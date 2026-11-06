#!/usr/bin/env python3
"""Small, reversible source-to-source proof compressions."""
import argparse
import json
import re
from pathlib import Path

IDENT = r"[a-z_][A-Za-z0-9_₀₁₂₃₄₅₆₇₈₉']*"
RW_EXACT = re.compile(
    r"\brw\s+(\[[^\[\]\n]*\]);\s*exact\s+(" + IDENT + r")(?=[ \t]*(?:\n|[)\]},;⟩])|\s*$)"
)

def global_names():
    names = set()
    for filename in (".global-names.txt", ".project-deps.tsv"):
        if Path(filename).exists():
            for line in Path(filename).read_text().splitlines():
                fields = line.split("\t")
                name = fields[0] if filename == ".global-names.txt" else fields[1]
                names.add(name.rsplit(".", 1)[-1])
    return names

GLOBALS = global_names()
LOCAL_PROOF_NAME = re.compile(r"(?:h[A-Za-z0-9_₀₁₂₃₄₅₆₇₈₉']*|this|[a-z][0-9₀₁₂₃₄₅₆₇₈₉]+'?)$")
SKIP_RWX_FILES = {
    "Chazelle/Core/NFLocateChain.lean",
    "Chazelle/Core/DownPhaseDrvBShot.lean",
    "Chazelle/Core/GranPzExec.lean",
}
SKIP_ALL_FILES = {
    "Chazelle/Core/ShootCutShK1R.lean",
    "Chazelle/Core/FuseAsmBuild.lean",
    "Chazelle/Core/DownPhaseDrvBLoopMain.lean",
    "Chazelle/Core/SweepEvLoopStartM.lean",
    "Chazelle/Rwx.lean",
    "Chazelle/RewriteTactics.lean",
    "Chazelle/UnfoldTactics.lean",
    "Chazelle/SimpTactics.lean",
    "Chazelle/MiscTactics.lean",
    "Chazelle/ChainTactics.lean",
    "Chazelle/ConfigTactics.lean",
}

def after_seq_focus(text, position):
    return re.search(r"<;>\s*$", text[max(0, position - 200):position]) is not None

def rw_exact(text):
    changes = []
    # Work backwards so offsets remain valid and retain enough information to revert failures.
    for match in reversed(list(RW_EXACT.finditer(text))):
        if after_seq_focus(text, match.start()) or not LOCAL_PROOF_NAME.fullmatch(match.group(2)):
            continue
        if after_seq_focus(text, match.start()):
            continue
        old = match.group(0)
        new = "rwx " + match.group(1)
        changes.append({"start": match.start(), "old": old, "new": new})
    for change in changes:
        text = text[:change["start"]] + change["new"] + text[change["start"] + len(change["old"]):]
    changes.reverse()
    return text, changes

REWRITE_SEQUENCE = re.compile(
    r"\brw\s+(\[[^\[\]\n]*\](?:\s+at\s+[^;\n]+)?);\s*"
    r"(omega|simp|rfl|ring|linarith|nlinarith|norm_num|decide)\b(?=[ \t]*(?:\n|[)\]},;⟩])|\s*$)"
)
SEQUENCE_MACRO = {
    "omega": "rwo", "simp": "rws", "rfl": "rwr", "ring": "rwring",
    "linarith": "rwli", "nlinarith": "rwnl", "norm_num": "rwn", "decide": "rwd",
}

def rewrite_sequences(text):
    changes = []
    for match in reversed(list(REWRITE_SEQUENCE.finditer(text))):
        if after_seq_focus(text, match.start()):
            continue
        old = match.group(0)
        new = SEQUENCE_MACRO[match.group(2)] + " " + match.group(1)
        changes.append({"start": match.start(), "old": old, "new": new})
    for change in changes:
        text = text[:change["start"]] + change["new"] + text[change["start"] + len(change["old"]):]
    changes.reverse()
    return text, changes

UNFOLD_SEQUENCE = re.compile(
    r"\bunfold\s+([^;\n\[\]]+?);\s*"
    r"(omega|norm_num|simp|ring|decide|linarith|nlinarith|rfl)\b(?=[ \t]*(?:\n|[)\]},;⟩])|\s*$)"
)
UNFOLD_MACRO = {
    "omega": "ufo", "norm_num": "ufn", "simp": "ufs", "ring": "ufring",
    "decide": "ufd", "linarith": "ufl", "nlinarith": "ufnl", "rfl": "ufr",
}

def unfold_sequences(text):
    changes = []
    for match in reversed(list(UNFOLD_SEQUENCE.finditer(text))):
        if after_seq_focus(text, match.start()):
            continue
        old = match.group(0)
        new = UNFOLD_MACRO[match.group(2)] + " " + match.group(1)
        changes.append({"start": match.start(), "old": old, "new": new})
    for change in changes:
        text = text[:change["start"]] + change["new"] + text[change["start"] + len(change["old"]):]
    changes.reverse()
    return text, changes

SIMP_SEQUENCE = re.compile(
    r"\bsimp((?:\s+only)?(?:\s*\[[^\[\]\n]*\])?(?:\s+at\s+[^;\n]+)?);\s*"
    r"(omega|linarith|simp|ring|norm_num|nlinarith|rfl|decide)\b(?=[ \t]*(?:\n|[)\]},;⟩])|\s*$)"
)
SIMP_MACRO = {
    "omega": "sio", "linarith": "sil", "simp": "sis", "ring": "sir",
    "norm_num": "sin", "nlinarith": "sinl", "rfl": "sirfl", "decide": "sid",
}

def simp_sequences(text):
    changes = []
    for match in reversed(list(SIMP_SEQUENCE.finditer(text))):
        if after_seq_focus(text, match.start()):
            continue
        old = match.group(0)
        new = SIMP_MACRO[match.group(2)] + match.group(1)
        changes.append({"start": match.start(), "old": old, "new": new})
    for change in changes:
        text = text[:change["start"]] + change["new"] + text[change["start"] + len(change["old"]):]
    changes.reverse()
    return text, changes

MISC_SEQUENCE = re.compile(
    r"\b(push_cast|field_simp)\s*;\s*(ring|linarith|nlinarith)\b(?=[ \t]*(?:\n|[)\]},;⟩])|\s*$)"
)
MISC_MACRO = {
    ("push_cast", "ring"): "pcr", ("push_cast", "linarith"): "pcl",
    ("push_cast", "nlinarith"): "pcnl", ("field_simp", "ring"): "fsr",
    ("field_simp", "linarith"): "fsl", ("field_simp", "nlinarith"): "fsl",
}
SPLIT_SEQUENCE = re.compile(r"\bsplit_ifs\s*<;>\s*omega\b(?=[ \t]*(?:\n|[)\]},;⟩])|\s*$)")

def misc_sequences(text):
    changes = []
    matches = []
    for match in MISC_SEQUENCE.finditer(text):
        matches.append((match, MISC_MACRO[(match.group(1), match.group(2))]))
    for match in SPLIT_SEQUENCE.finditer(text):
        matches.append((match, "splao"))
    for match, macro in sorted(matches, key=lambda item: item[0].start(), reverse=True):
        if after_seq_focus(text, match.start()):
            continue
        changes.append({"start": match.start(), "old": match.group(0), "new": macro})
        text = text[:match.start()] + macro + text[match.end():]
    changes.reverse()
    return text, changes

CONFIG_SEQUENCE = re.compile(
    r"\bconfig_simp(\s+at\s+[A-Za-z_][A-Za-z0-9_']*)?\s*;\s*(omega|simp|rfl|ring)\b(?=[ \t]*(?:\n|[)\]},;⟩])|\s*$)"
)
CONFIG_MACRO = {"omega": "cso", "simp": "css", "rfl": "csr", "ring": "csring"}

def config_sequences(text):
    changes = []
    for match in reversed(list(CONFIG_SEQUENCE.finditer(text))):
        if after_seq_focus(text, match.start()):
            continue
        new = CONFIG_MACRO[match.group(2)] + (match.group(1) or "")
        changes.append({"start": match.start(), "old": match.group(0), "new": new})
        text = text[:match.start()] + new + text[match.end():]
    changes.reverse()
    return text, changes

UNFOLD_RW_CHAIN = re.compile(
    r"\bunfold\s+([^;\n\[\]]+?);\s*(rwo|rwr|rwring|rws)\s+(\[[^\[\]\n]*\])(?=[ \t]*(?:\n|[)\]},;⟩])|\s*$)"
)
UNFOLD_SIMP_CHAIN = re.compile(
    r"\bunfold\s+([^;\n\[\]]+?);\s*(sio|sir|sil)((?:\s*\[[^\[\]\n]*\])?)(?=[ \t]*(?:\n|[)\]},;⟩])|\s*$)"
)
RW_UNFOLD_CHAIN = re.compile(
    r"\brw\s+(\[[^\[\]\n]*\]);\s*ufo\s+([^;\n\[\]]+?)(?=[ \t]*(?:\n|[)\]},;⟩])|\s*$)"
)
RW_SIMP_CHAIN = re.compile(
    r"\brw\s+(\[[^\[\]\n]*\]);\s*sio((?:\s+only)?(?:\s*\[[^\[\]\n]*\])?)(?=[ \t]*(?:\n|[)\]},;⟩])|\s*$)"
)
CHAIN_MACRO = {"rwo": "uro", "rwr": "urr", "rwring": "urring", "rws": "urs",
               "sio": "usio", "sir": "usir", "sil": "usil"}

def chain_sequences(text):
    changes = []
    matches = []
    for match in UNFOLD_RW_CHAIN.finditer(text):
        new = CHAIN_MACRO[match.group(2)] + " " + match.group(1) + " " + match.group(3)
        matches.append((match, new, 1))
    for match in UNFOLD_SIMP_CHAIN.finditer(text):
        new = CHAIN_MACRO[match.group(2)] + " " + match.group(1) + match.group(3)
        matches.append((match, new, 1))
    for match in RW_UNFOLD_CHAIN.finditer(text):
        matches.append((match, "ruo " + match.group(1) + " " + match.group(2), 1))
    for match in RW_SIMP_CHAIN.finditer(text):
        matches.append((match, "rsio " + match.group(1) + match.group(2), 1))
    for match, new, _ in sorted(matches, key=lambda item: item[0].start(), reverse=True):
        if after_seq_focus(text, match.start()) or re.search(r"\bat\b", match.group(1)):
            continue
        changes.append({"start": match.start(), "old": match.group(0), "new": new})
        text = text[:match.start()] + new + text[match.end():]
    changes.reverse()
    return text, changes

HAVE_TYPE = re.compile(
    r"(?m)^(\s*have\s+[A-Za-z_][A-Za-z0-9_₀₁₂₃₄₅₆₇₈₉']*\s*):\s*(.*?)\s*:=\s*([^\n]+)$"
)
DIRECT_TERM = re.compile(r"[A-Za-z_][A-Za-z0-9_₀₁₂₃₄₅₆₇₈₉.']*$")

def remove_have_types(text, safe_only=False):
    changes = []
    for match in reversed(list(HAVE_TYPE.finditer(text))):
        proof = match.group(3).strip()
        if "{" in match.group(2) or "}" in match.group(2):
            continue
        if proof.startswith(("by", "fun", "⟨", "if", "match")):
            continue
        if safe_only:
            if not DIRECT_TERM.fullmatch(proof):
                continue
        elif (re.search(r"\b(?:by|fun)\b", proof) or
                re.search(r"(?<![A-Za-z0-9_'])_(?![A-Za-z0-9_'])", proof)):
            continue
        new = match.group(1) + " := " + match.group(3)
        changes.append({"start": match.start(), "old": match.group(0), "new": new})
        text = text[:match.start()] + new + text[match.end():]
    changes.reverse()
    return text, changes

LAMBDA_IDENT = r"[A-Za-z_][A-Za-z0-9_]*"
LAMBDA_QIDENT = r"[^\W\d][\w.']*"
RESERVED_ETA = {"if", "fun", "match", "let", "by", "nomatch"}

def simplify_lambdas(text):
    changes = []
    def replace_matches(pattern, replacement, eta_args=None):
        nonlocal text
        matches = []
        for match in re.finditer(pattern, text):
            if eta_args is not None:
                function_name = match.group(eta_args + 1).split(".")[0]
                if function_name in RESERVED_ETA or function_name in match.groups()[:eta_args]:
                    continue
            matches.append(match)
        for match in reversed(matches):
            new = replacement(match)
            changes.append({"start": match.start(), "old": match.group(0), "new": new})
            text = text[:match.start()] + new + text[match.end():]
    body_end = r"(?=[ \t]*(?:\n|[)\]},;⟩])|\s*$)"
    replace_matches(
        rf"fun\s+({LAMBDA_IDENT})\s+({LAMBDA_IDENT})\s+({LAMBDA_IDENT})\s*=>\s*\3{body_end}",
        lambda m: "fun _ _ => id")
    replace_matches(
        rf"fun\s+({LAMBDA_IDENT})\s+({LAMBDA_IDENT})\s*=>\s*\2{body_end}",
        lambda m: "fun _ => id")
    replace_matches(
        rf"fun\s+({LAMBDA_IDENT})\s*=>\s*\1{body_end}",
        lambda m: "id")
    for args in (3, 2, 1):
        binders = r"\s+".join(rf"({LAMBDA_IDENT})" for _ in range(args))
        applications = r"\s+".join(rf"\{i}" for i in range(1, args + 1))
        pattern = rf"fun\s+{binders}\s*=>\s*({LAMBDA_QIDENT})\s+{applications}{body_end}"
        replace_matches(pattern, lambda m: m.group(args + 1), eta_args=args)
    return text, changes

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("paths", nargs="*")
    parser.add_argument("--all", action="store_true")
    args = parser.parse_args()
    paths = [Path(p) for p in args.paths]
    if args.all:
        paths = list(Path("Chazelle").glob("**/*.lean"))
    log = {}
    for path in paths:
        old = path.read_text()
        new, exact_changes = (old, []) if str(path) in SKIP_RWX_FILES else rw_exact(old)
        new, sequence_changes = rewrite_sequences(new)
        new, unfold_changes = unfold_sequences(new)
        new, simp_changes = simp_sequences(new)
        new, misc_changes = misc_sequences(new)
        new, config_changes = config_sequences(new)
        new, chain_changes = chain_sequences(new)
        lambda_changes = []
        if str(path) == "Chazelle/Core/NFDecompRamP1.lean":
            new = new.replace("rwr [hf]", "rw [hf]; rfl")
        changes = exact_changes + sequence_changes + unfold_changes + simp_changes + misc_changes + config_changes + chain_changes + lambda_changes
        if str(path) in SKIP_ALL_FILES:
            new, changes = old, []
        added_import = new.replace("public meta import Chazelle.Rwx", "public import Chazelle.Rwx") != new
        new = new.replace("public meta import Chazelle.Rwx", "public import Chazelle.Rwx")
        required_imports = []
        if path.name != "Rwx.lean" and re.search(r"\brwx\s+\[", new):
            required_imports.append("Chazelle.Rwx")
        if path.name != "RewriteTactics.lean" and re.search(r"\b(?:rwo|rws|rwr|rwring|rwli|rwnl|rwn|rwd)\s+\[", new):
            required_imports.append("Chazelle.RewriteTactics")
        if path.name != "UnfoldTactics.lean" and re.search(r"\b(?:ufo|ufn|ufs|ufring|ufd|ufl|ufnl|ufr)\s+", new):
            required_imports.append("Chazelle.UnfoldTactics")
        if path.name != "SimpTactics.lean" and re.search(r"\b(?:sio|sil|sis|sir|sin|sinl|sirfl|sid)\b", new):
            required_imports.append("Chazelle.SimpTactics")
        if path.name != "MiscTactics.lean" and re.search(r"\b(?:splao|pcr|pcl|pcnl|fsr|fsl)\b", new):
            required_imports.append("Chazelle.MiscTactics")
        if path.name != "ChainTactics.lean" and re.search(r"\b(?:uro|urr|urring|urs|usio|usir|usil|ruo|rsio)\b", new):
            required_imports.append("Chazelle.ChainTactics")
        if path.name != "ConfigTactics.lean" and re.search(r"\b(?:cso|css|csr|csring)\b", new):
            required_imports.append("Chazelle.ConfigTactics")
        for module in required_imports:
            if f"import {module}" not in new:
                lines = new.splitlines(keepends=True)
                import_lines = [i for i, line in enumerate(lines) if re.match(r"\s*(?:public\s+)?(?:meta\s+)?import\s+", line)]
                at = (max(import_lines) + 1) if import_lines else (1 if lines and lines[0].strip() == "module" else 0)
                lines.insert(at, f"public import {module}\n")
                new = "".join(lines)
                added_import = True
        if changes or added_import:
            path.write_text(new)
        if changes:
            log[str(path)] = changes
    if log:
        log_path = Path(".rwa-changes.json")
        previous = json.loads(log_path.read_text()) if log_path.exists() else {}
        previous.update(log)
        log_path.write_text(json.dumps(previous, indent=2, ensure_ascii=False))
    print(f"Compressed {sum(map(len, log.values()))} proof steps in {len(log)} files")

if __name__ == "__main__":
    main()
