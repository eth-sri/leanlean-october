#!/usr/bin/env python3
"""Remove declarations outside the protected theorem's kernel dependency closure."""
import argparse
import collections
import json
from pathlib import Path
import re
from lean_strip._pipeline.metrics.tokens import count_lean_tokens_in_source

HELPERS = {
    "Chazelle.Spec", "Chazelle.Rwx", "Chazelle.RewriteTactics",
    "Chazelle.UnfoldTactics", "Chazelle.SimpTactics", "Chazelle.MiscTactics",
    "Chazelle.ChainTactics", "Chazelle.ConfigTactics",
}
SYNTAX = re.compile(r"^(?:@\[[^\n]*\]\s*)?(?:private\s+|protected\s+|public\s+|local\s+|scoped\s+)*(?:macro|syntax|elab|notation)\b")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    status = {}
    modules = collections.defaultdict(list)
    for line in Path(".deps-current.tsv").read_text().splitlines():
        state, name, module = line.split("\t")
        status[name] = state
        modules[module].append(name)
    ranges = collections.defaultdict(list)
    for module in modules:
        artifact = Path(".lake/build/lib/lean") / (module.replace(".", "/") + ".ilean")
        if not artifact.exists():
            continue
        data = json.loads(artifact.read_text())
        for name, positions in data.get("decls", {}).items():
            if name in status:
                ranges[(module, tuple(positions[:4]))].append(name)
    by_file = collections.defaultdict(list)
    skipped = []
    for (module, positions), names in ranges.items():
        if module in HELPERS or any(status[name] == "USED" for name in names):
            continue
        path = Path(module.replace(".", "/") + ".lean")
        if not path.exists():
            continue
        source = path.read_text()
        lines = source.splitlines(keepends=True)
        offsets = [0]
        for line in lines:
            offsets.append(offsets[-1] + len(line))
        a, b, c, d = positions
        start, end = offsets[a] + b, offsets[c] + d
        text = source[start:end]
        if any("macroRules" in name for name in names) or SYNTAX.match(text.strip()):
            skipped.append((module, names, "syntax"))
            continue
        by_file[path].append({"module": module, "names": names, "start": start, "end": end, "text": text})
    total = sum(len(items) for items in by_file.values())
    chars = sum(len(item["text"]) for items in by_file.values() for item in items)
    tokens = sum(count_lean_tokens_in_source(item["text"]) for items in by_file.values() for item in items)
    print(f"dead declaration candidates: {total}, {chars} characters, {tokens} tokens, {len(by_file)} files; syntax skipped: {len(skipped)}")
    for path, items in sorted(by_file.items(), key=lambda item: -sum(len(x["text"]) for x in item[1]))[:30]:
        print(f"{sum(len(x['text']) for x in items):8} {len(items):4} {path}")
    if not args.apply:
        return
    log = {}
    for path, items in by_file.items():
        source = path.read_text()
        for item in sorted(items, key=lambda item: item["start"], reverse=True):
            start, end = item["start"], item["end"]
            if source[start:end] != item["text"]:
                raise RuntimeError(f"source changed since analysis: {path}: {item['names']}")
            removal_end = end + (end < len(source) and source[end] == "\n")
            source = source[:start] + source[removal_end:]
        path.write_text(source)
        log[str(path)] = [{k: v for k, v in item.items() if k not in {"start", "end"}} for item in items]
    Path(".dead-removal.json").write_text(json.dumps(log, indent=2, ensure_ascii=False))
    print(f"removed {total} declarations")


if __name__ == "__main__":
    main()
