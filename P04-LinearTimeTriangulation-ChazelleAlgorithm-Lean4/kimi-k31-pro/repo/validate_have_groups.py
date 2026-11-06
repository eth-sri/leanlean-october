#!/usr/bin/env python3
"""Fine-grained recovery of `have` type removals, one declaration group at a time."""
import concurrent.futures
import json
import os
from pathlib import Path
import re
import subprocess

from compress_codemods import remove_have_types
from lean_strip._pipeline.metrics.tokens import count_lean_tokens_in_source

DECL = re.compile(
    r"^\s*(?:(?:@\[.*\]|private|protected|public|noncomputable|unsafe|partial|set_option .* in)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|opaque)\b")


def lean(path):
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    try:
        result = subprocess.run(["lake", "env", "lean", str(path)], env=env,
                                capture_output=True, text=True, timeout=180)
        return result.returncode == 0, result.stdout + result.stderr
    except subprocess.TimeoutExpired as exc:
        return False, str(exc.stdout or "") + str(exc.stderr or "")


def check(item):
    filename, initial_status = item
    path = Path(filename)
    source = path.read_text()
    _, candidates = remove_have_types(source)
    if not candidates:
        return {"file": filename, "status": initial_status, "groups": 0, "count": 0, "tokens": 0}
    lines = source.splitlines(keepends=True)
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line))
    declaration_lines = [index for index, line in enumerate(lines) if DECL.match(line)]
    groups = {}
    for change in candidates:
        line_index = source.count("\n", 0, change["start"])
        preceding = [index for index in declaration_lines if index <= line_index]
        key = preceding[-1] if preceding else -1
        groups.setdefault(key, []).append(change)
    accepted_groups = 0
    accepted_changes = 0
    tokens = 0
    output = []
    for _, changes in sorted(groups.items(), key=lambda item: item[0], reverse=True):
        before = source
        for change in sorted(changes, key=lambda change: change["start"], reverse=True):
            start, end = change["start"], change["start"] + len(change["old"])
            if source[start:end] != change["old"]:
                raise RuntimeError(f"offset changed in {filename}: {change}")
            source = source[:start] + change["new"] + source[end:]
        path.write_text(source)
        ok, log = lean(path)
        if ok:
            accepted_groups += 1
            accepted_changes += len(changes)
            tokens += sum(count_lean_tokens_in_source(change["old"]) -
                          count_lean_tokens_in_source(change["new"]) for change in changes)
        else:
            source = before
            path.write_text(source)
            output.append(log)
    if output:
        Path(f".validate-have-groups-{filename.replace('/', '_')}.log").write_text("\n".join(output))
    status = initial_status + f"+{accepted_groups}groups"
    return {"file": filename, "status": status, "groups": accepted_groups,
            "count": accepted_changes, "tokens": tokens}


def main():
    previous = json.loads(Path(".validate-have-results.json").read_text())
    work = [(r["file"], r["status"]) for r in previous if r["status"] in {"reverted", "fallback"}]
    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        for index, result in enumerate(pool.map(check, work), 1):
            results.append(result)
            if index % 10 == 0 or result["groups"]:
                print(f"{index}/{len(work)}: {result['status']} {result['file']} "
                      f"({result['tokens']} tokens)", flush=True)
    Path(".validate-have-groups-results.json").write_text(json.dumps(results, indent=2))
    print(f"accepted {sum(r['groups'] for r in results)} groups, "
          f"{sum(r['count'] for r in results)} declarations, {sum(r['tokens'] for r in results)} tokens")


if __name__ == "__main__":
    main()
