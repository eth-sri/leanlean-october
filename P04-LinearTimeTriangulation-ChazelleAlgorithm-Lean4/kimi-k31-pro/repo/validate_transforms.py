#!/usr/bin/env python3
"""Validate optional source transformations independently per Lean module."""
import argparse
import concurrent.futures
import json
import os
from pathlib import Path
import re
import subprocess

from compress_codemods import simplify_lambdas


def transform(path, mode):
    source = path.read_text()
    if mode == "lambda":
        result, changes = simplify_lambdas(source)
        return result, len(changes)
    if mode == "simp":
        if str(path) in {
            "Chazelle/Programs/Tactics.lean",
            "Chazelle/Rwx.lean",
            "Chazelle/RewriteTactics.lean",
            "Chazelle/UnfoldTactics.lean",
            "Chazelle/SimpTactics.lean",
            "Chazelle/MiscTactics.lean",
            "Chazelle/ChainTactics.lean",
            "Chazelle/ConfigTactics.lean",
        }:
            return source, 0
        return source.replace("simp only", "simp"), source.count("simp only")
    if mode == "show":
        lines = source.splitlines(keepends=True)
        kept = []
        count = 0
        for index, line in enumerate(lines):
            stripped = line.strip()
            next_is_from = index + 1 < len(lines) and lines[index + 1].lstrip().startswith("from ")
            if (stripped.startswith("show ") and " from " not in stripped and
                    not re.search(r"\bby\b", stripped) and ";" not in stripped and not next_is_from):
                count += 1
            else:
                kept.append(line)
        return "".join(kept), count
    raise ValueError(mode)


def check(item):
    filename, mode = item
    path = Path(filename)
    original = path.read_text()
    updated, count = transform(path, mode)
    if not count or updated == original:
        return {"file": filename, "status": "skipped", "count": 0}
    path.write_text(updated)
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    try:
        result = subprocess.run(
            ["lake", "env", "lean", filename],
            cwd=Path.cwd(), env=env, capture_output=True, text=True, timeout=180)
        output = result.stdout + result.stderr
        ok = result.returncode == 0
    except subprocess.TimeoutExpired as exc:
        output = (exc.stdout or "") + (exc.stderr or "")
        ok = False
    if not ok:
        path.write_text(original)
        status = "reverted"
    else:
        status = "kept"
    if output:
        Path(f".validate-{mode}-{filename.replace('/', '_')}.log").write_text(output)
    return {"file": filename, "status": status, "count": count if ok else 0}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=["lambda", "simp", "show"])
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("paths", nargs="*")
    args = parser.parse_args()
    paths = [Path(p) for p in args.paths] if args.paths else list(Path("Chazelle").glob("**/*.lean"))
    work = [(str(path), args.mode) for path in paths]
    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        for index, result in enumerate(pool.map(check, work), 1):
            results.append(result)
            if index % 25 == 0 or result["status"] == "reverted":
                print(f"{index}/{len(work)}: {result['status']} {result['file']}", flush=True)
    Path(f".validate-{args.mode}-results.json").write_text(json.dumps(results, indent=2))
    kept = [r for r in results if r["status"] == "kept"]
    reverted = [r for r in results if r["status"] == "reverted"]
    print(f"kept {len(kept)} files / {sum(r['count'] for r in kept)} sites; reverted {len(reverted)} files")


if __name__ == "__main__":
    main()
