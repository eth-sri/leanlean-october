#!/usr/bin/env python3
"""Remove redundant term-mode `have` type annotations with per-file validation."""
import concurrent.futures
import json
import os
from pathlib import Path
import subprocess

from compress_codemods import remove_have_types


def lean(path):
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(path)], env=env,
            capture_output=True, text=True, timeout=180)
        return result.returncode == 0, result.stdout + result.stderr
    except subprocess.TimeoutExpired as exc:
        return False, str(exc.stdout or "") + str(exc.stderr or "")


def check(filename):
    path = Path(filename)
    original = path.read_text()
    updated, changes = remove_have_types(original)
    if not changes:
        return {"file": filename, "status": "skipped", "count": 0}
    path.write_text(updated)
    ok, output = lean(path)
    if ok:
        status = "full"
        count = len(changes)
    else:
        fallback, safe_changes = remove_have_types(original, safe_only=True)
        if safe_changes and fallback != updated:
            path.write_text(fallback)
            safe_ok, safe_output = lean(path)
            output += "\n--- conservative fallback ---\n" + safe_output
            if safe_ok:
                status = "fallback"
                count = len(safe_changes)
                ok = True
            else:
                ok = False
        else:
            ok = False
        if not ok:
            path.write_text(original)
            status = "reverted"
            count = 0
    if output:
        Path(f".validate-have-{filename.replace('/', '_')}.log").write_text(output)
    return {"file": filename, "status": status, "count": count}


def main():
    paths = list(Path("Chazelle").glob("**/*.lean"))
    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        for index, result in enumerate(pool.map(check, map(str, paths)), 1):
            results.append(result)
            if index % 25 == 0 or result["status"] == "reverted":
                print(f"{index}/{len(paths)}: {result['status']} {result['file']}", flush=True)
    Path(".validate-have-results.json").write_text(json.dumps(results, indent=2))
    for status in ("full", "fallback", "reverted", "skipped"):
        selected = [r for r in results if r["status"] == status]
        print(status, len(selected), sum(r["count"] for r in selected))


if __name__ == "__main__":
    main()
