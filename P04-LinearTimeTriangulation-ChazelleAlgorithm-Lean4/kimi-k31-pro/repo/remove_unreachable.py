#!/usr/bin/env python3
"""Delete modules outside the MainTheorem import closure and their umbrella imports."""
import argparse
from pathlib import Path
import re
from lean_strip._pipeline.metrics.tokens import count_lean_tokens_in_source

IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+([A-Za-z0-9_.]+)")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    files = {str(path.with_suffix("")).replace("/", "."): path for path in Path("Chazelle").glob("**/*.lean")}
    imports = {}
    for module, path in files.items():
        imports[module] = [match.group(1) for line in path.read_text().splitlines() if (match := IMPORT.match(line))]
    reachable = set()
    queue = ["Chazelle.Core.MainTheorem"]
    while queue:
        module = queue.pop()
        if module in reachable or module not in files:
            continue
        reachable.add(module)
        queue.extend(imports[module])
    unreachable = sorted(set(files) - reachable)
    tokens = sum(count_lean_tokens_in_source(files[module].read_text()) for module in unreachable)
    print(f"reachable {len(reachable)}; unreachable {len(unreachable)}; tokens {tokens}")
    for module in unreachable:
        print(module)
    if not args.apply:
        return
    for module in unreachable:
        files[module].unlink()
    removed = set(unreachable)
    root = Path("Chazelle.lean")
    lines = [line for line in root.read_text().splitlines(keepends=True)
             if not (match := IMPORT.match(line)) or match.group(1) not in removed]
    root.write_text("".join(lines))


if __name__ == "__main__":
    main()
