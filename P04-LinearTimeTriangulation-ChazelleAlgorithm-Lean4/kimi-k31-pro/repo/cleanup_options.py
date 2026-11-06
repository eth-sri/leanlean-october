#!/usr/bin/env python3
"""Hoist repeated per-declaration resource limits and remove linter-only options."""
from pathlib import Path
import re

NUMERIC = {"maxHeartbeats", "maxRecDepth", "synthInstance.maxSize", "synthInstance.maxHeartbeats"}
OPTION = re.compile(r"^\s*set_option\s+(\S+)\s+(\d+)(?:\s+in)?\s*$")
LINTER = re.compile(r"^\s*set_option\s+linter\.\S+\s+false(?:\s+in)?\s*$")


def cleanup(path):
    lines = path.read_text().splitlines(keepends=True)
    values = {}
    removed_numeric = 0
    removed_linter = 0
    kept = []
    for line in lines:
        match = OPTION.match(line.rstrip("\n"))
        if match and match.group(1) in NUMERIC:
            key, raw = match.groups()
            value = int(raw)
            previous = values.get(key)
            if previous is None or (value == 0 and previous != 0) or (previous != 0 and value > previous):
                values[key] = value
            removed_numeric += 1
            continue
        if LINTER.match(line.rstrip("\n")):
            removed_linter += 1
            continue
        kept.append(line)
    if not removed_numeric and not removed_linter:
        return 0, 0
    if values:
        import_lines = [i for i, line in enumerate(kept) if re.match(r"\s*(?:public\s+)?(?:meta\s+)?import\s+", line)]
        at = max(import_lines) + 1 if import_lines else (1 if kept and kept[0].strip() == "module" else 0)
        additions = [f"set_option {key} {value}\n" for key, value in sorted(values.items())]
        kept[at:at] = additions
    path.write_text("".join(kept))
    return removed_numeric, removed_linter


def main():
    numeric = linter = files = 0
    for path in Path("Chazelle").glob("**/*.lean"):
        n, l = cleanup(path)
        numeric += n
        linter += l
        files += bool(n or l)
    print(f"updated {files} files; hoisted {numeric} numeric options; removed {linter} linter options")


if __name__ == "__main__":
    main()
