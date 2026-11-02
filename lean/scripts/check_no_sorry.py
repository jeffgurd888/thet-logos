#!/usr/bin/env python3
"""Zero-sorry source gate for the thet-logos corpus.

Scans Lean sources for the token `sorry` in CODE position. Comments
(line `--`, block `/- ... -/` including docstrings `/-- ... -/`, with
nesting) and string literals are stripped first, so prose like a
docstring census note ("sorry/admit/axiom = 0/0/0") does not trigger
the gate — but an actual `sorry` tactic/command in code does.

This is the source-level half of the zero-sorry policy; the compiled
half is the axiom fence (scripts/run_axiom_fence.py): any theorem whose
proof used `sorry` depends on `sorryAx` and fails that fence.

Usage:  python3 scripts/check_no_sorry.py [DIR ...]   (default: ThetLogos/)
Exit 1 with a file:line report if any code-position `sorry` is found.
"""
import re
import sys
from pathlib import Path

TOKEN = re.compile(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])")


def strip_noncode(text: str) -> str:
    """Replace comments and string literals with spaces (keeping newlines
    so line numbers survive). Handles nested Lean block comments."""
    out = []
    i, n = 0, len(text)
    while i < n:
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j == -1 else j
            out.append(" " * (j - i))
            i = j
        elif text.startswith("/-", i):
            depth = 0
            j = i
            while j < n:
                if text.startswith("/-", j):
                    depth += 1
                    j += 2
                elif text.startswith("-/", j):
                    depth -= 1
                    j += 2
                    if depth == 0:
                        break
                else:
                    j += 1
            seg = text[i:j]
            out.append("".join(c if c == "\n" else " " for c in seg))
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == '"':
                    j += 1
                    break
                j += 1
            seg = text[i:j]
            out.append("".join(c if c == "\n" else " " for c in seg))
            i = j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def main() -> int:
    roots = [Path(p) for p in sys.argv[1:]] or [Path("ThetLogos")]
    findings = []
    files = []
    for root in roots:
        files.extend(sorted(root.rglob("*.lean")) if root.is_dir() else [root])
    for f in files:
        code = strip_noncode(f.read_text(encoding="utf-8", errors="replace"))
        for lineno, line in enumerate(code.splitlines(), 1):
            if TOKEN.search(line):
                findings.append(f"{f}:{lineno}: {line.strip()[:100]}")
    if findings:
        print("ZERO-SORRY GATE FAIL — `sorry` in code position:")
        for x in findings:
            print(" -", x)
        return 1
    print(f"ZERO-SORRY GATE PASS: {len(files)} files scanned, no code-position `sorry`.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
