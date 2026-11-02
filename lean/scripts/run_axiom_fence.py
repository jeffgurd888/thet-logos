#!/usr/bin/env python3
"""Axiom-fence runner for the thet-logos corpus.

Assembles a Lean check file from the registry (scripts/axiom-fence.txt):
`import` lines are copied verbatim, each bare declaration line becomes a
`#print axioms` command. Runs the check file under `lake env lean`, then
verifies that every registered declaration's axiom set is a subset of the
fence {propext, Classical.choice, Quot.sound}. `sorryAx`, any other axiom,
a missing declaration, or a Lean error fails the fence (exit 1).

Usage:  python3 scripts/run_axiom_fence.py [--registry PATH] [--json PATH]
Run from the lean/ directory (or anywhere; paths resolve relative to it).
"""
import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

FENCE = {"propext", "Classical.choice", "Quot.sound"}


def parse_registry(path: Path):
    imports, decls = [], []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("import "):
            imports.append(line)
        else:
            decls.append(line)
    return imports, decls


def main() -> int:
    here = Path(__file__).resolve().parent.parent  # lean/
    ap = argparse.ArgumentParser()
    ap.add_argument("--registry", default=str(here / "scripts" / "axiom-fence.txt"))
    ap.add_argument("--json", default=None, help="also write machine-readable results here")
    args = ap.parse_args()

    imports, decls = parse_registry(Path(args.registry))
    if not decls:
        print("FENCE FAIL: registry is empty")
        return 1

    check_src = "\n".join(imports) + "\n\n" + "\n".join(
        f"#print axioms {d}" for d in decls
    ) + "\n"

    with tempfile.NamedTemporaryFile(
        "w", suffix=".lean", dir="/tmp", delete=False
    ) as fh:
        fh.write(check_src)
        check_path = fh.name

    proc = subprocess.run(
        ["lake", "env", "lean", check_path],
        cwd=str(here), capture_output=True, text=True,
    )
    out = proc.stdout + proc.stderr

    # Literal per-declaration search (declaration names may themselves
    # contain apostrophes, e.g. discFactorisationHyp'_proved, so a generic
    # 'name' regex would mis-split them).
    results = {}
    for d in decls:
        m = re.search(re.escape(f"'{d}' depends on axioms: [") + r"([^\]]*)\]", out)
        if m:
            results[d] = [a.strip() for a in m.group(1).split(",") if a.strip()]
        elif f"'{d}' does not depend on any axioms" in out:
            results[d] = []

    failures = []
    report = {}
    for d in decls:
        if d not in results:
            failures.append(f"{d}: NOT REPORTED (unknown constant or Lean error)")
            report[d] = {"axioms": None, "pass": False}
            continue
        extra = sorted(set(results[d]) - FENCE)
        ok = not extra
        report[d] = {"axioms": results[d], "pass": ok}
        print(f"{'PASS' if ok else 'FAIL'}  {d}  axioms={results[d]}")
        if not ok:
            failures.append(f"{d}: axioms outside fence: {extra}")

    if "error" in out.lower() and proc.returncode != 0 and not results:
        failures.append("Lean run produced errors and no axiom reports")
        print(out[:4000])

    if args.json:
        Path(args.json).write_text(json.dumps(report, indent=2), encoding="utf-8")

    if failures:
        print("\nFENCE FAIL:")
        for f in failures:
            print(" -", f)
        return 1
    print(f"\nFENCE PASS: {len(decls)} declarations, all axiom sets within "
          f"{{propext, Classical.choice, Quot.sound}}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
