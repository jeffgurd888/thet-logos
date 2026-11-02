#!/usr/bin/env python3
"""Validator for the machine-readable Epistemic Ledger.

Checks, and reports honestly:
  1. The schema itself (ledger-entry.schema.json) is a valid JSON Schema.
  2. Every record in epistemic-ledger/records/*.json conforms to it.
  3. SELF-TEST: a deliberately broken record (a killed claim with no
     kill_id, a bad tier) is REJECTED — a validator that cannot bite is
     not a validator.
  4. Referenced paths exist: each record's module/dossier, when
     non-null, must resolve inside the repository.
  5. Frontmatter adoption scan over a NAMED subset of dossiers: a
     dossier 'carries' the schema if it opens with a --- fenced block
     containing one JSON object conforming to the schema. Absence is
     reported as absence (the schema is prospective for dossiers),
     never spun as conformance.

Usage:  python3 epistemic-ledger/validate_ledger.py
Exit 1 iff the schema is invalid, any record fails, the self-test does
not bite, or a referenced path is missing.
"""
import json
import sys
from pathlib import Path

from jsonschema import Draft202012Validator

HERE = Path(__file__).resolve().parent
REPO = HERE.parent

# Named subset for the frontmatter adoption scan: this run's dossiers.
DOSSIER_SUBSET = [
    "whitepaper/dc-f1-landing-2026-11-02.md",
    "whitepaper/dc-f2-landing-2026-11-02.md",
    "whitepaper/dc-f3-landing-2026-11-02.md",
    "whitepaper/bsd3-2r-pin-landing-2026-11-02.md",
    "whitepaper/bsd3-2r-sweep-landing-2026-11-02.md",
    "whitepaper/bsd3-2r-assembly-landing-2026-11-02.md",
    "whitepaper/ci-enforcement-landing-2026-11-02.md",
    "whitepaper/axiom-graph-landing-2026-11-02.md",
    "whitepaper/engine-property-tests-landing-2026-11-02.md",
]


def frontmatter_record(path: Path):
    """Return the parsed frontmatter object, or None if the file does
    not open with a --- fenced JSON block."""
    text = path.read_text(encoding="utf-8", errors="replace")
    if not text.startswith("---\n"):
        return None
    end = text.find("\n---", 4)
    if end == -1:
        return None
    try:
        return json.loads(text[4:end])
    except json.JSONDecodeError:
        return None


def main() -> int:
    failures = []

    schema = json.loads((HERE / "ledger-entry.schema.json").read_text())
    Draft202012Validator.check_schema(schema)
    print("SCHEMA: valid JSON Schema (draft 2020-12)")
    validator = Draft202012Validator(schema)

    records = sorted((HERE / "records").glob("*.json"))
    for rec_path in records:
        rec = json.loads(rec_path.read_text())
        errors = sorted(validator.iter_errors(rec), key=lambda e: e.path)
        if errors:
            failures.append(rec_path.name)
            print(f"RECORD FAIL {rec_path.name}:")
            for e in errors:
                print(f"   - {list(e.path)}: {e.message}")
        else:
            print(f"RECORD PASS {rec_path.name} (id={rec['id']}, "
                  f"status={rec['status']}, tier={rec['tier']})")
        for key in ("module", "dossier"):
            target = rec.get(key)
            if target is not None and not (REPO / target).exists():
                failures.append(f"{rec_path.name}:{key}")
                print(f"   PATH FAIL: {key} -> {target} does not exist")

    broken = {
        "id": "self-test-broken", "tier": "T9",
        "claim": "A killed claim with no kill id and a bad tier.",
        "status": "killed", "evidence": "self-test", "date": "2026-11-02",
        "kill_id": None, "census_at_landing": None,
        "module": None, "dossier": None,
    }
    if list(validator.iter_errors(broken)):
        print("SELF-TEST: broken record correctly REJECTED")
    else:
        failures.append("self-test")
        print("SELF-TEST FAIL: broken record was ACCEPTED")

    carrying = 0
    for rel in DOSSIER_SUBSET:
        p = REPO / rel
        if not p.exists():
            print(f"DOSSIER SCAN: {rel} NOT FOUND")
            continue
        rec = frontmatter_record(p)
        if rec is None:
            print(f"DOSSIER SCAN: {rel} carries no schema frontmatter")
        elif list(validator.iter_errors(rec)):
            failures.append(f"frontmatter:{rel}")
            print(f"DOSSIER SCAN: {rel} frontmatter present but INVALID")
        else:
            carrying += 1
            print(f"DOSSIER SCAN: {rel} frontmatter CONFORMS")
    print(f"DOSSIER SCAN SUMMARY: {carrying}/{len(DOSSIER_SUBSET)} named "
          f"dossiers carry conforming frontmatter (schema is prospective "
          f"for dossiers; absence is reported, not spun)")

    if failures:
        print(f"\nVALIDATION FAIL: {failures}")
        return 1
    print(f"\nVALIDATION PASS: schema valid; {len(records)} records "
          f"conform; paths resolve; self-test bites.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
