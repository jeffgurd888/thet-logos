# EPISTEMIC LEDGER SCHEMA LANDING — machine-readable T1–T5 records — 2026-11-02

Jeff's order (2026-11-01 23:04 EST, "fire 1→4"), vector 4. NO CLAIM;
dials 0/4; census unchanged (12,641 / 13,153 / 445, zero sorrys).

## What shipped (all under `epistemic-ledger/`)

- **`ledger-entry.schema.json`** — JSON Schema (draft 2020-12) for one
  ledger record per claim: `tier` (T1–T5 per TIERS.md), `claim`,
  `status` (standing / killed / partial / frontier), `evidence`
  qualifier, `date`, `kill_id` (schema-enforced: REQUIRED iff status
  is killed), `census_at_landing` ({strict, total, modules}; explicit
  nulls for unrecorded figures — never estimates), and repo-relative
  `module` / `dossier` links. All keys required; absence is data.
- **`records/`** — five seed records extracted faithfully from landed
  verdicts: DC-F1 helicity identity (standing), BSD3-2R assembly
  sha-iff (standing), CLS-B identification (killed, K-CLS-B), Hodge
  non-vacuous statement (killed, K-HODGE-0), TransferFormPos clause (a)
  (frontier).
- **`validate_ledger.py`** — the validator (see run results below).
- **`SCHEMA.md`** — the mapping note: field ↔ repo-structure table,
  the dossier-frontmatter adoption format, and the tier-dialect
  warning (next section).

## Tier-dialect warning (on the note's face, repeated here)

TIERS.md (framework §5) numbers proved/checked claims **T3**; the
bench's pipeline shorthand calls the same grade "T1". The schema uses
the TIERS.md dialect (it lives beside TIERS.md and mirrors LEDGER.md),
and every record also carries an `evidence` qualifier so the fact is
recoverable without the dialect. The divergence is recorded as a known
hazard; neither side is relabeled (relabeling rule).

## Validator run (2026-11-02, this tree)

- Schema itself: valid.
- Records: **5/5 conform**; every referenced module/dossier path
  resolves in the repository.
- Self-test: a deliberately broken record (killed, `kill_id: null`,
  tier `T9`) is correctly **rejected** — the validator bites.
- Frontmatter adoption scan over the named subset (this run's 9
  dossiers): **0/9 carry schema frontmatter.** The schema is
  prospective for dossiers; absence is reported as absence. The
  conformance claim covers the schema, the seed records, and the
  validator — nothing beyond.
