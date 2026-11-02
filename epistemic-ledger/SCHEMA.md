# Epistemic Ledger — machine-readable schema (mapping note)

Landed 2026-11-02 under Jeff's "fire 1→4" order, vector 4. This note is
the human companion to `ledger-entry.schema.json`; the validator is
`validate_ledger.py`; seed records live in `records/`.

## What the schema is for

`LEDGER.md` is the human ledger: prose and tables, per-component. The
schema gives the same verdicts a machine-readable mirror so tooling
(the axiom graph, future CI checks, census audits) can consume them
without scraping prose. A record exists per *ledgered claim* — one
claim, one verdict, one record.

## Field mapping (schema field ↔ repository structure)

| Field | Meaning | Repository anchor |
|---|---|---|
| `id` | stable slug | unique across `records/` |
| `tier` | T1–T5 per `TIERS.md` (framework §5) | `epistemic-ledger/TIERS.md` |
| `claim` | the claim at its tier, 1–2 sentences | the dossier's headline statement |
| `status` | `standing` / `killed` / `partial` / `frontier` | the landing's verdict |
| `evidence` | qualifier per TIERS.md convention ("Lean proof", "numerical", "audit memo", …) | dossier face |
| `date` | verdict date | landing date |
| `kill_id` | `K-…` identifier; **required iff `status` is `killed`** | the line's kill registry (charter / scoping) |
| `census_at_landing` | `{strict, total, modules}` corpus census at the landing; nulls are explicit unknowns, never estimates | pipeline log census chain |
| `module` | owning Lean module path or null | `lean/ThetLogos/*.lean` |
| `dossier` | whitepaper dossier path or null | `whitepaper/*.md` |

All fields are required keys; "none" is said with an explicit `null`,
so a missing module or unrecorded census is data, not silence.

## ⚠ Tier-dialect warning (read before consuming `tier`)

Two dialects coexist in this repository and they are NOT the same
numbering:

- **`TIERS.md` (framework §5)** — the ledger's own table: T1 assumed
  primitives, T2 defined operations, T3 proved/checked, T4
  emergent/standard, T5 open/withdrawn. **The schema's `tier` field
  uses THIS dialect**, because the schema lives beside TIERS.md and
  mirrors LEDGER.md.
- **Pipeline-log shorthand** — the bench's working verdicts speak of
  "T1" for Lean-proved headline grade, "T2" for labeled inputs, "T5"
  for seeings. A Lean-proved theorem is T3 under the schema's dialect
  but "T1" in pipeline shorthand.

Records also carry the `evidence` qualifier ("Lean proof", "Lean
refutation", …) precisely so a consumer can recover the fact without
depending on the tier dialect. Do not merge the two dialects silently;
this divergence is a known, recorded hazard, not an oversight to be
quietly "fixed" by relabeling either side (relabeling rule).

## Dossier frontmatter (prospective adoption)

A whitepaper dossier MAY carry its ledger record as frontmatter: a
leading `---` fence containing ONE JSON object (a YAML subset, so the
block stays valid YAML) conforming to the schema. The validator scans
for it. Adoption is prospective: dossiers written before this schema
do not carry it, and the validator reports that as absence.

## Conformance at landing (validator run, 2026-11-02)

- Schema: valid JSON Schema (draft 2020-12).
- Seed records: **5/5 conform** (2 standing, 2 killed, 1 frontier —
  spanning a Lean proof, a Lean refutation, an audit kill, and an open
  frontier statement); every referenced module/dossier path resolves.
- Self-test: a deliberately broken record (killed with `kill_id: null`,
  tier `T9`) is correctly REJECTED.
- Frontmatter adoption over the named subset of this run's 9 dossiers:
  **0/9 carry frontmatter** — reported as adoption state, not spun as
  conformance. The schema's conformance claim covers the schema, the
  records, and the validator's bite — nothing more.
