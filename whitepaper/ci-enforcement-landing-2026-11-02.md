# CI ENFORCEMENT LANDING — zero-sorry gate + axiom fence + README census repair — 2026-11-02

Jeff's order (2026-11-01 23:04 EST, "fire 1→4"), vector 1 of the audited
upgrade list. NO CLAIM; dials 0/4; census unchanged by this ship
(12,641 strict / 13,153 total / 445 modules, zero sorrys).

## What shipped

1. **`.github/workflows/lean-ci.yml`** — installed (from the parent's
   2026-11-01 draft, with the fence step made real; see Defects below).
   On every push/PR touching `lean/**`: elan install (pinned toolchain),
   Mathlib cache, root-library build, zero-sorry gate, registry-module
   build, axiom fence.
2. **`lean/scripts/axiom-fence.txt`** — the headline registry. Format:
   `import` lines name the owning module; bare lines are declarations
   checked with `#print axioms`. Admission rule (on the file's face):
   a declaration is listed only after local verification that it exists
   and passes. Seeded with 21 declarations: the successor-run headlines
   (Dual-Current F1–F3, BSD3-2R sweep + assembly, CLS-2G, CLS-3c-A) plus
   the disc-spectral-mapping and finite-Maxwell landmarks.
3. **`lean/scripts/run_axiom_fence.py`** — assembles the check file from
   the registry, runs it under `lake env lean`, and fails unless every
   registered declaration's axiom set ⊆ {propext, Classical.choice,
   Quot.sound} (sorryAx or anything else fails).
4. **`lean/scripts/check_no_sorry.py`** — the zero-sorry source gate.
   Strips line/block comments (nested, incl. docstrings) and string
   literals, then searches for `sorry` in code position only.
5. **README census repair (housekeeping in this ship)** — badge and body
   now read the verified ledger figures **12,641** declarations across
   **445** counted modules (were: 12,592 across a stale "360").

## Local verification (all before push)

- **Axiom fence: PASS, 21/21.** Every registered declaration's axiom set
  is exactly [propext, Classical.choice, Quot.sound] on the current tree.
- **Zero-sorry gate: PASS** on all 460 files under `lean/ThetLogos/`;
  **bite test PASS** — the gate correctly FAILS (exit 1) on a synthetic
  file containing a real `sorry`, and does NOT flag the docstring prose
  at `CharpolyFactor.lean:31` ("sorry/admit/axiom = 0/0/0").
- **Registry module build: green** (`lake build` over the 9 registry
  modules, 3980 jobs). Workflow YAML parses.

## Defects found in the draft, fixed in the installed version

- The draft's fence step appended bare `#print axioms` lines to a check
  file with **no imports** — it could never have resolved a single
  declaration (and `import ThetLogos` alone is insufficient: the root
  module imports only 15 core modules; the registry therefore carries
  per-module `import` lines).
- The draft's grep gate (`^\s*sorry\b`) false-positives on docstring
  prose (CharpolyFactor.lean:31); replaced by the comment/string-aware
  source gate above.
- Two registry headlines live under nested namespaces
  (`ThetLogos.DialOneSwapOrbitGroupLaw.*`,
  `ThetLogos.DialOneAntiparticleBase.*`); the registry carries the true
  full names. (First fence run reported them NOT REPORTED; root cause
  identified and fixed — including a parser edge case: declaration names
  containing an apostrophe, `discFactorisationHyp'_proved`, are matched
  literally, not by a name regex.)

## Coverage, stated honestly

CI enforces: source-level zero-sorry across ALL Lean sources; compiled
axiom fence over the registry (9 modules and their transitive closure);
the root library build. A from-scratch compile of all ~460 modules is
priced in hours and is NOT run by CI — it remains a local parent-ceremony
gate. The registry is seeded, not exhaustive: growing it is cheap
(one local fence run per admission) and is the intended path.

## Census reconciliation gap (logged, not papered over)

The census is a ledger over the program's COUNTED modules carried by
verified per-landing increments (method note in README; adopted
2026-10-17). A whole-tree raw count by the same per-file rule reads
13,259 strict / 454 files — a remainder of 15 files / 667 strict sits
in-tree outside the counted chain. The remainder set could not be
uniquely identified from the records and NO candidate set is certified.
The README repair in this ship uses the ledger figures (12,641 / 445),
which are the ceremony-verified numbers; the gap stays on the record
until a dedicated reconciliation pass closes it.
