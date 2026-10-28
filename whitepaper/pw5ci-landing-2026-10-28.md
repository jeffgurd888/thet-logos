# PW-5c-i — Pairing and Per-Pattern Nonnegativity

*Landing dossier, 2026-10-28. Module:
`lean/ThetLogos/PhiAssembly.lean`, section
§PatternEvaluation appended (section strict 13, defs
12; module total strict 48; zero placeholders, zero
`native_decide`; main-tree build green, 3,558 jobs,
parent-verified; axiom sets exactly
`[propext, Classical.choice, Quot.sound]` on both
headlines). **Parts of the Clay Yang–Mills statement
closed by this landing: 0.** The assembly's first
half. It lands stronger than its brief: no per-class
case analysis was needed — a single uniform argument
shows every pattern moment's real part is
individually nonnegative.*

## What landed

- **Pairing.** At the diagonal, for any column set C
  and pattern t ⊆ C:
  `quadCharMoment C (C ∖ t) u u = star (quadCharMoment
  C t u u)` — the complementary pattern is the
  conjugate moment, at general (G, ρ), no
  irreducibility. The "reverse traversal" the
  scoping asked after lives here, inside the same
  quad, exactly as scoped.
- **Per-pattern nonnegativity.** For C ∈
  primitiveQuads at (Even N, 3 ≤ N), irreducible ρ,
  0 < d, every pattern t:
  0 ≤ (M_t + M_{C∖t}).re. The engine is a
  **row/column network separation**: in R1's
  expansion every factor splits as a row part times
  a column part; a reindexing swap identifies the
  column network as exactly the conjugate of the row
  network; hence each moment itself satisfies
  Re M_t = (d : ℝ)⁻¹⁴ · ‖RN‖² ≥ 0 — a single squared
  norm, per moment, before any pairing. The pairing
  headline above is the form the assembly consumes;
  the per-moment fact is stronger.
- **Corrections at full rank.** (1) The scoping's
  PLAQ/WRAP case split and its per-class Gram
  evaluations (all-mixed constant, J-twisted forms,
  ν = 0 vanishing) were **not needed** — the uniform
  separation subsumes them, including the ν = 0 case
  (the pair sum is 2·Re M_t regardless of ν). The
  scoping's end-form analysis stands as the reason
  the result was expected; the proof found a shorter
  road. (2) **K-PW-5-2 does not engage** — no class
  failed to be nonnegative, no seat evaluation owed.
  (3) The PW-5c brick was split (5c-i/5c-ii) after
  its first builder died on an output cap before
  writing; the tree was verified untouched and the
  split bricks carry pre-chewed interface packs —
  recorded here as process, not mathematics.

## What remains

PW-5c-ii, the endpoint: the baseline step (at
irreducible ρ, e1 = 0 by §5a's pack, so Φ_C =
quadReMoment C u u; the trivial-representation and
d = 0 cases discharged by §5a), the sum over
patterns via `phiFunctional_eq` (each quadReMoment
is 2⁻⁴ · Σ_t Re M_t ≥ 0 by this section), the sum
over primitive quads, and `phi_diag_nonneg` with its
κ₄ corollary. Scope fences unchanged: diagonal,
β⁴, irreducible ρ, even N ≥ 4; NO CLAIM; dials 0/4.

Census effect: 6,992 → **7,005 strict** /
7,070 → **7,083 attribute-inclusive** / modules
unchanged at **239**; the seven quarantined
placeholders are unchanged.

## Backers since last landing

No new backers inscribed in this interval; the roll
stands as recorded in `BACKERS.md`. Every gift is
published with the proof stream, named as the giver
wishes, amounts only with the giver's permission —
the standing reciprocity of this house.
