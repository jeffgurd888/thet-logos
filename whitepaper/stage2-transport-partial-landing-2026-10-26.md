# Completion Transport — PARTIAL, by the Pre-Registered Slip

*Landing dossier, 2026-10-26. Module: `lean/ThetLogos/SliceTransport.lean`
(strict 12, defs 2, zero `sorry`, zero `native_decide`; main-tree build
green, 3,693 jobs). **Parts of the Clay Yang–Mills statement closed by
this landing: 0.***

## The errand

The honest battery's correspondence (`SliceSpectralCorrespondence`)
had exactly one open conjunct after FG-2c-4: the **gap clause** —
carry the pre-completion operator's spectral gap to the completed
operator's pairings, `⟪x, T̂_c x⟫.re ≤ 1 − δ`. The 2026-10-26 scoping
priced the transport **M** by an elementary Route A in three
packages, with a pre-registered slip: if the functional calculus at
the pre-completion operator fights instance synthesis, package A2
re-prices to L and A1 + A3 land as PARTIAL. **The slip is what
happened** — this dossier reports the partial at the same volume a
full landing would get.

## What landed (all parent-verified on the shipped text)

- **A1 — the completed weld (FULL).** `sliceWeldCompleted`, the weld
  extended to the completion by density: intertwining
  (`W_c ∘ T̂_c = transferOp ∘ W_c`), the twisted form identity
  (`⟪W_c u, W_c v⟫ = ⟪u, T̂_c v⟫`), vacuum-to-vacuum, and the moment
  identifications `‖W_c y‖² = b₁`, second moment `= b₂`, with
  orthogonality preserved.
- **A3 — the moment step (FULL).** `sliceTransport_moment_sq`:
  `b₁² ≤ b₂`, from the landed defect-moment recursion at j = 2 and
  the expansion `a₂ = 1 − 2b₁ + b₂`. (The functional calculus at the
  *completed* operator works fine.)
- **A2 — spectrum half (FULL).** The bump `sliceGapBump` and
  `transferOp_spectrum_dichotomy_circle`: every real spectral point
  of the pre-completion operator is 1 or ≤ 1 − δ, from `GapBoundU1`
  alone.

Headline axiom checks (A1 core, dichotomy, A3): exactly
`[propext, Classical.choice, Quot.sound]` each.

## The obstruction, named exactly (machinery, not math)

A2's remaining step — apply the bump through the continuous
functional calculus at `transferOp` on `osSpace` — stops at instance
synthesis in the pin (Mathlib v4.35.0-rc3):
`ContinuousFunctionalCalculus ℝ (osSpace →L[ℂ] osSpace) ?p` does not
synthesize, although every hypothesis of the generic instance
synthesizes standalone for this algebra, and the same synthesis
succeeds for the completed operator's algebra. One branch loops
through an Lp-coercion seminormed-group instance. Hand-supplying the
instance fails on a definitional mismatch: the generic instance's
spectrum-restriction predicate uses the `StarRing`-derived star,
which is not definitionally equal to `ContinuousLinearMap.instStarId`,
so the resulting calculus does not typecheck against the corpus's own
`IsSelfAdjoint (transferOp …)`. This is a **machinery wall in the
pin**, not a counterexample and not a math kill.

## What remains open, exactly

One step: the osSpace quadratic-form gap
`Re ⟪z, transferOp z⟫ ≤ (1 − δ)‖z‖²` for `z ⊥ Ω`, by a route that
does not need `cfc` at `transferOp`. The scoping's fallback —
**Route A′ (compact spectral decomposition)** — is priced **L** and
is the named continuation; the spectrum dichotomy above is its first
ingredient and is already landed. The battery correspondence stays a
carried hypothesis until A′ or a pin upgrade closes this step;
nothing in this dossier discharges it.

Per-(β, N) only, β > 0 — uniform in nothing, as scoped.

## Census effect

Strict 5,788 → **5,800**; attribute-inclusive 5,855 → **5,867**;
modules 188 → **189**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
