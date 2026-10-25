# Frontier brick — HDen DISCHARGE — LANDED STANDS T1 (full, general)

Date: 2026-10-25. Module: `LatticeHdenSeat` (46 strict / 11 defs).
Parent-verified: targeted build exit 0, olean present, zero sorry,
`#print axioms` on the headlines = [propext, Classical.choice,
Quot.sound] only. Census after landing: 5,290 strict / 5,339
attribute-inclusive / 176 modules.

## What stands
- `hden_all`: HDen — Q12's named hypothesis that the two-slice law has
  an L² density w.r.t. the product of the marginals — holds at GENERAL
  (G, ρ), every real β, every N ≥ 2. Not seat-specific, not β > 0 only:
  the weld's two-sided Gibbs bounds hold at every real β and the whole
  transport goes through generally.
- `gapBoundU1_unconditional`: Q12's per-instance spectral gap at the
  U(1) seat (β > 0, even N ≥ 2) is now assembled UNCONDITIONALLY —
  ∃ δ > 0 with the gap bound — from `gapBoundU1_of_weld` + this
  discharge. The only remaining carried datum is the Hilbert basis
  (FG-1's standing convention, named in the statement).

## Route
Partition scalar two-sided bounded by exp(±actionBound β) (the weld's
gibbsMeasure bounds on univ) ⇒ folded Gibbs density pointwise in
[exp(−2B), exp(2B)]; slice marginal density as a fiber integral in the
same window (bounded above AND away from 0); two-slice density via
prodAssoc reassociation and the sliceToCompl reindexing; explicit
kernel K(z,z′) = J̃(z,z′)/(M z · M z′) with values in
[0, exp(6·actionBound β)], measurable, hence L² by boundedness on a
finite measure space; form identity chained through the landed
two-slice law. The packaged Q12 theorem consumed the discharge exactly
as proved — no form mismatch.

## State of the seat (U(1), β > 0, even N)
Per-instance spectral theory of the transfer operator is COMPLETE:
compact (HDen discharged), spectrum discrete, vacuum unique
(D-1 weld), positivity whole-space (S2-3 + FG-1 audit), gap δ(β, N) > 0
with NO hypotheses left standing except the carried basis convention.
What remains open at the seat is exactly Item 3's wall: UNIFORMITY —
a floor on δ(β, N) as N varies ((U-vol)/(U-traj), formulated in FG-1,
unproved, (U-traj) carrying the T4 Coulomb-phase doubt). No continuum
object. NO CLAIM. Clay parts closed: 0. Dials 0/4.
