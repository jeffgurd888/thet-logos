import ThetLogos.DoeblinGap
import ThetLogos.LatticeVacuumSimple
import ThetLogos.LatticeUniformGap

/-!
# ThetLogos.FixedZeroPost — the Fixed Zero Question post

**Status: definitions only. NO CLAIM.**

Jeff Gurd's sentence (2026-10-18, verbatim):

> "Measuring the river of gravity and the paths light-water
> follows is to find an ultimate fixed zero point that holds
> the river together."

and his own correction of the same evening, which governs
every reading below: *"the teetertotter is not stationary"* —
the fixed zero is the pivot, the fulcrum the motion turns
around, not a freezing of the motion. The question that
sentence carries was formulated by Jeff on 2026-10-18, and
is posted here in his words:

> "Is there one zero that all the finite zeros are shadows
> of — a vacuum of the limit itself, holding a moat of
> positive width — or does the stillness dissolve exactly
> where the nesting never ends?"

**The finite pattern, as owned data.** For each finite box
of the corpus (general `(G, ρ)`, every real `β`, `2 ≤ N`)
the pattern below is landed, not hoped for: the vacuum is
fixed (`transferOp_vacuum`, LatticeTransfer); the fixed
space of the transfer operator is exactly the vacuum line
(`fixed_mem_span`, LatticeVacuumSimple — this is clause
(b) of the named package `TransferFormPos`, discharged at
general `(G, ρ)` by the D-1 weld's form-improvement route);
and everything orthogonal to the vacuum is contracted in
form by `1 − δ₀` with `δ₀ = doeblinDelta β > 0`
(`transfer_form_compression`, `doeblinDelta_pos`,
DoeblinGap). The moat's width is explicit —
`δ₀ = exp (−192 |β| N⁴)` at the volume normalization
(`actionBound_eq_volume`) — so each finite zero holds a
moat of positive width, and the owned widths have infimum
`0` over `N`. That tension is exactly what the question
asks about: the stillness is real in every box and the
moat around it is not yet known to survive the nesting.

**The answering statements.** This post names both answers
as answers and leans toward neither. YES, in the strongest
form statable over owned data, is the corpus's owned
trajectory-uniformity statement `UniformTrajectoryGapU1`
((U-traj), FG-1, LatticeUniformGap): along every
admissible trajectory the per-box moats keep a positive
physical floor. The full YES of Jeff's question — a
continuum limit object, obtained by reconstruction, whose
vacuum is that floor's ground — additionally requires the
reconstruction half, which is built nowhere in the corpus:
answering the question IS ladder Steps 3–5 (uniformity,
the trajectory, the continuum limit). NO is the closing of
the moat along the trajectory, stated below over the same
owned FG-1 data (`AdmissibleTrajectoryU1`, `GapPackageU1`,
`GapBoundU1`). Two honesty notes ride with the post, both
already on the corpus's face: the trajectory language is
owned only at the U(1) seat (FG-1's formulations are
seat-level, while the finite pattern above is general);
and (U-traj) carries a standing [T4] Coulomb-phase doubt
at that seat, recorded in LatticeUniformGap — formulability
is not truth, in either direction.

**Fences.** This post is the Yang–Mills
uniformity/continuum problem restated in the program's
first person; it is not a statement about gravitation.
The word for gravitation appears in this module only
inside Jeff's attributed quotation above. The river line's
standing kill condition (K-RIVER-3) rides on its face: any
presentation of this post, or of the finite fixed-point
content it records, as a gravity result is killed on
sight — the identification of the owned flows with a
gravitational river is Jeff's T5 image, quotable and
attributed, never citable as a derivation. Dial 2 (a
gravity object surviving audit) is unmoved by this post;
parts of any Clay statement closed by it: 0.

This module contains definitions only: no theorem, no
proof obligation discharged, and no placeholder.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- **The finite fixed-zero pattern** (definition; a posted
pattern over owned data, not a theorem).

At general `(G, ρ)`, every real `β`, `2 ≤ N`: the transfer
operator's fixed space is exactly the vacuum line, and the
form contracts on the vacuum-orthogonal complement by
`1 − doeblinDelta β`. Both conjuncts are the statement
shapes of landed theorems — `fixed_mem_span`
(LatticeVacuumSimple) and `transfer_form_compression`
(DoeblinGap), with `doeblinDelta_pos` giving the width's
positivity in each box. This definition states the
pattern; it does not re-prove it. -/
def fixedZeroFinitePattern (β : ℝ) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d) :
    Prop :=
  (∀ v : osSpace (N := N) μG ρ β,
    transferOp μG ρ hN2 hρcont β v = v →
    v ∈ Submodule.span ℂ {osVacuum (N := N) μG ρ hρcont hd β}) ∧
  (∀ f : osSpace (N := N) μG ρ β,
    inner ℂ (osVacuum (N := N) μG ρ hρcont hd β) f = 0 →
    ‖inner ℂ f (transferOp μG ρ hN2 hρcont β f)‖
      ≤ (1 - doeblinDelta (N := N) β) * ‖f‖ ^ 2)

/-- **The YES answer-shape** (definition; a posted
answer-shape, not a theorem).

The corpus's owned trajectory-uniformity statement
(U-traj) under the name the Fixed Zero Question gives it:
along every admissible trajectory, under the per-instance
package, the per-box moats keep a positive physical floor
`m` — the stillness has a vacuum in the limit whose moat
does not close. This is the strongest YES statable over
owned data; the question's full YES also demands a
continuum limit object with reconstruction, which is
unbuilt. This definition asserts neither. -/
def fixedZeroYes : Prop :=
  UniformTrajectoryGapU1

/-- **The NO answer-shape** (definition; a posted
answer-shape, not a theorem).

Over the same owned FG-1 data, with (U-traj)'s antecedents
mirrored: for every admissible trajectory, under the
per-instance package at every point of it, every proposed
physical floor `m > 0` fails somewhere — there are
arbitrarily large even `N` on the trajectory at which
every packaged gap bound `δ` has `(N : ℝ) * δ < m`. The
moat closes where the nesting never ends. Under the
package this shape contradicts `fixedZeroYes`; the post
asserts neither shape. -/
def fixedZeroNo : Prop :=
  ∀ βt : ℕ → ℝ, AdmissibleTrajectoryU1 βt →
    (∀ (N : ℕ) [NeZero N] (hN2 : 2 ≤ N) (_hN : Even N),
      GapPackageU1 (βt N) hN2) →
    ∀ m : ℝ, 0 < m →
      ∃ (N : ℕ) (hNe : NeZero N) (hN2 : 2 ≤ N) (_hN : Even N),
        ∀ δ : ℝ, @GapBoundU1 (βt N) N hNe hN2 δ → (N : ℝ) * δ < m

/-- **The Fixed Zero Question** (definition; the posted
question, not a theorem).

Jeff's question in the only shape in which the corpus can
currently ask it: whether the moat survives the nesting
(`fixedZeroYes`) or closes along every trajectory
(`fixedZeroNo`). The post asserts neither disjunct, and
asserts nothing about which answer-shape is true; whether
even this disjunction is the right frame is part of what
answering the question — ladder Steps 3–5 — would settle. -/
def fixedZeroQuestion : Prop :=
  fixedZeroYes ∨ fixedZeroNo

end ThetLogos
