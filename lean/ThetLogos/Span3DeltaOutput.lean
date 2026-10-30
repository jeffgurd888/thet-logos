/-
# S3-4: Δ-as-output — the weakest statable implication (STATEMENT ONLY)

Brick S3-4 of the Span-3 first pier
(`routeb-general-scratch/scoping-span3-first-rung-2026-10-29.md`
§2, candidate (d); pack
`routeb-general-scratch/pack-s3-4.md`). Governing fence,
verbatim in force: **STATEMENT only — its proof is NOT
priced and must not be attempted under this order.** This
module contains definitions only: no theorem is stated or
proved here, and nothing below asserts that any antecedent
holds, that any limit system exists, or that the implication
is true.

**The statement.** The implication with owned antecedents:

**(UniformTrajectoryGap (G ρ) with floor m) ∧
(ScalingLimitOfLattice) → LimitGapClustering of the limit
system at rate m**

— Δ as a conclusion-shaped property of the limit's
correlation functions: the weakest form in which Δ is an
output rather than an input that does not require a
reconstructed Hamiltonian (rung 4's, FRONTIER). It is stated
below in two forms over S3-2's limit system, both consuming
the landed names by name and nothing else:

- `DeltaAsOutputAtFloor m` — the named-floor form: for an
  admissible trajectory `βt` satisfying S3-0's named-floor
  hypothesis `TrajectoryGapFloor βt m` with `m > 0`, IF the
  scaling-limit pin `ScalingLimitOfLattice` holds, THEN
  there is a limit system `S` — tied to `βt` by pointwise
  convergence of the rescaled finite correlations
  (`CorrelationsConvergePointwise`) and identified as an OS
  bundle's Schwinger data
  (`LimitSystemIsOSSchwingerData`) — such that `S` clusters
  with rate at least the **same** `m`
  (`LimitGapClustering S m`).
- `DeltaAsOutput` — the existential-floor form: IF S3-0's
  `UniformTrajectoryGap` holds AND the scaling-limit pin
  holds, THEN for every admissible trajectory under its
  per-instance package there exist a floor `m > 0` and a
  limit system `S` tied to the trajectory as above with
  `LimitGapClustering S m`. The floor here is the one
  `UniformTrajectoryGap` itself provides; no floor is
  invented by this module.

**The finite shadow.** `FiniteGapShadow` states, per fixed
`(β, N)`, the exact shape of the pier's one proved template:
`transfer_gap_of_formPos` (`LatticeTransferCompact`,
restated at general `(G, ρ)` as `gapBound_of_package` in
`Span3GapPins`) — under the per-instance package, a gap
bound `δ > 0` exists at fixed `N` with the Hamiltonian
already in hand. The implication above is its
continuum-shaped generalization: the fixed-`N` spectral gap
bound `δ` is replaced by the uniform physical floor
`m ≤ N · δ` carried along the trajectory, and the finite
spectral bound is replaced by exponential clustering of the
limit system's connected two-point function at rate `m`.
**The template's proof is NOT transferred:** this module
does not re-prove the shadow, does not cite the template as
a premise of the implication, and the implication does not
follow from the shadow by anything stated here.

**K-S3-4 — decided on the evidence: does NOT fire.** The
kill fires if a clustering-rate consequent cannot be stated
on S3-2's limit system in owned vocabulary (no rate, no
decay predicate on the limit correlations). It can be
stated, and is: S3-2 landed FULL (dossier
`whitepaper/s32-landing-2026-10-30.md`) and its
`LimitGapClustering` is exactly such a predicate — some
`C ≥ 0` bounds the limit system's connected two-point
function by `C · exp (−m · separation)` at every pair of
insertions, in the limit system's own values, with the same
named floor `m` as the trajectory hypothesis. The consequent
below is therefore the full clustering consequent, NOT the
weakened finite-volume floor; the PARTIAL fallback (the
implication shipped with S3-0's floor restated as its own
consequent, and the finding that Δ-as-output has no statable
weakest form beyond the finite template in current
vocabulary) is NOT taken, and that finding is NOT made.

**Tree-defect note.** This module sits on the transfer side
of the `reflSite_eq_torusShift_zero` duplicate seam recorded
in `Span3GapPins`' header: it imports `Span3ScalingLimit`
(which imports `Span3GapPins`, `LatticeCorrelations`, and
`OsterwalderSchrader`), none of which pulls in the
`PlaneCrossingFactor` chain, and it does not import the
polymer side.

**Fences.** STATEMENT ONLY — no proof attempted, none
priced, none implied to be near. Proof-grade distance
toward the continuum covered here is **ZERO**. The pier's
frontier / Span-3 vocabulary remains unspent and appears
nowhere below as a name. **NO CLAIM** — parts of any Clay
statement closed by this module: 0. Dials: 0/4.
-/

import ThetLogos.Span3ScalingLimit

namespace ThetLogos

open MeasureTheory

section Span3DeltaOutput

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)

/-! ## The finite shadow: the template's shape at fixed `N` -/

/-- **The finite shadow the implication generalizes —
STATEMENT of the template's shape only.** At fixed coupling
`β` and fixed volume (every even `N ≥ 2`), under the
per-instance package (`GapPackage` — compactness plus the
named hypothesis `TransferFormPos`, exactly what the
template consumes), there exists a gap bound `δ > 0`:
every spectral point of the transfer operator other than
the vacuum eigenvalue `1` has norm at most `1 − δ`
(`GapBound`). This is exactly the output shape of the
landed theorem `transfer_gap_of_formPos`
(`LatticeTransferCompact`), restated at general `(G, ρ)`
by `gapBound_of_package` (`Span3GapPins`) — **the pier's
one proved template**, with the Hamiltonian already in
hand at fixed `N`. It is recorded here as a `Prop` so the
generalization below has its shadow on the same page.
This module does **not** prove it, does **not** cite it as
a premise of the implication, and transfers **none** of
its proof to the limit: the continuum-shaped statement
below stands as a statement, exactly as priced. -/
def FiniteGapShadow (β : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (hN2 : 2 ≤ N) (_hN : Even N),
    GapPackage μG ρ hρcont hd β hN2 →
    ∃ δ : ℝ, 0 < δ ∧ GapBound μG ρ hρcont β hN2 δ

/-! ## The implication: Δ as an output of the limit -/

/-- **S3-4, named-floor form — Δ-as-output, weakest
statable implication. STATEMENT ONLY; not proved, not
priced for proof, not implied to be near.** For every
admissible trajectory `βt` (S3-0's `AdmissibleTrajectory`,
with its nondegeneracy fence) and every floor `m > 0` such
that `βt` satisfies the named-floor hypothesis
`TrajectoryGapFloor βt m` — **the floor half of S3-0's
`UniformTrajectoryGap`, consumed by name, not
discharged** — IF the scaling-limit pin
`ScalingLimitOfLattice` (S3-2, consumed by name) holds,
THEN there exist a limit correlation system `S` and an
`OsterwalderSchraderAxioms` bundle such that the rescaled
finite correlations along `βt` converge to `S` pointwise
on stated test configurations
(`CorrelationsConvergePointwise`), `S` is identified as
the bundle's Schwinger data
(`LimitSystemIsOSSchwingerData`, by reference to the S-3
pin, its opacity inherited), and **`S` clusters with rate
at least the same `m`**: `LimitGapClustering S m` — some
`C ≥ 0` bounds `S`'s connected two-point function by
`C · exp (−m · separation)` at every pair of insertions.
The gap appears only in the consequent, as a property of
the limit's correlation functions: that is the sense in
which Δ is an output here rather than an input. No
reconstructed Hamiltonian is required or mentioned. -/
def DeltaAsOutputAtFloor (m : ℝ) : Prop :=
  ∀ βt : ℕ → ℝ, AdmissibleTrajectory βt →
  0 < m → TrajectoryGapFloor μG ρ hρcont hd βt m →
  ScalingLimitOfLattice μG ρ hρcont hd →
  ∃ S : LimitCorrelationSystem, ∃ os : OsterwalderSchraderAxioms,
    CorrelationsConvergePointwise μG ρ βt S ∧
    LimitSystemIsOSSchwingerData S os ∧
    LimitGapClustering S m

/-- **S3-4, existential-floor form — Δ-as-output with the
antecedents in exactly the pack's shape. STATEMENT ONLY;
not proved, not priced for proof.** IF S3-0's
`UniformTrajectoryGap` (consumed by name) holds AND
S3-2's `ScalingLimitOfLattice` (consumed by name) holds,
THEN for every admissible trajectory `βt` under the
per-instance package at every point of the trajectory
there exist a floor `m > 0` — the floor
`UniformTrajectoryGap` itself provides for `βt`, named
here, not invented — and a limit correlation system `S`
and an `OsterwalderSchraderAxioms` bundle such that the
rescaled finite correlations along `βt` converge to `S`
pointwise on stated test configurations, `S` is
identified as the bundle's Schwinger data, and `S`
clusters with rate at least `m` (`LimitGapClustering`).
This is the pack's implication — (uniform trajectory gap
with floor `m`) ∧ (scaling limit) → (limit-gap clustering
at rate `m`) — with the limit system in the consequent
tied to the trajectory by the convergence and
identification clauses, so the clustering is asserted of
*the* limit system of `βt`, not of an unrelated system.
Nothing here asserts either antecedent, and no existence
of any trajectory, floor, limit system, or bundle is
asserted unconditionally. -/
def DeltaAsOutput : Prop :=
  UniformTrajectoryGap μG ρ hρcont hd →
  ScalingLimitOfLattice μG ρ hρcont hd →
  ∀ βt : ℕ → ℝ, AdmissibleTrajectory βt →
    (∀ (N : ℕ) [NeZero N] (hN2 : 2 ≤ N) (_hN : Even N),
      GapPackage μG ρ hρcont hd (βt N) hN2) →
    ∃ m : ℝ, 0 < m ∧
      ∃ S : LimitCorrelationSystem, ∃ os : OsterwalderSchraderAxioms,
        CorrelationsConvergePointwise μG ρ βt S ∧
        LimitSystemIsOSSchwingerData S os ∧
        LimitGapClustering S m

end Span3DeltaOutput

end ThetLogos
