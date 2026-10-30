/-
# S3-2: the scaling-limit pin — what a continuum limit of THIS theory would assert

Brick S3-2 of the Span-3 first pier
(`routeb-general-scratch/scoping-span3-first-rung-2026-10-29.md` §2,
candidate (a); pack `routeb-general-scratch/pack-s3-2.md`).
Statement only, in the BSD-pin pattern: this module states the
`Prop` `ScalingLimitOfLattice` over owned objects only. It
asserts that nothing exists: it states what a continuum limit
of this lattice theory WOULD assert, conditional on labeled
hypothesis fields. Every future continuum claim in this
program is measured against this pin, never against a
weakening.

**The three clauses.** There is a system of rescaled finite
correlation functions (the finite `k`-point Wilson-loop
correlations of `LatticeCorrelations` / `LatticeGauge`, on the
concrete torus `Fin 4 → ZMod N` with shifts `torusShift N`,
along a trajectory `βt` at spacing `a = 1/N` — the rescaling
read as in `AdmissibleTrajectoryU1`'s fence and in S3-0's
`AdmissibleTrajectory`) such that:

- (i) `βt` is admissible and satisfies the trajectory floor
  with a named floor `m > 0`: both ride as **HYPOTHESIS
  fields, labeled** — S3-0's `UniformTrajectoryGap`
  (`ThetLogos.Span3GapPins`) is consumed, not discharged, and
  `TrajectoryGapFloor` below is exactly its consequent-shape
  with the existential floor named `m` (the naming is proved
  to be a restatement: `trajectoryGapFloor_of_uniform`).
  `m > 0` sits on the hypothesis side of the line, per the
  memo's honest-form ruling: a limit with `m = 0` is the
  free/trivial case, and this pin does not assert it away.
- (ii) the rescaled correlations converge to a limit system
  in the weakest convergence sense this corpus can state
  without distribution infrastructure, picked and labeled as
  such on the face: **pointwise convergence on stated test
  configurations** — for each fixed finite family of loop
  insertions (`LoopInsertion`: a rational physical position in
  the unit 4-torus and a fixed list of lattice `Step`s, i.e. a
  pointlike probe whose lattice shape does not grow with `N`)
  and each `ε > 0`, the finite correlations at all large even
  `N` are within `ε` of the limit value. No uniformity in the
  configuration, no rate, no distribution pairing is stated,
  because none is statable in owned vocabulary today.
- (iii) the limit system is identified as an
  `OsterwalderSchraderAxioms` bundle's Schwinger data, by
  reference to the S-3 pin (`ThetLogos.OsterwalderSchrader`):
  the bundle's `SchwingerMarker` carrier is named to be the
  limit correlation system's type. **The S-3 pin's opacity is
  inherited and labeled:** its E0–E4 fields are opaque `Prop`s,
  no analytic content about the limit system is asserted by
  the identification, and the identification is at
  marker/type level only — the same level at which the S-3
  pin itself ties data (compare brick S3-3's repair brief).

**K-S3-2 (vacuity) — decided on the evidence: does NOT fire.**
The kill fires if the floor cannot be grammatically attached
to the limit system in owned vocabulary, leaving a pin a
degenerate constant limit could satisfy with the floor doing
no work. It can be attached, and is: `LimitGapClustering`
states, on the limit system itself, that the connected
two-point function is bounded by `C · exp (−m · separation)`
for the **same** `m` as hypothesis (i), with separation the
owned ℓ¹ torus distance between the insertions' physical
positions. A constant limit system with nonzero connected
two-point function violates this at large separation, so the
floor does work on the limit. The attachment is a component
of clause (iii) (the identified limit system is a *gapped*
one), and it is the weakest grammatical attachment available:
it uses only the limit system's own values, the named floor,
and an owned distance. Note for the pier's later brick:
S3-4's consequent is this same clustering predicate, stated
there as an implication; this pin names the predicate and
fixes its form, and S3-4 consumes it by name.

**K-S3-2b (infrastructure) — decided on the evidence: does
NOT fire.** Stating (ii) needs a limit-object type. The one
used here, `LimitCorrelationSystem`, is a plain function type
over owned types (`LoopInsertion` is built from rational
positions and owned `Step` lists; the system's values are
complex numbers). It is not a marker and smuggles no content:
no axiom, bound, or symmetry is baked into the type — every
property the pin wants of the limit is stated as a separate
clause. No distribution space, nuclear space, or continuum
field type is introduced or needed.

**Tree-defect note.** This module sits on the transfer side
of the `reflSite_eq_torusShift_zero` duplicate seam recorded
in `Span3GapPins`' header: it imports `Span3GapPins`,
`LatticeCorrelations`, and `OsterwalderSchrader`, none of
which pulls in the `PlaneCrossingFactor` chain, and it does
not import the polymer side.

**Fences.** The pin states what a continuum limit WOULD
assert — nothing is asserted to exist; no trajectory is
asserted to satisfy the hypotheses; no convergence is
asserted to hold. Proof-grade distance toward the continuum
covered here is **ZERO**. The pier's frontier / Span-3
vocabulary remains unspent and appears nowhere below as a
name. **NO CLAIM** — parts of any Clay statement closed by
this module: 0. Dials: 0/4.
-/

import ThetLogos.Span3GapPins
import ThetLogos.LatticeCorrelations
import ThetLogos.OsterwalderSchrader

namespace ThetLogos

open MeasureTheory

section Span3ScalingLimit

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)

/-! ## Test configurations and the finite correlation system -/

/-- **A loop insertion: one stated test configuration atom.**
A Wilson loop used as a probe of the scaling limit, described
in physical (rescaled) terms: a position `pos` in the unit
4-torus (rational coordinates in `[0, 1)`) and a fixed list of
lattice steps. The step list does not grow with `N`, so at
spacing `a = 1/N` the insertion is pointlike — a local probe
at a physical position. This is the stated test configuration
of clause (ii): convergence is demanded configuration by
configuration for exactly these atoms (and finite families of
them), nothing stronger. -/
structure LoopInsertion where
  /-- Physical position in the unit 4-torus. -/
  pos : Fin 4 → ℚ
  /-- Positions are coordinates in `[0, 1)`: lower bound. -/
  pos_nonneg : ∀ μ, 0 ≤ pos μ
  /-- Positions are coordinates in `[0, 1)`: upper bound. -/
  pos_lt_one : ∀ μ, pos μ < 1
  /-- The fixed lattice shape of the probe. -/
  steps : List Step

/-- **The lattice site of a physical position at level `N`:**
the site nearest below `N · pos` in each coordinate, read in
`ZMod N` — the rescaling `a = 1/N` made concrete. Definition
only; no approximation property is claimed for it here. -/
def rescaledSite (N : ℕ) (x : Fin 4 → ℚ) : Fin 4 → ZMod N :=
  fun μ => ((⌊(N : ℚ) * x μ⌋₊ : ℕ) : ZMod N)

/-- **The finite correlation system at level `N` along
`βt`.** The `k`-point function of the loop insertions
`c : Fin k → LoopInsertion`: the Gibbs expectation, at
coupling `βt N` on the torus `Fin 4 → ZMod N` with shifts
`torusShift N`, of the product of the Wilson loops of the
insertions placed at their rescaled sites. Assembled from
owned objects only: `gibbsExpect` and `wilsonLoop`
(`LatticeGauge`), the same expectation whose two-point
specialization is `wilsonTwoPoint` (`LatticeCorrelations`).
At fixed `N` this is a finite-lattice correlation in exactly
that module's sense — no decay, clustering, or limit is
asserted by the definition. -/
noncomputable def finiteCorrelation (βt : ℕ → ℝ) (N : ℕ) [NeZero N]
    (k : ℕ) (c : Fin k → LoopInsertion) : ℂ :=
  gibbsExpect (torusShift N) μG ρ (βt N)
    (fun U => ∏ i : Fin k, wilsonLoop (torusShift N) ρ U
      (rescaledSite N (c i).pos) (c i).steps)

/-! ## The limit system and the weakest convergence -/

/-- **A limit correlation system.** A system of would-be
continuum correlation values: one complex number for every
finite family of loop insertions. This is a plain function
type over owned types — **not a marker** (K-S3-2b, module
header): the type carries no axioms, bounds, or symmetries,
and every property the pin requires of a limit system is
stated as a separate clause below. Its values are what clause
(iii) identifies as an `OsterwalderSchraderAxioms` bundle's
Schwinger data. -/
def LimitCorrelationSystem : Type :=
  ∀ k : ℕ, (Fin k → LoopInsertion) → ℂ

/-- **Pointwise convergence on stated test configurations —
the weakest convergence sense this corpus can state without
distribution infrastructure, picked and labeled as such.**
Along the trajectory `βt`, the finite correlations
`finiteCorrelation` converge to the limit system `S` if for
every fixed number `k` of insertions, every fixed family
`c` of insertions, and every `ε > 0`, the finite correlation
at every even `N ≥ 2` past some threshold is within `ε` of
`S k c`. No uniformity over configurations, no convergence
rate, and no pairing against test functions is stated:
none is statable in owned vocabulary today, and the pin
deliberately asks for no more than this. -/
def CorrelationsConvergePointwise (βt : ℕ → ℝ)
    (S : LimitCorrelationSystem) : Prop :=
  ∀ k : ℕ, ∀ c : Fin k → LoopInsertion, ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ (N : ℕ) [NeZero N], N₀ ≤ N → Even N → 2 ≤ N →
      ‖finiteCorrelation μG ρ βt N k c - S k c‖ < ε

/-! ## The floor, attached to the limit system -/

/-- **Physical separation of two insertions:** the ℓ¹ distance
between their positions on the unit 4-torus (each coordinate
contributes its circular distance `min (|x − y|, 1 − |x − y|)`
in ℝ). Owned vocabulary only: rational positions cast to ℝ,
finite sum over `Fin 4`. Definition only; no metric property
is claimed for it here. -/
noncomputable def insertionSeparation (a b : LoopInsertion) : ℝ :=
  ∑ μ : Fin 4, min (|(a.pos μ : ℝ) - (b.pos μ : ℝ)|)
    (1 - |(a.pos μ : ℝ) - (b.pos μ : ℝ)|)

/-- **The connected two-point function of a limit system:**
the two-point value minus the product of the one-point
values, in the limit system's own values — the limit-side
analogue of `wilsonTwoPointConnected` (`LatticeCorrelations`). -/
noncomputable def limitConnectedTwoPoint (S : LimitCorrelationSystem)
    (a b : LoopInsertion) : ℂ :=
  S 2 (fun i : Fin 2 => if i = 0 then a else b)
    - S 1 (fun _ => a) * S 1 (fun _ => b)

/-- **The floor `m`, grammatically attached to the limit
system (the K-S3-2 attachment).** A limit system clusters
with rate at least `m` if some constant `C ≥ 0` bounds its
connected two-point function by `C · exp (−m · separation)`
at every pair of insertions. This is a property of the limit
system's own values, stated in owned vocabulary; it is what
makes the hypothesis floor of clause (i) do work on the
limit: a constant limit system whose connected two-point
function does not vanish violates it at large separation.
No clustering of any finite-volume correlation is asserted
by this definition. -/
def LimitGapClustering (S : LimitCorrelationSystem) (m : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ a b : LoopInsertion,
      ‖limitConnectedTwoPoint S a b‖
        ≤ C * Real.exp (-m * insertionSeparation a b)

/-! ## Clause (i): the trajectory floor, as a labeled hypothesis -/

/-- **The trajectory floor with the floor named `m`:
clause (i)'s hypothesis field.** Under the per-instance
package (`GapPackage` — compactness plus the named hypothesis
`TransferFormPos`, exactly as S3-0's `UniformTrajectoryGap`
consumes it) at every point of the trajectory, the packaged
gap at every even `N ≥ 2` can be chosen normalized (`δ ≤ 1`)
with `m ≤ N · δ` — the physical floor `δ / a ≈ N · δ` of
S3-0, with its existential floor given the name `m` so the
**same** `m` can be attached to the limit system in
`LimitGapClustering`. This is a hypothesis of the pin, not a
conclusion: it is consumed, not discharged, and its truth at
any seat is exactly as open as `UniformTrajectoryGap`'s
(module header). -/
def TrajectoryGapFloor (βt : ℕ → ℝ) (m : ℝ) : Prop :=
  (∀ (N : ℕ) [NeZero N] (hN2 : 2 ≤ N) (_hN : Even N),
      GapPackage μG ρ hρcont hd (βt N) hN2) →
  ∀ (N : ℕ) [NeZero N] (hN2 : 2 ≤ N) (_hN : Even N),
    ∃ δ : ℝ, δ ≤ 1 ∧ GapBound μG ρ hρcont (βt N) hN2 δ ∧
      m ≤ (N : ℝ) * δ

/-- **The naming is a restatement, not a strengthening.**
S3-0's `UniformTrajectoryGap`, applied to an admissible
trajectory under its package, provides a floor `m > 0`
satisfying `TrajectoryGapFloor` for that same `m`. Proved by
unfolding S3-0's statement — the only proved content in this
module, at statement level: the hypothesis is consumed in
exactly the form S3-0 states it. -/
theorem trajectoryGapFloor_of_uniform
    (h : UniformTrajectoryGap μG ρ hρcont hd) (βt : ℕ → ℝ)
    (hadm : AdmissibleTrajectory βt)
    (hpack : ∀ (N : ℕ) [NeZero N] (hN2 : 2 ≤ N) (_hN : Even N),
      GapPackage μG ρ hρcont hd (βt N) hN2) :
    ∃ m : ℝ, 0 < m ∧ TrajectoryGapFloor μG ρ hρcont hd βt m := by
  rcases h βt hadm hpack with ⟨m, hm, hδ⟩
  exact ⟨m, hm, fun _ => hδ⟩

/-! ## Clause (iii): identification with the OS pin's Schwinger data -/

/-- **The limit system identified as an OS bundle's Schwinger
data — by reference to the S-3 pin, its opacity inherited and
labeled.** The identification names the bundle's
`SchwingerMarker` carrier to be the limit correlation
system's type: the limit system `S` is thereby *the* Schwinger
data of the bundle `os`, at exactly the marker/type level at
which the S-3 pin (`OsterwalderSchraderAxioms`) ties its
data. The bundle's E0–E4 fields remain the pin's opaque
`Prop`s: this identification asserts **no** analytic content
about `S` — no temperedness bound, covariance, positivity, or
clustering is inherited from the bundle; the one clustering
statement the pin makes about `S` is `LimitGapClustering`,
stated separately in owned vocabulary. -/
def LimitSystemIsOSSchwingerData (_S : LimitCorrelationSystem)
    (os : OsterwalderSchraderAxioms) : Prop :=
  os.schwinger.carrier = LimitCorrelationSystem

/-! ## The pin -/

/-- **S3-2 — `ScalingLimitOfLattice (G ρ)`: what a continuum
limit of THIS lattice theory would assert. STATEMENT ONLY.**
For every admissible trajectory `βt` (S3-0's
`AdmissibleTrajectory`: nonnegative, with the nondegeneracy
fence against the `β ≡ 0` shadow) and every floor `m > 0`
such that the trajectory satisfies the floor hypothesis
`TrajectoryGapFloor` with that `m` — **clause (i), a labeled
hypothesis field: S3-0's uniformity content, consumed, not
discharged** — there exist a limit correlation system `S` and
an `OsterwalderSchraderAxioms` bundle such that:

- **(ii)** the rescaled finite correlations
  (`finiteCorrelation` along `βt`, spacing `a = 1/N`) converge
  to `S` pointwise on stated test configurations
  (`CorrelationsConvergePointwise` — the weakest convergence
  sense statable without distribution infrastructure, picked
  and labeled as such);
- **(iii)** `S` is identified as the bundle's Schwinger data
  (`LimitSystemIsOSSchwingerData` — by reference to the S-3
  pin, its opacity inherited and labeled), **and** the floor
  is attached to the limit system itself: `S` clusters with
  rate at least the same `m` (`LimitGapClustering` — the
  K-S3-2 attachment, module header).

The pin asserts that no trajectory, floor, limit system, or
bundle exists: it is the conditional statement above, and
every future continuum claim in this program is measured
against it, never against a weakening. -/
def ScalingLimitOfLattice : Prop :=
  ∀ βt : ℕ → ℝ, AdmissibleTrajectory βt →
  ∀ m : ℝ, 0 < m → TrajectoryGapFloor μG ρ hρcont hd βt m →
  ∃ S : LimitCorrelationSystem, ∃ os : OsterwalderSchraderAxioms,
    CorrelationsConvergePointwise μG ρ βt S ∧
    LimitSystemIsOSSchwingerData S os ∧
    LimitGapClustering S m

/-- **The pin's content, projected.** A scaling limit in the
pin's sense provides, for any admissible floored trajectory,
a limit system that the finite correlations converge to
pointwise, that is identified as an OS bundle's Schwinger
data, and that clusters with rate at least the trajectory's
floor. Statement-level only: this is the definition of
`ScalingLimitOfLattice` read back, no existence asserted. -/
theorem scalingLimitOfLattice_limit
    (h : ScalingLimitOfLattice μG ρ hρcont hd) (βt : ℕ → ℝ)
    (hadm : AdmissibleTrajectory βt) (m : ℝ) (hm : 0 < m)
    (hfloor : TrajectoryGapFloor μG ρ hρcont hd βt m) :
    ∃ S : LimitCorrelationSystem, ∃ os : OsterwalderSchraderAxioms,
      CorrelationsConvergePointwise μG ρ βt S ∧
      LimitSystemIsOSSchwingerData S os ∧
      LimitGapClustering S m :=
  h βt hadm m hm hfloor

end Span3ScalingLimit

end ThetLogos
