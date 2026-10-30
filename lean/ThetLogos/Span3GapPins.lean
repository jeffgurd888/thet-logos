/-
# S3-0: Span 3's first pier — the uniformity statements at general (G, ρ)

Brick S3-0 of the Span-3 first pier
(`routeb-general-scratch/scoping-span3-first-rung-2026-10-29.md` §2).
This module lifts the U(1)-seat formulation of
`LatticeUniformGap.lean` (FG-1) to general `(G, ρ)`: the
per-instance gap predicate is defined from the output shape of
the landed general-`(G, ρ)` theorem `transfer_gap_of_formPos`
(`LatticeTransferCompact`), the hypothesis package mirrors
`GapPackageU1` with `TransferFormPos` named, and the two
uniformity statements carry the admissibility class and its
nondegeneracy fence at general `(G, ρ)`. The brick's remaining
pieces live in two companion modules, split by a pre-existing
tree defect (next paragraph): `Span3GapPinsU1` (the U(1)-seat
regression instances) and `Span3MarginPin` (the stratum column
factorization and the `UniformMarginFactorization` pin of the
S3-1 wall-identity gate,
`whitepaper/s31-wall-identity-gate-2026-10-29.md` §5, riding
inside this brick per that gate's §7 recommendation).

**Tree defect forcing the split, on the face.**
`ThetLogos.reflSite_eq_torusShift_zero` is declared twice in the
landed tree — `LatticeGramSeries.lean:1048` and
`PlaneCrossingFactor.lean:180` — so no single Lean environment
can import both the `LatticeSliceCircle`/`LatticeGramSeries`
chain (which `LatticeUniformGap` needs) and the
`PolymerPartition`/`PlaneCrossingFactor` chain (which the
factorization pin needs). The brick therefore splits along
exactly that seam: this module and `Span3GapPinsU1` sit on the
transfer side, `Span3MarginPin` imports this module plus
`PolymerPartition` on the polymer side. No landed file was
modified to work around it.

**STATEMENTS ONLY.** This module states the hypotheses a
continuum argument in this program would consume. It proves
none of them at any `β > 0` seat. The pier's distance
statement, verbatim in substance: these are statements for the
rungs; proof-grade distance toward the continuum covered here
is **ZERO**. The pier's frontier vocabulary remains unspent
and appears nowhere below as a name. `gap_closes`
(`ClayStatement`) stands as the certificate that finite gap
algebra does not transfer; no statement here is phrased as if
it does.

**The P-2 fence.** The per-instance predicate below is defined
from `transfer_gap_of_formPos`'s output shape and from nothing
else. In particular it is NOT defined from `doeblinDelta`
(`DoeblinGap`): the Doeblin `δ₀` is a proved mixing bound whose
volume behaviour — exponential decay in `N⁴` — is the opposite
of a mass gap's, and no statement in this module cites it as
gap evidence.

**Hypothesis status, on the face.** `TransferFormPos` at
general `(G, ρ)` is a named hypothesis of every statement
below: clause (a) is the open Stage 1b-B positivity content,
clause (b) is discharged at general `(G, ρ)` (`fixed_mem_span`).
Compactness of `transferOp` rides as a hypothesis alongside
(conditional at general `β`).

**The β = 0 shadow, fenced.** At `β = 0` the per-instance gap
is T1 with `δ = 1` at every `N` (`transfer_gap_zero`; restated
below as `gapBound_zero`) — true, uniform, and about the
degenerate theory (`T₀` is the vacuum projection). The
trajectory class `AdmissibleTrajectory` therefore carries the
nondegeneracy fence *in its definition*: admissible curves are
nonnegative and take a positive value at arbitrarily large
even `N`, so neither `β ≡ 0` nor any eventually-zero curve is
admissible, and no floor stated over this class is witnessed
by the degenerate trajectory.

**NO CLAIM** — parts of any Clay statement closed by this
module: 0. Dials: 0/4. Nothing here is an input to a continuum
claim.
-/

import ThetLogos.LatticeTransferCompact
import ThetLogos.LatticeGauge

namespace ThetLogos

open MeasureTheory

section Span3PerInstance

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)

/-! ## The per-instance gap predicate at general (G, ρ) -/

/-- **A gap bound at general `(G, ρ)`, per `(β, N)`.** `δ` is a
gap bound for `T_β` at `(μG, ρ)` if every spectral point other
than the vacuum eigenvalue `1` has norm at most `1 - δ`. This
is exactly the conclusion-shape of `transfer_gap_of_formPos`:
that theorem's output is `∃ δ > 0, GapBound μG ρ hρcont β hN2 δ`
(see `gapBound_of_package`). `δ` is **not** a landed function
of `(β, N)`; the corpus provides it only in this packaged
existence form, and the uniform statements below quantify
accordingly. Defined from `transfer_gap_of_formPos`'s output
shape only — never from `doeblinDelta` (the P-2 fence, module
header). -/
def GapBound (β : ℝ) (hN2 : 2 ≤ N) (δ : ℝ) : Prop :=
  ∀ lam ∈ spectrum ℂ (transferOp μG ρ hN2 hρcont β),
    lam ≠ 1 → ‖lam‖ ≤ 1 - δ

/-- Gap bounds are downward closed: a smaller number is a gap
bound whenever a larger one is. This is what licenses the
normalization `δ ≤ 1` in the uniform statements below (the
package's own β = 0 value is `δ = 1`). -/
theorem gapBound_of_le (β : ℝ) (hN2 : 2 ≤ N) {δ δ' : ℝ}
    (hδ' : δ' ≤ δ) (h : GapBound μG ρ hρcont β hN2 δ) :
    GapBound μG ρ hρcont β hN2 δ' := by
  intro lam hlam hlam1
  have hle := h lam hlam hlam1
  linarith

/-! ## The hypothesis package at general (G, ρ) -/

/-- **The per-instance hypothesis package at general
`(G, ρ)`:** everything `transfer_gap_of_formPos` consumes —
compactness of the transfer operator, and `TransferFormPos`
(the named (H-PF) package: transfer-form positivity on all of
`osSpace`, plus vacuum simplicity) with its continuity and
dimension hypotheses named. Mirrors `GapPackageU1`
clause-for-clause. Not discharged by any landed theorem at
`β > 0` at general `(G, ρ)`; see the module header. -/
def GapPackage (β : ℝ) (hN2 : 2 ≤ N) : Prop :=
  IsCompactOperator ⇑(transferOp μG ρ hN2 hρcont β) ∧
    TransferFormPos μG ρ β hN2 hρcont hd

/-- **The packaged existence form.** Under the per-instance
package, `transfer_gap_of_formPos` provides a `δ > 0` that is
a gap bound. This is that theorem restated through `GapBound`
— the raw material the uniform statements quantify over, and
the exact sense in which the corpus "has" a gap at general
`(G, ρ)` today: per `(β, N)`, conditional, with no modulus. -/
theorem gapBound_of_package (β : ℝ) (hN2 : 2 ≤ N) (hN : Even N)
    (h : GapPackage μG ρ hρcont hd β hN2) :
    ∃ δ > 0, GapBound μG ρ hρcont β hN2 δ :=
  transfer_gap_of_formPos μG ρ β hN2 hρcont hd hN h.1 h.2

/-! ## The β = 0 fence, per instance -/

/-- **The β = 0 shadow, per instance, at general `(G, ρ)`.**
At `β = 0` there is a gap bound with `δ = 1` (corpus-style:
the Hilbert basis that `transfer_gap_zero` consumes is carried
as data). T1 — and vacuous for uniformity: `T₀` is the vacuum
projection, the degenerate theory. Recorded so the shadow is
a named, checkable fact of this module, and so the
admissibility fence below has its referent on the page. -/
theorem gapBound_zero (hN2 : 2 ≤ N) {ι : Type*} [Countable ι]
    (hd : 0 < d)
    (b : HilbertBasis ι ℂ (osSpace (N := N) μG ρ 0)) :
    GapBound μG ρ hρcont 0 hN2 1 := by
  intro lam hlam hlam1
  have hsub := transfer_spectrum_zero μG ρ hN2 hρcont hd b hlam
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
  rcases hsub with rfl | h
  · simp
  · exact absurd h hlam1

end Span3PerInstance

section Span3Uniformity

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)

/-! ## Trajectory language [T2] -/

/-- **An admissible tuning trajectory at general `(G, ρ)`**
[T2 — the convention of `AdmissibleTrajectoryU1`, read at
general `(G, ρ)`]. A curve `βt : ℕ → ℝ`, read at even `N ≥ 2`
with lattice spacing `a = 1/N` in unit-physical-volume units
(`m = −log|λ₂| / a ≈ δ / a` is the physical mass the floor
below is about). Admissibility is two clauses: (i) `βt` is
nonnegative everywhere (the positivity region is `β ≥ 0`);
(ii) **the nondegeneracy fence** — `βt` takes a positive value
at arbitrarily large even `N`. Clause (ii) fences out, by
construction, the degenerate constant trajectory `β ≡ 0` and
every eventually-zero curve: no floor quantified over this
class can be witnessed by the β = 0 shadow (`gapBound_zero`).
The class is stated so that a seat-dependence fence (e.g.
nonabelian / asymptotically free trajectories only — the
Span-3 memo's DP-2) can be attached to it by name if the U(1)
trajectory doubt is ever certified. No curve in this class is
asserted to give a continuum limit; the statements below are
about floors, not convergence. -/
def AdmissibleTrajectory (βt : ℕ → ℝ) : Prop :=
  (∀ N : ℕ, 0 ≤ βt N) ∧
  (∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ Even N ∧ 0 < βt N)

/-! ## The uniform statements — FORMULATION ONLY -/

/-- **(U-vol) at general `(G, ρ)` — volume uniformity at fixed
coupling. FORMULATION ONLY.** Under the per-instance package
(`GapPackage` — compactness plus the named hypothesis
`TransferFormPos`) at every even `N ≥ 2`, there is a single
normalized gap bound `0 < δ ≤ 1` that works at every `N ≥ 2`:
the fixed-coupling gap does not close as the torus grows.
This statement is exactly the assertion that the `∀ N, ∃ δ_N`
of `gapBound_of_package` swaps to `∃ δ, ∀ N`; nothing else in
it mentions the stratum, columns, or polymers (S3-1 gate
§1(ii)). Hypothesis status: **under `TransferFormPos` at
general `(G, ρ)`**. Truth status: at `β = 0` the per-instance
content is T1 with `δ = 1` and vacuous (`gapBound_zero`); at
`β > 0` this statement is OPEN — no proof is scoped, priced,
or implied by this brick. -/
def UniformVolumeGap (β : ℝ) : Prop :=
  (∀ (N : ℕ) [NeZero N] (hN2 : 2 ≤ N) (_hN : Even N),
    GapPackage μG ρ hρcont hd β hN2) →
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
    ∀ (N : ℕ) [NeZero N] (hN2 : 2 ≤ N),
      GapBound μG ρ hρcont β hN2 δ

/-- **(U-traj) at general `(G, ρ)` — trajectory uniformity as
`a → 0`. FORMULATION ONLY.** For every admissible trajectory
`βt` (see `AdmissibleTrajectory` for the [T2] reading
`a = 1/N` and the nondegeneracy fence), under the per-instance
package at every point `(βt N, N)` of the trajectory, there is
a physical floor `m > 0` such that at every even `N ≥ 2` the
packaged gap can be chosen normalized (`δ ≤ 1`) with
`m ≤ N · δ` — i.e. `δ` closes at most linearly in `a`, with
`δ / a ≈ N · δ` bounded below. Hypothesis status: **under
`TransferFormPos` at general `(G, ρ)`**. Truth status: OPEN.
At the U(1) seat the mirrored statement is doubted on [T4]
grounds (a Coulomb phase whose continuum limit is a free
photon theory has no such floor along a trajectory entering
it — `LatticeUniformGap` header); formulability is not
truth, and this definition asserts neither. -/
def UniformTrajectoryGap : Prop :=
  ∀ βt : ℕ → ℝ, AdmissibleTrajectory βt →
    (∀ (N : ℕ) [NeZero N] (hN2 : 2 ≤ N) (_hN : Even N),
      GapPackage μG ρ hρcont hd (βt N) hN2) →
    ∃ m : ℝ, 0 < m ∧
      ∀ (N : ℕ) [NeZero N] (hN2 : 2 ≤ N) (_hN : Even N),
        ∃ δ : ℝ, δ ≤ 1 ∧ GapBound μG ρ hρcont (βt N) hN2 δ ∧
          m ≤ (N : ℝ) * δ

/-- **The β = 0 vacuous instance of the uniform consequent,
stated.** The consequent-shape of (U-vol) at `β = 0`: one
normalized `δ` bounding the gap at every volume. Its
per-instance content is T1 with `δ = 1` (`gapBound_zero`,
modulo a Hilbert basis carried as data at each `N`); as a
uniform statement it is about the degenerate theory (`T₀` is
the vacuum projection) and is fenced accordingly — in
particular it is NOT an admissible-trajectory witness, by
`AdmissibleTrajectory`'s clause (ii). Stated so the shadow has
a name at general `(G, ρ)`; nothing in this module asserts it
at any seat where the basis data is not supplied. -/
def UniformGapBoundZero : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
    ∀ (N : ℕ) [NeZero N] (hN2 : 2 ≤ N),
      GapBound μG ρ hρcont 0 hN2 δ

end Span3Uniformity

end ThetLogos
