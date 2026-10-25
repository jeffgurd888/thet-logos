/-
# FG-1: the uniform-estimate statements at the U(1) seat — FORMULATION ONLY

Frontier gate, brick FG-1 (priced M with this module), under
`whitepaper/frontier-gate-scoping-2026-10-25.md` §2.1 and its
parent resolution of dependency D-1. Companion paper:
`whitepaper/frontier-fg1-formulation-2026-10-25.md`.

**What this module is.** The statements (U-vol) and (U-traj) of
Stage 3c's demand (gap queue W1), written at the one seat where
they can be written today — the circle seat
`(haarProb Circle, circleRep)` — as Prop-valued definitions over
Q12's landed gap package (`LatticeTransferCompact`:
`transfer_gap_of_formPos`, `transfer_gap_zero`,
`transfer_spectrum_finite_above`). **No proof of (U-vol) or
(U-traj) is scoped, priced, implied, or attempted here.**
Formulability ≠ truth: the gate records a [T4] Coulomb-phase
doubt against (U-traj) at this seat (a 4D U(1) continuum limit is
expected to be a free, gapless photon theory).

**Hypothesis status, on the face (D-1, parent-resolved).**
`TransferFormPos` (`LatticeTransferCompact.lean:2191`) is the
conjunction of (a) transfer-form positivity on **all** of
`osSpace` and (b) simplicity of the vacuum eigenvalue for
`transferOp` on `osSpace`. What Stage 2 discharged at this seat
is `SliceHPosOne` (S2-3, `sliceHPosOne_circle`): the one-step
diagonal on slice observables. The descent brick's transport
theorem (`inner_transferOp_self_re_nonneg_of_sliceHPosOne`)
promotes that discharge to clause (a) on all of `osSpace` —
because `osSpace` is *defined* as `Lp` of the slice measure and
`sliceState` is `MemLp.toLp`, hence surjective. Clause (b) is
touched by no Stage 2 brick: the engine's vacuum clauses live on
the Π₁-quotient for the descended `T̂`, a different operator on a
different space. So `TransferFormPos` at U(1) remains a **named
hypothesis** of every statement below (kill K-FG-1's PARTIAL
branch), and the missing connector — whole-space OS positivity
at U(1) *as the package Q12 consumes it*, concretely its
simplicity conjunct (b) from the landed seats — is the next
brick after FG-1. Compactness of `transferOp` rides as a
hypothesis alongside (Q12: conditional on `HDen` at general β,
unconditional at β = 0 given a Hilbert basis).

**The β = 0 shadow, fenced.** At β = 0 the per-instance gap is
T1 with δ = 1 at every N (`transfer_gap_zero`; restated below
as `gapBoundU1_zero`) — true, uniform, and about the degenerate
theory (T₀ is the vacuum projection). The trajectory class
`AdmissibleTrajectoryU1` therefore carries the
K-FG-1-vacuity fence *in its definition*: admissible curves are
nonnegative and take a positive value at arbitrarily large even
N, so neither `β ≡ 0` nor any eventually-zero curve is
admissible, and no floor stated over this class is verified by
the degenerate trajectory.

**NO CLAIM** — parts of any Clay statement closed by this
module: 0. Dials: 0/4. Stage 1b-B at general `(G, ρ)` remains
OPEN; nothing here is an input to it.
-/

import ThetLogos.LatticeTransferCompact
import ThetLogos.LatticeSliceCircle

namespace ThetLogos

open MeasureTheory

section UniformGapU1

/-! ## The packaged gap bound at the circle seat -/

/-- **A gap bound at the circle seat, per `(β, N)`.** `δ` is a
gap bound for `T_β` at `(haarProb Circle, circleRep)` if every
spectral point other than the vacuum eigenvalue `1` has norm at
most `1 - δ`. This is exactly the conclusion-shape of Q12's
`transfer_gap_of_formPos`: that theorem's output is
`∃ δ > 0, GapBoundU1 β hN2 δ` (see `gapBoundU1_of_package`).
`δ` is **not** a landed function of `(β, N)`; the corpus
provides it only in this packaged existence form, and the
uniform statements below quantify accordingly. -/
def GapBoundU1 (β : ℝ) {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    (δ : ℝ) : Prop :=
  ∀ lam ∈ spectrum ℂ (transferOp (haarProb Circle) circleRep
      hN2 circleRep_continuous β),
    lam ≠ 1 → ‖lam‖ ≤ 1 - δ

/-- Gap bounds are downward closed: a smaller positive number
is a gap bound whenever a larger one is. This is what licenses
the normalization `δ ≤ 1` in the uniform statements below (the
package's own β = 0 value is `δ = 1`). -/
theorem gapBoundU1_of_le (β : ℝ) {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {δ δ' : ℝ} (hδ' : δ' ≤ δ)
    (h : GapBoundU1 β hN2 δ) : GapBoundU1 β hN2 δ' := by
  intro lam hlam hlam1
  have hle := h lam hlam hlam1
  linarith

/-! ## The hypothesis package at the seat (D-1 decomposition) -/

/-- **`TransferFormPos` at U(1)** — the named hypothesis of
this brick, verbatim Q12's package at the circle seat:
positivity of the transfer form on all of `osSpace`, plus
vacuum simplicity. Not discharged by any landed theorem at
`β > 0`; see the module header for the D-1 audit. -/
def TransferFormPosU1 (β : ℝ) {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) : Prop :=
  TransferFormPos (haarProb Circle) circleRep β hN2
    circleRep_continuous zero_lt_one

/-- Clause (a) of `TransferFormPos`, alone: the transfer
form's diagonal has nonnegative real part at **every** vector
of `osSpace`. -/
def TransferDiagU1 (β : ℝ) {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) : Prop :=
  ∀ f : osSpace (N := N) (haarProb Circle) circleRep β,
    0 ≤ (inner ℂ f (transferOp (haarProb Circle) circleRep hN2
      circleRep_continuous β f)).re

/-- Clause (b) of `TransferFormPos`, alone: **vacuum
simplicity** — every fixed vector of `transferOp` on
`osSpace` is a scalar multiple of the vacuum. This is the
conjunct the D-1 audit locates as unbridged at `β > 0`
(Perron–Frobenius content; the corpus's osSpace-side
positivity, `transferOp_form_nonneg`, is nonnegativity for
nonnegative observables, with no simplicity clause). -/
def VacuumSimpleU1 (β : ℝ) {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) : Prop :=
  ∀ v : osSpace (N := N) (haarProb Circle) circleRep β,
    transferOp (haarProb Circle) circleRep hN2
        circleRep_continuous β v = v →
    v ∈ Submodule.span ℂ {osVacuum (N := N) (haarProb Circle) circleRep circleRep_continuous zero_lt_one β}

/-- Clause (a) restricted to slice states: the transfer
form's diagonal at vectors of the form `sliceState φ`. This
is the exact content of the Stage 2 hypothesis
`SliceHPosOne` at the seat, with `slicePairOne` unfolded
(compare `sliceTransferDiagU1_iff_sliceHPosOne`) — the
slice-generated side of the D-1 distinction, against
`TransferDiagU1`'s whole space. -/
def SliceTransferDiagU1 (β : ℝ) {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) : Prop :=
  ∀ (φ : (↥(sliceLinks (N := N)) → Circle) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) (haarProb Circle)
      circleRep β)),
    0 ≤ (inner ℂ (sliceState (haarProb Circle) circleRep β
        φ hφ)
      (transferOp (haarProb Circle) circleRep hN2
        circleRep_continuous β
        (sliceState (haarProb Circle) circleRep β φ hφ))).re

/-- The D-1 decomposition, as a Lean identity:
`TransferFormPos` at the seat *is* the conjunction of its
whole-space diagonal clause and its simplicity clause. -/
theorem transferFormPosU1_iff (β : ℝ) {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) :
    TransferFormPosU1 β hN2
      ↔ TransferDiagU1 β hN2 ∧ VacuumSimpleU1 β hN2 :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- The slice side of the D-1 distinction, as a Lean
identity: `SliceHPosOne` at the seat *is* clause (a)
restricted to slice states, with `slicePairOne` unfolded. -/
theorem sliceTransferDiagU1_iff_sliceHPosOne (β : ℝ)
    {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) :
    SliceTransferDiagU1 β hN2
      ↔ SliceHPosOne (haarProb Circle) circleRep hN2
        circleRep_continuous β :=
  Iff.rfl

/-- **The audit's transport clause.** Clause (a) at the seat,
at every `β ≥ 0`, from landed theorems only: S2-3's discharge
`sliceHPosOne_circle` composed with the descent brick's
transport theorem `inner_transferOp_self_re_nonneg_of_sliceHPosOne`.
The composition is one line because `sliceState` is
surjective onto `osSpace` (it is `MemLp.toLp`, and `osSpace`
is `Lp` of the slice measure). No new positivity is proved
here; what this records is that the D-1 gap is clause (b),
not clause (a). -/
theorem transferDiagU1_circle (β : ℝ) (hβ : 0 ≤ β)
    {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) (hN : Even N) :
    TransferDiagU1 β hN2 :=
  fun f => inner_transferOp_self_re_nonneg_of_sliceHPosOne
    (haarProb Circle) circleRep hN2 circleRep_continuous β
    (sliceHPosOne_circle hN2 hN β hβ) f

/-- **The per-instance hypothesis package at the seat:**
everything `transfer_gap_of_formPos` consumes, at
`(haarProb Circle, circleRep)` — compactness of the transfer
operator, and `TransferFormPos` at U(1) as the named
hypothesis. (`Even N`, `circleRep_continuous`, and `0 < 1`
are fixed at the seat or carried separately.) -/
def GapPackageU1 (β : ℝ) {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) : Prop :=
  IsCompactOperator ⇑(transferOp (haarProb Circle) circleRep
      hN2 circleRep_continuous β) ∧
    TransferFormPosU1 β hN2

/-- **The packaged existence form, restated at the seat.**
Under the per-instance package, Q12's theorem provides a
`δ > 0` that is a gap bound. This is `transfer_gap_of_formPos`
with the seat substituted — the raw material (U-vol) and
(U-traj) quantify over, and the exact sense in which the
corpus "has" a gap at the seat today: per `(β, N)`,
conditional, with no modulus. -/
theorem gapBoundU1_of_package (β : ℝ) {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) (hN : Even N) (h : GapPackageU1 β hN2) :
    ∃ δ > 0, GapBoundU1 β hN2 δ :=
  transfer_gap_of_formPos (haarProb Circle) circleRep β hN2
    circleRep_continuous zero_lt_one hN h.1 h.2

/-! ## The β = 0 fence -/

/-- **The β = 0 shadow, in Lean.** At β = 0, `δ = 1` is a
gap bound at every `N` (corpus-style: the Hilbert basis that
`transfer_gap_zero` consumes is carried as data). T1 — and
vacuous for Item 3: `T₀` is the vacuum projection, the
degenerate theory. Recorded here so the shadow is a named,
checkable fact of this module, and so
`AdmissibleTrajectoryU1`'s fence below has its referent
on the page. -/
theorem gapBoundU1_zero {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (osSpace (N := N)
      (haarProb Circle) circleRep 0)) :
    GapBoundU1 0 hN2 1 := by
  intro lam hlam hlam1
  have hsub := transfer_spectrum_zero (haarProb Circle)
    circleRep hN2 circleRep_continuous zero_lt_one b hlam
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
  rcases hsub with rfl | h
  · simp
  · exact absurd h hlam1

/-! ## Trajectory language [T2] -/

/-- **An admissible tuning trajectory at the seat** [T2 —
convention adopted by this brick, per the frontier gate
§2.1]. A curve `βt : ℕ → ℝ`, read at even `N ≥ 2` with
lattice spacing `a = 1/N` in unit-physical-volume units
(`m = −log|λ₂| / a ≈ δ / a` is the physical mass the floor
below is about). Admissibility is two clauses:
(i) `βt` is nonnegative everywhere (the seat's positivity
region is `β ≥ 0`); (ii) **the nondegeneracy fence** —
`βt` takes a positive value at arbitrarily large even `N`.
Clause (ii) fences out, by construction, the degenerate
constant trajectory `β ≡ 0` and every eventually-zero
curve (kill K-FG-1-vacuity): no floor quantified over this
class can be witnessed by the β = 0 shadow. No curve in
this class is asserted to give a continuum limit; the
statements below are about floors, not convergence. -/
def AdmissibleTrajectoryU1 (βt : ℕ → ℝ) : Prop :=
  (∀ N : ℕ, 0 ≤ βt N) ∧
  (∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ Even N ∧ 0 < βt N)

/-! ## The uniform statements — FORMULATION ONLY -/

/-- **(U-vol) — volume uniformity at fixed coupling, at the
U(1) seat. FORMULATION ONLY.** Under the per-instance
package (`GapPackageU1` — compactness plus the named
hypothesis `TransferFormPos` at U(1)) at every even
`N ≥ 2`, there is a single normalized gap bound
`0 < δ ≤ 1` that works at every even `N ≥ 2`: the
fixed-coupling gap does not close as the torus grows.
Hypothesis status: **under TransferFormPos at U(1)**
(K-FG-1 PARTIAL branch). Truth status: at `β = 0` the
per-instance content is T1 with `δ = 1` and vacuous
(`gapBoundU1_zero`); at `β > 0` this statement is OPEN —
no proof is scoped, priced, or implied by this brick. -/
def UniformVolumeGapU1 (β : ℝ) : Prop :=
  (∀ (N : ℕ) [NeZero N] (hN2 : 2 ≤ N) (_hN : Even N),
    GapPackageU1 β hN2) →
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
    ∀ (N : ℕ) [NeZero N] (hN2 : 2 ≤ N),
      GapBoundU1 β hN2 δ

/-- **(U-traj) — trajectory uniformity as `a → 0`, at the
U(1) seat. FORMULATION ONLY.** For every admissible
trajectory `βt` (see `AdmissibleTrajectoryU1` for the [T2]
reading `a = 1/N` and the nondegeneracy fence), under the
per-instance package at every point `(βt N, N)` of the
trajectory, there is a physical floor `m > 0` such that at
every even `N ≥ 2` the packaged gap can be chosen
normalized (`δ ≤ 1`) with `m ≤ N · δ` — i.e. `δ` closes at
most linearly in `a`, with `δ / a ≈ N · δ` bounded below.
Hypothesis status: **under TransferFormPos at U(1)**
(K-FG-1 PARTIAL branch). Truth status: OPEN, and doubted
on [T4] grounds — 4D lattice U(1) is expected to have a
Coulomb phase whose continuum limit is a free photon
theory, in which the physical mass is `0` and no such `m`
exists along a trajectory entering that phase.
Formulability is not truth; this definition asserts
neither. -/
def UniformTrajectoryGapU1 : Prop :=
  ∀ βt : ℕ → ℝ, AdmissibleTrajectoryU1 βt →
    (∀ (N : ℕ) [NeZero N] (hN2 : 2 ≤ N) (_hN : Even N),
      GapPackageU1 (βt N) hN2) →
    ∃ m : ℝ, 0 < m ∧
      ∀ (N : ℕ) [NeZero N] (hN2 : 2 ≤ N) (_hN : Even N),
        ∃ δ : ℝ, δ ≤ 1 ∧ GapBoundU1 (βt N) hN2 δ ∧
          m ≤ (N : ℝ) * δ

end UniformGapU1

end ThetLogos
