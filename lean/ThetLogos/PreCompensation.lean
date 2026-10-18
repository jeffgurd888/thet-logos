import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import ThetLogos.DecoherenceToy

open Matrix Finset

namespace ThetLogos

/-!
# Pre-compensation: how far a state can be pre-deformed (T1, finite level)

Origin (Jeff, 2026-10-18): a bevel gear's teeth are machined
deliberately WRONG — tip relief, crowning, twist compensation — so
that under load the gear runs TRUE. (The trade is Caleb Gurd's.) The
transplant question: given a known channel that will deform a state,
can one prepare a pre-deformed state that the channel lands exactly
on target? This module answers that question at finite level, for
two channels, with the obstruction proved, not just the successes.

* **The systematic case (the gear case proper).** A known unitary
  error — conjugation by a fixed unitary `U` — is exactly
  pre-compensable for EVERY target: prepare `U† ρ U`
  (`unitary_precompensable`). Systematic deformation cancels
  completely.

* **The forgetting case.** The partial-dephasing family `dephase l`
  (diagonal fixed, off-diagonals scaled by `l`), interpolating the
  identity (`l = 1`) and the decoherence toy's pinching (`l = 0`,
  `DecoherenceToy.pinch`). For `0 ≤ l ≤ 1` it is a channel:
  density matrices map to density matrices
  (`isDensityMatrix_dephase`). The reachability theorem
  (`precompensable_iff`): for `l ≠ 0`, a target `ρ` is exactly
  pre-compensable **iff** the de-amplified candidate — diagonal
  unchanged, off-diagonals scaled by `l⁻¹` — is itself positive.
  At `l = 1` every target is reachable; at `l = 0` exactly the
  diagonal targets are (`precompensable_zero_iff_diagonal`); for
  `0 < l < 1` the reachable set is a genuine proper subset
  (`not_precompensable_pairPlus`): the maximally coherent target on
  any two basis states cannot be pre-compensated, because its
  de-amplification would need `1 - l⁻¹ < 0` of positivity. *The
  tooth can only be pre-cut so far.*

**Fences.** Finite matrices over a finite index type throughout.
`dephase l` for `l ∉ [0, 1]` is the same formula read as a linear
map (needed to state the de-amplification candidate at `l⁻¹`); it
is NOT claimed to be a channel there. Pre-compensation cancels a
systematic deformation exactly; fluctuations are not cancelled by
any theorem here — the `0 < l < 1` obstruction is the finite shadow
of why. The thermal instance (pre-distort so a Gibbs thermalization
lands on target; the question's original shelf on `ThermalClock`)
is NOT proved here: it is the named remainder, priced with the
ThermalClock scalar-shift leftover.
-/

section Dephase

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The partial-dephasing map at level `l : ℝ`: diagonal entries
fixed, off-diagonal entries scaled by `l`. Written as the affine
combination `l • A + (1 - l) • pinch A` (the toy's `pinch` is the
`l = 0` case; `l = 1` is the identity). A channel for
`0 ≤ l ≤ 1`; a bare linear map outside that range. -/
def dephase (l : ℝ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (l : ℂ) • A + (1 - (l : ℂ)) • pinch A

/-- Populations are invariant under partial dephasing, at every
level: the diagonal of `dephase l A` is the diagonal of `A`. -/
theorem dephase_diag (l : ℝ) (A : Matrix ι ι ℂ) (i : ι) :
    dephase l A i i = A i i := by
  simp only [dephase, Matrix.add_apply, Matrix.smul_apply, pinch_diag, smul_eq_mul]
  ring

/-- Off-diagonals are scaled by exactly `l`. -/
theorem dephase_apply_off (l : ℝ) (A : Matrix ι ι ℂ) {i j : ι} (h : i ≠ j) :
    dephase l A i j = (l : ℂ) * A i j := by
  simp only [dephase, Matrix.add_apply, Matrix.smul_apply, pinch_apply_ne A h,
    smul_eq_mul, mul_zero, add_zero]

/-- Pinching after partial dephasing is pinching: the family does
not move populations, so the `l = 0` endpoint sees the same
diagonal. -/
theorem pinch_dephase (l : ℝ) (A : Matrix ι ι ℂ) :
    pinch (dephase l A) = pinch A := by
  ext i j
  by_cases h : i = j
  · subst h; simp [pinch_diag, dephase_diag]
  · rw [pinch_apply_ne _ h, pinch_apply_ne _ h]

/-- Composition law: the family is multiplicative in the level,
`dephase a ∘ dephase b = dephase (a * b)` — as bare linear maps,
for all real levels. -/
theorem dephase_comp (a b : ℝ) (A : Matrix ι ι ℂ) :
    dephase a (dephase b A) = dephase (a * b) A := by
  ext i j
  by_cases h : i = j
  · subst h; rw [dephase_diag, dephase_diag, dephase_diag]
  · rw [dephase_apply_off a (dephase b A) h, dephase_apply_off b A h,
      dephase_apply_off (a * b) A h]
    push_cast
    ring

/-- The `l = 1` endpoint is the identity. -/
theorem dephase_one (A : Matrix ι ι ℂ) : dephase 1 A = A := by
  ext i j
  by_cases hij : i = j
  · subst hij; exact dephase_diag 1 A _
  · rw [dephase_apply_off _ _ hij]; simp

/-- The `l = 0` endpoint is the toy's pinching. -/
theorem dephase_zero (A : Matrix ι ι ℂ) : dephase 0 A = pinch A := by
  ext i j
  by_cases h : i = j
  · subst h; rw [dephase_diag, pinch_diag]
  · rw [dephase_apply_off _ _ h, pinch_apply_ne _ h]; simp

/-- De-amplification cancels dephasing (left inverse), for `l ≠ 0`:
`dephase l⁻¹` is the candidate-preparation map of the reachability
theorem. -/
theorem dephase_inv_cancel {l : ℝ} (hl : l ≠ 0) (A : Matrix ι ι ℂ) :
    dephase l (dephase l⁻¹ A) = A := by
  rw [dephase_comp, mul_inv_cancel₀ hl, dephase_one]

/-- Dephasing cancels de-amplification (right inverse), for
`l ≠ 0`. -/
theorem dephase_cancel_inv {l : ℝ} (hl : l ≠ 0) (A : Matrix ι ι ℂ) :
    dephase l⁻¹ (dephase l A) = A := by
  rw [dephase_comp, inv_mul_cancel₀ hl, dephase_one]

/-- Partial dephasing preserves the trace, at every real level. -/
theorem trace_dephase (l : ℝ) (A : Matrix ι ι ℂ) :
    Matrix.trace (dephase l A) = Matrix.trace A := by
  simp only [dephase, Matrix.trace_add, Matrix.trace_smul, trace_pinch, smul_eq_mul]
  ring

/-- Partial dephasing preserves Hermiticity, at every real level
(the level is real, so no conjugation lands on it). -/
theorem isHermitian_dephase (l : ℝ) {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (dephase l A).IsHermitian := by
  have hAe : Aᴴ = A := hA
  show (dephase l A)ᴴ = dephase l A
  rw [dephase, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_smul, hAe, conjTranspose_pinch, hAe]
  have hstar : star (l : ℂ) = (l : ℂ) := by
    rw [← starRingEnd_apply]; exact Complex.conj_ofReal l
  have hstar1 : star (1 - (l : ℂ)) = 1 - (l : ℂ) := by
    rw [star_sub, star_one, hstar]
  rw [hstar, hstar1]

/-- The quadratic form of a partial dephasing is the same affine
combination of the two endpoint quadratic forms. -/
theorem dephase_quad (l : ℝ) (A : Matrix ι ι ℂ) (x : ι → ℂ) :
    (star x) ⬝ᵥ ((dephase l A) *ᵥ x)
      = (l : ℂ) * ((star x) ⬝ᵥ (A *ᵥ x))
        + (1 - (l : ℂ)) * ((star x) ⬝ᵥ (pinch A *ᵥ x)) := by
  rw [dephase, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    dotProduct_add, dotProduct_smul, dotProduct_smul]
  simp only [smul_eq_mul]

/-- **Deliverable 1 (channel property).** For `0 ≤ l ≤ 1`, partial
dephasing maps density matrices to density matrices: it is the
affine combination of two density-preserving maps (the identity
and the toy's pinching) with weights in `[0, 1]`. -/
theorem isDensityMatrix_dephase {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (dephase l ρ) := by
  refine ⟨isHermitian_dephase l hρ.1, ?_, by rw [trace_dephase]; exact hρ.2.2⟩
  intro x
  have h1 := hρ.2.1 x
  have h2 := (isDensityMatrix_pinch hρ).2.1 x
  have hcast : (1 - (l : ℂ)) = ((1 - l : ℝ) : ℂ) := by push_cast; ring
  have hre : ∀ (c : ℝ) (z : ℂ), ((c : ℂ) * z).re = c * z.re := by
    intro c z
    simp [Complex.mul_re]
  rw [dephase_quad, hcast, Complex.add_re, hre, hre]
  exact add_nonneg (mul_nonneg hl0 h1) (mul_nonneg (by linarith) h2)

end Dephase

-- ============================================================================
-- Reachability: exactly which targets can be pre-compensated
-- ============================================================================

section Reachability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A target state `ρ` is **exactly pre-compensable** under
`dephase l` if some density matrix `σ` is mapped onto it:
`dephase l σ = ρ`. The pre-image `σ` is the pre-deformed
preparation — the tooth pre-cut so the channel lands it true. -/
def PreCompensable (l : ℝ) (ρ : Matrix ι ι ℂ) : Prop :=
  ∃ σ : Matrix ι ι ℂ, IsDensityMatrix σ ∧ dephase l σ = ρ

/-- **Deliverable 2 (the reachability theorem).** For `l ≠ 0`, a
density matrix `ρ` is exactly pre-compensable under `dephase l`
if and only if the **de-amplified candidate** `dephase l⁻¹ ρ` —
diagonal unchanged, off-diagonals scaled by `l⁻¹` — is itself a
density matrix. The candidate is the unique possible pre-image
(the family is invertible as linear maps); pre-compensation
exists exactly where de-amplification stays inside the state
space. -/
theorem precompensable_iff {l : ℝ} (hl : l ≠ 0) {ρ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) :
    PreCompensable l ρ ↔ IsDensityMatrix (dephase l⁻¹ ρ) := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rw [dephase_cancel_inv hl]
    exact hσ
  · intro h
    exact ⟨dephase l⁻¹ ρ, h, dephase_inv_cancel hl ρ⟩

/-- Of the candidate's three density conditions, two are automatic
(Hermiticity and trace, at every real level); the reachability
question is exactly the positivity clause. -/
theorem isDensityMatrix_dephase_iff_pos (l : ℝ) {ρ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (dephase l ρ)
      ↔ ∀ x : ι → ℂ, 0 ≤ ((star x) ⬝ᵥ ((dephase l ρ) *ᵥ x)).re :=
  ⟨fun h => h.2.1,
   fun h => ⟨isHermitian_dephase l hρ.1, h, by rw [trace_dephase]; exact hρ.2.2⟩⟩

/-- The reachability theorem, positivity form: `ρ` is exactly
pre-compensable under `dephase l` (`l ≠ 0`) iff the de-amplified
candidate's quadratic form is everywhere nonnegative. -/
theorem precompensable_iff_pos {l : ℝ} (hl : l ≠ 0) {ρ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) :
    PreCompensable l ρ
      ↔ ∀ x : ι → ℂ, 0 ≤ ((star x) ⬝ᵥ ((dephase l⁻¹ ρ) *ᵥ x)).re :=
  (precompensable_iff hl hρ).trans (isDensityMatrix_dephase_iff_pos l⁻¹ hρ)

/-- At `l = 1` (no dephasing) every target is reachable: prepare
the target itself. -/
theorem precompensable_one {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) :
    PreCompensable 1 ρ :=
  ⟨ρ, hρ, dephase_one ρ⟩

/-- Diagonal targets are reachable at every level: a state with
no coherences is a fixed point of the whole family. -/
theorem precompensable_of_diagonal (l : ℝ) {ρ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) (hdiag : pinch ρ = ρ) : PreCompensable l ρ := by
  refine ⟨ρ, hρ, ?_⟩
  ext i j
  by_cases h : i = j
  · subst h; exact dephase_diag l ρ _
  · have hρij : ρ i j = 0 := by
      have h2 : pinch ρ i j = ρ i j := by rw [hdiag]
      rw [pinch_apply_ne ρ h] at h2
      exact h2.symm
    rw [dephase_apply_off _ _ h, hρij, mul_zero]

/-- At `l = 0` (full pinching) the reachable targets are exactly
the fixed points of pinching. The channel forgets all coherence
in one step, so a target carrying any coherence has no pre-image
at all: forgetfulness as a proved obstruction. -/
theorem precompensable_zero_iff {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) :
    PreCompensable 0 ρ ↔ pinch ρ = ρ := by
  constructor
  · rintro ⟨σ, -, hσ⟩
    rw [dephase_zero] at hσ
    rw [← hσ, pinch_idem]
  · intro h
    exact ⟨ρ, hρ, by rw [dephase_zero]; exact h⟩

/-- At `l = 0`, reachable means diagonal — entry by entry. -/
theorem precompensable_zero_iff_diagonal {ρ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) :
    PreCompensable 0 ρ ↔ ∀ i j, i ≠ j → ρ i j = 0 :=
  (precompensable_zero_iff hρ).trans (pinch_eq_self_iff ρ)

end Reachability

-- ============================================================================
-- The obstruction: for 0 < l < 1 the reachable set is a proper subset
-- ============================================================================

section ProperSubset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The two-point coherent vector: amplitude `(√2)⁻¹` on each of
the basis states `i, j`, zero elsewhere. -/
noncomputable def pairVec (i j : ι) : ι → ℂ :=
  fun k => if k = i ∨ k = j then ((Real.sqrt 2 : ℂ))⁻¹ else 0

theorem pairVec_apply_left (i j : ι) :
    pairVec i j i = ((Real.sqrt 2 : ℂ))⁻¹ :=
  if_pos (Or.inl rfl)

theorem pairVec_apply_right (i j : ι) :
    pairVec i j j = ((Real.sqrt 2 : ℂ))⁻¹ :=
  if_pos (Or.inr rfl)

theorem pairVec_apply_of_ne {i j k : ι} (h1 : k ≠ i) (h2 : k ≠ j) :
    pairVec i j k = 0 :=
  if_neg (not_or.mpr ⟨h1, h2⟩)

/-- The maximally coherent pure state on the pair `i, j`: the
rank-one density matrix `u u*` for `u = pairVec i j`. Its
populations are `1/2, 1/2` and its coherence is `1/2` — as large
as positivity allows. -/
noncomputable def pairPlus (i j : ι) : Matrix ι ι ℂ :=
  Matrix.of fun a b => pairVec i j a * star (pairVec i j b)

theorem pairPlus_apply (i j : ι) (a b : ι) :
    pairPlus i j a b = pairVec i j a * star (pairVec i j b) :=
  rfl

/-- Every entry of `pairPlus i j` between the two support points
is exactly `1/2`. -/
theorem pairVec_mul_star (i j : ι) {a b : ι}
    (ha : a = i ∨ a = j) (hb : b = i ∨ b = j) :
    pairVec i j a * star (pairVec i j b) = (1 / 2 : ℂ) := by
  have hua : pairVec i j a = ((Real.sqrt 2 : ℂ))⁻¹ := if_pos ha
  have hub : pairVec i j b = ((Real.sqrt 2 : ℂ))⁻¹ := if_pos hb
  rw [hua, hub]
  have h1 : star (((Real.sqrt 2 : ℂ))⁻¹) = ((Real.sqrt 2 : ℂ))⁻¹ := by
    rw [star_inv₀]; simp
  rw [h1, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The maximally coherent pair state is a density matrix. -/
theorem isDensityMatrix_pairPlus {i j : ι} (hij : i ≠ j) :
    IsDensityMatrix (pairPlus i j) := by
  refine ⟨?_, ?_, ?_⟩
  · show (pairPlus i j)ᴴ = pairPlus i j
    ext a b
    rw [Matrix.conjTranspose_apply, pairPlus_apply, pairPlus_apply, star_mul,
      star_star, mul_comm]
  · intro x
    set S : ℂ := ∑ b, star (pairVec i j b) * x b with hS
    have hmv : ∀ a, (pairPlus i j *ᵥ x) a = pairVec i j a * S := by
      intro a
      rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [pairPlus_apply, mul_assoc]
    have hstarS : (∑ a, star (x a) * pairVec i j a) = star S := by
      rw [hS, star_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [star_mul, star_star]
    have hQ : (star x) ⬝ᵥ (pairPlus i j *ᵥ x) = star S * S := by
      show (∑ a, star (x a) * ((pairPlus i j *ᵥ x) a)) = star S * S
      rw [Finset.sum_congr rfl (g := fun a => star (x a) * (pairVec i j a * S))
        (fun a _ => by rw [hmv a])]
      rw [← hstarS, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_assoc]
    have hnorm : star S * S = (Complex.normSq S : ℂ) := by
      rw [mul_comm (star S) S, ← starRingEnd_apply, Complex.mul_conj]
    rw [hQ, hnorm, Complex.ofReal_re]
    exact Complex.normSq_nonneg S
  · have hterm : ∀ a, pairPlus i j a a
        = (if a = i ∨ a = j then (1 / 2 : ℂ) else 0) := by
      intro a
      by_cases ha : a = i ∨ a = j
      · rw [if_pos ha, pairPlus_apply]
        exact pairVec_mul_star i j ha ha
      · rw [if_neg ha, pairPlus_apply]
        have h1 : pairVec i j a = 0 :=
          pairVec_apply_of_ne (fun h => ha (Or.inl h)) (fun h => ha (Or.inr h))
        rw [h1, zero_mul]
    have htr : Matrix.trace (pairPlus i j) = ∑ a, pairPlus i j a a := rfl
    rw [htr, Finset.sum_congr rfl (fun a _ => hterm a)]
    have hsplit : (∑ a, (if a = i ∨ a = j then (1 / 2 : ℂ) else 0))
        = (∑ a, (if a = i then (1 / 2 : ℂ) else 0))
          + (∑ a, (if a = j then (1 / 2 : ℂ) else 0)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hai : a = i
      · subst hai
        rw [if_pos (Or.inl rfl), if_pos rfl, if_neg hij, add_zero]
      · by_cases haj : a = j
        · subst haj
          rw [if_pos (Or.inr rfl), if_neg hai, if_pos rfl, zero_add]
        · rw [if_neg (not_or.mpr ⟨hai, haj⟩), if_neg hai, if_neg haj, add_zero]
    have h1 : (∑ a, (if a = i then (1 / 2 : ℂ) else 0)) = 1 / 2 := by
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl]
      · intro b _ hb; rw [if_neg hb]
      · intro h; exact absurd (Finset.mem_univ i) h
    have h2 : (∑ a, (if a = j then (1 / 2 : ℂ) else 0)) = 1 / 2 := by
      rw [Finset.sum_eq_single j]
      · rw [if_pos rfl]
      · intro b _ hb; rw [if_neg hb]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hsplit, h1, h2]
    norm_num

/-- **The obstruction (the tooth can only be pre-cut so far).**
For `0 < l < 1`, the maximally coherent pair state is NOT exactly
pre-compensable under `dephase l`: its de-amplified candidate,
tested against `eᵢ - eⱼ`, has quadratic form `1 - l⁻¹ < 0`. The
reachable set at such `l` is therefore a genuine proper subset of
the density matrices — the states whose coherences are too large
for their populations cannot be pre-compensated. -/
theorem not_precompensable_pairPlus {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1)
    {i j : ι} (hij : i ≠ j) : ¬ PreCompensable l (pairPlus i j) := by
  intro hpre
  have hl : l ≠ 0 := ne_of_gt hl0
  have hDM : IsDensityMatrix (pairPlus i j) := isDensityMatrix_pairPlus hij
  have hpos := (precompensable_iff_pos hl hDM).mp hpre (basisVec i - basisVec j)
  set D : Matrix ι ι ℂ := dephase l⁻¹ (pairPlus i j) with hD
  have hDii : D i i = 1 / 2 := by
    rw [hD, dephase_diag, pairPlus_apply]
    exact pairVec_mul_star i j (Or.inl rfl) (Or.inl rfl)
  have hDjj : D j j = 1 / 2 := by
    rw [hD, dephase_diag, pairPlus_apply]
    exact pairVec_mul_star i j (Or.inr rfl) (Or.inr rfl)
  have hDij : D i j = ((l⁻¹ : ℝ) : ℂ) * (1 / 2) := by
    rw [hD, dephase_apply_off _ _ hij, pairPlus_apply]
    congr 1
    exact pairVec_mul_star i j (Or.inl rfl) (Or.inr rfl)
  have hDji : D j i = ((l⁻¹ : ℝ) : ℂ) * (1 / 2) := by
    rw [hD, dephase_apply_off _ _ (Ne.symm hij), pairPlus_apply]
    congr 1
    exact pairVec_mul_star i j (Or.inr rfl) (Or.inl rfl)
  have hQ : (star (basisVec i - basisVec j)) ⬝ᵥ (D *ᵥ (basisVec i - basisVec j))
      = ((1 - l⁻¹ : ℝ) : ℂ) := by
    have hsum : ∀ a ∉ ({i, j} : Finset ι),
        (star (basisVec i - basisVec j)) a * (D *ᵥ (basisVec i - basisVec j)) a
          = 0 := by
      intro a ha
      have hai : a ≠ i := fun h => ha (by simp [h])
      have haj : a ≠ j := fun h => ha (by simp [h])
      have hx : (basisVec i - basisVec j) a = 0 := by
        show (if a = i then (1 : ℂ) else 0) - (if a = j then (1 : ℂ) else 0) = 0
        rw [if_neg hai, if_neg haj, sub_zero]
      rw [Pi.star_apply, hx, star_zero, zero_mul]
    have hfi : (star (basisVec i - basisVec j)) i
        * (D *ᵥ (basisVec i - basisVec j)) i
        = 1 / 2 - ((l⁻¹ : ℝ) : ℂ) * (1 / 2) := by
      have hx1 : (basisVec i - basisVec j) i = 1 := by
        show (if i = i then (1 : ℂ) else 0) - (if i = j then (1 : ℂ) else 0) = 1
        rw [if_pos rfl, if_neg hij, sub_zero]
      have hmv1 : (D *ᵥ (basisVec i - basisVec j)) i = D i i - D i j := by
        rw [Matrix.mulVec_sub, Pi.sub_apply, mulVec_basisVec, mulVec_basisVec]
      rw [Pi.star_apply, hx1, star_one, one_mul, hmv1, hDii, hDij]
    have hfj : (star (basisVec i - basisVec j)) j
        * (D *ᵥ (basisVec i - basisVec j)) j
        = 1 / 2 - ((l⁻¹ : ℝ) : ℂ) * (1 / 2) := by
      have hx2 : (basisVec i - basisVec j) j = -1 := by
        show (if j = i then (1 : ℂ) else 0) - (if j = j then (1 : ℂ) else 0) = -1
        rw [if_neg (Ne.symm hij), if_pos rfl, zero_sub]
      have hmv2 : (D *ᵥ (basisVec i - basisVec j)) j = D j i - D j j := by
        rw [Matrix.mulVec_sub, Pi.sub_apply, mulVec_basisVec, mulVec_basisVec]
      rw [Pi.star_apply, hx2, hmv2, hDji, hDjj]
      simp only [star_neg, star_one]
      ring
    show (∑ a, (star (basisVec i - basisVec j)) a
        * (D *ᵥ (basisVec i - basisVec j)) a) = ((1 - l⁻¹ : ℝ) : ℂ)
    rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset ι))
      (fun a _ ha => hsum a ha), Finset.sum_pair hij, hfi, hfj]
    push_cast
    ring
  rw [hQ, Complex.ofReal_re] at hpos
  have hli : (1 : ℝ) < l⁻¹ := by
    rw [inv_eq_one_div]
    exact (one_lt_div hl0).mpr hl1
  linarith

end ProperSubset

-- ============================================================================
-- The systematic case: a known unitary error cancels completely
-- ============================================================================

section Unitary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conjugation by an isometry (`star V * V = 1`) preserves
density matrices: Hermiticity by the adjoint computation,
positivity by moving `V` across the quadratic form onto the test
vector, trace by cyclicity. -/
theorem isDensityMatrix_conj {V : Matrix ι ι ℂ} (hV : star V * V = 1)
    {A : Matrix ι ι ℂ} (hA : IsDensityMatrix A) :
    IsDensityMatrix (V * A * star V) := by
  have hSV : (star V)ᴴ = V := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  refine ⟨?_, ?_, ?_⟩
  · show (V * A * star V)ᴴ = V * A * star V
    have hAe : Aᴴ = A := hA.1
    have hVH : Vᴴ = star V := (Matrix.star_eq_conjTranspose V).symm
    rw [Matrix.conjTranspose_mul (V * A) (star V), Matrix.conjTranspose_mul V A,
      hSV, hAe, hVH, Matrix.mul_assoc]
  · intro x
    have hadj : (star x) ᵥ* V = star (star V *ᵥ x) := by
      rw [Matrix.star_mulVec, hSV]
    have hQ : (star x) ⬝ᵥ ((V * A * star V) *ᵥ x)
        = (star (star V *ᵥ x)) ⬝ᵥ (A *ᵥ (star V *ᵥ x)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, hadj]
    rw [hQ]
    exact hA.2.1 _
  · rw [Matrix.trace_mul_comm (V * A) (star V), ← Matrix.mul_assoc, hV,
      Matrix.one_mul]
    exact hA.2.2

/-- **Deliverable 3 (the gear case proper).** Against a KNOWN
unitary error channel — conjugation by a fixed unitary `U` — every
target state is exactly pre-compensable, by `U†`-preparation:
prepare `σ = star U * ρ * U`, itself a density matrix, and the
channel lands it exactly on `ρ`. A systematic deformation is
cancelled completely by machining the preparation wrong in
exactly the inverse way. Contrast `not_precompensable_pairPlus`:
this works because conjugation forgets nothing. -/
theorem unitary_precompensable {U : Matrix ι ι ℂ}
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) :
    ∃ σ : Matrix ι ι ℂ, IsDensityMatrix σ ∧ U * σ * star U = ρ := by
  have h1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hpre : IsDensityMatrix (star U * ρ * U) := by
    have h := isDensityMatrix_conj (V := star U) (A := ρ)
      (by rw [star_star]; exact h1) hρ
    rwa [star_star] at h
  refine ⟨star U * ρ * U, hpre, ?_⟩
  calc U * (star U * ρ * U) * star U
      = (U * star U) * ρ * (U * star U) := by
        rw [Matrix.mul_assoc U ((star U * ρ) * U) (star U),
          Matrix.mul_assoc (star U * ρ) U (star U),
          Matrix.mul_assoc (star U) ρ (U * star U),
          ← Matrix.mul_assoc U (star U) (ρ * (U * star U)),
          ← Matrix.mul_assoc (U * star U) ρ (U * star U)]
    _ = ρ := by rw [h1, Matrix.one_mul, Matrix.mul_one]

end Unitary

end ThetLogos
