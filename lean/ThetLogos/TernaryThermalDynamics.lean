import ThetLogos.ThermalKernel
import ThetLogos.TRO
import ThetLogos.ThermalClock

/-!
# ThetLogos.TernaryThermalDynamics — Ternary Thermal Kernel dynamics, brick 1 (Tiers T1/T2/T5-gloss)

Origin (Jeff's fragment, 2026-10-27, reading CONFIRMED by Jeff the same
day): "Ternary Thermal Kernel dynamics" — the ternary operation as the
ThermalKernel's update rule over time. That sentence is Jeff's T5 gloss
and stays a gloss: what is formalized here is exactly the finite,
diagonal content below, in owned vocabulary, and nothing more.

The joint this module fills: `heatKernel` (in `ThermalKernel`) is a
static one-parameter family of real diagonal matrices with a semigroup
law, but it had no action on states and no update rule; `ternaryMat`
(in `TRO`) is a complex three-place operation with no thermal content.
Exactly one bridge was missing — the complex cast of the kernel — and
rule (A) of the scoping memo: the kernel-sandwich step
`ternaryStep lam t X = ternaryMat (heatKernelC lam t) X (heatKernelC lam t)`,
i.e. `K_t * Xᴴ * K_t`. The rival rules were computed and rejected before
this brick was priced: the kernel-middle step (weights square and can
exceed 1; its fixed points are not states) and pure ternary
self-iteration (fixed points are tripotents, spectrum in {−1, 0, 1}, so
no faithful thermal state is fixed) are kills on the record in the
scoping memo, not built here.

What the step does, proved below: the kernel family is closed under the
ternary product (times add), the semigroup law is the ternary law with
middle argument `1`; a diagonal state relaxes entrywise,
`w i ↦ exp (−2t·lam i) * w i`; for `t > 0` a diagonal state is fixed
iff every mode it occupies has rate zero — relaxation to the ground
line, so the faithful clock state is NOT stationary under this step
(the modular `diagFlow` owns KMS stationarity; this step is dissipative
where that flow is automorphic). The raw step contracts the trace: no
trace- or payoff-preservation statement for it is claimed anywhere
(such a claim is pre-killed by the two-mode computation in the scoping
memo); the trace formula and its `≤ 1` bound are what is proved.

## Fences (what this module does NOT claim)

- Finite level, **diagonal seat only**. The general-Hermitian
  reduction is NOT part of this brick.
- `t` is the owned modular/thermal parameter of `heatKernel`; no
  physical time, no continuum kernel, no new physics is imported.
- "Dynamics" in every statement means exactly the maps defined here.
- NO CLAIM on any Millennium statement. This concept touches no dial:
  it computes no measured number and proves no continuum statement.
  Dials 0/4 before and after, unchanged by construction.

Tier map:
- T2 (definitions): `heatKernelC`, `ternaryStep`.
- T1 (proved): everything else.
- T5 (gloss only, in this header): Jeff's confirmed reading, above.
-/

open Matrix Finset

namespace ThetLogos

variable {N : ℕ}

/-- **The complex cast of the heat kernel** (Tier T2): the diagonal
    complex matrix with entries `(exp (−t·lam i) : ℂ)`. This is the
    single bridge definition between the real kernel of
    `ThermalKernel` and the complex ternary operation of `TRO`. -/
noncomputable def heatKernelC (lam : Fin N → ℝ) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun i => (Real.exp (-t * lam i) : ℂ))

/-- The cast is the entrywise `ofReal` map of the real kernel
    (Tier T1 — proved). -/
theorem heatKernelC_eq_map (lam : Fin N → ℝ) (t : ℝ) :
    heatKernelC lam t = (heatKernel lam t).map Complex.ofReal := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [heatKernelC, heatKernel, Matrix.map_apply, Matrix.diagonal_apply_eq]
  · simp [heatKernelC, heatKernel, Matrix.map_apply, Matrix.diagonal_apply, h]

/-- **Entry form of the complex kernel** (Tier T1 — proved):
    `(heatKernelC lam t) i j = if i = j then (exp (−t·lam i) : ℂ) else 0`. -/
theorem heatKernelC_apply (lam : Fin N → ℝ) (t : ℝ) (i j : Fin N) :
    heatKernelC lam t i j
      = if i = j then (Real.exp (-t * lam i) : ℂ) else 0 := by
  by_cases h : i = j
  · subst h
    simp [heatKernelC, Matrix.diagonal_apply_eq]
  · simp [heatKernelC, Matrix.diagonal_apply, h]

/-- The complex kernel at time zero is the identity (Tier T1 — proved). -/
theorem heatKernelC_zero (lam : Fin N → ℝ) : heatKernelC lam 0 = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [heatKernelC_apply]
  · simp [heatKernelC_apply, h]

/-- The complex kernel is self-adjoint (Tier T1 — proved): its entries
    are real, so `conjTranspose` is invisible on it. This is the fact
    that keeps the ternary closure below free of any sign from the
    middle conjugation. -/
theorem heatKernelC_conjTranspose (lam : Fin N → ℝ) (t : ℝ) :
    (heatKernelC lam t)ᴴ = heatKernelC lam t := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases h : i = j
  · subst h
    rw [heatKernelC_apply, if_pos rfl, Complex.star_def, Complex.conj_ofReal]
  · have h' : j ≠ i := fun hj => h hj.symm
    rw [heatKernelC_apply, if_neg h', heatKernelC_apply, if_neg h]
    simp

/-- **Ternary closure of the kernel family** (Tier T1 — proved): the
    ternary product of three kernels is the kernel at the summed time,
    `ternaryMat (K_s) (K_t) (K_u) = K_{s+t+u}`. The middle conjugation
    leaves no sign: the entries are real (see
    `heatKernelC_conjTranspose`). -/
theorem ternary_heatKernel_add3 (lam : Fin N → ℝ) (s t u : ℝ) :
    ternaryMat (heatKernelC lam s) (heatKernelC lam t) (heatKernelC lam u)
      = heatKernelC lam (s + t + u) := by
  show heatKernelC lam s * (heatKernelC lam t)ᴴ * heatKernelC lam u
    = heatKernelC lam (s + t + u)
  rw [heatKernelC_conjTranspose]
  unfold heatKernelC
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  ring_nf

/-- **The semigroup law as a ternary law** (Tier T1 — proved): with
    the middle argument `1 = K_0`, the ternary closure recovers the
    kernel product law — the complex form of `heatKernel_add`. -/
theorem ternary_heatKernel_semigroup (lam : Fin N → ℝ) (s u : ℝ) :
    heatKernelC lam (s + u) = heatKernelC lam s * heatKernelC lam u := by
  have h := ternary_heatKernel_add3 lam s 0 u
  rw [heatKernelC_zero] at h
  rw [show s + 0 + u = s + u by ring] at h
  show heatKernelC lam (s + u)
    = heatKernelC lam s * heatKernelC lam u
  rw [← h]
  show heatKernelC lam s * (1 : Matrix (Fin N) (Fin N) ℂ)ᴴ * heatKernelC lam u
    = heatKernelC lam s * heatKernelC lam u
  rw [Matrix.conjTranspose_one, Matrix.mul_one]

/-- **The clock kernel in power form** (Tier T1 — proved): for a
    thermal clock `C`, the complex kernel of its generator
    `K = −ln ρ` at time `t` is the diagonal of the real powers of the
    weights, `diag (fun j => ((C.weights j)^t : ℂ))` with `Real.rpow` —
    each mode's schedule `exp (t·log wⱼ)` is the power `wⱼ^t`. -/
theorem thermalClock_heatKernelC_rpow {N : ℕ} (C : ThermalClock N) (t : ℝ) :
    heatKernelC (fun j => -Real.log (C.weights j)) t
      = Matrix.diagonal (fun j => ((C.weights j ^ t : ℝ) : ℂ)) := by
  unfold heatKernelC
  congr 1
  funext j
  have hw : 0 < C.weights j := C.faithful j
  rw [Real.rpow_def_of_pos hw]
  congr 1
  congr 1
  ring

/-- **The jewel in complex form** (Tier T1 — proved): at `t = 1` the
    clock's complex kernel IS the state's diagonal density matrix,
    `e^{−K} = ρ` — the complex restatement of
    `thermalClock_heatKernel_one`. -/
theorem thermalClock_heatKernelC_one {N : ℕ} (C : ThermalClock N) :
    heatKernelC (fun j => -Real.log (C.weights j)) 1 = diagState C.weights := by
  rw [thermalClock_heatKernelC_rpow]
  simp [diagState, Real.rpow_one]

/-- The clock's complex kernel at `t = 0` is the identity
    (Tier T1 — proved): every weight to the power zero is one. -/
theorem thermalClock_heatKernelC_zero {N : ℕ} (C : ThermalClock N) :
    heatKernelC (fun j => -Real.log (C.weights j)) 0 = 1 := by
  rw [thermalClock_heatKernelC_rpow]
  simp [Real.rpow_zero]

/-- A diagonal state is self-adjoint (Tier T1 — proved): its entries
    are real casts. -/
theorem diagState_conjTranspose (w : Fin N → ℝ) :
    (diagState w)ᴴ = diagState w := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases h : j = i
  · subst h
    simp only [diagState, Matrix.diagonal_apply_eq]
    rw [Complex.star_def, Complex.conj_ofReal]
  · have h' : i ≠ j := fun hij => h hij.symm
    simp [diagState, Matrix.diagonal_apply, h, h']

/-- **The ternary thermal step** (Tier T2): rule (A) of the scoping
    memo — the kernel-sandwich step
    `ternaryStep lam t X = ternaryMat (heatKernelC lam t) X (heatKernelC lam t)`,
    i.e. `K_t * Xᴴ * K_t`. For Hermitian `X` this is the congruence
    `K_t X K_t`. -/
noncomputable def ternaryStep (lam : Fin N → ℝ) (t : ℝ)
    (X : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ternaryMat (heatKernelC lam t) X (heatKernelC lam t)

/-- The step at time zero is the conjugation itself (Tier T1 —
    proved): `ternaryStep lam 0 X = Xᴴ`, since `K_0 = 1` and the
    ternary operation conjugates its middle argument. On Hermitian
    inputs this is the identity, as it must be. -/
theorem ternaryStep_zero (lam : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℂ) :
    ternaryStep lam 0 X = Xᴴ := by
  show heatKernelC lam 0 * Xᴴ * heatKernelC lam 0 = Xᴴ
  rw [heatKernelC_zero, Matrix.one_mul, Matrix.mul_one]

/-- **The step commutes with `conjTranspose`** (Tier T1 — proved):
    `(ternaryStep lam t X)ᴴ = ternaryStep lam t Xᴴ` — in particular
    the step carries Hermitian matrices to Hermitian matrices. -/
theorem ternaryStep_conjTranspose (lam : Fin N → ℝ) (t : ℝ)
    (X : Matrix (Fin N) (Fin N) ℂ) :
    (ternaryStep lam t X)ᴴ = ternaryStep lam t Xᴴ := by
  show (heatKernelC lam t * Xᴴ * heatKernelC lam t)ᴴ
    = heatKernelC lam t * (Xᴴ)ᴴ * heatKernelC lam t
  simp only [Matrix.conjTranspose_mul, heatKernelC_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- **Diagonal action of the step** (Tier T1 — proved): a diagonal
    state relaxes entrywise, `w i ↦ exp (−2t·lam i) * w i` — each mode
    is scaled by its own schedule, twice over (once per sandwich
    side). The allocation survives as kernel-scaling of each mode. -/
theorem ternaryStep_diag (lam : Fin N → ℝ) (t : ℝ) (w : Fin N → ℝ) :
    ternaryStep lam t (diagState w)
      = diagState (fun i => Real.exp (-2 * t * lam i) * w i) := by
  show heatKernelC lam t * (diagState w)ᴴ * heatKernelC lam t = _
  rw [diagState_conjTranspose]
  unfold heatKernelC diagState
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  have hexp : Real.exp (-t * lam i) * Real.exp (-t * lam i)
      = Real.exp (-2 * t * lam i) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc Real.exp (-t * lam i) * w i * Real.exp (-t * lam i)
      = w i * (Real.exp (-t * lam i) * Real.exp (-t * lam i)) := by ring
    _ = Real.exp (-2 * t * lam i) * w i := by rw [hexp]; ring

/-- If `exp (−2t·l) = 1` at some `t > 0`, the rate is zero
    (Tier T1 — proved). -/
theorem exp_neg_two_mul_eq_one {t : ℝ} (ht : 0 < t) {l : ℝ}
    (h : Real.exp (-2 * t * l) = 1) : l = 0 := by
  have h4 : -2 * t * l = 0 := by
    have h5 : Real.exp (-2 * t * l) = Real.exp 0 := by rw [h, Real.exp_zero]
    exact Real.exp_injective h5
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exfalso
    rcases mul_eq_zero.mp h5 with h6 | h6
    · norm_num at h6
    · exact ht.ne' h6
  · exact h5

/-- If a mode's weight is unchanged by its relaxation factor at some
    `t > 0`, the weight is zero or the rate is (Tier T1 — proved). -/
theorem eq_of_exp_mul_eq_self {t : ℝ} (ht : 0 < t) {l w : ℝ}
    (h : Real.exp (-2 * t * l) * w = w) : w = 0 ∨ l = 0 := by
  by_cases hw : w = 0
  · exact Or.inl hw
  · refine Or.inr (exp_neg_two_mul_eq_one ht ?_)
    exact mul_right_cancel₀ hw (by rw [one_mul]; exact h)

/-- **Fixed diagonal states are exactly the ground-line states**
    (Tier T1 — proved): for `t > 0`, a diagonal state is fixed by the
    step iff every mode it occupies has rate zero,
    `∀ i, w i = 0 ∨ lam i = 0` — relaxation to the ground line. In
    particular no faithful state with a positive rate is stationary
    under the ternary step; KMS stationarity belongs to the modular
    flow, not to this dissipative step. -/
theorem ternaryStep_fixed_diag_iff (lam : Fin N → ℝ) {t : ℝ} (ht : 0 < t)
    (w : Fin N → ℝ) :
    ternaryStep lam t (diagState w) = diagState w
      ↔ ∀ i, w i = 0 ∨ lam i = 0 := by
  rw [ternaryStep_diag]
  constructor
  · intro h i
    have hi := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i i) h
    simp only [diagState, Matrix.diagonal_apply_eq] at hi
    exact eq_of_exp_mul_eq_self ht (Complex.ofReal_inj.mp hi)
  · intro h
    congr 1
    funext i
    rcases h i with hw | hl
    · simp [hw]
    · simp [hl]

/-- **Trace of the stepped diagonal state** (Tier T1 — proved):
    `trace (ternaryStep lam t (diagState w)) = ∑ i, (exp (−2t·lam i) * w i : ℂ)`.
    The raw step contracts the trace in general — this formula, not
    any preservation claim, is the statement. -/
theorem ternaryStep_trace (lam : Fin N → ℝ) (t : ℝ) (w : Fin N → ℝ) :
    Matrix.trace (ternaryStep lam t (diagState w))
      = ∑ i, ((Real.exp (-2 * t * lam i) * w i : ℝ) : ℂ) := by
  rw [ternaryStep_diag]
  simp only [diagState, Matrix.trace_diagonal]

/-- The trace formula in real form (Tier T1 — proved): the trace is a
    nonnegative combination of the weights whenever the rates and the
    weights are, and its real part is the real sum. -/
theorem ternaryStep_trace_re (lam : Fin N → ℝ) (t : ℝ) (w : Fin N → ℝ) :
    (Matrix.trace (ternaryStep lam t (diagState w))).re
      = ∑ i, Real.exp (-2 * t * lam i) * w i := by
  rw [ternaryStep_trace, ← Complex.ofReal_sum, Complex.ofReal_re]

/-- **The stepped trace is at most one** (Tier T1 — proved): for
    nonnegative rates, a state (nonnegative weights summing to one),
    and `t ≥ 0`, the real trace of the stepped state is `≤ 1` — the
    raw step only contracts. -/
theorem ternaryStep_trace_le_one (lam : Fin N → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hlam : ∀ i, 0 ≤ lam i) (w : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    (Matrix.trace (ternaryStep lam t (diagState w))).re ≤ 1 := by
  rw [ternaryStep_trace_re, ← hsum]
  apply Finset.sum_le_sum
  intro i _
  have h2 : (0 : ℝ) ≤ t * lam i := mul_nonneg ht (hlam i)
  have h1 : Real.exp (-2 * t * lam i) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have h3 : -2 * t * lam i = -(2 * (t * lam i)) := by ring
    rw [h3]
    exact neg_nonpos.mpr (mul_nonneg (by norm_num) h2)
  calc Real.exp (-2 * t * lam i) * w i ≤ 1 * w i :=
        mul_le_mul_of_nonneg_right h1 (hw i)
    _ = w i := one_mul _

/-- **The stepped trace equals one exactly on the ground line**
    (Tier T1 — proved): for `t > 0`, nonnegative rates, and a state,
    the real trace of the stepped state is `1` iff every occupied mode
    has rate zero — the same ground-line condition as the fixed-point
    characterization. -/
theorem ternaryStep_trace_eq_one_iff (lam : Fin N → ℝ) {t : ℝ} (ht : 0 < t)
    (hlam : ∀ i, 0 ≤ lam i) (w : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    (Matrix.trace (ternaryStep lam t (diagState w))).re = 1
      ↔ ∀ i, w i = 0 ∨ lam i = 0 := by
  rw [ternaryStep_trace_re]
  have hle : ∀ i ∈ Finset.univ, Real.exp (-2 * t * lam i) * w i ≤ w i := by
    intro i _
    have h2 : (0 : ℝ) ≤ t * lam i := mul_nonneg ht.le (hlam i)
    have h1 : Real.exp (-2 * t * lam i) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have h3 : -2 * t * lam i = -(2 * (t * lam i)) := by ring
      rw [h3]
      exact neg_nonpos.mpr (mul_nonneg (by norm_num) h2)
    calc Real.exp (-2 * t * lam i) * w i ≤ 1 * w i :=
          mul_le_mul_of_nonneg_right h1 (hw i)
      _ = w i := one_mul _
  constructor
  · intro h1
    have h2 : ∑ i, Real.exp (-2 * t * lam i) * w i = ∑ i, w i := by
      rw [h1, hsum]
    have heq := (Finset.sum_eq_sum_iff_of_le hle).mp h2
    intro i
    exact eq_of_exp_mul_eq_self ht (heq i (Finset.mem_univ i))
  · intro h
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro i _
    rcases h i with hw0 | hl0
    · simp [hw0]
    · simp [hl0]

end ThetLogos
