import ThetLogos.TernaryThermalDynamics

/-!
# ThetLogos.ViscousLine — VISC-0: the diagonal one-signedness pack (Tiers T1/T2/T5-gloss)

This is a REGISTRATION / formality brick: it assembles the diagonal
one-signedness of objects the corpus already owns — the heat kernel
of `ThermalKernel` and the ternary step of
`TernaryThermalDynamics` — into one named pack, citing the landed
theorems (`heatKernel_apply_diag`, `ternaryStep_diag`) rather than
re-proving them. Its kill K-VISC-0 (a diagonal multiplier outside
`(0, 1]` for `lam ≥ 0`, `t ≥ 0`) is vacuous by `Real.exp_pos` — the
brick is priced S and says so on its face.

"Viscosity" appears only as Jeff's T5 gloss for the line's subject
(one-signed dissipation of the owned heat / ternary step), fenced
as such; the line earns the name only at VISC-2 with the
dissipativity form (VISC-1). Finite level only. No
signature-transition vocabulary is spent anywhere in this line.
NO CLAIM; dials 0/4, unchanged by construction. TTK-2 stays
parked: nothing of its remaining components (`ternaryStepNorm`,
level-set fixed points) is built here.

Tier map:
- T1 (proved, by citation of landed facts): everything below.
- T5 (gloss only, in this header): Jeff's word for the line's
  subject, fenced above.
-/

open Matrix Finset

namespace ThetLogos

section HeatKernelDiagonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Diagonal entries of the heat kernel are positive** (Tier T1 —
    proved by citation): for `t ≥ 0` (any `lam`),
    `0 < heatKernel lam t i i`, via the landed
    `heatKernel_apply_diag` and `Real.exp_pos`. -/
theorem heatKernel_diag_pos (lam : ι → ℝ) {t : ℝ} (_ht : 0 ≤ t) (i : ι) :
    0 < heatKernel lam t i i := by
  rw [heatKernel_apply_diag]
  exact Real.exp_pos _

/-- **Diagonal entries of the heat kernel are at most one**
    (Tier T1 — proved by citation): for `lam i ≥ 0`, `t ≥ 0`,
    `heatKernel lam t i i ≤ 1`, since the exponent `-t * lam i`
    is nonpositive. -/
theorem heatKernel_diag_le_one (lam : ι → ℝ) {t : ℝ} (ht : 0 ≤ t)
    {i : ι} (hi : 0 ≤ lam i) :
    heatKernel lam t i i ≤ 1 := by
  rw [heatKernel_apply_diag]
  have hnonpos : -t * lam i ≤ 0 := by
    have h : 0 ≤ t * lam i := mul_nonneg ht hi
    linarith
  have h := Real.exp_le_exp.mpr hnonpos
  simpa using h

/-- **The pack form for the kernel diagonal** (Tier T1 — proved):
    for `lam i ≥ 0`, `t ≥ 0`, the `i`-th diagonal entry of the
    heat kernel lies in `(0, 1]`. -/
theorem heatKernel_diag_mem_Ioc (lam : ι → ℝ) {t : ℝ} (ht : 0 ≤ t)
    {i : ι} (hi : 0 ≤ lam i) :
    heatKernel lam t i i ∈ Set.Ioc 0 1 :=
  Set.mem_Ioc.mpr ⟨heatKernel_diag_pos lam ht i,
    heatKernel_diag_le_one lam ht hi⟩

end HeatKernelDiagonal

section GeneratorSide

variable {ι : Type*}

/-- **Generator-side one-sign at the diagonal seat** (Tier T1 —
    proved): for `lam i ≥ 0`, the diagonal generator value
    `-lam i` is nonpositive. This is the value VISC-1's generator
    has on matrix units at the diagonal seat. -/
theorem diag_generator_nonpos (lam : ι → ℝ) {i : ι} (hi : 0 ≤ lam i) :
    -lam i ≤ 0 :=
  neg_nonpos.mpr hi

end GeneratorSide

section TernaryStepDiagonal

variable {N : ℕ}

/-- **The ternary step's diagonal multiplier is one-signed**
    (Tier T1 — proved): the diagonal multiplier of the landed
    step, read off `ternaryStep_diag`, is
    `Real.exp (-2 * t * lam i) ∈ (0, 1]` for `lam i ≥ 0`,
    `t ≥ 0`. -/
theorem ternaryStep_diag_multiplier_mem_Ioc (lam : Fin N → ℝ)
    {t : ℝ} (ht : 0 ≤ t) {i : Fin N} (hi : 0 ≤ lam i) :
    Real.exp (-2 * t * lam i) ∈ Set.Ioc 0 1 := by
  have hnonpos : -2 * t * lam i ≤ 0 := by
    have h : 0 ≤ (2 * t) * lam i := mul_nonneg (by linarith) hi
    nlinarith
  have hle : Real.exp (-2 * t * lam i) ≤ 1 := by
    have h := Real.exp_le_exp.mpr hnonpos
    simpa using h
  exact Set.mem_Ioc.mpr ⟨Real.exp_pos _, hle⟩

/-- **Packaging corollary: the stepped diagonal state keeps its
    sign and does not grow** (Tier T1 — proved by citation): for
    a diagonal state `diagState w` with `0 ≤ w i`, rates
    `0 ≤ lam j` for all `j`, and `t ≥ 0`, the `i`-th diagonal
    entry of the stepped state — a complex number, stated here
    through its real part — is nonnegative and at most `w i`.
    From the landed `ternaryStep_diag` and the multiplier pack
    above. -/
theorem ternaryStep_diag_entry_nonneg_le (lam : Fin N → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (hlam : ∀ j, 0 ≤ lam j)
    (w : Fin N → ℝ) {i : Fin N} (hi : 0 ≤ w i) :
    0 ≤ ((ternaryStep lam t (diagState w)) i i).re ∧
      ((ternaryStep lam t (diagState w)) i i).re ≤ w i := by
  have hmul := ternaryStep_diag_multiplier_mem_Ioc lam ht (hlam i)
  rw [ternaryStep_diag]
  simp only [diagState, Matrix.diagonal_apply_eq, Complex.ofReal_re]
  constructor
  · exact mul_nonneg hmul.1.le hi
  · calc Real.exp (-2 * t * lam i) * w i
        ≤ 1 * w i := by
          exact mul_le_mul_of_nonneg_right hmul.2 hi
    _ = w i := one_mul _

end TernaryStepDiagonal

section TernaryGenerator

variable {N : ℕ}

/-- **The ternary generator** (Tier T2): the Lyapunov-form
    generator `L X = -(Λ X + X Λ)`, where
    `Λ = Matrix.diagonal (fun i => (lam i : ℂ))` is the complex
    diagonal rate matrix (the matrix whose exponential schedule
    is `heatKernelC lam t`). This is the candidate generator of
    the ternary step; that it IS the step's derivative at `0`
    is proved below, not assumed — see the K-VISC-1 check in
    `hasDerivAt_ternaryStep_zero`. -/
noncomputable def ternaryGenerator (lam : Fin N → ℝ)
    (X : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  -(Matrix.diagonal (fun i => (lam i : ℂ)) * X
    + X * Matrix.diagonal (fun i => (lam i : ℂ)))

/-- **Generator spectrum on matrix units** (Tier T1 — proved):
    the generator acts on the matrix unit `single i j 1` by the
    scalar `-(lam i + lam j)` — the eigenvalue content
    `-(λᵢ + λⱼ)` of the generator. -/
theorem ternaryGenerator_matrixUnit (lam : Fin N → ℝ) (i j : Fin N) :
    ternaryGenerator lam (Matrix.single i j 1)
      = (-((lam i + lam j : ℝ) : ℂ)) • Matrix.single i j 1 := by
  ext a b
  simp only [ternaryGenerator, Matrix.neg_apply, Matrix.add_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply,
    Matrix.single_apply]
  by_cases h : i = a ∧ j = b
  · rw [ite_eq_left h]
    obtain ⟨rfl, rfl⟩ := h
    push_cast
    ring
  · rw [ite_eq_right h]
    simp

/-- **The generator on a diagonal state, as a matrix** (Tier T1 —
    proved): `ternaryGenerator lam (diagState w)` is the diagonal
    state with weights `-2 * lam i * w i`. -/
theorem ternaryGenerator_diagState (lam : Fin N → ℝ) (w : Fin N → ℝ) :
    ternaryGenerator lam (diagState w)
      = diagState (fun i => -2 * lam i * w i) := by
  ext a b
  by_cases h : a = b
  · subst h
    simp only [ternaryGenerator, Matrix.neg_apply, Matrix.add_apply,
      Matrix.mul_diagonal, diagState, Matrix.diagonal_apply_eq]
    push_cast
    ring
  · simp only [ternaryGenerator, Matrix.neg_apply, Matrix.add_apply,
      Matrix.mul_diagonal, diagState, Matrix.diagonal_apply_ne _ h]
    simp

/-- **Generator diagonal entries** (Tier T1 — proved): the
    diagonal-seat check named by K-VISC-1 — on a diagonal state
    the generator's `i`-th diagonal entry is `-2 * lam i * w i`,
    the `i = j` case of `-(λᵢ + λⱼ)`. -/
theorem ternaryGenerator_diag (lam : Fin N → ℝ) (w : Fin N → ℝ)
    (i : Fin N) :
    (ternaryGenerator lam (diagState w)) i i
      = (-2 * (lam i : ℂ)) * (w i : ℂ) := by
  rw [ternaryGenerator_diagState]
  simp only [diagState, Matrix.diagonal_apply_eq]
  push_cast
  ring

end TernaryGenerator

section GeneratorTheorem

variable {N : ℕ}

/-- **Entry form of the ternary step** (Tier T1 — proved):
    `(ternaryStep lam t X) i j = exp (-t·lam i) * Xᴴ i j *
    exp (-t·lam j)` — the sandwich, entrywise. -/
theorem ternaryStep_apply (lam : Fin N → ℝ) (t : ℝ)
    (X : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    (ternaryStep lam t X) i j
      = (Real.exp (-t * lam i) : ℂ) * Xᴴ i j
        * (Real.exp (-t * lam j) : ℂ) := by
  show (heatKernelC lam t * Xᴴ * heatKernelC lam t) i j = _
  unfold heatKernelC
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- **The generator theorem** (Tier T1 — proved; the shared
    VISC-1 / TTK-2 generator brick): for ALL `X`, the ternary
    step differentiates at `0` to the generator applied to
    `Xᴴ`:
    `HasDerivAt (fun t => ternaryStep lam t X)
      (ternaryGenerator lam Xᴴ) 0`.
    K-VISC-1 CHECK: the derivative is COMPUTED entrywise here —
    each entry is `exp (-t·λᵢ) · (Xᴴ)ᵢⱼ · exp (-t·λⱼ)`, whose
    scalar derivative at `0` is `-(λᵢ + λⱼ) · (Xᴴ)ᵢⱼ`, exactly
    the `-(Λ Xᴴ + Xᴴ Λ)` entry; the predicted form is what the
    computation returns (diagonal entries `-2·lam i`, see
    `ternaryGenerator_diag`), so the kill does not fire.
    Route: entrywise scalar derivatives assembled to the
    matrix derivative by `hasDerivAt_pi`, applied twice. -/
theorem hasDerivAt_ternaryStep_zero (lam : Fin N → ℝ)
    (X : Matrix (Fin N) (Fin N) ℂ) :
    HasDerivAt (fun t => ternaryStep lam t X)
      (ternaryGenerator lam Xᴴ) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hfun : (fun t => (ternaryStep lam t X) i j)
      = (fun t => (Real.exp (-(lam i + lam j) * t) : ℂ)
          * Xᴴ i j) := by
    funext t
    rw [ternaryStep_apply]
    have hexp : (Real.exp (-t * lam i) : ℂ)
        * (Real.exp (-t * lam j) : ℂ)
        = (Real.exp (-(lam i + lam j) * t) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      congr 1
      congr 1
      ring
    calc (Real.exp (-t * lam i) : ℂ) * Xᴴ i j
          * (Real.exp (-t * lam j) : ℂ)
        = ((Real.exp (-t * lam i) : ℂ)
            * (Real.exp (-t * lam j) : ℂ)) * Xᴴ i j := by ring
      _ = (Real.exp (-(lam i + lam j) * t) : ℂ) * Xᴴ i j := by
          rw [hexp]
  rw [hfun]
  have harg : HasDerivAt (fun t : ℝ => -(lam i + lam j) * t)
      (-(lam i + lam j)) (0 : ℝ) := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (-(lam i + lam j))
  have hexpR : HasDerivAt
      (fun t : ℝ => Real.exp (-(lam i + lam j) * t))
      (-(lam i + lam j)) (0 : ℝ) := by
    simpa using harg.exp
  have hcast := hexpR.ofReal_comp
  have hmul := hcast.mul_const (Xᴴ i j)
  convert hmul using 1
  simp only [ternaryGenerator, Matrix.neg_apply, Matrix.add_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  push_cast
  ring

/-- **The generator theorem, Hermitian form** (Tier T1 —
    proved): for Hermitian `X`, the step differentiates at `0`
    to `ternaryGenerator lam X` itself. -/
theorem hasDerivAt_ternaryStep_zero_hermitian (lam : Fin N → ℝ)
    (X : Matrix (Fin N) (Fin N) ℂ) (hX : X.IsHermitian) :
    HasDerivAt (fun t => ternaryStep lam t X)
      (ternaryGenerator lam X) 0 := by
  have h := hasDerivAt_ternaryStep_zero lam X
  rwa [show Xᴴ = X from hX] at h

/-- **Dissipativity at the diagonal seat** (Tier T1 — proved):
    for nonnegative rates and a diagonal state `diagState w`,
    the Hilbert–Schmidt pairing of the state with its generator
    image — in the trace form `tr (Xᴴ * Y)` — has nonpositive
    real part:
    `(trace ((diagState w)ᴴ * ternaryGenerator lam
      (diagState w))).re ≤ 0`.
    Entrywise it is the sum of `-2 * lam i * (w i)^2` terms. -/
theorem ternaryGenerator_dissipative_diag (lam : Fin N → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (w : Fin N → ℝ) :
    (Matrix.trace ((diagState w)ᴴ
      * ternaryGenerator lam (diagState w))).re ≤ 0 := by
  rw [ternaryGenerator_diagState]
  have hmul : (diagState w)ᴴ
      * diagState (fun i => -2 * lam i * w i)
      = diagState (fun i => w i * (-2 * lam i * w i)) := by
    rw [diagState_conjTranspose]
    unfold diagState
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    push_cast
    ring
  rw [hmul]
  have htr : Matrix.trace (diagState (fun i => w i * (-2 * lam i * w i)))
      = ∑ i, ((w i * (-2 * lam i * w i) : ℝ) : ℂ) := by
    simp only [diagState, Matrix.trace_diagonal]
  rw [htr, ← Complex.ofReal_sum, Complex.ofReal_re]
  apply Finset.sum_nonpos
  intro i _
  have h1 : 0 ≤ lam i * (w i * w i) :=
    mul_nonneg (hlam i) (mul_self_nonneg (w i))
  have h2 : w i * (-2 * lam i * w i) = -(2 * (lam i * (w i * w i))) := by
    ring
  rw [h2]
  linarith

end GeneratorTheorem

end ThetLogos
