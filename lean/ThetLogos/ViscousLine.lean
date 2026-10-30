import ThetLogos.TernaryThermalDynamics
import ThetLogos.HermitianReduction
import Mathlib.Analysis.Matrix.PosDef

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

section GeneralStep

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The general-Hermitian step** (Tier T2): the dissipative
    step at a general Hermitian seat,
    `stepGen K t X = heatKernelGen K t * X * (heatKernelGen K t)ᴴ`.
    The PSD hypothesis `K.PosSemidef` is LOAD-BEARING for every
    contraction / multiplier-bound statement about this step
    below and is stated exactly on each of them: for indefinite
    Hermitian `K` the eigenbasis multipliers exceed `1` — that
    is where the master kill K-VISC lives, and this brick's
    claims are fenced to the Hermitian PSD scope precisely so
    the kill has a clean statement to register against. -/
noncomputable def stepGen (K : Matrix ι ι ℂ) (t : ℝ)
    (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  heatKernelGen K t * X * (heatKernelGen K t)ᴴ

/-- **The general heat kernel is self-adjoint at a Hermitian
    seat** (Tier T1 — proved): for `hK : K.IsHermitian`,
    `(heatKernelGen K t)ᴴ = heatKernelGen K t`, so the sandwich
    in `stepGen` is a congruence. Route: the exp route — the
    scaled generator `(-t) • K` is Hermitian (the scalar is a
    real cast, fixed by conjugation, and `K` is Hermitian), and
    Mathlib's `Matrix.IsHermitian.exp` closes it. -/
theorem heatKernelGen_isHermitian {K : Matrix ι ι ℂ}
    (hK : K.IsHermitian) (t : ℝ) :
    (heatKernelGen K t)ᴴ = heatKernelGen K t := by
  have hscale : ((-(t : ℂ)) • K).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hK.eq]
    congr 1
    have hcast : (-(t : ℂ)) = ((-t : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.star_def]
    exact Complex.conj_ofReal (-t)
  exact hscale.exp

end GeneralStep

open scoped ComplexOrder

section EigenbasisMultipliers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Entry form of the diagonal-kernel sandwich** (Tier T1 —
    proved): the conjugate-diagonal kernel of
    `HermitianReduction` sandwiches entrywise exactly as
    `heatKernelC` does at the diagonal seat. -/
theorem hermitianDiagKernel_sandwich_apply (d : ι → ℝ) (t : ℝ)
    (Y : Matrix ι ι ℂ) (i j : ι) :
    (hermitianDiagKernel d t * Y * hermitianDiagKernel d t) i j
      = (Real.exp (-t * d i) : ℂ) * Y i j
        * (Real.exp (-t * d j) : ℂ) := by
  show (hermitianDiagKernel d t * Y * hermitianDiagKernel d t) i j = _
  unfold hermitianDiagKernel
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- **The diagonal kernel on a matrix unit** (Tier T1 —
    proved): the sandwich of the unit `single i j 1` by the
    diagonal schedule kernel is the scalar
    `exp (-t * (d i + d j))` times the unit — the transported
    form of VISC-1's matrix-unit spectrum. -/
theorem hermitianDiagKernel_single_sandwich (d : ι → ℝ) (t : ℝ)
    (i j : ι) :
    hermitianDiagKernel d t * Matrix.single i j 1
        * hermitianDiagKernel d t
      = (Real.exp (-t * (d i + d j)) : ℂ)
        • Matrix.single i j 1 := by
  ext a b
  rw [hermitianDiagKernel_sandwich_apply]
  simp only [Matrix.smul_apply, Matrix.single_apply]
  by_cases h : i = a ∧ j = b
  · rw [ite_eq_left h]
    obtain ⟨rfl, rfl⟩ := h
    simp only [smul_eq_mul, mul_one]
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    congr 1
    ring
  · rw [ite_eq_right h]
    simp

/-- **Eigenbasis multipliers of the general step** (Tier T1 —
    proved): at a Hermitian seat `K`, with `U` the eigenvector
    unitary and `d` the eigenvalue function of `K`, the step
    acts on the eigenbasis unit
    `F i j = U * single i j 1 * star U` by the scalar
    multiplier `exp (-t * (d i + d j))`:
    `stepGen K t (F i j) = (exp (-t * (d i + d j)) : ℂ) • F i j`.
    Route: self-adjointness of the kernel
    (`heatKernelGen_isHermitian`), the conjugation formula
    (`heatKernelGen_eq_conj`), cancellation of the middle
    unitary pair (`conj_mul_conj`), and the diagonal-kernel
    unit computation above. -/
theorem stepGen_eigenbasis {K : Matrix ι ι ℂ} (hK : K.IsHermitian)
    (t : ℝ) (i j : ι) :
    stepGen K t ((hK.eigenvectorUnitary : Matrix ι ι ℂ)
        * Matrix.single i j 1
        * star (hK.eigenvectorUnitary : Matrix ι ι ℂ))
      = (Real.exp (-t * (hK.eigenvalues i + hK.eigenvalues j)) : ℂ)
        • ((hK.eigenvectorUnitary : Matrix ι ι ℂ)
          * Matrix.single i j 1
          * star (hK.eigenvectorUnitary : Matrix ι ι ℂ)) := by
  have hU : star (hK.eigenvectorUnitary : Matrix ι ι ℂ)
      * (hK.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  unfold stepGen
  rw [heatKernelGen_isHermitian hK, heatKernelGen_eq_conj hK,
    conj_mul_conj _ _ _ hU, conj_mul_conj _ _ _ hU,
    hermitianDiagKernel_single_sandwich, mul_smul_comm, smul_mul_assoc]

/-- **The eigenbasis multiplier lies in `(0, 1]`** (Tier T1 —
    proved): for PSD Hermitian `K` — the load-bearing scope
    hypothesis, stated exactly — and `t ≥ 0`, every eigenbasis
    multiplier `exp (-t * (d i + d j))` lies in `(0, 1]`, since
    a PSD Hermitian matrix has nonnegative eigenvalues
    (`Matrix.PosSemidef.eigenvalues_nonneg`). Outside this
    scope (indefinite Hermitian `K`) the multiplier can exceed
    `1`: that amplification seat is K-VISC's, fenced out here. -/
theorem stepGen_multiplier_mem_Ioc {K : Matrix ι ι ℂ}
    (hK : K.IsHermitian) (hKpos : K.PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) (i j : ι) :
    Real.exp (-t * (hK.eigenvalues i + hK.eigenvalues j))
      ∈ Set.Ioc 0 1 := by
  have hi : 0 ≤ hK.eigenvalues i :=
    Matrix.PosSemidef.eigenvalues_nonneg hKpos i
  have hj : 0 ≤ hK.eigenvalues j :=
    Matrix.PosSemidef.eigenvalues_nonneg hKpos j
  have hnonpos : -t * (hK.eigenvalues i + hK.eigenvalues j) ≤ 0 := by
    have h : 0 ≤ t * (hK.eigenvalues i + hK.eigenvalues j) :=
      mul_nonneg ht (add_nonneg hi hj)
    linarith
  have hle : Real.exp (-t * (hK.eigenvalues i + hK.eigenvalues j))
      ≤ 1 := by
    have h := Real.exp_le_exp.mpr hnonpos
    simpa using h
  exact Set.mem_Ioc.mpr ⟨Real.exp_pos _, hle⟩

/-- **The multiplier equals `1` exactly on the ground line**
    (Tier T1 — proved): for PSD Hermitian `K` and `t > 0`, the
    eigenbasis multiplier `exp (-t * (d i + d j))` equals `1`
    iff `d i = 0 ∧ d j = 0` — the step is the identity exactly
    on the ground-eigenspace units and strictly contracting on
    every other eigenbasis unit (by
    `stepGen_multiplier_mem_Ioc`, whose bound is then `< 1`
    off the ground line). -/
theorem stepGen_multiplier_eq_one_iff {K : Matrix ι ι ℂ}
    (hK : K.IsHermitian) (hKpos : K.PosSemidef)
    {t : ℝ} (ht : 0 < t) (i j : ι) :
    Real.exp (-t * (hK.eigenvalues i + hK.eigenvalues j)) = 1
      ↔ hK.eigenvalues i = 0 ∧ hK.eigenvalues j = 0 := by
  have hi : 0 ≤ hK.eigenvalues i :=
    Matrix.PosSemidef.eigenvalues_nonneg hKpos i
  have hj : 0 ≤ hK.eigenvalues j :=
    Matrix.PosSemidef.eigenvalues_nonneg hKpos j
  constructor
  · intro h
    have h0 : -t * (hK.eigenvalues i + hK.eigenvalues j) = 0 :=
      Real.exp_injective (show
        Real.exp (-t * (hK.eigenvalues i + hK.eigenvalues j))
          = Real.exp 0 by rw [h]; simp)
    have hsum : hK.eigenvalues i + hK.eigenvalues j = 0 := by
      rcases mul_eq_zero.mp h0 with h2 | h2
      · linarith
      · exact h2
    exact (add_eq_zero_iff_of_nonneg hi hj).mp hsum
  · rintro ⟨hi0, hj0⟩
    simp [hi0, hj0]

end EigenbasisMultipliers

section TransportedGenerator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The transported generator** (Tier T2): the Lyapunov-form
    generator at a general seat, `genTransported K X = -(K * X
    + X * K)` — VISC-1's `ternaryGenerator` with the diagonal
    rate matrix replaced by a general `K`. That it IS the
    derivative of `stepGen` at `0` is proved below
    (`hasDerivAt_stepGen_zero`), not assumed. -/
def genTransported (K X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  -(K * X + X * K)

/-- **Generator entries at the diagonal seat** (Tier T1 —
    proved): with `Λ` the diagonal cast of `d`,
    `(genTransported Λ Y) i j = -((d i + d j : ℝ) : ℂ) * Y i j`
    — the `-(λᵢ + λⱼ)` spectrum, entrywise. -/
theorem genTransported_diagonal_apply (d : ι → ℝ) (Y : Matrix ι ι ℂ)
    (i j : ι) :
    (genTransported (Matrix.diagonal (fun i => ((d i : ℂ)))) Y) i j
      = (-((d i + d j : ℝ) : ℂ)) * Y i j := by
  simp only [genTransported, Matrix.neg_apply, Matrix.add_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  push_cast
  ring

/-- **The diagonal sandwich differentiates to the diagonal
    generator** (Tier T1 — proved): the VISC-1 entrywise
    computation, run for the conjugate-diagonal kernel of
    `HermitianReduction` and a plain middle argument:
    `HasDerivAt (fun t => D t * Y * D t)
      (genTransported Λ Y) 0`. -/
theorem hasDerivAt_diagSandwich_zero (d : ι → ℝ) (Y : Matrix ι ι ℂ) :
    HasDerivAt
      (fun t => hermitianDiagKernel d t * Y * hermitianDiagKernel d t)
      (genTransported (Matrix.diagonal (fun i => ((d i : ℂ)))) Y) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hfun : (fun t => (hermitianDiagKernel d t * Y
        * hermitianDiagKernel d t) i j)
      = (fun t => (Real.exp (-(d i + d j) * t) : ℂ) * Y i j) := by
    funext t
    rw [hermitianDiagKernel_sandwich_apply]
    have hexp : (Real.exp (-t * d i) : ℂ)
        * (Real.exp (-t * d j) : ℂ)
        = (Real.exp (-(d i + d j) * t) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      congr 1
      congr 1
      ring
    calc (Real.exp (-t * d i) : ℂ) * Y i j
          * (Real.exp (-t * d j) : ℂ)
        = ((Real.exp (-t * d i) : ℂ)
            * (Real.exp (-t * d j) : ℂ)) * Y i j := by ring
      _ = (Real.exp (-(d i + d j) * t) : ℂ) * Y i j := by
          rw [hexp]
  rw [hfun]
  have harg : HasDerivAt (fun t : ℝ => -(d i + d j) * t)
      (-(d i + d j)) (0 : ℝ) := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (-(d i + d j))
  have hexpR : HasDerivAt
      (fun t : ℝ => Real.exp (-(d i + d j) * t))
      (-(d i + d j)) (0 : ℝ) := by
    simpa using harg.exp
  have hcast := hexpR.ofReal_comp
  have hmul := hcast.mul_const (Y i j)
  convert hmul using 1
  rw [genTransported_diagonal_apply]
  push_cast
  ring

/-- **The general step is the conjugated diagonal sandwich**
    (Tier T1 — proved): with `U` the eigenvector unitary of a
    Hermitian `K` and `Y = star U * X * U` the eigenbasis
    coordinates of `X`,
    `stepGen K t X = U * (D t * Y * D t) * star U`. -/
theorem stepGen_eq_conj_sandwich {K : Matrix ι ι ℂ}
    (hK : K.IsHermitian) (t : ℝ) (X : Matrix ι ι ℂ) :
    stepGen K t X
      = (hK.eigenvectorUnitary : Matrix ι ι ℂ)
        * (hermitianDiagKernel hK.eigenvalues t
          * (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * X
            * (hK.eigenvectorUnitary : Matrix ι ι ℂ))
          * hermitianDiagKernel hK.eigenvalues t)
        * star (hK.eigenvectorUnitary : Matrix ι ι ℂ) := by
  have hU : star (hK.eigenvectorUnitary : Matrix ι ι ℂ)
      * (hK.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  have hU' : (hK.eigenvectorUnitary : Matrix ι ι ℂ)
      * star (hK.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_mul_star_self _
  have hX : X = (hK.eigenvectorUnitary : Matrix ι ι ℂ)
      * (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * X
        * (hK.eigenvectorUnitary : Matrix ι ι ℂ))
      * star (hK.eigenvectorUnitary : Matrix ι ι ℂ) :=
    (conj_star_collapse _ _ hU hU').symm
  calc stepGen K t X
      = heatKernelGen K t * X * heatKernelGen K t := by
        rw [stepGen, heatKernelGen_isHermitian hK]
    _ = ((hK.eigenvectorUnitary : Matrix ι ι ℂ)
          * hermitianDiagKernel hK.eigenvalues t
          * star (hK.eigenvectorUnitary : Matrix ι ι ℂ))
        * ((hK.eigenvectorUnitary : Matrix ι ι ℂ)
          * (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * X
            * (hK.eigenvectorUnitary : Matrix ι ι ℂ))
          * star (hK.eigenvectorUnitary : Matrix ι ι ℂ))
        * ((hK.eigenvectorUnitary : Matrix ι ι ℂ)
          * hermitianDiagKernel hK.eigenvalues t
          * star (hK.eigenvectorUnitary : Matrix ι ι ℂ)) := by
        conv_lhs => rw [heatKernelGen_eq_conj hK, hX]
    _ = (hK.eigenvectorUnitary : Matrix ι ι ℂ)
          * (hermitianDiagKernel hK.eigenvalues t
            * (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * X
              * (hK.eigenvectorUnitary : Matrix ι ι ℂ))
            * hermitianDiagKernel hK.eigenvalues t)
          * star (hK.eigenvectorUnitary : Matrix ι ι ℂ) := by
        rw [conj_mul_conj _ _ _ hU, conj_mul_conj _ _ _ hU]

/-- **The generator transports by conjugation** (Tier T1 —
    proved): `U * genTransported Λ Y * star U
    = genTransported K X` for `Y = star U * X * U`, by the
    spectral form of `K` and the same unitary cancellations. -/
theorem genTransported_conj {K : Matrix ι ι ℂ} (hK : K.IsHermitian)
    (X : Matrix ι ι ℂ) :
    (hK.eigenvectorUnitary : Matrix ι ι ℂ)
        * genTransported
          (Matrix.diagonal (fun i => ((hK.eigenvalues i : ℂ))))
          (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * X
            * (hK.eigenvectorUnitary : Matrix ι ι ℂ))
        * star (hK.eigenvectorUnitary : Matrix ι ι ℂ)
      = genTransported K X := by
  have hU : star (hK.eigenvectorUnitary : Matrix ι ι ℂ)
      * (hK.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  have hU' : (hK.eigenvectorUnitary : Matrix ι ι ℂ)
      * star (hK.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_mul_star_self _
  have hX : X = (hK.eigenvectorUnitary : Matrix ι ι ℂ)
      * (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * X
        * (hK.eigenvectorUnitary : Matrix ι ι ℂ))
      * star (hK.eigenvectorUnitary : Matrix ι ι ℂ) :=
    (conj_star_collapse _ _ hU hU').symm
  have e1 : K * X = (hK.eigenvectorUnitary : Matrix ι ι ℂ)
      * (Matrix.diagonal (fun i => ((hK.eigenvalues i : ℂ)))
        * (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * X
          * (hK.eigenvectorUnitary : Matrix ι ι ℂ)))
      * star (hK.eigenvectorUnitary : Matrix ι ι ℂ) := by
    calc K * X
        = ((hK.eigenvectorUnitary : Matrix ι ι ℂ)
            * Matrix.diagonal (fun i => ((hK.eigenvalues i : ℂ)))
            * star (hK.eigenvectorUnitary : Matrix ι ι ℂ))
          * ((hK.eigenvectorUnitary : Matrix ι ι ℂ)
            * (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * X
              * (hK.eigenvectorUnitary : Matrix ι ι ℂ))
            * star (hK.eigenvectorUnitary : Matrix ι ι ℂ)) := by
          conv_lhs => rw [hermitian_spectral_form hK, hX]
      _ = (hK.eigenvectorUnitary : Matrix ι ι ℂ)
            * (Matrix.diagonal (fun i => ((hK.eigenvalues i : ℂ)))
              * (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * X
                * (hK.eigenvectorUnitary : Matrix ι ι ℂ)))
            * star (hK.eigenvectorUnitary : Matrix ι ι ℂ) :=
          conj_mul_conj _ _ _ hU
  have e2 : X * K = (hK.eigenvectorUnitary : Matrix ι ι ℂ)
      * ((star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * X
          * (hK.eigenvectorUnitary : Matrix ι ι ℂ))
        * Matrix.diagonal (fun i => ((hK.eigenvalues i : ℂ))))
      * star (hK.eigenvectorUnitary : Matrix ι ι ℂ) := by
    calc X * K
        = ((hK.eigenvectorUnitary : Matrix ι ι ℂ)
            * (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * X
              * (hK.eigenvectorUnitary : Matrix ι ι ℂ))
            * star (hK.eigenvectorUnitary : Matrix ι ι ℂ))
          * ((hK.eigenvectorUnitary : Matrix ι ι ℂ)
            * Matrix.diagonal (fun i => ((hK.eigenvalues i : ℂ)))
            * star (hK.eigenvectorUnitary : Matrix ι ι ℂ)) := by
          conv_lhs => rw [hermitian_spectral_form hK, hX]
      _ = (hK.eigenvectorUnitary : Matrix ι ι ℂ)
            * ((star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * X
                * (hK.eigenvectorUnitary : Matrix ι ι ℂ))
              * Matrix.diagonal (fun i => ((hK.eigenvalues i : ℂ))))
            * star (hK.eigenvectorUnitary : Matrix ι ι ℂ) :=
          conj_mul_conj _ _ _ hU
  unfold genTransported
  rw [e1, e2]
  noncomm_ring

/-- **Derivatives transport through a constant conjugation**
    (Tier T1 — proved): if `g` differentiates at `0` to `g'`,
    so does the conjugated path `t ↦ U * g t * star U`, to
    `U * g' * star U`. Entrywise: each entry is a finite sum of
    constant multiples of entries of `g`. (The direct
    `HasDerivAt.const_mul` route hits a normed-ring instance
    diamond for matrices in this pin; the entrywise route is
    the one VISC-1 already uses, and is recorded here.) -/
theorem hasDerivAt_conj_sandwich (U : Matrix ι ι ℂ)
    {g : ℝ → Matrix ι ι ℂ} {g' : Matrix ι ι ℂ}
    (hg : HasDerivAt g g' 0) :
    HasDerivAt (fun t => U * g t * star U) (U * g' * star U) 0 := by
  have hval : ∀ (M : Matrix ι ι ℂ) (i j : ι),
      (U * M * star U) i j
        = ∑ a, ∑ b, U i a * M a b * star U b j := by
    intro M i j
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hterm : ∀ a b : ι, HasDerivAt
      (fun t => U i a * g t a b * star U b j)
      (U i a * g' a b * star U b j) 0 := by
    intro a b
    have h := hasDerivAt_pi.mp (hasDerivAt_pi.mp hg a) b
    exact (h.const_mul (U i a)).mul_const (star U b j)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun a _ => HasDerivAt.fun_sum (u := Finset.univ)
      (fun b _ => hterm a b))
  have hfun : (fun t => (U * g t * star U) i j)
      = (fun t => ∑ a, ∑ b, U i a * g t a b * star U b j) := by
    funext t
    exact hval (g t) i j
  rw [hfun]
  convert hsum using 1
  exact hval g' i j

/-- **The generator theorem at the general seat** (Tier T1 —
    proved): for Hermitian `K` and Hermitian `X`, the general
    step differentiates at `0` to the transported generator:
    `HasDerivAt (fun t => stepGen K t X) (genTransported K X) 0`.
    K-VISC-2 CHECK: the transport carries — the kernel is
    self-adjoint at the Hermitian seat
    (`heatKernelGen_isHermitian`), the step is the conjugated
    diagonal sandwich (`stepGen_eq_conj_sandwich`), the
    diagonal sandwich differentiates to the diagonal generator
    (`hasDerivAt_diagSandwich_zero`, the VISC-1 computation),
    and the generator itself conjugates back
    (`genTransported_conj`) — so the named obstruction does
    not fire and the brick lands FULL. Route: conjugation
    transport of the entrywise diagonal derivative, through
    the entrywise conjugation transport
    (`hasDerivAt_conj_sandwich`). -/
theorem hasDerivAt_stepGen_zero {K : Matrix ι ι ℂ}
    (hK : K.IsHermitian) (X : Matrix ι ι ℂ) (_hX : X.IsHermitian) :
    HasDerivAt (fun t => stepGen K t X) (genTransported K X) 0 := by
  have hderiv := hasDerivAt_diagSandwich_zero hK.eigenvalues
    (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * X
      * (hK.eigenvectorUnitary : Matrix ι ι ℂ))
  have htrans := hasDerivAt_conj_sandwich
    (hK.eigenvectorUnitary : Matrix ι ι ℂ) hderiv
  have h2 : HasDerivAt (fun t => stepGen K t X)
      ((hK.eigenvectorUnitary : Matrix ι ι ℂ)
        * genTransported
          (Matrix.diagonal (fun i => ((hK.eigenvalues i : ℂ))))
          (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * X
            * (hK.eigenvectorUnitary : Matrix ι ι ℂ))
        * star (hK.eigenvectorUnitary : Matrix ι ι ℂ)) 0 := by
    convert htrans using 1
    funext t
    exact stepGen_eq_conj_sandwich hK t X
  rwa [genTransported_conj hK X] at h2

end TransportedGenerator

open scoped ComplexOrder

section Dissipativity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Dissipativity at the diagonal seat, trace form** (Tier
    T1 — proved): for nonnegative rates `d` and any `Y`, the
    Hilbert–Schmidt pairing of `Y` with its diagonal-generator
    image, in the trace form `tr (Yᴴ * genTransported Λ Y)`,
    has nonpositive real part. Entrywise the trace is
    `-∑ i j, (d i + d j) * ‖Y j i‖²`. -/
theorem genTransported_diagonal_dissipative (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) (Y : Matrix ι ι ℂ) :
    (Matrix.trace (Yᴴ * genTransported
      (Matrix.diagonal (fun i => ((d i : ℂ)))) Y)).re ≤ 0 := by
  have hterm : ∀ (z : ℂ) (c : ℝ),
      star z * ((-(c : ℂ)) * z)
        = ((-(c * ‖z‖ ^ 2) : ℝ) : ℂ) := by
    intro z c
    rw [show star z * ((-(c : ℂ)) * z)
        = (-(c : ℂ)) * (star z * z) by ring,
      Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  have hcast : Matrix.trace (Yᴴ * genTransported
        (Matrix.diagonal (fun i => ((d i : ℂ)))) Y)
      = ((-(∑ i, ∑ j, (d j + d i) * ‖Y j i‖ ^ 2) : ℝ)
        : ℂ) := by
    have h1 : Matrix.trace (Yᴴ * genTransported
          (Matrix.diagonal (fun i => ((d i : ℂ)))) Y)
        = ∑ i, (Yᴴ * genTransported
          (Matrix.diagonal (fun i => ((d i : ℂ)))) Y) i i := rfl
    have h2 : ∀ i : ι, (Yᴴ * genTransported
          (Matrix.diagonal (fun i => ((d i : ℂ)))) Y) i i
        = ((-(∑ j, (d j + d i) * ‖Y j i‖ ^ 2) : ℝ) : ℂ) := by
      intro i
      calc (Yᴴ * genTransported
              (Matrix.diagonal (fun i => ((d i : ℂ)))) Y) i i
          = ∑ j, ((-( (d j + d i) * ‖Y j i‖ ^ 2) : ℝ) : ℂ) := by
            rw [Matrix.mul_apply]
            exact Finset.sum_congr rfl (fun j _ => by
              rw [Matrix.conjTranspose_apply,
                genTransported_diagonal_apply, hterm])
        _ = ((∑ j, -( (d j + d i) * ‖Y j i‖ ^ 2) : ℝ) : ℂ) :=
            (Complex.ofReal_sum Finset.univ _).symm
        _ = ((-(∑ j, (d j + d i) * ‖Y j i‖ ^ 2) : ℝ) : ℂ) := by
            rw [Finset.sum_neg_distrib]
    calc Matrix.trace (Yᴴ * genTransported
          (Matrix.diagonal (fun i => ((d i : ℂ)))) Y)
        = ∑ i, ((-(∑ j, (d j + d i) * ‖Y j i‖ ^ 2) : ℝ) : ℂ) := by
          rw [h1]
          exact Finset.sum_congr rfl (fun i _ => h2 i)
      _ = ((∑ i, -(∑ j, (d j + d i) * ‖Y j i‖ ^ 2) : ℝ) : ℂ) :=
          (Complex.ofReal_sum Finset.univ _).symm
      _ = ((-(∑ i, ∑ j, (d j + d i) * ‖Y j i‖ ^ 2) : ℝ) : ℂ) := by
          rw [Finset.sum_neg_distrib]
  rw [hcast, Complex.ofReal_re]
  have hnonneg : 0 ≤ ∑ i, ∑ j,
      (d i + d j) * ‖Y j i‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (add_nonneg (hd i) (hd j))
      (pow_nonneg (norm_nonneg _) 2)
  have hsum : ∑ i, ∑ j, (d j + d i) * ‖Y j i‖ ^ 2
      = ∑ i, ∑ j, (d i + d j) * ‖Y j i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [add_comm (d j) (d i)]
  rw [hsum]
  linarith

/-- **The dissipativity trace transports by conjugation**
    (Tier T1 — proved): for Hermitian `K` and Hermitian `X`,
    with `Y = star U * X * U` the eigenbasis coordinates of
    `X` (themselves Hermitian),
    `tr (Xᴴ * genTransported K X)
      = tr (Yᴴ * genTransported Λ Y)`
    — by `genTransported_conj`, the unitary cancellation
    `conj_mul_conj`, and cyclicity of the trace. -/
theorem trace_genTransported_conj {K : Matrix ι ι ℂ}
    (hK : K.IsHermitian) (X : Matrix ι ι ℂ) (hX : X.IsHermitian) :
    Matrix.trace (Xᴴ * genTransported K X)
      = Matrix.trace ((star (hK.eigenvectorUnitary : Matrix ι ι ℂ)
          * X * (hK.eigenvectorUnitary : Matrix ι ι ℂ))ᴴ
        * genTransported
          (Matrix.diagonal (fun i => ((hK.eigenvalues i : ℂ))))
          (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * X
            * (hK.eigenvectorUnitary : Matrix ι ι ℂ))) := by
  set U : Matrix ι ι ℂ := (hK.eigenvectorUnitary : Matrix ι ι ℂ)
    with hUdef
  set Y : Matrix ι ι ℂ := star U * X * U with hYdef
  set Λ : Matrix ι ι ℂ :=
    Matrix.diagonal (fun i => ((hK.eigenvalues i : ℂ))) with hΛdef
  set G : Matrix ι ι ℂ := genTransported Λ Y with hGdef
  have hU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hXform : X = U * Y * star U :=
    (conj_star_collapse _ _ hU hU').symm
  have hGconj : U * G * star U = genTransported K X :=
    genTransported_conj hK X
  have hY : Y.IsHermitian := by
    show (star U * X * U)ᴴ = star U * X * U
    simp only [Matrix.conjTranspose_mul, hX.eq,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  calc Matrix.trace (Xᴴ * genTransported K X)
      = Matrix.trace (X * genTransported K X) := by
        rw [show Xᴴ = X from hX]
    _ = Matrix.trace ((U * Y * star U) * (U * G * star U)) := by
        rw [← hGconj, hXform]
    _ = Matrix.trace (U * (Y * G) * star U) := by
        rw [conj_mul_conj _ _ _ hU]
    _ = Matrix.trace (Y * G) := by
        rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
    _ = Matrix.trace (Yᴴ * G) := by
        rw [show Yᴴ = Y from hY]

/-- **Dissipativity at the general seat** (Tier T1 — proved):
    for PSD Hermitian `K` — the load-bearing scope hypothesis,
    stated exactly — and Hermitian `X`, the transported
    generator is dissipative in trace form:
    `(trace (Xᴴ * genTransported K X)).re ≤ 0`.
    This is VISC-1's dissipativity (C5) transported to the
    general Hermitian seat: the numerical-range one-sign
    statement, in the trace form the corpus owns. Together
    with `stepGen_eigenbasis` and
    `stepGen_multiplier_mem_Ioc`, this is where the line earns
    its name: "viscosity" is Jeff's T5 gloss for exactly this
    one-signed dissipation of the owned step, fenced as a
    gloss — no claim beyond the finite Hermitian PSD scope
    above is made or implied. -/
theorem genTransported_dissipative {K : Matrix ι ι ℂ}
    (hK : K.IsHermitian) (hKpos : K.PosSemidef)
    (X : Matrix ι ι ℂ) (hX : X.IsHermitian) :
    (Matrix.trace (Xᴴ * genTransported K X)).re ≤ 0 := by
  rw [trace_genTransported_conj hK X hX]
  exact genTransported_diagonal_dissipative hK.eigenvalues
    (fun i => Matrix.PosSemidef.eigenvalues_nonneg hKpos i) _

end Dissipativity

end ThetLogos
