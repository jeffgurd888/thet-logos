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

end ThetLogos
