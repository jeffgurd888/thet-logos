import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import ThetLogos.ResonanceSpectrum

open Matrix Finset MeasureTheory

namespace ThetLogos

/-!
# ThetLogos.ThermalKernel — the heat kernel of a thermal clock, amortized (Tiers T1/T2)

Origin (Jeff, 2026-10-18): "restart with an amortization of a thermal
spectral kernel of time." The reading (pinned in the dossier,
`whitepaper/thermal-kernel-2026-10-18.md`): the heat kernel of a
clock's generator `K = −ln ρ`, read as a portfolio of **amortization
schedules** — one exponential schedule `exp(−t·λᵢ)` per eigenmode.
Each mode pays on its own timescale `1/λᵢ`: fast modes pay early and
finish, slow modes pay late and linger. This module proves the
finite-level content of that reading:

- the kernel itself and its **spectral expansion** (entry form);
- the **semigroup law** — schedules compose: the kernel at `t + s`
  is the kernel at `t` times the kernel at `s`;
- the **trace schedule**: the trace is the sum of the schedules,
  and at `t = 0` it is the dimension;
- the **payoff integral**: each positive mode's schedule, run to the
  end of time, pays exactly `(λᵢ)⁻¹` — and the summed payoff over
  the positive modes is the sum of the reciprocals;
- the **jewel**: at `t = 1`, the heat kernel of a thermal clock's
  `K = −ln ρ` *is* the state's own diagonal density matrix,
  `e^{−K} = ρ` — the state is its own heat kernel at unit time.

## Fences (what this module does NOT claim)

- Finite level, **diagonal-generator case only**. A general
  Hermitian generator reduces to the diagonal case in its
  eigenbasis, but that reduction is NOT formalized here — it is the
  named remainder now shared by `ResonanceSpectrum`,
  `SpectralClock`, and this module.
- "Amortization" is Jeff's metaphor. The theorems are the
  exponential schedules, the semigroup law, and the payoff
  integrals — nothing financial is claimed or used.
- `t` is the modular/thermal parameter. It becomes physical time
  only through `ThermalClock`'s β for Gibbs states
  (`gibbs_conversion`: physical time = β × thermal time).
- The trace here is a finite sum over modes. No continuum heat
  kernel, no Seeley–DeWitt asymptotic expansion, no spectral
  action is claimed.

Tier map:
- T2 (definitions): `heatKernel`.
- T1 (proved): everything else — the spectral expansion, the
  semigroup law, the trace schedule, the payoff integrals, the
  `t = 1` jewel, and the Gibbs instance.
-/

-- ============================================================================
-- §1. The kernel and its spectral expansion
-- ============================================================================

section Diagonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The diagonal heat kernel** of a generator with eigenvalue
    function `lam`, at thermal time `t`: the diagonal matrix whose
    `i`-th entry is the `i`-th mode's exponential schedule
    `exp(−t·lam i)`. The kernel is the sum of the schedules running
    at once, one per eigenmode. Tier T2. -/
noncomputable def heatKernel (lam : ι → ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => Real.exp (-t * lam i))

/-- Diagonal entry of the kernel (Tier T1 — proved): the `i`-th
    mode's schedule at time `t` is `exp(−t·lam i)`. -/
theorem heatKernel_apply_diag (lam : ι → ℝ) (t : ℝ) (i : ι) :
    heatKernel lam t i i = Real.exp (-t * lam i) := by
  simp [heatKernel, Matrix.diagonal_apply_eq]

/-- Off-diagonal entries of the kernel vanish (Tier T1 — proved):
    the schedules do not mix modes. -/
theorem heatKernel_apply_off (lam : ι → ℝ) (t : ℝ) {i j : ι}
    (h : i ≠ j) : heatKernel lam t i j = 0 := by
  simp [heatKernel, Matrix.diagonal_apply, h]

/-- **Spectral expansion, entry form** (Tier T1 — proved): the
    kernel is the diagonal matrix of mode schedules,
    `(heatKernel lam t) i j = if i = j then exp(−t·lam i) else 0`. -/
theorem heatKernel_apply (lam : ι → ℝ) (t : ℝ) (i j : ι) :
    heatKernel lam t i j
      = if i = j then Real.exp (-t * lam i) else 0 := by
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, heatKernel_apply_diag]
  · rw [if_neg h, heatKernel_apply_off _ _ h]

/-- The kernel at time zero is the identity (Tier T1 — proved):
    no time has passed, no mode has paid anything. -/
theorem heatKernel_zero (lam : ι → ℝ) : heatKernel lam 0 = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [heatKernel_apply]
  · simp [heatKernel_apply, h]

/-- **The semigroup law — schedules compose** (Tier T1 — proved):
    the kernel at `t + s` is the kernel at `t` times the kernel at
    `s`. A payment plan that agrees with itself at every split:
    running the schedules for `t` and then `s` more is running them
    for `t + s`. -/
theorem heatKernel_add (lam : ι → ℝ) (t s : ℝ) :
    heatKernel lam (t + s) = heatKernel lam t * heatKernel lam s := by
  unfold heatKernel
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp only [Pi.mul_apply, ← Real.exp_add]
  congr 1
  ring

-- ============================================================================
-- §2. The trace schedule
-- ============================================================================

/-- **The trace schedule** (Tier T1 — proved): the trace of the
    kernel is the sum of the mode schedules — the total still owed
    across all modes at time `t`. -/
theorem heatKernel_trace (lam : ι → ℝ) (t : ℝ) :
    Matrix.trace (heatKernel lam t) = ∑ i, Real.exp (-t * lam i) := by
  rw [heatKernel, Matrix.trace_diagonal]

/-- The trace at time zero is the dimension (Tier T1 — proved):
    at `t = 0` every schedule stands at its full value 1, and the
    total is the number of modes. -/
theorem heatKernel_trace_zero (lam : ι → ℝ) :
    Matrix.trace (heatKernel lam 0) = (Fintype.card ι : ℝ) := by
  rw [heatKernel_trace]
  simp

end Diagonal

-- ============================================================================
-- §3. The payoff integral: each mode's total payment
-- ============================================================================

section Payoff

variable {ι : Type*} [Fintype ι]

/-- Each positive mode is integrable on the half-line (Tier T1 —
    proved): the schedule `exp(−t·lam i)` with `lam i > 0` decays,
    so its total payment is finite. Transport of Mathlib's
    `integrableOn_exp_mul_Ioi` at rate `−lam i < 0`. -/
theorem integrableOn_exp_neg_mul_Ioi {lam : ι → ℝ} (i : ι)
    (hi : 0 < lam i) :
    IntegrableOn (fun t : ℝ => Real.exp (-t * lam i)) (Set.Ioi 0)
      MeasureTheory.volume := by
  have hfun : (fun t : ℝ => Real.exp (-t * lam i))
      = fun t : ℝ => Real.exp ((-lam i) * t) := by
    funext t
    congr 1
    ring
  rw [hfun]
  exact integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hi) (0 : ℝ)

/-- **The payoff integral, mode-wise** (Tier T1 — proved): a
    positive mode's schedule, run to the end of time, pays exactly
    the reciprocal of its rate,
    `∫₀^∞ exp(−t·λᵢ) dt = (λᵢ)⁻¹`. The mode's total payment is its
    timescale. -/
theorem integral_exp_neg_mul_Ioi {lam : ι → ℝ} (i : ι) (hi : 0 < lam i) :
    ∫ t : ℝ in Set.Ioi 0, Real.exp (-t * lam i) = (lam i)⁻¹ := by
  have hfun : (fun t : ℝ => Real.exp (-t * lam i))
      = fun t : ℝ => Real.exp ((-lam i) * t) := by
    funext t
    congr 1
    ring
  rw [hfun, integral_exp_mul_Ioi (neg_lt_zero.mpr hi) (0 : ℝ)]
  rw [mul_zero, Real.exp_zero]
  field_simp

/-- **The payoff integral, summed form** (Tier T1 — proved): the
    total payment of all positive modes together is the sum of
    their reciprocals — the integral of the finite sum of schedules
    over the positive modes is the sum of the mode payoffs. -/
theorem integral_sum_exp_neg_mul_Ioi (lam : ι → ℝ) :
    ∫ t : ℝ in Set.Ioi 0,
        ∑ i ∈ Finset.univ.filter (fun i => 0 < lam i), Real.exp (-t * lam i)
      = ∑ i ∈ Finset.univ.filter (fun i => 0 < lam i), (lam i)⁻¹ := by
  rw [integral_finset_sum]
  · exact Finset.sum_congr rfl fun i hi =>
      integral_exp_neg_mul_Ioi i ((Finset.mem_filter.mp hi).2)
  · intro i hi
    exact integrableOn_exp_neg_mul_Ioi i ((Finset.mem_filter.mp hi).2)

end Payoff

-- ============================================================================
-- §4. The jewel: at t = 1 the kernel of K = −ln ρ IS the state
-- ============================================================================

section Jewel

/-- **THE JEWEL** (Tier T1 — proved): the heat kernel of a thermal
    clock's generator `K = −ln ρ` at unit time is the state's own
    diagonal density matrix:
    `heatKernel (fun j => −log (weights j)) 1 = Matrix.diagonal weights`,
    i.e. `e^{−K} = ρ`. The state is its own heat kernel at unit
    time — every mode's schedule at `t = 1` has paid exactly down
    to its weight, since `exp(−1·(−log w)) = exp (log w) = w` by
    faithfulness (`0 < w`). -/
theorem thermalClock_heatKernel_one {N : ℕ} (C : ThermalClock N) :
    heatKernel (fun j => -Real.log (C.weights j)) 1
      = Matrix.diagonal C.weights := by
  ext i j
  by_cases h : i = j
  · subst h
    rw [heatKernel_apply_diag, Matrix.diagonal_apply_eq]
    simp [Real.exp_log (C.faithful i)]
  · simp [heatKernel_apply_off _ _ h, Matrix.diagonal_apply, h]

/-- The jewel in trace form (Tier T1 — proved): the trace of the
    clock's kernel at `t = 1` is 1 — the state is normalized, read
    off the kernel: `∑ j, exp(−(−log wⱼ)) = ∑ j, wⱼ = 1`. -/
theorem thermalClock_heatKernel_one_trace {N : ℕ} (C : ThermalClock N) :
    Matrix.trace (heatKernel (fun j => -Real.log (C.weights j)) 1) = 1 := by
  rw [thermalClock_heatKernel_one, Matrix.trace_diagonal]
  exact C.normalized

end Jewel

-- ============================================================================
-- §5. The Gibbs instance
-- ============================================================================

section Gibbs

/-- **The Gibbs instance** (Tier T1 — proved): the diagonal matrix
    of Gibbs weights at inverse temperature `β` over a Dirac
    operator with eigenvalues `lam` is the scalar `exp(−logZ)`
    times the heat kernel of the laboratory generator `D²` at time
    `β`: `diag (gibbsDiagWeights β lam logZ) = exp(−logZ) • heatKernel (fun j => (lam j)^2) β`.
    Entry-wise this is the definition of the Gibbs weights:
    `exp(−(βλ² + logZ)) = exp(−logZ)·exp(−βλ²)`. The Gibbs state is
    the heat kernel of `D²` at thermal time `β`, up to the
    partition-function scalar — the same scalar the clock cannot
    see (`diagFlow_gibbs_logZ_independent`). -/
theorem gibbsWeights_eq_smul_heatKernel {N : ℕ} (β : ℝ) (lam : Fin N → ℝ)
    (logZ : ℝ) :
    Matrix.diagonal (gibbsDiagWeights β lam logZ)
      = Real.exp (-logZ) • heatKernel (fun j => (lam j) ^ 2) β := by
  ext i j
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.smul_apply, heatKernel_apply_diag,
      smul_eq_mul]
    simp only [gibbsDiagWeights, modularEigenvalue]
    rw [← Real.exp_add]
    congr 1
    ring
  · simp [Matrix.diagonal_apply, h, heatKernel_apply_off _ _ h]

end Gibbs

end ThetLogos
