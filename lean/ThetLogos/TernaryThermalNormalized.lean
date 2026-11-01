import ThetLogos.TernaryThermalDynamics

/-!
# ThetLogos.TernaryThermalNormalized — the normalized ternary step (TTK-2)

Brick 2 of the Ternary Thermal Kernel dynamics line (scoping memo
2026-10-27, §3 "Brick 2", unparked by Jeff 2026-11-01). TTK-1
(`TernaryThermalDynamics`) landed the raw kernel-sandwich step
`ternaryStep lam t X = K_t * Xᴴ * K_t` and proved that it contracts
the trace of a diagonal state: `w i ↦ exp (−2t·lam i) * w i`, with
trace `∑ i, exp (−2t·lam i) * w i ≤ 1`. This brick builds the
trace-restoring (normalized) step on top of it, characterizes its
diagonal fixed points exactly, proves the generator theorem for the
raw step, and quantifies — against the landed KMS identity
`kms_identity_diagonal` — how the normalized step fails the
stationarity that the modular flow owns.

What is proved, in owned vocabulary only:

- `ternaryStepNorm` (T2): the normalized step,
  `(trace (ternaryStep lam t X))⁻¹ • ternaryStep lam t X`. On a
  diagonal state it is again a diagonal state, with weights
  `w i ↦ Z⁻¹ * exp (−2t·lam i) * w i` where
  `Z = ∑ j, exp (−2t·lam j) * w j` is the (real) stepped trace; for
  a state (`w ≥ 0`, `∑ w = 1`) that `Z` is positive, the normalized
  weights are again a state, and the normalized trace is exactly 1.
- **The fixed-point theorem** (T1): for `t > 0` and a diagonal
  state, `ternaryStepNorm lam t (diagState w) = diagState w` iff
  the support of `w` lies inside a single `lam`-level:
  `∃ L, ∀ i, w i = 0 ∨ lam i = L`. Both directions. (Contrast
  TTK-1's raw step, whose fixed diagonal states are exactly the
  ground-line states `lam i = 0` on the support: normalization
  trades "ground line" for "single level".)
- **The generator theorem** (T1): the raw step differentiates at
  `0`. For general `X` the derivative the computation returns is
  the Lyapunov form at the conjugated argument,
  `-(Λ Xᴴ + Xᴴ Λ)` — the step's own definition conjugates its
  middle argument (`ternaryStep_zero`: at `t = 0` the step is
  `X ↦ Xᴴ`), so the literal form `-(Λ X + X Λ)` holds exactly on
  the Hermitian seat, and in particular for diagonal states, which
  is the form this brick was charged with. `Λ = rateMatrix lam` is
  the diagonal rate matrix.
- **The KMS-failure quantification** (T1): at a thermal clock's
  state (faithful weights, full support), the normalized step is
  fixed iff `lam` is constant; whenever two distinct `lam`-levels
  are present the normalized step moves the clock state — while
  the same state's KMS identity under its modular flow holds
  unconditionally (`kms_identity_diagonal`, restated in the same
  theorem). The ternary step is not the modular flow, and this is
  the exact size of the failure: one level versus two.

## Fences (what this module does NOT claim)

- Finite level, diagonal seat for the fixed-point and KMS
  statements. The generator theorem is stated for all `X` in the
  conjugated form the step forces, and in the literal Lyapunov
  form on the Hermitian seat.
- Definedness, honestly: `ternaryStepNorm` is defined for every
  `X` by Lean's convention `0⁻¹ = 0`; the fixed-point theorem is
  stated for states, where the stepped trace is positive, so no
  junk case enters any claim.
- `t` is the owned modular/thermal parameter of `heatKernel`; no
  physical time, no continuum kernel, no new physics is imported.
  "Dynamics" means exactly these maps.
- NO CLAIM on any Millennium statement. Dials 0/4 before and
  after, unchanged by construction.

Tier map:
- T2 (definitions): `ternaryStepNorm`, `rateMatrix`.
- T1 (proved): everything else.
-/

open Matrix Finset

namespace ThetLogos

variable {N : ℕ}

/-- **The rate matrix** (Tier T2): `Λ = diagonal (lam i : ℂ)`, the
    complex diagonal matrix of rates whose exponential schedule is
    `heatKernelC lam t`. It is the `Λ` of the generator theorem. -/
noncomputable def rateMatrix (lam : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun i => (lam i : ℂ))

/-- **The normalized ternary step** (Tier T2): the trace-restoring
    form of TTK-1's raw step,
    `ternaryStepNorm lam t X
      = (trace (ternaryStep lam t X))⁻¹ • ternaryStep lam t X`.
    The scalar is the inverse of the stepped trace; where that
    trace is `0` the scalar is `0⁻¹ = 0` in Lean's convention —
    the theorems below are stated where the trace is positive
    (states), so the convention never enters a claim. -/
noncomputable def ternaryStepNorm (lam : Fin N → ℝ) (t : ℝ)
    (X : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (Matrix.trace (ternaryStep lam t X))⁻¹ • ternaryStep lam t X

/-- A state has a positively weighted mode (Tier T1 — proved):
    nonnegative weights summing to `1` cannot all vanish. -/
theorem state_exists_pos_weight (w : Fin N → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    ∃ i, 0 < w i := by
  by_contra h
  push_neg at h
  have hz : ∀ i, w i = 0 := fun i => le_antisymm (h i) (hw i)
  simp [hz] at hsum

/-- **The stepped trace of a state is positive** (Tier T1 —
    proved): for a state `w`, the normalizing sum
    `∑ i, exp (−2t·lam i) * w i` is strictly positive — every
    schedule factor is positive and some mode carries weight.
    This is the definedness fact the fixed-point theorem uses:
    at a state, the normalized step never divides by zero. -/
theorem ternaryStepNorm_sum_pos (lam : Fin N → ℝ) (t : ℝ)
    (w : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    0 < ∑ i, Real.exp (-2 * t * lam i) * w i := by
  obtain ⟨i0, hi0⟩ := state_exists_pos_weight w hw hsum
  exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) hi0)
    (Finset.single_le_sum
      (fun i _ => mul_nonneg (Real.exp_pos _).le (hw i))
      (Finset.mem_univ i0))

/-- **Diagonal form of the normalized step** (Tier T1 — proved):
    a diagonal state stays diagonal, with weights
    `w i ↦ Z⁻¹ * (exp (−2t·lam i) * w i)`, where
    `Z = ∑ j, exp (−2t·lam j) * w j` is the stepped trace in real
    form. Unconditional: at `Z = 0` both sides read `0⁻¹ = 0`. -/
theorem ternaryStepNorm_diagState (lam : Fin N → ℝ) (t : ℝ)
    (w : Fin N → ℝ) :
    ternaryStepNorm lam t (diagState w)
      = diagState (fun i => (∑ j, Real.exp (-2 * t * lam j) * w j)⁻¹
          * (Real.exp (-2 * t * lam i) * w i)) := by
  have htrace : Matrix.trace (ternaryStep lam t (diagState w))
      = ((∑ i, Real.exp (-2 * t * lam i) * w i : ℝ) : ℂ) := by
    rw [ternaryStep_trace, ← Complex.ofReal_sum]
  unfold ternaryStepNorm
  rw [htrace, ternaryStep_diag]
  ext i j
  by_cases h : i = j
  · subst h
    simp only [Matrix.smul_apply, smul_eq_mul, diagState,
      Matrix.diagonal_apply_eq]
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
  · simp only [Matrix.smul_apply, smul_eq_mul, diagState,
      Matrix.diagonal_apply, if_neg h, mul_zero]

/-- The normalized weights sum to one whenever the normalizing
    sum is nonzero (Tier T1 — proved):
    `∑ i, Z⁻¹ * (exp (−2t·lam i) * w i) = 1`. -/
theorem ternaryStepNorm_weights_sum_eq_one (lam : Fin N → ℝ)
    (t : ℝ) (w : Fin N → ℝ)
    (hZ : (∑ i, Real.exp (-2 * t * lam i) * w i) ≠ 0) :
    ∑ i, (∑ j, Real.exp (-2 * t * lam j) * w j)⁻¹
        * (Real.exp (-2 * t * lam i) * w i) = 1 := by
  rw [← Finset.mul_sum, inv_mul_cancel₀ hZ]

/-- **The normalized step has trace exactly one on states**
    (Tier T1 — proved): normalization does what it says — for a
    state `w`, `trace (ternaryStepNorm lam t (diagState w)) = 1`,
    where TTK-1's raw step only had trace `≤ 1`. -/
theorem ternaryStepNorm_trace_eq_one_of_state (lam : Fin N → ℝ)
    (t : ℝ) (w : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    Matrix.trace (ternaryStepNorm lam t (diagState w)) = 1 := by
  have hZ : (∑ i, Real.exp (-2 * t * lam i) * w i) ≠ 0 :=
    (ternaryStepNorm_sum_pos lam t w hw hsum).ne'
  rw [ternaryStepNorm_diagState]
  simp only [diagState, Matrix.trace_diagonal]
  rw [← Complex.ofReal_sum,
    ternaryStepNorm_weights_sum_eq_one lam t w hZ]
  exact Complex.ofReal_one

/-- **The normalized step carries states to states** (Tier T1 —
    proved): for a state `w`, the normalized weights are
    nonnegative and sum to one — the normalized step is a genuine
    state dynamics where the raw step was only a contraction. -/
theorem ternaryStepNorm_diagState_isState (lam : Fin N → ℝ)
    (t : ℝ) (w : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    (∀ i, 0 ≤ (∑ j, Real.exp (-2 * t * lam j) * w j)⁻¹
        * (Real.exp (-2 * t * lam i) * w i))
      ∧ ∑ i, (∑ j, Real.exp (-2 * t * lam j) * w j)⁻¹
          * (Real.exp (-2 * t * lam i) * w i) = 1 := by
  have hZpos : 0 < ∑ i, Real.exp (-2 * t * lam i) * w i :=
    ternaryStepNorm_sum_pos lam t w hw hsum
  refine ⟨fun i => mul_nonneg (inv_nonneg.mpr hZpos.le)
    (mul_nonneg (Real.exp_pos _).le (hw i)),
    ternaryStepNorm_weights_sum_eq_one lam t w hZpos.ne'⟩

/-- **THE FIXED-POINT THEOREM** (Tier T1 — proved): for `t > 0`, a
    diagonal state is fixed by the normalized step iff its support
    lies inside a single `lam`-level:
    `ternaryStepNorm lam t (diagState w) = diagState w
      ↔ ∃ L, ∀ i, w i = 0 ∨ lam i = L`.
    Mechanism: mode `i` is scaled by `exp (−2t·lam i) / Z`; fixed
    iff that factor is `1` at every occupied mode, iff the factor
    — hence, `exp` being injective and `t > 0`, the rate itself —
    is constant on the support. Both directions are proved. -/
theorem ternaryStepNorm_fixed_diag_iff (lam : Fin N → ℝ) {t : ℝ}
    (ht : 0 < t) (w : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    ternaryStepNorm lam t (diagState w) = diagState w
      ↔ ∃ L, ∀ i, w i = 0 ∨ lam i = L := by
  set Z : ℝ := ∑ j, Real.exp (-2 * t * lam j) * w j with hZdef
  have hZpos : 0 < Z := ternaryStepNorm_sum_pos lam t w hw hsum
  have hZne : Z ≠ 0 := hZpos.ne'
  rw [ternaryStepNorm_diagState]
  show diagState (fun i => Z⁻¹ * (Real.exp (-2 * t * lam i) * w i))
      = diagState w ↔ _
  constructor
  · intro h
    have hentry : ∀ i, Z⁻¹ * (Real.exp (-2 * t * lam i) * w i)
        = w i := by
      intro i
      have hi := congrArg
        (fun M : Matrix (Fin N) (Fin N) ℂ => M i i) h
      simp only [diagState, Matrix.diagonal_apply_eq] at hi
      exact Complex.ofReal_inj.mp hi
    obtain ⟨i0, hi0⟩ := state_exists_pos_weight w hw hsum
    have key : ∀ k, w k ≠ 0 → Real.exp (-2 * t * lam k) = Z := by
      intro k hk
      have hk1 : Z⁻¹ * Real.exp (-2 * t * lam k) = 1 := by
        apply mul_right_cancel₀ hk
        calc (Z⁻¹ * Real.exp (-2 * t * lam k)) * w k
            = Z⁻¹ * (Real.exp (-2 * t * lam k) * w k) := by ring
          _ = w k := hentry k
          _ = 1 * w k := (one_mul _).symm
      calc Real.exp (-2 * t * lam k)
          = Z * (Z⁻¹ * Real.exp (-2 * t * lam k)) := by
            rw [← mul_assoc, mul_inv_cancel₀ hZne, one_mul]
        _ = Z := by rw [hk1, mul_one]
    refine ⟨lam i0, fun i => ?_⟩
    by_cases hwi : w i = 0
    · exact Or.inl hwi
    · refine Or.inr ?_
      have hexp : Real.exp (-2 * t * lam i)
          = Real.exp (-2 * t * lam i0) := by
        rw [key i hwi, key i0 hi0.ne']
      have harg := Real.exp_injective hexp
      have hcoef : (-2 * t : ℝ) ≠ 0 :=
        mul_ne_zero (by norm_num) ht.ne'
      exact mul_left_cancel₀ hcoef harg
  · rintro ⟨L, hL⟩
    have hZeq : Z = Real.exp (-2 * t * L) := by
      calc Z = ∑ i, Real.exp (-2 * t * L) * w i := by
            rw [hZdef]
            apply Finset.sum_congr rfl
            intro i _
            rcases hL i with hw0 | hl
            · simp [hw0]
            · rw [hl]
        _ = Real.exp (-2 * t * L) * ∑ i, w i := by
            rw [← Finset.mul_sum]
        _ = Real.exp (-2 * t * L) := by rw [hsum, mul_one]
    congr 1
    funext i
    rcases hL i with hw0 | hl
    · simp [hw0]
    · have he : Real.exp (-2 * t * lam i)
          = Real.exp (-2 * t * L) := by rw [hl]
      rw [hZeq, he, ← mul_assoc,
        inv_mul_cancel₀ (Real.exp_pos _).ne', one_mul]

/-- **The generator on a diagonal state, closed form** (Tier T1 —
    proved): `-(Λ ρ + ρ Λ)` for a diagonal state `ρ = diagState w`
    is the diagonal state with weights `-2 * lam i * w i` — the
    `i = j` case of the `-(λᵢ + λⱼ)` generator spectrum. -/
theorem rateMatrix_generator_diagState (lam : Fin N → ℝ)
    (w : Fin N → ℝ) :
    -(rateMatrix lam * diagState w + diagState w * rateMatrix lam)
      = diagState (fun i => -2 * lam i * w i) := by
  ext a b
  by_cases h : a = b
  · subst h
    simp only [Matrix.neg_apply, Matrix.add_apply, rateMatrix,
      Matrix.mul_diagonal, diagState, Matrix.diagonal_apply_eq]
    push_cast
    ring
  · simp only [Matrix.neg_apply, Matrix.add_apply, rateMatrix,
      Matrix.mul_diagonal, diagState, Matrix.diagonal_apply,
      if_neg h, zero_mul, add_zero, neg_zero]

/-- **Entry form of the ternary step** (Tier T1 — proved):
    `(ternaryStep lam t X) i j
      = exp (−t·lam i) * Xᴴ i j * exp (−t·lam j)` — the sandwich,
    entrywise; the middle argument appears conjugated, as the
    ternary operation dictates. -/
theorem ternaryStep_apply_ttk2 (lam : Fin N → ℝ) (t : ℝ)
    (X : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    (ternaryStep lam t X) i j
      = (Real.exp (-t * lam i) : ℂ) * Xᴴ i j
        * (Real.exp (-t * lam j) : ℂ) := by
  show (heatKernelC lam t * Xᴴ * heatKernelC lam t) i j = _
  unfold heatKernelC
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- **THE GENERATOR THEOREM, general form** (Tier T1 — proved):
    for ALL `X`, the ternary step differentiates at `0` to the
    Lyapunov form at the conjugated argument:
    `HasDerivAt (fun t => ternaryStep lam t X) (-(Λ Xᴴ + Xᴴ Λ)) 0`.
    The `Xᴴ` is not a defect: the step conjugates its middle
    argument by definition (`ternaryStep_zero`), so this is the
    derivative the entrywise computation returns — each entry is
    `exp (−t·λᵢ) · (Xᴴ)ᵢⱼ · exp (−t·λⱼ)`, whose scalar derivative
    at `0` is `-(λᵢ + λⱼ) · (Xᴴ)ᵢⱼ`. The literal `-(Λ X + X Λ)`
    form is the Hermitian corollary below. -/
theorem ternaryStep_hasDerivAt_zero (lam : Fin N → ℝ)
    (X : Matrix (Fin N) (Fin N) ℂ) :
    HasDerivAt (fun t => ternaryStep lam t X)
      (-(rateMatrix lam * Xᴴ + Xᴴ * rateMatrix lam)) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hfun : (fun t => (ternaryStep lam t X) i j)
      = (fun t => (Real.exp (-(lam i + lam j) * t) : ℂ)
          * Xᴴ i j) := by
    funext t
    rw [ternaryStep_apply_ttk2]
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
  simp only [rateMatrix, Matrix.neg_apply, Matrix.add_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  push_cast
  ring

/-- **The generator theorem in the charged form, diagonal seat**
    (Tier T1 — proved): for a diagonal state,
    `HasDerivAt (fun t => ternaryStep lam t (diagState w))
      (-(Λ (diagState w) + (diagState w) Λ)) 0` — the pack's
    literal statement, since a diagonal state is Hermitian
    (`diagState_conjTranspose`, TTK-1). Its closed form is
    `rateMatrix_generator_diagState`. -/
theorem ternaryStep_hasDerivAt_zero_diag (lam : Fin N → ℝ)
    (w : Fin N → ℝ) :
    HasDerivAt (fun t => ternaryStep lam t (diagState w))
      (-(rateMatrix lam * diagState w
        + diagState w * rateMatrix lam)) 0 := by
  have h := ternaryStep_hasDerivAt_zero lam (diagState w)
  rwa [diagState_conjTranspose] at h

/-- **The generator theorem in the charged form, Hermitian seat**
    (Tier T1 — proved): for Hermitian `X`,
    `HasDerivAt (fun t => ternaryStep lam t X) (-(Λ X + X Λ)) 0`
    — the literal Lyapunov form, valid exactly where `Xᴴ = X`. -/
theorem ternaryStep_hasDerivAt_zero_hermitian (lam : Fin N → ℝ)
    (X : Matrix (Fin N) (Fin N) ℂ) (hX : X.IsHermitian) :
    HasDerivAt (fun t => ternaryStep lam t X)
      (-(rateMatrix lam * X + X * rateMatrix lam)) 0 := by
  have h := ternaryStep_hasDerivAt_zero lam X
  rwa [show Xᴴ = X from hX] at h

/-- **The clock state under the normalized step** (Tier T1 —
    proved): a thermal clock's state has full support (faithful
    weights), so the single-level condition collapses to constancy
    of `lam` itself: for `t > 0`,
    `ternaryStepNorm lam t (diagState C.weights)
        = diagState C.weights`
    iff `lam` is constant — `∃ L, ∀ i, lam i = L`. -/
theorem ternaryStepNorm_clock_fixed_iff (C : ThermalClock N)
    (lam : Fin N → ℝ) {t : ℝ} (ht : 0 < t) :
    ternaryStepNorm lam t (diagState C.weights)
        = diagState C.weights
      ↔ ∃ L, ∀ i, lam i = L := by
  rw [ternaryStepNorm_fixed_diag_iff lam ht C.weights
    (fun i => (C.faithful i).le) C.normalized]
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L, fun i => ?_⟩
    rcases hL i with h0 | hl
    · exact absurd h0 (C.faithful i).ne'
    · exact hl
  · rintro ⟨L, hL⟩
    exact ⟨L, fun i => Or.inr (hL i)⟩

/-- **The normalized step moves the clock state across two
    levels** (Tier T1 — proved): if `lam` takes two distinct
    values, then for `t > 0` the clock state is NOT fixed by the
    normalized step — the dissipative step cannot hold a faithful
    state spread over two rates, however it is normalized. -/
theorem ternaryStepNorm_clock_not_fixed (C : ThermalClock N)
    (lam : Fin N → ℝ) {t : ℝ} (ht : 0 < t)
    (h : ∃ i j, lam i ≠ lam j) :
    ternaryStepNorm lam t (diagState C.weights)
      ≠ diagState C.weights := by
  intro hfixed
  obtain ⟨L, hL⟩ :=
    (ternaryStepNorm_clock_fixed_iff C lam ht).mp hfixed
  obtain ⟨i, j, hij⟩ := h
  exact hij ((hL i).trans (hL j).symm)

/-- **THE KMS CONTRAST** (Tier T1 — proved): the same clock state
    that satisfies the KMS identity under its own modular flow —
    `kms_identity_diagonal`, the Gibbs state's stationarity,
    holding for every pair of observables `A B` with no condition
    on any rate function — is moved by the normalized ternary
    step whenever `lam` takes two distinct values. One theorem,
    both halves: modular stationarity is unconditional; ternary
    stationarity fails exactly at the second level. Any claim
    that the ternary step "is" the modular flow dies here, at the
    clock state itself. -/
theorem kms_identity_and_ternaryStepNorm_moves_clock
    (C : ThermalClock N) (lam : Fin N → ℝ) {t : ℝ} (ht : 0 < t)
    (h : ∃ i j, lam i ≠ lam j) (A B : Matrix (Fin N) (Fin N) ℂ) :
    (Matrix.trace (diagState C.weights * A
        * (NormedSpace.exp (-diagModularK C.weights) * B
          * NormedSpace.exp (diagModularK C.weights)))
      = Matrix.trace (diagState C.weights * B * A))
      ∧ ternaryStepNorm lam t (diagState C.weights)
          ≠ diagState C.weights :=
  ⟨kms_identity_diagonal C.weights C.faithful C.normalized A B,
    ternaryStepNorm_clock_not_fixed C lam ht h⟩

end ThetLogos
