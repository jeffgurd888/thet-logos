import ThetLogos.SpectralActionFinite

/-!
# ThetLogos.SpectralActionBridge — finite spectral action + finite index theory (T1)

**Tier T1 (proved). Zero new axioms. Zero sorrys.**

Two bridges from the formalized finite spectral triple to the theories-intake
candidates "spectral action" and "index theory". The FIT TEST is met because
every statement below is a real theorem about the formalized objects
(`smDirac`, `gammaF`, `fluctuatedDirac`): no analogies, no hand-waving.

## Bridge (a): finite spectral action — FIT

For the concrete finite Dirac `D_F = smDirac …` (32×32, self-adjoint,
grading-odd), the spectral action with an even cutoff polynomial
`p(x) = c₀ + c₁x² + c₂x⁴` is the moment expansion
  `Tr(p(D_F/Λ)) = 32·c₀ + c₁Λ⁻²·Tr(D_F²) + c₂Λ⁻⁴·Tr(D_F⁴)`,
proved as `finite_spectral_action_expansion` (finite-dimensional linear
algebra). The machine-checked moments:
- a₀: `Tr₃₂(1) = 32` (`sa_finite_a0`) — the finite trace input to the
  continuum a₀ axiom `SpectralAction.seely_dewitt_a0`.
- a₂: `Tr₃₂(D_F²)` is the explicit Yukawa polynomial
  `4·(|yν|²+|ye|²+3|yu|²+3|yd|²) + 2|yR|²` (`sa_finite_a2_yukawa`, from the
  proved `tr_DF_sq_yukawa`), and with inner fluctuation
  `Tr((D_F^(A))²) = Tr(D_F²) + 2·Tr(D_F(A+A°)) + Tr((A+A°)²)`
  (`sa_finite_a2_fluctuated`, from the proved `tr_fluctuated_sq`).
- Odd moments vanish: `Tr(D^{2k+1}) = 0` for grading-odd D
  (`trace_odd_pow_vanishes`, abstract; `trace_smDirac_odd_vanishes`).

## Bridge (b): index theory — FIT at finite level

For grading-odd self-adjoint D, the chiral compression `D⁺ : H⁺ → H⁻` is
Fredholm in finite dimensions, and rank-nullity gives the elementary index
formula `ind(D⁺) = dim ker D⁺ − dim coker D⁺ = dim H⁺ − dim H⁻`
(`fredholm_index_fin_dim`, abstract). For the concrete triple the grading
`γ_F = diag(+I₈,−I₈,−I₈,+I₈)` gives `dim H⁺ = dim H⁻ = 16`
(`card_chiPlus`, `card_chiMinus`, by decide), hence every chiral
compression has index 0 (`chiral_compression_index_zero`), and the
supertrace vanishes: `Tr(γ_F) = 0` (`trace_gammaF_eq_zero`). This is the
finite-dimensional shadow of Atiyah–Singer: the analytic index is computed
by the supertrace.

## Priced windows (NOT claimed here)

- **a₄ finite moment**: `Tr(D_F⁴)` as a Yukawa polynomial is OPEN (stretch in
  `SpectralActionFinite.lean`: the D²-block infrastructure
  `pow2_buildDirac_blk_*` exists, the fourth-power trace is not finished).
  Finite linear algebra — no continuum needed — but unproved, so the a₄
  term stays a priced window.
- **Full heat-kernel expansion: NO-FIT.** The continuum expansion
  `Tr(e^{−tD_A²}) ~ Σ t^{(n−4)/2} a_n` (axiomatized in
  `SpectralAction.heatKernelExpansion`) needs the continuum/lattice limit:
  a 4-manifold Dirac, elliptic analysis, pseudodifferential calculus.
  None of that is formalized; the axiom stays untouched.
- **Atiyah–Singer on manifolds: NO-FIT (priced window).**
  `ind(D⁺_M) = ∫_M Â ∧ ch` needs elliptic PDE theory on manifolds.
  What IS proved is the finite-level index theorem above.

No physical predictions are claimed: spectral-action coefficients are
properties of the model, not measurements of nature.
-/

namespace ThetLogos

/-! ## Bridge (a): finite spectral action -/

/-! ### a₀ and a₂ moments -/

/-- T1: the finite a₀ moment `Tr₃₂(1) = 32`.
    Finite trace input to the continuum a₀ axiom
    (`SpectralAction.seely_dewitt_a0`); the `(4π)^{-2}` prefactor and the
    manifold volume factor stay T5. -/
theorem sa_finite_a0 : Matrix.trace (1 : Matrix I32 I32 ℂ) = 32 := by
  simp [Matrix.trace_one]

/-- T1: the finite a₂ moment is the Yukawa polynomial (K3).
    Discharges the symbolic `Tr₃₂((D_F)²)` in the continuum a₂ formula
    (`SpectralAction.seely_dewitt_a2_formula`). From `tr_DF_sq_yukawa`. -/
theorem sa_finite_a2_yukawa (yNu yE yU yD yR : ℂ) :
    Matrix.trace ((smDirac yNu yE yU yD yR) ^ 2)
      = ((4 * (Complex.normSq yNu + Complex.normSq yE
            + 3 * Complex.normSq yU + 3 * Complex.normSq yD)
          + 2 * Complex.normSq yR : ℝ) : ℂ) :=
  tr_DF_sq_yukawa _ _ _ _ _

/-- T1: the a₂ moment with inner fluctuation. From `tr_fluctuated_sq`:
    the Higgs/gauge kinetic content of a₂ sits in the A-dependent terms. -/
theorem sa_finite_a2_fluctuated (D_F A : Matrix I32 I32 ℂ) :
    Matrix.trace ((fluctuatedDirac D_F A) ^ 2)
      = Matrix.trace (D_F ^ 2)
        + 2 * Matrix.trace (D_F * (A + oppositeOneForm A))
        + Matrix.trace ((A + oppositeOneForm A) ^ 2) :=
  tr_fluctuated_sq D_F A

/-! ### Odd moments vanish -/

/-- T1 (abstract): odd heat-trace moments vanish for grading-odd D.
    From `γD^m = (−1)^m D^mγ` and cyclicity of the trace:
    `Tr(D^{2k+1}) = Tr(γ(γD^{2k+1})) = Tr((γD^{2k+1})γ) = −Tr(D^{2k+1})`. -/
theorem trace_odd_pow_vanishes {n : Type*} [Fintype n] [DecidableEq n]
    (γ D : Matrix n n ℂ) (hγ : γ * γ = 1) (hodd : γ * D + D * γ = 0) (k : ℕ) :
    Matrix.trace (D ^ (2 * k + 1)) = 0 := by
  have hod : γ * D = -(D * γ) := eq_neg_of_add_eq_zero_left hodd
  have hγD : ∀ m : ℕ, γ * D ^ m = (-1 : ℂ) ^ m • (D ^ m * γ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have e1 : γ * D ^ (m + 1) = (γ * D ^ m) * D := by rw [pow_succ, mul_assoc]
      have e2 : (D ^ m * γ) * D = -(D ^ (m + 1) * γ) := by
        rw [mul_assoc, hod, mul_neg, ← mul_assoc, pow_succ]
      have e3 : (-1 : ℂ) ^ (m + 1) • (D ^ (m + 1) * γ)
          = -((-1 : ℂ) ^ m • (D ^ (m + 1) * γ)) := by
        have hpm : (-1 : ℂ) ^ (m + 1) = -((-1 : ℂ) ^ m) := by
          rw [pow_succ, mul_neg, mul_one]
        rw [hpm, neg_smul]
      rw [e1, ih, smul_mul_assoc, e2, smul_neg, e3]
  have hneg1 : (-1 : ℂ) ^ (2 * k + 1) = -1 := Odd.neg_one_pow ⟨k, rfl⟩
  have hT : Matrix.trace (D ^ (2 * k + 1))
      = -Matrix.trace (D ^ (2 * k + 1)) := by
    have h1 : D ^ (2 * k + 1) = γ * (γ * D ^ (2 * k + 1)) := by
      rw [← mul_assoc, hγ, one_mul]
    conv_lhs => rw [h1, Matrix.trace_mul_comm]
    rw [hγD, hneg1, smul_mul_assoc, Matrix.trace_smul, neg_smul, one_smul,
      mul_assoc, hγ, mul_one]
  have h2 : (2 : ℂ) * Matrix.trace (D ^ (2 * k + 1)) = 0 := by
    linear_combination hT
  rcases mul_eq_zero.mp h2 with h3 | h3
  · norm_num at h3
  · exact h3

/-- T1: odd moments of the concrete finite Dirac vanish.
    Uses grading-oddness (`smDirac_grading_odd`) and `γ_F² = 1`. -/
theorem trace_smDirac_odd_vanishes (yNu yE yU yD yR : ℂ) (k : ℕ) :
    Matrix.trace ((smDirac yNu yE yU yD yR) ^ (2 * k + 1)) = 0 :=
  trace_odd_pow_vanishes gammaF _ gammaF_involutive
    (smDirac_grading_odd _ _ _ _ _) k

/-! ### Moment expansion of the finite spectral action -/

/-- The cutoff polynomial `p(x) = c₀ + c₁x² + c₂x⁴` evaluated on `D/Λ`,
    as a matrix. T1 definition. -/
noncomputable def cutoffPolyMat (D : Matrix I32 I32 ℂ) (c : Fin 3 → ℂ) (Λ : ℂ) :
    Matrix I32 I32 ℂ :=
  (c 0) • (1 : Matrix I32 I32 ℂ) + (c 1 * Λ⁻¹ ^ 2) • D ^ 2
    + (c 2 * Λ⁻¹ ^ 4) • D ^ 4

/-- The finite spectral action as a moment expansion. T1 definition.
    The a₄ moment `Tr(D⁴)` stays symbolic (priced window: open computation). -/
noncomputable def finiteSpectralAction (D : Matrix I32 I32 ℂ) (c : Fin 3 → ℂ)
    (Λ : ℂ) : ℂ :=
  c 0 * 32 + c 1 * Λ⁻¹ ^ 2 * Matrix.trace (D ^ 2)
    + c 2 * Λ⁻¹ ^ 4 * Matrix.trace (D ^ 4)

/-- T1: `Tr(p(D/Λ))` equals the moment expansion — the finite spectral
    action for an even cutoff polynomial. -/
theorem finite_spectral_action_expansion (D : Matrix I32 I32 ℂ) (c : Fin 3 → ℂ)
    (Λ : ℂ) :
    Matrix.trace (cutoffPolyMat D c Λ) = finiteSpectralAction D c Λ := by
  unfold cutoffPolyMat finiteSpectralAction
  rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_one]
  simp only [Fintype.card_fin, smul_eq_mul]
  ring

/-! ## Bridge (b): finite-dimensional index theory -/

/-- T1 (abstract): the elementary finite-dimensional index formula.
    For `f : V →ₗ W` between finite-dimensional spaces,
    `dim ker f − dim coker f = dim V − dim W` (rank-nullity twice).
    In particular the Fredholm index of a chiral compression `D⁺ : H⁺ → H⁻`
    depends only on the grading, not on D — the finite shadow of the
    deformation-invariance in Atiyah–Singer. -/
theorem fredholm_index_fin_dim {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (f : V →ₗ[ℂ] W) :
    (Module.finrank ℂ (LinearMap.ker f) : ℤ)
      - Module.finrank ℂ (W ⧸ LinearMap.range f)
      = (Module.finrank ℂ V : ℤ) - Module.finrank ℂ W := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  omega

/-- The +1 eigenspace index set of `γ_F = diag(+I₈,−I₈,−I₈,+I₈)`:
    indices `[0,8) ∪ [24,32)`. T1 definition. -/
def ChiPlus : Type := {i : Fin 32 // i.val < 8 ∨ 24 ≤ i.val}

/-- The −1 eigenspace index set of `γ_F`: indices `[8,24)`. T1 definition. -/
def ChiMinus : Type := {i : Fin 32 // 8 ≤ i.val ∧ i.val < 24}

instance : Fintype ChiPlus := by unfold ChiPlus; infer_instance
instance : Fintype ChiMinus := by unfold ChiMinus; infer_instance

/-- T1: `dim H⁺ = 16`, by decide. -/
theorem card_chiPlus : Fintype.card ChiPlus = 16 := by decide

/-- T1: `dim H⁻ = 16`, by decide. -/
theorem card_chiMinus : Fintype.card ChiMinus = 16 := by decide

/-- Diagonal entries of `γ_F`. T1 (from the T2 definition in
    `Scaffold32.lean`). -/
theorem gammaF_diag_entry (i : Fin 32) : gammaF i i
    = if i.val < 8 then (1 : ℂ) else if i.val < 16 then -1
      else if i.val < 24 then -1 else 1 := by
  unfold gammaF
  rw [dite_eq_left rfl]

/-- T1: the supertrace vanishes, `Tr(γ_F) = 0`. The finite shadow of the
    Atiyah–Singer principle that the analytic index is computed by the
    supertrace. -/
theorem trace_gammaF_eq_zero : Matrix.trace gammaF = 0 := by
  have hsum : (∑ i : Fin 32,
      (if i.val < 8 then (1 : ℤ) else if i.val < 16 then -1
        else if i.val < 24 then -1 else 1)) = 0 := by
    decide
  have h2 : (∑ i : Fin 32, gammaF i i)
      = ((∑ i : Fin 32,
          (if i.val < 8 then (1 : ℤ) else if i.val < 16 then -1
            else if i.val < 24 then -1 else 1 : ℤ)) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    exact gammaF_diag_entry i
  have h3 : ((∑ i : Fin 32,
      (if i.val < 8 then (1 : ℤ) else if i.val < 16 then -1
        else if i.val < 24 then -1 else 1 : ℤ)) : ℂ) = 0 := by
    exact_mod_cast hsum
  have h1 : Matrix.trace gammaF = ∑ i : Fin 32, gammaF i i := rfl
  rw [h1, h2, h3]

/-- T1: every chiral compression `D⁺ : H⁺ → H⁻` of the concrete triple has
    Fredholm index 0. By `fredholm_index_fin_dim` the index is
    `dim H⁺ − dim H⁻ = 16 − 16`; the actual Dirac compression of `smDirac`
    is such a map because nonzero entries of `buildDirac` connect opposite
    grading eigenspaces (`buildDirac_nonzero_opp_grading`). -/
theorem chiral_compression_index_zero (f : (ChiPlus → ℂ) →ₗ[ℂ] (ChiMinus → ℂ)) :
    (Module.finrank ℂ (LinearMap.ker f) : ℤ)
      - Module.finrank ℂ ((ChiMinus → ℂ) ⧸ LinearMap.range f) = 0 := by
  have h := fredholm_index_fin_dim f
  rw [Module.finrank_pi, Module.finrank_pi, card_chiPlus, card_chiMinus] at h
  omega

end ThetLogos
