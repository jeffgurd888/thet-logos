import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import ThetLogos.FiniteArrow

open scoped InnerProductSpace

/-!
# ThetLogos.FiniteArrowEntropy — FA-4b: production, entropy form

The contingent brick of the finite arrow line (scoping
`finite-arrow-scoping-2026-11-06.md` §3.1(i-b); pin FA-0,
`FiniteArrowPin.lean`). Working label only — naming is Jeff's.

**K-ARR-POS — decided at this brick's first step: it does NOT
fire.** The positivity lemma the scoping named as the brick's
unlanded obligation is proved here
(`arrowFlow_nonneg`, `arrowFlow_pos_lower`): the heat kernel
is entrywise nonnegative, and a strictly positive field stays
strictly positive with the explicit diagonal lower bound
`(θ t) i ≥ exp (−t · degSum w) · θ i`. The route is the
corpus's own: positivity is proved for one Euler step
(elementary, at the FA-3 stability bound), transported through
the step's iterates, and closed by the spectral limit
`(1 − (t/N) L)^N → heatOp t` — the step and flow halves of the
line meeting in one argument, exactly the house doctrine that
irreversibility lives in steps, read backwards as an
approximation theorem.

**What is proved, at T1.**
- Positivity: `arrowFlow` preserves nonnegative fields
  (`t ≥ 0`), and strictly positive fields with the exponential
  lower bound above. Mass is conserved (`sum_arrowFlow`), so
  the normalized evolved field is a probability weight at
  every time.
- The H-theorem shape, at its honest strength: for a strictly
  positive probability weight `p`, `entropyW (θ t)` is monotone
  non-decreasing on `t ≥ 0`, with production rate
  `d/dt entropyW (θ t) = ∑ i, log ((θ t) i) · (L (θ t)) i
  = (1/2) ∑ i j, w i j (log (θ t) i − log (θ t) j) ((θ t) i − (θ t) j) ≥ 0`
  (the symmetrization identity is proved, not cited).
- The relative-entropy form: `relEntW p uniform = log (card V)
  − entropyW p`, so relative entropy to the uniform equilibrium
  is antitone along the flow.

**Fences.** The entropy statement is for strictly positive
initial fields (a *positive* field, in the scoping's words);
at fields with zero entries the evolved entropy is not
claimed differentiable or monotone by anything here (mass in
a disconnected component never reaches another, and `log 0`
is not differentiable — the restriction is the mathematics,
not a hedge). NO CLAIM; dials 0/4; Dial 2 = 0. Not the
cosmological arrow, not the Second Law as a claim about the
world: a finite seat's H-theorem, exactly.
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Degree bookkeeping -/

theorem degSum_nonneg (w : V → V → ℝ) (hw0 : ∀ i j, 0 ≤ w i j) :
    0 ≤ degSum w := by
  show 0 ≤ ∑ i, ∑ j, if j = i then 0 else w i j
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs with h
  · exact le_refl 0
  · exact hw0 i j

theorem rowSum_le_degSum (w : V → V → ℝ) (hw0 : ∀ i j, 0 ≤ w i j) (i : V) :
    (∑ j, if j = i then 0 else w i j) ≤ degSum w := by
  show (∑ j, if j = i then 0 else w i j)
    ≤ ∑ i, ∑ j, if j = i then 0 else w i j
  apply Finset.single_le_sum (f := fun i => ∑ j, if j = i then 0 else w i j)
  · intro i' _
    apply Finset.sum_nonneg
    intro j _
    split_ifs with h
    · exact le_refl 0
    · exact hw0 i' j
  · exact Finset.mem_univ i

/-! ## The Euler step: entrywise form, positivity, lower bound -/

/-- The Euler step, entrywise: the diagonal coefficient is
`1 − τ · (row sum)`, the off-diagonal part is the weighted sum
of the other entries. -/
theorem eulerStep_apply_form (w : V → V → ℝ) (τ : ℝ) (F : V → ℝ) (i : V) :
    eulerStep w τ F i
      = (1 - τ * (∑ j, if j = i then 0 else w i j)) * F i
        + τ * ∑ j, (if j = i then 0 else w i j) * F j := by
  have hL : laplacianOp w F i
      = (∑ j, if j = i then 0 else w i j) * F i
        - ∑ j, (if j = i then 0 else w i j) * F j := by
    show (∑ j, w i j * (F i - F j)) = _
    have h1 : ∀ j, w i j * (F i - F j)
        = (if j = i then 0 else w i j) * (F i - F j) := by
      intro j
      by_cases h : j = i
      · rw [h]
        simp
      · rw [if_neg h]
    rw [Finset.sum_congr rfl (fun j _ => h1 j)]
    have h2 : ∀ j, (if j = i then 0 else w i j) * (F i - F j)
        = (if j = i then 0 else w i j) * F i
          - (if j = i then 0 else w i j) * F j := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => h2 j), Finset.sum_sub_distrib,
      ← Finset.sum_mul]
  show (F - τ • laplacianOp w F) i = _
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hL]
  ring

/-- One Euler step at/below the stability bound preserves
nonnegative fields, entrywise. -/
theorem eulerStep_nonneg (w : V → V → ℝ) (hw0 : ∀ i j, 0 ≤ w i j)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (hτR : ∀ i, τ * (∑ j, if j = i then 0 else w i j) ≤ 1)
    {F : V → ℝ} (hF : ∀ i, 0 ≤ F i) (i : V) :
    0 ≤ eulerStep w τ F i := by
  rw [eulerStep_apply_form]
  apply add_nonneg
  · exact mul_nonneg (by linarith [hτR i]) (hF i)
  · apply mul_nonneg hτ
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg _ (hF j)
    split_ifs with h
    · exact le_refl 0
    · exact hw0 i j

/-- Every Euler iterate preserves nonnegative fields. -/
theorem eulerStep_iterate_nonneg (w : V → V → ℝ) (hw0 : ∀ i j, 0 ≤ w i j)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (hτR : ∀ i, τ * (∑ j, if j = i then 0 else w i j) ≤ 1)
    {F : V → ℝ} (hF : ∀ i, 0 ≤ F i) (N : ℕ) (i : V) :
    0 ≤ (eulerStep w τ)^[N] F i := by
  induction N generalizing i with
  | zero => simpa using hF i
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact eulerStep_nonneg w hw0 hτ hτR ih i

/-- One Euler step dominates the diagonal lower bound
`(1 − τ · degSum w) · F i` — the off-diagonal contribution is
dropped (it is nonnegative), and the row sum is bounded by
`degSum w`. -/
theorem eulerStep_lower (w : V → V → ℝ) (hw0 : ∀ i j, 0 ≤ w i j)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (hτR : ∀ i, τ * (∑ j, if j = i then 0 else w i j) ≤ 1)
    {F : V → ℝ} (hF : ∀ i, 0 ≤ F i) (i : V) :
    (1 - τ * degSum w) * F i ≤ eulerStep w τ F i := by
  rw [eulerStep_apply_form]
  have h1 : τ * (∑ j, if j = i then 0 else w i j) ≤ τ * degSum w :=
    mul_le_mul_of_nonneg_left (rowSum_le_degSum w hw0 i) hτ
  have h2 : (1 - τ * degSum w) * F i
      ≤ (1 - τ * (∑ j, if j = i then 0 else w i j)) * F i :=
    mul_le_mul_of_nonneg_right (by linarith) (hF i)
  have h3 : (0:ℝ) ≤ τ * ∑ j, (if j = i then 0 else w i j) * F j :=
    mul_nonneg hτ (Finset.sum_nonneg fun j _ => mul_nonneg
      (by split_ifs with h
          · exact le_refl 0
          · exact hw0 i j) (hF j))
  linarith

/-- The diagonal lower bound iterates:
`(1 − τ · degSum w)^N · F i ≤ (eulerStep^N F) i`. -/
theorem eulerStep_iterate_lower (w : V → V → ℝ) (hw0 : ∀ i j, 0 ≤ w i j)
    {τ : ℝ} (hτ : 0 ≤ τ) (hτD : τ * degSum w ≤ 1)
    (hτR : ∀ i, τ * (∑ j, if j = i then 0 else w i j) ≤ 1)
    {F : V → ℝ} (hF : ∀ i, 0 ≤ F i) (N : ℕ) (i : V) :
    (1 - τ * degSum w) ^ N * F i ≤ (eulerStep w τ)^[N] F i := by
  induction N with
  | zero => simpa using le_refl (F i)
  | succ n ih =>
    calc (1 - τ * degSum w) ^ (n + 1) * F i
        = (1 - τ * degSum w) * ((1 - τ * degSum w) ^ n * F i) := by
          rw [pow_succ]
          ring
      _ ≤ (1 - τ * degSum w) * ((eulerStep w τ)^[n] F i) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
      _ ≤ eulerStep w τ ((eulerStep w τ)^[n] F) i :=
          eulerStep_lower w hw0 hτ hτR (eulerStep_iterate_nonneg w hw0 hτ hτR hF n) i
      _ = (eulerStep w τ)^[n + 1] F i :=
          congrFun (Function.iterate_succ_apply' _ _ _).symm i

/-! ## The Euclidean Euler step and the spectral limit -/

/-- The Euler step as an operator on the Euclidean space:
`1 − τ • lapLin w`, the same step `eulerStep` reads on fields. -/
noncomputable def arrowStepE (w : V → V → ℝ) (τ : ℝ) :
    EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V :=
  1 - τ • lapLin w

theorem arrowStepE_apply (w : V → V → ℝ) (τ : ℝ) (y : EuclideanSpace ℝ V) :
    arrowStepE w τ y = y - τ • lapLin w y := by
  show ((1 : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V) - τ • lapLin w) y = _
  rw [LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply]

/-- The step is diagonal in the spectral basis, with factor
`1 − τ λₖ`: its coefficients multiply mode by mode. -/
theorem repr_arrowStepE (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (τ : ℝ) (y : EuclideanSpace ℝ V)
    (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) :
    (lapBasis w hsymm).repr (arrowStepE w τ y) k
      = (1 - τ * lapEig w hsymm k) * (lapBasis w hsymm).repr y k := by
  rw [(lapBasis w hsymm).repr_apply_apply, arrowStepE_apply, inner_sub_right,
    inner_smul_right,
    ← hsymm ((lapBasis w hsymm) k) y, lapBasis_apply_eig, inner_smul_left,
    starRingEnd_apply, star_id_of_comm,
    ← (lapBasis w hsymm).repr_apply_apply]
  ring

/-- The iterated step's coefficients: `(1 − τ λₖ)^N` times the
initial coefficients. -/
theorem repr_arrowStepE_iterate (w : V → V → ℝ)
    (hsymm : (lapLin w).IsSymmetric) (τ : ℝ) (N : ℕ) (x : EuclideanSpace ℝ V)
    (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) :
    (lapBasis w hsymm).repr ((arrowStepE w τ)^[N] x) k
      = (1 - τ * lapEig w hsymm k) ^ N * (lapBasis w hsymm).repr x k := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', repr_arrowStepE, ih, ← mul_assoc,
      ← pow_succ']

/-- The field-side and Euclidean Euler steps are the same
operator, read through `euclEquiv` — and so are their
iterates. -/
theorem eulerStep_transport (w : V → V → ℝ) (τ : ℝ) (G : V → ℝ) :
    eulerStep w τ G = euclEquiv (arrowStepE w τ (euclEquiv.symm G)) := by
  show (G - τ • laplacianOp w G) = _
  rw [arrowStepE_apply, map_sub, map_smul, equiv_lapLin,
    LinearEquiv.apply_symm_apply]

theorem eulerStep_iterate_transport (w : V → V → ℝ) (τ : ℝ) (N : ℕ)
    (G : V → ℝ) :
    (eulerStep w τ)^[N] G
      = euclEquiv ((arrowStepE w τ)^[N] (euclEquiv.symm G)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      eulerStep_transport]
    have ih' : euclEquiv.symm ((eulerStep w τ)^[n] G)
        = (arrowStepE w τ)^[n] (euclEquiv.symm G) := by
      rw [ih, LinearEquiv.symm_apply_apply]
    rw [ih']

/-- The coefficients of a basis sum. -/
theorem repr_sum_smul (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (a : Fin (Module.finrank ℝ (EuclideanSpace ℝ V)) → ℝ)
    (j : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) :
    (lapBasis w hsymm).repr (∑ k, a k • (lapBasis w hsymm) k) j = a j := by
  rw [(lapBasis w hsymm).repr_apply_apply, inner_sum]
  rw [Finset.sum_eq_single j]
  · rw [inner_smul_right,
      orthonormal_iff_ite.mp (lapBasis w hsymm).orthonormal j j, if_pos rfl,
      mul_one]
  · intro k _ hk
    rw [inner_smul_right,
      orthonormal_iff_ite.mp (lapBasis w hsymm).orthonormal j k,
      if_neg (Ne.symm hk), mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- The scalar Euler limit: `(1 − a/N)^N → exp (−a)` — read off
Mathlib's complex `(1 + t/n)^n → exp t` through the real cast. -/
theorem tendsto_one_sub_div_pow_exp (a : ℝ) :
    Filter.Tendsto (fun N : ℕ => (1 - a / N) ^ N) Filter.atTop
      (nhds (Real.exp (-a))) := by
  have hC := Complex.tendsto_one_add_div_pow_exp ((-(a) : ℂ))
  have heq : ∀ N : ℕ, (1 + (-(a) : ℂ) / N) ^ N
      = (((1 - a / N) ^ N : ℝ) : ℂ) := by
    intro N
    push_cast
    congr 1
    ring
  have hC2 := hC.congr heq
  have harg : (-(a) : ℂ) = ((-a : ℝ) : ℂ) := by
    push_cast
    ring
  have hlim : Complex.exp (-(a) : ℂ) = ((Real.exp (-a) : ℝ) : ℂ) := by
    rw [harg, ← Complex.ofReal_exp]
  rw [hlim] at hC2
  exact Filter.tendsto_ofReal_iff.mp hC2

/-- **The approximation theorem.** The Euler iterates converge
to the heat flow in norm: `‖heatOp t x − (1 − (t/N)L)^N x‖ → 0`.
Mode by mode this is the scalar Euler limit; the finite sum
passes through. -/
theorem tendsto_arrowStepE_iterate (w : V → V → ℝ)
    (hsymm : (lapLin w).IsSymmetric) (t : ℝ) (x : EuclideanSpace ℝ V) :
    Filter.Tendsto (fun N : ℕ => (arrowStepE w (t / N))^[N] x) Filter.atTop
      (nhds (heatOp w hsymm t x)) := by
  have hdiff : Filter.Tendsto
      (fun N : ℕ => heatOp w hsymm t x - (arrowStepE w (t / N))^[N] x)
      Filter.atTop (nhds 0) := by
    have hfun : ∀ N : ℕ, heatOp w hsymm t x - (arrowStepE w (t / N))^[N] x
        = ∑ k, ((Real.exp (-(lapEig w hsymm k) * t)
            - (1 - (t / N) * lapEig w hsymm k) ^ N)
            * (lapBasis w hsymm).repr x k) • (lapBasis w hsymm) k := by
      intro N
      apply (lapBasis w hsymm).repr.injective
      apply PiLp.ext
      intro j
      rw [map_sub, PiLp.sub_apply, heatOp_repr,
        repr_arrowStepE_iterate, repr_sum_smul]
      ring
    rw [Filter.tendsto_congr (fun N => hfun N)]
    have hterm : ∀ k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V)),
        Filter.Tendsto (fun N : ℕ => ((Real.exp (-(lapEig w hsymm k) * t)
            - (1 - (t / N) * lapEig w hsymm k) ^ N)
            * (lapBasis w hsymm).repr x k) • (lapBasis w hsymm) k)
          Filter.atTop (nhds 0) := by
      intro k
      have hscal : Filter.Tendsto
          (fun N : ℕ => (1 - (t / N) * lapEig w hsymm k) ^ N) Filter.atTop
          (nhds (Real.exp (-(lapEig w hsymm k) * t))) := by
        have h := tendsto_one_sub_div_pow_exp (t * lapEig w hsymm k)
        have hform : ∀ N : ℕ, (1 - (t * lapEig w hsymm k) / N) ^ N
            = (1 - (t / N) * lapEig w hsymm k) ^ N := by
          intro N
          congr 1
          congr 1
          rw [div_mul_eq_mul_div]
        rw [Filter.tendsto_congr (fun N => hform N)] at h
        have hexp : Real.exp (-(t * lapEig w hsymm k))
            = Real.exp (-(lapEig w hsymm k) * t) := by
          congr 1
          ring
        rwa [hexp] at h
      have h1 : Filter.Tendsto
          (fun N : ℕ => Real.exp (-(lapEig w hsymm k) * t)
            - (1 - (t / N) * lapEig w hsymm k) ^ N) Filter.atTop (nhds 0) := by
        have h2 : Filter.Tendsto
            (fun N : ℕ => Real.exp (-(lapEig w hsymm k) * t)
              - (1 - (t / N) * lapEig w hsymm k) ^ N) Filter.atTop
            (nhds (Real.exp (-(lapEig w hsymm k) * t)
              - Real.exp (-(lapEig w hsymm k) * t))) :=
          tendsto_const_nhds.sub hscal
        rwa [sub_self] at h2
      have h2 := h1.mul_const ((lapBasis w hsymm).repr x k)
      rw [zero_mul] at h2
      have h3 := h2.smul_const ((lapBasis w hsymm) k)
      rwa [zero_smul] at h3
    have hsum := tendsto_finsetSum Finset.univ (fun k _ => hterm k)
    rwa [Finset.sum_const_zero] at hsum
  have h2 : Filter.Tendsto
      (fun N : ℕ => heatOp w hsymm t x
        - (heatOp w hsymm t x - (arrowStepE w (t / N))^[N] x))
      Filter.atTop (nhds (heatOp w hsymm t x)) := by
    have h3 : Filter.Tendsto
        (fun N : ℕ => heatOp w hsymm t x
          - (heatOp w hsymm t x - (arrowStepE w (t / N))^[N] x))
        Filter.atTop (nhds (heatOp w hsymm t x - 0)) :=
      tendsto_const_nhds.sub hdiff
    rwa [sub_zero] at h3
  exact h2.congr' (Filter.Eventually.of_forall fun N => sub_sub_self _ _)

/-- A component bound: a Euclidean vector's component is at
most its norm (Cauchy–Schwarz against a basis vector). -/
theorem norm_apply_le_norm (y : EuclideanSpace ℝ V) (i : V) :
    ‖y i‖ ≤ ‖y‖ := by
  have h : y i = ⟪EuclideanSpace.single i 1, y⟫_ℝ := by
    rw [EuclideanSpace.inner_single_left]
    simp
  rw [h]
  calc ‖⟪EuclideanSpace.single i 1, y⟫_ℝ‖
      ≤ ‖EuclideanSpace.single i 1‖ * ‖y‖ := norm_inner_le_norm _ _
    _ = ‖y‖ := by rw [EuclideanSpace.norm_single, norm_one, one_mul]

/-- Components of the Euler iterates converge to the flow's
components (norm convergence plus the component bound). -/
theorem tendsto_arrowStepE_iterate_apply (w : V → V → ℝ)
    (hsymm : (lapLin w).IsSymmetric) (t : ℝ) (x : EuclideanSpace ℝ V)
    (i : V) :
    Filter.Tendsto (fun N : ℕ => ((arrowStepE w (t / N))^[N] x) i)
      Filter.atTop (nhds ((heatOp w hsymm t x) i)) := by
  have hdiff : Filter.Tendsto
      (fun N : ℕ => ((arrowStepE w (t / N))^[N] x) i - (heatOp w hsymm t x) i)
      Filter.atTop (nhds 0) := by
    have hmain : Filter.Tendsto (fun N : ℕ => ((arrowStepE w (t / N))^[N] x) i)
        Filter.atTop (nhds ((heatOp w hsymm t x) i)) :=
      ((PiLp.continuous_apply (p := 2) (β := fun _ : V => ℝ) i).tendsto
        (heatOp w hsymm t x)).comp
          (tendsto_arrowStepE_iterate w hsymm t x)
    have hsub : Filter.Tendsto
        (fun N : ℕ => ((arrowStepE w (t / N))^[N] x) i
          - (heatOp w hsymm t x) i)
        Filter.atTop (nhds ((heatOp w hsymm t x) i
          - (heatOp w hsymm t x) i)) :=
      hmain.sub tendsto_const_nhds
    rwa [sub_self] at hsub
  have h := hdiff.add_const ((heatOp w hsymm t x) i)
  rw [zero_add] at h
  have hfun2 : (fun N : ℕ => ((arrowStepE w (t / N))^[N] x) i
        - (heatOp w hsymm t x) i + (heatOp w hsymm t x) i)
      = (fun N : ℕ => ((arrowStepE w (t / N))^[N] x) i) :=
    funext fun N => sub_add_cancel _ _
  rwa [hfun2] at h

/-! ## Positivity of the heat flow (K-ARR-POS's gate) -/

/-- For all sufficiently large `N`, the Euler step size
`t / N` is within the stability bound against every row sum
and against the degree sum. -/
theorem eventually_step_size (w : V → V → ℝ) (hw0 : ∀ i j, 0 ≤ w i j)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (∀ i, (t / N) * (∑ j, if j = i then 0 else w i j) ≤ 1)
        ∧ (t / N) * degSum w ≤ 1 := by
  refine Filter.eventually_atTop.mpr ⟨⌊t * degSum w⌋₊ + 1, fun N hN => ?_⟩
  have hN0 : (0:ℝ) < N := by
    have h1 : (0:ℕ) < N := lt_of_lt_of_le (by norm_num) hN
    exact_mod_cast h1
  have hlt : t * degSum w < (N : ℝ) := by
    have h2 := Nat.lt_floor_add_one (t * degSum w)
    have h3 : (⌊t * degSum w⌋₊ + 1 : ℝ) ≤ N := by exact_mod_cast hN
    have h4 : ((⌊t * degSum w⌋₊ + 1 : ℕ) : ℝ)
        = (⌊t * degSum w⌋₊ : ℝ) + 1 := by push_cast; ring
    linarith
  have h1 : (t / N) * degSum w ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hN0]
    linarith
  refine ⟨fun i => ?_, h1⟩
  calc (t / N) * (∑ j, if j = i then 0 else w i j)
      ≤ (t / N) * degSum w :=
        mul_le_mul_of_nonneg_left (rowSum_le_degSum w hw0 i)
          (div_nonneg ht (le_of_lt hN0))
    _ ≤ 1 := h1

/-- **Positivity (the K-ARR-POS gate, passed).** For `t ≥ 0`
the heat flow preserves nonnegative fields, entrywise: the
values at large `N` are Euler iterates, hence nonnegative,
and nonnegativity passes to the limit. -/
theorem arrowFlow_nonneg (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) (hsymm : (lapLin w).IsSymmetric)
    {t : ℝ} (ht : 0 ≤ t) {F : V → ℝ} (hF : ∀ i, 0 ≤ F i) (i : V) :
    0 ≤ arrowFlow w hsymm t F i := by
  have hlim : Filter.Tendsto
      (fun N : ℕ => ((arrowStepE w (t / N))^[N] (euclEquiv.symm F)) i)
      Filter.atTop (nhds (arrowFlow w hsymm t F i)) :=
    tendsto_arrowStepE_iterate_apply w hsymm t (euclEquiv.symm F) i
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [eventually_step_size w hw0 ht] with N hN
  have htr := eulerStep_iterate_transport w (t / N) N F
  have hcomp : ((arrowStepE w (t / N))^[N] (euclEquiv.symm F)) i
      = (eulerStep w (t / N))^[N] F i := by
    show euclEquiv ((arrowStepE w (t / N))^[N] (euclEquiv.symm F)) i
        = (eulerStep w (t / N))^[N] F i
    rw [htr]
  rw [hcomp]
  exact eulerStep_iterate_nonneg w hw0 (div_nonneg ht (by positivity)) hN.1
    hF N i

/-- **The strict lower bound.** A strictly positive field
stays strictly positive under the flow, with the diagonal
bound `(θ t) i ≥ exp (−t · degSum w) · θ i`: the Euler
iterates dominate `(1 − (t/N) degSum w)^N · θ i`, and the
scalar Euler limit closes it. -/
theorem arrowFlow_pos_lower (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) (hsymm : (lapLin w).IsSymmetric)
    {t : ℝ} (ht : 0 ≤ t) {F : V → ℝ} (hF : ∀ i, 0 < F i) (i : V) :
    Real.exp (-(t * degSum w)) * F i ≤ arrowFlow w hsymm t F i := by
  have hlim1 : Filter.Tendsto
      (fun N : ℕ => ((arrowStepE w (t / N))^[N] (euclEquiv.symm F)) i)
      Filter.atTop (nhds (arrowFlow w hsymm t F i)) :=
    tendsto_arrowStepE_iterate_apply w hsymm t (euclEquiv.symm F) i
  have hlim2 : Filter.Tendsto
      (fun N : ℕ => (1 - (t / N) * degSum w) ^ N * F i) Filter.atTop
      (nhds (Real.exp (-(t * degSum w)) * F i)) := by
    have h := tendsto_one_sub_div_pow_exp (t * degSum w)
    have hform : ∀ N : ℕ, (1 - (t * degSum w) / N) ^ N
        = (1 - (t / N) * degSum w) ^ N := by
      intro N
      congr 1
      congr 1
      rw [div_mul_eq_mul_div]
    rw [Filter.tendsto_congr (fun N => hform N)] at h
    exact h.mul_const (F i)
  apply le_of_tendsto_of_tendsto hlim2 hlim1
  filter_upwards [eventually_step_size w hw0 ht] with N hN
  have htr := eulerStep_iterate_transport w (t / N) N F
  have hcomp : ((arrowStepE w (t / N))^[N] (euclEquiv.symm F)) i
      = (eulerStep w (t / N))^[N] F i := by
    show euclEquiv ((arrowStepE w (t / N))^[N] (euclEquiv.symm F)) i
        = (eulerStep w (t / N))^[N] F i
    rw [htr]
  rw [hcomp]
  exact eulerStep_iterate_lower w hw0 (div_nonneg ht (by positivity)) hN.2
    hN.1 (fun i => (hF i).le) N i

/-- Strict positivity along the flow, as a corollary of the
lower bound. -/
theorem arrowFlow_pos (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) (hsymm : (lapLin w).IsSymmetric)
    {t : ℝ} (ht : 0 ≤ t) {F : V → ℝ} (hF : ∀ i, 0 < F i) (i : V) :
    0 < arrowFlow w hsymm t F i :=
  lt_of_lt_of_le (mul_pos (Real.exp_pos _) (hF i))
    (arrowFlow_pos_lower w hw hw0 hsymm ht hF i)

/-! ## Transported derivative and mass conservation -/

/-- The flow on fields differentiates to `−L (θ t)`: the
transport of the landed `heatFlow_hasDerivAt` through
`euclEquiv` as a continuous linear map. -/
theorem arrowFlow_hasDerivAt (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (G : V → ℝ) (t : ℝ) :
    HasDerivAt (fun s => arrowFlow w hsymm s G)
      (-(laplacianOp w (arrowFlow w hsymm t G))) t := by
  let cle : EuclideanSpace ℝ V →L[ℝ] (V → ℝ) :=
    { toLinearMap := euclEquiv.toLinearMap
      cont := euclEquiv.toLinearMap.continuous_of_finiteDimensional }
  have h := heatFlow_hasDerivAt w hsymm (euclEquiv.symm G) t
  have h2 := cle.hasFDerivAt.comp_hasDerivAt t h
  have h3 : cle (-(lapLin w (heatOp w hsymm t (euclEquiv.symm G))))
      = -(laplacianOp w (arrowFlow w hsymm t G)) := by
    show euclEquiv (-(lapLin w (heatOp w hsymm t (euclEquiv.symm G))))
      = -(laplacianOp w (euclEquiv (heatOp w hsymm t (euclEquiv.symm G))))
    rw [map_neg, equiv_lapLin]
  rwa [h3] at h2

/-- The heat operator is self-adjoint (spectral factors are
real): `⟪heatOp t a, b⟫ = ⟪a, heatOp t b⟫`. -/
theorem heatOp_inner_symm (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (t : ℝ) (a b : EuclideanSpace ℝ V) :
    ⟪heatOp w hsymm t a, b⟫_ℝ = ⟪a, heatOp w hsymm t b⟫_ℝ := by
  rw [← (lapBasis w hsymm).sum_inner_mul_inner (heatOp w hsymm t a) b,
    ← (lapBasis w hsymm).sum_inner_mul_inner a (heatOp w hsymm t b)]
  apply Finset.sum_congr rfl
  intro k _
  have e1 : ⟪heatOp w hsymm t a, (lapBasis w hsymm) k⟫_ℝ
      = Real.exp (-(lapEig w hsymm k) * t) * ⟪a, (lapBasis w hsymm) k⟫_ℝ := by
    rw [real_inner_comm ((lapBasis w hsymm) k) (heatOp w hsymm t a),
      heatOp_inner_basis, real_inner_comm a ((lapBasis w hsymm) k)]
  have e2 : ⟪(lapBasis w hsymm) k, heatOp w hsymm t b⟫_ℝ
      = Real.exp (-(lapEig w hsymm k) * t) * ⟪(lapBasis w hsymm) k, b⟫_ℝ :=
    heatOp_inner_basis w hsymm t b k
  rw [e1, e2]
  ring

/-- **Mass conservation.** The flow preserves the total:
`∑ j, (θ t) j = ∑ j, θ j` — the constant vector is fixed and
the flow is self-adjoint. Hence the normalized evolved field
of a probability weight is the evolved field itself. -/
theorem sum_arrowFlow (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (hsymm : (lapLin w).IsSymmetric) (t : ℝ) (G : V → ℝ) :
    ∑ j, arrowFlow w hsymm t G j = ∑ j, G j := by
  have h1 : ∀ y : EuclideanSpace ℝ V, ∑ j, (euclEquiv y) j
      = ⟪constEucl 1, y⟫_ℝ := by
    intro y
    rw [euclid_inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [constEucl_apply, euclEquiv_apply, one_mul]
  have h2 : ∑ j, arrowFlow w hsymm t G j
      = ⟪constEucl 1, heatOp w hsymm t (euclEquiv.symm G)⟫_ℝ := by
    rw [← h1 (heatOp w hsymm t (euclEquiv.symm G))]
    apply Finset.sum_congr rfl
    intro j _
    rfl
  have h3 : ∑ j, G j = ⟪constEucl 1, euclEquiv.symm G⟫_ℝ := by
    rw [← h1 (euclEquiv.symm G)]
    apply Finset.sum_congr rfl
    intro j _
    exact congrFun (LinearEquiv.apply_symm_apply euclEquiv G) j
  rw [h2, h3, ← heatOp_inner_symm w hsymm t (constEucl 1) (euclEquiv.symm G)]
  congr 1
  exact heatOp_eq_of_lapLin_eq_zero w hsymm t _ (lapLin_constEucl w 1)

/-- The flow is linear in the field (scalar form). -/
theorem arrowFlow_smul (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (t : ℝ) (c : ℝ) (G : V → ℝ) :
    arrowFlow w hsymm t (c • G) = c • arrowFlow w hsymm t G := by
  simp only [arrowFlow, map_smul]

/-! ## The entropy production identity -/

/-- **Entropy production.** For a strictly positive field
`q`, the entropy production of `L q` against `log q` is the
symmetrized Dirichlet form
`(1/2) ∑∑ w (log qᵢ − log qⱼ)(qᵢ − qⱼ)` — the
Fisher-information-type form of the Shannon entropy along
this flow. -/
theorem log_laplacianOp_symm (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    {q : V → ℝ} (hq : ∀ i, 0 < q i) :
    ∑ i, Real.log (q i) * laplacianOp w q i
      = (1/2) * ∑ i, ∑ j, w i j
          * (Real.log (q i) - Real.log (q j)) * (q i - q j) := by
  have hS : (∑ i, Real.log (q i) * laplacianOp w q i)
      = ∑ i, ∑ j, w i j * Real.log (q i) * (q i - q j) := by
    apply Finset.sum_congr rfl
    intro i _
    show Real.log (q i) * (∑ j, w i j * (q i - q j)) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hT : (∑ i, ∑ j, w i j
        * (Real.log (q i) - Real.log (q j)) * (q i - q j))
      = (∑ i, ∑ j, w i j * Real.log (q i) * (q i - q j))
        + ∑ i, ∑ j, w i j * Real.log (q j) * (q j - q i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hSwap : (∑ i, ∑ j, w i j * Real.log (q j) * (q j - q i))
      = ∑ i, ∑ j, w i j * Real.log (q i) * (q i - q j) := by
    calc (∑ i, ∑ j, w i j * Real.log (q j) * (q j - q i))
        = ∑ j, ∑ i, w i j * Real.log (q j) * (q j - q i) :=
          Finset.sum_comm
      _ = ∑ i, ∑ j, w i j * Real.log (q i) * (q i - q j) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [hw b a]
  linarith [hS, hT, hSwap]

/-- The production form is nonnegative: `log` is monotone,
so each factor pair has the same sign. -/
theorem log_laplacianOp_nonneg (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    {q : V → ℝ} (hq : ∀ i, 0 < q i) :
    0 ≤ ∑ i, Real.log (q i) * laplacianOp w q i := by
  rw [log_laplacianOp_symm w hw hq]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  by_cases hle : q i ≤ q j
  · have h1 : Real.log (q i) - Real.log (q j) ≤ 0 :=
      sub_nonpos.mpr (Real.log_le_log (hq i) hle)
    have h2 : q i - q j ≤ 0 := sub_nonpos.mpr hle
    have := mul_nonneg_of_nonpos_of_nonpos h1 h2
    rw [mul_assoc]
    exact mul_nonneg (hw0 i j) this
  · have hle2 : q j ≤ q i := le_of_not_ge hle
    have h1 : 0 ≤ Real.log (q i) - Real.log (q j) :=
      sub_nonneg.mpr (Real.log_le_log (hq j) hle2)
    have h2 : 0 ≤ q i - q j := sub_nonneg.mpr hle2
    rw [mul_assoc]
    exact mul_nonneg (hw0 i j) (mul_nonneg h1 h2)

/-- The derivative of the entropy along the flow is the
production: `d/dt entropyW (θ t) = ∑ log (θ t) · L (θ t)`. -/
theorem entropyW_arrowFlow_hasDerivAt (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) {F : V → ℝ} (hF : ∀ i, 0 < F i)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => entropyW (arrowFlow w hsymm s F))
      (∑ i, Real.log (arrowFlow w hsymm t F i)
        * laplacianOp w (arrowFlow w hsymm t F) i) t := by
  set q := arrowFlow w hsymm t F with hqdef
  have hq : ∀ i, 0 < q i := arrowFlow_pos w hw hw0 hsymm ht hF
  have hcomp : ∀ i, HasDerivAt (fun s => arrowFlow w hsymm s F i)
      (-(laplacianOp w q i)) t := by
    intro i
    have hfr := arrowFlow_hasDerivAt w hsymm F t
    exact ((ContinuousLinearMap.proj i).hasFDerivAt).comp_hasDerivAt t hfr
  have hterm : ∀ i, HasDerivAt
      (fun s => (fun x => x * Real.log x) (arrowFlow w hsymm s F i))
      ((Real.log (q i) + 1) * (-(laplacianOp w q i))) t := by
    intro i
    have hderiv : HasDerivAt (fun x : ℝ => x * Real.log x)
        (Real.log (q i) + 1) (q i) := by
      have h1 := (hasDerivAt_id (q i)).mul
        (Real.hasDerivAt_log (ne_of_gt (hq i)))
      have h2 : q i * (q i)⁻¹ = 1 :=
        mul_inv_cancel₀ (ne_of_gt (hq i))
      have h3 : (1 : ℝ) * Real.log (q i) + q i * (q i)⁻¹
          = Real.log (q i) + 1 := by
        rw [h2, one_mul]
      exact h1.congr_deriv h3
    exact hderiv.comp t (hcomp i)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hterm i)
  have hneg := hsum.neg
  have hfun : (fun s => entropyW (arrowFlow w hsymm s F))
      = fun s => -∑ i, (fun x => x * Real.log x)
          (arrowFlow w hsymm s F i) := by
    funext s
    rfl
  have e1 : (∑ i, (Real.log (q i) + 1) * (-(laplacianOp w q i)))
      = -∑ i, Real.log (q i) * laplacianOp w q i := by
    calc (∑ i, (Real.log (q i) + 1) * (-(laplacianOp w q i)))
        = ∑ i, (-(Real.log (q i) * laplacianOp w q i)
            + -laplacianOp w q i) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ i, -(Real.log (q i) * laplacianOp w q i))
            + ∑ i, -laplacianOp w q i := Finset.sum_add_distrib
      _ = -∑ i, Real.log (q i) * laplacianOp w q i := by
          rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib,
            sum_laplacianOp_eq_zero w hw q, neg_zero, add_zero]
  have hderiv_eq : -(∑ i, (Real.log (q i) + 1) * (-(laplacianOp w q i)))
      = ∑ i, Real.log (q i) * laplacianOp w q i := by
    rw [e1, neg_neg]
  rw [hfun]
  exact hderiv_eq ▸ hneg

/-- **FA-4b, LANDED (contingency passed).** The Shannon
entropy `entropyW` of the evolved field is monotone
nondecreasing in `t` on `Ici 0`, for strictly positive
initial fields on a nonnegative symmetric weight. -/
theorem entropyW_arrowFlow_monotoneOn (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) {F : V → ℝ} (hF : ∀ i, 0 < F i) :
    MonotoneOn (fun t => entropyW (arrowFlow w hsymm t F)) (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · intro t ht
    rw [Set.mem_Ici] at ht
    exact (entropyW_arrowFlow_hasDerivAt w hw hw0 hsymm hF
      ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ici, Set.mem_Ioi] at ht
    exact (entropyW_arrowFlow_hasDerivAt w hw hw0 hsymm hF
      ht.le).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici, Set.mem_Ioi] at ht
    have hd := entropyW_arrowFlow_hasDerivAt w hw hw0 hsymm hF ht.le
    rw [hd.deriv]
    exact log_laplacianOp_nonneg w hw hw0
      (arrowFlow_pos w hw hw0 hsymm ht.le hF)

/-! ## The relative-entropy face -/

/-- Relative entropy to the uniform weight is `log (card V)`
minus the Shannon entropy of the weight itself. -/
theorem relEntW_uniform_eq [Nonempty V] {p : V → ℝ}
    (hp : IsProbWeight p) :
    relEntW p (fun _ => (((Finset.univ : Finset V).card : ℝ))⁻¹)
      = Real.log ((Finset.univ : Finset V).card : ℝ) - entropyW p := by
  have hcard1 : Real.log ((Finset.univ : Finset V).card : ℝ)
      = ∑ i, p i * Real.log ((Finset.univ : Finset V).card : ℝ) := by
    rw [← Finset.sum_mul, hp.2, one_mul]
  calc relEntW p (fun _ => (((Finset.univ : Finset V).card : ℝ))⁻¹)
      = ∑ i, p i * Real.log (p i / (((Finset.univ : Finset V).card : ℝ))⁻¹) := rfl
    _ = ∑ i, (p i * Real.log (p i)
          + p i * Real.log ((Finset.univ : Finset V).card : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : p i = 0
        · simp [hi]
        · have hcard : (0:ℝ) < (Finset.univ : Finset V).card :=
            Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨i, Finset.mem_univ i⟩)
          have hlog : Real.log (p i / (((Finset.univ : Finset V).card : ℝ))⁻¹)
              = Real.log (p i) + Real.log ((Finset.univ : Finset V).card : ℝ) := by
            rw [div_eq_mul_inv, inv_inv, Real.log_mul hi (ne_of_gt hcard)]
          rw [hlog]
          ring
    _ = (∑ i, p i * Real.log (p i))
          + ∑ i, p i * Real.log ((Finset.univ : Finset V).card : ℝ) :=
        Finset.sum_add_distrib
    _ = Real.log ((Finset.univ : Finset V).card : ℝ) - entropyW p := by
        rw [← hcard1]
        show (∑ i, p i * Real.log (p i)) + Real.log ((Finset.univ : Finset V).card : ℝ)
            = Real.log ((Finset.univ : Finset V).card : ℝ)
              - (-∑ i, p i * Real.log (p i))
        ring

/-- The evolved field of a probability weight is a
probability weight (positivity + mass conservation). -/
theorem arrowFlow_probWeight (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) {t : ℝ} (ht : 0 ≤ t)
    {p : V → ℝ} (hp : IsProbWeight p) :
    IsProbWeight (arrowFlow w hsymm t p) :=
  ⟨fun i => arrowFlow_nonneg w hw hw0 hsymm ht hp.1 i,
    by rw [sum_arrowFlow w hw hsymm t p]; exact hp.2⟩

/-- **FA-4b, relative-entropy face.** The relative entropy
to the uniform weight is antitone along the flow. -/
theorem relEntW_arrowFlow_antitoneOn [Nonempty V] (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) {p : V → ℝ} (hp : IsProbWeight p)
    (hpos : ∀ i, 0 < p i) :
    AntitoneOn (fun t => relEntW (arrowFlow w hsymm t p)
      (fun _ => (((Finset.univ : Finset V).card : ℝ))⁻¹)) (Set.Ici 0) := by
  intro a ha b hb hab
  show relEntW (arrowFlow w hsymm b p) (fun _ => (((Finset.univ : Finset V).card : ℝ))⁻¹)
    ≤ relEntW (arrowFlow w hsymm a p) (fun _ => (((Finset.univ : Finset V).card : ℝ))⁻¹)
  have hle : entropyW (arrowFlow w hsymm a p)
      ≤ entropyW (arrowFlow w hsymm b p) :=
    entropyW_arrowFlow_monotoneOn w hw hw0 hsymm hpos ha hb hab
  have hpa := arrowFlow_probWeight w hw hw0 hsymm ha hp
  have hpb := arrowFlow_probWeight w hw hw0 hsymm hb hp
  rw [relEntW_uniform_eq hpa, relEntW_uniform_eq hpb]
  linarith

/-- **FA-4b pin discharge.** The contingency held:
positivity is proved (K-ARR-POS did not fire), and the
entropy claim lands at the grade pinned in FA-0: the
entropy of the *normalized* evolved field is monotone —
normalization is by the evolved total, which mass
conservation identifies with the initial total. -/
theorem fa4b_pin : @FA4bPin V _ _ := by
  intro w hw hw0 hsymm
  refine ⟨fun t ht F hF i => arrowFlow_nonneg w hw hw0 hsymm ht hF i, ?_⟩
  intro F hF
  by_cases hne : Nonempty V
  · -- The total `S = ∑ j, F j` is positive and conserved.
    haveI := hne
    set S := ∑ j, F j with hSdef
    have hS : 0 < S :=
      Finset.sum_pos (fun i _ => hF i) Finset.univ_nonempty
    -- The normalized evolved field is the flow of the
    -- normalized initial field.
    have hfield : ∀ t : ℝ,
        (fun i => arrowFlow w hsymm t F i / ∑ j, arrowFlow w hsymm t F j)
          = arrowFlow w hsymm t (fun i => F i / S) := by
      intro t
      have hlin : arrowFlow w hsymm t (fun i => F i / S)
          = fun i => arrowFlow w hsymm t F i / S := by
        have h1 : (fun i => F i / S) = S⁻¹ • F := by
          funext i
          rw [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
        rw [h1, arrowFlow_smul]
        funext i
        rw [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
      rw [hlin, sum_arrowFlow w hw hsymm t F]
    have hmono := entropyW_arrowFlow_monotoneOn w hw hw0 hsymm
      (F := fun i => F i / S) (fun i => div_pos (hF i) hS)
    refine hmono.congr ?_
    intro t _
    exact congrArg entropyW (hfield t).symm
  · -- Empty seat: every entropy is `0`; the claim is trivial.
    haveI : IsEmpty V := not_nonempty_iff.mp hne
    intro a _ b _ _
    have h0 : ∀ G : V → ℝ, entropyW G = 0 := by
      intro G
      show (-∑ i, G i * Real.log (G i)) = 0
      rw [Finset.univ_eq_empty, Finset.sum_empty, neg_zero]
    show entropyW (fun i => arrowFlow w hsymm a F i / ∑ j, arrowFlow w hsymm a F j)
        ≤ entropyW (fun i => arrowFlow w hsymm b F i / ∑ j, arrowFlow w hsymm b F j)
    rw [h0, h0]

end ThetLogos
