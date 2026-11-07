import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import ThetLogos.FiniteArrowPin

open scoped InnerProductSpace

/-!
# ThetLogos.FiniteArrow — the finite arrow seat: FA-1/2/3/4a/5/6

The content bricks of the finite arrow line (scoping
`finite-arrow-scoping-2026-11-06.md`; pin `FiniteArrowPin.lean`,
FA-0, commit f706874; Jeff fired the line 2026-11-06 17:57 EST).
Working label only — naming is Jeff's.

**What is proved here, at T1.** On the TE/Bridge graph seat
(finite `V`, symmetric `w ≥ 0`), with the flow the landed
`heatOp` read on fields (`arrowFlow`, pinned at FA-0):

- **FA-1 (the Lyapunov core).** The deviation energy
  `devEnergy (θ t)` has derivative `−2 ∑ i, (L (θ t)) i ^ 2`,
  is antitone on `t ≥ 0`, and drops strictly at every `t > 0`
  iff `F ∉ ker L`. The static energy identity was landed
  (`energy_eq_half`); the monotonicity was NOT in the tree —
  the tree's `heatFlow_decay` is a norm envelope at the Fiedler
  rate, not a monotonicity statement. The proof here is the
  spectral formula: `devEnergy (θ t) = ∑ k, λₖ e^{−2λₖt} cₖ²`.
- **FA-2.** Every field converges under the flow to its
  `ker L` projection `kerProj F` — the target is `ker L`, not
  the constant field (on disconnected seats `ker L` is the
  locally-constant fields; K-ARR-EQ).
- **FA-3.** One Euler step at/below the explicit stability
  bound `τ * (2 * degSum w) ≤ 1` does not increase the
  deviation energy, strictly iff `F ∉ ker L`. The eigenvalue
  bound used is the finite Gershgorin bound `λₖ ≤ 2 * degSum w`,
  proved here from `energy_eq_half`.
- **FA-4a.** The χ²-divergence (a *divergence*, not an entropy)
  along the flow has derivative `−(2 * devEnergy (θ t))` — the
  production rate is the deviation energy, proved, not defined
  (K-ARR-FIAT shape (1) decided: it does NOT fire) — is
  antitone on `t ≥ 0`, strict iff `F ∉ ker L`.
- **FA-5 (the Loschmidt pair).** The reversed curve solves the
  anti-heat equation `Ḟ = +L F`, and its deviation energy grows
  at exactly the forward production rate, monotone on `t ≥ 0`,
  same iff locus. The reverse is provable only in the OPPOSITE
  (growth) form — K-ARR-REVERSAL's guard holds: the direction
  lives in the generator's sign plus the off-equilibrium
  hypothesis (`F ∉ ker L`, a hypothesis on the strictness
  theorems), not in the law.
- **FA-6.** The TE time course: total separated charge stays
  `0` at every time (TE-T3 at `θ(t)`, citation-grade, labeled);
  the separation's gradient energy along the flow is exactly
  `2 * devEnergy (θ t)`, so FA-1 meters its decay. No
  persistence claim for the extremal sign law is made.

**Fences.** NO CLAIM; dials 0/4; Dial 2 = 0. Nothing here is
the cosmological arrow, the Past Hypothesis (it enters only as
the hypothesis `F ∉ ker L`), a local arrow (Claim 6(b) stays
KILLED; β is global), a derivation of physical time (Claim
6(a) stays T5), a gravity object, or a response law. The flow
seat acquires no dynamics from this line (species sibling
only, scoping §3.8(d2)). "SecondArrow" is not used (K-ARR-NAME).
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Spectral workhorses -/

/-- Every eigenvalue of the graph Laplacian is nonnegative:
`λₖ` is the energy of its own eigenvector, and the energy is
nonnegative (Thomson). -/
theorem lapEig_nonneg (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) (hsymm : (lapLin w).IsSymmetric)
    (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) :
    0 ≤ lapEig w hsymm k := by
  have hnorm : ‖(lapBasis w hsymm) k‖ = 1 := (lapBasis w hsymm).orthonormal.1 k
  have hsum : ∑ i, (euclEquiv ((lapBasis w hsymm) k)) i ^ 2 = 1 := by
    have h : ∑ i, (euclEquiv ((lapBasis w hsymm) k)) i ^ 2
        = ⟪(lapBasis w hsymm) k, (lapBasis w hsymm) k⟫_ℝ := by
      rw [euclid_inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [euclEquiv_apply, sq]
    rw [h, real_inner_self_eq_norm_sq, hnorm, one_pow]
  have hE := energy_of_eigenvector w (euclEquiv ((lapBasis w hsymm) k))
    (lapEig w hsymm k) (lapEig_eq_of_basis w hsymm k)
  rw [hsum, mul_one] at hE
  rw [← hE]
  exact energy_nonneg w hw hw0 _

/-- **The spectral energy formula.** The Dirichlet energy of a
field is the eigenvalue-weighted sum of its squared spectral
coefficients: `energy w (euclEquiv x) = ∑ k, λₖ (repr x k)²`.
Assembled from `euclid_inner_apply` and Parseval
(`OrthonormalBasis.sum_inner_mul_inner`) against the landed
eigenbasis; this is the computation every brick of the line
stands on. -/
theorem energy_eq_spectral (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (x : EuclideanSpace ℝ V) :
    energy w (euclEquiv x)
      = ∑ k, lapEig w hsymm k * ((lapBasis w hsymm).repr x k) ^ 2 := by
  have h1 : energy w (euclEquiv x) = ⟪x, lapLin w x⟫_ℝ := by
    rw [energy_def, euclid_inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [euclEquiv_apply, lapLin_apply]
  rw [h1, ← (lapBasis w hsymm).sum_inner_mul_inner x (lapLin w x)]
  apply Finset.sum_congr rfl
  intro k _
  have h2 : ⟪(lapBasis w hsymm) k, lapLin w x⟫_ℝ
      = lapEig w hsymm k * ⟪(lapBasis w hsymm) k, x⟫_ℝ := by
    rw [← hsymm ((lapBasis w hsymm) k) x, lapBasis_apply_eig, inner_smul_left,
      starRingEnd_apply, star_id_of_comm]
  rw [h2, real_inner_comm ((lapBasis w hsymm) k) x,
    (lapBasis w hsymm).repr_apply_apply]
  try rw [real_inner_comm ((lapBasis w hsymm) k) x]
  ring

/-- The spectral coefficients of the flowed field are the
initial coefficients damped by `exp (−λₖ t)` — the transport of
the landed `heatOp_repr` through `arrowFlow`'s definition. -/
theorem arrowFlow_repr (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (t : ℝ) (F : V → ℝ)
    (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) :
    (lapBasis w hsymm).repr (euclEquiv.symm (arrowFlow w hsymm t F)) k
      = Real.exp (-(lapEig w hsymm k) * t)
        * (lapBasis w hsymm).repr (euclEquiv.symm F) k := by
  have h : euclEquiv.symm (arrowFlow w hsymm t F)
      = heatOp w hsymm t (euclEquiv.symm F) := by
    simp only [arrowFlow, LinearEquiv.symm_apply_apply]
  rw [h, heatOp_repr]

/-- The deviation energy is the energy outright: the energy is
already mean-invariant, because `L` kills the (constant) mean
field and the mean pairing factors through the conserved total
`∑ i, (L F) i = 0`. So `devEnergy`'s deviation-field definition
(FA-0) and the seat's `energy` are one quantity. -/
theorem devEnergy_eq_energy (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (F : V → ℝ) :
    devEnergy w F = energy w F := by
  have hmeanE : energy w (meanVec F) = 0 := by
    rw [energy_def]
    have hL : laplacianOp w (meanVec F) = 0 := laplacianOp_const w (finMean F)
    rw [hL]
    simp
  have hbilin : bilin w F (meanVec F) = 0 := by
    rw [bilin_def]
    have hterm : ∀ i : V, (meanVec F) i * laplacianOp w F i
        = finMean F * laplacianOp w F i := fun i => rfl
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum,
      sum_laplacianOp_eq_zero w hw F, mul_zero]
  have h := energy_add_smul w hw F (meanVec F) (-1)
  rw [hmeanE, hbilin] at h
  have hsub : F - meanVec F = F + (-1) • meanVec F := by
    rw [sub_eq_add_neg, neg_one_smul]
  show energy w (F - meanVec F) = energy w F
  rw [hsub]
  simpa using h

/-- **The deviation energy along the flow, spectrally** (the
Lyapunov function's closed form):
`devEnergy (θ t) = ∑ k, λₖ (e^{−λₖt} cₖ)²`. -/
theorem devEnergy_arrowFlow (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (hsymm : (lapLin w).IsSymmetric) (t : ℝ) (F : V → ℝ) :
    devEnergy w (arrowFlow w hsymm t F)
      = ∑ k, lapEig w hsymm k
          * (Real.exp (-(lapEig w hsymm k) * t)
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k) ^ 2 := by
  rw [devEnergy_eq_energy w hw]
  show energy w (euclEquiv (heatOp w hsymm t (euclEquiv.symm F))) = _
  rw [energy_eq_spectral w hsymm]
  apply Finset.sum_congr rfl
  intro k _
  rw [heatOp_repr]

/-- The squared Laplacian of the flowed field, spectrally:
`∑ i, (L (θ t)) i ^ 2 = ∑ k, λₖ² (e^{−λₖt} cₖ)²` — the
production-rate identity's right-hand side in FA-1. -/
theorem sum_sq_laplacianOp_arrowFlow (w : V → V → ℝ)
    (hsymm : (lapLin w).IsSymmetric) (t : ℝ) (F : V → ℝ) :
    ∑ i, (laplacianOp w (arrowFlow w hsymm t F)) i ^ 2
      = ∑ k, (lapEig w hsymm k) ^ 2
          * (Real.exp (-(lapEig w hsymm k) * t)
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k) ^ 2 := by
  set x := euclEquiv.symm F with hx
  have h1 : euclEquiv.symm (arrowFlow w hsymm t F) = heatOp w hsymm t x := by
    simp only [arrowFlow, hx, LinearEquiv.symm_apply_apply]
  have h2 : ∑ i, (laplacianOp w (arrowFlow w hsymm t F)) i ^ 2
      = ‖lapLin w (heatOp w hsymm t x)‖ ^ 2 := by
    have h3 : ∀ i : V, laplacianOp w (arrowFlow w hsymm t F) i
        = (lapLin w (heatOp w hsymm t x)) i := by
      intro i
      rw [← h1, lapLin_apply, LinearEquiv.apply_symm_apply]
    rw [← real_inner_self_eq_norm_sq, euclid_inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [h3 i, pow_two]
  rw [h2, ← (lapBasis w hsymm).sum_sq_norm_inner_right
    (lapLin w (heatOp w hsymm t x))]
  apply Finset.sum_congr rfl
  intro k _
  have h4 : ⟪(lapBasis w hsymm) k, lapLin w (heatOp w hsymm t x)⟫_ℝ
      = lapEig w hsymm k * (Real.exp (-(lapEig w hsymm k) * t)
        * (lapBasis w hsymm).repr x k) := by
    rw [← hsymm ((lapBasis w hsymm) k) (heatOp w hsymm t x),
      lapBasis_apply_eig, inner_smul_left, starRingEnd_apply, star_id_of_comm,
      heatOp_inner_basis, (lapBasis w hsymm).repr_apply_apply]
  rw [h4, Real.norm_eq_abs, sq_abs]
  ring

/-- The flow at `t = 0` is the identity (the transport of the
landed `heatOp_zero`). -/
theorem arrowFlow_zero (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (F : V → ℝ) :
    arrowFlow w hsymm 0 F = F := by
  simp only [arrowFlow, heatOp_zero, LinearEquiv.apply_symm_apply]

/-- The flow fixes every equilibrium field, at every time
(positive or negative): the transport of the landed
`heatOp_eq_of_lapLin_eq_zero`. -/
theorem arrowFlow_of_laplacianOp_eq_zero (w : V → V → ℝ)
    (hsymm : (lapLin w).IsSymmetric) {F : V → ℝ}
    (hF : laplacianOp w F = 0) (t : ℝ) :
    arrowFlow w hsymm t F = F := by
  have hL : lapLin w (euclEquiv.symm F) = 0 := by
    apply euclEquiv.injective
    rw [map_zero, equiv_lapLin, LinearEquiv.apply_symm_apply]
    exact hF
  simp only [arrowFlow, heatOp_eq_of_lapLin_eq_zero w hsymm t _ hL,
    LinearEquiv.apply_symm_apply]

/-- Off-equilibrium means some mode is loaded: if
`laplacianOp w F ≠ 0` then some spectral coefficient pair
`λₖ cₖ` is nonzero. -/
theorem exists_mode_of_laplacianOp_ne_zero (w : V → V → ℝ)
    (hsymm : (lapLin w).IsSymmetric) {F : V → ℝ}
    (hF : laplacianOp w F ≠ 0) :
    ∃ k, lapEig w hsymm k
        * (lapBasis w hsymm).repr (euclEquiv.symm F) k ≠ 0 := by
  by_contra h
  push_neg at h
  apply hF
  have hL : lapLin w (euclEquiv.symm F) = 0 := by
    have hsum := (lapBasis w hsymm).sum_repr (lapLin w (euclEquiv.symm F))
    rw [← hsum]
    apply Finset.sum_eq_zero
    intro k _
    have hrep : (lapBasis w hsymm).repr (lapLin w (euclEquiv.symm F)) k
        = lapEig w hsymm k
          * (lapBasis w hsymm).repr (euclEquiv.symm F) k := by
      rw [(lapBasis w hsymm).repr_apply_apply, ← hsymm ((lapBasis w hsymm) k)
        (euclEquiv.symm F), lapBasis_apply_eig, inner_smul_left,
        starRingEnd_apply, star_id_of_comm,
        (lapBasis w hsymm).repr_apply_apply]
    rw [hrep, h k, zero_smul]
  have h2 : euclEquiv (lapLin w (euclEquiv.symm F))
      = laplacianOp w F := by
    rw [equiv_lapLin, LinearEquiv.apply_symm_apply]
  rw [hL, map_zero] at h2
  exact h2.symm

/-! ## FA-1 — the Lyapunov core -/

/-- **FA-1, derivative identity.** The deviation energy along
the flow differentiates to minus twice the squared Laplacian of
the current field: `d/dt devEnergy (θ t) = −2 ∑ i, (L (θ t)) i ^ 2`.
The production rate is a *theorem about* `devEnergy`, not its
definition (K-ARR-FIAT shape (1) does not fire here). -/
theorem devEnergy_arrowFlow_hasDerivAt (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) (F : V → ℝ) (t : ℝ) :
    HasDerivAt (fun s => devEnergy w (arrowFlow w hsymm s F))
      (-2 * ∑ i, (laplacianOp w (arrowFlow w hsymm t F)) i ^ 2) t := by
  have hterm : ∀ k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V)),
      HasDerivAt (fun s => lapEig w hsymm k
          * ((Real.exp (-(lapEig w hsymm k) * s)
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k)
            * (Real.exp (-(lapEig w hsymm k) * s)
              * (lapBasis w hsymm).repr (euclEquiv.symm F) k)))
        (lapEig w hsymm k
          * (((Real.exp (-(lapEig w hsymm k) * t)
              * (-(lapEig w hsymm k)))
              * (lapBasis w hsymm).repr (euclEquiv.symm F) k)
              * (Real.exp (-(lapEig w hsymm k) * t)
                * (lapBasis w hsymm).repr (euclEquiv.symm F) k)
            + (Real.exp (-(lapEig w hsymm k) * t)
              * (lapBasis w hsymm).repr (euclEquiv.symm F) k)
              * ((Real.exp (-(lapEig w hsymm k) * t)
                * (-(lapEig w hsymm k)))
                * (lapBasis w hsymm).repr (euclEquiv.symm F) k))) t := by
    intro k
    have harg : HasDerivAt (fun s : ℝ => -(lapEig w hsymm k) * s)
        (-(lapEig w hsymm k)) t := by
      simpa using (hasDerivAt_id t).const_mul (-(lapEig w hsymm k))
    have h1 := harg.exp
    have h2 := h1.mul_const ((lapBasis w hsymm).repr (euclEquiv.symm F) k)
    have h3 := h2.mul h2
    exact h3.const_mul (lapEig w hsymm k)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => hterm k)
  have hfun : (fun s => devEnergy w (arrowFlow w hsymm s F))
      = (fun s => ∑ k, lapEig w hsymm k
          * ((Real.exp (-(lapEig w hsymm k) * s)
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k)
            * (Real.exp (-(lapEig w hsymm k) * s)
              * (lapBasis w hsymm).repr (euclEquiv.symm F) k))) := by
    funext s
    rw [devEnergy_arrowFlow w hw hsymm s F]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_two]
  have hder : (∑ k, lapEig w hsymm k
        * (((Real.exp (-(lapEig w hsymm k) * t)
            * (-(lapEig w hsymm k)))
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k)
            * (Real.exp (-(lapEig w hsymm k) * t)
              * (lapBasis w hsymm).repr (euclEquiv.symm F) k)
          + (Real.exp (-(lapEig w hsymm k) * t)
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k)
            * ((Real.exp (-(lapEig w hsymm k) * t)
              * (-(lapEig w hsymm k)))
              * (lapBasis w hsymm).repr (euclEquiv.symm F) k)))
      = -2 * ∑ i, (laplacianOp w (arrowFlow w hsymm t F)) i ^ 2 := by
    rw [sum_sq_laplacianOp_arrowFlow w hsymm t F, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [← hfun, hder] at hsum
  exact hsum

/-- **FA-1, monotonicity.** The deviation energy along the flow
is antitone on `t ≥ 0` — termwise in the spectral formula, from
`λₖ ≥ 0` and the monotonicity of `exp`. This is the statement
the tree did NOT have: `heatFlow_decay` bounds the deviation's
norm by a decaying envelope and implies no monotonicity. -/
theorem devEnergy_arrowFlow_antitoneOn (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) (F : V → ℝ) :
    AntitoneOn (fun t => devEnergy w (arrowFlow w hsymm t F)) (Set.Ici 0) := by
  intro a _ b _ hab
  show devEnergy w (arrowFlow w hsymm b F) ≤ devEnergy w (arrowFlow w hsymm a F)
  rw [devEnergy_arrowFlow w hw hsymm a F, devEnergy_arrowFlow w hw hsymm b F]
  apply Finset.sum_le_sum
  intro k _
  have hl : 0 ≤ lapEig w hsymm k := lapEig_nonneg w hw hw0 hsymm k
  have hexp : Real.exp (-(lapEig w hsymm k) * b)
      ≤ Real.exp (-(lapEig w hsymm k) * a) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hab hl
    linarith
  have hsq : (Real.exp (-(lapEig w hsymm k) * b)
        * (lapBasis w hsymm).repr (euclEquiv.symm F) k) ^ 2
      ≤ (Real.exp (-(lapEig w hsymm k) * a)
        * (lapBasis w hsymm).repr (euclEquiv.symm F) k) ^ 2 := by
    rw [mul_pow, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Real.exp_nonneg _) hexp 2) (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left hsq hl

/-- **FA-1, the equality case (K-ARR-EQ form).** At every
`t > 0`, the deviation energy has dropped strictly iff
`F ∉ ker L`. No strictness is claimed at equilibrium. -/
theorem devEnergy_arrowFlow_strict_iff (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) (F : V → ℝ) {t : ℝ} (ht : 0 < t) :
    devEnergy w (arrowFlow w hsymm t F) < devEnergy w F
      ↔ laplacianOp w F ≠ 0 := by
  constructor
  · intro hlt hLF
    rw [arrowFlow_of_laplacianOp_eq_zero w hsymm hLF t] at hlt
    exact lt_irrefl _ hlt
  · intro hLF
    obtain ⟨k₀, hk₀⟩ := exists_mode_of_laplacianOp_ne_zero w hsymm hLF
    have hl : 0 ≤ lapEig w hsymm k₀ := lapEig_nonneg w hw hw0 hsymm k₀
    have hlpos : 0 < lapEig w hsymm k₀ :=
      lt_of_le_of_ne hl (fun h => hk₀ (by simp [← h]))
    have hc : (lapBasis w hsymm).repr (euclEquiv.symm F) k₀ ≠ 0 :=
      fun h => hk₀ (by simp [h])
    have h0 : devEnergy w F
        = ∑ k, lapEig w hsymm k
            * (Real.exp (-(lapEig w hsymm k) * (0 : ℝ))
              * (lapBasis w hsymm).repr (euclEquiv.symm F) k) ^ 2 := by
      have h := devEnergy_arrowFlow w hw hsymm 0 F
      rwa [arrowFlow_zero] at h
    rw [devEnergy_arrowFlow w hw hsymm t F, h0]
    apply Finset.sum_lt_sum
    · intro k _
      have hlk : 0 ≤ lapEig w hsymm k := lapEig_nonneg w hw hw0 hsymm k
      have hexp : Real.exp (-(lapEig w hsymm k) * t)
          ≤ Real.exp (-(lapEig w hsymm k) * (0 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_left ht.le hlk
        linarith
      have hsq : (Real.exp (-(lapEig w hsymm k) * t)
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k) ^ 2
          ≤ (Real.exp (-(lapEig w hsymm k) * (0 : ℝ))
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k) ^ 2 := by
        rw [mul_pow, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (Real.exp_nonneg _) hexp 2) (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left hsq hlk
    · refine ⟨k₀, Finset.mem_univ k₀, ?_⟩
      have hexp1 : Real.exp (-(lapEig w hsymm k₀) * t) < 1 := by
        rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
        apply Real.exp_lt_exp.mpr
        have h : lapEig w hsymm k₀ * t > 0 := mul_pos hlpos ht
        linarith
      have hsq : (Real.exp (-(lapEig w hsymm k₀) * t)
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k₀) ^ 2
          < (Real.exp (-(lapEig w hsymm k₀) * (0 : ℝ))
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k₀) ^ 2 := by
        rw [mul_pow, mul_pow]
        have he0 : Real.exp (-(lapEig w hsymm k₀) * (0 : ℝ)) = 1 := by simp
        rw [he0, one_pow]
        have h1 : Real.exp (-(lapEig w hsymm k₀) * t) ^ 2 < 1 :=
          pow_lt_one₀ (Real.exp_nonneg _) hexp1 (by norm_num)
        have h2 : (0:ℝ) < ((lapBasis w hsymm).repr (euclEquiv.symm F) k₀) ^ 2 :=
          sq_pos_of_ne_zero hc
        exact mul_lt_mul_of_pos_right h1 h2
      exact mul_lt_mul_of_pos_left hsq hlpos

/-! ## FA-2 — approach to equilibrium -/

/-- The spectral coefficients of a filtered basis sum: the
`j`-th coefficient of `∑ k ∈ filter P, a k • B k` is `a j` if
`P j` holds and `0` otherwise. -/
theorem repr_filter_smul_sum (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (P : Fin (Module.finrank ℝ (EuclideanSpace ℝ V)) → Prop) [DecidablePred P]
    (a : Fin (Module.finrank ℝ (EuclideanSpace ℝ V)) → ℝ)
    (j : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) :
    (lapBasis w hsymm).repr
        (∑ k ∈ Finset.univ.filter P, a k • (lapBasis w hsymm) k) j
      = if P j then a j else 0 := by
  rw [(lapBasis w hsymm).repr_apply_apply, inner_sum]
  by_cases hj : P j
  · rw [if_pos hj]
    rw [Finset.sum_eq_single j]
    · rw [inner_smul_right,
        orthonormal_iff_ite.mp (lapBasis w hsymm).orthonormal j j, if_pos rfl,
        mul_one]
    · intro k _ hk
      rw [inner_smul_right,
        orthonormal_iff_ite.mp (lapBasis w hsymm).orthonormal j k,
        if_neg (Ne.symm hk), mul_zero]
    · intro hjmem
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩) hjmem
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : k ≠ j := by
      intro h
      rw [h] at hk
      exact hj (Finset.mem_filter.mp hk).2
    rw [inner_smul_right,
      orthonormal_iff_ite.mp (lapBasis w hsymm).orthonormal j k,
      if_neg (Ne.symm hkj), mul_zero]

/-- The kernel projection lies in the kernel. -/
theorem lapLin_kerProjE (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (x : EuclideanSpace ℝ V) :
    lapLin w (kerProjE w hsymm x) = 0 := by
  have hdef : kerProjE w hsymm x
      = ∑ k ∈ Finset.univ.filter (fun k => lapEig w hsymm k = 0),
        ((lapBasis w hsymm).repr x k) • (lapBasis w hsymm) k := rfl
  rw [hdef, map_sum]
  apply Finset.sum_eq_zero
  intro k hk
  have hk0 : lapEig w hsymm k = 0 := (Finset.mem_filter.mp hk).2
  rw [map_smul, lapBasis_apply_eig, hk0, zero_smul, smul_zero]

/-- The flow minus its kernel projection is the sum of the
nonzero modes, each damped. -/
theorem heatOp_sub_kerProjE (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (t : ℝ) (x : EuclideanSpace ℝ V) :
    heatOp w hsymm t x - kerProjE w hsymm x
      = ∑ k ∈ Finset.univ.filter (fun k => lapEig w hsymm k ≠ 0),
        (Real.exp (-(lapEig w hsymm k) * t)
          * (lapBasis w hsymm).repr x k) • (lapBasis w hsymm) k := by
  have hdef : kerProjE w hsymm x
      = ∑ k ∈ Finset.univ.filter (fun k => lapEig w hsymm k = 0),
        ((lapBasis w hsymm).repr x k) • (lapBasis w hsymm) k := rfl
  apply (lapBasis w hsymm).repr.injective
  apply PiLp.ext
  intro j
  have hker : (lapBasis w hsymm).repr (kerProjE w hsymm x) j
      = if lapEig w hsymm j = 0
        then (lapBasis w hsymm).repr x j else 0 := by
    rw [hdef]
    exact repr_filter_smul_sum w hsymm (fun k => lapEig w hsymm k = 0)
      (fun k => (lapBasis w hsymm).repr x k) j
  have hsum := repr_filter_smul_sum w hsymm (fun k => lapEig w hsymm k ≠ 0)
    (fun k => Real.exp (-(lapEig w hsymm k) * t)
      * (lapBasis w hsymm).repr x k) j
  rw [map_sub, PiLp.sub_apply, heatOp_repr, hker, hsum]
  by_cases hj : lapEig w hsymm j = 0
  · rw [if_pos hj, if_neg (fun h => h hj)]
    simp [hj]
  · rw [if_neg hj, if_pos hj, sub_zero]

/-- **FA-2, Euclidean form.** The heat flow converges to the
kernel projection: each nonzero mode's factor `exp (−λₖ t)`
tends to `0`, and the finite sum passes through the limit. -/
theorem tendsto_heatOp_kerProjE (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) (x : EuclideanSpace ℝ V) :
    Filter.Tendsto (fun t => heatOp w hsymm t x) Filter.atTop
      (nhds (kerProjE w hsymm x)) := by
  have hdiff : Filter.Tendsto
      (fun t => heatOp w hsymm t x - kerProjE w hsymm x) Filter.atTop
      (nhds 0) := by
    have hfun : (fun t => heatOp w hsymm t x - kerProjE w hsymm x)
        = (fun t => ∑ k ∈ Finset.univ.filter (fun k => lapEig w hsymm k ≠ 0),
          (Real.exp (-(lapEig w hsymm k) * t)
            * (lapBasis w hsymm).repr x k) • (lapBasis w hsymm) k) :=
      funext fun t => heatOp_sub_kerProjE w hsymm t x
    rw [hfun]
    have hterm : ∀ k ∈ Finset.univ.filter (fun k => lapEig w hsymm k ≠ 0),
        Filter.Tendsto (fun t => (Real.exp (-(lapEig w hsymm k) * t)
          * (lapBasis w hsymm).repr x k) • (lapBasis w hsymm) k)
          Filter.atTop (nhds 0) := by
      intro k hk
      have hkne : lapEig w hsymm k ≠ 0 := (Finset.mem_filter.mp hk).2
      have hl : 0 < lapEig w hsymm k :=
        lt_of_le_of_ne (lapEig_nonneg w hw hw0 hsymm k) (Ne.symm hkne)
      have hexp : Filter.Tendsto (fun t => Real.exp (-(lapEig w hsymm k) * t))
          Filter.atTop (nhds 0) := by
        have h1 : Filter.Tendsto (fun t : ℝ => (-(lapEig w hsymm k)) * t)
            Filter.atTop Filter.atBot :=
          (Filter.tendsto_const_mul_atBot_of_neg
            (show (-(lapEig w hsymm k)) < 0 by linarith)).mpr Filter.tendsto_id
        exact Real.tendsto_exp_atBot.comp h1
      have hmul := hexp.mul_const ((lapBasis w hsymm).repr x k)
      rw [zero_mul] at hmul
      have hsmul := hmul.smul_const ((lapBasis w hsymm) k)
      rwa [zero_smul] at hsmul
    have hsum := tendsto_finsetSum _ hterm
    rwa [Finset.sum_const_zero] at hsum
  have h := hdiff.add_const (kerProjE w hsymm x)
  rw [zero_add] at h
  have hfun2 : (fun t => heatOp w hsymm t x - kerProjE w hsymm x
        + kerProjE w hsymm x)
      = (fun t => heatOp w hsymm t x) :=
    funext fun t => sub_add_cancel _ _
  rwa [hfun2] at h

/-- **FA-2 (approach to equilibrium).** Every field converges
under the flow to its `ker L` projection. The target is
`ker L` — on a disconnected seat the limit is a locally
constant field, not necessarily a constant one (K-ARR-EQ). -/
theorem arrowFlow_tendsto_kerProj (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) (F : V → ℝ) :
    Filter.Tendsto (fun t => arrowFlow w hsymm t F) Filter.atTop
      (nhds (kerProj w hsymm F)) := by
  show Filter.Tendsto
    (fun t => euclEquiv (heatOp w hsymm t (euclEquiv.symm F))) Filter.atTop
    (nhds (euclEquiv (kerProjE w hsymm (euclEquiv.symm F))))
  have hcont : Continuous (euclEquiv : EuclideanSpace ℝ V → (V → ℝ)) :=
    euclEquiv.toLinearMap.continuous_of_finiteDimensional
  exact (hcont.tendsto _).comp (tendsto_heatOp_kerProjE w hw hw0 hsymm _)

/-! ## FA-3 — the discrete step -/

/-- **The finite Gershgorin bound, energy form.** For `w ≥ 0`
symmetric, every field's energy is at most `2 * degSum w` times
its squared norm: `energy w G ≤ 2 * degSum w * ∑ i, G i ^ 2`.
From `energy_eq_half` and `(a − b)² ≤ 2(a² + b²)`; the row sums
are bounded by their total `degSum w`. -/
theorem energy_le_two_degSum_mul (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j) (G : V → ℝ) :
    energy w G ≤ 2 * degSum w * ∑ i, G i ^ 2 := by
  have hds : degSum w = ∑ i, ∑ j, if j = i then 0 else w i j := rfl
  have hrow : ∀ i : V, (∑ j, if j = i then 0 else w i j) ≤ degSum w := by
    intro i
    rw [hds]
    apply Finset.single_le_sum (f := fun i => ∑ j, if j = i then 0 else w i j)
    · intro i' _
      apply Finset.sum_nonneg
      intro j _
      split_ifs with h
      · exact le_refl 0
      · exact hw0 i' j
    · exact Finset.mem_univ i
  have hbound : ∀ i j : V, (if j = i then 0 else w i j) * (G i - G j) ^ 2
      ≤ (if j = i then 0 else w i j) * (2 * (G i ^ 2 + G j ^ 2)) := by
    intro i j
    have hcoef : 0 ≤ (if j = i then 0 else w i j) := by
      split_ifs with h
      · exact le_refl 0
      · exact hw0 i j
    apply mul_le_mul_of_nonneg_left _ hcoef
    nlinarith [sq_nonneg (G i + G j)]
  have hsum1 : (∑ i, ∑ j, w i j * (G i - G j) ^ 2)
      = ∑ i, ∑ j, (if j = i then 0 else w i j) * (G i - G j) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j = i
    · rw [h]
      simp
    · rw [if_neg h]
  have hsum2 : (∑ i, ∑ j, (if j = i then 0 else w i j)
        * (2 * (G i ^ 2 + G j ^ 2)))
      = 2 * (2 * ∑ i, (∑ j, if j = i then 0 else w i j) * G i ^ 2) := by
    have hterm : ∀ i j : V, (if j = i then 0 else w i j)
          * (2 * (G i ^ 2 + G j ^ 2))
        = 2 * ((if j = i then 0 else w i j) * G i ^ 2
          + (if j = i then 0 else w i j) * G j ^ 2) := by
      intro i j
      ring
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      hterm i j))]
    have hsplit : ∀ i, (∑ j, 2 * ((if j = i then 0 else w i j) * G i ^ 2
          + (if j = i then 0 else w i j) * G j ^ 2))
        = (∑ j, 2 * ((if j = i then 0 else w i j) * G i ^ 2))
          + ∑ j, 2 * ((if j = i then 0 else w i j) * G j ^ 2) := by
      intro i
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib]
    have hrow2 : ∀ i, (∑ j, 2 * ((if j = i then 0 else w i j) * G i ^ 2))
        = 2 * ((∑ j, if j = i then 0 else w i j) * G i ^ 2) := by
      intro i
      rw [← Finset.mul_sum, ← Finset.sum_mul]
    have hA1 : (∑ i, ∑ j, 2 * ((if j = i then 0 else w i j) * G i ^ 2))
        = 2 * ∑ i, (∑ j, if j = i then 0 else w i j) * G i ^ 2 := by
      rw [Finset.sum_congr rfl (fun i _ => hrow2 i), ← Finset.mul_sum]
    have hswap2 : (∑ i, ∑ j, 2 * ((if j = i then 0 else w i j) * G j ^ 2))
        = ∑ i, ∑ j, 2 * ((if j = i then 0 else w i j) * G i ^ 2) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : a = b
      · simp [h]
      · have h' : b ≠ a := Ne.symm h
        rw [if_neg h', if_neg h, hw b a]
    rw [hA1, hswap2, hA1]
    ring
  calc energy w G
      = (1 / 2) * ∑ i, ∑ j, w i j * (G i - G j) ^ 2 := by
        rw [energy_def, energy_eq_half w hw G]
    _ = (1 / 2) * ∑ i, ∑ j, (if j = i then 0 else w i j)
          * (G i - G j) ^ 2 := by rw [hsum1]
    _ ≤ (1 / 2) * ∑ i, ∑ j, (if j = i then 0 else w i j)
          * (2 * (G i ^ 2 + G j ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact hbound i j
    _ = 2 * ∑ i, (∑ j, if j = i then 0 else w i j) * G i ^ 2 := by
        rw [hsum2]
        ring
    _ ≤ 2 * (degSum w * ∑ i, G i ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
    _ = 2 * degSum w * ∑ i, G i ^ 2 := by ring

/-- **FA-3 (the discrete arrow).** One explicit Euler step at
or below the stability bound `τ * (2 * degSum w) ≤ 1` does not
increase the deviation energy, and strictly decreases it iff
`F ∉ ker L`. The increment is exact:
`devEnergy (step F) = devEnergy F − 2τ·S + τ²·energy (L F)`
with `S = ∑ i, (L F) i ^ 2`, and `energy (L F) ≤ 2 degSum w · S`
by the Gershgorin bound. The graph seat's analogue of the
diagonal seat's landed `traceDefect_nonneg` — irreversibility
in a step, at the seat where the continuous flow also exists. -/
theorem eulerStep_devEnergy (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    {τ : ℝ} (hτ : 0 < τ) (hstab : τ * (2 * degSum w) ≤ 1) (F : V → ℝ) :
    devEnergy w (eulerStep w τ F) ≤ devEnergy w F
      ∧ (devEnergy w (eulerStep w τ F) < devEnergy w F
        ↔ laplacianOp w F ≠ 0) := by
  set S := ∑ i, (laplacianOp w F) i ^ 2 with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hE2 : energy w (laplacianOp w F) ≤ 2 * degSum w * S :=
    energy_le_two_degSum_mul w hw hw0 (laplacianOp w F)
  have hbilin : bilin w F (laplacianOp w F) = S := by
    rw [bilin_def]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_two]
  have hincr : devEnergy w (eulerStep w τ F)
      = devEnergy w F - 2 * τ * S + τ ^ 2 * energy w (laplacianOp w F) := by
    have hstep : eulerStep w τ F = F + (-τ) • laplacianOp w F := by
      show F - τ • laplacianOp w F = F + (-τ) • laplacianOp w F
      rw [sub_eq_add_neg, neg_smul]
    rw [hstep, devEnergy_eq_energy w hw, devEnergy_eq_energy w hw,
      energy_add_smul w hw F (laplacianOp w F) (-τ), hbilin]
    ring
  have hτD : τ * degSum w ≤ 1 / 2 := by linarith
  have hbound : τ ^ 2 * energy w (laplacianOp w F)
      ≤ τ ^ 2 * (2 * degSum w * S) :=
    mul_le_mul_of_nonneg_left hE2 (sq_nonneg τ)
  have hdec : -2 * τ * S + τ ^ 2 * (2 * degSum w * S)
      = 2 * τ * S * (τ * degSum w - 1) := by ring
  have hnonpos : 2 * τ * S * (τ * degSum w - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg (by norm_num) hτ.le) hSnn) (by linarith)
  constructor
  · rw [hincr]
    have h2 : -2 * τ * S + τ ^ 2 * (2 * degSum w * S) ≤ 0 := by
      rw [hdec]
      exact hnonpos
    linarith [hbound, h2]
  · constructor
    · intro hlt hLF
      have hstepF : eulerStep w τ F = F := by
        show F - τ • laplacianOp w F = F
        rw [hLF, smul_zero, sub_zero]
      rw [hstepF] at hlt
      exact lt_irrefl _ hlt
    · intro hLF
      obtain ⟨i, hi⟩ : ∃ i, laplacianOp w F i ≠ 0 := by
        by_contra h
        push_neg at h
        exact hLF (funext h)
      have hSpos : 0 < S := by
        have h1 : (laplacianOp w F) i ^ 2 ≤ S :=
          Finset.single_le_sum (f := fun i => (laplacianOp w F) i ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        have h2 : (0:ℝ) < (laplacianOp w F) i ^ 2 := sq_pos_of_ne_zero hi
        linarith
      have hstrict : -2 * τ * S + τ ^ 2 * (2 * degSum w * S) < 0 := by
        have h1 : 2 * τ * S * (τ * degSum w - 1) ≤ -(τ * S) := by
          have h2 : τ * degSum w - 1 ≤ -1 / 2 := by linarith
          have h3 : (0:ℝ) ≤ 2 * τ * S :=
            mul_nonneg (mul_nonneg (by norm_num) hτ.le) hSnn
          calc 2 * τ * S * (τ * degSum w - 1)
              ≤ 2 * τ * S * (-1 / 2) :=
                mul_le_mul_of_nonneg_left h2 h3
            _ = -(τ * S) := by ring
        have h4 : (0:ℝ) < τ * S := mul_pos hτ hSpos
        rw [hdec]
        linarith [h1, h4]
      rw [hincr]
      linarith [hbound, hstrict]

/-! ## FA-4a — production, divergence form -/

/-- The χ²-divergence along the flow, spectrally:
`chiSq (θ t) = ∑ k (λₖ ≠ 0), (e^{−λₖt} cₖ)²`. -/
theorem chiSq_arrowFlow (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (t : ℝ) (F : V → ℝ) :
    chiSq w hsymm (arrowFlow w hsymm t F)
      = ∑ k ∈ Finset.univ.filter (fun k => lapEig w hsymm k ≠ 0),
        (Real.exp (-(lapEig w hsymm k) * t)
          * (lapBasis w hsymm).repr (euclEquiv.symm F) k) ^ 2 := by
  have hdef : chiSq w hsymm (arrowFlow w hsymm t F)
      = ∑ k ∈ Finset.univ.filter (fun k => lapEig w hsymm k ≠ 0),
        ((lapBasis w hsymm).repr (euclEquiv.symm (arrowFlow w hsymm t F)) k)
          ^ 2 := rfl
  rw [hdef]
  apply Finset.sum_congr rfl
  intro k _
  rw [arrowFlow_repr]

/-- The deviation energy is the χ²-sum's weighted form: its
spectral sum may be taken over the nonzero modes alone (the
zero modes contribute `0 * _ = 0`). -/
theorem devEnergy_arrowFlow_eq_filter (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hsymm : (lapLin w).IsSymmetric)
    (t : ℝ) (F : V → ℝ) :
    devEnergy w (arrowFlow w hsymm t F)
      = ∑ k ∈ Finset.univ.filter (fun k => lapEig w hsymm k ≠ 0),
        lapEig w hsymm k
          * (Real.exp (-(lapEig w hsymm k) * t)
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k) ^ 2 := by
  rw [devEnergy_arrowFlow w hw hsymm t F]
  have hnot : ∑ k ∈ Finset.univ.filter
        (fun k => ¬ lapEig w hsymm k ≠ 0),
      lapEig w hsymm k
        * (Real.exp (-(lapEig w hsymm k) * t)
          * (lapBasis w hsymm).repr (euclEquiv.symm F) k) ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk0 : lapEig w hsymm k = 0 :=
      not_ne_iff.mp (Finset.mem_filter.mp hk).2
    rw [hk0]
    ring
  calc ∑ k, lapEig w hsymm k
        * (Real.exp (-(lapEig w hsymm k) * t)
          * (lapBasis w hsymm).repr (euclEquiv.symm F) k) ^ 2
      = (∑ k ∈ Finset.univ.filter (fun k => lapEig w hsymm k ≠ 0),
          lapEig w hsymm k
            * (Real.exp (-(lapEig w hsymm k) * t)
              * (lapBasis w hsymm).repr (euclEquiv.symm F) k) ^ 2)
        + ∑ k ∈ Finset.univ.filter (fun k => ¬ lapEig w hsymm k ≠ 0),
          lapEig w hsymm k
            * (Real.exp (-(lapEig w hsymm k) * t)
              * (lapBasis w hsymm).repr (euclEquiv.symm F) k) ^ 2 :=
        (Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun k => lapEig w hsymm k ≠ 0) _).symm
    _ = ∑ k ∈ Finset.univ.filter (fun k => lapEig w hsymm k ≠ 0),
          lapEig w hsymm k
            * (Real.exp (-(lapEig w hsymm k) * t)
              * (lapBasis w hsymm).repr (euclEquiv.symm F) k) ^ 2 := by
        rw [hnot, add_zero]

/-- **FA-4a, production rate.** The χ²-divergence along the
flow has derivative `−(2 * devEnergy (θ t))`: the production
rate of the divergence IS the deviation energy of the current
field. This is a theorem, not a definition — the divergence
was defined at FA-0 as a mode sum, with no reference to decay
(K-ARR-FIAT shape (1) decided: it does not fire). χ² is a
divergence, not an entropy, here and on every face. -/
theorem chiSq_arrowFlow_hasDerivAt (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) (F : V → ℝ) (t : ℝ) :
    HasDerivAt (fun s => chiSq w hsymm (arrowFlow w hsymm s F))
      (-(2 * devEnergy w (arrowFlow w hsymm t F))) t := by
  have hterm : ∀ k ∈ Finset.univ.filter (fun k => lapEig w hsymm k ≠ 0),
      HasDerivAt (fun s => (Real.exp (-(lapEig w hsymm k) * s)
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k)
          * (Real.exp (-(lapEig w hsymm k) * s)
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k))
        (((Real.exp (-(lapEig w hsymm k) * t) * (-(lapEig w hsymm k)))
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k)
          * (Real.exp (-(lapEig w hsymm k) * t)
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k)
          + (Real.exp (-(lapEig w hsymm k) * t)
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k)
            * ((Real.exp (-(lapEig w hsymm k) * t) * (-(lapEig w hsymm k)))
              * (lapBasis w hsymm).repr (euclEquiv.symm F) k)) t := by
    intro k _
    have harg : HasDerivAt (fun s : ℝ => -(lapEig w hsymm k) * s)
        (-(lapEig w hsymm k)) t := by
      simpa using (hasDerivAt_id t).const_mul (-(lapEig w hsymm k))
    have h1 := harg.exp
    have h2 := h1.mul_const ((lapBasis w hsymm).repr (euclEquiv.symm F) k)
    exact h2.mul h2
  have hsum := HasDerivAt.fun_sum
    (u := Finset.univ.filter (fun k => lapEig w hsymm k ≠ 0)) hterm
  have hfun : (fun s => chiSq w hsymm (arrowFlow w hsymm s F))
      = (fun s => ∑ k ∈ Finset.univ.filter (fun k => lapEig w hsymm k ≠ 0),
          (Real.exp (-(lapEig w hsymm k) * s)
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k)
          * (Real.exp (-(lapEig w hsymm k) * s)
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k)) := by
    funext s
    rw [chiSq_arrowFlow w hsymm s F]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_two]
  have hder : (∑ k ∈ Finset.univ.filter (fun k => lapEig w hsymm k ≠ 0),
        (((Real.exp (-(lapEig w hsymm k) * t) * (-(lapEig w hsymm k)))
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k)
          * (Real.exp (-(lapEig w hsymm k) * t)
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k)
          + (Real.exp (-(lapEig w hsymm k) * t)
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k)
            * ((Real.exp (-(lapEig w hsymm k) * t) * (-(lapEig w hsymm k)))
              * (lapBasis w hsymm).repr (euclEquiv.symm F) k)))
      = -(2 * devEnergy w (arrowFlow w hsymm t F)) := by
    rw [devEnergy_arrowFlow_eq_filter w hw hsymm t F, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [← hfun, hder] at hsum
  exact hsum

/-- **FA-4a, monotonicity.** The χ²-divergence along the flow
is antitone on `t ≥ 0`. -/
theorem chiSq_arrowFlow_antitoneOn (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) (F : V → ℝ) :
    AntitoneOn (fun t => chiSq w hsymm (arrowFlow w hsymm t F)) (Set.Ici 0) := by
  intro a _ b _ hab
  show chiSq w hsymm (arrowFlow w hsymm b F) ≤ chiSq w hsymm (arrowFlow w hsymm a F)
  rw [chiSq_arrowFlow w hsymm a F, chiSq_arrowFlow w hsymm b F]
  apply Finset.sum_le_sum
  intro k hk
  have hl : 0 ≤ lapEig w hsymm k := lapEig_nonneg w hw hw0 hsymm k
  have hexp : Real.exp (-(lapEig w hsymm k) * b)
      ≤ Real.exp (-(lapEig w hsymm k) * a) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hab hl
    linarith
  rw [mul_pow, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Real.exp_nonneg _) hexp 2) (sq_nonneg _)

/-- **FA-4a, the equality case.** At every `t > 0`, the
χ²-divergence has dropped strictly iff `F ∉ ker L`. -/
theorem chiSq_arrowFlow_strict_iff (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) (F : V → ℝ) {t : ℝ} (ht : 0 < t) :
    chiSq w hsymm (arrowFlow w hsymm t F) < chiSq w hsymm F
      ↔ laplacianOp w F ≠ 0 := by
  constructor
  · intro hlt hLF
    rw [arrowFlow_of_laplacianOp_eq_zero w hsymm hLF t] at hlt
    exact lt_irrefl _ hlt
  · intro hLF
    obtain ⟨k₀, hk₀⟩ := exists_mode_of_laplacianOp_ne_zero w hsymm hLF
    have hl : 0 ≤ lapEig w hsymm k₀ := lapEig_nonneg w hw hw0 hsymm k₀
    have hlpos : 0 < lapEig w hsymm k₀ :=
      lt_of_le_of_ne hl (fun h => hk₀ (by simp [← h]))
    have hc : (lapBasis w hsymm).repr (euclEquiv.symm F) k₀ ≠ 0 :=
      fun h => hk₀ (by simp [h])
    have hk₀mem : k₀ ∈ Finset.univ.filter (fun k => lapEig w hsymm k ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ k₀, ne_of_gt hlpos⟩
    have h0 : chiSq w hsymm F
        = ∑ k ∈ Finset.univ.filter (fun k => lapEig w hsymm k ≠ 0),
          (Real.exp (-(lapEig w hsymm k) * (0 : ℝ))
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k) ^ 2 := by
      have h := chiSq_arrowFlow w hsymm 0 F
      rwa [arrowFlow_zero] at h
    rw [chiSq_arrowFlow w hsymm t F, h0]
    apply Finset.sum_lt_sum
    · intro k _
      have hlk : 0 ≤ lapEig w hsymm k := lapEig_nonneg w hw hw0 hsymm k
      have hexp : Real.exp (-(lapEig w hsymm k) * t)
          ≤ Real.exp (-(lapEig w hsymm k) * (0 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_left ht.le hlk
        linarith
      rw [mul_pow, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Real.exp_nonneg _) hexp 2) (sq_nonneg _)
    · refine ⟨k₀, hk₀mem, ?_⟩
      have hexp1 : Real.exp (-(lapEig w hsymm k₀) * t) < 1 := by
        rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
        apply Real.exp_lt_exp.mpr
        have h : lapEig w hsymm k₀ * t > 0 := mul_pos hlpos ht
        linarith
      rw [mul_pow, mul_pow]
      have he0 : Real.exp (-(lapEig w hsymm k₀) * (0 : ℝ)) = 1 := by simp
      rw [he0, one_pow]
      have h1 : Real.exp (-(lapEig w hsymm k₀) * t) ^ 2 < 1 :=
        pow_lt_one₀ (Real.exp_nonneg _) hexp1 (by norm_num)
      have h2 : (0:ℝ) < ((lapBasis w hsymm).repr (euclEquiv.symm F) k₀) ^ 2 :=
        sq_pos_of_ne_zero hc
      exact mul_lt_mul_of_pos_right h1 h2

/-! ## FA-5 — the Loschmidt pair -/

/-- **FA-5(a).** The reversed curve solves the anti-heat
equation: `d/ds (θ (−s)) = +L (θ (−s))`. The same law, read
backwards, is a growth equation — the seat's law itself
prefers no direction. Proved by transporting the landed
`heatFlow_hasDerivAt` through time negation and `euclEquiv`
(as a continuous linear map). -/
theorem arrowFlow_neg_hasDerivAt (w : V → V → ℝ)
    (hsymm : (lapLin w).IsSymmetric) (F : V → ℝ) (t : ℝ) :
    HasDerivAt (fun s => arrowFlow w hsymm (-s) F)
      (laplacianOp w (arrowFlow w hsymm (-t) F)) t := by
  have h1 : HasDerivAt (fun s => heatOp w hsymm (-s) (euclEquiv.symm F))
      (lapLin w (heatOp w hsymm (-t) (euclEquiv.symm F))) t := by
    have hcomp : HasDerivAt (fun s => heatOp w hsymm (-s) (euclEquiv.symm F))
        ((-1 : ℝ) • (-(lapLin w (heatOp w hsymm (-t) (euclEquiv.symm F))))) t :=
      (heatFlow_hasDerivAt w hsymm (euclEquiv.symm F) (-t)).scomp t
        (hasDerivAt_neg t)
    simpa using hcomp
  let cle : EuclideanSpace ℝ V →L[ℝ] (V → ℝ) :=
    { toLinearMap := euclEquiv.toLinearMap
      cont := euclEquiv.toLinearMap.continuous_of_finiteDimensional }
  have h2 := cle.hasFDerivAt.comp_hasDerivAt t h1
  exact h2

/-- **FA-5(b).** The deviation energy of the reversed curve
has derivative `+2 ∑ i, (L (θ (−t))) i ^ 2` — the forward
production rate, with the opposite sign. The reverse is
provable only in this growth form, never in the decaying
form of FA-1: that asymmetry of *form* is the arrow
(K-ARR-REVERSAL's guard). -/
theorem devEnergy_arrowFlow_neg_hasDerivAt (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) (F : V → ℝ) (t : ℝ) :
    HasDerivAt (fun s => devEnergy w (arrowFlow w hsymm (-s) F))
      (2 * ∑ i, (laplacianOp w (arrowFlow w hsymm (-t) F)) i ^ 2) t := by
  have hcomp : HasDerivAt (fun s => devEnergy w (arrowFlow w hsymm (-s) F))
      ((-2 * ∑ i, (laplacianOp w (arrowFlow w hsymm (-t) F)) i ^ 2) * -1) t :=
    (devEnergy_arrowFlow_hasDerivAt w hw hw0 hsymm F (-t)).comp t
      (hasDerivAt_neg t)
  convert hcomp using 1
  ring

/-- **FA-5(c).** The deviation energy of the reversed curve is
monotone (growing) on `t ≥ 0`. -/
theorem devEnergy_arrowFlow_neg_monotoneOn (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) (F : V → ℝ) :
    MonotoneOn (fun t => devEnergy w (arrowFlow w hsymm (-t) F)) (Set.Ici 0) := by
  intro a _ b _ hab
  show devEnergy w (arrowFlow w hsymm (-a) F)
    ≤ devEnergy w (arrowFlow w hsymm (-b) F)
  rw [devEnergy_arrowFlow w hw hsymm (-a) F, devEnergy_arrowFlow w hw hsymm (-b) F]
  apply Finset.sum_le_sum
  intro k _
  have hl : 0 ≤ lapEig w hsymm k := lapEig_nonneg w hw hw0 hsymm k
  have hexp : Real.exp (-(lapEig w hsymm k) * (-a))
      ≤ Real.exp (-(lapEig w hsymm k) * (-b)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hab hl
    linarith
  have hsq : (Real.exp (-(lapEig w hsymm k) * (-a))
        * (lapBasis w hsymm).repr (euclEquiv.symm F) k) ^ 2
      ≤ (Real.exp (-(lapEig w hsymm k) * (-b))
        * (lapBasis w hsymm).repr (euclEquiv.symm F) k) ^ 2 := by
    rw [mul_pow, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Real.exp_nonneg _) hexp 2) (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left hsq hl

/-- **FA-5(d).** At every `t > 0`, the reversed curve's
deviation energy has grown strictly iff `F ∉ ker L` — the
same locus as FA-1, in the opposite direction. -/
theorem devEnergy_arrowFlow_neg_strict_iff (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) (F : V → ℝ) {t : ℝ} (ht : 0 < t) :
    devEnergy w F < devEnergy w (arrowFlow w hsymm (-t) F)
      ↔ laplacianOp w F ≠ 0 := by
  constructor
  · intro hlt hLF
    rw [arrowFlow_of_laplacianOp_eq_zero w hsymm hLF (-t)] at hlt
    exact lt_irrefl _ hlt
  · intro hLF
    obtain ⟨k₀, hk₀⟩ := exists_mode_of_laplacianOp_ne_zero w hsymm hLF
    have hl : 0 ≤ lapEig w hsymm k₀ := lapEig_nonneg w hw hw0 hsymm k₀
    have hlpos : 0 < lapEig w hsymm k₀ :=
      lt_of_le_of_ne hl (fun h => hk₀ (by simp [← h]))
    have hc : (lapBasis w hsymm).repr (euclEquiv.symm F) k₀ ≠ 0 :=
      fun h => hk₀ (by simp [h])
    have h0 : devEnergy w F
        = ∑ k, lapEig w hsymm k
            * (Real.exp (-(lapEig w hsymm k) * (0 : ℝ))
              * (lapBasis w hsymm).repr (euclEquiv.symm F) k) ^ 2 := by
      have h := devEnergy_arrowFlow w hw hsymm 0 F
      rwa [arrowFlow_zero] at h
    rw [h0, devEnergy_arrowFlow w hw hsymm (-t) F]
    apply Finset.sum_lt_sum
    · intro k _
      have hlk : 0 ≤ lapEig w hsymm k := lapEig_nonneg w hw hw0 hsymm k
      have hexp : Real.exp (-(lapEig w hsymm k) * (0 : ℝ))
          ≤ Real.exp (-(lapEig w hsymm k) * (-t)) := by
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_left ht.le hlk
        linarith
      have hsq : (Real.exp (-(lapEig w hsymm k) * (0 : ℝ))
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k) ^ 2
          ≤ (Real.exp (-(lapEig w hsymm k) * (-t))
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k) ^ 2 := by
        rw [mul_pow, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (Real.exp_nonneg _) hexp 2) (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left hsq hlk
    · refine ⟨k₀, Finset.mem_univ k₀, ?_⟩
      have hexp1 : (1:ℝ) < Real.exp (-(lapEig w hsymm k₀) * (-t)) := by
        rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
        apply Real.exp_lt_exp.mpr
        have h : lapEig w hsymm k₀ * t > 0 := mul_pos hlpos ht
        linarith
      have hsq : (Real.exp (-(lapEig w hsymm k₀) * (0 : ℝ))
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k₀) ^ 2
          < (Real.exp (-(lapEig w hsymm k₀) * (-t))
            * (lapBasis w hsymm).repr (euclEquiv.symm F) k₀) ^ 2 := by
        rw [mul_pow, mul_pow]
        have he0 : Real.exp (-(lapEig w hsymm k₀) * (0 : ℝ)) = 1 := by simp
        rw [he0, one_pow]
        have h1 : (1:ℝ) < Real.exp (-(lapEig w hsymm k₀) * (-t)) ^ 2 :=
          one_lt_pow₀ hexp1 (by norm_num)
        have h2 : (0:ℝ) < ((lapBasis w hsymm).repr (euclEquiv.symm F) k₀) ^ 2 :=
          sq_pos_of_ne_zero hc
        exact mul_lt_mul_of_pos_right h1 h2
      exact mul_lt_mul_of_pos_left hsq hlpos

/-! ## FA-6 — the TE time course -/

/-- **FA-6(a) (citation-grade, labeled).** Total separated
charge stays `0` at every time along the flow: TE-T3
(`teCharge_sum_eq_zero`) evaluated at `θ(t)`. No new content
is claimed for this clause. -/
theorem teCharge_sum_arrowFlow (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hsymm : (lapLin w).IsSymmetric)
    (θ : V → ℝ) (t : ℝ) :
    ∑ i, teCharge w (arrowFlow w hsymm t θ) i = 0 := by
  by_cases hne : Nonempty V
  · haveI := hne
    exact teCharge_sum_eq_zero w hw (arrowFlow w hsymm t θ)
  · haveI : IsEmpty V := not_nonempty_iff.mp hne
    rw [Finset.univ_eq_empty, Finset.sum_empty]

/-- **FA-6(b).** The thermoelectric separation's gradient
energy is exactly twice the deviation energy, at every field —
so along the flow, FA-1's decaying quantity IS the separation's
meter (with the seat's factor of 2). An identity of the two
landed conventions (`teGradEnergy` is the ordered double sum;
`energy_eq_half`), read through `devEnergy_eq_energy`. -/
theorem teGradEnergy_eq_two_devEnergy (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (G : V → ℝ) :
    teGradEnergy w G = 2 * devEnergy w G := by
  have h1 : teGradEnergy w G
      = 2 * (∑ i, G i * laplacianOp w G i) := by
    show (∑ i, ∑ j, w i j * (G i - G j) ^ 2)
      = 2 * (∑ i, G i * laplacianOp w G i)
    rw [energy_eq_half w hw G]
    ring
  rw [h1, ← energy_def, ← devEnergy_eq_energy w hw]

/-- **FA-6(c).** The separation's gradient energy along the
flow is antitone on `t ≥ 0` — the time course of the TE seat's
separation, metered by FA-1. (The extremal sign law TE-T2
persists only while the extremal configuration persists; no
persistence claim is made — the honest statement is this
decay of the metering quantity.) -/
theorem teGradEnergy_arrowFlow_antitoneOn (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) (θ : V → ℝ) :
    AntitoneOn (fun t => teGradEnergy w (arrowFlow w hsymm t θ)) (Set.Ici 0) := by
  intro a ha b hb hab
  show teGradEnergy w (arrowFlow w hsymm b θ)
    ≤ teGradEnergy w (arrowFlow w hsymm a θ)
  rw [teGradEnergy_eq_two_devEnergy w hw, teGradEnergy_eq_two_devEnergy w hw]
  exact mul_le_mul_of_nonneg_left
    (devEnergy_arrowFlow_antitoneOn w hw hw0 hsymm θ ha hb hab) (by norm_num)

/-! ## Pin discharges (FA-0 forms, proved) -/

theorem fa1_pin : @FA1Pin V _ _ :=
  fun w hw hw0 hsymm F => ⟨fun t => devEnergy_arrowFlow_hasDerivAt w hw hw0 hsymm F t,
    devEnergy_arrowFlow_antitoneOn w hw hw0 hsymm F,
    fun t ht => devEnergy_arrowFlow_strict_iff w hw hw0 hsymm F ht⟩

theorem fa2_pin : @FA2Pin V _ _ :=
  fun w hw hw0 hsymm F => arrowFlow_tendsto_kerProj w hw hw0 hsymm F

theorem fa3_pin : @FA3Pin V _ _ :=
  fun w hw hw0 τ hτ hstab F => eulerStep_devEnergy w hw hw0 hτ hstab F

theorem fa4a_pin : @FA4aPin V _ _ :=
  fun w hw hw0 hsymm F => ⟨fun t => chiSq_arrowFlow_hasDerivAt w hw hw0 hsymm F t,
    chiSq_arrowFlow_antitoneOn w hw hw0 hsymm F,
    fun t ht => chiSq_arrowFlow_strict_iff w hw hw0 hsymm F ht⟩

theorem fa5_pin : @FA5Pin V _ _ :=
  fun w hw hw0 hsymm F => ⟨fun t => arrowFlow_neg_hasDerivAt w hsymm F t,
    fun t => devEnergy_arrowFlow_neg_hasDerivAt w hw hw0 hsymm F t,
    devEnergy_arrowFlow_neg_monotoneOn w hw hw0 hsymm F,
    fun t ht => devEnergy_arrowFlow_neg_strict_iff w hw hw0 hsymm F ht⟩

theorem fa6_pin : @FA6Pin V _ _ :=
  fun w hw hw0 hsymm θ => ⟨fun t => teCharge_sum_arrowFlow w hw hsymm θ t,
    fun t => teGradEnergy_eq_two_devEnergy w hw (arrowFlow w hsymm t θ),
    teGradEnergy_arrowFlow_antitoneOn w hw hw0 hsymm θ⟩

end ThetLogos
