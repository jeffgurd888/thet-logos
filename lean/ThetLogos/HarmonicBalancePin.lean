import Mathlib.Tactic
import ThetLogos.FiniteEntropy
import ThetLogos.ModularVariance
import ThetLogos.IdensityCoincidence
import ThetLogos.LeibnizGibbsBridgePin

/-!
# ThetLogos.HarmonicBalancePin — harmonic balance, in finite form

**Lane-grade pin. NO CLAIM. Pre-registered DIAL-INELIGIBLE; dials 0/4
under every outcome. Dial 2 = 0: nothing here is gravity; balance of
temperatures is not a force.**

Commissioned: Zero, 2026-11-20 10:18 EST ("yes"), from his seeing of
2026-11-20 10:14 EST — "we are out of equilibrium and beend to find
our harmonic balance" — spoken over the Bergson drop. Scope of
record: `harmonic-balance-pin-scope-2026-11-20.md` (T5 scope). The
Bergson thread stays philosophy on its own shelf; no theorem here
cites it as content. Working label only — Zero names.

## What already stands (not re-proved)

The static balance condition is census: two Gibbs systems combine
into one joint Gibbs state only at a SHARED `β`
(`LeibnizGibbsBridgePin`), and a Gibbs state sees its mass and
temperature only through `β · m` (`MassGibbsPin`). This pin is the
missing half: balance as an APPROACH — how two unbalanced families
get to the shared `β`, and what stops them short of it.

## The object and the step (definitions on the face)

Two finite Gibbs families: seats `X`, `Y`, energies `E₁ : X → ℝ`,
`E₂ : Y → ℝ`, at inverse temperatures `β₁`, `β₂`. Total entropy is
the sum of the two Gibbs entropies, `entropyW (gibbsProb Eᵢ βᵢ)`
(the Boltzmann–Shannon functional of `FiniteEntropy` /
`BoltzmannShannonPin`). The **exchange step** is the defined
energy-conserving equilibration

    (β₁, β₂) ↦ (β*, β*),

where `β*` is the common inverse temperature with the same total
mean energy: `⟨E₁⟩_{β*} + ⟨E₂⟩_{β*} = ⟨E₁⟩_{β₁} + ⟨E₂⟩_{β₂}`. The
transferred quantum is `δ = ⟨E₁⟩_{β₁} − ⟨E₁⟩_{β*}` — what family 1
hands over is exactly what family 2 receives. `β*` exists always
(HB-1, intermediate value theorem on the total mean energy) and is
unique when at least one family carries a genuine energy gap. The
step is a defined finite operation, not physical time evolution;
no continuum limit and no thermalization rate is claimed.

The faithful-reading fences, on the face:

- **Nondegeneracy.** The strict/equality dichotomies of HB-1/HB-2
  carry the hypothesis that each family has a genuine gap
  (`∃ i j, E i ≠ E j`). A family with all levels equal has the same
  Gibbs state at every `β` — it has no temperature to balance, and
  the dichotomy is false for it. The hypothesis is stated, never
  hidden.
- **HB-3 is a separate, discrete seat.** The overshoot phenomenon
  is a discreteness phenomenon: on a seat where energy comes in
  indivisible quanta, the full-imbalance step jumps past balance.
  HB-3 builds that seat on its own terms (an entropy function on
  quantum counts) and does not pretend it is the Gibbs seat of
  HB-1/HB-2.

## Kills armed (pre-registered in the scope)

- **K-HB-OSCILLATE** — the undamped full-imbalance step never
  rests (period-2 countermodel, HB-3). Firing is a result.
- **K-HB-DUP** — any brick collapsing to the already-proved static
  shared-`β` theorem is a costume. The approach content (variational
  principle, existence of the balance point, entropy monotonicity,
  oscillation) is what counts as new; the one transport statement
  (HB-2) is labeled transport and cites its dyadic instance.
- **K-HB-VACUOUS** — if the exchange step cannot move on any seat,
  the pin is vacuous. It can: HB-1's step moves every unbalanced
  pair (HB-2: it rests exactly at `β₁ = β₂`), and HB-3's greedy
  step moves on the exhibit. The kill does not fire.
-/

namespace ThetLogos

-- ============================================================================
-- HB-1 (machinery). The variational principle for the finite Gibbs state
-- ============================================================================

/-- **The Gibbs variational principle** (proved): among all
strictly positive probability weights `w` on a finite seat, the
Gibbs state at `β` maximizes the entropy at fixed mean energy —
equivalently, every `w` satisfies

    `entropyW w ≤ log Z(E, β) + β · ⟨E⟩_w`.

Route: the pointwise inequality `log t ≤ t − 1` applied to
`t = p i / w i` (the Kullback–Leibler argument in finite form),
summed against `w`; both states are strictly positive, so no
support convention is hidden. This is the engine of the approach:
it is NOT on the census shelf (the shelf owns the uniform
saturation `entropyW_eq_log_card_iff`, a different statement). -/
theorem variational_gibbs_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (E : ι → ℝ) (β : ℝ) (w : ι → ℝ) (hw : IsProbWeight w)
    (hwpos : ∀ i, 0 < w i) :
    entropyW w ≤ Real.log (ModularVariance.partSum E β)
      + β * ∑ i, w i * E i := by
  have hZ : ModularVariance.partSum E β ≠ 0 :=
    ModularVariance.partSum_ne_zero E β
  have hlogp : ∀ i, Real.log (ModularVariance.gibbsProb E β i)
      = -(β * E i) - Real.log (ModularVariance.partSum E β) := by
    intro i
    rw [ModularVariance.gibbsProb,
      Real.log_div (Real.exp_ne_zero _) hZ, Real.log_exp]
  have hpt : ∀ i, w i * Real.log (ModularVariance.gibbsProb E β i)
        - w i * Real.log (w i)
      ≤ ModularVariance.gibbsProb E β i - w i := by
    intro i
    have hp : 0 < ModularVariance.gibbsProb E β i :=
      ModularVariance.gibbsProb_pos E β i
    have hwi : 0 < w i := hwpos i
    have h1 : Real.log (ModularVariance.gibbsProb E β i / w i)
        ≤ ModularVariance.gibbsProb E β i / w i - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hp hwi)
    rw [Real.log_div (ne_of_gt hp) (ne_of_gt hwi)] at h1
    have h2 : w i * (Real.log (ModularVariance.gibbsProb E β i)
          - Real.log (w i))
        ≤ w i * (ModularVariance.gibbsProb E β i / w i - 1) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hwi)
    have h3 : w i * (ModularVariance.gibbsProb E β i / w i - 1)
        = ModularVariance.gibbsProb E β i - w i := by
      rw [mul_sub, mul_one, mul_div_assoc',
        mul_div_cancel_left₀ _ (ne_of_gt hwi)]
    have h4 : w i * Real.log (ModularVariance.gibbsProb E β i)
          - w i * Real.log (w i)
        = w i * (Real.log (ModularVariance.gibbsProb E β i)
          - Real.log (w i)) := by ring
    rw [h4]
    exact le_trans h2 (le_of_eq h3)
  have hsum : ∑ i, (w i * Real.log (ModularVariance.gibbsProb E β i)
        - w i * Real.log (w i))
      ≤ ∑ i, (ModularVariance.gibbsProb E β i - w i) :=
    Finset.sum_le_sum (fun i _ => hpt i)
  have hRHS : (∑ i, (ModularVariance.gibbsProb E β i - w i)) = 0 := by
    rw [Finset.sum_sub_distrib, ModularVariance.sum_gibbsProb, hw.2,
      sub_self]
  have hLHS : (∑ i, (w i * Real.log (ModularVariance.gibbsProb E β i)
        - w i * Real.log (w i)))
      = (∑ i, w i * Real.log (ModularVariance.gibbsProb E β i))
        - ∑ i, w i * Real.log (w i) :=
    Finset.sum_sub_distrib ..
  rw [hLHS, hRHS] at hsum
  have hA : (∑ i, w i * Real.log (ModularVariance.gibbsProb E β i))
      = -β * (∑ i, w i * E i)
        - Real.log (ModularVariance.partSum E β) := by
    have hterm : ∀ i, w i * Real.log (ModularVariance.gibbsProb E β i)
        = -β * (w i * E i)
          - Real.log (ModularVariance.partSum E β) * w i := by
      intro i
      rw [hlogp i]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i),
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hw.2, mul_one]
  rw [hA] at hsum
  unfold entropyW
  linarith

/-- **The equality case of the variational principle** (proved):
equality holds exactly for the Gibbs state itself. Route: under
equality the deficit sum vanishes; each deficit is
`w i · ((p i / w i − 1) − log (p i / w i)) ≥ 0`, and the strict
inequality `log t < t − 1` off `t = 1` forces `p i = w i` at every
site. The converse is the census β-form of the Gibbs entropy
(`entropyW_gibbsProb_eq_beta_form`, cited). -/
theorem variational_gibbs_eq_iff {ι : Type*} [Fintype ι] [Nonempty ι]
    (E : ι → ℝ) (β : ℝ) (w : ι → ℝ) (hw : IsProbWeight w)
    (hwpos : ∀ i, 0 < w i) :
    entropyW w = Real.log (ModularVariance.partSum E β)
        + β * ∑ i, w i * E i
      ↔ w = ModularVariance.gibbsProb E β := by
  constructor
  · intro heq
    have hZ : ModularVariance.partSum E β ≠ 0 :=
      ModularVariance.partSum_ne_zero E β
    have hlogp : ∀ i, Real.log (ModularVariance.gibbsProb E β i)
        = -(β * E i) - Real.log (ModularVariance.partSum E β) := by
      intro i
      rw [ModularVariance.gibbsProb,
        Real.log_div (Real.exp_ne_zero _) hZ, Real.log_exp]
    have hA : (∑ i, w i * Real.log (ModularVariance.gibbsProb E β i))
        = -β * (∑ i, w i * E i)
          - Real.log (ModularVariance.partSum E β) := by
      have hterm : ∀ i, w i * Real.log (ModularVariance.gibbsProb E β i)
          = -β * (w i * E i)
            - Real.log (ModularVariance.partSum E β) * w i := by
        intro i
        rw [hlogp i]
        ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i),
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        hw.2, mul_one]
    -- Under `heq`, the total deficit is zero.
    have hdef : ∀ i, (0:ℝ) ≤ (ModularVariance.gibbsProb E β i - w i)
        - (w i * Real.log (ModularVariance.gibbsProb E β i)
          - w i * Real.log (w i)) := by
      intro i
      have hp : 0 < ModularVariance.gibbsProb E β i :=
        ModularVariance.gibbsProb_pos E β i
      have hwi : 0 < w i := hwpos i
      have h1 : Real.log (ModularVariance.gibbsProb E β i / w i)
          ≤ ModularVariance.gibbsProb E β i / w i - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hp hwi)
      rw [Real.log_div (ne_of_gt hp) (ne_of_gt hwi)] at h1
      have h2 : w i * (Real.log (ModularVariance.gibbsProb E β i)
            - Real.log (w i))
          ≤ w i * (ModularVariance.gibbsProb E β i / w i - 1) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hwi)
      have h3 : w i * (ModularVariance.gibbsProb E β i / w i - 1)
          = ModularVariance.gibbsProb E β i - w i := by
        rw [mul_sub, mul_one, mul_div_assoc',
          mul_div_cancel_left₀ _ (ne_of_gt hwi)]
      have h4 : w i * Real.log (ModularVariance.gibbsProb E β i)
            - w i * Real.log (w i)
          = w i * (Real.log (ModularVariance.gibbsProb E β i)
            - Real.log (w i)) := by ring
      rw [h4]
      linarith
    have hsumA : (∑ i, (ModularVariance.gibbsProb E β i - w i))
        = 0 := by
      rw [Finset.sum_sub_distrib, ModularVariance.sum_gibbsProb,
        hw.2, sub_self]
    have hsumB : (∑ i, (w i * Real.log (ModularVariance.gibbsProb E β i)
          - w i * Real.log (w i)))
        = (∑ i, w i * Real.log (ModularVariance.gibbsProb E β i))
          - ∑ i, w i * Real.log (w i) :=
      Finset.sum_sub_distrib ..
    have hsum0 : ∑ i, ((ModularVariance.gibbsProb E β i - w i)
        - (w i * Real.log (ModularVariance.gibbsProb E β i)
          - w i * Real.log (w i))) = 0 := by
      rw [Finset.sum_sub_distrib, hsumA, hsumB, hA]
      unfold entropyW at heq
      linarith
    have hzero : ∀ i, (ModularVariance.gibbsProb E β i - w i)
        - (w i * Real.log (ModularVariance.gibbsProb E β i)
          - w i * Real.log (w i)) = 0 := by
      have h := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => hdef i)).mp hsum0
      exact fun i => h i (Finset.mem_univ i)
    funext i
    have hp : 0 < ModularVariance.gibbsProb E β i :=
      ModularVariance.gibbsProb_pos E β i
    have hwi : 0 < w i := hwpos i
    have hz := hzero i
    -- The deficit factors: `w i · ((p i / w i − 1) − log (p i / w i)) = 0`.
    have hfac : w i * ((ModularVariance.gibbsProb E β i / w i - 1)
        - Real.log (ModularVariance.gibbsProb E β i / w i)) = 0 := by
      rw [Real.log_div (ne_of_gt hp) (ne_of_gt hwi)]
      have h3 : w i * (ModularVariance.gibbsProb E β i / w i - 1)
          = ModularVariance.gibbsProb E β i - w i := by
        rw [mul_sub, mul_one, mul_div_assoc',
          mul_div_cancel_left₀ _ (ne_of_gt hwi)]
      have e1 : w i * ((ModularVariance.gibbsProb E β i / w i - 1)
          - (Real.log (ModularVariance.gibbsProb E β i)
            - Real.log (w i)))
          = w i * (ModularVariance.gibbsProb E β i / w i - 1)
            - w i * (Real.log (ModularVariance.gibbsProb E β i)
              - Real.log (w i)) := by ring
      rw [e1, h3]
      have h4 : w i * (Real.log (ModularVariance.gibbsProb E β i)
            - Real.log (w i))
          = w i * Real.log (ModularVariance.gibbsProb E β i)
            - w i * Real.log (w i) := by ring
      rw [h4]
      linarith
    have hbracket : (ModularVariance.gibbsProb E β i / w i - 1)
        - Real.log (ModularVariance.gibbsProb E β i / w i) = 0 := by
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd h (ne_of_gt hwi)
      · exact h
    have ht : ModularVariance.gibbsProb E β i / w i = 1 := by
      by_contra hne
      have hlt : Real.log (ModularVariance.gibbsProb E β i / w i)
          < ModularVariance.gibbsProb E β i / w i - 1 :=
        Real.log_lt_sub_one_of_pos (div_pos hp hwi) hne
      linarith
    have := (div_eq_one_iff_eq (ne_of_gt hwi)).mp ht
    rw [this]
  · intro h
    rw [h]
    have hform := entropyW_gibbsProb_eq_beta_form E β
    rw [hform]
    have hmean : (∑ i, ModularVariance.gibbsProb E β i * E i)
        = ModularVariance.meanEnergy E β := rfl
    rw [hmean]
    ring

/-- **A Gibbs family with a genuine gap reads its own `β`** (proved):
if the energy takes two distinct values, the Gibbs state determines
`β` — `gibbsProb E β = gibbsProb E β'` forces `β = β'`. Route: at
each site, cross-multiplying the equality of the two states and
taking `log` gives `−β·E k + log Z' = −β'·E k + log Z`; subtracting
the identities at two sites of distinct energy kills the `log Z`
terms and leaves `(β' − β)·(E i − E j) = 0`. -/
theorem gibbsProb_inj_beta {ι : Type*} [Fintype ι] [Nonempty ι]
    (E : ι → ℝ) (hE : ∃ i j, E i ≠ E j) {β β' : ℝ}
    (h : ModularVariance.gibbsProb E β
      = ModularVariance.gibbsProb E β') : β = β' := by
  obtain ⟨i, j, hij⟩ := hE
  have key : ∀ k : ι, -(β * E k)
        + Real.log (ModularVariance.partSum E β')
      = -(β' * E k) + Real.log (ModularVariance.partSum E β) := by
    intro k
    have hk := congrFun h k
    unfold ModularVariance.gibbsProb at hk
    have hZ : ModularVariance.partSum E β ≠ 0 :=
      ModularVariance.partSum_ne_zero E β
    have hZ' : ModularVariance.partSum E β' ≠ 0 :=
      ModularVariance.partSum_ne_zero E β'
    rw [div_eq_div_iff hZ hZ'] at hk
    have hlog := congrArg Real.log hk
    rw [Real.log_mul (Real.exp_ne_zero _)
        (ne_of_gt (ModularVariance.partSum_pos E β')),
      Real.log_mul (Real.exp_ne_zero _)
        (ne_of_gt (ModularVariance.partSum_pos E β)),
      Real.log_exp, Real.log_exp] at hlog
    exact hlog
  have hi := key i
  have hj := key j
  have hsub : (β' - β) * (E i - E j) = 0 := by
    have e : (β' - β) * (E i - E j)
        = (-(β * E i) + β * E j) - (-(β' * E i) + β' * E j) := by
      ring
    rw [e]
    linarith
  rcases mul_eq_zero.mp hsub with h1 | h2
  · linarith
  · exact absurd (sub_eq_zero.mp h2) hij

/-- **Mean energy is antitone in `β`** (proved, by citation of the
census fluctuation–response identity): hotter (smaller `β`) means
more mean energy. The derivative of `⟨E⟩_β` is `−Var_β(E) ≤ 0`
(`ModularVariance.hasDerivAt_meanEnergy`,
`ModularVariance.varEnergy_nonneg`), and a differentiable function
with nonpositive derivative is antitone. -/
theorem meanEnergy_antitone {ι : Type*} [Fintype ι] [Nonempty ι]
    (E : ι → ℝ) : Antitone (ModularVariance.meanEnergy E) := by
  apply antitone_of_deriv_nonpos
  · intro x
    exact (ModularVariance.hasDerivAt_meanEnergy E x).differentiableAt
  · intro x
    show deriv (fun β => ModularVariance.meanEnergy E β) x ≤ 0
    rw [(ModularVariance.hasDerivAt_meanEnergy E x).deriv]
    exact neg_nonpos.mpr (ModularVariance.varEnergy_nonneg E x)

-- ============================================================================
-- HB-1 (continued). The balance point and the approach
-- ============================================================================

/-- **The balance point exists** (proved): for every pair `(β₁, β₂)`
there is a common inverse temperature `βs`, between `β₁` and `β₂`,
at which the total mean energy equals the pair's total mean energy
— the energy-conserving equilibration of the exchange step always
exists. Route: the total mean energy at a common `β` is continuous
(each mean energy is differentiable, census fluctuation–response)
and each family's mean energy is antitone in `β`
(`meanEnergy_antitone`), so at `min β₁ β₂` the common-`β` total is
at least the pair's total and at `max β₁ β₂` at most; the
intermediate value theorem closes. -/
theorem exists_balance_beta {X Y : Type*} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] (E₁ : X → ℝ) (E₂ : Y → ℝ) (β₁ β₂ : ℝ) :
    ∃ βs, ModularVariance.meanEnergy E₁ βs
          + ModularVariance.meanEnergy E₂ βs
        = ModularVariance.meanEnergy E₁ β₁
          + ModularVariance.meanEnergy E₂ β₂
      ∧ βs ∈ Set.Icc (min β₁ β₂) (max β₁ β₂) := by
  have hcont₁ : Continuous (fun β => ModularVariance.meanEnergy E₁ β) :=
    continuous_iff_continuousAt.mpr fun x =>
      (ModularVariance.hasDerivAt_meanEnergy E₁ x).continuousAt
  have hcont₂ : Continuous (fun β => ModularVariance.meanEnergy E₂ β) :=
    continuous_iff_continuousAt.mpr fun x =>
      (ModularVariance.hasDerivAt_meanEnergy E₂ x).continuousAt
  have hcont : Continuous (fun β => ModularVariance.meanEnergy E₁ β
      + ModularVariance.meanEnergy E₂ β) :=
    hcont₁.add hcont₂
  have hmin : ModularVariance.meanEnergy E₁ β₁
        + ModularVariance.meanEnergy E₂ β₂
      ≤ ModularVariance.meanEnergy E₁ (min β₁ β₂)
        + ModularVariance.meanEnergy E₂ (min β₁ β₂) :=
    add_le_add (meanEnergy_antitone E₁ (min_le_left β₁ β₂))
      (meanEnergy_antitone E₂ (min_le_right β₁ β₂))
  have hmax : ModularVariance.meanEnergy E₁ (max β₁ β₂)
        + ModularVariance.meanEnergy E₂ (max β₁ β₂)
      ≤ ModularVariance.meanEnergy E₁ β₁
        + ModularVariance.meanEnergy E₂ β₂ :=
    add_le_add (meanEnergy_antitone E₁ (le_max_left β₁ β₂))
      (meanEnergy_antitone E₂ (le_max_right β₁ β₂))
  have hIVT : (ModularVariance.meanEnergy E₁ β₁
        + ModularVariance.meanEnergy E₂ β₂)
      ∈ (fun β => ModularVariance.meanEnergy E₁ β
          + ModularVariance.meanEnergy E₂ β)
        '' Set.Icc (min β₁ β₂) (max β₁ β₂) :=
    intermediate_value_Icc' (min_le_max) hcont.continuousOn
      ⟨hmax, hmin⟩
  obtain ⟨βs, hβsmem, hβseq⟩ := hIVT
  exact ⟨βs, hβseq, hβsmem⟩

/-- **The balance point is unique** (proved) when at least one
family carries a genuine energy gap: the total mean energy at a
common `β` is then strictly antitone — its derivative is
`−(Var₁ + Var₂) < 0` (census fluctuation–response plus
`varEnergy_pos_iff`) — hence injective, so at most one common `β`
conserves the pair's total mean energy. -/
theorem balance_beta_unique {X Y : Type*} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] (E₁ : X → ℝ) (E₂ : Y → ℝ)
    (hgap : (∃ i j, E₁ i ≠ E₁ j) ∨ (∃ i j, E₂ i ≠ E₂ j))
    (β₁ β₂ : ℝ) {β β' : ℝ}
    (hβ : ModularVariance.meanEnergy E₁ β
          + ModularVariance.meanEnergy E₂ β
        = ModularVariance.meanEnergy E₁ β₁
          + ModularVariance.meanEnergy E₂ β₂)
    (hβ' : ModularVariance.meanEnergy E₁ β'
          + ModularVariance.meanEnergy E₂ β'
        = ModularVariance.meanEnergy E₁ β₁
          + ModularVariance.meanEnergy E₂ β₂) :
    β = β' := by
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun β => ModularVariance.meanEnergy E₁ β
        + ModularVariance.meanEnergy E₂ β)
      (-(ModularVariance.varEnergy E₁ t)
        + -(ModularVariance.varEnergy E₂ t)) t :=
    fun t => (ModularVariance.hasDerivAt_meanEnergy E₁ t).add
      (ModularVariance.hasDerivAt_meanEnergy E₂ t)
  have hneg : ∀ t : ℝ, -(ModularVariance.varEnergy E₁ t)
      + -(ModularVariance.varEnergy E₂ t) < 0 := by
    intro t
    rcases hgap with h | h
    · have h1 : 0 < ModularVariance.varEnergy E₁ t :=
        (ModularVariance.varEnergy_pos_iff E₁ t).mpr h
      have h2 : 0 ≤ ModularVariance.varEnergy E₂ t :=
        ModularVariance.varEnergy_nonneg E₂ t
      linarith
    · have h1 : 0 ≤ ModularVariance.varEnergy E₁ t :=
        ModularVariance.varEnergy_nonneg E₁ t
      have h2 : 0 < ModularVariance.varEnergy E₂ t :=
        (ModularVariance.varEnergy_pos_iff E₂ t).mpr h
      linarith
  have hanti : StrictAnti (fun β => ModularVariance.meanEnergy E₁ β
      + ModularVariance.meanEnergy E₂ β) :=
    strictAnti_of_hasDerivAt_neg hderiv hneg
  apply hanti.injective
  show ModularVariance.meanEnergy E₁ β
      + ModularVariance.meanEnergy E₂ β
    = ModularVariance.meanEnergy E₁ β'
      + ModularVariance.meanEnergy E₂ β'
  rw [hβ, hβ']

/-- **One family against the balance point** (proved): moving one
family from `β` to the common `βs` costs it at most the
`βs`-weighted mean-energy change,

    `S(β) ≤ S(βs) + βs · (⟨E⟩_β − ⟨E⟩_{βs})`,

the variational principle at `βs` read through the census β-form
of the Gibbs entropy. Summed over the two families under energy
conservation, the correction terms cancel — that cancellation is
the approach theorem. -/
theorem entropyW_gibbs_le_of_balance {ι : Type*} [Fintype ι]
    [Nonempty ι] (E : ι → ℝ) (β βs : ℝ) :
    entropyW (ModularVariance.gibbsProb E β)
      ≤ entropyW (ModularVariance.gibbsProb E βs)
        + βs * (ModularVariance.meanEnergy E β
          - ModularVariance.meanEnergy E βs) := by
  have hvar := variational_gibbs_le E βs
    (ModularVariance.gibbsProb E β) (isProbWeight_gibbsProb E β)
    (fun i => ModularVariance.gibbsProb_pos E β i)
  have hform := entropyW_gibbsProb_eq_beta_form E βs
  have hmean : (∑ i, ModularVariance.gibbsProb E β i * E i)
      = ModularVariance.meanEnergy E β := rfl
  rw [hmean] at hvar
  have hsplit : βs * (ModularVariance.meanEnergy E β
        - ModularVariance.meanEnergy E βs)
      = βs * ModularVariance.meanEnergy E β
        - βs * ModularVariance.meanEnergy E βs := by ring
  linarith

/-- **HB-1, the approach** (proved): the exchange step never
decreases the total entropy. At the balance point `βs` (which
exists by `exists_balance_beta`), the sum of the two Gibbs
entropies is at least the pair's total entropy — each family's
variational correction is `βs` times its mean-energy change, and
energy conservation makes the two corrections cancel. -/
theorem balance_entropy_ge {X Y : Type*} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] (E₁ : X → ℝ) (E₂ : Y → ℝ)
    (β₁ β₂ βs : ℝ)
    (hβs : ModularVariance.meanEnergy E₁ βs
          + ModularVariance.meanEnergy E₂ βs
        = ModularVariance.meanEnergy E₁ β₁
          + ModularVariance.meanEnergy E₂ β₂) :
    entropyW (ModularVariance.gibbsProb E₁ β₁)
        + entropyW (ModularVariance.gibbsProb E₂ β₂)
      ≤ entropyW (ModularVariance.gibbsProb E₁ βs)
        + entropyW (ModularVariance.gibbsProb E₂ βs) := by
  have h1 := entropyW_gibbs_le_of_balance E₁ β₁ βs
  have h2 := entropyW_gibbs_le_of_balance E₂ β₂ βs
  have hcorr : βs * (ModularVariance.meanEnergy E₁ β₁
        - ModularVariance.meanEnergy E₁ βs)
      + βs * (ModularVariance.meanEnergy E₂ β₂
        - ModularVariance.meanEnergy E₂ βs) = 0 := by
    have hlin : (ModularVariance.meanEnergy E₁ β₁
          - ModularVariance.meanEnergy E₁ βs)
        + (ModularVariance.meanEnergy E₂ β₂
          - ModularVariance.meanEnergy E₂ βs) = 0 := by linarith
    calc βs * (ModularVariance.meanEnergy E₁ β₁
            - ModularVariance.meanEnergy E₁ βs)
          + βs * (ModularVariance.meanEnergy E₂ β₂
            - ModularVariance.meanEnergy E₂ βs)
        = βs * ((ModularVariance.meanEnergy E₁ β₁
            - ModularVariance.meanEnergy E₁ βs)
          + (ModularVariance.meanEnergy E₂ β₂
            - ModularVariance.meanEnergy E₂ βs)) := by ring
      _ = βs * 0 := by rw [hlin]
      _ = 0 := mul_zero βs
  linarith

/-- **HB-1, the dichotomy** (proved): when both families carry a
genuine energy gap, the exchange step increases the total entropy
STRICTLY unless the pair is already balanced — equality of the
total entropies holds exactly at `β₁ = β₂`. Forward: equality
forces equality in each family's variational principle (the two
corrections cancel under conservation), hence each family's state
at `βᵢ` is its state at `βs` (`variational_gibbs_eq_iff`), hence
`βᵢ = βs` (`gibbsProb_inj_beta`). Backward: at `β₁ = β₂` the
balance point is `β₁` itself (`balance_beta_unique`), so the step
changes nothing. -/
theorem balance_entropy_eq_iff {X Y : Type*} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] (E₁ : X → ℝ) (E₂ : Y → ℝ)
    (hE₁ : ∃ i j, E₁ i ≠ E₁ j) (hE₂ : ∃ i j, E₂ i ≠ E₂ j)
    (β₁ β₂ βs : ℝ)
    (hβs : ModularVariance.meanEnergy E₁ βs
          + ModularVariance.meanEnergy E₂ βs
        = ModularVariance.meanEnergy E₁ β₁
          + ModularVariance.meanEnergy E₂ β₂) :
    entropyW (ModularVariance.gibbsProb E₁ βs)
        + entropyW (ModularVariance.gibbsProb E₂ βs)
      = entropyW (ModularVariance.gibbsProb E₁ β₁)
        + entropyW (ModularVariance.gibbsProb E₂ β₂)
      ↔ β₁ = β₂ := by
  constructor
  · intro heq
    have hform₁ := entropyW_gibbsProb_eq_beta_form E₁ βs
    have hform₂ := entropyW_gibbsProb_eq_beta_form E₂ βs
    have hmean₁ : (∑ i, ModularVariance.gibbsProb E₁ β₁ i * E₁ i)
        = ModularVariance.meanEnergy E₁ β₁ := rfl
    have hmean₂ : (∑ i, ModularVariance.gibbsProb E₂ β₂ i * E₂ i)
        = ModularVariance.meanEnergy E₂ β₂ := rfl
    have h1 := entropyW_gibbs_le_of_balance E₁ β₁ βs
    have h2 := entropyW_gibbs_le_of_balance E₂ β₂ βs
    have hcorr : βs * (ModularVariance.meanEnergy E₁ β₁
          - ModularVariance.meanEnergy E₁ βs)
        + βs * (ModularVariance.meanEnergy E₂ β₂
          - ModularVariance.meanEnergy E₂ βs) = 0 := by
      have hlin : (ModularVariance.meanEnergy E₁ β₁
            - ModularVariance.meanEnergy E₁ βs)
          + (ModularVariance.meanEnergy E₂ β₂
            - ModularVariance.meanEnergy E₂ βs) = 0 := by linarith
      calc βs * (ModularVariance.meanEnergy E₁ β₁
              - ModularVariance.meanEnergy E₁ βs)
            + βs * (ModularVariance.meanEnergy E₂ β₂
              - ModularVariance.meanEnergy E₂ βs)
          = βs * ((ModularVariance.meanEnergy E₁ β₁
              - ModularVariance.meanEnergy E₁ βs)
            + (ModularVariance.meanEnergy E₂ β₂
              - ModularVariance.meanEnergy E₂ βs)) := by ring
        _ = βs * 0 := by rw [hlin]
        _ = 0 := mul_zero βs
    have h1eq : entropyW (ModularVariance.gibbsProb E₁ β₁)
        = entropyW (ModularVariance.gibbsProb E₁ βs)
          + βs * (ModularVariance.meanEnergy E₁ β₁
            - ModularVariance.meanEnergy E₁ βs) := by linarith
    have h2eq : entropyW (ModularVariance.gibbsProb E₂ β₂)
        = entropyW (ModularVariance.gibbsProb E₂ βs)
          + βs * (ModularVariance.meanEnergy E₂ β₂
            - ModularVariance.meanEnergy E₂ βs) := by linarith
    have hsplit₁ : βs * ModularVariance.meanEnergy E₁ βs
        + βs * (ModularVariance.meanEnergy E₁ β₁
          - ModularVariance.meanEnergy E₁ βs)
        = βs * ∑ i, ModularVariance.gibbsProb E₁ β₁ i * E₁ i := by
      rw [hmean₁]; ring
    have hsplit₂ : βs * ModularVariance.meanEnergy E₂ βs
        + βs * (ModularVariance.meanEnergy E₂ β₂
          - ModularVariance.meanEnergy E₂ βs)
        = βs * ∑ i, ModularVariance.gibbsProb E₂ β₂ i * E₂ i := by
      rw [hmean₂]; ring
    have hvar₁ : entropyW (ModularVariance.gibbsProb E₁ β₁)
        = Real.log (ModularVariance.partSum E₁ βs)
          + βs * ∑ i, ModularVariance.gibbsProb E₁ β₁ i * E₁ i := by
      linarith
    have hvar₂ : entropyW (ModularVariance.gibbsProb E₂ β₂)
        = Real.log (ModularVariance.partSum E₂ βs)
          + βs * ∑ i, ModularVariance.gibbsProb E₂ β₂ i * E₂ i := by
      linarith
    have hβ₁ : β₁ = βs := by
      have he1 : ModularVariance.gibbsProb E₁ β₁
          = ModularVariance.gibbsProb E₁ βs :=
        (variational_gibbs_eq_iff E₁ βs
          (ModularVariance.gibbsProb E₁ β₁)
          (isProbWeight_gibbsProb E₁ β₁)
          (fun i => ModularVariance.gibbsProb_pos E₁ β₁ i)).mp hvar₁
      exact gibbsProb_inj_beta E₁ hE₁ he1
    have hβ₂ : β₂ = βs := by
      have he2 : ModularVariance.gibbsProb E₂ β₂
          = ModularVariance.gibbsProb E₂ βs :=
        (variational_gibbs_eq_iff E₂ βs
          (ModularVariance.gibbsProb E₂ β₂)
          (isProbWeight_gibbsProb E₂ β₂)
          (fun i => ModularVariance.gibbsProb_pos E₂ β₂ i)).mp hvar₂
      exact gibbsProb_inj_beta E₂ hE₂ he2
    rw [hβ₁, hβ₂]
  · intro h
    have hstar : βs = β₁ := by
      apply balance_beta_unique E₁ E₂ (Or.inl hE₁) β₁ β₂ hβs
      show ModularVariance.meanEnergy E₁ β₁
          + ModularVariance.meanEnergy E₂ β₁
        = ModularVariance.meanEnergy E₁ β₁
          + ModularVariance.meanEnergy E₂ β₂
      rw [h]
    rw [hstar, ← h]


-- ============================================================================
-- HB-2. The rest point
-- ============================================================================

/-- **HB-2, the rest point** (proved): the exchange step rests
exactly at balance. The step sends `(β₁, β₂)` to `(βs, βs)`; it
fixes the pair — `βs = β₁` and `βs = β₂` — if and only if
`β₁ = β₂`. Out of equilibrium ⟺ the step still moves you.
Backward: at `β₁ = β₂` the pair's own common value already
conserves the total mean energy, so uniqueness
(`balance_beta_unique`, one genuine gap suffices) pins
`βs = β₁`. -/
theorem balance_step_fixed_iff {X Y : Type*} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] (E₁ : X → ℝ) (E₂ : Y → ℝ)
    (hE₁ : ∃ i j, E₁ i ≠ E₁ j) (β₁ β₂ βs : ℝ)
    (hβs : ModularVariance.meanEnergy E₁ βs
          + ModularVariance.meanEnergy E₂ βs
        = ModularVariance.meanEnergy E₁ β₁
          + ModularVariance.meanEnergy E₂ β₂) :
    (βs = β₁ ∧ βs = β₂) ↔ β₁ = β₂ := by
  constructor
  · rintro ⟨h1, h2⟩
    exact h1.symm.trans h2
  · intro h
    have hstar : βs = β₁ := by
      apply balance_beta_unique E₁ E₂ (Or.inl hE₁) β₁ β₂ hβs
      show ModularVariance.meanEnergy E₁ β₁
          + ModularVariance.meanEnergy E₂ β₁
        = ModularVariance.meanEnergy E₁ β₁
          + ModularVariance.meanEnergy E₂ β₂
      rw [h]
    exact ⟨hstar, by rw [hstar, h]⟩

/-- **Transport: the partition function of a sum energy on a
product seat factorizes** (proved): for the sum energy
`E₁ ⊕ E₂` on `X × Y`,
`Z(E₁ ⊕ E₂, β) = Z(E₁, β) · Z(E₂, β)`. This is the general
product form of the factorization whose dyadic instance is census
`partSum_linkEnergy` (`LeibnizGibbsBridgePin`, cited); the proof
is the same two moves — `Real.exp_add` and `Fintype.sum_mul_sum` —
on the binary product. Labeled transport: it is not approach
content, and no additivity is re-proved here. -/
theorem partSum_prod_energy {X Y : Type*} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] (E₁ : X → ℝ) (E₂ : Y → ℝ) (β : ℝ) :
    ModularVariance.partSum (fun p : X × Y => E₁ p.1 + E₂ p.2) β
      = ModularVariance.partSum E₁ β
        * ModularVariance.partSum E₂ β := by
  unfold ModularVariance.partSum
  rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  show Real.exp (-(β * (E₁ x + E₂ y)))
    = Real.exp (-(β * E₁ x)) * Real.exp (-(β * E₂ y))
  rw [← Real.exp_add]
  congr 1
  ring

/-- **Transport: at a shared `β`, the joint Gibbs state of a sum
energy is the product of the two Gibbs states** (proved) — the
Leibniz–Gibbs joint state on the binary product seat. At HB-2's
rest point the pair sits at a common `βs`, and this is the state
it sits in. The dyadic instance on the link seat is census
`gibbsProb_linkEnergy` (`LeibnizGibbsBridgePin`), cited, not
re-proved; this is its general product form, labeled transport. -/
theorem gibbsProb_prod_energy {X Y : Type*} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] (E₁ : X → ℝ) (E₂ : Y → ℝ) (β : ℝ)
    (p : X × Y) :
    ModularVariance.gibbsProb (fun q : X × Y => E₁ q.1 + E₂ q.2) β p
      = ModularVariance.gibbsProb E₁ β p.1
        * ModularVariance.gibbsProb E₂ β p.2 := by
  unfold ModularVariance.gibbsProb
  rw [partSum_prod_energy,
    show -(β * (E₁ p.1 + E₂ p.2)) = -(β * E₁ p.1) + -(β * E₂ p.2)
      from by ring,
    Real.exp_add, div_mul_div_comm]


-- ============================================================================
-- HB-3. The discrete seat: overshoot, and the damped step
-- ============================================================================

/-- **Marginal entropy of the next quantum** (definition): for an
entropy function `s : ℕ → ℝ` on quantum counts, `margEntropy s k`
is the entropy gained by adding one quantum to a family already
holding `k` — the discrete seat's `β`: entropy per quantum. -/
def margEntropy (s : ℕ → ℝ) (k : ℕ) : ℝ := s (k + 1) - s k

/-- **Total entropy of a split** (definition): with `K` quanta in
total and `a` of them in family 1 (so `K - a` in family 2), the
total entropy of the pair of identical families with entropy
function `s` is `s a + s (K - a)`. -/
def splitEntropy (s : ℕ → ℝ) (K a : ℕ) : ℝ := s a + s (K - a)

/-- **The one-quantum step's entropy change, exactly** (proved):
moving one quantum from family 1 (holding `a ≥ 1`) to family 2
changes the total entropy by

    `margEntropy s (K - a) - margEntropy s (a - 1)` —

what the receiving family's next quantum gains, minus what the
giving family's last quantum carried. Pure bookkeeping, stated
exactly; the content of HB-3 is in its corollaries. -/
theorem greedy_step_entropy_change (s : ℕ → ℝ) (K a : ℕ)
    (ha : 1 ≤ a) (haK : a ≤ K) :
    splitEntropy s K (a - 1) - splitEntropy s K a
      = margEntropy s (K - a) - margEntropy s (a - 1) := by
  have h1 : K - (a - 1) = K - a + 1 := by omega
  have h2 : a - 1 + 1 = a := by omega
  unfold splitEntropy margEntropy
  rw [h1, h2]
  ring

/-- **The damped step increases entropy** (proved): the damped
step — move ONE quantum, the smallest fraction of the imbalance —
in the direction the marginals dictate (family 1's last quantum
carries less entropy than family 2's next quantum would gain, i.e.
family 1 is hotter) strictly increases the total entropy. HB-1's
approach on the discrete seat: heat flows hot → cold, one quantum
at a time, and the books balance upward. -/
theorem greedy_step_increases (s : ℕ → ℝ) (K a : ℕ)
    (ha : 1 ≤ a) (haK : a ≤ K)
    (h : margEntropy s (a - 1) < margEntropy s (K - a)) :
    splitEntropy s K a < splitEntropy s K (a - 1) := by
  have hΔ := greedy_step_entropy_change s K a ha haK
  linarith

/-- **The two-seat exhibit's entropy function** (definition):
`s₀ k = log (k + 1)` — the entropy of a family holding `k` quanta
in the HB-3 countermodel. Its marginals are
`log 2, log (3/2), log (4/3), …` — strictly decreasing: each
further quantum carries less entropy (the discrete concavity). -/
noncomputable def hbExhibitEntropy (k : ℕ) : ℝ :=
  Real.log ((k + 1 : ℕ) : ℝ)

/-- The exhibit's marginals at the two lowest levels (proved):
the first quantum carries `log 2`; the second carries
`log 3 - log 2 = log (3/2)` — strictly less. -/
theorem exhibit_marginals :
    margEntropy hbExhibitEntropy 0 = Real.log 2
    ∧ margEntropy hbExhibitEntropy 1
      = Real.log 3 - Real.log 2 := by
  have h0 : hbExhibitEntropy 0 = 0 := by simp [hbExhibitEntropy]
  have h1 : hbExhibitEntropy 1 = Real.log 2 := by
    norm_num [hbExhibitEntropy]
  have h2 : hbExhibitEntropy 2 = Real.log 3 := by
    norm_num [hbExhibitEntropy]
  constructor
  · have e : margEntropy hbExhibitEntropy 0
        = hbExhibitEntropy 1 - hbExhibitEntropy 0 := rfl
    rw [e, h1, h0, sub_zero]
  · have e : margEntropy hbExhibitEntropy 1
        = hbExhibitEntropy 2 - hbExhibitEntropy 1 := rfl
    rw [e, h2, h1]

/-- **The exhibit's entropy values** (proved): with two quanta in
total, the unbalanced splits `(2, 0)` and `(0, 2)` have total
entropy `log 3`; the balanced split `(1, 1)` has `2 log 2`; and
`log 3 < 2 log 2`, since `3 < 4 = 2²`. -/
theorem exhibit_entropy_values :
    splitEntropy hbExhibitEntropy 2 0 = Real.log 3
    ∧ splitEntropy hbExhibitEntropy 2 1 = 2 * Real.log 2
    ∧ splitEntropy hbExhibitEntropy 2 2 = Real.log 3
    ∧ Real.log 3 < 2 * Real.log 2 := by
  have h0 : hbExhibitEntropy 0 = 0 := by simp [hbExhibitEntropy]
  have h1 : hbExhibitEntropy 1 = Real.log 2 := by
    norm_num [hbExhibitEntropy]
  have h2 : hbExhibitEntropy 2 = Real.log 3 := by
    norm_num [hbExhibitEntropy]
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : splitEntropy hbExhibitEntropy 2 0
        = hbExhibitEntropy 0 + hbExhibitEntropy 2 := rfl
    rw [e, h0, h2, zero_add]
  · have e : splitEntropy hbExhibitEntropy 2 1
        = hbExhibitEntropy 1 + hbExhibitEntropy 1 := rfl
    rw [e, h1]
    ring
  · have e : splitEntropy hbExhibitEntropy 2 2
        = hbExhibitEntropy 2 + hbExhibitEntropy 0 := rfl
    rw [e, h2, h0, add_zero]
  · rw [← hlog4]
    exact Real.log_lt_log (by norm_num) (by norm_num)

/-- **The undamped full-imbalance step** (definition): from split
`a` of `K` quanta, transfer the WHOLE imbalance at once — family 1
goes from holding `a` quanta to holding `K - a`: the mirror
split. -/
def undampedStep (K a : ℕ) : ℕ := K - a

/-- **K-HB-OSCILLATE FIRES** (proved — the pre-registered kill):
on the two-seat exhibit (`K = 2`, `s₀ = log (· + 1)`), the
undamped full-imbalance step sends the unbalanced split `2` to
`0` and straight back — period 2 — at constant total entropy
`log 3`, never reaching the balanced split `1`, whose entropy
`2 log 2` is strictly larger. And this despite a strictly
entropy-increasing one-quantum move existing at split `2`
(family 1's last quantum carries `log (3/2)`; family 2's next
quantum would gain `log 2`). The full step does not creep toward
balance; it jumps over it, forever. The undamped step is dead.
The damped one-quantum step is the saved form (next theorem). -/
theorem undamped_full_step_oscillates :
    undampedStep 2 2 = 0
    ∧ undampedStep 2 (undampedStep 2 2) = 2
    ∧ splitEntropy hbExhibitEntropy 2 (undampedStep 2 2)
      = splitEntropy hbExhibitEntropy 2 2
    ∧ splitEntropy hbExhibitEntropy 2 2
      < splitEntropy hbExhibitEntropy 2 1
    ∧ margEntropy hbExhibitEntropy (2 - 1)
      < margEntropy hbExhibitEntropy (2 - 2) := by
  obtain ⟨hv0, hv1, hv2, hlt⟩ := exhibit_entropy_values
  obtain ⟨hm0, hm1⟩ := exhibit_marginals
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · rw [show undampedStep 2 2 = 0 from rfl, hv0, hv2]
  · rw [hv2, hv1]
    exact hlt
  · show margEntropy hbExhibitEntropy 1
      < margEntropy hbExhibitEntropy 0
    rw [hm1, hm0]
    linarith

/-- **The damped step finds the balance** (proved, on the
exhibit): from the unbalanced split `2`, the one-quantum damped
step in the marginals' direction lands on the balanced split `1`
with strictly larger total entropy (`greedy_step_increases`); and
at `1` the pair rests — neither direction offers a strictly
improving move, and the two families' last-quantum marginals
agree on the nose (`log 2` each): the discrete seat's exact
balance, the rest point the undamped step jumps over forever. -/
theorem damped_step_balances_exhibit :
    splitEntropy hbExhibitEntropy 2 2
      < splitEntropy hbExhibitEntropy 2 1
    ∧ ¬ margEntropy hbExhibitEntropy (1 - 1)
        < margEntropy hbExhibitEntropy (2 - 1)
    ∧ ¬ margEntropy hbExhibitEntropy (2 - 1 - 1)
        < margEntropy hbExhibitEntropy 1
    ∧ margEntropy hbExhibitEntropy (1 - 1)
      = margEntropy hbExhibitEntropy (2 - 1 - 1) := by
  obtain ⟨hm0, hm1⟩ := exhibit_marginals
  obtain ⟨hv0, hv1, hv2, hlt⟩ := exhibit_entropy_values
  have hmove : splitEntropy hbExhibitEntropy 2 2
      < splitEntropy hbExhibitEntropy 2 (2 - 1) :=
    greedy_step_increases hbExhibitEntropy 2 2 (by norm_num)
      (by norm_num) (by
        show margEntropy hbExhibitEntropy 1
          < margEntropy hbExhibitEntropy 0
        rw [hm1, hm0]
        linarith)
  refine ⟨hmove, ?_, ?_, rfl⟩
  · show ¬ margEntropy hbExhibitEntropy 0
      < margEntropy hbExhibitEntropy 1
    rw [hm0, hm1]
    linarith
  · show ¬ margEntropy hbExhibitEntropy 0
      < margEntropy hbExhibitEntropy 1
    rw [hm0, hm1]
    linarith

end ThetLogos
