import ThetLogos.BlockingProjectionNonab
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# RG-2d — the tilt-mean differentiability kit and the matched slope

S5 of the RG-2 scoping, at the RG-2c seat (the nonabelian `D₄`
rebuild). RG-2c proved existence, uniqueness, and strict
monotonicity of the plaquette-matched projection `β′(β)` at that
seat *without taking a derivative anywhere*: strict antitonicity of
the tilt mean came from the symmetrized-sum variance identity, the
integrated form of the covariance. This module supplies the
differential form and its consequence for the projection.

**Part 1 (the kit).** For a finitely valued observable `a`, the
tilt mean `tiltMean a` of `BlockingProjectionNonab` is smooth
(`ContDiff` at every order), with derivative

  `deriv (tiltMean a) t = - tiltVar a t`,

where `tiltVar a t` is the variance of `a` under the tilted
(Gibbs) weights `e^{-t·a}` — the differential form of RG-2c's
covariance identity. The variance is *strictly positive at every
tilt* whenever `a` is nonconstant (`tiltVar_pos`): at finite
volume every configuration carries strictly positive weight at
every tilt, so a nondegenerate observable never degenerates.
This discharges kill condition KD-1 of the brick by proof: the
matched slope below has no pole at any matched point, interior
or otherwise.

**Part 2 (the slope).** At the `D₄` seat, let `nbMatched β` be
the unique matched value of RG-2c (for `β ≥ 0`). Then
`nbMatched` is differentiable on its domain (one-sidedly at the
endpoint), with

  slope at `β₀` `= 2 * tiltVar nbFine (12 * β₀)
                    / tiltVar nbCoarse (6 * nbMatched β₀)`,

the ratio of the two sides' tilt variances with their tilt
factors (fine tilt `12β`, coarse tilt `6β′`, per the RG-2c
bridges), the two minus signs cancelling. The slope is strictly
positive at every `β₀ ≥ 0`, in agreement with the landed strict
monotonicity. At the anchor `β₀ = 0` the formula evaluates with
the fine variance at tilt `0` (`nbFine_tiltVar_zero`); the coarse
variance sits at tilt `6 * nbMatched 0`, which is a *negative*
tilt at this seat (RG-2c: the anchor is negative), so no rational
closed form is claimed for the coarse factor.

**Fence (KD-2, standing).** The slope computed here is the
derivative of a *bookkeeping statistic* — a projection defined
by matching one observable between two measures at one finite
seat. It is not a β-function: nothing here runs, flows, iterates,
or has fixed points, and no sentence of this module promotes it
to one. Killed on sight, per the RG-2 scoping §0. NO CLAIM;
dials 0/4.
-/

open Finset Filter Topology Set

namespace ThetLogos

section TiltDerivKit

variable {ι : Type*} [Fintype ι]

/-- The second-moment numerator of the tilt family:
`Σᵢ e^{-t·aᵢ} · (aᵢ)²`. -/
noncomputable def tiltSq (a : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, Real.exp (-(t * a i)) * (a i) ^ 2

/-- The variance of the observable `a` under the tilted weights
`e^{-t·a}`: second tilted moment minus the squared tilt mean. -/
noncomputable def tiltVar (a : ι → ℝ) (t : ℝ) : ℝ :=
  tiltSq a t / tiltDen a t - (tiltMean a t) ^ 2

/-- The variance is the tilted mean squared deviation from the
tilt mean itself (the centered form). -/
theorem tiltVar_eq_centered [Nonempty ι] (a : ι → ℝ) (t : ℝ) :
    tiltVar a t
      = (∑ i, Real.exp (-(t * a i)) * (a i - tiltMean a t) ^ 2)
        / tiltDen a t := by
  have hD : (0 : ℝ) < tiltDen a t := tiltDen_pos a t
  have hN : tiltNum a t = tiltMean a t * tiltDen a t := by
    rw [tiltMean, div_mul_cancel₀ _ hD.ne']
  have hterm : ∀ i : ι, Real.exp (-(t * a i)) * (a i - tiltMean a t) ^ 2
      = Real.exp (-(t * a i)) * (a i) ^ 2
        - 2 * tiltMean a t * (Real.exp (-(t * a i)) * a i)
        + (tiltMean a t) ^ 2 * Real.exp (-(t * a i)) := fun i => by ring
  have hsum : (∑ i, Real.exp (-(t * a i)) * (a i - tiltMean a t) ^ 2)
      = tiltSq a t - (tiltMean a t) ^ 2 * tiltDen a t := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    show tiltSq a t - 2 * tiltMean a t * tiltNum a t
        + (tiltMean a t) ^ 2 * tiltDen a t
      = tiltSq a t - (tiltMean a t) ^ 2 * tiltDen a t
    rw [hN]
    ring
  rw [hsum]
  unfold tiltVar
  rw [sub_div, mul_div_cancel_right₀ _ hD.ne']

/-- The tilted variance is nonnegative. -/
theorem tiltVar_nonneg [Nonempty ι] (a : ι → ℝ) (t : ℝ) :
    0 ≤ tiltVar a t := by
  rw [tiltVar_eq_centered]
  exact div_nonneg
    (Finset.sum_nonneg fun i _ =>
      mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
    (tiltDen_pos a t).le

/-- **The tilted variance is strictly positive at every tilt for
a nonconstant observable** (every configuration keeps strictly
positive weight at every tilt, and the observable takes two
values, so it differs from its own mean somewhere). This is the
KD-1 discharge: the variance factor in any tilt-mean slope can
vanish nowhere. -/
theorem tiltVar_pos [Nonempty ι] (a : ι → ℝ)
    (hna : ¬ ∀ i j : ι, a i = a j) (t : ℝ) :
    0 < tiltVar a t := by
  obtain ⟨p, q, hpq⟩ : ∃ p q, a p ≠ a q := by
    by_contra hcon
    push_neg at hcon
    exact hna hcon
  rw [tiltVar_eq_centered]
  apply div_pos _ (tiltDen_pos a t)
  have hterm : ∀ i : ι, 0 ≤ Real.exp (-(t * a i))
      * (a i - tiltMean a t) ^ 2 :=
    fun i => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  rcases ne_or_eq (a p) (tiltMean a t) with hp | hp
  · exact Finset.sum_pos' (fun i _ => hterm i)
      ⟨p, Finset.mem_univ p,
        mul_pos (Real.exp_pos _)
          (sq_pos_of_ne_zero (sub_ne_zero.mpr hp))⟩
  · have hq : a q ≠ tiltMean a t := by
      intro h
      exact hpq (hp.trans h.symm ▸ rfl)
    exact Finset.sum_pos' (fun i _ => hterm i)
      ⟨q, Finset.mem_univ q,
        mul_pos (Real.exp_pos _)
          (sq_pos_of_ne_zero (sub_ne_zero.mpr hq))⟩

/-- One exponential tilt factor, differentiated. -/
theorem hasDerivAt_exp_neg_mul (c t : ℝ) :
    HasDerivAt (fun s => Real.exp (-(s * c)))
      (Real.exp (-(t * c)) * (-c)) t := by
  have hlin : HasDerivAt (fun s : ℝ => (-c) * s) (-c) t := by
    simpa using (hasDerivAt_id t).const_mul (-c)
  have hcomp := (Real.hasDerivAt_exp ((-c) * t)).comp t hlin
  have harg : (-c) * t = -(t * c) := by ring
  rw [harg] at hcomp
  refine hcomp.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext s
  show Real.exp (-(s * c)) = Real.exp ((-c) * s)
  congr 1
  ring

/-- The tilt denominator differentiates to minus the numerator. -/
theorem hasDerivAt_tiltDen (a : ι → ℝ) (t : ℝ) :
    HasDerivAt (tiltDen a) (- tiltNum a t) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => hasDerivAt_exp_neg_mul (a i) t)
  have hval : (∑ i, Real.exp (-(t * a i)) * (-(a i)))
      = - tiltNum a t := by
    unfold tiltNum
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hval] at h
  exact h

/-- The tilt numerator differentiates to minus the second-moment
numerator. -/
theorem hasDerivAt_tiltNum (a : ι → ℝ) (t : ℝ) :
    HasDerivAt (tiltNum a) (- tiltSq a t) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (hasDerivAt_exp_neg_mul (a i) t).mul_const (a i))
  have hval : (∑ i, Real.exp (-(t * a i)) * (-(a i)) * (a i))
      = - tiltSq a t := by
    unfold tiltSq
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hval] at h
  exact h

/-- **The tilt mean differentiates to minus the tilted
variance.** The differential form of the covariance identity
that RG-2c used in integrated (symmetrized-sum) form. -/
theorem hasDerivAt_tiltMean [Nonempty ι] (a : ι → ℝ) (t : ℝ) :
    HasDerivAt (tiltMean a) (- tiltVar a t) t := by
  have hD : tiltDen a t ≠ 0 := (tiltDen_pos a t).ne'
  have h := HasDerivAt.fun_div (hasDerivAt_tiltNum a t)
    (hasDerivAt_tiltDen a t) hD
  have hder : ((- tiltSq a t) * tiltDen a t
        - tiltNum a t * (- tiltNum a t)) / (tiltDen a t) ^ 2
      = - tiltVar a t := by
    unfold tiltVar tiltMean
    field_simp
    ring
  rw [hder] at h
  exact h

/-- The derivative of the tilt mean is minus the tilted
variance, at every tilt. -/
theorem deriv_tiltMean [Nonempty ι] (a : ι → ℝ) (t : ℝ) :
    deriv (tiltMean a) t = - tiltVar a t :=
  (hasDerivAt_tiltMean a t).deriv

/-- The tilt denominator is smooth. -/
theorem tiltDen_contDiff (a : ι → ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (tiltDen a) := by
  unfold tiltDen
  apply ContDiff.sum
  intro i _
  exact Real.contDiff_exp.comp
    ((contDiff_id.mul contDiff_const).neg)

/-- The tilt numerator is smooth. -/
theorem tiltNum_contDiff (a : ι → ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (tiltNum a) := by
  unfold tiltNum
  apply ContDiff.sum
  intro i _
  exact (Real.contDiff_exp.comp
    ((contDiff_id.mul contDiff_const).neg)).mul contDiff_const

/-- **The tilt mean is smooth** (at every order), being a ratio
of smooth functions with nowhere-vanishing denominator. -/
theorem tiltMean_contDiff [Nonempty ι] (a : ι → ℝ)
    (n : WithTop ℕ∞) : ContDiff ℝ n (tiltMean a) := by
  unfold tiltMean
  exact (tiltNum_contDiff a n).div (tiltDen_contDiff a n)
    (fun t => (tiltDen_pos a t).ne')

end TiltDerivKit

section MatchedSlope

/-- The matched projection at the `D₄` seat, as a function: for
`β ≥ 0`, the unique `β′` of `nb_matched_exists_unique`; a junk
value off the domain (nothing is ever proved about it there). -/
noncomputable def nbMatched (β : ℝ) : ℝ :=
  if h : 0 ≤ β then
    Classical.choose (nb_matched_exists_unique h)
  else 0

/-- The chosen value is matched. -/
theorem nbMatched_spec {β : ℝ} (hβ : 0 ≤ β) :
    PlaquetteMatched flowσ flowσ' nbμG nbRep flowBlocking β
      (nbMatched β) := by
  unfold nbMatched
  rw [dif_pos hβ]
  exact (Classical.choose_spec (nb_matched_exists_unique hβ)).1

/-- Matched values are the chosen one. -/
theorem nbMatched_eq {β β' : ℝ} (hβ : 0 ≤ β)
    (h : PlaquetteMatched flowσ flowσ' nbμG nbRep flowBlocking
      β β') :
    β' = nbMatched β :=
  (nb_matched_exists_unique hβ).unique h (nbMatched_spec hβ)

/-- The matching identity in tilt-mean form: the coarse tilt
mean at tilt `6 * nbMatched β` equals the fine tilt mean at
tilt `12 * β`. -/
theorem nb_match_eq {β : ℝ} (hβ : 0 ≤ β) :
    tiltMean nbCoarse (6 * nbMatched β) = tiltMean nbFine (12 * β) := by
  have h := (nb_plaquetteMatched_iff β (nbMatched β)).mp
    (nbMatched_spec hβ)
  rwa [nb_fine_bridge] at h

/-- The matched function is continuous on its domain: the
matching identity transports continuity of the fine tilt mean
through the strictly antitone coarse tilt mean. -/
theorem nbMatched_continuousWithinAt {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) :
    ContinuousWithinAt nbMatched (Set.Ici 0) β₀ := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hmatch₀ : tiltMean nbCoarse (6 * nbMatched β₀)
      = tiltMean nbFine (12 * β₀) := nb_match_eq hβ₀
  have hGanti := tiltMean_strictAnti nbCoarse nbCoarse_nonconst
  have hup : tiltMean nbCoarse (6 * (nbMatched β₀ + ε))
      < tiltMean nbFine (12 * β₀) := by
    rw [← hmatch₀]
    exact hGanti (by linarith)
  have hdn : tiltMean nbFine (12 * β₀)
      < tiltMean nbCoarse (6 * (nbMatched β₀ - ε)) := by
    rw [← hmatch₀]
    exact hGanti (by linarith)
  set η := min (tiltMean nbFine (12 * β₀)
      - tiltMean nbCoarse (6 * (nbMatched β₀ + ε)))
    (tiltMean nbCoarse (6 * (nbMatched β₀ - ε))
      - tiltMean nbFine (12 * β₀)) with hηdef
  have hη : 0 < η := lt_min (sub_pos.mpr hup) (sub_pos.mpr hdn)
  have hcont : ContinuousAt (fun β => tiltMean nbFine (12 * β)) β₀ :=
    ((tiltMean_continuous nbFine).comp
      (continuous_const.mul continuous_id)).continuousAt
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont η hη
  refine ⟨δ, hδpos, fun {β} hβ hδβ => ?_⟩
  have hβ0 : 0 ≤ β := hβ
  have hmatch : tiltMean nbCoarse (6 * nbMatched β)
      = tiltMean nbFine (12 * β) := nb_match_eq hβ0
  have hFβ : |tiltMean nbFine (12 * β)
      - tiltMean nbFine (12 * β₀)| < η := by
    have h := hδ hδβ
    rwa [Real.dist_eq] at h
  rw [Real.dist_eq, abs_lt]
  constructor
  · -- `-(nbMatched β - nbMatched β₀) < ε`
    by_contra hcon
    push Not at hcon
    have hle : tiltMean nbCoarse (6 * (nbMatched β₀ - ε))
        ≤ tiltMean nbCoarse (6 * nbMatched β) := by
      apply (hGanti.le_iff_ge).mpr
      linarith
    have h1 : tiltMean nbFine (12 * β₀) + η
        ≤ tiltMean nbCoarse (6 * (nbMatched β₀ - ε)) := by
      have hmin := min_le_right (tiltMean nbFine (12 * β₀)
        - tiltMean nbCoarse (6 * (nbMatched β₀ + ε)))
        (tiltMean nbCoarse (6 * (nbMatched β₀ - ε))
          - tiltMean nbFine (12 * β₀))
      rw [← hηdef] at hmin
      linarith
    linarith [abs_lt.mp hFβ |>.2]
  · -- `nbMatched β - nbMatched β₀ < ε`
    by_contra hcon
    push Not at hcon
    have hle : tiltMean nbCoarse (6 * nbMatched β)
        ≤ tiltMean nbCoarse (6 * (nbMatched β₀ + ε)) := by
      apply (hGanti.le_iff_ge).mpr
      linarith
    have h1 : tiltMean nbCoarse (6 * (nbMatched β₀ + ε))
        ≤ tiltMean nbFine (12 * β₀) - η := by
      have hmin := min_le_left (tiltMean nbFine (12 * β₀)
        - tiltMean nbCoarse (6 * (nbMatched β₀ + ε)))
        (tiltMean nbCoarse (6 * (nbMatched β₀ - ε))
          - tiltMean nbFine (12 * β₀))
      rw [← hηdef] at hmin
      linarith
    linarith [abs_lt.mp hFβ |>.1]

/-- The matched value differs at distinct domain points. -/
theorem nbMatched_ne {β β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : 0 ≤ β₀)
    (hne : β ≠ β₀) : nbMatched β ≠ nbMatched β₀ := by
  intro h
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := nb_matched_strict_mono hlt (nbMatched_spec hβ)
      (nbMatched_spec hβ₀)
    exact absurd h (ne_of_lt this)
  · have := nb_matched_strict_mono hgt (nbMatched_spec hβ₀)
      (nbMatched_spec hβ)
    exact absurd h (ne_of_gt this)

/-- **S5 at the `D₄` seat: the matched slope.** The matched
projection is differentiable on its domain (one-sidedly at the
endpoint `0`), with slope the ratio of the two sides' tilt
variances at their matched tilts — fine tilt `12 * β₀`, coarse
tilt `6 * nbMatched β₀` — the tilt factors `12` and `6` and the
two minus signs of `deriv_tiltMean` combining into the factor
`2` and a positive sign. -/
theorem nbMatched_hasDerivWithinAt {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) :
    HasDerivWithinAt nbMatched
      (2 * tiltVar nbFine (12 * β₀)
        / tiltVar nbCoarse (6 * nbMatched β₀)) (Set.Ici 0) β₀ := by
  have hVcpos : 0 < tiltVar nbCoarse (6 * nbMatched β₀) :=
    tiltVar_pos nbCoarse nbCoarse_nonconst _
  have hmatch₀ : tiltMean nbCoarse (6 * nbMatched β₀)
      = tiltMean nbFine (12 * β₀) := nb_match_eq hβ₀
  -- The fine side, as a function of `β`, and its slope limit.
  have hh : HasDerivAt (fun β : ℝ => 12 * β) 12 β₀ := by
    simpa using (hasDerivAt_id β₀).const_mul 12
  have hFβ : HasDerivWithinAt (fun β => tiltMean nbFine (12 * β))
      ((-(tiltVar nbFine (12 * β₀))) * 12) (Set.Ici 0) β₀ :=
    ((hasDerivAt_tiltMean nbFine (12 * β₀)).comp β₀ hh).hasDerivWithinAt
  have hTA : Tendsto (fun β => (tiltMean nbFine (12 * β)
        - tiltMean nbFine (12 * β₀)) / (β - β₀))
      (𝓝[Set.Ici 0 \ {β₀}] β₀)
      (𝓝 ((-(tiltVar nbFine (12 * β₀))) * 12)) := by
    have h := (hasDerivWithinAt_iff_tendsto_slope).mp hFβ
    refine h.congr' ?_
    filter_upwards with β
    rw [slope_def_field]
  -- The coarse side: its slope limit along the matched values.
  have hG : HasDerivAt (tiltMean nbCoarse)
      (-(tiltVar nbCoarse (6 * nbMatched β₀))) (6 * nbMatched β₀) :=
    hasDerivAt_tiltMean nbCoarse (6 * nbMatched β₀)
  have hu : Tendsto (fun β => 6 * nbMatched β)
      (𝓝[Set.Ici 0 \ {β₀}] β₀) (𝓝[≠] (6 * nbMatched β₀)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : Tendsto nbMatched (𝓝[Set.Ici 0 \ {β₀}] β₀)
          (𝓝 (nbMatched β₀)) :=
        (nbMatched_continuousWithinAt hβ₀).mono_left
          (nhdsWithin_mono β₀ Set.sdiff_subset)
      exact hc.const_mul 6
    · filter_upwards [self_mem_nhdsWithin] with β hβ
      obtain ⟨hβ0, hβne⟩ : β ∈ Set.Ici 0 ∧ β ≠ β₀ :=
        ⟨hβ.1, fun hh => hβ.2 (Set.mem_singleton_iff.mpr hh)⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun h => nbMatched_ne hβ0 hβ₀ hβne
        (mul_left_cancel₀ (show (6 : ℝ) ≠ 0 by norm_num) h)
  have hTB : Tendsto (fun β => (tiltMean nbCoarse (6 * nbMatched β)
        - tiltMean nbCoarse (6 * nbMatched β₀))
        / (6 * nbMatched β - 6 * nbMatched β₀))
      (𝓝[Set.Ici 0 \ {β₀}] β₀)
      (𝓝 (-(tiltVar nbCoarse (6 * nbMatched β₀)))) := by
    have h := ((hasDerivAt_iff_tendsto_slope).mp hG).comp hu
    refine h.congr' ?_
    filter_upwards with β
    simp only [Function.comp_apply, slope_def_field]
  -- The pointwise quotient identity on the punctured domain.
  have hident : (fun β => ((tiltMean nbFine (12 * β)
          - tiltMean nbFine (12 * β₀)) / (β - β₀))
        / (6 * ((tiltMean nbCoarse (6 * nbMatched β)
            - tiltMean nbCoarse (6 * nbMatched β₀))
          / (6 * nbMatched β - 6 * nbMatched β₀))))
      =ᶠ[𝓝[Set.Ici 0 \ {β₀}] β₀]
      (fun β => (nbMatched β - nbMatched β₀) / (β - β₀)) := by
    filter_upwards [self_mem_nhdsWithin] with β hβ
    obtain ⟨hβ0, hβne⟩ : β ∈ Set.Ici 0 ∧ β ≠ β₀ :=
      ⟨hβ.1, fun hh => hβ.2 (Set.mem_singleton_iff.mpr hh)⟩
    have hmatch : tiltMean nbCoarse (6 * nbMatched β)
        = tiltMean nbFine (12 * β) := nb_match_eq hβ0
    have hΔeq : tiltMean nbCoarse (6 * nbMatched β)
          - tiltMean nbCoarse (6 * nbMatched β₀)
        = tiltMean nbFine (12 * β)
          - tiltMean nbFine (12 * β₀) := by
      rw [hmatch, hmatch₀]
    have hΔ : tiltMean nbFine (12 * β)
        - tiltMean nbFine (12 * β₀) ≠ 0 := by
      have h12 : (12 : ℝ) * β ≠ 12 * β₀ :=
        fun h => hβne (mul_left_cancel₀
          (show (12 : ℝ) ≠ 0 by norm_num) h)
      exact sub_ne_zero.mpr
        ((tiltMean_strictAnti nbFine nbFine_nonconst).injective.ne
          h12)
    have h6 : (6 : ℝ) * nbMatched β - 6 * nbMatched β₀ ≠ 0 :=
      sub_ne_zero.mpr (fun h => nbMatched_ne hβ0 hβ₀ hβne
        (mul_left_cancel₀ (show (6 : ℝ) ≠ 0 by norm_num) h))
    rw [hΔeq]
    field_simp
  have hlim : Tendsto (fun β => (nbMatched β - nbMatched β₀)
        / (β - β₀))
      (𝓝[Set.Ici 0 \ {β₀}] β₀)
      (𝓝 (((-(tiltVar nbFine (12 * β₀))) * 12)
        / (6 * (-(tiltVar nbCoarse (6 * nbMatched β₀)))))) :=
    (hTA.div (hTB.const_mul 6)
      (mul_ne_zero (by norm_num)
        (neg_ne_zero.mpr hVcpos.ne'))).congr' hident
  have hval : ((-(tiltVar nbFine (12 * β₀))) * 12)
        / (6 * (-(tiltVar nbCoarse (6 * nbMatched β₀))))
      = 2 * tiltVar nbFine (12 * β₀)
        / tiltVar nbCoarse (6 * nbMatched β₀) := by
    field_simp
    ring
  rw [hval] at hlim
  exact (hasDerivWithinAt_iff_tendsto_slope).mpr (by
    refine hlim.congr' ?_
    filter_upwards with β
    rw [slope_def_field])

/-- The matched slope at an interior point of the domain, as an
ordinary derivative. -/
theorem nbMatched_hasDerivAt {β₀ : ℝ} (hβ₀ : 0 < β₀) :
    HasDerivAt nbMatched
      (2 * tiltVar nbFine (12 * β₀)
        / tiltVar nbCoarse (6 * nbMatched β₀)) β₀ :=
  (nbMatched_hasDerivWithinAt hβ₀.le).hasDerivAt
    (Ici_mem_nhds hβ₀)

/-- The derivative of the matched projection at an interior
point. -/
theorem deriv_nbMatched {β₀ : ℝ} (hβ₀ : 0 < β₀) :
    deriv nbMatched β₀
      = 2 * tiltVar nbFine (12 * β₀)
        / tiltVar nbCoarse (6 * nbMatched β₀) :=
  (nbMatched_hasDerivAt hβ₀).deriv

/-- The within-domain derivative of the matched projection. -/
theorem derivWithin_nbMatched {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) :
    derivWithin nbMatched (Set.Ici 0) β₀
      = 2 * tiltVar nbFine (12 * β₀)
        / tiltVar nbCoarse (6 * nbMatched β₀) :=
  (nbMatched_hasDerivWithinAt hβ₀).derivWithin
    ((uniqueDiffOn_Ici 0) β₀ hβ₀)

/-- **The matched slope is strictly positive** at every domain
point: both tilt variances are strictly positive (`tiltVar_pos`,
the KD-1 discharge), so their ratio is. In agreement with the
landed strict monotonicity of the projection. -/
theorem nbMatched_slope_pos {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) :
    0 < 2 * tiltVar nbFine (12 * β₀)
      / tiltVar nbCoarse (6 * nbMatched β₀) :=
  div_pos
    (mul_pos (by norm_num) (tiltVar_pos nbFine nbFine_nonconst _))
    (tiltVar_pos nbCoarse nbCoarse_nonconst _)

/-- **The slope at the anchor `β₀ = 0`.** The general formula
evaluated at the endpoint: the fine variance sits at tilt `0`,
the coarse variance at tilt `6 * nbMatched 0` — a negative tilt
at this seat, since the anchor value `nbMatched 0` is negative
(RG-2c's `nb_anchor_neg`). One-sided (within-domain) derivative,
as the endpoint requires. -/
theorem nbMatched_zero_hasDerivWithinAt :
    HasDerivWithinAt nbMatched
      (2 * tiltVar nbFine 0
        / tiltVar nbCoarse (6 * nbMatched 0)) (Set.Ici 0) 0 := by
  have h := nbMatched_hasDerivWithinAt (β₀ := 0) (le_refl 0)
  simpa using h

/-- The anchor slope is strictly positive. -/
theorem nbMatched_zero_slope_pos :
    0 < 2 * tiltVar nbFine 0
      / tiltVar nbCoarse (6 * nbMatched 0) := by
  have h := nbMatched_slope_pos (β₀ := 0) (le_refl 0)
  simpa using h

/-- The fine tilt variance at tilt `0` is the plain (uniform)
variance of the fine density: its second moment over all fine
configurations minus the squared mean `1`
(`nb_fine_tilt_zero`). -/
theorem nbFine_tiltVar_zero :
    tiltVar nbFine 0
      = (∑ U, (nbFine U) ^ 2)
        / (Fintype.card (Config (Fin 2) (DihedralGroup 4)) : ℝ)
        - 1 := by
  have hD : tiltDen nbFine 0
      = (Fintype.card (Config (Fin 2) (DihedralGroup 4)) : ℝ) := by
    unfold tiltDen
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hS : tiltSq nbFine 0 = ∑ U, (nbFine U) ^ 2 := by
    unfold tiltSq
    exact Finset.sum_congr rfl fun U _ => by simp
  unfold tiltVar
  rw [hS, hD, nb_fine_tilt_zero, one_pow]

end MatchedSlope

end ThetLogos
