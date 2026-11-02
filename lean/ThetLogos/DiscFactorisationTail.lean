import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.DSlope
import ThetLogos.DiscZeroFiniteness
import ThetLogos.DiscCoeffProduct

/-!
# B4-TAIL — multiplicity factorisation + tail identification (SHELF-7b-disc)

Brick B4-TAIL of the GATE-B4 discharge campaign (scoping
`whitepaper/scoping-gate-b4-2026-11-02.md`, ingredients 3d/3e;
pack `routeb-general-scratch/pack-gate-b4-tail.md`).

## Verdict shape — read this first

**FULL.** The pre-named PARTIAL seam (multiplicity + termination
resisting) does NOT trigger: the pin (Mathlib v4.35.0-rc3) provides
exactly the named API — `analyticOrderNatAt` (the order of
vanishing, `Mathlib.Analysis.Analytic.Order`) and the iterated
`dslope` factorisation (`HasFPowerSeriesAt.eq_pow_order_mul_iterate_dslope`,
`HasFPowerSeriesAt.iterate_dslope_fslope_ne_zero`). Termination is
not an argument we make: the multiplicity at a point *is*
`analyticOrderNatAt`, and the `order`-fold `dslope` iterate removes
it in one step, with the nonzero-tail fact landed by Mathlib.

## Content

For `f` with `DiscHolomorphic f R`, `mu : ℂ`, `g := fun z => f z - mu`
not identically zero on `ball 0 R`, and `0 < R₀ < R₂ < R`:

1. THE LIST (`discFactorisationTail`): `lam` is the list of zeros of
   `g` in `closedBall 0 R₂` WITH multiplicity — its support is
   exactly `zeroFinsetClosedBall` (B4-FIN) and
   `lam.count l = analyticOrderNatAt g l` at each zero.
2. THE FACTORISATION: a remainder `h`, `DiscHolomorphic h R`,
   zero-free on `closedBall 0 R₂`, with the *global* identity
   `g z = (lam.map (fun l => z - l)).prod * h z` (the pack asks for
   it on `ball 0 R`; the `dslope` identity is global, so the
   stronger form is what lands).
3. THE COEFFICIENT IDENTITY at `R₀`
   (`discCoeff_factorisationTail`): B4-PROD applied once to the
   global factorisation:
   `discCoeff g R₀ = discConv (discCoeff (linear-factor product) R₀)
   (discCoeff h R₀)`.
4. Summability transport for ASM is NOT reproved here (pack 3e):
   it is B2's landed `summable_norm_smul_pow_discCoeff_interior`
   applied to `h` at `R₀`, using `discHolomorphic_factorisationTail`
   below.

## Route

* Single point, full multiplicity (`discFactorStep`): at `l` in the
  disc, with `m := analyticOrderNatAt F l` and
  `G := (swap dslope l)^[m] F`, the series-level identity
  `HasFPowerSeriesAt.eq_pow_order_mul_iterate_dslope` gives
  `F z = (z - l)^m * G z` for all `z`, once `m` is identified with
  the presenting series' `order` through
  `AnalyticAt.analyticOrderNatAt_eq_iff`. `dslope` preserves
  `AnalyticOnNhd` on the disc (`analyticOnNhd_dslope_ball`: at the
  centre by `has_fpower_series_dslope_fslope`, off-centre because
  `dslope` agrees with the slope, an analytic expression, near any
  other point).
* Distinct points (`exists_discFactorisation_of_list`): induction
  over the distinct-zero list. The step re-derives the multiplicity
  of the *current tail* at the next zero from the multiplicity of
  `g` itself, via `analyticOrderNatAt_mul` and the fact that the
  already-removed factor is a unit at the next (distinct) point.
  Invariants carried: analyticity, not-identically-zero, the
  factorisation, nonvanishing at already-removed points, and the
  zero-set off the removed list.
* Assembly: the distinct list is `zeroFinsetClosedBall`'s `toList`;
  `lam` is its `flatMap` of `replicate (analyticOrderNatAt g l) l`,
  and the list-product of linear factors is the product of powers
  (`prod_map_flatMap_replicate`).

Face fence: 7b-disc is NOT 7b-in-full. NO CLAIM; dials 0/4.
-/

namespace ThetLogos

open Filter Metric Set
open scoped Topology

noncomputable section

/-! ## 1. `dslope` preserves analyticity on the disc -/

/-- One `dslope` step at a centre inside the disc preserves
`AnalyticOnNhd` on the disc: at the centre this is
`HasFPowerSeriesAt.has_fpower_series_dslope_fslope`; at any other
point `dslope F l` agrees near the point with the slope
`z ↦ (z - l)⁻¹ * (F z - F l)`, which is analytic there. -/
theorem analyticOnNhd_dslope_ball {F : ℂ → ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.ball 0 R)) {l : ℂ}
    (hl : l ∈ Metric.ball 0 R) :
    AnalyticOnNhd ℂ (dslope F l) (Metric.ball 0 R) := by
  intro x hx
  by_cases hxl : x = l
  · subst hxl
    obtain ⟨p, hp⟩ := hF x hx
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have hev : dslope F l =ᶠ[𝓝 x] fun z => (z - l)⁻¹ * (F z - F l) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds
        (show x ∈ {l}ᶜ from by simpa using hxl)] with z hz
      have hz' : z ≠ l := Set.mem_compl_singleton_iff.mp hz
      rw [dslope_of_ne F hz']
      show (z - l)⁻¹ • (F z - F l) = (z - l)⁻¹ * (F z - F l)
      rw [smul_eq_mul]
    exact AnalyticAt.congr
      (((analyticAt_id.sub analyticAt_const).inv
        (sub_ne_zero.mpr hxl)).mul ((hF x hx).sub analyticAt_const)) hev.symm

/-- Iterated `dslope` at a centre inside the disc preserves
`AnalyticOnNhd` on the disc. -/
theorem analyticOnNhd_iterate_dslope_ball {F : ℂ → ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.ball 0 R)) {l : ℂ}
    (hl : l ∈ Metric.ball 0 R) (m : ℕ) :
    AnalyticOnNhd ℂ ((Function.swap dslope l)^[m] F) (Metric.ball 0 R) := by
  induction m generalizing F with
  | zero => simpa using hF
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact analyticOnNhd_dslope_ball (ih hF) hl

/-! ## 2. Not identically zero on the disc → not locally zero -/

/-- If an analytic-on-the-disc function is not `EqOn 0` on the
(preconnected) disc, it is not locally zero at any disc point:
the identity theorem
`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`. -/
theorem not_eventuallyEq_zero_of_not_eqOn_ball {F : ℂ → ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.ball 0 R))
    (hne : ¬ Set.EqOn F 0 (Metric.ball 0 R))
    {x : ℂ} (hx : x ∈ Metric.ball 0 R) :
    ¬ ∀ᶠ z in 𝓝 x, F z = 0 := by
  intro hloc
  apply hne
  refine hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    Metric.isPreconnected_ball hx ?_
  rw [Filter.EventuallyEq]
  filter_upwards [hloc] with z hz
  simpa using hz

/-- Hence the analytic order at any disc point is finite
(not `⊤`). -/
theorem analyticOrderAt_ne_top_of_not_eqOn_ball {F : ℂ → ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.ball 0 R))
    (hne : ¬ Set.EqOn F 0 (Metric.ball 0 R))
    {x : ℂ} (hx : x ∈ Metric.ball 0 R) :
    analyticOrderAt F x ≠ ⊤ :=
  fun h => not_eventuallyEq_zero_of_not_eqOn_ball hF hne hx
    (analyticOrderAt_eq_top.mp h)

/-! ## 3. The single-zero step, at full multiplicity -/

/-- **The single-zero step (full multiplicity).** Let `F` be
analytic on the disc, `l` a disc point, `F` not locally zero at
`l`. With `m := analyticOrderNatAt F l` (the order of vanishing)
and `G := (swap dslope l)^[m] F` (the `m`-fold `dslope` tail):
`G` is analytic on the disc, `F z = (z - l)^m * G z` for *all* `z`,
`G l ≠ 0`, and off `l` the zeros of `G` are exactly those of `F`.
Termination is the pin's `order`: `m` is identified with the
presenting series' `FormalMultilinearSeries.order` through
`AnalyticAt.analyticOrderNatAt_eq_iff`, and the factorisation and
the nonvanishing are `HasFPowerSeriesAt.eq_pow_order_mul_iterate_dslope`
and `HasFPowerSeriesAt.iterate_dslope_fslope_ne_zero`. -/
theorem discFactorStep {F : ℂ → ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.ball 0 R)) {l : ℂ}
    (hl : l ∈ Metric.ball 0 R)
    (hnl : ¬ ∀ᶠ z in 𝓝 l, F z = 0) :
    AnalyticOnNhd ℂ ((Function.swap dslope l)^[analyticOrderNatAt F l] F)
        (Metric.ball 0 R)
      ∧ (∀ z, F z = (z - l) ^ analyticOrderNatAt F l
          * (Function.swap dslope l)^[analyticOrderNatAt F l] F z)
      ∧ (Function.swap dslope l)^[analyticOrderNatAt F l] F l ≠ 0
      ∧ (∀ w ≠ l, ((Function.swap dslope l)^[analyticOrderNatAt F l] F w = 0
          ↔ F w = 0)) := by
  obtain ⟨p, hp⟩ := hF l hl
  have hp0 : p ≠ 0 := fun h => hnl (hp.locally_zero_iff.mpr h)
  have hfin : analyticOrderAt F l ≠ ⊤ :=
    fun h => hnl (analyticOrderAt_eq_top.mp h)
  have hm : analyticOrderNatAt F l = p.order := by
    rw [AnalyticAt.analyticOrderNatAt_eq_iff ⟨p, hp⟩ hfin]
    exact ⟨(Function.swap dslope l)^[p.order] F,
      ⟨_, hp.has_fpower_series_iterate_dslope_fslope p.order⟩,
      hp.iterate_dslope_fslope_ne_zero hp0,
      Filter.Eventually.of_forall fun z => hp.eq_pow_order_mul_iterate_dslope z⟩
  refine ⟨analyticOnNhd_iterate_dslope_ball hF hl _, fun z => ?_,
    ?_, fun w hw => ?_⟩
  · rw [hm]
    have h := hp.eq_pow_order_mul_iterate_dslope z
    rwa [smul_eq_mul] at h
  · rw [hm]
    exact hp.iterate_dslope_fslope_ne_zero hp0
  · have hfact : F w = (w - l) ^ analyticOrderNatAt F l
        * (Function.swap dslope l)^[analyticOrderNatAt F l] F w := by
      rw [hm]
      have h := hp.eq_pow_order_mul_iterate_dslope w
      rwa [smul_eq_mul] at h
    constructor
    · intro hG
      rw [hfact, hG, mul_zero]
    · intro hFw
      have hpow : (w - l) ^ analyticOrderNatAt F l ≠ 0 :=
        pow_ne_zero _ (sub_ne_zero.mpr hw)
      rw [hfact] at hFw
      exact (mul_eq_zero.mp hFw).resolve_left hpow

/-! ## 4. Helpers for the product of already-removed factors -/

/-- The product of powers of distinct linear factors is analytic
at every point. -/
theorem analyticAt_prod_sub_pow (L : List ℂ) (e : ℂ → ℕ) (x : ℂ) :
    AnalyticAt ℂ (fun z => (L.map fun l => (z - l) ^ e l).prod) x := by
  induction L with
  | nil =>
    show AnalyticAt ℂ (fun _ => (1 : ℂ)) x
    exact analyticAt_const
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    exact ((analyticAt_id.sub analyticAt_const).pow _).mul ih

/-- The product of powers of linear factors `(a - l)`, `l ∈ L`,
is nonzero at a point `a ∉ L`. -/
theorem prod_sub_pow_ne_zero_of_not_mem {a : ℂ} (L : List ℂ) (e : ℂ → ℕ)
    (ha : a ∉ L) :
    (L.map fun l => (a - l) ^ e l).prod ≠ 0 := by
  induction L with
  | nil => simp
  | cons b t ih =>
    simp only [List.map_cons, List.prod_cons, ne_eq, mul_ne_zero_iff]
    refine ⟨pow_ne_zero _ ?_, ih (fun h => ha (List.mem_cons_of_mem b h))⟩
    have hb : a ≠ b := fun h => ha (h ▸ List.mem_cons_self)
    exact sub_ne_zero.mpr hb

/-! ## 5. Iteration over a list of distinct zeros -/

/-- **Iteration over distinct zeros.** Let `g` be analytic on the
disc and not identically zero there, and let `L` be a nodup list
of disc points at which `g` vanishes. Then there is a tail `h`,
analytic on the disc and not identically zero there, with
`g z = (∏ l ∈ L, (z - l) ^ (analyticOrderNatAt g l)) * h z` for
all `z`, `h` nonzero at every point of `L`, and the zeros of `h`
off `L` exactly those of `g`.

The step's multiplicity bookkeeping: the tail-so-far's order at
the next zero equals `g`'s own order there, because the
already-removed factor is analytic and nonzero at that (distinct)
point, so `analyticOrderNatAt_mul` contributes `0` from it. -/
theorem exists_discFactorisation_of_list {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 R))
    (hgne : ¬ Set.EqOn g 0 (Metric.ball 0 R)) :
    ∀ (L : List ℂ), L.Nodup → (∀ l ∈ L, l ∈ Metric.ball 0 R) →
      (∀ l ∈ L, g l = 0) →
      ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (Metric.ball 0 R)
        ∧ ¬ Set.EqOn h 0 (Metric.ball 0 R)
        ∧ (∀ z, g z = ((L.map fun l => (z - l) ^ analyticOrderNatAt g l).prod) * h z)
        ∧ (∀ l ∈ L, h l ≠ 0)
        ∧ (∀ w, w ∉ L → (h w = 0 ↔ g w = 0)) := by
  intro L
  induction L with
  | nil =>
    intro _ _ _
    exact ⟨g, hg, hgne, fun z => by simp, fun l hl => by simp at hl,
      fun w _ => Iff.rfl⟩
  | cons a t ih =>
    intro hnodup hball hzero
    have ha_notin : a ∉ t := List.nodup_cons.mp hnodup |>.1
    have ht_nodup : t.Nodup := List.nodup_cons.mp hnodup |>.2
    have ha_ball : a ∈ Metric.ball 0 R := hball a List.mem_cons_self
    have ha_zero : g a = 0 := hzero a List.mem_cons_self
    obtain ⟨F, hFan, hFne, hFfact, hFne0, hFeq⟩ := ih ht_nodup
      (fun l hl => hball l (List.mem_cons_of_mem a hl))
      (fun l hl => hzero l (List.mem_cons_of_mem a hl))
    -- The multiplicity of the current tail `F` at `a` equals `g`'s.
    have hFa : F a = 0 := (hFeq a ha_notin).mpr ha_zero
    have hnl : ¬ ∀ᶠ z in 𝓝 a, F z = 0 :=
      not_eventuallyEq_zero_of_not_eqOn_ball hFan hFne ha_ball
    set Q : ℂ → ℂ := fun z => (t.map fun l => (z - l) ^ analyticOrderNatAt g l).prod with hQ
    have hQan : AnalyticAt ℂ Q a := analyticAt_prod_sub_pow t _ a
    have hQa : Q a ≠ 0 := prod_sub_pow_ne_zero_of_not_mem t _ ha_notin
    have hQord : analyticOrderNatAt Q a = 0 := by
      have h0 : analyticOrderAt Q a = 0 :=
        (AnalyticAt.analyticOrderAt_eq_zero hQan).mpr hQa
      simp [analyticOrderNatAt, h0]
    have hQfin : analyticOrderAt Q a ≠ ⊤ := by
      rw [show analyticOrderAt Q a = 0 from (AnalyticAt.analyticOrderAt_eq_zero hQan).mpr hQa]
      exact ENat.zero_ne_top
    have hFfin : analyticOrderAt F a ≠ ⊤ :=
      analyticOrderAt_ne_top_of_not_eqOn_ball hFan hFne ha_ball
    have hgfin : analyticOrderAt g a ≠ ⊤ :=
      analyticOrderAt_ne_top_of_not_eqOn_ball hg hgne ha_ball
    have hmul := analyticOrderNatAt_mul hQan (hFan a ha_ball) hQfin hFfin
    have hQF : Q * F = g := by
      funext z
      rw [Pi.mul_apply]
      exact (hFfact z).symm
    rw [hQF, hQord, zero_add] at hmul
    -- hmul : analyticOrderNatAt g a = analyticOrderNatAt F a
    obtain ⟨hGan, hGfact, hGa, hGzeros⟩ := discFactorStep hFan ha_ball hnl
    rw [← hmul] at hGan hGfact hGa hGzeros
    refine ⟨(Function.swap dslope a)^[analyticOrderNatAt g a] F, hGan, ?_, ?_, ?_, ?_⟩
    · -- The new tail is not identically zero on the disc.
      intro hEq
      apply hFne
      intro z hz
      rw [hGfact z]
      have hz0 : (Function.swap dslope a)^[analyticOrderNatAt g a] F z = 0 := by
        have h := hEq hz
        simpa using h
      rw [hz0, mul_zero]
      rfl
    · -- The factorisation over `a :: t`.
      intro z
      rw [hFfact z, hGfact z]
      simp only [List.map_cons, List.prod_cons]
      ring
    · -- Nonvanishing at every removed point.
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hlt
      · exact hGa
      · have hFl : F l ≠ 0 := hFne0 l hlt
        intro hGl
        apply hFl
        rw [hGfact l, hGl, mul_zero]
    · -- The zero set off the removed list is unchanged.
      intro w hw
      have hwne : w ≠ a := fun h => hw (h ▸ List.mem_cons_self)
      have hwt : w ∉ t := fun h => hw (List.mem_cons_of_mem a h)
      exact (hGzeros w hwne).trans (hFeq w hwt)

/-! ## 6. List combinatorics for `lam` -/

/-- The product of the linear factors over the flat-mapped
replicate list is the product of the powers over the distinct
list. -/
theorem prod_map_flatMap_replicate (L : List ℂ) (e : ℂ → ℕ) (z : ℂ) :
    ((L.flatMap fun l => List.replicate (e l) l).map fun l => z - l).prod
      = (L.map fun l => (z - l) ^ e l).prod := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.flatMap_cons, List.map_append, List.prod_append,
      List.map_replicate, List.prod_replicate, List.map_cons, List.prod_cons, ih]

/-- Counting in the flat-mapped replicate list over a nodup list:
each distinct zero occurs exactly `e l` times. -/
theorem count_flatMap_replicate_of_nodup (L : List ℂ) (e : ℂ → ℕ)
    (hL : L.Nodup) (x : ℂ) :
    (L.flatMap fun l => List.replicate (e l) l).count x
      = if x ∈ L then e x else 0 := by
  induction L with
  | nil => simp
  | cons a t ih =>
    have ha_notin : a ∉ t := List.nodup_cons.mp hL |>.1
    have ht_nodup : t.Nodup := List.nodup_cons.mp hL |>.2
    rw [List.flatMap_cons, List.count_append, List.count_replicate, ih ht_nodup]
    by_cases hxa : x = a
    · subst hxa
      simp [ha_notin]
    · have hxt : (if x ∈ t then e x else 0) = if x ∈ a :: t then e x else 0 := by
        by_cases h : x ∈ t
        · simp [h, List.mem_cons_of_mem _ h]
        · have h2 : x ∉ a :: t := by
            intro hm
            rcases List.mem_cons.mp hm with h1 | h1
            · exact hxa h1
            · exact h h1
          simp [h, h2]
      rw [hxt]
      simp [hxa, Ne.symm hxa]

/-- The linear-factor product function is disc-holomorphic at
any positive radius (it is a polynomial). -/
theorem discHolomorphic_prod_sub_linear (L : List ℂ) {R : ℝ} (hR : 0 < R) :
    DiscHolomorphic (fun z => (L.map fun l => z - l).prod) R := by
  refine ⟨hR, ?_⟩
  have hd : Differentiable ℂ (fun z => (L.map fun l => z - l).prod) := by
    induction L with
    | nil =>
      show Differentiable ℂ (fun _ => (1 : ℂ))
      exact differentiable_const 1
    | cons a t ih =>
      simp only [List.map_cons, List.prod_cons]
      exact (differentiable_id.sub_const a).mul ih
  exact hd.differentiableOn

/-! ## 7. Assembly: the list, the tail, the factorisation -/

/-- **Headline (B4-TAIL).** For `f` disc-holomorphic on the disc
of radius `R`, `g = f - mu` not identically zero there, and
`0 < R₀ < R₂ < R`: there are a list `lam : List ℂ` and a tail
`h : ℂ → ℂ` such that

* `lam` is the zero list of `g` in `closedBall 0 R₂` WITH
  multiplicity: `lam.count l = analyticOrderNatAt g l` for
  `l ∈ zeroFinsetClosedBall` (B4-FIN's Finset) and `0` off it,
  and the support of `lam` is exactly that Finset;
* `DiscHolomorphic h R` and `h` is zero-free on `closedBall 0 R₂`;
* the factorisation `g z = (lam.map (fun l => z - l)).prod * h z`
  holds for all `z` (in particular on `ball 0 R`, as the pack
  asks).

The coefficient identity at `R₀` is
`discCoeff_factorisationTail` below. -/
theorem discFactorisationTail {f : ℂ → ℂ} {R R₀ R₂ : ℝ} {mu : ℂ}
    (hf : DiscHolomorphic f R)
    (hne : ¬ Set.EqOn (fun z => f z - mu) 0 (Metric.ball 0 R))
    (hR₀ : 0 < R₀) (hR₀₂ : R₀ ≤ R₂) (hR₂ : R₂ < R) :
    ∃ (lam : List ℂ) (h : ℂ → ℂ),
      (∀ l, lam.count l
        = if l ∈ zeroFinsetClosedBall hf hR₂ hne
          then analyticOrderNatAt (fun z => f z - mu) l else 0)
      ∧ (∀ l, l ∈ lam ↔ l ∈ zeroFinsetClosedBall hf hR₂ hne)
      ∧ DiscHolomorphic h R
      ∧ (∀ z ∈ Metric.closedBall 0 R₂, h z ≠ 0)
      ∧ (∀ z, f z - mu = (lam.map fun l => z - l).prod * h z) := by
  classical
  set s := zeroFinsetClosedBall hf hR₂ hne with hs
  set g : ℂ → ℂ := fun z => f z - mu with hg_def
  have hg : AnalyticOnNhd ℂ g (Metric.ball 0 R) := analyticOnNhd_sub_const hf mu
  have hgne : ¬ Set.EqOn g 0 (Metric.ball 0 R) := hne
  have hLball : ∀ l ∈ s.toList, l ∈ Metric.ball 0 R := by
    intro l hl
    have hls : l ∈ s := Finset.mem_toList.mp hl
    have hmem := (mem_zeroFinsetClosedBall hf hR₂ hne l).mp hls
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact lt_of_le_of_lt (by
      have h2 : l ∈ Metric.closedBall 0 R₂ := hmem.1
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h2) hR₂
  have hLzero : ∀ l ∈ s.toList, g l = 0 := by
    intro l hl
    have hls : l ∈ s := Finset.mem_toList.mp hl
    have hmem := (mem_zeroFinsetClosedBall hf hR₂ hne l).mp hls
    show f l - mu = 0
    rw [hmem.2, sub_self]
  obtain ⟨h, hhan, hhne, hfact, hhne0, hheq⟩ :=
    exists_discFactorisation_of_list hg hgne s.toList s.nodup_toList hLball hLzero
  refine ⟨s.toList.flatMap fun l => List.replicate (analyticOrderNatAt g l) l,
    h, ?_, ?_, ⟨hf.1, hhan.differentiableOn⟩, ?_, ?_⟩
  · intro l
    have hcount := count_flatMap_replicate_of_nodup s.toList
      (fun l => analyticOrderNatAt g l) s.nodup_toList l
    simp only [Finset.mem_toList] at hcount
    exact hcount
  · intro l
    constructor
    · intro hl
      rw [List.mem_flatMap] at hl
      obtain ⟨a, ha, hla⟩ := hl
      obtain ⟨-, rfl⟩ := List.mem_replicate.mp hla
      exact Finset.mem_toList.mp ha
    · intro hl
      have hls : l ∈ s.toList := Finset.mem_toList.mpr hl
      have hgl : g l = 0 := hLzero l hls
      have hAn : AnalyticAt ℂ g l := hg l (hLball l hls)
      have hfin : analyticOrderAt g l ≠ ⊤ :=
        analyticOrderAt_ne_top_of_not_eqOn_ball hg hgne (hLball l hls)
      have hpos : 0 < analyticOrderNatAt g l := by
        by_contra hcon
        have h0 : analyticOrderNatAt g l = 0 := Nat.eq_zero_of_not_pos hcon
        have hord0 : analyticOrderAt g l = 0 := by
          have hcast := Nat.cast_analyticOrderNatAt hfin
          rw [h0, Nat.cast_zero] at hcast
          exact hcast.symm
        have hne0 : g l ≠ 0 := (AnalyticAt.analyticOrderAt_eq_zero hAn).mp hord0
        exact hne0 hgl
      rw [List.mem_flatMap]
      exact ⟨l, hls, List.mem_replicate.mpr ⟨ne_of_gt hpos, rfl⟩⟩
  · -- Zero-free on the closed subdisc.
    intro z hz
    by_cases hzs : z ∈ s.toList
    · exact hhne0 z hzs
    · intro hz0
      have hgz : g z = 0 := (hheq z hzs).mp hz0
      have hzmem : z ∈ s :=
        (mem_zeroFinsetClosedBall hf hR₂ hne z).mpr ⟨hz, sub_eq_zero.mp hgz⟩
      exact hzs (Finset.mem_toList.mpr hzmem)
  · -- The factorisation, in `lam` form.
    intro z
    have h := hfact z
    rw [← prod_map_flatMap_replicate s.toList (fun l => analyticOrderNatAt g l) z] at h
    exact h

/-- The tail of `discFactorisationTail`, packaged for B2's
summability transport (`summable_norm_smul_pow_discCoeff_interior`
at an interior radius): this `DiscHolomorphic h R` is the form
ASM consumes for `Summable (fun n => ‖discCoeff h R₀ n • a ^ n‖)`
under `spectralRadius < R₀`. The transport itself is B2's landed
lemma, not reproved here (pack 3e). -/
theorem discHolomorphic_factorisationTail {f : ℂ → ℂ} {R R₂ : ℝ} {mu : ℂ}
    (hf : DiscHolomorphic f R) (hR₂0 : 0 < R₂) (hR₂ : R₂ < R)
    (hne : ¬ Set.EqOn (fun z => f z - mu) 0 (Metric.ball 0 R)) :
    ∃ (lam : List ℂ) (h : ℂ → ℂ), DiscHolomorphic h R
      ∧ (∀ z ∈ Metric.closedBall 0 R₂, h z ≠ 0)
      ∧ (∀ z, f z - mu = (lam.map fun l => z - l).prod * h z) := by
  obtain ⟨lam, h, -, -, hhol, hfree, hfact⟩ :=
    discFactorisationTail hf hne hR₂0 (le_refl R₂) hR₂
  exact ⟨lam, h, hhol, hfree, hfact⟩

/-! ## 8. The coefficient identity at the interior radius `R₀` -/

/-- **Coefficient identity (B4-TAIL, part 3).** With `lam` and
`h` as in `discFactorisationTail`, B4-PROD
(`discCoeff_mul`) applied to the global factorisation gives, at
every interior presenting radius `R₀` with `0 < R₀ < R`,
`discCoeff g R₀ = discConv (discCoeff (linear-factor product) R₀)
(discCoeff h R₀)`. This is the shape B4-ASM consumes; the fully
iterated form over the individual linear factors is obtained by
re-applying `discCoeff_mul` to the product factor, whose
coefficients are those of a polynomial. -/
theorem discCoeff_factorisationTail {f : ℂ → ℂ} {R R₀ R₂ : ℝ} {mu : ℂ}
    (hf : DiscHolomorphic f R)
    (hne : ¬ Set.EqOn (fun z => f z - mu) 0 (Metric.ball 0 R))
    (hR₀ : 0 < R₀) (hR₀₂ : R₀ ≤ R₂) (hR₂ : R₂ < R) :
    ∃ (lam : List ℂ) (h : ℂ → ℂ),
      DiscHolomorphic h R
      ∧ (∀ z ∈ Metric.closedBall 0 R₂, h z ≠ 0)
      ∧ (∀ z, f z - mu = (lam.map fun l => z - l).prod * h z)
      ∧ discCoeff (fun z => f z - mu) R₀
        = discConv (discCoeff (fun z => (lam.map fun l => z - l).prod) R₀)
            (discCoeff h R₀) := by
  obtain ⟨lam, h, -, -, hhhol, hhfree, hfact⟩ :=
    discFactorisationTail hf hne hR₀ hR₀₂ hR₂
  have hR₀R : R₀ < R := lt_of_le_of_lt hR₀₂ hR₂
  have hfun : (fun z => f z - mu) = (fun z => (lam.map fun l => z - l).prod * h z) :=
    funext hfact
  refine ⟨lam, h, hhhol, hhfree, hfact, ?_⟩
  rw [hfun]
  exact discCoeff_mul (discHolomorphic_prod_sub_linear lam hf.1) hhhol hR₀ hR₀R

end

end ThetLogos

#print axioms ThetLogos.discFactorisationTail
#print axioms ThetLogos.discCoeff_factorisationTail
