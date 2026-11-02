import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.DiscreteSubset
import ThetLogos.Shelf7bPin

/-!
# B4-FIN — finiteness of zeros in a closed subdisc (SHELF-7b-disc chain)

Brick B4-FIN of the GATE-B4 discharge campaign (scoping
`whitepaper/scoping-gate-b4-2026-11-02.md`, ingredient 3c).
This brick is the finiteness ingredient ONLY — no factorisation,
no tail work, no multiplicity bookkeeping.

## Content

For `f : ℂ → ℂ` holomorphic on the open disc of radius `R`
(`DiscHolomorphic f R`, Shelf7bPin's definition) and `mu : ℂ`,
if `g := fun z => f z - mu` is not identically zero on the open
disc, then for every `R₂ < R` the zero set
`{z ∈ closedBall 0 R₂ | f z = mu}` is finite, delivered as the
`Finset` `zeroFinsetClosedBall` with membership exactly
`z ∈ closedBall 0 R₂ ∧ f z = mu`.

Registered route (scoping 3c), followed verbatim:
1. `DifferentiableOn.analyticOnNhd` gives `g` analytic on the
   open disc.
2. `AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected`
   on the preconnected open disc: the `EqOn g 0` disjunct is the
   excluded identically-zero case; the surviving disjunct says
   `{z | g z ≠ 0}` lies in `codiscreteWithin (ball 0 R)`.
3. Transport to the closed ball: `Filter.codiscreteWithin_mono`
   along `closedBall_subset_ball` (this is the seat of
   **K-B4-FIN**), then
   `IsCompact.finite_sdiff_of_mem_codiscreteWithin` at
   `isCompact_closedBall` gives finiteness.

## Kill register

* **K-B4-FIN: DOES NOT FIRE.** The codiscrete transport glue
  (step 3) went through with the pin's API:
  `Filter.codiscreteWithin_mono` restricts codiscreteness from
  the open disc to any subset, in particular the closed ball.
  The kill was armed exactly at that step; it stayed silent.

Face fence: 7b-disc is NOT 7b-in-full. NO CLAIM; dials 0/4.
-/

namespace ThetLogos

open Filter Metric Set

noncomputable section

/-! ## 1. Analyticity transport (route step 1) -/

/-- Subtracting a constant preserves disc holomorphicity. -/
theorem discHolomorphic_sub_const {f : ℂ → ℂ} {R : ℝ} (hf : DiscHolomorphic f R)
    (mu : ℂ) : DiscHolomorphic (fun z => f z - mu) R :=
  ⟨hf.1, hf.2.sub_const mu⟩

/-- `g = f - mu` is analytic on the open disc
(`DifferentiableOn.analyticOnNhd`, route step 1). -/
theorem analyticOnNhd_sub_const {f : ℂ → ℂ} {R : ℝ} (hf : DiscHolomorphic f R)
    (mu : ℂ) : AnalyticOnNhd ℂ (fun z => f z - mu) (Metric.ball 0 R) :=
  (discHolomorphic_sub_const hf mu).2.analyticOnNhd Metric.isOpen_ball

/-! ## 2. Codiscreteness on the open disc (route step 2) -/

/-- Isolated zeros, codiscrete form: if `g = f - mu` is not
identically zero on the open disc, then the set where `g` is
nonzero is codiscrete within the open disc
(`AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected`,
route step 2). -/
theorem mem_codiscreteWithin_ball_sub_const {f : ℂ → ℂ} {R : ℝ} {mu : ℂ}
    (hf : DiscHolomorphic f R)
    (hne : ¬ Set.EqOn (fun z => f z - mu) 0 (Metric.ball 0 R)) :
    {z | f z - mu ≠ 0} ∈ Filter.codiscreteWithin (Metric.ball 0 R) := by
  rcases (analyticOnNhd_sub_const hf mu).eqOn_zero_or_eventually_ne_zero_of_preconnected
      Metric.isPreconnected_ball with h0 | hne'
  · exact absurd h0 hne
  · exact hne'

/-! ## 3. Transport to the closed ball and finiteness (route step 3;
the seat of K-B4-FIN — the glue is `Filter.codiscreteWithin_mono`) -/

/-- The zero set of `f - mu` in a closed subdisc is finite, as a
set: `closedBall 0 R₂ \ {z | g z ≠ 0}` via
`IsCompact.finite_sdiff_of_mem_codiscreteWithin`, rewritten to the
intersection form. The only radius hypothesis the route needs is
`R₂ < R`. -/
theorem finite_zeroSet_closedBall {f : ℂ → ℂ} {R R₂ : ℝ} {mu : ℂ}
    (hf : DiscHolomorphic f R) (hR₂ : R₂ < R)
    (hne : ¬ Set.EqOn (fun z => f z - mu) 0 (Metric.ball 0 R)) :
    (Metric.closedBall 0 R₂ ∩ {z | f z = mu}).Finite := by
  have hs : {z | f z - mu ≠ 0} ∈ Filter.codiscreteWithin (Metric.ball 0 R) :=
    mem_codiscreteWithin_ball_sub_const hf hne
  have hsK : {z | f z - mu ≠ 0} ∈ Filter.codiscreteWithin (Metric.closedBall 0 R₂) :=
    Filter.codiscreteWithin_mono (Metric.closedBall_subset_ball hR₂) hs
  have hfin := (isCompact_closedBall (0 : ℂ) R₂).finite_sdiff_of_mem_codiscreteWithin hsK
  have hset : Metric.closedBall 0 R₂ \ {z | f z - mu ≠ 0}
      = Metric.closedBall 0 R₂ ∩ {z | f z = mu} := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_inter_iff, ne_eq, not_not,
      sub_eq_zero]
  rwa [hset] at hfin

/-! ## 4. The Finset delivery -/

/-- The zeros of `f - mu` in the closed subdisc, as a `Finset`. -/
def zeroFinsetClosedBall {f : ℂ → ℂ} {R R₂ : ℝ} {mu : ℂ}
    (hf : DiscHolomorphic f R) (hR₂ : R₂ < R)
    (hne : ¬ Set.EqOn (fun z => f z - mu) 0 (Metric.ball 0 R)) : Finset ℂ :=
  (finite_zeroSet_closedBall hf hR₂ hne).toFinset

/-- Membership in `zeroFinsetClosedBall` is exactly
"in the closed subdisc and a zero of `f - mu`". -/
theorem mem_zeroFinsetClosedBall {f : ℂ → ℂ} {R R₂ : ℝ} {mu : ℂ}
    (hf : DiscHolomorphic f R) (hR₂ : R₂ < R)
    (hne : ¬ Set.EqOn (fun z => f z - mu) 0 (Metric.ball 0 R)) (z : ℂ) :
    z ∈ zeroFinsetClosedBall hf hR₂ hne
      ↔ z ∈ Metric.closedBall 0 R₂ ∧ f z = mu := by
  simp only [zeroFinsetClosedBall, Set.Finite.mem_toFinset, Set.mem_inter_iff,
    Set.mem_ofPred_eq]

/-- **Headline (B4-FIN).** For `f` holomorphic on the open disc
of radius `R` with `f - mu` not identically zero there, the zero
set `{z ∈ closedBall 0 R₂ | f z = mu}` is finite for every
`R₂ < R`, delivered as a `Finset` whose membership is exactly
`z ∈ closedBall 0 R₂ ∧ f z = mu`. -/
theorem finite_zeros_closedBall {f : ℂ → ℂ} {R R₂ : ℝ} {mu : ℂ}
    (hf : DiscHolomorphic f R) (hR₂ : R₂ < R)
    (hne : ¬ Set.EqOn (fun z => f z - mu) 0 (Metric.ball 0 R)) :
    ∃ s : Finset ℂ, ∀ z, z ∈ s ↔ z ∈ Metric.closedBall 0 R₂ ∧ f z = mu :=
  ⟨zeroFinsetClosedBall hf hR₂ hne, mem_zeroFinsetClosedBall hf hR₂ hne⟩

end

end ThetLogos

#print axioms ThetLogos.finite_zeros_closedBall
