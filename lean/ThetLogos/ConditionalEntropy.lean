import Mathlib.Tactic
import ThetLogos.SubsetMarginals
import ThetLogos.ConditionalEntropyPin

namespace ThetLogos

/-!
# ThetLogos.ConditionalEntropy — conditional entropy at subset level (H-2)

Content module for the pin `ConditionalEntropyPin` (frozen names
and forms). **Commission:** brick **H-2** of the priced
obstruction package in the holographic-shadow scoping
(`~/workspace/your_files/holographic-shadow-scoping-2026-11-07.md`,
§4), fired by Jeff's direct word **"build and run h-2"**
(2026-11-08). **Price: band M. NO CLAIM. Dials 0/4.
Dial-neutral, dial-ineligible.**

## What stands here

The second half of the subset-entropy vocabulary the scoping
found absent (its deciding reason for verdict (C) on the
holographic fragment): conditional entropy over H-1's subset
marginals, its chain rule, and monotonicity under
marginalization. Components:

1. **The working lemmas** (§1): a domination inequality between
   marginals — the joint marginal at `s ∪ t` is pointwise at
   most the marginal at `t`, read at the restricted
   configuration, since the union's fiber is contained in the
   conditioning region's fiber — and the sum characterization
   of `condEntropy`, obtained by refibering both entropy sums
   with H-1's `sum_margWeightSet_mul_log`, the working identity
   the H-1 pin's face names as the one H-2 consumes.
2. **Form (1)** — `condEntropy_chain`: the chain rule, the
   definition read backwards.
3. **Form (2)** — `condEntropy_nonneg`: conditional entropy of
   a probability weight is nonnegative, by the sum
   characterization and the domination inequality — on each
   configuration of positive weight, the union marginal is
   positive and dominated by the conditioning marginal, so the
   log gap is nonnegative.
4. **Form (3)** — `regionEntropy_mono`: region entropy is
   monotone under inclusion, by the chain rule at
   `t = (t ∖ s) ∪ s` plus form (2).

## Faces

- **Vocabulary, not the claim** (the pin's fence, restated):
  nothing here states an area-shaped bound, a boundary, an
  adjacency, or a locality hypothesis. `s` and `t` are any
  finsets, distinguished by nothing; the boundary-layer reading
  of the conditioning set awaits H-3, which is Jeff's design
  decision and is not touched here. Landing this brick does
  not make the holographic fragment stateable and moves no
  dial.
- **Kills (scoping §5), armed on the pin's face:** K-HOL-PROXY
  (no renaming of counting as dimension/area/gravity),
  K-HOL-INFLATE (no counting bound presented as holography or
  as a gravity object), K-HOL-DUP (prospective; this brick is
  conditional entropy over arbitrary weights — genuinely absent
  vocabulary, not product-weight additivity restated). None
  fired.
-/

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*}
  [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

/-! ## §1. Working lemmas -/

/-- **Domination between marginals:** the marginal at the union
`s ∪ t`, read at a configuration `z` of the union, is at most
the marginal at `t`, read at `z`'s restriction to `t` — the
union's fiber (configurations agreeing with `z` on all of
`s ∪ t`) is contained in `t`'s fiber (configurations agreeing
with `z` on `t`). For nonnegative weights. -/
theorem margWeightSet_union_le (w : (∀ i, X i) → ℝ)
    (hw : ∀ y, 0 ≤ w y) (s t : Finset κ) (z : ∀ i : ↥(s ∪ t), X i) :
    margWeightSet w (s ∪ t) z
      ≤ margWeightSet w t
        (fun i : t => z ⟨i, Finset.mem_union_right s i.2⟩) := by
  simp only [margWeightSet_apply]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro y hy
    rw [Finset.mem_filter] at hy ⊢
    refine ⟨hy.1, ?_⟩
    funext i
    exact congrFun hy.2 ⟨i, Finset.mem_union_right s i.2⟩
  · intro y _ _
    exact hw y

/-- **The sum characterization of conditional entropy:** the
entropy gap refibers over configurations — `condEntropy` is the
weight-averaged log ratio of the conditioning marginal to the
union marginal. Both entropy sums are refibered by H-1's
`sum_margWeightSet_mul_log`. -/
theorem condEntropy_eq_sum (w : (∀ i, X i) → ℝ) (s t : Finset κ) :
    condEntropy w s t
      = ∑ y, w y
          * (Real.log (margWeightSet w t (fun i : t => y i))
            - Real.log (margWeightSet w (s ∪ t)
                (fun i : ↥(s ∪ t) => y i))) := by
  show (-∑ z, margWeightSet w (s ∪ t) z
        * Real.log (margWeightSet w (s ∪ t) z))
      - (-∑ z, margWeightSet w t z
        * Real.log (margWeightSet w t z)) = _
  rw [sum_margWeightSet_mul_log, sum_margWeightSet_mul_log,
    neg_sub_neg, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun y _ => (mul_sub _ _ _).symm)

/-! ## §2. The chain rule (form (1)) -/

/-- **Form (1), working statement:** the chain rule — the
union's entropy is the conditioning region's entropy plus the
conditional entropy. The definition of `condEntropy` read
backwards. -/
theorem condEntropy_chain (w : (∀ i, X i) → ℝ) (s t : Finset κ) :
    regionEntropy w (s ∪ t)
      = regionEntropy w t + condEntropy w s t := by
  show regionEntropy w (s ∪ t) = regionEntropy w t
    + (regionEntropy w (s ∪ t) - regionEntropy w t)
  exact (add_sub_cancel _ _).symm

/-! ## §3. Nonnegativity (form (2)) -/

/-- **Form (2), working statement:** conditional entropy of a
probability weight is nonnegative. By the sum characterization:
on a configuration of positive weight, the union marginal is
positive (`le_margWeightSet_self`) and at most the conditioning
marginal (`margWeightSet_union_le`), so its log gap against the
conditioning marginal is nonnegative; configurations of zero
weight contribute nothing. -/
theorem condEntropy_nonneg (w : (∀ i, X i) → ℝ)
    (hw : IsProbWeight w) (s t : Finset κ) :
    0 ≤ condEntropy w s t := by
  rw [condEntropy_eq_sum]
  refine Finset.sum_nonneg (fun y _ => ?_)
  rcases eq_or_lt_of_le (hw.1 y) with hy0 | hy0
  · rw [← hy0]
    simp
  · have hle1 : w y
        ≤ margWeightSet w (s ∪ t) (fun i : ↥(s ∪ t) => y i) :=
      le_margWeightSet_self w hw.1 y (s ∪ t)
    have hpos : 0
        < margWeightSet w (s ∪ t) (fun i : ↥(s ∪ t) => y i) :=
      lt_of_lt_of_le hy0 hle1
    have hle2 : margWeightSet w (s ∪ t) (fun i : ↥(s ∪ t) => y i)
        ≤ margWeightSet w t (fun i : t => y i) :=
      margWeightSet_union_le w hw.1 s t (fun i : ↥(s ∪ t) => y i)
    have hlog : Real.log
          (margWeightSet w (s ∪ t) (fun i : ↥(s ∪ t) => y i))
        ≤ Real.log (margWeightSet w t (fun i : t => y i)) :=
      Real.log_le_log hpos hle2
    exact mul_nonneg (hw.1 y) (sub_nonneg.mpr hlog)

/-! ## §4. Monotonicity under marginalization (form (3)) -/

/-- **Form (3), working statement:** region entropy is monotone
under inclusion — a subregion's entropy is at most the larger
region's. By the chain rule at `t = (t ∖ s) ∪ s` plus
nonnegativity of the conditional entropy of the added part. -/
theorem regionEntropy_mono (w : (∀ i, X i) → ℝ)
    (hw : IsProbWeight w) {s t : Finset κ} (hst : s ⊆ t) :
    regionEntropy w s ≤ regionEntropy w t := by
  have hU : (t \ s) ∪ s = t := Finset.sdiff_union_of_subset hst
  calc regionEntropy w s
      ≤ regionEntropy w s + condEntropy w (t \ s) s :=
        le_add_of_nonneg_right (condEntropy_nonneg w hw _ _)
    _ = regionEntropy w ((t \ s) ∪ s) :=
        (condEntropy_chain w (t \ s) s).symm
    _ = regionEntropy w t := by rw [hU]

/-! ## §5. The frozen forms, assembled

The form constants are applied with named arguments
`(κ := κ) (X := X)`: in this seat a bare reference to a pin
form leaves the dependent family instance
`(i : κ) → DecidableEq (X i)` stuck on metavariables during
elaboration (the same bare idiom happens to elaborate inside
H-1's own content file, but not from a downstream module, in
this pin). Naming `κ` and `X` pins the elaboration; the
propositions proved are the pin's forms verbatim. -/

/-- **Form (1), verbatim** (the pin's `CondEntropyChainForm`). -/
theorem condEntropy_chain_form :
    CondEntropyChainForm (κ := κ) (X := X) :=
  fun w s t => condEntropy_chain w s t

/-- **Form (2), verbatim** (the pin's `CondEntropyNonnegForm`). -/
theorem condEntropy_nonneg_form :
    CondEntropyNonnegForm (κ := κ) (X := X) :=
  fun w hw s t => condEntropy_nonneg w hw s t

/-- **Form (3), verbatim** (the pin's `RegionEntropyMonoForm`). -/
theorem regionEntropy_mono_form :
    RegionEntropyMonoForm (κ := κ) (X := X) :=
  fun w hw s t h => regionEntropy_mono w hw h

end ThetLogos
