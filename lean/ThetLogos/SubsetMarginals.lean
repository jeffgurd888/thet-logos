import Mathlib.Tactic
import ThetLogos.SubsetMarginalsPin

namespace ThetLogos

/-!
# ThetLogos.SubsetMarginals — subset marginals and region entropy (H-1)

Content module for the pin `SubsetMarginalsPin` (frozen names and
forms). **Commission:** brick **H-1** of the priced obstruction
package in the holographic-shadow scoping
(`~/workspace/your_files/holographic-shadow-scoping-2026-11-07.md`,
§4), enrolled by Jeff's **"build all you can"** (2026-11-07).
**Price: band S–M. NO CLAIM. Dials 0/4. Dial-neutral,
dial-ineligible.**

## What stands here

The subset-level marginal vocabulary the scoping found absent
(its deciding reason for verdict (C) on the holographic
fragment). Components:

1. **The subset marginal's basic theory** (§1), mirroring
   `SiteEntropyMap` §1 at subset level: the marginal is
   nonnegative (`margWeightSet_nonneg`), its total mass is the
   weight's total mass (`sum_margWeightSet`, by fibering the
   configuration sum over restrictions to `s`), a configuration's
   own weight is at most its region marginal
   (`le_margWeightSet_self`), and the marginal's entropy sum
   refibers over configurations (`sum_margWeightSet_mul_log` —
   the working identity H-2's chain rules will consume).
2. **Form (1)** — `isProbWeight_margWeightSet`: the subset
   marginal of a probability weight is a probability weight;
   `margWeightSet_prob_form` proves the pin's form verbatim.
3. **Form (2)** — `regionEntropy_nonneg`,
   `regionEntropy_le_log_card`: the region entropy's basic
   bounds, consumed from `FiniteEntropy` at the marginal
   exactly as `SiteEntropyMap` §2 consumes them for
   `siteEntropy`; `regionEntropy_bounds_form` proves the pin's
   form verbatim.
4. **Forms (3) and (4)** — `margWeightSet_singleton`,
   `regionEntropy_singleton` prove the pin's singleton forms
   verbatim: the single-site map is the singleton case of the
   subset map, at the marginal level and at the entropy level
   (the latter via `FiniteEntropy`'s relabeling invariance
   `entropyW_comp_equiv` at a proof-local evaluation
   equivalence — no new frozen name).

## Faces

- **Vocabulary, not the claim** (the pin's fence, restated):
  nothing here states an area-shaped bound, a boundary, an
  adjacency, or a locality hypothesis. A subset `s` is any
  `Finset κ`, distinguished by nothing. H-2 (conditional
  entropy, chain rules) builds on these names; H-3 (the
  locality hypothesis) is Jeff's design decision and is not
  touched here. Landing this brick does not make the
  holographic fragment stateable and moves no dial.
- **Kills (scoping §5), armed on the pin's face:** K-HOL-PROXY
  (no renaming of counting as dimension/area/gravity),
  K-HOL-INFLATE (no counting bound presented as holography or
  as a gravity object), K-HOL-DUP (no holographic-dress
  restatement of landed additivity). **None fired:** this
  brick states the genuinely absent vocabulary for arbitrary
  weights — no product hypothesis, no boundary language.
- Everything is **T1 finite information bookkeeping**: a
  finite index type `κ`, finite local state types `X i`, a
  weight on the configuration space. Zero sorrys, no
  `native_decide`; headline theorems checked against the
  standard three axioms (`propext`, `Classical.choice`,
  `Quot.sound`).
-/

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*}
  [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

/-! ## §1. The subset marginal's basic theory -/

/-- The subset marginal, unfolded: the total weight of the
configurations restricting to `z` on `s`. -/
theorem margWeightSet_apply (w : (∀ i, X i) → ℝ) (s : Finset κ)
    (z : ∀ i : s, X i) :
    margWeightSet w s z
      = ∑ y ∈ Finset.univ.filter
          (fun y => (fun i : s => y i) = z), w y := rfl

/-- Marginals of a nonnegative weight are nonnegative, at
every subset. -/
theorem margWeightSet_nonneg (w : (∀ i, X i) → ℝ)
    (hw : ∀ y, 0 ≤ w y) (s : Finset κ) (z : ∀ i : s, X i) :
    0 ≤ margWeightSet w s z :=
  Finset.sum_nonneg (fun y _ => hw y)

/-- The total mass of a subset marginal is the total mass of
the weight: fibering the configuration sum over the
restriction map to `s`. -/
theorem sum_margWeightSet (w : (∀ i, X i) → ℝ) (s : Finset κ) :
    ∑ z, margWeightSet w s z = ∑ y, w y := by
  have h := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (∀ i, X i)))
    (t := (Finset.univ : Finset (∀ i : s, X i)))
    (g := fun y : (∀ i, X i) => fun i : s => y i)
    (f := w) (fun y _ => Finset.mem_univ _)
  exact h

/-- **Form (1), working statement:** subset marginals of a
probability weight are probability weights. -/
theorem isProbWeight_margWeightSet (w : (∀ i, X i) → ℝ)
    (hw : IsProbWeight w) (s : Finset κ) :
    IsProbWeight (margWeightSet w s) :=
  ⟨fun z => margWeightSet_nonneg w hw.1 s z, by
    rw [sum_margWeightSet]; exact hw.2⟩

/-- A configuration's own weight is at most its marginal at
any region containing its restriction: the fiber over `y`'s
restriction to `s` contains `y` itself. -/
theorem le_margWeightSet_self (w : (∀ i, X i) → ℝ)
    (hw : ∀ y, 0 ≤ w y) (y : ∀ i, X i) (s : Finset κ) :
    w y ≤ margWeightSet w s (fun i : s => y i) := by
  rw [margWeightSet_apply]
  apply Finset.single_le_sum (fun z _ => hw z)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, rfl⟩

/-- The subset marginal's entropy sum, refibered over
configurations: on each fiber the marginal factor is
constant. The working identity H-2's chain rules consume;
the subset analog of `sum_margWeight_mul_log`. -/
theorem sum_margWeightSet_mul_log (w : (∀ i, X i) → ℝ)
    (s : Finset κ) :
    ∑ z, margWeightSet w s z * Real.log (margWeightSet w s z)
      = ∑ y, w y
        * Real.log (margWeightSet w s (fun i : s => y i)) := by
  have h := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (∀ i, X i)))
    (t := (Finset.univ : Finset (∀ i : s, X i)))
    (g := fun y : (∀ i, X i) => fun i : s => y i)
    (f := fun y => w y
      * Real.log (margWeightSet w s (fun i : s => y i)))
    (fun y _ => Finset.mem_univ _)
  rw [← h]
  apply Finset.sum_congr rfl
  intro z _
  have step : ∀ y ∈ Finset.univ.filter
        (fun y => (fun i : s => y i) = z),
      w y * Real.log (margWeightSet w s (fun i : s => y i))
        = w y * Real.log (margWeightSet w s z) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    rw [hy.2]
  rw [Finset.sum_congr rfl step, ← Finset.sum_mul,
    ← margWeightSet_apply]

/-! ## §2. The region entropy's basic bounds (form (2)) -/

/-- Region entropy is nonnegative. -/
theorem regionEntropy_nonneg (w : (∀ i, X i) → ℝ)
    (hw : IsProbWeight w) (s : Finset κ) :
    0 ≤ regionEntropy w s :=
  entropyW_nonneg (isProbWeight_margWeightSet w hw s)

/-- Region entropy is at most the log of the region's
configuration count. -/
theorem regionEntropy_le_log_card (w : (∀ i, X i) → ℝ)
    (hw : IsProbWeight w) (s : Finset κ) :
    regionEntropy w s
      ≤ Real.log (Fintype.card (∀ i : s, X i) : ℝ) :=
  entropyW_le_log_card (isProbWeight_margWeightSet w hw s)

/-! ## §3. Singleton recovery (forms (3) and (4)) -/

/-- **Form (3), verbatim:** the subset marginal at the
singleton `{i}` is the single-site marginal, read at the
subtype configuration's unique coordinate. The two fiber
predicates agree: a configuration restricts to `z` on `{i}`
iff its `i`-th coordinate is `z`'s unique coordinate. -/
theorem margWeightSet_singleton :
    MargWeightSetSingletonForm (κ := κ) (X := X) := by
  intro w i z
  have hfil : Finset.univ.filter
        (fun y : (∀ i, X i) =>
          (fun j : ({i} : Finset κ) => y j) = z)
      = Finset.univ.filter
        (fun y : (∀ i, X i) => y i
          = z ⟨i, Finset.mem_singleton_self i⟩) := by
    apply Finset.filter_congr
    intro y _
    constructor
    · intro h
      exact congrFun h ⟨i, Finset.mem_singleton_self i⟩
    · intro h
      funext j
      obtain rfl : j = ⟨i, Finset.mem_singleton_self i⟩ :=
        Subtype.ext (Finset.mem_singleton.mp j.2)
      exact h
  rw [margWeightSet_apply, margWeight_apply, hfil]

/-- **Form (4), verbatim:** the entropy of the singleton
region `{i}` is the site entropy at `i`. Route: form (3)
identifies the subset marginal with the single-site marginal
composed with evaluation at the unique coordinate, and
`entropyW_comp_equiv` (landed relabeling invariance) closes
at the evaluation equivalence, built proof-locally. -/
theorem regionEntropy_singleton :
    RegionEntropySingletonForm (κ := κ) (X := X) := by
  intro w i
  let e : (∀ j : ({i} : Finset κ), X j) ≃ X i :=
    { toFun := fun z => z ⟨i, Finset.mem_singleton_self i⟩
      invFun := fun x j =>
        cast (congrArg X (Finset.mem_singleton.mp j.2)).symm x
      left_inv := by
        intro z
        funext j
        obtain rfl : j = ⟨i, Finset.mem_singleton_self i⟩ :=
          Subtype.ext (Finset.mem_singleton.mp j.2)
        rfl
      right_inv := by
        intro x
        rfl }
  have hcomp : (fun z => margWeight w i (e z))
      = margWeightSet w {i} := by
    funext z
    exact (margWeightSet_singleton w i z).symm
  show entropyW (margWeightSet w {i})
    = entropyW (margWeight w i)
  rw [← hcomp]
  exact entropyW_comp_equiv (margWeight w i) e

/-! ## §4. The frozen forms, assembled -/

/-- **Form (1), verbatim** (the pin's `MargWeightSetProbForm`). -/
theorem margWeightSet_prob_form :
    MargWeightSetProbForm (κ := κ) (X := X) :=
  fun w s hw => isProbWeight_margWeightSet w hw s

/-- **Form (2), verbatim** (the pin's
`RegionEntropyBoundsForm`). -/
theorem regionEntropy_bounds_form :
    RegionEntropyBoundsForm (κ := κ) (X := X) :=
  fun w s hw => ⟨regionEntropy_nonneg w hw s,
    regionEntropy_le_log_card w hw s⟩

end ThetLogos
