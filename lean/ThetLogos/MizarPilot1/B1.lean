import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Tauto

/-!
# Mizar Pilot 1 — Brick B1: XBOOLE_0 / XBOOLE_1 set algebra

MZ pilot wave, tranche 1, brick B1 — after Zero's 2026-11-09 pilot call.
Source working list: the Mizar registry (XBOOLE_0 and XBOOLE_1 items drawn
for this brick: 37 items).

**NO CLAIM; dials 0/4.** This is a re-proof exercise against a foreign
registry, at restatement grade only: nothing here is counted toward the
corpus census, and no dial moves on the strength of this file.

Protocol: every item restated + proved; probe verdicts are twin-notes,
never skips. An item that resists is marked as stuck in place, never
silently dropped — all 37 identifiers appear below.

Priority credit: Mizar proved it first, in its system; we re-prove our
restatement in ours.

## Restatement idiom

Mizar sets are sets in a universe — restated here over `Set α` for an
arbitrary type `α`, with `A B C … : Set α` and points `x : α`.
Mizar `\/` is `∪`, `/\` is `∩`, `\` is `\` (set difference), `c=` is `⊆`,
`c<` is `⊂` (strict inclusion), `{}` is `∅`, and a quantified
"for A, B being set" becomes a quantifier over `Set α`.
Two idiom choices, flagged:

* `X \+\ Y` (Mizar symmetric difference) is restated explicitly as
  `(X \ Y) ∪ (Y \ X)`, avoiding any notation whose Mathlib spelling
  might drift.
* `X meets Y` is restated as `(X ∩ Y).Nonempty`.
-/

namespace ThetLogos.MizarPilot1.B1

variable {α : Type*}

/-- after Mizar XBOOLE_0:1 — a point lies in the symmetric difference
iff it does not lie in both-or-neither. -/
theorem mem_symm_diff_iff {X Y : Set α} {x : α} :
    x ∈ (X \ Y) ∪ (Y \ X) ↔ ¬ (x ∈ X ↔ x ∈ Y) := by
  simp only [Set.mem_union, Set.mem_diff]
  tauto

/-- after Mizar XBOOLE_0:2 — a set whose non-membership is pointwise
equivalent to agreement of `Y` and `Z` is the symmetric difference. -/
theorem eq_symm_diff_of_forall {X Y Z : Set α}
    (h : ∀ x : α, (¬ x ∈ X) ↔ (x ∈ Y ↔ x ∈ Z)) : X = (Y \ Z) ∪ (Z \ Y) := by
  ext x
  have hx := h x
  simp only [Set.mem_union, Set.mem_diff]
  tauto

/-- after Mizar XBOOLE_0:3 — `X` meets `Y` iff some point lies in
both. -/
theorem meets_iff_exists_mem {X Y : Set α} :
    (X ∩ Y).Nonempty ↔ ∃ x : α, x ∈ X ∧ x ∈ Y := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (Set.mem_inter_iff x X Y).mp hx⟩
  · rintro ⟨x, hxX, hxY⟩
    exact ⟨x, (Set.mem_inter_iff x X Y).mpr ⟨hxX, hxY⟩⟩

/-- after Mizar XBOOLE_0:4 — `X` meets `Y` iff some point lies in
`X ∩ Y`. -/
theorem meets_iff_exists_mem_inter {X Y : Set α} :
    (X ∩ Y).Nonempty ↔ ∃ x : α, x ∈ X ∩ Y := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, hx⟩

/-- after Mizar XBOOLE_1:1 — inclusion is transitive.
(twin: `Set.Subset.trans` — near-exact) -/
theorem subset_trans_of {X Y Z : Set α} (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) :
    X ⊆ Z := by
  intro x hx
  exact hYZ (hXY hx)

/-- after Mizar XBOOLE_1:2 — the empty set is included in every set.
(twin: `Set.empty_subset` — exact) -/
theorem empty_subset_any {X : Set α} : (∅ : Set α) ⊆ X :=
  Set.empty_subset X

/-- after Mizar XBOOLE_1:3 — a set included in the empty set is
empty. -/
theorem eq_empty_of_subset_empty {X : Set α} (h : X ⊆ ∅) : X = ∅ :=
  Set.Subset.antisymm h (Set.empty_subset X)

/-- after Mizar XBOOLE_1:4 — union is associative.
(twin: `Set.union_assoc` — exact) -/
theorem union_assoc_three {X Y Z : Set α} : (X ∪ Y) ∪ Z = X ∪ (Y ∪ Z) :=
  Set.union_assoc X Y Z

/-- after Mizar XBOOLE_1:5 — `(X ∪ Y) ∪ Z = (X ∪ Z) ∪ (Y ∪ Z)`. -/
theorem union_union_self_right {X Y Z : Set α} :
    (X ∪ Y) ∪ Z = (X ∪ Z) ∪ (Y ∪ Z) := by
  ext x
  simp only [Set.mem_union]
  tauto

/-- after Mizar XBOOLE_1:6 — `X ∪ (X ∪ Y) = X ∪ Y`. -/
theorem union_absorb_union_left {X Y : Set α} : X ∪ (X ∪ Y) = X ∪ Y := by
  ext x
  simp only [Set.mem_union]
  tauto

/-- after Mizar XBOOLE_1:7 — a set is included in its union with any
set. (twin: `Set.subset_union_left` — exact) -/
theorem subset_union_left_any {X Y : Set α} : X ⊆ X ∪ Y :=
  Set.subset_union_left

/-- after Mizar XBOOLE_1:8 — two sets included in `Z` have their union
included in `Z`. (twin: `Set.union_subset` — near-exact) -/
theorem union_subset_of_both {X Y Z : Set α} (hX : X ⊆ Z) (hY : Y ⊆ Z) :
    X ∪ Y ⊆ Z := by
  intro x hx
  simp only [Set.mem_union] at hx
  rcases hx with hx | hx
  · exact hX hx
  · exact hY hx

/-- after Mizar XBOOLE_1:9 — inclusion is monotone in the left union
argument. -/
theorem union_subset_union_left_of {X Y Z : Set α} (h : X ⊆ Y) :
    X ∪ Z ⊆ Y ∪ Z := by
  intro x hx
  simp only [Set.mem_union] at hx ⊢
  rcases hx with hx | hx
  · left
    exact h hx
  · right
    exact hx

/-- after Mizar XBOOLE_1:10 — if `X ⊆ Y` then `X` is included in
`Z ∪ Y`. -/
theorem subset_union_right_of {X Y Z : Set α} (h : X ⊆ Y) : X ⊆ Z ∪ Y := by
  intro x hx
  simp only [Set.mem_union]
  right
  exact h hx

/-- after Mizar XBOOLE_1:11 — if `X ∪ Y ⊆ Z` then `X ⊆ Z`. -/
theorem subset_of_union_subset {X Y Z : Set α} (h : X ∪ Y ⊆ Z) : X ⊆ Z := by
  intro x hx
  apply h
  simp only [Set.mem_union]
  left
  exact hx

/-- after Mizar XBOOLE_1:12 — if `X ⊆ Y` then `X ∪ Y = Y`. -/
theorem union_eq_of_subset {X Y : Set α} (h : X ⊆ Y) : X ∪ Y = Y := by
  ext x
  simp only [Set.mem_union]
  constructor
  · rintro (hx | hx)
    · exact h hx
    · exact hx
  · intro hx
    right
    exact hx

/-- after Mizar XBOOLE_1:13 — union is monotone in both arguments. -/
theorem union_subset_union_of {X Y Z V : Set α} (hXY : X ⊆ Y) (hZV : Z ⊆ V) :
    X ∪ Z ⊆ Y ∪ V := by
  intro x hx
  simp only [Set.mem_union] at hx ⊢
  rcases hx with hx | hx
  · left
    exact hXY hx
  · right
    exact hZV hx

/-- after Mizar XBOOLE_1:14 — a set containing both `Y` and `Z`, and
included in every common container of them, is `Y ∪ Z`. -/
theorem eq_union_of_least {X Y Z : Set α} (hYX : Y ⊆ X) (hZX : Z ⊆ X)
    (hmin : ∀ V : Set α, Y ⊆ V → Z ⊆ V → X ⊆ V) : X = Y ∪ Z :=
  Set.Subset.antisymm
    (hmin (Y ∪ Z) Set.subset_union_left Set.subset_union_right)
    (by
      intro x hx
      simp only [Set.mem_union] at hx
      rcases hx with hx | hx
      · exact hYX hx
      · exact hZX hx)

/-- after Mizar XBOOLE_1:15 — if `X ∪ Y = ∅` then `X = ∅`. -/
theorem eq_empty_of_union_eq_empty {X Y : Set α} (h : X ∪ Y = ∅) : X = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro x hx
  have hx2 : x ∈ X ∪ Y := by
    simp only [Set.mem_union]
    left
    exact hx
  rw [h] at hx2
  exact hx2

/-- after Mizar XBOOLE_1:16 — intersection is associative.
(twin: `Set.inter_assoc` — exact) -/
theorem inter_assoc_three {X Y Z : Set α} : (X ∩ Y) ∩ Z = X ∩ (Y ∩ Z) :=
  Set.inter_assoc X Y Z

/-- after Mizar XBOOLE_1:17 — an intersection is included in its left
factor. (twin: `Set.inter_subset_left` — exact) -/
theorem inter_subset_left_any {X Y : Set α} : X ∩ Y ⊆ X :=
  Set.inter_subset_left

/-- after Mizar XBOOLE_1:18 — a set included in `Y ∩ Z` is included
in `Y`. -/
theorem subset_left_of_subset_inter {X Y Z : Set α} (h : X ⊆ Y ∩ Z) :
    X ⊆ Y := by
  intro x hx
  exact (h hx).1

/-- after Mizar XBOOLE_1:19 — a set included in both `X` and `Y` is
included in `X ∩ Y`. -/
theorem subset_inter_of_both {X Y Z : Set α} (hX : Z ⊆ X) (hY : Z ⊆ Y) :
    Z ⊆ X ∩ Y := by
  intro x hx
  exact ⟨hX hx, hY hx⟩

/-- after Mizar XBOOLE_1:20 — a set included in both `Y` and `Z`, and
containing every common subset of them, is `Y ∩ Z`. -/
theorem eq_inter_of_greatest {X Y Z : Set α} (hXY : X ⊆ Y) (hXZ : X ⊆ Z)
    (hmax : ∀ V : Set α, V ⊆ Y → V ⊆ Z → V ⊆ X) : X = Y ∩ Z :=
  Set.Subset.antisymm
    (by
      intro x hx
      exact ⟨hXY hx, hXZ hx⟩)
    (hmax (Y ∩ Z) Set.inter_subset_left Set.inter_subset_right)

/-- after Mizar XBOOLE_1:21 — absorption: `X ∩ (X ∪ Y) = X`. -/
theorem inter_union_absorb {X Y : Set α} : X ∩ (X ∪ Y) = X := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_union]
  tauto

/-- after Mizar XBOOLE_1:22 — absorption: `X ∪ (X ∩ Y) = X`. -/
theorem union_inter_absorb {X Y : Set α} : X ∪ (X ∩ Y) = X := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_union]
  tauto

/-- after Mizar XBOOLE_1:23 — intersection distributes over union on
the left. (twin: `Set.inter_union_distrib_left` — near-exact) -/
theorem inter_union_distrib {X Y Z : Set α} :
    X ∩ (Y ∪ Z) = X ∩ Y ∪ X ∩ Z := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_union]
  tauto

/-- after Mizar XBOOLE_1:24 — union distributes over intersection on
the left: `X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z)`.
(twin: `Set.union_inter_distrib_left` — near-exact) -/
theorem union_inter_distrib {X Y Z : Set α} :
    X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_union]
  tauto

/-- after Mizar XBOOLE_1:25 — the median identity:
`(X ∩ Y) ∪ (Y ∩ Z) ∪ (Z ∩ X) = (X ∪ Y) ∩ (Y ∪ Z) ∩ (Z ∪ X)`. -/
theorem median_identity {X Y Z : Set α} :
    (X ∩ Y) ∪ (Y ∩ Z) ∪ (Z ∩ X) = (X ∪ Y) ∩ (Y ∪ Z) ∩ (Z ∪ X) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_union]
  tauto

/-- after Mizar XBOOLE_1:26 — inclusion is monotone in the left
intersection argument. -/
theorem inter_subset_inter_left_of {X Y Z : Set α} (h : X ⊆ Y) :
    X ∩ Z ⊆ Y ∩ Z := by
  intro x hx
  exact ⟨h hx.1, hx.2⟩

/-- after Mizar XBOOLE_1:27 — intersection is monotone in both
arguments. -/
theorem inter_subset_inter_of {X Y Z V : Set α} (hXY : X ⊆ Y) (hZV : Z ⊆ V) :
    X ∩ Z ⊆ Y ∩ V := by
  intro x hx
  exact ⟨hXY hx.1, hZV hx.2⟩

/-- after Mizar XBOOLE_1:28 — if `X ⊆ Y` then `X ∩ Y = X`. -/
theorem inter_eq_of_subset {X Y : Set α} (h : X ⊆ Y) : X ∩ Y = X := by
  ext x
  simp only [Set.mem_inter_iff]
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact ⟨hx, h hx⟩

/-- after Mizar XBOOLE_1:29 — `X ∩ Y` is included in `X ∪ Z`. -/
theorem inter_subset_union_any {X Y Z : Set α} : X ∩ Y ⊆ X ∪ Z := by
  intro x hx
  simp only [Set.mem_union]
  left
  exact hx.1

/-- after Mizar XBOOLE_1:30 — if `X ⊆ Z` then
`X ∪ (Y ∩ Z) = (X ∪ Y) ∩ Z`. -/
theorem union_inter_eq_of_subset {X Y Z : Set α} (h : X ⊆ Z) :
    X ∪ (Y ∩ Z) = (X ∪ Y) ∩ Z := by
  ext x
  have hxZ : x ∈ X → x ∈ Z := fun hx => h hx
  simp only [Set.mem_inter_iff, Set.mem_union]
  tauto

/-- after Mizar XBOOLE_1:31 — `(X ∩ Y) ∪ (X ∩ Z)` is included in
`Y ∪ Z`. -/
theorem union_inter_subset {X Y Z : Set α} :
    (X ∩ Y) ∪ (X ∩ Z) ⊆ Y ∪ Z := by
  intro x hx
  simp only [Set.mem_union, Set.mem_inter_iff] at hx ⊢
  rcases hx with hx | hx
  · left
    exact hx.2
  · right
    exact hx.2

/-- after Mizar XBOOLE_1:61 — a nonempty set strictly contains the
empty set: `X ≠ ∅` implies `∅ ⊂ X`. -/
theorem empty_ssubset_of_ne_empty {X : Set α} (h : X ≠ ∅) : ∅ ⊂ X := by
  refine ⟨Set.empty_subset X, ?_⟩
  intro hsub
  exact h (Set.Subset.antisymm hsub (Set.empty_subset X))

/-- after Mizar XBOOLE_1:62 — no set is strictly included in the empty
set. -/
theorem not_ssubset_empty {X : Set α} : ¬ X ⊂ ∅ := by
  intro h
  exact h.2 (Set.empty_subset X)

end ThetLogos.MizarPilot1.B1
