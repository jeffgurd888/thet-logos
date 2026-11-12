import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Data.Set.Disjoint
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.Tactic.Tauto

/-!
# Mizar Pilot 2 — Brick B1: XBOOLE_0 / XBOOLE_1 set algebra (continued)

Working label: MZ-W1-P2. MZ pilot wave, tranche 2, brick B1.
Source working list: the Mizar registry (XBOOLE_0 and XBOOLE_1 items drawn
for this brick: 33 items).

**NO CLAIM; dials 0/4.** This is a re-proof exercise against a foreign
registry, at restatement grade only: nothing here is counted toward the
corpus census, and no dial moves on the strength of this file.

Protocol: every item restated + proved; probe verdicts are twin-notes,
never skips. An item that resists is marked as stuck in place, never
silently dropped — all 33 identifiers appear below.

Priority credit: Mizar proved it first, in its system; we re-prove our
restatement in ours.

## Restatement idiom

Mizar sets are sets in a universe — restated here over `Set α` for an
arbitrary type `α`, with `X Y Z V … : Set α` and points `x : α`.
Mizar `\/` is `∪`, `/\` is `∩`, `\` is `\` (set difference), `c=` is `⊆`,
`c<` is `⊂` (strict inclusion), `{}` is `∅`, `x in X` is `x ∈ X`, and a
quantified "for A, B being set" becomes a quantifier over `Set α`.
Idiom choices, flagged:

* `X \+\ Y` (Mizar symmetric difference) is restated explicitly as
  `(X \ Y) ∪ (Y \ X)`, avoiding any notation whose Mathlib spelling
  might drift.
* `X misses Y` is restated as `Disjoint X Y`.
* `{x}` is the singleton set, written `{x}`.
* Mizar precedence reads are made explicit with parentheses where the
  registry text is unparenthesised (XBOOLE_1:47, XBOOLE_1:50,
  XBOOLE_1:52); see the report for the reads taken.
-/

namespace ThetLogos.MizarPilot2.B1

variable {α : Type*}

/-- after Mizar XBOOLE_0:5 — if `X` misses `Y`, a point of `X ∪ Y`
lies in exactly one of the two. -/
theorem misses_mem_union_cases {X Y : Set α} {x : α}
    (h : Disjoint X Y) (hx : x ∈ X ∪ Y) :
    (x ∈ X ∧ x ∉ Y) ∨ (x ∈ Y ∧ x ∉ X) := by
  have hdis : ∀ a : α, a ∈ X → a ∉ Y := Set.disjoint_left.mp h
  simp only [Set.mem_union] at hx
  rcases hx with hx | hx
  · left
    exact ⟨hx, hdis x hx⟩
  · right
    exact ⟨hx, fun hxX => hdis x hxX hx⟩

/-- after Mizar XBOOLE_0:6 — a strictly included set misses some point
of the larger set. -/
theorem exists_mem_not_mem_of_ssubset {X Y : Set α} (h : X ⊂ Y) :
    ∃ x : α, x ∈ Y ∧ x ∉ X := by
  by_contra hcon
  push_neg at hcon
  exact h.2 (fun x hx => hcon x hx)

/-- after Mizar XBOOLE_0:7 — a nonempty set has a point. -/
theorem exists_mem_of_ne_empty {X : Set α} (h : X ≠ ∅) :
    ∃ x : α, x ∈ X := by
  by_contra hcon
  push_neg at hcon
  exact h (Set.eq_empty_of_forall_notMem hcon)

/-- after Mizar XBOOLE_0:8 — a strict inclusion `X ⊂ Y` is witnessed
by a point `x ∈ Y` with `X ⊆ Y \ {x}`. -/
theorem exists_witness_ssubset_subset_diff_singleton {X Y : Set α}
    (h : X ⊂ Y) : ∃ x : α, x ∈ Y ∧ X ⊆ Y \ {x} := by
  obtain ⟨x, hxY, hxX⟩ := exists_mem_not_mem_of_ssubset h
  refine ⟨x, hxY, ?_⟩
  intro a ha
  refine ⟨h.1 ha, ?_⟩
  intro haSing
  simp only [Set.mem_singleton_iff] at haSing
  rw [haSing] at ha
  exact hxX ha

/-- after Mizar XBOOLE_1:32 — equal differences in both directions
force the sets equal. -/
theorem eq_of_diff_eq_diff_swap {X Y : Set α} (h : X \ Y = Y \ X) :
    X = Y := by
  ext x
  have hx := Set.ext_iff.mp h x
  simp only [Set.mem_diff] at hx
  tauto

/-- after Mizar XBOOLE_1:33 — difference is monotone in the left
argument. -/
theorem diff_subset_diff_left_of_subset {X Y Z : Set α} (h : X ⊆ Y) :
    X \ Z ⊆ Y \ Z := by
  intro x hx
  exact ⟨h hx.1, hx.2⟩

/-- after Mizar XBOOLE_1:34 — difference is antitone in the right
argument. -/
theorem diff_subset_diff_right_of_subset {X Y Z : Set α} (h : X ⊆ Y) :
    Z \ Y ⊆ Z \ X := by
  intro x hx
  exact ⟨hx.1, fun hxX => hx.2 (h hxX)⟩

/-- after Mizar XBOOLE_1:35 — difference is monotone in the left and
antitone in the right argument, jointly. -/
theorem diff_subset_diff_of_subset_of_subset {X Y Z V : Set α}
    (hXY : X ⊆ Y) (hZV : Z ⊆ V) : X \ V ⊆ Y \ Z := by
  intro x hx
  exact ⟨hXY hx.1, fun hxZ => hx.2 (hZV hxZ)⟩

/-- after Mizar XBOOLE_1:36 — a difference is included in its left
argument. (twin: `Set.sdiff_subset` — exact) -/
theorem diff_subset_self {X Y : Set α} : X \ Y ⊆ X :=
  Set.sdiff_subset

/-- after Mizar XBOOLE_1:37 — `X \ Y = ∅` iff `X ⊆ Y`.
(twin: `Set.sdiff_eq_empty` — exact) -/
theorem diff_eq_empty_iff_subset {X Y : Set α} :
    X \ Y = ∅ ↔ X ⊆ Y :=
  Set.sdiff_eq_empty

/-- after Mizar XBOOLE_1:38 — a set included in its own difference
from `Y` is empty. -/
theorem eq_empty_of_subset_diff_self {X Y : Set α} (h : X ⊆ Y \ X) :
    X = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro x hx
  have hx2 := h hx
  exact hx2.2 hx

/-- after Mizar XBOOLE_1:39 — `X ∪ (Y \ X) = X ∪ Y`. -/
theorem union_diff_self_eq_union {X Y : Set α} :
    X ∪ (Y \ X) = X ∪ Y := by
  ext x
  simp only [Set.mem_union, Set.mem_diff]
  tauto

/-- after Mizar XBOOLE_1:40 — `(X ∪ Y) \ Y = X \ Y`. -/
theorem union_diff_right_eq_diff {X Y : Set α} :
    (X ∪ Y) \ Y = X \ Y := by
  ext x
  simp only [Set.mem_diff, Set.mem_union]
  tauto

/-- after Mizar XBOOLE_1:41 — `(X \ Y) \ Z = X \ (Y ∪ Z)`. -/
theorem diff_diff_eq_diff_union {X Y Z : Set α} :
    (X \ Y) \ Z = X \ (Y ∪ Z) := by
  ext x
  simp only [Set.mem_diff, Set.mem_union]
  tauto

/-- after Mizar XBOOLE_1:42 — `(X ∪ Y) \ Z = (X \ Z) ∪ (Y \ Z)`. -/
theorem union_diff_eq_union_diff_diff {X Y Z : Set α} :
    (X ∪ Y) \ Z = (X \ Z) ∪ (Y \ Z) := by
  ext x
  simp only [Set.mem_diff, Set.mem_union]
  tauto

/-- after Mizar XBOOLE_1:43 — if `X ⊆ Y ∪ Z` then `X \ Y ⊆ Z`. -/
theorem diff_subset_of_subset_union {X Y Z : Set α} (h : X ⊆ Y ∪ Z) :
    X \ Y ⊆ Z := by
  intro x hx
  have hxYZ := h hx.1
  simp only [Set.mem_union] at hxYZ
  rcases hxYZ with hxY | hxZ
  · exact absurd hxY hx.2
  · exact hxZ

/-- after Mizar XBOOLE_1:44 — if `X \ Y ⊆ Z` then `X ⊆ Y ∪ Z`. -/
theorem subset_union_of_diff_subset {X Y Z : Set α} (h : X \ Y ⊆ Z) :
    X ⊆ Y ∪ Z := by
  intro x hxX
  by_cases hxY : x ∈ Y
  · simp only [Set.mem_union]
    left
    exact hxY
  · simp only [Set.mem_union]
    right
    exact h ⟨hxX, hxY⟩

/-- after Mizar XBOOLE_1:45 — if `X ⊆ Y` then `Y = X ∪ (Y \ X)`. -/
theorem eq_union_diff_self_of_subset {X Y : Set α} (h : X ⊆ Y) :
    Y = X ∪ (Y \ X) := by
  ext x
  have hxsub : x ∈ X → x ∈ Y := fun hx => h hx
  simp only [Set.mem_union, Set.mem_diff]
  tauto

/-- after Mizar XBOOLE_1:46 — `X \ (X ∪ Y) = ∅`. -/
theorem diff_union_self_eq_empty {X Y : Set α} :
    X \ (X ∪ Y) = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro x hx
  have hxU : x ∈ X ∪ Y := by
    simp only [Set.mem_union]
    left
    exact hx.1
  exact hx.2 hxU

/-- after Mizar XBOOLE_1:47 — `X \ (X ∩ Y) = X \ Y`
(Mizar precedence read: `\` over the intersection `X /\ Y`). -/
theorem diff_inter_self_eq_diff {X Y : Set α} :
    X \ (X ∩ Y) = X \ Y := by
  ext x
  simp only [Set.mem_diff, Set.mem_inter_iff]
  tauto

/-- after Mizar XBOOLE_1:48 — `X \ (X \ Y) = X ∩ Y`. -/
theorem diff_diff_self_eq_inter {X Y : Set α} :
    X \ (X \ Y) = X ∩ Y := by
  ext x
  simp only [Set.mem_diff, Set.mem_inter_iff]
  tauto

/-- after Mizar XBOOLE_1:49 — `X ∩ (Y \ Z) = (X ∩ Y) \ Z`. -/
theorem inter_diff_eq_inter_diff {X Y Z : Set α} :
    X ∩ (Y \ Z) = (X ∩ Y) \ Z := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_diff]
  tauto

/-- after Mizar XBOOLE_1:50 — `X ∩ (Y \ Z) = (X ∩ Y) \ (X ∩ Z)`
(Mizar precedence read: the right side is `X /\ Y \ X /\ Z` with the
difference taken between the two intersections). -/
theorem inter_diff_eq_diff_inter_inter {X Y Z : Set α} :
    X ∩ (Y \ Z) = (X ∩ Y) \ (X ∩ Z) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_diff]
  tauto

/-- after Mizar XBOOLE_1:51 — `(X ∩ Y) ∪ (X \ Y) = X`. -/
theorem inter_union_diff_self_eq_self {X Y : Set α} :
    (X ∩ Y) ∪ (X \ Y) = X := by
  ext x
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
  tauto

/-- after Mizar XBOOLE_1:52 — `X \ (Y \ Z) = (X \ Y) ∪ (X ∩ Z)`
(Mizar precedence read: the right side's second disjunct is
`X /\ Z`). -/
theorem diff_diff_eq_union_inter {X Y Z : Set α} :
    X \ (Y \ Z) = (X \ Y) ∪ (X ∩ Z) := by
  ext x
  simp only [Set.mem_diff, Set.mem_union, Set.mem_inter_iff]
  tauto

/-- after Mizar XBOOLE_1:53 — `X \ (Y ∪ Z) = (X \ Y) ∩ (X \ Z)`. -/
theorem diff_union_eq_inter_diff_diff {X Y Z : Set α} :
    X \ (Y ∪ Z) = (X \ Y) ∩ (X \ Z) := by
  ext x
  simp only [Set.mem_diff, Set.mem_union, Set.mem_inter_iff]
  tauto

/-- after Mizar XBOOLE_1:54 — `X \ (Y ∩ Z) = (X \ Y) ∪ (X \ Z)`. -/
theorem diff_inter_eq_union_diff_diff {X Y Z : Set α} :
    X \ (Y ∩ Z) = (X \ Y) ∪ (X \ Z) := by
  ext x
  simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_union]
  tauto

/-- after Mizar XBOOLE_1:55 — the symmetric difference as
`(X ∪ Y) \ (X ∩ Y) = (X \ Y) ∪ (Y \ X)`. -/
theorem union_diff_inter_eq_symm_diff {X Y : Set α} :
    (X ∪ Y) \ (X ∩ Y) = (X \ Y) ∪ (Y \ X) := by
  ext x
  simp only [Set.mem_diff, Set.mem_union, Set.mem_inter_iff]
  tauto

/-- after Mizar XBOOLE_1:56 — strict inclusion is transitive. -/
theorem ssubset_trans_of {X Y Z : Set α} (hXY : X ⊂ Y) (hYZ : Y ⊂ Z) :
    X ⊂ Z := by
  refine ⟨fun x hx => hYZ.1 (hXY.1 hx), ?_⟩
  intro hZX
  exact hYZ.2 (fun x hx => hXY.1 (hZX hx))

/-- after Mizar XBOOLE_1:57 — strict inclusion is not symmetric:
never both `X ⊂ Y` and `Y ⊂ X`. -/
theorem not_ssubset_and_ssubset_swap {X Y : Set α} :
    ¬ (X ⊂ Y ∧ Y ⊂ X) := by
  rintro ⟨hXY, hYX⟩
  exact hXY.2 hYX.1

/-- after Mizar XBOOLE_1:58 — strict inclusion followed by inclusion
is strict. -/
theorem ssubset_of_ssubset_of_subset {X Y Z : Set α} (hXY : X ⊂ Y)
    (hYZ : Y ⊆ Z) : X ⊂ Z := by
  refine ⟨fun x hx => hYZ (hXY.1 hx), ?_⟩
  intro hZX
  exact hXY.2 (fun x hx => hZX (hYZ hx))

/-- after Mizar XBOOLE_1:59 — inclusion followed by strict inclusion
is strict. -/
theorem ssubset_of_subset_of_ssubset {X Y Z : Set α} (hXY : X ⊆ Y)
    (hYZ : Y ⊂ Z) : X ⊂ Z := by
  refine ⟨fun x hx => hYZ.1 (hXY hx), ?_⟩
  intro hZX
  exact hYZ.2 (fun x hx => hXY (hZX hx))

/-- after Mizar XBOOLE_1:60 — if `X ⊆ Y` then not `Y ⊂ X`. -/
theorem not_ssubset_rev_of_subset {X Y : Set α} (h : X ⊆ Y) :
    ¬ Y ⊂ X := by
  intro hss
  exact hss.2 h

end ThetLogos.MizarPilot2.B1
