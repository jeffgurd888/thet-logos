import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range

/-!
# ThetLogos.MizarPilot1.B5 — MZ pilot wave tranche 1, brick B5: FINSEQ_1 remainder (Seg arithmetic, extensionality, concatenation)

Programme: the Mizar working list, MZ pilot wave tranche 1 brick B5
(36 FINSEQ_1 items: 1–20, 22–24, 26–32, 34, 36–40), on Zero's
2026-11-09 pilot call.
**NO CLAIM; dials 0/4.**

Protocol: every item is restated + proved here; probe verdicts are
recorded as twin-notes in the doc-comments, never as skips.
Each declaration below is a restatement, from the mathematics, of one
Mizar item, proved in this environment; its doc-comment carries the
priority credit "after Mizar ⟨ARTICLE:ordinal⟩" — Mizar proved it first,
in its system (Tarski–Grothendieck set theory); we re-proved our
restatement in ours (dependent type theory). No Mizar text appears in
this file.

Restatement idiom (tranche 1's, settled): a finite sequence is a
`List α`; `Seg n` is `Finset.range n`; `dom p` is
`Finset.range p.length`; `p ^ q` is `p ++ q`; restriction `p | A` is
`List.take`; `len p` is `p.length`; `rng p` is restated as element
membership in the list. Mizar sequence indexing is 1-based (the item
at position `i` is `p[i-1]` in Lean `getElem` terms); Mizar's `Seg n`
is the 1-based segment `{1, …, n}`, while `Finset.range n` is the
0-based `{0, …, n-1}` — items whose Mizar statement is about `Seg`
itself (FINSEQ_1:1–10) are therefore restated in range-native form,
with the shift recorded in each item's doc-comment, as tranche 1 did
for FINSEQ_2:7. D-valued / `FinSequence of D` is restated with a
predicate `P : α → Prop` holding of every element.
-/

namespace ThetLogos.MizarPilot1.B5

variable {α β : Type*}

/-- after Mizar FINSEQ_1:1 — membership in an initial segment.
Idiom shift: Mizar's `Seg b = {1, …, b}` gives `1 ≤ a ∧ a ≤ b`; the
range-native form is `a < b`. (twin: `Finset.mem_range` — exact) -/
theorem finseq1_1 {a b : ℕ} : a ∈ Finset.range b ↔ a < b :=
  Finset.mem_range

/-- after Mizar FINSEQ_1:2 — the first two initial segments.
Idiom shift: Mizar's `Seg 1 = {1}` and `Seg 2 = {1, 2}` become
`range 1 = {0}` and `range 2 = {0, 1}` in the 0-based idiom. -/
theorem finseq1_2 : Finset.range 1 = {0} ∧ Finset.range 2 = {0, 1} := by
  constructor
  · ext x
    simp only [Finset.mem_range, Finset.mem_singleton]
    omega
  · ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    omega

/-- after Mizar FINSEQ_1:3 — every positive natural lies in its own
initial segment. Idiom shift: Mizar's `a = 0 ∨ a ∈ Seg a` becomes, for
the element in 0-based position `a - 1`, `a = 0 ∨ a - 1 ∈ range a`. -/
theorem finseq1_3 {a : ℕ} : a = 0 ∨ a - 1 ∈ Finset.range a := by
  rcases Nat.eq_zero_or_pos a with h | h
  · exact Or.inl h
  · exact Or.inr (Finset.mem_range.mpr (by omega))

/-- after Mizar FINSEQ_1:4 — the top element lies in the next initial
segment. Idiom shift: Mizar's `a + 1 ∈ Seg (a + 1)` becomes
`a ∈ range (a + 1)` in the 0-based idiom. -/
theorem finseq1_4 {a : ℕ} : a ∈ Finset.range (a + 1) :=
  Finset.mem_range.mpr (Nat.lt_succ_self a)

/-- after Mizar FINSEQ_1:5 — order on naturals is inclusion of initial
segments. -/
theorem finseq1_5 {a b : ℕ} :
    a ≤ b ↔ Finset.range a ⊆ Finset.range b := by
  constructor
  · intro h x hx
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) h)
  · intro h
    by_contra hc
    push_neg at hc
    have hmem : b ∈ Finset.range a := Finset.mem_range.mpr hc
    have := h hmem
    simp only [Finset.mem_range, lt_self_iff_false] at this

/-- after Mizar FINSEQ_1:6 — equal initial segments have equal lengths.
(twin: `Finset.card_range` — via cardinality) -/
theorem finseq1_6 {a b : ℕ} (h : Finset.range a = Finset.range b) : a = b := by
  have hcard := congrArg Finset.card h
  simpa [Finset.card_range] using hcard

/-- after Mizar FINSEQ_1:7 — the smaller initial segment is the
intersection with the larger one. (twin: `Finset.range_inter_range` —
the intersection form) -/
theorem finseq1_7 {a c : ℕ} (h : c ≤ a) :
    Finset.range c = Finset.range a ∩ Finset.range c := by
  rw [Finset.range_inter_range, min_eq_right h]

/-- after Mizar FINSEQ_1:8 — if an initial segment equals its
intersection with another, it is the smaller one. -/
theorem finseq1_8 {a c : ℕ} (h : Finset.range c = Finset.range c ∩ Finset.range a) :
    c ≤ a := by
  apply finseq1_5.mpr
  intro x hx
  have hx2 : x ∈ Finset.range c ∩ Finset.range a := h ▸ hx
  exact (Finset.mem_inter.mp hx2).2

/-- after Mizar FINSEQ_1:9 — adjoining the top element extends the
segment. Idiom shift: Mizar's `Seg a ∪ {a + 1} = Seg (a + 1)` becomes
`range a ∪ {a} = range (a + 1)` in the 0-based idiom. -/
theorem finseq1_9 {a : ℕ} :
    Finset.range a ∪ {a} = Finset.range (a + 1) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_singleton]
  omega

/-- after Mizar FINSEQ_1:10 — removing the top element from the next
segment gives the segment. Idiom shift: Mizar's
`Seg k = Seg (k + 1) \ {k + 1}` becomes `range k = range (k + 1) \ {k}`
in the 0-based idiom. -/
theorem finseq1_10 {k : ℕ} :
    Finset.range k = Finset.range (k + 1) \ {k} := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]
  omega


/-- after Mizar FINSEQ_1:11 — a function whose domain is bounded by an
initial segment is (a subset of) a finite sequence. Idiom shift: in
the List idiom every list is already a finite sequence, so the content
is the length bound: a sequence whose domain sits inside `range k`
has length at most `k`, and is its own witness. -/
theorem finseq1_11 {p : List α} {k : ℕ}
    (h : Finset.range p.length ⊆ Finset.range k) :
    ∃ q : List α, q = p ∧ q.length ≤ k := by
  refine ⟨p, rfl, ?_⟩
  have hcard := Finset.card_le_card h
  simpa [Finset.card_range] using hcard

/-- after Mizar FINSEQ_1:12 — an element of a sequence is the value at
some index in its domain (Mizar's form: the element, viewed as a pair,
is `[k, p.k]` for some `k ∈ dom p`). -/
theorem finseq1_12 {p : List α} {x : α} (hx : x ∈ p) :
    ∃ k, ∃ hk : k < p.length, p[k]'hk = x :=
  List.mem_iff_getElem.mp hx

/-- after Mizar FINSEQ_1:13 — extensionality: sequences with the same
domain agreeing at every index of the domain are equal. Values are
compared through the total lookup `p[k]?` (this pin has no `List.get?`
constant, as tranche 1 recorded). -/
theorem finseq1_13 {p q : List α}
    (hdom : Finset.range p.length = Finset.range q.length)
    (h : ∀ k ∈ Finset.range p.length, p[k]? = q[k]?) : p = q := by
  have hlen : p.length = q.length := by
    have hcard := congrArg Finset.card hdom
    simpa [Finset.card_range] using hcard
  apply List.ext_getElem?
  intro k
  by_cases hk : k < p.length
  · exact h k (Finset.mem_range.mpr hk)
  · have hp : p[k]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    have hq : q[k]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [hp, hq]

/-- after Mizar FINSEQ_1:14 — extensionality in the 1-based form:
sequences of equal length agreeing at every position `k` with
`1 ≤ k ≤ len p` are equal (position `k` is index `k - 1`). -/
theorem finseq1_14 {p q : List α} (hlen : p.length = q.length)
    (h : ∀ k, 1 ≤ k → k ≤ p.length → p[k - 1]? = q[k - 1]?) : p = q := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < p.length
  · have h2 := h (i + 1) (by omega) (by omega)
    simpa using h2
  · have hp : p[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    have hq : q[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [hp, hq]

/-- after Mizar FINSEQ_1:15 — the restriction of a finite sequence to
an initial segment is a finite sequence. Idiom shift: in the List
idiom the restriction `p.take a` is a list by construction; the
content recorded here is that its length is bounded by both the bound
and the original length. (twin: `List.length_take` — the bound) -/
theorem finseq1_15 {p : List α} {a : ℕ} :
    (p.take a).length ≤ a ∧ (p.take a).length ≤ p.length := by
  rw [List.length_take]
  exact ⟨min_le_left _ _, min_le_right _ _⟩

/-- after Mizar FINSEQ_1:16 — composing a finite sequence with a
function gives a finite sequence (Mizar's hypothesis `rng p ⊆ dom f`
is vacuous for the total functions of the List idiom). The content is
length preservation. (twin: `List.length_map` — exact) -/
theorem finseq1_16 {p : List α} {f : α → β} : (p.map f).length = p.length := by
  rw [List.length_map]

/-- after Mizar FINSEQ_1:17 — restricting a sequence at a bound within
its length gives a sequence of exactly that length, with that initial
segment as domain. -/
theorem finseq1_17 {p : List α} {a : ℕ} (h : a ≤ p.length) :
    (p.take a).length = a ∧ Finset.range (p.take a).length = Finset.range a := by
  rw [List.length_take, min_eq_left h]
  exact ⟨rfl, rfl⟩

/-- after Mizar FINSEQ_1:18 — the restriction of a D-valued sequence is
D-valued (D restated as a predicate holding of every element).
(twin: `List.mem_of_mem_take` — membership in a restriction) -/
theorem finseq1_18 {p : List α} {P : α → Prop} {a : ℕ}
    (h : ∀ x ∈ p, P x) : ∀ x ∈ p.take a, P x :=
  fun x hx => h x (List.mem_of_mem_take hx)

/-- after Mizar FINSEQ_1:19 — over a nonempty D there is a D-valued
sequence of every prescribed length. (twin: `List.length_replicate` —
the constant sequence) -/
theorem finseq1_19 [Nonempty α] {a : ℕ} : ∃ p : List α, p.length = a := by
  obtain ⟨d⟩ := ‹Nonempty α›
  exact ⟨List.replicate a d, List.length_replicate⟩

/-- after Mizar FINSEQ_1:20 — a sequence is nonempty iff its length is
at least 1. -/
theorem finseq1_20 {p : List α} : p ≠ [] ↔ 1 ≤ p.length := by
  constructor
  · intro h
    cases p with
    | nil => exact absurd rfl h
    | cons a p => simp
  · intro h hp
    rw [hp] at h
    simp at h

/-- after Mizar FINSEQ_1:22 — the length of a concatenation is the sum
of the lengths. (twin: `List.length_append` — exact) -/
theorem finseq1_22 {p q : List α} : (p ++ q).length = p.length + q.length :=
  List.length_append


/-- after Mizar FINSEQ_1:23 — indexing a concatenation past the left
factor (1-based bound form): at position `k` with
`len p + 1 ≤ k ≤ len p + len q`, the value is `q`'s value at position
`k - len p`. Values are read through the total lookup at index
`k - 1`. (twin: `List.getElem?_append_right` — the index-shift form) -/
theorem finseq1_23 {p q : List α} {k : ℕ}
    (h1 : p.length + 1 ≤ k) (_h2 : k ≤ p.length + q.length) :
    (p ++ q)[k - 1]? = q[k - 1 - p.length]? :=
  List.getElem?_append_right (by omega)

/-- after Mizar FINSEQ_1:24 — indexing a concatenation past the left
factor (strict bound form): at position `k` with `len p < k ≤
len (p ^ q)`, the value is `q`'s value at position `k - len p`. For
naturals this bound is the same condition as FINSEQ_1:23's, and the
proof is the same index shift. (twin: `List.getElem?_append_right` —
the index-shift form) -/
theorem finseq1_24 {p q : List α} {k : ℕ}
    (h1 : p.length < k) (_h2 : k ≤ (p ++ q).length) :
    (p ++ q)[k - 1]? = q[k - 1 - p.length]? :=
  List.getElem?_append_right (by omega)

/-- after Mizar FINSEQ_1:26 — the domain of a sequence is included in
the domain of any concatenation extending it on the right. -/
theorem finseq1_26 {p q : List α} :
    Finset.range p.length ⊆ Finset.range (p ++ q).length := by
  intro x hx
  simp only [Finset.mem_range, List.length_append] at hx ⊢
  omega

/-- after Mizar FINSEQ_1:27 — an index of the right factor, shifted by
the left factor's length, is an index of the concatenation (the
existential form: the shifted index is `len p + k` for `k` itself). -/
theorem finseq1_27 {p q : List α} {x : ℕ} (hx : x ∈ Finset.range q.length) :
    ∃ k, k = x ∧ p.length + k ∈ Finset.range (p ++ q).length := by
  refine ⟨x, rfl, ?_⟩
  simp only [Finset.mem_range, List.length_append] at hx ⊢
  omega

/-- after Mizar FINSEQ_1:28 — an index of the right factor, shifted by
the left factor's length, is an index of the concatenation. -/
theorem finseq1_28 {p q : List α} {k : ℕ} (hk : k ∈ Finset.range q.length) :
    p.length + k ∈ Finset.range (p ++ q).length := by
  simp only [Finset.mem_range, List.length_append] at hk ⊢
  omega

/-- after Mizar FINSEQ_1:29 — the range of the left factor is included
in the range of the concatenation (`rng` restated as membership).
(twin: `List.mem_append` — the left disjunct) -/
theorem finseq1_29 {p q : List α} {x : α} (hx : x ∈ p) : x ∈ p ++ q :=
  List.mem_append.mpr (Or.inl hx)

/-- after Mizar FINSEQ_1:30 — the range of the right factor is
included in the range of the concatenation (`rng` restated as
membership). (twin: `List.mem_append` — the right disjunct) -/
theorem finseq1_30 {p q : List α} {x : α} (hx : x ∈ q) : x ∈ p ++ q :=
  List.mem_append.mpr (Or.inr hx)

/-- after Mizar FINSEQ_1:31 — the range of a concatenation is the union
of the ranges (`rng` restated as membership, union as disjunction).
(twin: `List.mem_append` — exact) -/
theorem finseq1_31 {p q : List α} {x : α} :
    x ∈ p ++ q ↔ x ∈ p ∨ x ∈ q :=
  List.mem_append

/-- after Mizar FINSEQ_1:32 — concatenation is associative.
(twin: `List.append_assoc` — exact) -/
theorem finseq1_32 {p q r : List α} : p ++ q ++ r = p ++ (q ++ r) :=
  List.append_assoc p q r

/-- after Mizar FINSEQ_1:34 — the empty sequence is a two-sided unit
for concatenation. (twins: `List.append_nil`, `List.nil_append` —
exact) -/
theorem finseq1_34 {p : List α} : p ++ [] = p ∧ [] ++ p = p :=
  ⟨List.append_nil p, List.nil_append p⟩

/-- after Mizar FINSEQ_1:36 — if a concatenation is D-valued, so are
both factors (D restated as a predicate holding of every element). -/
theorem finseq1_36 {p q : List α} {P : α → Prop}
    (h : ∀ x ∈ p ++ q, P x) :
    (∀ x ∈ p, P x) ∧ (∀ x ∈ q, P x) := by
  constructor
  · intro x hx
    exact h x (List.mem_append.mpr (Or.inl hx))
  · intro x hx
    exact h x (List.mem_append.mpr (Or.inr hx))


/-- after Mizar FINSEQ_1:37 — the one-element sequence `<*x*>` is the
singleton set of the pair `[1, x]`. Idiom shift: a Mizar sequence is
its graph (a set of index–value pairs); in the List idiom the content
is that `[x]` has length 1 and sole element `x` (at position 1, index
0). -/
theorem finseq1_37 {x : α} :
    [x].length = 1 ∧ ∀ y, y ∈ [x] ↔ y = x := by
  simp

/-- after Mizar FINSEQ_1:38 — a sequence is `<*x*>` iff its domain is
`Seg 1` and its range is `{x}` (`dom` as `Finset.range` of the length,
`rng` restated as membership). -/
theorem finseq1_38 {p : List α} {x : α} :
    p = [x] ↔ Finset.range p.length = Finset.range 1 ∧
      ∀ y, y ∈ p ↔ y = x := by
  constructor
  · intro h
    subst h
    simp
  · rintro ⟨hdom, hrng⟩
    have hl : p.length = 1 := by
      have hcard := congrArg Finset.card hdom
      simpa [Finset.card_range] using hcard
    cases p with
    | nil => simp at hl
    | cons a p =>
      cases p with
      | cons b p =>
        simp only [List.length_cons] at hl
        omega
      | nil =>
        have hax : a = x := (hrng a).mp (by simp)
        rw [hax]

/-- after Mizar FINSEQ_1:39 — a sequence is `<*x*>` iff its length is
1 and its range is `{x}` (`rng` restated as membership). -/
theorem finseq1_39 {p : List α} {x : α} :
    p = [x] ↔ p.length = 1 ∧ ∀ y, y ∈ p ↔ y = x := by
  constructor
  · intro h
    subst h
    simp
  · rintro ⟨hl, hrng⟩
    cases p with
    | nil => simp at hl
    | cons a p =>
      cases p with
      | cons b p =>
        simp only [List.length_cons] at hl
        omega
      | nil =>
        have hax : a = x := (hrng a).mp (by simp)
        rw [hax]

/-- after Mizar FINSEQ_1:40 — a sequence is `<*x*>` iff its length is
1 and its value at position 1 is `x` (position 1 is index 0 in the
0-based idiom). -/
theorem finseq1_40 {p : List α} {x : α} :
    p = [x] ↔ p.length = 1 ∧ ∀ h : 0 < p.length, p[0]'h = x := by
  constructor
  · intro h
    subst h
    simp
  · rintro ⟨hl, hval⟩
    cases p with
    | nil => simp at hl
    | cons a p =>
      cases p with
      | cons b p =>
        simp only [List.length_cons] at hl
        omega
      | nil =>
        have hax : a = x := by
          have hv := hval (show 0 < [a].length by simp)
          simpa using hv
        rw [hax]

end ThetLogos.MizarPilot1.B5
