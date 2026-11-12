import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range

/-!
# ThetLogos.MizarPilot1.B6 — MZ pilot tranche 1, brick B6: FINSEQ_2 remainder (max/Seg arithmetic, D-valued sequences, composition)

Programme: the Mizar working list, MZ pilot tranche 1 brick B6
(30 FINSEQ_2 items: 3–5, 8–16, 18, 19, 23–28, 30–33, 35–40), on
Zero's 2026-11-09 pilot call.
**NO CLAIM; dials 0/4.**

Protocol: every item restated + proved; twin verdicts are twin-notes,
never skips. An item that resists is marked as stuck in place, never
silently dropped — all 30 identifiers appear below.
Each declaration below is a restatement, from the mathematics, of one
Mizar item, proved in this environment; its doc-comment carries the
priority credit "after Mizar ⟨ARTICLE:ordinal⟩" — Mizar proved it first,
in its system (Tarski–Grothendieck set theory); we re-proved our
restatement in ours (dependent type theory). No Mizar text appears in
this file.

Restatement idiom (tranche 1's, settled): a finite sequence is a
`List α`; `Seg n` is `Finset.range n`; `dom p` is
`Finset.range p.length`; `p ^ q` is `p ++ q`; restriction is
`List.take`; `len p` is `p.length`; `rng p` is restated as element
membership in the list. Mizar indexing is 1-based (the item at
position `i` is `p[i-1]` in Lean `getElem` terms); statements below
are in the 0-based range-native form, with the shift recorded per
item where it matters.
FINSEQ_2 also treats sequences over a fixed set `D` (`FinSequence
of D`): two restatements are used, recorded per item — either
`List α` with a membership hypothesis `∀ x ∈ p, x ∈ D` (for
`D : Set α`), or `List D` (lists over the subtype `↥D`), where the
valuedness is carried by the type itself.
Mizar's `i - j` in FINSEQ_2:3–5 is integer subtraction (the result
is truncated at `0` by the `max`), so those items are restated over
`ℤ`.
-/

namespace ThetLogos.MizarPilot1.B6

variable {α β : Type*}

/-- after Mizar FINSEQ_2:3 — if `i ≤ j` then the truncated difference
`max(0, i - j)` is `0`. Idiom shift: Mizar's subtraction here is
integer subtraction, restated over `ℤ`. -/
theorem finseq2_3 {i j : ℤ} (h : i ≤ j) : max 0 (i - j) = 0 :=
  max_eq_left (by omega)

/-- after Mizar FINSEQ_2:4 — if `j ≤ i` then the truncated difference
`max(0, i - j)` is the plain difference `i - j`. Idiom shift as in
FINSEQ_2:3: restated over `ℤ`. -/
theorem finseq2_4 {i j : ℤ} (h : j ≤ i) : max 0 (i - j) = i - j :=
  max_eq_right (by omega)

/-- after Mizar FINSEQ_2:5 — the truncated difference `max(0, i - j)`
is a natural number. Idiom shift: "is an element of NAT" is restated
as the existence of a natural casting to it. -/
theorem finseq2_5 {i j : ℤ} : ∃ n : ℕ, max 0 (i - j) = (n : ℤ) :=
  ⟨(max 0 (i - j)).toNat, (Int.toNat_of_nonneg (le_max_left 0 (i - j))).symm⟩

/-- after Mizar FINSEQ_2:8 — an index in `Seg l` is an index in the
longer segment `Seg (l + j)`. Range-native form: membership in
`Finset.range l` gives membership in `Finset.range (l + j)`. -/
theorem finseq2_8 {i l j : ℕ} (h : i ∈ Finset.range l) :
    i ∈ Finset.range (l + j) :=
  Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp h) (Nat.le_add_right l j))

/-- after Mizar FINSEQ_2:9 — extensionality: sequences of equal
length agreeing at every index of the domain are equal. Idiom
shift: Mizar's 1-based `p.j` for `j ∈ dom p` is the 0-based
`p[j]` for `j < p.length` here. -/
theorem finseq2_9 {p q : List α} (hlen : p.length = q.length)
    (h : ∀ j : ℕ, ∀ hj : j < p.length, p[j] = q[j]'(hlen ▸ hj)) : p = q :=
  List.ext_getElem hlen (fun j hj₁ _ => h j hj₁)

/-- after Mizar FINSEQ_2:10 — every element of the range of `p`
occurs at some index of the domain. Idiom shift: `rng p` is list
membership, and Mizar's 1-based index is the 0-based `getElem`
index here. -/
theorem finseq2_10 {p : List α} {b : α} (hb : b ∈ p) :
    ∃ i : ℕ, ∃ hi : i < p.length, p[i] = b := by
  obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp hb
  exact ⟨i, hi, hia⟩

/-- after Mizar FINSEQ_2:11 — an entry of a `D`-valued sequence lies
in `D`. Restatement choice: `D`-valued is `List ↥D` (lists over the
subtype), so the entry's value lies in `D` by its subtype
property. -/
theorem finseq2_11 {D : Set α} {p : List D} {j : ℕ} (hj : j < p.length) :
    (p[j] : α) ∈ D :=
  (p[j]).property

/-- after Mizar FINSEQ_2:12 — a sequence all of whose entries lie in
`D` is a sequence of `D`. Restatement choice: the conclusion is the
existence of a `List ↥D` (subtype-valued list) mapping back onto
`p` under `Subtype.val`. -/
theorem finseq2_12 {D : Set α} {p : List α}
    (h : ∀ j : ℕ, ∀ hj : j < p.length, p[j] ∈ D) :
    ∃ q : List D, q.map Subtype.val = p := by
  have key : ∀ r : List α, (∀ j : ℕ, ∀ hj : j < r.length, r[j] ∈ D) →
      ∃ q : List D, q.map Subtype.val = r := by
    intro r
    induction r with
    | nil => intro _; exact ⟨[], rfl⟩
    | cons a p ih =>
      intro hr
      have ha : a ∈ D := hr 0 (by simp)
      have hp : ∀ j : ℕ, ∀ hj : j < p.length, p[j] ∈ D := by
        intro j hj
        have hstep := hr (j + 1) (by
          show j + 1 < p.length + 1
          omega)
        rwa [List.getElem_cons_succ] at hstep
      obtain ⟨q, hq⟩ := ih hp
      exact ⟨⟨a, ha⟩ :: q, by simp [hq]⟩
  exact key p h

/-- after Mizar FINSEQ_2:13 — a two-element sequence of elements of
`D` is a sequence of `D`. Restatement choice: `FinSequence of D`
as the membership predicate on `List α`. -/
theorem finseq2_13 {D : Set α} {d₁ d₂ : α} (h₁ : d₁ ∈ D) (h₂ : d₂ ∈ D) :
    ∀ x ∈ [d₁, d₂], x ∈ D := by
  intro x hx
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact h₁
  · exact h₂

/-- after Mizar FINSEQ_2:14 — a three-element sequence of elements
of `D` is a sequence of `D`. Restatement choice as in
FINSEQ_2:13. -/
theorem finseq2_14 {D : Set α} {d₁ d₂ d₃ : α}
    (h₁ : d₁ ∈ D) (h₂ : d₂ ∈ D) (h₃ : d₃ ∈ D) :
    ∀ x ∈ [d₁, d₂, d₃], x ∈ D := by
  intro x hx
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact h₁
  · exact h₂
  · exact h₃

/-- after Mizar FINSEQ_2:15 — an index of `p` is an index of the
concatenation `p ^ q`. -/
theorem finseq2_15 {p q : List α} {i : ℕ} (h : i ∈ Finset.range p.length) :
    i ∈ Finset.range (p ++ q).length :=
  Finset.mem_range.mpr (by
    have hi := Finset.mem_range.mp h
    rw [List.length_append]
    omega)

/-- after Mizar FINSEQ_2:16 — appending a singleton adds one to the
length. (twin: `List.length_append` — exact, with
`List.length_singleton`) -/
theorem finseq2_16 {p : List α} {a : α} : (p ++ [a]).length = p.length + 1 := by
  rw [List.length_append, List.length_singleton]

/-- after Mizar FINSEQ_2:18 — a sequence of length `i + 1` is a
sequence with a last element appended. -/
theorem finseq2_18 {p : List α} {i : ℕ} (h : p.length = i + 1) :
    ∃ q : List α, ∃ a : α, p = q ++ [a] := by
  have key : ∀ r : List α, r ≠ [] → ∃ q : List α, ∃ a : α, r = q ++ [a] := by
    intro r
    induction r with
    | nil => intro hne; exact absurd rfl hne
    | cons x xs ih =>
      intro _
      cases xs with
      | nil => exact ⟨[], x, rfl⟩
      | cons y ys =>
        obtain ⟨q, a, hq⟩ := ih (List.cons_ne_nil y ys)
        exact ⟨x :: q, a, by simp [hq]⟩
  exact key p (by
    intro hp
    rw [hp] at h
    simp at h)

/-- after Mizar FINSEQ_2:19 — a nonempty sequence over a set `A`
is a sequence over `A` with a last element of `A` appended.
Restatement choice: sequences over `A` are `List ↥A`, so the
decomposition stays inside the subtype. -/
theorem finseq2_19 {A : Set α} {p : List A} (h : p.length ≠ 0) :
    ∃ q : List A, ∃ d : A, p = q ++ [d] := by
  have key : ∀ r : List A, r ≠ [] → ∃ q : List A, ∃ d : A, r = q ++ [d] := by
    intro r
    induction r with
    | nil => intro hne; exact absurd rfl hne
    | cons x xs ih =>
      intro _
      cases xs with
      | nil => exact ⟨[], x, rfl⟩
      | cons y ys =>
        obtain ⟨q, d, hq⟩ := ih (List.cons_ne_nil y ys)
        exact ⟨x :: q, d, by simp [hq]⟩
  exact key p (by
    intro hp
    apply h
    rw [hp]
    rfl)

/-- after Mizar FINSEQ_2:23 — a `D`-valued sequence of length
`i + j` splits into `D`-valued factors of lengths `i` and `j`.
Restatement choice: `List ↥D`, so `take`/`drop` stay valued. -/
theorem finseq2_23 {D : Set α} {r : List D} {i j : ℕ} (h : r.length = i + j) :
    ∃ p q : List D, p.length = i ∧ q.length = j ∧ r = p ++ q := by
  refine ⟨r.take i, r.drop i, ?_, ?_, (List.take_append_drop i r).symm⟩
  · rw [List.length_take, h]
    exact min_eq_left (by omega)
  · rw [List.length_drop, h]
    omega

/-- after Mizar FINSEQ_2:24 — a sequence valued in a subset `D₁`
of `D` is a sequence valued in `D`. Restatement choice: the
conclusion is a `List ↥D` with the same underlying values and
length as the given `List ↥D₁`. -/
theorem finseq2_24 {D D₁ : Set α} (hsub : D₁ ⊆ D) {p : List D₁} :
    ∃ q : List D, q.map Subtype.val = p.map Subtype.val ∧ q.length = p.length := by
  refine ⟨p.map (fun x => ⟨x.val, hsub x.property⟩), ?_, by rw [List.length_map]⟩
  simp [List.map_map]

/-- after Mizar FINSEQ_2:25 — a function on `Seg i` with values in
`D` is a sequence of `D`. Restatement choice: the function is
`Fin i → ↥D` and its sequence is `List.ofFn f`; the recorded
content is its length and that every entry lies in `D`. -/
theorem finseq2_25 {D : Set α} {i : ℕ} {f : Fin i → D} :
    (List.ofFn f).length = i ∧ ∀ x ∈ List.ofFn f, (x : α) ∈ D :=
  ⟨List.length_ofFn, fun x _ => x.property⟩

/-- after Mizar FINSEQ_2:26 — a sequence of `D` is a function of
its domain into `D`. Restatement choice: the function is the
`Fin p.length`-indexed lookup into the `List ↥D`. -/
theorem finseq2_26 {D : Set α} {p : List D} :
    ∃ g : Fin p.length → D, ∀ j : Fin p.length, g j = p[j.val]'j.isLt :=
  ⟨fun j => p[j.val]'j.isLt, fun _ => rfl⟩

/-- after Mizar FINSEQ_2:27 — restricting a sequence of `D` to
`Seg i` gives a sequence of `D`. Restatement choice: the ambient
sequence is `ℕ → ↥D` and restriction to `Seg i` is mapping it
over `List.range i`; every entry of the restriction lies in `D`
by its subtype property. -/
theorem finseq2_27 {D : Set α} {f : ℕ → D} {i : ℕ} :
    ∀ x ∈ (List.range i).map f, (x : α) ∈ D := by
  intro x hx
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp hx
  exact (f n).property

/-- after Mizar FINSEQ_2:28 — the restriction of a sequence to
`Seg i` has length `i`. Restatement choice as in FINSEQ_2:27.
(twin: `List.length_map` with `List.length_range` — exact) -/
theorem finseq2_28 {D : Set α} {f : ℕ → D} {i : ℕ} :
    ((List.range i).map f).length = i := by
  rw [List.length_map, List.length_range]

/-- after Mizar FINSEQ_2:30 — with `D = Seg i`, composing a
sequence `p` (with `i ≤ len p`) after a sequence `q` of indices
from `D` gives a sequence. Restatement: `q`'s entries are naturals
below `i` (the range-native form of `Seg i`), composition is
reindexing `p` along `q` (via `q.attach`, so each entry carries
its bound), and since being a `List` is automatic in Lean the
recorded content is the length of the composite. Idiom shift:
Mizar's 1-based indices in `Seg i` are 0-based bounds `x < i`
here. -/
theorem finseq2_30 {p : List α} {q : List ℕ} {i : ℕ}
    (hq : ∀ x ∈ q, x < i) (hp : i ≤ p.length) :
    (q.attach.map (fun x => p.get ⟨x.val, lt_of_lt_of_le (hq x.val x.property) hp⟩)).length
      = q.length := by
  rw [List.length_map, List.length_attach]

/-- after Mizar FINSEQ_2:31 — with `D = Seg i`, composing a
sequence `p` valued in `D9` (with `i ≤ len p`) after a sequence
`q` of indices from `D` gives a sequence of `D9`. Restatement as
in FINSEQ_2:30, with `p`'s value type standing for `D9`; the
composite is valued there by construction, and the recorded
content is its length. -/
theorem finseq2_31 {p : List β} {q : List ℕ} {i : ℕ}
    (hq : ∀ x ∈ q, x < i) (hp : i ≤ p.length) :
    (q.attach.map (fun x => p.get ⟨x.val, lt_of_lt_of_le (hq x.val x.property) hp⟩)).length
      = q.length := by
  rw [List.length_map, List.length_attach]

/-- after Mizar FINSEQ_2:32 — composing a function `f` of `A`
into `D` after a sequence of `A` gives a sequence of `D`.
Restatement choice: `FinSequence of D` as the membership
predicate on `List`, composition as `List.map f`. -/
theorem finseq2_32 {A : Set α} {D : Set β} {f : α → β} {p : List α}
    (hf : ∀ a ∈ A, f a ∈ D) (hp : ∀ x ∈ p, x ∈ A) :
    ∀ y ∈ p.map f, y ∈ D := by
  intro y hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
  exact hf a (hp a ha)

/-- after Mizar FINSEQ_2:33 — composing a function after a
sequence preserves length. (twin: `List.length_map` — exact) -/
theorem finseq2_33 {p : List α} {f : α → β} : (p.map f).length = p.length := by
  rw [List.length_map]

/-- after Mizar FINSEQ_2:35 — a function composed after a
one-element sequence gives the one-element sequence of the
value. (twin: `List.map_singleton` — exact) -/
theorem finseq2_35 {f : α → β} {x₁ : α} : [x₁].map f = [f x₁] :=
  List.map_singleton

/-- after Mizar FINSEQ_2:36 — a function composed after a
two-element sequence gives the two-element sequence of the
values. -/
theorem finseq2_36 {f : α → β} {x₁ x₂ : α} : [x₁, x₂].map f = [f x₁, f x₂] := by
  simp

/-- after Mizar FINSEQ_2:37 — a function composed after a
three-element sequence gives the three-element sequence of the
values. -/
theorem finseq2_37 {f : α → β} {x₁ x₂ x₃ : α} :
    [x₁, x₂, x₃].map f = [f x₁, f x₂, f x₃] := by
  simp

/-- after Mizar FINSEQ_2:38 — composing a sequence `p` (with
`j ≤ len p`) after a function `f` of `Seg i` into `Seg j` gives
a sequence. Restatement: `f` is `Fin i → Fin j`, composition is
reindexing `p` along `f` over `List.finRange i`, and the
recorded content is the composite's length. Mizar's side
condition (`j = 0` implies `i = 0`) has no Lean content here:
the given `f : Fin i → Fin j` already forces it. -/
theorem finseq2_38 {p : List α} {i j : ℕ} (hj : j ≤ p.length) {f : Fin i → Fin j} :
    ((List.finRange i).map
      (fun k => p[(f k).val]'(lt_of_lt_of_le (f k).isLt hj))).length = i := by
  rw [List.length_map, List.length_finRange]

/-- after Mizar FINSEQ_2:39 — composing a sequence `p` (with
`i ≤ len p`) after a function `f` of `Seg i` into itself gives
a sequence. Restatement as in FINSEQ_2:38 with `j = i`. -/
theorem finseq2_39 {p : List α} {i : ℕ} (hi : i ≤ p.length) {f : Fin i → Fin i} :
    ((List.finRange i).map
      (fun k => p[(f k).val]'(lt_of_lt_of_le (f k).isLt hi))).length = i := by
  rw [List.length_map, List.length_finRange]

/-- after Mizar FINSEQ_2:40 — composing a sequence `p` after a
function `f` of `dom p` into itself gives a sequence.
Restatement as in FINSEQ_2:38 with the segment `Fin p.length`. -/
theorem finseq2_40 {p : List α} {f : Fin p.length → Fin p.length} :
    ((List.finRange p.length).map
      (fun k => p[(f k).val]'(f k).isLt)).length = p.length := by
  rw [List.length_map, List.length_finRange]

end ThetLogos.MizarPilot1.B6
