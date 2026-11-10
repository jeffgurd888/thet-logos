import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range

/-!
# ThetLogos.MizarTranche1 — MZ-2 tranche 1: doorstep finite-sequence items

> Import note (MZ-2 lane, 2026-11-09): the staged draft imported all of
> Mathlib; the import is narrowed to the closure this file's content
> actually uses, because full-Mathlib import elaboration repeatedly died
> in this environment's restart windows under disk thrash. Content is
> unchanged; the parent integration re-verifies the module in the main
> tree, whose root imports Mathlib in full.

Programme: the Mizar working list (scoping `mizar-working-list-scope-2026-11-08.md`),
brick MZ-2, tranche 1 (25 FINSEQ_1/FINSEQ_2 doorstep items, FIN + ORD basics).
**NO CLAIM; dials 0/4.**

Protocol (§4 of the scoping), AS AMENDED by Zero's directive of 2026-11-09
01:14 EST: ALL 25 tranche items are restated and proved here, including the
10 match-step reclassification candidates. Probe results are recorded as
twin-notes on the items, never as skips; the §5.2 STOP rule does not fire
in this tranche. Adjoint reflections / duplicates are to be trimmed by a
later brick, not by omission here.
Each declaration below is a restatement, from the mathematics, of one Mizar
item, proved in this environment; its doc-comment carries the priority
credit "after Mizar ⟨ARTICLE:ordinal⟩" — Mizar proved it first, in its
system (Tarski–Grothendieck set theory); we re-proved our restatement in
ours (dependent type theory). No Mizar text appears in this file.

Restatement idiom: a finite sequence is a `List`; the initial segment
`Seg n` is `Finset.range n`; restriction to `Seg n` is `List.take n`;
the domain of a sequence is `Finset.range` of its length.
-/

namespace ThetLogos.MizarTranche1

variable {α β γ : Type*}

/-- after Mizar FINSEQ_1:25 — an index of a concatenation lies in the left
factor's index set or is a shifted index of the right factor. -/
theorem mem_range_length_append {p q : List α} {k : ℕ} (hk : k ∈ Finset.range (p ++ q).length) :
    k ∈ Finset.range p.length ∨ ∃ n ∈ Finset.range q.length, k = p.length + n := by
  simp only [Finset.mem_range, List.length_append] at hk ⊢
  rcases lt_or_ge k p.length with h | h
  · exact Or.inl h
  · exact Or.inr ⟨k - p.length, by omega, by omega⟩

/-- after Mizar FINSEQ_1:47 — two decompositions of one sequence whose left
lengths are comparable differ by a common middle piece. -/
theorem exists_append_eq_of_append_eq_append {p q r s : List α}
    (h : p ++ q = r ++ s) (hle : p.length ≤ r.length) : ∃ t : List α, p ++ t = r := by
  refine ⟨r.drop p.length, ?_⟩
  have h1 : r.take p.length = p := by
    have h2 := congrArg (List.take p.length) h
    rw [List.take_left, List.take_append_of_le_length hle] at h2
    exact h2.symm
  calc p ++ r.drop p.length = r.take p.length ++ r.drop p.length := by rw [h1]
    _ = r := List.take_append_drop _ _

/-- after Mizar FINSEQ_1:51 — the increasing enumeration of a subset of an
initial segment is empty iff the subset is empty. -/
theorem sort_eq_nil_iff {X : Finset ℕ} {n : ℕ} (_hX : X ⊆ Finset.range n) :
    X.sort (· ≤ ·) = [] ↔ X = ∅ := by
  constructor
  · intro h
    have hlen : (X.sort (· ≤ ·)).length = 0 := by rw [h]; rfl
    rw [Finset.length_sort] at hlen
    exact Finset.card_eq_zero.mp hlen
  · intro h
    rw [h]
    exact Finset.sort_empty (· ≤ ·)

/-- after Mizar FINSEQ_1:53 — equipotent initial segments of naturals have
the same length (equipotence restated as equality of `Fintype.card`). -/
theorem card_fin_eq {n m : ℕ} (h : Fintype.card (Fin n) = Fintype.card (Fin m)) : n = m := by
  simpa [Fintype.card_fin] using h

/-- after Mizar FINSEQ_1:63 — a subsequence, or a sequence whose index set
is included in another's, is no longer than it. -/
theorem length_le_of_sublist_or_range_subset {p q : List α}
    (h : p.Sublist q ∨ Finset.range p.length ⊆ Finset.range q.length) : p.length ≤ q.length := by
  rcases h with h | h
  · exact h.length_le
  · have := Finset.card_le_card h
    simpa [Finset.card_range] using this

/-- after Mizar FINSEQ_1:80 — every initial segment of a sequence extends
to the whole sequence. -/
theorem exists_append_take {p : List α} {n : ℕ} : ∃ q : List α, p = p.take n ++ q :=
  ⟨p.drop n, (List.take_append_drop n p).symm⟩

/-- after Mizar FINSEQ_1:82 — restricting twice, at bounds `m ≤ n`, is
restricting by the smaller bound. -/
theorem take_take_of_le {p : List α} {n m : ℕ} (h : m ≤ n) : (p.take n).take m = p.take m := by
  rw [List.take_take, min_eq_left h]

/-- after Mizar FINSEQ_1:86 — an initial segment cut at `n` has length
at most `n`. -/
theorem length_take_le {p : List α} {n : ℕ} : (p.take n).length ≤ n := by
  rw [List.length_take]
  exact min_le_left _ _

/-- after Mizar FINSEQ_1:87 — a sequence equal to itself concatenated with
another (on either side) forces the other to be empty. -/
theorem eq_nil_of_append_eq_self {p q : List α} (h : p = p ++ q ∨ p = q ++ p) : q = [] := by
  have hlen : q.length = 0 := by
    rcases h with h | h
    · have h2 : p.length = p.length + q.length := by
        conv_lhs => rw [h]
        rw [List.length_append]
      omega
    · have h2 : p.length = q.length + p.length := by
        conv_lhs => rw [h]
        rw [List.length_append]
      omega
  exact List.length_eq_zero_iff.mp hlen

/-- after Mizar FINSEQ_1:88 — a concatenation that is a singleton splits as
singleton-then-empty or empty-then-singleton. -/
theorem append_eq_singleton {p q : List α} {x : α} (h : p ++ q = [x]) :
    (p = [x] ∧ q = []) ∨ (p = [] ∧ q = [x]) := by
  have hlen : p.length + q.length = 1 := by
    have := congrArg List.length h
    simpa [List.length_append] using this
  rcases (by omega : p.length = 0 ∨ p.length = 1) with hp | hp
  · right
    have hpq : p = [] := List.length_eq_zero_iff.mp hp
    refine ⟨hpq, ?_⟩
    rw [hpq, List.nil_append] at h
    exact h
  · left
    have hq : q.length = 0 := by omega
    have hqq : q = [] := List.length_eq_zero_iff.mp hq
    refine ⟨?_, hqq⟩
    rw [hqq, List.append_nil] at h
    exact h

/-- after Mizar FINSEQ_2:7 — membership in the next initial segment means
membership in the previous one or equality with the new point (the new
point of `Finset.range (l+1)` over `Finset.range l` is `l`). -/
theorem mem_range_succ {i l : ℕ} (h : i ∈ Finset.range (l + 1)) :
    i ∈ Finset.range l ∨ i = l := by
  simp only [Finset.mem_range] at h ⊢
  omega

/-- after Mizar FINSEQ_2:17 — equality of one-element extensions gives
equality of the bases and of the appended elements. -/
theorem append_singleton_inj {p q : List α} {a b : α} (h : p ++ [a] = q ++ [b]) :
    p = q ∧ a = b := by
  have hr := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append] at hr
  injection hr with hab hrev
  exact ⟨List.reverse_injective hrev, hab⟩

/-- after Mizar FINSEQ_2:22 — a sequence of length `i + j` splits into
factors of lengths `i` and `j`. -/
theorem exists_split_of_length_add {r : List α} {i j : ℕ} (h : r.length = i + j) :
    ∃ p q : List α, p.length = i ∧ q.length = j ∧ r = p ++ q := by
  refine ⟨r.take i, r.drop i, ?_, ?_, (List.take_append_drop i r).symm⟩
  · rw [List.length_take, h]
    exact min_eq_left (by omega)
  · rw [List.length_drop, h]
    omega

/-- after Mizar FINSEQ_2:41 — reindexing a sequence by a surjection of its
index segment: the reindexed sequence has the segment's length. -/
theorem length_map_finRange_get {p : List α} {i : ℕ} (hp : i ≤ p.length)
    {f : Fin i → Fin i} (_hf : Function.Surjective f) :
    ((List.finRange i).map (fun j => p[(f j).val]'(lt_of_lt_of_le (f j).isLt hp))).length = i := by
  rw [List.length_map, List.length_finRange]

/-- after Mizar FINSEQ_1:21 — a sequence is its own initial segment of any
extension by concatenation. Twin-note: twin known — Mathlib
`List.take_left` (exact statement twin; compiled per Zero's 2026-11-09
override, trim pass later). -/
theorem take_append_self {p q : List α} : (p ++ q).take p.length = p :=
  List.take_left

/-- after Mizar FINSEQ_1:33 — concatenation is cancellative on either
side. Twin-note: twins known — Lean core `List.append_cancel_right` and
`List.append_cancel_left` (content twins; Mizar's statement is the
implication-of-disjunction form). -/
theorem append_cancel {p q r : List α} (h : p ++ r = q ++ r ∨ r ++ p = r ++ q) : p = q := by
  rcases h with h | h
  · exact List.append_cancel_right h
  · exact List.append_cancel_left h

/-- after Mizar FINSEQ_1:35 — a concatenation is empty only if both factors
are empty. Twin-note: twin known — Mathlib `List.append_eq_nil_iff`
(exact twin, iff form). -/
theorem append_eq_nil {p q : List α} (h : p ++ q = []) : p = [] ∧ q = [] :=
  List.append_eq_nil_iff.mp h

/-- after Mizar FINSEQ_2:2 — the intersection of two initial segments is
the initial segment of the minimum. Twin-note: twin known — Mathlib
`Finset.range_inter_range` (exact statement twin). -/
theorem range_inter {i j : ℕ} : Finset.range i ∩ Finset.range j = Finset.range (min i j) :=
  Finset.range_inter_range i j

/-- after Mizar FINSEQ_2:20 — restricting a sequence beyond its length
returns the sequence. Twin-note: twin known — Mathlib
`List.take_of_length_le` (exact statement twin). -/
theorem take_of_length_le {p : List α} {i : ℕ} (h : p.length ≤ i) : p.take i = p :=
  List.take_of_length_le h

/-- after Mizar FINSEQ_2:21 — the length of a restriction is the minimum
of the bound and the length. Twin-note: twin known — Mathlib
`List.length_take` (exact statement twin). -/
theorem length_take {p : List α} {i : ℕ} : (p.take i).length = min i p.length :=
  List.length_take

/-- after Mizar FINSEQ_2:29 — applying a function pointwise to a sequence
preserves its length (Mizar's form is composition with a function on the
range). Twin-note: twin known — Mathlib `List.length_map` (exact twin of
the map restatement). -/
theorem length_map {p : List α} {f : α → β} : (p.map f).length = p.length := by
  rw [List.length_map]

/-- after Mizar FINSEQ_2:34 — a function applied pointwise to a singleton
sequence gives the singleton of the value. Twin-note: twin known —
Mathlib `List.map_singleton` (exact statement twin). -/
theorem map_singleton {f : α → β} {x : α} : List.map f [x] = [f x] :=
  List.map_singleton

/-- after Mizar FINSEQ_2:57 — a constant finite sequence takes its
constant value at every index in range. Twin-note: twin known — Mathlib
`List.getElem_replicate` (exact statement twin). -/
theorem getElem_replicate_const {k : ℕ} {d : α} {j : ℕ}
    (h : j < (List.replicate k d).length) : (List.replicate k d)[j] = d :=
  List.getElem_replicate h

/-- after Mizar FINSEQ_2:65 — pointwise pairing of two sequences by a
binary function has length the minimum of the lengths. Twin-note: twin
known — Mathlib `List.length_zipWith` (exact statement twin). -/
theorem length_zipWith {F : α → β → γ} {p : List α} {q : List β} :
    (List.zipWith F p q).length = min p.length q.length :=
  List.length_zipWith

/-- after Mizar FINSEQ_2:54 — reindexing by the identity sequence (long
enough) returns the sequence: filtering the pointwise lookups over a long
enough initial segment recovers the sequence itself. Restated with the
`p[j]?` lookup (this pin has no `List.get?` constant; same mathematics —
restatement repair logged in the lane report). -/
theorem filterMap_getElem?_range {p : List α} {k : ℕ} (h : p.length ≤ k) :
    (List.range k).filterMap (fun j => p[j]?) = p := by
  induction p generalizing k with
  | nil =>
    simp [List.filterMap_eq_nil_iff, List.getElem?_nil]
  | cons a p ih =>
    cases k with
    | zero => simp at h
    | succ k =>
      rw [List.range_succ_eq_map, List.filterMap_cons, List.getElem?_cons_zero]
      simp only [Option.some.injEq]
      rw [List.filterMap_map]
      have h' : (List.range k).filterMap ((fun j => (a :: p)[j]?) ∘ (· + 1)) =
          (List.range k).filterMap (fun j => p[j]?) := by
        apply List.filterMap_congr
        intro j _
        exact List.getElem?_cons_succ
      rw [h']
      exact congrArg (a :: ·) (ih (by simpa using h))

end ThetLogos.MizarTranche1
