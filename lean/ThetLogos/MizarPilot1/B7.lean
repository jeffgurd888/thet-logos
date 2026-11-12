import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.List.Basic

/-!
# ThetLogos.MizarPilot1.B7 — MZ pilot tranche 1, brick B7: FINSEQ_3 segment items

Programme: the Mizar working list, MZ pilot tranche 1 brick B7
(24 items, all from Mizar FINSEQ_3), drafted under Zero's 2026-11-09
pilot call.
**NO CLAIM; dials 0/4.**

Protocol: ALL 24 brick items are restated and proved here. Probe results
are recorded as twin-notes on the items, never as skips. Each declaration
below is a restatement, from the mathematics, of one Mizar item, proved
in this environment; its doc-comment carries the priority credit
"after Mizar FINSEQ_3:nn" — Mizar proved it first, in its system
(Tarski–Grothendieck set theory); we re-proved our restatement in ours
(dependent type theory). No Mizar text appears in this file.

Restatement idiom: a finite sequence is a `List` (settled tranche-1
idiom: `^` is `++`, `len` is `List.length`, indexing is 1-based).
Mizar's `Seg n` is the 1-based initial segment `{1, …, n}`; it is
restated here as `seg n := Finset.Icc 1 n`, i.e. the tranche-1
`Finset.range n` shifted by `+1` (the unshifted `Finset.range n` would
make FINSEQ_3:1–6, :7, :9 false as stated, since Mizar's `Seg` starts
at 1). The domain of a sequence `p` is Mizar's `Seg (len p)`, restated
as `seg p.length`. No item in this brick quantifies over a set `D`
("FinSequence of D"), so no `D`-hypothesis or subtype coercion is
needed: the segment items are pure natural-number arithmetic, and the
domain items quantify over plain `List α`.
-/

namespace ThetLogos.MizarPilot1.B7

variable {α β : Type*}

/-- The 1-based initial segment `Seg n = {1, …, n}`, restated as
`Finset.Icc 1 n` (the `Finset.range n` of the tranche-1 idiom, shifted
by `+1`). -/
def seg (n : ℕ) : Finset ℕ := Finset.Icc 1 n

/-- Membership in the restated segment: `x ∈ seg n ↔ 1 ≤ x ∧ x ≤ n`. -/
theorem mem_seg {x n : ℕ} : x ∈ seg n ↔ 1 ≤ x ∧ x ≤ n := Finset.mem_Icc

/-- after Mizar FINSEQ_3:1 — the segment of length 3 is `{1, 2, 3}`. -/
theorem seg_three : seg 3 = {1, 2, 3} := by
  ext x
  simp only [mem_seg, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- after Mizar FINSEQ_3:2 — the segment of length 4 is `{1, 2, 3, 4}`. -/
theorem seg_four : seg 4 = {1, 2, 3, 4} := by
  ext x
  simp only [mem_seg, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- after Mizar FINSEQ_3:3 — the segment of length 5 is `{1, 2, 3, 4, 5}`. -/
theorem seg_five : seg 5 = {1, 2, 3, 4, 5} := by
  ext x
  simp only [mem_seg, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- after Mizar FINSEQ_3:4 — the segment of length 6 is `{1, 2, 3, 4, 5, 6}`. -/
theorem seg_six : seg 6 = {1, 2, 3, 4, 5, 6} := by
  ext x
  simp only [mem_seg, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- after Mizar FINSEQ_3:5 — the segment of length 7 is `{1, 2, 3, 4, 5, 6, 7}`. -/
theorem seg_seven : seg 7 = {1, 2, 3, 4, 5, 6, 7} := by
  ext x
  simp only [mem_seg, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- after Mizar FINSEQ_3:6 — the segment of length 8 is `{1, 2, 3, 4, 5, 6, 7, 8}`. -/
theorem seg_eight : seg 8 = {1, 2, 3, 4, 5, 6, 7, 8} := by
  ext x
  simp only [mem_seg, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- after Mizar FINSEQ_3:7 — a segment is empty iff its own bound is not
in it (both sides say the bound is 0). -/
theorem seg_eq_empty_iff_notMem_self {k : ℕ} : seg k = ∅ ↔ k ∉ seg k := by
  constructor
  · intro h hk
    rw [h] at hk
    simp at hk
  · intro h
    ext x
    rw [mem_seg]
    constructor
    · intro hx
      exfalso
      apply h
      rw [mem_seg]
      exact ⟨by omega, le_refl k⟩
    · intro hx
      simp at hx

/-- after Mizar FINSEQ_3:8 — the successor of the bound is never in the
segment. -/
theorem succ_notMem_seg {k : ℕ} : k + 1 ∉ seg k := by
  rw [mem_seg]
  omega

/-- after Mizar FINSEQ_3:9 — a nonzero bound lies in every longer segment
starting at the same bound. -/
theorem mem_seg_add_of_ne_zero {k n : ℕ} (hk : k ≠ 0) : k ∈ seg (k + n) := by
  rw [mem_seg]
  exact ⟨by omega, by omega⟩

/-- after Mizar FINSEQ_3:10 — if a shifted bound `k + n` still lies in
`Seg k`, the shift was zero. -/
theorem eq_zero_of_add_mem_seg {k n : ℕ} (h : k + n ∈ seg k) : n = 0 := by
  rw [mem_seg] at h
  omega

/-- after Mizar FINSEQ_3:11 — below `n`, the successor still lies in
`Seg n`. -/
theorem succ_mem_seg_of_lt {k n : ℕ} (h : k < n) : k + 1 ∈ seg n := by
  rw [mem_seg]
  exact ⟨by omega, by omega⟩

/-- after Mizar FINSEQ_3:12 — subtracting a smaller number from a member
of a segment stays in the segment. -/
theorem sub_mem_seg_of_mem_of_lt {k m n : ℕ} (hk : k ∈ seg n) (hm : m < k) :
    k - m ∈ seg n := by
  rw [mem_seg] at hk ⊢
  exact ⟨by omega, by omega⟩

/-- after Mizar FINSEQ_3:13 — `k - n` lies in `Seg k` iff `n < k`
(truncated subtraction lands at 0, outside the 1-based segment, exactly
when `n ≥ k`). -/
theorem sub_mem_seg_iff {k n : ℕ} : k - n ∈ seg k ↔ n < k := by
  rw [mem_seg]
  constructor
  · rintro ⟨h1, -⟩
    omega
  · intro h
    exact ⟨by omega, by omega⟩

/-- after Mizar FINSEQ_3:14 — a segment misses the singleton of its
bound's successor (Mizar's `misses` is disjointness). -/
theorem seg_disjoint_singleton_succ {k : ℕ} : Disjoint (seg k) {k + 1} := by
  rw [Finset.disjoint_left]
  intro x hx hx2
  rw [mem_seg] at hx
  rw [Finset.mem_singleton] at hx2
  omega

/-- after Mizar FINSEQ_3:15 — cutting the previous segment out of the
next one leaves exactly the new point. -/
theorem seg_succ_sdiff_seg {k : ℕ} : seg (k + 1) \ seg k = {k + 1} := by
  ext x
  simp only [mem_seg, Finset.mem_sdiff, Finset.mem_singleton]
  omega

/-- after Mizar FINSEQ_3:16 — a segment differs from its successor
segment: the new point `k + 1` separates them. -/
theorem seg_ne_seg_succ {k : ℕ} : seg k ≠ seg (k + 1) := by
  intro h
  have h1 : k + 1 ∈ seg (k + 1) := by
    rw [mem_seg]
    exact ⟨by omega, le_refl (k + 1)⟩
  rw [← h] at h1
  rw [mem_seg] at h1
  omega

/-- after Mizar FINSEQ_3:17 — equal segments with a shifted bound force
the shift to be zero: the shifted bound itself separates them. -/
theorem eq_zero_of_seg_eq_seg_add {k n : ℕ} (h : seg k = seg (k + n)) : n = 0 := by
  rcases (by omega : n = 0 ∨ 0 < n) with hn | hn
  · exact hn
  · exfalso
    have h1 : k + n ∈ seg (k + n) := by
      rw [mem_seg]
      exact ⟨by omega, le_refl (k + n)⟩
    rw [← h] at h1
    rw [mem_seg] at h1
    omega

/-- after Mizar FINSEQ_3:18 — a segment is included in every longer
segment (`c=` is inclusion). -/
theorem seg_subset_seg_add {k n : ℕ} : seg k ⊆ seg (k + n) := by
  intro x hx
  rw [mem_seg] at hx ⊢
  obtain ⟨h1, h2⟩ := hx
  exact ⟨h1, by omega⟩

/-- after Mizar FINSEQ_3:19 — any two segments are comparable by
inclusion (`are_c=-comparable`): the shorter is included in the longer. -/
theorem seg_comparable {k n : ℕ} : seg k ⊆ seg n ∨ seg n ⊆ seg k := by
  rcases le_total k n with h | h
  · left
    intro x hx
    rw [mem_seg] at hx ⊢
    obtain ⟨h1, h2⟩ := hx
    exact ⟨h1, by omega⟩
  · right
    intro x hx
    rw [mem_seg] at hx ⊢
    obtain ⟨h1, h2⟩ := hx
    exact ⟨h1, by omega⟩

/-- after Mizar FINSEQ_3:20 — a segment that is a singleton is `Seg 1`,
and its only element is 1: both 1 and the bound `k` lie in the segment,
so both equal the singleton's element. (Draw-tag B in the brick list.
Mizar's `y` ranges over objects; here `y` is a natural, the only type
that can name a segment element.) -/
theorem seg_eq_singleton {k y : ℕ} (h : seg k = {y}) : k = 1 ∧ y = 1 := by
  have hy : y ∈ seg k := by
    rw [h]
    exact Finset.mem_singleton_self y
  rw [mem_seg] at hy
  obtain ⟨hy1, hy2⟩ := hy
  have h1 : (1 : ℕ) ∈ seg k := by
    rw [mem_seg]
    exact ⟨le_refl 1, by omega⟩
  have hk : k ∈ seg k := by
    rw [mem_seg]
    exact ⟨by omega, le_refl k⟩
  rw [h] at h1 hk
  have e1 : (1 : ℕ) = y := Finset.mem_singleton.mp h1
  have ek : k = y := Finset.mem_singleton.mp hk
  omega

/-- after Mizar FINSEQ_3:21 — a segment that is a two-element set is
`Seg 2`, and the set is `{1, 2}`: the bound is at least 1 (the elements
lie in the segment), is not 1 (two distinct elements cannot both lie in
`Seg 1`), and is at most 2 (three distinct points 1, 2, 3 cannot take
only two values). -/
theorem seg_eq_pair {k x y : ℕ} (h : seg k = {x, y} ∧ x ≠ y) :
    k = 2 ∧ ({x, y} : Finset ℕ) = {1, 2} := by
  obtain ⟨h, hxy⟩ := h
  have hx : x ∈ seg k := by
    rw [h]
    exact Finset.mem_insert_self x {y}
  have hy : y ∈ seg k := by
    rw [h]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
  rw [mem_seg] at hx hy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have key : ∀ z ∈ seg k, z = x ∨ z = y := by
    intro z hz
    rw [h] at hz
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hz
  have hkne1 : k ≠ 1 := by
    intro hk
    have ex : x = 1 := by omega
    have ey : y = 1 := by omega
    exact hxy (by rw [ex, ey])
  have hk2 : k ≤ 2 := by
    by_contra hcon
    have hgt : 2 < k := by omega
    have e1 := key 1 (by rw [mem_seg]; exact ⟨le_refl 1, by omega⟩)
    have e2 := key 2 (by rw [mem_seg]; exact ⟨by omega, by omega⟩)
    have e3 := key 3 (by rw [mem_seg]; exact ⟨by omega, by omega⟩)
    rcases e1 with r | r <;> rcases e2 with r | r <;> rcases e3 with r | r <;> omega
  have hk : k = 2 := by omega
  subst hk
  refine ⟨rfl, ?_⟩
  have hseg2 : seg 2 = {1, 2} := by
    ext z
    simp only [mem_seg, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [← h]
  exact hseg2

/-- after Mizar FINSEQ_3:22 — an index in the domain of `p` stays in the
domain of the concatenation `p ^ q` (domain restated as `seg` of the
length; concatenation cannot shrink the length). -/
theorem mem_seg_length_append {p q : List α} {x : ℕ} (h : x ∈ seg p.length) :
    x ∈ seg (p ++ q).length := by
  rw [mem_seg] at h ⊢
  obtain ⟨h1, h2⟩ := h
  rw [List.length_append]
  exact ⟨h1, by omega⟩

/-- after Mizar FINSEQ_3:23 — an index in the domain of a sequence is a
natural number. In the typed restatement the index is already carried
as a `ℕ`; the Mizar content is recorded as the existence of that
natural witness. -/
theorem exists_nat_eq_of_mem_seg_length {p : List α} {x : ℕ}
    (_h : x ∈ seg p.length) : ∃ n : ℕ, x = n :=
  ⟨x, rfl⟩

/-- after Mizar FINSEQ_3:24 — an index in the domain of a sequence is
nonzero: the domain is the 1-based segment of the length. -/
theorem ne_zero_of_mem_seg_length {p : List α} {x : ℕ} (h : x ∈ seg p.length) :
    x ≠ 0 := by
  rw [mem_seg] at h
  obtain ⟨h1, -⟩ := h
  omega

end ThetLogos.MizarPilot1.B7
