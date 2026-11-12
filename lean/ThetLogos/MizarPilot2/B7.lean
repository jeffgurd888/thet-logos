import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range

/-!
# ThetLogos.MizarPilot2.B7 — MZ-W1-P2, brick B7: FINSEQ_3 domain / Sgm / restriction / preimage items

Programme: the Mizar working list, MZ pilot tranche 2 (MZ-W1-P2) brick B7
(36 items, all from Mizar FINSEQ_3: 25, 26, 29–40, 42–63), drafted under
Zero's 2026-11-09 pilot call.
**NO CLAIM; dials 0/4.** Restatement grade only: each declaration below
is a restatement, from the mathematics, of one Mizar item; its
doc-comment carries the priority credit "after Mizar FINSEQ_3:nn" —
Mizar proved it first, in its system (Tarski–Grothendieck set theory);
we re-prove our restatement in ours (dependent type theory). No Mizar
text appears in this file.

Protocol: all 36 brick items are present. Twin verdicts are recorded
as twin-notes on the items, never as skips. One item (FINSEQ_3:56) is
STUCK in place, commented out with its reason; it is not dropped and
not repaired into a different claim.

Restatement idiom (P1-B7's, followed exactly): a finite sequence is a
`List α` (`^` is `++`, `len` is `List.length`, Mizar indexing is
1-based: the item at position `k` is `p[k-1]` in Lean `getElem`
terms, read through the total lookup `p[k-1]?` where a proof is not
carried). Mizar's `Seg n` is the 1-based initial segment `{1, …, n}`;
it is restated here as `seg n := Finset.Icc 1 n`, i.e. the tranche-1
`Finset.range n` shifted by `+1` (the unshifted `Finset.range n`
reading falsifies the FINSEQ_3 segment items, as recorded in P1-B7).
The domain of a sequence `p` is Mizar's `Seg (len p)`, restated as
`seg p.length`. `rng p` is restated as element membership in the list.

Brick-specific restatements, recorded here once:
* `Sgm A` (Mizar's increasing enumeration of an included-in-Seg set
  `A`) is restated as `sgm A := A.sort (· ≤ ·)` over `Finset ℕ`; the
  `included_in_Seg` hypothesis is carried as `∃ k, A ⊆ seg k` where
  Mizar states it (items 39, 40, 42) — the Lean statements in fact
  hold for every `Finset ℕ`, which is noted per item.
* `idseq n` is restated as `List.range' 1 n = [1, …, n]`.
* Restriction `p | Seg n` is `List.take n` (P1 idiom).
* The preimage `p " A` is restated in the 0-based range-native form
  (the P1-B5 precedent): `pre p A` is the finset of 0-based indices
  `i` with `p[i]?` a value in `A` — Mizar's 1-based index set shifted
  by `-1`. Cardinality (57, 59, 62) and inclusion (58) content is
  shift-invariant, and the shift is recorded per item.
* Deletion `p - A` is restated as `sminus p A := p.filter (· ∉ A)`,
  the list of entries of `p` whose value is not in `A`, in order.
-/

namespace ThetLogos.MizarPilot2.B7

variable {α β : Type*}

/-- The 1-based initial segment `Seg n = {1, …, n}`, restated as
`Finset.Icc 1 n` (the `Finset.range n` of the tranche-1 idiom, shifted
by `+1`). -/
def seg (n : ℕ) : Finset ℕ := Finset.Icc 1 n

/-- Membership in the restated segment: `x ∈ seg n ↔ 1 ≤ x ∧ x ≤ n`.
(Auxiliary helper, as P1-B7's `mem_seg`.) -/
theorem mem_seg {x n : ℕ} : x ∈ seg n ↔ 1 ≤ x ∧ x ≤ n := Finset.mem_Icc

/-- Mizar's `Sgm`: the increasing enumeration of a set of naturals,
restated as the sorted list of the finset. -/
def sgm (A : Finset ℕ) : List ℕ := A.sort (· ≤ ·)

/-- Mizar's `idseq n`: the identity sequence on `Seg n`, restated as
`[1, …, n]`. -/
def idseq (n : ℕ) : List ℕ := List.range' 1 n

/- Mizar's preimage `p " A`, in the 0-based range-native form: the
finset of 0-based indices whose value lies in `A`. -/
open Classical in
noncomputable def pre (p : List α) (A : Finset α) : Finset ℕ :=
  (Finset.range p.length).filter (fun i => ∃ v, p[i]? = some v ∧ v ∈ A)

/- Mizar's deletion `p - A`: the entries of `p` whose value is not
in `A`, kept in order. -/
open Classical in
noncomputable def sminus (p : List α) (A : Finset α) : List α :=
  p.filter (fun x => x ∉ A)

/-- Auxiliary helper (single-point repair seat for the `Sgm` items,
mirroring P1-B7's `mem_seg` pattern): a nodup pairwise-`(· ≤ ·)`
list with the same elements as `A` is `sgm A`. (At this pin
`List.Sorted` does not exist; sortedness is `List.Pairwise`, and
the uniqueness route is `List.toFinset_sort`.) -/
theorem sgm_eq_of {A : Finset ℕ} {l : List ℕ} (hd : l.Nodup)
    (hs : l.Pairwise (· ≤ ·)) (hm : ∀ x, x ∈ l ↔ x ∈ A) : sgm A = l := by
  have htf : l.toFinset = A := by
    ext x
    simp only [List.mem_toFinset]
    exact hm x
  unfold sgm
  rw [← htf]
  exact (List.toFinset_sort (· ≤ ·) hd).mpr hs

/-- Auxiliary helper: `Sgm (Seg k) = idseq k`, the content of
FINSEQ_3:48, proved once here so the earlier-numbered FINSEQ_3:47 can
use it. GUESSED-NAME: `List.nodup_range'`, `List.sorted_range'`,
`List.mem_range'`. -/
theorem sgm_seg_eq_idseq (k : ℕ) : sgm (seg k) = idseq k := by
  apply sgm_eq_of
  · exact List.nodup_range'
  · show (List.range' 1 k).Pairwise (· ≤ ·)
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [List.getElem_range', List.getElem_range']
    omega
  · intro x
    simp only [idseq, List.mem_range', mem_seg]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨by omega, by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨x - 1, by omega, by omega⟩

/-- Auxiliary helper (the counting bridge for the preimage items):
the cardinal of the restated preimage is the count of entries of `p`
lying in `A`. GUESSED-NAME: `List.getElem?_cons_zero`,
`List.getElem?_cons_succ`, `Finset.card_union_of_disjoint`,
`Finset.card_image_of_injective`, `List.countP_cons`. -/
theorem card_pre_eq_countP [DecidableEq α] (p : List α) (A : Finset α) :
    (pre p A).card = p.countP (fun v => v ∈ A) := by
  induction p with
  | nil => simp [pre]
  | cons a as ih =>
    by_cases ha : a ∈ A
    · have hset : pre (a :: as) A = {0} ∪ (pre as A).image (· + 1) := by
        ext i
        cases i with
        | zero =>
          simp only [pre, Finset.mem_filter, Finset.mem_range, List.length_cons,
            List.getElem?_cons_zero, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_image]
          constructor
          · rintro ⟨-, v, hv, hvA⟩
            exact Or.inl trivial
          · intro h
            rcases h with h | ⟨y, -, hy⟩
            · exact ⟨by omega, a, rfl, ha⟩
            · exact absurd hy (by simp)
        | succ i =>
          simp only [pre, Finset.mem_filter, Finset.mem_range, List.length_cons,
            List.getElem?_cons_succ, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_image, Nat.succ_ne_zero, false_and, or_false]
          constructor
          · rintro ⟨h1, v, hv, hvA⟩
            exact Or.inr ⟨i, ⟨by omega, v, hv, hvA⟩, rfl⟩
          · rintro (h | ⟨y, ⟨h1, v, hv, hvA⟩, hy⟩)
            · exact h.elim
            · have hiy : i = y := by omega
              subst hiy
              exact ⟨by omega, v, hv, hvA⟩
      have hdisj : Disjoint ({0} : Finset ℕ) ((pre as A).image (· + 1)) := by
        rw [Finset.disjoint_left]
        intro x hx
        simp only [Finset.mem_singleton] at hx
        subst hx
        simp only [Finset.mem_image]
        rintro ⟨y, -, hy⟩
        omega
      rw [hset, Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _
          (by intro a b h; have h' : a + 1 = b + 1 := h; omega), ih]
      simp [List.countP_cons, ha]
      rw [add_comm]
    · have hset : pre (a :: as) A = (pre as A).image (· + 1) := by
        ext i
        cases i with
        | zero =>
          simp only [pre, Finset.mem_filter, Finset.mem_range, List.length_cons,
            List.getElem?_cons_zero, Finset.mem_image]
          constructor
          · rintro ⟨-, v, hv, hvA⟩
            have hvv : v = a := by
              have h2 : a = v := Option.some.inj hv
              exact h2.symm
            rw [hvv] at hvA
            exact absurd hvA ha
          · rintro ⟨y, -, hy⟩
            exact absurd hy (by simp)
        | succ i =>
          simp only [pre, Finset.mem_filter, Finset.mem_range, List.length_cons,
            List.getElem?_cons_succ, Finset.mem_image]
          constructor
          · rintro ⟨h1, v, hv, hvA⟩
            exact ⟨i, ⟨by omega, v, hv, hvA⟩, rfl⟩
          · rintro ⟨y, ⟨h1, v, hv, hvA⟩, hy⟩
            have hiy : i = y := by omega
            subst hiy
            exact ⟨by omega, v, hv, hvA⟩
      rw [hset, Finset.card_image_of_injective _
          (by intro a b h; have h' : a + 1 = b + 1 := h; omega), ih]
      simp [List.countP_cons, ha]

/-- after Mizar FINSEQ_3:25 — an index lies in the domain of `p` iff
it is a 1-based position within the length (`dom p` restated as
`seg p.length`). (twin: `mem_seg` — exact) -/
theorem finseq3_25 {p : List α} {n : ℕ} :
    n ∈ seg p.length ↔ 1 ≤ n ∧ n ≤ p.length :=
  mem_seg

/-- after Mizar FINSEQ_3:26 — the same domain characterization in
Mizar's "is an Element of NAT" form: for naturals, `n - 1` and
`len p - n` are (integer) naturals exactly when `0 < n` and
`n ≤ len p`; in the typed restatement that content is the pair of
bounds on the right. -/
theorem finseq3_26 {p : List α} {n : ℕ} :
    n ∈ seg p.length ↔ 0 < n ∧ n ≤ p.length := by
  rw [mem_seg]
  constructor <;> intro h <;> exact ⟨by omega, by omega⟩

/-- after Mizar FINSEQ_3:29 — two sequences have the same length iff
they have the same domain. GUESSED-NAME: `Nat.card_Icc` (the cardinal
of the restated segment). -/
theorem finseq3_29 {p q : List α} :
    p.length = q.length ↔ seg p.length = seg q.length := by
  constructor
  · intro h
    rw [h]
  · intro h
    have hcard := congrArg Finset.card h
    simp only [seg, Nat.card_Icc] at hcard
    omega

/-- after Mizar FINSEQ_3:30 — length comparison is domain inclusion
(`c=` is inclusion). -/
theorem finseq3_30 {p q : List α} :
    p.length ≤ q.length ↔ seg p.length ⊆ seg q.length := by
  constructor
  · intro h x hx
    rw [mem_seg] at hx ⊢
    exact ⟨hx.1, by omega⟩
  · intro h
    by_cases hp : p.length = 0
    · omega
    · have hmem : p.length ∈ seg p.length := by
        rw [mem_seg]
        exact ⟨by omega, le_refl _⟩
      have h2 := h hmem
      rw [mem_seg] at h2
      omega

/-- after Mizar FINSEQ_3:31 — if a value occurs in `p` (`x ∈ rng p`,
restated as membership), position 1 lies in the domain: the sequence
is nonempty. -/
theorem finseq3_31 {p : List α} {x : α} (hx : x ∈ p) :
    1 ∈ seg p.length := by
  obtain ⟨i, hi, -⟩ := List.mem_iff_getElem.mp hx
  rw [mem_seg]
  exact ⟨le_refl 1, by omega⟩

/-- after Mizar FINSEQ_3:32 — if the range of `p` is nonempty
(`rng p ≠ {}`, restated as the existence of an element), position 1
lies in the domain. -/
theorem finseq3_32 {p : List α} (hx : ∃ x, x ∈ p) :
    1 ∈ seg p.length := by
  obtain ⟨x, hx⟩ := hx
  exact finseq3_31 hx

/-- after Mizar FINSEQ_3:33 — the empty sequence is not the
two-element sequence `<*x, y*>`. -/
theorem finseq3_33 {x y : α} : ([] : List α) ≠ [x, y] := by
  intro h
  have hlen := congrArg List.length h
  simp at hlen

/-- after Mizar FINSEQ_3:34 — the empty sequence is not the
three-element sequence `<*x, y, z*>`. -/
theorem finseq3_34 {x y z : α} : ([] : List α) ≠ [x, y, z] := by
  intro h
  have hlen := congrArg List.length h
  simp at hlen

/-- after Mizar FINSEQ_3:35 — a one-element sequence is not a
two-element sequence. -/
theorem finseq3_35 {x y z : α} : [x] ≠ [y, z] := by
  intro h
  have hlen := congrArg List.length h
  simp at hlen

/-- after Mizar FINSEQ_3:36 — a one-element sequence is not a
three-element sequence. -/
theorem finseq3_36 {u x y z : α} : [u] ≠ [x, y, z] := by
  intro h
  have hlen := congrArg List.length h
  simp at hlen

/-- after Mizar FINSEQ_3:37 — a two-element sequence is not a
three-element sequence. -/
theorem finseq3_37 {u v x y z : α} : [u, v] ≠ [x, y, z] := by
  intro h
  have hlen := congrArg List.length h
  simp at hlen

/-- after Mizar FINSEQ_3:38 — concatenation is characterized by its
length and its values: a sequence of length `len p + len q` agreeing
with `p` on `dom p` (1-based positions `k`, read at index `k - 1`)
and with `q` on the shifted positions is `p ^ q`. (Draw-tag B in the
brick list. Twins: `List.getElem?_append_left`,
`List.getElem?_append_right` — the index-shift forms, tranche-1
attested on the right.) -/
theorem finseq3_38 {p q r : List α} (hlen : r.length = p.length + q.length)
    (hp : ∀ k ∈ seg p.length, r[k - 1]? = p[k - 1]?)
    (hq : ∀ k ∈ seg q.length, r[p.length + k - 1]? = q[k - 1]?) :
    r = p ++ q := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < p.length
  · have h := hp (i + 1) (by rw [mem_seg]; exact ⟨by omega, by omega⟩)
    simp only [Nat.add_sub_cancel] at h
    rw [List.getElem?_append_left hi]
    exact h
  · by_cases hi2 : i < r.length
    · have h := hq (i - p.length + 1) (by rw [mem_seg]; exact ⟨by omega, by omega⟩)
      have e1 : p.length + (i - p.length + 1) - 1 = i := by omega
      have e2 : i - p.length + 1 - 1 = i - p.length := by omega
      rw [e1, e2] at h
      rw [List.getElem?_append_right (by omega : p.length ≤ i)]
      exact h
    · have hr : r[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      have hq2 : (p ++ q)[i]? = none :=
        List.getElem?_eq_none_iff.mpr (by rw [List.length_append]; omega)
      rw [hr, hq2]

/-- after Mizar FINSEQ_3:39 — the length of `Sgm A` is the cardinal
of `A`, for `A` included in a segment (the hypothesis is carried as
Mizar states it; the sorted-list restatement in fact needs none).
(Draw-tag B. Twin: `Finset.length_sort` — GUESSED-NAME.) -/
theorem finseq3_39 {A : Finset ℕ} (_hA : ∃ k, A ⊆ seg k) :
    (sgm A).length = A.card := by
  simp only [sgm, Finset.length_sort]

/-- after Mizar FINSEQ_3:40 — the domain of `Sgm A` is
`Seg (card A)` (`dom` restated as `seg` of the length). (Draw-tag B.) -/
theorem finseq3_40 {A : Finset ℕ} (hA : ∃ k, A ⊆ seg k) :
    seg (sgm A).length = seg A.card := by
  rw [finseq3_39 hA]

/-- after Mizar FINSEQ_3:42 — for included-in-Seg sets `X`, `Y`
(hypotheses carried as Mizar states them; the restatement needs
none), every element of `X` lies below every element of `Y` iff
`Sgm (X ∪ Y)` splits as `Sgm X ^ Sgm Y`. (Draw-tag B. GUESSED-NAME:
`List.Sorted.append`, `List.nodup_append`, `Finset.sort_sorted`,
`Finset.sort_nodup`, `Finset.mem_sort` — via the `sgm_eq_of`
helper.) -/
theorem finseq3_42 {X Y : Finset ℕ} (_hX : ∃ k, X ⊆ seg k)
    (_hY : ∃ k, Y ⊆ seg k) :
    (∀ m ∈ X, ∀ n ∈ Y, m < n) ↔ sgm (X ∪ Y) = sgm X ++ sgm Y := by
  constructor
  · intro h
    apply sgm_eq_of
    · rw [List.nodup_append]
      refine ⟨Finset.sort_nodup _ _, Finset.sort_nodup _ _, ?_⟩
      intro a ha b hb heq
      have ha' : a ∈ X := (Finset.mem_sort (· ≤ ·)).mp ha
      have hb' : b ∈ Y := (Finset.mem_sort (· ≤ ·)).mp hb
      subst heq
      exact (lt_irrefl a) (h a ha' a hb')
    · rw [List.pairwise_append]
      refine ⟨Finset.pairwise_sort _ _, Finset.pairwise_sort _ _, ?_⟩
      intro a ha b hb
      have ha' : a ∈ X := (Finset.mem_sort (· ≤ ·)).mp ha
      have hb' : b ∈ Y := (Finset.mem_sort (· ≤ ·)).mp hb
      exact le_of_lt (h a ha' b hb')
    · intro x
      simp only [sgm, List.mem_append, Finset.mem_sort, Finset.mem_union]
  · intro h m hm n hn
    have hsorted : (sgm (X ∪ Y)).Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
    rw [h] at hsorted
    rw [List.pairwise_append] at hsorted
    obtain ⟨-, -, hcross⟩ := hsorted
    have hle : m ≤ n :=
      hcross m ((Finset.mem_sort (· ≤ ·)).mpr hm) n ((Finset.mem_sort (· ≤ ·)).mpr hn)
    have hne : m ≠ n := by
      have hnd : (sgm (X ∪ Y)).Nodup := Finset.sort_nodup _ _
      rw [h] at hnd
      rw [List.nodup_append] at hnd
      obtain ⟨-, -, hdisj⟩ := hnd
      exact hdisj m ((Finset.mem_sort (· ≤ ·)).mpr hm) n
        ((Finset.mem_sort (· ≤ ·)).mpr hn)
    omega

/-- after Mizar FINSEQ_3:43 — `Sgm` of the empty set is the empty
sequence. -/
theorem finseq3_43 : sgm (∅ : Finset ℕ) = ([] : List ℕ) := by
  apply sgm_eq_of
  · exact List.nodup_nil
  · exact List.Pairwise.nil
  · intro x
    simp

/-- after Mizar FINSEQ_3:44 — `Sgm` of a singleton `{n}` (with
`n ≠ 0`, Mizar's included-in-Seg side condition) is `<*n*>`; the
sorted-list restatement in fact needs no side condition. -/
theorem finseq3_44 {n : ℕ} (_hn : n ≠ 0) : sgm {n} = [n] := by
  apply sgm_eq_of
  · exact List.nodup_singleton _
  · exact List.pairwise_singleton _ _
  · intro x
    simp only [List.mem_singleton, Finset.mem_singleton]

/-- after Mizar FINSEQ_3:45 — `Sgm` of a two-element set `{n, m}`
with `0 < n < m` is `<*n, m*>`. -/
theorem finseq3_45 {n m : ℕ} (_hn : 0 < n) (h : n < m) :
    sgm {n, m} = [n, m] := by
  apply sgm_eq_of
  · exact List.Pairwise.cons
      (by intro b hb; rw [List.mem_singleton] at hb; omega)
      (List.nodup_singleton _)
  · exact List.Pairwise.cons
      (by intro b hb; rw [List.mem_singleton] at hb; omega)
      (List.pairwise_singleton _ _)
  · intro x
    simp

/-- after Mizar FINSEQ_3:46 — the length of `Sgm (Seg k)` is `k`.
GUESSED-NAME: `Finset.length_sort`, `Nat.card_Icc`. -/
theorem finseq3_46 {k : ℕ} : (sgm (seg k)).length = k := by
  simp only [sgm, seg, Finset.length_sort, Nat.card_Icc, Nat.add_sub_cancel]

/-- after Mizar FINSEQ_3:47 — restricting `Sgm (Seg (k + n))` to
`Seg k` gives `Sgm (Seg k)` (restriction restated as `List.take`).
GUESSED-NAME: `List.take_range'`. -/
theorem finseq3_47 {k n : ℕ} : (sgm (seg (k + n))).take k = sgm (seg k) := by
  rw [sgm_seg_eq_idseq, sgm_seg_eq_idseq]
  unfold idseq
  apply List.ext_getElem
  · simp only [List.length_take, List.length_range']
    omega
  · intro i h1 h2
    rw [List.getElem_take, List.getElem_range', List.getElem_range']

/-- after Mizar FINSEQ_3:48 — `Sgm (Seg k)` is the identity sequence
`idseq k`. (Proved as the auxiliary `sgm_seg_eq_idseq` above, so
that FINSEQ_3:47 could use it.) -/
theorem finseq3_48 {k : ℕ} : sgm (seg k) = idseq k :=
  sgm_seg_eq_idseq k

/-- after Mizar FINSEQ_3:49 — restricting `p` to `Seg n` (restated
as `List.take n`) returns `p` iff `len p ≤ n`. GUESSED-NAME:
`List.take_of_length_le`, `List.length_take`. -/
theorem finseq3_49 {p : List α} {n : ℕ} :
    p.take n = p ↔ p.length ≤ n := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hlt : (p.take n).length < p.length := by
      rw [List.length_take]
      omega
    rw [h] at hlt
    omega
  · intro h
    exact List.take_of_length_le h

/-- after Mizar FINSEQ_3:50 — restricting `idseq (n + k)` to `Seg n`
gives `idseq n`. GUESSED-NAME: `List.take_range'`. -/
theorem finseq3_50 {n k : ℕ} : (idseq (n + k)).take n = idseq n := by
  unfold idseq
  apply List.ext_getElem
  · simp only [List.length_take, List.length_range']
    omega
  · intro i h1 h2
    rw [List.getElem_take, List.getElem_range', List.getElem_range']

/-- after Mizar FINSEQ_3:51 — restricting `idseq n` to `Seg m`
gives `idseq m` iff `m ≤ n`. GUESSED-NAME: `List.take_range'`,
`List.length_take`. -/
theorem finseq3_51 {n m : ℕ} : (idseq n).take m = idseq m ↔ m ≤ n := by
  constructor
  · intro h
    have hlen := congrArg List.length h
    simp only [idseq, List.length_take, List.length_range'] at hlen
    omega
  · intro h
    unfold idseq
    apply List.ext_getElem
    · simp only [List.length_take, List.length_range']
      omega
    · intro i h1 h2
      rw [List.getElem_take, List.getElem_range', List.getElem_range']

/-- after Mizar FINSEQ_3:52 — restricting `idseq n` to `Seg m`
gives `idseq n` iff `n ≤ m`. GUESSED-NAME: `List.take_range'`,
`List.length_take`. -/
theorem finseq3_52 {n m : ℕ} : (idseq n).take m = idseq n ↔ n ≤ m := by
  constructor
  · intro h
    have hlen := congrArg List.length h
    simp only [idseq, List.length_take, List.length_range'] at hlen
    omega
  · intro h
    unfold idseq
    apply List.ext_getElem
    · simp only [List.length_take, List.length_range']
      omega
    · intro i h1 h2
      simp only [List.getElem_take, List.getElem_range']

/-- after Mizar FINSEQ_3:53 — if `len p = k + l` and `q` is the
restriction of `p` to `Seg k`, then `len q = k`. -/
theorem finseq3_53 {p q : List α} {k l : ℕ} (hlen : p.length = k + l)
    (hq : q = p.take k) : q.length = k := by
  rw [hq, List.length_take, hlen]
  exact min_eq_left (by omega)

/-- after Mizar FINSEQ_3:54 — under the same hypotheses, the domain
of `q` is `Seg k`. -/
theorem finseq3_54 {p q : List α} {k l : ℕ} (hlen : p.length = k + l)
    (hq : q = p.take k) : seg q.length = seg k := by
  rw [finseq3_53 hlen hq]

/-- after Mizar FINSEQ_3:55 — if `len p = k + 1` and `q` is the
restriction of `p` to `Seg k`, then `p` is `q` followed by the single
entry at Mizar position `k + 1` (0-based index `k`).
GUESSED-NAME: `List.take_of_length_le`, `List.take_succ`,
`List.getElem?_eq_getElem`, `Option.toList_some`. -/
theorem finseq3_55 {p q : List α} {k : ℕ} (hlen : p.length = k + 1)
    (hq : q = p.take k) : p = q ++ [(p[k]'(by omega))] := by
  rw [hq]
  have htake : p.take (k + 1) = p := List.take_of_length_le (by omega)
  have hsucc : p.take (k + 1) = p.take k ++ (p[k]?).toList := List.take_succ
  rw [htake] at hsucc
  have hk : k < p.length := by omega
  have hget : (p[k]?) = some (p[k]'hk) :=
    List.getElem?_eq_getElem hk
  rw [hget, Option.toList_some] at hsucc
  exact hsucc

-- STUCK — after Mizar FINSEQ_3:56 — `p | X is FinSequence iff
-- ex k, X /\ dom p = Seg k`.
-- Reason (representation mismatch, not a gap in the mathematics):
-- Mizar's restriction `p | X` of a function to an arbitrary set `X`
-- is a partial function whose domain is `X ∩ dom p`; it is a
-- FinSequence exactly when that domain is an initial segment. The
-- List idiom has no such gappy restriction: the only list-valued
-- candidate (filtering `p` to the indices in `X`) is a list — hence
-- a "FinSequence" — for every `X`, which would falsify the iff as
-- stated (the right-hand side fails e.g. for `X = {2}` and
-- `len p = 2`). A faithful restatement needs a partial-function /
-- `FinSequence`-predicate infrastructure that this brick does not
-- carry. Left in place as STUCK; not restated on a guess and not
-- repaired into a different claim.

/-- after Mizar FINSEQ_3:57 — the preimage of `A` under a
concatenation splits over the factors, at the level of cardinals
(the 0-based restatement's shift cancels in the count).
GUESSED-NAME: `List.countP_append` (via the `card_pre_eq_countP`
helper). -/
theorem finseq3_57 {p q : List α} {A : Finset α} :
    (pre (p ++ q) A).card = (pre p A).card + (pre q A).card := by
  classical
  rw [card_pre_eq_countP, card_pre_eq_countP, card_pre_eq_countP,
    List.countP_append]

/-- after Mizar FINSEQ_3:58 — the preimage of `A` under `p` is
included in its preimage under `p ^ q` (0-based restatement: the
indices of the left factor are indices of the concatenation, with
the same values). Twin: `List.getElem?_append_left`. -/
theorem finseq3_58 {p q : List α} {A : Finset α} :
    pre p A ⊆ pre (p ++ q) A := by
  intro i hi
  simp only [pre, Finset.mem_filter, Finset.mem_range, List.length_append] at hi ⊢
  obtain ⟨hi1, v, hv, hvA⟩ := hi
  exact ⟨by omega, v, by rw [List.getElem?_append_left hi1, hv], hvA⟩

/-- after Mizar FINSEQ_3:59 — deleting the `A`-valued entries from
`p` leaves `len p - card (p " A)` entries. GUESSED-NAME:
`List.countP_add_countP_compl`, `List.length_filter` (via the
`card_pre_eq_countP` helper). -/
theorem finseq3_59 {p : List α} {A : Finset α} :
    (sminus p A).length = p.length - (pre p A).card := by
  classical
  have hsum := List.length_eq_countP_add_countP (fun v => v ∈ A) (l := p)
  rw [card_pre_eq_countP]
  simp only [sminus, ← List.countP_eq_length_filter]
  simp only [Bool.not_eq_true, decide_eq_false_iff_not] at hsum
  rw [hsum]
  omega

/-- after Mizar FINSEQ_3:60 — deletion does not lengthen: the
length of `p - A` is at most `len p`. -/
theorem finseq3_60 {p : List α} {A : Finset α} :
    (sminus p A).length ≤ p.length := by
  rw [finseq3_59]
  exact Nat.sub_le _ _

/-- after Mizar FINSEQ_3:61 — if deleting the `A`-valued entries
changes nothing (`len (p - A) = len p`), then `A` misses the range
of `p` (restated as: no element of `p` lies in `A`).
GUESSED-NAME: `List.getElem?_eq_getElem`, `Finset.card_pos`. -/
theorem finseq3_61 {p : List α} {A : Finset α}
    (h : (sminus p A).length = p.length) : ∀ x ∈ p, x ∉ A := by
  intro x hx hxa
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
  have himem : i ∈ pre p A := by
    simp only [pre, Finset.mem_filter, Finset.mem_range]
    refine ⟨hi, x, ?_, hxa⟩
    rw [List.getElem?_eq_getElem hi, hix]
  have hcard : 1 ≤ (pre p A).card := Finset.card_pos.mpr ⟨i, himem⟩
  have h59 := finseq3_59 (p := p) (A := A)
  omega

/-- after Mizar FINSEQ_3:62 — if `n = len p - card (p " A)`, the
domain of `p - A` is `Seg n`. -/
theorem finseq3_62 {p : List α} {A : Finset α} {n : ℕ}
    (hn : n = p.length - (pre p A).card) :
    seg (sminus p A).length = seg n := by
  rw [finseq3_59, hn]

/-- after Mizar FINSEQ_3:63 — the domain of `p - A` is included in
the domain of `p`. -/
theorem finseq3_63 {p : List α} {A : Finset α} :
    seg (sminus p A).length ⊆ seg p.length := by
  intro x hx
  rw [mem_seg] at hx ⊢
  have h60 := finseq3_60 (p := p) (A := A)
  exact ⟨hx.1, by omega⟩

end ThetLogos.MizarPilot2.B7
