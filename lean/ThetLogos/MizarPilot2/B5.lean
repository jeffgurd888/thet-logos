import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# ThetLogos.MizarPilot2.B5 — MZ pilot wave tranche 2, brick B5: FINSEQ_1 remainder (singletons, last-element split, finiteness, Seg arithmetic, concatenation indexing)

Programme: the Mizar working list, MZ pilot wave tranche 2 brick B5
(MZ-W1-P2; 24 FINSEQ_1 items: 41–46, 48–50, 52, 54–62, 64, 65, 72–74),
on Zero's 2026-11-09 pilot call.
**NO CLAIM; dials 0/4.**

Protocol: every item is restated + proved here; probe verdicts are
recorded as twin-notes in the doc-comments, never as skips.
Each declaration below is a restatement, from the mathematics, of one
Mizar item, proved in this environment; its doc-comment carries the
priority credit "after Mizar ⟨ARTICLE:ordinal⟩" — Mizar proved it first,
in its system (Tarski–Grothendieck set theory); we re-proved our
restatement in ours (dependent type theory). No Mizar text appears in
this file.

Restatement idiom (tranche 1's, settled, carried into tranche 2): a
finite sequence is a `List α`; `Seg n` is `Finset.range n`; `dom p` is
`Finset.range p.length`; `p ^ q` is `p ++ q`; restriction `p | A` is
`List.take`; `len p` is `p.length`; `rng p` is restated as element
membership in the list. Mizar sequence indexing is 1-based (the item
at position `i` is `p[i-1]` in Lean `getElem` terms); Mizar's `Seg n`
is the 1-based segment `{1, …, n}`, while `Finset.range n` is the
0-based `{0, …, n-1}` — items whose Mizar statement is about `Seg`
itself are therefore restated in range-native form, with the shift
recorded in each item's doc-comment, as tranche 1 did for FINSEQ_2:7.
D-valued / `FinSequence of D` is restated with a predicate
`P : α → Prop` holding of every element. Two items in this brick
(FINSEQ_1:54, 55, 57) keep `Seg n` as `Finset.Icc 1 n` instead, because
their content is the comparison of `Seg n` with `n` itself — in pure
range form that comparison would collapse to a vacuous identity, and
the shift is recorded in each doc-comment.

Imports: tranche-1 narrow set (`Mathlib.Data.Finset.Range`,
`Mathlib.Data.Finset.Sort`, `Mathlib.Data.Fintype.Card`,
`Mathlib.Data.List.Basic`, `Mathlib.Data.List.Range`) plus two narrow
additions this brick needs — `Mathlib.Data.Set.Finite.Basic` (the
`Set.Finite` API for FINSEQ_1:52, 56) and
`Mathlib.Order.Interval.Finset.Nat` (`Nat.card_Icc` for FINSEQ_1:54,
55, 57). Still narrow, NOT full Mathlib.
-/

namespace ThetLogos.MizarPilot2.B5

variable {α : Type*}

/-- after Mizar FINSEQ_1:41 — the first element of a singleton
concatenated on the left is the singleton's element (position 1 is
index 0 in the 0-based idiom). -/
theorem finseq1_41 {x : α} {p : List α} : ([x] ++ p)[0]? = some x := by
  simp

/-- after Mizar FINSEQ_1:42 — the element appended on the right sits at
position `len p + 1` (index `len p` in the 0-based idiom).
GUESSED-NAME: `List.getElem?_append_right` (same name as tranche 1's
FINSEQ_1:23/24). -/
theorem finseq1_42 {p : List α} {x : α} : (p ++ [x])[p.length]? = some x := by
  rw [List.getElem?_append_right (le_refl _)]
  simp

/-- after Mizar FINSEQ_1:43 — a three-element sequence splits after the
first element and after the second. -/
theorem finseq1_43 {x y z : α} :
    [x, y, z] = [x] ++ [y, z] ∧ [x, y, z] = [x, y] ++ [z] :=
  ⟨rfl, rfl⟩

/-- after Mizar FINSEQ_1:44 — a sequence is `<*x,y*>` iff its length is
2 and its values at positions 1 and 2 are `x` and `y` (positions 1, 2
are indices 0, 1 in the 0-based idiom; values read through the total
lookup `p[k]?`). -/
theorem finseq1_44 {p : List α} {x y : α} :
    p = [x, y] ↔ p.length = 2 ∧ p[0]? = some x ∧ p[1]? = some y := by
  constructor
  · intro h
    subst h
    simp
  · rintro ⟨hl, h0, h1⟩
    cases p with
    | nil => simp at hl
    | cons a p =>
      cases p with
      | nil => simp at hl
      | cons b p =>
        cases p with
        | cons c p =>
          simp only [List.length_cons] at hl
          omega
        | nil =>
          have hax : a = x := by simpa using h0
          have hby : b = y := by simpa using h1
          rw [hax, hby]

/-- after Mizar FINSEQ_1:45 — a sequence is `<*x,y,z*>` iff its length
is 3 and its values at positions 1, 2, 3 are `x`, `y`, `z` (positions
1, 2, 3 are indices 0, 1, 2 in the 0-based idiom; values read through
the total lookup `p[k]?`). -/
theorem finseq1_45 {p : List α} {x y z : α} :
    p = [x, y, z] ↔ p.length = 3 ∧ p[0]? = some x ∧ p[1]? = some y ∧
      p[2]? = some z := by
  constructor
  · intro h
    subst h
    simp
  · rintro ⟨hl, h0, h1, h2⟩
    cases p with
    | nil => simp at hl
    | cons a p =>
      cases p with
      | nil => simp at hl
      | cons b p =>
        cases p with
        | nil => simp at hl
        | cons c p =>
          cases p with
          | nil =>
            have hax : a = x := by simpa using h0
            have hby : b = y := by simpa using h1
            have hcz : c = z := by simpa using h2
            rw [hax, hby, hcz]
          | cons d p =>
            simp only [List.length_cons] at hl
            omega

/-- after Mizar FINSEQ_1:46 — a nonempty sequence splits as a sequence
followed by its last element.
GUESSED-NAME: `List.dropLast_append_getLast` (and `List.getLast`). -/
theorem finseq1_46 {p : List α} (h : p ≠ []) :
    ∃ q x, p = q ++ [x] :=
  ⟨p.dropLast, p.getLast h, (List.dropLast_append_getLast h).symm⟩

/-- after Mizar FINSEQ_1:48 — injective sequences with the same range
have the same length (`rng` restated as membership; one-to-one
restated as `List.Nodup`).
GUESSED-NAME: `List.toFinset_card_of_nodup`, `List.mem_toFinset`. -/
theorem finseq1_48 [DecidableEq α] {p q : List α}
    (h : ∀ x, x ∈ p ↔ x ∈ q) (hp : p.Nodup) (hq : q.Nodup) :
    p.length = q.length := by
  have hset : p.toFinset = q.toFinset := by
    ext x
    simp only [List.mem_toFinset]
    exact h x
  have hcard := congrArg Finset.card hset
  rw [List.toFinset_card_of_nodup hp, List.toFinset_card_of_nodup hq] at hcard
  exact hcard

/-- after Mizar FINSEQ_1:49 — the empty sequence is a `D`-sequence
(`D*` membership restated as: every element of the empty list
satisfies the predicate `P`). -/
theorem finseq1_49 {P : α → Prop} : ∀ x ∈ ([] : List α), P x := by
  simp

/-- after Mizar FINSEQ_1:50 — the range of the increasing enumeration
of a sequence's domain is the domain itself. Idiom: `Sgm (dom p)` is
the increasing enumeration `List.range p.length` of `dom p =
Finset.range p.length`, and `rng` is restated as membership.
(twin: `List.mem_range` / `Finset.mem_range` — both sides are the
same `< length` condition) -/
theorem finseq1_50 {p : List α} {x : ℕ} :
    x ∈ List.range p.length ↔ x ∈ Finset.range p.length := by
  simp only [List.mem_range, Finset.mem_range]

/-- after Mizar FINSEQ_1:52 — a set is finite iff it is the range of
some finite sequence (`rng p` restated as membership).
GUESSED-NAME: `Set.Finite.exists_finset`, `Finset.mem_toList`,
`Finset.finite_toSet`, `List.mem_toFinset`. -/
theorem finseq1_52 [DecidableEq α] {D : Set α} :
    D.Finite ↔ ∃ p : List α, ∀ x, x ∈ D ↔ x ∈ p := by
  constructor
  · intro hD
    obtain ⟨t, ht⟩ := hD.exists_finset
    exact ⟨t.toList, fun x => (ht x).symm.trans Finset.mem_toList.symm⟩
  · rintro ⟨p, hp⟩
    have hDeq : D = ↑p.toFinset := by
      ext x
      simp only [Finset.mem_coe, List.mem_toFinset]
      exact hp x
    rw [hDeq]
    exact Finset.finite_toSet _

/-- after Mizar FINSEQ_1:54 — `Seg n` and `n` are equipotent. Idiom
shift (flagged): `Seg n` is kept here as `Finset.Icc 1 n`, the 1-based
segment itself, and `n` as a set is `Finset.range n` — in pure
range-native form the statement would collapse to the vacuous
identity `range n ≃ range n`, so the comparison is stated between the
two forms and proved by the `+1` shift in cardinality.
GUESSED-NAME: `Finset.equivOfCardEq`, `Nat.card_Icc`. -/
theorem finseq1_54 {n : ℕ} :
    Nonempty (Finset.range n ≃ Finset.Icc 1 n) := by
  have hcard : (Finset.range n).card = (Finset.Icc 1 n).card := by
    simp [Finset.card_range, Nat.card_Icc]
  exact ⟨Finset.equivOfCardEq hcard⟩

/-- after Mizar FINSEQ_1:55 — the cardinality of `Seg n` equals the
cardinality of `n` (as a set). Idiom shift: `Seg n` is `Finset.Icc
1 n` and `n` as a set is `Finset.range n` (see FINSEQ_1:54).
(twin: `Nat.card_Icc` — via `Finset.card_range`) -/
theorem finseq1_55 {n : ℕ} :
    (Finset.Icc 1 n).card = (Finset.range n).card := by
  simp [Finset.card_range, Nat.card_Icc]

/-- after Mizar FINSEQ_1:56 — a finite set is equipotent to some
`Seg n`. Idiom shift: `Seg n` is identified with `Fin n` (Mizar's
`n` as a set is `{0, …, n-1}`, the 0-based ordinal); the 1-based
`Seg n` form is equipotent to it by the `+1` shift of FINSEQ_1:54.
GUESSED-NAME: `Set.Finite.fintype`, `Fintype.equivFinOfCardEq`. -/
theorem finseq1_56 {D : Set α} (hD : D.Finite) :
    ∃ n, Nonempty (↥D ≃ Fin n) := by
  letI := hD.fintype
  exact ⟨Fintype.card ↥D, ⟨Fintype.equivFinOfCardEq rfl⟩⟩

/-- after Mizar FINSEQ_1:57 — the cardinality of `Seg n` is `n`.
Idiom shift: `Seg n` is `Finset.Icc 1 n` (see FINSEQ_1:54).
(twin: `Nat.card_Icc` — exact, after the `n + 1 - 1` simplification) -/
theorem finseq1_57 {n : ℕ} : (Finset.Icc 1 n).card = n := by
  simp [Nat.card_Icc]

/-- after Mizar FINSEQ_1:58 — restricting a sequence at a bound at or
past its length leaves it unchanged. (twin-candidate:
`List.take_of_length_le` — GUESSED-NAME, believed correct for this
pin but not attested in tranche 1's landed file) -/
theorem finseq1_58 {q : List α} {i : ℕ} (h : q.length ≤ i) :
    q.take i = q :=
  List.take_of_length_le h

/-- after Mizar FINSEQ_1:59 — restricting a sequence at a bound within
its length gives a sequence of exactly that length.
(twin: `List.length_take` — the bound, as in tranche 1's
FINSEQ_1:17) -/
theorem finseq1_59 {q : List α} {i : ℕ} (h : i ≤ q.length) :
    (q.take i).length = i := by
  rw [List.length_take, min_eq_left h]

/-- after Mizar FINSEQ_1:60 — shifting an element of an initial segment
by `m` lands in the shifted segment. Idiom shift: Mizar's
`i ∈ Seg n → i + m ∈ Seg (n + m)` (1-based, `1 ≤ i ≤ n`) becomes the
range-native `i ∈ range n → i + m ∈ range (n + m)`. -/
theorem finseq1_60 {i n m : ℕ} (h : i ∈ Finset.range n) :
    i + m ∈ Finset.range (n + m) := by
  simp only [Finset.mem_range] at h ⊢
  omega

/-- after Mizar FINSEQ_1:61 — a positive index whose shift lands in the
shifted segment lies in both segments. Idiom shift: Mizar's
`i ∈ Seg n ∧ i ∈ Seg (n + m)` (1-based) becomes the range-native
`i ∈ range n ∧ i ∈ range (n + m)`; the hypothesis `i > 0` is kept
for fidelity and is vacuous in the 0-based idiom. -/
theorem finseq1_61 {i n m : ℕ} (_h1 : 0 < i)
    (h2 : i + m ∈ Finset.range (n + m)) :
    i ∈ Finset.range n ∧ i ∈ Finset.range (n + m) := by
  simp only [Finset.mem_range] at h2 ⊢
  omega

/-- after Mizar FINSEQ_1:62 — if `D1 ⊆ D2` then every `D1`-sequence is
a `D2`-sequence (`D*` restated as predicate-form lists: a sequence
whose elements all satisfy `P` has all its elements satisfying `Q`
whenever `P` implies `Q`). -/
theorem finseq1_62 {P Q : α → Prop} (h : ∀ x, P x → Q x) {p : List α}
    (hp : ∀ x ∈ p, P x) : ∀ x ∈ p, Q x :=
  fun x hx => h x (hp x hx)

/-- after Mizar FINSEQ_1:64 — indexing a concatenation inside the left
factor (1-based position `i`, `1 ≤ i ≤ len p`, is index `i - 1`).
GUESSED-NAME: `List.getElem?_append_left`. -/
theorem finseq1_64 {p q : List α} {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ p.length) :
    (p ++ q)[i - 1]? = p[i - 1]? :=
  List.getElem?_append_left (by omega)

/-- after Mizar FINSEQ_1:65 — indexing a concatenation inside the right
factor (1-based position `len p + i`, `1 ≤ i ≤ len q`, is index
`len p + i - 1`; the right factor's value is at shifted index
`len p + i - 1 - len p`, as in tranche 1's FINSEQ_1:23/24).
GUESSED-NAME: `List.getElem?_append_right` (same name as tranche 1's
FINSEQ_1:23/24). -/
theorem finseq1_65 {p q : List α} {i : ℕ} (h1 : 1 ≤ i) (_h2 : i ≤ q.length) :
    (p ++ q)[p.length + i - 1]? = q[p.length + i - 1 - p.length]? :=
  List.getElem?_append_right (by omega)

/-- after Mizar FINSEQ_1:72 — restricting a sequence to the empty
segment gives the empty sequence (`Seg 0` is empty, so the restriction
is `p.take 0`). -/
theorem finseq1_72 {p : List α} : p.take 0 = [] := by
  simp

/-- after Mizar FINSEQ_1:73 — restrictions of any two sequences to the
empty segment agree (both are empty, by FINSEQ_1:72). -/
theorem finseq1_73 {f g : List α} : f.take 0 = g.take 0 := by
  rw [finseq1_72, finseq1_72]

/-- after Mizar FINSEQ_1:74 — the singleton of an element of `D` is a
`D`-sequence (`FinSequence of D` restated as a predicate `P` holding
of every element). -/
theorem finseq1_74 {P : α → Prop} {x : α} (hx : P x) :
    ∀ y ∈ [x], P y := by
  intro y hy
  have hyx : y = x := by simpa using hy
  rw [hyx]
  exact hx

end ThetLogos.MizarPilot2.B5
