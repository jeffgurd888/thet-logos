import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range

/-!
# ThetLogos.MizarPilot2.B6 — MZ-W1-P2, brick B6: FINSEQ_2 (composition, idseq, constant sequences, pairwise application)

Programme: the Mizar working list, MZ pilot tranche 2 brick B6
(30 FINSEQ_2 items: 42–44, 45–47, 48–53, 55, 56, 58–64, 66–74), on
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

Restatement idiom (tranche 1's, settled; see MizarPilot1.B6): a finite
sequence is a `List α`; `Seg n` is `Finset.range n`; `dom p` is
`Finset.range p.length`; `len p` is `p.length`; `rng p` is restated
as element membership in the list. Mizar indexing is 1-based;
statements below are in the 0-based range-native form, with the shift
recorded per item where it matters.
Sequences over a fixed set `D` (`FinSequence of D`) are `List ↥D`
(lists over the subtype), so `take`/`drop`/`get` stay valued, or the
membership-predicate form `∀ x ∈ p, x ∈ D` where tranche 1 used it.
Composition `p * f` (Mizar's function composition, `p` after `f`) is
reindexing of `p` along `f`, spelled `List.ofFn (fun k => p.get ⟨…⟩)`
— the `.get` form, not the bracket/`GetElem` form, inside lambdas
(tranche 1 repair pin). A permutation is `Equiv.Perm (Fin n)`.
Mizar's `idseq i` (the identity sequence `⟨1, …, i⟩`) is restated
0-based as `(List.range i).map (· + 1)` via the local definition
`idseq` below; Mizar's `n |-> a` (constant sequence) is
`List.replicate n a`; Mizar's pairwise application `F.:(p, q)` is
`List.zipWith (fun a b => F (a, b)) p q`, and its one-sided variants
`F[;](a, p)` / `F[:](p, a)` are the corresponding `List.map` forms.
Where Mizar's `F` is a partial function whose domain merely contains
the relevant rectangle, the restatement takes `F` total
(`α × β → γ`), so the domain hypothesis has no Lean content; this is
recorded per item.
-/

namespace ThetLogos.MizarPilot2.B6

variable {α β γ : Type*}

/-- Restatement device (not a Mizar identifier): Mizar's `idseq i`,
the identity sequence `⟨1, …, i⟩`, in 0-based range-native form. -/
def idseq (i : ℕ) : List ℕ := (List.range i).map (fun j => j + 1)

/-- after Mizar FINSEQ_2:42 — composing a sequence `p` after a
function `f` of `dom p` into itself whose range is all of `dom p`
preserves length: `len (p * f) = len p`. Restatement: `f` is
`Fin p.length → Fin p.length`, `rng f = dom p` is surjectivity of
`f`, and composition is reindexing via `List.ofFn` with `.get`.
(twin: `List.length_ofFn` — exact, function argument implicit) -/
theorem finseq2_42 {p q : List α} {f : Fin p.length → Fin p.length}
    (_hrng : ∀ y : Fin p.length, ∃ x, f x = y)
    (hq : q = List.ofFn (fun k => p.get ⟨(f k).val, (f k).isLt⟩)) :
    q.length = p.length := by
  rw [hq]
  exact List.length_ofFn

/-- after Mizar FINSEQ_2:43 — composing a sequence `p` (with
`i ≤ len p`) after a permutation `f` of `Seg i` gives a sequence of
length `i`: `len (p * f) = i`. Restatement as in FINSEQ_2:42, with
`f` an `Equiv.Perm (Fin i)`. (twin: `List.length_ofFn` — exact) -/
theorem finseq2_43 {p q : List α} {i : ℕ} {f : Equiv.Perm (Fin i)}
    (hp : i ≤ p.length)
    (hq : q = List.ofFn
      (fun k : Fin i => p.get ⟨(f k).val, lt_of_lt_of_le (f k).isLt hp⟩)) :
    q.length = i := by
  rw [hq]
  exact List.length_ofFn

/-- after Mizar FINSEQ_2:44 — composing a sequence `p` after a
permutation `f` of `dom p` preserves length: `len (p * f) = len p`.
Restatement as in FINSEQ_2:42, with `f` an
`Equiv.Perm (Fin p.length)` (surjectivity is then automatic, so
FINSEQ_2:42's range hypothesis has no separate content here).
(twin: `List.length_ofFn` — exact) -/
theorem finseq2_44 {p q : List α} {f : Equiv.Perm (Fin p.length)}
    (hq : q = List.ofFn (fun k => p.get ⟨(f k).val, (f k).isLt⟩)) :
    q.length = p.length := by
  rw [hq]
  exact List.length_ofFn

/-- after Mizar FINSEQ_2:45 — composing a `D`-valued sequence `p`
(with `j ≤ len p`) after a function `f` of `Seg i` into `Seg j`
gives a `D`-valued sequence. Restatement choice: `List ↥D`, so the
composite is valued by construction; the recorded content is its
length. Mizar's side condition (`j = 0` implies `i = 0`) has no Lean
content here: the given `f : Fin i → Fin j` already forces it. -/
theorem finseq2_45 {D : Set α} {p : List D} {i j : ℕ}
    {f : Fin i → Fin j} (hj : j ≤ p.length) :
    (List.ofFn
      (fun k : Fin i => p.get ⟨(f k).val, lt_of_lt_of_le (f k).isLt hj⟩)).length = i
    ∧ ∀ x ∈ List.ofFn
      (fun k : Fin i => p.get ⟨(f k).val, lt_of_lt_of_le (f k).isLt hj⟩),
      (x : α) ∈ D :=
  ⟨List.length_ofFn, fun x _ => x.property⟩

/-- after Mizar FINSEQ_2:46 — composing a `D`-valued sequence `p`
(with `i ≤ len p`) after a function `f` of `Seg i` into itself
gives a `D`-valued sequence. Restatement as in FINSEQ_2:45 with
`j = i`. -/
theorem finseq2_46 {D : Set α} {p : List D} {i : ℕ}
    {f : Fin i → Fin i} (hi : i ≤ p.length) :
    (List.ofFn
      (fun k : Fin i => p.get ⟨(f k).val, lt_of_lt_of_le (f k).isLt hi⟩)).length = i
    ∧ ∀ x ∈ List.ofFn
      (fun k : Fin i => p.get ⟨(f k).val, lt_of_lt_of_le (f k).isLt hi⟩),
      (x : α) ∈ D :=
  ⟨List.length_ofFn, fun x _ => x.property⟩

/-- after Mizar FINSEQ_2:47 — composing a `D`-valued sequence `p`
after a function `f` of `dom p` into itself gives a `D`-valued
sequence. Restatement as in FINSEQ_2:45 with the segment
`Fin p.length`. -/
theorem finseq2_47 {D : Set α} {p : List D}
    {f : Fin p.length → Fin p.length} :
    (List.ofFn (fun k => p.get ⟨(f k).val, (f k).isLt⟩)).length = p.length
    ∧ ∀ x ∈ List.ofFn (fun k => p.get ⟨(f k).val, (f k).isLt⟩),
      (x : α) ∈ D :=
  ⟨List.length_ofFn, fun x _ => x.property⟩

/-- after Mizar FINSEQ_2:48 — the identity function on `Seg k`,
read as a sequence, is a sequence of naturals. Restatement: that
sequence is `idseq k` (see the `idseq` device above); the recorded
content is its length and that every entry lies between `1` and
`k` (the 0-based form of membership in `Seg k` under the `+1`
shift). -/
theorem finseq2_48 {k : ℕ} :
    (idseq k).length = k ∧ ∀ x ∈ idseq k, 1 ≤ x ∧ x ≤ k := by
  constructor
  · simp [idseq]
  · intro x hx
    simp only [idseq, List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    omega

/-- after Mizar FINSEQ_2:49 — the entry of `idseq i` at an index
of `Seg i` is that index itself. Idiom shift: Mizar's index `k`
is 1-based (`1 ≤ k ≤ i`, value `k` at position `k`); here the
position is the 0-based `j.val` and the value is `j.val + 1`. -/
theorem finseq2_49 {i : ℕ} {j : Fin i} :
    (idseq i).get ⟨j.val, by
      simp only [idseq, List.length_map, List.length_range]
      exact j.isLt⟩ = j.val + 1 := by
  show ((List.range i).map (fun t => t + 1))[j.val]'(by
    simp only [List.length_map, List.length_range]
    exact j.isLt) = j.val + 1
  rw [List.getElem_map, List.getElem_range]

/-- after Mizar FINSEQ_2:50 — `idseq 1 = ⟨1⟩`. 0-based form via
the `idseq` device. -/
theorem finseq2_50 : idseq 1 = [1] := by
  simp [idseq, List.range_succ]

/-- after Mizar FINSEQ_2:51 — `idseq (i + 1)` is `idseq i` with
the new last entry `i + 1` appended. 0-based form via the `idseq`
device. -/
theorem finseq2_51 {i : ℕ} : idseq (i + 1) = idseq i ++ [i + 1] := by
  simp only [idseq, List.range_succ, List.map_append, List.map_singleton]

/-- after Mizar FINSEQ_2:52 — `idseq 2 = ⟨1, 2⟩`. 0-based form via
the `idseq` device. -/
theorem finseq2_52 : idseq 2 = [1, 2] := by
  simp [idseq, List.range_succ]

/-- after Mizar FINSEQ_2:53 — `idseq 3 = ⟨1, 2, 3⟩`. 0-based form
via the `idseq` device. -/
theorem finseq2_53 : idseq 3 = [1, 2, 3] := by
  simp [idseq, List.range_succ]

/-- after Mizar FINSEQ_2:55 — `idseq k` is a permutation of
`Seg k`. Restatement: the identity permutation of `Fin k`
realises `idseq k` entry-by-entry (entry at 0-based position
`j.val` is `(e j).val + 1`, the shifted form of FINSEQ_2:49). -/
theorem finseq2_55 {k : ℕ} :
    ∃ e : Equiv.Perm (Fin k), ∀ j : Fin k,
      (idseq k).get ⟨j.val, by
        simp only [idseq, List.length_map, List.length_range]
        exact j.isLt⟩ = (e j).val + 1 :=
  ⟨Equiv.refl (Fin k), fun j => finseq2_49⟩

/-- after Mizar FINSEQ_2:56 — the constant function `(Seg k) --> a`
is a finite sequence. Restatement: as a sequence it is
`List.replicate k a` (Mizar's `k |-> a`); the recorded content is
its length. (twin: `List.length_replicate` — exact) -/
theorem finseq2_56 {a : α} {k : ℕ} : (List.replicate k a).length = k :=
  List.length_replicate

/-- after Mizar FINSEQ_2:58 — the constant sequence of length `0`
is empty: `0 |-> a = ∅`. Restatement: `List.replicate 0 a = []`. -/
theorem finseq2_58 {a : α} : List.replicate 0 a = [] := by
  simp

/-- after Mizar FINSEQ_2:59 — the constant sequence of length `1`
is the singleton: `1 |-> a = ⟨a⟩`. -/
theorem finseq2_59 {a : α} : List.replicate 1 a = [a] := by
  simp

/-- after Mizar FINSEQ_2:60 — the constant sequence of length
`i + 1` is the constant sequence of length `i` with one more `a`
appended: `(i + 1) |-> a = (i |-> a) ^ ⟨a⟩`.
(twin: `List.replicate_succ'` — exact) -/
theorem finseq2_60 {a : α} {i : ℕ} :
    List.replicate (i + 1) a = List.replicate i a ++ [a] :=
  List.replicate_succ'

/-- after Mizar FINSEQ_2:61 — the constant sequence of length `2`
is `⟨a, a⟩`: `2 |-> a = ⟨a, a⟩`. -/
theorem finseq2_61 {a : α} : List.replicate 2 a = [a, a] := by
  simp

/-- after Mizar FINSEQ_2:62 — the constant sequence of length `3`
is `⟨a, a, a⟩`: `3 |-> a = ⟨a, a, a⟩`. -/
theorem finseq2_62 {a : α} : List.replicate 3 a = [a, a, a] := by
  simp

/-- after Mizar FINSEQ_2:63 — the constant sequence `k |-> d` at
an element `d` of `D` is a sequence of `D`. Restatement choice:
`List ↥D`, so `List.replicate k d` is valued by construction; the
recorded content is its length and that every entry lies in `D`. -/
theorem finseq2_63 {D : Set α} {d : D} {k : ℕ} :
    (List.replicate k d).length = k
    ∧ ∀ x ∈ List.replicate k d, (x : α) ∈ D :=
  ⟨List.length_replicate, fun x _ => x.property⟩

/-- after Mizar FINSEQ_2:64 — for a function `F` defined on the
rectangle `[:rng p, rng q:]`, the pairwise application `F.:(p, q)`
is a finite sequence. Restatement: `F` is taken total
(`α × β → γ`), so the domain hypothesis has no Lean content and
being a `List` is automatic; the recorded content is the length
of the pairwise application. -/
theorem finseq2_64 {p : List α} {q : List β} {F : α × β → γ} :
    (List.zipWith (fun a b => F (a, b)) p q).length
      = min p.length q.length :=
  List.length_zipWith

/-- after Mizar FINSEQ_2:66 — for a function `F` defined on
`[:{a}, rng p:]`, the left-section application `F[;](a, p)` is a
finite sequence. Restatement as in FINSEQ_2:64, with the section
as `List.map`; the recorded content is its length.
(twin: `List.length_map` — exact) -/
theorem finseq2_66 {F : α × β → γ} {a : α} {p : List β} :
    (p.map (fun x => F (a, x))).length = p.length := by
  rw [List.length_map]

/-- after Mizar FINSEQ_2:67 — the length of the left-section
application: if `r = F[;](a, p)` then `len r = len p`.
Restatement as in FINSEQ_2:66. (The brick's source line carries
no conclusion after `r = F[;](a, p)`; the conclusion is restated
by the pattern of FINSEQ_2:69, its right-section twin.) -/
theorem finseq2_67 {F : α × β → γ} {a : α} {p : List β} {r : List γ}
    (hr : r = p.map (fun x => F (a, x))) : r.length = p.length := by
  rw [hr, List.length_map]

/-- after Mizar FINSEQ_2:68 — for a function `F` defined on
`[:rng p, {a}:]`, the right-section application `F[:](p, a)` is a
finite sequence. Restatement as in FINSEQ_2:66 on the other side.
(twin: `List.length_map` — exact) -/
theorem finseq2_68 {F : α × β → γ} {p : List α} {a : β} :
    (p.map (fun x => F (x, a))).length = p.length := by
  rw [List.length_map]

/-- after Mizar FINSEQ_2:69 — the length of the right-section
application: if `r = F[:](p, a)` then `len r = len p`.
Restatement as in FINSEQ_2:68. -/
theorem finseq2_69 {F : α × β → γ} {p : List α} {a : β} {r : List γ}
    (hr : r = p.map (fun x => F (x, a))) : r.length = p.length := by
  rw [hr, List.length_map]

/-- after Mizar FINSEQ_2:70 — for a function `F` of
`[:D, D9:]` into `E`, the pairwise application `F.:(p, q)` of a
sequence `p` of `D` and a sequence `q` of `D9` is a sequence of
`E`. Restatement choice: `List ↥D`, `List ↥D9`, `List ↥E`, so the
application is valued by construction; the recorded content is
its length and that every entry lies in `E`. -/
theorem finseq2_70 {D : Set α} {D9 : Set β} {E : Set γ}
    {F : D × D9 → E} {p : List D} {q : List D9} :
    (List.zipWith (fun a b => F (a, b)) p q).length
      = min p.length q.length
    ∧ ∀ z ∈ List.zipWith (fun a b => F (a, b)) p q, (z : γ) ∈ E :=
  ⟨List.length_zipWith, fun z _ => z.property⟩

/-- after Mizar FINSEQ_2:71 — the length of the pairwise
application is the minimum of the lengths: if `r = F.:(p, q)`
then `len r = min (len p, len q)`. Restatement as in
FINSEQ_2:70. (twin: `List.length_zipWith` — exact) -/
theorem finseq2_71 {D : Set α} {D9 : Set β} {E : Set γ}
    {F : D × D9 → E} {p : List D} {q : List D9} {r : List E}
    (hr : r = List.zipWith (fun a b => F (a, b)) p q) :
    r.length = min p.length q.length := by
  rw [hr]
  exact List.length_zipWith

/-- after Mizar FINSEQ_2:72 — when `len p = len q`, the pairwise
application has that common length: `len r = len p` and
`len r = len q`. Restatement as in FINSEQ_2:70. -/
theorem finseq2_72 {D : Set α} {D9 : Set β} {E : Set γ}
    {F : D × D9 → E} {p : List D} {q : List D9} {r : List E}
    (hlen : p.length = q.length)
    (hr : r = List.zipWith (fun a b => F (a, b)) p q) :
    r.length = p.length ∧ r.length = q.length := by
  simp [hr, List.length_zipWith, hlen]

/-- after Mizar FINSEQ_2:73 — the pairwise application against an
empty sequence is empty, on either side:
`F.:(⟨⟩D, q) = ⟨⟩E` and `F.:(p, ⟨⟩D9) = ⟨⟩E`. Restatement as in
FINSEQ_2:70. -/
theorem finseq2_73 {D : Set α} {D9 : Set β} {E : Set γ}
    {F : D × D9 → E} {p : List D} {q : List D9} :
    List.zipWith (fun a b => F (a, b)) ([] : List D) q = ([] : List E)
    ∧ List.zipWith (fun a b => F (a, b)) p ([] : List D9) = ([] : List E) := by
  simp

/-- after Mizar FINSEQ_2:74 — the pairwise application of two
singletons is the singleton of the value:
`F.:(⟨d1⟩, ⟨d19⟩) = ⟨F (d1, d19)⟩`. Restatement as in
FINSEQ_2:70. -/
theorem finseq2_74 {D : Set α} {D9 : Set β} {E : Set γ}
    {F : D × D9 → E} {d₁ : D} {d₁₉ : D9} :
    List.zipWith (fun a b => F (a, b)) [d₁] [d₁₉] = [F (d₁, d₁₉)] := by
  simp

end ThetLogos.MizarPilot2.B6
