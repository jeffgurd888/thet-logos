import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Prod
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic

/-!
# Mizar Pilot Tranche 1 — Brick B4 (RELSET_1, FINSET_1)

Programme credit: Mizar working list, MZ pilot tranche 1, brick B4;
Zero's 2026-11-09 pilot call.

**NO CLAIM; dials 0/4.**

Protocol: one theorem per Mizar item, restated in the idiom below;
priority for the underlying results belongs to the Mizar authors
(RELSET_1 / FINSET_1). This file is a restatement draft only.

Restatement idiom (recorded for this brick):
* A Mizar relation on sets is a set of ordered pairs:
  `R : Set (α × β)`.
* "`R` is Relation of `X, Y`" is read as `R ⊆ X ×ˢ Y`
  (`Set.prod`), with `X : Set α`, `Y : Set β`.
* `dom R` is read as `Prod.fst '' R`; `rng R` as `Prod.snd '' R`.
* `field R` (RELSET_1:8) needs one ambient type, so it is read,
  for `R : Set (α × α)`, as `Prod.fst '' R ∪ Prod.snd '' R`.
* The converse `R~` is read as `{p : β × α | (p.2, p.1) ∈ R}`.
* `id X` is read as `{p : α × α | p.2 = p.1 ∧ p.1 ∈ X}`.
* Domain restriction `R|X1` is read as `{p | p ∈ R ∧ p.1 ∈ X1}`;
  codomain restriction `Y1|`R` is read as `{p | p ∈ R ∧ p.2 ∈ Y1}`.
* Where Mizar works in the ambient context "`R` is a Relation of
  `X, Y`", that context is made explicit as a hypothesis
  `hR : R ⊆ X ×ˢ Y`.
* FINSET_1: the finite set is a `Finset α`; finiteness of a
  `Set α` is `Set.Finite` (being covered by a `Finset`).
-/

namespace ThetLogos.MizarPilot1.B4

/-- after Mizar RELSET_1:1 — a subset of a relation of X, Y is again
a relation of X, Y. Mizar: `A c= R implies A is Relation of X,Y`. -/
theorem relset_1_1 {α β : Type*} {X : Set α} {Y : Set β} {R A : Set (α × β)}
    (hR : R ⊆ X ×ˢ Y) (hA : A ⊆ R) : A ⊆ X ×ˢ Y :=
  fun _ hx => hR (hA hx)

/-- after Mizar RELSET_1:2 — every element of a relation of X, Y is a
pair `[x, y]` with `x ∈ X` and `y ∈ Y`.
Mizar: `a in R implies ex x,y st a = [x,y] & x in X & y in Y`. -/
theorem relset_1_2 {α β : Type*} {X : Set α} {Y : Set β} {R : Set (α × β)}
    (hR : R ⊆ X ×ˢ Y) {a : α × β} (ha : a ∈ R) :
    ∃ x ∈ X, ∃ y ∈ Y, a = (x, y) := by
  obtain ⟨x, y⟩ := a
  exact ⟨x, (hR ha).1, y, (hR ha).2, rfl⟩

/-- after Mizar RELSET_1:3 — a singleton pair from X and Y is a
relation of X, Y.
Mizar: `x in X & y in Y implies {[x,y]} is Relation of X,Y`. -/
theorem relset_1_3 {α β : Type*} {X : Set α} {Y : Set β} {x : α} {y : β}
    (hx : x ∈ X) (hy : y ∈ Y) : ({(x, y)} : Set (α × β)) ⊆ X ×ˢ Y := by
  intro p hp
  rw [Set.mem_singleton_iff] at hp
  rw [hp]
  exact ⟨hx, hy⟩

/-- after Mizar RELSET_1:4 — a relation whose domain lies in X and
whose range lies in Y is a relation of X, Y.
Mizar: `for R being Relation st dom R c= X & rng R c= Y holds
R is Relation of X,Y`. -/
theorem relset_1_4 {α β : Type*} {X : Set α} {Y : Set β} {R : Set (α × β)}
    (hdom : Prod.fst '' R ⊆ X) (hrng : Prod.snd '' R ⊆ Y) :
    R ⊆ X ×ˢ Y := by
  rintro ⟨x, y⟩ h
  exact ⟨hdom ⟨(x, y), h, rfl⟩, hrng ⟨(x, y), h, rfl⟩⟩

/-- after Mizar RELSET_1:5 — enlarging the domain bound keeps a
relation of X, Y a relation of the larger first set.
Mizar: `dom R c= X1 implies R is Relation of X1,Y`. -/
theorem relset_1_5 {α β : Type*} {X X1 : Set α} {Y : Set β} {R : Set (α × β)}
    (hR : R ⊆ X ×ˢ Y) (hdom : Prod.fst '' R ⊆ X1) : R ⊆ X1 ×ˢ Y := by
  rintro ⟨x, y⟩ h
  exact ⟨hdom ⟨(x, y), h, rfl⟩, (hR h).2⟩

/-- after Mizar RELSET_1:6 — enlarging the range bound keeps a
relation of X, Y a relation of the larger second set.
Mizar: `rng R c= Y1 implies R is Relation of X,Y1`. -/
theorem relset_1_6 {α β : Type*} {X : Set α} {Y Y1 : Set β} {R : Set (α × β)}
    (hR : R ⊆ X ×ˢ Y) (hrng : Prod.snd '' R ⊆ Y1) : R ⊆ X ×ˢ Y1 := by
  rintro ⟨x, y⟩ h
  exact ⟨(hR h).1, hrng ⟨(x, y), h, rfl⟩⟩

/-- after Mizar RELSET_1:7 — a relation of X, Y is a relation of any
larger pair of sets.
Mizar: `X c= X1 & Y c= Y1 implies R is Relation of X1,Y1`. -/
theorem relset_1_7 {α β : Type*} {X X1 : Set α} {Y Y1 : Set β} {R : Set (α × β)}
    (hR : R ⊆ X ×ˢ Y) (hX : X ⊆ X1) (hY : Y ⊆ Y1) : R ⊆ X1 ×ˢ Y1 := by
  intro p hp
  exact ⟨hX (hR hp).1, hY (hR hp).2⟩

/-- after Mizar RELSET_1:8 — the field of a relation of X, Y lies in
`X ∪ Y`. Stated at a single ambient type, with `field R` read as
`dom R ∪ rng R`. Mizar: `field R c= X \/ Y`. -/
theorem relset_1_8 {α : Type*} {X Y : Set α} {R : Set (α × α)}
    (hR : R ⊆ X ×ˢ Y) : Prod.fst '' R ∪ Prod.snd '' R ⊆ X ∪ Y := by
  intro z hz
  rcases hz with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · exact Or.inl (hR hp).1
  · exact Or.inr (hR hp).2

/-- after Mizar RELSET_1:9 — every element of X starts a pair of R
iff the domain of R is all of X (in the ambient context that R is a
relation of X, Y).
Mizar: `(for x being object st x in X ex y being object st [x,y] in R)
iff dom R = X`. -/
theorem relset_1_9 {α β : Type*} {X : Set α} {Y : Set β} {R : Set (α × β)}
    (hR : R ⊆ X ×ˢ Y) :
    (∀ x ∈ X, ∃ y, (x, y) ∈ R) ↔ Prod.fst '' R = X := by
  constructor
  · intro h
    apply Set.Subset.antisymm
    · rintro x ⟨p, hp, rfl⟩
      exact (hR hp).1
    · intro x hx
      obtain ⟨y, hy⟩ := h x hx
      exact ⟨(x, y), hy, rfl⟩
  · intro h x hx
    rw [← h] at hx
    obtain ⟨⟨x', y⟩, hxy, hx'⟩ := hx
    have hxx : x' = x := hx'
    subst hxx
    exact ⟨y, hxy⟩

/-- after Mizar RELSET_1:10 — every element of Y ends a pair of R
iff the range of R is all of Y (in the ambient context that R is a
relation of X, Y).
Mizar: `(for y being object st y in Y ex x being object st [x,y] in R)
iff rng R = Y`. -/
theorem relset_1_10 {α β : Type*} {X : Set α} {Y : Set β} {R : Set (α × β)}
    (hR : R ⊆ X ×ˢ Y) :
    (∀ y ∈ Y, ∃ x, (x, y) ∈ R) ↔ Prod.snd '' R = Y := by
  constructor
  · intro h
    apply Set.Subset.antisymm
    · rintro y ⟨p, hp, rfl⟩
      exact (hR hp).2
    · intro y hy
      obtain ⟨x, hx⟩ := h y hy
      exact ⟨(x, y), hx, rfl⟩
  · intro h y hy
    rw [← h] at hy
    obtain ⟨⟨x, y'⟩, hxy, hy'⟩ := hy
    have hyy : y' = y := hy'
    subst hyy
    exact ⟨x, hxy⟩

/-- after Mizar RELSET_1:11 — domain and range swap under the
converse relation `R~`, here read as `{p : β × α | (p.2, p.1) ∈ R}`.
Mizar: `dom (R~) = rng R & rng (R~) = dom R`. -/
theorem relset_1_11 {α β : Type*} (R : Set (α × β)) :
    Prod.fst '' {p : β × α | (p.2, p.1) ∈ R} = Prod.snd '' R ∧
    Prod.snd '' {p : β × α | (p.2, p.1) ∈ R} = Prod.fst '' R := by
  constructor
  · ext y
    constructor
    · rintro ⟨⟨y', x⟩, hp, rfl⟩
      exact ⟨(x, y'), hp, rfl⟩
    · rintro ⟨⟨x, y'⟩, hp, rfl⟩
      exact ⟨(y', x), hp, rfl⟩
  · ext x
    constructor
    · rintro ⟨⟨y, x'⟩, hp, rfl⟩
      exact ⟨(x', y), hp, rfl⟩
    · rintro ⟨⟨x', y⟩, hp, rfl⟩
      exact ⟨(y, x'), hp, rfl⟩

/-- after Mizar RELSET_1:12 — the empty set is a relation of X, Y.
Mizar: `{} is Relation of X,Y`. -/
theorem relset_1_12 {α β : Type*} {X : Set α} {Y : Set β} :
    (∅ : Set (α × β)) ⊆ X ×ˢ Y :=
  Set.empty_subset _

/-- after Mizar RELSET_1:13 — the identity relation on X lies in
`X × X`, with `id X` read as `{p : α × α | p.2 = p.1 ∧ p.1 ∈ X}`.
Mizar: `id X c= [:X,X:]`. -/
theorem relset_1_13 {α : Type*} {X : Set α} :
    {p : α × α | p.2 = p.1 ∧ p.1 ∈ X} ⊆ X ×ˢ X := by
  rintro ⟨x, y⟩ ⟨h, hx⟩
  have hy : (x, y).2 ∈ X := by
    rw [h]
    exact hx
  exact ⟨hx, hy⟩

/-- after Mizar RELSET_1:14 — the identity relation on X is a
relation of X, X. In this brick's idiom "is Relation of X, X" and
the inclusion of RELSET_1:13 are the same statement `⊆ X ×ˢ X`.
Mizar: `id X is Relation of X,X`. -/
theorem relset_1_14 {α : Type*} {X : Set α} :
    {p : α × α | p.2 = p.1 ∧ p.1 ∈ X} ⊆ X ×ˢ X :=
  relset_1_13

/-- after Mizar RELSET_1:15 — if the identity relation on A is
contained in R, then A lies in both the domain and the range of R.
Mizar: `id A c= R implies A c= dom R & A c= rng R`. -/
theorem relset_1_15 {α : Type*} {A : Set α} {R : Set (α × α)}
    (h : {p : α × α | p.2 = p.1 ∧ p.1 ∈ A} ⊆ R) :
    A ⊆ Prod.fst '' R ∧ A ⊆ Prod.snd '' R := by
  constructor
  · intro x hx
    exact ⟨(x, x), h ⟨rfl, hx⟩, rfl⟩
  · intro x hx
    exact ⟨(x, x), h ⟨rfl, hx⟩, rfl⟩

/-- after Mizar RELSET_1:16 — if the identity relation on X is
contained in R (a relation of X, Y), then X is the domain of R and
lies in its range.
Mizar: `id X c= R implies X = dom R & X c= rng R`. -/
theorem relset_1_16 {α : Type*} {X Y : Set α} {R : Set (α × α)}
    (hR : R ⊆ X ×ˢ Y) (h : {p : α × α | p.2 = p.1 ∧ p.1 ∈ X} ⊆ R) :
    X = Prod.fst '' R ∧ X ⊆ Prod.snd '' R := by
  refine ⟨?_, (relset_1_15 h).2⟩
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨(x, x), h ⟨rfl, hx⟩, rfl⟩
  · rintro x ⟨p, hp, rfl⟩
    exact (hR hp).1

/-- after Mizar RELSET_1:17 — if the identity relation on Y is
contained in R (a relation of X, Y), then Y lies in the domain of R
and is its range.
Mizar: `id Y c= R implies Y c= dom R & Y = rng R`. -/
theorem relset_1_17 {α : Type*} {X Y : Set α} {R : Set (α × α)}
    (hR : R ⊆ X ×ˢ Y) (h : {p : α × α | p.2 = p.1 ∧ p.1 ∈ Y} ⊆ R) :
    Y ⊆ Prod.fst '' R ∧ Y = Prod.snd '' R := by
  refine ⟨(relset_1_15 h).1, ?_⟩
  apply Set.Subset.antisymm
  · intro y hy
    exact ⟨(y, y), h ⟨rfl, hy⟩, rfl⟩
  · rintro y ⟨p, hp, rfl⟩
    exact (hR hp).2

/-- after Mizar RELSET_1:18 — the domain restriction `R|X1`, read as
`{p | p ∈ R ∧ p.1 ∈ X1}`, is a relation of X1, Y.
Mizar: `R|X1 is Relation of X1,Y`. -/
theorem relset_1_18 {α β : Type*} {X : Set α} {Y : Set β} {R : Set (α × β)}
    {X1 : Set α} (hR : R ⊆ X ×ˢ Y) :
    {p | p ∈ R ∧ p.1 ∈ X1} ⊆ X1 ×ˢ Y := by
  rintro ⟨x, y⟩ ⟨hp, hx1⟩
  exact ⟨hx1, (hR hp).2⟩

/-- after Mizar RELSET_1:19 — restricting a relation of X, Y to a
larger domain set X1 changes nothing.
Mizar: `X c= X1 implies R|X1 = R`. -/
theorem relset_1_19 {α β : Type*} {X X1 : Set α} {Y : Set β} {R : Set (α × β)}
    (hR : R ⊆ X ×ˢ Y) (hX : X ⊆ X1) :
    {p | p ∈ R ∧ p.1 ∈ X1} = R := by
  ext ⟨x, y⟩
  constructor
  · intro hp
    exact hp.1
  · intro hp
    exact ⟨hp, hX (hR hp).1⟩

/-- after Mizar RELSET_1:20 — the codomain restriction `Y1|`R`, read
as `{p | p ∈ R ∧ p.2 ∈ Y1}`, is a relation of X, Y1.
Mizar: `Y1|`R is Relation of X,Y1`. -/
theorem relset_1_20 {α β : Type*} {X : Set α} {Y : Set β} {R : Set (α × β)}
    {Y1 : Set β} (hR : R ⊆ X ×ˢ Y) :
    {p | p ∈ R ∧ p.2 ∈ Y1} ⊆ X ×ˢ Y1 := by
  rintro ⟨x, y⟩ ⟨hp, hy1⟩
  exact ⟨(hR hp).1, hy1⟩

/-- after Mizar RELSET_1:21 — restricting a relation of X, Y to a
larger codomain set Y1 changes nothing.
Mizar: `Y c= Y1 implies Y1|`R = R`. -/
theorem relset_1_21 {α β : Type*} {X : Set α} {Y Y1 : Set β} {R : Set (α × β)}
    (hR : R ⊆ X ×ˢ Y) (hY : Y ⊆ Y1) :
    {p | p ∈ R ∧ p.2 ∈ Y1} = R := by
  ext ⟨x, y⟩
  constructor
  · intro hp
    exact hp.1
  · intro hp
    exact ⟨hp, hY (hR hp).2⟩

/-- after Mizar FINSET_1:1 — a subset of a finite set is finite.
Finset idiom: the finite set is a `Finset α`, and finiteness of the
subset is `Set.Finite`. (twin: `Set.Finite.subset` applied to
`Finset.finite_toSet`)
Mizar: `A c= B & B is finite implies A is finite`. -/
theorem finset_1_1 {α : Type*} {A : Set α} {B : Finset α}
    (hA : A ⊆ ↑B) : A.Finite :=
  (Finset.finite_toSet B).subset hA

end ThetLogos.MizarPilot1.B4
