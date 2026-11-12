import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Prod
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Basic

/-!
# Mizar Pilot Tranche 2 — Brick B4 (RELSET_1, FINSET_1)

Programme credit: Mizar working list, MZ-W1-P2, MZ pilot tranche 2, brick B4.

**NO CLAIM; dials 0/4.**

Protocol: one theorem per Mizar item, restated in the idiom below;
priority for the underlying results belongs to the Mizar authors
(RELSET_1 / FINSET_1). This file is a restatement draft only
(write-only lane; no build run here — the coordinator builds).

Restatement idiom (recorded for this brick; extends the tranche-1
brick B4 idiom):
* A Mizar relation on sets is a set of ordered pairs:
  `R : Set (α × β)`.
* "`R` is Relation of `X, Y`" is read as `R ⊆ X ×ˢ Y`
  (`Set.prod`), with `X : Set α`, `Y : Set β`.
* `dom R` is read as `Prod.fst '' R`; `rng R` as `Prod.snd '' R`.
* `R.:X` (image of a set under `R`) is read as
  `{y | ∃ x ∈ X, (x, y) ∈ R}`; `R"Y` (preimage) is read as
  `{x | ∃ y ∈ Y, (x, y) ∈ R}`. Iterated image/preimage
  (RELSET_1:23) is spelled with the inner membership unfolded to
  its `∃` form.
* `P * R` (relational composition) is read as
  `{q | ∃ y, (q.1, y) ∈ P ∧ (y, q.2) ∈ R}`.
* `Im(R, i)` is read as `{y | (i, y) ∈ R}` (the image of the
  singleton `{i}`).
* Domain restriction `P|A` is read as `{p | p ∈ P ∧ p.1 ∈ A}`
  (as in tranche 1); "`A` misses `X`" is read as `A ∩ X = ∅`.
* Where Mizar works in the ambient context "`R` is a Relation of
  `X, Y`", that context is made explicit as a hypothesis
  `hR : R ⊆ X ×ˢ Y`.
* FINSET_1: "is finite" for a `Set α` is `Set.Finite`. A Mizar
  Function `f` is read as a Lean function `α → β` where the
  statement is about images (FINSET_1:5), and as a functional
  relation `f : Set (α × β)` with hypothesis
  `∀ x y₁ y₂, (x, y₁) ∈ f → (x, y₂) ∈ f → y₁ = y₂` where the
  statement turns on partiality and `dom`/`rng` (FINSET_1:8, 9, 10).
  `union A` is `⋃₀ A`; "`F` is `c=`-linear" is
  `∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A`.
* FINSET_1:15 is STUCK in place (see its comment): untyped set
  membership has no typed counterpart in this idiom.
-/

namespace ThetLogos.MizarPilot2.B4

/-- after Mizar RELSET_1:22 — imaging a relation over its whole
first set gives its range, and taking the preimage over its whole
second set gives its domain (in the ambient context that `R` is a
relation of `X, Y`).
Mizar: `R.:X = rng R & R"Y = dom R`. -/
theorem relset_1_22 {α β : Type*} {X : Set α} {Y : Set β} {R : Set (α × β)}
    (hR : R ⊆ X ×ˢ Y) :
    {y | ∃ x ∈ X, (x, y) ∈ R} = Prod.snd '' R ∧
    {x | ∃ y ∈ Y, (x, y) ∈ R} = Prod.fst '' R := by
  constructor
  · ext y
    constructor
    · rintro ⟨x, hxX, hxy⟩
      exact ⟨(x, y), hxy, rfl⟩
    · rintro ⟨⟨x, y'⟩, hxy, rfl⟩
      exact ⟨x, (hR hxy).1, hxy⟩
  · ext x
    constructor
    · rintro ⟨y, hyY, hxy⟩
      exact ⟨(x, y), hxy, rfl⟩
    · rintro ⟨⟨x', y⟩, hxy, rfl⟩
      exact ⟨y, (hR hxy).2, hxy⟩

/-- after Mizar RELSET_1:23 — imaging over the preimage of the whole
second set gives the range, and taking the preimage over the image
of the whole first set gives the domain (in the ambient context that
`R` is a relation of `X, Y`).
Mizar: `R.:(R"Y) = rng R & R"(R.:X) = dom R`. -/
theorem relset_1_23 {α β : Type*} {X : Set α} {Y : Set β} {R : Set (α × β)}
    (hR : R ⊆ X ×ˢ Y) :
    {y | ∃ x, (∃ y' ∈ Y, (x, y') ∈ R) ∧ (x, y) ∈ R} = Prod.snd '' R ∧
    {x | ∃ y, (∃ x' ∈ X, (x', y) ∈ R) ∧ (x, y) ∈ R} = Prod.fst '' R := by
  constructor
  · ext y
    constructor
    · rintro ⟨x, ⟨y', hy'Y, hx⟩, hxy⟩
      exact ⟨(x, y), hxy, rfl⟩
    · rintro ⟨⟨x, y'⟩, hxy, rfl⟩
      exact ⟨x, ⟨y', (hR hxy).2, hxy⟩, hxy⟩
  · ext x
    constructor
    · rintro ⟨y, ⟨x', hx'X, hy⟩, hxy⟩
      exact ⟨(x, y), hxy, rfl⟩
    · rintro ⟨⟨x', y⟩, hxy, rfl⟩
      exact ⟨y, ⟨x', (hR hxy).1, hxy⟩, hxy⟩

/-- after Mizar RELSET_1:24 — an element `x` of `D` is in the domain
of `R` iff some element of `E` pairs with it in `R` (in the ambient
context that `R` is a relation of `D, E`; the hypothesis `hx` records
the Mizar typing "`x` being Element of `D`" and is not needed by the
proof).
Mizar: `for x being Element of D holds x in dom R iff ex y being
Element of E st [x,y] in R`. -/
theorem relset_1_24 {α β : Type*} {D : Set α} {E : Set β} {R : Set (α × β)}
    (hR : R ⊆ D ×ˢ E) (x : α) (hx : x ∈ D) :
    x ∈ Prod.fst '' R ↔ ∃ y ∈ E, (x, y) ∈ R := by
  constructor
  · rintro ⟨⟨x', y⟩, hxy, hx'⟩
    have hxx : x' = x := hx'
    subst hxx
    exact ⟨y, (hR hxy).2, hxy⟩
  · rintro ⟨y, -, hxy⟩
    exact ⟨(x, y), hxy, rfl⟩

/-- after Mizar RELSET_1:25 — `y` is in the range of `R` iff some
element of `D` pairs with it in `R` (in the ambient context that `R`
is a relation of `D, E`).
Mizar: `for y being object holds y in rng R iff ex x being Element
of D st [x,y] in R`. -/
theorem relset_1_25 {α β : Type*} {D : Set α} {E : Set β} {R : Set (α × β)}
    (hR : R ⊆ D ×ˢ E) (y : β) :
    y ∈ Prod.snd '' R ↔ ∃ x ∈ D, (x, y) ∈ R := by
  constructor
  · rintro ⟨⟨x, y'⟩, hxy, hy'⟩
    have hyy : y' = y := hy'
    subst hyy
    exact ⟨x, (hR hxy).1, hxy⟩
  · rintro ⟨x, -, hxy⟩
    exact ⟨(x, y), hxy, rfl⟩

/-- after Mizar RELSET_1:26 — if the domain of `R` is nonempty, some
element of `E` is in its range (in the ambient context that `R` is a
relation of `D, E`).
Mizar: `dom R <> {} implies ex y being Element of E st y in rng R`. -/
theorem relset_1_26 {α β : Type*} {D : Set α} {E : Set β} {R : Set (α × β)}
    (hR : R ⊆ D ×ˢ E) (h : Prod.fst '' R ≠ ∅) :
    ∃ y ∈ E, y ∈ Prod.snd '' R := by
  obtain ⟨x, hx⟩ : ∃ x, x ∈ Prod.fst '' R :=
    Classical.byContradiction (fun hc =>
      h (Set.eq_empty_of_forall_notMem (fun x hx => hc ⟨x, hx⟩)))
  obtain ⟨⟨x', y⟩, hp, hx'⟩ := hx
  exact ⟨y, (hR hp).2, ⟨(x', y), hp, rfl⟩⟩

/-- after Mizar RELSET_1:27 — if the range of `R` is nonempty, some
element of `D` is in its domain (in the ambient context that `R` is a
relation of `D, E`).
Mizar: `rng R <> {} implies ex x being Element of D st x in dom R`. -/
theorem relset_1_27 {α β : Type*} {D : Set α} {E : Set β} {R : Set (α × β)}
    (hR : R ⊆ D ×ˢ E) (h : Prod.snd '' R ≠ ∅) :
    ∃ x ∈ D, x ∈ Prod.fst '' R := by
  obtain ⟨y, hy⟩ : ∃ y, y ∈ Prod.snd '' R :=
    Classical.byContradiction (fun hc =>
      h (Set.eq_empty_of_forall_notMem (fun y hy => hc ⟨y, hy⟩)))
  obtain ⟨⟨x, y'⟩, hp, hy'⟩ := hy
  exact ⟨x, (hR hp).1, ⟨(x, y'), hp, rfl⟩⟩

/-- after Mizar RELSET_1:28 — membership in the composite `P * R`
is existence of a middle element of `E` (in the ambient context
that `P` is a relation of `D, E`; the codomain bound of `R` is not
needed for this characterization, so no hypothesis on `R` is taken).
Mizar: `for P being Relation of D,E, R being Relation of E,F for
x, z being object holds [x,z] in P*R iff ex y being Element of E st
[x,y] in P & [y,z] in R`. -/
theorem relset_1_28 {α β γ : Type*} {D : Set α} {E : Set β}
    {P : Set (α × β)} {R : Set (β × γ)} (hP : P ⊆ D ×ˢ E) (x : α) (z : γ) :
    (x, z) ∈ {q : α × γ | ∃ y, (q.1, y) ∈ P ∧ (y, q.2) ∈ R} ↔
    ∃ y ∈ E, (x, y) ∈ P ∧ (y, z) ∈ R := by
  constructor
  · rintro ⟨y, h1, h2⟩
    exact ⟨y, (hP h1).2, h1, h2⟩
  · rintro ⟨y, -, h1, h2⟩
    exact ⟨y, h1, h2⟩

/-- after Mizar RELSET_1:29 — `y` is in the image of `D1` under `R`
iff some element of `D` in `D1` pairs with it in `R` (with `D1`
a subset of `D`).
Mizar: `y in R.:D1 iff ex x being Element of D st [x,y] in R &
x in D1`. -/
theorem relset_1_29 {α β : Type*} {D : Set α} {R : Set (α × β)} {D1 : Set α}
    (hD1 : D1 ⊆ D) (y : β) :
    y ∈ {y | ∃ x ∈ D1, (x, y) ∈ R} ↔ ∃ x ∈ D, (x, y) ∈ R ∧ x ∈ D1 := by
  constructor
  · rintro ⟨x, hx1, hxy⟩
    exact ⟨x, hD1 hx1, hxy, hx1⟩
  · rintro ⟨x, hxD, hxy, hx1⟩
    exact ⟨x, hx1, hxy⟩

/-- after Mizar RELSET_1:30 — `x` is in the preimage of `D2` under
`R` iff some element of `E` in `D2` pairs with it in `R` (with `D2`
a subset of `E`).
Mizar: `x in R"D2 iff ex y being Element of E st [x,y] in R &
y in D2`. -/
theorem relset_1_30 {α β : Type*} {E : Set β} {R : Set (α × β)} {D2 : Set β}
    (hD2 : D2 ⊆ E) (x : α) :
    x ∈ {x | ∃ y ∈ D2, (x, y) ∈ R} ↔ ∃ y ∈ E, (x, y) ∈ R ∧ y ∈ D2 := by
  constructor
  · rintro ⟨y, hy2, hxy⟩
    exact ⟨y, hD2 hy2, hxy, hy2⟩
  · rintro ⟨y, hyE, hxy, hy2⟩
    exact ⟨y, hy2, hxy⟩

/-- after Mizar RELSET_1:31 — two relations of `N` that agree on the
image of every element of `N` are equal, where `Im(R, i)` is read as
`{y | (i, y) ∈ R}`.
Mizar: `for N being set, R,S being Relation of N st for i being set
st i in N holds Im(R,i) = Im(S,i) holds R = S`. -/
theorem relset_1_31 {α : Type*} {N : Set α} {R S : Set (α × α)}
    (hR : R ⊆ N ×ˢ N) (hS : S ⊆ N ×ˢ N)
    (h : ∀ i ∈ N, {y | (i, y) ∈ R} = {y | (i, y) ∈ S}) :
    R = S := by
  ext ⟨x, y⟩
  constructor
  · intro hxy
    have hxN : x ∈ N := (hR hxy).1
    have hy : y ∈ {y | (x, y) ∈ R} := hxy
    rw [h x hxN] at hy
    exact hy
  · intro hxy
    have hxN : x ∈ N := (hS hxy).1
    have hy : y ∈ {y | (x, y) ∈ S} := hxy
    rw [← h x hxN] at hy
    exact hy

/-- after Mizar RELSET_1:32 — restricting `P` to a set `A` disjoint
from the first set `X` gives the empty relation (in the ambient
context that `P` is a relation of `X, Y`; "`A` misses `X`" is read
as `A ∩ X = ∅`).
Mizar: `A misses X implies P|A = {}`. -/
theorem relset_1_32 {α β : Type*} {X : Set α} {Y : Set β} {P : Set (α × β)}
    {A : Set α} (hP : P ⊆ X ×ˢ Y) (hAX : A ∩ X = ∅) :
    {p | p ∈ P ∧ p.1 ∈ A} = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro ⟨x, y⟩ ⟨hp, hxA⟩
  have hxX : x ∈ X := (hP hp).1
  have hmem : x ∈ A ∩ X := ⟨hxA, hxX⟩
  rw [hAX] at hmem
  exact Set.notMem_empty x hmem

/-- after Mizar FINSET_1:2 — the union of two finite sets is finite.
(twin: `Set.Finite.union`)
Mizar: `A is finite & B is finite implies A \/ B is finite`. -/
theorem finset_1_2 {α : Type*} {A B : Set α} (hA : A.Finite) (hB : B.Finite) :
    (A ∪ B).Finite :=
  hA.union hB

/-- after Mizar FINSET_1:3 — the intersection of a finite set with
any set is finite.
Mizar: `A is finite implies A /\ B is finite`. -/
theorem finset_1_3 {α : Type*} {A B : Set α} (hA : A.Finite) :
    (A ∩ B).Finite :=
  hA.subset Set.inter_subset_left

/-- after Mizar FINSET_1:4 — the difference of a finite set and any
set is finite.
Mizar: `A is finite implies A \ B is finite`. -/
theorem finset_1_4 {α : Type*} {A B : Set α} (hA : A.Finite) :
    (A \ B).Finite :=
  hA.subset Set.diff_subset

/-- after Mizar FINSET_1:5 — the image of a finite set under a
function is finite. The Mizar Function `f` is read here as a Lean
function `α → β`, and `f.:A` as `f '' A`.
(twin: `Set.Finite.image`)
Mizar: `A is finite implies f.:A is finite`. -/
theorem finset_1_5 {α β : Type*} {A : Set α} {f : α → β} (hA : A.Finite) :
    (f '' A).Finite :=
  hA.image f

/-- after Mizar FINSET_1:6 — a nonempty family of subsets of a finite
set has a `⊆`-minimal member. (GUESSED-NAME: `Set.Finite.powerset`,
`Set.Finite.exists_minimal`, `Set.nonempty_iff_ne_empty` — lemma
names and the `𝒫 A` membership step to verify at build.)
Mizar: `A is finite implies for X being Subset-Family of A st
X <> {} ex x being set st x in X & for B being set st B in X holds
x c= B implies B = x`. -/
theorem finset_1_6 {α : Type*} {A : Set α} (hA : A.Finite)
    {X : Set (Set α)} (hX : ∀ B ∈ X, B ⊆ A) (hne : X ≠ ∅) :
    ∃ x ∈ X, ∀ B ∈ X, x ⊆ B → B = x := by
  have hXfin : X.Finite :=
    Set.Finite.subset (Set.Finite.powerset hA) (fun B hB => hX B hB)
  have hne' : X.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨x, hxX, hmax⟩ := hXfin.exists_maximal hne'
  exact ⟨x, hxX, fun B hB hxB => Set.Subset.antisymm (hmax hB hxB) hxB⟩

/-- after Mizar FINSET_1:7 — a family of sets has finite union iff
the family itself is finite and each of its members is finite.
(GUESSED-NAME: `Set.Finite.sUnion`, `Set.subset_sUnion_of_mem`,
`Set.Finite.powerset` — lemma names to verify at build.)
Mizar: `A is finite & (for X st X in A holds X is finite) iff
union A is finite`. -/
theorem finset_1_7 {α : Type*} {A : Set (Set α)} :
    (A.Finite ∧ ∀ X ∈ A, X.Finite) ↔ (⋃₀ A).Finite := by
  constructor
  · rintro ⟨hA, hX⟩
    exact Set.Finite.sUnion hA hX
  · intro h
    have hsub : ∀ X ∈ A, X ⊆ ⋃₀ A := fun X hX => Set.subset_sUnion_of_mem hX
    have hXfin : ∀ X ∈ A, X.Finite := fun X hX => Set.Finite.subset h (hsub X hX)
    have hAfin : A.Finite :=
      Set.Finite.subset (Set.Finite.powerset h) (fun X hX => hsub X hX)
    exact ⟨hAfin, hXfin⟩

/-- after Mizar FINSET_1:8 — the range of a (functional) function
is finite when its domain is finite. The Mizar Function `f` is read
as a functional relation, and the graph function on the domain
subtype (chosen with `Classical.choose`) witnesses the range as a
finite image. (GUESSED-NAME: `Set.Finite.fintype`,
`Set.finite_range` — lemma names to verify at build.)
Mizar: `dom f is finite implies rng f is finite`. -/
theorem finset_1_8 {α β : Type*} {f : Set (α × β)}
    (hfun : ∀ x y₁ y₂, (x, y₁) ∈ f → (x, y₂) ∈ f → y₁ = y₂)
    (hdom : (Prod.fst '' f).Finite) :
    (Prod.snd '' f).Finite := by
  have hex : ∀ x : ↥(Prod.fst '' f), ∃ y, (x.1, y) ∈ f := by
    intro x
    obtain ⟨⟨a, b⟩, hp, hpx⟩ := x.2
    have hax : a = x.1 := hpx
    subst hax
    exact ⟨b, hp⟩
  let g : ↥(Prod.fst '' f) → β := fun x => Classical.choose (hex x)
  have hg : ∀ x, (x.1, g x) ∈ f := fun x => Classical.choose_spec (hex x)
  have hsub : Prod.snd '' f ⊆ Set.range g := by
    rintro y ⟨⟨a, b⟩, hab, hb⟩
    have hb' : b = y := hb
    have ha : a ∈ Prod.fst '' f := ⟨(a, b), hab, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    exact (hfun a _ b (hg ⟨a, ha⟩) hab).trans hb'
  haveI : Fintype ↥(Prod.fst '' f) := hdom.fintype
  exact Set.Finite.subset (Set.toFinite (Set.range g)) hsub

/-- after Mizar FINSET_1:9 — a subset `Y` of the range of a
(functional) function is finite when its preimage is finite: every
`y ∈ Y` is the graph-function value of a point of the preimage.
The Mizar Function `f` is read as a functional relation.
(GUESSED-NAME: `Set.Finite.fintype`, `Set.finite_range` — lemma
names to verify at build.)
Mizar: `Y c= rng f & f"Y is finite implies Y is finite`. -/
theorem finset_1_9 {α β : Type*} {f : Set (α × β)} {Y : Set β}
    (hfun : ∀ x y₁ y₂, (x, y₁) ∈ f → (x, y₂) ∈ f → y₁ = y₂)
    (hY : Y ⊆ Prod.snd '' f)
    (hpre : {x | ∃ y ∈ Y, (x, y) ∈ f}.Finite) :
    Y.Finite := by
  have hex : ∀ x : ↥{x | ∃ y ∈ Y, (x, y) ∈ f}, ∃ y, (x.1, y) ∈ f := by
    intro x
    obtain ⟨y, -, hy⟩ := x.2
    exact ⟨y, hy⟩
  let g : ↥{x | ∃ y ∈ Y, (x, y) ∈ f} → β := fun x => Classical.choose (hex x)
  have hg : ∀ x, (x.1, g x) ∈ f := fun x => Classical.choose_spec (hex x)
  have hsub : Y ⊆ Set.range g := by
    intro y hy
    obtain ⟨⟨a, b⟩, hab, hb⟩ := hY hy
    have hb' : b = y := hb
    have hbY : b ∈ Y := by
      rw [← hb'] at hy
      exact hy
    have ha : a ∈ {x | ∃ y ∈ Y, (x, y) ∈ f} := ⟨b, hbY, hab⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    exact (hfun a _ b (hg ⟨a, ha⟩) hab).trans hb'
  haveI : Fintype ↥{x | ∃ y ∈ Y, (x, y) ∈ f} := hpre.fintype
  exact Set.Finite.subset (Set.toFinite (Set.range g)) hsub

/-- after Mizar FINSET_1:10 — the domain of a (functional) function
is finite iff the function, as a set of pairs, is finite. Forward:
the function is the range of its graph function on the domain
subtype. Reverse: the domain is the image of the function under
`Prod.fst`. (GUESSED-NAME: `Set.Finite.fintype`,
`Set.finite_range`, `Set.Finite.image` — lemma names to verify at
build.)
Mizar: `for f being Function holds dom f is finite iff f is finite`. -/
theorem finset_1_10 {α β : Type*} {f : Set (α × β)}
    (hfun : ∀ x y₁ y₂, (x, y₁) ∈ f → (x, y₂) ∈ f → y₁ = y₂) :
    (Prod.fst '' f).Finite ↔ f.Finite := by
  constructor
  · intro hdom
    have hex : ∀ x : ↥(Prod.fst '' f), ∃ y, (x.1, y) ∈ f := by
      intro x
      obtain ⟨⟨a, b⟩, hp, hpx⟩ := x.2
      have hax : a = x.1 := hpx
      subst hax
      exact ⟨b, hp⟩
    let g : ↥(Prod.fst '' f) → β := fun x => Classical.choose (hex x)
    have hg : ∀ x, (x.1, g x) ∈ f := fun x => Classical.choose_spec (hex x)
    have hsub : f ⊆ Set.range (fun x : ↥(Prod.fst '' f) => (x.1, g x)) := by
      rintro ⟨a, b⟩ hab
      have ha : a ∈ Prod.fst '' f := ⟨(a, b), hab, rfl⟩
      refine ⟨⟨a, ha⟩, ?_⟩
      show (a, g ⟨a, ha⟩) = (a, b)
      have hgb : g ⟨a, ha⟩ = b := hfun a _ b (hg ⟨a, ha⟩) hab
      rw [hgb]
    haveI : Fintype ↥(Prod.fst '' f) := hdom.fintype
    exact Set.Finite.subset (Set.toFinite (Set.range (fun x : ↥(Prod.fst '' f) => (x.1, g x)))) hsub
  · intro hf
    exact hf.image Prod.fst

/-- after Mizar FINSET_1:11 — a nonempty finite `⊆`-linear family
of sets has a least member: take a minimal member (it exists by
finiteness) and linearity upgrades minimal to least.
(GUESSED-NAME: `Set.Finite.exists_minimal`,
`Set.nonempty_iff_ne_empty` — lemma names to verify at build.)
Mizar: `for F being set st F is finite & F <> {} & F is c=-linear
ex m being set st m in F & for C being set st C in F holds m c= C`. -/
theorem finset_1_11 {α : Type*} {F : Set (Set α)}
    (hF : F.Finite) (hne : F ≠ ∅)
    (hlin : ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A) :
    ∃ m ∈ F, ∀ C ∈ F, m ⊆ C := by
  have hne' : F.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨m, hmF, hmin⟩ := hF.exists_minimal hne'
  refine ⟨m, hmF, fun C hC => ?_⟩
  rcases hlin m hmF C hC with h | h
  · exact h
  · exact hmin hC h

/-- after Mizar FINSET_1:12 — a nonempty finite `⊆`-linear family
of sets has a greatest member: take a maximal member (it exists by
finiteness) and linearity upgrades maximal to greatest.
(GUESSED-NAME: `Set.Finite.exists_maximal`,
`Set.nonempty_iff_ne_empty` — lemma names to verify at build.)
Mizar: `for F being set st F is finite & F <> {} & F is c=-linear
ex m being set st m in F & for C being set st C in F holds C c= m`. -/
theorem finset_1_12 {α : Type*} {F : Set (Set α)}
    (hF : F.Finite) (hne : F ≠ ∅)
    (hlin : ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A) :
    ∃ m ∈ F, ∀ C ∈ F, C ⊆ m := by
  have hne' : F.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨m, hmF, hmax⟩ := hF.exists_maximal hne'
  refine ⟨m, hmF, fun C hC => ?_⟩
  rcases hlin m hmF C hC with h | h
  · exact hmax hC h
  · exact h

/-- after Mizar FINSET_1:14 — a finite set of pairs inside `[:Y,Z:]`
is already inside `[:A,Z:]` for the finite first projection
`A = Prod.fst '' X`, which lies in `Y`.
(twin: `Set.Finite.image`)
Mizar: `X is finite & X c= [:Y,Z:] implies ex A being set st
A is finite & A c= Y & X c= [:A,Z:]`. -/
theorem finset_1_14 {α β : Type*} {X : Set (α × β)} {Y : Set α} {Z : Set β}
    (hX : X.Finite) (hsub : X ⊆ Y ×ˢ Z) :
    ∃ A : Set α, A.Finite ∧ A ⊆ Y ∧ X ⊆ A ×ˢ Z := by
  refine ⟨Prod.fst '' X, hX.image Prod.fst, ?_, ?_⟩
  · rintro x ⟨p, hp, rfl⟩
    exact (hsub hp).1
  · rintro ⟨x, y⟩ hp
    exact ⟨⟨(x, y), hp, rfl⟩, (hsub hp).2⟩

/- after Mizar FINSET_1:15 — STUCK (no theorem stated).
Mizar: `B is infinite implies not B in [:A,B:]`.
The Mizar statement is untyped set membership: the set `B` itself
is claimed not to be an element of the product set `[:A,B:]`. In
this brick's typed idiom `B : Set β` and `[:A,B:] : Set (α × β)`,
so `B ∈ A ×ˢ B` does not typecheck — there is no typed counterpart
of a set being an element of a product of sets, and the Mizar
truth of the statement turns on the Kuratowski-pair / foundation
content of untyped set theory, which the idiom does not carry. No
repair attempted; the item is left STUCK in place. -/
-- STUCK: FINSET_1:15 — see the doc comment above; no theorem stated.

end ThetLogos.MizarPilot2.B4
