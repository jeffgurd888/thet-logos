import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Prod
import Mathlib.Data.Prod.Basic

/-!
# Mizar Pilot Tranche 1 — Brick B3 (SUBSET_1 remainder ×10 + ZFMISC_1 ×30)

Programme credit: Mizar working list, MZ pilot tranche 1 brick B3; Zero's
2026-11-09 pilot call.

**NO CLAIM; dials 0/4.**

Protocol: one theorem per Mizar item, restated in the house idiom below;
priority for the underlying results belongs to the Mizar library
(SUBSET_1 / ZFMISC_1) — these are re-proofs in our environment, disclosed
as twins where a Mathlib lemma already carries the content.

Restatement idiom:
- Mizar sets / subsets of a set `E` → `Set α`; `c=` → `⊆`; `\/` → `∪`;
  `/\` → `∩`; `\` → `\`; `{x}`, `{x, y}` → Set insert notation.
- Mizar `A misses B` → `Disjoint A B`.
- Mizar complement `A\`` (complement w.r.t. `E`) → Lean `Aᶜ` (w.r.t. `univ`),
  EXCEPT SUBSET_1:30, whose hypothesis constrains only elements of `E`, so
  the univ-complement flattening would be unsound there; :30 is restated
  with the honest E-relative complement `E \ B`.
- Mizar's typed `A` being a Subset of `E` (i.e. `A ⊆ E` by typing) is
  flattened to an explicit hypothesis where the argument uses it
  (SUBSET_1:27, :28, :30).
- Mizar `bool X` (powerset) → `Set.powerset X`; Mizar `union X` → `Set.sUnion X`.
- Mizar `[:A, B:]` (Cartesian product of sets) → `A ×ˢ B` (`Set.prod`);
  ordered pair `[x, y]` → `(x, y)`.
- Mizar `\+/` (symmetric difference, ZFMISC_1:23) is restated by its
  definition `(A \ B) ∪ (B \ A)`, since `Set.symmDiff` sits outside the
  narrowed import set of this brick.
- SUBSET_1:29 is STUCK: as extracted ("`x ∉ B` implies `x ∈ B`") it is
  false under the literal reading; a negation/complement was very likely
  dropped in extraction. It is commented out in place below.
-/

namespace ThetLogos.MizarPilot1.B3

variable {α : Type*}

/-- after Mizar SUBSET_1:21 — the complement of a union is contained in the
complement of either factor. (twin: `Set.compl_subset_compl.mpr Set.subset_union_left`) -/
theorem subset_1_21 (A B : Set α) : (A ∪ B)ᶜ ⊆ Aᶜ := by
  intro x hx hxA
  exact hx (Or.inl hxA)

/-- after Mizar SUBSET_1:22 — the complement of a set is contained in the
complement of any intersection it participates in. (twin: `Set.compl_subset_compl.mpr Set.inter_subset_left`) -/
theorem subset_1_22 (A B : Set α) : Aᶜ ⊆ (A ∩ B)ᶜ := by
  intro x hx hxAB
  exact hx hxAB.1

/-- after Mizar SUBSET_1:23 — `A` misses `B` iff `A` is contained in the
complement of `B`. (twin: `Set.subset_compl_iff_disjoint_left`) -/
theorem subset_1_23 (A B : Set α) : Disjoint A B ↔ A ⊆ Bᶜ := by
  constructor
  · intro h x hx
    exact Set.disjoint_left.mp h hx
  · intro h
    rw [Set.disjoint_left]
    intro x hx hxB
    exact h hx hxB

/-- after Mizar SUBSET_1:24 — `A` misses the complement of `B` iff `A` is
contained in `B`. (twin: `Set.disjoint_compl_right_iff_subset`) -/
theorem subset_1_24 (A B : Set α) : Disjoint A Bᶜ ↔ A ⊆ B := by
  constructor
  · intro h x hx
    by_contra hxB
    exact Set.disjoint_left.mp h hx hxB
  · intro h
    rw [Set.disjoint_left]
    intro x hx hxBc
    exact hxBc (h hx)

/-- after Mizar SUBSET_1:25 — if `A` misses both `B` and the complement
pairing `Aᶜ` misses `Bᶜ`, then `A` is the complement of `B`. -/
theorem subset_1_25 (A B : Set α) (h : Disjoint A B ∧ Disjoint Aᶜ Bᶜ) :
    A = Bᶜ := by
  apply Set.Subset.antisymm
  · intro x hx
    exact Set.disjoint_left.mp h.1 hx
  · intro x hx
    by_contra hxA
    exact Set.disjoint_left.mp h.2 hxA hx

/-- after Mizar SUBSET_1:26 — a subset of `B` is contained in the complement
of anything that misses `B`. -/
theorem subset_1_26 (A B C : Set α) (h : A ⊆ B ∧ Disjoint C B) : A ⊆ Cᶜ := by
  intro x hx hxC
  exact Set.disjoint_left.mp h.2 hxC (h.1 hx)

/-- after Mizar SUBSET_1:27 — if every element of `E` lies in `B`, then any
subset of `E` is contained in `B`. (Mizar's typing `A` a Subset of `E`
flattened to the hypothesis `hAE`.) -/
theorem subset_1_27 (A B E : Set α) (hAE : A ⊆ E) (h : ∀ a ∈ E, a ∈ B) :
    A ⊆ B :=
  fun x hx => h x (hAE hx)

/-- after Mizar SUBSET_1:28 — if every element of `E` lies in `A`, then
`E = A`. (Mizar's typing flattened to `hAE` as in :27.) -/
theorem subset_1_28 (A E : Set α) (hAE : A ⊆ E) (h : ∀ x ∈ E, x ∈ A) :
    E = A :=
  Set.Subset.antisymm (fun x hx => h x hx) hAE

-- STUCK SUBSET_1:29: statement as extracted ("E ≠ ∅ implies for B, for
-- x ∈ E with x ∉ B, x ∈ B") is false under the literal reading — from
-- x ∉ B nothing gives x ∈ B. A negation or complement (likely the
-- conclusion was x ∈ Bᶜ, or the hypothesis x ∈ Bᶜ) was dropped in
-- extraction; not restated on a guess.
-- theorem subset_1_29 (B E : Set α) (hE : E ≠ ∅) (x : α) (hxE : x ∈ E)
--     (hxB : x ∉ B) : x ∈ B := ...

/-- after Mizar SUBSET_1:30 — if membership in `A` is, over `E`, exactly
non-membership in `B`, then `A` is the E-relative complement of `B`
(restated as `E \ B`; see the header for why the univ-complement
flattening is not used here). -/
theorem subset_1_30 (A B E : Set α) (hAE : A ⊆ E) (hBE : B ⊆ E)
    (h : ∀ x ∈ E, x ∈ A ↔ x ∉ B) : A = E \ B := by
  ext x
  by_cases hxE : x ∈ E
  · have hx := h x hxE
    constructor
    · intro hxa
      exact ⟨hxE, hx.mp hxa⟩
    · intro hxEB
      exact hx.mpr hxEB.2
  · have hxA : x ∉ A := fun hxa => hxE (hAE hxa)
    have hxEB : x ∉ E \ B := fun hxEB => hxE hxEB.1
    exact iff_of_false hxA hxEB

/-- after Mizar ZFMISC_1:1 — the powerset of the empty set is the singleton
of the empty set. (twin: `Set.powerset_empty`) -/
theorem zfmisc_1_1 : Set.powerset (∅ : Set α) = {∅} := by
  ext s
  simp only [Set.mem_powerset_iff, Set.subset_empty_iff, Set.mem_singleton_iff]

/-- after Mizar ZFMISC_1:2 — the union of the empty family is empty.
(twin: `Set.sUnion_empty`) -/
theorem zfmisc_1_2 : Set.sUnion (∅ : Set (Set α)) = ∅ :=
  Set.sUnion_empty

/-- after Mizar ZFMISC_1:3 — a singleton contained in a singleton forces
equality of the points. (twin: `Set.singleton_subset_singleton_iff`) -/
theorem zfmisc_1_3 (x y : α) (h : ({x} : Set α) ⊆ {y}) : x = y :=
  Set.mem_singleton_iff.mp (h (Set.mem_singleton x))

/-- after Mizar ZFMISC_1:4 — if a singleton equals a pair, its point is the
first entry of the pair. -/
theorem zfmisc_1_4 (x y1 y2 : α) (h : ({x} : Set α) = {y1, y2}) : x = y1 := by
  have hy1 : y1 ∈ ({x} : Set α) := by
    rw [h]
    exact Set.mem_insert y1 {y2}
  exact (Set.mem_singleton_iff.mp hy1).symm

/-- after Mizar ZFMISC_1:5 — if a singleton equals a pair, the pair's two
entries agree. -/
theorem zfmisc_1_5 (x y1 y2 : α) (h : ({x} : Set α) = {y1, y2}) : y1 = y2 := by
  have hy1 : y1 ∈ ({x} : Set α) := by
    rw [h]
    exact Set.mem_insert y1 {y2}
  have hy2 : y2 ∈ ({x} : Set α) := by
    rw [h]
    exact Set.mem_insert_of_mem y1 (Set.mem_singleton y2)
  rw [Set.mem_singleton_iff] at hy1 hy2
  exact hy1.trans hy2.symm

/-- after Mizar ZFMISC_1:6 — if two pairs are equal, the first entry of one
is an entry of the other. -/
theorem zfmisc_1_6 (x1 x2 y1 y2 : α) (h : ({x1, x2} : Set α) = {y1, y2}) :
    x1 = y1 ∨ x1 = y2 := by
  have hx : x1 ∈ ({y1, y2} : Set α) := by
    rw [← h]
    exact Set.mem_insert x1 {x2}
  rwa [Set.mem_insert_iff, Set.mem_singleton_iff] at hx

/-- after Mizar ZFMISC_1:7 — a singleton is contained in any pair it heads.
(twin: `Set.singleton_subset_iff.mpr (Set.mem_insert _ _)`) -/
theorem zfmisc_1_7 (x y : α) : ({x} : Set α) ⊆ {x, y} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert x {y})

/-- after Mizar ZFMISC_1:8 — if `{x} ∪ {y}` collapses to `{x}`, then
`x = y`. -/
theorem zfmisc_1_8 (x y : α) (h : ({x} : Set α) ∪ {y} = {x}) : x = y := by
  have hy : y ∈ ({x} : Set α) ∪ {y} := Or.inr (Set.mem_singleton y)
  rw [h] at hy
  exact (Set.mem_singleton_iff.mp hy).symm

/-- after Mizar ZFMISC_1:9 — adjoining a singleton already present in a pair
changes nothing. -/
theorem zfmisc_1_9 (x y : α) : ({x} : Set α) ∪ {x, y} = {x, y} := by
  ext a
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    cases h with
    | inl h => exact Or.inl h
    | inr h =>
      cases h with
      | inl h => exact Or.inl h
      | inr h => exact Or.inr h
  · intro h
    cases h with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (Or.inr h)

/-- after Mizar ZFMISC_1:10 — disjoint singletons have distinct points. -/
theorem zfmisc_1_10 (x y : α) (h : Disjoint ({x} : Set α) {y}) : x ≠ y := by
  intro hxy
  rw [hxy] at h
  exact Set.disjoint_left.mp h (Set.mem_singleton y) (Set.mem_singleton y)

/-- after Mizar ZFMISC_1:11 — distinct points give disjoint singletons.
(twin: `Set.disjoint_singleton`) -/
theorem zfmisc_1_11 (x y : α) (h : x ≠ y) : Disjoint ({x} : Set α) {y} := by
  rw [Set.disjoint_left]
  intro a ha hb
  rw [Set.mem_singleton_iff] at ha hb
  exact h (ha.symm.trans hb)

/-- after Mizar ZFMISC_1:12 — if `{x} ∩ {y}` is all of `{x}`, then `x = y`. -/
theorem zfmisc_1_12 (x y : α) (h : ({x} : Set α) ∩ {y} = {x}) : x = y := by
  have hx : x ∈ ({x} : Set α) ∩ {y} := by
    rw [h]
    exact Set.mem_singleton x
  exact Set.mem_singleton_iff.mp hx.2

/-- after Mizar ZFMISC_1:13 — intersecting a pair with one of its
singletons returns that singleton. -/
theorem zfmisc_1_13 (x y : α) : ({x} : Set α) ∩ {x, y} = {x} := by
  ext a
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, Or.inl h⟩

/-- after Mizar ZFMISC_1:14 — removing a distinct point from a singleton
leaves the singleton; the difference is the singleton iff the points
differ. -/
theorem zfmisc_1_14 (x y : α) : ({x} : Set α) \ {y} = {x} ↔ x ≠ y := by
  constructor
  · intro h hxy
    subst hxy
    rw [Set.diff_self] at h
    exact Set.singleton_ne_empty x h.symm
  · intro h
    ext a
    simp only [Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · intro ha
      exact ha.1
    · intro hax
      subst hax
      exact ⟨rfl, h⟩

/-- after Mizar ZFMISC_1:15 — if removing a point from a singleton empties
it, the points were equal. -/
theorem zfmisc_1_15 (x y : α) (h : ({x} : Set α) \ {y} = ∅) : x = y := by
  by_contra hxy
  have h14 := (zfmisc_1_14 x y).mpr hxy
  rw [h] at h14
  exact Set.singleton_ne_empty x h14.symm

/-- after Mizar ZFMISC_1:16 — removing a pair from one of its singletons
leaves nothing. -/
theorem zfmisc_1_16 (x y : α) : ({x} : Set α) \ {x, y} = ∅ := by
  ext a
  simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, iff_false]
  intro h
  exact h.2 (Or.inl h.1)

/-- after Mizar ZFMISC_1:17 — removing one point of a pair of distinct
points leaves the other singleton. -/
theorem zfmisc_1_17 (x y : α) (h : x ≠ y) : ({x, y} : Set α) \ {y} = {x} := by
  ext a
  simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro ha
    cases ha.1 with
    | inl hax => exact hax
    | inr hay => exact absurd hay ha.2
  · intro hax
    subst hax
    exact ⟨Or.inl rfl, h⟩

/-- after Mizar ZFMISC_1:18 — a singleton contained in a singleton forces
equality of the points. (Duplicate of ZFMISC_1:3 in the Mizar list;
restated as its own item.) -/
theorem zfmisc_1_18 (x y : α) (h : ({x} : Set α) ⊆ {y}) : x = y :=
  Set.mem_singleton_iff.mp (h (Set.mem_singleton x))

/-- after Mizar ZFMISC_1:19 — a singleton contained in a pair has its point
among the pair's entries. -/
theorem zfmisc_1_19 (x y z : α) (h : ({z} : Set α) ⊆ {x, y}) :
    z = x ∨ z = y := by
  have hz := h (Set.mem_singleton z)
  rwa [Set.mem_insert_iff, Set.mem_singleton_iff] at hz

/-- after Mizar ZFMISC_1:20 — a pair contained in a singleton has its first
entry equal to the singleton's point. -/
theorem zfmisc_1_20 (x y z : α) (h : ({x, y} : Set α) ⊆ {z}) : x = z :=
  Set.mem_singleton_iff.mp (h (Set.mem_insert x {y}))

/-- after Mizar ZFMISC_1:21 — a pair contained in a singleton equals that
singleton. -/
theorem zfmisc_1_21 (x y z : α) (h : ({x, y} : Set α) ⊆ {z}) :
    ({x, y} : Set α) = {z} := by
  have hx : x = z := zfmisc_1_20 x y z h
  have hy : y = z := by
    have hyz := h (Set.mem_insert_of_mem x (Set.mem_singleton y))
    exact Set.mem_singleton_iff.mp hyz
  rw [hx, hy]
  exact Set.insert_eq_of_mem (Set.mem_singleton z)

/-- after Mizar ZFMISC_1:22 — a pair contained in a pair has its first entry
among the other's entries. -/
theorem zfmisc_1_22 (x1 x2 y1 y2 : α) (h : ({x1, x2} : Set α) ⊆ {y1, y2}) :
    x1 = y1 ∨ x1 = y2 := by
  have hx := h (Set.mem_insert x1 {x2})
  rwa [Set.mem_insert_iff, Set.mem_singleton_iff] at hx

/-- after Mizar ZFMISC_1:23 — the symmetric difference of two singletons of
distinct points is the pair. (Mizar `\+/` restated by its definition;
see the header.) -/
theorem zfmisc_1_23 (x y : α) (h : x ≠ y) :
    (({x} : Set α) \ {y}) ∪ (({y} : Set α) \ {x}) = {x, y} := by
  ext a
  simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff,
    Set.mem_insert_iff]
  constructor
  · intro ha
    cases ha with
    | inl ha => exact Or.inl ha.1
    | inr ha => exact Or.inr ha.1
  · intro ha
    cases ha with
    | inl ha =>
      subst ha
      exact Or.inl ⟨rfl, h⟩
    | inr ha =>
      subst ha
      exact Or.inr ⟨rfl, h.symm⟩

/-- after Mizar ZFMISC_1:24 — the powerset of a singleton is the pair of the
empty set and the singleton. (twin: `Set.powerset_singleton`, via
`Set.subset_singleton_iff_eq`) -/
theorem zfmisc_1_24 (x : α) : Set.powerset ({x} : Set α) = {∅, {x}} := by
  ext s
  simp only [Set.mem_powerset_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact Set.subset_singleton_iff_eq

/-- after Mizar ZFMISC_1:25 — the union of a singleton family is its member.
(twin: `Set.sUnion_singleton`) -/
theorem zfmisc_1_25 (x : Set α) : Set.sUnion {x} = x :=
  Set.sUnion_singleton x

/-- after Mizar ZFMISC_1:26 — the union of two singletons is the pair of
their points. -/
theorem zfmisc_1_26 (x y : α) :
    Set.sUnion ({{x}, {y}} : Set (Set α)) = {x, y} := by
  ext a
  simp only [Set.mem_sUnion, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    cases h with
    | intro s hs =>
      cases hs.1 with
      | inl hs1 =>
        subst hs1
        exact Or.inl (Set.mem_singleton_iff.mp hs.2)
      | inr hs1 =>
        subst hs1
        exact Or.inr (Set.mem_singleton_iff.mp hs.2)
  · intro h
    cases h with
    | inl h =>
      exact ⟨{x}, Or.inl rfl, Set.mem_singleton_iff.mpr h⟩
    | inr h =>
      exact ⟨{y}, Or.inr rfl, Set.mem_singleton_iff.mpr h⟩

/-- after Mizar ZFMISC_1:28 — a pair lies in the product of two singletons
iff it is the pair of their points. (twin: `Set.mem_prod` with
`Set.mem_singleton_iff`) -/
theorem zfmisc_1_28 (x y x1 y1 : α) :
    (x, y) ∈ ({x1} : Set α) ×ˢ {y1} ↔ x = x1 ∧ y = y1 := by
  constructor
  · intro h
    exact ⟨Set.mem_singleton_iff.mp h.1, Set.mem_singleton_iff.mp h.2⟩
  · intro h
    cases h with
    | intro h1 h2 =>
      subst h1
      subst h2
      exact Set.mk_mem_prod (Set.mem_singleton _) (Set.mem_singleton _)

/-- after Mizar ZFMISC_1:29 — the product of two singletons is the singleton
of the pair. (twin: `Set.singleton_prod_singleton`) -/
theorem zfmisc_1_29 (x y : α) : ({x} : Set α) ×ˢ {y} = {(x, y)} := by
  ext p
  constructor
  · intro h
    have h1 : p.1 = x := Set.mem_singleton_iff.mp h.1
    have h2 : p.2 = y := Set.mem_singleton_iff.mp h.2
    rw [Set.mem_singleton_iff]
    exact Prod.ext h1 h2
  · intro h
    rw [Set.mem_singleton_iff] at h
    rw [h]
    exact Set.mk_mem_prod (Set.mem_singleton x) (Set.mem_singleton y)

/-- after Mizar ZFMISC_1:30 — distributing a product over a pair on either
side gives the pair of products. -/
theorem zfmisc_1_30 (x y z : α) :
    ({x} : Set α) ×ˢ {y, z} = {(x, y), (x, z)} ∧
      ({x, y} : Set α) ×ˢ {z} = {(x, z), (y, z)} := by
  constructor
  · ext p
    constructor
    · intro h
      have ha : p.1 = x := Set.mem_singleton_iff.mp h.1
      have hb : p.2 = y ∨ p.2 = z := by
        have h2 := h.2
        rwa [Set.mem_insert_iff, Set.mem_singleton_iff] at h2
      cases hb with
      | inl hb =>
        have hp : p = (x, y) := Prod.ext ha hb
        rw [hp]
        exact Set.mem_insert (x, y) {(x, z)}
      | inr hb =>
        have hp : p = (x, z) := Prod.ext ha hb
        rw [hp]
        exact Set.mem_insert_of_mem (x, y) (Set.mem_singleton (x, z))
    · intro h
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      cases h with
      | inl h =>
        rw [h]
        exact Set.mk_mem_prod (Set.mem_singleton x) (Set.mem_insert y {z})
      | inr h =>
        rw [h]
        exact Set.mk_mem_prod (Set.mem_singleton x)
          (Set.mem_insert_of_mem y (Set.mem_singleton z))
  · ext p
    constructor
    · intro h
      have ha : p.1 = x ∨ p.1 = y := by
        have h1 := h.1
        rwa [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
      have hb : p.2 = z := Set.mem_singleton_iff.mp h.2
      cases ha with
      | inl ha =>
        have hp : p = (x, z) := Prod.ext ha hb
        rw [hp]
        exact Set.mem_insert (x, z) {(y, z)}
      | inr ha =>
        have hp : p = (y, z) := Prod.ext ha hb
        rw [hp]
        exact Set.mem_insert_of_mem (x, z) (Set.mem_singleton (y, z))
    · intro h
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      cases h with
      | inl h =>
        rw [h]
        exact Set.mk_mem_prod (Set.mem_insert x {y}) (Set.mem_singleton z)
      | inr h =>
        rw [h]
        exact Set.mk_mem_prod
          (Set.mem_insert_of_mem x (Set.mem_singleton y)) (Set.mem_singleton z)

/-- after Mizar ZFMISC_1:31 — a singleton is contained in a set iff its
point lies in the set. (twin: `Set.singleton_subset_iff`) -/
theorem zfmisc_1_31 (x : α) (X : Set α) : ({x} : Set α) ⊆ X ↔ x ∈ X :=
  Set.singleton_subset_iff

end ThetLogos.MizarPilot1.B3
