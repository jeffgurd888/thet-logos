import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Prod
import Mathlib.Data.Prod.Basic

/-!
# Mizar Pilot Tranche 2 — Brick B3 (SUBSET_1 remainder ×12 + ZFMISC_1 ×30)

Working label: MZ-W1-P2. MZ pilot wave, tranche 2, brick B3.
Source working list: the Mizar registry (SUBSET_1:42–:53 and
ZFMISC_1:32–:61 drawn for this brick: 42 items).

**NO CLAIM; dials 0/4.** This is a re-proof exercise against a foreign
registry, at restatement grade only: nothing here is counted toward the
corpus census, and no dial moves on the strength of this file.

Protocol: one theorem per Mizar item, restated in the house idiom below;
priority for the underlying results belongs to the Mizar library
(SUBSET_1 / ZFMISC_1) — these are re-proofs in our environment, disclosed
as twins where a Mathlib lemma already carries the content. An item that
resists is marked as stuck in place, never silently dropped — all 42
identifiers appear below. (No item in this brick is stuck: every registry
text was checked against the current Mizar source and reads true under
the literal reading once the typing context noted below is restored.)

Restatement idiom:
- Mizar sets / subsets of a set `E` → `Set α`; `c=` → `⊆`; `c<` → `⊂`
  (strict inclusion); `\/` → `∪`; `/\` → `∩`; `\` → `\`;
  `{x}`, `{x, y}` → Set insert notation.
- Mizar `A misses B` → `Disjoint A B`.
- Mizar's typed `A` being a Subset of `E` (i.e. `A ⊆ E` by typing) is
  flattened to an explicit hypothesis where the argument uses it
  (SUBSET_1:42, :44, :45, :47, :51).
- SUBSET_1:42: Mizar's complement `A\`` is the E-relative complement
  (SUBSET_1:def 4: `A\` = E \ A`), and `A`, `B` are Subsets of `E` by the
  standing reserve in SUBSET_1, so :42 is restated with the honest
  E-relative complement `E \ A = E \ B`, following the P1-B3 precedent
  for SUBSET_1:30 (the univ-complement flattening would state a
  different, stronger-hypothesis implication).
- SUBSET_1 `trivial` (SUBSET_1:def 7): a set `S` is trivial iff any two
  of its elements are equal. It is restated literally as the predicate
  `∀ a ∈ S, ∀ b ∈ S, a = b`; `non trivial` is its negation
  (SUBSET_1:45–:48, :50, :51; also :46, :47 for the trivial side).
  `X` being a non empty set is restated as `X.Nonempty`.
- SUBSET_1:49: Mizar's `In(x, X)` (SUBSET_1:def 8) is defined, under the
  assumption `x ∈ X`, to equal `x` as an Element of `X`. It is restated
  by its definition via `mizarIn` below, exactly as P1-B3 restated
  ZFMISC_1:23's `\+/` by its definition.
- SUBSET_1:43: in Mizar both factors of `[:X, Y:]` are sets of objects
  in one universe; the house idiom puts both over the same `α`, so
  `A : Set (α × α)`, `z : α × α` and `[:X, Y:]` → `X ×ˢ Y` (`Set.prod`);
  ordered pair `[x, y]` → `(x, y)`.
- SUBSET_1:52, :53: the variables `x1, …, x10` are reserved in SUBSET_1
  as `Element of X`, and the hypothesis `X ≠ {}` is in force, so each
  `xi` lies in `X`. That typing is flattened to the explicit membership
  hypotheses `hx1, …, hx10`; the stated `X ≠ ∅` hypothesis is then
  redundant (it follows from `hx1`) and is retained for fidelity.
  " `{x1, …, xn}` is Subset of X" is restated as `⊆ X`.
- Mizar objects quantified without a set typing (`p being set`,
  `y be object`) are flattened to `α`, the universe of this brick.
-/

namespace ThetLogos.MizarPilot2.B3

variable {α : Type*}

/-- Mizar's `In(x, X)` (SUBSET_1:def 8): under the assumption `x ∈ X`,
`In(x, X)` equals `x`, as an Element of `X`. Restated by its definition;
used only in SUBSET_1:49 below. -/
def mizarIn (x : α) (X : Set α) (_h : x ∈ X) : α := x

/-- after Mizar SUBSET_1:42 — equal E-relative complements of subsets of
`E` force the sets equal. (`A\`` is `E \ A` by SUBSET_1:def 4; the
univ-complement analogue is `Set.compl_injective`.) -/
theorem subset_1_42 (A B E : Set α) (hAE : A ⊆ E) (hBE : B ⊆ E)
    (h : E \ A = E \ B) : A = B := by
  ext x
  by_cases hxE : x ∈ E
  · constructor
    · intro hxa
      by_contra hxb
      have hxEB : x ∈ E \ B := ⟨hxE, hxb⟩
      rw [← h] at hxEB
      exact hxEB.2 hxa
    · intro hxb
      by_contra hxa
      have hxEA : x ∈ E \ A := ⟨hxE, hxa⟩
      rw [h] at hxEA
      exact hxEA.2 hxb
  · have hxA : x ∉ A := fun hxa => hxE (hAE hxa)
    have hxB : x ∉ B := fun hxb => hxE (hBE hxb)
    exact iff_of_false hxA hxB

/-- after Mizar SUBSET_1:43 — a point of a subset of a Cartesian product
is a pair of points of the two factors. (twin in content: `Set.mem_prod`
for the membership of `z` in `X ×ˢ Y`) -/
theorem subset_1_43 (X Y : Set α) (A : Set (α × α)) (z : α × α)
    (hz : z ∈ A) (hA : A ⊆ X ×ˢ Y) :
    ∃ x, x ∈ X ∧ ∃ y, y ∈ Y ∧ z = (x, y) := by
  have hz2 := hA hz
  cases z with
  | mk x y =>
    exact ⟨x, hz2.1, y, hz2.2, rfl⟩

/-- after Mizar SUBSET_1:44 — a strictly smaller nonempty subset is
contained in the larger set minus a single point of the larger set.
(`A`, `B` are nonempty Subsets of `X` by Mizar typing, flattened to
`hAX`, `hBX`, `hA`, `hB`; `A c< B` is `A ⊂ B`.) -/
theorem subset_1_44 (X A B : Set α) (hAX : A ⊆ X) (hBX : B ⊆ X)
    (hA : A.Nonempty) (hB : B.Nonempty) (hAB : A ⊂ B) :
    ∃ p, p ∈ B ∧ A ⊆ B \ {p} := by
  have hex : ∃ p, p ∈ B ∧ p ∉ A := by
    by_contra h
    apply hAB.2
    intro p hp
    by_contra hpA
    exact h ⟨p, hp, hpA⟩
  obtain ⟨p, hpB, hpA⟩ := hex
  refine ⟨p, hpB, ?_⟩
  intro a ha
  refine ⟨hAB.1 ha, ?_⟩
  intro hap
  rw [Set.mem_singleton_iff] at hap
  subst hap
  exact hpA ha

/-- after Mizar SUBSET_1:45 — a non trivial subset has two distinct
points. Here `A` is a Subset of `D` (flattened to `hAD`), and
`A is non trivial` is the negation of SUBSET_1:def 7; the conclusion's
`d1, d2` are Elements of `D`, with membership in `D` supplied by `hAD`.
(In content this is the defining property of Mathlib's
`Set.Nontrivial A`.) -/
theorem subset_1_45 (D A : Set α) (hAD : A ⊆ D)
    (hnt : ¬ ∀ a ∈ A, ∀ b ∈ A, a = b) :
    ∃ d1, d1 ∈ D ∧ d1 ∈ A ∧ ∃ d2, d2 ∈ D ∧ d2 ∈ A ∧ d1 ≠ d2 := by
  have hex : ∃ d1, d1 ∈ A ∧ ∃ d2, d2 ∈ A ∧ d1 ≠ d2 := by
    by_contra h
    apply hnt
    intro a ha b hb
    by_contra hab
    exact h ⟨a, ha, b, hb, hab⟩
  obtain ⟨d1, hd1, d2, hd2, hne⟩ := hex
  exact ⟨d1, hAD hd1, hd1, d2, hAD hd2, hd2, hne⟩

/-- after Mizar SUBSET_1:46 — a trivial nonempty set is a singleton. -/
theorem subset_1_46 (X : Set α) (htriv : ∀ a ∈ X, ∀ b ∈ X, a = b)
    (hne : X.Nonempty) : ∃ x, x ∈ X ∧ X = {x} := by
  obtain ⟨x, hx⟩ := hne
  refine ⟨x, hx, ?_⟩
  ext y
  constructor
  · intro hy
    exact Set.mem_singleton_iff.mpr (htriv y hy x hx)
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hx

/-- after Mizar SUBSET_1:47 — a trivial nonempty subset is a singleton
at a point of the ambient set. (`A` is a non empty Subset of `X` by
Mizar typing, flattened to `hAX` and `hne`.) -/
theorem subset_1_47 (X A : Set α) (hAX : A ⊆ X)
    (htriv : ∀ a ∈ A, ∀ b ∈ A, a = b) (hne : A.Nonempty) :
    ∃ x, x ∈ X ∧ A = {x} := by
  obtain ⟨x, hx⟩ := hne
  refine ⟨x, hAX hx, ?_⟩
  ext y
  constructor
  · intro hy
    exact Set.mem_singleton_iff.mpr (htriv y hy x hx)
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hx

/-- after Mizar SUBSET_1:48 — in a non trivial set, any given point has
another point beside it. -/
theorem subset_1_48 (X : Set α) (hnt : ¬ ∀ a ∈ X, ∀ b ∈ X, a = b)
    (x : α) (hx : x ∈ X) : ∃ y, y ∈ X ∧ x ≠ y := by
  by_contra h
  apply hnt
  intro a ha b hb
  have hax : a = x := by
    by_contra hax
    exact h ⟨a, ha, fun hxa => hax hxa.symm⟩
  have hbx : b = x := by
    by_contra hbx
    exact h ⟨b, hb, fun hxb => hbx hxb.symm⟩
  exact hax.trans hbx.symm

/-- after Mizar SUBSET_1:49 — if `x` lies in `X ∩ Y`, then `In(x, X)`
equals `In(x, Y)`. (`In` restated by its definition, SUBSET_1:def 8:
both sides are `x`.) -/
theorem subset_1_49 (x : α) (X Y : Set α) (h : x ∈ X ∩ Y) :
    mizarIn x X h.1 = mizarIn x Y h.2 :=
  rfl

/-- after Mizar SUBSET_1:50 — a non trivial set has a point different
from any given object. (Routes through SUBSET_1:45.) -/
theorem subset_1_50 (X : Set α) (hnt : ¬ ∀ a ∈ X, ∀ b ∈ X, a = b)
    (p : α) : ∃ q, q ∈ X ∧ q ≠ p := by
  obtain ⟨d1, _, hd1, d2, _, hd2, hne⟩ :=
    subset_1_45 X X (fun _ h => h) hnt
  by_cases h1 : d1 = p
  · refine ⟨d2, hd2, ?_⟩
    intro h2
    exact hne (h1.trans h2.symm)
  · exact ⟨d1, hd1, h1⟩

/-- after Mizar SUBSET_1:51 — a non trivial subset of a set has a point
different from any given object. (`X` is a non trivial Subset of `T` by
Mizar typing, flattened to `hXT`; `T`'s own non triviality is retained
as `hntT` for fidelity and is implied by the rest. Routes through
SUBSET_1:45.) -/
theorem subset_1_51 (T X : Set α) (hXT : X ⊆ T)
    (hntT : ¬ ∀ a ∈ T, ∀ b ∈ T, a = b)
    (hntX : ¬ ∀ a ∈ X, ∀ b ∈ X, a = b) (p : α) :
    ∃ q, q ∈ T ∧ q ∈ X ∧ q ≠ p := by
  obtain ⟨d1, hd1T, hd1X, d2, hd2T, hd2X, hne⟩ :=
    subset_1_45 T X hXT hntX
  by_cases h1 : d1 = p
  · refine ⟨d2, hd2T, hd2X, ?_⟩
    intro h2
    exact hne (h1.trans h2.symm)
  · exact ⟨d1, hd1T, hd1X, h1⟩

/-- after Mizar SUBSET_1:52 — a nine-point enumeration of Elements of a
nonempty set `X` is a subset of `X`. (The `xi` are Elements of `X` by
the standing reserve in SUBSET_1, flattened to `hx1, …, hx9`; the
hypothesis `X ≠ ∅` is retained for fidelity.) -/
theorem subset_1_52 (X : Set α) (hX : X ≠ ∅)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 : α)
    (hx1 : x1 ∈ X) (hx2 : x2 ∈ X) (hx3 : x3 ∈ X) (hx4 : x4 ∈ X)
    (hx5 : x5 ∈ X) (hx6 : x6 ∈ X) (hx7 : x7 ∈ X) (hx8 : x8 ∈ X)
    (hx9 : x9 ∈ X) :
    ({x1, x2, x3, x4, x5, x6, x7, x8, x9} : Set α) ⊆ X := by
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hx1
  · exact hx2
  · exact hx3
  · exact hx4
  · exact hx5
  · exact hx6
  · exact hx7
  · exact hx8
  · exact hx9

/-- after Mizar SUBSET_1:53 — a ten-point enumeration of Elements of a
nonempty set `X` is a subset of `X`. (Same flattening as SUBSET_1:52.) -/
theorem subset_1_53 (X : Set α) (hX : X ≠ ∅)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : α)
    (hx1 : x1 ∈ X) (hx2 : x2 ∈ X) (hx3 : x3 ∈ X) (hx4 : x4 ∈ X)
    (hx5 : x5 ∈ X) (hx6 : x6 ∈ X) (hx7 : x7 ∈ X) (hx8 : x8 ∈ X)
    (hx9 : x9 ∈ X) (hx10 : x10 ∈ X) :
    ({x1, x2, x3, x4, x5, x6, x7, x8, x9, x10} : Set α) ⊆ X := by
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hx1
  · exact hx2
  · exact hx3
  · exact hx4
  · exact hx5
  · exact hx6
  · exact hx7
  · exact hx8
  · exact hx9
  · exact hx10

/-- after Mizar ZFMISC_1:32 — a pair is contained in a set iff both of
its points lie in the set. (twin: `Set.insert_subset_iff` with
`Set.singleton_subset_iff`) -/
theorem zfmisc_1_32 (x1 x2 : α) (Z : Set α) :
    ({x1, x2} : Set α) ⊆ Z ↔ x1 ∈ Z ∧ x2 ∈ Z := by
  constructor
  · intro h
    exact ⟨h (Set.mem_insert x1 {x2}),
      h (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton x2)))⟩
  · intro h a ha
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    cases ha with
    | inl ha => rw [ha]; exact h.1
    | inr ha => rw [ha]; exact h.2

/-- after Mizar ZFMISC_1:33 — a set contained in a singleton is empty or
the singleton itself. (twin: `Set.subset_singleton_iff_eq`) -/
theorem zfmisc_1_33 (x : α) (Y : Set α) :
    Y ⊆ {x} ↔ Y = ∅ ∨ Y = {x} := by
  constructor
  · intro h
    by_cases hx : x ∈ Y
    · refine Or.inr ?_
      ext a
      constructor
      · intro ha
        exact Set.mem_singleton_iff.mpr (Set.mem_singleton_iff.mp (h ha))
      · intro ha
        rw [Set.mem_singleton_iff] at ha
        rw [ha]
        exact hx
    · refine Or.inl ?_
      apply Set.eq_empty_of_forall_notMem
      intro a ha
      exact hx ((Set.mem_singleton_iff.mp (h ha)) ▸ ha)
  · intro h
    cases h with
    | inl h => rw [h]; exact fun a ha => absurd ha (Set.notMem_empty a)
    | inr h => rw [h]

/-- after Mizar ZFMISC_1:34 — a subset avoiding `x` is contained in the
set minus `x`. -/
theorem zfmisc_1_34 (x : α) (X Y : Set α) (h : Y ⊆ X ∧ x ∉ Y) :
    Y ⊆ X \ {x} := by
  intro y hy
  refine ⟨h.1 hy, ?_⟩
  intro hyx
  rw [Set.mem_singleton_iff] at hyx
  subst hyx
  exact h.2 hy

/-- after Mizar ZFMISC_1:35 — a set that is neither empty nor a given
singleton has a point different from the singleton's point. -/
theorem zfmisc_1_35 (x : α) (X : Set α) (h1 : X ≠ {x}) (h2 : X ≠ ∅) :
    ∃ y, y ∈ X ∧ y ≠ x := by
  have hne : X.Nonempty := by
    by_contra hc
    exact h2 (Set.eq_empty_of_forall_notMem (fun a ha => hc ⟨a, ha⟩))
  obtain ⟨a, ha⟩ := hne
  by_cases hax : a = x
  · by_contra hcon
    apply h1
    ext b
    constructor
    · intro hb
      by_contra hbx
      rw [Set.mem_singleton_iff] at hbx
      exact hcon ⟨b, hb, hbx⟩
    · intro hb
      rw [Set.mem_singleton_iff] at hb
      rw [hb]
      rw [← hax]
      exact ha
  · exact ⟨a, ha, hax⟩

/-- after Mizar ZFMISC_1:36 — the subsets of a pair are the empty set,
the two singletons, and the pair itself. -/
theorem zfmisc_1_36 (x1 x2 : α) (Z : Set α) :
    Z ⊆ {x1, x2} ↔
      Z = ∅ ∨ Z = {x1} ∨ Z = {x2} ∨ Z = ({x1, x2} : Set α) := by
  constructor
  · intro hZ
    by_cases h1 : x1 ∈ Z
    · by_cases h2 : x2 ∈ Z
      · refine Or.inr (Or.inr (Or.inr ?_))
        ext a
        constructor
        · intro ha
          have ha12 := hZ ha
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha12
          exact Set.mem_insert_iff.mpr ha12
        · intro ha
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
          cases ha with
          | inl ha => rw [ha]; exact h1
          | inr ha => rw [ha]; exact h2
      · refine Or.inr (Or.inl ?_)
        ext a
        constructor
        · intro ha
          have ha12 := hZ ha
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha12
          cases ha12 with
          | inl ha1 => exact Set.mem_singleton_iff.mpr ha1
          | inr ha2 =>
            rw [ha2] at ha
            exact absurd ha h2
        · intro ha
          rw [Set.mem_singleton_iff] at ha
          rw [ha]
          exact h1
    · by_cases h2 : x2 ∈ Z
      · refine Or.inr (Or.inr (Or.inl ?_))
        ext a
        constructor
        · intro ha
          have ha12 := hZ ha
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha12
          cases ha12 with
          | inl ha1 =>
            rw [ha1] at ha
            exact absurd ha h1
          | inr ha2 => exact Set.mem_singleton_iff.mpr ha2
        · intro ha
          rw [Set.mem_singleton_iff] at ha
          rw [ha]
          exact h2
      · refine Or.inl ?_
        apply Set.eq_empty_of_forall_notMem
        intro a ha
        have ha12 := hZ ha
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha12
        cases ha12 with
        | inl ha1 =>
          rw [ha1] at ha
          exact h1 ha
        | inr ha2 =>
          rw [ha2] at ha
          exact h2 ha
  · intro h
    cases h with
    | inl h =>
      rw [h]
      exact fun a ha => absurd ha (Set.notMem_empty a)
    | inr h =>
      cases h with
      | inl h =>
        rw [h]
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        rw [ha]
        exact Set.mem_insert x1 {x2}
      | inr h =>
        cases h with
        | inl h =>
          rw [h]
          intro a ha
          rw [Set.mem_singleton_iff] at ha
          rw [ha]
          exact Set.mem_insert_iff.mpr
            (Or.inr (Set.mem_singleton x2))
        | inr h =>
          rw [h]

/-- after Mizar ZFMISC_1:37 — if a singleton is a union, the factors are
among the empty set and the singleton itself. (Mizar's unparenthesised
`&`/`or` text read with the standard precedence: `&` binds tighter
than `or`.) -/
theorem zfmisc_1_37 (z : α) (X Y : Set α) (h : ({z} : Set α) = X ∪ Y) :
    (X = {z} ∧ Y = {z}) ∨ (X = ∅ ∧ Y = {z}) ∨ (X = {z} ∧ Y = ∅) := by
  have hXsub : X ⊆ {z} := by
    intro a ha
    have haU : a ∈ X ∪ Y := Or.inl ha
    rw [← h] at haU
    exact haU
  have hYsub : Y ⊆ {z} := by
    intro a ha
    have haU : a ∈ X ∪ Y := Or.inr ha
    rw [← h] at haU
    exact haU
  have hz : z ∈ X ∨ z ∈ Y := by
    have hzU : z ∈ X ∪ Y := by
      rw [← h]
      exact Set.mem_singleton z
    exact hzU
  by_cases hx : z ∈ X
  · by_cases hy : z ∈ Y
    · exact Or.inl
        ⟨Set.Subset.antisymm hXsub (Set.singleton_subset_iff.mpr hx),
         Set.Subset.antisymm hYsub (Set.singleton_subset_iff.mpr hy)⟩
    · refine Or.inr (Or.inr ?_)
      refine
        ⟨Set.Subset.antisymm hXsub (Set.singleton_subset_iff.mpr hx), ?_⟩
      apply Set.eq_empty_of_forall_notMem
      intro a ha
      have haz : a = z := Set.mem_singleton_iff.mp (hYsub ha)
      subst haz
      exact hy ha
  · by_cases hy : z ∈ Y
    · refine Or.inr (Or.inl ?_)
      refine
        ⟨?_, Set.Subset.antisymm hYsub (Set.singleton_subset_iff.mpr hy)⟩
      apply Set.eq_empty_of_forall_notMem
      intro a ha
      have haz : a = z := Set.mem_singleton_iff.mp (hXsub ha)
      subst haz
      exact hx ha
    · cases hz with
      | inl hz => exact absurd hz hx
      | inr hz => exact absurd hz hy

/-- after Mizar ZFMISC_1:38 — if a singleton is a union of two distinct
sets, one of the factors is empty. (Routes through ZFMISC_1:37.) -/
theorem zfmisc_1_38 (z : α) (X Y : Set α) (h : ({z} : Set α) = X ∪ Y)
    (hne : X ≠ Y) : X = ∅ ∨ Y = ∅ := by
  have h37 := zfmisc_1_37 z X Y h
  cases h37 with
  | inl h37 => exact absurd (h37.1.trans h37.2.symm) hne
  | inr h37 =>
    cases h37 with
    | inl h37 => exact Or.inl h37.1
    | inr h37 => exact Or.inr h37.2

/-- after Mizar ZFMISC_1:39 — if adjoining a singleton does not leave a
set, the point already lies in the set. -/
theorem zfmisc_1_39 (x : α) (X : Set α) (h : ({x} : Set α) ∪ X ⊆ X) :
    x ∈ X :=
  h (Or.inl (Set.mem_singleton x))

/-- after Mizar ZFMISC_1:40 — adjoining a point already in a set changes
nothing. -/
theorem zfmisc_1_40 (x : α) (X : Set α) (hx : x ∈ X) :
    ({x} : Set α) ∪ X = X := by
  ext a
  simp only [Set.mem_union, Set.mem_singleton_iff]
  constructor
  · intro h
    cases h with
    | inl h => rw [h]; exact hx
    | inr h => exact h
  · intro h
    exact Or.inr h

/-- after Mizar ZFMISC_1:41 — if adjoining a pair does not leave a set,
the pair's first point already lies in the set. -/
theorem zfmisc_1_41 (x y : α) (Z : Set α) (h : ({x, y} : Set α) ∪ Z ⊆ Z) :
    x ∈ Z :=
  h (Or.inl (Set.mem_insert x {y}))

/-- after Mizar ZFMISC_1:42 — adjoining a pair both of whose points lie
in a set changes nothing. -/
theorem zfmisc_1_42 (x y : α) (Z : Set α) (hx : x ∈ Z) (hy : y ∈ Z) :
    ({x, y} : Set α) ∪ Z = Z := by
  ext a
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    cases h with
    | inl h =>
      cases h with
      | inl h => rw [h]; exact hx
      | inr h => rw [h]; exact hy
    | inr h => exact h
  · intro h
    exact Or.inr h

/-- after Mizar ZFMISC_1:43 — a singleton union anything is nonempty. -/
theorem zfmisc_1_43 (x : α) (X : Set α) : ({x} : Set α) ∪ X ≠ ∅ := by
  intro h
  have hx : x ∈ ({x} : Set α) ∪ X := Or.inl (Set.mem_singleton x)
  rw [h] at hx
  exact Set.notMem_empty x hx

/-- after Mizar ZFMISC_1:44 — a pair union anything is nonempty. -/
theorem zfmisc_1_44 (x y : α) (X : Set α) :
    ({x, y} : Set α) ∪ X ≠ ∅ := by
  intro h
  have hx : x ∈ ({x, y} : Set α) ∪ X := Or.inl (Set.mem_insert x {y})
  rw [h] at hx
  exact Set.notMem_empty x hx

/-- after Mizar ZFMISC_1:45 — if intersecting with a singleton returns
the singleton, its point lies in the set. -/
theorem zfmisc_1_45 (x : α) (X : Set α) (h : X ∩ ({x} : Set α) = {x}) :
    x ∈ X := by
  have hx : x ∈ X ∩ ({x} : Set α) := by
    rw [h]
    exact Set.mem_singleton x
  exact hx.1

/-- after Mizar ZFMISC_1:46 — intersecting with a singleton already in
the set returns the singleton. (twin: `Set.inter_eq_right` applied to
`Set.singleton_subset_iff.mpr`) -/
theorem zfmisc_1_46 (x : α) (X : Set α) (hx : x ∈ X) :
    X ∩ ({x} : Set α) = {x} := by
  ext a
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    exact h.2
  · intro h
    subst h
    exact ⟨hx, Set.mem_singleton _⟩

/-- after Mizar ZFMISC_1:47 — intersecting a pair both of whose points
lie in a set with that set returns the pair. -/
theorem zfmisc_1_47 (x y : α) (Z : Set α) (hx : x ∈ Z) (hy : y ∈ Z) :
    ({x, y} : Set α) ∩ Z = {x, y} := by
  ext a
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    exact h.1
  · intro h
    cases h with
    | inl h =>
      subst h
      exact ⟨Or.inl rfl, hx⟩
    | inr h =>
      subst h
      exact ⟨Or.inr rfl, hy⟩

/-- after Mizar ZFMISC_1:48 — a singleton missing a set has its point
outside the set. (twin in content: `Set.disjoint_singleton_left`) -/
theorem zfmisc_1_48 (x : α) (X : Set α) (h : Disjoint ({x} : Set α) X) :
    x ∉ X :=
  fun hx => Set.disjoint_left.mp h (Set.mem_singleton x) hx

/-- after Mizar ZFMISC_1:49 — a pair missing a set has its first point
outside the set. -/
theorem zfmisc_1_49 (x y : α) (Z : Set α)
    (h : Disjoint ({x, y} : Set α) Z) : x ∉ Z :=
  fun hz => Set.disjoint_left.mp h
    (Set.mem_insert_iff.mpr (Or.inl rfl)) hz

/-- after Mizar ZFMISC_1:50 — a singleton at a point outside a set
misses the set. (twin: `Set.disjoint_singleton_left`) -/
theorem zfmisc_1_50 (x : α) (X : Set α) (hx : x ∉ X) :
    Disjoint ({x} : Set α) X := by
  rw [Set.disjoint_left]
  intro a ha hb
  rw [Set.mem_singleton_iff] at ha
  subst ha
  exact hx hb

/-- after Mizar ZFMISC_1:51 — a pair both of whose points lie outside a
set misses the set. -/
theorem zfmisc_1_51 (x y : α) (Z : Set α) (hx : x ∉ Z) (hy : y ∉ Z) :
    Disjoint ({x, y} : Set α) Z := by
  rw [Set.disjoint_left]
  intro a ha hb
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  cases ha with
  | inl ha => subst ha; exact hx hb
  | inr ha => subst ha; exact hy hb

/-- after Mizar ZFMISC_1:52 — a singleton either misses a set or
intersecting it with the set returns the singleton. (Routes through
ZFMISC_1:46 and ZFMISC_1:50.) -/
theorem zfmisc_1_52 (x : α) (X : Set α) :
    Disjoint ({x} : Set α) X ∨ ({x} : Set α) ∩ X = {x} := by
  by_cases hx : x ∈ X
  · refine Or.inr ?_
    ext a
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      exact h.1
    · intro h
      subst h
      exact ⟨Set.mem_singleton _, hx⟩
  · exact Or.inl (zfmisc_1_50 x X hx)

/-- after Mizar ZFMISC_1:53 — if intersecting a pair with a set returns
the first singleton, the second point is outside the set or the points
agree. -/
theorem zfmisc_1_53 (x y : α) (X : Set α)
    (h : ({x, y} : Set α) ∩ X = {x}) : y ∉ X ∨ x = y := by
  by_cases hy : y ∈ X
  · refine Or.inr ?_
    have hy2 : y ∈ ({x, y} : Set α) ∩ X :=
      ⟨Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton y)), hy⟩
    rw [h] at hy2
    exact (Set.mem_singleton_iff.mp hy2).symm
  · exact Or.inl hy

/-- after Mizar ZFMISC_1:54 — if the first point of a pair lies in a set
and the second point is outside it or agrees with the first,
intersecting returns the first singleton. -/
theorem zfmisc_1_54 (x y : α) (X : Set α) (hx : x ∈ X)
    (h : y ∉ X ∨ x = y) : ({x, y} : Set α) ∩ X = {x} := by
  ext a
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro ha
    cases ha.1 with
    | inl ha1 => exact ha1
    | inr ha2 =>
      cases h with
      | inl hy =>
        have hay : y ∈ X := by
          rw [← ha2]
          exact ha.2
        exact absurd hay hy
      | inr hxy => exact ha2.trans hxy.symm
  · intro ha
    subst ha
    exact ⟨Or.inl rfl, hx⟩

/-- after Mizar ZFMISC_1:55 — if intersecting a pair with a set returns
the pair, its first point lies in the set. -/
theorem zfmisc_1_55 (x y : α) (X : Set α)
    (h : ({x, y} : Set α) ∩ X = {x, y}) : x ∈ X := by
  have hx : x ∈ ({x, y} : Set α) ∩ X := by
    rw [h]
    exact Set.mem_insert x {y}
  exact hx.2

/-- after Mizar ZFMISC_1:56 — membership in a set minus a singleton.
(twin: `Set.mem_diff` with `Set.mem_singleton_iff`) -/
theorem zfmisc_1_56 (x z : α) (X : Set α) :
    z ∈ X \ {x} ↔ z ∈ X ∧ z ≠ x := by
  constructor
  · intro h
    exact ⟨h.1, fun hzx => h.2 (Set.mem_singleton_iff.mpr hzx)⟩
  · intro h
    exact ⟨h.1, fun hzx => h.2 (Set.mem_singleton_iff.mp hzx)⟩

/-- after Mizar ZFMISC_1:57 — removing a singleton from a set changes
nothing iff its point lies outside the set. -/
theorem zfmisc_1_57 (x : α) (X : Set α) :
    X \ {x} = X ↔ x ∉ X := by
  constructor
  · intro h hx
    have hxdiff : x ∈ X \ {x} := by
      rw [← h] at hx
      exact hx
    exact hxdiff.2 (Set.mem_singleton x)
  · intro hx
    ext a
    constructor
    · intro ha
      exact ha.1
    · intro ha
      refine ⟨ha, ?_⟩
      intro hax
      rw [Set.mem_singleton_iff] at hax
      subst hax
      exact hx ha

/-- after Mizar ZFMISC_1:58 — if removing a singleton from a set empties
it, the set was empty or that singleton. -/
theorem zfmisc_1_58 (x : α) (X : Set α) (h : X \ {x} = ∅) :
    X = ∅ ∨ X = {x} := by
  by_cases hx : x ∈ X
  · refine Or.inr ?_
    ext a
    constructor
    · intro ha
      by_contra hax
      rw [Set.mem_singleton_iff] at hax
      have hdiff : a ∈ X \ {x} :=
        ⟨ha, fun hax2 => hax (Set.mem_singleton_iff.mpr hax2)⟩
      rw [h] at hdiff
      exact Set.notMem_empty a hdiff
    · intro ha
      rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hx
  · refine Or.inl ?_
    apply Set.eq_empty_of_forall_notMem
    intro a ha
    have hane : a ≠ x := by
      intro hax
      subst hax
      exact hx ha
    have hdiff : a ∈ X \ {x} :=
      ⟨ha, fun hax2 => hane (Set.mem_singleton_iff.mp hax2)⟩
    rw [h] at hdiff
    exact Set.notMem_empty a hdiff

/-- after Mizar ZFMISC_1:59 — removing a set from a singleton leaves the
singleton iff its point lies outside the set. -/
theorem zfmisc_1_59 (x : α) (X : Set α) :
    ({x} : Set α) \ X = {x} ↔ x ∉ X := by
  constructor
  · intro h hx
    have hxdiff : x ∈ ({x} : Set α) \ X := by
      have hxx : x ∈ ({x} : Set α) := Set.mem_singleton x
      rw [← h] at hxx
      exact hxx
    exact hxdiff.2 hx
  · intro hx
    ext a
    constructor
    · intro ha
      exact Set.mem_singleton_iff.mp ha.1
    · intro ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact ⟨Set.mem_singleton _, hx⟩

/-- after Mizar ZFMISC_1:60 — removing a set from a singleton empties it
iff its point lies in the set. -/
theorem zfmisc_1_60 (x : α) (X : Set α) :
    ({x} : Set α) \ X = ∅ ↔ x ∈ X := by
  constructor
  · intro h
    by_contra hx
    have h59 := (zfmisc_1_59 x X).mpr hx
    rw [h59] at h
    exact Set.singleton_ne_empty x h
  · intro hx
    ext a
    constructor
    · intro ha
      have hax : a = x := Set.mem_singleton_iff.mp ha.1
      subst hax
      exact ha.2 hx
    · intro ha
      exact absurd ha (Set.notMem_empty a)

/-- after Mizar ZFMISC_1:61 — removing a set from a singleton leaves it
empty or leaves it whole. (Routes through ZFMISC_1:59 and
ZFMISC_1:60.) -/
theorem zfmisc_1_61 (x : α) (X : Set α) :
    ({x} : Set α) \ X = ∅ ∨ ({x} : Set α) \ X = {x} := by
  by_cases hx : x ∈ X
  · exact Or.inl ((zfmisc_1_60 x X).mpr hx)
  · exact Or.inr ((zfmisc_1_59 x X).mpr hx)

end ThetLogos.MizarPilot2.B3
