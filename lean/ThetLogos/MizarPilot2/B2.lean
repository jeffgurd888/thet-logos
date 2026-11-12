import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Operations
import Mathlib.Tactic.Tauto

/-!
# Mizar Pilot 2 — Brick B2: SETFAM_1 / SUBSET_1 families and subsets (continued)

Working label: MZ-W1-P2. MZ pilot wave, tranche 2, brick B2.
Source working list: the Mizar registry (SETFAM_1 items 21–49 and
SUBSET_1 items 31–41 drawn for this brick: 40 items).

**NO CLAIM; dials 0/4.** This is a re-proof exercise against a foreign
registry, at restatement grade only: nothing here is counted toward the
corpus census, and no dial moves on the strength of this file.

Protocol: every item restated + proved; twin verdicts are twin-notes,
never skips. An item that resists is marked `STUCK` in place, never
silently dropped — all 40 identifiers appear below.

Priority credit: Mizar proved it first, in its system ("after Mizar" =
Mizar proved it first); we re-prove our restatement in ours.

## Restatement idiom

As in pilot 1, brick B2: Mizar sets are restated over `Set α` for an
arbitrary type `α`. A Mizar family of sets is a `Set (Set α)`.
Mizar `\/` is `∪`, `/\` is `∩`, `\` is `\` (set difference),
`c=` is `⊆`, `misses` is `Disjoint`, and `union F` is `⋃₀ F`.

Idiom choices, flagged:

* Mizar `meet F` is **not** Mathlib `⋂₀ F`: Mizar pins
  `meet ∅ = ∅` (SETFAM_1:1), while `⋂₀ ∅ = univ` in Mathlib.
  We reuse pilot 1's local `mmeet F := ⋂₀ F ∩ ⋃₀ F`, which agrees
  with `⋂₀ F` on every nonempty family and gives `∅` on the empty
  family — exactly Mizar's convention.
* `is_finer_than` (SETFAM_1:21, 22) reuses pilot 1's local
  `IsFinerThan`, and `UNION(F, G)` reuses pilot 1's local
  `PairUnion`. The sibling operations `INTERSECTION(F, G)` and
  `DIFFERENCE(F, G)` are restated by the same pattern as the local
  `PairInter` / `PairDiff`: families of pairwise intersections /
  differences.
* Mizar `Intersect R` (SETFAM_1:43, 44) is **not** `meet R`:
  Mizar's `Intersect` of the empty family is the ambient set `X`,
  which in Mathlib is `⋂₀ ∅ = univ`. It is therefore restated as
  `⋂₀ R` directly, without the `mmeet` correction.
* `COMPLEMENT F` (SETFAM_1:32–40), for a `Subset-Family of X`, is
  the family of ambient-relative complements of the members of `F`;
  in the flattened idiom the ambient is `univ`, so it is the local
  `ComplementFam F := { P | ∃ Q ∈ F, P = Qᶜ }`. SETFAM_1:35's
  registry text `P` in COMPLEMENT F iff P in F` reads the tick on
  the left-hand `P` (the complemented member is in the complemented
  family), consistent with 36–38.
* `F is Cover of X` (SETFAM_1:45) is the local `IsCover`:
  `univ ⊆ ⋃₀ F` in the flattened idiom.
* `is Subset-Family of X` (SETFAM_1:46) is the local
  `IsSubsetFamilyOf`; `with_proper_subsets` (SETFAM_1:47, 48) is
  the local `WithProperSubsets`: every member is a strict subset
  of the ambient set (`⊂ univ` flattened).
* SUBSET_1 flattening as in pilot 1 (plain `Set α`, `[#] E` =
  `Set.univ`, complement tick = `ᶜ`). For SUBSET_1:33–40 the
  points `x1, …, x8` are Mizar `Element of X`; the element
  discipline is restated as explicit membership hypotheses
  `xi ∈ X`. Mizar's side hypothesis `X ≠ ∅` is then absorbed —
  a membership hypothesis already witnesses it — and is not
  repeated (see the report).
-/

namespace ThetLogos.MizarPilot2.B2

variable {α : Type*}

/-- Mizar `meet F`, with Mizar's convention `meet ∅ = ∅`
(unlike Mathlib's `⋂₀ ∅ = univ`). Re-declared from pilot 1. -/
def mmeet (F : Set (Set α)) : Set α := ⋂₀ F ∩ ⋃₀ F

/-- Mizar `F is_finer_than G`: every member of `F` is included in
some member of `G`. Re-declared from pilot 1. -/
def IsFinerThan (F G : Set (Set α)) : Prop :=
  ∀ X ∈ F, ∃ Y ∈ G, X ⊆ Y

/-- Mizar `UNION(F, G)`: the family of pairwise unions.
Re-declared from pilot 1. -/
def PairUnion (F G : Set (Set α)) : Set (Set α) :=
  { Z | ∃ X ∈ F, ∃ Y ∈ G, Z = X ∪ Y }

/-- Mizar `INTERSECTION(F, G)`: the family of pairwise
intersections. -/
def PairInter (F G : Set (Set α)) : Set (Set α) :=
  { Z | ∃ X ∈ F, ∃ Y ∈ G, Z = X ∩ Y }

/-- Mizar `DIFFERENCE(F, G)`: the family of pairwise
differences. -/
def PairDiff (F G : Set (Set α)) : Set (Set α) :=
  { Z | ∃ X ∈ F, ∃ Y ∈ G, Z = X \ Y }

/-- Mizar `COMPLEMENT F` for a family over the ambient set:
the family of complements of the members of `F`. -/
def ComplementFam (F : Set (Set α)) : Set (Set α) :=
  { P | ∃ Q ∈ F, P = Qᶜ }

/-- Mizar `F is Cover of X`, flattened (ambient `X` = `univ`):
the union of `F` covers the whole ambient set. -/
def IsCover (F : Set (Set α)) : Prop :=
  (Set.univ : Set α) ⊆ ⋃₀ F

/-- Mizar `F is Subset-Family of D`: every member of `F` is
included in `D`. -/
def IsSubsetFamilyOf (D : Set α) (F : Set (Set α)) : Prop :=
  ∀ Y ∈ F, Y ⊆ D

/-- Mizar `F is with_proper_subsets`, flattened (ambient =
`univ`): every member of `F` is a strict subset of the
ambient set. -/
def WithProperSubsets (F : Set (Set α)) : Prop :=
  ∀ Y ∈ F, Y ⊂ Set.univ

/-- Auxiliary (from pilot 1): on a nonempty family, `mmeet` is
Mathlib's `⋂₀`. -/
theorem mmeet_eq_sInter_of_nonempty {F : Set (Set α)} (hF : F.Nonempty) :
    mmeet F = ⋂₀ F := by
  apply Set.Subset.antisymm Set.inter_subset_left
  intro x hx
  obtain ⟨T, hT⟩ := hF
  have hxT : x ∈ T := Set.mem_sInter.mp hx T hT
  exact ⟨hx, Set.mem_sUnion.mpr ⟨T, hT, hxT⟩⟩

/-- after Mizar SETFAM_1:21 — the pairwise-intersection family
of a family with itself is finer than the family. -/
theorem setfam_1_21_pairInter_finer_self {SFX : Set (Set α)} :
    IsFinerThan (PairInter SFX SFX) SFX := by
  intro Z hZ
  obtain ⟨X, hX, Y, _hY, rfl⟩ := hZ
  exact ⟨X, hX, Set.inter_subset_left⟩

/-- after Mizar SETFAM_1:22 — the pairwise-difference family
of a family with itself is finer than the family. -/
theorem setfam_1_22_pairDiff_finer_self {SFX : Set (Set α)} :
    IsFinerThan (PairDiff SFX SFX) SFX := by
  intro Z hZ
  obtain ⟨X, hX, Y, _hY, rfl⟩ := hZ
  exact ⟨X, hX, Set.diff_subset⟩

/-- after Mizar SETFAM_1:23 — if the two families meet (have a
common member, Mizar's `SFX meets SFY` for families), the
intersection of their `meet`s is the `meet` of their
pairwise-intersection family. -/
theorem setfam_1_23_meet_pairInter {SFX SFY : Set (Set α)}
    (h : ∃ Z, Z ∈ SFX ∧ Z ∈ SFY) :
    mmeet SFX ∩ mmeet SFY = mmeet (PairInter SFX SFY) := by
  obtain ⟨Z0, hZ0F, hZ0G⟩ := h
  ext x
  constructor
  · intro hx
    have hAllF : ∀ t ∈ SFX, x ∈ t := Set.mem_sInter.mp hx.1.1
    have hAllG : ∀ t ∈ SFY, x ∈ t := Set.mem_sInter.mp hx.2.1
    show x ∈ ⋂₀ (PairInter SFX SFY) ∩ ⋃₀ (PairInter SFX SFY)
    refine ⟨?_, ?_⟩
    · rw [Set.mem_sInter]
      intro Z hZ
      obtain ⟨A, hA, B, hB, rfl⟩ := hZ
      exact ⟨hAllF A hA, hAllG B hB⟩
    · exact Set.mem_sUnion.mpr
        ⟨Z0 ∩ Z0, ⟨Z0, hZ0F, Z0, hZ0G, rfl⟩,
          ⟨hAllF Z0 hZ0F, hAllG Z0 hZ0G⟩⟩
  · intro hx
    have hAllP : ∀ t ∈ PairInter SFX SFY, x ∈ t :=
      Set.mem_sInter.mp hx.1
    obtain ⟨Z, hZ, hxZ⟩ := Set.mem_sUnion.mp hx.2
    obtain ⟨A0, hA0, B0, hB0, hZeq⟩ := hZ
    rw [hZeq] at hxZ
    refine ⟨?_, ?_⟩
    · show x ∈ ⋂₀ SFX ∩ ⋃₀ SFX
      refine ⟨?_, ?_⟩
      · rw [Set.mem_sInter]
        intro A hA
        exact (hAllP (A ∩ Z0) ⟨A, hA, Z0, hZ0G, rfl⟩).1
      · exact Set.mem_sUnion.mpr ⟨A0, hA0, hxZ.1⟩
    · show x ∈ ⋂₀ SFY ∩ ⋃₀ SFY
      refine ⟨?_, ?_⟩
      · rw [Set.mem_sInter]
        intro B hB
        exact (hAllP (Z0 ∩ B) ⟨Z0, hZ0F, B, hB, rfl⟩).2
      · exact Set.mem_sUnion.mpr ⟨B0, hB0, hxZ.2⟩

/-- after Mizar SETFAM_1:24 — union with `X` distributes over
a nonempty family's `meet`, as the `meet` of the pairwise-union
family with the singleton `{X}`. -/
theorem setfam_1_24_union_mmeet {X : Set α} {SFY : Set (Set α)}
    (hne : SFY ≠ ∅) :
    X ∪ mmeet SFY = mmeet (PairUnion {X} SFY) := by
  obtain ⟨Y0, hY0⟩ := Set.nonempty_iff_ne_empty.mpr hne
  ext x
  constructor
  · intro hx
    show x ∈ ⋂₀ (PairUnion {X} SFY) ∩ ⋃₀ (PairUnion {X} SFY)
    rcases hx with hxX | hxM
    · refine ⟨?_, ?_⟩
      · rw [Set.mem_sInter]
        intro Z hZ
        obtain ⟨A, hA, Y, hY, rfl⟩ := hZ
        rw [Set.mem_singleton_iff] at hA
        rw [hA]
        exact Set.mem_union_left _ hxX
      · exact Set.mem_sUnion.mpr
          ⟨X ∪ Y0, ⟨X, Set.mem_singleton X, Y0, hY0, rfl⟩,
            Set.mem_union_left _ hxX⟩
    · have hAll : ∀ t ∈ SFY, x ∈ t := Set.mem_sInter.mp hxM.1
      refine ⟨?_, ?_⟩
      · rw [Set.mem_sInter]
        intro Z hZ
        obtain ⟨A, hA, Y, hY, rfl⟩ := hZ
        rw [Set.mem_singleton_iff] at hA
        rw [hA]
        exact Set.mem_union_right _ (hAll Y hY)
      · exact Set.mem_sUnion.mpr
          ⟨X ∪ Y0, ⟨X, Set.mem_singleton X, Y0, hY0, rfl⟩,
            Set.mem_union_right _ (hAll Y0 hY0)⟩
  · intro hx
    have hAll : ∀ t ∈ PairUnion {X} SFY, x ∈ t :=
      Set.mem_sInter.mp hx.1
    obtain ⟨Z, hZ, hxZ⟩ := Set.mem_sUnion.mp hx.2
    obtain ⟨A, hA, Y1, hY1, hZeq⟩ := hZ
    rw [Set.mem_singleton_iff] at hA
    rw [hZeq, hA] at hxZ
    by_cases hxX : x ∈ X
    · exact Or.inl hxX
    · refine Or.inr ?_
      show x ∈ ⋂₀ SFY ∩ ⋃₀ SFY
      refine ⟨?_, ?_⟩
      · rw [Set.mem_sInter]
        intro Y hY
        have hmem := hAll (X ∪ Y) ⟨X, Set.mem_singleton X, Y, hY, rfl⟩
        rcases (Set.mem_union x X Y).mp hmem with h | h
        · exact absurd h hxX
        · exact h
      · rcases (Set.mem_union x X Y1).mp hxZ with h | h
        · exact absurd h hxX
        · exact Set.mem_sUnion.mpr ⟨Y1, hY1, h⟩

/-- after Mizar SETFAM_1:25 — intersection with `X` distributes
over a family's union, as the union of the pairwise-intersection
family with the singleton `{X}`. -/
theorem setfam_1_25_inter_sUnion {X : Set α} {SFY : Set (Set α)} :
    X ∩ ⋃₀ SFY = ⋃₀ (PairInter {X} SFY) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxX, hxU⟩ := hx
    obtain ⟨Y, hY, hxY⟩ := Set.mem_sUnion.mp hxU
    exact Set.mem_sUnion.mpr
      ⟨X ∩ Y, ⟨X, Set.mem_singleton X, Y, hY, rfl⟩, ⟨hxX, hxY⟩⟩
  · intro hx
    obtain ⟨Z, hZ, hxZ⟩ := Set.mem_sUnion.mp hx
    obtain ⟨A, hA, Y, hY, rfl⟩ := hZ
    rw [Set.mem_singleton_iff] at hA
    rw [hA] at hxZ
    exact ⟨hxZ.1, Set.mem_sUnion.mpr ⟨Y, hY, hxZ.2⟩⟩

/-- after Mizar SETFAM_1:26 — difference from `X` turns a
nonempty family's union into the `meet` of the pairwise-difference
family with the singleton `{X}`. -/
theorem setfam_1_26_diff_sUnion {X : Set α} {SFY : Set (Set α)}
    (hne : SFY ≠ ∅) :
    X \ ⋃₀ SFY = mmeet (PairDiff {X} SFY) := by
  obtain ⟨Y0, hY0⟩ := Set.nonempty_iff_ne_empty.mpr hne
  ext x
  constructor
  · intro hx
    have hxX : x ∈ X := ((Set.mem_sdiff _).mp hx).1
    have hxU : x ∉ ⋃₀ SFY := ((Set.mem_sdiff _).mp hx).2
    have hAll : ∀ Y ∈ SFY, x ∉ Y := by
      intro Y hY hxY
      exact hxU (Set.mem_sUnion.mpr ⟨Y, hY, hxY⟩)
    show x ∈ ⋂₀ (PairDiff {X} SFY) ∩ ⋃₀ (PairDiff {X} SFY)
    refine ⟨?_, ?_⟩
    · rw [Set.mem_sInter]
      intro Z hZ
      obtain ⟨A, hA, Y, hY, rfl⟩ := hZ
      rw [Set.mem_singleton_iff] at hA
      rw [hA]
      exact ⟨hxX, hAll Y hY⟩
    · exact Set.mem_sUnion.mpr
        ⟨X \ Y0, ⟨X, Set.mem_singleton X, Y0, hY0, rfl⟩,
          ⟨hxX, hAll Y0 hY0⟩⟩
  · intro hx
    have hAll : ∀ t ∈ PairDiff {X} SFY, x ∈ t :=
      Set.mem_sInter.mp hx.1
    obtain ⟨Z, hZ, hxZ⟩ := Set.mem_sUnion.mp hx.2
    obtain ⟨A, hA, Y0, hY0, hZeq⟩ := hZ
    rw [Set.mem_singleton_iff] at hA
    rw [hZeq, hA] at hxZ
    refine ⟨((Set.mem_sdiff _).mp hxZ).1, ?_⟩
    intro hU
    obtain ⟨Y, hY, hxY⟩ := Set.mem_sUnion.mp hU
    have hmem := hAll (X \ Y) ⟨X, Set.mem_singleton X, Y, hY, rfl⟩
    exact ((Set.mem_sdiff _).mp hmem).2 hxY

/-- after Mizar SETFAM_1:27 — difference from `X` turns a
nonempty family's `meet` into the union of the pairwise-difference
family with the singleton `{X}`. -/
theorem setfam_1_27_diff_mmeet {X : Set α} {SFY : Set (Set α)}
    (hne : SFY ≠ ∅) :
    X \ mmeet SFY = ⋃₀ (PairDiff {X} SFY) := by
  obtain ⟨Y0, hY0⟩ := Set.nonempty_iff_ne_empty.mpr hne
  ext x
  constructor
  · intro hx
    have hxX : x ∈ X := ((Set.mem_sdiff _).mp hx).1
    have hxM : x ∉ mmeet SFY := ((Set.mem_sdiff _).mp hx).2
    by_cases hI : x ∈ ⋂₀ SFY
    · have hU : x ∉ ⋃₀ SFY := by
        intro hU
        exact hxM ⟨hI, hU⟩
      have hxY0 : x ∉ Y0 := by
        intro h
        exact hU (Set.mem_sUnion.mpr ⟨Y0, hY0, h⟩)
      exact Set.mem_sUnion.mpr
        ⟨X \ Y0, ⟨X, Set.mem_singleton X, Y0, hY0, rfl⟩,
          ⟨hxX, hxY0⟩⟩
    · have hex : ∃ Y ∈ SFY, x ∉ Y := by
        simp only [Set.mem_sInter, not_forall, not_imp] at hI
        obtain ⟨Y, hY, hxY⟩ := hI
        exact ⟨Y, hY, hxY⟩
      obtain ⟨Y, hY, hxY⟩ := hex
      exact Set.mem_sUnion.mpr
        ⟨X \ Y, ⟨X, Set.mem_singleton X, Y, hY, rfl⟩, ⟨hxX, hxY⟩⟩
  · intro hx
    obtain ⟨Z, hZ, hxZ⟩ := Set.mem_sUnion.mp hx
    obtain ⟨A, hA, Y, hY, hZeq⟩ := hZ
    rw [Set.mem_singleton_iff] at hA
    rw [hZeq, hA] at hxZ
    have hxY : x ∉ Y := ((Set.mem_sdiff _).mp hxZ).2
    have hxX : x ∈ X := ((Set.mem_sdiff _).mp hxZ).1
    refine (Set.mem_sdiff _).mpr ⟨hxX, ?_⟩
    intro hxM
    exact hxY (Set.mem_sInter.mp hxM.1 Y hY)

/-- after Mizar SETFAM_1:28 — the union of the pairwise-intersection
family is the intersection of the unions. -/
theorem setfam_1_28_sUnion_pairInter {SFX SFY : Set (Set α)} :
    ⋃₀ (PairInter SFX SFY) = ⋃₀ SFX ∩ ⋃₀ SFY := by
  ext x
  constructor
  · intro hx
    obtain ⟨Z, hZ, hxZ⟩ := Set.mem_sUnion.mp hx
    obtain ⟨A, hA, B, hB, rfl⟩ := hZ
    exact ⟨Set.mem_sUnion.mpr ⟨A, hA, hxZ.1⟩,
      Set.mem_sUnion.mpr ⟨B, hB, hxZ.2⟩⟩
  · intro hx
    obtain ⟨A, hA, hxA⟩ := Set.mem_sUnion.mp hx.1
    obtain ⟨B, hB, hxB⟩ := Set.mem_sUnion.mp hx.2
    exact Set.mem_sUnion.mpr
      ⟨A ∩ B, ⟨A, hA, B, hB, rfl⟩, ⟨hxA, hxB⟩⟩

/-- after Mizar SETFAM_1:29 — for two nonempty families, the
union of their `meet`s is included in the `meet` of their
pairwise-union family. -/
theorem setfam_1_29_meets_subset_mmeet_pairUnion {SFX SFY : Set (Set α)}
    (hX : SFX.Nonempty) (hY : SFY.Nonempty) :
    mmeet SFX ∪ mmeet SFY ⊆ mmeet (PairUnion SFX SFY) := by
  obtain ⟨A0, hA0⟩ := hX
  obtain ⟨B0, hB0⟩ := hY
  intro x hx
  show x ∈ ⋂₀ (PairUnion SFX SFY) ∩ ⋃₀ (PairUnion SFX SFY)
  rcases hx with hxF | hxG
  · have hAllF : ∀ t ∈ SFX, x ∈ t := Set.mem_sInter.mp hxF.1
    refine ⟨?_, ?_⟩
    · rw [Set.mem_sInter]
      intro Z hZ
      obtain ⟨A, hA, B, _hB, rfl⟩ := hZ
      exact Set.mem_union_left _ (hAllF A hA)
    · obtain ⟨A, hA, hxA⟩ := Set.mem_sUnion.mp hxF.2
      exact Set.mem_sUnion.mpr
        ⟨A ∪ B0, ⟨A, hA, B0, hB0, rfl⟩, Set.mem_union_left _ hxA⟩
  · have hAllG : ∀ t ∈ SFY, x ∈ t := Set.mem_sInter.mp hxG.1
    refine ⟨?_, ?_⟩
    · rw [Set.mem_sInter]
      intro Z hZ
      obtain ⟨A, _hA, B, hB, rfl⟩ := hZ
      exact Set.mem_union_right _ (hAllG B hB)
    · obtain ⟨B, hB, hxB⟩ := Set.mem_sUnion.mp hxG.2
      exact Set.mem_sUnion.mpr
        ⟨A0 ∪ B, ⟨A0, hA0, B, hB, rfl⟩, Set.mem_union_right _ hxB⟩

/-- after Mizar SETFAM_1:30 — the `meet` of the pairwise-difference
family is included in the difference of the `meet`s. -/
theorem setfam_1_30_mmeet_pairDiff_subset {SFX SFY : Set (Set α)} :
    mmeet (PairDiff SFX SFY) ⊆ mmeet SFX \ mmeet SFY := by
  intro x hx
  have hAll : ∀ t ∈ PairDiff SFX SFY, x ∈ t :=
    Set.mem_sInter.mp hx.1
  obtain ⟨Z, hZ, hxZ⟩ := Set.mem_sUnion.mp hx.2
  obtain ⟨A0, hA0, B0, hB0, hZeq⟩ := hZ
  rw [hZeq] at hxZ
  have hxA0 : x ∈ A0 := ((Set.mem_sdiff _).mp hxZ).1
  have hxB0 : x ∉ B0 := ((Set.mem_sdiff _).mp hxZ).2
  refine (Set.mem_sdiff _).mpr ⟨?_, ?_⟩
  · show x ∈ ⋂₀ SFX ∩ ⋃₀ SFX
    refine ⟨?_, ?_⟩
    · rw [Set.mem_sInter]
      intro A hA
      exact ((Set.mem_sdiff _).mp
        (hAll (A \ B0) ⟨A, hA, B0, hB0, rfl⟩)).1
    · exact Set.mem_sUnion.mpr ⟨A0, hA0, hxA0⟩
  · intro hxG
    exact hxB0 (Set.mem_sInter.mp hxG.1 B0 hB0)

/-- after Mizar SETFAM_1:31 — families with the same members
are equal. (twin: `Set.ext` — exact) -/
theorem setfam_1_31_eq_of_forall_mem_iff {F G : Set (Set α)}
    (h : ∀ P : Set α, P ∈ F ↔ P ∈ G) : F = G :=
  Set.ext h

/-- after Mizar SETFAM_1:32 — the complement family of a
nonempty family is nonempty. -/
theorem setfam_1_32_complementFam_nonempty {F : Set (Set α)}
    (hne : F ≠ ∅) : ComplementFam F ≠ ∅ := by
  obtain ⟨Q, hQ⟩ := Set.nonempty_iff_ne_empty.mpr hne
  intro hcontra
  have hmem : Qᶜ ∈ ComplementFam F := ⟨Q, hQ, rfl⟩
  rw [hcontra] at hmem
  exact Set.notMem_empty _ hmem

/-- after Mizar SETFAM_1:33 — for a nonempty family over the
ambient set `D`, the complement of the union is the `meet` of
the complement family (`[#] D` flattened to `univ`). -/
theorem setfam_1_33_univ_diff_sUnion_complementFam {F : Set (Set α)}
    (hne : F ≠ ∅) :
    (Set.univ : Set α) \ ⋃₀ F = mmeet (ComplementFam F) := by
  obtain ⟨Q0, hQ0⟩ := Set.nonempty_iff_ne_empty.mpr hne
  ext x
  constructor
  · intro hx
    have hxU : x ∉ ⋃₀ F := ((Set.mem_sdiff _).mp hx).2
    have hAll : ∀ Q ∈ F, x ∉ Q := by
      intro Q hQ hxQ
      exact hxU (Set.mem_sUnion.mpr ⟨Q, hQ, hxQ⟩)
    show x ∈ ⋂₀ (ComplementFam F) ∩ ⋃₀ (ComplementFam F)
    refine ⟨?_, ?_⟩
    · rw [Set.mem_sInter]
      intro P hP
      obtain ⟨Q, hQ, rfl⟩ := hP
      exact hAll Q hQ
    · exact Set.mem_sUnion.mpr ⟨Q0ᶜ, ⟨Q0, hQ0, rfl⟩, hAll Q0 hQ0⟩
  · intro hx
    have hAll : ∀ P ∈ ComplementFam F, x ∈ P :=
      Set.mem_sInter.mp hx.1
    refine (Set.mem_sdiff _).mpr ⟨Set.mem_univ x, ?_⟩
    intro hU
    obtain ⟨Q, hQ, hxQ⟩ := Set.mem_sUnion.mp hU
    exact (hAll Qᶜ ⟨Q, hQ, rfl⟩) hxQ

/-- after Mizar SETFAM_1:34 — for a nonempty family over the
ambient set `D`, the union of the complement family is the
complement of the `meet` (`[#] D` flattened to `univ`). -/
theorem setfam_1_34_sUnion_complementFam {F : Set (Set α)}
    (hne : F ≠ ∅) :
    ⋃₀ (ComplementFam F) = (Set.univ : Set α) \ mmeet F := by
  obtain ⟨Q0, hQ0⟩ := Set.nonempty_iff_ne_empty.mpr hne
  ext x
  constructor
  · intro hx
    obtain ⟨P, hP, hxP⟩ := Set.mem_sUnion.mp hx
    obtain ⟨Q, hQ, rfl⟩ := hP
    refine (Set.mem_sdiff _).mpr ⟨Set.mem_univ x, ?_⟩
    intro hxM
    exact hxP (Set.mem_sInter.mp hxM.1 Q hQ)
  · intro hx
    have hxM : x ∉ mmeet F := ((Set.mem_sdiff _).mp hx).2
    by_cases hI : x ∈ ⋂₀ F
    · have hU : x ∉ ⋃₀ F := by
        intro hU
        exact hxM ⟨hI, hU⟩
      have hxQ0 : x ∉ Q0 := by
        intro h
        exact hU (Set.mem_sUnion.mpr ⟨Q0, hQ0, h⟩)
      exact Set.mem_sUnion.mpr ⟨Q0ᶜ, ⟨Q0, hQ0, rfl⟩, hxQ0⟩
    · have hex : ∃ Q ∈ F, x ∉ Q := by
        simp only [Set.mem_sInter, not_forall, not_imp] at hI
        obtain ⟨Q, hQ, hxQ⟩ := hI
        exact ⟨Q, hQ, hxQ⟩
      obtain ⟨Q, hQ, hxQ⟩ := hex
      exact Set.mem_sUnion.mpr ⟨Qᶜ, ⟨Q, hQ, rfl⟩, hxQ⟩

/-- after Mizar SETFAM_1:35 — a set belongs to the complement
family exactly when its complement is a member of the family
(the registry text's tick is on the left-hand `P`). -/
theorem setfam_1_35_compl_mem_complementFam_iff {F : Set (Set α)}
    {P : Set α} :
    Pᶜ ∈ ComplementFam F ↔ P ∈ F := by
  constructor
  · intro h
    obtain ⟨Q, hQ, hEq⟩ := h
    have hPQ : P = Q := by
      have h2 := congrArg (·ᶜ) hEq
      simp only [compl_compl] at h2
      exact h2
    rw [hPQ]
    exact hQ
  · intro h
    exact ⟨P, h, rfl⟩

/-- after Mizar SETFAM_1:36 — inclusion of complement families
gives inclusion of the families. -/
theorem setfam_1_36_subset_of_complementFam_subset {F G : Set (Set α)}
    (h : ComplementFam F ⊆ ComplementFam G) : F ⊆ G := by
  intro P hP
  have hmem : Pᶜ ∈ ComplementFam G := h ⟨P, hP, rfl⟩
  obtain ⟨Q, hQ, hEq⟩ := hmem
  have hPQ : P = Q := by
    have h2 := congrArg (·ᶜ) hEq
    simp only [compl_compl] at h2
    exact h2
  rw [hPQ]
  exact hQ

/-- after Mizar SETFAM_1:37 — the complement family of `F` is
included in `G` exactly when `F` is included in the complement
family of `G`. -/
theorem setfam_1_37_complementFam_subset_iff {F G : Set (Set α)} :
    ComplementFam F ⊆ G ↔ F ⊆ ComplementFam G := by
  constructor
  · intro h P hP
    have hmem : Pᶜ ∈ G := h ⟨P, hP, rfl⟩
    exact ⟨Pᶜ, hmem, (compl_compl P).symm⟩
  · intro h P hP
    obtain ⟨Q, hQ, hEq⟩ := hP
    obtain ⟨R, hR, hQeq⟩ := h hQ
    have hPR : P = R := by
      rw [hEq, hQeq]
      exact compl_compl R
    rw [hPR]
    exact hR

/-- after Mizar SETFAM_1:38 — families with equal complement
families are equal. -/
theorem setfam_1_38_eq_of_complementFam_eq {F G : Set (Set α)}
    (h : ComplementFam F = ComplementFam G) : F = G := by
  have h1 : ComplementFam F ⊆ ComplementFam G := by
    rw [h]
  have h2 : ComplementFam G ⊆ ComplementFam F := by
    rw [h]
  exact Set.Subset.antisymm
    (setfam_1_36_subset_of_complementFam_subset h1)
    (setfam_1_36_subset_of_complementFam_subset h2)

/-- after Mizar SETFAM_1:39 — the complement family of a union
is the union of the complement families. -/
theorem setfam_1_39_complementFam_union {F G : Set (Set α)} :
    ComplementFam (F ∪ G) = ComplementFam F ∪ ComplementFam G := by
  ext P
  constructor
  · intro h
    obtain ⟨Q, hQ, hEq⟩ := h
    rcases (Set.mem_union Q F G).mp hQ with hQF | hQG
    · exact Or.inl ⟨Q, hQF, hEq⟩
    · exact Or.inr ⟨Q, hQG, hEq⟩
  · intro h
    rcases h with ⟨Q, hQ, hEq⟩ | ⟨Q, hQ, hEq⟩
    · exact ⟨Q, Set.mem_union_left _ hQ, hEq⟩
    · exact ⟨Q, Set.mem_union_right _ hQ, hEq⟩

/-- after Mizar SETFAM_1:40 — the complement family of the
singleton ambient family `{X}` is the singleton empty family
(`X` flattened to `univ`, whose complement is `∅`). -/
theorem setfam_1_40_complementFam_singleton_univ {F : Set (Set α)}
    (hF : F = {(Set.univ : Set α)}) :
    ComplementFam F = {(∅ : Set α)} := by
  subst hF
  ext P
  constructor
  · intro h
    obtain ⟨Q, hQ, hEq⟩ := h
    rw [Set.mem_singleton_iff] at hQ
    rw [hQ, Set.compl_univ] at hEq
    rw [hEq]
    exact Set.mem_singleton ∅
  · intro h
    rw [Set.mem_singleton_iff] at h
    rw [h]
    exact ⟨Set.univ, Set.mem_singleton _, Set.compl_univ.symm⟩

/-- after Mizar SETFAM_1:41 — a member of a family whose union
is included in `Z` is itself included in `Z`. -/
theorem setfam_1_41_subset_of_sUnion_subset {Y : Set (Set α)}
    {X Z : Set α} (hsub : ⋃₀ Y ⊆ Z) (hX : X ∈ Y) : X ⊆ Z := by
  intro x hx
  exact hsub (Set.mem_sUnion.mpr ⟨X, hX, hx⟩)

/-- after Mizar SETFAM_1:42 — a set included in the union of
two families, and missing every member of the second, is
included in the union of the first (`misses` = `Disjoint`). -/
theorem setfam_1_42_subset_sUnion_of_misses {A B : Set (Set α)}
    {X : Set α} (hsub : X ⊆ ⋃₀ (A ∪ B))
    (hB : ∀ Y ∈ B, Disjoint Y X) : X ⊆ ⋃₀ A := by
  intro x hx
  obtain ⟨T, hT, hxT⟩ := Set.mem_sUnion.mp (hsub hx)
  rcases (Set.mem_union T A B).mp hT with hTA | hTB
  · exact Set.mem_sUnion.mpr ⟨T, hTA, hxT⟩
  · have hdis : ∀ a : α, a ∈ T → a ∉ X := Set.disjoint_left.mp (hB T hTB)
    exact absurd hx (hdis x hxT)

/-- after Mizar SETFAM_1:43 — membership in `Intersect R`:
a point lies in every member of `R`. `Intersect` is restated
as `⋂₀` (see header): Mizar's hypothesis `x in X` is vacuous
in the flattened idiom (`X` = `univ`), and `Intersect` of the
empty family is the ambient set, matching `⋂₀ ∅ = univ` —
this is the one place the `mmeet` correction must NOT be
applied. (twin: `Set.mem_sInter` — exact) -/
theorem setfam_1_43_mem_sInter_iff {R : Set (Set α)} {x : α} :
    x ∈ ⋂₀ R ↔ ∀ Y ∈ R, x ∈ Y :=
  Set.mem_sInter

/-- after Mizar SETFAM_1:44 — `Intersect` is antitone in the
family. -/
theorem setfam_1_44_sInter_antitone {H J : Set (Set α)}
    (h : H ⊆ J) : ⋂₀ J ⊆ ⋂₀ H := by
  intro x hx
  rw [Set.mem_sInter] at hx ⊢
  intro T hT
  exact hx T (h hT)

/-- after Mizar SETFAM_1:45 — a family is a cover of the
ambient set exactly when its union is the whole set. -/
theorem setfam_1_45_isCover_iff {F : Set (Set α)} :
    IsCover F ↔ ⋃₀ F = Set.univ := by
  constructor
  · intro h
    exact Set.Subset.antisymm (Set.subset_univ _) h
  · intro h
    show (Set.univ : Set α) ⊆ ⋃₀ F
    rw [h]

/-- after Mizar SETFAM_1:46 — the singleton empty family is
a subset-family of every set. -/
theorem setfam_1_46_singleton_empty_isSubsetFamilyOf
    (D : Set α) : IsSubsetFamilyOf D ({(∅ : Set α)} : Set (Set α)) := by
  intro Y hY
  rw [Set.mem_singleton_iff] at hY
  rw [hY]
  exact Set.empty_subset D

/-- after Mizar SETFAM_1:47 — a subfamily of a
`with_proper_subsets` family is `with_proper_subsets`. -/
theorem setfam_1_47_withProperSubsets_of_subset {F G : Set (Set α)}
    (hF : WithProperSubsets F) (hsub : G ⊆ F) :
    WithProperSubsets G := by
  intro Y hY
  exact hF Y (hsub hY)

/-- after Mizar SETFAM_1:48 — the union of two
`with_proper_subsets` families over a nonempty ambient set
is `with_proper_subsets`. (Mizar's nonempty-set typing of
the ambient is the instance argument; it is not spent in
the flattened proof.) -/
theorem setfam_1_48_withProperSubsets_union [Nonempty α]
    {A B : Set (Set α)} (hA : WithProperSubsets A)
    (hB : WithProperSubsets B) :
    WithProperSubsets (A ∪ B) := by
  intro Y hY
  rcases (Set.mem_union Y A B).mp hY with hYA | hYB
  · exact hA Y hYA
  · exact hB Y hYB

/-- after Mizar SETFAM_1:49 — in a nonempty set not equal to
a singleton `{b}`, some member differs from `b`. -/
theorem setfam_1_49_exists_mem_ne_of_ne_singleton {A : Set α}
    {b : α} (hA : A.Nonempty) (hne : A ≠ {b}) :
    ∃ a ∈ A, a ≠ b := by
  obtain ⟨a0, ha0⟩ := hA
  by_cases hab : ∃ a ∈ A, a ≠ b
  · exact hab
  · exfalso
    apply hne
    have hall : ∀ a ∈ A, a = b := by
      intro a ha
      by_contra hne2
      exact hab ⟨a, ha, hne2⟩
    apply Set.Subset.antisymm
    · intro x hx
      rw [Set.mem_singleton_iff]
      exact hall x hx
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx, ← hall a0 ha0]
      exact ha0

/-- after Mizar SUBSET_1:31 — if pointwise non-membership in
`A` agrees with membership in `B`, then `A` is the complement
of `B` (the registry line's closing tick is on `B`). -/
theorem subset_1_31_eq_compl_of_not_mem_iff {A B : Set α}
    (h : ∀ x : α, (¬ x ∈ A) ↔ x ∈ B) : A = Bᶜ := by
  ext x
  simp only [Set.mem_compl_iff]
  have hx := h x
  tauto

/-- after Mizar SUBSET_1:32 — if pointwise membership in `A`
and in `B` always disagree, then `A` is the complement
of `B` (the registry line's closing tick is on `B`). -/
theorem subset_1_32_eq_compl_of_not_mem_iff_iff {A B : Set α}
    (h : ∀ x : α, ¬ (x ∈ A ↔ x ∈ B)) : A = Bᶜ := by
  ext x
  simp only [Set.mem_compl_iff]
  have hx := h x
  tauto

/-- after Mizar SUBSET_1:33 — a singleton of a point of `X`
is a subset of `X`. The point is an `Element of X` in Mizar;
the element discipline is the membership hypothesis (which
also absorbs Mizar's `X ≠ ∅` side hypothesis). -/
theorem subset_1_33_singleton_subset {X : Set α} {x1 : α}
    (h1 : x1 ∈ X) : ({x1} : Set α) ⊆ X :=
  Set.singleton_subset_iff.mpr h1

/-- after Mizar SUBSET_1:34 — a two-point set of points of
`X` is a subset of `X` (`Element of X` as membership
hypotheses, as in SUBSET_1:33). -/
theorem subset_1_34_pair_subset {X : Set α} {x1 x2 : α}
    (h1 : x1 ∈ X) (h2 : x2 ∈ X) : ({x1, x2} : Set α) ⊆ X := by
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact h1
  · exact h2

/-- after Mizar SUBSET_1:35 — a three-point set of points of
`X` is a subset of `X` (`Element of X` as membership
hypotheses, as in SUBSET_1:33). -/
theorem subset_1_35_triple_subset {X : Set α} {x1 x2 x3 : α}
    (h1 : x1 ∈ X) (h2 : x2 ∈ X) (h3 : x3 ∈ X) :
    ({x1, x2, x3} : Set α) ⊆ X := by
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

/-- after Mizar SUBSET_1:36 — a four-point set of points of
`X` is a subset of `X` (`Element of X` as membership
hypotheses, as in SUBSET_1:33). -/
theorem subset_1_36_quad_subset {X : Set α} {x1 x2 x3 x4 : α}
    (h1 : x1 ∈ X) (h2 : x2 ∈ X) (h3 : x3 ∈ X) (h4 : x4 ∈ X) :
    ({x1, x2, x3, x4} : Set α) ⊆ X := by
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- after Mizar SUBSET_1:37 — a five-point set of points of
`X` is a subset of `X` (`Element of X` as membership
hypotheses, as in SUBSET_1:33). -/
theorem subset_1_37_five_subset {X : Set α} {x1 x2 x3 x4 x5 : α}
    (h1 : x1 ∈ X) (h2 : x2 ∈ X) (h3 : x3 ∈ X) (h4 : x4 ∈ X)
    (h5 : x5 ∈ X) :
    ({x1, x2, x3, x4, x5} : Set α) ⊆ X := by
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

/-- after Mizar SUBSET_1:38 — a six-point set of points of
`X` is a subset of `X` (`Element of X` as membership
hypotheses, as in SUBSET_1:33). -/
theorem subset_1_38_six_subset {X : Set α}
    {x1 x2 x3 x4 x5 x6 : α}
    (h1 : x1 ∈ X) (h2 : x2 ∈ X) (h3 : x3 ∈ X) (h4 : x4 ∈ X)
    (h5 : x5 ∈ X) (h6 : x6 ∈ X) :
    ({x1, x2, x3, x4, x5, x6} : Set α) ⊆ X := by
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

/-- after Mizar SUBSET_1:39 — a seven-point set of points of
`X` is a subset of `X` (`Element of X` as membership
hypotheses, as in SUBSET_1:33). -/
theorem subset_1_39_seven_subset {X : Set α}
    {x1 x2 x3 x4 x5 x6 x7 : α}
    (h1 : x1 ∈ X) (h2 : x2 ∈ X) (h3 : x3 ∈ X) (h4 : x4 ∈ X)
    (h5 : x5 ∈ X) (h6 : x6 ∈ X) (h7 : x7 ∈ X) :
    ({x1, x2, x3, x4, x5, x6, x7} : Set α) ⊆ X := by
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

/-- after Mizar SUBSET_1:40 — an eight-point set of points of
`X` is a subset of `X` (`Element of X` as membership
hypotheses, as in SUBSET_1:33). -/
theorem subset_1_40_eight_subset {X : Set α}
    {x1 x2 x3 x4 x5 x6 x7 x8 : α}
    (h1 : x1 ∈ X) (h2 : x2 ∈ X) (h3 : x3 ∈ X) (h4 : x4 ∈ X)
    (h5 : x5 ∈ X) (h6 : x6 ∈ X) (h7 : x7 ∈ X) (h8 : x8 ∈ X) :
    ({x1, x2, x3, x4, x5, x6, x7, x8} : Set α) ⊆ X := by
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8

/-- after Mizar SUBSET_1:41 — a singleton of a point of `X`
is a subset of `X`. (twin: SUBSET_1:33 above, restated
without the absorbed nonemptiness side condition) -/
theorem subset_1_41_singleton_subset {X : Set α} {x : α}
    (hx : x ∈ X) : ({x} : Set α) ⊆ X :=
  Set.singleton_subset_iff.mpr hx

end ThetLogos.MizarPilot2.B2
