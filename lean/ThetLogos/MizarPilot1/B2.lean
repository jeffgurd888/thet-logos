import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Tauto

/-!
# Mizar Pilot 1 — Brick B2: SETFAM_1 / SUBSET_1 families and subsets

MZ pilot wave, tranche 1, brick B2 — after Zero's 2026-11-09 pilot call.
Source working list: the Mizar registry (SETFAM_1 items 1–20 and
SUBSET_1 items 1–20 drawn for this brick: 40 items).

**NO CLAIM; dials 0/4.** This is a re-proof exercise against a foreign
registry, at restatement grade only: nothing here is counted toward the
corpus census, and no dial moves on the strength of this file.

Protocol: every item restated + proved; twin verdicts are twin-notes,
never skips. An item that resists is marked `STUCK` in place, never
silently dropped — all 40 identifiers appear below.

Priority credit: Mizar proved it first, in its system ("after Mizar" =
Mizar proved it first); we re-prove our restatement in ours.

## Restatement idiom

Mizar sets are sets in a universe — restated here over `Set α` for an
arbitrary type `α`. A Mizar family of sets is a `Set (Set α)`.
Mizar `\/` is `∪`, `/\` is `∩`, `\` is `\` (set difference),
`\+\` is symmetric difference (spelled out as `(X \ Y) ∪ (Y \ X)`,
as in brick B1), `c=` is `⊆`, `misses` is `Disjoint`, and
`union F` is `⋃₀ F`.

Two idiom choices, flagged:

* Mizar `meet F` is **not** Mathlib `⋂₀ F`: Mizar pins
  `meet ∅ = ∅` (SETFAM_1:1), while `⋂₀ ∅ = univ` in Mathlib.
  We therefore use the local `mmeet F := ⋂₀ F ∩ ⋃₀ F`, which agrees
  with `⋂₀ F` on every nonempty family and gives `∅` on the empty
  family — exactly Mizar's convention. The nonemptiness hypotheses
  in SETFAM_1:5, 6, 9 are the visible trace of this divergence.
* `is_finer_than` / `is_coarser_than` (SETFAM_1:12–20) are local
  definitions, restating Mizar's: `F` is finer than `G` when every
  member of `F` is included in some member of `G`; `F` is coarser
  than `G` when every member of `F` includes some member of `G`.
  Mizar `UNION(F, G)` (SETFAM_1:20) is the local `PairUnion`:
  the family of pairwise unions.

SUBSET_1 flattening: Mizar's `A being Subset of X` / `Element of E`
discipline is flattened — subsets are plain `A B C : Set α`, points
are plain `x : α`, `[#] E` (the full subset) is `Set.univ`, and
`A`` (Mizar's complement tick) is `Aᶜ`. In SUBSET_1:10 the registry
text lost the complement tick; it is restored as `A ∪ Aᶜ = univ`,
the only reading consistent with the surrounding items.
-/

namespace ThetLogos.MizarPilot1.B2

variable {α : Type*}

/-- Mizar `meet F`, with Mizar's convention `meet ∅ = ∅`
(unlike Mathlib's `⋂₀ ∅ = univ`). -/
def mmeet (F : Set (Set α)) : Set α := ⋂₀ F ∩ ⋃₀ F

/-- Mizar `F is_finer_than G`: every member of `F` is included in
some member of `G`. -/
def IsFinerThan (F G : Set (Set α)) : Prop :=
  ∀ X ∈ F, ∃ Y ∈ G, X ⊆ Y

/-- Mizar `F is_coarser_than G`: every member of `F` includes
some member of `G`. -/
def IsCoarserThan (F G : Set (Set α)) : Prop :=
  ∀ X ∈ F, ∃ Y ∈ G, Y ⊆ X

/-- Mizar `UNION(F, G)`: the family of pairwise unions. -/
def PairUnion (F G : Set (Set α)) : Set (Set α) :=
  { Z | ∃ X ∈ F, ∃ Y ∈ G, Z = X ∪ Y }

/-- Auxiliary: on a nonempty family, `mmeet` is Mathlib's `⋂₀`. -/
theorem mmeet_eq_sInter_of_nonempty {F : Set (Set α)} (hF : F.Nonempty) :
    mmeet F = ⋂₀ F := by
  apply Set.Subset.antisymm Set.inter_subset_left
  intro x hx
  obtain ⟨T, hT⟩ := hF
  have hxT : x ∈ T := Set.mem_sInter.mp hx T hT
  exact ⟨hx, Set.mem_sUnion.mpr ⟨T, hT, hxT⟩⟩

/-- after Mizar SETFAM_1:1 — `meet {}` is empty (Mizar convention;
Mathlib's `⋂₀ ∅` is `univ`, hence the local `mmeet`). -/
theorem setfam_1_1_meet_empty : mmeet (∅ : Set (Set α)) = ∅ := by
  unfold mmeet
  simp

/-- after Mizar SETFAM_1:2 — `meet X` is included in `union X`. -/
theorem setfam_1_2_meet_subset_sUnion {X : Set (Set α)} :
    mmeet X ⊆ ⋃₀ X :=
  Set.inter_subset_right

/-- after Mizar SETFAM_1:3 — `meet X` is included in every member
of `X`. -/
theorem setfam_1_3_meet_subset_of_mem {X : Set (Set α)} {Z : Set α}
    (hZ : Z ∈ X) : mmeet X ⊆ Z := by
  intro x hx
  have hAll : ∀ t ∈ X, x ∈ t := Set.mem_sInter.mp hx.1
  exact hAll Z hZ

/-- after Mizar SETFAM_1:4 — if the empty set is a member of `X`,
then `meet X` is empty. -/
theorem setfam_1_4_meet_eq_empty_of_empty_mem {X : Set (Set α)}
    (h : (∅ : Set α) ∈ X) : mmeet X = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro x hx
  have hAll : ∀ t ∈ X, x ∈ t := Set.mem_sInter.mp hx.1
  exact Set.notMem_empty x (hAll ∅ h)

/-- after Mizar SETFAM_1:5 — a set included in every member of a
nonempty family is included in its `meet`. -/
theorem setfam_1_5_subset_meet_of_forall_subset {X : Set (Set α)}
    {Z : Set α} (hne : X ≠ ∅) (hZ : ∀ Z1 ∈ X, Z ⊆ Z1) :
    Z ⊆ mmeet X := by
  intro x hx
  obtain ⟨T, hT⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hI : x ∈ ⋂₀ X := by
    rw [Set.mem_sInter]
    intro T hT
    exact hZ T hT hx
  have hU : x ∈ ⋃₀ X := Set.mem_sUnion.mpr ⟨T, hT, hZ T hT hx⟩
  show x ∈ ⋂₀ X ∩ ⋃₀ X
  exact ⟨hI, hU⟩

/-- after Mizar SETFAM_1:6 — `meet` is antitone in the family,
for a nonempty smaller family. -/
theorem setfam_1_6_meet_mono_of_subset {X Y : Set (Set α)}
    (hne : X ≠ ∅) (hsub : X ⊆ Y) : mmeet Y ⊆ mmeet X := by
  intro x hx
  have hAll : ∀ t ∈ Y, x ∈ t := Set.mem_sInter.mp hx.1
  obtain ⟨T, hT⟩ := Set.nonempty_iff_ne_empty.mpr hne
  show x ∈ ⋂₀ X ∩ ⋃₀ X
  refine ⟨?_, ?_⟩
  · rw [Set.mem_sInter]
    intro S hS
    exact hAll S (hsub hS)
  · exact Set.mem_sUnion.mpr ⟨T, hT, hAll T (hsub hT)⟩

/-- after Mizar SETFAM_1:7 — if a member of the family is included
in `Z`, so is the family's `meet`. -/
theorem setfam_1_7_meet_subset_of_mem_subset {Y : Set (Set α)}
    {X Z : Set α} (hX : X ∈ Y) (hsub : X ⊆ Z) : mmeet Y ⊆ Z := by
  intro x hx
  have hAll : ∀ t ∈ Y, x ∈ t := Set.mem_sInter.mp hx.1
  exact hsub (hAll X hX)

/-- after Mizar SETFAM_1:8 — if a member of the family misses `Z`,
so does the family's `meet`. -/
theorem setfam_1_8_meet_disjoint_of_mem_disjoint {Y : Set (Set α)}
    {X Z : Set α} (hX : X ∈ Y) (hdisj : Disjoint X Z) :
    Disjoint (mmeet Y) Z := by
  rw [Set.disjoint_left] at hdisj ⊢
  intro a ha haZ
  have hAll : ∀ t ∈ Y, a ∈ t := Set.mem_sInter.mp ha.1
  exact hdisj (hAll X hX) haZ

/-- after Mizar SETFAM_1:9 — `meet` of a union of two nonempty
families is the intersection of the `meet`s. -/
theorem setfam_1_9_meet_union {X Y : Set (Set α)}
    (hX : X.Nonempty) (hY : Y.Nonempty) :
    mmeet (X ∪ Y) = mmeet X ∩ mmeet Y := by
  rw [mmeet_eq_sInter_of_nonempty (hX.mono Set.subset_union_left),
    mmeet_eq_sInter_of_nonempty hX, mmeet_eq_sInter_of_nonempty hY,
    Set.sInter_union]

/-- after Mizar SETFAM_1:10 — `meet` of a singleton family is its
member. (twin: `Set.sInter_singleton` / `Set.sUnion_singleton`) -/
theorem setfam_1_10_meet_singleton {X : Set α} : mmeet {X} = X := by
  unfold mmeet
  rw [Set.sInter_singleton, Set.sUnion_singleton, Set.inter_self]

/-- after Mizar SETFAM_1:11 — `meet` of a two-member family is the
intersection of the members. -/
theorem setfam_1_11_meet_pair {X Y : Set α} :
    mmeet {X, Y} = X ∩ Y := by
  unfold mmeet
  rw [Set.sInter_pair, Set.sUnion_pair]
  exact Set.inter_eq_left.mpr
    (Set.Subset.trans Set.inter_subset_left Set.subset_union_left)

/-- after Mizar SETFAM_1:12 — an included family is finer. -/
theorem setfam_1_12_finer_of_subset {SFX SFY : Set (Set α)}
    (h : SFX ⊆ SFY) : IsFinerThan SFX SFY := by
  intro X hX
  exact ⟨X, h hX, Set.Subset.refl X⟩

/-- after Mizar SETFAM_1:13 — a finer family has a smaller union. -/
theorem setfam_1_13_sUnion_subset_of_finer {SFX SFY : Set (Set α)}
    (h : IsFinerThan SFX SFY) : ⋃₀ SFX ⊆ ⋃₀ SFY := by
  intro x hx
  obtain ⟨t, htF, hxt⟩ := Set.mem_sUnion.mp hx
  obtain ⟨u, huG, htu⟩ := h t htF
  exact Set.mem_sUnion.mpr ⟨u, huG, htu hxt⟩

/-- after Mizar SETFAM_1:14 — if `SFY` is coarser than `SFX`
(and nonempty), then `meet SFX` is included in `meet SFY`. -/
theorem setfam_1_14_meet_subset_of_coarser {SFX SFY : Set (Set α)}
    (hne : SFY ≠ ∅) (h : IsCoarserThan SFY SFX) :
    mmeet SFX ⊆ mmeet SFY := by
  intro x hx
  have hAll : ∀ t ∈ SFX, x ∈ t := Set.mem_sInter.mp hx.1
  obtain ⟨T0, hT0⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨S0, hS0, hS0T0⟩ := h T0 hT0
  show x ∈ ⋂₀ SFY ∩ ⋃₀ SFY
  refine ⟨?_, ?_⟩
  · rw [Set.mem_sInter]
    intro T hT
    obtain ⟨S, hS, hST⟩ := h T hT
    exact hST (hAll S hS)
  · exact Set.mem_sUnion.mpr ⟨T0, hT0, hS0T0 (hAll S0 hS0)⟩

/-- after Mizar SETFAM_1:15 — the empty family is finer than
every family. -/
theorem setfam_1_15_empty_finer {SFX : Set (Set α)} :
    IsFinerThan (∅ : Set (Set α)) SFX := by
  intro X hX
  exact (Set.notMem_empty X hX).elim

/-- after Mizar SETFAM_1:16 — a family finer than the empty
family is empty. -/
theorem setfam_1_16_eq_empty_of_finer_empty {SFX : Set (Set α)}
    (h : IsFinerThan SFX (∅ : Set (Set α))) : SFX = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro X hX
  obtain ⟨Y, hY, -⟩ := h X hX
  exact Set.notMem_empty Y hY

/-- after Mizar SETFAM_1:17 — `is_finer_than` is transitive. -/
theorem setfam_1_17_finer_trans {SFX SFY SFZ : Set (Set α)}
    (hFG : IsFinerThan SFX SFY) (hGH : IsFinerThan SFY SFZ) :
    IsFinerThan SFX SFZ := by
  intro X hX
  obtain ⟨Y, hY, hXY⟩ := hFG X hX
  obtain ⟨Z, hZ, hYZ⟩ := hGH Y hY
  exact ⟨Z, hZ, Set.Subset.trans hXY hYZ⟩

/-- after Mizar SETFAM_1:18 — a family finer than a singleton
has all its members included in the singleton's member. -/
theorem setfam_1_18_finer_singleton {SFX : Set (Set α)} {Y : Set α}
    (h : IsFinerThan SFX {Y}) : ∀ X ∈ SFX, X ⊆ Y := by
  intro X hX
  obtain ⟨Z, hZ, hXZ⟩ := h X hX
  rw [Set.mem_singleton_iff] at hZ
  rwa [hZ] at hXZ

/-- after Mizar SETFAM_1:19 — a family finer than a pair has all
its members included in one of the two members. -/
theorem setfam_1_19_finer_pair {SFX : Set (Set α)} {X Y : Set α}
    (h : IsFinerThan SFX {X, Y}) :
    ∀ Z ∈ SFX, Z ⊆ X ∨ Z ⊆ Y := by
  intro Z hZ
  obtain ⟨W, hW, hZW⟩ := h Z hZ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hW
  rcases hW with rfl | rfl
  · exact Or.inl hZW
  · exact Or.inr hZW

/-- after Mizar SETFAM_1:20 — every family is finer than its
pairwise-union family with itself. -/
theorem setfam_1_20_finer_pairUnion_self {SFX : Set (Set α)} :
    IsFinerThan SFX (PairUnion SFX SFX) := by
  intro X hX
  exact ⟨X ∪ X, ⟨X, hX, X, hX, rfl⟩, Set.subset_union_left⟩

/-- after Mizar SUBSET_1:1 — the empty set is a subset of every
set. (twin: `Set.empty_subset` — exact) -/
theorem subset_1_1_empty_subset {X : Set α} : (∅ : Set α) ⊆ X :=
  Set.empty_subset X

/-- after Mizar SUBSET_1:2 — pointwise inclusion of points
gives inclusion of subsets (ambient `E` flattened away). -/
theorem subset_1_2_subset_of_forall_mem {A B : Set α}
    (h : ∀ x : α, x ∈ A → x ∈ B) : A ⊆ B := by
  intro x hx
  exact h x hx

/-- after Mizar SUBSET_1:3 — pointwise agreement of membership
gives equality of subsets. (twin: `Set.ext` — near-exact) -/
theorem subset_1_3_eq_of_forall_mem_iff {A B : Set α}
    (h : ∀ x : α, x ∈ A ↔ x ∈ B) : A = B :=
  Set.ext h

/-- after Mizar SUBSET_1:4 — a nonempty subset has a point. -/
theorem subset_1_4_exists_mem_of_ne_empty {A : Set α}
    (h : A ≠ ∅) : ∃ x : α, x ∈ A :=
  Set.nonempty_iff_ne_empty.mpr h

/-- after Mizar SUBSET_1:5 — pointwise "in `B` or in `C`"
characterises the union. -/
theorem subset_1_5_eq_union_of_forall {A B C : Set α}
    (h : ∀ x : α, x ∈ A ↔ x ∈ B ∨ x ∈ C) : A = B ∪ C := by
  ext x
  simp only [Set.mem_union]
  exact h x

/-- after Mizar SUBSET_1:6 — pointwise "in `B` and in `C`"
characterises the intersection. -/
theorem subset_1_6_eq_inter_of_forall {A B C : Set α}
    (h : ∀ x : α, x ∈ A ↔ x ∈ B ∧ x ∈ C) : A = B ∩ C := by
  ext x
  simp only [Set.mem_inter_iff]
  exact h x

/-- after Mizar SUBSET_1:7 — pointwise "in `B` and not in `C`"
characterises the difference. -/
theorem subset_1_7_eq_diff_of_forall {A B C : Set α}
    (h : ∀ x : α, x ∈ A ↔ x ∈ B ∧ x ∉ C) : A = B \ C := by
  ext x
  simp only [Set.mem_diff]
  exact h x

/-- after Mizar SUBSET_1:8 — pointwise disagreement of `B` and
`C` characterises the symmetric difference, spelled out as
`(B \ C) ∪ (C \ B)` as in brick B1. -/
theorem subset_1_8_eq_symmDiff_of_forall {A B C : Set α}
    (h : ∀ x : α, x ∈ A ↔ ¬ (x ∈ B ↔ x ∈ C)) :
    A = (B \ C) ∪ (C \ B) := by
  ext x
  simp only [Set.mem_union, Set.mem_diff]
  have hx := h x
  tauto

/-- after Mizar SUBSET_1:9 — the full subset `[#] E` is the
complement of the empty subset. (twin: `Set.compl_empty`) -/
theorem subset_1_9_univ_eq_compl_empty :
    (Set.univ : Set α) = (∅ : Set α)ᶜ :=
  Set.compl_empty.symm

/-- after Mizar SUBSET_1:10 — a set together with its complement
is the full set (complement tick restored; see header).
(twin: `Set.union_compl_self`) -/
theorem subset_1_10_union_compl_self {A : Set α} :
    A ∪ Aᶜ = Set.univ :=
  Set.union_compl_self A

/-- after Mizar SUBSET_1:11 — union with the full set is the
full set. -/
theorem subset_1_11_union_univ {A : Set α} :
    A ∪ Set.univ = Set.univ := by
  simp

/-- after Mizar SUBSET_1:12 — inclusion is complement-reversing,
as an iff. (twin: `Set.compl_subset_compl_iff_subset`) -/
theorem subset_1_12_subset_iff_compl_subset {A B : Set α} :
    A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  constructor
  · intro h x hx hxA
    exact hx (h hxA)
  · intro h x hx
    by_contra hxB
    exact h hxB hx

/-- after Mizar SUBSET_1:13 — difference is intersection with
the complement. (twin: `Set.diff_eq` — exact) -/
theorem subset_1_13_diff_eq_inter_compl {A B : Set α} :
    A \ B = A ∩ Bᶜ :=
  Set.diff_eq A B

/-- after Mizar SUBSET_1:14 — complement of a difference.
(twin: `Set.compl_diff`) -/
theorem subset_1_14_compl_diff {A B : Set α} :
    (A \ B)ᶜ = Aᶜ ∪ B := by
  rw [Set.compl_sdiff, Set.union_comm]

/-- after Mizar SUBSET_1:15 — complement of the symmetric
difference (spelled out as in brick B1) is agreement:
`(A ∩ B) ∪ (Aᶜ ∩ Bᶜ)`. -/
theorem subset_1_15_compl_symmDiff {A B : Set α} :
    ((A \ B) ∪ (B \ A))ᶜ = (A ∩ B) ∪ (Aᶜ ∩ Bᶜ) := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_inter_iff,
    Set.mem_diff]
  tauto

/-- after Mizar SUBSET_1:16 — if `A` is included in the
complement of `B`, then `B` is included in the complement
of `A`. -/
theorem subset_1_16_subset_compl_swap {A B : Set α}
    (h : A ⊆ Bᶜ) : B ⊆ Aᶜ := by
  intro x hxB
  simp only [Set.mem_compl_iff]
  intro hxA
  have hxBc : x ∉ B := h hxA
  exact hxBc hxB

/-- after Mizar SUBSET_1:17 — if the complement of `A` is
included in `B`, then the complement of `B` is included
in `A`. -/
theorem subset_1_17_compl_subset_swap {A B : Set α}
    (h : Aᶜ ⊆ B) : Bᶜ ⊆ A := by
  intro x hx
  by_contra hxA
  exact hx (h hxA)

/-- after Mizar SUBSET_1:18 — a set included in its own
complement is empty, and conversely. -/
theorem subset_1_18_subset_compl_iff_empty {A : Set α} :
    A ⊆ Aᶜ ↔ A = ∅ := by
  constructor
  · intro h
    apply Set.eq_empty_of_forall_notMem
    intro x hxA
    exact (h hxA) hxA
  · intro h
    rw [h]
    exact Set.empty_subset _

/-- after Mizar SUBSET_1:19 — a set including its own
complement is the full set, and conversely. -/
theorem subset_1_19_compl_subset_iff_univ {A : Set α} :
    Aᶜ ⊆ A ↔ A = Set.univ := by
  constructor
  · intro h
    apply Set.eq_univ_of_forall
    intro x
    by_contra hxA
    exact hxA (h hxA)
  · intro h
    rw [h, Set.compl_univ]
    exact Set.empty_subset _

/-- after Mizar SUBSET_1:20 — a set included in both a set and
its complement is empty. -/
theorem subset_1_20_eq_empty_of_subset_and_compl {X A : Set α}
    (hA : X ⊆ A) (hAc : X ⊆ Aᶜ) : X = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro x hxX
  exact (hAc hxX) (hA hxX)

end ThetLogos.MizarPilot1.B2
