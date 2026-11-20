/-
# OrbifoldGapZF8 — ZF-8a: the quotient arithmetic at the headline seat (2, 0)

**Scope: ~/workspace/your_files/gravity-orb-z3-fold-scope-2026-11-18.md,
§2 Leg C, brick ZF-8 (first half). Commissioned by Zero, 2026-11-18
18:07 EST ("Fire all three legs"). NO CLAIM. Dials 0/4.
Dial-ineligible.**

The quotient at `(2, 0)` has exactly three vertices — the centre
orbit and the two rim orbits — and this brick banks their complete
arithmetic: exhaustion, distinctness, the universe as a three-element
finset, and the nine values of the averaged quotient weights `quotW`
(the totals of ZF-1 made concrete: centre–rim `3` against rim–centre
`1` is the disclosed asymmetry, in numbers). The floor itself and the
exhibited `5`-eigenpair are ZF-8b.

Kills watched: K-ORB-GAPMAP-FLOOR — the row values below are what
the floor stands on; had any total come back different from the
scoping numerics, the floor would be re-scoped before any decision
is claimed. The arithmetic below is the numerics, checked.
-/

import ThetLogos.OrbifoldGapZF7

namespace ThetLogos
namespace OrbifoldGapPin

/-- Every quotient vertex at `(2, 0)` is the centre orbit or one of
the two rim orbits: the seven nodes fall into three orbits. -/
theorem quot_exhaustion (o : SliceQuot 2 0) :
    o = Quotient.mk (orbitSetoid 2 0) centerNode
      ∨ o = Quotient.mk (orbitSetoid 2 0) rimANode
      ∨ o = Quotient.mk (orbitSetoid 2 0) rimBNode := by
  obtain ⟨p, rfl⟩ := Quotient.exists_rep o
  have hp : p.1 ∈ ({(0, 0, 0), (1, -1, 0), (0, 1, -1), (-1, 0, 1),
      (-1, 1, 0), (1, 0, -1), (0, -1, 1)} : Finset (ℤ × ℤ × ℤ)) := by
    rw [← layerFinset_two_zero]; exact p.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with h | h | h | h | h | h | h
  · have hpe : p = centerNode := Subtype.ext h
    rw [hpe]
    exact Or.inl rfl
  · have hpe : p = rimANode := Subtype.ext h
    rw [hpe]
    exact Or.inr (Or.inl rfl)
  · have hpe : p = cycSlice 2 0 rimANode := Subtype.ext h
    rw [hpe]
    exact Or.inr (Or.inl (Quotient.eq.mpr
      (orbitRel_symm (show orbitRel 2 0 rimANode (cycSlice 2 0 rimANode)
        from Or.inr (Or.inl rfl)))))
  · have hpe : p = cycSlice 2 0 (cycSlice 2 0 rimANode) := Subtype.ext h
    rw [hpe]
    exact Or.inr (Or.inl (Quotient.eq.mpr
      (orbitRel_symm (show orbitRel 2 0 rimANode
        (cycSlice 2 0 (cycSlice 2 0 rimANode)) from Or.inr (Or.inr rfl)))))
  · have hpe : p = rimBNode := Subtype.ext h
    rw [hpe]
    exact Or.inr (Or.inr rfl)
  · have hpe : p = cycSlice 2 0 (cycSlice 2 0 rimBNode) := Subtype.ext h
    rw [hpe]
    exact Or.inr (Or.inr (Quotient.eq.mpr
      (orbitRel_symm (show orbitRel 2 0 rimBNode
        (cycSlice 2 0 (cycSlice 2 0 rimBNode)) from Or.inr (Or.inr rfl)))))
  · have hpe : p = cycSlice 2 0 rimBNode := Subtype.ext h
    rw [hpe]
    exact Or.inr (Or.inr (Quotient.eq.mpr
      (orbitRel_symm (show orbitRel 2 0 rimBNode (cycSlice 2 0 rimBNode)
        from Or.inr (Or.inl rfl)))))

/-- The three quotient vertices at `(2, 0)` are pairwise distinct:
the centre orbit is told from the rim orbits by its fibre size
(`1` against `3`), and the two rim orbits are told apart by
membership — `rimBNode` is not in the first rim orbit. -/
theorem quot_distinct :
    Quotient.mk (orbitSetoid 2 0) centerNode
      ≠ Quotient.mk (orbitSetoid 2 0) rimANode
    ∧ Quotient.mk (orbitSetoid 2 0) centerNode
      ≠ Quotient.mk (orbitSetoid 2 0) rimBNode
    ∧ Quotient.mk (orbitSetoid 2 0) rimANode
      ≠ Quotient.mk (orbitSetoid 2 0) rimBNode := by
  refine ⟨?_, ?_, ?_⟩
  · intro hcon
    have hcard := congrArg (fun o => (fiber o).card) hcon
    rw [fiber_mk_eq_orbitFinset, fiber_mk_eq_orbitFinset,
      orbit_card_center, orbit_card_rimA] at hcard
    exact (by decide : (1 : ℕ) ≠ 3) hcard
  · intro hcon
    have hcard := congrArg (fun o => (fiber o).card) hcon
    rw [fiber_mk_eq_orbitFinset, fiber_mk_eq_orbitFinset,
      orbit_card_center, orbit_card_rimB] at hcard
    exact (by decide : (1 : ℕ) ≠ 3) hcard
  · intro hcon
    have hmem : rimBNode ∈ fiber (Quotient.mk (orbitSetoid 2 0) rimBNode) := by
      simp [fiber]
    rw [← hcon, fiber_mk_eq_orbitFinset] at hmem
    exact (by decide : ¬ (rimBNode ∈ orbitFinset rimANode)) hmem

/-- The universe of the quotient at `(2, 0)` is the three-element
finset of its orbits. -/
theorem univ_quot_two_zero :
    (Finset.univ : Finset (SliceQuot 2 0))
      = {Quotient.mk (orbitSetoid 2 0) centerNode,
        Quotient.mk (orbitSetoid 2 0) rimANode,
        Quotient.mk (orbitSetoid 2 0) rimBNode} := by
  apply Finset.Subset.antisymm
  · intro o _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact quot_exhaustion o
  · exact Finset.subset_univ _

/-- The centre row of the quotient weights at `(2, 0)`: the centre
sees each rim orbit with total `3` over its single node — the
averaged weight is `3`. -/
theorem quotW_row_center :
    quotW (Quotient.mk (orbitSetoid 2 0) centerNode)
        (Quotient.mk (orbitSetoid 2 0) centerNode) = 0
    ∧ quotW (Quotient.mk (orbitSetoid 2 0) centerNode)
        (Quotient.mk (orbitSetoid 2 0) rimANode) = 3
    ∧ quotW (Quotient.mk (orbitSetoid 2 0) centerNode)
        (Quotient.mk (orbitSetoid 2 0) rimBNode) = 3 := by
  have hfC : fiber (Quotient.mk (orbitSetoid 2 0) centerNode)
      = {centerNode} := (fiber_mk_eq_orbitFinset centerNode).trans (by decide)
  have hfA : fiber (Quotient.mk (orbitSetoid 2 0) rimANode)
      = {rimANode, (⟨(0, 1, -1), by decide⟩ : Slice 2 0), (⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} :=
    (fiber_mk_eq_orbitFinset rimANode).trans (by decide)
  have hfB : fiber (Quotient.mk (orbitSetoid 2 0) rimBNode)
      = {rimBNode, (⟨(0, -1, 1), by decide⟩ : Slice 2 0), (⟨(1, 0, -1), by decide⟩ : Slice 2 0)} :=
    (fiber_mk_eq_orbitFinset rimBNode).trans (by decide)
  have eCC : sliceW centerNode centerNode = 0 := by
    simp [sliceW, centerNode]
  have eCA1 : sliceW centerNode rimANode = 1 := by
    simp [sliceW, rimANode, centerNode]
  have eCA2 : sliceW centerNode (⟨(0, 1, -1), by decide⟩ : Slice 2 0) = 1 := by
    simp [sliceW, centerNode]
  have eCA3 : sliceW centerNode (⟨(-1, 0, 1), by decide⟩ : Slice 2 0) = 1 := by
    simp [sliceW, centerNode]
  have eCB1 : sliceW centerNode rimBNode = 1 := by
    simp [sliceW, rimBNode, centerNode]
  have eCB2 : sliceW centerNode (⟨(0, -1, 1), by decide⟩ : Slice 2 0) = 1 := by
    simp [sliceW, centerNode]
  have eCB3 : sliceW centerNode (⟨(1, 0, -1), by decide⟩ : Slice 2 0) = 1 := by
    simp [sliceW, centerNode]
  refine ⟨?_, ?_, ?_⟩
  · unfold quotW
    rw [hfC, Finset.card_singleton, Finset.sum_singleton,
      Finset.sum_singleton, eCC]
    norm_num
  · unfold quotW
    rw [hfC, hfA, Finset.card_singleton, Finset.sum_singleton,
      Finset.sum_insert (by decide : rimANode ∉
        ({(⟨(0, 1, -1), by decide⟩ : Slice 2 0), (⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_insert (by decide : (⟨(0, 1, -1), by decide⟩ : Slice 2 0) ∉
        ({(⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_singleton, eCA1, eCA2, eCA3]
    norm_num
  · unfold quotW
    rw [hfC, hfB, Finset.card_singleton, Finset.sum_singleton,
      Finset.sum_insert (by decide : rimBNode ∉
        ({(⟨(0, -1, 1), by decide⟩ : Slice 2 0), (⟨(1, 0, -1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_insert (by decide : (⟨(0, -1, 1), by decide⟩ : Slice 2 0) ∉
        ({(⟨(1, 0, -1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_singleton, eCB1, eCB2, eCB3]
    norm_num

/-- The first rim row of the quotient weights at `(2, 0)`: total `3`
into the centre and `6` into the other rim orbit, over a fibre of
`3` — averaged weights `1` and `2`; nothing inside its own orbit. -/
theorem quotW_row_rimA :
    quotW (Quotient.mk (orbitSetoid 2 0) rimANode)
        (Quotient.mk (orbitSetoid 2 0) centerNode) = 1
    ∧ quotW (Quotient.mk (orbitSetoid 2 0) rimANode)
        (Quotient.mk (orbitSetoid 2 0) rimANode) = 0
    ∧ quotW (Quotient.mk (orbitSetoid 2 0) rimANode)
        (Quotient.mk (orbitSetoid 2 0) rimBNode) = 2 := by
  have hfC : fiber (Quotient.mk (orbitSetoid 2 0) centerNode)
      = {centerNode} := (fiber_mk_eq_orbitFinset centerNode).trans (by decide)
  have hfA : fiber (Quotient.mk (orbitSetoid 2 0) rimANode)
      = {rimANode, (⟨(0, 1, -1), by decide⟩ : Slice 2 0), (⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} :=
    (fiber_mk_eq_orbitFinset rimANode).trans (by decide)
  have hfB : fiber (Quotient.mk (orbitSetoid 2 0) rimBNode)
      = {rimBNode, (⟨(0, -1, 1), by decide⟩ : Slice 2 0), (⟨(1, 0, -1), by decide⟩ : Slice 2 0)} :=
    (fiber_mk_eq_orbitFinset rimBNode).trans (by decide)
  have hcA : ({rimANode, (⟨(0, 1, -1), by decide⟩ : Slice 2 0), (⟨(-1, 0, 1), by decide⟩ : Slice 2 0)}
      : Finset (Slice 2 0)).card = 3 := by decide
  have eAC1 : sliceW rimANode centerNode = 1 := by
    simp [sliceW, rimANode, centerNode]
  have eAC2 : sliceW (⟨(0, 1, -1), by decide⟩ : Slice 2 0) centerNode = 1 := by
    simp [sliceW, centerNode]
  have eAC3 : sliceW (⟨(-1, 0, 1), by decide⟩ : Slice 2 0) centerNode = 1 := by
    simp [sliceW, centerNode]
  have eAA1 : sliceW rimANode rimANode = 0 := by simp [sliceW, rimANode]
  have eAA2 : sliceW rimANode (⟨(0, 1, -1), by decide⟩ : Slice 2 0) = 0 := by
    simp [sliceW, rimANode]
  have eAA3 : sliceW rimANode (⟨(-1, 0, 1), by decide⟩ : Slice 2 0) = 0 := by
    simp [sliceW, rimANode]
  have eAA4 : sliceW (⟨(0, 1, -1), by decide⟩ : Slice 2 0) rimANode = 0 := by
    simp [sliceW, rimANode]
  have eAA5 : sliceW (⟨(0, 1, -1), by decide⟩ : Slice 2 0) (⟨(0, 1, -1), by decide⟩ : Slice 2 0) = 0 := by
    simp [sliceW]
  have eAA6 : sliceW (⟨(0, 1, -1), by decide⟩ : Slice 2 0) (⟨(-1, 0, 1), by decide⟩ : Slice 2 0) = 0 := by
    simp [sliceW]
  have eAA7 : sliceW (⟨(-1, 0, 1), by decide⟩ : Slice 2 0) rimANode = 0 := by
    simp [sliceW, rimANode]
  have eAA8 : sliceW (⟨(-1, 0, 1), by decide⟩ : Slice 2 0) (⟨(0, 1, -1), by decide⟩ : Slice 2 0) = 0 := by
    simp [sliceW]
  have eAA9 : sliceW (⟨(-1, 0, 1), by decide⟩ : Slice 2 0) (⟨(-1, 0, 1), by decide⟩ : Slice 2 0) = 0 := by
    simp [sliceW]
  have eAB1 : sliceW rimANode rimBNode = 0 := by
    simp [sliceW, rimANode, rimBNode]
  have eAB2 : sliceW rimANode (⟨(0, -1, 1), by decide⟩ : Slice 2 0) = 1 := by
    simp [sliceW, rimANode]
  have eAB3 : sliceW rimANode (⟨(1, 0, -1), by decide⟩ : Slice 2 0) = 1 := by
    simp [sliceW, rimANode]
  have eAB4 : sliceW (⟨(0, 1, -1), by decide⟩ : Slice 2 0) rimBNode = 1 := by
    simp [sliceW, rimBNode]
  have eAB5 : sliceW (⟨(0, 1, -1), by decide⟩ : Slice 2 0) (⟨(0, -1, 1), by decide⟩ : Slice 2 0) = 0 := by
    simp [sliceW]
  have eAB6 : sliceW (⟨(0, 1, -1), by decide⟩ : Slice 2 0) (⟨(1, 0, -1), by decide⟩ : Slice 2 0) = 1 := by
    simp [sliceW]
  have eAB7 : sliceW (⟨(-1, 0, 1), by decide⟩ : Slice 2 0) rimBNode = 1 := by
    simp [sliceW, rimBNode]
  have eAB8 : sliceW (⟨(-1, 0, 1), by decide⟩ : Slice 2 0) (⟨(0, -1, 1), by decide⟩ : Slice 2 0) = 1 := by
    simp [sliceW]
  have eAB9 : sliceW (⟨(-1, 0, 1), by decide⟩ : Slice 2 0) (⟨(1, 0, -1), by decide⟩ : Slice 2 0) = 0 := by
    simp [sliceW]
  refine ⟨?_, ?_, ?_⟩
  · unfold quotW
    rw [hfA, hfC, hcA,
      Finset.sum_insert (by decide : rimANode ∉
        ({(⟨(0, 1, -1), by decide⟩ : Slice 2 0), (⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_insert (by decide : (⟨(0, 1, -1), by decide⟩ : Slice 2 0) ∉
        ({(⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_singleton,
      Finset.sum_singleton, Finset.sum_singleton, Finset.sum_singleton,
      eAC1, eAC2, eAC3]
    norm_num
  · unfold quotW
    rw [hfA, hcA,
      Finset.sum_insert (by decide : rimANode ∉
        ({(⟨(0, 1, -1), by decide⟩ : Slice 2 0), (⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_insert (by decide : (⟨(0, 1, -1), by decide⟩ : Slice 2 0) ∉
        ({(⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_singleton,
      Finset.sum_insert (by decide : rimANode ∉
        ({(⟨(0, 1, -1), by decide⟩ : Slice 2 0), (⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_insert (by decide : (⟨(0, 1, -1), by decide⟩ : Slice 2 0) ∉
        ({(⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_singleton,
      Finset.sum_insert (by decide : rimANode ∉
        ({(⟨(0, 1, -1), by decide⟩ : Slice 2 0), (⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_insert (by decide : (⟨(0, 1, -1), by decide⟩ : Slice 2 0) ∉
        ({(⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_singleton,
      Finset.sum_insert (by decide : rimANode ∉
        ({(⟨(0, 1, -1), by decide⟩ : Slice 2 0), (⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_insert (by decide : (⟨(0, 1, -1), by decide⟩ : Slice 2 0) ∉
        ({(⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_singleton,
      eAA1, eAA2, eAA3, eAA4, eAA5, eAA6, eAA7, eAA8, eAA9]
    norm_num
  · unfold quotW
    rw [hfA, hfB, hcA,
      Finset.sum_insert (by decide : rimANode ∉
        ({(⟨(0, 1, -1), by decide⟩ : Slice 2 0), (⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_insert (by decide : (⟨(0, 1, -1), by decide⟩ : Slice 2 0) ∉
        ({(⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_singleton,
      Finset.sum_insert (by decide : rimBNode ∉
        ({(⟨(0, -1, 1), by decide⟩ : Slice 2 0), (⟨(1, 0, -1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_insert (by decide : (⟨(0, -1, 1), by decide⟩ : Slice 2 0) ∉
        ({(⟨(1, 0, -1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_singleton,
      Finset.sum_insert (by decide : rimBNode ∉
        ({(⟨(0, -1, 1), by decide⟩ : Slice 2 0), (⟨(1, 0, -1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_insert (by decide : (⟨(0, -1, 1), by decide⟩ : Slice 2 0) ∉
        ({(⟨(1, 0, -1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_singleton,
      Finset.sum_insert (by decide : rimBNode ∉
        ({(⟨(0, -1, 1), by decide⟩ : Slice 2 0), (⟨(1, 0, -1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_insert (by decide : (⟨(0, -1, 1), by decide⟩ : Slice 2 0) ∉
        ({(⟨(1, 0, -1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_singleton,
      eAB1, eAB2, eAB3, eAB4, eAB5, eAB6, eAB7, eAB8, eAB9]
    norm_num

/-- The second rim row of the quotient weights at `(2, 0)`: the
mirror of the first rim row — `1` into the centre, `2` into the
first rim orbit, nothing inside its own orbit. -/
theorem quotW_row_rimB :
    quotW (Quotient.mk (orbitSetoid 2 0) rimBNode)
        (Quotient.mk (orbitSetoid 2 0) centerNode) = 1
    ∧ quotW (Quotient.mk (orbitSetoid 2 0) rimBNode)
        (Quotient.mk (orbitSetoid 2 0) rimANode) = 2
    ∧ quotW (Quotient.mk (orbitSetoid 2 0) rimBNode)
        (Quotient.mk (orbitSetoid 2 0) rimBNode) = 0 := by
  have hfC : fiber (Quotient.mk (orbitSetoid 2 0) centerNode)
      = {centerNode} := (fiber_mk_eq_orbitFinset centerNode).trans (by decide)
  have hfA : fiber (Quotient.mk (orbitSetoid 2 0) rimANode)
      = {rimANode, (⟨(0, 1, -1), by decide⟩ : Slice 2 0), (⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} :=
    (fiber_mk_eq_orbitFinset rimANode).trans (by decide)
  have hfB : fiber (Quotient.mk (orbitSetoid 2 0) rimBNode)
      = {rimBNode, (⟨(0, -1, 1), by decide⟩ : Slice 2 0), (⟨(1, 0, -1), by decide⟩ : Slice 2 0)} :=
    (fiber_mk_eq_orbitFinset rimBNode).trans (by decide)
  have hcB : ({rimBNode, (⟨(0, -1, 1), by decide⟩ : Slice 2 0), (⟨(1, 0, -1), by decide⟩ : Slice 2 0)}
      : Finset (Slice 2 0)).card = 3 := by decide
  have eBC1 : sliceW rimBNode centerNode = 1 := by
    simp [sliceW, rimBNode, centerNode]
  have eBC2 : sliceW (⟨(0, -1, 1), by decide⟩ : Slice 2 0) centerNode = 1 := by
    simp [sliceW, centerNode]
  have eBC3 : sliceW (⟨(1, 0, -1), by decide⟩ : Slice 2 0) centerNode = 1 := by
    simp [sliceW, centerNode]
  have eBA1 : sliceW rimBNode rimANode = 0 := by
    simp [sliceW, rimANode, rimBNode]
  have eBA2 : sliceW rimBNode (⟨(0, 1, -1), by decide⟩ : Slice 2 0) = 1 := by
    simp [sliceW, rimBNode]
  have eBA3 : sliceW rimBNode (⟨(-1, 0, 1), by decide⟩ : Slice 2 0) = 1 := by
    simp [sliceW, rimBNode]
  have eBA4 : sliceW (⟨(0, -1, 1), by decide⟩ : Slice 2 0) rimANode = 1 := by
    simp [sliceW, rimANode]
  have eBA5 : sliceW (⟨(0, -1, 1), by decide⟩ : Slice 2 0) (⟨(0, 1, -1), by decide⟩ : Slice 2 0) = 0 := by
    simp [sliceW]
  have eBA6 : sliceW (⟨(0, -1, 1), by decide⟩ : Slice 2 0) (⟨(-1, 0, 1), by decide⟩ : Slice 2 0) = 1 := by
    simp [sliceW]
  have eBA7 : sliceW (⟨(1, 0, -1), by decide⟩ : Slice 2 0) rimANode = 1 := by
    simp [sliceW, rimANode]
  have eBA8 : sliceW (⟨(1, 0, -1), by decide⟩ : Slice 2 0) (⟨(0, 1, -1), by decide⟩ : Slice 2 0) = 1 := by
    simp [sliceW]
  have eBA9 : sliceW (⟨(1, 0, -1), by decide⟩ : Slice 2 0) (⟨(-1, 0, 1), by decide⟩ : Slice 2 0) = 0 := by
    simp [sliceW]
  have eBB1 : sliceW rimBNode rimBNode = 0 := by simp [sliceW, rimBNode]
  have eBB2 : sliceW rimBNode (⟨(0, -1, 1), by decide⟩ : Slice 2 0) = 0 := by
    simp [sliceW, rimBNode]
  have eBB3 : sliceW rimBNode (⟨(1, 0, -1), by decide⟩ : Slice 2 0) = 0 := by
    simp [sliceW, rimBNode]
  have eBB4 : sliceW (⟨(0, -1, 1), by decide⟩ : Slice 2 0) rimBNode = 0 := by
    simp [sliceW, rimBNode]
  have eBB5 : sliceW (⟨(0, -1, 1), by decide⟩ : Slice 2 0) (⟨(0, -1, 1), by decide⟩ : Slice 2 0) = 0 := by
    simp [sliceW]
  have eBB6 : sliceW (⟨(0, -1, 1), by decide⟩ : Slice 2 0) (⟨(1, 0, -1), by decide⟩ : Slice 2 0) = 0 := by
    simp [sliceW]
  have eBB7 : sliceW (⟨(1, 0, -1), by decide⟩ : Slice 2 0) rimBNode = 0 := by
    simp [sliceW, rimBNode]
  have eBB8 : sliceW (⟨(1, 0, -1), by decide⟩ : Slice 2 0) (⟨(0, -1, 1), by decide⟩ : Slice 2 0) = 0 := by
    simp [sliceW]
  have eBB9 : sliceW (⟨(1, 0, -1), by decide⟩ : Slice 2 0) (⟨(1, 0, -1), by decide⟩ : Slice 2 0) = 0 := by
    simp [sliceW]
  refine ⟨?_, ?_, ?_⟩
  · unfold quotW
    rw [hfB, hfC, hcB,
      Finset.sum_insert (by decide : rimBNode ∉
        ({(⟨(0, -1, 1), by decide⟩ : Slice 2 0), (⟨(1, 0, -1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_insert (by decide : (⟨(0, -1, 1), by decide⟩ : Slice 2 0) ∉
        ({(⟨(1, 0, -1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_singleton,
      Finset.sum_singleton, Finset.sum_singleton, Finset.sum_singleton,
      eBC1, eBC2, eBC3]
    norm_num
  · unfold quotW
    rw [hfB, hfA, hcB,
      Finset.sum_insert (by decide : rimBNode ∉
        ({(⟨(0, -1, 1), by decide⟩ : Slice 2 0), (⟨(1, 0, -1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_insert (by decide : (⟨(0, -1, 1), by decide⟩ : Slice 2 0) ∉
        ({(⟨(1, 0, -1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_singleton,
      Finset.sum_insert (by decide : rimANode ∉
        ({(⟨(0, 1, -1), by decide⟩ : Slice 2 0), (⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_insert (by decide : (⟨(0, 1, -1), by decide⟩ : Slice 2 0) ∉
        ({(⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_singleton,
      Finset.sum_insert (by decide : rimANode ∉
        ({(⟨(0, 1, -1), by decide⟩ : Slice 2 0), (⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_insert (by decide : (⟨(0, 1, -1), by decide⟩ : Slice 2 0) ∉
        ({(⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_singleton,
      Finset.sum_insert (by decide : rimANode ∉
        ({(⟨(0, 1, -1), by decide⟩ : Slice 2 0), (⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_insert (by decide : (⟨(0, 1, -1), by decide⟩ : Slice 2 0) ∉
        ({(⟨(-1, 0, 1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_singleton,
      eBA1, eBA2, eBA3, eBA4, eBA5, eBA6, eBA7, eBA8, eBA9]
    norm_num
  · unfold quotW
    rw [hfB, hcB,
      Finset.sum_insert (by decide : rimBNode ∉
        ({(⟨(0, -1, 1), by decide⟩ : Slice 2 0), (⟨(1, 0, -1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_insert (by decide : (⟨(0, -1, 1), by decide⟩ : Slice 2 0) ∉
        ({(⟨(1, 0, -1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_singleton,
      Finset.sum_insert (by decide : rimBNode ∉
        ({(⟨(0, -1, 1), by decide⟩ : Slice 2 0), (⟨(1, 0, -1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_insert (by decide : (⟨(0, -1, 1), by decide⟩ : Slice 2 0) ∉
        ({(⟨(1, 0, -1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_singleton,
      Finset.sum_insert (by decide : rimBNode ∉
        ({(⟨(0, -1, 1), by decide⟩ : Slice 2 0), (⟨(1, 0, -1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_insert (by decide : (⟨(0, -1, 1), by decide⟩ : Slice 2 0) ∉
        ({(⟨(1, 0, -1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_singleton,
      Finset.sum_insert (by decide : rimBNode ∉
        ({(⟨(0, -1, 1), by decide⟩ : Slice 2 0), (⟨(1, 0, -1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_insert (by decide : (⟨(0, -1, 1), by decide⟩ : Slice 2 0) ∉
        ({(⟨(1, 0, -1), by decide⟩ : Slice 2 0)} : Finset (Slice 2 0))),
      Finset.sum_singleton,
      eBB1, eBB2, eBB3, eBB4, eBB5, eBB6, eBB7, eBB8, eBB9]
    norm_num

end OrbifoldGapPin
end ThetLogos
