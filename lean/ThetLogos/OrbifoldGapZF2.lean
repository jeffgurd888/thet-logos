/-
# OrbifoldGapZF2 — ZF-2: census of the diagonal-free layer (2, 1)

**Scope: ~/workspace/your_files/gravity-orb-z3-fold-scope-2026-11-18.md,
§2 Leg A, brick ZF-2. Commissioned by Zero, 2026-11-18 18:07 EST
("Fire all three legs"). NO CLAIM. Dials 0/4. Dial-ineligible.**

The second seat of the fold, chosen because it is diagonal-free:
a cyc-fixed node has all coordinates equal, so its coordinate sum
is `3t` — a diagonal node lies in `L_h` only if `3 ∣ h`
(`three_dvd_of_cyc_fixed`, general). At `h = 1` there is therefore
no fixed node, and the census by `decide` bears it out: the layer
has 6 nodes in two orbits of 3, every fibre has card 3, and the
quotient has 2 points. At this seat — unlike the headline seat —
all fibres agree, so ZF-1's `quotW_symm_of_card_eq` makes the
averaged weights symmetric: Leg A's variational form is statable
here (ZF-3).

 DISCLOSED DEVIATION FROM THE SCOPE TEXT: the scope's ZF-2 line
 quotes `Fintype.card (SliceQuot 2 1) = 3`. That number is
 inconsistent with the scope's own census on the same line (6
 nodes, fibres 3 + 3 — two orbits), and the census decides it:
 the card is `2` (`card_quot_two_one`). The fibre claim — the
 K-ORB-FOLD-FIBRE trigger — is the load-bearing one, and it
 holds: **K-ORB-FOLD-FIBRE does not fire.**
-/

import ThetLogos.OrbifoldGapZF7

namespace ThetLogos
namespace OrbifoldGapPin

/-- A representative of the full orbit at `(2, 1)`: the node
`(1, 1, -1)`, whose cyc-orbit is `{(1, 1, -1), (-1, 1, 1),
(1, -1, 1)}`. -/
def fullNode21 : Slice 2 1 := ⟨(1, 1, -1), by decide⟩

/-- A representative of the axis orbit at `(2, 1)`: the node
`(1, 0, 0)`, whose cyc-orbit is `{(1, 0, 0), (0, 1, 0),
(0, 0, 1)}`. -/
def axisNode21 : Slice 2 1 := ⟨(1, 0, 0), by decide⟩

/-- The layer at `(2, 1)`, by `decide`: six nodes — the full orbit
and the axis orbit. -/
theorem layerFinset_two_one :
    layerFinset 2 1 = {(1, 1, -1), (-1, 1, 1), (1, -1, 1),
      (1, 0, 0), (0, 1, 0), (0, 0, 1)} := by decide

/-- A cyc-fixed node has all three coordinates equal, so its
coordinate sum is a multiple of `3`: a diagonal node lies in
`L_h` only if `3 ∣ h`. -/
theorem three_dvd_of_cyc_fixed {R : ℕ} {h : ℤ} (p : Slice R h)
    (hp : cycSlice R h p = p) : 3 ∣ h := by
  have hv : cyc p.1 = p.1 := congrArg Subtype.val hp
  have e1 : p.1.2.2 = p.1.1 := congrArg Prod.fst hv
  have e2 : p.1.1 = p.1.2.1 := congrArg (fun t : ℤ × ℤ × ℤ => t.2.1) hv
  have hsum : p.1.1 + p.1.2.1 + p.1.2.2 = h :=
    (Finset.mem_filter.mp p.2).2
  exact ⟨p.1.1, by omega⟩

/-- At `(2, 1)` there is no cyc-fixed node: `3 ∤ 1`. -/
theorem no_cyc_fixed_two_one (p : Slice 2 1) :
    cycSlice 2 1 p ≠ p :=
  fun hp => (by decide : ¬ (3 ∣ (1 : ℤ))) (three_dvd_of_cyc_fixed p hp)

/-- Every point of the quotient at `(2, 1)` is one of the two
orbits. -/
theorem quot_exhaustion_two_one (o : SliceQuot 2 1) :
    o = Quotient.mk (orbitSetoid 2 1) fullNode21
      ∨ o = Quotient.mk (orbitSetoid 2 1) axisNode21 := by
  obtain ⟨p, rfl⟩ := Quotient.exists_rep o
  have hp : p.1 ∈ ({(1, 1, -1), (-1, 1, 1), (1, -1, 1),
      (1, 0, 0), (0, 1, 0), (0, 0, 1)} : Finset (ℤ × ℤ × ℤ)) := by
    rw [← layerFinset_two_one]; exact p.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with h | h | h | h | h | h
  · have hpe : p = fullNode21 := Subtype.ext h
    rw [hpe]
    exact Or.inl rfl
  · have hpe : p = cycSlice 2 1 fullNode21 := Subtype.ext h
    rw [hpe]
    exact Or.inl (Quotient.eq.mpr
      (orbitRel_symm (show orbitRel 2 1 fullNode21 (cycSlice 2 1 fullNode21)
        from Or.inr (Or.inl rfl))))
  · have hpe : p = cycSlice 2 1 (cycSlice 2 1 fullNode21) := Subtype.ext h
    rw [hpe]
    exact Or.inl (Quotient.eq.mpr
      (orbitRel_symm (show orbitRel 2 1 fullNode21
        (cycSlice 2 1 (cycSlice 2 1 fullNode21)) from Or.inr (Or.inr rfl))))
  · have hpe : p = axisNode21 := Subtype.ext h
    rw [hpe]
    exact Or.inr rfl
  · have hpe : p = cycSlice 2 1 axisNode21 := Subtype.ext h
    rw [hpe]
    exact Or.inr (Quotient.eq.mpr
      (orbitRel_symm (show orbitRel 2 1 axisNode21 (cycSlice 2 1 axisNode21)
        from Or.inr (Or.inl rfl))))
  · have hpe : p = cycSlice 2 1 (cycSlice 2 1 axisNode21) := Subtype.ext h
    rw [hpe]
    exact Or.inr (Quotient.eq.mpr
      (orbitRel_symm (show orbitRel 2 1 axisNode21
        (cycSlice 2 1 (cycSlice 2 1 axisNode21)) from Or.inr (Or.inr rfl))))

/-- The two orbits at `(2, 1)` are distinct points of the
quotient. -/
theorem quot_distinct_two_one :
    Quotient.mk (orbitSetoid 2 1) fullNode21
      ≠ Quotient.mk (orbitSetoid 2 1) axisNode21 := by
  intro hcon
  have hmem : fullNode21 ∈ fiber (Quotient.mk (orbitSetoid 2 1) fullNode21) := by
    simp [fiber]
  rw [hcon, fiber_mk_eq_orbitFinset] at hmem
  exact (by decide : ¬ (fullNode21 ∈ orbitFinset axisNode21)) hmem

/-- The universe of the quotient at `(2, 1)` is the two-element
finset of its orbits. -/
theorem univ_quot_two_one :
    (Finset.univ : Finset (SliceQuot 2 1))
      = {Quotient.mk (orbitSetoid 2 1) fullNode21,
        Quotient.mk (orbitSetoid 2 1) axisNode21} := by
  symm
  apply Finset.eq_univ_of_forall
  intro o
  rcases quot_exhaustion_two_one o with rfl | rfl
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- Every fibre at `(2, 1)` has card `3`: the two orbits are the
same size — the equal-orbit case, in contrast to the headline
seat's `1, 3, 3`. -/
theorem fiber_card_two_one (o : SliceQuot 2 1) : (fiber o).card = 3 := by
  rcases quot_exhaustion_two_one o with rfl | rfl
  · rw [fiber_mk_eq_orbitFinset]; decide
  · rw [fiber_mk_eq_orbitFinset]; decide

/-- The quotient at `(2, 1)` has exactly two points. (The scope
text quotes `3` here; the census decides `2` — see the header.) -/
theorem card_quot_two_one : Fintype.card (SliceQuot 2 1) = 2 := by
  rw [← Finset.card_univ, univ_quot_two_one,
    Finset.card_insert_of_notMem
      (Finset.notMem_singleton.mpr quot_distinct_two_one),
    Finset.card_singleton]

end OrbifoldGapPin
end ThetLogos
