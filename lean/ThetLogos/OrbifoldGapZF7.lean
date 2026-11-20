/-
# OrbifoldGapZF7 — ZF-7: a concrete upper bound on the slice gap at (2, 0)

**Scope: ~/workspace/your_files/gravity-orb-z3-fold-scope-2026-11-18.md,
§2 Leg C, brick ZF-7. Commissioned by Zero, 2026-11-18 18:07 EST
("Fire all three legs"). NO CLAIM. Dials 0/4. Dial-ineligible.**

`fiedler (sliceW (R := 2) (h := 0)) ≤ 2`, by exhibition: the first
coordinate function `p ↦ p.1` on the headline slice is an
eigenfunction of the slice Laplacian with eigenvalue `2` (the
rim is a 6-cycle with a hub; the first coordinate is its `k = 1`
Fourier mode), mean-zero and nonzero, so the banked
`fiedler_le_of_eigenvector` applies.

This brick also banks two pieces of Leg C infrastructure used by
ZF-8: the headline layer as an explicit finset, and the identity
of a represented fibre with the orbit finset.
-/

import ThetLogos.OrbifoldGapPin

namespace ThetLogos
namespace OrbifoldGapPin

/-- The headline layer, explicitly: the seven nodes of `L_0` at
`R = 2` — the centre and the two rim orbits. -/
theorem layerFinset_two_zero :
    layerFinset 2 0 = {(0, 0, 0), (1, -1, 0), (0, 1, -1), (-1, 0, 1),
      (-1, 1, 0), (1, 0, -1), (0, -1, 1)} := by decide

/-- The fibre over a represented quotient vertex is exactly the
orbit finset of the representative. -/
theorem fiber_mk_eq_orbitFinset {R : ℕ} {h : ℤ} (p : Slice R h) :
    fiber (Quotient.mk (orbitSetoid R h) p) = orbitFinset p := by
  ext q
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and,
    orbitFinset, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hq
    have hrel : orbitRel R h q p := Quotient.eq.mp hq
    rcases orbitRel_symm hrel with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact Quotient.eq.mpr (Or.inl rfl)
    · exact Quotient.eq.mpr
        (orbitRel_symm (show orbitRel R h p (cycSlice R h p)
          from Or.inr (Or.inl rfl)))
    · exact Quotient.eq.mpr
        (orbitRel_symm (show orbitRel R h p (cycSlice R h (cycSlice R h p))
          from Or.inr (Or.inr rfl)))

/-- Evaluation infrastructure: a `sliceW`-weighted sum over the
headline slice is the explicit seven-term sum over the layer. -/
theorem sum_sliceW_two_zero (p : Slice 2 0) (g : (ℤ × ℤ × ℤ) → ℝ) :
    (∑ q : Slice 2 0, sliceW p q * (g p.1 - g q.1))
      = ∑ q ∈ ({(0, 0, 0), (1, -1, 0), (0, 1, -1), (-1, 0, 1),
          (-1, 1, 0), (1, 0, -1), (0, -1, 1)} : Finset (ℤ × ℤ × ℤ)),
        (if (p.1.1 - q.1) ^ 2 + (p.1.2.1 - q.2.1) ^ 2
            + (p.1.2.2 - q.2.2) ^ 2 = 2 then (1 : ℝ) else 0)
          * (g p.1 - g q) := by
  calc (∑ q : Slice 2 0, sliceW p q * (g p.1 - g q.1))
      = ∑ q : Slice 2 0, (if (p.1.1 - q.1.1) ^ 2 + (p.1.2.1 - q.1.2.1) ^ 2
          + (p.1.2.2 - q.1.2.2) ^ 2 = 2 then (1 : ℝ) else 0)
          * (g p.1 - g q.1) :=
        Finset.sum_congr rfl (fun q _ => rfl)
    _ = ∑ t ∈ layerFinset 2 0, (if (p.1.1 - t.1) ^ 2 + (p.1.2.1 - t.2.1) ^ 2
          + (p.1.2.2 - t.2.2) ^ 2 = 2 then (1 : ℝ) else 0) * (g p.1 - g t) :=
        Finset.sum_coe_sort (layerFinset 2 0) (fun t : ℤ × ℤ × ℤ =>
          (if (p.1.1 - t.1) ^ 2 + (p.1.2.1 - t.2.1) ^ 2
            + (p.1.2.2 - t.2.2) ^ 2 = 2 then (1 : ℝ) else 0) * (g p.1 - g t))
    _ = ∑ t ∈ ({(0, 0, 0), (1, -1, 0), (0, 1, -1), (-1, 0, 1),
          (-1, 1, 0), (1, 0, -1), (0, -1, 1)} : Finset (ℤ × ℤ × ℤ)),
        (if (p.1.1 - t.1) ^ 2 + (p.1.2.1 - t.2.1) ^ 2
          + (p.1.2.2 - t.2.2) ^ 2 = 2 then (1 : ℝ) else 0) * (g p.1 - g t) :=
        Finset.sum_congr layerFinset_two_zero (fun t _ => rfl)

/-- The first coordinate is a slice eigenfunction at `(2, 0)`
with eigenvalue `2`: at every node, the weighted sum of its
coordinate drops is twice its coordinate. -/
theorem coord_fst_eigen (p : Slice 2 0) :
    laplacianOp sliceW (fun q : Slice 2 0 => (q.1.1 : ℝ)) p
      = 2 * (p.1.1 : ℝ) := by
  rw [laplacianOp_apply, sum_sliceW_two_zero p (fun t => (t.1 : ℝ))]
  have hp : p.1 ∈ ({(0, 0, 0), (1, -1, 0), (0, 1, -1), (-1, 0, 1),
      (-1, 1, 0), (1, 0, -1), (0, -1, 1)} : Finset (ℤ × ℤ × ℤ)) := by
    rw [← layerFinset_two_zero]; exact p.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with h | h | h | h | h | h | h <;> rw [h] <;>
    norm_num [Finset.sum_insert, Finset.sum_singleton]

/-- **ZF-7 headline.** The slice Fiedler value at the headline
seat is at most `2`. -/
theorem fiedler_slice_two_zero_le_two :
    fiedler (sliceW (R := 2) (h := 0)) ≤ 2 := by
  apply fiedler_le_of_eigenvector sliceW sliceW_symm sliceW_nonneg
    (fun q : Slice 2 0 => (q.1.1 : ℝ)) 2 _ _ coord_fst_eigen
  · -- mean-zero: the first coordinates of the seven nodes sum to 0
    have : (∑ q : Slice 2 0, (q.1.1 : ℝ))
        = ∑ q ∈ layerFinset 2 0, (q.1 : ℝ) :=
      Finset.sum_coe_sort (layerFinset 2 0) (fun t : ℤ × ℤ × ℤ => (t.1 : ℝ))
    rw [this, layerFinset_two_zero]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  · -- nonzero: the first rim node has first coordinate `1`
    intro hfun
    have h1 := congrFun hfun rimANode
    simp only [Pi.zero_apply] at h1
    norm_num [rimANode] at h1

end OrbifoldGapPin
end ThetLogos
