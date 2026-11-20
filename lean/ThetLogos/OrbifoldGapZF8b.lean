/-
# OrbifoldGapZF8b — ZF-8b: the quotient floor at (2, 0)

**Scope: ~/workspace/your_files/gravity-orb-z3-fold-scope-2026-11-18.md,
§2 Leg C, brick ZF-8 (second half). Commissioned by Zero, 2026-11-18
18:07 EST ("Fire all three legs"). NO CLAIM. Dials 0/4.
Dial-ineligible.**

ZF-8a banked the quotient's arithmetic at the headline seat; this
brick spends it. The quotient Laplacian's three rows are explicit,
so an eigenpair's three scalar equations are explicit: subtracting
the rim equations gives `(a − b)(μ − 5) = 0`, and combining the
centre equation with the rim sum gives `μ(μ − 7)c = 0`. A
nonconstant eigenpair therefore has `μ ∈ {5, 7}` — the floor is
`5`, and it is attained: the orientation function
`(x − y)(y − z)(z − x)` on the slice is cyc-invariant with
eigenvalue `5` and descends to the quotient eigenpair at `5`.

Kills watched: K-ORB-GAPMAP-FLOOR — had the arithmetic of ZF-8a
come back with a nonconstant eigenpair below `5`, the floor would
die here. It does not: the floor is `5`, decided.
-/

import ThetLogos.OrbifoldGapZF8

namespace ThetLogos
namespace OrbifoldGapPin

/-- The quotient Laplacian at `(2, 0)`, row by row: on the centre
it is `6c − 3a − 3b`, on the rim orbits `−c + 3a − 2b` and
`−c − 2a + 3b`, where `c, a, b` are the function's three values. -/
theorem laplacian_quot_two_zero (G : SliceQuot 2 0 → ℝ) :
    laplacianOp quotW G (Quotient.mk (orbitSetoid 2 0) centerNode)
      = 6 * G (Quotient.mk (orbitSetoid 2 0) centerNode)
        - 3 * G (Quotient.mk (orbitSetoid 2 0) rimANode)
        - 3 * G (Quotient.mk (orbitSetoid 2 0) rimBNode)
    ∧ laplacianOp quotW G (Quotient.mk (orbitSetoid 2 0) rimANode)
      = - G (Quotient.mk (orbitSetoid 2 0) centerNode)
        + 3 * G (Quotient.mk (orbitSetoid 2 0) rimANode)
        - 2 * G (Quotient.mk (orbitSetoid 2 0) rimBNode)
    ∧ laplacianOp quotW G (Quotient.mk (orbitSetoid 2 0) rimBNode)
      = - G (Quotient.mk (orbitSetoid 2 0) centerNode)
        - 2 * G (Quotient.mk (orbitSetoid 2 0) rimANode)
        + 3 * G (Quotient.mk (orbitSetoid 2 0) rimBNode) := by
  have hCne : (Quotient.mk (orbitSetoid 2 0) centerNode)
      ∉ ({Quotient.mk (orbitSetoid 2 0) rimANode,
        Quotient.mk (orbitSetoid 2 0) rimBNode} : Finset (SliceQuot 2 0)) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨quot_distinct.1, quot_distinct.2.1⟩
  have hAne : (Quotient.mk (orbitSetoid 2 0) rimANode)
      ∉ ({Quotient.mk (orbitSetoid 2 0) rimBNode} : Finset (SliceQuot 2 0)) :=
    Finset.notMem_singleton.mpr quot_distinct.2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [laplacianOp_apply, univ_quot_two_zero, Finset.sum_insert hCne,
      Finset.sum_insert hAne, Finset.sum_singleton,
      quotW_row_center.1, quotW_row_center.2.1, quotW_row_center.2.2]
    ring
  · rw [laplacianOp_apply, univ_quot_two_zero, Finset.sum_insert hCne,
      Finset.sum_insert hAne, Finset.sum_singleton,
      quotW_row_rimA.1, quotW_row_rimA.2.1, quotW_row_rimA.2.2]
    ring
  · rw [laplacianOp_apply, univ_quot_two_zero, Finset.sum_insert hCne,
      Finset.sum_insert hAne, Finset.sum_singleton,
      quotW_row_rimB.1, quotW_row_rimB.2.1, quotW_row_rimB.2.2]
    ring

/-- The orientation density of a tuple: `(x − y)(y − z)(z − x)`.
Cyclically invariant, mirror-odd — on the headline slice it is the
`5`-eigenfunction of the invariant sector, with orbit values
`(0, 2, −2)`. -/
def orientCoord (t : ℤ × ℤ × ℤ) : ℝ :=
  ((t.1 : ℝ) - (t.2.1 : ℝ)) * ((t.2.1 : ℝ) - (t.2.2 : ℝ))
    * ((t.2.2 : ℝ) - (t.1 : ℝ))

/-- The orientation function on the headline slice. -/
def orientFn (p : Slice 2 0) : ℝ := orientCoord p.1

/-- The orientation function is cyc-invariant: the fold's rotation
permutes its three factors cyclically. -/
theorem orientFn_invariant (p : Slice 2 0) :
    orientFn (cycSlice 2 0 p) = orientFn p := by
  show ((p.1.2.2 : ℝ) - (p.1.1 : ℝ)) * ((p.1.1 : ℝ) - (p.1.2.1 : ℝ))
      * ((p.1.2.1 : ℝ) - (p.1.2.2 : ℝ))
    = ((p.1.1 : ℝ) - (p.1.2.1 : ℝ)) * ((p.1.2.1 : ℝ) - (p.1.2.2 : ℝ))
      * ((p.1.2.2 : ℝ) - (p.1.1 : ℝ))
  ring

/-- The orientation function is a slice eigenfunction at `(2, 0)`
with eigenvalue `5`: at every node, the weighted sum of its drops
is five times its value. -/
theorem orientFn_eigen (p : Slice 2 0) :
    laplacianOp sliceW orientFn p = 5 * orientFn p := by
  rw [laplacianOp_apply]
  unfold orientFn
  rw [sum_sliceW_two_zero p orientCoord]
  have hp : p.1 ∈ ({(0, 0, 0), (1, -1, 0), (0, 1, -1), (-1, 0, 1),
      (-1, 1, 0), (1, 0, -1), (0, -1, 1)} : Finset (ℤ × ℤ × ℤ)) := by
    rw [← layerFinset_two_zero]; exact p.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with h | h | h | h | h | h | h <;> rw [h] <;>
    norm_num [Finset.sum_insert, Finset.sum_singleton, orientCoord]

/-- The exhibited quotient eigenpair at `μ = 5`: the orientation
function, descended to the quotient. -/
theorem eigenpair_five (o : SliceQuot 2 0) :
    laplacianOp quotW (descend orientFn orientFn_invariant) o
      = 5 * descend orientFn orientFn_invariant o :=
  descend_eigen orientFn_invariant orientFn_eigen o

/-- The descended orientation function is nonconstant: it takes
the values `2` and `−2` on the two rim orbits. -/
theorem eigenpair_five_nonconst :
    ∃ o o', descend orientFn orientFn_invariant o
      ≠ descend orientFn orientFn_invariant o' :=
  ⟨Quotient.mk (orbitSetoid 2 0) rimANode,
    Quotient.mk (orbitSetoid 2 0) rimBNode, by
    show orientFn rimANode ≠ orientFn rimBNode
    norm_num [orientFn, orientCoord, rimANode, rimBNode]⟩

/-- **ZF-8 headline — the quotient floor at `(2, 0)`.** Every
nonconstant quotient eigenpair at the headline seat has eigenvalue
at least `5`. The proof is the three scalar equations of
`laplacian_quot_two_zero`: their rim difference gives
`(a − b)(μ − 5) = 0` and their centre/rim-sum combination gives
`μ(μ − 7)c = 0`; a nonconstant eigenpair has `μ ∈ {5, 7}`. -/
theorem quot_floor_two_zero {G : SliceQuot 2 0 → ℝ} {μ : ℝ}
    (hG : ∀ o, laplacianOp quotW G o = μ * G o)
    (hGnc : ∃ o o', G o ≠ G o') :
    5 ≤ μ := by
  have hC : μ * G (Quotient.mk (orbitSetoid 2 0) centerNode)
      = 6 * G (Quotient.mk (orbitSetoid 2 0) centerNode)
        - 3 * G (Quotient.mk (orbitSetoid 2 0) rimANode)
        - 3 * G (Quotient.mk (orbitSetoid 2 0) rimBNode) :=
    (hG _).symm.trans (laplacian_quot_two_zero G).1
  have hA : μ * G (Quotient.mk (orbitSetoid 2 0) rimANode)
      = - G (Quotient.mk (orbitSetoid 2 0) centerNode)
        + 3 * G (Quotient.mk (orbitSetoid 2 0) rimANode)
        - 2 * G (Quotient.mk (orbitSetoid 2 0) rimBNode) :=
    (hG _).symm.trans (laplacian_quot_two_zero G).2.1
  have hB : μ * G (Quotient.mk (orbitSetoid 2 0) rimBNode)
      = - G (Quotient.mk (orbitSetoid 2 0) centerNode)
        - 2 * G (Quotient.mk (orbitSetoid 2 0) rimANode)
        + 3 * G (Quotient.mk (orbitSetoid 2 0) rimBNode) :=
    (hG _).symm.trans (laplacian_quot_two_zero G).2.2
  have hdiff : (G (Quotient.mk (orbitSetoid 2 0) rimANode)
      - G (Quotient.mk (orbitSetoid 2 0) rimBNode)) * (μ - 5) = 0 := by
    have h : μ * (G (Quotient.mk (orbitSetoid 2 0) rimANode)
        - G (Quotient.mk (orbitSetoid 2 0) rimBNode))
      = 5 * (G (Quotient.mk (orbitSetoid 2 0) rimANode)
        - G (Quotient.mk (orbitSetoid 2 0) rimBNode)) := by linarith [hA, hB]
    have e : (G (Quotient.mk (orbitSetoid 2 0) rimANode)
        - G (Quotient.mk (orbitSetoid 2 0) rimBNode)) * (μ - 5)
      = μ * (G (Quotient.mk (orbitSetoid 2 0) rimANode)
        - G (Quotient.mk (orbitSetoid 2 0) rimBNode))
        - 5 * (G (Quotient.mk (orbitSetoid 2 0) rimANode)
        - G (Quotient.mk (orbitSetoid 2 0) rimBNode)) := by ring
    rw [e, h, sub_self]
  have hkey : μ * (μ - 7) * G (Quotient.mk (orbitSetoid 2 0) centerNode)
      = 0 := by
    have hE1 : 3 * (G (Quotient.mk (orbitSetoid 2 0) rimANode)
        + G (Quotient.mk (orbitSetoid 2 0) rimBNode))
      = (6 - μ) * G (Quotient.mk (orbitSetoid 2 0) centerNode) := by
      linarith [hC]
    have hE2 : (1 - μ) * (G (Quotient.mk (orbitSetoid 2 0) rimANode)
        + G (Quotient.mk (orbitSetoid 2 0) rimBNode))
      = 2 * G (Quotient.mk (orbitSetoid 2 0) centerNode) := by
      linarith [hA, hB]
    have hP : (1 - μ) * (3 * (G (Quotient.mk (orbitSetoid 2 0) rimANode)
        + G (Quotient.mk (orbitSetoid 2 0) rimBNode)))
      = (1 - μ) * ((6 - μ) * G (Quotient.mk (orbitSetoid 2 0) centerNode)) := by
      rw [hE1]
    have hQ : (1 - μ) * (3 * (G (Quotient.mk (orbitSetoid 2 0) rimANode)
        + G (Quotient.mk (orbitSetoid 2 0) rimBNode)))
      = 6 * G (Quotient.mk (orbitSetoid 2 0) centerNode) := by
      linear_combination 3 * hE2
    linear_combination hQ - hP
  by_cases hab : G (Quotient.mk (orbitSetoid 2 0) rimANode)
      = G (Quotient.mk (orbitSetoid 2 0) rimBNode)
  · -- The rim values agree; nonconstancy forces the centre apart,
    -- and the key identity leaves only `μ = 7` (μ = 0 collapses the
    -- centre onto the rim, and a vanishing centre forces all three
    -- values to `0`).
    have hca : G (Quotient.mk (orbitSetoid 2 0) centerNode)
        ≠ G (Quotient.mk (orbitSetoid 2 0) rimANode) := by
      intro hcon
      obtain ⟨o, o', hoo'⟩ := hGnc
      apply hoo'
      have e1 : G o = G (Quotient.mk (orbitSetoid 2 0) rimANode) := by
        rcases quot_exhaustion o with rfl | rfl | rfl
        · exact hcon
        · rfl
        · exact hab.symm
      have e2 : G o' = G (Quotient.mk (orbitSetoid 2 0) rimANode) := by
        rcases quot_exhaustion o' with rfl | rfl | rfl
        · exact hcon
        · rfl
        · exact hab.symm
      rw [e1, e2]
    rcases mul_eq_zero.mp hkey with hX | hc0
    · rcases mul_eq_zero.mp hX with hμ0 | hμ7
      · -- μ = 0: the rim equation collapses the centre onto the rim.
        have hcollapse : G (Quotient.mk (orbitSetoid 2 0) centerNode)
            = G (Quotient.mk (orbitSetoid 2 0) rimANode) := by
          rw [hμ0] at hA
          linarith [hA, hab]
        exact absurd hcollapse hca
      · linarith [sub_eq_zero.mp hμ7]
    · -- The centre value vanishes; the centre equation then forces
      -- the rim values to vanish too — all three are `0`.
      have hrim0 : G (Quotient.mk (orbitSetoid 2 0) rimANode) = 0 := by
        rw [hc0] at hC
        linarith [hC, hab]
      exact absurd (hc0.trans hrim0.symm) hca
  · -- The rim values differ; the difference identity gives `μ = 5`.
    have hμ5 : μ - 5 = 0 := by
      rcases mul_eq_zero.mp hdiff with h1 | h2
      · exact absurd (sub_eq_zero.mp h1) hab
      · exact h2
    linarith [hμ5]

end OrbifoldGapPin
end ThetLogos
