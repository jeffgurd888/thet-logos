/-
# OrbifoldGapZF4 — ZF-4: the weighted repair, isometry + self-adjointness

**Scope: ~/workspace/your_files/gravity-orb-z3-fold-scope-2026-11-18.md,
§2 Leg B, brick ZF-4. Commissioned by Zero, 2026-11-18 18:07 EST
("Fire all three legs"). NO CLAIM. Dials 0/4. Dial-ineligible.**

The deviation banked in the base pin — the averaged quotient
weights `quotW` are not plain-symmetric at unequal orbit sizes —
is repaired by the orbit-size weighting. With
`orbSize o = |fiber o|`:

* the pullback is an isometry from the `orbSize`-weighted inner
  product on the quotient to the plain inner product on the
  slice (`pullback_isometry`), by the fibre decomposition of the
  slice sum;
* the quotient operator is self-adjoint in the weighted inner
  product (`quotW_weighted_self_adjoint`), by the isometry, the
  banked `intertwining`, and the slice operator's own
  self-adjointness.

Both at general `(R, h)` — unequal orbit sizes included, the
headline seat included. This is the inner product in which ZF-5
defines the weighted folded gap.

Kills watched: K-ORB-FOLD-WEIGHTED — had some fibre identity
failed here, the weighted repair would die and the deviation
would stand as the final form. It does not fire: the isometry is
exact, with no correction term.
-/

import ThetLogos.OrbifoldGapZF1

namespace ThetLogos
namespace OrbifoldGapPin

/-- The orbit-size weight: the cardinality of the fibre over a
quotient point, as a real number. At the headline seat it takes
the values `(1, 3, 3)`; at `(2, 1)` it is constantly `3`. -/
noncomputable def orbSize {R : ℕ} {h : ℤ} (o : SliceQuot R h) : ℝ :=
  ((fiber o).card : ℝ)

/-- **The pullback isometry**: the plain inner product of two
pullbacks on the slice is the `orbSize`-weighted inner product
on the quotient. Each fibre contributes its constant value once
per node. -/
theorem pullback_isometry {R : ℕ} {h : ℤ} (G H : SliceQuot R h → ℝ) :
    ∑ p, pullback G p * pullback H p
      = ∑ o, orbSize o * G o * H o := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ)
    (g := fun p : Slice R h => Quotient.mk (orbitSetoid R h) p)
    (f := fun p : Slice R h => pullback G p * pullback H p)
    (fun p _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro o _
  show (∑ p ∈ fiber o, pullback G p * pullback H p)
    = orbSize o * G o * H o
  have hterm : ∀ p ∈ fiber o, pullback G p * pullback H p
      = G o * H o := by
    intro p hp
    have hmk : Quotient.mk (orbitSetoid R h) p = o :=
      (Finset.mem_filter.mp hp).2
    show G (Quotient.mk (orbitSetoid R h) p)
        * H (Quotient.mk (orbitSetoid R h) p) = G o * H o
    rw [hmk]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  show ((fiber o).card : ℝ) * (G o * H o)
    = ((fiber o).card : ℝ) * G o * H o
  exact (mul_assoc _ _ _).symm

/-- **Weighted self-adjointness**: the quotient operator is
self-adjoint in the `orbSize`-weighted inner product, at general
`(R, h)` — the symmetry the averaged weights lack pointwise is
restored by the weighting. -/
theorem quotW_weighted_self_adjoint {R : ℕ} {h : ℤ}
    (G H : SliceQuot R h → ℝ) :
    ∑ o, orbSize o * laplacianOp quotW G o * H o
      = ∑ o, orbSize o * G o * laplacianOp quotW H o := by
  calc ∑ o, orbSize o * laplacianOp quotW G o * H o
      = ∑ p, laplacianOp sliceW (pullback G) p * pullback H p := by
        rw [← pullback_isometry]
        apply Finset.sum_congr rfl
        intro p _
        have e : pullback (laplacianOp quotW G) p
            = laplacianOp sliceW (pullback G) p :=
          (intertwining G p).symm
        exact congrArg (· * pullback H p) e
    _ = ∑ p, pullback H p * laplacianOp sliceW (pullback G) p := by
        apply Finset.sum_congr rfl
        intro p _
        exact mul_comm _ _
    _ = ∑ p, pullback G p * laplacianOp sliceW (pullback H) p :=
        laplacianOp_symm_form sliceW sliceW_symm (pullback G) (pullback H)
    _ = ∑ p, pullback G p * pullback (laplacianOp quotW H) p := by
        apply Finset.sum_congr rfl
        intro p _
        exact congrArg (pullback G p * ·) (intertwining H p)
    _ = ∑ o, orbSize o * G o * laplacianOp quotW H o :=
        pullback_isometry G (laplacianOp quotW H)

end OrbifoldGapPin
end ThetLogos
