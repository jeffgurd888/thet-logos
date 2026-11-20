/-
# OrbifoldGapZF5 — ZF-5a: the weighted folded gap, definitions and algebra

**Scope: ~/workspace/your_files/gravity-orb-z3-fold-scope-2026-11-18.md,
§2 Leg B, brick ZF-5 (first half; the brick is split at the
declaration seam under the small-brick rule — attainment and the
eigenvector conclusion are ZF-5b). Commissioned by Zero,
2026-11-18 18:07 EST ("Fire all three legs"). NO CLAIM. Dials
0/4. Dial-ineligible.**

The weighted variational package on the quotient, at general
`(R, h)`, built on ZF-4's weighted inner product
`⟨G, H⟩_w = ∑ o, orbSize o * G o * H o`:

* `wAdmissible` — the weighted-mean-zero, weighted-unit
  potentials (the constraint is the weighted mean: under the
  pullback it is exactly the slice's plain mean, by ZF-4's
  isometry at `H = 1`);
* `wEnergy` — the weighted Dirichlet energy
  `⟨G, laplacianOp quotW G⟩_w`, which by the isometry and the
  banked intertwining is the slice energy of the pullback
  (`wEnergy_eq_slice_energy`), hence nonnegative;
* `wBilin` — its polarization, symmetric by ZF-4's weighted
  self-adjointness, with the quadratic variation formulas
  (`wEnergy_smul`, `wEnergy_add_smul`) the Lagrange argument of
  ZF-5b feeds on.
-/

import ThetLogos.OrbifoldGapZF4

namespace ThetLogos
namespace OrbifoldGapPin

/-- The orbit-size weights are positive: every fibre is nonempty
(ZF-1). -/
theorem orbSize_pos {R : ℕ} {h : ℤ} (o : SliceQuot R h) :
    0 < orbSize o := by
  show (0:ℝ) < ((fiber o).card : ℝ)
  exact lt_of_le_of_ne (Nat.cast_nonneg _) (fiber_card_ne_zero o).symm

/-- The weighted-admissible potentials: weighted mean zero and
weighted unit norm, in the `orbSize` inner product. -/
noncomputable def wAdmissible {R : ℕ} {h : ℤ} :
    Set (SliceQuot R h → ℝ) :=
  {G | (∑ o, orbSize o * G o = 0) ∧ (∑ o, orbSize o * G o ^ 2 = 1)}

/-- The weighted Dirichlet energy of a quotient function:
`⟨G, laplacianOp quotW G⟩_w`. -/
noncomputable def wEnergy {R : ℕ} {h : ℤ} (G : SliceQuot R h → ℝ) :
    ℝ :=
  ∑ o, orbSize o * G o * laplacianOp quotW G o

/-- The polarized weighted energy: `⟨G, laplacianOp quotW F⟩_w`
in the second-named function's values against the first's
operator — the convention of BridgeCompletion's `bilin`. -/
noncomputable def wBilin {R : ℕ} {h : ℤ} (F G : SliceQuot R h → ℝ) :
    ℝ :=
  ∑ o, orbSize o * G o * laplacianOp quotW F o

/-- The weighted bilinear form on the diagonal is the energy. -/
theorem wBilin_self {R : ℕ} {h : ℤ} (F : SliceQuot R h → ℝ) :
    wBilin F F = wEnergy F := rfl

/-- The weighted bilinear form is symmetric — ZF-4's weighted
self-adjointness, restated. -/
theorem wBilin_symm {R : ℕ} {h : ℤ} (F G : SliceQuot R h → ℝ) :
    wBilin F G = wBilin G F := by
  have h := quotW_weighted_self_adjoint F G
  have e1 : wBilin F G
      = ∑ o, orbSize o * laplacianOp quotW F o * G o := by
    show (∑ o, orbSize o * G o * laplacianOp quotW F o)
      = ∑ o, orbSize o * laplacianOp quotW F o * G o
    exact Finset.sum_congr rfl (fun o _ => by ring)
  have e2 : wBilin G F
      = ∑ o, orbSize o * F o * laplacianOp quotW G o := by
    show (∑ o, orbSize o * F o * laplacianOp quotW G o)
      = ∑ o, orbSize o * F o * laplacianOp quotW G o
    exact Finset.sum_congr rfl (fun o _ => by ring)
  rw [e1, e2]
  exact h

/-- The weighted energy is quadratic in the potential. -/
theorem wEnergy_smul {R : ℕ} {h : ℤ} (c : ℝ) (F : SliceQuot R h → ℝ) :
    wEnergy (c • F) = c ^ 2 * wEnergy F := by
  have hterm : ∀ o : SliceQuot R h,
      orbSize o * (c • F) o * laplacianOp quotW (c • F) o
        = c ^ 2 * (orbSize o * F o * laplacianOp quotW F o) := by
    intro o
    rw [laplacianOp_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  show (∑ o, orbSize o * (c • F) o * laplacianOp quotW (c • F) o)
    = c ^ 2 * ∑ o, orbSize o * F o * laplacianOp quotW F o
  rw [Finset.sum_congr rfl (fun o _ => hterm o), ← Finset.mul_sum]

/-- The one-step variation of the weighted energy: along
`F + t • G` it is a quadratic polynomial in `t` whose linear
coefficient is twice the weighted bilinear form. -/
theorem wEnergy_add_smul {R : ℕ} {h : ℤ} (F G : SliceQuot R h → ℝ)
    (t : ℝ) :
    wEnergy (F + t • G)
      = wEnergy F + 2 * t * wBilin F G + t ^ 2 * wEnergy G := by
  have hexp : ∀ o : SliceQuot R h,
      orbSize o * (F + t • G) o * laplacianOp quotW (F + t • G) o
        = orbSize o * F o * laplacianOp quotW F o
          + t * (orbSize o * G o * laplacianOp quotW F o
            + orbSize o * F o * laplacianOp quotW G o)
          + t ^ 2 * (orbSize o * G o * laplacianOp quotW G o) := by
    intro o
    rw [laplacianOp_add, laplacianOp_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsum : wEnergy (F + t • G)
      = wEnergy F + t * (wBilin F G + wBilin G F)
        + t ^ 2 * wEnergy G := by
    show (∑ o, orbSize o * (F + t • G) o
        * laplacianOp quotW (F + t • G) o)
      = (∑ o, orbSize o * F o * laplacianOp quotW F o)
        + t * ((∑ o, orbSize o * G o * laplacianOp quotW F o)
          + ∑ o, orbSize o * F o * laplacianOp quotW G o)
        + t ^ 2 * ∑ o, orbSize o * G o * laplacianOp quotW G o
    rw [Finset.sum_congr rfl (fun o _ => hexp o),
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsum, wBilin_symm G F]
  ring

/-- **The ZF-4 equivalence, energy form**: the weighted energy
of a quotient function is the slice energy of its pullback —
the folded variational problem is the slice's variational
problem restricted to invariant potentials. -/
theorem wEnergy_eq_slice_energy {R : ℕ} {h : ℤ}
    (G : SliceQuot R h → ℝ) :
    wEnergy G = energy sliceW (pullback G) := by
  calc wEnergy G = ∑ o, orbSize o * G o * laplacianOp quotW G o := rfl
    _ = ∑ p, pullback G p * pullback (laplacianOp quotW G) p :=
        (pullback_isometry G (laplacianOp quotW G)).symm
    _ = ∑ p, pullback G p * laplacianOp sliceW (pullback G) p := by
        apply Finset.sum_congr rfl
        intro p _
        exact congrArg (pullback G p * ·) (intertwining G p).symm
    _ = energy sliceW (pullback G) := rfl

/-- The weighted energy is nonnegative: it is a slice energy. -/
theorem wEnergy_nonneg {R : ℕ} {h : ℤ} (G : SliceQuot R h → ℝ) :
    0 ≤ wEnergy G := by
  rw [wEnergy_eq_slice_energy]
  exact energy_nonneg sliceW sliceW_symm sliceW_nonneg (pullback G)

end OrbifoldGapPin
end ThetLogos
