/-
# OrbifoldGapZF9 — ZF-9: Leg C assembly at (2, 0)

**Scope: ~/workspace/your_files/gravity-orb-z3-fold-scope-2026-11-18.md,
§2 Leg C, brick ZF-9. Commissioned by Zero, 2026-11-18 18:07 EST
("Fire all three legs"). NO CLAIM. Dials 0/4. Dial-ineligible.**

The assembly of ZF-7 and ZF-8 at the headline seat. The quotient's
least nonconstant eigenvalue is exactly `5` (ZF-8b's floor, attained
by the descended orientation function), while the slice's own
Fiedler value is at most `2` (ZF-7) — a strict raise. Consequently
the base pin's equality criterion `fiedler_eq_iff_invariant_eigen`
is decided NEGATIVELY at `(2, 0)`: no nonconstant quotient
eigenpair sits at the slice's Fiedler value, and the slice has no
cyc-invariant Fiedler eigenvector — the slice's gap is attained
only off the fold's symmetric sector, and the fold raises the gap
at this seat from `≤ 2` to exactly `5`.

K-ORB-GAPMAP-EQ (two-sided) resolves on its negative side: equality
is not the theorem at `(2, 0)`; the strict raise is.
-/

import ThetLogos.OrbifoldGapZF8b
import ThetLogos.OrbifoldGapZF7

namespace ThetLogos
namespace OrbifoldGapPin

/-- **The least nonconstant quotient eigenvalue at `(2, 0)` is
exactly `5`**: ZF-8b's floor from below, the descended orientation
function's eigenpair from above. -/
theorem quot_least_eigen_two_zero :
    IsLeast {μ : ℝ | ∃ G : SliceQuot 2 0 → ℝ,
      (∀ o, laplacianOp quotW G o = μ * G o) ∧ ∃ o o', G o ≠ G o'} 5 :=
  ⟨⟨descend orientFn orientFn_invariant, eigenpair_five,
      eigenpair_five_nonconst⟩,
    by
      intro μ hμ
      obtain ⟨G, hG, hnc⟩ := hμ
      exact quot_floor_two_zero hG hnc⟩

/-- **The strict raise at `(2, 0)`**: the slice's Fiedler value is
strictly below the quotient's least nonconstant eigenvalue — the
fold raises the gap at the headline seat. -/
theorem fiedler_strict_raise_two_zero :
    fiedler (sliceW (R := 2) (h := 0)) < 5 :=
  lt_of_le_of_lt fiedler_slice_two_zero_le_two (by norm_num)

/-- No nonconstant quotient eigenpair at `(2, 0)` sits at the
slice's Fiedler value: the floor `5` and ZF-7's bound `≤ 2`
exclude it. -/
theorem no_quotient_eigen_at_fiedler_two_zero :
    ¬ ∃ G : SliceQuot 2 0 → ℝ, (∃ o o', G o ≠ G o')
      ∧ ∀ o, laplacianOp quotW G o
        = fiedler (sliceW (R := 2) (h := 0)) * G o := by
  rintro ⟨G, hnc, heig⟩
  have h5 := quot_floor_two_zero heig hnc
  have h2 := fiedler_slice_two_zero_le_two
  linarith

/-- **The equality criterion decided negatively at `(2, 0)`**: the
slice has no cyc-invariant Fiedler eigenvector. Via the base pin's
`fiedler_eq_iff_invariant_eigen`, an invariant Fiedler eigenvector
would descend to a nonconstant quotient eigenpair at the slice's
Fiedler value — excluded by the previous theorem. -/
theorem no_invariant_fiedler_eigen_two_zero :
    ¬ ∃ F : Slice 2 0 → ℝ, (∀ p, F (cycSlice 2 0 p) = F p) ∧ F ≠ 0
      ∧ (∑ p, F p = 0)
      ∧ ∀ p, laplacianOp sliceW F p
        = fiedler (sliceW (R := 2) (h := 0)) * F p := by
  have hcard : (Fintype.card (Slice 2 0) : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast Fintype.card_pos_iff.mpr ⟨centerNode⟩)
  intro h
  exact no_quotient_eigen_at_fiedler_two_zero
    ((fiedler_eq_iff_invariant_eigen hcard).mpr h)

end OrbifoldGapPin
end ThetLogos
