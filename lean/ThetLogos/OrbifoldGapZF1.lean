/-
# OrbifoldGapZF1 — ZF-1: the totals identity and the symmetry criterion

**Scope: ~/workspace/your_files/gravity-orb-z3-fold-scope-2026-11-18.md,
§2 Leg A, brick ZF-1. Commissioned by Zero, 2026-11-18 18:07 EST
("Fire all three legs"). NO CLAIM. Dials 0/4. Dial-ineligible.**

The averaged quotient weights `quotW` of `OrbifoldGapPin` are not
plain-symmetric at unequal orbit sizes — the disclosed deviation.
This brick proves the exact bookkeeping identity behind that fact:
`quotW o o' * |fiber o| = quotW o' o * |fiber o'|` — both sides are
the inter-orbit totals, which are symmetric by `sliceW_symm`.
Corollary: wherever all fibres share one cardinality, `quotW` *is*
symmetric, and the variational `fiedler` applies to the quotient.
`quotW` is also nonnegative at general `(R, h)`.

Kills watched: K-ORB-FOLD-SYMM — had the totals identity failed,
no weighting repair of the averaged fold would exist. It stands.
-/

import ThetLogos.OrbifoldGapPin

namespace ThetLogos
namespace OrbifoldGapPin

variable {R : ℕ} {h : ℤ}

/-- Every fibre is nonempty: a quotient vertex has a representative,
and the representative lies in its own fibre. Hence every fibre
cardinality is a positive natural, as a real number nonzero. -/
theorem fiber_card_ne_zero (o : SliceQuot R h) :
    ((fiber o).card : ℝ) ≠ 0 := by
  obtain ⟨p, hp⟩ := Quotient.exists_rep o
  have hmem : p ∈ fiber (Quotient.mk (orbitSetoid R h) p) := by
    simp [fiber]
  rw [hp] at hmem
  have hpos : 0 < (fiber o).card := Finset.card_pos.mpr ⟨p, hmem⟩
  exact_mod_cast hpos.ne'

/-- Un-averaging the quotient weight: `quotW o o'` times the size
of its own fibre is the inter-orbit total of slice weights. -/
theorem quotW_mul_card (o o' : SliceQuot R h) :
    quotW o o' * ((fiber o).card : ℝ)
      = ∑ p ∈ fiber o, ∑ q ∈ fiber o', sliceW p q := by
  unfold quotW
  rw [div_mul_cancel₀ _ (fiber_card_ne_zero o)]

/-- **The totals identity.** `quotW o o' * |fiber o|` equals
`quotW o' o * |fiber o'|` — both are the inter-orbit totals, and
the totals are symmetric because `sliceW` is. This is the exact
reason `quotW` fails to be plain-symmetric only through the fibre
sizes: the asymmetry is `|fiber o| : |fiber o'|`, nothing else. -/
theorem quotW_totals (o o' : SliceQuot R h) :
    quotW o o' * ((fiber o).card : ℝ)
      = quotW o' o * ((fiber o').card : ℝ) := by
  rw [quotW_mul_card, quotW_mul_card, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro p _
  exact sliceW_symm p q

/-- **The symmetry criterion.** Where two fibres have the same
cardinality, the averaged quotient weights between them are
symmetric. In particular, at a layer where every orbit has one
common size, `quotW` is a symmetric weight and BridgeCompletion's
variational package applies to the quotient verbatim. -/
theorem quotW_symm_of_card_eq {o o' : SliceQuot R h}
    (hcard : (fiber o).card = (fiber o').card) :
    quotW o o' = quotW o' o := by
  have ht := quotW_totals (R := R) (h := h) o o'
  rw [hcard] at ht
  exact mul_right_cancel₀ (fiber_card_ne_zero o') ht

/-- The quotient weights are nonnegative at general `(R, h)`:
an average of nonnegative slice weights over a nonempty fibre. -/
theorem quotW_nonneg (o o' : SliceQuot R h) : 0 ≤ quotW o o' := by
  unfold quotW
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro p _
    apply Finset.sum_nonneg
    intro q _
    exact sliceW_nonneg p q
  · exact Nat.cast_nonneg _

end OrbifoldGapPin
end ThetLogos
