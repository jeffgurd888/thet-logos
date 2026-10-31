# SHELF-3a-i — LANDED FULL: the Hilbert–Schmidt core — the pin's missing HS API, basis independence included

**Verdict: SHELF-3a-i FULL. The corpus now owns a general Hilbert–Schmidt operator API where Mathlib v4.35.0-rc3 has none (pin re-grepped at dispatch: `HilbertSchmidt` / `Schatten` zero hits). All statements are for arbitrary Hilbert spaces over ℂ with `CompleteSpace` — no finite-dimensionality, no separability, no seat types anywhere; the pack's vacuity fence holds on the types. The pre-named P-HS-BASIS seam (basis independence) was NOT hit: independence is proved in full. NO CLAIM. Dials 0/4.**

## What landed

- **The class:** `IsHilbertSchmidt T` (summability of squared norms over some orthonormal basis) with `hilbertSchmidtNormSq T b := ∑' i, ‖T (b i)‖^2` and the membership characterization `isHilbertSchmidt_iff`.
- **Basis independence, FULL:** at the ℝ≥0∞ level both domain-basis totals equal the adjoint's codomain-basis total (Parseval in the other factor + `ENNReal.tsum_comm`), transported back to ℝ: `IsHilbertSchmidt.summable_norm_sq` (some basis ⇒ every basis summable) and `hilbertSchmidtNormSq_eq` (the sums are equal).
- **Rank-one and finite-rank:** `hilbertSchmidtNormSq_rankOne` (HS² of `rankOne ℂ x y` is `‖x‖^2 * ‖y‖^2` for every basis), `isHilbertSchmidt_rankOne`, `isHilbertSchmidt_sum_rankOne`; plus the general pin-missing lemma `hs_isCompactOperator_of_range_le_finiteDimensional` (plain normed spaces; named distinctly from Q12's seat-module copy to avoid a namespace clash).
- **HS ⇒ compact:** finite-rank truncations `hsApprox` with tail control (`hs_tailSq_tendsto_zero`, `hs_approx_bound`, norm convergence `hs_tendsto_approx`) and the headline `IsHilbertSchmidt.isCompactOperator` via the pin's `isCompactOperator_of_tendsto`.
- **Ideal structure (the pack's stretch item, fully reached):** `IsHilbertSchmidt.opNorm_le` (‖T‖ ≤ √HS²), zero/add/smul closure, the adjoint symmetry (`IsHilbertSchmidt.adjoint`, `hilbertSchmidtNormSq_adjoint` — equal HS norm), and the two-sided ideal property with product bounds (`IsHilbertSchmidt.comp_left` / `comp_right`, `hilbertSchmidtNormSq_comp_left_le` / `comp_right_le`).

## Fence status

This is the first half of the SHELF-3 fill. The Q12 fence ("general API absent") retires only when **3a-ii** (integral-kernel operators on L², the HS identity Σᵢ ‖T(b i)‖² = ‖K‖₂², and the Q12-seat specialization check) also lands; the F2 fence's first half is stocked by this module, and its second half is SHELF-3b (gated on 3a-ii per the map). Nothing about this landing touches the 𝒜 ⪰ 0 core, the F2 weld itself, or any dial.

## Parent verification (from disk)

- Module `lean/ThetLogos/HilbertSchmidt.lean` (NEW, 782 lines): canonical counter **strict=39, defs=5** (pack estimate 20–35; the stretch item accounts for the excess), zero attribute-prefixed declarations, zero "sorry"/`native_decide` tokens; no landed file edited.
- Parent module build green (3,210 jobs), independently reproduced.
- Parent axiom check: `hilbertSchmidtNormSq_eq`, `IsHilbertSchmidt.isCompactOperator`, `IsHilbertSchmidt.opNorm_le`, `hilbertSchmidtNormSq_adjoint` each on exactly `[propext, Classical.choice, Quot.sound]` (the builder's log additionally certifies `IsHilbertSchmidt.summable_norm_sq`, `hilbertSchmidtNormSq_rankOne`, and both comp bounds on the same three).

## Census

9,779 → **9,818 strict** / 9,857 → **9,896 attribute-inclusive** / 327 → **328 modules** (delta +39 strict, +1 module).

## Backers since last landing

No change to the backer roll since the last landing.
