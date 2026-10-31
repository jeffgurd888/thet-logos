# SHELF-3a-ii — LANDED FULL at the P-KERNEL-CONVERSE seam: integral-kernel operators on L², the HS identity as an EQUALITY, and the Q12 seat as a proved specialization

**Verdict: SHELF-3a-ii FULL at the pre-named P-KERNEL-CONVERSE seam. The general integral-kernel operator on L² now exists in the corpus: construction, form identity, HS bound, the headline Hilbert–Schmidt identity as a full equality (not merely the inequality — the P-KERNEL-EQ fallback seam is superseded by the result), compactness, and an exact specialization theorem identifying the Q12 seat's hand-built `kernelOp` with the general operator. The one open item is the pack's item (6), the converse/kernel extraction, standing at its pre-registered seam P-KERNEL-CONVERSE by design (no bijection/isometry language anywhere). The Q12 fence's "general API absent" clause RETIRES. The F2 fence does NOT retire here — that is SHELF-3b's, as this module's face states. NO CLAIM. Dials 0/4.**

## What landed

- **Construction:** `integralKernelOp hK : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ` for general SFinite measure spaces, with the pointwise characterization `coeFn_integralKernelOp` (the operator's values are a.e. the partial integral of the kernel against the input).
- **Form identity:** `integralKernelOp_inner` (product-measure/star form) and `integralKernelOp_inner_iterated` (the pack's displayed iterated form).
- **HS bound:** `integralKernelOp_norm_le : ‖integralKernelOp hK‖ ≤ ‖K‖₂` with `‖K‖₂ := (eLpNorm K 2 (μ.prod ν)).toReal`.
- **The HS identity, as equality:** `integralKernel_isHilbertSchmidt` (in 3a-i's sense) and `integralKernel_tsum_norm_sq_eq : ∑' i, ‖integralKernelOp hK (b i)‖^2 = (eLpNorm K 2 (μ.prod ν)).toReal^2` for every Hilbert basis, with its ℝ≥0∞ and `hilbertSchmidtNormSq` forms. Method (on the record): direct Tonelli over the basis fails in this pin (`lintegral_tsum` needs a countable index); the identity is proved by a separable-range/residual argument over the countable support `kernelSupport hK b` (crux `hs_identity_subtype_ae`), on top of a finite-measure density core (tensor-span density of L² of a product) that makes the section map strongly measurable.
- **Compactness:** `integralKernelOp_isCompactOperator`, via 3a-i's `IsHilbertSchmidt.isCompactOperator`.
- **Specialization check (exact):** `kernelOp_eq_integralKernelOp` — at the Q12 seat (`α = β := ↥(sliceLinks) → G`, the seat measure, under the seat's own hypotheses including its probability-measure fact carried as an instance binder), the seat's `kernelOp μG ρ β hρcont hd K hK` **equals** `integralKernelOp hK` as continuous linear maps on `osSpace`, proved by extensionality against the seat's `coeFn_kernelLinMap`. Corollaries: `kernelOp_tsum_norm_sq_eq` (the seat's HS identity, now a corollary of the general theorem) and `kernelOp_isCompactOperator_seat`. `LatticeTransferCompact.lean` was not edited. Seat types (`osSpace`/`sliceMeasure`) occur only in the header's fence disclaimer and the final specialization section — the general statements are seat-free, so the vacuity fence holds.

## The standing seam

**P-KERNEL-CONVERSE remains open:** given a Hilbert–Schmidt operator on an L² space, extracting an L² kernel that induces it (the converse direction) is not proved. This was pre-registered in the pack as the expected seam — the pin has no `Lp`-of-product ≃ tensor-product identification to extract a kernel through — and it is recorded here as an open registered item, not a fence and not a defect in what landed. Any future converse is a NEW entry.

## Parent verification (from disk)

- Module `lean/ThetLogos/IntegralKernelHS.lean` (NEW, 3,127 lines): canonical counter **strict=103, defs=20**, zero attribute-prefixed declarations, zero "sorry"/`native_decide` tokens; no landed file edited.
- Parent module build green (3,562 jobs), independently reproduced.
- Parent axiom check: `integralKernel_tsum_norm_sq_eq`, `integralKernelOp_isCompactOperator`, `integralKernel_isHilbertSchmidt`, `kernelOp_eq_integralKernelOp` each on exactly `[propext, Classical.choice, Quot.sound]` (the builder's log additionally certifies the ℝ≥0∞ identity form and `kernelOp_tsum_norm_sq_eq` on the same three).

## Census

9,818 → **9,921 strict** / 9,896 → **9,999 attribute-inclusive** / 328 → **329 modules** (delta +103 strict, +1 module).

## Backers since last landing

No change to the backer roll since the last landing.
