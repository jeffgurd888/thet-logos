# Third Family, Brick F2 — PARTIAL: The Assembly Stands, the Damping Lemma Is Killed

**Date:** 2026-10-24 · **Road Map Item 1 (Stage 1b-B, general (G, ρ)), third family, brick F2 of F1 → F2 → F3. Priced L.**
**Verdict: PARTIAL.** Full builder's record: `routeb-general-scratch/verdict-memo-third-family-f2.md`. Parent-verified 2026-10-24: targeted build exit 0 (3,447 jobs), `.olean` present, strict recount 49, zero `sorry`/`admit`, all six headline declarations on standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

**NO CLAIM.** Parts of any official Clay statement closed: **0**. Stage 1b-B label unchanged: T1 for U(1) at all β ≥ 0 (Route C); general (G, ρ) **OPEN**.

## What stands (T1) — module `LatticeGramAssembly` (49 strict / 12 defs)

The global word family over the reflection seam is assembled from F1's single-plaquette factorization, and the integrated criterion's pointwise Gram identity is **proved** for it (`assembly_hgram`): for every even N ≥ 2, every d > 0, every real β, the Gibbs weight of the unsplit configuration equals the `∑′` over the global word index `SeamIdx` of `conj(featGB) * featGA`. Also proved and packaged (`assembly_package`): measurability of both feature families (the criterion's `hAA`/`hBA`), the domination package (`norm_featGA_le`, `norm_featB_le`, `boundCA_nonneg`, `summable_boundCA_mul_boundCB` — the criterion's `hAB`/`hBB`/`hCA`/`hsum`). Supporting results of independent standing: `hasSum_pi_prod` (finite products of dominated summable families over a pi type) and `trace_plaquette_eq_hsInner` (the plaquette trace is the Hilbert–Schmidt inner product of the two arc matrices). Everything the criterion asks of a family **except the two marginals** is now theorem.

## What is killed (K-F2(b)/(c)) — the Damping Lemma, by exhibited mechanism

The criterion's marginals require both sides' marginals to factor through **one** common Ξ with real dampings dA, dB ≥ 0. For the assembled family they do not. At the charter's test index (word levels (1,1) at one lower crossing plaquette, (0,0) elsewhere), the trace identity forces an arc split in which one side's matrix is the **three-link entangled product** ρ(A⁻¹·D·C) and the other's is the **bare link** ρ(B). Integrating the plane links: on the entangled side the invariant (Schur) pairing collapses the strict-link sum to a constant, so Ã_{i₀}(z) = C₀·exp(−S₊(z)) with C₀ = (β/d)²/d > 0 (β ≠ 0); on the bare side the strict link survives as a single entry of the transported configuration, B̃_{i₀}(z) = exp(−S₊(z))·|ρ(z_{linkD})_{(α0).1,(α0).2}|². A common Ξ would force the ratio B̃/Ã to be constant; it is C₀⁻¹·|ρ(z_D)_{(α0).1,(α0).2}|², nonconstant for every d ≥ 2. **Finite check:** (S₃, standard 2-dim irrep), N = 2, β = 1: the entry takes values 1 (at z_D = e) and 1/4 (at a reflection). At d = 1 the internal sum is trivial, both survivors coincide, and the marginals do factor — exactly Route C's discharge.

This is the (k,a)/(j,i) mechanism at its last named seat: the holonomy's cyclic order puts three of its four links on one side of the arc split and one on the other, so the reflection plane's two halves cannot carry the same word index symmetrically. It is an **index mismatch (K-F2(b))** issuing in **common-Ξ failure (K-F2(c))** — not a sign failure: K-F2(a) does not fire (no damping is ever negative; there is no damping), K-F2(d) does not fire (assembly summability stands), K-F2(e) does not fire (the criterion's shape fits verbatim; the family fails its marginal hypotheses, not its form). The kill is a paper exhibit at the charter's kill standard (T4c′ precedent), with a finite checkable instance; it is not Lean-formalized, and is recorded as such.

## Consequence (charter U3)

The third family terminates at F2. F3 is **not** commissioned — its only input would be a family satisfying the marginals, and no such family exists in this family. The integrated criterion `osForm_nonneg_of_gram_integrated` remains a true conditional, unapplied at general (G, ρ). **Four closures now stand around 1b-B general (G, ρ): factored Route B (T4c/T4c′ obstructions), the regrouped route (died at R0), transfer-matrix R2 (seam-kernel positivity obstruction), and the third family (this kill). Per charter U3 there is no fifth named family; the next direction on Item 1 is a new route decision (Jeff's).** The assembly module remains in the corpus at full rank: its theorems about the seam kernel's word expansion are true independent of the dead route.

## Census

4,510 → **4,559 strict** · 4,559 → **4,608 attribute-inclusive** · 152 → **153 counted modules**. Seven-sorry qualification unchanged (this module contains none).
