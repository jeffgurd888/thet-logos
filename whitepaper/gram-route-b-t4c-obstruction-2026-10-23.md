# Gram clause, Route B, step T4c — OBSTRUCTION (the sandwich monomial)

**Date:** 2026-10-23. **Verdict: T4c does NOT land.** No module was
built, no proved file was touched, no statement was weakened. The
stop is the brief's own kill condition, triggered in the design
phase. Full memo: builder's verdict memo (scratch archive,
`routeb-general-scratch/verdict-memo-t4c.md`). Census unchanged:
**4,299 strict / 4,238 attribute-inclusive / 141 modules.** Landing
label unchanged: Stage 1b-B positivity T1 for U(1); general (G, ρ)
**OPEN**.

## The computation

Fix a crossing plaquette at the lower plane. The corpus anatomy
(`LatticeGramSeries.zero_link_pattern`, `linkA/B/C/D`) gives its
holonomy in the split configuration as `A · B · C⁻¹ · D⁻¹`, where
**A and C lie in the positive stratum**, B in the negative half, and
D in the strict positive half. Hence

  `tr ρ(plaq) = Σ_{a,i,j,k} (ρA)_{a i} (ρB)_{i j} (ρC⁻¹)_{j k} (ρD⁻¹)_{k a}`,

and splitting the loop at its only negative-half factor leaves the
closed-half arc `ρ(C⁻¹) · ρ(D⁻¹) · ρ(A)` — a
**stratum · strict · stratum sandwich**: the strict factor sits
*between* the two stratum factors.

## Why word-entry features cannot carry it

Every monomial in a word entry `(ρW)_{αβ}` is a **path monomial** —
consecutive factors share an index. The arc's monomial
`(ρC⁻¹)_{j k} · (ρA)_{a i}` with `k ≠ a` has its stratum factors
sharing **no** index; they are joined only through the strict matrix
`(ρD⁻¹)_{k a}`. It is an occurrence (tensor) coefficient, not a word
entry, and no sum of path monomials contains it. Concretely, at
(G, ρ, d, N) = (U(2), inclusion, 2, 4), the monomial
`(ρC⁻¹)_{0 1} (ρA)_{0 0} (ρD⁻¹)_{1 0} (ρB)_{0 0}` occurs in
`tr ρ(plaq)` with coefficient 1 (loop indices a=0, i=0, j=0, k=1;
the path condition would need a = k, i.e. 0 = 1), and occurs in no
`conj(featB) · featA` summand. So the pointwise Gram identity
`hgram` is **false for the word-entry feature family**, already at
order β¹. A second, independent failure: `exp(−S₀)` is a product
over all crossing plaquettes, and a product of word entries is again
an occurrence coefficient, not a word entry.

The obstruction is invisible at d = 1 and for abelian ρ — scalars
have no index contraction — which is exactly why Route C closed for
U(1) and why the word-entry design looked sufficient from the
abelian template.

## What stands

The integrated criterion `osForm_nonneg_of_gram_integrated`
(untouched — a conditional theorem about arbitrary families), and
T4a/T4b entire: `featA_marginal`, `featB_marginal`, `dual_gamma`
are integral identities about single word entries and remain true.
What fails is exactly one pointwise identity, for these features.
The blocker is now precisely located: not the criterion, not the
marginals, not domination — the pointwise Gram identity for
word-entry features, killed by the sandwich monomial.

## The repair (priced; commissioned as a re-charter)

**Occurrence features**: replace the word datum by the two-slot arc
datum `(linkC, linkA)` with flavors `(flavRep ρ false, flavRep ρ
true)`; `featAᵒᶜᶜ := φ₀(restrictPos y) · occMat-coefficient(stratPart
y)` with φ₀ carrying the strict matrix coefficient, and
`Ξᵒᶜᶜ := γᵒᶜᶜ • φ₀`. The two hard headlines are **already landed**:
the stratum integral of an occMat coefficient
(`GramAssembly.stratum_integral_occMat`) and the occMat-level dual
transport (`GramMirror.integral_occMat_dual`, `coeff_dual` — the
word-level `dual_gamma` was proved through them); the marginal
proof template never used word-ness. Split: **T4a′** (A-side
occurrence features + marginal, ~T4a scale), **T4b′** (B side,
cheaper — dual transport landed), **T4c′** (the closer on the
ᵒᶜᶜ family; `hgram` then holds by construction).

**NO CLAIM.** Parts of any official Clay statement closed: 0.
