# Stage 2, Brick S2-4 (form seat) — the Hamiltonian form — LANDED STANDS

Date: 2026-10-24. Module: `LatticeSliceHamiltonian` (38 strict / 7 defs).
Parent-verified: targeted build exit 0, olean present, axioms clean
(`[propext, Classical.choice, Quot.sound]`) on the package, the circle
package, the β=0 clause, and the vacuum clause. Census after landing:
5,122 strict / 5,171 attribute-inclusive / 171 modules.

## Scope
Charter half (a) ONLY: Ĥ as a positive quadratic form on the S2-2 engine
space (priced M). Half (b) — a self-adjoint operator Ĥ with
exp(−Ĥ) = T̂ (priced L) — was NOT attempted; kill K-S2-4 (operator) stays
OPEN, not faked. The form-level kill did not fire: the package holds on
the whole engine space, with the domain *characterized*, not assumed.

## Construction
No roots of T̂ and no spectral calculus exist in the corpus, so the
−log T̂ form is built from the Taylor series of −log at λ = 1 read on the
defect A := 1 − T̂: approximants
q_K x = Σ_{j∈Icc 1 K} (j:ℝ)⁻¹·(⟪x, A^[j] x⟫).re, and
sliceHamForm x = ⨆ K, ENNReal.ofReal (q_K x) — ℝ≥0∞-valued, so ⊤
honestly marks outside-the-domain. sliceHamFormDomain is the finiteness
locus as a Submodule ℂ. Termwise positivity rests on
sliceHamDefect_iter_diag (defect-iterate diagonals real ≥ 0), tracing to
S2-2b's FACTORED-form positivity — labels kept throughout; no osForm
assertion; not a 1b-B input.

## The package (sliceHamiltonian_package, 15 clauses)
Conditional at general (G, ρ), every real β, even N, under exactly
SliceHPosOne: approximants ≥ 0 and monotone in K; parallelogram law;
q_K 0 = 0; q_0 x = 0; homogeneity q_K(c•x) = ‖c‖²·q_K x; vacuum in the
kernel (sliceHamForm Ω = 0, Ω ∈ domain); domain characterized
(x ∈ domain ↔ sliceHamForm x ≠ ⊤); tying identities — energy forms
Q_n x = ‖x‖² − (⟪x, T̂^[n] x⟫).re ≥ 0 for all n, vanishing on Ω, with
Q₁ = q₁ and ofReal Q₁ ≤ sliceHamForm; every ofReal (q_K x) ≤ form;
T̂x = x → form x = 0.

Unconditional specializations: sliceHamiltonian_circle_package (full
package at the U(1) seat, all β ≥ 0, via S2-3); sliceHamForm_beta_zero
(form ≡ 0 at β = 0, general (G, ρ), via S2-2d).

## Residue for the L operator brick (exact)
(i) completed Hilbert space + T̂ by continuity (the engine space is
still the pre-Hilbert Π₁-quotient); (ii) self-adjoint Ĥ ≥ 0 with
‖Ĥ^{1/2}x‖² = sliceHamForm x on the completed domain; (iii) exp(−Ĥ) = T̂.
The (1 − T̂^{1/n}) root route was not taken (no roots available); it
enters, if ever, as a new brick.

## S2-5 interface (charter: the weld, M)
Consume sliceHamiltonianPackage / sliceHamiltonian_circle_package /
sliceHamForm_beta_zero: form, domain submodule + membership criterion,
vacuum kernel, Q₁ = q₁, ofReal Q₁ ≤ form, monotonicity, fixed-vector
vanishing — all at form level. The weld's own charter (pre-revision
text) targets the unitary/isometry between the reconstructed space and
the slice picture, with kill K-S2-5 priced: if the OS-quotient norm on
slice observables differs from the L² slice norm beyond S1's identity,
the weld lands as an isometry onto its image or a form-level identity,
PARTIAL, discrepancy named. The gate revision's record already
establishes that the Π₁ norm is the transfer-form norm, NOT L² — the
weld is aimed at the surviving objects (S2-2 engine; S1 sliceState /
transferOp), P₂ pairing dead and not consumed.

## Fences
NO CLAIM. Clay parts closed: 0. Dials 0/4. Stage 1b-B label untouched
(OPEN at general (G, ρ)). Factored-form labels stay factored.
