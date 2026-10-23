# Scoping — the Gram clause (Pitch 4, Stage 1b-B completion)

**Date:** 2026-10-23
**Status:** SCOPING ONLY. No build commissioned by this document.
Jeff commissioned the scope + price on 2026-10-23; the build decision
is his, on the prices below.
**Object:** discharge the one open clause of Stage 1b-B
(`whitepaper/pitch-4-stage-1b-b-2026-10-17.md`): reflection positivity
of the Wilson Gibbs weight at general β ≥ 0, at general (G, ρ), on the
even-extent torus.
**NO CLAIM.** Parts of any official Clay statement closed by anything
in this document: 0. Stage 1b-B's current verdict — PARTIAL, form and
criterion standing, the factorization open — is unchanged by scoping.

## 1. The open content, exactly

`LatticePositivity.lean` proves the Gram criterion
`osForm_nonneg_of_gram` (line 1425): IF the Gibbs weight in split
variables is a finite Gram sum

  exp(−wilsonAction (splitEquiv.symm (y, u)))
    = ∑ᵢ conj(Ξᵢ (mirrorP u)) · Ξᵢ (restrictPos y)        (hgram)

with ι a `Fintype` and Ξᵢ bounded measurable features on strict-half
configurations, THEN the OS form's diagonal is a nonnegative real at
that β (any real β; the criterion is sign-free). Everything else in
1b-B stands: the form, its factorization, the kernel identity
(`osForm_eq_kernel`), positivity at β = 0. The open content is
exactly: **supply (ι, Ξ) and prove `hgram` for the Wilson weight.**

## 2. T0 finding — the literal `hgram` is probably not the door

Two independent obstructions to `hgram` *as literally stated* were
found in scoping. Neither is a defect in the proved criterion (a
proved implication with a hard hypothesis is still proved); both say
the standard proof does not produce this hypothesis. T0 of any build
settles them on paper and by finite probes before code is priced
further.

**(i) Plane-link dependence.** `y` ranges over `halfLinks`
configurations, which include the reflection-fixed stratum links at
t = N/2−1 (`planeLinks`, def. line 157); `restrictPos y` forgets them,
and `mirrorP u` likewise forgets the t = N−1 stratum in `u`. But the
crossing action S₀ — Stage 1b-A's stratum-crossing plaquette sum —
depends on those very links: varying one stratum link at fixed
(restrictPos y, mirrorP u) changes exp(−S) and cannot change the
right-hand side. The module's own header (lines 38–54) frames the
true target as *positivity of the stratum-integrated crossing
kernel*, and records that the fixed-stratum kernel is **not**
positive — consistent with this obstruction and inconsistent with a
pointwise, stratum-blind, finite Gram identity. Expected verdict:
`hgram` is unsatisfiable for the Wilson weight at β ≠ 0.

**(ii) Finite-rank obstruction.** Even with the stratum integrated,
a *finite* Gram sum means the crossing kernel has finite rank. The
plaquette factor exp((β/d)·Re tr ρ(g)) has full Peter–Weyl support
(e.g. on U(1): exp(β·cos θ) = I₀(β) + 2·∑ₙ Iₙ(β)·cos nθ, every
Iₙ(β) > 0 at β > 0) — infinite rank. The standard proof's Gram sum
is a *series*, converging in the kernel's L² sense, which is all the
OS form ever tests (it integrates the kernel against bounded
observables).

**Consequence.** The build's first theorem is a **criterion
variant**: `osForm_nonneg_of_gram_integrated` — the OS form is
nonnegative when the *stratum-integrated* crossing kernel is a
convergent Gram series (countable index, square-summable features,
domination hypotheses shaped like the existing criterion's). This is
new theorem-proving inside the corpus's own architecture, priced
into Routes B and C below. `osForm_nonneg_of_gram` stands as proved;
it is expected to be a lemma about a hypothesis the Wilson weight
does not satisfy, and the dossier will say so at full rank if T0
confirms it.

## 3. What Mathlib has today (pinned v4.35.0-rc3, checked 2026-10-23)

- Peter–Weyl for compact groups: **absent** (no file matches).
- Matrix coefficients as a named API: **absent** (the identifier does
  not occur). Orthogonality of matrix coefficients for compact
  groups: absent. `RepresentationTheory/Character.lean` covers
  **finite** groups only.
- Present and sufficient for the routes below: Haar probability
  measure on compact groups with two-sided invariance (already the
  1b-B setup), Bochner integration of finite-dimensional-valued
  functions, Fubini on product measures, finite-dimensional inner
  product spaces with orthonormal bases, `Matrix.kronecker`
  (tensor products of matrices), uniform-convergence machinery.

## 4. Routes, priced

**Route A — full Peter–Weyl in Lean. XL / blocked. DO NOT COMMISSION.**
Building orthogonality of matrix coefficients for a general compact
group is a Mathlib-scale project of its own (it is a known gap in
the library, with multi-year efforts elsewhere). It would discharge
the clause, but it is not a brick in this ladder; it is a detour
through someone else's mountain.

**Route B — averaging, not orthogonality (general G). L.**
Avoid irreducibles entirely. Per crossing plaquette and per tensor
power k, the factor (Re tr ρ(w))ᵏ is a matrix coefficient of a
*finite-dimensional* tensor-power representation of the stratum
product group; integrating the stratum variables is applying the
averaging operator A = ∫ ρ_big(g) dμ, which for a unitary
representation is an **orthogonal projection** (idempotent and
self-adjoint by Haar invariance and unitarity) — no Peter–Weyl, no
Schur, no irreducibility anywhere. A projection is a finite Gram
sum over an orthonormal basis of its range, per k; the exponential
series (coefficients ≥ 0 exactly when β ≥ 0) is summed across k by
domination (|Re tr ρ| ≤ d on the compact group). Steps:
- **T0** (paper + ≤150 lines of probes): settle §2 (i)/(ii); exhibit
  the crossing action's word structure in split variables against
  1b-A's `splitEquiv` and 1b-B's `wilsonAction_split_half`.
- **T1**: the criterion variant of §2 (series/integrated Gram).
- **T2**: the averaging-projection lemma (general compact G,
  finite-dimensional unitary rep): A is the orthogonal projection
  onto the invariant subspace; range has an ONB; A is a finite Gram
  sum. A reusable module in its own right.
- **T3**: word/tensor bookkeeping: crossing plaquette words as
  tensor-representation matrix coefficients; joint stratum integral
  = A applied (the rectangular pairing of the dossier's
  counterexample 2 is absorbed by tensoring both stratum factors —
  T0 confirms the joint, not per-plaquette, tensoring suffices).
- **T4**: assembly: features Ξ on the strict half, boundedness and
  measurability (polynomials in link entries — continuous), series
  domination, and the discharge: OS positivity at every β ≥ 0,
  general (G, ρ). **1b-B STANDS WHOLE.**
Estimated size 1,400–2,400 lines across two modules (comparable to
`LatticePositivity.lean` itself, 1,559). Risk is bookkeeping mass,
not missing theory. Kill conditions: T0 shows the word structure
does not split as required even jointly (would reprice upward);
T2's projection identity fails for merely-continuous (non-unitary
w.r.t. the chosen inner product) reps — fenced by working
throughout with the corpus's unitary-valued ρ and tensor inner
products, where unitarity is definitional.

**Route C — U(1) first (the abelian discharge). S–M.**
Same architecture, one group: matrix coefficients of U(1) are
z ↦ zⁿ; the needed orthogonality on the circle is Fourier
orthogonality, elementary against Mathlib's circle API. Discharges
the clause **for U(1)** (defining representation): OS positivity of
the U(1) Wilson theory at every β ≥ 0 becomes T1. Shares T0 and the
T1 criterion variant with Route B, and its T3 assembly is Route B's
dress rehearsal at 1/10 the bookkeeping. Estimated 400–800 lines.
Honest label on landing: 1b-B positivity stands for U(1); the clause
at general (G, ρ) remains open until Route B. This is the
recommended first commission: it converts the clause from
"reduced to harmonic analysis we don't have" into "proved in the
abelian case, general case priced and de-risked."

**Route D — T2 wrapper. S. NOT RECOMMENDED.** Axiomatize the Gram
property as a named hypothesis and restate positivity conditionally.
Adds a label, no content; 1b-B already *is* that statement. Listed
for completeness, priced, and declined.

## 5. Fences

- β ≥ 0 only (the nonnegative-coefficient step); β < 0 positivity
  is not claimed by any route (the criterion itself is sign-free,
  its Wilson discharge is not).
- Even N, the corpus's standing hypotheses (`[MeasurableInv G]`,
  continuity of `repMatrix ρ` passed explicitly) are inherited.
- Finite volume only. No OS Hilbert space (1b-C), no transfer
  matrix (1b-D), no thermodynamic or continuum limit, no gap.
- If T0 confirms §2(i), the 1b-B dossier gains an addendum at full
  rank: the finite pointwise criterion is not satisfiable by the
  Wilson weight; the integrated criterion replaces it as the named
  door. The proved theorem is not edited retroactively; the record
  is corrected by addition, per the relabeling rule.

## 6. Recommendation

Commission **T0 + Route C** as one brick (the anatomy, the criterion
variant, and the U(1) discharge), priced S–M. Route B is then a
separate commission at L with its main risks already retired. Route
A stays on the shelf as a named XL; if Mathlib ever lands
Peter–Weyl, Route B's price collapses and the record will say so.

*Charter written 2026-10-23. Anchors: `LatticePositivity.lean`
lines 30–54 (header), 134–171 (link sets), 999 (`wilsonAction_split_half`),
1392–1447 (criterion + `hgram`); dossier
`pitch-4-stage-1b-b-2026-10-17.md`; Mathlib checks by `rg` over the
pinned checkout, 2026-10-23.*
