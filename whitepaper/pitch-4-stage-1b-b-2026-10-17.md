# Pitch 4 — Stage 1b-B: Reflection Positivity, the Form and the Criterion

**Date:** 2026-10-17
**Module:** `lean/ThetLogos/LatticePositivity.lean` (1,559 lines; 44 theorem/lemma
declarations + 10 definitions; NOT root-imported — verified by targeted build,
3,393 jobs, green; `.olean` present; zero sorrys — the only grep hit for
"sorry/admit" is the English word "admits" in a comment).
**Axioms:** the six headline results checked below depend only on
`propext`, `Classical.choice`, `Quot.sound`.
**Program total:** 2,283 + 44 = **2,327** theorem/lemma declarations.

## Verdict: PARTIAL (pre-named shape γ, extended) — one clause open

Stage 1b-A stands whole. Stage 1b-B lands as follows:

- **The OS form is constructed and fully factored** at general (G, ρ) on the
  even-extent torus, at **every real β**: the sesquilinear form, its conjugate
  symmetry (hence reality of the diagonal), the bridge to the bare-pullback
  reading of ⟨θ(F)·F̄⟩, and the exact kernel identity in split variables.
- **Positivity stands at β = 0** for every observable supported on the strict
  positive half.
- **Positivity at general β is reduced losslessly to one named lemma** — the
  Gram factorization of the Gibbs weight in split variables (`osForm_nonneg_of_gram`
  is an if-and-only-if-shaped criterion: it assumes *only* the factorization and
  concludes nonnegativity, at any real β, no sign hypothesis used). Supplying
  that factorization for the Wilson weight is the character-expansion step,
  whose harmonic-analytic input — Peter–Weyl orthogonality on a general compact
  group — **is not in the pinned Mathlib (v4.35.0-rc3)**. Priced **XL /
  Mathlib-blocked**.

**PARTIAL-δ is therefore NOT claimed.** The gauntlet's δ is A + B with B's
positivity proved; here B's *form* stands whole and its *inequality* is the
single open clause, fenced on both sides (β = 0 below, the criterion above).
Positivity itself remains a true theorem (Osterwalder–Schrader / Glimm–Jaffe);
it is unproved here, not killed.

**Finite-volume OS axiom check only.** No Hilbert space (that is 1b-C), no
transfer matrix (1b-D), no thermodynamic or continuum limit.
**Clay parts closed: 0.**

## The observable class: the strict positive half (and why)

Reflection is 1b-A's between-sites reflection θ on direction 0 of the
even-extent torus. Links split by base time into the positive half
`halfLinks` (t < N/2), its complement, and the **reflection-fixed stratum**
`planeLinks` — the time links at t = N/2−1 and t = N−1. The OS observable
class of this module is the **strict positive half**
`posLinks = halfLinks \ planeLinks`. The exclusion of the plane links is
forced, by two finite counterexamples (hand computations, recorded here as
the reason for the class choice; they are not Lean theorems of the module):

1. **A plane-link observable breaks the form at β = 0.** Take
   G = ℤ/3, F(U) = ω^z − ω^{2z} where z is the value at one
   fixed-stratum time link. Then θF·F̄ averages to the value of
   (z − z²)² over z ∈ {0, i√3, −i√3}-valued F, i.e. (0 + (−3) + (−3))/3 =
   **−2 < 0**. No positivity statement over a class containing plane
   links is true.
2. **The stratum cannot be held fixed.** With G = U(1), d = 1, ρ = id and
   the stratum variables held at phase γ, a single-link character
   observable gives the form value I₁(β)·e^{iγ} — not even real. The
   integration over the plane variables is load-bearing; the naive
   "positive kernel at fixed plane variables" argument is false (a single
   crossing plaquette's trace is a Frobenius pairing of *rectangular*
   form — the two sides' link matrices are sandwiched by *different*
   stratum matrices — and products/series over crossing plaquettes
   preserve that rectangularity).

The strict-half convention matches the literature's: the reflection plane
sits between sites, and the plane links belong to neither open half.

## What stands (module inventory)

**§1 Links.** `halfLinks`, `negLinks` (= complement, reducible, so 1a's
`splitEquiv` applies verbatim), `planeLinks` (the fixed stratum),
`posLinks`; membership characterizations; the mirror transport of links:
reflection maps the strict positive half bijectively onto the
non-stratum part of the negative half and back (`reflLink_mem_posLinks`,
`reflLink_mem_negLinks`).

**§2 Mirror.** `mirrorP` (the negative-half restriction of a reflected
configuration, read as a strict-half configuration, with the direction-0
inversion), `restrictPos`; `reflConfig_apply_pos` (θ on a configuration,
restricted to the strict half, *is* the mirror of its negative half); the
two marginal identities `integral_mirrorP`, `integral_restrictPos`.

**§3 Factors.** Plaquettes of the positive class read only strict-half
links (`plaquetteDensity_eq_of_agree_posLinks`); the half-action
`halfActionP` (S₊ as a function of the strict-half variables alone);
`wilsonActionMinus_eq_halfActionP` (S₋ is the *same* half-action of the
mirrored variables — 1b-A's S₊(θU) = S₋(U) composed with the factorization).

**§4 Form.** `reflObs F = conj ∘ F ∘ reflConfig` (the gauntlet's ruled
convention; conjugation spelled `starRingEnd ℂ`); `osForm β F H`; conjugate
symmetry `osForm_conj_symm` at **every real β** (cheap: substitution
U ↦ θU via 1b-A's `gibbsMeasure_map_reflConfig` plus involutivity);
`osForm_self_im`; full sesquilinearity; `osForm_bare_eq` — the task's
literal ⟨θ(F)·F̄⟩ with the bare coordinate pullback equals the diagonal,
the two readings coinciding because the diagonal is real.

**§5 Kernel.** `integral_gibbsMeasure` (the Gibbs integral as Z⁻¹ times
the Haar integral of density-times-observable, the plumbing 1b-C will
also need); `wilsonAction_split_half` (in split variables the total
action is halfActionP(restrict) + halfActionP(mirror) + S₀ — 1b-A's split
with both halves factored); **`osForm_eq_kernel`**: for
strict-half-supported F with factor f,

  osForm β F F = Z⁻¹ · ∫∫ exp(−S(y₊, u₋)) · conj(f (mirror u₋)) · f (restrict y₊)

over the product Haar measure of the two halves — the exact point where
positivity becomes a property of the crossing kernel, at every real β.

**§6 Positivity pieces.** `osForm_zero_eq` / `osForm_zero_nonneg`
(β = 0 stands: the weight is 1, the kernel integral factors by
`integral_prod_mul`, both marginals collapse to the strict half, and the
diagonal is W·W̄ with W = ∫ f — hence nonnegative real part, zero
imaginary part). `measurePreserving_restrictPos`,
`measurePreserving_mirrorP` (the §2 transports are genuinely
measure-preserving). **`osForm_nonneg_of_gram`** (the Gram criterion of
the verdict above).

## The missing lemma, named and priced

**Lemma (open).** For the Wilson weight at β ≥ 0 there exist a finite
index set ι and bounded measurable features Ξᵢ on the strict half with

  exp(−S(y₊, u₋)) = ∑ᵢ conj(Ξᵢ (mirror u₋)) · Ξᵢ (restrict y₊)

in split variables — equivalently, the stratum-integrated crossing
kernel is positive semidefinite.

The standard proof expands each crossing plaquette's Boltzmann factor
exp((β/d)·Re tr ρ(g)) in matrix coefficients of tensor powers of ρ
(nonnegative coefficients, since exp of a character-generating class
function), writes each crossing trace as a Frobenius pairing, and
integrates the plane variables by **Schur orthogonality / Peter–Weyl**
on the compact group G, which collapses the rectangular pairings into
Gram sums. The pinned Mathlib's `RepresentationTheory/` covers
finite-group and algebraic representation theory; no Peter–Weyl theorem
and no orthogonality of matrix coefficients for a general compact group
was found in it. **Price: XL, blocked on Mathlib infrastructure** —
building Peter–Weyl for compact groups in Lean is a project of its own,
not a 1b-B-sized step. Two cheaper-looking detours are closed by the
counterexamples above: fixed-stratum positivity is false, and the
difference-kernel exp(c·Re tr ρ(x⁻¹y)) (which *is* positive definite for
c ≥ 0, elementarily) cannot be reached, because the crossing factor is
not a function of a difference of one-variable functions of the two
sides — the stratum matrices sandwich the two sides differently.

## Accommodations and notes

- `[MeasurableInv G]` is carried (inherited from 1b-A's Gibbs section).
- Continuity of `repMatrix ρ` is passed as an explicit hypothesis
  (`hρcont`) wherever the Gibbs-measure API requires it, rather than as a
  section variable.
- The results of §§4–5 hold at **every real β**; the criterion of §6 is
  also β-sign-free. The open clause is not a sign issue — it is the
  Gram factorization itself.
- Sesquilinearity is stated for bounded measurable observables (the
  natural domain on a probability space); the positivity statements use
  only the factorization form `F U = f (restriction of U)`, so they apply
  to every strict-half-supported observable with a measurable factor f.

## What this does not do

No OS Hilbert space, no reconstruction, no transfer matrix, no gap, no
limit of any kind. Pitch 4's remaining queue is unchanged below this
landing: 1b-C (OS space) can consume §5's kernel identity and §4's form;
1b-D remains downstream of both. Stage 3c's uniform estimates remain
priced research-scale/open elsewhere in the pitch. **Parts of any
official Clay statement closed by this stage: 0.**
