# Pitch 4, Stage 1b-B — the Gram clause, Route C (T0 + criterion variant + U(1) discharge)

**Date:** 2026-10-23
**Module:** `lean/ThetLogos/LatticeGramSeries.lean` (new; 3,006 lines,
109 strict theorem/lemma declarations, 38 defs, 0 sorry).
**Charter:** `whitepaper/gram-clause-scoping-2026-10-23.md` (§6:
T0 + Route C as one brick, commissioned by Jeff's word "route c",
2026-10-23).
**Verdict: STANDS** — at the charter's honest label: **Stage 1b-B
positivity T1 for U(1); the clause at general (G, ρ) remains open
(Route B).**
**NO CLAIM.** Parts of any official Clay statement closed: 0.

## What landed

**T0 — anatomy: both scoping obstructions CONFIRMED.**
(i) *Plane-link dependence:* the literal finite pointwise `hgram`
of `osForm_nonneg_of_gram` is **not satisfiable by the Wilson
weight** at β ≠ 0: `restrictPos`/`mirrorP` forget the
reflection-plane (stratum) links, and the crossing action genuinely
depends on them — varying one stratum link at fixed
(restrictPos y, mirrorP u) moves exp(−S) while any Gram right side
stands still (explicit family U_s at N = 2: S(U_s) = 6β(1 − Re s)
against S(U_1) = 0). **Status: paper proof** (finite plaquette-star
check by hand at N = 2) — recorded at that rank; it is not a Lean
theorem of the module. (ii) *Finite-rank obstruction:* a finite
Gram sum forces every kernel section into a finite-dimensional
span — formalized as `finite_gram_sections_span` (T1) — while the
U(1) crossing kernel's Fourier coefficients are all ≥ 0 with full
support at β ≥ 0: the Gram expansion is a **series**, not a finite
sum. The proved finite criterion stands untouched; its hypothesis
does not hold for the Wilson weight, and the 1b-B dossier carries
an addendum saying so.

**T1 — the criterion variant STANDS (T1, general (G, ρ), any real β).**
`osForm_nonneg_of_gram_integrated`: if the Gibbs weight in split
variables is a convergent Gram series over a countable index with
dominated features, and its two stratum marginals factor through
one common strict-half feature with nonnegative real damping
factors dA, dB ≥ 0, then the OS form's diagonal is a nonnegative
real (the proof exhibits it as Z⁻¹ • ∑'ᵢ (dAᵢ·dBᵢ)·‖∫ Ξᵢ f‖²).

**Route C — the U(1) discharge STANDS (T1).**
For G = Circle with the defining representation, at every even N
and every β ≥ 0: the Gram identity holds pointwise in split
variables as a series over Fourier-mode tuples of the crossing
plaquettes (`gram_identity_circle`), with features built from the
half actions and weights wR = ∏ exp(−β)·I_{n}(β), where `besselI`
is built from the exponential series (the pinned Mathlib has no
usable Bessel API; `hasSum_fourier_exp_circle` proves
exp(β·Re w) = ∑'ₙ Iₙ(β)·wⁿ from the exponential series directly);
the marginals hold by Fourier orthogonality on the circle
(`marginalA`, `marginalB`); and the discharge
`osForm_circle_nonneg` concludes: OS positivity of the U(1) Wilson
theory at every β ≥ 0 is T1.

## Verification (parent, 2026-10-23)

- Targeted build on the exact shipped text: `lake build
  ThetLogos.LatticeGramSeries` — **exit 0**, .olean present.
- Parent recount on comment-stripped source: **109 strict /
  109 attribute-inclusive, 38 defs** — matches the builder's count.
- Sorry census: **0** in code and in the raw file.
- `#print axioms` on all eight headlines
  (`osForm_nonneg_of_gram_integrated`, `gram_identity_circle`,
  `marginalA`, `marginalB`, `osForm_circle_nonneg`,
  `hasSum_fourier_exp_circle`, `tsum_besselI_int`,
  `finite_gram_sections_span`): each **[propext, Classical.choice,
  Quot.sound]** — standard axioms only.
- **Parent correction at full rank:** the module header as built
  first cited two lemma names (`hgram_stratum_blind`,
  `hgram_impossible_circle`) that do not exist in the module —
  T0(i)'s status is a paper proof, and the header was corrected
  to say so before this dossier shipped; the green parent build
  above is on the corrected text.

## Accommodations (from the builder's memo, accepted)

Marginals in two-selector (dA/dB) form; no separate CB ≥ 0
hypothesis (domination forces it); the Gram index is the stratum's
Fourier lattice; Bessel facts built from scratch; features proved
continuous (stronger than the AEStronglyMeasurable the criterion
consumes); `circleRep` reused from the corpus's LatticeGauge.

## Fences

β ≥ 0 spent only where the charter puts it (coefficient
nonnegativity, feature bounds); the criterion and the Fourier
input are sign-free. Even N; finite volume only. No OS Hilbert
space (1b-C), no transfer matrix (1b-D), no limits, no gap.
General (G, ρ) is **not** discharged: Route B (averaging, L,
chartered in the scoping document) is the named next brick.

**Program census after this landing: 4,189 strict / 4,238
attribute-inclusive; 137 counted modules.**
