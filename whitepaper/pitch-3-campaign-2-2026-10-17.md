# Pitch 3, Campaign 2 — Bosonic Finite-Mode Interaction (2026-10-17)

**Campaign verdict: STANDS in every scoped item except one — essential
self-adjointness is PRICED (see B2).**
**Pitch 3 verdict: the pre-named PARTIAL of the scoping (§6), narrowed to a
single clause** — stated in full at the end of this dossier.

Parent-verified firsthand: targeted build green (2,704 jobs; full project
3,325 jobs per the builder), all six headline axiom checks exactly
`[propext, Classical.choice, Quot.sound]`, zero `sorry`/`admit` (grep-clean,
code and prose).

**Module:** `lean/ThetLogos/BosonicInteraction.lean` — 1,956 lines,
**69 theorem/lemma declarations + 21 definitions**. (Attribute-inclusive raw
grep gives 75 `(theorem|lemma)` hits; the 6 extra are docstring prose,
disclosed.) Bosonic environment only; the fermionic parent is never imported
(the `adag` clash is respected by construction). One disclosed build
accommodation: `hamIntBosSector_spectral` carries
`set_option maxHeartbeats 1600000` (a defeq cost in the Hermitian spectral
application); its axiom check is clean.

Mandatory §6 header clause is carried in the module header, including:
finite modes; eigenvalue-sense/windowed gaps stated exactly; matter
self-interaction only; no gauge field, no continuum, no Poincaré; uniform
bosonic persistence false in general and not claimed; **not** the interacting
Yang–Mills mass gap.

## B1 — Wick calculus on the finite-particle domain: STANDS

Monomial calculus on `Dom d` (`monoC`/`monoPhi`/`monoCoef`) with the
√-coefficient basis formula, support injectivity, and number-relative
coefficient and column-sum bounds (`intBoundBos W = 2 · couplingMassBos W`).
The symmetrized quartic `intOpBos W` is proved **symmetric on `Dom d` for
every coupling tensor W** (`intOpBos_isSymmetric`).

## B2 — Self-adjointness package: STANDS in three scoped senses; the fourth is PRICED

Proved:
1. **Symmetry** of `hamIntBos lam W g` on the dense domain `Dom d`
   (`hamIntBos_isSymmetric`; density `dom_dense`).
2. **Sectorwise self-adjointness with full diagonalization**: on every
   finite particle sector, `hamIntBosSector` is symmetric with an
   orthonormal eigenbasis and real eigenvalues (`hamIntBosSector_spectral`,
   via the Hermitian spectral theorem; sector finite-dimensionality proved
   from the finite configuration basis).
3. **LinearPMap formal self-adjointness**: `hamPMap` is a densely defined
   partial linear map with `hamPMap ≤ hamPMap†` (`hamPMap_le_adjoint`, via
   `IsFormalAdjoint.le_adjoint`).

**Not proved — PRICED:** essential self-adjointness of the closure /
equality `hamPMap = hamPMap†` as partial maps. Mathlib has no LinearPMap
closure operator producing equality from sectorwise data and no Kato–Rellich
theorem; the closure's domain is an ℓ²-growth condition across infinitely
many sectors. This was §6's named "single hardest priced step in the pitch,"
and it remains priced. No text may call the bosonic Hamiltonian self-adjoint
without one of the three scoped senses above attached.

## B3(i) — Exact diagonal gap: STANDS

`hamiltonianDensBos_gap_exact`: under `0 < Δ`, the **strong dichotomy**
`∀ i, Δ ≤ lam i` (no zero modes), `0 ≤ g`, `0 ≤ U i j`: every eigenvalue is
exactly **0 or ≥ Δ**, uniformly over all sectors.

Scoped FALSE claim caught inside the build (recorded in-doc): the exact gap
under the *weak* dichotomy fails — two zero modes a < b with U a b > 0 give
eigenvalue g·U a b ∈ (0, Δ) at the one-particle-each configuration. The
weak-hypothesis form is proved only in dominated form
(`hamiltonianDensBos_eigenvalue_form`). Same honesty pattern as Campaign 1.

## B3(ii) — Windowed persistence: STANDS

`hamIntBos_gap_persistence_windowed`: for an eigenvector in sector `n`,
under the threshold
`2 · (‖g‖ · intBoundBos W · (n+2)²) ≤ Δ/4`, the eigenvalue's real part is
either within `‖g‖ · intBoundBos W · (n+2)²` of 0 or ≥ Δ/2. The **window is
in the statement**, as scoped. Proof by sector transport (maximal-coordinate
/ Gershgorin-type step on the column-sum bound).

## The scoped FALSE claim, disproved in-module

**Uniform gap persistence for general bosonic quartic coupling is FALSE —
proved, not merely unclaimed.** `densHamEigBos_unbounded_below`: attractive
pair coupling (U a b = −1, g = 1) gives eigenvalue
(lam a + lam b)·n − n² at the (n, n) configuration — below every bound for
large n. This is the proved reason B3(ii) is windowed.

## Certificate: STANDS

`densityIntBos_not_dgamma`: the bosonic density interaction is `dgammaBos M`
for **no** one-particle matrix M (whenever some U a b ≠ 0). Interaction is
provably not a one-particle lift, for both statistics now.

## Pitch 3 verdict (against the scoping §6, applied exactly as written)

§6 item 2 requires, for the unqualified headline, bosonic "essential
self-adjointness proved via its sector decomposition." Sectorwise
self-adjointness **was** proved; essential self-adjointness (closure
equality) was **not**. The pre-agreed consequence therefore applies, and
this dossier does not soften it:

> **Pitch 3 STANDS for fermionic interaction (Campaign 1, whole). For
> bosonic interaction: the Wick calculus with relative bounds, the exact
> diagonal gap, windowed persistence, sectorwise self-adjointness, and
> LinearPMap formal self-adjointness all stand; essential self-adjointness
> is priced.** The §6 headline sentence ("…both statistics, with
> self-adjointness proved…") is **not** spendable in unqualified form.

The landing **exceeds** the scoping's named PARTIAL shape on every other
axis — that shape (B1 + B3(i) only, "defined and symmetric") omitted
B3(ii), the sectorwise diagonalization, the LinearPMap package, and a
*proved* (not merely recorded) collapse counterexample. The gap between
this landing and the full §6 headline is exactly one theorem: essential
self-adjointness of the bosonic interacting Hamiltonian — now the pitch's
sole remaining priced item, with its obstruction named (no closure API,
no Kato–Rellich; the core/ℓ²-growth domain argument is the work).

## Program total

1,896 (through SchrodingerDynamics) + 69 = **1,965 declarations**.
