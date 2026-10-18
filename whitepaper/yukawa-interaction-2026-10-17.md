# Yukawa Brick — Dossier

Module: `lean/ThetLogos/YukawaInteraction.lean` (2,355 lines; 119 theorems/lemmas
by the strict line-initial count on the comment-stripped file — the raw count is
also 119, no prose hits; 44 defs; zero `sorry`/`admit` in code).
Commission: gauntlet parked-fleet §6 (priced M–L, product-config presentation).
Build: pinned Mathlib v4.35.0-rc3, `lake build ThetLogos.YukawaInteraction` —
**Build completed successfully (3313 jobs)**.
Axiom audit (`#print axioms` in-module, §7): `hamYuk_isSymmetric`,
`hamYukPMap_le_adjoint`, `hamFreeJBand_spectral`,
`hamYuk_gap_persistence_windowed`, `yukawaIntJ_not_diagonal` each depend on
exactly `[propext, Classical.choice, Quot.sound]`.

## Verdict: STANDS (a–f at the scoped senses)

## What was built

A finite-mode fermion–boson interaction of Yukawa SHAPE, machine-checked, in
the product-config presentation: the joint space is `lp` over product
configurations `Finset (Fin df) × Config db` (NOT a completed tensor product —
the two factors share one orthonormal basis, as in both parent campaigns).
The interaction is
`H_Y = Σ_{i,j,k} (Y_{ijk} + conj Y_{jik}) • (a†ᵢ aⱼ) ⊗ (a†ₖ + aₖ)`,
a fermionic density/current bilinear tensored with a bosonic field, and the
total Hamiltonian is `H = H_free + (g : ℂ) • H_Y` with `g : ℝ` real and
`H_free` the joint diagonal operator whose eigenvalue on `(S, c)` is the
fermionic `freeEig` plus the bosonic number-weighted energy.

## Per-rung outcomes

- (a) Product space, product finite-particle domain, coupling operator:
  STANDS (§0, §1, §3). Cross-factor commutation is a THEOREM (§1, four
  commutation identities on the nose), not a convention.
- (b) Wick-type coefficient calculus: STANDS (§2). The coupled monomial's
  matrix element factors (CF1: density matrix element × field matrix
  element); the field coefficient bound is output-side (CF2:
  `≤ sqrt (bTot c' + 1)`); the symmetrized total coefficient is hermitian
  in the joint indices (CF3).
- (c) Symmetry of H_Y and of H on the product domain: STANDS (§4), via one
  generic transported-symmetry lemma (double induction on the product
  domain) instantiated at CF3 and at the real diagonal.
  DEVIATION FOUND AND FIXED DURING THE BUILD (kernel-caught): the coupling
  `g` must be REAL, as in both Pitch 3 campaigns. For complex `g` the
  operator is not symmetric — the two inner-product slots produce
  `conj g` versus `g`. The module takes `g : ℝ` throughout; named here and
  in the `hamYuk` docstring.
- (d) Relative bounds with explicit constants: STANDS (§5), in the
  output-side coordinate form: at a maximal coefficient `q₀`,
  `‖(H_Y f) q₀‖ ≤ yukBound Y * ‖f q₀‖ * sqrt (bTot q₀.2 + 1)` with
  `yukBound Y = 4 * Σ ‖Y i j k‖` — two from symmetrization, two from the
  field's two preimages per output (the two-point support argument: the
  density factor has the single preimage `densPre`; the field factor has
  exactly the two preimages `c' ∓ single k 1`). This is the
  `(tot + 1)^{1/2}` growth made explicit per output configuration.
- (e) Self-adjointness in Pitch 3's scoped senses ONLY: STANDS (§4).
  (i) `H` is symmetric on the dense product domain and its partial map
  satisfies `hamYukPMap ≤ hamYukPMap†` (formal self-adjointness,
  `IsFormalAdjoint.le_adjoint` at the dense domain). (ii) Sectorwise: the
  free Hamiltonian preserves every bosonic band `jBand N` (proved
  finite-dimensional), and its band restrictions are diagonalized by an
  EXHIBITED orthonormal eigenbasis — the joint basis restricted to the
  band (`jBandBasis`, orthonormal by `jBandBasis_orthonormal`), with
  eigenvalues the joint free eigenvalues (`hamFreeJBand_spectral`).
  PRESENTATION NOTE: the spectral statement is in the exhibited-basis
  form rather than the abstract `Fin (finrank)` form used in Campaign 2;
  the abstract form's `Module.finrank` instance unification is
  prohibitively expensive on this nested-submodule type (it did not
  elaborate within any tried heartbeat budget, while the whole rest of
  the module elaborates in ~30 s), and the exhibited form is the stronger
  exhibit in any case: it names the eigenbasis and the eigenvalues.
  The interaction does NOT preserve bands — it maps band `N` into band
  `N + 1` (proved), because the field changes the total boson number by
  ±1 — so there is no bandwise spectral theorem for `H` itself, and none
  is claimed.
  ESSENTIAL SELF-ADJOINTNESS IS NOT PROVED and is not claimed: it is
  Pitch 3's priced remainder, verbatim (pinned Mathlib has no
  LinearPMap closure-equality API from sectorwise/domain data and no
  Kato–Rellich theorem).
- (f) Gap persistence: STANDS IN WINDOWED FORM ONLY (§5). With per-mode
  gap hypotheses at `Δ` on BOTH free factors (strong dichotomy: every
  joint free eigenvalue is `0` or `≥ Δ`), an eigenvector of `H` supported
  in bosonic band `N` at the explicit threshold
  `2 * (‖g‖ * yukBound Y * sqrt (N + 1)) ≤ Δ / 4` obeys
  `μ.re ≤ ‖g‖ * yukBound Y * sqrt (N + 1) ∨ Δ / 2 ≤ μ.re`, with `μ`
  proved real. NO uniform (band-independent or coupling-independent)
  persistence is claimed: it is FALSE in general for bosonic factors —
  Campaign 2's proved collapse counterexample embeds at the fermion
  vacuum sector — so the window is in the hypotheses from line one.

## Additional exhibits

- The joint vacuum `(∅, 0)` is an exact `0`-eigenvector of `H` for every
  coupling (§6): the density annihilates the fermion vacuum before the
  field can act.
- Not-a-dΓ certificate (§6): if some diagonal coupling `Y i i k` has
  nonzero real part, `H_Y` is not a diagonal operator in the joint basis
  for any eigenvalue function — its vacuum-sector matrix element
  `({i}, 0) → ({i}, single k 1)` is exactly `2 * Re (Y i i k) ≠ 0`. It is
  not a function of the joint free eigenvalue data.

## Mandatory fences (verbatim substance)

- FINITE MODES ONLY: `df` fermionic modes, `db` bosonic modes, both
  finite. No infinite-mode limit, no continuum limit is taken or claimed.
- This is a matter coupling of Yukawa SHAPE only (fermion bilinear ×
  boson field). It is NOT the Standard Model Yukawa sector: no Higgs
  mechanism, no flavor or chirality structure is present or claimed.
- No gauge field appears. No continuum. This is NOT a mass gap, and it
  closes no part of any Millennium Problem statement.
- ESSENTIAL SELF-ADJOINTNESS IS NOT PROVED. As in Pitch 3 (Campaign 2),
  it is the priced remainder: pinned Mathlib has no `LinearPMap`
  closure-equality API from sectorwise/domain data and no Kato–Rellich
  theorem; the closure domain of `H` here is an ℓ²-growth condition on
  coefficients, not a band. The scoped senses of (e) are what stands.
- UNIFORM (coupling-independent, band-independent) gap persistence is
  FALSE in general for bosonic factors (Pitch 3 Campaign 2's in-module
  collapse counterexample embeds at the fermion vacuum sector): only the
  windowed statement of (f) is claimed, with the window in the hypotheses
  from line one.
- `BosonicInteraction` does NOT co-import with the fermionic stack (the
  censused `numberOp` collision in `BosonicAssembly`, adag-repair dossier
  2026-10-17); the bosonic coefficient machinery above `BosonicFock`'s
  parent API is therefore rebuilt inside this module on the product
  configurations, in the same style. No statement is routed through
  `BosonicAssembly`.
