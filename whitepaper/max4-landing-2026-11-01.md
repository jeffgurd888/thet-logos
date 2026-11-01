# MAX-4 LANDING DOSSIER — 2026-11-01

**Item:** MAX-4 (the Poincaré brick), fired under auto-fire from
MAX-3's registered re-price: discharge clause 4 of `maxwellM5` —
the gap as a bound — and assert M5 in FULL if it closes.

**Status: FULL. Clause 4 closed; `maxwellM5` is asserted in FULL
as `maxwellM5_full`.** Card MAX's verdict is thereby upgraded from
MAX-3's PARTIAL: the five-clause statement of the finite lattice
Maxwell operator's spectrum now stands whole at general Even N.

**Artifact:** `lean/ThetLogos/MaxwellPoincare.lean` — strict 54,
defs 9 (in the registered band). Verified by the coordinator in
the main tree (build green, 3660 jobs); `maxwellM5_full`,
`clause4`, and `maxwellQuad_gap_bound` each on exactly
`[propext, Classical.choice, Quot.sound]`. No `maxHeartbeats`
raise anywhere in the module (improving on MAX-3's disclosed
scoped raise).

## Clause 4 as landed (verbatim)

```lean
theorem clause4 (hN : Even N) :
    ∀ μ : ℝ, Module.End.HasEigenvalue (maxwellOp N) μ →
      μ = 0 ∨ 4 * Real.sin (Real.pi / (N : ℝ)) ^ 2 ≤ μ
```

`maxwellM5_full (hN : Even N) : maxwellM5 N hN` combines
`maxwellM5_spectrum_part` (MAX-3's clauses 1, 2, 3, 5) with
`clause4`. House language, now exact in both directions:
**4·sin²(π/N) is attained as an eigenvalue (MAX-3) AND is a lower
bound on every nonzero eigenvalue (MAX-4)** — it is the spectral
gap of `maxwellOp N` at general Even N, as a theorem.

## Route

Complex Fourier analysis on (ZMod N)³. An eigenvector with
eigenvalue μ ≠ 0 is orthogonal to the kernel (`maxwellOp_form_symm`);
orthogonality to gauge modes forces `maxwellDiv θ = 0` pointwise;
orthogonality to constant direction fields forces zero component
means (via MAX-2's kernel characterization). Then
`maxwellQuad_gap_bound`: the plaquette pair form of `maxwellQuad`,
Parseval per pair, the per-momentum Lagrange identity (defect term
= the Fourier coefficient of the divergence, hence 0), the
multiplier bound `Σⱼ 4 sin²(π(kⱼ).val/N) ≥ 4 sin²(π/N)` at k ≠ 0,
the zero-momentum term killed by the means. Registered-statement
note: `maxwellQuad_gap_bound` carries no `2 ≤ N` hypothesis and
none was added — at N = 1 the gap factor is `4 sin² π = 0` and the
bound reduces to nonnegativity inside the proof.

## Fences

NO CLAIM — no Millennium problem is claimed solved or advanced.
This is the spectral gap of the FINITE lattice Maxwell operator —
a free-field lattice object. It is not the Yang–Mills mass gap,
not a continuum statement, and no dial moves: dials 0/4. The
MAX claims-registry card's verdict is FULL as of this landing; its
pre-written sentences remain in Jeff's review-and-amend state and
nothing has been posted.

**Census after landing: 10,784 strict / 10,877 total / 364 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
