# β↔A symmetry test — results (2026-10-08)

Tier T4 numerical. Script: `scripts/beta_A_symmetry_test.py`.
Numbers: `scripts/beta-A-symmetry-results.json` (seeds 2026 / 202607 inherited).

## What was tested

Jeff's adjoint-primitives thesis (heat and magnetism as the two physical
primitives in thet) predicts a possible **involutive symmetry exchanging
the β (thermal) and A (gauge/magnetic) axes** of the measured landscapes.
Tested on the two full (β, A) landscapes on record:

- `||φ(β,A)||_F` active-mode flux landscape, 13×10
  (`scripts/beta-flux-results.json`, β log-spaced 0.1–10, `t = ||A₁||/||D||`
  ∈ [0, 0.05]);
- `S(β,A)` thermal magnetophase entropy landscape, 13×10
  (`scripts/magnetophase-results.json`, same grid).

The non-Gibbs active-mode landscape (`scripts/non-gibbs-magnetophase-results.json`)
has **β fixed at 1** (axes are drive × A), so the swap test does not apply to
it; it is used as an independent check of the A-profile shape.

Normalized coordinates: `u` = normalized log₁₀β ∈ [0,1] (13 pts),
`v` = normalized A-strength t/t_max ∈ [0,1] (10 pts).

## Test 1 — strict swap in normalized coordinates

Each landscape bilinearly interpolated onto a common 65×65 `(u,v)` grid `G`;
residual `R = ||G − Gᵀ||_F / ||G||_F` (raw, min–max-normalized, and log-scale):

| landscape | R_raw | R_minmax | R_log |
|---|---|---|---|
| flux `\|\|φ\|\|` (active) | **1.076** | **1.097** | 0.253 |
| entropy S | 0.086 | **0.687** | 0.200 |

The flux landscape's swapped version differs by *more than the signal itself*.
The entropy R_raw looks small only because the Frobenius norm is dominated by
the constant ln 4 ≈ 1.386 floor (values span 1.386–2.277); after offset removal
the *shapes* mismatch by 69%. Strict involutive symmetry: **rejected** on both
landscapes.

(The equilibrium flux landscape is identically zero — trivially
swap-symmetric and content-free; not a symmetry of the thesis.)

## Test 2 — separability (structure diagnosis)

- Flux: SVD rank-1 energy fraction **1.000000**; `F(β,A) = β·s(A)` with
  β-linearity holding to 8.3e-16 relative. Exactly separable: β is the whole
  story, A is a multiplicative dressing.
- Entropy: rank-1 fraction 0.997 (0.974 for `S − ln4`) — *not* separable; the
  A-effect is β-dependent (strong at low β, vanishing at high β).

## Test 3 — weak form: monotone reparametrization

**Corner theorem.** If onto strictly-increasing warps
`φ, ψ : [0,1] → [0,1]` made `M(u,v) = L(φ(u),ψ(v))` symmetric, then onto +
increasing forces `φ(0)=ψ(0)=0`, `φ(1)=ψ(1)=1`, and `M(0,1) = M(1,0)` gives the
necessary condition **`L(0,1) = L(1,0)`**. (Onto-ness is the standard meaning
of "reparametrization of the axis"; without it one may zoom into any flat
patch and the question is vacuous.)

| landscape | L(0,1) = L(β_min, A_max) | L(1,0) = L(β_max, A_min) | rel. diff |
|---|---|---|---|
| flux | 164.38 | 16416.22 | **0.990** (factor ~100) |
| entropy | 1.76763 | 1.38629 | **0.216** (0.381 nats) |

Weak form: **rejected** on both landscapes, rigorously, from two data points.

Two independent structural kills agree:

1. **Flux profile monotonicity.** The β-profile (at A=0) is strictly monotone
   (Spearman 1.0, 0 critical points); the A-profile (at β=1) is **non-monotone**:
   Spearman 0.36, one interior minimum at t≈0.0071, dipping 0.14% below its
   endpoints (~10¹¹× above the 1e-15 numerical floor — structural, not noise).
   Since the landscape is exactly separable, weak symmetry would require the
   log-profiles to match under a monotone warp — impossible, because
   monotone∘monotone is monotone and the A-profile isn't.
2. **Entropy ln 4 plateau.** `{S = ln 4}` contains the rectangle
   `[11/12, 1] × [0,1]` (β ≥ 6.81 × all A, numerically exact to 16 digits —
   the 4-fold-degenerate ground state). A symmetric `M` would reflect this
   rectangle to `[0,1] × [11/12, 1]`, forcing `M(0,1) = ln 4`, i.e.
   `S(β_min, A_max) = ln 4` — but it is 1.7676. Contradiction.

## Non-Gibbs corroboration (β = 1)

Active flux vs A at drive 0.35: ratio rises to a **peak of 1.0207 (2.07%)**
at t≈0.0188, then slightly declines — non-monotone (one interior maximum),
a small saturating modulation. Same moral as the Gibbs-active A-profile
(which instead dips then rises 0.14%): **A is a small non-monotone dressing;
β is the exact monotone driver.** No axis of the data looks like the other
under any monotone rewarp.

## Verdict

**β↔A symmetry: ABSENT — clean negative, with numbers.**

- Strict swap residual: 1.08 (flux), 0.69 shape-level (entropy).
- Weak form (any onto monotone reparametrization): killed by the corner
  condition — anti-diagonal corners differ by factor ~100 (flux) and
  0.381 nats (entropy) — plus two independent structural kills
  (A-profile non-monotonicity; ln 4 plateau rectangle).
- Mechanism of failure, measured: β-scaling is *exactly* linear (theorem
  `modularFlux_betaScale`, 8e-16); A-dressing is a 0.14% U-shaped modulation
  (Gibbs-active) / 2.07% saturating hump (non-Gibbs-active). The two axes play
  qualitatively different roles — a linear driver vs. a small non-monotone
  dressing — so no involution can exchange them, strictly or weakly.

Caveat: the exact dip/hump location in the A-profile is draw-dependent
(seeded 1-form, seed_A 202607); the qualitative facts it rests on — exact
β-linearity, small non-monotone A-modulation — are not.

## Files

- `scripts/beta_A_symmetry_test.py` — analysis script
- `scripts/beta-A-symmetry-results.json` — all numbers
- `scripts/beta-A-symmetry-results.md` — this file
