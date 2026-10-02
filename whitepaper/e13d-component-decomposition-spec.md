# E13-D — Full-Representation Component Decomposition ("building blocks")

*Spec 2026-10-01 (Jeff: spec requested). Tier T4 numerical. LOCAL — not pushed.*
*Parent: Engine 13 (Relational Spectral Dynamics). Quarantine wall holds.*

## Motivation

E13-A ran the Connes distance on the Option-A represented algebra and found a
thin geometry: 1-dimensional plus disconnected components, 6 finite distances
all equal to 0.4065 GeV⁻¹, 78 infinite pairs. The thinness was diagnosed as the
embedding's: `common.pi` (Option-A) kills the pure M₃(ℂ) summand — in
`embedSM`, the color matrix enters only multiplied by the electroweak
components, so a pure-color element maps to zero.

E13-D removes that artifact. Work with a representation of the **full**
A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ) on H_F = ℂ³² in which every summand acts nontrivially,
decompose the pure state space into its finite-distance connected components,
and measure the inter-component distances. The components are the "smaller
building blocks": states at infinite spectral distance cannot reach each
other, so each connected island is an irreducible piece of the finite
geometry. (Precedent, Tier-2 textbook: in the SM triple the finite space has
discrete sheets and the Higgs is the inner fluctuation in the discrete
inter-sheet direction.)

## D1 — Faithful full representation

Construct π_full: A_F → M₃₂(ℂ) extending `common.embedSM` so that the pure
M₃(ℂ) summand acts nontrivially (u1 = 0, q = 0, color ≠ 0 must give a nonzero
operator). Document the construction against `lean/ThetLogos/
FiniteSpectralTriple.lean`. Numerical faithfulness check: ker π_full = {0}
(smallest singular value of the representation map > 0).

**Correction 2026-10-01 (build):** `common.embedSM`/`pi` are *bilinear* in
(q, color) — verified numerically (`embedSM((0,q,m)) ≠ embedSM((0,q,0)) +
embedSM((0,0,m))`); the Lean proves `pi_pure_color_zero` as a theorem about
the same map. So π_full is a probe EMBEDDING — block_diag of the Lean's
quadratic Option-A embedding and a genuine linear unital *-representation
ρ₂ = diag(u1·I₄, I₂⊗q, color, color, u1·I₂) on the probe block — not a linear
*-homomorphism overall. The "faithfulness" check is linear independence of
the 24 generator images (every summand resolved). The Connes distance needs
only the order-unit space (span_ℝ of Hermitian parts) + D_F, so the metric
is unaffected; D2 states are supported on the linear block, hence genuine
pullbacks of pure states of A_F.

## D2 — Pure-state sample

Pure states of A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ), pulled back via π_full:
- ℂ summand: the single pure state.
- ℍ summand: sample of the Bloch S² (pure states of ℍ ≅ S²).
- M₃(ℂ) summand: sample of ℂP² (rank-1 projectors).
- Include particle/antiparticle doubling via the partner map / πOp where the
  representation supports it.
Seeded, documented sample sizes. States as density matrices ρ on ℂ³²,
ω_ρ(a) = Tr(ρ·π_full(a)).

## D3 — Distance matrix

d_D(ω₁, ω₂) = sup { |ω₁(a) − ω₂(a)| : a ∈ A_F, ‖[D_F, π_full(a)]‖ ≤ 1 },
D_F the physical-Yukawa Dirac (same as E13-A/B/C). Quotient out ker[D,·]
exactly via real SVD (as in E13-A). **Build correction 2026-10-01:** the
E13-A multi-start-COBYLA optimizer does not converge reliably at quotient
dimension r = 10 (measured: directional asymmetry up to 28% and
order-of-magnitude underestimates on some pairs). E13-D instead maximizes
f(u) = (c_Q·u)/‖[D_F, A(u)]‖ over the unit sphere with adaptive multi-start
L-BFGS-B (analytic gradient via top singular vectors, verified to 5e-12
against finite differences) plus a random-direction exact-boundary
cross-check, both directions, taking the max. **Build correction 2026-10-02:**
the landscape has deceptive narrow basins (measured on an M3/C pair: ~78%
of random starts converge to a local basin at ~half the global value), so
the two directions share discoveries by alternating warm-start refinement
(up to 2 rounds: if one direction finds a ≥2%-better basin, the other
re-attacks warm-started from it). Every evaluation is exactly feasible, so
values are rigorous lower bounds (cannot overestimate); post-refinement
directional asymmetry is asserted < 0.10 and the worst offenders are
printed; verified consistent with E13-A's closed-form r = 1
case. Infinite distances are legal output.

## D4 — Component decomposition

Equivalence classes of the sampled pure states under finite spectral
distance. Report: number of components, membership, and the algebraic origin
of each (which summand / sheet each component comes from). This is the
building-block inventory.

## D5 — Inter-component distances

**Build note 2026-10-02:** D4 components are connected components *under
finite distance*, so no two distinct components are joined by a finite pair
by construction. D5 therefore reports finite-nonzero distances between
algebraic ORIGINS (ℂ / ℍ / M₃ summands, partners folded into their origin)
— the quantity the pre-registered expectations actually describe. The kill
condition is read the same way: no finite inter-origin distance at all.

For every pair of distinct components joined by finite distance, report the
distance. Consistency check (not a fit): compare the distance scale against
the mass parameters entering D_F (Yukawa × VEV = 246 GeV). No tuning of
Yukawas toward any target — the numbers come out as they come out.

## Controls

- **C-back:** restrict π_full to the Option-A subrepresentation; must
  reproduce E13-A exactly (6 finite distances at 0.4065 GeV⁻¹, 78 infinite
  pairs, triangle audit clean). Failure here invalidates the implementation,
  not the hypothesis.
- **C-deg:** degenerate controls (tracial state, zero Dirac) behave as
  analytically expected.

## Kill condition

If the full representation yields **no** finite inter-component distances at
all (every cross-component pair infinite, or every distance zero), the
"building blocks with measurable separations" hypothesis fails at this rung.
Report the kill; do not rescue it.

## Forbidden inside E13-D

- Tuning Yukawas or the representation to hit a target distance.
- Identifying components with physical particles beyond what the
  representation supports.
- Any finite→continuum, d_spec→4, modular→clock, Lorentzian/GR, or
  experimental-prediction claim (quarantine wall, unchanged).

## Pre-registered expectations (not predictions)

Components are expected to track the algebra summands (ℂ / ℍ / M₃ sheets,
possibly × particle/antiparticle doubling), and inter-component distances are
expected to scale with D_F's off-diagonal mass terms. A fully degenerate
result (all inter-component distances equal, as in E13-A) is a legal outcome
and must be reported as-is.

## Tiering

T4 numerical. Anchors: the proved finite triple (Tier-1), pure-state theory
of finite-dimensional C*-algebras (Tier-2), E13-A as backward-compatibility
control (Tier-4).

## Phase 5 results (2026-10-02) — SELECTION-CONFIRMED

Follow-up whitepaper: `e13d-electroweak-selection.md`; code:
`python/thet_logos/e13d_ew_selection.py` (seeded, exit 0, deterministic
across runs). P_EW = diag(0₁₆, I₈, 0₈) constructed and algebraically
characterized via π_full((1,I₂,0)) = Q_top + P_EW + Q_tail (verified).
Selection theorem witnessed (T4): 1/d(C,H) = max(Y)·VEV at 0.00% rel.
err across 8 Yukawa configurations (position-permuted maxima, rescaled
maxima, democratic, both knockouts). Mechanism: 99.1% of the binding
[D_F,A*] weight on max-Yukawa positions. Value inherited from input
(circularity firewall holds); analytic closed-form proof open
(Phase-3 candidate). Spectral-action half frozen per ledger (SA-4).

## Phase 2+4 results (2026-10-02) — CLOSED-FORM + DUAL BRACKETS (E13-E)

Code: `python/thet_logos/engine13e_hardening.py` (seeded, exit 0).
Overall: E13-E PASS. Quarantine scan clean.

### P2a — closed form for d(C,H) (PASS)

- **Lemma 1, analytic (H-collapse):** self-adjoint quaternions are real
  scalars, so the 12 H Bloch-sphere samples induce the *same* state on the
  order-unit space: all 12 C–H quotient coefficient vectors cQ are parallel
  (cosine = 1 to 2e-16), ‖cQ‖ = 0.5400617. The "12 identical distances" are
  one distance repeated, structurally.
- **Exact convex reformulation:** d(C,H) = ‖cQ‖/μ*,
  μ* = min{‖[D_F,A(u)]‖ : ê_c·u = 1}, ê_c = cQ/‖cQ‖ (convex → global min
  reliable). Gives d_closed = 0.004371011452050007, matching the E13-D D3
  value to 2e-16 (PASS < 1e-9).
- **Controlling block, exact:** the top singular value is degenerate (×2),
  so the statement is at block level: ‖M(u*)[16:24,24:32]‖ = 123.555321 =
  μ* while ‖M(u*)[0:8,8:16]‖ = 1.33. The probe Yukawa off-diagonal
  D[16:24,24:32] = diag(Y)·VEV controls the distance, exclusively.
- **Value:** 1/d_closed = 228.78 GeV = Yu·VEV to 14 digits. HEADLINE (law):
  SELECTION (distance locks onto the heaviest-Yukawa block) is structural;
  VALUE 228.78 inherits from the Yukawa input Y_PHYS — never a discovery.

### P2b — MPFR 80-digit recomputation (PASS)

d_MPFR vs Float64 d_closed: rel diff < 1e-12. No catastrophic
cancellation; all 14 printed digits of d(C,H) are correct.

### P2c — seed perturbations (PASS)

Convex μ*: 24 seeds, rel spread 1.84e-15. D3 optimizer on 2 C–H pairs ×
24 seeds: rel spread ≤ 1.4e-15. The C–H value is seed-invariant.

### P2d — Yukawa shuffles: selection = heaviest Yukawa (PASS)

6 shuffles of Y_PHYS (incl. 0.93 moved to the Yd slot, Yu slot set to 0):
1/d(C,H) = max(Y)·VEV = 228.78 GeV at rel 3.7e-16 in ALL cases.
Selection is position-independent; the value remains input. Consistent
with the independent Phase-5 selection confirmation above.

### P4 — dual SDP brackets (PASS with flags)

Dual d = min{‖Z‖₁ : Tr(Z·i[D,A_k]) = cQ_k} implemented via smoothed
nuclear-norm minimization (scipy; cvxpy not installable without shadowing
the repo's debian numpy — documented); reported bounds are EXACT nuclear
norms of feasible points (rigorous uppers, no smoothing error in the
value). Zero duality gap used as the finite-dim convex theorem it is.
- C–H: [0.004371011452, 0.004371012902], rel gap 3.3e-7 (hard target
  < 1e-6 MET).
- 8 further finite pairs (C–M3, H–M3): rigorous brackets, rel gaps
  6e-4–7e-3, all FLAGGED per the flag-not-tune rule (sample <1e-4 target
  not met). Diagnostic: residual is dual-side L-BFGS stall on instances
  with top-singular multiplicity 4 (restart- and iteration-independent);
  the convex primal is the tighter side (differential-evolution
  cross-check: ≤0.6% residual solver spread). Not physics.
- Invariant held on every pair: dual upper ≥ primal lower (bug check).

### Net

The C–H distance is now: closed-form derived (convex reformulation +
H-collapse lemma + block identification), MPFR-verified, seed-invariant,
shuffle-confirmed as heaviest-Yukawa selection, and two-sided bracketed
to 3.3e-7. The E13-D lower bounds stand; on the hardest pairs the D3
optimizer underestimated by ~1.5% (rigorous lower bounds regardless).
