# Engine 13 — Relational Spectral Dynamics: Finite Spectral-to-Spacetime Emergence

*Commissioned 2026-10-01 (Jeff: GO). Tier T4 numerical. LOCAL — not pushed.*

## Program

Relational Spectral Dynamics (RSD): space and time are not primitive containers
in which dynamics occur. They are effective geometric descriptions extracted
from the spectrum, state, and dynamical relations of the underlying operator
system. Engine 13 works **only the finite rung**: the finite spectral triple
(A_F, H_F, D_F) with H_F = ℂ³² and D_F the physical-Yukawa Dirac from
`python/thet_logos/finite_thermal_flow.py` (`DF_oneGen` × VEV = 246 GeV).

Catalog anchors: H19 (relational primacy), H20 (spectral geometry emergence,
finite rung), H21 (emergent temporal structure — clock identification
quarantined), H22 (relativistic recovery — quarantined, K2). Locked corrections
C1 (finite d_spec → 0 is a control) and C2 (tracial ⇒ trivial flow) are law
for this engine.

## E13-A — Spectral distance

Compute the Connes spectral distance on the actual finite triple:

d_D(ω₁, ω₂) = sup { |ω₁(a) − ω₂(a)| : a ∈ A_F, ‖[D_F, π(a)]‖ ≤ 1 }.

- Algebra grounded in `common.af_generators` (24 real generators of
  ℂ⊕ℍ⊕M₃(ℂ)) represented by `common.pi` (Option-A: supported on the first
  16-sector). Optimization restricted to self-adjoint elements (the difference
  of two states is Hermitian, so the sup is attained there).
- States: density matrices ρ on ℂ³², ω_ρ(a) = Tr(ρ·π(a)). Sample: pure
  computational-basis states of the active sector, thermal states
  ρ_β = e^{−βD_F²}/Z, the maximally mixed active-sector state, one dead-sector
  pure state (diagnoses ∞), one seeded random state.
- Method: convex problem (linear objective over the ‖[D,·]‖ ≤ 1 convex set).
  The implementation quotients out ker[D,·] exactly (real SVD) and uses the
  closed form |cQ|/‖[D,A(ê)]‖ when the quotient is 1-dimensional (the case
  for the Option-A triple); a multi-start derivative-free optimizer with an
  exact-boundary random-direction cross-check covers the general case.
  Infinite distances are legal output (see below).
- Stability: recompute under D → D + δD with δD an inner-fluctuation-type
  self-adjoint perturbation (one-form + J-conjugate, symmetrized),
  ‖δD‖ ≤ 0.05·‖D‖, J via `common.UJ`.

**PASS criteria:** (1) some finite nonzero distances exist (nontriviality);
(2) finiteness pattern unchanged by the fluctuation; (3) max relative distance
change < 1.0 (no blow-up/collapse); (4) sampled triangle-inequality audit holds
within tolerance (optimizer sanity).
**FAIL = kill-relevant for H20:** all distances 0/∞, or instability under the
fluctuation.

## E13-B — Spectral-dimension control

K(t) = Tr(e^{−tD_F²}), d_spec(t) = −2 d log K(t)/d log t, log-spaced t.

**Locked expectation (C1):** finite matrix ⇒ d_spec → 0 at both ends. The
mid-range transient (log-derivative through exponential underflow) is recorded
as identified artifact.
**PASS criteria:** d_spec < 0.5 at the UV end; d_spec → 0 at the IR end (before
underflow); no plateau of ≥ 1 decade with |d_spec − 4| < 0.5.
**Interpretation rule:** PASS confirms the no-go. It is never read as emergence.

## E13-C — Modular-flow inventory

For admissible states ρ (tracial I/32; thermal ρ_β at several β; seeded random
states) and observables a (self-adjoint algebra basis + D_F, D_F² as test
observables):

σ_s^ρ(a) = ρ^{is} a ρ^{−is},  K = −ln ρ.

Classify per pair: [ρ,a] = 0 ⇒ inert observable; [ρ,a] ≠ 0 ⇒ nontrivial modular
response (verify σ_s actually moves a). KMS check for thermal states at their β.

**PASS criteria:** (1) tracial state ⇒ all observables inert (σ_s = id,
asserted); (2) inventory table produced with the inert/nontrivial split;
(3) KMS holds for thermal states within tolerance.
**Hard rule:** no identification of the modular parameter with clock time
anywhere in E13. E13-C does not relitigate the killed finite-thermal-flow
force probe — it is an inventory, not a force search.

## Quarantine wall

Engine 13 does not attempt, claim, or smuggle:

- finite → continuum passage,
- d_spec → 4,
- modular parameter → clock time,
- emergent geometry → Lorentzian GR,
- GR → experimental prediction.

Those are the downstream rungs (H21-clock-half, H22, K2 quarantine).

## Deliverable

`python/thet_logos/engine13_rsd.py`: seeded, self-contained, each of E13-A/B/C
ending in an explicit PASS/FAIL against the criteria above. A FAIL is reported
honestly — never tuned into a PASS.

## Results (2026-10-01 run, exit 0, deterministic)

**E13-A — PASS.** The Option-A represented self-adjoint algebra is 2-dim
(the M₃(ℂ) summand is killed by the embedding — documented artifact);
ker[D,·] is 1-dim, so the finite spectral geometry is 1-dimensional plus
disconnected components. 105 pairs: 6 finite-nonzero (all 0.4065 GeV⁻¹, same
kernel class), 78 infinite (kernel-separated), rest 0. Triangle audit: 0
violation. Under a 5% inner-fluctuation-type perturbation: 0 finiteness flips,
max relative change 1.97e-4 — the finite geometry is stable.

**E13-B — PASS (control).** d_spec = 0.0004 (UV) → −0.0000 (IR); max transient
1.006 (recorded artifact); no 4-plateau over any decade. Locked correction C1
confirmed on the actual D_F.

**E13-C — PASS.** Tracial state fully inert (4/4, σ_s = id asserted). Thermal
states w.r.t. D_F² at β = 1e-4, 0.01, 1.0: fully inert vs all observables
([e^{−βD²},·] = 0 on the represented algebra — the "natural" states see
nothing; nontrivial flow requires generic states). Random states: 4/4
nontrivial with flow/commutator consistency verified. KMS at β_KMS = 1:
err 6.7e-16. No clock-time identification made.
