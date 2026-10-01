# Continuum Effective Theory (CET) — Program Spec

**Status:** SPEC (T5 program definition). No prototype beyond Engine #11.
**Author:** Jeffrey Michael Gurd, Nexus Research (independent research)
**Date:** 2026-09-30

## 1. Objective

Build the continuum effective-theory layer that the finite-triple program
does not supply: starting from a microscopic UV action S_UV at cutoff Λ,
derive mesoscale constitutive tensors (ε_eff, μ_eff, ξ_eff, and nonlinear
χ⁽²⁾, χ⁽³⁾) via the functional renormalization group (FRG), with every
truncation stated and every audit checkable. The honest market is quantum
metamaterials — systems where the microscopic quantum field theory actually
controls the mesoscale response. For conventional metamaterials this
machinery is overkill; classical homogenization already works there.

## 2. Background: what exists

**Engine #11 prototype** (`python/thet_logos/frg_constitutive.py`,
`whitepaper/frg-constitutive-tensors.md`, T4 numerical): one-loop/RPA-level
flow in the optical limit (q → 0) with a Litim regulator and Drude
calibration. It sets μ_eff = I and ξ_eff = 0 from the non-magnetic,
achiral truncation plus cubic symmetry. It is explicitly NOT a full
microscopic quantum-metamaterial calculation — it is the calibration
rung of the ladder below.

**The finite-triple program** (this week's work): the machine-checked
classification of the order-one commutant W_22 is the verified UV matter
content — the bottom link of the chain. CET is the IR flow *above* it:
verified SM → CET → materials. Nothing in the Lean proofs derives a
constitutive tensor; that derivation is this program's job.

## 3. The pipeline

1. **UV input.** Microscopic action S_UV at cutoff Λ: field content,
   symmetries, and (where the finite-triple program applies) the verified
   fermionic sector. State what is verified vs. stipulated.
2. **Regulator.** IR regulator R_k suppressing modes below k. MUST be
   gauge-invariant (or the Ward–Takahashi identities fail and nothing
   downstream is trustworthy). This is the single biggest technical risk.
3. **Wetterich flow.** Integrate the exact flow equation for the effective
   average action Γ_k from Λ down to mesoscale k₀. The equation is exact;
   every truncation is stated explicitly — the truncation is where nearly
   all the physics lives.
4. **Derivative expansion.** Expand Γ_{k₀} in gradients of the
   (electromagnetic) background fields.
5. **Tensor extraction.** Constitutive tensors via functional
   differentiation at A = 0: ε_eff, μ_eff, ξ_eff from the quadratic piece;
   χ⁽²⁾, χ⁽³⁾ from higher orders. Project χ⁽²⁾ onto the crystal point
   group — a χ⁽²⁾ component forbidden by symmetry is a bug, not a
   discovery.
6. **RG flow of the tensors.** Run the extracted tensors under
   t = ln(k/Λ); regulator-independence of physical predictions is the
   internal consistency check.
7. **Audits.** Causality (Kramers–Kronig), passivity (no gain from a
   passive microscopic action), and Ward–Takahashi at every scale.

## 4. Epistemic ledger

| Component | Tier | Notes |
|---|---|---|
| Wetterich equation itself | T1 (math) | exact identity, textbook |
| Regulator choice + gauge invariance | T5 (model) | must be demonstrated per target |
| Truncation scheme | T5 (model) | derivative expansion order stated |
| Engine #11 calibration rung | T4 (numerical) | one-loop/RPA, optical limit |
| Extracted tensors | T4 (numerical) | conditional on K1–K5 below |
| Any claim about a real material | T5+experiment | no material claim without measurement |

## 5. Kill criteria

- **K1 — Gauge violation.** If the regulator breaks Ward–Takahashi
  identities beyond the stated tolerance at any scale, the flow stops.
  No patching with counterterms outside the stated scheme.
- **K2 — Regulator dominance.** If physical predictions (sign of
  ξ_eff, band gaps, χ⁽²⁾ selection rules) move with the regulator choice
  more than with the truncation order, the truncation is too coarse —
  refine or kill.
- **K3 — Calibration failure.** If the pipeline cannot reproduce the
  Engine #11 Drude-calibration results in the weak-coupling limit, the
  implementation is wrong, not the physics.
- **K4 — Symmetry violation.** Any extracted tensor component forbidden
  by the stated point group kills that run; it indicates a broken
  projection, not new physics.
- **K5 — Causality/passivity violation.** A passive UV action producing
  an active (gain) effective tensor means the truncation broke unitarity
  — kill the truncation, keep the program.

## 6. Verdict

**GO as a specified program** (this document). **CONDITIONAL GO as a
build**: the condition is a scoped first target — one material class,
one truncation order, one regulator — with K1–K5 wired in from the first
commit. Unscoped ("derive all metamaterials") is a NO-GO; it repeats the
old failure mode of claiming a framework instead of a result.

## 7. Open decisions (Jeff's call)

1. First target material class (quantum metamaterial candidate?).
2. Truncation order for the first run (derivative expansion to ∂²? ∂⁴?).
3. Compute budget — full Wetterich flows are not laptop jobs.
4. Whether CET results feed the KDP/manuscript track or stay a lab
   program until K1–K5 are all green on the first target.

## 8. Implementation status (2026-09-30, local, unpushed)

Module: `python/thet_logos/engine12_cet.py`. Test suite:
`python/tests/test_engine12_cet.py` (27 tests, all passing).

Gate numbering in the implementation (differs from §5 above):
K1 gauge, K2 calibration-vs-analytic-running-model, K3 point-group
symmetry, K4 Kramers–Kronig causality, K5 passivity. The §5 "regulator
dominance" kill is implemented as a regulator-dependence *measurement*,
not a kill gate (see below).

Hardened audit cadence (200 log-spaced macro-steps, 100 RK2 substeps
each): K1 + finiteness every step; K2/K3/K5 every macro-step; K4 every
10th macro-step (Cauchy-quadrature cost) plus end-of-run. Any gate
failure raises `AuditFailureException` and halts the run.

Regulators: Litim (threshold number T = 3, exact in the stipulated
spectral-flow truncation) and exponential (T = 3·J[exp]/J[litim] =
3.1726, J the explicitly defined threshold weight of the truncation,
quadrature-convergence self-tested). Measured IR regulator dependence
on the Drude calibration: 5.75e-2 relative, exactly matching the
|T_exp − T_lit|/T_lit prediction — the dependence is the truncation's
systematic, reported honestly, not a failure. K2 passes independently
per regulator.

K4 resolution requirement (empirical): ≥ 400 frequency points on
[0.05, 30] eV; coarser grids raise instead of false-killing.

Trajectories (k, f_k, eps_diag per macro-step) saved to
`trajectories/*.npz`. Point-group registries: Oh, D4h with explicit
generators; unknown labels raise (no silent cubic fallback). Target
schema validated on construction (shapes, monotonicity, finiteness,
loss-tangent ≥ 0, known point group).

Verified 2026-09-30 on synthetic data only: Drude calibration K2 =
2.4e-8 (tol 1e-6) both regulators, K4 = 1.8e-3/1.9e-3 (tol 5e-3);
TiO2-like target 200/200 steps, k2 = 1.4e-8, k4 = 1.1e-4, k5 = 0,
tan-delta cross-check reported. NO fabricated device, NO measured
dataset — the numerical pipeline is verified, not a material.
