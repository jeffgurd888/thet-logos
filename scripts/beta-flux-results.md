# β–A flux landscape — results (2026-10-07)

Tier T4 numerical + T1 Lean. Script: `scripts/beta_flux_landscape.py`
(seeds 2026 / 202607). Figures: `whitepaper/figs/beta-flux-landscape/`.

## What was built

The honest, computable core of a "thermal × gauge → flux" probe on the
finite triple. β-family of Gibbs states `ρ_β = e^{−βK}/Z` over a global-β
grid (0.1–10, log-spaced, 13 pts); inner-fluctuation axis
`D_A = D + A₁ + J(A₁)` with a structured 1-form
`A₁(t) = t·(c₀[D,h₀] + c₁[D,h₁])`, `‖A₁‖/‖D‖ ∈ [0, 0.05]` (Span-2 structured
regime). Landscape: `‖φ(β,A)‖_F`, `φ = i[K_β, D_A]`.

Explicit boundary: β is GLOBAL. The finite triple has no x-dependence, so
there is no β(x) gradient here. Killed claims (photons in ker D_F,
H = D², cloaking, refractive index) were not built.

## Headline results

1. **Exact β-linearity (active mode).** `‖φ(β,A)‖_F = β·‖φ(1,A)‖_F` to
   1.8e-12 over the full grid at every fluctuation strength. This is not a
   fit — it is the Lean theorem `modularFlux_betaScale` (T1): the Gibbs
   rescaling gives `K_β = βK + (ln Z)I` analytically, and the scalar drops
   out of the commutator. Numerical subtlety found and fixed: computing
   `K_β` via `logm(expm(−βK))` loses ~10 digits at large β (eigenvalue
   spread `e^{β·range(K)}` destroys small modes); the analytic construction
   is exact and is what the script uses. Documented in the script.
2. **Equilibrium: zero everywhere.** `‖φ‖_F = 0.000e+00` at every
   (β, A) — including fluctuated D_A. The numerical counterpart of
   `thermal_flux_vanishes_allBeta` (T1): the Gibbs modular Hamiltonian
   commutes with D at every β, and fluctuation does not break that.
3. **No superadditive amplification.** Triangle ratio
   `‖[K,D_A]‖ / (‖[K,D]‖ + ‖[K,fluct]‖)`: 1.000000 → 0.943269 as
   fluctuation grows — monotone *decrease*, never > 1. Thermal × gauge
   adds at most triangle-bound; the "thermomagnetic force field" does not
   bootstrap itself. (Impossible otherwise by the triangle inequality;
   now checked.)
4. **KMS at own β:** max residual 3.2e-15 (active), 3.6e-15 (equilibrium),
   via the stable cyclic form `Tr(A e^{−βK} B)/Z` — the naive
   `e^{+βK}` form overflows at 9.8e12 (documented in the script).
5. **Landscape shape:** a ruled surface — linear in β, gently rising in A
   (slope 1641.6 → 1643.8 from t=0 to t=0.05). Max `‖φ‖_F = 1.644e4` at
   (β=10, t=0.05); min at smallest β. No ridges, no valleys, no driver
   on/off transition: the active driver never switches, it just scales.
   Hot (β→0) = no flux; cold = maximal flux.

## Lean (ModularFlux.lean, builds green, 3239 jobs)

- T1 `modularFlux_betaScale`: `modularFlux ((β:ℂ)•K) D = (β:ℂ)•modularFlux K D`
  — axioms [propext, Classical.choice, Quot.sound], zero sorrys.
- T1 `thermal_flux_vanishes_allBeta`: vanishing for every β — direct
  corollary of `thermal_flux_vanishes`.
- T5 pinned `GibbsKMSAtOwnBeta`: the Gibbs-KMS-at-own-β statement with
  `NormedSpace.exp`; ρ existentially quantified (matrix exp/log KMS
  machinery beyond `kms_identity_diagonal` not formalized — precise
  obstruction stated in the docstring).

## Verdict

The landscape is *honestly boring in exactly the right way*: β-linearity is
a theorem, equilibrium is zero by theorem, amplification is bounded by
theorem. The computable content of "thermal × gauge → flux" on the finite
triple is `φ(β,A) = β·i[K, D_A]` — no emergent ridge, no hidden transition.
Any interesting structure in a thermomagnetic coupling must come from
ingredients absent here: β(x) (needs the manifold factor — canyon), or a
non-Gibbs state family. That negative result is the result.
