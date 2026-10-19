# ThermalKernel — the heat kernel of a thermal clock, amortized

**Date:** 2026-10-18
**Module:** `lean/ThetLogos/ThermalKernel.lean`
**Verdict: STANDS WHOLE** — 13 strict T1 theorems, 0 sorry, 0 admit,
standard three axioms only (`propext`, `Classical.choice`, `Quot.sound`).

## Origin

Jeff's sentence (2026-10-18 ~21:54 EDT): *"so restart with an
amortization of a thermal spectral kernel of time."*

The reading (marked as a reading when given, then commissioned by
Jeff's tap): restart the line with a brick on the heat kernel of the
thermal clock, `e^{−tK}` with `K = −ln ρ`, **amortized mode by
mode** — each eigenmode pays `exp(−t·λᵢ)` on its own schedule.
Schedules compose (the semigroup law); each mode's total payment
over all time is `∫₀^∞ exp(−t·λᵢ) dt = 1/λᵢ` for `λᵢ > 0`; at
`t = 1` the kernel *is* `ρ`; at `t = β` it is the Gibbs state. The
state is its own heat kernel at unit time.

"Amortization" is Jeff's metaphor. The theorems are the exponential
schedules, the semigroup law, and the payoff integrals — nothing
financial is claimed or used.

## What was built

`heatKernel lam t = Matrix.diagonal (fun i => Real.exp (-t * lam i))`
over a general Fintype `ι` with eigenvalue function `lam : ι → ℝ`
(T2 definition; the diagonal definition is the object of record).
Imports `ThetLogos.ResonanceSpectrum` (hence `ThermalClock`).

| Theorem | Content |
|---|---|
| `heatKernel_apply_diag` | diagonal entry is the mode's schedule `exp(−t·λᵢ)` |
| `heatKernel_apply_off` | off-diagonal entries vanish — schedules do not mix modes |
| `heatKernel_apply` | **spectral expansion, entry form**: `(heatKernel lam t) i j = if i = j then exp(−t·λᵢ) else 0` |
| `heatKernel_zero` | identity at zero: `heatKernel lam 0 = 1` |
| `heatKernel_add` | **semigroup law — schedules compose**: `heatKernel lam (t + s) = heatKernel lam t * heatKernel lam s` |
| `heatKernel_trace` | **trace schedule**: `trace (heatKernel lam t) = ∑ i, exp(−t·λᵢ)` |
| `heatKernel_trace_zero` | trace at `t = 0` is the dimension `(card ι : ℝ)` |
| `integrableOn_exp_neg_mul_Ioi` | each positive mode's schedule is integrable on `Ioi 0` (transport of Mathlib's `integrableOn_exp_mul_Ioi`) |
| `integral_exp_neg_mul_Ioi` | **payoff integral, mode-wise**: for `0 < lam i`, `∫ t in Ioi 0, exp(−t·lam i) = (lam i)⁻¹` (via pinned `integral_exp_mul_Ioi` at rate `−lam i`) |
| `integral_sum_exp_neg_mul_Ioi` | **payoff integral, summed form**: integral over `Ioi 0` of the finite sum of positive-mode schedules = `∑ (lam i)⁻¹` over the positive modes (via `integral_finset_sum`, integrability discharged per mode) |
| `thermalClock_heatKernel_one` | **THE JEWEL**: for a packaged `ThermalClock C`, `heatKernel (fun j => −log (C.weights j)) 1 = Matrix.diagonal C.weights` — i.e. `e^{−K} = ρ`, entry-wise `exp(−1·(−log w)) = exp (log w) = w` by faithfulness |
| `thermalClock_heatKernel_one_trace` | the jewel in trace form: the trace of the clock's kernel at `t = 1` is 1 (normalization read off the kernel) |
| `gibbsWeights_eq_smul_heatKernel` | **Gibbs instance**: `Matrix.diagonal (gibbsDiagWeights β lam logZ) = Real.exp (−logZ) • heatKernel (fun j => (lam j)^2) β` — the Gibbs state is the heat kernel of `D²` at thermal time `β`, up to the partition-function scalar (the same scalar the clock cannot see, `diagFlow_gibbs_logZ_independent`) |

Count: **13 strict** (line-initial `^(theorem|lemma) ` on
comment-stripped source), 1 definition. Program total on landing:
3,302 + 13 = **3,315 strict** (parent to confirm at landing).

## Fences (also in the module header)

- Finite level, **diagonal-generator case only**. The general
  Hermitian-generator reduction is NOT attempted — it is now the
  named remainder shared by three bricks: `ResonanceSpectrum`,
  `SpectralClock`, and this one.
- `t` is the modular/thermal parameter; it becomes physical time
  only through `ThermalClock`'s β for Gibbs states
  (`gibbs_conversion`: physical time = β × thermal time).
- The trace here is a finite sum over modes. No continuum heat
  kernel, no Seeley–DeWitt asymptotic expansion, no spectral
  action is claimed.
- No new axioms; nothing routes through the quarantined
  `ModularTime` sorry.

## What remains open

- The general Hermitian-generator reduction (shared named remainder,
  above) — priced S–M on the shelf.
- Nothing else in this brick's scope: the payoff integral landed in
  both mode-wise and summed form; no open clause.
