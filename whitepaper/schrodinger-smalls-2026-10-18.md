# Schrödinger smalls — the two priced remainders of `SchrodingerDynamics`, discharged

**Date:** 2026-10-18
**Module:** `lean/ThetLogos/SchrodingerSmalls.lean` (487 lines)
**Builds on:** `lean/ThetLogos/SchrodingerDynamics.lean` (not modified),
`lean/ThetLogos/FermionicInteraction.lean` (via `SchrodingerDynamics`)
**Spec:** `whitepaper/gauntlet-parked-fleet-2026-10-17.md` §5 (which re-prices
`whitepaper/gauntlet-schrodinger-2026-10-16.md`'s two remainders)
**Ledger position:** program total 3,017 strict before this brick → **3,041 strict** after.

## Verdict — STANDS WHOLE (T1, both deliverables)

Both priced remainders landed in one module, at their priced scope, with no
narrowing:

| Deliverable | Price | Disposition |
|---|---|---|
| 5a — literal `NormedSpace.exp` identification | S | **STANDS (T1)** |
| 5b-α — Dyson first-order term `W₁(t)` | S | **STANDS (T1)** |
| 5b-β — Duhamel identity with integral remainder | M | **STANDS (T1)** |

**Counts (parent-verifiable):** 24 strict theorems/lemmas (line-initial
`^(theorem|lemma) ` on comment-stripped source; attribute-inclusive count is
also 24 — the module uses **zero `@[simp]`**), 5 definitions, **zero
`sorry`/`admit`** in stripped source. Targeted build green (**3,497 jobs**),
`.olean` present. `#print axioms` on seven headlines (`evolOp_apply_eq_exp`,
`evolCLM_eq_exp`, `dysonW1_apply`, `hasDerivAt_dysonW1`, `duhamel_interaction`,
`duhamel_first_order`, `dyson_first_order_schrodinger`): all depend only on
the standard three — `propext`, `Classical.choice`, `Quot.sound`. No
`sorryAx`.

## 5a — what was proved

`SchrodingerDynamics` characterized its evolution operator `evolOp hT t` as
"exp(−itT)" through the Schrödinger equation and the uniqueness theorem
`evolOp_unique`, but never identified it with Mathlib's literal exponential.
This module closes that, for a symmetric operator `T` on a finite-dimensional
complex inner-product space:

- `genCLM hT : H →L[ℂ] H` — the generator `(-i) • T` as a continuous linear map.
- `hasDerivAt_exp_curve_apply` — the curve `s ↦ NormedSpace.exp (s • genCLM hT) ψ₀`
  satisfies the Schrödinger equation with generator `T` (its derivative at `t`
  is `(-i) • T (NormedSpace.exp (t • genCLM hT) ψ₀)`).
- **`evolOp_apply_eq_exp` (headline):** `evolOp hT t ψ₀ = NormedSpace.exp (t • genCLM hT) ψ₀`,
  by `evolOp_unique` — the exponential curve and `evolOp` solve the same ODE
  with the same initial value.
- **`evolCLM_eq_exp` (headline, packaged form):** with
  `evolCLM hT t := (evolOp hT t)` as a CLM, `evolCLM hT t = NormedSpace.exp (t • genCLM hT)`
  as continuous linear maps (extensionality on vectors).
- `continuous_evolCLM` — the packaged evolution is continuous in operator
  norm (corollary used by §3).

**Form note (not a deviation):** the gauntlet wrote the curve as
`NormedSpace.exp (−it • T̂)`; the landed statement is
`NormedSpace.exp (t • genCLM hT)` with `genCLM hT = (-i) • T̂` — the same
operator exponential with the generator packaged once. The derivative lemma
(`hasDerivAt_exp_smul_const'`) is used at the **real** scalar field: in the
pinned Mathlib (v4.35.0-rc3), `NormedSpace.exp` is a *single field-independent
function* — the exponential series at any characteristic-zero scalar field
(`NormedSpace.exp_eq_tsum`) — so the ℝ/ℂ bridge the scoping budgeted friction
for does not arise.

## 5b — what was proved

Environment: Pitch 3 Campaign 1's fermionic interaction,
`hamInt d lam W g = freeHamiltonian d lam + (g : ℂ) • intOp d W` on
`FermionicFock d`, with the free symmetry reproved as
`freeHamiltonian_isSymmetric` (the diagonal-operator argument already inside
`hamInt_isSymmetric`).

**Dyson-α (S).**
- `intPictCLM d lam W g s` — the interaction-picture perturbation
  `heisenbergEvol (free) s ((g : ℂ) • intOp d W)` packaged as a CLM
  (`intPictCLM_apply`); its product form through the §1 packaged evolution is
  `intPictCLM_eq`, and it is continuous in operator norm
  (`continuous_intPictCLM`) — continuity comes from the exponential form of
  the free evolution.
- `dysonW1 d lam W g t := (-i) • ∫ s in (0)..t, intPictCLM d lam W g s`
  (interval integral of the continuous CLM curve).
- `dysonW1_zero`: `W₁(0) = 0`. `hasDerivAt_dysonW1`: `dW₁/dt = -i • V_I(t)`
  (FTC, `intervalIntegral.integral_hasDerivAt_right`).
- `dysonW1_apply`: `W₁(t) ψ₀ = ∫₀ᵗ -i • (V_I(s) ψ₀) ds`.

**Dyson-β (M).** With the interaction-picture state
`intState ψ₀ t := evolOp (free) (-t) (evolOp (interacting) t ψ₀)`:
- `hasDerivAt_intState` — `F'(t)ψ₀ = -i • V_I(t) (F(t)ψ₀)`. Route: the state
  is the CLM product `exp (t • (−A₀)) * exp (t • A)` applied to `ψ₀`
  (`intState_eq_mul_exp`, via §1); the product is differentiated **in the CLM
  algebra** (`HasDerivAt.mul` over ℝ) and only then applied to the fixed
  vector (`hasDerivAt_apply_const`); the free-generator terms cancel against
  the free part of `hamInt` via `evolOp_apply_commute`, leaving exactly the
  interaction-picture perturbation.
- **`duhamel_interaction` (headline):** the exact integral equation
  `F(t)ψ₀ = ψ₀ + ∫₀ᵗ -i • V_I(s) (F(s)ψ₀) ds` (FTC).
- **`duhamel_first_order` (headline):** splitting `F(s) = ψ₀ + (F(s) − ψ₀)`
  inside the integral (integrand split via `intervalIntegral.integral_add`
  and pointwise `map_add`):
  `F(t)ψ₀ = ψ₀ + W₁(t)ψ₀ + ∫₀ᵗ -i • V_I(s)(F(s)ψ₀ − ψ₀) ds` — the remainder
  is a theorem-level integral term, so "first-order" is an approximation
  statement, not a notation.
- **`dyson_first_order_schrodinger` (headline):** the Schrödinger-picture
  form, applying `U₀(t)` to both sides (`free_apply_intState`):
  `U(t)ψ₀ = U₀(t)ψ₀ + U₀(t)(W₁(t)ψ₀) + U₀(t)(remainder)`.

**Helper of independent use:** `hasDerivAt_apply_const` — a real curve of
complex CLMs applied to a *fixed* vector differentiates by applying the
derivative. (Mathlib's `HasDerivAt.clm_apply` / `HasFDerivAt.clm_apply`
require the curve's scalar field to equal the maps' field, so they do not
apply to real curves of ℂ-CLMs; this lemma goes through the evaluation
continuous linear map restricted to ℝ and `HasFDerivAt.comp_hasDerivAt`.)

## Fences

- **Finite dimensions / finite modes only**, exactly as in
  `SchrodingerDynamics`. Nothing here is an unbounded-generator statement.
- The Dyson term is a **formal first-order coefficient** of the
  interaction-picture evolution plus an exact integral remainder. **No
  scattering theory, no S-matrix, no Dyson-series convergence claim, no
  continuum statement** is made or implied.
- Fermionic environment only (the corpus's `hamInt`); the bosonic analog is
  not stated here.
- `SchrodingerDynamics.lean` is unmodified; its uniqueness section
  characterized the evolution as `exp (−i t T)` without identifying it with
  the literal `NormedSpace.exp` — §1 of this module is that identification,
  so the corpus's remaining Schrödinger remainders list is thereby
  **empty at the priced scope**.

## Surprises / build notes

1. The pinned Mathlib's `NormedSpace.exp` is field-independent (above) —
   the expected ℝ-vs-ℂ exponential bridge was unnecessary; the one genuine
   friction was the `clm_apply` field tie, solved once by
   `hasDerivAt_apply_const`.
2. `FiniteDimensional.complete` is a theorem, not an instance, in this
   Mathlib; it is fed locally (`haveI`) where the exponential lemmas need
   completeness of the CLM algebra.
3. No deviation from the gauntlet's scoping of either item was needed:
   the spec in parked-fleet §5 matched the module's actual objects
   (`evolOp`, `evolOp_unique`, `heisenbergEvol`, `hamInt`) as written.
