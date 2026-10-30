# VISC-3 LANDING — 2026-10-29 (the viscous line closes)

**Verdict: FULL, with one pack-level kill recorded below.**
Appended to `ThetLogos/ViscousLine.lean` (VISC-3 adds
strict 7 / defs 1; module totals strict 35 / defs 4).

**NO CLAIM. Parts of any Millennium statement closed by this
landing: 0. Dials 0/4.**

## What landed

- `traceDefect lam t w := 1 − Re tr (ternaryStep lam t
  (diagState w))` — the relaxation defect of a diagonal
  state under the raw step.
- The trace computation (`trace_ternaryStep_diagState`,
  from the landed `ternaryStep_trace`): the trace is the
  multiplier-weighted sum
  `∑ i, w i · exp(−2t·lam i)`. **K-VISC-3 does not fire** —
  the computation returns exactly the predicted sum.
- **The closed form** (`traceDefect_eq_sum`): for a state
  (`∑ w = 1`),
  `traceDefect lam t w = ∑ i, w i · (1 − exp(−2t·lam i))`.
- Signs: `traceDefect_nonneg` (states with nonneg weights,
  `lam, t ≥ 0`) and the vanishing characterization
  (`defect = 0` iff every occupied mode has `t·lam i = 0`).

## Pack-level kill, at full rank (the stated rate bound was FALSE)

The interface pack prescribed `traceDefect_le_slowest`:
defect `≤ 1 − exp(−2t·lam i₀)` when `lam i₀` is the
smallest occupied rate. **That inequality is false** — the
per-mode defect `1 − exp(−2t·λ)` increases with λ, so the
slowest mode bounds the average defect from BELOW, not
above. Counterexample (the builder's): `lam = (0, 10)`,
`w = (½, ½)`, `t = 1`: the prescribed bound is `0`, the
defect is `½(1 − e^{−20}) ≈ 0.5`. The error was the
coordinator's pack text, not the mathematics. What landed
is the correct sharp pair, with attainment at both ends
(`traceDefect_eq_of_single`):
- `traceDefect_ge_slowest`: `1 − exp(−2t·lam i₀) ≤ defect`
  for a slowest occupied `i₀` — the state's relaxation is
  at least as slow as its slowest occupied mode's own
  defect is small; equivalently the defect is bounded
  below by the slowest mode's contribution scale;
- `traceDefect_le_fastest`: `defect ≤ 1 − exp(−2t·lam i₀)`
  for a fastest occupied `i₀`.
The relaxation-rate reading survives correctly: the
defect of a mixed state is trapped between its slowest
and fastest occupied modes' defects, and both bounds are
attained by concentrated states.

## Verification (parent, independent, from disk)

- Parent count of the whole module from disk: strict 35,
  defs 4. Census after this landing: **7,375 strict /
  7,453 attribute-inclusive / 251 counted modules** (from
  7,368 / 7,446 / 251 — an append).
- Main-tree build green (3,325 jobs). Parent axiom check
  on `traceDefect_eq_sum`: exactly
  `[propext, Classical.choice, Quot.sound]`.
- Parent grep: placeholder tactic, `native_decide`, banned
  signature word — 0 occurrences.

## The viscous line, closed

VISC-0 (diagonal one-signedness, registration), VISC-1
(the generator −(ΛX + XΛ), spectrum −(λᵢ + λⱼ), diagonal
dissipativity — the brick shared with the parked TTK-2),
VISC-2 (the general-Hermitian transport under the
load-bearing PSD fence; K-VISC armed and not fired inside
scope), VISC-3 (the trace-defect closed form and the
two-sided sharp rate). The line's claims are permanently
scoped to the RAW step at positive generators: the
normalized step is untouched, and any future extension to
it is a new entry. "Viscosity" remains Jeff's T5 gloss;
the content is the landed theorems.

## Backers since last landing

No new backers recorded since the VISC-2 landing (earlier
today). The backers roll in `BACKERS.md` is unchanged.
