# TwoDirections — the two directions of a heat kernel's spectrum

**Date:** 2026-10-19
**Module:** `lean/ThetLogos/TwoDirections.lean`
**Verdict: STANDS WHOLE** — 8 strict T1 theorems, 0 sorry, 0 admit,
standard three axioms only (`propext`, `Classical.choice`,
`Quot.sound`; spot-checked by `#print axioms` on the dichotomy,
the iff headline, the gap-rate bound, and the sub-card corollary).

## Origin

Jeff's question (2026-10-19): *"gravity and matter one way light
and heat the other?"* — a proposed pairing of the world into two
directions. Formalize-and-gauntlet was commissioned the same day.

**Gauntlet verdict:**

- **NO-GO as a physical partition.** Gravity bends light; heat
  conducts through matter; the two columns interconvert (a star is
  the two directions in continuous exchange, balanced by trading,
  not by separation). No theorem of this corpus states a physical
  separation of gravity/matter from light/heat, and this module
  does not revive one.
- **FIT as the spectral dichotomy of a finite heat kernel.** The
  pairing's mathematical skeleton is a true, provable split: under
  a nonnegative diagonal generator, a heat kernel's spectrum has
  exactly two parts — modes that never decay and modes that decay
  exponentially, with the gap setting the slowest decay. That
  skeleton is what was built.

## What was built

Built on `ThetLogos.ThermalKernel` (`heatKernel lam t =
Matrix.diagonal (fun i => Real.exp (-t * lam i))`). Setting:
general Fintype `ι`, eigenvalue function `lam : ι → ℝ`,
nonnegative (`hlam : ∀ i, 0 ≤ lam i`) where required.

| Theorem | Content |
|---|---|
| `heatKernel_diag_eq_one_of_eq_zero` | **zero-mode conservation**: if `lam i = 0`, the mode's kernel entry is `1` at every time — the gathered column is exactly conserved |
| `exp_neg_mul_eq_one_of_eq_zero` | schedule form of conservation: a zero rate makes the schedule identically `1` |
| `heatKernel_diag_le_one_of_pos` | **dispersal, weak form**: a positive-rate mode's schedule is `≤ 1` at every nonnegative time |
| `heatKernel_diag_lt_one_of_pos` | **dispersal, strict form**: a positive-rate mode's schedule is `< 1` at every positive time — dispersal is real |
| `heatKernel_diag_le_exp_neg_mul_of_le` | **the gap-rate bound**: if `g ≤ lam i`, the mode's schedule is `≤ exp(−t·g)` — with `g` the smallest positive rate, the gap sets the slowest dispersal |
| `heatKernel_trace_dichotomy` | **the dichotomy, headline**: `trace (heatKernel lam t) = (#{i : lam i = 0} : ℝ) + ∑_{i : 0 < lam i} exp(−t·lam i)` — the trace is the gathered count plus the dispersing schedules, exactly |
| `heatKernel_trace_sub_card` | **the gathered part is constant**: trace minus the zero-mode count is exactly the dispersing sum — the first summand is a literal cardinality, independent of `t` |
| `exp_neg_mul_forall_eq_one_iff` | **the iff headline**: for `0 ≤ lam i`, `(∀ t, exp(−t·lam i) = 1) ↔ lam i = 0` — gathered ⇔ never disperses, mode by mode |

Count: **8 strict** (line-initial `^(theorem|lemma) ` on
comment-stripped source), 0 definitions (the kernel is
`ThermalKernel`'s). No narrowings against the commission: all five
targets landed in the specified forms, plus the schedule-form
companion of target 1 and the sub-card corollary of target 4.

## Fences

- Finite level, **diagonal-generator case only**, as in
  `ThermalKernel`. The general Hermitian-generator reduction
  remains the named remainder shared by `ResonanceSpectrum`,
  `SpectralClock`, and `ThermalKernel`; this module does not
  attempt it.
- The module packages the spectral dichotomy only. It contains no
  gravity, no light, no continuum limit, and no physical claim.
  "Gathered" and "dispersing" name the zero part and the positive
  part of a finite spectrum, nothing more.
- `t` is the modular/thermal parameter, as in `ThermalKernel`.

Tier map: T2 — no new definitions. T1 — all eight theorems.
