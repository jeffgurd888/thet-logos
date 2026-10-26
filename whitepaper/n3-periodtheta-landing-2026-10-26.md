# Period Stage N3 — The Two-Sided Rate: Θ(|log τ|)

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/SolidBodyPeriodTheta.lean` (strict 8, zero
`sorry`, zero `native_decide`; main-tree build green, 3,510 jobs,
parent-verified on the shipped text). **Parts of the Clay
Yang–Mills statement closed by this landing: 0.** Classical
mechanics, abstract body only, frozen coefficients.*

## What landed

The matching upper bound, in both bands, and with it the
two-sided rate:

- **`periodQuad_le_abs_log_top/bot`** — `periodQuad ≤
  upCoeff·|log τ| + upC2` for τ = |E − E_sep| small: the integral
  splits at U − Λ/4; the away part is bounded pointwise (no
  compactness argument was needed — it closes with `√(U−Λ/4) ≤
  √Λ` and `∫₀^a u^(−1/2) du = 2√a`); the window part gives the log.
- **`periodQuad_theta_top/bot`** — the conjunction with N2's lower
  bound: the quadrature period is **Θ(|log τ|)** as E → E_sep,
  per band.
- **`upCoeff_eq_sqrt_two_mul_divCoeff`** — the two constants are
  not independent: the upper coefficient is *exactly* √2 times
  N2's lower coefficient. The √2 is the window factor's price,
  identified, not estimated.

Axiom sets on the headlines: exactly
`[propext, Classical.choice, Quot.sound]`.

## State of the nonlinear program

With N3 landed, every priced stage of the variable-axis
nonlinear program is complete: N0 (affine forms + saddle), the
portrait (band separation, saddle passage, crossing corollary),
N1 (quadrature period, finite), N2 (log divergence), N3
(two-sided Θ rate). Remaining, named and fenced: N4, the
trajectory identification (deferred by design — until it lands,
all period theorems here are about the *quadrature* period), and
the portrait's exact component count (L tail).

## Census effect

Strict 6,050 → **6,058**; attribute-inclusive 6,128 → **6,136**;
modules 206 → **207**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
