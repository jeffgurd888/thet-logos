# Green–Kubo, finite form — Stokes–Einstein Rung 2 (2026-10-22)

**Verdict: STANDS WHOLE (T1).** Module `ThetLogos.GreenKubo`
(16 strict theorems, 4 definitions, 0 sorry, standard axioms only).
Commissioned by Jeff 2026-10-22 ("both tvmd and Stokes"); charter:
`whitepaper/stokes-einstein-scoping-DRAFT-2026-10-18.md`, §5 Rung 2 —
"D as the summed velocity autocorrelation of the Rung-1 process
(autocovariance a^|k| · stationary variance), proved equal to Rung 1's
rate — the Kubo shape checked against the direct computation."
Builds on Rung 1 (`ThetLogos.DiscreteLangevin`, imported, unmodified).

## What stands

- **T1 — lag autocovariance.** `lagCov a σ k = a^k · statVar a σ`, proved
  equal to the Rung-1 stationary-start process covariance at lag k
  (`lagCov_eq_velS_cov`, from `velS_cov_abs` with w = √(statVar a σ)).
- **T2 — the Green–Kubo sum (headline).** `gkSum_eq_diffusivity`:
  V/2 + ∑′_{k≥0} a^(k+1)·V = `diffusivity a σ` = σ²/(2(1−a)²), at a² < 1.
  The summed velocity autocorrelation of the Rung-1 process, in Kubo
  form (zero-lag term at trapezoidal weight ½), equals Rung 1's
  diffusivity exactly — the Kubo shape checked against the direct
  computation, as chartered.
- **T3 — finite-horizon consistency, at the level of Rung 1's closed
  forms (stated on the module's face, not a silent pin).**
  `posVar_lag_form`: the position variance over n steps is
  n·C(0) + 2·Σ_{k=1}^{n−1} (n−k)·C(k) — the two-sided lag sum
  Σ (n−|k|)·C(k). The bridge `posGrow = lagSum` is proved by matching
  the exact one-step recurrence both sides satisfy. The path-space
  double sum itself is Rung 1's `expct_dispS_sq`, cited, not duplicated.
- **T4 — partial sums.** `gkPartial_closed`: the finite partial Kubo sum
  through lag N is V/2 + V·a(1−a^N)/(1−a); `gkPartial_tendsto`: the
  partial sums converge to `diffusivity a σ` as N → ∞.

## Fences (charter §6, on the module's face)

- **K1:** Θ (`noiseTemp`, Rung 1) is a model ratio defined by the
  finite model's fluctuation–dissipation balance — never thermodynamic
  k_BT. Nothing here derives a thermodynamic temperature.
- **K3:** `DiffusionDefect` is neither imported nor cited; the only
  corpus import is Rung 1, whose position variance is derived there
  from its own Langevin update.
- **K4:** no continuum statement. The only limits are N → ∞ of finite
  partial sums and the sum of a convergent series of finite lag
  covariances.

## Verification (parent, independent of the build agent)

- Candidate md5 `ce31e9ef3ebe222440b5b1403ae483d9`; shipped file md5
  `2a4c6233601d487f8d842596a1a3ce33` (differs only by the header status
  flip at landing).
- Own comment-stripped scan: 16 strict, 0 @[simp]-attribute declarations,
  0 sorry, 0 admit; 4 defs.
- Own `#print axioms` on the six headlines (gkSum_eq_diffusivity,
  lagCov_eq_velS_cov, posVar_lag_form, posVar_eq_lagSum,
  gkPartial_tendsto, gkPartial_closed): each exactly
  [propext, Classical.choice, Quot.sound].
- In-tree build on the exact shipped text: `lake build
  ThetLogos.GreenKubo`, exit 0, 3,118 jobs, .olean present.

## Census step

Program total: **3,561 → 3,577 strict** (3,601 → 3,617
attribute-inclusive), **128 → 129 counted modules**.

NO CLAIM beyond the finite and series identities above. Rung 3
(continuum passage) remains unscheduled, per the charter.
