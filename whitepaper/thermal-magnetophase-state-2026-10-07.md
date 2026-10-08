# The thermal magnetophase entropy state (2026-10-07)

**Status:** STAND as an entropy entry; KILLED as a flux entry (proved no-go).
**Tiers:** T1 (flux no-go, A=0 reduction) / T4 (entropy landscape, KMS) / T5 (KMS pin).

## 1. Definition

$$\rho_{\beta,A} = \frac{e^{-\beta D_A^2}}{Z(\beta,A)}, \qquad
Z = \operatorname{Tr} e^{-\beta D_A^2},$$

where $D_A = D + A_1 + J(A_1)$ is the gauge-fluctuated Dirac
($\rho$-real structured 1-forms, $\|A_1\|/\|D\| \in [0, 0.05]$, seeds
2026/202607). The modular Hamiltonian is

$$K_A = -\ln \rho_{\beta,A} = \beta D_A^2 + (\ln Z) I$$

(spectral mapping theorem — exact; the scalar drops from all commutators).
$\beta$ is GLOBAL: the finite triple has no $x$-dependence, so there is no
$\beta(x)$ gradient in this construction (explicit, load-bearing boundary).

This differs from the $\beta$–$A$ landscape (`scripts/beta_flux_landscape.py`),
which used $K$ from the UNFLUCTUATED triple. Here the state knows the magnetic
background intrinsically: $K$ itself depends on $A$.

## 2. The flux no-go (T1 — proved, kill-condition (b))

$$[K_A, D_A] = [\beta D_A^2 + (\ln Z)I, D_A] = 0$$

identically, since $K_A = f(D_A)$. Hence

$$\phi_{\beta,A} = i[K_A, D_A] = 0 \qquad \forall\,(\beta, A).$$

Lean: `magnetophaseFlux_vanishes` (ModularFlux.lean) — `thermal_flux_vanishes`
applied to $D_A$, zero sorrys. Numerics: $0.000\mathrm{e}{+}00$ over the full
$13 \times 10$ grid. The "magnetophase" **as a flux concept is killed by
theorem**, not by failed numerics. Letting $K$ depend on $A$ does not generate
a thermomagnetic flux — it annihilates the flux entirely: equilibrium w.r.t.
the magnetized Dirac is flux-free by construction.

Comparison: old flux $\beta \cdot i[K_{\mathrm{active}}, D_A]$ peaks at
$1.696\mathrm{e}{+}04$ (ruled surface); new flux is $0$ everywhere (fig4).

## 3. The entropy landscape (T4 — the surviving entry)

$S(\rho_{\beta,A}) = -\operatorname{Tr}(\rho \ln \rho)$ over the grid
(fig1–fig3):

| quantity | value |
|---|---|
| $S(\beta{=}1, A{=}0)$ | 1.402858 nats |
| $S(\beta{=}1)$ range over $A$ | [1.386294, 1.402858] |
| max $\|dS\|$ over $A$ at $\beta{=}1$ | 0.016564 nats (1.18%) |
| monotone decreasing in $A$ at $\beta{=}1$ | yes |
| $S(\beta{=}10)$ for ALL $A$ | 1.386294 $= \ln 4$ exactly |

Findings:
- **Magnetic imprint is real but small**: the fluctuation lowers the entropy
  monotonically (spectrum spreading at fixed $\beta$), max effect 1.18%.
  No ridges, no crossover signature in the finite sense — smooth.
- **Cold limit is $A$-independent**: $S \to \ln 4$ for every tested $A$.
  Direct check: $\dim \ker D_A^2 = 4$ at $t$-ratios $0, 10^{-3}, 10^{-2},
  0.05$, with spectral gap $6.05 \to 34.86\ \mathrm{GeV}^2$ above zero.
  The 4-fold ground-state degeneracy is **stable under fluctuation** —
  finite index stability. The magnetic background cannot lift the kernel.
- **KMS verified** at the state's own $\beta$ w.r.t. the $D_A^2$-flow:
  max residual $3.997\mathrm{e}{-}15$ (stable cyclic form).
- **A=0 reduction exact**: $\|\rho_{1,0} - \rho_{\mathrm{eq}}(1)\|_1 =
  0.000\mathrm{e}{+}00$ (Lean: `magnetophase_reduces_at_zero`, `rfl`).

## 4. What this buys toward the thermomagnetic intuition

The original intuition ("thermal $\times$ gauge $\to$ flux") is now fully
priced:
- As a **flux** mechanism: dead by theorem. Any future thermomagnetic flux
  needs either $\beta(x)$ (manifold factor — canyon) or a **non-Gibbs**
  state family (e.g., the active non-equilibrium mode with $K_A$ not
  commuting with $D_A$ — open, well-posed on the finite triple).
- As an **entropy** mechanism: alive and measured. The magnetized triple has
  a well-defined thermal entropy with quantified magnetic imprint and a
  protected kernel. This is the honest finite remnant of "the state knows
  the magnetic background."

## 5. Remaining open

- Non-Gibbs magnetophase families (active mode + $A$-dependent $K$): the one
  place a non-zero magnetophase flux could still live. Well-posed, unbuilt.
- Manifold $\beta(x)$: canyon (needs the continuum triple).
- `MagnetophaseKMSAtOwnBeta` pinned T5 (inherits the `GibbsKMSAtOwnBeta` pin;
  no new machinery needed).

## 6. Tier ledger

| claim | tier | evidence |
|---|---|---|
| $\phi_{\beta,A} = 0$ identically | T1 | `magnetophaseFlux_vanishes`, zero sorrys; T4 $0.000\mathrm{e}{+}00$ |
| A=0 reduction to $\beta$-family | T1 | `magnetophase_reduces_at_zero` (`rfl`); T4 exact |
| entropy magnetic imprint (1.18%, monotone) | T4 | `magnetophase_lab.py`, seeds 2026/202607 |
| $\dim \ker D_A^2 = 4$ stable | T4 | direct eigencheck + cold-limit $\ln 4$ |
| KMS at own $\beta$ | T4 + T5 pin | $3.997\mathrm{e}{-}15$; `MagnetophaseKMSAtOwnBeta` |
| killed: magnetophase flux, $\beta(x)$, photons, cloaking | killed | theorem / no-manifold / category error |

## Files

- `scripts/magnetophase_lab.py`, `scripts/magnetophase-results.json`,
  `scripts/magnetophase-results.md`
- `whitepaper/figs/thermal-magnetophase/` (fig1–fig4)
- `lean/ThetLogos/ModularFlux.lean` (magnetophase section)
