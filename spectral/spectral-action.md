# Seeley–DeWitt expansion of the spectral action

**Tier T4 — Emergent/Standard** (the coefficient table: standard NCG
results, recorded from the literature via the framework);
**Tier T5 — Open** (missing formulas; continuum derivation not
re-derived here).
Source: architectural stack doc (B6); Gurd framework §§2.1.7–2.1.8
for the finite-side inputs.

## Setup

Total spectral action for the fluctuated operator `D_A = D + A`:

```
S = Tr( f(D_A / Λ) )
```

Expanded via the generalized Lichnerowicz formula:

```
D_A² = −(∇_A^μ ∇_{A,μ} + E)
```

[FORMULA PENDING — spin-connection endomorphism cross-term did not
survive the source paste → Tier T5.]

## Heat-kernel coefficients (T4: standard results)

`Σ_n f_{4−n} Λ^{4−n} a_n(D_A²)` extracts:

| Coefficient | Trace formula | Physical sector |
|---|---|---|
| `a₀` | `∫ d⁴x √−g Tr(1₃₂)` | Cosmological constant |
| `a₂` | `∫ d⁴x √−g Tr(R/6 + Φ²D_F²)` | Einstein–Hilbert gravity & Higgs mass term |
| `a₄` | `∫ d⁴x √−g Tr(E² + RE/6 + F_μν²/12)` | Gauge kinetic term; Higgs kinetic term; Higgs quartic potential; non-minimal scalar–curvature `ξR\|Φ\|²`; topological spin–scalar cross term |

## Product operator (T2)

```
D_A = D_M ⊗ I₃₂ + γ₅ ⊗ D_F^{(A)}
```

over the manifold `M`, acting on `L²(M) ⊗ ℂ³²`.

## What this repository does and does not do

- DOES: record the coefficient table faithfully; provide the finite-side
  inputs (`D_F`, `γ_F`, traces over `ℂ³²`) that feed `a₀, a₂, a₄`;
  numerically evaluate finite traces (`Tr(D_F²)`-type moments in
  `python/thet_logos/spectral_gap.py`).
- DOES NOT: derive the heat-kernel expansion, prove the Lichnerowicz
  formula, or compute the continuum coefficients. Those belong to the
  paper layer, not to this formalization pass (Tier T5 as re-derivation).
