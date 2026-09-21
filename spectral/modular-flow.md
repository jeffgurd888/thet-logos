# Modular flow, exchange flux, and mass gap

**Tier T2 — Defined Operations** (K, σ_s, Z_F, Δ as definitions);
**Tier T3 — Proved/Checked** (flow group property, KMS cyclicity —
numerical);
**Tier T5 — Open** (explicit exchange-flux and mass-gap closed forms;
Haar-averaged K^G implementation).
Source: Gurd, *The Ontological Thet–LOGOS Framework* (Revised Draft, Nexus
Research, Sept 2026), §2.1.4 (Rung 4, Crimson) and Table 1.

## Modular Hamiltonian and flow (T2/T3)

For a positive density state `ρ` (finite-dimensional: `ρ > 0`, `Tr ρ = 1`):

```
K = −log ρ            (modular operator / modular Hamiltonian)
σ_s(A) = e^{isK} A e^{−isK}     (modular time flow — thermal-time hypothesis)
```

Time as the flow of the statistical state; KMS equilibrium is associated
with the flow (Framework §2.1.4).

Python (`python/thet_logos/modular_flow.py`) verifies on random `ρ`
(T3 numerical):

- `σ_s` is a one-parameter group: `σ_{s+t} = σ_s ∘ σ_t`.
- `σ_s` is implemented by unitary conjugation; `K` is Hermitian.
- KMS-type cyclicity of the Gibbs state `ρ_β = e^{−βK}/Z` under the flow.

## Gauge-invariant modular operator (T2 def; T5 implementation)

Haar averaging over the Standard Model gauge group:

```
K^G = ∫_{G_SM} π(g) K π(g)† dg
Z_F(β) = Tr_{ℂ³²}( e^{−β K^G} )
```

Definition recorded (T2); the Haar integral is not implemented
numerically and has no Lean target in this pass (Tier T5).

## Non-equilibrium exchange flux (T5: formula missing)

When `[K, D_H] ≠ 0` for the perturbed Dirac operator `D_H = D_F + H`
(`H = H†` an inner fluctuation), non-zero exchange flux is generated.

[FORMULA PENDING — the explicit exchange-flux expression did not survive
the source paste → Tier T5.]

Python (`spectral_gap.py`) tracks `‖[K, D_H]‖` as a flux proxy under
perturbations — T3 illustration, not the missing formula.

## Linear mass gap (T2 def; T3 numerical)

```
Δ = min { |λ| ∈ spec(D_H) : |λ| > 0 }     (lowest positive |eigenvalue|)
```

[The explicit mass-gap closed form did not survive the source paste;
the definition above is the surviving statement → closed form is T5.]

Python (`python/thet_logos/spectral_gap.py`, `examples/spectral_gap_demo.py`):
builds `D_F` from Yukawa blocks, perturbs by random Hermitian `H`,
computes `Δ` via `eigvalsh` (T3 numerical).

## Torsion sector (T5: open)

The 7-state frame-twist sector enters either by state addition
`H = ℂ³² ⊕ ℂ⁷ = ℂ³⁹` or by embedding `M₇(ℂ) ⊂ End(ℂ³²)` — undecided in
the source (Tier T5).

## Lean mirror

`lean/ThetLogos/ThermalKMS.lean` — `modularOp`, `modularFlow`,
`partitionTrace` definitions (T2); group-property statements (T3,
proofs pending build).
