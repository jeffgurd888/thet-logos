# Ontology Index

Every entity in the thet-logos repository, its rung, its tier, and where it
lives. Tiers per `../epistemic-ledger/TIERS.md`. Strict rule:
**Theorem ≠ Simulation ≠ Experiment ≠ Device.**

## Rung 1 — Void (∅) · Black · T1

| Entity | Location |
|---|---|
| Proto-linguistic Void (assumed pre-metric origin) | `axioms/thet-primitives.md` |

## Rung 2 — Distinction ⟨a,b,c⟩ · Cobalt · T2/T3

| Entity | Tier | Location |
|---|---|---|
| Ternary product ⟨a,b,c⟩ = ab†c | T2 | `axioms/TRO-axioms.md`, `lean/ThetLogos/TRO.lean` |
| TRO associativity law | T3 | `algebra/ternary-TRO.md`, `python/thet_logos/tro.py` |

## Rung 3 — Thet Primitive Θ · Purple · T1

| Entity | Location |
|---|---|
| Primitive pair (θ, θ†) | `axioms/thet-primitives.md`, `lean/ThetLogos/Axioms.lean` |
| Five-step nilpotent ladder (working hypothesis) | `axioms/thet-primitives.md` |

## Rung 4 — LOGOS Engine · Crimson · T2/T3

| Entity | Tier | Location |
|---|---|---|
| K = −log ρ, σ_s(A) = e^{isK}Ae^{−isK} | T2 | `spectral/modular-flow.md`, `lean/ThetLogos/ThermalKMS.lean` |
| Group property, KMS cyclicity | T3 | `python/thet_logos/modular_flow.py`, `examples/modular_flow_demo.py` |
| K^G Haar average, Z_F(β) | T2 def / T5 impl | `spectral/modular-flow.md` |

## Rung 5 — Tripotent Variety · Amber · T1/T5

| Entity | Tier | Location |
|---|---|---|
| N₀³ = N₀ | T1 | `axioms/thet-primitives.md`, `lean/ThetLogos/Axioms.lean` |
| L(X) = X + N₀XN₀ | T2 | `algebra/tripotent-N0.md` |
| dim ker L = 4 | **T5 WITHDRAWN** | `algebra/tripotent-N0.md`, `epistemic-ledger/LEDGER.md` |

## Rung 6 — 32-State Spectrum · Magenta · T2/T3/T5

| Entity | Tier | Location |
|---|---|---|
| H_F = ℂ³², four chiral 8-blocks | T2 | `spectral/hilbert-space-32.md`, `lean/ThetLogos/Scaffold32.lean` |
| p, γ_F, J_F/U_J; p²=1, γ_F²=1, U_J²=1, KO sign | T3 | `axioms/KO-relations.md`, `python/thet_logos/order_zero.py` |
| A_F = ℂ⊕ℍ⊕M₃(ℂ); π, π° = Jπ*J⁻¹ | T2 | `spectral/gauge-algebra.md`, `lean/ThetLogos/FiniteSpectralTriple.lean` |
| Three generations (ℂ⁹⁶ / ℂ³²⊗ℂ³) | T5 | — (open) |

## Rung 7 — Spectral Triple D_F · Cyan · T2/T3

| Entity | Tier | Location |
|---|---|---|
| D_F block matrix (A,B,C,E) | T2 | `spectral/dirac-order-one.md`, `lean/ThetLogos/FiniteSpectralTriple.lean` |
| D_F* = D_F, γ_F-odd | T3 | Lean proofs (pending build) |
| J_F D_F = D_F J_F (conditional) | T3 | Lean statement (proof pending) |

## Rung 8 — Order Conditions · Emerald · T3/T4

| Entity | Tier | Location |
|---|---|---|
| Order-zero [π(a),π°(b)] = 0 | T3 | `lean/.../FiniteSpectralTriple.lean`, `python/thet_logos/order_zero.py` |
| Single-probe [[D,P₊],P₋] = 0 | T3 | `examples/order_one_probe.py` |
| C, E vanish → Yukawa form (Y_u,Y_d,Y_e,Y_ν,Y_R) | T4 | `lean/ThetLogos/OrderOne.lean`, `spectral/dirac-order-one.md` |
| Full 576-pair machine check | T5 | `lean/ThetLogos/OrderOne.lean` (`order_one_full`, sorry) |

## Rung 9 — Thet Engine (∆gap) · Indigo · T2/T3/T5

| Entity | Tier | Location |
|---|---|---|
| ∆ = min{\|λ\|>0} (definition) | T2 | `spectral/modular-flow.md`, `lean/ThetLogos/ThermalKMS.lean` |
| Gap perturbation engine D_H = D_F + H | T3 | `python/thet_logos/spectral_gap.py`, `examples/spectral_gap_demo.py` |
| Hardware realization | T5 | **not asserted** |

## Rung 10 — Epistemic Ledger · White · meta

| Entity | Location |
|---|---|
| Five-tier system | `epistemic-ledger/TIERS.md`, `epistemic-ledger/LEDGER.md` |
