# Epistemic Ledger — per-component entries

Tiers per `TIERS.md` (Framework §5). Strict rule: **Theorem ≠ Simulation ≠
Experiment ≠ Device.** "Proof pending" = Lean statement with `sorry`;
it is a T3 statement, not a proof.

## Rung 1 — Void (∅)

| Component | Tier | Evidence |
|---|---|---|
| Proto-linguistic Void as pre-metric origin | T1 | Assumed primitive (Framework Def. 1.1) |

## Rung 2 — Distinction ⟨a,b,c⟩

| Component | Tier | Evidence |
|---|---|---|
| Ternary product ⟨a,b,c⟩ = ab†c (definition) | T2 | `ThetLogos.TRO.ternary`, `python/thet_logos/tro.py` |
| TRO associativity [[abc]de]=[ab[cde]]=[a[dcb]e], matrix models | T3 | Numerical (`tro.py`, random matrices, seed 2026) |
| TRO associativity, scalar case | T3 | Lean `ternary_assoc_scalar` proved; matrix case `ternaryMat_assoc` sorry |

## Rung 3 — Thet Primitive Θ = (θ, θ†)

| Component | Tier | Evidence |
|---|---|---|
| Primitive adjoint pair (θ, θ†) | T1 | Assumed primitive (Framework Def. 1.2) |
| Five-step nilpotent ladder | T1 | Working hypothesis (Framework §2.1.3), not a theorem |

## Rung 4 — LOGOS Engine

| Component | Tier | Evidence |
|---|---|---|
| K = −log ρ, σ_s(A) = e^{isK}Ae^{−isK} (definitions) | T2 | `ThetLogos.ThermalKMS`, `python/thet_logos/modular_flow.py` |
| Flow group property σ_{s+t} = σ_s∘σ_t | T3 | Numerical (`modular_flow.py`) |
| KMS cyclicity of Gibbs state | T3 | Numerical (`modular_flow.py`) |
| Haar-averaged K^G = ∫ π(g)Kπ(g)†dg, Z_F(β) (definitions) | T2 | `spectral/modular-flow.md` |
| Haar integral implementation | T5 | Open — not implemented |
| **Thet-engine graduation: quantum Otto cycle on H = D_F²** | **T4** | **GO (engine design)** — `python/thet_logos/engine_cycle.py`: Gibbs/KMS baths at T_c=0.5, T_h=3.0 (KMS identity verified ~1e-15), uniform gap-scaling strokes; W_net = 0.155 > 0, η = 0.50 < η_Carnot = 0.83. Numerical only: Theorem ≠ Simulation ≠ Experiment ≠ Device — no device asserted |
| **Dynamic density-matrix thermalization (engine #7)** | **T4** | **GO (engine design)** — `python/thet_logos/thermalize.py`: Lindblad evolution of the 32-state ρ(t) with detailed-balance jumps (g_{m→n} = κ/(1+e^{β(E_n−E_m)}), Gibbs stationary to 1.2e-15); pure |E_max⟩ initial state (S=0) thermalizes to ρ_β (S=3.234039 exact, trace_dist 4.4e-16); modular-Hamiltonian clock readout K(t) = −log ρ(t) → β(H−F) (err 5.1e-15); clock-settling time t≈1.0 at κ=1. Numerical only: Theorem ≠ Simulation ≠ Experiment ≠ Device — no device asserted |
| **THET Proto-Lingua Greek (engine #8)** | **T4** | **GO (engine design)** — `python/thet_logos/protolingua.py`: Rung-4 operator alphabet L₀ = {⊤,⊥,∅,1,Θ,Φ,Ω} as stipulated syntax. Θ = Θ_dual ⊕ Θ_nil ⊕ M verified numerically: Θ_dual Pauli-X involution (flip err 0), Θ_nil 6×6 shift with 5 transition stages (‖N⁶‖=0, ‖N⁵‖=1 — nilpotency index 6, spec's "order 5" is the stage count), M = [[1,1],[1,0]] with spec {φ, −1/φ} to 4.4e-16 and exact Fibonacci tower Mⁿ[0,0] = F_{n+1} (n=1..12); Ω = sector completeness. LOGOS cycle on the 32-state triple reusing engine #7: REFLECT J²=+I, JD=DJ, Jρ_βJ=ρ_β (all ~0); FLOW Lindblad t=8 → trace_dist 2.6e-16; GENERATE K(t) err 3.9e-15; CLOSE KMS err 1.8e-15. Numerical only: Theorem ≠ Simulation ≠ Experiment ≠ Device — the symbol→operator map is stipulated, not derived; "pre-spatiotemporal" is architectural placement, not a numerical result |

## Rung 5 — Tripotent Variety

| Component | Tier | Evidence |
|---|---|---|
| N₀³ = N₀ (N₀ ∈ M₂(ℝ)) | T1 | Assumed primitive (Framework Table 1) |
| L(X) = X + N₀XN₀ (definition) | T2 | `ThetLogos.TRO.L` |
| **dim_ℝ ker L = 4 fixing spacetime dimension** | **T5** | **WITHDRAWN** — inconsistent on M₂(ℝ) (Framework §2.1.5); numerical kernel census in `tro.py` consistent with withdrawal |
| Geometric meaning of N₀ | T5 | Open question |

## Rung 6 — 32-State Spectrum

| Component | Tier | Evidence |
|---|---|---|
| H_F = ℂ³² = ℂ⁸⊕ℂ⁸⊕ℂ⁸⊕ℂ⁸; A_F = ℂ⊕ℍ⊕M₃(ℂ); π, π° = Jπ*J⁻¹ (definitions) | T2 | `ThetLogos.Scaffold32`, `ThetLogos.FiniteSpectralTriple` |
| p² = 1; γ_F² = 1, γ_F* = γ_F; U_J² = 1 | T3 | Lean proved (`gammaF_self_adjoint`, `gammaF_involutive`, `UJ_mul_self`) + numerical |
| J_F γ_F = −γ_F J_F | T3 | Lean statement `UJ_gamma_anticomm` (sorry); numerical check exact |
| Three generations (ℂ⁹⁶ or ℂ³²⊗ℂ³) | T5 | Open (Framework §2.1.6) |

## Rung 7 — Spectral Triple D_F

| Component | Tier | Evidence |
|---|---|---|
| D_F block matrix (A,B,C,E) (definition) | T2 | `ThetLogos.FiniteSpectralTriple.buildDirac` |
| D_F* = D_F; γ_F D_F + D_F γ_F = 0 | T3 | Lean proved (`buildDirac_self_adjoint`, `buildDirac_gamma_odd`) |
| J_F D_F = D_F J_F (conditional on B = Ā, C,E symmetric) | T3 | Lean statement `buildDirac_J_compat` (sorry) |

## Rung 8 — Order Conditions

| Component | Tier | Evidence |
|---|---|---|
| Order-zero [π(a), π°(b)] = 0 | T3 | Lean proof (`order_zero_condition`, pending build) + numerical < 1e-14 (`order_zero.py`, `examples/`) |
| Single-probe [[D_F,P₊],P₋] = 0 ⇒ C = E = 0 | T3 | Numerical (`examples/order_one_probe.py`) |
| Vanishing cross-terms under order-one; Yukawa form (Y_u,Y_d,Y_e,Y_ν, Y_R) | T4 | Standard one-generation NCG; no new mass predictions claimed |
| Full 576-pair order-one machine check | T5 | Open ("complete Lean archive") |

## Rung 9 — Thet Engine (∆gap)

| Component | Tier | Evidence |
|---|---|---|
| ∆ = min{\|λ\| ∈ spec(D_F) : \|λ\| > 0} (definition) | T2 | `ThetLogos.ThermalKMS`, `python/thet_logos/spectral_gap.py` |
| Gap computation under perturbations D_H = D_F + H | T3 | Numerical (`spectral_gap.py`, `examples/spectral_gap_demo.py`) |
| Exchange-flux closed form | T5 | Formula missing from source |
| Mass-gap closed form | T5 | Formula missing from source |
| Hardware realization of Thet Engine | T5 | **Not asserted** (Framework §2.1.9) |

## Rung 10 — Epistemic Ledger

| Component | Tier | Evidence |
|---|---|---|
| Five-tier system itself | (meta) | Framework §5; this directory |

## Cross-cutting

| Component | Tier | Evidence |
|---|---|---|
| Spectral-action coefficients a₀, a₂, a₄ (table) | T4 | Standard NCG results, recorded from literature |
| Lichnerowicz spin-connection cross-term | T5 | Formula missing from source |
| Torsion sector (ℂ³⁹ vs M₇(ℂ) ⊂ End(ℂ³²)) | T5 | Undecided in source |
| Formal Möbius-bundle chromatic topology | T5 | Open (Framework §2: "does not yet constitute") |
| Coupling unification; mass predictions | T5 | Open/withdrawn as predictions |
| Complete Lean archive (zero-sorry) | T5 | Open — this pass ends with 10 documented sorrys; `lake build` green 2026-09-21 |
