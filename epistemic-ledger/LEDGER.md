# Epistemic Ledger — per-component entries

Tiers per `TIERS.md` (Framework §5). Strict rule: **Theorem ≠ Simulation ≠
Experiment ≠ Device.** "Proof pending" = Lean statement with `sorry`;
it is a T3 statement, not a proof.

**Three claims (2026-09-25): MATHEMATICAL THEOREM ≠ MODEL PROPERTY ≠
PHYSICAL INTERPRETATION.** A theorem (T1) is proved in Lean. A model
property (T2/T3/T4) is defined, checked, or numerically realized *inside
the stipulated model* — rigorous relative to the model; the model itself
is stipulated. A physical interpretation (T5) is what the mathematics would
mean *if* the model described nature — open until a calibration exists.
These three are never conflated.

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
| K_ρ := −ln ρ, σ_s(A) = e^{isK_ρ}Ae^{−isK_ρ} (definitions; thermal case K_ρ = βD_F² + (ln Z)·I, ln Z cancels in the flow) | T2 | `ThetLogos.ModularTime`, `spectral/modular-time.md` |
| Formal-core corrections (2026-09-25): (1) time derived, not primitive — (ρ,D_F,β) → K → σ_s → T; (2) trivial-flow condition is non-centrality, ρ = I/N ⟹ σ_s = id, nontriviality relative to the observable algebra; (3) K_ρ := −ln ρ, σ_s sees only βD_F² (Lean `modularEigenvalue_diff` proved); (4) ternary data 𝔗=ρ, ℌ=β, 𝔊=D_F, temporal generator synthesized | T2 | `spectral/modular-time.md`, `lean/ThetLogos/ModularTime.lean` |
| Scalar-flow triviality (2026-09-26): [ρ,a] = 0 ⟹ σ_s(a) = a (eigenbasis form); scalar modular unitaries act trivially; maximal ignorance gives trivial modular flow (`maximallyMixed_flow_trivial`) | **T1** | Lean `ThetLogos.ModularTime`: `diagFlow_trivial_of_commute`, `scalar_conj_trivial`, `diagFlow_trivial_of_const`, `maximallyMixed_flow_trivial` — all proved, no sorry. Converse (trivial flow on a subalgebra ⟹ ρ = I/N) deliberately not formalized |
| KMS identity ω(aσ_{−i}(b)) = ω(ba) as the stationarity check (replaces the automatic [ρ,K] = 0) | T3 | Numerical: engines verify the identity directly, 1e-15–1e-20 (`modular_flow.py`, `engine_cycle.py`, `thermalize.py`, `ternary.py`, `integration.py`); Lean `kms_identity_diagonal` sorry |
| Modular-frequency scale κ_i − κ_j = β(λ_i²−λ_j²); gap enters as Δ² | T2 | `spectral/modular-time.md` §5; Lean `modularEigenvalue_diff` |
| Physical time calibration ω_modular = c_T·Δ²/ℏ as theorem | T5 | Open — c_T undefined; explicitly NOT claimed |
| Flow group property σ_{s+t} = σ_s∘σ_t | T3 | Numerical (`modular_flow.py`) |
| KMS cyclicity of Gibbs state | T3 | Numerical (`modular_flow.py`) |
| Haar-averaged K^G = ∫ π(g)Kπ(g)†dg, Z_F(β) (definitions) | T2 | `spectral/modular-flow.md` |
| Haar integral implementation | T5 | Open — not implemented |
| **Thet-engine graduation: quantum Otto cycle on H = D_F²** | **T4** | **GO (engine design)** — `python/thet_logos/engine_cycle.py`: Gibbs/KMS baths at T_c=0.5, T_h=3.0 (KMS identity verified ~1e-15), uniform gap-scaling strokes; W_net = 0.155 > 0, η = 0.50 < η_Carnot = 0.83. Numerical only: Theorem ≠ Simulation ≠ Experiment ≠ Device — no device asserted |
| **Dynamic density-matrix thermalization (engine #7)** | **T4** | **GO (engine design)** — `python/thet_logos/thermalize.py`: Lindblad evolution of the 32-state ρ(t) with detailed-balance jumps (g_{m→n} = κ/(1+e^{β(E_n−E_m)}), Gibbs stationary to 1.2e-15); pure |E_max⟩ initial state (S=0) thermalizes to ρ_β (S=3.234039 exact, trace_dist 4.4e-16); modular-Hamiltonian clock readout K(t) = −log ρ(t) → β(H−F) (err 5.1e-15); clock-settling time t≈1.0 at κ=1. Numerical only: Theorem ≠ Simulation ≠ Experiment ≠ Device — no device asserted |
| **THET Proto-Lingua Greek (engine #8)** | **T4** | **GO (engine design)** — `python/thet_logos/protolingua.py`: Rung-4 operator alphabet L₀ = {⊤,⊥,∅,1,Θ,Φ,Ω} as stipulated syntax. Θ = Θ_dual ⊕ Θ_nil ⊕ M verified numerically: Θ_dual Pauli-X involution (flip err 0), Θ_nil 6×6 shift with 5 transition stages (‖N⁶‖=0, ‖N⁵‖=1 — nilpotency index 6, spec's "order 5" is the stage count), M = [[1,1],[1,0]] with spec {φ, −1/φ} to 4.4e-16 and exact Fibonacci tower Mⁿ[0,0] = F_{n+1} (n=1..12); Ω = sector completeness. LOGOS cycle on the 32-state triple reusing engine #7: REFLECT J²=+I, JD=DJ, Jρ_βJ=ρ_β (all ~0); FLOW Lindblad t=8 → trace_dist 2.6e-16; GENERATE K(t) err 3.9e-15; CLOSE KMS err 1.8e-15. Numerical only: Theorem ≠ Simulation ≠ Experiment ≠ Device — the symbol→operator map is stipulated, not derived; "pre-spatiotemporal" is architectural placement, not a numerical result |
| **Triple Point -- ternary Heat-Gravity-Time fixed point (engine #9)** | **T4** |
| **GO (engine design)** — `python/thet_logos/ternary.py`: X_{n+1} = T_dt o G_ell o H_beta(X_n) on a 1D ring lattice (dim 16) as manifold proxy (the finite triple has no spatial part -- labeled toy). H_beta = exact finite-time Lindblad step (same dissipator as engine #7, integrated exactly in the energy eigenbasis); G_ell = Nicolini-style smeared Newton kernel V_j = -G_N sum_i m_i erf(d_ji/2ell)/d_ji with back-reaction D <- D_bare + lam_g (V (x) I_2) (scalar-potential proxy -- labeled); T_dt = modular-flow probe readout (identity on X at the fixed point: rho_* Gibbs is KMS-stationary under its own flow, the engine-#7 subtlety); combiner = sequential composition (labeled stipulation). Mode A (fixed ell=1.0): converges in 17 iters; Gibbs self-consistency resid 4.8e-9; KMS err 1.0e-7; back-reaction redshifts the ring zero mode -> Delta_*=0.045 (bare nonzero-mode gap 0.785); dimensionless readout beta*Delta_*=0.091, ell*Delta_*=0.045, kappa/Delta_*=22.1. Mode B (dynamical locking ell_{n+1}=1/Delta_n): RUNAWAY (ell>1e6 after 5 iters) -- no finite locking fixed point on the periodic ring; the rule chases the zero mode down and switches gravity off. Mode C (locking + antiperiodic BCs, no zero mode): locking fixed point EXISTS -- converges in 19 iters, ell_*Delta_*=1.000000, Gibbs resid 3.2e-9, KMS err 2.9e-9. Numerical only: Theorem != Simulation != Experiment != Device -- the locking result is a numerical fixed point, not a derivation; smearing, proxy, and combiner are stipulated |
| **Synthesis -- product geometry M x F (engine #10)** | **T4** |
| **GO (engine design)** — `python/thet_logos/integration.py`: Combines all nine engines on the almost-commutative product: H = H_lat (x) H_F (dim 512), D = D_lat (x) I + Gamma_lat (x) D_F (antiperiodic ring). Ternary iteration at full scale. Back-reaction deforms D_lat as sigma_3 (x) (p + lam_g V), preserving {D_lat, Gamma}=0 exactly (product structure survives, as in NCG). Mode A: 3 iters, Gibbs resid 6.7e-15, KMS 1.5e-20. Mode B (locking): 7 iters, ell_*Delta_*=1.000000, Gibbs resid 1.2e-10. Fixed point factorizes rho_* = rho_lat (x) rho_F to 4.1e-15; finite factor exactly thermal (KMS 2.3e-18). T readout o_n = Tr(rho_n X) is the probe expectation (a state is stationary under its own modular flow -- the tick tracks inter-iteration drift). Proves CONSISTENCY of the nine pieces at full scale, not new physics. Caught and fixed during build: scalar-potential back-reaction I_2 (x) V does NOT anticommute with lattice chirality, breaking the D^2 product identity; replaced by the chirality-preserving deformation. |
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
| J_F γ_F = −γ_F J_F | T3 | Lean proved (`UJ_gammaF_anticommute`, via `gammaF_partner_flip`) |
| Unitality P_C + P_H + P_M = 1 | T3 | Lean proved (`unitality`): `-(genC²)` projects onto 8–15,16,17,24,25; `(genH k)²` onto 0–7 (`genH_sq_proj`); `(3/16)·∑ₐ(genM a)²` onto triplets 18–23,26–31 (`genM_sq_sum_proj`); supports partition 0–31 (`unitality_arith`). Zero sorrys. |
| Three generations (ℂ⁹⁶ or ℂ³²⊗ℂ³) | T5 | Open (Framework §2.1.6) |

## Rung 7 — Spectral Triple D_F

| Component | Tier | Evidence |
|---|---|---|
| D_F block matrix (A,B,C,E) (definition) | T2 | `ThetLogos.FiniteSpectralTriple.buildDirac` |
| D_F* = D_F; γ_F D_F + D_F γ_F = 0 | T3 | Lean proved (`buildDirac_self_adjoint`, `buildDirac_gamma_odd`) |
| J_F D_F = D_F J_F (conditional on B = Ā, C,E symmetric) | T3 | Lean proved (`buildDirac_J_compat`, 16-case analysis; ledger previously mislabeled this as sorry — corrected 2026-09-27) |
| One-generation SM ansatz D_F: complex Yukawas (yν,yE,yU,yD) + Majorana yR; B = Ā, C = 0; conventional flavour slots (ν_L(0)↔ν_R(8), e_L(1)↔e_R(9), u/d colours) | T2 | `ThetLogos.MartinettiRep.smDirac` (definition). **ANSATZ — imposed, not derived**: order-one alone leaves a 46-dim nullspace (T4); 36 extra dims uncharacterized |
| Ansatz: {Γ,D_F} = 0; D_F* = D_F; UJ·D̄_F = D_F·UJ (KO-dim 6: JD = DJ) | T3 | Lean proved (`smDirac_grading_odd`, `smDirac_self_adjoint`, `smDirac_J_compat`). Zero sorrys. |

## Rung 8 — Order Conditions

| Component | Tier | Evidence |
|---|---|---|
| Order-zero [π(a), π°(b)] = 0 | T3 | Lean proof (`order_zero_condition`, pending build) + numerical < 1e-14 (`order_zero.py`, `examples/`) |
| Order-one [[D_F,π(a)],π°(b)] = 0 for the SM ansatz (12 selected generators, 144 pairs) | T3 | Lean proved 2026-09-27 (`ThetLogos.MartinettiRep.smDirac_order_one`): all 144 double commutators vanish for arbitrary complex (yν,yE,yU,yD,yR); zero sorrys. **Imposed ansatz, not derived**: T4 evidence stands — 46-dim order-one nullspace, ~36 extra directions (`attack4_corrected/REPORT.md`) |
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

## Rung 9b — FRG Constitutive Pipeline (Engine #11)

| Component | Tier | Evidence |
|---|---|---|
| Wetterich flow, Litim regulator, one-loop truncation | T4 | `python/thet_logos/frg_constitutive.py`; flow reproduces analytic Drude to 3.3e-8 |
| ε_eff(ω) extraction at k₀ = 2π/d | T4 | Validated vs analytic; plasma edge correct |
| Kramers–Kronig compliance | T4 | Cauchy-PV numerical audit, residual 2.2e-9 |
| Passivity Im(ε) > 0 | T4 | min 1.7e-3 on ω > 0 |
| Cubic (O_h) isotropy | T4 | Anisotropy/off-diagonal exactly 0 |
| μ_eff = 1, ξ_eff = 0 | T4 | Truncation artifacts (non-magnetic, achiral UV), reported not hidden |
| Spatial dispersion (q-dependence) | T5 | Not implemented; optical q→0 only |
| Real metamaterial prediction | T5 | Not asserted — Drude UV is calibration, not discovery |

## Rung 10 — Epistemic Ledger

| Component | Tier | Evidence |
|---|---|---|
| Five-tier system itself | (meta) | Framework §5; this directory |

## Rung 9c — Finite-Lattice Kohn-Sham DFT (Engine #12, SPEC ONLY)

| Component | Tier | Evidence |
|---|---|---|
| Engine #12 specification | T5 | `whitepaper/engine12-dft-spec.md`; no implementation yet |
| Falsifiable targets T1–T4 (convergence, BALDA vs exact, HK inversion, dissociation) | T5 | Defined, not run |
| Kill criteria K1–K4 | T5 | Defined; 2-day time box |
| Claim of any molecular/chemistry result | T5 | Explicitly excluded — lattice Hubbard only |

## Cross-cutting

| Component | Tier | Evidence |
|---|---|---|
| Spectral-action coefficients a₀, a₂, a₄ (table) | T4 | Standard NCG results, recorded from literature |
| Lichnerowicz spin-connection cross-term | T5 | Formula missing from source |
| Torsion sector (ℂ³⁹ vs M₇(ℂ) ⊂ End(ℂ³²)) | T5 | Undecided in source |
| Formal Möbius-bundle chromatic topology | T5 | Open (Framework §2: "does not yet constitute") |
| Coupling unification; mass predictions | T5 | Open/withdrawn as predictions |
| Complete Lean archive (zero-sorry) | T5 | Open — this pass ends with 10 documented sorrys; `lake build` green 2026-09-21 |

## 2026-09-27 — Order-zero COMPLETE (144/144, zero sorrys)

**Status**: T1 (machine-checked proof, Lean 4, zero sorrys in MartinettiRep.lean)

**Result**: All 144 generator pairs satisfy [smGen g1, smGenOp g2] = 0.

**Sectors proven**:
- C/C°: 1 pair (order_zero_C_C)
- H/H°: 9 pairs (order_zero_H_H)
- M/M°: 64 pairs (order_zero_M_M)
- C/H°, H/C°: 3+3 pairs
- C/M°, M/C°: 8+8 pairs
- H/M°: 24 pairs (order_zero_H_M, tensor-product structure)
- M/H°: 24 pairs (order_zero_M_H, via duality: transpose + UJ conjugation)

**Key techniques**:
- order_zero_H_M: tensor-product factorization on indices 2-7 (flavour ⊗ colour)
- order_zero_M_H: duality from order_zero_H_M using UJᵀ=UJ and UJ*UJ=1
- smGen_order_zero: structured 144-case split

**Commit**: 668daf5 (local, push pending auth)

**Honesty boundary**: Order-zero is ONE axiom. J²=1 and JΓ=-ΓJ now Lean-proven
(`UJ_mul_self`, `UJ_gammaF_anticommute`). Unitality now Lean-proven
(`unitality`, zero sorrys): ℂ-projection `-genC²` (`genC_sq_proj`,
`genC_sq_proj_offdiag`); ℍ-projection `(genH k)²` onto 0–7 (`genH_sq_proj`,
`genH_sq_offdiag`, via Pauli square `pauli_sq`); M₃-projection
`(3/16)·∑ₐ(genM a)²` onto the colour triplets (`genM_sq_sum_proj`,
`genM_sq_sum_offdiag`, via Gell-Mann square sum `gellMann_sq_sum`); the three
supports partition all 32 dimensions (`unitality_arith`). Faithfulness
(kernel = {0}) now Lean-proven (`faithful_blocks`:
block-form independence using `genC_faithful`, `genH_linear_independent`,
`genM_linear_independent` on disjoint supports; zero sorrys in
`MartinettiRep.lean`). Still open: order-one, D_F construction, Yukawa derivation.
A verified representation is not a verified SM derivation.

## 2026-09-27 — CB1 + CB2: colour-blindness of imposed smDirac ansatz (T3)

**Status**: T1 (machine-checked proof, Lean 4, zero new sorrys in MartinettiRep.lean)

**Results**:
- **CB1** (`CB1`): `[smDirac yNu yE yU yD yR, genM a] = 0` for arbitrary complex
  Yukawas and all 8 colour generators. The imposed one-generation Dirac ansatz
  is colour-blind: D acts as a scalar on each colour triplet (via
  `smDirac_triplet_row`/`smDirac_triplet_val`), genM acts via Gell-Mann.
- **CB2** (`CB2`): `[smDirac yNu yE yU yD yR, UJ*(genM a)ᵀ*UJ] = 0`.
  Proof via: genM Hermitian (`genM_herm`, from Gell-Mann entrywise Hermiticity
  `gellMann_herm`), J-compatibility (`smDirac_J_compat`), UJ²=1 (`UJ_mul_self`).
  Key step: `[D̄, Gᵀ]=0` (`Dbar_Gt_comm`) from `[D, (Ḡ)ᵀ]=0` via `map star`,
  then UJ-conjugation.
- **jacobi_reorder**: `[[D,G1],G2°] = [[D,G2°],G1]` when `[G1,G2°]=0` (order-zero).

**Order-one coverage**: CB1 gives `[[D,genM _], _°]=0` (M-row, 96 pairs).
CB2 + jacobi_reorder gives `[[D,_], (genM _)°]=0` (M°-column, 96 pairs,
64 overlap). **Remaining**: 16 pairs with (C/H, C°/H°) — require support/
diagonal-constancy arguments (numerical audit: `[D,C]` on 0↔8 Yukawa blocks,
`C°` diagonal-constant there; `[D,H]` on 0–15, `H°` on 16–23, disjoint).

**Commit**: b4b5c7e (local, no push from subagent)

**Honesty boundary**: The ansatz is **imposed**, not derived. CB1/CB2 do not
alter the corrected Attack 4 T4 verdict (2026-09-27): 46-dimensional order-one
nullspace, 10 expected SM directions, ~36 extra uncharacterized directions,
nullity gap 0.36 — **NO-GO** for order-one uniquely selecting the SM ansatz.
One generation only; ℂ⁹⁶ untested.

## 2026-09-27 — Full order-one: all 144 pairs machine-proven (T3)

**Status**: T3 (machine-checked proof, Lean 4, zero sorrys; full `lake build` passes, 3316 jobs)

**Theorem**: `ThetLogos.MartinettiRep.smDirac_order_one` — for arbitrary complex
(yν, yE, yU, yD, yR), `smDiracOrderOne` holds: all 144 double commutators
`[[D, smGen g1], smGenOp g2]` vanish.

**Proof structure**:
- (C,C°) `orderOne_C_C`: `[D,genC]` supported on indices < 16 (`DC_cases`,
  `DC_supp16`); C° diagonal and constant on its support (`Cop_diag_val`,
  `DC_Cop_const`); commutes via `diag_mul_comm_of_const_on_supp`.
- (H,C°) `orderOne_H_C`: same via `DH_Cop_const` / `DH_supp16`.
- (C,H°) `orderOne_C_H` and (H,H°) `orderOne_H_H`: `[D,genC]`/`[D,genH k]`
  live on < 16, H° on 16–23 (`UJ_genH_transpose_UJ_supp`); both products
  vanish by `disjoint_mul_zero`.
- M-row `orderOne_M_row` (96 pairs): CB1 makes `[D, genM a] = 0`.
- M°-column `orderOne_M_col` (96 pairs, 64 overlap): `jacobi_reorder` +
  `orderZero_genM_op` + CB2.
- Assembly `smDirac_order_one`: `fin_cases` over all 144 (g1, g2).

**Coverage**: 144/144 selected pairs. Single commutators `[D,genC]`, `[D,genH]`
are genuinely nonzero (not claimed zero); only the double commutators vanish.

**Honesty boundary**: Order-one is machine-proven **for the imposed
one-generation SM ansatz over the selected 12-generator family**. This does
not derive the ansatz and does not uniquely select the Standard Model — the
Attack 4 T4 NO-GO stands (46 vs 10 real dimensions, ~36 extra directions
uncharacterized). One generation only; ℂ⁹⁶ untested; flavour placement
conventional.

## 2026-09-27 — Three-generation triplication: T4 census + T2/T3 Lean scaffolding

**Status**: T4 numerical (Steps 1–3 complete); T2/T3 Lean (definitions + Γ₃ lemmas proven; full diagonal-case proofs deferred)

**T4 Numerical** (`attack4_corrected/attack4_3gen.py`, `attack4_corrected/THREE_GEN.md`):
- Imposed ℂ⁹⁶ = ℂ³² ⊗ ℂ³ with arbitrary complex 3×3 Yukawas (Yν,Ye,Yu,Yd),
  complex symmetric 3×3 M_R. Triplication is IMPOSED, not derived.
- 3 random trials: exact zeros for grading-oddness, self-adjointness,
  J-compatibility, order-one (144 SM-selected + 144 all-lifted pairs).
  Non-vacuous: ‖[D,X₀]‖ ≈ 17–19. J-compat breaks (6.70e+00) for non-symmetric M_R.
- Admissible dim at ℂ⁹⁶: 2352 (= 3×272 diag + 3×512 off-diag).
- **Order-one nullity: 402** (= 3×46 diagonal + 3×88 mixing-pair).
  Diagonal 46 reproduces 1-gen; mixing 88 is new. Confirms predicted 402 ≠ 414.
- Step 4 (classification of 88 mixing directions) **complete 2026-09-27**
  (`attack4_corrected/classify_mixing.py`, verified by `verify_mixing.py`,
  write-up `attack4_corrected/MIXING_264.md`): per pair, 18 SM-like mixing
  (8 complex Yukawa + 1 complex MR) + 16 flipped Yukawa mixing (8 complex) +
  54 exotic Majorana mixing (27 complex; E-symmetry dropped). B=conj(A),
  Bd=conj(Ad), C=0, Ed real-linear in E, color locking holds. Direct-sum
  verified to ~1e-15. Charge conservation kills all 54 exotic; one-Higgs
  shelves the 16 flipped; 18 SM-like survive per pair → 3×18+3×10 = 84 =
  SM flavor count (T4).

**T2/T3 Lean** (`lean/ThetLogos/ThreeGen.lean`, imports into `ThetLogos.lean`):
- Definitions: `I96`, `gamma3`, `UJ3`, `smGen3`, `smGenOp3`, `smDirac3diag`.
- Proven (zero sorrys, full `lake build` passes): `gamma3_apply`, `gamma3_diag`,
  `gamma3_mul_apply`, `mul_gamma3_apply` (blockwise Γ₃ action).
- Deferred: full diagonal-case grading-odd/self-adjoint/J-compat/order-one
  proofs (mathematics is D₁⊗I₃ Kronecker reduction; tactic engineering deferred).
- Arbitrary-matrix case remains T4-only by design.

**Honesty boundary**: Three generations are imposed. Flavour structure (CKM/PMNS,
masses) is input. Order-one does not select the SM (402 admitted, 84 selected
by charge conservation + one-Higgs minimality). T4 ≠ T3. The 36 extra 1-gen
directions (DIRECTIONS_36.md) are now characterized at 3-gen (MIXING_264.md):
per pair, 16 flipped + 54 exotic join the 18 SM-like mixing dims.
