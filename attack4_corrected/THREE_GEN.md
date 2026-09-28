# Three-Generation Triplication — T4 Numerical Report

**Date:** 2026-09-27  
**Tier:** T4 (numerical evidence only — NOT a Lean theorem)  
**Script:** `attack4_corrected/attack4_3gen.py`  
**Status:** Steps 1–4 complete (classification done 2026-09-27; see MIXING_264.md)

## What was imposed

The one-generation SM finite geometry (ℂ³², D₁, Γ, J, π) is triplicated to
ℂ⁹⁶ = ℂ³² ⊗ ℂ³ by imposing:

- π₃(a) = π(a) ⊗ I₃ (representation)
- Γ₃ = Γ ⊗ I₃ (grading)
- U_{J,3} = U_J ⊗ I₃ (real structure)
- D₃: 96×96 Dirac ansatz with arbitrary complex 3×3 Yukawa matrices
  (Y_ν, Y_e, Y_u, Y_d), complex symmetric 3×3 Majorana M_R

**Nothing derives three generations.** This is an imposed ansatz. CKM/PMNS,
mass hierarchies, and flavour structure are inputs, not outputs.

## Step 1: D₃ ansatz verification (3 random trials)

Arbitrary complex 3×3 Yukawas, symmetric M_R. All residuals are exact
displayed zeros (float64):

| Trial | ‖{D,G}‖ | ‖D*−D‖ | ‖UJ·conj(D)−D·UJ‖ | max ‖[[D,X],Y°]‖ (144+144) | ‖[D,X₀]‖ |
|-------|----------|---------|-------------------|---------------------------|----------|
| 0 | 0.00e+00 | 0.00e+00 | 0.00e+00 | 0.00e+00 / 0.00e+00 | 1.79e+01 |
| 1 | 0.00e+00 | 0.00e+00 | 0.00e+00 | 0.00e+00 / 0.00e+00 | 1.72e+01 |
| 2 | 0.00e+00 | 0.00e+00 | 0.00e+00 | 0.00e+00 / 0.00e+00 | 1.92e+01 |

- **Grading-oddness:** {Γ₃, D₃} = 0 ✓
- **Self-adjointness:** D₃* = D₃ ✓
- **J-compatibility:** UJ·conj(D₃) = D₃·UJ ✓ (requires symmetric M_R)
- **Order-one:** all 144 SM-selected + 144 all-lifted generator pairs ✓
- **Non-vacuity:** ‖[D,X₀]‖ ≈ 17–19 ≫ 0 (D₃ is not a multiple of identity)

**Sanity checks:**
- Non-symmetric M_R → ‖D*−D‖ = 0.00e+00 (self-adjointness needs no symmetry) ✓
- Non-symmetric M_R → ‖UJ·conj(D)−D·UJ‖ = 6.70e+00 ≫ 0 (J-compat needs symmetry) ✓

## Step 2: Admissible-space census at ℂ⁹⁶

- 1-gen Adm⁺ basis: (272, 32, 32) [loaded from prior run]
- Grading-odd Hermitian 32-basis: 512
- J-anti-compatible dimension: 240
- Off-diagonal block basis: 512
- Max ‖UJ·conj(H)+H·UJ‖ on Bminus: 7.06e-15
- Max ‖UJ·conj(M)−M·UJ‖: 7.06e-15; max ‖{M,G}‖: 6.02e-15
- **Admissible dim at ℂ⁹⁶: 2352** (= 3×272 diagonal + 3×512 off-diagonal)

## Step 3: Order-one nullity per generation-block type

Normal-equation eigenvalues (squared singular values); cutoff with gap:

| Block type | P (dim) | Nullity | Gap | Eigenvalues at cutoff |
|------------|---------|---------|-----|----------------------|
| Diagonal (g,g) | 272 | **46** | 0.774 | [215.11 ×4] |
| Off-diagonal (g≠g′) | 512 | **88** | 0.774 | [215.11 ×4] |

**TOTAL order-one nullity at ℂ⁹⁶: 402** (= 3×46 diagonal + 3×88 mixing)

This confirms the parameter-count prediction of 402, NOT 9×46=414:
- Yukawa-like A: 8 positions × 18 real = 144
- Majorana-like E: 2 symmetric diag slots ×12 + 13 arbitrary cross slots ×18 = 258
- Total: 144 + 258 = 402

The diagonal nullity 46 reproduces the one-generation result. The mixing-pair
nullity 88 reflects the additional flavour-mixing directions.

## Step 4: Classification (COMPLETE 2026-09-27)

Step 4 is done. New script `classify_mixing.py` (bug fixed; N_off cached in
`results3gen/`), independently verified by `verify_mixing.py`. Full write-up:
**[MIXING_264.md](MIXING_264.md)**.

Per unordered generation pair, the 88 real dims decompose as a direct sum:
- **SM-like mixing: 18** (8 complex Yukawa mixing + 1 complex MR mixing).
- **Flipped Yukawa mixing: 16** (8 complex; mixing analogue of 1-gen flipped).
- **Exotic Majorana mixing: 54** (27 complex; E-symmetry dropped vs 1-gen).
- B=conj(A), Bd=conj(Ad), C=0; Ed = real-linear fn of E; color locking holds.

Charge conservation kills all 54 exotic (every exotic E entry is charged);
one-Higgs minimality shelves the 16 flipped. **18 SM-like survive per pair.**
Total physics-selected: 3×18 (mixing) + 3×10 (diagonal) = **84** =
4×18 Yukawa + 12 MR = the SM flavor parameter count.

**This does not affect the nullity counts** (Steps 1–3), which are the primary
result. The classification is now complete (T4 numerical, not a theorem).

## Honesty boundary

- **T4 only.** These are numerical SVD/eigenvalue computations, not Lean theorems.
- **Imposed, not derived.** Three generations, the tensor-product structure,
  and the Yukawa matrices are inputs.
- **No flavour physics derived.** CKM/PMNS, masses, and hierarchies remain inputs.
- **Order-one does not select the SM.** The 402 null directions include many
  beyond the 10 conventional SM Yukawa+Majorana directions per generation.
- **Step 4 complete (2026-09-27).** The 88 mixing directions per pair are
  classified: 18 SM-like + 16 flipped + 54 exotic Majorana (MIXING_264.md).

## Files

- Script: `attack4_corrected/attack4_3gen.py`
- 1-gen basis: `attack4_corrected/` (Adm⁺ basis, 272×32×32)
- This report: `attack4_corrected/THREE_GEN.md`
- Lean T2/T3: `lean/ThetLogos/ThreeGen.lean` (definitions + Γ₃ blockwise lemmas;
  diagonal-case full proofs deferred, arbitrary-case is T4-only)

## Step 5: Spectral action over the 84 selected directions (COMPLETE 2026-09-27)

New script `spectral_action_84.py`; full write-up:
**[SPECTRAL_ACTION_84.md](SPECTRAL_ACTION_84.md)**.

D_96 parameterized by the 84 physical parameters (Y_ν,Y_e,Y_u,Y_d 3×3
complex + symmetric 3×3 M_R); inner fluctuations OFF (finite-triple traces
only). Derived structural formulas, verified by brute force:

- **Tr(D²)** = 4·(‖Y_ν‖²_F + ‖Y_e‖²_F + 3‖Y_u‖²_F + 3‖Y_d‖²_F) + 2‖M_R‖²_F
- **Tr(D⁴)** = 4·[q(Y_ν)+q(Y_e)+3q(Y_u)+3q(Y_d)] − 2q(Y_ν)
  + ‖Y_ν†Y_ν + M_R†M_R‖²_F + ‖conj(Y_ν†Y_ν) + M_RM_R†‖²_F + 4‖Y_νM_R†‖²_F
  (q(Y) = Tr((Y†Y)²)); Tr(D) = Tr(D³) = 0.

Three parameter points (hierarchical, random, CKM-like mixing): brute vs
structural agree to machine precision (worst rel. err 1.8e-16); D²
slot-block structure audited on a fresh seed (36 nonzero blocks, worst
residual 7.7e-15). Monomial structure matches Chamseddine–Connes–Marcolli
𝔞…𝔢 qualitatively (uniform factor-4 normalization from our block
convention, stated). Hierarchical point: 𝔞 ≈ 3.008 ≈ 3y_t² (top dominance).

Two formula bugs caught by the random point and fixed (off-diagonal D²
slot blocks; slot-24 conj slip) — see report §6. Cutoff moments f_k stay
symbolic: no Higgs-mass or cosmological-constant prediction claimed. T4.
