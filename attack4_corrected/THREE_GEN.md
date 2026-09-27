# Three-Generation Triplication — T4 Numerical Report

**Date:** 2026-09-27  
**Tier:** T4 (numerical evidence only — NOT a Lean theorem)  
**Script:** `attack4_corrected/attack4_3gen.py`  
**Status:** Steps 1–3 complete; Step 4 (classification) hit a shape bug

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

## Step 4: Classification (INCOMPLETE)

The script crashed in Step 4 with:
```
ValueError: shape-mismatch for sum
  File ".../attack4_3gen.py", line 231, in <module>
    Mnull = np.tensordot(vecs.T, P_off, axes=([0],[0]))
```

The null-space basis vectors (`vecs`) have a different leading dimension than
expected for the tensordot with `P_off`. The classification of the 88
mixing-pair null directions into Yukawa-like vs Majorana-like (and the
Yukawa/Majorana split of the 46 diagonal directions) was not completed.

**This does not affect the nullity counts** (Steps 1–3), which are the primary
result. The classification is a refinement for future work.

## Honesty boundary

- **T4 only.** These are numerical SVD/eigenvalue computations, not Lean theorems.
- **Imposed, not derived.** Three generations, the tensor-product structure,
  and the Yukawa matrices are inputs.
- **No flavour physics derived.** CKM/PMNS, masses, and hierarchies remain inputs.
- **Order-one does not select the SM.** The 402 null directions include many
  beyond the 10 conventional SM Yukawa+Majorana directions per generation.
- **Step 4 incomplete.** The 88 mixing directions are counted but not classified.

## Files

- Script: `attack4_corrected/attack4_3gen.py`
- 1-gen basis: `attack4_corrected/` (Adm⁺ basis, 272×32×32)
- This report: `attack4_corrected/THREE_GEN.md`
- Lean T2/T3: `lean/ThetLogos/ThreeGen.lean` (definitions + Γ₃ blockwise lemmas;
  diagonal-case full proofs deferred, arbitrary-case is T4-only)
