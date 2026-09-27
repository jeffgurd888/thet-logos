# Attack 4 (Corrected) Report: 24-generator order-one rerun

**Date:** 2026-09-27
**Status:** T4 numerical exploration only. Not a theorem, not a Lean proof.
**Program:** `attack4_corrected/attack4_corrected.py` (self-contained, ~440 lines)

## What was corrected

The previous scan used **23** real generators — `M₃(C): {1, iλ_a, λ_a}` —
omitting **i·I₃**, the imaginary unit of the M₃ summand. This rerun uses the
full **24**:

| Block | Generators | Real dim |
|-------|-----------|----------|
| C | P_C, genC | 2 |
| H | P_H, i·genH₀, i·genH₁, i·genH₂ | 4 |
| M₃ | P_M, **i·P_M**, genM₀…₇, i·genM₀…₇ | 18 |

Generator matrices ported exactly from `lean/ThetLogos/MartinettiRep.lean`
(`genC`, `genH`, `genM`, Gell-Mann, Pauli), the representation Lean-proved
faithful (`faithful_blocks`, kernel = {0}). Conventions match
`Scaffold32.lean`: Γ = diag(+I₈,−I₈,−I₈,+I₈), UJ partner-swap,
π°(M) = UJ·Mᵀ·UJ, J-compat UJ·conj(D) = D·UJ.

## Results

### Step 1 — generator certification
- Real rank of the 24-generator set: **24** (per-block: 2 / 4 / 18) ✓
- Unitality: ‖P_C + P_H + P_M − I₃₂‖_F = **0.00e+00** (exact) ✓
- Grading-evenness: max ‖[Γ, π(a)]‖ = **0.00e+00** ✓
- Order-zero: max ‖[π(a), π°(b)]‖ = **0.00e+00** ✓

### Step 2 — admissible D_F basis (built from linear constraints, not assumed)
Self-adjoint + grading-odd + J-compatible, solved as a real linear system
(1024-dim hermitian space, 4096 constraint rows, SVD nullspace):
- **Dimension: 272** — confirms the expected count independently.
- Constraint residuals on basis: ≤ 6.9e−15. Real rank 272. ✓

### Step 3 — order-one nullspace, all 24² = 576 pairs
- **Nullity: 46** — **unchanged** from the 23-generator scan.
- The missing i·I₃ generator adds **no independent order-one constraint**.
- Normalized gap (corrected definition, smallest non-null SV / largest):
  **0.36**. Cutoff straddles 6.00 → 1.7e−13: clean separation, count robust.
- max |R·v| over nullspace basis: **7.66e−14**.
- ⚠️ Correction to the old report: its "gap 0.83–0.88" was a mislabeled
  interior ratio (s[46]/smax — same indexing slip existed in
  `repair_scan.py`). The true nullity gap is 0.36. The nullity count 46 is
  unaffected.

### Step 4 — SM Yukawa + Majorana directions
Explicit one-generation directions (conventional flavour choice within
degenerate irreps — see caveats): 4 complex Yukawas (Y_ν, Y_e, Y_u, Y_d)
+ 1 complex Majorana (Y_R, ν_R ↔ ν̄_R slot):

| direction | rel. order-one residual | nullspace fraction |
|-----------|------------------------|--------------------|
| Re/Im(Y_ν) | ≤ 2.2e−13 | 1.000000 |
| Re/Im(Y_e) | ≤ 2.2e−13 | 1.000000 |
| Re/Im(Y_u) | ≤ 1.8e−13 | 1.000000 |
| Re/Im(Y_d) | ≤ 1.9e−13 | 1.000000 |
| Re/Im(Y_R) | ≤ 1.9e−13 | 1.000000 |

- Rank of the 10 SM directions: **10**; rank inside nullspace: **10**.
- All are J-compatible and grading-odd to machine precision.
- Nullspace slot profile (basis-invariant): mean Yukawa-slot fraction
  0.348, Majorana-slot fraction 0.652; all 46 SVD basis vectors mixed
  (the old "8+38" split was basis-dependent).

### Step 5 — spectral gap sweep (Δ_gap vs top-Yukawa / Majorana scales)
Grid over (t_Y, t_M) ∈ [1e−2, 1e1]², hierarchy
(Y_ν, Y_e, Y_u, Y_d) = (1e−6, 1e−3, 5e−3, 1.0) at t_Y = 1:
- Δ_gap scales linearly with t_Y; at top scale (t_Y = 1) Δ_gap = 1e−3,
  set by the electron Yukawa floor in this 1-gen hierarchy.
- **Type-I seesaw emerges numerically**: the ν_L–ν_R–ν̄_R subsystem yields
  a light eigenvalue ≈ (t_Y·Y_ν)²/t_M wherever it sits above the ~1e−10
  numerical floor (e.g. t_Y=3, t_M=1e−2 → Δ_gap ≈ 1e−9 = seesaw value).
  Below the floor it is filtered and the electron Yukawa sets the gap.
- Saved in `results/sweep.npz`.

## Verdict

**NO-GO stands, now on the corrected 24-generator basis.** Order-one gives
nullity **46**, not 10. The SM Yukawa + Majorana content (10 real dims) is
a subspace of the 46, but order-one does not select it — 36 extra
dimensions survive. The five-block Dirac form remains an **ansatz**
(physical input), not a consequence of the first-order condition. The
omitted i·I₃ generator changed nothing: the 23-generator result was not
an artifact of the missing generator.

## Honest caveats (T4)

1. **Numerics, not proof.** Nullity via SVD with relative tolerance 1e−8;
   the Lean proof of "order-one → 46-dim nullspace" does not exist yet.
2. **Flavour assignment is conventional.** The representation does not
   distinguish the lepton doublet from quark doublets (H acts identically
   on all four); the "SM Yukawa form" tested here is an ansatz choice.
3. **One generation only** (ℂ³²). The ℂ⁹⁶ three-generation extension is
   untested.
4. **Gap numbers below ~1e−10** (relative to unit scale) are numerical
   floor, not physics.
5. The 36 extra nullspace dimensions are **uncharacterized** (physical?
   gauge artifact? representation redundancy?).

## Files

- `attack4_corrected.py` — the program (Steps 1–5)
- `results/generators.npy` — (24,32,32) complex generator matrices
- `results/dbasis.npy` — (272,32,32) admissible D_F basis
- `results/V_null.npy` — (272,46) real orthonormal nullspace coefficients
- `results/Dnull.npy` — (46,32,32) nullspace Dirac matrices
- `results/sm_coeffs.npy` + `sm_labels.json` — 10 SM direction coefficients
- `results/sweep.npz` — spectral-gap grid (tY, tM, gap)
- `results/numbers.json` — headline numbers
- `run2.log`, `run3.log` — run logs (run1 superseded: gap mislabeled;
  run2 crashed on a scoping bug before writing numbers.json)
