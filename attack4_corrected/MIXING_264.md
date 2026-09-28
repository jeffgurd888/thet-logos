# Mixing-Block Classification — the 264 generation-mixing directions

**Status:** T4 numerical classification (not a theorem). **Date:** 2026-09-27.
**Scope:** one unordered generation pair (g,g′), g<g′; the 88-dim order-one
nullspace of the off-diagonal 32×32 block. Times three pairs = 264.

## Result

The 88 real dimensions per generation pair decompose as a **direct sum of
slot-disjoint subspaces**:

| family | real dims | complex params | description |
|---|---|---|---|
| SM-like mixing | 18 | 8 Yukawa + 1 MR | ordinary generation-mixing Yukawas Y(g,g′), Y(g′,g) for Yν,Ye,Yu,Yd, plus MR(g,g′) |
| flipped Yukawa mixing | 16 | 8 | mixing analogue of the 1-gen flipped Yukawas (off-diagonal within isospin pairs) |
| exotic Majorana mixing | 54 | 27 | general non-symmetric E-block entries (symmetry dropped vs 1-gen) |
| **total** | **88** | | |

**Physics selection** (same rules as the 1-gen DIRECTIONS_36 verdict):
- **Charge conservation** kills all 54 exotic-Majorana dims: every one of the
  27 exotic E entries carries nonzero EM charge (Qp+Qq≠0); only the SM
  (νR,νR) entry is neutral.
- **One-Higgs minimality** shelves the 16 flipped dims (as in 1-gen).
- **Survives: 18 SM-like mixing dims per pair** (16 Yukawa + 2 Majorana).

Across three pairs: 3×18 = **54 mixing params**. With the 3×10 diagonal SM
params: **84 total = 4×18 (Yukawa 3×3 complex) + 12 (MR 3×3 symmetric)** —
exactly the SM flavor parameter count. Order-one admits 402; physics selects 84.

## How it was computed

Script: `classify_mixing.py` (fixed tensor contraction
`Mnull = tensordot(vecs, P_off, axes=([0],[0]))` → (88,32,32)).
Independent verification: `verify_mixing.py` (proper complex z=1,i patterns).

1. Built the 512-dim real space of grading-odd J-compatible 32×32 blocks
   (P_off, real-orthonormal to 4.6e-15).
2. Normal equations N_off for the 576 order-one pairs [[M,X],Y°]; nullspace
   dim = 88 (eigenvalues < 1e-10).
3. Direct recheck: max ||[[M,X],Y°]|| = **1.62e-15** over 88×576.
4. Grading oddness 3.2e-15, J-compat 3.9e-15, C=Cd=0 (2.5e-15).
5. Slot census + explicit pattern families (see below).

## Structural facts (all numerical, residuals ~1e-15)

- **A-sector (A,Ad): 32 real.** A alone 16, Ad alone 16, independent.
  A carries the 8 (g,g′)-ordering complex Yukawas (4 SM + 4 flipped);
  Ad carries the 8 (g′,g)-ordering ones. B=conj(A), Bd=conj(Ad) exactly;
  B,Bd determined by (A,Ad). C=0 forced.
- **E-sector (E,Ed): 56 real.** E full (56 real = 28 complex) on 28 entries;
  Ed = L(E) a fixed real-linear map (lstsq residual 2.1e-15). **E-symmetry
  dropped**: max||E−Eᵀ|| = 1.15 (vs 0 in 1-gen). E support is an "L-shape":
  rows 0–1 (νR,eR) full + columns 0–1 elsewhere.
- **Color locking** holds in A/B/Ad/Bd (5.8e-16); Yu/Yd mixing params are
  color-universal as in the SM.
- **Direct-sum decomposition** verified by slot-disjoint intersections:
  dim(Mnull ∩ SM-A slots)=16, ∩ flipped-A slots=16, ∩ E slots=56; sum=88.
- **Explicit families** (z=1 and z=i built separately — the z→pattern map is
  real-linear, not complex-linear):
  - 18 SM-like patterns: rank 18, in Mnull (5.1e-15).
  - 16 flipped patterns: rank 16, in Mnull (4.8e-15).
  - 54 exotic-E patterns (E + L(E)): rank 54, in Mnull (5.7e-15).
  - Joint rank 88, projection residual 4.7e-15. Families mutually independent
    (SM+flipped=34, SM+exotic=72).

## Interpretation

The mixing nullspace is **exactly the complexification the SM needs**:
each 1-gen direction tensored with generation mixing, with the (g,g′)/(g′,g)
ordering doubling the Yukawa-like params (16→32) and the Majorana symmetry
relaxing (30→56). **No genuinely new structures** beyond this — the
classification is the 1-gen verdict (DIRECTIONS_36) crossed with 3×3 flavor.

The 18 SM-like mixing dims per pair are the off-diagonal entries of the
four Yukawa matrices (4 types × 2 orderings × 2 real = 16) plus the
off-diagonal MR (2 real). These are the CKM/PMNS-relevant params — imposed,
not derived (T4).

## Caveats (T4, not a theorem)

- Numerical evidence only: finite-difference-free exact arithmetic residuals,
  but no Lean proof. Full diagonal 3-gen order-one theorem still deferred.
- Three generations and flavor matrices imposed, not derived.
- The exact complex-linear/conjugate-linear form of the E→Ed map L was not
  determined (only real-linearity).
- Charge-conservation and one-Higgs arguments are physical selection rules,
  not mathematical consequences of order-one.

## Verdict: GO (as classification)

The 264 mixing directions are fully classified, the decomposition is
machine-verified to ~1e-15, and the physics-selected 54+30=84 matches the SM
flavor count. This completes Step 4 of the three-generation triplication.

## Artifacts

- `classify_mixing.py` — main classification (N_off cached in results3gen/).
- `verify_mixing.py` — independent pattern-family verification.
- `results3gen/Mnull_off.npy` — 88×32×32 orthonormal nullspace basis.
- `results3gen/N_off.npy` — 512×512 normal-equation matrix.
- `results3gen/numbers_mixing.json` — machine-readable numbers (**note:**
  its `rank_A_sector`/`rank_B_sector` (16) suffer a subspace-coincidence
  artifact; corrected values are 32 — see verify_mixing.py).
