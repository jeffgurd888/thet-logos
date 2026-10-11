# Rung 2 lattice toy — results (T4-at-best, TOY)

> TOY. No continuum conclusions. No physical claims. Naive lattice Dirac; doublers not handled; a=1 toy units mixed with GeV-scale D_F.

- D_F kernel dim: 4; ||D_F|| = 228.8 GeV
- L=3 product: dim 10368, lattice kernel 4, product kernel 16 = 4 x 4 (sparse eigsh)
- D^2 identity rel err: 0.000e+00
- kernel factorization: D-resid 1.243e-15, finite leak 0.000e+00, lattice leak 1.373e-15, max Schmidt rank 4
- L=3 first excited sqrt: 0.866025 (toy units)
- L=4: product kernel 256 (expect 256), gap above block 1.000000 (via machine-verified D^2 identity, dense factor spectra)

## Toy fluctuation sweeps

### (a) finite one-form (links trivial)

- t_ratio=0.0: D_FA kernel 4 (was 4), rel change 0.000e+00
- t_ratio=0.001: D_FA kernel 4 (was 4), rel change 1.352e-03
- t_ratio=0.01: D_FA kernel 4 (was 4), rel change 1.352e-02
- t_ratio=0.05: D_FA kernel 4 (was 4), rel change 6.759e-02

### (b) U(1) links, L=3

- amp=0.0: lattice kernel 4 (free: 4), product kernel 16 (free: 16); would-be-16-block [0.000e+00, 2.581e-08], gap above block 8.660e-01
- amp=0.1: lattice kernel 0 (free: 4), product kernel 0 (free: 16); would-be-16-block [1.339e-02, 1.439e-02], gap above block 8.130e-01
- amp=0.3: lattice kernel 0 (free: 4), product kernel 0 (free: 16); would-be-16-block [1.993e-02, 3.665e-02], gap above block 6.816e-01
- amp=0.7: lattice kernel 0 (free: 4), product kernel 0 (free: 16); would-be-16-block [9.696e-02, 1.311e-01], gap above block 3.576e-01
- amp=3.141592653589793: lattice kernel 0 (free: 4), product kernel 0 (free: 16); would-be-16-block [4.989e-03, 8.665e-03], gap above block 3.183e-02

### (c) combined (links x finite one-form), L=3

- links only, amp=0.3: D_FA kernel 4 (D_F: 4), product kernel 0; would-be-16-block [3.443e-02, 4.431e-02], gap above block 6.731e-01
- finite 1-form only, t=0.01: D_FA kernel 4 (D_F: 4), product kernel 16; would-be-16-block [0.000e+00, 2.581e-08], gap above block 8.660e-01
- both: amp=0.3 x t=0.01: D_FA kernel 4 (D_F: 4), product kernel 0; would-be-16-block [4.862e-02, 5.602e-02], gap above block 6.655e-01

## What this toy shows / cannot show

- SHOWS (T4 toy): kernel multiplicity 4 x (lattice zeros) is an exact algebraic consequence of the product form D = D_lat (+) I + Gamma (+) D_F with {D_lat, Gamma} = 0; the finite 4-kernel sits inside the product kernel with Schmidt rank <= 4; toy fluctuations lift zeros but the block stays lowest.
- CANNOT SHOW: anything about the continuum, the SM, emergent spacetime, or physical scales. Naive discretization, unhandled doublers, no index theorem, single tiny volume, no continuum limit.
