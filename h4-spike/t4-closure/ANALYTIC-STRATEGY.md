# T4 closure: diagonal-pair killing mechanism (2026-09-30)

Computational verification of `Module.finrank ℝ W22 ≤ 22` is COMPLETE (scripts in this
directory). The Lean formalization is NOT yet done. This note records the analytic
strategy so a future session can pick it up.

## Computational result

- The 4 linear conditions (grading-odd, [D,cfMat]=0, self-adjoint, J-compatible) as a
  real constraint matrix → nullspace dim **92** (`v4.py`, `v4basis.npy`).
- All 144 order-one pairs `[[D, smGen a], smGenOp b] = 0` as real-linear constraints
  on V4 → rank **70**, null dim **22** (`orderone.py`, `killers*.py`).
- The 22-dim nullspace is exactly spanned by the 22 explicit `dirs22` (10 SM + 12 exotic)
  (`w22basis_v4coords.npy`, `w22mats.npy`).
- Nullspace support is exactly the 72-entry SM∪exotic support — no entries outside.

## Master lemma (diagonal-pair killing)

For diagonal `A = diag(λ)`, `B = diag(μ)`:

    [[D, A], B](i,j) = D(i,j) · (λⱼ − λᵢ) · (μⱼ − μᵢ)

Hence order-one `[[D,A],B] = 0` forces `D(i,j) = 0` whenever both eigenvalue
differences are nonzero. This is the uniform killer — no case analysis per entry.

## The 16 killing pairs

Diagonal generators: `smGen 0 = C`, `smGen 3 = H2 = σ₃`, `smGen 6 = M2 = λ₃`,
`smGen 11 = M7 = λ₈`; their opposites are also diagonal.

The 104 "extra" entries (allowed by the 4 linear conditions but outside the 72-support)
are ALL killed by 16 diagonal-diagonal order-one pairs:
- `(C, C°)` uniformly kills all 8 lepton entries `(0/1 × 16/17)`.
- `(C, M2°)` uniformly kills all 24 fundamental quark entries `(2..7 × 10..15)` —
  the μ^{M2} eigenvalues always differ on non-SM/exotic pairs.
- Self-adjointness + J-compatibility propagate these to the full 96 quark entries;
  24 more `(10..15 × 24/25)` fall to J + cfMat.
- Union of the 16 pairs kills all 104. Verifiable by a computable killer-function + `decide`
  over the 952-case analysis (`killers*.py`).

## SA/J orbit structure on the 72-entry support

- 19 orbits (38 real params). 11 orbits contain the pivots directly.
- 8 are **color-copy orbits** (e.g. `(4,12)` must equal `(2,10) = yU`) requiring
  **color-universality** via off-diagonal (M,M°) order-one pairs. The identifications are
  forced (nullspace is 22-dim, not 38-dim) but the minimal explicit killing pairs were
  NOT yet identified (`color_id*.py`, `orbits.py`).

## What the Lean formalization needs

1. Diagonal identifications: `smGen 3/6/11` as diagonal matrices (unfold `genH`/`genM`,
   case analysis on `tripletOf`/`pauli`/`gellMann`).
2. Master lemma `oo_diag_kill`: matrix-entry computation for `[[D, diag λ], diag μ]`.
3. Killer-function + `decide` infrastructure for the support lemma.
4. Color-universality: 8 complex identifications via explicit off-diagonal pair lemmas
   (minimal pairs not yet found — start from `color_id*.py`).
5. Assemble: support lemma → block decomposition → `finrank ℝ W22 ≤ 22` → drop
   `h_census` from `cf_kernel_classification_46_22` in `CFKernel22.lean`.

## Status

`h_census : Module.finrank ℝ W22 = 22` REMAINS in `CFKernel22.lean` (T4, stated not proved).
The announcement trigger is NOT met. Lean files untouched by this analysis; the
started `CFKernel22Dim.lean` (eigenvalue defs only) was removed rather than left
with sorrys.
