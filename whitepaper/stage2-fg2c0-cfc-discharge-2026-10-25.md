# FG-2c-0 LANDED FULL — the cfc for T̂_c, T̂² ≤ T̂, and step 0 discharged

**Date:** 2026-10-25 · **Status: T1** (parent-verified: forced
from-scratch rebuild exit 0 on the exact shipped text; olean present;
0 sorry in module; corpus sorry census unchanged at exactly 7).
**Module:** `lean/ThetLogos/LatticeSliceCfc.lean` — 64 strict,
12 instances, 4 defs. **Axioms:** `sliceCfc_package` and the
checked specializations print exactly
[propext, Classical.choice, Quot.sound].

## What stands

- **§0 (infrastructure):** pinned Mathlib has NO
  `StarOrderedRing (E →L[ℂ] E)`; the module builds it from a cfc
  square root (`cfc Real.sqrt`), switching on the CFC order API for
  continuous linear maps. (The §1b instance cache is load-bearing
  for elaboration and carries no mathematical content.)
- **Brick 1:** `sliceTc_spectrum_subset : spectrum ℝ T̂_c ⊆ [0,1]`,
  and polynomial agreement for the cfc
  (`sliceCfc_id/pow/const/one_sub/defect_pow/mul_defect_pow/truncation`).
- **Brick 2:** the order-to-pairing bridge
  `sliceCfc_pairing_nonneg`; **`sliceTc_sq_le_self : T̂_c² ≤ T̂_c`**
  in operator and pairing form; and
  **`sliceTc_mixed_pairing_nonneg`** — `⟪x, T̂_c Â_c^j x⟫.re ≥ 0`
  for all j, step 0's exact missing input.
- **Brick 3 (step 0 DISCHARGED, monotone-pairing route):** the
  truncation approximants as single cfc pairings; Bernoulli bound
  `S_{K,n} ≤ n²`; form control `q_K(p_n x) ≤ n²‖x‖²`; the Cauchy
  identity and `sliceTrunc_tendsto` on `(ker T̂_c)⊥`; headline
  **`sliceFormClosure_eq_ker_orthogonal :
  sliceFormClosure = (ker T̂_c)ᗮ`** at general (G, ρ) under
  `SliceHPosOne`, packaged as `sliceCfc_package`, with free
  specializations at β = 0 and at the U(1) seat (all β ≥ 0, even N).

**Consequence:** FG-2b's carrier is now IDENTIFIED — H′, defined
by form-norm completion, equals `(ker T̂_c)ᗮ` as a theorem; the
FG-2a density residue (density inside the kernel complement) is
closed by the same stroke. The Hamiltonian Ĥ of FG-2b lives on a
named space.

**Not asserted:** `exp(−Ĥ) = T̂_c` (FG-2c proper remains: bricks
2c-1 resolvent family, 2c-3/2c-2 constructs, 2c-4 IDENTIFY), no
Borel calculus for Ĥ, no uniformity in N, no continuum content.
**NO CLAIM; dials 0/4.**
