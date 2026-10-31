# SHELF-5 — LANDED FULL: finite-dimensional Perron–Frobenius (positive-matrix case), both halves at full strength

**Verdict: SHELF-5 FULL. The corpus now owns a citable finite-dimensional Perron–Frobenius theorem where the pin owns only the irreducible/primitive graph interface and fragments of spectral theory. For a strictly positive real matrix: a positive eigenvalue with a strictly positive eigenvector exists, and it is the spectral radius — every complex eigenvalue of the complexification is bounded by it in modulus. The pre-named PARTIAL seam (uniqueness in place of maximality) was not needed. The prose-level PF/Jentzsch invocations in the corpus's transfer modules retire at the finite-dimensional level. NO CLAIM. Dials 0/4.**

## What landed

- **`perronFrobenius`:** for finite `n`, `[Nonempty n]`, `A : Matrix n n ℝ` with `∀ i j, 0 < A i j`: there exist `lam : ℝ` and `x : n → ℝ` with `0 < lam`, `∀ i, 0 < x i`, `A *ᵥ x = lam • x`, and for every complex eigenvalue `mu` of the complexification (`A.map Complex.ofReal`) with nonzero eigenvector, `‖mu‖ ≤ lam`.
- **`isPrimitive_of_pos`:** a strictly positive matrix is `Matrix.IsPrimitive` (at power 1), tying the theorem into the pin's own vocabulary.
- **Proof route (built here, on the pin's fragments):** the pin's radius-attaining complex eigenvalue (`spectrum.exists_nnnorm_eq_spectralRadius`) gives a modulus vector; the triangle inequality yields a positive `y` with `rho • y ≤ A *ᵥ y`; any strictness would promote to `(rho + delta) • z ≤ A *ᵥ z` for a positive `z`, forcing `(rho+delta)^k ≤ ‖A^k‖` for all k (growth lemma `pow_norm_ge`), contradicting Gelfand's formula — so `y` is a positive eigenvector for `rho`, and `rho > 0`.

## Pin inventory (why this was a fill, not a strike)

Tree-wide, the pin's Perron–Frobenius content is: `Matrix.IsIrreducible` / `Matrix.IsPrimitive` definitions and their graph interface (`Mathlib/LinearAlgebra/Matrix/Irreducible/Defs.lean` — its tag line mentions perron-frobenius; no eigenvalue theorem is in it), the spectral-radius API (`spectrum.exists_nnnorm_eq_spectralRadius`, Gelfand's formula), charpoly/eigenvalue bridges, and Gershgorin (a bound only). No positive-eigenvector existence theorem and no PF maximality statement exists at v4.35.0-rc3. The fill consumed the fragments and built the missing theorem on them.

## Scope fence (on the module's face)

This retires the PF/Jentzsch prose at the **finite-dimensional** level: any finite positive transfer/Gibbs matrix at `LatticeTransferCompact` / `LatticeVacuumSimple` / `LatticeUniformGap` can now cite a theorem. The infinite-dimensional Jentzsch content stays with those modules, exactly as the module's face states; the invoking modules were not edited.

## Parent verification (from disk)

- Module `lean/ThetLogos/PerronFrobenius.lean` (NEW): canonical counter **strict=9, defs=1** (under the map's M estimate of 25–45 — the route reuses the pin's spectral-radius/Gelfand machinery instead of building it), zero attribute-prefixed declarations, zero "sorry"/`native_decide` tokens; no landed file edited.
- Parent module build green (8,976 jobs), independently reproduced.
- Parent axiom check: `perronFrobenius`, `isPrimitive_of_pos` each on exactly `[propext, Classical.choice, Quot.sound]`.

## Census

9,938 → **9,947 strict** / 10,016 → **10,025 attribute-inclusive** / 330 → **331 modules** (delta +9 strict, +1 module). README badge and body both updated at this landing and verified against the committed README.

## Backers since last landing

No change to the backer roll since the last landing.
