# FG-2b — The Friedrichs construction: the Hamiltonian exists — FULL

*Landed 2026-10-25. Module `ThetLogos.LatticeSliceFriedrichs`
(41 strict / 11 defs). Parent-verified: targeted build exit 0,
olean present, zero `sorry`/`admit`, `#print axioms` on the
packages returns exactly [propext, Classical.choice, Quot.sound].
Program census after landing: 5,409 strict / 178 counted modules.*

## Placement

Stage 2 completeness work (frontier-gate §2.2, FG-2 line). Fixed
volume, fixed lattice. **Not frontier progress; Items 3/4
untouched. NO CLAIM. Dials 0/4.**

## Step 0 — the FG-2a residue: OBSTRUCTED, named, bypassed

Density of the form domain inside (ker T̂_c)^⊥ via polynomial
truncations p_n(T̂_c) reduces, in every route found, to the mixed
form inequality ⟪x, T̂_c A_c^j x⟫.re ≥ 0 — defect-pairing
monotonicity, i.e. form-order **T̂_c² ≤ T̂_c**. The landed record
carries pure pairings only; no functional calculus for the bounded
operator `sliceHatCompleted` is assembled. Stopped per the
commission's rule, obstruction named — and NOT carried as a
hypothesis: the construction's carrier is instead
H′ := `sliceFormClosure`, the topological closure of the form
domain, where density holds by construction. FG-2a gives
H′ ⊆ (ker T̂_c)^⊥; the reverse inclusion is the recorded residue,
consumed by no clause of the package.

## Step 1 — what stands (T1)

At general (G, ρ), every real β, under exactly `SliceHPosOne`:

* The Riesz representative `sliceFriedrichsRep` of the form
  (via `InnerProductSpace.toDual`), with specification and
  uniqueness.
* The resolvent `sliceFriedrichsResolventLin` (λ = 1 seat):
  linear, symmetric, ‖R f‖ ≤ ‖f‖, in CLM form, injective, range
  characterized.
* The operator `sliceHamOperator` on D(Ĥ) = range R, Ĥ u = f − u:
  symmetric; ⟪Ĥu, u⟫ = the form value, hence Ĥ ≥ 0; **the form
  identity** `sliceFormB û v = ⟪Ĥu, v⟫` for u ∈ D(Ĥ),
  v ∈ form domain (Kato's first representation theorem, at this
  seat).
* **Ĥ + 1 surjective onto H′** — self-adjointness in the
  resolvent sense, the honest form available for an operator
  carried as a LinearMap on its domain; no bounded-operator
  typeclass self-adjointness is claimed.
* **Vacuum:** Ω ∈ D(Ĥ) and Ĥ Ω = 0.

Packages: `sliceFriedrichs_package` (10 clauses);
`sliceFriedrichs_circle_package` (U(1) seat, β ≥ 0,
hypothesis-free); β = 0 package (carrier = whole space, form ≡ 0,
R = id, Ĥ = 0).

## What this is not

H′ = (ker T̂_c)^⊥ is not asserted; `exp(−Ĥ) = T̂_c` is FG-2c and
is not asserted; no spectral or gap statement for Ĥ is made. The
Hamiltonian now exists as a machine-checked object; its
exponential has not yet been identified with the transfer
operator. FG-2c opens with a gate paper: its routes (Hille–Yosida
from the resolvent family vs a functional calculus for T̂_c vs a
form-uniqueness argument) hit the same named missing ingredient
as step 0, and the routes must be priced before a builder is
commissioned.
