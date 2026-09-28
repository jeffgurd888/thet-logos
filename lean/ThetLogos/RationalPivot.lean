import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# ThetLogos.RationalPivot — exact rational nonsingularity certificate (interface, T5)

## What this file is

The 46→10 exotic elimination (`ThetLogos.CFKernelClassification`) rests on two
T4 numerical axioms: the exotic-basis decomposition and the invertibility of the
36×36 real pivot matrix (`pivot_matrix_invertible`, cond ≈ 5.25e2).  This file
specifies the *exact* upgrade path: a rational nonsingularity certificate
`M_Q.det ≠ 0` over ℚ.

## Two corrections to the naive plan (read before extending this file)

1. **Direct `decide` on `Matrix.det` at 36×36 is infeasible.**  Mathlib defines
   `Matrix.det` by the Leibniz formula — a sum over all 36! permutations — and
   `decide` evaluates that definition in the kernel.  No data change fixes this;
   the algorithm is the obstacle.

2. **No concrete pivot matrix exists in the repo.**  The Lean T4 axiom carries an
   *opaque* real matrix; the Python census (`attack4_corrected/`, `E36.npy`)
   holds *floating-point* SVD output.  An exact theorem over ℚ needs exact
   rational data, which the pipeline has not produced.

## The feasible exact strategy (implemented below)

Exhibit an explicit rational inverse `N_Q` with `M_Q * N_Q = 1`, checked by
`decide` (O(n³) kernel computation — feasible in principle), and conclude
`M_Q.det ≠ 0` from `det_mul` / `det_one`.  The checker lemma
`det_ne_zero_of_mul_eq_one` is PROVED here; the 2×2 demo shows the exact
`decide`-certificate pattern the pipeline must instantiate at 36×36 once
rational data exists.

## Pipeline TODO (data, not logic)

Export from the census: rational `M_Q` (rows = the 36 pivots of
`exoticPivotTable` in `ThetLogos.CFKernelClassification`, columns = a rational
exotic basis) and its exact rational inverse `N_Q`; then `decide (M_Q * N_Q = 1)`
discharges `hcert` in `rational_pivot_nonsingular` below.  Until that data
exists, the T4 real axiom remains the honest certificate.
-/

namespace ThetLogos

/-- Nonsingularity from an explicit inverse: if `M * N = 1` over ℚ then
    `M.det ≠ 0`.  This is the certificate *checker*; the pipeline supplies
    the concrete `(M_Q, N_Q)` pair. -/
theorem det_ne_zero_of_mul_eq_one {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℚ)
    (h : M * N = 1) : M.det ≠ 0 := by
  have hdet : M.det * N.det = 1 := by
    rw [← Matrix.det_mul, h, Matrix.det_one]
  intro hz
  rw [hz, zero_mul] at hdet
  exact zero_ne_one hdet

/-- 2×2 demo of the decide-certificate pattern: the inverse is checked
    entrywise, nonsingularity follows from the checker.  The 36×36 case is the
    same two lines once the rational data exists (there, `decide` on the
    O(n³) inverse check is the feasible route — unlike `decide` on `det`). -/
def demoM : Matrix (Fin 2) (Fin 2) ℚ := !![1, 2; 3, 4]
def demoN : Matrix (Fin 2) (Fin 2) ℚ := !![-2, 1; 3/2, -1/2]

/-- The demo inverse checks out (entrywise `decide` chokes on the `!!`
    notation's kernel unfolding, so this goes by `ext` + `fin_cases`). -/
theorem demo_cert : demoM * demoN = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [demoM, demoN, Matrix.mul_apply, Fin.sum_univ_two] <;>
    norm_num

/-- Hence the demo matrix is exactly nonsingular over ℚ. -/
theorem demo_det_ne_zero : demoM.det ≠ 0 :=
  det_ne_zero_of_mul_eq_one demoM demoN demo_cert

/-- The 36×36 rational pivot certificate, as an interface: given the rational
    pivot matrix `M_Q` and its explicit rational inverse `N_Q` (pipeline TODO),
    nonsingularity is exact over ℚ. -/
theorem rational_pivot_nonsingular
    (M_Q N_Q : Matrix (Fin 36) (Fin 36) ℚ)
    (hcert : M_Q * N_Q = 1) : M_Q.det ≠ 0 :=
  det_ne_zero_of_mul_eq_one M_Q N_Q hcert

end ThetLogos
