import Mathlib.Tactic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import ThetLogos.Q7C4R4Assembly
import ThetLogos.ThermalZ4Ladder

/-!
# ThetLogos.Q7C4R4Spectrum — the spectrum of the instantiated Q⁷C⁴R⁴
product Dirac, computed exactly and certified (Q7CR-2)

**Status: T1 certification brick at named, labeled choices.
NO CLAIM. Dials 0/4. No measured number is claimed by this line.**

Governing scoping: `scoping-q7c4r4-gauntlet-2026-10-30.md` §3
(Q7CR-2, tests gauntlet Item 4), pack `pack-q7cr-2.md`. Gates:
Q7CR-0/1a/1b landed (`Q7C4R4Post`, `Q7C4R4Realify`,
`Q7C4R4Assembly`: `diracQ7C4R4` and the D² identity
`diracQ7C4R4_sq` in lifted form). Python exact side: BR1-012
(`routeb-general-scratch/q7cr2-spectrum.py`, run record
`q7cr2-run.txt`; fractions only, no floats).

## The instantiated factor operators — choices NAMED, with labels

All three factor operators are diagonal in their site bases, with
gradings that are permutations pairing each site with the site
carrying the negated diagonal entry (the diagonal sign at a fixed
site is zero). This paired shape is what makes a grading
anticommute with a diagonal operator at all.

- **Q⁷ factor — CHOSEN diagonal.** `a₇ : Fin 7 → ℝ`,
  `a₇ = (3, -3, 2, -2, 1, -1, 0)`; grading the permutation
  `(0 1)(2 3)(4 5)`, fixing `6`. Label: **CHOSEN** (named entries).
  The corpus's owned `Fin 7` data, `clockObs`
  (`MeasuredClockSpectrum`, Tier T4 measured ratios), is a list of
  frequency *ratios*, not operator entries, and its all-positive
  entries admit no pairing of the stated shape, so it is not used
  as a diagonal here; any spectrum built from it would be a
  separate labeled step carrying the D1 fence.
- **C⁴ factor — ladder-generator analog (T2 input, centering
  CHOSEN).** `d₄ k = z4Energy k - 3/8`, where `z4Energy`
  (`ThermalZ4Ladder`, Tier T2 chosen ladder input, `E_k = k/4`) is
  the diagonal of the landed ladder generator `z4Generator`
  (`ThermalZ4KMS`); `3/8` is the ladder's mean, so
  `d₄ = (-3/8, -1/8, 1/8, 3/8)`, symmetric under the grading
  permutation `k ↦ 3 - k`. The cyclic shift-Dirac of the 4-cycle
  was not chosen: its square is not site-diagonal (it is diagonal
  in the pair basis instead), and this brick certifies the
  spectrum in the site basis.
- **R⁴ factor — CHOSEN diagonal.** `r_R = (0, 2, -2, 0)` on the
  Minkowski seat; grading the permutation swapping sites `1, 2`
  (both spatial, so the permutation is self-adjoint for
  `minkowskiInner`), fixing `0, 3`, where the diagonal is `0`.

## What is certified

An explicit real eigenbasis of the composite (`basisComp`, §5:
realified site bases tensored) diagonalizes
`(diracQ7C4R4 factorQ7 factorC4 factorR)²`: every basis vector is
an eigenvector whose eigenvalue is the sumset value
`s₇ + s₄ + s_R` of the factor-square eigenvalue functions
(**required names** `s₇ : Fin 14 → ℝ`, `s₄ : Fin 8 → ℝ`,
`s_R : Fin 4 → ℝ`, §4 — consumed by RES-4). The eigenvalue
multiset is therefore the sumset multiset with product
multiplicities (§6), with anchors: total count `448`, spectral
trace `M 1 = 2723` (the sum of the D² eigenvalues, i.e. the trace
of D² against this eigenbasis), second moment
`M 2 = 1518111 / 64` (the sum of their squares, i.e. the trace of
D⁴), smallest eigenvalue `1 / 64`, largest `841 / 64`. The
eigenvalues of `D` itself are `±√` of these (D is self-adjoint,
Q7CR-1b); the endpoints are rational squares, `√(1/64) = 1/8`,
`√(841/64) = 29/8`.

## Kill K-Q7CR-2 — evaluated on the face: does NOT fire

The spectrum is **not forced**. §7 exhibits a second admissible
Q⁷ package (`a₇' = (4, -4, 2, -2, 1, -1, 0)`, same grading) whose
spectral trace is `3619 ≠ 2723`; the spectrum is an explicit
function of the factor data, and changing one diagonal pair
changes it. Dependence is shown in the landed form, so the
evaluation is discharged: Item 4's spectrum does work in this
form. (A spectrum that merely disappoints would not be a kill;
this one is not a tautology either.)

## Fences

- Bounded-commutator vacuity caveat: in finite dimension that
  criterion is vacuous; the testable content here is the spectrum.
- No measured number is claimed by this line; any numerical
  coincidence in the spectrum is not reported as a result.
- No entropy language. NO CLAIM; Dial 1 unmoved.
-/

namespace ThetLogos

open TensorProduct

/-! ## §1. Diagonal and permutation operators on a complex factor -/

/-- The diagonal operator with real entries `d` on the realified
factor `Fin n → ℂ`, as an ℝ-linear map: `(diagOpC d x) k =
(d k : ℂ) * x k`. -/
def diagOpC {n : ℕ} (d : Fin n → ℝ) : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) where
  toFun := fun x k => (d k : ℂ) * x k
  map_add' := fun x y => by
    funext k
    simp [mul_add]
  map_smul' := fun r x => by
    funext k
    show (d k : ℂ) * ((r : ℂ) * x k) = (r : ℂ) * ((d k : ℂ) * x k)
    ring

/-- Pointwise formula for `diagOpC`. -/
theorem diagOpC_apply {n : ℕ} (d : Fin n → ℝ) (x : Fin n → ℂ) (k : Fin n) :
    diagOpC d x k = (d k : ℂ) * x k :=
  rfl

/-- The permutation operator of `p` on the realified factor, as an
ℝ-linear map: `(permOpC p x) k = x (p k)`. -/
def permOpC {n : ℕ} (p : Fin n → Fin n) : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) where
  toFun := fun x k => x (p k)
  map_add' := fun x y => rfl
  map_smul' := fun r x => by
    funext k
    simp [Pi.smul_apply, Complex.real_smul]

/-- Pointwise formula for `permOpC`. -/
theorem permOpC_apply {n : ℕ} (p : Fin n → Fin n) (x : Fin n → ℂ) (k : Fin n) :
    permOpC p x k = x (p k) :=
  rfl

/-- A diagonal operator with real entries is self-adjoint for the
registered real pairing `factorPair`. -/
theorem diagOpC_selfAdjoint {n : ℕ} (d : Fin n → ℝ) :
    RealSelfAdjoint (diagOpC d) := by
  intro x y
  show (cplxPair n (diagOpC d x) y).re = (cplxPair n x (diagOpC d y)).re
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro k _
  show (d k : ℂ) * x k * star (y k) = x k * star ((d k : ℂ) * y k)
  have hstar : star ((d k : ℂ)) = (d k : ℂ) := by simp
  rw [star_mul, hstar]
  ac_rfl

/-- A permutation operator of an involutive permutation is
self-adjoint for the registered real pairing `factorPair`. -/
theorem permOpC_selfAdjoint {n : ℕ} (p : Fin n → Fin n)
    (hinv : ∀ k, p (p k) = k) : RealSelfAdjoint (permOpC p) := by
  intro x y
  show (cplxPair n (permOpC p x) y).re = (cplxPair n x (permOpC p y)).re
  apply congrArg Complex.re
  show (∑ k, x (p k) * star (y k)) = ∑ k, x k * star (y (p k))
  have hbij : Function.Bijective p :=
    Function.Involutive.bijective (fun k => hinv k)
  have h := hbij.sum_comp (fun j => x j * star (y (p j)))
  simp only [hinv] at h
  exact h

/-- **The diagonal factor-package constructor.** A diagonal
operator with entries `d` and the permutation grading of an
involutive `p` with `d (p k) = - d k` form a `FactorOp n`
package: involution and anticommutation are the pairing
hypotheses, self-adjointness is §1's two lemmas. -/
def diagFactorOp {n : ℕ} (d : Fin n → ℝ) (p : Fin n → Fin n)
    (hanti : ∀ k, d (p k) = - d k) (hinv : ∀ k, p (p k) = k) :
    FactorOp n where
  D := diagOpC d
  γ := permOpC p
  γ_invol := by
    apply LinearMap.ext
    intro x
    funext k
    simp only [LinearMap.comp_apply, permOpC_apply, Module.End.one_apply]
    rw [hinv]
  γ_selfadj := permOpC_selfAdjoint p hinv
  D_selfadj := diagOpC_selfAdjoint d
  anticomm := by
    apply LinearMap.ext
    intro x
    funext k
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Pi.add_apply,
      diagOpC_apply, permOpC_apply, LinearMap.zero_apply, Pi.zero_apply]
    have hcast : ((d (p k) : ℂ)) = -((d k : ℂ)) := by
      rw [hanti k]
      simp
    rw [hcast]
    ring

/-- The square of a diagonal operator is the diagonal of the
squares, pointwise. -/
theorem diagOpC_sq_apply {n : ℕ} (d : Fin n → ℝ) (x : Fin n → ℂ)
    (k : Fin n) : ((diagOpC d) ^ 2) x k = ((d k) ^ 2 : ℂ) * x k := by
  rw [pow_two]
  show (d k : ℂ) * ((d k : ℂ) * x k) = ((d k) ^ 2 : ℂ) * x k
  ring

/-! ## §2. Diagonal and permutation operators on the R⁴ factor -/

/-- The diagonal operator with entries `r` on the Minkowski seat,
as an ℝ-linear map. -/
def diagOpR (r : Fin 4 → ℝ) : Minkowski →ₗ[ℝ] Minkowski where
  toFun := fun x k => r k * x k
  map_add' := fun x y => by
    funext k
    simp [mul_add]
  map_smul' := fun s x => by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_left_comm _ _ _

/-- Pointwise formula for `diagOpR`. -/
theorem diagOpR_apply (r : Fin 4 → ℝ) (x : Minkowski) (k : Fin 4) :
    diagOpR r x k = r k * x k :=
  rfl

/-- The permutation operator of `p` on the Minkowski seat. -/
def permOpR (p : Fin 4 → Fin 4) : Minkowski →ₗ[ℝ] Minkowski where
  toFun := fun x k => x (p k)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/-- Pointwise formula for `permOpR`. -/
theorem permOpR_apply (p : Fin 4 → Fin 4) (x : Minkowski) (k : Fin 4) :
    permOpR p x k = x (p k) :=
  rfl

/-- A diagonal operator on the Minkowski seat is self-adjoint for
`minkowskiInner`. -/
theorem diagOpR_selfAdjoint (r : Fin 4 → ℝ) : MinkSelfAdjoint (diagOpR r) := by
  intro x y
  show r 0 * x 0 * y 0 - r 1 * x 1 * y 1 - r 2 * x 2 * y 2 - r 3 * x 3 * y 3
      = x 0 * (r 0 * y 0) - x 1 * (r 1 * y 1) - x 2 * (r 2 * y 2)
        - x 3 * (r 3 * y 3)
  ring

/-- The square of a diagonal operator on the Minkowski seat is the
diagonal of the squares, pointwise. -/
theorem diagOpR_sq_apply (r : Fin 4 → ℝ) (x : Minkowski) (k : Fin 4) :
    ((diagOpR r) ^ 2) x k = (r k) ^ 2 * x k := by
  rw [pow_two]
  show r k * (r k * x k) = (r k) ^ 2 * x k
  ring

/-! ## §3. The instantiated factor packages (choices, labeled) -/

/-- **The Q⁷ diagonal (CHOSEN, named entries):**
`a₇ = (3, -3, 2, -2, 1, -1, 0)`. -/
def a₇ : Fin 7 → ℝ := ![3, -3, 2, -2, 1, -1, 0]

/-- **The Q⁷ grading permutation (CHOSEN):** `(0 1)(2 3)(4 5)`,
fixing `6` — it pairs each site with the site carrying the negated
diagonal entry. -/
def p₇ : Fin 7 → Fin 7 := ![1, 0, 3, 2, 5, 4, 6]

/-- The Q⁷ pairing law: `a₇ (p₇ k) = - a₇ k`. -/
theorem a₇_anti : ∀ k, a₇ (p₇ k) = - a₇ k := by
  intro k
  fin_cases k <;> simp [a₇, p₇]

/-- The Q⁷ grading permutation is involutive. -/
theorem p₇_inv : ∀ k, p₇ (p₇ k) = k := by
  intro k
  fin_cases k <;> simp [p₇]

/-- **The instantiated Q⁷ factor package** (CHOSEN diagonal,
paired permutation grading), built by the §1 constructor. -/
def factorQ7 : FactorOp 7 := diagFactorOp a₇ p₇ a₇_anti p₇_inv

/-- The Q⁷ package's operator is the stated diagonal. -/
theorem factorQ7_D : factorQ7.D = diagOpC a₇ := rfl

/-- The Q⁷ factor square, pointwise: `D₇²` is the diagonal of the
squared entries. -/
theorem factorQ7_D_sq_apply (x : Fin 7 → ℂ) (k : Fin 7) :
    (factorQ7.D ^ 2) x k = ((a₇ k) ^ 2 : ℂ) * x k :=
  diagOpC_sq_apply a₇ x k

/-- **The C⁴ diagonal (ladder-generator analog):**
`d₄ k = z4Energy k - 3/8`, the landed Z4 ladder generator's
diagonal (`z4Energy`, Tier T2) centered by its mean `3/8`
(CHOSEN centering), so `d₄ = (-3/8, -1/8, 1/8, 3/8)`. -/
noncomputable def d₄ : Fin 4 → ℝ := fun k => z4Energy k - 3 / 8

/-- **The C⁴ grading permutation (CHOSEN):** the reversal
`k ↦ 3 - k`, pairing each ladder rung with the rung carrying the
negated centered entry. -/
def p₄ : Fin 4 → Fin 4 := ![3, 2, 1, 0]

/-- The C⁴ pairing law: `d₄ (p₄ k) = - d₄ k`. -/
theorem d₄_anti : ∀ k, d₄ (p₄ k) = - d₄ k := by
  intro k
  fin_cases k <;> norm_num [d₄, p₄, z4Energy]

/-- The C⁴ grading permutation is involutive. -/
theorem p₄_inv : ∀ k, p₄ (p₄ k) = k := by
  intro k
  fin_cases k <;> simp [p₄]

/-- **The instantiated C⁴ factor package** (centered ladder
diagonal, reversal grading), built by the §1 constructor. -/
noncomputable def factorC4 : FactorOp 4 := diagFactorOp d₄ p₄ d₄_anti p₄_inv

/-- The C⁴ package's operator is the stated diagonal. -/
theorem factorC4_D : factorC4.D = diagOpC d₄ := rfl

/-- The C⁴ factor square, pointwise. -/
theorem factorC4_D_sq_apply (x : Fin 4 → ℂ) (k : Fin 4) :
    (factorC4.D ^ 2) x k = ((d₄ k) ^ 2 : ℂ) * x k :=
  diagOpC_sq_apply d₄ x k

/-- **The R⁴ diagonal (CHOSEN, named entries):**
`r_R = (0, 2, -2, 0)` on the Minkowski seat. -/
def r_R : Fin 4 → ℝ := ![0, 2, -2, 0]

/-- **The R⁴ grading permutation (CHOSEN):** swaps sites `1, 2`
(both spatial, so Minkowski-self-adjoint), fixing `0, 3`, where
the diagonal is `0`. -/
def p_R : Fin 4 → Fin 4 := ![0, 2, 1, 3]

/-- **The instantiated R⁴ factor package** (CHOSEN diagonal,
spatial-swap grading). -/
def factorR : FactorOpR where
  D := diagOpR r_R
  γ := permOpR p_R
  γ_invol := by
    apply LinearMap.ext
    intro x
    funext k
    fin_cases k <;> simp [LinearMap.comp_apply, permOpR_apply, p_R,
      Module.End.one_apply]
  γ_selfadj := by
    intro x y
    show x 0 * y 0 - x 2 * y 1 - x 1 * y 2 - x 3 * y 3
        = x 0 * y 0 - x 1 * y 2 - x 2 * y 1 - x 3 * y 3
    ring
  D_selfadj := diagOpR_selfAdjoint r_R
  anticomm := by
    apply LinearMap.ext
    intro x
    funext k
    fin_cases k <;> simp [LinearMap.add_apply, LinearMap.comp_apply,
      diagOpR_apply, permOpR_apply, r_R, p_R]

/-- The R⁴ package's operator is the stated diagonal. -/
theorem factorR_D : factorR.D = diagOpR r_R := rfl

/-- The R⁴ factor square, pointwise. -/
theorem factorR_D_sq_apply (x : Minkowski) (k : Fin 4) :
    (factorR.D ^ 2) x k = (r_R k) ^ 2 * x k :=
  diagOpR_sq_apply r_R x k

/-! ## §4. The factor-square eigenvalue functions (REQUIRED NAMES)

`s₇`, `s₄`, `s_R` give the eigenvalues of the three factor squares
in the realified dimensions `14 / 8 / 4`: each complex site
contributes its squared diagonal entry twice (real and imaginary
parts), indexed through `finProdFinEquiv (site, part)`. These are
the names RES-4 consumes. -/

/-- **The Q⁷ factor-square eigenvalues** (realified, `Fin 14`):
`s₇ (site, part) = a₇ site ^ 2`. -/
def s₇ : Fin 14 → ℝ :=
  fun i => a₇ ((finProdFinEquiv (m := 7) (n := 2)).symm i).1 ^ 2

/-- **The C⁴ factor-square eigenvalues** (realified, `Fin 8`):
`s₄ (site, part) = d₄ site ^ 2`. -/
noncomputable def s₄ : Fin 8 → ℝ :=
  fun i => d₄ ((finProdFinEquiv (m := 4) (n := 2)).symm i).1 ^ 2

/-- **The R⁴ factor-square eigenvalues** (`Fin 4`):
`s_R m = r_R m ^ 2`. -/
def s_R : Fin 4 → ℝ := fun m => r_R m ^ 2

/-- `s₇` on a realified index pair is the site square. -/
theorem s₇_pair (k : Fin 7) (b : Fin 2) :
    s₇ ((finProdFinEquiv (m := 7) (n := 2)) (k, b)) = a₇ k ^ 2 := by
  simp [s₇]

/-- `s₄` on a realified index pair is the site square. -/
theorem s₄_pair (k : Fin 4) (b : Fin 2) :
    s₄ ((finProdFinEquiv (m := 4) (n := 2)) (k, b)) = d₄ k ^ 2 := by
  simp [s₄]

/-- The Q⁷ site squares sum to `28`. -/
theorem a₇_sum_sq : ∑ k, a₇ k ^ 2 = 28 := by
  norm_num [Fin.sum_univ_seven, a₇]

/-- The Q⁷ fourth powers of the entries sum to `196`. -/
theorem a₇_sum_sq_sq : ∑ k, (a₇ k ^ 2) ^ 2 = 196 := by
  norm_num [Fin.sum_univ_seven, a₇]

/-- The C⁴ site squares sum to `5 / 16`. -/
theorem d₄_sum_sq : ∑ k, d₄ k ^ 2 = 5 / 16 := by
  norm_num [Fin.sum_univ_four, d₄, z4Energy]

/-- The C⁴ fourth powers of the entries sum to `41 / 1024`. -/
theorem d₄_sum_sq_sq : ∑ k, (d₄ k ^ 2) ^ 2 = 41 / 1024 := by
  norm_num [Fin.sum_univ_four, d₄, z4Energy]

/-- **Sum of `s₇`: `56`** (each site square counted twice). -/
theorem sum_s₇ : ∑ i, s₇ i = 56 := by
  have h := (finProdFinEquiv (m := 7) (n := 2)).sum_comp s₇
  rw [← h, Fintype.sum_prod_type]
  simp only [s₇_pair, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← Finset.mul_sum, a₇_sum_sq]
  norm_num

/-- **Sum of `(s₇)²`: `392`.** -/
theorem sum_s₇_sq : ∑ i, (s₇ i) ^ 2 = 392 := by
  have h := (finProdFinEquiv (m := 7) (n := 2)).sum_comp (fun i => (s₇ i) ^ 2)
  rw [← h, Fintype.sum_prod_type]
  simp only [s₇_pair, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← Finset.mul_sum, a₇_sum_sq_sq]
  norm_num

/-- **Sum of `s₄`: `5 / 8`.** -/
theorem sum_s₄ : ∑ i, s₄ i = 5 / 8 := by
  have h := (finProdFinEquiv (m := 4) (n := 2)).sum_comp s₄
  rw [← h, Fintype.sum_prod_type]
  simp only [s₄_pair, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← Finset.mul_sum, d₄_sum_sq]
  norm_num

/-- **Sum of `(s₄)²`: `41 / 512`.** -/
theorem sum_s₄_sq : ∑ i, (s₄ i) ^ 2 = 41 / 512 := by
  have h := (finProdFinEquiv (m := 4) (n := 2)).sum_comp (fun i => (s₄ i) ^ 2)
  rw [← h, Fintype.sum_prod_type]
  simp only [s₄_pair, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← Finset.mul_sum, d₄_sum_sq_sq]
  norm_num

/-- **Sum of `s_R`: `8`.** -/
theorem sum_s_R : ∑ m, s_R m = 8 := by
  norm_num [Fin.sum_univ_four, s_R, r_R]

/-- **Sum of `(s_R)²`: `32`.** -/
theorem sum_s_R_sq : ∑ m, (s_R m) ^ 2 = 32 := by
  norm_num [Fin.sum_univ_four, s_R, r_R]

/-- Every `s₇` value is nonnegative (it is a square). -/
theorem s₇_nonneg (i : Fin 14) : 0 ≤ s₇ i :=
  sq_nonneg _

/-- Every `s₇` value is at most `9`. -/
theorem s₇_le (i : Fin 14) : s₇ i ≤ 9 := by
  have h : ∀ k : Fin 7, a₇ k ^ 2 ≤ 9 := by
    intro k
    fin_cases k <;> norm_num [a₇]
  exact h _

/-- Every `s₄` value is at least `1 / 64`. -/
theorem s₄_ge (i : Fin 8) : 1 / 64 ≤ s₄ i := by
  have h : ∀ k : Fin 4, 1 / 64 ≤ d₄ k ^ 2 := by
    intro k
    fin_cases k <;> norm_num [d₄, z4Energy]
  exact h _

/-- Every `s₄` value is at most `9 / 64`. -/
theorem s₄_le (i : Fin 8) : s₄ i ≤ 9 / 64 := by
  have h : ∀ k : Fin 4, d₄ k ^ 2 ≤ 9 / 64 := by
    intro k
    fin_cases k <;> norm_num [d₄, z4Energy]
  exact h _

/-- Every `s_R` value is nonnegative (it is a square). -/
theorem s_R_nonneg (m : Fin 4) : 0 ≤ s_R m :=
  sq_nonneg _

/-- Every `s_R` value is at most `4`. -/
theorem s_R_le (m : Fin 4) : s_R m ≤ 4 := by
  have h : ∀ k : Fin 4, r_R k ^ 2 ≤ 4 := by
    intro k
    fin_cases k <;> norm_num [r_R]
  exact h m

/-! ## §5. The real eigenbasis of the composite

The realified factor `Fin n → ℂ` has the real basis of site
vectors `e_{k,0} = δ_k` and `e_{k,1} = i δ_k`, indexed by
`Fin n × Fin 2`, transported along the real/imaginary-parts
equivalence. The factor squares are site-diagonal, so these are
eigenvectors of the factor squares; tensored, they are an
eigenbasis of the composite `D²`. -/

/-- Real/imaginary parts: the realified factor `Fin n → ℂ` as
real functions on `Fin n × Fin 2`. -/
noncomputable def realBasisEquiv (n : ℕ) :
    (Fin n → ℂ) ≃ₗ[ℝ] ((Fin n × Fin 2) → ℝ) where
  toFun := fun x kb => if kb.2 = 0 then (x kb.1).re else (x kb.1).im
  invFun := fun f k => ⟨f (k, 0), f (k, 1)⟩
  left_inv := fun x => by
    funext k
    apply Complex.ext
    · show (if (0 : Fin 2) = 0 then (x k).re else (x k).im) = (x k).re
      rw [if_pos rfl]
    · show (if (1 : Fin 2) = 0 then (x k).re else (x k).im) = (x k).im
      rw [if_neg (by decide)]
  right_inv := fun f => by
    funext ⟨k, b⟩
    fin_cases b
    · show (if (0 : Fin 2) = 0 then (⟨f (k, 0), f (k, 1)⟩ : ℂ).re
        else (⟨f (k, 0), f (k, 1)⟩ : ℂ).im) = f (k, 0)
      rw [if_pos rfl]
    · show (if (1 : Fin 2) = 0 then (⟨f (k, 0), f (k, 1)⟩ : ℂ).re
        else (⟨f (k, 0), f (k, 1)⟩ : ℂ).im) = f (k, 1)
      rw [if_neg (by decide)]
  map_add' := fun x y => by
    funext ⟨k, b⟩
    by_cases hb : b = 0 <;>
      simp [hb, Pi.add_apply, Complex.add_re, Complex.add_im]
  map_smul' := fun r x => by
    funext ⟨k, b⟩
    by_cases hb : b = 0 <;>
      simp [hb, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
        Complex.mul_re, Complex.mul_im]

/-- **The real site basis of a realified factor**: `basisC n (k, 0)`
is the site vector `δ_k`, `basisC n (k, 1)` is `i δ_k`. -/
noncomputable def basisC (n : ℕ) : Module.Basis (Fin n × Fin 2) ℝ (Fin n → ℂ) :=
  (Pi.basisFun ℝ (Fin n × Fin 2)).map (realBasisEquiv n).symm

/-- A vector is reassembled from its real and imaginary parts. -/
theorem eq_mk_re_im (n : ℕ) (x : Fin n → ℂ) (j : Fin n) :
    x j = ⟨(realBasisEquiv n x) (j, 0), (realBasisEquiv n x) (j, 1)⟩ := by
  have h := congrFun ((realBasisEquiv n).toEquiv.left_inv x) j
  exact h.symm

/-- The real site basis, evaluated: `basisC n (k, b) j` is `1`
(resp. `i`) at `j = k` for `b = 0` (resp. `b = 1`), else `0`. -/
theorem basisC_apply (n : ℕ) (k : Fin n) (b : Fin 2) (j : Fin n) :
    basisC n (k, b) j
      = if j = k then (if b = 0 then 1 else Complex.I) else 0 := by
  have himg : (realBasisEquiv n) (basisC n (k, b)) = Pi.single (k, b) 1 := by
    unfold basisC
    rw [Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply]
  have h2 : basisC n (k, b) j
      = ⟨(realBasisEquiv n (basisC n (k, b))) (j, 0),
          (realBasisEquiv n (basisC n (k, b))) (j, 1)⟩ :=
    eq_mk_re_im n _ j
  rw [h2, himg]
  by_cases hj : j = k
  · subst hj
    fin_cases b <;>
      simp [Pi.single_apply, Prod.mk.injEq, Fin.mk.injEq, Complex.ext_iff]
  · have hne : ∀ c : Fin 2, (j, c) ≠ (k, b) :=
      fun c h => hj (congrArg Prod.fst h)
    simp [Pi.single_apply, hne, hj, Complex.ext_iff]

/-- The Q⁷ real site basis vectors are eigenvectors of `D₇²`, with
eigenvalue `a₇ k ^ 2`. -/
theorem factorQ7_basisC_eigen (k : Fin 7) (b : Fin 2) :
    (factorQ7.D ^ 2) (basisC 7 (k, b)) = (a₇ k ^ 2) • basisC 7 (k, b) := by
  funext j
  rw [factorQ7_D_sq_apply]
  by_cases hj : j = k
  · subst hj
    rw [Pi.smul_apply, Complex.real_smul, basisC_apply]
    simp only [if_pos rfl]
    congr 1
    push_cast
    ring
  · simp [basisC_apply, hj, Pi.smul_apply]

/-- The C⁴ real site basis vectors are eigenvectors of `D₄²`, with
eigenvalue `d₄ k ^ 2`. -/
theorem factorC4_basisC_eigen (k : Fin 4) (b : Fin 2) :
    (factorC4.D ^ 2) (basisC 4 (k, b)) = (d₄ k ^ 2) • basisC 4 (k, b) := by
  funext j
  rw [factorC4_D_sq_apply]
  by_cases hj : j = k
  · subst hj
    rw [Pi.smul_apply, Complex.real_smul, basisC_apply]
    simp only [if_pos rfl]
    congr 1
    push_cast
    ring
  · simp [basisC_apply, hj, Pi.smul_apply]

/-- The R⁴ site basis vectors are eigenvectors of `D_R²`, with
eigenvalue `r_R m ^ 2`. -/
theorem factorR_basis_eigen (m : Fin 4) :
    (factorR.D ^ 2) ((Pi.basisFun ℝ (Fin 4)) m)
      = (r_R m ^ 2) • (Pi.basisFun ℝ (Fin 4)) m := by
  funext j
  rw [factorR_D_sq_apply, Pi.smul_apply, smul_eq_mul, Pi.basisFun_apply,
    Pi.single_apply]
  by_cases hj : j = m <;> simp [hj]

/-- The composite index type: realified site indices of the three
factors, `((Fin 7 × Fin 2) × (Fin 4 × Fin 2)) × Fin 4`, of
cardinality `14 · 8 · 4 = 448`. -/
abbrev compIndex : Type := ((Fin 7 × Fin 2) × (Fin 4 × Fin 2)) × Fin 4

/-- **The composite real basis**: the tensor product of the three
factor bases, in the registered association. -/
noncomputable def basisComp : Module.Basis compIndex ℝ q7c4r4Composite :=
  Module.Basis.tensorProduct
    (Module.Basis.tensorProduct (basisC 7) (basisC 4)) (Pi.basisFun ℝ (Fin 4))

/-- **The eigenbasis theorem.** Every composite basis vector is an
eigenvector of the instantiated product Dirac squared, with
eigenvalue the sumset value `a₇² + d₄² + r_R²` at its index —
proved from the landed D² identity `diracQ7C4R4_sq` and the
factor eigen lemmas, not by a `448 × 448` computation. -/
theorem dirac_sq_basisComp (k₇ : Fin 7) (b₇ : Fin 2) (k₄ : Fin 4)
    (b₄ : Fin 2) (m : Fin 4) :
    ((diracQ7C4R4 factorQ7 factorC4 factorR) ^ 2)
        (basisComp (((k₇, b₇), (k₄, b₄)), m))
      = (a₇ k₇ ^ 2 + d₄ k₄ ^ 2 + r_R m ^ 2)
        • basisComp (((k₇, b₇), (k₄, b₄)), m) := by
  have hb : basisComp (((k₇, b₇), (k₄, b₄)), m)
      = ((basisC 7 (k₇, b₇) ⊗ₜ[ℝ] basisC 4 (k₄, b₄))
          ⊗ₜ[ℝ] (Pi.basisFun ℝ (Fin 4)) m) := by
    show Module.Basis.tensorProduct
        (Module.Basis.tensorProduct (basisC 7) (basisC 4))
        (Pi.basisFun ℝ (Fin 4)) (((k₇, b₇), (k₄, b₄)), m) = _
    rw [Module.Basis.tensorProduct_apply, Module.Basis.tensorProduct_apply]
  rw [hb, diracQ7C4R4_sq]
  simp only [LinearMap.add_apply, opTensorQ_tmul, Module.End.one_apply,
    factorQ7_basisC_eigen, factorC4_basisC_eigen, factorR_basis_eigen]
  simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  rw [← add_smul, ← add_smul]

/-! ## §6. The sumset spectrum: multiset, moments, endpoints

The composite eigenvalue function is the sumset
`s₇ + s₄ + s_R` over the composite index. Its multiset is the
spectrum of `D²` (the eigenbasis of §5 diagonalizes `D²` with
exactly these eigenvalues), and its power sums are the spectral
moments `M 1` (the trace of `D²`) and `M 2` (the trace of `D⁴`). -/

/-- The Q⁷ factor-square eigenvalues, composed with the
realification index equiv (the form the composite consumes). -/
def s₇c : Fin 7 × Fin 2 → ℝ :=
  fun a => s₇ ((finProdFinEquiv (m := 7) (n := 2)) a)

/-- The C⁴ factor-square eigenvalues, composed with the
realification index equiv. -/
noncomputable def s₄c : Fin 4 × Fin 2 → ℝ :=
  fun a => s₄ ((finProdFinEquiv (m := 4) (n := 2)) a)

/-- `s₇c` at a realified index is the site square. -/
theorem s₇c_apply (a : Fin 7 × Fin 2) : s₇c a = a₇ a.1 ^ 2 := by
  simp [s₇c, s₇]

/-- `s₄c` at a realified index is the site square. -/
theorem s₄c_apply (a : Fin 4 × Fin 2) : s₄c a = d₄ a.1 ^ 2 := by
  simp [s₄c, s₄]

/-- The composed Q⁷ eigenvalues sum to the `s₇` sum. -/
theorem sum_s₇c : ∑ a, s₇c a = ∑ i, s₇ i :=
  (finProdFinEquiv (m := 7) (n := 2)).sum_comp s₇

/-- The composed C⁴ eigenvalues sum to the `s₄` sum. -/
theorem sum_s₄c : ∑ a, s₄c a = ∑ i, s₄ i :=
  (finProdFinEquiv (m := 4) (n := 2)).sum_comp s₄

/-- The composed Q⁷ eigenvalues sum of squares. -/
theorem sum_s₇c_sq : ∑ a, (s₇c a) ^ 2 = ∑ i, (s₇ i) ^ 2 :=
  (finProdFinEquiv (m := 7) (n := 2)).sum_comp (fun i => (s₇ i) ^ 2)

/-- The composed C⁴ eigenvalues sum of squares. -/
theorem sum_s₄c_sq : ∑ a, (s₄c a) ^ 2 = ∑ i, (s₄ i) ^ 2 :=
  (finProdFinEquiv (m := 4) (n := 2)).sum_comp (fun i => (s₄ i) ^ 2)

/-- Bounds transport: `s₇c` is nonnegative. -/
theorem s₇c_nonneg (a : Fin 7 × Fin 2) : 0 ≤ s₇c a :=
  s₇_nonneg _

/-- Bounds transport: `s₇c` is at most `9`. -/
theorem s₇c_le (a : Fin 7 × Fin 2) : s₇c a ≤ 9 :=
  s₇_le _

/-- Bounds transport: `s₄c` is at least `1 / 64`. -/
theorem s₄c_ge (a : Fin 4 × Fin 2) : 1 / 64 ≤ s₄c a :=
  s₄_ge _

/-- Bounds transport: `s₄c` is at most `9 / 64`. -/
theorem s₄c_le (a : Fin 4 × Fin 2) : s₄c a ≤ 9 / 64 :=
  s₄_le _

/-- **The composite eigenvalue function**: the sumset value at a
composite index. -/
noncomputable def eigComp (t : compIndex) : ℝ := s₇c t.1.1 + s₄c t.1.2 + s_R t.2

/-- The composite eigenvalue function, in factor entries. -/
theorem eigComp_eq (t : compIndex) :
    eigComp t = a₇ t.1.1.1 ^ 2 + d₄ t.1.2.1 ^ 2 + r_R t.2 ^ 2 := by
  show s₇c t.1.1 + s₄c t.1.2 + r_R t.2 ^ 2
      = a₇ t.1.1.1 ^ 2 + d₄ t.1.2.1 ^ 2 + r_R t.2 ^ 2
  rw [s₇c_apply, s₄c_apply]

/-- **Eigenvalue determination, restated**: every composite basis
vector is an eigenvector of the instantiated `D²` with eigenvalue
`eigComp t`. With `basisComp` a basis, this determines the
spectrum of `D²` completely: the eigenvalue multiset is the
sumset multiset of §6's `spectrumQ7CR2`. -/
theorem dirac_sq_basisComp_eig (t : compIndex) :
    ((diracQ7C4R4 factorQ7 factorC4 factorR) ^ 2) (basisComp t)
      = eigComp t • basisComp t := by
  obtain ⟨⟨⟨k₇, b₇⟩, ⟨k₄, b₄⟩⟩, m⟩ := t
  rw [eigComp_eq]
  exact dirac_sq_basisComp k₇ b₇ k₄ b₄ m

section SumsetLemmas

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Sum over a product of a first-factor function. -/
theorem sum_prod_fst (F : α → ℝ) :
    ∑ x : α × β, F x.1 = (Fintype.card β : ℝ) * ∑ a, F a := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum]

/-- Sum over a product of a second-factor function. -/
theorem sum_prod_snd (G : β → ℝ) :
    ∑ x : α × β, G x.2 = (Fintype.card α : ℝ) * ∑ b, G b := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Sum over a product of a product of factor functions. -/
theorem sum_prod_mul (F : α → ℝ) (G : β → ℝ) :
    ∑ x : α × β, F x.1 * G x.2 = (∑ a, F a) * ∑ b, G b := by
  rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum]

/-- Sum over the triple product of a first-factor function. -/
theorem sum_trio_fst (F : α → ℝ) :
    ∑ t : (α × β) × γ, F t.1.1
      = ((Fintype.card β : ℝ) * Fintype.card γ) * ∑ a, F a := by
  calc ∑ t : (α × β) × γ, F t.1.1
      = (Fintype.card γ : ℝ) * ∑ x : α × β, F x.1 :=
        sum_prod_fst (fun x : α × β => F x.1)
    _ = (Fintype.card γ : ℝ) * ((Fintype.card β : ℝ) * ∑ a, F a) := by
        rw [sum_prod_fst]
    _ = ((Fintype.card β : ℝ) * Fintype.card γ) * ∑ a, F a := by ring

/-- Sum over the triple product of a middle-factor function. -/
theorem sum_trio_mid (G : β → ℝ) :
    ∑ t : (α × β) × γ, G t.1.2
      = ((Fintype.card α : ℝ) * Fintype.card γ) * ∑ b, G b := by
  calc ∑ t : (α × β) × γ, G t.1.2
      = (Fintype.card γ : ℝ) * ∑ x : α × β, G x.2 :=
        sum_prod_fst (fun x : α × β => G x.2)
    _ = (Fintype.card γ : ℝ) * ((Fintype.card α : ℝ) * ∑ b, G b) := by
        rw [sum_prod_snd]
    _ = ((Fintype.card α : ℝ) * Fintype.card γ) * ∑ b, G b := by ring

/-- Sum over the triple product of a last-factor function. -/
theorem sum_trio_snd (H : γ → ℝ) :
    ∑ t : (α × β) × γ, H t.2
      = ((Fintype.card α : ℝ) * Fintype.card β) * ∑ c, H c := by
  calc ∑ t : (α × β) × γ, H t.2
      = (Fintype.card (α × β) : ℝ) * ∑ c, H c := sum_prod_snd H
    _ = ((Fintype.card α : ℝ) * Fintype.card β) * ∑ c, H c := by
        rw [Fintype.card_prod]
        push_cast
        ring

/-- Sum over the triple product of a first×middle product. -/
theorem sum_trio_mul_fst_mid (F : α → ℝ) (G : β → ℝ) :
    ∑ t : (α × β) × γ, F t.1.1 * G t.1.2
      = (Fintype.card γ : ℝ) * ((∑ a, F a) * ∑ b, G b) := by
  calc ∑ t : (α × β) × γ, F t.1.1 * G t.1.2
      = ∑ x : α × β, ∑ c : γ, F x.1 * G x.2 :=
        Fintype.sum_prod_type ..
    _ = ∑ x : α × β, (Fintype.card γ : ℝ) * (F x.1 * G x.2) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card γ : ℝ) * ∑ x : α × β, F x.1 * G x.2 := by
        rw [← Finset.mul_sum]
    _ = (Fintype.card γ : ℝ) * ((∑ a, F a) * ∑ b, G b) := by
        rw [sum_prod_mul]

/-- Sum over the triple product of a first×last product. -/
theorem sum_trio_mul_fst_snd (F : α → ℝ) (H : γ → ℝ) :
    ∑ t : (α × β) × γ, F t.1.1 * H t.2
      = (Fintype.card β : ℝ) * ((∑ a, F a) * ∑ c, H c) := by
  calc ∑ t : (α × β) × γ, F t.1.1 * H t.2
      = (∑ x : α × β, F x.1) * (∑ c, H c) :=
        sum_prod_mul (fun x : α × β => F x.1) H
    _ = ((Fintype.card β : ℝ) * ∑ a, F a) * (∑ c, H c) := by
        rw [sum_prod_fst]
    _ = (Fintype.card β : ℝ) * ((∑ a, F a) * (∑ c, H c)) := by ring

/-- Sum over the triple product of a middle×last product. -/
theorem sum_trio_mul_mid_snd (G : β → ℝ) (H : γ → ℝ) :
    ∑ t : (α × β) × γ, G t.1.2 * H t.2
      = (Fintype.card α : ℝ) * ((∑ b, G b) * ∑ c, H c) := by
  calc ∑ t : (α × β) × γ, G t.1.2 * H t.2
      = (∑ x : α × β, G x.2) * (∑ c, H c) :=
        sum_prod_mul (fun x : α × β => G x.2) H
    _ = ((Fintype.card α : ℝ) * ∑ b, G b) * (∑ c, H c) := by
        rw [sum_prod_snd]
    _ = (Fintype.card α : ℝ) * ((∑ b, G b) * (∑ c, H c)) := by ring

end SumsetLemmas

/-- **The first spectral moment, in factor sums:**
`∑ eigComp = 32 * ∑ s₇ + 56 * ∑ s₄ + 112 * ∑ s_R` (each factor
sum weighted by the other two realified dimensions). -/
theorem sum_eigComp :
    ∑ t, eigComp t
      = 32 * (∑ i, s₇ i) + 56 * (∑ j, s₄ j) + 112 * (∑ m, s_R m) := by
  have hsplit : ∑ t, eigComp t
      = ∑ t : compIndex, (s₇c t.1.1 + s₄c t.1.2 + s_R t.2) := by
    apply Finset.sum_congr rfl
    intro t _
    rfl
  rw [hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_trio_fst, sum_trio_mid, sum_trio_snd, sum_s₇c, sum_s₄c]
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring_nf

/-- **The second spectral moment**: `∑ (eigComp)² = 1518111 / 64`,
by the sumset expansion `(x + y + z)²` and the factor moments —
the exact value of the Python side (BR1-012). -/
theorem sum_eigComp_sq : ∑ t, (eigComp t) ^ 2 = 1518111 / 64 := by
  have hsplit : ∑ t, (eigComp t) ^ 2
      = ∑ t : compIndex, ((s₇c t.1.1) ^ 2 + (s₄c t.1.2) ^ 2
          + (s_R t.2) ^ 2 + 2 * (s₇c t.1.1 * s₄c t.1.2)
          + 2 * (s₇c t.1.1 * s_R t.2) + 2 * (s₄c t.1.2 * s_R t.2)) := by
    apply Finset.sum_congr rfl
    intro t _
    show (s₇c t.1.1 + s₄c t.1.2 + s_R t.2) ^ 2 = _
    ring
  have h1 := sum_trio_fst (α := Fin 7 × Fin 2) (β := Fin 4 × Fin 2)
    (γ := Fin 4) (fun a => (s₇c a) ^ 2)
  have h2 := sum_trio_mid (α := Fin 7 × Fin 2) (β := Fin 4 × Fin 2)
    (γ := Fin 4) (fun a => (s₄c a) ^ 2)
  have h3 := sum_trio_snd (α := Fin 7 × Fin 2) (β := Fin 4 × Fin 2)
    (γ := Fin 4) (fun a => (s_R a) ^ 2)
  have h4 := sum_trio_mul_fst_mid (γ := Fin 4) s₇c s₄c
  have h5 := sum_trio_mul_fst_snd (β := Fin 4 × Fin 2) s₇c s_R
  have h6 := sum_trio_mul_mid_snd (α := Fin 7 × Fin 2) s₄c s_R
  rw [hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    h1, h2, h3, h4, h5, h6, sum_s₇c, sum_s₄c, sum_s₇c_sq, sum_s₄c_sq,
    sum_s₇, sum_s₄, sum_s_R, sum_s₇_sq, sum_s₄_sq, sum_s_R_sq]
  norm_num [Fintype.card_prod, Fintype.card_fin]

/-- **The spectrum of the instantiated `D²`, as a multiset**: the
sumset multiset of the composite eigenvalue function over the
448 composite indices. By `dirac_sq_basisComp_eig` and `basisComp`
being a basis, these are exactly the eigenvalues of
`(diracQ7C4R4 factorQ7 factorC4 factorR)²`, with multiplicity. -/
noncomputable def spectrumQ7CR2 : Multiset ℝ :=
  Finset.univ.val.map eigComp

/-- **Anchor — total count: `448`.** -/
theorem spectrumQ7CR2_card : spectrumQ7CR2.card = 448 := by
  have h : spectrumQ7CR2.card = Fintype.card compIndex := by
    unfold spectrumQ7CR2
    rw [Multiset.card_map]
    rfl
  rw [h]
  norm_num [Fintype.card_prod, Fintype.card_fin]

/-- **Anchor — the spectral trace `M 1 = 2723`** (the sum of the
`D²` eigenvalues; the trace of `D²` against the §5 eigenbasis). -/
theorem spectrumQ7CR2_sum : spectrumQ7CR2.sum = 2723 := by
  show ∑ t, eigComp t = 2723
  rw [sum_eigComp, sum_s₇, sum_s₄, sum_s_R]
  norm_num

/-- **Anchor — the second moment `M 2 = 1518111 / 64`** (the sum
of the squared `D²` eigenvalues; the trace of `D⁴`). -/
theorem spectrumQ7CR2_sq_sum :
    (spectrumQ7CR2.map fun v => v ^ 2).sum = 1518111 / 64 := by
  rw [spectrumQ7CR2, Multiset.map_map]
  show ∑ t, (eigComp t) ^ 2 = 1518111 / 64
  exact sum_eigComp_sq

/-- **Endpoint — smallest eigenvalue: every composite eigenvalue
is at least `1 / 64`.** In particular the instantiated `D²` is
strictly positive on the eigenbasis: its smallest eigenvalue is
`1 / 64`, not `0`. -/
theorem eigComp_ge (t : compIndex) : 1 / 64 ≤ eigComp t := by
  show (1 : ℝ) / 64 ≤ s₇c t.1.1 + s₄c t.1.2 + s_R t.2
  have h1 := s₇c_nonneg t.1.1
  have h2 := s₄c_ge t.1.2
  have h3 := s_R_nonneg t.2
  linarith

/-- **Endpoint — largest eigenvalue: every composite eigenvalue
is at most `841 / 64`.** -/
theorem eigComp_le (t : compIndex) : eigComp t ≤ 841 / 64 := by
  show s₇c t.1.1 + s₄c t.1.2 + s_R t.2 ≤ 841 / 64
  have h1 := s₇c_le t.1.1
  have h2 := s₄c_le t.1.2
  have h3 := s_R_le t.2
  linarith

/-- The smallest eigenvalue `1 / 64` is attained (at Q⁷ site `6`,
C⁴ rung `1`, R⁴ site `0`). -/
theorem eigComp_min_attained :
    eigComp (((6, 0), (1, 0)), 0) = 1 / 64 := by
  show s₇c (6, 0) + s₄c (1, 0) + s_R 0 = 1 / 64
  rw [s₇c_apply, s₄c_apply]
  norm_num [a₇, d₄, z4Energy, s_R, r_R]

/-- The largest eigenvalue `841 / 64` is attained (at Q⁷ site `0`,
C⁴ rung `0`, R⁴ site `1`). -/
theorem eigComp_max_attained :
    eigComp (((0, 0), (0, 0)), 1) = 841 / 64 := by
  show s₇c (0, 0) + s₄c (0, 0) + s_R 1 = 841 / 64
  rw [s₇c_apply, s₄c_apply]
  norm_num [a₇, d₄, z4Energy, s_R, r_R]

/-- The endpoint squares are rational squares: the instantiated
`D`'s extreme eigenvalues are `±1 / 8` and `±29 / 8`. -/
theorem endpoint_squares :
    (1 / 8 : ℝ) ^ 2 = 1 / 64 ∧ (29 / 8 : ℝ) ^ 2 = 841 / 64 := by
  constructor <;> norm_num

/-! ## §7. Kill K-Q7CR-2 — the spectrum is NOT forced

A second admissible Q⁷ package, differing from `factorQ7` only in
the first diagonal pair (`3 ↦ 4`), has a different spectrum: its
spectral trace is `3619 ≠ 2723`. The spectrum is an explicit
function of the factor data, so the kill — which fires only if
the spectrum is identical for every choice of the free factor
operators — does **not** fire. -/

/-- **The varied Q⁷ diagonal (CHOSEN):** `a₇' = (4, -4, 2, -2, 1,
-1, 0)` — `a₇` with the first pair's magnitude changed. -/
def a₇' : Fin 7 → ℝ := ![4, -4, 2, -2, 1, -1, 0]

/-- The varied pairing law: `a₇' (p₇ k) = - a₇' k` (the same
grading `p₇` is admissible for the varied diagonal). -/
theorem a₇'_anti : ∀ k, a₇' (p₇ k) = - a₇' k := by
  intro k
  fin_cases k <;> simp [a₇', p₇]

/-- **The varied Q⁷ factor package**: a second admissible
`FactorOp 7`, built by the same §1 constructor. -/
def factorQ7' : FactorOp 7 := diagFactorOp a₇' p₇ a₇'_anti p₇_inv

/-- The varied Q⁷ factor square, pointwise. -/
theorem factorQ7'_D_sq_apply (x : Fin 7 → ℂ) (k : Fin 7) :
    (factorQ7'.D ^ 2) x k = ((a₇' k) ^ 2 : ℂ) * x k :=
  diagOpC_sq_apply a₇' x k

/-- The varied Q⁷ real site basis vectors are eigenvectors of
`(D₇')²`, with eigenvalue `a₇' k ^ 2`. -/
theorem factorQ7'_basisC_eigen (k : Fin 7) (b : Fin 2) :
    (factorQ7'.D ^ 2) (basisC 7 (k, b)) = (a₇' k ^ 2) • basisC 7 (k, b) := by
  funext j
  rw [factorQ7'_D_sq_apply]
  by_cases hj : j = k
  · subst hj
    rw [Pi.smul_apply, Complex.real_smul, basisC_apply]
    simp only [if_pos rfl]
    congr 1
    push_cast
    ring
  · simp [basisC_apply, hj, Pi.smul_apply]

/-- **The composite eigenvalue function with Q⁷ diagonal `a`**
(the C⁴ and R⁴ factors held at the §3 choices). -/
noncomputable def eigOf (a : Fin 7 → ℝ) (t : compIndex) : ℝ :=
  a t.1.1.1 ^ 2 + d₄ t.1.2.1 ^ 2 + r_R t.2 ^ 2

/-- The main eigenvalue function is `eigOf` at the §3 diagonal. -/
theorem eigComp_eq_eigOf (t : compIndex) : eigComp t = eigOf a₇ t := by
  unfold eigOf
  exact eigComp_eq t

/-- The squared Q⁷ diagonal, as a function on the realified Q⁷
index (the first factor of the sumset at diagonal `a`). -/
def aSq (a : Fin 7 → ℝ) : Fin 7 × Fin 2 → ℝ := fun x => a x.1 ^ 2

/-- **The varied eigenbasis theorem**: the composite basis
vectors are eigenvectors of the varied package's `D²`, with
eigenvalues `eigOf a₇'`. -/
theorem dirac_sq_basisComp_alt (k₇ : Fin 7) (b₇ : Fin 2) (k₄ : Fin 4)
    (b₄ : Fin 2) (m : Fin 4) :
    ((diracQ7C4R4 factorQ7' factorC4 factorR) ^ 2)
        (basisComp (((k₇, b₇), (k₄, b₄)), m))
      = eigOf a₇' (((k₇, b₇), (k₄, b₄)), m)
        • basisComp (((k₇, b₇), (k₄, b₄)), m) := by
  have hb : basisComp (((k₇, b₇), (k₄, b₄)), m)
      = ((basisC 7 (k₇, b₇) ⊗ₜ[ℝ] basisC 4 (k₄, b₄))
          ⊗ₜ[ℝ] (Pi.basisFun ℝ (Fin 4)) m) := by
    show Module.Basis.tensorProduct
        (Module.Basis.tensorProduct (basisC 7) (basisC 4))
        (Pi.basisFun ℝ (Fin 4)) (((k₇, b₇), (k₄, b₄)), m) = _
    rw [Module.Basis.tensorProduct_apply, Module.Basis.tensorProduct_apply]
  rw [hb, diracQ7C4R4_sq]
  simp only [LinearMap.add_apply, opTensorQ_tmul, Module.End.one_apply,
    factorQ7'_basisC_eigen, factorC4_basisC_eigen, factorR_basis_eigen]
  simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  rw [← add_smul, ← add_smul]
  rfl

/-- The spectral trace of `eigOf a`, in factor sums. -/
theorem sum_eigOf (a : Fin 7 → ℝ) :
    ∑ t, eigOf a t
      = 32 * (2 * ∑ k, a k ^ 2) + 56 * (∑ j, s₄ j)
        + 112 * (∑ m, s_R m) := by
  have hF : ∑ x : Fin 7 × Fin 2, aSq a x = 2 * ∑ k, a k ^ 2 := by
    show ∑ x : Fin 7 × Fin 2, a x.1 ^ 2 = 2 * ∑ k, a k ^ 2
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    norm_num
  have hsplit : ∑ t, eigOf a t
      = ∑ t : compIndex, (aSq a t.1.1 + s₄c t.1.2 + s_R t.2) := by
    apply Finset.sum_congr rfl
    intro t _
    show a t.1.1.1 ^ 2 + d₄ t.1.2.1 ^ 2 + r_R t.2 ^ 2
        = aSq a t.1.1 + s₄c t.1.2 + s_R t.2
    rw [s₄c_apply]
    rfl
  rw [hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_trio_fst, sum_trio_mid, sum_trio_snd, sum_s₄c, hF]
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring_nf

/-- The varied site squares sum to `42`. -/
theorem a₇'_sum_sq : ∑ k, a₇' k ^ 2 = 42 := by
  norm_num [Fin.sum_univ_seven, a₇']

/-- **The varied spectral trace: `3619`.** -/
theorem spectral_trace_alt : ∑ t, eigOf a₇' t = 3619 := by
  rw [sum_eigOf, a₇'_sum_sq, sum_s₄, sum_s_R]
  norm_num

/-- **The main spectral trace, in `eigOf` form: `2723`.** -/
theorem spectral_trace_main : ∑ t, eigOf a₇ t = 2723 := by
  rw [sum_eigOf, a₇_sum_sq, sum_s₄, sum_s_R]
  norm_num

/-- The spectrum, as a multiset, at Q⁷ diagonal `a`. -/
noncomputable def spectrumOf (a : Fin 7 → ℝ) : Multiset ℝ :=
  Finset.univ.val.map (eigOf a)

/-- At the §3 diagonal, `spectrumOf` is the certified spectrum. -/
theorem spectrumOf_a₇ : spectrumOf a₇ = spectrumQ7CR2 := by
  unfold spectrumOf spectrumQ7CR2
  apply Multiset.map_congr rfl
  intro t _
  exact (eigComp_eq_eigOf t).symm

/-- **The two spectral traces differ** (`3619 ≠ 2723`). -/
theorem spectral_traces_differ :
    (∑ t, eigOf a₇' t) ≠ (∑ t, eigOf a₇ t) := by
  rw [spectral_trace_alt, spectral_trace_main]
  norm_num

/-- **The two spectra differ as multisets.** -/
theorem spectrumOf_not_forced : spectrumOf a₇' ≠ spectrumOf a₇ := by
  intro h
  have hsum : (spectrumOf a₇').sum = (spectrumOf a₇).sum := by rw [h]
  have e1 : (spectrumOf a₇').sum = ∑ t, eigOf a₇' t := rfl
  have e2 : (spectrumOf a₇).sum = ∑ t, eigOf a₇ t := rfl
  rw [e1, e2, spectral_trace_alt, spectral_trace_main] at hsum
  norm_num at hsum

/-- **K-Q7CR-2, discharged in the landed form.** The instantiated
spectrum is not forced: two admissible Q⁷ factor packages —
`factorQ7` and `factorQ7'`, differing in one diagonal pair —
give different eigenvalue multisets for the composite `D²`
(their spectral traces are `2723` and `3619`). The kill does not
fire; Item 4's spectrum does work in this form. -/
theorem k_q7cr2_not_forced :
    spectrumOf a₇' ≠ spectrumOf a₇
      ∧ (∑ t, eigOf a₇' t) ≠ (∑ t, eigOf a₇ t) :=
  ⟨spectrumOf_not_forced, spectral_traces_differ⟩

end ThetLogos
