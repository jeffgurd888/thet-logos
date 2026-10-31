import Mathlib.Tactic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.TensorProduct.Basis
import ThetLogos.Q7C4R4Assembly
import ThetLogos.Q7C4R4Spectrum

/-!
# ThetLogos.SpectralActionQ7CR — the finite spectral action of the
Q⁷C⁴R⁴ composite: definitions + the moment-composition backbone
(Q7CR-SA0)

**Status: T1 brick (general, over factor operators).
NO CLAIM. Dials 0/4. No measured number is claimed by this line.**

Governing scoping: `scoping-q7cr-spectral-action-2026-10-30.md`
§§2, 3.1–3.2, 4 (brick Q7CR-SA0), 6, 7. Anchor: Q7CR-1b
(`ThetLogos.Q7C4R4Assembly`): the assembled product Dirac
`diracQ7C4R4` on the registered composite `q7c4r4Composite`
(the tensor seat `((Fin 7 → ℂ) ⊗[ℝ] (Fin 4 → ℂ)) ⊗[ℝ] Minkowski`,
real dimension 448), and its proved square identity
`diracQ7C4R4_sq`, in the lifted form. This module follows that
seat and idiom exactly: traces are `LinearMap.trace ℝ _` of
endomorphisms of the tensor seat; the factor spaces are
`Fin 7 → ℂ` (real dimension 14), `Fin 4 → ℂ` (real dimension 8)
and `Minkowski` (real dimension 4).

## What this brick is

The spectral action of the composite, defined **numerically**
(design decision D-SA-2 of the scoping memo): never as an
operator `f (D²)` — no functional calculus is defined or used
anywhere in this module. The action is a NUMBER assembled from
spectral data, in the two forms that need no calculus:

* the **spectral-sum form** (§1, `specSum`): a sum over supplied
  eigenvalue data of a cutoff's values;
* the **moment form** (§1, `q7crMom7`, `q7crMom4`, `q7crMomR`,
  `q7crMoment`): traces of powers of the factor squares and of
  the composite square, and the polynomial action
  `q7crActionPoly` assembled from the composite moments.

The brick's content (the scoping memo's SA-COMP-2, §3) is the
**moment-composition backbone**: at general `k`, the composite
moment `M k = tr ((D²)^k)` is the multinomial composition of the
factor moments — the trinomial expansion of the Kronecker sum
`D² = A ⊗ 1 ⊗ 1 + 1 ⊗ B ⊗ 1 + 1 ⊗ 1 ⊗ C` (1b's square identity),
with each mixed trace split by the trace-of-tensor-product
compatibility lemma (§2, D-SA-1) and the unit factors
contributing their real dimensions 14 / 8 / 4 at power 0.
Printed instances `M 0 = 448`, `M 1`, `M 2` are corollaries (§5).

## Fences, on the face

- **Finite moments are NOT Seeley–DeWitt coefficients.** No
  moment in this module is an Einstein–Hilbert term, a
  cosmological term, or any curvature quantity; the composite
  object has **no curvature slot** and no manifold factor (its
  R⁴ factor is a 4-dimensional representation space). The moment
  sequence is coefficient-grade finite data attached to a chosen
  operator — the finite seat's substitute for a coefficient
  sequence, nothing more.
- **Dial 1 unmoved by construction.** Every number produced
  here is an explicit function of declared inputs (the cutoff
  coefficients, the scale `Λ`, and the three factor operator
  packages; scoping memo §6). Any coincidence of an output with
  a measured value would be a NEW entry under the Dial-1
  process (kill K-SA-4), never a result of this line.
- **Kill K-SA-2 (vacuity guard).** A definitions-only landing
  would be PARTIAL for this brick; the content is SA-COMP-2 at
  general `k`, proved in §4 below.
- **Bounded-commutator caveat.** In finite dimension the
  bounded-commutator criterion is vacuous; the testable content
  here is spectrum, grading, and `D²` — here, the trace-level
  consequences of `D²`.
- NO entropy language anywhere in this line (the T-ENT gate).
- NO CLAIM; dials 0/4; no measured number is claimed by this
  line; the continuum Spectral Action Principle is FRONTIER and
  is not approximated, shadowed, or prefigured by anything here.
-/

namespace ThetLogos

/-! ## §1. Definitions — the action as a number (D-SA-2) -/

/-- **The finite spectral action in spectral-sum form**: a sum
over a supplied eigenvalue list `e` of a cutoff `f`'s values at
`e i / Λ²`. The list is data; no diagonalization is asserted or
proved here. `Λ ≠ 0` is the reading's only hypothesis and is not
needed by the definition. -/
noncomputable def specSum {n : ℕ} (e : Fin n → ℝ) (f : ℝ → ℝ) (Λ : ℝ) : ℝ :=
  ∑ i, f (e i / Λ ^ 2)

/-- **The Q⁷ factor moment**: `a p = tr ((D₇²)^p)`, a real number
assembled from the factor package alone (traces of powers; never
an operator function of `D₇²`). -/
noncomputable def q7crMom7 (F₇ : FactorOp 7) (p : ℕ) : ℝ :=
  LinearMap.trace ℝ (Fin 7 → ℂ) ((F₇.D ^ 2) ^ p)

/-- **The C⁴ factor moment**: `b p = tr ((D₄²)^p)`. -/
noncomputable def q7crMom4 (F₄ : FactorOp 4) (p : ℕ) : ℝ :=
  LinearMap.trace ℝ (Fin 4 → ℂ) ((F₄.D ^ 2) ^ p)

/-- **The R⁴ factor moment**: `c p = tr ((D_R²)^p)`. -/
noncomputable def q7crMomR (F_R : FactorOpR) (p : ℕ) : ℝ :=
  LinearMap.trace ℝ Minkowski ((F_R.D ^ 2) ^ p)

/-- **The composite moment**: `M k = tr ((D²)^k)` for the
assembled product Dirac `D = diracQ7C4R4 F₇ F₄ F_R`. -/
noncomputable def q7crMoment (F₇ : FactorOp 7) (F₄ : FactorOp 4) (F_R : FactorOpR)
    (k : ℕ) : ℝ :=
  LinearMap.trace ℝ q7c4r4Composite
    (((diracQ7C4R4 F₇ F₄ F_R) ^ 2) ^ k)

/-- **The polynomial spectral action of the composite** (moment
form): for a polynomial cutoff with coefficients
`c : Fin (K+1) → ℝ` at a stated degree `K` and scale `Λ`, the
number `∑ k, c k · M k / (Λ²)^k`, assembled from the composite
moments alone. -/
noncomputable def q7crActionPoly (F₇ : FactorOp 7) (F₄ : FactorOp 4)
    (F_R : FactorOpR) (K : ℕ) (c : Fin (K + 1) → ℝ) (Λ : ℝ) : ℝ :=
  ∑ k : Fin (K + 1), c k * (q7crMoment F₇ F₄ F_R k.val / (Λ ^ 2) ^ k.val)

/-! ## §2. D-SA-1 — trace of a triple tensor product

The compatibility lemma at 1b's landed seat: the trace of a
triple operator tensor is the product of the factor traces.
This is the pin's `LinearMap.trace_tensorProduct'` (the
`⊗ₜ`-seat form of `Matrix.trace_kronecker`), applied twice along
the composite's association. -/

/-- **D-SA-1 (trace–tensor compatibility at the composite
seat).** `tr (X ⊗ₜ Y ⊗ₜ Z) = tr X · tr Y · tr Z` for
endomorphisms of the three registered factors. -/
theorem trace_opTensorQ (X : Module.End ℝ (Fin 7 → ℂ))
    (Y : Module.End ℝ (Fin 4 → ℂ)) (Z : Module.End ℝ Minkowski) :
    LinearMap.trace ℝ q7c4r4Composite (opTensorQ X Y Z)
      = LinearMap.trace ℝ (Fin 7 → ℂ) X
        * LinearMap.trace ℝ (Fin 4 → ℂ) Y
        * LinearMap.trace ℝ Minkowski Z := by
  unfold opTensorQ opTensor3
  rw [LinearMap.trace_tensorProduct', LinearMap.trace_tensorProduct']

/-! ## §3. The factor dimensions and the power-zero moments

The unit factors in the Kronecker sum contribute their real
dimensions at power 0: `tr (1) = finrank`, and the registered
dimensions are 14, 8, 4 (composite 448). -/

/-- The Q⁷ factor's real dimension is 14. -/
theorem finrank_q7_factor : Module.finrank ℝ (Fin 7 → ℂ) = 14 := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex]

/-- The C⁴ factor's real dimension is 8. -/
theorem finrank_c4_factor : Module.finrank ℝ (Fin 4 → ℂ) = 8 := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex]

/-- The R⁴ factor's real dimension is 4. -/
theorem finrank_r4_factor : Module.finrank ℝ Minkowski = 4 := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp

/-- The composite's real dimension is 448 `= 14 · 8 · 4`. -/
theorem finrank_q7c4r4Composite :
    Module.finrank ℝ q7c4r4Composite = 448 := by
  rw [Module.finrank_tensorProduct, Module.finrank_tensorProduct,
    finrank_q7_factor, finrank_c4_factor, finrank_r4_factor]

/-- Power-zero Q⁷ factor moment: `a 0 = 14`. -/
theorem q7crMom7_zero (F₇ : FactorOp 7) : q7crMom7 F₇ 0 = 14 := by
  unfold q7crMom7
  rw [pow_zero, LinearMap.trace_one, finrank_q7_factor]
  norm_num

/-- Power-zero C⁴ factor moment: `b 0 = 8`. -/
theorem q7crMom4_zero (F₄ : FactorOp 4) : q7crMom4 F₄ 0 = 8 := by
  unfold q7crMom4
  rw [pow_zero, LinearMap.trace_one, finrank_c4_factor]
  norm_num

/-- Power-zero R⁴ factor moment: `c 0 = 4`. -/
theorem q7crMomR_zero (F_R : FactorOpR) : q7crMomR F_R 0 = 4 := by
  unfold q7crMomR
  rw [pow_zero, LinearMap.trace_one, finrank_r4_factor]
  norm_num

/-! ## §4. SA-COMP-2 — the moment-composition backbone

The three summands of `D²` (1b's square identity) act on distinct
tensor factors, hence pairwise commute; `(D²)^k` expands by two
applications of the binomial theorem for commuting elements
(`Commute.add_pow`), and each mixed product is a triple tensor
whose trace splits by D-SA-1. -/

/-- Powers of a left triple tensor. -/
theorem opTensorQ_pow_left (X : Module.End ℝ (Fin 7 → ℂ)) (i : ℕ) :
    (opTensorQ X 1 1) ^ i = opTensorQ (X ^ i) 1 1 := by
  induction i with
  | zero =>
    simp only [pow_zero]
    unfold opTensorQ
    exact opTensor3_one.symm
  | succ n ih =>
    rw [pow_succ, ih, ← opTensorQ_mul]
    simp [pow_succ]

/-- Powers of a middle triple tensor. -/
theorem opTensorQ_pow_mid (Y : Module.End ℝ (Fin 4 → ℂ)) (j : ℕ) :
    (opTensorQ 1 Y 1) ^ j = opTensorQ 1 (Y ^ j) 1 := by
  induction j with
  | zero =>
    simp only [pow_zero]
    unfold opTensorQ
    exact opTensor3_one.symm
  | succ n ih =>
    rw [pow_succ, ih, ← opTensorQ_mul]
    simp [pow_succ]

/-- Powers of a right triple tensor. -/
theorem opTensorQ_pow_right (Z : Module.End ℝ Minkowski) (l : ℕ) :
    (opTensorQ 1 1 Z) ^ l = opTensorQ 1 1 (Z ^ l) := by
  induction l with
  | zero =>
    simp only [pow_zero]
    unfold opTensorQ
    exact opTensor3_one.symm
  | succ n ih =>
    rw [pow_succ, ih, ← opTensorQ_mul]
    simp [pow_succ]

/-- A product of powers of the three factor tensors is the triple
tensor of the powers. -/
theorem opTensorQ_pow_mul (X : Module.End ℝ (Fin 7 → ℂ))
    (Y : Module.End ℝ (Fin 4 → ℂ)) (Z : Module.End ℝ Minkowski)
    (i j l : ℕ) :
    (opTensorQ X 1 1) ^ i * (opTensorQ 1 Y 1) ^ j
        * (opTensorQ 1 1 Z) ^ l
      = opTensorQ (X ^ i) (Y ^ j) (Z ^ l) := by
  rw [opTensorQ_pow_left, opTensorQ_pow_mid, opTensorQ_pow_right,
    ← opTensorQ_mul, ← opTensorQ_mul]
  simp

/-- The left and middle summands of `D²` commute. -/
theorem commute_opTensorQ_left_mid (X : Module.End ℝ (Fin 7 → ℂ))
    (Y : Module.End ℝ (Fin 4 → ℂ)) :
    Commute (opTensorQ X 1 1) (opTensorQ 1 Y 1) := by
  show opTensorQ X 1 1 * opTensorQ 1 Y 1
      = opTensorQ 1 Y 1 * opTensorQ X 1 1
  rw [← opTensorQ_mul, ← opTensorQ_mul]
  simp

/-- The left and right summands of `D²` commute. -/
theorem commute_opTensorQ_left_right (X : Module.End ℝ (Fin 7 → ℂ))
    (Z : Module.End ℝ Minkowski) :
    Commute (opTensorQ X 1 1) (opTensorQ 1 1 Z) := by
  show opTensorQ X 1 1 * opTensorQ 1 1 Z
      = opTensorQ 1 1 Z * opTensorQ X 1 1
  rw [← opTensorQ_mul, ← opTensorQ_mul]
  simp

/-- The middle and right summands of `D²` commute. -/
theorem commute_opTensorQ_mid_right (Y : Module.End ℝ (Fin 4 → ℂ))
    (Z : Module.End ℝ Minkowski) :
    Commute (opTensorQ 1 Y 1) (opTensorQ 1 1 Z) := by
  show opTensorQ 1 Y 1 * opTensorQ 1 1 Z
      = opTensorQ 1 1 Z * opTensorQ 1 Y 1
  rw [← opTensorQ_mul, ← opTensorQ_mul]
  simp

/-- The sum of the left and middle summands commutes with the
right summand (proved directly, in the same style as the pairwise
commutes above). -/
theorem commute_opTensorQ_add_left_right (X : Module.End ℝ (Fin 7 → ℂ))
    (Y : Module.End ℝ (Fin 4 → ℂ)) (Z : Module.End ℝ Minkowski) :
    Commute (opTensorQ X 1 1 + opTensorQ 1 Y 1) (opTensorQ 1 1 Z) := by
  show (opTensorQ X 1 1 + opTensorQ 1 Y 1) * opTensorQ 1 1 Z
      = opTensorQ 1 1 Z * (opTensorQ X 1 1 + opTensorQ 1 Y 1)
  rw [add_mul, mul_add, ← opTensorQ_mul, ← opTensorQ_mul,
    ← opTensorQ_mul, ← opTensorQ_mul]
  simp

/-- Moving two binomial-coefficient casts out of an operator
product: `(P * ↑a) * Q * ↑b = ↑(b * a) * (P * Q)`, with all casts
in the endomorphism ring (no scalar action is used anywhere in
this section: `Module.End` carries two module structures over
ℝ, and keeping the coefficient as a cast multiplication keeps
every statement instance-unambiguous). Stated at the composite
seat directly: `Module.End` bakes the factor module instances
into its type, so a generic-`V` form of this lemma does not
match the tensor seat's terms. -/
theorem mul_natCast_mul_natCast
    (P Q : Module.End ℝ q7c4r4Composite) (a b : ℕ) :
    (P * (a : Module.End ℝ q7c4r4Composite)) * Q
        * (b : Module.End ℝ q7c4r4Composite)
      = ((b * a : ℕ) : Module.End ℝ q7c4r4Composite) * (P * Q) := by
  calc (P * (a : Module.End ℝ q7c4r4Composite)) * Q
        * (b : Module.End ℝ q7c4r4Composite)
      = (b : Module.End ℝ q7c4r4Composite)
          * ((P * (a : Module.End ℝ q7c4r4Composite)) * Q) :=
        (Nat.cast_commute b _).eq.symm
    _ = (b : Module.End ℝ q7c4r4Composite)
          * ((a : Module.End ℝ q7c4r4Composite) * (P * Q)) := by
        rw [(Nat.cast_commute a P).eq.symm, mul_assoc]
    _ = ((b * a : ℕ) : Module.End ℝ q7c4r4Composite) * (P * Q) := by
        rw [← mul_assoc, ← Nat.cast_mul]

/-- **The operator-level trinomial expansion.** `(D²)^k` is the
sum, over `l ≤ k` (the power of the `R⁴` summand split off first)
and `i ≤ l` (the power of the Q⁷ summand), of the scalar
`k.choose l * l.choose i` times the product of the three factor
tensors' powers. The coefficient is the trinomial coefficient
`k! / (i! · (l - i)! · (k - l)!)` in its choose-product form. -/
theorem diracQ7C4R4_sq_pow_expand (F₇ : FactorOp 7) (F₄ : FactorOp 4)
    (F_R : FactorOpR) (k : ℕ) :
    ((diracQ7C4R4 F₇ F₄ F_R) ^ 2) ^ k
      = ∑ l ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (l + 1),
        ((Nat.choose k l * Nat.choose l i : ℕ)
            : Module.End ℝ q7c4r4Composite)
          * ((opTensorQ (F₇.D ^ 2) 1 1) ^ i
            * (opTensorQ 1 (F₄.D ^ 2) 1) ^ (l - i)
            * (opTensorQ 1 1 (F_R.D ^ 2)) ^ (k - l)) := by
  have hXY : Commute (opTensorQ (F₇.D ^ 2) 1 1)
      (opTensorQ 1 (F₄.D ^ 2) 1) :=
    commute_opTensorQ_left_mid _ _
  have hXYZ : Commute (opTensorQ (F₇.D ^ 2) 1 1
      + opTensorQ 1 (F₄.D ^ 2) 1) (opTensorQ 1 1 (F_R.D ^ 2)) :=
    commute_opTensorQ_add_left_right _ _ _
  have hexp : (opTensorQ (F₇.D ^ 2) 1 1 + opTensorQ 1 (F₄.D ^ 2) 1
        + opTensorQ 1 1 (F_R.D ^ 2)) ^ k
      = ∑ l ∈ Finset.range (k + 1),
        (opTensorQ (F₇.D ^ 2) 1 1 + opTensorQ 1 (F₄.D ^ 2) 1) ^ l
          * (opTensorQ 1 1 (F_R.D ^ 2)) ^ (k - l)
          * (Nat.choose k l) :=
    hXYZ.add_pow k
  rw [diracQ7C4R4_sq, hexp]
  apply Finset.sum_congr rfl
  intro l _
  have hexp2 : (opTensorQ (F₇.D ^ 2) 1 1
        + opTensorQ 1 (F₄.D ^ 2) 1) ^ l
      = ∑ i ∈ Finset.range (l + 1),
        (opTensorQ (F₇.D ^ 2) 1 1) ^ i
          * (opTensorQ 1 (F₄.D ^ 2) 1) ^ (l - i)
          * (Nat.choose l i) :=
    hXY.add_pow l
  rw [hexp2, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_natCast_mul_natCast
    ((opTensorQ (F₇.D ^ 2) 1 1) ^ i
      * (opTensorQ 1 (F₄.D ^ 2) 1) ^ (l - i))
    ((opTensorQ 1 1 (F_R.D ^ 2)) ^ (k - l))
    (Nat.choose l i) (Nat.choose k l)

/-- The trace of a natural-cast multiple of an endomorphism:
`tr (↑n * T) = n * tr T`, by induction on `n` (no scalar action
on `Module.End` is used — see `mul_natCast_mul_natCast`). -/
theorem trace_natCast_mul (n : ℕ)
    (T : Module.End ℝ q7c4r4Composite) :
    LinearMap.trace ℝ q7c4r4Composite
        ((n : Module.End ℝ q7c4r4Composite) * T)
      = (n : ℝ) * LinearMap.trace ℝ q7c4r4Composite T := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ, add_mul, one_mul, map_add, ih, Nat.cast_succ]
    ring

/-- **SA-COMP-2 — moment composition (the backbone).** For every
`k`, the composite moment is the multinomial composition of the
factor moments:
`M k = Σ_{l ≤ k} Σ_{i ≤ l} (k.choose l · l.choose i) · a i · b (l - i) · c (k - l)`,
where the coefficient `k.choose l · l.choose i` is the trinomial
coefficient `k! / (i! · (l - i)! · (k - l)!)` in choose-product
form — the expansion of `(A + B + C)^k` traced term by term, each
mixed trace splitting by D-SA-1 with the unit factors
contributing `a 0 = 14`, `b 0 = 8`, `c 0 = 4` at power zero. -/
theorem moment_composition (F₇ : FactorOp 7) (F₄ : FactorOp 4)
    (F_R : FactorOpR) (k : ℕ) :
    q7crMoment F₇ F₄ F_R k
      = ∑ l ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (l + 1),
        (Nat.choose k l * Nat.choose l i : ℝ)
          * q7crMom7 F₇ i * q7crMom4 F₄ (l - i)
          * q7crMomR F_R (k - l) := by
  unfold q7crMoment
  rw [diracQ7C4R4_sq_pow_expand]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [trace_natCast_mul, opTensorQ_pow_mul, trace_opTensorQ]
  simp only [q7crMom7, q7crMom4, q7crMomR, Nat.cast_mul]
  ring

/-! ## §5. Printed instances: `M 0`, `M 1`, `M 2`

Checkable forms on the face, as corollaries of SA-COMP-2 (and, for
`M 0`, of the trace of the identity). Sanity: at unit factor
squares these give `M 1 = 3 · 448` and `M 2 = 9 · 448`, as
`D² = 3 · 1` on the composite demands. These moments are
coefficient-grade finite data — NOT Seeley–DeWitt coefficients
(see the header fences). -/

/-- Power-zero composite moment: `M 0 = 448`, the composite real
dimension — the `k = 0` instance of SA-COMP-2 (equivalently, the
trace of the identity on the composite). -/
theorem q7crMoment_zero (F₇ : FactorOp 7) (F₄ : FactorOp 4)
    (F_R : FactorOpR) : q7crMoment F₇ F₄ F_R 0 = 448 := by
  rw [moment_composition]
  norm_num [Finset.sum_range_succ, q7crMom7_zero, q7crMom4_zero,
    q7crMomR_zero]

/-- First composite moment:
`M 1 = 32 · a 1 + 56 · b 1 + 112 · c 1`. -/
theorem moment_one (F₇ : FactorOp 7) (F₄ : FactorOp 4)
    (F_R : FactorOpR) :
    q7crMoment F₇ F₄ F_R 1
      = 32 * q7crMom7 F₇ 1 + 56 * q7crMom4 F₄ 1
        + 112 * q7crMomR F_R 1 := by
  rw [moment_composition]
  norm_num [Finset.sum_range_succ, q7crMom7_zero, q7crMom4_zero,
    q7crMomR_zero]
  ring

/-- Second composite moment:
`M 2 = 32 · a 2 + 56 · b 2 + 112 · c 2 + 8 · (a 1)(b 1)
      + 16 · (a 1)(c 1) + 28 · (b 1)(c 1)`. -/
theorem moment_two (F₇ : FactorOp 7) (F₄ : FactorOp 4)
    (F_R : FactorOpR) :
    q7crMoment F₇ F₄ F_R 2
      = 32 * q7crMom7 F₇ 2 + 56 * q7crMom4 F₄ 2
        + 112 * q7crMomR F_R 2
        + 8 * (q7crMom7 F₇ 1 * q7crMom4 F₄ 1)
        + 16 * (q7crMom7 F₇ 1 * q7crMomR F_R 1)
        + 28 * (q7crMom4 F₄ 1 * q7crMomR F_R 1) := by
  rw [moment_composition]
  norm_num [Finset.sum_range_succ, q7crMom7_zero, q7crMom4_zero,
    q7crMomR_zero]
  ring

/-! ## §6. Q7CR-SA1 — the spectral-sum composition

The spectral-sum side of the action (scoping memo §3.1, §3.3):
eigenvalue data packaged WITH diagonalization witnesses
(`SpectralList`), the tensoring of factor witnesses across the
Kronecker sum (SA-COMP-1), the heat-trace factorization
(SA-COMP-3), and the agreement of the spectral-sum and moment
forms on polynomial cutoffs (SA-COMP-5, with SA-COMP-4 as its
composition corollary).

**K-SA-3 status (named, exact).** Diagonalization data is
PRODUCED from the pin where the pin's seat reaches, and consumed
as supplied data where it does not:

* For the two realified complex factors the production goes
  through (§6.5): the pin has no `InnerProductSpace ℝ` instance
  on the plain function space `Fin n → ℂ`, so the registered
  pairing `factorPair n` is installed as a local inner product
  through the pin's own `InnerProductSpace.Core` /
  `InnerProductSpace.ofCore` route, the factor square is
  symmetric for it from the package's own `D_selfadj`, and
  `LinearMap.IsSymmetric.eigenvectorBasis` /
  `LinearMap.IsSymmetric.eigenvalues` of
  `Mathlib/Analysis/InnerProductSpace/Spectrum.lean` supply the
  eigenvalue list and orthonormal eigenbasis.
* The R⁴ factor's seat is NOT reached by those APIs, and this is
  the exact mismatch: `FactorOpR.D_selfadj` is self-adjointness
  for `minkowskiInner`, the INDEFINITE η-pairing (signature
  (−,+,+,+); `minkowskiInner x x` takes negative values), so it
  is not a positive-definite inner product and no
  `InnerProductSpace.Core` with inner `minkowskiInner` exists;
  the pin's spectral APIs require a positive-definite
  `InnerProductSpace` and `LinearMap.IsSymmetric` with respect
  to THAT inner product — at this seat the Euclidean Pi inner
  product, for which the package carries no symmetry hypothesis
  at all. The composite seat inherits the same obstruction
  (its registered pairing is the product pairing, indefinite
  through the R⁴ factor). So the R⁴ spectral list is consumed
  as supplied data in SA-COMP-1/3/5, exactly as the memo's
  K-SA-3 fences: the list-level identities below are theorems
  about supplied lists and their sumsets, and the step "the R⁴
  factor's own spectral list is produced from its package" is
  the FRONTIER-marked step at this seat only. The moment
  backbone (§4, SA0) never touches an eigenvalue and is
  unaffected.

Fences as in the header: numeric forms only, never an operator
`f (D²)`; the moments are NOT Seeley–DeWitt coefficients; no
curvature slot; Dial 1 unmoved; no measured number is claimed
by this line; NO CLAIM. -/

/-! ### §6.1. Spectral lists as data with witnesses -/

/-- **A spectral list for `X`, as supplied data with its
diagonalization witness**: an eigenvalue function `e` on a finite
index type, a basis `b` of the space, and the eigenvector law
`X (b i) = e i • b i` for every index. This is the memo's §3.1
definition — eigenvalue data as data, with the witness carried,
not asserted into existence. Taking the index to be a general
finite type (rather than `Fin n`) is what lets the composite's
list live on the product index of §6.2 with its multiplicities
on the nose. -/
structure SpectralList (V : Type*) [AddCommGroup V] [Module ℝ V]
    (ι : Type*) [Fintype ι] (X : Module.End ℝ V) where
  /-- The eigenvalue list, as a function on the index type. -/
  e : ι → ℝ
  /-- The diagonalizing basis (the witness). -/
  b : Module.Basis ι ℝ V
  /-- Every basis vector is an eigenvector with eigenvalue `e i`. -/
  eig : ∀ i, X (b i) = e i • b i

/-- The eigenvalue multiset of a spectral list (the list read
with multiplicities). -/
noncomputable def SpectralList.eigenMultiset {V : Type*}
    [AddCommGroup V] [Module ℝ V] {ι : Type*} [Fintype ι]
    {X : Module.End ℝ V} (S : SpectralList V ι X) : Multiset ℝ :=
  (Finset.univ.val).map S.e

/-- **The composite spectral list, at the level of eigenvalue
functions**: the sumset of the three factor-square lists,
`specComp e₇ e₄ eR (i, j, k) = e₇ i + e₄ j + eR k` on the product
index `Fin 14 × Fin 8 × Fin 4` (cardinality `14 · 8 · 4 = 448`). -/
def specComp (e₇ : Fin 14 → ℝ) (e₄ : Fin 8 → ℝ) (eR : Fin 4 → ℝ) :
    (Fin 14 × Fin 8 × Fin 4) → ℝ :=
  fun p => e₇ p.1 + e₄ p.2.1 + eR p.2.2

/-- **The spectral-sum form at a general finite index type.**
SA0's `specSum` is indexed by `Fin n`; the composite's list lives
on the product index, so SA1 uses this general-index form, which
restricts to `specSum` on `Fin n` on the nose. -/
noncomputable def specSumIdx {ι : Type*} [Fintype ι] (e : ι → ℝ) (f : ℝ → ℝ)
    (Λ : ℝ) : ℝ :=
  ∑ i, f (e i / Λ ^ 2)

/-- The general-index spectral sum restricts to SA0's `specSum`
at a `Fin n` index. -/
theorem specSumIdx_fin {n : ℕ} (e : Fin n → ℝ) (f : ℝ → ℝ)
    (Λ : ℝ) : specSumIdx e f Λ = specSum e f Λ :=
  rfl

/-- A spectral list for a power, from a spectral list for the
base: same witness basis, eigenvalues raised to the power. -/
def SpectralList.pow {V : Type*} [AddCommGroup V] [Module ℝ V]
    {ι : Type*} [Fintype ι] {X : Module.End ℝ V}
    (S : SpectralList V ι X) (k : ℕ) : SpectralList V ι (X ^ k) where
  e := fun i => (S.e i) ^ k
  b := S.b
  eig := by
    intro i
    induction k with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, S.eig i,
        smul_smul, ← pow_succ]

/-- The trace of an endomorphism with a spectral list is the sum
of its eigenvalues (the diagonal of its matrix in the witness
basis). -/
theorem SpectralList.trace_eq_sum {V : Type*} [AddCommGroup V]
    [Module ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Module.End ℝ V} (S : SpectralList V ι X) :
    LinearMap.trace ℝ V X = ∑ i, S.e i := by
  rw [LinearMap.trace_eq_matrix_trace ℝ S.b]
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.toMatrix_apply, S.eig i]
  simp

/-- The trace of a power, from a spectral list:
`tr (X^k) = ∑ i, (e i)^k` — the bridge SA-COMP-5 stands on. -/
theorem SpectralList.trace_pow_eq_sum {V : Type*} [AddCommGroup V]
    [Module ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Module.End ℝ V} (S : SpectralList V ι X) (k : ℕ) :
    LinearMap.trace ℝ V (X ^ k) = ∑ i, (S.e i) ^ k :=
  (S.pow k).trace_eq_sum

/-! ### §6.2. Tensoring witnesses — SA-COMP-1 -/

/-- The Kronecker-sum eigenvector law on pure tensors: a tensor
product of eigenvectors of the three factor squares is an
eigenvector of the Kronecker sum, with eigenvalue the sum of the
factor eigenvalues. -/
theorem kronecker_sum_eigenvector
    (A : Module.End ℝ (Fin 7 → ℂ)) (B : Module.End ℝ (Fin 4 → ℂ))
    (C : Module.End ℝ Minkowski)
    (x : Fin 7 → ℂ) (y : Fin 4 → ℂ) (z : Minkowski)
    (a b c : ℝ) (hx : A x = a • x) (hy : B y = b • y)
    (hz : C z = c • z) :
    (opTensorQ A 1 1 + opTensorQ 1 B 1 + opTensorQ 1 1 C)
        ((x ⊗ₜ[ℝ] y) ⊗ₜ[ℝ] z)
      = (a + b + c) • ((x ⊗ₜ[ℝ] y) ⊗ₜ[ℝ] z) := by
  rw [LinearMap.add_apply, LinearMap.add_apply, opTensorQ_tmul,
    opTensorQ_tmul, opTensorQ_tmul, hx, hy, hz]
  simp only [Module.End.one_apply, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul]
  rw [add_smul, add_smul]

/-- **Tensoring of witnesses.** From spectral lists for the three
factor squares, a spectral list for the composite square
`(diracQ7C4R4 F₇ F₄ F_R)²`: the witness is the tensor product of
the factor eigenbases (reindexed along the associator of the
product index), and the eigenvalue function is `specComp` of the
factor lists — the sumset, with multiplicities. The composite
list is PRODUCED here from the factor lists; producing the
factor lists themselves is §6.5's business (and its named seam). -/
noncomputable def SpectralList.tensorQ (F₇ : FactorOp 7)
    (F₄ : FactorOp 4) (F_R : FactorOpR)
    (S₇ : SpectralList (Fin 7 → ℂ) (Fin 14) (F₇.D ^ 2)) (S₄ : SpectralList (Fin 4 → ℂ) (Fin 8) (F₄.D ^ 2))
    (SR : SpectralList Minkowski (Fin 4) (F_R.D ^ 2)) :
    SpectralList q7c4r4Composite (Fin 14 × Fin 8 × Fin 4)
      ((diracQ7C4R4 F₇ F₄ F_R) ^ 2) where
  e := specComp S₇.e S₄.e SR.e
  b := ((S₇.b.tensorProduct S₄.b).tensorProduct SR.b).reindex
    (Equiv.prodAssoc (Fin 14) (Fin 8) (Fin 4))
  eig := by
    intro p
    obtain ⟨i, j, k⟩ := p
    have hvec : (((S₇.b.tensorProduct S₄.b).tensorProduct SR.b).reindex
        (Equiv.prodAssoc (Fin 14) (Fin 8) (Fin 4))) (i, j, k)
        = (S₇.b i ⊗ₜ[ℝ] S₄.b j) ⊗ₜ[ℝ] SR.b k := by
      simp [Module.Basis.reindex_apply, Module.Basis.tensorProduct_apply]
    rw [hvec, diracQ7C4R4_sq]
    exact kronecker_sum_eigenvector _ _ _ _ _ _ _ _ _
      (S₇.eig i) (S₄.eig j) (SR.eig k)

/-- **SA-COMP-1 — the composite's spectrum is the sumset, and the
spectral-sum action composes.** For every cutoff `f` and scale
`Λ`, the spectral-sum action of the composite, evaluated on the
tensored spectral list of §6.2, is the triple sum of `f` over the
sumset of the factor-square eigenvalue lists — the action of the
composite assembled from factor spectral data by addition alone.
(The identity is false for a generic operator on the composite:
it holds because 1b's anchor makes `D²` a Kronecker sum.) -/
theorem spectral_action_composition (F₇ : FactorOp 7)
    (F₄ : FactorOp 4) (F_R : FactorOpR)
    (S₇ : SpectralList (Fin 7 → ℂ) (Fin 14) (F₇.D ^ 2)) (S₄ : SpectralList (Fin 4 → ℂ) (Fin 8) (F₄.D ^ 2))
    (SR : SpectralList Minkowski (Fin 4) (F_R.D ^ 2)) (f : ℝ → ℝ) (Λ : ℝ) :
    specSumIdx (SpectralList.tensorQ F₇ F₄ F_R S₇ S₄ SR).e f Λ
      = ∑ i, ∑ j, ∑ k,
        f ((S₇.e i + S₄.e j + SR.e k) / Λ ^ 2) := by
  unfold specSumIdx
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rfl

/-- SA-COMP-1 at the multiset level: the composite's eigenvalue
multiset is the sumset multiset of the factor lists — the image
of the product multiset of the three index multisets under
addition of the three coordinates. -/
theorem eigenMultiset_tensorQ (F₇ : FactorOp 7) (F₄ : FactorOp 4)
    (F_R : FactorOpR) (S₇ : SpectralList (Fin 7 → ℂ) (Fin 14) (F₇.D ^ 2))
    (S₄ : SpectralList (Fin 4 → ℂ) (Fin 8) (F₄.D ^ 2)) (SR : SpectralList Minkowski (Fin 4) (F_R.D ^ 2)) :
    (SpectralList.tensorQ F₇ F₄ F_R S₇ S₄ SR).eigenMultiset
      = ((Finset.univ.val).product
          ((Finset.univ.val).product Finset.univ.val)).map
        (fun p : Fin 14 × Fin 8 × Fin 4 =>
          S₇.e p.1 + S₄.e p.2.1 + SR.e p.2.2) := by
  unfold SpectralList.eigenMultiset
  show Multiset.map (specComp S₇.e S₄.e SR.e)
      (Finset.univ : Finset (Fin 14 × Fin 8 × Fin 4)).val = _
  rw [← Finset.univ_product_univ, Finset.product_val,
    ← Finset.univ_product_univ, Finset.product_val]
  rfl

/-! ### §6.3. SA-COMP-3 — heat-trace factorization -/

/-- A triple sum of a product of separated factors factorizes. -/
theorem sum_triple_mul {α β γ : Type*} [Fintype α] [Fintype β]
    [Fintype γ] (f : α → ℝ) (g : β → ℝ) (h : γ → ℝ) :
    (∑ i, ∑ j, ∑ k, f i * g j * h k)
      = (∑ i, f i) * (∑ j, g j) * (∑ k, h k) := by
  have h1 : ∀ (i : α) (j : β), (∑ k, f i * g j * h k)
      = (f i * g j) * ∑ k, h k := by
    intro i j
    rw [Finset.mul_sum]
  have h2 : ∀ i : α, (∑ j, ∑ k, f i * g j * h k)
      = f i * ((∑ j, g j) * (∑ k, h k)) := by
    intro i
    rw [Finset.sum_congr rfl (fun j _ => h1 i j), ← Finset.sum_mul,
      ← Finset.mul_sum, mul_assoc]
  rw [Finset.sum_congr rfl (fun i _ => h2 i), ← Finset.sum_mul,
    ← mul_assoc]

/-- **SA-COMP-3 — heat-trace factorization.** The composite heat
trace (the spectral-sum form of §3.1 with the heat cutoff
`x ↦ exp (−t·x)` at `Λ = 1`, over the tensored spectral list) is
the PRODUCT of the three factor heat traces:
`exp (−t(λ+μ+ν)) = exp (−tλ) exp (−tμ) exp (−tν)` over the
sumset, then the triple sum factorizes. The exact finite analogue
of heat-kernel multiplicativity — a theorem here, not an
asymptotic. -/
theorem heat_trace_factorization (F₇ : FactorOp 7)
    (F₄ : FactorOp 4) (F_R : FactorOpR)
    (S₇ : SpectralList (Fin 7 → ℂ) (Fin 14) (F₇.D ^ 2)) (S₄ : SpectralList (Fin 4 → ℂ) (Fin 8) (F₄.D ^ 2))
    (SR : SpectralList Minkowski (Fin 4) (F_R.D ^ 2)) (t : ℝ) :
    specSumIdx (SpectralList.tensorQ F₇ F₄ F_R S₇ S₄ SR).e
        (fun x => Real.exp (-t * x)) 1
      = specSum S₇.e (fun x => Real.exp (-t * x)) 1
        * specSum S₄.e (fun x => Real.exp (-t * x)) 1
        * specSum SR.e (fun x => Real.exp (-t * x)) 1 := by
  rw [spectral_action_composition]
  unfold specSum
  have hexp : ∀ i j k, Real.exp
        (-t * ((S₇.e i + S₄.e j + SR.e k) / (1 : ℝ) ^ 2))
      = Real.exp (-t * (S₇.e i / (1 : ℝ) ^ 2))
        * Real.exp (-t * (S₄.e j / (1 : ℝ) ^ 2))
        * Real.exp (-t * (SR.e k / (1 : ℝ) ^ 2)) := by
    intro i j k
    have h : -t * ((S₇.e i + S₄.e j + SR.e k) / (1 : ℝ) ^ 2)
        = (-t * (S₇.e i / (1 : ℝ) ^ 2))
          + (-t * (S₄.e j / (1 : ℝ) ^ 2))
          + (-t * (SR.e k / (1 : ℝ) ^ 2)) := by ring
    rw [h, Real.exp_add, Real.exp_add]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
    (fun j _ => Finset.sum_congr rfl (fun k _ => hexp i j k)))]
  exact sum_triple_mul _ _ _

/-! ### §6.4. The polynomial action — SA-COMP-5 and SA-COMP-4 -/

/-- A polynomial cutoff as a function: `x ↦ ∑ k, c k · x^k` for
coefficients `c : Fin (K+1) → ℝ` at a stated degree `K`. -/
def polyCutoff (K : ℕ) (c : Fin (K + 1) → ℝ) : ℝ → ℝ :=
  fun x => ∑ k : Fin (K + 1), c k * x ^ k.val

/-- **SA-COMP-5 — the two forms agree on polynomial cutoffs.**
For a polynomial cutoff, the spectral-sum form of the action,
evaluated on ANY spectral list of the composite square (any
witness, any indexing), equals the moment form `q7crActionPoly`:
expand the polynomial over the list and use
`tr ((D²)^k) = ∑ i, (e i)^k` term by term. This is what licenses
computing the action from whichever side is cheaper. -/
theorem spectral_sum_eq_actionPoly (F₇ : FactorOp 7)
    (F₄ : FactorOp 4) (F_R : FactorOpR) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (S : SpectralList q7c4r4Composite ι ((diracQ7C4R4 F₇ F₄ F_R) ^ 2))
    (K : ℕ) (c : Fin (K + 1) → ℝ) (Λ : ℝ) :
    specSumIdx S.e (polyCutoff K c) Λ
      = q7crActionPoly F₇ F₄ F_R K c Λ := by
  unfold specSumIdx polyCutoff q7crActionPoly q7crMoment
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [SpectralList.trace_pow_eq_sum S k.val, Finset.sum_div,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_pow]

/-- **SA-COMP-4 — the action composes (corollary of SA-COMP-2).**
The polynomial action of the composite is the same assembly with
every composite moment replaced by SA-COMP-2's trinomial
polynomial in the factor moments: for any polynomial cutoff, the
action is an explicit function of `Λ` and the factor moment
sequences alone, with no 448-dimensional computation anywhere. -/
theorem q7crActionPoly_composition (F₇ : FactorOp 7)
    (F₄ : FactorOp 4) (F_R : FactorOpR) (K : ℕ)
    (c : Fin (K + 1) → ℝ) (Λ : ℝ) :
    q7crActionPoly F₇ F₄ F_R K c Λ
      = ∑ k : Fin (K + 1), c k *
        ((∑ l ∈ Finset.range (k.val + 1),
          ∑ i ∈ Finset.range (l + 1),
          (Nat.choose k.val l * Nat.choose l i : ℝ)
            * q7crMom7 F₇ i * q7crMom4 F₄ (l - i)
            * q7crMomR F_R (k.val - l)) / (Λ ^ 2) ^ k.val) := by
  unfold q7crActionPoly
  apply Finset.sum_congr rfl
  intro k _
  rw [moment_composition]

/-- SA-COMP-4 in spectral-sum dress (SA-COMP-1 + SA-COMP-5 +
SA-COMP-2 chained): the spectral-sum action on the tensored
composite list, for a polynomial cutoff, is the trinomial
assembly of the factor moments. -/
theorem spectral_action_poly_composition (F₇ : FactorOp 7)
    (F₄ : FactorOp 4) (F_R : FactorOpR)
    (S₇ : SpectralList (Fin 7 → ℂ) (Fin 14) (F₇.D ^ 2)) (S₄ : SpectralList (Fin 4 → ℂ) (Fin 8) (F₄.D ^ 2))
    (SR : SpectralList Minkowski (Fin 4) (F_R.D ^ 2)) (K : ℕ)
    (c : Fin (K + 1) → ℝ) (Λ : ℝ) :
    specSumIdx (SpectralList.tensorQ F₇ F₄ F_R S₇ S₄ SR).e
        (polyCutoff K c) Λ
      = ∑ k : Fin (K + 1), c k *
        ((∑ l ∈ Finset.range (k.val + 1),
          ∑ i ∈ Finset.range (l + 1),
          (Nat.choose k.val l * Nat.choose l i : ℝ)
            * q7crMom7 F₇ i * q7crMom4 F₄ (l - i)
            * q7crMomR F_R (k.val - l)) / (Λ ^ 2) ^ k.val) := by
  rw [spectral_sum_eq_actionPoly, q7crActionPoly_composition]

/-! ### §6.5. Production where the pin reaches — and the seam

For the two realified complex factors, diagonalization data is
PRODUCED from the package, via the pin's real spectral theorem.
The seat needs one adapter: the pin has NO `InnerProductSpace ℝ`
instance on the plain function space `Fin n → ℂ` (its inner
product spaces on function spaces live on `PiLp 2` /
`EuclideanSpace`, a different type), so the registered pairing
is installed as a local inner product through the pin's own
`InnerProductSpace.Core` / `InnerProductSpace.ofCore` route
(the GNS / exterior-power pattern): the core's inner is
`factorPair n` on the nose, positive-definite because
`factorPair n x x = ∑ k, ‖x k‖²`. Inside the production the
spectral APIs of `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`
then apply verbatim. The R⁴ seat is not reached — see §6's
header for the exact mismatch (K-SA-3). -/

/-- The registered real pairing of a complex factor, packaged as
an inner-product core: `factorPair n` is a positive-definite
real inner product on `Fin n → ℂ`. -/
@[instance_reducible]
noncomputable def factorInnerCore (n : ℕ) :
    InnerProductSpace.Core ℝ (Fin n → ℂ) where
  inner := factorPair n
  conj_inner_symm := by
    intro x y
    simp [factorPair_symm]
  re_inner_nonneg := by
    intro x
    show 0 ≤ factorPair n x x
    have h : factorPair n x x = ∑ k, ‖x k‖ ^ 2 := by
      unfold factorPair cplxPair
      simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    rw [h]
    exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
  definite := by
    intro x hx
    have h : factorPair n x x = ∑ k, ‖x k‖ ^ 2 := by
      unfold factorPair cplxPair
      simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    rw [h] at hx
    have hk := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => sq_nonneg (‖x k‖))).mp hx
    funext k
    have h2 := hk k (Finset.mem_univ k)
    simp at h2
    exact h2
  add_left := factorPair_add_left n
  smul_left := by
    intro x y r
    show factorPair n (r • x) y = _
    rw [factorPair_smul_left]
    simp [smul_eq_mul]

/-- A complex factor package's square is symmetric for the
registered pairing (its self-adjointness, applied twice). This
is the symmetry the spectral theorem consumes, stated at the
pairing seat where the package carries it. -/
theorem factorSq_factorPair_symmetric {n : ℕ} (F : FactorOp n)
    (x y : Fin n → ℂ) :
    factorPair n ((F.D ^ 2) x) y = factorPair n x ((F.D ^ 2) y) := by
  rw [pow_two, Module.End.mul_apply, Module.End.mul_apply,
    F.D_selfadj, F.D_selfadj]

/-- **Production, at a complex factor.** The spectral list of a
complex factor package's square, produced from the package by
the pin's spectral theorem
(`LinearMap.IsSymmetric.eigenvectorBasis` /
`LinearMap.IsSymmetric.eigenvalues` of the Spectrum file),
at a stated real dimension `m` with its finrank certificate.
The norm and inner product of the spectral theorem are the
locally installed core instances of `factorInnerCore` (the
pin has no `InnerProductSpace ℝ` instance on the plain
function space `Fin n → ℂ`); the produced data — eigenvalue
function, basis, eigenvector law — mention no norm and are
ordinary spectral-list data for the rest of this section. -/
noncomputable def spectralList_of_factorSq {n m : ℕ}
    (F : FactorOp n) (hn : Module.finrank ℝ (Fin n → ℂ) = m) :
    SpectralList (Fin n → ℂ) (Fin m) (F.D ^ 2) := by
  letI : InnerProductSpace.Core ℝ (Fin n → ℂ) := factorInnerCore n
  letI : SeminormedAddCommGroup (Fin n → ℂ) :=
    InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)
  letI : NormedAddCommGroup (Fin n → ℂ) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  letI : InnerProductSpace ℝ (Fin n → ℂ) :=
    InnerProductSpace.ofCore (𝕜 := ℝ) (F := Fin n → ℂ)
      (inferInstance : PreInnerProductSpace.Core ℝ (Fin n → ℂ))
  have hsym : LinearMap.IsSymmetric (F.D ^ 2) :=
    factorSq_factorPair_symmetric F
  exact { e := hsym.eigenvalues hn
          b := (hsym.eigenvectorBasis hn).toBasis
          eig := by
            intro i
            exact hsym.apply_eigenvectorBasis hn i }

/-- **Production assembled as far as the pin reaches.** With the
two complex factors' lists produced in-house
(`spectralList_of_factorSq` at the registered dimensions 14 and
8), SA-COMP-1's composite list needs only the R⁴ list supplied:
the tensored list at the produced Q⁷/C⁴ witnesses and any
supplied R⁴ witness. This is the exact boundary of K-SA-3 at
this seat. -/
theorem spectral_action_composition_produced (F₇ : FactorOp 7)
    (F₄ : FactorOp 4) (F_R : FactorOpR)
    (SR : SpectralList Minkowski (Fin 4) (F_R.D ^ 2)) (f : ℝ → ℝ) (Λ : ℝ) :
    specSumIdx (SpectralList.tensorQ F₇ F₄ F_R
        (spectralList_of_factorSq F₇ finrank_q7_factor)
        (spectralList_of_factorSq F₄ finrank_c4_factor)
        SR).e f Λ
      = ∑ i, ∑ j, ∑ k,
        f (((spectralList_of_factorSq F₇ finrank_q7_factor).e i
          + (spectralList_of_factorSq F₄ finrank_c4_factor).e j
          + SR.e k) / Λ ^ 2) :=
  spectral_action_composition F₇ F₄ F_R _ _ SR f Λ

/-! ## §7. Q7CR-SA2 — the instantiated evaluation at Q7CR-2's seat

The instantiated evaluation (scoping memo §4, brick Q7CR-SA2):
SA0/SA1's composition machinery evaluated AT Q7CR-2's chosen
seat — the factor packages `factorQ7` (Q⁷ CHOSEN diagonal
`a₇ = (3, −3, 2, −2, 1, −1, 0)`), `factorC4` (centered C⁴ ladder
data `d₄ = (−3/8, −1/8, 1/8, 3/8)`) and `factorR` (R⁴ CHOSEN
diagonal `r_R = (0, 2, −2, 0)`) of `ThetLogos.Q7C4R4Spectrum`,
whose certified factor-square eigenvalue functions are `s₇`
(`Fin 14 → ℝ`), `s₄` (`Fin 8 → ℝ`) and `s_R` (`Fin 4 → ℝ`), and
whose composite eigenvalue multiset `spectrumQ7CR2` carries the
proved anchors `spectrumQ7CR2_card` (`448`),
`spectrumQ7CR2_sum` (`2723`) and `spectrumQ7CR2_sq_sum`
(`1518111 / 64`). No 448-dimensional trace is computed here:
the composition theorems are the computation (memo §4) — the
factor moments are read off the factor spectral lists (§7.1–7.2)
and the composite moments are assembled from them by SA0's
`moment_composition` in its printed forms (§5), then checked
numeral-for-numeral against Q7CR-2's multiset anchors (§7.3).

**Inputs ledger, §7 instance (memo §6 discipline).** The seat's
inputs are exactly Q7CR-2's labeled choices named above (the
three factor packages, with their diagonals and gradings), the
cutoff coefficients and the scale `Λ` stated in each §7.4
statement. Nothing else enters: no measured number, no
curvature or manifold data, no Seeley–DeWitt prefactor.

**K-SA-3 seam, inherited and stated.** §6.5's production reaches
the two complex factors through the pin's spectral theorem; the
R⁴ factor's list is NOT produced that way (its package
self-adjointness is for the indefinite `minkowskiInner`). At
this instantiated seat the factor lists are DISCHARGED from
Q7CR-2's certified forms (§7.1): the Q⁷/C⁴ lists are Q7CR-2's
explicit real site eigenbases (`basisC`) reindexed to the
registered `Fin 14` / `Fin 8` lists, and the R⁴ list is consumed
AS SUPPLIED DATA — Q7CR-2's explicit site eigenbasis
(`Pi.basisFun ℝ (Fin 4)`, `factorR_basis_eigen`) with eigenvalue
function `s_R`. The evaluation below is of the instantiated
composite whose factor lists are Q7CR-2's registered data, in
exactly that form; no §6.5-style production of the R⁴ list from
its package is asserted or used.

**Fences (standing SA-line discipline, restated at this seat).**
The action here is NUMERICAL (spectral sums / moments) — never
an operator `f (D²)`. The finite moments `448 / 2723 /
1518111 / 64` are coefficient-grade finite data attached to the
chosen seat: they are NEVER Seeley–DeWitt coefficients or
gravity terms, and no curvature slot exists in this object.
Dial 1 is unmoved by construction (K-SA-4: any coincidence of
an output with a measured value is a new-entry matter, not a
claim of this line). The bounded-commutator criterion is
VACUOUS in finite dimension; the testable content here is the
spectrum and the trace-level consequences of `D²`. This line
is NOT a gauntlet item: no bearing on the meta-kill, the
trifecta, or the C⁴ leg, in either direction. NO CLAIM; dials
0/4. The Python companion of this section is registered as
BR1-014 in `whitepaper/cross-check-registry.md`. -/

/-! ### §7.1. The seat's spectral lists, discharged from Q7CR-2 -/

/-- **The Q⁷ seat spectral list**: Q7CR-2's explicit real site
eigenbasis `basisC 7` (eigenvectors of `factorQ7.D²` by
`factorQ7_basisC_eigen`), reindexed along `finProdFinEquiv` to
the registered index `Fin 14`, with eigenvalue function Q7CR-2's
`s₇`. -/
noncomputable def spectralListQ7Seat :
    SpectralList (Fin 7 → ℂ) (Fin 14) (factorQ7.D ^ 2) where
  e := s₇
  b := (basisC 7).reindex (finProdFinEquiv (m := 7) (n := 2))
  eig := by
    intro i
    simp only [Module.Basis.reindex_apply]
    exact factorQ7_basisC_eigen _ _

/-- **The C⁴ seat spectral list**: Q7CR-2's explicit real site
eigenbasis `basisC 4` (eigenvectors of `factorC4.D²` by
`factorC4_basisC_eigen`), reindexed along `finProdFinEquiv` to
the registered index `Fin 8`, with eigenvalue function Q7CR-2's
`s₄`. -/
noncomputable def spectralListC4Seat :
    SpectralList (Fin 4 → ℂ) (Fin 8) (factorC4.D ^ 2) where
  e := s₄
  b := (basisC 4).reindex (finProdFinEquiv (m := 4) (n := 2))
  eig := by
    intro i
    simp only [Module.Basis.reindex_apply]
    exact factorC4_basisC_eigen _ _

/-- **The R⁴ seat spectral list, consumed as supplied data**
(K-SA-3 inherited, see the §7 header): Q7CR-2's explicit site
eigenbasis `Pi.basisFun ℝ (Fin 4)` (eigenvectors of
`factorR.D²` by `factorR_basis_eigen`), with eigenvalue
function Q7CR-2's `s_R`. This list is Q7CR-2's registered data,
not a §6.5 production from the R⁴ package. -/
noncomputable def spectralListRSeat :
    SpectralList Minkowski (Fin 4) (factorR.D ^ 2) where
  e := s_R
  b := Pi.basisFun ℝ (Fin 4)
  eig := fun m => factorR_basis_eigen m

/-- **The composite seat spectral list in tensored form**
(SA-COMP-1's packaging at the seat): the tensoring, along
§6.2, of the three discharged factor lists of §7.1. -/
noncomputable def spectralListSeat :
    SpectralList q7c4r4Composite (Fin 14 × Fin 8 × Fin 4)
      ((diracQ7C4R4 factorQ7 factorC4 factorR) ^ 2) :=
  SpectralList.tensorQ factorQ7 factorC4 factorR
    spectralListQ7Seat spectralListC4Seat spectralListRSeat

/-- **The composite seat spectral list in Q7CR-2's direct
form**: Q7CR-2's composite real eigenbasis `basisComp` with
eigenvalue function `eigComp` (its eigenbasis theorem
`dirac_sq_basisComp_eig`). Its eigenvalue multiset is
`spectrumQ7CR2` on the nose. -/
noncomputable def spectralListCompSeat :
    SpectralList q7c4r4Composite compIndex
      ((diracQ7C4R4 factorQ7 factorC4 factorR) ^ 2) where
  e := eigComp
  b := basisComp
  eig := dirac_sq_basisComp_eig

/-! ### §7.2. The factor moments at the seat

Read off the §7.1 lists by `SpectralList.trace_pow_eq_sum`:
`tr ((D²)^p) = ∑ i, (e i)^p`, with the sums evaluated by
Q7CR-2's factor anchors (`sum_s₇`, `sum_s₇_sq`, `sum_s₄`,
`sum_s₄_sq`, `sum_s_R`, `sum_s_R_sq`). The power-zero values
are §3's dimension counts, restated at the seat. -/

/-- Seat Q⁷ factor moment, power 0: `a 0 = 14`. -/
theorem seat_mom7_zero : q7crMom7 factorQ7 0 = 14 :=
  q7crMom7_zero factorQ7

/-- Seat Q⁷ factor moment, power 1: `a 1 = 56`. -/
theorem seat_mom7_one : q7crMom7 factorQ7 1 = 56 := by
  unfold q7crMom7
  rw [SpectralList.trace_pow_eq_sum spectralListQ7Seat 1]
  simp only [pow_one]
  exact sum_s₇

/-- Seat Q⁷ factor moment, power 2: `a 2 = 392`. -/
theorem seat_mom7_two : q7crMom7 factorQ7 2 = 392 := by
  unfold q7crMom7
  rw [SpectralList.trace_pow_eq_sum spectralListQ7Seat 2]
  exact sum_s₇_sq

/-- Seat C⁴ factor moment, power 0: `b 0 = 8`. -/
theorem seat_mom4_zero : q7crMom4 factorC4 0 = 8 :=
  q7crMom4_zero factorC4

/-- Seat C⁴ factor moment, power 1: `b 1 = 5 / 8`. -/
theorem seat_mom4_one : q7crMom4 factorC4 1 = 5 / 8 := by
  unfold q7crMom4
  rw [SpectralList.trace_pow_eq_sum spectralListC4Seat 1]
  simp only [pow_one]
  exact sum_s₄

/-- Seat C⁴ factor moment, power 2: `b 2 = 41 / 512`. -/
theorem seat_mom4_two : q7crMom4 factorC4 2 = 41 / 512 := by
  unfold q7crMom4
  rw [SpectralList.trace_pow_eq_sum spectralListC4Seat 2]
  exact sum_s₄_sq

/-- Seat R⁴ factor moment, power 0: `c 0 = 4`. -/
theorem seat_momR_zero : q7crMomR factorR 0 = 4 :=
  q7crMomR_zero factorR

/-- Seat R⁴ factor moment, power 1: `c 1 = 8`. -/
theorem seat_momR_one : q7crMomR factorR 1 = 8 := by
  unfold q7crMomR
  rw [SpectralList.trace_pow_eq_sum spectralListRSeat 1]
  simp only [pow_one]
  exact sum_s_R

/-- Seat R⁴ factor moment, power 2: `c 2 = 32`. -/
theorem seat_momR_two : q7crMomR factorR 2 = 32 := by
  unfold q7crMomR
  rw [SpectralList.trace_pow_eq_sum spectralListRSeat 2]
  exact sum_s_R_sq

/-! ### §7.3. The composite moments at the seat

Assembled from the §7.2 factor moments by SA0's
`moment_composition`, in the printed forms of §5
(`q7crMoment_zero`, `moment_one`, `moment_two`) — the
composition theorems are the computation — and then tied
numeral-for-numeral to Q7CR-2's proved multiset anchors on
`spectrumQ7CR2`. These are the spectral-action values
`M 0 / M 1 / M 2` at the seat: traces of `(D²)^k` for the
instantiated composite, as spectral sums over its certified
spectrum. Coefficient-grade finite data only — never
Seeley–DeWitt coefficients or gravity terms (see §7 header). -/

/-- **Seat composite moment `M 0 = 448`** — the composite real
dimension, as a spectral-action value. -/
theorem seat_M0 :
    q7crMoment factorQ7 factorC4 factorR 0 = 448 :=
  q7crMoment_zero factorQ7 factorC4 factorR

/-- **Seat composite moment `M 1 = 2723`**, assembled by
SA-COMP-2's printed first form from the §7.2 factor moments:
`32 · 56 + 56 · (5 / 8) + 112 · 8 = 2723`. -/
theorem seat_M1 :
    q7crMoment factorQ7 factorC4 factorR 1 = 2723 := by
  rw [moment_one, seat_mom7_one, seat_mom4_one, seat_momR_one]
  norm_num

/-- **Seat composite moment `M 2 = 1518111 / 64`**, assembled
by SA-COMP-2's printed second form from the §7.2 factor
moments. -/
theorem seat_M2 :
    q7crMoment factorQ7 factorC4 factorR 2 = 1518111 / 64 := by
  rw [moment_two, seat_mom7_one, seat_mom4_one, seat_momR_one,
    seat_mom7_two, seat_mom4_two, seat_momR_two]
  norm_num

/-- The seat's `M 0` is Q7CR-2's multiset anchor
`spectrumQ7CR2_card`, routed through §7.1's packaging: the
spectral sum of the constant `1` over the seat's spectrum. -/
theorem seat_M0_eq_card :
    q7crMoment factorQ7 factorC4 factorR 0
      = spectrumQ7CR2.card := by
  rw [seat_M0, spectrumQ7CR2_card]
  norm_num

/-- The seat's `M 1` is Q7CR-2's multiset anchor
`spectrumQ7CR2_sum`: the trace of the instantiated `D²` is the
sum of its certified eigenvalue multiset. -/
theorem seat_M1_eq_sum :
    q7crMoment factorQ7 factorC4 factorR 1
      = spectrumQ7CR2.sum := by
  rw [seat_M1, spectrumQ7CR2_sum]

/-- The seat's `M 2` is Q7CR-2's multiset anchor
`spectrumQ7CR2_sq_sum`: the trace of the instantiated `D⁴` is
the sum of the squares of its certified eigenvalue multiset. -/
theorem seat_M2_eq_sq_sum :
    q7crMoment factorQ7 factorC4 factorR 2
      = (spectrumQ7CR2.map fun v => v ^ 2).sum := by
  rw [seat_M2, spectrumQ7CR2_sq_sum]

/-! ### §7.4. Polynomial-cutoff evaluations at the seat

SA-COMP-4 instantiated (`spectral_action_poly_composition` at
the §7.1 tensored list, with the seat's registered factor
moment functions), and the first three cutoffs evaluated
numeral-for-numeral: the polynomial cutoffs `f = x⁰`, `f = x¹`,
`f = x²` as coefficient data, in both the moment form
(`q7crActionPoly`) and the spectral-sum form (`specSumIdx` on
the tensored list, the two forms agreeing by SA-COMP-5). The
`x¹` and `x²` values carry their exact `Λ`-dependence on the
face: `2723 / Λ²` and `(1518111 / 64) / (Λ²)²`. -/

/-- **SA-COMP-4 at the seat.** For every polynomial cutoff, the
spectral-sum action on the tensored seat list is the trinomial
assembly of the seat's factor moments. -/
theorem spectral_action_poly_composition_seat (K : ℕ)
    (c : Fin (K + 1) → ℝ) (Λ : ℝ) :
    specSumIdx spectralListSeat.e (polyCutoff K c) Λ
      = ∑ k : Fin (K + 1), c k *
        ((∑ l ∈ Finset.range (k.val + 1),
          ∑ i ∈ Finset.range (l + 1),
          (Nat.choose k.val l * Nat.choose l i : ℝ)
            * q7crMom7 factorQ7 i * q7crMom4 factorC4 (l - i)
            * q7crMomR factorR (k.val - l)) / (Λ ^ 2) ^ k.val) :=
  spectral_action_poly_composition factorQ7 factorC4 factorR
    spectralListQ7Seat spectralListC4Seat spectralListRSeat K c Λ

/-- The `x⁰` cutoff, as coefficient data at degree `0`, is the
constant function `1`. -/
theorem polyCutoff_seat_x0 :
    polyCutoff 0 (fun _ => (1 : ℝ)) = fun _ => 1 := by
  funext x
  simp [polyCutoff]

/-- The `x¹` cutoff, as coefficient data at degree `1`
(`c k = k`), is the identity function. -/
theorem polyCutoff_seat_x1 :
    polyCutoff 1 (fun k : Fin 2 => (k.val : ℝ)) = fun x => x := by
  funext x
  simp [polyCutoff, Fin.sum_univ_two]

/-- The `x²` cutoff, as coefficient data at degree `2`
(`c k = 1` exactly at `k = 2`), is the squaring function. -/
theorem polyCutoff_seat_x2 :
    polyCutoff 2 (fun k : Fin 3 => if k.val = 2 then (1 : ℝ) else 0)
      = fun x => x ^ 2 := by
  funext x
  simp [polyCutoff, Fin.sum_univ_three]

/-- **Polynomial action at the seat, `f = x⁰`:** the moment
form is `M 0 = 448`, at every scale `Λ`. -/
theorem seat_action_x0 (Λ : ℝ) :
    q7crActionPoly factorQ7 factorC4 factorR 0 (fun _ => (1 : ℝ)) Λ
      = 448 := by
  unfold q7crActionPoly
  rw [Fin.sum_univ_one]
  simp [seat_M0]

/-- **Polynomial action at the seat, `f = x¹`:** the moment
form is `M 1 / Λ² = 2723 / Λ²`. -/
theorem seat_action_x1 (Λ : ℝ) :
    q7crActionPoly factorQ7 factorC4 factorR 1
        (fun k : Fin 2 => (k.val : ℝ)) Λ
      = 2723 / Λ ^ 2 := by
  unfold q7crActionPoly
  rw [Fin.sum_univ_two]
  simp [seat_M1]

/-- **Polynomial action at the seat, `f = x²`:** the moment
form is `M 2 / (Λ²)² = (1518111 / 64) / (Λ²)²`. -/
theorem seat_action_x2 (Λ : ℝ) :
    q7crActionPoly factorQ7 factorC4 factorR 2
        (fun k : Fin 3 => if k.val = 2 then (1 : ℝ) else 0) Λ
      = (1518111 / 64) / (Λ ^ 2) ^ 2 := by
  unfold q7crActionPoly
  rw [Fin.sum_univ_three]
  simp [seat_M2]

/-- **Spectral-sum action at the seat, `f = x⁰`:** on the
tensored seat list, the spectral-sum form agrees with the
moment form (SA-COMP-5) at the value `448`. -/
theorem seat_specSum_x0 (Λ : ℝ) :
    specSumIdx spectralListSeat.e
        (polyCutoff 0 (fun _ => (1 : ℝ))) Λ = 448 :=
  (spectral_sum_eq_actionPoly factorQ7 factorC4 factorR
    spectralListSeat 0 (fun _ => (1 : ℝ)) Λ).trans (seat_action_x0 Λ)

/-- **Spectral-sum action at the seat, `f = x¹`:** the
spectral-sum form agrees with the moment form at the value
`2723 / Λ²`. -/
theorem seat_specSum_x1 (Λ : ℝ) :
    specSumIdx spectralListSeat.e
        (polyCutoff 1 (fun k : Fin 2 => (k.val : ℝ))) Λ
      = 2723 / Λ ^ 2 :=
  (spectral_sum_eq_actionPoly factorQ7 factorC4 factorR
    spectralListSeat 1 (fun k : Fin 2 => (k.val : ℝ)) Λ).trans
    (seat_action_x1 Λ)

/-- **Spectral-sum action at the seat, `f = x²`:** the
spectral-sum form agrees with the moment form at the value
`(1518111 / 64) / (Λ²)²`. -/
theorem seat_specSum_x2 (Λ : ℝ) :
    specSumIdx spectralListSeat.e
        (polyCutoff 2
          (fun k : Fin 3 => if k.val = 2 then (1 : ℝ) else 0)) Λ
      = (1518111 / 64) / (Λ ^ 2) ^ 2 :=
  (spectral_sum_eq_actionPoly factorQ7 factorC4 factorR
    spectralListSeat 2
      (fun k : Fin 3 => if k.val = 2 then (1 : ℝ) else 0) Λ).trans
    (seat_action_x2 Λ)

/-! ### §7.5. The heat trace at the seat (SA-COMP-3 instantiated)

SA-COMP-3's factorization, instantiated at the §7.1 lists: the
composite seat's heat trace is the product of the three factor
heat traces, each evaluated on its registered eigenvalue
function (`s₇`, `s₄`, `s_R`). This is a factorization statement
about the seat's spectral sums (the heat cutoff is a chosen
one-parameter family, memo §6 item 1); it is not an asymptotic
expansion and carries no coefficient reading. The K-SA-3 seam
of the §7 header applies verbatim: the R⁴ factor trace is the
trace over the supplied R⁴ list of §7.1. -/

/-- **Heat-trace factorization at the seat.** The instantiated
composite's heat trace (spectral-sum form, heat cutoff
`x ↦ exp (−t·x)` at `Λ = 1`, over the tensored seat list) is
the product of the three factor heat traces at the seat. -/
theorem heat_trace_factorization_seat (t : ℝ) :
    specSumIdx spectralListSeat.e (fun x => Real.exp (-t * x)) 1
      = specSum s₇ (fun x => Real.exp (-t * x)) 1
        * specSum s₄ (fun x => Real.exp (-t * x)) 1
        * specSum s_R (fun x => Real.exp (-t * x)) 1 :=
  heat_trace_factorization factorQ7 factorC4 factorR
    spectralListQ7Seat spectralListC4Seat spectralListRSeat t

end ThetLogos
