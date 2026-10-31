import Mathlib.Tactic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import ThetLogos.Q7C4R4Assembly

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

end ThetLogos
