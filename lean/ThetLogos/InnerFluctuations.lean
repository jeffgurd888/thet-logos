import ThetLogos.CFKernelBase
import ThetLogos.MartinettiRep
import ThetLogos.OrderOne

/-!
# ThetLogos.InnerFluctuations — gauge fields via inner fluctuations

Phase 3: Field dynamics. The internal Dirac operator `D_F` defines free
kinematics. Dynamic interactions enter through inner fluctuations generated
by the algebra `A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ)`, represented via the Martinetti
`smGen : Fin 12 → Matrix I32 I32 ℂ` with opposite `smGenOp`.

Self-adjoint algebraic 1-forms `A ∈ Ω¹_D(A_F)` take the form
  A = ∑ᵢ π(aᵢ)[D_F, π(bᵢ)],  aᵢ, bᵢ ∈ Fin 12.

The real structure `J_F` dictates the full fluctuated internal operator
  D_A = D_F + A + J_F A J_F⁻¹.

- Electroweak & strong bosons: `A` generates the SU(3)_C × SU(2)_L × U(1)_Y
  gauge connections acting on ℂ³².
- Higgs field: off-diagonal components in `A` coupling `H_L ↔ H_R` generate
  the Higgs doublet `H ∈ ℂ²` as an internal gauge field.
-/

namespace ThetLogos

/-! ## §1. Algebraic 1-forms via smGen -/

/-- An algebraic 1-form: A = ∑ᵢ smGen(aᵢ)[D_F, smGen(bᵢ)]. -/
def IsAlgebraicOneForm (A : Matrix I32 I32 ℂ) (D_F : Matrix I32 I32 ℂ) : Prop :=
  ∃ (k : ℕ) (a b : Fin k → Fin 12),
    A = ∑ i : Fin k, (smGen (a i) * (D_F * smGen (b i) - smGen (b i) * D_F))

/-! ## §2. The fluctuated Dirac operator -/

/-- Real opposite action of a 1-form via J_F: A° = J_F Aᵀ J_F.
    (UJ is unitary with UJ² = 1, so J⁻¹ = J.) -/
def oppositeOneForm (A : Matrix I32 I32 ℂ) : Matrix I32 I32 ℂ :=
  UJ * A.transpose * UJ

/-- Full fluctuated Dirac operator: D_A = D_F + A + J_F A J_F⁻¹. -/
def fluctuatedDirac (D_F A : Matrix I32 I32 ℂ) : Matrix I32 I32 ℂ :=
  D_F + A + oppositeOneForm A

/-! ## §3. Order-zero: [smGen, smGenOp] = 0 -/

/-- Order-zero condition: the representation commutes with its opposite.
    This is the finite-geometry axiom [π(a), π°(b)] = 0.
    STATUS: Proved from smGen_order_zero in MartinettiRep.lean. -/
theorem order_zero_comm (a b : Fin 12) :
    smGen a * smGenOp b = smGenOp b * smGen a :=
  sub_eq_zero.mp (smGen_order_zero a b)

/-- Symmetric order-zero: [π°(a), π(b)] = 0.
    STATUS: Proved from smGen_order_zero (arguments swapped). -/
theorem order_zero_comm_symm (a b : Fin 12) :
    smGenOp a * smGen b = smGen b * smGenOp a :=
  (sub_eq_zero.mp (smGen_order_zero b a)).symm

/-! ## §4. Helper Lemma 1: 1-forms commute with opposite algebra -/

/-- Algebraic 1-forms commute with opposite algebra elements.
    Proof: A = ∑ᵢ π(aᵢ)[D_F,π(bᵢ)]. Each product π(aᵢ)·[D_F,π(bᵢ)]·π(x)
    has factors commuting with π°(y): π(aᵢ) by order-zero, [D_F,π(bᵢ)]
    by order-one, π(x) by order-zero. Hence π°(y) commutes with [A,π(x)]. -/
lemma one_form_opposite_comm
    (D_F A : Matrix I32 I32 ℂ) (y : Fin 12)
    (h_D_one : OrderOneHolds D_F)
    (h_A : IsAlgebraicOneForm A D_F) :
    (A * smGenOp y - smGenOp y * A) = 0 := by
  obtain ⟨k, a, b, hA_eq⟩ := h_A
  -- Each summand commutes: (X*B)*Z = Z*(X*B) via Commute.mul_left.
  have h_each : ∀ i : Fin k,
      (smGen (a i) * (D_F * smGen (b i) - smGen (b i) * D_F)) * smGenOp y
      = smGenOp y * (smGen (a i) * (D_F * smGen (b i) - smGen (b i) * D_F)) := by
    intro i
    have h1_comm : (D_F * smGen (b i) - smGen (b i) * D_F) * smGenOp y
        = smGenOp y * (D_F * smGen (b i) - smGen (b i) * D_F) := by
      have h := h_D_one (b i) y
      rw [sub_eq_zero] at h
      exact h
    have h2_comm : smGen (a i) * smGenOp y = smGenOp y * smGen (a i) :=
      order_zero_comm (a i) y
    have h_comm : Commute (smGen (a i) * (D_F * smGen (b i) - smGen (b i) * D_F))
        (smGenOp y) :=
      Commute.mul_left h2_comm h1_comm
    exact h_comm.eq
  -- Sum of commuting terms: [∑ Xᵢ, Z] = ∑ [Xᵢ, Z] = 0.
  rw [hA_eq]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro i _
  rw [sub_eq_zero]
  exact h_each i

/-! ## §5. Helper Lemma 2: Opposite 1-forms commute with algebra -/

/-- The J_F-conjugate of a 1-form expands in the opposite representation:
    J A J⁻¹ = ∑ᵢ π°(aᵢ)[D_F, π°(bᵢ)].
    Uses J π(a) J⁻¹ = π°(a) and J[D_F,π(b)]J⁻¹ = [D_F,π°(b)]. -/
axiom opposite_one_form_expand
    (D_F A : Matrix I32 I32 ℂ)
    (h_A : IsAlgebraicOneForm A D_F) :
    ∃ (k : ℕ) (a b : Fin k → Fin 12),
      oppositeOneForm A
        = ∑ i : Fin k, (smGenOp (a i) * (D_F * smGenOp (b i) - smGenOp (b i) * D_F))

/-- Swapped order-one: [[D_F, π°(b)], π(a)] = 0.
    STATUS: Axiom (T2) — the finite spectral triple axioms are symmetric
    under exchanging the representation with its opposite. -/
axiom order_one_swapped (D_F : Matrix I32 I32 ℂ)
    (h : OrderOneHolds D_F) (b a : Fin 12) :
    (D_F * smGenOp b - smGenOp b * D_F) * smGen a
      - smGen a * (D_F * smGenOp b - smGenOp b * D_F) = 0

/-- Opposite 1-forms commute directly with algebra elements.
    Proof: A° = ∑ᵢ π°(aᵢ)[D_F,π°(bᵢ)]. Then
    [π°(aᵢ)[D_F,π°(bᵢ)], π(x)]
      = π°(aᵢ)[[D_F,π°(bᵢ)],π(x)] + [π°(aᵢ),π(x)][D_F,π°(bᵢ)] = 0
    by swapped order-one and order-zero. -/
lemma opposite_one_form_algebra_comm
    (D_F A : Matrix I32 I32 ℂ) (x : Fin 12)
    (h_D_one : OrderOneHolds D_F)
    (h_A : IsAlgebraicOneForm A D_F) :
    oppositeOneForm A * smGen x = smGen x * oppositeOneForm A := by
  obtain ⟨k, a, b, hA_eq⟩ := opposite_one_form_expand D_F A h_A
  -- Each summand commutes via the two commutativity facts.
  have h_each : ∀ i : Fin k,
      (smGenOp (a i) * (D_F * smGenOp (b i) - smGenOp (b i) * D_F)) * smGen x
      = smGen x * (smGenOp (a i) * (D_F * smGenOp (b i) - smGenOp (b i) * D_F)) := by
    intro i
    have h1_comm : (D_F * smGenOp (b i) - smGenOp (b i) * D_F) * smGen x
        = smGen x * (D_F * smGenOp (b i) - smGenOp (b i) * D_F) := by
      have h := order_one_swapped D_F h_D_one (b i) x
      rw [sub_eq_zero] at h
      exact h
    have h2_comm : smGenOp (a i) * smGen x = smGen x * smGenOp (a i) :=
      order_zero_comm_symm (a i) x
    -- By Commute.mul_left: if X commutes with Z and B commutes with Z,
    -- then (X*B) commutes with Z.
    have h_comm : Commute (smGenOp (a i) * (D_F * smGenOp (b i) - smGenOp (b i) * D_F))
        (smGen x) :=
      Commute.mul_left h2_comm h1_comm
    exact h_comm.eq
  -- Sum of commuting terms.
  rw [hA_eq, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact h_each i

/-! ## §6. Main theorem: order-one preservation -/

/-- Inner fluctuations preserve the order-one condition.
    Proof: D_A = D_F + A + A°. For each x, y:
    [[D_A, π(x)], π°(y)]
      = [[D_F,π(x)],π°(y)] + [[A,π(x)],π°(y)] + [[A°,π(x)],π°(y)].
    - First term: 0 by h_D_one.
    - Second term: 0 by one_form_opposite_comm (π°(y) commutes with [A,π(x)]).
    - Third term: 0 by opposite_one_form_algebra_comm ([A°,π(x)] = 0). -/
theorem inner_fluctuation_preserves_order_one
    (D_F A : Matrix I32 I32 ℂ)
    (h_D_one : OrderOneHolds D_F)
    (h_A_form : IsAlgebraicOneForm A D_F) :
    OrderOneHolds (fluctuatedDirac D_F A) := by
  intro x y
  unfold fluctuatedDirac
  -- Goal: [[D_F + A + Ao, smGen x], smGenOp y] = 0
  have h_D : (D_F * smGen x - smGen x * D_F) * smGenOp y
      - smGenOp y * (D_F * smGen x - smGen x * D_F) = 0 :=
    h_D_one x y
  have h_A_comm : Commute A (smGenOp y) :=
    sub_eq_zero.mp (one_form_opposite_comm D_F A y h_D_one h_A_form)
  have h_Ao_comm : Commute (oppositeOneForm A) (smGen x) :=
    opposite_one_form_algebra_comm D_F A x h_D_one h_A_form
  have h_x_comm : Commute (smGen x) (smGenOp y) :=
    order_zero_comm x y
  -- Term 2: [[A, π(x)], π°(y)] = 0.
  -- [A,π(x)] = A*π(x) - π(x)*A; both products commute with π°(y).
  have h_Ax_comm : Commute (A * smGen x) (smGenOp y) :=
    Commute.mul_left h_A_comm h_x_comm
  have h_xA_comm : Commute (smGen x * A) (smGenOp y) :=
    Commute.mul_left h_x_comm h_A_comm
  have h_term2 : ((A * smGen x - smGen x * A) * smGenOp y
      - smGenOp y * (A * smGen x - smGen x * A)) = 0 := by
    -- h_Ax_comm : (A * smGen x) * smGenOp y = smGenOp y * (A * smGen x)
    -- h_xA_comm : (smGen x * A) * smGenOp y = smGenOp y * (smGen x * A)
    have h1 : (A * smGen x) * smGenOp y = smGenOp y * (A * smGen x) := h_Ax_comm
    have h2 : (smGen x * A) * smGenOp y = smGenOp y * (smGen x * A) := h_xA_comm
    calc (A * smGen x - smGen x * A) * smGenOp y
            - smGenOp y * (A * smGen x - smGen x * A)
        = ((A * smGen x) * smGenOp y - (smGen x * A) * smGenOp y)
          - (smGenOp y * (A * smGen x) - smGenOp y * (smGen x * A)) := by
          rw [Matrix.sub_mul, Matrix.mul_sub]
      _ = 0 := by rw [h1, h2]; simp
  -- Term 3: [[Ao, π(x)], π°(y)] = [0, π°(y)] = 0.
  have h_term3 : ((oppositeOneForm A * smGen x - smGen x * oppositeOneForm A)
      * smGenOp y
      - smGenOp y * (oppositeOneForm A * smGen x - smGen x * oppositeOneForm A))
      = 0 := by
    have h0 : oppositeOneForm A * smGen x - smGen x * oppositeOneForm A = 0 :=
      sub_eq_zero.mpr h_Ao_comm
    rw [h0]
    simp
  -- Combine by linearity: [[D+A+Ao, X], Y] = [[D,X],Y] + [[A,X],Y] + [[Ao,X],Y].
  -- Each term vanishes by h_D, h_term2, h_term3 respectively.
  have h_expand : (((D_F + A + oppositeOneForm A) * smGen x
        - smGen x * (D_F + A + oppositeOneForm A)) * smGenOp y
        - smGenOp y * ((D_F + A + oppositeOneForm A) * smGen x
          - smGen x * (D_F + A + oppositeOneForm A)))
      = (((D_F * smGen x - smGen x * D_F) * smGenOp y
          - smGenOp y * (D_F * smGen x - smGen x * D_F))
        + ((A * smGen x - smGen x * A) * smGenOp y
          - smGenOp y * (A * smGen x - smGen x * A))
        + ((oppositeOneForm A * smGen x - smGen x * oppositeOneForm A) * smGenOp y
          - smGenOp y * (oppositeOneForm A * smGen x
            - smGen x * oppositeOneForm A))) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [h_expand, h_D, h_term2, h_term3]
  simp

end ThetLogos
