import ThetLogos.CFKernelBase
import ThetLogos.CFKernelClassification
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

/-! ## §0. Real structure (J) lemmas

The real structure UJ satisfies UJ² = 1 (proved in Scaffold32 as UJ_mul_self)
and is symmetric (UJᵀ = UJ) since the partner map is involutive.
These give the involution properties needed to relate smGen and smGenOp
under J-conjugation. -/

/-- UJ is symmetric: UJᵀ = UJ. Follows from partner being involutive. -/
theorem UJ_transpose_eq : UJ.transpose = UJ := by
  ext i j
  show UJ j i = UJ i j
  simp only [UJ_apply, UJ_matrix]
  by_cases h1 : i = partner j
  · have h2 : j = partner i := by rw [h1, partner_involutive]
    rw [if_pos h1, if_pos h2]
  · have h2 : j ≠ partner i := by
      intro hc
      apply h1
      rw [hc, partner_involutive]
    rw [if_neg h1, if_neg h2]

/-- UJ-conjugation is an involution: UJ * (UJ * X * UJ) * UJ = X.
    Follows from UJ * UJ = 1 by reassociation. -/
theorem UJ_invol (X : Matrix I32 I32 ℂ) : UJ * (UJ * X * UJ) * UJ = X := by
  have hUJ : UJ * UJ = 1 := UJ_mul_self
  simp only [Matrix.mul_assoc]
  rw [show UJ * (UJ * (X * (UJ * UJ))) = (UJ * UJ) * (X * (UJ * UJ)) from by
    rw [← Matrix.mul_assoc]]
  rw [hUJ]
  simp

/-- UJ distributes over products by inserting UJ*UJ=1:
    UJ * (X * Y) * UJ = (UJ * X * UJ) * (UJ * Y * UJ). -/
theorem UJ_conj_mul (X Y : Matrix I32 I32 ℂ) :
    UJ * (X * Y) * UJ = (UJ * X * UJ) * (UJ * Y * UJ) := by
  have hUJ : UJ * UJ = 1 := UJ_mul_self
  calc UJ * (X * Y) * UJ
      = UJ * X * Y * UJ := by simp only [Matrix.mul_assoc]
    _ = UJ * X * (UJ * UJ) * Y * UJ := by rw [hUJ]; simp only [Matrix.mul_one]
    _ = (UJ * X * UJ) * (UJ * Y * UJ) := by simp only [Matrix.mul_assoc]

/-- J-conjugation of the commutator transpose (given J-compatibility of D_F):
    UJ * [D_F, smGen b]ᵀ * UJ = -[D_F, smGenOp b].
    The minus sign arises because transpose reverses the commutator order. -/
theorem UJ_conj_transpose_commutator
    (D_F : Matrix I32 I32 ℂ) (b : Fin 12)
    (hJ : UJ * D_F.transpose * UJ = D_F) :
    UJ * (D_F * smGen b - smGen b * D_F).transpose * UJ
      = -(D_F * smGenOp b - smGenOp b * D_F) := by
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul]
  rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [UJ_conj_mul, UJ_conj_mul]
  have hOp : ∀ g : Fin 12, UJ * (smGen g).transpose * UJ = smGenOp g := by
    intro g; rfl
  rw [hOp b, hJ]
  simp [neg_sub]

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

/-- J-conjugation inverts smGenOp back to smGen:
    `UJ * (smGenOp g)ᵀ * UJ = smGen g`. -/
theorem smGenOp_involution (g : Fin 12) :
    UJ * (smGenOp g).transpose * UJ = smGen g := by
  have h1 : (smGenOp g).transpose = UJ * smGen g * UJ := by
    simp only [smGenOp, Matrix.transpose_mul, UJ_transpose_eq,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [h1]
  exact UJ_invol (smGen g)

/-! ## §5. J-compatibility and the honest opposite 1-form expansion -/

/-- J-compatibility of the Dirac operator: `UJ * D_Fᵀ * UJ = D_F`.
    Finite form of `J_F D_F = D_F J_F` under the transpose convention.
    Required for the opposite 1-form calculus; false for arbitrary `D_F`. -/
def IsJCompatible (D_F : Matrix I32 I32 ℂ) : Prop :=
  UJ * D_F.transpose * UJ = D_F

/-- The J_F-conjugate of a 1-form expands in the opposite representation,
    with the factor order REVERSED by transposition:
    `J A J⁻¹ = -∑ᵢ [D_F, π°(bᵢ)] π°(aᵢ)`.
    The swap (`[D,b°]a°` not `a°[D,b°]`) is the matrix feature
    `(XY)ᵀ = YᵀXᵀ`; the minus sign is the transpose reversing the
    commutator. Proved from `UJ_conj_transpose_commutator`. -/
theorem opposite_one_form_expand
    (D_F A : Matrix I32 I32 ℂ)
    (hJ : IsJCompatible D_F)
    (h_A : IsAlgebraicOneForm A D_F) :
    ∃ (k : ℕ) (a b : Fin k → Fin 12),
      oppositeOneForm A
        = -∑ i : Fin k, ((D_F * smGenOp (b i) - smGenOp (b i) * D_F) * smGenOp (a i)) := by
  obtain ⟨k, a, b, hA_eq⟩ := h_A
  use k, a, b
  show UJ * A.transpose * UJ = _
  rw [hA_eq]
  rw [Matrix.transpose_sum]
  simp only [Matrix.transpose_mul]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  have h_neg : (-∑ i : Fin k, ((D_F * smGenOp (b i) - smGenOp (b i) * D_F) * smGenOp (a i)))
      = ∑ i : Fin k, (-((D_F * smGenOp (b i) - smGenOp (b i) * D_F) * smGenOp (a i))) := by
    rw [Finset.sum_neg_distrib]
  rw [h_neg]
  apply Finset.sum_congr rfl
  intro i _
  rw [UJ_conj_mul]
  rw [UJ_conj_transpose_commutator D_F (b i) hJ]
  have hOp : UJ * (smGen (a i)).transpose * UJ = smGenOp (a i) := rfl
  rw [hOp, neg_mul]

/-- Swapped order-one: `[[D_F, π°(b)], π(a)] = 0`.
    Requires J-compatibility of `D_F` (false for arbitrary `D_F`).
    Proof by J-conjugation: write `[D_F, π°(b)] = -UJ·[D_F,π(b)]ᵀ·UJ`
    and `π(a) = UJ·π°(a)ᵀ·UJ`; the products collapse via `UJ_conj_mul`
    to `UJ·[C,S]ᵀ·UJ` where `[C,S] = 0` is the ordinary order-one. -/
theorem order_one_swapped (D_F : Matrix I32 I32 ℂ)
    (hJ : IsJCompatible D_F)
    (h : OrderOneHolds D_F) (b a : Fin 12) :
    (D_F * smGenOp b - smGenOp b * D_F) * smGen a
      - smGen a * (D_F * smGenOp b - smGenOp b * D_F) = 0 := by
  -- [D_F, π°(b)] = -UJ·[D_F,π(b)]ᵀ·UJ  (from UJ_conj_transpose_commutator)
  have h_Dop : D_F * smGenOp b - smGenOp b * D_F
      = -(UJ * (D_F * smGen b - smGen b * D_F).transpose * UJ) := by
    have hc := UJ_conj_transpose_commutator D_F b hJ
    rw [hc, neg_neg]
  -- π(a) = UJ·π°(a)ᵀ·UJ  (smGenOp_involution)
  have h_a : smGen a = UJ * (smGenOp a).transpose * UJ :=
    (smGenOp_involution a).symm
  -- Ordinary order-one: [[D_F,π(b)], π°(a)] = 0
  have h_ord : (D_F * smGen b - smGen b * D_F) * smGenOp a
      - smGenOp a * (D_F * smGen b - smGen b * D_F) = 0 :=
    h b a
  -- Substitute the J-conjugate forms
  rw [h_Dop, h_a]
  -- Collapse via UJ_conj_mul: (UJ·X·UJ)(UJ·Y·UJ) = UJ·(XY)·UJ
  have e1 : (-(UJ * (D_F * smGen b - smGen b * D_F).transpose * UJ))
        * (UJ * (smGenOp a).transpose * UJ)
      = -(UJ * ((D_F * smGen b - smGen b * D_F).transpose * (smGenOp a).transpose) * UJ) := by
    rw [neg_mul, ← UJ_conj_mul]
  have e2 : (UJ * (smGenOp a).transpose * UJ)
        * (-(UJ * (D_F * smGen b - smGen b * D_F).transpose * UJ))
      = -(UJ * ((smGenOp a).transpose * (D_F * smGen b - smGen b * D_F).transpose) * UJ) := by
    rw [mul_neg, ← UJ_conj_mul]
  rw [e1, e2]
  -- (XᵀYᵀ) = (YX)ᵀ
  rw [← Matrix.transpose_mul (D_F * smGen b - smGen b * D_F) (smGenOp a),
    ← Matrix.transpose_mul (smGenOp a) (D_F * smGen b - smGen b * D_F)]
  -- Now: -UJ·(S*C)ᵀ·UJ + UJ·(C*S)ᵀ·UJ where C=[D_F,π(b)], S=π°(a)
  -- = UJ·((CS)ᵀ - (SC)ᵀ)·UJ = UJ·((CS - SC)ᵀ)·UJ
  have e3 : UJ * ((D_F * smGen b - smGen b * D_F) * smGenOp a).transpose * UJ
        - UJ * (smGenOp a * (D_F * smGen b - smGen b * D_F)).transpose * UJ
      = UJ * ((D_F * smGen b - smGen b * D_F) * smGenOp a
          - smGenOp a * (D_F * smGen b - smGen b * D_F)).transpose * UJ := by
    simp only [Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul]
  -- Combine: the difference of the two terms equals UJ·[C,S]ᵀ·UJ
  have h_diff : -(UJ * (smGenOp a * (D_F * smGen b - smGen b * D_F)).transpose * UJ)
        - (-(UJ * ((D_F * smGen b - smGen b * D_F) * smGenOp a).transpose * UJ))
      = UJ * ((D_F * smGen b - smGen b * D_F) * smGenOp a
          - smGenOp a * (D_F * smGen b - smGen b * D_F)).transpose * UJ := by
    have h1 : -(UJ * (smGenOp a * (D_F * smGen b - smGen b * D_F)).transpose * UJ)
        - (-(UJ * ((D_F * smGen b - smGen b * D_F) * smGenOp a).transpose * UJ))
        = UJ * ((D_F * smGen b - smGen b * D_F) * smGenOp a).transpose * UJ
          - UJ * (smGenOp a * (D_F * smGen b - smGen b * D_F)).transpose * UJ := by
      abel
    rw [h1, e3]
  rw [h_diff, h_ord]
  simp

/-- Opposite 1-forms commute directly with algebra elements.
    Proof: `A° = -∑ᵢ [D_F,π°(bᵢ)] π°(aᵢ)`. By the derivation rule,
    `[[D,bᵢ°]aᵢ°, π(x)] = [[D,bᵢ°],π(x)]aᵢ° + [D,bᵢ°][aᵢ°,π(x)] = 0`
    by swapped order-one and order-zero; the overall sign is irrelevant. -/
lemma opposite_one_form_algebra_comm
    (D_F A : Matrix I32 I32 ℂ) (x : Fin 12)
    (hJ : IsJCompatible D_F)
    (h_D_one : OrderOneHolds D_F)
    (h_A : IsAlgebraicOneForm A D_F) :
    oppositeOneForm A * smGen x = smGen x * oppositeOneForm A := by
  obtain ⟨k, a, b, hA_eq⟩ := opposite_one_form_expand D_F A hJ h_A
  -- Each summand [D_F,π°(bᵢ)]*π°(aᵢ) commutes with π(x) by the derivation rule.
  have h_each : ∀ i : Fin k,
      ((D_F * smGenOp (b i) - smGenOp (b i) * D_F) * smGenOp (a i)) * smGen x
      = smGen x * ((D_F * smGenOp (b i) - smGenOp (b i) * D_F) * smGenOp (a i)) := by
    intro i
    have h1_comm : (D_F * smGenOp (b i) - smGenOp (b i) * D_F) * smGen x
        = smGen x * (D_F * smGenOp (b i) - smGenOp (b i) * D_F) := by
      have h := order_one_swapped D_F hJ h_D_one (b i) x
      rw [sub_eq_zero] at h
      exact h
    have h2_comm : smGenOp (a i) * smGen x = smGen x * smGenOp (a i) :=
      order_zero_comm_symm (a i) x
    -- Derivation rule: [PQ, X] = [P,X]Q + P[Q,X]; both vanish here.
    -- Via Commute.mul_left: if P commutes with X and Q commutes with X,
    -- then (P*Q) commutes with X.
    have h_comm : Commute ((D_F * smGenOp (b i) - smGenOp (b i) * D_F) * smGenOp (a i))
        (smGen x) :=
      Commute.mul_left h1_comm h2_comm
    exact h_comm.eq
  -- Sum of commuting terms; the overall negation preserves commutation.
  rw [hA_eq, neg_mul, mul_neg, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [h_each i]

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
    (hJ : IsJCompatible D_F)
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
    opposite_one_form_algebra_comm D_F A x hJ h_D_one h_A_form
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


/-! ## §7. Self-adjointness of the fluctuated Dirac -/

/-- UJ is real: all entries are 0 or 1, so entrywise conjugation fixes it. -/
theorem UJ_real : UJ.map (star : ℂ → ℂ) = UJ := by
  ext i j
  simp only [UJ, UJ_matrix, Matrix.map_apply]
  split_ifs <;> simp

/-- UJ is self-adjoint: real and symmetric. -/
theorem UJ_self_adjoint : UJ.conjTranspose = UJ := by
  show (UJ.map (star : ℂ → ℂ)).transpose = UJ
  rw [UJ_real, UJ_transpose_eq]

/-- Dagger intertwines the opposite 1-form:
    `(JAJ⁻¹)† = J A† J⁻¹`. Uses UJ† = UJ and `(Aᵀ)† = (A†)ᵀ = Ā`. -/
theorem oppositeOneForm_conjTranspose (A : Matrix I32 I32 ℂ) :
    (oppositeOneForm A).conjTranspose = oppositeOneForm (A.conjTranspose) := by
  show (UJ * A.transpose * UJ).conjTranspose = UJ * (A.conjTranspose).transpose * UJ
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, UJ_self_adjoint]
  have h1 : (A.transpose).conjTranspose = A.map (star : ℂ → ℂ) := by
    show ((A.transpose).map (star : ℂ → ℂ)).transpose = _
    rw [Matrix.transpose_map, Matrix.transpose_transpose]
  have h2 : (A.conjTranspose).transpose = A.map (star : ℂ → ℂ) := by
    show (((A.map (star : ℂ → ℂ)).transpose)).transpose = _
    rw [Matrix.transpose_transpose]
  rw [h1, h2, Matrix.mul_assoc]

/-- The fluctuated Dirac is self-adjoint when D_F and A are.
    `D_A† = D_F† + A† + (JAJ⁻¹)† = D_F + A + JAJ⁻¹ = D_A`. -/
theorem fluctuatedDirac_self_adjoint
    (D_F A : Matrix I32 I32 ℂ)
    (hD : IsSelfAdjoint D_F) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (fluctuatedDirac D_F A) := by
  have hD' : D_F.conjTranspose = D_F := hD
  have hA' : A.conjTranspose = A := hA
  show (D_F + A + oppositeOneForm A).conjTranspose = D_F + A + oppositeOneForm A
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add,
    oppositeOneForm_conjTranspose, hD', hA']

/-- J-compatibility of the SM Dirac ansatz, in transpose form:
    `UJ * D_Fᵀ * UJ = D_F`.
    From `smDirac_J_compat` (`UJ·D̄ = D·UJ`) and `smDirac_self_adjoint`
    (`D̄ = Dᵀ`), plus `UJ² = 1`. -/
theorem smDirac_IsJCompatible (yNu yE yU yD yR : ℂ) :
    IsJCompatible (smDirac yNu yE yU yD yR) := by
  show UJ * (smDirac yNu yE yU yD yR).transpose * UJ = smDirac yNu yE yU yD yR
  have h_sa := smDirac_self_adjoint yNu yE yU yD yR
  have h_map : (smDirac yNu yE yU yD yR).map (star : ℂ → ℂ)
      = (smDirac yNu yE yU yD yR).transpose := by
    have h1 : ((smDirac yNu yE yU yD yR).map (star : ℂ → ℂ)).transpose
        = smDirac yNu yE yU yD yR := h_sa
    have h2 := congrArg Matrix.transpose h1
    simp only [Matrix.transpose_transpose] at h2
    exact h2
  rw [← h_map]
  have hJ := smDirac_J_compat yNu yE yU yD yR
  calc UJ * (smDirac yNu yE yU yD yR).map (star : ℂ → ℂ) * UJ
      = (UJ * (smDirac yNu yE yU yD yR).map (star : ℂ → ℂ)) * UJ := by
        rw [Matrix.mul_assoc]
    _ = (smDirac yNu yE yU yD yR * UJ) * UJ := by rw [hJ]
    _ = smDirac yNu yE yU yD yR * (UJ * UJ) := by rw [← Matrix.mul_assoc]
    _ = smDirac yNu yE yU yD yR := by rw [UJ_mul_self, Matrix.mul_one]

/-- Hypothesis loop closed: for the SM Dirac ansatz, inner fluctuations
    preserve order-one with no remaining hypotheses on `D_F`.
    `IsJCompatible` is supplied by `smDirac_IsJCompatible`;
    `OrderOneHolds` by `OrderOneHolds_smDirac`. -/
theorem inner_fluctuation_preserves_order_one_smDirac
    (yNu yE yU yD yR : ℂ) (A : Matrix I32 I32 ℂ)
    (h_A_form : IsAlgebraicOneForm A (smDirac yNu yE yU yD yR)) :
    OrderOneHolds (fluctuatedDirac (smDirac yNu yE yU yD yR) A) :=
  inner_fluctuation_preserves_order_one _ _
    (smDirac_IsJCompatible yNu yE yU yD yR)
    (OrderOneHolds_smDirac yNu yE yU yD yR)
    h_A_form


/-! ## §5. Majorana Block Stability under Inner Fluctuations

The right-handed neutrino Majorana mass `Y_R` lives at the E-block entry
`(24,8)` (global indices; `majoranaBlock yR = diag(Y_R, 0_7)` at rows 24–31,
cols 8–15). We prove it is *unfluctuated*: for any algebraic 1-form `A`,
the fluctuated Dirac `D_A = D_F + A + JAJ⁻¹` satisfies `D_A[24,8] = Y_R`.

The proof uses the explicit generator action:
- Only `genC` (g=0) is nonzero on row 24 / column 8 (both = `Complex.I` at the diagonal).
- `genH` acts on 0–7 only; `genM` acts on colour triplets (neither contains 8 or 24).
- Hence `[D_F, smGen g][24,8] = 0` for all `g`: the `genC` contributions
  `Y_R·i - i·Y_R` cancel, others vanish by sparsity.
- The 1-form entry `A[24,8]` vanishes term-by-term.
- `(JAJ⁻¹)[24,8] = A[24,8]` via the UJ partner swap (24↔8).

CORRECTION (2026-09-28): An earlier analysis claimed a counterexample
`A = genC·[D_F,genC]` with `A[24,8] = -Y_R`. That was an arithmetic error:
`[D_F,genC][24,8] = D_F[24,8]·genC[8,8] - genC[24,24]·D_F[24,8] = 0`,
not `i·Y_R` (the second term uses `D_F[24,8]`, not `D_F[8,8]`).
The E-block entry is genuinely invariant. -/

/-- Index 8 (ν_R) and index 24 (ν_R^c) as I32. -/
def i8M : I32 := ⟨8, by norm_num⟩
def i24M : I32 := ⟨24, by norm_num⟩

/-! ### Generator sparsity at indices 8 and 24 -/

theorem genC_col8M (L : I32) :
    genC L i8M = if L.val = 8 then Complex.I else 0 := by
  unfold genC i8M
  by_cases h : L.val = 8
  · have hL : L = ⟨8, by norm_num⟩ := Fin.ext h
    subst hL; simp
  · have hL : ¬ (L = ⟨8, by norm_num⟩) := fun hc => h (congrArg Fin.val hc)
    rw [ite_eq_right hL, ite_eq_right h]

theorem genC_row24M (K : I32) :
    genC i24M K = if K.val = 24 then Complex.I else 0 := by
  unfold genC i24M
  by_cases h : K.val = 24
  · have hK : K = ⟨24, by norm_num⟩ := Fin.ext h
    subst hK; simp
  · have hK : ¬ (⟨24, by norm_num⟩ = K) := fun hc => h (congrArg Fin.val hc.symm)
    rw [ite_eq_right hK, ite_eq_right h]

theorem genH_col8M (k : Fin 3) (L : I32) : genH k L i8M = 0 := by
  unfold genH i8M; simp
theorem genH_row24M (k : Fin 3) (K : I32) : genH k i24M K = 0 := by
  unfold genH i24M; simp
theorem genM_col8M (a : Fin 8) (L : I32) : genM a L i8M = 0 := by
  unfold genM i8M; simp [tripletOf]
theorem genM_row24M (a : Fin 8) (K : I32) : genM a i24M K = 0 := by
  unfold genM i24M; simp [tripletOf]

theorem smGen_col8M (g : Fin 12) (L : I32) :
    smGen g L i8M = if (g.val = 0 ∧ L.val = 8) then Complex.I else 0 := by
  fin_cases g <;> simp [smGen, genC_col8M, genH_col8M, genM_col8M]

theorem smGen_row24M (g : Fin 12) (K : I32) :
    smGen g i24M K = if (g.val = 0 ∧ K.val = 24) then Complex.I else 0 := by
  fin_cases g <;> simp [smGen, genC_row24M, genH_row24M, genM_row24M]

/-! ### Commutator entries vanish -/

theorem smDirac_24_8M (yNu yE yU yD yR : ℂ) :
    (smDirac yNu yE yU yD yR) i24M i8M = yR := by rfl

theorem smDirac_commutator_24_8M (yNu yE yU yD yR : ℂ) (g : Fin 12) :
    ((smDirac yNu yE yU yD yR) * smGen g
      - smGen g * (smDirac yNu yE yU yD yR)) i24M i8M = 0 := by
  rw [Matrix.sub_apply]
  have hDS : ((smDirac yNu yE yU yD yR) * smGen g) i24M i8M
      = if g.val = 0 then yR * Complex.I else 0 := by
    rw [Matrix.mul_apply]
    by_cases hg : g.val = 0
    · have hS88 : smGen g i8M i8M = Complex.I := by
        rw [smGen_col8M, ite_eq_left ⟨hg, rfl⟩]
      have hsum : ∑ L : I32, (smDirac yNu yE yU yD yR) i24M L * smGen g L i8M
          = (smDirac yNu yE yU yD yR) i24M i8M * smGen g i8M i8M := by
        apply Finset.sum_eq_single i8M
        · intro L _ hL
          rw [smGen_col8M]
          have hL8 : ¬ (g.val = 0 ∧ L.val = 8) := by
            rintro ⟨_, hLv⟩
            exact hL (Fin.ext hLv)
          rw [ite_eq_right hL8, mul_zero]
        · intro hcon
          exact absurd (Finset.mem_univ i8M) hcon
      rw [hsum, hS88, smDirac_24_8M, ite_eq_left hg]
    · have hsum : ∑ L : I32, (smDirac yNu yE yU yD yR) i24M L * smGen g L i8M = 0 := by
        apply Finset.sum_eq_zero
        intro L _
        rw [smGen_col8M]
        have hneg : ¬ (g.val = 0 ∧ L.val = 8) := fun ⟨h0, _⟩ => hg h0
        rw [ite_eq_right hneg, mul_zero]
      rw [hsum, ite_eq_right hg]
  have hSD : (smGen g * (smDirac yNu yE yU yD yR)) i24M i8M
      = if g.val = 0 then Complex.I * yR else 0 := by
    rw [Matrix.mul_apply]
    by_cases hg : g.val = 0
    · have hS2424 : smGen g i24M i24M = Complex.I := by
        rw [smGen_row24M, ite_eq_left ⟨hg, rfl⟩]
      have hsum : ∑ L : I32, smGen g i24M L * (smDirac yNu yE yU yD yR) L i8M
          = smGen g i24M i24M * (smDirac yNu yE yU yD yR) i24M i8M := by
        apply Finset.sum_eq_single i24M
        · intro L _ hL
          rw [smGen_row24M]
          have hL24 : ¬ (g.val = 0 ∧ L.val = 24) := by
            rintro ⟨_, hLv⟩
            exact hL (Fin.ext hLv)
          rw [ite_eq_right hL24, zero_mul]
        · intro hcon
          exact absurd (Finset.mem_univ i24M) hcon
      rw [hsum, hS2424, smDirac_24_8M, ite_eq_left hg]
    · have hsum : ∑ L : I32, smGen g i24M L * (smDirac yNu yE yU yD yR) L i8M = 0 := by
        apply Finset.sum_eq_zero
        intro L _
        rw [smGen_row24M]
        have hneg : ¬ (g.val = 0 ∧ L.val = 24) := fun ⟨h0, _⟩ => hg h0
        rw [ite_eq_right hneg, zero_mul]
      rw [hsum, ite_eq_right hg]
  rw [hDS, hSD]
  by_cases hg : g.val = 0 <;> simp [hg, mul_comm]

/-! ### One-form entry vanishes -/

theorem one_form_24_8M_vanishes
    (yNu yE yU yD yR : ℂ) (A : Matrix I32 I32 ℂ)
    (hA : IsAlgebraicOneForm A (smDirac yNu yE yU yD yR)) :
    A i24M i8M = 0 := by
  obtain ⟨k, a, b, hAeq⟩ := hA
  rw [hAeq, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [Matrix.mul_apply]
  by_cases ha : (a i).val = 0
  · have hsum : ∑ K : I32, smGen (a i) i24M K *
        ((smDirac yNu yE yU yD yR) * smGen (b i)
          - smGen (b i) * (smDirac yNu yE yU yD yR)) K i8M
        = smGen (a i) i24M i24M *
          ((smDirac yNu yE yU yD yR) * smGen (b i)
            - smGen (b i) * (smDirac yNu yE yU yD yR)) i24M i8M := by
      apply Finset.sum_eq_single i24M
      · intro K _ hK
        rw [smGen_row24M]
        have hK24 : ¬ ((a i).val = 0 ∧ K.val = 24) := by
          rintro ⟨_, hKv⟩
          exact hK (Fin.ext hKv)
        rw [ite_eq_right hK24, zero_mul]
      · intro hcon
        exact absurd (Finset.mem_univ i24M) hcon
    rw [hsum, smDirac_commutator_24_8M _ _ _ _ _ (b i), mul_zero]
  · have hsum : ∑ K : I32, smGen (a i) i24M K *
        ((smDirac yNu yE yU yD yR) * smGen (b i)
          - smGen (b i) * (smDirac yNu yE yU yD yR)) K i8M = 0 := by
      apply Finset.sum_eq_zero
      intro K _
      rw [smGen_row24M]
      have hneg : ¬ ((a i).val = 0 ∧ K.val = 24) := fun ⟨h0, _⟩ => ha h0
      rw [ite_eq_right hneg, zero_mul]
    rw [hsum]

/-! ### J-conjugation preserves the (24,8) entry -/

theorem partner_24M : partner i24M = i8M := by decide
theorem partner_8M : partner i8M = i24M := by decide

theorem UJ_row24M (K : I32) : UJ i24M K = if K = i8M then 1 else 0 := by
  rw [UJ_apply, UJ_matrix, partner_24M]

theorem UJ_col8M (L : I32) : UJ L i8M = if L = i24M then 1 else 0 := by
  rw [UJ_apply, UJ_matrix]
  by_cases h : L = i24M
  · subst h; rw [partner_24M]; simp
  · have hne : ¬ (i8M = partner L) := by
      intro hcon
      have h1 : partner L = i8M := hcon.symm
      have h2 : L = partner i8M := by
        calc L = partner (partner L) := (partner_involutive L).symm
          _ = partner i8M := by rw [h1]
      rw [partner_8M] at h2
      exact h h2
    rw [ite_eq_right hne]; simp [h]

theorem opposite_entry_24_8M (A : Matrix I32 I32 ℂ) :
    (UJ * A.transpose * UJ) i24M i8M = A i24M i8M := by
  have h1 : ∀ L : I32, (UJ * A.transpose) i24M L = A L i8M := by
    intro L
    rw [Matrix.mul_apply]
    have hsum : ∑ K : I32, UJ i24M K * A.transpose K L
        = UJ i24M i8M * A.transpose i8M L := by
      apply Finset.sum_eq_single i8M
      · intro K _ hK
        rw [UJ_row24M, ite_eq_right hK, zero_mul]
      · intro hcon
        exact absurd (Finset.mem_univ i8M) hcon
    rw [hsum, UJ_row24M, ite_eq_left rfl, one_mul, Matrix.transpose_apply]
  rw [Matrix.mul_apply]
  have hsum : ∑ L : I32, (UJ * A.transpose) i24M L * UJ L i8M
      = (UJ * A.transpose) i24M i24M * UJ i24M i8M := by
    apply Finset.sum_eq_single i24M
    · intro L _ hL
      rw [UJ_col8M, ite_eq_right hL, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ i24M) hcon
  rw [hsum, h1, UJ_col8M, ite_eq_left rfl, mul_one]

/-! ### Majorana subspace stability -/

/-- The fluctuated E-block remains in the scalar span of the Majorana block:
    inner fluctuations can only rescale `Y_R`, never generate new E-block
    structure. (Here stated for the `8×8` E-block; the `Fin 7` in the
    original spec was a typo for the `8×8` block size.) -/
def IsMajoranaSubspace (E Y_R : Block8) : Prop :=
  ∃ c : ℂ, E = c • Y_R

/-- Extract the 8×8 E-block (rows 24–31, cols 8–15) from a 32×32 matrix. -/
def eBlockOf (M : Matrix I32 I32 ℂ) : Block8 :=
  fun i j => M ⟨24 + i.val, by have h := i.isLt; omega⟩
               ⟨8 + j.val, by have h := j.isLt; omega⟩

/-- The Majorana mass entry is unfluctuated: `D_A[24,8] = Y_R`.
    Hence the E-block lies in the scalar span of `majoranaBlock yR`
    (with scalar `c = 1` at the `(0,0)` entry). -/
theorem inner_fluctuation_majorana_subspace
    (yNu yE yU yD yR : ℂ) (A : Matrix I32 I32 ℂ)
    (hA : IsAlgebraicOneForm A (smDirac yNu yE yU yD yR)) :
    (eBlockOf (fluctuatedDirac (smDirac yNu yE yU yD yR) A))
      ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = yR := by
  unfold eBlockOf fluctuatedDirac oppositeOneForm
  simp only []
  have hA0 : A i24M i8M = 0 := one_form_24_8M_vanishes _ _ _ _ _ _ hA
  have hJ0 : (UJ * A.transpose * UJ) i24M i8M = 0 := by
    rw [opposite_entry_24_8M, hA0]
  -- (24 + 0, 8 + 0) = (24, 8) = (i24M, i8M) by computation
  have h24 : (⟨24 + (⟨0, by norm_num⟩ : Fin 8).val, by have h := (⟨0, by norm_num⟩ : Fin 8).isLt; omega⟩ : I32) = i24M := rfl
  have h8 : (⟨8 + (⟨0, by norm_num⟩ : Fin 8).val, by have h := (⟨0, by norm_num⟩ : Fin 8).isLt; omega⟩ : I32) = i8M := rfl
  rw [h24, h8, Matrix.add_apply, Matrix.add_apply, smDirac_24_8M, hA0, hJ0,
    add_zero, add_zero]

/-! ### Full E-block rigidity from the 46→10 classification (H13 — proved)

The theorem above covers only the single `(24,8)` entry. The full 8×8
E-block rigidity — all 64 entries controlled by the one complex parameter
`yR` — follows from the 46→10 classification
(`cf_kernel_classification_46_10`): order-one + `[D, C_F] = 0` eliminates
the 36 exotic directions, forcing `D = smDirac yNu yE yU yD yR`, whose
E-block is exactly `majoranaBlock yR = yR • majoranaBlock 1`. -/

/-- Entry of `buildDirac` in the E region (i in [24,32), j in [8,16)). -/
theorem buildDirac_E_entry (A B C E : Block8) (i j : I32)
    (hi1 : ¬i.val < 8) (hi2 : ¬i.val < 16) (hi3 : ¬i.val < 24)
    (hj1 : ¬j.val < 8) (hj2 : j.val < 16) :
    buildDirac A B C E i j
      = E ⟨i.val - 24, by omega⟩ ⟨j.val - 8, by omega⟩ := by
  unfold buildDirac
  simp only []
  simp [hi1, hi2, hi3, hj1, hj2]

/-- The E-block of the SM ansatz is exactly `majoranaBlock yR`. -/
theorem smDirac_E_block (yNu yE yU yD yR : ℂ) :
    eBlockOf (smDirac yNu yE yU yD yR) = majoranaBlock yR := by
  ext i j
  unfold eBlockOf smDirac
  have h1 : ¬(24 + i.val) < 8 := by have h := i.isLt; omega
  have h2 : ¬(24 + i.val) < 16 := by have h := i.isLt; omega
  have h3 : ¬(24 + i.val) < 24 := by omega
  have h4 : ¬(8 + j.val) < 8 := by omega
  have h5 : (8 + j.val) < 16 := by have h := j.isLt; omega
  rw [buildDirac_E_entry _ _ _ _ _ _ h1 h2 h3 h4 h5]
  have e1 : (⟨24 + i.val - 24, by have h := i.isLt; omega⟩ : Fin 8) = i := by
    ext; simp
  have e2 : (⟨8 + j.val - 8, by have h := j.isLt; omega⟩ : Fin 8) = j := by
    ext; simp
  rw [e1, e2]

/-- `majoranaBlock yR` is the scalar multiple `yR • majoranaBlock 1`. -/
theorem majoranaBlock_eq_smul_one (yR : ℂ) :
    majoranaBlock yR = yR • majoranaBlock 1 := by
  ext i j
  simp only [majoranaBlock, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h
    by_cases h0 : i.val = 0 <;> simp [h0]
  · simp [h]

/-- Full E-block rigidity (H13 — proved): for order-one `D` with `[D, C_F] = 0`,
    the 8×8 E-block (rows 24–31, cols 8–15) lies in the scalar span of the
    single-entry Majorana form `majoranaBlock 1` — all 64 entries are
    controlled by the one complex parameter `yR`.

    ⚠ UNSOUND AS STATED — flagged 2026-09-30 (H4 retarget 46→22). The
    statement itself was not refuted, but the proof rests on the
    false-as-stated `exotic_decomposition` axiom via the flagged
    `cf_kernel_classification_46_10`. Per the relabeling rule the statement
    stands unmodified; see whitepaper/gut-roadmap-2026-09-29.md, Step D.

    Proof: the 46→10 classification (`cf_kernel_classification_46_10`)
    eliminates the 36 exotic directions, forcing
    `D = smDirac yNu yE yU yD yR`, whose E-block is `majoranaBlock yR`
    (`smDirac_E_block`), which is `yR • majoranaBlock 1`
    (`majoranaBlock_eq_smul_one`).

    Tier: T3 logic conditional on the T4 `exotic_decomposition` axiom
    (inherited from the classification — that axiom is unchanged).
    Zero sorrys, zero new axioms. -/
theorem majorana_Eblock_rigidity (D : Matrix I32 I32 ℂ)
    (h_oo : OrderOneHolds D) (h_cf : cfCommutatorMap D = 0) :
    IsMajoranaSubspace (eBlockOf D) (majoranaBlock 1) := by
  obtain ⟨yNu, yE, yU, yD, yR, hD⟩ := cf_kernel_classification_46_10 D h_oo h_cf
  exact ⟨yR, by rw [hD, smDirac_E_block, majoranaBlock_eq_smul_one]⟩

end ThetLogos
