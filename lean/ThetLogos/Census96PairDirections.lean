import ThetLogos.Census96PairSpace
import ThetLogos.Census96GeneratorBridge

/-!
# ThetLogos.Census96PairDirections - C96-3a2: pair directions II

Continuation of C96-3a (lane 2). The frozen interface of C96-3a
(`PairSpace`, `mem_pairSpace_iff`, `pairDir22`, `pairDirSM`,
`pairDirExotic`, `dir88Of`) is imported and untouched; every name
defined here is new.

## What this module does

1. **The non-hermitian engine.** C96-3a's named stall (a): the
   directions `Complex.I • H` where `H` is hermitian and
   J-ANTI-compatible. The J-anticompatible one-generation predicate
   `IsAntiAdm32` is defined below (self-adjoint, grading-odd, and
   `UJ * H.transpose * UJ = -H`), and the engine theorem
   `pairSpace_of_isAntiAdm32` proves, for every such `H` satisfying
   `OrderOneHolds H`, that `Complex.I • H` lies in `PairSpace`:
   all four conditions of `mem_pairSpace_iff` are proved for the
   product. The partner computation is
   `(Complex.I • H).conjTranspose = - (Complex.I • H)` (the product
   is anti-hermitian), so the partner conditions follow from the
   first member's by real negation.

2. **The S-conjugation transport.** The anti directions are not
   built entry-by-entry: conjugation by the diagonal antiparticle
   sign matrix `aRSign` (sign `-1` exactly on the right-antiparticle
   sector `24-31`) fixes every gauge generator and every opposite
   generator (`aRSign_conj_smGen`, `aRSign_conj_smGenOp`, via the
   double-commutator conjugation identity `dcGen_conj`), hence
   preserves the order-one condition; and it sends a hermitian,
   grading-odd, J-compatible pattern matrix whose support joins
   opposite partner twists to a J-anticompatible matrix
   (`isAntiAdm32_aRSign_conj`).

3. **Families (complete).** The SM-like family is completed to
   `pairDirSM18 : Fin 18 -> PairSpace`: indices 0-9 are C96-3a's
   landed `pairDirSM` (`pairDirSM18_SM`), indices 10-17 are the
   non-hermitian partners `Complex.I • (aRSign * X * aRSign)` of the
   eight diagonal SM patterns (`pairDirSM18_anti`). The flipped
   family is `pairDirFlip16 : Fin 16 -> PairSpace`: indices 0-7 are
   the hermitian flipped directions (`pairDirFlip16_herm`), indices
   8-15 their non-hermitian partners (`pairDirFlip16_anti`). The
   remaining exotic directions (42 of the 88) are NOT this module;
   they are C96-3a3.

## Kills and fences (on the face)

- K-C96-1 (armed): a PROVED 89th independent direction, or any
  proved finrank of `PairSpace` different from 88, kills the T4
  note. Nothing here proves any finrank or any independence.
  A stall is a stall, never a kill.
- K-C96-2 (vacuity): every direction named here is an element of
  `PairSpace` with its four coupling conditions proved; no slot
  counting, no zero padding.
- Generations IMPOSED; CKM/PMNS input-only; Q3 OPEN; NO CLAIM.
  The old 46 -> 10 gloss is UNSOUND AS STATED and is not cited.
-/

open Matrix

namespace ThetLogos

/-! ## 1. Auxiliary transport lemmas -/

/-- `star` of the imaginary unit, as a `star` computation:
    `star Complex.I = -Complex.I`. -/
theorem star_I_eq_neg_I : star (Complex.I : ℂ) = -Complex.I :=
  Complex.conj_I

/-- Entrywise conjugation of `Complex.I • M` is
    `(-Complex.I) • entrywiseConj M`. -/
theorem entrywiseConj_smul_I (M : Matrix I32 I32 ℂ) :
    entrywiseConj (Complex.I • M) = (-Complex.I) • entrywiseConj M := by
  ext i j
  have e1 : entrywiseConj (Complex.I • M) i j
      = star (Complex.I * M i j) := rfl
  have e2 : ((-Complex.I) • entrywiseConj M) i j
      = -Complex.I * star (M i j) := rfl
  rw [e1, e2, star_mul, star_I_eq_neg_I, mul_comm]

/-- The conjugate-transpose of `Complex.I • M`:
    `(Complex.I • M).conjTranspose = (-Complex.I) • M.conjTranspose`. -/
theorem conjTranspose_smul_I (M : Matrix I32 I32 ℂ) :
    (Complex.I • M).conjTranspose = (-Complex.I) • M.conjTranspose := by
  rw [Matrix.conjTranspose_smul, star_I_eq_neg_I]

/-- The order-one condition is complex-homogeneous: if `M` is
    order-one, so is `c • M` for a complex scalar `c`. The double
    commutator is complex-linear in `M`. -/
theorem orderOneHolds_smul_complex (c : ℂ) {M : Matrix I32 I32 ℂ}
    (hM : OrderOneHolds M) : OrderOneHolds (c • M) := by
  intro a b
  have e := hM a b
  have hX : (c • M) * smGen a - smGen a * (c • M)
      = c • (M * smGen a - smGen a * M) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  show ((c • M) * smGen a - smGen a * (c • M)) * smGenOp b
    - smGenOp b * ((c • M) * smGen a - smGen a * (c • M)) = 0
  rw [hX, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, e, smul_zero]

/-- The order-one condition is closed under negation. -/
theorem orderOneHolds_neg {M : Matrix I32 I32 ℂ}
    (hM : OrderOneHolds M) : OrderOneHolds (-M) := by
  have h := orderOneHolds_smul_complex (-1 : ℂ) hM
  rwa [neg_one_smul] at h

/-- Block-admissibility is closed under negation (it is a real
    submodule condition, `AdmBlock`). -/
theorem isAdmBlock_neg {M : Matrix I32 I32 ℂ}
    (hM : IsAdmBlock M) : IsAdmBlock (-M) :=
  AdmBlock.neg_mem hM

/-! ## 2. The J-anticompatible predicate and the engine -/

/-- **J-anticompatible one-generation data** (`H-` in the Python
    census's `272 + 240` split of the pair pattern space): `H` is
    self-adjoint, grading-odd, and J-ANTI-compatible in the owned
    transpose form, `UJ * H.transpose * UJ = -H`. Tier T2. -/
def IsAntiAdm32 (H : Matrix I32 I32 ℂ) : Prop :=
  H.conjTranspose = H ∧
  gammaF * H + H * gammaF = 0 ∧
  UJ * H.transpose * UJ = -H

/-- Entry form of J-anticompatibility:
    `H (partner j) (partner i) = - H i j`. -/
theorem jAnti_entry {H : Matrix I32 I32 ℂ}
    (hJ : UJ * H.transpose * UJ = -H) (i j : I32) :
    H (partner j) (partner i) = - H i j := by
  have he := congrFun (congrFun hJ i) j
  rw [UJ_conj_apply, Matrix.transpose_apply, Matrix.neg_apply] at he
  exact he

/-- The product `Complex.I • H` of a J-anticompatible `H` is
    block-admissible. Grading-oddness is complex-linear; the
    entrywise-conj J-condition flips sign twice: conjugation sends
    the scalar `I` to `-I`, and anticompatibility supplies the
    second sign. -/
theorem isAdmBlock_smul_I_of_isAntiAdm32 {H : Matrix I32 I32 ℂ}
    (hA : IsAntiAdm32 H) : IsAdmBlock (Complex.I • H) := by
  obtain ⟨hsa, hgr, hJ⟩ := hA
  refine ⟨?_, ?_⟩
  · have e : gammaF * (Complex.I • H) + (Complex.I • H) * gammaF
        = Complex.I • (gammaF * H + H * gammaF) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
    rw [e, hgr, smul_zero]
  · ext i j
    rw [UJ_mul_apply, mul_UJ_apply, entrywiseConj_smul_I]
    have eL : ((-Complex.I) • entrywiseConj H) (partner i) j
        = -Complex.I * star (H (partner i) j) := rfl
    have eR : (Complex.I • H) i (partner j)
        = Complex.I * H i (partner j) := rfl
    rw [eL, eR]
    have hs : star (H (partner i) j) = H j (partner i) := by
      rw [selfAdjoint_entry H hsa (partner i) j, star_star]
    rw [hs]
    have hj := jAnti_entry hJ i (partner j)
    rw [partner_involutive] at hj
    rw [hj]
    ring

/-- The SA partner of the product is its negation:
    `(Complex.I • H).conjTranspose = - (Complex.I • H)` for
    self-adjoint `H` (the product is anti-hermitian). -/
theorem conjTranspose_smul_I_of_selfAdjoint {H : Matrix I32 I32 ℂ}
    (hsa : H.conjTranspose = H) :
    (Complex.I • H).conjTranspose = - (Complex.I • H) := by
  rw [conjTranspose_smul_I, hsa, neg_smul]

/-- **THE NON-HERMITIAN ENGINE (C96-3a2 headline).** For a hermitian
    J-anticompatible order-one block `H`, the non-hermitian product
    `Complex.I • H` lies in `PairSpace`: block-admissibility of the
    product is `isAdmBlock_smul_I_of_isAntiAdm32`; its SA partner is
    `-(Complex.I • H)`, so the partner's admissibility and
    order-one conditions follow by negation; and order-one is
    complex-homogeneous. All four conditions of
    `mem_pairSpace_iff` are thereby proved for the product. -/
theorem pairSpace_of_isAntiAdm32 {H : Matrix I32 I32 ℂ}
    (hA : IsAntiAdm32 H) (hO : OrderOneHolds H) :
    Complex.I • H ∈ PairSpace := by
  have hAdm : IsAdmBlock (Complex.I • H) :=
    isAdmBlock_smul_I_of_isAntiAdm32 hA
  have hOO : OrderOneHolds (Complex.I • H) :=
    orderOneHolds_smul_complex Complex.I hO
  have hpartner : (Complex.I • H).conjTranspose = - (Complex.I • H) :=
    conjTranspose_smul_I_of_selfAdjoint hA.1
  refine ⟨hAdm, ?_, hOO, ?_⟩
  · rw [hpartner]; exact isAdmBlock_neg hAdm
  · rw [hpartner]; exact orderOneHolds_neg hOO

/-! ## 3. The antiparticle sign matrix and S-conjugation

The anti directions are obtained from the landed hermitian pattern
matrices `X` (the SM diagonal and flipped directions of
`CFKernel22`) by conjugation with the diagonal sign matrix
`aRSign = diag(1, ..., 1, -1, ..., -1)` (the sign flips exactly on
the right-antiparticle sector `24-31`). Conjugation by `aRSign`
fixes every generator and every opposite generator, hence preserves
the order-one condition; on a J-compatible hermitian pattern matrix
it negates exactly the `B` block, producing a J-ANTI-compatible
matrix. -/

/-- The sign function of `aRSign`: `1` below index `24`, `-1` on the
    right-antiparticle sector `24-31`. -/
def aRSgn (i : I32) : ℂ := if i.val < 24 then 1 else -1

/-- The antiparticle sign matrix: diagonal with sign `aRSgn`. -/
def aRSign : Matrix I32 I32 ℂ := Matrix.diagonal aRSgn

theorem aRSgn_apply (i : I32) : aRSgn i = if i.val < 24 then 1 else -1 := rfl

theorem aRSgn_sq (i : I32) : aRSgn i * aRSgn i = 1 := by
  unfold aRSgn; split_ifs <;> norm_num

theorem aRSgn_eq_one_or_neg_one (i : I32) :
    aRSgn i = 1 ∨ aRSgn i = -1 := by
  unfold aRSgn; split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem aRSign_mul_self : aRSign * aRSign = 1 := by
  rw [aRSign, Matrix.diagonal_mul_diagonal]
  have h : (fun i => aRSgn i * aRSgn i) = 1 := by
    funext i
    simpa using aRSgn_sq i
  rw [h]
  exact Matrix.diagonal_one

theorem aRSign_apply (i j : I32) :
    aRSign i j = if i = j then aRSgn i else 0 := by
  simp only [aRSign, Matrix.diagonal_apply]

theorem aRSign_mul_apply (M : Matrix I32 I32 ℂ) (i j : I32) :
    (aRSign * M) i j = aRSgn i * M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [aRSign_apply, if_pos rfl]
  · intro k _ hki
    rw [aRSign_apply, if_neg (Ne.symm hki), zero_mul]
  · intro hcon; exact absurd (Finset.mem_univ i) hcon

theorem mul_aRSign_apply (M : Matrix I32 I32 ℂ) (i j : I32) :
    (M * aRSign) i j = M i j * aRSgn j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [aRSign_apply, if_pos rfl]
  · intro k _ hkj
    rw [aRSign_apply, if_neg hkj, mul_zero]
  · intro hcon; exact absurd (Finset.mem_univ j) hcon

theorem aRSign_conjTranspose : aRSign.conjTranspose = aRSign := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases h : j = i
  · subst h
    rw [aRSign_apply, if_pos rfl]
    rcases aRSgn_eq_one_or_neg_one j with h1 | h1 <;> rw [h1] <;> simp
  · rw [aRSign_apply, aRSign_apply, if_neg h, if_neg (Ne.symm h), star_zero]

/-- `aRSign` commutes with the grading matrix (both are diagonal). -/
theorem aRSign_comm_gammaF : aRSign * gammaF = gammaF * aRSign := by
  ext i j
  rw [aRSign_mul_apply, gammaF_mul_apply]
  by_cases h : i = j
  · subst h; rw [aRSign_apply, if_pos rfl, mul_comm]
  · rw [gammaF_apply_ne h, mul_zero, aRSign_apply, if_neg h, mul_zero]

/-- The double commutator conjugates: for an involutive `u`,
    `dcGen (u * M * u) A B = u * dcGen M (u * A * u) (u * B * u) * u`. -/
theorem dcGen_conj (u M A B : Matrix I32 I32 ℂ) (hu : u * u = 1) :
    dcGen (u * M * u) A B
      = u * dcGen M (u * A * u) (u * B * u) * u := by
  have e1 : ∀ Y : Matrix I32 I32 ℂ, u * Y = (u * Y * u) * u := by
    intro Y
    rw [Matrix.mul_assoc (u * Y) u u, hu, Matrix.mul_one]
  have e2 : ∀ Y : Matrix I32 I32 ℂ, Y * u = u * (u * Y * u) := by
    intro Y
    rw [← Matrix.mul_assoc u (u * Y) u, ← Matrix.mul_assoc u u Y, hu,
      Matrix.one_mul]
  have conj_mul : ∀ X Y : Matrix I32 I32 ℂ,
      (u * X * u) * Y = u * (X * (u * Y * u)) * u := by
    intro X Y
    calc (u * X * u) * Y = u * X * (u * Y) := by noncomm_ring
      _ = u * X * ((u * Y * u) * u) := by conv_lhs => rw [e1 Y]
      _ = u * (X * (u * Y * u)) * u := by noncomm_ring
  have mul_conj : ∀ X Y : Matrix I32 I32 ℂ,
      Y * (u * X * u) = u * ((u * Y * u) * X) * u := by
    intro X Y
    calc Y * (u * X * u) = (Y * u) * X * u := by noncomm_ring
      _ = u * ((u * Y * u) * X) * u := by rw [e2 Y]; noncomm_ring
  have factor : ∀ P Q : Matrix I32 I32 ℂ,
      u * P * u - u * Q * u = u * (P - Q) * u := by
    intro P Q
    rw [Matrix.mul_sub, Matrix.sub_mul]
  have hcomm : (u * M * u) * A - A * (u * M * u)
      = u * (M * (u * A * u) - (u * A * u) * M) * u := by
    rw [conj_mul M A, mul_conj M A]
    exact factor _ _
  unfold dcGen
  rw [hcomm, conj_mul _ B, mul_conj _ B]
  exact factor _ _

/-- Conjugation by `aRSign` fixes any matrix whose support lies in
    the equal-sign region. -/
theorem aRSign_conj_eq_of_supp {G : Matrix I32 I32 ℂ}
    (h : ∀ i j : I32, G i j ≠ 0 → aRSgn i = aRSgn j) :
    aRSign * G * aRSign = G := by
  ext i j
  rw [mul_aRSign_apply, aRSign_mul_apply]
  by_cases hG : G i j = 0
  · rw [hG, mul_zero, zero_mul]
  · rw [h i j hG]
    linear_combination G i j * aRSgn_sq j

theorem aRSgn_eq_of_genH_supp {k : Fin 3} {i j : I32}
    (h : genH k i j ≠ 0) : aRSgn i = aRSgn j := by
  have hs := genH_supp k i j h
  unfold aRSgn
  rw [if_pos (by omega : i.val < 24), if_pos (by omega : j.val < 24)]

theorem aRSgn_eq_of_genM_supp {a : Fin 8} {i j : I32}
    (h : genM a i j ≠ 0) : aRSgn i = aRSgn j := by
  obtain ⟨t, p, q, hi, hj⟩ := genM_supp_triplet a i j h
  have hti := tripletOf_eig i.val i.isLt t p hi
  have htj := tripletOf_eig j.val j.isLt t q hj
  unfold aRSgn
  rcases hti with ⟨ht, h1, h2⟩ | ⟨ht, h1, h2⟩ <;>
    rcases htj with ⟨ht', h1', h2'⟩ | ⟨ht', h1', h2'⟩ <;>
    first
      | rw [if_pos (by omega : i.val < 24), if_pos (by omega : j.val < 24)]
      | rw [if_neg (by omega : ¬ i.val < 24), if_neg (by omega : ¬ j.val < 24)]
      | (exfalso; omega)

/-- `aRSign` conjugation fixes every gauge generator: the `C`
    generator is diagonal, the `H` generators live below index `8`
    (sign `+1`), and each `M` generator lives in a single triplet,
    which lies entirely in one sign region. -/
theorem aRSign_conj_smGen (g : Fin 12) :
    aRSign * smGen g * aRSign = smGen g := by
  apply aRSign_conj_eq_of_supp
  intro i j h
  fin_cases g
  · rw [genC_diag i j h]
  · exact aRSgn_eq_of_genH_supp h
  · exact aRSgn_eq_of_genH_supp h
  · exact aRSgn_eq_of_genH_supp h
  · exact aRSgn_eq_of_genM_supp h
  · exact aRSgn_eq_of_genM_supp h
  · exact aRSgn_eq_of_genM_supp h
  · exact aRSgn_eq_of_genM_supp h
  · exact aRSgn_eq_of_genM_supp h
  · exact aRSgn_eq_of_genM_supp h
  · exact aRSgn_eq_of_genM_supp h
  · exact aRSgn_eq_of_genM_supp h

theorem aRSgn_eq_of_genH_op_supp {k : Fin 3} {i j : I32}
    (h : genH k (partner j) (partner i) ≠ 0) : aRSgn i = aRSgn j := by
  have hs := genH_supp k (partner j) (partner i) h
  have key : ∀ x : I32, (partner x).val < 8 → x.val < 24 := by
    intro x hx
    have hpv := partner_val_eq x
    split_ifs at hpv <;> omega
  unfold aRSgn
  rw [if_pos (key i hs.2), if_pos (key j hs.1)]

theorem aRSgn_eq_of_genM_op_supp {a : Fin 8} {i j : I32}
    (h : genM a (partner j) (partner i) ≠ 0) : aRSgn i = aRSgn j := by
  obtain ⟨t, p, q, hi, hj⟩ := genM_supp_triplet a (partner j) (partner i) h
  have hti := tripletOf_eig (partner i).val (partner i).isLt t q hj
  have htj := tripletOf_eig (partner j).val (partner j).isLt t p hi
  have keyi : i.val < 24 := by
    have hpv := partner_val_eq i
    have hlt := i.isLt
    rcases hti with ⟨ht, h1, h2⟩ | ⟨ht, h1, h2⟩ <;>
      split_ifs at hpv <;> omega
  have keyj : j.val < 24 := by
    have hpv := partner_val_eq j
    have hlt := j.isLt
    rcases htj with ⟨ht, h1, h2⟩ | ⟨ht, h1, h2⟩ <;>
      split_ifs at hpv <;> omega
  unfold aRSgn
  rw [if_pos keyi, if_pos keyj]

/-- `aRSign` conjugation fixes every opposite generator: opposite
    supports are the partner images of the generator supports, which
    land in the sign-`+1` region `[0, 24)`. -/
theorem aRSign_conj_smGenOp (g : Fin 12) :
    aRSign * smGenOp g * aRSign = smGenOp g := by
  apply aRSign_conj_eq_of_supp
  intro i j h
  rw [smGenOp_apply] at h
  fin_cases g
  · have hpp : partner j = partner i := genC_diag (partner j) (partner i) h
    have : j = i := by
      have h2 := congrArg partner hpp
      rwa [partner_involutive, partner_involutive] at h2
    rw [this]
  · exact aRSgn_eq_of_genH_op_supp h
  · exact aRSgn_eq_of_genH_op_supp h
  · exact aRSgn_eq_of_genH_op_supp h
  · exact aRSgn_eq_of_genM_op_supp h
  · exact aRSgn_eq_of_genM_op_supp h
  · exact aRSgn_eq_of_genM_op_supp h
  · exact aRSgn_eq_of_genM_op_supp h
  · exact aRSgn_eq_of_genM_op_supp h
  · exact aRSgn_eq_of_genM_op_supp h
  · exact aRSgn_eq_of_genM_op_supp h
  · exact aRSgn_eq_of_genM_op_supp h

/-- S-conjugation preserves the order-one condition. -/
theorem orderOneHolds_aRSign_conj {X : Matrix I32 I32 ℂ}
    (hX : OrderOneHolds X) :
    OrderOneHolds (aRSign * X * aRSign) := by
  intro g1 g2
  have h := dcGen_conj aRSign X (smGen g1) (smGenOp g2) aRSign_mul_self
  rw [aRSign_conj_smGen, aRSign_conj_smGenOp] at h
  have h0 : dcGen X (smGen g1) (smGenOp g2) = 0 := hX g1 g2
  rw [h0, Matrix.mul_zero, Matrix.zero_mul] at h
  exact h

/-- The partner-sign twist of an index: `+1` on the left sectors
    `[0, 8)` and `[16, 24)`, `-1` on the right sectors `[8, 16)` and
    `[24, 32)`. -/
theorem aRSgn_partner_mul_self (i : I32) :
    aRSgn (partner i) * aRSgn i = if i.val % 16 < 8 then 1 else -1 := by
  have hlt := i.isLt
  rcases (show i.val < 8 ∨ (8 ≤ i.val ∧ i.val < 16)
      ∨ (16 ≤ i.val ∧ i.val < 24) ∨ 24 ≤ i.val by omega)
    with h | h | h | h
  · have hpv : (partner i).val = i.val + 16 := by
      rw [partner_val_eq, if_pos (by omega : i.val < 16)]
    unfold aRSgn
    rw [hpv, if_pos (by omega : i.val + 16 < 24),
      if_pos (by omega : i.val < 24), if_pos (by omega : i.val % 16 < 8)]
    norm_num
  · have hpv : (partner i).val = i.val + 16 := by
      rw [partner_val_eq, if_pos (by omega : i.val < 16)]
    unfold aRSgn
    rw [hpv, if_neg (by omega : ¬ i.val + 16 < 24),
      if_pos (by omega : i.val < 24), if_neg (by omega : ¬ i.val % 16 < 8)]
    norm_num
  · have hpv : (partner i).val = i.val - 16 := by
      rw [partner_val_eq, if_neg (by omega : ¬ i.val < 16)]
    unfold aRSgn
    rw [hpv, if_pos (by omega : i.val - 16 < 24),
      if_pos (by omega : i.val < 24), if_pos (by omega : i.val % 16 < 8)]
    norm_num
  · have hpv : (partner i).val = i.val - 16 := by
      rw [partner_val_eq, if_neg (by omega : ¬ i.val < 16)]
    unfold aRSgn
    rw [hpv, if_pos (by omega : i.val - 16 < 24),
      if_neg (by omega : ¬ i.val < 24), if_neg (by omega : ¬ i.val % 16 < 8)]
    norm_num

/-- If the partner twists of `i` and `j` are opposite, the
    S-conjugate entry picks up exactly one minus sign. -/
theorem aRSgn_anti_of_tprod {i j : I32}
    (h : (aRSgn (partner i) * aRSgn i)
      * (aRSgn (partner j) * aRSgn j) = -1) :
    aRSgn (partner i) * aRSgn (partner j) = - (aRSgn i * aRSgn j) := by
  calc aRSgn (partner i) * aRSgn (partner j)
      = (aRSgn (partner i) * aRSgn (partner j))
        * ((aRSgn i * aRSgn i) * (aRSgn j * aRSgn j)) := by
        rw [aRSgn_sq, aRSgn_sq, mul_one, mul_one]
    _ = ((aRSgn (partner i) * aRSgn i) * (aRSgn (partner j) * aRSgn j))
        * (aRSgn i * aRSgn j) := by ring
    _ = - (aRSgn i * aRSgn j) := by rw [h, neg_one_mul]

/-- **The anti transport theorem.** S-conjugation sends a hermitian,
    grading-odd, J-compatible pattern matrix whose support lies in
    the opposite-twist region to a J-anticompatible hermitian
    grading-odd matrix. -/
theorem isAntiAdm32_aRSign_conj {X : Matrix I32 I32 ℂ}
    (hsa : X.conjTranspose = X)
    (hgr : gammaF * X + X * gammaF = 0)
    (hJ : IsJCompatible X)
    (hsupp : ∀ i j : I32, X i j ≠ 0 →
      (aRSgn (partner i) * aRSgn i)
        * (aRSgn (partner j) * aRSgn j) = -1) :
    IsAntiAdm32 (aRSign * X * aRSign) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      aRSign_conjTranspose, hsa, ← Matrix.mul_assoc]
  · have e1 : gammaF * (aRSign * X * aRSign)
        = aRSign * (gammaF * X) * aRSign := by
      calc gammaF * (aRSign * X * aRSign)
          = (gammaF * aRSign) * X * aRSign := by noncomm_ring
        _ = aRSign * (gammaF * X) * aRSign := by
            rw [← aRSign_comm_gammaF]; noncomm_ring
    have e2 : (aRSign * X * aRSign) * gammaF
        = aRSign * (X * gammaF) * aRSign := by
      calc (aRSign * X * aRSign) * gammaF
          = aRSign * X * (aRSign * gammaF) := by noncomm_ring
        _ = aRSign * (X * gammaF) * aRSign := by
            rw [aRSign_comm_gammaF]; noncomm_ring
    have e3 : aRSign * (gammaF * X) * aRSign
          + aRSign * (X * gammaF) * aRSign
        = aRSign * (gammaF * X + X * gammaF) * aRSign := by
      rw [Matrix.mul_add, Matrix.add_mul]
    rw [e1, e2, e3, hgr, Matrix.mul_zero, Matrix.zero_mul]
  · ext i j
    rw [UJ_conj_apply, Matrix.transpose_apply, Matrix.neg_apply]
    rw [mul_aRSign_apply, mul_aRSign_apply, aRSign_mul_apply,
      aRSign_mul_apply, ← jCompat_entry_local X hJ i j]
    by_cases hX : X i j = 0
    · rw [hX, mul_zero, mul_zero, zero_mul, zero_mul, neg_zero]
    · have hanti := aRSgn_anti_of_tprod (hsupp i j hX)
      linear_combination X i j * hanti

/-- The `(8, 24)` entry of an `smDirac` with vanishing right-handed
    Majorana parameter is zero (it is the conjugate Majorana block). -/
theorem smDirac_apply_8_24 (yNu yE yU yD : ℂ) :
    smDirac yNu yE yU yD 0 (⟨8, by norm_num⟩ : I32)
      (⟨24, by norm_num⟩ : I32) = 0 := by
  rw [smDirac_Edag_entry_aux yNu yE yU yD 0 _ _ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num), Matrix.conjTranspose_apply]
  simp [majoranaBlock]

/-- The `(24, 8)` entry of an `smDirac` with vanishing right-handed
    Majorana parameter is zero (it is the Majorana block). -/
theorem smDirac_apply_24_8 (yNu yE yU yD : ℂ) :
    smDirac yNu yE yU yD 0 (⟨24, by norm_num⟩ : I32)
      (⟨8, by norm_num⟩ : I32) = 0 := by
  simp [smDirac, buildDirac, majoranaBlock]

/-- Every nonzero entry of an `smDirac` with vanishing right-handed
    Majorana parameter joins opposite partner twists. -/
theorem smDirac_tprod_of_ne (yNu yE yU yD : ℂ) {i j : I32}
    (h : smDirac yNu yE yU yD 0 i j ≠ 0) :
    (aRSgn (partner i) * aRSgn i)
      * (aRSgn (partner j) * aRSgn j) = -1 := by
  have hs := smDirac_supp_aux yNu yE yU yD 0 i j h
  rw [aRSgn_partner_mul_self, aRSgn_partner_mul_self]
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos (by omega : i.val % 16 < 8),
      if_neg (by omega : ¬ j.val % 16 < 8)]
    norm_num
  · rw [if_neg (by omega : ¬ i.val % 16 < 8),
      if_pos (by omega : j.val % 16 < 8)]
    norm_num
  · rw [if_pos (by omega : i.val % 16 < 8),
      if_neg (by omega : ¬ j.val % 16 < 8)]
    norm_num
  · rw [if_neg (by omega : ¬ i.val % 16 < 8),
      if_pos (by omega : j.val % 16 < 8)]
    norm_num
  · exfalso
    apply h
    have hi : i = ⟨8, by omega⟩ := Fin.ext h1
    have hj : j = ⟨24, by omega⟩ := Fin.ext h2
    rw [hi, hj]
    exact smDirac_apply_8_24 yNu yE yU yD
  · exfalso
    apply h
    have hi : i = ⟨24, by omega⟩ := Fin.ext h1
    have hj : j = ⟨8, by omega⟩ := Fin.ext h2
    rw [hi, hj]
    exact smDirac_apply_24_8 yNu yE yU yD

/-- Every nonzero entry of `exoticReNuLeR` joins opposite partner twists. -/
theorem exoticReNuLeR_tprod_of_ne {i j : I32} (h : exoticReNuLeR i j ≠ 0) :
    (aRSgn (partner i) * aRSgn i)
      * (aRSgn (partner j) * aRSgn j) = -1 := by
  have hs := exoticReNuLeR_supp i j h
  rw [aRSgn_partner_mul_self, aRSgn_partner_mul_self]
  rcases hs with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
  · have hiv : i.val = 0 := by rw [hi]; rfl
    have hjv : j.val = 9 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (0:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (9:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 9 := by rw [hi]; rfl
    have hjv : j.val = 0 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (9:ℕ) % 16 < 8), if_pos (by norm_num : (0:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 16 := by rw [hi]; rfl
    have hjv : j.val = 25 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (16:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (25:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 25 := by rw [hi]; rfl
    have hjv : j.val = 16 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (25:ℕ) % 16 < 8), if_pos (by norm_num : (16:ℕ) % 16 < 8)]
    norm_num

/-- Every nonzero entry of `exoticImNuLeR` joins opposite partner twists. -/
theorem exoticImNuLeR_tprod_of_ne {i j : I32} (h : exoticImNuLeR i j ≠ 0) :
    (aRSgn (partner i) * aRSgn i)
      * (aRSgn (partner j) * aRSgn j) = -1 := by
  have hs := exoticImNuLeR_supp i j h
  rw [aRSgn_partner_mul_self, aRSgn_partner_mul_self]
  rcases hs with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
  · have hiv : i.val = 0 := by rw [hi]; rfl
    have hjv : j.val = 9 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (0:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (9:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 9 := by rw [hi]; rfl
    have hjv : j.val = 0 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (9:ℕ) % 16 < 8), if_pos (by norm_num : (0:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 16 := by rw [hi]; rfl
    have hjv : j.val = 25 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (16:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (25:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 25 := by rw [hi]; rfl
    have hjv : j.val = 16 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (25:ℕ) % 16 < 8), if_pos (by norm_num : (16:ℕ) % 16 < 8)]
    norm_num

/-- Every nonzero entry of `exoticReELNuR` joins opposite partner twists. -/
theorem exoticReELNuR_tprod_of_ne {i j : I32} (h : exoticReELNuR i j ≠ 0) :
    (aRSgn (partner i) * aRSgn i)
      * (aRSgn (partner j) * aRSgn j) = -1 := by
  have hs := exoticReELNuR_supp i j h
  rw [aRSgn_partner_mul_self, aRSgn_partner_mul_self]
  rcases hs with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
  · have hiv : i.val = 1 := by rw [hi]; rfl
    have hjv : j.val = 8 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (1:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (8:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 8 := by rw [hi]; rfl
    have hjv : j.val = 1 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (8:ℕ) % 16 < 8), if_pos (by norm_num : (1:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 17 := by rw [hi]; rfl
    have hjv : j.val = 24 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (17:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (24:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 24 := by rw [hi]; rfl
    have hjv : j.val = 17 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (24:ℕ) % 16 < 8), if_pos (by norm_num : (17:ℕ) % 16 < 8)]
    norm_num

/-- Every nonzero entry of `exoticImELNuR` joins opposite partner twists. -/
theorem exoticImELNuR_tprod_of_ne {i j : I32} (h : exoticImELNuR i j ≠ 0) :
    (aRSgn (partner i) * aRSgn i)
      * (aRSgn (partner j) * aRSgn j) = -1 := by
  have hs := exoticImELNuR_supp i j h
  rw [aRSgn_partner_mul_self, aRSgn_partner_mul_self]
  rcases hs with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
  · have hiv : i.val = 1 := by rw [hi]; rfl
    have hjv : j.val = 8 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (1:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (8:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 24 := by rw [hi]; rfl
    have hjv : j.val = 17 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (24:ℕ) % 16 < 8), if_pos (by norm_num : (17:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 8 := by rw [hi]; rfl
    have hjv : j.val = 1 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (8:ℕ) % 16 < 8), if_pos (by norm_num : (1:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 17 := by rw [hi]; rfl
    have hjv : j.val = 24 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (17:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (24:ℕ) % 16 < 8)]
    norm_num

/-- Every nonzero entry of `exoticReULDR` joins opposite partner twists. -/
theorem exoticReULDR_tprod_of_ne {i j : I32} (h : exoticReULDR i j ≠ 0) :
    (aRSgn (partner i) * aRSgn i)
      * (aRSgn (partner j) * aRSgn j) = -1 := by
  have hs := exoticReULDR_supp i j h
  rw [aRSgn_partner_mul_self, aRSgn_partner_mul_self]
  rcases hs with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
  · have hiv : i.val = 2 := by rw [hi]; rfl
    have hjv : j.val = 11 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (2:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (11:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 11 := by rw [hi]; rfl
    have hjv : j.val = 2 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (11:ℕ) % 16 < 8), if_pos (by norm_num : (2:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 4 := by rw [hi]; rfl
    have hjv : j.val = 13 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (4:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (13:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 13 := by rw [hi]; rfl
    have hjv : j.val = 4 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (13:ℕ) % 16 < 8), if_pos (by norm_num : (4:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 6 := by rw [hi]; rfl
    have hjv : j.val = 15 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (6:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (15:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 15 := by rw [hi]; rfl
    have hjv : j.val = 6 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (15:ℕ) % 16 < 8), if_pos (by norm_num : (6:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 18 := by rw [hi]; rfl
    have hjv : j.val = 27 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (18:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (27:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 27 := by rw [hi]; rfl
    have hjv : j.val = 18 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (27:ℕ) % 16 < 8), if_pos (by norm_num : (18:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 20 := by rw [hi]; rfl
    have hjv : j.val = 29 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (20:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (29:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 29 := by rw [hi]; rfl
    have hjv : j.val = 20 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (29:ℕ) % 16 < 8), if_pos (by norm_num : (20:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 22 := by rw [hi]; rfl
    have hjv : j.val = 31 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (22:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (31:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 31 := by rw [hi]; rfl
    have hjv : j.val = 22 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (31:ℕ) % 16 < 8), if_pos (by norm_num : (22:ℕ) % 16 < 8)]
    norm_num

/-- Every nonzero entry of `exoticImULDR` joins opposite partner twists. -/
theorem exoticImULDR_tprod_of_ne {i j : I32} (h : exoticImULDR i j ≠ 0) :
    (aRSgn (partner i) * aRSgn i)
      * (aRSgn (partner j) * aRSgn j) = -1 := by
  have hs := exoticImULDR_supp i j h
  rw [aRSgn_partner_mul_self, aRSgn_partner_mul_self]
  rcases hs with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
  · have hiv : i.val = 2 := by rw [hi]; rfl
    have hjv : j.val = 11 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (2:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (11:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 4 := by rw [hi]; rfl
    have hjv : j.val = 13 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (4:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (13:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 6 := by rw [hi]; rfl
    have hjv : j.val = 15 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (6:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (15:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 27 := by rw [hi]; rfl
    have hjv : j.val = 18 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (27:ℕ) % 16 < 8), if_pos (by norm_num : (18:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 29 := by rw [hi]; rfl
    have hjv : j.val = 20 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (29:ℕ) % 16 < 8), if_pos (by norm_num : (20:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 31 := by rw [hi]; rfl
    have hjv : j.val = 22 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (31:ℕ) % 16 < 8), if_pos (by norm_num : (22:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 11 := by rw [hi]; rfl
    have hjv : j.val = 2 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (11:ℕ) % 16 < 8), if_pos (by norm_num : (2:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 13 := by rw [hi]; rfl
    have hjv : j.val = 4 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (13:ℕ) % 16 < 8), if_pos (by norm_num : (4:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 15 := by rw [hi]; rfl
    have hjv : j.val = 6 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (15:ℕ) % 16 < 8), if_pos (by norm_num : (6:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 18 := by rw [hi]; rfl
    have hjv : j.val = 27 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (18:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (27:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 20 := by rw [hi]; rfl
    have hjv : j.val = 29 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (20:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (29:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 22 := by rw [hi]; rfl
    have hjv : j.val = 31 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (22:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (31:ℕ) % 16 < 8)]
    norm_num

/-- Every nonzero entry of `exoticReDLUR` joins opposite partner twists. -/
theorem exoticReDLUR_tprod_of_ne {i j : I32} (h : exoticReDLUR i j ≠ 0) :
    (aRSgn (partner i) * aRSgn i)
      * (aRSgn (partner j) * aRSgn j) = -1 := by
  have hs := exoticReDLUR_supp i j h
  rw [aRSgn_partner_mul_self, aRSgn_partner_mul_self]
  rcases hs with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
  · have hiv : i.val = 3 := by rw [hi]; rfl
    have hjv : j.val = 10 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (3:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (10:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 10 := by rw [hi]; rfl
    have hjv : j.val = 3 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (10:ℕ) % 16 < 8), if_pos (by norm_num : (3:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 5 := by rw [hi]; rfl
    have hjv : j.val = 12 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (5:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (12:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 12 := by rw [hi]; rfl
    have hjv : j.val = 5 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (12:ℕ) % 16 < 8), if_pos (by norm_num : (5:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 7 := by rw [hi]; rfl
    have hjv : j.val = 14 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (7:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (14:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 14 := by rw [hi]; rfl
    have hjv : j.val = 7 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (14:ℕ) % 16 < 8), if_pos (by norm_num : (7:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 19 := by rw [hi]; rfl
    have hjv : j.val = 26 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (19:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (26:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 26 := by rw [hi]; rfl
    have hjv : j.val = 19 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (26:ℕ) % 16 < 8), if_pos (by norm_num : (19:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 21 := by rw [hi]; rfl
    have hjv : j.val = 28 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (21:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (28:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 28 := by rw [hi]; rfl
    have hjv : j.val = 21 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (28:ℕ) % 16 < 8), if_pos (by norm_num : (21:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 23 := by rw [hi]; rfl
    have hjv : j.val = 30 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (23:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (30:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 30 := by rw [hi]; rfl
    have hjv : j.val = 23 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (30:ℕ) % 16 < 8), if_pos (by norm_num : (23:ℕ) % 16 < 8)]
    norm_num

/-- Every nonzero entry of `exoticImDLUR` joins opposite partner twists. -/
theorem exoticImDLUR_tprod_of_ne {i j : I32} (h : exoticImDLUR i j ≠ 0) :
    (aRSgn (partner i) * aRSgn i)
      * (aRSgn (partner j) * aRSgn j) = -1 := by
  have hs := exoticImDLUR_supp i j h
  rw [aRSgn_partner_mul_self, aRSgn_partner_mul_self]
  rcases hs with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
  · have hiv : i.val = 3 := by rw [hi]; rfl
    have hjv : j.val = 10 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (3:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (10:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 5 := by rw [hi]; rfl
    have hjv : j.val = 12 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (5:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (12:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 7 := by rw [hi]; rfl
    have hjv : j.val = 14 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (7:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (14:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 26 := by rw [hi]; rfl
    have hjv : j.val = 19 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (26:ℕ) % 16 < 8), if_pos (by norm_num : (19:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 28 := by rw [hi]; rfl
    have hjv : j.val = 21 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (28:ℕ) % 16 < 8), if_pos (by norm_num : (21:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 30 := by rw [hi]; rfl
    have hjv : j.val = 23 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (30:ℕ) % 16 < 8), if_pos (by norm_num : (23:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 10 := by rw [hi]; rfl
    have hjv : j.val = 3 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (10:ℕ) % 16 < 8), if_pos (by norm_num : (3:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 12 := by rw [hi]; rfl
    have hjv : j.val = 5 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (12:ℕ) % 16 < 8), if_pos (by norm_num : (5:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 14 := by rw [hi]; rfl
    have hjv : j.val = 7 := by rw [hj]; rfl
    rw [hiv, hjv, if_neg (by norm_num : ¬ (14:ℕ) % 16 < 8), if_pos (by norm_num : (7:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 19 := by rw [hi]; rfl
    have hjv : j.val = 26 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (19:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (26:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 21 := by rw [hi]; rfl
    have hjv : j.val = 28 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (21:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (28:ℕ) % 16 < 8)]
    norm_num
  · have hiv : i.val = 23 := by rw [hi]; rfl
    have hjv : j.val = 30 := by rw [hj]; rfl
    rw [hiv, hjv, if_pos (by norm_num : (23:ℕ) % 16 < 8), if_neg (by norm_num : ¬ (30:ℕ) % 16 < 8)]
    norm_num

/-! ## 4. The anti families and the completed direction families -/

/-- The anti SM pattern matrices: S-conjugates of the eight diagonal
    SM pattern matrices (`dirs22` indices `0-7`). -/
def antiSMMat (k : Fin 8) : Matrix I32 I32 ℂ :=
  aRSign * dirs22 ⟨k.val, by omega⟩ * aRSign

/-- The anti flipped pattern matrices: S-conjugates of the eight
    flipped hermitian matrices (`dirs22` indices `10-17`). -/
def antiFlipMat (k : Fin 8) : Matrix I32 I32 ℂ :=
  aRSign * dirs22 ⟨k.val + 10, by omega⟩ * aRSign

theorem antiSMMat_isAnti (k : Fin 8) : IsAntiAdm32 (antiSMMat k) := by
  have hW := dirs22_mem ⟨k.val, by omega⟩
  refine isAntiAdm32_aRSign_conj hW.2.2.1 hW.2.2.2.2 hW.2.2.2.1 ?_
  intro i j h
  fin_cases k
  · exact smDirac_tprod_of_ne 1 0 0 0 h
  · exact smDirac_tprod_of_ne Complex.I 0 0 0 h
  · exact smDirac_tprod_of_ne 0 1 0 0 h
  · exact smDirac_tprod_of_ne 0 Complex.I 0 0 h
  · exact smDirac_tprod_of_ne 0 0 1 0 h
  · exact smDirac_tprod_of_ne 0 0 Complex.I 0 h
  · exact smDirac_tprod_of_ne 0 0 0 1 h
  · exact smDirac_tprod_of_ne 0 0 0 Complex.I h

theorem antiFlipMat_isAnti (k : Fin 8) : IsAntiAdm32 (antiFlipMat k) := by
  have hW := dirs22_mem ⟨k.val + 10, by omega⟩
  refine isAntiAdm32_aRSign_conj hW.2.2.1 hW.2.2.2.2 hW.2.2.2.1 ?_
  intro i j h
  fin_cases k
  · exact exoticReNuLeR_tprod_of_ne h
  · exact exoticImNuLeR_tprod_of_ne h
  · exact exoticReELNuR_tprod_of_ne h
  · exact exoticImELNuR_tprod_of_ne h
  · exact exoticReULDR_tprod_of_ne h
  · exact exoticImULDR_tprod_of_ne h
  · exact exoticReDLUR_tprod_of_ne h
  · exact exoticImDLUR_tprod_of_ne h

/-- The eight anti SM directions, as pair-space elements. -/
def antiSMDir (k : Fin 8) : PairSpace :=
  ⟨Complex.I • antiSMMat k,
    pairSpace_of_isAntiAdm32 (antiSMMat_isAnti k)
      (orderOneHolds_aRSign_conj (dirs22_mem ⟨k.val, by omega⟩).1)⟩

/-- The eight anti flipped directions, as pair-space elements. -/
def antiFlipDir (k : Fin 8) : PairSpace :=
  ⟨Complex.I • antiFlipMat k,
    pairSpace_of_isAntiAdm32 (antiFlipMat_isAnti k)
      (orderOneHolds_aRSign_conj (dirs22_mem ⟨k.val + 10, by omega⟩).1)⟩

/-- **The completed SM-like family**: the ten landed hermitian SM
    directions (`pairDirSM`, indices `0-9`) followed by their eight
    non-hermitian partners (indices `10-17`, in the pattern order
    Nu, E, U, D, each real then imaginary). -/
def pairDirSM18 : Fin 18 → PairSpace := Fin.append pairDirSM antiSMDir

theorem pairDirSM18_SM (k : Fin 10) :
    pairDirSM18 ⟨k.val, by omega⟩ = pairDirSM k := by
  have e1 : (⟨k.val, by omega⟩ : Fin 18) = Fin.castAdd 8 k := rfl
  rw [pairDirSM18, e1, Fin.append_left]

theorem pairDirSM18_anti (k : Fin 8) :
    pairDirSM18 ⟨10 + k.val, by omega⟩ = antiSMDir k := by
  have e1 : (⟨10 + k.val, by omega⟩ : Fin 18) = Fin.natAdd 10 k := rfl
  rw [pairDirSM18, e1, Fin.append_right]

/-- The eight hermitian flipped directions, as pair-space elements
    (`dirs22` indices `10-17`). -/
def flipHermDir (k : Fin 8) : PairSpace := pairDir22 ⟨k.val + 10, by omega⟩

/-- **The flipped family**: the eight hermitian flipped directions
    (indices `0-7`) followed by their eight non-hermitian partners
    (indices `8-15`, in the pattern order NuLeR, ELNuR, ULDR, DLUR,
    each real then imaginary). -/
def pairDirFlip16 : Fin 16 → PairSpace :=
  Fin.append flipHermDir antiFlipDir

theorem pairDirFlip16_herm (k : Fin 8) :
    pairDirFlip16 ⟨k.val, by omega⟩ = flipHermDir k := by
  have e1 : (⟨k.val, by omega⟩ : Fin 16) = Fin.castAdd 8 k := rfl
  rw [pairDirFlip16, e1, Fin.append_left]

theorem pairDirFlip16_anti (k : Fin 8) :
    pairDirFlip16 ⟨8 + k.val, by omega⟩ = antiFlipDir k := by
  have e1 : (⟨8 + k.val, by omega⟩ : Fin 16) = Fin.natAdd 8 k := rfl
  rw [pairDirFlip16, e1, Fin.append_right]

end ThetLogos
