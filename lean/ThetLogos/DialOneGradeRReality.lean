import Mathlib.Tactic
import ThetLogos.DialOneGradeRConjPin
import ThetLogos.DialOneConjugationCounterexample

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneGammaFamilyPin
open ThetLogos.DialOneGradeRConjPin

namespace ThetLogos.DialOneGradeRReality

/-!
# ThetLogos.DialOneGradeRReality — GRADE R, gap (α): CLOSED, NEGATIVELY

Governing texts: the pin `DialOneGradeRConjPin` (the
centralizing class, conditions (a)/(b)/(c)) and the
content module `DialOneGradeRConj`, whose
`dialOneBase_preserved` transports the base's star
clause only under the extra hypothesis `IsRealMat U`
(`Uᴴ = Uᵀ`). Gap (α) asked whether reality FOLLOWS
from the class — the expected engine being condition
(c) at generic Yukawas.

**Verdict: it does not.** This module exhibits a
concrete non-real member of the centralizing class
and verifies it entrywise. The witness `U0` is the
block-repeat (once per 8-seat block) of the 8×8
complex-orthogonal matrix `P8` which is the identity
except on the colour seats {2, 4} (both of Yukawa
weight Yu), where it acts as
`[[5/4, 3i/4], [−3i/4, 5/4]]` — transpose-orthogonal
(`c² − s² = 1` for `c = 5/4`, `s = 3/4`) but not real.
It satisfies transpose-unitarity, (a) (it is block
diagonal over the γ_F blocks), (b) (it is the same on
partner blocks), and (c): inside each block it is
supported on equal-Yukawa-weight seat pairs only, so
it commutes with the diagonal Yukawa matrix `A`, and
the intertwining relations the Dirac operator imposes
between blocks are identities for a block-repeat.

Consequences, stated at their exact scope:

* The reality lemma is FALSE: `reality_does_not_follow`
  (`¬ ∀ U, CentralizingClass U → IsRealMat U`).
  The hypothesis `IsRealMat U` in
  `dialOneBase_preserved` and in the capstone
  `strengthened_preserved_of_reality_pulled` is
  ESSENTIAL — it cannot be discharged from (a)/(b)/(c).
* No class amendment is made here: the class is the
  paper's (a)/(b)/(c), and amending it is Jeff's call.
* This witness alone does NOT decide `PreservationQ`:
  that would additionally require a strengthened `π`
  whose star clause fails under `U0`. Not asserted
  here, in either direction.

NO CLAIM. Dial 1 = 0.
-/

/-! ## The block decomposition of `Fin 32` -/

/-- The product decomposition `Fin 32 ≃ Fin 4 × Fin 8`
(block, seat-in-block), with `val = block * 8 + seat`. -/
def e32 : Fin 4 × Fin 8 ≃ Fin 32 where
  toFun p := ⟨p.1.val * 8 + p.2.val, by
    have h1 := p.1.isLt; have h2 := p.2.isLt; omega⟩
  invFun k := (⟨k.val / 8, by have h := k.isLt; omega⟩,
    ⟨k.val % 8, Nat.mod_lt _ (by norm_num)⟩)
  left_inv p := by
    obtain ⟨⟨b, hb⟩, ⟨r, hr⟩⟩ := p
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · show (b * 8 + r) / 8 = b
      omega
    · show (b * 8 + r) % 8 = r
      omega
  right_inv k := by
    apply Fin.ext
    show (k.val / 8) * 8 + (k.val % 8) = k.val
    omega

theorem e32_val (b : Fin 4) (r : Fin 8) :
    (e32 (b, r)).val = b.val * 8 + r.val := rfl

theorem e32_block (b : Fin 4) (r : Fin 8) :
    (e32 (b, r)).val / 8 = b.val := by
  rw [e32_val]; omega

theorem e32_local (b : Fin 4) (r : Fin 8) :
    (e32 (b, r)).val % 8 = r.val := by
  rw [e32_val]; omega

/-! ## The witness -/

/-- The 8×8 complex-orthogonal block: the identity off
the colour seats {2, 4} (both of Yukawa weight Yu);
on them, `[[5/4, 3i/4], [−3i/4, 5/4]]`. -/
noncomputable def P8 : Matrix (Fin 8) (Fin 8) ℂ := fun r s =>
  if r.val = 2 ∧ s.val = 4 then (3 / 4 : ℂ) * Complex.I
  else if r.val = 4 ∧ s.val = 2 then -(3 / 4 : ℂ) * Complex.I
  else if r = s then (if r.val = 2 ∨ r.val = 4 then (5 / 4 : ℂ) else 1)
  else 0

/-- The witness matrix: `P8` repeated identically on
each of the four 8-seat blocks of `Fin 32`. -/
noncomputable def U0 : Matrix (Fin 32) (Fin 32) ℂ := fun i j =>
  if i.val / 8 = j.val / 8 then
    P8 ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩
      ⟨j.val % 8, Nat.mod_lt _ (by norm_num)⟩
  else 0

theorem U0_apply (i j : Fin 32) :
    U0 i j = if i.val / 8 = j.val / 8 then
      P8 ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩
        ⟨j.val % 8, Nat.mod_lt _ (by norm_num)⟩
    else 0 := rfl

/-- Entry of `U0` at a product-decomposed column. -/
theorem U0_apply_e32_right (i : Fin 32) (b : Fin 4) (r : Fin 8) :
    U0 i (e32 (b, r)) = if i.val / 8 = b.val then
      P8 ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩ r
    else 0 := by
  have hfin : (⟨(e32 (b, r)).val % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8)
      = r := Fin.ext (e32_local b r)
  rw [U0_apply, e32_block, hfin]

/-- Entry of `U0` at a product-decomposed row. -/
theorem U0_apply_e32_left (b : Fin 4) (r : Fin 8) (j : Fin 32) :
    U0 (e32 (b, r)) j = if b.val = j.val / 8 then
      P8 r ⟨j.val % 8, Nat.mod_lt _ (by norm_num)⟩
    else 0 := by
  have hfin : (⟨(e32 (b, r)).val % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8)
      = r := Fin.ext (e32_local b r)
  rw [U0_apply, e32_block, hfin]

/-! ## The block `P8` is transpose-orthogonal -/

theorem P8_mul_transpose : P8 * P8ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, P8, Fin.sum_univ_eight] <;>
    norm_num [Complex.ext_iff]

theorem P8_transpose_mul : P8ᵀ * P8 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, P8, Fin.sum_univ_eight] <;>
    norm_num [Complex.ext_iff]

/-! ## Sum reduction: multiplication by `U0` is a block sum -/

/-- Left multiplication by `U0` reduces to the sum
over the 8 seats of `i`'s block. -/
theorem U0_mul_apply (M : Matrix (Fin 32) (Fin 32) ℂ) (i j : Fin 32) :
    (U0 * M) i j = ∑ r : Fin 8,
      P8 ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩ r
        * M (e32 (⟨i.val / 8, by have h := i.isLt; omega⟩, r)) j := by
  rw [Matrix.mul_apply,
    ← Equiv.sum_comp e32 (fun k => U0 i k * M k j),
    Fintype.sum_prod_type]
  refine (Finset.sum_eq_single (⟨i.val / 8, by have h := i.isLt; omega⟩ : Fin 4)
    ?_ ?_).trans ?_
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro r _
    rw [U0_apply_e32_right, if_neg]
    · exact zero_mul _
    · intro hcon
      apply hb
      apply Fin.ext
      exact hcon.symm
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon
  · apply Finset.sum_congr rfl
    intro r _
    rw [U0_apply_e32_right, if_pos rfl]

/-- Left multiplication by `U0ᵀ` reduces to the sum
over the 8 seats of `i`'s block. -/
theorem U0_transpose_mul_apply (M : Matrix (Fin 32) (Fin 32) ℂ)
    (i j : Fin 32) :
    (U0ᵀ * M) i j = ∑ r : Fin 8,
      P8 r ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩
        * M (e32 (⟨i.val / 8, by have h := i.isLt; omega⟩, r)) j := by
  rw [Matrix.mul_apply]
  have htr : ∀ k : Fin 32, (U0ᵀ) i k = U0 k i :=
    fun k => Matrix.transpose_apply U0 i k
  simp only [htr]
  rw [← Equiv.sum_comp e32 (fun k => U0 k i * M k j),
    Fintype.sum_prod_type]
  refine (Finset.sum_eq_single (⟨i.val / 8, by have h := i.isLt; omega⟩ : Fin 4)
    ?_ ?_).trans ?_
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro r _
    rw [U0_apply_e32_left, if_neg]
    · exact zero_mul _
    · intro hcon
      apply hb
      apply Fin.ext
      exact hcon
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon
  · apply Finset.sum_congr rfl
    intro r _
    rw [U0_apply_e32_left, if_pos rfl]

/-! ## `U0` is transpose-unitary -/

theorem U0_mul_transpose : U0 * U0ᵀ = 1 := by
  ext i j
  rw [U0_mul_apply, Matrix.one_apply]
  by_cases hb : i.val / 8 = j.val / 8
  · have hterm : ∀ r : Fin 8,
        P8 ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩ r
            * U0ᵀ (e32 (⟨i.val / 8, by have h := i.isLt; omega⟩, r)) j
          = P8 ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩ r
            * P8 ⟨j.val % 8, Nat.mod_lt _ (by norm_num)⟩ r := by
      intro r
      rw [Matrix.transpose_apply, U0_apply_e32_right, if_pos hb.symm]
    rw [Finset.sum_congr rfl (fun r _ => hterm r)]
    have hPP : (P8 * P8ᵀ) ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩
          ⟨j.val % 8, Nat.mod_lt _ (by norm_num)⟩
        = ∑ r : Fin 8, P8 ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩ r
            * P8 ⟨j.val % 8, Nat.mod_lt _ (by norm_num)⟩ r := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro r _
      rw [Matrix.transpose_apply]
    rw [← hPP, P8_mul_transpose, Matrix.one_apply]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (by rw [hij] : (⟨i.val % 8,
        Nat.mod_lt _ (by norm_num)⟩ : Fin 8)
        = ⟨j.val % 8, Nat.mod_lt _ (by norm_num)⟩)]
    · rw [if_neg hij, if_neg]
      intro hcon
      apply hij
      apply Fin.ext
      have h1 : i.val % 8 = j.val % 8 := congrArg Fin.val hcon
      omega
  · have hterm : ∀ r : Fin 8,
        P8 ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩ r
            * U0ᵀ (e32 (⟨i.val / 8, by have h := i.isLt; omega⟩, r)) j
          = 0 := by
      intro r
      rw [Matrix.transpose_apply, U0_apply_e32_right, if_neg, mul_zero]
      intro hcon
      apply hb
      exact hcon.symm
    rw [Finset.sum_congr rfl (fun r _ => hterm r), Finset.sum_const_zero,
      if_neg]
    intro hij
    apply hb
    rw [hij]

theorem U0_transpose_mul : U0ᵀ * U0 = 1 := by
  ext i j
  rw [U0_transpose_mul_apply, Matrix.one_apply]
  by_cases hb : i.val / 8 = j.val / 8
  · have hterm : ∀ r : Fin 8,
        P8 r ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩
            * U0 (e32 (⟨i.val / 8, by have h := i.isLt; omega⟩, r)) j
          = P8 r ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩
            * P8 r ⟨j.val % 8, Nat.mod_lt _ (by norm_num)⟩ := by
      intro r
      rw [U0_apply_e32_left, if_pos hb]
    rw [Finset.sum_congr rfl (fun r _ => hterm r)]
    have hPP : (P8ᵀ * P8) ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩
          ⟨j.val % 8, Nat.mod_lt _ (by norm_num)⟩
        = ∑ r : Fin 8, P8 r ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩
            * P8 r ⟨j.val % 8, Nat.mod_lt _ (by norm_num)⟩ := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro r _
      rw [Matrix.transpose_apply]
    rw [← hPP, P8_transpose_mul, Matrix.one_apply]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (by rw [hij] : (⟨i.val % 8,
        Nat.mod_lt _ (by norm_num)⟩ : Fin 8)
        = ⟨j.val % 8, Nat.mod_lt _ (by norm_num)⟩)]
    · rw [if_neg hij, if_neg]
      intro hcon
      apply hij
      apply Fin.ext
      have h1 : i.val % 8 = j.val % 8 := congrArg Fin.val hcon
      omega
  · have hterm : ∀ r : Fin 8,
        P8 r ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩
            * U0 (e32 (⟨i.val / 8, by have h := i.isLt; omega⟩, r)) j
          = 0 := by
      intro r
      rw [U0_apply_e32_left, if_neg, mul_zero]
      intro hcon
      apply hb
      exact hcon
    rw [Finset.sum_congr rfl (fun r _ => hterm r), Finset.sum_const_zero,
      if_neg]
    intro hij
    apply hb
    rw [hij]

/-! ## Condition (a): `U0` commutes with `gammaF` -/

/-- The grading is constant on 8-seat blocks. -/
theorem gammaF_block_eq {i j : Fin 32} (h : i.val / 8 = j.val / 8) :
    gammaF i i = gammaF j j := by
  have h8 : i.val < 8 ↔ j.val < 8 := by omega
  have h16 : i.val < 16 ↔ j.val < 16 := by omega
  have h24 : i.val < 24 ↔ j.val < 24 := by omega
  have gi : gammaF i i = if i.val < 8 then 1
      else if i.val < 16 then -1
      else if i.val < 24 then -1 else 1 := by
    unfold gammaF
    rw [dif_pos rfl]
  have gj : gammaF j j = if j.val < 8 then 1
      else if j.val < 16 then -1
      else if j.val < 24 then -1 else 1 := by
    unfold gammaF
    rw [dif_pos rfl]
  rw [gi, gj]
  split_ifs <;> simp_all

theorem U0_gammaF_comm : gammaF * U0 = U0 * gammaF := by
  ext i j
  rw [ThetLogos.gammaF_mul_apply, ThetLogos.mul_gammaF_apply]
  by_cases h0 : U0 i j = 0
  · rw [h0]; simp
  · have hb : i.val / 8 = j.val / 8 := by
      by_contra hc
      apply h0
      rw [U0_apply, if_neg hc]
    rw [gammaF_block_eq hb]
    exact mul_comm _ _

/-! ## Condition (b): `piOp U0 = U0ᵀ` -/

theorem partner_block (x : Fin 32) :
    (partner x).val / 8 = (x.val / 8 + 2) % 4 := by
  rw [partner_val_eq]
  split_ifs <;> omega

theorem partner_local (x : Fin 32) :
    (partner x).val % 8 = x.val % 8 := by
  rw [partner_val_eq]
  split_ifs <;> omega

theorem U0_partner (i j : Fin 32) :
    U0 (partner j) (partner i) = U0 j i := by
  have hcond : ((partner j).val / 8 = (partner i).val / 8)
      ↔ (j.val / 8 = i.val / 8) := by
    rw [partner_block, partner_block]
    have hi := i.isLt
    have hj := j.isLt
    constructor <;> intro h <;> omega
  rw [U0_apply, U0_apply]
  by_cases hc : j.val / 8 = i.val / 8
  · have hfinj : (⟨(partner j).val % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8)
        = ⟨j.val % 8, Nat.mod_lt _ (by norm_num)⟩ :=
      Fin.ext (partner_local j)
    have hfini : (⟨(partner i).val % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8)
        = ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩ :=
      Fin.ext (partner_local i)
    rw [if_pos (hcond.mpr hc), if_pos hc, hfinj, hfini]
  · rw [if_neg (fun h => hc (hcond.mp h)), if_neg hc]

theorem U0_piOp : piOp U0 = U0ᵀ := by
  ext i j
  show (UJ * U0ᵀ * UJ) i j = U0ᵀ i j
  rw [UJ_conj_apply, Matrix.transpose_apply, Matrix.transpose_apply]
  exact U0_partner i j

/-! ## Condition (c): `U0` commutes with `DF_oneGen` at all Yukawas -/

theorem dparSeat_local (x : Fin 32) :
    (ThetLogos.DialOneConjugationCounterexample.dparSeat x).val % 8
      = x.val % 8 := by
  unfold ThetLogos.DialOneConjugationCounterexample.dparSeat
  split_ifs <;> simp only [] <;> omega

theorem dparSeat_val (x : Fin 32) :
    (ThetLogos.DialOneConjugationCounterexample.dparSeat x).val
      = if x.val < 8 then x.val + 8
        else if x.val < 16 then x.val - 8
        else if x.val < 24 then x.val + 8
        else x.val - 8 := by
  unfold ThetLogos.DialOneConjugationCounterexample.dparSeat
  split_ifs <;> simp only [] <;> omega

/-- The Dirac-partner symmetry of the witness:
pulling `U0` across `dparSeat` on either side gives
the same entry. -/
theorem U0_dparSeat_key (i j : Fin 32) :
    U0 (ThetLogos.DialOneConjugationCounterexample.dparSeat i) j
      = U0 i (ThetLogos.DialOneConjugationCounterexample.dparSeat j) := by
  have hcond :
      ((ThetLogos.DialOneConjugationCounterexample.dparSeat i).val / 8
          = j.val / 8)
        ↔ (i.val / 8
          = (ThetLogos.DialOneConjugationCounterexample.dparSeat j).val
            / 8) := by
    have hi := i.isLt
    have hj := j.isLt
    rw [dparSeat_val, dparSeat_val]
    split_ifs <;> constructor <;> intro h <;> omega
  rw [U0_apply, U0_apply]
  by_cases hc : i.val / 8
      = (ThetLogos.DialOneConjugationCounterexample.dparSeat j).val / 8
  · have hfinL : (⟨(ThetLogos.DialOneConjugationCounterexample.dparSeat
          i).val % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8)
        = ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩ :=
      Fin.ext (dparSeat_local i)
    have hfinR : (⟨(ThetLogos.DialOneConjugationCounterexample.dparSeat
          j).val % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8)
        = ⟨j.val % 8, Nat.mod_lt _ (by norm_num)⟩ :=
      Fin.ext (dparSeat_local j)
    rw [if_pos (hcond.mpr hc), if_pos hc, hfinL, hfinR]
  · rw [if_neg (fun h => hc (hcond.mp h)), if_neg hc]

/-- The support of `P8`: off the diagonal it is
nonzero only on the equal-weight pair {2, 4}. -/
theorem P8_support {a b : Fin 8} (h : P8 a b ≠ 0) :
    a = b ∨ (a.val = 2 ∧ b.val = 4) ∨ (a.val = 4 ∧ b.val = 2) := by
  fin_cases a <;> fin_cases b <;> simp [P8] at h ⊢

/-- On the support of `P8`, the Dirac coefficient
(`dcoef`, a function of the seat's `val % 8` and its
Yukawa weight class) takes equal values: the only
off-diagonal support pair is {2, 4}, both of weight
Yu. -/
theorem dcoef_eq_of_P8_ne {i j : Fin 32}
    (Ynu Ye Yu Yd : ℝ)
    (h : P8 ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩
      ⟨j.val % 8, Nat.mod_lt _ (by norm_num)⟩ ≠ 0) :
    ThetLogos.DialOneConjugationCounterexample.dcoef Ynu Ye Yu Yd i
      = ThetLogos.DialOneConjugationCounterexample.dcoef Ynu Ye Yu Yd j := by
  rcases P8_support h with h1 | ⟨h2, h4⟩ | ⟨h4, h2⟩
  · have hm : i.val % 8 = j.val % 8 := congrArg Fin.val h1
    unfold ThetLogos.DialOneConjugationCounterexample.dcoef
    rw [hm]
  · have hm2 : i.val % 8 = 2 := h2
    have hm4 : j.val % 8 = 4 := h4
    unfold ThetLogos.DialOneConjugationCounterexample.dcoef
    rw [hm2, hm4]
    norm_num
  · have hm4 : i.val % 8 = 4 := h4
    have hm2 : j.val % 8 = 2 := h2
    unfold ThetLogos.DialOneConjugationCounterexample.dcoef
    rw [hm4, hm2]
    norm_num

theorem U0_df_comm (Ynu Ye Yu Yd : ℝ) :
    DF_oneGen Ynu Ye Yu Yd * U0
      = U0 * DF_oneGen Ynu Ye Yu Yd := by
  ext i j
  have hL : (DF_oneGen Ynu Ye Yu Yd * U0) i j
      = ThetLogos.DialOneConjugationCounterexample.dcoef Ynu Ye Yu Yd i
        * U0 (ThetLogos.DialOneConjugationCounterexample.dparSeat i) j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single
      (ThetLogos.DialOneConjugationCounterexample.dparSeat i)]
    · rw [ThetLogos.DialOneConjugationCounterexample.df_entry, if_pos rfl]
    · intro k _ hk
      rw [ThetLogos.DialOneConjugationCounterexample.df_entry,
        if_neg hk, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  have hR : (U0 * DF_oneGen Ynu Ye Yu Yd) i j
      = U0 i (ThetLogos.DialOneConjugationCounterexample.dparSeat j)
        * ThetLogos.DialOneConjugationCounterexample.dcoef
          Ynu Ye Yu Yd j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single
      (ThetLogos.DialOneConjugationCounterexample.dparSeat j)]
    · rw [ThetLogos.DialOneConjugationCounterexample.df_entry,
        if_pos (ThetLogos.DialOneConjugationCounterexample.dparSeat_involutive j).symm,
        ThetLogos.DialOneConjugationCounterexample.dcoef_dparSeat]
    · intro k _ hk
      have hne : ¬ (j
          = ThetLogos.DialOneConjugationCounterexample.dparSeat k) := by
        intro hcon
        apply hk
        have h2 : ThetLogos.DialOneConjugationCounterexample.dparSeat j
            = ThetLogos.DialOneConjugationCounterexample.dparSeat
              (ThetLogos.DialOneConjugationCounterexample.dparSeat k) :=
          congrArg ThetLogos.DialOneConjugationCounterexample.dparSeat hcon
        rw [ThetLogos.DialOneConjugationCounterexample.dparSeat_involutive]
          at h2
        exact h2.symm
      rw [ThetLogos.DialOneConjugationCounterexample.df_entry,
        if_neg hne, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  rw [hL, hR, U0_dparSeat_key]
  by_cases hz : U0 i
      (ThetLogos.DialOneConjugationCounterexample.dparSeat j) = 0
  · rw [hz]; simp
  · have hP : P8 ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩
        ⟨j.val % 8, Nat.mod_lt _ (by norm_num)⟩ ≠ 0 := by
      rw [U0_apply] at hz
      split_ifs at hz with hc
      · have hfin : (⟨(ThetLogos.DialOneConjugationCounterexample.dparSeat
              j).val % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8)
            = ⟨j.val % 8, Nat.mod_lt _ (by norm_num)⟩ :=
          Fin.ext (dparSeat_local j)
        rwa [hfin] at hz
      · simp at hz
    have hd := dcoef_eq_of_P8_ne Ynu Ye Yu Yd hP
    rw [hd]
    exact mul_comm _ _

/-! ## The verdict on gap (α) -/

/-- **The witness belongs to the centralizing class**:
transpose-unitarity, (a), (b), (c) — each proved in
its section above. -/
theorem U0_centralizing : CentralizingClass U0 :=
  ⟨U0_mul_transpose, U0_transpose_mul, U0_gammaF_comm, U0_piOp,
    U0_df_comm⟩

/-- **The witness is not real**: at the seat pair
(2, 4) of the first block, `(U0ᴴ) ⟨4⟩ ⟨2⟩ = −3i/4`
while `(U0ᵀ) ⟨4⟩ ⟨2⟩ = 3i/4`. -/
theorem U0_not_real : ¬ IsRealMat U0 := by
  intro h
  have h' : U0ᴴ = U0ᵀ := h
  have h2 := congrArg
    (fun M : Matrix (Fin 32) (Fin 32) ℂ =>
      M ⟨4, by norm_num⟩ ⟨2, by norm_num⟩) h'
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply] at h2
  have e : U0 ⟨2, by norm_num⟩ ⟨4, by norm_num⟩
      = (3 / 4 : ℂ) * Complex.I := rfl
  rw [e] at h2
  simp [Complex.ext_iff] at h2
  norm_num at h2

/-- **Gap (α) is closed, negatively**: reality does
NOT follow from the centralizing class. The
hypothesis `IsRealMat U` carried by
`DialOneGradeRConj.dialOneBase_preserved` and by the
capstone `strengthened_preserved_of_reality_pulled`
is essential and cannot be discharged from
(a)/(b)/(c). (This does not by itself decide
`PreservationQ` — see the header.) -/
theorem reality_does_not_follow :
    ¬ ∀ U : Matrix (Fin 32) (Fin 32) ℂ,
      CentralizingClass U → IsRealMat U :=
  fun h => U0_not_real (h U0 U0_centralizing)

end ThetLogos.DialOneGradeRReality
