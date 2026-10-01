import ThetLogos.CFKernelRetarget
import ThetLogos.CFKernel
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The 46 → 22 classification (capstone, Phase 2c)

Machine-checked capstone for the corrected classification.

**Status.** The original 46 → 10 claim (`cf_kernel_classification_46_10`,
`exotic_decomposition`, and downstream results) is flagged **UNSOUND AS STATED**
and left unmodified. This file proves a *new*, corrected classification as a new
theorem entry.

**What is proved.** Let `IsW22 D` be the repaired admissibility predicate
(repaired `OrderOneHolds` + `cfCommutatorMap D = 0` + self-adjointness +
J-compatibility + grading oddness). Then:

* **(A)** 10 explicit SM Yukawa directions satisfy `IsW22`
  (reusing the existing `OrderOneHolds_smDirac`, `smDirac_self_adjoint`,
  `smDirac_grading_odd`, `smDirac_IsJCompatible`, `smDirac_comm_cfMat`).
* **(B)** All 12 exotic survivors satisfy `IsW22` (repackaging the 12
  `*_orderOne` theorems of `CFKernelRetarget.lean` with their 48 companion lemmas).
* **(C)** The 22 directions are linearly independent over `ℝ`
  (`dirs22_independent`), via 11 disjoint entry pivots.
* **(D)** Classification (`cf_kernel_classification_46_22`): every `D`
  satisfying the repaired hypotheses lies in the real span of the 22 directions.

**Honesty ledger.** Step (D) is now unconditional: the dimension bound
`Module.finrank ℝ W22 ≤ 22` is proved in `CFKernelRetarget.lean`
(`finrank_W22_le_22`, via the injective pivot map into `Fin 11 → ℂ`),
so no numerical census hypothesis is needed. The old 46 → 10 chain
remains flagged unsound-as-stated and is not modified (relabeling rule).

No `sorry`s. The old flagged chain is not modified.
-/

namespace ThetLogos

open Matrix

/-! ## §0. The repaired solution predicate -/

/-- Repaired admissibility: the real-linear physical constraints
(self-adjointness, J-compatibility, grading oddness) plus the repaired
`OrderOneHolds` and the `cfMat`-commutant condition. -/
def IsW22 (D : Matrix I32 I32 ℂ) : Prop :=
  OrderOneHolds D ∧
  cfCommutatorMap D = 0 ∧
  D.conjTranspose = D ∧
  IsJCompatible D ∧
  gammaF * D + D * gammaF = 0

/-! ## §1. Entry infrastructure for the SM pivots -/

/-- Entry of `buildDirac` in the A region (i in [0,8), j in [8,16)). -/
theorem buildDirac_A_entry (A B C E : Block8) (i j : I32)
    (hi1 : i.val < 8) (hj1 : ¬j.val < 8) (hj2 : j.val < 16) :
    buildDirac A B C E i j = A ⟨i.val, hi1⟩ ⟨j.val - 8, by omega⟩ := by
  unfold buildDirac
  simp only []
  simp [hi1, hj1, hj2]

/-- The A-block of `smDirac` is the diagonal Yukawa matrix; pivot entries. -/
theorem smDirac_08 (yNu yE yU yD yR : ℂ) :
    smDirac yNu yE yU yD yR 0 8 = yNu := by
  have h := buildDirac_A_entry (yukawaBlock yNu yE yU yD)
    ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)) 0 (majoranaBlock yR)
    0 8 (by decide) (by decide) (by decide)
  unfold smDirac yukawaBlock at h ⊢
  rw [h, Matrix.diagonal_apply]
  simp

theorem smDirac_19 (yNu yE yU yD yR : ℂ) :
    smDirac yNu yE yU yD yR 1 9 = yE := by
  have h := buildDirac_A_entry (yukawaBlock yNu yE yU yD)
    ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)) 0 (majoranaBlock yR)
    1 9 (by decide) (by decide) (by decide)
  unfold smDirac yukawaBlock at h ⊢
  rw [h, Matrix.diagonal_apply]
  simp

theorem smDirac_2_10 (yNu yE yU yD yR : ℂ) :
    smDirac yNu yE yU yD yR 2 10 = yU := by
  have h := buildDirac_A_entry (yukawaBlock yNu yE yU yD)
    ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)) 0 (majoranaBlock yR)
    2 10 (by decide) (by decide) (by decide)
  unfold smDirac yukawaBlock at h ⊢
  rw [h, Matrix.diagonal_apply]
  simp

theorem smDirac_3_11 (yNu yE yU yD yR : ℂ) :
    smDirac yNu yE yU yD yR 3 11 = yD := by
  have h := buildDirac_A_entry (yukawaBlock yNu yE yU yD)
    ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)) 0 (majoranaBlock yR)
    3 11 (by decide) (by decide) (by decide)
  unfold smDirac yukawaBlock at h ⊢
  rw [h, Matrix.diagonal_apply]
  simp

theorem smDirac_24_8 (yNu yE yU yD yR : ℂ) :
    smDirac yNu yE yU yD yR 24 8 = yR := by
  have h := buildDirac_E_entry (yukawaBlock yNu yE yU yD)
    ((yukawaBlock yNu yE yU yD).map (starRingEnd ℂ)) 0 (majoranaBlock yR)
    24 8 (by decide) (by decide) (by decide) (by decide) (by decide)
  unfold smDirac at h ⊢
  rw [h]
  unfold majoranaBlock
  rw [Matrix.diagonal_apply]
  simp

/-- The SM Dirac operator vanishes at the exotic pivots (support disjointness). -/
theorem smDirac_09_zero (yNu yE yU yD yR : ℂ) :
    smDirac yNu yE yU yD yR 0 9 = 0 := by
  by_contra h
  have hs := smDirac_supp_aux yNu yE yU yD yR 0 9 h
  simp at hs

theorem smDirac_18_zero (yNu yE yU yD yR : ℂ) :
    smDirac yNu yE yU yD yR 1 8 = 0 := by
  by_contra h
  have hs := smDirac_supp_aux yNu yE yU yD yR 1 8 h
  simp at hs

theorem smDirac_2_11_zero (yNu yE yU yD yR : ℂ) :
    smDirac yNu yE yU yD yR 2 11 = 0 := by
  by_contra h
  have hs := smDirac_supp_aux yNu yE yU yD yR 2 11 h
  simp at hs

theorem smDirac_3_10_zero (yNu yE yU yD yR : ℂ) :
    smDirac yNu yE yU yD yR 3 10 = 0 := by
  by_contra h
  have hs := smDirac_supp_aux yNu yE yU yD yR 3 10 h
  simp at hs

theorem smDirac_8_25_zero (yNu yE yU yD yR : ℂ) :
    smDirac yNu yE yU yD yR 8 25 = 0 := by
  by_contra h
  have hs := smDirac_supp_aux yNu yE yU yD yR 8 25 h
  simp at hs

theorem smDirac_9_25_zero (yNu yE yU yD yR : ℂ) :
    smDirac yNu yE yU yD yR 9 25 = 0 := by
  by_contra h
  have hs := smDirac_supp_aux yNu yE yU yD yR 9 25 h
  simp at hs

/-! ## §2. STEP A: the 10 SM directions satisfy `IsW22` -/

def smDirReNu : Matrix I32 I32 ℂ := smDirac 1 0 0 0 0
def smDirImNu : Matrix I32 I32 ℂ := smDirac Complex.I 0 0 0 0
def smDirReE : Matrix I32 I32 ℂ := smDirac 0 1 0 0 0
def smDirImE : Matrix I32 I32 ℂ := smDirac 0 Complex.I 0 0 0
def smDirReU : Matrix I32 I32 ℂ := smDirac 0 0 1 0 0
def smDirImU : Matrix I32 I32 ℂ := smDirac 0 0 Complex.I 0 0
def smDirReD : Matrix I32 I32 ℂ := smDirac 0 0 0 1 0
def smDirImD : Matrix I32 I32 ℂ := smDirac 0 0 0 Complex.I 0
def smDirReR : Matrix I32 I32 ℂ := smDirac 0 0 0 0 1
def smDirImR : Matrix I32 I32 ℂ := smDirac 0 0 0 0 Complex.I

theorem smDirReNu_mem : IsW22 smDirReNu := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact OrderOneHolds_smDirac 1 0 0 0 0
  · show smDirac 1 0 0 0 0 * cfMat - cfMat * smDirac 1 0 0 0 0 = 0
    exact smDirac_comm_cfMat 1 0 0 0 0
  · show (smDirac 1 0 0 0 0).conjTranspose = smDirac 1 0 0 0 0
    exact smDirac_self_adjoint 1 0 0 0 0
  · exact smDirac_IsJCompatible 1 0 0 0 0
  · show gammaF * smDirac 1 0 0 0 0 + smDirac 1 0 0 0 0 * gammaF = 0
    exact smDirac_grading_odd 1 0 0 0 0

theorem smDirImNu_mem : IsW22 smDirImNu := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact OrderOneHolds_smDirac Complex.I 0 0 0 0
  · show smDirac Complex.I 0 0 0 0 * cfMat - cfMat * smDirac Complex.I 0 0 0 0 = 0
    exact smDirac_comm_cfMat Complex.I 0 0 0 0
  · show (smDirac Complex.I 0 0 0 0).conjTranspose = smDirac Complex.I 0 0 0 0
    exact smDirac_self_adjoint Complex.I 0 0 0 0
  · exact smDirac_IsJCompatible Complex.I 0 0 0 0
  · show gammaF * smDirac Complex.I 0 0 0 0 + smDirac Complex.I 0 0 0 0 * gammaF = 0
    exact smDirac_grading_odd Complex.I 0 0 0 0

theorem smDirReE_mem : IsW22 smDirReE := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact OrderOneHolds_smDirac 0 1 0 0 0
  · show smDirac 0 1 0 0 0 * cfMat - cfMat * smDirac 0 1 0 0 0 = 0
    exact smDirac_comm_cfMat 0 1 0 0 0
  · show (smDirac 0 1 0 0 0).conjTranspose = smDirac 0 1 0 0 0
    exact smDirac_self_adjoint 0 1 0 0 0
  · exact smDirac_IsJCompatible 0 1 0 0 0
  · show gammaF * smDirac 0 1 0 0 0 + smDirac 0 1 0 0 0 * gammaF = 0
    exact smDirac_grading_odd 0 1 0 0 0

theorem smDirImE_mem : IsW22 smDirImE := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact OrderOneHolds_smDirac 0 Complex.I 0 0 0
  · show smDirac 0 Complex.I 0 0 0 * cfMat - cfMat * smDirac 0 Complex.I 0 0 0 = 0
    exact smDirac_comm_cfMat 0 Complex.I 0 0 0
  · show (smDirac 0 Complex.I 0 0 0).conjTranspose = smDirac 0 Complex.I 0 0 0
    exact smDirac_self_adjoint 0 Complex.I 0 0 0
  · exact smDirac_IsJCompatible 0 Complex.I 0 0 0
  · show gammaF * smDirac 0 Complex.I 0 0 0 + smDirac 0 Complex.I 0 0 0 * gammaF = 0
    exact smDirac_grading_odd 0 Complex.I 0 0 0

theorem smDirReU_mem : IsW22 smDirReU := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact OrderOneHolds_smDirac 0 0 1 0 0
  · show smDirac 0 0 1 0 0 * cfMat - cfMat * smDirac 0 0 1 0 0 = 0
    exact smDirac_comm_cfMat 0 0 1 0 0
  · show (smDirac 0 0 1 0 0).conjTranspose = smDirac 0 0 1 0 0
    exact smDirac_self_adjoint 0 0 1 0 0
  · exact smDirac_IsJCompatible 0 0 1 0 0
  · show gammaF * smDirac 0 0 1 0 0 + smDirac 0 0 1 0 0 * gammaF = 0
    exact smDirac_grading_odd 0 0 1 0 0

theorem smDirImU_mem : IsW22 smDirImU := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact OrderOneHolds_smDirac 0 0 Complex.I 0 0
  · show smDirac 0 0 Complex.I 0 0 * cfMat - cfMat * smDirac 0 0 Complex.I 0 0 = 0
    exact smDirac_comm_cfMat 0 0 Complex.I 0 0
  · show (smDirac 0 0 Complex.I 0 0).conjTranspose = smDirac 0 0 Complex.I 0 0
    exact smDirac_self_adjoint 0 0 Complex.I 0 0
  · exact smDirac_IsJCompatible 0 0 Complex.I 0 0
  · show gammaF * smDirac 0 0 Complex.I 0 0 + smDirac 0 0 Complex.I 0 0 * gammaF = 0
    exact smDirac_grading_odd 0 0 Complex.I 0 0

theorem smDirReD_mem : IsW22 smDirReD := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact OrderOneHolds_smDirac 0 0 0 1 0
  · show smDirac 0 0 0 1 0 * cfMat - cfMat * smDirac 0 0 0 1 0 = 0
    exact smDirac_comm_cfMat 0 0 0 1 0
  · show (smDirac 0 0 0 1 0).conjTranspose = smDirac 0 0 0 1 0
    exact smDirac_self_adjoint 0 0 0 1 0
  · exact smDirac_IsJCompatible 0 0 0 1 0
  · show gammaF * smDirac 0 0 0 1 0 + smDirac 0 0 0 1 0 * gammaF = 0
    exact smDirac_grading_odd 0 0 0 1 0

theorem smDirImD_mem : IsW22 smDirImD := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact OrderOneHolds_smDirac 0 0 0 Complex.I 0
  · show smDirac 0 0 0 Complex.I 0 * cfMat - cfMat * smDirac 0 0 0 Complex.I 0 = 0
    exact smDirac_comm_cfMat 0 0 0 Complex.I 0
  · show (smDirac 0 0 0 Complex.I 0).conjTranspose = smDirac 0 0 0 Complex.I 0
    exact smDirac_self_adjoint 0 0 0 Complex.I 0
  · exact smDirac_IsJCompatible 0 0 0 Complex.I 0
  · show gammaF * smDirac 0 0 0 Complex.I 0 + smDirac 0 0 0 Complex.I 0 * gammaF = 0
    exact smDirac_grading_odd 0 0 0 Complex.I 0

theorem smDirReR_mem : IsW22 smDirReR := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact OrderOneHolds_smDirac 0 0 0 0 1
  · show smDirac 0 0 0 0 1 * cfMat - cfMat * smDirac 0 0 0 0 1 = 0
    exact smDirac_comm_cfMat 0 0 0 0 1
  · show (smDirac 0 0 0 0 1).conjTranspose = smDirac 0 0 0 0 1
    exact smDirac_self_adjoint 0 0 0 0 1
  · exact smDirac_IsJCompatible 0 0 0 0 1
  · show gammaF * smDirac 0 0 0 0 1 + smDirac 0 0 0 0 1 * gammaF = 0
    exact smDirac_grading_odd 0 0 0 0 1

theorem smDirImR_mem : IsW22 smDirImR := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact OrderOneHolds_smDirac 0 0 0 0 Complex.I
  · show smDirac 0 0 0 0 Complex.I * cfMat - cfMat * smDirac 0 0 0 0 Complex.I = 0
    exact smDirac_comm_cfMat 0 0 0 0 Complex.I
  · show (smDirac 0 0 0 0 Complex.I).conjTranspose = smDirac 0 0 0 0 Complex.I
    exact smDirac_self_adjoint 0 0 0 0 Complex.I
  · exact smDirac_IsJCompatible 0 0 0 0 Complex.I
  · show gammaF * smDirac 0 0 0 0 Complex.I + smDirac 0 0 0 0 Complex.I * gammaF = 0
    exact smDirac_grading_odd 0 0 0 0 Complex.I

/-! ## The 12 exotic survivors satisfy `IsW22` (repackaging `CFKernelRetarget`) -/

theorem exoticReNuLeR_mem : IsW22 exoticReNuLeR :=
  ⟨exoticReNuLeR_orderOne,
   by show exoticReNuLeR * cfMat - cfMat * exoticReNuLeR = 0; exact exoticReNuLeR_cfMat,
   exoticReNuLeR_selfAdjoint, exoticReNuLeR_Jcompat, exoticReNuLeR_gradingOdd⟩

theorem exoticImNuLeR_mem : IsW22 exoticImNuLeR :=
  ⟨exoticImNuLeR_orderOne,
   by show exoticImNuLeR * cfMat - cfMat * exoticImNuLeR = 0; exact exoticImNuLeR_cfMat,
   exoticImNuLeR_selfAdjoint, exoticImNuLeR_Jcompat, exoticImNuLeR_gradingOdd⟩

theorem exoticReELNuR_mem : IsW22 exoticReELNuR :=
  ⟨exoticReELNuR_orderOne,
   by show exoticReELNuR * cfMat - cfMat * exoticReELNuR = 0; exact exoticReELNuR_cfMat,
   exoticReELNuR_selfAdjoint, exoticReELNuR_Jcompat, exoticReELNuR_gradingOdd⟩

theorem exoticImELNuR_mem : IsW22 exoticImELNuR :=
  ⟨exoticImELNuR_orderOne,
   by show exoticImELNuR * cfMat - cfMat * exoticImELNuR = 0; exact exoticImELNuR_cfMat,
   exoticImELNuR_selfAdjoint, exoticImELNuR_Jcompat, exoticImELNuR_gradingOdd⟩

theorem exoticReULDR_mem : IsW22 exoticReULDR :=
  ⟨exoticReULDR_orderOne,
   by show exoticReULDR * cfMat - cfMat * exoticReULDR = 0; exact exoticReULDR_cfMat,
   exoticReULDR_selfAdjoint, exoticReULDR_Jcompat, exoticReULDR_gradingOdd⟩

theorem exoticImULDR_mem : IsW22 exoticImULDR :=
  ⟨exoticImULDR_orderOne,
   by show exoticImULDR * cfMat - cfMat * exoticImULDR = 0; exact exoticImULDR_cfMat,
   exoticImULDR_selfAdjoint, exoticImULDR_Jcompat, exoticImULDR_gradingOdd⟩

theorem exoticReDLUR_mem : IsW22 exoticReDLUR :=
  ⟨exoticReDLUR_orderOne,
   by show exoticReDLUR * cfMat - cfMat * exoticReDLUR = 0; exact exoticReDLUR_cfMat,
   exoticReDLUR_selfAdjoint, exoticReDLUR_Jcompat, exoticReDLUR_gradingOdd⟩

theorem exoticImDLUR_mem : IsW22 exoticImDLUR :=
  ⟨exoticImDLUR_orderOne,
   by show exoticImDLUR * cfMat - cfMat * exoticImDLUR = 0; exact exoticImDLUR_cfMat,
   exoticImDLUR_selfAdjoint, exoticImDLUR_Jcompat, exoticImDLUR_gradingOdd⟩

theorem exoticReNuREbarR_mem : IsW22 exoticReNuREbarR :=
  ⟨exoticReNuREbarR_orderOne,
   by show exoticReNuREbarR * cfMat - cfMat * exoticReNuREbarR = 0; exact exoticReNuREbarR_cfMat,
   exoticReNuREbarR_selfAdjoint, exoticReNuREbarR_Jcompat, exoticReNuREbarR_gradingOdd⟩

theorem exoticImNuREbarR_mem : IsW22 exoticImNuREbarR :=
  ⟨exoticImNuREbarR_orderOne,
   by show exoticImNuREbarR * cfMat - cfMat * exoticImNuREbarR = 0; exact exoticImNuREbarR_cfMat,
   exoticImNuREbarR_selfAdjoint, exoticImNuREbarR_Jcompat, exoticImNuREbarR_gradingOdd⟩

theorem exoticReEREbarR_mem : IsW22 exoticReEREbarR :=
  ⟨exoticReEREbarR_orderOne,
   by show exoticReEREbarR * cfMat - cfMat * exoticReEREbarR = 0; exact exoticReEREbarR_cfMat,
   exoticReEREbarR_selfAdjoint, exoticReEREbarR_Jcompat, exoticReEREbarR_gradingOdd⟩

theorem exoticImEREbarR_mem : IsW22 exoticImEREbarR :=
  ⟨exoticImEREbarR_orderOne,
   by show exoticImEREbarR * cfMat - cfMat * exoticImEREbarR = 0; exact exoticImEREbarR_cfMat,
   exoticImEREbarR_selfAdjoint, exoticImEREbarR_Jcompat, exoticImEREbarR_gradingOdd⟩

/-! ## §3. The 22-direction family -/

/-- The 22 basis directions: indices 0–9 are the SM real/imaginary Yukawa
directions, indices 10–21 are the 12 exotic survivors. -/
def dirs22Aux : Nat → Matrix I32 I32 ℂ
  | 0 => smDirReNu
  | 1 => smDirImNu
  | 2 => smDirReE
  | 3 => smDirImE
  | 4 => smDirReU
  | 5 => smDirImU
  | 6 => smDirReD
  | 7 => smDirImD
  | 8 => smDirReR
  | 9 => smDirImR
  | 10 => exoticReNuLeR
  | 11 => exoticImNuLeR
  | 12 => exoticReELNuR
  | 13 => exoticImELNuR
  | 14 => exoticReULDR
  | 15 => exoticImULDR
  | 16 => exoticReDLUR
  | 17 => exoticImDLUR
  | 18 => exoticReNuREbarR
  | 19 => exoticImNuREbarR
  | 20 => exoticReEREbarR
  | 21 => exoticImEREbarR
  | _ + 22 => 0

def dirs22 (k : Fin 22) : Matrix I32 I32 ℂ := dirs22Aux k.val

theorem dirs22_mem (k : Fin 22) : IsW22 (dirs22 k) := by
  fin_cases k
  · exact smDirReNu_mem
  · exact smDirImNu_mem
  · exact smDirReE_mem
  · exact smDirImE_mem
  · exact smDirReU_mem
  · exact smDirImU_mem
  · exact smDirReD_mem
  · exact smDirImD_mem
  · exact smDirReR_mem
  · exact smDirImR_mem
  · exact exoticReNuLeR_mem
  · exact exoticImNuLeR_mem
  · exact exoticReELNuR_mem
  · exact exoticImELNuR_mem
  · exact exoticReULDR_mem
  · exact exoticImULDR_mem
  · exact exoticReDLUR_mem
  · exact exoticImDLUR_mem
  · exact exoticReNuREbarR_mem
  · exact exoticImNuREbarR_mem
  · exact exoticReEREbarR_mem
  · exact exoticImEREbarR_mem

/-! ## §4. STEP B: linear independence of the 22 directions -/

/-- Pivot extraction: if a pivot entry `(r,c)` sees only the pair `(a,b)` with
values `1` and `Complex.I`, then a vanishing real-linear combination has
`g a = 0` and `g b = 0`. -/
theorem pivot_extract (r c : I32) (a b : Fin 22) (hab : a ≠ b)
    (hva : dirs22 a r c = 1) (hvb : dirs22 b r c = Complex.I)
    (hvan : ∀ i : Fin 22, i ≠ a → i ≠ b → dirs22 i r c = 0)
    (g : Fin 22 → ℝ) (hg : ∑ i, g i • dirs22 i = 0) :
    g a = 0 ∧ g b = 0 := by
  have hP : ∑ i : Fin 22, (g i • dirs22 i) r c = 0 := by
    have h := congrFun (congrFun hg r) c
    rwa [Matrix.sum_apply] at h
  have hcollapse : ∑ i : Fin 22, (g i • dirs22 i) r c
      = (g a • dirs22 a) r c + (g b • dirs22 b) r c := by
    have h1 : ∑ i : Fin 22, (g i • dirs22 i) r c
        = ∑ i ∈ ({a, b} : Finset (Fin 22)), (g i • dirs22 i) r c := by
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro x _ hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      have hx' := not_or.mp hx
      have hv := hvan x hx'.1 hx'.2
      show (g x) • ((dirs22 x) r c) = 0
      rw [hv, smul_zero]
    have h2 : ∑ i ∈ ({a, b} : Finset (Fin 22)), (g i • dirs22 i) r c
        = (g a • dirs22 a) r c + (g b • dirs22 b) r c :=
      Finset.sum_pair hab
    rw [h1, h2]
  rw [hcollapse] at hP
  have hP2 : (g a) • (dirs22 a r c) + (g b) • (dirs22 b r c) = 0 := hP
  rw [hva, hvb] at hP2
  have h' : ((g a : ℝ) : ℂ) + ((g b : ℝ) : ℂ) * Complex.I = 0 := by
    have e1 : (g a) • (1:ℂ) = ((g a : ℝ) : ℂ) := by simp
    have e2 : (g b) • Complex.I = ((g b : ℝ) : ℂ) * Complex.I := by simp
    rw [e1, e2] at hP2
    simpa using hP2
  have hre := congrArg Complex.re h'
  have him := congrArg Complex.im h'
  simp at hre him
  exact ⟨hre, him⟩

/-! ### Pivot 1: (0,8), active pair (0,1) — SM y_ν -/

theorem hva_08 : dirs22 0 0 8 = 1 := by
  show smDirac 1 0 0 0 0 0 8 = 1
  exact smDirac_08 1 0 0 0 0

theorem hvb_08 : dirs22 1 0 8 = Complex.I := by
  show smDirac Complex.I 0 0 0 0 0 8 = Complex.I
  exact smDirac_08 Complex.I 0 0 0 0

theorem hvan_08 : ∀ i : Fin 22, i ≠ 0 → i ≠ 1 → dirs22 i 0 8 = 0 := by
  intro i h0 h1
  fin_cases i
  · exact absurd rfl h0
  · exact absurd rfl h1
  · show smDirac 0 1 0 0 0 0 8 = 0; exact smDirac_08 0 1 0 0 0
  · show smDirac 0 Complex.I 0 0 0 0 8 = 0; exact smDirac_08 0 Complex.I 0 0 0
  · show smDirac 0 0 1 0 0 0 8 = 0; exact smDirac_08 0 0 1 0 0
  · show smDirac 0 0 Complex.I 0 0 0 8 = 0; exact smDirac_08 0 0 Complex.I 0 0
  · show smDirac 0 0 0 1 0 0 8 = 0; exact smDirac_08 0 0 0 1 0
  · show smDirac 0 0 0 Complex.I 0 0 8 = 0; exact smDirac_08 0 0 0 Complex.I 0
  · show smDirac 0 0 0 0 1 0 8 = 0; exact smDirac_08 0 0 0 0 1
  · show smDirac 0 0 0 0 Complex.I 0 8 = 0; exact smDirac_08 0 0 0 0 Complex.I
  · show exoticReNuLeR 0 8 = 0; simp [exoticReNuLeR]
  · show exoticImNuLeR 0 8 = 0; simp [exoticImNuLeR]
  · show exoticReELNuR 0 8 = 0; simp [exoticReELNuR]
  · show exoticImELNuR 0 8 = 0; simp [exoticImELNuR]
  · show exoticReULDR 0 8 = 0; simp [exoticReULDR]
  · show exoticImULDR 0 8 = 0; simp [exoticImULDR]
  · show exoticReDLUR 0 8 = 0; simp [exoticReDLUR]
  · show exoticImDLUR 0 8 = 0; simp [exoticImDLUR]
  · show exoticReNuREbarR 0 8 = 0; simp [exoticReNuREbarR]
  · show exoticImNuREbarR 0 8 = 0; simp [exoticImNuREbarR]
  · show exoticReEREbarR 0 8 = 0; simp [exoticReEREbarR]
  · show exoticImEREbarR 0 8 = 0; simp [exoticImEREbarR]

/-! ### Pivot 2: (1,9), active pair (2,3) — SM y_E -/

theorem hva_19 : dirs22 2 1 9 = 1 := by
  show smDirac 0 1 0 0 0 1 9 = 1
  exact smDirac_19 0 1 0 0 0

theorem hvb_19 : dirs22 3 1 9 = Complex.I := by
  show smDirac 0 Complex.I 0 0 0 1 9 = Complex.I
  exact smDirac_19 0 Complex.I 0 0 0

theorem hvan_19 : ∀ i : Fin 22, i ≠ 2 → i ≠ 3 → dirs22 i 1 9 = 0 := by
  intro i h2 h3
  fin_cases i
  · show smDirac 1 0 0 0 0 1 9 = 0; exact smDirac_19 1 0 0 0 0
  · show smDirac Complex.I 0 0 0 0 1 9 = 0; exact smDirac_19 Complex.I 0 0 0 0
  · exact absurd rfl h2
  · exact absurd rfl h3
  · show smDirac 0 0 1 0 0 1 9 = 0; exact smDirac_19 0 0 1 0 0
  · show smDirac 0 0 Complex.I 0 0 1 9 = 0; exact smDirac_19 0 0 Complex.I 0 0
  · show smDirac 0 0 0 1 0 1 9 = 0; exact smDirac_19 0 0 0 1 0
  · show smDirac 0 0 0 Complex.I 0 1 9 = 0; exact smDirac_19 0 0 0 Complex.I 0
  · show smDirac 0 0 0 0 1 1 9 = 0; exact smDirac_19 0 0 0 0 1
  · show smDirac 0 0 0 0 Complex.I 1 9 = 0; exact smDirac_19 0 0 0 0 Complex.I
  · show exoticReNuLeR 1 9 = 0; simp [exoticReNuLeR]
  · show exoticImNuLeR 1 9 = 0; simp [exoticImNuLeR]
  · show exoticReELNuR 1 9 = 0; simp [exoticReELNuR]
  · show exoticImELNuR 1 9 = 0; simp [exoticImELNuR]
  · show exoticReULDR 1 9 = 0; simp [exoticReULDR]
  · show exoticImULDR 1 9 = 0; simp [exoticImULDR]
  · show exoticReDLUR 1 9 = 0; simp [exoticReDLUR]
  · show exoticImDLUR 1 9 = 0; simp [exoticImDLUR]
  · show exoticReNuREbarR 1 9 = 0; simp [exoticReNuREbarR]
  · show exoticImNuREbarR 1 9 = 0; simp [exoticImNuREbarR]
  · show exoticReEREbarR 1 9 = 0; simp [exoticReEREbarR]
  · show exoticImEREbarR 1 9 = 0; simp [exoticImEREbarR]

/-! ### Pivot 3: (2,10), active pair (4,5) — SM y_U -/

theorem hva_2_10 : dirs22 4 2 10 = 1 := by
  show smDirac 0 0 1 0 0 2 10 = 1
  exact smDirac_2_10 0 0 1 0 0

theorem hvb_2_10 : dirs22 5 2 10 = Complex.I := by
  show smDirac 0 0 Complex.I 0 0 2 10 = Complex.I
  exact smDirac_2_10 0 0 Complex.I 0 0

theorem hvan_2_10 : ∀ i : Fin 22, i ≠ 4 → i ≠ 5 → dirs22 i 2 10 = 0 := by
  intro i h4 h5
  fin_cases i
  · show smDirac 1 0 0 0 0 2 10 = 0; exact smDirac_2_10 1 0 0 0 0
  · show smDirac Complex.I 0 0 0 0 2 10 = 0; exact smDirac_2_10 Complex.I 0 0 0 0
  · show smDirac 0 1 0 0 0 2 10 = 0; exact smDirac_2_10 0 1 0 0 0
  · show smDirac 0 Complex.I 0 0 0 2 10 = 0; exact smDirac_2_10 0 Complex.I 0 0 0
  · exact absurd rfl h4
  · exact absurd rfl h5
  · show smDirac 0 0 0 1 0 2 10 = 0; exact smDirac_2_10 0 0 0 1 0
  · show smDirac 0 0 0 Complex.I 0 2 10 = 0; exact smDirac_2_10 0 0 0 Complex.I 0
  · show smDirac 0 0 0 0 1 2 10 = 0; exact smDirac_2_10 0 0 0 0 1
  · show smDirac 0 0 0 0 Complex.I 2 10 = 0; exact smDirac_2_10 0 0 0 0 Complex.I
  · show exoticReNuLeR 2 10 = 0; simp [exoticReNuLeR]
  · show exoticImNuLeR 2 10 = 0; simp [exoticImNuLeR]
  · show exoticReELNuR 2 10 = 0; simp [exoticReELNuR]
  · show exoticImELNuR 2 10 = 0; simp [exoticImELNuR]
  · show exoticReULDR 2 10 = 0; simp [exoticReULDR]
  · show exoticImULDR 2 10 = 0; simp [exoticImULDR]
  · show exoticReDLUR 2 10 = 0; simp [exoticReDLUR]
  · show exoticImDLUR 2 10 = 0; simp [exoticImDLUR]
  · show exoticReNuREbarR 2 10 = 0; simp [exoticReNuREbarR]
  · show exoticImNuREbarR 2 10 = 0; simp [exoticImNuREbarR]
  · show exoticReEREbarR 2 10 = 0; simp [exoticReEREbarR]
  · show exoticImEREbarR 2 10 = 0; simp [exoticImEREbarR]

/-! ### Pivot 4: (3,11), active pair (6,7) — SM y_D -/

theorem hva_3_11 : dirs22 6 3 11 = 1 := by
  show smDirac 0 0 0 1 0 3 11 = 1
  exact smDirac_3_11 0 0 0 1 0

theorem hvb_3_11 : dirs22 7 3 11 = Complex.I := by
  show smDirac 0 0 0 Complex.I 0 3 11 = Complex.I
  exact smDirac_3_11 0 0 0 Complex.I 0

theorem hvan_3_11 : ∀ i : Fin 22, i ≠ 6 → i ≠ 7 → dirs22 i 3 11 = 0 := by
  intro i h6 h7
  fin_cases i
  · show smDirac 1 0 0 0 0 3 11 = 0; exact smDirac_3_11 1 0 0 0 0
  · show smDirac Complex.I 0 0 0 0 3 11 = 0; exact smDirac_3_11 Complex.I 0 0 0 0
  · show smDirac 0 1 0 0 0 3 11 = 0; exact smDirac_3_11 0 1 0 0 0
  · show smDirac 0 Complex.I 0 0 0 3 11 = 0; exact smDirac_3_11 0 Complex.I 0 0 0
  · show smDirac 0 0 1 0 0 3 11 = 0; exact smDirac_3_11 0 0 1 0 0
  · show smDirac 0 0 Complex.I 0 0 3 11 = 0; exact smDirac_3_11 0 0 Complex.I 0 0
  · exact absurd rfl h6
  · exact absurd rfl h7
  · show smDirac 0 0 0 0 1 3 11 = 0; exact smDirac_3_11 0 0 0 0 1
  · show smDirac 0 0 0 0 Complex.I 3 11 = 0; exact smDirac_3_11 0 0 0 0 Complex.I
  · show exoticReNuLeR 3 11 = 0; simp [exoticReNuLeR]
  · show exoticImNuLeR 3 11 = 0; simp [exoticImNuLeR]
  · show exoticReELNuR 3 11 = 0; simp [exoticReELNuR]
  · show exoticImELNuR 3 11 = 0; simp [exoticImELNuR]
  · show exoticReULDR 3 11 = 0; simp [exoticReULDR]
  · show exoticImULDR 3 11 = 0; simp [exoticImULDR]
  · show exoticReDLUR 3 11 = 0; simp [exoticReDLUR]
  · show exoticImDLUR 3 11 = 0; simp [exoticImDLUR]
  · show exoticReNuREbarR 3 11 = 0; simp [exoticReNuREbarR]
  · show exoticImNuREbarR 3 11 = 0; simp [exoticImNuREbarR]
  · show exoticReEREbarR 3 11 = 0; simp [exoticReEREbarR]
  · show exoticImEREbarR 3 11 = 0; simp [exoticImEREbarR]

/-! ### Pivot 5: (24,8), active pair (8,9) — SM y_R -/

theorem hva_24_8 : dirs22 8 24 8 = 1 := by
  show smDirac 0 0 0 0 1 24 8 = 1
  exact smDirac_24_8 0 0 0 0 1

theorem hvb_24_8 : dirs22 9 24 8 = Complex.I := by
  show smDirac 0 0 0 0 Complex.I 24 8 = Complex.I
  exact smDirac_24_8 0 0 0 0 Complex.I

theorem hvan_24_8 : ∀ i : Fin 22, i ≠ 8 → i ≠ 9 → dirs22 i 24 8 = 0 := by
  intro i h8 h9
  fin_cases i
  · show smDirac 1 0 0 0 0 24 8 = 0; exact smDirac_24_8 1 0 0 0 0
  · show smDirac Complex.I 0 0 0 0 24 8 = 0; exact smDirac_24_8 Complex.I 0 0 0 0
  · show smDirac 0 1 0 0 0 24 8 = 0; exact smDirac_24_8 0 1 0 0 0
  · show smDirac 0 Complex.I 0 0 0 24 8 = 0; exact smDirac_24_8 0 Complex.I 0 0 0
  · show smDirac 0 0 1 0 0 24 8 = 0; exact smDirac_24_8 0 0 1 0 0
  · show smDirac 0 0 Complex.I 0 0 24 8 = 0; exact smDirac_24_8 0 0 Complex.I 0 0
  · show smDirac 0 0 0 1 0 24 8 = 0; exact smDirac_24_8 0 0 0 1 0
  · show smDirac 0 0 0 Complex.I 0 24 8 = 0; exact smDirac_24_8 0 0 0 Complex.I 0
  · exact absurd rfl h8
  · exact absurd rfl h9
  · show exoticReNuLeR 24 8 = 0; simp [exoticReNuLeR]
  · show exoticImNuLeR 24 8 = 0; simp [exoticImNuLeR]
  · show exoticReELNuR 24 8 = 0; simp [exoticReELNuR]
  · show exoticImELNuR 24 8 = 0; simp [exoticImELNuR]
  · show exoticReULDR 24 8 = 0; simp [exoticReULDR]
  · show exoticImULDR 24 8 = 0; simp [exoticImULDR]
  · show exoticReDLUR 24 8 = 0; simp [exoticReDLUR]
  · show exoticImDLUR 24 8 = 0; simp [exoticImDLUR]
  · show exoticReNuREbarR 24 8 = 0; simp [exoticReNuREbarR]
  · show exoticImNuREbarR 24 8 = 0; simp [exoticImNuREbarR]
  · show exoticReEREbarR 24 8 = 0; simp [exoticReEREbarR]
  · show exoticImEREbarR 24 8 = 0; simp [exoticImEREbarR]

/-! ### Pivot 6: (0,9), active pair (10,11) — exotic ν_L↔e_R -/

theorem hva_09 : dirs22 10 0 9 = 1 := by
  show exoticReNuLeR 0 9 = 1
  simp [exoticReNuLeR]

theorem hvb_09 : dirs22 11 0 9 = Complex.I := by
  show exoticImNuLeR 0 9 = Complex.I
  simp [exoticImNuLeR]

theorem hvan_09 : ∀ i : Fin 22, i ≠ 10 → i ≠ 11 → dirs22 i 0 9 = 0 := by
  intro i h10 h11
  fin_cases i
  · show smDirac 1 0 0 0 0 0 9 = 0; exact smDirac_09_zero 1 0 0 0 0
  · show smDirac Complex.I 0 0 0 0 0 9 = 0; exact smDirac_09_zero Complex.I 0 0 0 0
  · show smDirac 0 1 0 0 0 0 9 = 0; exact smDirac_09_zero 0 1 0 0 0
  · show smDirac 0 Complex.I 0 0 0 0 9 = 0; exact smDirac_09_zero 0 Complex.I 0 0 0
  · show smDirac 0 0 1 0 0 0 9 = 0; exact smDirac_09_zero 0 0 1 0 0
  · show smDirac 0 0 Complex.I 0 0 0 9 = 0; exact smDirac_09_zero 0 0 Complex.I 0 0
  · show smDirac 0 0 0 1 0 0 9 = 0; exact smDirac_09_zero 0 0 0 1 0
  · show smDirac 0 0 0 Complex.I 0 0 9 = 0; exact smDirac_09_zero 0 0 0 Complex.I 0
  · show smDirac 0 0 0 0 1 0 9 = 0; exact smDirac_09_zero 0 0 0 0 1
  · show smDirac 0 0 0 0 Complex.I 0 9 = 0; exact smDirac_09_zero 0 0 0 0 Complex.I
  · exact absurd rfl h10
  · exact absurd rfl h11
  · show exoticReELNuR 0 9 = 0; simp [exoticReELNuR]
  · show exoticImELNuR 0 9 = 0; simp [exoticImELNuR]
  · show exoticReULDR 0 9 = 0; simp [exoticReULDR]
  · show exoticImULDR 0 9 = 0; simp [exoticImULDR]
  · show exoticReDLUR 0 9 = 0; simp [exoticReDLUR]
  · show exoticImDLUR 0 9 = 0; simp [exoticImDLUR]
  · show exoticReNuREbarR 0 9 = 0; simp [exoticReNuREbarR]
  · show exoticImNuREbarR 0 9 = 0; simp [exoticImNuREbarR]
  · show exoticReEREbarR 0 9 = 0; simp [exoticReEREbarR]
  · show exoticImEREbarR 0 9 = 0; simp [exoticImEREbarR]

/-! ### Pivot 7: (1,8), active pair (12,13) — exotic e_L↔ν_R -/

theorem hva_18 : dirs22 12 1 8 = 1 := by
  show exoticReELNuR 1 8 = 1
  simp [exoticReELNuR]

theorem hvb_18 : dirs22 13 1 8 = Complex.I := by
  show exoticImELNuR 1 8 = Complex.I
  simp [exoticImELNuR]

theorem hvan_18 : ∀ i : Fin 22, i ≠ 12 → i ≠ 13 → dirs22 i 1 8 = 0 := by
  intro i h12 h13
  fin_cases i
  · show smDirac 1 0 0 0 0 1 8 = 0; exact smDirac_18_zero 1 0 0 0 0
  · show smDirac Complex.I 0 0 0 0 1 8 = 0; exact smDirac_18_zero Complex.I 0 0 0 0
  · show smDirac 0 1 0 0 0 1 8 = 0; exact smDirac_18_zero 0 1 0 0 0
  · show smDirac 0 Complex.I 0 0 0 1 8 = 0; exact smDirac_18_zero 0 Complex.I 0 0 0
  · show smDirac 0 0 1 0 0 1 8 = 0; exact smDirac_18_zero 0 0 1 0 0
  · show smDirac 0 0 Complex.I 0 0 1 8 = 0; exact smDirac_18_zero 0 0 Complex.I 0 0
  · show smDirac 0 0 0 1 0 1 8 = 0; exact smDirac_18_zero 0 0 0 1 0
  · show smDirac 0 0 0 Complex.I 0 1 8 = 0; exact smDirac_18_zero 0 0 0 Complex.I 0
  · show smDirac 0 0 0 0 1 1 8 = 0; exact smDirac_18_zero 0 0 0 0 1
  · show smDirac 0 0 0 0 Complex.I 1 8 = 0; exact smDirac_18_zero 0 0 0 0 Complex.I
  · show exoticReNuLeR 1 8 = 0; simp [exoticReNuLeR]
  · show exoticImNuLeR 1 8 = 0; simp [exoticImNuLeR]
  · exact absurd rfl h12
  · exact absurd rfl h13
  · show exoticReULDR 1 8 = 0; simp [exoticReULDR]
  · show exoticImULDR 1 8 = 0; simp [exoticImULDR]
  · show exoticReDLUR 1 8 = 0; simp [exoticReDLUR]
  · show exoticImDLUR 1 8 = 0; simp [exoticImDLUR]
  · show exoticReNuREbarR 1 8 = 0; simp [exoticReNuREbarR]
  · show exoticImNuREbarR 1 8 = 0; simp [exoticImNuREbarR]
  · show exoticReEREbarR 1 8 = 0; simp [exoticReEREbarR]
  · show exoticImEREbarR 1 8 = 0; simp [exoticImEREbarR]

/-! ### Pivot 8: (2,11), active pair (14,15) — exotic u_L↔d_R -/

theorem hva_2_11 : dirs22 14 2 11 = 1 := by
  show exoticReULDR 2 11 = 1
  simp [exoticReULDR]

theorem hvb_2_11 : dirs22 15 2 11 = Complex.I := by
  show exoticImULDR 2 11 = Complex.I
  simp [exoticImULDR]

theorem hvan_2_11 : ∀ i : Fin 22, i ≠ 14 → i ≠ 15 → dirs22 i 2 11 = 0 := by
  intro i h14 h15
  fin_cases i
  · show smDirac 1 0 0 0 0 2 11 = 0; exact smDirac_2_11_zero 1 0 0 0 0
  · show smDirac Complex.I 0 0 0 0 2 11 = 0; exact smDirac_2_11_zero Complex.I 0 0 0 0
  · show smDirac 0 1 0 0 0 2 11 = 0; exact smDirac_2_11_zero 0 1 0 0 0
  · show smDirac 0 Complex.I 0 0 0 2 11 = 0; exact smDirac_2_11_zero 0 Complex.I 0 0 0
  · show smDirac 0 0 1 0 0 2 11 = 0; exact smDirac_2_11_zero 0 0 1 0 0
  · show smDirac 0 0 Complex.I 0 0 2 11 = 0; exact smDirac_2_11_zero 0 0 Complex.I 0 0
  · show smDirac 0 0 0 1 0 2 11 = 0; exact smDirac_2_11_zero 0 0 0 1 0
  · show smDirac 0 0 0 Complex.I 0 2 11 = 0; exact smDirac_2_11_zero 0 0 0 Complex.I 0
  · show smDirac 0 0 0 0 1 2 11 = 0; exact smDirac_2_11_zero 0 0 0 0 1
  · show smDirac 0 0 0 0 Complex.I 2 11 = 0; exact smDirac_2_11_zero 0 0 0 0 Complex.I
  · show exoticReNuLeR 2 11 = 0; simp [exoticReNuLeR]
  · show exoticImNuLeR 2 11 = 0; simp [exoticImNuLeR]
  · show exoticReELNuR 2 11 = 0; simp [exoticReELNuR]
  · show exoticImELNuR 2 11 = 0; simp [exoticImELNuR]
  · exact absurd rfl h14
  · exact absurd rfl h15
  · show exoticReDLUR 2 11 = 0; simp [exoticReDLUR]
  · show exoticImDLUR 2 11 = 0; simp [exoticImDLUR]
  · show exoticReNuREbarR 2 11 = 0; simp [exoticReNuREbarR]
  · show exoticImNuREbarR 2 11 = 0; simp [exoticImNuREbarR]
  · show exoticReEREbarR 2 11 = 0; simp [exoticReEREbarR]
  · show exoticImEREbarR 2 11 = 0; simp [exoticImEREbarR]

/-! ### Pivot 9: (3,10), active pair (16,17) — exotic d_L↔u_R -/

theorem hva_3_10 : dirs22 16 3 10 = 1 := by
  show exoticReDLUR 3 10 = 1
  simp [exoticReDLUR]

theorem hvb_3_10 : dirs22 17 3 10 = Complex.I := by
  show exoticImDLUR 3 10 = Complex.I
  simp [exoticImDLUR]

theorem hvan_3_10 : ∀ i : Fin 22, i ≠ 16 → i ≠ 17 → dirs22 i 3 10 = 0 := by
  intro i h16 h17
  fin_cases i
  · show smDirac 1 0 0 0 0 3 10 = 0; exact smDirac_3_10_zero 1 0 0 0 0
  · show smDirac Complex.I 0 0 0 0 3 10 = 0; exact smDirac_3_10_zero Complex.I 0 0 0 0
  · show smDirac 0 1 0 0 0 3 10 = 0; exact smDirac_3_10_zero 0 1 0 0 0
  · show smDirac 0 Complex.I 0 0 0 3 10 = 0; exact smDirac_3_10_zero 0 Complex.I 0 0 0
  · show smDirac 0 0 1 0 0 3 10 = 0; exact smDirac_3_10_zero 0 0 1 0 0
  · show smDirac 0 0 Complex.I 0 0 3 10 = 0; exact smDirac_3_10_zero 0 0 Complex.I 0 0
  · show smDirac 0 0 0 1 0 3 10 = 0; exact smDirac_3_10_zero 0 0 0 1 0
  · show smDirac 0 0 0 Complex.I 0 3 10 = 0; exact smDirac_3_10_zero 0 0 0 Complex.I 0
  · show smDirac 0 0 0 0 1 3 10 = 0; exact smDirac_3_10_zero 0 0 0 0 1
  · show smDirac 0 0 0 0 Complex.I 3 10 = 0; exact smDirac_3_10_zero 0 0 0 0 Complex.I
  · show exoticReNuLeR 3 10 = 0; simp [exoticReNuLeR]
  · show exoticImNuLeR 3 10 = 0; simp [exoticImNuLeR]
  · show exoticReELNuR 3 10 = 0; simp [exoticReELNuR]
  · show exoticImELNuR 3 10 = 0; simp [exoticImELNuR]
  · show exoticReULDR 3 10 = 0; simp [exoticReULDR]
  · show exoticImULDR 3 10 = 0; simp [exoticImULDR]
  · exact absurd rfl h16
  · exact absurd rfl h17
  · show exoticReNuREbarR 3 10 = 0; simp [exoticReNuREbarR]
  · show exoticImNuREbarR 3 10 = 0; simp [exoticImNuREbarR]
  · show exoticReEREbarR 3 10 = 0; simp [exoticReEREbarR]
  · show exoticImEREbarR 3 10 = 0; simp [exoticImEREbarR]

/-! ### Pivot 10: (8,25), active pair (18,19) — exotic ν_R↔ē_R -/

theorem hva_8_25 : dirs22 18 8 25 = 1 := by
  show exoticReNuREbarR 8 25 = 1
  simp [exoticReNuREbarR]

theorem hvb_8_25 : dirs22 19 8 25 = Complex.I := by
  show exoticImNuREbarR 8 25 = Complex.I
  simp [exoticImNuREbarR]

theorem hvan_8_25 : ∀ i : Fin 22, i ≠ 18 → i ≠ 19 → dirs22 i 8 25 = 0 := by
  intro i h18 h19
  fin_cases i
  · show smDirac 1 0 0 0 0 8 25 = 0; exact smDirac_8_25_zero 1 0 0 0 0
  · show smDirac Complex.I 0 0 0 0 8 25 = 0; exact smDirac_8_25_zero Complex.I 0 0 0 0
  · show smDirac 0 1 0 0 0 8 25 = 0; exact smDirac_8_25_zero 0 1 0 0 0
  · show smDirac 0 Complex.I 0 0 0 8 25 = 0; exact smDirac_8_25_zero 0 Complex.I 0 0 0
  · show smDirac 0 0 1 0 0 8 25 = 0; exact smDirac_8_25_zero 0 0 1 0 0
  · show smDirac 0 0 Complex.I 0 0 8 25 = 0; exact smDirac_8_25_zero 0 0 Complex.I 0 0
  · show smDirac 0 0 0 1 0 8 25 = 0; exact smDirac_8_25_zero 0 0 0 1 0
  · show smDirac 0 0 0 Complex.I 0 8 25 = 0; exact smDirac_8_25_zero 0 0 0 Complex.I 0
  · show smDirac 0 0 0 0 1 8 25 = 0; exact smDirac_8_25_zero 0 0 0 0 1
  · show smDirac 0 0 0 0 Complex.I 8 25 = 0; exact smDirac_8_25_zero 0 0 0 0 Complex.I
  · show exoticReNuLeR 8 25 = 0; simp [exoticReNuLeR]
  · show exoticImNuLeR 8 25 = 0; simp [exoticImNuLeR]
  · show exoticReELNuR 8 25 = 0; simp [exoticReELNuR]
  · show exoticImELNuR 8 25 = 0; simp [exoticImELNuR]
  · show exoticReULDR 8 25 = 0; simp [exoticReULDR]
  · show exoticImULDR 8 25 = 0; simp [exoticImULDR]
  · show exoticReDLUR 8 25 = 0; simp [exoticReDLUR]
  · show exoticImDLUR 8 25 = 0; simp [exoticImDLUR]
  · exact absurd rfl h18
  · exact absurd rfl h19
  · show exoticReEREbarR 8 25 = 0; simp [exoticReEREbarR]
  · show exoticImEREbarR 8 25 = 0; simp [exoticImEREbarR]

/-! ### Pivot 11: (9,25), active pair (20,21) — exotic e_R↔ē_R -/

theorem hva_9_25 : dirs22 20 9 25 = 1 := by
  show exoticReEREbarR 9 25 = 1
  simp [exoticReEREbarR]

theorem hvb_9_25 : dirs22 21 9 25 = Complex.I := by
  show exoticImEREbarR 9 25 = Complex.I
  simp [exoticImEREbarR]

theorem hvan_9_25 : ∀ i : Fin 22, i ≠ 20 → i ≠ 21 → dirs22 i 9 25 = 0 := by
  intro i h20 h21
  fin_cases i
  · show smDirac 1 0 0 0 0 9 25 = 0; exact smDirac_9_25_zero 1 0 0 0 0
  · show smDirac Complex.I 0 0 0 0 9 25 = 0; exact smDirac_9_25_zero Complex.I 0 0 0 0
  · show smDirac 0 1 0 0 0 9 25 = 0; exact smDirac_9_25_zero 0 1 0 0 0
  · show smDirac 0 Complex.I 0 0 0 9 25 = 0; exact smDirac_9_25_zero 0 Complex.I 0 0 0
  · show smDirac 0 0 1 0 0 9 25 = 0; exact smDirac_9_25_zero 0 0 1 0 0
  · show smDirac 0 0 Complex.I 0 0 9 25 = 0; exact smDirac_9_25_zero 0 0 Complex.I 0 0
  · show smDirac 0 0 0 1 0 9 25 = 0; exact smDirac_9_25_zero 0 0 0 1 0
  · show smDirac 0 0 0 Complex.I 0 9 25 = 0; exact smDirac_9_25_zero 0 0 0 Complex.I 0
  · show smDirac 0 0 0 0 1 9 25 = 0; exact smDirac_9_25_zero 0 0 0 0 1
  · show smDirac 0 0 0 0 Complex.I 9 25 = 0; exact smDirac_9_25_zero 0 0 0 0 Complex.I
  · show exoticReNuLeR 9 25 = 0; simp [exoticReNuLeR]
  · show exoticImNuLeR 9 25 = 0; simp [exoticImNuLeR]
  · show exoticReELNuR 9 25 = 0; simp [exoticReELNuR]
  · show exoticImELNuR 9 25 = 0; simp [exoticImELNuR]
  · show exoticReULDR 9 25 = 0; simp [exoticReULDR]
  · show exoticImULDR 9 25 = 0; simp [exoticImULDR]
  · show exoticReDLUR 9 25 = 0; simp [exoticReDLUR]
  · show exoticImDLUR 9 25 = 0; simp [exoticImDLUR]
  · show exoticReNuREbarR 9 25 = 0; simp [exoticReNuREbarR]
  · show exoticImNuREbarR 9 25 = 0; simp [exoticImNuREbarR]
  · exact absurd rfl h20
  · exact absurd rfl h21

/-! ### The independence theorem -/

theorem dirs22_independent : LinearIndependent ℝ dirs22 := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  fin_cases i
  · exact (pivot_extract 0 8 0 1 (by decide) hva_08 hvb_08 hvan_08 g hg).1
  · exact (pivot_extract 0 8 0 1 (by decide) hva_08 hvb_08 hvan_08 g hg).2
  · exact (pivot_extract 1 9 2 3 (by decide) hva_19 hvb_19 hvan_19 g hg).1
  · exact (pivot_extract 1 9 2 3 (by decide) hva_19 hvb_19 hvan_19 g hg).2
  · exact (pivot_extract 2 10 4 5 (by decide) hva_2_10 hvb_2_10 hvan_2_10 g hg).1
  · exact (pivot_extract 2 10 4 5 (by decide) hva_2_10 hvb_2_10 hvan_2_10 g hg).2
  · exact (pivot_extract 3 11 6 7 (by decide) hva_3_11 hvb_3_11 hvan_3_11 g hg).1
  · exact (pivot_extract 3 11 6 7 (by decide) hva_3_11 hvb_3_11 hvan_3_11 g hg).2
  · exact (pivot_extract 24 8 8 9 (by decide) hva_24_8 hvb_24_8 hvan_24_8 g hg).1
  · exact (pivot_extract 24 8 8 9 (by decide) hva_24_8 hvb_24_8 hvan_24_8 g hg).2
  · exact (pivot_extract 0 9 10 11 (by decide) hva_09 hvb_09 hvan_09 g hg).1
  · exact (pivot_extract 0 9 10 11 (by decide) hva_09 hvb_09 hvan_09 g hg).2
  · exact (pivot_extract 1 8 12 13 (by decide) hva_18 hvb_18 hvan_18 g hg).1
  · exact (pivot_extract 1 8 12 13 (by decide) hva_18 hvb_18 hvan_18 g hg).2
  · exact (pivot_extract 2 11 14 15 (by decide) hva_2_11 hvb_2_11 hvan_2_11 g hg).1
  · exact (pivot_extract 2 11 14 15 (by decide) hva_2_11 hvb_2_11 hvan_2_11 g hg).2
  · exact (pivot_extract 3 10 16 17 (by decide) hva_3_10 hvb_3_10 hvan_3_10 g hg).1
  · exact (pivot_extract 3 10 16 17 (by decide) hva_3_10 hvb_3_10 hvan_3_10 g hg).2
  · exact (pivot_extract 8 25 18 19 (by decide) hva_8_25 hvb_8_25 hvan_8_25 g hg).1
  · exact (pivot_extract 8 25 18 19 (by decide) hva_8_25 hvb_8_25 hvan_8_25 g hg).2
  · exact (pivot_extract 9 25 20 21 (by decide) hva_9_25 hvb_9_25 hvan_9_25 g hg).1
  · exact (pivot_extract 9 25 20 21 (by decide) hva_9_25 hvb_9_25 hvan_9_25 g hg).2

/-! ## §5. STEP C: the solution submodule and the conditional classification -/

/-- Real scalars commute with `star` on `ℂ`. -/
theorem star_real_smul (c : ℝ) (z : ℂ) : star (c • z) = c • star z := by
  have h : ∀ w : ℂ, (c : ℝ) • w = (c : ℂ) * w := fun w => by simp
  rw [h, h, star_mul]
  simp
  ring

/-- The solution space: matrices satisfying the repaired admissibility predicate.
This is a real submodule because all five conditions are real-linear. -/
def W22 : Submodule ℝ (Matrix I32 I32 ℂ) where
  carrier := {D | IsW22 D}
  add_mem' := by
    intro D1 D2 h1 h2
    obtain ⟨o1, c1, s1, j1, g1⟩ := h1
    obtain ⟨o2, c2, s2, j2, g2⟩ := h2
    have j1e : UJ * D1.transpose * UJ = D1 := j1
    have j2e : UJ * D2.transpose * UJ = D2 := j2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- OrderOneHolds is additive
      intro a b
      have e1 := o1 a b
      have e2 := o2 a b
      have hX : (D1 + D2) * smGen a - smGen a * (D1 + D2)
          = (D1 * smGen a - smGen a * D1) + (D2 * smGen a - smGen a * D2) := by
        simp only [Matrix.add_mul, Matrix.mul_add, sub_eq_add_neg, neg_add]
        ac_rfl
      rw [hX, Matrix.add_mul, Matrix.mul_add]
      have h3 : ((D1 * smGen a - smGen a * D1) * smGenOp b
          + (D2 * smGen a - smGen a * D2) * smGenOp b)
          - (smGenOp b * (D1 * smGen a - smGen a * D1)
          + smGenOp b * (D2 * smGen a - smGen a * D2))
          = ((D1 * smGen a - smGen a * D1) * smGenOp b
          - smGenOp b * (D1 * smGen a - smGen a * D1))
          + ((D2 * smGen a - smGen a * D2) * smGenOp b
          - smGenOp b * (D2 * smGen a - smGen a * D2)) := by
        simp only [sub_eq_add_neg, neg_add]
        ac_rfl
      rw [h3, e1, e2, add_zero]
    · -- cfCommutatorMap is additive
      have hC : cfCommutatorMap (D1 + D2)
          = cfCommutatorMap D1 + cfCommutatorMap D2 := by
        unfold cfCommutatorMap
        simp only [Matrix.add_mul, Matrix.mul_add, sub_eq_add_neg, neg_add]
        ac_rfl
      rw [hC, c1, c2, add_zero]
    · -- conjTranspose is additive
      show (D1 + D2).conjTranspose = D1 + D2
      rw [Matrix.conjTranspose_add, s1, s2]
    · -- IsJCompatible is additive
      show UJ * (D1 + D2).transpose * UJ = D1 + D2
      rw [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, j1e, j2e]
    · -- grading oddness is additive
      show gammaF * (D1 + D2) + (D1 + D2) * gammaF = 0
      rw [Matrix.mul_add, Matrix.add_mul]
      have h3 : (gammaF * D1 + gammaF * D2) + (D1 * gammaF + D2 * gammaF)
          = (gammaF * D1 + D1 * gammaF) + (gammaF * D2 + D2 * gammaF) := by
        ac_rfl
      rw [h3, g1, g2, add_zero]
  zero_mem' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a b
      simp
    · show cfCommutatorMap (0 : Matrix I32 I32 ℂ) = 0
      unfold cfCommutatorMap
      simp
    · show (0 : Matrix I32 I32 ℂ).conjTranspose = 0
      simp
    · show IsJCompatible (0 : Matrix I32 I32 ℂ)
      show UJ * (0 : Matrix I32 I32 ℂ).transpose * UJ = 0
      simp
    · show gammaF * (0 : Matrix I32 I32 ℂ) + (0 : Matrix I32 I32 ℂ) * gammaF = 0
      simp
  smul_mem' := by
    intro c D hD
    obtain ⟨o, cc, s, j, g⟩ := hD
    have je : UJ * D.transpose * UJ = D := j
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- OrderOneHolds is ℝ-homogeneous
      intro a b
      have e := o a b
      have hX : (c • D) * smGen a - smGen a * (c • D)
          = c • (D * smGen a - smGen a * D) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
      show ((c • D) * smGen a - smGen a * (c • D)) * smGenOp b
        - smGenOp b * ((c • D) * smGen a - smGen a * (c • D)) = 0
      rw [hX, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, e, smul_zero]
    · -- cfCommutatorMap is ℝ-homogeneous
      have hC : cfCommutatorMap (c • D) = c • cfCommutatorMap D := by
        unfold cfCommutatorMap
        rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
      show cfCommutatorMap (c • D) = 0
      rw [hC, cc, smul_zero]
    · -- conjTranspose is ℝ-homogeneous
      have hS : (c • D).conjTranspose = c • D.conjTranspose := by
        ext i j
        have e1 : ((c • D) j i) = c • (D j i) := rfl
        have e2 : ((c • D.conjTranspose) i j) = c • (D.conjTranspose i j) := rfl
        rw [Matrix.conjTranspose_apply, e1, star_real_smul, e2,
          Matrix.conjTranspose_apply]
      show (c • D).conjTranspose = c • D
      rw [hS, s]
    · -- IsJCompatible is ℝ-homogeneous
      have hJ : UJ * (c • D).transpose * UJ = c • (UJ * D.transpose * UJ) := by
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
      show UJ * (c • D).transpose * UJ = c • D
      rw [hJ, je]
    · -- grading oddness is ℝ-homogeneous
      have hG : gammaF * (c • D) + (c • D) * gammaF
          = c • (gammaF * D + D * gammaF) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
      show gammaF * (c • D) + (c • D) * gammaF = 0
      rw [hG, g, smul_zero]

/-! ## Pivot map and the dimension bound

Proved here, next to `W22`: `CFKernelRetarget` cannot host this block
because `W22` is defined in this module, and this module imports
`CFKernelRetarget` — the reverse import would be a cycle. -/

/-- The 11 pivots as Fin 32 pairs. -/
def pivots11 : Fin 11 → (Fin 32 × Fin 32)
  | ⟨0, _⟩ => ((0 : Fin 32), (8 : Fin 32))
  | ⟨1, _⟩ => ((1 : Fin 32), (9 : Fin 32))
  | ⟨2, _⟩ => ((2 : Fin 32), (10 : Fin 32))
  | ⟨3, _⟩ => ((3 : Fin 32), (11 : Fin 32))
  | ⟨4, _⟩ => ((24 : Fin 32), (8 : Fin 32))
  | ⟨5, _⟩ => ((0 : Fin 32), (9 : Fin 32))
  | ⟨6, _⟩ => ((1 : Fin 32), (8 : Fin 32))
  | ⟨7, _⟩ => ((2 : Fin 32), (11 : Fin 32))
  | ⟨8, _⟩ => ((3 : Fin 32), (10 : Fin 32))
  | ⟨9, _⟩ => ((8 : Fin 32), (25 : Fin 32))
  | ⟨10, _⟩ => ((9 : Fin 32), (25 : Fin 32))

/-- Pivot map to complex values. -/
def pivotMapC : W22 →ₗ[ℝ] (Fin 11 → ℂ) where
  toFun D k := D.val (pivots11 k).1 (pivots11 k).2
  map_add' D1 D2 := by
    funext k
    show (D1 + D2).val (pivots11 k).1 (pivots11 k).2
      = D1.val (pivots11 k).1 (pivots11 k).2 + D2.val (pivots11 k).1 (pivots11 k).2
    rw [Submodule.coe_add, Matrix.add_apply]
  map_smul' r D := by
    funext k
    show (r • D).val (pivots11 k).1 (pivots11 k).2
      = r • D.val (pivots11 k).1 (pivots11 k).2
    rw [Submodule.coe_smul, Matrix.smul_apply]

/-- The pivot map is injective: if all 11 pivots of `D1 - D2` vanish,
`D_eq_zero_of_pivots_vanish` forces `D1 - D2 = 0`. -/
theorem pivotMapC_injective : Function.Injective pivotMapC := by
  intro D1 D2 h
  have hker : pivotMapC (D1 - D2) = 0 := by rw [map_sub, h, sub_self]
  have h11 : ∀ k : Fin 11, ((D1 - D2).val) (pivots11 k).1 (pivots11 k).2 = 0 := by
    intro k
    have h1 := congrFun hker k
    have e1 : pivotMapC (D1 - D2) k
        = ((D1 - D2).val) (pivots11 k).1 (pivots11 k).2 := rfl
    have e2 : (0 : Fin 11 → ℂ) k = (0 : ℂ) := rfl
    rw [e1, e2] at h1
    exact h1
  have hlist : ([(0,8),(1,9),(2,10),(3,11),(24,8),(0,9),(1,8),(2,11),(3,10),(8,25),(9,25)]
      : List (ℕ × ℕ))
      = List.ofFn (fun k : Fin 11 => ((pivots11 k).1.val, (pivots11 k).2.val)) := by
    decide
  have hpiv : ∀ m n : Fin 32, (m.val, n.val) ∈
      ([(0,8),(1,9),(2,10),(3,11),(24,8),(0,9),(1,8),(2,11),(3,10),(8,25),(9,25)]
      : List (ℕ × ℕ)) →
      ((D1 - D2).val) m n = 0 := by
    intro m n hmn
    rw [hlist, List.mem_ofFn] at hmn
    obtain ⟨k, hk⟩ := hmn
    obtain ⟨hh1, hh2⟩ := Prod.mk.inj hk
    have e1 : (pivots11 k).1 = m := Fin.ext hh1
    have e2 : (pivots11 k).2 = n := Fin.ext hh2
    rw [← e1, ← e2]
    exact h11 k
  have hmem : IsW22 ((D1 - D2).val) := (D1 - D2).2
  obtain ⟨o, c, s, j, g⟩ := hmem
  have hzero : ((D1 - D2).val) = 0 := D_eq_zero_of_pivots_vanish _ o c s j g hpiv
  have hsub0 : D1 - D2 = 0 := Subtype.ext hzero
  exact sub_eq_zero.mp hsub0

/-- finrank ≤ 22. -/
theorem finrank_W22_le_22 : Module.finrank ℝ W22 ≤ 22 := by
  have h := LinearMap.finrank_le_finrank_of_injective pivotMapC_injective
  -- finrank ℝ (Fin 11 → ℂ) = 11 * 2 = 22
  have h22 : Module.finrank ℝ (Fin 11 → ℂ) = 22 := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Complex.finrank_real_complex]
    decide
  rw [h22] at h
  exact h


/-- Every basis direction lies in the solution submodule. -/
theorem dirs22_mem_W22 (k : Fin 22) : dirs22 k ∈ W22 :=
  dirs22_mem k

/-- **The 46 → 22 classification (unconditional).**

Every matrix satisfying the repaired admissibility hypotheses lies in the real
linear span of the 22 explicit directions (10 SM Yukawa + 12 exotic survivors).

The dimension bound `Module.finrank ℝ W22 ≤ 22` is proved just above
(`finrank_W22_le_22`) via the injective pivot map; combined with the 22
independent directions, the census hypothesis is eliminated.
-/
theorem cf_kernel_classification_46_22
    (D : Matrix I32 I32 ℂ) (hD : IsW22 D) :
    D ∈ Submodule.span ℝ (Set.range dirs22) := by
  have hle : Submodule.span ℝ (Set.range dirs22) ≤ W22 := by
    rw [Submodule.span_le]
    rintro x ⟨k, rfl⟩
    exact dirs22_mem_W22 k
  have hfr : Module.finrank ℝ (Submodule.span ℝ (Set.range dirs22)) = 22 := by
    rw [finrank_span_eq_card dirs22_independent, Fintype.card_fin]
  have hfin22 : Module.finrank ℝ W22 = 22 := by
    apply le_antisymm
    · exact finrank_W22_le_22
    · rw [← hfr]
      exact Submodule.finrank_mono hle
  have heq : Submodule.span ℝ (Set.range dirs22) = W22 :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr, hfin22])
  have hDmem : D ∈ W22 := hD
  rw [heq]
  exact hDmem

end ThetLogos
