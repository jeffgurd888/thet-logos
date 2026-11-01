import Mathlib.Tactic
import ThetLogos.DialOneGammaFamilyChecks
import ThetLogos.DialOneClassificationPin

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneDoubleFlipPin
open ThetLogos.DialOneGammaTraceChecks
open ThetLogos.DialOneGammaFamilyPin
open ThetLogos.DialOneGammaFamilyChecks
open ThetLogos.DialOneClassificationPin

/-!
# CLS-2 — the toggle-orbit structure

NO CLAIM; Dial 1 = 0. The four toggles (piDouble, bit 0;
piSwap c, bit c+1) in additive single-correction form.
Group-law ((ℤ/2)^4 composition) is the pre-named PARTIAL
seam: named open below, not proved here.
Membership is decided at every orbit point except the
all-swaps point `allSwapBits` (bits 1,2,3 set, bit 0
unset): there both exclusion mechanisms provably fail,
C3 and the clean family HOLD, and membership is exactly
its `DialOneBase` clause (`strengthened_allSwap_iff_base`)
— the K-CLS-2 candidate seat, reported at full rank.
-/

namespace ThetLogos.DialOneSwapOrbit

/-- Index in `Fin 4` of the swap toggle for colour `c`. -/
def swapIdx (c : Fin 3) : Fin 4 := ⟨c.val + 1, by have h := c.isLt; omega⟩

/-- piDouble's two single corrections. -/
def orbitCorrD (a : AF) : Matrix (Fin 32) (Fin 32) ℂ :=
  Matrix.single s8 s8 (star a.u1 - a.u1)
    + Matrix.single s9 s9 (a.u1 - star a.u1)

/-- piSwap c's two single corrections. -/
def orbitCorrS (c : Fin 3) (a : AF) : Matrix (Fin 32) (Fin 32) ℂ :=
  Matrix.single (uSeat c) (uSeat c) (star a.u1 - a.u1)
    + Matrix.single (dSeat c) (dSeat c) (a.u1 - star a.u1)

/-- The orbit representative: π₁ plus the corrections of
the toggles whose bit is set. -/
def orbitRep (b : Fin 4 → Bool) (a : AF) : Matrix (Fin 32) (Fin 32) ℂ :=
  pi1 a
    + (if b 0 then orbitCorrD a else 0)
    + (if b 1 then orbitCorrS 0 a else 0)
    + (if b 2 then orbitCorrS 1 a else 0)
    + (if b 3 then orbitCorrS 2 a else 0)

theorem orbitRep_zero : orbitRep (fun _ => false) = pi1 := by
  funext a
  simp [orbitRep]

theorem orbitRep_bit0 :
    orbitRep (fun j => decide (j = (0 : Fin 4))) = piDouble := by
  funext a
  simp only [orbitRep, orbitCorrD, orbitCorrS]
  norm_num [piDouble, add_assoc]

theorem orbitRep_bitSwap (c : Fin 3) :
    orbitRep (fun j => decide (j = swapIdx c)) = piSwap c := by
  fin_cases c <;> funext a <;>
    simp only [orbitRep, orbitCorrD, orbitCorrS, swapIdx] <;>
    norm_num [piSwap, add_assoc, uSeat, dSeat]

theorem orbitCorrD_s9 (a : AF) :
    orbitCorrD a s9 s9 = a.u1 - star a.u1 := by
  rw [orbitCorrD, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply,
    if_neg (by decide : ¬ (s8 = s9 ∧ s8 = s9)),
    if_pos ⟨rfl, rfl⟩, zero_add]

theorem orbitCorrS_s9 (c : Fin 3) (a : AF) :
    orbitCorrS c a s9 s9 = 0 := by
  have hu : ¬ (uSeat c = s9 ∧ uSeat c = s9) := by
    intro h
    have hv := congrArg Fin.val h.1
    simp only [uSeat] at hv
    have hc := c.isLt
    omega
  have hd : ¬ (dSeat c = s9 ∧ dSeat c = s9) := by
    intro h
    have hv := congrArg Fin.val h.1
    simp only [dSeat] at hv
    have hc := c.isLt
    omega
  rw [orbitCorrS, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply, if_neg hu, if_neg hd, add_zero]

theorem orbitRep_s9_diag (b : Fin 4 → Bool) (a : AF) :
    orbitRep b a s9 s9 = if b 0 then a.u1 else star a.u1 := by
  have hpi : pi1 a s9 s9 = star a.u1 := pi1_entry_eR a
  show (pi1 a + (if b 0 then orbitCorrD a else 0)
      + (if b 1 then orbitCorrS 0 a else 0)
      + (if b 2 then orbitCorrS 1 a else 0)
      + (if b 3 then orbitCorrS 2 a else 0)) s9 s9 = _
  by_cases h0 : b 0 <;> by_cases h1 : b 1 <;> by_cases h2 : b 2 <;>
    by_cases h3 : b 3 <;>
    simp [Matrix.add_apply, h0, h1, h2, h3,
      orbitCorrS_s9, orbitCorrD_s9, hpi] <;> ring

theorem orbitCorrD_uSeat (c : Fin 3) (a : AF) :
    orbitCorrD a (uSeat c) (uSeat c) = 0 := by
  have h8 : ¬ (s8 = uSeat c ∧ s8 = uSeat c) := by
    intro h; have hv := congrArg Fin.val h.1
    simp only [uSeat] at hv; have hc := c.isLt; omega
  have h9 : ¬ (s9 = uSeat c ∧ s9 = uSeat c) := by
    intro h; have hv := congrArg Fin.val h.1
    simp only [uSeat] at hv; have hc := c.isLt; omega
  rw [orbitCorrD, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply, if_neg h8, if_neg h9, add_zero]

theorem orbitCorrS_uSeat_diag (c : Fin 3) (a : AF) :
    orbitCorrS c a (uSeat c) (uSeat c) = star a.u1 - a.u1 := by
  have hd : ¬ (dSeat c = uSeat c ∧ dSeat c = uSeat c) := by
    intro h; have hv := congrArg Fin.val h.1
    simp only [dSeat, uSeat] at hv; omega
  rw [orbitCorrS, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply, if_pos ⟨rfl, rfl⟩, if_neg hd, add_zero]

theorem orbitCorrS_uSeat_of_ne (c c' : Fin 3) (h : c' ≠ c) (a : AF) :
    orbitCorrS c' a (uSeat c) (uSeat c) = 0 := by
  have hu : ¬ (uSeat c' = uSeat c ∧ uSeat c' = uSeat c) := by
    intro hh; apply h
    have hv := congrArg Fin.val hh.1
    simp only [uSeat] at hv
    exact Fin.ext (by omega)
  have hd : ¬ (dSeat c' = uSeat c ∧ dSeat c' = uSeat c) := by
    intro hh; have hv := congrArg Fin.val hh.1
    simp only [dSeat, uSeat] at hv; have hc := c'.isLt; omega
  rw [orbitCorrS, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply, if_neg hu, if_neg hd, add_zero]

theorem pi1_uSeat_diag (c : Fin 3) (a : AF) :
    pi1 a (uSeat c) (uSeat c) = a.u1 := by
  have h := pi1_entry_quarkR a c c ⟨0, by omega⟩ ⟨0, by omega⟩
  simpa [uSeat] using h

theorem orbitRep_uSeat_diag (b : Fin 4 → Bool) (c : Fin 3) (a : AF) :
    orbitRep b a (uSeat c) (uSeat c)
      = if b (swapIdx c) then star a.u1 else a.u1 := by
  fin_cases c <;>
    (show (pi1 a + (if b 0 then orbitCorrD a else 0)
        + (if b 1 then orbitCorrS 0 a else 0)
        + (if b 2 then orbitCorrS 1 a else 0)
        + (if b 3 then orbitCorrS 2 a else 0)) _ _
      = _; by_cases h0 : b 0 <;> by_cases h1 : b 1 <;>
      by_cases h2 : b 2 <;> by_cases h3 : b 3 <;>
      simp [Matrix.add_apply, h0, h1, h2, h3, pi1_uSeat_diag,
        orbitCorrD_uSeat, orbitCorrS_uSeat_diag,
        orbitCorrS_uSeat_of_ne, swapIdx] <;> ring)

theorem orbitRep_injective :
    Function.Injective orbitRep := by
  intro b b' h
  funext i
  by_contra hi
  have hne : b i ≠ b' i := fun hh => hi (by rw [hh])
  have hI : (-Complex.I : ℂ) ≠ Complex.I := by
    norm_num [Complex.ext_iff]
  have hI2 : (Complex.I : ℂ) ≠ -Complex.I := by
    norm_num [Complex.ext_iff]
  fin_cases i
  · have he := congrFun (congrFun (congrFun h ⟨Complex.I, 0, 0⟩) s9) s9
    rw [orbitRep_s9_diag, orbitRep_s9_diag] at he
    cases hb : b 0 <;> cases hb' : b' 0 <;> simp [hb, hb'] at he ⊢
    · exact hne (by simp [hb, hb'])
    · exact hI he
    · exact hI2 he
    · exact hne (by simp [hb, hb'])
  · have he := congrFun (congrFun (congrFun h ⟨Complex.I, 0, 0⟩)
      (uSeat 0)) (uSeat 0)
    rw [orbitRep_uSeat_diag, orbitRep_uSeat_diag] at he
    have hs : swapIdx 0 = (1 : Fin 4) := rfl
    rw [hs] at he
    cases hb : b 1 <;> cases hb' : b' 1 <;> simp [hb, hb'] at he ⊢
    · exact hne (by simp [hb, hb', hs])
    · exact hI2 he
    · exact hI he
    · exact hne (by simp [hb, hb', hs])
  · have he := congrFun (congrFun (congrFun h ⟨Complex.I, 0, 0⟩)
      (uSeat 1)) (uSeat 1)
    rw [orbitRep_uSeat_diag, orbitRep_uSeat_diag] at he
    have hs : swapIdx 1 = (2 : Fin 4) := rfl
    rw [hs] at he
    cases hb : b 2 <;> cases hb' : b' 2 <;> simp [hb, hb'] at he ⊢
    · exact hne (by simp [hb, hb', hs])
    · exact hI2 he
    · exact hI he
    · exact hne (by simp [hb, hb', hs])
  · have he := congrFun (congrFun (congrFun h ⟨Complex.I, 0, 0⟩)
      (uSeat 2)) (uSeat 2)
    rw [orbitRep_uSeat_diag, orbitRep_uSeat_diag] at he
    have hs : swapIdx 2 = (3 : Fin 4) := rfl
    rw [hs] at he
    cases hb : b 3 <;> cases hb' : b' 3 <;> simp [hb, hb'] at he ⊢
    · exact hne (by simp [hb, hb', hs])
    · exact hI2 he
    · exact hI he
    · exact hne (by simp [hb, hb', hs])

/-- The 16 orbit points are pairwise distinct. -/
theorem orbitRep_pairwise_distinct {b b' : Fin 4 → Bool}
    (h : orbitRep b = orbitRep b') : b = b' :=
  orbitRep_injective h

theorem trace_feR_corrD (α β : ℤ) :
    Matrix.trace (gammaF * eRProj * orbitCorrD (u1Gen α β))
      = -2 * (α : ℂ) * Complex.I := by
  have p8 : eRProj s8 s8 = 0 := by
    have h := eRProj_diag s8
    simpa [eRInd] using h
  have p9 : eRProj s9 s9 = 1 := by
    have h := eRProj_diag s9
    simpa [eRInd] using h
  have hdec : orbitCorrD (u1Gen α β)
      = Matrix.single s8 s8 (star ((α : ℂ) * Complex.I) - (α : ℂ) * Complex.I)
        + Matrix.single s9 s9 ((α : ℂ) * Complex.I
            - star ((α : ℂ) * Complex.I)) := rfl
  rw [hdec, Matrix.mul_add, Matrix.trace_add,
    trace_gammaF_proj_single, trace_gammaF_proj_single,
    gammaF_s8, gammaF_s9, p8, p9, hstar α]
  ring

theorem trace_feR_corrS (c : Fin 3) (α β : ℤ) :
    Matrix.trace (gammaF * eRProj * orbitCorrS c (u1Gen α β)) = 0 := by
  have hdec : orbitCorrS c (u1Gen α β)
      = Matrix.single (uSeat c) (uSeat c)
          (star ((α : ℂ) * Complex.I) - (α : ℂ) * Complex.I)
        + Matrix.single (dSeat c) (dSeat c) ((α : ℂ) * Complex.I
            - star ((α : ℂ) * Complex.I)) := rfl
  rw [hdec, Matrix.mul_add, Matrix.trace_add,
    trace_gammaF_proj_single, trace_gammaF_proj_single,
    eRProj_uSeat, eRProj_dSeat]
  simp

theorem trace_feR_orbitRep (b : Fin 4 → Bool) (α β : ℤ) :
    Matrix.trace (gammaF * eRProj * orbitRep b (u1Gen α β))
      = if b 0 then -2 * (α : ℂ) * Complex.I else 0 := by
  by_cases h0 : b 0 <;> by_cases h1 : b 1 <;> by_cases h2 : b 2 <;>
    by_cases h3 : b 3 <;>
    simp [orbitRep, h0, h1, h2, h3, Matrix.mul_add, Matrix.trace_add,
      feR_pi1 α β, trace_feR_corrD α β, trace_feR_corrS]

theorem not_feR_orbitRep_of_bit0 {b : Fin 4 → Bool} (hb : b 0 = true) :
    ¬ FeR (orbitRep b) := by
  intro h
  have h10 := h 1 0
  rw [trace_feR_orbitRep, hb] at h10
  simp only [if_true] at h10
  norm_num [Complex.ext_iff] at h10

theorem not_strengthened_orbitRep_of_bit0 {b : Fin 4 → Bool}
    (hb : b 0 = true) : ¬ DialOneStrengthenedFam (orbitRep b) :=
  fun h => not_feR_orbitRep_of_bit0 hb h.2.2.2.2

theorem orbitCorrD_row_uSeat (c : Fin 3) (a : AF) (j : Fin 32) :
    orbitCorrD a (uSeat c) j = 0 := by
  have h8 : ¬ (s8 = uSeat c ∧ s8 = j) := by
    intro h; have hv := congrArg Fin.val h.1
    simp only [uSeat] at hv; have hc := c.isLt; omega
  have h9 : ¬ (s9 = uSeat c ∧ s9 = j) := by
    intro h; have hv := congrArg Fin.val h.1
    simp only [uSeat] at hv; have hc := c.isLt; omega
  rw [orbitCorrD, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply, if_neg h8, if_neg h9, add_zero]

theorem orbitCorrS_row_uSeat (c : Fin 3) (a : AF) (j : Fin 32) :
    orbitCorrS c a (uSeat c) j
      = if j = uSeat c then star a.u1 - a.u1 else 0 := by
  have hd : ¬ (dSeat c = uSeat c ∧ dSeat c = j) := by
    intro h; have hv := congrArg Fin.val h.1
    simp only [dSeat, uSeat] at hv; omega
  by_cases hj : j = uSeat c
  · subst hj
    rw [orbitCorrS, Matrix.add_apply, Matrix.single_apply,
      Matrix.single_apply, if_pos ⟨rfl, rfl⟩, if_neg hd,
      add_zero, if_pos rfl]
  · rw [orbitCorrS, Matrix.add_apply, Matrix.single_apply,
      Matrix.single_apply,
      if_neg (fun h : uSeat c = uSeat c ∧ uSeat c = j => hj h.2.symm),
      if_neg hd, add_zero, if_neg hj]

theorem orbitCorrS_row_uSeat_of_ne (c c' : Fin 3) (h : c' ≠ c)
    (a : AF) (j : Fin 32) :
    orbitCorrS c' a (uSeat c) j = 0 := by
  have hu : ¬ (uSeat c' = uSeat c ∧ uSeat c' = j) := by
    intro hh; apply h
    have hv := congrArg Fin.val hh.1
    simp only [uSeat] at hv
    exact Fin.ext (by omega)
  have hd : ¬ (dSeat c' = uSeat c ∧ dSeat c' = j) := by
    intro hh; have hv := congrArg Fin.val hh.1
    simp only [dSeat, uSeat] at hv; have hc := c'.isLt; omega
  rw [orbitCorrS, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply, if_neg hu, if_neg hd, add_zero]

theorem pi1_row_uSeat (c : Fin 3) (a : AF) (j : Fin 32) :
    pi1 a (uSeat c) j = if j = uSeat c then a.u1 else 0 := by
  have h : pi1 a = piSwap c a - orbitCorrS c a := by
    rw [piSwap, orbitCorrS]
    abel
  rw [h, Matrix.sub_apply, piSwap_row_uSeat, orbitCorrS_row_uSeat]
  by_cases hj : j = uSeat c <;> simp [hj] <;> ring

theorem orbitRep_row_uSeat (b : Fin 4 → Bool) (c : Fin 3) (a : AF)
    (j : Fin 32) :
    orbitRep b a (uSeat c) j
      = if j = uSeat c
        then (if b (swapIdx c) then star a.u1 else a.u1) else 0 := by
  fin_cases c <;>
    (show (pi1 a + (if b 0 then orbitCorrD a else 0)
        + (if b 1 then orbitCorrS 0 a else 0)
        + (if b 2 then orbitCorrS 1 a else 0)
        + (if b 3 then orbitCorrS 2 a else 0)) _ _
      = _; by_cases h0 : b 0 <;> by_cases h1 : b 1 <;>
      by_cases h2 : b 2 <;> by_cases h3 : b 3 <;>
      simp [Matrix.add_apply, h0, h1, h2, h3, pi1_row_uSeat,
        orbitCorrD_row_uSeat, orbitCorrS_row_uSeat,
        orbitCorrS_row_uSeat_of_ne, swapIdx] <;> split_ifs <;> ring)

theorem orbitCorrD_col_uSeat (c : Fin 3) (a : AF) (k : Fin 32) :
    orbitCorrD a k (uSeat c) = 0 := by
  have h8 : ¬ (s8 = k ∧ s8 = uSeat c) := by
    intro h; have hv := congrArg Fin.val h.2
    simp only [uSeat] at hv; have hc := c.isLt; omega
  have h9 : ¬ (s9 = k ∧ s9 = uSeat c) := by
    intro h; have hv := congrArg Fin.val h.2
    simp only [uSeat] at hv; have hc := c.isLt; omega
  rw [orbitCorrD, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply, if_neg h8, if_neg h9, add_zero]

theorem orbitCorrS_col_uSeat (c : Fin 3) (a : AF) (k : Fin 32) :
    orbitCorrS c a k (uSeat c)
      = if k = uSeat c then star a.u1 - a.u1 else 0 := by
  have hd : ¬ (dSeat c = k ∧ dSeat c = uSeat c) := by
    intro h; have hv := congrArg Fin.val h.2
    simp only [dSeat, uSeat] at hv; omega
  by_cases hk : k = uSeat c
  · subst hk
    rw [orbitCorrS, Matrix.add_apply, Matrix.single_apply,
      Matrix.single_apply, if_pos ⟨rfl, rfl⟩, if_neg hd,
      add_zero, if_pos rfl]
  · rw [orbitCorrS, Matrix.add_apply, Matrix.single_apply,
      Matrix.single_apply,
      if_neg (fun h : uSeat c = k ∧ uSeat c = uSeat c => hk h.1.symm),
      if_neg hd, add_zero, if_neg hk]

theorem orbitCorrS_col_uSeat_of_ne (c c' : Fin 3) (h : c' ≠ c)
    (a : AF) (k : Fin 32) :
    orbitCorrS c' a k (uSeat c) = 0 := by
  have hu : ¬ (uSeat c' = k ∧ uSeat c' = uSeat c) := by
    intro hh; apply h
    have hv := congrArg Fin.val hh.2
    simp only [uSeat] at hv
    exact Fin.ext (by omega)
  have hd : ¬ (dSeat c' = k ∧ dSeat c' = uSeat c) := by
    intro hh; have hv := congrArg Fin.val hh.2
    simp only [dSeat, uSeat] at hv; have hc := c'.isLt; omega
  rw [orbitCorrS, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply, if_neg hu, if_neg hd, add_zero]

theorem pi1_col_uSeat (c : Fin 3) (a : AF) (k : Fin 32) :
    pi1 a k (uSeat c) = if k = uSeat c then a.u1 else 0 := by
  fin_cases c <;> obtain ⟨v, hv⟩ := k <;> interval_cases v <;>
    simp [pi1, uSeat]

theorem orbitRep_col_uSeat (b : Fin 4 → Bool) (c : Fin 3) (a : AF)
    (k : Fin 32) :
    orbitRep b a k (uSeat c)
      = if k = uSeat c
        then (if b (swapIdx c) then star a.u1 else a.u1) else 0 := by
  fin_cases c <;>
    (show (pi1 a + (if b 0 then orbitCorrD a else 0)
        + (if b 1 then orbitCorrS 0 a else 0)
        + (if b 2 then orbitCorrS 1 a else 0)
        + (if b 3 then orbitCorrS 2 a else 0)) _ _
      = _; by_cases h0 : b 0 <;> by_cases h1 : b 1 <;>
      by_cases h2 : b 2 <;> by_cases h3 : b 3 <;>
      simp [Matrix.add_apply, h0, h1, h2, h3, pi1_col_uSeat,
        orbitCorrD_col_uSeat, orbitCorrS_col_uSeat,
        orbitCorrS_col_uSeat_of_ne, swapIdx] <;> split_ifs <;> ring)

theorem orbitCorrD_partner (k l : Fin 3) (a : AF) :
    orbitCorrD a ⟨26 + 2 * k.val, by have h := k.isLt; omega⟩
      ⟨26 + 2 * l.val, by have h := l.isLt; omega⟩ = 0 := by
  have h8 : ¬ (s8 = ⟨26 + 2 * k.val, by have h := k.isLt; omega⟩
      ∧ s8 = ⟨26 + 2 * l.val, by have h := l.isLt; omega⟩) := by
    intro h; have hv := congrArg Fin.val h.1
    simp only [] at hv; omega
  have h9 : ¬ (s9 = ⟨26 + 2 * k.val, by have h := k.isLt; omega⟩
      ∧ s9 = ⟨26 + 2 * l.val, by have h := l.isLt; omega⟩) := by
    intro h; have hv := congrArg Fin.val h.1
    simp only [] at hv; omega
  rw [orbitCorrD, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply, if_neg h8, if_neg h9, add_zero]

theorem orbitCorrS_partner (c k l : Fin 3) (a : AF) :
    orbitCorrS c a ⟨26 + 2 * k.val, by have h := k.isLt; omega⟩
      ⟨26 + 2 * l.val, by have h := l.isLt; omega⟩ = 0 := by
  have hu : ¬ (uSeat c = ⟨26 + 2 * k.val, by have h := k.isLt; omega⟩
      ∧ uSeat c = ⟨26 + 2 * l.val, by have h := l.isLt; omega⟩) := by
    intro h; have hv := congrArg Fin.val h.1
    simp only [uSeat] at hv; have hc := c.isLt; omega
  have hd : ¬ (dSeat c = ⟨26 + 2 * k.val, by have h := k.isLt; omega⟩
      ∧ dSeat c = ⟨26 + 2 * l.val, by have h := l.isLt; omega⟩) := by
    intro h; have hv := congrArg Fin.val h.1
    simp only [dSeat] at hv; have hc := c.isLt; omega
  rw [orbitCorrS, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply, if_neg hu, if_neg hd, add_zero]

theorem orbitRep_partner_entry (b : Fin 4 → Bool) (k l : Fin 3) (a : AF) :
    orbitRep b a ⟨26 + 2 * k.val, by have h := k.isLt; omega⟩
        ⟨26 + 2 * l.val, by have h := l.isLt; omega⟩
      = pi1 a ⟨26 + 2 * k.val, by have h := k.isLt; omega⟩
          ⟨26 + 2 * l.val, by have h := l.isLt; omega⟩ := by
  show (pi1 a + (if b 0 then orbitCorrD a else 0)
      + (if b 1 then orbitCorrS 0 a else 0)
      + (if b 2 then orbitCorrS 1 a else 0)
      + (if b 3 then orbitCorrS 2 a else 0)) _ _ = _
  by_cases h0 : b 0 <;> by_cases h1 : b 1 <;> by_cases h2 : b 2 <;>
    by_cases h3 : b 3 <;>
    simp [Matrix.add_apply, h0, h1, h2, h3, orbitCorrD_partner,
      orbitCorrS_partner]

theorem orbitOp_uSeat (b : Fin 4 → Bool) (c c' : Fin 3) (a : AF)
    (ha : a.color = Matrix.single c' c 1) :
    piOp (orbitRep b a) (uSeat c) (uSeat c') = 1 := by
  rw [piOp_apply, partner_uSeat, partner_uSeat,
    orbitRep_partner_entry]
  have h := pi1_entry_quarkRc a c' c ⟨0, by omega⟩ ⟨0, by omega⟩
  rw [ha] at h
  simpa using h

theorem not_base_orbitRep_of_swap_pair {b : Fin 4 → Bool}
    (c c' : Fin 3) (hc' : c' ≠ c)
    (hc : b (swapIdx c) = true) (hc2 : b (swapIdx c') = false) :
    ¬ DialOneBase (orbitRep b) := by
  intro hbase
  have hoz := hbase.2.2.2.2.2.2.2.1 (⟨Complex.I, 0, 0⟩ : AF)
    (⟨0, 0, Matrix.single c' c 1⟩ : AF)
  have hentry := congrArg (fun M : Matrix (Fin 32) (Fin 32) ℂ =>
    M (uSeat c) (uSeat c')) hoz
  have hL : (orbitRep b (⟨Complex.I, 0, 0⟩ : AF)
      * piOp (orbitRep b (⟨0, 0, Matrix.single c' c 1⟩ : AF)))
        (uSeat c) (uSeat c')
      = star Complex.I := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (uSeat c)]
    · rw [orbitRep_row_uSeat, if_pos rfl,
        orbitOp_uSeat b c c' _ rfl]
      simp [hc]
    · intro k _ hk
      rw [orbitRep_row_uSeat, if_neg hk, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hR : (piOp (orbitRep b (⟨0, 0, Matrix.single c' c 1⟩ : AF))
      * orbitRep b (⟨Complex.I, 0, 0⟩ : AF)) (uSeat c) (uSeat c')
      = Complex.I := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (uSeat c')]
    · rw [orbitOp_uSeat b c c' _ rfl, orbitRep_col_uSeat,
        if_pos rfl]
      simp [hc2]
    · intro k _ hk
      rw [orbitRep_col_uSeat, if_neg hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hL, hR] at hentry
  exact hneI hentry

theorem not_strengthened_orbitRep_of_swap_pair {b : Fin 4 → Bool}
    (c c' : Fin 3) (hc' : c' ≠ c)
    (hc : b (swapIdx c) = true) (hc2 : b (swapIdx c') = false) :
    ¬ DialOneStrengthenedFam (orbitRep b) :=
  fun h => not_base_orbitRep_of_swap_pair c c' hc' hc hc2 h.1

theorem trace_gammaF_single (s : Fin 32) (x : ℂ) :
    Matrix.trace (gammaF * Matrix.single s s x) = gammaF s s * x := by
  have h := trace_gammaF_proj_single (1 : Matrix (Fin 32) (Fin 32) ℂ) s x
  simpa using h

theorem trace_plain_corrD (α β : ℤ) :
    Matrix.trace (gammaF * orbitCorrD (u1Gen α β)) = 0 := by
  have hdec : orbitCorrD (u1Gen α β)
      = Matrix.single s8 s8 (star ((α : ℂ) * Complex.I) - (α : ℂ) * Complex.I)
        + Matrix.single s9 s9 ((α : ℂ) * Complex.I
            - star ((α : ℂ) * Complex.I)) := rfl
  rw [hdec, Matrix.mul_add, Matrix.trace_add, trace_gammaF_single,
    trace_gammaF_single, gammaF_s8, gammaF_s9, hstar α]
  ring

theorem trace_plain_corrS (c : Fin 3) (α β : ℤ) :
    Matrix.trace (gammaF * orbitCorrS c (u1Gen α β)) = 0 := by
  have hdec : orbitCorrS c (u1Gen α β)
      = Matrix.single (uSeat c) (uSeat c)
          (star ((α : ℂ) * Complex.I) - (α : ℂ) * Complex.I)
        + Matrix.single (dSeat c) (dSeat c) ((α : ℂ) * Complex.I
            - star ((α : ℂ) * Complex.I)) := rfl
  rw [hdec, Matrix.mul_add, Matrix.trace_add, trace_gammaF_single,
    trace_gammaF_single, gammaF_uSeat, gammaF_dSeat, hstar α]
  ring

theorem c3_orbitRep (b : Fin 4 → Bool) : C3 (orbitRep b) := by
  intro α β
  by_cases h0 : b 0 <;> by_cases h1 : b 1 <;> by_cases h2 : b 2 <;>
    by_cases h3 : b 3 <;>
    simp [orbitRep, h0, h1, h2, h3, Matrix.mul_add, Matrix.trace_add,
      trace_gammaF_pi1_u1Gen α β, trace_plain_corrD α β,
      trace_plain_corrS]

theorem trace_lep_corrD (α β : ℤ) :
    Matrix.trace (gammaF * lepProj * orbitCorrD (u1Gen α β)) = 0 := by
  have hdec : orbitCorrD (u1Gen α β)
      = Matrix.single s8 s8 (star ((α : ℂ) * Complex.I) - (α : ℂ) * Complex.I)
        + Matrix.single s9 s9 ((α : ℂ) * Complex.I
            - star ((α : ℂ) * Complex.I)) := rfl
  have p8 : lepProj s8 s8 = 1 := by
    have h := lepProj_diag s8
    simpa [lepInd] using h
  have p9 : lepProj s9 s9 = 1 := by
    have h := lepProj_diag s9
    simpa [lepInd] using h
  rw [hdec, Matrix.mul_add, Matrix.trace_add,
    trace_gammaF_proj_single, trace_gammaF_proj_single,
    gammaF_s8, gammaF_s9, p8, p9, hstar α]
  ring

theorem trace_lep_corrS (c : Fin 3) (α β : ℤ) :
    Matrix.trace (gammaF * lepProj * orbitCorrS c (u1Gen α β)) = 0 := by
  have hdec : orbitCorrS c (u1Gen α β)
      = Matrix.single (uSeat c) (uSeat c)
          (star ((α : ℂ) * Complex.I) - (α : ℂ) * Complex.I)
        + Matrix.single (dSeat c) (dSeat c) ((α : ℂ) * Complex.I
            - star ((α : ℂ) * Complex.I)) := rfl
  rw [hdec, Matrix.mul_add, Matrix.trace_add,
    trace_gammaF_proj_single, trace_gammaF_proj_single,
    lepProj_uSeat, lepProj_dSeat]
  simp

theorem trace_col_corrD (c : Fin 3) (α β : ℤ) :
    Matrix.trace (gammaF * colProj c * orbitCorrD (u1Gen α β)) = 0 := by
  have hdec : orbitCorrD (u1Gen α β)
      = Matrix.single s8 s8 (star ((α : ℂ) * Complex.I) - (α : ℂ) * Complex.I)
        + Matrix.single s9 s9 ((α : ℂ) * Complex.I
            - star ((α : ℂ) * Complex.I)) := rfl
  rw [hdec, Matrix.mul_add, Matrix.trace_add,
    trace_gammaF_proj_single, trace_gammaF_proj_single,
    colProj_s8 c, colProj_s9 c]
  simp

theorem trace_col_corrS (c c' : Fin 3) (α β : ℤ) :
    Matrix.trace (gammaF * colProj c * orbitCorrS c' (u1Gen α β)) = 0 := by
  have hdec : orbitCorrS c' (u1Gen α β)
      = Matrix.single (uSeat c') (uSeat c')
          (star ((α : ℂ) * Complex.I) - (α : ℂ) * Complex.I)
        + Matrix.single (dSeat c') (dSeat c') ((α : ℂ) * Complex.I
            - star ((α : ℂ) * Complex.I)) := rfl
  rw [hdec, Matrix.mul_add, Matrix.trace_add,
    trace_gammaF_proj_single, trace_gammaF_proj_single,
    gammaF_uSeat, gammaF_dSeat, colProj_uSeat, colProj_dSeat]
  split_ifs with hc'
  · rw [hstar α]; ring
  · simp

theorem gammaFamily_orbitRep_of_bit0_false {b : Fin 4 → Bool}
    (hb : b 0 = false) : GammaFamily (orbitRep b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro α β
    by_cases h0 : b 0 <;> by_cases h1 : b 1 <;> by_cases h2 : b 2 <;>
      by_cases h3 : b 3 <;>
      simp [orbitRep, h0, h1, h2, h3, Matrix.mul_add, Matrix.trace_add,
        c3lep_pi1 α β, trace_lep_corrD α β, trace_lep_corrS]
  · intro c α β
    by_cases h0 : b 0 <;> by_cases h1 : b 1 <;> by_cases h2 : b 2 <;>
      by_cases h3 : b 3 <;>
      simp [orbitRep, h0, h1, h2, h3, Matrix.mul_add, Matrix.trace_add,
        c3col_pi1 c α β, trace_col_corrD c α β, trace_col_corrS c]
  · intro α β
    rw [trace_feR_orbitRep, hb]
    simp

/-- The all-swaps bit pattern: bits 1,2,3 set, bit 0 unset. -/
def allSwapBits : Fin 4 → Bool := fun j => decide (j ≠ 0)

theorem gammaFamily_allSwap : GammaFamily (orbitRep allSwapBits) :=
  gammaFamily_orbitRep_of_bit0_false (by decide)

theorem c3_allSwap : C3 (orbitRep allSwapBits) := c3_orbitRep _

theorem strengthened_orbitRep_iff_of_ne_allSwap {b : Fin 4 → Bool}
    (hb : b ≠ allSwapBits) :
    DialOneStrengthenedFam (orbitRep b) ↔ b = (fun _ => false) := by
  constructor
  · intro h
    by_contra hb0
    by_cases h0 : b 0 = true
    · exact not_strengthened_orbitRep_of_bit0 h0 h
    · have h0f : b 0 = false := by cases hv : b 0 <;> simp_all
      cases h1 : b 1 <;> cases h2 : b 2 <;> cases h3 : b 3
      · exact hb0 (by funext i; fin_cases i <;> simp [h0f, h1, h2, h3])
      · exact not_strengthened_orbitRep_of_swap_pair 2 0 (by decide)
          h3 h1 h
      · exact not_strengthened_orbitRep_of_swap_pair 1 2 (by decide)
          h2 h3 h
      · exact not_strengthened_orbitRep_of_swap_pair 1 0 (by decide)
          h2 h1 h
      · exact not_strengthened_orbitRep_of_swap_pair 0 1 (by decide)
          h1 h2 h
      · exact not_strengthened_orbitRep_of_swap_pair 0 1 (by decide)
          h1 h2 h
      · exact not_strengthened_orbitRep_of_swap_pair 1 2 (by decide)
          h2 h3 h
      · exact hb (by funext i; fin_cases i <;>
          simp [allSwapBits, h0f, h1, h2, h3])
  · intro hb0
    rw [hb0, orbitRep_zero]
    exact strengthened_pi1

theorem allSwap_swapIdx (c : Fin 3) :
    allSwapBits (swapIdx c) = true := by
  fin_cases c <;> decide

/-- At `allSwapBits` both landed exclusion mechanisms
provably fail: `FeR` HOLDS there, and no swap pair
(set, unset) exists for the order-zero mechanism. -/
theorem allSwap_exclusion_mechanisms_fail :
    FeR (orbitRep allSwapBits)
    ∧ ∀ c c' : Fin 3, c' ≠ c →
        ¬ (allSwapBits (swapIdx c) = true
          ∧ allSwapBits (swapIdx c') = false) := by
  refine ⟨gammaFamily_allSwap.2.2, ?_⟩
  intro c c' _ h
  have h2 := h.2
  rw [allSwap_swapIdx] at h2
  exact (by decide : ¬ ((true : Bool) = false)) h2

/-- Membership of the all-swap point in the strengthened
set is exactly its `DialOneBase` clause: C3 and the clean
family are proved above. **K-CLS-2 candidate seat.** -/
theorem strengthened_allSwap_iff_base :
    DialOneStrengthenedFam (orbitRep allSwapBits)
      ↔ DialOneBase (orbitRep allSwapBits) :=
  ⟨fun h => h.1, fun h => ⟨h, c3_allSwap, gammaFamily_allSwap⟩⟩

/-- The landed orbit classification, assembled. -/
theorem orbit_membership_status :
    (∀ b : Fin 4 → Bool, b ≠ allSwapBits →
      (DialOneStrengthenedFam (orbitRep b)
        ↔ b = (fun _ => false)))
    ∧ (DialOneStrengthenedFam (orbitRep allSwapBits)
        ↔ DialOneBase (orbitRep allSwapBits))
    ∧ Function.Injective orbitRep :=
  ⟨fun b hb => strengthened_orbitRep_iff_of_ne_allSwap hb,
    strengthened_allSwap_iff_base, orbitRep_injective⟩

/-- **PARTIAL seam (named, pre-registered in the pack):**
the (ℤ/2)^4 group / composition law for the toggles as maps
on representations is NOT proved here. The orbit is landed
as a SET (16 distinct points, `orbitRep_injective`) with
membership decided at every point except `allSwapBits`,
whose status is pinned by `gammaFamily_allSwap`,
`c3_allSwap`, and the failure of both exclusion mechanisms
there (see the module report): its `DialOneBase` clause is
the remaining open seat. -/
theorem groupLaw_partial_seam : True := trivial

#print axioms orbitRep_injective
#print axioms orbitRep_zero
#print axioms orbitRep_bit0
#print axioms orbitRep_bitSwap
#print axioms trace_feR_orbitRep
#print axioms not_strengthened_orbitRep_of_bit0
#print axioms not_strengthened_orbitRep_of_swap_pair
#print axioms c3_orbitRep
#print axioms gammaFamily_orbitRep_of_bit0_false
#print axioms strengthened_orbitRep_iff_of_ne_allSwap
#print axioms allSwap_exclusion_mechanisms_fail
#print axioms strengthened_allSwap_iff_base
#print axioms orbit_membership_status

end ThetLogos.DialOneSwapOrbit
