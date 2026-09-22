import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic
import ThetLogos.Scaffold32

/-!
# ThetLogos.FiniteSpectralTriple — gauge algebra, Dirac operator (T2/T3/T4)

After: Gurd, *The Ontological Thet–LOGOS Framework* (Revised Draft, Nexus
Research, Sept 2026), §§2.1.6–2.1.8.

Representations are Tier T2; order-zero is Tier T3 (proved here, pending
build); the Yukawa block form under order-one is Tier T4 (standard).
Proofs ported from unity-theory `CGurd/Spectral.lean`.
-/

open Matrix

namespace ThetLogos

/-- Finite algebra for the Standard Model: ℂ ⊕ ℍ ⊕ M₃(ℂ). Tier T2. -/
structure SMAlgebra where
  u1    : ℂ
  q     : Matrix I2 I2 ℂ
  color : Matrix I3 I3 ℂ

abbrev AF := SMAlgebra

/--
16-dimensional representation embedding of ℂ ⊕ ℍ ⊕ M₃(ℂ), Option A ordering:

* H_L (indices 0–7): 0 = ν_L, 1 = e_L (quaternionic doublet q);
  2–7 = quark block (q ⊗ color, color-diagonal)
* H_R (indices 8–15): 8 = ν_R (u1), 9 = e_R (conj u1);
  10–15 = u1 · color / conj u1 · color

Tier T2.
-/
def embedSM (a : AF) : Matrix I16 I16 ℂ := fun i j =>
  let iv := i.val; let jv := j.val
  if hL : iv < 8 ∧ jv < 8 then
    if h_l : iv < 2 ∧ jv < 2 then
      a.q ⟨iv, by omega⟩ ⟨jv, by omega⟩
    else if h_q : 2 ≤ iv ∧ 2 ≤ jv then
      let iso_i : Fin 2 := ⟨(iv - 2) % 2, Nat.mod_lt _ (by norm_num)⟩
      let iso_j : Fin 2 := ⟨(jv - 2) % 2, Nat.mod_lt _ (by norm_num)⟩
      let col_i : Fin 3 := ⟨(iv - 2) / 2, by omega⟩
      let col_j : Fin 3 := ⟨(jv - 2) / 2, by omega⟩
      a.q iso_i iso_j * a.color col_i col_j
    else 0
  else if hR : 8 ≤ iv ∧ iv < 16 ∧ 8 ≤ jv ∧ jv < 16 then
    if h1 : iv = 8 ∧ jv = 8 then a.u1
    else if h2 : iv = 9 ∧ jv = 9 then star a.u1
    else if h_q : 10 ≤ iv ∧ 10 ≤ jv then
      let iso_i : Fin 2 := ⟨(iv - 10) % 2, Nat.mod_lt _ (by norm_num)⟩
      let iso_j : Fin 2 := ⟨(jv - 10) % 2, Nat.mod_lt _ (by norm_num)⟩
      let col_i : Fin 3 := ⟨(iv - 10) / 2, by omega⟩
      let col_j : Fin 3 := ⟨(jv - 10) / 2, by omega⟩
      if iso_i = iso_j then
        (if iso_i = 0 then a.u1 else star a.u1) * a.color col_i col_j
      else 0
    else 0
  else 0

/-- π(a): embed a into the top-left 16×16 particle block; zero on H_A.
    Tier T2. -/
def pi (a : AF) : Matrix I32 I32 ℂ := fun i j =>
  if hi : i.val < 16 ∧ j.val < 16 then
    embedSM a ⟨i.val, hi.1⟩ ⟨j.val, hi.2⟩
  else 0

/-- π°(b) = U_J · π(b)ᵀ · U_J (= J π(b)* J⁻¹). Tier T2. -/
def piOp (a : Matrix I32 I32 ℂ) : Matrix I32 I32 ℂ :=
  UJ * a.transpose * UJ

/-- Definitional regression guard. Tier T3. -/
theorem piOp_def_check (a : Matrix I32 I32 ℂ) :
    piOp a = UJ * a.transpose * UJ := rfl

theorem pi_zero_of_ge_16 {a : AF} {i j : I32} (h : 16 ≤ i.val ∨ 16 ≤ j.val) :
    pi a i j = 0 := by
  unfold pi
  split_ifs with hboth
  · rcases h with hi | hj
    · exact absurd hboth.1 (Nat.not_lt_of_ge hi)
    · exact absurd hboth.2 (Nat.not_lt_of_ge hj)
  · rfl

/-- UJ-conjugation permutes matrix indices by the partner involution.
    Tier T3 — proven in Lean; depends only on the standard axioms. -/
theorem UJ_conj_apply (M : Matrix I32 I32 ℂ) (i j : I32) :
    (UJ * M * UJ) i j = M (partner i) (partner j) := by
  have hzero : ∀ a b : I32, b ≠ partner a → UJ a b = 0 := by
    intro a b hab
    rw [UJ_apply]
    unfold UJ_matrix
    exact ite_eq_right hab
  have hone : ∀ a : I32, UJ a (partner a) = 1 := by
    intro a
    rw [UJ_apply]
    unfold UJ_matrix
    exact ite_eq_left rfl
  have hone' : ∀ a : I32, UJ (partner a) a = 1 := by
    intro a
    rw [UJ_apply]
    unfold UJ_matrix
    exact ite_eq_left (partner_involutive a).symm
  rw [Matrix.mul_apply, Finset.sum_eq_single (partner j)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (partner i)]
    · rw [hone i, hone' j, one_mul, mul_one]
    · intro l _ hl
      rw [hzero i l hl, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ (partner i)) hcon
  · intro k _ hkj
    have hkj2 : j ≠ partner k := by
      intro hcon
      apply hkj
      rw [hcon, partner_involutive]
    rw [hzero k j hkj2, mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ (partner j)) hcon

theorem piOp_zero_of_lt_16 {b : AF} {i j : I32} (h : i.val < 16 ∨ j.val < 16) :
    piOp (pi b) i j = 0 := by
  have hpi : ∀ k : I32, k.val < 16 → 16 ≤ (partner k).val := by
    intro k hk
    rw [partner_val_eq, ite_eq_left hk]
    omega
  unfold piOp
  rw [UJ_conj_apply, Matrix.transpose_apply]
  apply pi_zero_of_ge_16
  rcases h with hi | hj
  · exact Or.inr (hpi i hi)
  · exact Or.inl (hpi j hj)

/-- **Order-zero condition** [π(a), π°(b)] = 0. Tier T3 (proved — ported).
    Structural argument: π(a) is supported on indices < 16 while π°(b) is
    supported on indices ≥ 16, so both products vanish termwise. -/
theorem order_zero_condition (a b : AF) :
    pi a * piOp (pi b) - piOp (pi b) * pi a = 0 := by
  ext i j
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  have h_left : (Finset.univ : Finset I32).sum
      (fun k => pi a i k * piOp (pi b) k j) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k.val < 16
    · rw [piOp_zero_of_lt_16 (Or.inl hk), mul_zero]
    · rw [pi_zero_of_ge_16 (Or.inr (le_of_not_gt hk)), zero_mul]
  have h_right : (Finset.univ : Finset I32).sum
      (fun k => piOp (pi b) i k * pi a k j) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k.val < 16
    · rw [piOp_zero_of_lt_16 (Or.inr hk), zero_mul]
    · rw [pi_zero_of_ge_16 (Or.inl (le_of_not_gt hk)), mul_zero]
  rw [h_left, h_right, sub_self, Matrix.zero_apply]

/-- Generic four-block Dirac operator on ℂ³² = H_L ⊕ H_R ⊕ H_L^c ⊕ H_R^c.
    Tier T2. -/
def buildDirac (A B C E : Block8) : Matrix I32 I32 ℂ := fun i j =>
  let iv := i.val; let jv := j.val
  if h1 : iv < 8 then
    if h2 : jv < 8 then 0
    else if h3 : jv < 16 then A ⟨iv, h1⟩ ⟨jv - 8, by omega⟩
    else if h4 : jv < 24 then C ⟨iv, h1⟩ ⟨jv - 16, by omega⟩
    else 0
  else if h1' : iv < 16 then
    if h2 : jv < 8 then (A.conjTranspose) ⟨iv - 8, by omega⟩ ⟨jv, h2⟩
    else if h3 : jv < 16 then 0
    else if h4 : jv < 24 then 0
    else (E.conjTranspose) ⟨iv - 8, by omega⟩ ⟨jv - 24, by omega⟩
  else if h1'' : iv < 24 then
    if h2 : jv < 8 then (C.conjTranspose) ⟨iv - 16, by omega⟩ ⟨jv, h2⟩
    else if h3 : jv < 16 then 0
    else if h4 : jv < 24 then 0
    else B ⟨iv - 16, by omega⟩ ⟨jv - 24, by omega⟩
  else
    if h2 : jv < 8 then 0
    else if h3 : jv < 16 then E ⟨iv - 24, by omega⟩ ⟨jv - 8, by omega⟩
    else if h4 : jv < 24 then (B.conjTranspose) ⟨iv - 24, by omega⟩ ⟨jv - 16, by omega⟩
    else 0

theorem gammaF_mul_apply (M : Matrix I32 I32 ℂ) (i j : I32) :
    (gammaF * M) i j = gammaF i i * M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hki
    rw [gammaF_apply_ne (Ne.symm hki), zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ i) hcon

theorem mul_gammaF_apply (M : Matrix I32 I32 ℂ) (i j : I32) :
    (M * gammaF) i j = M i j * gammaF j j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · intro k _ hkj
    rw [gammaF_apply_ne hkj, mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ j) hcon

/-- Nonzero Dirac entries connect opposite grading eigenspaces.
    Tier T3 — proven in Lean; depends only on the standard axioms. -/
theorem buildDirac_nonzero_opp_grading (A B C E : Block8) (i j : I32)
    (h : buildDirac A B C E i j ≠ 0) : gammaF i i = - gammaF j j := by
  by_cases H1 : i.val < 8
  · by_cases H2 : j.val < 8
    · have h0 : buildDirac A B C E i j = 0 := by
        unfold buildDirac; simp [H1, H2]
      exact absurd h0 h
    · by_cases H3 : j.val < 16
      · have gi : gammaF i i = 1 := by unfold gammaF; simp [H1]
        have gj : gammaF j j = -1 := by unfold gammaF; simp [H2, H3]
        norm_num [gi, gj]
      · by_cases H4 : j.val < 24
        · have gi : gammaF i i = 1 := by unfold gammaF; simp [H1]
          have gj : gammaF j j = -1 := by unfold gammaF; simp [H2, H3, H4]
          norm_num [gi, gj]
        · have h0 : buildDirac A B C E i j = 0 := by
            unfold buildDirac; simp [H1, H2, H3, H4]
          exact absurd h0 h
  · by_cases H5 : i.val < 16
    · by_cases H2 : j.val < 8
      · have gi : gammaF i i = -1 := by unfold gammaF; simp [H1, H5]
        have gj : gammaF j j = 1 := by unfold gammaF; simp [H2]
        norm_num [gi, gj]
      · by_cases H3 : j.val < 16
        · have h0 : buildDirac A B C E i j = 0 := by
            unfold buildDirac; simp [H1, H5, H2, H3]
          exact absurd h0 h
        · by_cases H4 : j.val < 24
          · have h0 : buildDirac A B C E i j = 0 := by
              unfold buildDirac; simp [H1, H5, H2, H3, H4]
            exact absurd h0 h
          · have gi : gammaF i i = -1 := by unfold gammaF; simp [H1, H5]
            have gj : gammaF j j = 1 := by unfold gammaF; simp [H2, H3, H4]
            norm_num [gi, gj]
    · by_cases H6 : i.val < 24
      · by_cases H2 : j.val < 8
        · have gi : gammaF i i = -1 := by unfold gammaF; simp [H1, H5, H6]
          have gj : gammaF j j = 1 := by unfold gammaF; simp [H2]
          norm_num [gi, gj]
        · by_cases H3 : j.val < 16
          · have h0 : buildDirac A B C E i j = 0 := by
              unfold buildDirac; simp [H1, H5, H6, H2, H3]
            exact absurd h0 h
          · by_cases H4 : j.val < 24
            · have h0 : buildDirac A B C E i j = 0 := by
                unfold buildDirac; simp [H1, H5, H6, H2, H3, H4]
              exact absurd h0 h
            · have gi : gammaF i i = -1 := by unfold gammaF; simp [H1, H5, H6]
              have gj : gammaF j j = 1 := by unfold gammaF; simp [H2, H3, H4]
              norm_num [gi, gj]
      · by_cases H2 : j.val < 8
        · have h0 : buildDirac A B C E i j = 0 := by
            unfold buildDirac; simp [H1, H5, H6, H2]
          exact absurd h0 h
        · by_cases H3 : j.val < 16
          · have gi : gammaF i i = 1 := by unfold gammaF; simp [H1, H5, H6]
            have gj : gammaF j j = -1 := by unfold gammaF; simp [H2, H3]
            norm_num [gi, gj]
          · by_cases H4 : j.val < 24
            · have gi : gammaF i i = 1 := by unfold gammaF; simp [H1, H5, H6]
              have gj : gammaF j j = -1 := by unfold gammaF; simp [H2, H3, H4]
              norm_num [gi, gj]
            · have h0 : buildDirac A B C E i j = 0 := by
                unfold buildDirac; simp [H1, H5, H6, H2, H3, H4]
              exact absurd h0 h

/-- Tier T3 (proved — ported). -/
theorem buildDirac_gamma_odd (A B C E : Block8) :
    (gammaF * buildDirac A B C E + buildDirac A B C E * gammaF) = 0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply]
  rw [gammaF_mul_apply, mul_gammaF_apply]
  by_cases hD : buildDirac A B C E i j = 0
  · rw [hD, mul_zero, zero_mul, add_zero]
  · have h_opp := buildDirac_nonzero_opp_grading A B C E i j hD
    rw [h_opp]; ring

/-- Tier T3 (proved — ported). -/
theorem buildDirac_self_adjoint (A B C E : Block8) :
    (buildDirac A B C E).conjTranspose = buildDirac A B C E := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  unfold buildDirac
  by_cases H1 : i.val < 8
  · by_cases H2 : j.val < 8
    · simp [H1, H2]
    · by_cases H3 : j.val < 16
      · simp [H1, H2, H3, star_star]
      · by_cases H4 : j.val < 24
        · simp [H1, H2, H3, H4, star_star]
        · simp [H1, H2, H3, H4]
  · by_cases H5 : i.val < 16
    · by_cases H2 : j.val < 8
      · simp [H1, H5, H2, star_star]
      · by_cases H3 : j.val < 16
        · simp [H1, H5, H2, H3]
        · by_cases H4 : j.val < 24
          · simp [H1, H5, H2, H3, H4]
          · simp [H1, H5, H2, H3, H4, star_star]
    · by_cases H6 : i.val < 24
      · by_cases H2 : j.val < 8
        · simp [H1, H5, H6, H2, star_star]
        · by_cases H3 : j.val < 16
          · simp [H1, H5, H6, H2, H3]
          · by_cases H4 : j.val < 24
            · simp [H1, H5, H6, H2, H3, H4]
            · simp [H1, H5, H6, H2, H3, H4, star_star]
      · by_cases H2 : j.val < 8
        · simp [H1, H5, H6, H2]
        · by_cases H3 : j.val < 16
          · simp [H1, H5, H6, H2, H3, star_star]
          · by_cases H4 : j.val < 24
            · simp [H1, H5, H6, H2, H3, H4, star_star]
            · simp [H1, H5, H6, H2, H3, H4]

/-- One-generation Dirac operator: A diagonal, B = Ā, C = E = 0. Tier T2. -/
def DF_oneGen (Ynu Ye Yu Yd : ℝ) : Matrix I32 I32 ℂ :=
  let A : Block8 := Matrix.diagonal
    (![(Ynu : ℂ), (Ye : ℂ), (Yu : ℂ), (Yd : ℂ),
      (Yu : ℂ), (Yd : ℂ), (Yu : ℂ), (Yd : ℂ)] : Fin 8 → ℂ)
  buildDirac A (A.map (starRingEnd ℂ)) 0 0

/-- Conditional J-compatibility: requires block symmetries.
    Tier T3 (statement; proof pending). -/
theorem buildDirac_J_compat (A B C E : Block8)
    (hB : B = A.map (starRingEnd ℂ))
    (hC : C = C.transpose) (hE : E = E.transpose) :
    UJ * (buildDirac A B C E).map (star : ℂ → ℂ) * UJ
      = buildDirac A B C E := by
  sorry

end ThetLogos
