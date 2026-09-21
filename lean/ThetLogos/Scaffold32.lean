import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-!
# ThetLogos.Scaffold32 — the 32-state scaffold (Tiers T2/T3)

After: Gurd, *The Ontological Thet–LOGOS Framework* (Revised Draft, Nexus
Research, Sept 2026), §2.1.6.

Definitions are Tier T2; the combinatorial identities are Tier T3.
Proofs below are ported from unity-theory `CGurd/Spectral.lean`
(which states them over the same definitions); they become machine-checked
in *this* repository only after `lake build` succeeds here.
-/

open Matrix

namespace ThetLogos

abbrev I32 := Fin 32
abbrev I16 := Fin 16
abbrev I8  := Fin 8
abbrev I3  := Fin 3
abbrev I2  := Fin 2

abbrev Block8 := Matrix I8 I8 ℂ

/-- Particle ↔ antiparticle index swap: i ↦ (i + 16) mod 32. Tier T2. -/
def partner (i : I32) : I32 :=
  if h : i.val < 16 then ⟨i.val + 16, by omega⟩
  else ⟨i.val - 16, by omega⟩

/-- Unfolded value of the partner map. Tier T2. -/
@[simp] theorem partner_val_eq (i : I32) :
    (partner i).val = if i.val < 16 then i.val + 16 else i.val - 16 := by
  by_cases h : i.val < 16 <;> simp [partner, h]

/-- Tier T3 (proved). -/
theorem partner_involutive (i : I32) : partner (partner i) = i := by
  rw [Fin.ext_iff, partner_val_eq, partner_val_eq]
  split_ifs with h1 h2 <;> omega

def UJ_matrix (i j : I32) : ℂ := if j = partner i then 1 else 0

/-- The real structure as a proper `Matrix` (so `*` is matrix multiplication).
    Tier T2. -/
def UJ : Matrix I32 I32 ℂ := fun i j => UJ_matrix i j

@[simp] theorem UJ_apply (i j : I32) : UJ i j = UJ_matrix i j := rfl

/-- Grading γ_F = diag(+I₈, -I₈, -I₈, +I₈) on (H_L, H_R, H_L^c, H_R^c).
    Tier T2. -/
def gammaF : Matrix I32 I32 ℂ := fun i j =>
  if h : i = j then
    let k := i.val
    if k < 8 then 1
    else if k < 16 then -1
    else if k < 24 then -1
    else 1
  else 0

/-- Off-diagonal entries of γ_F vanish. Tier T2. -/
@[simp] theorem gammaF_apply_ne {i j : I32} (h : i ≠ j) : gammaF i j = 0 := by
  unfold gammaF
  simp [h]

/-- Tier T3 (proved). -/
theorem gammaF_self_adjoint : gammaF.conjTranspose = gammaF := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases h : i = j
  · subst h
    simp only [gammaF]
    split_ifs with h8 h16 h24 <;> simp
  · rw [gammaF_apply_ne (fun h' => h h'.symm), gammaF_apply_ne h, star_zero]

/-- Tier T3 (proved). -/
theorem gammaF_involutive : gammaF * gammaF = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq _]
    have hsum : ∑ k : I32, gammaF i k * gammaF k i
        = gammaF i i * gammaF i i := by
      apply Finset.sum_eq_single i
      · intro k _ hk
        unfold gammaF; split_ifs with heq
        · exact absurd heq.symm hk
        · ring
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    have hdiag : gammaF i i
        = (if i.val < 8 then (1:ℂ) else if i.val < 16 then -1
           else if i.val < 24 then -1 else 1) := by
      unfold gammaF; simp
    rw [hsum, hdiag]
    split_ifs <;> ring
  · rw [Matrix.one_apply_ne h]
    apply Finset.sum_eq_zero
    intro k _
    unfold gammaF; split_ifs with h1 h2
    · exfalso; exact h (h1.trans h2)
    · ring
    · ring
    · ring

/-- Tier T3 (proved). -/
theorem UJ_mul_self : UJ * UJ = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [UJ_apply]
  by_cases h : j = i
  · subst h
    rw [Matrix.one_apply_eq _]
    have hsum : ∑ k : I32, UJ_matrix j k * UJ_matrix k j
        = UJ_matrix j (partner j) * UJ_matrix (partner j) j := by
      apply Finset.sum_eq_single (partner j)
      · intro k _ hk
        have h0 : UJ_matrix j k = 0 := by unfold UJ_matrix; simp [hk]
        rw [h0, zero_mul]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    rw [hsum]
    unfold UJ_matrix; simp [partner_involutive]
  · rw [Matrix.one_apply_ne' h]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k = partner i
    · subst hk
      have h0 : UJ_matrix (partner i) j = 0 := by
        unfold UJ_matrix; simp [partner_involutive, show j ≠ i from h]
      rw [h0, mul_zero]
    · have h0 : UJ_matrix i k = 0 := by unfold UJ_matrix; simp [hk]
      rw [h0, zero_mul]

/-- KO-dim 6 real-structure grading sign: U_J · star(γ_F) · U_J = -γ_F.
    Tier T3 (statement; proof pending — the ported case analysis needs
    rework for the current Mathlib; cf. "complete Lean archive", T5). -/
theorem UJ_gamma_anticomm :
    UJ * gammaF.map (star : ℂ → ℂ) * UJ = -gammaF := by
  sorry
end ThetLogos
