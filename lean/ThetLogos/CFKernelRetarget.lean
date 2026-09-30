import ThetLogos.OrderOne
import ThetLogos.CFKernelBase
import ThetLogos.InnerFluctuations
import ThetLogos.Scaffold32
import ThetLogos.MartinettiRep

namespace ThetLogos
open Matrix

/-! # CFKernel Retarget: 12 exotic survivor matrices (46 → 22)

Explicit real basis for the 12-dimensional exotic part of W22, from
`h4-spike/w22_characterization.txt`. Each complex coupling contributes a
real (Re) and imaginary (Im) direction.

Index sectors: H_L 0-7, H_R 8-15, H_L^c 16-23, H_R^c 24-31.
partner(i) = i+16 for i<16, i-16 for i≥16.

**Grading note** (corrected 2026-09-29): W22 "grading-odd" is the
equation `gammaF * D + D * gammaF = 0` for the repo's
`gammaF = diag(+1×8, -1×8, -1×8, +1×8)` (`Scaffold32.gammaF`).
All 12 exotic directions below satisfy it: every support pair `(i,j)`
joins indices of opposite `gammaF`-sign, so the anticommutator vanishes
entrywise (proved as `exotic{Re,Im}*_gradingOdd`). An earlier draft of
this note used the wrong diagonal `diag(+1×16,-1×16)` and wrongly
claimed 8 directions fail; that claim is retracted.
-/

-- ============================================================================
-- 1. nuL_eR : (0,9) orbit
-- ============================================================================

def exoticReNuLeR : Matrix I32 I32 ℂ := fun i j =>
  if (i = 0 ∧ j = 9) ∨ (i = 9 ∧ j = 0) ∨
     (i = 16 ∧ j = 25) ∨ (i = 25 ∧ j = 16) then 1 else 0

def exoticImNuLeR : Matrix I32 I32 ℂ := fun i j =>
  if (i = 0 ∧ j = 9) ∨ (i = 25 ∧ j = 16) then Complex.I
  else if (i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25) then -Complex.I
  else 0

-- ============================================================================
-- 2. eL_nuR : (1,8) orbit
-- ============================================================================

def exoticReELNuR : Matrix I32 I32 ℂ := fun i j =>
  if (i = 1 ∧ j = 8) ∨ (i = 8 ∧ j = 1) ∨
     (i = 17 ∧ j = 24) ∨ (i = 24 ∧ j = 17) then 1 else 0

def exoticImELNuR : Matrix I32 I32 ℂ := fun i j =>
  if (i = 1 ∧ j = 8) ∨ (i = 24 ∧ j = 17) then Complex.I
  else if (i = 8 ∧ j = 1) ∨ (i = 17 ∧ j = 24) then -Complex.I
  else 0

-- ============================================================================
-- 3. uL_dR : color-universal (2,11),(4,13),(6,15) + J partners
-- ============================================================================

def exoticReULDR : Matrix I32 I32 ℂ := fun i j =>
  if (i = 2 ∧ j = 11) ∨ (i = 11 ∧ j = 2) ∨
     (i = 4 ∧ j = 13) ∨ (i = 13 ∧ j = 4) ∨
     (i = 6 ∧ j = 15) ∨ (i = 15 ∧ j = 6) ∨
     (i = 18 ∧ j = 27) ∨ (i = 27 ∧ j = 18) ∨
     (i = 20 ∧ j = 29) ∨ (i = 29 ∧ j = 20) ∨
     (i = 22 ∧ j = 31) ∨ (i = 31 ∧ j = 22) then 1 else 0

def exoticImULDR : Matrix I32 I32 ℂ := fun i j =>
  if (i = 2 ∧ j = 11) ∨ (i = 4 ∧ j = 13) ∨ (i = 6 ∧ j = 15) ∨
     (i = 27 ∧ j = 18) ∨ (i = 29 ∧ j = 20) ∨ (i = 31 ∧ j = 22) then Complex.I
  else if (i = 11 ∧ j = 2) ∨ (i = 13 ∧ j = 4) ∨ (i = 15 ∧ j = 6) ∨
     (i = 18 ∧ j = 27) ∨ (i = 20 ∧ j = 29) ∨ (i = 22 ∧ j = 31) then -Complex.I
  else 0

-- ============================================================================
-- 4. dL_uR : color-universal (3,10),(5,12),(7,14) + J partners
-- ============================================================================

def exoticReDLUR : Matrix I32 I32 ℂ := fun i j =>
  if (i = 3 ∧ j = 10) ∨ (i = 10 ∧ j = 3) ∨
     (i = 5 ∧ j = 12) ∨ (i = 12 ∧ j = 5) ∨
     (i = 7 ∧ j = 14) ∨ (i = 14 ∧ j = 7) ∨
     (i = 19 ∧ j = 26) ∨ (i = 26 ∧ j = 19) ∨
     (i = 21 ∧ j = 28) ∨ (i = 28 ∧ j = 21) ∨
     (i = 23 ∧ j = 30) ∨ (i = 30 ∧ j = 23) then 1 else 0

def exoticImDLUR : Matrix I32 I32 ℂ := fun i j =>
  if (i = 3 ∧ j = 10) ∨ (i = 5 ∧ j = 12) ∨ (i = 7 ∧ j = 14) ∨
     (i = 26 ∧ j = 19) ∨ (i = 28 ∧ j = 21) ∨ (i = 30 ∧ j = 23) then Complex.I
  else if (i = 10 ∧ j = 3) ∨ (i = 12 ∧ j = 5) ∨ (i = 14 ∧ j = 7) ∨
     (i = 19 ∧ j = 26) ∨ (i = 21 ∧ j = 28) ∨ (i = 23 ∧ j = 30) then -Complex.I
  else 0

-- ============================================================================
-- 5. nuR_ebarR : (8,25) orbit
-- ============================================================================

def exoticReNuREbarR : Matrix I32 I32 ℂ := fun i j =>
  if (i = 8 ∧ j = 25) ∨ (i = 25 ∧ j = 8) ∨
     (i = 24 ∧ j = 9) ∨ (i = 9 ∧ j = 24) then 1 else 0

def exoticImNuREbarR : Matrix I32 I32 ℂ := fun i j =>
  if (i = 8 ∧ j = 25) ∨ (i = 9 ∧ j = 24) then Complex.I
  else if (i = 25 ∧ j = 8) ∨ (i = 24 ∧ j = 9) then -Complex.I
  else 0

-- ============================================================================
-- 6. eR_ebarR : J-degenerate (9,25) orbit
-- ============================================================================

def exoticReEREbarR : Matrix I32 I32 ℂ := fun i j =>
  if (i = 9 ∧ j = 25) ∨ (i = 25 ∧ j = 9) then 1 else 0

def exoticImEREbarR : Matrix I32 I32 ℂ := fun i j =>
  if (i = 9 ∧ j = 25) then Complex.I
  else if (i = 25 ∧ j = 9) then -Complex.I
  else 0

/-! ## Self-adjointness -/

theorem exoticReNuLeR_symm (i j : I32)
    (h : (i = 0 ∧ j = 9) ∨ (i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25) ∨ (i = 25 ∧ j = 16)) :
    (j = 0 ∧ i = 9) ∨ (j = 9 ∧ i = 0) ∨ (j = 16 ∧ i = 25) ∨ (j = 25 ∧ i = 16) := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem exoticReNuLeR_selfAdjoint : exoticReNuLeR.conjTranspose = exoticReNuLeR := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  unfold exoticReNuLeR
  by_cases h : (i = 0 ∧ j = 9) ∨ (i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25) ∨ (i = 25 ∧ j = 16)
  · have h1 := exoticReNuLeR_symm i j h
    simp [h, h1]
  · have h1 : ¬((j = 0 ∧ i = 9) ∨ (j = 9 ∧ i = 0) ∨ (j = 16 ∧ i = 25) ∨ (j = 25 ∧ i = 16)) :=
      fun h3 => h (exoticReNuLeR_symm j i h3)
    simp [h, h1]

/-! ## J-compatibility -/

theorem exoticReNuLeR_Jsupp (i j : I32)
    (h : (i = 0 ∧ j = 9) ∨ (i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25) ∨ (i = 25 ∧ j = 16)) :
    (partner j = 0 ∧ partner i = 9) ∨ (partner j = 9 ∧ partner i = 0) ∨
    (partner j = 16 ∧ partner i = 25) ∨ (partner j = 25 ∧ partner i = 16) := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · simp [partner]
  · simp [partner]
  · simp [partner]
  · simp [partner]

/-! ## Phase 2b: verification lemmas for the 12 explicit exotic matrices

Each complex coupling contributes a real (Re) and an imaginary (Im)
direction. For every direction we prove: self-adjointness, grading
oddness (`gammaF * D + D * gammaF = 0`), `IsJCompatible`, and
commutation with `cfMat`. Proofs are by support disjunction (no
`fin_cases` enumeration), using the repo's `gammaF_mul_apply` /
`mul_gammaF_apply` (`FiniteSpectralTriple.lean`) and `UJ_conj_apply`
(`Scaffold32.lean`).
-/

-- J-partner involution packaged for rewriting `partner j = b` into `j = partner b`.
theorem partner_eq_of {a b : I32} (h : partner a = b) : a = partner b := by
  have h2 := congrArg partner h
  rwa [partner_involutive] at h2

/-! ### NuLeR (Re) -/

theorem exoticReNuLeR_Jchar (i j : I32) :
    ((partner j = 0 ∧ partner i = 9) ∨ (partner j = 9 ∧ partner i = 0) ∨ (partner j = 16 ∧ partner i = 25) ∨ (partner j = 25 ∧ partner i = 16)) ↔
    ((i = 0 ∧ j = 9) ∨ (i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25) ∨ (i = 25 ∧ j = 16)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩)
    · have hj : j = (16:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (0:I32) = (16:I32) from by decide] at h1'
      have hi : i = (25:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (9:I32) = (25:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (⟨rfl, rfl⟩)))
    · have hj : j = (25:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (9:I32) = (25:I32) from by decide] at h1'
      have hi : i = (16:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (0:I32) = (16:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · have hj : j = (0:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (16:I32) = (0:I32) from by decide] at h1'
      have hi : i = (9:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (25:I32) = (9:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · have hj : j = (9:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (25:I32) = (9:I32) from by decide] at h1'
      have hi : i = (0:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (16:I32) = (0:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inl ⟨rfl, rfl⟩
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> simp [partner]

theorem exoticReNuLeR_gsign (i j : I32)
    (h : (i = 0 ∧ j = 9) ∨ (i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25) ∨ (i = 25 ∧ j = 16)) :
    gammaF i i + gammaF j j = 0 := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · have g1 : gammaF (0:I32) (0:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (9:I32) (9:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (9:I32) (9:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (0:I32) (0:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (16:I32) (16:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (25:I32) (25:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (25:I32) (25:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (16:I32) (16:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num

theorem exoticReNuLeR_cfInd (i j : I32)
    (h : (i = 0 ∧ j = 9) ∨ (i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25) ∨ (i = 25 ∧ j = 16)) :
    cfIndicator i = cfIndicator j := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp

theorem exoticReNuLeR_gradingOdd : gammaF * exoticReNuLeR + exoticReNuLeR * gammaF = 0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply, gammaF_mul_apply, mul_gammaF_apply]
  by_cases h : (i = 0 ∧ j = 9) ∨ (i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25) ∨ (i = 25 ∧ j = 16)
  · have hD : exoticReNuLeR i j = 1 := by unfold exoticReNuLeR; simp [h]
    have hsign : gammaF i i + gammaF j j = 0 := exoticReNuLeR_gsign i j h
    rw [hD]
    linear_combination hsign
  · have hD : exoticReNuLeR i j = 0 := by unfold exoticReNuLeR; simp [h]
    rw [hD]; simp

theorem exoticReNuLeR_Jcompat : IsJCompatible exoticReNuLeR := by
  show UJ * exoticReNuLeR.transpose * UJ = exoticReNuLeR
  ext i j
  rw [UJ_conj_apply, Matrix.transpose_apply]
  unfold exoticReNuLeR
  simp only [exoticReNuLeR_Jchar i j]

theorem exoticReNuLeR_cfMat : exoticReNuLeR * cfMat - cfMat * exoticReNuLeR = 0 := by
  ext i j
  rw [Matrix.sub_apply, Matrix.zero_apply, mul_cfMat_apply, cfMat_mul_apply]
  by_cases h : (i = 0 ∧ j = 9) ∨ (i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25) ∨ (i = 25 ∧ j = 16)
  · have hD : exoticReNuLeR i j = 1 := by unfold exoticReNuLeR; simp [h]
    have hcf : cfIndicator i = cfIndicator j := exoticReNuLeR_cfInd i j h
    rw [hD, hcf]; ring
  · have hD : exoticReNuLeR i j = 0 := by unfold exoticReNuLeR; simp [h]
    rw [hD]; ring

/-! ### NuLeR (Im) -/

theorem exoticImNuLeR_swap1 (i j : I32) :
    ((j = 0 ∧ i = 9) ∨ (j = 25 ∧ i = 16)) ↔ ((i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (⟨h2, h1⟩)
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (⟨h2, h1⟩)

theorem exoticImNuLeR_swap2 (i j : I32) :
    ((j = 9 ∧ i = 0) ∨ (j = 16 ∧ i = 25)) ↔ ((i = 0 ∧ j = 9) ∨ (i = 25 ∧ j = 16)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (⟨h2, h1⟩)
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (⟨h2, h1⟩)

theorem exoticImNuLeR_disjoint (i j : I32)
    (h : (i = 0 ∧ j = 9) ∨ (i = 25 ∧ j = 16)) : ¬ ((i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25)) := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · intro hcon
    rcases hcon with ⟨h1,_⟩|⟨h1,_⟩
    · exact (by decide : (0:I32) ≠ 9) h1
    · exact (by decide : (0:I32) ≠ 16) h1
  · intro hcon
    rcases hcon with ⟨h1,_⟩|⟨h1,_⟩
    · exact (by decide : (25:I32) ≠ 9) h1
    · exact (by decide : (25:I32) ≠ 16) h1

theorem exoticImNuLeR_Jchar1 (i j : I32) :
    ((partner j = 0 ∧ partner i = 9) ∨ (partner j = 25 ∧ partner i = 16)) ↔
    ((i = 0 ∧ j = 9) ∨ (i = 25 ∧ j = 16)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
    · have hj : j = (16:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (0:I32) = (16:I32) from by decide] at h1'
      have hi : i = (25:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (9:I32) = (25:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (⟨rfl, rfl⟩)
    · have hj : j = (9:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (25:I32) = (9:I32) from by decide] at h1'
      have hi : i = (0:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (16:I32) = (0:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inl ⟨rfl, rfl⟩
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> simp [partner]

theorem exoticImNuLeR_Jchar2 (i j : I32) :
    ((partner j = 9 ∧ partner i = 0) ∨ (partner j = 16 ∧ partner i = 25)) ↔
    ((i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
    · have hj : j = (25:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (9:I32) = (25:I32) from by decide] at h1'
      have hi : i = (16:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (0:I32) = (16:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (⟨rfl, rfl⟩)
    · have hj : j = (0:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (16:I32) = (0:I32) from by decide] at h1'
      have hi : i = (9:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (25:I32) = (9:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inl ⟨rfl, rfl⟩
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> simp [partner]

theorem exoticImNuLeR_gsign (i j : I32)
    (h : ((i = 0 ∧ j = 9) ∨ (i = 25 ∧ j = 16)) ∨ ((i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25))) :
    gammaF i i + gammaF j j = 0 := by
  rcases h with (⟨rfl,rfl⟩|⟨rfl,rfl⟩)|(⟨rfl,rfl⟩|⟨rfl,rfl⟩)
  · have g1 : gammaF (0:I32) (0:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (9:I32) (9:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (25:I32) (25:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (16:I32) (16:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (9:I32) (9:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (0:I32) (0:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (16:I32) (16:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (25:I32) (25:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num

theorem exoticImNuLeR_cfInd (i j : I32)
    (h : ((i = 0 ∧ j = 9) ∨ (i = 25 ∧ j = 16)) ∨ ((i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25))) :
    cfIndicator i = cfIndicator j := by
  rcases h with (⟨rfl,rfl⟩|⟨rfl,rfl⟩)|(⟨rfl,rfl⟩|⟨rfl,rfl⟩)
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp

theorem exoticImNuLeR_selfAdjoint : exoticImNuLeR.conjTranspose = exoticImNuLeR := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  unfold exoticImNuLeR
  simp only [exoticImNuLeR_swap1 i j, exoticImNuLeR_swap2 i j]
  by_cases h1 : (i = 0 ∧ j = 9) ∨ (i = 25 ∧ j = 16)
  · by_cases h2 : (i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25)
    · exact absurd h2 (exoticImNuLeR_disjoint i j h1)
    · simp [h1, h2]
  · by_cases h2 : (i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25)
    · simp [h1, h2]
    · simp [h1, h2]

theorem exoticImNuLeR_gradingOdd : gammaF * exoticImNuLeR + exoticImNuLeR * gammaF = 0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply, gammaF_mul_apply, mul_gammaF_apply]
  by_cases h1 : (i = 0 ∧ j = 9) ∨ (i = 25 ∧ j = 16)
  · have hD : exoticImNuLeR i j = Complex.I := by unfold exoticImNuLeR; simp [h1]
    have hsign : gammaF i i + gammaF j j = 0 := exoticImNuLeR_gsign i j (Or.inl h1)
    rw [hD]
    have hrw : gammaF i i * Complex.I + Complex.I * gammaF j j
        = (gammaF i i + gammaF j j) * Complex.I := by ring
    rw [hrw, hsign, zero_mul]
  · by_cases h2 : (i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25)
    · have hD : exoticImNuLeR i j = -Complex.I := by unfold exoticImNuLeR; simp [h1, h2]
      have hsign : gammaF i i + gammaF j j = 0 := exoticImNuLeR_gsign i j (Or.inr h2)
      rw [hD]
      have hrw : gammaF i i * -Complex.I + -Complex.I * gammaF j j
          = (gammaF i i + gammaF j j) * -Complex.I := by ring
      rw [hrw, hsign, zero_mul]
    · have hD : exoticImNuLeR i j = 0 := by unfold exoticImNuLeR; simp [h1, h2]
      rw [hD]; simp

theorem exoticImNuLeR_Jcompat : IsJCompatible exoticImNuLeR := by
  show UJ * exoticImNuLeR.transpose * UJ = exoticImNuLeR
  ext i j
  rw [UJ_conj_apply, Matrix.transpose_apply]
  unfold exoticImNuLeR
  simp only [exoticImNuLeR_Jchar1 i j, exoticImNuLeR_Jchar2 i j]

theorem exoticImNuLeR_cfMat : exoticImNuLeR * cfMat - cfMat * exoticImNuLeR = 0 := by
  ext i j
  rw [Matrix.sub_apply, Matrix.zero_apply, mul_cfMat_apply, cfMat_mul_apply]
  by_cases h1 : (i = 0 ∧ j = 9) ∨ (i = 25 ∧ j = 16)
  · have hD : exoticImNuLeR i j = Complex.I := by unfold exoticImNuLeR; simp [h1]
    have hcf : cfIndicator i = cfIndicator j := exoticImNuLeR_cfInd i j (Or.inl h1)
    rw [hD, hcf]; ring
  · by_cases h2 : (i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25)
    · have hD : exoticImNuLeR i j = -Complex.I := by unfold exoticImNuLeR; simp [h1, h2]
      have hcf : cfIndicator i = cfIndicator j := exoticImNuLeR_cfInd i j (Or.inr h2)
      rw [hD, hcf]; ring
    · have hD : exoticImNuLeR i j = 0 := by unfold exoticImNuLeR; simp [h1, h2]
      rw [hD]; ring

/-! ### ELNuR (Re) -/

theorem exoticReELNuR_symm (i j : I32)
    (h : (i = 1 ∧ j = 8) ∨ (i = 8 ∧ j = 1) ∨ (i = 17 ∧ j = 24) ∨ (i = 24 ∧ j = 17)) :
    (j = 1 ∧ i = 8) ∨ (j = 8 ∧ i = 1) ∨ (j = 17 ∧ i = 24) ∨ (j = 24 ∧ i = 17) := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inr (Or.inr (⟨rfl, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem exoticReELNuR_Jchar (i j : I32) :
    ((partner j = 1 ∧ partner i = 8) ∨ (partner j = 8 ∧ partner i = 1) ∨ (partner j = 17 ∧ partner i = 24) ∨ (partner j = 24 ∧ partner i = 17)) ↔
    ((i = 1 ∧ j = 8) ∨ (i = 8 ∧ j = 1) ∨ (i = 17 ∧ j = 24) ∨ (i = 24 ∧ j = 17)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩)
    · have hj : j = (17:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (1:I32) = (17:I32) from by decide] at h1'
      have hi : i = (24:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (8:I32) = (24:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (⟨rfl, rfl⟩)))
    · have hj : j = (24:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (8:I32) = (24:I32) from by decide] at h1'
      have hi : i = (17:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (1:I32) = (17:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · have hj : j = (1:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (17:I32) = (1:I32) from by decide] at h1'
      have hi : i = (8:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (24:I32) = (8:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · have hj : j = (8:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (24:I32) = (8:I32) from by decide] at h1'
      have hi : i = (1:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (17:I32) = (1:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inl ⟨rfl, rfl⟩
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> simp [partner]

theorem exoticReELNuR_gsign (i j : I32)
    (h : (i = 1 ∧ j = 8) ∨ (i = 8 ∧ j = 1) ∨ (i = 17 ∧ j = 24) ∨ (i = 24 ∧ j = 17)) :
    gammaF i i + gammaF j j = 0 := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · have g1 : gammaF (1:I32) (1:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (8:I32) (8:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (8:I32) (8:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (1:I32) (1:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (17:I32) (17:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (24:I32) (24:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (24:I32) (24:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (17:I32) (17:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num

theorem exoticReELNuR_cfInd (i j : I32)
    (h : (i = 1 ∧ j = 8) ∨ (i = 8 ∧ j = 1) ∨ (i = 17 ∧ j = 24) ∨ (i = 24 ∧ j = 17)) :
    cfIndicator i = cfIndicator j := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp

theorem exoticReELNuR_selfAdjoint : exoticReELNuR.conjTranspose = exoticReELNuR := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  unfold exoticReELNuR
  by_cases h : (i = 1 ∧ j = 8) ∨ (i = 8 ∧ j = 1) ∨ (i = 17 ∧ j = 24) ∨ (i = 24 ∧ j = 17)
  · have h1 := exoticReELNuR_symm i j h
    simp [h, h1]
  · have h1 : ¬((j = 1 ∧ i = 8) ∨ (j = 8 ∧ i = 1) ∨ (j = 17 ∧ i = 24) ∨ (j = 24 ∧ i = 17)) :=
      fun h3 => h (exoticReELNuR_symm j i h3)
    simp [h, h1]

theorem exoticReELNuR_gradingOdd : gammaF * exoticReELNuR + exoticReELNuR * gammaF = 0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply, gammaF_mul_apply, mul_gammaF_apply]
  by_cases h : (i = 1 ∧ j = 8) ∨ (i = 8 ∧ j = 1) ∨ (i = 17 ∧ j = 24) ∨ (i = 24 ∧ j = 17)
  · have hD : exoticReELNuR i j = 1 := by unfold exoticReELNuR; simp [h]
    have hsign : gammaF i i + gammaF j j = 0 := exoticReELNuR_gsign i j h
    rw [hD]
    linear_combination hsign
  · have hD : exoticReELNuR i j = 0 := by unfold exoticReELNuR; simp [h]
    rw [hD]; simp

theorem exoticReELNuR_Jcompat : IsJCompatible exoticReELNuR := by
  show UJ * exoticReELNuR.transpose * UJ = exoticReELNuR
  ext i j
  rw [UJ_conj_apply, Matrix.transpose_apply]
  unfold exoticReELNuR
  simp only [exoticReELNuR_Jchar i j]

theorem exoticReELNuR_cfMat : exoticReELNuR * cfMat - cfMat * exoticReELNuR = 0 := by
  ext i j
  rw [Matrix.sub_apply, Matrix.zero_apply, mul_cfMat_apply, cfMat_mul_apply]
  by_cases h : (i = 1 ∧ j = 8) ∨ (i = 8 ∧ j = 1) ∨ (i = 17 ∧ j = 24) ∨ (i = 24 ∧ j = 17)
  · have hD : exoticReELNuR i j = 1 := by unfold exoticReELNuR; simp [h]
    have hcf : cfIndicator i = cfIndicator j := exoticReELNuR_cfInd i j h
    rw [hD, hcf]; ring
  · have hD : exoticReELNuR i j = 0 := by unfold exoticReELNuR; simp [h]
    rw [hD]; ring

/-! ### ELNuR (Im) -/

theorem exoticImELNuR_swap1 (i j : I32) :
    ((j = 1 ∧ i = 8) ∨ (j = 24 ∧ i = 17)) ↔ ((i = 8 ∧ j = 1) ∨ (i = 17 ∧ j = 24)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (⟨h2, h1⟩)
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (⟨h2, h1⟩)

theorem exoticImELNuR_swap2 (i j : I32) :
    ((j = 8 ∧ i = 1) ∨ (j = 17 ∧ i = 24)) ↔ ((i = 1 ∧ j = 8) ∨ (i = 24 ∧ j = 17)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (⟨h2, h1⟩)
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (⟨h2, h1⟩)

theorem exoticImELNuR_disjoint (i j : I32)
    (h : (i = 1 ∧ j = 8) ∨ (i = 24 ∧ j = 17)) : ¬ ((i = 8 ∧ j = 1) ∨ (i = 17 ∧ j = 24)) := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · intro hcon
    rcases hcon with ⟨h1,_⟩|⟨h1,_⟩
    · exact (by decide : (1:I32) ≠ 8) h1
    · exact (by decide : (1:I32) ≠ 17) h1
  · intro hcon
    rcases hcon with ⟨h1,_⟩|⟨h1,_⟩
    · exact (by decide : (24:I32) ≠ 8) h1
    · exact (by decide : (24:I32) ≠ 17) h1

theorem exoticImELNuR_Jchar1 (i j : I32) :
    ((partner j = 1 ∧ partner i = 8) ∨ (partner j = 24 ∧ partner i = 17)) ↔
    ((i = 1 ∧ j = 8) ∨ (i = 24 ∧ j = 17)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
    · have hj : j = (17:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (1:I32) = (17:I32) from by decide] at h1'
      have hi : i = (24:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (8:I32) = (24:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (⟨rfl, rfl⟩)
    · have hj : j = (8:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (24:I32) = (8:I32) from by decide] at h1'
      have hi : i = (1:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (17:I32) = (1:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inl ⟨rfl, rfl⟩
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> simp [partner]

theorem exoticImELNuR_Jchar2 (i j : I32) :
    ((partner j = 8 ∧ partner i = 1) ∨ (partner j = 17 ∧ partner i = 24)) ↔
    ((i = 8 ∧ j = 1) ∨ (i = 17 ∧ j = 24)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
    · have hj : j = (24:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (8:I32) = (24:I32) from by decide] at h1'
      have hi : i = (17:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (1:I32) = (17:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (⟨rfl, rfl⟩)
    · have hj : j = (1:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (17:I32) = (1:I32) from by decide] at h1'
      have hi : i = (8:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (24:I32) = (8:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inl ⟨rfl, rfl⟩
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> simp [partner]

theorem exoticImELNuR_gsign (i j : I32)
    (h : ((i = 1 ∧ j = 8) ∨ (i = 24 ∧ j = 17)) ∨ ((i = 8 ∧ j = 1) ∨ (i = 17 ∧ j = 24))) :
    gammaF i i + gammaF j j = 0 := by
  rcases h with (⟨rfl,rfl⟩|⟨rfl,rfl⟩)|(⟨rfl,rfl⟩|⟨rfl,rfl⟩)
  · have g1 : gammaF (1:I32) (1:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (8:I32) (8:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (24:I32) (24:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (17:I32) (17:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (8:I32) (8:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (1:I32) (1:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (17:I32) (17:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (24:I32) (24:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num

theorem exoticImELNuR_cfInd (i j : I32)
    (h : ((i = 1 ∧ j = 8) ∨ (i = 24 ∧ j = 17)) ∨ ((i = 8 ∧ j = 1) ∨ (i = 17 ∧ j = 24))) :
    cfIndicator i = cfIndicator j := by
  rcases h with (⟨rfl,rfl⟩|⟨rfl,rfl⟩)|(⟨rfl,rfl⟩|⟨rfl,rfl⟩)
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp

theorem exoticImELNuR_selfAdjoint : exoticImELNuR.conjTranspose = exoticImELNuR := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  unfold exoticImELNuR
  simp only [exoticImELNuR_swap1 i j, exoticImELNuR_swap2 i j]
  by_cases h1 : (i = 1 ∧ j = 8) ∨ (i = 24 ∧ j = 17)
  · by_cases h2 : (i = 8 ∧ j = 1) ∨ (i = 17 ∧ j = 24)
    · exact absurd h2 (exoticImELNuR_disjoint i j h1)
    · simp [h1, h2]
  · by_cases h2 : (i = 8 ∧ j = 1) ∨ (i = 17 ∧ j = 24)
    · simp [h1, h2]
    · simp [h1, h2]

theorem exoticImELNuR_gradingOdd : gammaF * exoticImELNuR + exoticImELNuR * gammaF = 0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply, gammaF_mul_apply, mul_gammaF_apply]
  by_cases h1 : (i = 1 ∧ j = 8) ∨ (i = 24 ∧ j = 17)
  · have hD : exoticImELNuR i j = Complex.I := by unfold exoticImELNuR; simp [h1]
    have hsign : gammaF i i + gammaF j j = 0 := exoticImELNuR_gsign i j (Or.inl h1)
    rw [hD]
    have hrw : gammaF i i * Complex.I + Complex.I * gammaF j j
        = (gammaF i i + gammaF j j) * Complex.I := by ring
    rw [hrw, hsign, zero_mul]
  · by_cases h2 : (i = 8 ∧ j = 1) ∨ (i = 17 ∧ j = 24)
    · have hD : exoticImELNuR i j = -Complex.I := by unfold exoticImELNuR; simp [h1, h2]
      have hsign : gammaF i i + gammaF j j = 0 := exoticImELNuR_gsign i j (Or.inr h2)
      rw [hD]
      have hrw : gammaF i i * -Complex.I + -Complex.I * gammaF j j
          = (gammaF i i + gammaF j j) * -Complex.I := by ring
      rw [hrw, hsign, zero_mul]
    · have hD : exoticImELNuR i j = 0 := by unfold exoticImELNuR; simp [h1, h2]
      rw [hD]; simp

theorem exoticImELNuR_Jcompat : IsJCompatible exoticImELNuR := by
  show UJ * exoticImELNuR.transpose * UJ = exoticImELNuR
  ext i j
  rw [UJ_conj_apply, Matrix.transpose_apply]
  unfold exoticImELNuR
  simp only [exoticImELNuR_Jchar1 i j, exoticImELNuR_Jchar2 i j]

theorem exoticImELNuR_cfMat : exoticImELNuR * cfMat - cfMat * exoticImELNuR = 0 := by
  ext i j
  rw [Matrix.sub_apply, Matrix.zero_apply, mul_cfMat_apply, cfMat_mul_apply]
  by_cases h1 : (i = 1 ∧ j = 8) ∨ (i = 24 ∧ j = 17)
  · have hD : exoticImELNuR i j = Complex.I := by unfold exoticImELNuR; simp [h1]
    have hcf : cfIndicator i = cfIndicator j := exoticImELNuR_cfInd i j (Or.inl h1)
    rw [hD, hcf]; ring
  · by_cases h2 : (i = 8 ∧ j = 1) ∨ (i = 17 ∧ j = 24)
    · have hD : exoticImELNuR i j = -Complex.I := by unfold exoticImELNuR; simp [h1, h2]
      have hcf : cfIndicator i = cfIndicator j := exoticImELNuR_cfInd i j (Or.inr h2)
      rw [hD, hcf]; ring
    · have hD : exoticImELNuR i j = 0 := by unfold exoticImELNuR; simp [h1, h2]
      rw [hD]; ring

/-! ### ULDR (Re) -/

theorem exoticReULDR_symm (i j : I32)
    (h : (i = 2 ∧ j = 11) ∨ (i = 11 ∧ j = 2) ∨ (i = 4 ∧ j = 13) ∨ (i = 13 ∧ j = 4) ∨ (i = 6 ∧ j = 15) ∨ (i = 15 ∧ j = 6) ∨ (i = 18 ∧ j = 27) ∨ (i = 27 ∧ j = 18) ∨ (i = 20 ∧ j = 29) ∨ (i = 29 ∧ j = 20) ∨ (i = 22 ∧ j = 31) ∨ (i = 31 ∧ j = 22)) :
    (j = 2 ∧ i = 11) ∨ (j = 11 ∧ i = 2) ∨ (j = 4 ∧ i = 13) ∨ (j = 13 ∧ i = 4) ∨ (j = 6 ∧ i = 15) ∨ (j = 15 ∧ i = 6) ∨ (j = 18 ∧ i = 27) ∨ (j = 27 ∧ i = 18) ∨ (j = 20 ∧ i = 29) ∨ (j = 29 ∧ i = 20) ∨ (j = 22 ∧ i = 31) ∨ (j = 31 ∧ i = 22) := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, rfl⟩)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))))))

theorem exoticReULDR_Jchar (i j : I32) :
    ((partner j = 2 ∧ partner i = 11) ∨ (partner j = 11 ∧ partner i = 2) ∨ (partner j = 4 ∧ partner i = 13) ∨ (partner j = 13 ∧ partner i = 4) ∨ (partner j = 6 ∧ partner i = 15) ∨ (partner j = 15 ∧ partner i = 6) ∨ (partner j = 18 ∧ partner i = 27) ∨ (partner j = 27 ∧ partner i = 18) ∨ (partner j = 20 ∧ partner i = 29) ∨ (partner j = 29 ∧ partner i = 20) ∨ (partner j = 22 ∧ partner i = 31) ∨ (partner j = 31 ∧ partner i = 22)) ↔
    ((i = 2 ∧ j = 11) ∨ (i = 11 ∧ j = 2) ∨ (i = 4 ∧ j = 13) ∨ (i = 13 ∧ j = 4) ∨ (i = 6 ∧ j = 15) ∨ (i = 15 ∧ j = 6) ∨ (i = 18 ∧ j = 27) ∨ (i = 27 ∧ j = 18) ∨ (i = 20 ∧ j = 29) ∨ (i = 29 ∧ j = 20) ∨ (i = 22 ∧ j = 31) ∨ (i = 31 ∧ j = 22)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩)
    · have hj : j = (18:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (2:I32) = (18:I32) from by decide] at h1'
      have hi : i = (27:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (11:I32) = (27:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))))
    · have hj : j = (27:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (11:I32) = (27:I32) from by decide] at h1'
      have hi : i = (18:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (2:I32) = (18:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))
    · have hj : j = (20:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (4:I32) = (20:I32) from by decide] at h1'
      have hi : i = (29:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (13:I32) = (29:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))))))
    · have hj : j = (29:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (13:I32) = (29:I32) from by decide] at h1'
      have hi : i = (20:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (4:I32) = (20:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))))
    · have hj : j = (22:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (6:I32) = (22:I32) from by decide] at h1'
      have hi : i = (31:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (15:I32) = (31:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, rfl⟩)))))))))))
    · have hj : j = (31:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (15:I32) = (31:I32) from by decide] at h1'
      have hi : i = (22:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (6:I32) = (22:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))))))
    · have hj : j = (2:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (18:I32) = (2:I32) from by decide] at h1'
      have hi : i = (11:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (27:I32) = (11:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · have hj : j = (11:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (27:I32) = (11:I32) from by decide] at h1'
      have hi : i = (2:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (18:I32) = (2:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inl ⟨rfl, rfl⟩
    · have hj : j = (4:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (20:I32) = (4:I32) from by decide] at h1'
      have hi : i = (13:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (29:I32) = (13:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    · have hj : j = (13:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (29:I32) = (13:I32) from by decide] at h1'
      have hi : i = (4:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (20:I32) = (4:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · have hj : j = (6:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (22:I32) = (6:I32) from by decide] at h1'
      have hi : i = (15:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (31:I32) = (15:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
    · have hj : j = (15:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (31:I32) = (15:I32) from by decide] at h1'
      have hi : i = (6:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (22:I32) = (6:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> simp [partner]

theorem exoticReULDR_gsign (i j : I32)
    (h : (i = 2 ∧ j = 11) ∨ (i = 11 ∧ j = 2) ∨ (i = 4 ∧ j = 13) ∨ (i = 13 ∧ j = 4) ∨ (i = 6 ∧ j = 15) ∨ (i = 15 ∧ j = 6) ∨ (i = 18 ∧ j = 27) ∨ (i = 27 ∧ j = 18) ∨ (i = 20 ∧ j = 29) ∨ (i = 29 ∧ j = 20) ∨ (i = 22 ∧ j = 31) ∨ (i = 31 ∧ j = 22)) :
    gammaF i i + gammaF j j = 0 := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · have g1 : gammaF (2:I32) (2:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (11:I32) (11:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (11:I32) (11:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (2:I32) (2:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (4:I32) (4:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (13:I32) (13:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (13:I32) (13:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (4:I32) (4:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (6:I32) (6:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (15:I32) (15:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (15:I32) (15:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (6:I32) (6:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (18:I32) (18:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (27:I32) (27:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (27:I32) (27:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (18:I32) (18:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (20:I32) (20:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (29:I32) (29:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (29:I32) (29:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (20:I32) (20:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (22:I32) (22:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (31:I32) (31:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (31:I32) (31:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (22:I32) (22:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num

theorem exoticReULDR_cfInd (i j : I32)
    (h : (i = 2 ∧ j = 11) ∨ (i = 11 ∧ j = 2) ∨ (i = 4 ∧ j = 13) ∨ (i = 13 ∧ j = 4) ∨ (i = 6 ∧ j = 15) ∨ (i = 15 ∧ j = 6) ∨ (i = 18 ∧ j = 27) ∨ (i = 27 ∧ j = 18) ∨ (i = 20 ∧ j = 29) ∨ (i = 29 ∧ j = 20) ∨ (i = 22 ∧ j = 31) ∨ (i = 31 ∧ j = 22)) :
    cfIndicator i = cfIndicator j := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp

theorem exoticReULDR_selfAdjoint : exoticReULDR.conjTranspose = exoticReULDR := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  unfold exoticReULDR
  by_cases h : (i = 2 ∧ j = 11) ∨ (i = 11 ∧ j = 2) ∨ (i = 4 ∧ j = 13) ∨ (i = 13 ∧ j = 4) ∨ (i = 6 ∧ j = 15) ∨ (i = 15 ∧ j = 6) ∨ (i = 18 ∧ j = 27) ∨ (i = 27 ∧ j = 18) ∨ (i = 20 ∧ j = 29) ∨ (i = 29 ∧ j = 20) ∨ (i = 22 ∧ j = 31) ∨ (i = 31 ∧ j = 22)
  · have h1 := exoticReULDR_symm i j h
    simp [h, h1]
  · have h1 : ¬((j = 2 ∧ i = 11) ∨ (j = 11 ∧ i = 2) ∨ (j = 4 ∧ i = 13) ∨ (j = 13 ∧ i = 4) ∨ (j = 6 ∧ i = 15) ∨ (j = 15 ∧ i = 6) ∨ (j = 18 ∧ i = 27) ∨ (j = 27 ∧ i = 18) ∨ (j = 20 ∧ i = 29) ∨ (j = 29 ∧ i = 20) ∨ (j = 22 ∧ i = 31) ∨ (j = 31 ∧ i = 22)) :=
      fun h3 => h (exoticReULDR_symm j i h3)
    simp [h, h1]

theorem exoticReULDR_gradingOdd : gammaF * exoticReULDR + exoticReULDR * gammaF = 0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply, gammaF_mul_apply, mul_gammaF_apply]
  by_cases h : (i = 2 ∧ j = 11) ∨ (i = 11 ∧ j = 2) ∨ (i = 4 ∧ j = 13) ∨ (i = 13 ∧ j = 4) ∨ (i = 6 ∧ j = 15) ∨ (i = 15 ∧ j = 6) ∨ (i = 18 ∧ j = 27) ∨ (i = 27 ∧ j = 18) ∨ (i = 20 ∧ j = 29) ∨ (i = 29 ∧ j = 20) ∨ (i = 22 ∧ j = 31) ∨ (i = 31 ∧ j = 22)
  · have hD : exoticReULDR i j = 1 := by unfold exoticReULDR; simp [h]
    have hsign : gammaF i i + gammaF j j = 0 := exoticReULDR_gsign i j h
    rw [hD]
    linear_combination hsign
  · have hD : exoticReULDR i j = 0 := by unfold exoticReULDR; simp [h]
    rw [hD]; simp

theorem exoticReULDR_Jcompat : IsJCompatible exoticReULDR := by
  show UJ * exoticReULDR.transpose * UJ = exoticReULDR
  ext i j
  rw [UJ_conj_apply, Matrix.transpose_apply]
  unfold exoticReULDR
  simp only [exoticReULDR_Jchar i j]

theorem exoticReULDR_cfMat : exoticReULDR * cfMat - cfMat * exoticReULDR = 0 := by
  ext i j
  rw [Matrix.sub_apply, Matrix.zero_apply, mul_cfMat_apply, cfMat_mul_apply]
  by_cases h : (i = 2 ∧ j = 11) ∨ (i = 11 ∧ j = 2) ∨ (i = 4 ∧ j = 13) ∨ (i = 13 ∧ j = 4) ∨ (i = 6 ∧ j = 15) ∨ (i = 15 ∧ j = 6) ∨ (i = 18 ∧ j = 27) ∨ (i = 27 ∧ j = 18) ∨ (i = 20 ∧ j = 29) ∨ (i = 29 ∧ j = 20) ∨ (i = 22 ∧ j = 31) ∨ (i = 31 ∧ j = 22)
  · have hD : exoticReULDR i j = 1 := by unfold exoticReULDR; simp [h]
    have hcf : cfIndicator i = cfIndicator j := exoticReULDR_cfInd i j h
    rw [hD, hcf]; ring
  · have hD : exoticReULDR i j = 0 := by unfold exoticReULDR; simp [h]
    rw [hD]; ring

/-! ### ULDR (Im) -/

theorem exoticImULDR_swap1 (i j : I32) :
    ((j = 2 ∧ i = 11) ∨ (j = 4 ∧ i = 13) ∨ (j = 6 ∧ i = 15) ∨ (j = 27 ∧ i = 18) ∨ (j = 29 ∧ i = 20) ∨ (j = 31 ∧ i = 22)) ↔ ((i = 11 ∧ j = 2) ∨ (i = 13 ∧ j = 4) ∨ (i = 15 ∧ j = 6) ∨ (i = 18 ∧ j = 27) ∨ (i = 20 ∧ j = 29) ∨ (i = 22 ∧ j = 31)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h2, h1⟩)))))
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h2, h1⟩)))))

theorem exoticImULDR_swap2 (i j : I32) :
    ((j = 11 ∧ i = 2) ∨ (j = 13 ∧ i = 4) ∨ (j = 15 ∧ i = 6) ∨ (j = 18 ∧ i = 27) ∨ (j = 20 ∧ i = 29) ∨ (j = 22 ∧ i = 31)) ↔ ((i = 2 ∧ j = 11) ∨ (i = 4 ∧ j = 13) ∨ (i = 6 ∧ j = 15) ∨ (i = 27 ∧ j = 18) ∨ (i = 29 ∧ j = 20) ∨ (i = 31 ∧ j = 22)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h2, h1⟩)))))
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h2, h1⟩)))))

theorem exoticImULDR_disjoint (i j : I32)
    (h : (i = 2 ∧ j = 11) ∨ (i = 4 ∧ j = 13) ∨ (i = 6 ∧ j = 15) ∨ (i = 27 ∧ j = 18) ∨ (i = 29 ∧ j = 20) ∨ (i = 31 ∧ j = 22)) : ¬ ((i = 11 ∧ j = 2) ∨ (i = 13 ∧ j = 4) ∨ (i = 15 ∧ j = 6) ∨ (i = 18 ∧ j = 27) ∨ (i = 20 ∧ j = 29) ∨ (i = 22 ∧ j = 31)) := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · intro hcon
    rcases hcon with ⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩
    · exact (by decide : (2:I32) ≠ 11) h1
    · exact (by decide : (2:I32) ≠ 13) h1
    · exact (by decide : (2:I32) ≠ 15) h1
    · exact (by decide : (2:I32) ≠ 18) h1
    · exact (by decide : (2:I32) ≠ 20) h1
    · exact (by decide : (2:I32) ≠ 22) h1
  · intro hcon
    rcases hcon with ⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩
    · exact (by decide : (4:I32) ≠ 11) h1
    · exact (by decide : (4:I32) ≠ 13) h1
    · exact (by decide : (4:I32) ≠ 15) h1
    · exact (by decide : (4:I32) ≠ 18) h1
    · exact (by decide : (4:I32) ≠ 20) h1
    · exact (by decide : (4:I32) ≠ 22) h1
  · intro hcon
    rcases hcon with ⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩
    · exact (by decide : (6:I32) ≠ 11) h1
    · exact (by decide : (6:I32) ≠ 13) h1
    · exact (by decide : (6:I32) ≠ 15) h1
    · exact (by decide : (6:I32) ≠ 18) h1
    · exact (by decide : (6:I32) ≠ 20) h1
    · exact (by decide : (6:I32) ≠ 22) h1
  · intro hcon
    rcases hcon with ⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩
    · exact (by decide : (27:I32) ≠ 11) h1
    · exact (by decide : (27:I32) ≠ 13) h1
    · exact (by decide : (27:I32) ≠ 15) h1
    · exact (by decide : (27:I32) ≠ 18) h1
    · exact (by decide : (27:I32) ≠ 20) h1
    · exact (by decide : (27:I32) ≠ 22) h1
  · intro hcon
    rcases hcon with ⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩
    · exact (by decide : (29:I32) ≠ 11) h1
    · exact (by decide : (29:I32) ≠ 13) h1
    · exact (by decide : (29:I32) ≠ 15) h1
    · exact (by decide : (29:I32) ≠ 18) h1
    · exact (by decide : (29:I32) ≠ 20) h1
    · exact (by decide : (29:I32) ≠ 22) h1
  · intro hcon
    rcases hcon with ⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩
    · exact (by decide : (31:I32) ≠ 11) h1
    · exact (by decide : (31:I32) ≠ 13) h1
    · exact (by decide : (31:I32) ≠ 15) h1
    · exact (by decide : (31:I32) ≠ 18) h1
    · exact (by decide : (31:I32) ≠ 20) h1
    · exact (by decide : (31:I32) ≠ 22) h1

theorem exoticImULDR_Jchar1 (i j : I32) :
    ((partner j = 2 ∧ partner i = 11) ∨ (partner j = 4 ∧ partner i = 13) ∨ (partner j = 6 ∧ partner i = 15) ∨ (partner j = 27 ∧ partner i = 18) ∨ (partner j = 29 ∧ partner i = 20) ∨ (partner j = 31 ∧ partner i = 22)) ↔
    ((i = 2 ∧ j = 11) ∨ (i = 4 ∧ j = 13) ∨ (i = 6 ∧ j = 15) ∨ (i = 27 ∧ j = 18) ∨ (i = 29 ∧ j = 20) ∨ (i = 31 ∧ j = 22)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩)
    · have hj : j = (18:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (2:I32) = (18:I32) from by decide] at h1'
      have hi : i = (27:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (11:I32) = (27:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    · have hj : j = (20:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (4:I32) = (20:I32) from by decide] at h1'
      have hi : i = (29:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (13:I32) = (29:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    · have hj : j = (22:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (6:I32) = (22:I32) from by decide] at h1'
      have hi : i = (31:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (15:I32) = (31:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, rfl⟩)))))
    · have hj : j = (11:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (27:I32) = (11:I32) from by decide] at h1'
      have hi : i = (2:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (18:I32) = (2:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inl ⟨rfl, rfl⟩
    · have hj : j = (13:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (29:I32) = (13:I32) from by decide] at h1'
      have hi : i = (4:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (20:I32) = (4:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · have hj : j = (15:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (31:I32) = (15:I32) from by decide] at h1'
      have hi : i = (6:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (22:I32) = (6:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> simp [partner]

theorem exoticImULDR_Jchar2 (i j : I32) :
    ((partner j = 11 ∧ partner i = 2) ∨ (partner j = 13 ∧ partner i = 4) ∨ (partner j = 15 ∧ partner i = 6) ∨ (partner j = 18 ∧ partner i = 27) ∨ (partner j = 20 ∧ partner i = 29) ∨ (partner j = 22 ∧ partner i = 31)) ↔
    ((i = 11 ∧ j = 2) ∨ (i = 13 ∧ j = 4) ∨ (i = 15 ∧ j = 6) ∨ (i = 18 ∧ j = 27) ∨ (i = 20 ∧ j = 29) ∨ (i = 22 ∧ j = 31)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩)
    · have hj : j = (27:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (11:I32) = (27:I32) from by decide] at h1'
      have hi : i = (18:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (2:I32) = (18:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    · have hj : j = (29:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (13:I32) = (29:I32) from by decide] at h1'
      have hi : i = (20:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (4:I32) = (20:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    · have hj : j = (31:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (15:I32) = (31:I32) from by decide] at h1'
      have hi : i = (22:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (6:I32) = (22:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, rfl⟩)))))
    · have hj : j = (2:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (18:I32) = (2:I32) from by decide] at h1'
      have hi : i = (11:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (27:I32) = (11:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inl ⟨rfl, rfl⟩
    · have hj : j = (4:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (20:I32) = (4:I32) from by decide] at h1'
      have hi : i = (13:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (29:I32) = (13:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · have hj : j = (6:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (22:I32) = (6:I32) from by decide] at h1'
      have hi : i = (15:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (31:I32) = (15:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> simp [partner]

theorem exoticImULDR_gsign (i j : I32)
    (h : ((i = 2 ∧ j = 11) ∨ (i = 4 ∧ j = 13) ∨ (i = 6 ∧ j = 15) ∨ (i = 27 ∧ j = 18) ∨ (i = 29 ∧ j = 20) ∨ (i = 31 ∧ j = 22)) ∨ ((i = 11 ∧ j = 2) ∨ (i = 13 ∧ j = 4) ∨ (i = 15 ∧ j = 6) ∨ (i = 18 ∧ j = 27) ∨ (i = 20 ∧ j = 29) ∨ (i = 22 ∧ j = 31))) :
    gammaF i i + gammaF j j = 0 := by
  rcases h with (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩)|(⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩)
  · have g1 : gammaF (2:I32) (2:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (11:I32) (11:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (4:I32) (4:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (13:I32) (13:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (6:I32) (6:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (15:I32) (15:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (27:I32) (27:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (18:I32) (18:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (29:I32) (29:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (20:I32) (20:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (31:I32) (31:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (22:I32) (22:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (11:I32) (11:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (2:I32) (2:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (13:I32) (13:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (4:I32) (4:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (15:I32) (15:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (6:I32) (6:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (18:I32) (18:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (27:I32) (27:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (20:I32) (20:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (29:I32) (29:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (22:I32) (22:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (31:I32) (31:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num

theorem exoticImULDR_cfInd (i j : I32)
    (h : ((i = 2 ∧ j = 11) ∨ (i = 4 ∧ j = 13) ∨ (i = 6 ∧ j = 15) ∨ (i = 27 ∧ j = 18) ∨ (i = 29 ∧ j = 20) ∨ (i = 31 ∧ j = 22)) ∨ ((i = 11 ∧ j = 2) ∨ (i = 13 ∧ j = 4) ∨ (i = 15 ∧ j = 6) ∨ (i = 18 ∧ j = 27) ∨ (i = 20 ∧ j = 29) ∨ (i = 22 ∧ j = 31))) :
    cfIndicator i = cfIndicator j := by
  rcases h with (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩)|(⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩)
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp

theorem exoticImULDR_selfAdjoint : exoticImULDR.conjTranspose = exoticImULDR := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  unfold exoticImULDR
  simp only [exoticImULDR_swap1 i j, exoticImULDR_swap2 i j]
  by_cases h1 : (i = 2 ∧ j = 11) ∨ (i = 4 ∧ j = 13) ∨ (i = 6 ∧ j = 15) ∨ (i = 27 ∧ j = 18) ∨ (i = 29 ∧ j = 20) ∨ (i = 31 ∧ j = 22)
  · by_cases h2 : (i = 11 ∧ j = 2) ∨ (i = 13 ∧ j = 4) ∨ (i = 15 ∧ j = 6) ∨ (i = 18 ∧ j = 27) ∨ (i = 20 ∧ j = 29) ∨ (i = 22 ∧ j = 31)
    · exact absurd h2 (exoticImULDR_disjoint i j h1)
    · simp [h1, h2]
  · by_cases h2 : (i = 11 ∧ j = 2) ∨ (i = 13 ∧ j = 4) ∨ (i = 15 ∧ j = 6) ∨ (i = 18 ∧ j = 27) ∨ (i = 20 ∧ j = 29) ∨ (i = 22 ∧ j = 31)
    · simp [h1, h2]
    · simp [h1, h2]

theorem exoticImULDR_gradingOdd : gammaF * exoticImULDR + exoticImULDR * gammaF = 0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply, gammaF_mul_apply, mul_gammaF_apply]
  by_cases h1 : (i = 2 ∧ j = 11) ∨ (i = 4 ∧ j = 13) ∨ (i = 6 ∧ j = 15) ∨ (i = 27 ∧ j = 18) ∨ (i = 29 ∧ j = 20) ∨ (i = 31 ∧ j = 22)
  · have hD : exoticImULDR i j = Complex.I := by unfold exoticImULDR; simp [h1]
    have hsign : gammaF i i + gammaF j j = 0 := exoticImULDR_gsign i j (Or.inl h1)
    rw [hD]
    have hrw : gammaF i i * Complex.I + Complex.I * gammaF j j
        = (gammaF i i + gammaF j j) * Complex.I := by ring
    rw [hrw, hsign, zero_mul]
  · by_cases h2 : (i = 11 ∧ j = 2) ∨ (i = 13 ∧ j = 4) ∨ (i = 15 ∧ j = 6) ∨ (i = 18 ∧ j = 27) ∨ (i = 20 ∧ j = 29) ∨ (i = 22 ∧ j = 31)
    · have hD : exoticImULDR i j = -Complex.I := by unfold exoticImULDR; simp [h1, h2]
      have hsign : gammaF i i + gammaF j j = 0 := exoticImULDR_gsign i j (Or.inr h2)
      rw [hD]
      have hrw : gammaF i i * -Complex.I + -Complex.I * gammaF j j
          = (gammaF i i + gammaF j j) * -Complex.I := by ring
      rw [hrw, hsign, zero_mul]
    · have hD : exoticImULDR i j = 0 := by unfold exoticImULDR; simp [h1, h2]
      rw [hD]; simp

theorem exoticImULDR_Jcompat : IsJCompatible exoticImULDR := by
  show UJ * exoticImULDR.transpose * UJ = exoticImULDR
  ext i j
  rw [UJ_conj_apply, Matrix.transpose_apply]
  unfold exoticImULDR
  simp only [exoticImULDR_Jchar1 i j, exoticImULDR_Jchar2 i j]

theorem exoticImULDR_cfMat : exoticImULDR * cfMat - cfMat * exoticImULDR = 0 := by
  ext i j
  rw [Matrix.sub_apply, Matrix.zero_apply, mul_cfMat_apply, cfMat_mul_apply]
  by_cases h1 : (i = 2 ∧ j = 11) ∨ (i = 4 ∧ j = 13) ∨ (i = 6 ∧ j = 15) ∨ (i = 27 ∧ j = 18) ∨ (i = 29 ∧ j = 20) ∨ (i = 31 ∧ j = 22)
  · have hD : exoticImULDR i j = Complex.I := by unfold exoticImULDR; simp [h1]
    have hcf : cfIndicator i = cfIndicator j := exoticImULDR_cfInd i j (Or.inl h1)
    rw [hD, hcf]; ring
  · by_cases h2 : (i = 11 ∧ j = 2) ∨ (i = 13 ∧ j = 4) ∨ (i = 15 ∧ j = 6) ∨ (i = 18 ∧ j = 27) ∨ (i = 20 ∧ j = 29) ∨ (i = 22 ∧ j = 31)
    · have hD : exoticImULDR i j = -Complex.I := by unfold exoticImULDR; simp [h1, h2]
      have hcf : cfIndicator i = cfIndicator j := exoticImULDR_cfInd i j (Or.inr h2)
      rw [hD, hcf]; ring
    · have hD : exoticImULDR i j = 0 := by unfold exoticImULDR; simp [h1, h2]
      rw [hD]; ring

/-! ### DLUR (Re) -/

theorem exoticReDLUR_symm (i j : I32)
    (h : (i = 3 ∧ j = 10) ∨ (i = 10 ∧ j = 3) ∨ (i = 5 ∧ j = 12) ∨ (i = 12 ∧ j = 5) ∨ (i = 7 ∧ j = 14) ∨ (i = 14 ∧ j = 7) ∨ (i = 19 ∧ j = 26) ∨ (i = 26 ∧ j = 19) ∨ (i = 21 ∧ j = 28) ∨ (i = 28 ∧ j = 21) ∨ (i = 23 ∧ j = 30) ∨ (i = 30 ∧ j = 23)) :
    (j = 3 ∧ i = 10) ∨ (j = 10 ∧ i = 3) ∨ (j = 5 ∧ i = 12) ∨ (j = 12 ∧ i = 5) ∨ (j = 7 ∧ i = 14) ∨ (j = 14 ∧ i = 7) ∨ (j = 19 ∧ i = 26) ∨ (j = 26 ∧ i = 19) ∨ (j = 21 ∧ i = 28) ∨ (j = 28 ∧ i = 21) ∨ (j = 23 ∧ i = 30) ∨ (j = 30 ∧ i = 23) := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, rfl⟩)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))))))

theorem exoticReDLUR_Jchar (i j : I32) :
    ((partner j = 3 ∧ partner i = 10) ∨ (partner j = 10 ∧ partner i = 3) ∨ (partner j = 5 ∧ partner i = 12) ∨ (partner j = 12 ∧ partner i = 5) ∨ (partner j = 7 ∧ partner i = 14) ∨ (partner j = 14 ∧ partner i = 7) ∨ (partner j = 19 ∧ partner i = 26) ∨ (partner j = 26 ∧ partner i = 19) ∨ (partner j = 21 ∧ partner i = 28) ∨ (partner j = 28 ∧ partner i = 21) ∨ (partner j = 23 ∧ partner i = 30) ∨ (partner j = 30 ∧ partner i = 23)) ↔
    ((i = 3 ∧ j = 10) ∨ (i = 10 ∧ j = 3) ∨ (i = 5 ∧ j = 12) ∨ (i = 12 ∧ j = 5) ∨ (i = 7 ∧ j = 14) ∨ (i = 14 ∧ j = 7) ∨ (i = 19 ∧ j = 26) ∨ (i = 26 ∧ j = 19) ∨ (i = 21 ∧ j = 28) ∨ (i = 28 ∧ j = 21) ∨ (i = 23 ∧ j = 30) ∨ (i = 30 ∧ j = 23)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩)
    · have hj : j = (19:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (3:I32) = (19:I32) from by decide] at h1'
      have hi : i = (26:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (10:I32) = (26:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))))
    · have hj : j = (26:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (10:I32) = (26:I32) from by decide] at h1'
      have hi : i = (19:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (3:I32) = (19:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))
    · have hj : j = (21:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (5:I32) = (21:I32) from by decide] at h1'
      have hi : i = (28:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (12:I32) = (28:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))))))
    · have hj : j = (28:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (12:I32) = (28:I32) from by decide] at h1'
      have hi : i = (21:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (5:I32) = (21:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))))
    · have hj : j = (23:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (7:I32) = (23:I32) from by decide] at h1'
      have hi : i = (30:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (14:I32) = (30:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, rfl⟩)))))))))))
    · have hj : j = (30:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (14:I32) = (30:I32) from by decide] at h1'
      have hi : i = (23:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (7:I32) = (23:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))))))
    · have hj : j = (3:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (19:I32) = (3:I32) from by decide] at h1'
      have hi : i = (10:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (26:I32) = (10:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · have hj : j = (10:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (26:I32) = (10:I32) from by decide] at h1'
      have hi : i = (3:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (19:I32) = (3:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inl ⟨rfl, rfl⟩
    · have hj : j = (5:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (21:I32) = (5:I32) from by decide] at h1'
      have hi : i = (12:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (28:I32) = (12:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    · have hj : j = (12:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (28:I32) = (12:I32) from by decide] at h1'
      have hi : i = (5:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (21:I32) = (5:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · have hj : j = (7:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (23:I32) = (7:I32) from by decide] at h1'
      have hi : i = (14:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (30:I32) = (14:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
    · have hj : j = (14:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (30:I32) = (14:I32) from by decide] at h1'
      have hi : i = (7:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (23:I32) = (7:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> simp [partner]

theorem exoticReDLUR_gsign (i j : I32)
    (h : (i = 3 ∧ j = 10) ∨ (i = 10 ∧ j = 3) ∨ (i = 5 ∧ j = 12) ∨ (i = 12 ∧ j = 5) ∨ (i = 7 ∧ j = 14) ∨ (i = 14 ∧ j = 7) ∨ (i = 19 ∧ j = 26) ∨ (i = 26 ∧ j = 19) ∨ (i = 21 ∧ j = 28) ∨ (i = 28 ∧ j = 21) ∨ (i = 23 ∧ j = 30) ∨ (i = 30 ∧ j = 23)) :
    gammaF i i + gammaF j j = 0 := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · have g1 : gammaF (3:I32) (3:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (10:I32) (10:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (10:I32) (10:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (3:I32) (3:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (5:I32) (5:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (12:I32) (12:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (12:I32) (12:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (5:I32) (5:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (7:I32) (7:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (14:I32) (14:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (14:I32) (14:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (7:I32) (7:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (19:I32) (19:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (26:I32) (26:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (26:I32) (26:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (19:I32) (19:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (21:I32) (21:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (28:I32) (28:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (28:I32) (28:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (21:I32) (21:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (23:I32) (23:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (30:I32) (30:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (30:I32) (30:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (23:I32) (23:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num

theorem exoticReDLUR_cfInd (i j : I32)
    (h : (i = 3 ∧ j = 10) ∨ (i = 10 ∧ j = 3) ∨ (i = 5 ∧ j = 12) ∨ (i = 12 ∧ j = 5) ∨ (i = 7 ∧ j = 14) ∨ (i = 14 ∧ j = 7) ∨ (i = 19 ∧ j = 26) ∨ (i = 26 ∧ j = 19) ∨ (i = 21 ∧ j = 28) ∨ (i = 28 ∧ j = 21) ∨ (i = 23 ∧ j = 30) ∨ (i = 30 ∧ j = 23)) :
    cfIndicator i = cfIndicator j := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp

theorem exoticReDLUR_selfAdjoint : exoticReDLUR.conjTranspose = exoticReDLUR := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  unfold exoticReDLUR
  by_cases h : (i = 3 ∧ j = 10) ∨ (i = 10 ∧ j = 3) ∨ (i = 5 ∧ j = 12) ∨ (i = 12 ∧ j = 5) ∨ (i = 7 ∧ j = 14) ∨ (i = 14 ∧ j = 7) ∨ (i = 19 ∧ j = 26) ∨ (i = 26 ∧ j = 19) ∨ (i = 21 ∧ j = 28) ∨ (i = 28 ∧ j = 21) ∨ (i = 23 ∧ j = 30) ∨ (i = 30 ∧ j = 23)
  · have h1 := exoticReDLUR_symm i j h
    simp [h, h1]
  · have h1 : ¬((j = 3 ∧ i = 10) ∨ (j = 10 ∧ i = 3) ∨ (j = 5 ∧ i = 12) ∨ (j = 12 ∧ i = 5) ∨ (j = 7 ∧ i = 14) ∨ (j = 14 ∧ i = 7) ∨ (j = 19 ∧ i = 26) ∨ (j = 26 ∧ i = 19) ∨ (j = 21 ∧ i = 28) ∨ (j = 28 ∧ i = 21) ∨ (j = 23 ∧ i = 30) ∨ (j = 30 ∧ i = 23)) :=
      fun h3 => h (exoticReDLUR_symm j i h3)
    simp [h, h1]

theorem exoticReDLUR_gradingOdd : gammaF * exoticReDLUR + exoticReDLUR * gammaF = 0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply, gammaF_mul_apply, mul_gammaF_apply]
  by_cases h : (i = 3 ∧ j = 10) ∨ (i = 10 ∧ j = 3) ∨ (i = 5 ∧ j = 12) ∨ (i = 12 ∧ j = 5) ∨ (i = 7 ∧ j = 14) ∨ (i = 14 ∧ j = 7) ∨ (i = 19 ∧ j = 26) ∨ (i = 26 ∧ j = 19) ∨ (i = 21 ∧ j = 28) ∨ (i = 28 ∧ j = 21) ∨ (i = 23 ∧ j = 30) ∨ (i = 30 ∧ j = 23)
  · have hD : exoticReDLUR i j = 1 := by unfold exoticReDLUR; simp [h]
    have hsign : gammaF i i + gammaF j j = 0 := exoticReDLUR_gsign i j h
    rw [hD]
    linear_combination hsign
  · have hD : exoticReDLUR i j = 0 := by unfold exoticReDLUR; simp [h]
    rw [hD]; simp

theorem exoticReDLUR_Jcompat : IsJCompatible exoticReDLUR := by
  show UJ * exoticReDLUR.transpose * UJ = exoticReDLUR
  ext i j
  rw [UJ_conj_apply, Matrix.transpose_apply]
  unfold exoticReDLUR
  simp only [exoticReDLUR_Jchar i j]

theorem exoticReDLUR_cfMat : exoticReDLUR * cfMat - cfMat * exoticReDLUR = 0 := by
  ext i j
  rw [Matrix.sub_apply, Matrix.zero_apply, mul_cfMat_apply, cfMat_mul_apply]
  by_cases h : (i = 3 ∧ j = 10) ∨ (i = 10 ∧ j = 3) ∨ (i = 5 ∧ j = 12) ∨ (i = 12 ∧ j = 5) ∨ (i = 7 ∧ j = 14) ∨ (i = 14 ∧ j = 7) ∨ (i = 19 ∧ j = 26) ∨ (i = 26 ∧ j = 19) ∨ (i = 21 ∧ j = 28) ∨ (i = 28 ∧ j = 21) ∨ (i = 23 ∧ j = 30) ∨ (i = 30 ∧ j = 23)
  · have hD : exoticReDLUR i j = 1 := by unfold exoticReDLUR; simp [h]
    have hcf : cfIndicator i = cfIndicator j := exoticReDLUR_cfInd i j h
    rw [hD, hcf]; ring
  · have hD : exoticReDLUR i j = 0 := by unfold exoticReDLUR; simp [h]
    rw [hD]; ring

/-! ### DLUR (Im) -/

theorem exoticImDLUR_swap1 (i j : I32) :
    ((j = 3 ∧ i = 10) ∨ (j = 5 ∧ i = 12) ∨ (j = 7 ∧ i = 14) ∨ (j = 26 ∧ i = 19) ∨ (j = 28 ∧ i = 21) ∨ (j = 30 ∧ i = 23)) ↔ ((i = 10 ∧ j = 3) ∨ (i = 12 ∧ j = 5) ∨ (i = 14 ∧ j = 7) ∨ (i = 19 ∧ j = 26) ∨ (i = 21 ∧ j = 28) ∨ (i = 23 ∧ j = 30)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h2, h1⟩)))))
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h2, h1⟩)))))

theorem exoticImDLUR_swap2 (i j : I32) :
    ((j = 10 ∧ i = 3) ∨ (j = 12 ∧ i = 5) ∨ (j = 14 ∧ i = 7) ∨ (j = 19 ∧ i = 26) ∨ (j = 21 ∧ i = 28) ∨ (j = 23 ∧ i = 30)) ↔ ((i = 3 ∧ j = 10) ∨ (i = 5 ∧ j = 12) ∨ (i = 7 ∧ j = 14) ∨ (i = 26 ∧ j = 19) ∨ (i = 28 ∧ j = 21) ∨ (i = 30 ∧ j = 23)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h2, h1⟩)))))
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h2, h1⟩)))))

theorem exoticImDLUR_disjoint (i j : I32)
    (h : (i = 3 ∧ j = 10) ∨ (i = 5 ∧ j = 12) ∨ (i = 7 ∧ j = 14) ∨ (i = 26 ∧ j = 19) ∨ (i = 28 ∧ j = 21) ∨ (i = 30 ∧ j = 23)) : ¬ ((i = 10 ∧ j = 3) ∨ (i = 12 ∧ j = 5) ∨ (i = 14 ∧ j = 7) ∨ (i = 19 ∧ j = 26) ∨ (i = 21 ∧ j = 28) ∨ (i = 23 ∧ j = 30)) := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · intro hcon
    rcases hcon with ⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩
    · exact (by decide : (3:I32) ≠ 10) h1
    · exact (by decide : (3:I32) ≠ 12) h1
    · exact (by decide : (3:I32) ≠ 14) h1
    · exact (by decide : (3:I32) ≠ 19) h1
    · exact (by decide : (3:I32) ≠ 21) h1
    · exact (by decide : (3:I32) ≠ 23) h1
  · intro hcon
    rcases hcon with ⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩
    · exact (by decide : (5:I32) ≠ 10) h1
    · exact (by decide : (5:I32) ≠ 12) h1
    · exact (by decide : (5:I32) ≠ 14) h1
    · exact (by decide : (5:I32) ≠ 19) h1
    · exact (by decide : (5:I32) ≠ 21) h1
    · exact (by decide : (5:I32) ≠ 23) h1
  · intro hcon
    rcases hcon with ⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩
    · exact (by decide : (7:I32) ≠ 10) h1
    · exact (by decide : (7:I32) ≠ 12) h1
    · exact (by decide : (7:I32) ≠ 14) h1
    · exact (by decide : (7:I32) ≠ 19) h1
    · exact (by decide : (7:I32) ≠ 21) h1
    · exact (by decide : (7:I32) ≠ 23) h1
  · intro hcon
    rcases hcon with ⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩
    · exact (by decide : (26:I32) ≠ 10) h1
    · exact (by decide : (26:I32) ≠ 12) h1
    · exact (by decide : (26:I32) ≠ 14) h1
    · exact (by decide : (26:I32) ≠ 19) h1
    · exact (by decide : (26:I32) ≠ 21) h1
    · exact (by decide : (26:I32) ≠ 23) h1
  · intro hcon
    rcases hcon with ⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩
    · exact (by decide : (28:I32) ≠ 10) h1
    · exact (by decide : (28:I32) ≠ 12) h1
    · exact (by decide : (28:I32) ≠ 14) h1
    · exact (by decide : (28:I32) ≠ 19) h1
    · exact (by decide : (28:I32) ≠ 21) h1
    · exact (by decide : (28:I32) ≠ 23) h1
  · intro hcon
    rcases hcon with ⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩
    · exact (by decide : (30:I32) ≠ 10) h1
    · exact (by decide : (30:I32) ≠ 12) h1
    · exact (by decide : (30:I32) ≠ 14) h1
    · exact (by decide : (30:I32) ≠ 19) h1
    · exact (by decide : (30:I32) ≠ 21) h1
    · exact (by decide : (30:I32) ≠ 23) h1

theorem exoticImDLUR_Jchar1 (i j : I32) :
    ((partner j = 3 ∧ partner i = 10) ∨ (partner j = 5 ∧ partner i = 12) ∨ (partner j = 7 ∧ partner i = 14) ∨ (partner j = 26 ∧ partner i = 19) ∨ (partner j = 28 ∧ partner i = 21) ∨ (partner j = 30 ∧ partner i = 23)) ↔
    ((i = 3 ∧ j = 10) ∨ (i = 5 ∧ j = 12) ∨ (i = 7 ∧ j = 14) ∨ (i = 26 ∧ j = 19) ∨ (i = 28 ∧ j = 21) ∨ (i = 30 ∧ j = 23)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩)
    · have hj : j = (19:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (3:I32) = (19:I32) from by decide] at h1'
      have hi : i = (26:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (10:I32) = (26:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    · have hj : j = (21:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (5:I32) = (21:I32) from by decide] at h1'
      have hi : i = (28:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (12:I32) = (28:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    · have hj : j = (23:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (7:I32) = (23:I32) from by decide] at h1'
      have hi : i = (30:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (14:I32) = (30:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, rfl⟩)))))
    · have hj : j = (10:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (26:I32) = (10:I32) from by decide] at h1'
      have hi : i = (3:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (19:I32) = (3:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inl ⟨rfl, rfl⟩
    · have hj : j = (12:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (28:I32) = (12:I32) from by decide] at h1'
      have hi : i = (5:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (21:I32) = (5:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · have hj : j = (14:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (30:I32) = (14:I32) from by decide] at h1'
      have hi : i = (7:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (23:I32) = (7:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> simp [partner]

theorem exoticImDLUR_Jchar2 (i j : I32) :
    ((partner j = 10 ∧ partner i = 3) ∨ (partner j = 12 ∧ partner i = 5) ∨ (partner j = 14 ∧ partner i = 7) ∨ (partner j = 19 ∧ partner i = 26) ∨ (partner j = 21 ∧ partner i = 28) ∨ (partner j = 23 ∧ partner i = 30)) ↔
    ((i = 10 ∧ j = 3) ∨ (i = 12 ∧ j = 5) ∨ (i = 14 ∧ j = 7) ∨ (i = 19 ∧ j = 26) ∨ (i = 21 ∧ j = 28) ∨ (i = 23 ∧ j = 30)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩)
    · have hj : j = (26:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (10:I32) = (26:I32) from by decide] at h1'
      have hi : i = (19:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (3:I32) = (19:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    · have hj : j = (28:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (12:I32) = (28:I32) from by decide] at h1'
      have hi : i = (21:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (5:I32) = (21:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    · have hj : j = (30:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (14:I32) = (30:I32) from by decide] at h1'
      have hi : i = (23:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (7:I32) = (23:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, rfl⟩)))))
    · have hj : j = (3:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (19:I32) = (3:I32) from by decide] at h1'
      have hi : i = (10:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (26:I32) = (10:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inl ⟨rfl, rfl⟩
    · have hj : j = (5:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (21:I32) = (5:I32) from by decide] at h1'
      have hi : i = (12:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (28:I32) = (12:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · have hj : j = (7:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (23:I32) = (7:I32) from by decide] at h1'
      have hi : i = (14:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (30:I32) = (14:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> simp [partner]

theorem exoticImDLUR_gsign (i j : I32)
    (h : ((i = 3 ∧ j = 10) ∨ (i = 5 ∧ j = 12) ∨ (i = 7 ∧ j = 14) ∨ (i = 26 ∧ j = 19) ∨ (i = 28 ∧ j = 21) ∨ (i = 30 ∧ j = 23)) ∨ ((i = 10 ∧ j = 3) ∨ (i = 12 ∧ j = 5) ∨ (i = 14 ∧ j = 7) ∨ (i = 19 ∧ j = 26) ∨ (i = 21 ∧ j = 28) ∨ (i = 23 ∧ j = 30))) :
    gammaF i i + gammaF j j = 0 := by
  rcases h with (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩)|(⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩)
  · have g1 : gammaF (3:I32) (3:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (10:I32) (10:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (5:I32) (5:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (12:I32) (12:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (7:I32) (7:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (14:I32) (14:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (26:I32) (26:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (19:I32) (19:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (28:I32) (28:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (21:I32) (21:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (30:I32) (30:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (23:I32) (23:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (10:I32) (10:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (3:I32) (3:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (12:I32) (12:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (5:I32) (5:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (14:I32) (14:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (7:I32) (7:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (19:I32) (19:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (26:I32) (26:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (21:I32) (21:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (28:I32) (28:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (23:I32) (23:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (30:I32) (30:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num

theorem exoticImDLUR_cfInd (i j : I32)
    (h : ((i = 3 ∧ j = 10) ∨ (i = 5 ∧ j = 12) ∨ (i = 7 ∧ j = 14) ∨ (i = 26 ∧ j = 19) ∨ (i = 28 ∧ j = 21) ∨ (i = 30 ∧ j = 23)) ∨ ((i = 10 ∧ j = 3) ∨ (i = 12 ∧ j = 5) ∨ (i = 14 ∧ j = 7) ∨ (i = 19 ∧ j = 26) ∨ (i = 21 ∧ j = 28) ∨ (i = 23 ∧ j = 30))) :
    cfIndicator i = cfIndicator j := by
  rcases h with (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩)|(⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩)
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp

theorem exoticImDLUR_selfAdjoint : exoticImDLUR.conjTranspose = exoticImDLUR := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  unfold exoticImDLUR
  simp only [exoticImDLUR_swap1 i j, exoticImDLUR_swap2 i j]
  by_cases h1 : (i = 3 ∧ j = 10) ∨ (i = 5 ∧ j = 12) ∨ (i = 7 ∧ j = 14) ∨ (i = 26 ∧ j = 19) ∨ (i = 28 ∧ j = 21) ∨ (i = 30 ∧ j = 23)
  · by_cases h2 : (i = 10 ∧ j = 3) ∨ (i = 12 ∧ j = 5) ∨ (i = 14 ∧ j = 7) ∨ (i = 19 ∧ j = 26) ∨ (i = 21 ∧ j = 28) ∨ (i = 23 ∧ j = 30)
    · exact absurd h2 (exoticImDLUR_disjoint i j h1)
    · simp [h1, h2]
  · by_cases h2 : (i = 10 ∧ j = 3) ∨ (i = 12 ∧ j = 5) ∨ (i = 14 ∧ j = 7) ∨ (i = 19 ∧ j = 26) ∨ (i = 21 ∧ j = 28) ∨ (i = 23 ∧ j = 30)
    · simp [h1, h2]
    · simp [h1, h2]

theorem exoticImDLUR_gradingOdd : gammaF * exoticImDLUR + exoticImDLUR * gammaF = 0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply, gammaF_mul_apply, mul_gammaF_apply]
  by_cases h1 : (i = 3 ∧ j = 10) ∨ (i = 5 ∧ j = 12) ∨ (i = 7 ∧ j = 14) ∨ (i = 26 ∧ j = 19) ∨ (i = 28 ∧ j = 21) ∨ (i = 30 ∧ j = 23)
  · have hD : exoticImDLUR i j = Complex.I := by unfold exoticImDLUR; simp [h1]
    have hsign : gammaF i i + gammaF j j = 0 := exoticImDLUR_gsign i j (Or.inl h1)
    rw [hD]
    have hrw : gammaF i i * Complex.I + Complex.I * gammaF j j
        = (gammaF i i + gammaF j j) * Complex.I := by ring
    rw [hrw, hsign, zero_mul]
  · by_cases h2 : (i = 10 ∧ j = 3) ∨ (i = 12 ∧ j = 5) ∨ (i = 14 ∧ j = 7) ∨ (i = 19 ∧ j = 26) ∨ (i = 21 ∧ j = 28) ∨ (i = 23 ∧ j = 30)
    · have hD : exoticImDLUR i j = -Complex.I := by unfold exoticImDLUR; simp [h1, h2]
      have hsign : gammaF i i + gammaF j j = 0 := exoticImDLUR_gsign i j (Or.inr h2)
      rw [hD]
      have hrw : gammaF i i * -Complex.I + -Complex.I * gammaF j j
          = (gammaF i i + gammaF j j) * -Complex.I := by ring
      rw [hrw, hsign, zero_mul]
    · have hD : exoticImDLUR i j = 0 := by unfold exoticImDLUR; simp [h1, h2]
      rw [hD]; simp

theorem exoticImDLUR_Jcompat : IsJCompatible exoticImDLUR := by
  show UJ * exoticImDLUR.transpose * UJ = exoticImDLUR
  ext i j
  rw [UJ_conj_apply, Matrix.transpose_apply]
  unfold exoticImDLUR
  simp only [exoticImDLUR_Jchar1 i j, exoticImDLUR_Jchar2 i j]

theorem exoticImDLUR_cfMat : exoticImDLUR * cfMat - cfMat * exoticImDLUR = 0 := by
  ext i j
  rw [Matrix.sub_apply, Matrix.zero_apply, mul_cfMat_apply, cfMat_mul_apply]
  by_cases h1 : (i = 3 ∧ j = 10) ∨ (i = 5 ∧ j = 12) ∨ (i = 7 ∧ j = 14) ∨ (i = 26 ∧ j = 19) ∨ (i = 28 ∧ j = 21) ∨ (i = 30 ∧ j = 23)
  · have hD : exoticImDLUR i j = Complex.I := by unfold exoticImDLUR; simp [h1]
    have hcf : cfIndicator i = cfIndicator j := exoticImDLUR_cfInd i j (Or.inl h1)
    rw [hD, hcf]; ring
  · by_cases h2 : (i = 10 ∧ j = 3) ∨ (i = 12 ∧ j = 5) ∨ (i = 14 ∧ j = 7) ∨ (i = 19 ∧ j = 26) ∨ (i = 21 ∧ j = 28) ∨ (i = 23 ∧ j = 30)
    · have hD : exoticImDLUR i j = -Complex.I := by unfold exoticImDLUR; simp [h1, h2]
      have hcf : cfIndicator i = cfIndicator j := exoticImDLUR_cfInd i j (Or.inr h2)
      rw [hD, hcf]; ring
    · have hD : exoticImDLUR i j = 0 := by unfold exoticImDLUR; simp [h1, h2]
      rw [hD]; ring

/-! ### NuREbarR (Re) -/

theorem exoticReNuREbarR_symm (i j : I32)
    (h : (i = 8 ∧ j = 25) ∨ (i = 25 ∧ j = 8) ∨ (i = 24 ∧ j = 9) ∨ (i = 9 ∧ j = 24)) :
    (j = 8 ∧ i = 25) ∨ (j = 25 ∧ i = 8) ∨ (j = 24 ∧ i = 9) ∨ (j = 9 ∧ i = 24) := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inr (Or.inr (⟨rfl, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem exoticReNuREbarR_Jchar (i j : I32) :
    ((partner j = 8 ∧ partner i = 25) ∨ (partner j = 25 ∧ partner i = 8) ∨ (partner j = 24 ∧ partner i = 9) ∨ (partner j = 9 ∧ partner i = 24)) ↔
    ((i = 8 ∧ j = 25) ∨ (i = 25 ∧ j = 8) ∨ (i = 24 ∧ j = 9) ∨ (i = 9 ∧ j = 24)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩)
    · have hj : j = (24:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (8:I32) = (24:I32) from by decide] at h1'
      have hi : i = (9:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (25:I32) = (9:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inr (⟨rfl, rfl⟩)))
    · have hj : j = (9:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (25:I32) = (9:I32) from by decide] at h1'
      have hi : i = (24:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (8:I32) = (24:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · have hj : j = (8:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (24:I32) = (8:I32) from by decide] at h1'
      have hi : i = (25:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (9:I32) = (25:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · have hj : j = (25:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (9:I32) = (25:I32) from by decide] at h1'
      have hi : i = (8:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (24:I32) = (8:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inl ⟨rfl, rfl⟩
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> simp [partner]

theorem exoticReNuREbarR_gsign (i j : I32)
    (h : (i = 8 ∧ j = 25) ∨ (i = 25 ∧ j = 8) ∨ (i = 24 ∧ j = 9) ∨ (i = 9 ∧ j = 24)) :
    gammaF i i + gammaF j j = 0 := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · have g1 : gammaF (8:I32) (8:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (25:I32) (25:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (25:I32) (25:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (8:I32) (8:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (24:I32) (24:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (9:I32) (9:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (9:I32) (9:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (24:I32) (24:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num

theorem exoticReNuREbarR_cfInd (i j : I32)
    (h : (i = 8 ∧ j = 25) ∨ (i = 25 ∧ j = 8) ∨ (i = 24 ∧ j = 9) ∨ (i = 9 ∧ j = 24)) :
    cfIndicator i = cfIndicator j := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp

theorem exoticReNuREbarR_selfAdjoint : exoticReNuREbarR.conjTranspose = exoticReNuREbarR := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  unfold exoticReNuREbarR
  by_cases h : (i = 8 ∧ j = 25) ∨ (i = 25 ∧ j = 8) ∨ (i = 24 ∧ j = 9) ∨ (i = 9 ∧ j = 24)
  · have h1 := exoticReNuREbarR_symm i j h
    simp [h, h1]
  · have h1 : ¬((j = 8 ∧ i = 25) ∨ (j = 25 ∧ i = 8) ∨ (j = 24 ∧ i = 9) ∨ (j = 9 ∧ i = 24)) :=
      fun h3 => h (exoticReNuREbarR_symm j i h3)
    simp [h, h1]

theorem exoticReNuREbarR_gradingOdd : gammaF * exoticReNuREbarR + exoticReNuREbarR * gammaF = 0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply, gammaF_mul_apply, mul_gammaF_apply]
  by_cases h : (i = 8 ∧ j = 25) ∨ (i = 25 ∧ j = 8) ∨ (i = 24 ∧ j = 9) ∨ (i = 9 ∧ j = 24)
  · have hD : exoticReNuREbarR i j = 1 := by unfold exoticReNuREbarR; simp [h]
    have hsign : gammaF i i + gammaF j j = 0 := exoticReNuREbarR_gsign i j h
    rw [hD]
    linear_combination hsign
  · have hD : exoticReNuREbarR i j = 0 := by unfold exoticReNuREbarR; simp [h]
    rw [hD]; simp

theorem exoticReNuREbarR_Jcompat : IsJCompatible exoticReNuREbarR := by
  show UJ * exoticReNuREbarR.transpose * UJ = exoticReNuREbarR
  ext i j
  rw [UJ_conj_apply, Matrix.transpose_apply]
  unfold exoticReNuREbarR
  simp only [exoticReNuREbarR_Jchar i j]

theorem exoticReNuREbarR_cfMat : exoticReNuREbarR * cfMat - cfMat * exoticReNuREbarR = 0 := by
  ext i j
  rw [Matrix.sub_apply, Matrix.zero_apply, mul_cfMat_apply, cfMat_mul_apply]
  by_cases h : (i = 8 ∧ j = 25) ∨ (i = 25 ∧ j = 8) ∨ (i = 24 ∧ j = 9) ∨ (i = 9 ∧ j = 24)
  · have hD : exoticReNuREbarR i j = 1 := by unfold exoticReNuREbarR; simp [h]
    have hcf : cfIndicator i = cfIndicator j := exoticReNuREbarR_cfInd i j h
    rw [hD, hcf]; ring
  · have hD : exoticReNuREbarR i j = 0 := by unfold exoticReNuREbarR; simp [h]
    rw [hD]; ring

/-! ### NuREbarR (Im) -/

theorem exoticImNuREbarR_swap1 (i j : I32) :
    ((j = 8 ∧ i = 25) ∨ (j = 9 ∧ i = 24)) ↔ ((i = 25 ∧ j = 8) ∨ (i = 24 ∧ j = 9)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (⟨h2, h1⟩)
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (⟨h2, h1⟩)

theorem exoticImNuREbarR_swap2 (i j : I32) :
    ((j = 25 ∧ i = 8) ∨ (j = 24 ∧ i = 9)) ↔ ((i = 8 ∧ j = 25) ∨ (i = 9 ∧ j = 24)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (⟨h2, h1⟩)
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (⟨h2, h1⟩)

theorem exoticImNuREbarR_disjoint (i j : I32)
    (h : (i = 8 ∧ j = 25) ∨ (i = 9 ∧ j = 24)) : ¬ ((i = 25 ∧ j = 8) ∨ (i = 24 ∧ j = 9)) := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · intro hcon
    rcases hcon with ⟨h1,_⟩|⟨h1,_⟩
    · exact (by decide : (8:I32) ≠ 25) h1
    · exact (by decide : (8:I32) ≠ 24) h1
  · intro hcon
    rcases hcon with ⟨h1,_⟩|⟨h1,_⟩
    · exact (by decide : (9:I32) ≠ 25) h1
    · exact (by decide : (9:I32) ≠ 24) h1

theorem exoticImNuREbarR_Jchar1 (i j : I32) :
    ((partner j = 8 ∧ partner i = 25) ∨ (partner j = 9 ∧ partner i = 24)) ↔
    ((i = 8 ∧ j = 25) ∨ (i = 9 ∧ j = 24)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
    · have hj : j = (24:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (8:I32) = (24:I32) from by decide] at h1'
      have hi : i = (9:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (25:I32) = (9:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (⟨rfl, rfl⟩)
    · have hj : j = (25:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (9:I32) = (25:I32) from by decide] at h1'
      have hi : i = (8:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (24:I32) = (8:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inl ⟨rfl, rfl⟩
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> simp [partner]

theorem exoticImNuREbarR_Jchar2 (i j : I32) :
    ((partner j = 25 ∧ partner i = 8) ∨ (partner j = 24 ∧ partner i = 9)) ↔
    ((i = 25 ∧ j = 8) ∨ (i = 24 ∧ j = 9)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
    · have hj : j = (9:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (25:I32) = (9:I32) from by decide] at h1'
      have hi : i = (24:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (8:I32) = (24:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (⟨rfl, rfl⟩)
    · have hj : j = (8:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (24:I32) = (8:I32) from by decide] at h1'
      have hi : i = (25:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (9:I32) = (25:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inl ⟨rfl, rfl⟩
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> simp [partner]

theorem exoticImNuREbarR_gsign (i j : I32)
    (h : ((i = 8 ∧ j = 25) ∨ (i = 9 ∧ j = 24)) ∨ ((i = 25 ∧ j = 8) ∨ (i = 24 ∧ j = 9))) :
    gammaF i i + gammaF j j = 0 := by
  rcases h with (⟨rfl,rfl⟩|⟨rfl,rfl⟩)|(⟨rfl,rfl⟩|⟨rfl,rfl⟩)
  · have g1 : gammaF (8:I32) (8:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (25:I32) (25:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (9:I32) (9:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (24:I32) (24:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (25:I32) (25:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (8:I32) (8:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (24:I32) (24:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (9:I32) (9:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num

theorem exoticImNuREbarR_cfInd (i j : I32)
    (h : ((i = 8 ∧ j = 25) ∨ (i = 9 ∧ j = 24)) ∨ ((i = 25 ∧ j = 8) ∨ (i = 24 ∧ j = 9))) :
    cfIndicator i = cfIndicator j := by
  rcases h with (⟨rfl,rfl⟩|⟨rfl,rfl⟩)|(⟨rfl,rfl⟩|⟨rfl,rfl⟩)
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp

theorem exoticImNuREbarR_selfAdjoint : exoticImNuREbarR.conjTranspose = exoticImNuREbarR := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  unfold exoticImNuREbarR
  simp only [exoticImNuREbarR_swap1 i j, exoticImNuREbarR_swap2 i j]
  by_cases h1 : (i = 8 ∧ j = 25) ∨ (i = 9 ∧ j = 24)
  · by_cases h2 : (i = 25 ∧ j = 8) ∨ (i = 24 ∧ j = 9)
    · exact absurd h2 (exoticImNuREbarR_disjoint i j h1)
    · simp [h1, h2]
  · by_cases h2 : (i = 25 ∧ j = 8) ∨ (i = 24 ∧ j = 9)
    · simp [h1, h2]
    · simp [h1, h2]

theorem exoticImNuREbarR_gradingOdd : gammaF * exoticImNuREbarR + exoticImNuREbarR * gammaF = 0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply, gammaF_mul_apply, mul_gammaF_apply]
  by_cases h1 : (i = 8 ∧ j = 25) ∨ (i = 9 ∧ j = 24)
  · have hD : exoticImNuREbarR i j = Complex.I := by unfold exoticImNuREbarR; simp [h1]
    have hsign : gammaF i i + gammaF j j = 0 := exoticImNuREbarR_gsign i j (Or.inl h1)
    rw [hD]
    have hrw : gammaF i i * Complex.I + Complex.I * gammaF j j
        = (gammaF i i + gammaF j j) * Complex.I := by ring
    rw [hrw, hsign, zero_mul]
  · by_cases h2 : (i = 25 ∧ j = 8) ∨ (i = 24 ∧ j = 9)
    · have hD : exoticImNuREbarR i j = -Complex.I := by unfold exoticImNuREbarR; simp [h1, h2]
      have hsign : gammaF i i + gammaF j j = 0 := exoticImNuREbarR_gsign i j (Or.inr h2)
      rw [hD]
      have hrw : gammaF i i * -Complex.I + -Complex.I * gammaF j j
          = (gammaF i i + gammaF j j) * -Complex.I := by ring
      rw [hrw, hsign, zero_mul]
    · have hD : exoticImNuREbarR i j = 0 := by unfold exoticImNuREbarR; simp [h1, h2]
      rw [hD]; simp

theorem exoticImNuREbarR_Jcompat : IsJCompatible exoticImNuREbarR := by
  show UJ * exoticImNuREbarR.transpose * UJ = exoticImNuREbarR
  ext i j
  rw [UJ_conj_apply, Matrix.transpose_apply]
  unfold exoticImNuREbarR
  simp only [exoticImNuREbarR_Jchar1 i j, exoticImNuREbarR_Jchar2 i j]

theorem exoticImNuREbarR_cfMat : exoticImNuREbarR * cfMat - cfMat * exoticImNuREbarR = 0 := by
  ext i j
  rw [Matrix.sub_apply, Matrix.zero_apply, mul_cfMat_apply, cfMat_mul_apply]
  by_cases h1 : (i = 8 ∧ j = 25) ∨ (i = 9 ∧ j = 24)
  · have hD : exoticImNuREbarR i j = Complex.I := by unfold exoticImNuREbarR; simp [h1]
    have hcf : cfIndicator i = cfIndicator j := exoticImNuREbarR_cfInd i j (Or.inl h1)
    rw [hD, hcf]; ring
  · by_cases h2 : (i = 25 ∧ j = 8) ∨ (i = 24 ∧ j = 9)
    · have hD : exoticImNuREbarR i j = -Complex.I := by unfold exoticImNuREbarR; simp [h1, h2]
      have hcf : cfIndicator i = cfIndicator j := exoticImNuREbarR_cfInd i j (Or.inr h2)
      rw [hD, hcf]; ring
    · have hD : exoticImNuREbarR i j = 0 := by unfold exoticImNuREbarR; simp [h1, h2]
      rw [hD]; ring

/-! ### EREbarR (Re) -/

theorem exoticReEREbarR_symm (i j : I32)
    (h : (i = 9 ∧ j = 25) ∨ (i = 25 ∧ j = 9)) :
    (j = 9 ∧ i = 25) ∨ (j = 25 ∧ i = 9) := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact Or.inr (⟨rfl, rfl⟩)
  · exact Or.inl ⟨rfl, rfl⟩

theorem exoticReEREbarR_Jchar (i j : I32) :
    ((partner j = 9 ∧ partner i = 25) ∨ (partner j = 25 ∧ partner i = 9)) ↔
    ((i = 9 ∧ j = 25) ∨ (i = 25 ∧ j = 9)) := by
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
    · have hj : j = (25:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (9:I32) = (25:I32) from by decide] at h1'
      have hi : i = (9:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (25:I32) = (9:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inl ⟨rfl, rfl⟩
    · have hj : j = (9:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (25:I32) = (9:I32) from by decide] at h1'
      have hi : i = (25:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (9:I32) = (25:I32) from by decide] at h2'
      rw [hi, hj]
      exact Or.inr (⟨rfl, rfl⟩)
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> simp [partner]

theorem exoticReEREbarR_gsign (i j : I32)
    (h : (i = 9 ∧ j = 25) ∨ (i = 25 ∧ j = 9)) :
    gammaF i i + gammaF j j = 0 := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · have g1 : gammaF (9:I32) (9:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (25:I32) (25:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (25:I32) (25:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (9:I32) (9:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num

theorem exoticReEREbarR_cfInd (i j : I32)
    (h : (i = 9 ∧ j = 25) ∨ (i = 25 ∧ j = 9)) :
    cfIndicator i = cfIndicator j := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp

theorem exoticReEREbarR_selfAdjoint : exoticReEREbarR.conjTranspose = exoticReEREbarR := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  unfold exoticReEREbarR
  by_cases h : (i = 9 ∧ j = 25) ∨ (i = 25 ∧ j = 9)
  · have h1 := exoticReEREbarR_symm i j h
    simp [h, h1]
  · have h1 : ¬((j = 9 ∧ i = 25) ∨ (j = 25 ∧ i = 9)) :=
      fun h3 => h (exoticReEREbarR_symm j i h3)
    simp [h, h1]

theorem exoticReEREbarR_gradingOdd : gammaF * exoticReEREbarR + exoticReEREbarR * gammaF = 0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply, gammaF_mul_apply, mul_gammaF_apply]
  by_cases h : (i = 9 ∧ j = 25) ∨ (i = 25 ∧ j = 9)
  · have hD : exoticReEREbarR i j = 1 := by unfold exoticReEREbarR; simp [h]
    have hsign : gammaF i i + gammaF j j = 0 := exoticReEREbarR_gsign i j h
    rw [hD]
    linear_combination hsign
  · have hD : exoticReEREbarR i j = 0 := by unfold exoticReEREbarR; simp [h]
    rw [hD]; simp

theorem exoticReEREbarR_Jcompat : IsJCompatible exoticReEREbarR := by
  show UJ * exoticReEREbarR.transpose * UJ = exoticReEREbarR
  ext i j
  rw [UJ_conj_apply, Matrix.transpose_apply]
  unfold exoticReEREbarR
  simp only [exoticReEREbarR_Jchar i j]

theorem exoticReEREbarR_cfMat : exoticReEREbarR * cfMat - cfMat * exoticReEREbarR = 0 := by
  ext i j
  rw [Matrix.sub_apply, Matrix.zero_apply, mul_cfMat_apply, cfMat_mul_apply]
  by_cases h : (i = 9 ∧ j = 25) ∨ (i = 25 ∧ j = 9)
  · have hD : exoticReEREbarR i j = 1 := by unfold exoticReEREbarR; simp [h]
    have hcf : cfIndicator i = cfIndicator j := exoticReEREbarR_cfInd i j h
    rw [hD, hcf]; ring
  · have hD : exoticReEREbarR i j = 0 := by unfold exoticReEREbarR; simp [h]
    rw [hD]; ring

/-! ### EREbarR (Im) -/

theorem exoticImEREbarR_swap1 (i j : I32) :
    ((j = 9 ∧ i = 25)) ↔ ((i = 25 ∧ j = 9)) := by
  constructor
  · rintro ⟨h1,h2⟩
    · exact ⟨h2, h1⟩
  · rintro ⟨h1,h2⟩
    · exact ⟨h2, h1⟩

theorem exoticImEREbarR_swap2 (i j : I32) :
    ((j = 25 ∧ i = 9)) ↔ ((i = 9 ∧ j = 25)) := by
  constructor
  · rintro ⟨h1,h2⟩
    · exact ⟨h2, h1⟩
  · rintro ⟨h1,h2⟩
    · exact ⟨h2, h1⟩

theorem exoticImEREbarR_disjoint (i j : I32)
    (h : (i = 9 ∧ j = 25)) : ¬ ((i = 25 ∧ j = 9)) := by
  rcases h with ⟨rfl,rfl⟩
  · intro hcon
    rcases hcon with ⟨h1,_⟩
    · exact (by decide : (9:I32) ≠ 25) h1

theorem exoticImEREbarR_Jchar1 (i j : I32) :
    ((partner j = 9 ∧ partner i = 25)) ↔
    ((i = 9 ∧ j = 25)) := by
  constructor
  · rintro ⟨h1,h2⟩
    · have hj : j = (25:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (9:I32) = (25:I32) from by decide] at h1'
      have hi : i = (9:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (25:I32) = (9:I32) from by decide] at h2'
      rw [hi, hj]
      exact ⟨rfl, rfl⟩
  · rintro (⟨rfl,rfl⟩) <;> simp [partner]

theorem exoticImEREbarR_Jchar2 (i j : I32) :
    ((partner j = 25 ∧ partner i = 9)) ↔
    ((i = 25 ∧ j = 9)) := by
  constructor
  · rintro ⟨h1,h2⟩
    · have hj : j = (9:I32) := by
        have h1' := partner_eq_of h1
        rwa [show partner (25:I32) = (9:I32) from by decide] at h1'
      have hi : i = (25:I32) := by
        have h2' := partner_eq_of h2
        rwa [show partner (9:I32) = (25:I32) from by decide] at h2'
      rw [hi, hj]
      exact ⟨rfl, rfl⟩
  · rintro (⟨rfl,rfl⟩) <;> simp [partner]

theorem exoticImEREbarR_gsign (i j : I32)
    (h : ((i = 9 ∧ j = 25)) ∨ ((i = 25 ∧ j = 9))) :
    gammaF i i + gammaF j j = 0 := by
  rcases h with (⟨rfl,rfl⟩)|(⟨rfl,rfl⟩)
  · have g1 : gammaF (9:I32) (9:I32) = -1 := by unfold gammaF; simp
    have g2 : gammaF (25:I32) (25:I32) = 1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num
  · have g1 : gammaF (25:I32) (25:I32) = 1 := by unfold gammaF; simp
    have g2 : gammaF (9:I32) (9:I32) = -1 := by unfold gammaF; simp
    rw [g1, g2]; norm_num

theorem exoticImEREbarR_cfInd (i j : I32)
    (h : ((i = 9 ∧ j = 25)) ∨ ((i = 25 ∧ j = 9))) :
    cfIndicator i = cfIndicator j := by
  rcases h with (⟨rfl,rfl⟩)|(⟨rfl,rfl⟩)
  · unfold cfIndicator; simp
  · unfold cfIndicator; simp

theorem exoticImEREbarR_selfAdjoint : exoticImEREbarR.conjTranspose = exoticImEREbarR := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  unfold exoticImEREbarR
  simp only [exoticImEREbarR_swap1 i j, exoticImEREbarR_swap2 i j]
  by_cases h1 : (i = 9 ∧ j = 25)
  · by_cases h2 : (i = 25 ∧ j = 9)
    · exact absurd h2 (exoticImEREbarR_disjoint i j h1)
    · simp [h1, h2]
  · by_cases h2 : (i = 25 ∧ j = 9)
    · simp [h1, h2]
    · simp [h1, h2]

theorem exoticImEREbarR_gradingOdd : gammaF * exoticImEREbarR + exoticImEREbarR * gammaF = 0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply, gammaF_mul_apply, mul_gammaF_apply]
  by_cases h1 : (i = 9 ∧ j = 25)
  · have hD : exoticImEREbarR i j = Complex.I := by unfold exoticImEREbarR; simp [h1]
    have hsign : gammaF i i + gammaF j j = 0 := exoticImEREbarR_gsign i j (Or.inl h1)
    rw [hD]
    have hrw : gammaF i i * Complex.I + Complex.I * gammaF j j
        = (gammaF i i + gammaF j j) * Complex.I := by ring
    rw [hrw, hsign, zero_mul]
  · by_cases h2 : (i = 25 ∧ j = 9)
    · have hD : exoticImEREbarR i j = -Complex.I := by unfold exoticImEREbarR; simp [h1, h2]
      have hsign : gammaF i i + gammaF j j = 0 := exoticImEREbarR_gsign i j (Or.inr h2)
      rw [hD]
      have hrw : gammaF i i * -Complex.I + -Complex.I * gammaF j j
          = (gammaF i i + gammaF j j) * -Complex.I := by ring
      rw [hrw, hsign, zero_mul]
    · have hD : exoticImEREbarR i j = 0 := by unfold exoticImEREbarR; simp [h1, h2]
      rw [hD]; simp

theorem exoticImEREbarR_Jcompat : IsJCompatible exoticImEREbarR := by
  show UJ * exoticImEREbarR.transpose * UJ = exoticImEREbarR
  ext i j
  rw [UJ_conj_apply, Matrix.transpose_apply]
  unfold exoticImEREbarR
  simp only [exoticImEREbarR_Jchar1 i j, exoticImEREbarR_Jchar2 i j]

theorem exoticImEREbarR_cfMat : exoticImEREbarR * cfMat - cfMat * exoticImEREbarR = 0 := by
  ext i j
  rw [Matrix.sub_apply, Matrix.zero_apply, mul_cfMat_apply, cfMat_mul_apply]
  by_cases h1 : (i = 9 ∧ j = 25)
  · have hD : exoticImEREbarR i j = Complex.I := by unfold exoticImEREbarR; simp [h1]
    have hcf : cfIndicator i = cfIndicator j := exoticImEREbarR_cfInd i j (Or.inl h1)
    rw [hD, hcf]; ring
  · by_cases h2 : (i = 25 ∧ j = 9)
    · have hD : exoticImEREbarR i j = -Complex.I := by unfold exoticImEREbarR; simp [h1, h2]
      have hcf : cfIndicator i = cfIndicator j := exoticImEREbarR_cfInd i j (Or.inr h2)
      rw [hD, hcf]; ring
    · have hD : exoticImEREbarR i j = 0 := by unfold exoticImEREbarR; simp [h1, h2]
      rw [hD]; ring

end ThetLogos
