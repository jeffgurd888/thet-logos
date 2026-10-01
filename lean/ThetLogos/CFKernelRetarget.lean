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

/-! ## Phase 2c: Order-one for the 12 exotic matrices

`OrderOneHolds E` unfolds to the 144 double commutators
`[[E, smGen g1], smGenOp g2] = 0`.  Strategy per matrix:

* (M, ·): the inner commutator `[E, genM a]` vanishes (leptonic directions
  have support disjoint from the colour triplets; quark directions use
  colour-universal intertwining), so all 96 pairs are trivial.
* (C, C°): both generators diagonal; entrywise
  `E_{ij}(c_j-c_i)(d_j-d_i)` with the factor vanishing on `supp(E)`.
* (C, H°), (C, M°), (H, H°), (H, M°): support-disjointness via
  `disjoint_mul_zero` / `oo_disjoint`.
* (H, C°): `C°` diagonal and constant on the `[E, genH k]` support.

The eight leptonic directions (νL↔eR, eL↔νR, νR↔ēR, eR↔ēR, Re/Im) and
the four quark directions (uL↔dR, dL↔uR, Re/Im) are all proved completely:
all twelve `OrderOneHolds` theorems are machine-checked below with no
unfinished proofs.  The (C, M°) and (H, M°) classes close via the Jacobi-style
`double_comm_of_comm` (using `[E, M°] = 0` and `[genC/genH, M°] = 0`)
rather than support-disjointness.
-/

-- ==========================================================================
-- Shared infrastructure
-- ==========================================================================

/-- genC diagonal values. -/
def genCVal : I32 → ℂ := fun k =>
  if 8 ≤ k.val ∧ k.val < 16 then Complex.I
  else if k.val = 16 ∨ k.val = 17 ∨ k.val = 24 ∨ k.val = 25 then Complex.I
  else 0

theorem genC_eq_diag (i j : I32) : genC i j = if i = j then genCVal i else 0 := by
  unfold genC genCVal
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- smGenOp 0 diagonal values: genCVal at the partner index. -/
def genCOpVal : I32 → ℂ := fun k => genCVal (partner k)

theorem smGenOp_zero_eq (i j : I32) :
    smGenOp 0 i j = if i = j then genCOpVal i else 0 := by
  have h1 : smGen 0 = genC := rfl
  show (UJ * (smGen 0).transpose * UJ) i j = _
  rw [h1, UJ_conj_apply]
  simp only [Matrix.transpose_apply]
  rw [genC_eq_diag (partner j) (partner i)]
  by_cases h : i = j
  · subst h
    simp [genCOpVal]
  · have hp : partner j ≠ partner i := by
      intro hc
      apply h
      have h2 := congrArg partner hc
      rw [partner_involutive, partner_involutive] at h2
      exact h2.symm
    simp [h, hp]

/-- Commutator entry with a diagonal matrix. -/
theorem comm_diag_entry (E : Matrix I32 I32 ℂ) (v : I32 → ℂ)
    (D : Matrix I32 I32 ℂ) (hD : ∀ i j, D i j = if i = j then v i else 0)
    (i j : I32) :
    (E * D - D * E) i j = E i j * (v j - v i) := by
  have h1 : (E * D) i j = E i j * v j := by
    simp only [Matrix.mul_apply]
    rw [Finset.sum_eq_single j]
    · simp [hD j j]
    · intro k _ hkj
      rw [hD k j, if_neg hkj, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ j) hcon
  have h2 : (D * E) i j = v i * E i j := by
    simp only [Matrix.mul_apply]
    rw [Finset.sum_eq_single i]
    · simp [hD i i]
    · intro k _ hki
      rw [hD i k, if_neg (Ne.symm hki), zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ i) hcon
  simp only [Matrix.sub_apply]
  rw [h1, h2]
  ring

/-- Double-commutator entry with two diagonal matrices. -/
theorem oo_diag_diag_entry (E : Matrix I32 I32 ℂ) (v w : I32 → ℂ)
    (D1 D2 : Matrix I32 I32 ℂ)
    (hD1 : ∀ i j, D1 i j = if i = j then v i else 0)
    (hD2 : ∀ i j, D2 i j = if i = j then w i else 0)
    (i j : I32) :
    ((E * D1 - D1 * E) * D2 - D2 * (E * D1 - D1 * E)) i j
      = E i j * ((v j - v i) * (w j - w i)) := by
  have hC : ∀ x y, (E * D1 - D1 * E) x y = E x y * (v y - v x) :=
    fun x y => comm_diag_entry E v D1 hD1 x y
  have h1 : ((E * D1 - D1 * E) * D2) i j = (E * D1 - D1 * E) i j * w j := by
    simp only [Matrix.mul_apply]
    rw [Finset.sum_eq_single j]
    · simp [hD2 j j]
    · intro k _ hkj
      rw [hD2 k j, if_neg hkj, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ j) hcon
  have h2 : (D2 * (E * D1 - D1 * E)) i j = w i * (E * D1 - D1 * E) i j := by
    simp only [Matrix.mul_apply]
    rw [Finset.sum_eq_single i]
    · simp [hD2 i i]
    · intro k _ hki
      rw [hD2 i k, if_neg (Ne.symm hki), zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ i) hcon
  simp only [Matrix.sub_apply]
  rw [h1, h2, hC i j]
  ring

/-- (C, C°) case from a support factor condition. -/
theorem oo_C_C_of_factor (E : Matrix I32 I32 ℂ)
    (hE : ∀ i j, E i j ≠ 0 →
      (genCVal j - genCVal i) * (genCOpVal j - genCOpVal i) = 0) :
    (E * genC - genC * E) * smGenOp 0
      - smGenOp 0 * (E * genC - genC * E) = 0 := by
  ext i j
  simp only [Matrix.zero_apply]
  rw [oo_diag_diag_entry E genCVal genCOpVal genC (smGenOp 0)
    (fun x y => genC_eq_diag x y) (fun x y => smGenOp_zero_eq x y)]
  rcases eq_or_ne (E i j) 0 with hEij | hEij
  · rw [hEij, zero_mul]
  · rw [hE i j hEij, mul_zero]

/-- Double commutator via support disjointness: `[E,P]` lives on `RS × RS`
    while `Q` avoids `RS`. -/
theorem oo_disjoint (E P Q : Matrix I32 I32 ℂ) (RS : Finset I32)
    (hEP : ∀ i j, (E * P - P * E) i j ≠ 0 → i ∈ RS ∧ j ∈ RS)
    (hQ : ∀ x y, Q x y ≠ 0 → x ∉ RS ∧ y ∉ RS) :
    (E * P - P * E) * Q - Q * (E * P - P * E) = 0 := by
  have h1 : (E * P - P * E) * Q = 0 := by
    apply disjoint_mul_zero (fun m => m ∈ RS)
    · intro i k hik
      exact (hEP i k hik).2
    · intro k j hkj
      exact (hQ k j hkj).1
  have h2 : Q * (E * P - P * E) = 0 := by
    apply disjoint_mul_zero (fun m => m ∉ RS)
    · intro i k hik
      exact (hQ i k hik).2
    · intro k j hkj
      exact not_not_intro (hEP k j hkj).1
  rw [h1, h2, sub_self]

/-- If E's support avoids the colour triplets, `[E, genM a] = 0`. -/
theorem comm_genM_of_avoids (E : Matrix I32 I32 ℂ) (a : Fin 8)
    (hE : ∀ x y, E x y ≠ 0 → tripletOf x.val = none ∧ tripletOf y.val = none) :
    E * genM a = genM a * E := by
  ext i j
  simp only [Matrix.mul_apply]
  have h1 : ∑ k : I32, E i k * genM a k j = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases hEk : E i k = 0
    · rw [hEk, zero_mul]
    · have hG : genM a k j = 0 := by
        by_contra hG'
        push_neg at hG'
        obtain ⟨t, p, q, hkt, _⟩ := genM_supp_triplet a k j hG'
        rw [(hE i k hEk).2] at hkt
        simp at hkt
      rw [hG, mul_zero]
  have h2 : ∑ k : I32, genM a i k * E k j = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases hG : genM a i k = 0
    · rw [hG, zero_mul]
    · have hEkj : E k j = 0 := by
        by_contra hE'
        push_neg at hE'
        obtain ⟨t, p, q, _, hkt⟩ := genM_supp_triplet a i k hG
        rw [(hE k j hE').1] at hkt
        simp at hkt
      rw [hEkj, mul_zero]
  rw [h1, h2]

-- ==========================================================================
-- exoticReNuLeR : OrderOneHolds
-- ==========================================================================

theorem exoticReNuLeR_supp (i j : I32) (h : exoticReNuLeR i j ≠ 0) :
    (i = 0 ∧ j = 9) ∨ (i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25) ∨ (i = 25 ∧ j = 16) := by
  unfold exoticReNuLeR at h
  by_cases hs : (i = 0 ∧ j = 9) ∨ (i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25) ∨ (i = 25 ∧ j = 16)
  · exact hs
  · rw [if_neg hs] at h
    exact absurd rfl h

theorem exoticReNuLeR_avoids_triplets (x y : I32) (h : exoticReNuLeR x y ≠ 0) :
    tripletOf x.val = none ∧ tripletOf y.val = none := by
  rcases exoticReNuLeR_supp x y h with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; decide
  · rw [hx, hy]; decide
  · rw [hx, hy]; decide
  · rw [hx, hy]; decide

theorem exoticReNuLeR_comm_genM (a : Fin 8) :
    exoticReNuLeR * genM a = genM a * exoticReNuLeR :=
  comm_genM_of_avoids exoticReNuLeR a exoticReNuLeR_avoids_triplets

theorem exoticReNuLeR_factor_CC (i j : I32) (h : exoticReNuLeR i j ≠ 0) :
    (genCVal j - genCVal i) * (genCOpVal j - genCOpVal i) = 0 := by
  rcases exoticReNuLeR_supp i j h with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]

theorem exoticReNuLeR_oo_C_C :
    (exoticReNuLeR * genC - genC * exoticReNuLeR) * smGenOp 0
      - smGenOp 0 * (exoticReNuLeR * genC - genC * exoticReNuLeR) = 0 :=
  oo_C_C_of_factor exoticReNuLeR exoticReNuLeR_factor_CC

theorem exoticReNuLeR_comm_genC_mem (i j : I32)
    (h : (exoticReNuLeR * genC - genC * exoticReNuLeR) i j ≠ 0) :
    (i = 0 ∨ i = 9) ∧ (j = 0 ∨ j = 9) := by
  rw [comm_diag_entry _ _ _ (fun x y => genC_eq_diag x y) i j] at h
  have hE : exoticReNuLeR i j ≠ 0 := by
    intro h0; apply h; rw [h0, zero_mul]
  have hc : genCVal j - genCVal i ≠ 0 := by
    intro h0; apply h; rw [h0, mul_zero]
  rcases exoticReNuLeR_supp i j hE with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; exact ⟨Or.inl rfl, Or.inr rfl⟩
  · rw [hx, hy]; exact ⟨Or.inr rfl, Or.inl rfl⟩
  · exfalso; rw [hx, hy] at hc; simp [genCVal] at hc
  · exfalso; rw [hx, hy] at hc; simp [genCVal] at hc

theorem exoticReNuLeR_EgenH_supp (k : Fin 3) (i j : I32)
    (h : (exoticReNuLeR * genH k) i j ≠ 0) :
    i = 9 ∧ (j = 0 ∨ j = 1) := by
  simp only [Matrix.mul_apply] at h
  by_cases hi9 : i = 9
  · subst hi9
    have hE90 : exoticReNuLeR 9 0 = 1 := by simp [exoticReNuLeR]
    have hsum : (∑ l, exoticReNuLeR 9 l * genH k l j) = genH k 0 j := by
      rw [Finset.sum_eq_single 0]
      · rw [hE90, one_mul]
      · intro l _ hl0
        by_cases hE : exoticReNuLeR 9 l = 0
        · rw [hE, zero_mul]
        · exfalso
          rcases exoticReNuLeR_supp 9 l hE with ⟨hx,_⟩|⟨_,hy⟩|⟨hx,_⟩|⟨hx,_⟩
          · simp at hx
          · exact hl0 hy
          · simp at hx
          · simp at hx
      · intro hcon; exact absurd (Finset.mem_univ 0) hcon
    rw [hsum] at h
    have hblock := genH_supp_block k 0 j h
    obtain ⟨_, hj8, hdiv⟩ := hblock
    have hj01 : j.val = 0 ∨ j.val = 1 := by omega
    refine ⟨rfl, ?_⟩
    rcases hj01 with hv|hv
    · left; exact Fin.ext (by simpa using hv)
    · right; exact Fin.ext (by simpa using hv)
  · exfalso
    apply h
    apply Finset.sum_eq_zero
    intro l _
    by_cases hE : exoticReNuLeR i l = 0
    · rw [hE, zero_mul]
    · rcases exoticReNuLeR_supp i l hE with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
      · rw [hy]
        have hG0 : genH k 9 j = 0 := by
          by_contra hG'
          have hs := genH_supp k 9 j hG'
          simp at hs
        rw [hG0, mul_zero]
      · exfalso; exact hi9 hx
      · rw [hy]
        have hG0 : genH k 25 j = 0 := by
          by_contra hG'
          have hs := genH_supp k 25 j hG'
          simp at hs
        rw [hG0, mul_zero]
      · rw [hy]
        have hG0 : genH k 16 j = 0 := by
          by_contra hG'
          have hs := genH_supp k 16 j hG'
          simp at hs
        rw [hG0, mul_zero]

theorem not_mem_09_of_ge16 {x : I32} (h : 16 ≤ x.val) :
    x ∉ ({0, 9} : Finset I32) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h

theorem not_mem_09_of_genM_supp {x : I32}
    (h : (2 ≤ x.val ∧ x.val < 8) ∨ (10 ≤ x.val ∧ x.val < 16)) :
    x ∉ ({0, 9} : Finset I32) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  rcases h with ⟨h1,h2⟩|⟨h1,h2⟩
  · constructor
    · intro hcon; rw [hcon] at h1; simp at h1
    · intro hcon; rw [hcon] at h2; simp at h2
  · constructor
    · intro hcon; rw [hcon] at h1; simp at h1
    · intro hcon; rw [hcon] at h1; simp at h1

theorem exoticReNuLeR_oo_C_H (k : Fin 3) :
    (exoticReNuLeR * genC - genC * exoticReNuLeR) * (UJ * (genH k).transpose * UJ)
      - (UJ * (genH k).transpose * UJ) * (exoticReNuLeR * genC - genC * exoticReNuLeR) = 0 := by
  apply oo_disjoint _ _ _ {0, 9}
  · intro i j hij
    obtain ⟨hi, hj⟩ := exoticReNuLeR_comm_genC_mem i j hij
    constructor
    · simp only [Finset.mem_insert, Finset.mem_singleton]; exact hi
    · simp only [Finset.mem_insert, Finset.mem_singleton]; exact hj
  · intro x y hxy
    have hsupp := UJ_genH_transpose_UJ_supp k x y hxy
    exact ⟨not_mem_09_of_ge16 hsupp.1, not_mem_09_of_ge16 hsupp.2.2.1⟩

theorem exoticReNuLeR_oo_C_M (a : Fin 8) :
    (exoticReNuLeR * genC - genC * exoticReNuLeR) * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ) * (exoticReNuLeR * genC - genC * exoticReNuLeR) = 0 := by
  apply oo_disjoint _ _ _ {0, 9}
  · intro i j hij
    obtain ⟨hi, hj⟩ := exoticReNuLeR_comm_genC_mem i j hij
    constructor
    · simp only [Finset.mem_insert, Finset.mem_singleton]; exact hi
    · simp only [Finset.mem_insert, Finset.mem_singleton]; exact hj
  · intro x y hxy
    obtain ⟨hx, hy⟩ := UJ_genM_transpose_UJ_supp a x y hxy
    exact ⟨not_mem_09_of_genM_supp hx, not_mem_09_of_genM_supp hy⟩

theorem smGen_zero_eq : smGen (0 : Fin 12) = genC := rfl
theorem smGen_one_eq : smGen (1 : Fin 12) = genH 0 := rfl
theorem smGen_two_eq : smGen (2 : Fin 12) = genH 1 := rfl
theorem smGen_three_eq : smGen (3 : Fin 12) = genH 2 := rfl
theorem smGen_four_eq : smGen (4 : Fin 12) = genM 0 := rfl
theorem smGen_five_eq : smGen (5 : Fin 12) = genM 1 := rfl
theorem smGen_six_eq : smGen (6 : Fin 12) = genM 2 := rfl
theorem smGen_seven_eq : smGen (7 : Fin 12) = genM 3 := rfl
theorem smGen_eight_eq : smGen (8 : Fin 12) = genM 4 := rfl
theorem smGen_nine_eq : smGen (9 : Fin 12) = genM 5 := rfl
theorem smGen_ten_eq : smGen (10 : Fin 12) = genM 6 := rfl
theorem smGen_eleven_eq : smGen (11 : Fin 12) = genM 7 := rfl

theorem smGenOp_zero_eq' : smGenOp (0 : Fin 12) = UJ * genC.transpose * UJ := rfl
theorem smGenOp_one_eq : smGenOp (1 : Fin 12) = UJ * (genH 0).transpose * UJ := rfl
theorem smGenOp_two_eq : smGenOp (2 : Fin 12) = UJ * (genH 1).transpose * UJ := rfl
theorem smGenOp_three_eq : smGenOp (3 : Fin 12) = UJ * (genH 2).transpose * UJ := rfl
theorem smGenOp_four_eq : smGenOp (4 : Fin 12) = UJ * (genM 0).transpose * UJ := rfl
theorem smGenOp_five_eq : smGenOp (5 : Fin 12) = UJ * (genM 1).transpose * UJ := rfl
theorem smGenOp_six_eq : smGenOp (6 : Fin 12) = UJ * (genM 2).transpose * UJ := rfl
theorem smGenOp_seven_eq : smGenOp (7 : Fin 12) = UJ * (genM 3).transpose * UJ := rfl
theorem smGenOp_eight_eq : smGenOp (8 : Fin 12) = UJ * (genM 4).transpose * UJ := rfl
theorem smGenOp_nine_eq : smGenOp (9 : Fin 12) = UJ * (genM 5).transpose * UJ := rfl
theorem smGenOp_ten_eq : smGenOp (10 : Fin 12) = UJ * (genM 6).transpose * UJ := rfl
theorem smGenOp_eleven_eq : smGenOp (11 : Fin 12) = UJ * (genM 7).transpose * UJ := rfl

theorem exoticReNuLeR_oo_C (g2 : Fin 12) :
    (exoticReNuLeR * genC - genC * exoticReNuLeR) * smGenOp g2
      - smGenOp g2 * (exoticReNuLeR * genC - genC * exoticReNuLeR) = 0 := by
  fin_cases g2
  · exact exoticReNuLeR_oo_C_C
  · show (exoticReNuLeR * genC - genC * exoticReNuLeR) * (UJ * (genH 0).transpose * UJ)
        - (UJ * (genH 0).transpose * UJ) * (exoticReNuLeR * genC - genC * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_C_H 0
  · show (exoticReNuLeR * genC - genC * exoticReNuLeR) * (UJ * (genH 1).transpose * UJ)
        - (UJ * (genH 1).transpose * UJ) * (exoticReNuLeR * genC - genC * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_C_H 1
  · show (exoticReNuLeR * genC - genC * exoticReNuLeR) * (UJ * (genH 2).transpose * UJ)
        - (UJ * (genH 2).transpose * UJ) * (exoticReNuLeR * genC - genC * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_C_H 2
  · show (exoticReNuLeR * genC - genC * exoticReNuLeR) * (UJ * (genM 0).transpose * UJ)
        - (UJ * (genM 0).transpose * UJ) * (exoticReNuLeR * genC - genC * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_C_M 0
  · show (exoticReNuLeR * genC - genC * exoticReNuLeR) * (UJ * (genM 1).transpose * UJ)
        - (UJ * (genM 1).transpose * UJ) * (exoticReNuLeR * genC - genC * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_C_M 1
  · show (exoticReNuLeR * genC - genC * exoticReNuLeR) * (UJ * (genM 2).transpose * UJ)
        - (UJ * (genM 2).transpose * UJ) * (exoticReNuLeR * genC - genC * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_C_M 2
  · show (exoticReNuLeR * genC - genC * exoticReNuLeR) * (UJ * (genM 3).transpose * UJ)
        - (UJ * (genM 3).transpose * UJ) * (exoticReNuLeR * genC - genC * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_C_M 3
  · show (exoticReNuLeR * genC - genC * exoticReNuLeR) * (UJ * (genM 4).transpose * UJ)
        - (UJ * (genM 4).transpose * UJ) * (exoticReNuLeR * genC - genC * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_C_M 4
  · show (exoticReNuLeR * genC - genC * exoticReNuLeR) * (UJ * (genM 5).transpose * UJ)
        - (UJ * (genM 5).transpose * UJ) * (exoticReNuLeR * genC - genC * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_C_M 5
  · show (exoticReNuLeR * genC - genC * exoticReNuLeR) * (UJ * (genM 6).transpose * UJ)
        - (UJ * (genM 6).transpose * UJ) * (exoticReNuLeR * genC - genC * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_C_M 6
  · show (exoticReNuLeR * genC - genC * exoticReNuLeR) * (UJ * (genM 7).transpose * UJ)
        - (UJ * (genM 7).transpose * UJ) * (exoticReNuLeR * genC - genC * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_C_M 7


theorem exoticReNuLeR_oo_M (a : Fin 8) (g2 : Fin 12) :
    (exoticReNuLeR * genM a - genM a * exoticReNuLeR) * smGenOp g2
      - smGenOp g2 * (exoticReNuLeR * genM a - genM a * exoticReNuLeR) = 0 := by
  have hcomm : exoticReNuLeR * genM a - genM a * exoticReNuLeR = 0 :=
    sub_eq_zero.mpr (exoticReNuLeR_comm_genM a)
  rw [hcomm, zero_mul, mul_zero, sub_zero]

theorem exoticReNuLeR_mul_genH (k : Fin 3) (i j : I32) :
    (exoticReNuLeR * genH k) i j = if i = 9 then genH k 0 j else 0 := by
  simp only [Matrix.mul_apply]
  by_cases hi : i = 9
  · subst hi
    have hE90 : exoticReNuLeR 9 0 = 1 := by simp [exoticReNuLeR]
    rw [if_pos rfl, Finset.sum_eq_single 0]
    · rw [hE90, one_mul]
    · intro l _ hl0
      by_cases hE : exoticReNuLeR 9 l = 0
      · rw [hE, zero_mul]
      · exfalso
        have hsupp := exoticReNuLeR_supp 9 l hE
        rcases hsupp with ⟨h1,_⟩|⟨_,h2⟩|⟨h1,_⟩|⟨h1,_⟩
        · simp at h1
        · exact hl0 h2
        · simp at h1
        · simp at h1
    · intro hcon; exact absurd (Finset.mem_univ 0) hcon
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hE : exoticReNuLeR i l = 0
    · rw [hE, zero_mul]
    · have hsupp := exoticReNuLeR_supp i l hE
      rcases hsupp with ⟨_,h2⟩|⟨h1,_⟩|⟨_,h2⟩|⟨_,h2⟩
      · rw [h2]
        have hG0 : genH k 9 j = 0 := by
          by_contra hG'
          have hs := genH_supp k 9 j hG'
          simp at hs
        rw [hG0, mul_zero]
      · exfalso; exact hi h1
      · rw [h2]
        have hG0 : genH k 25 j = 0 := by
          by_contra hG'
          have hs := genH_supp k 25 j hG'
          simp at hs
        rw [hG0, mul_zero]
      · rw [h2]
        have hG0 : genH k 16 j = 0 := by
          by_contra hG'
          have hs := genH_supp k 16 j hG'
          simp at hs
        rw [hG0, mul_zero]

theorem exoticReNuLeR_genH_mul (k : Fin 3) (i j : I32) :
    (genH k * exoticReNuLeR) i j = if j = 9 then genH k i 0 else 0 := by
  simp only [Matrix.mul_apply]
  by_cases hj : j = 9
  · subst hj
    have hE09 : exoticReNuLeR 0 9 = 1 := by simp [exoticReNuLeR]
    rw [if_pos rfl, Finset.sum_eq_single 0]
    · rw [hE09, mul_one]
    · intro l _ hl0
      by_cases hE : exoticReNuLeR l 9 = 0
      · rw [hE, mul_zero]
      · exfalso
        have hsupp := exoticReNuLeR_supp l 9 hE
        rcases hsupp with ⟨h1,_⟩|⟨_,h2⟩|⟨_,h2⟩|⟨_,h2⟩
        · exact hl0 h1
        · simp at h2
        · simp at h2
        · simp at h2
    · intro hcon; exact absurd (Finset.mem_univ 0) hcon
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hE : exoticReNuLeR l j = 0
    · rw [hE, mul_zero]
    · have hsupp := exoticReNuLeR_supp l j hE
      rcases hsupp with ⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩
      · -- (l,j)=(0,9): j=9, contradiction
        exfalso; exact hj h2
      · -- (l,j)=(9,0): l=9, genH_{i,9}=0
        rw [h1]
        have hG0 : genH k i 9 = 0 := by
          by_contra hG'
          have hs := genH_supp k i 9 hG'
          simp at hs
        rw [hG0, zero_mul]
      · -- (l,j)=(16,25): l=16, genH_{i,16}=0
        rw [h1]
        have hG0 : genH k i 16 = 0 := by
          by_contra hG'
          have hs := genH_supp k i 16 hG'
          simp at hs
        rw [hG0, zero_mul]
      · -- (l,j)=(25,16): l=25, genH_{i,25}=0
        rw [h1]
        have hG0 : genH k i 25 = 0 := by
          by_contra hG'
          have hs := genH_supp k i 25 hG'
          simp at hs
        rw [hG0, zero_mul]

theorem exoticReNuLeR_CH_supp (k : Fin 3) (i j : I32)
    (h : (exoticReNuLeR * genH k - genH k * exoticReNuLeR) i j ≠ 0) :
    (i = 9 ∧ (j = 0 ∨ j = 1)) ∨ ((i = 0 ∨ i = 1) ∧ j = 9) := by
  simp only [Matrix.sub_apply] at h
  by_cases h1 : (exoticReNuLeR * genH k) i j = 0
  · have h2 : (genH k * exoticReNuLeR) i j ≠ 0 := by
      intro hc
      apply h
      rw [h1, hc, sub_zero]
    right
    rw [exoticReNuLeR_genH_mul k i j] at h2
    by_cases hj9 : j = 9
    · subst hj9
      simp only [if_pos rfl] at h2
      have hblock := genH_supp_block k i 0 h2
      obtain ⟨_, _, hdiv⟩ := hblock
      have hi01 : i.val = 0 ∨ i.val = 1 := by omega
      refine ⟨?_, rfl⟩
      rcases hi01 with hv|hv
      · left; exact Fin.ext (by simpa using hv)
      · right; exact Fin.ext (by simpa using hv)
    · rw [if_neg hj9] at h2
      exact absurd rfl h2
  · left
    have h1ne : (exoticReNuLeR * genH k) i j ≠ 0 := h1
    rw [exoticReNuLeR_mul_genH k i j] at h1ne
    by_cases hi9 : i = 9
    · subst hi9
      simp only [if_pos rfl] at h1ne
      have hblock := genH_supp_block k 0 j h1ne
      obtain ⟨_, _, hdiv⟩ := hblock
      have hj01 : j.val = 0 ∨ j.val = 1 := by omega
      refine ⟨rfl, ?_⟩
      rcases hj01 with hv|hv
      · left; exact Fin.ext (by simpa using hv)
      · right; exact Fin.ext (by simpa using hv)
    · rw [if_neg hi9] at h1ne
      exact absurd rfl h1ne

theorem genCOpVal_0_eq : genCOpVal (0 : I32) = Complex.I := by
  simp [genCOpVal, genCVal, partner]
theorem genCOpVal_1_eq : genCOpVal (1 : I32) = Complex.I := by
  simp [genCOpVal, genCVal, partner]
theorem genCOpVal_9_eq : genCOpVal (9 : I32) = Complex.I := by
  simp [genCOpVal, genCVal, partner]

theorem exoticReNuLeR_oo_H_C (k : Fin 3) :
    (exoticReNuLeR * genH k - genH k * exoticReNuLeR) * smGenOp 0
      - smGenOp 0 * (exoticReNuLeR * genH k - genH k * exoticReNuLeR) = 0 := by
  have hD : ∀ x y : I32, smGenOp 0 x y = if x = y then genCOpVal x else 0 :=
    fun x y => smGenOp_zero_eq x y
  ext i j
  simp only [Matrix.zero_apply, Matrix.sub_apply]
  have hCD : ((exoticReNuLeR * genH k - genH k * exoticReNuLeR) * smGenOp 0) i j
           = (exoticReNuLeR * genH k - genH k * exoticReNuLeR) i j * genCOpVal j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hD j j, if_pos rfl]
    · intro l _ hlj
      rw [hD l j, if_neg hlj, mul_zero]
    · intro hcon; exact absurd (Finset.mem_univ j) hcon
  have hDC : (smGenOp 0 * (exoticReNuLeR * genH k - genH k * exoticReNuLeR)) i j
           = genCOpVal i * (exoticReNuLeR * genH k - genH k * exoticReNuLeR) i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hD i i, if_pos rfl]
    · intro l _ hli
      rw [hD i l, if_neg (Ne.symm hli), zero_mul]
    · intro hcon; exact absurd (Finset.mem_univ i) hcon
  rw [hCD, hDC]
  by_cases hC : (exoticReNuLeR * genH k - genH k * exoticReNuLeR) i j = 0
  · rw [hC, zero_mul, mul_zero, sub_zero]
  · have hsupp := exoticReNuLeR_CH_supp k i j hC
    have hw : genCOpVal j = genCOpVal i := by
      rcases hsupp with ⟨hi9, hj01⟩|⟨hi01, hj9⟩
      · subst hi9
        rcases hj01 with hj0|hj1
        · subst hj0; rw [genCOpVal_0_eq, genCOpVal_9_eq]
        · subst hj1; rw [genCOpVal_1_eq, genCOpVal_9_eq]
      · subst hj9
        rcases hi01 with hi0|hi1
        · subst hi0; rw [genCOpVal_0_eq, genCOpVal_9_eq]
        · subst hi1; rw [genCOpVal_1_eq, genCOpVal_9_eq]
    rw [hw, mul_comm, sub_self]

theorem not_mem_019_of_ge16 {x : I32} (h : 16 ≤ x.val) :
    x ∉ ({0, 1, 9} : Finset I32) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_, ?_⟩
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h

theorem not_mem_019_of_genM_supp {x : I32}
    (h : (2 ≤ x.val ∧ x.val < 8) ∨ (10 ≤ x.val ∧ x.val < 16)) :
    x ∉ ({0, 1, 9} : Finset I32) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  rcases h with ⟨h1,h2⟩|⟨h1,h2⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro hcon; rw [hcon] at h1; simp at h1
    · intro hcon; rw [hcon] at h1; simp at h1
    · intro hcon; rw [hcon] at h2; simp at h2
  · refine ⟨?_, ?_, ?_⟩
    · intro hcon; rw [hcon] at h1; simp at h1
    · intro hcon; rw [hcon] at h1; simp at h1
    · intro hcon; rw [hcon] at h1; simp at h1

theorem exoticReNuLeR_oo_H_H (k : Fin 3) (a : Fin 3) :
    (exoticReNuLeR * genH k - genH k * exoticReNuLeR) * (UJ * (genH a).transpose * UJ)
      - (UJ * (genH a).transpose * UJ) * (exoticReNuLeR * genH k - genH k * exoticReNuLeR) = 0 := by
  apply oo_disjoint _ _ _ {0, 1, 9}
  · intro i j hij
    have hsupp := exoticReNuLeR_CH_supp k i j hij
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hsupp with ⟨hi9, hj01⟩|⟨hi01, hj9⟩
    · subst hi9
      rcases hj01 with hj0|hj1
      · subst hj0; exact ⟨Or.inr (Or.inr rfl), Or.inl rfl⟩
      · subst hj1; exact ⟨Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩
    · subst hj9
      rcases hi01 with hi0|hi1
      · subst hi0; exact ⟨Or.inl rfl, Or.inr (Or.inr rfl)⟩
      · subst hi1; exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
  · intro x y hxy
    have hsupp := UJ_genH_transpose_UJ_supp a x y hxy
    exact ⟨not_mem_019_of_ge16 hsupp.1, not_mem_019_of_ge16 hsupp.2.2.1⟩

theorem exoticReNuLeR_oo_H_M (k : Fin 3) (a : Fin 8) :
    (exoticReNuLeR * genH k - genH k * exoticReNuLeR) * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ) * (exoticReNuLeR * genH k - genH k * exoticReNuLeR) = 0 := by
  apply oo_disjoint _ _ _ {0, 1, 9}
  · intro i j hij
    have hsupp := exoticReNuLeR_CH_supp k i j hij
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hsupp with ⟨hi9, hj01⟩|⟨hi01, hj9⟩
    · subst hi9
      rcases hj01 with hj0|hj1
      · subst hj0; exact ⟨Or.inr (Or.inr rfl), Or.inl rfl⟩
      · subst hj1; exact ⟨Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩
    · subst hj9
      rcases hi01 with hi0|hi1
      · subst hi0; exact ⟨Or.inl rfl, Or.inr (Or.inr rfl)⟩
      · subst hi1; exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
  · intro x y hxy
    have hsupp := UJ_genM_transpose_UJ_supp a x y hxy
    exact ⟨not_mem_019_of_genM_supp hsupp.1, not_mem_019_of_genM_supp hsupp.2⟩

theorem exoticReNuLeR_oo_H (k : Fin 3) (g2 : Fin 12) :
    (exoticReNuLeR * genH k - genH k * exoticReNuLeR) * smGenOp g2
      - smGenOp g2 * (exoticReNuLeR * genH k - genH k * exoticReNuLeR) = 0 := by
  fin_cases g2
  · exact exoticReNuLeR_oo_H_C k
  · show (exoticReNuLeR * genH k - genH k * exoticReNuLeR) * (UJ * (genH 0).transpose * UJ)
        - (UJ * (genH 0).transpose * UJ) * (exoticReNuLeR * genH k - genH k * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_H_H k 0
  · show (exoticReNuLeR * genH k - genH k * exoticReNuLeR) * (UJ * (genH 1).transpose * UJ)
        - (UJ * (genH 1).transpose * UJ) * (exoticReNuLeR * genH k - genH k * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_H_H k 1
  · show (exoticReNuLeR * genH k - genH k * exoticReNuLeR) * (UJ * (genH 2).transpose * UJ)
        - (UJ * (genH 2).transpose * UJ) * (exoticReNuLeR * genH k - genH k * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_H_H k 2
  · show (exoticReNuLeR * genH k - genH k * exoticReNuLeR) * (UJ * (genM 0).transpose * UJ)
        - (UJ * (genM 0).transpose * UJ) * (exoticReNuLeR * genH k - genH k * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_H_M k 0
  · show (exoticReNuLeR * genH k - genH k * exoticReNuLeR) * (UJ * (genM 1).transpose * UJ)
        - (UJ * (genM 1).transpose * UJ) * (exoticReNuLeR * genH k - genH k * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_H_M k 1
  · show (exoticReNuLeR * genH k - genH k * exoticReNuLeR) * (UJ * (genM 2).transpose * UJ)
        - (UJ * (genM 2).transpose * UJ) * (exoticReNuLeR * genH k - genH k * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_H_M k 2
  · show (exoticReNuLeR * genH k - genH k * exoticReNuLeR) * (UJ * (genM 3).transpose * UJ)
        - (UJ * (genM 3).transpose * UJ) * (exoticReNuLeR * genH k - genH k * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_H_M k 3
  · show (exoticReNuLeR * genH k - genH k * exoticReNuLeR) * (UJ * (genM 4).transpose * UJ)
        - (UJ * (genM 4).transpose * UJ) * (exoticReNuLeR * genH k - genH k * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_H_M k 4
  · show (exoticReNuLeR * genH k - genH k * exoticReNuLeR) * (UJ * (genM 5).transpose * UJ)
        - (UJ * (genM 5).transpose * UJ) * (exoticReNuLeR * genH k - genH k * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_H_M k 5
  · show (exoticReNuLeR * genH k - genH k * exoticReNuLeR) * (UJ * (genM 6).transpose * UJ)
        - (UJ * (genM 6).transpose * UJ) * (exoticReNuLeR * genH k - genH k * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_H_M k 6
  · show (exoticReNuLeR * genH k - genH k * exoticReNuLeR) * (UJ * (genM 7).transpose * UJ)
        - (UJ * (genM 7).transpose * UJ) * (exoticReNuLeR * genH k - genH k * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_H_M k 7

theorem exoticReNuLeR_orderOne : OrderOneHolds exoticReNuLeR := by
  intro g1 g2
  fin_cases g1
  · show (exoticReNuLeR * genC - genC * exoticReNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticReNuLeR * genC - genC * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_C g2
  · show (exoticReNuLeR * genH 0 - genH 0 * exoticReNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticReNuLeR * genH 0 - genH 0 * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_H 0 g2
  · show (exoticReNuLeR * genH 1 - genH 1 * exoticReNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticReNuLeR * genH 1 - genH 1 * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_H 1 g2
  · show (exoticReNuLeR * genH 2 - genH 2 * exoticReNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticReNuLeR * genH 2 - genH 2 * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_H 2 g2
  · show (exoticReNuLeR * genM 0 - genM 0 * exoticReNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticReNuLeR * genM 0 - genM 0 * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_M 0 g2
  · show (exoticReNuLeR * genM 1 - genM 1 * exoticReNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticReNuLeR * genM 1 - genM 1 * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_M 1 g2
  · show (exoticReNuLeR * genM 2 - genM 2 * exoticReNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticReNuLeR * genM 2 - genM 2 * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_M 2 g2
  · show (exoticReNuLeR * genM 3 - genM 3 * exoticReNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticReNuLeR * genM 3 - genM 3 * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_M 3 g2
  · show (exoticReNuLeR * genM 4 - genM 4 * exoticReNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticReNuLeR * genM 4 - genM 4 * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_M 4 g2
  · show (exoticReNuLeR * genM 5 - genM 5 * exoticReNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticReNuLeR * genM 5 - genM 5 * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_M 5 g2
  · show (exoticReNuLeR * genM 6 - genM 6 * exoticReNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticReNuLeR * genM 6 - genM 6 * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_M 6 g2
  · show (exoticReNuLeR * genM 7 - genM 7 * exoticReNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticReNuLeR * genM 7 - genM 7 * exoticReNuLeR) = 0
    exact exoticReNuLeR_oo_M 7 g2

-- ============================================================================
-- exoticImNuLeR : order-one (same support as Re, values ±I)
-- ============================================================================

theorem exoticImNuLeR_supp (i j : I32) (h : exoticImNuLeR i j ≠ 0) :
    (i = 0 ∧ j = 9) ∨ (i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25) ∨ (i = 25 ∧ j = 16) := by
  unfold exoticImNuLeR at h
  by_cases h1 : (i = 0 ∧ j = 9) ∨ (i = 25 ∧ j = 16)
  · rcases h1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · by_cases h2 : (i = 9 ∧ j = 0) ∨ (i = 16 ∧ j = 25)
    · rcases h2 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · simp [h1, h2] at h

theorem exoticImNuLeR_avoids_triplets (x y : I32) (h : exoticImNuLeR x y ≠ 0) :
    tripletOf x.val = none ∧ tripletOf y.val = none := by
  rcases exoticImNuLeR_supp x y h with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; decide
  · rw [hx, hy]; decide
  · rw [hx, hy]; decide
  · rw [hx, hy]; decide

theorem exoticImNuLeR_comm_genM (a : Fin 8) :
    exoticImNuLeR * genM a = genM a * exoticImNuLeR :=
  comm_genM_of_avoids exoticImNuLeR a exoticImNuLeR_avoids_triplets

theorem exoticImNuLeR_factor_CC (i j : I32) (h : exoticImNuLeR i j ≠ 0) :
    (genCVal j - genCVal i) * (genCOpVal j - genCOpVal i) = 0 := by
  rcases exoticImNuLeR_supp i j h with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]

theorem exoticImNuLeR_oo_C_C :
    (exoticImNuLeR * genC - genC * exoticImNuLeR) * smGenOp 0
      - smGenOp 0 * (exoticImNuLeR * genC - genC * exoticImNuLeR) = 0 :=
  oo_C_C_of_factor exoticImNuLeR exoticImNuLeR_factor_CC

/-! ## Phase 2c infrastructure: colour-triplet commutation -/

/-- The `t = 0` colour triplet is exactly `{18, 20, 22}`. -/
theorem triplet_cover_T0 : ∀ x : I32, ∀ q : Fin 3,
    tripletOf x.val = some (0, q) → x = ![18, 20, 22] q := by
  decide

/-- The `t = 3` colour triplet is exactly `{27, 29, 31}`. -/
theorem triplet_cover_T3 : ∀ x : I32, ∀ q : Fin 3,
    tripletOf x.val = some (3, q) → x = ![27, 29, 31] q := by
  decide

/-- The `t = 1` colour triplet is exactly `{19, 21, 23}`. -/
theorem triplet_cover_T1 : ∀ x : I32, ∀ q : Fin 3,
    tripletOf x.val = some (1, q) → x = ![19, 21, 23] q := by
  decide

/-- The `t = 2` colour triplet is exactly `{26, 28, 30}`. -/
theorem triplet_cover_T2 : ∀ x : I32, ∀ q : Fin 3,
    tripletOf x.val = some (2, q) → x = ![26, 28, 30] q := by
  decide

/-- Products of disjoint `if-then-zero` factors conjoin the conditions. -/
theorem ite_mul_ite_zero (c d : Prop) [Decidable c] [Decidable d] (a b : ℂ) :
    (if c then a else 0) * (if d then b else 0) = (if c ∧ d then a * b else 0) := by
  by_cases hc : c <;> by_cases hd : d <;> simp [hc, hd]

/-- A sum over `I32` of a function vanishing off two disjoint 3-element
    colour images collapses to the sum over the images. -/
theorem sum_over_color_image (f : I32 → ℂ) (A B : Fin 3 → I32)
    (hAinj : Function.Injective A) (hBinj : Function.Injective B)
    (hdisj : ∀ p q, A p ≠ B q)
    (hvan : ∀ l : I32, l ∉ Finset.image A Finset.univ ∪ Finset.image B Finset.univ → f l = 0) :
    ∑ l : I32, f l = ∑ p : Fin 3, (f (B p) + f (A p)) := by
  have hsub : Finset.image A Finset.univ ∪ Finset.image B Finset.univ ⊆ Finset.univ :=
    Finset.subset_univ _
  have hdisj' : Disjoint (Finset.image A Finset.univ) (Finset.image B Finset.univ) := by
    rw [Finset.disjoint_left]
    rintro l hAl hBl
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hAl
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hBl
    exact hdisj p q (hp.trans hq.symm)
  have hAinj' : ∀ x ∈ (Finset.univ : Finset (Fin 3)), ∀ y ∈ Finset.univ,
      A x = A y → x = y := fun p _ q _ h => hAinj h
  have hBinj' : ∀ x ∈ (Finset.univ : Finset (Fin 3)), ∀ y ∈ Finset.univ,
      B x = B y → x = y := fun p _ q _ h => hBinj h
  calc ∑ l : I32, f l
      = ∑ l ∈ Finset.image A Finset.univ ∪ Finset.image B Finset.univ, f l :=
        (Finset.sum_subset hsub (fun l _ hl => hvan l hl)).symm
    _ = (∑ l ∈ Finset.image A Finset.univ, f l)
        + (∑ l ∈ Finset.image B Finset.univ, f l) :=
        Finset.sum_union hdisj'
    _ = ∑ p : Fin 3, (f (B p) + f (A p)) := by
        have e1 : (∑ l ∈ Finset.image A Finset.univ, f l) = ∑ p : Fin 3, f (A p) :=
          Finset.sum_image hAinj'
        have e2 : (∑ l ∈ Finset.image B Finset.univ, f l) = ∑ p : Fin 3, f (B p) :=
          Finset.sum_image hBinj'
        rw [e1, e2, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun p _ => add_comm (f (A p)) (f (B p)))

/-- A colour-block generator's column at a triplet element expands over that triplet. -/
theorem G_expand (G : Matrix I32 I32 ℂ) (C : Fin 3 → I32) (tC : Fin 4)
    (F : Fin 3 → Fin 3 → ℂ)
    (hC : ∀ p, tripletOf (C p).val = some (tC, p))
    (hCinj : Function.Injective C)
    (hG : ∀ x y : I32, ∀ t : Fin 4, ∀ px py : Fin 3,
      tripletOf x.val = some (t, px) → tripletOf y.val = some (t, py) →
      G x y = F px py)
    (hG0 : ∀ x y : I32, G x y ≠ 0 →
      ∃ t : Fin 4, ∃ px py : Fin 3,
        tripletOf x.val = some (t, px) ∧ tripletOf y.val = some (t, py))
    (hcov : ∀ x : I32, ∀ q : Fin 3, tripletOf x.val = some (tC, q) → x = C q)
    (p : Fin 3) (z : I32) :
    G (C p) z = ∑ q : Fin 3, (if z = C q then F p q else 0) := by
  by_cases hj : ∃ q, z = C q
  · obtain ⟨q0, rfl⟩ := hj
    rw [hG (C p) (C q0) tC p q0 (hC p) (hC q0)]
    have heq : ∀ q : Fin 3, (if (C q0 : I32) = C q then F p q else (0:ℂ))
        = (if q = q0 then F p q else 0) := by
      intro q
      by_cases hqq : q = q0
      · subst hqq; simp
      · have hne : C q0 ≠ C q := fun h => hqq (hCinj h.symm)
        rw [if_neg hne, if_neg hqq]
    simp_rw [heq]
    rw [Finset.sum_ite_eq']
    simp
  · push_neg at hj
    have hLHS : G (C p) z = 0 := by
      by_contra hcon
      obtain ⟨t, px, py, htx, hty⟩ := hG0 (C p) z hcon
      rw [hC p] at htx
      have hteq : t = tC := by
        have e := Option.some_inj.mp htx
        rw [Prod.mk.injEq] at e
        exact e.1.symm
      subst hteq
      exact hj py (hcov z py hty)
    have hRHS : ∑ q : Fin 3, (if z = C q then F p q else (0:ℂ)) = 0 := by
      apply Finset.sum_eq_zero
      intro q _
      rw [if_neg (hj q)]
    rw [hLHS, hRHS]

/-- Row version: a colour-block generator's row at a triplet element. -/
theorem G_expand_row (G : Matrix I32 I32 ℂ) (C : Fin 3 → I32) (tC : Fin 4)
    (F : Fin 3 → Fin 3 → ℂ)
    (hC : ∀ p, tripletOf (C p).val = some (tC, p))
    (hCinj : Function.Injective C)
    (hG : ∀ x y : I32, ∀ t : Fin 4, ∀ px py : Fin 3,
      tripletOf x.val = some (t, px) → tripletOf y.val = some (t, py) →
      G x y = F px py)
    (hG0 : ∀ x y : I32, G x y ≠ 0 →
      ∃ t : Fin 4, ∃ px py : Fin 3,
        tripletOf x.val = some (t, px) ∧ tripletOf y.val = some (t, py))
    (hcov : ∀ x : I32, ∀ q : Fin 3, tripletOf x.val = some (tC, q) → x = C q)
    (p : Fin 3) (z : I32) :
    G z (C p) = ∑ q : Fin 3, (if z = C q then F q p else 0) := by
  by_cases hj : ∃ q, z = C q
  · obtain ⟨q0, rfl⟩ := hj
    rw [hG (C q0) (C p) tC q0 p (hC q0) (hC p)]
    have heq : ∀ q : Fin 3, (if (C q0 : I32) = C q then F q p else (0:ℂ))
        = (if q = q0 then F q p else 0) := by
      intro q
      by_cases hqq : q = q0
      · subst hqq; simp
      · have hne : C q0 ≠ C q := fun h => hqq (hCinj h.symm)
        rw [if_neg hne, if_neg hqq]
    simp_rw [heq]
    rw [Finset.sum_ite_eq']
    simp
  · push_neg at hj
    have hLHS : G z (C p) = 0 := by
      by_contra hcon
      obtain ⟨t, px, py, htx, hty⟩ := hG0 z (C p) hcon
      rw [hC p] at hty
      have hteq : t = tC := by
        have e := Option.some_inj.mp hty
        rw [Prod.mk.injEq] at e
        exact e.1.symm
      subst hteq
      exact hj px (hcov z px htx)
    have hRHS : ∑ q : Fin 3, (if z = C q then F q p else (0:ℂ)) = 0 := by
      apply Finset.sum_eq_zero
      intro q _
      rw [if_neg (hj q)]
    rw [hLHS, hRHS]

/-- Colour-universal commutation: `E` swaps two colour triplets `A ↔ B`
    with uniform values (`vAB`, `vBA`) plus non-triplet entries, while `G`
    acts as the same colour operator `F` inside each triplet.
    Then `E * G = G * E`.  (Quark-sector M-class.) -/
theorem color_universal_comm
    (E G : Matrix I32 I32 ℂ)
    (A B : Fin 3 → I32) (tA tB : Fin 4)
    (F : Fin 3 → Fin 3 → ℂ)
    (hA : ∀ p, tripletOf (A p).val = some (tA, p))
    (hB : ∀ p, tripletOf (B p).val = some (tB, p))
    (hne : tA ≠ tB)
    (hcovA : ∀ x : I32, ∀ q : Fin 3, tripletOf x.val = some (tA, q) → x = A q)
    (hcovB : ∀ x : I32, ∀ q : Fin 3, tripletOf x.val = some (tB, q) → x = B q)
    (hG : ∀ x y : I32, ∀ t : Fin 4, ∀ px py : Fin 3,
      tripletOf x.val = some (t, px) → tripletOf y.val = some (t, py) →
      G x y = F px py)
    (hG0 : ∀ x y : I32, G x y ≠ 0 →
      ∃ t : Fin 4, ∃ px py : Fin 3,
        tripletOf x.val = some (t, px) ∧ tripletOf y.val = some (t, py))
    (vAB vBA : ℂ)
    (hvalAB : ∀ p, E (A p) (B p) = vAB)
    (hvalBA : ∀ p, E (B p) (A p) = vBA)
    (hsupp : ∀ x y, E x y ≠ 0 →
      (∃ p, x = A p ∧ y = B p) ∨ (∃ p, x = B p ∧ y = A p) ∨
      (tripletOf x.val = none ∧ tripletOf y.val = none)) :
    E * G = G * E := by
  have hAinj : Function.Injective A := by
    intro p1 p2 h
    have e1 := hA p1
    rw [h] at e1
    rw [hA p2] at e1
    have e2 := Option.some_inj.mp e1
    rw [Prod.mk.injEq] at e2
    exact e2.2.symm
  have hBinj : Function.Injective B := by
    intro p1 p2 h
    have e1 := hB p1
    rw [h] at e1
    rw [hB p2] at e1
    have e2 := Option.some_inj.mp e1
    rw [Prod.mk.injEq] at e2
    exact e2.2.symm
  have hdisj : ∀ p q, A p ≠ B q := by
    intro p q h
    have e1 := hA p
    rw [h] at e1
    rw [hB q] at e1
    have e2 := Option.some_inj.mp e1
    rw [Prod.mk.injEq] at e2
    exact hne e2.1.symm
  -- E-value characterizations (column and row)
  ext i j
  simp only [Matrix.mul_apply]
  have hEcolB : ∀ p i, E i (B p) = if i = A p then vAB else 0 := by
    intro p i
    by_cases h : i = A p
    · subst h; rw [if_pos rfl]; exact hvalAB p
    · rw [if_neg h]
      by_contra hcon
      rcases hsupp i (B p) hcon with ⟨q, hq1, hq2⟩|⟨q, hq1, hq2⟩|⟨hx, hy⟩
      · have hpq : p = q := hBinj hq2
        subst hpq; exact h hq1
      · have e2 := hA q
        rw [← hq2, hB p] at e2
        have e3 := Option.some_inj.mp e2
        rw [Prod.mk.injEq] at e3
        exact hne e3.1.symm
      · rw [hB p] at hy; simp at hy
  have hEcolA : ∀ p i, E i (A p) = if i = B p then vBA else 0 := by
    intro p i
    by_cases h : i = B p
    · subst h; rw [if_pos rfl]; exact hvalBA p
    · rw [if_neg h]
      by_contra hcon
      rcases hsupp i (A p) hcon with ⟨q, hq1, hq2⟩|⟨q, hq1, hq2⟩|⟨hx, hy⟩
      · have e1 := hA p
        rw [hq2, hB q] at e1
        have e3 := Option.some_inj.mp e1
        rw [Prod.mk.injEq] at e3
        exact hne e3.1.symm
      · have hpq : p = q := hAinj hq2
        subst hpq; exact h hq1
      · rw [hA p] at hy; simp at hy
  have hErowB : ∀ p j, E (B p) j = if j = A p then vBA else 0 := by
    intro p j
    by_cases h : j = A p
    · subst h; rw [if_pos rfl]; exact hvalBA p
    · rw [if_neg h]
      by_contra hcon
      rcases hsupp (B p) j hcon with ⟨q, hq1, hq2⟩|⟨q, hq1, hq2⟩|⟨hx, hy⟩
      · have e1 := hB p
        rw [hq1, hA q] at e1
        have e3 := Option.some_inj.mp e1
        rw [Prod.mk.injEq] at e3
        exact hne e3.1
      · have hpq : p = q := hBinj hq1
        subst hpq; exact h hq2
      · rw [hB p] at hx; simp at hx
  have hErowA : ∀ p j, E (A p) j = if j = B p then vAB else 0 := by
    intro p j
    by_cases h : j = B p
    · subst h; rw [if_pos rfl]; exact hvalAB p
    · rw [if_neg h]
      by_contra hcon
      rcases hsupp (A p) j hcon with ⟨q, hq1, hq2⟩|⟨q, hq1, hq2⟩|⟨hx, hy⟩
      · have hpq : p = q := hAinj hq1
        subst hpq; exact h hq2
      · have e1 := hA p
        rw [hq1, hB q] at e1
        have e3 := Option.some_inj.mp e1
        rw [Prod.mk.injEq] at e3
        exact hne e3.1.symm
      · rw [hA p] at hx; simp at hx
  -- Vanishing off the colour images
  have van1 : ∀ i j l : I32, l ∉ Finset.image A Finset.univ ∪ Finset.image B Finset.univ →
      E i l * G l j = 0 := by
    intro i j l hl
    by_cases hEl : E i l = 0
    · rw [hEl, zero_mul]
    · have hG0' : G l j = 0 := by
        by_contra hcon
        obtain ⟨t, px, py, htx, hty⟩ := hG0 l j hcon
        rcases hsupp i l hEl with ⟨p, hp1, hp2⟩|⟨p, hp1, hp2⟩|⟨hx, hy⟩
        · exact hl (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, hp2.symm⟩))
        · exact hl (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, hp2.symm⟩))
        · simp [htx] at hy
      rw [hG0', mul_zero]
  have van2 : ∀ i j l : I32, l ∉ Finset.image A Finset.univ ∪ Finset.image B Finset.univ →
      G i l * E l j = 0 := by
    intro i j l hl
    by_cases hEl : E l j = 0
    · rw [hEl, mul_zero]
    · have hG0' : G i l = 0 := by
        by_contra hcon
        obtain ⟨t, px, py, htx, hty⟩ := hG0 i l hcon
        rcases hsupp l j hEl with ⟨p, hp1, hp2⟩|⟨p, hp1, hp2⟩|⟨hx, hy⟩
        · exact hl (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, hp1.symm⟩))
        · exact hl (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, hp1.symm⟩))
        · simp [hty] at hx
      rw [hG0', zero_mul]
  -- G column/row expansions
  have eBcol : ∀ p : Fin 3, G (B p) j = ∑ q : Fin 3, (if j = B q then F p q else (0:ℂ)) :=
    fun p => G_expand G B tB F hB hBinj hG hG0 hcovB p j
  have eAcol : ∀ p : Fin 3, G (A p) j = ∑ q : Fin 3, (if j = A q then F p q else (0:ℂ)) :=
    fun p => G_expand G A tA F hA hAinj hG hG0 hcovA p j
  have eBrow : ∀ p : Fin 3, G i (B p) = ∑ q : Fin 3, (if i = B q then F q p else (0:ℂ)) :=
    fun p => G_expand_row G B tB F hB hBinj hG hG0 hcovB p i
  have eArow : ∀ p : Fin 3, G i (A p) = ∑ q : Fin 3, (if i = A q then F q p else (0:ℂ)) :=
    fun p => G_expand_row G A tA F hA hAinj hG hG0 hcovA p i
  -- Collapse to double sums with conjoined conditions
  have hL : ∀ p : Fin 3,
      ((if i = A p then vAB else 0) * G (B p) j + (if i = B p then vBA else 0) * G (A p) j)
      = ∑ q : Fin 3, ((if i = A p ∧ j = B q then vAB * F p q else (0:ℂ))
          + (if i = B p ∧ j = A q then vBA * F p q else 0)) := by
    intro p
    rw [eBcol p, eAcol p, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [ite_mul_ite_zero, ite_mul_ite_zero]
  have hR : ∀ p : Fin 3,
      (G i (B p) * (if j = A p then vBA else 0) + G i (A p) * (if j = B p then vAB else 0))
      = ∑ q : Fin 3, ((if i = B q ∧ j = A p then F q p * vBA else (0:ℂ))
          + (if i = A q ∧ j = B p then F q p * vAB else 0)) := by
    intro p
    rw [eBrow p, eArow p, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [ite_mul_ite_zero, ite_mul_ite_zero]
  -- The two double sums agree (swap p ↔ q and commute)
  have hVU : ∀ p q : Fin 3,
      ((if i = B q ∧ j = A p then F q p * vBA else (0:ℂ))
        + (if i = A q ∧ j = B p then F q p * vAB else 0))
      = ((if i = A q ∧ j = B p then vAB * F q p else (0:ℂ))
        + (if i = B q ∧ j = A p then vBA * F q p else 0)) := by
    intro p q
    rw [add_comm ((if i = B q ∧ j = A p then F q p * vBA else (0:ℂ))) _]
    congr 1
    · by_cases hC : i = A q ∧ j = B p <;> simp [hC, mul_comm]
    · by_cases hC : i = B q ∧ j = A p <;> simp [hC, mul_comm]
  rw [sum_over_color_image (fun l => E i l * G l j) A B hAinj hBinj hdisj (van1 i j),
      sum_over_color_image (fun l => G i l * E l j) A B hAinj hBinj hdisj (van2 i j)]
  simp_rw [hEcolB, hEcolA, hErowB, hErowA, hL, hR]
  calc (∑ p : Fin 3, ∑ q : Fin 3, ((if i = A p ∧ j = B q then vAB * F p q else (0:ℂ))
          + (if i = B p ∧ j = A q then vBA * F p q else 0)))
      = (∑ q : Fin 3, ∑ p : Fin 3, ((if i = A q ∧ j = B p then vAB * F q p else (0:ℂ))
          + (if i = B q ∧ j = A p then vBA * F q p else 0))) := rfl
    _ = (∑ p : Fin 3, ∑ q : Fin 3, ((if i = A q ∧ j = B p then vAB * F q p else (0:ℂ))
          + (if i = B q ∧ j = A p then vBA * F q p else 0))) := Finset.sum_comm.symm
    _ = (∑ p : Fin 3, ∑ q : Fin 3, ((if i = B q ∧ j = A p then F q p * vBA else (0:ℂ))
          + (if i = A q ∧ j = B p then F q p * vAB else 0))) :=
        Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => (hVU p q).symm))

/-- J-conjugation transfers `[E, genM a] = 0` to `[E, M°_a] = 0`. -/
theorem comm_MOp_of_Jcompat (E : Matrix I32 I32 ℂ)
    (hJ : UJ * E.transpose * UJ = E)
    (a : Fin 8) (hcomm : E * genM a = genM a * E) :
    E * (UJ * (genM a).transpose * UJ) = (UJ * (genM a).transpose * UJ) * E := by
  have hU : UJ * UJ = 1 := UJ_mul_self
  have hT : (genM a).transpose * E.transpose = E.transpose * (genM a).transpose := by
    have h := congrArg Matrix.transpose hcomm
    simpa [Matrix.transpose_mul] using h
  have e1 : (UJ * (genM a).transpose * UJ) * (UJ * E.transpose * UJ)
      = UJ * ((genM a).transpose * E.transpose) * UJ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc UJ UJ (E.transpose * UJ), hU, Matrix.one_mul]
  have e2 : (UJ * E.transpose * UJ) * (UJ * (genM a).transpose * UJ)
      = UJ * (E.transpose * (genM a).transpose) * UJ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc UJ UJ ((genM a).transpose * UJ), hU, Matrix.one_mul]
  have key : (UJ * (genM a).transpose * UJ) * (UJ * E.transpose * UJ)
      = (UJ * E.transpose * UJ) * (UJ * (genM a).transpose * UJ) := by
    rw [e1, e2, hT]
  rw [hJ] at key
  exact key.symm

/-- Jacobi-style: `[[E,P],Q] = 0` from `[E,Q] = 0` and `[P,Q] = 0`. -/
theorem double_comm_of_comm (E P Q : Matrix I32 I32 ℂ)
    (hEQ : E * Q = Q * E) (hPQ : P * Q = Q * P) :
    (E * P - P * E) * Q - Q * (E * P - P * E) = 0 := by
  have h1 : (E * P) * Q = Q * (E * P) := by
    calc (E * P) * Q = E * (P * Q) := by rw [Matrix.mul_assoc]
    _ = E * (Q * P) := by rw [hPQ]
    _ = (E * Q) * P := by rw [← Matrix.mul_assoc]
    _ = (Q * E) * P := by rw [hEQ]
    _ = Q * (E * P) := by rw [Matrix.mul_assoc]
  have h2 : (P * E) * Q = Q * (P * E) := by
    calc (P * E) * Q = P * (E * Q) := by rw [Matrix.mul_assoc]
    _ = P * (Q * E) := by rw [hEQ]
    _ = (P * Q) * E := by rw [← Matrix.mul_assoc]
    _ = (Q * P) * E := by rw [hPQ]
    _ = Q * (P * E) := by rw [Matrix.mul_assoc]
  have h3 : (E * P - P * E) * Q = Q * (E * P) - Q * (P * E) := by
    rw [Matrix.sub_mul, h1, h2]
  have h4 : Q * (E * P - P * E) = Q * (E * P) - Q * (P * E) := by
    rw [Matrix.mul_sub]
  rw [h3, h4, sub_self]

/-- Order-zero transfer: `[genC, M°_b] = 0` from `smGen_order_zero`. -/
theorem comm_genC_MOp (b : Fin 8) :
    genC * (UJ * (genM b).transpose * UJ)
      = (UJ * (genM b).transpose * UJ) * genC := by
  have hb : smGenOp (⟨4 + b.val, by have hb := b.isLt; omega⟩ : Fin 12)
      = UJ * (genM b).transpose * UJ := by
    fin_cases b <;> rfl
  have h := smGen_order_zero 0 ⟨4 + b.val, by have hb := b.isLt; omega⟩
  rw [smGen_zero_eq, hb] at h
  exact sub_eq_zero.mp h

/-- Order-zero transfer: `[genH k, M°_b] = 0` from `smGen_order_zero`. -/
theorem comm_genH_MOp (k : Fin 3) (b : Fin 8) :
    genH k * (UJ * (genM b).transpose * UJ)
      = (UJ * (genM b).transpose * UJ) * genH k := by
  have hk : smGen (⟨1 + k.val, by have hk := k.isLt; omega⟩ : Fin 12) = genH k := by
    fin_cases k <;> rfl
  have hb : smGenOp (⟨4 + b.val, by have hb := b.isLt; omega⟩ : Fin 12)
      = UJ * (genM b).transpose * UJ := by
    fin_cases b <;> rfl
  have h := smGen_order_zero ⟨1 + k.val, by have hk := k.isLt; omega⟩
    ⟨4 + b.val, by have hb := b.isLt; omega⟩
  rw [hk, hb] at h
  exact sub_eq_zero.mp h



/-! ## M-class: commutation with genM -/

theorem exoticReULDR_comm_genM (a : Fin 8) :
    exoticReULDR * genM a = genM a * exoticReULDR := by
  apply color_universal_comm exoticReULDR (genM a)
    (((![18, 20, 22] : Fin 3 → I32))) (((![27, 29, 31] : Fin 3 → I32)))
    0 3 (fun px py => gellMann a px py)
  · decide
  · decide
  · decide
  · exact triplet_cover_T0
  · exact triplet_cover_T3
  · exact (fun x y t px py hx hy => genM_apply_eq a x y t px py hx hy)
  · exact (fun x y h => genM_supp_triplet a x y h)
  · intro p; fin_cases p <;> rfl
  · intro p; fin_cases p <;> rfl
  · intro x y hne
    have hC : (x = 2 ∧ y = 11) ∨ (x = 11 ∧ y = 2) ∨ (x = 4 ∧ y = 13) ∨ (x = 13 ∧ y = 4) ∨ (x = 6 ∧ y = 15) ∨ (x = 15 ∧ y = 6) ∨ (x = 18 ∧ y = 27) ∨ (x = 27 ∧ y = 18) ∨ (x = 20 ∧ y = 29) ∨ (x = 29 ∧ y = 20) ∨ (x = 22 ∧ y = 31) ∨ (x = 31 ∧ y = 22) := by
      by_cases hCc : (x = 2 ∧ y = 11) ∨ (x = 11 ∧ y = 2) ∨ (x = 4 ∧ y = 13) ∨ (x = 13 ∧ y = 4) ∨ (x = 6 ∧ y = 15) ∨ (x = 15 ∧ y = 6) ∨ (x = 18 ∧ y = 27) ∨ (x = 27 ∧ y = 18) ∨ (x = 20 ∧ y = 29) ∨ (x = 29 ∧ y = 20) ∨ (x = 22 ∧ y = 31) ∨ (x = 31 ∧ y = 22)
      · exact hCc
      · exfalso
        have hif : (if (x = 2 ∧ y = 11) ∨ (x = 11 ∧ y = 2) ∨ (x = 4 ∧ y = 13) ∨ (x = 13 ∧ y = 4) ∨ (x = 6 ∧ y = 15) ∨ (x = 15 ∧ y = 6) ∨ (x = 18 ∧ y = 27) ∨ (x = 27 ∧ y = 18) ∨ (x = 20 ∧ y = 29) ∨ (x = 29 ∧ y = 20) ∨ (x = 22 ∧ y = 31) ∨ (x = 31 ∧ y = 22) then (1:ℂ) else 0) = 0 := if_neg hCc
        simp only [exoticReULDR] at hne
        rw [hif] at hne
        exact hne rfl
    rcases hC with ⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩
    · right; right; exact ⟨by decide, by decide⟩
    · right; right; exact ⟨by decide, by decide⟩
    · right; right; exact ⟨by decide, by decide⟩
    · right; right; exact ⟨by decide, by decide⟩
    · right; right; exact ⟨by decide, by decide⟩
    · right; right; exact ⟨by decide, by decide⟩
    · left; exact ⟨0, rfl, rfl⟩
    · right; left; exact ⟨0, rfl, rfl⟩
    · left; exact ⟨1, rfl, rfl⟩
    · right; left; exact ⟨1, rfl, rfl⟩
    · left; exact ⟨2, rfl, rfl⟩
    · right; left; exact ⟨2, rfl, rfl⟩


theorem exoticReDLUR_comm_genM (a : Fin 8) :
    exoticReDLUR * genM a = genM a * exoticReDLUR := by
  apply color_universal_comm exoticReDLUR (genM a)
    (((![19, 21, 23] : Fin 3 → I32))) (((![26, 28, 30] : Fin 3 → I32)))
    1 2 (fun px py => gellMann a px py)
  · decide
  · decide
  · decide
  · exact triplet_cover_T1
  · exact triplet_cover_T2
  · exact (fun x y t px py hx hy => genM_apply_eq a x y t px py hx hy)
  · exact (fun x y h => genM_supp_triplet a x y h)
  · intro p; fin_cases p <;> rfl
  · intro p; fin_cases p <;> rfl
  · intro x y hne
    have hC : (x = 3 ∧ y = 10) ∨ (x = 10 ∧ y = 3) ∨ (x = 5 ∧ y = 12) ∨ (x = 12 ∧ y = 5) ∨ (x = 7 ∧ y = 14) ∨ (x = 14 ∧ y = 7) ∨ (x = 19 ∧ y = 26) ∨ (x = 26 ∧ y = 19) ∨ (x = 21 ∧ y = 28) ∨ (x = 28 ∧ y = 21) ∨ (x = 23 ∧ y = 30) ∨ (x = 30 ∧ y = 23) := by
      by_cases hCc : (x = 3 ∧ y = 10) ∨ (x = 10 ∧ y = 3) ∨ (x = 5 ∧ y = 12) ∨ (x = 12 ∧ y = 5) ∨ (x = 7 ∧ y = 14) ∨ (x = 14 ∧ y = 7) ∨ (x = 19 ∧ y = 26) ∨ (x = 26 ∧ y = 19) ∨ (x = 21 ∧ y = 28) ∨ (x = 28 ∧ y = 21) ∨ (x = 23 ∧ y = 30) ∨ (x = 30 ∧ y = 23)
      · exact hCc
      · exfalso
        have hif : (if (x = 3 ∧ y = 10) ∨ (x = 10 ∧ y = 3) ∨ (x = 5 ∧ y = 12) ∨ (x = 12 ∧ y = 5) ∨ (x = 7 ∧ y = 14) ∨ (x = 14 ∧ y = 7) ∨ (x = 19 ∧ y = 26) ∨ (x = 26 ∧ y = 19) ∨ (x = 21 ∧ y = 28) ∨ (x = 28 ∧ y = 21) ∨ (x = 23 ∧ y = 30) ∨ (x = 30 ∧ y = 23) then (1:ℂ) else 0) = 0 := if_neg hCc
        simp only [exoticReDLUR] at hne
        rw [hif] at hne
        exact hne rfl
    rcases hC with ⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩
    · right; right; exact ⟨by decide, by decide⟩
    · right; right; exact ⟨by decide, by decide⟩
    · right; right; exact ⟨by decide, by decide⟩
    · right; right; exact ⟨by decide, by decide⟩
    · right; right; exact ⟨by decide, by decide⟩
    · right; right; exact ⟨by decide, by decide⟩
    · left; exact ⟨0, rfl, rfl⟩
    · right; left; exact ⟨0, rfl, rfl⟩
    · left; exact ⟨1, rfl, rfl⟩
    · right; left; exact ⟨1, rfl, rfl⟩
    · left; exact ⟨2, rfl, rfl⟩
    · right; left; exact ⟨2, rfl, rfl⟩


theorem exoticImULDR_comm_genM (a : Fin 8) :
    exoticImULDR * genM a = genM a * exoticImULDR := by
  apply color_universal_comm exoticImULDR (genM a)
    (((![18, 20, 22] : Fin 3 → I32))) (((![27, 29, 31] : Fin 3 → I32)))
    0 3 (fun px py => gellMann a px py)
  · decide
  · decide
  · decide
  · exact triplet_cover_T0
  · exact triplet_cover_T3
  · exact (fun x y t px py hx hy => genM_apply_eq a x y t px py hx hy)
  · exact (fun x y h => genM_supp_triplet a x y h)
  · intro p; fin_cases p <;> rfl
  · intro p; fin_cases p <;> rfl
  · intro x y hne
    have hC : ((x = 2 ∧ y = 11) ∨ (x = 4 ∧ y = 13) ∨ (x = 6 ∧ y = 15) ∨ (x = 27 ∧ y = 18) ∨ (x = 29 ∧ y = 20) ∨ (x = 31 ∧ y = 22)) ∨ ((x = 11 ∧ y = 2) ∨ (x = 13 ∧ y = 4) ∨ (x = 15 ∧ y = 6) ∨ (x = 18 ∧ y = 27) ∨ (x = 20 ∧ y = 29) ∨ (x = 22 ∧ y = 31)) := by
      by_cases hCc : ((x = 2 ∧ y = 11) ∨ (x = 4 ∧ y = 13) ∨ (x = 6 ∧ y = 15) ∨ (x = 27 ∧ y = 18) ∨ (x = 29 ∧ y = 20) ∨ (x = 31 ∧ y = 22)) ∨ ((x = 11 ∧ y = 2) ∨ (x = 13 ∧ y = 4) ∨ (x = 15 ∧ y = 6) ∨ (x = 18 ∧ y = 27) ∨ (x = 20 ∧ y = 29) ∨ (x = 22 ∧ y = 31))
      · exact hCc
      · exfalso
        have hC1n : ¬((x = 2 ∧ y = 11) ∨ (x = 4 ∧ y = 13) ∨ (x = 6 ∧ y = 15) ∨ (x = 27 ∧ y = 18) ∨ (x = 29 ∧ y = 20) ∨ (x = 31 ∧ y = 22)) := fun h => hCc (Or.inl h)
        have hC2n : ¬((x = 11 ∧ y = 2) ∨ (x = 13 ∧ y = 4) ∨ (x = 15 ∧ y = 6) ∨ (x = 18 ∧ y = 27) ∨ (x = 20 ∧ y = 29) ∨ (x = 22 ∧ y = 31)) := fun h => hCc (Or.inr h)
        have hE0 : exoticImULDR x y = 0 := by
          simp only [exoticImULDR, if_neg hC1n, if_neg hC2n]
        exact hne hE0
    rcases hC with hC1|hC2
    · rcases hC1 with ⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩
      · right; right; exact ⟨by decide, by decide⟩
      · right; right; exact ⟨by decide, by decide⟩
      · right; right; exact ⟨by decide, by decide⟩
      · right; left; exact ⟨0, rfl, rfl⟩
      · right; left; exact ⟨1, rfl, rfl⟩
      · right; left; exact ⟨2, rfl, rfl⟩
    · rcases hC2 with ⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩
      · right; right; exact ⟨by decide, by decide⟩
      · right; right; exact ⟨by decide, by decide⟩
      · right; right; exact ⟨by decide, by decide⟩
      · left; exact ⟨0, rfl, rfl⟩
      · left; exact ⟨1, rfl, rfl⟩
      · left; exact ⟨2, rfl, rfl⟩


theorem exoticImDLUR_comm_genM (a : Fin 8) :
    exoticImDLUR * genM a = genM a * exoticImDLUR := by
  apply color_universal_comm exoticImDLUR (genM a)
    (((![19, 21, 23] : Fin 3 → I32))) (((![26, 28, 30] : Fin 3 → I32)))
    1 2 (fun px py => gellMann a px py)
  · decide
  · decide
  · decide
  · exact triplet_cover_T1
  · exact triplet_cover_T2
  · exact (fun x y t px py hx hy => genM_apply_eq a x y t px py hx hy)
  · exact (fun x y h => genM_supp_triplet a x y h)
  · intro p; fin_cases p <;> rfl
  · intro p; fin_cases p <;> rfl
  · intro x y hne
    have hC : ((x = 3 ∧ y = 10) ∨ (x = 5 ∧ y = 12) ∨ (x = 7 ∧ y = 14) ∨ (x = 26 ∧ y = 19) ∨ (x = 28 ∧ y = 21) ∨ (x = 30 ∧ y = 23)) ∨ ((x = 10 ∧ y = 3) ∨ (x = 12 ∧ y = 5) ∨ (x = 14 ∧ y = 7) ∨ (x = 19 ∧ y = 26) ∨ (x = 21 ∧ y = 28) ∨ (x = 23 ∧ y = 30)) := by
      by_cases hCc : ((x = 3 ∧ y = 10) ∨ (x = 5 ∧ y = 12) ∨ (x = 7 ∧ y = 14) ∨ (x = 26 ∧ y = 19) ∨ (x = 28 ∧ y = 21) ∨ (x = 30 ∧ y = 23)) ∨ ((x = 10 ∧ y = 3) ∨ (x = 12 ∧ y = 5) ∨ (x = 14 ∧ y = 7) ∨ (x = 19 ∧ y = 26) ∨ (x = 21 ∧ y = 28) ∨ (x = 23 ∧ y = 30))
      · exact hCc
      · exfalso
        have hC1n : ¬((x = 3 ∧ y = 10) ∨ (x = 5 ∧ y = 12) ∨ (x = 7 ∧ y = 14) ∨ (x = 26 ∧ y = 19) ∨ (x = 28 ∧ y = 21) ∨ (x = 30 ∧ y = 23)) := fun h => hCc (Or.inl h)
        have hC2n : ¬((x = 10 ∧ y = 3) ∨ (x = 12 ∧ y = 5) ∨ (x = 14 ∧ y = 7) ∨ (x = 19 ∧ y = 26) ∨ (x = 21 ∧ y = 28) ∨ (x = 23 ∧ y = 30)) := fun h => hCc (Or.inr h)
        have hE0 : exoticImDLUR x y = 0 := by
          simp only [exoticImDLUR, if_neg hC1n, if_neg hC2n]
        exact hne hE0
    rcases hC with hC1|hC2
    · rcases hC1 with ⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩
      · right; right; exact ⟨by decide, by decide⟩
      · right; right; exact ⟨by decide, by decide⟩
      · right; right; exact ⟨by decide, by decide⟩
      · right; left; exact ⟨0, rfl, rfl⟩
      · right; left; exact ⟨1, rfl, rfl⟩
      · right; left; exact ⟨2, rfl, rfl⟩
    · rcases hC2 with ⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩
      · right; right; exact ⟨by decide, by decide⟩
      · right; right; exact ⟨by decide, by decide⟩
      · right; right; exact ⟨by decide, by decide⟩
      · left; exact ⟨0, rfl, rfl⟩
      · left; exact ⟨1, rfl, rfl⟩
      · left; exact ⟨2, rfl, rfl⟩


theorem exoticReELNuR_comm_genM (a : Fin 8) :
    exoticReELNuR * genM a = genM a * exoticReELNuR := by
  apply comm_genM_of_avoids
  intro x y hne
  have hC : (x = 1 ∧ y = 8) ∨ (x = 8 ∧ y = 1) ∨ (x = 17 ∧ y = 24) ∨ (x = 24 ∧ y = 17) := by
    by_cases hCc : (x = 1 ∧ y = 8) ∨ (x = 8 ∧ y = 1) ∨ (x = 17 ∧ y = 24) ∨ (x = 24 ∧ y = 17)
    · exact hCc
    · exfalso
      have hif : (if (x = 1 ∧ y = 8) ∨ (x = 8 ∧ y = 1) ∨ (x = 17 ∧ y = 24) ∨ (x = 24 ∧ y = 17) then (1:ℂ) else 0) = 0 := if_neg hCc
      simp only [exoticReELNuR] at hne
      rw [hif] at hne
      exact hne rfl
  rcases hC with ⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩


theorem exoticReNuREbarR_comm_genM (a : Fin 8) :
    exoticReNuREbarR * genM a = genM a * exoticReNuREbarR := by
  apply comm_genM_of_avoids
  intro x y hne
  have hC : (x = 8 ∧ y = 25) ∨ (x = 25 ∧ y = 8) ∨ (x = 24 ∧ y = 9) ∨ (x = 9 ∧ y = 24) := by
    by_cases hCc : (x = 8 ∧ y = 25) ∨ (x = 25 ∧ y = 8) ∨ (x = 24 ∧ y = 9) ∨ (x = 9 ∧ y = 24)
    · exact hCc
    · exfalso
      have hif : (if (x = 8 ∧ y = 25) ∨ (x = 25 ∧ y = 8) ∨ (x = 24 ∧ y = 9) ∨ (x = 9 ∧ y = 24) then (1:ℂ) else 0) = 0 := if_neg hCc
      simp only [exoticReNuREbarR] at hne
      rw [hif] at hne
      exact hne rfl
  rcases hC with ⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩


theorem exoticReEREbarR_comm_genM (a : Fin 8) :
    exoticReEREbarR * genM a = genM a * exoticReEREbarR := by
  apply comm_genM_of_avoids
  intro x y hne
  have hC : (x = 9 ∧ y = 25) ∨ (x = 25 ∧ y = 9) := by
    by_cases hCc : (x = 9 ∧ y = 25) ∨ (x = 25 ∧ y = 9)
    · exact hCc
    · exfalso
      have hif : (if (x = 9 ∧ y = 25) ∨ (x = 25 ∧ y = 9) then (1:ℂ) else 0) = 0 := if_neg hCc
      simp only [exoticReEREbarR] at hne
      rw [hif] at hne
      exact hne rfl
  rcases hC with ⟨rfl, rfl⟩|⟨rfl, rfl⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩


theorem exoticImELNuR_comm_genM (a : Fin 8) :
    exoticImELNuR * genM a = genM a * exoticImELNuR := by
  apply comm_genM_of_avoids
  intro x y hne
  have hC : ((x = 1 ∧ y = 8) ∨ (x = 24 ∧ y = 17)) ∨ ((x = 8 ∧ y = 1) ∨ (x = 17 ∧ y = 24)) := by
    by_cases hCc : ((x = 1 ∧ y = 8) ∨ (x = 24 ∧ y = 17)) ∨ ((x = 8 ∧ y = 1) ∨ (x = 17 ∧ y = 24))
    · exact hCc
    · exfalso
      have hC1n : ¬((x = 1 ∧ y = 8) ∨ (x = 24 ∧ y = 17)) := fun h => hCc (Or.inl h)
      have hC2n : ¬((x = 8 ∧ y = 1) ∨ (x = 17 ∧ y = 24)) := fun h => hCc (Or.inr h)
      have hE0 : exoticImELNuR x y = 0 := by
        simp only [exoticImELNuR, if_neg hC1n, if_neg hC2n]
      exact hne hE0
  rcases hC with hC1|hC2
  · rcases hC1 with ⟨rfl, rfl⟩|⟨rfl, rfl⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
  · rcases hC2 with ⟨rfl, rfl⟩|⟨rfl, rfl⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩


theorem exoticImNuREbarR_comm_genM (a : Fin 8) :
    exoticImNuREbarR * genM a = genM a * exoticImNuREbarR := by
  apply comm_genM_of_avoids
  intro x y hne
  have hC : ((x = 8 ∧ y = 25) ∨ (x = 9 ∧ y = 24)) ∨ ((x = 25 ∧ y = 8) ∨ (x = 24 ∧ y = 9)) := by
    by_cases hCc : ((x = 8 ∧ y = 25) ∨ (x = 9 ∧ y = 24)) ∨ ((x = 25 ∧ y = 8) ∨ (x = 24 ∧ y = 9))
    · exact hCc
    · exfalso
      have hC1n : ¬((x = 8 ∧ y = 25) ∨ (x = 9 ∧ y = 24)) := fun h => hCc (Or.inl h)
      have hC2n : ¬((x = 25 ∧ y = 8) ∨ (x = 24 ∧ y = 9)) := fun h => hCc (Or.inr h)
      have hE0 : exoticImNuREbarR x y = 0 := by
        simp only [exoticImNuREbarR, if_neg hC1n, if_neg hC2n]
      exact hne hE0
  rcases hC with hC1|hC2
  · rcases hC1 with ⟨rfl, rfl⟩|⟨rfl, rfl⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
  · rcases hC2 with ⟨rfl, rfl⟩|⟨rfl, rfl⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩


theorem exoticImEREbarR_comm_genM (a : Fin 8) :
    exoticImEREbarR * genM a = genM a * exoticImEREbarR := by
  apply comm_genM_of_avoids
  intro x y hne
  have hC : ((x = 9 ∧ y = 25)) ∨ ((x = 25 ∧ y = 9)) := by
    by_cases hCc : ((x = 9 ∧ y = 25)) ∨ ((x = 25 ∧ y = 9))
    · exact hCc
    · exfalso
      have hC1n : ¬((x = 9 ∧ y = 25)) := fun h => hCc (Or.inl h)
      have hC2n : ¬((x = 25 ∧ y = 9)) := fun h => hCc (Or.inr h)
      have hE0 : exoticImEREbarR x y = 0 := by
        simp only [exoticImEREbarR, if_neg hC1n, if_neg hC2n]
      exact hne hE0
  rcases hC with hC1|hC2
  · rcases hC1 with ⟨rfl, rfl⟩
    · exact ⟨by decide, by decide⟩
  · rcases hC2 with ⟨rfl, rfl⟩
    · exact ⟨by decide, by decide⟩



/-! ## MOp-class: commutation with opposite genM -/

theorem exoticReULDR_comm_MOp (a : Fin 8) :
    exoticReULDR * (UJ * (genM a).transpose * UJ) = (UJ * (genM a).transpose * UJ) * exoticReULDR :=
  comm_MOp_of_Jcompat exoticReULDR exoticReULDR_Jcompat a (exoticReULDR_comm_genM a)

theorem exoticReDLUR_comm_MOp (a : Fin 8) :
    exoticReDLUR * (UJ * (genM a).transpose * UJ) = (UJ * (genM a).transpose * UJ) * exoticReDLUR :=
  comm_MOp_of_Jcompat exoticReDLUR exoticReDLUR_Jcompat a (exoticReDLUR_comm_genM a)

theorem exoticImULDR_comm_MOp (a : Fin 8) :
    exoticImULDR * (UJ * (genM a).transpose * UJ) = (UJ * (genM a).transpose * UJ) * exoticImULDR :=
  comm_MOp_of_Jcompat exoticImULDR exoticImULDR_Jcompat a (exoticImULDR_comm_genM a)

theorem exoticImDLUR_comm_MOp (a : Fin 8) :
    exoticImDLUR * (UJ * (genM a).transpose * UJ) = (UJ * (genM a).transpose * UJ) * exoticImDLUR :=
  comm_MOp_of_Jcompat exoticImDLUR exoticImDLUR_Jcompat a (exoticImDLUR_comm_genM a)

theorem exoticReELNuR_comm_MOp (a : Fin 8) :
    exoticReELNuR * (UJ * (genM a).transpose * UJ) = (UJ * (genM a).transpose * UJ) * exoticReELNuR :=
  comm_MOp_of_Jcompat exoticReELNuR exoticReELNuR_Jcompat a (exoticReELNuR_comm_genM a)

theorem exoticReNuREbarR_comm_MOp (a : Fin 8) :
    exoticReNuREbarR * (UJ * (genM a).transpose * UJ) = (UJ * (genM a).transpose * UJ) * exoticReNuREbarR :=
  comm_MOp_of_Jcompat exoticReNuREbarR exoticReNuREbarR_Jcompat a (exoticReNuREbarR_comm_genM a)

theorem exoticReEREbarR_comm_MOp (a : Fin 8) :
    exoticReEREbarR * (UJ * (genM a).transpose * UJ) = (UJ * (genM a).transpose * UJ) * exoticReEREbarR :=
  comm_MOp_of_Jcompat exoticReEREbarR exoticReEREbarR_Jcompat a (exoticReEREbarR_comm_genM a)

theorem exoticImNuLeR_comm_MOp (a : Fin 8) :
    exoticImNuLeR * (UJ * (genM a).transpose * UJ) = (UJ * (genM a).transpose * UJ) * exoticImNuLeR :=
  comm_MOp_of_Jcompat exoticImNuLeR exoticImNuLeR_Jcompat a (exoticImNuLeR_comm_genM a)

theorem exoticImELNuR_comm_MOp (a : Fin 8) :
    exoticImELNuR * (UJ * (genM a).transpose * UJ) = (UJ * (genM a).transpose * UJ) * exoticImELNuR :=
  comm_MOp_of_Jcompat exoticImELNuR exoticImELNuR_Jcompat a (exoticImELNuR_comm_genM a)

theorem exoticImNuREbarR_comm_MOp (a : Fin 8) :
    exoticImNuREbarR * (UJ * (genM a).transpose * UJ) = (UJ * (genM a).transpose * UJ) * exoticImNuREbarR :=
  comm_MOp_of_Jcompat exoticImNuREbarR exoticImNuREbarR_Jcompat a (exoticImNuREbarR_comm_genM a)

theorem exoticImEREbarR_comm_MOp (a : Fin 8) :
    exoticImEREbarR * (UJ * (genM a).transpose * UJ) = (UJ * (genM a).transpose * UJ) * exoticImEREbarR :=
  comm_MOp_of_Jcompat exoticImEREbarR exoticImEREbarR_Jcompat a (exoticImEREbarR_comm_genM a)

-- ============================================================================
-- ============================================================================
-- ============================================================================
-- ============================================================================
-- ============================================================================
-- ============================================================================
-- Phase 2c generic helpers (trivial C/H classes)
-- ============================================================================

/-- If `genCVal` is constant on `E`'s support, `[E, genC] = 0`. -/
theorem comm_genC_of_CVal_const (E : Matrix I32 I32 ℂ)
    (hE : ∀ x y, E x y ≠ 0 → genCVal x = genCVal y) :
    E * genC = genC * E := by
  ext i j
  have hsub : (E * genC - genC * E) i j = 0 := by
    rw [comm_diag_entry E genCVal genC (fun x y => genC_eq_diag x y) i j]
    rcases eq_or_ne (E i j) 0 with h0 | h0
    · rw [h0, zero_mul]
    · have hcc : genCVal j - genCVal i = 0 := by
        have h2 := hE i j h0
        rw [h2, sub_self]
      rw [hcc, mul_zero]
  rw [Matrix.sub_apply] at hsub
  exact sub_eq_zero.mp hsub

/-- If `E`'s support lies at indices ≥ 8, `[E, genH k] = 0`
    (genH is supported on 0–7). -/
theorem comm_genH_of_ge8 (E : Matrix I32 I32 ℂ)
    (hE : ∀ x y, E x y ≠ 0 → 8 ≤ x.val ∧ 8 ≤ y.val) (k : Fin 3) :
    E * genH k = genH k * E := by
  ext i j
  simp only [Matrix.mul_apply]
  have h1 : ∑ l : I32, E i l * genH k l j = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    by_cases hEl : E i l = 0
    · rw [hEl, zero_mul]
    · have hG : genH k l j = 0 := by
        by_contra hG'
        have hs := genH_supp k l j hG'
        have h8 := (hE i l hEl).2
        omega
      rw [hG, mul_zero]
  have h2 : ∑ l : I32, genH k i l * E l j = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    by_cases hGl : genH k i l = 0
    · rw [hGl, zero_mul]
    · have hE0 : E l j = 0 := by
        by_contra hE'
        have hs := genH_supp k i l hGl
        have h8 := (hE l j hE').1
        omega
      rw [hE0, mul_zero]
  rw [h1, h2]


-- ============================================================================
-- exoticImNuLeR : order-one
-- ============================================================================

theorem exoticImNuLeR_comm_genC_mem (i j : I32)
    (h : (exoticImNuLeR * genC - genC * exoticImNuLeR) i j ≠ 0) :
    (i = 0 ∨ i = 9) ∧ (j = 0 ∨ j = 9) := by
  rw [comm_diag_entry _ _ _ (fun x y => genC_eq_diag x y) i j] at h
  have hE : exoticImNuLeR i j ≠ 0 := by
    intro h0; apply h; rw [h0, zero_mul]
  have hc : genCVal j - genCVal i ≠ 0 := by
    intro h0; apply h; rw [h0, mul_zero]
  rcases exoticImNuLeR_supp i j hE with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy] at hc; simp [genCVal] at hc

theorem exoticImNuLeR_not_mem_RC_of_ge16 {x : I32} (h : 16 ≤ x.val) :
    x ∉ ({0, 9} : Finset I32) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_⟩
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h

theorem exoticImNuLeR_oo_C_H (k : Fin 3) :
    (exoticImNuLeR * genC - genC * exoticImNuLeR) * (UJ * (genH k).transpose * UJ)
      - (UJ * (genH k).transpose * UJ) * (exoticImNuLeR * genC - genC * exoticImNuLeR) = 0 := by
  apply oo_disjoint _ _ _ {0, 9}
  · intro i j hij
    obtain ⟨hi, hj⟩ := exoticImNuLeR_comm_genC_mem i j hij
    constructor
    · simp only [Finset.mem_insert, Finset.mem_singleton]; exact hi
    · simp only [Finset.mem_insert, Finset.mem_singleton]; exact hj
  · intro x y hxy
    have hsupp := UJ_genH_transpose_UJ_supp k x y hxy
    exact ⟨exoticImNuLeR_not_mem_RC_of_ge16 hsupp.1, exoticImNuLeR_not_mem_RC_of_ge16 hsupp.2.2.1⟩

theorem exoticImNuLeR_oo_C_M (a : Fin 8) :
    (exoticImNuLeR * genC - genC * exoticImNuLeR) * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ) * (exoticImNuLeR * genC - genC * exoticImNuLeR) = 0 :=
  double_comm_of_comm exoticImNuLeR genC _ (exoticImNuLeR_comm_MOp a) (comm_genC_MOp a)

theorem exoticImNuLeR_oo_C (g2 : Fin 12) :
    (exoticImNuLeR * genC - genC * exoticImNuLeR) * smGenOp g2
      - smGenOp g2 * (exoticImNuLeR * genC - genC * exoticImNuLeR) = 0 := by
  fin_cases g2
  · exact exoticImNuLeR_oo_C_C
  · show (exoticImNuLeR * genC - genC * exoticImNuLeR) * (UJ * (genH 0).transpose * UJ)
        - (UJ * (genH 0).transpose * UJ) * (exoticImNuLeR * genC - genC * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_C_H 0
  · show (exoticImNuLeR * genC - genC * exoticImNuLeR) * (UJ * (genH 1).transpose * UJ)
        - (UJ * (genH 1).transpose * UJ) * (exoticImNuLeR * genC - genC * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_C_H 1
  · show (exoticImNuLeR * genC - genC * exoticImNuLeR) * (UJ * (genH 2).transpose * UJ)
        - (UJ * (genH 2).transpose * UJ) * (exoticImNuLeR * genC - genC * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_C_H 2
  · show (exoticImNuLeR * genC - genC * exoticImNuLeR) * (UJ * (genM 0).transpose * UJ)
        - (UJ * (genM 0).transpose * UJ) * (exoticImNuLeR * genC - genC * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_C_M 0
  · show (exoticImNuLeR * genC - genC * exoticImNuLeR) * (UJ * (genM 1).transpose * UJ)
        - (UJ * (genM 1).transpose * UJ) * (exoticImNuLeR * genC - genC * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_C_M 1
  · show (exoticImNuLeR * genC - genC * exoticImNuLeR) * (UJ * (genM 2).transpose * UJ)
        - (UJ * (genM 2).transpose * UJ) * (exoticImNuLeR * genC - genC * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_C_M 2
  · show (exoticImNuLeR * genC - genC * exoticImNuLeR) * (UJ * (genM 3).transpose * UJ)
        - (UJ * (genM 3).transpose * UJ) * (exoticImNuLeR * genC - genC * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_C_M 3
  · show (exoticImNuLeR * genC - genC * exoticImNuLeR) * (UJ * (genM 4).transpose * UJ)
        - (UJ * (genM 4).transpose * UJ) * (exoticImNuLeR * genC - genC * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_C_M 4
  · show (exoticImNuLeR * genC - genC * exoticImNuLeR) * (UJ * (genM 5).transpose * UJ)
        - (UJ * (genM 5).transpose * UJ) * (exoticImNuLeR * genC - genC * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_C_M 5
  · show (exoticImNuLeR * genC - genC * exoticImNuLeR) * (UJ * (genM 6).transpose * UJ)
        - (UJ * (genM 6).transpose * UJ) * (exoticImNuLeR * genC - genC * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_C_M 6
  · show (exoticImNuLeR * genC - genC * exoticImNuLeR) * (UJ * (genM 7).transpose * UJ)
        - (UJ * (genM 7).transpose * UJ) * (exoticImNuLeR * genC - genC * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_C_M 7

theorem exoticImNuLeR_oo_M (a : Fin 8) (g2 : Fin 12) :
    (exoticImNuLeR * genM a - genM a * exoticImNuLeR) * smGenOp g2
      - smGenOp g2 * (exoticImNuLeR * genM a - genM a * exoticImNuLeR) = 0 := by
  have hcomm : exoticImNuLeR * genM a - genM a * exoticImNuLeR = 0 :=
    sub_eq_zero.mpr (exoticImNuLeR_comm_genM a)
  rw [hcomm, zero_mul, mul_zero, sub_zero]

theorem exoticImNuLeR_genCOpVal_0_eq : genCOpVal (0 : I32) = Complex.I := by
  simp [genCOpVal, genCVal, partner]
theorem exoticImNuLeR_genCOpVal_1_eq : genCOpVal (1 : I32) = Complex.I := by
  simp [genCOpVal, genCVal, partner]
theorem exoticImNuLeR_genCOpVal_9_eq : genCOpVal (9 : I32) = Complex.I := by
  simp [genCOpVal, genCVal, partner]

theorem exoticImNuLeR_CH_supp (k : Fin 3) (i j : I32)
    (h : (exoticImNuLeR * genH k - genH k * exoticImNuLeR) i j ≠ 0) :
    (i = 9 ∧ j = 0) ∨ (i = 9 ∧ j = 1) ∨ (i = 0 ∧ j = 9) ∨ (i = 1 ∧ j = 9) := by
  simp only [Matrix.sub_apply] at h
  by_cases h1 : (exoticImNuLeR * genH k) i j = 0
  · have h2 : (genH k * exoticImNuLeR) i j ≠ 0 := by
      intro hc
      apply h
      rw [h1, hc, sub_zero]
    simp only [Matrix.mul_apply] at h2
    have hex : ∃ l, genH k i l * exoticImNuLeR l j ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply h2
      exact Finset.sum_eq_zero (fun l _ => hc l)
    obtain ⟨l, hl⟩ := hex
    have hGl : genH k i l ≠ 0 := fun h0 => hl (by rw [h0, zero_mul])
    have hEl : exoticImNuLeR l j ≠ 0 := fun h0 => hl (by rw [h0, mul_zero])
    have hblock := genH_supp_block k i l hGl
    have hsupp := exoticImNuLeR_supp l j hEl
    rcases hsupp with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
    · rw [hx] at hblock
      have hi : i.val = 0 ∨ i.val = 1 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hi with hv | hv
      · have hatom : i = 0 ∧ j = 9 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 0 ∧ j = 9) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 1 ∧ j = 9 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 1 ∧ j = 9) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
  · have h1ne : (exoticImNuLeR * genH k) i j ≠ 0 := h1
    simp only [Matrix.mul_apply] at h1ne
    have hex : ∃ l, exoticImNuLeR i l * genH k l j ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply h1ne
      exact Finset.sum_eq_zero (fun l _ => hc l)
    obtain ⟨l, hl⟩ := hex
    have hEl : exoticImNuLeR i l ≠ 0 := fun h0 => hl (by rw [h0, zero_mul])
    have hG : genH k l j ≠ 0 := fun h0 => hl (by rw [h0, mul_zero])
    have hblock := genH_supp_block k l j hG
    have hsupp := exoticImNuLeR_supp i l hEl
    rcases hsupp with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
    · rw [hy] at hblock; omega
    · rw [hy] at hblock
      have hj : j.val = 0 ∨ j.val = 1 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hj with hv | hv
      · have hatom : i = 9 ∧ j = 0 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 9 ∧ j = 0) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 9 ∧ j = 1 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 9 ∧ j = 1) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega

theorem exoticImNuLeR_oo_H_C (k : Fin 3) :
    (exoticImNuLeR * genH k - genH k * exoticImNuLeR) * smGenOp 0
      - smGenOp 0 * (exoticImNuLeR * genH k - genH k * exoticImNuLeR) = 0 := by
  have hD : ∀ x y : I32, smGenOp 0 x y = if x = y then genCOpVal x else 0 :=
    fun x y => smGenOp_zero_eq x y
  ext i j
  simp only [Matrix.zero_apply, Matrix.sub_apply]
  have hCD : ((exoticImNuLeR * genH k - genH k * exoticImNuLeR) * smGenOp 0) i j
           = (exoticImNuLeR * genH k - genH k * exoticImNuLeR) i j * genCOpVal j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hD j j, if_pos rfl]
    · intro l _ hlj
      rw [hD l j, if_neg hlj, mul_zero]
    · intro hcon; exact absurd (Finset.mem_univ j) hcon
  have hDC : (smGenOp 0 * (exoticImNuLeR * genH k - genH k * exoticImNuLeR)) i j
           = genCOpVal i * (exoticImNuLeR * genH k - genH k * exoticImNuLeR) i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hD i i, if_pos rfl]
    · intro l _ hli
      rw [hD i l, if_neg (Ne.symm hli), zero_mul]
    · intro hcon; exact absurd (Finset.mem_univ i) hcon
  rw [hCD, hDC]
  by_cases hC : (exoticImNuLeR * genH k - genH k * exoticImNuLeR) i j = 0
  · rw [hC, zero_mul, mul_zero, sub_zero]
  · have hsupp := exoticImNuLeR_CH_supp k i j hC
    have hw : genCOpVal j = genCOpVal i := by
      rcases hsupp with ⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩
      · rw [hix, hjy, exoticImNuLeR_genCOpVal_0_eq, exoticImNuLeR_genCOpVal_9_eq]
      · rw [hix, hjy, exoticImNuLeR_genCOpVal_1_eq, exoticImNuLeR_genCOpVal_9_eq]
      · rw [hix, hjy, exoticImNuLeR_genCOpVal_9_eq, exoticImNuLeR_genCOpVal_0_eq]
      · rw [hix, hjy, exoticImNuLeR_genCOpVal_9_eq, exoticImNuLeR_genCOpVal_1_eq]
    rw [hw, mul_comm, sub_self]

theorem exoticImNuLeR_not_mem_RSH_of_ge16 {x : I32} (h : 16 ≤ x.val) :
    x ∉ ({0, 1, 9} : Finset I32) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_, ?_⟩
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h

theorem exoticImNuLeR_oo_H_H (k : Fin 3) (a : Fin 3) :
    (exoticImNuLeR * genH k - genH k * exoticImNuLeR) * (UJ * (genH a).transpose * UJ)
      - (UJ * (genH a).transpose * UJ) * (exoticImNuLeR * genH k - genH k * exoticImNuLeR) = 0 := by
  apply oo_disjoint _ _ _ {0, 1, 9}
  · intro i j hij
    have hsupp := exoticImNuLeR_CH_supp k i j hij
    rcases hsupp with ⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
  · intro x y hxy
    have hsupp := UJ_genH_transpose_UJ_supp a x y hxy
    exact ⟨exoticImNuLeR_not_mem_RSH_of_ge16 hsupp.1, exoticImNuLeR_not_mem_RSH_of_ge16 hsupp.2.2.1⟩

theorem exoticImNuLeR_oo_H_M (k : Fin 3) (a : Fin 8) :
    (exoticImNuLeR * genH k - genH k * exoticImNuLeR) * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ) * (exoticImNuLeR * genH k - genH k * exoticImNuLeR) = 0 :=
  double_comm_of_comm exoticImNuLeR (genH k) _ (exoticImNuLeR_comm_MOp a) (comm_genH_MOp k a)

theorem exoticImNuLeR_oo_H (k : Fin 3) (g2 : Fin 12) :
    (exoticImNuLeR * genH k - genH k * exoticImNuLeR) * smGenOp g2
      - smGenOp g2 * (exoticImNuLeR * genH k - genH k * exoticImNuLeR) = 0 := by
  fin_cases g2
  · exact exoticImNuLeR_oo_H_C k
  · show (exoticImNuLeR * genH k - genH k * exoticImNuLeR) * (UJ * (genH 0).transpose * UJ)
        - (UJ * (genH 0).transpose * UJ) * (exoticImNuLeR * genH k - genH k * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_H_H k 0
  · show (exoticImNuLeR * genH k - genH k * exoticImNuLeR) * (UJ * (genH 1).transpose * UJ)
        - (UJ * (genH 1).transpose * UJ) * (exoticImNuLeR * genH k - genH k * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_H_H k 1
  · show (exoticImNuLeR * genH k - genH k * exoticImNuLeR) * (UJ * (genH 2).transpose * UJ)
        - (UJ * (genH 2).transpose * UJ) * (exoticImNuLeR * genH k - genH k * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_H_H k 2
  · show (exoticImNuLeR * genH k - genH k * exoticImNuLeR) * (UJ * (genM 0).transpose * UJ)
        - (UJ * (genM 0).transpose * UJ) * (exoticImNuLeR * genH k - genH k * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_H_M k 0
  · show (exoticImNuLeR * genH k - genH k * exoticImNuLeR) * (UJ * (genM 1).transpose * UJ)
        - (UJ * (genM 1).transpose * UJ) * (exoticImNuLeR * genH k - genH k * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_H_M k 1
  · show (exoticImNuLeR * genH k - genH k * exoticImNuLeR) * (UJ * (genM 2).transpose * UJ)
        - (UJ * (genM 2).transpose * UJ) * (exoticImNuLeR * genH k - genH k * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_H_M k 2
  · show (exoticImNuLeR * genH k - genH k * exoticImNuLeR) * (UJ * (genM 3).transpose * UJ)
        - (UJ * (genM 3).transpose * UJ) * (exoticImNuLeR * genH k - genH k * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_H_M k 3
  · show (exoticImNuLeR * genH k - genH k * exoticImNuLeR) * (UJ * (genM 4).transpose * UJ)
        - (UJ * (genM 4).transpose * UJ) * (exoticImNuLeR * genH k - genH k * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_H_M k 4
  · show (exoticImNuLeR * genH k - genH k * exoticImNuLeR) * (UJ * (genM 5).transpose * UJ)
        - (UJ * (genM 5).transpose * UJ) * (exoticImNuLeR * genH k - genH k * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_H_M k 5
  · show (exoticImNuLeR * genH k - genH k * exoticImNuLeR) * (UJ * (genM 6).transpose * UJ)
        - (UJ * (genM 6).transpose * UJ) * (exoticImNuLeR * genH k - genH k * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_H_M k 6
  · show (exoticImNuLeR * genH k - genH k * exoticImNuLeR) * (UJ * (genM 7).transpose * UJ)
        - (UJ * (genM 7).transpose * UJ) * (exoticImNuLeR * genH k - genH k * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_H_M k 7

theorem exoticImNuLeR_orderOne : OrderOneHolds exoticImNuLeR := by
  intro g1 g2
  fin_cases g1
  · show (exoticImNuLeR * genC - genC * exoticImNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticImNuLeR * genC - genC * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_C g2
  · show (exoticImNuLeR * genH 0 - genH 0 * exoticImNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticImNuLeR * genH 0 - genH 0 * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_H 0 g2
  · show (exoticImNuLeR * genH 1 - genH 1 * exoticImNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticImNuLeR * genH 1 - genH 1 * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_H 1 g2
  · show (exoticImNuLeR * genH 2 - genH 2 * exoticImNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticImNuLeR * genH 2 - genH 2 * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_H 2 g2
  · show (exoticImNuLeR * genM 0 - genM 0 * exoticImNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticImNuLeR * genM 0 - genM 0 * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_M 0 g2
  · show (exoticImNuLeR * genM 1 - genM 1 * exoticImNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticImNuLeR * genM 1 - genM 1 * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_M 1 g2
  · show (exoticImNuLeR * genM 2 - genM 2 * exoticImNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticImNuLeR * genM 2 - genM 2 * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_M 2 g2
  · show (exoticImNuLeR * genM 3 - genM 3 * exoticImNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticImNuLeR * genM 3 - genM 3 * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_M 3 g2
  · show (exoticImNuLeR * genM 4 - genM 4 * exoticImNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticImNuLeR * genM 4 - genM 4 * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_M 4 g2
  · show (exoticImNuLeR * genM 5 - genM 5 * exoticImNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticImNuLeR * genM 5 - genM 5 * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_M 5 g2
  · show (exoticImNuLeR * genM 6 - genM 6 * exoticImNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticImNuLeR * genM 6 - genM 6 * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_M 6 g2
  · show (exoticImNuLeR * genM 7 - genM 7 * exoticImNuLeR) * smGenOp g2
        - smGenOp g2 * (exoticImNuLeR * genM 7 - genM 7 * exoticImNuLeR) = 0
    exact exoticImNuLeR_oo_M 7 g2

-- ============================================================================
-- exoticReELNuR : order-one
-- ============================================================================

theorem exoticReELNuR_supp (i j : I32) (h : exoticReELNuR i j ≠ 0) :
    (i = 1 ∧ j = 8) ∨ (i = 8 ∧ j = 1) ∨ (i = 17 ∧ j = 24) ∨ (i = 24 ∧ j = 17) := by
  unfold exoticReELNuR at h
  by_cases hs : (i = 1 ∧ j = 8) ∨ (i = 8 ∧ j = 1) ∨ (i = 17 ∧ j = 24) ∨ (i = 24 ∧ j = 17)
  · exact hs
  · rw [if_neg hs] at h
    exact absurd rfl h

theorem exoticReELNuR_factor_CC (i j : I32) (h : exoticReELNuR i j ≠ 0) :
    (genCVal j - genCVal i) * (genCOpVal j - genCOpVal i) = 0 := by
  rcases exoticReELNuR_supp i j h with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]

theorem exoticReELNuR_oo_C_C :
    (exoticReELNuR * genC - genC * exoticReELNuR) * smGenOp 0
      - smGenOp 0 * (exoticReELNuR * genC - genC * exoticReELNuR) = 0 :=
  oo_C_C_of_factor exoticReELNuR exoticReELNuR_factor_CC

theorem exoticReELNuR_comm_genC_mem (i j : I32)
    (h : (exoticReELNuR * genC - genC * exoticReELNuR) i j ≠ 0) :
    (i = 1 ∨ i = 8) ∧ (j = 1 ∨ j = 8) := by
  rw [comm_diag_entry _ _ _ (fun x y => genC_eq_diag x y) i j] at h
  have hE : exoticReELNuR i j ≠ 0 := by
    intro h0; apply h; rw [h0, zero_mul]
  have hc : genCVal j - genCVal i ≠ 0 := by
    intro h0; apply h; rw [h0, mul_zero]
  rcases exoticReELNuR_supp i j hE with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy] at hc; simp [genCVal] at hc

theorem exoticReELNuR_not_mem_RC_of_ge16 {x : I32} (h : 16 ≤ x.val) :
    x ∉ ({1, 8} : Finset I32) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_⟩
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h

theorem exoticReELNuR_oo_C_H (k : Fin 3) :
    (exoticReELNuR * genC - genC * exoticReELNuR) * (UJ * (genH k).transpose * UJ)
      - (UJ * (genH k).transpose * UJ) * (exoticReELNuR * genC - genC * exoticReELNuR) = 0 := by
  apply oo_disjoint _ _ _ {1, 8}
  · intro i j hij
    obtain ⟨hi, hj⟩ := exoticReELNuR_comm_genC_mem i j hij
    constructor
    · simp only [Finset.mem_insert, Finset.mem_singleton]; exact hi
    · simp only [Finset.mem_insert, Finset.mem_singleton]; exact hj
  · intro x y hxy
    have hsupp := UJ_genH_transpose_UJ_supp k x y hxy
    exact ⟨exoticReELNuR_not_mem_RC_of_ge16 hsupp.1, exoticReELNuR_not_mem_RC_of_ge16 hsupp.2.2.1⟩

theorem exoticReELNuR_oo_C_M (a : Fin 8) :
    (exoticReELNuR * genC - genC * exoticReELNuR) * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ) * (exoticReELNuR * genC - genC * exoticReELNuR) = 0 :=
  double_comm_of_comm exoticReELNuR genC _ (exoticReELNuR_comm_MOp a) (comm_genC_MOp a)

theorem exoticReELNuR_oo_C (g2 : Fin 12) :
    (exoticReELNuR * genC - genC * exoticReELNuR) * smGenOp g2
      - smGenOp g2 * (exoticReELNuR * genC - genC * exoticReELNuR) = 0 := by
  fin_cases g2
  · exact exoticReELNuR_oo_C_C
  · show (exoticReELNuR * genC - genC * exoticReELNuR) * (UJ * (genH 0).transpose * UJ)
        - (UJ * (genH 0).transpose * UJ) * (exoticReELNuR * genC - genC * exoticReELNuR) = 0
    exact exoticReELNuR_oo_C_H 0
  · show (exoticReELNuR * genC - genC * exoticReELNuR) * (UJ * (genH 1).transpose * UJ)
        - (UJ * (genH 1).transpose * UJ) * (exoticReELNuR * genC - genC * exoticReELNuR) = 0
    exact exoticReELNuR_oo_C_H 1
  · show (exoticReELNuR * genC - genC * exoticReELNuR) * (UJ * (genH 2).transpose * UJ)
        - (UJ * (genH 2).transpose * UJ) * (exoticReELNuR * genC - genC * exoticReELNuR) = 0
    exact exoticReELNuR_oo_C_H 2
  · show (exoticReELNuR * genC - genC * exoticReELNuR) * (UJ * (genM 0).transpose * UJ)
        - (UJ * (genM 0).transpose * UJ) * (exoticReELNuR * genC - genC * exoticReELNuR) = 0
    exact exoticReELNuR_oo_C_M 0
  · show (exoticReELNuR * genC - genC * exoticReELNuR) * (UJ * (genM 1).transpose * UJ)
        - (UJ * (genM 1).transpose * UJ) * (exoticReELNuR * genC - genC * exoticReELNuR) = 0
    exact exoticReELNuR_oo_C_M 1
  · show (exoticReELNuR * genC - genC * exoticReELNuR) * (UJ * (genM 2).transpose * UJ)
        - (UJ * (genM 2).transpose * UJ) * (exoticReELNuR * genC - genC * exoticReELNuR) = 0
    exact exoticReELNuR_oo_C_M 2
  · show (exoticReELNuR * genC - genC * exoticReELNuR) * (UJ * (genM 3).transpose * UJ)
        - (UJ * (genM 3).transpose * UJ) * (exoticReELNuR * genC - genC * exoticReELNuR) = 0
    exact exoticReELNuR_oo_C_M 3
  · show (exoticReELNuR * genC - genC * exoticReELNuR) * (UJ * (genM 4).transpose * UJ)
        - (UJ * (genM 4).transpose * UJ) * (exoticReELNuR * genC - genC * exoticReELNuR) = 0
    exact exoticReELNuR_oo_C_M 4
  · show (exoticReELNuR * genC - genC * exoticReELNuR) * (UJ * (genM 5).transpose * UJ)
        - (UJ * (genM 5).transpose * UJ) * (exoticReELNuR * genC - genC * exoticReELNuR) = 0
    exact exoticReELNuR_oo_C_M 5
  · show (exoticReELNuR * genC - genC * exoticReELNuR) * (UJ * (genM 6).transpose * UJ)
        - (UJ * (genM 6).transpose * UJ) * (exoticReELNuR * genC - genC * exoticReELNuR) = 0
    exact exoticReELNuR_oo_C_M 6
  · show (exoticReELNuR * genC - genC * exoticReELNuR) * (UJ * (genM 7).transpose * UJ)
        - (UJ * (genM 7).transpose * UJ) * (exoticReELNuR * genC - genC * exoticReELNuR) = 0
    exact exoticReELNuR_oo_C_M 7

theorem exoticReELNuR_oo_M (a : Fin 8) (g2 : Fin 12) :
    (exoticReELNuR * genM a - genM a * exoticReELNuR) * smGenOp g2
      - smGenOp g2 * (exoticReELNuR * genM a - genM a * exoticReELNuR) = 0 := by
  have hcomm : exoticReELNuR * genM a - genM a * exoticReELNuR = 0 :=
    sub_eq_zero.mpr (exoticReELNuR_comm_genM a)
  rw [hcomm, zero_mul, mul_zero, sub_zero]

theorem exoticReELNuR_genCOpVal_0_eq : genCOpVal (0 : I32) = Complex.I := by
  simp [genCOpVal, genCVal, partner]
theorem exoticReELNuR_genCOpVal_1_eq : genCOpVal (1 : I32) = Complex.I := by
  simp [genCOpVal, genCVal, partner]
theorem exoticReELNuR_genCOpVal_8_eq : genCOpVal (8 : I32) = Complex.I := by
  simp [genCOpVal, genCVal, partner]

theorem exoticReELNuR_CH_supp (k : Fin 3) (i j : I32)
    (h : (exoticReELNuR * genH k - genH k * exoticReELNuR) i j ≠ 0) :
    (i = 8 ∧ j = 0) ∨ (i = 8 ∧ j = 1) ∨ (i = 0 ∧ j = 8) ∨ (i = 1 ∧ j = 8) := by
  simp only [Matrix.sub_apply] at h
  by_cases h1 : (exoticReELNuR * genH k) i j = 0
  · have h2 : (genH k * exoticReELNuR) i j ≠ 0 := by
      intro hc
      apply h
      rw [h1, hc, sub_zero]
    simp only [Matrix.mul_apply] at h2
    have hex : ∃ l, genH k i l * exoticReELNuR l j ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply h2
      exact Finset.sum_eq_zero (fun l _ => hc l)
    obtain ⟨l, hl⟩ := hex
    have hGl : genH k i l ≠ 0 := fun h0 => hl (by rw [h0, zero_mul])
    have hEl : exoticReELNuR l j ≠ 0 := fun h0 => hl (by rw [h0, mul_zero])
    have hblock := genH_supp_block k i l hGl
    have hsupp := exoticReELNuR_supp l j hEl
    rcases hsupp with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
    · rw [hx] at hblock
      have hi : i.val = 0 ∨ i.val = 1 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hi with hv | hv
      · have hatom : i = 0 ∧ j = 8 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 0 ∧ j = 8) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 1 ∧ j = 8 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 1 ∧ j = 8) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
  · have h1ne : (exoticReELNuR * genH k) i j ≠ 0 := h1
    simp only [Matrix.mul_apply] at h1ne
    have hex : ∃ l, exoticReELNuR i l * genH k l j ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply h1ne
      exact Finset.sum_eq_zero (fun l _ => hc l)
    obtain ⟨l, hl⟩ := hex
    have hEl : exoticReELNuR i l ≠ 0 := fun h0 => hl (by rw [h0, zero_mul])
    have hG : genH k l j ≠ 0 := fun h0 => hl (by rw [h0, mul_zero])
    have hblock := genH_supp_block k l j hG
    have hsupp := exoticReELNuR_supp i l hEl
    rcases hsupp with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
    · rw [hy] at hblock; omega
    · rw [hy] at hblock
      have hj : j.val = 0 ∨ j.val = 1 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hj with hv | hv
      · have hatom : i = 8 ∧ j = 0 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 8 ∧ j = 0) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 8 ∧ j = 1 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 8 ∧ j = 1) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega

theorem exoticReELNuR_oo_H_C (k : Fin 3) :
    (exoticReELNuR * genH k - genH k * exoticReELNuR) * smGenOp 0
      - smGenOp 0 * (exoticReELNuR * genH k - genH k * exoticReELNuR) = 0 := by
  have hD : ∀ x y : I32, smGenOp 0 x y = if x = y then genCOpVal x else 0 :=
    fun x y => smGenOp_zero_eq x y
  ext i j
  simp only [Matrix.zero_apply, Matrix.sub_apply]
  have hCD : ((exoticReELNuR * genH k - genH k * exoticReELNuR) * smGenOp 0) i j
           = (exoticReELNuR * genH k - genH k * exoticReELNuR) i j * genCOpVal j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hD j j, if_pos rfl]
    · intro l _ hlj
      rw [hD l j, if_neg hlj, mul_zero]
    · intro hcon; exact absurd (Finset.mem_univ j) hcon
  have hDC : (smGenOp 0 * (exoticReELNuR * genH k - genH k * exoticReELNuR)) i j
           = genCOpVal i * (exoticReELNuR * genH k - genH k * exoticReELNuR) i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hD i i, if_pos rfl]
    · intro l _ hli
      rw [hD i l, if_neg (Ne.symm hli), zero_mul]
    · intro hcon; exact absurd (Finset.mem_univ i) hcon
  rw [hCD, hDC]
  by_cases hC : (exoticReELNuR * genH k - genH k * exoticReELNuR) i j = 0
  · rw [hC, zero_mul, mul_zero, sub_zero]
  · have hsupp := exoticReELNuR_CH_supp k i j hC
    have hw : genCOpVal j = genCOpVal i := by
      rcases hsupp with ⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩
      · rw [hix, hjy, exoticReELNuR_genCOpVal_0_eq, exoticReELNuR_genCOpVal_8_eq]
      · rw [hix, hjy, exoticReELNuR_genCOpVal_1_eq, exoticReELNuR_genCOpVal_8_eq]
      · rw [hix, hjy, exoticReELNuR_genCOpVal_8_eq, exoticReELNuR_genCOpVal_0_eq]
      · rw [hix, hjy, exoticReELNuR_genCOpVal_8_eq, exoticReELNuR_genCOpVal_1_eq]
    rw [hw, mul_comm, sub_self]

theorem exoticReELNuR_not_mem_RSH_of_ge16 {x : I32} (h : 16 ≤ x.val) :
    x ∉ ({0, 1, 8} : Finset I32) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_, ?_⟩
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h

theorem exoticReELNuR_oo_H_H (k : Fin 3) (a : Fin 3) :
    (exoticReELNuR * genH k - genH k * exoticReELNuR) * (UJ * (genH a).transpose * UJ)
      - (UJ * (genH a).transpose * UJ) * (exoticReELNuR * genH k - genH k * exoticReELNuR) = 0 := by
  apply oo_disjoint _ _ _ {0, 1, 8}
  · intro i j hij
    have hsupp := exoticReELNuR_CH_supp k i j hij
    rcases hsupp with ⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
  · intro x y hxy
    have hsupp := UJ_genH_transpose_UJ_supp a x y hxy
    exact ⟨exoticReELNuR_not_mem_RSH_of_ge16 hsupp.1, exoticReELNuR_not_mem_RSH_of_ge16 hsupp.2.2.1⟩

theorem exoticReELNuR_oo_H_M (k : Fin 3) (a : Fin 8) :
    (exoticReELNuR * genH k - genH k * exoticReELNuR) * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ) * (exoticReELNuR * genH k - genH k * exoticReELNuR) = 0 :=
  double_comm_of_comm exoticReELNuR (genH k) _ (exoticReELNuR_comm_MOp a) (comm_genH_MOp k a)

theorem exoticReELNuR_oo_H (k : Fin 3) (g2 : Fin 12) :
    (exoticReELNuR * genH k - genH k * exoticReELNuR) * smGenOp g2
      - smGenOp g2 * (exoticReELNuR * genH k - genH k * exoticReELNuR) = 0 := by
  fin_cases g2
  · exact exoticReELNuR_oo_H_C k
  · show (exoticReELNuR * genH k - genH k * exoticReELNuR) * (UJ * (genH 0).transpose * UJ)
        - (UJ * (genH 0).transpose * UJ) * (exoticReELNuR * genH k - genH k * exoticReELNuR) = 0
    exact exoticReELNuR_oo_H_H k 0
  · show (exoticReELNuR * genH k - genH k * exoticReELNuR) * (UJ * (genH 1).transpose * UJ)
        - (UJ * (genH 1).transpose * UJ) * (exoticReELNuR * genH k - genH k * exoticReELNuR) = 0
    exact exoticReELNuR_oo_H_H k 1
  · show (exoticReELNuR * genH k - genH k * exoticReELNuR) * (UJ * (genH 2).transpose * UJ)
        - (UJ * (genH 2).transpose * UJ) * (exoticReELNuR * genH k - genH k * exoticReELNuR) = 0
    exact exoticReELNuR_oo_H_H k 2
  · show (exoticReELNuR * genH k - genH k * exoticReELNuR) * (UJ * (genM 0).transpose * UJ)
        - (UJ * (genM 0).transpose * UJ) * (exoticReELNuR * genH k - genH k * exoticReELNuR) = 0
    exact exoticReELNuR_oo_H_M k 0
  · show (exoticReELNuR * genH k - genH k * exoticReELNuR) * (UJ * (genM 1).transpose * UJ)
        - (UJ * (genM 1).transpose * UJ) * (exoticReELNuR * genH k - genH k * exoticReELNuR) = 0
    exact exoticReELNuR_oo_H_M k 1
  · show (exoticReELNuR * genH k - genH k * exoticReELNuR) * (UJ * (genM 2).transpose * UJ)
        - (UJ * (genM 2).transpose * UJ) * (exoticReELNuR * genH k - genH k * exoticReELNuR) = 0
    exact exoticReELNuR_oo_H_M k 2
  · show (exoticReELNuR * genH k - genH k * exoticReELNuR) * (UJ * (genM 3).transpose * UJ)
        - (UJ * (genM 3).transpose * UJ) * (exoticReELNuR * genH k - genH k * exoticReELNuR) = 0
    exact exoticReELNuR_oo_H_M k 3
  · show (exoticReELNuR * genH k - genH k * exoticReELNuR) * (UJ * (genM 4).transpose * UJ)
        - (UJ * (genM 4).transpose * UJ) * (exoticReELNuR * genH k - genH k * exoticReELNuR) = 0
    exact exoticReELNuR_oo_H_M k 4
  · show (exoticReELNuR * genH k - genH k * exoticReELNuR) * (UJ * (genM 5).transpose * UJ)
        - (UJ * (genM 5).transpose * UJ) * (exoticReELNuR * genH k - genH k * exoticReELNuR) = 0
    exact exoticReELNuR_oo_H_M k 5
  · show (exoticReELNuR * genH k - genH k * exoticReELNuR) * (UJ * (genM 6).transpose * UJ)
        - (UJ * (genM 6).transpose * UJ) * (exoticReELNuR * genH k - genH k * exoticReELNuR) = 0
    exact exoticReELNuR_oo_H_M k 6
  · show (exoticReELNuR * genH k - genH k * exoticReELNuR) * (UJ * (genM 7).transpose * UJ)
        - (UJ * (genM 7).transpose * UJ) * (exoticReELNuR * genH k - genH k * exoticReELNuR) = 0
    exact exoticReELNuR_oo_H_M k 7

theorem exoticReELNuR_orderOne : OrderOneHolds exoticReELNuR := by
  intro g1 g2
  fin_cases g1
  · show (exoticReELNuR * genC - genC * exoticReELNuR) * smGenOp g2
        - smGenOp g2 * (exoticReELNuR * genC - genC * exoticReELNuR) = 0
    exact exoticReELNuR_oo_C g2
  · show (exoticReELNuR * genH 0 - genH 0 * exoticReELNuR) * smGenOp g2
        - smGenOp g2 * (exoticReELNuR * genH 0 - genH 0 * exoticReELNuR) = 0
    exact exoticReELNuR_oo_H 0 g2
  · show (exoticReELNuR * genH 1 - genH 1 * exoticReELNuR) * smGenOp g2
        - smGenOp g2 * (exoticReELNuR * genH 1 - genH 1 * exoticReELNuR) = 0
    exact exoticReELNuR_oo_H 1 g2
  · show (exoticReELNuR * genH 2 - genH 2 * exoticReELNuR) * smGenOp g2
        - smGenOp g2 * (exoticReELNuR * genH 2 - genH 2 * exoticReELNuR) = 0
    exact exoticReELNuR_oo_H 2 g2
  · show (exoticReELNuR * genM 0 - genM 0 * exoticReELNuR) * smGenOp g2
        - smGenOp g2 * (exoticReELNuR * genM 0 - genM 0 * exoticReELNuR) = 0
    exact exoticReELNuR_oo_M 0 g2
  · show (exoticReELNuR * genM 1 - genM 1 * exoticReELNuR) * smGenOp g2
        - smGenOp g2 * (exoticReELNuR * genM 1 - genM 1 * exoticReELNuR) = 0
    exact exoticReELNuR_oo_M 1 g2
  · show (exoticReELNuR * genM 2 - genM 2 * exoticReELNuR) * smGenOp g2
        - smGenOp g2 * (exoticReELNuR * genM 2 - genM 2 * exoticReELNuR) = 0
    exact exoticReELNuR_oo_M 2 g2
  · show (exoticReELNuR * genM 3 - genM 3 * exoticReELNuR) * smGenOp g2
        - smGenOp g2 * (exoticReELNuR * genM 3 - genM 3 * exoticReELNuR) = 0
    exact exoticReELNuR_oo_M 3 g2
  · show (exoticReELNuR * genM 4 - genM 4 * exoticReELNuR) * smGenOp g2
        - smGenOp g2 * (exoticReELNuR * genM 4 - genM 4 * exoticReELNuR) = 0
    exact exoticReELNuR_oo_M 4 g2
  · show (exoticReELNuR * genM 5 - genM 5 * exoticReELNuR) * smGenOp g2
        - smGenOp g2 * (exoticReELNuR * genM 5 - genM 5 * exoticReELNuR) = 0
    exact exoticReELNuR_oo_M 5 g2
  · show (exoticReELNuR * genM 6 - genM 6 * exoticReELNuR) * smGenOp g2
        - smGenOp g2 * (exoticReELNuR * genM 6 - genM 6 * exoticReELNuR) = 0
    exact exoticReELNuR_oo_M 6 g2
  · show (exoticReELNuR * genM 7 - genM 7 * exoticReELNuR) * smGenOp g2
        - smGenOp g2 * (exoticReELNuR * genM 7 - genM 7 * exoticReELNuR) = 0
    exact exoticReELNuR_oo_M 7 g2

-- ============================================================================
-- exoticImELNuR : order-one
-- ============================================================================

theorem exoticImELNuR_supp (i j : I32) (h : exoticImELNuR i j ≠ 0) :
    (i = 1 ∧ j = 8) ∨ (i = 24 ∧ j = 17) ∨ (i = 8 ∧ j = 1) ∨ (i = 17 ∧ j = 24) := by
  unfold exoticImELNuR at h
  by_cases h1 : (i = 1 ∧ j = 8) ∨ (i = 24 ∧ j = 17)
  · rcases h1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simp
    · simp
  · by_cases h2 : (i = 8 ∧ j = 1) ∨ (i = 17 ∧ j = 24)
    · rcases h2 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · simp
      · simp
    · simp [h1, h2] at h

theorem exoticImELNuR_factor_CC (i j : I32) (h : exoticImELNuR i j ≠ 0) :
    (genCVal j - genCVal i) * (genCOpVal j - genCOpVal i) = 0 := by
  rcases exoticImELNuR_supp i j h with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]

theorem exoticImELNuR_oo_C_C :
    (exoticImELNuR * genC - genC * exoticImELNuR) * smGenOp 0
      - smGenOp 0 * (exoticImELNuR * genC - genC * exoticImELNuR) = 0 :=
  oo_C_C_of_factor exoticImELNuR exoticImELNuR_factor_CC

theorem exoticImELNuR_comm_genC_mem (i j : I32)
    (h : (exoticImELNuR * genC - genC * exoticImELNuR) i j ≠ 0) :
    (i = 1 ∨ i = 8) ∧ (j = 1 ∨ j = 8) := by
  rw [comm_diag_entry _ _ _ (fun x y => genC_eq_diag x y) i j] at h
  have hE : exoticImELNuR i j ≠ 0 := by
    intro h0; apply h; rw [h0, zero_mul]
  have hc : genCVal j - genCVal i ≠ 0 := by
    intro h0; apply h; rw [h0, mul_zero]
  rcases exoticImELNuR_supp i j hE with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy] at hc; simp [genCVal] at hc

theorem exoticImELNuR_not_mem_RC_of_ge16 {x : I32} (h : 16 ≤ x.val) :
    x ∉ ({1, 8} : Finset I32) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_⟩
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h

theorem exoticImELNuR_oo_C_H (k : Fin 3) :
    (exoticImELNuR * genC - genC * exoticImELNuR) * (UJ * (genH k).transpose * UJ)
      - (UJ * (genH k).transpose * UJ) * (exoticImELNuR * genC - genC * exoticImELNuR) = 0 := by
  apply oo_disjoint _ _ _ {1, 8}
  · intro i j hij
    obtain ⟨hi, hj⟩ := exoticImELNuR_comm_genC_mem i j hij
    constructor
    · simp only [Finset.mem_insert, Finset.mem_singleton]; exact hi
    · simp only [Finset.mem_insert, Finset.mem_singleton]; exact hj
  · intro x y hxy
    have hsupp := UJ_genH_transpose_UJ_supp k x y hxy
    exact ⟨exoticImELNuR_not_mem_RC_of_ge16 hsupp.1, exoticImELNuR_not_mem_RC_of_ge16 hsupp.2.2.1⟩

theorem exoticImELNuR_oo_C_M (a : Fin 8) :
    (exoticImELNuR * genC - genC * exoticImELNuR) * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ) * (exoticImELNuR * genC - genC * exoticImELNuR) = 0 :=
  double_comm_of_comm exoticImELNuR genC _ (exoticImELNuR_comm_MOp a) (comm_genC_MOp a)

theorem exoticImELNuR_oo_C (g2 : Fin 12) :
    (exoticImELNuR * genC - genC * exoticImELNuR) * smGenOp g2
      - smGenOp g2 * (exoticImELNuR * genC - genC * exoticImELNuR) = 0 := by
  fin_cases g2
  · exact exoticImELNuR_oo_C_C
  · show (exoticImELNuR * genC - genC * exoticImELNuR) * (UJ * (genH 0).transpose * UJ)
        - (UJ * (genH 0).transpose * UJ) * (exoticImELNuR * genC - genC * exoticImELNuR) = 0
    exact exoticImELNuR_oo_C_H 0
  · show (exoticImELNuR * genC - genC * exoticImELNuR) * (UJ * (genH 1).transpose * UJ)
        - (UJ * (genH 1).transpose * UJ) * (exoticImELNuR * genC - genC * exoticImELNuR) = 0
    exact exoticImELNuR_oo_C_H 1
  · show (exoticImELNuR * genC - genC * exoticImELNuR) * (UJ * (genH 2).transpose * UJ)
        - (UJ * (genH 2).transpose * UJ) * (exoticImELNuR * genC - genC * exoticImELNuR) = 0
    exact exoticImELNuR_oo_C_H 2
  · show (exoticImELNuR * genC - genC * exoticImELNuR) * (UJ * (genM 0).transpose * UJ)
        - (UJ * (genM 0).transpose * UJ) * (exoticImELNuR * genC - genC * exoticImELNuR) = 0
    exact exoticImELNuR_oo_C_M 0
  · show (exoticImELNuR * genC - genC * exoticImELNuR) * (UJ * (genM 1).transpose * UJ)
        - (UJ * (genM 1).transpose * UJ) * (exoticImELNuR * genC - genC * exoticImELNuR) = 0
    exact exoticImELNuR_oo_C_M 1
  · show (exoticImELNuR * genC - genC * exoticImELNuR) * (UJ * (genM 2).transpose * UJ)
        - (UJ * (genM 2).transpose * UJ) * (exoticImELNuR * genC - genC * exoticImELNuR) = 0
    exact exoticImELNuR_oo_C_M 2
  · show (exoticImELNuR * genC - genC * exoticImELNuR) * (UJ * (genM 3).transpose * UJ)
        - (UJ * (genM 3).transpose * UJ) * (exoticImELNuR * genC - genC * exoticImELNuR) = 0
    exact exoticImELNuR_oo_C_M 3
  · show (exoticImELNuR * genC - genC * exoticImELNuR) * (UJ * (genM 4).transpose * UJ)
        - (UJ * (genM 4).transpose * UJ) * (exoticImELNuR * genC - genC * exoticImELNuR) = 0
    exact exoticImELNuR_oo_C_M 4
  · show (exoticImELNuR * genC - genC * exoticImELNuR) * (UJ * (genM 5).transpose * UJ)
        - (UJ * (genM 5).transpose * UJ) * (exoticImELNuR * genC - genC * exoticImELNuR) = 0
    exact exoticImELNuR_oo_C_M 5
  · show (exoticImELNuR * genC - genC * exoticImELNuR) * (UJ * (genM 6).transpose * UJ)
        - (UJ * (genM 6).transpose * UJ) * (exoticImELNuR * genC - genC * exoticImELNuR) = 0
    exact exoticImELNuR_oo_C_M 6
  · show (exoticImELNuR * genC - genC * exoticImELNuR) * (UJ * (genM 7).transpose * UJ)
        - (UJ * (genM 7).transpose * UJ) * (exoticImELNuR * genC - genC * exoticImELNuR) = 0
    exact exoticImELNuR_oo_C_M 7

theorem exoticImELNuR_oo_M (a : Fin 8) (g2 : Fin 12) :
    (exoticImELNuR * genM a - genM a * exoticImELNuR) * smGenOp g2
      - smGenOp g2 * (exoticImELNuR * genM a - genM a * exoticImELNuR) = 0 := by
  have hcomm : exoticImELNuR * genM a - genM a * exoticImELNuR = 0 :=
    sub_eq_zero.mpr (exoticImELNuR_comm_genM a)
  rw [hcomm, zero_mul, mul_zero, sub_zero]

theorem exoticImELNuR_genCOpVal_0_eq : genCOpVal (0 : I32) = Complex.I := by
  simp [genCOpVal, genCVal, partner]
theorem exoticImELNuR_genCOpVal_1_eq : genCOpVal (1 : I32) = Complex.I := by
  simp [genCOpVal, genCVal, partner]
theorem exoticImELNuR_genCOpVal_8_eq : genCOpVal (8 : I32) = Complex.I := by
  simp [genCOpVal, genCVal, partner]

theorem exoticImELNuR_CH_supp (k : Fin 3) (i j : I32)
    (h : (exoticImELNuR * genH k - genH k * exoticImELNuR) i j ≠ 0) :
    (i = 8 ∧ j = 0) ∨ (i = 8 ∧ j = 1) ∨ (i = 0 ∧ j = 8) ∨ (i = 1 ∧ j = 8) := by
  simp only [Matrix.sub_apply] at h
  by_cases h1 : (exoticImELNuR * genH k) i j = 0
  · have h2 : (genH k * exoticImELNuR) i j ≠ 0 := by
      intro hc
      apply h
      rw [h1, hc, sub_zero]
    simp only [Matrix.mul_apply] at h2
    have hex : ∃ l, genH k i l * exoticImELNuR l j ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply h2
      exact Finset.sum_eq_zero (fun l _ => hc l)
    obtain ⟨l, hl⟩ := hex
    have hGl : genH k i l ≠ 0 := fun h0 => hl (by rw [h0, zero_mul])
    have hEl : exoticImELNuR l j ≠ 0 := fun h0 => hl (by rw [h0, mul_zero])
    have hblock := genH_supp_block k i l hGl
    have hsupp := exoticImELNuR_supp l j hEl
    rcases hsupp with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
    · rw [hx] at hblock
      have hi : i.val = 0 ∨ i.val = 1 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hi with hv | hv
      · have hatom : i = 0 ∧ j = 8 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 0 ∧ j = 8) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 1 ∧ j = 8 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 1 ∧ j = 8) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
  · have h1ne : (exoticImELNuR * genH k) i j ≠ 0 := h1
    simp only [Matrix.mul_apply] at h1ne
    have hex : ∃ l, exoticImELNuR i l * genH k l j ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply h1ne
      exact Finset.sum_eq_zero (fun l _ => hc l)
    obtain ⟨l, hl⟩ := hex
    have hEl : exoticImELNuR i l ≠ 0 := fun h0 => hl (by rw [h0, zero_mul])
    have hG : genH k l j ≠ 0 := fun h0 => hl (by rw [h0, mul_zero])
    have hblock := genH_supp_block k l j hG
    have hsupp := exoticImELNuR_supp i l hEl
    rcases hsupp with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega
    · rw [hy] at hblock
      have hj : j.val = 0 ∨ j.val = 1 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hj with hv | hv
      · have hatom : i = 8 ∧ j = 0 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 8 ∧ j = 0) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 8 ∧ j = 1 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 8 ∧ j = 1) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hy] at hblock; omega

theorem exoticImELNuR_oo_H_C (k : Fin 3) :
    (exoticImELNuR * genH k - genH k * exoticImELNuR) * smGenOp 0
      - smGenOp 0 * (exoticImELNuR * genH k - genH k * exoticImELNuR) = 0 := by
  have hD : ∀ x y : I32, smGenOp 0 x y = if x = y then genCOpVal x else 0 :=
    fun x y => smGenOp_zero_eq x y
  ext i j
  simp only [Matrix.zero_apply, Matrix.sub_apply]
  have hCD : ((exoticImELNuR * genH k - genH k * exoticImELNuR) * smGenOp 0) i j
           = (exoticImELNuR * genH k - genH k * exoticImELNuR) i j * genCOpVal j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hD j j, if_pos rfl]
    · intro l _ hlj
      rw [hD l j, if_neg hlj, mul_zero]
    · intro hcon; exact absurd (Finset.mem_univ j) hcon
  have hDC : (smGenOp 0 * (exoticImELNuR * genH k - genH k * exoticImELNuR)) i j
           = genCOpVal i * (exoticImELNuR * genH k - genH k * exoticImELNuR) i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hD i i, if_pos rfl]
    · intro l _ hli
      rw [hD i l, if_neg (Ne.symm hli), zero_mul]
    · intro hcon; exact absurd (Finset.mem_univ i) hcon
  rw [hCD, hDC]
  by_cases hC : (exoticImELNuR * genH k - genH k * exoticImELNuR) i j = 0
  · rw [hC, zero_mul, mul_zero, sub_zero]
  · have hsupp := exoticImELNuR_CH_supp k i j hC
    have hw : genCOpVal j = genCOpVal i := by
      rcases hsupp with ⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩
      · rw [hix, hjy, exoticImELNuR_genCOpVal_0_eq, exoticImELNuR_genCOpVal_8_eq]
      · rw [hix, hjy, exoticImELNuR_genCOpVal_1_eq, exoticImELNuR_genCOpVal_8_eq]
      · rw [hix, hjy, exoticImELNuR_genCOpVal_8_eq, exoticImELNuR_genCOpVal_0_eq]
      · rw [hix, hjy, exoticImELNuR_genCOpVal_8_eq, exoticImELNuR_genCOpVal_1_eq]
    rw [hw, mul_comm, sub_self]

theorem exoticImELNuR_not_mem_RSH_of_ge16 {x : I32} (h : 16 ≤ x.val) :
    x ∉ ({0, 1, 8} : Finset I32) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_, ?_⟩
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h

theorem exoticImELNuR_oo_H_H (k : Fin 3) (a : Fin 3) :
    (exoticImELNuR * genH k - genH k * exoticImELNuR) * (UJ * (genH a).transpose * UJ)
      - (UJ * (genH a).transpose * UJ) * (exoticImELNuR * genH k - genH k * exoticImELNuR) = 0 := by
  apply oo_disjoint _ _ _ {0, 1, 8}
  · intro i j hij
    have hsupp := exoticImELNuR_CH_supp k i j hij
    rcases hsupp with ⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
  · intro x y hxy
    have hsupp := UJ_genH_transpose_UJ_supp a x y hxy
    exact ⟨exoticImELNuR_not_mem_RSH_of_ge16 hsupp.1, exoticImELNuR_not_mem_RSH_of_ge16 hsupp.2.2.1⟩

theorem exoticImELNuR_oo_H_M (k : Fin 3) (a : Fin 8) :
    (exoticImELNuR * genH k - genH k * exoticImELNuR) * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ) * (exoticImELNuR * genH k - genH k * exoticImELNuR) = 0 :=
  double_comm_of_comm exoticImELNuR (genH k) _ (exoticImELNuR_comm_MOp a) (comm_genH_MOp k a)

theorem exoticImELNuR_oo_H (k : Fin 3) (g2 : Fin 12) :
    (exoticImELNuR * genH k - genH k * exoticImELNuR) * smGenOp g2
      - smGenOp g2 * (exoticImELNuR * genH k - genH k * exoticImELNuR) = 0 := by
  fin_cases g2
  · exact exoticImELNuR_oo_H_C k
  · show (exoticImELNuR * genH k - genH k * exoticImELNuR) * (UJ * (genH 0).transpose * UJ)
        - (UJ * (genH 0).transpose * UJ) * (exoticImELNuR * genH k - genH k * exoticImELNuR) = 0
    exact exoticImELNuR_oo_H_H k 0
  · show (exoticImELNuR * genH k - genH k * exoticImELNuR) * (UJ * (genH 1).transpose * UJ)
        - (UJ * (genH 1).transpose * UJ) * (exoticImELNuR * genH k - genH k * exoticImELNuR) = 0
    exact exoticImELNuR_oo_H_H k 1
  · show (exoticImELNuR * genH k - genH k * exoticImELNuR) * (UJ * (genH 2).transpose * UJ)
        - (UJ * (genH 2).transpose * UJ) * (exoticImELNuR * genH k - genH k * exoticImELNuR) = 0
    exact exoticImELNuR_oo_H_H k 2
  · show (exoticImELNuR * genH k - genH k * exoticImELNuR) * (UJ * (genM 0).transpose * UJ)
        - (UJ * (genM 0).transpose * UJ) * (exoticImELNuR * genH k - genH k * exoticImELNuR) = 0
    exact exoticImELNuR_oo_H_M k 0
  · show (exoticImELNuR * genH k - genH k * exoticImELNuR) * (UJ * (genM 1).transpose * UJ)
        - (UJ * (genM 1).transpose * UJ) * (exoticImELNuR * genH k - genH k * exoticImELNuR) = 0
    exact exoticImELNuR_oo_H_M k 1
  · show (exoticImELNuR * genH k - genH k * exoticImELNuR) * (UJ * (genM 2).transpose * UJ)
        - (UJ * (genM 2).transpose * UJ) * (exoticImELNuR * genH k - genH k * exoticImELNuR) = 0
    exact exoticImELNuR_oo_H_M k 2
  · show (exoticImELNuR * genH k - genH k * exoticImELNuR) * (UJ * (genM 3).transpose * UJ)
        - (UJ * (genM 3).transpose * UJ) * (exoticImELNuR * genH k - genH k * exoticImELNuR) = 0
    exact exoticImELNuR_oo_H_M k 3
  · show (exoticImELNuR * genH k - genH k * exoticImELNuR) * (UJ * (genM 4).transpose * UJ)
        - (UJ * (genM 4).transpose * UJ) * (exoticImELNuR * genH k - genH k * exoticImELNuR) = 0
    exact exoticImELNuR_oo_H_M k 4
  · show (exoticImELNuR * genH k - genH k * exoticImELNuR) * (UJ * (genM 5).transpose * UJ)
        - (UJ * (genM 5).transpose * UJ) * (exoticImELNuR * genH k - genH k * exoticImELNuR) = 0
    exact exoticImELNuR_oo_H_M k 5
  · show (exoticImELNuR * genH k - genH k * exoticImELNuR) * (UJ * (genM 6).transpose * UJ)
        - (UJ * (genM 6).transpose * UJ) * (exoticImELNuR * genH k - genH k * exoticImELNuR) = 0
    exact exoticImELNuR_oo_H_M k 6
  · show (exoticImELNuR * genH k - genH k * exoticImELNuR) * (UJ * (genM 7).transpose * UJ)
        - (UJ * (genM 7).transpose * UJ) * (exoticImELNuR * genH k - genH k * exoticImELNuR) = 0
    exact exoticImELNuR_oo_H_M k 7

theorem exoticImELNuR_orderOne : OrderOneHolds exoticImELNuR := by
  intro g1 g2
  fin_cases g1
  · show (exoticImELNuR * genC - genC * exoticImELNuR) * smGenOp g2
        - smGenOp g2 * (exoticImELNuR * genC - genC * exoticImELNuR) = 0
    exact exoticImELNuR_oo_C g2
  · show (exoticImELNuR * genH 0 - genH 0 * exoticImELNuR) * smGenOp g2
        - smGenOp g2 * (exoticImELNuR * genH 0 - genH 0 * exoticImELNuR) = 0
    exact exoticImELNuR_oo_H 0 g2
  · show (exoticImELNuR * genH 1 - genH 1 * exoticImELNuR) * smGenOp g2
        - smGenOp g2 * (exoticImELNuR * genH 1 - genH 1 * exoticImELNuR) = 0
    exact exoticImELNuR_oo_H 1 g2
  · show (exoticImELNuR * genH 2 - genH 2 * exoticImELNuR) * smGenOp g2
        - smGenOp g2 * (exoticImELNuR * genH 2 - genH 2 * exoticImELNuR) = 0
    exact exoticImELNuR_oo_H 2 g2
  · show (exoticImELNuR * genM 0 - genM 0 * exoticImELNuR) * smGenOp g2
        - smGenOp g2 * (exoticImELNuR * genM 0 - genM 0 * exoticImELNuR) = 0
    exact exoticImELNuR_oo_M 0 g2
  · show (exoticImELNuR * genM 1 - genM 1 * exoticImELNuR) * smGenOp g2
        - smGenOp g2 * (exoticImELNuR * genM 1 - genM 1 * exoticImELNuR) = 0
    exact exoticImELNuR_oo_M 1 g2
  · show (exoticImELNuR * genM 2 - genM 2 * exoticImELNuR) * smGenOp g2
        - smGenOp g2 * (exoticImELNuR * genM 2 - genM 2 * exoticImELNuR) = 0
    exact exoticImELNuR_oo_M 2 g2
  · show (exoticImELNuR * genM 3 - genM 3 * exoticImELNuR) * smGenOp g2
        - smGenOp g2 * (exoticImELNuR * genM 3 - genM 3 * exoticImELNuR) = 0
    exact exoticImELNuR_oo_M 3 g2
  · show (exoticImELNuR * genM 4 - genM 4 * exoticImELNuR) * smGenOp g2
        - smGenOp g2 * (exoticImELNuR * genM 4 - genM 4 * exoticImELNuR) = 0
    exact exoticImELNuR_oo_M 4 g2
  · show (exoticImELNuR * genM 5 - genM 5 * exoticImELNuR) * smGenOp g2
        - smGenOp g2 * (exoticImELNuR * genM 5 - genM 5 * exoticImELNuR) = 0
    exact exoticImELNuR_oo_M 5 g2
  · show (exoticImELNuR * genM 6 - genM 6 * exoticImELNuR) * smGenOp g2
        - smGenOp g2 * (exoticImELNuR * genM 6 - genM 6 * exoticImELNuR) = 0
    exact exoticImELNuR_oo_M 6 g2
  · show (exoticImELNuR * genM 7 - genM 7 * exoticImELNuR) * smGenOp g2
        - smGenOp g2 * (exoticImELNuR * genM 7 - genM 7 * exoticImELNuR) = 0
    exact exoticImELNuR_oo_M 7 g2

-- ============================================================================
-- exoticReNuREbarR : order-one
-- ============================================================================

theorem exoticReNuREbarR_supp (i j : I32) (h : exoticReNuREbarR i j ≠ 0) :
    (i = 8 ∧ j = 25) ∨ (i = 25 ∧ j = 8) ∨ (i = 24 ∧ j = 9) ∨ (i = 9 ∧ j = 24) := by
  unfold exoticReNuREbarR at h
  by_cases hs : (i = 8 ∧ j = 25) ∨ (i = 25 ∧ j = 8) ∨ (i = 24 ∧ j = 9) ∨ (i = 9 ∧ j = 24)
  · exact hs
  · rw [if_neg hs] at h
    exact absurd rfl h

theorem exoticReNuREbarR_CVal_const (x y : I32) (h : exoticReNuREbarR x y ≠ 0) :
    genCVal x = genCVal y := by
  rcases exoticReNuREbarR_supp x y h with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; simp [genCVal]
  · rw [hx, hy]; simp [genCVal]
  · rw [hx, hy]; simp [genCVal]
  · rw [hx, hy]; simp [genCVal]

theorem exoticReNuREbarR_comm_genC : exoticReNuREbarR * genC = genC * exoticReNuREbarR :=
  comm_genC_of_CVal_const exoticReNuREbarR exoticReNuREbarR_CVal_const

theorem exoticReNuREbarR_oo_C (g2 : Fin 12) :
    (exoticReNuREbarR * genC - genC * exoticReNuREbarR) * smGenOp g2
      - smGenOp g2 * (exoticReNuREbarR * genC - genC * exoticReNuREbarR) = 0 := by
  have hcomm : exoticReNuREbarR * genC - genC * exoticReNuREbarR = 0 := sub_eq_zero.mpr exoticReNuREbarR_comm_genC
  rw [hcomm, zero_mul, mul_zero, sub_zero]

theorem exoticReNuREbarR_ge8 (x y : I32) (h : exoticReNuREbarR x y ≠ 0) :
    8 ≤ x.val ∧ 8 ≤ y.val := by
  rcases exoticReNuREbarR_supp x y h with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩

theorem exoticReNuREbarR_comm_genH (k : Fin 3) : exoticReNuREbarR * genH k = genH k * exoticReNuREbarR :=
  comm_genH_of_ge8 exoticReNuREbarR exoticReNuREbarR_ge8 k

theorem exoticReNuREbarR_oo_H (k : Fin 3) (g2 : Fin 12) :
    (exoticReNuREbarR * genH k - genH k * exoticReNuREbarR) * smGenOp g2
      - smGenOp g2 * (exoticReNuREbarR * genH k - genH k * exoticReNuREbarR) = 0 := by
  have hcomm : exoticReNuREbarR * genH k - genH k * exoticReNuREbarR = 0 := sub_eq_zero.mpr (exoticReNuREbarR_comm_genH k)
  rw [hcomm, zero_mul, mul_zero, sub_zero]

theorem exoticReNuREbarR_oo_M (a : Fin 8) (g2 : Fin 12) :
    (exoticReNuREbarR * genM a - genM a * exoticReNuREbarR) * smGenOp g2
      - smGenOp g2 * (exoticReNuREbarR * genM a - genM a * exoticReNuREbarR) = 0 := by
  have hcomm : exoticReNuREbarR * genM a - genM a * exoticReNuREbarR = 0 :=
    sub_eq_zero.mpr (exoticReNuREbarR_comm_genM a)
  rw [hcomm, zero_mul, mul_zero, sub_zero]

theorem exoticReNuREbarR_orderOne : OrderOneHolds exoticReNuREbarR := by
  intro g1 g2
  fin_cases g1
  · show (exoticReNuREbarR * genC - genC * exoticReNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReNuREbarR * genC - genC * exoticReNuREbarR) = 0
    exact exoticReNuREbarR_oo_C g2
  · show (exoticReNuREbarR * genH 0 - genH 0 * exoticReNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReNuREbarR * genH 0 - genH 0 * exoticReNuREbarR) = 0
    exact exoticReNuREbarR_oo_H 0 g2
  · show (exoticReNuREbarR * genH 1 - genH 1 * exoticReNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReNuREbarR * genH 1 - genH 1 * exoticReNuREbarR) = 0
    exact exoticReNuREbarR_oo_H 1 g2
  · show (exoticReNuREbarR * genH 2 - genH 2 * exoticReNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReNuREbarR * genH 2 - genH 2 * exoticReNuREbarR) = 0
    exact exoticReNuREbarR_oo_H 2 g2
  · show (exoticReNuREbarR * genM 0 - genM 0 * exoticReNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReNuREbarR * genM 0 - genM 0 * exoticReNuREbarR) = 0
    exact exoticReNuREbarR_oo_M 0 g2
  · show (exoticReNuREbarR * genM 1 - genM 1 * exoticReNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReNuREbarR * genM 1 - genM 1 * exoticReNuREbarR) = 0
    exact exoticReNuREbarR_oo_M 1 g2
  · show (exoticReNuREbarR * genM 2 - genM 2 * exoticReNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReNuREbarR * genM 2 - genM 2 * exoticReNuREbarR) = 0
    exact exoticReNuREbarR_oo_M 2 g2
  · show (exoticReNuREbarR * genM 3 - genM 3 * exoticReNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReNuREbarR * genM 3 - genM 3 * exoticReNuREbarR) = 0
    exact exoticReNuREbarR_oo_M 3 g2
  · show (exoticReNuREbarR * genM 4 - genM 4 * exoticReNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReNuREbarR * genM 4 - genM 4 * exoticReNuREbarR) = 0
    exact exoticReNuREbarR_oo_M 4 g2
  · show (exoticReNuREbarR * genM 5 - genM 5 * exoticReNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReNuREbarR * genM 5 - genM 5 * exoticReNuREbarR) = 0
    exact exoticReNuREbarR_oo_M 5 g2
  · show (exoticReNuREbarR * genM 6 - genM 6 * exoticReNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReNuREbarR * genM 6 - genM 6 * exoticReNuREbarR) = 0
    exact exoticReNuREbarR_oo_M 6 g2
  · show (exoticReNuREbarR * genM 7 - genM 7 * exoticReNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReNuREbarR * genM 7 - genM 7 * exoticReNuREbarR) = 0
    exact exoticReNuREbarR_oo_M 7 g2

-- ============================================================================
-- exoticImNuREbarR : order-one
-- ============================================================================

theorem exoticImNuREbarR_supp (i j : I32) (h : exoticImNuREbarR i j ≠ 0) :
    (i = 8 ∧ j = 25) ∨ (i = 9 ∧ j = 24) ∨ (i = 25 ∧ j = 8) ∨ (i = 24 ∧ j = 9) := by
  unfold exoticImNuREbarR at h
  by_cases h1 : (i = 8 ∧ j = 25) ∨ (i = 9 ∧ j = 24)
  · rcases h1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simp
    · simp
  · by_cases h2 : (i = 25 ∧ j = 8) ∨ (i = 24 ∧ j = 9)
    · rcases h2 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · simp
      · simp
    · simp [h1, h2] at h

theorem exoticImNuREbarR_CVal_const (x y : I32) (h : exoticImNuREbarR x y ≠ 0) :
    genCVal x = genCVal y := by
  rcases exoticImNuREbarR_supp x y h with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; simp [genCVal]
  · rw [hx, hy]; simp [genCVal]
  · rw [hx, hy]; simp [genCVal]
  · rw [hx, hy]; simp [genCVal]

theorem exoticImNuREbarR_comm_genC : exoticImNuREbarR * genC = genC * exoticImNuREbarR :=
  comm_genC_of_CVal_const exoticImNuREbarR exoticImNuREbarR_CVal_const

theorem exoticImNuREbarR_oo_C (g2 : Fin 12) :
    (exoticImNuREbarR * genC - genC * exoticImNuREbarR) * smGenOp g2
      - smGenOp g2 * (exoticImNuREbarR * genC - genC * exoticImNuREbarR) = 0 := by
  have hcomm : exoticImNuREbarR * genC - genC * exoticImNuREbarR = 0 := sub_eq_zero.mpr exoticImNuREbarR_comm_genC
  rw [hcomm, zero_mul, mul_zero, sub_zero]

theorem exoticImNuREbarR_ge8 (x y : I32) (h : exoticImNuREbarR x y ≠ 0) :
    8 ≤ x.val ∧ 8 ≤ y.val := by
  rcases exoticImNuREbarR_supp x y h with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩

theorem exoticImNuREbarR_comm_genH (k : Fin 3) : exoticImNuREbarR * genH k = genH k * exoticImNuREbarR :=
  comm_genH_of_ge8 exoticImNuREbarR exoticImNuREbarR_ge8 k

theorem exoticImNuREbarR_oo_H (k : Fin 3) (g2 : Fin 12) :
    (exoticImNuREbarR * genH k - genH k * exoticImNuREbarR) * smGenOp g2
      - smGenOp g2 * (exoticImNuREbarR * genH k - genH k * exoticImNuREbarR) = 0 := by
  have hcomm : exoticImNuREbarR * genH k - genH k * exoticImNuREbarR = 0 := sub_eq_zero.mpr (exoticImNuREbarR_comm_genH k)
  rw [hcomm, zero_mul, mul_zero, sub_zero]

theorem exoticImNuREbarR_oo_M (a : Fin 8) (g2 : Fin 12) :
    (exoticImNuREbarR * genM a - genM a * exoticImNuREbarR) * smGenOp g2
      - smGenOp g2 * (exoticImNuREbarR * genM a - genM a * exoticImNuREbarR) = 0 := by
  have hcomm : exoticImNuREbarR * genM a - genM a * exoticImNuREbarR = 0 :=
    sub_eq_zero.mpr (exoticImNuREbarR_comm_genM a)
  rw [hcomm, zero_mul, mul_zero, sub_zero]

theorem exoticImNuREbarR_orderOne : OrderOneHolds exoticImNuREbarR := by
  intro g1 g2
  fin_cases g1
  · show (exoticImNuREbarR * genC - genC * exoticImNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImNuREbarR * genC - genC * exoticImNuREbarR) = 0
    exact exoticImNuREbarR_oo_C g2
  · show (exoticImNuREbarR * genH 0 - genH 0 * exoticImNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImNuREbarR * genH 0 - genH 0 * exoticImNuREbarR) = 0
    exact exoticImNuREbarR_oo_H 0 g2
  · show (exoticImNuREbarR * genH 1 - genH 1 * exoticImNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImNuREbarR * genH 1 - genH 1 * exoticImNuREbarR) = 0
    exact exoticImNuREbarR_oo_H 1 g2
  · show (exoticImNuREbarR * genH 2 - genH 2 * exoticImNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImNuREbarR * genH 2 - genH 2 * exoticImNuREbarR) = 0
    exact exoticImNuREbarR_oo_H 2 g2
  · show (exoticImNuREbarR * genM 0 - genM 0 * exoticImNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImNuREbarR * genM 0 - genM 0 * exoticImNuREbarR) = 0
    exact exoticImNuREbarR_oo_M 0 g2
  · show (exoticImNuREbarR * genM 1 - genM 1 * exoticImNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImNuREbarR * genM 1 - genM 1 * exoticImNuREbarR) = 0
    exact exoticImNuREbarR_oo_M 1 g2
  · show (exoticImNuREbarR * genM 2 - genM 2 * exoticImNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImNuREbarR * genM 2 - genM 2 * exoticImNuREbarR) = 0
    exact exoticImNuREbarR_oo_M 2 g2
  · show (exoticImNuREbarR * genM 3 - genM 3 * exoticImNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImNuREbarR * genM 3 - genM 3 * exoticImNuREbarR) = 0
    exact exoticImNuREbarR_oo_M 3 g2
  · show (exoticImNuREbarR * genM 4 - genM 4 * exoticImNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImNuREbarR * genM 4 - genM 4 * exoticImNuREbarR) = 0
    exact exoticImNuREbarR_oo_M 4 g2
  · show (exoticImNuREbarR * genM 5 - genM 5 * exoticImNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImNuREbarR * genM 5 - genM 5 * exoticImNuREbarR) = 0
    exact exoticImNuREbarR_oo_M 5 g2
  · show (exoticImNuREbarR * genM 6 - genM 6 * exoticImNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImNuREbarR * genM 6 - genM 6 * exoticImNuREbarR) = 0
    exact exoticImNuREbarR_oo_M 6 g2
  · show (exoticImNuREbarR * genM 7 - genM 7 * exoticImNuREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImNuREbarR * genM 7 - genM 7 * exoticImNuREbarR) = 0
    exact exoticImNuREbarR_oo_M 7 g2

-- ============================================================================
-- exoticReEREbarR : order-one
-- ============================================================================

theorem exoticReEREbarR_supp (i j : I32) (h : exoticReEREbarR i j ≠ 0) :
    (i = 9 ∧ j = 25) ∨ (i = 25 ∧ j = 9) := by
  unfold exoticReEREbarR at h
  by_cases hs : (i = 9 ∧ j = 25) ∨ (i = 25 ∧ j = 9)
  · exact hs
  · rw [if_neg hs] at h
    exact absurd rfl h

theorem exoticReEREbarR_CVal_const (x y : I32) (h : exoticReEREbarR x y ≠ 0) :
    genCVal x = genCVal y := by
  rcases exoticReEREbarR_supp x y h with ⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; simp [genCVal]
  · rw [hx, hy]; simp [genCVal]

theorem exoticReEREbarR_comm_genC : exoticReEREbarR * genC = genC * exoticReEREbarR :=
  comm_genC_of_CVal_const exoticReEREbarR exoticReEREbarR_CVal_const

theorem exoticReEREbarR_oo_C (g2 : Fin 12) :
    (exoticReEREbarR * genC - genC * exoticReEREbarR) * smGenOp g2
      - smGenOp g2 * (exoticReEREbarR * genC - genC * exoticReEREbarR) = 0 := by
  have hcomm : exoticReEREbarR * genC - genC * exoticReEREbarR = 0 := sub_eq_zero.mpr exoticReEREbarR_comm_genC
  rw [hcomm, zero_mul, mul_zero, sub_zero]

theorem exoticReEREbarR_ge8 (x y : I32) (h : exoticReEREbarR x y ≠ 0) :
    8 ≤ x.val ∧ 8 ≤ y.val := by
  rcases exoticReEREbarR_supp x y h with ⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩

theorem exoticReEREbarR_comm_genH (k : Fin 3) : exoticReEREbarR * genH k = genH k * exoticReEREbarR :=
  comm_genH_of_ge8 exoticReEREbarR exoticReEREbarR_ge8 k

theorem exoticReEREbarR_oo_H (k : Fin 3) (g2 : Fin 12) :
    (exoticReEREbarR * genH k - genH k * exoticReEREbarR) * smGenOp g2
      - smGenOp g2 * (exoticReEREbarR * genH k - genH k * exoticReEREbarR) = 0 := by
  have hcomm : exoticReEREbarR * genH k - genH k * exoticReEREbarR = 0 := sub_eq_zero.mpr (exoticReEREbarR_comm_genH k)
  rw [hcomm, zero_mul, mul_zero, sub_zero]

theorem exoticReEREbarR_oo_M (a : Fin 8) (g2 : Fin 12) :
    (exoticReEREbarR * genM a - genM a * exoticReEREbarR) * smGenOp g2
      - smGenOp g2 * (exoticReEREbarR * genM a - genM a * exoticReEREbarR) = 0 := by
  have hcomm : exoticReEREbarR * genM a - genM a * exoticReEREbarR = 0 :=
    sub_eq_zero.mpr (exoticReEREbarR_comm_genM a)
  rw [hcomm, zero_mul, mul_zero, sub_zero]

theorem exoticReEREbarR_orderOne : OrderOneHolds exoticReEREbarR := by
  intro g1 g2
  fin_cases g1
  · show (exoticReEREbarR * genC - genC * exoticReEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReEREbarR * genC - genC * exoticReEREbarR) = 0
    exact exoticReEREbarR_oo_C g2
  · show (exoticReEREbarR * genH 0 - genH 0 * exoticReEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReEREbarR * genH 0 - genH 0 * exoticReEREbarR) = 0
    exact exoticReEREbarR_oo_H 0 g2
  · show (exoticReEREbarR * genH 1 - genH 1 * exoticReEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReEREbarR * genH 1 - genH 1 * exoticReEREbarR) = 0
    exact exoticReEREbarR_oo_H 1 g2
  · show (exoticReEREbarR * genH 2 - genH 2 * exoticReEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReEREbarR * genH 2 - genH 2 * exoticReEREbarR) = 0
    exact exoticReEREbarR_oo_H 2 g2
  · show (exoticReEREbarR * genM 0 - genM 0 * exoticReEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReEREbarR * genM 0 - genM 0 * exoticReEREbarR) = 0
    exact exoticReEREbarR_oo_M 0 g2
  · show (exoticReEREbarR * genM 1 - genM 1 * exoticReEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReEREbarR * genM 1 - genM 1 * exoticReEREbarR) = 0
    exact exoticReEREbarR_oo_M 1 g2
  · show (exoticReEREbarR * genM 2 - genM 2 * exoticReEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReEREbarR * genM 2 - genM 2 * exoticReEREbarR) = 0
    exact exoticReEREbarR_oo_M 2 g2
  · show (exoticReEREbarR * genM 3 - genM 3 * exoticReEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReEREbarR * genM 3 - genM 3 * exoticReEREbarR) = 0
    exact exoticReEREbarR_oo_M 3 g2
  · show (exoticReEREbarR * genM 4 - genM 4 * exoticReEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReEREbarR * genM 4 - genM 4 * exoticReEREbarR) = 0
    exact exoticReEREbarR_oo_M 4 g2
  · show (exoticReEREbarR * genM 5 - genM 5 * exoticReEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReEREbarR * genM 5 - genM 5 * exoticReEREbarR) = 0
    exact exoticReEREbarR_oo_M 5 g2
  · show (exoticReEREbarR * genM 6 - genM 6 * exoticReEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReEREbarR * genM 6 - genM 6 * exoticReEREbarR) = 0
    exact exoticReEREbarR_oo_M 6 g2
  · show (exoticReEREbarR * genM 7 - genM 7 * exoticReEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticReEREbarR * genM 7 - genM 7 * exoticReEREbarR) = 0
    exact exoticReEREbarR_oo_M 7 g2

-- ============================================================================
-- exoticImEREbarR : order-one
-- ============================================================================

theorem exoticImEREbarR_supp (i j : I32) (h : exoticImEREbarR i j ≠ 0) :
    (i = 9 ∧ j = 25) ∨ (i = 25 ∧ j = 9) := by
  unfold exoticImEREbarR at h
  by_cases h1 : (i = 9 ∧ j = 25)
  · rcases h1 with ⟨rfl,rfl⟩
    · simp
  · by_cases h2 : (i = 25 ∧ j = 9)
    · rcases h2 with ⟨rfl,rfl⟩
      · simp
    · simp [h1, h2] at h

theorem exoticImEREbarR_CVal_const (x y : I32) (h : exoticImEREbarR x y ≠ 0) :
    genCVal x = genCVal y := by
  rcases exoticImEREbarR_supp x y h with ⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; simp [genCVal]
  · rw [hx, hy]; simp [genCVal]

theorem exoticImEREbarR_comm_genC : exoticImEREbarR * genC = genC * exoticImEREbarR :=
  comm_genC_of_CVal_const exoticImEREbarR exoticImEREbarR_CVal_const

theorem exoticImEREbarR_oo_C (g2 : Fin 12) :
    (exoticImEREbarR * genC - genC * exoticImEREbarR) * smGenOp g2
      - smGenOp g2 * (exoticImEREbarR * genC - genC * exoticImEREbarR) = 0 := by
  have hcomm : exoticImEREbarR * genC - genC * exoticImEREbarR = 0 := sub_eq_zero.mpr exoticImEREbarR_comm_genC
  rw [hcomm, zero_mul, mul_zero, sub_zero]

theorem exoticImEREbarR_ge8 (x y : I32) (h : exoticImEREbarR x y ≠ 0) :
    8 ≤ x.val ∧ 8 ≤ y.val := by
  rcases exoticImEREbarR_supp x y h with ⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩

theorem exoticImEREbarR_comm_genH (k : Fin 3) : exoticImEREbarR * genH k = genH k * exoticImEREbarR :=
  comm_genH_of_ge8 exoticImEREbarR exoticImEREbarR_ge8 k

theorem exoticImEREbarR_oo_H (k : Fin 3) (g2 : Fin 12) :
    (exoticImEREbarR * genH k - genH k * exoticImEREbarR) * smGenOp g2
      - smGenOp g2 * (exoticImEREbarR * genH k - genH k * exoticImEREbarR) = 0 := by
  have hcomm : exoticImEREbarR * genH k - genH k * exoticImEREbarR = 0 := sub_eq_zero.mpr (exoticImEREbarR_comm_genH k)
  rw [hcomm, zero_mul, mul_zero, sub_zero]

theorem exoticImEREbarR_oo_M (a : Fin 8) (g2 : Fin 12) :
    (exoticImEREbarR * genM a - genM a * exoticImEREbarR) * smGenOp g2
      - smGenOp g2 * (exoticImEREbarR * genM a - genM a * exoticImEREbarR) = 0 := by
  have hcomm : exoticImEREbarR * genM a - genM a * exoticImEREbarR = 0 :=
    sub_eq_zero.mpr (exoticImEREbarR_comm_genM a)
  rw [hcomm, zero_mul, mul_zero, sub_zero]

theorem exoticImEREbarR_orderOne : OrderOneHolds exoticImEREbarR := by
  intro g1 g2
  fin_cases g1
  · show (exoticImEREbarR * genC - genC * exoticImEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImEREbarR * genC - genC * exoticImEREbarR) = 0
    exact exoticImEREbarR_oo_C g2
  · show (exoticImEREbarR * genH 0 - genH 0 * exoticImEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImEREbarR * genH 0 - genH 0 * exoticImEREbarR) = 0
    exact exoticImEREbarR_oo_H 0 g2
  · show (exoticImEREbarR * genH 1 - genH 1 * exoticImEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImEREbarR * genH 1 - genH 1 * exoticImEREbarR) = 0
    exact exoticImEREbarR_oo_H 1 g2
  · show (exoticImEREbarR * genH 2 - genH 2 * exoticImEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImEREbarR * genH 2 - genH 2 * exoticImEREbarR) = 0
    exact exoticImEREbarR_oo_H 2 g2
  · show (exoticImEREbarR * genM 0 - genM 0 * exoticImEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImEREbarR * genM 0 - genM 0 * exoticImEREbarR) = 0
    exact exoticImEREbarR_oo_M 0 g2
  · show (exoticImEREbarR * genM 1 - genM 1 * exoticImEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImEREbarR * genM 1 - genM 1 * exoticImEREbarR) = 0
    exact exoticImEREbarR_oo_M 1 g2
  · show (exoticImEREbarR * genM 2 - genM 2 * exoticImEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImEREbarR * genM 2 - genM 2 * exoticImEREbarR) = 0
    exact exoticImEREbarR_oo_M 2 g2
  · show (exoticImEREbarR * genM 3 - genM 3 * exoticImEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImEREbarR * genM 3 - genM 3 * exoticImEREbarR) = 0
    exact exoticImEREbarR_oo_M 3 g2
  · show (exoticImEREbarR * genM 4 - genM 4 * exoticImEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImEREbarR * genM 4 - genM 4 * exoticImEREbarR) = 0
    exact exoticImEREbarR_oo_M 4 g2
  · show (exoticImEREbarR * genM 5 - genM 5 * exoticImEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImEREbarR * genM 5 - genM 5 * exoticImEREbarR) = 0
    exact exoticImEREbarR_oo_M 5 g2
  · show (exoticImEREbarR * genM 6 - genM 6 * exoticImEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImEREbarR * genM 6 - genM 6 * exoticImEREbarR) = 0
    exact exoticImEREbarR_oo_M 6 g2
  · show (exoticImEREbarR * genM 7 - genM 7 * exoticImEREbarR) * smGenOp g2
        - smGenOp g2 * (exoticImEREbarR * genM 7 - genM 7 * exoticImEREbarR) = 0
    exact exoticImEREbarR_oo_M 7 g2

-- ============================================================================
-- exoticReULDR : order-one
-- ============================================================================

theorem exoticReULDR_supp (i j : I32) (h : exoticReULDR i j ≠ 0) :
    (i = 2 ∧ j = 11) ∨ (i = 11 ∧ j = 2) ∨ (i = 4 ∧ j = 13) ∨ (i = 13 ∧ j = 4) ∨ (i = 6 ∧ j = 15) ∨ (i = 15 ∧ j = 6) ∨ (i = 18 ∧ j = 27) ∨ (i = 27 ∧ j = 18) ∨ (i = 20 ∧ j = 29) ∨ (i = 29 ∧ j = 20) ∨ (i = 22 ∧ j = 31) ∨ (i = 31 ∧ j = 22) := by
  unfold exoticReULDR at h
  by_cases hs : (i = 2 ∧ j = 11) ∨ (i = 11 ∧ j = 2) ∨ (i = 4 ∧ j = 13) ∨ (i = 13 ∧ j = 4) ∨ (i = 6 ∧ j = 15) ∨ (i = 15 ∧ j = 6) ∨ (i = 18 ∧ j = 27) ∨ (i = 27 ∧ j = 18) ∨ (i = 20 ∧ j = 29) ∨ (i = 29 ∧ j = 20) ∨ (i = 22 ∧ j = 31) ∨ (i = 31 ∧ j = 22)
  · exact hs
  · rw [if_neg hs] at h
    exact absurd rfl h

theorem exoticReULDR_factor_CC (i j : I32) (h : exoticReULDR i j ≠ 0) :
    (genCVal j - genCVal i) * (genCOpVal j - genCOpVal i) = 0 := by
  rcases exoticReULDR_supp i j h with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]

theorem exoticReULDR_oo_C_C :
    (exoticReULDR * genC - genC * exoticReULDR) * smGenOp 0
      - smGenOp 0 * (exoticReULDR * genC - genC * exoticReULDR) = 0 :=
  oo_C_C_of_factor exoticReULDR exoticReULDR_factor_CC

theorem exoticReULDR_comm_genC_mem (i j : I32)
    (h : (exoticReULDR * genC - genC * exoticReULDR) i j ≠ 0) :
    (i = 2 ∨ i = 4 ∨ i = 6 ∨ i = 11 ∨ i = 13 ∨ i = 15) ∧ (j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 11 ∨ j = 13 ∨ j = 15) := by
  rw [comm_diag_entry _ _ _ (fun x y => genC_eq_diag x y) i j] at h
  have hE : exoticReULDR i j ≠ 0 := by
    intro h0; apply h; rw [h0, zero_mul]
  have hc : genCVal j - genCVal i ≠ 0 := by
    intro h0; apply h; rw [h0, mul_zero]
  rcases exoticReULDR_supp i j hE with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy] at hc; simp [genCVal] at hc

theorem exoticReULDR_not_mem_RC_of_ge16 {x : I32} (h : 16 ≤ x.val) :
    x ∉ ({2, 4, 6, 11, 13, 15} : Finset I32) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h

theorem exoticReULDR_oo_C_H (k : Fin 3) :
    (exoticReULDR * genC - genC * exoticReULDR) * (UJ * (genH k).transpose * UJ)
      - (UJ * (genH k).transpose * UJ) * (exoticReULDR * genC - genC * exoticReULDR) = 0 := by
  apply oo_disjoint _ _ _ {2, 4, 6, 11, 13, 15}
  · intro i j hij
    obtain ⟨hi, hj⟩ := exoticReULDR_comm_genC_mem i j hij
    constructor
    · simp only [Finset.mem_insert, Finset.mem_singleton]; exact hi
    · simp only [Finset.mem_insert, Finset.mem_singleton]; exact hj
  · intro x y hxy
    have hsupp := UJ_genH_transpose_UJ_supp k x y hxy
    exact ⟨exoticReULDR_not_mem_RC_of_ge16 hsupp.1, exoticReULDR_not_mem_RC_of_ge16 hsupp.2.2.1⟩

theorem exoticReULDR_oo_C_M (a : Fin 8) :
    (exoticReULDR * genC - genC * exoticReULDR) * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ) * (exoticReULDR * genC - genC * exoticReULDR) = 0 :=
  double_comm_of_comm exoticReULDR genC _ (exoticReULDR_comm_MOp a) (comm_genC_MOp a)

theorem exoticReULDR_oo_C (g2 : Fin 12) :
    (exoticReULDR * genC - genC * exoticReULDR) * smGenOp g2
      - smGenOp g2 * (exoticReULDR * genC - genC * exoticReULDR) = 0 := by
  fin_cases g2
  · exact exoticReULDR_oo_C_C
  · show (exoticReULDR * genC - genC * exoticReULDR) * (UJ * (genH 0).transpose * UJ)
        - (UJ * (genH 0).transpose * UJ) * (exoticReULDR * genC - genC * exoticReULDR) = 0
    exact exoticReULDR_oo_C_H 0
  · show (exoticReULDR * genC - genC * exoticReULDR) * (UJ * (genH 1).transpose * UJ)
        - (UJ * (genH 1).transpose * UJ) * (exoticReULDR * genC - genC * exoticReULDR) = 0
    exact exoticReULDR_oo_C_H 1
  · show (exoticReULDR * genC - genC * exoticReULDR) * (UJ * (genH 2).transpose * UJ)
        - (UJ * (genH 2).transpose * UJ) * (exoticReULDR * genC - genC * exoticReULDR) = 0
    exact exoticReULDR_oo_C_H 2
  · show (exoticReULDR * genC - genC * exoticReULDR) * (UJ * (genM 0).transpose * UJ)
        - (UJ * (genM 0).transpose * UJ) * (exoticReULDR * genC - genC * exoticReULDR) = 0
    exact exoticReULDR_oo_C_M 0
  · show (exoticReULDR * genC - genC * exoticReULDR) * (UJ * (genM 1).transpose * UJ)
        - (UJ * (genM 1).transpose * UJ) * (exoticReULDR * genC - genC * exoticReULDR) = 0
    exact exoticReULDR_oo_C_M 1
  · show (exoticReULDR * genC - genC * exoticReULDR) * (UJ * (genM 2).transpose * UJ)
        - (UJ * (genM 2).transpose * UJ) * (exoticReULDR * genC - genC * exoticReULDR) = 0
    exact exoticReULDR_oo_C_M 2
  · show (exoticReULDR * genC - genC * exoticReULDR) * (UJ * (genM 3).transpose * UJ)
        - (UJ * (genM 3).transpose * UJ) * (exoticReULDR * genC - genC * exoticReULDR) = 0
    exact exoticReULDR_oo_C_M 3
  · show (exoticReULDR * genC - genC * exoticReULDR) * (UJ * (genM 4).transpose * UJ)
        - (UJ * (genM 4).transpose * UJ) * (exoticReULDR * genC - genC * exoticReULDR) = 0
    exact exoticReULDR_oo_C_M 4
  · show (exoticReULDR * genC - genC * exoticReULDR) * (UJ * (genM 5).transpose * UJ)
        - (UJ * (genM 5).transpose * UJ) * (exoticReULDR * genC - genC * exoticReULDR) = 0
    exact exoticReULDR_oo_C_M 5
  · show (exoticReULDR * genC - genC * exoticReULDR) * (UJ * (genM 6).transpose * UJ)
        - (UJ * (genM 6).transpose * UJ) * (exoticReULDR * genC - genC * exoticReULDR) = 0
    exact exoticReULDR_oo_C_M 6
  · show (exoticReULDR * genC - genC * exoticReULDR) * (UJ * (genM 7).transpose * UJ)
        - (UJ * (genM 7).transpose * UJ) * (exoticReULDR * genC - genC * exoticReULDR) = 0
    exact exoticReULDR_oo_C_M 7

theorem exoticReULDR_oo_M (a : Fin 8) (g2 : Fin 12) :
    (exoticReULDR * genM a - genM a * exoticReULDR) * smGenOp g2
      - smGenOp g2 * (exoticReULDR * genM a - genM a * exoticReULDR) = 0 := by
  have hcomm : exoticReULDR * genM a - genM a * exoticReULDR = 0 :=
    sub_eq_zero.mpr (exoticReULDR_comm_genM a)
  rw [hcomm, zero_mul, mul_zero, sub_zero]

theorem exoticReULDR_genCOpVal_2_eq : genCOpVal (2 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticReULDR_genCOpVal_3_eq : genCOpVal (3 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticReULDR_genCOpVal_4_eq : genCOpVal (4 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticReULDR_genCOpVal_5_eq : genCOpVal (5 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticReULDR_genCOpVal_6_eq : genCOpVal (6 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticReULDR_genCOpVal_7_eq : genCOpVal (7 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticReULDR_genCOpVal_11_eq : genCOpVal (11 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticReULDR_genCOpVal_13_eq : genCOpVal (13 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticReULDR_genCOpVal_15_eq : genCOpVal (15 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]

theorem exoticReULDR_CH_supp (k : Fin 3) (i j : I32)
    (h : (exoticReULDR * genH k - genH k * exoticReULDR) i j ≠ 0) :
    (i = 11 ∧ j = 2) ∨ (i = 11 ∧ j = 3) ∨ (i = 13 ∧ j = 4) ∨ (i = 13 ∧ j = 5) ∨ (i = 15 ∧ j = 6) ∨ (i = 15 ∧ j = 7) ∨ (i = 2 ∧ j = 11) ∨ (i = 3 ∧ j = 11) ∨ (i = 4 ∧ j = 13) ∨ (i = 5 ∧ j = 13) ∨ (i = 6 ∧ j = 15) ∨ (i = 7 ∧ j = 15) := by
  simp only [Matrix.sub_apply] at h
  by_cases h1 : (exoticReULDR * genH k) i j = 0
  · have h2 : (genH k * exoticReULDR) i j ≠ 0 := by
      intro hc
      apply h
      rw [h1, hc, sub_zero]
    simp only [Matrix.mul_apply] at h2
    have hex : ∃ l, genH k i l * exoticReULDR l j ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply h2
      exact Finset.sum_eq_zero (fun l _ => hc l)
    obtain ⟨l, hl⟩ := hex
    have hGl : genH k i l ≠ 0 := fun h0 => hl (by rw [h0, zero_mul])
    have hEl : exoticReULDR l j ≠ 0 := fun h0 => hl (by rw [h0, mul_zero])
    have hblock := genH_supp_block k i l hGl
    have hsupp := exoticReULDR_supp l j hEl
    rcases hsupp with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
    · rw [hx] at hblock
      have hi : i.val = 2 ∨ i.val = 3 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hi with hv | hv
      · have hatom : i = 2 ∧ j = 11 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 2 ∧ j = 11) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 3 ∧ j = 11 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 3 ∧ j = 11) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hx] at hblock; omega
    · rw [hx] at hblock
      have hi : i.val = 4 ∨ i.val = 5 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hi with hv | hv
      · have hatom : i = 4 ∧ j = 13 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 4 ∧ j = 13) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 5 ∧ j = 13 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 5 ∧ j = 13) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hx] at hblock; omega
    · rw [hx] at hblock
      have hi : i.val = 6 ∨ i.val = 7 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hi with hv | hv
      · have hatom : i = 6 ∧ j = 15 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 6 ∧ j = 15) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 7 ∧ j = 15 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 7 ∧ j = 15) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
  · have h1ne : (exoticReULDR * genH k) i j ≠ 0 := h1
    simp only [Matrix.mul_apply] at h1ne
    have hex : ∃ l, exoticReULDR i l * genH k l j ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply h1ne
      exact Finset.sum_eq_zero (fun l _ => hc l)
    obtain ⟨l, hl⟩ := hex
    have hEl : exoticReULDR i l ≠ 0 := fun h0 => hl (by rw [h0, zero_mul])
    have hG : genH k l j ≠ 0 := fun h0 => hl (by rw [h0, mul_zero])
    have hblock := genH_supp_block k l j hG
    have hsupp := exoticReULDR_supp i l hEl
    rcases hsupp with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
    · rw [hy] at hblock; omega
    · rw [hy] at hblock
      have hj : j.val = 2 ∨ j.val = 3 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hj with hv | hv
      · have hatom : i = 11 ∧ j = 2 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 11 ∧ j = 2) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 11 ∧ j = 3 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 11 ∧ j = 3) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hy] at hblock; omega
    · rw [hy] at hblock
      have hj : j.val = 4 ∨ j.val = 5 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hj with hv | hv
      · have hatom : i = 13 ∧ j = 4 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 13 ∧ j = 4) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 13 ∧ j = 5 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 13 ∧ j = 5) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hy] at hblock; omega
    · rw [hy] at hblock
      have hj : j.val = 6 ∨ j.val = 7 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hj with hv | hv
      · have hatom : i = 15 ∧ j = 6 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 15 ∧ j = 6) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 15 ∧ j = 7 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 15 ∧ j = 7) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega

theorem exoticReULDR_oo_H_C (k : Fin 3) :
    (exoticReULDR * genH k - genH k * exoticReULDR) * smGenOp 0
      - smGenOp 0 * (exoticReULDR * genH k - genH k * exoticReULDR) = 0 := by
  have hD : ∀ x y : I32, smGenOp 0 x y = if x = y then genCOpVal x else 0 :=
    fun x y => smGenOp_zero_eq x y
  ext i j
  simp only [Matrix.zero_apply, Matrix.sub_apply]
  have hCD : ((exoticReULDR * genH k - genH k * exoticReULDR) * smGenOp 0) i j
           = (exoticReULDR * genH k - genH k * exoticReULDR) i j * genCOpVal j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hD j j, if_pos rfl]
    · intro l _ hlj
      rw [hD l j, if_neg hlj, mul_zero]
    · intro hcon; exact absurd (Finset.mem_univ j) hcon
  have hDC : (smGenOp 0 * (exoticReULDR * genH k - genH k * exoticReULDR)) i j
           = genCOpVal i * (exoticReULDR * genH k - genH k * exoticReULDR) i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hD i i, if_pos rfl]
    · intro l _ hli
      rw [hD i l, if_neg (Ne.symm hli), zero_mul]
    · intro hcon; exact absurd (Finset.mem_univ i) hcon
  rw [hCD, hDC]
  by_cases hC : (exoticReULDR * genH k - genH k * exoticReULDR) i j = 0
  · rw [hC, zero_mul, mul_zero, sub_zero]
  · have hsupp := exoticReULDR_CH_supp k i j hC
    have hw : genCOpVal j = genCOpVal i := by
      rcases hsupp with ⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩
      · rw [hix, hjy, exoticReULDR_genCOpVal_2_eq, exoticReULDR_genCOpVal_11_eq]
      · rw [hix, hjy, exoticReULDR_genCOpVal_3_eq, exoticReULDR_genCOpVal_11_eq]
      · rw [hix, hjy, exoticReULDR_genCOpVal_4_eq, exoticReULDR_genCOpVal_13_eq]
      · rw [hix, hjy, exoticReULDR_genCOpVal_5_eq, exoticReULDR_genCOpVal_13_eq]
      · rw [hix, hjy, exoticReULDR_genCOpVal_6_eq, exoticReULDR_genCOpVal_15_eq]
      · rw [hix, hjy, exoticReULDR_genCOpVal_7_eq, exoticReULDR_genCOpVal_15_eq]
      · rw [hix, hjy, exoticReULDR_genCOpVal_11_eq, exoticReULDR_genCOpVal_2_eq]
      · rw [hix, hjy, exoticReULDR_genCOpVal_11_eq, exoticReULDR_genCOpVal_3_eq]
      · rw [hix, hjy, exoticReULDR_genCOpVal_13_eq, exoticReULDR_genCOpVal_4_eq]
      · rw [hix, hjy, exoticReULDR_genCOpVal_13_eq, exoticReULDR_genCOpVal_5_eq]
      · rw [hix, hjy, exoticReULDR_genCOpVal_15_eq, exoticReULDR_genCOpVal_6_eq]
      · rw [hix, hjy, exoticReULDR_genCOpVal_15_eq, exoticReULDR_genCOpVal_7_eq]
    rw [hw, mul_comm, sub_self]

theorem exoticReULDR_not_mem_RSH_of_ge16 {x : I32} (h : 16 ≤ x.val) :
    x ∉ ({2, 3, 4, 5, 6, 7, 11, 13, 15} : Finset I32) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h

theorem exoticReULDR_oo_H_H (k : Fin 3) (a : Fin 3) :
    (exoticReULDR * genH k - genH k * exoticReULDR) * (UJ * (genH a).transpose * UJ)
      - (UJ * (genH a).transpose * UJ) * (exoticReULDR * genH k - genH k * exoticReULDR) = 0 := by
  apply oo_disjoint _ _ _ {2, 3, 4, 5, 6, 7, 11, 13, 15}
  · intro i j hij
    have hsupp := exoticReULDR_CH_supp k i j hij
    rcases hsupp with ⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
  · intro x y hxy
    have hsupp := UJ_genH_transpose_UJ_supp a x y hxy
    exact ⟨exoticReULDR_not_mem_RSH_of_ge16 hsupp.1, exoticReULDR_not_mem_RSH_of_ge16 hsupp.2.2.1⟩

theorem exoticReULDR_oo_H_M (k : Fin 3) (a : Fin 8) :
    (exoticReULDR * genH k - genH k * exoticReULDR) * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ) * (exoticReULDR * genH k - genH k * exoticReULDR) = 0 :=
  double_comm_of_comm exoticReULDR (genH k) _ (exoticReULDR_comm_MOp a) (comm_genH_MOp k a)

theorem exoticReULDR_oo_H (k : Fin 3) (g2 : Fin 12) :
    (exoticReULDR * genH k - genH k * exoticReULDR) * smGenOp g2
      - smGenOp g2 * (exoticReULDR * genH k - genH k * exoticReULDR) = 0 := by
  fin_cases g2
  · exact exoticReULDR_oo_H_C k
  · show (exoticReULDR * genH k - genH k * exoticReULDR) * (UJ * (genH 0).transpose * UJ)
        - (UJ * (genH 0).transpose * UJ) * (exoticReULDR * genH k - genH k * exoticReULDR) = 0
    exact exoticReULDR_oo_H_H k 0
  · show (exoticReULDR * genH k - genH k * exoticReULDR) * (UJ * (genH 1).transpose * UJ)
        - (UJ * (genH 1).transpose * UJ) * (exoticReULDR * genH k - genH k * exoticReULDR) = 0
    exact exoticReULDR_oo_H_H k 1
  · show (exoticReULDR * genH k - genH k * exoticReULDR) * (UJ * (genH 2).transpose * UJ)
        - (UJ * (genH 2).transpose * UJ) * (exoticReULDR * genH k - genH k * exoticReULDR) = 0
    exact exoticReULDR_oo_H_H k 2
  · show (exoticReULDR * genH k - genH k * exoticReULDR) * (UJ * (genM 0).transpose * UJ)
        - (UJ * (genM 0).transpose * UJ) * (exoticReULDR * genH k - genH k * exoticReULDR) = 0
    exact exoticReULDR_oo_H_M k 0
  · show (exoticReULDR * genH k - genH k * exoticReULDR) * (UJ * (genM 1).transpose * UJ)
        - (UJ * (genM 1).transpose * UJ) * (exoticReULDR * genH k - genH k * exoticReULDR) = 0
    exact exoticReULDR_oo_H_M k 1
  · show (exoticReULDR * genH k - genH k * exoticReULDR) * (UJ * (genM 2).transpose * UJ)
        - (UJ * (genM 2).transpose * UJ) * (exoticReULDR * genH k - genH k * exoticReULDR) = 0
    exact exoticReULDR_oo_H_M k 2
  · show (exoticReULDR * genH k - genH k * exoticReULDR) * (UJ * (genM 3).transpose * UJ)
        - (UJ * (genM 3).transpose * UJ) * (exoticReULDR * genH k - genH k * exoticReULDR) = 0
    exact exoticReULDR_oo_H_M k 3
  · show (exoticReULDR * genH k - genH k * exoticReULDR) * (UJ * (genM 4).transpose * UJ)
        - (UJ * (genM 4).transpose * UJ) * (exoticReULDR * genH k - genH k * exoticReULDR) = 0
    exact exoticReULDR_oo_H_M k 4
  · show (exoticReULDR * genH k - genH k * exoticReULDR) * (UJ * (genM 5).transpose * UJ)
        - (UJ * (genM 5).transpose * UJ) * (exoticReULDR * genH k - genH k * exoticReULDR) = 0
    exact exoticReULDR_oo_H_M k 5
  · show (exoticReULDR * genH k - genH k * exoticReULDR) * (UJ * (genM 6).transpose * UJ)
        - (UJ * (genM 6).transpose * UJ) * (exoticReULDR * genH k - genH k * exoticReULDR) = 0
    exact exoticReULDR_oo_H_M k 6
  · show (exoticReULDR * genH k - genH k * exoticReULDR) * (UJ * (genM 7).transpose * UJ)
        - (UJ * (genM 7).transpose * UJ) * (exoticReULDR * genH k - genH k * exoticReULDR) = 0
    exact exoticReULDR_oo_H_M k 7

theorem exoticReULDR_orderOne : OrderOneHolds exoticReULDR := by
  intro g1 g2
  fin_cases g1
  · show (exoticReULDR * genC - genC * exoticReULDR) * smGenOp g2
        - smGenOp g2 * (exoticReULDR * genC - genC * exoticReULDR) = 0
    exact exoticReULDR_oo_C g2
  · show (exoticReULDR * genH 0 - genH 0 * exoticReULDR) * smGenOp g2
        - smGenOp g2 * (exoticReULDR * genH 0 - genH 0 * exoticReULDR) = 0
    exact exoticReULDR_oo_H 0 g2
  · show (exoticReULDR * genH 1 - genH 1 * exoticReULDR) * smGenOp g2
        - smGenOp g2 * (exoticReULDR * genH 1 - genH 1 * exoticReULDR) = 0
    exact exoticReULDR_oo_H 1 g2
  · show (exoticReULDR * genH 2 - genH 2 * exoticReULDR) * smGenOp g2
        - smGenOp g2 * (exoticReULDR * genH 2 - genH 2 * exoticReULDR) = 0
    exact exoticReULDR_oo_H 2 g2
  · show (exoticReULDR * genM 0 - genM 0 * exoticReULDR) * smGenOp g2
        - smGenOp g2 * (exoticReULDR * genM 0 - genM 0 * exoticReULDR) = 0
    exact exoticReULDR_oo_M 0 g2
  · show (exoticReULDR * genM 1 - genM 1 * exoticReULDR) * smGenOp g2
        - smGenOp g2 * (exoticReULDR * genM 1 - genM 1 * exoticReULDR) = 0
    exact exoticReULDR_oo_M 1 g2
  · show (exoticReULDR * genM 2 - genM 2 * exoticReULDR) * smGenOp g2
        - smGenOp g2 * (exoticReULDR * genM 2 - genM 2 * exoticReULDR) = 0
    exact exoticReULDR_oo_M 2 g2
  · show (exoticReULDR * genM 3 - genM 3 * exoticReULDR) * smGenOp g2
        - smGenOp g2 * (exoticReULDR * genM 3 - genM 3 * exoticReULDR) = 0
    exact exoticReULDR_oo_M 3 g2
  · show (exoticReULDR * genM 4 - genM 4 * exoticReULDR) * smGenOp g2
        - smGenOp g2 * (exoticReULDR * genM 4 - genM 4 * exoticReULDR) = 0
    exact exoticReULDR_oo_M 4 g2
  · show (exoticReULDR * genM 5 - genM 5 * exoticReULDR) * smGenOp g2
        - smGenOp g2 * (exoticReULDR * genM 5 - genM 5 * exoticReULDR) = 0
    exact exoticReULDR_oo_M 5 g2
  · show (exoticReULDR * genM 6 - genM 6 * exoticReULDR) * smGenOp g2
        - smGenOp g2 * (exoticReULDR * genM 6 - genM 6 * exoticReULDR) = 0
    exact exoticReULDR_oo_M 6 g2
  · show (exoticReULDR * genM 7 - genM 7 * exoticReULDR) * smGenOp g2
        - smGenOp g2 * (exoticReULDR * genM 7 - genM 7 * exoticReULDR) = 0
    exact exoticReULDR_oo_M 7 g2

-- ============================================================================
-- exoticImULDR : order-one
-- ============================================================================

theorem exoticImULDR_supp (i j : I32) (h : exoticImULDR i j ≠ 0) :
    (i = 2 ∧ j = 11) ∨ (i = 4 ∧ j = 13) ∨ (i = 6 ∧ j = 15) ∨ (i = 27 ∧ j = 18) ∨ (i = 29 ∧ j = 20) ∨ (i = 31 ∧ j = 22) ∨ (i = 11 ∧ j = 2) ∨ (i = 13 ∧ j = 4) ∨ (i = 15 ∧ j = 6) ∨ (i = 18 ∧ j = 27) ∨ (i = 20 ∧ j = 29) ∨ (i = 22 ∧ j = 31) := by
  unfold exoticImULDR at h
  by_cases h1 : (i = 2 ∧ j = 11) ∨ (i = 4 ∧ j = 13) ∨ (i = 6 ∧ j = 15) ∨ (i = 27 ∧ j = 18) ∨ (i = 29 ∧ j = 20) ∨ (i = 31 ∧ j = 22)
  · rcases h1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
  · by_cases h2 : (i = 11 ∧ j = 2) ∨ (i = 13 ∧ j = 4) ∨ (i = 15 ∧ j = 6) ∨ (i = 18 ∧ j = 27) ∨ (i = 20 ∧ j = 29) ∨ (i = 22 ∧ j = 31)
    · rcases h2 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp
    · simp [h1, h2] at h

theorem exoticImULDR_factor_CC (i j : I32) (h : exoticImULDR i j ≠ 0) :
    (genCVal j - genCVal i) * (genCOpVal j - genCOpVal i) = 0 := by
  rcases exoticImULDR_supp i j h with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]

theorem exoticImULDR_oo_C_C :
    (exoticImULDR * genC - genC * exoticImULDR) * smGenOp 0
      - smGenOp 0 * (exoticImULDR * genC - genC * exoticImULDR) = 0 :=
  oo_C_C_of_factor exoticImULDR exoticImULDR_factor_CC

theorem exoticImULDR_comm_genC_mem (i j : I32)
    (h : (exoticImULDR * genC - genC * exoticImULDR) i j ≠ 0) :
    (i = 2 ∨ i = 4 ∨ i = 6 ∨ i = 11 ∨ i = 13 ∨ i = 15) ∧ (j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 11 ∨ j = 13 ∨ j = 15) := by
  rw [comm_diag_entry _ _ _ (fun x y => genC_eq_diag x y) i j] at h
  have hE : exoticImULDR i j ≠ 0 := by
    intro h0; apply h; rw [h0, zero_mul]
  have hc : genCVal j - genCVal i ≠ 0 := by
    intro h0; apply h; rw [h0, mul_zero]
  rcases exoticImULDR_supp i j hE with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy] at hc; simp [genCVal] at hc

theorem exoticImULDR_not_mem_RC_of_ge16 {x : I32} (h : 16 ≤ x.val) :
    x ∉ ({2, 4, 6, 11, 13, 15} : Finset I32) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h

theorem exoticImULDR_oo_C_H (k : Fin 3) :
    (exoticImULDR * genC - genC * exoticImULDR) * (UJ * (genH k).transpose * UJ)
      - (UJ * (genH k).transpose * UJ) * (exoticImULDR * genC - genC * exoticImULDR) = 0 := by
  apply oo_disjoint _ _ _ {2, 4, 6, 11, 13, 15}
  · intro i j hij
    obtain ⟨hi, hj⟩ := exoticImULDR_comm_genC_mem i j hij
    constructor
    · simp only [Finset.mem_insert, Finset.mem_singleton]; exact hi
    · simp only [Finset.mem_insert, Finset.mem_singleton]; exact hj
  · intro x y hxy
    have hsupp := UJ_genH_transpose_UJ_supp k x y hxy
    exact ⟨exoticImULDR_not_mem_RC_of_ge16 hsupp.1, exoticImULDR_not_mem_RC_of_ge16 hsupp.2.2.1⟩

theorem exoticImULDR_oo_C_M (a : Fin 8) :
    (exoticImULDR * genC - genC * exoticImULDR) * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ) * (exoticImULDR * genC - genC * exoticImULDR) = 0 :=
  double_comm_of_comm exoticImULDR genC _ (exoticImULDR_comm_MOp a) (comm_genC_MOp a)

theorem exoticImULDR_oo_C (g2 : Fin 12) :
    (exoticImULDR * genC - genC * exoticImULDR) * smGenOp g2
      - smGenOp g2 * (exoticImULDR * genC - genC * exoticImULDR) = 0 := by
  fin_cases g2
  · exact exoticImULDR_oo_C_C
  · show (exoticImULDR * genC - genC * exoticImULDR) * (UJ * (genH 0).transpose * UJ)
        - (UJ * (genH 0).transpose * UJ) * (exoticImULDR * genC - genC * exoticImULDR) = 0
    exact exoticImULDR_oo_C_H 0
  · show (exoticImULDR * genC - genC * exoticImULDR) * (UJ * (genH 1).transpose * UJ)
        - (UJ * (genH 1).transpose * UJ) * (exoticImULDR * genC - genC * exoticImULDR) = 0
    exact exoticImULDR_oo_C_H 1
  · show (exoticImULDR * genC - genC * exoticImULDR) * (UJ * (genH 2).transpose * UJ)
        - (UJ * (genH 2).transpose * UJ) * (exoticImULDR * genC - genC * exoticImULDR) = 0
    exact exoticImULDR_oo_C_H 2
  · show (exoticImULDR * genC - genC * exoticImULDR) * (UJ * (genM 0).transpose * UJ)
        - (UJ * (genM 0).transpose * UJ) * (exoticImULDR * genC - genC * exoticImULDR) = 0
    exact exoticImULDR_oo_C_M 0
  · show (exoticImULDR * genC - genC * exoticImULDR) * (UJ * (genM 1).transpose * UJ)
        - (UJ * (genM 1).transpose * UJ) * (exoticImULDR * genC - genC * exoticImULDR) = 0
    exact exoticImULDR_oo_C_M 1
  · show (exoticImULDR * genC - genC * exoticImULDR) * (UJ * (genM 2).transpose * UJ)
        - (UJ * (genM 2).transpose * UJ) * (exoticImULDR * genC - genC * exoticImULDR) = 0
    exact exoticImULDR_oo_C_M 2
  · show (exoticImULDR * genC - genC * exoticImULDR) * (UJ * (genM 3).transpose * UJ)
        - (UJ * (genM 3).transpose * UJ) * (exoticImULDR * genC - genC * exoticImULDR) = 0
    exact exoticImULDR_oo_C_M 3
  · show (exoticImULDR * genC - genC * exoticImULDR) * (UJ * (genM 4).transpose * UJ)
        - (UJ * (genM 4).transpose * UJ) * (exoticImULDR * genC - genC * exoticImULDR) = 0
    exact exoticImULDR_oo_C_M 4
  · show (exoticImULDR * genC - genC * exoticImULDR) * (UJ * (genM 5).transpose * UJ)
        - (UJ * (genM 5).transpose * UJ) * (exoticImULDR * genC - genC * exoticImULDR) = 0
    exact exoticImULDR_oo_C_M 5
  · show (exoticImULDR * genC - genC * exoticImULDR) * (UJ * (genM 6).transpose * UJ)
        - (UJ * (genM 6).transpose * UJ) * (exoticImULDR * genC - genC * exoticImULDR) = 0
    exact exoticImULDR_oo_C_M 6
  · show (exoticImULDR * genC - genC * exoticImULDR) * (UJ * (genM 7).transpose * UJ)
        - (UJ * (genM 7).transpose * UJ) * (exoticImULDR * genC - genC * exoticImULDR) = 0
    exact exoticImULDR_oo_C_M 7

theorem exoticImULDR_oo_M (a : Fin 8) (g2 : Fin 12) :
    (exoticImULDR * genM a - genM a * exoticImULDR) * smGenOp g2
      - smGenOp g2 * (exoticImULDR * genM a - genM a * exoticImULDR) = 0 := by
  have hcomm : exoticImULDR * genM a - genM a * exoticImULDR = 0 :=
    sub_eq_zero.mpr (exoticImULDR_comm_genM a)
  rw [hcomm, zero_mul, mul_zero, sub_zero]

theorem exoticImULDR_genCOpVal_2_eq : genCOpVal (2 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticImULDR_genCOpVal_3_eq : genCOpVal (3 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticImULDR_genCOpVal_4_eq : genCOpVal (4 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticImULDR_genCOpVal_5_eq : genCOpVal (5 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticImULDR_genCOpVal_6_eq : genCOpVal (6 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticImULDR_genCOpVal_7_eq : genCOpVal (7 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticImULDR_genCOpVal_11_eq : genCOpVal (11 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticImULDR_genCOpVal_13_eq : genCOpVal (13 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticImULDR_genCOpVal_15_eq : genCOpVal (15 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]

theorem exoticImULDR_CH_supp (k : Fin 3) (i j : I32)
    (h : (exoticImULDR * genH k - genH k * exoticImULDR) i j ≠ 0) :
    (i = 11 ∧ j = 2) ∨ (i = 11 ∧ j = 3) ∨ (i = 13 ∧ j = 4) ∨ (i = 13 ∧ j = 5) ∨ (i = 15 ∧ j = 6) ∨ (i = 15 ∧ j = 7) ∨ (i = 2 ∧ j = 11) ∨ (i = 3 ∧ j = 11) ∨ (i = 4 ∧ j = 13) ∨ (i = 5 ∧ j = 13) ∨ (i = 6 ∧ j = 15) ∨ (i = 7 ∧ j = 15) := by
  simp only [Matrix.sub_apply] at h
  by_cases h1 : (exoticImULDR * genH k) i j = 0
  · have h2 : (genH k * exoticImULDR) i j ≠ 0 := by
      intro hc
      apply h
      rw [h1, hc, sub_zero]
    simp only [Matrix.mul_apply] at h2
    have hex : ∃ l, genH k i l * exoticImULDR l j ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply h2
      exact Finset.sum_eq_zero (fun l _ => hc l)
    obtain ⟨l, hl⟩ := hex
    have hGl : genH k i l ≠ 0 := fun h0 => hl (by rw [h0, zero_mul])
    have hEl : exoticImULDR l j ≠ 0 := fun h0 => hl (by rw [h0, mul_zero])
    have hblock := genH_supp_block k i l hGl
    have hsupp := exoticImULDR_supp l j hEl
    rcases hsupp with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
    · rw [hx] at hblock
      have hi : i.val = 2 ∨ i.val = 3 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hi with hv | hv
      · have hatom : i = 2 ∧ j = 11 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 2 ∧ j = 11) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 3 ∧ j = 11 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 3 ∧ j = 11) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hx] at hblock
      have hi : i.val = 4 ∨ i.val = 5 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hi with hv | hv
      · have hatom : i = 4 ∧ j = 13 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 4 ∧ j = 13) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 5 ∧ j = 13 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 5 ∧ j = 13) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hx] at hblock
      have hi : i.val = 6 ∨ i.val = 7 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hi with hv | hv
      · have hatom : i = 6 ∧ j = 15 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 6 ∧ j = 15) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 7 ∧ j = 15 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 7 ∧ j = 15) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
  · have h1ne : (exoticImULDR * genH k) i j ≠ 0 := h1
    simp only [Matrix.mul_apply] at h1ne
    have hex : ∃ l, exoticImULDR i l * genH k l j ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply h1ne
      exact Finset.sum_eq_zero (fun l _ => hc l)
    obtain ⟨l, hl⟩ := hex
    have hEl : exoticImULDR i l ≠ 0 := fun h0 => hl (by rw [h0, zero_mul])
    have hG : genH k l j ≠ 0 := fun h0 => hl (by rw [h0, mul_zero])
    have hblock := genH_supp_block k l j hG
    have hsupp := exoticImULDR_supp i l hEl
    rcases hsupp with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega
    · rw [hy] at hblock
      have hj : j.val = 2 ∨ j.val = 3 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hj with hv | hv
      · have hatom : i = 11 ∧ j = 2 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 11 ∧ j = 2) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 11 ∧ j = 3 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 11 ∧ j = 3) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hy] at hblock
      have hj : j.val = 4 ∨ j.val = 5 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hj with hv | hv
      · have hatom : i = 13 ∧ j = 4 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 13 ∧ j = 4) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 13 ∧ j = 5 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 13 ∧ j = 5) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hy] at hblock
      have hj : j.val = 6 ∨ j.val = 7 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hj with hv | hv
      · have hatom : i = 15 ∧ j = 6 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 15 ∧ j = 6) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 15 ∧ j = 7 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 15 ∧ j = 7) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega

theorem exoticImULDR_oo_H_C (k : Fin 3) :
    (exoticImULDR * genH k - genH k * exoticImULDR) * smGenOp 0
      - smGenOp 0 * (exoticImULDR * genH k - genH k * exoticImULDR) = 0 := by
  have hD : ∀ x y : I32, smGenOp 0 x y = if x = y then genCOpVal x else 0 :=
    fun x y => smGenOp_zero_eq x y
  ext i j
  simp only [Matrix.zero_apply, Matrix.sub_apply]
  have hCD : ((exoticImULDR * genH k - genH k * exoticImULDR) * smGenOp 0) i j
           = (exoticImULDR * genH k - genH k * exoticImULDR) i j * genCOpVal j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hD j j, if_pos rfl]
    · intro l _ hlj
      rw [hD l j, if_neg hlj, mul_zero]
    · intro hcon; exact absurd (Finset.mem_univ j) hcon
  have hDC : (smGenOp 0 * (exoticImULDR * genH k - genH k * exoticImULDR)) i j
           = genCOpVal i * (exoticImULDR * genH k - genH k * exoticImULDR) i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hD i i, if_pos rfl]
    · intro l _ hli
      rw [hD i l, if_neg (Ne.symm hli), zero_mul]
    · intro hcon; exact absurd (Finset.mem_univ i) hcon
  rw [hCD, hDC]
  by_cases hC : (exoticImULDR * genH k - genH k * exoticImULDR) i j = 0
  · rw [hC, zero_mul, mul_zero, sub_zero]
  · have hsupp := exoticImULDR_CH_supp k i j hC
    have hw : genCOpVal j = genCOpVal i := by
      rcases hsupp with ⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩
      · rw [hix, hjy, exoticImULDR_genCOpVal_2_eq, exoticImULDR_genCOpVal_11_eq]
      · rw [hix, hjy, exoticImULDR_genCOpVal_3_eq, exoticImULDR_genCOpVal_11_eq]
      · rw [hix, hjy, exoticImULDR_genCOpVal_4_eq, exoticImULDR_genCOpVal_13_eq]
      · rw [hix, hjy, exoticImULDR_genCOpVal_5_eq, exoticImULDR_genCOpVal_13_eq]
      · rw [hix, hjy, exoticImULDR_genCOpVal_6_eq, exoticImULDR_genCOpVal_15_eq]
      · rw [hix, hjy, exoticImULDR_genCOpVal_7_eq, exoticImULDR_genCOpVal_15_eq]
      · rw [hix, hjy, exoticImULDR_genCOpVal_11_eq, exoticImULDR_genCOpVal_2_eq]
      · rw [hix, hjy, exoticImULDR_genCOpVal_11_eq, exoticImULDR_genCOpVal_3_eq]
      · rw [hix, hjy, exoticImULDR_genCOpVal_13_eq, exoticImULDR_genCOpVal_4_eq]
      · rw [hix, hjy, exoticImULDR_genCOpVal_13_eq, exoticImULDR_genCOpVal_5_eq]
      · rw [hix, hjy, exoticImULDR_genCOpVal_15_eq, exoticImULDR_genCOpVal_6_eq]
      · rw [hix, hjy, exoticImULDR_genCOpVal_15_eq, exoticImULDR_genCOpVal_7_eq]
    rw [hw, mul_comm, sub_self]

theorem exoticImULDR_not_mem_RSH_of_ge16 {x : I32} (h : 16 ≤ x.val) :
    x ∉ ({2, 3, 4, 5, 6, 7, 11, 13, 15} : Finset I32) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h

theorem exoticImULDR_oo_H_H (k : Fin 3) (a : Fin 3) :
    (exoticImULDR * genH k - genH k * exoticImULDR) * (UJ * (genH a).transpose * UJ)
      - (UJ * (genH a).transpose * UJ) * (exoticImULDR * genH k - genH k * exoticImULDR) = 0 := by
  apply oo_disjoint _ _ _ {2, 3, 4, 5, 6, 7, 11, 13, 15}
  · intro i j hij
    have hsupp := exoticImULDR_CH_supp k i j hij
    rcases hsupp with ⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
  · intro x y hxy
    have hsupp := UJ_genH_transpose_UJ_supp a x y hxy
    exact ⟨exoticImULDR_not_mem_RSH_of_ge16 hsupp.1, exoticImULDR_not_mem_RSH_of_ge16 hsupp.2.2.1⟩

theorem exoticImULDR_oo_H_M (k : Fin 3) (a : Fin 8) :
    (exoticImULDR * genH k - genH k * exoticImULDR) * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ) * (exoticImULDR * genH k - genH k * exoticImULDR) = 0 :=
  double_comm_of_comm exoticImULDR (genH k) _ (exoticImULDR_comm_MOp a) (comm_genH_MOp k a)

theorem exoticImULDR_oo_H (k : Fin 3) (g2 : Fin 12) :
    (exoticImULDR * genH k - genH k * exoticImULDR) * smGenOp g2
      - smGenOp g2 * (exoticImULDR * genH k - genH k * exoticImULDR) = 0 := by
  fin_cases g2
  · exact exoticImULDR_oo_H_C k
  · show (exoticImULDR * genH k - genH k * exoticImULDR) * (UJ * (genH 0).transpose * UJ)
        - (UJ * (genH 0).transpose * UJ) * (exoticImULDR * genH k - genH k * exoticImULDR) = 0
    exact exoticImULDR_oo_H_H k 0
  · show (exoticImULDR * genH k - genH k * exoticImULDR) * (UJ * (genH 1).transpose * UJ)
        - (UJ * (genH 1).transpose * UJ) * (exoticImULDR * genH k - genH k * exoticImULDR) = 0
    exact exoticImULDR_oo_H_H k 1
  · show (exoticImULDR * genH k - genH k * exoticImULDR) * (UJ * (genH 2).transpose * UJ)
        - (UJ * (genH 2).transpose * UJ) * (exoticImULDR * genH k - genH k * exoticImULDR) = 0
    exact exoticImULDR_oo_H_H k 2
  · show (exoticImULDR * genH k - genH k * exoticImULDR) * (UJ * (genM 0).transpose * UJ)
        - (UJ * (genM 0).transpose * UJ) * (exoticImULDR * genH k - genH k * exoticImULDR) = 0
    exact exoticImULDR_oo_H_M k 0
  · show (exoticImULDR * genH k - genH k * exoticImULDR) * (UJ * (genM 1).transpose * UJ)
        - (UJ * (genM 1).transpose * UJ) * (exoticImULDR * genH k - genH k * exoticImULDR) = 0
    exact exoticImULDR_oo_H_M k 1
  · show (exoticImULDR * genH k - genH k * exoticImULDR) * (UJ * (genM 2).transpose * UJ)
        - (UJ * (genM 2).transpose * UJ) * (exoticImULDR * genH k - genH k * exoticImULDR) = 0
    exact exoticImULDR_oo_H_M k 2
  · show (exoticImULDR * genH k - genH k * exoticImULDR) * (UJ * (genM 3).transpose * UJ)
        - (UJ * (genM 3).transpose * UJ) * (exoticImULDR * genH k - genH k * exoticImULDR) = 0
    exact exoticImULDR_oo_H_M k 3
  · show (exoticImULDR * genH k - genH k * exoticImULDR) * (UJ * (genM 4).transpose * UJ)
        - (UJ * (genM 4).transpose * UJ) * (exoticImULDR * genH k - genH k * exoticImULDR) = 0
    exact exoticImULDR_oo_H_M k 4
  · show (exoticImULDR * genH k - genH k * exoticImULDR) * (UJ * (genM 5).transpose * UJ)
        - (UJ * (genM 5).transpose * UJ) * (exoticImULDR * genH k - genH k * exoticImULDR) = 0
    exact exoticImULDR_oo_H_M k 5
  · show (exoticImULDR * genH k - genH k * exoticImULDR) * (UJ * (genM 6).transpose * UJ)
        - (UJ * (genM 6).transpose * UJ) * (exoticImULDR * genH k - genH k * exoticImULDR) = 0
    exact exoticImULDR_oo_H_M k 6
  · show (exoticImULDR * genH k - genH k * exoticImULDR) * (UJ * (genM 7).transpose * UJ)
        - (UJ * (genM 7).transpose * UJ) * (exoticImULDR * genH k - genH k * exoticImULDR) = 0
    exact exoticImULDR_oo_H_M k 7

theorem exoticImULDR_orderOne : OrderOneHolds exoticImULDR := by
  intro g1 g2
  fin_cases g1
  · show (exoticImULDR * genC - genC * exoticImULDR) * smGenOp g2
        - smGenOp g2 * (exoticImULDR * genC - genC * exoticImULDR) = 0
    exact exoticImULDR_oo_C g2
  · show (exoticImULDR * genH 0 - genH 0 * exoticImULDR) * smGenOp g2
        - smGenOp g2 * (exoticImULDR * genH 0 - genH 0 * exoticImULDR) = 0
    exact exoticImULDR_oo_H 0 g2
  · show (exoticImULDR * genH 1 - genH 1 * exoticImULDR) * smGenOp g2
        - smGenOp g2 * (exoticImULDR * genH 1 - genH 1 * exoticImULDR) = 0
    exact exoticImULDR_oo_H 1 g2
  · show (exoticImULDR * genH 2 - genH 2 * exoticImULDR) * smGenOp g2
        - smGenOp g2 * (exoticImULDR * genH 2 - genH 2 * exoticImULDR) = 0
    exact exoticImULDR_oo_H 2 g2
  · show (exoticImULDR * genM 0 - genM 0 * exoticImULDR) * smGenOp g2
        - smGenOp g2 * (exoticImULDR * genM 0 - genM 0 * exoticImULDR) = 0
    exact exoticImULDR_oo_M 0 g2
  · show (exoticImULDR * genM 1 - genM 1 * exoticImULDR) * smGenOp g2
        - smGenOp g2 * (exoticImULDR * genM 1 - genM 1 * exoticImULDR) = 0
    exact exoticImULDR_oo_M 1 g2
  · show (exoticImULDR * genM 2 - genM 2 * exoticImULDR) * smGenOp g2
        - smGenOp g2 * (exoticImULDR * genM 2 - genM 2 * exoticImULDR) = 0
    exact exoticImULDR_oo_M 2 g2
  · show (exoticImULDR * genM 3 - genM 3 * exoticImULDR) * smGenOp g2
        - smGenOp g2 * (exoticImULDR * genM 3 - genM 3 * exoticImULDR) = 0
    exact exoticImULDR_oo_M 3 g2
  · show (exoticImULDR * genM 4 - genM 4 * exoticImULDR) * smGenOp g2
        - smGenOp g2 * (exoticImULDR * genM 4 - genM 4 * exoticImULDR) = 0
    exact exoticImULDR_oo_M 4 g2
  · show (exoticImULDR * genM 5 - genM 5 * exoticImULDR) * smGenOp g2
        - smGenOp g2 * (exoticImULDR * genM 5 - genM 5 * exoticImULDR) = 0
    exact exoticImULDR_oo_M 5 g2
  · show (exoticImULDR * genM 6 - genM 6 * exoticImULDR) * smGenOp g2
        - smGenOp g2 * (exoticImULDR * genM 6 - genM 6 * exoticImULDR) = 0
    exact exoticImULDR_oo_M 6 g2
  · show (exoticImULDR * genM 7 - genM 7 * exoticImULDR) * smGenOp g2
        - smGenOp g2 * (exoticImULDR * genM 7 - genM 7 * exoticImULDR) = 0
    exact exoticImULDR_oo_M 7 g2

-- ============================================================================
-- exoticReDLUR : order-one
-- ============================================================================

theorem exoticReDLUR_supp (i j : I32) (h : exoticReDLUR i j ≠ 0) :
    (i = 3 ∧ j = 10) ∨ (i = 10 ∧ j = 3) ∨ (i = 5 ∧ j = 12) ∨ (i = 12 ∧ j = 5) ∨ (i = 7 ∧ j = 14) ∨ (i = 14 ∧ j = 7) ∨ (i = 19 ∧ j = 26) ∨ (i = 26 ∧ j = 19) ∨ (i = 21 ∧ j = 28) ∨ (i = 28 ∧ j = 21) ∨ (i = 23 ∧ j = 30) ∨ (i = 30 ∧ j = 23) := by
  unfold exoticReDLUR at h
  by_cases hs : (i = 3 ∧ j = 10) ∨ (i = 10 ∧ j = 3) ∨ (i = 5 ∧ j = 12) ∨ (i = 12 ∧ j = 5) ∨ (i = 7 ∧ j = 14) ∨ (i = 14 ∧ j = 7) ∨ (i = 19 ∧ j = 26) ∨ (i = 26 ∧ j = 19) ∨ (i = 21 ∧ j = 28) ∨ (i = 28 ∧ j = 21) ∨ (i = 23 ∧ j = 30) ∨ (i = 30 ∧ j = 23)
  · exact hs
  · rw [if_neg hs] at h
    exact absurd rfl h

theorem exoticReDLUR_factor_CC (i j : I32) (h : exoticReDLUR i j ≠ 0) :
    (genCVal j - genCVal i) * (genCOpVal j - genCOpVal i) = 0 := by
  rcases exoticReDLUR_supp i j h with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]

theorem exoticReDLUR_oo_C_C :
    (exoticReDLUR * genC - genC * exoticReDLUR) * smGenOp 0
      - smGenOp 0 * (exoticReDLUR * genC - genC * exoticReDLUR) = 0 :=
  oo_C_C_of_factor exoticReDLUR exoticReDLUR_factor_CC

theorem exoticReDLUR_comm_genC_mem (i j : I32)
    (h : (exoticReDLUR * genC - genC * exoticReDLUR) i j ≠ 0) :
    (i = 3 ∨ i = 5 ∨ i = 7 ∨ i = 10 ∨ i = 12 ∨ i = 14) ∧ (j = 3 ∨ j = 5 ∨ j = 7 ∨ j = 10 ∨ j = 12 ∨ j = 14) := by
  rw [comm_diag_entry _ _ _ (fun x y => genC_eq_diag x y) i j] at h
  have hE : exoticReDLUR i j ≠ 0 := by
    intro h0; apply h; rw [h0, zero_mul]
  have hc : genCVal j - genCVal i ≠ 0 := by
    intro h0; apply h; rw [h0, mul_zero]
  rcases exoticReDLUR_supp i j hE with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy] at hc; simp [genCVal] at hc

theorem exoticReDLUR_not_mem_RC_of_ge16 {x : I32} (h : 16 ≤ x.val) :
    x ∉ ({3, 5, 7, 10, 12, 14} : Finset I32) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h

theorem exoticReDLUR_oo_C_H (k : Fin 3) :
    (exoticReDLUR * genC - genC * exoticReDLUR) * (UJ * (genH k).transpose * UJ)
      - (UJ * (genH k).transpose * UJ) * (exoticReDLUR * genC - genC * exoticReDLUR) = 0 := by
  apply oo_disjoint _ _ _ {3, 5, 7, 10, 12, 14}
  · intro i j hij
    obtain ⟨hi, hj⟩ := exoticReDLUR_comm_genC_mem i j hij
    constructor
    · simp only [Finset.mem_insert, Finset.mem_singleton]; exact hi
    · simp only [Finset.mem_insert, Finset.mem_singleton]; exact hj
  · intro x y hxy
    have hsupp := UJ_genH_transpose_UJ_supp k x y hxy
    exact ⟨exoticReDLUR_not_mem_RC_of_ge16 hsupp.1, exoticReDLUR_not_mem_RC_of_ge16 hsupp.2.2.1⟩

theorem exoticReDLUR_oo_C_M (a : Fin 8) :
    (exoticReDLUR * genC - genC * exoticReDLUR) * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ) * (exoticReDLUR * genC - genC * exoticReDLUR) = 0 :=
  double_comm_of_comm exoticReDLUR genC _ (exoticReDLUR_comm_MOp a) (comm_genC_MOp a)

theorem exoticReDLUR_oo_C (g2 : Fin 12) :
    (exoticReDLUR * genC - genC * exoticReDLUR) * smGenOp g2
      - smGenOp g2 * (exoticReDLUR * genC - genC * exoticReDLUR) = 0 := by
  fin_cases g2
  · exact exoticReDLUR_oo_C_C
  · show (exoticReDLUR * genC - genC * exoticReDLUR) * (UJ * (genH 0).transpose * UJ)
        - (UJ * (genH 0).transpose * UJ) * (exoticReDLUR * genC - genC * exoticReDLUR) = 0
    exact exoticReDLUR_oo_C_H 0
  · show (exoticReDLUR * genC - genC * exoticReDLUR) * (UJ * (genH 1).transpose * UJ)
        - (UJ * (genH 1).transpose * UJ) * (exoticReDLUR * genC - genC * exoticReDLUR) = 0
    exact exoticReDLUR_oo_C_H 1
  · show (exoticReDLUR * genC - genC * exoticReDLUR) * (UJ * (genH 2).transpose * UJ)
        - (UJ * (genH 2).transpose * UJ) * (exoticReDLUR * genC - genC * exoticReDLUR) = 0
    exact exoticReDLUR_oo_C_H 2
  · show (exoticReDLUR * genC - genC * exoticReDLUR) * (UJ * (genM 0).transpose * UJ)
        - (UJ * (genM 0).transpose * UJ) * (exoticReDLUR * genC - genC * exoticReDLUR) = 0
    exact exoticReDLUR_oo_C_M 0
  · show (exoticReDLUR * genC - genC * exoticReDLUR) * (UJ * (genM 1).transpose * UJ)
        - (UJ * (genM 1).transpose * UJ) * (exoticReDLUR * genC - genC * exoticReDLUR) = 0
    exact exoticReDLUR_oo_C_M 1
  · show (exoticReDLUR * genC - genC * exoticReDLUR) * (UJ * (genM 2).transpose * UJ)
        - (UJ * (genM 2).transpose * UJ) * (exoticReDLUR * genC - genC * exoticReDLUR) = 0
    exact exoticReDLUR_oo_C_M 2
  · show (exoticReDLUR * genC - genC * exoticReDLUR) * (UJ * (genM 3).transpose * UJ)
        - (UJ * (genM 3).transpose * UJ) * (exoticReDLUR * genC - genC * exoticReDLUR) = 0
    exact exoticReDLUR_oo_C_M 3
  · show (exoticReDLUR * genC - genC * exoticReDLUR) * (UJ * (genM 4).transpose * UJ)
        - (UJ * (genM 4).transpose * UJ) * (exoticReDLUR * genC - genC * exoticReDLUR) = 0
    exact exoticReDLUR_oo_C_M 4
  · show (exoticReDLUR * genC - genC * exoticReDLUR) * (UJ * (genM 5).transpose * UJ)
        - (UJ * (genM 5).transpose * UJ) * (exoticReDLUR * genC - genC * exoticReDLUR) = 0
    exact exoticReDLUR_oo_C_M 5
  · show (exoticReDLUR * genC - genC * exoticReDLUR) * (UJ * (genM 6).transpose * UJ)
        - (UJ * (genM 6).transpose * UJ) * (exoticReDLUR * genC - genC * exoticReDLUR) = 0
    exact exoticReDLUR_oo_C_M 6
  · show (exoticReDLUR * genC - genC * exoticReDLUR) * (UJ * (genM 7).transpose * UJ)
        - (UJ * (genM 7).transpose * UJ) * (exoticReDLUR * genC - genC * exoticReDLUR) = 0
    exact exoticReDLUR_oo_C_M 7

theorem exoticReDLUR_oo_M (a : Fin 8) (g2 : Fin 12) :
    (exoticReDLUR * genM a - genM a * exoticReDLUR) * smGenOp g2
      - smGenOp g2 * (exoticReDLUR * genM a - genM a * exoticReDLUR) = 0 := by
  have hcomm : exoticReDLUR * genM a - genM a * exoticReDLUR = 0 :=
    sub_eq_zero.mpr (exoticReDLUR_comm_genM a)
  rw [hcomm, zero_mul, mul_zero, sub_zero]

theorem exoticReDLUR_genCOpVal_2_eq : genCOpVal (2 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticReDLUR_genCOpVal_3_eq : genCOpVal (3 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticReDLUR_genCOpVal_4_eq : genCOpVal (4 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticReDLUR_genCOpVal_5_eq : genCOpVal (5 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticReDLUR_genCOpVal_6_eq : genCOpVal (6 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticReDLUR_genCOpVal_7_eq : genCOpVal (7 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticReDLUR_genCOpVal_10_eq : genCOpVal (10 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticReDLUR_genCOpVal_12_eq : genCOpVal (12 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticReDLUR_genCOpVal_14_eq : genCOpVal (14 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]

theorem exoticReDLUR_CH_supp (k : Fin 3) (i j : I32)
    (h : (exoticReDLUR * genH k - genH k * exoticReDLUR) i j ≠ 0) :
    (i = 10 ∧ j = 2) ∨ (i = 10 ∧ j = 3) ∨ (i = 12 ∧ j = 4) ∨ (i = 12 ∧ j = 5) ∨ (i = 14 ∧ j = 6) ∨ (i = 14 ∧ j = 7) ∨ (i = 2 ∧ j = 10) ∨ (i = 3 ∧ j = 10) ∨ (i = 4 ∧ j = 12) ∨ (i = 5 ∧ j = 12) ∨ (i = 6 ∧ j = 14) ∨ (i = 7 ∧ j = 14) := by
  simp only [Matrix.sub_apply] at h
  by_cases h1 : (exoticReDLUR * genH k) i j = 0
  · have h2 : (genH k * exoticReDLUR) i j ≠ 0 := by
      intro hc
      apply h
      rw [h1, hc, sub_zero]
    simp only [Matrix.mul_apply] at h2
    have hex : ∃ l, genH k i l * exoticReDLUR l j ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply h2
      exact Finset.sum_eq_zero (fun l _ => hc l)
    obtain ⟨l, hl⟩ := hex
    have hGl : genH k i l ≠ 0 := fun h0 => hl (by rw [h0, zero_mul])
    have hEl : exoticReDLUR l j ≠ 0 := fun h0 => hl (by rw [h0, mul_zero])
    have hblock := genH_supp_block k i l hGl
    have hsupp := exoticReDLUR_supp l j hEl
    rcases hsupp with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
    · rw [hx] at hblock
      have hi : i.val = 2 ∨ i.val = 3 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hi with hv | hv
      · have hatom : i = 2 ∧ j = 10 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 2 ∧ j = 10) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 3 ∧ j = 10 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 3 ∧ j = 10) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hx] at hblock; omega
    · rw [hx] at hblock
      have hi : i.val = 4 ∨ i.val = 5 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hi with hv | hv
      · have hatom : i = 4 ∧ j = 12 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 4 ∧ j = 12) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 5 ∧ j = 12 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 5 ∧ j = 12) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hx] at hblock; omega
    · rw [hx] at hblock
      have hi : i.val = 6 ∨ i.val = 7 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hi with hv | hv
      · have hatom : i = 6 ∧ j = 14 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 6 ∧ j = 14) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 7 ∧ j = 14 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 7 ∧ j = 14) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
  · have h1ne : (exoticReDLUR * genH k) i j ≠ 0 := h1
    simp only [Matrix.mul_apply] at h1ne
    have hex : ∃ l, exoticReDLUR i l * genH k l j ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply h1ne
      exact Finset.sum_eq_zero (fun l _ => hc l)
    obtain ⟨l, hl⟩ := hex
    have hEl : exoticReDLUR i l ≠ 0 := fun h0 => hl (by rw [h0, zero_mul])
    have hG : genH k l j ≠ 0 := fun h0 => hl (by rw [h0, mul_zero])
    have hblock := genH_supp_block k l j hG
    have hsupp := exoticReDLUR_supp i l hEl
    rcases hsupp with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
    · rw [hy] at hblock; omega
    · rw [hy] at hblock
      have hj : j.val = 2 ∨ j.val = 3 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hj with hv | hv
      · have hatom : i = 10 ∧ j = 2 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 10 ∧ j = 2) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 10 ∧ j = 3 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 10 ∧ j = 3) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hy] at hblock; omega
    · rw [hy] at hblock
      have hj : j.val = 4 ∨ j.val = 5 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hj with hv | hv
      · have hatom : i = 12 ∧ j = 4 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 12 ∧ j = 4) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 12 ∧ j = 5 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 12 ∧ j = 5) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hy] at hblock; omega
    · rw [hy] at hblock
      have hj : j.val = 6 ∨ j.val = 7 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hj with hv | hv
      · have hatom : i = 14 ∧ j = 6 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 14 ∧ j = 6) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 14 ∧ j = 7 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 14 ∧ j = 7) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega

theorem exoticReDLUR_oo_H_C (k : Fin 3) :
    (exoticReDLUR * genH k - genH k * exoticReDLUR) * smGenOp 0
      - smGenOp 0 * (exoticReDLUR * genH k - genH k * exoticReDLUR) = 0 := by
  have hD : ∀ x y : I32, smGenOp 0 x y = if x = y then genCOpVal x else 0 :=
    fun x y => smGenOp_zero_eq x y
  ext i j
  simp only [Matrix.zero_apply, Matrix.sub_apply]
  have hCD : ((exoticReDLUR * genH k - genH k * exoticReDLUR) * smGenOp 0) i j
           = (exoticReDLUR * genH k - genH k * exoticReDLUR) i j * genCOpVal j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hD j j, if_pos rfl]
    · intro l _ hlj
      rw [hD l j, if_neg hlj, mul_zero]
    · intro hcon; exact absurd (Finset.mem_univ j) hcon
  have hDC : (smGenOp 0 * (exoticReDLUR * genH k - genH k * exoticReDLUR)) i j
           = genCOpVal i * (exoticReDLUR * genH k - genH k * exoticReDLUR) i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hD i i, if_pos rfl]
    · intro l _ hli
      rw [hD i l, if_neg (Ne.symm hli), zero_mul]
    · intro hcon; exact absurd (Finset.mem_univ i) hcon
  rw [hCD, hDC]
  by_cases hC : (exoticReDLUR * genH k - genH k * exoticReDLUR) i j = 0
  · rw [hC, zero_mul, mul_zero, sub_zero]
  · have hsupp := exoticReDLUR_CH_supp k i j hC
    have hw : genCOpVal j = genCOpVal i := by
      rcases hsupp with ⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩
      · rw [hix, hjy, exoticReDLUR_genCOpVal_2_eq, exoticReDLUR_genCOpVal_10_eq]
      · rw [hix, hjy, exoticReDLUR_genCOpVal_3_eq, exoticReDLUR_genCOpVal_10_eq]
      · rw [hix, hjy, exoticReDLUR_genCOpVal_4_eq, exoticReDLUR_genCOpVal_12_eq]
      · rw [hix, hjy, exoticReDLUR_genCOpVal_5_eq, exoticReDLUR_genCOpVal_12_eq]
      · rw [hix, hjy, exoticReDLUR_genCOpVal_6_eq, exoticReDLUR_genCOpVal_14_eq]
      · rw [hix, hjy, exoticReDLUR_genCOpVal_7_eq, exoticReDLUR_genCOpVal_14_eq]
      · rw [hix, hjy, exoticReDLUR_genCOpVal_10_eq, exoticReDLUR_genCOpVal_2_eq]
      · rw [hix, hjy, exoticReDLUR_genCOpVal_10_eq, exoticReDLUR_genCOpVal_3_eq]
      · rw [hix, hjy, exoticReDLUR_genCOpVal_12_eq, exoticReDLUR_genCOpVal_4_eq]
      · rw [hix, hjy, exoticReDLUR_genCOpVal_12_eq, exoticReDLUR_genCOpVal_5_eq]
      · rw [hix, hjy, exoticReDLUR_genCOpVal_14_eq, exoticReDLUR_genCOpVal_6_eq]
      · rw [hix, hjy, exoticReDLUR_genCOpVal_14_eq, exoticReDLUR_genCOpVal_7_eq]
    rw [hw, mul_comm, sub_self]

theorem exoticReDLUR_not_mem_RSH_of_ge16 {x : I32} (h : 16 ≤ x.val) :
    x ∉ ({2, 3, 4, 5, 6, 7, 10, 12, 14} : Finset I32) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h

theorem exoticReDLUR_oo_H_H (k : Fin 3) (a : Fin 3) :
    (exoticReDLUR * genH k - genH k * exoticReDLUR) * (UJ * (genH a).transpose * UJ)
      - (UJ * (genH a).transpose * UJ) * (exoticReDLUR * genH k - genH k * exoticReDLUR) = 0 := by
  apply oo_disjoint _ _ _ {2, 3, 4, 5, 6, 7, 10, 12, 14}
  · intro i j hij
    have hsupp := exoticReDLUR_CH_supp k i j hij
    rcases hsupp with ⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
  · intro x y hxy
    have hsupp := UJ_genH_transpose_UJ_supp a x y hxy
    exact ⟨exoticReDLUR_not_mem_RSH_of_ge16 hsupp.1, exoticReDLUR_not_mem_RSH_of_ge16 hsupp.2.2.1⟩

theorem exoticReDLUR_oo_H_M (k : Fin 3) (a : Fin 8) :
    (exoticReDLUR * genH k - genH k * exoticReDLUR) * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ) * (exoticReDLUR * genH k - genH k * exoticReDLUR) = 0 :=
  double_comm_of_comm exoticReDLUR (genH k) _ (exoticReDLUR_comm_MOp a) (comm_genH_MOp k a)

theorem exoticReDLUR_oo_H (k : Fin 3) (g2 : Fin 12) :
    (exoticReDLUR * genH k - genH k * exoticReDLUR) * smGenOp g2
      - smGenOp g2 * (exoticReDLUR * genH k - genH k * exoticReDLUR) = 0 := by
  fin_cases g2
  · exact exoticReDLUR_oo_H_C k
  · show (exoticReDLUR * genH k - genH k * exoticReDLUR) * (UJ * (genH 0).transpose * UJ)
        - (UJ * (genH 0).transpose * UJ) * (exoticReDLUR * genH k - genH k * exoticReDLUR) = 0
    exact exoticReDLUR_oo_H_H k 0
  · show (exoticReDLUR * genH k - genH k * exoticReDLUR) * (UJ * (genH 1).transpose * UJ)
        - (UJ * (genH 1).transpose * UJ) * (exoticReDLUR * genH k - genH k * exoticReDLUR) = 0
    exact exoticReDLUR_oo_H_H k 1
  · show (exoticReDLUR * genH k - genH k * exoticReDLUR) * (UJ * (genH 2).transpose * UJ)
        - (UJ * (genH 2).transpose * UJ) * (exoticReDLUR * genH k - genH k * exoticReDLUR) = 0
    exact exoticReDLUR_oo_H_H k 2
  · show (exoticReDLUR * genH k - genH k * exoticReDLUR) * (UJ * (genM 0).transpose * UJ)
        - (UJ * (genM 0).transpose * UJ) * (exoticReDLUR * genH k - genH k * exoticReDLUR) = 0
    exact exoticReDLUR_oo_H_M k 0
  · show (exoticReDLUR * genH k - genH k * exoticReDLUR) * (UJ * (genM 1).transpose * UJ)
        - (UJ * (genM 1).transpose * UJ) * (exoticReDLUR * genH k - genH k * exoticReDLUR) = 0
    exact exoticReDLUR_oo_H_M k 1
  · show (exoticReDLUR * genH k - genH k * exoticReDLUR) * (UJ * (genM 2).transpose * UJ)
        - (UJ * (genM 2).transpose * UJ) * (exoticReDLUR * genH k - genH k * exoticReDLUR) = 0
    exact exoticReDLUR_oo_H_M k 2
  · show (exoticReDLUR * genH k - genH k * exoticReDLUR) * (UJ * (genM 3).transpose * UJ)
        - (UJ * (genM 3).transpose * UJ) * (exoticReDLUR * genH k - genH k * exoticReDLUR) = 0
    exact exoticReDLUR_oo_H_M k 3
  · show (exoticReDLUR * genH k - genH k * exoticReDLUR) * (UJ * (genM 4).transpose * UJ)
        - (UJ * (genM 4).transpose * UJ) * (exoticReDLUR * genH k - genH k * exoticReDLUR) = 0
    exact exoticReDLUR_oo_H_M k 4
  · show (exoticReDLUR * genH k - genH k * exoticReDLUR) * (UJ * (genM 5).transpose * UJ)
        - (UJ * (genM 5).transpose * UJ) * (exoticReDLUR * genH k - genH k * exoticReDLUR) = 0
    exact exoticReDLUR_oo_H_M k 5
  · show (exoticReDLUR * genH k - genH k * exoticReDLUR) * (UJ * (genM 6).transpose * UJ)
        - (UJ * (genM 6).transpose * UJ) * (exoticReDLUR * genH k - genH k * exoticReDLUR) = 0
    exact exoticReDLUR_oo_H_M k 6
  · show (exoticReDLUR * genH k - genH k * exoticReDLUR) * (UJ * (genM 7).transpose * UJ)
        - (UJ * (genM 7).transpose * UJ) * (exoticReDLUR * genH k - genH k * exoticReDLUR) = 0
    exact exoticReDLUR_oo_H_M k 7

theorem exoticReDLUR_orderOne : OrderOneHolds exoticReDLUR := by
  intro g1 g2
  fin_cases g1
  · show (exoticReDLUR * genC - genC * exoticReDLUR) * smGenOp g2
        - smGenOp g2 * (exoticReDLUR * genC - genC * exoticReDLUR) = 0
    exact exoticReDLUR_oo_C g2
  · show (exoticReDLUR * genH 0 - genH 0 * exoticReDLUR) * smGenOp g2
        - smGenOp g2 * (exoticReDLUR * genH 0 - genH 0 * exoticReDLUR) = 0
    exact exoticReDLUR_oo_H 0 g2
  · show (exoticReDLUR * genH 1 - genH 1 * exoticReDLUR) * smGenOp g2
        - smGenOp g2 * (exoticReDLUR * genH 1 - genH 1 * exoticReDLUR) = 0
    exact exoticReDLUR_oo_H 1 g2
  · show (exoticReDLUR * genH 2 - genH 2 * exoticReDLUR) * smGenOp g2
        - smGenOp g2 * (exoticReDLUR * genH 2 - genH 2 * exoticReDLUR) = 0
    exact exoticReDLUR_oo_H 2 g2
  · show (exoticReDLUR * genM 0 - genM 0 * exoticReDLUR) * smGenOp g2
        - smGenOp g2 * (exoticReDLUR * genM 0 - genM 0 * exoticReDLUR) = 0
    exact exoticReDLUR_oo_M 0 g2
  · show (exoticReDLUR * genM 1 - genM 1 * exoticReDLUR) * smGenOp g2
        - smGenOp g2 * (exoticReDLUR * genM 1 - genM 1 * exoticReDLUR) = 0
    exact exoticReDLUR_oo_M 1 g2
  · show (exoticReDLUR * genM 2 - genM 2 * exoticReDLUR) * smGenOp g2
        - smGenOp g2 * (exoticReDLUR * genM 2 - genM 2 * exoticReDLUR) = 0
    exact exoticReDLUR_oo_M 2 g2
  · show (exoticReDLUR * genM 3 - genM 3 * exoticReDLUR) * smGenOp g2
        - smGenOp g2 * (exoticReDLUR * genM 3 - genM 3 * exoticReDLUR) = 0
    exact exoticReDLUR_oo_M 3 g2
  · show (exoticReDLUR * genM 4 - genM 4 * exoticReDLUR) * smGenOp g2
        - smGenOp g2 * (exoticReDLUR * genM 4 - genM 4 * exoticReDLUR) = 0
    exact exoticReDLUR_oo_M 4 g2
  · show (exoticReDLUR * genM 5 - genM 5 * exoticReDLUR) * smGenOp g2
        - smGenOp g2 * (exoticReDLUR * genM 5 - genM 5 * exoticReDLUR) = 0
    exact exoticReDLUR_oo_M 5 g2
  · show (exoticReDLUR * genM 6 - genM 6 * exoticReDLUR) * smGenOp g2
        - smGenOp g2 * (exoticReDLUR * genM 6 - genM 6 * exoticReDLUR) = 0
    exact exoticReDLUR_oo_M 6 g2
  · show (exoticReDLUR * genM 7 - genM 7 * exoticReDLUR) * smGenOp g2
        - smGenOp g2 * (exoticReDLUR * genM 7 - genM 7 * exoticReDLUR) = 0
    exact exoticReDLUR_oo_M 7 g2

-- ============================================================================
-- exoticImDLUR : order-one
-- ============================================================================

theorem exoticImDLUR_supp (i j : I32) (h : exoticImDLUR i j ≠ 0) :
    (i = 3 ∧ j = 10) ∨ (i = 5 ∧ j = 12) ∨ (i = 7 ∧ j = 14) ∨ (i = 26 ∧ j = 19) ∨ (i = 28 ∧ j = 21) ∨ (i = 30 ∧ j = 23) ∨ (i = 10 ∧ j = 3) ∨ (i = 12 ∧ j = 5) ∨ (i = 14 ∧ j = 7) ∨ (i = 19 ∧ j = 26) ∨ (i = 21 ∧ j = 28) ∨ (i = 23 ∧ j = 30) := by
  unfold exoticImDLUR at h
  by_cases h1 : (i = 3 ∧ j = 10) ∨ (i = 5 ∧ j = 12) ∨ (i = 7 ∧ j = 14) ∨ (i = 26 ∧ j = 19) ∨ (i = 28 ∧ j = 21) ∨ (i = 30 ∧ j = 23)
  · rcases h1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
  · by_cases h2 : (i = 10 ∧ j = 3) ∨ (i = 12 ∧ j = 5) ∨ (i = 14 ∧ j = 7) ∨ (i = 19 ∧ j = 26) ∨ (i = 21 ∧ j = 28) ∨ (i = 23 ∧ j = 30)
    · rcases h2 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp
    · simp [h1, h2] at h

theorem exoticImDLUR_factor_CC (i j : I32) (h : exoticImDLUR i j ≠ 0) :
    (genCVal j - genCVal i) * (genCOpVal j - genCOpVal i) = 0 := by
  rcases exoticImDLUR_supp i j h with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]
  · rw [hx, hy]; simp [genCVal, genCOpVal, partner]

theorem exoticImDLUR_oo_C_C :
    (exoticImDLUR * genC - genC * exoticImDLUR) * smGenOp 0
      - smGenOp 0 * (exoticImDLUR * genC - genC * exoticImDLUR) = 0 :=
  oo_C_C_of_factor exoticImDLUR exoticImDLUR_factor_CC

theorem exoticImDLUR_comm_genC_mem (i j : I32)
    (h : (exoticImDLUR * genC - genC * exoticImDLUR) i j ≠ 0) :
    (i = 3 ∨ i = 5 ∨ i = 7 ∨ i = 10 ∨ i = 12 ∨ i = 14) ∧ (j = 3 ∨ j = 5 ∨ j = 7 ∨ j = 10 ∨ j = 12 ∨ j = 14) := by
  rw [comm_diag_entry _ _ _ (fun x y => genC_eq_diag x y) i j] at h
  have hE : exoticImDLUR i j ≠ 0 := by
    intro h0; apply h; rw [h0, zero_mul]
  have hc : genCVal j - genCVal i ≠ 0 := by
    intro h0; apply h; rw [h0, mul_zero]
  rcases exoticImDLUR_supp i j hE with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy]; exact ⟨by decide, by decide⟩
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy] at hc; simp [genCVal] at hc
  · rw [hx, hy] at hc; simp [genCVal] at hc

theorem exoticImDLUR_not_mem_RC_of_ge16 {x : I32} (h : 16 ≤ x.val) :
    x ∉ ({3, 5, 7, 10, 12, 14} : Finset I32) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h

theorem exoticImDLUR_oo_C_H (k : Fin 3) :
    (exoticImDLUR * genC - genC * exoticImDLUR) * (UJ * (genH k).transpose * UJ)
      - (UJ * (genH k).transpose * UJ) * (exoticImDLUR * genC - genC * exoticImDLUR) = 0 := by
  apply oo_disjoint _ _ _ {3, 5, 7, 10, 12, 14}
  · intro i j hij
    obtain ⟨hi, hj⟩ := exoticImDLUR_comm_genC_mem i j hij
    constructor
    · simp only [Finset.mem_insert, Finset.mem_singleton]; exact hi
    · simp only [Finset.mem_insert, Finset.mem_singleton]; exact hj
  · intro x y hxy
    have hsupp := UJ_genH_transpose_UJ_supp k x y hxy
    exact ⟨exoticImDLUR_not_mem_RC_of_ge16 hsupp.1, exoticImDLUR_not_mem_RC_of_ge16 hsupp.2.2.1⟩

theorem exoticImDLUR_oo_C_M (a : Fin 8) :
    (exoticImDLUR * genC - genC * exoticImDLUR) * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ) * (exoticImDLUR * genC - genC * exoticImDLUR) = 0 :=
  double_comm_of_comm exoticImDLUR genC _ (exoticImDLUR_comm_MOp a) (comm_genC_MOp a)

theorem exoticImDLUR_oo_C (g2 : Fin 12) :
    (exoticImDLUR * genC - genC * exoticImDLUR) * smGenOp g2
      - smGenOp g2 * (exoticImDLUR * genC - genC * exoticImDLUR) = 0 := by
  fin_cases g2
  · exact exoticImDLUR_oo_C_C
  · show (exoticImDLUR * genC - genC * exoticImDLUR) * (UJ * (genH 0).transpose * UJ)
        - (UJ * (genH 0).transpose * UJ) * (exoticImDLUR * genC - genC * exoticImDLUR) = 0
    exact exoticImDLUR_oo_C_H 0
  · show (exoticImDLUR * genC - genC * exoticImDLUR) * (UJ * (genH 1).transpose * UJ)
        - (UJ * (genH 1).transpose * UJ) * (exoticImDLUR * genC - genC * exoticImDLUR) = 0
    exact exoticImDLUR_oo_C_H 1
  · show (exoticImDLUR * genC - genC * exoticImDLUR) * (UJ * (genH 2).transpose * UJ)
        - (UJ * (genH 2).transpose * UJ) * (exoticImDLUR * genC - genC * exoticImDLUR) = 0
    exact exoticImDLUR_oo_C_H 2
  · show (exoticImDLUR * genC - genC * exoticImDLUR) * (UJ * (genM 0).transpose * UJ)
        - (UJ * (genM 0).transpose * UJ) * (exoticImDLUR * genC - genC * exoticImDLUR) = 0
    exact exoticImDLUR_oo_C_M 0
  · show (exoticImDLUR * genC - genC * exoticImDLUR) * (UJ * (genM 1).transpose * UJ)
        - (UJ * (genM 1).transpose * UJ) * (exoticImDLUR * genC - genC * exoticImDLUR) = 0
    exact exoticImDLUR_oo_C_M 1
  · show (exoticImDLUR * genC - genC * exoticImDLUR) * (UJ * (genM 2).transpose * UJ)
        - (UJ * (genM 2).transpose * UJ) * (exoticImDLUR * genC - genC * exoticImDLUR) = 0
    exact exoticImDLUR_oo_C_M 2
  · show (exoticImDLUR * genC - genC * exoticImDLUR) * (UJ * (genM 3).transpose * UJ)
        - (UJ * (genM 3).transpose * UJ) * (exoticImDLUR * genC - genC * exoticImDLUR) = 0
    exact exoticImDLUR_oo_C_M 3
  · show (exoticImDLUR * genC - genC * exoticImDLUR) * (UJ * (genM 4).transpose * UJ)
        - (UJ * (genM 4).transpose * UJ) * (exoticImDLUR * genC - genC * exoticImDLUR) = 0
    exact exoticImDLUR_oo_C_M 4
  · show (exoticImDLUR * genC - genC * exoticImDLUR) * (UJ * (genM 5).transpose * UJ)
        - (UJ * (genM 5).transpose * UJ) * (exoticImDLUR * genC - genC * exoticImDLUR) = 0
    exact exoticImDLUR_oo_C_M 5
  · show (exoticImDLUR * genC - genC * exoticImDLUR) * (UJ * (genM 6).transpose * UJ)
        - (UJ * (genM 6).transpose * UJ) * (exoticImDLUR * genC - genC * exoticImDLUR) = 0
    exact exoticImDLUR_oo_C_M 6
  · show (exoticImDLUR * genC - genC * exoticImDLUR) * (UJ * (genM 7).transpose * UJ)
        - (UJ * (genM 7).transpose * UJ) * (exoticImDLUR * genC - genC * exoticImDLUR) = 0
    exact exoticImDLUR_oo_C_M 7

theorem exoticImDLUR_oo_M (a : Fin 8) (g2 : Fin 12) :
    (exoticImDLUR * genM a - genM a * exoticImDLUR) * smGenOp g2
      - smGenOp g2 * (exoticImDLUR * genM a - genM a * exoticImDLUR) = 0 := by
  have hcomm : exoticImDLUR * genM a - genM a * exoticImDLUR = 0 :=
    sub_eq_zero.mpr (exoticImDLUR_comm_genM a)
  rw [hcomm, zero_mul, mul_zero, sub_zero]

theorem exoticImDLUR_genCOpVal_2_eq : genCOpVal (2 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticImDLUR_genCOpVal_3_eq : genCOpVal (3 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticImDLUR_genCOpVal_4_eq : genCOpVal (4 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticImDLUR_genCOpVal_5_eq : genCOpVal (5 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticImDLUR_genCOpVal_6_eq : genCOpVal (6 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticImDLUR_genCOpVal_7_eq : genCOpVal (7 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticImDLUR_genCOpVal_10_eq : genCOpVal (10 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticImDLUR_genCOpVal_12_eq : genCOpVal (12 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]
theorem exoticImDLUR_genCOpVal_14_eq : genCOpVal (14 : I32) = (0:ℂ) := by
  simp [genCOpVal, genCVal, partner]

theorem exoticImDLUR_CH_supp (k : Fin 3) (i j : I32)
    (h : (exoticImDLUR * genH k - genH k * exoticImDLUR) i j ≠ 0) :
    (i = 10 ∧ j = 2) ∨ (i = 10 ∧ j = 3) ∨ (i = 12 ∧ j = 4) ∨ (i = 12 ∧ j = 5) ∨ (i = 14 ∧ j = 6) ∨ (i = 14 ∧ j = 7) ∨ (i = 2 ∧ j = 10) ∨ (i = 3 ∧ j = 10) ∨ (i = 4 ∧ j = 12) ∨ (i = 5 ∧ j = 12) ∨ (i = 6 ∧ j = 14) ∨ (i = 7 ∧ j = 14) := by
  simp only [Matrix.sub_apply] at h
  by_cases h1 : (exoticImDLUR * genH k) i j = 0
  · have h2 : (genH k * exoticImDLUR) i j ≠ 0 := by
      intro hc
      apply h
      rw [h1, hc, sub_zero]
    simp only [Matrix.mul_apply] at h2
    have hex : ∃ l, genH k i l * exoticImDLUR l j ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply h2
      exact Finset.sum_eq_zero (fun l _ => hc l)
    obtain ⟨l, hl⟩ := hex
    have hGl : genH k i l ≠ 0 := fun h0 => hl (by rw [h0, zero_mul])
    have hEl : exoticImDLUR l j ≠ 0 := fun h0 => hl (by rw [h0, mul_zero])
    have hblock := genH_supp_block k i l hGl
    have hsupp := exoticImDLUR_supp l j hEl
    rcases hsupp with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
    · rw [hx] at hblock
      have hi : i.val = 2 ∨ i.val = 3 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hi with hv | hv
      · have hatom : i = 2 ∧ j = 10 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 2 ∧ j = 10) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 3 ∧ j = 10 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 3 ∧ j = 10) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hx] at hblock
      have hi : i.val = 4 ∨ i.val = 5 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hi with hv | hv
      · have hatom : i = 4 ∧ j = 12 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 4 ∧ j = 12) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 5 ∧ j = 12 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 5 ∧ j = 12) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hx] at hblock
      have hi : i.val = 6 ∨ i.val = 7 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hi with hv | hv
      · have hatom : i = 6 ∧ j = 14 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 6 ∧ j = 14) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 7 ∧ j = 14 := ⟨Fin.ext (by simpa using hv), hy⟩
        have htrue : (i = 7 ∧ j = 14) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
    · rw [hx] at hblock; omega
  · have h1ne : (exoticImDLUR * genH k) i j ≠ 0 := h1
    simp only [Matrix.mul_apply] at h1ne
    have hex : ∃ l, exoticImDLUR i l * genH k l j ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply h1ne
      exact Finset.sum_eq_zero (fun l _ => hc l)
    obtain ⟨l, hl⟩ := hex
    have hEl : exoticImDLUR i l ≠ 0 := fun h0 => hl (by rw [h0, zero_mul])
    have hG : genH k l j ≠ 0 := fun h0 => hl (by rw [h0, mul_zero])
    have hblock := genH_supp_block k l j hG
    have hsupp := exoticImDLUR_supp i l hEl
    rcases hsupp with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega
    · rw [hy] at hblock
      have hj : j.val = 2 ∨ j.val = 3 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hj with hv | hv
      · have hatom : i = 10 ∧ j = 2 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 10 ∧ j = 2) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 10 ∧ j = 3 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 10 ∧ j = 3) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hy] at hblock
      have hj : j.val = 4 ∨ j.val = 5 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hj with hv | hv
      · have hatom : i = 12 ∧ j = 4 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 12 ∧ j = 4) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 12 ∧ j = 5 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 12 ∧ j = 5) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hy] at hblock
      have hj : j.val = 6 ∨ j.val = 7 := by
        obtain ⟨_, _, hdiv⟩ := hblock
        omega
      rcases hj with hv | hv
      · have hatom : i = 14 ∧ j = 6 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 14 ∧ j = 6) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
      · have hatom : i = 14 ∧ j = 7 := ⟨hx, Fin.ext (by simpa using hv)⟩
        have htrue : (i = 14 ∧ j = 7) = True :=
          propext ⟨fun _ => trivial, fun _ => hatom⟩
        simp only [htrue, or_true, true_or]
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega
    · rw [hy] at hblock; omega

theorem exoticImDLUR_oo_H_C (k : Fin 3) :
    (exoticImDLUR * genH k - genH k * exoticImDLUR) * smGenOp 0
      - smGenOp 0 * (exoticImDLUR * genH k - genH k * exoticImDLUR) = 0 := by
  have hD : ∀ x y : I32, smGenOp 0 x y = if x = y then genCOpVal x else 0 :=
    fun x y => smGenOp_zero_eq x y
  ext i j
  simp only [Matrix.zero_apply, Matrix.sub_apply]
  have hCD : ((exoticImDLUR * genH k - genH k * exoticImDLUR) * smGenOp 0) i j
           = (exoticImDLUR * genH k - genH k * exoticImDLUR) i j * genCOpVal j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hD j j, if_pos rfl]
    · intro l _ hlj
      rw [hD l j, if_neg hlj, mul_zero]
    · intro hcon; exact absurd (Finset.mem_univ j) hcon
  have hDC : (smGenOp 0 * (exoticImDLUR * genH k - genH k * exoticImDLUR)) i j
           = genCOpVal i * (exoticImDLUR * genH k - genH k * exoticImDLUR) i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hD i i, if_pos rfl]
    · intro l _ hli
      rw [hD i l, if_neg (Ne.symm hli), zero_mul]
    · intro hcon; exact absurd (Finset.mem_univ i) hcon
  rw [hCD, hDC]
  by_cases hC : (exoticImDLUR * genH k - genH k * exoticImDLUR) i j = 0
  · rw [hC, zero_mul, mul_zero, sub_zero]
  · have hsupp := exoticImDLUR_CH_supp k i j hC
    have hw : genCOpVal j = genCOpVal i := by
      rcases hsupp with ⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩
      · rw [hix, hjy, exoticImDLUR_genCOpVal_2_eq, exoticImDLUR_genCOpVal_10_eq]
      · rw [hix, hjy, exoticImDLUR_genCOpVal_3_eq, exoticImDLUR_genCOpVal_10_eq]
      · rw [hix, hjy, exoticImDLUR_genCOpVal_4_eq, exoticImDLUR_genCOpVal_12_eq]
      · rw [hix, hjy, exoticImDLUR_genCOpVal_5_eq, exoticImDLUR_genCOpVal_12_eq]
      · rw [hix, hjy, exoticImDLUR_genCOpVal_6_eq, exoticImDLUR_genCOpVal_14_eq]
      · rw [hix, hjy, exoticImDLUR_genCOpVal_7_eq, exoticImDLUR_genCOpVal_14_eq]
      · rw [hix, hjy, exoticImDLUR_genCOpVal_10_eq, exoticImDLUR_genCOpVal_2_eq]
      · rw [hix, hjy, exoticImDLUR_genCOpVal_10_eq, exoticImDLUR_genCOpVal_3_eq]
      · rw [hix, hjy, exoticImDLUR_genCOpVal_12_eq, exoticImDLUR_genCOpVal_4_eq]
      · rw [hix, hjy, exoticImDLUR_genCOpVal_12_eq, exoticImDLUR_genCOpVal_5_eq]
      · rw [hix, hjy, exoticImDLUR_genCOpVal_14_eq, exoticImDLUR_genCOpVal_6_eq]
      · rw [hix, hjy, exoticImDLUR_genCOpVal_14_eq, exoticImDLUR_genCOpVal_7_eq]
    rw [hw, mul_comm, sub_self]

theorem exoticImDLUR_not_mem_RSH_of_ge16 {x : I32} (h : 16 ≤ x.val) :
    x ∉ ({2, 3, 4, 5, 6, 7, 10, 12, 14} : Finset I32) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h
  · intro hcon; rw [hcon] at h; simp at h

theorem exoticImDLUR_oo_H_H (k : Fin 3) (a : Fin 3) :
    (exoticImDLUR * genH k - genH k * exoticImDLUR) * (UJ * (genH a).transpose * UJ)
      - (UJ * (genH a).transpose * UJ) * (exoticImDLUR * genH k - genH k * exoticImDLUR) = 0 := by
  apply oo_disjoint _ _ _ {2, 3, 4, 5, 6, 7, 10, 12, 14}
  · intro i j hij
    have hsupp := exoticImDLUR_CH_supp k i j hij
    rcases hsupp with ⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩|⟨hix,hjy⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
    · rw [hix, hjy]; exact ⟨by decide, by decide⟩
  · intro x y hxy
    have hsupp := UJ_genH_transpose_UJ_supp a x y hxy
    exact ⟨exoticImDLUR_not_mem_RSH_of_ge16 hsupp.1, exoticImDLUR_not_mem_RSH_of_ge16 hsupp.2.2.1⟩

theorem exoticImDLUR_oo_H_M (k : Fin 3) (a : Fin 8) :
    (exoticImDLUR * genH k - genH k * exoticImDLUR) * (UJ * (genM a).transpose * UJ)
      - (UJ * (genM a).transpose * UJ) * (exoticImDLUR * genH k - genH k * exoticImDLUR) = 0 :=
  double_comm_of_comm exoticImDLUR (genH k) _ (exoticImDLUR_comm_MOp a) (comm_genH_MOp k a)

theorem exoticImDLUR_oo_H (k : Fin 3) (g2 : Fin 12) :
    (exoticImDLUR * genH k - genH k * exoticImDLUR) * smGenOp g2
      - smGenOp g2 * (exoticImDLUR * genH k - genH k * exoticImDLUR) = 0 := by
  fin_cases g2
  · exact exoticImDLUR_oo_H_C k
  · show (exoticImDLUR * genH k - genH k * exoticImDLUR) * (UJ * (genH 0).transpose * UJ)
        - (UJ * (genH 0).transpose * UJ) * (exoticImDLUR * genH k - genH k * exoticImDLUR) = 0
    exact exoticImDLUR_oo_H_H k 0
  · show (exoticImDLUR * genH k - genH k * exoticImDLUR) * (UJ * (genH 1).transpose * UJ)
        - (UJ * (genH 1).transpose * UJ) * (exoticImDLUR * genH k - genH k * exoticImDLUR) = 0
    exact exoticImDLUR_oo_H_H k 1
  · show (exoticImDLUR * genH k - genH k * exoticImDLUR) * (UJ * (genH 2).transpose * UJ)
        - (UJ * (genH 2).transpose * UJ) * (exoticImDLUR * genH k - genH k * exoticImDLUR) = 0
    exact exoticImDLUR_oo_H_H k 2
  · show (exoticImDLUR * genH k - genH k * exoticImDLUR) * (UJ * (genM 0).transpose * UJ)
        - (UJ * (genM 0).transpose * UJ) * (exoticImDLUR * genH k - genH k * exoticImDLUR) = 0
    exact exoticImDLUR_oo_H_M k 0
  · show (exoticImDLUR * genH k - genH k * exoticImDLUR) * (UJ * (genM 1).transpose * UJ)
        - (UJ * (genM 1).transpose * UJ) * (exoticImDLUR * genH k - genH k * exoticImDLUR) = 0
    exact exoticImDLUR_oo_H_M k 1
  · show (exoticImDLUR * genH k - genH k * exoticImDLUR) * (UJ * (genM 2).transpose * UJ)
        - (UJ * (genM 2).transpose * UJ) * (exoticImDLUR * genH k - genH k * exoticImDLUR) = 0
    exact exoticImDLUR_oo_H_M k 2
  · show (exoticImDLUR * genH k - genH k * exoticImDLUR) * (UJ * (genM 3).transpose * UJ)
        - (UJ * (genM 3).transpose * UJ) * (exoticImDLUR * genH k - genH k * exoticImDLUR) = 0
    exact exoticImDLUR_oo_H_M k 3
  · show (exoticImDLUR * genH k - genH k * exoticImDLUR) * (UJ * (genM 4).transpose * UJ)
        - (UJ * (genM 4).transpose * UJ) * (exoticImDLUR * genH k - genH k * exoticImDLUR) = 0
    exact exoticImDLUR_oo_H_M k 4
  · show (exoticImDLUR * genH k - genH k * exoticImDLUR) * (UJ * (genM 5).transpose * UJ)
        - (UJ * (genM 5).transpose * UJ) * (exoticImDLUR * genH k - genH k * exoticImDLUR) = 0
    exact exoticImDLUR_oo_H_M k 5
  · show (exoticImDLUR * genH k - genH k * exoticImDLUR) * (UJ * (genM 6).transpose * UJ)
        - (UJ * (genM 6).transpose * UJ) * (exoticImDLUR * genH k - genH k * exoticImDLUR) = 0
    exact exoticImDLUR_oo_H_M k 6
  · show (exoticImDLUR * genH k - genH k * exoticImDLUR) * (UJ * (genM 7).transpose * UJ)
        - (UJ * (genM 7).transpose * UJ) * (exoticImDLUR * genH k - genH k * exoticImDLUR) = 0
    exact exoticImDLUR_oo_H_M k 7

theorem exoticImDLUR_orderOne : OrderOneHolds exoticImDLUR := by
  intro g1 g2
  fin_cases g1
  · show (exoticImDLUR * genC - genC * exoticImDLUR) * smGenOp g2
        - smGenOp g2 * (exoticImDLUR * genC - genC * exoticImDLUR) = 0
    exact exoticImDLUR_oo_C g2
  · show (exoticImDLUR * genH 0 - genH 0 * exoticImDLUR) * smGenOp g2
        - smGenOp g2 * (exoticImDLUR * genH 0 - genH 0 * exoticImDLUR) = 0
    exact exoticImDLUR_oo_H 0 g2
  · show (exoticImDLUR * genH 1 - genH 1 * exoticImDLUR) * smGenOp g2
        - smGenOp g2 * (exoticImDLUR * genH 1 - genH 1 * exoticImDLUR) = 0
    exact exoticImDLUR_oo_H 1 g2
  · show (exoticImDLUR * genH 2 - genH 2 * exoticImDLUR) * smGenOp g2
        - smGenOp g2 * (exoticImDLUR * genH 2 - genH 2 * exoticImDLUR) = 0
    exact exoticImDLUR_oo_H 2 g2
  · show (exoticImDLUR * genM 0 - genM 0 * exoticImDLUR) * smGenOp g2
        - smGenOp g2 * (exoticImDLUR * genM 0 - genM 0 * exoticImDLUR) = 0
    exact exoticImDLUR_oo_M 0 g2
  · show (exoticImDLUR * genM 1 - genM 1 * exoticImDLUR) * smGenOp g2
        - smGenOp g2 * (exoticImDLUR * genM 1 - genM 1 * exoticImDLUR) = 0
    exact exoticImDLUR_oo_M 1 g2
  · show (exoticImDLUR * genM 2 - genM 2 * exoticImDLUR) * smGenOp g2
        - smGenOp g2 * (exoticImDLUR * genM 2 - genM 2 * exoticImDLUR) = 0
    exact exoticImDLUR_oo_M 2 g2
  · show (exoticImDLUR * genM 3 - genM 3 * exoticImDLUR) * smGenOp g2
        - smGenOp g2 * (exoticImDLUR * genM 3 - genM 3 * exoticImDLUR) = 0
    exact exoticImDLUR_oo_M 3 g2
  · show (exoticImDLUR * genM 4 - genM 4 * exoticImDLUR) * smGenOp g2
        - smGenOp g2 * (exoticImDLUR * genM 4 - genM 4 * exoticImDLUR) = 0
    exact exoticImDLUR_oo_M 4 g2
  · show (exoticImDLUR * genM 5 - genM 5 * exoticImDLUR) * smGenOp g2
        - smGenOp g2 * (exoticImDLUR * genM 5 - genM 5 * exoticImDLUR) = 0
    exact exoticImDLUR_oo_M 5 g2
  · show (exoticImDLUR * genM 6 - genM 6 * exoticImDLUR) * smGenOp g2
        - smGenOp g2 * (exoticImDLUR * genM 6 - genM 6 * exoticImDLUR) = 0
    exact exoticImDLUR_oo_M 6 g2
  · show (exoticImDLUR * genM 7 - genM 7 * exoticImDLUR) * smGenOp g2
        - smGenOp g2 * (exoticImDLUR * genM 7 - genM 7 * exoticImDLUR) = 0
    exact exoticImDLUR_oo_M 7 g2

/-! ## §T4a. Diagonal-pair killing: master lemma for the dimension bound

The four diagonal SM generators (C, σ₃, λ₃, λ₈) have integer eigenvalue patterns.
For D satisfying the order-one condition, the double commutator [[D, A], B]
with diagonal A, B forces D i j = 0 whenever the patterns separate i from j.
This is the key tool for killing off-support entries in the T4 census. -/

theorem tripletOf_inj (m n : Fin 32)
    (h : tripletOf m.val = tripletOf n.val) (hs : (tripletOf m.val).isSome = true) :
    m.val = n.val := by
  revert m n
  decide

/-- Integer eigenvalue patterns for the four diagonal generators. -/
def diagPat : Fin 4 → I32 → ℤ
  | 0, i => if 8 ≤ i.val ∧ i.val < 16 then 1
            else if i.val = 16 ∨ i.val = 17 ∨ i.val = 24 ∨ i.val = 25 then 1 else 0
  | 1, i => if i.val < 8 then (if i.val % 2 = 0 then 1 else -1) else 0
  | 2, i => match tripletOf i.val with
            | some (_, p) => if p.val = 0 then 1 else if p.val = 1 then -1 else 0
            | none => 0
  | 3, i => match tripletOf i.val with
            | some (_, p) => if p.val = 2 then -2 else 1
            | none => 0

/-- The four diagonal generators as smGen indices: C=0, H2=σ₃=3, M2=λ₃=6, M7=λ₈=11. -/
def diagIdx : Fin 4 → Fin 12
  | 0 => 0 | 1 => 3 | 2 => 6 | 3 => 11

/-- Nonzero scale factors: eigenvalue = scale * (pattern : ℂ). -/
noncomputable def diagScale : Fin 4 → ℂ
  | 0 => Complex.I | 1 => 1 | 2 => 1 | 3 => (Real.sqrt 3 : ℂ)⁻¹

theorem diagPat0 (i : I32) : diagPat 0 i =
    (if 8 ≤ i.val ∧ i.val < 16 then 1
     else if i.val = 16 ∨ i.val = 17 ∨ i.val = 24 ∨ i.val = 25 then 1 else 0 : ℤ) := rfl

theorem diagPat1 (i : I32) : diagPat 1 i =
    (if i.val < 8 then (if i.val % 2 = 0 then 1 else -1) else 0 : ℤ) := rfl

theorem diagScale_ne_zero (a : Fin 4) : diagScale a ≠ 0 := by
  fin_cases a
  · show Complex.I ≠ 0; exact Complex.I_ne_zero
  · show (1:ℂ) ≠ 0; exact one_ne_zero
  · show (1:ℂ) ≠ 0; exact one_ne_zero
  · show (Real.sqrt 3 : ℂ)⁻¹ ≠ 0
    apply inv_ne_zero
    have h : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    exact_mod_cast h

/-- genC diagonal values. -/
theorem genC_val (i : I32) : genC i i = Complex.I * ((diagPat 0 i : ℤ) : ℂ) := by
  have hCii : genC i i = (if 8 ≤ i.val ∧ i.val < 16 then Complex.I
      else if i.val = 16 ∨ i.val = 17 ∨ i.val = 24 ∨ i.val = 25 then Complex.I
      else 0) := by
    unfold genC
    rw [if_pos rfl]
  rw [hCii, diagPat0, Int.cast_ite, Int.cast_ite]
  split_ifs with h1 h2 <;> simp_all

/-- genH 2 (σ₃) diagonal values. -/
theorem genH2_val (i : I32) : genH 2 i i = ((diagPat 1 i : ℤ) : ℂ) := by
  have hpauli_diag : ∀ m : Fin 2, pauli 2 m m = (if m.val = 0 then 1 else -1 : ℂ) := by
    intro m; fin_cases m <;> simp [pauli]
  have hgenH : genH 2 i i =
      (if i.val < 8 ∧ i.val < 8 ∧ i.val / 2 = i.val / 2 then
        pauli 2 ⟨i.val % 2, Nat.mod_lt _ (by norm_num)⟩ ⟨i.val % 2, Nat.mod_lt _ (by norm_num)⟩
       else 0) := rfl
  rw [hgenH, diagPat1, Int.cast_ite, Int.cast_ite]
  by_cases hi8 : i.val < 8
  · rw [if_pos ⟨hi8, hi8, rfl⟩, if_pos hi8, hpauli_diag]
    by_cases hm : i.val % 2 = 0 <;> simp_all
  · rw [if_neg (fun h => hi8 h.1), if_neg hi8]
    simp

/-- genH 2 (σ₃) off-diagonal vanishes. -/
theorem genH2_off (i j : I32) (hij : i ≠ j) : genH 2 i j = 0 := by
  have hpauli_off : ∀ a b : Fin 2, a ≠ b → pauli 2 a b = 0 := by
    intro a b hab; fin_cases a <;> fin_cases b <;> simp_all [pauli]
  have hgenH : genH 2 i j =
      (if i.val < 8 ∧ j.val < 8 ∧ i.val / 2 = j.val / 2 then
        pauli 2 ⟨i.val % 2, Nat.mod_lt _ (by norm_num)⟩ ⟨j.val % 2, Nat.mod_lt _ (by norm_num)⟩
       else 0) := rfl
  rw [hgenH]
  by_cases hc : i.val < 8 ∧ j.val < 8 ∧ i.val / 2 = j.val / 2
  · rw [if_pos hc]
    have hmod : i.val % 2 ≠ j.val % 2 := by
      intro hcon
      apply hij
      apply Fin.ext
      have h1 : i.val = 2 * (i.val / 2) + i.val % 2 := (Nat.div_add_mod i.val 2).symm
      have h2 : j.val = 2 * (j.val / 2) + j.val % 2 := (Nat.div_add_mod j.val 2).symm
      omega
    apply hpauli_off
    simp [Fin.ext_iff]
    exact hmod
  · rw [if_neg hc]

/-- Generic off-diagonal vanishing for genM with diagonal gellMann. -/
theorem genM_off_of_gellMann_off (a : Fin 8) (i j : I32) (hij : i ≠ j)
    (hg_off : ∀ p1 p2 : Fin 3, p1 ≠ p2 → gellMann a p1 p2 = 0) :
    genM a i j = 0 := by
  have hgenM : genM a i j = (match tripletOf i.val, tripletOf j.val with
      | some (t1, p1), some (t2, p2) => if t1 = t2 then gellMann a p1 p2 else 0
      | _, _ => 0) := rfl
  rw [hgenM]
  cases hti : tripletOf i.val with
  | none => simp only
  | some tpi =>
    cases htj : tripletOf j.val with
    | none => simp only
    | some tpj =>
      obtain ⟨t1, p1⟩ := tpi
      obtain ⟨t2, p2⟩ := tpj
      simp only
      split_ifs with hte
      · by_cases hpe : p1 = p2
        · subst hpe
          exfalso
          apply hij; apply Fin.ext
          have heq : tripletOf i.val = tripletOf j.val := by
            rw [hti, htj, hte]
          have hs : (tripletOf i.val).isSome = true := by rw [hti]; rfl
          exact tripletOf_inj i j heq hs
        · exact hg_off p1 p2 hpe
      · rfl

/-- genM 2 (λ₃) off-diagonal vanishes. -/
theorem genM2_off (i j : I32) (hij : i ≠ j) : genM 2 i j = 0 := by
  apply genM_off_of_gellMann_off 2 i j hij
  intro p1 p2 hne; fin_cases p1 <;> fin_cases p2 <;> simp_all [gellMann]

/-- genM 7 (λ₈) off-diagonal vanishes. -/
theorem genM7_off (i j : I32) (hij : i ≠ j) : genM 7 i j = 0 := by
  apply genM_off_of_gellMann_off 7 i j hij
  intro p1 p2 hne; fin_cases p1 <;> fin_cases p2 <;> simp_all [gellMann]

theorem diagPat2 (i : I32) : diagPat 2 i =
    (match tripletOf i.val with
     | some (_, p) => (if p.val = 0 then 1 else if p.val = 1 then -1 else 0 : ℤ)
     | none => 0) := rfl

/-- genM 2 (λ₃) diagonal values. -/
theorem genM2_val (i : I32) : genM 2 i i = ((diagPat 2 i : ℤ) : ℂ) := by
  have hg2_diag : ∀ p : Fin 3, gellMann 2 p p =
      (if p.val = 0 then (1:ℂ) else if p.val = 1 then -1 else 0) := by
    intro p; fin_cases p <;> simp [gellMann]
  have hgenM : genM 2 i i = (match tripletOf i.val, tripletOf i.val with
      | some (t1, p1), some (t2, p2) => if t1 = t2 then gellMann 2 p1 p2 else 0
      | _, _ => 0) := rfl
  rw [hgenM, diagPat2]
  cases hti : tripletOf i.val with
  | none => simp
  | some tp =>
    obtain ⟨t, p⟩ := tp
    simp only
    fin_cases p <;> simp [gellMann]

theorem diagPat3 (i : I32) : diagPat 3 i =
    (match tripletOf i.val with
     | some (_, p) => (if p.val = 2 then -2 else 1 : ℤ)
     | none => 0) := rfl

/-- genM 7 (λ₈) diagonal values. -/
theorem genM7_val (i : I32) : genM 7 i i = (Real.sqrt 3 : ℂ)⁻¹ * ((diagPat 3 i : ℤ) : ℂ) := by
  have hgenM : genM 7 i i = (match tripletOf i.val, tripletOf i.val with
      | some (t1, p1), some (t2, p2) => if t1 = t2 then gellMann 7 p1 p2 else 0
      | _, _ => 0) := rfl
  rw [hgenM, diagPat3]
  cases hti : tripletOf i.val with
  | none => simp
  | some tp =>
    obtain ⟨t, p⟩ := tp
    simp only
    fin_cases p <;> simp [gellMann]

-- diagIdx values
theorem diagIdx0 : diagIdx 0 = (0 : Fin 12) := rfl
theorem diagIdx1 : diagIdx 1 = (3 : Fin 12) := rfl
theorem diagIdx2 : diagIdx 2 = (6 : Fin 12) := rfl
theorem diagIdx3 : diagIdx 3 = (11 : Fin 12) := rfl

-- diagScale values
theorem diagScale0 : diagScale 0 = Complex.I := rfl
theorem diagScale1 : diagScale 1 = (1 : ℂ) := rfl
theorem diagScale2 : diagScale 2 = (1 : ℂ) := rfl
theorem diagScale3 : diagScale 3 = (Real.sqrt 3 : ℂ)⁻¹ := rfl

-- smGen at diagonal indices
theorem smGen_zero : smGen (0 : Fin 12) = genC := rfl
theorem smGen_three : smGen (3 : Fin 12) = genH 2 := rfl
theorem smGen_six : smGen (6 : Fin 12) = genM 2 := rfl
theorem smGen_eleven : smGen (11 : Fin 12) = genM 7 := rfl

/-- The four diagonal generators are diagonal with the stated patterns. -/
theorem smGen_diag (a : Fin 4) (i j : I32) :
    smGen (diagIdx a) i j
      = if i = j then diagScale a * ((diagPat a i : ℤ) : ℂ) else 0 := by
  fin_cases a
  · show smGen (diagIdx (0 : Fin 4)) i j
      = if i = j then diagScale (0 : Fin 4) * ((diagPat (0 : Fin 4) i : ℤ) : ℂ) else 0
    rw [diagIdx0, smGen_zero, diagScale0]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl]; exact genC_val i
    · rw [if_neg hij]; exact genC_apply_ne hij
  · show smGen (diagIdx (1 : Fin 4)) i j
      = if i = j then diagScale (1 : Fin 4) * ((diagPat (1 : Fin 4) i : ℤ) : ℂ) else 0
    rw [diagIdx1, smGen_three, diagScale1]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, genH2_val i]; ring
    · rw [if_neg hij]; exact genH2_off i j hij
  · show smGen (diagIdx (2 : Fin 4)) i j
      = if i = j then diagScale (2 : Fin 4) * ((diagPat (2 : Fin 4) i : ℤ) : ℂ) else 0
    rw [diagIdx2, smGen_six, diagScale2]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, genM2_val i]; ring
    · rw [if_neg hij]; exact genM2_off i j hij
  · show smGen (diagIdx (3 : Fin 4)) i j
      = if i = j then diagScale (3 : Fin 4) * (((diagPat (3 : Fin 4) i : ℤ)) : ℂ) else 0
    rw [diagIdx3, smGen_eleven, diagScale3]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl]; exact genM7_val i
    · rw [if_neg hij]; exact genM7_off i j hij

/-- The opposite-algebra diagonal generators are diagonal with partner-twisted patterns. -/
theorem smGenOp_diag (b : Fin 4) (i j : I32) :
    smGenOp (diagIdx b) i j
      = if i = j then diagScale b * (((diagPat b (partner i) : ℤ)) : ℂ) else 0 := by
  rw [smGenOp_apply, smGen_diag]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg hij, if_neg]
    intro hcon
    exact hij (partner_injective hcon).symm

/-- Double commutator entry for diagonal A, B. -/
theorem dcomm_diag_entry
    (D A B : Matrix I32 I32 ℂ)
    (lam mu : I32 → ℂ)
    (hA : ∀ i j, A i j = if i = j then lam i else 0)
    (hB : ∀ i j, B i j = if i = j then mu i else 0)
    (i j : I32) :
    ((D * A - A * D) * B - B * (D * A - A * D)) i j
      = D i j * (lam j - lam i) * (mu j - mu i) := by
  have hAdiag : A = Matrix.diagonal lam := by
    ext p q
    rw [hA p q, Matrix.diagonal_apply]
  have hBdiag : B = Matrix.diagonal mu := by
    ext p q
    rw [hB p q, Matrix.diagonal_apply]
  have hDA : ∀ p q : I32, (D * A - A * D) p q = D p q * (lam q - lam p) := by
    intro p q
    rw [hAdiag, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    ring
  rw [hBdiag, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hDA i j]
  ring

/-- Master diagonal-pair killing lemma.
If D satisfies the order-one condition, and (a,b) are diagonal generator indices
whose integer eigenvalue patterns separate i from j (resp. partner-twisted),
then D i j = 0. -/
theorem diagonal_pair_kill (D : Matrix I32 I32 ℂ) (h_oo : OrderOneHolds D)
    (a b : Fin 4) (i j : I32)
    (h1 : diagPat a j ≠ diagPat a i)
    (h2 : diagPat b (partner j) ≠ diagPat b (partner i)) :
    D i j = 0 := by
  have hA : ∀ p q : I32, smGen (diagIdx a) p q =
      if p = q then diagScale a * ((diagPat a p : ℤ) : ℂ) else 0 :=
    fun p q => smGen_diag a p q
  have hB : ∀ p q : I32, smGenOp (diagIdx b) p q =
      if p = q then diagScale b * (((diagPat b (partner p) : ℤ)) : ℂ) else 0 :=
    fun p q => smGenOp_diag b p q
  have hdc := dcomm_diag_entry D (smGen (diagIdx a)) (smGenOp (diagIdx b))
    (fun k => diagScale a * ((diagPat a k : ℤ) : ℂ))
    (fun k => diagScale b * (((diagPat b (partner k) : ℤ)) : ℂ))
    hA hB i j
  have hzero := h_oo (diagIdx a) (diagIdx b)
  have he : ((D * smGen (diagIdx a) - smGen (diagIdx a) * D) * smGenOp (diagIdx b) -
      smGenOp (diagIdx b) * (D * smGen (diagIdx a) - smGen (diagIdx a) * D)) i j = 0 := by
    rw [hzero]; rfl
  rw [hdc] at he
  have hlam : diagScale a * ((diagPat a j : ℤ) : ℂ) - diagScale a * ((diagPat a i : ℤ) : ℂ) ≠ 0 := by
    have hsc := diagScale_ne_zero a
    have hpat : ((diagPat a j : ℤ) : ℂ) - ((diagPat a i : ℤ) : ℂ) ≠ 0 := by
      intro hcon
      apply h1
      have h2' : ((diagPat a j : ℤ) : ℂ) = ((diagPat a i : ℤ) : ℂ) := sub_eq_zero.mp hcon
      exact Int.cast_injective h2'
    have hfac : diagScale a * ((diagPat a j : ℤ) : ℂ) - diagScale a * ((diagPat a i : ℤ) : ℂ)
        = diagScale a * (((diagPat a j : ℤ) : ℂ) - ((diagPat a i : ℤ) : ℂ)) := by ring
    rw [hfac]
    exact mul_ne_zero hsc hpat
  have hmu : diagScale b * (((diagPat b (partner j) : ℤ)) : ℂ) -
      diagScale b * (((diagPat b (partner i) : ℤ)) : ℂ) ≠ 0 := by
    have hsc := diagScale_ne_zero b
    have hpat : (((diagPat b (partner j) : ℤ)) : ℂ) - (((diagPat b (partner i) : ℤ)) : ℂ) ≠ 0 := by
      intro hcon
      apply h2
      have h2' : (((diagPat b (partner j) : ℤ)) : ℂ) = (((diagPat b (partner i) : ℤ)) : ℂ) :=
        sub_eq_zero.mp hcon
      exact Int.cast_injective h2'
    have hfac : diagScale b * (((diagPat b (partner j) : ℤ)) : ℂ) -
        diagScale b * (((diagPat b (partner i) : ℤ)) : ℂ)
        = diagScale b * (((((diagPat b (partner j) : ℤ)) : ℂ) - (((diagPat b (partner i) : ℤ)) : ℂ))) := by ring
    rw [hfac]
    exact mul_ne_zero hsc hpat
  rcases mul_eq_zero.mp he with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd h' hlam
  · exact absurd h hmu


/-! ## §T4b. Entrywise vanishing for off-support indices -/

set_option maxRecDepth 10000

open Matrix

/-- gammaF diagonal entries are ±1. -/
theorem gammaF_diag_pm1 (i : I32) : gammaF i i = 1 ∨ gammaF i i = -1 := by
  unfold gammaF
  simp only
  by_cases h8 : i.val < 8
  · left; simp [h8]
  · by_cases h16 : i.val < 16
    · right; simp [h8, h16]
    · by_cases h24 : i.val < 24
      · right; simp [h8, h16, h24]
      · left; simp [h8, h16, h24]

/-- Grading killer. -/
theorem kill_grading (D : Matrix I32 I32 ℂ) (hgr : gammaF * D + D * gammaF = 0)
    (i j : I32) (hij : gammaF i i = gammaF j j) : D i j = 0 := by
  have he : (gammaF * D + D * gammaF) i j = 0 := by rw [hgr]; rfl
  rw [Matrix.add_apply] at he
  have h1 : (gammaF * D) i j = gammaF i i * D i j := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_single i
    · intro k _ hk
      rw [gammaF_apply_ne (Ne.symm hk), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have h2 : (D * gammaF) i j = D i j * gammaF j j := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_single j
    · intro k _ hk
      rw [gammaF_apply_ne hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [h1, h2, hij] at he
  rcases gammaF_diag_pm1 j with h | h
  · rw [h] at he
    have hzero : (2 : ℂ) * D i j = 0 := by
      calc (2 : ℂ) * D i j = 1 * D i j + D i j * 1 := by ring
        _ = 0 := he
    have h2ne : (2 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hzero).resolve_left h2ne
  · rw [h] at he
    have hzero : (-2 : ℂ) * D i j = 0 := by
      calc (-2 : ℂ) * D i j = -1 * D i j + D i j * -1 := by ring
        _ = 0 := he
    have h2ne : (-2 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hzero).resolve_left h2ne

/-- cfIndicator takes values 0 or 1. -/
theorem cfIndicator_zero_or_one (i : I32) : cfIndicator i = 0 ∨ cfIndicator i = 1 := by
  unfold cfIndicator
  by_cases h : i.val < 18 ∨ i.val = 24 ∨ i.val = 25
  · right; simp [h]
  · left; simp [h]

/-- cfMat killer. -/
theorem kill_cf (D : Matrix I32 I32 ℂ) (hcf : D * cfMat - cfMat * D = 0)
    (i j : I32) (hij : cfIndicator i ≠ cfIndicator j) : D i j = 0 := by
  have he : (D * cfMat - cfMat * D) i j = 0 := by rw [hcf]; rfl
  have hcf_diag : cfMat = Matrix.diagonal cfIndicator := rfl
  rw [hcf_diag, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at he
  rcases cfIndicator_zero_or_one i with hi | hi <;> rcases cfIndicator_zero_or_one j with hj | hj
  · rw [hi, hj] at hij; exact absurd rfl hij
  · rw [hi, hj] at he; simp at he; exact he
  · rw [hi, hj] at he; simp at he; exact he
  · rw [hi, hj] at hij; exact absurd rfl hij

/-- J-compatibility entrywise. -/
theorem j_compat_entry (D : Matrix I32 I32 ℂ) (hJ : IsJCompatible D) (i j : I32) :
    D i j = D (partner j) (partner i) := by
  have h := hJ
  have he : (UJ * D.transpose * UJ) i j = D i j := by rw [h]
  rw [UJ_conj_apply D.transpose i j, Matrix.transpose_apply] at he
  exact he.symm

/-- J-transport killer. -/
theorem kill_j_transport (D : Matrix I32 I32 ℂ) (hJ : IsJCompatible D)
    (i j : I32) (h : D (partner j) (partner i) = 0) : D i j = 0 := by
  rw [j_compat_entry D hJ i j]; exact h

/-- SA-transport killer. -/
theorem kill_sa_transport (D : Matrix I32 I32 ℂ) (hSA : D.conjTranspose = D)
    (i j : I32) (h : D j i = 0) : D i j = 0 := by
  have h1 : D i j = star (D j i) := by
    calc D i j = D.conjTranspose i j := by rw [hSA]
      _ = star (D j i) := by rw [Matrix.conjTranspose_apply]
  rw [h1]
  rw [h]
  exact star_zero ℂ

/-- The 72-entry support. -/
def support72 : Finset (ℕ × ℕ) :=
  {(0,8), (8,0), (1,9), (9,1), (2,10), (10,2), (3,11), (11,3),
   (4,12), (12,4), (5,13), (13,5), (6,14), (14,6), (7,15), (15,7),
   (16,24), (24,16), (17,25), (25,17), (18,26), (26,18), (19,27), (27,19),
   (20,28), (28,20), (21,29), (29,21), (22,30), (30,22), (23,31), (31,23),
   (8,24), (24,8), (0,9), (9,0), (16,25), (25,16), (1,8), (8,1), (17,24), (24,17),
   (2,11), (11,2), (18,27), (27,18), (4,13), (13,4), (20,29), (29,20),
   (6,15), (15,6), (22,31), (31,22), (3,10), (10,3), (19,26), (26,19),
   (5,12), (12,5), (21,28), (28,21), (7,14), (14,7), (23,30), (30,23),
   (8,25), (25,8), (24,9), (9,24), (9,25), (25,9)}

/-- All off-support entries vanish. -/
theorem D_off_support_zero (D : Matrix I32 I32 ℂ)
    (h_oo : OrderOneHolds D)
    (h_cf : cfCommutatorMap D = 0)
    (h_sa : D.conjTranspose = D)
    (h_J : IsJCompatible D)
    (h_gr : gammaF * D + D * gammaF = 0)
    (i j : I32) (h_off : (i.val, j.val) ∉ support72) : D i j = 0 := by
  have hcf' : D * cfMat - cfMat * D = 0 := by unfold cfCommutatorMap at h_cf; exact h_cf
  fin_cases i <;> fin_cases j
  · apply kill_grading D h_gr (0 : I32) (0 : I32); rfl
  · apply kill_grading D h_gr (0 : I32) (1 : I32); rfl
  · apply kill_grading D h_gr (0 : I32) (2 : I32); rfl
  · apply kill_grading D h_gr (0 : I32) (3 : I32); rfl
  · apply kill_grading D h_gr (0 : I32) (4 : I32); rfl
  · apply kill_grading D h_gr (0 : I32) (5 : I32); rfl
  · apply kill_grading D h_gr (0 : I32) (6 : I32); rfl
  · apply kill_grading D h_gr (0 : I32) (7 : I32); rfl
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (0 : I32) (10 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (0 : I32) (11 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (0 : I32) (12 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (0 : I32) (13 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (0 : I32) (14 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (0 : I32) (15 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (0 : I32) (16 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (0 : I32) (17 : I32) <;> decide
  · apply kill_cf D hcf' (0 : I32) (18 : I32)
    intro hcon
    have h1 : cfIndicator ((0 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((18 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (0 : I32) (19 : I32)
    intro hcon
    have h1 : cfIndicator ((0 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((19 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (0 : I32) (20 : I32)
    intro hcon
    have h1 : cfIndicator ((0 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((20 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (0 : I32) (21 : I32)
    intro hcon
    have h1 : cfIndicator ((0 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((21 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (0 : I32) (22 : I32)
    intro hcon
    have h1 : cfIndicator ((0 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((22 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (0 : I32) (23 : I32)
    intro hcon
    have h1 : cfIndicator ((0 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((23 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_grading D h_gr (0 : I32) (24 : I32); rfl
  · apply kill_grading D h_gr (0 : I32) (25 : I32); rfl
  · apply kill_grading D h_gr (0 : I32) (26 : I32); rfl
  · apply kill_grading D h_gr (0 : I32) (27 : I32); rfl
  · apply kill_grading D h_gr (0 : I32) (28 : I32); rfl
  · apply kill_grading D h_gr (0 : I32) (29 : I32); rfl
  · apply kill_grading D h_gr (0 : I32) (30 : I32); rfl
  · apply kill_grading D h_gr (0 : I32) (31 : I32); rfl
  · apply kill_grading D h_gr (1 : I32) (0 : I32); rfl
  · apply kill_grading D h_gr (1 : I32) (1 : I32); rfl
  · apply kill_grading D h_gr (1 : I32) (2 : I32); rfl
  · apply kill_grading D h_gr (1 : I32) (3 : I32); rfl
  · apply kill_grading D h_gr (1 : I32) (4 : I32); rfl
  · apply kill_grading D h_gr (1 : I32) (5 : I32); rfl
  · apply kill_grading D h_gr (1 : I32) (6 : I32); rfl
  · apply kill_grading D h_gr (1 : I32) (7 : I32); rfl
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (1 : I32) (10 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (1 : I32) (11 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (1 : I32) (12 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (1 : I32) (13 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (1 : I32) (14 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (1 : I32) (15 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (1 : I32) (16 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (1 : I32) (17 : I32) <;> decide
  · apply kill_cf D hcf' (1 : I32) (18 : I32)
    intro hcon
    have h1 : cfIndicator ((1 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((18 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (1 : I32) (19 : I32)
    intro hcon
    have h1 : cfIndicator ((1 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((19 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (1 : I32) (20 : I32)
    intro hcon
    have h1 : cfIndicator ((1 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((20 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (1 : I32) (21 : I32)
    intro hcon
    have h1 : cfIndicator ((1 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((21 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (1 : I32) (22 : I32)
    intro hcon
    have h1 : cfIndicator ((1 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((22 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (1 : I32) (23 : I32)
    intro hcon
    have h1 : cfIndicator ((1 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((23 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_grading D h_gr (1 : I32) (24 : I32); rfl
  · apply kill_grading D h_gr (1 : I32) (25 : I32); rfl
  · apply kill_grading D h_gr (1 : I32) (26 : I32); rfl
  · apply kill_grading D h_gr (1 : I32) (27 : I32); rfl
  · apply kill_grading D h_gr (1 : I32) (28 : I32); rfl
  · apply kill_grading D h_gr (1 : I32) (29 : I32); rfl
  · apply kill_grading D h_gr (1 : I32) (30 : I32); rfl
  · apply kill_grading D h_gr (1 : I32) (31 : I32); rfl
  · apply kill_grading D h_gr (2 : I32) (0 : I32); rfl
  · apply kill_grading D h_gr (2 : I32) (1 : I32); rfl
  · apply kill_grading D h_gr (2 : I32) (2 : I32); rfl
  · apply kill_grading D h_gr (2 : I32) (3 : I32); rfl
  · apply kill_grading D h_gr (2 : I32) (4 : I32); rfl
  · apply kill_grading D h_gr (2 : I32) (5 : I32); rfl
  · apply kill_grading D h_gr (2 : I32) (6 : I32); rfl
  · apply kill_grading D h_gr (2 : I32) (7 : I32); rfl
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (2 : I32) (8 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (2 : I32) (9 : I32) <;> decide
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (2 : I32) (12 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (2 : I32) (13 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (2 : I32) (14 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (2 : I32) (15 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (2 : I32) (16 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (2 : I32) (17 : I32) <;> decide
  · apply kill_cf D hcf' (2 : I32) (18 : I32)
    intro hcon
    have h1 : cfIndicator ((2 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((18 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (2 : I32) (19 : I32)
    intro hcon
    have h1 : cfIndicator ((2 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((19 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (2 : I32) (20 : I32)
    intro hcon
    have h1 : cfIndicator ((2 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((20 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (2 : I32) (21 : I32)
    intro hcon
    have h1 : cfIndicator ((2 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((21 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (2 : I32) (22 : I32)
    intro hcon
    have h1 : cfIndicator ((2 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((22 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (2 : I32) (23 : I32)
    intro hcon
    have h1 : cfIndicator ((2 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((23 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_grading D h_gr (2 : I32) (24 : I32); rfl
  · apply kill_grading D h_gr (2 : I32) (25 : I32); rfl
  · apply kill_grading D h_gr (2 : I32) (26 : I32); rfl
  · apply kill_grading D h_gr (2 : I32) (27 : I32); rfl
  · apply kill_grading D h_gr (2 : I32) (28 : I32); rfl
  · apply kill_grading D h_gr (2 : I32) (29 : I32); rfl
  · apply kill_grading D h_gr (2 : I32) (30 : I32); rfl
  · apply kill_grading D h_gr (2 : I32) (31 : I32); rfl
  · apply kill_grading D h_gr (3 : I32) (0 : I32); rfl
  · apply kill_grading D h_gr (3 : I32) (1 : I32); rfl
  · apply kill_grading D h_gr (3 : I32) (2 : I32); rfl
  · apply kill_grading D h_gr (3 : I32) (3 : I32); rfl
  · apply kill_grading D h_gr (3 : I32) (4 : I32); rfl
  · apply kill_grading D h_gr (3 : I32) (5 : I32); rfl
  · apply kill_grading D h_gr (3 : I32) (6 : I32); rfl
  · apply kill_grading D h_gr (3 : I32) (7 : I32); rfl
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (3 : I32) (8 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (3 : I32) (9 : I32) <;> decide
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (3 : I32) (12 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (3 : I32) (13 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (3 : I32) (14 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (3 : I32) (15 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (3 : I32) (16 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (3 : I32) (17 : I32) <;> decide
  · apply kill_cf D hcf' (3 : I32) (18 : I32)
    intro hcon
    have h1 : cfIndicator ((3 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((18 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (3 : I32) (19 : I32)
    intro hcon
    have h1 : cfIndicator ((3 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((19 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (3 : I32) (20 : I32)
    intro hcon
    have h1 : cfIndicator ((3 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((20 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (3 : I32) (21 : I32)
    intro hcon
    have h1 : cfIndicator ((3 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((21 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (3 : I32) (22 : I32)
    intro hcon
    have h1 : cfIndicator ((3 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((22 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (3 : I32) (23 : I32)
    intro hcon
    have h1 : cfIndicator ((3 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((23 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_grading D h_gr (3 : I32) (24 : I32); rfl
  · apply kill_grading D h_gr (3 : I32) (25 : I32); rfl
  · apply kill_grading D h_gr (3 : I32) (26 : I32); rfl
  · apply kill_grading D h_gr (3 : I32) (27 : I32); rfl
  · apply kill_grading D h_gr (3 : I32) (28 : I32); rfl
  · apply kill_grading D h_gr (3 : I32) (29 : I32); rfl
  · apply kill_grading D h_gr (3 : I32) (30 : I32); rfl
  · apply kill_grading D h_gr (3 : I32) (31 : I32); rfl
  · apply kill_grading D h_gr (4 : I32) (0 : I32); rfl
  · apply kill_grading D h_gr (4 : I32) (1 : I32); rfl
  · apply kill_grading D h_gr (4 : I32) (2 : I32); rfl
  · apply kill_grading D h_gr (4 : I32) (3 : I32); rfl
  · apply kill_grading D h_gr (4 : I32) (4 : I32); rfl
  · apply kill_grading D h_gr (4 : I32) (5 : I32); rfl
  · apply kill_grading D h_gr (4 : I32) (6 : I32); rfl
  · apply kill_grading D h_gr (4 : I32) (7 : I32); rfl
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (4 : I32) (8 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (4 : I32) (9 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (4 : I32) (10 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (4 : I32) (11 : I32) <;> decide
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (4 : I32) (14 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (4 : I32) (15 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (4 : I32) (16 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (4 : I32) (17 : I32) <;> decide
  · apply kill_cf D hcf' (4 : I32) (18 : I32)
    intro hcon
    have h1 : cfIndicator ((4 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((18 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (4 : I32) (19 : I32)
    intro hcon
    have h1 : cfIndicator ((4 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((19 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (4 : I32) (20 : I32)
    intro hcon
    have h1 : cfIndicator ((4 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((20 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (4 : I32) (21 : I32)
    intro hcon
    have h1 : cfIndicator ((4 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((21 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (4 : I32) (22 : I32)
    intro hcon
    have h1 : cfIndicator ((4 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((22 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (4 : I32) (23 : I32)
    intro hcon
    have h1 : cfIndicator ((4 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((23 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_grading D h_gr (4 : I32) (24 : I32); rfl
  · apply kill_grading D h_gr (4 : I32) (25 : I32); rfl
  · apply kill_grading D h_gr (4 : I32) (26 : I32); rfl
  · apply kill_grading D h_gr (4 : I32) (27 : I32); rfl
  · apply kill_grading D h_gr (4 : I32) (28 : I32); rfl
  · apply kill_grading D h_gr (4 : I32) (29 : I32); rfl
  · apply kill_grading D h_gr (4 : I32) (30 : I32); rfl
  · apply kill_grading D h_gr (4 : I32) (31 : I32); rfl
  · apply kill_grading D h_gr (5 : I32) (0 : I32); rfl
  · apply kill_grading D h_gr (5 : I32) (1 : I32); rfl
  · apply kill_grading D h_gr (5 : I32) (2 : I32); rfl
  · apply kill_grading D h_gr (5 : I32) (3 : I32); rfl
  · apply kill_grading D h_gr (5 : I32) (4 : I32); rfl
  · apply kill_grading D h_gr (5 : I32) (5 : I32); rfl
  · apply kill_grading D h_gr (5 : I32) (6 : I32); rfl
  · apply kill_grading D h_gr (5 : I32) (7 : I32); rfl
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (5 : I32) (8 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (5 : I32) (9 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (5 : I32) (10 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (5 : I32) (11 : I32) <;> decide
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (5 : I32) (14 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (5 : I32) (15 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (5 : I32) (16 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (5 : I32) (17 : I32) <;> decide
  · apply kill_cf D hcf' (5 : I32) (18 : I32)
    intro hcon
    have h1 : cfIndicator ((5 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((18 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (5 : I32) (19 : I32)
    intro hcon
    have h1 : cfIndicator ((5 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((19 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (5 : I32) (20 : I32)
    intro hcon
    have h1 : cfIndicator ((5 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((20 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (5 : I32) (21 : I32)
    intro hcon
    have h1 : cfIndicator ((5 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((21 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (5 : I32) (22 : I32)
    intro hcon
    have h1 : cfIndicator ((5 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((22 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (5 : I32) (23 : I32)
    intro hcon
    have h1 : cfIndicator ((5 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((23 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_grading D h_gr (5 : I32) (24 : I32); rfl
  · apply kill_grading D h_gr (5 : I32) (25 : I32); rfl
  · apply kill_grading D h_gr (5 : I32) (26 : I32); rfl
  · apply kill_grading D h_gr (5 : I32) (27 : I32); rfl
  · apply kill_grading D h_gr (5 : I32) (28 : I32); rfl
  · apply kill_grading D h_gr (5 : I32) (29 : I32); rfl
  · apply kill_grading D h_gr (5 : I32) (30 : I32); rfl
  · apply kill_grading D h_gr (5 : I32) (31 : I32); rfl
  · apply kill_grading D h_gr (6 : I32) (0 : I32); rfl
  · apply kill_grading D h_gr (6 : I32) (1 : I32); rfl
  · apply kill_grading D h_gr (6 : I32) (2 : I32); rfl
  · apply kill_grading D h_gr (6 : I32) (3 : I32); rfl
  · apply kill_grading D h_gr (6 : I32) (4 : I32); rfl
  · apply kill_grading D h_gr (6 : I32) (5 : I32); rfl
  · apply kill_grading D h_gr (6 : I32) (6 : I32); rfl
  · apply kill_grading D h_gr (6 : I32) (7 : I32); rfl
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (6 : I32) (8 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (6 : I32) (9 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (6 : I32) (10 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (6 : I32) (11 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (6 : I32) (12 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (6 : I32) (13 : I32) <;> decide
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (6 : I32) (16 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (6 : I32) (17 : I32) <;> decide
  · apply kill_cf D hcf' (6 : I32) (18 : I32)
    intro hcon
    have h1 : cfIndicator ((6 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((18 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (6 : I32) (19 : I32)
    intro hcon
    have h1 : cfIndicator ((6 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((19 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (6 : I32) (20 : I32)
    intro hcon
    have h1 : cfIndicator ((6 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((20 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (6 : I32) (21 : I32)
    intro hcon
    have h1 : cfIndicator ((6 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((21 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (6 : I32) (22 : I32)
    intro hcon
    have h1 : cfIndicator ((6 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((22 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (6 : I32) (23 : I32)
    intro hcon
    have h1 : cfIndicator ((6 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((23 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_grading D h_gr (6 : I32) (24 : I32); rfl
  · apply kill_grading D h_gr (6 : I32) (25 : I32); rfl
  · apply kill_grading D h_gr (6 : I32) (26 : I32); rfl
  · apply kill_grading D h_gr (6 : I32) (27 : I32); rfl
  · apply kill_grading D h_gr (6 : I32) (28 : I32); rfl
  · apply kill_grading D h_gr (6 : I32) (29 : I32); rfl
  · apply kill_grading D h_gr (6 : I32) (30 : I32); rfl
  · apply kill_grading D h_gr (6 : I32) (31 : I32); rfl
  · apply kill_grading D h_gr (7 : I32) (0 : I32); rfl
  · apply kill_grading D h_gr (7 : I32) (1 : I32); rfl
  · apply kill_grading D h_gr (7 : I32) (2 : I32); rfl
  · apply kill_grading D h_gr (7 : I32) (3 : I32); rfl
  · apply kill_grading D h_gr (7 : I32) (4 : I32); rfl
  · apply kill_grading D h_gr (7 : I32) (5 : I32); rfl
  · apply kill_grading D h_gr (7 : I32) (6 : I32); rfl
  · apply kill_grading D h_gr (7 : I32) (7 : I32); rfl
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (7 : I32) (8 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (7 : I32) (9 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (7 : I32) (10 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (7 : I32) (11 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (7 : I32) (12 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (7 : I32) (13 : I32) <;> decide
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (7 : I32) (16 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (7 : I32) (17 : I32) <;> decide
  · apply kill_cf D hcf' (7 : I32) (18 : I32)
    intro hcon
    have h1 : cfIndicator ((7 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((18 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (7 : I32) (19 : I32)
    intro hcon
    have h1 : cfIndicator ((7 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((19 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (7 : I32) (20 : I32)
    intro hcon
    have h1 : cfIndicator ((7 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((20 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (7 : I32) (21 : I32)
    intro hcon
    have h1 : cfIndicator ((7 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((21 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (7 : I32) (22 : I32)
    intro hcon
    have h1 : cfIndicator ((7 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((22 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (7 : I32) (23 : I32)
    intro hcon
    have h1 : cfIndicator ((7 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((23 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_grading D h_gr (7 : I32) (24 : I32); rfl
  · apply kill_grading D h_gr (7 : I32) (25 : I32); rfl
  · apply kill_grading D h_gr (7 : I32) (26 : I32); rfl
  · apply kill_grading D h_gr (7 : I32) (27 : I32); rfl
  · apply kill_grading D h_gr (7 : I32) (28 : I32); rfl
  · apply kill_grading D h_gr (7 : I32) (29 : I32); rfl
  · apply kill_grading D h_gr (7 : I32) (30 : I32); rfl
  · apply kill_grading D h_gr (7 : I32) (31 : I32); rfl
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (8 : I32) (2 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (8 : I32) (3 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (8 : I32) (4 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (8 : I32) (5 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (8 : I32) (6 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (8 : I32) (7 : I32) <;> decide
  · apply kill_grading D h_gr (8 : I32) (8 : I32); rfl
  · apply kill_grading D h_gr (8 : I32) (9 : I32); rfl
  · apply kill_grading D h_gr (8 : I32) (10 : I32); rfl
  · apply kill_grading D h_gr (8 : I32) (11 : I32); rfl
  · apply kill_grading D h_gr (8 : I32) (12 : I32); rfl
  · apply kill_grading D h_gr (8 : I32) (13 : I32); rfl
  · apply kill_grading D h_gr (8 : I32) (14 : I32); rfl
  · apply kill_grading D h_gr (8 : I32) (15 : I32); rfl
  · apply kill_grading D h_gr (8 : I32) (16 : I32); rfl
  · apply kill_grading D h_gr (8 : I32) (17 : I32); rfl
  · apply kill_grading D h_gr (8 : I32) (18 : I32); rfl
  · apply kill_grading D h_gr (8 : I32) (19 : I32); rfl
  · apply kill_grading D h_gr (8 : I32) (20 : I32); rfl
  · apply kill_grading D h_gr (8 : I32) (21 : I32); rfl
  · apply kill_grading D h_gr (8 : I32) (22 : I32); rfl
  · apply kill_grading D h_gr (8 : I32) (23 : I32); rfl
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply kill_cf D hcf' (8 : I32) (26 : I32)
    intro hcon
    have h1 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (8 : I32) (27 : I32)
    intro hcon
    have h1 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (8 : I32) (28 : I32)
    intro hcon
    have h1 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (8 : I32) (29 : I32)
    intro hcon
    have h1 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (8 : I32) (30 : I32)
    intro hcon
    have h1 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (8 : I32) (31 : I32)
    intro hcon
    have h1 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (9 : I32) (2 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (9 : I32) (3 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (9 : I32) (4 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (9 : I32) (5 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (9 : I32) (6 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (9 : I32) (7 : I32) <;> decide
  · apply kill_grading D h_gr (9 : I32) (8 : I32); rfl
  · apply kill_grading D h_gr (9 : I32) (9 : I32); rfl
  · apply kill_grading D h_gr (9 : I32) (10 : I32); rfl
  · apply kill_grading D h_gr (9 : I32) (11 : I32); rfl
  · apply kill_grading D h_gr (9 : I32) (12 : I32); rfl
  · apply kill_grading D h_gr (9 : I32) (13 : I32); rfl
  · apply kill_grading D h_gr (9 : I32) (14 : I32); rfl
  · apply kill_grading D h_gr (9 : I32) (15 : I32); rfl
  · apply kill_grading D h_gr (9 : I32) (16 : I32); rfl
  · apply kill_grading D h_gr (9 : I32) (17 : I32); rfl
  · apply kill_grading D h_gr (9 : I32) (18 : I32); rfl
  · apply kill_grading D h_gr (9 : I32) (19 : I32); rfl
  · apply kill_grading D h_gr (9 : I32) (20 : I32); rfl
  · apply kill_grading D h_gr (9 : I32) (21 : I32); rfl
  · apply kill_grading D h_gr (9 : I32) (22 : I32); rfl
  · apply kill_grading D h_gr (9 : I32) (23 : I32); rfl
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply kill_cf D hcf' (9 : I32) (26 : I32)
    intro hcon
    have h1 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (9 : I32) (27 : I32)
    intro hcon
    have h1 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (9 : I32) (28 : I32)
    intro hcon
    have h1 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (9 : I32) (29 : I32)
    intro hcon
    have h1 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (9 : I32) (30 : I32)
    intro hcon
    have h1 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (9 : I32) (31 : I32)
    intro hcon
    have h1 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (10 : I32) (0 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (10 : I32) (1 : I32) <;> decide
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (10 : I32) (4 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (10 : I32) (5 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (10 : I32) (6 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (10 : I32) (7 : I32) <;> decide
  · apply kill_grading D h_gr (10 : I32) (8 : I32); rfl
  · apply kill_grading D h_gr (10 : I32) (9 : I32); rfl
  · apply kill_grading D h_gr (10 : I32) (10 : I32); rfl
  · apply kill_grading D h_gr (10 : I32) (11 : I32); rfl
  · apply kill_grading D h_gr (10 : I32) (12 : I32); rfl
  · apply kill_grading D h_gr (10 : I32) (13 : I32); rfl
  · apply kill_grading D h_gr (10 : I32) (14 : I32); rfl
  · apply kill_grading D h_gr (10 : I32) (15 : I32); rfl
  · apply kill_grading D h_gr (10 : I32) (16 : I32); rfl
  · apply kill_grading D h_gr (10 : I32) (17 : I32); rfl
  · apply kill_grading D h_gr (10 : I32) (18 : I32); rfl
  · apply kill_grading D h_gr (10 : I32) (19 : I32); rfl
  · apply kill_grading D h_gr (10 : I32) (20 : I32); rfl
  · apply kill_grading D h_gr (10 : I32) (21 : I32); rfl
  · apply kill_grading D h_gr (10 : I32) (22 : I32); rfl
  · apply kill_grading D h_gr (10 : I32) (23 : I32); rfl
  · apply kill_j_transport D h_J (10 : I32) (24 : I32)
    have hp1 : partner ((24 : I32) : I32) = ((8 : I32) : I32) := by decide
    have hp2 : partner ((10 : I32) : I32) = ((26 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (8 : I32) (26 : I32)
    intro hcon
    have h1 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_j_transport D h_J (10 : I32) (25 : I32)
    have hp1 : partner ((25 : I32) : I32) = ((9 : I32) : I32) := by decide
    have hp2 : partner ((10 : I32) : I32) = ((26 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (9 : I32) (26 : I32)
    intro hcon
    have h1 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (10 : I32) (26 : I32)
    intro hcon
    have h1 : cfIndicator ((10 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (10 : I32) (27 : I32)
    intro hcon
    have h1 : cfIndicator ((10 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (10 : I32) (28 : I32)
    intro hcon
    have h1 : cfIndicator ((10 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (10 : I32) (29 : I32)
    intro hcon
    have h1 : cfIndicator ((10 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (10 : I32) (30 : I32)
    intro hcon
    have h1 : cfIndicator ((10 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (10 : I32) (31 : I32)
    intro hcon
    have h1 : cfIndicator ((10 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (11 : I32) (0 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (11 : I32) (1 : I32) <;> decide
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (11 : I32) (4 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (11 : I32) (5 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (11 : I32) (6 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (11 : I32) (7 : I32) <;> decide
  · apply kill_grading D h_gr (11 : I32) (8 : I32); rfl
  · apply kill_grading D h_gr (11 : I32) (9 : I32); rfl
  · apply kill_grading D h_gr (11 : I32) (10 : I32); rfl
  · apply kill_grading D h_gr (11 : I32) (11 : I32); rfl
  · apply kill_grading D h_gr (11 : I32) (12 : I32); rfl
  · apply kill_grading D h_gr (11 : I32) (13 : I32); rfl
  · apply kill_grading D h_gr (11 : I32) (14 : I32); rfl
  · apply kill_grading D h_gr (11 : I32) (15 : I32); rfl
  · apply kill_grading D h_gr (11 : I32) (16 : I32); rfl
  · apply kill_grading D h_gr (11 : I32) (17 : I32); rfl
  · apply kill_grading D h_gr (11 : I32) (18 : I32); rfl
  · apply kill_grading D h_gr (11 : I32) (19 : I32); rfl
  · apply kill_grading D h_gr (11 : I32) (20 : I32); rfl
  · apply kill_grading D h_gr (11 : I32) (21 : I32); rfl
  · apply kill_grading D h_gr (11 : I32) (22 : I32); rfl
  · apply kill_grading D h_gr (11 : I32) (23 : I32); rfl
  · apply kill_j_transport D h_J (11 : I32) (24 : I32)
    have hp1 : partner ((24 : I32) : I32) = ((8 : I32) : I32) := by decide
    have hp2 : partner ((11 : I32) : I32) = ((27 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (8 : I32) (27 : I32)
    intro hcon
    have h1 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_j_transport D h_J (11 : I32) (25 : I32)
    have hp1 : partner ((25 : I32) : I32) = ((9 : I32) : I32) := by decide
    have hp2 : partner ((11 : I32) : I32) = ((27 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (9 : I32) (27 : I32)
    intro hcon
    have h1 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (11 : I32) (26 : I32)
    intro hcon
    have h1 : cfIndicator ((11 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (11 : I32) (27 : I32)
    intro hcon
    have h1 : cfIndicator ((11 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (11 : I32) (28 : I32)
    intro hcon
    have h1 : cfIndicator ((11 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (11 : I32) (29 : I32)
    intro hcon
    have h1 : cfIndicator ((11 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (11 : I32) (30 : I32)
    intro hcon
    have h1 : cfIndicator ((11 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (11 : I32) (31 : I32)
    intro hcon
    have h1 : cfIndicator ((11 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (12 : I32) (0 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (12 : I32) (1 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (12 : I32) (2 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (12 : I32) (3 : I32) <;> decide
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (12 : I32) (6 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (12 : I32) (7 : I32) <;> decide
  · apply kill_grading D h_gr (12 : I32) (8 : I32); rfl
  · apply kill_grading D h_gr (12 : I32) (9 : I32); rfl
  · apply kill_grading D h_gr (12 : I32) (10 : I32); rfl
  · apply kill_grading D h_gr (12 : I32) (11 : I32); rfl
  · apply kill_grading D h_gr (12 : I32) (12 : I32); rfl
  · apply kill_grading D h_gr (12 : I32) (13 : I32); rfl
  · apply kill_grading D h_gr (12 : I32) (14 : I32); rfl
  · apply kill_grading D h_gr (12 : I32) (15 : I32); rfl
  · apply kill_grading D h_gr (12 : I32) (16 : I32); rfl
  · apply kill_grading D h_gr (12 : I32) (17 : I32); rfl
  · apply kill_grading D h_gr (12 : I32) (18 : I32); rfl
  · apply kill_grading D h_gr (12 : I32) (19 : I32); rfl
  · apply kill_grading D h_gr (12 : I32) (20 : I32); rfl
  · apply kill_grading D h_gr (12 : I32) (21 : I32); rfl
  · apply kill_grading D h_gr (12 : I32) (22 : I32); rfl
  · apply kill_grading D h_gr (12 : I32) (23 : I32); rfl
  · apply kill_j_transport D h_J (12 : I32) (24 : I32)
    have hp1 : partner ((24 : I32) : I32) = ((8 : I32) : I32) := by decide
    have hp2 : partner ((12 : I32) : I32) = ((28 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (8 : I32) (28 : I32)
    intro hcon
    have h1 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_j_transport D h_J (12 : I32) (25 : I32)
    have hp1 : partner ((25 : I32) : I32) = ((9 : I32) : I32) := by decide
    have hp2 : partner ((12 : I32) : I32) = ((28 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (9 : I32) (28 : I32)
    intro hcon
    have h1 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (12 : I32) (26 : I32)
    intro hcon
    have h1 : cfIndicator ((12 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (12 : I32) (27 : I32)
    intro hcon
    have h1 : cfIndicator ((12 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (12 : I32) (28 : I32)
    intro hcon
    have h1 : cfIndicator ((12 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (12 : I32) (29 : I32)
    intro hcon
    have h1 : cfIndicator ((12 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (12 : I32) (30 : I32)
    intro hcon
    have h1 : cfIndicator ((12 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (12 : I32) (31 : I32)
    intro hcon
    have h1 : cfIndicator ((12 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (13 : I32) (0 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (13 : I32) (1 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (13 : I32) (2 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (13 : I32) (3 : I32) <;> decide
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (13 : I32) (6 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (13 : I32) (7 : I32) <;> decide
  · apply kill_grading D h_gr (13 : I32) (8 : I32); rfl
  · apply kill_grading D h_gr (13 : I32) (9 : I32); rfl
  · apply kill_grading D h_gr (13 : I32) (10 : I32); rfl
  · apply kill_grading D h_gr (13 : I32) (11 : I32); rfl
  · apply kill_grading D h_gr (13 : I32) (12 : I32); rfl
  · apply kill_grading D h_gr (13 : I32) (13 : I32); rfl
  · apply kill_grading D h_gr (13 : I32) (14 : I32); rfl
  · apply kill_grading D h_gr (13 : I32) (15 : I32); rfl
  · apply kill_grading D h_gr (13 : I32) (16 : I32); rfl
  · apply kill_grading D h_gr (13 : I32) (17 : I32); rfl
  · apply kill_grading D h_gr (13 : I32) (18 : I32); rfl
  · apply kill_grading D h_gr (13 : I32) (19 : I32); rfl
  · apply kill_grading D h_gr (13 : I32) (20 : I32); rfl
  · apply kill_grading D h_gr (13 : I32) (21 : I32); rfl
  · apply kill_grading D h_gr (13 : I32) (22 : I32); rfl
  · apply kill_grading D h_gr (13 : I32) (23 : I32); rfl
  · apply kill_j_transport D h_J (13 : I32) (24 : I32)
    have hp1 : partner ((24 : I32) : I32) = ((8 : I32) : I32) := by decide
    have hp2 : partner ((13 : I32) : I32) = ((29 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (8 : I32) (29 : I32)
    intro hcon
    have h1 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_j_transport D h_J (13 : I32) (25 : I32)
    have hp1 : partner ((25 : I32) : I32) = ((9 : I32) : I32) := by decide
    have hp2 : partner ((13 : I32) : I32) = ((29 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (9 : I32) (29 : I32)
    intro hcon
    have h1 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (13 : I32) (26 : I32)
    intro hcon
    have h1 : cfIndicator ((13 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (13 : I32) (27 : I32)
    intro hcon
    have h1 : cfIndicator ((13 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (13 : I32) (28 : I32)
    intro hcon
    have h1 : cfIndicator ((13 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (13 : I32) (29 : I32)
    intro hcon
    have h1 : cfIndicator ((13 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (13 : I32) (30 : I32)
    intro hcon
    have h1 : cfIndicator ((13 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (13 : I32) (31 : I32)
    intro hcon
    have h1 : cfIndicator ((13 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (14 : I32) (0 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (14 : I32) (1 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (14 : I32) (2 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (14 : I32) (3 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (14 : I32) (4 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (14 : I32) (5 : I32) <;> decide
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply kill_grading D h_gr (14 : I32) (8 : I32); rfl
  · apply kill_grading D h_gr (14 : I32) (9 : I32); rfl
  · apply kill_grading D h_gr (14 : I32) (10 : I32); rfl
  · apply kill_grading D h_gr (14 : I32) (11 : I32); rfl
  · apply kill_grading D h_gr (14 : I32) (12 : I32); rfl
  · apply kill_grading D h_gr (14 : I32) (13 : I32); rfl
  · apply kill_grading D h_gr (14 : I32) (14 : I32); rfl
  · apply kill_grading D h_gr (14 : I32) (15 : I32); rfl
  · apply kill_grading D h_gr (14 : I32) (16 : I32); rfl
  · apply kill_grading D h_gr (14 : I32) (17 : I32); rfl
  · apply kill_grading D h_gr (14 : I32) (18 : I32); rfl
  · apply kill_grading D h_gr (14 : I32) (19 : I32); rfl
  · apply kill_grading D h_gr (14 : I32) (20 : I32); rfl
  · apply kill_grading D h_gr (14 : I32) (21 : I32); rfl
  · apply kill_grading D h_gr (14 : I32) (22 : I32); rfl
  · apply kill_grading D h_gr (14 : I32) (23 : I32); rfl
  · apply kill_j_transport D h_J (14 : I32) (24 : I32)
    have hp1 : partner ((24 : I32) : I32) = ((8 : I32) : I32) := by decide
    have hp2 : partner ((14 : I32) : I32) = ((30 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (8 : I32) (30 : I32)
    intro hcon
    have h1 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_j_transport D h_J (14 : I32) (25 : I32)
    have hp1 : partner ((25 : I32) : I32) = ((9 : I32) : I32) := by decide
    have hp2 : partner ((14 : I32) : I32) = ((30 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (9 : I32) (30 : I32)
    intro hcon
    have h1 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (14 : I32) (26 : I32)
    intro hcon
    have h1 : cfIndicator ((14 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (14 : I32) (27 : I32)
    intro hcon
    have h1 : cfIndicator ((14 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (14 : I32) (28 : I32)
    intro hcon
    have h1 : cfIndicator ((14 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (14 : I32) (29 : I32)
    intro hcon
    have h1 : cfIndicator ((14 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (14 : I32) (30 : I32)
    intro hcon
    have h1 : cfIndicator ((14 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (14 : I32) (31 : I32)
    intro hcon
    have h1 : cfIndicator ((14 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (15 : I32) (0 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (15 : I32) (1 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (15 : I32) (2 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (15 : I32) (3 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (15 : I32) (4 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (2 : Fin 4) (15 : I32) (5 : I32) <;> decide
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply kill_grading D h_gr (15 : I32) (8 : I32); rfl
  · apply kill_grading D h_gr (15 : I32) (9 : I32); rfl
  · apply kill_grading D h_gr (15 : I32) (10 : I32); rfl
  · apply kill_grading D h_gr (15 : I32) (11 : I32); rfl
  · apply kill_grading D h_gr (15 : I32) (12 : I32); rfl
  · apply kill_grading D h_gr (15 : I32) (13 : I32); rfl
  · apply kill_grading D h_gr (15 : I32) (14 : I32); rfl
  · apply kill_grading D h_gr (15 : I32) (15 : I32); rfl
  · apply kill_grading D h_gr (15 : I32) (16 : I32); rfl
  · apply kill_grading D h_gr (15 : I32) (17 : I32); rfl
  · apply kill_grading D h_gr (15 : I32) (18 : I32); rfl
  · apply kill_grading D h_gr (15 : I32) (19 : I32); rfl
  · apply kill_grading D h_gr (15 : I32) (20 : I32); rfl
  · apply kill_grading D h_gr (15 : I32) (21 : I32); rfl
  · apply kill_grading D h_gr (15 : I32) (22 : I32); rfl
  · apply kill_grading D h_gr (15 : I32) (23 : I32); rfl
  · apply kill_j_transport D h_J (15 : I32) (24 : I32)
    have hp1 : partner ((24 : I32) : I32) = ((8 : I32) : I32) := by decide
    have hp2 : partner ((15 : I32) : I32) = ((31 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (8 : I32) (31 : I32)
    intro hcon
    have h1 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_j_transport D h_J (15 : I32) (25 : I32)
    have hp1 : partner ((25 : I32) : I32) = ((9 : I32) : I32) := by decide
    have hp2 : partner ((15 : I32) : I32) = ((31 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (9 : I32) (31 : I32)
    intro hcon
    have h1 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (15 : I32) (26 : I32)
    intro hcon
    have h1 : cfIndicator ((15 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (15 : I32) (27 : I32)
    intro hcon
    have h1 : cfIndicator ((15 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (15 : I32) (28 : I32)
    intro hcon
    have h1 : cfIndicator ((15 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (15 : I32) (29 : I32)
    intro hcon
    have h1 : cfIndicator ((15 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (15 : I32) (30 : I32)
    intro hcon
    have h1 : cfIndicator ((15 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (15 : I32) (31 : I32)
    intro hcon
    have h1 : cfIndicator ((15 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (16 : I32) (0 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (16 : I32) (1 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (16 : I32) (2 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (16 : I32) (3 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (16 : I32) (4 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (16 : I32) (5 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (16 : I32) (6 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (16 : I32) (7 : I32) <;> decide
  · apply kill_grading D h_gr (16 : I32) (8 : I32); rfl
  · apply kill_grading D h_gr (16 : I32) (9 : I32); rfl
  · apply kill_grading D h_gr (16 : I32) (10 : I32); rfl
  · apply kill_grading D h_gr (16 : I32) (11 : I32); rfl
  · apply kill_grading D h_gr (16 : I32) (12 : I32); rfl
  · apply kill_grading D h_gr (16 : I32) (13 : I32); rfl
  · apply kill_grading D h_gr (16 : I32) (14 : I32); rfl
  · apply kill_grading D h_gr (16 : I32) (15 : I32); rfl
  · apply kill_grading D h_gr (16 : I32) (16 : I32); rfl
  · apply kill_grading D h_gr (16 : I32) (17 : I32); rfl
  · apply kill_grading D h_gr (16 : I32) (18 : I32); rfl
  · apply kill_grading D h_gr (16 : I32) (19 : I32); rfl
  · apply kill_grading D h_gr (16 : I32) (20 : I32); rfl
  · apply kill_grading D h_gr (16 : I32) (21 : I32); rfl
  · apply kill_grading D h_gr (16 : I32) (22 : I32); rfl
  · apply kill_grading D h_gr (16 : I32) (23 : I32); rfl
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply kill_cf D hcf' (16 : I32) (26 : I32)
    intro hcon
    have h1 : cfIndicator ((16 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (16 : I32) (27 : I32)
    intro hcon
    have h1 : cfIndicator ((16 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (16 : I32) (28 : I32)
    intro hcon
    have h1 : cfIndicator ((16 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (16 : I32) (29 : I32)
    intro hcon
    have h1 : cfIndicator ((16 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (16 : I32) (30 : I32)
    intro hcon
    have h1 : cfIndicator ((16 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (16 : I32) (31 : I32)
    intro hcon
    have h1 : cfIndicator ((16 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (17 : I32) (0 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (0 : Fin 4) (17 : I32) (1 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (17 : I32) (2 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (17 : I32) (3 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (17 : I32) (4 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (17 : I32) (5 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (17 : I32) (6 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (0 : Fin 4) (1 : Fin 4) (17 : I32) (7 : I32) <;> decide
  · apply kill_grading D h_gr (17 : I32) (8 : I32); rfl
  · apply kill_grading D h_gr (17 : I32) (9 : I32); rfl
  · apply kill_grading D h_gr (17 : I32) (10 : I32); rfl
  · apply kill_grading D h_gr (17 : I32) (11 : I32); rfl
  · apply kill_grading D h_gr (17 : I32) (12 : I32); rfl
  · apply kill_grading D h_gr (17 : I32) (13 : I32); rfl
  · apply kill_grading D h_gr (17 : I32) (14 : I32); rfl
  · apply kill_grading D h_gr (17 : I32) (15 : I32); rfl
  · apply kill_grading D h_gr (17 : I32) (16 : I32); rfl
  · apply kill_grading D h_gr (17 : I32) (17 : I32); rfl
  · apply kill_grading D h_gr (17 : I32) (18 : I32); rfl
  · apply kill_grading D h_gr (17 : I32) (19 : I32); rfl
  · apply kill_grading D h_gr (17 : I32) (20 : I32); rfl
  · apply kill_grading D h_gr (17 : I32) (21 : I32); rfl
  · apply kill_grading D h_gr (17 : I32) (22 : I32); rfl
  · apply kill_grading D h_gr (17 : I32) (23 : I32); rfl
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply kill_cf D hcf' (17 : I32) (26 : I32)
    intro hcon
    have h1 : cfIndicator ((17 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (17 : I32) (27 : I32)
    intro hcon
    have h1 : cfIndicator ((17 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (17 : I32) (28 : I32)
    intro hcon
    have h1 : cfIndicator ((17 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (17 : I32) (29 : I32)
    intro hcon
    have h1 : cfIndicator ((17 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (17 : I32) (30 : I32)
    intro hcon
    have h1 : cfIndicator ((17 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (17 : I32) (31 : I32)
    intro hcon
    have h1 : cfIndicator ((17 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (18 : I32) (0 : I32)
    intro hcon
    have h1 : cfIndicator ((18 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((0 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (18 : I32) (1 : I32)
    intro hcon
    have h1 : cfIndicator ((18 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((1 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (18 : I32) (2 : I32)
    intro hcon
    have h1 : cfIndicator ((18 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((2 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (18 : I32) (3 : I32)
    intro hcon
    have h1 : cfIndicator ((18 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((3 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (18 : I32) (4 : I32)
    intro hcon
    have h1 : cfIndicator ((18 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((4 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (18 : I32) (5 : I32)
    intro hcon
    have h1 : cfIndicator ((18 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((5 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (18 : I32) (6 : I32)
    intro hcon
    have h1 : cfIndicator ((18 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((6 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (18 : I32) (7 : I32)
    intro hcon
    have h1 : cfIndicator ((18 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((7 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_grading D h_gr (18 : I32) (8 : I32); rfl
  · apply kill_grading D h_gr (18 : I32) (9 : I32); rfl
  · apply kill_grading D h_gr (18 : I32) (10 : I32); rfl
  · apply kill_grading D h_gr (18 : I32) (11 : I32); rfl
  · apply kill_grading D h_gr (18 : I32) (12 : I32); rfl
  · apply kill_grading D h_gr (18 : I32) (13 : I32); rfl
  · apply kill_grading D h_gr (18 : I32) (14 : I32); rfl
  · apply kill_grading D h_gr (18 : I32) (15 : I32); rfl
  · apply kill_grading D h_gr (18 : I32) (16 : I32); rfl
  · apply kill_grading D h_gr (18 : I32) (17 : I32); rfl
  · apply kill_grading D h_gr (18 : I32) (18 : I32); rfl
  · apply kill_grading D h_gr (18 : I32) (19 : I32); rfl
  · apply kill_grading D h_gr (18 : I32) (20 : I32); rfl
  · apply kill_grading D h_gr (18 : I32) (21 : I32); rfl
  · apply kill_grading D h_gr (18 : I32) (22 : I32); rfl
  · apply kill_grading D h_gr (18 : I32) (23 : I32); rfl
  · apply kill_cf D hcf' (18 : I32) (24 : I32)
    intro hcon
    have h1 : cfIndicator ((18 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((24 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (18 : I32) (25 : I32)
    intro hcon
    have h1 : cfIndicator ((18 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((25 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (18 : I32) (28 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (18 : I32) (29 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (18 : I32) (30 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (18 : I32) (31 : I32) <;> decide
  · apply kill_cf D hcf' (19 : I32) (0 : I32)
    intro hcon
    have h1 : cfIndicator ((19 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((0 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (19 : I32) (1 : I32)
    intro hcon
    have h1 : cfIndicator ((19 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((1 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (19 : I32) (2 : I32)
    intro hcon
    have h1 : cfIndicator ((19 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((2 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (19 : I32) (3 : I32)
    intro hcon
    have h1 : cfIndicator ((19 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((3 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (19 : I32) (4 : I32)
    intro hcon
    have h1 : cfIndicator ((19 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((4 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (19 : I32) (5 : I32)
    intro hcon
    have h1 : cfIndicator ((19 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((5 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (19 : I32) (6 : I32)
    intro hcon
    have h1 : cfIndicator ((19 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((6 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (19 : I32) (7 : I32)
    intro hcon
    have h1 : cfIndicator ((19 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((7 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_grading D h_gr (19 : I32) (8 : I32); rfl
  · apply kill_grading D h_gr (19 : I32) (9 : I32); rfl
  · apply kill_grading D h_gr (19 : I32) (10 : I32); rfl
  · apply kill_grading D h_gr (19 : I32) (11 : I32); rfl
  · apply kill_grading D h_gr (19 : I32) (12 : I32); rfl
  · apply kill_grading D h_gr (19 : I32) (13 : I32); rfl
  · apply kill_grading D h_gr (19 : I32) (14 : I32); rfl
  · apply kill_grading D h_gr (19 : I32) (15 : I32); rfl
  · apply kill_grading D h_gr (19 : I32) (16 : I32); rfl
  · apply kill_grading D h_gr (19 : I32) (17 : I32); rfl
  · apply kill_grading D h_gr (19 : I32) (18 : I32); rfl
  · apply kill_grading D h_gr (19 : I32) (19 : I32); rfl
  · apply kill_grading D h_gr (19 : I32) (20 : I32); rfl
  · apply kill_grading D h_gr (19 : I32) (21 : I32); rfl
  · apply kill_grading D h_gr (19 : I32) (22 : I32); rfl
  · apply kill_grading D h_gr (19 : I32) (23 : I32); rfl
  · apply kill_cf D hcf' (19 : I32) (24 : I32)
    intro hcon
    have h1 : cfIndicator ((19 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((24 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (19 : I32) (25 : I32)
    intro hcon
    have h1 : cfIndicator ((19 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((25 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (19 : I32) (28 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (19 : I32) (29 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (19 : I32) (30 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (19 : I32) (31 : I32) <;> decide
  · apply kill_cf D hcf' (20 : I32) (0 : I32)
    intro hcon
    have h1 : cfIndicator ((20 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((0 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (20 : I32) (1 : I32)
    intro hcon
    have h1 : cfIndicator ((20 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((1 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (20 : I32) (2 : I32)
    intro hcon
    have h1 : cfIndicator ((20 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((2 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (20 : I32) (3 : I32)
    intro hcon
    have h1 : cfIndicator ((20 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((3 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (20 : I32) (4 : I32)
    intro hcon
    have h1 : cfIndicator ((20 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((4 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (20 : I32) (5 : I32)
    intro hcon
    have h1 : cfIndicator ((20 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((5 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (20 : I32) (6 : I32)
    intro hcon
    have h1 : cfIndicator ((20 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((6 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (20 : I32) (7 : I32)
    intro hcon
    have h1 : cfIndicator ((20 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((7 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_grading D h_gr (20 : I32) (8 : I32); rfl
  · apply kill_grading D h_gr (20 : I32) (9 : I32); rfl
  · apply kill_grading D h_gr (20 : I32) (10 : I32); rfl
  · apply kill_grading D h_gr (20 : I32) (11 : I32); rfl
  · apply kill_grading D h_gr (20 : I32) (12 : I32); rfl
  · apply kill_grading D h_gr (20 : I32) (13 : I32); rfl
  · apply kill_grading D h_gr (20 : I32) (14 : I32); rfl
  · apply kill_grading D h_gr (20 : I32) (15 : I32); rfl
  · apply kill_grading D h_gr (20 : I32) (16 : I32); rfl
  · apply kill_grading D h_gr (20 : I32) (17 : I32); rfl
  · apply kill_grading D h_gr (20 : I32) (18 : I32); rfl
  · apply kill_grading D h_gr (20 : I32) (19 : I32); rfl
  · apply kill_grading D h_gr (20 : I32) (20 : I32); rfl
  · apply kill_grading D h_gr (20 : I32) (21 : I32); rfl
  · apply kill_grading D h_gr (20 : I32) (22 : I32); rfl
  · apply kill_grading D h_gr (20 : I32) (23 : I32); rfl
  · apply kill_cf D hcf' (20 : I32) (24 : I32)
    intro hcon
    have h1 : cfIndicator ((20 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((24 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (20 : I32) (25 : I32)
    intro hcon
    have h1 : cfIndicator ((20 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((25 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (20 : I32) (26 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (20 : I32) (27 : I32) <;> decide
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (20 : I32) (30 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (20 : I32) (31 : I32) <;> decide
  · apply kill_cf D hcf' (21 : I32) (0 : I32)
    intro hcon
    have h1 : cfIndicator ((21 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((0 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (21 : I32) (1 : I32)
    intro hcon
    have h1 : cfIndicator ((21 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((1 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (21 : I32) (2 : I32)
    intro hcon
    have h1 : cfIndicator ((21 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((2 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (21 : I32) (3 : I32)
    intro hcon
    have h1 : cfIndicator ((21 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((3 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (21 : I32) (4 : I32)
    intro hcon
    have h1 : cfIndicator ((21 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((4 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (21 : I32) (5 : I32)
    intro hcon
    have h1 : cfIndicator ((21 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((5 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (21 : I32) (6 : I32)
    intro hcon
    have h1 : cfIndicator ((21 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((6 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (21 : I32) (7 : I32)
    intro hcon
    have h1 : cfIndicator ((21 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((7 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_grading D h_gr (21 : I32) (8 : I32); rfl
  · apply kill_grading D h_gr (21 : I32) (9 : I32); rfl
  · apply kill_grading D h_gr (21 : I32) (10 : I32); rfl
  · apply kill_grading D h_gr (21 : I32) (11 : I32); rfl
  · apply kill_grading D h_gr (21 : I32) (12 : I32); rfl
  · apply kill_grading D h_gr (21 : I32) (13 : I32); rfl
  · apply kill_grading D h_gr (21 : I32) (14 : I32); rfl
  · apply kill_grading D h_gr (21 : I32) (15 : I32); rfl
  · apply kill_grading D h_gr (21 : I32) (16 : I32); rfl
  · apply kill_grading D h_gr (21 : I32) (17 : I32); rfl
  · apply kill_grading D h_gr (21 : I32) (18 : I32); rfl
  · apply kill_grading D h_gr (21 : I32) (19 : I32); rfl
  · apply kill_grading D h_gr (21 : I32) (20 : I32); rfl
  · apply kill_grading D h_gr (21 : I32) (21 : I32); rfl
  · apply kill_grading D h_gr (21 : I32) (22 : I32); rfl
  · apply kill_grading D h_gr (21 : I32) (23 : I32); rfl
  · apply kill_cf D hcf' (21 : I32) (24 : I32)
    intro hcon
    have h1 : cfIndicator ((21 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((24 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (21 : I32) (25 : I32)
    intro hcon
    have h1 : cfIndicator ((21 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((25 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (21 : I32) (26 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (21 : I32) (27 : I32) <;> decide
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (21 : I32) (30 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (21 : I32) (31 : I32) <;> decide
  · apply kill_cf D hcf' (22 : I32) (0 : I32)
    intro hcon
    have h1 : cfIndicator ((22 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((0 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (22 : I32) (1 : I32)
    intro hcon
    have h1 : cfIndicator ((22 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((1 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (22 : I32) (2 : I32)
    intro hcon
    have h1 : cfIndicator ((22 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((2 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (22 : I32) (3 : I32)
    intro hcon
    have h1 : cfIndicator ((22 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((3 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (22 : I32) (4 : I32)
    intro hcon
    have h1 : cfIndicator ((22 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((4 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (22 : I32) (5 : I32)
    intro hcon
    have h1 : cfIndicator ((22 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((5 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (22 : I32) (6 : I32)
    intro hcon
    have h1 : cfIndicator ((22 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((6 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (22 : I32) (7 : I32)
    intro hcon
    have h1 : cfIndicator ((22 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((7 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_grading D h_gr (22 : I32) (8 : I32); rfl
  · apply kill_grading D h_gr (22 : I32) (9 : I32); rfl
  · apply kill_grading D h_gr (22 : I32) (10 : I32); rfl
  · apply kill_grading D h_gr (22 : I32) (11 : I32); rfl
  · apply kill_grading D h_gr (22 : I32) (12 : I32); rfl
  · apply kill_grading D h_gr (22 : I32) (13 : I32); rfl
  · apply kill_grading D h_gr (22 : I32) (14 : I32); rfl
  · apply kill_grading D h_gr (22 : I32) (15 : I32); rfl
  · apply kill_grading D h_gr (22 : I32) (16 : I32); rfl
  · apply kill_grading D h_gr (22 : I32) (17 : I32); rfl
  · apply kill_grading D h_gr (22 : I32) (18 : I32); rfl
  · apply kill_grading D h_gr (22 : I32) (19 : I32); rfl
  · apply kill_grading D h_gr (22 : I32) (20 : I32); rfl
  · apply kill_grading D h_gr (22 : I32) (21 : I32); rfl
  · apply kill_grading D h_gr (22 : I32) (22 : I32); rfl
  · apply kill_grading D h_gr (22 : I32) (23 : I32); rfl
  · apply kill_cf D hcf' (22 : I32) (24 : I32)
    intro hcon
    have h1 : cfIndicator ((22 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((24 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (22 : I32) (25 : I32)
    intro hcon
    have h1 : cfIndicator ((22 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((25 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (22 : I32) (26 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (22 : I32) (27 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (22 : I32) (28 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (22 : I32) (29 : I32) <;> decide
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply kill_cf D hcf' (23 : I32) (0 : I32)
    intro hcon
    have h1 : cfIndicator ((23 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((0 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (23 : I32) (1 : I32)
    intro hcon
    have h1 : cfIndicator ((23 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((1 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (23 : I32) (2 : I32)
    intro hcon
    have h1 : cfIndicator ((23 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((2 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (23 : I32) (3 : I32)
    intro hcon
    have h1 : cfIndicator ((23 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((3 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (23 : I32) (4 : I32)
    intro hcon
    have h1 : cfIndicator ((23 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((4 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (23 : I32) (5 : I32)
    intro hcon
    have h1 : cfIndicator ((23 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((5 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (23 : I32) (6 : I32)
    intro hcon
    have h1 : cfIndicator ((23 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((6 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (23 : I32) (7 : I32)
    intro hcon
    have h1 : cfIndicator ((23 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((7 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_grading D h_gr (23 : I32) (8 : I32); rfl
  · apply kill_grading D h_gr (23 : I32) (9 : I32); rfl
  · apply kill_grading D h_gr (23 : I32) (10 : I32); rfl
  · apply kill_grading D h_gr (23 : I32) (11 : I32); rfl
  · apply kill_grading D h_gr (23 : I32) (12 : I32); rfl
  · apply kill_grading D h_gr (23 : I32) (13 : I32); rfl
  · apply kill_grading D h_gr (23 : I32) (14 : I32); rfl
  · apply kill_grading D h_gr (23 : I32) (15 : I32); rfl
  · apply kill_grading D h_gr (23 : I32) (16 : I32); rfl
  · apply kill_grading D h_gr (23 : I32) (17 : I32); rfl
  · apply kill_grading D h_gr (23 : I32) (18 : I32); rfl
  · apply kill_grading D h_gr (23 : I32) (19 : I32); rfl
  · apply kill_grading D h_gr (23 : I32) (20 : I32); rfl
  · apply kill_grading D h_gr (23 : I32) (21 : I32); rfl
  · apply kill_grading D h_gr (23 : I32) (22 : I32); rfl
  · apply kill_grading D h_gr (23 : I32) (23 : I32); rfl
  · apply kill_cf D hcf' (23 : I32) (24 : I32)
    intro hcon
    have h1 : cfIndicator ((23 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((24 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (23 : I32) (25 : I32)
    intro hcon
    have h1 : cfIndicator ((23 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((25 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (23 : I32) (26 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (23 : I32) (27 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (23 : I32) (28 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (23 : I32) (29 : I32) <;> decide
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply kill_grading D h_gr (24 : I32) (0 : I32); rfl
  · apply kill_grading D h_gr (24 : I32) (1 : I32); rfl
  · apply kill_grading D h_gr (24 : I32) (2 : I32); rfl
  · apply kill_grading D h_gr (24 : I32) (3 : I32); rfl
  · apply kill_grading D h_gr (24 : I32) (4 : I32); rfl
  · apply kill_grading D h_gr (24 : I32) (5 : I32); rfl
  · apply kill_grading D h_gr (24 : I32) (6 : I32); rfl
  · apply kill_grading D h_gr (24 : I32) (7 : I32); rfl
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply kill_j_transport D h_J (24 : I32) (10 : I32)
    have hp1 : partner ((10 : I32) : I32) = ((26 : I32) : I32) := by decide
    have hp2 : partner ((24 : I32) : I32) = ((8 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (26 : I32) (8 : I32)
    intro hcon
    have h1 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_j_transport D h_J (24 : I32) (11 : I32)
    have hp1 : partner ((11 : I32) : I32) = ((27 : I32) : I32) := by decide
    have hp2 : partner ((24 : I32) : I32) = ((8 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (27 : I32) (8 : I32)
    intro hcon
    have h1 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_j_transport D h_J (24 : I32) (12 : I32)
    have hp1 : partner ((12 : I32) : I32) = ((28 : I32) : I32) := by decide
    have hp2 : partner ((24 : I32) : I32) = ((8 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (28 : I32) (8 : I32)
    intro hcon
    have h1 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_j_transport D h_J (24 : I32) (13 : I32)
    have hp1 : partner ((13 : I32) : I32) = ((29 : I32) : I32) := by decide
    have hp2 : partner ((24 : I32) : I32) = ((8 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (29 : I32) (8 : I32)
    intro hcon
    have h1 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_j_transport D h_J (24 : I32) (14 : I32)
    have hp1 : partner ((14 : I32) : I32) = ((30 : I32) : I32) := by decide
    have hp2 : partner ((24 : I32) : I32) = ((8 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (30 : I32) (8 : I32)
    intro hcon
    have h1 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_j_transport D h_J (24 : I32) (15 : I32)
    have hp1 : partner ((15 : I32) : I32) = ((31 : I32) : I32) := by decide
    have hp2 : partner ((24 : I32) : I32) = ((8 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (31 : I32) (8 : I32)
    intro hcon
    have h1 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply kill_cf D hcf' (24 : I32) (18 : I32)
    intro hcon
    have h1 : cfIndicator ((24 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((18 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (24 : I32) (19 : I32)
    intro hcon
    have h1 : cfIndicator ((24 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((19 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (24 : I32) (20 : I32)
    intro hcon
    have h1 : cfIndicator ((24 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((20 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (24 : I32) (21 : I32)
    intro hcon
    have h1 : cfIndicator ((24 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((21 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (24 : I32) (22 : I32)
    intro hcon
    have h1 : cfIndicator ((24 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((22 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (24 : I32) (23 : I32)
    intro hcon
    have h1 : cfIndicator ((24 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((23 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_grading D h_gr (24 : I32) (24 : I32); rfl
  · apply kill_grading D h_gr (24 : I32) (25 : I32); rfl
  · apply kill_grading D h_gr (24 : I32) (26 : I32); rfl
  · apply kill_grading D h_gr (24 : I32) (27 : I32); rfl
  · apply kill_grading D h_gr (24 : I32) (28 : I32); rfl
  · apply kill_grading D h_gr (24 : I32) (29 : I32); rfl
  · apply kill_grading D h_gr (24 : I32) (30 : I32); rfl
  · apply kill_grading D h_gr (24 : I32) (31 : I32); rfl
  · apply kill_grading D h_gr (25 : I32) (0 : I32); rfl
  · apply kill_grading D h_gr (25 : I32) (1 : I32); rfl
  · apply kill_grading D h_gr (25 : I32) (2 : I32); rfl
  · apply kill_grading D h_gr (25 : I32) (3 : I32); rfl
  · apply kill_grading D h_gr (25 : I32) (4 : I32); rfl
  · apply kill_grading D h_gr (25 : I32) (5 : I32); rfl
  · apply kill_grading D h_gr (25 : I32) (6 : I32); rfl
  · apply kill_grading D h_gr (25 : I32) (7 : I32); rfl
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply kill_j_transport D h_J (25 : I32) (10 : I32)
    have hp1 : partner ((10 : I32) : I32) = ((26 : I32) : I32) := by decide
    have hp2 : partner ((25 : I32) : I32) = ((9 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (26 : I32) (9 : I32)
    intro hcon
    have h1 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_j_transport D h_J (25 : I32) (11 : I32)
    have hp1 : partner ((11 : I32) : I32) = ((27 : I32) : I32) := by decide
    have hp2 : partner ((25 : I32) : I32) = ((9 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (27 : I32) (9 : I32)
    intro hcon
    have h1 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_j_transport D h_J (25 : I32) (12 : I32)
    have hp1 : partner ((12 : I32) : I32) = ((28 : I32) : I32) := by decide
    have hp2 : partner ((25 : I32) : I32) = ((9 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (28 : I32) (9 : I32)
    intro hcon
    have h1 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_j_transport D h_J (25 : I32) (13 : I32)
    have hp1 : partner ((13 : I32) : I32) = ((29 : I32) : I32) := by decide
    have hp2 : partner ((25 : I32) : I32) = ((9 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (29 : I32) (9 : I32)
    intro hcon
    have h1 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_j_transport D h_J (25 : I32) (14 : I32)
    have hp1 : partner ((14 : I32) : I32) = ((30 : I32) : I32) := by decide
    have hp2 : partner ((25 : I32) : I32) = ((9 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (30 : I32) (9 : I32)
    intro hcon
    have h1 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_j_transport D h_J (25 : I32) (15 : I32)
    have hp1 : partner ((15 : I32) : I32) = ((31 : I32) : I32) := by decide
    have hp2 : partner ((25 : I32) : I32) = ((9 : I32) : I32) := by decide
    rw [hp1, hp2]
    apply kill_cf D hcf' (31 : I32) (9 : I32)
    intro hcon
    have h1 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply kill_cf D hcf' (25 : I32) (18 : I32)
    intro hcon
    have h1 : cfIndicator ((25 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((18 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (25 : I32) (19 : I32)
    intro hcon
    have h1 : cfIndicator ((25 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((19 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (25 : I32) (20 : I32)
    intro hcon
    have h1 : cfIndicator ((25 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((20 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (25 : I32) (21 : I32)
    intro hcon
    have h1 : cfIndicator ((25 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((21 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (25 : I32) (22 : I32)
    intro hcon
    have h1 : cfIndicator ((25 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((22 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_cf D hcf' (25 : I32) (23 : I32)
    intro hcon
    have h1 : cfIndicator ((25 : I32) : I32) = (1 : ℂ) := rfl
    have h2 : cfIndicator ((23 : I32) : I32) = (0 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact one_ne_zero hcon
  · apply kill_grading D h_gr (25 : I32) (24 : I32); rfl
  · apply kill_grading D h_gr (25 : I32) (25 : I32); rfl
  · apply kill_grading D h_gr (25 : I32) (26 : I32); rfl
  · apply kill_grading D h_gr (25 : I32) (27 : I32); rfl
  · apply kill_grading D h_gr (25 : I32) (28 : I32); rfl
  · apply kill_grading D h_gr (25 : I32) (29 : I32); rfl
  · apply kill_grading D h_gr (25 : I32) (30 : I32); rfl
  · apply kill_grading D h_gr (25 : I32) (31 : I32); rfl
  · apply kill_grading D h_gr (26 : I32) (0 : I32); rfl
  · apply kill_grading D h_gr (26 : I32) (1 : I32); rfl
  · apply kill_grading D h_gr (26 : I32) (2 : I32); rfl
  · apply kill_grading D h_gr (26 : I32) (3 : I32); rfl
  · apply kill_grading D h_gr (26 : I32) (4 : I32); rfl
  · apply kill_grading D h_gr (26 : I32) (5 : I32); rfl
  · apply kill_grading D h_gr (26 : I32) (6 : I32); rfl
  · apply kill_grading D h_gr (26 : I32) (7 : I32); rfl
  · apply kill_cf D hcf' (26 : I32) (8 : I32)
    intro hcon
    have h1 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (26 : I32) (9 : I32)
    intro hcon
    have h1 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (26 : I32) (10 : I32)
    intro hcon
    have h1 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((10 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (26 : I32) (11 : I32)
    intro hcon
    have h1 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((11 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (26 : I32) (12 : I32)
    intro hcon
    have h1 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((12 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (26 : I32) (13 : I32)
    intro hcon
    have h1 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((13 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (26 : I32) (14 : I32)
    intro hcon
    have h1 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((14 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (26 : I32) (15 : I32)
    intro hcon
    have h1 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((15 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (26 : I32) (16 : I32)
    intro hcon
    have h1 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((16 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (26 : I32) (17 : I32)
    intro hcon
    have h1 : cfIndicator ((26 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((17 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (26 : I32) (20 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (26 : I32) (21 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (26 : I32) (22 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (26 : I32) (23 : I32) <;> decide
  · apply kill_grading D h_gr (26 : I32) (24 : I32); rfl
  · apply kill_grading D h_gr (26 : I32) (25 : I32); rfl
  · apply kill_grading D h_gr (26 : I32) (26 : I32); rfl
  · apply kill_grading D h_gr (26 : I32) (27 : I32); rfl
  · apply kill_grading D h_gr (26 : I32) (28 : I32); rfl
  · apply kill_grading D h_gr (26 : I32) (29 : I32); rfl
  · apply kill_grading D h_gr (26 : I32) (30 : I32); rfl
  · apply kill_grading D h_gr (26 : I32) (31 : I32); rfl
  · apply kill_grading D h_gr (27 : I32) (0 : I32); rfl
  · apply kill_grading D h_gr (27 : I32) (1 : I32); rfl
  · apply kill_grading D h_gr (27 : I32) (2 : I32); rfl
  · apply kill_grading D h_gr (27 : I32) (3 : I32); rfl
  · apply kill_grading D h_gr (27 : I32) (4 : I32); rfl
  · apply kill_grading D h_gr (27 : I32) (5 : I32); rfl
  · apply kill_grading D h_gr (27 : I32) (6 : I32); rfl
  · apply kill_grading D h_gr (27 : I32) (7 : I32); rfl
  · apply kill_cf D hcf' (27 : I32) (8 : I32)
    intro hcon
    have h1 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (27 : I32) (9 : I32)
    intro hcon
    have h1 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (27 : I32) (10 : I32)
    intro hcon
    have h1 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((10 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (27 : I32) (11 : I32)
    intro hcon
    have h1 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((11 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (27 : I32) (12 : I32)
    intro hcon
    have h1 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((12 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (27 : I32) (13 : I32)
    intro hcon
    have h1 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((13 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (27 : I32) (14 : I32)
    intro hcon
    have h1 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((14 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (27 : I32) (15 : I32)
    intro hcon
    have h1 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((15 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (27 : I32) (16 : I32)
    intro hcon
    have h1 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((16 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (27 : I32) (17 : I32)
    intro hcon
    have h1 : cfIndicator ((27 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((17 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (27 : I32) (20 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (27 : I32) (21 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (27 : I32) (22 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (27 : I32) (23 : I32) <;> decide
  · apply kill_grading D h_gr (27 : I32) (24 : I32); rfl
  · apply kill_grading D h_gr (27 : I32) (25 : I32); rfl
  · apply kill_grading D h_gr (27 : I32) (26 : I32); rfl
  · apply kill_grading D h_gr (27 : I32) (27 : I32); rfl
  · apply kill_grading D h_gr (27 : I32) (28 : I32); rfl
  · apply kill_grading D h_gr (27 : I32) (29 : I32); rfl
  · apply kill_grading D h_gr (27 : I32) (30 : I32); rfl
  · apply kill_grading D h_gr (27 : I32) (31 : I32); rfl
  · apply kill_grading D h_gr (28 : I32) (0 : I32); rfl
  · apply kill_grading D h_gr (28 : I32) (1 : I32); rfl
  · apply kill_grading D h_gr (28 : I32) (2 : I32); rfl
  · apply kill_grading D h_gr (28 : I32) (3 : I32); rfl
  · apply kill_grading D h_gr (28 : I32) (4 : I32); rfl
  · apply kill_grading D h_gr (28 : I32) (5 : I32); rfl
  · apply kill_grading D h_gr (28 : I32) (6 : I32); rfl
  · apply kill_grading D h_gr (28 : I32) (7 : I32); rfl
  · apply kill_cf D hcf' (28 : I32) (8 : I32)
    intro hcon
    have h1 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (28 : I32) (9 : I32)
    intro hcon
    have h1 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (28 : I32) (10 : I32)
    intro hcon
    have h1 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((10 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (28 : I32) (11 : I32)
    intro hcon
    have h1 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((11 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (28 : I32) (12 : I32)
    intro hcon
    have h1 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((12 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (28 : I32) (13 : I32)
    intro hcon
    have h1 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((13 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (28 : I32) (14 : I32)
    intro hcon
    have h1 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((14 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (28 : I32) (15 : I32)
    intro hcon
    have h1 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((15 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (28 : I32) (16 : I32)
    intro hcon
    have h1 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((16 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (28 : I32) (17 : I32)
    intro hcon
    have h1 : cfIndicator ((28 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((17 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (28 : I32) (18 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (28 : I32) (19 : I32) <;> decide
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (28 : I32) (22 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (28 : I32) (23 : I32) <;> decide
  · apply kill_grading D h_gr (28 : I32) (24 : I32); rfl
  · apply kill_grading D h_gr (28 : I32) (25 : I32); rfl
  · apply kill_grading D h_gr (28 : I32) (26 : I32); rfl
  · apply kill_grading D h_gr (28 : I32) (27 : I32); rfl
  · apply kill_grading D h_gr (28 : I32) (28 : I32); rfl
  · apply kill_grading D h_gr (28 : I32) (29 : I32); rfl
  · apply kill_grading D h_gr (28 : I32) (30 : I32); rfl
  · apply kill_grading D h_gr (28 : I32) (31 : I32); rfl
  · apply kill_grading D h_gr (29 : I32) (0 : I32); rfl
  · apply kill_grading D h_gr (29 : I32) (1 : I32); rfl
  · apply kill_grading D h_gr (29 : I32) (2 : I32); rfl
  · apply kill_grading D h_gr (29 : I32) (3 : I32); rfl
  · apply kill_grading D h_gr (29 : I32) (4 : I32); rfl
  · apply kill_grading D h_gr (29 : I32) (5 : I32); rfl
  · apply kill_grading D h_gr (29 : I32) (6 : I32); rfl
  · apply kill_grading D h_gr (29 : I32) (7 : I32); rfl
  · apply kill_cf D hcf' (29 : I32) (8 : I32)
    intro hcon
    have h1 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (29 : I32) (9 : I32)
    intro hcon
    have h1 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (29 : I32) (10 : I32)
    intro hcon
    have h1 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((10 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (29 : I32) (11 : I32)
    intro hcon
    have h1 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((11 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (29 : I32) (12 : I32)
    intro hcon
    have h1 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((12 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (29 : I32) (13 : I32)
    intro hcon
    have h1 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((13 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (29 : I32) (14 : I32)
    intro hcon
    have h1 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((14 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (29 : I32) (15 : I32)
    intro hcon
    have h1 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((15 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (29 : I32) (16 : I32)
    intro hcon
    have h1 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((16 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (29 : I32) (17 : I32)
    intro hcon
    have h1 : cfIndicator ((29 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((17 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (29 : I32) (18 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (29 : I32) (19 : I32) <;> decide
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (29 : I32) (22 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (29 : I32) (23 : I32) <;> decide
  · apply kill_grading D h_gr (29 : I32) (24 : I32); rfl
  · apply kill_grading D h_gr (29 : I32) (25 : I32); rfl
  · apply kill_grading D h_gr (29 : I32) (26 : I32); rfl
  · apply kill_grading D h_gr (29 : I32) (27 : I32); rfl
  · apply kill_grading D h_gr (29 : I32) (28 : I32); rfl
  · apply kill_grading D h_gr (29 : I32) (29 : I32); rfl
  · apply kill_grading D h_gr (29 : I32) (30 : I32); rfl
  · apply kill_grading D h_gr (29 : I32) (31 : I32); rfl
  · apply kill_grading D h_gr (30 : I32) (0 : I32); rfl
  · apply kill_grading D h_gr (30 : I32) (1 : I32); rfl
  · apply kill_grading D h_gr (30 : I32) (2 : I32); rfl
  · apply kill_grading D h_gr (30 : I32) (3 : I32); rfl
  · apply kill_grading D h_gr (30 : I32) (4 : I32); rfl
  · apply kill_grading D h_gr (30 : I32) (5 : I32); rfl
  · apply kill_grading D h_gr (30 : I32) (6 : I32); rfl
  · apply kill_grading D h_gr (30 : I32) (7 : I32); rfl
  · apply kill_cf D hcf' (30 : I32) (8 : I32)
    intro hcon
    have h1 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (30 : I32) (9 : I32)
    intro hcon
    have h1 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (30 : I32) (10 : I32)
    intro hcon
    have h1 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((10 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (30 : I32) (11 : I32)
    intro hcon
    have h1 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((11 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (30 : I32) (12 : I32)
    intro hcon
    have h1 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((12 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (30 : I32) (13 : I32)
    intro hcon
    have h1 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((13 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (30 : I32) (14 : I32)
    intro hcon
    have h1 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((14 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (30 : I32) (15 : I32)
    intro hcon
    have h1 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((15 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (30 : I32) (16 : I32)
    intro hcon
    have h1 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((16 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (30 : I32) (17 : I32)
    intro hcon
    have h1 : cfIndicator ((30 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((17 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (30 : I32) (18 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (30 : I32) (19 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (30 : I32) (20 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (30 : I32) (21 : I32) <;> decide
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply kill_grading D h_gr (30 : I32) (24 : I32); rfl
  · apply kill_grading D h_gr (30 : I32) (25 : I32); rfl
  · apply kill_grading D h_gr (30 : I32) (26 : I32); rfl
  · apply kill_grading D h_gr (30 : I32) (27 : I32); rfl
  · apply kill_grading D h_gr (30 : I32) (28 : I32); rfl
  · apply kill_grading D h_gr (30 : I32) (29 : I32); rfl
  · apply kill_grading D h_gr (30 : I32) (30 : I32); rfl
  · apply kill_grading D h_gr (30 : I32) (31 : I32); rfl
  · apply kill_grading D h_gr (31 : I32) (0 : I32); rfl
  · apply kill_grading D h_gr (31 : I32) (1 : I32); rfl
  · apply kill_grading D h_gr (31 : I32) (2 : I32); rfl
  · apply kill_grading D h_gr (31 : I32) (3 : I32); rfl
  · apply kill_grading D h_gr (31 : I32) (4 : I32); rfl
  · apply kill_grading D h_gr (31 : I32) (5 : I32); rfl
  · apply kill_grading D h_gr (31 : I32) (6 : I32); rfl
  · apply kill_grading D h_gr (31 : I32) (7 : I32); rfl
  · apply kill_cf D hcf' (31 : I32) (8 : I32)
    intro hcon
    have h1 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((8 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (31 : I32) (9 : I32)
    intro hcon
    have h1 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((9 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (31 : I32) (10 : I32)
    intro hcon
    have h1 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((10 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (31 : I32) (11 : I32)
    intro hcon
    have h1 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((11 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (31 : I32) (12 : I32)
    intro hcon
    have h1 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((12 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (31 : I32) (13 : I32)
    intro hcon
    have h1 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((13 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (31 : I32) (14 : I32)
    intro hcon
    have h1 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((14 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (31 : I32) (15 : I32)
    intro hcon
    have h1 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((15 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (31 : I32) (16 : I32)
    intro hcon
    have h1 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((16 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply kill_cf D hcf' (31 : I32) (17 : I32)
    intro hcon
    have h1 : cfIndicator ((31 : I32) : I32) = (0 : ℂ) := rfl
    have h2 : cfIndicator ((17 : I32) : I32) = (1 : ℂ) := rfl
    rw [h1, h2] at hcon
    exact zero_ne_one hcon
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (31 : I32) (18 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (31 : I32) (19 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (31 : I32) (20 : I32) <;> decide
  · apply diagonal_pair_kill D h_oo (2 : Fin 4) (0 : Fin 4) (31 : I32) (21 : I32) <;> decide
  · exfalso; apply h_off; decide
  · exfalso; apply h_off; decide
  · apply kill_grading D h_gr (31 : I32) (24 : I32); rfl
  · apply kill_grading D h_gr (31 : I32) (25 : I32); rfl
  · apply kill_grading D h_gr (31 : I32) (26 : I32); rfl
  · apply kill_grading D h_gr (31 : I32) (27 : I32); rfl
  · apply kill_grading D h_gr (31 : I32) (28 : I32); rfl
  · apply kill_grading D h_gr (31 : I32) (29 : I32); rfl
  · apply kill_grading D h_gr (31 : I32) (30 : I32); rfl
  · apply kill_grading D h_gr (31 : I32) (31 : I32); rfl

/-! ## §T4b½. Color-universality identifications -
Moved here from `CFKernel22Dim.lean` (2026-09-30): the 8
`ident_yU_*` theorems must live in this module because §T4c
below uses them, and `CFKernel22Dim` imports `CFKernel22` which
imports this module (an import here would be a cycle). -/

/-!
# T4 Closure: Dimension bound for the order-one kernel

This module proves `Module.finrank ℝ W22 ≤ 22` by establishing the 8 color-universality
identifications and the support lemmas, discharging the `h_census` hypothesis.
-/


open Matrix

/-- The double commutator vanishes entrywise from `OrderOneHolds`. -/
theorem dcomm_entry_zero (D : Matrix I32 I32 ℂ) (h_oo : OrderOneHolds D)
    (g1 g2 : Fin 12) (i j : I32) :
    ((D * smGen g1 - smGen g1 * D) * smGenOp g2
      - smGenOp g2 * (D * smGen g1 - smGen g1 * D)) i j = 0 := by
  have h := h_oo g1 g2
  have he := congrArg (fun M : Matrix I32 I32 ℂ => M i j) h
  simpa using he

/-! ### Sparsity lemmas for smGenOp 4 and smGen 1 -/

/-- `smGenOp 4` column 12: only row 10 is nonzero (value 1). -/
theorem smGenOp4_col12 (p : I32) :
    smGenOp 4 p ⟨12, by norm_num⟩ = if p = ⟨10, by norm_num⟩ then 1 else 0 := by
  rw [smGenOp_apply]
  have h4 : smGen (4 : Fin 12) = genM 0 := rfl
  rw [h4]
  have hp12 : partner ⟨12, by norm_num⟩ = ⟨28, by norm_num⟩ := by
    rw [Fin.ext_iff, partner_val_eq]
    norm_num
  rw [hp12]
  fin_cases p <;>
    simp only [partner, genM, tripletOf, gellMann, Fin.mk.injEq] <;>
    norm_num

/-- `smGenOp 4` row 3: only column 5 is nonzero (value 1). -/
theorem smGenOp4_row3 (p : I32) :
    smGenOp 4 ⟨3, by norm_num⟩ p = if p = ⟨5, by norm_num⟩ then 1 else 0 := by
  rw [smGenOp_apply]
  have h4 : smGen (4 : Fin 12) = genM 0 := rfl
  rw [h4]
  have hp3 : partner ⟨3, by norm_num⟩ = ⟨19, by norm_num⟩ := by
    rw [Fin.ext_iff, partner_val_eq]
    norm_num
  rw [hp3]
  fin_cases p <;>
    simp only [partner, genM, tripletOf, gellMann, Fin.mk.injEq] <;>
    norm_num

/-- `smGen 1` column 10: all zeros. -/
theorem smGen1_col10 (q : I32) : smGen 1 q ⟨10, by norm_num⟩ = 0 := by
  have h1 : smGen (1 : Fin 12) = genH 0 := rfl
  rw [h1]
  by_cases hq : genH 0 q ⟨10, by norm_num⟩ ≠ 0
  · have hsupp := genH_supp 0 q ⟨10, by norm_num⟩ hq
    norm_num at hsupp
  · exact not_not.mp hq

/-- `smGen 1` row 3: only column 2 is nonzero (value 1). -/
theorem smGen1_row3 (q : I32) :
    smGen 1 ⟨3, by norm_num⟩ q = if q = ⟨2, by norm_num⟩ then 1 else 0 := by
  have h1 : smGen (1 : Fin 12) = genH 0 := rfl
  rw [h1]
  fin_cases q <;>
    simp only [genH, pauli, Fin.mk.injEq] <;>
    norm_num

/-- `smGen 1` column 12: all zeros. -/
theorem smGen1_col12 (q : I32) : smGen 1 q ⟨12, by norm_num⟩ = 0 := by
  have h1 : smGen (1 : Fin 12) = genH 0 := rfl
  rw [h1]
  by_cases hq : genH 0 q ⟨12, by norm_num⟩ ≠ 0
  · have hsupp := genH_supp 0 q ⟨12, by norm_num⟩ hq
    norm_num at hsupp
  · exact not_not.mp hq

/-- `smGen 1` row 5: only column 4 is nonzero (value 1). -/
theorem smGen1_row5 (q : I32) :
    smGen 1 ⟨5, by norm_num⟩ q = if q = ⟨4, by norm_num⟩ then 1 else 0 := by
  have h1 : smGen (1 : Fin 12) = genH 0 := rfl
  rw [h1]
  fin_cases q <;>
    simp only [genH, pauli, Fin.mk.injEq] <;>
    norm_num

/-- `smGenOp 4` column 13: only row 11 is nonzero (value 1). -/
theorem smGenOp4_col13 (p : I32) :
    smGenOp 4 p ⟨13, by norm_num⟩ = if p = ⟨11, by norm_num⟩ then 1 else 0 := by
  rw [smGenOp_apply]
  have h4 : smGen (4 : Fin 12) = genM 0 := rfl
  rw [h4]
  have hp13 : partner ⟨13, by norm_num⟩ = ⟨29, by norm_num⟩ := by
    rw [Fin.ext_iff, partner_val_eq]
    norm_num
  rw [hp13]
  fin_cases p <;>
    simp only [partner, genM, tripletOf, gellMann, Fin.mk.injEq] <;>
    norm_num

/-- `smGenOp 4` row 2: only column 4 is nonzero (value 1). -/
theorem smGenOp4_row2 (p : I32) :
    smGenOp 4 ⟨2, by norm_num⟩ p = if p = ⟨4, by norm_num⟩ then 1 else 0 := by
  rw [smGenOp_apply]
  have h4 : smGen (4 : Fin 12) = genM 0 := rfl
  rw [h4]
  have hp2 : partner ⟨2, by norm_num⟩ = ⟨18, by norm_num⟩ := by
    rw [Fin.ext_iff, partner_val_eq]
    norm_num
  rw [hp2]
  fin_cases p <;>
    simp only [partner, genM, tripletOf, gellMann, Fin.mk.injEq] <;>
    norm_num

/-- `smGenOp 7` column 14: only row 10 is nonzero (value 1). -/
theorem smGenOp7_col14 (p : I32) :
    smGenOp 7 p ⟨14, by norm_num⟩ = if p = ⟨10, by norm_num⟩ then 1 else 0 := by
  rw [smGenOp_apply]
  have h7 : smGen (7 : Fin 12) = genM 3 := rfl
  rw [h7]
  have hp14 : partner ⟨14, by norm_num⟩ = ⟨30, by norm_num⟩ := by
    rw [Fin.ext_iff, partner_val_eq]
    norm_num
  rw [hp14]
  fin_cases p <;>
    simp only [partner, genM, tripletOf, gellMann, Fin.mk.injEq] <;>
    norm_num

/-- `smGenOp 7` column 15: only row 11 is nonzero (value 1). -/
theorem smGenOp7_col15 (p : I32) :
    smGenOp 7 p ⟨15, by norm_num⟩ = if p = ⟨11, by norm_num⟩ then 1 else 0 := by
  rw [smGenOp_apply]
  have h7 : smGen (7 : Fin 12) = genM 3 := rfl
  rw [h7]
  have hp15 : partner ⟨15, by norm_num⟩ = ⟨31, by norm_num⟩ := by
    rw [Fin.ext_iff, partner_val_eq]
    norm_num
  rw [hp15]
  fin_cases p <;>
    simp only [partner, genM, tripletOf, gellMann, Fin.mk.injEq] <;>
    norm_num

/-- `smGenOp 7` row 2: only column 6 is nonzero (value 1). -/
theorem smGenOp7_row2 (p : I32) :
    smGenOp 7 ⟨2, by norm_num⟩ p = if p = ⟨6, by norm_num⟩ then 1 else 0 := by
  rw [smGenOp_apply]
  have h7 : smGen (7 : Fin 12) = genM 3 := rfl
  rw [h7]
  have hp2 : partner ⟨2, by norm_num⟩ = ⟨18, by norm_num⟩ := by
    rw [Fin.ext_iff, partner_val_eq]
    norm_num
  rw [hp2]
  fin_cases p <;>
    simp only [partner, genM, tripletOf, gellMann, Fin.mk.injEq] <;>
    norm_num

/-- `smGenOp 7` row 3: only column 7 is nonzero (value 1). -/
theorem smGenOp7_row3 (p : I32) :
    smGenOp 7 ⟨3, by norm_num⟩ p = if p = ⟨7, by norm_num⟩ then 1 else 0 := by
  rw [smGenOp_apply]
  have h7 : smGen (7 : Fin 12) = genM 3 := rfl
  rw [h7]
  have hp3 : partner ⟨3, by norm_num⟩ = ⟨19, by norm_num⟩ := by
    rw [Fin.ext_iff, partner_val_eq]
    norm_num
  rw [hp3]
  fin_cases p <;>
    simp only [partner, genM, tripletOf, gellMann, Fin.mk.injEq] <;>
    norm_num

/-- `smGen 1` column 11: all zeros. -/
theorem smGen1_col11 (q : I32) : smGen 1 q ⟨11, by norm_num⟩ = 0 := by
  have h1 : smGen (1 : Fin 12) = genH 0 := rfl
  rw [h1]
  by_cases hq : genH 0 q ⟨11, by norm_num⟩ ≠ 0
  · have hsupp := genH_supp 0 q ⟨11, by norm_num⟩ hq
    norm_num at hsupp
  · exact not_not.mp hq

/-- `smGen 1` column 13: all zeros. -/
theorem smGen1_col13 (q : I32) : smGen 1 q ⟨13, by norm_num⟩ = 0 := by
  have h1 : smGen (1 : Fin 12) = genH 0 := rfl
  rw [h1]
  by_cases hq : genH 0 q ⟨13, by norm_num⟩ ≠ 0
  · have hsupp := genH_supp 0 q ⟨13, by norm_num⟩ hq
    norm_num at hsupp
  · exact not_not.mp hq

/-- `smGen 1` column 14: all zeros. -/
theorem smGen1_col14 (q : I32) : smGen 1 q ⟨14, by norm_num⟩ = 0 := by
  have h1 : smGen (1 : Fin 12) = genH 0 := rfl
  rw [h1]
  by_cases hq : genH 0 q ⟨14, by norm_num⟩ ≠ 0
  · have hsupp := genH_supp 0 q ⟨14, by norm_num⟩ hq
    norm_num at hsupp
  · exact not_not.mp hq

/-- `smGen 1` column 15: all zeros. -/
theorem smGen1_col15 (q : I32) : smGen 1 q ⟨15, by norm_num⟩ = 0 := by
  have h1 : smGen (1 : Fin 12) = genH 0 := rfl
  rw [h1]
  by_cases hq : genH 0 q ⟨15, by norm_num⟩ ≠ 0
  · have hsupp := genH_supp 0 q ⟨15, by norm_num⟩ hq
    norm_num at hsupp
  · exact not_not.mp hq

/-- `smGen 1` row 2: only column 3 is nonzero (value 1). -/
theorem smGen1_row2 (q : I32) :
    smGen 1 ⟨2, by norm_num⟩ q = if q = ⟨3, by norm_num⟩ then 1 else 0 := by
  have h1 : smGen (1 : Fin 12) = genH 0 := rfl
  rw [h1]
  fin_cases q <;>
    simp only [genH, pauli, Fin.mk.injEq] <;>
    norm_num

/-- `smGen 1` row 4: only column 5 is nonzero (value 1). -/
theorem smGen1_row4 (q : I32) :
    smGen 1 ⟨4, by norm_num⟩ q = if q = ⟨5, by norm_num⟩ then 1 else 0 := by
  have h1 : smGen (1 : Fin 12) = genH 0 := rfl
  rw [h1]
  fin_cases q <;>
    simp only [genH, pauli, Fin.mk.injEq] <;>
    norm_num

/-- `smGen 1` row 6: only column 7 is nonzero (value 1). -/
theorem smGen1_row6 (q : I32) :
    smGen 1 ⟨6, by norm_num⟩ q = if q = ⟨7, by norm_num⟩ then 1 else 0 := by
  have h1 : smGen (1 : Fin 12) = genH 0 := rfl
  rw [h1]
  fin_cases q <;>
    simp only [genH, pauli, Fin.mk.injEq] <;>
    norm_num

/-- `smGen 1` row 7: only column 6 is nonzero (value 1). -/
theorem smGen1_row7 (q : I32) :
    smGen 1 ⟨7, by norm_num⟩ q = if q = ⟨6, by norm_num⟩ then 1 else 0 := by
  have h1 : smGen (1 : Fin 12) = genH 0 := rfl
  rw [h1]
  fin_cases q <;>
    simp only [genH, pauli, Fin.mk.injEq] <;>
    norm_num

/-! ### The 8 color-universality identifications -/
/-- Identification 1: D(4,12) = D(2,10) (yU green = red).
From `[[D, smGen 1], smGenOp 4](3,12) = D(4,12) - D(2,10) = 0`. -/
theorem ident_yU_green (D : Matrix I32 I32 ℂ) (h_oo : OrderOneHolds D) :
    D (4 : I32) (12 : I32) = D (2 : I32) (10 : I32) := by
  have hzero := dcomm_entry_zero D h_oo 1 4 (3 : I32) (12 : I32)
  have hcomp : ((D * smGen 1 - smGen 1 * D) * smGenOp 4
      - smGenOp 4 * (D * smGen 1 - smGen 1 * D)) (3 : I32) (12 : I32)
      = D (4 : I32) (12 : I32) - D (2 : I32) (10 : I32) := by
    have Xeq : ∀ i j : I32, (D * smGen 1 - smGen 1 * D) i j
        = (∑ q, D i q * smGen 1 q j) - (∑ q, smGen 1 i q * D q j) := by
      intro i j
      rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
    rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Xeq]
    -- Convert lemmas to (n : I32) form
    have col12 : ∀ p : I32, smGenOp 4 p (12 : I32)
        = if p = (10 : I32) then 1 else 0 := fun p => smGenOp4_col12 p
    have row3 : ∀ p : I32, smGenOp 4 (3 : I32) p
        = if p = (5 : I32) then 1 else 0 := fun p => smGenOp4_row3 p
    have s1row3 : ∀ q : I32, smGen 1 (3 : I32) q
        = if q = (2 : I32) then 1 else 0 := fun q => smGen1_row3 q
    have s1row5 : ∀ q : I32, smGen 1 (5 : I32) q
        = if q = (4 : I32) then 1 else 0 := fun q => smGen1_row5 q
    have s1col10 : ∀ q : I32, smGen 1 q (10 : I32) = 0 := fun q => smGen1_col10 q
    have s1col12 : ∀ q : I32, smGen 1 q (12 : I32) = 0 := fun q => smGen1_col12 q
    have sum1 : ∑ p : I32, ((∑ q, D (3 : I32) q * smGen 1 q p)
          - (∑ q, smGen 1 (3 : I32) q * D q p)) * smGenOp 4 p (12 : I32)
        = (∑ q, D (3 : I32) q * smGen 1 q (10 : I32))
        - (∑ q, smGen 1 (3 : I32) q * D q (10 : I32)) := by
      have h0 : ∀ p ∈ (Finset.univ : Finset I32), p ≠ (10 : I32) →
          ((∑ q, D (3 : I32) q * smGen 1 q p)
          - (∑ q, smGen 1 (3 : I32) q * D q p)) * smGenOp 4 p (12 : I32) = 0 := by
        intro p _ hp
        rw [col12 p, if_neg hp, mul_zero]
      have h1 : ((∑ q, D (3 : I32) q * smGen 1 q (10 : I32))
          - (∑ q, smGen 1 (3 : I32) q * D q (10 : I32)))
          * smGenOp 4 (10 : I32) (12 : I32)
          = (∑ q, D (3 : I32) q * smGen 1 q (10 : I32))
          - (∑ q, smGen 1 (3 : I32) q * D q (10 : I32)) := by
        rw [col12 (10 : I32), if_pos rfl, mul_one]
      exact calc ∑ p : I32, ((∑ q, D (3 : I32) q * smGen 1 q p)
              - (∑ q, smGen 1 (3 : I32) q * D q p)) * smGenOp 4 p (12 : I32)
          = ((∑ q, D (3 : I32) q * smGen 1 q (10 : I32))
            - (∑ q, smGen 1 (3 : I32) q * D q (10 : I32)))
            * smGenOp 4 (10 : I32) (12 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
        _ = _ := h1
    have sum2 : ∑ p : I32, smGenOp 4 (3 : I32) p *
        ((∑ q, D p q * smGen 1 q (12 : I32))
        - (∑ q, smGen 1 p q * D q (12 : I32)))
        = (∑ q, D (5 : I32) q * smGen 1 q (12 : I32))
        - (∑ q, smGen 1 (5 : I32) q * D q (12 : I32)) := by
      have h0 : ∀ p ∈ (Finset.univ : Finset I32), p ≠ (5 : I32) →
          smGenOp 4 (3 : I32) p *
          ((∑ q, D p q * smGen 1 q (12 : I32))
          - (∑ q, smGen 1 p q * D q (12 : I32))) = 0 := by
        intro p _ hp
        rw [row3 p, if_neg hp, zero_mul]
      have h1 : smGenOp 4 (3 : I32) (5 : I32) *
          ((∑ q, D (5 : I32) q * smGen 1 q (12 : I32))
          - (∑ q, smGen 1 (5 : I32) q * D q (12 : I32)))
          = (∑ q, D (5 : I32) q * smGen 1 q (12 : I32))
          - (∑ q, smGen 1 (5 : I32) q * D q (12 : I32)) := by
        rw [row3 (5 : I32), if_pos rfl, one_mul]
      exact calc ∑ p : I32, smGenOp 4 (3 : I32) p *
            ((∑ q, D p q * smGen 1 q (12 : I32))
            - (∑ q, smGen 1 p q * D q (12 : I32)))
          = smGenOp 4 (3 : I32) (5 : I32) *
            ((∑ q, D (5 : I32) q * smGen 1 q (12 : I32))
            - (∑ q, smGen 1 (5 : I32) q * D q (12 : I32))) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
        _ = _ := h1
    rw [sum1, sum2]
    have hX310 : (∑ q, D (3 : I32) q * smGen 1 q (10 : I32))
        - (∑ q, smGen 1 (3 : I32) q * D q (10 : I32))
        = -D (2 : I32) (10 : I32) := by
      have s1 : ∑ q : I32, D (3 : I32) q * smGen 1 q (10 : I32) = 0 := by
        apply Finset.sum_eq_zero
        intro q _
        rw [s1col10 q, mul_zero]
      have s2 : ∑ q : I32, smGen 1 (3 : I32) q * D q (10 : I32)
          = D (2 : I32) (10 : I32) := by
        have h0 : ∀ q ∈ (Finset.univ : Finset I32), q ≠ (2 : I32) →
            smGen 1 (3 : I32) q * D q (10 : I32) = 0 := by
          intro q _ hq
          rw [s1row3 q, if_neg hq, zero_mul]
        have h1 : smGen 1 (3 : I32) (2 : I32) * D (2 : I32) (10 : I32)
            = D (2 : I32) (10 : I32) := by
          rw [s1row3 (2 : I32), if_pos rfl, one_mul]
        exact calc ∑ q : I32, smGen 1 (3 : I32) q * D q (10 : I32)
            = smGen 1 (3 : I32) (2 : I32) * D (2 : I32) (10 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
          _ = _ := h1
      rw [s1, s2, zero_sub]
    have hX512 : (∑ q, D (5 : I32) q * smGen 1 q (12 : I32))
        - (∑ q, smGen 1 (5 : I32) q * D q (12 : I32))
        = -D (4 : I32) (12 : I32) := by
      have s1 : ∑ q : I32, D (5 : I32) q * smGen 1 q (12 : I32) = 0 := by
        apply Finset.sum_eq_zero
        intro q _
        rw [s1col12 q, mul_zero]
      have s2 : ∑ q : I32, smGen 1 (5 : I32) q * D q (12 : I32)
          = D (4 : I32) (12 : I32) := by
        have h0 : ∀ q ∈ (Finset.univ : Finset I32), q ≠ (4 : I32) →
            smGen 1 (5 : I32) q * D q (12 : I32) = 0 := by
          intro q _ hq
          rw [s1row5 q, if_neg hq, zero_mul]
        have h1 : smGen 1 (5 : I32) (4 : I32) * D (4 : I32) (12 : I32)
            = D (4 : I32) (12 : I32) := by
          rw [s1row5 (4 : I32), if_pos rfl, one_mul]
        exact calc ∑ q : I32, smGen 1 (5 : I32) q * D q (12 : I32)
            = smGen 1 (5 : I32) (4 : I32) * D (4 : I32) (12 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
          _ = _ := h1
      rw [s1, s2, zero_sub]
    rw [hX310, hX512]
    ring
  rw [hcomp] at hzero
  exact sub_eq_zero.mp hzero

/-- Identification 2: D(4,13) = D(2,11).
From `[[D, smGen 1], smGenOp 4](3,13) = D(4,13) - D(2,11) = 0`. -/
theorem ident_yU_green2 (D : Matrix I32 I32 ℂ) (h_oo : OrderOneHolds D) :
    D (4 : I32) (13 : I32) = D (2 : I32) (11 : I32) := by
  have hzero := dcomm_entry_zero D h_oo 1 4 (3 : I32) (13 : I32)
  have hcomp : ((D * smGen 1 - smGen 1 * D) * smGenOp 4
      - smGenOp 4 * (D * smGen 1 - smGen 1 * D)) (3 : I32) (13 : I32)
      = D (4 : I32) (13 : I32) - D (2 : I32) (11 : I32) := by
    have Xeq : ∀ i j : I32, (D * smGen 1 - smGen 1 * D) i j
        = (∑ q, D i q * smGen 1 q j) - (∑ q, smGen 1 i q * D q j) := by
      intro i j
      rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
    rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Xeq]
    have col13 : ∀ p : I32, smGenOp 4 p (13 : I32)
        = if p = (11 : I32) then 1 else 0 := fun p => smGenOp4_col13 p
    have row3 : ∀ p : I32, smGenOp 4 (3 : I32) p
        = if p = (5 : I32) then 1 else 0 := fun p => smGenOp4_row3 p
    have s1row3 : ∀ q : I32, smGen 1 (3 : I32) q
        = if q = (2 : I32) then 1 else 0 := fun q => smGen1_row3 q
    have s1row5 : ∀ q : I32, smGen 1 (5 : I32) q
        = if q = (4 : I32) then 1 else 0 := fun q => smGen1_row5 q
    have s1col11 : ∀ q : I32, smGen 1 q (11 : I32) = 0 := fun q => smGen1_col11 q
    have s1col13 : ∀ q : I32, smGen 1 q (13 : I32) = 0 := fun q => smGen1_col13 q
    have sum1 : ∑ p : I32, ((∑ q, D (3 : I32) q * smGen 1 q p)
          - (∑ q, smGen 1 (3 : I32) q * D q p)) * smGenOp 4 p (13 : I32)
        = (∑ q, D (3 : I32) q * smGen 1 q (11 : I32))
        - (∑ q, smGen 1 (3 : I32) q * D q (11 : I32)) := by
      have h0 : ∀ p ∈ (Finset.univ : Finset I32), p ≠ (11 : I32) →
          ((∑ q, D (3 : I32) q * smGen 1 q p)
          - (∑ q, smGen 1 (3 : I32) q * D q p)) * smGenOp 4 p (13 : I32) = 0 := by
        intro p _ hp
        rw [col13 p, if_neg hp, mul_zero]
      have h1 : ((∑ q, D (3 : I32) q * smGen 1 q (11 : I32))
          - (∑ q, smGen 1 (3 : I32) q * D q (11 : I32)))
          * smGenOp 4 (11 : I32) (13 : I32)
          = (∑ q, D (3 : I32) q * smGen 1 q (11 : I32))
          - (∑ q, smGen 1 (3 : I32) q * D q (11 : I32)) := by
        rw [col13 (11 : I32), if_pos rfl, mul_one]
      exact calc ∑ p : I32, ((∑ q, D (3 : I32) q * smGen 1 q p)
              - (∑ q, smGen 1 (3 : I32) q * D q p)) * smGenOp 4 p (13 : I32)
          = ((∑ q, D (3 : I32) q * smGen 1 q (11 : I32))
            - (∑ q, smGen 1 (3 : I32) q * D q (11 : I32)))
            * smGenOp 4 (11 : I32) (13 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
        _ = _ := h1
    have sum2 : ∑ p : I32, smGenOp 4 (3 : I32) p *
        ((∑ q, D p q * smGen 1 q (13 : I32))
        - (∑ q, smGen 1 p q * D q (13 : I32)))
        = (∑ q, D (5 : I32) q * smGen 1 q (13 : I32))
        - (∑ q, smGen 1 (5 : I32) q * D q (13 : I32)) := by
      have h0 : ∀ p ∈ (Finset.univ : Finset I32), p ≠ (5 : I32) →
          smGenOp 4 (3 : I32) p *
          ((∑ q, D p q * smGen 1 q (13 : I32))
          - (∑ q, smGen 1 p q * D q (13 : I32))) = 0 := by
        intro p _ hp
        rw [row3 p, if_neg hp, zero_mul]
      have h1 : smGenOp 4 (3 : I32) (5 : I32) *
          ((∑ q, D (5 : I32) q * smGen 1 q (13 : I32))
          - (∑ q, smGen 1 (5 : I32) q * D q (13 : I32)))
          = (∑ q, D (5 : I32) q * smGen 1 q (13 : I32))
          - (∑ q, smGen 1 (5 : I32) q * D q (13 : I32)) := by
        rw [row3 (5 : I32), if_pos rfl, one_mul]
      exact calc ∑ p : I32, smGenOp 4 (3 : I32) p *
            ((∑ q, D p q * smGen 1 q (13 : I32))
            - (∑ q, smGen 1 p q * D q (13 : I32)))
          = smGenOp 4 (3 : I32) (5 : I32) *
            ((∑ q, D (5 : I32) q * smGen 1 q (13 : I32))
            - (∑ q, smGen 1 (5 : I32) q * D q (13 : I32))) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
        _ = _ := h1
    rw [sum1, sum2]
    have hX311 : (∑ q, D (3 : I32) q * smGen 1 q (11 : I32))
        - (∑ q, smGen 1 (3 : I32) q * D q (11 : I32))
        = -D (2 : I32) (11 : I32) := by
      have s1 : ∑ q : I32, D (3 : I32) q * smGen 1 q (11 : I32) = 0 := by
        apply Finset.sum_eq_zero
        intro q _
        rw [s1col11 q, mul_zero]
      have s2 : ∑ q : I32, smGen 1 (3 : I32) q * D q (11 : I32)
          = D (2 : I32) (11 : I32) := by
        have h0 : ∀ q ∈ (Finset.univ : Finset I32), q ≠ (2 : I32) →
            smGen 1 (3 : I32) q * D q (11 : I32) = 0 := by
          intro q _ hq
          rw [s1row3 q, if_neg hq, zero_mul]
        have h1 : smGen 1 (3 : I32) (2 : I32) * D (2 : I32) (11 : I32)
            = D (2 : I32) (11 : I32) := by
          rw [s1row3 (2 : I32), if_pos rfl, one_mul]
        exact calc ∑ q : I32, smGen 1 (3 : I32) q * D q (11 : I32)
            = smGen 1 (3 : I32) (2 : I32) * D (2 : I32) (11 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
          _ = _ := h1
      rw [s1, s2, zero_sub]
    have hX513 : (∑ q, D (5 : I32) q * smGen 1 q (13 : I32))
        - (∑ q, smGen 1 (5 : I32) q * D q (13 : I32))
        = -D (4 : I32) (13 : I32) := by
      have s1 : ∑ q : I32, D (5 : I32) q * smGen 1 q (13 : I32) = 0 := by
        apply Finset.sum_eq_zero
        intro q _
        rw [s1col13 q, mul_zero]
      have s2 : ∑ q : I32, smGen 1 (5 : I32) q * D q (13 : I32)
          = D (4 : I32) (13 : I32) := by
        have h0 : ∀ q ∈ (Finset.univ : Finset I32), q ≠ (4 : I32) →
            smGen 1 (5 : I32) q * D q (13 : I32) = 0 := by
          intro q _ hq
          rw [s1row5 q, if_neg hq, zero_mul]
        have h1 : smGen 1 (5 : I32) (4 : I32) * D (4 : I32) (13 : I32)
            = D (4 : I32) (13 : I32) := by
          rw [s1row5 (4 : I32), if_pos rfl, one_mul]
        exact calc ∑ q : I32, smGen 1 (5 : I32) q * D q (13 : I32)
            = smGen 1 (5 : I32) (4 : I32) * D (4 : I32) (13 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
          _ = _ := h1
      rw [s1, s2, zero_sub]
    rw [hX311, hX513]
    ring
  rw [hcomp] at hzero
  exact sub_eq_zero.mp hzero

/-- Identification 3: D(5,12) = D(3,10).
From `[[D, smGen 1], smGenOp 4](2,12) = D(5,12) - D(3,10) = 0`. -/
theorem ident_yU_green3 (D : Matrix I32 I32 ℂ) (h_oo : OrderOneHolds D) :
    D (5 : I32) (12 : I32) = D (3 : I32) (10 : I32) := by
  have hzero := dcomm_entry_zero D h_oo 1 4 (2 : I32) (12 : I32)
  have hcomp : ((D * smGen 1 - smGen 1 * D) * smGenOp 4
      - smGenOp 4 * (D * smGen 1 - smGen 1 * D)) (2 : I32) (12 : I32)
      = D (5 : I32) (12 : I32) - D (3 : I32) (10 : I32) := by
    have Xeq : ∀ i j : I32, (D * smGen 1 - smGen 1 * D) i j
        = (∑ q, D i q * smGen 1 q j) - (∑ q, smGen 1 i q * D q j) := by
      intro i j
      rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
    rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Xeq]
    have col12 : ∀ p : I32, smGenOp 4 p (12 : I32)
        = if p = (10 : I32) then 1 else 0 := fun p => smGenOp4_col12 p
    have row2 : ∀ p : I32, smGenOp 4 (2 : I32) p
        = if p = (4 : I32) then 1 else 0 := fun p => smGenOp4_row2 p
    have s1row2 : ∀ q : I32, smGen 1 (2 : I32) q
        = if q = (3 : I32) then 1 else 0 := fun q => smGen1_row2 q
    have s1row4 : ∀ q : I32, smGen 1 (4 : I32) q
        = if q = (5 : I32) then 1 else 0 := fun q => smGen1_row4 q
    have s1col10 : ∀ q : I32, smGen 1 q (10 : I32) = 0 := fun q => smGen1_col10 q
    have s1col12 : ∀ q : I32, smGen 1 q (12 : I32) = 0 := fun q => smGen1_col12 q
    have sum1 : ∑ p : I32, ((∑ q, D (2 : I32) q * smGen 1 q p)
          - (∑ q, smGen 1 (2 : I32) q * D q p)) * smGenOp 4 p (12 : I32)
        = (∑ q, D (2 : I32) q * smGen 1 q (10 : I32))
        - (∑ q, smGen 1 (2 : I32) q * D q (10 : I32)) := by
      have h0 : ∀ p ∈ (Finset.univ : Finset I32), p ≠ (10 : I32) →
          ((∑ q, D (2 : I32) q * smGen 1 q p)
          - (∑ q, smGen 1 (2 : I32) q * D q p)) * smGenOp 4 p (12 : I32) = 0 := by
        intro p _ hp
        rw [col12 p, if_neg hp, mul_zero]
      have h1 : ((∑ q, D (2 : I32) q * smGen 1 q (10 : I32))
          - (∑ q, smGen 1 (2 : I32) q * D q (10 : I32)))
          * smGenOp 4 (10 : I32) (12 : I32)
          = (∑ q, D (2 : I32) q * smGen 1 q (10 : I32))
          - (∑ q, smGen 1 (2 : I32) q * D q (10 : I32)) := by
        rw [col12 (10 : I32), if_pos rfl, mul_one]
      exact calc ∑ p : I32, ((∑ q, D (2 : I32) q * smGen 1 q p)
              - (∑ q, smGen 1 (2 : I32) q * D q p)) * smGenOp 4 p (12 : I32)
          = ((∑ q, D (2 : I32) q * smGen 1 q (10 : I32))
            - (∑ q, smGen 1 (2 : I32) q * D q (10 : I32)))
            * smGenOp 4 (10 : I32) (12 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
        _ = _ := h1
    have sum2 : ∑ p : I32, smGenOp 4 (2 : I32) p *
        ((∑ q, D p q * smGen 1 q (12 : I32))
        - (∑ q, smGen 1 p q * D q (12 : I32)))
        = (∑ q, D (4 : I32) q * smGen 1 q (12 : I32))
        - (∑ q, smGen 1 (4 : I32) q * D q (12 : I32)) := by
      have h0 : ∀ p ∈ (Finset.univ : Finset I32), p ≠ (4 : I32) →
          smGenOp 4 (2 : I32) p *
          ((∑ q, D p q * smGen 1 q (12 : I32))
          - (∑ q, smGen 1 p q * D q (12 : I32))) = 0 := by
        intro p _ hp
        rw [row2 p, if_neg hp, zero_mul]
      have h1 : smGenOp 4 (2 : I32) (4 : I32) *
          ((∑ q, D (4 : I32) q * smGen 1 q (12 : I32))
          - (∑ q, smGen 1 (4 : I32) q * D q (12 : I32)))
          = (∑ q, D (4 : I32) q * smGen 1 q (12 : I32))
          - (∑ q, smGen 1 (4 : I32) q * D q (12 : I32)) := by
        rw [row2 (4 : I32), if_pos rfl, one_mul]
      exact calc ∑ p : I32, smGenOp 4 (2 : I32) p *
            ((∑ q, D p q * smGen 1 q (12 : I32))
            - (∑ q, smGen 1 p q * D q (12 : I32)))
          = smGenOp 4 (2 : I32) (4 : I32) *
            ((∑ q, D (4 : I32) q * smGen 1 q (12 : I32))
            - (∑ q, smGen 1 (4 : I32) q * D q (12 : I32))) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
        _ = _ := h1
    rw [sum1, sum2]
    have hX210 : (∑ q, D (2 : I32) q * smGen 1 q (10 : I32))
        - (∑ q, smGen 1 (2 : I32) q * D q (10 : I32))
        = -D (3 : I32) (10 : I32) := by
      have s1 : ∑ q : I32, D (2 : I32) q * smGen 1 q (10 : I32) = 0 := by
        apply Finset.sum_eq_zero
        intro q _
        rw [s1col10 q, mul_zero]
      have s2 : ∑ q : I32, smGen 1 (2 : I32) q * D q (10 : I32)
          = D (3 : I32) (10 : I32) := by
        have h0 : ∀ q ∈ (Finset.univ : Finset I32), q ≠ (3 : I32) →
            smGen 1 (2 : I32) q * D q (10 : I32) = 0 := by
          intro q _ hq
          rw [s1row2 q, if_neg hq, zero_mul]
        have h1 : smGen 1 (2 : I32) (3 : I32) * D (3 : I32) (10 : I32)
            = D (3 : I32) (10 : I32) := by
          rw [s1row2 (3 : I32), if_pos rfl, one_mul]
        exact calc ∑ q : I32, smGen 1 (2 : I32) q * D q (10 : I32)
            = smGen 1 (2 : I32) (3 : I32) * D (3 : I32) (10 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
          _ = _ := h1
      rw [s1, s2, zero_sub]
    have hX412 : (∑ q, D (4 : I32) q * smGen 1 q (12 : I32))
        - (∑ q, smGen 1 (4 : I32) q * D q (12 : I32))
        = -D (5 : I32) (12 : I32) := by
      have s1 : ∑ q : I32, D (4 : I32) q * smGen 1 q (12 : I32) = 0 := by
        apply Finset.sum_eq_zero
        intro q _
        rw [s1col12 q, mul_zero]
      have s2 : ∑ q : I32, smGen 1 (4 : I32) q * D q (12 : I32)
          = D (5 : I32) (12 : I32) := by
        have h0 : ∀ q ∈ (Finset.univ : Finset I32), q ≠ (5 : I32) →
            smGen 1 (4 : I32) q * D q (12 : I32) = 0 := by
          intro q _ hq
          rw [s1row4 q, if_neg hq, zero_mul]
        have h1 : smGen 1 (4 : I32) (5 : I32) * D (5 : I32) (12 : I32)
            = D (5 : I32) (12 : I32) := by
          rw [s1row4 (5 : I32), if_pos rfl, one_mul]
        exact calc ∑ q : I32, smGen 1 (4 : I32) q * D q (12 : I32)
            = smGen 1 (4 : I32) (5 : I32) * D (5 : I32) (12 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
          _ = _ := h1
      rw [s1, s2, zero_sub]
    rw [hX210, hX412]
    ring
  rw [hcomp] at hzero
  exact sub_eq_zero.mp hzero

/-- Identification 4: D(5,13) = D(3,11).
From `[[D, smGen 1], smGenOp 4](2,13) = D(5,13) - D(3,11) = 0`. -/
theorem ident_yU_green4 (D : Matrix I32 I32 ℂ) (h_oo : OrderOneHolds D) :
    D (5 : I32) (13 : I32) = D (3 : I32) (11 : I32) := by
  have hzero := dcomm_entry_zero D h_oo 1 4 (2 : I32) (13 : I32)
  have hcomp : ((D * smGen 1 - smGen 1 * D) * smGenOp 4
      - smGenOp 4 * (D * smGen 1 - smGen 1 * D)) (2 : I32) (13 : I32)
      = D (5 : I32) (13 : I32) - D (3 : I32) (11 : I32) := by
    have Xeq : ∀ i j : I32, (D * smGen 1 - smGen 1 * D) i j
        = (∑ q, D i q * smGen 1 q j) - (∑ q, smGen 1 i q * D q j) := by
      intro i j
      rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
    rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Xeq]
    have col13 : ∀ p : I32, smGenOp 4 p (13 : I32)
        = if p = (11 : I32) then 1 else 0 := fun p => smGenOp4_col13 p
    have row2 : ∀ p : I32, smGenOp 4 (2 : I32) p
        = if p = (4 : I32) then 1 else 0 := fun p => smGenOp4_row2 p
    have s1row2 : ∀ q : I32, smGen 1 (2 : I32) q
        = if q = (3 : I32) then 1 else 0 := fun q => smGen1_row2 q
    have s1row4 : ∀ q : I32, smGen 1 (4 : I32) q
        = if q = (5 : I32) then 1 else 0 := fun q => smGen1_row4 q
    have s1col11 : ∀ q : I32, smGen 1 q (11 : I32) = 0 := fun q => smGen1_col11 q
    have s1col13 : ∀ q : I32, smGen 1 q (13 : I32) = 0 := fun q => smGen1_col13 q
    have sum1 : ∑ p : I32, ((∑ q, D (2 : I32) q * smGen 1 q p)
          - (∑ q, smGen 1 (2 : I32) q * D q p)) * smGenOp 4 p (13 : I32)
        = (∑ q, D (2 : I32) q * smGen 1 q (11 : I32))
        - (∑ q, smGen 1 (2 : I32) q * D q (11 : I32)) := by
      have h0 : ∀ p ∈ (Finset.univ : Finset I32), p ≠ (11 : I32) →
          ((∑ q, D (2 : I32) q * smGen 1 q p)
          - (∑ q, smGen 1 (2 : I32) q * D q p)) * smGenOp 4 p (13 : I32) = 0 := by
        intro p _ hp
        rw [col13 p, if_neg hp, mul_zero]
      have h1 : ((∑ q, D (2 : I32) q * smGen 1 q (11 : I32))
          - (∑ q, smGen 1 (2 : I32) q * D q (11 : I32)))
          * smGenOp 4 (11 : I32) (13 : I32)
          = (∑ q, D (2 : I32) q * smGen 1 q (11 : I32))
          - (∑ q, smGen 1 (2 : I32) q * D q (11 : I32)) := by
        rw [col13 (11 : I32), if_pos rfl, mul_one]
      exact calc ∑ p : I32, ((∑ q, D (2 : I32) q * smGen 1 q p)
              - (∑ q, smGen 1 (2 : I32) q * D q p)) * smGenOp 4 p (13 : I32)
          = ((∑ q, D (2 : I32) q * smGen 1 q (11 : I32))
            - (∑ q, smGen 1 (2 : I32) q * D q (11 : I32)))
            * smGenOp 4 (11 : I32) (13 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
        _ = _ := h1
    have sum2 : ∑ p : I32, smGenOp 4 (2 : I32) p *
        ((∑ q, D p q * smGen 1 q (13 : I32))
        - (∑ q, smGen 1 p q * D q (13 : I32)))
        = (∑ q, D (4 : I32) q * smGen 1 q (13 : I32))
        - (∑ q, smGen 1 (4 : I32) q * D q (13 : I32)) := by
      have h0 : ∀ p ∈ (Finset.univ : Finset I32), p ≠ (4 : I32) →
          smGenOp 4 (2 : I32) p *
          ((∑ q, D p q * smGen 1 q (13 : I32))
          - (∑ q, smGen 1 p q * D q (13 : I32))) = 0 := by
        intro p _ hp
        rw [row2 p, if_neg hp, zero_mul]
      have h1 : smGenOp 4 (2 : I32) (4 : I32) *
          ((∑ q, D (4 : I32) q * smGen 1 q (13 : I32))
          - (∑ q, smGen 1 (4 : I32) q * D q (13 : I32)))
          = (∑ q, D (4 : I32) q * smGen 1 q (13 : I32))
          - (∑ q, smGen 1 (4 : I32) q * D q (13 : I32)) := by
        rw [row2 (4 : I32), if_pos rfl, one_mul]
      exact calc ∑ p : I32, smGenOp 4 (2 : I32) p *
            ((∑ q, D p q * smGen 1 q (13 : I32))
            - (∑ q, smGen 1 p q * D q (13 : I32)))
          = smGenOp 4 (2 : I32) (4 : I32) *
            ((∑ q, D (4 : I32) q * smGen 1 q (13 : I32))
            - (∑ q, smGen 1 (4 : I32) q * D q (13 : I32))) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
        _ = _ := h1
    rw [sum1, sum2]
    have hX211 : (∑ q, D (2 : I32) q * smGen 1 q (11 : I32))
        - (∑ q, smGen 1 (2 : I32) q * D q (11 : I32))
        = -D (3 : I32) (11 : I32) := by
      have s1 : ∑ q : I32, D (2 : I32) q * smGen 1 q (11 : I32) = 0 := by
        apply Finset.sum_eq_zero
        intro q _
        rw [s1col11 q, mul_zero]
      have s2 : ∑ q : I32, smGen 1 (2 : I32) q * D q (11 : I32)
          = D (3 : I32) (11 : I32) := by
        have h0 : ∀ q ∈ (Finset.univ : Finset I32), q ≠ (3 : I32) →
            smGen 1 (2 : I32) q * D q (11 : I32) = 0 := by
          intro q _ hq
          rw [s1row2 q, if_neg hq, zero_mul]
        have h1 : smGen 1 (2 : I32) (3 : I32) * D (3 : I32) (11 : I32)
            = D (3 : I32) (11 : I32) := by
          rw [s1row2 (3 : I32), if_pos rfl, one_mul]
        exact calc ∑ q : I32, smGen 1 (2 : I32) q * D q (11 : I32)
            = smGen 1 (2 : I32) (3 : I32) * D (3 : I32) (11 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
          _ = _ := h1
      rw [s1, s2, zero_sub]
    have hX413 : (∑ q, D (4 : I32) q * smGen 1 q (13 : I32))
        - (∑ q, smGen 1 (4 : I32) q * D q (13 : I32))
        = -D (5 : I32) (13 : I32) := by
      have s1 : ∑ q : I32, D (4 : I32) q * smGen 1 q (13 : I32) = 0 := by
        apply Finset.sum_eq_zero
        intro q _
        rw [s1col13 q, mul_zero]
      have s2 : ∑ q : I32, smGen 1 (4 : I32) q * D q (13 : I32)
          = D (5 : I32) (13 : I32) := by
        have h0 : ∀ q ∈ (Finset.univ : Finset I32), q ≠ (5 : I32) →
            smGen 1 (4 : I32) q * D q (13 : I32) = 0 := by
          intro q _ hq
          rw [s1row4 q, if_neg hq, zero_mul]
        have h1 : smGen 1 (4 : I32) (5 : I32) * D (5 : I32) (13 : I32)
            = D (5 : I32) (13 : I32) := by
          rw [s1row4 (5 : I32), if_pos rfl, one_mul]
        exact calc ∑ q : I32, smGen 1 (4 : I32) q * D q (13 : I32)
            = smGen 1 (4 : I32) (5 : I32) * D (5 : I32) (13 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
          _ = _ := h1
      rw [s1, s2, zero_sub]
    rw [hX211, hX413]
    ring
  rw [hcomp] at hzero
  exact sub_eq_zero.mp hzero

/-- Identification 5: D(6,14) = D(2,10).
From `[[D, smGen 1], smGenOp 7](3,14) = D(6,14) - D(2,10) = 0`. -/
theorem ident_yU_blue (D : Matrix I32 I32 ℂ) (h_oo : OrderOneHolds D) :
    D (6 : I32) (14 : I32) = D (2 : I32) (10 : I32) := by
  have hzero := dcomm_entry_zero D h_oo 1 7 (3 : I32) (14 : I32)
  have hcomp : ((D * smGen 1 - smGen 1 * D) * smGenOp 7
      - smGenOp 7 * (D * smGen 1 - smGen 1 * D)) (3 : I32) (14 : I32)
      = D (6 : I32) (14 : I32) - D (2 : I32) (10 : I32) := by
    have Xeq : ∀ i j : I32, (D * smGen 1 - smGen 1 * D) i j
        = (∑ q, D i q * smGen 1 q j) - (∑ q, smGen 1 i q * D q j) := by
      intro i j
      rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
    rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Xeq]
    have col14 : ∀ p : I32, smGenOp 7 p (14 : I32)
        = if p = (10 : I32) then 1 else 0 := fun p => smGenOp7_col14 p
    have row3 : ∀ p : I32, smGenOp 7 (3 : I32) p
        = if p = (7 : I32) then 1 else 0 := fun p => smGenOp7_row3 p
    have s1row3 : ∀ q : I32, smGen 1 (3 : I32) q
        = if q = (2 : I32) then 1 else 0 := fun q => smGen1_row3 q
    have s1row7 : ∀ q : I32, smGen 1 (7 : I32) q
        = if q = (6 : I32) then 1 else 0 := fun q => smGen1_row7 q
    have s1col10 : ∀ q : I32, smGen 1 q (10 : I32) = 0 := fun q => smGen1_col10 q
    have s1col14 : ∀ q : I32, smGen 1 q (14 : I32) = 0 := fun q => smGen1_col14 q
    have sum1 : ∑ p : I32, ((∑ q, D (3 : I32) q * smGen 1 q p)
          - (∑ q, smGen 1 (3 : I32) q * D q p)) * smGenOp 7 p (14 : I32)
        = (∑ q, D (3 : I32) q * smGen 1 q (10 : I32))
        - (∑ q, smGen 1 (3 : I32) q * D q (10 : I32)) := by
      have h0 : ∀ p ∈ (Finset.univ : Finset I32), p ≠ (10 : I32) →
          ((∑ q, D (3 : I32) q * smGen 1 q p)
          - (∑ q, smGen 1 (3 : I32) q * D q p)) * smGenOp 7 p (14 : I32) = 0 := by
        intro p _ hp
        rw [col14 p, if_neg hp, mul_zero]
      have h1 : ((∑ q, D (3 : I32) q * smGen 1 q (10 : I32))
          - (∑ q, smGen 1 (3 : I32) q * D q (10 : I32)))
          * smGenOp 7 (10 : I32) (14 : I32)
          = (∑ q, D (3 : I32) q * smGen 1 q (10 : I32))
          - (∑ q, smGen 1 (3 : I32) q * D q (10 : I32)) := by
        rw [col14 (10 : I32), if_pos rfl, mul_one]
      exact calc ∑ p : I32, ((∑ q, D (3 : I32) q * smGen 1 q p)
              - (∑ q, smGen 1 (3 : I32) q * D q p)) * smGenOp 7 p (14 : I32)
          = ((∑ q, D (3 : I32) q * smGen 1 q (10 : I32))
            - (∑ q, smGen 1 (3 : I32) q * D q (10 : I32)))
            * smGenOp 7 (10 : I32) (14 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
        _ = _ := h1
    have sum2 : ∑ p : I32, smGenOp 7 (3 : I32) p *
        ((∑ q, D p q * smGen 1 q (14 : I32))
        - (∑ q, smGen 1 p q * D q (14 : I32)))
        = (∑ q, D (7 : I32) q * smGen 1 q (14 : I32))
        - (∑ q, smGen 1 (7 : I32) q * D q (14 : I32)) := by
      have h0 : ∀ p ∈ (Finset.univ : Finset I32), p ≠ (7 : I32) →
          smGenOp 7 (3 : I32) p *
          ((∑ q, D p q * smGen 1 q (14 : I32))
          - (∑ q, smGen 1 p q * D q (14 : I32))) = 0 := by
        intro p _ hp
        rw [row3 p, if_neg hp, zero_mul]
      have h1 : smGenOp 7 (3 : I32) (7 : I32) *
          ((∑ q, D (7 : I32) q * smGen 1 q (14 : I32))
          - (∑ q, smGen 1 (7 : I32) q * D q (14 : I32)))
          = (∑ q, D (7 : I32) q * smGen 1 q (14 : I32))
          - (∑ q, smGen 1 (7 : I32) q * D q (14 : I32)) := by
        rw [row3 (7 : I32), if_pos rfl, one_mul]
      exact calc ∑ p : I32, smGenOp 7 (3 : I32) p *
            ((∑ q, D p q * smGen 1 q (14 : I32))
            - (∑ q, smGen 1 p q * D q (14 : I32)))
          = smGenOp 7 (3 : I32) (7 : I32) *
            ((∑ q, D (7 : I32) q * smGen 1 q (14 : I32))
            - (∑ q, smGen 1 (7 : I32) q * D q (14 : I32))) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
        _ = _ := h1
    rw [sum1, sum2]
    have hX310 : (∑ q, D (3 : I32) q * smGen 1 q (10 : I32))
        - (∑ q, smGen 1 (3 : I32) q * D q (10 : I32))
        = -D (2 : I32) (10 : I32) := by
      have s1 : ∑ q : I32, D (3 : I32) q * smGen 1 q (10 : I32) = 0 := by
        apply Finset.sum_eq_zero
        intro q _
        rw [s1col10 q, mul_zero]
      have s2 : ∑ q : I32, smGen 1 (3 : I32) q * D q (10 : I32)
          = D (2 : I32) (10 : I32) := by
        have h0 : ∀ q ∈ (Finset.univ : Finset I32), q ≠ (2 : I32) →
            smGen 1 (3 : I32) q * D q (10 : I32) = 0 := by
          intro q _ hq
          rw [s1row3 q, if_neg hq, zero_mul]
        have h1 : smGen 1 (3 : I32) (2 : I32) * D (2 : I32) (10 : I32)
            = D (2 : I32) (10 : I32) := by
          rw [s1row3 (2 : I32), if_pos rfl, one_mul]
        exact calc ∑ q : I32, smGen 1 (3 : I32) q * D q (10 : I32)
            = smGen 1 (3 : I32) (2 : I32) * D (2 : I32) (10 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
          _ = _ := h1
      rw [s1, s2, zero_sub]
    have hX714 : (∑ q, D (7 : I32) q * smGen 1 q (14 : I32))
        - (∑ q, smGen 1 (7 : I32) q * D q (14 : I32))
        = -D (6 : I32) (14 : I32) := by
      have s1 : ∑ q : I32, D (7 : I32) q * smGen 1 q (14 : I32) = 0 := by
        apply Finset.sum_eq_zero
        intro q _
        rw [s1col14 q, mul_zero]
      have s2 : ∑ q : I32, smGen 1 (7 : I32) q * D q (14 : I32)
          = D (6 : I32) (14 : I32) := by
        have h0 : ∀ q ∈ (Finset.univ : Finset I32), q ≠ (6 : I32) →
            smGen 1 (7 : I32) q * D q (14 : I32) = 0 := by
          intro q _ hq
          rw [s1row7 q, if_neg hq, zero_mul]
        have h1 : smGen 1 (7 : I32) (6 : I32) * D (6 : I32) (14 : I32)
            = D (6 : I32) (14 : I32) := by
          rw [s1row7 (6 : I32), if_pos rfl, one_mul]
        exact calc ∑ q : I32, smGen 1 (7 : I32) q * D q (14 : I32)
            = smGen 1 (7 : I32) (6 : I32) * D (6 : I32) (14 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
          _ = _ := h1
      rw [s1, s2, zero_sub]
    rw [hX310, hX714]
    ring
  rw [hcomp] at hzero
  exact sub_eq_zero.mp hzero

/-- Identification 6: D(6,15) = D(2,11).
From `[[D, smGen 1], smGenOp 7](3,15) = D(6,15) - D(2,11) = 0`. -/
theorem ident_yU_blue2 (D : Matrix I32 I32 ℂ) (h_oo : OrderOneHolds D) :
    D (6 : I32) (15 : I32) = D (2 : I32) (11 : I32) := by
  have hzero := dcomm_entry_zero D h_oo 1 7 (3 : I32) (15 : I32)
  have hcomp : ((D * smGen 1 - smGen 1 * D) * smGenOp 7
      - smGenOp 7 * (D * smGen 1 - smGen 1 * D)) (3 : I32) (15 : I32)
      = D (6 : I32) (15 : I32) - D (2 : I32) (11 : I32) := by
    have Xeq : ∀ i j : I32, (D * smGen 1 - smGen 1 * D) i j
        = (∑ q, D i q * smGen 1 q j) - (∑ q, smGen 1 i q * D q j) := by
      intro i j
      rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
    rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Xeq]
    have col15 : ∀ p : I32, smGenOp 7 p (15 : I32)
        = if p = (11 : I32) then 1 else 0 := fun p => smGenOp7_col15 p
    have row3 : ∀ p : I32, smGenOp 7 (3 : I32) p
        = if p = (7 : I32) then 1 else 0 := fun p => smGenOp7_row3 p
    have s1row3 : ∀ q : I32, smGen 1 (3 : I32) q
        = if q = (2 : I32) then 1 else 0 := fun q => smGen1_row3 q
    have s1row7 : ∀ q : I32, smGen 1 (7 : I32) q
        = if q = (6 : I32) then 1 else 0 := fun q => smGen1_row7 q
    have s1col11 : ∀ q : I32, smGen 1 q (11 : I32) = 0 := fun q => smGen1_col11 q
    have s1col15 : ∀ q : I32, smGen 1 q (15 : I32) = 0 := fun q => smGen1_col15 q
    have sum1 : ∑ p : I32, ((∑ q, D (3 : I32) q * smGen 1 q p)
          - (∑ q, smGen 1 (3 : I32) q * D q p)) * smGenOp 7 p (15 : I32)
        = (∑ q, D (3 : I32) q * smGen 1 q (11 : I32))
        - (∑ q, smGen 1 (3 : I32) q * D q (11 : I32)) := by
      have h0 : ∀ p ∈ (Finset.univ : Finset I32), p ≠ (11 : I32) →
          ((∑ q, D (3 : I32) q * smGen 1 q p)
          - (∑ q, smGen 1 (3 : I32) q * D q p)) * smGenOp 7 p (15 : I32) = 0 := by
        intro p _ hp
        rw [col15 p, if_neg hp, mul_zero]
      have h1 : ((∑ q, D (3 : I32) q * smGen 1 q (11 : I32))
          - (∑ q, smGen 1 (3 : I32) q * D q (11 : I32)))
          * smGenOp 7 (11 : I32) (15 : I32)
          = (∑ q, D (3 : I32) q * smGen 1 q (11 : I32))
          - (∑ q, smGen 1 (3 : I32) q * D q (11 : I32)) := by
        rw [col15 (11 : I32), if_pos rfl, mul_one]
      exact calc ∑ p : I32, ((∑ q, D (3 : I32) q * smGen 1 q p)
              - (∑ q, smGen 1 (3 : I32) q * D q p)) * smGenOp 7 p (15 : I32)
          = ((∑ q, D (3 : I32) q * smGen 1 q (11 : I32))
            - (∑ q, smGen 1 (3 : I32) q * D q (11 : I32)))
            * smGenOp 7 (11 : I32) (15 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
        _ = _ := h1
    have sum2 : ∑ p : I32, smGenOp 7 (3 : I32) p *
        ((∑ q, D p q * smGen 1 q (15 : I32))
        - (∑ q, smGen 1 p q * D q (15 : I32)))
        = (∑ q, D (7 : I32) q * smGen 1 q (15 : I32))
        - (∑ q, smGen 1 (7 : I32) q * D q (15 : I32)) := by
      have h0 : ∀ p ∈ (Finset.univ : Finset I32), p ≠ (7 : I32) →
          smGenOp 7 (3 : I32) p *
          ((∑ q, D p q * smGen 1 q (15 : I32))
          - (∑ q, smGen 1 p q * D q (15 : I32))) = 0 := by
        intro p _ hp
        rw [row3 p, if_neg hp, zero_mul]
      have h1 : smGenOp 7 (3 : I32) (7 : I32) *
          ((∑ q, D (7 : I32) q * smGen 1 q (15 : I32))
          - (∑ q, smGen 1 (7 : I32) q * D q (15 : I32)))
          = (∑ q, D (7 : I32) q * smGen 1 q (15 : I32))
          - (∑ q, smGen 1 (7 : I32) q * D q (15 : I32)) := by
        rw [row3 (7 : I32), if_pos rfl, one_mul]
      exact calc ∑ p : I32, smGenOp 7 (3 : I32) p *
            ((∑ q, D p q * smGen 1 q (15 : I32))
            - (∑ q, smGen 1 p q * D q (15 : I32)))
          = smGenOp 7 (3 : I32) (7 : I32) *
            ((∑ q, D (7 : I32) q * smGen 1 q (15 : I32))
            - (∑ q, smGen 1 (7 : I32) q * D q (15 : I32))) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
        _ = _ := h1
    rw [sum1, sum2]
    have hX311 : (∑ q, D (3 : I32) q * smGen 1 q (11 : I32))
        - (∑ q, smGen 1 (3 : I32) q * D q (11 : I32))
        = -D (2 : I32) (11 : I32) := by
      have s1 : ∑ q : I32, D (3 : I32) q * smGen 1 q (11 : I32) = 0 := by
        apply Finset.sum_eq_zero
        intro q _
        rw [s1col11 q, mul_zero]
      have s2 : ∑ q : I32, smGen 1 (3 : I32) q * D q (11 : I32)
          = D (2 : I32) (11 : I32) := by
        have h0 : ∀ q ∈ (Finset.univ : Finset I32), q ≠ (2 : I32) →
            smGen 1 (3 : I32) q * D q (11 : I32) = 0 := by
          intro q _ hq
          rw [s1row3 q, if_neg hq, zero_mul]
        have h1 : smGen 1 (3 : I32) (2 : I32) * D (2 : I32) (11 : I32)
            = D (2 : I32) (11 : I32) := by
          rw [s1row3 (2 : I32), if_pos rfl, one_mul]
        exact calc ∑ q : I32, smGen 1 (3 : I32) q * D q (11 : I32)
            = smGen 1 (3 : I32) (2 : I32) * D (2 : I32) (11 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
          _ = _ := h1
      rw [s1, s2, zero_sub]
    have hX715 : (∑ q, D (7 : I32) q * smGen 1 q (15 : I32))
        - (∑ q, smGen 1 (7 : I32) q * D q (15 : I32))
        = -D (6 : I32) (15 : I32) := by
      have s1 : ∑ q : I32, D (7 : I32) q * smGen 1 q (15 : I32) = 0 := by
        apply Finset.sum_eq_zero
        intro q _
        rw [s1col15 q, mul_zero]
      have s2 : ∑ q : I32, smGen 1 (7 : I32) q * D q (15 : I32)
          = D (6 : I32) (15 : I32) := by
        have h0 : ∀ q ∈ (Finset.univ : Finset I32), q ≠ (6 : I32) →
            smGen 1 (7 : I32) q * D q (15 : I32) = 0 := by
          intro q _ hq
          rw [s1row7 q, if_neg hq, zero_mul]
        have h1 : smGen 1 (7 : I32) (6 : I32) * D (6 : I32) (15 : I32)
            = D (6 : I32) (15 : I32) := by
          rw [s1row7 (6 : I32), if_pos rfl, one_mul]
        exact calc ∑ q : I32, smGen 1 (7 : I32) q * D q (15 : I32)
            = smGen 1 (7 : I32) (6 : I32) * D (6 : I32) (15 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
          _ = _ := h1
      rw [s1, s2, zero_sub]
    rw [hX311, hX715]
    ring
  rw [hcomp] at hzero
  exact sub_eq_zero.mp hzero

/-- Identification 7: D(7,14) = D(3,10).
From `[[D, smGen 1], smGenOp 7](2,14) = D(7,14) - D(3,10) = 0`. -/
theorem ident_yU_blue3 (D : Matrix I32 I32 ℂ) (h_oo : OrderOneHolds D) :
    D (7 : I32) (14 : I32) = D (3 : I32) (10 : I32) := by
  have hzero := dcomm_entry_zero D h_oo 1 7 (2 : I32) (14 : I32)
  have hcomp : ((D * smGen 1 - smGen 1 * D) * smGenOp 7
      - smGenOp 7 * (D * smGen 1 - smGen 1 * D)) (2 : I32) (14 : I32)
      = D (7 : I32) (14 : I32) - D (3 : I32) (10 : I32) := by
    have Xeq : ∀ i j : I32, (D * smGen 1 - smGen 1 * D) i j
        = (∑ q, D i q * smGen 1 q j) - (∑ q, smGen 1 i q * D q j) := by
      intro i j
      rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
    rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Xeq]
    have col14 : ∀ p : I32, smGenOp 7 p (14 : I32)
        = if p = (10 : I32) then 1 else 0 := fun p => smGenOp7_col14 p
    have row2 : ∀ p : I32, smGenOp 7 (2 : I32) p
        = if p = (6 : I32) then 1 else 0 := fun p => smGenOp7_row2 p
    have s1row2 : ∀ q : I32, smGen 1 (2 : I32) q
        = if q = (3 : I32) then 1 else 0 := fun q => smGen1_row2 q
    have s1row6 : ∀ q : I32, smGen 1 (6 : I32) q
        = if q = (7 : I32) then 1 else 0 := fun q => smGen1_row6 q
    have s1col10 : ∀ q : I32, smGen 1 q (10 : I32) = 0 := fun q => smGen1_col10 q
    have s1col14 : ∀ q : I32, smGen 1 q (14 : I32) = 0 := fun q => smGen1_col14 q
    have sum1 : ∑ p : I32, ((∑ q, D (2 : I32) q * smGen 1 q p)
          - (∑ q, smGen 1 (2 : I32) q * D q p)) * smGenOp 7 p (14 : I32)
        = (∑ q, D (2 : I32) q * smGen 1 q (10 : I32))
        - (∑ q, smGen 1 (2 : I32) q * D q (10 : I32)) := by
      have h0 : ∀ p ∈ (Finset.univ : Finset I32), p ≠ (10 : I32) →
          ((∑ q, D (2 : I32) q * smGen 1 q p)
          - (∑ q, smGen 1 (2 : I32) q * D q p)) * smGenOp 7 p (14 : I32) = 0 := by
        intro p _ hp
        rw [col14 p, if_neg hp, mul_zero]
      have h1 : ((∑ q, D (2 : I32) q * smGen 1 q (10 : I32))
          - (∑ q, smGen 1 (2 : I32) q * D q (10 : I32)))
          * smGenOp 7 (10 : I32) (14 : I32)
          = (∑ q, D (2 : I32) q * smGen 1 q (10 : I32))
          - (∑ q, smGen 1 (2 : I32) q * D q (10 : I32)) := by
        rw [col14 (10 : I32), if_pos rfl, mul_one]
      exact calc ∑ p : I32, ((∑ q, D (2 : I32) q * smGen 1 q p)
              - (∑ q, smGen 1 (2 : I32) q * D q p)) * smGenOp 7 p (14 : I32)
          = ((∑ q, D (2 : I32) q * smGen 1 q (10 : I32))
            - (∑ q, smGen 1 (2 : I32) q * D q (10 : I32)))
            * smGenOp 7 (10 : I32) (14 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
        _ = _ := h1
    have sum2 : ∑ p : I32, smGenOp 7 (2 : I32) p *
        ((∑ q, D p q * smGen 1 q (14 : I32))
        - (∑ q, smGen 1 p q * D q (14 : I32)))
        = (∑ q, D (6 : I32) q * smGen 1 q (14 : I32))
        - (∑ q, smGen 1 (6 : I32) q * D q (14 : I32)) := by
      have h0 : ∀ p ∈ (Finset.univ : Finset I32), p ≠ (6 : I32) →
          smGenOp 7 (2 : I32) p *
          ((∑ q, D p q * smGen 1 q (14 : I32))
          - (∑ q, smGen 1 p q * D q (14 : I32))) = 0 := by
        intro p _ hp
        rw [row2 p, if_neg hp, zero_mul]
      have h1 : smGenOp 7 (2 : I32) (6 : I32) *
          ((∑ q, D (6 : I32) q * smGen 1 q (14 : I32))
          - (∑ q, smGen 1 (6 : I32) q * D q (14 : I32)))
          = (∑ q, D (6 : I32) q * smGen 1 q (14 : I32))
          - (∑ q, smGen 1 (6 : I32) q * D q (14 : I32)) := by
        rw [row2 (6 : I32), if_pos rfl, one_mul]
      exact calc ∑ p : I32, smGenOp 7 (2 : I32) p *
            ((∑ q, D p q * smGen 1 q (14 : I32))
            - (∑ q, smGen 1 p q * D q (14 : I32)))
          = smGenOp 7 (2 : I32) (6 : I32) *
            ((∑ q, D (6 : I32) q * smGen 1 q (14 : I32))
            - (∑ q, smGen 1 (6 : I32) q * D q (14 : I32))) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
        _ = _ := h1
    rw [sum1, sum2]
    have hX210 : (∑ q, D (2 : I32) q * smGen 1 q (10 : I32))
        - (∑ q, smGen 1 (2 : I32) q * D q (10 : I32))
        = -D (3 : I32) (10 : I32) := by
      have s1 : ∑ q : I32, D (2 : I32) q * smGen 1 q (10 : I32) = 0 := by
        apply Finset.sum_eq_zero
        intro q _
        rw [s1col10 q, mul_zero]
      have s2 : ∑ q : I32, smGen 1 (2 : I32) q * D q (10 : I32)
          = D (3 : I32) (10 : I32) := by
        have h0 : ∀ q ∈ (Finset.univ : Finset I32), q ≠ (3 : I32) →
            smGen 1 (2 : I32) q * D q (10 : I32) = 0 := by
          intro q _ hq
          rw [s1row2 q, if_neg hq, zero_mul]
        have h1 : smGen 1 (2 : I32) (3 : I32) * D (3 : I32) (10 : I32)
            = D (3 : I32) (10 : I32) := by
          rw [s1row2 (3 : I32), if_pos rfl, one_mul]
        exact calc ∑ q : I32, smGen 1 (2 : I32) q * D q (10 : I32)
            = smGen 1 (2 : I32) (3 : I32) * D (3 : I32) (10 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
          _ = _ := h1
      rw [s1, s2, zero_sub]
    have hX614 : (∑ q, D (6 : I32) q * smGen 1 q (14 : I32))
        - (∑ q, smGen 1 (6 : I32) q * D q (14 : I32))
        = -D (7 : I32) (14 : I32) := by
      have s1 : ∑ q : I32, D (6 : I32) q * smGen 1 q (14 : I32) = 0 := by
        apply Finset.sum_eq_zero
        intro q _
        rw [s1col14 q, mul_zero]
      have s2 : ∑ q : I32, smGen 1 (6 : I32) q * D q (14 : I32)
          = D (7 : I32) (14 : I32) := by
        have h0 : ∀ q ∈ (Finset.univ : Finset I32), q ≠ (7 : I32) →
            smGen 1 (6 : I32) q * D q (14 : I32) = 0 := by
          intro q _ hq
          rw [s1row6 q, if_neg hq, zero_mul]
        have h1 : smGen 1 (6 : I32) (7 : I32) * D (7 : I32) (14 : I32)
            = D (7 : I32) (14 : I32) := by
          rw [s1row6 (7 : I32), if_pos rfl, one_mul]
        exact calc ∑ q : I32, smGen 1 (6 : I32) q * D q (14 : I32)
            = smGen 1 (6 : I32) (7 : I32) * D (7 : I32) (14 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
          _ = _ := h1
      rw [s1, s2, zero_sub]
    rw [hX210, hX614]
    ring
  rw [hcomp] at hzero
  exact sub_eq_zero.mp hzero

/-- Identification 8: D(7,15) = D(3,11).
From `[[D, smGen 1], smGenOp 7](2,15) = D(7,15) - D(3,11) = 0`. -/
theorem ident_yU_blue4 (D : Matrix I32 I32 ℂ) (h_oo : OrderOneHolds D) :
    D (7 : I32) (15 : I32) = D (3 : I32) (11 : I32) := by
  have hzero := dcomm_entry_zero D h_oo 1 7 (2 : I32) (15 : I32)
  have hcomp : ((D * smGen 1 - smGen 1 * D) * smGenOp 7
      - smGenOp 7 * (D * smGen 1 - smGen 1 * D)) (2 : I32) (15 : I32)
      = D (7 : I32) (15 : I32) - D (3 : I32) (11 : I32) := by
    have Xeq : ∀ i j : I32, (D * smGen 1 - smGen 1 * D) i j
        = (∑ q, D i q * smGen 1 q j) - (∑ q, smGen 1 i q * D q j) := by
      intro i j
      rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
    rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Xeq]
    have col15 : ∀ p : I32, smGenOp 7 p (15 : I32)
        = if p = (11 : I32) then 1 else 0 := fun p => smGenOp7_col15 p
    have row2 : ∀ p : I32, smGenOp 7 (2 : I32) p
        = if p = (6 : I32) then 1 else 0 := fun p => smGenOp7_row2 p
    have s1row2 : ∀ q : I32, smGen 1 (2 : I32) q
        = if q = (3 : I32) then 1 else 0 := fun q => smGen1_row2 q
    have s1row6 : ∀ q : I32, smGen 1 (6 : I32) q
        = if q = (7 : I32) then 1 else 0 := fun q => smGen1_row6 q
    have s1col11 : ∀ q : I32, smGen 1 q (11 : I32) = 0 := fun q => smGen1_col11 q
    have s1col15 : ∀ q : I32, smGen 1 q (15 : I32) = 0 := fun q => smGen1_col15 q
    have sum1 : ∑ p : I32, ((∑ q, D (2 : I32) q * smGen 1 q p)
          - (∑ q, smGen 1 (2 : I32) q * D q p)) * smGenOp 7 p (15 : I32)
        = (∑ q, D (2 : I32) q * smGen 1 q (11 : I32))
        - (∑ q, smGen 1 (2 : I32) q * D q (11 : I32)) := by
      have h0 : ∀ p ∈ (Finset.univ : Finset I32), p ≠ (11 : I32) →
          ((∑ q, D (2 : I32) q * smGen 1 q p)
          - (∑ q, smGen 1 (2 : I32) q * D q p)) * smGenOp 7 p (15 : I32) = 0 := by
        intro p _ hp
        rw [col15 p, if_neg hp, mul_zero]
      have h1 : ((∑ q, D (2 : I32) q * smGen 1 q (11 : I32))
          - (∑ q, smGen 1 (2 : I32) q * D q (11 : I32)))
          * smGenOp 7 (11 : I32) (15 : I32)
          = (∑ q, D (2 : I32) q * smGen 1 q (11 : I32))
          - (∑ q, smGen 1 (2 : I32) q * D q (11 : I32)) := by
        rw [col15 (11 : I32), if_pos rfl, mul_one]
      exact calc ∑ p : I32, ((∑ q, D (2 : I32) q * smGen 1 q p)
              - (∑ q, smGen 1 (2 : I32) q * D q p)) * smGenOp 7 p (15 : I32)
          = ((∑ q, D (2 : I32) q * smGen 1 q (11 : I32))
            - (∑ q, smGen 1 (2 : I32) q * D q (11 : I32)))
            * smGenOp 7 (11 : I32) (15 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
        _ = _ := h1
    have sum2 : ∑ p : I32, smGenOp 7 (2 : I32) p *
        ((∑ q, D p q * smGen 1 q (15 : I32))
        - (∑ q, smGen 1 p q * D q (15 : I32)))
        = (∑ q, D (6 : I32) q * smGen 1 q (15 : I32))
        - (∑ q, smGen 1 (6 : I32) q * D q (15 : I32)) := by
      have h0 : ∀ p ∈ (Finset.univ : Finset I32), p ≠ (6 : I32) →
          smGenOp 7 (2 : I32) p *
          ((∑ q, D p q * smGen 1 q (15 : I32))
          - (∑ q, smGen 1 p q * D q (15 : I32))) = 0 := by
        intro p _ hp
        rw [row2 p, if_neg hp, zero_mul]
      have h1 : smGenOp 7 (2 : I32) (6 : I32) *
          ((∑ q, D (6 : I32) q * smGen 1 q (15 : I32))
          - (∑ q, smGen 1 (6 : I32) q * D q (15 : I32)))
          = (∑ q, D (6 : I32) q * smGen 1 q (15 : I32))
          - (∑ q, smGen 1 (6 : I32) q * D q (15 : I32)) := by
        rw [row2 (6 : I32), if_pos rfl, one_mul]
      exact calc ∑ p : I32, smGenOp 7 (2 : I32) p *
            ((∑ q, D p q * smGen 1 q (15 : I32))
            - (∑ q, smGen 1 p q * D q (15 : I32)))
          = smGenOp 7 (2 : I32) (6 : I32) *
            ((∑ q, D (6 : I32) q * smGen 1 q (15 : I32))
            - (∑ q, smGen 1 (6 : I32) q * D q (15 : I32))) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
        _ = _ := h1
    rw [sum1, sum2]
    have hX211 : (∑ q, D (2 : I32) q * smGen 1 q (11 : I32))
        - (∑ q, smGen 1 (2 : I32) q * D q (11 : I32))
        = -D (3 : I32) (11 : I32) := by
      have s1 : ∑ q : I32, D (2 : I32) q * smGen 1 q (11 : I32) = 0 := by
        apply Finset.sum_eq_zero
        intro q _
        rw [s1col11 q, mul_zero]
      have s2 : ∑ q : I32, smGen 1 (2 : I32) q * D q (11 : I32)
          = D (3 : I32) (11 : I32) := by
        have h0 : ∀ q ∈ (Finset.univ : Finset I32), q ≠ (3 : I32) →
            smGen 1 (2 : I32) q * D q (11 : I32) = 0 := by
          intro q _ hq
          rw [s1row2 q, if_neg hq, zero_mul]
        have h1 : smGen 1 (2 : I32) (3 : I32) * D (3 : I32) (11 : I32)
            = D (3 : I32) (11 : I32) := by
          rw [s1row2 (3 : I32), if_pos rfl, one_mul]
        exact calc ∑ q : I32, smGen 1 (2 : I32) q * D q (11 : I32)
            = smGen 1 (2 : I32) (3 : I32) * D (3 : I32) (11 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
          _ = _ := h1
      rw [s1, s2, zero_sub]
    have hX615 : (∑ q, D (6 : I32) q * smGen 1 q (15 : I32))
        - (∑ q, smGen 1 (6 : I32) q * D q (15 : I32))
        = -D (7 : I32) (15 : I32) := by
      have s1 : ∑ q : I32, D (6 : I32) q * smGen 1 q (15 : I32) = 0 := by
        apply Finset.sum_eq_zero
        intro q _
        rw [s1col15 q, mul_zero]
      have s2 : ∑ q : I32, smGen 1 (6 : I32) q * D q (15 : I32)
          = D (7 : I32) (15 : I32) := by
        have h0 : ∀ q ∈ (Finset.univ : Finset I32), q ≠ (7 : I32) →
            smGen 1 (6 : I32) q * D q (15 : I32) = 0 := by
          intro q _ hq
          rw [s1row6 q, if_neg hq, zero_mul]
        have h1 : smGen 1 (6 : I32) (7 : I32) * D (7 : I32) (15 : I32)
            = D (7 : I32) (15 : I32) := by
          rw [s1row6 (7 : I32), if_pos rfl, one_mul]
        exact calc ∑ q : I32, smGen 1 (6 : I32) q * D q (15 : I32)
            = smGen 1 (6 : I32) (7 : I32) * D (7 : I32) (15 : I32) :=
            Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
          _ = _ := h1
      rw [s1, s2, zero_sub]
    rw [hX211, hX615]
    ring
  rw [hcomp] at hzero
  exact sub_eq_zero.mp hzero


/-! ## §T4c. Injective map and finrank bound -/

set_option maxRecDepth 10000

open Matrix

/-- SA transport of vanishing: if D i j = 0 then D j i = 0. -/
theorem sa_vanish (D : Matrix I32 I32 ℂ) (hSA : D.conjTranspose = D)
    (i j : I32) (h : D i j = 0) : D j i = 0 := by
  have h1 : D j i = star (D i j) := by
    calc D j i = D.conjTranspose j i := by rw [hSA]
    _ = star (D i j) := by rw [Matrix.conjTranspose_apply]
  rw [h1, h]; exact star_zero ℂ

/-- J transport of vanishing. -/
theorem j_vanish (D : Matrix I32 I32 ℂ) (hJ : IsJCompatible D)
    (i j : I32) (h : D (partner j) (partner i) = 0) : D i j = 0 := by
  rw [j_compat_entry D hJ i j]; exact h

/-- If all 11 pivots vanish, D = 0. -/
theorem D_eq_zero_of_pivots_vanish (D : Matrix I32 I32 ℂ)
    (h_oo : OrderOneHolds D)
    (h_cf : cfCommutatorMap D = 0)
    (h_sa : D.conjTranspose = D)
    (h_J : IsJCompatible D)
    (h_gr : gammaF * D + D * gammaF = 0)
    (hpiv : ∀ m n : Fin 32, (m.val, n.val) ∈ ([(0,8),(1,9),(2,10),(3,11),(24,8),(0,9),(1,8),(2,11),(3,10),(8,25),(9,25)] : List (ℕ × ℕ)) → D m n = 0) :
    D = 0 := by
  have hcf' : D * cfMat - cfMat * D = 0 := by unfold cfCommutatorMap at h_cf; exact h_cf
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.zero_apply]
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (7 : I32) (by decide)
  · -- (0,8) reduces to pivot (0,8)
    have hpiv_mn : D (0 : I32) (8 : I32) = 0 := hpiv (0 : Fin 32) (8 : Fin 32) (by decide)
    exact hpiv_mn
  · -- (0,9) reduces to pivot (0,9)
    have hpiv_mn : D (0 : I32) (9 : I32) = 0 := hpiv (0 : Fin 32) (9 : Fin 32) (by decide)
    exact hpiv_mn
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (0 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (7 : I32) (by decide)
  · -- (1,8) reduces to pivot (1,8)
    have hpiv_mn : D (1 : I32) (8 : I32) = 0 := hpiv (1 : Fin 32) (8 : Fin 32) (by decide)
    exact hpiv_mn
  · -- (1,9) reduces to pivot (1,9)
    have hpiv_mn : D (1 : I32) (9 : I32) = 0 := hpiv (1 : Fin 32) (9 : Fin 32) (by decide)
    exact hpiv_mn
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (1 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (9 : I32) (by decide)
  · -- (2,10) reduces to pivot (2,10)
    have hpiv_mn : D (2 : I32) (10 : I32) = 0 := hpiv (2 : Fin 32) (10 : Fin 32) (by decide)
    exact hpiv_mn
  · -- (2,11) reduces to pivot (2,11)
    have hpiv_mn : D (2 : I32) (11 : I32) = 0 := hpiv (2 : Fin 32) (11 : Fin 32) (by decide)
    exact hpiv_mn
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (2 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (9 : I32) (by decide)
  · -- (3,10) reduces to pivot (3,10)
    have hpiv_mn : D (3 : I32) (10 : I32) = 0 := hpiv (3 : Fin 32) (10 : Fin 32) (by decide)
    exact hpiv_mn
  · -- (3,11) reduces to pivot (3,11)
    have hpiv_mn : D (3 : I32) (11 : I32) = 0 := hpiv (3 : Fin 32) (11 : Fin 32) (by decide)
    exact hpiv_mn
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (3 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (11 : I32) (by decide)
  · -- (4,12) reduces to pivot (2,10)
    have hpiv_mn : D (2 : I32) (10 : I32) = 0 := hpiv (2 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (4 : I32) (12 : I32) = 0 := by rw [ident_yU_green D h_oo]; exact hpiv_mn
    exact hstep_0
  · -- (4,13) reduces to pivot (2,11)
    have hpiv_mn : D (2 : I32) (11 : I32) = 0 := hpiv (2 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (4 : I32) (13 : I32) = 0 := by rw [ident_yU_green2 D h_oo]; exact hpiv_mn
    exact hstep_0
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (4 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (11 : I32) (by decide)
  · -- (5,12) reduces to pivot (3,10)
    have hpiv_mn : D (3 : I32) (10 : I32) = 0 := hpiv (3 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (5 : I32) (12 : I32) = 0 := by rw [ident_yU_green3 D h_oo]; exact hpiv_mn
    exact hstep_0
  · -- (5,13) reduces to pivot (3,11)
    have hpiv_mn : D (3 : I32) (11 : I32) = 0 := hpiv (3 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (5 : I32) (13 : I32) = 0 := by rw [ident_yU_green4 D h_oo]; exact hpiv_mn
    exact hstep_0
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (5 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (13 : I32) (by decide)
  · -- (6,14) reduces to pivot (2,10)
    have hpiv_mn : D (2 : I32) (10 : I32) = 0 := hpiv (2 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (6 : I32) (14 : I32) = 0 := by rw [ident_yU_blue D h_oo]; exact hpiv_mn
    exact hstep_0
  · -- (6,15) reduces to pivot (2,11)
    have hpiv_mn : D (2 : I32) (11 : I32) = 0 := hpiv (2 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (6 : I32) (15 : I32) = 0 := by rw [ident_yU_blue2 D h_oo]; exact hpiv_mn
    exact hstep_0
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (6 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (13 : I32) (by decide)
  · -- (7,14) reduces to pivot (3,10)
    have hpiv_mn : D (3 : I32) (10 : I32) = 0 := hpiv (3 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (7 : I32) (14 : I32) = 0 := by rw [ident_yU_blue3 D h_oo]; exact hpiv_mn
    exact hstep_0
  · -- (7,15) reduces to pivot (3,11)
    have hpiv_mn : D (3 : I32) (11 : I32) = 0 := hpiv (3 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (7 : I32) (15 : I32) = 0 := by rw [ident_yU_blue4 D h_oo]; exact hpiv_mn
    exact hstep_0
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (7 : I32) (31 : I32) (by decide)
  · -- (8,0) reduces to pivot (0,8)
    have hpiv_mn : D (0 : I32) (8 : I32) = 0 := hpiv (0 : Fin 32) (8 : Fin 32) (by decide)
    have hstep_0 : D (8 : I32) (0 : I32) = 0 := sa_vanish D h_sa (0 : I32) (8 : I32) hpiv_mn
    exact hstep_0
  · -- (8,1) reduces to pivot (1,8)
    have hpiv_mn : D (1 : I32) (8 : I32) = 0 := hpiv (1 : Fin 32) (8 : Fin 32) (by decide)
    have hstep_0 : D (8 : I32) (1 : I32) = 0 := sa_vanish D h_sa (1 : I32) (8 : I32) hpiv_mn
    exact hstep_0
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (23 : I32) (by decide)
  · -- (8,24) reduces to pivot (24,8)
    have hpiv_mn : D (24 : I32) (8 : I32) = 0 := hpiv (24 : Fin 32) (8 : Fin 32) (by decide)
    have hstep_0 : D (8 : I32) (24 : I32) = 0 := sa_vanish D h_sa (24 : I32) (8 : I32) hpiv_mn
    exact hstep_0
  · -- (8,25) reduces to pivot (8,25)
    have hpiv_mn : D (8 : I32) (25 : I32) = 0 := hpiv (8 : Fin 32) (25 : Fin 32) (by decide)
    exact hpiv_mn
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (8 : I32) (31 : I32) (by decide)
  · -- (9,0) reduces to pivot (0,9)
    have hpiv_mn : D (0 : I32) (9 : I32) = 0 := hpiv (0 : Fin 32) (9 : Fin 32) (by decide)
    have hstep_0 : D (9 : I32) (0 : I32) = 0 := sa_vanish D h_sa (0 : I32) (9 : I32) hpiv_mn
    exact hstep_0
  · -- (9,1) reduces to pivot (1,9)
    have hpiv_mn : D (1 : I32) (9 : I32) = 0 := hpiv (1 : Fin 32) (9 : Fin 32) (by decide)
    have hstep_0 : D (9 : I32) (1 : I32) = 0 := sa_vanish D h_sa (1 : I32) (9 : I32) hpiv_mn
    exact hstep_0
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (23 : I32) (by decide)
  · -- (9,24) reduces to pivot (8,25)
    have hpiv_mn : D (8 : I32) (25 : I32) = 0 := hpiv (8 : Fin 32) (25 : Fin 32) (by decide)
    have hstep_0 : D (9 : I32) (24 : I32) = 0 := j_vanish D h_J (9 : I32) (24 : I32) hpiv_mn
    exact hstep_0
  · -- (9,25) reduces to pivot (9,25)
    have hpiv_mn : D (9 : I32) (25 : I32) = 0 := hpiv (9 : Fin 32) (25 : Fin 32) (by decide)
    exact hpiv_mn
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (9 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (1 : I32) (by decide)
  · -- (10,2) reduces to pivot (2,10)
    have hpiv_mn : D (2 : I32) (10 : I32) = 0 := hpiv (2 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (10 : I32) (2 : I32) = 0 := sa_vanish D h_sa (2 : I32) (10 : I32) hpiv_mn
    exact hstep_0
  · -- (10,3) reduces to pivot (3,10)
    have hpiv_mn : D (3 : I32) (10 : I32) = 0 := hpiv (3 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (10 : I32) (3 : I32) = 0 := sa_vanish D h_sa (3 : I32) (10 : I32) hpiv_mn
    exact hstep_0
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (10 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (1 : I32) (by decide)
  · -- (11,2) reduces to pivot (2,11)
    have hpiv_mn : D (2 : I32) (11 : I32) = 0 := hpiv (2 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (11 : I32) (2 : I32) = 0 := sa_vanish D h_sa (2 : I32) (11 : I32) hpiv_mn
    exact hstep_0
  · -- (11,3) reduces to pivot (3,11)
    have hpiv_mn : D (3 : I32) (11 : I32) = 0 := hpiv (3 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (11 : I32) (3 : I32) = 0 := sa_vanish D h_sa (3 : I32) (11 : I32) hpiv_mn
    exact hstep_0
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (11 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (3 : I32) (by decide)
  · -- (12,4) reduces to pivot (2,10)
    have hpiv_mn : D (2 : I32) (10 : I32) = 0 := hpiv (2 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (4 : I32) (12 : I32) = 0 := by rw [ident_yU_green D h_oo]; exact hpiv_mn
    have hstep_1 : D (12 : I32) (4 : I32) = 0 := sa_vanish D h_sa (4 : I32) (12 : I32) hstep_0
    exact hstep_1
  · -- (12,5) reduces to pivot (3,10)
    have hpiv_mn : D (3 : I32) (10 : I32) = 0 := hpiv (3 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (5 : I32) (12 : I32) = 0 := by rw [ident_yU_green3 D h_oo]; exact hpiv_mn
    have hstep_1 : D (12 : I32) (5 : I32) = 0 := sa_vanish D h_sa (5 : I32) (12 : I32) hstep_0
    exact hstep_1
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (12 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (3 : I32) (by decide)
  · -- (13,4) reduces to pivot (2,11)
    have hpiv_mn : D (2 : I32) (11 : I32) = 0 := hpiv (2 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (4 : I32) (13 : I32) = 0 := by rw [ident_yU_green2 D h_oo]; exact hpiv_mn
    have hstep_1 : D (13 : I32) (4 : I32) = 0 := sa_vanish D h_sa (4 : I32) (13 : I32) hstep_0
    exact hstep_1
  · -- (13,5) reduces to pivot (3,11)
    have hpiv_mn : D (3 : I32) (11 : I32) = 0 := hpiv (3 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (5 : I32) (13 : I32) = 0 := by rw [ident_yU_green4 D h_oo]; exact hpiv_mn
    have hstep_1 : D (13 : I32) (5 : I32) = 0 := sa_vanish D h_sa (5 : I32) (13 : I32) hstep_0
    exact hstep_1
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (13 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (5 : I32) (by decide)
  · -- (14,6) reduces to pivot (2,10)
    have hpiv_mn : D (2 : I32) (10 : I32) = 0 := hpiv (2 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (6 : I32) (14 : I32) = 0 := by rw [ident_yU_blue D h_oo]; exact hpiv_mn
    have hstep_1 : D (14 : I32) (6 : I32) = 0 := sa_vanish D h_sa (6 : I32) (14 : I32) hstep_0
    exact hstep_1
  · -- (14,7) reduces to pivot (3,10)
    have hpiv_mn : D (3 : I32) (10 : I32) = 0 := hpiv (3 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (7 : I32) (14 : I32) = 0 := by rw [ident_yU_blue3 D h_oo]; exact hpiv_mn
    have hstep_1 : D (14 : I32) (7 : I32) = 0 := sa_vanish D h_sa (7 : I32) (14 : I32) hstep_0
    exact hstep_1
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (14 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (5 : I32) (by decide)
  · -- (15,6) reduces to pivot (2,11)
    have hpiv_mn : D (2 : I32) (11 : I32) = 0 := hpiv (2 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (6 : I32) (15 : I32) = 0 := by rw [ident_yU_blue2 D h_oo]; exact hpiv_mn
    have hstep_1 : D (15 : I32) (6 : I32) = 0 := sa_vanish D h_sa (6 : I32) (15 : I32) hstep_0
    exact hstep_1
  · -- (15,7) reduces to pivot (3,11)
    have hpiv_mn : D (3 : I32) (11 : I32) = 0 := hpiv (3 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (7 : I32) (15 : I32) = 0 := by rw [ident_yU_blue4 D h_oo]; exact hpiv_mn
    have hstep_1 : D (15 : I32) (7 : I32) = 0 := sa_vanish D h_sa (7 : I32) (15 : I32) hstep_0
    exact hstep_1
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (15 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (23 : I32) (by decide)
  · -- (16,24) reduces to pivot (0,8)
    have hpiv_mn : D (0 : I32) (8 : I32) = 0 := hpiv (0 : Fin 32) (8 : Fin 32) (by decide)
    have hstep_0 : D (24 : I32) (16 : I32) = 0 := j_vanish D h_J (24 : I32) (16 : I32) hpiv_mn
    have hstep_1 : D (16 : I32) (24 : I32) = 0 := sa_vanish D h_sa (24 : I32) (16 : I32) hstep_0
    exact hstep_1
  · -- (16,25) reduces to pivot (0,9)
    have hpiv_mn : D (0 : I32) (9 : I32) = 0 := hpiv (0 : Fin 32) (9 : Fin 32) (by decide)
    have hstep_0 : D (25 : I32) (16 : I32) = 0 := j_vanish D h_J (25 : I32) (16 : I32) hpiv_mn
    have hstep_1 : D (16 : I32) (25 : I32) = 0 := sa_vanish D h_sa (25 : I32) (16 : I32) hstep_0
    exact hstep_1
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (16 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (23 : I32) (by decide)
  · -- (17,24) reduces to pivot (1,8)
    have hpiv_mn : D (1 : I32) (8 : I32) = 0 := hpiv (1 : Fin 32) (8 : Fin 32) (by decide)
    have hstep_0 : D (24 : I32) (17 : I32) = 0 := j_vanish D h_J (24 : I32) (17 : I32) hpiv_mn
    have hstep_1 : D (17 : I32) (24 : I32) = 0 := sa_vanish D h_sa (24 : I32) (17 : I32) hstep_0
    exact hstep_1
  · -- (17,25) reduces to pivot (1,9)
    have hpiv_mn : D (1 : I32) (9 : I32) = 0 := hpiv (1 : Fin 32) (9 : Fin 32) (by decide)
    have hstep_0 : D (25 : I32) (17 : I32) = 0 := j_vanish D h_J (25 : I32) (17 : I32) hpiv_mn
    have hstep_1 : D (17 : I32) (25 : I32) = 0 := sa_vanish D h_sa (25 : I32) (17 : I32) hstep_0
    exact hstep_1
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (17 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (25 : I32) (by decide)
  · -- (18,26) reduces to pivot (2,10)
    have hpiv_mn : D (2 : I32) (10 : I32) = 0 := hpiv (2 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (26 : I32) (18 : I32) = 0 := j_vanish D h_J (26 : I32) (18 : I32) hpiv_mn
    have hstep_1 : D (18 : I32) (26 : I32) = 0 := sa_vanish D h_sa (26 : I32) (18 : I32) hstep_0
    exact hstep_1
  · -- (18,27) reduces to pivot (2,11)
    have hpiv_mn : D (2 : I32) (11 : I32) = 0 := hpiv (2 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (27 : I32) (18 : I32) = 0 := j_vanish D h_J (27 : I32) (18 : I32) hpiv_mn
    have hstep_1 : D (18 : I32) (27 : I32) = 0 := sa_vanish D h_sa (27 : I32) (18 : I32) hstep_0
    exact hstep_1
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (18 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (25 : I32) (by decide)
  · -- (19,26) reduces to pivot (3,10)
    have hpiv_mn : D (3 : I32) (10 : I32) = 0 := hpiv (3 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (26 : I32) (19 : I32) = 0 := j_vanish D h_J (26 : I32) (19 : I32) hpiv_mn
    have hstep_1 : D (19 : I32) (26 : I32) = 0 := sa_vanish D h_sa (26 : I32) (19 : I32) hstep_0
    exact hstep_1
  · -- (19,27) reduces to pivot (3,11)
    have hpiv_mn : D (3 : I32) (11 : I32) = 0 := hpiv (3 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (27 : I32) (19 : I32) = 0 := j_vanish D h_J (27 : I32) (19 : I32) hpiv_mn
    have hstep_1 : D (19 : I32) (27 : I32) = 0 := sa_vanish D h_sa (27 : I32) (19 : I32) hstep_0
    exact hstep_1
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (19 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (27 : I32) (by decide)
  · -- (20,28) reduces to pivot (2,10)
    have hpiv_mn : D (2 : I32) (10 : I32) = 0 := hpiv (2 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (4 : I32) (12 : I32) = 0 := by rw [ident_yU_green D h_oo]; exact hpiv_mn
    have hstep_1 : D (12 : I32) (4 : I32) = 0 := sa_vanish D h_sa (4 : I32) (12 : I32) hstep_0
    have hstep_2 : D (20 : I32) (28 : I32) = 0 := j_vanish D h_J (20 : I32) (28 : I32) hstep_1
    exact hstep_2
  · -- (20,29) reduces to pivot (2,11)
    have hpiv_mn : D (2 : I32) (11 : I32) = 0 := hpiv (2 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (4 : I32) (13 : I32) = 0 := by rw [ident_yU_green2 D h_oo]; exact hpiv_mn
    have hstep_1 : D (13 : I32) (4 : I32) = 0 := sa_vanish D h_sa (4 : I32) (13 : I32) hstep_0
    have hstep_2 : D (20 : I32) (29 : I32) = 0 := j_vanish D h_J (20 : I32) (29 : I32) hstep_1
    exact hstep_2
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (20 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (27 : I32) (by decide)
  · -- (21,28) reduces to pivot (3,10)
    have hpiv_mn : D (3 : I32) (10 : I32) = 0 := hpiv (3 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (5 : I32) (12 : I32) = 0 := by rw [ident_yU_green3 D h_oo]; exact hpiv_mn
    have hstep_1 : D (12 : I32) (5 : I32) = 0 := sa_vanish D h_sa (5 : I32) (12 : I32) hstep_0
    have hstep_2 : D (21 : I32) (28 : I32) = 0 := j_vanish D h_J (21 : I32) (28 : I32) hstep_1
    exact hstep_2
  · -- (21,29) reduces to pivot (3,11)
    have hpiv_mn : D (3 : I32) (11 : I32) = 0 := hpiv (3 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (5 : I32) (13 : I32) = 0 := by rw [ident_yU_green4 D h_oo]; exact hpiv_mn
    have hstep_1 : D (13 : I32) (5 : I32) = 0 := sa_vanish D h_sa (5 : I32) (13 : I32) hstep_0
    have hstep_2 : D (21 : I32) (29 : I32) = 0 := j_vanish D h_J (21 : I32) (29 : I32) hstep_1
    exact hstep_2
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (21 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (22 : I32) (29 : I32) (by decide)
  · -- (22,30) reduces to pivot (2,10)
    have hpiv_mn : D (2 : I32) (10 : I32) = 0 := hpiv (2 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (6 : I32) (14 : I32) = 0 := by rw [ident_yU_blue D h_oo]; exact hpiv_mn
    have hstep_1 : D (14 : I32) (6 : I32) = 0 := sa_vanish D h_sa (6 : I32) (14 : I32) hstep_0
    have hstep_2 : D (22 : I32) (30 : I32) = 0 := j_vanish D h_J (22 : I32) (30 : I32) hstep_1
    exact hstep_2
  · -- (22,31) reduces to pivot (2,11)
    have hpiv_mn : D (2 : I32) (11 : I32) = 0 := hpiv (2 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (6 : I32) (15 : I32) = 0 := by rw [ident_yU_blue2 D h_oo]; exact hpiv_mn
    have hstep_1 : D (15 : I32) (6 : I32) = 0 := sa_vanish D h_sa (6 : I32) (15 : I32) hstep_0
    have hstep_2 : D (22 : I32) (31 : I32) = 0 := j_vanish D h_J (22 : I32) (31 : I32) hstep_1
    exact hstep_2
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (23 : I32) (29 : I32) (by decide)
  · -- (23,30) reduces to pivot (3,10)
    have hpiv_mn : D (3 : I32) (10 : I32) = 0 := hpiv (3 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (7 : I32) (14 : I32) = 0 := by rw [ident_yU_blue3 D h_oo]; exact hpiv_mn
    have hstep_1 : D (14 : I32) (7 : I32) = 0 := sa_vanish D h_sa (7 : I32) (14 : I32) hstep_0
    have hstep_2 : D (23 : I32) (30 : I32) = 0 := j_vanish D h_J (23 : I32) (30 : I32) hstep_1
    exact hstep_2
  · -- (23,31) reduces to pivot (3,11)
    have hpiv_mn : D (3 : I32) (11 : I32) = 0 := hpiv (3 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (7 : I32) (15 : I32) = 0 := by rw [ident_yU_blue4 D h_oo]; exact hpiv_mn
    have hstep_1 : D (15 : I32) (7 : I32) = 0 := sa_vanish D h_sa (7 : I32) (15 : I32) hstep_0
    have hstep_2 : D (23 : I32) (31 : I32) = 0 := j_vanish D h_J (23 : I32) (31 : I32) hstep_1
    exact hstep_2
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (7 : I32) (by decide)
  · -- (24,8) reduces to pivot (24,8)
    have hpiv_mn : D (24 : I32) (8 : I32) = 0 := hpiv (24 : Fin 32) (8 : Fin 32) (by decide)
    exact hpiv_mn
  · -- (24,9) reduces to pivot (8,25)
    have hpiv_mn : D (8 : I32) (25 : I32) = 0 := hpiv (8 : Fin 32) (25 : Fin 32) (by decide)
    have hstep_0 : D (9 : I32) (24 : I32) = 0 := j_vanish D h_J (9 : I32) (24 : I32) hpiv_mn
    have hstep_1 : D (24 : I32) (9 : I32) = 0 := sa_vanish D h_sa (9 : I32) (24 : I32) hstep_0
    exact hstep_1
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (15 : I32) (by decide)
  · -- (24,16) reduces to pivot (0,8)
    have hpiv_mn : D (0 : I32) (8 : I32) = 0 := hpiv (0 : Fin 32) (8 : Fin 32) (by decide)
    have hstep_0 : D (24 : I32) (16 : I32) = 0 := j_vanish D h_J (24 : I32) (16 : I32) hpiv_mn
    exact hstep_0
  · -- (24,17) reduces to pivot (1,8)
    have hpiv_mn : D (1 : I32) (8 : I32) = 0 := hpiv (1 : Fin 32) (8 : Fin 32) (by decide)
    have hstep_0 : D (24 : I32) (17 : I32) = 0 := j_vanish D h_J (24 : I32) (17 : I32) hpiv_mn
    exact hstep_0
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (24 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (7 : I32) (by decide)
  · -- (25,8) reduces to pivot (8,25)
    have hpiv_mn : D (8 : I32) (25 : I32) = 0 := hpiv (8 : Fin 32) (25 : Fin 32) (by decide)
    have hstep_0 : D (25 : I32) (8 : I32) = 0 := sa_vanish D h_sa (8 : I32) (25 : I32) hpiv_mn
    exact hstep_0
  · -- (25,9) reduces to pivot (9,25)
    have hpiv_mn : D (9 : I32) (25 : I32) = 0 := hpiv (9 : Fin 32) (25 : Fin 32) (by decide)
    have hstep_0 : D (25 : I32) (9 : I32) = 0 := sa_vanish D h_sa (9 : I32) (25 : I32) hpiv_mn
    exact hstep_0
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (15 : I32) (by decide)
  · -- (25,16) reduces to pivot (0,9)
    have hpiv_mn : D (0 : I32) (9 : I32) = 0 := hpiv (0 : Fin 32) (9 : Fin 32) (by decide)
    have hstep_0 : D (25 : I32) (16 : I32) = 0 := j_vanish D h_J (25 : I32) (16 : I32) hpiv_mn
    exact hstep_0
  · -- (25,17) reduces to pivot (1,9)
    have hpiv_mn : D (1 : I32) (9 : I32) = 0 := hpiv (1 : Fin 32) (9 : Fin 32) (by decide)
    have hstep_0 : D (25 : I32) (17 : I32) = 0 := j_vanish D h_J (25 : I32) (17 : I32) hpiv_mn
    exact hstep_0
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (25 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (17 : I32) (by decide)
  · -- (26,18) reduces to pivot (2,10)
    have hpiv_mn : D (2 : I32) (10 : I32) = 0 := hpiv (2 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (26 : I32) (18 : I32) = 0 := j_vanish D h_J (26 : I32) (18 : I32) hpiv_mn
    exact hstep_0
  · -- (26,19) reduces to pivot (3,10)
    have hpiv_mn : D (3 : I32) (10 : I32) = 0 := hpiv (3 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (26 : I32) (19 : I32) = 0 := j_vanish D h_J (26 : I32) (19 : I32) hpiv_mn
    exact hstep_0
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (26 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (17 : I32) (by decide)
  · -- (27,18) reduces to pivot (2,11)
    have hpiv_mn : D (2 : I32) (11 : I32) = 0 := hpiv (2 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (27 : I32) (18 : I32) = 0 := j_vanish D h_J (27 : I32) (18 : I32) hpiv_mn
    exact hstep_0
  · -- (27,19) reduces to pivot (3,11)
    have hpiv_mn : D (3 : I32) (11 : I32) = 0 := hpiv (3 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (27 : I32) (19 : I32) = 0 := j_vanish D h_J (27 : I32) (19 : I32) hpiv_mn
    exact hstep_0
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (21 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (27 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (19 : I32) (by decide)
  · -- (28,20) reduces to pivot (2,10)
    have hpiv_mn : D (2 : I32) (10 : I32) = 0 := hpiv (2 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (4 : I32) (12 : I32) = 0 := by rw [ident_yU_green D h_oo]; exact hpiv_mn
    have hstep_1 : D (28 : I32) (20 : I32) = 0 := j_vanish D h_J (28 : I32) (20 : I32) hstep_0
    exact hstep_1
  · -- (28,21) reduces to pivot (3,10)
    have hpiv_mn : D (3 : I32) (10 : I32) = 0 := hpiv (3 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (5 : I32) (12 : I32) = 0 := by rw [ident_yU_green3 D h_oo]; exact hpiv_mn
    have hstep_1 : D (28 : I32) (21 : I32) = 0 := j_vanish D h_J (28 : I32) (21 : I32) hstep_0
    exact hstep_1
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (28 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (19 : I32) (by decide)
  · -- (29,20) reduces to pivot (2,11)
    have hpiv_mn : D (2 : I32) (11 : I32) = 0 := hpiv (2 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (4 : I32) (13 : I32) = 0 := by rw [ident_yU_green2 D h_oo]; exact hpiv_mn
    have hstep_1 : D (29 : I32) (20 : I32) = 0 := j_vanish D h_J (29 : I32) (20 : I32) hstep_0
    exact hstep_1
  · -- (29,21) reduces to pivot (3,11)
    have hpiv_mn : D (3 : I32) (11 : I32) = 0 := hpiv (3 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (5 : I32) (13 : I32) = 0 := by rw [ident_yU_green4 D h_oo]; exact hpiv_mn
    have hstep_1 : D (29 : I32) (21 : I32) = 0 := j_vanish D h_J (29 : I32) (21 : I32) hstep_0
    exact hstep_1
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (22 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (23 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (29 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (21 : I32) (by decide)
  · -- (30,22) reduces to pivot (2,10)
    have hpiv_mn : D (2 : I32) (10 : I32) = 0 := hpiv (2 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (6 : I32) (14 : I32) = 0 := by rw [ident_yU_blue D h_oo]; exact hpiv_mn
    have hstep_1 : D (30 : I32) (22 : I32) = 0 := j_vanish D h_J (30 : I32) (22 : I32) hstep_0
    exact hstep_1
  · -- (30,23) reduces to pivot (3,10)
    have hpiv_mn : D (3 : I32) (10 : I32) = 0 := hpiv (3 : Fin 32) (10 : Fin 32) (by decide)
    have hstep_0 : D (7 : I32) (14 : I32) = 0 := by rw [ident_yU_blue3 D h_oo]; exact hpiv_mn
    have hstep_1 : D (30 : I32) (23 : I32) = 0 := j_vanish D h_J (30 : I32) (23 : I32) hstep_0
    exact hstep_1
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (30 : I32) (31 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (0 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (1 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (2 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (3 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (4 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (5 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (6 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (7 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (8 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (9 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (10 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (11 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (12 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (13 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (14 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (15 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (16 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (17 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (18 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (19 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (20 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (21 : I32) (by decide)
  · -- (31,22) reduces to pivot (2,11)
    have hpiv_mn : D (2 : I32) (11 : I32) = 0 := hpiv (2 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (6 : I32) (15 : I32) = 0 := by rw [ident_yU_blue2 D h_oo]; exact hpiv_mn
    have hstep_1 : D (31 : I32) (22 : I32) = 0 := j_vanish D h_J (31 : I32) (22 : I32) hstep_0
    exact hstep_1
  · -- (31,23) reduces to pivot (3,11)
    have hpiv_mn : D (3 : I32) (11 : I32) = 0 := hpiv (3 : Fin 32) (11 : Fin 32) (by decide)
    have hstep_0 : D (7 : I32) (15 : I32) = 0 := by rw [ident_yU_blue4 D h_oo]; exact hpiv_mn
    have hstep_1 : D (31 : I32) (23 : I32) = 0 := j_vanish D h_J (31 : I32) (23 : I32) hstep_0
    exact hstep_1
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (24 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (25 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (26 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (27 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (28 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (29 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (30 : I32) (by decide)
  · exact D_off_support_zero D h_oo h_cf h_sa h_J h_gr (31 : I32) (31 : I32) (by decide)



end ThetLogos