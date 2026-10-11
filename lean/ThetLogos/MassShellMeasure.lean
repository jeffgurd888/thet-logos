import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import ThetLogos.PoincareAction

namespace ThetLogos

open MeasureTheory

/-!
# ThetLogos.MassShellMeasure — the Lorentz-invariant measure on the mass shell

Source: Rung 7, Prong 4 (2026-10-11) — mass-shell measure + one-particle rep,
Jeff's "push ACMD to the frontier of known Physics".

**What IS proved here (T1, zero sorrys):**
- `properOrtho` / `RestrictedLorentz` — the restricted (proper orthochronous)
  Lorentz group SO⁺(1,3) as a subgroup of `LorentzGroup`, with `Group` instance.
  This discharges the *restricted pin* priced in `PoincareAction.lean`: the
  nontrivial step is that orthochronous maps compose (via reverse
  Cauchy–Schwarz, already T1 in `WightmanAxioms.lean`).
- `restricted_preserves_shell` — restricted Lorentz maps preserve the full mass
  shell `{p : ⟪p,p⟫ = m², p⁰ > 0}` (m > 0), including the `p⁰ > 0` half.
- `massShellMeasure` — the invariant measure `d³p / (2E_p)` on `Hₘ⁺` as a
  Mathlib `Measure`, via pushforward of density-weighted Lebesgue measure on
  ℝ³ along the graph parametrization `u ↦ (E_u, u)`, with its integral formula.
- `spatialLift_preserves_measure` — invariance under spatial rotations (lifts
  of 3D linear isometries), via change of variables on ℝ³.

**What is PRICED (T5 window, exact statement):**
- `BoostInvariance_window` — invariance under boosts. The exact missing lemma
  is the 1D Jacobian identity for the boost action on the ℝ³ parametrization
  (see the PRICE docstring); everything around it (restricted subgroup, shell
  preservation, integral formula, rotation case) is T1.

Tier honesty: no 4D interacting QFT is claimed; no mass gap is claimed.
`satisfiesDestruction` untouched; no existing file modified.
-/

/-!
## The restricted (proper orthochronous) Lorentz group
-/

/-- The time-axis vector `e₀ = (1,0,0,0)`. -/
def timeVec : Minkowski := ![1, 0, 0, 0]

/-- `⟪e₀, p⟫ = p⁰`. -/
theorem minkowskiInner_timeVec_left (p : Minkowski) :
    minkowskiInner timeVec p = p 0 := by
  unfold minkowskiInner timeVec
  simp

/-- `⟪p, e₀⟫ = p⁰`. -/
theorem minkowskiInner_timeVec_right (p : Minkowski) :
    minkowskiInner p timeVec = p 0 := by
  unfold minkowskiInner timeVec
  simp

/-- `⟪e₀, e₀⟫ = 1`. -/
theorem minkowskiInner_timeVec_self : minkowskiInner timeVec timeVec = 1 := by
  unfold minkowskiInner timeVec
  simp

/-- `e₀` is in the forward light cone. -/
theorem timeVec_mem_forwardLightCone : timeVec ∈ forwardLightCone := by
  simp only [forwardLightCone, Set.mem_ofPred_eq]
  exact ⟨by rw [minkowskiInner_timeVec_self]; norm_num, by unfold timeVec; simp⟩

/-- Negation is Minkowski-linear on the left. -/
theorem minkowskiInner_neg_left (x y : Minkowski) :
    minkowskiInner (-x) y = -minkowskiInner x y := by
  unfold minkowskiInner
  simp [Pi.neg_apply]
  ring

/-- Negation is Minkowski-linear on the right. -/
theorem minkowskiInner_neg_right (x y : Minkowski) :
    minkowskiInner x (-y) = -minkowskiInner x y := by
  unfold minkowskiInner
  simp [Pi.neg_apply]
  ring

/-- Positive scaling is Minkowski-linear on the left. -/
theorem minkowskiInner_smul_left (c : ℝ) (x y : Minkowski) :
    minkowskiInner (c • x) y = c * minkowskiInner x y := by
  unfold minkowskiInner
  simp [Pi.smul_apply, smul_eq_mul]
  ring

/-- Positive scaling is Minkowski-linear on the right. -/
theorem minkowskiInner_smul_right (c : ℝ) (x y : Minkowski) :
    minkowskiInner x (c • y) = c * minkowskiInner x y := by
  unfold minkowskiInner
  simp [Pi.smul_apply, smul_eq_mul]
  ring

/-- A Lorentz map sends `e₀` into the forward light cone iff it is orthochronous. -/
theorem lorentz_timeVec_mem_cone_iff (Λ : LorentzGroup) :
    (Λ : LorentzGroup).toLin timeVec ∈ forwardLightCone ↔ 0 ≤ minkowskiInner ((Λ : LorentzGroup).toLin timeVec) ((Λ : LorentzGroup).toLin timeVec)
      ∧ 0 ≤ ((Λ : LorentzGroup).toLin timeVec) 0 := by
  simp only [forwardLightCone, Set.mem_ofPred_eq]

/-- **T1:** orthochronous = `e₀` maps to positive time component. -/
def IsOrthoChronous (Λ : LorentzGroup) : Prop := 0 < ((Λ : LorentzGroup).toLin timeVec) 0

/-- **T1:** proper = determinant one (as a unit). -/
def IsProper (Λ : LorentzGroup) : Prop := LinearEquiv.det Λ.toLin = 1

/-- Helper: determinant of a Lorentz product. -/
theorem lorentz_det_mul (a b : LorentzGroup) :
    LinearEquiv.det (a * b).toLin = LinearEquiv.det a.toLin * LinearEquiv.det b.toLin := by
  rw [LorentzGroup.mul_toLin, LinearEquiv.det_trans]

/-- Helper: determinant of a Lorentz inverse. -/
theorem lorentz_det_inv (a : LorentzGroup) :
    LinearEquiv.det a⁻¹.toLin = (LinearEquiv.det a.toLin)⁻¹ := by
  have h : LinearEquiv.det a⁻¹.toLin * LinearEquiv.det a.toLin = 1 := by
    rw [← lorentz_det_mul, lorentz_inv_mul_cancel, LorentzGroup.one_toLin]
    exact LinearEquiv.det_refl
  exact eq_inv_of_mul_eq_one_left h

/-- **T1:** the restricted (proper orthochronous) Lorentz group SO⁺(1,3) as a
    subgroup of `LorentzGroup`. The nontrivial step is closure of the
    orthochronous condition under composition, via reverse Cauchy–Schwarz
    (`minkowskiInner_nonneg_of_mem`, T1 in `WightmanAxioms.lean`). -/
def properOrtho : Subgroup LorentzGroup where
  carrier := {Λ | IsProper Λ ∧ IsOrthoChronous Λ}
  mul_mem' := by
    rintro a b ⟨hpa, hoa⟩ ⟨hpb, hob⟩
    refine ⟨?_, ?_⟩
    · -- det(ab) = det(a)det(b) = 1
      show IsProper (a * b)
      rw [IsProper] at hpa hpb ⊢
      rw [lorentz_det_mul, hpa, hpb, mul_one]
    · -- orthochronous composes: a(b(e₀)) has positive time component
      show IsOrthoChronous (a * b)
      show 0 < ((a * b).toLin timeVec) 0
      rw [LorentzGroup.mul_toLin, LinearEquiv.trans_apply]
      -- x := b(e₀) is future-timelike; z := a(x); suppose z⁰ ≤ 0
      set x := b.toLin timeVec with hx
      have hx0 : 0 < x 0 := hob
      have hxx : minkowskiInner x x = 1 := by
        rw [hx, b.preserves timeVec timeVec, minkowskiInner_timeVec_self]
      set z := a.toLin x with hz
      have hzz : minkowskiInner z z = 1 := by rw [hz, a.preserves x x, hxx]
      by_contra hle
      push Not at hle
      -- z⁰ ≠ 0 since z is timelike
      have hz0ne : z 0 ≠ 0 := by
        intro hz0
        have : (0:ℝ) < minkowskiInner z z := by rw [hzz]; norm_num
        unfold minkowskiInner at this
        rw [hz0] at this
        nlinarith [sq_nonneg (z 1), sq_nonneg (z 2), sq_nonneg (z 3)]
      have hz0neg : z 0 < 0 := lt_of_le_of_ne hle hz0ne
      -- y := a(e₀) and w := -z are both in the forward light cone
      have hy : a.toLin timeVec ∈ forwardLightCone := by
        simp only [forwardLightCone, Set.mem_ofPred_eq]
        exact ⟨by rw [a.preserves timeVec timeVec, minkowskiInner_timeVec_self]; norm_num, le_of_lt hoa⟩
      have hw : -z ∈ forwardLightCone := by
        simp only [forwardLightCone, Set.mem_ofPred_eq]
        refine ⟨by rw [minkowskiInner_neg_left, minkowskiInner_neg_right, hzz]; norm_num, ?_⟩
        simp [Pi.neg_apply]
        linarith
      have hcs := minkowskiInner_nonneg_of_mem hy hw
      -- but ⟪y, -z⟫ = -x⁰ < 0
      have hcomp : minkowskiInner (a.toLin timeVec) (-z) = -(x 0) := by
        rw [minkowskiInner_neg_right, hz,
          a.preserves timeVec x, minkowskiInner_timeVec_left]
      rw [hcomp] at hcs
      linarith
  one_mem' := by
    refine ⟨?_, ?_⟩
    · show IsProper 1
      rw [IsProper, LorentzGroup.one_toLin]
      exact LinearEquiv.det_refl
    · show IsOrthoChronous 1
      show 0 < ((1 : LorentzGroup).toLin timeVec) 0
      rw [LorentzGroup.one_toLin]
      show 0 < (LinearEquiv.refl ℝ Minkowski timeVec) 0
      unfold timeVec
      simp
  inv_mem' := by
    rintro a ⟨hpa, hoa⟩
    refine ⟨?_, ?_⟩
    · show IsProper a⁻¹
      rw [IsProper] at hpa ⊢
      rw [lorentz_det_inv, hpa, inv_one]
    · -- inverse of orthochronous is orthochronous
      show IsOrthoChronous a⁻¹
      show 0 < (a⁻¹.toLin timeVec) 0
      rw [LorentzGroup.inv_toLin]
      have hyy : minkowskiInner (a.toLin.symm timeVec) (a.toLin.symm timeVec) = 1 := by
        have h := a.preserves (a.toLin.symm timeVec) (a.toLin.symm timeVec)
        rw [LinearEquiv.apply_symm_apply, minkowskiInner_timeVec_self] at h
        exact h.symm
      by_contra hle
      push Not at hle
      have hy0ne : (a.toLin.symm timeVec) 0 ≠ 0 := by
        intro hy0
        have : (0:ℝ) < minkowskiInner (a.toLin.symm timeVec) (a.toLin.symm timeVec) := by
          rw [hyy]; norm_num
        unfold minkowskiInner at this
        rw [hy0] at this
        nlinarith [sq_nonneg ((a.toLin.symm timeVec) 1),
                   sq_nonneg ((a.toLin.symm timeVec) 2),
                   sq_nonneg ((a.toLin.symm timeVec) 3)]
      have hy0neg : (a.toLin.symm timeVec) 0 < 0 := lt_of_le_of_ne hle hy0ne
      -- ⟪e₀, y⟫ = y⁰ < 0, but = ⟪a(e₀), e₀⟫ = (a(e₀))⁰ > 0
      have hcontra : minkowskiInner timeVec (a.toLin.symm timeVec) = (a.toLin timeVec) 0 := by
        have h1 : minkowskiInner timeVec (a.toLin.symm timeVec)
            = minkowskiInner (a.toLin timeVec) (a.toLin (a.toLin.symm timeVec)) :=
          (a.preserves timeVec (a.toLin.symm timeVec)).symm
        rw [h1, LinearEquiv.apply_symm_apply, minkowskiInner_timeVec_right]
      rw [minkowskiInner_timeVec_left] at hcontra
      have hoa' : 0 < (a.toLin timeVec) 0 := hoa
      linarith

/-- The restricted Lorentz group SO⁺(1,3), as a type. -/
abbrev RestrictedLorentz := properOrtho

/-- **T1:** restricted Lorentz maps preserve the full mass shell
    `{p : ⟪p,p⟫ = m², p⁰ > 0}` (m > 0) — including the `p⁰ > 0` half that the
    full O(1,3) does not preserve. This discharges the restricted pin for the
    shell action. -/
theorem restricted_preserves_shell (Λ : RestrictedLorentz) (p : Minkowski) (m : ℝ)
    (hm : 0 < m) (h : p ∈ massShell m) : (Λ : LorentzGroup).toLin p ∈ massShell m := by
  obtain ⟨heq, hp0⟩ := h
  have hΛ := Λ.property
  obtain ⟨hprop, hortho⟩ := hΛ
  refine ⟨lorentz_preserves_massShell_eq (Λ : LorentzGroup) p m heq, ?_⟩
  -- p⁰ > 0 half: suppose (Λp)⁰ ≤ 0, contradict reverse Cauchy–Schwarz
  show 0 < (((Λ : LorentzGroup).toLin) p) 0
  by_contra hle
  push Not at hle
  set z := ((Λ : LorentzGroup).toLin) p with hz
  have hzz : minkowskiInner z z = m ^ 2 := by
    rw [hz]; exact lorentz_preserves_massShell_eq (Λ : LorentzGroup) p m heq
  have hz0ne : z 0 ≠ 0 := by
    intro hz0
    have : (0:ℝ) < minkowskiInner z z := by rw [hzz]; positivity
    unfold minkowskiInner at this
    rw [hz0] at this
    nlinarith [sq_nonneg (z 1), sq_nonneg (z 2), sq_nonneg (z 3)]
  have hz0neg : z 0 < 0 := lt_of_le_of_ne hle hz0ne
  -- w := (-1/m) • z is future-timelike; y := Λ(e₀) is too
  have hy : ((Λ : LorentzGroup).toLin) timeVec ∈ forwardLightCone := by
    simp only [forwardLightCone, Set.mem_ofPred_eq]
    exact ⟨by rw [((Λ : LorentzGroup)).preserves timeVec timeVec, minkowskiInner_timeVec_self]; norm_num,
      le_of_lt hortho⟩
  have hsmul0 : ((-(1/m)) • z) 0 = (-(1/m)) * z 0 := by
    simp [Pi.smul_apply, smul_eq_mul]
  have hneg : (-(1/m) : ℝ) < 0 := by
    have hpos : (0:ℝ) < 1/m := by positivity
    linarith
  have hpos0 : (0:ℝ) < (-(1/m)) * z 0 := mul_pos_of_neg_of_neg hneg hz0neg
  have hw : (-(1/m)) • z ∈ forwardLightCone := by
    simp only [forwardLightCone, Set.mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · have e1 : minkowskiInner ((-(1/m)) • z) ((-(1/m)) • z)
          = (-(1/m)) ^ 2 * minkowskiInner z z := by
        unfold minkowskiInner
        simp [Pi.smul_apply, smul_eq_mul]
        ring
      have e2 : (-(1/m) : ℝ) * m = -1 := by
        rw [neg_mul, one_div, inv_mul_cancel₀ (ne_of_gt hm)]
      have h1 : (-(1/m)) ^ 2 * m ^ 2 = 1 := by
        rw [← mul_pow, e2]
        norm_num
      rw [e1, hzz]
      linarith [h1]
    · rw [hsmul0]
      linarith [hpos0]
  have hcs := minkowskiInner_nonneg_of_mem hy hw
  -- ⟪y, w⟫ = (-1/m) p⁰ < 0
  have hcomp : minkowskiInner (((Λ : LorentzGroup)).toLin timeVec) ((-(1/m)) • z)
      = (-(1/m)) * p 0 := by
    rw [minkowskiInner_smul_right, hz,
      ((Λ : LorentzGroup)).preserves timeVec p, minkowskiInner_timeVec_left]
  rw [hcomp] at hcs
  have : (-(1/m)) * p 0 < 0 := by
    apply mul_neg_of_neg_of_pos
    · have : (0:ℝ) < 1/m := by positivity
      linarith
    · exact hp0
  linarith

end ThetLogos

namespace ThetLogos

open MeasureTheory
open scoped ENNReal
open scoped RealInnerProductSpace

/-!
## The invariant measure d³p/(2E_p)
-/

/-- Relativistic energy `E_u = √(m² + ‖u‖²)` of a spatial momentum `u ∈ ℝ³`. -/
noncomputable def shellEnergy (m : ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Real.sqrt (m ^ 2 + ‖u‖ ^ 2)

/-- The energy is positive for `m > 0`. -/
theorem shellEnergy_pos (hm : 0 < m) (u : EuclideanSpace ℝ (Fin 3)) :
    0 < shellEnergy m u := by
  unfold shellEnergy
  apply Real.sqrt_pos.mpr
  have h1 : (0:ℝ) < m ^ 2 := by positivity
  have h2 : (0:ℝ) ≤ ‖u‖ ^ 2 := sq_nonneg _
  linarith

/-- `E_u² = m² + ‖u‖²`. -/
theorem shellEnergy_sq (m : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    (shellEnergy m u) ^ 2 = m ^ 2 + ‖u‖ ^ 2 := by
  unfold shellEnergy
  apply Real.sq_sqrt
  positivity

/-- The energy is measurable in the spatial momentum. -/
theorem measurable_shellEnergy (m : ℝ) :
    Measurable (shellEnergy m) :=
  Real.continuous_sqrt.measurable.comp
    (measurable_const.add (measurable_norm.pow_const 2))

/-- The graph parametrization `ℝ³ → Hₘ⁺`, `u ↦ (E_u, u)`. -/
noncomputable def shellParam (m : ℝ) (u : EuclideanSpace ℝ (Fin 3)) : Minkowski :=
  ![shellEnergy m u, u 0, u 1, u 2]

theorem shellParam_comp0 (m : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    (shellParam m u) 0 = shellEnergy m u := by
  unfold shellParam; simp

theorem shellParam_comp1 (m : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    (shellParam m u) 1 = u 0 := by
  unfold shellParam; simp

theorem shellParam_comp2 (m : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    (shellParam m u) 2 = u 1 := by
  unfold shellParam; simp

theorem shellParam_comp3 (m : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    (shellParam m u) 3 = u 2 := by
  unfold shellParam; simp

/-- The parametrization is measurable. -/
theorem measurable_shellParam (m : ℝ) : Measurable (shellParam m) := by
  have h0 : Measurable (fun u : EuclideanSpace ℝ (Fin 3) => (shellParam m u) 0) := by
    simp only [shellParam_comp0]; exact measurable_shellEnergy m
  have h1 : Measurable (fun u : EuclideanSpace ℝ (Fin 3) => (shellParam m u) 1) := by
    simp only [shellParam_comp1]; exact Continuous.measurable (PiLp.continuous_apply 2 _ (0 : Fin 3))
  have h2 : Measurable (fun u : EuclideanSpace ℝ (Fin 3) => (shellParam m u) 2) := by
    simp only [shellParam_comp2]; exact Continuous.measurable (PiLp.continuous_apply 2 _ (1 : Fin 3))
  have h3 : Measurable (fun u : EuclideanSpace ℝ (Fin 3) => (shellParam m u) 3) := by
    simp only [shellParam_comp3]; exact Continuous.measurable (PiLp.continuous_apply 2 _ (2 : Fin 3))
  apply Measurable.of_eval
  intro i
  fin_cases i
  · dsimp only; rw [Fin.mk_zero]; exact h0
  · dsimp only; rw [show ((⟨1, by omega⟩ : Fin 4)) = 1 from rfl]; exact h1
  · dsimp only; rw [show ((⟨2, by omega⟩ : Fin 4)) = 2 from rfl]; exact h2
  · dsimp only; rw [show ((⟨3, by omega⟩ : Fin 4)) = 3 from rfl]; exact h3

/-- **T1:** the graph parametrization lands on the mass shell. -/
theorem shellParam_mem (m : ℝ) (hm : 0 < m) (u : EuclideanSpace ℝ (Fin 3)) :
    shellParam m u ∈ massShell m := by
  have hE := shellEnergy_sq m u
  have hnorm : ‖u‖ ^ 2 = (u 0) ^ 2 + (u 1) ^ 2 + (u 2) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [Real.norm_eq_abs, sq_abs]
  have hEE : (shellEnergy m u) * (shellEnergy m u) = (shellEnergy m u) ^ 2 := by ring
  simp only [massShell, Set.mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · -- ⟪p,p⟫ = E² − ‖u‖² = m²
    unfold minkowskiInner
    rw [shellParam_comp0, shellParam_comp1, shellParam_comp2, shellParam_comp3,
      hEE, hE, hnorm]
    ring
  · rw [shellParam_comp0]
    exact shellEnergy_pos hm u

/-- The mass-shell measure `d³p/(2E_p)` for `m > 0`: pushforward of the
    density-weighted Lebesgue measure on ℝ³ along the graph parametrization.
    This is the standard Lorentz-invariant measure on the mass shell. -/
noncomputable def massShellMeasure (m : ℝ) (hm : 0 < m) : Measure (massShell m) :=
  Measure.map (fun u => (⟨shellParam m u, shellParam_mem m hm u⟩ : massShell m))
    (Measure.withDensity volume
      (fun u : EuclideanSpace ℝ (Fin 3) => (ENNReal.ofReal (2 * shellEnergy m u))⁻¹))

/-- The density `1/(2E_u)` is measurable. -/
theorem measurable_shellDensity (m : ℝ) :
    Measurable (fun u : EuclideanSpace ℝ (Fin 3) => (ENNReal.ofReal (2 * shellEnergy m u))⁻¹) := by
  apply Measurable.inv
  apply Measurable.ennreal_ofReal
  exact measurable_const.mul (measurable_shellEnergy m)

/-- The subtype-valued parametrization is measurable. -/
theorem measurable_shellParam_subtype (m : ℝ) (hm : 0 < m) :
    Measurable (fun u => (⟨shellParam m u, shellParam_mem m hm u⟩ : massShell m)) :=
  (measurable_shellParam m).subtype_mk (h := fun u => shellParam_mem m hm u)

/-- **T1 (integral formula):** integration against `d³p/(2E_p)` is integration
    of `f(E_u, u)/(2E_u)` against Lebesgue measure on ℝ³. -/
theorem lintegral_massShellMeasure (m : ℝ) (hm : 0 < m)
    (f : massShell m → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ p, f p ∂(massShellMeasure m hm)
      = ∫⁻ u, (ENNReal.ofReal (2 * shellEnergy m u))⁻¹
          * f ⟨shellParam m u, shellParam_mem m hm u⟩ ∂volume := by
  unfold massShellMeasure
  rw [MeasureTheory.lintegral_map hf (measurable_shellParam_subtype m hm)]
  have h := MeasureTheory.lintegral_withDensity_eq_lintegral_mul (μ := volume)
    (f := fun u : EuclideanSpace ℝ (Fin 3) => (ENNReal.ofReal (2 * shellEnergy m u))⁻¹)
    (g := fun u : EuclideanSpace ℝ (Fin 3) => f ⟨shellParam m u, shellParam_mem m hm u⟩)
    (measurable_shellDensity m) (hf.comp (measurable_shellParam_subtype m hm))
  rw [h]
  rfl

/-!
## Rotation invariance of the mass-shell measure
-/

/-- The spatial part as a linear map `ℝ^{1,3} →ₗ[ℝ] ℝ³`. -/
noncomputable def spatialPartLin : Minkowski →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toLinearMap.comp
    (LinearMap.pi fun (j : Fin 3) => LinearMap.proj j.succ)

theorem spatialPartLin_apply (p : Minkowski) (j : Fin 3) :
    spatialPartLin p j = p j.succ := by
  simp [spatialPartLin]

/-- The Euclidean inner product as a sum of coordinate products. -/
theorem euclidean_inner_sum (u v : EuclideanSpace ℝ (Fin 3)) :
    ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  have hsum : ⟪u, v⟫ = ∑ j : Fin 3, ⟪u j, v j⟫ := rfl
  rw [hsum, Fin.sum_univ_three]
  simp [RCLike.inner_apply, mul_comm]

/-- Bridge: the Minkowski form is time part minus Euclidean inner of spatial parts. -/
theorem minkowskiInner_spatial (p q : Minkowski) :
    minkowskiInner p q = p 0 * q 0 - ⟪spatialPartLin p, spatialPartLin q⟫ := by
  rw [euclidean_inner_sum]
  unfold minkowskiInner
  simp only [spatialPartLin_apply]
  have e1 : Fin.succ (0 : Fin 3) = (1 : Fin 4) := rfl
  have e2 : Fin.succ (1 : Fin 3) = (2 : Fin 4) := rfl
  have e3 : Fin.succ (2 : Fin 3) = (3 : Fin 4) := rfl
  rw [e1, e2, e3]
  ring

/-- The 1+3 splitting `ℝ^{1,3} ≃ₗ[ℝ] ℝ × ℝ³`. -/
noncomputable def finFourEquiv : Minkowski ≃ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin 3)) where
  toFun p := (p 0, spatialPartLin p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun pr := ![pr.1, pr.2 0, pr.2 1, pr.2 2]
  left_inv p := by
    show ![p 0, spatialPartLin p 0, spatialPartLin p 1, spatialPartLin p 2] = p
    rw [spatialPartLin_apply, spatialPartLin_apply, spatialPartLin_apply]
    funext i
    fin_cases i <;> simp
  right_inv := by
    rintro ⟨t, u⟩
    show ((![t, u 0, u 1, u 2]) 0, spatialPartLin ![t, u 0, u 1, u 2]) = (t, u)
    have hsp : spatialPartLin ![t, u 0, u 1, u 2] = u := by
      ext j
      rw [spatialPartLin_apply]
      fin_cases j <;> simp
    simp [hsp]

theorem finFourEquiv_fst (p : Minkowski) : (finFourEquiv p).1 = p 0 := rfl
theorem finFourEquiv_snd (p : Minkowski) : (finFourEquiv p).2 = spatialPartLin p := rfl

/-- A spatial linear isometry acting on `ℝ^{1,3}` (fixing the time axis). -/
noncomputable def spatialLiftLin
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    Minkowski ≃ₗ[ℝ] Minkowski :=
  finFourEquiv.trans
    (((LinearEquiv.refl ℝ ℝ).prodCongr R.toLinearEquiv).trans finFourEquiv.symm)

/-- The lift fixes the time component and rotates the spatial part. -/
theorem spatialLiftLin_apply
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (p : Minkowski) :
    finFourEquiv (spatialLiftLin R p) = (p 0, R (spatialPartLin p)) := by
  unfold spatialLiftLin
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.prodCongr_apply]
  rfl

/-- **T1:** the spatial lift preserves the Minkowski form. -/
theorem spatialLift_preserves
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (p q : Minkowski) :
    minkowskiInner (spatialLiftLin R p) (spatialLiftLin R q) = minkowskiInner p q := by
  have h1 := spatialLiftLin_apply R p
  have h2 := spatialLiftLin_apply R q
  have hp0 : (spatialLiftLin R p) 0 = p 0 := by
    have h := congrArg Prod.fst h1
    rwa [finFourEquiv_fst] at h
  have hq0 : (spatialLiftLin R q) 0 = q 0 := by
    have h := congrArg Prod.fst h2
    rwa [finFourEquiv_fst] at h
  have hsp : spatialPartLin (spatialLiftLin R p) = R (spatialPartLin p) := by
    have h := congrArg Prod.snd h1
    rwa [finFourEquiv_snd] at h
  have hsq : spatialPartLin (spatialLiftLin R q) = R (spatialPartLin q) := by
    have h := congrArg Prod.snd h2
    rwa [finFourEquiv_snd] at h
  rw [minkowskiInner_spatial, minkowskiInner_spatial, hp0, hq0, hsp, hsq,
    LinearIsometryEquiv.inner_map_map]

/-- **T1:** the spatial lift as a Lorentz group element (fixes the time axis). -/
noncomputable def spatialLift
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    LorentzGroup where
  toLin := spatialLiftLin R
  preserves := spatialLift_preserves R

/-- The energy is rotation-invariant. -/
theorem shellEnergy_rot (m : ℝ)
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (u : EuclideanSpace ℝ (Fin 3)) :
    shellEnergy m (R u) = shellEnergy m u := by
  unfold shellEnergy
  rw [R.norm_map]

/-- The spatial part of the parametrization is the identity. -/
theorem spatialPartLin_shellParam (m : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    spatialPartLin (shellParam m u) = u := by
  ext j
  rw [spatialPartLin_apply]
  fin_cases j <;> rfl

/-- **T1:** the lift acts on the parametrization by rotating the spatial momentum. -/
theorem spatialLiftLin_shellParam (m : ℝ)
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (u : EuclideanSpace ℝ (Fin 3)) :
    spatialLiftLin R (shellParam m u) = shellParam m (R u) := by
  have h1 := spatialLiftLin_apply R (shellParam m u)
  rw [spatialPartLin_shellParam] at h1
  have h2 : spatialLiftLin R (shellParam m u)
      = finFourEquiv.symm (shellEnergy m u, R u) := by
    have h3 := congrArg finFourEquiv.symm h1
    rwa [LinearEquiv.symm_apply_apply] at h3
  rw [h2]
  have h4 : finFourEquiv.symm (shellEnergy m u, R u)
      = ![shellEnergy m u, (R u) 0, (R u) 1, (R u) 2] := rfl
  rw [h4]
  show ![shellEnergy m u, (R u) 0, (R u) 1, (R u) 2]
     = ![shellEnergy m (R u), (R u) 0, (R u) 1, (R u) 2]
  rw [shellEnergy_rot m R u]

/-- **T1:** the spatial lift preserves the mass shell (it fixes `p⁰`). -/
theorem spatialLift_mem_shell
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (m : ℝ) (p : Minkowski) (h : p ∈ massShell m) :
    (spatialLift R).toLin p ∈ massShell m := by
  obtain ⟨heq, hp0⟩ := h
  have hp0' : ((spatialLift R).toLin p) 0 = p 0 := by
    have h1 := spatialLiftLin_apply R p
    have h := congrArg Prod.fst h1
    rwa [finFourEquiv_fst] at h
  refine ⟨?_, ?_⟩
  · exact ((spatialLift R).preserves p p).trans heq
  · rw [hp0']; exact hp0

/-- The shell action of a spatial rotation. -/
noncomputable def shellActLift
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (m : ℝ) : massShell m → massShell m :=
  fun p => ⟨(spatialLift R).toLin p.val, spatialLift_mem_shell R m p.val p.property⟩

theorem measurable_shellActLift
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (m : ℝ) : Measurable (shellActLift R m) := by
  unfold shellActLift
  apply Measurable.subtype_mk
  exact (LinearMap.continuous_of_finiteDimensional
    (spatialLift R).toLin.toLinearMap).measurable.comp measurable_subtype_coe

/-- The shell action on the parametrization. -/
theorem shellActLift_param
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (m : ℝ) (hm : 0 < m) (u : EuclideanSpace ℝ (Fin 3)) :
    shellActLift R m ⟨shellParam m u, shellParam_mem m hm u⟩
      = ⟨shellParam m (R u), shellParam_mem m hm (R u)⟩ := by
  unfold shellActLift
  have h : (spatialLift R).toLin (shellParam m u) = shellParam m (R u) :=
    spatialLiftLin_shellParam m R u
  exact Subtype.ext h

/-- The energy is invariant under the inverse rotation too. -/
theorem shellEnergy_rot_symm (m : ℝ)
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (u : EuclideanSpace ℝ (Fin 3)) :
    shellEnergy m (R.symm u) = shellEnergy m u := by
  unfold shellEnergy
  rw [R.symm.norm_map]

/-- Change-of-variables identity for the rotation-invariant density. -/
theorem w_integral_rot (m : ℝ)
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (f : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ u, (ENNReal.ofReal (2 * shellEnergy m u))⁻¹ * f (R u) ∂volume
    = ∫⁻ u, (ENNReal.ofReal (2 * shellEnergy m u))⁻¹ * f u ∂volume := by
  have hR := LinearIsometryEquiv.measurePreserving R
  have hF : Measurable (fun v : EuclideanSpace ℝ (Fin 3) =>
      (ENNReal.ofReal (2 * shellEnergy m (R.symm v)))⁻¹ * f v) :=
    (Measurable.inv (Measurable.ennreal_ofReal
      (measurable_const.mul ((measurable_shellEnergy m).comp R.symm.continuous.measurable)))).mul hf
  have hchange := hR.lintegral_comp hF
  calc ∫⁻ u, (ENNReal.ofReal (2 * shellEnergy m u))⁻¹ * f (R u) ∂volume
      = ∫⁻ a, (fun v : EuclideanSpace ℝ (Fin 3) =>
          (ENNReal.ofReal (2 * shellEnergy m (R.symm v)))⁻¹ * f v) (R a) ∂volume := by
        apply lintegral_congr_ae
        filter_upwards with a
        rw [R.symm_apply_apply]
    _ = ∫⁻ b, (fun v : EuclideanSpace ℝ (Fin 3) =>
          (ENNReal.ofReal (2 * shellEnergy m (R.symm v)))⁻¹ * f v) b ∂volume := hchange
    _ = ∫⁻ u, (ENNReal.ofReal (2 * shellEnergy m u))⁻¹ * f u ∂volume := by
        apply lintegral_congr_ae
        filter_upwards with v
        rw [shellEnergy_rot_symm m R v]

/-- **T1:** rotation invariance of the density-weighted measure on ℝ³. -/
theorem measure_map_rot_density (m : ℝ)
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    Measure.map R (Measure.withDensity volume
      (fun u : EuclideanSpace ℝ (Fin 3) => (ENNReal.ofReal (2 * shellEnergy m u))⁻¹))
    = Measure.withDensity volume
      (fun u : EuclideanSpace ℝ (Fin 3) => (ENNReal.ofReal (2 * shellEnergy m u))⁻¹) := by
  apply Measure.ext
  intro s hs
  have hf_ind : Measurable (s.indicator 1 : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞) :=
    (measurable_const (a := (1 : ℝ≥0∞))).indicator hs
  have hg : Measurable (fun a : EuclideanSpace ℝ (Fin 3) => s.indicator 1 (R a)) :=
    hf_ind.comp R.continuous.measurable
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs,
    MeasureTheory.lintegral_map hf_ind R.continuous.measurable]
  have h1 : ∫⁻ a, s.indicator 1 (R a)
      ∂(Measure.withDensity volume fun u => (ENNReal.ofReal (2 * shellEnergy m u))⁻¹)
      = ∫⁻ u, (ENNReal.ofReal (2 * shellEnergy m u))⁻¹ * s.indicator 1 (R u) ∂volume :=
    MeasureTheory.lintegral_withDensity_eq_lintegral_mul volume (measurable_shellDensity m) hg
  have h2 : ∫⁻ a, s.indicator 1 a
      ∂(Measure.withDensity volume fun u => (ENNReal.ofReal (2 * shellEnergy m u))⁻¹)
      = ∫⁻ u, (ENNReal.ofReal (2 * shellEnergy m u))⁻¹ * s.indicator 1 u ∂volume :=
    MeasureTheory.lintegral_withDensity_eq_lintegral_mul volume (measurable_shellDensity m) hf_ind
  rw [h1, h2]
  exact w_integral_rot m R _ hf_ind

/-- **T1:** the mass-shell measure `d³p/(2E_p)` is invariant under spatial
    rotations (lifts of 3D linear isometries). -/
theorem spatialLift_preserves_measure
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (m : ℝ) (hm : 0 < m) :
    Measure.map (shellActLift R m) (massShellMeasure m hm)
      = massShellMeasure m hm := by
  have hS := measurable_shellActLift R m
  have hparam := measurable_shellParam_subtype m hm
  have hR := R.continuous.measurable
  have hcomp : (shellActLift R m)
        ∘ (fun u => (⟨shellParam m u, shellParam_mem m hm u⟩ : massShell m))
      = (fun u => (⟨shellParam m u, shellParam_mem m hm u⟩ : massShell m)) ∘ R := by
    funext u
    exact shellActLift_param R m hm u
  unfold massShellMeasure
  rw [MeasureTheory.Measure.map_map hS hparam, hcomp,
    ← MeasureTheory.Measure.map_map hparam hR,
    measure_map_rot_density m R]

/-!
## T5 window: boost invariance (exact price)
-/

/-- **T5 window:** invariance of the mass-shell measure under the full
    restricted Lorentz group (boosts included).

    Exact statement: for `Λ : RestrictedLorentz`, the shell action is
    measure-preserving for `massShellMeasure m hm`.

    PRICE — the exact missing lemma. Write a boost along the `x¹`-axis with
    rapidity parameter `β ∈ (-1, 1)`, `γ = (1-β²)^{-1/2}`, as
    `B(t,x,y,z) = (γt-βγx, -βγt+γx, y, z)`. On the ℝ³ parametrization this
    induces `Φ(u₁,u₂,u₃) = (γu₁-βγE_u, u₂, u₃)` with `E_u = √(m²+‖u‖²)`.
    The missing computation is the 1D Jacobian identity, for fixed `(u₂,u₃)`:
    the map `φ(u₁) = γu₁ - βγ√(m²+u₁²+u₂²+u₃²)` is a `C¹` diffeomorphism
    `ℝ → ℝ` with `|φ'(u₁)| = E'_{φ(u₁)}/E_u` (where `E'` is the energy of the
    image), so that 1D change of variables (`MeasureTheory` integral image
    formula) cancels the density: `w(u)/|φ'(u₁)| = w(φ(u₁),u₂,u₃)` with
    `w = 1/(2E)`. Tonelli on `(u₂,u₃)` then gives invariance under `B`.
    Rotations/reflections (the `spatialLift` case) are T1 above
    (`spatialLift_preserves_measure`); boosts are generated by the `x¹`-boost
    and rotations, so this Jacobian identity is the *entire* remaining gap
    for full restricted-Lorentz invariance. What would discharge it: the 1D
    `C¹` change-of-variables computation (established analysis; only the
    formalization is missing). -/
def BoostInvariance_window (m : ℝ) (hm : 0 < m) : Prop :=
  ∀ Λ : RestrictedLorentz,
    MeasurePreserving (fun p : massShell m =>
      (⟨(Λ : LorentzGroup).toLin p.val,
        restricted_preserves_shell Λ p.val m hm p.property⟩ : massShell m))
      (massShellMeasure m hm) (massShellMeasure m hm)

/-!
## The restricted Poincaré group and the one-particle representation
-/

/-- The restricted Poincaré group: translations ⋊ (restricted Lorentz).
    Mirrors `PoincareGroup` with `RestrictedLorentz` in place of `LorentzGroup`. -/
structure RPoincare where
  trans : Minkowski
  lor : RestrictedLorentz

@[ext]
theorem RPoincare.ext {a b : RPoincare}
    (ht : a.trans = b.trans) (hl : a.lor = b.lor) : a = b := by
  obtain ⟨ta, la⟩ := a
  obtain ⟨tb, lb⟩ := b
  have ht' : ta = tb := ht
  have hl' : la = lb := hl
  subst ht'
  subst hl'
  rfl

instance : Mul RPoincare where
  mul g₁ g₂ := ⟨g₁.trans + (g₁.lor : LorentzGroup).toLin g₂.trans, g₁.lor * g₂.lor⟩

instance : One RPoincare := ⟨⟨0, 1⟩⟩

instance : Inv RPoincare where
  inv g := ⟨-(g.lor : LorentzGroup).toLin.symm g.trans, g.lor⁻¹⟩

@[simp] theorem RPoincare.mul_trans (g₁ g₂ : RPoincare) :
    (g₁ * g₂).trans = g₁.trans + (g₁.lor : LorentzGroup).toLin g₂.trans := rfl

@[simp] theorem RPoincare.mul_lor (g₁ g₂ : RPoincare) :
    (g₁ * g₂).lor = g₁.lor * g₂.lor := rfl

@[simp] theorem RPoincare.one_trans : (1 : RPoincare).trans = 0 := rfl
@[simp] theorem RPoincare.one_lor : (1 : RPoincare).lor = 1 := rfl

@[simp] theorem RPoincare.inv_lor (g : RPoincare) :
    g⁻¹.lor = g.lor⁻¹ := rfl

@[simp] theorem RPoincare.inv_trans (g : RPoincare) :
    g⁻¹.trans = -(g.lor : LorentzGroup).toLin.symm g.trans := rfl

/-- **T1:** the restricted Poincaré multiplication is associative. -/
theorem rpoincare_mul_assoc (a b c : RPoincare) :
    (a * b) * c = a * (b * c) := by
  refine RPoincare.ext ?_ ?_
  · simp only [RPoincare.mul_trans, RPoincare.mul_lor]
    have h : ((a.lor * b.lor : RestrictedLorentz) : LorentzGroup).toLin
        = (b.lor : LorentzGroup).toLin.trans (a.lor : LorentzGroup).toLin := by
      have := LorentzGroup.mul_toLin (a.lor : LorentzGroup) (b.lor : LorentzGroup)
      -- ((a.lor * b.lor : RestrictedLorentz) : LorentzGroup) = (a.lor : LorentzGroup) * (b.lor : LorentzGroup)
      have hcoe : ((a.lor * b.lor : RestrictedLorentz) : LorentzGroup)
          = (a.lor : LorentzGroup) * (b.lor : LorentzGroup) := rfl
      rw [hcoe, this]
    rw [h, LinearEquiv.trans_apply, map_add]
    exact add_assoc _ _ _
  · simp only [RPoincare.mul_lor]
    -- associativity in RestrictedLorentz (subgroup of a group)
    exact mul_assoc _ _ _

/-- **T1:** the identity acts trivially. -/
theorem rpoincare_one_mul (a : RPoincare) : 1 * a = a := by
  refine RPoincare.ext ?_ ?_
  · simp only [RPoincare.mul_trans, RPoincare.one_trans, RPoincare.one_lor]
    have h1 : ((1 : RestrictedLorentz) : LorentzGroup) = 1 := rfl
    rw [h1, LorentzGroup.one_toLin, LinearEquiv.refl_apply, zero_add]
  · simp only [RPoincare.mul_lor, RPoincare.one_lor, one_mul]

/-- **T1:** inverses cancel. -/
theorem rpoincare_inv_mul_cancel (a : RPoincare) : a⁻¹ * a = 1 := by
  refine RPoincare.ext ?_ ?_
  · simp only [RPoincare.mul_trans, RPoincare.inv_trans, RPoincare.inv_lor, RPoincare.one_trans]
    have h1 : ((a.lor⁻¹ : RestrictedLorentz) : LorentzGroup).toLin
        = (a.lor : LorentzGroup).toLin.symm := by
      have hcoe : ((a.lor⁻¹ : RestrictedLorentz) : LorentzGroup)
          = (a.lor : LorentzGroup)⁻¹ := rfl
      rw [hcoe, LorentzGroup.inv_toLin]
    rw [h1, neg_add_cancel]
  · simp only [RPoincare.mul_lor, RPoincare.inv_lor, RPoincare.one_lor, inv_mul_cancel]

/-- **T1:** the restricted Poincaré group is a group. -/
instance : Group RPoincare :=
  Group.ofLeftAxioms rpoincare_mul_assoc rpoincare_one_mul rpoincare_inv_mul_cancel

/-- The shell action of a restricted Lorentz element. -/
noncomputable def shellActR (Λ : RestrictedLorentz) (m : ℝ) (hm : 0 < m) :
    massShell m → massShell m :=
  fun p => ⟨(Λ : LorentzGroup).toLin p.val,
    restricted_preserves_shell Λ p.val m hm p.property⟩

/-- The translation phase `e^{ia·p}` (Minkowski inner product in the exponent). -/
noncomputable def phase (a : Minkowski) (p : massShell m) : ℂ :=
  Complex.exp (Complex.I * (minkowskiInner a p.val : ℂ))

/-- The phase has modulus 1. -/
theorem phase_norm (a : Minkowski) (p : massShell m) : ‖phase a p‖ = 1 := by
  unfold phase
  rw [Complex.norm_exp]
  have h : (Complex.I * (minkowskiInner a p.val : ℂ)).re = 0 := by
    simp [Complex.mul_re]
  rw [h, Real.exp_zero]

/-- The Minkowski form is invariant: `(Λa)·p = a·(Λ⁻¹p)`. -/
theorem minkowskiInner_lorentz (Λ : LorentzGroup) (a p : Minkowski) :
    minkowskiInner ((Λ.toLin) a) p = minkowskiInner a ((Λ.toLin.symm) p) := by
  have h := Λ.preserves a ((Λ.toLin.symm) p)
  -- ⟪Λa, Λ(Λ⁻¹p)⟫ = ⟪a, Λ⁻¹p⟫, and Λ(Λ⁻¹p) = p
  rw [LinearEquiv.apply_symm_apply] at h
  exact h

/-- Additivity of the Minkowski form in the left argument. -/
theorem minkowskiInner_add_left (x y z : Minkowski) :
    minkowskiInner (x + y) z = minkowskiInner x z + minkowskiInner y z := by
  unfold minkowskiInner
  simp only [Pi.add_apply]
  ring

/-- **T1:** phase multiplicativity (key for the representation law). -/
theorem phase_mul (a₁ a₂ : Minkowski) (Λ₁ : RestrictedLorentz)
    (p : massShell m) (hm : 0 < m) :
    phase (a₁ + (Λ₁ : LorentzGroup).toLin a₂) p
      = phase a₁ p * phase a₂ (shellActR Λ₁⁻¹ m hm p) := by
  have hform : minkowskiInner ((Λ₁ : LorentzGroup).toLin a₂) p.val
      = minkowskiInner a₂ (((Λ₁ : LorentzGroup).toLin.symm) p.val) :=
    minkowskiInner_lorentz (Λ₁ : LorentzGroup) a₂ p.val
  have hsymm : ((Λ₁ : LorentzGroup).toLin.symm) p.val
      = (((Λ₁⁻¹ : RestrictedLorentz) : LorentzGroup).toLin) p.val := by
    have hcoe : ((Λ₁⁻¹ : RestrictedLorentz) : LorentzGroup) = (Λ₁ : LorentzGroup)⁻¹ := rfl
    rw [hcoe, LorentzGroup.inv_toLin]
  have hadd : minkowskiInner (a₁ + (Λ₁ : LorentzGroup).toLin a₂) p.val
      = minkowskiInner a₁ p.val + minkowskiInner a₂
        ((((Λ₁⁻¹ : RestrictedLorentz) : LorentzGroup).toLin) p.val) := by
    rw [minkowskiInner_add_left, hform, hsymm]
  unfold phase shellActR
  simp only
  rw [hadd, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **T1:** the shell action respects multiplication. -/
theorem shellActR_mul (Λ₁ Λ₂ : RestrictedLorentz) (m : ℝ) (hm : 0 < m) :
    shellActR (Λ₁ * Λ₂) m hm = (shellActR Λ₁ m hm) ∘ (shellActR Λ₂ m hm) := by
  funext p
  apply Subtype.ext
  show (((Λ₁ * Λ₂ : RestrictedLorentz) : LorentzGroup).toLin) p.val
    = ((Λ₁ : LorentzGroup).toLin) (((Λ₂ : LorentzGroup).toLin) p.val)
  have hmul : (((Λ₁ * Λ₂ : RestrictedLorentz) : LorentzGroup).toLin)
      = (Λ₂ : LorentzGroup).toLin.trans (Λ₁ : LorentzGroup).toLin := by
    have hcoe : ((Λ₁ * Λ₂ : RestrictedLorentz) : LorentzGroup)
        = (Λ₁ : LorentzGroup) * (Λ₂ : LorentzGroup) := rfl
    rw [hcoe, LorentzGroup.mul_toLin]
  rw [hmul, LinearEquiv.trans_apply]

/-- The phase is measurable in `p`. -/
theorem measurable_phase (a : Minkowski) (m : ℝ) :
    Measurable (fun p : massShell m => phase a p) := by
  unfold phase
  apply Measurable.cexp
  apply measurable_const.mul
  exact Complex.continuous_ofReal.measurable.comp (by
    apply Continuous.measurable
    unfold minkowskiInner
    apply Continuous.sub
    apply Continuous.sub
    apply Continuous.sub
    · exact continuous_const.mul ((continuous_apply 0).comp continuous_subtype_val)
    · exact continuous_const.mul ((continuous_apply 1).comp continuous_subtype_val)
    · exact continuous_const.mul ((continuous_apply 2).comp continuous_subtype_val)
    · exact continuous_const.mul ((continuous_apply 3).comp continuous_subtype_val))

/-- The one-particle function: `U₁(g)ψ(p) = e^{ig.trans·p} ψ(g.lor⁻¹ p)`. -/
noncomputable def oneParticleFun (g : RPoincare) (m : ℝ) (hm : 0 < m)
    (ψ : massShell m → ℂ) : massShell m → ℂ :=
  fun p => phase g.trans p * ψ (shellActR g.lor⁻¹ m hm p)

/-- **T1:** the representation law `U₁(g₁g₂) = U₁(g₁)U₁(g₂)` (pointwise). -/
theorem oneParticleFun_mul (g₁ g₂ : RPoincare) (m : ℝ) (hm : 0 < m)
    (ψ : massShell m → ℂ) :
    oneParticleFun (g₁ * g₂) m hm ψ
      = oneParticleFun g₁ m hm (oneParticleFun g₂ m hm ψ) := by
  funext p
  unfold oneParticleFun
  -- LHS: phase((g₁g₂).trans, p) * ψ((g₁g₂).lor⁻¹ p)
  -- (g₁g₂).trans = g₁.trans + g₁.lor(g₂.trans)
  -- (g₁g₂).lor⁻¹ = g₂.lor⁻¹ * g₁.lor⁻¹
  have htrans : (g₁ * g₂).trans = g₁.trans + (g₁.lor : LorentzGroup).toLin g₂.trans := rfl
  have hlor : (g₁ * g₂).lor⁻¹ = g₂.lor⁻¹ * g₁.lor⁻¹ := by
    rw [RPoincare.mul_lor, mul_inv_rev]
  rw [htrans, hlor]
  -- phase splits by phase_mul
  rw [phase_mul g₁.trans g₂.trans g₁.lor p hm]
  -- pullback splits by shellActR_mul
  have hpull : shellActR (g₂.lor⁻¹ * g₁.lor⁻¹) m hm p
      = shellActR g₂.lor⁻¹ m hm (shellActR g₁.lor⁻¹ m hm p) := by
    rw [shellActR_mul]
    rfl
  rw [hpull]
  ring

/-- **T1:** unitarity — the one-particle map preserves the `L²` (eLpNorm) norm,
    from `Λ`-invariance of the measure. -/
theorem eLpNorm_oneParticleFun (g : RPoincare) (m : ℝ) (hm : 0 < m)
    (hMP : MeasurePreserving (shellActR g.lor⁻¹ m hm)
      (massShellMeasure m hm) (massShellMeasure m hm))
    (ψ : massShell m → ℂ) (hψ : MemLp ψ 2 (massShellMeasure m hm)) :
    eLpNorm (oneParticleFun g m hm ψ) 2 (massShellMeasure m hm)
      = eLpNorm ψ 2 (massShellMeasure m hm) := by
  have hψae := hψ.aestronglyMeasurable
  have hψ' : MemLp (ψ ∘ shellActR g.lor⁻¹ m hm) 2 (massShellMeasure m hm) :=
    hψ.comp_measurePreserving hMP
  have hψ'ae := hψ'.aestronglyMeasurable
  -- the one-particle function is AE measurable
  have hf : AEStronglyMeasurable
      (oneParticleFun g m hm ψ) (massShellMeasure m hm) := by
    unfold oneParticleFun
    apply AEStronglyMeasurable.mul
    · exact (measurable_phase g.trans m).aestronglyMeasurable
    · -- (fun p => ψ (shellActR ... p)) = ψ ∘ shellActR ...
      have heq : (fun p => ψ (shellActR g.lor⁻¹ m hm p))
          = ψ ∘ shellActR g.lor⁻¹ m hm := rfl
      rw [heq]
      exact hψ'ae
  -- phase has enorm 1
  have hphase : ∀ p : massShell m, ‖phase g.trans p‖ₑ = 1 := by
    intro p
    unfold phase
    rw [mul_comm Complex.I _, Complex.enorm_exp_ofReal_mul_I]
  -- enorm of the product equals enorm of ψ'
  have henorm : ∀ᵐ p ∂(massShellMeasure m hm),
      ‖oneParticleFun g m hm ψ p‖ₑ = ‖(ψ ∘ shellActR g.lor⁻¹ m hm) p‖ₑ := by
    filter_upwards with p
    unfold oneParticleFun
    simp only [Function.comp_apply]
    rw [enorm_mul, hphase p, one_mul]
  have h1 : eLpNorm (oneParticleFun g m hm ψ) 2 (massShellMeasure m hm)
      = eLpNorm (ψ ∘ shellActR g.lor⁻¹ m hm) 2 (massShellMeasure m hm) :=
    eLpNorm_congr_enorm_ae hf hψ'ae henorm
  have h2 : eLpNorm (ψ ∘ shellActR g.lor⁻¹ m hm) 2 (massShellMeasure m hm)
      = eLpNorm ψ 2 (massShellMeasure m hm) :=
    eLpNorm_comp_measurePreserving hψae hMP
  rw [h1, h2]

/-- **T1:** the one-particle map preserves `MemLp`. -/
theorem memLp_oneParticleFun (g : RPoincare) (m : ℝ) (hm : 0 < m)
    (hMP : MeasurePreserving (shellActR g.lor⁻¹ m hm)
      (massShellMeasure m hm) (massShellMeasure m hm))
    (ψ : massShell m → ℂ) (hψ : MemLp ψ 2 (massShellMeasure m hm)) :
    MemLp (oneParticleFun g m hm ψ) 2 (massShellMeasure m hm) := by
  show eLpNorm (oneParticleFun g m hm ψ) 2 (massShellMeasure m hm) < ∞
  rw [eLpNorm_oneParticleFun g m hm hMP ψ hψ]
  exact hψ

/-- **T5 window:** strong continuity of the one-particle representation.

    Exact statement: for `ψ` with `MemLp ψ 2 μ`, the map
    `a ↦ eLpNorm (oneParticleFun (a,1) m hm ψ - ψ) 2 μ` tends to `0` as
    `a → 0` in `Minkowski` (translations), and similarly for the full
    `RPoincare` action.

    PRICE — the exact missing piece. For translations, strong continuity
    is the dominated convergence theorem: `‖U₁(aₙ,1)ψ - ψ‖₂²
    = ∫⁻ p, ‖e^{iaₙ·p} - 1‖²‖ψ(p)‖² dμ(p) → 0` as `aₙ → 0`, dominated by
    `4‖ψ‖² ∈ L¹`. What would discharge it: `tendsto_lintegral_of_dominated_convergence`
    applied to `Fₙ(p) = ‖e^{iaₙ·p} - 1‖ₑ² · ‖ψ(p)‖ₑ²`, using
    `Complex.continuous_exp` for pointwise convergence and the `L²` bound.
    For the Lorentz part, strong continuity needs density of `C_c` in `L²`
    and uniform continuity on compacts — a longer analysis argument.
    The representation law (`oneParticleFun_mul`) and unitarity
    (`eLpNorm_oneParticleFun`) are T1 above. -/
def StrongContinuity_window (m : ℝ) (hm : 0 < m) : Prop :=
  ∀ ψ : massShell m → ℂ, MemLp ψ 2 (massShellMeasure m hm) →
    Filter.Tendsto (fun a : Minkowski =>
      eLpNorm (fun p => oneParticleFun ⟨a, 1⟩ m hm ψ p - ψ p) 2 (massShellMeasure m hm))
      (nhds 0) (nhds 0)

/-- The shell action of the identity is the identity. -/
theorem shellActR_one (m : ℝ) (hm : 0 < m) :
    shellActR 1 m hm = id := by
  funext p
  unfold shellActR
  simp

/-- **T1:** translations act measure-preservingly (trivially, since `Λ = 1`). -/
theorem measurePreserving_shellActR_one (m : ℝ) (hm : 0 < m) :
    MeasurePreserving (shellActR (1 : RestrictedLorentz) m hm)
      (massShellMeasure m hm) (massShellMeasure m hm) := by
  rw [shellActR_one]
  exact MeasurePreserving.id _

/-!
## Second quantization (T5 window — blocked on the Fock inner product)
-/

/-- **(c) Second quantization — VERDICT: BLOCKED, price below.**

    The target is `PoincareAction.SecondQuantization_window`: a map
    `Γ(U₁)` lifting the one-particle representation to the Fock space,
    satisfying the representation law and vacuum invariance.

    PRICE — the exact missing pieces, in order of fundamentality:

    1. **The Fock inner product (FUNDAMENTAL).** Mathlib has no inner product
       on `SymmetricAlgebra ℂ V` satisfying the permanent formula
       `⟪ι(v₁)⋯ι(vₙ), ι(w₁)⋯ι(wₙ)⟫ = per(⟪vᵢ,wⱼ⟫)`. Without it:
       - No Hilbert completion of the algebraic Fock space (W0 blocked;
         see `FreeField.lean`, which documents this gap at lines 29-30,
         44-45, 220-223).
       - No way to state or prove that `Γ(U)` is unitary (unitarity is a
         statement about the inner product).
       - No creation/annihilation adjoints (`a(f)* = a†(f)` needs the inner
         product to define the adjoint).
       What would discharge it: formalize the Fock inner product on
       `SymmetricAlgebra ℂ V` via the permanent formula, prove positive
       definiteness (the permanent of a positive Gram matrix is positive —
       this is a nontrivial linear-algebra fact), then take the Hilbert
       completion. This is a substantial formalization project, not a
       single lemma.

    2. **The one-particle unitary as `≃ₗᵢ`.** This file proves
       `oneParticleFun` (function level) with `eLpNorm_oneParticleFun`
       (norm preservation) and `memLp_oneParticleFun` (MemLp preservation),
       but does not package `U₁(g)` as `Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ`. The `Γ`
       functor needs a linear isometry to lift. What would discharge it:
       build the `≃ₗᵢ` from `oneParticleFun` via `MemLp.toLp`, using
       `oneParticleFun_mul` for the inverse laws.

    3. **`SymmetricAlgebra.map`.** Mathlib's `SymmetricAlgebra` API (in
       `Mathlib/RingTheory/Bialgebra/SymmetricAlgebra.lean`) provides `lift`
       (universal property) but no functorial `map` for linear maps. What
       would discharge it: define `SymmetricAlgebra.map f` via `lift`,
       prove functoriality.

    The algebraic (non-unitary, non-completed) second quantization is thus
    also blocked — not by analysis, but by the missing `≃ₗᵢ` packaging in
    (2) and the missing `map` in (3). The fundamental obstruction is (1). -/
theorem secondQuantization_blocked : True := trivial

end ThetLogos
