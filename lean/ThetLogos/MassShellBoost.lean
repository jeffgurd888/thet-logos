import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Constructions.Pi
import ThetLogos.MassShellMeasure

namespace ThetLogos

open MeasureTheory
open scoped ENNReal
open scoped RealInnerProductSpace

/-!
# ThetLogos.MassShellBoost — boost invariance of the mass-shell measure

Discharges the exact price quoted in `MassShellMeasure.lean` for
`BoostInvariance_window`: the 1D Jacobian identity for a boost along the
`x¹`-axis acting on the ℝ³ parametrization of the mass shell.

**What IS proved here (T1, zero sorrys):**
- `boostLin` — the concrete `x¹`-boost as a linear equivalence of Minkowski
  space, parametrized by the velocity `β ∈ (-1, 1)`, with
  `γ = (1 - β²)^(-1/2)`;
- `boostLorentz` / `boostRestricted` — the boost as an element of
  `LorentzGroup`, resp. of `RestrictedLorentz` (Minkowski-form preservation,
  determinant `1`, orthochronous);
- `boostLin_shellParam` — the shell action of the boost intertwines the graph
  parametrization: `B (shellParam m u) = shellParam m (Φ u)` with
  `Φ(u) = (γu₁ - βγE_u, u₂, u₃)`, including the boosted-energy identity
  `E_{Φ u} = γ(E_u - βu₁)`;
- the 1D Jacobian core: for fixed `(u₂, u₃)`, the slice map
  `φ(u₁) = γu₁ - βγ√(m² + u₁² + u₂² + u₃²)` is a strictly monotone `C¹`
  bijection `ℝ → ℝ` with `|φ'(u₁)| = E_{φ(u₁)}/E_u`;
- `boost_preserves_massShellMeasure` — the shell action of the boost is
  `MeasurePreserving` for `massShellMeasure m hm` (via the mass-shell integral
  formula, the 1D image formula in `u₁`, and Tonelli over `(u₂, u₃)`);
- the cap: `boostInvariance_window_proved` — `BoostInvariance_window` itself,
  via the boost–rotation factorization of the restricted Lorentz group
  (every `Λ : RestrictedLorentz` is a product of a spatial rotation, an
  `x¹`-boost and a spatial rotation).

Tier honesty: this is invariance of the *free* one-particle mass-shell measure
under the restricted Lorentz group. No interacting QFT, no continuum limit and
no mass gap are claimed. No existing file is modified.

Counts (attribute-inclusive grep convention, all hits genuine declarations,
no prose hits): 86 theorem/lemma declarations and 15 definitions in this
module. The word `sorry` occurs only in prose (here and in the axiom-audit
section); there is no `sorry`/`admit` in code.
-/

/-!
## The boost factor `γ`
-/

/-- The Lorentz factor `γ = (1 - β²)^(-1/2)`. -/
noncomputable def boostGamma (β : ℝ) : ℝ := (Real.sqrt (1 - β ^ 2))⁻¹

/-- For `|β| < 1`, the number `1 - β²` is positive. -/
theorem boost_one_sub_sq_pos (β : ℝ) (hβ : |β| < 1) : (0:ℝ) < 1 - β ^ 2 := by
  have h2 : β ^ 2 < 1 := by rwa [sq_lt_one_iff_abs_lt_one]
  linarith

/-- `γ > 0` for `|β| < 1`. -/
theorem boostGamma_pos (β : ℝ) (hβ : |β| < 1) : 0 < boostGamma β :=
  inv_pos.mpr (Real.sqrt_pos.mpr (boost_one_sub_sq_pos β hβ))

/-- The defining identity `γ²(1 - β²) = 1`. -/
theorem boostGamma_sq_mul (β : ℝ) (hβ : |β| < 1) :
    (boostGamma β) ^ 2 * (1 - β ^ 2) = 1 := by
  have h1 : (0:ℝ) ≤ 1 - β ^ 2 := le_of_lt (boost_one_sub_sq_pos β hβ)
  have h2 : (1:ℝ) - β ^ 2 ≠ 0 := ne_of_gt (boost_one_sub_sq_pos β hβ)
  unfold boostGamma
  rw [inv_pow, Real.sq_sqrt h1]
  exact inv_mul_cancel₀ h2

/-- `γ ≠ 0` for `|β| < 1`. -/
theorem boostGamma_ne_zero (β : ℝ) (hβ : |β| < 1) : boostGamma β ≠ 0 :=
  ne_of_gt (boostGamma_pos β hβ)

/-!
## Task 1: the concrete `x¹`-boost
-/

/-- The boost along the `x¹`-axis with velocity parameter `β ∈ (-1, 1)`:
    `B(t, x, y, z) = (γt - βγx, -βγt + γx, y, z)`, as a linear equivalence of
    Minkowski space. Its inverse is the boost with velocity `-β` (same `γ`,
    since `γ` depends on `β²`). -/
noncomputable def boostLin (β : ℝ) (hβ : |β| < 1) : Minkowski ≃ₗ[ℝ] Minkowski where
  toFun p := ![boostGamma β * p 0 - β * boostGamma β * p 1,
    -β * boostGamma β * p 0 + boostGamma β * p 1, p 2, p 3]
  invFun p := ![boostGamma β * p 0 + β * boostGamma β * p 1,
    β * boostGamma β * p 0 + boostGamma β * p 1, p 2, p 3]
  map_add' p q := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c p := by
    funext i
    fin_cases i <;> simp <;> ring
  left_inv p := by
    have hγ := boostGamma_sq_mul β hβ
    funext i
    fin_cases i
    · simp only [Fin.mk_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination (p 0) * hγ
    · simp only [Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination (p 1) * hγ
    · simp
    · simp
  right_inv p := by
    have hγ := boostGamma_sq_mul β hβ
    funext i
    fin_cases i
    · simp only [Fin.mk_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination (p 0) * hγ
    · simp only [Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination (p 1) * hγ
    · simp
    · simp

/-- Coordinate formula for the boost. -/
theorem boostLin_apply (β : ℝ) (hβ : |β| < 1) (p : Minkowski) :
    boostLin β hβ p = ![boostGamma β * p 0 - β * boostGamma β * p 1,
      -β * boostGamma β * p 0 + boostGamma β * p 1, p 2, p 3] := rfl

@[simp] theorem boostLin_apply_zero (β : ℝ) (hβ : |β| < 1) (p : Minkowski) :
    (boostLin β hβ p) 0 = boostGamma β * p 0 - β * boostGamma β * p 1 := by
  rw [boostLin_apply]; rfl

@[simp] theorem boostLin_apply_one (β : ℝ) (hβ : |β| < 1) (p : Minkowski) :
    (boostLin β hβ p) 1 = -β * boostGamma β * p 0 + boostGamma β * p 1 := by
  rw [boostLin_apply]; rfl

@[simp] theorem boostLin_apply_two (β : ℝ) (hβ : |β| < 1) (p : Minkowski) :
    (boostLin β hβ p) 2 = p 2 := by
  rw [boostLin_apply]; rfl

@[simp] theorem boostLin_apply_three (β : ℝ) (hβ : |β| < 1) (p : Minkowski) :
    (boostLin β hβ p) 3 = p 3 := by
  rw [boostLin_apply]; rfl

/-- Coordinate formula for the inverse boost (velocity `-β`). -/
theorem boostLin_symm_apply (β : ℝ) (hβ : |β| < 1) (p : Minkowski) :
    (boostLin β hβ).symm p = ![boostGamma β * p 0 + β * boostGamma β * p 1,
      β * boostGamma β * p 0 + boostGamma β * p 1, p 2, p 3] := rfl

@[simp] theorem boostLin_symm_apply_zero (β : ℝ) (hβ : |β| < 1) (p : Minkowski) :
    ((boostLin β hβ).symm p) 0 = boostGamma β * p 0 + β * boostGamma β * p 1 := by
  rw [boostLin_symm_apply]; rfl

@[simp] theorem boostLin_symm_apply_one (β : ℝ) (hβ : |β| < 1) (p : Minkowski) :
    ((boostLin β hβ).symm p) 1 = β * boostGamma β * p 0 + boostGamma β * p 1 := by
  rw [boostLin_symm_apply]; rfl

/-- **T1:** the boost preserves the Minkowski form. The cross terms cancel and
    the diagonal terms collapse via `γ²(1 - β²) = 1`. -/
theorem boostLin_preserves (β : ℝ) (hβ : |β| < 1) (p q : Minkowski) :
    minkowskiInner (boostLin β hβ p) (boostLin β hβ q) = minkowskiInner p q := by
  have hγ := boostGamma_sq_mul β hβ
  unfold minkowskiInner
  simp only [boostLin_apply_zero, boostLin_apply_one, boostLin_apply_two,
    boostLin_apply_three]
  linear_combination (p 0 * q 0 - p 1 * q 1) * hγ

/-- The boost as an element of the Lorentz group `O(1,3)`. -/
noncomputable def boostLorentz (β : ℝ) (hβ : |β| < 1) : LorentzGroup where
  toLin := boostLin β hβ
  preserves := boostLin_preserves β hβ

/-- The boost fixes the spatial `y, z` coordinates and mixes `(t, x)`. Its
    action on the time axis: `B e₀ = (γ, -βγ, 0, 0)`, in particular the time
    component is `γ > 0` — the boost is orthochronous. -/
theorem boostLorentz_timeVec (β : ℝ) (hβ : |β| < 1) :
    (boostLorentz β hβ).toLin timeVec
      = ![boostGamma β, -β * boostGamma β, 0, 0] := by
  show boostLin β hβ timeVec = _
  rw [boostLin_apply]
  unfold timeVec
  simp

/-- **T1:** the boost is orthochronous. -/
theorem boost_isOrthoChronous (β : ℝ) (hβ : |β| < 1) :
    IsOrthoChronous (boostLorentz β hβ) := by
  show 0 < ((boostLorentz β hβ).toLin timeVec) 0
  rw [boostLorentz_timeVec]
  simp only [Matrix.cons_val_zero]
  exact boostGamma_pos β hβ

/-!
## Properness: `det B = 1` via light-cone conjugation

In light-cone coordinates `u = t + x`, `w = t - x` the boost is diagonal:
`u ↦ γ(1 - β) u`, `w ↦ γ(1 + β) w`. Hence, with `C` the light-cone change of
coordinates, `B = C ∘ D ∘ C⁻¹` with `D` diagonal, and conjugation invariance
of the determinant gives `det B = γ(1 - β) · γ(1 + β) = γ²(1 - β²) = 1`.
-/

/-- The light-cone coordinate change `(t, x, y, z) ↦ (t + x, t - x, y, z)`. -/
noncomputable def lightConeEquiv : Minkowski ≃ₗ[ℝ] Minkowski where
  toFun p := ![p 0 + p 1, p 0 - p 1, p 2, p 3]
  invFun q := ![(q 0 + q 1) / 2, (q 0 - q 1) / 2, q 2, q 3]
  map_add' p q := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c p := by
    funext i
    fin_cases i <;> simp <;> ring
  left_inv p := by
    funext i
    fin_cases i <;> simp
  right_inv p := by
    funext i
    fin_cases i <;> simp <;> ring

theorem lightConeEquiv_apply (p : Minkowski) :
    lightConeEquiv p = ![p 0 + p 1, p 0 - p 1, p 2, p 3] := rfl

theorem lightConeEquiv_symm_apply (q : Minkowski) :
    lightConeEquiv.symm q = ![(q 0 + q 1) / 2, (q 0 - q 1) / 2, q 2, q 3] := rfl

/-- The diagonal light-cone form of the boost: scales `u = t + x` by
    `γ(1 - β)` and `w = t - x` by `γ(1 + β)`. -/
noncomputable def boostDiagEquiv (β : ℝ) (hβ : |β| < 1) : Minkowski ≃ₗ[ℝ] Minkowski where
  toFun q := ![boostGamma β * (1 - β) * q 0, boostGamma β * (1 + β) * q 1, q 2, q 3]
  invFun q := ![(boostGamma β * (1 - β))⁻¹ * q 0, (boostGamma β * (1 + β))⁻¹ * q 1,
    q 2, q 3]
  map_add' p q := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c p := by
    funext i
    fin_cases i <;> simp <;> ring
  left_inv p := by
    have hβ1 : β < 1 := (abs_lt.mp hβ).2
    have hβ2 : -1 < β := (abs_lt.mp hβ).1
    have h1 : boostGamma β * (1 - β) ≠ 0 :=
      mul_ne_zero (boostGamma_ne_zero β hβ) (by linarith)
    have h2 : boostGamma β * (1 + β) ≠ 0 :=
      mul_ne_zero (boostGamma_ne_zero β hβ) (by linarith)
    funext i
    fin_cases i
    · simp only [Fin.mk_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← mul_assoc, inv_mul_cancel₀ h1, one_mul]
    · simp only [Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← mul_assoc, inv_mul_cancel₀ h2, one_mul]
    · simp
    · simp
  right_inv p := by
    have hβ1 : β < 1 := (abs_lt.mp hβ).2
    have hβ2 : -1 < β := (abs_lt.mp hβ).1
    have h1 : boostGamma β * (1 - β) ≠ 0 :=
      mul_ne_zero (boostGamma_ne_zero β hβ) (by linarith)
    have h2 : boostGamma β * (1 + β) ≠ 0 :=
      mul_ne_zero (boostGamma_ne_zero β hβ) (by linarith)
    funext i
    fin_cases i
    · simp only [Fin.mk_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← mul_assoc, mul_inv_cancel₀ h1, one_mul]
    · simp only [Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← mul_assoc, mul_inv_cancel₀ h2, one_mul]
    · simp
    · simp

theorem boostDiagEquiv_apply (β : ℝ) (hβ : |β| < 1) (q : Minkowski) :
    boostDiagEquiv β hβ q = ![boostGamma β * (1 - β) * q 0,
      boostGamma β * (1 + β) * q 1, q 2, q 3] := rfl

/-- **T1:** the boost is the light-cone conjugate of its diagonal form:
    `B = C ∘ D ∘ C⁻¹`. -/
theorem boostLin_eq_conj (β : ℝ) (hβ : |β| < 1) :
    boostLin β hβ
      = lightConeEquiv.trans ((boostDiagEquiv β hβ).trans lightConeEquiv.symm) := by
  apply LinearEquiv.ext
  intro p
  funext i
  fin_cases i
  · simp only [LinearEquiv.trans_apply, boostLin_apply, lightConeEquiv_apply,
      lightConeEquiv_symm_apply, boostDiagEquiv_apply, Fin.mk_zero,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · simp only [LinearEquiv.trans_apply, boostLin_apply, lightConeEquiv_apply,
      lightConeEquiv_symm_apply, boostDiagEquiv_apply, Fin.mk_one,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · simp [LinearEquiv.trans_apply, lightConeEquiv_apply,
      lightConeEquiv_symm_apply, boostDiagEquiv_apply]
  · simp [LinearEquiv.trans_apply, lightConeEquiv_apply,
      lightConeEquiv_symm_apply, boostDiagEquiv_apply]

/-- The diagonal form as a matrix operator. -/
theorem boostDiagEquiv_toLinearMap (β : ℝ) (hβ : |β| < 1) :
    (boostDiagEquiv β hβ).toLinearMap
      = Matrix.toLin' (Matrix.diagonal
          ![boostGamma β * (1 - β), boostGamma β * (1 + β), 1, 1]) := by
  apply LinearMap.ext
  intro p
  funext i
  fin_cases i <;>
    simp [Matrix.toLin'_apply', Matrix.mulVec_diagonal,
      boostDiagEquiv_apply]

/-- **T1:** the boost has determinant `1` (it is proper). -/
theorem boost_isProper (β : ℝ) (hβ : |β| < 1) : IsProper (boostLorentz β hβ) := by
  have hγ := boostGamma_sq_mul β hβ
  show LinearEquiv.det (boostLorentz β hβ).toLin = 1
  have hform : lightConeEquiv.trans ((boostDiagEquiv β hβ).trans lightConeEquiv.symm)
      = ((lightConeEquiv.symm).symm.trans (boostDiagEquiv β hβ)).trans
        lightConeEquiv.symm := by
    rw [LinearEquiv.symm_symm, LinearEquiv.trans_assoc]
  have hdet : LinearEquiv.det (boostLin β hβ) = 1 := by
    rw [boostLin_eq_conj, hform, LinearEquiv.det_conj]
    apply Units.ext
    rw [LinearEquiv.coe_det, boostDiagEquiv_toLinearMap, LinearMap.det_toLin',
      Matrix.det_diagonal, Units.val_one]
    simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, mul_one]
    linear_combination hγ
  exact hdet

/-- The boost as an element of the restricted Lorentz group `SO⁺(1,3)`. -/
noncomputable def boostRestricted (β : ℝ) (hβ : |β| < 1) : RestrictedLorentz :=
  ⟨boostLorentz β hβ, boost_isProper β hβ, boost_isOrthoChronous β hβ⟩

theorem boostRestricted_coe (β : ℝ) (hβ : |β| < 1) :
    ((boostRestricted β hβ : RestrictedLorentz) : LorentzGroup)
      = boostLorentz β hβ := rfl

/-!
## Task 2: compatibility with the mass-shell parametrization
-/

/-- The boost's action on the spatial momentum: `Φ(u) = (γu₁ - βγE_u, u₂, u₃)`. -/
noncomputable def boostParamMap (m β : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm
    ![boostGamma β * u 0 - β * boostGamma β * shellEnergy m u, u 1, u 2]

theorem boostParamMap_zero (m β : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    boostParamMap m β u 0
      = boostGamma β * u 0 - β * boostGamma β * shellEnergy m u := rfl

theorem boostParamMap_one (m β : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    boostParamMap m β u 1 = u 1 := rfl

theorem boostParamMap_two (m β : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    boostParamMap m β u 2 = u 2 := rfl

/-- The squared norm in coordinates. -/
theorem euclidean_norm_sq_coord (u : EuclideanSpace ℝ (Fin 3)) :
    ‖u‖ ^ 2 = (u 0) ^ 2 + (u 1) ^ 2 + (u 2) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

/-- `E_u - βu₁ > 0`: the energy dominates the first spatial component. -/
theorem shellEnergy_sub_pos (m β : ℝ) (hm : 0 < m) (hβ : |β| < 1)
    (u : EuclideanSpace ℝ (Fin 3)) : 0 < shellEnergy m u - β * u 0 := by
  have h1 : ‖u‖ < shellEnergy m u := by
    unfold shellEnergy
    nth_rewrite 1 [← Real.sqrt_sq (norm_nonneg u)]
    apply Real.sqrt_lt_sqrt (sq_nonneg _)
    have h2 : (0:ℝ) < m ^ 2 := pow_pos hm 2
    linarith [sq_nonneg ‖u‖]
  have h2 : |u 0| ≤ ‖u‖ := by
    have h := PiLp.norm_apply_le u (0 : Fin 3)
    rwa [Real.norm_eq_abs] at h
  have h3 : β * u 0 ≤ |β| * |u 0| := (le_abs_self _).trans_eq (abs_mul _ _)
  have h4 : |β| * |u 0| ≤ |u 0| := by
    have h := mul_le_mul_of_nonneg_right (le_of_lt hβ) (abs_nonneg (u 0))
    rwa [one_mul] at h
  linarith

/-- **T1 (boosted-energy identity):** `E_{Φ u} = γ(E_u - βu₁)`. Proved by
    comparing squares (both sides are positive) via `γ²(1 - β²) = 1` and
    `E_u² = m² + ‖u‖²`. -/
theorem shellEnergy_boostParamMap (m β : ℝ) (hm : 0 < m) (hβ : |β| < 1)
    (u : EuclideanSpace ℝ (Fin 3)) :
    shellEnergy m (boostParamMap m β u)
      = boostGamma β * (shellEnergy m u - β * u 0) := by
  have hγ := boostGamma_sq_mul β hβ
  have hE : (shellEnergy m u) ^ 2
      = m ^ 2 + ((u 0) ^ 2 + (u 1) ^ 2 + (u 2) ^ 2) := by
    rw [shellEnergy_sq, euclidean_norm_sq_coord]
  have hsq : (shellEnergy m (boostParamMap m β u)) ^ 2
      = (boostGamma β * (shellEnergy m u - β * u 0)) ^ 2 := by
    rw [shellEnergy_sq, euclidean_norm_sq_coord]
    simp only [boostParamMap_zero, boostParamMap_one, boostParamMap_two]
    linear_combination (-(shellEnergy m u) ^ 2 + (u 0) ^ 2) * hγ - hE
  have h1 : (0:ℝ) ≤ shellEnergy m (boostParamMap m β u) := Real.sqrt_nonneg _
  have h2 : (0:ℝ) ≤ boostGamma β * (shellEnergy m u - β * u 0) :=
    le_of_lt (mul_pos (boostGamma_pos β hβ) (shellEnergy_sub_pos m β hm hβ u))
  exact (sq_eq_sq₀ h1 h2).mp hsq

/-- **T1 (param compatibility):** the boost intertwines the graph
    parametrization: `B (shellParam m u) = shellParam m (Φ u)`. -/
theorem boostLin_shellParam (m β : ℝ) (hm : 0 < m) (hβ : |β| < 1)
    (u : EuclideanSpace ℝ (Fin 3)) :
    boostLin β hβ (shellParam m u) = shellParam m (boostParamMap m β u) := by
  funext i
  fin_cases i
  · simp only [Fin.mk_zero, shellParam_comp0, shellParam_comp1, boostLin_apply_zero]
    rw [shellEnergy_boostParamMap m β hm hβ u]
    ring
  · simp only [Fin.mk_one, shellParam_comp0, shellParam_comp1,
      boostLin_apply_one, boostParamMap_zero]
    ring
  · simp [shellParam_comp2, boostLin_apply_two, boostParamMap_one]
  · simp [shellParam_comp3, boostLin_apply_three, boostParamMap_two]

/-!
## Task 3: the 1D Jacobian core

For fixed `(a, b) = (u₂, u₃)`, the slice map
`φ(x) = γx - βγ√(m² + a² + b² + x²)` is a strictly monotone `C¹` bijection
`ℝ → ℝ` whose derivative satisfies `|φ'(x)| = E_{φ(x)}/E_x`, where
`E_x = √(m² + a² + b² + x²)` and `E_{φ(x)} = √(m² + a² + b² + φ(x)²)`.
-/

/-- The slice map of the boost at fixed transverse coordinates `(a, b)`. -/
noncomputable def boostSlice (m β a b : ℝ) (x : ℝ) : ℝ :=
  boostGamma β * x - β * boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2)

/-- The slice energy is positive. -/
theorem sliceEnergy_pos (m a b x : ℝ) (hm : 0 < m) :
    0 < Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2) :=
  Real.sqrt_pos.mpr (by
    have h1 : (0:ℝ) < m ^ 2 := pow_pos hm 2
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg x])

/-- The slice energy dominates the slice coordinate: `|x| < E_x`. -/
theorem sliceEnergy_gt (m a b x : ℝ) (hm : 0 < m) :
    |x| < Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_lt_sqrt (sq_nonneg x)
  have h1 : (0:ℝ) < m ^ 2 := pow_pos hm 2
  nlinarith [sq_nonneg a, sq_nonneg b]

/-- `E_x - βx > 0`. -/
theorem sliceEnergy_sub_pos (m β a b x : ℝ) (hm : 0 < m) (hβ : |β| < 1) :
    0 < Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2) - β * x := by
  have h1 := sliceEnergy_gt m a b x hm
  have h2 : β * x ≤ |β| * |x| := (le_abs_self _).trans_eq (abs_mul _ _)
  have h3 : |β| * |x| ≤ |x| := by
    have h := mul_le_mul_of_nonneg_right (le_of_lt hβ) (abs_nonneg x)
    rwa [one_mul] at h
  linarith

/-- The slice map is differentiable everywhere, with
    `φ'(x) = γ - βγ · x/E_x`. -/
theorem boostSlice_hasDerivAt (m β a b : ℝ) (hm : 0 < m) (x : ℝ) :
    HasDerivAt (boostSlice m β a b)
      (boostGamma β - β * boostGamma β
        * (x / Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2))) x := by
  have hpos : (0:ℝ) < m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2 := by
    have h1 : (0:ℝ) < m ^ 2 := pow_pos hm 2
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg x]
  have h1 : HasDerivAt (fun y : ℝ => m ^ 2 + a ^ 2 + b ^ 2 + y ^ 2) (2 * x) x := by
    have h := (hasDerivAt_pow 2 x).const_add (m ^ 2 + a ^ 2 + b ^ 2)
    simpa using h
  have h2 : HasDerivAt (fun y : ℝ => Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + y ^ 2))
      (x / Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2)) x := by
    have h := h1.sqrt (ne_of_gt hpos)
    rwa [mul_div_mul_left _ _ (two_ne_zero : (2:ℝ) ≠ 0)] at h
  have h3 := ((hasDerivAt_id' x).const_mul (boostGamma β)).sub
    (h2.const_mul (β * boostGamma β))
  unfold boostSlice
  simpa only [Pi.sub_def, mul_one] using h3

/-- The slice map is continuous. -/
theorem boostSlice_continuous (m β a b : ℝ) (hm : 0 < m) :
    Continuous (boostSlice m β a b) :=
  continuous_iff_continuousAt.mpr
    (fun x => (boostSlice_hasDerivAt m β a b hm x).continuousAt)

/-- The derivative of the slice map in the form `γ(E_x - βx)/E_x`. -/
theorem boostSlice_deriv_eq (m β a b : ℝ) (hm : 0 < m) (x : ℝ) :
    boostGamma β - β * boostGamma β
        * (x / Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2))
      = boostGamma β * (Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2) - β * x)
        / Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2) := by
  have hE : Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2) ≠ 0 :=
    ne_of_gt (sliceEnergy_pos m a b x hm)
  field_simp

/-- The derivative of the slice map is everywhere positive. -/
theorem boostSlice_deriv_pos (m β a b : ℝ) (hm : 0 < m) (hβ : |β| < 1) (x : ℝ) :
    0 < boostGamma β - β * boostGamma β
        * (x / Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2)) := by
  rw [boostSlice_deriv_eq m β a b hm x]
  exact div_pos (mul_pos (boostGamma_pos β hβ) (sliceEnergy_sub_pos m β a b x hm hβ))
    (sliceEnergy_pos m a b x hm)

/-- **T1:** the slice map is strictly monotone. -/
theorem boostSlice_strictMono (m β a b : ℝ) (hm : 0 < m) (hβ : |β| < 1) :
    StrictMono (boostSlice m β a b) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(boostSlice_hasDerivAt m β a b hm x).deriv]
  exact boostSlice_deriv_pos m β a b hm hβ x

/-- Affine lower bound for the slice map on `x ≥ 0`:
    `φ(x) ≥ γ(1 - |β|)x - γ√(m² + a² + b²)`. -/
theorem boostSlice_lower_bound (m β a b : ℝ) (hβ : |β| < 1) (x : ℝ) (hx : 0 ≤ x) :
    boostGamma β * (1 - |β|) * x - boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2)
      ≤ boostSlice m β a b x := by
  have hγ := boostGamma_pos β hβ
  have hsqrt : Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2)
      ≤ x + Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2) := by
    have hnn : (0:ℝ) ≤ x + Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2) :=
      add_nonneg hx (Real.sqrt_nonneg _)
    rw [← Real.sqrt_sq hnn]
    apply Real.sqrt_le_sqrt
    rw [add_sq, Real.sq_sqrt (by
      have h1 : (0:ℝ) ≤ m ^ 2 := sq_nonneg m
      nlinarith [sq_nonneg a, sq_nonneg b])]
    nlinarith [mul_nonneg hx (Real.sqrt_nonneg (m ^ 2 + a ^ 2 + b ^ 2))]
  have hS : (0:ℝ) ≤ Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2) := Real.sqrt_nonneg _
  have step1 : β * boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2)
      ≤ |β| * boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self β) (le_of_lt hγ)) hS
  have step2 : |β| * boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2)
      ≤ |β| * boostGamma β * (x + Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2)) :=
    mul_le_mul_of_nonneg_left hsqrt (mul_nonneg (abs_nonneg β) (le_of_lt hγ))
  have step3 : |β| * boostGamma β * (x + Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2))
      ≤ |β| * boostGamma β * x
        + boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2) := by
    rw [mul_add]
    gcongr
    simpa using mul_le_mul_of_nonneg_right (le_of_lt hβ) (le_of_lt hγ)
  have hle : β * boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2)
      ≤ |β| * boostGamma β * x
        + boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2) :=
    le_trans step1 (le_trans step2 step3)
  have hform : boostGamma β * (1 - |β|) * x
        - boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2)
      = boostGamma β * x - (|β| * boostGamma β * x
        + boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2)) := by ring
  rw [hform]
  unfold boostSlice
  linarith [hle]

/-- Affine upper bound for the slice map on `x ≤ 0`:
    `φ(x) ≤ γ(1 - |β|)x + γ√(m² + a² + b²)`. -/
theorem boostSlice_upper_bound (m β a b : ℝ) (hβ : |β| < 1) (x : ℝ) (hx : x ≤ 0) :
    boostSlice m β a b x
      ≤ boostGamma β * (1 - |β|) * x
        + boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2) := by
  have hγ := boostGamma_pos β hβ
  have hsqrt : Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2)
      ≤ -x + Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2) := by
    have hnn : (0:ℝ) ≤ -x + Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2) :=
      add_nonneg (neg_nonneg.mpr hx) (Real.sqrt_nonneg _)
    rw [← Real.sqrt_sq hnn]
    apply Real.sqrt_le_sqrt
    rw [add_sq, Real.sq_sqrt (by
      have h1 : (0:ℝ) ≤ m ^ 2 := sq_nonneg m
      nlinarith [sq_nonneg a, sq_nonneg b])]
    nlinarith [mul_nonneg (neg_nonneg.mpr hx) (Real.sqrt_nonneg (m ^ 2 + a ^ 2 + b ^ 2))]
  have hS : (0:ℝ) ≤ Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2) := Real.sqrt_nonneg _
  have stepA : -β * boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2)
      ≤ |β| * boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (neg_le_abs β) (le_of_lt hγ)) hS
  have stepB : |β| * boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2)
      ≤ |β| * boostGamma β * (-x + Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2)) :=
    mul_le_mul_of_nonneg_left hsqrt (mul_nonneg (abs_nonneg β) (le_of_lt hγ))
  have stepC : |β| * boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2)
      ≤ boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2) := by
    calc |β| * boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2)
        = (|β| * boostGamma β) * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2) := by ring
      _ ≤ (1 * boostGamma β) * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_of_lt hβ) (le_of_lt hγ))
          (Real.sqrt_nonneg _)
      _ = boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2) := by ring
  have stepD : |β| * boostGamma β * (-x + Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2))
      = |β| * boostGamma β * (-x)
        + |β| * boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2) := mul_add _ _ _
  have hle : -β * boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2)
      ≤ |β| * boostGamma β * (-x)
        + boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2) :=
    le_trans stepA (le_trans stepB (stepD ▸ add_le_add le_rfl stepC))
  have hform : boostGamma β * (1 - |β|) * x
        + boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2)
      = boostGamma β * x + (|β| * boostGamma β * (-x)
        + boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2)) := by ring
  have hunfold : boostSlice m β a b x
      = boostGamma β * x
        + -β * boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2) := by
    unfold boostSlice
    ring
  rw [hunfold, hform]
  exact add_le_add le_rfl hle

/-- The slice map tends to `+∞` at `+∞` (it dominates an affine function
    with positive slope). -/
theorem boostSlice_tendsto_atTop (m β a b : ℝ) (hβ : |β| < 1) :
    Filter.Tendsto (boostSlice m β a b) Filter.atTop Filter.atTop := by
  have hγ := boostGamma_pos β hβ
  have hcoef : (0:ℝ) < boostGamma β * (1 - |β|) :=
    mul_pos hγ (by linarith [abs_nonneg β])
  refine Filter.tendsto_atTop_mono' Filter.atTop
    (f₁ := fun x : ℝ => boostGamma β * (1 - |β|) * x
      + (-(boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2)))) ?_ ?_
  · refine Filter.eventually_atTop.2 ⟨0, fun x hx => ?_⟩
    have h := boostSlice_lower_bound m β a b hβ x hx
    rwa [sub_eq_add_neg] at h
  · exact Filter.tendsto_atTop_add_const_right _ _
      (Filter.Tendsto.const_mul_atTop hcoef Filter.tendsto_id)

/-- The slice map tends to `-∞` at `-∞` (it is dominated by an affine
    function with positive slope). -/
theorem boostSlice_tendsto_atBot (m β a b : ℝ) (hβ : |β| < 1) :
    Filter.Tendsto (boostSlice m β a b) Filter.atBot Filter.atBot := by
  have hγ := boostGamma_pos β hβ
  have hcoef : (0:ℝ) < boostGamma β * (1 - |β|) :=
    mul_pos hγ (by linarith [abs_nonneg β])
  refine Filter.tendsto_atBot_mono' Filter.atBot
    (f₁ := fun x : ℝ => boostGamma β * (1 - |β|) * x
      + boostGamma β * Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2)) ?_ ?_
  · exact Filter.eventually_atBot.2
      ⟨0, fun x hx => boostSlice_upper_bound m β a b hβ x hx⟩
  · exact Filter.tendsto_atBot_add_const_right _ _
      (Filter.Tendsto.const_mul_atBot hcoef Filter.tendsto_id)

/-- **T1:** the slice map is a bijection `ℝ → ℝ` (continuous, strictly
    monotone, with limits `±∞` at `±∞`; surjectivity by the intermediate
    value theorem). -/
theorem boostSlice_surjective (m β a b : ℝ) (hm : 0 < m) (hβ : |β| < 1) :
    Function.Surjective (boostSlice m β a b) := by
  intro y
  obtain ⟨A, hA⟩ : ∃ A, y < boostSlice m β a b A := by
    obtain ⟨i, hi⟩ := Filter.eventually_atTop.mp
      ((boostSlice_tendsto_atTop m β a b hβ).eventually_gt_atTop y)
    exact ⟨i, hi i le_rfl⟩
  obtain ⟨A', hA'⟩ : ∃ A', boostSlice m β a b A' < y := by
    obtain ⟨i, hi⟩ := Filter.eventually_atBot.mp
      ((boostSlice_tendsto_atBot m β a b hβ).eventually_lt_atBot y)
    exact ⟨i, hi i le_rfl⟩
  have hmono := (boostSlice_strictMono m β a b hm hβ).monotone
  obtain ⟨x, -, hfx⟩ : y ∈ boostSlice m β a b '' Set.Icc (min A' A) (max A' A) := by
    apply intermediate_value_Icc (min_le_max)
    · exact (boostSlice_continuous m β a b hm).continuousOn
    · constructor
      · exact le_of_lt (lt_of_le_of_lt (hmono (min_le_left A' A)) hA')
      · exact le_of_lt (lt_of_lt_of_le hA (hmono (le_max_right A' A)))
  exact ⟨x, hfx⟩

/-- **T1 (the Jacobian identity):** the energy of the image point is
    `E_{φ(x)} = γ(E_x - βx)`. Proved by comparing squares via
    `γ²(1 - β²) = 1` and `E_x² = m² + a² + b² + x²`. -/
theorem boostSlice_jacobian (m β a b : ℝ) (hm : 0 < m) (hβ : |β| < 1) (x : ℝ) :
    Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + (boostSlice m β a b x) ^ 2)
      = boostGamma β * (Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2) - β * x) := by
  have hγ := boostGamma_sq_mul β hβ
  have hE : (Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2)) ^ 2
      = m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg x, sq_nonneg m])
  have hsq : (Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + (boostSlice m β a b x) ^ 2)) ^ 2
      = (boostGamma β * (Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2) - β * x)) ^ 2 := by
    rw [Real.sq_sqrt (by
      nlinarith [sq_nonneg (boostSlice m β a b x), sq_nonneg a, sq_nonneg b,
        sq_nonneg m])]
    unfold boostSlice
    linear_combination
      (x ^ 2 - (Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2)) ^ 2) * hγ - hE
  have h1 : (0:ℝ) ≤ Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + (boostSlice m β a b x) ^ 2) :=
    Real.sqrt_nonneg _
  have h2 : (0:ℝ) ≤ boostGamma β * (Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2) - β * x) :=
    le_of_lt (mul_pos (boostGamma_pos β hβ) (sliceEnergy_sub_pos m β a b x hm hβ))
  exact (sq_eq_sq₀ h1 h2).mp hsq

/-- **T1:** `|φ'(x)| = E_{φ(x)}/E_x` — the Jacobian of the slice map is the
    ratio of the image energy to the source energy. This is the identity
    that cancels the density `1/(2E)`. -/
theorem boostSlice_abs_deriv (m β a b : ℝ) (hm : 0 < m) (hβ : |β| < 1) (x : ℝ) :
    |boostGamma β - β * boostGamma β
        * (x / Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2))|
      = Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + (boostSlice m β a b x) ^ 2)
        / Real.sqrt (m ^ 2 + a ^ 2 + b ^ 2 + x ^ 2) := by
  rw [boostSlice_jacobian m β a b hm hβ x,
    abs_of_pos (boostSlice_deriv_pos m β a b hm hβ x),
    boostSlice_deriv_eq m β a b hm x]

/-!
## Task 4: the measure discharge

The density identity on the parametrization space. The change of variables
is `MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul` (the
`∫⁻`-form of the 1D Jacobian formula in
`Mathlib/MeasureTheory/Function/JacobianOneDim.lean`), applied slice by
slice, with Tonelli (`lintegral_prod_symm`) over the transverse plane and
the parametrization transported between `EuclideanSpace ℝ (Fin 3)` and
`Fin 3 → ℝ` by `PiLp.volume_preserving_toLp`.
-/

/-- The shell energy is continuous. -/
theorem shellEnergy_continuous (m : ℝ) : Continuous (shellEnergy m) := by
  unfold shellEnergy
  exact Real.continuous_sqrt.comp
    (continuous_const.add (continuous_norm.pow 2))

/-- The parametrized boost action is continuous, hence measurable. -/
theorem boostParamMap_continuous (m β : ℝ) : Continuous (boostParamMap m β) := by
  have hcoord : Continuous (fun u : EuclideanSpace ℝ (Fin 3) =>
      ![boostGamma β * u 0 - β * boostGamma β * shellEnergy m u, u 1, u 2]) := by
    apply continuous_pi
    intro i
    fin_cases i
    · simpa only [Pi.sub_def, Fin.mk_zero, Matrix.cons_val_zero] using
        ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ)
          (i := (0 : Fin 3))).const_mul (boostGamma β)).sub
          ((shellEnergy_continuous m).const_mul (β * boostGamma β))
    · simpa using PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) (i := (1 : Fin 3))
    · simpa using PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) (i := (2 : Fin 3))
  have hlin : Continuous (EuclideanSpace.equiv (Fin 3) ℝ).symm :=
    LinearMap.continuous_of_finiteDimensional
      (EuclideanSpace.equiv (Fin 3) ℝ).symm.toLinearMap
  exact hlin.comp hcoord

theorem boostParamMap_measurable (m β : ℝ) : Measurable (boostParamMap m β) :=
  (boostParamMap_continuous m β).measurable

/-- The slice map, jointly measurable in the momentum coordinates. -/
theorem boostSlice_measurable3 (m β : ℝ) :
    Measurable (fun v : Fin 3 → ℝ => boostSlice m β (v 1) (v 2) (v 0)) := by
  have hcont : Continuous (fun v : Fin 3 → ℝ => boostSlice m β (v 1) (v 2) (v 0)) := by
    unfold boostSlice
    fun_prop
  exact hcont.measurable

/-- The boost's action on the function-space model `Fin 3 → ℝ` of the
    parametrization. -/
noncomputable def boostFnMap (m β : ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![boostSlice m β (v 1) (v 2) (v 0), v 1, v 2]

theorem boostFnMap_measurable (m β : ℝ) : Measurable (boostFnMap m β) := by
  rw [measurable_pi_iff]
  intro i
  fin_cases i
  · simpa [boostFnMap] using boostSlice_measurable3 m β
  · simpa [boostFnMap] using measurable_pi_apply (1 : Fin 3)
  · simpa [boostFnMap] using measurable_pi_apply (2 : Fin 3)

theorem boostFnMap_apply (m β : ℝ) (x : ℝ) (w : Fin 2 → ℝ) :
    boostFnMap m β ![x, w 0, w 1]
      = ![boostSlice m β (w 0) (w 1) x, w 0, w 1] := rfl

/-- The shell energy on the function-space model. -/
theorem shellEnergy_toLp (m : ℝ) (v : Fin 3 → ℝ) :
    shellEnergy m (WithLp.toLp 2 v)
      = Real.sqrt (m ^ 2 + (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2) := by
  unfold shellEnergy
  rw [euclidean_norm_sq_coord]
  congr 1
  ring

/-- The parametrized boost action commutes with the `PiLp` identification. -/
theorem boostParamMap_toLp (m β : ℝ) (v : Fin 3 → ℝ) :
    boostParamMap m β (WithLp.toLp 2 v)
      = WithLp.toLp 2 (boostFnMap m β v) := by
  ext i
  fin_cases i
  · simp only [Fin.mk_zero, boostParamMap_zero, shellEnergy_toLp,
      boostFnMap, Matrix.cons_val_zero, boostSlice]
    congr 1
    congr 1
    ring
  · simp [boostParamMap_one, boostFnMap]
  · simp [boostParamMap_two, boostFnMap]

/-- The pointwise cancellation: the Jacobian factor `E'/E` against the
    density `1/(2E')` leaves `1/(2E)`. -/
theorem ennreal_jacobian_cancel (E E' : ℝ) (hE : 0 < E) (hE' : 0 < E') (F : ℝ≥0∞) :
    ENNReal.ofReal (E' / E) * ((ENNReal.ofReal (2 * E'))⁻¹ * F)
      = (ENNReal.ofReal (2 * E))⁻¹ * F := by
  have h1 : ENNReal.ofReal (E' / E) * (ENNReal.ofReal (2 * E'))⁻¹
      = (ENNReal.ofReal (2 * E))⁻¹ := by
    have e1 : (ENNReal.ofReal (2 * E'))⁻¹ = ENNReal.ofReal ((2 * E')⁻¹) :=
      (ENNReal.ofReal_inv_of_pos (by linarith)).symm
    have e2 : (ENNReal.ofReal (2 * E))⁻¹ = ENNReal.ofReal ((2 * E)⁻¹) :=
      (ENNReal.ofReal_inv_of_pos (by linarith)).symm
    rw [e1, e2, ← ENNReal.ofReal_mul (div_nonneg hE'.le hE.le)]
    congr 1
    field_simp [ne_of_gt hE, ne_of_gt hE']
  rw [← mul_assoc, h1]

/-- **T1 (the slice lintegral identity):** for each fixed transverse
    momentum `w`, the 1D change of variables along the boost slice cancels
    the density `1/(2E)` exactly. This is the mass-shell instance of the
    identity priced in `MassShellMeasure.lean`. -/
theorem boostSlice_lintegral (m β : ℝ) (hm : 0 < m) (hβ : |β| < 1)
    (w : Fin 2 → ℝ) (F : (Fin 3 → ℝ) → ℝ≥0∞) :
    ∫⁻ x : ℝ, (ENNReal.ofReal
        (2 * Real.sqrt (m ^ 2 + (w 0) ^ 2 + (w 1) ^ 2 + x ^ 2)))⁻¹
        * F ![boostSlice m β (w 0) (w 1) x, w 0, w 1]
      = ∫⁻ y : ℝ, (ENNReal.ofReal
          (2 * Real.sqrt (m ^ 2 + (w 0) ^ 2 + (w 1) ^ 2 + y ^ 2)))⁻¹
          * F ![y, w 0, w 1] := by
  classical
  set φ := boostSlice m β (w 0) (w 1) with hφ
  set G : ℝ → ℝ≥0∞ := fun y => (ENNReal.ofReal
      (2 * Real.sqrt (m ^ 2 + (w 0) ^ 2 + (w 1) ^ 2 + y ^ 2)))⁻¹
    * F ![y, w 0, w 1] with hG
  have hsurj : φ '' Set.univ = Set.univ := by
    rw [Set.image_univ]
    exact (boostSlice_surjective m β (w 0) (w 1) hm hβ).range_eq
  have h1 : ∫⁻ y : ℝ, G y
      = ∫⁻ x : ℝ, ENNReal.ofReal |boostGamma β - β * boostGamma β
          * (x / Real.sqrt (m ^ 2 + (w 0) ^ 2 + (w 1) ^ 2 + x ^ 2))| * G (φ x) := by
    have h := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul
      MeasurableSet.univ
      (fun x _ => (boostSlice_hasDerivAt m β (w 0) (w 1) hm x).hasDerivWithinAt)
      ((boostSlice_strictMono m β (w 0) (w 1) hm hβ).injective.injOn) G
    rw [hsurj] at h
    simpa [Measure.restrict_univ] using h
  rw [h1]
  apply MeasureTheory.lintegral_congr_ae
  refine Filter.Eventually.of_forall (fun x => ?_)
  simp only [hG]
  rw [boostSlice_abs_deriv m β (w 0) (w 1) hm hβ x]
  exact (ennreal_jacobian_cancel _ _ (sliceEnergy_pos m (w 0) (w 1) x hm)
    (by
      have h := boostSlice_jacobian m β (w 0) (w 1) hm hβ x
      rw [h]
      exact mul_pos (boostGamma_pos β hβ)
        (sliceEnergy_sub_pos m β (w 0) (w 1) x hm hβ)) _).symm

/-- **T1 (master identity on the function-space model):** the density
    `1/(2E)` is invariant under the boost's action, for every measurable
    test function `F`. Assembled from the slice identity by Tonelli over
    the transverse plane. -/
theorem boostFnMap_lintegral (m β : ℝ) (hm : 0 < m) (hβ : |β| < 1)
    (F : (Fin 3 → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ v, (ENNReal.ofReal
        (2 * Real.sqrt (m ^ 2 + (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2)))⁻¹
        * F (boostFnMap m β v)
      = ∫⁻ v, (ENNReal.ofReal
          (2 * Real.sqrt (m ^ 2 + (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2)))⁻¹
          * F v := by
  set dens : (Fin 3 → ℝ) → ℝ≥0∞ := fun v => (ENNReal.ofReal
    (2 * Real.sqrt (m ^ 2 + (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2)))⁻¹ with hdens
  have hdens_meas : Measurable dens := by
    have hfun : dens = (fun u : EuclideanSpace ℝ (Fin 3) =>
        (ENNReal.ofReal (2 * shellEnergy m u))⁻¹) ∘ (WithLp.toLp 2) := by
      funext v
      simp only [hdens, Function.comp_apply, shellEnergy_toLp]
    rw [hfun]
    exact (measurable_shellDensity m).comp
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurable
  set σ : (Fin 3 → ℝ) ≃ᵐ (ℝ × (Fin 2 → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0 with hσdef
  have hσsymm : ∀ z : ℝ × (Fin 2 → ℝ), σ.symm z = ![z.1, z.2 0, z.2 1] := by
    intro z
    funext i
    fin_cases i
    · simp [hσdef, MeasurableEquiv.piFinSuccAbove]
    · simp [hσdef, MeasurableEquiv.piFinSuccAbove]
    · simp [hσdef, MeasurableEquiv.piFinSuccAbove]
      rw [show (2 : Fin 3) = Fin.succ (1 : Fin 2) from rfl, Fin.cons_succ]
  have hG_meas : Measurable (fun v => dens v * F (boostFnMap m β v)) :=
    hdens_meas.mul (hF.comp (boostFnMap_measurable m β))
  have hG'_meas : Measurable (fun v => dens v * F v) := hdens_meas.mul hF
  have hpres : MeasurePreserving σ.symm
      ((volume : Measure ℝ).prod (Measure.pi fun _ : Fin 2 => (volume : Measure ℝ)))
      (Measure.pi fun _ : Fin 3 => (volume : Measure ℝ)) :=
    MeasurePreserving.symm σ (volume_preserving_piFinSuccAbove
      (fun _ : Fin 3 => ℝ) 0)
  calc ∫⁻ v, dens v * F (boostFnMap m β v)
      = ∫⁻ v, dens v * F (boostFnMap m β v)
          ∂(Measure.pi fun _ : Fin 3 => (volume : Measure ℝ)) := by
        rw [MeasureTheory.volume_pi]
    _ = ∫⁻ z, dens (σ.symm z) * F (boostFnMap m β (σ.symm z))
          ∂((volume : Measure ℝ).prod (Measure.pi fun _ : Fin 2 => (volume : Measure ℝ))) :=
        (hpres.lintegral_comp_emb σ.symm.measurableEmbedding
          (fun v => dens v * F (boostFnMap m β v))).symm
    _ = ∫⁻ w, ∫⁻ x, dens (σ.symm (x, w)) * F (boostFnMap m β (σ.symm (x, w)))
          ∂volume ∂(Measure.pi fun _ : Fin 2 => (volume : Measure ℝ)) :=
        MeasureTheory.lintegral_prod_symm _
          (hG_meas.comp σ.symm.measurable).aemeasurable
    _ = ∫⁻ w, ∫⁻ x, (ENNReal.ofReal
            (2 * Real.sqrt (m ^ 2 + (w 0) ^ 2 + (w 1) ^ 2 + x ^ 2)))⁻¹
            * F ![boostSlice m β (w 0) (w 1) x, w 0, w 1]
          ∂volume ∂(Measure.pi fun _ : Fin 2 => (volume : Measure ℝ)) := by
        apply MeasureTheory.lintegral_congr_ae
        refine Filter.Eventually.of_forall (fun w => ?_)
        apply MeasureTheory.lintegral_congr_ae
        refine Filter.Eventually.of_forall (fun x => ?_)
        show dens (σ.symm (x, w)) * F (boostFnMap m β (σ.symm (x, w)))
            = (ENNReal.ofReal
                (2 * Real.sqrt (m ^ 2 + (w 0) ^ 2 + (w 1) ^ 2 + x ^ 2)))⁻¹
                * F ![boostSlice m β (w 0) (w 1) x, w 0, w 1]
        rw [hσsymm (x, w), boostFnMap_apply]
        simp only [hdens, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
        rw [show m ^ 2 + x ^ 2 + (w 0) ^ 2 + (w 1) ^ 2
            = m ^ 2 + (w 0) ^ 2 + (w 1) ^ 2 + x ^ 2 from by ring]
    _ = ∫⁻ w, ∫⁻ y, (ENNReal.ofReal
            (2 * Real.sqrt (m ^ 2 + (w 0) ^ 2 + (w 1) ^ 2 + y ^ 2)))⁻¹
            * F ![y, w 0, w 1]
          ∂volume ∂(Measure.pi fun _ : Fin 2 => (volume : Measure ℝ)) := by
        apply MeasureTheory.lintegral_congr_ae
        refine Filter.Eventually.of_forall (fun w => ?_)
        exact boostSlice_lintegral m β hm hβ w F
    _ = ∫⁻ w, ∫⁻ x, dens (σ.symm (x, w)) * F (σ.symm (x, w))
          ∂volume ∂(Measure.pi fun _ : Fin 2 => (volume : Measure ℝ)) := by
        apply MeasureTheory.lintegral_congr_ae
        refine Filter.Eventually.of_forall (fun w => ?_)
        apply MeasureTheory.lintegral_congr_ae
        refine Filter.Eventually.of_forall (fun x => ?_)
        show (ENNReal.ofReal
                (2 * Real.sqrt (m ^ 2 + (w 0) ^ 2 + (w 1) ^ 2 + x ^ 2)))⁻¹
                * F ![x, w 0, w 1]
            = dens (σ.symm (x, w)) * F (σ.symm (x, w))
        rw [hσsymm (x, w)]
        simp only [hdens, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
        rw [show m ^ 2 + (w 0) ^ 2 + (w 1) ^ 2 + x ^ 2
            = m ^ 2 + x ^ 2 + (w 0) ^ 2 + (w 1) ^ 2 from by ring]
    _ = ∫⁻ z, dens (σ.symm z) * F (σ.symm z)
          ∂((volume : Measure ℝ).prod (Measure.pi fun _ : Fin 2 => (volume : Measure ℝ))) :=
        (MeasureTheory.lintegral_prod_symm _
          (hG'_meas.comp σ.symm.measurable).aemeasurable).symm
    _ = ∫⁻ v, dens v * F v ∂(Measure.pi fun _ : Fin 3 => (volume : Measure ℝ)) :=
        hpres.lintegral_comp_emb σ.symm.measurableEmbedding
          (fun v => dens v * F v)
    _ = ∫⁻ v, dens v * F v := by
        rw [← MeasureTheory.volume_pi]

/-- **T1 (the parametrized density identity):** integration against
    `d³u/(2E_u)` is invariant under the boost's action on the
    parametrization, for every measurable test function. -/
theorem boostParamMap_lintegral (m β : ℝ) (hm : 0 < m) (hβ : |β| < 1)
    (f : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ u, (ENNReal.ofReal (2 * shellEnergy m u))⁻¹ * f (boostParamMap m β u)
      = ∫⁻ u, (ENNReal.ofReal (2 * shellEnergy m u))⁻¹ * f u := by
  have htoLp := PiLp.volume_preserving_toLp (Fin 3)
  have step : ∀ g : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞,
      ∫⁻ u, g u = ∫⁻ v, g (WithLp.toLp 2 v) :=
    fun g => (htoLp.lintegral_comp_emb
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding g).symm
  have hpt : ∀ v : Fin 3 → ℝ,
      (ENNReal.ofReal (2 * shellEnergy m (WithLp.toLp 2 v)))⁻¹
          * f (boostParamMap m β (WithLp.toLp 2 v))
        = (ENNReal.ofReal
            (2 * Real.sqrt (m ^ 2 + (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2)))⁻¹
            * (f ∘ WithLp.toLp 2) (boostFnMap m β v) := by
    intro v
    rw [shellEnergy_toLp, boostParamMap_toLp]
    rfl
  have hpt' : ∀ v : Fin 3 → ℝ,
      (ENNReal.ofReal (2 * shellEnergy m (WithLp.toLp 2 v)))⁻¹
          * f (WithLp.toLp 2 v)
        = (ENNReal.ofReal
            (2 * Real.sqrt (m ^ 2 + (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2)))⁻¹
            * (f ∘ WithLp.toLp 2) v := by
    intro v
    rw [shellEnergy_toLp]
    rfl
  rw [step _, step _,
    MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall hpt')]
  exact boostFnMap_lintegral m β hm hβ _
    (hf.comp (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurable)

/-- **T1:** the boost preserves the density measure `d³u/(2E_u)` on the
    parametrization space (the exact analogue of the corpus's rotation
    case `measure_map_rot_density`). -/
theorem boostParamMap_measurePreserving_density (m β : ℝ) (hm : 0 < m)
    (hβ : |β| < 1) :
    Measure.map (boostParamMap m β) (Measure.withDensity volume
      (fun u : EuclideanSpace ℝ (Fin 3) => (ENNReal.ofReal (2 * shellEnergy m u))⁻¹))
    = Measure.withDensity volume
      (fun u : EuclideanSpace ℝ (Fin 3) => (ENNReal.ofReal (2 * shellEnergy m u))⁻¹) := by
  apply Measure.ext
  intro s hs
  have hf_ind : Measurable (s.indicator 1 : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞) :=
    (measurable_const (a := (1 : ℝ≥0∞))).indicator hs
  have hg : Measurable (fun a : EuclideanSpace ℝ (Fin 3) =>
      s.indicator 1 (boostParamMap m β a)) :=
    hf_ind.comp (boostParamMap_measurable m β)
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs,
    MeasureTheory.lintegral_map hf_ind (boostParamMap_measurable m β)]
  have h1 : ∫⁻ a, s.indicator 1 (boostParamMap m β a)
        ∂(Measure.withDensity volume
          fun u => (ENNReal.ofReal (2 * shellEnergy m u))⁻¹)
      = ∫⁻ u, (ENNReal.ofReal (2 * shellEnergy m u))⁻¹
          * s.indicator 1 (boostParamMap m β u) ∂volume :=
    MeasureTheory.lintegral_withDensity_eq_lintegral_mul volume
      (measurable_shellDensity m) hg
  have h2 : ∫⁻ a, s.indicator 1 a
        ∂(Measure.withDensity volume
          fun u => (ENNReal.ofReal (2 * shellEnergy m u))⁻¹)
      = ∫⁻ u, (ENNReal.ofReal (2 * shellEnergy m u))⁻¹
          * s.indicator 1 u ∂volume :=
    MeasureTheory.lintegral_withDensity_eq_lintegral_mul volume
      (measurable_shellDensity m) hf_ind
  rw [h1, h2]
  exact boostParamMap_lintegral m β hm hβ _ hf_ind

/-- The boost's shell action is measurable. -/
theorem measurable_boostShellAct (m β : ℝ) (hm : 0 < m) (hβ : |β| < 1) :
    Measurable (shellActR (boostRestricted β hβ) m hm) := by
  unfold shellActR
  apply Measurable.subtype_mk
  exact (LinearMap.continuous_of_finiteDimensional
    (boostLorentz β hβ).toLin.toLinearMap).measurable.comp
      measurable_subtype_coe

/-- **T1 (Task 4, the measure discharge):** the `x¹`-boost's shell action
    preserves the mass-shell measure `d³p/(2E_p)`, for every
    `β ∈ (-1, 1)`. This discharges `BoostInvariance_window` at all boost
    elements. -/
theorem boost_preserves_massShellMeasure (m β : ℝ) (hm : 0 < m) (hβ : |β| < 1) :
    MeasurePreserving (shellActR (boostRestricted β hβ) m hm)
      (massShellMeasure m hm) (massShellMeasure m hm) := by
  refine ⟨measurable_boostShellAct m β hm hβ, ?_⟩
  unfold massShellMeasure
  rw [Measure.map_map (measurable_boostShellAct m β hm hβ)
    (measurable_shellParam_subtype m hm)]
  have hcomp : shellActR (boostRestricted β hβ) m hm
        ∘ (fun u => (⟨shellParam m u, shellParam_mem m hm u⟩ : massShell m))
      = (fun u => (⟨shellParam m u, shellParam_mem m hm u⟩ : massShell m))
        ∘ boostParamMap m β := by
    funext u
    apply Subtype.ext
    show (boostLorentz β hβ).toLin (shellParam m u)
      = shellParam m (boostParamMap m β u)
    exact boostLin_shellParam m β hm hβ u
  rw [hcomp, ← Measure.map_map (measurable_shellParam_subtype m hm)
    (boostParamMap_measurable m β),
    boostParamMap_measurePreserving_density m β hm hβ]

/-- **T1:** `BoostInvariance_window`, discharged at every `x¹`-boost
    element of the restricted Lorentz group. -/
theorem boostInvariance_window_at_boost (m : ℝ) (hm : 0 < m)
    (β : ℝ) (hβ : |β| < 1) :
    MeasurePreserving
      (fun p : massShell m => ⟨((boostRestricted β hβ : RestrictedLorentz)
          : LorentzGroup).toLin p.val,
        restricted_preserves_shell (boostRestricted β hβ) p.val m hm
          p.property⟩)
      (massShellMeasure m hm) (massShellMeasure m hm) :=
  boost_preserves_massShellMeasure m β hm hβ

/-!
## Task 5 — the cap: boost–rotation factorization

The remaining content of `BoostInvariance_window` is generation of the
restricted Lorentz group by rotations and the `x¹`-boost. We prove it in
the concrete form needed: every `Λ : RestrictedLorentz` factors, at the
level of shell actions, as (rotation) ∘ (`x¹`-boost) ∘ (rotation). The
middle step is the standard one: a Householder reflection in the spatial
variables moves the spatial part of `Λ e₀` onto the `x¹`-axis, where the
`x¹`-boost of Task 4 undoes it; the remainder fixes `e₀`, hence is a
spatial lift by the block lemma below.
-/

/-- The first spatial basis vector `e₁` (the boost axis) in
    `EuclideanSpace ℝ (Fin 3)`. -/
noncomputable def spatialBasisVec : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![1, 0, 0]

theorem spatialBasisVec_zero : spatialBasisVec 0 = 1 := rfl

theorem spatialBasisVec_one : spatialBasisVec 1 = 0 := rfl

theorem spatialBasisVec_two : spatialBasisVec 2 = 0 := rfl

theorem spatialBasisVec_norm : ‖spatialBasisVec‖ = 1 := by
  have h : ‖spatialBasisVec‖ ^ 2 = (1 : ℝ) ^ 2 := by
    rw [euclidean_norm_sq_coord, spatialBasisVec_zero, spatialBasisVec_one,
      spatialBasisVec_two]
    norm_num
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp h

/-- Pairing with the boost axis reads off the first coordinate. -/
theorem inner_spatialBasisVec (u : EuclideanSpace ℝ (Fin 3)) :
    ⟪u, spatialBasisVec⟫ = u 0 := by
  rw [euclidean_inner_sum, spatialBasisVec_zero, spatialBasisVec_one,
    spatialBasisVec_two]
  ring

/-- A linear equivalence preserving the inner product is a linear
    isometry equivalence. -/
def linIsometryEquivOfInnerPreserving
    (f : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3))
    (hf : ∀ u v, ⟪f u, f v⟫ = ⟪u, v⟫) :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toLinearEquiv := f
  norm_map' := by
    intro u
    have h : ‖f u‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hf]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- The Householder reflection across the hyperplane orthogonal to
    `ŵ - e₁`: as a linear map, `u ↦ u - (2/⟪ŵ-e₁, ŵ-e₁⟫) ⟪u, ŵ-e₁⟫ • (ŵ-e₁)`. -/
noncomputable def householderLin (ŵ : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun u := u - ((2 / ⟪ŵ - spatialBasisVec, ŵ - spatialBasisVec⟫)
    * ⟪u, ŵ - spatialBasisVec⟫) • (ŵ - spatialBasisVec)
  map_add' := by
    intro u v
    show (u + v) - ((2 / ⟪ŵ - spatialBasisVec, ŵ - spatialBasisVec⟫)
        * ⟪u + v, ŵ - spatialBasisVec⟫) • (ŵ - spatialBasisVec)
      = (u - ((2 / ⟪ŵ - spatialBasisVec, ŵ - spatialBasisVec⟫)
          * ⟪u, ŵ - spatialBasisVec⟫) • (ŵ - spatialBasisVec))
        + (v - ((2 / ⟪ŵ - spatialBasisVec, ŵ - spatialBasisVec⟫)
          * ⟪v, ŵ - spatialBasisVec⟫) • (ŵ - spatialBasisVec))
    rw [inner_add_left, mul_add, add_smul]
    abel
  map_smul' := by
    intro c u
    show (c • u) - ((2 / ⟪ŵ - spatialBasisVec, ŵ - spatialBasisVec⟫)
        * ⟪c • u, ŵ - spatialBasisVec⟫) • (ŵ - spatialBasisVec)
      = c • (u - ((2 / ⟪ŵ - spatialBasisVec, ŵ - spatialBasisVec⟫)
          * ⟪u, ŵ - spatialBasisVec⟫) • (ŵ - spatialBasisVec))
    rw [real_inner_smul_left]
    module

theorem householderLin_apply (ŵ u : EuclideanSpace ℝ (Fin 3)) :
    householderLin ŵ u
      = u - ((2 / ⟪ŵ - spatialBasisVec, ŵ - spatialBasisVec⟫)
          * ⟪u, ŵ - spatialBasisVec⟫) • (ŵ - spatialBasisVec) := rfl

/-- The reflector's normal vector has `⟪ŵ-e₁, ŵ-e₁⟫ = 2(1 - ŵ₀)`. -/
theorem householderLin_sq (ŵ : EuclideanSpace ℝ (Fin 3)) (hŵ : ‖ŵ‖ = 1) :
    ⟪ŵ - spatialBasisVec, ŵ - spatialBasisVec⟫ = 2 * (1 - ŵ 0) := by
  have hwe : ⟪ŵ, spatialBasisVec⟫ = ŵ 0 := inner_spatialBasisVec ŵ
  have hew : ⟪spatialBasisVec, ŵ ⟫ = ŵ 0 := by
    rw [real_inner_comm]
    exact inner_spatialBasisVec ŵ
  have hee : ⟪spatialBasisVec, spatialBasisVec⟫ = 1 := by
    have h := inner_spatialBasisVec spatialBasisVec
    rwa [spatialBasisVec_zero] at h
  have hww : ⟪ŵ, ŵ⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hŵ]
    norm_num
  rw [inner_sub_left, inner_sub_right, inner_sub_right, hwe, hew, hee, hww]
  ring

/-- For a unit vector `ŵ ≠ e₁`, the first coordinate is `< 1`. -/
theorem householder_one_sub_ne (ŵ : EuclideanSpace ℝ (Fin 3))
    (hŵ : ‖ŵ‖ = 1) (hne : ŵ ≠ spatialBasisVec) : 1 - ŵ 0 ≠ 0 := by
  intro h
  apply hne
  have h0 : ŵ 0 = 1 := by linarith
  have hnorm2 : (ŵ 0) ^ 2 + (ŵ 1) ^ 2 + (ŵ 2) ^ 2 = 1 := by
    have h2 := euclidean_norm_sq_coord ŵ
    rw [hŵ, one_pow] at h2
    exact h2.symm
  have h12 : (ŵ 1) ^ 2 + (ŵ 2) ^ 2 = 0 := by
    rw [h0, one_pow] at hnorm2
    linarith
  have h1 : ŵ 1 = 0 := by
    have hsq : (ŵ 1) ^ 2 = 0 :=
      (add_eq_zero_iff_of_nonneg (sq_nonneg (ŵ 1)) (sq_nonneg (ŵ 2))).mp h12 |>.1
    exact sq_eq_zero_iff.mp hsq
  have h2' : ŵ 2 = 0 := by
    have hsq : (ŵ 2) ^ 2 = 0 :=
      (add_eq_zero_iff_of_nonneg (sq_nonneg (ŵ 1)) (sq_nonneg (ŵ 2))).mp h12 |>.2
    exact sq_eq_zero_iff.mp hsq
  ext i
  fin_cases i
  · show ŵ 0 = spatialBasisVec 0
    rw [spatialBasisVec_zero]
    exact h0
  · show ŵ 1 = spatialBasisVec 1
    rw [spatialBasisVec_one]
    exact h1
  · show ŵ 2 = spatialBasisVec 2
    rw [spatialBasisVec_two]
    exact h2'

theorem householderLin_ne (ŵ : EuclideanSpace ℝ (Fin 3))
    (hŵ : ‖ŵ‖ = 1) (hne : ŵ ≠ spatialBasisVec) :
    ⟪ŵ - spatialBasisVec, ŵ - spatialBasisVec⟫ ≠ 0 := by
  rw [householderLin_sq ŵ hŵ]
  exact mul_ne_zero two_ne_zero (householder_one_sub_ne ŵ hŵ hne)

/-- **T1:** the Householder reflection preserves the inner product. -/
theorem householderLin_inner (ŵ : EuclideanSpace ℝ (Fin 3))
    (hŵ : ‖ŵ‖ = 1) (hne : ŵ ≠ spatialBasisVec)
    (u v : EuclideanSpace ℝ (Fin 3)) :
    ⟪householderLin ŵ u, householderLin ŵ v⟫ = ⟪u, v⟫ := by
  rw [householderLin_apply, householderLin_apply]
  set n := ŵ - spatialBasisVec with hn
  have hnn : ⟪n, n⟫ ≠ 0 := householderLin_ne ŵ hŵ hne
  have hc : (2 / ⟪n, n⟫) * ⟪n, n⟫ = 2 := div_mul_cancel₀ 2 hnn
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm v n]
  linear_combination (⟪u, n⟫ * ⟪v, n⟫ * (2 / ⟪n, n⟫)) * hc

/-- **T1:** the Householder reflection flips the normal component. -/
theorem householderLin_apply_inner (ŵ : EuclideanSpace ℝ (Fin 3))
    (hŵ : ‖ŵ‖ = 1) (hne : ŵ ≠ spatialBasisVec)
    (u : EuclideanSpace ℝ (Fin 3)) :
    ⟪householderLin ŵ u, ŵ - spatialBasisVec⟫
      = -⟪u, ŵ - spatialBasisVec⟫ := by
  have hnn : ⟪ŵ - spatialBasisVec, ŵ - spatialBasisVec⟫ ≠ 0 :=
    householderLin_ne ŵ hŵ hne
  have hc : (2 / ⟪ŵ - spatialBasisVec, ŵ - spatialBasisVec⟫)
      * ⟪ŵ - spatialBasisVec, ŵ - spatialBasisVec⟫ = 2 :=
    div_mul_cancel₀ 2 hnn
  rw [householderLin_apply, inner_sub_left, real_inner_smul_left]
  linear_combination (-⟪u, ŵ - spatialBasisVec⟫) * hc

/-- **T1:** the Householder reflection is involutive. -/
theorem householderLin_involutive (ŵ : EuclideanSpace ℝ (Fin 3))
    (hŵ : ‖ŵ‖ = 1) (hne : ŵ ≠ spatialBasisVec)
    (u : EuclideanSpace ℝ (Fin 3)) :
    householderLin ŵ (householderLin ŵ u) = u := by
  have e1 : householderLin ŵ (householderLin ŵ u)
      = householderLin ŵ u
        - ((2 / ⟪ŵ - spatialBasisVec, ŵ - spatialBasisVec⟫)
          * ⟪householderLin ŵ u, ŵ - spatialBasisVec⟫)
          • (ŵ - spatialBasisVec) :=
    householderLin_apply ŵ _
  rw [e1, householderLin_apply_inner ŵ hŵ hne u, householderLin_apply,
    mul_neg, neg_smul, sub_neg_eq_add, sub_add_cancel]

/-- The Householder reflection as a linear equivalence (its own inverse). -/
noncomputable def householderEquiv (ŵ : EuclideanSpace ℝ (Fin 3))
    (hŵ : ‖ŵ‖ = 1) (hne : ŵ ≠ spatialBasisVec) :
    EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearEquiv.ofLinearMap (householderLin ŵ) (householderLin ŵ)
    (by apply LinearMap.ext
        intro u
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        exact householderLin_involutive ŵ hŵ hne u)
    (by apply LinearMap.ext
        intro u
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        exact householderLin_involutive ŵ hŵ hne u)

/-- The Householder reflection as a linear isometry equivalence. -/
noncomputable def householder (ŵ : EuclideanSpace ℝ (Fin 3))
    (hŵ : ‖ŵ‖ = 1) (hne : ŵ ≠ spatialBasisVec) :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  linIsometryEquivOfInnerPreserving (householderEquiv ŵ hŵ hne)
    (householderLin_inner ŵ hŵ hne)

/-- **T1:** the Householder reflection sends `ŵ` to the boost axis `e₁`. -/
theorem householderLin_apply_self (ŵ : EuclideanSpace ℝ (Fin 3))
    (hŵ : ‖ŵ‖ = 1) (hne : ŵ ≠ spatialBasisVec) :
    householderLin ŵ ŵ = spatialBasisVec := by
  have hnn2 : ⟪ŵ - spatialBasisVec, ŵ - spatialBasisVec⟫
      = 2 * (1 - ŵ 0) := householderLin_sq ŵ hŵ
  have h1ne : (1 - ŵ 0) ≠ 0 := householder_one_sub_ne ŵ hŵ hne
  have hŵn : ⟪ŵ, ŵ - spatialBasisVec⟫ = 1 - ŵ 0 := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, hŵ,
      inner_spatialBasisVec, one_pow]
  have hcoef : (2 / ⟪ŵ - spatialBasisVec, ŵ - spatialBasisVec⟫)
      * (1 - ŵ 0) = 1 := by
    rw [hnn2]
    have hne2 : (2 : ℝ) * (1 - ŵ 0) ≠ 0 := mul_ne_zero two_ne_zero h1ne
    field_simp
  rw [householderLin_apply, hŵn, hcoef, one_smul]
  abel

/-- The spatial block of a Lorentz transformation: the linear map on ℝ³
    induced on spatial parts of vectors with vanishing time component. -/
noncomputable def spatialBlock (L : LorentzGroup) :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  spatialPartLin.comp (L.toLin.toLinearMap.comp
    (finFourEquiv.symm.toLinearMap.comp (LinearMap.inr ℝ ℝ _)))

theorem spatialBlock_apply (L : LorentzGroup) (u : EuclideanSpace ℝ (Fin 3)) :
    spatialBlock L u
      = spatialPartLin (L.toLin (finFourEquiv.symm (0, u))) := by
  simp [spatialBlock]

theorem spatialPartLin_emb (u : EuclideanSpace ℝ (Fin 3)) :
    spatialPartLin (finFourEquiv.symm (0, u)) = u := by
  ext j
  rw [spatialPartLin_apply]
  fin_cases j <;> rfl

theorem spatialPartLin_timeVec : spatialPartLin timeVec = 0 := by
  ext j
  rw [spatialPartLin_apply]
  fin_cases j <;> simp [timeVec]

/-- Every Minkowski vector decomposes into its time part along `e₀` plus
    its embedded spatial part. -/
theorem minkowski_decomp (p : Minkowski) :
    p = (p 0) • timeVec + finFourEquiv.symm (0, spatialPartLin p) := by
  apply finFourEquiv.injective
  rw [map_add, map_smul, LinearEquiv.apply_symm_apply]
  have htv : finFourEquiv timeVec = (1, 0) := by
    apply Prod.ext
    · rw [finFourEquiv_fst]
      rfl
    · rw [finFourEquiv_snd]
      show spatialPartLin timeVec = (0 : EuclideanSpace ℝ (Fin 3))
      exact spatialPartLin_timeVec
  rw [htv]
  apply Prod.ext
  · rw [finFourEquiv_fst]
    simp
  · rw [finFourEquiv_snd]
    simp

/-- **T1:** a Lorentz transformation fixing `e₀` fixes every time
    component. -/
theorem lorentz_time_component (L : LorentzGroup)
    (hL : L.toLin timeVec = timeVec) (p : Minkowski) :
    (L.toLin p) 0 = p 0 := by
  have h := L.preserves p timeVec
  rw [hL, minkowskiInner_timeVec_right, minkowskiInner_timeVec_right] at h
  exact h

/-- **T1:** a Lorentz transformation fixing `e₀` acts on spatial parts
    through its spatial block. -/
theorem spatialPartLin_lorentz (L : LorentzGroup)
    (hL : L.toLin timeVec = timeVec) (p : Minkowski) :
    spatialPartLin (L.toLin p) = spatialBlock L (spatialPartLin p) := by
  have hstep : L.toLin p
      = (p 0) • timeVec
        + L.toLin (finFourEquiv.symm (0, spatialPartLin p)) := by
    have h2 := congrArg (⇑L.toLin) (minkowski_decomp p)
    rwa [map_add, map_smul, hL] at h2
  rw [hstep, map_add, map_smul, spatialPartLin_timeVec, smul_zero, zero_add,
    spatialBlock_apply]

/-- **T1:** the spatial block of a Lorentz transformation fixing `e₀`
    preserves the Euclidean inner product. -/
theorem spatialBlock_inner (L : LorentzGroup)
    (hL : L.toLin timeVec = timeVec) (u v : EuclideanSpace ℝ (Fin 3)) :
    ⟪spatialBlock L u, spatialBlock L v⟫ = ⟪u, v⟫ := by
  have hpres := L.preserves (finFourEquiv.symm (0, u))
    (finFourEquiv.symm (0, v))
  rw [minkowskiInner_spatial, minkowskiInner_spatial] at hpres
  rw [spatialPartLin_emb, spatialPartLin_emb] at hpres
  have he0 : ∀ w : EuclideanSpace ℝ (Fin 3),
      (finFourEquiv.symm (0, w)) 0 = 0 := by
    intro w
    have h := finFourEquiv_fst (finFourEquiv.symm (0, w))
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  rw [lorentz_time_component L hL, lorentz_time_component L hL, he0, he0]
    at hpres
  rw [spatialBlock_apply, spatialBlock_apply]
  simp only [zero_mul, zero_sub] at hpres
  exact neg_inj.mp hpres

/-- **T1 (the block lemma):** a Lorentz transformation fixing `e₀` is a
    spatial lift. -/
theorem lorentz_fixing_timeVec_is_spatialLift (L : LorentzGroup)
    (hL : L.toLin timeVec = timeVec) :
    ∃ R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
      L.toLin = spatialLiftLin R := by
  have hinj : Function.Injective (spatialBlock L) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h0 : ⟪u, u⟫ = 0 := by
      have h := spatialBlock_inner L hL u u
      rw [hu, inner_zero_left] at h
      exact h.symm
    exact inner_self_eq_zero.mp h0
  have hsurj : Function.Surjective (spatialBlock L) :=
    LinearMap.injective_iff_surjective.mp hinj
  refine ⟨linIsometryEquivOfInnerPreserving
    (LinearEquiv.ofBijective (spatialBlock L) ⟨hinj, hsurj⟩)
    (spatialBlock_inner L hL), ?_⟩
  apply LinearEquiv.ext
  intro p
  apply finFourEquiv.injective
  rw [spatialLiftLin_apply]
  show ((L.toLin p) 0, spatialPartLin (L.toLin p))
    = (p 0, spatialBlock L (spatialPartLin p))
  exact Prod.ext (lorentz_time_component L hL p)
    (spatialPartLin_lorentz L hL p)

/-- **T1:** the spatial lift of the inverse isometry is the inverse of
    the spatial lift. -/
theorem spatialLiftLin_symm
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    (spatialLiftLin R).symm = spatialLiftLin R.symm := by
  apply LinearEquiv.ext
  intro p
  apply finFourEquiv.injective
  have h := spatialLiftLin_apply R ((spatialLiftLin R).symm p)
  rw [LinearEquiv.apply_symm_apply] at h
  have hfst := congrArg Prod.fst h
  rw [finFourEquiv_fst] at hfst
  have hsnd := congrArg Prod.snd h
  rw [finFourEquiv_snd] at hsnd
  have hsq : spatialPartLin ((spatialLiftLin R).symm p)
      = R.symm (spatialPartLin p) := by
    apply R.injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact hsnd.symm
  rw [spatialLiftLin_apply]
  show (((spatialLiftLin R).symm p) 0,
      spatialPartLin ((spatialLiftLin R).symm p))
    = (p 0, R.symm (spatialPartLin p))
  exact Prod.ext hfst.symm hsq

/-- The `toLin` field of a spatial lift is the spatial lift linear
    equivalence (definitional). -/
theorem spatialLift_toLin
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    (spatialLift R).toLin = spatialLiftLin R := rfl

/-- The spatial lift of the identity isometry is the identity. -/
theorem spatialLiftLin_one :
    spatialLiftLin (1 : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin 3)) = LinearEquiv.refl ℝ Minkowski := by
  apply LinearEquiv.ext
  intro p
  apply finFourEquiv.injective
  rw [spatialLiftLin_apply]
  rfl

/-- The Householder isometry equivalence applies as the Householder
    linear map (definitional). -/
theorem householder_apply (ŵ : EuclideanSpace ℝ (Fin 3))
    (hŵ : ‖ŵ‖ = 1) (hne : ŵ ≠ spatialBasisVec)
    (u : EuclideanSpace ℝ (Fin 3)) :
    householder ŵ hŵ hne u = householderLin ŵ u := rfl

/-- **T1 (THE CAP): the full `BoostInvariance_window`, discharged.**
    Every restricted Lorentz transformation factors, at the level of
    shell actions, as a spatial rotation, an `x¹`-boost, and a spatial
    rotation; each factor preserves `massShellMeasure` (rotations by
    `spatialLift_preserves_measure`, the boost by
    `boost_preserves_massShellMeasure`). Hence the mass-shell measure
    `d³p/(2E_p)` is invariant under the full restricted Lorentz group. -/
theorem boostInvariance_window_proved (m : ℝ) (hm : 0 < m) :
    BoostInvariance_window m hm := by
  intro Λ
  obtain ⟨hprop, hortho⟩ := Λ.property
  generalize hv : (Λ : LorentzGroup).toLin timeVec = v
  generalize hs : spatialPartLin v = s
  have hv0 : 0 < v 0 := by
    have h : IsOrthoChronous (Λ : LorentzGroup) := hortho
    unfold IsOrthoChronous at h
    rwa [hv] at h
  have hnorm : (v 0) ^ 2 - ‖s‖ ^ 2 = 1 := by
    have h := (Λ : LorentzGroup).preserves timeVec timeVec
    rw [hv, minkowskiInner_timeVec_self, minkowskiInner_spatial, hs,
      real_inner_self_eq_norm_sq] at h
    have h2 : (v 0) ^ 2 = v 0 * v 0 := by ring
    rw [h2]
    exact h
  have hslt : ‖s‖ < v 0 := by
    have h1 : ‖s‖ ^ 2 < (v 0) ^ 2 := by linarith [hnorm]
    have h2 := abs_lt_of_sq_lt_sq h1 (le_of_lt hv0)
    rwa [abs_of_nonneg (norm_nonneg s)] at h2
  have hvv : v = ![v 0, s 0, s 1, s 2] := by
    have e0 : s 0 = v 1 := by
      rw [← hs, spatialPartLin_apply,
        show Fin.succ (0 : Fin 3) = (1 : Fin 4) from rfl]
    have e1 : s 1 = v 2 := by
      rw [← hs, spatialPartLin_apply,
        show Fin.succ (1 : Fin 3) = (2 : Fin 4) from rfl]
    have e2 : s 2 = v 3 := by
      rw [← hs, spatialPartLin_apply,
        show Fin.succ (2 : Fin 3) = (3 : Fin 4) from rfl]
    funext i
    fin_cases i
    · rfl
    · show v 1 = s 0
      exact e0.symm
    · show v 2 = s 1
      exact e1.symm
    · show v 3 = s 2
      exact e2.symm
  -- Choose the spatial rotation moving `s` onto the `x¹`-axis.
  obtain ⟨R₁, hA⟩ : ∃ R₁ : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin 3),
      (spatialLift R₁).toLin v = ![v 0, ‖s‖, 0, 0] := by
    by_cases hs0 : s = 0
    · refine ⟨1, ?_⟩
      conv_lhs => rw [spatialLift_toLin, spatialLiftLin_one,
        LinearEquiv.refl_apply, hvv]
      rw [hs0]
      simp
    · have hsnz : ‖s‖ ≠ 0 := by
        rw [norm_ne_zero_iff]
        exact hs0
      by_cases hŵe : ‖s‖⁻¹ • s = spatialBasisVec
      · refine ⟨1, ?_⟩
        have hs_eq : s = ‖s‖ • spatialBasisVec := by
          have hs_eq2 : ‖s‖ • (‖s‖⁻¹ • s) = s := by
            rw [smul_smul, mul_inv_cancel₀ hsnz, one_smul]
          rw [← hŵe]
          exact hs_eq2.symm
        have hs0' : s 0 = ‖s‖ := by
          conv_lhs => rw [hs_eq]
          simp [PiLp.smul_apply, smul_eq_mul, spatialBasisVec_zero]
        have hs1' : s 1 = 0 := by
          conv_lhs => rw [hs_eq]
          simp [PiLp.smul_apply, smul_eq_mul, spatialBasisVec_one]
        have hs2' : s 2 = 0 := by
          conv_lhs => rw [hs_eq]
          simp [PiLp.smul_apply, smul_eq_mul, spatialBasisVec_two]
        conv_lhs => rw [spatialLift_toLin, spatialLiftLin_one,
          LinearEquiv.refl_apply, hvv]
        rw [hs0', hs1', hs2']
      · set ŵ : EuclideanSpace ℝ (Fin 3) := ‖s‖⁻¹ • s with hŵdef
        have hŵnorm : ‖ŵ‖ = 1 := by
          rw [hŵdef, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (norm_nonneg s)),
            inv_mul_cancel₀ hsnz]
        have hs_eq2 : ‖s‖ • ŵ = s := by
          rw [hŵdef, smul_smul, mul_inv_cancel₀ hsnz, one_smul]
        refine ⟨householder ŵ hŵnorm hŵe, ?_⟩
        apply finFourEquiv.injective
        rw [spatialLift_toLin, spatialLiftLin_apply, hs]
        show (v 0, householder ŵ hŵnorm hŵe s)
          = ((![v 0, ‖s‖, 0, 0] : Minkowski) 0,
            spatialPartLin ![v 0, ‖s‖, 0, 0])
        apply Prod.ext
        · rfl
        · conv_lhs => rw [← hs_eq2]
          rw [householder_apply, map_smul,
            householderLin_apply_self ŵ hŵnorm hŵe]
          ext j
          rw [spatialPartLin_apply]
          fin_cases j <;> simp [PiLp.smul_apply, smul_eq_mul,
            spatialBasisVec_zero, spatialBasisVec_one, spatialBasisVec_two]
  -- The boost undoing the rotated `Λ e₀`.
  set β : ℝ := -‖s‖ / v 0 with hβdef
  have hv0' : v 0 ≠ 0 := ne_of_gt hv0
  have hβ : |β| < 1 := by
    rw [hβdef, abs_div, abs_neg, abs_of_nonneg (norm_nonneg s),
      abs_of_pos hv0]
    exact (div_lt_one hv0).mpr hslt
  have hγ : boostGamma β = v 0 := by
    have hnorm' : ‖s‖ ^ 2 = (v 0) ^ 2 - 1 := by linarith [hnorm]
    have e1 : ‖s‖ ^ 2 / (v 0) ^ 2 = 1 - 1 / (v 0) ^ 2 := by
      rw [hnorm', sub_div, div_self (pow_ne_zero 2 hv0')]
    have hβ2 : β ^ 2 = ‖s‖ ^ 2 / (v 0) ^ 2 := by
      rw [hβdef, neg_div, neg_sq, div_pow]
    have h1m : 1 - β ^ 2 = (1 / v 0) ^ 2 := by
      calc 1 - β ^ 2 = 1 - ‖s‖ ^ 2 / (v 0) ^ 2 := by rw [hβ2]
      _ = 1 / (v 0) ^ 2 := by
          rw [e1]
          ring
      _ = (1 / v 0) ^ 2 := by rw [div_pow, one_pow]
    unfold boostGamma
    rw [h1m, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 / v 0), one_div,
      inv_inv]
  have hB : (boostLorentz β hβ).toLin timeVec = ![v 0, ‖s‖, 0, 0] := by
    have hβv : -β * v 0 = ‖s‖ := by
      rw [hβdef, neg_div, neg_neg]
      exact div_mul_cancel₀ ‖s‖ hv0'
    rw [boostLorentz_timeVec, hγ, hβv]
  -- The remainder fixes `e₀`, hence is a spatial lift.
  set L₂ : LorentzGroup := (boostLorentz β hβ)⁻¹ * spatialLift R₁
    * (Λ : LorentzGroup) with hL₂def
  have hL₂fix : L₂.toLin timeVec = timeVec := by
    show (boostLorentz β hβ).toLin.symm
        ((spatialLift R₁).toLin ((Λ : LorentzGroup).toLin timeVec))
      = timeVec
    rw [hv, hA, ← hB]
    exact LinearEquiv.symm_apply_apply _ _
  obtain ⟨R₂, hR₂⟩ := lorentz_fixing_timeVec_is_spatialLift L₂ hL₂fix
  have hGfac : (Λ : LorentzGroup)
      = (spatialLift R₁)⁻¹ * boostLorentz β hβ * L₂ := by
    rw [hL₂def]
    group
  -- Factor the shell action.
  have hval : ∀ p : massShell m, (shellActR Λ m hm p).val
      = (spatialLift R₁.symm).toLin
        ((boostLorentz β hβ).toLin (L₂.toLin p.val)) := by
    intro p
    show (Λ : LorentzGroup).toLin p.val
      = (spatialLift R₁.symm).toLin
        ((boostLorentz β hβ).toLin (L₂.toLin p.val))
    rw [hGfac]
    simp only [LorentzGroup.mul_toLin, LorentzGroup.inv_toLin,
      LinearEquiv.trans_apply]
    rw [spatialLift_toLin, spatialLift_toLin, spatialLiftLin_symm]
  have hcomp_val : ∀ p : massShell m,
      ((shellActLift R₁.symm m ∘ shellActR (boostRestricted β hβ) m hm
        ∘ shellActLift R₂ m) p).val
      = (spatialLift R₁.symm).toLin
        ((boostLorentz β hβ).toLin (L₂.toLin p.val)) := by
    intro p
    show (spatialLift R₁.symm).toLin
        ((boostLorentz β hβ).toLin ((spatialLift R₂).toLin p.val))
      = (spatialLift R₁.symm).toLin
        ((boostLorentz β hβ).toLin (L₂.toLin p.val))
    rw [spatialLift_toLin, spatialLift_toLin, ← hR₂]
  have hfac : shellActR Λ m hm
      = shellActLift R₁.symm m ∘ shellActR (boostRestricted β hβ) m hm
        ∘ shellActLift R₂ m := by
    funext p
    apply Subtype.ext
    rw [hval p, hcomp_val p]
  -- Assemble the three measure-preserving factors.
  have hrot1 : MeasurePreserving (shellActLift R₂ m)
      (massShellMeasure m hm) (massShellMeasure m hm) :=
    ⟨measurable_shellActLift R₂ m, spatialLift_preserves_measure R₂ m hm⟩
  have hboost : MeasurePreserving (shellActR (boostRestricted β hβ) m hm)
      (massShellMeasure m hm) (massShellMeasure m hm) :=
    boost_preserves_massShellMeasure m β hm hβ
  have hrot2 : MeasurePreserving (shellActLift R₁.symm m)
      (massShellMeasure m hm) (massShellMeasure m hm) :=
    ⟨measurable_shellActLift R₁.symm m,
      spatialLift_preserves_measure R₁.symm m hm⟩
  show MeasurePreserving (shellActR Λ m hm) (massShellMeasure m hm)
    (massShellMeasure m hm)
  rw [hfac]
  exact hrot2.comp (hboost.comp hrot1)

/-!
## Axiom audit

Each headline result depends only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no `sorry`, no extra
axioms. Verified by the `#print axioms` commands below.
-/

#print axioms boostRestricted
#print axioms boostLin_shellParam
#print axioms boostSlice_jacobian
#print axioms boostSlice_abs_deriv
#print axioms boost_preserves_massShellMeasure
#print axioms boostInvariance_window_proved

end ThetLogos
