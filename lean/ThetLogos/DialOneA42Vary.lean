/-
# A42-VARY: the finite-moment ratios are not constant in the Yukawa inputs

Brick A42-VARY (Q1). Only deliverable: fire kill **K-Q1-A42-VARY** at T1.
Governing spec: `q1-extraction-rescope-2026-11-08.md` §2.3 (audit §2.2).
NO CLAIM. Dial 1 = 0: a kill of a circular target is hygiene, not derivation.

For `D_F = smDirac yNu yE yU yD yR`, write
`M2 := Matrix.trace (D_F ^ 2)` and `M4 := Matrix.trace (D_F ^ 4)`.
Both are proved polynomials in the free Yukawa inputs (landed T1:
`tr_DF_sq_yukawa`, `tr_DF_fourth_yukawa` in `SpectralActionFinite`).
This module proves, at exhibited settings:

(i) `M4 / M2 = 1` at `(yE = 1, rest 0)` and `M4 / M2 = 4` at
    `(yE = 2, rest 0)` — the raw ratio is not constant in the inputs;
(ii) `M4 / M2 ^ 2 = 1 / 4` at `(yE = 1, rest 0)` and `M4 / M2 ^ 2 = 1 / 2`
    at `(yR = 1, rest 0)` — the dimensionless normalization is not
    constant either;
(iii) ∀-corollaries: no constant `c : ℂ` has `M4 = c * M2` at all
    settings, and none has `M4 = c * M2 ^ 2` at all settings.

Hence the α0⁻¹-from-a4/a2 target, in every form whose right-hand side is
a fixed normalization of the finite moments M2, M4, is not a Dial-1
derivation: its value moves when measured inputs move (K-Q1-A42-VARY).
The finite moments are NOT labelled a2/a4 here (K-Q1-A42-PROXY).
-/
import ThetLogos.SpectralActionFinite

namespace ThetLogos

namespace DialOneA42Vary

/-- (i), first setting: at `(yNu, yE, yU, yD, yR) = (0, 1, 0, 0, 0)`,
    `M2 = 4` and `M4 = 4` by the landed formulas, so `M4 / M2 = 1`. -/
theorem ratio_one_at_yE_one :
    Matrix.trace ((smDirac 0 1 0 0 0) ^ 4) / Matrix.trace ((smDirac 0 1 0 0 0) ^ 2)
      = 1 := by
  rw [tr_DF_sq_yukawa, tr_DF_fourth_yukawa]
  norm_num [Complex.normSq]

/-- (i), second setting: at `(0, 2, 0, 0, 0)`, `M2 = 16` and `M4 = 64`
    by the landed formulas, so `M4 / M2 = 4 ≠ 1`: the raw ratio moves. -/
theorem ratio_four_at_yE_two :
    Matrix.trace ((smDirac 0 2 0 0 0) ^ 4) / Matrix.trace ((smDirac 0 2 0 0 0) ^ 2)
      = 4 := by
  rw [tr_DF_sq_yukawa, tr_DF_fourth_yukawa]
  norm_num [Complex.normSq]

/-- (ii), first setting: at `(0, 1, 0, 0, 0)`, `M4 / M2 ^ 2 = 4 / 16 = 1 / 4`. -/
theorem normRatio_quarter_at_yE_one :
    Matrix.trace ((smDirac 0 1 0 0 0) ^ 4) / (Matrix.trace ((smDirac 0 1 0 0 0) ^ 2)) ^ 2
      = 1 / 4 := by
  rw [tr_DF_sq_yukawa, tr_DF_fourth_yukawa]
  norm_num [Complex.normSq]

/-- (ii), second setting: at `(0, 0, 0, 0, 1)` (Majorana only),
    `M2 = 2` and `M4 = 2`, so `M4 / M2 ^ 2 = 2 / 4 = 1 / 2 ≠ 1 / 4`:
    the dimensionless normalization moves too. -/
theorem normRatio_half_at_yR_one :
    Matrix.trace ((smDirac 0 0 0 0 1) ^ 4) / (Matrix.trace ((smDirac 0 0 0 0 1) ^ 2)) ^ 2
      = 1 / 2 := by
  rw [tr_DF_sq_yukawa, tr_DF_fourth_yukawa]
  norm_num [Complex.normSq]

/-- (iii), raw form: there is no constant `c : ℂ` with `M4 = c * M2`
    at all Yukawa settings. At `yE = 1` this forces `c = 1`; at
    `yE = 2` it forces `c = 4`. -/
theorem no_constant_ratio :
    ¬ ∃ c : ℂ, ∀ yNu yE yU yD yR : ℂ,
      Matrix.trace ((smDirac yNu yE yU yD yR) ^ 4)
        = c * Matrix.trace ((smDirac yNu yE yU yD yR) ^ 2) := by
  rintro ⟨c, hc⟩
  have h1 := hc 0 1 0 0 0
  have h2 := hc 0 2 0 0 0
  have hM4a : Matrix.trace ((smDirac 0 1 0 0 0) ^ 4) = 4 := by
    rw [tr_DF_fourth_yukawa]; norm_num [Complex.normSq]
  have hM2a : Matrix.trace ((smDirac 0 1 0 0 0) ^ 2) = 4 := by
    rw [tr_DF_sq_yukawa]; norm_num [Complex.normSq]
  have hM4b : Matrix.trace ((smDirac 0 2 0 0 0) ^ 4) = 64 := by
    rw [tr_DF_fourth_yukawa]; norm_num [Complex.normSq]
  have hM2b : Matrix.trace ((smDirac 0 2 0 0 0) ^ 2) = 16 := by
    rw [tr_DF_sq_yukawa]; norm_num [Complex.normSq]
  rw [hM4a, hM2a] at h1
  rw [hM4b, hM2b] at h2
  -- h1 : (4 : ℂ) = c * 4, h2 : (64 : ℂ) = c * 16
  have hc1 : c = 1 := by linear_combination -h1 / 4
  have hc4 : c = 4 := by linear_combination -h2 / 16
  rw [hc1] at hc4
  norm_num at hc4

/-- (iii), dimensionless form: there is no constant `c : ℂ` with
    `M4 = c * M2 ^ 2` at all Yukawa settings. At `yE = 1` this forces
    `c = 1 / 4`; at `yR = 1` it forces `c = 1 / 2`. -/
theorem no_constant_normRatio :
    ¬ ∃ c : ℂ, ∀ yNu yE yU yD yR : ℂ,
      Matrix.trace ((smDirac yNu yE yU yD yR) ^ 4)
        = c * (Matrix.trace ((smDirac yNu yE yU yD yR) ^ 2)) ^ 2 := by
  rintro ⟨c, hc⟩
  have h1 := hc 0 1 0 0 0
  have h2 := hc 0 0 0 0 1
  have hM4a : Matrix.trace ((smDirac 0 1 0 0 0) ^ 4) = 4 := by
    rw [tr_DF_fourth_yukawa]; norm_num [Complex.normSq]
  have hM2a : Matrix.trace ((smDirac 0 1 0 0 0) ^ 2) = 4 := by
    rw [tr_DF_sq_yukawa]; norm_num [Complex.normSq]
  have hM4b : Matrix.trace ((smDirac 0 0 0 0 1) ^ 4) = 2 := by
    rw [tr_DF_fourth_yukawa]; norm_num [Complex.normSq]
  have hM2b : Matrix.trace ((smDirac 0 0 0 0 1) ^ 2) = 2 := by
    rw [tr_DF_sq_yukawa]; norm_num [Complex.normSq]
  rw [hM4a, hM2a] at h1
  rw [hM4b, hM2b] at h2
  -- h1 : (4 : ℂ) = c * 4 ^ 2, h2 : (2 : ℂ) = c * 2 ^ 2
  have hc1 : c = 1 / 4 := by linear_combination -h1 / 16
  have hc2 : c = 1 / 2 := by linear_combination -h2 / 4
  rw [hc1] at hc2
  norm_num at hc2

end DialOneA42Vary

end ThetLogos
