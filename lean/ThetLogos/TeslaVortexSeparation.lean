import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import ThetLogos.GibbsSpan
import ThetLogos.FluxClassification

open Matrix Filter Topology
open ThetLogos.GibbsSpan ThetLogos.FluxClassification

namespace ThetLogos.TeslaVortexSeparation

/-!
# ThetLogos.TeslaVortexSeparation — Tesla Vortex Modular Dynamics, Rung 1:
# thermal separation (T1 target, finite level)

STATUS: STANDS WHOLE (T1) — landed 2026-10-22 under Jeff's commission
(widget tap + text, 2026-10-22 14:55 EDT). Charter:
`whitepaper/tesla-vortex-modular-dynamics-scoping-2026-10-22.md`.
Parent-verified: independent md5, hygiene scan, strict recount and
in-tree build green; dossier
`whitepaper/tesla-vortex-modular-dynamics-rung1-2026-10-22.md`.

## The idea, at the tier it can carry

Jeff's chain (2026-10-22): a thermal density matrix creates charge
separation through thermodynamics; that separation creates the
proton/neutron nuclear charge, trapping electrons in magnetic
suspension. Rung 1 builds ONLY the first link, in the finite form that
proves: a Gibbs state over two energy-split sectors populates the
sectors unequally, and the normalized thermal expectation of a
sector-signed charge observable — the *separation* — is an exact,
explicit function of the inverse temperature `β` and the energy gap.
Thermodynamics converts an energy gap into a population separation;
it does not create the gap.

## Fences (on the face, per the charter)

- **K-TV1:** `q` and the energies `E` are INPUTS. No charge values are
  derived; the `±q` here are not the proton, neutron, or electron
  charges, and nothing in this module models a nucleus or an atom.
- **K-TV2:** Links 2–3 of Jeff's chain (separation creating the nuclear
  charge; electrons trapped in magnetic suspension) are NOT modeled in
  Rung 1. They stand as Jeff's T5 picture, with the standing NO-GOs the
  record holds (charge assignments pinned by measurement, verdict
  2026-10-22; charges labeled INPUTS in SM-Match and in the
  circularity ledger, Row 2).
- **K-TV3:** "Tesla Vortex" is Jeff's coinage for his electric heat
  gauge vortex (pinned 2026-10-21) — not Tesla's devices, not 3-6-9
  numerology.

## Contents

- §0: the separation (T2 definition), its independence of the Gibbs
  normalization convention, the exact exponential formula (T1), and
  the tanh form (T1 corollary).
- §1: separation vanishes iff the energies agree, at `β > 0` (T1);
  the two degenerate cases (equal energies, `β = 0`) vanish outright.
- §2: the absolute-separation representation
  `|S| = |q| · (1 − e^{−β|gap|}) / (1 + e^{−β|gap|})` at `β ≥ 0`, and
  strict monotonicity of `|S|` in `β` for a nonzero gap (T1).
- §3: the finite bound `|S| < |q|` at every `β` (T1), saturation
  `|S| → |q|` as `β → ∞` for a nonzero gap (T1), and the signed
  limits `S → q` / `S → −q` by gap sign (T1).
- §4: the flux hook (T1, via FluxClassification): at `β > 0`, a Dirac
  operator with a nonzero cross-sector entry has nonzero modular flux
  at the Gibbs state's `K = diagModularK w`; the flux vanishes iff
  `D` has no entries across distinct energy sectors.
-/

-- ============================================================================
-- §0. The separation and its exact formula (Targets T1)
-- ============================================================================

/-- **Thermal separation** (Tier T2 — definition): for two sectors
indexed by `Fin 2`, energies `E : Fin 2 → ℝ`, an INPUT sector charge
`q` (sector `0` carries `+q`, sector `1` carries `−q` — fence K-TV1:
`q` and `E` are inputs, no charge values are derived), and inverse
temperature `β`, the separation is the normalized thermal expectation
of the charge observable under the Gibbs weights `gibbsWeightsE`:

    `S(β) = q · (w₀ − w₁) / (w₀ + w₁)`,

where `w = gibbsWeightsE β E 0` (the normalization convention
`logZ = 0` is immaterial by `thermalSeparation_eq_of_logZ` below:
any common rescaling of the weights cancels in the ratio). -/
noncomputable def thermalSeparation (q : ℝ) (E : Fin 2 → ℝ) (β : ℝ) : ℝ :=
  q * (gibbsWeightsE β E (0 : ℝ) (0 : Fin 2)
        - gibbsWeightsE β E (0 : ℝ) (1 : Fin 2))
    / (gibbsWeightsE β E (0 : ℝ) (0 : Fin 2)
        + gibbsWeightsE β E (0 : ℝ) (1 : Fin 2))

/-- The `logZ = 0` Gibbs weights are bare exponentials (Tier T1 —
proved): `gibbsWeightsE β E 0 j = exp(−(β · E j))`. -/
theorem gibbsWeightsE_zero_logZ (β : ℝ) (E : Fin 2 → ℝ) (j : Fin 2) :
    gibbsWeightsE β E (0 : ℝ) j = Real.exp (-(β * E j)) := by
  show Real.exp (-(β * E j + 0)) = Real.exp (-(β * E j))
  rw [add_zero]

/-- **Normalization independence** (Tier T1 — proved): the separation
does not depend on the Gibbs normalization convention — with weights
`gibbsWeightsE β E logZ` at ANY `logZ`, the same ratio results,
because the common factor `exp(−logZ)` cancels between numerator and
denominator. -/
theorem thermalSeparation_eq_of_logZ (q : ℝ) (E : Fin 2 → ℝ) (β logZ : ℝ) :
    q * (gibbsWeightsE β E logZ (0 : Fin 2) - gibbsWeightsE β E logZ (1 : Fin 2))
        / (gibbsWeightsE β E logZ (0 : Fin 2) + gibbsWeightsE β E logZ (1 : Fin 2))
      = thermalSeparation q E β := by
  have key : ∀ j : Fin 2, gibbsWeightsE β E logZ j
      = Real.exp (-logZ) * Real.exp (-(β * E j)) := by
    intro j
    show Real.exp (-(β * E j + logZ)) = Real.exp (-logZ) * Real.exp (-(β * E j))
    rw [← Real.exp_add]
    congr 1
    ring
  have ha : (0 : ℝ) < Real.exp (-(β * E (0 : Fin 2))) := Real.exp_pos _
  have hb : (0 : ℝ) < Real.exp (-(β * E (1 : Fin 2))) := Real.exp_pos _
  have hc : Real.exp (-logZ) ≠ 0 := Real.exp_ne_zero _
  have hsum : Real.exp (-(β * E (0 : Fin 2))) + Real.exp (-(β * E (1 : Fin 2))) ≠ 0 :=
    ne_of_gt (add_pos ha hb)
  rw [key, key, thermalSeparation, gibbsWeightsE_zero_logZ, gibbsWeightsE_zero_logZ]
  have e1 : Real.exp (-logZ) * Real.exp (-(β * E (0 : Fin 2)))
        - Real.exp (-logZ) * Real.exp (-(β * E (1 : Fin 2)))
      = Real.exp (-logZ)
        * (Real.exp (-(β * E (0 : Fin 2))) - Real.exp (-(β * E (1 : Fin 2)))) := by ring
  have e2 : Real.exp (-logZ) * Real.exp (-(β * E (0 : Fin 2)))
        + Real.exp (-logZ) * Real.exp (-(β * E (1 : Fin 2)))
      = Real.exp (-logZ)
        * (Real.exp (-(β * E (0 : Fin 2))) + Real.exp (-(β * E (1 : Fin 2)))) := by ring
  rw [e1, e2,
    show q * (Real.exp (-logZ)
        * (Real.exp (-(β * E (0 : Fin 2))) - Real.exp (-(β * E (1 : Fin 2)))))
      = Real.exp (-logZ)
        * (q * (Real.exp (-(β * E (0 : Fin 2))) - Real.exp (-(β * E (1 : Fin 2))))) from by ring]
  exact mul_div_mul_left _ _ hc

/-- **TARGET T1 — the exact formula** (Tier T1 — proved): the
partition normalization cancels, and the separation is a bare ratio
of exponentials in `β` and the two energies:

    `S(β) = q · (e^{−βE₀} − e^{−βE₁}) / (e^{−βE₀} + e^{−βE₁})`. -/
theorem thermalSeparation_eq_exp_formula (q : ℝ) (E : Fin 2 → ℝ) (β : ℝ) :
    thermalSeparation q E β
      = q * (Real.exp (-(β * E (0 : Fin 2))) - Real.exp (-(β * E (1 : Fin 2))))
          / (Real.exp (-(β * E (0 : Fin 2))) + Real.exp (-(β * E (1 : Fin 2)))) := by
  unfold thermalSeparation
  simp only [gibbsWeightsE_zero_logZ]

/-- **TARGET T1, tanh form** (Tier T1 — proved): the separation is
`−q · tanh(β · (E₀ − E₁) / 2)` — the two-sector Gibbs population
imbalance is a hyperbolic tangent of half the dimensionless gap. -/
theorem thermalSeparation_eq_neg_tanh (q : ℝ) (E : Fin 2 → ℝ) (β : ℝ) :
    thermalSeparation q E β
      = -q * Real.tanh (β * (E (0 : Fin 2) - E (1 : Fin 2)) / 2) := by
  have htanh : Real.tanh (β * (E (0 : Fin 2) - E (1 : Fin 2)) / 2)
      = (Real.exp (β * (E (0 : Fin 2) - E (1 : Fin 2)) / 2)
          - Real.exp (-(β * (E (0 : Fin 2) - E (1 : Fin 2)) / 2)))
        / (Real.exp (β * (E (0 : Fin 2) - E (1 : Fin 2)) / 2)
          + Real.exp (-(β * (E (0 : Fin 2) - E (1 : Fin 2)) / 2))) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    field_simp
  have ha : Real.exp (-(β * E (0 : Fin 2)))
      = Real.exp (-(β * (E (0 : Fin 2) + E (1 : Fin 2)) / 2))
        * Real.exp (-(β * (E (0 : Fin 2) - E (1 : Fin 2)) / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hb : Real.exp (-(β * E (1 : Fin 2)))
      = Real.exp (-(β * (E (0 : Fin 2) + E (1 : Fin 2)) / 2))
        * Real.exp (β * (E (0 : Fin 2) - E (1 : Fin 2)) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hc : (0 : ℝ) < Real.exp (-(β * (E (0 : Fin 2) + E (1 : Fin 2)) / 2)) :=
    Real.exp_pos _
  have hu : (0 : ℝ) < Real.exp (β * (E (0 : Fin 2) - E (1 : Fin 2)) / 2) :=
    Real.exp_pos _
  have hv : (0 : ℝ) < Real.exp (-(β * (E (0 : Fin 2) - E (1 : Fin 2)) / 2)) :=
    Real.exp_pos _
  rw [thermalSeparation_eq_exp_formula, htanh, ha, hb]
  field_simp
  ring

-- ============================================================================
-- §1. Vanishing: zero iff equal (Target T2)
-- ============================================================================

/-- **TARGET T2 — separation vanishes iff the energies agree**
(Tier T1 — proved): for `β > 0` and `q ≠ 0`,
`S(β) = 0 ⟺ E₀ = E₁`. A nonzero energy gap at positive inverse
temperature always separates; equal energies never do. -/
theorem thermalSeparation_eq_zero_iff (q : ℝ) (E : Fin 2 → ℝ) (β : ℝ)
    (hq : q ≠ 0) (hβ : 0 < β) :
    thermalSeparation q E β = 0 ↔ E (0 : Fin 2) = E (1 : Fin 2) := by
  have ha : (0 : ℝ) < Real.exp (-(β * E (0 : Fin 2))) := Real.exp_pos _
  have hb : (0 : ℝ) < Real.exp (-(β * E (1 : Fin 2))) := Real.exp_pos _
  rw [thermalSeparation_eq_exp_formula, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · rcases mul_eq_zero.mp h with hq0 | hab
      · exact absurd hq0 hq
      · have hab2 : Real.exp (-(β * E (0 : Fin 2)))
            = Real.exp (-(β * E (1 : Fin 2))) := sub_eq_zero.mp hab
        have harg : -(β * E (0 : Fin 2)) = -(β * E (1 : Fin 2)) :=
          Real.exp_strictMono.injective hab2
        have hmul : β * E (0 : Fin 2) = β * E (1 : Fin 2) := neg_inj.mp harg
        exact mul_left_cancel₀ (ne_of_gt hβ) hmul
    · exact absurd h (ne_of_gt (add_pos ha hb))
  · intro h
    left
    rw [h, sub_self, mul_zero]

/-- **Equal energies never separate** (Tier T1 — proved): if
`E₀ = E₁` the separation vanishes at every `β` and every `q` — the
one-sector collapse, companion of `flux_diagModularK_eq_zero_of_const`. -/
theorem thermalSeparation_eq_zero_of_energy_eq (q : ℝ) (E : Fin 2 → ℝ) (β : ℝ)
    (h : E (0 : Fin 2) = E (1 : Fin 2)) : thermalSeparation q E β = 0 := by
  rw [thermalSeparation_eq_exp_formula, h, sub_self, mul_zero, zero_div]

/-- **Infinite temperature never separates** (Tier T1 — proved): at
`β = 0` both Gibbs weights equal `1`, so the separation vanishes for
any energies and any `q`. -/
theorem thermalSeparation_zero_beta (q : ℝ) (E : Fin 2 → ℝ) :
    thermalSeparation q E 0 = 0 := by
  simp [thermalSeparation_eq_exp_formula]

-- ============================================================================
-- §2. The absolute separation and monotonicity (Target T3)
-- ============================================================================

/-- **The absolute-separation representation** (Tier T1 — proved):
for `β ≥ 0`,

    `|S(β)| = |q| · (1 − e^{−β·|E₀ − E₁|}) / (1 + e^{−β·|E₀ − E₁|})`.

Only the gap's absolute value enters: the two sectors enter
symmetrically, through `min/max` of the two Gibbs weights. -/
theorem abs_thermalSeparation_eq (q : ℝ) (E : Fin 2 → ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    |thermalSeparation q E β|
      = |q| * ((1 - Real.exp (-(β * |E (0 : Fin 2) - E (1 : Fin 2)|)))
          / (1 + Real.exp (-(β * |E (0 : Fin 2) - E (1 : Fin 2)|)))) := by
  have ha : (0 : ℝ) < Real.exp (-(β * E (0 : Fin 2))) := Real.exp_pos _
  have hb : (0 : ℝ) < Real.exp (-(β * E (1 : Fin 2))) := Real.exp_pos _
  have hsum : (0 : ℝ) < Real.exp (-(β * E (0 : Fin 2)))
      + Real.exp (-(β * E (1 : Fin 2))) := add_pos ha hb
  have hratio : |Real.exp (-(β * E (0 : Fin 2))) - Real.exp (-(β * E (1 : Fin 2)))|
        / (Real.exp (-(β * E (0 : Fin 2))) + Real.exp (-(β * E (1 : Fin 2))))
      = (1 - Real.exp (-(β * |E (0 : Fin 2) - E (1 : Fin 2)|)))
          / (1 + Real.exp (-(β * |E (0 : Fin 2) - E (1 : Fin 2)|))) := by
    rcases le_total (E (0 : Fin 2)) (E (1 : Fin 2)) with hle | hle
    · have hba : Real.exp (-(β * E (1 : Fin 2)))
          ≤ Real.exp (-(β * E (0 : Fin 2))) := by
        apply Real.exp_le_exp.mpr
        have hmul : β * E (0 : Fin 2) ≤ β * E (1 : Fin 2) :=
          mul_le_mul_of_nonneg_left hle hβ
        linarith
      have hr : Real.exp (-(β * E (1 : Fin 2))) / Real.exp (-(β * E (0 : Fin 2)))
          = Real.exp (-(β * |E (0 : Fin 2) - E (1 : Fin 2)|)) := by
        rw [← Real.exp_sub]
        congr 1
        rw [abs_of_nonpos (sub_nonpos.mpr hle)]
        ring
      have h1r : (1 : ℝ) + Real.exp (-(β * E (1 : Fin 2)))
          / Real.exp (-(β * E (0 : Fin 2))) ≠ 0 :=
        ne_of_gt (by have := div_pos hb ha; linarith)
      rw [abs_of_nonneg (sub_nonneg.mpr hba), ← hr, div_eq_div_iff (ne_of_gt hsum) h1r]
      field_simp
    · have hab : Real.exp (-(β * E (0 : Fin 2)))
          ≤ Real.exp (-(β * E (1 : Fin 2))) := by
        apply Real.exp_le_exp.mpr
        have hmul : β * E (1 : Fin 2) ≤ β * E (0 : Fin 2) :=
          mul_le_mul_of_nonneg_left hle hβ
        linarith
      have hr : Real.exp (-(β * E (0 : Fin 2))) / Real.exp (-(β * E (1 : Fin 2)))
          = Real.exp (-(β * |E (0 : Fin 2) - E (1 : Fin 2)|)) := by
        rw [← Real.exp_sub]
        congr 1
        rw [abs_of_nonneg (sub_nonneg.mpr hle)]
        ring
      have h1r : (1 : ℝ) + Real.exp (-(β * E (0 : Fin 2)))
          / Real.exp (-(β * E (1 : Fin 2))) ≠ 0 :=
        ne_of_gt (by have := div_pos ha hb; linarith)
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab), ← hr,
        div_eq_div_iff (ne_of_gt hsum) h1r]
      field_simp
      ring
  rw [thermalSeparation_eq_exp_formula, abs_div, abs_of_pos hsum, abs_mul,
    mul_div_assoc, hratio]

/-- **TARGET T3 — |separation| strictly increases in β** (Tier T1 —
proved): for a nonzero gap and `q ≠ 0`, `0 ≤ β₁ < β₂` gives
`|S(β₁)| < |S(β₂)|`. Cooling (raising `β`) strictly deepens the
separation; there is no plateau at finite `β`. -/
theorem abs_thermalSeparation_strictMono (q : ℝ) (E : Fin 2 → ℝ)
    (hE : E (0 : Fin 2) ≠ E (1 : Fin 2)) (hq : q ≠ 0)
    {β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ : β₁ < β₂) :
    |thermalSeparation q E β₁| < |thermalSeparation q E β₂| := by
  have hg : (0 : ℝ) < |E (0 : Fin 2) - E (1 : Fin 2)| :=
    abs_pos.mpr (sub_ne_zero.mpr hE)
  have ht : Real.exp (-(β₂ * |E (0 : Fin 2) - E (1 : Fin 2)|))
      < Real.exp (-(β₁ * |E (0 : Fin 2) - E (1 : Fin 2)|)) := by
    apply Real.exp_lt_exp.mpr
    have hmul : β₁ * |E (0 : Fin 2) - E (1 : Fin 2)|
        < β₂ * |E (0 : Fin 2) - E (1 : Fin 2)| := mul_lt_mul_of_pos_right hβ hg
    linarith
  have ht₁pos : (0 : ℝ) < Real.exp (-(β₁ * |E (0 : Fin 2) - E (1 : Fin 2)|)) :=
    Real.exp_pos _
  have ht₂pos : (0 : ℝ) < Real.exp (-(β₂ * |E (0 : Fin 2) - E (1 : Fin 2)|)) :=
    Real.exp_pos _
  have hψ : (1 - Real.exp (-(β₁ * |E (0 : Fin 2) - E (1 : Fin 2)|)))
        / (1 + Real.exp (-(β₁ * |E (0 : Fin 2) - E (1 : Fin 2)|)))
      < (1 - Real.exp (-(β₂ * |E (0 : Fin 2) - E (1 : Fin 2)|)))
        / (1 + Real.exp (-(β₂ * |E (0 : Fin 2) - E (1 : Fin 2)|))) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    have hexp : (1 - Real.exp (-(β₂ * |E (0 : Fin 2) - E (1 : Fin 2)|)))
          * (1 + Real.exp (-(β₁ * |E (0 : Fin 2) - E (1 : Fin 2)|)))
        - (1 - Real.exp (-(β₁ * |E (0 : Fin 2) - E (1 : Fin 2)|)))
          * (1 + Real.exp (-(β₂ * |E (0 : Fin 2) - E (1 : Fin 2)|)))
        = 2 * (Real.exp (-(β₁ * |E (0 : Fin 2) - E (1 : Fin 2)|))
            - Real.exp (-(β₂ * |E (0 : Fin 2) - E (1 : Fin 2)|))) := by ring
    linarith
  rw [abs_thermalSeparation_eq q E hβ₁,
    abs_thermalSeparation_eq q E (le_trans hβ₁ (le_of_lt hβ))]
  exact mul_lt_mul_of_pos_left hψ (abs_pos.mpr hq)

-- ============================================================================
-- §3. Bound and saturation (Target T4)
-- ============================================================================

/-- **TARGET T4, finite bound** (Tier T1 — proved): the separation
never reaches the full input charge at any finite `β`:
`|S(β)| < |q|` for `q ≠ 0`, at EVERY real `β`. Saturation is a limit
statement, never a finite attainment. -/
theorem abs_thermalSeparation_lt (q : ℝ) (E : Fin 2 → ℝ) (β : ℝ) (hq : q ≠ 0) :
    |thermalSeparation q E β| < |q| := by
  have ha : (0 : ℝ) < Real.exp (-(β * E (0 : Fin 2))) := Real.exp_pos _
  have hb : (0 : ℝ) < Real.exp (-(β * E (1 : Fin 2))) := Real.exp_pos _
  have hsum : (0 : ℝ) < Real.exp (-(β * E (0 : Fin 2)))
      + Real.exp (-(β * E (1 : Fin 2))) := add_pos ha hb
  have hlt : |Real.exp (-(β * E (0 : Fin 2))) - Real.exp (-(β * E (1 : Fin 2)))|
      < Real.exp (-(β * E (0 : Fin 2))) + Real.exp (-(β * E (1 : Fin 2))) := by
    rw [abs_lt]
    constructor <;> linarith
  rw [thermalSeparation_eq_exp_formula, abs_div, abs_of_pos hsum, abs_mul,
    div_lt_iff₀ hsum]
  exact mul_lt_mul_of_pos_left hlt (abs_pos.mpr hq)

/-- The ratio form of the separation (Tier T1 — proved): dividing
through by the sector-`0` weight,

    `S(β) = q · (1 − e^{−β(E₁ − E₀)}) / (1 + e^{−β(E₁ − E₀)})`,

the form in which the `β → ∞` limits are read off. -/
theorem thermalSeparation_eq_ratio (q : ℝ) (E : Fin 2 → ℝ) (β : ℝ) :
    thermalSeparation q E β
      = q * (1 - Real.exp (-(β * (E (1 : Fin 2) - E (0 : Fin 2)))))
          / (1 + Real.exp (-(β * (E (1 : Fin 2) - E (0 : Fin 2))))) := by
  have ha : (0 : ℝ) < Real.exp (-(β * E (0 : Fin 2))) := Real.exp_pos _
  have hb : (0 : ℝ) < Real.exp (-(β * E (1 : Fin 2))) := Real.exp_pos _
  have hsum : (0 : ℝ) < Real.exp (-(β * E (0 : Fin 2)))
      + Real.exp (-(β * E (1 : Fin 2))) := add_pos ha hb
  have hr : Real.exp (-(β * E (1 : Fin 2))) / Real.exp (-(β * E (0 : Fin 2)))
      = Real.exp (-(β * (E (1 : Fin 2) - E (0 : Fin 2)))) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have h1r : (1 : ℝ) + Real.exp (-(β * E (1 : Fin 2)))
      / Real.exp (-(β * E (0 : Fin 2))) ≠ 0 :=
    ne_of_gt (by have := div_pos hb ha; linarith)
  rw [thermalSeparation_eq_exp_formula, ← hr, div_eq_div_iff (ne_of_gt hsum) h1r]
  field_simp

/-- The flipped ratio form (Tier T1 — proved): dividing through by
the sector-`1` weight,

    `S(β) = −q · (1 − e^{−β(E₀ − E₁)}) / (1 + e^{−β(E₀ − E₁)})`. -/
theorem thermalSeparation_eq_neg_ratio (q : ℝ) (E : Fin 2 → ℝ) (β : ℝ) :
    thermalSeparation q E β
      = -q * (1 - Real.exp (-(β * (E (0 : Fin 2) - E (1 : Fin 2)))))
          / (1 + Real.exp (-(β * (E (0 : Fin 2) - E (1 : Fin 2))))) := by
  have ha : (0 : ℝ) < Real.exp (-(β * E (0 : Fin 2))) := Real.exp_pos _
  have hb : (0 : ℝ) < Real.exp (-(β * E (1 : Fin 2))) := Real.exp_pos _
  have hsum : (0 : ℝ) < Real.exp (-(β * E (0 : Fin 2)))
      + Real.exp (-(β * E (1 : Fin 2))) := add_pos ha hb
  have hr : Real.exp (-(β * E (0 : Fin 2))) / Real.exp (-(β * E (1 : Fin 2)))
      = Real.exp (-(β * (E (0 : Fin 2) - E (1 : Fin 2)))) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have h1r : (1 : ℝ) + Real.exp (-(β * E (0 : Fin 2)))
      / Real.exp (-(β * E (1 : Fin 2))) ≠ 0 :=
    ne_of_gt (by have := div_pos ha hb; linarith)
  have ha' : Real.exp (-(β * E (0 : Fin 2))) ≠ 0 := ne_of_gt ha
  have hb' : Real.exp (-(β * E (1 : Fin 2))) ≠ 0 := ne_of_gt hb
  have hsum' : Real.exp (-(β * E (0 : Fin 2))) + Real.exp (-(β * E (1 : Fin 2))) ≠ 0 :=
    ne_of_gt hsum
  rw [thermalSeparation_eq_exp_formula, ← hr]
  field_simp
  ring

/-- **TARGET T4, saturation** (Tier T1 — proved): for a nonzero gap,
`|S(β)| → |q|` as `β → ∞` — the bound of `abs_thermalSeparation_lt`
is sharp, attained only in the zero-temperature limit. -/
theorem tendsto_abs_thermalSeparation_atTop (q : ℝ) (E : Fin 2 → ℝ)
    (hE : E (0 : Fin 2) ≠ E (1 : Fin 2)) :
    Tendsto (fun β => |thermalSeparation q E β|) atTop (𝓝 |q|) := by
  have hg : (0 : ℝ) < |E (0 : Fin 2) - E (1 : Fin 2)| :=
    abs_pos.mpr (sub_ne_zero.mpr hE)
  have ht : Tendsto (fun β : ℝ => Real.exp (-(β * |E (0 : Fin 2) - E (1 : Fin 2)|)))
      atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_id).atTop_mul_const hg)
  have hψ : Tendsto (fun β : ℝ => (1 - Real.exp (-(β * |E (0 : Fin 2) - E (1 : Fin 2)|)))
        / (1 + Real.exp (-(β * |E (0 : Fin 2) - E (1 : Fin 2)|)))) atTop (𝓝 1) := by
    have hnum : Tendsto (fun β : ℝ => (1 : ℝ)
        - Real.exp (-(β * |E (0 : Fin 2) - E (1 : Fin 2)|))) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub ht
    have hden : Tendsto (fun β : ℝ => (1 : ℝ)
        + Real.exp (-(β * |E (0 : Fin 2) - E (1 : Fin 2)|))) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add ht
    have h := hnum.div hden (by norm_num)
    have h' : Tendsto (fun β : ℝ => (1 - Real.exp (-(β * |E (0 : Fin 2) - E (1 : Fin 2)|)))
        / (1 + Real.exp (-(β * |E (0 : Fin 2) - E (1 : Fin 2)|)))) atTop
        (𝓝 ((1 - 0) / (1 + 0))) := h
    simpa using h'
  have heq : (fun β => |thermalSeparation q E β|) =ᶠ[atTop]
      (fun β => |q| * ((1 - Real.exp (-(β * |E (0 : Fin 2) - E (1 : Fin 2)|)))
        / (1 + Real.exp (-(β * |E (0 : Fin 2) - E (1 : Fin 2)|))))) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with β hβ
    exact abs_thermalSeparation_eq q E hβ
  have hmul := hψ.const_mul |q|
  rw [mul_one] at hmul
  exact hmul.congr' heq.symm

/-- **TARGET T4, signed saturation, sector 1 heavier** (Tier T1 —
proved): if `E₀ < E₁`, the light sector `0` wins at low temperature
and `S(β) → q` as `β → ∞`. -/
theorem tendsto_thermalSeparation_atTop_of_energy_lt (q : ℝ) (E : Fin 2 → ℝ)
    (hE : E (0 : Fin 2) < E (1 : Fin 2)) :
    Tendsto (thermalSeparation q E) atTop (𝓝 q) := by
  have hc : (0 : ℝ) < E (1 : Fin 2) - E (0 : Fin 2) := sub_pos.mpr hE
  have hr : Tendsto (fun β : ℝ => Real.exp (-(β * (E (1 : Fin 2) - E (0 : Fin 2)))))
      atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp ((tendsto_id).atTop_mul_const hc)
  have hψ : Tendsto (fun β : ℝ => (1 - Real.exp (-(β * (E (1 : Fin 2) - E (0 : Fin 2)))))
        / (1 + Real.exp (-(β * (E (1 : Fin 2) - E (0 : Fin 2)))))) atTop (𝓝 1) := by
    have hnum : Tendsto (fun β : ℝ => (1 : ℝ)
        - Real.exp (-(β * (E (1 : Fin 2) - E (0 : Fin 2))))) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hr
    have hden : Tendsto (fun β : ℝ => (1 : ℝ)
        + Real.exp (-(β * (E (1 : Fin 2) - E (0 : Fin 2))))) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hr
    have h := hnum.div hden (by norm_num)
    have h' : Tendsto (fun β : ℝ => (1 - Real.exp (-(β * (E (1 : Fin 2) - E (0 : Fin 2)))))
        / (1 + Real.exp (-(β * (E (1 : Fin 2) - E (0 : Fin 2)))))) atTop
        (𝓝 ((1 - 0) / (1 + 0))) := h
    simpa using h'
  have hfun : thermalSeparation q E
      = fun β => q * ((1 - Real.exp (-(β * (E (1 : Fin 2) - E (0 : Fin 2)))))
          / (1 + Real.exp (-(β * (E (1 : Fin 2) - E (0 : Fin 2)))))) := by
    funext β
    rw [thermalSeparation_eq_ratio, mul_div_assoc]
  rw [hfun]
  have hmul := hψ.const_mul q
  rwa [mul_one] at hmul

/-- **TARGET T4, signed saturation, sector 0 heavier** (Tier T1 —
proved): if `E₁ < E₀`, sector `1` wins at low temperature and
`S(β) → −q` as `β → ∞`. Together with the previous theorem, the
zero-temperature limit is the sign-determined `∓q` of the charter. -/
theorem tendsto_thermalSeparation_atTop_of_energy_gt (q : ℝ) (E : Fin 2 → ℝ)
    (hE : E (1 : Fin 2) < E (0 : Fin 2)) :
    Tendsto (thermalSeparation q E) atTop (𝓝 (-q)) := by
  have hc : (0 : ℝ) < E (0 : Fin 2) - E (1 : Fin 2) := sub_pos.mpr hE
  have hr : Tendsto (fun β : ℝ => Real.exp (-(β * (E (0 : Fin 2) - E (1 : Fin 2)))))
      atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp ((tendsto_id).atTop_mul_const hc)
  have hψ : Tendsto (fun β : ℝ => (1 - Real.exp (-(β * (E (0 : Fin 2) - E (1 : Fin 2)))))
        / (1 + Real.exp (-(β * (E (0 : Fin 2) - E (1 : Fin 2)))))) atTop (𝓝 1) := by
    have hnum : Tendsto (fun β : ℝ => (1 : ℝ)
        - Real.exp (-(β * (E (0 : Fin 2) - E (1 : Fin 2))))) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hr
    have hden : Tendsto (fun β : ℝ => (1 : ℝ)
        + Real.exp (-(β * (E (0 : Fin 2) - E (1 : Fin 2))))) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hr
    have h := hnum.div hden (by norm_num)
    have h' : Tendsto (fun β : ℝ => (1 - Real.exp (-(β * (E (0 : Fin 2) - E (1 : Fin 2)))))
        / (1 + Real.exp (-(β * (E (0 : Fin 2) - E (1 : Fin 2)))))) atTop
        (𝓝 ((1 - 0) / (1 + 0))) := h
    simpa using h'
  have hfun : thermalSeparation q E
      = fun β => -q * ((1 - Real.exp (-(β * (E (0 : Fin 2) - E (1 : Fin 2)))))
          / (1 + Real.exp (-(β * (E (0 : Fin 2) - E (1 : Fin 2)))))) := by
    funext β
    rw [thermalSeparation_eq_neg_ratio, mul_div_assoc]
  rw [hfun]
  have hmul := hψ.const_mul (-q)
  rwa [mul_one] at hmul

-- ============================================================================
-- §4. The flux hook (Target T5)
-- ============================================================================

/-- **TARGET T5 — cross-sector entry forces flux at the Gibbs K**
(Tier T1 — proved, via FluxClassification): let `ρ` be the two-sector
Gibbs state with weights `w = gibbsWeightsE β E logZ` and
`K = diagModularK w` its modular Hamiltonian. At `β > 0` with a
nonzero energy gap, any Dirac operator `D` with a nonzero
cross-sector entry `D 0 1 ≠ 0` has nonzero modular flux
`φ = i[K, D] ≠ 0`: coupling the thermally separated sectors switches
the flux on. This is the vortex's anchor, `φ = i[K, D]`. -/
theorem gibbs_flux_ne_zero_of_cross_entry (E : Fin 2 → ℝ) (β logZ : ℝ)
    (hβ : 0 < β) (hE : E (0 : Fin 2) ≠ E (1 : Fin 2))
    (D : Matrix (Fin 2) (Fin 2) ℂ) (hD : D 0 1 ≠ 0) :
    modularFlux (diagModularK (gibbsWeightsE β E logZ)) D ≠ 0 := by
  apply flux_diagModularK_ne_zero_of_entry _ _ _ hD
  rw [gibbsWeightsE_log, gibbsWeightsE_log]
  intro hcon
  apply hE
  have h1 : β * E (0 : Fin 2) + logZ = β * E (1 : Fin 2) + logZ := neg_inj.mp hcon
  have h2 : β * E (0 : Fin 2) = β * E (1 : Fin 2) := by linarith
  exact mul_left_cancel₀ (ne_of_gt hβ) h2

/-- **TARGET T5, classification form** (Tier T1 — proved, via
FluxClassification): at `β > 0`, the modular flux at the Gibbs state's
`K` vanishes iff `D` has no entries across distinct energy sectors:

    `φ = i[K, D] = 0 ⟺ ∀ i j, E i ≠ E j → D i j = 0`.

At positive `β` the Gibbs weights separate the sectors exactly when
the energies do (`gibbsWeightsE` is injective on sectors), so the
weight-level sectors of `classification_diagModularK_of_pos` are the
energy level sets. Fence K-TV1 stands: the sectors are the INPUT
energies' level sets; no charge is derived. -/
theorem gibbs_flux_eq_zero_iff (E : Fin 2 → ℝ) (β logZ : ℝ) (hβ : 0 < β)
    (D : Matrix (Fin 2) (Fin 2) ℂ) :
    modularFlux (diagModularK (gibbsWeightsE β E logZ)) D = 0
      ↔ ∀ i j, E i ≠ E j → D i j = 0 := by
  have e : ∀ k : Fin 2, gibbsWeightsE β E logZ k
      = Real.exp (-(β * E k + logZ)) := fun k => rfl
  have hw : ∀ i j : Fin 2, gibbsWeightsE β E logZ i = gibbsWeightsE β E logZ j
      ↔ E i = E j := by
    intro i j
    rw [e i, e j]
    constructor
    · intro h
      have harg : -(β * E i + logZ) = -(β * E j + logZ) := Real.exp_strictMono.injective h
      have h1 : β * E i + logZ = β * E j + logZ := neg_inj.mp harg
      have h2 : β * E i = β * E j := by linarith
      exact mul_left_cancel₀ (ne_of_gt hβ) h2
    · intro h
      rw [h]
  rw [classification_diagModularK_of_pos _ (fun j => gibbsWeightsE_pos β E logZ j) D]
  constructor
  · intro h i j hij
    exact h i j (fun hw_eq => hij ((hw i j).mp hw_eq))
  · intro h i j hij
    exact h i j (fun hE_eq => hij ((hw i j).mpr hE_eq))

/-- **One-sector collapse at the Gibbs K** (Tier T1 — proved): if the
two energies agree, there is a single sector and the flux at the
Gibbs state's `K` vanishes for every `D` — the flux-side companion
of `thermalSeparation_eq_zero_of_energy_eq`. -/
theorem gibbs_flux_eq_zero_of_energy_eq (E : Fin 2 → ℝ) (β logZ : ℝ) (hβ : 0 < β)
    (h : E (0 : Fin 2) = E (1 : Fin 2)) (D : Matrix (Fin 2) (Fin 2) ℂ) :
    modularFlux (diagModularK (gibbsWeightsE β E logZ)) D = 0 := by
  rw [gibbs_flux_eq_zero_iff E β logZ hβ D]
  intro i j hij
  exact absurd (show E i = E j by fin_cases i <;> fin_cases j <;> simp_all) hij

end ThetLogos.TeslaVortexSeparation
