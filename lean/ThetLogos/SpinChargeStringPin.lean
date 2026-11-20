/-
# SpinChargeStringPin — the spin-charge seat: winding, endpoint charges, and a centrifugal term on the thermal string

**Scope: ~/workspace/your_files/spin-charge-string-pin-scope-2026-11-16.md
(Zero's seeing of 2026-11-16 23:18 EST, filed verbatim in the day
log; the finite flag fired by his word "load up the bench",
2026-11-16 23:19 EST).
NO CLAIM. Dial-ineligible.**

WORKING LABEL: the module name `SpinChargeStringPin` is a
working label only — final naming is Zero's.

THE SEAT: the landed winding seat (`StringWindingPin`: a chain
of `n` links, each link a step state from `Fin 3` — down, flat,
up; a CONFIGURATION is the tuple of link states), with the two
ingredients tonight named, added on the corpus's own
finite-Gibbs machinery (`ModularVariance.gibbsProb` / `partSum`
at the effective energy). No parallel apparatus.

- SPIN SEAT: a configuration's ROTATION NUMBER is its winding
  (`StringWindingPin.winding`, the total displacement
  `∑ i, stepValue (c i)` in `ℤ`) — a classical integer, the
  finite shadow of a string's spin.
- CHARGE SEAT: endpoint charges `q₋, q₊`, each in
  `{−1, 0, +1}` (ternary, the program's grain), seated at the
  string's two ends as PARAMETERS of the seat — the
  flux-tube arrangement (charges at the ends, string
  between). Only their bookkeeping is pinned here
  (`totalEndpointCharge` and its ternary bound).
- CENTRIFUGAL TERM: each configuration has a MOMENT OF
  INERTIA `I(c) = ∑ i, (position of link i)²`, where a link's
  position is the height of the finite path after that link.
  The EFFECTIVE ENERGY is
  `E_κ(c) = stepEnergyR(c) − κ · I(c)`, with `κ ≥ 0` the
  centrifugal coefficient (κ plays the role of ω²/2). The
  sign is the physics: in the rotating frame the centrifugal
  potential REWARDS extension — rotation tips the Gibbs
  balance toward spread configurations, against the bend
  (variation) cost that tips it straight.

THE MENU (the scope's): S-2 reduction (at `κ = 0` the
effective energy is the seat's bend energy and the Gibbs
weights are exactly the landed winding seat's — the new seat
is a one-parameter extension, not a new ensemble); S-3 weight
ratio (the Gibbs weight ratio of two configurations is
`exp(−β·(E_κ(c₁) − E_κ(c₂)))` in closed form — the partition
sum cancels); S-4 the flip (for the straight configuration
against a fixed extended configuration `c*` with bend gap
`Δbend > 0` and inertia gap `ΔI > 0`, both stated as
hypotheses: at every slope `β > 0` the relative Gibbs weight
of `c*` is `< 1` when `κ < Δbend/ΔI`, `= 1` at
`κ = Δbend/ΔI`, and `> 1` when `κ > Δbend/ΔI` — rotation past
a computable threshold makes the spread configuration the
favourite).

FIDELITY FENCES (the scope's, in plain words):
- "Spin" here is a CLASSICAL winding/rotation number of a
  finite configuration — NOT quantum spin, NOT a Regge
  trajectory. The Regge relation `J = α′M²`, the QCD flux
  tube, the Hagedorn temperature and deconfinement are
  Register-2 rhymes, cited as rhyme only, never as theorems
  of this seat.
- Endpoint charges are seat parameters: there is no charge
  dynamics, no field, no quantization, no continuum string.
- The flip is a TWO-CONFIGURATION Gibbs comparison — not a
  phase transition, not deconfinement, not Hagedorn.
- This pin derives NO Standard Model output; no measured
  number enters or leaves. M-U2 untouched; the word
  "solves" is not used. NO CLAIM; dials 0/4.
  K-STRING-PHYS armed; K-PLANCK-SEAT respected (no Planck
  scale, no physical units anywhere in the module).

STATUS: STATUS-SPINCHARGE.md.
-/

import Mathlib.Tactic
import ThetLogos.ModularVariance
import ThetLogos.StringWindingPin

namespace ThetLogos.SpinChargeStringPin

variable {n : ℕ}

/-! ## §1 — Brick 1: the seat (S-0) and the κ = 0 reduction (S-2) -/

/-- **Rotation number of a configuration**: its winding in
`StringWindingPin`'s form — the total displacement
`∑ i, stepValue (c i)` in `ℤ`. A classical integer: the
finite shadow of the string's spin. -/
def rotNum (c : Fin n → Fin 3) : ℤ :=
  StringWindingPin.winding c

/-- **Position of link `i`**: the height of the finite path
after link `i` — the prefix sum of the step values through
`i`, in `ℤ`. The straight (flat) configuration sits at
position `0` at every link. -/
def linkPos (c : Fin n → Fin 3) (i : Fin n) : ℤ :=
  ∑ j ∈ Finset.Iic i, StringWindingPin.stepValue (c j)

/-- **Moment of inertia of a configuration**:
`I(c) = ∑ i, (position of link i)²`, as a real number —
how extended the path is, weighted by where its links
sit. -/
noncomputable def inertia (c : Fin n → Fin 3) : ℝ :=
  ∑ i, (linkPos c i : ℝ) ^ 2

/-- **Effective energy at centrifugal coefficient `κ`**:
the seat's variation (bend) energy minus `κ` times the
moment of inertia, `E_κ(c) = stepEnergyR(c) − κ · I(c)`.
The sign is the physics: the centrifugal term REWARDS
extension — in the rotating frame, spread configurations
pay less. -/
noncomputable def effEnergy (κ : ℝ) (c : Fin n → Fin 3) : ℝ :=
  StringWindingPin.stepEnergyR c - κ * inertia c

/-- **Total endpoint charge**: the sum of the charges
seated at the string's two ends, `q₋ + q₊`. The charges
are parameters of the seat (each in `{−1, 0, +1}`, carried
as the hypothesis `|q| ≤ 1` where used); there is no
charge dynamics. -/
def totalEndpointCharge (qMinus qPlus : ℤ) : ℤ :=
  qMinus + qPlus

/-- The total endpoint charge of two ternary charges is
at most `2` in absolute value — the seat's charge
bookkeeping bound. -/
theorem totalEndpointCharge_abs_le {qMinus qPlus : ℤ}
    (hMinus : |qMinus| ≤ 1) (hPlus : |qPlus| ≤ 1) :
    |totalEndpointCharge qMinus qPlus| ≤ 2 := by
  unfold totalEndpointCharge
  calc |qMinus + qPlus| ≤ |qMinus| + |qPlus| := abs_add_le _ _
    _ ≤ 1 + 1 := add_le_add hMinus hPlus
    _ = 2 := by norm_num

/-- The moment of inertia is non-negative — a sum of
squares. -/
theorem inertia_nonneg (c : Fin n → Fin 3) : 0 ≤ inertia c :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (linkPos c i : ℝ))

/-- **S-2, energy form (reduction)**: at `κ = 0` the
effective energy is the seat's bend (variation) energy —
the centrifugal term switches off and the seat is the
landed winding seat. -/
theorem effEnergy_zero (c : Fin n → Fin 3) :
    effEnergy 0 c = StringWindingPin.stepEnergyR c := by
  simp [effEnergy]

/-- **S-2, weight form (reduction)**: at `κ = 0` the Gibbs
weights of the effective energy are the landed winding
seat's Gibbs weights, at every slope `β` and every
configuration — the extension is invisible at `κ = 0`. -/
theorem gibbsProb_effEnergy_zero (β : ℝ) (c : Fin n → Fin 3) :
    ModularVariance.gibbsProb (effEnergy 0) β c
      = ModularVariance.gibbsProb StringWindingPin.stepEnergyR β c := by
  have hfun : effEnergy (n := n) 0
      = StringWindingPin.stepEnergyR := by
    funext c
    exact effEnergy_zero c
  rw [hfun]

/-! ## §2 — Brick 2: the weight ratio (S-3) and the flip (S-4) -/

/-- **The straight configuration**: every link flat — the
winding seat's ground configuration (step energy `0`,
every link at position `0`, inertia `0`). -/
def straightConfig : Fin n → Fin 3 :=
  fun _ => 1

/-- The straight configuration's effective energy is `0`
at every centrifugal coefficient `κ` — rotation cannot
reward a configuration with no extension: its step energy
and its inertia both vanish. -/
theorem effEnergy_straightConfig (κ : ℝ) :
    effEnergy κ (straightConfig : Fin n → Fin 3) = 0 := by
  have hv1 : StringWindingPin.stepValue (1 : Fin 3) = 0 := rfl
  have hE : StringWindingPin.stepEnergy
      (straightConfig : Fin n → Fin 3) = 0 := by
    show (∑ i, |StringWindingPin.stepValue
      ((fun _ : Fin n => (1 : Fin 3)) i)|) = 0
    simp [hv1]
  have hI : inertia (straightConfig : Fin n → Fin 3) = 0 := by
    show (∑ i, (linkPos (fun _ : Fin n => (1 : Fin 3)) i : ℝ) ^ 2) = 0
    apply Finset.sum_eq_zero
    intro i _
    have hpos : linkPos (fun _ : Fin n => (1 : Fin 3)) i = 0 := by
      show (∑ j ∈ Finset.Iic i, StringWindingPin.stepValue
        ((fun _ : Fin n => (1 : Fin 3)) j)) = 0
      simp [hv1]
    rw [hpos]
    simp
  show StringWindingPin.stepEnergyR (straightConfig : Fin n → Fin 3)
      - κ * inertia (straightConfig : Fin n → Fin 3) = 0
  rw [hI, mul_zero, sub_zero]
  show ((StringWindingPin.stepEnergy
    (straightConfig : Fin n → Fin 3) : ℤ) : ℝ) = 0
  rw [hE]
  exact Int.cast_zero

/-- The effective-energy difference against the straight
configuration, in gap form: bend gap minus `κ` times the
inertia gap. This is the algebra the flip reads. -/
theorem effEnergy_sub_straightConfig (κ : ℝ) (cstar : Fin n → Fin 3) :
    effEnergy κ cstar - effEnergy κ (straightConfig : Fin n → Fin 3)
      = (StringWindingPin.stepEnergyR cstar
          - StringWindingPin.stepEnergyR (straightConfig : Fin n → Fin 3))
        - κ * (inertia cstar
          - inertia (straightConfig : Fin n → Fin 3)) := by
  unfold effEnergy
  ring

/-- **S-3 (weight ratio)**: for any two configurations,
the Gibbs weight ratio at the effective energy is the
exponential of the energy difference, in closed form —
the partition sum cancels between numerator and
denominator. -/
theorem gibbsProb_ratio (κ β : ℝ) (c₁ c₂ : Fin n → Fin 3) :
    ModularVariance.gibbsProb (effEnergy κ) β c₁
        / ModularVariance.gibbsProb (effEnergy κ) β c₂
      = Real.exp (-(β * (effEnergy κ c₁ - effEnergy κ c₂))) := by
  have hZ : ModularVariance.partSum (effEnergy κ) β ≠ 0 :=
    ModularVariance.partSum_ne_zero (effEnergy (n := n) κ) β
  have hnum : Real.exp (-(β * effEnergy κ c₁))
      = Real.exp (-(β * (effEnergy κ c₁ - effEnergy κ c₂)))
        * Real.exp (-(β * effEnergy κ c₂)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold ModularVariance.gibbsProb
  rw [hnum]
  field_simp [hZ, (Real.exp_pos (-(β * effEnergy κ c₂))).ne']

/-- **S-4, below threshold (the flip, cold side of
rotation)**: for `β > 0`, `κ ≥ 0`, and an extended
configuration `cstar` whose bend gap and inertia gap over
the straight configuration are both positive, if
`κ < Δbend/ΔI` then the relative Gibbs weight of `cstar`
against the straight configuration is `< 1` — the bend
cost still wins; the straight configuration is the
favourite. -/
theorem flip_lt {κ β : ℝ} (hβ : 0 < β) (hκ : 0 ≤ κ)
    (cstar : Fin n → Fin 3)
    (hΔbend : 0 < StringWindingPin.stepEnergyR cstar
      - StringWindingPin.stepEnergyR (straightConfig : Fin n → Fin 3))
    (hΔI : 0 < inertia cstar
      - inertia (straightConfig : Fin n → Fin 3))
    (hκt : κ < (StringWindingPin.stepEnergyR cstar
        - StringWindingPin.stepEnergyR (straightConfig : Fin n → Fin 3))
      / (inertia cstar
        - inertia (straightConfig : Fin n → Fin 3))) :
    ModularVariance.gibbsProb (effEnergy κ) β cstar
        / ModularVariance.gibbsProb (effEnergy κ) β
          (straightConfig : Fin n → Fin 3)
      < 1 := by
  have hκΔ : κ * (inertia cstar
        - inertia (straightConfig : Fin n → Fin 3))
      < StringWindingPin.stepEnergyR cstar
        - StringWindingPin.stepEnergyR (straightConfig : Fin n → Fin 3) :=
    (lt_div_iff₀ hΔI).mp hκt
  have hpos : 0 < (StringWindingPin.stepEnergyR cstar
        - StringWindingPin.stepEnergyR (straightConfig : Fin n → Fin 3))
      - κ * (inertia cstar
        - inertia (straightConfig : Fin n → Fin 3)) := by
    linarith
  rw [gibbsProb_ratio, effEnergy_sub_straightConfig]
  have hexp : Real.exp (-(β * ((StringWindingPin.stepEnergyR cstar
        - StringWindingPin.stepEnergyR (straightConfig : Fin n → Fin 3))
      - κ * (inertia cstar
        - inertia (straightConfig : Fin n → Fin 3)))))
      < Real.exp 0 :=
    Real.exp_lt_exp.mpr (neg_lt_zero.mpr (mul_pos hβ hpos))
  rwa [Real.exp_zero] at hexp

/-- **S-4, at threshold (the flip, the balance point)**:
under the same hypotheses, if `κ = Δbend/ΔI` then the
relative Gibbs weight of `cstar` against the straight
configuration is exactly `1` — the bend cost and the
centrifugal reward cancel; the two configurations carry
equal weight. -/
theorem flip_eq {κ β : ℝ} (hβ : 0 < β) (hκ : 0 ≤ κ)
    (cstar : Fin n → Fin 3)
    (hΔbend : 0 < StringWindingPin.stepEnergyR cstar
      - StringWindingPin.stepEnergyR (straightConfig : Fin n → Fin 3))
    (hΔI : 0 < inertia cstar
      - inertia (straightConfig : Fin n → Fin 3))
    (hκt : κ = (StringWindingPin.stepEnergyR cstar
        - StringWindingPin.stepEnergyR (straightConfig : Fin n → Fin 3))
      / (inertia cstar
        - inertia (straightConfig : Fin n → Fin 3))) :
    ModularVariance.gibbsProb (effEnergy κ) β cstar
        / ModularVariance.gibbsProb (effEnergy κ) β
          (straightConfig : Fin n → Fin 3)
      = 1 := by
  have hκΔ : κ * (inertia cstar
        - inertia (straightConfig : Fin n → Fin 3))
      = StringWindingPin.stepEnergyR cstar
        - StringWindingPin.stepEnergyR (straightConfig : Fin n → Fin 3) := by
    rw [hκt]
    exact div_mul_cancel₀ _ (ne_of_gt hΔI)
  rw [gibbsProb_ratio, effEnergy_sub_straightConfig]
  have hzero : (StringWindingPin.stepEnergyR cstar
        - StringWindingPin.stepEnergyR (straightConfig : Fin n → Fin 3))
      - κ * (inertia cstar
        - inertia (straightConfig : Fin n → Fin 3)) = 0 :=
    sub_eq_zero.mpr hκΔ.symm
  rw [hzero]
  simp

/-- **S-4, above threshold (the flip, the rotating side)**:
under the same hypotheses, if `κ > Δbend/ΔI` then the
relative Gibbs weight of `cstar` against the straight
configuration is `> 1` — rotation has tipped the balance;
the spread configuration is the favourite. A
two-configuration comparison, stated as exactly that. -/
theorem flip_gt {κ β : ℝ} (hβ : 0 < β) (hκ : 0 ≤ κ)
    (cstar : Fin n → Fin 3)
    (hΔbend : 0 < StringWindingPin.stepEnergyR cstar
      - StringWindingPin.stepEnergyR (straightConfig : Fin n → Fin 3))
    (hΔI : 0 < inertia cstar
      - inertia (straightConfig : Fin n → Fin 3))
    (hκt : (StringWindingPin.stepEnergyR cstar
        - StringWindingPin.stepEnergyR (straightConfig : Fin n → Fin 3))
      / (inertia cstar
        - inertia (straightConfig : Fin n → Fin 3)) < κ) :
    1 < ModularVariance.gibbsProb (effEnergy κ) β cstar
        / ModularVariance.gibbsProb (effEnergy κ) β
          (straightConfig : Fin n → Fin 3) := by
  have hκΔ : StringWindingPin.stepEnergyR cstar
        - StringWindingPin.stepEnergyR (straightConfig : Fin n → Fin 3)
      < κ * (inertia cstar
        - inertia (straightConfig : Fin n → Fin 3)) :=
    (div_lt_iff₀ hΔI).mp hκt
  have hneg : (StringWindingPin.stepEnergyR cstar
        - StringWindingPin.stepEnergyR (straightConfig : Fin n → Fin 3))
      - κ * (inertia cstar
        - inertia (straightConfig : Fin n → Fin 3)) < 0 := by
    linarith
  rw [gibbsProb_ratio, effEnergy_sub_straightConfig]
  have hexp : Real.exp 0 < Real.exp (-(β * ((StringWindingPin.stepEnergyR cstar
        - StringWindingPin.stepEnergyR (straightConfig : Fin n → Fin 3))
      - κ * (inertia cstar
        - inertia (straightConfig : Fin n → Fin 3))))) :=
    Real.exp_lt_exp.mpr (neg_pos.mpr (mul_neg_of_pos_of_neg hβ hneg))
  rwa [Real.exp_zero] at hexp

end ThetLogos.SpinChargeStringPin
