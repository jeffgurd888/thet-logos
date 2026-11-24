/-
# EinsteinPlanckGibbsWeldPin — Zero's chain, welded at its two real joints (working label)

**Commissioned by Zero, 2026-11-21 01:21 EST ("Scope the
Einstein–Planck–Gibbs weld pin"), fired 2026-11-21 01:27 EST,
on his question of 01:18 EST: "can we build the planck hf
Einstein -Gibbs bridge". Scope of record:
~/workspace/your_files/einstein-planck-gibbs-weld-scope-2026-11-21.md.
Lane-grade pin. NO CLAIM. T5; pre-registered DIAL-INELIGIBLE;
Dial 2 stays 0 under every outcome, including a clean landing of
every brick.**

Working label only — "Einstein–Planck–Gibbs weld" is Zero's name
for the bridge; module naming beyond the working label is his hand.

Zero's chain, verbatim (2026-11-18): "Einstein and planck both set
E=mass •c²=hf therefore mass = Gibbs". The chain runs one energy
through three costumes. Most of it already stands in the corpus
under other names (the receipts are in the scope, §§1–4): KHP owns
the Planck factor and its mean-energy sum (KHP-2/KHP-4);
MassGibbs owns the mass costume — the state sees exactly the
product β·m (MG-1/MG-3/MG-5); Cymatics owns the hf costume —
`modeEnergy h λ = h·√λ`, h a bare parameter, never valued. This
pin is the WELD: it chains the standing pieces at the two points
where they genuinely compose (Brick 1: the shell's thermal mean
energy in closed form; Brick 2: the exact fork between the
corpus's two Gibbs readings), and cards the one pier that does
not exist (the Einstein equations, below).

## Brick 0 — the chain card (0 strict by design)

The two Gibbs readings, named and frozen so Bricks 1–2 state
against fixed names:
- `planckMeanEnergy β E = E · planckFactor β E` — the Planck
  (bosonic ladder) reading: a mode of energy E has mean energy
  E/(e^{βE} − 1) (KHP-2's factor times the energy; the singleton
  of KHP-4's sum). A definition citing KHP's ownership — not a
  re-proof (K-EPG-DUP).
- `siteMeanEnergy β E` — the finite-site (classical) reading:
  `ModularVariance.meanEnergy` at the two-site profile (0, E) —
  which is `massEnergy ![0,1] E`'s profile, MassGibbs' home seat.

THE c VERDICT (scope, "The c question"): the chain is stated
WITHOUT c. No c object exists in-tree (strike-checked: no
definition, parameter, or valued constant; the only `c²` strings
are in MassGibbsPin's own header, excluding c). A valued c is
refused (a measured number inside theorem statements); a bare c
would ride through every weld equality as a passenger factor and
cancel (each is a reading of the single product β·(energy
scale), and MG-1 already seats the mass as one scalar carrying an
energy profile). E = mc² is named here as the seeing's motivation
for that seating, in MassGibbsPin's own words — as Register data,
never a theorem.

THE EINSTEIN CARD (the far pier, stated exactly; the
registrations are CITED in prose, never re-registered —
K-EPG-DUP): the spectral action's a₂ Einstein–Hilbert slot —
`a2GravCoeff` of `SpectralActionA2`, registered in
`CpecBridgePost` as `cpecEinsteinSlotCoeff` / `CpecEinsteinSlot`
— is occupied, separated, proved nonzero
(`a2_grav_coeff_ne_zero`), and proved IMPORTED, not derived
(GR-POSE-1 / `poseKill_decision`; W2 decided negative,
`CpecW2ConnesEinsteinDecided`). It multiplies an abstract
curvature slot (`scalarR`) that nothing in the corpus computes.
**What this weld delivers to it: nothing.** No brick of this pin
states, feeds, bounds, or touches the slot. What is absent (the
W4 price, named): (i) a manifold factor with a Lorentzian
metric; (ii) a stress-energy operator built from the triple's
fields; (iii) the Einstein equations as a machine-checked
relation — per `UltimateReduction`'s Claim-5 fence, nothing of
the form G_μν = 8πT_μν can be stated in the corpus today (W4
registered UNSTATABLE, `CpecW4PlanckEinsteinAbsent`).

THE COMPTON FENCE: no frequency is assigned to a mass anywhere in
this pin; f = mc²/h stays a seeing (MassGibbs' MG-6 discipline,
inherited).

KILLS PRE-REGISTERED: K-EPG-RENAME (armed at drafting — if either
Joint equality is found already owned, the affected brick dies
and the pin ships as Brick 0 alone, a registration card;
scoping verdict: does NOT fire, strike-checked) · K-EPG-EINSTEIN
(any field-equation-shaped statement, or any statement feeding
the a₂ slot as if the weld reached it, is void on sight) ·
K-EPG-DERIVE (c, h, G, ℏ, k_B never derived; h stays Cymatics'
bare parameter; no c at all) · K-EPG-DUP (KHP-2/4, Cymatics'
ladder, MG-1/3/5, the CPEC registrations — cited, never
re-proved) · K-EPG-STATISTICS (the weld's own fence: the two
Gibbs readings are NEVER identified — Brick 2 proves their
difference is 2·U_P(2β) > 0). Inherited, standing: K-KHP-UNIT /
K-KHP-TIME / K-KHP-SEAT · K-CPEC-PLANCK-RENAME ·
K-CPEC-EINSTEIN-RESTATE · K-CPEC-TORSION-IMPORT · K-PLANCK-SEAT
· K-MASSGIBBS-SPLIT / K-MASSGIBBS-COSTUME (neither triggered by
the fork — it does not split m from β·m; stated on Brick 2's
face) · the Cymatics fences (h bare, never valued; no frequency
in Hz; no terrestrial identification).

IMPORTS, counted honestly: `KernelHeatPlanckBridge`,
`MassGibbsPin` (hence `ModularVariance`), `CymaticsBridgePin`.
NOT imported: `MassGibbsPinOG` / `OGResponse`,
`SpectralActionA2`, `CpecBridgePost` — the Einstein card cites
their registrations in prose; no statement of the weld depends
on the slot.

STATUS: STATUS-EPG.md.
-/

import Mathlib.Tactic
import ThetLogos.KernelHeatPlanckBridge
import ThetLogos.MassGibbsPin
import ThetLogos.CymaticsBridgePin

namespace ThetLogos

/-- The two-site energy profile `(0, E)` on `Fin 2` — the
finite-site seat of Brick 2's classical reading. This is the
profile of `massEnergy ![0, 1] E` (MassGibbs' mass form: one mass
scalar `E` carrying the unit profile), stated once here so the
reading's name is fixed. -/
def siteProfile (E : ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then 0 else E

/-- **The Planck (bosonic ladder) reading** of "the mean energy
at energy `E` and cold `β`": `U_P(β, E) = E · planckFactor β E =
E / (e^{βE} − 1)`. A definition citing KHP's ownership (KHP-2's
factor; the singleton of KHP-4's sum) — not a re-proof
(K-EPG-DUP). -/
noncomputable def planckMeanEnergy (β E : ℝ) : ℝ :=
  E * planckFactor β E

/-- **The finite-site (classical) reading** of the same words:
`U_F(β, E)`, the Gibbs mean energy of the two-site profile
`(0, E)` in `ModularVariance` — MassGibbs' home seat. Brick 2
evaluates it in closed form and proves the fork between the two
readings; they are never identified (K-EPG-STATISTICS). -/
noncomputable def siteMeanEnergy (β E : ℝ) : ℝ :=
  ModularVariance.meanEnergy (siteProfile E) β

/-! ## Brick 1 — the shell weld (Joint 1: Planck ∘ hf)

KHP-4 prices any finite family of positive-energy modes as a
Planck sum but names no family; Cymatics prices the shell's modes
(`E = h·√λ`) but is athermal — it states no mean energy at all.
This brick instantiates KHP-4 at Cymatics' priced positive ladder
— eigenvalues (4, 4, 4, 6, 6) priced to (2h, 2h, 2h, h√6, h√6) —
and evaluates. The ground mode (λ = 0) is EXCLUDED, on the face:
KHP-4's hypothesis (∀ i, 0 < lam i) cannot seat it — its priced
energy is 0 (`modeEnergy_zero`) and its occupation form is the
divergent ladder, not a term; the same genre of exclusion as
KHP's zero-point flag, carded, never silent. Mass does not enter
this brick: this is the Planck ∘ hf joint only. -/

/-- The priced positive-mode family over `Fin 5`: Cymatics'
ladder eigenvalues (4, 4, 4, 6, 6) under `modeEnergy h` — priced
(2h, 2h, 2h, h√6, h√6) once the ladder values below are applied.
The ground mode (λ = 0) is not a member (see the brick header). -/
noncomputable def pricedShellModes (h : ℝ) : Fin 5 → ℝ :=
  ![CymaticsBridgePin.modeEnergy h 4, CymaticsBridgePin.modeEnergy h 4,
    CymaticsBridgePin.modeEnergy h 4, CymaticsBridgePin.modeEnergy h 6,
    CymaticsBridgePin.modeEnergy h 6]

/-- The λ = 4 ladder value in priced form: `modeEnergy h 4 =
2h` — Cymatics' `modeEnergy_fiedler` computation at the numeral
(the landed lemma prices `fiedler shellW`; the shell's Fiedler
value is 4, and this is the same √4 = 2 step at the ladder entry
itself). -/
theorem modeEnergy_four (h : ℝ) :
    CymaticsBridgePin.modeEnergy h 4 = 2 * h := by
  rw [CymaticsBridgePin.modeEnergy,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  ring

/-- The priced ladder is positive at `h > 0` — KHP-4's seating
hypothesis for the family. -/
theorem pricedShellModes_pos {h : ℝ} (hh : 0 < h) :
    ∀ i, 0 < pricedShellModes h i := by
  have h4 : 0 < CymaticsBridgePin.modeEnergy h 4 := by
    rw [modeEnergy_four]; linarith
  have h6 : 0 < CymaticsBridgePin.modeEnergy h 6 := by
    rw [CymaticsBridgePin.modeEnergy_six]
    exact mul_pos hh (Real.sqrt_pos.mpr (by norm_num))
  intro i
  fin_cases i <;> simp [pricedShellModes] <;> assumption

/-- **The keystone (Joint 1).** The shell's total Gibbs mean
energy in closed form: `U_shell(β, h) = 6h / (e^{2βh} − 1) +
2h√6 / (e^{βh√6} − 1)` for `β > 0`, `h > 0` — KHP-4's Planck sum
(`gibbsMeanEnergy_eq`, cited) instantiated at the priced ladder
and evaluated over `Fin 5`. Each mode's mean occupation is
KHP-2's Planck factor at its hf-priced energy. No shelf states
this equality (K-EPG-RENAME strike-check, scope §Joint 1). -/
theorem shellMeanEnergy_eq {β h : ℝ} (hβ : 0 < β) (hh : 0 < h) :
    gibbsMeanEnergy (pricedShellModes h) β
      = 6 * h / (Real.exp (2 * β * h) - 1)
        + 2 * h * Real.sqrt 6
          / (Real.exp (β * (h * Real.sqrt 6)) - 1) := by
  have term4 : (2 * h) * planckFactor β (2 * h)
      = 2 * h / (Real.exp (2 * β * h) - 1) := by
    rw [planckFactor, show β * (2 * h) = 2 * β * h by ring,
      mul_one_div]
  have term6 : (h * Real.sqrt 6) * planckFactor β (h * Real.sqrt 6)
      = h * Real.sqrt 6 / (Real.exp (β * (h * Real.sqrt 6)) - 1) := by
    rw [planckFactor, mul_one_div]
  rw [gibbsMeanEnergy_eq β hβ (pricedShellModes_pos hh),
    Fin.sum_univ_five]
  simp [pricedShellModes, modeEnergy_four,
    CymaticsBridgePin.modeEnergy_six]
  rw [term4, term6]
  have d1 : (Real.exp (2 * β * h) - 1) ≠ 0 := by
    have h1 : (1 : ℝ) < Real.exp (2 * β * h) :=
      Real.one_lt_exp_iff.mpr (by positivity)
    linarith
  have d2 : (Real.exp (β * (h * Real.sqrt 6)) - 1) ≠ 0 := by
    have h1 : (1 : ℝ) < Real.exp (β * (h * Real.sqrt 6)) :=
      Real.one_lt_exp_iff.mpr (by positivity)
    linarith
  field_simp
  ring

/-! ## Brick 2 — the statistics fork (Joint 2)

The corpus owns TWO Gibbs readings of "the mean energy at energy
E and cold β", on two different seats, and no shelf compares
them: Brick 0's `planckMeanEnergy` (the bosonic ladder reading)
and `siteMeanEnergy` (the finite-site reading). This brick
evaluates the finite-site reading in closed form, proves the
exact relation between the readings, and proves they are NOT the
same reading. **K-EPG-STATISTICS stands as this brick's fence:**
the two readings are related by the fork and distinguished by
it — never identified. And **K-MASSGIBBS-SPLIT does not
trigger**, stated on the face: the fork does not separate m from
β·m — both readings run through the single product β·E (the mass
reading below) — so MassGibbs' identification (MG-1/MG-5) stands
exactly where its pin put it, inside the finite-site seat. -/

/-- **The finite-site closed form.** `U_F(β, E) = E / (e^{βE} +
1)`: the two-site Gibbs mean energy, by finite evaluation of
`ModularVariance`'s `partSum` / `gibbsProb` over `Fin 2` — the
closed form no shelf states (strike-checked, scope §Joint 2).
Holds at every `β, E` (the partition sum is a sum of positive
exponentials, never 0). -/
theorem siteMeanEnergy_eq (β E : ℝ) :
    siteMeanEnergy β E = E / (Real.exp (β * E) + 1) := by
  have hpart : ModularVariance.partSum (siteProfile E) β
      = 1 + Real.exp (-(β * E)) := by
    rw [ModularVariance.partSum, Fin.sum_univ_two]
    simp [siteProfile]
  have hmul : Real.exp (β * E) * Real.exp (-(β * E)) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : (0 : ℝ) < Real.exp (-(β * E)) := Real.exp_pos _
  have hne : (1 + Real.exp (-(β * E))) ≠ 0 := by
    have := hpos; linarith
  rw [siteMeanEnergy, ModularVariance.meanEnergy,
    ModularVariance.gibbsExpect, Fin.sum_univ_two,
    ModularVariance.gibbsProb, ModularVariance.gibbsProb, hpart]
  simp only [siteProfile]
  rw [if_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]
  field_simp
  linear_combination E * hmul

/-- **The fork relation.** `U_P(β, E) − U_F(β, E) = 2 ·
U_P(2β, E)` for `β, E > 0` — the exact relation between the
corpus's two Gibbs readings: E/(e^{βE} − 1) − E/(e^{βE} + 1) =
2E/(e^{2βE} − 1). Pure algebra from the two closed forms
(Brick 0's definition and `siteMeanEnergy_eq` above), with
e^{2βE} = (e^{βE})². -/
theorem planck_sub_site_eq {β E : ℝ} (hβ : 0 < β) (hE : 0 < E) :
    planckMeanEnergy β E - siteMeanEnergy β E
      = 2 * planckMeanEnergy (2 * β) E := by
  have hX2 : Real.exp ((2 * β) * E) = (Real.exp (β * E)) ^ 2 := by
    have hrw : (2 * β) * E = ((2 : ℕ) : ℝ) * (β * E) := by
      norm_num; ring
    rw [hrw, Real.exp_nat_mul]
  have hXpos : (0 : ℝ) < Real.exp (β * E) := Real.exp_pos _
  have hX1 : (1 : ℝ) < Real.exp (β * E) :=
    Real.one_lt_exp_iff.mpr (mul_pos hβ hE)
  have key : ∀ X : ℝ, (1 : ℝ) < X → (0 : ℝ) < X →
      E * (1 / (X - 1)) - E / (X + 1)
        = 2 * (E * (1 / (X ^ 2 - 1))) := by
    intro X hX1X hX0X
    have hne1 : (X - 1) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hX1X)
    have hne2 : (X + 1) ≠ 0 := ne_of_gt (by linarith)
    have hne3 : (X ^ 2 - 1) ≠ 0 := by
      have hfact : X ^ 2 - 1 = (X - 1) * (X + 1) := by ring
      rw [hfact]; exact mul_ne_zero hne1 hne2
    field_simp
    ring
  rw [siteMeanEnergy_eq, planckMeanEnergy, planckMeanEnergy,
    planckFactor, planckFactor, hX2]
  exact key _ hX1 hXpos

/-- **The separation corollary.** `U_F ≠ U_P` at every
`β, E > 0`: the two Gibbs seats are NOT the same reading, and
MG-1's identification does not transport across seats. Their
difference is `2 · U_P(2β, E) > 0` by the fork. This corollary
is K-EPG-STATISTICS' teeth. -/
theorem siteMeanEnergy_ne_planck {β E : ℝ} (hβ : 0 < β)
    (hE : 0 < E) : siteMeanEnergy β E ≠ planckMeanEnergy β E := by
  intro hcon
  have hfork := planck_sub_site_eq hβ hE
  rw [← hcon, sub_self] at hfork
  have hpos : 0 < planckMeanEnergy (2 * β) E := by
    rw [planckMeanEnergy, planckFactor]
    apply mul_pos hE
    apply div_pos one_pos
    have h1 : (1 : ℝ) < Real.exp ((2 * β) * E) :=
      Real.one_lt_exp_iff.mpr (by
        have := mul_pos hβ hE; linarith)
    linarith
  linarith

/-- **The mass reading of the fork.** Both readings are the mass
times a function of the single product `β·m`: `U_P(β, m) = m ·
g_P(β·m)` and `U_F(β, m) = m · g_F(β·m)`. The fork separates
two ENSEMBLES, never m from β·m — K-MASSGIBBS-SPLIT explicitly
not triggered, and MassGibbs' seat-relative identification
("mass = Gibbs", MG-1/MG-5) stands untouched inside its seat. -/
theorem fork_mass_reading :
    ∃ gP gF : ℝ → ℝ, ∀ β m : ℝ,
      planckMeanEnergy β m = m * gP (β * m)
        ∧ siteMeanEnergy β m = m * gF (β * m) :=
  ⟨fun x => planckFactor 1 x, fun x => 1 / (Real.exp x + 1), by
    intro β m
    constructor
    · simp only [planckMeanEnergy, planckFactor, one_mul]
    · rw [siteMeanEnergy_eq, mul_one_div]⟩

end ThetLogos
