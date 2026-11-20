import Mathlib.Tactic
import ThetLogos.ThermalSourceComposite
import ThetLogos.BoundarySeat

/-!
# ThetLogos.ThermalLiftPin — THERMAL LIFT, record pin (LIFT-0a)

Lane brick, commissioned by Zero 2026-11-17 ("yes scope it" →
"build it") on the THERMAL LIFT scope
(`~/workspace/your_files/thermal-lift-scope-2026-11-17.md`).
Working label only — public naming is Zero's.

**What this pin freezes (0 theorems, 0 strict, by design).**
The profiled thermal source — T1's profiled Gibbs weight
(`ThermalProfileSeparation.profWeight`, β a *profile*
`β : V → ℝ`) times the site energies — its potential, field
and flow through the landed Poisson channel
(`PoissonTotalMassBlindness.poissonPotential` / `poissonField`
/ `poissonFlow`, cited by application, never redefined), the
interface (cut) energy of a potential, and the frozen target
forms of brick LIFT-1 (the profiled composite) as `Prop`s
between independently defined objects. The fall vocabulary
and the LIFT-2 / LIFT-3 / ST-1 target forms are frozen in the
companion pin `ThermalLiftFallPin`.

**Why a profile.** The landed composite
(`ThermalSourceComposite`) consumes only the *constant*
profile: `thermalSource E β = gibbsProb E β * E`, and
`gibbsProb_eq_profWeight_const` identifies `gibbsProb` with
the profiled weight at `fun _ => β`. A thermal gradient — a
non-constant profile — is stateable in-tree (T1) and has
never been fed to the channel. This line feeds it.

**Kill registry (scope §4, on the face).**
- **K-LIFT-EQUIL** — already a theorem, cited not re-armed:
  a constant thermal source returns the zero field
  (`PoissonTotalMassBlindness.poissonField_const`, read at
  the composite in `ThermalSourceComposite`). Any form of
  this line needing a field at exact uniform equilibrium is
  dead on arrival.
- **K-LIFT-BLIND** — any form needing the source's *total*
  (mean energy / total mass) dies: the channel factors
  through the mean-subtracted source alone
  (`poissonField_eq_of_meanSub_eq`,
  `not_exists_fieldFactor_detects_totalMass`).
- **K-LIFT-SIGN** — if thermal descent strands under
  sign-indefinite contrast, "fall" holds exactly under the
  stated sign condition and the line reports that boundary
  as its result (FALL-1's countermodel is the mirror).
- **K-LIFT-COSTUME** — source and potential stay
  independently defined; the only bridge is the Poisson
  inversion theorem. Definition-stacking kills the brick.
- **K-LIFT-PROFILE** — if the composite's proofs route
  through constant-profile identities that do not
  generalize, LIFT-1 re-prices as a machinery gap at full
  rank; no silent weakening to the constant profile (that
  case is already landed).
- **K-GR-LAUNDER** (standing) — the gravity word attaches
  to no output of this line, in vocabulary or in claim.
  Zero's thesis is the program's direction, not module
  vocabulary.

**Fences.** This pin seats no gravity object, defines no
response law, states no universality, and derives no
attraction sign. It inherits SR-5's pre-registered
dial-ineligibility: **Dial 2 = 0 under every outcome.**
Statics only — no dynamics is defined or claimed
(the fall of LIFT-2 is a descent bookkeeping over a
potential, as in FALL-1). FRONTIER, flagged never priced:
attraction sign; lift as motion (the D2-0 / U-INERTIA
board); continuum Tolman form (K-TOL-PROXY); Young–Laplace.

NO CLAIM; dials 0/4.
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## §1. The profiled thermal source -/

/-- **The profiled thermal source**: at each site, the
profiled Gibbs weight of the site times its energy,
`profWeight β E i * E i`. A function of owned thermal data
only — a temperature *profile* `β : V → ℝ` and site
energies `E` — exactly `ThermalSourceComposite`'s source
with the constant profile replaced by a general one. No
vocabulary from outside the thermal line appears in its
construction, and no mass appears anywhere: the weight is
a probability (T1: `profWeight_pos`,
`sum_profWeight_eq_one`). -/
noncomputable def profThermalSource (β : V → ℝ) (E : V → ℝ) :
    V → ℝ :=
  fun i => profWeight β E i * E i

/-! ## §2. The channel, cited: potential, field, flow -/

/-- **The profiled composite potential**: the landed
Poisson channel's canonical potential for the profiled
thermal source — a potential for its mean-subtraction,
chosen by T2 existence (`poissonPotential`). Cited, not
redefined: the body is the channel applied to §1's
source, and nothing else. -/
noncomputable def profThermalPotential (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (β : V → ℝ)
    (E : V → ℝ) : V → ℝ :=
  poissonPotential w hw hw0 hpos (profThermalSource β E)

/-- **The profiled composite field**: the channel's
canonical field of the profiled thermal source — the edge
drop of §2's potential, well-defined on the nose by T2
uniqueness. -/
noncomputable def profThermalField (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (β : V → ℝ)
    (E : V → ℝ) : V → V → ℝ :=
  poissonField w hw hw0 hpos (profThermalSource β E)

/-- **The profiled composite flow**: the channel's
canonical Ohm flow of the profiled thermal source. -/
noncomputable def profThermalFlow (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (β : V → ℝ)
    (E : V → ℝ) : V → V → ℝ :=
  poissonFlow w hw hw0 hpos (profThermalSource β E)

/-! ## §3. The interface (cut) energy -/

/-- **The interface (cut) energy of a potential across a
region**: the sum over the cut edges — one end in `S`, the
other outside — of the conductance times the potential
drop across the edge, `∑ i ∈ S, ∑ j ∈ Sᶜ, w i j * dropVec
φ i j`. This is ST-1's object: the seat form of an
interface energy of the thermal state on a region's
boundary (an interface is where a gradient concentrates).
Bookkeeping only: no minimization, no curvature law, and
no Young–Laplace form is stated anywhere in this line
(FRONTIER). -/
noncomputable def cutEnergy (w : V → V → ℝ) (φ : V → ℝ)
    (S : Finset V) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ Sᶜ, w i j * dropVec φ i j

/-! ## §4. Frozen target forms for LIFT-1

Each form is a `Prop` between independently defined
objects: §1's source and §2's channel outputs on one side,
T2's mean-subtraction and the landed constant-profile
composite on the other. LIFT-1 proves or kills them; this
pin only freezes their statements. -/

/-- **LIFT-1 target, the Poisson form.** The profiled
composite potential solves the projected problem for the
profiled source: `L φ = meanSub (profThermalSource β E)`.
(The bare form `L φ = profThermalSource β E` is NOT the
target: it is false whenever the source's total is
nonzero — the channel sees the contrast, K-LIFT-BLIND.) -/
def ProfPoissonForm (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (β : V → ℝ)
    (E : V → ℝ) : Prop :=
  laplacianOp w (profThermalPotential w hw hw0 hpos β E)
    = meanSub (profThermalSource β E)

/-- **LIFT-1 target, the contrast form.** The profiled
field and flow factor through the contrast: two profiled
sources with the same mean-subtraction have the same
field and the same flow. (K-LIFT-BLIND's positive face.) -/
def ProfContrastForm (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (β β' : V → ℝ)
    (E E' : V → ℝ) : Prop :=
  meanSub (profThermalSource β E)
      = meanSub (profThermalSource β' E')
    → profThermalField w hw hw0 hpos β E
        = profThermalField w hw hw0 hpos β' E'
      ∧ profThermalFlow w hw hw0 hpos β E
        = profThermalFlow w hw hw0 hpos β' E'

/-- **LIFT-1 target, the reduction form.** At a constant
profile the profiled composite *is* the landed composite:
potential, field and flow agree with
`ThermalSourceComposite`'s on the nose. This is the hinge
that keeps the generalization honest — the new line
contains the landed one as its constant-profile face. -/
def ProfReductionForm (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (β : ℝ)
    (E : V → ℝ) : Prop :=
  profThermalPotential w hw hw0 hpos (fun _ => β) E
      = thermalPotential w hw hw0 hpos E β
    ∧ profThermalField w hw hw0 hpos (fun _ => β) E
      = thermalField w hw hw0 hpos E β
    ∧ profThermalFlow w hw hw0 hpos (fun _ => β) E
      = thermalFlow w hw hw0 hpos E β

end ThetLogos
