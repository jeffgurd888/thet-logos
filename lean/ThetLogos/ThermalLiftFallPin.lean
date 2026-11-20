import Mathlib.Tactic
import ThetLogos.ThermalLiftPin

/-!
# ThetLogos.ThermalLiftFallPin — THERMAL LIFT, record pin (LIFT-0b)

Companion to `ThermalLiftPin` (LIFT-0a), same commission and
fences. **0 theorems, 0 strict, by design.** This pin freezes
the fall vocabulary of brick LIFT-2, the grounded thermal
potential, and the frozen target forms of LIFT-2 (fall inside
the gradient), LIFT-3 (cold out of heat) and ST-1 (surface
tension form) as `Prop`s between independently defined
objects.

**The fed source, stated once.** Both landed channels see a
source through its contrast: the closed channel by
construction (`poissonPotential` solves for `meanSub g`),
the grounded channel here by this pin's choice — the
grounded thermal potential is the grounded potential of the
*mean-subtracted profiled source*. One contrast, two
channels; the choice is disclosed here, not hidden in a
proof. (K-LIFT-BLIND is the reason: the total is not data
any channel of this line may use.)

**Fall vocabulary.** `IsThermalFallMin` and
`ThermalFallPath` mirror FALL-1's descent bookkeeping
(`IsFallMin`, `FallPath` — lane grade at the time of
writing) under this line's own names: FALL-1 is cited at
its grade if landed, never depended on. Descent is
bookkeeping over a potential — statics, not dynamics; no
motion is defined or claimed (the D2-0 board owns motion).

**Kill registry and fences:** as `ThermalLiftPin`'s face —
K-LIFT-EQUIL (already a theorem), K-LIFT-BLIND, K-LIFT-SIGN,
K-LIFT-COSTUME, K-LIFT-PROFILE, K-GR-LAUNDER all stand.
**Dial 2 = 0 under every outcome. NO CLAIM; dials 0/4.**
-/

namespace ThetLogos

open Filter

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## §1. The contrast and the grounded thermal potential -/

/-- **The thermal contrast**: the mean-subtraction of the
profiled thermal source — the only face of the source any
channel of this line sees (K-LIFT-BLIND). Sums to zero,
always (`sum_meanSub_eq_zero`). -/
noncomputable def thermalContrast (β : V → ℝ) (E : V → ℝ) :
    V → ℝ :=
  meanSub (profThermalSource β E)

/-- **The grounded thermal potential**: the grounded
seat's canonical potential for the thermal contrast,
pinned to `0` at the ground `b`
(`BoundarySeat.groundedPotential`, cited by application).
At every ungrounded site it solves `L φ = contrast`
(`laplacianOp_groundedPotential`). -/
noncomputable def groundedThermalPotential (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (β : V → ℝ)
    (E : V → ℝ) : V → ℝ :=
  groundedPotential w hw hw0 hpos b (thermalContrast β E)

/-! ## §2. Fall vocabulary (bookkeeping) -/

/-- A **thermal fall minimum** of a potential `φ`: no site
sits strictly below `m`. (On the grounded seat every site
is adjacent to every other — `hpos` — so this is also the
global minimum; it is stated in descent language because
descent is what LIFT-2 is about.) -/
def IsThermalFallMin (φ : V → ℝ) (m : V) : Prop :=
  ∀ j ≠ m, φ m ≤ φ j

/-- A **thermal fall path** from `i` to `k`: a finite chain
of strict decreases of `φ`. Bookkeeping for the
termination statement; the step rule is a definition, and
no dynamics is claimed for it. -/
inductive ThermalFallPath (φ : V → ℝ) : V → V → Prop
  | refl (i : V) : ThermalFallPath φ i i
  | step {i j k : V} (hji : φ j < φ i)
      (hjk : ThermalFallPath φ j k) : ThermalFallPath φ i k

/-! ## §3. Frozen target forms for LIFT-2 -/

/-- **LIFT-2 target, the descent step.** At an ungrounded
site where the thermal contrast is positive, some site
sits strictly lower in the grounded thermal potential —
the fall inside the gradient, one step. -/
def ThermalDescentForm (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (β : V → ℝ)
    (E : V → ℝ) : Prop :=
  ∀ {i : V}, i ≠ b → 0 < thermalContrast β E i →
    ∃ j ≠ i, groundedThermalPotential w hw hw0 hpos b β E j
      < groundedThermalPotential w hw hw0 hpos b β E i

/-- **LIFT-2 target, the ground form.** Under the sign
condition — the thermal contrast nonnegative at every
ungrounded site (the ground carries the below-mean face
of the contrast) — the ground is a thermal fall minimum
of the grounded thermal potential. K-LIFT-SIGN is the
registered boundary: without the sign condition this
form is expected to die, and its countermodel is part of
LIFT-2's brick. -/
def ThermalGroundForm (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (β : V → ℝ)
    (E : V → ℝ) : Prop :=
  (∀ i, i ≠ b → 0 ≤ thermalContrast β E i) →
    IsThermalFallMin
      (groundedThermalPotential w hw hw0 hpos b β E) b

/-- **LIFT-2 target, termination.** From any site, a
thermal fall path over the grounded thermal potential
reaches a thermal fall minimum in finitely many steps.
Pure finite combinatorics — no thermal data is used. -/
def ThermalTerminationForm (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (β : V → ℝ)
    (E : V → ℝ) : Prop :=
  ∀ i, ∃ m, IsThermalFallMin
      (groundedThermalPotential w hw hw0 hpos b β E) m
    ∧ ThermalFallPath
      (groundedThermalPotential w hw hw0 hpos b β E) i m

/-! ## §4. Frozen target form for LIFT-3 -/

/-- **LIFT-3 target, the cold face.** At a site strictly
above the energy floor `E i₀`, the constant-profile Gibbs
weight dies as `β → ∞`: the cold face is a limit of the
heat family, not a separate state. (The quantitative
bounds behind this limit — monotonicity at the floor and
the `e^{−βΔ}` off-floor bound — are LIFT-3's supporting
theorems; their shape is proved at the diagonal seat by
the lane-grade `HotColdLimits`, consumed at its grade and
cited on LIFT-3's face.) -/
def ColdTieForm (E : V → ℝ) (i₀ : V) : Prop :=
  (∀ i, E i₀ ≤ E i) → ∀ i, E i₀ < E i →
    Tendsto (fun β : ℝ => profWeight (fun _ => β) E i)
      atTop (nhds 0)

/-! ## §5. Frozen target forms for ST-1 -/

/-- **ST-1 target, the field form.** The interface energy
of the profiled thermal potential across a region's cut
is the conductance-weighted sum of the profiled thermal
*field* over the same cut — the interface energy is the
field, integrated over the boundary. -/
def CutFieldForm (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (β : V → ℝ)
    (E : V → ℝ) (S : Finset V) : Prop :=
  cutEnergy w (profThermalPotential w hw hw0 hpos β E) S
    = ∑ i ∈ S, ∑ j ∈ Sᶜ, w i j
      * profThermalField w hw hw0 hpos β E i j

/-- **ST-1 target, the flip form.** Reversing a region
reverses its interface energy: the cut energy of the
complement is the negative of the cut energy of the
region (conductances symmetric). An interface has two
sides and one tension, read in opposite directions. -/
def CutFlipForm (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (φ : V → ℝ)
    (S : Finset V) : Prop :=
  cutEnergy w φ Sᶜ = - cutEnergy w φ S

end ThetLogos
