import ThetLogos.SpectralActionBridge
import ThetLogos.GravityPoseDecision
import ThetLogos.GravityPoseResponse
import ThetLogos.DiracTorsionMap

namespace ThetLogos

/-!
# ThetLogos.CpecBridgePost - CPEC-0: the bridge pin

**Working label only.** The module name `CpecBridgePost` and the
line name CPEC are working labels; Jeff names. Nothing in this
module is a name Jeff has given.

**Status: REGISTRATION ONLY - definitions, statement pins,
named-absence and remainder registration structures, and
pin-grade read-backs of landed theorems. This pin asserts
nothing new. NO CLAIM. No gravity object is defined,
constructed, or asserted to exist. Dial 2 = 0, dials 0/4.**

Governing text: `routeb-general-scratch/scoping-cpec-bridge-2026-10-31.md`
(section 0 ceiling, section 1 pillar census, section 2 six
wires, section 3 pin contents, section 5 kills), commissioned
by the pack `routeb-general-scratch/pack-cpec-0.md`. The grades
below are PINNED by that memo: this pin registers them; it does
not re-grade, soften, or raise any of them. Interface-first:
this pin lands as its own parent-verified commit before any
follow-on brick; no later brick may rename or silently extend
it.

## Section 0 ceiling (verbatim in effect, on the face)

The strongest landing this whole program could ever produce
is a proved MAP plus decided spans: for each wire between the
four named pillars, decided (with the deciding theorem cited),
statable in owned vocabulary, statable only as a finite
shadow, or unstatable (with the exact missing vocabulary
named). The bridge as a physical claim remains Jeff's T5
seeing, untouched by anything here. Nothing in this program
seats a gravity object, moves Dial 2 at all, or brings the
continuum closer; NO CLAIM on any Millennium Problem, parts
closed 0.

## The four pillars, at their section 1 grades

- **Connes - owned, heavily (T1).** The corpus is Connes-style
  spectral triples throughout; the Connes distance line is
  COMPLETE and the spectral action's finite theory is landed.
  The pillar's owned cutoff action is registered below as
  `cpecConnesAction`, citing the landed `finiteSpectralAction`
  of `SpectralActionBridge`.
- **Planck - absent as an object.** The name's only occurrence
  in the Lean tree is one fence line (`SMHiggsBreaking.lean:502`:
  the hierarchy question - why the Higgs scale sits far below
  the Planck scale - is unasked and unanswered there). There is
  no Planck-scale object, no Planck length, and no
  measured-scale theorem anywhere in the corpus. Registered
  below as the named absence `CpecPillarPlanckAbsent` - one
  fence line only.
- **Einstein - a slot, not equations.** The Einstein-Hilbert
  slot of the corpus's a2 is occupied, separated, and proved
  nonzero: the coefficient `a2GravCoeff` of `SpectralActionA2`,
  registered below as `cpecEinsteinSlotCoeff` and
  `CpecEinsteinSlot`. The equations themselves are absent; see
  the W4 registration for the exact admission price. The home
  module's own fence stands: not spacetime gravity, not a
  gravity object, not a derivation of Einstein's equations,
  and not a Dial-2 movement.
- **Cartan - thin but real, with two name collisions
  registered.** Owned (T1): the defect law of `EdgeSignature`
  (`torsion_defect`, `torsion_flat_iff`) and its Dirac
  instantiation in `DiracTorsionMap` (`defect`,
  `dirac_torsion_flat_iff`), registered below as
  `cpecCartanDefect` and `CpecCartanFlat`. Collision 1:
  `XYZTripotents.lean:511` uses "Cartan" in Mathlib's Lie sense
  - the diagonal (Cartan) subalgebra - which is vocabulary of
  that pin, not an owned Elie-Cartan object; spending it as
  this pillar is K-CPEC-CARTAN-NAME. Collision 2: `ProductTriple`'s
  "twist" is the flip twist of first-order-condition machinery
  - twisted spectral triples - a different word from torsion;
  twisted is not torsion, and no statement here blends them.

## DiracTorsionMap's own fences, riding along

Wherever the defect law is registered in this pin, its home
fence repeats: this "torsion" is the algebraic defect of a
deformed fundamental symmetry under inner fluctuation; it is
NOT the antisymmetric part of an affine connection. The home
module's face states it plainly: no continuum operator, **no
connection**. Any wire statement trading on the shared word
without this fence is a smuggle (K-CPEC-TORSION-IMPORT).

## The six wires, at their section 2 grades verbatim

- **W1 Connes-Planck: FINITE SHADOW ONLY, decided by form.**
  Registered as `CpecW1FiniteShadowOnly`: the scale and the
  cutoff coefficients are free inputs of the landed
  `finite_spectral_action_expansion` (`SpectralActionBridge.lean:158`,
  holding for all `c : Fin 3 -> ℂ` and all `Λ : ℂ`); the finite
  data constrain neither. Registration ONLY - no decision
  theorem is registered or priced for this wire; a proof of
  such a theorem would be reading the universal form back
  (K-GR-VAC shape).
- **W2 Connes-Einstein: CLOSED / DECIDED (negative).**
  Registered as `CpecW2ConnesEinsteinDecided`, citing the
  landed `poseKill_decision` (`GravityPoseDecision.lean`): the
  coefficient is imported, not derived. The response half is
  cited beside it: `poseVarA_discharged`
  (`GravityPoseResponse.lean`) - the finite action's numbers do
  respond lawfully to inner fluctuation; the curvature slot's
  response exists only in the abstract variable. Restatement
  of this decision in friendlier words is
  K-CPEC-EINSTEIN-RESTATE, void on sight, named on this face.
- **W3 Connes-Cartan: STATABLE, main span already landed**
  (`DiracTorsionMap.lean`, 2026-10-22). Registered as
  `CpecW3ConnesCartan` (the sign seat's survival verdict), with
  its remainders and gates in `CpecW3Remainders`: CC-1 the
  J-seat (priced remainder); CC-2 triplication - **FIRED by
  Jeff 2026-11-01 00:28 EDT as "the unity brick"**, registered
  here as a fired remainder, its sweep gate unchanged; named
  unpriced spans R1 (general sign) and R4 (twisted-FOC weld),
  each needing its own scoping; gates: the two owed direct
  axiom sweeps, of `EdgeSignature` (hard gate for CC-1) and of
  `DiracTorsionMap` (hard gate for CC-2).
- **W4 Planck-Einstein: UNSTATABLE.** Registered as the named
  absent wire `CpecW4PlanckEinsteinAbsent`, citing the
  admission price of `UltimateReduction.lean:233-241` in
  effect: (i) a manifold factor with a Lorentzian metric,
  (ii) a stress-energy operator, (iii) the equations as a
  machine-checked relation. The `ProductTriple` frame is an
  uninstantiated T2 class - a frame with no instance is not a
  down payment.
- **W5 Planck-Cartan: KILLED at scoping.** Registered as the
  killed wire `CpecW5PlanckCartanKilled`, with its receipt:
  one end a scale-free law (the defect law quantifies over an
  arbitrary ring with `η * η = 1`; there is no scale, dimension,
  or parameter in it for a Planck word to attach to), no other
  end (no Planck object; the corpus's only Planck sentence is
  a refusal to ask), and no middle (no owned statement relates
  a scale to the defect, and manufacturing one would be a
  rename). The kill is part of the map.
- **W6 Einstein-Cartan: UNSTATABLE as a wire; one finite
  shadow statable.** The wire's absence is registered as
  `CpecW6WireAbsent` (three missing vocabularies: a
  connection, a spin-density tensor, and field equations).
  The one statable shadow is registered verbatim as
  `CpecW6Shadow`, with supplied parameters `(y, s)`, never
  existentially quantified: along the Majorana line
  `s ↦ smDirac ↑y ↑y ↑y ↑y s`, the finite a2 matter slot is an
  explicit function of `(y, s)` in which the torsion parameter
  enters in degree 2 (`2|s|^2`, via the landed
  `sa_finite_a2_yukawa` form) while its torsion defect enters
  in degree 1 (`(↑y)⁻¹ * star s`, via `defect_entry`). The
  Einstein-Cartan (ECSK) reading of that degree pattern is a
  T4 rhyme, printed here on the face as a rhyme, never inside
  a statement.

## Pre-registered kills, named on the face

Carried over from the governing memos: K-GR-VAC, K-GR-SMUG,
K-GR-LAUNDER, K-GR-STAB, K-GR-BUY. The CPEC instances
(memo section 5):

- **K-CPEC-PLANCK-RENAME** (K-GR-VAC instance): any "Planck
  wire" content whose scale is a renamed cutoff or chosen
  input. The W1 registration above (free by form) is the only
  licensed Planck sentence in this program.
- **K-CPEC-EINSTEIN-RESTATE** (K-GR-LAUNDER instance): any
  brick, dossier, or draft restating the imported coefficient
  as a derivation, or the W2 decision as "progress toward
  Einstein." The wire is decided; it does not get re-decided
  in friendlier words. Void on sight.
- **K-CPEC-CARTAN-NAME** (K-GR-SMUG instance): spending
  Mathlib's Lie-theory Cartan material, or the
  `XYZTripotents.lean:511` diagonal-subalgebra usage, as the
  Elie Cartan pillar; or spending the defect law's
  "Maurer-Cartan-type" label as differential geometry (a
  connection, a curvature 2-form, structure equations) - the
  law is ring algebra over an arbitrary ring, and its home
  module fences "no connection" on its face.
- **K-CPEC-TORSION-IMPORT** (K-GR-SMUG instance): importing
  Einstein-Cartan connection-torsion (antisymmetric affine
  connection, spin-density sourcing, ECSK field equations) as
  if the corpus's defect were that object. Different types: a
  matrix defect of a deformed fundamental symmetry versus a
  connection component.
- **K-GR-STAB (CPEC instance):** the EC-1 degree pattern of
  the W6 shadow flipping at a boundary of its seat (`s = 0` is
  the survival point; `y = 0` is outside the seat by the
  landed `y ≠ 0` fence) - any such flip is reported as the
  finding with the seat named, never repaired by silently
  narrowing the seat list.
- **K-GR-BUY:** section 0's paragraph is the whole buy,
  forever. A landed CPEC map is a map.

## What is registered here

1. The pillar registrations: `cpecConnesAction`,
   `CpecPillarPlanckAbsent`, `cpecEinsteinSlotCoeff`,
   `CpecEinsteinSlot`, `cpecCartanDefect`, `CpecCartanFlat`.
2. `CpecW1FiniteShadowOnly` - wire W1, registration only.
3. `CpecW2ConnesEinsteinDecided` - wire W2, decided, with its
   two cited landed theorems read back.
4. `CpecW3ConnesCartan` and `CpecW3Remainders` - wire W3, its
   main span's seat verdict, its remainders and its gates.
5. `CpecW4PlanckEinsteinAbsent` - wire W4, a named absence.
6. `CpecW5PlanckCartanKilled` - wire W5, killed, with receipt.
7. `CpecW6WireAbsent` and `CpecW6Shadow` - wire W6, unstatable
   as a wire, its one finite shadow registered verbatim.

The only proved content is pin-grade read-backs: unfoldings
of the registered definitions and restatements of theorems
already landed in `SpectralActionBridge`,
`GravityPoseDecision`, `GravityPoseResponse`, and
`DiracTorsionMap`, each cited at its read-back. The W1 and W6
registrations are stated, NOT asserted: no member of either
is proved in this module.
-/

/-! ## Pillar registrations -/

/-- **Pillar Connes - owned (T1): the owned cutoff action.**
The finite spectral action of `SpectralActionBridge`, cited
as a definition so the name is code-checked: for a finite
Dirac `D`, cutoff coefficients `c : Fin 3 -> ℂ`, and a scale
`Λ : ℂ`, this is the landed moment expansion's value. The
scale enters the corpus's proved spectral action only as
this free, universally quantified parameter - that is the
Connes end of wire W1, and the Planck end is the absence
registered next. -/
noncomputable def cpecConnesAction (D : Matrix I32 I32 ℂ)
    (c : Fin 3 → ℂ) (Λ : ℂ) : ℂ :=
  finiteSpectralAction D c Λ

/-- **Read-back.** The registered action is exactly the
landed `finiteSpectralAction`, by definition. Pin-grade
only. -/
theorem cpecConnesAction_eq (D : Matrix I32 I32 ℂ)
    (c : Fin 3 → ℂ) (Λ : ℂ) :
    cpecConnesAction D c Λ = finiteSpectralAction D c Λ :=
  rfl

/-- **NAMED ABSENCE - pillar Planck, absent as an object.**
The name's only occurrence in the Lean tree is one fence
line (`SMHiggsBreaking.lean:502`): the hierarchy question is
unasked and unanswered there. There is no Planck-scale
object, no Planck length, and no measured-scale theorem in
the corpus; every measured number is a T2 input. The two
fields are the registration of exactly that absence; both
are labeled opaque - the pin asserts no content for either,
and no inhabitant is supplied. -/
structure CpecPillarPlanckAbsent where
  /-- Opaque (labeled): the missing Planck-scale object.
  Not supplied anywhere in the corpus. -/
  missingPlanckObject : Prop
  /-- Opaque (labeled): the fence field recording that the
  name's sole Lean habitat is the one fence line cited in
  this registration's docstring, not an object. -/
  fenceLineOnly : Prop

/-- **Pillar Einstein - the slot coefficient.** The
Einstein-Hilbert slot of the corpus's a2, as one named
coefficient: `a2GravCoeff` of `SpectralActionA2`, the slope
of the separated a2's R-slot. This is a slot inside a stated
Gilkey form over an abstract scalar that nothing in the
corpus computes - a slot, not equations. -/
noncomputable def cpecEinsteinSlotCoeff : ℂ :=
  a2GravCoeff

/-- **Pillar Einstein - grade: a slot, occupied and nonzero.**
The slot registration: the coefficient registered above is
nonzero. That is the whole Einstein pillar the corpus owns;
the equations are absent (wire W4). -/
def CpecEinsteinSlot : Prop :=
  cpecEinsteinSlotCoeff ≠ 0

/-- **Read-back.** The Einstein slot registration is exactly
its registered statement, unfolded. The slot itself is not
asserted by this read-back. -/
theorem cpecEinsteinSlot_unfold :
    CpecEinsteinSlot ↔ cpecEinsteinSlotCoeff ≠ 0 :=
  Iff.rfl

/-- **Slot read-back, discharged by citation.** The slot is
nonzero, by the landed `a2_grav_coeff_ne_zero` of
`SpectralActionA2`, consumed through the registered
coefficient name. Pin-grade only: a coefficient inside a
chosen standard form, not a derivation of anything. -/
theorem cpecEinsteinSlot_nonzero : CpecEinsteinSlot :=
  a2_grav_coeff_ne_zero

/-- **Pillar Cartan - the defect, at the Dirac arena.** The
corpus's Cartan-shaped object: `defect` of
`DiracTorsionMap`, the Maurer-Cartan-type defect
`η * T + T * η + T * T` of a deformed fundamental symmetry,
cited as a definition so the name is code-checked. Fence,
from its home module's face: this "torsion" is the algebraic
defect of a deformed fundamental symmetry; no connection is
involved, and it is not the antisymmetric part of an affine
connection. -/
def cpecCartanDefect (η T : Matrix I32 I32 ℂ) :
    Matrix I32 I32 ℂ :=
  defect η T

/-- **Pillar Cartan - the flatness law, at the Dirac arena.**
For matrices `η, T` with `η * η = 1`, `η + T` is a fundamental
symmetry if and only if the registered defect vanishes.
This is `EdgeSignature`'s `torsion_flat_iff` instantiated at
the Dirac arena by `DiracTorsionMap` - ring algebra, not
connection geometry (K-CPEC-CARTAN-NAME fence). -/
def CpecCartanFlat : Prop :=
  ∀ (η T : Matrix I32 I32 ℂ), η * η = 1 →
    ((η + T) * (η + T) = 1 ↔ cpecCartanDefect η T = 0)

/-- **Read-back.** The Cartan flatness registration is
exactly its registered statement, unfolded. -/
theorem cpecCartanFlat_unfold :
    CpecCartanFlat
      ↔ ∀ (η T : Matrix I32 I32 ℂ), η * η = 1 →
          ((η + T) * (η + T) = 1 ↔ cpecCartanDefect η T = 0) :=
  Iff.rfl

/-- **Flatness read-back, discharged by citation.** The
registered law holds, by the landed
`dirac_torsion_flat_iff` of `DiracTorsionMap`. Pin-grade
only. -/
theorem cpecCartanFlat_holds : CpecCartanFlat :=
  fun η T h => dirac_torsion_flat_iff η T h

/-! ## W1 - Connes-Planck: finite shadow only, decided by form -/

/-- **Wire W1 - grade FINITE SHADOW ONLY, decided by form.**
The wire's only honest predicate, registered: the landed
finite spectral action expansion holds for every finite
Dirac `D`, every cutoff coefficient function
`c : Fin 3 -> ℂ`, and every scale `Λ : ℂ` - the scale and the
coefficients are free inputs of the identity, and the finite
data constrain neither. REGISTRATION ONLY: this statement is
registered as the wire's decision-by-form and is NOT
asserted in this module; a standalone decision theorem for
it is not priced, because its proof would be reading the
universal form back (K-GR-VAC shape, and
K-CPEC-PLANCK-RENAME fences anything warmer). -/
def CpecW1FiniteShadowOnly : Prop :=
  ∀ (D : Matrix I32 I32 ℂ) (c : Fin 3 → ℂ) (Λ : ℂ),
    Matrix.trace (cutoffPolyMat D c Λ)
      = finiteSpectralAction D c Λ

/-- **Read-back.** Wire W1 is exactly its registered
statement, unfolded. This is the definition read back, not
a proof of it - `CpecW1FiniteShadowOnly` is not asserted
anywhere in this module. -/
theorem cpecW1_unfold :
    CpecW1FiniteShadowOnly
      ↔ ∀ (D : Matrix I32 I32 ℂ) (c : Fin 3 → ℂ) (Λ : ℂ),
          Matrix.trace (cutoffPolyMat D c Λ)
            = finiteSpectralAction D c Λ :=
  Iff.rfl

/-! ## W2 - Connes-Einstein: closed, decided negative -/

/-- **Wire W2 - grade CLOSED / DECIDED (negative).** The
wire's question - does the Connes frame derive the Einstein
coefficient? - is answered NO at theorem grade by the landed
decision: the registered content is the pose line's
`PoseKill` (no functional of the finite spectral data alone
carries the R-response), discharged by
`poseKill_decision`. The coefficient is imported, not
derived. Restating this decision in friendlier words is
K-CPEC-EINSTEIN-RESTATE, void on sight. -/
def CpecW2ConnesEinsteinDecided : Prop :=
  PoseKill

/-- **Read-back.** Wire W2 is exactly its registered
statement, unfolded: the pose line's `PoseKill`. -/
theorem cpecW2_unfold :
    CpecW2ConnesEinsteinDecided ↔ PoseKill :=
  Iff.rfl

/-- **W2 decided, as a read-back.** The decision is the
landed `poseKill_decision` of `GravityPoseDecision`,
restated in the pin's name; nothing new is proved. -/
theorem cpecW2_decided : CpecW2ConnesEinsteinDecided :=
  poseKill_decision

/-- **W2 response read-back.** The decision's other half,
cited beside it: along the pose line's frozen fluctuation
path, the finite action's trace-of-square does respond
lawfully - the landed `poseVarA_discharged` of
`GravityPoseResponse`. The response lives in the matter
slot; the curvature slot's response exists only in the
abstract variable. Pin-grade citation only. -/
theorem cpecW2_response_readback (P : PoseVarAPathData) :
    PoseVarA P :=
  poseVarA_discharged P

/-! ## W3 - Connes-Cartan: statable, main span already landed -/

/-- **Wire W3 - grade STATABLE, main span already landed.**
The wire's main span IS `DiracTorsionMap` (landed
2026-10-22): a Connes object (the corpus's Dirac operator)
read through the Cartan-shaped defect law. The registered
content here is the span's sign-seat verdict, in its landed
shape: for a flat-sector scale `y ≠ 0` and every Majorana
parameter `s`, the deformed fundamental symmetry
`etaSign y + torsionMajorana y s` is an involution if and
only if `s = 0` - survival holds exactly at the undeformed
point, and the Majorana block is the seat's torsion, not
flat. The grading seat's verdict (the torsion map is the
zero map, survival proved) is part of the same landed span,
cited in this registration's prose. The naming fence of the
pillar registration governs every word of this statement:
algebraic defect of a deformed fundamental symmetry, no
connection. -/
def CpecW3ConnesCartan : Prop :=
  ∀ (y : ℝ), y ≠ 0 → ∀ s : ℂ,
    ((etaSign y + torsionMajorana y s)
        * (etaSign y + torsionMajorana y s) = 1 ↔ s = 0)

/-- **Read-back.** Wire W3 is exactly its registered
statement, unfolded. The statement itself is read back from
the landed span by `cpecW3_seat2_readback` below. -/
theorem cpecW3_unfold :
    CpecW3ConnesCartan
      ↔ ∀ (y : ℝ), y ≠ 0 → ∀ s : ℂ,
          ((etaSign y + torsionMajorana y s)
              * (etaSign y + torsionMajorana y s) = 1 ↔ s = 0) :=
  Iff.rfl

/-- **Seat 2 read-back, discharged by citation.** The
registered verdict is the landed `majorana_survival_iff` of
`DiracTorsionMap`, restated in the pin's name; nothing new
is proved. -/
theorem cpecW3_seat2_readback : CpecW3ConnesCartan :=
  fun y hy s => majorana_survival_iff y hy s

/-- **Wire W3 - remainders, unpriced spans, and gates.**
The landed span's named remainder, registered as labeled
opaque fields; no inhabitant is supplied and no field is
asserted. CC-1: the J-seat (remainder R2 of the home module)
- `UJ` is a fundamental-symmetry candidate whose torsion map
is unbuilt; priced, gated below. CC-2: triplication
(remainder R3) - the torsion map carried to the
three-generation operator; **FIRED by Jeff 2026-11-01
00:28 EDT as "the unity brick"**, registered here as a fired
remainder, its sweep gate unchanged; it studies the
triplicated space and does not derive why three. R1: the
sign of a general `buildDirac` via spectral functional
calculus - a named unpriced span, needing its own scoping.
R4: the weld of torsion-flatness to the twisted
first-order-condition machinery - a named unpriced span,
needing its own scoping (twisted is not torsion; see the
pillar collisions). Gates: the owed direct axiom sweep of
`EdgeSignature` is a hard gate for CC-1, and the owed direct
axiom sweep of `DiracTorsionMap` is a hard gate for CC-2 -
a bridge brick must not be the load that discovers the
corpus's open certification seam. -/
structure CpecW3Remainders where
  /-- Opaque (labeled): CC-1, the J-seat torsion map.
  Priced remainder; unbuilt. -/
  cc1JSeat : Prop
  /-- Opaque (labeled): CC-2, the triplication seat. Fired
  remainder (Jeff, 2026-11-01, "the unity brick"); its sweep
  gate is the field below, unchanged by the firing. -/
  cc2TriplicationFired : Prop
  /-- Opaque (labeled): R1, the general sign of a
  `buildDirac`. Named unpriced span; own scoping owed. -/
  r1GeneralSignUnpriced : Prop
  /-- Opaque (labeled): R4, the torsion-flatness weld to
  the twisted first-order-condition machinery. Named
  unpriced span; own scoping owed. -/
  r4TwistedFOCWeldUnpriced : Prop
  /-- Opaque (labeled): the hard gate for CC-1 - the owed
  direct axiom sweep of `EdgeSignature`. -/
  edgeSignatureSweepGate : Prop
  /-- Opaque (labeled): the hard gate for CC-2 - the owed
  direct axiom sweep of `DiracTorsionMap`. -/
  diracTorsionMapSweepGate : Prop

/-! ## W4 - Planck-Einstein: unstatable, a named absent wire -/

/-- **NAMED ABSENCE - wire W4, grade UNSTATABLE.** Neither
end exists (pillar census): no Planck object, and no
Einstein equations. The fields register the exact admission
price of `UltimateReduction.lean:233-241`: (i) a manifold
factor with a Lorentzian metric, (ii) a stress-energy
operator built from the triple's fields, (iii) the Einstein
equations as a machine-checked relation between them. The
fourth field registers the frame note: the `ProductTriple`
frame is admission item (i)'s shape as an uninstantiated T2
class - a frame with no instance is not a down payment on
(i). All fields are labeled opaque; no inhabitant is
supplied and nothing is asserted. -/
structure CpecW4PlanckEinsteinAbsent where
  /-- Opaque (labeled): admission item (i) - a manifold
  factor with a Lorentzian metric. Not supplied. -/
  missingManifoldFactor : Prop
  /-- Opaque (labeled): admission item (ii) - a
  stress-energy operator. Not supplied. -/
  missingStressEnergyOperator : Prop
  /-- Opaque (labeled): admission item (iii) - the
  equations as a machine-checked relation. Not supplied. -/
  missingEinsteinEquationsRelation : Prop
  /-- Opaque (labeled): the fence field recording that the
  `ProductTriple` frame is an uninstantiated T2 class, not
  a down payment on admission item (i). -/
  productTripleFrameUninstantiated : Prop

/-! ## W5 - Planck-Cartan: killed at scoping, with its receipt -/

/-- **KILLED WIRE - wire W5, grade DOES NOT SURVIVE.** A
wire needs two ends and a statable middle. This wire has
one end (a scale-free algebraic law: the defect law
quantifies over an arbitrary ring with `η * η = 1`, and its
Dirac seats attach the defect to dimensionless matrix data),
no other end (no Planck object exists, and the corpus's
only Planck sentence is a refusal to ask), and no middle
(no owned statement relates a scale to the defect, and
manufacturing one would compose K-CPEC-PLANCK-RENAME with
K-CPEC-TORSION-IMPORT). There is no T4 anchor of standing.
The fields register the receipt of the kill; all are
labeled opaque, no inhabitant is supplied, and the kill -
not an absence politely stated - is the registration. -/
structure CpecW5PlanckCartanKilled where
  /-- Opaque (labeled): the Planck end - absent; no Planck
  object exists for the wire to attach to. -/
  planckEndAbsent : Prop
  /-- Opaque (labeled): the Cartan end - the defect law is
  scale-free by construction; no scale attaches to it. -/
  cartanLawScaleFree : Prop
  /-- Opaque (labeled): the middle - no owned statement
  relates a scale to the defect. -/
  noMiddleStatement : Prop

/-! ## W6 - Einstein-Cartan: unstatable as a wire, one shadow -/

/-- **NAMED ABSENCE - wire W6 as a wire, grade UNSTATABLE.**
The wire as physics - torsion sourced by spin, feeding back
into the gravitational equations - needs three vocabularies
the corpus does not own, each named in
`UltimateReduction.lean:233-241` or in `DiracTorsionMap`'s
own no-connection fence. The fields register exactly those
absences; all are labeled opaque, no inhabitant is
supplied, and nothing is asserted. The one finite shadow
that IS statable is registered separately, immediately
below, as `CpecW6Shadow`. -/
structure CpecW6WireAbsent where
  /-- Opaque (labeled): the missing connection. The corpus's
  defect is not a connection component. -/
  missingConnection : Prop
  /-- Opaque (labeled): the missing spin-density tensor. -/
  missingSpinDensityTensor : Prop
  /-- Opaque (labeled): the missing field equations
  relating torsion, spin, and the gravitational slot. -/
  missingFieldEquations : Prop

/-- **Wire W6 - the one statable finite shadow, registered
verbatim.** Stated with supplied parameters `(y, s)`, never
existentially quantified: along the Majorana line
`s ↦ smDirac ↑y ↑y ↑y ↑y s` on the flat sector, under the
seat fence `y ≠ 0`, the finite a2 matter slot - the trace of
the square of the line's operator, in the landed
`sa_finite_a2_yukawa` form - is the displayed explicit
function of `(y, s)`, in which the torsion parameter enters
in degree 2 (the `2 * Complex.normSq s` term), AND the
torsion defect at its witness entry is the displayed value
of `defect_entry`, in which the parameter enters in degree 1
(the `(↑y)⁻¹ * star s` term, linear in `star s`). This
registration is finite arithmetic about two landed objects.
The Einstein-Cartan reading of the degree pattern is a T4
rhyme, on this module's face in the header, never inside
this statement. REGISTERED ONLY: the shadow is NOT asserted
in this module; its decision is the follow-on brick EC-1,
gated on the owed direct axiom sweep of `DiracTorsionMap`,
and any degree flip at a seat boundary is a finding under
the K-GR-STAB CPEC instance, never a silent repair. Fence,
repeated from the defect's home: the defect here is the
algebraic defect of a deformed fundamental symmetry - no
connection. -/
def CpecW6Shadow (y : ℝ) (s : ℂ) : Prop :=
  y ≠ 0 →
    Matrix.trace ((smDirac (y : ℂ) (y : ℂ) (y : ℂ) (y : ℂ) s) ^ 2)
      = (((4 * (Complex.normSq (y : ℂ) + Complex.normSq (y : ℂ)
              + 3 * Complex.normSq (y : ℂ)
              + 3 * Complex.normSq (y : ℂ))
            + 2 * Complex.normSq s) : ℝ) : ℂ)
    ∧ (defect (etaSign y) (torsionMajorana y s))
        ⟨0, by norm_num⟩ ⟨24, by norm_num⟩
      = (y : ℂ)⁻¹ * star s

/-- **Read-back.** The W6 shadow is exactly its registered
statement, unfolded, at the same supplied parameters `(y, s)`.
This is the definition read back, not a decision of it -
`CpecW6Shadow` is not asserted for any parameters anywhere
in this module. -/
theorem cpecW6Shadow_unfold (y : ℝ) (s : ℂ) :
    CpecW6Shadow y s
      ↔ (y ≠ 0 →
          Matrix.trace
              ((smDirac (y : ℂ) (y : ℂ) (y : ℂ) (y : ℂ) s) ^ 2)
            = (((4 * (Complex.normSq (y : ℂ)
                    + Complex.normSq (y : ℂ)
                    + 3 * Complex.normSq (y : ℂ)
                    + 3 * Complex.normSq (y : ℂ))
                  + 2 * Complex.normSq s) : ℝ) : ℂ)
          ∧ (defect (etaSign y) (torsionMajorana y s))
              ⟨0, by norm_num⟩ ⟨24, by norm_num⟩
            = (y : ℂ)⁻¹ * star s) :=
  Iff.rfl

end ThetLogos
