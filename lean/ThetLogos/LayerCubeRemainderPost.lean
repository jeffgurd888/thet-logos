import ThetLogos.MaxwellQuadPost

namespace ThetLogos

open Finset

/-!
# ThetLogos.LayerCubeRemainderPost - REM-0: registration pin for the
closure remainder on the finite base

**Status: REGISTRATION ONLY - definitions and stated `Prop`s, plus
`rfl`-grade read-backs. NO CLAIM. No Millennium statement, no ladder
rung, no dial. Nothing in this module asserts that either registered
Prop holds; they are stated as targets for REM-1 and REM-2.**

Commission: Jeff, 2026-11-01 01:02 EDT ("yes" to the offered scoping).
Governing memo: `routeb-general-scratch/scoping-closure-remainder-
2026-11-01.md` (the base audit section 2, the split section 4, the
REM-0 contents section 5, the kills section 7). Working label: REM.
Every name in this module is a working label; naming is Jeff's hand.

## Ceiling (memo section 0, on the face)

Finite remainder only. The words "Lorentzian" and "bridge" are
**unspent in this line**: they appear only inside this fence
sentence, as refused terms, and as the named trigger of K-REM-SMUG
below. **Dial 2 = 0. Dial 3 = 0.** Parts of any Millennium
statement closed by this line: **0**. **NO CLAIM.** Jeff's seeing
(2026-11-01 00:59 EDT) and his framing (01:04 EDT) stay **T5**,
quoted verbatim and attributed; they commissioned a question, they
are not its answer.

## Interfaces (cited, never forked - K-REM-FORK)

This pin consumes the MAX pin `MaxwellQuadPost.lean` BY CITATION:
`plaqAngle`, `allPlaqData`, `maxwellQuad`, `gaugeAngle`, `linkTail`,
`linkHead` are the MAX pin's registered vocabulary, used here and
never redefined or re-registered. In particular **M3 is not
re-registered here under any REM name**, and `plaqAngle` is not
redefined. From `PlaquetteTelescoping.lean`: `PlaqDatum` and its
four edges. From the GEO base: `LayerSite`, `LayerLink`,
`layerLinkOf`, `layerShift` (`PlaneCrossingCube.lean`), and the
`cycDist` material of `LayerCubeDistancePost.lean`, cited as the
geometry the wrap cycles live on.

## The split (memo section 4) and the REM-CYCLE registration

The remainder shape is TWO questions, and this pin's first job is
keeping them apart:

- **REM-CONFIG** (this line, live): a static configuration
  `theta : linkAngle N` on the cube. Its remainder is the pair -
  the plaquette-defect field (local remainder, registered below)
  and the three wrap holonomies (global remainder, registered
  below) - with `maxwellQuad N theta` (MAX pin, cited) as the
  field's aggregate size.
- **REM-CYCLE** (registration only, NO bricks): a drive acting on
  a state, whose step-factor product around a full circuit fails
  to be 1. This side is **decided already, at two seats, both
  T1**: NO at the clock seat - `z4_clock_defect_factor` and
  `z4_clock_not_invariant` (`ThermalZ4ClockDefect.lean`): under
  the clock turn the ladder's Gibbs weights do not return to
  themselves - and YES at the pump seat - PUMP-2 (the
  `ChargePumpPost.lean` line): the driven cycle returns the state
  exactly, net change zero. A shape with a landed YES seat and a
  landed NO seat is a decided shape; **zero cycle bricks are
  priced or registered here.** Any future cycle remainder at a
  new seat is a new entry on its own scoping.

Jeff's framing of the cycle side, carried VERBATIM as his T5
framing of that side (Jeff, 2026-11-01 01:04 EDT):
**"the driver is the walker"**.

**K-REM-MERGE binds this pin and the whole line:** REM-CONFIG and
REM-CYCLE are never merged into one quantity, one headline, or
one verdict - in this pin or anywhere. They differ in type (a
field of reals on plaquettes, plus three real wrap sums, versus a
factor on weights along a drive), in seat, and in landed state.

## Base-site convention for the wrap holonomies (on the face)

Each wrap holonomy below is registered **at a named base-site
convention**: the coordinate cycle through a chosen base site
`c : LayerSite N`, in a fixed spatial direction `nu`, proceeding
by successive `layerShift nu` steps and returning to `c` after
`N` steps; the holonomy is the sum of `theta` over the `N` links
`layerLinkOf (site at step k) nu` for `k = 0, ..., N - 1`. The
three registered directions are `1`, `2`, `3` (the three spatial
coordinates of `Fin 4`; coordinate `0` is time). Whether the sum
is independent of the base site under flatness is **REM-2's
business and is NOT asserted here**; accordingly `RemClosure`
below quantifies the vanishing over all base sites.

## Kills, pre-registered on the face (memo section 7)

- **K-REM-SMUG.** Any brick, dossier, or prose calling the
  remainder "the Lorentzian bridge," a metric signature, or a
  gravity object fires on sight. **The trigger is named: the
  opposition-minus spent as a signature-minus.** Jeff's "-" (a
  side that opposes, algebra) and a Lorentzian "-" (a direction
  of opposite metric sign, geometry) are different objects; a
  text that lets the remainder inherit the second meaning from
  the first has committed the conflation this line exists to
  refuse. Seat clause: the same kill fires for spending the
  triple-seat flux (the modular flux commutator of
  `ModularTime.lean`) as if it were a base quantity - **the
  triple-seat flux is never a base quantity.**
- **K-GR-LAUNDER.** A remainder value at a finite seat (a
  `plaqAngle` value, a wrap sum, `maxwellQuad` at some `theta`)
  quoted as evidence about any continuum or bulk quantity is
  void on sight. **Finite seat values testify about finite
  seats only.**
- **K-GR-STAB.** A seat where the remainder behaves opposite to
  the seeing's shape is reported **as the finding**, never
  silently restricted away. **Instance in hand: the naive
  closure's death** - `RemNaiveClosure` below is expected FALSE
  on this base (flatness failing to force a gradient is the base
  telling us the remainder has a global part); its theorem-grade
  kill is REM-1's job, and the seat list is not edited to hide
  it.
- **K-REM-MERGE.** Any prose that merges REM-CONFIG and
  REM-CYCLE into one "remainder" - one quantity, one headline,
  one verdict - is a correction at full rank. (Stated again
  here; it is registered in the split paragraph above.)
- **K-REM-FORK.** Re-registering `maxwellM3`, redefining
  `plaqAngle`, or restating M1/M2 under REM names instead of
  citing the MAX pin is a fork of a frozen registration and dies
  on sight. REM consumes the MAX pin's vocabulary by citation
  or not at all.
- **Vacuity guard (the teeth test).** A "remainder" that
  vanishes identically on every configuration by definition, or
  is nonzero identically by definition, is a kill-grade defect
  of the formalization. The registered formalization passes on
  its face: **zero is attained** (`theta = 0`; gradients),
  **nonzero is attained with an exact value** (the
  single-plaquette excitation whose seat value REM-1 decides),
  and **the headline Prop has a false naive form**
  (`RemNaiveClosure`, registered below with its expected death
  on its face).

## What this pin asserts

Nothing. The only theorems below are `rfl`-grade read-backs of
the definitions just registered.
-/

section RemDefectField

/-- **The plaquette-defect field** (memo sections 4-5): the
local remainder of a configuration `theta : linkAngle N`, read
as a named function of `theta`: `P ↦ plaqAngle P theta`.
**Honest form, stated on the face:** this is a plain def equal
to the MAX pin's `plaqAngle` with its arguments read in field
order - a named read of the MAX pin's definition BY CITATION.
It does not redefine `plaqAngle` (K-REM-FORK). -/
def plaqDefectField {N : ℕ} [NeZero N] (θ : linkAngle N) :
    PlaqDatum N → ℝ :=
  fun P => plaqAngle P θ

/-- Read-back: the defect field at `P` is `plaqAngle P theta`,
by definition. -/
theorem plaqDefectField_apply {N : ℕ} [NeZero N]
    (θ : linkAngle N) (P : PlaqDatum N) :
    plaqDefectField θ P = plaqAngle P θ :=
  rfl

/-- Read-back: the zero configuration's defect field is zero
at every plaquette (the teeth test's zero, attained). -/
theorem plaqDefectField_zero {N : ℕ} [NeZero N]
    (P : PlaqDatum N) :
    plaqDefectField (0 : linkAngle N) P = 0 := by
  simp [plaqDefectField, plaqAngle]

end RemDefectField

section RemWrapHolonomies

/-- **The wrap holonomy** (memo sections 4-5) at the named
base-site convention stated on the module face: for a spatial
direction `nu` (with `hnu : nu ≠ 0`) and a base site
`c : LayerSite N`, the sum of `theta` along the coordinate
cycle through `c` in direction `nu` - the `N` links
`layerLinkOf ((layerShift nu hnu)^[k] c) nu`, `k = 0, ..., N - 1`,
where `^[k]` is function iteration, so step `k` is the site
reached from `c` by `k` successive `layerShift nu` steps.
A definition only: no base-site independence is asserted
(that is REM-2's business). -/
def wrapHolonomy {N : ℕ} [NeZero N] (θ : linkAngle N)
    (ν : Fin 4) (hν : ν ≠ 0) (c : LayerSite N) : ℝ :=
  ∑ k ∈ Finset.range N,
    θ (layerLinkOf ((layerShift ν hν)^[k] c) ν hν)

/-- **Wrap holonomy, direction 1** (the first spatial
coordinate): `wrapHolonomy theta 1 _ c` at the module face's
base-site convention. -/
def wrapHolonomy1 {N : ℕ} [NeZero N] (θ : linkAngle N)
    (c : LayerSite N) : ℝ :=
  wrapHolonomy θ 1 (by decide) c

/-- **Wrap holonomy, direction 2** (the second spatial
coordinate): `wrapHolonomy theta 2 _ c` at the module face's
base-site convention. -/
def wrapHolonomy2 {N : ℕ} [NeZero N] (θ : linkAngle N)
    (c : LayerSite N) : ℝ :=
  wrapHolonomy θ 2 (by decide) c

/-- **Wrap holonomy, direction 3** (the third spatial
coordinate): `wrapHolonomy theta 3 _ c` at the module face's
base-site convention. -/
def wrapHolonomy3 {N : ℕ} [NeZero N] (θ : linkAngle N)
    (c : LayerSite N) : ℝ :=
  wrapHolonomy θ 3 (by decide) c

/-- Read-back: the wrap holonomy is the cycle sum of its
definition. -/
theorem wrapHolonomy_apply {N : ℕ} [NeZero N] (θ : linkAngle N)
    (ν : Fin 4) (hν : ν ≠ 0) (c : LayerSite N) :
    wrapHolonomy θ ν hν c
      = ∑ k ∈ Finset.range N,
          θ (layerLinkOf ((layerShift ν hν)^[k] c) ν hν) :=
  rfl

/-- Read-back: direction 1 is the generic wrap holonomy at
`nu = 1`. -/
theorem wrapHolonomy1_apply {N : ℕ} [NeZero N] (θ : linkAngle N)
    (c : LayerSite N) :
    wrapHolonomy1 θ c = wrapHolonomy θ 1 (by decide) c :=
  rfl

/-- Read-back: direction 2 is the generic wrap holonomy at
`nu = 2`. -/
theorem wrapHolonomy2_apply {N : ℕ} [NeZero N] (θ : linkAngle N)
    (c : LayerSite N) :
    wrapHolonomy2 θ c = wrapHolonomy θ 2 (by decide) c :=
  rfl

/-- Read-back: direction 3 is the generic wrap holonomy at
`nu = 3`. -/
theorem wrapHolonomy3_apply {N : ℕ} [NeZero N] (θ : linkAngle N)
    (c : LayerSite N) :
    wrapHolonomy3 θ c = wrapHolonomy θ 3 (by decide) c :=
  rfl

/-- Read-back: the zero configuration's wrap holonomy is zero
in every direction at every base site. -/
theorem wrapHolonomy_zero {N : ℕ} [NeZero N]
    (ν : Fin 4) (hν : ν ≠ 0) (c : LayerSite N) :
    wrapHolonomy (0 : linkAngle N) ν hν c = 0 := by
  simp [wrapHolonomy]

/-- Read-back: direction 1 of the zero configuration vanishes. -/
theorem wrapHolonomy1_zero {N : ℕ} [NeZero N] (c : LayerSite N) :
    wrapHolonomy1 (0 : linkAngle N) c = 0 :=
  wrapHolonomy_zero 1 (by decide) c

/-- Read-back: direction 2 of the zero configuration vanishes. -/
theorem wrapHolonomy2_zero {N : ℕ} [NeZero N] (c : LayerSite N) :
    wrapHolonomy2 (0 : linkAngle N) c = 0 :=
  wrapHolonomy_zero 2 (by decide) c

/-- Read-back: direction 3 of the zero configuration vanishes. -/
theorem wrapHolonomy3_zero {N : ℕ} [NeZero N] (c : LayerSite N) :
    wrapHolonomy3 (0 : linkAngle N) c = 0 :=
  wrapHolonomy_zero 3 (by decide) c

end RemWrapHolonomies

section RemProps

/-- **REM-NAIVE-CLOSURE (registered, expected FALSE).** The
naive closure statement of memo section 3 (i): every flat
configuration is a pure site-potential gradient - for every
`theta : linkAngle N`, if `plaqAngle P theta = 0` at every
`P ∈ allPlaqData N` (the MAX pin's enumeration, cited), then
`theta = gaugeAngle phi` for some site potential `phi`.

**EXPECTED DEATH, ON ITS FACE:** this Prop is expected **FALSE**
on this base. The constant direction field (`theta = 1` on every
link of one fixed spatial direction, `0` elsewhere) is flat at
every plaquette - its per-plaquette sum reads `1 + 0 - 1 - 0` -
yet is not a gradient: its wrap sum in its own direction is
`N ≠ 0` while every gradient's wrap sum telescopes to `0`
(scoping-grade counterexample, memo section 3 (i)). Its
theorem-grade kill is REM-1's job (K-GR-STAB: the death is the
finding, reported at full rank, never repaired by narrowing the
seat). **Registering this Prop is freezing the question, not
asserting it. It is not asserted to hold in this brick.** -/
def RemNaiveClosure (N : ℕ) [NeZero N] : Prop :=
  ∀ θ : linkAngle N,
    (∀ P ∈ allPlaqData N, plaqAngle P θ = 0) →
      ∃ φ : LayerSite N → ℝ, θ = gaugeAngle φ

/-- **REM-CLOSURE (registered, corrected form).** The corrected
closure statement of memo sections 4-5: a configuration is flat
at every plaquette **and** has vanishing wrap holonomy in all
three spatial directions (at every base site, per the
base-site convention on the module face) **iff** it is a pure
site-potential gradient - for every `theta : linkAngle N`,
`((∀ P, plaqAngle P theta = 0) ∧ (∀ c, wrapHolonomy1 theta c = 0
∧ wrapHolonomy2 theta c = 0 ∧ wrapHolonomy3 theta c = 0)) ↔
∃ φ, theta = gaugeAngle φ`. The forward direction is REM-2's
target and is hard-gated on MAX-2 (it consumes the MAX pin's
M3, cited, never re-registered here - K-REM-FORK).
**Not asserted to hold in this brick.** -/
def RemClosure (N : ℕ) [NeZero N] : Prop :=
  ∀ θ : linkAngle N,
    ((∀ P : PlaqDatum N, plaqAngle P θ = 0) ∧
      (∀ c : LayerSite N, wrapHolonomy1 θ c = 0 ∧
        wrapHolonomy2 θ c = 0 ∧ wrapHolonomy3 θ c = 0)) ↔
      ∃ φ : LayerSite N → ℝ, θ = gaugeAngle φ

/-- Read-back: `RemNaiveClosure` unfolds to its registered
statement. -/
theorem remNaiveClosure_iff (N : ℕ) [NeZero N] :
    RemNaiveClosure N ↔
      ∀ θ : linkAngle N,
        (∀ P ∈ allPlaqData N, plaqAngle P θ = 0) →
          ∃ φ : LayerSite N → ℝ, θ = gaugeAngle φ :=
  Iff.rfl

/-- Read-back: `RemClosure` unfolds to its registered
statement. -/
theorem remClosure_iff (N : ℕ) [NeZero N] :
    RemClosure N ↔
      ∀ θ : linkAngle N,
        ((∀ P : PlaqDatum N, plaqAngle P θ = 0) ∧
          (∀ c : LayerSite N, wrapHolonomy1 θ c = 0 ∧
            wrapHolonomy2 θ c = 0 ∧ wrapHolonomy3 θ c = 0)) ↔
          ∃ φ : LayerSite N → ℝ, θ = gaugeAngle φ :=
  Iff.rfl

end RemProps

end ThetLogos
