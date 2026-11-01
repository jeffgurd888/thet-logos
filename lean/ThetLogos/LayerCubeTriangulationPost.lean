import Mathlib.Tactic
import ThetLogos.LayerCubeDistance

namespace ThetLogos

/-!
# ThetLogos.LayerCubeTriangulationPost - TOY-0: the finite
triangulation toy's registration pin

**Working label only.** The module name
`LayerCubeTriangulationPost`, the line name FINITE
TRIANGULATION TOY, and the brick labels TOY-0, TOY-1, TOY-2,
TOY-3 are working labels; Jeff names. Nothing in this module
is a name Jeff has given.

**Status: REGISTRATION ONLY - definitions and statement pins
on the LANDED GR-GEO base (`LayerSite N`, `cubeGraph N`,
`geoDist N` of `LayerCubeDistancePost`, and the GEO-1
theorems `cubeGraph_connected` and `geoDist_l1_formula` of
`LayerCubeDistance`). This pin does not rename or extend the
GEO pins. It proves NOTHING about any seat. NO CLAIM.**

Governing text:
`routeb-general-scratch/scoping-triangulation-toy-2026-11-01.md`
(sections 1-3, 6, 7). The grades and fences below are PINNED
by that text: this pin registers them; it does not re-grade,
soften, or raise any of them.

## Section-0 ceiling (on the face)

A toy is a model. Its verdicts, if the bricks land, are T1
about the toy only - about one finite graph the house owns -
and nothing about the sky, nothing about the gravity shadow,
and nothing about spacetime. Dial 2 = 0 and Dial 3 = 0 under
every outcome, including total success.

The toy triangulates the FINITE half of the posed base of
the corpus's gravity shadow - the half the house owns - and
says nothing about the other half. Per the GR-POSE record
(GR-POSE-1), the posed base is half owned finite geometry
and half a variable: the 4D curvature slot enters as an
abstract variable, and no functional of the finite spectral
data alone carries its response. The toy operates entirely
inside the owned half. It neither supplies nor tests the 4D
half; it does not warm the chair.

The sky enters the toy as input-shape only: the seeing's two
factor shapes (landmarks, as fixed map points; bearing
patterns, as orientation) are instantiated as finite objects
on the owned base. No sky data is an input; no sky claim is
an output.

The pre-registered comparison (section 3 of the governing
memo, registered below as `ToyComparison`) can be decided
NO - the bearing analogue may add nothing on a seat. A NO is
a full-rank deliverable, at the same volume as a YES.

## Section-4 DIST fence (on the face)

The toy's only distance is `geoDist`. `connesDist` may not
appear in the toy as a landmark distance, a channel, or a
comparison term, for both reasons on the record: (i) wrong
space - it lives on states of an algebra, `geoDist` lives on
sites; (ii) the proved discrete value at its seat (GR-DIST-2:
the discrete metric, 0 on the diagonal, 1 elsewhere) carries
one bit per landmark and cannot carry a distance vector. In
this module `connesDist` appears in this fence sentence
only - never in any definition, statement, or proof. Every
distance below is `geoDist` only.

## Section-7 kills (pre-registered, verbatim in effect)

- K-TOY-DREDGE (the numerology fence): exactly ONE
  comparison is registered (below), at exactly the seats
  {2, 3}. Any pattern noticed while running the seats - a
  pretty landmark configuration, a count that matches 42,
  96, 7, or any number with a name in this house - is not a
  finding and ships nowhere. A new pattern requires a NEW
  entry with its own registration before it is computed.
- K-GR-SMUG (instance for this line): the bearing analogue
  described as the 42-degree bow, as "antisolar," or as an
  angle; the toy's resolution described as triangulating
  spacetime, the sky, or the shadow - void on sight,
  correction at full rank. The analogue word rides in every
  statement that mentions the bearing channel.
- K-GR-LAUNDER (instance for this line): toy outputs
  described as correlations - with the sky, with quasars,
  with the rainbow, with the gravity shadow - void on sight.
  The toy decides facts about a finite graph; its connection
  to the seeing is input-shape only, and that sentence is the
  whole connection.
- K-GR-STAB (instance for this line): the channels' texture
  is seat-dependent by design (sign collapse at N = 2, full
  signs at N = 3, tie class live at N = 4). If the comparison
  flips between its registered seats, the flip is the
  finding, reported per seat at full rank. Silently dropping
  or restricting the flipping seat - or re-choosing the seat
  list after seeing an outcome - is void on sight; the seat
  list {2, 3} is frozen in this pin.
- K-TOY-VAC (vacuity watch): if the bearing pattern, as
  implemented, determines the displacement (or the distance)
  after all - the comparison is void by construction and the
  line stops for re-registration; a joint "win" bought by a
  too-strong channel is reported as a kill of the pin, not a
  result. The bearing-coarsening target below is registered
  precisely so this watch has a stated form.

## What is registered here

1. `distVector` - the distance vector of a site against a
   landmark finset, via `geoDist` only.
2. `cubeStepSite` (auxiliary) and `bearingPattern` - the finite
   bearing ANALOGUE, in the governing memo's registered form
   and no other: the set of all shortest first steps, the tie
   class carried in the codomain.
3. `jointRepresentation`, `ResolvesDist`, `ResolvesJoint`.
4. `ToyComparison` - the ONE comparison, as a per-seat
   statement schema; the seat list {2, 3} frozen in
   `toyComparisonSeats` and `ToyComparisonAtRegisteredSeats`.
   The schema is asserted for NO seat in this pin.
5. `BearingCoarseningTarget` - the bearing-coarsening target,
   a pin-grade target Prop; its proof is owed to TOY-1.
6. The seat-texture targets of memo section 2, registered as
   named target Props: `BearingSignCollapseTwoTarget`,
   `BearingUniqueSignThreeTarget`, `BearingTieLiveFourTarget`.
   None is proved here; they are TOY-1 / TOY-2 obligations.

The only proved content is pin-grade read-backs: unfoldings
of the registered definitions.
-/

/-! ## Channel 1: landmark distances (via `geoDist` only) -/

/-- **The distance vector (registered).** For a landmark
finset `S : Finset (LayerSite N)` and a site `x`,
`distVector N S x` is the finset-indexed family
`S -> Nat` sending each landmark `l : S` to
`geoDist N x l.1` - the distance vector `Phi_S(x)` of memo
section 2, via `geoDist` ONLY. -/
noncomputable def distVector (N : ℕ) [NeZero N]
    (S : Finset (LayerSite N)) (x : LayerSite N) : S → ℕ :=
  fun ℓ => geoDist N x ℓ.1

/-- **Read-back.** The distance vector at a landmark is
exactly the `geoDist` to that landmark, unfolded. Pin-grade
only. -/
theorem distVector_apply {N : ℕ} [NeZero N]
    (S : Finset (LayerSite N)) (x : LayerSite N) (ℓ : S) :
    distVector N S x ℓ = geoDist N x ℓ.1 :=
  rfl

/-! ## Channel 2: the bearing analogue (finite analogue) -/

/-- **One step on the layer (registered auxiliary).**
`cubeStepSite N x i s` is the site obtained from `x` by stepping
in coordinate `i` by `+1` if `s = true` and by `-1` if
`s = false` (addition in `ZMod N`). Coordinate `0` is the
fixed time coordinate of the layer: if `i = 0` the step is
registered as the identity (no step is taken), so the result
is always a layer site. Only spatial coordinates carry
bearing directions; the bearing pattern below quantifies
over `i ≠ 0` only. -/
def cubeStepSite (N : ℕ) [NeZero N] (x : LayerSite N)
    (i : Fin 4) (s : Bool) : LayerSite N :=
  if hi : i ≠ 0 then
    ⟨Function.update x.1 i (x.1 i + if s then 1 else -1), by
      rw [Function.update_apply, if_neg (Ne.symm hi)]
      exact x.2⟩
  else x

/-- **The bearing pattern - the finite bearing ANALOGUE
(registered, in the memo's registered form and no other).**
For a site `x` and a landmark `l`, `bearingPattern N x l`
is the set of signed spatial directions `(i, s)` - `i` a
spatial coordinate only (coordinate `0` is the fixed time
coordinate and is excluded by the `i ≠ 0` clause), `s` the
sign, `true` for `+` and `false` for `-` - such that
stepping from `x` by `s` in coordinate `i` strictly
decreases `geoDist N . l`: exactly the set of ALL shortest
first steps from `x` toward `l`. The tie class is carried
in the codomain: when the two wrap arcs of a coordinate are
equal, BOTH signs satisfy the decrease condition and the
pattern, being the set of all such steps, contains both -
this is automatic from the definition as a set of all
shortest first steps, and is stated here on the face. This
is a finite analogue of a bearing: it records directions
only - not distances, not displacements. -/
noncomputable def bearingPattern (N : ℕ) [NeZero N]
    (x ℓ : LayerSite N) : Set (Fin 4 × Bool) :=
  {p : Fin 4 × Bool | p.1 ≠ 0 ∧
    geoDist N (cubeStepSite N x p.1 p.2) ℓ < geoDist N x ℓ}

/-- **Read-back (bearing analogue).** Membership in the
bearing pattern is exactly the registered decrease
condition, unfolded. Pin-grade only. -/
theorem bearingPattern_mem {N : ℕ} [NeZero N]
    (x ℓ : LayerSite N) (i : Fin 4) (s : Bool) :
    (i, s) ∈ bearingPattern N x ℓ ↔ i ≠ 0 ∧
      geoDist N (cubeStepSite N x i s) ℓ < geoDist N x ℓ :=
  Iff.rfl

/-! ## The joint representation and resolution -/

/-- **The joint representation (registered).** The joint
representation of `x` against a landmark finset `S` is the
pair of its distance vector (channel 1) and its family of
bearing patterns against `S` (channel 2, the finite bearing
analogue): `(distVector N S x, fun l : S => bearingPattern
N x l.1)`. -/
noncomputable def jointRepresentation (N : ℕ) [NeZero N]
    (S : Finset (LayerSite N)) (x : LayerSite N) :
    (S → ℕ) × (S → Set (Fin 4 × Bool)) :=
  (distVector N S x, fun ℓ => bearingPattern N x ℓ.1)

/-- **Read-back.** The joint representation is exactly the
registered pair of channels, unfolded. Pin-grade only. -/
theorem jointRepresentation_unfold {N : ℕ} [NeZero N]
    (S : Finset (LayerSite N)) (x : LayerSite N) :
    jointRepresentation N S x
      = (distVector N S x,
          fun ℓ => bearingPattern N x ℓ.1) :=
  rfl

/-- **Distance-only resolution (registered Prop).** `S`
resolves the seat by distances alone iff `distVector N S`
is injective on sites. -/
def ResolvesDist (N : ℕ) [NeZero N]
    (S : Finset (LayerSite N)) : Prop :=
  Function.Injective (distVector N S)

/-- **Read-back.** Distance-only resolution is exactly the
registered injectivity, unfolded. The predicate itself is
not asserted for any landmark set here. -/
theorem resolvesDist_unfold {N : ℕ} [NeZero N]
    (S : Finset (LayerSite N)) :
    ResolvesDist N S ↔ Function.Injective (distVector N S) :=
  Iff.rfl

/-- **Joint resolution (registered Prop).** `S` jointly
resolves the seat iff the joint representation - distance
vector together with the bearing patterns of the finite
bearing analogue against `S` - is injective on sites. -/
def ResolvesJoint (N : ℕ) [NeZero N]
    (S : Finset (LayerSite N)) : Prop :=
  Function.Injective (jointRepresentation N S)

/-- **Read-back.** Joint resolution is exactly the
registered injectivity of the joint representation (distance
vector plus bearing-analogue patterns), unfolded. The
predicate itself is not asserted for any landmark set
here. -/
theorem resolvesJoint_unfold {N : ℕ} [NeZero N]
    (S : Finset (LayerSite N)) :
    ResolvesJoint N S
      ↔ Function.Injective (jointRepresentation N S) :=
  Iff.rfl

/-! ## The ONE comparison (statement schema; asserted for
no seat) -/

/-- **The comparison, per seat (registered statement
schema).** `ToyComparison N` states: there is a jointly
resolving landmark finset `S` of some size `k` such that
EVERY distance-only resolving landmark finset `S'` is
strictly larger than `k` - i.e. the minimum jointly
resolving size is strictly smaller than the minimum
distance-only resolving size, with the minima phrased
without choice, in exactly this existential / universal
form. This is the ONE comparison of memo section 3: does
the bearing-analogue channel buy any landmarks, yes or no.
Registered as a schema only; asserted for NO seat in this
pin. -/
def ToyComparison (N : ℕ) [NeZero N] : Prop :=
  ∃ S : Finset (LayerSite N), ∃ k : ℕ,
    ResolvesJoint N S ∧ S.card = k ∧
      ∀ S' : Finset (LayerSite N),
        ResolvesDist N S' → k < S'.card

/-- **Read-back.** The comparison schema is exactly its
registered statement, unfolded. The schema itself is not
asserted for any seat anywhere in this module. -/
theorem toyComparison_unfold {N : ℕ} [NeZero N] :
    ToyComparison N
      ↔ ∃ S : Finset (LayerSite N), ∃ k : ℕ,
          ResolvesJoint N S ∧ S.card = k ∧
            ∀ S' : Finset (LayerSite N),
              ResolvesDist N S' → k < S'.card :=
  Iff.rfl

/-- **The frozen seat list (registered).** The comparison's
seats are exactly {2, 3}, frozen in this pin (K-GR-STAB
instance for this line: the seat list is not re-chosen after
seeing an outcome). Seat N = 4 carries descriptive counts
only in the optional TOY-3 and is NOT a comparison seat. -/
def toyComparisonSeats : Finset ℕ := {2, 3}

/-- **Read-back.** The frozen seat list is exactly {2, 3},
unfolded. Pin-grade only. -/
theorem toyComparisonSeats_unfold :
    toyComparisonSeats = {2, 3} :=
  rfl

/-- **The comparison at its registered seats (registered
Prop).** The conjunction of the comparison schema at
exactly its frozen seats, N = 2 and N = 3. Registered only;
asserted for no seat in this pin - this definition states
what TOY-1 and TOY-2 owe, per seat, and decides nothing. -/
def ToyComparisonAtRegisteredSeats : Prop :=
  ToyComparison 2 ∧ ToyComparison 3

/-- **Read-back.** The registered-seats comparison is
exactly the conjunction at seats 2 and 3, unfolded. It is
not asserted anywhere in this module. -/
theorem toyComparisonAtRegisteredSeats_unfold :
    ToyComparisonAtRegisteredSeats
      ↔ ToyComparison 2 ∧ ToyComparison 3 :=
  Iff.rfl

/-! ## The bearing-coarsening target (pin-grade target;
proof owed to TOY-1) -/

/-- **The bearing-coarsening target (registered target
Prop; proof owed to TOY-1).** The bearing pattern - the
finite bearing analogue - determines NEITHER the distance
nor the displacement: (a) there exist sites `x y` and a
landmark `l` with equal bearing-analogue patterns toward
`l` and different distances `geoDist N x l ≠ geoDist N y l`;
and (b) there exist sites `x y` and a landmark `l` with
equal bearing-analogue patterns toward `l` and different
displacements, the displacement of a site from `l` being
registered here as the coordinatewise difference function
`fun i => x.1 i - l.1 i` in `ZMod N`. Registered only; not
proved in this pin. This target is the stated form of the
K-TOY-VAC watch: if it fails, the comparison is void by
construction and the line stops for re-registration. -/
def BearingCoarseningTarget (N : ℕ) [NeZero N] : Prop :=
  (∃ x y ℓ : LayerSite N,
    bearingPattern N x ℓ = bearingPattern N y ℓ ∧
      geoDist N x ℓ ≠ geoDist N y ℓ) ∧
  (∃ x y ℓ : LayerSite N,
    bearingPattern N x ℓ = bearingPattern N y ℓ ∧
      (fun i => x.1 i - ℓ.1 i) ≠ (fun i => y.1 i - ℓ.1 i))

/-- **Read-back (bearing analogue).** The coarsening target
is exactly its registered statement, unfolded, both clauses
included. The target itself is not asserted anywhere in
this module. -/
theorem bearingCoarseningTarget_unfold {N : ℕ} [NeZero N] :
    BearingCoarseningTarget N
      ↔ (∃ x y ℓ : LayerSite N,
          bearingPattern N x ℓ = bearingPattern N y ℓ ∧
            geoDist N x ℓ ≠ geoDist N y ℓ) ∧
        (∃ x y ℓ : LayerSite N,
          bearingPattern N x ℓ = bearingPattern N y ℓ ∧
            (fun i => x.1 i - ℓ.1 i)
              ≠ (fun i => y.1 i - ℓ.1 i)) :=
  Iff.rfl

/-! ## Seat-texture targets (registered; TOY-1 / TOY-2
obligations; none proved here) -/

/-- **Seat texture at N = 2 - sign collapse (registered
target Prop; obligation of TOY-1).** At seat N = 2 the
bearing analogue carries only the differ-pattern: the
pattern is sign-symmetric - whenever a signed spatial
direction `(i, s)` lies in the bearing pattern (the finite
bearing analogue) of `x` toward `l`, the opposite sign
`(i, !s)` lies in it too. Registered only; not proved
here. -/
def BearingSignCollapseTwoTarget : Prop :=
  ∀ x ℓ : LayerSite 2, ∀ i : Fin 4, ∀ s : Bool,
    (i, s) ∈ bearingPattern 2 x ℓ → (i, !s) ∈ bearingPattern 2 x ℓ

/-- **Seat texture at N = 3 - full signs (registered target
Prop; obligation of TOY-2).** At seat N = 3 the bearing
analogue has full signs: no coordinate of any bearing
pattern (the finite bearing analogue) carries both signs at
once - for every `x l i`, `(i, true)` and `(i, false)` are
not both in the pattern. Registered only; not proved
here. -/
def BearingUniqueSignThreeTarget : Prop :=
  ∀ x ℓ : LayerSite 3, ∀ i : Fin 4,
    ¬ ((i, true) ∈ bearingPattern 3 x ℓ ∧
        (i, false) ∈ bearingPattern 3 x ℓ)

/-- **Seat texture at N = 4 - the tie class is live
(registered target Prop; obligation of TOY-2's optional
extension).** At seat N = 4 there exist a site `x`, a
landmark `l`, and a spatial coordinate `i` such that BOTH
signs lie in the bearing pattern (the finite bearing
analogue) of `x` toward `l` - a coordinate whose two wrap
arcs are equal. Registered only; not proved here. Seat
N = 4 is not a comparison seat (the seat list {2, 3} is
frozen above); this target registers texture only. -/
def BearingTieLiveFourTarget : Prop :=
  ∃ x ℓ : LayerSite 4, ∃ i : Fin 4,
    (i, true) ∈ bearingPattern 4 x ℓ ∧
      (i, false) ∈ bearingPattern 4 x ℓ

end ThetLogos
