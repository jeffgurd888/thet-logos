import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import ThetLogos.MaxwellQuadPost

namespace ThetLogos

/-!
# ThetLogos.LayerCubeDistancePost - GR-GEO-0: the cube-distance registration pin

**Working label only.** The module name `LayerCubeDistancePost`
and the line name GR-GEO are working labels; Jeff names.
Nothing in this module is a name Jeff has given.

**Status: REGISTRATION ONLY - the cube graph, the distance as
a citation-definition, two target Props for GR-GEO-1, and the
`PoseObjF` shadow predicate registered verbatim with its
comparison. NO CLAIM. No gravity object is defined,
constructed, or asserted to exist. Dial 2 = 0 under every
outcome of this line, including total success. This pin seats
NO object; it registers words and seat decisions only.**

Governing text: `routeb-general-scratch/scoping-gravity-vocabulary-2026-10-31.md`
(sections 1-3 and 8). The grades and fences below are PINNED
by that text: this pin registers them; it does not re-grade,
soften, or raise any of them.

## Section-0 fence of the vocabulary program (on the face)

This program builds words and decides shadow predicates at
named seats - it seats NO gravity object; Dial 2 = 0 under
EVERY outcome. The strongest landing this line could ever
produce is statability: a finite shadow predicate becomes
writable and, at named seats, decidable. Nothing beyond that
paragraph is bought here.

## Finite names only (on the face)

`geoDist` is a combinatorial graph distance on the owned
layer cube: a finite object carrying a finite name.
Continuum nouns remain FRONTIER and unspendable in this
line, and appear in this module only inside this fence
sentence: geodesic-as-spacetime-object, metric tensor,
curvature-as-computed, stress-energy, Einstein equation,
null cone, ray optics. Any use of one of those words for an
object defined, registered, or proved here is dressing a
finite object in continuum clothes and is struck on sight.

## The DIST-not-GEO fence, from this side (on the face)

`geoDist` lives on SITES of the layer cube. `connesDist`
(GR-DIST) lives on STATES of an algebra. The two sub-lines
may not cite each other as evidence, and neither distance is
the other's road: the state-space distance is not a spatial
separation and may never be spent as the `r` of a falloff
statement, and this graph distance says nothing about states.

## K-GR-SMUG instance (iv), on the face

The l1 formula - `geoDist N x y` equals the sum over the
coordinates of the cyclic coordinate distances - is a
THEOREM TO BE (GR-GEO-1, registered below as
`GeoDistL1Formula`), never the definition. A "distance"
defined by importing the formula's answer does not land:
`geoDist` below is defined ONLY as Mathlib's
`SimpleGraph.dist` on the registered cube graph, and its
metric content must come from Mathlib's graph-distance
theory plus the connectedness theorem of GR-GEO-1, not from
the definition.

## Pre-registered kills, named on the face

- K-GR-VAC: a distance whose metric properties hold by
  definition alone is struck at full rank, not weakened;
  likewise a shadow predicate registered in a form every
  operator satisfies (no named function, no named comparison
  value) is struck. The comparison registered below names
  its function, its constant, and its profile for exactly
  this reason.
- K-GR-SMUG: with instance (iv) named above. The DIST and
  GEO objects live on different spaces; spending either as
  the other fires on sight.
- K-GR-LAUNDER: any text describing a landed item of this
  program as progress toward an object (as opposed to toward
  statability), or in the laundered phrases the governing
  memo names, is a correction at full rank, same volume.
  This program's output vocabulary is: statable, decided at
  the seat, killed at the seat. No other verbs ship.
- K-GR-STAB: with instance (iii) named: the l1 formula
  failing at `N = 2` boundary cases (coordinate wrap
  degeneracies) would be a FINDING, reported with the seat
  named, not a repair; the seat list is not edited to hide
  a flip.
- K-GR-BUY: the vocabulary program's section-0 paragraph is
  the whole buy, forever. This program makes the chair
  addressable; it does not warm it.

## What is registered here

1. `cubeGraph N` - the cube graph on `LayerSite N`, from the
   landed link head/tail data (`linkTail`, `linkHead` of
   `MaxwellQuadPost`, over `LayerLink N` from
   `PlaneCrossingCube`). Encoding, stated on the face: two
   sites are adjacent iff they are distinct AND some link
   has them as its tail and head, in either order. Symmetry
   and looplessness hold by the encoding's form (the
   distinctness clause is what makes looplessness hold at
   every seat, including degenerate small ones).
2. `geoDist N x y : Nat` - Mathlib's `SimpleGraph.dist` on
   that graph. A CITATION-definition (see the K-GR-SMUG
   instance (iv) fence above).
3. The two registered targets of GR-GEO-1:
   `CubeGraphConnected` (without it the distance is
   infinity-valued junk in the extended sense and the
   formula target does not land) and `GeoDistL1Formula`,
   stated against the registered coordinate distance
   `cycDist`.
4. `PoseObjFShadow` - the `PoseObjF` SHADOW PREDICATE,
   registered verbatim in the section below, with its
   ceiling and its prior on its face.

The only proved content is pin-grade read-backs: unfoldings
of the registered definitions and one adjacency
construction. Neither target Prop is asserted anywhere in
this module, and the shadow predicate is not asserted for
any function, constant, or seat here.
-/

/-! ## The cube graph, from the landed head/tail data -/

/-- **The cube graph on `LayerSite N` (registered).**
Adjacency is read off the landed link data of
`MaxwellQuadPost`: sites `x` and `y` are adjacent iff
`x ≠ y` and some link `ℓ : LayerLink N` has them as tail
and head, in either order (`linkTail ℓ = x` and
`linkHead ℓ = y`, or the reverse). The disjunction makes
the relation symmetric by form; the distinctness clause
makes it loopless by form. This graph is the whole spatial
seat of this line: a finite graph on a finite site type. -/
def cubeGraph (N : ℕ) [NeZero N] : SimpleGraph (LayerSite N) where
  Adj x y := x ≠ y ∧ ∃ ℓ : LayerLink N,
    (linkTail ℓ = x ∧ linkHead ℓ = y) ∨
      (linkTail ℓ = y ∧ linkHead ℓ = x)
  symm := ⟨fun x y h => by
    obtain ⟨hne, ℓ, hℓ | hℓ⟩ := h
    · exact ⟨hne.symm, ℓ, Or.inr hℓ⟩
    · exact ⟨hne.symm, ℓ, Or.inl hℓ⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-- **Read-back.** Adjacency in `cubeGraph N` is exactly its
registered encoding, unfolded. Pin-grade only. -/
theorem cubeGraph_adj {N : ℕ} [NeZero N] (x y : LayerSite N) :
    (cubeGraph N).Adj x y ↔ x ≠ y ∧ ∃ ℓ : LayerLink N,
      (linkTail ℓ = x ∧ linkHead ℓ = y) ∨
        (linkTail ℓ = y ∧ linkHead ℓ = x) :=
  Iff.rfl

/-- **Pin-grade adjacency construction.** A link whose tail
and head are distinct sites makes its tail and head
adjacent in `cubeGraph N`, by the registered encoding.
Nothing about paths, reachability, or values is asserted. -/
theorem cubeGraph_adj_of_link {N : ℕ} [NeZero N]
    (ℓ : LayerLink N) (h : linkTail ℓ ≠ linkHead ℓ) :
    (cubeGraph N).Adj (linkTail ℓ) (linkHead ℓ) :=
  ⟨h, ℓ, Or.inl ⟨rfl, rfl⟩⟩

/-! ## The distance: a citation-definition -/

/-- **`geoDist N x y : Nat` (registered CITATION-definition).**
`geoDist` IS Mathlib's `SimpleGraph.dist` on `cubeGraph N`,
cited, not re-derived: `geoDist N x y := (cubeGraph N).dist x y`.
Per the K-GR-SMUG instance (iv) fence on this module's face,
the l1 formula is NOT this definition; it is the registered
target `GeoDistL1Formula` below, a theorem-to-be of
GR-GEO-1. Note on the citation's own terms, stated for
honesty: Mathlib's `dist` returns `0` for unreachable pairs,
so until `CubeGraphConnected` is proved the value at an
unreached pair carries no separation content at all - one
more reason connectedness is GR-GEO-1's first target. -/
noncomputable def geoDist (N : ℕ) [NeZero N]
    (x y : LayerSite N) : ℕ :=
  (cubeGraph N).dist x y

/-- **Read-back.** `geoDist` is exactly the cited Mathlib
distance on the registered graph, unfolded. Pin-grade
only: this exhibits the citation; it asserts no value. -/
theorem geoDist_unfold {N : ℕ} [NeZero N] (x y : LayerSite N) :
    geoDist N x y = (cubeGraph N).dist x y :=
  rfl

/-! ## The registered targets of GR-GEO-1 -/

/-- **The cyclic distance on one coordinate (registered
auxiliary).** For `a b : ZMod N`, `cycDist N a b` is the
smaller of the two wrap readings, `min (a - b).val (b - a).val`:
the distance around the cycle in the shorter direction.
This is a one-coordinate combinatorial quantity, registered
so the l1 target below can be stated exactly; it is not
`geoDist` and asserts nothing about the graph. -/
def cycDist (N : ℕ) [NeZero N] (a b : ZMod N) : ℕ :=
  min (a - b).val (b - a).val

/-- **Pin-grade read-back.** The cyclic coordinate distance
from a point to itself is `0`, by the registered definition. -/
theorem cycDist_self {N : ℕ} [NeZero N] (a : ZMod N) :
    cycDist N a a = 0 := by
  simp [cycDist]

/-- **GR-GEO-1 target 1 - connectedness (registered Prop).**
The cube graph is connected, in Mathlib's sense:
`(cubeGraph N).Connected`. Without it the distance is
junk at unreached pairs (see the honesty note at `geoDist`)
and GR-GEO-1 does not land. Registered only; not asserted
in this pin. -/
def CubeGraphConnected (N : ℕ) [NeZero N] : Prop :=
  (cubeGraph N).Connected

/-- **Read-back.** The connectedness target is exactly its
registered statement, unfolded. The target itself is not
asserted anywhere here. -/
theorem cubeGraphConnected_unfold {N : ℕ} [NeZero N] :
    CubeGraphConnected N ↔ (cubeGraph N).Connected :=
  Iff.rfl

/-- **GR-GEO-1 target 2 - the l1 value formula (registered
Prop).** For all sites `x y : LayerSite N`,
`geoDist N x y = Finset.sum Finset.univ (fun i : Fin 4 =>
cycDist N (x.1 i) (y.1 i))` - the graph distance is the sum
over the four coordinates of the cyclic coordinate
distances (the time coordinate contributes `0`, since
every layer site has time coordinate `0`). This formula is
a THEOREM TO BE, registered here as a target: it is not
the definition of `geoDist` (K-GR-SMUG instance (iv)), and
it is not asserted in this pin. K-GR-STAB instance (iii),
on the face: if this formula fails at `N = 2` wrap cases,
that failure is a finding reported at full rank, not a
repair of this registration. -/
def GeoDistL1Formula (N : ℕ) [NeZero N] : Prop :=
  ∀ x y : LayerSite N, geoDist N x y
    = ∑ i : Fin 4, cycDist N (x.1 i) (y.1 i)

/-- **Read-back.** The l1 target is exactly its registered
statement, unfolded. The target itself is not asserted
anywhere here. -/
theorem geoDistL1Formula_unfold {N : ℕ} [NeZero N] :
    GeoDistL1Formula N
      ↔ ∀ x y : LayerSite N, geoDist N x y
          = ∑ i : Fin 4, cycDist N (x.1 i) (y.1 i) :=
  Iff.rfl

/-! ## The PoseObjF shadow predicate, registered verbatim

REGISTRATION CHOICE, on the face: the predicate quantifies
over LINK pairs, not site pairs - the intended two-point
function (the Green kernel of GR-GEO-2, below) lives on
links. The separation of a link pair is registered as
`linkGeoDist`: the `geoDist` between the two links' TAILS.
That is this registration's choice of link separation,
stated here so no later brick can quietly re-choose it.

THE REGISTERED COMPARISON, verbatim: for a named two-point
function `K : LayerLink N -> LayerLink N -> Real` and a
named constant `C : Real` supplied WITH the candidate (a
parameter of the predicate, never existentially quantified
inside it - an existentially quantified constant over a
finite pair set is satisfiable by every kernel and would
be K-GR-VAC, struck), the predicate is: `0 ≤ C`, and for
every pair of links `ℓ ℓ'` with `1 ≤ linkGeoDist N ℓ ℓ'`,
`|K ℓ ℓ'| ≤ C / (linkGeoDist N ℓ ℓ')^2` - the value at
distance-`r` pairs is bounded by the stated constant times
the `1/r^2` profile, at every distance `r ≥ 1` the seat
carries.

CEILING, on the predicate's face: FINITE SHADOW ONLY. This
predicate is statable, NOT true: nothing in this pin or
line asserts it of any function at any seat. Its
registered PRIOR is DEATH BY FINITE SIZE AT ITS SEAT: a
finite torus's two-point function does not follow a `1/r^2`
law, and the first candidate brick asserting this predicate
of a named kernel at a named seat is EXPECTED to be its
kill. That expected death is a legitimate landing: it
converts `PoseObjF` from unstatable to stated-and-killed at
the finite shadow, and it seats nothing either way.

INTENDED INSTANTIATION, named on the face: `K` is intended
to be the Green kernel `greenKernel m` of GR-GEO-2 (for its
named `m > 0`; gated on MAX-2 and on GR-GEO-1), at the
smallest cube seats - `N = 2` first, the seat where
K-GR-STAB instance (iii) wrap degeneracies would show.
`greenKernel` is not defined in this pin and nothing here
asserts the predicate of it.
-/

/-- **The separation of a link pair (registered).** The
distance between links `ℓ` and `ℓ'` is the `geoDist`
between their tails: `linkGeoDist N ℓ ℓ' := geoDist N
(linkTail ℓ) (linkTail ℓ')`. This is the separation the
shadow predicate below is stated in. -/
noncomputable def linkGeoDist (N : ℕ) [NeZero N]
    (ℓ ℓ' : LayerLink N) : ℕ :=
  geoDist N (linkTail ℓ) (linkTail ℓ')

/-- **Read-back.** `linkGeoDist` is exactly its registered
definition, unfolded. Pin-grade only. -/
theorem linkGeoDist_unfold {N : ℕ} [NeZero N]
    (ℓ ℓ' : LayerLink N) :
    linkGeoDist N ℓ ℓ' = geoDist N (linkTail ℓ) (linkTail ℓ') :=
  rfl

/-- **The `PoseObjF` SHADOW PREDICATE (registered verbatim).**
At seat size `N`, for a named two-point function
`K : LayerLink N -> LayerLink N -> Real` on link pairs and
a named constant `C : Real` supplied as a parameter of the
predicate: `0 ≤ C`, and every link pair at
`linkGeoDist`-distance `r ≥ 1` satisfies the finite falloff
comparison `|K ℓ ℓ'| ≤ C / (linkGeoDist N ℓ ℓ')^2`.
Finite shadow form only; statable, not true; the
registered prior is death by finite size at its seat (see
the section text above, which is part of this
registration). Registered only; not asserted for any `K`,
any `C`, or any seat in this pin. -/
def PoseObjFShadow (N : ℕ) [NeZero N]
    (K : LayerLink N → LayerLink N → ℝ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ ℓ ℓ' : LayerLink N, 1 ≤ linkGeoDist N ℓ ℓ' →
    |K ℓ ℓ'| ≤ C / (linkGeoDist N ℓ ℓ' : ℝ) ^ 2

/-- **Read-back.** The shadow predicate is exactly its
registered statement, unfolded, comparison and constant
condition included. The predicate itself is not asserted
for any function, constant, or seat anywhere in this
module. -/
theorem poseObjFShadow_unfold {N : ℕ} [NeZero N]
    (K : LayerLink N → LayerLink N → ℝ) (C : ℝ) :
    PoseObjFShadow N K C
      ↔ 0 ≤ C ∧ ∀ ℓ ℓ' : LayerLink N,
          1 ≤ linkGeoDist N ℓ ℓ' →
            |K ℓ ℓ'| ≤ C / (linkGeoDist N ℓ ℓ' : ℝ) ^ 2 :=
  Iff.rfl

end ThetLogos
