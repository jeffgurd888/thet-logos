import Mathlib.Tactic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import ThetLogos.ChargePumpPost

open scoped Matrix.Norms.L2Operator ENNReal

namespace ThetLogos

/-!
# ThetLogos.ConnesDistancePost - GR-DIST-0: the Connes-distance registration pin

**Working label only.** The module name `ConnesDistancePost` and
the line name GR-DIST are working labels; Jeff names. Nothing in
this module is a name Jeff has given.

**Status: REGISTRATION ONLY - seat data, one definition, the
five-row axiom table registered as Props at their exact grades,
and the sector-separation predicate registered for a named seat
and a named sector pair. NO CLAIM. No gravity object is defined,
constructed, or asserted to exist. Dial 2 = 0 under every outcome
of this line, including total success.**

Governing texts: `routeb-general-scratch/scoping-gravity-vocabulary-2026-10-31.md`
(sections 1-3 and 8) **as corrected by**
`routeb-general-scratch/scoping-gravity-vocabulary-ANNEX-connes-python-2026-10-31.md`.
Where the two differ, the annex governs. The grades below are
PINNED by those texts: this pin registers them; it does not
re-grade, soften, or raise any of them.

## The annex correction, verbatim-grade (on the face)

This pin begins the corpus's first **Lean (T1)** Connes distance -
NOT its first Connes distance. A T4 Python implementation exists
and runs: `thet-logos/python/thet_logos/engine13_rsd.py`,
`connes_distance` (Engine 13), and it is the engine under the
macroscope's distance instrument. DIST-2's BRIDGE-1 cross-check
against that implementation is formula/obstruction-grade (the
seats differ; no same-seat numeric equality is promised).

## Section-0 fence of the vocabulary program (on the face)

This program builds words and decides shadow predicates at named
seats - it seats NO gravity object; Dial 2 = 0 under EVERY
outcome. Continuum vocabulary remains FRONTIER and unspendable in
this line; the only object registered here is a distance on the
point states of a finite commutative algebra seat, a finite
combinatorial object carrying a finite name.

## The DIST-not-GEO fence (K-GR-SMUG instance (i), on the face)

`connesDist` is a distance between STATES of an algebra (here:
point evaluations of a diagonal algebra). It is not a spatial
separation and may never be spent as the `r` of a field law. This
pin does NOT make `PoseObjF` statable - that is GR-GEO's job, in
finite shadow form - and the DIST and GEO sub-lines may not cite
each other as evidence. One yield of this line, stated as the
governing memo states it: GR-POSE-0's fence at
`GravityPosePost.lean:213/:225` - whose ruling stands - acquires a
real T1 referent in the object registered here.

## Seat restriction, stated on the face (not smuggled generality)

The seats of this pin are COMMUTATIVE seats only: a finite index
type, a self-adjoint matrix `D` on it, the commutative algebra of
diagonal matrices, and pure states as point evaluations. No
noncommutative-algebra state space, and no general state
machinery, is registered or implied.

## Pre-registered kills, named on the face

- K-GR-VAC: a registered row whose content holds by definition
  alone, or a conditional row upgraded to unconditional without
  its seat hypothesis on its face, is struck at full rank.
- K-GR-SMUG: `connesDist` spent as a spatial separation anywhere -
  in a falloff statement, a dossier, or a brick name - fires on
  sight; the DIST and GEO objects live on different spaces.
- K-GR-LAUNDER: any text describing a landed item of this program
  as progress toward an object (as opposed to toward statability),
  or in the laundered phrases the governing memo names, is a
  correction at full rank, same volume.
- K-GR-STAB: definiteness or finiteness of `connesDist` flipping
  at a boundary seat is reported as the finding with the seat
  named, never repaired by silently restricting the seat list.
  The two conditional rows below carry their conditions on their
  faces for exactly this reason.
- K-GR-BUY: the vocabulary program's section-0 paragraph is the
  whole buy, forever. This program makes the chair addressable;
  it does not warm it.
- K-DIST-DEG (line-specific): a degenerate seat - the distance
  identically infinite on distinct states, or identically `0` on
  distinct states - SOLD as a metric result is the kill. As a
  finding, a degenerate seat is legitimate: it decides the
  separation predicate negatively at that seat.

## What is registered here

1. `ConnesDistanceSeat` - the seat data (finite index type,
   self-adjoint `D`), with `diagAlg` the diagonal algebra element
   and `pointEval` the point-evaluation pure state.
2. `commDiag` - the commutator of `D` with a diagonal algebra
   element, and `connesDist` - the Connes distance, valued in
   `ENNReal` so the definition is total before any finiteness is
   proved (honesty by type).
3. The five-row axiom table, as registered target Props at their
   exact grades: `ConnesDistDiagZero`, `ConnesDistSymm`,
   `ConnesDistTriangle` (GENERAL - targets of GR-DIST-1);
   `ConnesDistDefiniteConditional` and
   `ConnesDistFiniteConditional` (CONDITIONAL - each registered
   as a conditional shape with its condition named:
   `ConnesCommSeparates` for definiteness, `HasCommutantObstruction`
   and its absence for finiteness).
4. `DistSeparates` - the sector-separation predicate, registered
   for the named Fin 4 cycle seat and the corpus's named sector
   pair at that seat (see its registration for the pair decision).

The only proved content is pin-grade read-backs: unfoldings of
the registered definitions and one diagonal evaluation. No row
of the table is asserted to hold anywhere in this module.
-/

/-! ## Seat data: a commutative seat, stated as a restriction -/

/-- **The seat data of this pin.** A finite index type `iota`
(carried by the ambient `Fintype` instance), a matrix
`D : Matrix iota iota Complex` over it, and the labeled field
`D_selfAdjoint` recording that `D` is self-adjoint. This is the
whole seat: the algebra at the seat is the commutative algebra
of diagonal matrices (see `diagAlg`), and the pure states are
point evaluations (see `pointEval`). Commutative seats only -
the restriction is part of the registration, not a caveat
beneath it. -/
structure ConnesDistanceSeat (iota : Type*) [Fintype iota]
    [DecidableEq iota] where
  /-- The seat operator. -/
  D : Matrix iota iota ℂ
  /-- Labeled field: the seat operator is self-adjoint. -/
  D_selfAdjoint : IsSelfAdjoint D

/-- **The diagonal algebra at a seat.** The algebra element
named by `a : iota -> Complex` is the diagonal matrix
`Matrix.diagonal a`. These diagonal matrices are the seat's
commutative algebra `A_iota`; every algebra element quantified
over in this pin is of this form. -/
def diagAlg {iota : Type*} [DecidableEq iota] (a : iota -> ℂ) :
    Matrix iota iota ℂ :=
  Matrix.diagonal a

/-- **The pure state at a seat point.** The point evaluation at
`i`: the algebra element named by `a` is evaluated as `a i`.
Pure states in this pin are exactly these point evaluations -
no other state is registered. -/
def pointEval {iota : Type*} (i : iota) (a : iota -> ℂ) : ℂ :=
  a i

/-- **Pin-grade read-back.** The point evaluation is the diagonal
entry of the diagonal algebra element: `pointEval i a` is
`(diagAlg a) i i`, by the diagonal evaluation lemma. Nothing
beyond the registered definitions is asserted. -/
theorem pointEval_diagAlg {iota : Type*} [DecidableEq iota]
    (a : iota -> ℂ) (i : iota) :
    pointEval i a = diagAlg a i i :=
  (Matrix.diagonal_apply_eq a i).symm

/-! ## The commutator and the distance -/

/-- **The commutator of the seat operator with an algebra
element**: `[D, diag a] = D * diagAlg a - diagAlg a * D`. The
norm in the bound below is the operator norm on matrices (the
`Matrix.Norms.L2Operator` scoped instance opened at the head of
this module) - the norm of the governing formula, named here so
the choice is on the face and not left to elaboration. -/
def commDiag {iota : Type*} [Fintype iota] [DecidableEq iota]
    (D : Matrix iota iota ℂ) (a : iota -> ℂ) :
    Matrix iota iota ℂ :=
  D * diagAlg a - diagAlg a * D

/-- **Pin-grade read-back.** The commutator with the zero algebra
element is zero: the zero element commutes with every `D`, and
its bound is met trivially. Exhibited so the supremum below is
seen to range over a nonempty bound class. -/
theorem commDiag_zero {iota : Type*} [Fintype iota]
    [DecidableEq iota] (D : Matrix iota iota ℂ) :
    commDiag D 0 = 0 := by
  simp [commDiag, diagAlg]

/-- **The Connes distance at a seat (registered definition).**
For seat operator `D` and seat points `i, j`, `connesDist D i j`
is the supremum, over algebra elements `a : iota -> Complex`
whose commutator with `D` has operator norm at most `1`, of the
modulus `|a i - a j|` of the point evaluations - read into
`ENNReal` by `ENNReal.ofReal`, so the value may be infinite and
the definition is total before any finiteness is proved or even
stated (honesty by type, per the governing memo section 2). -/
noncomputable def connesDist {iota : Type*} [Fintype iota]
    [DecidableEq iota] (D : Matrix iota iota ℂ) (i j : iota) :
    ℝ≥0∞ :=
  ⨆ a : iota -> ℂ, ⨆ _ : ‖commDiag D a‖ ≤ 1,
    ENNReal.ofReal ‖a i - a j‖

/-- **Read-back.** `connesDist` is exactly its registered
definition, unfolded. Pin-grade only: this exhibits the formula
the later bricks build against; it asserts no value. -/
theorem connesDist_unfold {iota : Type*} [Fintype iota]
    [DecidableEq iota] (D : Matrix iota iota ℂ) (i j : iota) :
    connesDist D i j
      = ⨆ a : iota -> ℂ, ⨆ _ : ‖commDiag D a‖ ≤ 1,
          ENNReal.ofReal ‖a i - a j‖ :=
  rfl

/-! ## The five-row axiom table, at its exact grades

Rows one to three are GENERAL: registered as target Props for
GR-DIST-1, asserted nowhere here. Rows four and five are
CONDITIONAL: each is registered as a conditional statement shape
whose hypothesis is the named condition on its face. Upgrading
either conditional row to an unconditional statement without the
seat hypothesis on its face is K-GR-VAC / K-GR-STAB territory.
-/

/-- **Row 1 - `d(i, i) = 0`. Grade: GENERAL (target Prop for
GR-DIST-1).** Every term of the supremum vanishes at `i = j`.
Registered only; not asserted in this pin. -/
def ConnesDistDiagZero {iota : Type*} [Fintype iota]
    [DecidableEq iota] (D : Matrix iota iota ℂ) : Prop :=
  ∀ i : iota, connesDist D i i = 0

/-- **Row 2 - symmetry. Grade: GENERAL (target Prop for
GR-DIST-1).** `d(i, j) = d(j, i)`, term-wise by symmetry of the
modulus. Registered only; not asserted in this pin. -/
def ConnesDistSymm {iota : Type*} [Fintype iota]
    [DecidableEq iota] (D : Matrix iota iota ℂ) : Prop :=
  ∀ i j : iota, connesDist D i j = connesDist D j i

/-- **Row 3 - the triangle inequality, in the extended sense.
Grade: GENERAL (target Prop for GR-DIST-1).**
`d(i, k) <= d(i, j) + d(j, k)` in `ENNReal`, by the pointwise
triangle inequality and subadditivity of the supremum.
Registered only; not asserted in this pin. -/
def ConnesDistTriangle {iota : Type*} [Fintype iota]
    [DecidableEq iota] (D : Matrix iota iota ℂ) : Prop :=
  ∀ i j k : iota,
    connesDist D i k ≤ connesDist D i j + connesDist D j k

/-- **Read-back.** Row 1 is exactly its registered statement,
unfolded. This is the definition read back, not a proof of the
row - `ConnesDistDiagZero` is not asserted anywhere here. -/
theorem connesDistDiagZero_unfold {iota : Type*} [Fintype iota]
    [DecidableEq iota] (D : Matrix iota iota ℂ) :
    ConnesDistDiagZero D ↔ ∀ i : iota, connesDist D i i = 0 :=
  Iff.rfl

/-- **Read-back.** Row 2 is exactly its registered statement,
unfolded. The row itself is not asserted anywhere here. -/
theorem connesDistSymm_unfold {iota : Type*} [Fintype iota]
    [DecidableEq iota] (D : Matrix iota iota ℂ) :
    ConnesDistSymm D
      ↔ ∀ i j : iota, connesDist D i j = connesDist D j i :=
  Iff.rfl

/-- **Read-back.** Row 3 is exactly its registered statement,
unfolded. The row itself is not asserted anywhere here. -/
theorem connesDistTriangle_unfold {iota : Type*} [Fintype iota]
    [DecidableEq iota] (D : Matrix iota iota ℂ) :
    ConnesDistTriangle D
      ↔ ∀ i j k : iota,
          connesDist D i k ≤ connesDist D i j + connesDist D j k :=
  Iff.rfl

/-- **The separating condition for row 4, named.** `D`'s
commutators separate every pair of distinct seat points: for
`i ≠ j` some algebra element `a` meets the commutator bound
`‖[D, diag a]‖ ≤ 1` and its point evaluations at `i` and `j`
differ. Definiteness fails exactly where this fails - where
`D`'s commutators cannot separate `i` from `j`. -/
def ConnesCommSeparates {iota : Type*} [Fintype iota]
    [DecidableEq iota] (D : Matrix iota iota ℂ) : Prop :=
  ∀ i j : iota, i ≠ j →
    ∃ a : iota -> ℂ, ‖commDiag D a‖ ≤ 1 ∧ a i ≠ a j

/-- **Row 4 - definiteness. Grade: CONDITIONAL, registered as a
conditional shape with its condition named.** Under the
hypothesis `ConnesCommSeparates D` - `D`'s commutators separate
every distinct pair - the distance is definite:
`connesDist D i j = 0 -> i = j`. The unconditional form is NOT
registered and may not be quoted as registered: definiteness is
a seat theorem (target of GR-DIST-2 at its seat), not a
definitional fact. Not asserted in this pin. -/
def ConnesDistDefiniteConditional {iota : Type*} [Fintype iota]
    [DecidableEq iota] (D : Matrix iota iota ℂ) : Prop :=
  ConnesCommSeparates D →
    ∀ i j : iota, connesDist D i j = 0 → i = j

/-- **The commutant obstruction for row 5, named.** An algebra
element commutes with `D` - it lies in the commutant of `D`,
read here as the vanishing of the commutator - yet its point
evaluations separate `i` from `j`. Where such an element exists,
scaling it makes the supremum unbounded: the distance is
infinite at that pair. This is the obstruction the conditional
finiteness row is conditioned against. -/
def HasCommutantObstruction {iota : Type*} [Fintype iota]
    [DecidableEq iota] (D : Matrix iota iota ℂ) (i j : iota) :
    Prop :=
  ∃ a : iota -> ℂ, commDiag D a = 0 ∧ a i ≠ a j

/-- **Row 5 - finiteness. Grade: CONDITIONAL, registered as a
conditional shape with the commutant criterion named as its
condition.** Under the hypothesis that NO pair of seat points
carries the commutant obstruction (`HasCommutantObstruction`
nowhere), the distance is finite: `connesDist D i j < ⊤` for
every pair. The unconditional form is NOT registered and may not
be quoted as registered: finiteness fails exactly under the
commutant obstruction, and its criterion theorem-shape - with
its hard direction pre-named as a PARTIAL seam - is GR-DIST-1's
registered work. Corroboration at T4, not proof, per the annex:
the Python implementation already returns infinity exactly for
kernel-separated pairs. Not asserted in this pin. -/
def ConnesDistFiniteConditional {iota : Type*} [Fintype iota]
    [DecidableEq iota] (D : Matrix iota iota ℂ) : Prop :=
  (∀ i j : iota, ¬ HasCommutantObstruction D i j) →
    ∀ i j : iota, connesDist D i j < ⊤

/-- **Read-back.** Row 4 is exactly its registered conditional
statement, unfolded, condition included. The row itself, in
either form, is not asserted anywhere here. -/
theorem connesDistDefiniteConditional_unfold {iota : Type*}
    [Fintype iota] [DecidableEq iota] (D : Matrix iota iota ℂ) :
    ConnesDistDefiniteConditional D
      ↔ (ConnesCommSeparates D →
          ∀ i j : iota, connesDist D i j = 0 → i = j) :=
  Iff.rfl

/-- **Read-back.** Row 5 is exactly its registered conditional
statement, unfolded, commutant condition included. The row
itself, in either form, is not asserted anywhere here. -/
theorem connesDistFiniteConditional_unfold {iota : Type*}
    [Fintype iota] [DecidableEq iota] (D : Matrix iota iota ℂ) :
    ConnesDistFiniteConditional D
      ↔ ((∀ i j : iota, ¬ HasCommutantObstruction D i j) →
          ∀ i j : iota, connesDist D i j < ⊤) :=
  Iff.rfl

/-! ## DistSeparates: the sector-separation predicate, at its named seat

SEAT AND PAIR DECISION, on the face. The named seat is the
**Fin 4 cycle seat**: index type `Fin 4`, with the seat operator
`D` left as the predicate's argument - the concrete cycle
operator, built from the landed shift kit (`z4ShiftOp` of
`Q7C4R4SecondLeg`, `shiftC4C` of `Q7C4R4LinkC4`), is GR-DIST-2's
registered construction, gated on GR-DIST-1, and no operator is
chosen in this pin. The named sector pair is the pair the corpus
already names at this seat, consumed as registered and cited:
the chosen rung grading of `ChargePumpPost` section 1 -
`chargePumpSectorA = {0, 1}` (the low sector) and
`chargePumpSectorB = {2, 3}` (the high sector), pin data of that
module, a CHOSEN grading and not a derived object, in that
module's own words. No pair is invented here. (The C4 character
sectors `sectorC4 j` of `Q7C4R4Charge` are submodules of the
factor space, not subsets of the seat points, so they cannot be
the cross-pair index sets of a point-state distance; the rung
pair above is the corpus's named pair of subsets of `Fin 4`.)
-/

/-- **The sector-separation predicate (registered).** At the
Fin 4 cycle seat, for a seat operator `D`, the distance
separates the named sectors - the low sector
`chargePumpSectorA` and the high sector `chargePumpSectorB`,
consumed from `ChargePumpPost` as registered - iff on every
cross pair the distance is positive AND finite:
`0 < connesDist D i j` and `connesDist D i j < ⊤`, in both
cross directions. This is the Q7 gauntlet Item 7 second half's
shape - the distance separates the named sectors, or it does
not - made statable here and decidable at the seat by
GR-DIST-3, gated on GR-DIST-2. A degenerate seat (K-DIST-DEG)
decides it negatively, as a finding. Registered only; not
asserted for any `D` in this pin. -/
def DistSeparates (D : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  (∀ i ∈ chargePumpSectorA, ∀ j ∈ chargePumpSectorB,
    0 < connesDist D i j ∧ connesDist D i j < ⊤) ∧
  (∀ j ∈ chargePumpSectorB, ∀ i ∈ chargePumpSectorA,
    0 < connesDist D i j ∧ connesDist D i j < ⊤)

/-- **Read-back.** `DistSeparates` is exactly its registered
statement, unfolded: positivity and finiteness on every cross
pair of the named sectors, in both cross directions. The
predicate itself is not asserted for any operator anywhere in
this module. -/
theorem distSeparates_unfold (D : Matrix (Fin 4) (Fin 4) ℂ) :
    DistSeparates D
      ↔ (∀ i ∈ chargePumpSectorA, ∀ j ∈ chargePumpSectorB,
          0 < connesDist D i j ∧ connesDist D i j < ⊤) ∧
        (∀ j ∈ chargePumpSectorB, ∀ i ∈ chargePumpSectorA,
          0 < connesDist D i j ∧ connesDist D i j < ⊤) :=
  Iff.rfl

end ThetLogos
