import Mathlib.Tactic
import ThetLogos.MeaningBridge
import ThetLogos.PrimordialsExhibit
import ThetLogos.ThermalSourceComposite

/-!
# ThetLogos.PrimordialAlignment — brick 2: one checkable shape for the three correlations

HONESTY LEDGER (read before citing):

- COMMISSION. Jeff's seeing (2026-11-04, T5, filed verbatim in
  `~/memory/2026-11-04.md`): the primordials are mathematics,
  physics, and the correlations of letters and meanings.
  Jeff's commission chain: "build the bridge of the alignment"
  → "do all and see" (2026-11-04). This module is BRICK 2 of
  that commission: the three-primordial alignment exhibit. It
  consumes brick 1 (`ThetLogos.MeaningBridge`, interface
  FROZEN) and the primordials exhibit
  (`ThetLogos.PrimordialsExhibit`), and SR-5
  (`ThetLogos.ThermalSourceComposite`).
- THE THESIS TESTED, AND ITS EXACT STRENGTH. Brick 1 (pin
  N1's first formable core) fixed what a *denotation* is: an
  alignment (a relation between a syntax set and a meaning
  set) that is FUNCTIONAL (no conflation) and TOTAL (no
  gaps) — equivalently, the graph of one checkable function.
  This brick tests one claim at the corpus's three owned
  seats: **where the corpus actually has content, each
  primordial's correlation is a denotation in that sense.**
  §1 (mathematics): the exhibit's number-action correlation
  IS a functional, total, injective alignment, and its
  canonical denotation is the exhibit's own assignment.
  §2 (language): ANY total alignment has a denotation whose
  graph is a functional+total alignment; under functionality
  the alignment IS that graph, and its synonym classes are
  brick 1's quotient object. §3 (physics): the corpus's
  thermal source, viewed through the graph construction, is
  a functional+total alignment, and the total of its
  canonical denotation is the state's mean energy (SR-5's
  landed identity). §4 bundles the three into one record
  with one shared-shape theorem.
- GRADE OF EACH ITEM, ON ITS FACE. DEFINITIONAL items pin
  shapes and prove nothing. GENERIC items are general facts
  of the pinned type theory, true of every relation of the
  shape. SEAT-CONTENT items consume facts the corpus itself
  proved at its own seats (`numAction_injective`, SR-5's
  `sum_thermalSource`). No grade is upgraded to match the
  commission's sketch: where a seat's honest content is
  definitional, the face says DEFINITIONAL.
- WHAT THIS MODULE IS NOT. The physics seat (§3) is the
  careful one, and its limit is stated here once, plainly:
  ANY function whatsoever has a functional+total graph, so
  §3's shape facts show only that the physics seat's
  assignments FIT the denotation shape; they derive nothing
  physical — no response, no motion, no law. The one
  seat-content fact (§3's total) is SR-5's bookkeeping
  identity restated: the source's total is the state's mean
  energy. Nothing in this module connects the seats to each
  other: mathematics↔physics as a DERIVATION (pin N4, the
  program horizon) is not stated, natural-language semantics
  (pin N2) is untouched, and no unified-language object
  (pin N5) is built — §4's record holds three alignments
  side by side; it is a bundle, not a container of every
  language. No gravitational vocabulary appears anywhere in
  this module (kill K-MB-3 stands armed over the whole
  commission). Jeff's seeing stands at T5 as filed; this
  module is the formable core of its alignment shape and
  nothing more. NO CLAIM; dials 0/4.
-/

namespace ThetLogos

/-! ## §1. The mathematics seat: the number-action correlation is a denotation

The primordials exhibit pinned the mathematics primordial's
own correlation: a real number IS an object and DOES an
action (`numAction a`, scaling on the potential space), and
the assignment is faithful at an inhabited seat
(`numAction_injective`). Read through brick 1's
`graphAlign`, that correlation is an alignment from numbers
to actions — and it is a denotation in the N1 sense:
functional, total, and injective, with the exhibit's own
assignment as its canonical denotation. -/

/-- **The mathematics seat's alignment (DEFINITIONAL).**
Numbers aligned to their actions: the graph of the
exhibit's `numAction`. The shape is pinned here; the content
is the theorems below. -/
def numAlign (V : Type*) :
    MeaningAlign ℝ ((V → ℝ) →ₗ[ℝ] (V → ℝ)) :=
  graphAlign (numAction (V := V))

/-- **The number-action alignment never conflates and never
gaps (DEFINITIONAL-grade fact).** It is a function's graph,
and functions never conflate and never gap (brick 1's
`graphAlign_functional_total`). Stated at the seat so §4's
bundle can consume it in the seat's own name. -/
theorem numAlign_functional_total (V : Type*) :
    (numAlign V).Functional ∧ (numAlign V).Total := by
  show (graphAlign (numAction (V := V))).Functional ∧
    (graphAlign (numAction (V := V))).Total
  exact graphAlign_functional_total _

/-- **The number-action alignment has no synonymy
(SEAT-CONTENT).** Distinct numbers carry distinct actions:
this is the exhibit's faithfulness theorem
`numAction_injective` restated in the alignment's
vocabulary. The hypothesis has teeth, as it did there: on an
empty seat there are no potentials to act on and the
correlation collapses — `[Nonempty V]` is on the face. -/
theorem numAlign_injective (V : Type*) [Nonempty V] :
    (numAlign V).InjectiveAlign := by
  intro a b T h₁ h₂
  have h₁' : T = numAction (V := V) a := h₁
  have h₂' : T = numAction (V := V) b := h₂
  exact numAction_injective (h₁'.symm.trans h₂')

/-- **The alignment's canonical denotation is the exhibit's
assignment (SEAT-CONTENT).** Brick 1's `denotationOf` — the
picked meaning under totality — applied to the number-action
alignment returns exactly `numAction`: the abstract
denotation machinery and the corpus's own number-action
agree on the nose, not merely up to the characterization. -/
theorem numAlign_denotationOf (V : Type*) (hT : (numAlign V).Total) :
    (numAlign V).denotationOf hT = numAction (V := V) := by
  funext a
  have h' : (numAlign V).denotationOf hT a = numAction (V := V) a :=
    (numAlign V).denotationOf_spec hT a
  exact h'

/-! ## §2. The language seat: every denotation's graph is an alignment of the shape

Brick 1 built the language seat abstractly: a syntax set, a
meaning set, an alignment. This section records, in the
exhibit's vocabulary, the three facts §4's bundle consumes:
the graph of a picked denotation is functional+total; under
functionality the alignment IS that graph (brick 1's
`align_iff_denotation`, promoted to an equality of
relations); and the alignment's meaning-classes object is
brick 1's quotient of same-meaning glyphs. All GENERIC
grade — true of every alignment of this shape; no semantics
is claimed for anything. -/

/-- **A functional+total alignment IS the graph of its
denotation (GENERIC).** Brick 1 characterized such
alignments as graphs (`functional_total_iff`); here the
canonical denotation's graph is the alignment itself, as an
equality of relations. -/
theorem MeaningAlign.eq_graphAlign_denotationOf {S M : Type*}
    (A : MeaningAlign S M) (hF : A.Functional) (hT : A.Total) :
    A = graphAlign (A.denotationOf hT) := by
  funext s m
  exact propext (A.align_iff_denotation hF hT s m)

/-- **The picked denotation's graph never conflates and
never gaps (GENERIC).** For ANY total alignment, the graph
of its picked denotation is a functional+total alignment —
brick 1's `graphAlign_functional_total` at the denotation.
(Any function would do; the denotation is the one brick 1's
machinery picks.) -/
theorem denotation_graph_functional_total {S M : Type*} (A : MeaningAlign S M)
    (hT : A.Total) :
    (graphAlign (A.denotationOf hT)).Functional ∧
      (graphAlign (A.denotationOf hT)).Total :=
  graphAlign_functional_total _

/-- **The alignment's meaning-classes object (GENERIC).**
For a total alignment, the classes of glyphs sharing a
denoted meaning — the quotient of the syntax by brick 1's
same-meaning setoid of the picked denotation — named here
as the alignment's own object. It is brick 1's
`quotientSameMeaningEquivRange`: the classes are equivalent
to the range of the denotation, the occurring meanings,
each counted once. -/
noncomputable def meaningClassesEquiv {S M : Type*} (A : MeaningAlign S M)
    (hT : A.Total) :
    Quotient (sameMeaningSetoid (A.denotationOf hT)) ≃
      Set.range (A.denotationOf hT) :=
  quotientSameMeaningEquivRange _

/-! ## §3. The physics seat: the thermal source fits the shape — and that is all it does

The corpus's physics content at a seat is Gibbs/energy
bookkeeping. SR-5 built the thermal source: a Gibbs state's
site-energy density, `thermalSource E β i = gibbsProb E β i
* E i`. Viewed through `graphAlign`, it is an alignment
from sites to their source values, and — like every
function's graph — functional and total. THE GRADE IS
DEFINITIONAL AND THE REASON IS ON THE FACE: any function
whatsoever passes this test, so passing it shows the
physics seat's assignment FITS the denotation shape and
derives nothing physical. The one seat-content fact is the
total: the sum of the alignment's canonical denotation over
the seat is the state's mean energy — SR-5's landed
identity `sum_thermalSource`, restated as a fact about the
alignment's denotation. What that total is (a thermal
expectation) and is not (anything downstream: SR-5's
ceiling stands — the Poisson channel fed by this source is
blind to exactly this total) is SR-5's record, consumed
here, not extended. -/

/-- **The physics seat's alignment (DEFINITIONAL).** Sites
aligned to their thermal-source values: the graph of SR-5's
`thermalSource`. A Gibbs state's site-energy assignment,
read as an alignment. -/
def thermalSourceAlign {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (E : V → ℝ) (β : ℝ) : MeaningAlign V ℝ :=
  graphAlign (thermalSource E β)

/-- **The thermal-source alignment never conflates and
never gaps (DEFINITIONAL-grade fact).** It is a function's
graph. This is the whole of the physics seat's shape claim,
and it is definitional for the reason stated in the
section prose: the test admits every function. -/
theorem thermalSourceAlign_functional_total {V : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] (E : V → ℝ) (β : ℝ) :
    (thermalSourceAlign E β).Functional ∧
      (thermalSourceAlign E β).Total := by
  show (graphAlign (thermalSource E β)).Functional ∧
    (graphAlign (thermalSource E β)).Total
  exact graphAlign_functional_total _

/-- **The alignment's canonical denotation is SR-5's source
(SEAT-CONTENT).** Brick 1's picked denotation of the
thermal-source alignment is the thermal source itself: the
abstract machinery returns the corpus's own composite, on
the nose. -/
theorem thermalSourceAlign_denotationOf {V : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] (E : V → ℝ) (β : ℝ)
    (hT : (thermalSourceAlign E β).Total) :
    (thermalSourceAlign E β).denotationOf hT = thermalSource E β := by
  funext i
  have h' : (thermalSourceAlign E β).denotationOf hT i
      = thermalSource E β i :=
    (thermalSourceAlign E β).denotationOf_spec hT i
  exact h'

/-- **The total of the denotation is the mean energy
(SEAT-CONTENT).** Summing the thermal-source alignment's
canonical denotation over the seat returns exactly the
Gibbs state's mean energy: SR-5's `sum_thermalSource`,
restated as a fact about the alignment. This says what the
alignment's total IS — a thermal expectation, bookkeeping
data of the state. It derives nothing downstream of the
source; in particular SR-5's ceiling (the channel fed by
this source cannot see this total) is untouched. -/
theorem sum_denotation_thermalSourceAlign {V : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] (E : V → ℝ) (β : ℝ) :
    ∑ i, (thermalSourceAlign E β).denotationOf
        (thermalSourceAlign_functional_total E β).2 i
      = ModularVariance.meanEnergy E β := by
  rw [thermalSourceAlign_denotationOf]
  exact sum_thermalSource E β

/-! ## §4. The alignment object: three seats, one checkable shape

One record bundling the three seats' alignments, and one
theorem: in the canonical bundle built from the corpus's
own objects, all three components are functional and total
— each primordial's correlation, where the corpus has
content, is a denotation in brick 1's sense. The bundle is
DEFINITIONAL as a structure (it holds the three side by
side and asserts nothing by its shape); the shared-shape
theorem is SEAT-CONTENT exactly to the extent its
components are — the mathematics component rests on the
exhibit's faithful assignment, the physics component is
definitional-grade (§3's face), the language component is
brick 1's generic machinery at a picked denotation. The
bundle is NOT a unified language and NOT a container of
every language: it is three alignments in one record, with
the shared shape proved. -/

/-- **The alignment bundle (DEFINITIONAL).** One record
holding the three primordials' alignments at their seats:
mathematics (numbers to their actions at seat `V`), language
(glyphs `S` to meanings `M`), physics (sites of `V` to
thermal-source values). A working label only — naming is
Jeff's hand. The record asserts nothing; §4's theorem is
the content. -/
structure PrimordialAlignment (V S M : Type*) where
  /-- The mathematics seat's alignment. -/
  mathAlign : MeaningAlign ℝ ((V → ℝ) →ₗ[ℝ] (V → ℝ))
  /-- The language seat's alignment. -/
  langAlign : MeaningAlign S M
  /-- The physics seat's alignment. -/
  physAlign : MeaningAlign V ℝ

/-- **The canonical bundle (DEFINITIONAL).** The bundle
built from the corpus's own objects: the exhibit's
number-action alignment; the graph of a total alignment's
picked denotation, for the language seat; SR-5's
thermal-source alignment, for the physics seat. -/
def PrimordialAlignment.canonical {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] {S M : Type*} (A : MeaningAlign S M) (hT : A.Total)
    (E : V → ℝ) (β : ℝ) : PrimordialAlignment V S M where
  mathAlign := numAlign V
  langAlign := graphAlign (A.denotationOf hT)
  physAlign := thermalSourceAlign E β

/-- **THE SHARED SHAPE (SEAT-CONTENT, to the extent of its
components).** In the canonical bundle, all three
components are functional and total: no conflation and no
gaps at any of the three seats. This is the brick's thesis
at its proved strength — "correlation", across the seats
the corpus owns, has one checkable shape: a denotation.
The components' grades differ and stay as graded: the
mathematics component is the graph of the exhibit's
faithful assignment (§1), the language component is brick
1's generic graph fact at a picked denotation (§2), the
physics component is definitional-grade (§3). The theorem
asserts the shared shape and nothing between the seats:
no seat is derived from another. -/
theorem PrimordialAlignment.canonical_shared_shape {V : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] {S M : Type*}
    (A : MeaningAlign S M) (hT : A.Total) (E : V → ℝ) (β : ℝ) :
    (PrimordialAlignment.canonical A hT E β).mathAlign.Functional ∧
    (PrimordialAlignment.canonical A hT E β).mathAlign.Total ∧
    (PrimordialAlignment.canonical A hT E β).langAlign.Functional ∧
    (PrimordialAlignment.canonical A hT E β).langAlign.Total ∧
    (PrimordialAlignment.canonical A hT E β).physAlign.Functional ∧
    (PrimordialAlignment.canonical A hT E β).physAlign.Total :=
  ⟨(numAlign_functional_total V).1, (numAlign_functional_total V).2,
    (graphAlign_functional_total _).1, (graphAlign_functional_total _).2,
    (thermalSourceAlign_functional_total E β).1,
    (thermalSourceAlign_functional_total E β).2⟩

end ThetLogos
