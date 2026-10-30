/-
# S3-3: repair the reconstruction pin; the finite reflection-positivity clause

Brick S3-3 of the Span-3 first pier
(`routeb-general-scratch/scoping-span3-first-rung-2026-10-29.md` §2,
candidate (b); pack `routeb-general-scratch/pack-s3-3.md`).

**This is a STATEMENT REPAIR, not a proof.** It repairs the
*shape* of the corpus's one confirmed empty statement — the
2026 pin `OSReconstruction`
(`ThetLogos.OsterwalderSchrader`), audited degenerate: its
output bundle is unconnected to its input bundle
(`∀ _ : OsterwalderSchraderAxioms, ∃ _ : WightmanAxioms, True`,
proved outright in `ThetLogos.OSRepin` as
`oldPin_osReconstruction_trivial`). The 2026 pin stands
untouched beside the new entry (relabeling rule); nothing in
this module modifies, weakens, or re-uses it as a premise.
Reconstruction itself is **FRONTIER**: this module asserts
that nothing exists, proves no reconstruction, and takes no
limit. Proof-grade distance covered: **ZERO**. **NO CLAIM**
— parts of any Clay statement closed by this module: 0.
Dials: 0/4. The pier's fenced Span-3 vocabulary remains
unspent and appears nowhere below as a name.

## Outcome (1) — FINDING-form, with the maximal marker-level repair landed

The brief allowed two outcomes: a full repair (an
operation-shaped `Prop` tying output to input), or, if the
marker types cannot carry even that relation, the FINDING
that the 2026 pin sits below the house pin standard, with
the pin re-chartered as far as the types allow. The evidence
below decides a precise mixture, recorded at full rank:

- The marker types **can** carry exactly one grammatical
  tie. The only type-valued data in the two 2026 bundles are
  the input's `schwinger.carrier : Type` (`SchwingerMarker`
  has no other field — there are no Schwinger *functions* in
  the 2026 pin, only a bare type) and the output's
  `hilbert.carrier : Type` (`HilbertMarker` likewise; every
  other field of `WightmanAxioms` is a free `Prop`). §1 lands
  that tie (`ReconstructionTie`: output carrier **equals**
  input carrier) and the repaired pin built from it
  (`OSReconstructionTied`). The tie is a real relation at the
  level of *pairs*: some input/output pairs fail it
  (`reconstructionTie_counterexample`, proved).
- But the tie cannot carry the *content* a reconstruction
  relation must express — "the output field data arise from
  the input Schwinger functions" — because neither side has
  any field data or functions for a relation to bind. And at
  the pin level the repair buys nothing: the tied pin is
  still provable outright (`osReconstructionTied_trivial`,
  proved: choose the output carrier to be the input carrier
  and every free `Prop` field `True`). **FINDING, on the
  face: the 2026 pin sits below the house pin standard** —
  the standard the house later set for its statement pins,
  whose pins tie their data (the BSD pins tie their analytic
  package to their curve; the OS re-pin of 2026-10-18,
  `ThetLogos.OSRepin`, ties genuine tempered-distribution
  data through named analytic holes). No relation statable
  on the 2026 marker types can reach that standard, because
  the types contain nothing to tie. The re-charter (§1,
  `OSReconstructionCharter`) therefore points Span-3 work at
  the re-pin's schema — `OSReconstructionStatement` over the
  genuine Schwinger data `OSBundle.S`, with its two analytic
  holes named as parameters — as the only house-standard
  form of the reconstruction pin the corpus owns. The marker
  pin, tied or not, is quarantined: citable only with its
  weakness attached, never as "the reconstruction theorem,
  pinned" (scoping memo, DP-4).

## Outcome (2) — the finite E2 clause, and K-S3-3 FIRES (PARTIAL)

§2 states the finite reflection-positivity clause
(`FiniteReflectionPositivity`): the lattice theory's finite
Schwinger system — Gibbs expectations of configuration
observables (`LatticeCorrelations` / `LatticePositivity`) —
satisfies the E2-shaped clause **in its finite form**: for
every observable factoring through the strict positive half
(`posLinks`), the OS form's diagonal `osForm β F F` is a
nonnegative real number. This is the finite analogue of the
OS bundle's E2 (`OSBundle.reflectionPositive` in the re-pin:
a double sum over positive-time test functions is a
nonnegative real), read on finite objects.

**K-S3-3 — decided explicitly: the finite clause is NOT the
same statement as clause (a) of `TransferFormPos`, and the
difference matters.** The two are landed side by side in §2
(`FiniteReflectionPositivity` and `TransferClauseA`), with
the discrepancy named:

- **Different quantification class.** The finite clause
  quantifies over configuration observables factoring
  through the strict positive half — a proper, reflection-
  shaped subclass of observables, presented by a function on
  `posLinks` configurations, with the regularity (measurability
  and boundedness) of a test observable. Clause (a)
  quantifies over **every** vector of the OS Hilbert space
  `osSpace` (an `Lp` space over one time slice), with no
  factorization or regularity hypothesis.
- **Different form.** The finite clause is positivity of
  the reflection form `osForm` (Gibbs expectation of the
  reflected observable times the observable, over the whole
  configuration space). Clause (a) is positivity of the
  transfer operator's quadratic form `⟪f, T f⟫` on the OS
  space. Related by the finite reconstruction *construction*
  (`LatticeOSSpace` / `LatticeTransfer`), not by definition:
  neither statement is a paraphrase of the other.

The brick therefore lands **PARTIAL** on this item, and the
discrepancy becomes a named finite-side question on the
face: `FiniteE2ClauseAQuestion` — whether the two clauses
imply each other (stated as an equivalence `Prop`, **not
proved, not claimed**). What is landed about the two sides:
the finite clause at `β = 0`, hypothesis-free
(`finiteReflectionPositivity_zero`, by the landed
`osForm_zero_nonneg`); the finite clause at general `β`
under the finite Gram hypothesis
(`finiteReflectionPositivity_of_gram`, by the landed
criterion `osForm_nonneg_of_gram`); and clause (a) as the
first projection of `TransferFormPos`
(`transferClauseA_of_transferFormPos`, a landed triviality
of the same kind as `Span3FactLayerKernelPos`'s registration
— that module's `TransferFormClauseA` is the same quoted
clause, registered there for the A0 assembly and not
imported here).

## The stated implication chain toward the OS pin's E2 (each link labeled)

- **Link 1 (finite, LANDED):** the finite clause at
  `β = 0` — `finiteReflectionPositivity_zero`.
- **Link 2 (finite, LANDED as a criterion):** finite Gram
  hypothesis ⇒ the finite clause at that `β` —
  `finiteReflectionPositivity_of_gram`. The Gram hypothesis
  at general `(G, ρ)` is itself open (Stage 1b-B's clause;
  its standard proof needs character expansion / Peter–Weyl,
  absent from the pinned Mathlib).
- **Link 3 (finite, OPEN — the K-S3-3 question):** the
  finite clause ⇔ clause (a) of `TransferFormPos` —
  `FiniteE2ClauseAQuestion`, stated, not proved. (One level
  up, clause (a) together with its sibling clause (b) is
  the package `TransferFormPos` under which the landed
  `transfer_gap_of_formPos` gives the finite gap; that
  theorem is cited, not re-proved.)
- **Link 4 (continuum, HYPOTHESIS):** passage of the finite
  clause to a limit system's E2 — `E2PassageHypothesis`,
  stated as a schema whose limit-relation hole
  (`IsLimitOf`, the S3-2 scaling-limit construction) is a
  named parameter, with the target E2 registered standalone
  as `SchwingerSystemE2` and checked against the OS bundle's
  own E2 field (`schwingerSystemE2_of_osBundle`). No passage
  is proved or claimed; there is no limit object in the
  corpus for it to land on.
- **Link 5 (continuum, FRONTIER):** E2 for a limit bundle
  is one field of the OS axioms; the step from an OS bundle
  to a Wightman theory is reconstruction itself — the
  re-chartered pin of §1, whose analytic holes (analytic
  continuation; the Wightman-side conditions) are named
  parameters there, exactly because they are not statable
  as owned content today.

The chain is stated, not proved, except Links 1–2 and the
clause-(a) projection, which are landed theorems cited by
name above. `FiniteToOSE2Chain` (§2) assembles the five
links as one named `Prop` so the chain itself is a Lean
statement, not prose only.

**Tree-defect note.** This module sits on the transfer side
of the `reflSite_eq_torusShift_zero` duplicate seam: its
imports (`OSRepin`, `LatticeTransferCompact`) pull in the
`LatticeTransfer` / `LatticePositivity` chain and neither
the `LatticeGramSeries` chain nor the `PlaneCrossingFactor`
chain, the two sides that declare that name.
-/

import ThetLogos.OSRepin
import ThetLogos.LatticeTransferCompact

namespace ThetLogos

open MeasureTheory Finset

/-! ## §1. The marker-level repair, its limit, and the re-charter

All statements in this section are about the **2026 marker
pin** (`OsterwalderSchraderAxioms` / `WightmanAxioms` and
their marker types). The 2026 pin itself,
`OSReconstruction`, is not modified and is used only as the
target of the comparison lemmas. This section is a
**statement repair, not a proof** of reconstruction. -/

/-- **The one tie the 2026 marker types can carry.** The
output bundle is *of* the input system, at marker level:
the output's Hilbert-space marker carrier **is** the input's
Schwinger marker carrier. This is the strongest relation
statable on the two bundles: `SchwingerMarker` and
`HilbertMarker` each carry a single bare `Type`, and every
remaining field of `WightmanAxioms` is a free `Prop` with no
reference to either carrier, so no relation on these types
can mention Schwinger functions, field data, or analytic
continuation — none of those objects exist in the types. -/
def ReconstructionTie (B : OsterwalderSchraderAxioms)
    (W : WightmanAxioms) : Prop :=
  W.hilbert.carrier = B.schwinger.carrier

/-- **The non-degenerate reconstruction pin, marker form —
the NEW entry, beside the untouched 2026 pin.** Operation-
shaped: for every OS bundle there exist Wightman data
**tied to the input** by `ReconstructionTie` — the output
bundle is of the input system, not of nothing. Contrast the
2026 pin `OSReconstruction`
(`∀ _ : OsterwalderSchraderAxioms, ∃ _ : WightmanAxioms, True`),
whose existential body is `True` and which therefore ties
nothing. This entry is a **statement repair, not a proof**:
it asserts that no bundle exists, and — per
`osReconstructionTied_trivial` below — its own truth is as
cheap as the old pin's, which is the finding recorded in
the module header. -/
def OSReconstructionTied : Prop :=
  ∀ B : OsterwalderSchraderAxioms, ∃ W : WightmanAxioms,
    ReconstructionTie B W

/-- The repaired pin implies the 2026 pin: the tie is
additional statement shape on top of the old quantifiers,
not a weakening of them. Statement-level only. -/
theorem osReconstructionTied_implies_old :
    OSReconstructionTied → OSReconstruction :=
  fun h B => let ⟨W, _hW⟩ := h B; ⟨W, trivial⟩

/-- **The tie is a real relation on pairs.** There are an
input bundle and an output bundle that are **not** tied:
input carrier `PUnit`, output carrier `Empty`. So
`ReconstructionTie` is not the always-true relation — the
repaired pin's existential body genuinely restricts which
outputs count as outputs *of* a given input, at the only
level (pairs of marker carriers) the 2026 types support. -/
theorem reconstructionTie_counterexample :
    ∃ B : OsterwalderSchraderAxioms, ∃ W : WightmanAxioms,
      ¬ ReconstructionTie B W := by
  refine ⟨⟨⟨PUnit⟩, True, True, True, True, True⟩,
    ⟨⟨Empty⟩, True, True, True, True, True, True, True⟩, ?_⟩
  intro h
  change (Empty : Type) = PUnit at h
  exact Empty.elim (cast h.symm PUnit.unit)

/-- **The finding, machine-checked: the tied pin is still
trivial.** For every input bundle, the output bundle with
Hilbert carrier *chosen to be* the input carrier and every
free `Prop` field `True` satisfies the tie by `rfl`. So the
maximal marker-level repair remains satisfiable with no
analytic content whatsoever — no relation on the 2026
marker types can do better, because the types carry no
Schwinger functions and no field data for a stronger
relation to bind (module header). This theorem proves the
REPAIRED STATEMENT and thereby the limit of the repair; it
constructs no reconstruction, no measure, and no QFT. -/
theorem osReconstructionTied_trivial : OSReconstructionTied :=
  fun B => ⟨⟨⟨B.schwinger.carrier⟩, True, True, True, True,
    True, True, True⟩, rfl⟩

/-- **The re-charter: the house-standard form of the
reconstruction pin.** Span-3 work builds on this form or on
no pin (scoping memo, DP-4): the OS re-pin's schema
(`OSReconstructionStatement`, `ThetLogos.OSRepin`), in which
the input is a genuine OS bundle `OSBundle` whose Schwinger
data `B.S` are tempered distributions, the output `W` is a
family of tempered distributions, and the relation binding
output to input is the named parameter `IsBoundaryValueOf`
— applied there to `B.S` and `W`, so the output is *of this
input's data* by the statement's grammar, not by a label.
The second hole, `SatisfiesWightman`, is the Wightman-side
condition (filled by the sibling re-pin as
`SatisfiesWightmanPin`, `ThetLogos.WightmanRepin`). No
instantiation of either hole is given or claimed here;
reconstruction itself is **FRONTIER**. This definition is a
naming of the re-pin's schema as the charter — a statement
repair's pointer, not new content and not a proof. -/
def OSReconstructionCharter
    (IsBoundaryValueOf : ((n : ℕ) → SchwingerDist n) →
      ((n : ℕ) → SchwingerDist n) → Prop)
    (SatisfiesWightman : ((n : ℕ) → SchwingerDist n) → Prop) :
    Prop :=
  OSReconstructionStatement IsBoundaryValueOf SatisfiesWightman

/-- **The charter's quantifier shape, projected.** Under the
charter, every genuine OS bundle `B` provides output data
`W` bound to **this** bundle's Schwinger data by the named
relation, and satisfying the named Wightman-side condition.
Statement-level only: this reads the charter's definition
back; no bundle, output, or relation instance is asserted
to exist. -/
theorem osReconstructionCharter_output_tied
    (IsBoundaryValueOf : ((n : ℕ) → SchwingerDist n) →
      ((n : ℕ) → SchwingerDist n) → Prop)
    (SatisfiesWightman : ((n : ℕ) → SchwingerDist n) → Prop)
    (h : OSReconstructionCharter IsBoundaryValueOf
      SatisfiesWightman) (B : OSBundle) :
    ∃ W : (n : ℕ) → SchwingerDist n,
      IsBoundaryValueOf B.S W ∧ SatisfiesWightman W :=
  h B

/-! ## §2. The finite E2 clause, clause (a) beside it, and the chain

All statements in this section are about the **finite**
lattice theory at fixed `N` (the torus `Fin 4 → ZMod N`,
shifts `torusShift N`): its finite Schwinger system is the
Gibbs-expectation correlation system (`gibbsExpect`,
`LatticeCorrelations` / `LatticeGauge`), its reflection form
is `osForm` (`LatticePositivity`), and its OS Hilbert space
and transfer operator are `osSpace` / `transferOp`
(`LatticeOSSpace` / `LatticeTransfer`). This section is a
**statement repair, not a proof**: the two clauses are
stated and compared, the landed links are cited by name,
and the open links are labeled, not discharged. -/

section FiniteE2

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  {N : ℕ} [NeZero N] (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- **The finite reflection-positivity clause, stated
(deliverable (2), first half).** The lattice theory's finite
Schwinger system satisfies the E2-shaped reflection-
positivity clause **in its finite form**: for every
configuration observable `F` factoring through the strict
positive half — presented by a function `f` on `posLinks`
configurations, with the regularity of a test observable
(measurable and bounded against the product measure) — the
OS form's diagonal at coupling `β` is a nonnegative real
number: `0 ≤ (osForm β F F).re` and `(osForm β F F).im = 0`.
This is the finite analogue of the OS bundle's E2
(`OSBundle.reflectionPositive`: double sums over positive-
time test functions are nonnegative reals), with the finite
system's own reflection (`reflObs`, inside `osForm`) in
place of the continuum time reflection, and a single
observable's diagonal in place of the double sum — the
diagonal is the clause's content at finite volume, since
the form is sesquilinear (`osForm_add_left`,
`osForm_smul_left` and their right-hand siblings,
`LatticePositivity`). **Stated, not asserted**: no `β` is
claimed to satisfy this clause here; its landed instances
are the two theorems following. -/
def FiniteReflectionPositivity (β : ℝ) : Prop :=
  ∀ (F : Config (Fin 4 → ZMod N) G → ℂ)
    (f : (↥(posLinks (N := N)) → G) → ℂ),
    (∀ U, F U = f (fun ℓ : ↥(posLinks (N := N)) => U ℓ.1)) →
    AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) →
    (∃ Cf : ℝ, ∀ z, ‖f z‖ ≤ Cf) →
    0 ≤ (osForm μG ρ β F F).re ∧ (osForm μG ρ β F F).im = 0

/-- **Link 1 (finite, LANDED): the finite clause at
`β = 0`.** Hypothesis-free beyond `Even N` (the reflection's
own hypothesis), by the landed `osForm_zero_nonneg`
(`LatticePositivity`, Stage 1b-B): at zero coupling the
diagonal is a squared norm. The regularity hypotheses of
the clause are not consumed at `β = 0` — the landed
theorem needs none. -/
theorem finiteReflectionPositivity_zero (hN : Even N) :
    FiniteReflectionPositivity (N := N) μG ρ 0 :=
  fun F f hF _hfA _hCf => osForm_zero_nonneg μG ρ hN F f hF

/-- **The finite Gram data at coupling `β`** — the
hypothesis of the landed Gram criterion, registered as a
statement: a finite family of bounded measurable features
`Ξ i` on `posLinks` configurations over which the crossing
Boltzmann weight (the reflected half's weight, in split
variables `(y, u)`) is a finite Gram sum. At general
`(G, ρ)` this data's existence is **open** — Stage 1b-B's
clause, whose standard proof needs the character expansion
/ Peter–Weyl orthogonality absent from the pinned Mathlib.
Registered here so Link 2 below is a Lean implication, not
prose. -/
def FiniteGramData {ι : Type*} [Fintype ι]
    (Ξ : ι → (↥(posLinks (N := N)) → G) → ℂ) (β : ℝ)
    (hN : Even N) : Prop :=
  (∀ i, AEStronglyMeasurable (Ξ i)
    (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) ∧
  (∃ CΞ : ℝ, ∀ i z, ‖Ξ i z‖ ≤ CΞ) ∧
  ∀ (y : ↥(halfLinks (N := N)) → G)
    (u : ↥(negLinks (N := N)) → G),
    (Real.exp (- wilsonAction (torusShift N) ρ β
      ((splitEquiv (halfLinks (N := N))).symm (y, u))) : ℂ)
    = ∑ i, (starRingEnd ℂ) (Ξ i (mirrorP hN u))
        * Ξ i (restrictPos y)

/-- **Link 2 (finite, LANDED as a criterion): Gram data ⇒
the finite clause at that `β`.** By the landed criterion
`osForm_nonneg_of_gram` (`LatticePositivity`, Stage 1b-B),
applied observable by observable. This implication is a
theorem; its hypothesis is not discharged here or anywhere
at general `(G, ρ)` (see `FiniteGramData`). -/
theorem finiteReflectionPositivity_of_gram
    (hρcont : Continuous fun g => repMatrix ρ g) (hN : Even N)
    (hd : 0 < d) (β : ℝ) {ι : Type*} [Fintype ι]
    (Ξ : ι → (↥(posLinks (N := N)) → G) → ℂ)
    (hgram : FiniteGramData μG ρ Ξ β hN) :
    FiniteReflectionPositivity (N := N) μG ρ β := by
  obtain ⟨hΞA, ⟨CΞ, hΞB⟩, hsum⟩ := hgram
  intro F f hF hfA ⟨Cf, hfB⟩
  exact osForm_nonneg_of_gram μG ρ hρcont hN hd β F f hF hfA
    Cf hfB Ξ hΞA CΞ hΞB hsum

/-- **Clause (a) of `TransferFormPos`, quoted exactly** —
its first component (`LatticeTransferCompact`):

  `(∀ f : osSpace (N := N) μG ρ β,`
  `  0 ≤ (inner ℂ f (transferOp μG ρ hN2 hρcont β f)).re)`

registered here as a standalone predicate so the K-S3-3
comparison is between two Lean statements in one module,
side by side. (Clause (b), vacuum simplicity, is the second
component; it is not E2-shaped and is not this brick's
subject. The same quoted clause is registered for the A0
assembly as `TransferFormClauseA` in
`Span3FactLayerKernelPos`, not imported here.) -/
def TransferClauseA (β : ℝ) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) : Prop :=
  ∀ f : osSpace (N := N) μG ρ β,
    0 ≤ (inner ℂ f (transferOp μG ρ hN2 hρcont β f)).re

/-- Clause (a) is exactly the first projection of
`TransferFormPos` — a landed triviality, recorded so the
registration above is checked against the definition, not
against a paraphrase. -/
theorem transferClauseA_of_transferFormPos (β : ℝ)
    (hN2 : 2 ≤ N) (hρcont : Continuous fun g => repMatrix ρ g)
    (hd : 0 < d) (hPF : TransferFormPos μG ρ β hN2 hρcont hd) :
    TransferClauseA (N := N) μG ρ β hN2 hρcont :=
  hPF.1

/-- **K-S3-3's named finite-side question (OPEN, stated,
not proved).** Do the finite E2 clause and clause (a) of
`TransferFormPos` imply each other — here stated as their
equivalence at the same `(β, N)`? The module header names
why this is a question and not a remark: the two clauses
quantify over different classes (strict-positive-half
configuration observables with test regularity, versus
**every** vector of `osSpace`) and posit positivity of
different forms (`osForm`'s reflection form, versus the
transfer operator's quadratic form). **PARTIAL, on the
face**: brick S3-3 lands the two statements side by side
with the discrepancy named, and this question is the
discrepancy's name. Nothing in this module proves either
direction, and the question's truth at any `β` — including
`β = 0`, where the finite clause is landed (Link 1) — is
not claimed. -/
def FiniteE2ClauseAQuestion (β : ℝ) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) : Prop :=
  FiniteReflectionPositivity (N := N) μG ρ β ↔
    TransferClauseA (N := N) μG ρ β hN2 hρcont

/-- **The OS pin's E2, read on a bare Schwinger system.**
The `reflectionPositive` field of `OSBundle`
(`ThetLogos.OSRepin`), stated as a predicate of the system
`S` alone — same quantifiers, same factorization shape,
same conclusion (the double sum over reflected positive-
time test functions is a nonnegative real number), with
`S` in place of a bundle's `S` field. Registered standalone
because the passage link below must speak of the system a
limit *would produce*, before any bundle is built on it;
the lemma following checks this predicate against the
bundle's field. -/
def SchwingerSystemE2 (S : (n : ℕ) → SchwingerDist n) :
    Prop :=
  ∀ (k : ℕ) (ns : Fin k → ℕ)
    (F : (i : Fin k) → EucTest (ns i)),
    (∀ i, InPositiveTime (F i)) →
    ∀ (G : (i j : Fin k) → EucTest (ns i + ns j)),
    (∀ i j (z : Fin (ns i + ns j) × Fin 4 → ℝ),
      G i j z = (starRingEnd ℂ) (F i (reflFirst z))
        * F j (secondBlock z)) →
    ∃ r : ℝ, 0 ≤ r ∧ (∑ i, ∑ j, S (ns i + ns j) (G i j)) = r

/-- Every genuine OS bundle's Schwinger system satisfies
`SchwingerSystemE2` — by the bundle's own E2 field. A landed
triviality, recorded so the standalone predicate above is
checked against the re-pin's E2, not against a paraphrase:
the passage hypothesis below therefore really does target
the OS pin's E2, read on the system a limit would produce. -/
theorem schwingerSystemE2_of_osBundle (B : OSBundle) :
    SchwingerSystemE2 B.S :=
  B.reflectionPositive

/-- **Link 4, restated on systems.** Passage of the finite
clause to a limit system's E2: **if** the finite clause
held at every coupling `β` for this lattice datum, **then**
every Schwinger system that is a limit of this datum would
satisfy `SchwingerSystemE2` — the OS pin's E2, read on the
system itself (a bundle built on such a system, with this
system as its `S` field, would carry E2 as its
`reflectionPositive` field, by
`schwingerSystemE2_of_osBundle` read in reverse). The
limit relation `IsLimitOf` is a **named hole**, not a
definition: the corpus owns no construction of a continuum
Schwinger system from finite data (that construction is
the S3-2 scaling limit's subject, pinned there as a
statement of what its existence would assert, with no
instance asserted). This hypothesis is the weakest
schematic form of the passage: it is recorded so the chain
below names the exact place a continuum argument would
have to be supplied, and it is **not** a step toward
supplying one. -/
def E2PassageHypothesis
    (IsLimitOf : ((n : ℕ) → SchwingerDist n) → Prop) : Prop :=
  (∀ β : ℝ, FiniteReflectionPositivity (N := N) μG ρ β) →
  ∀ S : (n : ℕ) → SchwingerDist n, IsLimitOf S →
    SchwingerSystemE2 S

/-- **The stated implication chain, assembled (deliverable
(2), second half).** One named `Prop` whose conjuncts are
the chain's links, each labeled in the module header:

- conjunct 1: the finite clause at `β = 0` (**LANDED** —
  `finiteReflectionPositivity_zero` proves it under the
  `Even N` this chain takes as a parameter);
- conjunct 2: Gram data ⇒ the finite clause at every `β`
  (**LANDED as a criterion** —
  `finiteReflectionPositivity_of_gram`; the data's
  existence at general `(G, ρ)` is open). The conjunct
  states the Gram family indexed by `Fin k` — the
  reindexed form of a finite family; the criterion theorem
  itself allows any `Fintype` index;
- conjunct 3: the finite clause ⇔ clause (a) at every `β`
  (**OPEN** — `FiniteE2ClauseAQuestion`, the K-S3-3
  discrepancy as a named finite-side question);
- conjunct 4: passage to a limit system's E2
  (**HYPOTHESIS** — `E2PassageHypothesis`, its limit
  relation a named hole).

Beyond conjunct 4 the chain continues only in prose
(Link 5, module header): from an OS bundle to a Wightman
theory is reconstruction itself, **FRONTIER**, re-chartered
in §1 as `OSReconstructionCharter`. This chain is a
**statement repair, not a proof**: the assembled `Prop` is
not proved in this module, and its first two conjuncts are
proved separately below precisely so that what is landed
and what is open are never conflated. -/
def FiniteToOSE2Chain (hN : Even N) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (_hd : 0 < d)
    (IsLimitOf : ((n : ℕ) → SchwingerDist n) → Prop) :
    Prop :=
  FiniteReflectionPositivity (N := N) μG ρ 0 ∧
  (∀ (β : ℝ) (k : ℕ)
    (Ξ : Fin k → (↥(posLinks (N := N)) → G) → ℂ),
    FiniteGramData μG ρ Ξ β hN →
    FiniteReflectionPositivity (N := N) μG ρ β) ∧
  (∀ β : ℝ, FiniteE2ClauseAQuestion μG ρ β hN2 hρcont) ∧
  E2PassageHypothesis (N := N) μG ρ IsLimitOf

/-- **The chain's finite links, landed.** Conjuncts 1 and 2
of `FiniteToOSE2Chain` hold: the `β = 0` instance and the
Gram criterion are the landed theorems cited there. This
is the whole proved content of the chain — conjuncts 3
(the K-S3-3 question) and 4 (the passage hypothesis) are
**not** part of this theorem and remain open / hypothetical
exactly as labeled. Statement-level assembly of landed
links; no new positivity is proved. -/
theorem finiteToOSE2Chain_finiteLinks (hN : Even N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d) :
    FiniteReflectionPositivity (N := N) μG ρ 0 ∧
    (∀ (β : ℝ) (k : ℕ)
      (Ξ : Fin k → (↥(posLinks (N := N)) → G) → ℂ),
      FiniteGramData μG ρ Ξ β hN →
      FiniteReflectionPositivity (N := N) μG ρ β) :=
  ⟨finiteReflectionPositivity_zero μG ρ hN,
   fun β _k Ξ hgram =>
     finiteReflectionPositivity_of_gram μG ρ hρcont hN hd β
       Ξ hgram⟩

end FiniteE2

end ThetLogos
