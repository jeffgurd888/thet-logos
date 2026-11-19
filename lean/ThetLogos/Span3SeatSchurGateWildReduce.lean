import ThetLogos.Span3SeatSchurGateWild
/-!
# W-2′ — statement freeze (DRAFT): the even-N restatement of
# the W-2 rigidity reduction (steps 1–2), frozen as statement
# forms before content

Queue position 21 (bench queue, QUEUE.md). Sources of record:
the original W-2 spec (q3-2-gate3wild-scoping-2026-11-06.md
§2 steps 1–2; q3-closable-scope-2026-11-08.md item 2), the
W-2 lane STATUS (~/workspace/thet-logos-w2/STATUS.md, branch
`w2-rigidity` @ 1be0d40), and Zero's ruling of 2026-11-08
18:44 EST ("Rule the even-N restatement for W-2") discharging
the restatement decision.

## Why this slot exists

W-2 as frozen is FALSE in its own section context: at
`N = 1` every plaquette collapses to a commutator, the
Boltzmann factor is constant (Step 1's premise holds for
every `ρ`), while at the Circle/Hamel seat the trace
function `χ` is not `AEStronglyMeasurable` (Step 1's
conclusion fails) — and the same seat refutes
`Gate3WildLemma` itself at `N = 1`. The formalization of
that refutation is queue position 20 (W-2-KILL, pin-first
pair, branch `w2kill`). The obstruction is exactly the
missing `Even N` / `2 ≤ N`: the consuming headline
(`pullBotKernel_seatFactorApproxExpansion_of_gate3WildLemma`)
already carries `Even N`, and at even `N` the time-1 read
fires, so the plaquette word form
`α c * u' ℓ * (α (σ_ν c))⁻¹ * (u ℓ)⁻¹` is genuine and the
section + trace-form route is the standard one. This slot
is the restated reduction: steps 1–2 with `Even N` in
context. NOT `Gate3WildLemma` (its assembly from W-1 +
this reduction is W-3's slot), NOT the continuity step.

## What this draft is

The queue freezes this brick's statement in its STATUS
before content (STATUS-W2PRIME.md). This module carries
exactly those frozen forms as named Props — definitions
ONLY, 0 theorems BY DESIGN at the freeze. The content
(the proofs of the two step forms, priced ~M) is attempted
only at this slot's build turn, against these forms,
unchanged. If a form below proves unprovable as written,
that is a kill report to the parent, never a quiet
restatement.

## Frozen-form choices (declared, per STATUS-W2PRIME §3)

- `Even N` rides as an explicit hypothesis inside each
  frozen form, so no consumer can use the unrestated
  (false) shape by accident.
- Step 1 is frozen at every `β > 0` (the audit fixes `β`
  in context; the ∀-form is the same content applied at
  each `β`).
- Trace functions are frozen as
  `g ↦ Matrix.trace (A * repMatrix ρ g)` for `A` in
  `span ℂ (range (repMatrix ρ ·))`. The span is
  `*`-closed (the range of a unitary representation is
  closed under `conjTranspose` via `g ↦ g⁻¹`), so this
  shape and the `tr (A* * ·)` shape carry the same
  content for Step 2's dual-basis route; the choice is
  recorded here so the content brick does not re-decide
  it silently.

## Pre-registered fences

- DIAL-INELIGIBLE map work (Q3 scoping R5): Dial 3 = 0
  on every outcome; no dial moves if this lands in full.
- K-W2-EVENN ARMED on the restated pair: it fires if an
  in-context seat at even `N` refutes steps 1–2 as
  restated here — i.e. the narrowing itself dies. (The
  original scoping armed no kills on Q3-2; K-W2-EVENN is
  the restated form's own kill, per QUEUE.md position 21.)
- This module does NOT restate `Gate3WildLemma`, does
  NOT touch the wild section, and does NOT pre-empt
  W-2-KILL (the frozen form's refutation is its own
  slot).

NO CLAIM; dials 0/4.
-/


namespace ThetLogos

open MeasureTheory Finset Filter Topology
open scoped Matrix ENNReal NNReal

section Gate3WildReduce

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-! ## The premise and conclusion forms -/

/-- **Premise form (Step 1's hypothesis):** at inverse
temperature `β`, the stratum Boltzmann factor is
`AEStronglyMeasurable` in the stratum variable for every
pair of layer data `u u'`. Identical in shape to the
conclusion side of `Gate3WildLemma`, negated there. -/
def WildBoltzmannPremise (β : ℝ) : Prop :=
  ∀ u u' : LayerLink N → G,
    AEStronglyMeasurable
      (fun α : LayerSite N → G =>
        (Real.exp (-(layerAction ρ β α u u')) : ℂ))
      (Measure.pi fun _ : LayerSite N => μG)

/-- **Conclusion form (Step 1's output, Step 2's input):**
every trace function of `repMatrix ρ` against a matrix
`A` in the span of the representation's range is
`AEStronglyMeasurable` w.r.t. `μG`. -/
def WildTraceConclusion : Prop :=
  ∀ A ∈ Submodule.span ℂ (Set.range (fun g : G => repMatrix ρ g)),
    AEStronglyMeasurable
      (fun g : G => Matrix.trace (A * repMatrix ρ g)) μG

/-! ## The two frozen step forms (even-N restatement) -/

/-- **Step 1, restated (frozen form):** under `Even N`,
if the Boltzmann factor is `AEStronglyMeasurable` for
every pair of layer data at every `β > 0`, then every
trace function of `repMatrix ρ` over the span of its
range is `AEStronglyMeasurable` w.r.t. `μG`. (Proof
route, audit: a.e. sections on the finite stratum
product; the plaquette word form at even `N`.) -/
def WildStep1EvenN : Prop :=
  Even N →
    ∀ (β : ℝ), 0 < β →
      WildBoltzmannPremise (N := N) μG ρ β →
      WildTraceConclusion μG ρ

/-- **Step 2, restated (frozen form):** under `Even N`,
if every trace function over the span of the range is
`AEStronglyMeasurable`, then `repMatrix ρ` itself is
`AEStronglyMeasurable` w.r.t. `μG`. (Proof route,
audit: nondegeneracy of the trace form
`(X, Y) ↦ tr (X* * Y)` on the finite-dimensional span —
a fact consumed inside the proof, not a hypothesis —
and a dual basis.) -/
def WildStep2EvenN : Prop :=
  Even N →
    WildTraceConclusion μG ρ →
    AEStronglyMeasurable (fun g : G => repMatrix ρ g) μG

/-- **The pair, restated (frozen form):** under `Even N`,
the Boltzmann premise at any `β > 0` delivers
`AEStronglyMeasurable (fun g => repMatrix ρ g) μG` —
the exact input W-1/W-3 consume. This is the W-2′
brick's headline form; the content module proves it via
the two step forms above. -/
def WildReducePairEvenN : Prop :=
  Even N →
    ∀ (β : ℝ), 0 < β →
      WildBoltzmannPremise (N := N) μG ρ β →
      AEStronglyMeasurable (fun g : G => repMatrix ρ g) μG

end Gate3WildReduce

end ThetLogos
