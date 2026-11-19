import ThetLogos.Span3SeatSchurGateWild
/-!
# W-2-KILL — record pin: the frozen W-2 form's N = 1 refutation,
# frozen as statement forms (pin-first pair, part 1: the pin)

Queue position 20 (bench queue, QUEUE.md). Source of record:
the W-2 lane STATUS (~/workspace/thet-logos-w2/STATUS.md,
branch `w2-rigidity` @ 1be0d40), whose paper-grade verdict of
2026-11-08 stands: **W-2 NOT LANDABLE AS FROZEN** — the
Gate3Wild rigidity reduction (steps 1–2 of
q3-2-gate3wild-scoping-2026-11-06.md §2–§3) is FALSE in its
own section context at the seat `N = 1`, and the same seat
refutes `Gate3WildLemma` itself at `N = 1`. Zero ruled the
even-N restatement for the narrowed successor (W-2', queue
position 21) the same day; this slot is the T1 formalization
of the refutation of the FROZEN form.

## What this pin is

A record pin in the house pin pattern (OG-0 / ACT-0 /
MV-3): definitions and frozen statement forms ONLY —
0 theorems BY DESIGN. The queue prices this slot as a
PIN-FIRST PAIR inside one queue slot: this pin (S), then
the content module (M–L) proving the forms below. Nothing
here is proved; nothing here is claimed. The content
module's verdicts land under their own commits.

## The counterexample seat (paper form, lane STATUS)

- `G = Circle`, `μG` = normalized Haar probability
  (`volume`), `d = 1`, `N = 1` — every hypothesis is
  in-context for the wild section (`[NeZero 1]`; NO
  `Even N`, NO `2 ≤ N`, NO local compactness anywhere).
- At `N = 1` the layer's time-1 read never fires
  (`(x 0).val = 1` is impossible in `ZMod 1`), every
  plaquette of `layerConfig α u u'` is the commutator
  `α c * u ℓ * (α c)⁻¹ * (u ℓ)⁻¹ = 1` (Circle abelian),
  so `layerAction = 0` and the Boltzmann factor is the
  constant `1` — for EVERY `ρ`. Step 1's premise holds.
- The character `χ = λ̃ · id` with `λ̃` induced by a
  ℚ-linear `Ã : ℝ → ℝ`, `Ã(1) = 0`, `Ã ≠ 0` (Hamel basis),
  is a group endomorphism of Circle that is NOT
  `AEStronglyMeasurable` (nor measurable): a.e. equality
  to a measurable map would make the convolution
  `F(x) = ∫ m(xy)·conj(m(y)) dμ(y)` a continuous
  representative of `χ`, forcing `λ̃` continuous, and a
  continuous `λ̃` lifts to `ψ(x) = cx` on ℝ, whence
  `Ã − c·id` is ℚ-linear, integer-valued, and divisible
  by every `2^n` — hence zero, contradicting `Ã ≠ 0`
  via `Ã(1) = 0 ⇒ c = 0`.
- With `ρ'` the scalar representation of `χ`, the pair's
  conclusion (`repMatrix ρ'` AEStronglyMeasurable) fails
  while its premise holds: Step 1 is false in-context,
  and `Gate3WildLemma` at this seat has a true premise
  (`¬ Measurable (repMatrix ρ')`) and a false conclusion.

## Pre-registered fences

- DIAL-INELIGIBLE, pre-registered: this is kill
  documentation for a frozen statement form. Dial 3 = 0;
  no dial moves if the content lands in full.
- The frozen form stays frozen: this pin does NOT
  restate `Gate3WildLemma`, does NOT touch the wild
  section, and does NOT pre-empt W-2' (the ruled even-N
  restatement is a separate slot with its own frozen
  statement).
- NO CLAIM. The paper verdict is already on record
  (2026-11-08); this pin freezes the Lean forms the
  content module must discharge, nothing more.

NO CLAIM; dials 0/4.

**Repair (2026-11-12, bench successor #2, under Zero's
full-control grant of 2026-11-12 14:13 EST).** As first
drafted, this module did not elaborate: the line
`noncomputable def n1μ : Measure Circle := volume`
failed, because this Mathlib pin (v4.35.0-rc3) carries
NO `MeasureSpace Circle` instance (Circle.lean provides
MeasurableSpace + BorelSpace only; `#synth MeasureSpace
Circle` fails), so `volume` has no referent at `Circle`.
All other declarations elaborated. Disposition taken —
the brief's preference (ii): **`n1μ` is re-pinned as an
abstract measure parameter** (a section variable carrying
exactly the wild file's Haar-class hypotheses:
probability, both-sided invariance, inversion
invariance), and the forms that mention it quantify over
it. No statement form is otherwise changed; no content
is dropped — the census change is disclosed here and in
STATUS-W2KILL.md: nine statement forms + one parameter,
where the draft had ten definitions. The content module
instantiates the parameter with a Haar measure (e.g.
`Measure.haarMeasure` of an explicitly chosen
`PositiveCompacts Circle`) when it lands; nothing in the
kill-forms prefers one Haar-class measure over another,
which is exactly why the parameter form loses nothing.
-/


namespace ThetLogos

open MeasureTheory

/-! ## The seat measure -/

section N1Seat

/- The seat's measure — a **parameter**, not a
definition (repair of 2026-11-12, on the module's face;
see the header note): the seat's measure is normalized
Haar probability on `Circle`, but this pin of Mathlib
has no `MeasureSpace Circle` instance, so `volume`
cannot name it. The parameter carries exactly the
hypothesis class the wild file's lemmas quantify over
for `μG` — a probability measure, invariant on both
sides and under inversion (the Haar class). Every form
below that mentions `n1μ` is a form about an arbitrary
such measure; the premise halves hold for every measure
of the class (at `N = 1` the Boltzmann factor is the
constant 1), and the character halves consume exactly
these invariance hypotheses. The content module
instantiates `n1μ` with a Haar measure when it lands. -/
variable (n1μ : Measure Circle) [IsProbabilityMeasure n1μ]
  [n1μ.IsMulLeftInvariant] [n1μ.IsMulRightInvariant]
  [n1μ.IsInvInvariant]

/-! ## The wild ℚ-linear data and its character -/

/-- The existence form for the wild ℚ-linear map: a
ℚ-linear `Ã : ℝ → ℝ` killing `1` but not identically
zero (Hamel basis of ℝ over ℚ containing `1`). The
content module proves this from the basis API. -/
def WildQLinearExists : Prop :=
  ∃ A : ℝ →ₗ[ℚ] ℝ, A 1 = 0 ∧ A ≠ 0

/-- The character form: `χ : Circle → Circle` is the
wild character of `A` when it is a group endomorphism
linked to `A` along the covering
`t ↦ Circle.exp (2π t)` — the linking is well-defined
exactly because `A 1 = 0` absorbs the period. -/
def IsWildCharacter (A : ℝ →ₗ[ℚ] ℝ) (χ : Circle → Circle) :
    Prop :=
  (∀ x y : Circle, χ (x * y) = χ x * χ y) ∧
    ∀ t : ℝ, χ (Circle.exp (2 * Real.pi * t))
      = Circle.exp (2 * Real.pi * (A t))

/-- The linked-pair existence form: some ℚ-linear `A`
and some `χ` realize the wild character. Content
discharges this from `WildQLinearExists` by the
quotient descent `ℝ ⧸ ℤ → Circle`. -/
def WildCharacterExists : Prop :=
  ∃ (A : ℝ →ₗ[ℚ] ℝ) (χ : Circle → Circle),
    A 1 = 0 ∧ A ≠ 0 ∧ IsWildCharacter A χ

/-- The representation form: `ρ` is the scalar
representation of the character `χ` at `d = 1` when
every matrix of `ρ` is the diagonal (1×1) matrix of the
character value. Content constructs such a `ρ` from the
endomorphism property of `χ` (and `χ 1 = 1`, its
consequence at `x = y = 1` after cancellation in the
group `Circle`). -/
def IsScalarRep (χ : Circle → Circle)
    (ρ : Circle →* ↥(Matrix.unitaryGroup (Fin 1) ℂ)) :
    Prop :=
  ∀ g : Circle, repMatrix ρ g
    = Matrix.diagonal (fun _ : Fin 1 => (χ g : ℂ))

/-! ## The premise half (ρ-independent, at N = 1) -/

/-- **Premise form (the S half):** at `N = 1`, over
`Circle`, the stratum Boltzmann factor is
`AEStronglyMeasurable` for EVERY representation `ρ`,
every `β`, and every pair of layer data — because the
layer action vanishes identically (every plaquette is
a commutator in an abelian group). Content proves this
half; it is the half that makes the seat a
counterexample rather than a gap. -/
def N1BoltzmannAEStronglyMeasurable : Prop :=
  ∀ (ρ : Circle →* ↥(Matrix.unitaryGroup (Fin 1) ℂ))
    (β : ℝ) (u u' : LayerLink 1 → Circle),
    AEStronglyMeasurable
      (fun α : LayerSite 1 → Circle =>
        (Real.exp (-(layerAction ρ β α u u')) : ℂ))
      (Measure.pi fun _ : LayerSite 1 => n1μ)

/-! ## The character half (the M–L half) -/

/-- **Character form 1:** the wild character is not
measurable. Content route (lane STATUS): if it were,
its self-convolution against Haar would be a continuous
representative; the covering argument then forces the
ℚ-linear map to be a scalar, contradicting
`A 1 = 0 ∧ A ≠ 0`. -/
def WildCharacterNotMeasurable : Prop :=
  ∀ (A : ℝ →ₗ[ℚ] ℝ) (χ : Circle → Circle),
    A 1 = 0 → A ≠ 0 → IsWildCharacter A χ →
    ¬ Measurable χ

/-- **Character form 2:** the wild character is not
`AEStronglyMeasurable` — the same convolution argument
with an a.e. representative in place of a measurable
one (Haar's left invariance moves the a.e. equality
through the integral). -/
def WildCharacterNotAEStronglyMeasurable : Prop :=
  ∀ (A : ℝ →ₗ[ℚ] ℝ) (χ : Circle → Circle),
    A 1 = 0 → A ≠ 0 → IsWildCharacter A χ →
    ¬ AEStronglyMeasurable χ n1μ

/-- **Conclusion-failure form:** at the scalar
representation of a wild character, the W-2 pair's
conclusion fails outright — `repMatrix ρ` is not
`AEStronglyMeasurable` (its trace/entry is `χ` itself,
via composition with the continuous entry evaluation
at `d = 1`). This is Step 1 refuted at its output,
with Step 2 standing sound-but-starved beside it
(documented in the lane STATUS; no form here asserts
anything false about Step 2). -/
def N1PairConclusionFails : Prop :=
  ∀ (A : ℝ →ₗ[ℚ] ℝ) (χ : Circle → Circle)
    (ρ : Circle →* ↥(Matrix.unitaryGroup (Fin 1) ℂ)),
    A 1 = 0 → A ≠ 0 → IsWildCharacter A χ →
    IsScalarRep χ ρ →
    ¬ AEStronglyMeasurable (fun g : Circle => repMatrix ρ g)
        n1μ

/-! ## The capstone form -/

/-- **Capstone form — `Gate3WildLemma` is false at the
N = 1 seat:** there exist a wild character and its
scalar representation at which the frozen wild lemma,
instantiated at `G = Circle`, `d = 1`, `N = 1`,
`μG = n1μ`, does not hold. Together with
`N1BoltzmannAEStronglyMeasurable` (its conclusion's
negation, since the Boltzmann factor IS
AEStronglyMeasurable there) and the premise
`¬ Measurable (repMatrix ρ)` from
`WildCharacterNotMeasurable` transported along
`IsScalarRep`, this is the T1 form of the 2026-11-08
paper kill of the frozen W-2 shape. -/
def Gate3WildLemmaFalseAtN1 : Prop :=
  ∃ (A : ℝ →ₗ[ℚ] ℝ) (χ : Circle → Circle)
    (ρ : Circle →* ↥(Matrix.unitaryGroup (Fin 1) ℂ)),
    A 1 = 0 ∧ A ≠ 0 ∧ IsWildCharacter A χ ∧
      IsScalarRep χ ρ ∧
      ¬ Gate3WildLemma (μG := n1μ) (N := 1) ρ

end N1Seat

end ThetLogos
