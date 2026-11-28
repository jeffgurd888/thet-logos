import Mathlib.Tactic
import ThetLogos.BoltzmannShannonPin

/-!
# ThetLogos.NegativeDensityPin — negative energy density, registered (T5)

Working label only — naming is Zero's hand. Zero's seeing,
verbatim, 2026-11-26 18:37 EST: "negative energy density can
only mean maximal thermal entropy with 0 static charge."
Brick 0 fired by Zero's word, 2026-11-26 18:38 EST ("fire
this lane only"). Scope of record:
`~/workspace/your_files/negative-energy-density-pin-scope-DRAFT-2026-11-26.md`.

TIER: T5 as physics, NO CLAIM — under EVERY outcome of this
line, including total success. In the standard literature,
negative energy density names other configurations (Casimir,
squeezed states) that are not maximal-entropy states; this
pin tests Zero's identification inside a finite frame, and
establishes nothing about the literature's objects (L15, the
Composition Rule: the pin earns the word "identification"
only if the finite structures coincide, not because the
names match). The finite core is T1-or-kill, like every pin.
No dial moves; dials 0/4 under every outcome. No gravity
object is constructed, fed, or identified.

## The official statement (pinned verbatim at this brick)

**The density functional attains its negative extreme
exactly at the maximal-entropy, zero-charge configurations
— every negative-extreme configuration has maximal entropy
and zero charge, and every maximal-entropy zero-charge
configuration attains the negative extreme.**

Registered below as `nedExtremalCharacterization`, in
statement form only. Nothing about it is claimed in this
brick: Brick 1 computes a small exhibit, Brick 2 proves the
characterization on the registered seat class — or K-NED
fires.

## Registration decisions (frozen on the face at this brick)

- **The seat.** A finite seat of microstates `Ω` (a
  `Fintype`), following the Gibbs dialect of
  `ThetLogos.BoltzmannShannonPin`. A **configuration** is a
  weight function `p : Ω → ℝ` on the seat — the same object
  the in-tree Gibbs lane already works with. The thermal
  (Gibbs) configuration at energy landscape `E` and inverse
  temperature `β` is registered as `nedGibbsDist`.
- **The entropy functional is REUSED, not redefined.**
  `nedEntropy` is the in-tree Gibbs entropy
  (`gibbsEntropy`, from `ThetLogos.BoltzmannShannonPin`):
  `-∑ i, p i * Real.log (p i)`, with Mathlib's
  `Real.log 0 = 0` convention, so zero-weight terms vanish
  on their own.
- **Charge.** Each microstate carries an integer charge
  `q : Ω → ℤ`; a configuration's static charge is the
  weight-expectation `nedCharge q p = ∑ i, p i * (q i : ℝ)`,
  and `nedZeroCharge q p` is its vanishing.
- **The density functional, and why it has this shape.**
  Registered as `nedDensity q p = (nedCharge q p)^2 -
  nedEntropy p`: squared charge minus entropy. The shape is
  chosen openly, on the face: its negative extreme is the
  balanced state the seeing names — the value `-S` can only
  be approached as charge vanishes and entropy grows, and
  the global floor `-Smax` is attained, if anywhere, exactly
  at a maximal-entropy zero-charge configuration. Whether
  the extreme IS attained exactly there is the pinned
  statement above — Brick 2's charge — not this def's claim.
- **"Negative extreme" and "maximal entropy", as
  registered.** Both are global over all weight functions
  on the seat: `p` attains the negative extreme when
  `∀ r, nedDensity q p ≤ nedDensity q r`, and `p` has
  maximal entropy when `∀ r, nedEntropy r ≤ nedEntropy p`.
  Restricting the seat class (e.g. to normalised
  distributions) is a later brick's stated change, never a
  silent one.

## Kills pre-registered (armed by this registration, not fired by it)

- **K-NED** — if the density functional attains its
  negative extreme at any configuration that is not
  maximal-entropy, or not zero-charge — or if no
  maximal-entropy zero-charge configuration attains it —
  the identification is DEAD at the finite level, and the
  kill banks at the same rank as a proof. No re-aiming the
  functionals mid-line without a new scope and Zero's word.

## Walls named on the face

- **L15 (the Composition Rule)** rides verbatim from the
  scope: this pin tests an identification of finite
  structures; it borrows no authority from the literature's
  use of the same words.
- **S-1 does not govern here** — no centre is picked out.
  But if a later brick quietly turns the extremal
  configuration into a picked-out object, S-1's jurisdiction
  attaches and the brick dies on it.

## Brick 0's charge

Definitions and the pinned statement ONLY: 0 strict by
design. Names frozen at this brick: `nedGibbsWeight`,
`nedPartition`, `nedGibbsDist`, `nedEntropy`, `nedCharge`,
`nedZeroCharge`, `nedDensity`,
`nedExtremalCharacterization`.
-/

namespace ThetLogos

/-- **The Gibbs thermal weight of a microstate.** At energy
landscape `E : Ω → ℝ` and inverse temperature `β`, microstate
`i` carries the unnormalised Gibbs weight `exp (-β * E i)` —
the Gibbs Jump Pin's dialect: weights are exponentials of
minus `β` times energy, and everything thermal in this line
is built from this one factor. -/
noncomputable def nedGibbsWeight {Ω : Type*} [Fintype Ω]
    (E : Ω → ℝ) (β : ℝ) (i : Ω) : ℝ :=
  Real.exp (-β * E i)

/-- **The partition sum.** The total Gibbs weight of the
seat at `(E, β)` — the normaliser of the thermal
configuration, registered as its own object so later bricks
can speak about it without unfolding the sum. -/
noncomputable def nedPartition {Ω : Type*} [Fintype Ω]
    (E : Ω → ℝ) (β : ℝ) : ℝ :=
  ∑ i, nedGibbsWeight E β i

/-- **The Gibbs configuration.** The thermal weighting of
the seat, normalised: configuration `i ↦ exp (-β * E i) / Z`
with `Z = nedPartition E β`. This is the line's registered
thermal configuration — one configuration among all weight
functions, named so the bricks can ask where it sits
relative to the density functional's extreme. (No claim
that `Z ≠ 0` is made here; positivity of the weights is a
later brick's lemma, not this def's assumption.) -/
noncomputable def nedGibbsDist {Ω : Type*} [Fintype Ω]
    (E : Ω → ℝ) (β : ℝ) (i : Ω) : ℝ :=
  nedGibbsWeight E β i / nedPartition E β

/-- **The entropy functional — REUSED from the Gibbs lane.**
`nedEntropy p` is the in-tree Gibbs entropy of the weight
function `p` (`gibbsEntropy`, `ThetLogos.BoltzmannShannonPin`):
`-∑ i, p i * Real.log (p i)`. Registered under this line's
name so the pinned statement speaks in the pin's own frozen
vocabulary; the functional itself is the corpus's existing
one, not a redefinition. -/
noncomputable def nedEntropy {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) : ℝ :=
  gibbsEntropy p

/-- **The static charge of a configuration.** Each
microstate carries an integer charge `q : Ω → ℤ`; the
configuration `p` carries the weight-expectation of that
charge, `∑ i, p i * (q i : ℝ)`. This is the "static charge"
of the seeing: a property of the configuration as a whole,
read off its weights — not a charge located at any point. -/
noncomputable def nedCharge {Ω : Type*} [Fintype Ω]
    (q : Ω → ℤ) (p : Ω → ℝ) : ℝ :=
  ∑ i, p i * (q i : ℝ)

/-- **The zero-charge locus, as a predicate.** A
configuration is zero-charge when its static charge
vanishes exactly. The locus is registered as a `Prop` so
the pinned statement and K-NED both speak about the same
set of configurations. -/
def nedZeroCharge {Ω : Type*} [Fintype Ω]
    (q : Ω → ℤ) (p : Ω → ℝ) : Prop :=
  nedCharge q p = 0

/-- **The density functional.** Registered as squared
charge minus entropy:
`nedDensity q p = (nedCharge q p)^2 - nedEntropy p`.
The shape is a registration decision, stated openly in the
header: the functional's negative extreme is the balanced
state the seeing names — charge contributes a nonnegative
penalty that vanishes only on the zero-charge locus, and
entropy enters negatively, so the floor is reached, if
anywhere, at maximal entropy. Whether the floor is
attained exactly at the maximal-entropy zero-charge
configurations is the pinned statement below, NOT a claim
of this definition. -/
noncomputable def nedDensity {Ω : Type*} [Fintype Ω]
    (q : Ω → ℤ) (p : Ω → ℝ) : ℝ :=
  (nedCharge q p) ^ 2 - nedEntropy p

/-- **THE OFFICIAL STATEMENT, pinned as the line's target.**
The density functional attains its negative extreme exactly
at the maximal-entropy, zero-charge configurations: for
every configuration `p`, `p` is a global minimiser of
`nedDensity q` (the negative extreme: `∀ r, nedDensity q p
≤ nedDensity q r`) if and only if `p` is a global maximiser
of `nedEntropy` (`∀ r, nedEntropy r ≤ nedEntropy p`) and
`p` is zero-charge. Stated in statement form only; nothing
about it is claimed in this brick. Brick 2's charge is the
theorem — or K-NED, each a landing at the same volume. -/
def nedExtremalCharacterization {Ω : Type*} [Fintype Ω]
    (q : Ω → ℤ) : Prop :=
  ∀ p : Ω → ℝ,
    (∀ r : Ω → ℝ, nedDensity q p ≤ nedDensity q r) ↔
      ((∀ r : Ω → ℝ, nedEntropy r ≤ nedEntropy p) ∧
        nedZeroCharge q p)

end ThetLogos
