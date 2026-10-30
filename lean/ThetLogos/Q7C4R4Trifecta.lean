import Mathlib.Tactic
import ThetLogos.Q7C4R4Post
import ThetLogos.KMSBridge
import ThetLogos.ViscousLine

/-!
# ThetLogos.Q7C4R4Trifecta — Q7CR-T0: the trifecta registration amendment

**Status: REGISTRATION ONLY — the assignment as data, leg-`Prop`s
stated as schemas over their missing objects, no proof attempted.
NO CLAIM. No board, no dial.**

Governing scoping: `scoping-q7c4r4-trifecta-2026-10-30.md` (§1's
registration form, §2's per-leg sort, §3's refutation, §4's kills
govern; K-Q7CR-T0 armed). This module is gated on landed Q7CR-0
(`ThetLogos.Q7C4R4Post`: `q7c4r4Q7` / `q7c4r4C4` / `q7c4r4R4` /
`q7c4r4Composite`), imported above, and speaks in its registered
factors' names.

## Jeff's assignment and glosses (verbatim, attributed, T5)

Jeff Gurd's trifecta assignment (Jeff, 2026-10-30, his words,
registered here, never revised) — four laws over three factors,
R⁴ carrying two, registered as DISTINCT assignments in §1 below:

- **Q⁷ → First Law:** "The 7-dimensional octonionic imaginary
  boundary governs internal degrees of freedom, non-commutative
  operator norm conservation, and microstate density."
- **C⁴ → Second Law:** "The cyclic Z₄ phase clock acts as the
  discrete generator for Tomita-Takesaki modular time. Phase
  transitions around the 4-clock break time-reversal symmetry at
  discrete steps, enforcing non-decreasing entropy across cyclic
  evolution."
- **R⁴ → Zeroth & Third Laws:** "Continuous Euclidean/Minkowski
  space ℝ⁴ provides the global thermal background frame required
  to define temperature equivalence (Zeroth) and the asymptotic
  zero-entropy vacuum state (Third)."

The sort beside the glosses (§2 of the scoping):

- "octonionic" = NO OBJECT in tree or pin — frontier,
  unpriceable, not a placeholder; it carries no finite content in
  this registration and no slot below stands in for it.
- "operator norm conservation" = a tautology gloss: under any
  automorphism / unitary evolution, norm conservation is
  automatic — a definitional truth, not a consequence, and not a
  leg's witness.
- The R⁴ legs are statements about the corpus's Minkowski seat
  (`q7c4r4R4`, i.e. `Minkowski := Fin 4 → ℝ` from
  `ThetLogos.WightmanAxioms`), NOT about continuum spacetime
  (the Item 6 fence, inherited).

## The C⁴ / Second-Law leg, strong form: REFUTED-AS-STATED

Recorded on the face, at full rank, so the literal reading can
never be re-spent as open. The C⁴ gloss's literal reading is
refuted by landed theorems of this corpus:

- **G1 (finite-order vs continuous flow).** A finite-order Z₄
  action does not generate the continuous modular flow except at
  tuned seats: the flow is a continuous one-parameter group and
  sees only spectral differences, so quarter-period sampling
  closes to Z₄ only under a measure-zero spectral lattice
  condition. The strong "discrete generator" reading is false in
  general.
- **G2 (stationarity).** `gibbsWeight_stationary` and
  `gibbs_kms_flux_stationary` (`ThetLogos.KMSBridge`, T1): the
  Gibbs state is exactly stationary under its modular flow. A
  flow that fixes its defining state cannot enforce that state's
  growth along the flow; and no group action, being reversible,
  enforces an arrow — the corpus's arrows live in steps, not
  flows.

The correspondence does NOT die with its gloss: assignment ≠
commentary. The assignment is Jeff's act; the gloss is his T5
prose about it, and T5 prose is refutable without touching the
act. What survives beside the refuted strong form:

- **W1 (the section):** the clock as a 4-point sampling/section
  of modular time at tuned seats — a real, falsifiable,
  seat-scoped claim; registered as a schema in §2
  (`SecondW1Section`).
- **W2 (the relocation):** the clock as the GRADING of an
  irreversible step with sectorwise-nonnegative defect — the
  corpus's arrow anatomy; its owned core is
  `ViscousLine.traceDefect_nonneg`. This is the leg's registered
  form (`LegSecondArrow`, §3).
- **W3 (the floor):** if W1 and W2 both die at their seats, the
  leg reverts to pure definition, labeled as such. W3 is named
  here as the floor; it is not a claim.

## The standing fence (verbatim, on the face)

**no outcome of any later brick promotes the assignment itself
to T1** — consequences are theorems or kills; the choice stays
Jeff's. A leg whose every testable consequence dies does not get
deleted — it reverts to pure definition, labeled as such, at
full rank.

## What is missing, named (the schemas' slots)

The tree's missing definition is T-ENT's: the entropy functional
the First and Third legs consume is T-ENT's to supply, and it
does not exist in the tree today. The other slots are named at
each leg in §3: Q7CR-2's spectrum, Q7CR-3's grading, a composite
step (Q7CR-5 family), and a contact step. No vocabulary is
invented to fill a slot (K-Q7CR-T0).
-/

namespace ThetLogos

/-! ## §1. The assignment as data (Jeff's act, in the tree's own hand) -/

/-- The three registered factors of Q⁷C⁴R⁴, as registration
labels (the factors themselves are `q7c4r4Q7` / `q7c4r4C4` /
`q7c4r4R4` in `ThetLogos.Q7C4R4Post`). -/
inductive TrifectaFactor where
  | Q7
  | C4
  | R4
  deriving DecidableEq, Repr

/-- The four laws of Jeff's assignment, as registration labels. -/
inductive TrifectaLaw where
  | First
  | Second
  | Zeroth
  | Third
  deriving DecidableEq, Repr

/-- **Jeff's trifecta assignment, as data.** Q⁷ ↦ [First],
C⁴ ↦ [Second], R⁴ ↦ [Zeroth, Third]. A definition — Jeff's act
recorded in the tree's own hand — not a theorem and not a claim. -/
def trifectaAssignment : TrifectaFactor → List TrifectaLaw
  | .Q7 => [.First]
  | .C4 => [.Second]
  | .R4 => [.Zeroth, .Third]

/-- **The assignment, field by field.** The four assignments as
four DISTINCT fields, separately readable — in particular the
two R⁴ fields (`legR4Zeroth`, `legR4Third`) are distinct, so no
later brick can spend one R⁴ leg's evidence on the other. -/
structure TrifectaAssignment where
  /-- Q⁷'s law: the First. -/
  legQ7First : TrifectaLaw
  /-- C⁴'s law: the Second. -/
  legC4Second : TrifectaLaw
  /-- R⁴'s first law: the Zeroth (distinct from `legR4Third`). -/
  legR4Zeroth : TrifectaLaw
  /-- R⁴'s second law: the Third (distinct from `legR4Zeroth`). -/
  legR4Third : TrifectaLaw

/-- **The registered assignment record.** Jeff's assignment in
its field-by-field form: Q⁷ ↦ First, C⁴ ↦ Second, R⁴ ↦ Zeroth,
R⁴ ↦ Third. -/
def trifectaAssignmentRecord : TrifectaAssignment where
  legQ7First := .First
  legC4Second := .Second
  legR4Zeroth := .Zeroth
  legR4Third := .Third

/-! ## §2. The four leg-Props, stated as schemas

Each leg-Prop below quantifies over its missing object as a
VARIABLE (the BSD-pin pattern): the schema is statable today,
honestly, in owned vocabulary; the object that would instantiate
it is named in the leg's docstring and is a later brick's to
supply. None of the four is proved here, and none is a vacuous
pin. -/

/-- **Leg 1 — First-Law capacity, as a schema** over a functional
`S : (Fin 7 → ℂ) → ℝ` on the Q⁷ factor: every state's value under
`S` is at most `Real.log 7`.

Registered form: `log 7`, the complex count. The fork is recorded
here, on the face: `log 14` is the same bound read under the raw
real dimension of the DQ1-realified factor; T0 registers the
`log 7` form, and neither reading may be used silently in place
of the other. The `log 448` equivocation is pre-caught here:
448 is real-dimension bookkeeping (`14 · 8 · 4`) for the full
composite, NOT a microstate capacity, and no dossier may spend
it as this leg's content.

What is missing: `S` itself, and the state predicate on
`Fin 7 → ℂ` that the intended quantification runs over — the
entropy functional is T-ENT's to supply (T-ENT is the tree's
missing definition; see the header), and the Q⁷ factor's state
vocabulary comes with it. -/
def LegFirstCapacity (S : (Fin 7 → ℂ) → ℝ) : Prop :=
  ∀ ρ : Fin 7 → ℂ, S ρ ≤ Real.log 7

/-- **W1, the C⁴ leg's section form, as a schema** over two
variables on the C⁴ factor: a quarter-period sample
`quarterSample` of a modular flow, and a shift `shift`. The
section claim is that the sample IS the shift, and that the
shift has the Z₄ order (fourfold iterate = identity). The flow
itself, its seat, and the spectral lattice condition under which
sampling could close are NOT owned objects on the composite
today; the instantiated form awaits Q7CR-0's seats and Q7CR-2's
spectrum. Seat-scoped: a failure at a seat kills W1 at that seat
only. -/
def SecondW1Section
    (quarterSample shift : (Fin 4 → ℂ) → (Fin 4 → ℂ)) : Prop :=
  quarterSample = shift ∧
    ∀ x : Fin 4 → ℂ, (shift ∘ shift ∘ shift ∘ shift) x = x

/-- **Leg 2 — Second-Law arrow, W2 form, as a schema** over a
stated step's sector data: for each C⁴ character sector
`j : Fin 4`, a rate family `lam j` and a weight family `w j` on
a `Fin N` seat, at step parameter `t`. The claim is sectorwise
nonnegativity of the defect, the defect taken in the corpus's
owned form, `ViscousLine.traceDefect` (whose landed
`traceDefect_nonneg` is the owned core: at the diagonal seat the
step's defect is nonnegative under its stated hypotheses).

What is missing: the grading object itself (Q7CR-3's to supply)
and a composite step (Q7CR-5 family) whose sector data would
instantiate `lam` and `w`; the hypotheses under which
`traceDefect_nonneg` applies are part of that later
instantiation. The strong form of this leg is NOT registered
here — it is recorded as REFUTED-AS-STATED in the header. -/
def LegSecondArrow {N : ℕ} (lam : Fin 4 → Fin N → ℝ) (t : ℝ)
    (w : Fin 4 → Fin N → ℝ) : Prop :=
  ∀ j : Fin 4, 0 ≤ traceDefect (lam j) t (w j)

/-- **Contact-compatibility, as a schema** over a stated contact
step: states `ρ`, `σ` (matrices on a `Fin N` seat) are
contact-compatible under `step` for the operator `K` exactly
when `step` drives the pair to a COMMON Gibbs state
`gibbsState K β` (`ThetLogos.KMSBridge`) at a single `β`. -/
def ContactCompatible {N : ℕ}
    (step : (Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ) →
      (Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ))
    (K : Matrix (Fin N) (Fin N) ℂ)
    (ρ σ : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∃ β : ℝ, (step (ρ, σ)).1 = gibbsState K β ∧
    (step (ρ, σ)).2 = gibbsState K β

/-- **Leg 3 — Zeroth-Law contact form, as a schema** over a
stated contact step: contact-compatibility (per
`ContactCompatible`) is TRANSITIVE.

The weak form of this leg — "same temperature" as the kernel of
a stated β-functional, an equivalence relation by construction
for any function whatsoever — is named here as REFUSED-as-a-test
(tautological): it witnesses nothing and is not registered.
What is missing: the contact step itself, a stated equilibration
step on the composite (latest in the dependency order, behind
the Q7CR-5 family); no owned composite step object exists today
to instantiate `step`. -/
def LegZerothContact {N : ℕ}
    (step : (Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ) →
      (Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ))
    (K : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ ρ σ τ : Matrix (Fin N) (Fin N) ℂ,
    ContactCompatible step K ρ σ → ContactCompatible step K σ τ →
      ContactCompatible step K ρ τ

/-- **Leg 4 — Third-Law finite form, as a schema** over a
functional `S` and the Gibbs family of a stated operator `K`:
`S (gibbsState K β)` tends, as `β → ∞`, to `Real.log` of `K`'s
ground degeneracy (`groundDeg`, a variable: the degeneracy
object and its certification are Q7CR-2's spectrum work).

What is missing: `S` — the entropy functional is T-ENT's to
supply (the tree's missing definition; see the header) — and
`K`'s certified ground degeneracy. -/
def LegThirdFinite {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ → ℝ)
    (K : Matrix (Fin N) (Fin N) ℂ) (groundDeg : ℕ) : Prop :=
  Filter.Tendsto (fun β : ℝ => S (gibbsState K β)) Filter.atTop
    (nhds (Real.log (groundDeg : ℝ)))

/-- **Leg 4 — the strong form, recorded as a schema beside the
finite form:** the limit is `0` if and only if the ground space
is one-dimensional (`groundDeg = 1`). Genuinely falsifiable per
seat: at an operator with `groundDeg > 1` the strong form fails
there and the leg survives only in the degeneracy form
(`LegThirdFinite`), recorded at full rank. -/
def LegThirdFiniteStrong {N : ℕ}
    (S : Matrix (Fin N) (Fin N) ℂ → ℝ)
    (K : Matrix (Fin N) (Fin N) ℂ) (groundDeg : ℕ) : Prop :=
  (Filter.Tendsto (fun β : ℝ => S (gibbsState K β)) Filter.atTop
    (nhds 0)) ↔ groundDeg = 1

/-! ## §3. The correspondence, at the registered forms -/

/-- **The Trifecta Correspondence, as registered (unproved).**
A schema over the objects the later bricks supply: the
assignment holds as registered in §1 (its defining property,
stated plainly as the four list equalities), AND the four
leg-Props hold at their registered forms — `LegFirstCapacity`
at the `log 7` form, `LegSecondArrow` in the weakened W2 form
(the strong form stands REFUTED-AS-STATED on this module's
face), `LegZerothContact` in the contact form,
`LegThirdFinite` in the degeneracy form.

The supplied objects, named: the two functionals `S₇` and `S`
are T-ENT's to supply; `lam` / `w` await Q7CR-3's grading and a
composite step (Q7CR-5 family); `step` is the contact step;
`K` and `groundDeg` await Q7CR-2's certified spectrum. Stated
only: no proof is attempted or asserted in this module, and —
per the standing fence on this module's face — no outcome of
any later brick promotes the assignment itself to T1. -/
def TrifectaCorrespondence {N : ℕ}
    (S₇ : (Fin 7 → ℂ) → ℝ)
    (lam : Fin 4 → Fin N → ℝ) (t : ℝ) (w : Fin 4 → Fin N → ℝ)
    (step : (Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ) →
      (Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ))
    (K : Matrix (Fin N) (Fin N) ℂ)
    (S : Matrix (Fin N) (Fin N) ℂ → ℝ) (groundDeg : ℕ) : Prop :=
  (trifectaAssignment .Q7 = [.First] ∧
    trifectaAssignment .C4 = [.Second] ∧
    trifectaAssignment .R4 = [.Zeroth, .Third]) ∧
  LegFirstCapacity S₇ ∧ LegSecondArrow lam t w ∧
    LegZerothContact step K ∧ LegThirdFinite S K groundDeg

end ThetLogos
