import ThetLogos.NavierStokesStatement

namespace ThetLogos

/-!
# ThetLogos.NavierStokesClaimPin — Navier–Stokes claim-tester pin (CT-0)

Board charter: **NO CLAIM.** Parts of the Clay Navier–Stokes problem
closed by this house: **0** — now, and after this line lands. This
module is the PIN of the claim-tester model commissioned by Jeff
2026-11-06 22:25 EST ("build the model that answers those three
questions from the statement"): given a candidate claim about the
Navier–Stokes problem, answer **from the pinned statement**
(`ThetLogos.NavierStokesStatement`, NS-1b, composing the frozen
NS-1a packages of `ThetLogos.NavierStokesDefs`)

1. **which alternative** does it purport to settle — (A), (B), (C),
   or (D);
2. **in which shape** — does its shape match the pin's shape for
   that alternative exactly (domain, viscosity regime, forcing
   regime, mode), and if not, which parameters mismatch;
3. **does it smuggle in the ¬C → A step** — does its derivation
   route pass through a negation step between alternatives, and is
   that step valid at the pin's quantifier shape.

This pin module contains DEFINITIONS ONLY: the claim descriptor,
the derivation-route descriptor, and the three question functions
as a frozen interface. The theorems that justify the interface are
CT-1 (`ThetLogos.NavierStokesClaimClassify`: Q1/Q2 as proved
classification, including the mismatch verdicts) and CT-2
(`ThetLogos.NavierStokesClaimSteps`: Q3 as proved non-entailment at
the level of logical shape, with explicit countermodels, plus the
exact fixed-ν status of every step). No theorem is stated or proved
here, and nothing here asserts anything about Navier–Stokes: the
model tests claim-SHAPES against the statement; it is not progress
on the problem.

## The shape the pin exposes

Read off `NavierStokesStatement`'s compositions (its header states
the composition choice on its face): each alternative quantifies
`ν` INSIDE its own `Prop` (`∀ (ν : ℝ), 0 < ν → …`), (A)/(B) fix
`f ≡ 0` exactly (`NSZeroForcing`), (C)/(D) range over all
admissible forcing (`NSForcingDataR3` / `NSForcingDataTorus`), (A)/(B)
are existence-shaped (`∀` admissible data, `∃` solution), (C)/(D)
breakdown-shaped (`∃` admissible data, `¬∃` solution), (A)/(C) live
on ℝ³, (B)/(D) on the torus ℝ³/ℤ³. A board claim (a claim to have
solved the Clay problem) is tested as the alternative it purports
to prove — `NSBoardStatement` is the disjunction, and proving any
one alternative settles it; there is no fifth shape.

## The step-status table is an interface, not a verdict

`nsStepStatus` below freezes the model's classification of every
negation step `¬src → tgt` between alternatives. Its entries are
DEFINITIONS at this pin; CT-2 carries the proofs that they are the
right entries:

- same-domain steps at the pin's regime (`quantifiedInside`) are
  `blockedByNuQuantification`: the step fails on the ν-quantifier
  alone — CT-2's countermodels grant even the zero-forcing
  admissibility inclusion and the steps still fail, because `¬C`
  as composed yields A's content at a single viscosity only, and
  `¬A` as composed yields C's witness at a single viscosity only,
  while both alternatives quantify over every `ν > 0`;
- cross-domain steps are `blockedByDomain` at every regime;
- same-domain steps at the `fixedGlobal` regime (Fefferman's
  ambient-`ν` reading: one fixed `ν > 0` shared by both sides) are
  `needsAdmissibilityAtFixedNu`: CT-2 proves each direction is pure
  logic GIVEN the inclusion `∀ f, NSZeroForcing f → admissible f`,
  and proves by countermodel that without the inclusion each
  direction fails even at fixed `ν`.

## CT-3 — the ¬A → C reading, fenced here as a remark

The ¬A → C direction stands in this line EXACTLY as the board's
Letter of 2026-11-06 holds it: a READING of the Clay text, NOT a
proved theorem, and no module in this line states it as a theorem
about the pin's `Prop`s. The reading's grounds, stated plainly:
Fefferman's preamble takes `ν > 0` as a given (the ambient reading),
and the zero forcing is (5)-admissible, so at a fixed `ν` a ¬A
witness is a C witness. Two fences ride with the reading wherever
it is mentioned in this line: (i) exhibiting `f ≡ 0` as
`NSForcingDataR3` inside Lean is analysis content beyond statement
grade (the NS-1b header's own caveat), so the inclusion is an
audit-level reading of the text, not a house lemma; (ii) under the
pin's composition as actually written (`∀ν` inside each `Prop`),
CT-2's shape analysis shows the ν-step blocks ¬A → C as well, even
granting the inclusion — so the reading needs BOTH the ambient-ν
reading AND the admissibility inclusion. NS-0's honesty clause
("¬A ⇒ C and ¬C ⇒ A hold") is the ambient-reading statement; the
NS-1b header already records that ¬C ⇒ A does not survive the
composition; CT-2 records the matching fact for ¬A ⇒ C. The pin's
statements themselves are untouched by any of this: they are the
Clay text as composed, and K-NS-1 does not fire on them.

## K-NS-1 discipline

Nothing in this line asserts that any alternative is non-vacuous,
and no existence content of any kind is stated or proved. The
countermodels of CT-2 are assignments to ABSTRACT shape predicates
(they refute inference FORMS); they assert nothing about the truth
values of `NSAlternativeA`–`NSAlternativeD`.

Honesty tiers in this file:
- **Definitions (no tier):** everything below. A definition
  asserts nothing.
- **NO CLAIM:** existence, smoothness, breakdown — untouched.
-/

/-- The four Fefferman alternatives, as claim targets. A board
claim is tested as the alternative it purports to prove (the board
statement is their disjunction; there is no fifth shape). -/
inductive NSAlt where
  | A | B | C | D
  deriving DecidableEq, Repr

/-- The spatial domain of a claim shape: ℝ³, or the torus ℝ³/ℤ³. -/
inductive NSDom where
  | r3 | torus
  deriving DecidableEq, Repr

/-- The viscosity regime of a claim shape: `fixedGlobal` — one
fixed `ν > 0` given once for all alternatives (Fefferman's
ambient reading of his preamble); `quantifiedInside` — `ν`
universally quantified inside each alternative (the pin's
composition in `NavierStokesStatement`). -/
inductive NSNuRegime where
  | fixedGlobal | quantifiedInside
  deriving DecidableEq, Repr

/-- The forcing regime of a claim shape: `zeroOnly` — the forcing
is fixed at `f ≡ 0` exactly (alternatives (A)/(B));
`allAdmissible` — the forcing ranges over all admissible forcing
of the domain (the (5) package on ℝ³, the (9) package on the
torus; the witness range of alternatives (C)/(D)). -/
inductive NSForcingRegime where
  | zeroOnly | allAdmissible
  deriving DecidableEq, Repr

/-- The mode of a claim shape: `existence` — for all admissible
data there is a smooth bounded-energy solution (alternatives
(A)/(B)); `breakdown` — for some admissible data there is none
(alternatives (C)/(D)). -/
inductive NSMode where
  | existence | breakdown
  deriving DecidableEq, Repr

/-- A candidate claim's shape descriptor: the alternative it
purports to settle, and the shape parameters the pin exposes —
domain, viscosity regime, forcing regime, mode. Q1 reads the
first field; Q2 reads the rest against `nsPinShape`. -/
structure NSClaimShape where
  alt : NSAlt
  dom : NSDom
  nu : NSNuRegime
  forcing : NSForcingRegime
  mode : NSMode
  deriving DecidableEq, Repr

/-- The domain of an alternative, as pinned: (A)/(C) on ℝ³,
(B)/(D) on the torus. -/
def nsAltDom : NSAlt → NSDom
  | .A => .r3
  | .B => .torus
  | .C => .r3
  | .D => .torus

/-- **The pin's shape for each alternative**, read off the
compositions in `NavierStokesStatement`: `ν` quantified inside,
(A)/(B) zero forcing and existence mode, (C)/(D) all-admissible
forcing and breakdown mode, domains per `nsAltDom`. This table
is the standard Q1/Q2 judge a candidate shape against. -/
def nsPinShape : NSAlt → NSClaimShape
  | .A => ⟨.A, .r3, .quantifiedInside, .zeroOnly, .existence⟩
  | .B => ⟨.B, .torus, .quantifiedInside, .zeroOnly, .existence⟩
  | .C => ⟨.C, .r3, .quantifiedInside, .allAdmissible, .breakdown⟩
  | .D => ⟨.D, .torus, .quantifiedInside, .allAdmissible, .breakdown⟩

/-- A single shape parameter on which a candidate shape can
mismatch the pin's shape for its purported alternative. Q2's
answer is a list of these; the empty list is an exact match. -/
inductive NSMismatch where
  | wrongNu | wrongDomain | wrongForcing | wrongMode
  deriving DecidableEq, Repr

/-- **Q2 (interface):** the list of shape mismatches between a
candidate shape and the pin's shape for its purported
alternative — the viscosity regime, domain, forcing regime, and
mode are compared field by field, in that order. -/
def nsShapeMismatches (s : NSClaimShape) : List NSMismatch :=
  let p := nsPinShape s.alt
  (if s.nu = p.nu then [] else [.wrongNu]) ++
    (if s.dom = p.dom then [] else [.wrongDomain]) ++
    (if s.forcing = p.forcing then [] else [.wrongForcing]) ++
    (if s.mode = p.mode then [] else [.wrongMode])

/-- **Q2 (interface):** does the candidate shape match the pin's
shape for its purported alternative exactly? -/
def nsShapeMatches (s : NSClaimShape) : Bool :=
  (nsShapeMismatches s).isEmpty

/-- **Q1 (interface):** the alternative a candidate shape matches
exactly, if any — `some a` when the shape is the pin's shape for
`a` (which forces `a` to be the purported alternative), `none`
when it matches no alternative as pinned. -/
def nsMatchedAlt (s : NSClaimShape) : Option NSAlt :=
  if nsShapeMatches s then some s.alt else none

/-- The verdict of Q1+Q2 on a candidate shape: an exact match
with the pin's shape, or the list of mismatches. -/
inductive NSClaimVerdict where
  | matchesPin : NSClaimVerdict
  | mismatch : List NSMismatch → NSClaimVerdict
  deriving DecidableEq, Repr

/-- **Q1+Q2 (interface):** classify a candidate shape against the
pin. `matchesPin` — the shape is exactly the pin's shape for its
alternative; `mismatch ms` — it is not, and `ms` names every
parameter on which it differs. CT-1 proves this classification
correct, including the headline mismatch verdict: a shape whose
viscosity regime is `fixedGlobal` matches NO alternative as
pinned (`wrongNu` is always among its mismatches). -/
def nsClassify (s : NSClaimShape) : NSClaimVerdict :=
  match nsShapeMismatches s with
  | [] => .matchesPin
  | ms => .mismatch ms

/-- One negation step in a purported derivation between
alternatives: the step that claims `tgt` from the NEGATION of
`src` (e.g. `⟨.C, .A⟩` is the ¬C → A step). -/
structure NSNegStep where
  src : NSAlt
  tgt : NSAlt
  deriving DecidableEq, Repr

/-- A derivation-route descriptor: `direct` settles its target
outright; `viaNeg s r` first passes through the negation step
`s`, then continues as route `r`. Rich enough to express any
route that passes through a negation-of-one-alternative →
another-alternative inference, which is exactly what Q3 reads. -/
inductive NSRoute where
  | direct : NSRoute
  | viaNeg : NSNegStep → NSRoute → NSRoute
  deriving DecidableEq, Repr

/-- The status of a negation step at a given viscosity regime,
as classified by this model (frozen interface; CT-2 carries the
justifying theorems — see the module header):

- `blockedByNuQuantification` — same domain, pin regime: the
  step fails on the ν-quantifier alone, even granting the
  zero-forcing admissibility inclusion (explicit countermodels).
- `blockedByDomain` — cross-domain: no viscosity regime repairs
  a step between ℝ³ and torus alternatives.
- `needsAdmissibilityAtFixedNu` — same domain, fixed-ν regime:
  the step is pure logic GIVEN the inclusion of zero forcing in
  the admissible class, and fails without it (countermodels).
- `degenerate` — `src = tgt`: no cross-alternative content. -/
inductive NSStepStatus where
  | blockedByNuQuantification
  | blockedByDomain
  | needsAdmissibilityAtFixedNu
  | degenerate
  deriving DecidableEq, Repr

/-- **Q3 (interface):** the status of a negation step at a given
viscosity regime. At the pin's regime every genuine
cross-alternative step is blocked — same-domain steps by the
ν-quantification, cross-domain steps by domain. -/
def nsStepStatus (reg : NSNuRegime) (s : NSNegStep) : NSStepStatus :=
  if s.src = s.tgt then .degenerate
  else if nsAltDom s.src ≠ nsAltDom s.tgt then .blockedByDomain
  else match reg with
    | .quantifiedInside => .blockedByNuQuantification
    | .fixedGlobal => .needsAdmissibilityAtFixedNu

/-- Is a step status a BLOCKED status at the pin's regime?
(`needsAdmissibilityAtFixedNu` never occurs at the pin's regime,
and `degenerate` is not a smuggled step — it is no step at all.) -/
def NSStepStatus.isBlocked : NSStepStatus → Bool
  | .blockedByNuQuantification => true
  | .blockedByDomain => true
  | .needsAdmissibilityAtFixedNu => false
  | .degenerate => false

/-- **Q3 (interface):** does this route pass through the ¬C → A
step, or its torus mirror ¬D → B — the headline smuggled step of
the board's Letter? -/
def nsRouteUsesNotCtoA : NSRoute → Bool
  | .direct => false
  | .viaNeg s r =>
      (s = ⟨.C, .A⟩ || s = ⟨.D, .B⟩) || nsRouteUsesNotCtoA r

/-- **Q3 (interface), general form:** does this route pass
through ANY negation step that is blocked at the pin's
quantifier shape? A route that does rests on an inference the
pinned statement does not license. -/
def nsRouteUsesBlockedStep : NSRoute → Bool
  | .direct => false
  | .viaNeg s r =>
      (nsStepStatus .quantifiedInside s).isBlocked || nsRouteUsesBlockedStep r

end ThetLogos
