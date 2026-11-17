import Mathlib.Tactic
import ThetLogos.ThermoelectricSeat

namespace ThetLogos

/-!
# ThetLogos.OGPin — OG-0, the pin (bench position 17)

**Commission:** Zero's tap 2026-11-08 18:15 EST (QUEUE.md position
17), on the pricing of `og-scope-2026-11-08.md` §5. Built under the
parent resequence of 2026-11-11. The name **OG** is Zero's coinage,
carried exactly as given; the letters are NOT expanded into words
anywhere in this module — an expansion would be a reading installed
by the bench, and naming is Zero's hand.

## Face declarations (read before anything below)

- **This module is a PIN.** It contains definitions and frozen
  statement forms only: **no theorems, no axioms, no proofs.**
  0 strict, BY DESIGN. It freezes names and forms so that OG-1
  (bench position 18) proves against a target that cannot move.
- **PRE-REGISTERED DIAL-INELIGIBLE.** Dial 2 = 0 before this pin,
  0 after it, and 0 on every outcome of OG-1. **NO CLAIM.**
- **The declaration is Register-A design, carried as a
  postulate-bucket datum.** The bucket is DOCUMENTATION: the
  declaration below is recorded in this header and embodied in
  the `OGDatum` structure's shape. It is NOT a Lean `axiom`, and
  nothing in this module can be cited as a hypothesis by any
  proof. A declaration is design, not a result.
- The identity reading of OG ("gravity is the unity datum",
  "gravity is this read") remains Register B in full: underived,
  and unaffected by the primitive's declaration. Declaring the
  primitive named unity does not derive that gravity *is* it.

## The declaration of record (Register A, T2-design bucket)

Zero, 2026-11-08 18:02 EST, verbatim:

> **"gravity's primitive is unity."**

Delivered while the OG scoping was in flight; it takes the
Register-A side of the register fork **for the primitive**: Gate B
is no longer undeclared. What the declaration buys (scoping §4,
exactly): provenance at the declaration door (D2-0 re-graded
PASS-AS-DESIGN / DIAL-INELIGIBLE); ground to formulate on (the
three statement shapes F1–F3 below); a definite audit target.
What it does NOT buy: no identity, no response law, no carrier
beyond this pin's datum form, no dial motion. The Dial-2 event is
unchanged: **a derived test-body response law surviving P-D2**
(D2-0..D2-6, all seven, at a predeclared scope).

## Source text (Zero verbatim, 2026-11-08 17:33–17:55 EST; scoping §0)

> (1) "I want to say that the gravity I feel is more of a density
> issue than magnetism, maybe spectral density muon and gluon or
> gamma. I am trying to think of how weight is created and it's a
> thermal density issue"
>
> (2) "matter and energy are by products of thermal charge
> separation over entropy"
>
> (3) "gravity is the unity"
>
> (4) "the equal but opposite of being"
>
> (5) "our exact gravity is the sun total of thermal charge
> separation at the intersection" — ruled by Zero to read BOTH
> ways in duality: sun AND sum.
>
> (6) "our existences' keel is our gravity=sum total of thermal
> charge separation from the sun held in Electric/field loops"
>
> (7) "that electric vortex loop that creates the magnetic field
> at that 8.∞" (the mark 8.∞ is unresolved)
>
> (8) "your saying it's our spin 2 working against our ground
> state and the effect we feel is from the electroweak" (Zero's
> synthesis; attribution corrected in chat at the time: this line
> is Zero's, not BONES's).

Component grades (scoping §2, summary): (a) density sourcing NOT
STATEABLE as a source, its ground-state form DEAD ON EXISTING
DATA (K-OG-SQUEEZE); (b) separation landed mathematics, generation
NOT STATEABLE, and the seat's conservation law fences the literal
reading; (c) unity NOT STATEABLE as an object — the name of the
joint-spec target, now also declared ground; (d) pair structure
STATEABLE as landed mathematics, NOT STATEABLE as a gravity
ingredient; (e) sum reading REFUTED on the only seat that owns its
words (K-OG-SUM, fired), sun reading NOT STATEABLE, the duality
ruling standing as Zero's naming act at T5; (f) loops landed, keel
and containment join NOT STATEABLE; (g) PARTIAL as mathematics
(finite Maxwell), NOT STATEABLE as a gravity component; (h)
spin-2 / ground state / felt effect NOT STATEABLE ×3. Against the
D2 teeth OG as specified fails D2-1..D2-6, with D2-0 re-graded by
the declaration (scoping §3).

## The pinned datum and the declared read

- **`OGDatum`** (below): over the thermoelectric seat's own site
  conventions, ONE structure carrying symmetric nonnegative
  weights `w` and a thermal field `θ`. Body-side and
  background-side data are **one datum**: the structure has no
  factorization fields. That absence is the declared unity made
  structural rather than verbal — it is a design choice of this
  pin (bench proposal under Zero's standing design call,
  scoping §6 decision 2; flagged for his ruling at integration).
- **`ogRead`** (below): the DECLARED response read,
  `ogRead D := teDirichlet D.w D.θ` — the TE seat's landed
  Dirichlet pairing `∑ i, teCharge w θ i * θ i`
  (`ThermoelectricSeat`, TE-T4). Chosen because the scoping
  (§2(e)) names the pairing as the seat's live content, where
  the total is its dead content: `∑ i, teCharge w θ i = 0`
  identically (TE-T3, landed T1). The read is declared as part
  of the design (Register A). It is labeled a **read** on its
  face: it is not a derived response law, and K-OG-PROXY /
  K-OG-SHADOW stand armed over any presentation of it as one.

## The frozen forms (OG-1's targets; names frozen here)

In the `TolmanExhibitPin` → `TolmanCharForm` pattern: OG-1 proves
theorems OF these types, or reports the failure as the result.

- **F1 — `OGUnityForm`**: the unity datum with its declared read,
  at characterization grade (scoping §4 F1 + §5 OG-1 targets
  (i)+(ii)): over a symmetric nonnegative weight with at least
  one live edge, the read vanishes exactly on the fields constant
  on the weight's support (equilibrium = constancy on the
  support), and some nonconstant field has nonzero read
  (non-vacuity, both directions). K-OG-FIAT arms over any
  postulated (underived) discharge; K-OG-VAC over collapsed
  witnesses.
- **F2 — `OGFactorizationForm`**: the factorization fence
  (scoping §4 F2): for every ordered-pair factorization of the
  datum's own field, `θ = φ + ψ`, constancy of one side on the
  support collapses the read's `θ`-dependence to the other side
  alone. The scoping's either-direction clause stands: if OG-1's
  proof fails, the failure is information the house does not
  currently own, and fires no kill.
- **F3 — `OGEquilibriumForm`**: the equilibrium fence (scoping
  §4 F3 + §5 OG-1 target (iv)): at equilibrium the datum's
  thermal content is constant-field on the support — the Tolman
  rigidity restated over the declared datum, the discipline that
  keeps any future OG equilibrium claim honest. K-OG-TOLMAN arms
  over any equilibrium formulation claiming more.

## The kill registry (K-OG-*, as armed in the scoping §5)

- **K-OG-SUM — FIRED at read level, 2026-11-08, at zero new
  strict.** The sum reading of source line (5) is dead:
  `∑ i, teCharge w θ i = 0` identically, for every thermal field
  (TE-T3, landed T1: `teCharge_sum_eq_zero`). A total of a
  conserved separation is the conservation law itself and carries
  no information; the live content of the seat is in the
  distribution, never in the total. This kills the *reading*, not
  Zero's sentence: the sun reading and the duality ruling stand.
- **K-OG-SHADOW** (armed) — fires on any OG response law,
  exhibit summary, or post that routes the response through the
  Poisson / thermal-charge channel: by SHADOW-TEST-1 (landed T1)
  that channel is total-mass-blind, so the response cannot be
  gravity's (D2-3 / D2-4).
- **K-OG-TOLMAN** (armed) — fires on any OG formulation stated
  over thermal equilibria that claims nonconstant content: the
  landed characterization forces the slope condition at one
  global λ; equilibrium forms are constant-field.
- **K-OG-SQUEEZE** (armed; K-SM-SQUEEZE inherited) — fires on
  any OG formulation making weight a functional of the
  ground-state spectrum or ground-state thermal density:
  MICROSCOPE `η(Ti, Pt) ≤ 2.7 × 10⁻¹⁵`, coupling room
  `κ ≲ 10⁻¹⁰–10⁻¹⁴`, i.e. none. Prepared-state formulations are
  not this kill's target and must say so on their face to pass it.
- **K-OG-PROXY** (armed on OG-0 / OG-1) — fires if the declared
  primitive, the unity datum, or the exhibit's response read is
  ever named or presented as a gravity object, a response law,
  an identity, or Dial evidence.
- **K-OG-FIAT** (armed on OG-1) — fires if the characterization
  (F1) is postulated rather than derived.
- **K-OG-VAC** (armed on OG-1) — fires if F1's witnesses
  collapse: if the read cannot differ where the form requires
  difference, the exhibit is vacuous and does not ship.
- **K-OG-DIAL** (standing) — fires on any text presenting the
  declaration, the scoping, this pin, or OG-1's landing as
  motion of Dial 2.


## Spec note 1 — Trinity of actions (Zero, 2026-11-08 18:18 EST, VERBATIM)

> "we need to layer the thermal entropy field into Trinity of
> actions. identity/friction/confinement the balance of action is
> gravity"

Carriage: part of OG's DECLARED structure — a Trinity of actions
(identity / friction / confinement) with the thermal entropy
field layered into it, gravity designated as the balance of
action — Register-A designation content beside the 18:02
declaration, verbatim, unexpanded, uninterpreted. Effect: NONE on
the F1–F3 statement forms; no theorems added to OG-0 or OG-1.

## Spec note 2 — Trinity of primitives (Zero, 2026-11-08 18:50 EST, VERBATIM)

> "So our Trinity of primitives is time unity and heat"

Carriage: a Trinity of PRIMITIVES (time / unity / heat),
Register-A architecture content, verbatim, unexpanded,
uninterpreted. **Status precision, preserved on this face — the
three primitives do NOT stand at the same documentary rank, and
this pin does not flatten them:** unity was DECLARED at 18:02
("gravity's primitive is unity"); time was DEFINED in-ideology at
18:46 — Zero's words: "time is a prediction of probability of
Thermaldynamics"; heat is NAMED to primitive rank by the 18:50
line itself. Effect: NONE on the F1–F3 forms; no theorems.
Documentation only.

## Spec note 3 — the composition (Zero directed the composition; ratified verbatim "perfect", 2026-11-08 18:56 EST)

Carried as Register-A design notation, EXACTLY as ratified.
NO CLAIM, no theorem content:

- Action vector A = (I, F, C): identity / friction / confinement.
- Barycentric projection Pi(A) = (I/(I+F+C), F/(I+F+C),
  C/(I+F+C)) in Delta^2.
- Sierpinski weaving through the primitives time/unity/heat:
  Phi_{n+1} = (S_T Phi_n + S_U Phi_n + S_H Phi_n)/3;
  Phi_inf = lim Phi_n.
- Gravity G = M(Phi_inf) = (1/3, 1/3, 1/3), the Morley center of
  the woven limit triangle.
- Residual rho = Phi_inf - G (glossed in Zero's line of 18:48
  EST: a residual is negative time in the making).

Effect: NONE on the F1–F3 forms; no strict added to OG-0 (0 by
design) or OG-1. Documentation only.

## Spec note 4 — the IFS formal skeleton (Zero adopted the audited skeleton, 2026-11-08 19:01 EST, "yes" as audited)

Carried as Register-A design content, WITH the audit's repairs
applied and the audit on the face:

- Object: Gcal = (Delta^2, {S_T, S_U, S_H}, mu_inf, b(mu_inf),
  rho); S_i(x) = lambda*x + (1-lambda)*v_i contractions toward
  the Time/Unity/Heat vertices; W(mu) = sum_i p_i (S_i)_# mu
  with weights (p_T, p_U, p_H), p_T + p_U + p_H = 1, NOT frozen
  at 1/3; mu_inf = lim W^n(delta_{x0}) (Hutchinson
  existence/uniqueness cited as literature, not corpus).
- Residual REPAIRED to the single definition
  rho = b(mu_inf) - (1/3, 1/3, 1/3). **The pasted text's earlier
  definition (rho = b(mu_inf) - G with G := b(mu_inf)) is
  DISCARDED as vacuous — it is NOT carried here.** On the face:
  at equal weights and symmetric vertices rho = 0 by symmetry;
  rho becomes informative only off-symmetry.
- "Morley center" = Zero's NAME for the barycenter functional b
  (Option A of the audit); naming, not a derivation step.
- Tier on the face: mass-blind by construction; no metric,
  response law, or test body; NOT a gravity object under the
  D2 audit; Dial 2 = 0; the action->gravity negative
  (2026-11-08) stands untouched.

Effect: NONE on the F1–F3 forms; no strict added to OG-0 or
OG-1. Documentation only.

## Spec note 5 — heat-confinement (HC-1; Zero's claim 2026-11-08 20:40 EST, VERBATIM)

> "you can't have heat without confinement"

Source scoping: `heat-confinement-scope-2026-11-08.md`. Carried
as Register-A / T5 design content WITH the scoping's verdicts on
the face, exactly:

- **K-HC-TRIVIAL FIRED** (finiteness reading true by
  construction — confinement smuggled into the seat definition).
- **K-HC-FREE FIRED at read level** (grounding reading FALSE at
  the closed ThermoelectricSeat, TE-T2).
- Physics form corrected by one word: no SUSTAINED heat without
  confinement ("keep", not "have").
- Sustainment/dynamics form NOT STATEABLE in-corpus (no
  unconfined thermal seat exists; building one is the
  MQ3/Minlos FRONTIER wall).
- HC-3 NOT PRICED — do not enroll. HC-2 (optional citation
  assembly) is NOT fired — awaits Zero's separate word.

This note is HC-1 (band S, 0 strict): documentation only; no
change to the F1–F3 forms.

## Spec note 6 — squeeze / compression design lines (Zero's word "go", 2026-11-08 23:16 EST)

Two lines forwarded as DESIGN CONTENT, verbatim, uninterpreted:

- Line 1 (Zero, 2026-11-08 22:05 EST): "squeezing a vacuum
  creates gravity"
- Line 2 (Zero, 2026-11-08 23:11 EST, his time-mark carried):
  "11:11 compression is the missing link in gravity engine"

Tier on this note's face: Register-A / T5 design content — the
programme's stated mechanism-bet beneath the Gate B primitive
(gravity's primitive is unity, declared 2026-11-08 18:02 EST).
IDENTITY GRADING STANDS ON THIS FACE: as an identity the squeeze
claim is NOT STATEABLE in the corpus and NOT an established
result; its recorded neighbourhood (pressure itself gravitates in
Einstein's equations; Casimir squeeze is electromagnetic;
Kelvin-Helmholtz compression heating) is neighbourhood, not
derivation. Documentation only; F1–F3 forms unchanged.
Dial 2 = 0.

## Spec note 7 — heat<->cold design duality (cold-heat-duality-scope-2026-11-09.md §5, AS AMENDED by its §7)

Both of Zero's lines, verbatim:

- (2026-11-09 08:45 EST) "if heat is a primitive and it pushes
  cold must also be a primitive that pulls. is cold gravity"
- (2026-11-09 08:49 EST) "if heat is alone it must have two
  actions push and pull -1 +1"

Design content filed: HEAT and COLD stand in this dossier as a
primitive duality of directions. Heat pushes: expansion,
pressure, spread toward uniformity. Cold pulls: contraction,
densification, concentration on the ground. The cold direction
is the same design neighbourhood as Note 6's lines — compression
and densification are what the cold direction means here.

**The grading travels attached — read no further without it:**
the identity "cold is gravity" is **KILLED** (K-COLD-GRAVITY,
fired 2026-11-09 at read level). Cold is a state variable, not
an agent; and thermal energy itself gravitates, so a heated body
pulls negligibly *more*, not less — the identity's sign is
backwards. This note does **not** stand behind the identity,
does not amend Gate B (gravity's primitive is UNITY,
2026-11-08), and seats no second gravity primitive
(K-COLD-SEAT). The contraction language is design language; its
use as evidence of a physical pull is killed separately
(K-COLD-PROXY).

**Framing-invariance ruling (parent, on the face):** the
two-primitive reading (08:45) and the one-primitive-± reading
(08:49) buy the SAME mathematics — one temperature/β axis, two
directions along it (heating: expansion, disordering,
uniformization — COLD-3's end; cooling: concentration, ordering
— COLD-1's end). The difference is Register-A bookkeeping only.
No brick changes price, statement, or order under either
framing.

**Registered tension (FA-4b, rides with both framings):** the
"must" is a design preference, not a theorem. The corpus holds a
proved ONE-WAY law — FA-4b, the finite H-theorem: entropy's
drift does not reverse. A lone primitive with symmetric ±
actions is therefore a bet against the second law's shape; at
our seats the pull direction exists as a DRIVEN process
(cooling/compression done to a system), not as the system's own
drift. COLD-1's concentration is a statement about the Gibbs
WEIGHTS as β varies — a comparison across equilibria — not a
claim that a system spontaneously pulls itself cold.

**Formal residue** (priced in the duality scoping §4; every
brick pre-registered dial-ineligible): COLD-0 documentation pin
· COLD-1 cold-limit ground-state concentration (M, est. 10–18
strict) · COLD-2 β-monotonicity of entropy and mean energy (M,
est. 8–16 strict) · COLD-3 hot-limit uniformization (S, est.
3–7 strict) — bench positions 27–30. These are theorems about
finite Gibbs weights — push and pull *in the seat of a state*,
at the two ends of the temperature axis. No reading of them as
gravity, a force, or a metric is licensed by this note or by
the bricks.

**Carry-condition strain, DECLARED rather than forced:** the
dossier's design-note form carries no dedicated field for an
attached kill, so K-COLD-GRAVITY rides in this note's body
(above) instead of a form field, exactly per the duality
scoping's §5 carry-condition check; if the parent rules that
insufficient, the note returns for re-form rather than shipping
without the kill attached. F1–F3 forms unchanged.

## Spec note 8 — design language (Zero's word "design language og", 2026-11-09 08:56 EST)

DOCUMENTATION-ONLY design content (Register A / T5); F1–F3 forms
unchanged. The relayed vacuum-response line, carried as DESIGN
LANGUAGE with attribution and audit attached, UNMERGED:

- The line (Zero relaying an UNNAMED outside voice, 2026-11-09
  08:54 EST, verbatim incl. spelling): "Planck vaccum response
  medium creates time and gravity. someone said". Attribution
  on the face: NOT Zero's coinage — an outside voice he relayed
  and then directed into the dossier as design language.
- The audit travels attached (parent grading, 2026-11-09): the
  claim's respectable ancestor is Sakharov induced gravity
  (1967); as a corpus claim it is NOT STATEABLE — the corpus
  owns no vacuum object at any seat (the same wall the squeeze
  line hit) — and "creates time" sits in DECLARED TENSION with
  Zero's own Trinity of primitives (Note 2), where TIME is a
  declared primitive, not a created thing. Both the design
  language and the tension stand in this note; neither is
  smoothed into the other. Dial 2 = 0; NO CLAIM. The corpus's
  proved neighbour is a STATE's response (modular-flow clock
  material; TCS-T1 beta-response; COLD-2 queued) — response of
  a state, not of a vacuum; this note cites that neighbour as a
  POINTER ONLY, never as the claim restated.
- NOT PART OF THE DOSSIER:
  `~/workspace/your_files/response-vacuum-response-claim-2026-11-09.md`
  (a draft response text; Zero's to use or not) — not folded in.
-/

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- **The OG datum — PINNED FORM (Register A, declared design).**

The declared primitive's design form, in the exhibit pattern: over
the thermoelectric seat's site type `V`, ONE datum carrying a
symmetric nonnegative weight function `w` and a thermal field `θ`.
There are deliberately **no body/background factorization fields**:
body-side and background-side data are one datum, which is what
"unity" declares, made structural. An inhabitant of this structure
is a *choice* of seat data; the structure itself asserts nothing
about any physical system. NO CLAIM; dial-ineligible; Dial 2 = 0. -/
structure OGDatum (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V] where
  /-- The seat weights (the background side and the body side,
  carried as one datum — no split exists to name). -/
  w : V → V → ℝ
  /-- Weights are nonnegative. -/
  w_nonneg : ∀ i j, 0 ≤ w i j
  /-- Weights are symmetric. -/
  w_symm : ∀ i j, w i j = w j i
  /-- The thermal field on the seat. -/
  θ : V → ℝ

/-- **The declared response read (Register A — a READ, not a law).**

`ogRead D := teDirichlet D.w D.θ`, the thermoelectric seat's landed
Dirichlet pairing of the separated charge against the thermal
field, `∑ i, teCharge w θ i * θ i`. Declared as part of the OG
design at this pin. It is NOT a derived response law: no test body,
no attraction, no fall is stated or implied, and the seat's total
charge is identically zero (TE-T3) — the read lives in the
distribution, never in the total (K-OG-SUM). K-OG-PROXY and
K-OG-SHADOW stand armed over any presentation of this read as a
gravity object, a response law, an identity, or Dial evidence. -/
def ogRead (D : OGDatum V) : ℝ :=
  teDirichlet D.w D.θ

/-- **Equilibrium of the datum (pinned predicate).** A datum is at
equilibrium when its thermal field is constant across every live
edge of its weight — constant-field on the support. This is the
only equilibrium notion OG-1 may use; any future equilibrium claim
for OG must factor through this constancy (K-OG-TOLMAN). -/
def OGDatum.IsEquilibrium (D : OGDatum V) : Prop :=
  ∀ i j, D.w i j ≠ 0 → D.θ i = D.θ j

/-- **FROZEN FORM F1 — the unity datum with its declared read
(scoping §4 F1; §5 OG-1 targets (i) + (ii)).**

Over a symmetric nonnegative weight with at least one live edge:
the declared read vanishes exactly on the fields constant on the
weight's support (the characterization direction, iff), and some
field not constant on the support has nonzero read (non-vacuity).
OG-1 proves a theorem of this type or reports the failure.
K-OG-FIAT arms over a postulated discharge; K-OG-VAC over
collapsed witnesses. Tier: statement pin, T1 form / Register-A
content. NO CLAIM; dial-ineligible. -/
def OGUnityForm (w : V → V → ℝ) : Prop :=
  (∀ i j, w i j = w j i) → (∀ i j, 0 ≤ w i j) → (∃ i j, w i j ≠ 0) →
    (∀ θ : V → ℝ, teDirichlet w θ = 0 ↔
      ∀ i j, w i j ≠ 0 → θ i = θ j) ∧
    ∃ θ : V → ℝ, (¬ ∀ i j, w i j ≠ 0 → θ i = θ j) ∧
      teDirichlet w θ ≠ 0

/-- **FROZEN FORM F2 — the factorization fence (scoping §4 F2).**

J-1 demands a test-body × background split; unity declares there
is none. Over the pinned datum this is a statable, failable form:
for every ordered-pair factorization of the datum's own field,
`θ = φ + ψ`, if one side `φ` is constant on the weight's support
then the read's `θ`-dependence collapses to the other side alone —
`teDirichlet w θ = teDirichlet w ψ`. OG-1 proves a theorem of this
type or reports the failure; **either outcome is information the
house does not currently own, and the failure fires no kill.**
Tier: statement pin. NO CLAIM; dial-ineligible. -/
def OGFactorizationForm (w : V → V → ℝ) (θ : V → ℝ) : Prop :=
  (∀ i j, w i j = w j i) → (∀ i j, 0 ≤ w i j) →
    ∀ φ ψ : V → ℝ, θ = φ + ψ →
      (∀ i j, w i j ≠ 0 → φ i = φ j) →
      teDirichlet w θ = teDirichlet w ψ

/-- **FROZEN FORM F3 — the equilibrium fence (scoping §4 F3;
§5 OG-1 target (iv)).**

At equilibrium, every datum's declared read is zero and its
thermal content is constant-field on the support — the Tolman
rigidity restated over the declared datum. OG-1 proves a theorem
of this type or reports the failure. K-OG-TOLMAN arms over any
equilibrium formulation claiming nonconstant content. Tier:
statement pin. NO CLAIM; dial-ineligible. -/
def OGEquilibriumForm : Prop :=
  ∀ D : OGDatum V, D.IsEquilibrium → ogRead D = 0 ∧
    ∀ i j, D.w i j ≠ 0 → D.θ i = D.θ j
