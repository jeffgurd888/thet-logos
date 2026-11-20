import Mathlib.Tactic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import ThetLogos.OGResponsePin

namespace ThetLogos

/-!
# ThetLogos.UnityInertiaPin — U-INERTIA-0, the unity-inertia record pin (0 strict, by design)

**Commission:** Zero opened the D2-0 gate — "yes open it please full
send everywhere we can" (2026-11-17 12:42 EST) — and declared the
primitive in his own words, verbatim (2026-11-17 12:44 EST):

> **"Gravity's Primitive is Unity."**

**Governing document:** `inertia-time-primitive-investigation-2026-11-17.md`
§5 (the declaration, graded) and §6 (this pin, priced S, 0 strict).
This pin is the first failable form over that declaration. It fires
under Zero's full-send extension of 2026-11-09/12, as bounded by the
investigation. U-INERTIA-1 and U-INERTIA-2 are NOT commissioned by
this pin: U-INERTIA-1 is gated on OG-RL-1 at lane grade, U-INERTIA-2
on this pin and the relaxation apparatus's lane state.

## What the declaration is, and what "Unity" already is in-tree

The declaration is **Register A — declared, not derived** (the Gate B
precedent, 2026-11-08: the same sentence bought OG its pinned datum
and, on its own face, "buys no identity, no response law, no dial
motion"). In-tree, Unity already names a datum and its fences:
`OGPin` (ledger #122) — `OGDatum`, ONE structure, weights `w` +
thermal field `θ`, deliberately no body/background factorization —
and `OGExhibit` (#123), whose frozen F1 conjunction is
**kernel-REFUTED as pinned** and stands under a disclosed
off-diagonal live-edge narrowing (the F-6 scar, on the record).
This pin extends the same primitive's name over the inertia/time
side, over the OG-RL extended datum — and inherits the scar's
discipline: its hypotheses are stated in the live-edge form. That
form is carried STRUCTURALLY here: the extended datum's `w_pos`
field (complete positivity of the seat's own weights) is exactly
the live-edge hypothesis, a field of `OGResponseDatum`, not an
assumption added by this pin.

## Face declarations (read before anything below)

- **This module is a PIN.** Definitions and one frozen statement
  form only: **no theorems, no axioms, no proofs.** 0 strict,
  BY DESIGN (the OG-0 / OG-RL-0 form).
- **PRE-REGISTERED DIAL-INELIGIBLE.** NO CLAIM. Dial 2 = 0 before
  this pin, 0 after it, and 0 under every outcome of U-INERTIA-1/2.
  A declaration opens the D2-0 gate; it does not move the dial.
  Dial 2 moves only on a derived test-body response law surviving
  a future P-D2 audit, which no brick on this line performs or
  promises.
- **The declaration is Register-A design**, not a Lean `axiom`,
  and nothing here can be cited as a hypothesis by any proof.
- **Equilibrium fence (standing for this line):** where any later
  brick uses the Gibbs face, its identities are equilibrium-only
  and must be stated as such on their face (K-UIN-EQUIL). This pin
  itself uses no Gibbs face: its kernel is the grounded seat's
  relaxation semigroup, its response is OG-RL's stationarity.
- **No pinned structure is edited.** This pin cites OG-RL-0's
  frozen objects (`OGResponseDatum`, `OGBody`, `seatKinetic`,
  `ogAction`, `ogStationary`, `ogChargePotential`) from
  `OGResponsePin` at the ogrl lane tip (66bf075, the disclosed
  OG-RL-0 pin repair on 843ccb0) and redefines none of them
  (K-OG-RL-AMEND applies in full).
- **What this pin does NOT buy** (investigation §5, on the face):
  no measured number (no value of any mass, of `G`, of `c`); no
  derived inertia, no derived time, no acceleration — acceleration
  proper stays FRONTIER until a theorem closes over the declared
  primitive; no vindication of the dropped text that walked at
  this gate (it enters no register; its candidate primitives keep
  their §4 grades — two costumes and a redescription — and none of
  them is the declared primitive).

## The frozen objects

- **`groundedLapMatrix`** — the grounded seat's Laplacian in
  matrix form, from `w` and the grounding `b` ALONE: the matrix of
  `laplacianOp w` (BridgeLaplacian's landed conventions:
  `laplacianOp w F i = Σ j, w i j * (F i − F j)`) with the ground's
  row and column pinned to `0` — the Dirichlet pin in matrix form,
  so the semigroup below preserves the grounded subspace
  (`F b = 0`). No datum field beyond `w` and `b` enters.
- **`unityKernel`** — (i) of the investigation §6: the two-time
  kernel of the grounded seat, `(exp (−t • L_b)) i j`, the grounded
  heat semigroup's kernel at sites `i, j`. Defined from
  `laplacianOp w`'s matrix and `b` ALONE — **no body data, no
  response data, no source field enters its definition.** This is
  K-UIN-COSTUME's fence made structural: the kernel cannot have
  been fitted to the response it will be compared against, because
  the response's objects (`ogAction`, `ogStationary`, `ρ`, `m`)
  do not occur in its construction.
- **`groundedGreen`** — the grounded Green kernel: the landed
  grounded inversion (`groundedPotential`, UA-2, via OG-RL-0's
  cited `ogChargePotential`) applied to the unit source at `j`,
  read at `i`. The kernel of the grounded Laplacian's inverse on
  the grounded seat.
- **`unityKernelFirstMoment`** — the first moment of
  `unityKernel` across a step, frozen in its operator form:
  `∫₀^∞ t • exp(−t • L_b) dt = L_b⁻²` on the grounded seat (the
  standard resolvent identity), i.e. the Green kernel composed
  with itself, `Σ k, G i k * G k j`. The pin freezes the operator
  form — definable from landed objects, no integral taken. Note
  the grounded extension: the moment vanishes on the ground's row
  and column (the Green kernel is grounded: `G b k = 0` and
  `G k b = 0`), while `seatKinetic` does not — see the target
  form's completion note.
- **`unityResponse`** — (ii) of §6: the body's stationarity
  response under `ogAction`. This is OG-RL's object,
  `ogStationary`, CITED by reference — an alias whose body is the
  cited name, so the pin's vocabulary can name the response under
  the declaration without touching OG-RL's frozen object.
- **`UnityInertiaTargetForm`** — (iii) of §6: the FROZEN TARGET
  FORM. The EL step-cost of `ogAction` at a path step equals the
  first moment of `unityKernel` across that step. Stated as a
  target identity between two INDEPENDENTLY defined objects —
  `seatKinetic` (from `w` alone, Ruling 4) on one side, the
  squared grounded Green kernel (from the grounded inversion of
  `w` at `b`) on the other; different inputs, different
  constructions (K-UIN-RENAME's fence, structural). Its proof is
  U-INERTIA-1's theorem; its failure is U-INERTIA-1's
  countermodel; it is never a definition wearing an iff.

## Pin-level completions (disclosed on the face, OG-RL-0's species)

1. **Per unit mass.** `ogAction`'s step term is
   `B.m * seatKinetic D.w i j` — the mass is the action's single
   common scalar factor (its cancellation is OG-RL-2's theorem,
   K-UIN-MASS's ground). The target form is therefore frozen
   between the two mass-free objects, `seatKinetic` and the first
   moment: the identity per unit mass, in the only form in which
   both sides are independently defined objects of the datum.
2. **Ungrounded steps.** The form is stated across steps between
   ungrounded sites (`i ≠ b`, `j ≠ b`): the grounded semigroup
   moves on the grounded seat, and on the ground's row/column the
   moment is the pseudo-inverse's zero extension (completion
   note at `unityKernelFirstMoment`) while `seatKinetic` is the
   seat's raw weight — the identity there would be a statement
   about the Dirichlet pin's bookkeeping, not about the seat's
   two objects. The restriction is stated here, in the form, not
   discovered at U-INERTIA-1.

## The kill registry (K-UIN-*, pre-registered in the investigation §4/§6)

- **K-UIN-COSTUME** — fires if inertia/cost/memory is computed
  from data containing the response it explains. The kernel is
  defined from (`w`, `b`) alone or the line dies on arrival.
- **K-UIN-RENAME** — fires if `unityKernel`'s moment and the EL
  step-cost turn out to be one object under two names (the
  U-INERTIA-1 identity then being a definition, not a theorem):
  the two definitions must be audibly independent — different
  inputs, different constructions — or the brick does not ship.
- **K-UIN-MASS** — fires if any statement reintroduces
  mass-dependence into stationarity (against
  `rlp1Stationary_m_indep` and OG-RL-2's universality), or
  states/derives a VALUE for any mass, or presents
  mass-cancellation as a defect the primitive repairs.
- **K-UIN-TIME** — fires if "time" in any brick is an imported
  background parameter rather than the seat's own flow (the
  relaxation semigroup's parameter, or the modular flow where the
  Gibbs face is used).
- **K-UIN-EQUIL** — fires if an equilibrium identity is presented
  as a dynamics, a fall, or an out-of-equilibrium response
  (K-FALL-TOLMAN's sibling, registered for this line in advance).
- **K-UIN-SCOPE** — fires on any text presenting a U-INERTIA
  landing as: inertia derived, time derived, acceleration
  derived, the dropped text vindicated, a gravity object, or
  Dial evidence.

The K-OG-RL registry (OGResponsePin face) and the K-FALL registry
(fall-pin scope) apply in full — in particular K-OG-RL-AMEND (no
pinned structure edited; this pin edits none), K-OG-RL-SCOPE, and
K-FALL-CIRCULAR (K-UIN-COSTUME's sibling one level down: there the
gradient could not rename the fall; here the cost cannot rename
the mass). K-FALL-TOLMAN is NOT reopened by anything here: the
Tolman seat remains equilibrium, and naming Unity over this line
does not give it a body.
-/

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- **The grounded Laplacian matrix — PINNED.**

The matrix of the seat's own Laplacian (`laplacianOp w`,
`BridgeLaplacian`: `laplacianOp w F i = Σ j, w i j * (F i − F j)`,
so the matrix carries `Σ_{k ≠ i} w i k` on the diagonal and
`−w i j` off it), with the ground's row and column pinned to `0`
— the Dirichlet pin of the grounded channel (OG-RL Ruling 3) in
matrix form. From `w` and `b` ALONE: no source, no body, no
response object enters. The zero ground row is what makes the
heat semigroup of this matrix preserve the grounded subspace
(`F b = 0`) — the seat the grounded potential lives on. -/
def groundedLapMatrix (w : V → V → ℝ) (b : V) : Matrix V V ℝ :=
  Matrix.of fun i j =>
    if i = b ∨ j = b then 0
    else if i = j then ∑ k ∈ Finset.univ.erase i, w i k
    else -w i j

/-- **The unity kernel — PINNED (investigation §6 (i)).**

The two-time kernel of the grounded seat: the `(i, j)` entry of
the grounded heat semigroup `exp (−t • L_b)`, `L_b` the grounded
Laplacian matrix of the datum's own weights at the datum's own
ground. The corpus's heat-kernel habitat (`heatKernelGen`,
`HermitianReduction`) fed with the grounded seat's generator.

Defined from `laplacianOp w` and the grounding `b` ALONE — via
`D.w` and `D.b`, and nothing else of the datum: no `ρ`, no `θ`,
no body, no action, no stationarity enters. That exclusion is
K-UIN-COSTUME's fence made structural, and it is the whole
content of the word "alone" in the governing scope. -/
noncomputable def unityKernel (D : OGResponseDatum V) (t : ℝ)
    (i j : V) : ℝ :=
  (NormedSpace.exp ((-t) • groundedLapMatrix D.w D.b)) i j

/-- **The grounded Green kernel — PINNED (the moment's auxiliary).**

`G i j` = the grounded potential of the unit source at `j`, read
at `i`: the landed grounded inversion (`groundedPotential`, UA-2)
applied to `Pi.single j 1`, cited through OG-RL-0's
`ogChargePotential` — the same inversion, no new channel. The
kernel of the grounded Laplacian's inverse on the grounded seat;
grounded in both arguments (`G b j = 0`, `G i b = 0` are the
Dirichlet pin's content, theorem-material for later bricks, not
asserted here). From the datum's (`w`, `b`) and its landed
hypotheses (`w_symm`, `w_nonneg`, `w_pos`) alone. -/
noncomputable def groundedGreen (D : OGResponseDatum V) (i j : V) :
    ℝ :=
  ogChargePotential D (Pi.single j 1) i

/-- **The first moment of the unity kernel — PINNED (§6 (iii)).**

The first moment of `unityKernel` across the step `i → j`,
frozen in its operator form: on the grounded seat,
`∫₀^∞ t • exp(−t • L_b) dt = L_b⁻²` (the resolvent identity for
the first moment of a heat kernel), and `L_b⁻¹` is the grounded
Green operator — so the moment is the Green kernel composed with
itself, `Σ k, G i k * G k j`. The pin freezes this operator form:
it is definable from landed objects with no integral taken, and
it is built from (`w`, `b`) alone — the costume fence of
`unityKernel` is inherited, not re-argued.

Grounded extension, on the face: the moment vanishes whenever
`i = b` or `j = b` (the Green kernel is grounded in both
arguments), while `seatKinetic D.w b j = D.w b j` does not. The
target form below is therefore stated across ungrounded steps —
see its completion note. -/
noncomputable def unityKernelFirstMoment (D : OGResponseDatum V)
    (i j : V) : ℝ :=
  ∑ k, groundedGreen D i k * groundedGreen D k j

/-- **The unity response — CITED, not redefined (§6 (ii)).**

The body's stationarity response under `ogAction` — OG-RL's
object `ogStationary`, cited by reference. This alias's body is
the cited name and nothing else: the response object of this
line is OG-RL-0's frozen predicate, unedited and unextended
(K-OG-RL-AMEND). Whether it has instances, and whether it bites,
is OG-RL-1/3's theorem-content (K-OG-RL-VAC) — this pin asserts
nothing about it. -/
def unityResponse (D : OGResponseDatum V) (B : OGBody V) (n : ℕ)
    (x : Fin (n + 1) → V) : Prop :=
  ogStationary D B n x

/-- **FROZEN TARGET FORM — the kernel identity (§6 (iii);
U-INERTIA-1's target).**

The EL step-cost of `ogAction` at a path step equals the first
moment of `unityKernel` across that step: for every step between
ungrounded sites, the seat's kinetic kernel (`seatKinetic`, from
`w` alone — OG-RL Ruling 4) equals the first moment of the
grounded seat's two-time kernel across the same step
(`unityKernelFirstMoment`, from the grounded inversion of `w`
at `b`, squared).

A target identity between two INDEPENDENTLY defined objects:
different inputs (the raw weight vs. the grounded inverse),
different constructions (a field read vs. a semigroup moment).
Its proof is a theorem (U-INERTIA-1); its failure is a
countermodel (U-INERTIA-1, the same brick); it is never a
definition wearing an iff (K-UIN-RENAME).

Completions, disclosed (see the header): per unit mass — the
action's step term is `B.m * seatKinetic`, the mass the action's
single common scalar, so the identity is frozen between the two
mass-free objects; and across ungrounded steps — on the ground's
row/column the moment is the grounded extension `0` while
`seatKinetic` is the raw weight, a bookkeeping fact about the
Dirichlet pin, not a comparison of the seat's two objects. -/
def UnityInertiaTargetForm (D : OGResponseDatum V) : Prop :=
  ∀ i j : V, i ≠ D.b → j ≠ D.b →
    seatKinetic D.w i j = unityKernelFirstMoment D i j

end ThetLogos
