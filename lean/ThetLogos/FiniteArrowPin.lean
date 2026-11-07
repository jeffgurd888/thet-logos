import Mathlib.Tactic
import Mathlib.Analysis.Matrix.PosDef
import ThetLogos.BridgeCompletion
import ThetLogos.ThermoelectricSeat
import ThetLogos.FiniteEntropy
import ThetLogos.BridgeMagneticHeat

/-!
# ThetLogos.FiniteArrowPin — FA-0: the finite arrow seat, pinned

**Working label only** ("finite arrow seat", FA-0..FA-7) — naming is
Jeff's. Scoping: `finite-arrow-scoping-2026-11-06.md` (Jeff's
commission 2026-11-06 09:56 EST, "scope it fully"; the line fired
2026-11-06 17:57 EST, "fire finite arrow"). This module is the pin:
definitions and frozen statement forms only, no proofs. The content
bricks live in `FiniteArrow.lean` (FA-1/2/3/4a/5/6),
`FiniteArrowEntropy.lean` (FA-4b), `FiniteArrowMagnetic.lean` (FA-7).

**The seat.** The TE/Bridge graph seat, unchanged: finite `V`,
symmetric weights `w : V → V → ℝ`. The flow is the landed
`BridgeCompletion.heatOp`, transported to fields `θ : V → ℝ` (the TE
seat's own type) by `euclEquiv`. Nothing landed is redefined:
`laplacianOp`, `energy`, `heatOp`, `teCharge`, `teGradEnergy`,
`entropyW` are all imported.

**What the arrow is here, at the strength the corpus can own**
(scoping §2): on this seat the heat flow has exactly one dissipative
direction — forward (`t ≥ 0`) every off-equilibrium field strictly
loses Dirichlet energy and converges to `ker L`; the reversed curve
is a growth curve solving the anti-heat equation; the equilibrium
locus `ker L` is the unique fixed set. The direction lives in the
sign of the generator plus the off-equilibrium initial condition
(a *hypothesis* on the strictness theorems, `F ∉ ker L`), never in
a time-asymmetric law, and never as a conclusion about the world.

**Fences (on the face, binding every brick of this line).**
- NO CLAIM; dials 0/4; Dial 2 = 0. A finite arrow theorem is a
  decay/entropy theorem about a finite seat. It is not the
  cosmological arrow, not the Past Hypothesis, not a gravity
  object, not a response law, not Dial evidence of any species.
- The thermal-time hypothesis (`UltimateReduction` Claim 6(a)) —
  the identification of a modular/thermal flow with physical
  time — remains T5, a hypothesis, unproved and unmoved by
  anything in this line.
- The LOCAL time arrow (`UltimateReduction` Claim 6(b)) stays
  KILLED in-tree: a local arrow needs a local temperature field
  β(x); the finite seat has none — β is global. Nothing here is a
  site-varying arrow.
- Phase accumulation along the heat flow is NOT STATEABLE
  (scoping §3.6(b2), obstruction proved from the tree's own
  group/isometry theorems): phases live on the reversible side;
  `heatOp` damps real amplitudes and has no phase to advance. No
  brick attempts it.
- "Heat rises" (a spatial direction) is NOT merged with the arrow
  (a time direction) anywhere in this line (scoping §3.7).
- χ² (`chiSq` below) is a *divergence*, not an entropy, and is
  labeled so on every face. Divergence is never renamed entropy.
- The name-space "SecondArrow" / `LegSecondArrow` belongs to the
  Q7 trace-defect leg and is never reused here.

**Kill register (armed from this pin onward; scoping §5).**
- K-ARR-FIAT — the stipulation kill: the production quantity is
  defined *as* the decay it is proved to have, or a divergence is
  renamed "entropy"; or all surviving targets are pin-checks /
  citations with FA-1/FA-2/FA-5 unlanded. Assessed at FA-0 in
  scoping form: content bricks exist (§3.2/3.3/3.5 of the
  scoping), so the pin stands. Shape (1) is decided at FA-4a.
- K-ARR-REVERSAL — the Loschmidt kill: a headline "arrow"
  statement invariant under time reversal (its reverse provable
  in the same decaying form), or a mere unsigned rate bound.
  FA-5 is the standing guard.
- K-ARR-EQ — the equilibrium kill: strictness claimed at
  equilibrium, or convergence "to the constant field / the mean"
  on the full seat family (false on disconnected seats, where
  `ker L` strictly contains the constants). Strictness is stated
  only as: strict iff `F ∉ ker L`; convergence targets `ker L`.
- K-ARR-POS — the positivity kill (FA-4b only): the simplex
  entropy shape stated along the flow without the heat-kernel
  positivity lemma landed. Decided at FA-4b's first step.
- K-ARR-NAME — the collision kill: "SecondArrow" reused, or this
  seat presented as a local arrow, or Claim 6(a) presented as
  proved.
- K-ARR-GRAV — the laundering kill: this seat presented as a
  gravity candidate, response law, cosmological-arrow evidence,
  derivation of physical time, or Dial evidence.

Frozen names (this module): `arrowFlow`, `devEnergy`, `kerProjE`,
`kerProj`, `chiSq`, `eulerStep`, `degSum`, `relEntW`, and the
statement pins `FA1Pin`–`FA7Pin`.
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The pinned definitions -/

/-- **The arrow seat's flow** (pinned): the landed `heatOp` read on
fields `F : V → ℝ`, the TE seat's own type, via `euclEquiv`.
`arrowFlow w hsymm t F` is the field at time `t`. -/
noncomputable def arrowFlow (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (t : ℝ) (F : V → ℝ) : V → ℝ :=
  euclEquiv (heatOp w hsymm t (euclEquiv.symm F))

/-- **The deviation energy** (pinned, scoping §3.2): the Dirichlet
energy of the deviation field `F − meanVec F`. (FA-1 proves this
equals `energy w F` outright: the energy is already mean-invariant,
since `L` kills constants and is symmetric.) -/
noncomputable def devEnergy (w : V → V → ℝ) (F : V → ℝ) : ℝ :=
  energy w (F - meanVec F)

/-- **The kernel projection, Euclidean side** (pinned, scoping
§3.3): the mode-sum over the zero eigenvalues — the projection of
`x` onto `ker (lapLin w)` in the spectral basis. The target of
convergence is `ker L`, NOT the constant field (K-ARR-EQ). -/
noncomputable def kerProjE (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (x : EuclideanSpace ℝ V) : EuclideanSpace ℝ V :=
  ∑ k ∈ Finset.univ.filter (fun k => lapEig w hsymm k = 0),
    ((lapBasis w hsymm).repr x k) • (lapBasis w hsymm) k

/-- **The kernel projection on fields** (pinned): `kerProjE`
transported to `V → ℝ`. -/
noncomputable def kerProj (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (F : V → ℝ) : V → ℝ :=
  euclEquiv (kerProjE w hsymm (euclEquiv.symm F))

/-- **The χ²-divergence to equilibrium** (pinned, scoping
§3.1(i-a)): the sum of the squared mode weights over the NONZERO
modes — equivalently `‖F − kerProj F‖²`. **A divergence, not an
entropy** (K-ARR-FIAT shape (1) fence): it is the L² shadow of
relative entropy, and is named a divergence on every face. -/
noncomputable def chiSq (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (F : V → ℝ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => lapEig w hsymm k ≠ 0),
    ((lapBasis w hsymm).repr (euclEquiv.symm F) k) ^ 2

/-- **One explicit Euler step** (pinned, scoping §3.4):
`eulerStep w τ F = F − τ • L F`. -/
noncomputable def eulerStep (w : V → V → ℝ) (τ : ℝ) (F : V → ℝ) : V → ℝ :=
  F - τ • laplacianOp w F

/-- **The off-diagonal degree sum** (pinned): a named function of
the weights' row sums, `∑ i, ∑ j ≠ i, w i j`, bounding every
off-diagonal row sum (for `w ≥ 0`). The stability bound of FA-3
and FA-4b is stated against `2 * degSum w`. -/
noncomputable def degSum (w : V → V → ℝ) : ℝ :=
  ∑ i, ∑ j, if j = i then 0 else w i j

/-- **Finite relative entropy** (pinned, scoping §3.1(i-b); absent
from the tree before this line): `relEntW p q = ∑ i, p i * log (p i / q i)`,
with Mathlib's `log 0 = 0` convention in force. -/
noncomputable def relEntW (p q : V → ℝ) : ℝ :=
  ∑ i, p i * Real.log (p i / q i)

/-! ## The frozen statement forms (FA-1..FA-7)

Each pin below is the verbatim statement form its brick must land.
The content modules prove the theorems and discharge these pins. -/

/-- **FA-1 (the Lyapunov core), frozen form** (scoping §3.2): the
deviation energy along the flow has derivative
`−2 ∑ i, (L (θ t)) i ^ 2`, is antitone on `t ≥ 0`, and is strictly
decreasing at every `t > 0` iff `F ∉ ker L` — strictness in the
iff form only (K-ARR-EQ). -/
def FA1Pin : Prop :=
  ∀ (w : V → V → ℝ) (_hw : ∀ i j, w i j = w j i) (_hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) (F : V → ℝ),
    (∀ t : ℝ, HasDerivAt (fun s => devEnergy w (arrowFlow w hsymm s F))
        (-2 * ∑ i, (laplacianOp w (arrowFlow w hsymm t F)) i ^ 2) t)
    ∧ AntitoneOn (fun t => devEnergy w (arrowFlow w hsymm t F)) (Set.Ici 0)
    ∧ (∀ t : ℝ, 0 < t →
        (devEnergy w (arrowFlow w hsymm t F) < devEnergy w F
          ↔ laplacianOp w F ≠ 0))

/-- **FA-2 (approach to equilibrium), frozen form** (scoping §3.3):
every field converges under the flow to its `ker L` projection —
the target is `ker L`, not the constants (K-ARR-EQ). -/
def FA2Pin : Prop :=
  ∀ (w : V → V → ℝ) (_hw : ∀ i j, w i j = w j i) (_hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) (F : V → ℝ),
    Filter.Tendsto (fun t => arrowFlow w hsymm t F) Filter.atTop
      (nhds (kerProj w hsymm F))

/-- **FA-3 (the discrete step), frozen form** (scoping §3.4): one
Euler step at/below the explicit stability bound
`τ * (2 * degSum w) ≤ 1` does not increase the deviation energy,
and strictly decreases it iff `F ∉ ker L`. -/
def FA3Pin : Prop :=
  ∀ (w : V → V → ℝ) (_hw : ∀ i j, w i j = w j i) (_hw0 : ∀ i j, 0 ≤ w i j)
    (τ : ℝ) (_hτ : 0 < τ) (_hstab : τ * (2 * degSum w) ≤ 1) (F : V → ℝ),
    devEnergy w (eulerStep w τ F) ≤ devEnergy w F
    ∧ (devEnergy w (eulerStep w τ F) < devEnergy w F
        ↔ laplacianOp w F ≠ 0)

/-- **FA-4a (production, divergence form), frozen form** (scoping
§3.1(i-a)): the χ²-divergence along the flow has derivative
`−(2 * devEnergy (θ t))` — the production rate is the deviation
energy itself, a theorem, not a definition (K-ARR-FIAT shape (1)
is decided against this form) — is antitone on `t ≥ 0`, and is
strictly decreasing at every `t > 0` iff `F ∉ ker L`. -/
def FA4aPin : Prop :=
  ∀ (w : V → V → ℝ) (_hw : ∀ i j, w i j = w j i) (_hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) (F : V → ℝ),
    (∀ t : ℝ, HasDerivAt (fun s => chiSq w hsymm (arrowFlow w hsymm s F))
        (-(2 * devEnergy w (arrowFlow w hsymm t F))) t)
    ∧ AntitoneOn (fun t => chiSq w hsymm (arrowFlow w hsymm t F)) (Set.Ici 0)
    ∧ (∀ t : ℝ, 0 < t →
        (chiSq w hsymm (arrowFlow w hsymm t F) < chiSq w hsymm F
          ↔ laplacianOp w F ≠ 0))

/-- **FA-4b (production, entropy form — CONTINGENT), frozen form**
(scoping §3.1(i-b); K-ARR-POS decides at its first step): the heat
kernel is entrywise nonnegative — the flow preserves positive
fields, with the diagonal lower bound `e^{−t·degSum} · F i` at
strictly positive fields — and the Shannon entropy of the
normalized evolved field is monotone non-decreasing on `t ≥ 0`.
Stated for strictly positive initial fields (a *positive* field,
in the scoping's words), whose normalizations are probability
weights. -/
def FA4bPin : Prop :=
  ∀ (w : V → V → ℝ) (_hw : ∀ i j, w i j = w j i) (_hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric),
    (∀ (t : ℝ) (_ht : 0 ≤ t) (F : V → ℝ) (_hF : ∀ i, 0 ≤ F i) (i : V),
        0 ≤ arrowFlow w hsymm t F i)
    ∧ (∀ (F : V → ℝ) (_hF : ∀ i, 0 < F i),
        MonotoneOn (fun t => entropyW (fun i =>
            arrowFlow w hsymm t F i / ∑ j, arrowFlow w hsymm t F j))
          (Set.Ici 0))

/-- **FA-5 (the Loschmidt pair), frozen form** (scoping §3.5): the
reversed curve solves the anti-heat equation `Ḟ = +L F` and its
deviation energy GROWS at exactly the forward production rate
(derivative `+2 ∑ i, (L (θ (−t))) i ^ 2`), is monotone on
`t ≥ 0`, with the same iff equality locus. The pair — forward
decay (FA-1) with backward growth in the OPPOSITE form — is the
seat's standing guard against K-ARR-REVERSAL: the direction is
located in the generator's sign (`L ≥ 0`, the seat's datum) plus
the off-equilibrium hypothesis, not in the law. -/
def FA5Pin : Prop :=
  ∀ (w : V → V → ℝ) (_hw : ∀ i j, w i j = w j i) (_hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) (F : V → ℝ),
    (∀ t : ℝ, HasDerivAt (fun s => arrowFlow w hsymm (-s) F)
        (laplacianOp w (arrowFlow w hsymm (-t) F)) t)
    ∧ (∀ t : ℝ, HasDerivAt (fun s => devEnergy w (arrowFlow w hsymm (-s) F))
        (2 * ∑ i, (laplacianOp w (arrowFlow w hsymm (-t) F)) i ^ 2) t)
    ∧ MonotoneOn (fun t => devEnergy w (arrowFlow w hsymm (-t) F)) (Set.Ici 0)
    ∧ (∀ t : ℝ, 0 < t →
        (devEnergy w F < devEnergy w (arrowFlow w hsymm (-t) F)
          ↔ laplacianOp w F ≠ 0))

/-- **FA-6 (the TE time course), frozen form** (scoping §3.8(d1)):
the TE seat composed with the flow — total separated charge stays
`0` at every time (TE-T3 at `θ(t)`, citation-grade, labeled), and
the separation's gradient energy along the flow is exactly twice
the deviation energy (so FA-1 meters the separation's decay; NO
persistence claim for the extremal sign law is made or priced). -/
def FA6Pin : Prop :=
  ∀ (w : V → V → ℝ) (_hw : ∀ i j, w i j = w j i) (_hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) (θ : V → ℝ),
    (∀ t : ℝ, ∑ i, teCharge w (arrowFlow w hsymm t θ) i = 0)
    ∧ (∀ t : ℝ, teGradEnergy w (arrowFlow w hsymm t θ)
        = 2 * devEnergy w (arrowFlow w hsymm t θ))
    ∧ AntitoneOn (fun t => teGradEnergy w (arrowFlow w hsymm t θ)) (Set.Ici 0)

/-- **FA-7 (magnetic decay, OPTIONAL), frozen form** (scoping
§3.8(d3)): the gauged flow's quadratic form `⟪x, magHeat t x⟫` is
antitone in `t` on `t ≥ 0` — energy decay survives gauging, as a
citation-assembly on `heatKernelGen`'s quadratic-form identities.
NO time-reversal-breaking claim is made (fenced NOT STATEABLE in
the scoping: `magHeat` is a self-adjoint semigroup whose Loschmidt
pair has the ungauged form). -/
def FA7Pin : Prop :=
  ∀ (w : V → V → ℝ) (_hw : ∀ i j, w i j = w j i) (_hw0 : ∀ i j, 0 ≤ w i j)
    (θ : V → V → Circle) (_hθ : ∀ i j, θ j i = (θ i j)⁻¹)
    (x : V → ℂ),
    AntitoneOn (fun t => (dotProduct (star x)
      (Matrix.mulVec (magHeat w θ t) x)).re) (Set.Ici 0)

end ThetLogos
