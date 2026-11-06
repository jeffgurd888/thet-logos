import Mathlib.Tactic
import ThetLogos.BridgeLaplacian
import ThetLogos.ThermalChargePoisson

/-!
# ThetLogos.ThermoelectricSeat — the thermoelectric seat (heat in, separated charge out)

Thread name: **THERMOELECTROGRAVITIC** — Jeff's coinage (2026-11-05 16:32
EST: "well if hear rises then gravity goes down thermoelectrogravitic";
"hear" is dictation for "heat"). Per Jeff's naming rule the coinage is
carried as the *thread name* only: it names the program line this module
belongs to and nothing more. It asserts no identity, discharges no claim,
and moves no dial. The seat's working engineering label is the
thermoelectric seat; scoping: `thermoelectric-seat-scoping-2026-11-05.md`
(§1 grades the motivating question, §2 the corpus audit, §3 the pin, §4
the targets TE-T1…TE-T6 and the kill register, §5 the menu TE-0…TE-3).

**Origin (Jeff, 2026-11-05 16:29 EST, verbatim):** "well I was more
speaking to the primitive of heat to create charge separation. is
gravity the heat generating the up arrow and flow direction"

**The question, graded (§1 of the scoping) — a live external direction,
NOT an identity, never a premise.** The direction Jeff proposes (heat
relations primitive, gravity derived) is the direction of a named
research program: Jacobson's 1995 derivation of Einstein's field
equations as an equation of state from δQ = T dS on local horizons;
behind it Bekenstein–Hawking horizon thermodynamics and Tolman–Ehrenfest
grading of temperature by gravitational potential. Convection is the
established literal case of heat generating an up arrow and a flow
direction under gravity (Rayleigh–Bénard). What the field has not
settled is whether gravity *is* heat at bottom or only obeys heat's laws
at horizons. The question stays where Jeff put it — a question — and
appears in this module only as the seat's motivation. The seat itself
builds the **separation primitive** (heat creates charge separation), a
mechanism with established literal instances (Seebeck / thermoelectric
effect, thermionic emission, plasma separation), needing no gravity
claim. The seat has no up, no down, and no gravity: a finite graph has
no preferred direction until a field supplies one, and the only
direction this seat ever sees is the thermal field's own gradient
(hot to cold).

## The pin (Register A — scoping §3)

Seat data: a finite nonempty site type `V` (`Fintype V`, `Nonempty V`;
`DecidableEq V` is carried to match the graph seat family's own variable
conventions in `BridgeLaplacian`/`ThermalChargePoisson`) with symmetric
weights `w : V → V → ℝ`, `w i j ≥ 0` — the corpus's graph seat, imported
from `BridgeLaplacian`/`ThermalChargePoisson`, not redefined. A
**thermal field** `θ : V → ℝ` (no positivity on `θ` is needed by any
target; the mathematics runs on any real field). Its gradient is the
edge-difference field `θ i − θ j`. The **separated charge** is the
divergence of the thermal flux:

> `teCharge w θ i := −(laplacianOp w θ) i`

**Reconciliation with the landed operator (checked at the pin, not
assumed):** the landed `laplacianOp` (`BridgeLaplacian.lean`) satisfies
`(laplacianOp w θ) i = ∑ j, w i j * (θ i − θ j)` definitionally
(`laplacianOp_apply` is `rfl`), so the pinned rule
`−∑ j, w i j · (θ i − θ j)` is the landed operator verbatim — same sign,
same scaling, no adjustment. The flux across edge `(i,j)` is
`w i j (θ i − θ j)` (hot to cold) and `q` is its net inflow. **Response
generalization, pinned at the same brick:** for `ψ : ℝ → ℝ`,
`teChargeResp ψ w θ := −laplacianOp w (ψ ∘ θ)`; the linear rule is
`ψ = id`. Nothing else is stipulated: no carriers, no quantization, no
dynamics.

**Sign convention (pinned once, here):** flux flows hot → cold, `q` is
net inflow, so a hot peak (flux diverging out) carries `q < 0` and a
cold sink carries `q > 0`.

**What "charge" is at this tier.** A signed density field `q : V → ℝ`
whose total is identically zero (landed range theory:
`range_lapLinFun_eq_ker_chargeSum` — the range of the graph Laplacian
is exactly the sum-zero fields). Separation *redistributes*; it creates
nothing net. That is the strongest notion of charge the corpus's
primitives honestly support: `q` is not electric charge, carries no
coupling, and obeys no field equation — it is the thermal field's flux
divergence, full stop.

## What this seat is NOT

- **Not a gravity candidate, not a response law, not Dial evidence**
  (kill **K-TE-GRAV**). There is no test body: `θ` is a background field
  and `q` is read off it — the RL-1/RL-8 species of ineligibility, if it
  were ever proposed as a response law, which it is not. **Dial 2 = 0**
  is part of this seat's statement, not a footnote to it.
- **Not an extension, completion, or supersession of
  `ChargeSeparationPost`** (kill **K-TE-NAME**). That landed module owns
  "charge separation" in the *sector-expectation* sense: a uniform
  scalar `β` biases a ± grading's expectation. This seat is *gradient*
  separation: a spatial thermal field, transport along its gradient, a
  signed charge field located at sites. The two mechanisms share words
  and nothing else. Nor is this seat an extension of
  `ThermalProfileSeparation` (a two-level temperature profile producing
  a sector *population imbalance* — a probability over a chosen subset,
  not a signed field on sites).
- **Not dynamics.** The seat is a static configuration and its induced
  field. No approach-to-equilibrium statement is made or priced here.

## Weighting of the targets (on the face)

**TE-T1** (zero gradient ⇒ no separation) is a **pin-check**: it
certifies the pinned law is a gradient law, graded as such, not
inflated. **TE-T3** (conservation) is **citation-grade**: it is landed
range theory restated on this seat's definitions. The seat's content
theorems are **TE-T2** (the extremal sign law — separation as a located
fact), **TE-T4** (the Dirichlet identity and variation bound — the
quantitative heart) and, at TE-3, **TE-T5** (the two-level Seebeck law).
**TE-T6** (the response generalization) is the brick that separates a
law from a relabeling: TE-T1/T2/T3 carried through nonlinear response
`ψ`, with signs by monotonicity direction. TE-T4(a)'s rank is recorded
exactly where it is proved: the Dirichlet identity itself is landed on
this seat family (`energy_eq_half` in `BridgeLaplacian`); TE-T4(a) here
is a sign/pairing repackaging of it — citation-assembly rank, no
inflation either way.

## Sums over edges (a formalization note for TE-T4)

The scoping writes the gradient energy and the variation as sums over
unordered edge pairs `∑_{i<j}`. An unordered finite type `V` carries no
`i < j`; this module pins both as **ordered double sums**
(`∑ i, ∑ j, …`), in which each unordered edge is counted twice and the
diagonal terms vanish. Under that identification the charter's
`−∑_{i<j} w i j (θ i − θ j)²` is `−(1/2) · teGradEnergy`, and its
`2 · ∑_{i<j} w i j |θ i − θ j|` is `teVariation` itself. The factor is
stated on the theorems' faces, not absorbed into the definitions.

## Kill register (armed from the pin brick onward)

- **K-TE-FIAT** — the stipulation kill. Shape (1): fires at TE-0 if the
  targets surviving audit are all definitional tautologies or pure
  citations (TE-T1/T3 alone do not constitute a seat). Shape (2): fires
  at TE-2 if TE-T6 fails — the sign law cannot be carried through any
  nonlinear response `ψ`.
- **K-TE-CONSERVE** — the creation kill. Fires at TE-0 if any pinned
  separation rule has total charge not identically zero for some `θ`.
- **K-TE-NAME** — the collision kill (§2.3 of the scoping): fires if
  any text presents this seat as extending/completing/superseding
  `ChargeSeparationPost`, or uses "charge separation" for this seat
  without the gradient/sector distinction stated (it is stated above).
- **K-TE-GRAV** — the laundering kill: fires if any text presents this
  seat, its theorems, or the coinage THERMOELECTROGRAVITIC as a gravity
  candidate, response law, Dial evidence, or support for the identity
  in Jeff's question. It is none of those (see above).

**NO CLAIM. Dials 0/4. Dial 2 = 0.**
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## TE-0 — the pin

Seat data on the landed `(V, w)` graph seat; the thermal field; the
separated charge `teCharge w θ := −laplacianOp w θ` and its response
generalization `teChargeResp`. K-TE-CONSERVE is checked at this brick:
the pinned rule's total is identically zero because `teCharge w θ` lies
in the range of `laplacianOp`, which landed range theory
(`lapLinFun_mapsTo_ker_chargeSum`, `range_lapLinFun_eq_ker_chargeSum`)
places inside `ker chargeSum`; the check was run against the
definitions below and passes (the conservation theorem itself is landed
as TE-T3 at TE-1, labeled citation-grade there). No Rule-B variant is
entertained by this pin, so no variant dies here. K-TE-FIAT shape (1)
is assessed at this brick: it does **not** fire — beyond the pin-check
TE-T1 and the citation TE-T3, the audit leaves content theorems
standing (TE-T2's strict sign law, TE-T4's quantitative bounds, TE-T5's
explicit coefficient), so the seat is not pin-checks alone. -/

/-- **The separated charge field** (the pin, scoping §3):
`teCharge w θ i = −(laplacianOp w θ) i` — the divergence of the thermal
flux. Charge accumulates where heat flux converges: the discrete
Seebeck shape. -/
def teCharge (w : V → V → ℝ) (θ : V → ℝ) (i : V) : ℝ :=
  -(laplacianOp w θ i)

/-- **The response-generalized separated charge** (pinned at the same
brick): `teChargeResp ψ w θ = −laplacianOp w (ψ ∘ θ)`. The linear rule
`teCharge` is the case `ψ = id`. -/
def teChargeResp (ψ : ℝ → ℝ) (w : V → V → ℝ) (θ : V → ℝ) (i : V) : ℝ :=
  -(laplacianOp w (ψ ∘ θ) i)

/-- The pinned rule, unfolded: `teCharge w θ i = −∑ j, w i j * (θ i −
θ j)`. This is the scoping's display verbatim; it holds definitionally
because the landed `laplacianOp_apply` is `rfl` — the reconciliation
recorded in the header. -/
theorem teCharge_apply (w : V → V → ℝ) (θ : V → ℝ) (i : V) :
    teCharge w θ i = -∑ j, w i j * (θ i - θ j) := rfl

/-- The response rule is the linear rule applied to the responded
field: `teChargeResp ψ w θ = teCharge w (ψ ∘ θ)`, by definition. Every
TE-T6 statement is proved through this bridge. -/
theorem teChargeResp_eq (ψ : ℝ → ℝ) (w : V → V → ℝ) (θ : V → ℝ) :
    teChargeResp ψ w θ = teCharge w (ψ ∘ θ) := rfl

/-! ## TE-1 — sign and conservation

TE-T1 (pin-check, labeled), TE-T3 (citation-grade, labeled), and TE-T2,
the brick's real proof: the extremal sign law. -/

/-- **TE-T1 — zero gradient ⇒ no separation (PIN-CHECK).** If `θ` is
constant on the weight support (across every edge of nonzero weight),
the separated charge vanishes at every site. Graded a pin-check: it
certifies the pinned law is a gradient law — differences vanish edge by
edge — and is not inflated beyond that. (Its energy-criterion
strengthening is TE-T4's equality case at TE-2.) -/
theorem teCharge_eq_zero_of_forall_eq (w : V → V → ℝ) (θ : V → ℝ)
    (hθ : ∀ i j, w i j ≠ 0 → θ i = θ j) (i : V) :
    teCharge w θ i = 0 := by
  rw [teCharge_apply, neg_eq_zero]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hw : w i j = 0
  · rw [hw, zero_mul]
  · rw [hθ i j hw, sub_self, mul_zero]

/-- **TE-T3 — conservation (CITATION-grade).** The total separated
charge is identically zero, for every thermal field: `∑ i, teCharge w
θ i = 0`. This is landed range theory restated on the seat's
definitions — `teCharge w θ` lies in the range of the Laplacian, which
`lapLinFun_mapsTo_ker_chargeSum` (the ⊆ half of
`range_lapLinFun_eq_ker_chargeSum`, `ThermalChargePoisson`) places
inside `ker chargeSum`. Recorded as a citation: it is the seat's
license to call `q` a *separation* (redistribution) rather than a
creation. The ψ-response form is TE-T6 at TE-2. -/
theorem teCharge_sum_eq_zero (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (θ : V → ℝ) :
    ∑ i, teCharge w θ i = 0 := by
  have h := lapLinFun_mapsTo_ker_chargeSum w hw θ
  rw [mem_ker_chargeSum_iff, lapLinFun_apply] at h
  have hsum : (∑ i, teCharge w θ i) = ∑ i, (-laplacianOp w θ i) :=
    Finset.sum_congr rfl fun i _ => rfl
  rw [hsum, Finset.sum_neg_distrib, h, neg_zero]

/-- **TE-T2, maximum form — the extremal sign law.** At a site `i`
attaining the maximum of `θ`, with a positive-weight edge to a strictly
cooler site, the separated charge is strictly negative: the hottest
site is a source of the negative sign (flux diverging out, `q` = net
inflow `< 0`, per the pinned sign convention). Every flux term at `i`
is nonnegative and the witness edge's term is strictly positive. This
is the theorem that makes "separation" a located fact. -/
theorem teCharge_neg_of_max (w : V → V → ℝ) (hw0 : ∀ i j, 0 ≤ w i j)
    (θ : V → ℝ) (i : V) (hmax : ∀ j, θ j ≤ θ i)
    {j₀ : V} (hwpos : 0 < w i j₀) (hcool : θ j₀ < θ i) :
    teCharge w θ i < 0 := by
  have hsum : 0 < ∑ j, w i j * (θ i - θ j) := by
    have h := Finset.sum_lt_sum
      (s := Finset.univ) (f := fun _ => (0 : ℝ)) (g := fun j => w i j * (θ i - θ j))
      (fun j _ => mul_nonneg (hw0 i j) (sub_nonneg.mpr (hmax j)))
      ⟨j₀, Finset.mem_univ j₀, mul_pos hwpos (sub_pos.mpr hcool)⟩
    simpa using h
  rw [teCharge_apply]
  exact neg_lt_zero.mpr hsum

/-- **TE-T2, minimum form — the extremal sign law.** At a site `i`
attaining the minimum of `θ`, with a positive-weight edge to a strictly
hotter site, the separated charge is strictly positive: the coldest
site is a sink of the positive sign (flux converging in). Dual of
`teCharge_neg_of_max`. -/
theorem teCharge_pos_of_min (w : V → V → ℝ) (hw0 : ∀ i j, 0 ≤ w i j)
    (θ : V → ℝ) (i : V) (hmin : ∀ j, θ i ≤ θ j)
    {j₀ : V} (hwpos : 0 < w i j₀) (hhot : θ i < θ j₀) :
    0 < teCharge w θ i := by
  have hsum : ∑ j, w i j * (θ i - θ j) < 0 := by
    have h := Finset.sum_lt_sum
      (s := Finset.univ) (f := fun j => w i j * (θ i - θ j)) (g := fun _ => (0 : ℝ))
      (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hw0 i j)
        (sub_nonpos.mpr (hmin j)))
      ⟨j₀, Finset.mem_univ j₀,
        mul_neg_of_pos_of_neg hwpos (sub_neg.mpr hhot)⟩
    simpa using h
  rw [teCharge_apply]
  exact neg_pos.mpr hsum

/-! ## TE-2 — the quantitative heart

TE-T4 (the Dirichlet identity, its sign, its equality case, and the
variation bound) and TE-T6 (the response generalization; K-TE-FIAT
shape (2) is decided in this section — it does **not** fire: the sign
law is carried through strictly monotone and strictly antitone
response, below). -/

/-- **The Dirichlet pairing** (new definition, TE-T4): the separated
charge paired against the thermal field, `∑ i, teCharge w θ i * θ i`.
Separation is metered by the gradient energy through this pairing
(`teDirichlet_eq`). -/
def teDirichlet (w : V → V → ℝ) (θ : V → ℝ) : ℝ :=
  ∑ i, teCharge w θ i * θ i

/-- **The gradient energy** (new definition, TE-T4): the ordered
double sum `∑ i, ∑ j, w i j * (θ i − θ j)^2`. Ordered, per the header's
edge-sum note: each unordered edge is counted twice, diagonal terms
vanish; this is twice the charter's `∑_{i<j}` sum. -/
def teGradEnergy (w : V → V → ℝ) (θ : V → ℝ) : ℝ :=
  ∑ i, ∑ j, w i j * (θ i - θ j) ^ 2

/-- **The total variation** (new definition, TE-T4): the ordered
double sum `∑ i, ∑ j, w i j * |θ i − θ j|` — the charter's
`2 · ∑_{i<j} w i j |θ i − θ j|` under the same edge identification. -/
def teVariation (w : V → V → ℝ) (θ : V → ℝ) : ℝ :=
  ∑ i, ∑ j, w i j * |θ i - θ j|

/-- **TE-T4 (a) — the Dirichlet identity.** `teDirichlet w θ =
−(teGradEnergy w θ)/2`: the separated charge paired against the
thermal field is exactly minus the gradient energy (the `/2` is the
ordered-sum factor of the header's edge note — this display *is* the
charter's `−∑_{i<j} w i j (θ i − θ j)²`).

**Rank, recorded exactly:** the identity itself is landed on this seat
family — it is `energy_eq_half` in `BridgeLaplacian`, applied here to
the pairing `∑ i, θ i * laplacianOp w θ i`. This theorem is a
sign/pairing repackaging of that landed identity (citation-assembly
rank): the only step of its own is commuting each factor and negating
through the sum. No inflation either way. -/
theorem teDirichlet_eq (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (θ : V → ℝ) :
    teDirichlet w θ = -(teGradEnergy w θ) / 2 := by
  have h1 : teDirichlet w θ = -(∑ i, θ i * laplacianOp w θ i) := by
    have hsum : teDirichlet w θ = ∑ i, (-laplacianOp w θ i * θ i) :=
      Finset.sum_congr rfl fun i _ => rfl
    rw [hsum]
    have h2 : (∑ i, (-laplacianOp w θ i * θ i))
        = ∑ i, (-(θ i * laplacianOp w θ i)) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [h2, Finset.sum_neg_distrib]
  have hE : teGradEnergy w θ = ∑ i, ∑ j, w i j * (θ i - θ j) ^ 2 := rfl
  rw [h1, energy_eq_half w hw θ, hE]
  ring

/-- **TE-T4 (a), sign.** The Dirichlet pairing is nonpositive:
separation paired against its own thermal field never returns a
positive value; it is metered by (minus) the gradient energy
(`teDirichlet_eq`), which is a sum of nonnegative terms. -/
theorem teDirichlet_nonpos (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) (θ : V → ℝ) :
    teDirichlet w θ ≤ 0 := by
  rw [teDirichlet_eq w hw θ]
  have hE : 0 ≤ teGradEnergy w θ := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (hw0 i j) (sq_nonneg _)
  have hE2 : teGradEnergy w θ
      = ∑ i, ∑ j, w i j * (θ i - θ j) ^ 2 := rfl
  rw [hE2] at hE
  linarith

/-- **TE-T4 (a), equality case.** The Dirichlet pairing vanishes iff
`θ` is constant on the weight support — across every edge of nonzero
weight, `θ i = θ j`. This strengthens TE-T1 from the definition to an
energy criterion: zero pairing, zero gradient energy, and zero
separation are the same configuration class. (The middle step is the
landed `energy_eq_zero_iff`; the support reading of its conclusion is
this seat's.) -/
theorem teDirichlet_eq_zero_iff (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j) (θ : V → ℝ) :
    teDirichlet w θ = 0 ↔ ∀ i j, w i j ≠ 0 → θ i = θ j := by
  have h1 : teDirichlet w θ = -(∑ i, θ i * laplacianOp w θ i) := by
    have hsum : teDirichlet w θ = ∑ i, (-laplacianOp w θ i * θ i) :=
      Finset.sum_congr rfl fun i _ => rfl
    rw [hsum]
    have h2 : (∑ i, (-laplacianOp w θ i * θ i))
        = ∑ i, (-(θ i * laplacianOp w θ i)) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [h2, Finset.sum_neg_distrib]
  rw [h1, neg_eq_zero]
  constructor
  · intro h i j hij
    have hterm := (energy_eq_zero_iff w hw hw0 θ).mp h i j
    rcases mul_eq_zero.mp hterm with h1' | h2'
    · exact absurd h1' hij
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h2')
  · intro h
    apply (energy_eq_zero_iff w hw hw0 θ).mpr
    intro i j
    by_cases hw : w i j = 0
    · rw [hw, zero_mul]
    · rw [h i j hw, sub_self, sq, mul_zero, mul_zero]

/-- **TE-T4 (b) — the variation bound.** The total separated charge,
in absolute value, is bounded by the total variation of the thermal
field: `∑ i, |teCharge w θ i| ≤ teVariation w θ` (the charter's
`2 · ∑_{i<j}` bound, under the header's edge identification). Proof:
the triangle inequality at each site, with `|w i j| = w i j` by
nonnegativity, then summed. -/
theorem teVariation_bound (w : V → V → ℝ) (hw0 : ∀ i j, 0 ≤ w i j)
    (θ : V → ℝ) :
    ∑ i, |teCharge w θ i| ≤ teVariation w θ := by
  show ∑ i, |teCharge w θ i| ≤ ∑ i, ∑ j, w i j * |θ i - θ j|
  apply Finset.sum_le_sum
  intro i _
  rw [teCharge_apply, abs_neg]
  calc |∑ j, w i j * (θ i - θ j)|
      ≤ ∑ j, |w i j * (θ i - θ j)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, w i j * |θ i - θ j| :=
        Finset.sum_congr rfl fun j _ => by
          rw [abs_mul, abs_of_nonneg (hw0 i j)]

/-! ### TE-T6 — the response generalization

TE-T1, TE-T3, and TE-T2 carried through the response `q[ψ, θ] =
−laplacianOp w (ψ ∘ θ)`, via the definitional bridge `teChargeResp_eq`.
TE-T1 and TE-T3 hold for *every* `ψ`; TE-T2's signs hold by
monotonicity direction: strictly monotone `ψ` preserves the extrema
and the signs; strictly antitone `ψ` swaps the extrema and flips the
signs. TE-T5's response form (drop `ψ(θ_H) − ψ(θ_C)`) is TE-3's brick,
not stated here. **K-TE-FIAT shape (2) is decided by this section and
does not fire:** the separation content survives nonlinear response,
so the rule is not the Laplacian wearing a name. -/

/-- **TE-T6 / TE-T1 for response fields.** Zero gradient ⇒ no
separation, for every response `ψ`: if `θ` is constant on the weight
support, so is `ψ ∘ θ`. -/
theorem teChargeResp_eq_zero_of_forall_eq (ψ : ℝ → ℝ) (w : V → V → ℝ)
    (θ : V → ℝ) (hθ : ∀ i j, w i j ≠ 0 → θ i = θ j) (i : V) :
    teChargeResp ψ w θ i = 0 := by
  have h := teCharge_eq_zero_of_forall_eq w (ψ ∘ θ)
    (fun a b hab => by
      show ψ (θ a) = ψ (θ b)
      rw [hθ a b hab]) i
  exact h

/-- **TE-T6 / TE-T3 for response fields.** Conservation for every
response `ψ`: the total of `teChargeResp ψ w θ` is identically zero —
the same landed range theory, applied to the field `ψ ∘ θ`. -/
theorem teChargeResp_sum_eq_zero (ψ : ℝ → ℝ) (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (θ : V → ℝ) :
    ∑ i, teChargeResp ψ w θ i = 0 := by
  have hsum : (∑ i, teChargeResp ψ w θ i)
      = ∑ i, teCharge w (ψ ∘ θ) i :=
    Finset.sum_congr rfl fun i _ => congrFun (teChargeResp_eq ψ w θ) i
  rw [hsum]
  exact teCharge_sum_eq_zero w hw (ψ ∘ θ)

/-- **TE-T6 / TE-T2, strictly monotone response, maximum form.** A
strictly monotone `ψ` preserves the maximum and its sign: at a
`θ`-maximum with a cooler conducting edge, `teChargeResp ψ w θ i <
0`. -/
theorem teChargeResp_neg_of_strictMono (ψ : ℝ → ℝ) (hψ : StrictMono ψ)
    (w : V → V → ℝ) (hw0 : ∀ i j, 0 ≤ w i j) (θ : V → ℝ) (i : V)
    (hmax : ∀ j, θ j ≤ θ i)
    {j₀ : V} (hwpos : 0 < w i j₀) (hcool : θ j₀ < θ i) :
    teChargeResp ψ w θ i < 0 := by
  have h := teCharge_neg_of_max w hw0 (ψ ∘ θ) i
    (fun j => hψ.monotone (hmax j)) hwpos (hψ hcool)
  exact h

/-- **TE-T6 / TE-T2, strictly monotone response, minimum form.** At a
`θ`-minimum with a hotter conducting edge, `teChargeResp ψ w θ i >
0`. -/
theorem teChargeResp_pos_of_strictMono (ψ : ℝ → ℝ) (hψ : StrictMono ψ)
    (w : V → V → ℝ) (hw0 : ∀ i j, 0 ≤ w i j) (θ : V → ℝ) (i : V)
    (hmin : ∀ j, θ i ≤ θ j)
    {j₀ : V} (hwpos : 0 < w i j₀) (hhot : θ i < θ j₀) :
    0 < teChargeResp ψ w θ i := by
  have h := teCharge_pos_of_min w hw0 (ψ ∘ θ) i
    (fun j => hψ.monotone (hmin j)) hwpos (hψ hhot)
  exact h

/-- **TE-T6 / TE-T2, strictly antitone response, maximum form.** A
strictly antitone `ψ` swaps the extrema: a `θ`-maximum is a
`ψ ∘ θ`-minimum, and the sign flips — `teChargeResp ψ w θ i > 0`. -/
theorem teChargeResp_pos_of_strictAnti (ψ : ℝ → ℝ) (hψ : StrictAnti ψ)
    (w : V → V → ℝ) (hw0 : ∀ i j, 0 ≤ w i j) (θ : V → ℝ) (i : V)
    (hmax : ∀ j, θ j ≤ θ i)
    {j₀ : V} (hwpos : 0 < w i j₀) (hcool : θ j₀ < θ i) :
    0 < teChargeResp ψ w θ i := by
  have hmin : ∀ j, (ψ ∘ θ) i ≤ (ψ ∘ θ) j := by
    intro j
    show ψ (θ i) ≤ ψ (θ j)
    rcases (hmax j).eq_or_lt with h | h
    · rw [h]
    · exact le_of_lt (hψ h)
  have h := teCharge_pos_of_min w hw0 (ψ ∘ θ) i hmin hwpos
    (show (ψ ∘ θ) i < (ψ ∘ θ) j₀ from hψ hcool)
  exact h

/-- **TE-T6 / TE-T2, strictly antitone response, minimum form.** At a
`θ`-minimum with a hotter conducting edge, a strictly antitone
response gives `teChargeResp ψ w θ i < 0` — the flipped sign of the
linear rule. -/
theorem teChargeResp_neg_of_strictAnti (ψ : ℝ → ℝ) (hψ : StrictAnti ψ)
    (w : V → V → ℝ) (hw0 : ∀ i j, 0 ≤ w i j) (θ : V → ℝ) (i : V)
    (hmin : ∀ j, θ i ≤ θ j)
    {j₀ : V} (hwpos : 0 < w i j₀) (hhot : θ i < θ j₀) :
    teChargeResp ψ w θ i < 0 := by
  have hmax : ∀ j, (ψ ∘ θ) j ≤ (ψ ∘ θ) i := by
    intro j
    show ψ (θ j) ≤ ψ (θ i)
    rcases (hmin j).eq_or_lt with h | h
    · rw [← h]
    · exact le_of_lt (hψ h)
  have h := teCharge_neg_of_max w hw0 (ψ ∘ θ) i hmax hwpos
    (show (ψ ∘ θ) j₀ < (ψ ∘ θ) i from hψ hhot)
  exact h

/-! ## TE-3 — TE-T5, the two-level Seebeck law

The seat's Seebeck law (scoping §4, TE-T5): for a two-level thermal
field — `θH` on a sector `H`, `θC` off it — the total charge
separated onto `H` is exactly `−(θH − θC) · W(∂H)`, where `W(∂H)`
is the boundary conductance, the total weight of the cut edges.
Interior edges cancel pairwise (both endpoints at the same level,
difference zero); only cut edges contribute, each carrying the full
drop. Separation onto a sector is **linear in the temperature drop
with an explicit, computable coefficient** — the finite Seebeck
coefficient of the seat, and the transport-form counterpart of
`ThermalProfileSeparation`'s two-level population law. Companion to
TE-T2: summed over the hot sector, the sign is pinned by `θH − θC`
alone, since `W(∂H) ≥ 0` (`teBoundaryConductance_nonneg`).

The header's fences stand unchanged over this section: this is a
mechanism exhibit for the separation primitive under the thread
name THERMOELECTROGRAVITIC — **not a gravity candidate, not a
response law, not Dial evidence** (K-TE-GRAV: Jeff's question stays
graded as a live external direction, never a premise), and the
gradient separation here is not `ChargeSeparationPost`'s
sector-expectation separation (K-TE-NAME). **NO CLAIM. Dials 0/4.
Dial 2 = 0.** -/

/-- **The boundary conductance** (new definition, TE-T5): the total
weight crossing the cut of `H`, `W(∂H) = ∑ i ∈ H, ∑ j ∉ H, w i j`.
The explicit coefficient of the two-level Seebeck law: a graph
quantity — no units exist at this tier and none are claimed. -/
def teBoundaryConductance (w : V → V → ℝ) (H : Finset V) : ℝ :=
  ∑ i ∈ H, ∑ j ∈ Hᶜ, w i j

/-- The boundary conductance is nonnegative for nonnegative
weights: every cut edge contributes a nonnegative weight. This is
the companion fact to TE-T2 for TE-T5: it makes the sign of the
separated total in `teCharge_twoLevel_sum` the sign of the drop
`θH − θC` alone. -/
theorem teBoundaryConductance_nonneg (w : V → V → ℝ)
    (hw0 : ∀ i j, 0 ≤ w i j) (H : Finset V) :
    0 ≤ teBoundaryConductance w H := by
  classical
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hw0 i j

/-- **The two-level thermal field** (TE-T5's configuration): the
field taking the value `θH` on the sector `H` and `θC` off it. -/
def teTwoLevel (H : Finset V) (θH θC : ℝ) : V → ℝ :=
  fun i => if i ∈ H then θH else θC

/-- **TE-T5 — the two-level Seebeck law.** For the two-level field
`teTwoLevel H θH θC`, the total charge separated onto the sector
`H` is `−(θH − θC) · W(∂H)`: linear in the temperature drop, with
the boundary conductance as its explicit, computable coefficient.
No symmetry or nonnegativity hypothesis is needed — the identity
is exact for arbitrary weights, because the interior-edge terms
vanish identically and each cut edge carries the full drop
`θH − θC`. -/
theorem teCharge_twoLevel_sum (w : V → V → ℝ) (H : Finset V)
    (θH θC : ℝ) :
    ∑ i ∈ H, teCharge w (teTwoLevel H θH θC) i
      = -(θH - θC) * teBoundaryConductance w H := by
  classical
  have hsite : ∀ i ∈ H, teCharge w (teTwoLevel H θH θC) i
      = -(θH - θC) * (∑ j ∈ Hᶜ, w i j) := by
    intro i hi
    have hiH : teTwoLevel H θH θC i = θH := by
      show (if i ∈ H then θH else θC) = θH
      exact if_pos hi
    rw [teCharge_apply]
    have hsplit : (∑ j, w i j * (teTwoLevel H θH θC i - teTwoLevel H θH θC j))
        = ∑ j ∈ Hᶜ, w i j * (θH - θC) := by
      rw [← Finset.sum_add_sum_compl H
        (fun j => w i j * (teTwoLevel H θH θC i - teTwoLevel H θH θC j))]
      have hH : (∑ j ∈ H, w i j * (teTwoLevel H θH θC i - teTwoLevel H θH θC j))
          = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hjH : teTwoLevel H θH θC j = θH := by
          show (if j ∈ H then θH else θC) = θH
          exact if_pos hj
        rw [hiH, hjH, sub_self, mul_zero]
      have hC : (∑ j ∈ Hᶜ, w i j * (teTwoLevel H θH θC i - teTwoLevel H θH θC j))
          = ∑ j ∈ Hᶜ, w i j * (θH - θC) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjC : teTwoLevel H θH θC j = θC := by
          show (if j ∈ H then θH else θC) = θC
          exact if_neg (Finset.mem_compl.mp hj)
        rw [hiH, hjC]
      rw [hH, hC, zero_add]
    rw [hsplit, ← Finset.sum_mul]
    ring
  calc ∑ i ∈ H, teCharge w (teTwoLevel H θH θC) i
      = ∑ i ∈ H, (-(θH - θC) * (∑ j ∈ Hᶜ, w i j)) :=
        Finset.sum_congr rfl hsite
    _ = -(θH - θC) * (∑ i ∈ H, ∑ j ∈ Hᶜ, w i j) := by
        rw [Finset.mul_sum]
    _ = -(θH - θC) * teBoundaryConductance w H := rfl

/-- **TE-T5, response form (the TE-T5 clause of TE-T6).** The
two-level law carried through a response `ψ`: the total charge
separated onto `H` under `teChargeResp ψ` is
`−(ψ θH − ψ θC) · W(∂H)` — the same law with the drop read through
`ψ`, for *every* `ψ` (no monotonicity needed: both levels are read
through the same function). Proved by the definitional bridge
`teChargeResp_eq`: the responded two-level field is the two-level
field of the responded levels. -/
theorem teChargeResp_twoLevel_sum (ψ : ℝ → ℝ) (w : V → V → ℝ)
    (H : Finset V) (θH θC : ℝ) :
    ∑ i ∈ H, teChargeResp ψ w (teTwoLevel H θH θC) i
      = -(ψ θH - ψ θC) * teBoundaryConductance w H := by
  classical
  have hfield : ψ ∘ teTwoLevel H θH θC
      = teTwoLevel H (ψ θH) (ψ θC) := by
    funext i
    show ψ (teTwoLevel H θH θC i) = teTwoLevel H (ψ θH) (ψ θC) i
    by_cases hi : i ∈ H <;> simp [teTwoLevel, hi]
  have hsum : (∑ i ∈ H, teChargeResp ψ w (teTwoLevel H θH θC) i)
      = ∑ i ∈ H, teCharge w (teTwoLevel H (ψ θH) (ψ θC)) i := by
    apply Finset.sum_congr rfl
    intro i _
    have h := congrFun (teChargeResp_eq ψ w (teTwoLevel H θH θC)) i
    rw [hfield] at h
    exact h
  rw [hsum]
  exact teCharge_twoLevel_sum w H (ψ θH) (ψ θC)

end ThetLogos
