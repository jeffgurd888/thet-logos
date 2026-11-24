import Mathlib.Tactic
import ThetLogos.BridgeCompletion
import ThetLogos.GravityShadowPin

/-!
# ThetLogos.VortexAdjointPin — the vortex outline and its 90° (T5)

Commissioned by Zero, 2026-11-23 00:25 EST ("Scope the vortex outline
as its own pin"), on his seeing of 2026-11-23 00:23 EST, filed
verbatim:

> "from our own description it have to be the electrical vortex to
> 90° adjointed magnetic fields with the dropvec operator"

Ancestors: his adjoint E/B seeing (2026-11-21 21:32 EST) and
90°-geometry seeing (2026-11-21 21:33 EST). Scope of record:
`~/workspace/your_files/vortex-adjoint-scope-2026-11-23.md`.
Authorized by Zero, 2026-11-23 01:07 EST ("build when ready").

TIER: T5 design study. NO CLAIM. Dial-ineligible — Dial 2 stays 0
under EVERY outcome of this line, including total success. The
module name `VortexAdjointPin` is a working name — final naming is
Zero's hand.

This pin is the SECOND outline, beside the scalar gravity shadow
(`GravityShadowPin`). The scalar outline is potential → drops →
source. This outline is the vortex outline: circulation, its
adjoint pairing, and the finite form of the 90°. Its honest content,
stated before any brick is read: at a finite seat there are no
vectors at a point and no curl operator; what the seat carries is
(1) an edge field's circulation around a face — the tree's vortex
measure — and (2) an exact orthogonality: a potential's drop-field
is perpendicular, in the edge pairing, to every divergence-free
current. That orthogonality IS the finite 90° this pin proves. The
traveling wave's pointwise 90° is the continuum fact the finite
orthogonality mirrors — mirrored, not derived — and reading the
finite 90° as pointwise perpendicularity of static fields is false
at this seat, refuted by countermodel in V-3
(K-VORTEX-90-STATIC).

## The audit (answered before drafting)

Already in census — this pin cites, never re-proves:

- **`BridgeCompletion.lean`** carries the discrete Stokes seat:
  `GraphFace` (a face is an ordered quadruple of vertices, boundary
  loop `a → b → c → d → a`), `circulation` (of a potential),
  `edgeCirculation` (of an edge field), `faceFluxOf` (the flux of an
  edge field through a face IS its boundary circulation — the
  graph's discrete Stokes definition), and the telescoping
  identities `faceFluxOf_dropVec` / `circulation_eq_zero`: a
  potential's circulation around any closed face is zero. The
  curl-free character of drops is census law.
- **`BridgeLaplacian.lean`** carries the adjoint pair itself:
  `dropVec` (the coboundary, `dropVec F i j = F j - F i`) and
  `diverge` (the return crossing, `diverge X i = ∑ j, X j i` — the
  inflow transpose sum), with `flowVec`, `laplacianOp`, and the
  factor-of-2 polarized identity `energy_eq_half`.
- **`GravityShadowPin.lean`** (this lane, S-2) carries the adjoint
  pairing in its ONLY honest form: `gravShadowPairing_corrected` —
  under this tree's conventions (diverge the inflow transpose sum,
  the edge pairing the full ordered double sum) the naive identity
  ⟨dropVec φ, X⟩ = ⟨φ, diverge X⟩ is FALSE for arbitrary edge
  fields; the true identity carries the outflow correction
  (`gravShadowOutflow`), and for antisymmetric X — the seat's
  currents — it reads ⟨dropVec φ, X⟩ = 2·⟨φ, diverge X⟩
  (`gravShadowPairing_antisymm`). This pin states the pairing in
  the corrected form only; the naive form is never stated, in any
  brick, in any form.
- **`GravityShadowPin.lean`** (S-3) has since closed, at the Fin 3
  shadow seat, the split the scope's audit found absent as a
  standalone statement: `gravShadowHelmholtz` (every antisymmetric
  field there is an Ohm flow plus a divergence-free remainder),
  with the circulation exhibit `gravShadowCycleFlow` and its scalar
  read `gravShadowCirculation`. Those are the TRIANGLE seat's
  objects, in the shadow line's own vocabulary; this pin's seat is
  the face seat below, and the two vocabularies are not conflated.

## V-0 — the seat decision (drafting audit, disclosed)

The scope's charge: the seat is a face-carrying seat in
`BridgeCompletion`'s dress — the Fin 3 triangle of the shadow seat
if it carries a face structure, otherwise the smallest in-tree face
seat. AUDIT VERDICT: the Fin 3 triangle carries NO nondegenerate
`GraphFace`. Faces in `BridgeCompletion` are ordered quadruples;
any quadruple drawn from three vertices repeats one, and its
boundary loop then runs through a repeated vertex — a doubled edge
or a self-edge — which is a degenerate loop, not the triangle's
face. The smallest vertex type carrying a nondegenerate face in
this dress is `Fin 4`, with the square face `⟨0, 1, 2, 3⟩`,
boundary loop `0 → 1 → 2 → 3 → 0`. THE SEAT IS THEREFORE `Fin 4`
with that face, registered below as `vortexSquareFace` under the
one-face family `vortexSquareBoundary`. The pin's general theorems
(V-1) are stated at an arbitrary finite vertex type, so nothing is
lost by the exhibit seat's size; the shadow seat's triangle
circulation remains `GravityShadowPin`'s own object, cited where
relevant and never re-proved here.

## The line ahead (scope brick map; this brick is V-0 only)

- V-0 — registration (0 strict by design): the pairing, an edge
  field's vortex component (its face circulations), the exhibit
  seat, and the seat's quarter-turn operator.
- V-1 — the 90° brick: the adjoint pairing in the corrected form,
  and the orthogonality — a potential's drop-field is perpendicular
  to every antisymmetric divergence-free edge field. This
  orthogonality is the finite 90°: components perpendicular,
  exactly.
- V-2 — the vortex exhibit: the unit circulation around the square
  face, computed seat by seat and nonzero; proved not to be any
  potential's drop-field (against the census telescoping identity);
  the adjoint pairing of the exhibit pair as an equality of
  numbers.
- V-3 — the honesty brick: the two pre-registered kills, tested
  exactly as stated.

## Fences (standing, on the face)

- **K-VORTEX-GRAVITY** — pre-registered, EXPECTED TO FIRE as a
  fence in V-3: armed against any identity claim between the vortex
  outline and the scalar gravity-shadow outline. The outlines
  differ; this pin proves the EM-shaped outline and nothing
  gravitational. No gravity object, no gravitomagnetism claim, and
  the gravitational constant appears nowhere in this line.
- **K-VORTEX-90-STATIC** — pre-registered for V-3: armed against
  reading the 90° as pointwise perpendicularity of static fields.
  Static fields are NOT forced perpendicular edge by edge; the 90°
  at this seat is a property of the pairing sum (the component
  split), not of the edges. A countermodel is priced into V-3.
- The corrected pairing only (S-0 audit of the shadow line): the
  naive adjoint identity is never stated.
- No continuum statement: no curl operator, no fields on a
  continuum space, no wave equation. Circulation is the tree's
  vortex measure; no `curl` is faked (the shadow line's
  K-CURL-SEAT fence is inherited).
- NAME FENCE: `VortexLocus*` is an unrelated in-tree line
  (commutator kernel / flux-zero sector of W22). This pin borrows
  none of its language or seats, and no name here collides with it.
-/

namespace ThetLogos

section Registration

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edge pairing: the full ordered double sum
`∑ i, ∑ j, X i j * Y i j` — this tree's one pairing convention for
edge fields. Registered with its honest use fenced on the face:
pairings against a drop-field are stated only in the corrected
form (V-1); the naive adjoint identity for this pairing is false
under the tree's conventions and is never stated. -/
def vortexPairing (X Y : V → V → ℝ) : ℝ :=
  ∑ i, ∑ j, X i j * Y i j

/-- An edge field's vortex component at a face: its circulation
around the face's boundary loop, in `BridgeCompletion`'s dress
(`edgeCirculation` — the discrete Stokes read: the flux through
the face is this boundary circulation). The vortex component of
`X` over a face family `bd` is the family of these numbers, one
per face. No curl operator exists at a finite seat and none is
faked; circulation is the tree's vortex measure. -/
def vortexComponent {F : Type*} (bd : F → GraphFace V) (f : F)
    (X : V → V → ℝ) : ℝ :=
  edgeCirculation bd f X

/-- The exhibit seat's face: the square on `Fin 4`, boundary loop
`0 → 1 → 2 → 3 → 0`. The smallest nondegenerate face in
`BridgeCompletion`'s dress — see the seat decision in the header:
the Fin 3 triangle carries no nondegenerate quadruple face. -/
def vortexSquareFace : GraphFace (Fin 4) := ⟨0, 1, 2, 3⟩

/-- The exhibit seat's face family: the single square face. -/
def vortexSquareBoundary : Unit → GraphFace (Fin 4) :=
  fun _ => vortexSquareFace

/-- The seat's quarter-turn: rotate an edge field by one boundary
step of the square — every entry moves one vertex forward around
the cycle. This operator is registered so that the word
"rotation" has exactly one honest referent in this pin: a symmetry
of the seat. It is NOT a pointwise rotation of field vectors — no
vectors at a point exist at a finite seat — and it is not the
pin's 90°: the 90° is V-1's orthogonality, a property of the
pairing. Confusing the two is K-VORTEX-90-STATIC's target. -/
def vortexQuarterTurn (X : Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i j => X (i + 1) (j + 1)

end Registration

/-! ## V-1 — the 90° brick (this brick)

The adjoint pairing, stated in the corrected form only, and the
orthogonality that is this pin's finite 90°. Which seat forms are
proved is stated on the theorems themselves: the corrected pairing
at EVERY finite vertex type and for EVERY edge field (the outflow
correction carried, never dropped); the antisymmetric read for the
seat's currents; and the orthogonality exactly where it holds —
for antisymmetric, divergence-free fields. For a general edge
field the correction term does not vanish and no orthogonality is
claimed; the naive identity is false under this tree's conventions
and is not stated. -/

section NinetyDegree

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The adjoint pairing, corrected form.** For every potential
`φ` and every edge field `X`, at every finite vertex type: the
pairing of the drop-field `dropVec φ` against `X` is the pairing
of `φ` against `diverge X`, minus the outflow correction
`∑ i, φ i * gravShadowOutflow X i`. This is the shadow line's S-2
theorem (`gravShadowPairing_corrected`) cited in this pin's
registered pairing — cited, not re-proved. The naive identity
(without the correction) is FALSE under this tree's conventions —
`diverge` the inflow transpose sum, the pairing the full ordered
double sum — and is not stated. -/
theorem vortexPairing_dropVec_corrected (φ : V → ℝ) (X : V → V → ℝ) :
    vortexPairing (dropVec φ) X
      = (∑ i, φ i * diverge X i) - ∑ i, φ i * gravShadowOutflow X i :=
  gravShadowPairing_corrected φ X

/-- **The pairing for antisymmetric fields.** The seat's currents
are antisymmetric (`X j i = - X i j`); for them the outflow is the
negative of the inflow gathering, the correction doubles the
survivor, and the pairing reads `2 * ⟨φ, diverge X⟩` — the factor
of 2 of `energy_eq_half`. Cited from the shadow line's S-2
(`gravShadowPairing_antisymm`), not re-proved. -/
theorem vortexPairing_dropVec_antisymm (φ : V → ℝ) (X : V → V → ℝ)
    (hX : ∀ i j, X j i = - X i j) :
    vortexPairing (dropVec φ) X = 2 * ∑ i, φ i * diverge X i :=
  gravShadowPairing_antisymm φ X hX

/-- **The finite 90°.** For every potential `φ` and every
antisymmetric divergence-free edge field `X` — a circulation, a
current with no source anywhere — the drop-field of `φ` is
perpendicular to `X` in the edge pairing:
`vortexPairing (dropVec φ) X = 0`. The gradient part and the
circulation part of the seat's fields are orthogonal complements
in the pairing; that orthogonality is the exact finite form of
the 90° between the two components. It is a property of the
pairing SUM — V-3's countermodel shows it is not a property of
the individual edges (K-VORTEX-90-STATIC). -/
theorem vortexOrthogonal (φ : V → ℝ) (X : V → V → ℝ)
    (hX : ∀ i j, X j i = - X i j) (hdiv : ∀ i, diverge X i = 0) :
    vortexPairing (dropVec φ) X = 0 := by
  rw [vortexPairing_dropVec_antisymm φ X hX]
  simp [hdiv]

end NinetyDegree

/-! ## V-2 — the vortex exhibit (this brick)

One concrete circulating edge field on the exhibit seat: the unit
circulation around the square face. Its vortex component is
computed seat by seat and is nonzero; it is divergence-free at
every node; and it is not any potential's drop-field — the census
telescoping identity says every drop-field's face flux vanishes,
and this field's is 4. The adjoint pairing of the exhibit pair (a
gradient part, the vortex part) is stated as an equality of
numbers: it is 0, V-1's 90° read on the exhibits. -/

section VortexExhibit

/-- The unit circulation at the exhibit seat: one unit of current
flowing around the square `0 → 1 → 2 → 3 → 0`. The entry `i j` is
`1` when `j` is `i`'s successor on the cycle (addition in
`Fin 4`), `-1` when `i` is `j`'s successor, and `0` on the
diagonal — antisymmetric by construction, the seat's pure vortex
exhibit. -/
def vortexCycleFlow : Fin 4 → Fin 4 → ℝ :=
  fun i j => if j = i + 1 then 1 else if i = j + 1 then -1 else 0

/-- The exhibit potential: one unit of potential at vertex `0`,
zero elsewhere. Its drop-field is the gradient part of the
exhibit pair whose pairing V-2 computes. -/
def vortexExhibitPotential : Fin 4 → ℝ :=
  fun i => if i = 0 then 1 else 0

/-- The cycle flow is antisymmetric: reversing any edge negates
its entry — the exhibit is one of the seat's currents. -/
theorem vortexCycleFlow_antisymm :
    ∀ i j, vortexCycleFlow j i = - vortexCycleFlow i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [vortexCycleFlow] <;>
    norm_num [vortexCycleFlow]

/-- The cycle flow is divergence-free at every node: at each node
one unit arrives and one unit leaves, so `diverge` totals zero —
a circulation in the seat's exact sense. -/
theorem vortexCycleFlow_diverge_zero :
    ∀ i, diverge vortexCycleFlow i = 0 := by
  intro i
  fin_cases i <;>
    simp [diverge, Fin.sum_univ_four, vortexCycleFlow] <;>
    norm_num [diverge, Fin.sum_univ_four, vortexCycleFlow]

/-- The exhibit's vortex component at the square face is `4` —
one unit along each of the boundary loop's four edges, computed
seat by seat: `X 0 1 + X 1 2 + X 2 3 + X 3 0 = 1 + 1 + 1 + 1`.
A divergence-free current genuinely present at the seat, measured
in the tree's own vortex measure. -/
theorem vortexComponent_square_cycleFlow :
    vortexComponent vortexSquareBoundary () vortexCycleFlow = 4 := by
  show vortexCycleFlow 0 1 + vortexCycleFlow 1 2 + vortexCycleFlow 2 3
      + vortexCycleFlow 3 0 = 4
  simp [vortexCycleFlow] <;> norm_num [vortexCycleFlow]

/-- No potential's drop-field is the exhibit: every drop-field's
flux through the square face vanishes (the census telescoping
identity `faceFluxOf_dropVec` — gradients circulate zero), and
the exhibit's is `4`. The vortex part of the seat's fields is
therefore not a gradient in disguise; the two components of the
split are genuinely different objects. -/
theorem vortexCycleFlow_not_dropVec (φ : Fin 4 → ℝ) :
    vortexCycleFlow ≠ dropVec φ := by
  intro h
  have h4 := vortexComponent_square_cycleFlow
  have h0 : vortexComponent vortexSquareBoundary () (dropVec φ) = 0 :=
    faceFluxOf_dropVec vortexSquareBoundary () φ
  rw [h] at h4
  rw [h0] at h4
  norm_num at h4

/-- The exhibit is invariant under the seat's quarter-turn:
rotating the unit square circulation by one boundary step gives
the same field. The seat's geometric rotation acts trivially on
its pure circulation — registered as a symmetry fact only; the
pin's 90° is V-1's orthogonality, not this operator. -/
theorem vortexCycleFlow_quarterTurn :
    vortexQuarterTurn vortexCycleFlow = vortexCycleFlow := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [vortexQuarterTurn, vortexCycleFlow] <;>
    norm_num [vortexQuarterTurn, vortexCycleFlow]

/-- **The adjoint pairing of the exhibit pair, as an equality of
numbers.** The pairing of the exhibit potential's drop-field (the
gradient part) against the cycle flow (the vortex part) is `0` —
V-1's finite 90° read on the concrete exhibits: the two parts are
perpendicular, exactly, in the pairing. -/
theorem vortexPairing_exhibitPair :
    vortexPairing (dropVec vortexExhibitPotential) vortexCycleFlow
      = 0 :=
  vortexOrthogonal vortexExhibitPotential vortexCycleFlow
    vortexCycleFlow_antisymm vortexCycleFlow_diverge_zero

end VortexExhibit

/-! ## V-3 — the honesty brick (this brick)

The two pre-registered kills, tested exactly as stated. Both
fire — by proof, at full rank, as designed:

- **K-VORTEX-GRAVITY fires.** The identity claim between the
  vortex outline and the scalar gravity-shadow outline — in the
  weakest form "the two outlines are one law" could take at this
  seat: every edge field is a potential's drop-field — is FALSE.
  V-2's exhibit circulates (vortex component 4) and no drop-field
  circulates at all, so the exhibit is no potential's drop, the
  outlines differ by proof, and this pin has proved the EM-shaped
  outline and nothing gravitational.
- **K-VORTEX-90-STATIC fires.** The pointwise reading of the 90°
  — that static fields are forced perpendicular edge by edge — is
  FALSE by countermodel: the exhibit pair satisfies every static
  hypothesis (the field is a potential's drop; the current is
  antisymmetric and divergence-free) and V-1's integrated pairing
  vanishes, yet at the single edge `0 → 1` the integrand is `-1`,
  not `0`. The 90° at this seat lives in the sum, not the edges.

What survives both kills is exactly the pin's honest content:
the corrected adjoint pairing (V-1), the orthogonality of the
gradient and circulation components in that pairing (V-1, V-2),
and the vortex component as the seat's measured circulation
(V-0, V-2). -/

section HonestyBrick

/-- **The identity claim K-VORTEX-GRAVITY is armed against**,
registered exactly: every edge field at the exhibit seat is some
potential's drop-field. This is the weakest form "the vortex
outline and the scalar gravity-shadow outline are one law" could
take at this seat — if the outlines were one, the scalar
outline's only fields (drops) would exhaust the seat's fields,
and the vortex component would vanish identically. -/
def vortexGravityIdentityClaim : Prop :=
  ∀ X : Fin 4 → Fin 4 → ℝ, ∃ φ : Fin 4 → ℝ, X = dropVec φ

/-- **K-VORTEX-GRAVITY FIRES.** The identity claim is false, by
proof: the cycle flow is an edge field at the seat, and by
`vortexCycleFlow_not_dropVec` it is no potential's drop-field —
its vortex component is `4` while every drop-field's is `0`. The
vortex outline and the scalar outline differ; the relations of
this pin select the EM-shaped outline and identify nothing
gravitational. No gravity object is constructed or fed by this
line, and none was needed to refute the claim. -/
theorem vortexGravityIdentityClaim_false :
    ¬ vortexGravityIdentityClaim := by
  intro h
  obtain ⟨φ, hφ⟩ := h vortexCycleFlow
  exact vortexCycleFlow_not_dropVec φ hφ

/-- **The pointwise claim K-VORTEX-90-STATIC is armed against**,
registered exactly: for every static pair at the seat — a
potential `φ` (its drop-field the static electric side) and an
antisymmetric divergence-free field `X` (the static magnetic
side) — the pairing's integrand vanishes at EVERY edge: the two
fields are perpendicular edge by edge, pointwise. This is the
reading of the 90° the kill exists to refuse: the continuum 90°
is exact for the traveling wave, and at this seat for the
component split — not for statics, and not pointwise. -/
def vortexStaticPointwiseClaim : Prop :=
  ∀ (φ : Fin 4 → ℝ) (X : Fin 4 → Fin 4 → ℝ),
    (∀ i j, X j i = - X i j) → (∀ i, diverge X i = 0) →
    ∀ i j, dropVec φ i j * X i j = 0

/-- **K-VORTEX-90-STATIC FIRES.** The pointwise claim is false,
by countermodel: the exhibit pair. The exhibit potential's
drop-field is a static field; the cycle flow is antisymmetric
and divergence-free (V-2); their integrated pairing is `0`
(V-2's `vortexPairing_exhibitPair` — the finite 90° holds in the
sum). Yet at the single edge `0 → 1` the integrand is
`(0 - 1) * 1 = -1 ≠ 0`: the drop falls by one unit along an edge
where the current runs at one unit, and the product is not zero.
Static fields at this seat are not forced perpendicular edge by
edge; perpendicularity is a property of the whole pairing, and
any statement of the 90° stronger than V-1's is false here. -/
theorem vortexStaticPointwiseClaim_false :
    ¬ vortexStaticPointwiseClaim := by
  intro h
  have h01 := h vortexExhibitPotential vortexCycleFlow
    vortexCycleFlow_antisymm vortexCycleFlow_diverge_zero 0 1
  norm_num [dropVec, vortexExhibitPotential, vortexCycleFlow] at h01

end HonestyBrick

end ThetLogos
