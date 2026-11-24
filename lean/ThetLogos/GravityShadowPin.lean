import Mathlib.Tactic
import ThetLogos.BridgeLaplacian

/-!
# ThetLogos.GravityShadowPin — the shadow of the gravity object (T5)

Commissioned by Zero, 2026-11-22 11:36–11:37 EST. Zero's words: the
vector-calculus visual guide he dropped was "an outline for a shadow
of the gravity object"; on the assimilation ledger he ruled "scope it
for intuition." Scope of record:
`~/workspace/your_files/gravity-shadow-scope-2026-11-22.md`.

TIER: T5 design study. NO CLAIM. Dials 0/4 — Dial 2 (derived gravity
object) stays 0 under EVERY outcome of this line, including total
success. "Shadow" is Zero's word and the working label; the module
name `GravityShadowPin` is a working name — final naming is his hand.

A shadow is the outline an object casts on a wall it never touches.
Our wall is the finite seats. The outline of a would-be gravity
field, drawn on that wall with the only drawing tools the corpus
owns — the binary adjoint pair — is: a scalar seat weighting read as
the potential's shadow (φ), its gradient (`dropVec φ`) read as the
field's shadow, its Laplacian (`laplacianOp φ`) read as the source's
shadow, with the rim of the outline closed by the finite boundary
theorem and the unseen part carried by circulation. In continuum
dress this is Poisson's equation, ∇²φ = source — the Newtonian field
equation. Its finite shadow is the strongest honest form the
intuition can take in-tree: the shape of a potential theory,
exhibited seat by seat. It is the shape of EVERY potential theory —
which is exactly what the honesty brick (S-4) proves, and why the
shadow can never be sold as the object.

## S-0 — the audit (this brick's first charge, answered before drafting)

- **`BridgeLaplacian.lean` (census)** carries the drawing tools:
  `dropVec` (line 128, the coboundary `d`), `ohm` (the conductance
  factor `σ`), `diverge` (line 140, the return crossing `dᵀ`),
  `flowVec`, `laplacianOp` — with the factorization
  `laplacianOp_eq_diverge_ohm_drop` and `laplacianOp_eq_diverge_flow`
  proved (Δ = div ∘ flow), both Kirchhoff laws, the polarized energy
  identity `bilin_identity`, `energy_identity`, the self-adjointness
  of the composite `laplacianOp_symm_form`, and the kernel route
  `eq_const_of_energy_eq_zero`.
- **`ThermalChargePoisson.lean` (census)** carries the general
  discrete Poisson theory on the Bridge seat:
  `exists_potential_iff_sum_eq_zero` (a potential exists iff the
  total charge vanishes), `discrete_poisson`, uniqueness of the
  potential up to an additive constant, and uniqueness of the field
  (`dropVec_eq_of_laplacianOp_eq`) and the Ohm flow on the nose. It
  does NOT exhibit a concrete point source at a concrete seat with
  the potential computed seat by seat — so S-1 remains a concrete
  exhibit brick, citing this theory as its backdrop, not a pure
  citation brick.
- **`PoissonTotalMassBlindness.lean` (census)** carries the standing
  fence in class form: every quantity factoring through
  `ThermalChargePoisson`'s output sees only the mean-subtracted
  source contrast; total mass is invisible at the seat. This line
  inherits that fence untouched.
- **THE ADJOINT PAIRING — AUDIT VERDICT: ABSENT as a standalone
  statement.** The open question was whether the summation-by-parts
  pairing ⟨dropVec φ, X⟩ = ⟨φ, diverge X⟩ is already proved anywhere
  in the Bridge family. Searched in both trees (this lane tree and
  the census tree): NO theorem anywhere states a pairing between
  `dropVec` and `diverge` for a general edge field `X`. The nearest
  material is composite-level only: `bilin_identity` /
  `energy_identity` (the Ohm flow paired against a drop, with the
  factor of 2 below), `laplacianOp_symm_form` (self-adjointness of
  the composite `L`), `BridgeCompletion`'s `lapLin_isSymmetric`,
  and `BridgeMagnetic`'s `magLap_eq_diverge_ohm_drop` (the
  factorization ported to ℂ). CONSEQUENCE: the pairing cannot be
  cited — **S-2 carries it**, as the scope priced.
- **CONVENTION WARNING (priced into S-2).** Under this tree's
  conventions — `diverge` the inflow transpose sum, the edge pairing
  the full ordered double sum — the naive identity
  ⟨dropVec φ, X⟩ = ⟨φ, diverge X⟩ does NOT hold for arbitrary edge
  fields `X`. The true identity carries an outflow correction:
  ⟨dropVec φ, X⟩ = ⟨φ, diverge X⟩ − ∑ i, φ i * (∑ j, X i j); and for
  antisymmetric `X` — the seat's currents — it reads
  ⟨dropVec φ, X⟩ = 2 * ⟨φ, diverge X⟩, the same factor of 2 that
  `energy_eq_half` carries. S-2 must state the pairing in a
  corrected form; the uncorrected form is FALSE at this seat and
  must not be stated.

## S-0 — the seat and the three readings (registration, 0 strict by design)

THE SEAT: `Fin 3` — the smallest seat carrying a cycle and a
boundary. On three vertices the cycle closes (0 → 1 → 2 → 0) and
every proper nonempty region has edges crossing its rim; the
two-vertex "cycle" is a doubled edge, degenerate. The seat's
conductances `gravShadowWeight` are unit off the diagonal and zero
on it — on `Fin 3` the 3-cycle IS the complete graph — hence
symmetric, nonnegative, and strictly positive off the diagonal:
exactly the hypotheses `ThermalChargePoisson`'s theory and
`BridgeLaplacian`'s kernel route consume, so later bricks can cite
them at this seat.

THE THREE READINGS, registered under frozen names:
`gravShadowPotential` (a scalar seat weighting, read as the
potential's shadow — the reading is the weighting itself, registered
under its reading name so the line's bricks cite the reading, not
the raw function), `gravShadowField` (its gradient: the
field-shadow), `gravShadowSource` (its Laplacian at the seat: the
source-shadow). In continuum dress: φ, ∇φ, ∇²φ = source.

## The line ahead (scope brick map; this brick is S-0 only)

- S-1 — the Poisson seat: a concrete point source at this seat with
  Δφ = source exhibited and φ computed seat by seat, citing
  `ThermalChargePoisson` as backdrop.
- S-2 — the boundary rim: the finite divergence theorem at the seat
  (region sum of `diverge X` = flux across the region's boundary),
  PLUS the adjoint pairing, which the audit found ABSENT — stated in
  the corrected form the convention warning prices.
- S-3 — circulation and the split (stretch): div-free edge fields at
  the seat, one nonzero circulation exhibited, the finite Helmholtz
  split.
- S-4 — the honesty brick: (a) kernel of `dropVec` at the seat =
  the constants; (b) the universality theorem.

## Fences (standing, on the face)

- **K-SHADOW-IDENTITY** — pre-registered, EXPECTED TO FIRE as
  S-4(b)'s theorem: the claim "these relations pick out gravity"
  dies by proof — the relations hold for all potentials, so they
  identify no object.
- **K-SHADOW-OBJECT** (fence): no gravity object, no G, no
  continuum field, no Einstein slot is constructed or fed by this
  line. Dial 2 stays 0.
- **K-CURL-SEAT** (fence): no curl operator exists at a finite seat
  and none will be faked; circulation (div-free flow) is the only
  honest seat.
- The albedo verdict stands untouched: gravity ≠ total thermal
  albedo loss (K-ALB-EQ, banked on the L2 lane). The shadow is not
  a back door around it.
- FRONTIER, never priced: the continuum limit of the shadow
  (Dial 3), any derivation of G, any coupling of the shadow to
  inertia or time (the U-INERTIA-0 gate is a separate line).
-/

namespace ThetLogos

/-- The shadow seat's conductances: the 3-cycle on `Fin 3` — unit
conductance across every distinct pair (on three vertices the cycle
and the complete graph coincide), zero on the diagonal. Symmetric,
nonnegative, strictly positive off the diagonal. -/
def gravShadowWeight : Fin 3 → Fin 3 → ℝ :=
  fun i j => if i = j then 0 else 1

/-- The potential-shadow reading: a scalar seat weighting on
`Fin 3`, read as the potential's shadow. The reading is the
weighting itself, registered under its reading name so the line's
bricks cite the reading, not the raw function. -/
def gravShadowPotential (φ : Fin 3 → ℝ) : Fin 3 → ℝ := φ

/-- The field-shadow reading: the gradient (drop) of the
potential-shadow — an edge field on the seat. -/
def gravShadowField (φ : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  dropVec (gravShadowPotential φ)

/-- The source-shadow reading: the Laplacian of the potential-shadow
at the seat's conductances — a node function on the seat. In
continuum dress, `gravShadowSource φ = gravShadowPotential φ`'s
Poisson source: ∇²φ = source. -/
def gravShadowSource (φ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  laplacianOp gravShadowWeight (gravShadowPotential φ)

end ThetLogos
