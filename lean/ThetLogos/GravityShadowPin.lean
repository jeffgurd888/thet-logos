import Mathlib.Tactic
import ThetLogos.BridgeLaplacian
import ThetLogos.ThermalChargePoisson

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

/-! ## S-1 — the Poisson seat (the exhibit)

THE EXHIBIT. The audit (S-0) found the general Poisson theory
standing in `ThermalChargePoisson` — a potential exists iff the
total charge vanishes, unique up to a constant, its field unique on
the nose — but no concrete seat-by-seat exhibit anywhere. This brick
is that exhibit, at this line's seat (`Fin 3`, `gravShadowWeight`).

THE SOURCE IS A CONTRAST, AND THE FACE SAYS SO. The point source is
`gravShadowPointSource` = δ₀ − 1/3: value 2/3 at node 0, −1/3 at
nodes 1 and 2. A bare delta δ₀ admits NO potential at this seat — by
the census current law (`exists_potential_iff_sum_eq_zero`, the (⇒)
direction) a potential's source always totals zero, and δ₀ totals 1.
And `PoissonTotalMassBlindness` fences the reading: the seat sees
only the mean-subtracted contrast; the uniform background subtracted
here is exactly the invisible part. The exhibit therefore carries
the contrast, never the bare point mass.

THE POTENTIAL, SEAT BY SEAT. `gravShadowExhibitPotential` is
φ = (2/9, −1/9, −1/9) — itself a contrast (it totals zero: the
mean-zero representative of its constant class), and
`gravShadowSource φ = gravShadowPointSource` is PROVED below as an
equality of functions, computed seat by seat: at node 0 the two unit
edges each drop 1/3, totalling 2/3; at each rim node the single
conducting drop is −1/3. The backdrop weld then cites the census
theory at this seat: any other potential for the same source differs
from φ by a constant, and its field-shadow equals φ's field-shadow
on the nose. -/

/-- The point source at the seat: the mean-subtracted contrast
δ₀ − 1/3 on `Fin 3` — value `2/3` at node `0`, `-1/3` at the rim
nodes. A bare delta admits no potential (its total is 1, and a
potential's source always totals zero); the seat sees only this
contrast (`PoissonTotalMassBlindness`). -/
noncomputable def gravShadowPointSource : Fin 3 → ℝ :=
  fun i => if i = 0 then 2 / 3 else -1 / 3

/-- The exhibited potential for `gravShadowPointSource`: seat by
seat, `φ 0 = 2/9`, `φ 1 = φ 2 = -1/9`. It totals zero — the
mean-zero representative of its constant class. -/
noncomputable def gravShadowExhibitPotential : Fin 3 → ℝ :=
  fun i => if i = 0 then 2 / 9 else -1 / 9

/-- Compatibility at the seat: the point source totals zero — the
hypothesis the census Poisson iff consumes. -/
theorem gravShadowPointSource_sum_eq_zero :
    ∑ i, gravShadowPointSource i = 0 := by
  rw [Fin.sum_univ_three]
  have h0 : gravShadowPointSource 0 = 2 / 3 := if_pos rfl
  have h1 : gravShadowPointSource 1 = -1 / 3 := if_neg (by decide)
  have h2 : gravShadowPointSource 2 = -1 / 3 := if_neg (by decide)
  rw [h0, h1, h2]
  norm_num

/-- The potential, computed seat by seat. -/
theorem gravShadowExhibitPotential_values :
    gravShadowExhibitPotential 0 = 2 / 9 ∧
    gravShadowExhibitPotential 1 = -1 / 9 ∧
    gravShadowExhibitPotential 2 = -1 / 9 :=
  ⟨if_pos rfl, if_neg (by decide), if_neg (by decide)⟩

/-- **The Poisson equation at the seat.** The source-shadow of the
exhibited potential IS the point source: `Δφ = δ₀ − 1/3`, as an
equality of functions on `Fin 3`, computed seat by seat. -/
theorem gravShadowSource_exhibitPotential :
    gravShadowSource gravShadowExhibitPotential = gravShadowPointSource := by
  funext i
  fin_cases i <;>
    simp only [gravShadowSource, gravShadowPotential, laplacianOp,
      Fin.sum_univ_three] <;>
    norm_num [gravShadowWeight, gravShadowExhibitPotential,
      gravShadowPointSource]

/-- **The backdrop weld.** The census Poisson theory
(`ThermalChargePoisson`), cited at this seat: any potential whose
source-shadow is the point source differs from the exhibited
potential by an additive constant, and its field-shadow equals the
exhibited field-shadow on the nose. -/
theorem gravShadowExhibit_weld (φ' : Fin 3 → ℝ)
    (hφ' : gravShadowSource φ' = gravShadowPointSource) :
    (∃ c : ℝ, ∀ i, φ' i = gravShadowExhibitPotential i + c) ∧
    gravShadowField φ' = gravShadowField gravShadowExhibitPotential := by
  have hw : ∀ i j, gravShadowWeight i j = gravShadowWeight j i := by
    intro i j
    by_cases h : i = j
    · simp [gravShadowWeight, h]
    · simp [gravShadowWeight, h, Ne.symm h]
  have hw0 : ∀ i j, 0 ≤ gravShadowWeight i j := by
    intro i j
    by_cases h : i = j <;> simp [gravShadowWeight, h]
  have hpos : ∀ i j, i ≠ j → 0 < gravShadowWeight i j := by
    intro i j h
    simp [gravShadowWeight, h]
  have hL : laplacianOp gravShadowWeight φ'
      = laplacianOp gravShadowWeight gravShadowExhibitPotential := by
    have h1 : laplacianOp gravShadowWeight φ' = gravShadowPointSource := hφ'
    have h2 : laplacianOp gravShadowWeight gravShadowExhibitPotential
        = gravShadowPointSource := gravShadowSource_exhibitPotential
    rw [h1, h2]
  constructor
  · exact exists_add_const_of_laplacianOp_eq gravShadowWeight hw hw0 hpos
      gravShadowExhibitPotential φ' hL.symm
  · exact dropVec_eq_of_laplacianOp_eq gravShadowWeight hw hw0 hpos
      gravShadowExhibitPotential φ' hL.symm

/-! ## S-2 — the boundary rim (this brick)

THE RIM, CLOSED TWO WAYS. This brick carries the two statements
S-0's audit left to it, both in the corrected form the audit
priced:

1. **The adjoint pairing, corrected.** The audit's CONVENTION
   WARNING stands on this module's face: under this tree's
   conventions — `diverge` the inflow transpose sum
   (`diverge X i = ∑ j, X j i`), the edge pairing the full ordered
   double sum — the naive identity ⟨dropVec φ, X⟩ = ⟨φ, diverge X⟩
   is FALSE for a general edge field `X`, and it is NOT stated
   here. The true identity carries the outflow correction
   (`gravShadowPairing_corrected`): what `diverge` gathers in
   (`X j i`), the pairing also spends out (`X i j`), and the
   difference is the outflow term `∑ i, φ i * gravShadowOutflow X i`.
   For antisymmetric `X` — the seat's currents, the Ohm flows among
   them — inflow and outflow are negatives of each other and the
   correction doubles the surviving term
   (`gravShadowPairing_antisymm`): the pairing reads
   `2 * ⟨φ, diverge X⟩`, the same factor of 2 `energy_eq_half`
   carries. Both statements are convention identities: they hold
   for every finite vertex type, every weighting `φ`, and every
   edge field `X` (antisymmetric, for the second) — the seat
   `Fin 3` is the instance this line reads.

2. **The finite divergence theorem** (`gravShadowDivergence_rim`):
   for an antisymmetric edge field and any region `S`, the region
   total of `diverge X` equals the rim flux `gravShadowRimFlux S X`
   — the entries `X j i` with `i` inside and `j` outside, in the
   orientation `diverge` gathers. The interior edges cancel in
   pairs: over `S × S` the field's entries sum to their own
   negative by antisymmetry, hence to zero. Antisymmetry is a real
   hypothesis, not decoration: for a general field the interior
   sum survives and the rim alone does not close the outline. The
   weld (`gravShadowSource_rimFlux`) spends the theorem on the
   seat's own current: the Ohm flow of a potential is
   antisymmetric (symmetric conductances), so the total
   source-shadow over any region equals the rim flux of its
   field-shadow's flow — the outline's rim, closed on the line's
   own objects, via the census factorization
   `laplacianOp_eq_diverge_flow` cited, not re-proved.

NOTHING HERE REACHES FOR S-4. The kernel of `dropVec` and the
universality theorem are the honesty brick's charges, untouched.
K-SHADOW-IDENTITY stays pre-registered, unfired. -/

section BoundaryRim

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The outflow of an edge field at a node: the row sum
`∑ j, X i j` — everything `X` sends out of `i`, gathered WITHOUT
the transpose `diverge` applies (`diverge X i = ∑ j, X j i`
gathers what arrives). The difference between the two gatherings
is the correction term of the adjoint pairing. -/
def gravShadowOutflow (X : V → V → ℝ) (i : V) : ℝ := ∑ j, X i j

/-- The flux of an edge field across the rim of a region `S`, in
the orientation `diverge` gathers: the sum of the entries `X j i`
with `i` inside the region and `j` outside it. -/
def gravShadowRimFlux (S : Finset V) (X : V → V → ℝ) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ Sᶜ, X j i

/-- **The adjoint pairing, corrected form.** For every weighting
`φ` and every edge field `X`: the full ordered pairing of the
field-shadow `dropVec φ` against `X` is the pairing of `φ`
against `diverge X`, minus the outflow correction. The naive
identity (without the correction) is FALSE under this tree's
conventions — S-0's convention warning — and is not stated. -/
theorem gravShadowPairing_corrected (φ : V → ℝ) (X : V → V → ℝ) :
    (∑ i, ∑ j, dropVec φ i j * X i j)
      = (∑ i, φ i * diverge X i) - ∑ i, φ i * gravShadowOutflow X i := by
  have hL : (∑ i, ∑ j, dropVec φ i j * X i j)
      = (∑ i, ∑ j, φ j * X i j) - ∑ i, ∑ j, φ i * X i j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [dropVec_apply]
    ring
  have hIn : (∑ i, ∑ j, φ j * X i j) = ∑ j, φ j * diverge X j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [diverge_apply, Finset.mul_sum]
  have hOut : (∑ i, ∑ j, φ i * X i j)
      = ∑ i, φ i * gravShadowOutflow X i := by
    apply Finset.sum_congr rfl
    intro i _
    show (∑ j, φ i * X i j) = φ i * ∑ j, X i j
    rw [Finset.mul_sum]
  rw [hL, hIn, hOut]

/-- **The adjoint pairing for antisymmetric fields.** The seat's
currents are antisymmetric (`X j i = - X i j`); for them the
outflow is the negative of the inflow gathering, the correction
term doubles the survivor, and the pairing reads
`2 * ⟨φ, diverge X⟩` — the factor of 2 of `energy_eq_half`. -/
theorem gravShadowPairing_antisymm (φ : V → ℝ) (X : V → V → ℝ)
    (hX : ∀ i j, X j i = - X i j) :
    (∑ i, ∑ j, dropVec φ i j * X i j)
      = 2 * ∑ i, φ i * diverge X i := by
  have hdiv : ∀ i, diverge X i = - gravShadowOutflow X i := by
    intro i
    rw [diverge_apply]
    show (∑ j, X j i) = - ∑ j, X i j
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact hX i j
  have hrel : (∑ i, φ i * gravShadowOutflow X i)
      = -∑ i, φ i * diverge X i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hout : gravShadowOutflow X i = - diverge X i := by
      rw [hdiv i, neg_neg]
    rw [hout, mul_neg]
  rw [gravShadowPairing_corrected, hrel]
  ring

/-- **The finite divergence theorem.** For an antisymmetric edge
field `X` and any region `S`, the region total of the divergence
is the flux across the region's rim: the interior edges cancel in
pairs (over `S × S` the entries sum to their own negative, hence
to zero), and only the crossings survive. -/
theorem gravShadowDivergence_rim (X : V → V → ℝ)
    (hX : ∀ i j, X j i = - X i j) (S : Finset V) :
    (∑ i ∈ S, diverge X i) = gravShadowRimFlux S X := by
  have hInt : (∑ i ∈ S, ∑ j ∈ S, X j i) = 0 := by
    have hswap : (∑ i ∈ S, ∑ j ∈ S, X j i)
        = ∑ i ∈ S, ∑ j ∈ S, X i j := Finset.sum_comm
    have hneg : (∑ i ∈ S, ∑ j ∈ S, X i j)
        = -∑ i ∈ S, ∑ j ∈ S, X j i := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      exact hX j i
    linarith
  show (∑ i ∈ S, diverge X i) = ∑ i ∈ S, ∑ j ∈ Sᶜ, X j i
  have hsplit : ∀ i ∈ S, diverge X i
      = (∑ j ∈ S, X j i) + ∑ j ∈ Sᶜ, X j i := by
    intro i _
    rw [diverge_apply, ← Finset.sum_add_sum_compl S (fun j => X j i)]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hInt,
    zero_add]

/-- **The rim weld on the line's own objects.** The Ohm flow of a
potential under symmetric conductances is antisymmetric, so the
divergence theorem closes on it: the total source-shadow
(`laplacianOp w φ`) over any region equals the rim flux of the
field-shadow's flow. The census factorization
`laplacianOp_eq_diverge_flow` is cited, not re-proved. -/
theorem gravShadowSource_rimFlux (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (φ : V → ℝ) (S : Finset V) :
    (∑ i ∈ S, laplacianOp w φ i)
      = gravShadowRimFlux S (flowVec w φ) := by
  have hanti : ∀ i j, flowVec w φ j i = - flowVec w φ i j :=
    fun i j => flowVec_antisymm w hw φ j i
  have hstep : (∑ i ∈ S, laplacianOp w φ i)
      = ∑ i ∈ S, diverge (flowVec w φ) i :=
    Finset.sum_congr rfl (fun i _ =>
      congrFun (laplacianOp_eq_diverge_flow w hw φ) i)
  rw [hstep]
  exact gravShadowDivergence_rim (flowVec w φ) hanti S

end BoundaryRim

/-! ## S-3 — circulation and the split (this brick)

THE PART NO POTENTIAL CAN CAST. S-2 closed the rim: for an
antisymmetric edge field — a current — what a region's divergence
totals is exactly what crosses its rim. This brick names what
lives inside the rim when the divergence vanishes altogether:
circulation, curl's ghost at the seat (K-CURL-SEAT: no curl
operator exists here and none is faked; a divergence-free
antisymmetric field IS the honest finite seat of circulation).

THE EXHIBIT. `gravShadowCycleFlow` is the unit circulation around
the seat's 3-cycle: one unit flowing `0 → 1 → 2 → 0`, antisymmetric
by construction (the reverse entries carry `-1`, the diagonal and
the chords — there are none on three vertices — carry `0`). It is
divergence-free at every node (what arrives, leaves:
`gravShadowCycleFlow_diverge_zero`), and its circulation — the
forward rim sum `gravShadowCirculation`, the entries along the
cycle read in the direction of flow — is `3`, not zero
(`gravShadowCirculation_cycleFlow`): a divergence-free current
that is genuinely there, measured, not gestured at. No
field-shadow can produce it: the circulation of any `dropVec φ`
around the closed cycle telescopes to zero
(`gravShadowCirculation_dropVec`), so the cycle flow is not the
field-shadow of any potential — nor, the split adds, of any Ohm
flow either, since those are field-shadows dressed by the seat's
unit conductances.

THE SPLIT (`gravShadowHelmholtz`). Every antisymmetric edge field
at the seat decomposes as the Ohm flow of a potential — the
gradient part, `flowVec gravShadowWeight φ`, the field-shadow of
`φ` under the seat's conductances — plus an antisymmetric
divergence-free remainder, the circulation part. The proof is the
seat's own Poisson theory, cited not re-proved: an antisymmetric
field's total divergence vanishes (the S-2 interior-cancellation
argument read at the whole seat), so `exists_potential_of_sum_eq_zero`
hands back a potential whose Laplacian is the field's divergence;
the remainder then has divergence zero by construction, and it
stays antisymmetric because both summands are. The split is
stated for antisymmetric fields only — the seat's currents — and
that restriction is the tree's conventions speaking, not a gap
being hidden: `diverge` gathers transposed entries, and it is
antisymmetry that makes the total divergence vanish and the rim
close (S-2). A general field's symmetric part is a different
animal and this brick does not name it.

NOT THIS BRICK'S NEIGHBOURS. The U(1) holonomy material in
`BridgeMagneticCycle` is a different vocabulary (Circle-valued
connections, gauge classes) and is not this circulation; nothing
here cites it. S-4's charges — the kernel of `dropVec` and the
universality theorem, K-SHADOW-IDENTITY's seat — are untouched.
-/

section CirculationSplit

/-- The unit circulation at the seat: one unit of current flowing
around the 3-cycle `0 → 1 → 2 → 0`. The entry `i j` is `1` when
`j` is `i`'s successor on the cycle, `-1` when `i` is `j`'s
successor, and `0` on the diagonal — antisymmetric by
construction, the seat's pure circulation exhibit. -/
def gravShadowCycleFlow : Fin 3 → Fin 3 → ℝ :=
  fun i j => if j = i + 1 then 1 else if i = j + 1 then -1 else 0

/-- The circulation of an edge field around the seat's 3-cycle:
the forward rim sum, the entries along `0 → 1 → 2 → 0` read in
the direction of flow. This is the seat's honest curl-ghost —
a scalar read off the field, not an operator (K-CURL-SEAT). -/
def gravShadowCirculation (X : Fin 3 → Fin 3 → ℝ) : ℝ :=
  X 0 1 + X 1 2 + X 2 0

/-- The cycle flow is antisymmetric: reversing any edge negates
its entry — the seat's currents are antisymmetric, and the
exhibit is one of them. -/
theorem gravShadowCycleFlow_antisymm :
    ∀ i j, gravShadowCycleFlow j i = - gravShadowCycleFlow i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [gravShadowCycleFlow] <;>
    norm_num [gravShadowCycleFlow]

/-- The cycle flow is divergence-free at every node: at each node
one unit arrives and one unit leaves, so `diverge` totals zero —
a circulation in the seat's exact sense. -/
theorem gravShadowCycleFlow_diverge_zero :
    ∀ i, diverge gravShadowCycleFlow i = 0 := by
  intro i
  fin_cases i <;>
    simp [diverge, Fin.sum_univ_three, gravShadowCycleFlow] <;>
    norm_num [diverge, Fin.sum_univ_three, gravShadowCycleFlow]

/-- The exhibit's circulation is nonzero — it is `3`, one unit
along each of the cycle's three edges. A divergence-free current
that is genuinely there: named and measured, not gestured at. -/
theorem gravShadowCirculation_cycleFlow :
    gravShadowCirculation gravShadowCycleFlow = 3 := by
  simp [gravShadowCirculation, gravShadowCycleFlow] <;>
    norm_num [gravShadowCirculation, gravShadowCycleFlow]

/-- No field-shadow circulates: the circulation of any
`dropVec φ` around the closed cycle telescopes to zero. The
cycle flow above is therefore not the field-shadow of any
potential whatsoever. -/
theorem gravShadowCirculation_dropVec (φ : Fin 3 → ℝ) :
    gravShadowCirculation (dropVec φ) = 0 := by
  simp only [gravShadowCirculation, dropVec_apply]
  ring

/-- **The finite Helmholtz split at the seat.** Every
antisymmetric edge field — every current at the seat — decomposes
as the Ohm flow of a potential (the gradient part: the
field-shadow of `φ` under the seat's conductances) plus an
antisymmetric divergence-free remainder (the circulation part).
The potential comes from the census Poisson existence theorem,
cited not re-proved: an antisymmetric field's total divergence
vanishes, which is exactly that theorem's hypothesis. Stated for
antisymmetric fields only — antisymmetry is what makes the total
divergence vanish and the rim close in this tree's conventions
(S-2), and the restriction is on the face, not hidden. -/
theorem gravShadowHelmholtz (X : Fin 3 → Fin 3 → ℝ)
    (hX : ∀ i j, X j i = - X i j) :
    ∃ φ : Fin 3 → ℝ, ∃ Z : Fin 3 → Fin 3 → ℝ,
      (∀ i j, Z j i = - Z i j) ∧ (∀ i, diverge Z i = 0) ∧
      X = flowVec gravShadowWeight φ + Z := by
  have hw : ∀ i j, gravShadowWeight i j = gravShadowWeight j i := by
    intro i j
    by_cases h : i = j
    · simp [gravShadowWeight, h]
    · simp [gravShadowWeight, h, Ne.symm h]
  have hw0 : ∀ i j, 0 ≤ gravShadowWeight i j := by
    intro i j
    by_cases h : i = j <;> simp [gravShadowWeight, h]
  have hpos : ∀ i j, i ≠ j → 0 < gravShadowWeight i j := by
    intro i j h
    simp [gravShadowWeight, h]
  have hsum : ∑ i, diverge X i = 0 := by
    have htot : (∑ i, diverge X i) = ∑ i, ∑ j, X j i :=
      Finset.sum_congr rfl fun i _ => diverge_apply X i
    have hswap : (∑ i, ∑ j, X j i) = ∑ i, ∑ j, X i j := Finset.sum_comm
    have hneg : (∑ i, ∑ j, X i j) = -∑ i, ∑ j, X j i := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      exact hX j i
    linarith
  obtain ⟨φ, hφ⟩ := exists_potential_of_sum_eq_zero gravShadowWeight hw hw0
    hpos (diverge X) hsum
  refine ⟨φ, X - flowVec gravShadowWeight φ, ?_, ?_, ?_⟩
  · intro i j
    have hflow : flowVec gravShadowWeight φ j i
        = - flowVec gravShadowWeight φ i j :=
      flowVec_antisymm gravShadowWeight hw φ j i
    simp only [Pi.sub_apply]
    rw [hX i j, hflow]
    ring
  · intro i
    have hdiv : diverge (X - flowVec gravShadowWeight φ) i
        = diverge X i - diverge (flowVec gravShadowWeight φ) i := by
      rw [diverge_apply, diverge_apply, diverge_apply,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp only [Pi.sub_apply]
    rw [hdiv,
      ← congrFun (laplacianOp_eq_diverge_flow gravShadowWeight hw φ) i,
      ← congrFun hφ i]
    exact sub_self _
  · ext i j
    simp only [Pi.add_apply, Pi.sub_apply]
    abel

end CirculationSplit

/-! ## S-4 — the honesty brick (this brick)

THE SHADOW IS THE SHAPE OF EVERY POTENTIAL THEORY, AND THIS
BRICK PROVES IT — which is why the shadow can never be sold as
the object. Two charges, both from the scope:

(a) **The kernel of the drop.** The field-shadow determines the
potential-shadow only up to an additive constant: `gravShadowField
φ = 0` iff `φ` is constant (`gravShadowField_eq_zero_iff`), and
two weightings cast the same field-shadow iff they differ by a
constant (`gravShadowField_eq_iff`). At this seat the drop is
taken over every ordered pair, so the kernel is read off directly
— no energy argument is needed, and none is borrowed.

(b) **Universality, and the kill it carries.**
`gravShadowRelations φ` assembles the shadow relations of
S-1–S-3 as one predicate on a weighting: the Poisson
factorization at the seat (the source-shadow is the divergence
of the field-shadow's Ohm flow), the current law (every
source-shadow totals zero), the rim closure (every region's
source-shadow total is the rim flux of the flow), the vanishing
circulation of the field-shadow, and the corrected pairing read
against the cycle exhibit. `gravShadowRelations_universal`
proves the predicate for EVERY weighting `φ : Fin 3 → ℝ`
whatsoever — each conjunct is one of the earlier bricks'
theorems, cited, at a general `φ`.

**K-SHADOW-IDENTITY — FIRED, at full rank, as designed.** The
claim this kill was pre-registered against: "these relations
pick out gravity." Registered formally as
`gravShadowIdentityClaim` — the weakest form "picking out"
could take after (a): some single constant class of weightings
is the one the relations select. It is FALSE, by proof
(`gravShadowIdentityClaim_false`): the relations hold for every
weighting, in particular for the zero weighting and for the
exhibited potential `φ = (2/9, −1/9, −1/9)`, which lie in
different constant classes — so the relations select no class,
hence no object. The relations are the shape of potential
theory itself; gravity is one tenant of that shape among
infinitely many, and nothing in S-1–S-3 ever distinguished it.
That is not a defect of the line: it is the line's designed
final theorem, the fence that keeps the shadow honest. Dial 2
stays 0; no object was constructed, fed, or identified. -/

section HonestyBrick

/-- **(a) The kernel of the drop at the seat.** The
field-shadow of `φ` vanishes iff `φ` is constant: the
field-shadow determines the potential-shadow only up to an
additive constant, and the constants are exactly its kernel. -/
theorem gravShadowField_eq_zero_iff (φ : Fin 3 → ℝ) :
    gravShadowField φ = 0 ↔ ∃ c : ℝ, ∀ i, φ i = c := by
  constructor
  · intro h
    refine ⟨φ 0, fun i => ?_⟩
    have hi : φ i - φ 0 = 0 := by
      have h' := congrFun (congrFun h 0) i
      simp only [Pi.zero_apply] at h'
      exact h'
    exact sub_eq_zero.mp hi
  · rintro ⟨c, hc⟩
    funext i j
    show φ j - φ i = 0
    rw [hc i, hc j, sub_self]

/-- **(a) The determination, in full.** Two weightings cast the
same field-shadow iff they differ by an additive constant — the
field-shadow sees the potential-shadow exactly up to the kernel
of the drop, no more and no less. -/
theorem gravShadowField_eq_iff (φ ψ : Fin 3 → ℝ) :
    gravShadowField φ = gravShadowField ψ ↔
      ∃ c : ℝ, ∀ i, φ i = ψ i + c := by
  constructor
  · intro h
    have h0 : gravShadowField (fun k => φ k - ψ k) = 0 := by
      funext i j
      show (φ j - ψ j) - (φ i - ψ i) = 0
      have hij : φ j - φ i = ψ j - ψ i := by
        have h' := congrFun (congrFun h i) j
        exact h'
      linarith
    obtain ⟨c, hc⟩ :=
      (gravShadowField_eq_zero_iff (fun k => φ k - ψ k)).mp h0
    refine ⟨c, fun i => ?_⟩
    have hci : φ i - ψ i = c := hc i
    linarith
  · rintro ⟨c, hc⟩
    funext i j
    show φ j - φ i = ψ j - ψ i
    rw [hc i, hc j]
    ring

/-- **The shadow relations of S-1–S-3, assembled as one
predicate on a weighting `φ`.** In order: the Poisson
factorization at the seat (S-1's backbone, the census
`laplacianOp_eq_diverge_flow` read on the line's own objects);
the current law (every source-shadow totals zero); the rim
closure (S-2's divergence theorem on the flow: every region's
source-shadow total is the rim flux across its boundary); the
vanishing circulation of the field-shadow (S-3); and the
corrected adjoint pairing (S-2) read against the cycle exhibit
(S-3). These are the relations the line has been calling the
shadow's outline. -/
def gravShadowRelations (φ : Fin 3 → ℝ) : Prop :=
  gravShadowSource φ = diverge (flowVec gravShadowWeight φ) ∧
  (∑ i, gravShadowSource φ i) = 0 ∧
  (∀ S : Finset (Fin 3), (∑ i ∈ S, gravShadowSource φ i)
    = gravShadowRimFlux S (flowVec gravShadowWeight φ)) ∧
  gravShadowCirculation (gravShadowField φ) = 0 ∧
  (∑ i, ∑ j, gravShadowField φ i j * gravShadowCycleFlow i j)
    = 2 * ∑ i, φ i * diverge gravShadowCycleFlow i

/-- **(b) The universality theorem.** The shadow relations hold
for EVERY seat weighting `φ : Fin 3 → ℝ` whatsoever — no
hypothesis on `φ`: not mean-zero, not a contrast, nothing. Each
conjunct is an earlier brick's theorem cited at a general `φ`:
the census factorization, the rim theorem spent on the Ohm
flow (antisymmetric, so the total divergence vanishes by the
interior-cancellation argument), the telescoping circulation,
and the corrected pairing against the antisymmetric cycle
exhibit. The shadow is the shape of every potential theory at
this seat — that is the theorem, and it is also the kill. -/
theorem gravShadowRelations_universal (φ : Fin 3 → ℝ) :
    gravShadowRelations φ := by
  have hw : ∀ i j, gravShadowWeight i j = gravShadowWeight j i := by
    intro i j
    by_cases h : i = j
    · simp [gravShadowWeight, h]
    · simp [gravShadowWeight, h, Ne.symm h]
  have hanti : ∀ i j, flowVec gravShadowWeight φ j i
      = - flowVec gravShadowWeight φ i j :=
    fun i j => flowVec_antisymm gravShadowWeight hw φ j i
  unfold gravShadowRelations
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact laplacianOp_eq_diverge_flow gravShadowWeight hw φ
  · have h2 : (∑ i, gravShadowSource φ i)
        = ∑ i, diverge (flowVec gravShadowWeight φ) i :=
      Finset.sum_congr rfl fun i _ =>
        congrFun (laplacianOp_eq_diverge_flow gravShadowWeight hw φ) i
    rw [h2]
    have htot : (∑ i, diverge (flowVec gravShadowWeight φ) i)
        = ∑ i, ∑ j, flowVec gravShadowWeight φ j i :=
      Finset.sum_congr rfl fun i _ => diverge_apply _ i
    have hswap : (∑ i, ∑ j, flowVec gravShadowWeight φ j i)
        = ∑ i, ∑ j, flowVec gravShadowWeight φ i j := Finset.sum_comm
    have hneg : (∑ i, ∑ j, flowVec gravShadowWeight φ i j)
        = -∑ i, ∑ j, flowVec gravShadowWeight φ j i := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      exact hanti j i
    linarith
  · intro S
    have hstep : (∑ i ∈ S, gravShadowSource φ i)
        = ∑ i ∈ S, diverge (flowVec gravShadowWeight φ) i :=
      Finset.sum_congr rfl fun i _ =>
        congrFun (laplacianOp_eq_diverge_flow gravShadowWeight hw φ) i
    rw [hstep]
    exact gravShadowDivergence_rim (flowVec gravShadowWeight φ) hanti S
  · exact gravShadowCirculation_dropVec φ
  · exact gravShadowPairing_antisymm φ gravShadowCycleFlow
      gravShadowCycleFlow_antisymm

/-- **The identity claim, registered exactly as it dies.** The
claim "these relations pick out gravity," in the weakest form
"picking out" could take after (a): there is a single constant
class of weightings — one would-be object's potential-shadow,
up to the drop's kernel — such that every weighting satisfying
the shadow relations lies in it. If the relations identified
an object, they would identify at most this. They do not. -/
def gravShadowIdentityClaim : Prop :=
  ∃ φ₀ : Fin 3 → ℝ, ∀ φ : Fin 3 → ℝ, gravShadowRelations φ →
    ∃ c : ℝ, ∀ i, φ i = φ₀ i + c

/-- **K-SHADOW-IDENTITY — FIRED.** The identity claim is false,
by proof. By universality the relations hold for the zero
weighting and for the exhibited potential `(2/9, −1/9, −1/9)`;
were the claim true, both would lie in one constant class,
forcing the exhibited potential's values at `0` and `1` to
agree — they are `2/9` and `−1/9`. So the shadow relations
select no constant class, hence no potential, hence no object:
they are the shape of every potential theory at the seat, and
a shape is not an identity. Reported at full rank, at the same
volume as a landing — this kill is S-4's designed result, and
it is what the whole line was built to be able to say. -/
theorem gravShadowIdentityClaim_false : ¬ gravShadowIdentityClaim := by
  rintro ⟨φ₀, hφ₀⟩
  obtain ⟨c₁, hc₁⟩ := hφ₀ (fun _ => 0) (gravShadowRelations_universal _)
  obtain ⟨c₂, hc₂⟩ := hφ₀ gravShadowExhibitPotential
    (gravShadowRelations_universal _)
  have g0 : (0 : ℝ) = φ₀ 0 + c₁ := hc₁ 0
  have g1 : (0 : ℝ) = φ₀ 1 + c₁ := hc₁ 1
  have h0 : gravShadowExhibitPotential 0 = φ₀ 0 + c₂ := hc₂ 0
  have h1 : gravShadowExhibitPotential 1 = φ₀ 1 + c₂ := hc₂ 1
  rw [gravShadowExhibitPotential_values.1] at h0
  rw [gravShadowExhibitPotential_values.2.1] at h1
  linarith

end HonestyBrick

end ThetLogos
