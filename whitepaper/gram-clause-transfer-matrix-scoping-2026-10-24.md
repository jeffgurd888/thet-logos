# Gram clause — the transfer-matrix route: SCOPING CHARTER

**Date:** 2026-10-24. **Status: SCOPING ONLY.** This document
designs a proposed route and prices it. It commissions nothing,
builds nothing, and proves nothing. Every construction below is
a design hypothesis at FRONTIER tier until its rung lands.

**NO CLAIM.** Parts of any official Clay statement closed by
this document: 0. Stage 1b-B label unchanged: positivity **T1
for U(1)** (Route C); general (G, ρ) **OPEN**. Census
unchanged: 4,339 strict / 4,388 attribute-inclusive / 143
modules.

## Background in one paragraph

The Gram-criterion roads to Stage 1b-B's open clause are
closed. The integrated criterion
`osForm_nonneg_of_gram_integrated` (`LatticeGramSeries`) stands
as a true conditional, but its factored occurrence family is
not a model at d ≥ 2 (T4c′: the strict factor's two readings
are the transposed entries (k, a) and (j, i) of one matrix),
and neither is its reflection-regrouping/polarization class
(R0: symmetrized proportionality is false at the same SU(2)
instance). The criterion remains available as a tool; it is no
longer the target. This charter scopes the classical
alternative the T4c′ dossier named: prove `osForm_nonneg`
**directly**, through the transfer operator the corpus already
built at Stage 1b-D, bypassing any factored family for the
criterion. The inventory (§2) holds a surprise that shapes the
whole charter: most of the classical route's machinery is
already T1 in this corpus — what is missing is named,
fenced, and was already priced by the landings themselves.

## §1 The classical route (literature-shaped; T4 anchors)

The argument shape is the standard one for Wilson lattice
gauge theory (anchors: E. Seiler, *Gauge Theories as a
Problem of Constructive Quantum Field Theory and Statistical
Mechanics*, Springer Lecture Notes in Physics 159, 1982 —
reflection positivity via the transfer matrix and the Markov
property of the lattice Gibbs measure; J. Glimm & A. Jaffe,
*Quantum Physics: A Functional Integral Point of View*, 2nd
ed., 1987 — the time-zero Hilbert space, the transfer matrix
as a positive self-adjoint contraction, and reflection
positivity read off it).

1. **Time-zero Hilbert space.** States are L² functions of
   one time slice's gauge field, against the slice marginal
   of the Gibbs measure. A slice observable F prepares a
   state; the vacuum is the constant function.
2. **The transfer operator.** One time step is the integral
   operator whose kernel is built from the Boltzmann factors
   of the plaquettes in one time layer (spatial plaquettes of
   the two boundary slices split symmetrically between the
   steps adjacent to them). Classically T is self-adjoint
   (time-reflection symmetry of the layer), a contraction,
   and **positive**: its kernel, read through the middle of
   the layer, is an inner product — the half-step kernel
   paired with its own adjoint over the intermediate slice
   configuration — so ⟨ψ, Tψ⟩ ≥ 0 for every state ψ, not
   only positive ones.
3. **OS positivity from T.** An observable F supported in
   the positive half-time slab is propagated by transfer
   steps to the reflection plane; its reflection ΘF is the
   mirror propagation. The Markov property of the Gibbs
   measure (successive conditioning on time slices) then
   identifies the OS diagonal ⟨ΘF · F⟩ with a transfer
   quadratic form ⟨ψ_F, T^m ψ_F⟩ at the prepared state ψ_F,
   where m is set by the slab's depth. Positivity of T plus
   self-adjointness gives positivity of every power
   (T^{2k} = (T^k)†T^k; T^{2k+1} = (T^k)† T T^k), hence
   ⟨ΘF · F⟩ ≥ 0: **osForm_nonneg**, with no expansion of
   the Boltzmann weight in any basis and no per-plaquette
   factorization anywhere.

The target statement is the corpus's own (see §3): for every
observable F factoring through the strict positive half,
`0 ≤ (osForm β F F).re ∧ (osForm β F F).im = 0` — the exact
conclusion shape of both landed criteria.

## §2 Corpus inventory (what already stands, with names)

Inventoried 2026-10-24 from the modules' headers, dossiers,
and declaration lists. The route's ingredients, one by one:

**Time-zero Hilbert space — STANDS (Stage 1b-C,
`LatticeOSSpace`, 42 strict).** `osSpace β = Lp ℂ 2
(sliceMeasure β)`, the L² space of the time-0 slice's
configuration space under the Gibbs slice marginal — an
honest Mathlib Hilbert space at general (G, ρ), every real β.
With it: `osVacuum` (norm 1), `sliceState` (observables as
vectors, `inner_sliceState`, `vacuum_expectation`), the
multiplication operators `sliceMul` with `sliceMul_adjoint` /
`sliceMul_selfAdjoint`, and `sliceLinks_subset_posLinks`
(the slice sits inside the strict positive half — the
preparation map's foothold).

**Reflection and measure splitting — STANDS (Stage 1b-A,
`LatticeReflection`, 67 strict).** `reflConfig` (involutive),
`gibbsMeasure_map_reflConfig`, the action split
S = S₊ + S₋ + S₀ with S₋ = S₊ ∘ θ, plaquette reflection
laws, mirror transports. Consumed by 1b-B as
`wilsonAction_split_half` and the transports `restrictPos` /
`mirrorP` with `integral_restrictPos` / `integral_mirrorP`.

**The OS form — STANDS as a form; its positivity is the
target (Stage 1b-B, `LatticePositivity`, 44 strict).**
`osForm` (§4 of the module), conjugate symmetry
`osForm_conj_symm` at every real β, the exact kernel form
`osForm_eq_kernel` (§5), positivity at β = 0
(`osForm_zero_nonneg`), and the finite Gram criterion
`osForm_nonneg_of_gram` (§6). Nothing in this module is
superseded by the present route; the route aims at the same
module's open clause from outside it.

**The transfer operator — STANDS as an operator package;
its positivity on arbitrary vectors is ABSENT (Stage 1b-D,
`LatticeTransfer`, 58 strict).** `transferOp
= (slicePull)† ∘L nextPull : osSpace β →L[ℂ] osSpace β`,
with:
- `transferOp_inner` — the quadratic form IS the two-slice
  Gibbs kernel pairing: ⟪g, T f⟫ = ∫ conj(g∘restrictConfig)
  · (f∘nextConfig) dGibbs. **STANDS.**
- `transferOp_norm_le` (contraction), `transferOp_vacuum`
  (vacuum fixed) — **STAND.**
- `transferOp_inner_symm`, `transferOp_adjoint`,
  `transferOp_isSelfAdjoint` (Even N) — **STAND.**
- `transferOp_form_nonneg` — **PARTIAL, and the partiality
  is the route's first work item:** it proves
  0 ≤ ⟪g, Tf⟫.re (and vanishing imaginary part) only for
  slice observables f, g that are pointwise real and
  nonnegative, by a pointwise kernel argument. Operator
  positivity — 0 ≤ ⟪ψ, Tψ⟫.re for an *arbitrary* complex
  vector ψ — is **ABSENT**: no half-step factorization
  (T = V†V shape) and no positivity-on-all-vectors statement
  exists in the module.
- The β = 0 sector is exact (`transferOp_zero_apply`:
  T₀ = vacuum projection; gap exactly 1) — **STANDS**, and
  is the route's d = 1-style shadow check at zero coupling.

**The identification of T's form with osForm — ABSENT,
fenced and priced by its own landing.** The 1b-D dossier
fences it verbatim: "It would need a time-direction
Markov/layer factorization of the Gibbs measure, not
formalized in this corpus (priced **M–L**)." That same
layer factorization is the missing input for operator
positivity above (the half-step read of the one-step
kernel) — one missing lemma feeds both gaps, which is what
makes this route cheaper than it looks. The dossier also
prices pointwise positivity of T f at **S** (not
formalized; a corollary shape, not needed by this route).

**Named loose end (in-file, priced S there):** the
`posToSlice` marginal identity in `LatticeOSSpace`
(measure.map of the product Haar measure under the
slice-coordinatization equals the product measure) —
unproved, explicitly not used by the landed theorems;
§4's R0/R3 may consume it.

**The criterion, for contrast — STANDS as a conditional,
not the target.** `osForm_nonneg_of_gram_integrated`
(`LatticeGramSeries`, line 431) concludes the same
`osForm_nonneg` shape from a countable factored family
(A, B, Ξ) with `hgram` + marginals. The transfer route
differs in kind: it produces *no* family and satisfies *no*
hypothesis of the criterion; it proves the conclusion by
identifying the OS diagonal with a quadratic form of an
operator already known to be self-adjoint (and, after R2,
positive). If it closes, the criterion is simply never
invoked at general (G, ρ) — it stands for the record, and
its U(1) model (Route C) stands as that theory's proof.

## §3 Design constraints carried over

- **D1 — The corpus's definitions govern.** `osForm`,
  `gibbsMeasure`, `sliceMeasure`, `transferOp` are consumed
  as landed. No parallel OS form, no re-based transfer
  operator, no re-split action. A rung that needs a variant
  proves the variant *equal* to the landed object or stops.
- **D2 — General (G, ρ) or an explicit fence.** Every rung
  states its (G, ρ) scope on its face. A step that only
  closes at d = 1 or for abelian G is a kill, not a landing
  (that ground is Route C's, already held).
- **D3 — β discipline, stated exactly.** The landed transfer
  package holds at every real β; the classical positivity
  argument consumes only that the Boltzmann weight is a
  positive function, which is β-sign-free for the Wilson
  weight. The route therefore *aims* at the conclusion at
  every real β — matching both criteria's conclusion
  shape — and any rung where a sign condition on β is
  actually consumed must name it and narrow the target on
  its face. (Route C's β ≥ 0 was a property of the Bessel
  expansion, not of positivity; this route must not inherit
  it silently, nor claim the wider range without the
  lemmas being sign-free in fact.)
- **D4 — The d = 1 shadow.** Nothing in the route is
  representation-index-based (§5), so the U(1) case must
  flow through the same proof and reproduce Route C's
  result as a special case when it closes. A construction
  that excludes d = 1 is wrong-shaped on its face, the
  mirror image of the exclusions that killed T4c/T4c′.
- **D5 — No basis expansions of the weight.** The route's
  point is to never expand exp(−S) in characters or matrix
  coefficients. A rung that finds itself summing over
  representation indices has wandered back into the closed
  territory and should stop and report, whatever it was
  proving (measurability and integrability side conditions
  are to be discharged by the corpus's continuity/boundedness
  API, as the landed modules do).
- **D6 — Finiteness.** Everything is at fixed even N,
  finite lattice, exactly as in 1b-A–D. No continuum,
  thermodynamic, or spectral claim is in scope; the
  general-β *gap* fenced by 1b-D stays fenced (it is not
  this route's target and does not follow from it).

## §4 Rung ladder (prices; pre-registered kill criteria)

- **R0 — Depth-one identification, on paper. Price: S.**
  Take the smallest nontrivial case: N = 4, and F a
  *slice* observable (factors through `sliceLinks`, the
  depth-one subclass `LatticeOSSpace` already isolates).
  By hand, from landed statements only (`osForm_eq_kernel`,
  `transferOp_inner`, the slice-marginal identities),
  determine whether the OS diagonal equals a transfer
  quadratic form at a prepared slice state — and if the
  chain breaks, name the FIRST identity it needs that is
  not landed, stated as a finite lemma about the corpus's
  own measures and maps. *Kill:* the identification fails
  even at depth one (a mismatch term no transfer power
  reproduces — e.g. a cross-plane temporal coupling that
  survives as an unpaired factor), or the first missing
  identity is not statable finitely in the corpus's
  language (needs a disintegration theory the finite
  product spaces do not already support). Passing R0 means
  the chain closes at depth one modulo named finite
  lemmas; it is a gate, not evidence about depth N/2.
- **R1 — The layer factorization. Price: M.** Formalize
  the time-direction Markov/layer factorization of the
  Gibbs measure at one-step level: the Gibbs expectation
  of a two-slice observable as the slice-marginal integral
  of the one-step kernel pairing, in the form
  `transferOp_inner` consumes and R3 iterates — the lemma
  the 1b-D dossier fenced at M–L, taken here at its
  one-step core. Includes the `posToSlice` marginal
  identity if the iteration consumes it (priced S in its
  home file). *Kill:* the one-step conditional density
  cannot be written with the symmetric half-step split —
  the temporal plaquettes shared between layers force a
  kernel whose two half-step factors are not adjoints of
  one another, so no square exists even before Lean cost
  is counted.
- **R2 — Operator positivity on all vectors. Price: M.**
  From R1: the half-step operator V (osSpace → L² of the
  doubled/mid-layer data) with `transferOp = V† ∘L V`,
  or directly 0 ≤ ⟪ψ, Tψ⟫.re for arbitrary ψ, upgrading
  `transferOp_form_nonneg` from positive observables to
  the whole space. *Kill:* the positivity proof is found
  to need a factorization of the one-step kernel over
  representation indices of a crossing plaquette — the
  (k, a)/(j, i) obstruction reappearing one level up
  (§5, U1) — rather than over the mid-layer configuration.
- **R3 — Preparation and powers: the full identification.
  Price: L.** Iterate R1 over the positive half's layers:
  for arbitrary strict-half F, a prepared state ψ_F in
  osSpace and an exponent m (the half's depth) with
  osForm β F F = ⟪ψ_F, T^m ψ_F⟫; positivity of powers from
  `transferOp_isSelfAdjoint` + R2 by the even/odd square
  argument (analytic glue: adjoint algebra on `→L[ℂ]`,
  expected routine). This rung contains the 1b-D fence's
  "identification (M–L)" and is priced at its top.
  *Kill:* preparation closes for slice observables only —
  temporal links *inside* the positive half couple the
  layers in a way the iteration does not absorb — or the
  exponent/state depends on F through the kernel in a
  form that breaks the quadratic-form reading.
- **R4 — Discharge. Price: S.** Assemble:
  `osForm_nonneg` at general (G, ρ) — at every real β if
  R1–R3 are in fact sign-free (D3), else at β ≥ 0 with
  the narrowing named — by R3 + R2, in the corpus's exact
  conclusion shape; flip the Stage 1b-B label. *Kill:*
  any hypothesis mismatch at the application site
  (hρcont, Even N, 2 ≤ N are corpus-standard; a mismatch
  means an upstream rung silently changed the target).

Total price if the route runs clean: **S + M + M + L + S**.
The cheapest rung again carries a real kill by design:
R0 can sink the identification before any Lean is written.

## §5 Honest unknowns

- **U1 — Could the (k, a)/(j, i) obstruction reappear one
  level up? (The route's defining question.)** The
  argument that it cannot, stated at full strength so it
  can be attacked: the T4c′ kill lived in the *strict
  factor's* being a single **matrix entry** of ρ, read at
  transposed indices by the two halves, because the
  criterion's hinge Ξ had to be one scalar function
  carrying that entry for both. The transfer route's
  hinge is not an entry of anything. The half-step
  factorization (R2) pairs the half-step kernel with
  **itself** over the mid-layer *configuration*: the
  pairing is a plain L² inner product
  ∫ conj(K(w, z)) · K(w, z') dμ(w) of a scalar kernel,
  and the representation indices of every plaquette are
  contracted inside the scalar tr ρ(plaq) **before** any
  splitting takes place — the sandwich monomials of T4c
  never have their factors separated across the hinge,
  because the hinge is a whole group-valued configuration,
  summed by Haar measure, not an index. The transposition
  that killed the factored family is an operation on
  index pairs of one link's matrix; no such pair exists
  here. *Residual risk, honestly kept:* if formalizing
  the layer factorization (R1) forces the Boltzmann weight
  to be manipulated in a basis — e.g. a measurability or
  density identity that is only available through a
  character expansion in the pinned Mathlib — index
  splitting could re-enter through the side door. D5 is
  written to catch exactly that; R1/R2's kill criteria
  name it. Assessment: the obstruction's mechanism has
  no purchase on the construction as designed; the risk
  is infrastructural, not mathematical.
- **U2 — Gauss law / gauge fixing: not needed here, and
  why.** The classical continuum transfer matrix is often
  presented on gauge-invariant states (the Gauss-law
  subspace). On the finite lattice, reflection positivity
  is a statement about the Gibbs expectation on the
  *full* slice space: positivity proved on the whole
  osSpace restricts to any subspace for free, and the
  landed `transferOp` already acts on the full space with
  its positivity (on positive observables) proved without
  any gauge fixing. No gauge fixing, no Faddeev–Popov, no
  constraint projection is consumed by this stage's
  statement. (Gauge invariance of the physical subspace
  matters for Stage 2's reconstruction, not for 1b-B.)
- **U3 — The slice space is finite, and that is the
  corpus's setting, not an approximation to repair.**
  Classically the time-zero configuration space of a
  lattice theory at fixed volume is a finite product of
  copies of G with product Haar measure — exactly the
  corpus's `sliceLinks → G`. The continuum-of-the-slice
  questions (fields over ℝ³) belong to the continuum
  limit, Stages 3c/4, and are out of scope by D6. No
  classical step in §1 uses more than the finite product
  structure plus Fubini.
- **U4 — Markov formalization cost is the real unknown
  mass.** The finite-product setting makes layer
  factorization *true by Fubini*, but the corpus's
  identities must thread N/2 layers of transports,
  restrictions, and marginal identifications whose
  bookkeeping has surprised this campaign before (the
  T4c sandwich was found inside just such plumbing).
  R1/R3 prices (M, L) carry this; a blow-up would show
  first as R3's preparation step resisting induction
  over layers. Priced, not hidden.
- **U5 — The β range.** §1's argument is sign-free as
  classical mathematics (the weight is a positive
  function at any real β). But the corpus's landed
  pieces were each proved under their own hypotheses,
  and whether every link of R1–R3 is in fact β-sign-free
  is a property of the formalization, to be verified
  rung by rung under D3 — not assumed in this charter.
  The stage's clause is discharged at β ≥ 0 in the
  worst case; the wider range is a bonus the route must
  earn, and the difference will be printed on R4's face
  either way.
- **U6 — Scope of a positive outcome.** A clean run
  closes Stage 1b-B's clause at general (G, ρ) — full
  stop. It yields PARTIAL-δ's missing half (with 1b-A),
  feeds Stage 2's reconstruction, and retires the Gram
  clause as a *need* (the criterion and its U(1) model
  remain as record). It does not touch the general-β gap
  (fenced separately in 1b-D), Stage 3c's uniform
  estimates, Stage 4, or any official statement.

---

**Charter ends.** What would commission work: Jeff's word
on this charter, rung by rung, R0 first. Until then the
record stands where the R0 dossier left it — criterion T1
as a conditional, its factored and regrouped model classes
killed at d ≥ 2, U(1) closed, general (G, ρ) OPEN — and the
transfer-matrix route scoped, priced, and unclaimed:
the classical road, on a corpus that turns out to have
already built most of it. **NO CLAIM.**
