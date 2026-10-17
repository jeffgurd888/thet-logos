# Gauntlet: The Parked Fleet

**Date:** 2026-10-17. **Mode:** standard gauntlet — every parked item
re-audited against the corpus *as it stands today*, every standing price
re-derived rather than inherited, every verdict grep/evidence-based.
No Lean was built for this dossier; it is a map, not a result.
**Order of record:** Jeff, 2026-10-17 — "run the gauntlet with the
parked fleet in priority."

**The gauntlet's rules.** Verdicts: **STANDS-AS-PRICED** (the parked
price survives re-derivation), **RE-PRICED** (new price, reason named),
**SPLIT** (the item decomposes into campaigns with separate prices),
**KILL** (a claim, a clause, or a route is dead, at full strength),
**PROMOTE** (an item moves up the queue on audited merit). Sizes are
the corpus's working bands (S ≈ one module-sitting, a few hundred
lines; M ≈ one campaign module, ~1–2k lines by recent calibration —
Stage 1a was priced M and landed 1,667 lines; L ≈ two-to-three
module campaigns; XL ≈ research-scale formalization).

**What moved the ground today.** Pitch 4 Stage 1a landed this morning
(`LatticeCorrelations.lean`, 68 T1; dossier
`pitch-4-stage-1a-2026-10-17.md`): the Gibbs measure exists as a
probability-measure object at every real β, the expectation algebra
and covariance package stand, the Elitzur mechanism theorem stands at
general (G, ρ), and the β = 0 factorization machinery (link-set splits
of the product measure) stands. Several parked prices were set before
that landing; this gauntlet re-tests each against it.

---

## Verdict table

| # | Item | Standing price | Verdict |
|---|---|---|---|
| 1 | Pitch 4 Stage 1b — reflection positivity | L–XL | **SPLIT + RE-PRICED → L** (four campaigns A–D; the XL tail is **KILL**ed, §1) |
| 2 | Pitch 4 Stage 1c — strong-coupling clustering | XL, killable | **SPLIT** — a finite-order exhibit (1c-0, **M**) carved out; the uniform body **STANDS at XL**; kill criteria pre-named (§2) |
| 3 | Bosonic essential self-adjointness | priced, obstruction named | **RE-PRICED → M–L**; the dossier clause "no LinearPMap closure operator" is **KILL**ed as stale — the closure API exists (§3) |
| 4a | Rung 7 — strong continuity | S–M (bundled) | **SPLIT** — translations **S** (discharge-ready); Lorentz part **S–M** (§4) |
| 4b | Rung 7 — Fock packaging | M | **STANDS-AS-PRICED (M)** — route pinned to the concrete ONB port; the abstract route re-confirmed blocked (§4) |
| 5a | Schrödinger — literal `NormedSpace.exp` identification | S | **STANDS-AS-PRICED (S)** — one-sitting build, route named (§5) |
| 5b | Schrödinger — Dyson first-order term | S–M | **STANDS-AS-PRICED (S–M)** — internal split named (§5) |
| 6 | `adag` namespace repair (+ the Yukawa campaign it unlocks) | unscored | **SCOPED + PRICED** — repair **S–M**; Yukawa **M–L** (§6) |
| 7 | Bridge follow-ons — attainment + decay; Faraday storey | priced, unsized | **RE-PRICED (sized)** — attainment **S**, decay package **M**; Faraday **S–M**, LatticeGauge ruled *not* to cheapen it (§7) |
| 8 | Theories-intake Round 2 — BRST / OS bridge / Dixmier | authorized, unpriced | BRST **M**, Dixmier **S–M** stand as intakes; OS item **SPLIT** — its fit half is **KILL**ed as redundant (absorbed by Pitch 4), its re-pin half stands at **S–M** (§8) |
| 9 | Decoherence toy (partial trace + toy) | S–M (Schrödinger gauntlet) | **STANDS-AS-PRICED (S–M)** — re-grepped today; partial trace still exists nowhere (§9) |
| 10 | Paper v3 assembly | owed, unpriced | **PRICED — S** (assembly, not research); exact contents delta listed, plus one catch the owed-list missed (§10) |

---

## 1. Stage 1b — reflection positivity · **SPLIT + RE-PRICED → L**

**Spec of record:** scoping §6.2 (1b): for F supported on the positive
half-lattice, ⟨(θF)·F⟩_β ≥ 0 (complex form ⟨conj(θF)·F⟩ ≥ 0), proved
via the action split S = S₊ + S₋ + S₀ with crossing plaquettes as a
positive kernel; corollaries: OS scalar product, finite-volume Hilbert
space, transfer matrix as positive self-adjoint contraction, lattice
gap = −log of the second-eigenvalue ratio at fixed (a, L, β) under
§8's naming clause. Scoping §8 calls 1b's factorization "the single
hardest priced step inside the landing."

**What 1a changed — three real inputs, audited one by one.**

- **The measure exists (real saving).** 1b's parked price assumed it
  would consume — and implicitly help pay for — a Gibbs *measure*.
  1a Item 1 landed exactly that: `gibbsMeasure` as a probability
  measure at every real β, with `gibbsExpect_eq_integral` identifying
  Stage 0's ratios with its integrals. The measure line-item is
  **deleted** from 1b's price.
- **The split machinery exists (real saving).** 1a Item 5 built the
  product-measure split over link subsets (`splitEquiv`,
  `MeasurePreserving` splitting, `integral_pi_split_mul`) for the
  β = 0 factorization. Reflection positivity needs the same move one
  level up — split over the reflection trichotomy, with the Gibbs
  density (a `withDensity` factor) in place of the bare product
  measure. The equiv/splitting skeleton is reusable; the density
  factorization is new work inside the same campaign, not a new
  campaign.
- **The covariance package is NOT consumed (no saving, said plainly).**
  Positivity is proved by a sum-of-squares factorization, not by any
  Cauchy–Schwarz/variance argument. What 1b consumes from 1a is the
  expectation *algebra* (products of observables, integrability of
  bounded observables) — worth S inside the positivity campaign, not
  more. Any future text crediting "1a's covariance package" with
  cheapening 1b is wrong.

**What 1a exposed — the obstruction the parked price glossed.**

- **The abstract-Λ presentation has no reflection.** Stage 0's
  lattice is a bare `Fintype Λ` with shifts `σ : Fin 4 → Equiv.Perm Λ`
  and commutation as a *hypothesis* (`hσ`). A reflection is extra
  structure that does not exist in either lattice module today
  (grep: `reflect|involut` over `LatticeGauge.lean` +
  `LatticeCorrelations.lean` returns only priced-remainder prose).
  1b is the first Pitch 4 stage that cannot proceed in Stage 0's
  abstract generality for free: it needs a *reflection structure
  pack* — an involution Θ on sites with Θσ₀Θ = σ₀⁻¹, ΘσᵢΘ = σᵢ
  (i ≠ 0), and a link trichotomy (+ / − / plane) relative to which
  every plaquette classifies. Per corpus pattern this is stated as
  hypotheses and discharged on the concrete torus
  (`Fin 4 → ZMod N`, shifts at `LatticeGauge.lean:1431`) — but the
  pack itself is new formalization surface, and it is priced below
  as its own campaign (1b-A).
- **The torus reflection has a fixed link stratum — the scoping's
  "S₀" is not a footnote.** Computed from the torus presentation.
  Through-sites reflection (x₀ ↦ −x₀, needs N even): fixed *sites*
  in two slices (x₀ = 0, x₀ = N/2); no fixed time links; but the
  *spatial* links inside the two fixed slices are fixed indices of
  the induced link involution. Between-sites reflection
  (x₀ ↦ −x₀ − 1): no fixed sites; the induced link involution has
  fixed *time-link* layers — exactly one for odd N, exactly two for
  even N (solutions of 2x₀ ≡ −2 mod N). Either convention carries a
  nonempty plane stratum of links that belong to neither half; the
  S₀ bookkeeping (which plaquettes touch the stratum, and how their
  Boltzmann factors split) is genuine torus combinatorics with no
  infinite-lattice analogue to copy. This is priced inside 1b-A/1b-B,
  and it is the reason the floor of the old band was honest.
- **The "Δ = 2 transfer-matrix setup" has no ledger address.** The
  phrase in the gauntlet's order does not occur in the scoping, in
  Stage 0, or in Stage 1a (grep-verified: no `Δ = 2` / `2Δ` / extent
  language). The scoping's 1b text fixes no time extent at all. The
  campaign must pin its setup as its first act — this gauntlet prices
  the general even-extent case; the minimal nondegenerate
  through-sites torus is extent 4 (extent 2 fixes both slices and
  leaves the halves empty of interior plaquettes). Recorded as a
  naming gap in the order, not silently papered over.

**The reflection choice, ruled.** Two involutions were on the table:
bare coordinate reflection on observables (F ↦ F∘Θ) versus
conjugation composed (F ↦ conj ∘ F ∘ Θ). The corpus's expectations
are ℂ-valued (Stage 0's `gibbsExpect`), and the OS output is a
*sesquilinear* form — so the reflection operator on observables is
**the conjugation-composed one**; the bare coordinate reflection is
recorded as the real form (they agree on real observables, and 1a's
`gibbsExpectR` package is where the real form lives). Θ on
configurations is the underlying site involution either way.

**Decomposition (the verdict's operative content).**

- **1b-A — Reflection structure pack + action split · M.**
  Θ as site involution (hypotheses pack + torus discharge); induced
  involution on configurations and on links; the trichotomy; the
  plaquette classification (every plaquette is +, −, or
  plane-touching, with plane-touching ones enumerated by the fixed
  stratum); the split identity S_β = S₊ + S₋ + S₀ with
  θ(S₊) = S₋ and S₀ θ-invariant. Landing: the split is a theorem on
  the torus for even N, under the pack's hypotheses in abstract form.
- **1b-B — Reflection positivity proper · L.** Θ preserves
  `configMeasure` (link permutation + inversions — Stage 0's
  `measurePreserving_mul_mul` / Pi-preservation patterns) and hence
  interacts with `gibbsMeasure` through the density; the density
  factorizes over the trichotomy (1a's split skeleton, density form);
  integrating the − half first yields ⟨conj(ΘF)·F⟩_β as an integral
  of a squared modulus over the plane variables — ≥ 0. This is the
  §8-named hardest step; its price does not drop below L on any
  honest accounting.
- **1b-C — The OS scalar product and finite-volume Hilbert space ·
  M (route chosen) / L (route declined).** Two routes were priced:
  (i) *time-slice L² route (chosen)* — states as L² functions of one
  time slice's spatial links against the slice Haar measure, an
  honest Mathlib `Lp` space, no abstract completion machinery;
  (ii) *quotient/completion route (declined)* — the OS form's
  null-space quotient + `InnerProductSpace.Core` completion,
  heavier API for the same finite-volume content. The route choice
  is made here so the campaign cannot drift into (ii) by accident.
- **1b-D — Transfer matrix + lattice gap · M.** The transfer matrix
  as the one-step integral operator on 1b-C's space: positivity from
  1b-B, self-adjointness from Θ-symmetry, contractivity from Stage
  0's density bounds transported through 1a's expectation algebra;
  compactness (continuous kernel on a compact configuration space)
  and the spectral statement; the gap named *only* as the lattice
  gap at fixed (a, L, β) under §8's mandatory clause, in the module
  header, verbatim discipline.

**Total: M + L + M + M = L, top of band.** The standing L–XL is
therefore **RE-PRICED to L**, and the XL tail is **KILL**ed, with
reasons: the XL was pricing (a) a measure construction that now
exists, (b) an undecided OS-space route that is now decided, and
(c) split bookkeeping that 1a partially pre-built. What survives of
the old band's caution is concentrated in 1b-B, which stays L on its
own. **Landing definition:** A + B = "reflection positivity stands"
(a new pre-named shape — **PARTIAL-δ**: Stages 0 + 1a + positivity;
the OS space and transfer matrix may not be mentioned as standing);
A + B + C + D = Stage 1b stands whole in the sense of §8 item 2,
and the pitch shape advances from PARTIAL-β accordingly.

---

## 2. Stage 1c — strong-coupling clustering · **SPLIT** (body stands at XL)

**Spec of record:** scoping §6.2 (1c): at small β the cluster
(character) expansion converges and correlations of gauge-invariant
observables decay exponentially in lattice distance with rate
m(β) > 0, uniformly in volume — Osterwalder–Seiler at corpus level.
Priced XL, separately killable; Stage 1 lands without it.

**The re-test against 1a.** Two pieces of 1a/Stage-0 machinery are
shared with the strong-coupling expansion's first steps: the Haar
intertwiner calculus (Stage 0's `haarIntertwiner` P — idempotent,
`repMatrix_mul_haarIntertwiner`, the β = 0 package
`⟨W_p⟩₀ = tr P`), and 1a Item 5's disjoint-support factorization at
β = 0. The question the gauntlet was asked: is 1c's *first* campaign
smaller than XL? **Yes — its first order is an M-sized exhibit**, and
it is carved out:

**1c-0 — Finite-order strong-coupling exhibit · M.** At fixed
(Λ, G, ρ) — fixed finite volume, no uniformity claimed anywhere:
(i) *Analyticity*: β ↦ ⟨F⟩_β is analytic at β = 0 (ratio of
integral-analytic functions; the denominator is Stage 0's
`gibbsDenom_pos` at 0 plus its in-module bounds; differentiation
under the integral is Mathlib stock). (ii) *The first-order
plaquette coefficient, exactly*: writing the action as β·A with
A the β-free density sum (Stage 0's `wilsonAction` is literally
β · Σ plaquetteDensity, `LatticeGauge.lean:287`), the expansion
⟨W_p⟩_β = tr P − β·κ_p + O(β²) holds with κ_p = Cov₀(W_p, A)
computed *in closed form* as a finite sum of intertwiner products —
at β = 0 the covariance factorizes over links (1a Item 5), so only
plaquettes sharing a link with p contribute, and each contribution
is a Stage-0 P-calculus integral. (iii) *The loop version is a
perimeter law at first order*: for a Wilson loop W_C, the first-order
term receives contributions only from plaquettes sharing a link with
C — a perimeter-counting finite sum, proved from the same
factorization. (This is the honest finite-order shadow of the area
law: the minimal-surface tiling is an all-orders phenomenon, and no
text may quote 1c-0 as area-law evidence.) (iv) *Rigorous remainder*:
the O(β²) constant is explicit at fixed Λ from Stage 0's
`wilsonAction_abs_le` / `wilsonAction_le` bounds. Landing: the
plaquette coefficient theorem + the perimeter-at-first-order theorem
+ the remainder, on the torus instances and under the abstract
hypotheses wherever the link-sharing case analysis closes.

**1c proper — uniform clustering · STANDS at XL.** Nothing in 1a
touches the uniformity content: convergence of the expansion with
volume-independent rate is the combinatorial campaign the scoping
priced (connected lattice animals, uniformity in L), and the
scoping's §5 Mathlib audit stands unrefuted — Mathlib has no
statistical-mechanics infrastructure (no spin systems, no cluster
expansions, no animal enumeration). 1c-0 is a ladder *toward* it,
not a down payment that reduces its price.

**Kill criteria, pre-named (sharper than the scoping's):**

- **KILL-1c-α (mechanism failure).** If 1c-0's κ_p computation shows
  the intertwiner calculus does *not* close at first order — the
  link-sharing case analysis needs hypotheses Stage 0 doesn't carry
  and explodes on the torus — the expansion *route* is killed, not
  delayed: 1c reverts to a bare XL wall with no exhibit ladder, and
  the failure is published as the reason.
- **KILL-1c-β (statement-form kill).** Any clustering statement
  whose proof obligations route through gauge-variant intermediate
  observables is dead on arrival: 1a's Elitzur theorem makes their
  expectations vanish identically, so a "decay" proved for them is a
  decay of zero. Clustering claims are well-formed only for
  gauge-invariant observables, in the connected-correlator form 1a
  already defines (`wilsonTwoPointConnected`).
- **PARK-1c-γ (infrastructure park).** If the uniformity step is
  found to require connected-animal counting bounds with no Mathlib
  path short of building the enumeration theory itself, 1c stays
  parked at XL indefinitely — recorded as infrastructure absence,
  not as a failed attempt, and not re-priced downward by optimism.

---

## 3. Bosonic essential self-adjointness · **RE-PRICED → M–L** (one clause KILLed)

**Parked state (dossier `pitch-3-campaign-2-2026-10-17.md`, §B2):**
symmetry on the dense domain, sectorwise self-adjointness with full
diagonalization, and LinearPMap formal self-adjointness
(`hamPMap ≤ hamPMap†`) all stand. Not proved: essential
self-adjointness / the equality `hamPMap = hamPMap†`. The dossier's
obstruction sentence: "Mathlib has no LinearPMap closure operator
producing equality from sectorwise data and no Kato–Rellich theorem;
the closure's domain is an ℓ²-growth condition across infinitely
many sectors."

**Re-test (grep-level, pinned checkout, today):**

- **KILL — the clause "no LinearPMap closure operator" is dead.**
  `Mathlib/Topology/Algebra/Module/LinearPMap.lean:94`:
  `noncomputable def closure (f : E →ₗ.[R] F) : E →ₗ.[R] F`, with
  `le_closure` (:110), `IsClosable.closure_isClosed` (:125),
  `IsClosable.graph_closure_eq_closure_graph` (:104). The inner-
  product file adds `adjoint_isClosed`
  (`Mathlib/Analysis/InnerProductSpace/LinearPMap.lean:332`) and
  `IsSelfAdjoint.isClosed` (:340). The closure operator, its order
  API, and the closedness of adjoints **exist**. The dossier
  sentence survives only in its weaker form: no theorem produces
  the *equality* from sectorwise data. Any future text quoting the
  strong form of the obstruction is quoting a killed clause.
- **The rest of the wall re-tests as standing.** Kato–Rellich:
  0 hits (`KatoRellich|Kato-Rellich` over the checkout). Nelson's
  analytic-vector theorem / analytic vectors: 0 hits. "Essentially
  self-adjoint" as vocabulary: 0 hits. The corpus's own position is
  unchanged: `hamPMap ≤ hamPMap†` is the frontier of what is proved.
- **Consequence of the find:** the ESA target is now *statable in
  sharp form* — `hamPMap.closure = hamPMap†`, equivalently
  `IsSelfAdjoint hamPMap.closure` — and closability of a symmetric
  densely-defined pmap is a short chain from the found API
  (T ≤ T† with T† closed ⇒ graph closure stays functional).
  Stating the target precisely was part of the parked price; it is
  now S of the price, not an unknown.

**The crack, named (two routes; neither exists in Mathlib).**

- **R1 — Faris–Lavine / Nelson commutator theorem.** A general
  theorem: a symmetric operator bounded by a self-adjoint
  comparison operator N with a commutator bound is essentially
  self-adjoint on any core of N. With N = (number + 1)², its
  hypotheses match the *shape* of B1's proved inputs (the
  number-relative bound ‖monoCoef‖ ≤ (n+2)² on sector n,
  `BosonicInteraction.lean:31`). Formalizing the general theorem is
  new Mathlib-gap analysis: **L**.
- **R2 — Banded truncation, corpus-local (recommended).**
  `intOpBos` is a sum of quartic monomials (four indices per
  monomial, `monoC`), so it moves sectors by Δn ∈ {−4, −2, 0, 2, 4}
  only — a finite band. For a banded symmetric operator, the
  adjoint action is sectorwise *finite*; the core property
  (Dom = finite-particle vectors is a core for the closure) reduces
  to one ℓ² tail estimate: truncations of an adjoint-domain vector
  converge in graph norm, the estimate fed by the (n+2)² relative
  bound and the band's finiteness. No general theorem is built;
  the argument lives in `BosonicInteraction`'s own vocabulary.
  **M–L**, risk concentrated in the tail estimate.

**Verdict: RE-PRICED → M–L** as a campaign pair: **ESA-α (S)** —
restate the target as closure equality using the found API, prove
closability and `closure ≤ adjoint` from existing pieces;
**ESA-β (M–L)** — the domain argument via R2 (R1 held in reserve at
L if R2's tail estimate fails, and that failure would itself be a
publishable obstruction refinement). For today the item remains
*walled* — no off-the-shelf discharge exists — but the wall now has
a door drawn on it at a named price, and the parked dossier's
obstruction text is corrected in its first clause. Pitch 3's verdict
is untouched: the §6 headline remains unspendable unqualified until
ESA-β lands.

---

## 4. Rung 7 remainders — strong continuity **SPLIT**; Fock packaging **STANDS (M)**

Standing prices (scoping §2.3, inherited there from Rung 7): strong
continuity **S–M** bundled; Fock packaging **M**. Both re-derived.

### 4a. Strong continuity of the one-particle representation

The target is pinned in the corpus: `StrongContinuity_window`
(`MassShellMeasure.lean:976`) — and its in-file price note names the
discharge *exactly*: for translations, the statement is one
application of dominated convergence
(`tendsto_lintegral_of_dominated_convergence`) with dominating
function 4‖ψ‖² ∈ L¹ and pointwise convergence from
`Complex.continuous_exp`; the representation law and unitarity it
feeds on are already T1 in the same file. The audit confirms the
note: every ingredient is in place, and the Prop as pinned is the
*translation* statement (`a : Minkowski`, `⟨a, 1⟩`).

- **Translations: S — discharge-ready.** This is no longer a price
  so much as a sitting: one DCT application against in-file T1
  assets. **RE-PRICED (floor): S, named as the fleet's cheapest
  discharge-ready theorem.**
- **Lorentz part: S–M.** The in-file note prices the longer argument
  (C_c density in L² + uniform continuity on compacts). Since that
  note was written, MassShellBoost landed the x¹-boost with its
  Jacobian identity |φ′| = E′/E — exactly the domination control a
  generator-wise DCT along the boost parameter consumes; rotations,
  a compact parameter family, are DCT with domination on compacts.
  The residual risk is the route choice (generator-wise DCT for the
  three generator families + the standard dense-set/equicontinuity
  assembly, vs the note's C_c-density route, whose Mathlib density
  lemma for the shell measure is unverified). **S–M**, M-tail only
  if the density route is forced.
- **SchrodingerDynamics discharge: NONE (negative finding, checked).**
  Its `evolOp` is finite-dimensional spectral machinery; the shell
  argument is measure-theoretic DCT on an Lp space. No lemma, route,
  or pattern transfers. Do not let the dynamics landing be quoted as
  progress on this window.

### 4b. Fock packaging of the one-particle representation

Target: `SecondQuantization_window` (`PoincareAction.lean:323`) —
a Γ(U₁) on a Fock carrier with representation law and vacuum
invariance. Two routes exist in principle; the audit rules on both:

- **The abstract route stays BLOCKED (re-confirmed).** The in-file
  price (MassShellMeasure §(c)) names the fundamental gap: no inner
  product on `SymmetricAlgebra ℂ V` satisfying the permanent formula
  in Mathlib, hence no completion, no unitarity statements.
  Re-grepped today: 0 hits for any SymmetricAlgebra inner-product
  construction. The blocker is verbatim as parked.
- **The concrete ONB port is the route — price M STANDS.** The
  corpus now owns the destination shape: Pitch 2 built the
  countable-mode Fock space concretely (`BosonicFockLim := lp (fun _
  : ConfigLim => ℂ) 2` over `ConfigLim := Finsupp ℕ ℕ`,
  `BosonicLimit.lean:198,69`) with Hilbert bases and isometric
  embeddings, and the finite-d Γ functor with its permanent
  Cauchy–Binet (repeated indices) in `BosonicGammaFunctor.lean`.
  What the port still owes, decomposed: (i) U₁ packaged as a
  `≃ₗᵢ` (MassShellMeasure's own missing piece #2 — from
  `oneParticleFun` via `MemLp.toLp`; **S**, mechanical); (ii) an
  ONB for the shell space + separability side-lemmas (**S** —
  Mathlib stock for separable Hilbert spaces; the shell L² space's
  separability is the checkable side-condition); (iii) the Γ-kernel
  for a *general* unitary at the limit — the LimitOps files carry
  rectangular finite-stage kernels (`gammaKernelRect`), and grep
  confirms no limit kernel for an ℕ×ℕ matrix exists yet; defining
  Γ(U) config-wise by finite sub-permanents of U's matrix in the
  chosen ONB, with unitarity via the infinite Cauchy–Binet, is the
  campaign's core (**M**); (iv) representation law + vacuum
  invariance assembly from the functor laws (**S**). Total **M**,
  upper end — the inherited price survives re-derivation
  **STANDS-AS-PRICED**, now with its route pinned and its abstract
  alternative re-killed.
- **SchrodingerDynamics discharge: NONE** (same negative finding as
  §4a; the synergy is downstream — a packaged free Fock
  representation is what a future free-field dynamics would consume
  — and downstream value is not a price cut).

---

## 5. Schrödinger smalls — both **STANDS-AS-PRICED**

Evidence: dossier `schrodinger-dynamics-2026-10-17.md` (module
STANDS, 49 T1; `evolOp` constructed diagonally via
`eigenvectorBasis` and *characterized* as the exponential by the
Schrödinger equation + uniqueness, `evolOp_unique`).

- **5a. Literal `NormedSpace.exp` identification · S — confirmed,
  one sitting: YES.** Route, fully determined by in-corpus assets:
  for each ψ₀, the curve t ↦ `NormedSpace.exp (−it • T̂) ψ₀` in the
  CLM algebra satisfies the same ODE (Mathlib's exp-derivative along
  scalar multiples — the lemma the 2026-10-16 gauntlet already
  located in `Mathlib/Analysis/SpecialFunctions/Exponential.lean`)
  with the same initial value; `evolOp_unique` identifies the curves
  pointwise in ψ₀; two continuous linear maps agreeing on every
  vector are equal. Est. 150–300 lines. The only risk is
  lemma-name/form friction against the pinned Mathlib — friction,
  not content. **One-sitting build: yes.**
- **5b. Dyson first-order term · S–M — confirmed, split named.**
  **Dyson-α (S):** define the first-order interaction-picture term
  W₁(t) := −i∫₀ᵗ heisenbergEvol_free(s)(g • intOp W) ds as an
  interval integral of a continuous CLM-valued curve
  (`heisenbergEvol` and its derivative law stand in
  SchrodingerDynamics), and characterize it: W₁(0) = 0,
  dW₁/dt = −i • V_I(t) (FTC for interval integrals — Mathlib
  stock). **Dyson-β (M):** the full Duhamel identity for the
  interacting evolution against the free one, with the integral
  remainder as a theorem (not a notation) — the content that makes
  "first-order" an approximation statement rather than a definition.
  The parked S–M is exactly α + β; it stands.

---

## 6. The `adag` namespace repair · **SCOPED + PRICED (S–M)**; Yukawa · **M–L**

**The obstruction, forensically.** `FermionicFock.lean` and
`BosonicFock.lean` both declare in `namespace ThetLogos`, and the
name intersection of their declaration sets is exactly four
constants (computed by intersecting line-initial declaration
names):

```
adag        FermionicFock.lean:361  End ℂ (FermionicFock d)
            BosonicFock.lean:186    Dom d →ₗ[ℂ] Dom d
ann         (same pair of files)
adag_basis  (theorem, both files)
ann_basis   (theorem, both files)
```

Same fully-qualified names, different types — the two files cannot
be imported into one environment (the duplicate-declaration
collision, including generated auxiliaries). The rest of the joint
closure is clean, also verified: the declaration-name intersection
of `FermionicInteraction.lean` ∩ `BosonicInteraction.lean` is
**empty**, and there are **zero** qualified `ThetLogos.adag` /
`ThetLogos.ann` uses anywhere in the tree (all uses are bare,
in-namespace), so a rename has a bounded, enumerable blast radius.

**The repair, scoped.** Rename the *bosonic* side (the fermionic
`adag` is the older name, cited across Rung 5/8/9/10 and Pitch 2/3
prose; the bosonic side already suffixes its coordinate variants —
`adagC`/`annC` in `BosonicAssembly.lean` — so suffixing is the
house pattern): `adag → adagBos`, `ann → annBos`,
`adag_basis → adagBos_basis`, `ann_basis → annBos_basis`, at the
definitions in `BosonicFock.lean` and at every bare use site.
Use-site census (grep `\badag\b|\bann\b` per file): BosonicFock
internal 17, `BosonicAssembly` 46, `BosonicSecondQuant` 16,
`BosonicInteraction` 3 — **82 sites in 4 files**, plus the fermionic
side untouched (89 sites in 3 files, not modified). Then: rebuild
the bosonic chain module by module (BosonicFock → BosonicAssembly →
BosonicSecondQuant → BosonicGamma → BosonicGammaFunctor →
BosonicInteraction → BosonicLimit → BosonicLimitOps), and the
campaign's actual deliverable — **a co-import smoke module**:
imports both Fock parents (transitively both interactions), states
a trivial mixed object (e.g. the joint vacuum and one mixed
operator), builds green. The smoke module is the proof the repair
worked; a rename without it is a claim, not a repair.
**Price: S–M.** The work is mechanical (word-boundary rename, no
proof content changes); the M-tail is build-iteration time on the
heavy bosonic modules (BosonicInteraction's targeted build is
~2,700 jobs) and any hidden shadowing the census can't see
(none known; the census is the evidence).

**The Yukawa campaign it unlocks · M–L.** Scoped here for the
first time, fenced precisely. *Setting:* finite modes both sides,
df fermionic + db bosonic. Because the fermion factor is
finite-dimensional, no completed Hilbert tensor product is needed:
the joint space is ℓ² over the *product config type*
(Finset (Fin df) × Config db) — the same lp-over-configs
construction both parents use — with joint finite-particle domain
(the fermionic factor is automatically finite). Fermion creators
act on the Finset factor (bounded), boson creators on the Config
factor (Dom-relative); cross-factor operators commute *on the
nose* in this presentation (no Koszul sign arises — the bosonic
factor carries no fermion parity; the joint CAR/CCR split is a
theorem to state, not a convention to assume). *Interaction:* the
Yukawa-shaped term H_int = Σ Y_ijk (adag_f i ∘ ann_f j) ⊗
(adag_b k + ann_b k) — fermion density ⊗ bosonic field.
*Targets, mirroring Pitch 3 exactly:* symmetry on the joint
domain; number-relative bounds (density factors bounded, field
factor (N_b + 1)^{1/2}-relative — B1's bosonic calculus ports);
windowed gap persistence in the Pitch-3 form; the not-a-dΓ
certificate for the mixed term. *Inherited walls, stated in
advance:* essential self-adjointness inherits §3's wall verbatim
(ESA-β is the same door); uniform (non-windowed) persistence is
**false** for the mixed term by embedding Campaign 2's proved
attractive-collapse counterexample at the fermion vacuum — the
disproof ports, and the module must carry the window in its
statements from line one. *What it is not:* not the Standard
Model Yukawa sector (no spinor structure, no chirality, no gauge
covariance, no continuum), and it changes no SM-Match verdict.
**Price: M–L** (one module, est. 900–1,500 lines by Pitch-3
calibration; new content = product-config presentation +
cross-factor commutation + bound assembly; the spectral arguments
are ports). Hard prerequisite: the repair above, verified by its
smoke module.

---

## 7. Bridge follow-ons · **RE-PRICED (sized)**

Evidence: dossier `bridge-laplacian-2026-10-17.md`; module
`BridgeLaplacian.lean` (466 lines, 29 T1) with `fiedler w := sInf
(fiedlerSet w)` over mean-zero unit-norm potentials,
`fiedler_le_energy` + `fiedler_nonneg` standing, attainment and
decay named as priced-not-attempted in the header.

- **Attainment of the Fiedler infimum · S.** The admissible
  potentials are a closed subset of the unit sphere of the
  finite-dimensional space (V → ℝ) — compact (finite-dimensional ⇒
  proper; Mathlib's compactness for closed bounded sets applies);
  the energy is a polynomial, hence continuous; attainment is
  `IsCompact.exists_isMinOn` plus the identification of the attained
  minimizer as an eigenvector for the attained value on the
  mean-zero subspace (Lagrange condition in finite dimensions —
  the one real lemma). One sitting to one small module section:
  **S**.
- **Exponential decay of Ḟ = −LF at the Fiedler rate · M.**
  With attainment: the Fiedler value *is* the smallest positive
  eigenvalue λ₂ of L (variational characterization completed by
  §attainment + the eigenbasis expansion: energy of a mean-zero
  unit vector is a convex combination of eigenvalues ≥ λ₂). The
  flow is then defined eigenbasis-wise — a direct port of
  SchrodingerDynamics' `evolOp` pattern (spectral phases; here
  real decaying exponentials e^{−λt} on the eigenbasis of a
  symmetric function-level operator, the transport of
  `laplacianOp` through its bilinear form being the friction) —
  with dF/dt = −LF as a derivative theorem and the decay estimate
  ‖F(t) − mean‖ ≤ e^{−λ₂t}‖F₀ − mean‖. **Package (attainment +
  λ₂-identification + decay): M**, attainment alone S.
- **The Faraday storey · S–M — and LatticeGauge does NOT cheapen
  it (ruled).** The hope under test: Stage 0 now has plaquettes,
  fluxes, and loop products, so the Bridge's missing cycle/flux
  data might be importable. It is not, and the reason is type-level,
  not effort-level: BridgeLaplacian's objects are **ℝ-valued**
  potentials and flows on an *abstract finite graph* (V, w), with
  the additive telescoping KVL (`dropVec_telescope`);
  LatticeGauge's plaquettes are **group-valued** holonomies on a
  cubical 4D torus, whose loop calculus (`loopProd`,
  `loopProd_plaquetteSteps`) is multiplicative in a generally
  nonabelian G. A Faraday storey for the Bridge needs a *face
  structure on the Bridge's own graph* (a chosen 2-chain/faces
  datum), an ℝ-valued flux per face, and the discrete Stokes
  identity (drop-sum around a face boundary = flux) — the additive
  ℝ shadow that the nonabelian lattice objects do not provide.
  What transfers is only the *pattern* (paths as lists, telescoping
  by induction — already the Bridge's own pattern since
  `dropVec_telescope`). **Verdict: genuinely different objects;
  price essentially unchanged: S–M** (faces datum + flux variable +
  Stokes/telescoping identity + the EMF = −dΦ/dt statement as a
  definition-theorem pair, header-fenced as graph-Faraday, not
  Maxwell). The storey remains a Bridge-local build.

---

## 8. Theories-intake Round 2 · BRST **M**; Dixmier **S–M**; OS item **SPLIT** (fit half KILLed)

Queue of record (`theories-intake-2026-10-11.md`, Intake queue):
BRST/anomalies; the Osterwalder–Schrader reconstruction bridge;
noncommutative integration / Dixmier trace. Intakes are audits with
fit-test Lean files (Round 1 calibration: one file + dossier per
candidate, T1s where the fit is real), priced as such.

- **BRST / anomalies — stands as an intake, M.** Untouched by
  Pitch 4 (the pitch is gauge-fixing-free by design — Stage 0's
  pre-kill), which is exactly why the intake has content: the fit
  test must confront a formalism whose standard presentation
  *requires* gauge fixing + ghosts against a corpus that proves
  exact invariance without either. The predictable honest shape —
  BRST as pure algebra (a nilpotent differential on a graded
  complex built from the finite triple's fluctuation data) FITs as
  algebra; BRST as a quantization procedure NO-FITs against the
  corpus's stance; the anomaly side tests against the finite
  triple's actual cocycle content. The intake's job is to make
  those verdicts theorems-and-greps rather than expectations.
  **M** (one fit-test file + dossier, Round-1 calibration).
- **Dixmier trace / noncommutative integration — stands as an
  intake, S–M.** Unrelated to Pitch 4 (spectral side, not lattice
  side). At finite level the Dixmier trace on the finite triple is
  a finite, computable shadow (the noncommutative integral as a
  residue/trace functional on the finite algebra) — a FIT-at-finite-
  level verdict is there to be tested with real theorems; the
  continuum Dixmier trace (singular traces on compacts,
  measurability) is the predictable NO-FIT/window half, needing
  the analytic house Round 1 already fenced. **S–M.**
- **The OS bridge item — SPLIT.**
  - **Fit half: KILLed as redundant.** The intake would ask: does
    the corpus's OS pin match the literature, and does the corpus
    hold OS-shaped objects? Pitch 4 has absorbed both questions
    with more precision than an intake would: Stage 1b (§1) proves
    the finite-lattice reflection positivity — the E2 content in
    the form the program can actually own — and Stage 3a is scoped
    to re-pin E0–E4 *as conditions on the lattice program's own
    Schwinger data*, with the uniform obligations named. Running
    the Round-2 fit audit now would produce a second, divergent
    pin of the same axioms and a verdict Pitch 4 supersedes on
    arrival. **KILL — absorbed, not merely postponed.** (What dies
    is the duplicate audit, not the subject.)
  - **Re-pin / reconstruction-audit half: STANDS as a distinct
    intake, S–M.** Two contents Pitch 4 does *not* do: (i) the
    corpus's own `OsterwalderSchrader.lean` is stale in a named
    place — its header asserts "Mathlib (2026) has no tempered
    distributions" and its `SchwingerMarker` is an opaque
    placeholder, but the Pitch 4 scoping's §5 audit established
    the pinned Mathlib **has** 𝓢′ (tempered distributions) with
    Fourier theory; the E0–E4 bundle can and should be re-pinned
    with distribution-valued Schwinger functions as real objects,
    shrinking the opaque-Prop surface. That is file maintenance on
    the axioms pin, not a Pitch 4 stage (3a re-pins the *target
    for the limit*, not this file). (ii) The reconstruction theorem
    itself (OS ⇒ Wightman) as an audited object — its proof's
    actual dependency list (analytic continuation,
    edge-of-the-wedge, growth control) priced against Mathlib —
    lives in §9-wall territory for Pitch 4, which names it as an
    obligation but does not audit it; the intake is the audit.
    **S–M** (dossier + re-pin of the file's statement layer; no
    proof of reconstruction is priced or implied).

---

## 9. Decoherence toy · **STANDS-AS-PRICED (S–M)**

Re-derived from the Schrödinger gauntlet §4c, re-grepped today.
Assets: density matrices exist (`IsDensityMatrix`,
`FlowKernel.lean:270`, with the Gibbs/KMS apparatus); operator
tensor/Kronecker tools exist (ProductTriple's `opTensor`, Mathlib
Kronecker in corpus use). The missing piece is exactly where the
gauntlet left it: **partial trace — 0 hits in the corpus (grep
`partial.?trace|traceLeft|traceRight` over `ThetLogos/`), and 0
hits in the pinned Mathlib checkout (grep `partialTrace|
partial_trace`)**. Nothing landed since (SchrodingerDynamics
included) touches it. Decomposition, confirmed: **PT-1 (S)** —
partial trace at the matrix level over Fin m × Fin n factors:
definition by block trace; trace preservation; positivity
preservation; the product rule Tr_B(A ⊗ B) = Tr(B)·A; adjoint/star
compatibility. **PT-2 (S)** — the toy on top: dephasing channel as
diagonal pinching in a product basis; populations invariant;
off-diagonals killed in one application (geometric decay under
iteration); purity Tr ρ² non-increasing, equality iff already
diagonal; reduced diagonal = system populations. Header-labeled
TOY (finite-dimensional, single channel, no environment dynamics;
the measurement problem remains T5 by type, per the gauntlet §4b).
**Total S–M, unchanged.** Noted for the priority order: this is
the fleet's cheapest fully standalone landing — it waits on
nothing.

---

## 10. Paper v3 · **PRICED — S (assembly)**; contents delta exact, one catch

V2 of record: `acmd-machine-verified-foundations-v2-2026-10-16.md`
(§§0–17 + Appendix A; program total at its freeze: 1,648). Assembly
is not research: the paper pipeline exists (`build_paper.py`), the
dossiers for every increment exist, and the v2 addendum pattern
(§0's "increments since the freeze") is the template. **Price: S**
— a section-writing + audit + rebuild + Zenodo-version pass.

**Contents delta vs v2, exact list:**

1. **Pitch 3 verdict** (new section): Campaign 1 whole (fermionic
   interaction, gap persistence), Campaign 2 with the §6 headline
   carried *unspendable-unqualified* exactly as its dossier states
   it — bosonic package stands, essential self-adjointness priced
   (and, if this gauntlet's §3 has landed by assembly time, with
   the corrected obstruction: closure API exists, equality
   unproved, crack named).
2. **SchrodingerDynamics** (new section): 49 T1, picture
   equivalence, gap persistence in time; the exp-identification
   and Dyson follow-ons named as priced.
3. **MassShellBoost / Rung 7 discharge** (§7 amendment): the boost
   window discharged whole — the x¹-boost Jacobian identity and
   the factorization cap; Rung 7's priced remainders updated to
   this gauntlet's §4 prices.
4. **Bridge exhibit** (Appendix-A-fenced, per the v2 pattern for
   background algebra): L = dᵀσd, Kirchhoff package, Fiedler bound;
   follow-ons priced per §7.
5. **Pitch 4, Stages 0 + 1a** (new section): the pitch scoped
   (lattice route, PARTIAL shapes named), Stage 0 stands (68 T1),
   Stage 1a stands (68 T1, Elitzur at general (G, ρ)); pitch-level
   shape stated as PARTIAL-β with 1b/1c prices attached — and, if
   §1 of this gauntlet has landed by assembly time, PARTIAL-δ.
6. **The ACK credit line**: the staircase acknowledgment (the
   repo's `ACKNOWLEDGMENTS.md`, landed 2026-10-17 under Jeff's
   "make sure the true credit goes to them") carried into the
   paper as its credits text — cite the originators first.
7. **Count + inventory refresh**: 1,648 → 2,216 (Δ +568:
   Pitch 2's 141 — see the catch — Pitch 3 C2's 69, Schrodinger
   49, MassShellBoost 86, Bridge 29, Stage 0 68, Stage 1a 68,
   Weld/Γ-era increments already in v2's count where applicable;
   the assembly pass re-derives the total by the standing grep
   method rather than trusting this arithmetic).

**THE CATCH (flagged at full strength).** The owed-list this
gauntlet was handed — Pitch 3 verdict, SchrodingerDynamics,
MassShellBoost, Bridge, Pitch 4 Stages 0+1a, ACK line — **omits
Pitch 2**, and v2 needs it: Pitch 2 (free theory at countably many
modes, STANDS WHOLE, 141 declarations) landed the night v2
published, *after* its freeze, and v2's §16 NOT-claimed list
consequently carries a now-false line — "No infinite-mode or
continuum Γ" (v2 md lines 903–905) — contradicted by the corpus
since 2026-10-16 ~21:19 EDT. A v3 assembled from the handed list
alone would re-ship that stale line. **Ruling: Pitch 2 is item 0
of the delta** (new section: Campaigns A + B, the Δ-general free
gap at countable modes in the eigenvalue-on-finite-particle-domain
sense, the spectral statement priced), and the assembly includes a
**full NOT-claimed audit**: every line of §16 re-checked against
the current corpus, stale lines amended in the open (the v2→v3
diff is public; the amendment is recorded in §0's addendum, per
house pattern — never silently edited).

---

---

## THE PRIORITY ORDER — the fleet, sequenced

Execution sequence for the whole parked fleet, one-line rationale
each. (Pitch 4's own Stage 2 sits in plan position after Stage 1
and is not part of this fleet; Stage 1c proper and Stage 3/4 remain
parked behind §2's kill criteria and the scoping's §9 wall.)

1. **1b-A — reflection structure pack + action split (M).** The
   gate for the entire back half of Pitch 4's landing, and the
   cheapest fail-fast probe of the torus fixed-stratum
   combinatorics — if a monster lives in 1b, it lives here, and it
   should be met first and cheapest.
2. **1b-B — reflection positivity proper (L).** The §8-named
   hardest step, taken while 1b-A's bookkeeping is warm; A + B
   together already earn the PARTIAL-δ shape.
3. **1b-C — OS space, time-slice route (M).** Decided route, no
   drift; converts positivity into a Hilbert space.
4. **1b-D — transfer matrix + lattice gap (M).** Completes Stage
   1b whole (§8 item 2): the gauge sector's first
   Hamiltonian-shaped object, honestly labeled.
5. **Paper v3 assembly (S).** Owed, cheap, and now also carries
   1b; kills the stale public NOT-claimed lines (a Concrete
   exposure that should not outlive another landing).
6. **`adag` repair (S–M).** Mechanical, bounded (82 sites), and
   removes the standing absurdity that the program's two Fock
   halves cannot coexist in one environment.
7. **Yukawa campaign (M–L).** The first new physics-shaped object
   since Pitch 3; consumes both parents the day the repair's smoke
   module is green.
8. **ESA-α (S) → ESA-β (M–L).** α is a sitting (the target,
   restated sharply, using the closure API this gauntlet found);
   β closes Pitch 3's last clause — the fleet's highest
   verdict-changing value per campaign.
9. **Strong continuity — translations (S).** Discharge-ready
   (named lemma, named dominator, all inputs T1): the fleet's
   cheapest theorem; slot it as a palate cleanser between heavy
   campaigns, but not before the plan's critical path (1–4).
10. **1c-0 — finite-order strong-coupling exhibit (M).** Opens the
    1c ladder at exhibit scale and stress-tests the expansion
    route against KILL-1c-α while failure is still cheap.
11. **Fock packaging (M; U₁-as-≃ₗᵢ (S) folded in as step 0).**
    Completes Rung 7's free side and is the prerequisite for any
    future free-field dynamics on the shell.
12. **Strong continuity — Lorentz part (S–M).** After 11 (same
    file's neighborhood, shared Lp machinery); the boost Jacobian
    asset is already in hand.
13. **Schrödinger smalls — exp identification (S), Dyson-α (S),
    Dyson-β (M).** One-sitting and near-sitting items that close
    the dynamics exhibit's fenced shortfalls.
14. **Bridge spectral completion (M; attainment S inside).**
    Closes the Bridge exhibit's own priced follow-ons; the
    Faraday storey (S–M) rides along only if Jeff wants the
    second storey — it is exhibit furniture, not ladder.
15. **Decoherence toy (S–M).** Cheapest fully standalone landing
    in the fleet; waits on nothing; schedule it whenever a light
    week wants a certain green.
16. **Round 2 intakes — OS re-pin (S–M), Dixmier (S–M), BRST
    (M).** Audits, valuable and unhurried; the OS re-pin goes
    first among them because it repairs a stale premise in a
    standing axioms file.
17. **1c proper (XL) — stays parked.** Behind KILL/PARK criteria
    §2; revisited only when 1c-0 has reported and the animal-
    enumeration infrastructure question has an answer.

**The single item to run first tomorrow: 1b-A** — *Reflection
structure pack and the Wilson action split across it.* Campaign
shape: hypotheses pack (Θ, trichotomy, ΘσΘ relations) stated in
Stage 0's abstract style; the split identity
S_β = S₊ + S₋ + S₀ proved under the pack; the pack discharged on
the concrete torus at even N with the fixed stratum enumerated
(both reflection conventions computed, one chosen and disclosed);
§8's mandatory header clauses carried. Its landing either hands
1b-B a clean factorization to prove positivity from, or discovers
— at M prices, not L — that the torus combinatorics needs a
different setup. Either outcome is a result.

## Kill ledger (this gauntlet)

- **K1.** The XL tail of Stage 1b's L–XL — killed (§1): its three
  cost drivers (measure construction, undecided OS route, split
  bookkeeping) are discharged, decided, and partially pre-built.
- **K2.** The clause "Mathlib has no LinearPMap closure operator"
  in Pitch 3 Campaign 2's obstruction — killed as stale (§3): the
  closure operator and its API exist
  (`Topology/Algebra/Module/LinearPMap.lean:94`); only the equality
  theorem is missing.
- **K3.** Round 2's OS *fit-audit* — killed as redundant (§8):
  absorbed by Pitch 4 Stages 1b/3a; a duplicate pin is a liability,
  not a backup.
- **K4.** The abstract (SymmetricAlgebra) route to Fock packaging
  — re-killed on re-grep (§4b): the permanent inner product does
  not exist in the pinned Mathlib; the concrete ONB port is the
  only route priced.
- **K5.** Any reading of 1c-0 (if built) as area-law evidence —
  killed in advance (§2): first order is perimeter; the area law
  is all-orders.

## Closing honesty

What this gauntlet changed: Stage 1b stopped being a band and
became four campaigns with a decided route and a landing shape;
Stage 1c acquired a first rung and three kill criteria with teeth;
Pitch 3's last wall got a door drawn on it (and its dossier a
corrected clause); two Rung-7 items were decomposed to their
actual discharge shapes; the corpus's most embarrassing structural
defect — two Fock halves that cannot share an environment — got a
bounded repair plan and the campaign it unlocks; the paper's
owed-list was caught missing an item whose absence would have
re-shipped a false NOT-claimed line. Nothing in this dossier is a
theorem. Every price in it is re-derived from today's corpus, and
the ones that survived say so; the ones that didn't, say why.
Parts of the official Clay Yang–Mills statement closed by this
dossier: 0.
