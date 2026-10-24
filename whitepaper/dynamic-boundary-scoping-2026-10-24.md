# The dynamic boundary (Jeff's fragment of 2026-10-24) — SCOPING CHARTER

**Date:** 2026-10-24. **Status: SCOPING (paper only). No Lean
built by this charter; census unchanged at scoping time.**
Commissioned by Jeff's ruling 2026-10-24 ("yes build it") on
his dictated fragment, held open verbatim:

> "can the degrees of freedom of expansion create a dynamic
> boundary of confinement, the charge collapse creates the
> dynamics of the boundary that reflects the dynamics into
> identity and symmetry"

The fragment is his candidate mechanism for his question of
the same morning — "could our boundary be created by the
interaction" — in the line of Gurd's Law ("Before
information can be processed or communicated, the boundary
must first be drawn and contained"; corollary, Jeff
2026-10-06: "the boundary creates identity"; ordering
ratified by Jeff 2026-10-24: principle → boundary → identity
→ information).

**NO CLAIM.** Parts of any official Clay statement closed by
this document: **0**. Stage 1b-B positivity: **T1 for U(1)**
at all β ≥ 0 (Route C); general (G, ρ) **OPEN**, owned by the
third-family F-chain (charter
`whitepaper/gram-third-family-scoping-2026-10-24.md`), not by
this charter.

**Scope fence, on the face.** The buildable content is the
FINITE seat only. Continuum confinement (QCD) is FRONTIER —
a sibling of the mass gap, unproved by anyone — and this
charter claims nothing there. "Charge collapse" has no
corpus seat as dynamics (§2.4); its only finite reading is
adjudicated there. The fragment as a whole is **T5** (Jeff's
ontology); §4 states which finite statements below are
T1-candidates and which readings stay FRONTIER/unseated.

---

## §1 Content audit — most of the fragment is already the landed architecture

The parent session's reading, checked against the dossiers:
the fragment's central images are not new proposals about
the corpus — they are descriptions of machinery that
landed this week. Item by item, with sites. **Nothing in
this section is re-queued.**

**1.1 The reflection plane IS a boundary — LANDED.**
Stage 1b-A's `splitEquiv halfLinks` splits configurations at
the time-reflection plane into the closed half and the
negative half; S1's L1/L2 built the reflection's slice
reading and the axis reflection `axisRefl` (reflection about
the axis through slices `0` and `N/2`), with the Gibbs
measure invariant under it (`gibbsMeasure_map_axisRefl`,
every real β). Sites: dossier
`whitepaper/gram-transfer-s1-depth-one-identification-2026-10-24.md`
§§L1–L2; module `LatticeTransferID`.

**1.2 The boundary has dynamics, and the dynamics is the
seam kernel — LANDED AS OBJECT; its positivity is Item 1's
open question.** R1's factorization: in split coordinates
the Gibbs measure is `Z⁻¹ • (halfGibbsPlus.prod
halfGibbsMinus).withDensity layerWeightZero`, where
`layerWeightZero = exp(−S₀)` and `S₀ = wilsonActionZero`
sums the temporal plaquettes based at the two fixed layers
`N/2 − 1` and `N − 1` — **the only plaquettes coupling the
two halves** (dossier
`whitepaper/gram-transfer-r1-layer-factorization-2026-10-24.md`,
headline `gibbsMeasure_map_splitEquiv`). The R2 obstruction
dossier then reduced all-vector positivity of the transfer
operator to positive-definiteness of exactly this seam
kernel. So "the boundary's dynamics" already has a name, a
definition, and a dossier; what is open about it is its
positivity at general (G, ρ) — which is Road Map Item 1,
being attacked by the F-chain, not by this charter (§2.1
names the one consolidation this charter adds).

**1.3 "Reflects the dynamics into identity" — LANDED AT
DEPTH ONE; the general statement is the OS programme
itself.** S1's headline `osForm_depthOne_transfer`: the OS
form's diagonal at a slice observable **is** the depth-one
transfer quadratic form at the prepared slice state — the
reflection pairing, read as an operator pairing. Whether
that pairing is positive (i.e. actually becomes the inner
product — the identity structure — of a physical Hilbert
space) is Stage 1b-B/1b-C territory: T1 for U(1), general
case OPEN, F-chain commissioned. The fragment's identity
beat is this programme in ontology's language; it is
already the road map.

**1.4 "…and symmetry" — LANDED.** R1's two half measures
are built from **the same half-action function
`halfActionP` on both halves** (the closed half by
`restrictPos`, the negative half through the mirror, by the
landed `wilsonActionMinus_eq_halfActionP`) — the boundary's
two faces are symmetric by theorem, and this identical-
halves fact is load-bearing (it is what R2's adjointness
question consumed). No new symmetry work is queued by the
fragment.

**1.5 "Degrees of freedom of expansion" — partially
seated.** More degrees of freedom = deeper observables /
more layers: S1 closes depth one; the depth-`N/2`
identification is queued as R3-identification in the
standing build order. The fragment's *generative* direction
— expansion CREATES the boundary — is not the corpus's
direction: in every landed finite statement the plane is
posited by the torus geometry and the seam is the leftover
coupling across it. §2.2 adjudicates the one finite
statement in the generative direction that is honestly
statable (stability of the boundary under expansion); the
stronger reading (a boundary arising unposited) gets no
brick — see the fence in §4.

---

## §2 The genuinely new finite core — adjudication of the three candidates

### 2.1 (a) The seam kernel as a named BOUNDARY OPERATOR — ACCEPTED, reshaped, small (brick DB1)

What exists: `layerWeightZero` as a density inside R1's
measure identity, and the seam kernel as the object of R2's
positivity reduction. What does not exist: the boundary as
a **named, citable object with its own basic theory** — the
thing Jeff's fragment asks for ("the boundary," as an actor
with dynamics). DB1 supplies exactly that, and no more:

- **Definition.** The boundary operator `Bdry` of the
  finite theory at `(G, ρ, β, N)`: the seam kernel in the
  form R2's reduction uses — the kernel/factor
  `layerWeightZero = exp(−wilsonActionZero)` on the split
  configuration space, packaged as one named object with
  its type and its place in R1's factorization stated once.
- **β = 0 form, computed.** At β = 0, `wilsonActionZero =
  0`, so `layerWeightZero ≡ 1`: the boundary operator at
  zero coupling is the trivial kernel (constant density 1;
  the halves decouple — product Haar, cf. S1's companion
  `osForm_depthOne_zero`). A stated theorem, not a remark.
- **Self-adjointness at the level statable.** The seam
  factor is a positive real function, and under the mirror
  exchange of the two halves it is symmetric — the action
  split `S = S₊ + S₋ + S₀` of R1 has `S₀` invariant under
  the reflection pairing (it is built from the plaquettes
  at the two fixed layers, which the reflection exchanges).
  DB1 states this as: the boundary kernel is real and
  mirror-symmetric, i.e. the quadratic form it defines (the
  form of R2's reduction) is self-adjoint at the level R2
  states it. **Fence:** DB1 does NOT assert
  positive-definiteness of the boundary operator — that is
  exactly Item 1's open question, whose answer is F3's
  output. Asserting it in DB1 would beg the question; the
  charter forbids it on its face (kill K-DB1(c)).
- **The confinement corollary (§2.3) folds in here** as a
  fourth component at no extra price.

Price and kills in §5. Honest classification: DB1 is
consolidation with one real theorem-shaped content (the
β = 0 computation and the mirror symmetry, stated about the
named object) — its mathematical weight is small and the
charter says so; its value is that "the boundary" becomes
an object the record — and F3's discharge — can quote.

### 2.2 (b) EXPANSION: does the boundary regenerate? — ACCEPTED IN REDUCED FORM (brick DB2); the attractor reading is KILLED at scoping

Setup: insert a layer pair, `N → N + 2`, adding two
consecutive time layers in the interior of the closed half
(away from the seam), with the obvious monotone index
transport carrying the old seam layers to the new seam
layers (`N/2 − 1 ↦ N/2`, `N − 1 ↦ N + 1` in base time). The
finite claim, two levels:

- **(b0) β = 0 control.** The boundary weight at β = 0 is
  `≡ 1` at every N (§2.1), and the inserted layers carry
  product Haar, which marginalizes to product Haar (the
  landed Q1 `posToSlice` marginal machinery is the tool):
  the boundary the expansion "creates" at zero coupling is
  the same trivial boundary operator, transported. True,
  and thin — stated as the control, not the headline.
- **(bβ) general β: locality transport.** `S₀` at `N + 2`
  sums plaquettes based only at the transported seam
  layers; the inserted layers' plaquettes belong to the
  half actions, not to `S₀`. Hence `layerWeightZero` at
  `N + 2`, as a function of the seam neighborhood, equals
  `layerWeightZero` at `N` under the index transport — the
  seam factor does not see the inserted bulk. This is the
  honest finite content of "expansion creates the same
  boundary": the boundary operator is **stable** under
  adding degrees of freedom in the bulk, because its
  definition is local to the seam.

**Killed at scoping:** the dynamical fixed-point reading —
repeated expansion converging to / attracting toward a
boundary — requires a limit over `N` and is a
continuum-limit-flavoured claim. No finite brick states it;
it is FRONTIER (§4), and DB2's statement must not be
quoted as evidence for it.

**Pre-registered kill (K-DB2(a)):** if the transported
boundary operator at `N + 2` differs from the `N` operator
by more than the stated identification (index transport +
Haar marginalization of the inserted layers) — e.g. an
inserted-layer plaquette is found inside `wilsonActionZero`
as defined, breaking locality — DB2 dies and the differing
factor is exhibited in the obstruction dossier, at landing
speed.

### 2.3 (c) CONFINEMENT in the finite seat — ALREADY BUILT in substance (R1); NO new brick

Candidate claim: the halves' observables pair **only
through the boundary** — cross-half correlations factor
through the seam operator. Adjudication: this is R1's
factorization read through its own consumer form. In split
coordinates the Gibbs density is `wPlus · wMinus · wZero`
(R1, `gibbsDensity_split` / `layerWeight_product`), and
`wZero` depends on each half's configuration only through
the links entering `S₀`'s plaquettes — the seam-layer
links. Marginalizing each half over its interior at fixed
seam links (Fubini; R1's shipped `integral_layerFactor_iterated`
is precisely the iteration tool) gives: conditionally on
the seam data, the two halves are independent, and every
cross-half pairing factors through the seam kernel. That
is a corollary of landed statements plus one Fubini step —
not a new brick, and the charter does not re-queue it as
one. It is recorded here so the fragment's "confinement"
beat has its finite address on the record (R1), and DB1
(§2.1) states the corollary explicitly about the named
boundary operator: *pairing through the boundary* — the
only channel between the halves is `Bdry`. The continuum
meaning of confinement is untouched and unclaimed (§4).

### 2.4 "Charge collapse" — adjudicated: honest as the F-chain's static trace contraction; a STRETCH as dynamics; no brick

The finite reading on offer: inside the seam weight, each
crossing plaquette contributes
`exp((β/d) · Re ⟨ρ(y), ρ(τ⁻¹uτ′)⟩_HS)`, and the
Hilbert–Schmidt inner product is a **trace over the
representation indices** — by cyclicity,
`tr ρ(U_p) = ⟨ρ(y), ρ(τ⁻¹uτ′)⟩_HS` (third-family charter
§2.1, with its SU(2) certificate). In that static,
bookkeeping sense, the plaquette's representation data
("charge data," in the fragment's word) does collapse —
contract — into the single scalar that drives the boundary
weight. **Verdict: that reading is honest, and it is
already owned**: the identity is F1's theorem content in
the F-chain (building now), not a new brick of this
charter. As **dynamics** — charge evolving, collapsing in
time, and thereby *creating* the boundary's motion — the
reading is a stretch and is rejected as a charter basis:
nothing in the corpus evolves charge; charges and
hypercharges enter as matched inputs (MEMORY, Track 2–4),
there is no time evolution for them to collapse under, and
"collapse" survives only as a T5 name for the trace
contraction. Dynamic charge collapse: **unseated**, no
brick, FRONTIER-adjacent (§4). This charter will not let
the word do T1 work.

---

## §3 What this charter deliberately does NOT build

- No proof that a boundary can arise **unposited**. Every
  finite statement here lives on the posited reflection
  plane of the torus; the bricks study the boundary's
  dynamics, symmetry, and stability on that plane. Jeff's
  generative question stays T5 with its finite rhyme
  recorded (§1, §2.2), exactly as his ratified ordering
  (principle → boundary → identity → information) is a
  doctrine statement, not a corpus theorem.
- No new attack on positivity. The F-chain owns Item 1's
  positivity half; DB1/DB2 consume nothing it needs and
  assert nothing it must prove.
- No continuum statement of any kind: no confinement
  claim, no limit, no gap. (Road Map Items 2–5 untouched.)

---

## §4 The ontology fence (on the face)

- **T5 (Jeff's ontology, no corpus claim):** the fragment
  as a whole; "expansion creates the boundary" as a
  generative doctrine; Proto-Thet / Gurd's Law framing.
- **T1 (landed, cited, not re-queued):** reflection plane
  as boundary (S1/R1); seam kernel as the boundary's
  dynamics (R1; positivity reduction R2); identical halves
  as symmetry (R1); depth-one reflection-into-identity
  (S1); finite confinement-as-factorization (R1, §2.3).
- **T1-candidates (this charter's bricks, unbuilt):** DB1
  (the named boundary operator: definition, β = 0 form,
  mirror symmetry, the through-the-boundary corollary);
  DB2 (expansion stability: β = 0 control + general-β
  locality transport).
- **FRONTIER / unseated (no brick, no claim):** continuum
  (QCD) confinement; charge-collapse *dynamics*; a
  boundary arising unposited; the expansion-attractor /
  repeated-expansion limit reading of (b).
- **NO CLAIM; Clay parts closed: 0.** Stage 1b-B label
  unchanged: T1 for U(1); general (G, ρ) OPEN until F3.

---

## §5 Ladder (prices; pre-registered kill criteria)

Prices in the house scale (S = one brick; M = a module with
real content; L = research-scale brick). Dependencies are
on landed statements only. Standing build order (Jeff,
2026-10-24): F1 (building) → F2 → F3 → R3-identification →
B4′ → B4. This charter's bricks slot **after the F-chain**
(no dependency argues otherwise — F2/F3 neither need nor
consume them), **before R3-identification by this charter's
choice** (their statements complete the fragment's finite
content while the seam is the active front; nothing
downstream consumes them, so the placement is movable at
Jeff's word without breakage).

**DB0 — this charter (paper). Price: S. DONE as scoped.**
Content audit (§1), adjudications (§2), fence (§4), kills
registered below before any build, per the Concrete.

**DB1 — the boundary operator as a named object.
Price: S** (ceiling S–M; re-price in the open if the
packaging exceeds it — see K-DB1(a)).
New module (house name, e.g. `LatticeBoundaryOp`):
definition of `Bdry` from `layerWeightZero` in the form
R2's reduction uses; `Bdry` at β = 0 is the trivial kernel
(`layerWeightZero ≡ 1`); reality + mirror symmetry of the
seam kernel (self-adjointness of its quadratic form at the
level R2 states); the identification of R1's factorization
with `Bdry` as its density; and §2.3's corollary — every
cross-half pairing factors through `Bdry` (R1 +
`integral_layerFactor_iterated`). Dependencies: R1
(`LatticeLayerFactor`), the action split, Q1 marginals as
needed. **Positive-definiteness is NOT a DB1 statement**
(§2.1 fence).
*Kills, pre-registered:*
- **K-DB1(a)** — the operator packaging forces a
  disintegration or a mid-layer marginal not present in
  R1's factorization. R1's whole content was achieving the
  split with finite density algebra and no disintegration;
  a boundary operator that needs one is an artifact of the
  packaging, not of the corpus. Kill DB1; the seam kernel
  stays a density, and the fragment's finite address stays
  R1 as-is.
- **K-DB1(b)** — the mirror symmetry fails at the stated
  level: `wilsonActionZero` is found not invariant under
  the reflection exchange of the halves. (This would
  contradict the landed action split's structure, so this
  kill doubles as a consistency check on §1's audit.) Kill
  with the asymmetric term exhibited.
- **K-DB1(c)** — charter-violation fence, registered so it
  cannot happen silently: any DB1 draft asserting
  positive-definiteness (or positivity on any vector class)
  of `Bdry` at general (G, ρ) is out of charter — that
  statement is F3's output or nobody's.

**DB2 — expansion stability (the finite fixed point).
Price: M** (the β = 0 level alone is S; the general-β
index transport is the content).
Layer-pair insertion `N → N + 2` with its configuration
embedding and index transport constructed as plumbing;
(b0) at β = 0 the boundary weight is invariant under the
insertion, the inserted Haar layers marginalizing away
(Q1's `posToSlice` machinery); (bβ) at general β the
transport identity for `layerWeightZero` (locality of
`wilsonActionZero` under the transport). Dependencies:
DB1 (the statement is quoted about the named operator —
this dependency is why DB1 precedes DB2), R1, Q1.
*Kills, pre-registered:*
- **K-DB2(a)** — the transported operator at `N + 2`
  differs from the `N` operator by more than the stated
  identification (index transport + Haar marginalization):
  kill, with the differing factor exhibited (cf. the R2
  dossier's practice of shipping the obstruction at full
  rank).
- **K-DB2(b)** — the β = 0 control fails: marginalizing the
  inserted layers does not return the boundary weight.
  Kill — (bβ) without its control is unanchored, and the
  brick does not proceed to the general-β level on a failed
  control.
- **K-DB2(c)** — scope fence, not a kill of the finite
  brick: any statement requiring iteration to a limit
  (attractor, `N → ∞` stability, rescaling) is out of
  charter (FRONTIER, §4) and must not be attached to DB2's
  landing.

**Charter total beyond DB0: DB1 S + DB2 M.** Both bricks
are consolidation-grade, and the charter prices them as
such: the road map's critical path (Item 1's positivity) is
the F-chain's, and nothing here pretends otherwise.

---

## §6 Honest unknowns

- **U1 — DB1's packaging has one real choice in it.**
  R2's reduction speaks of the seam kernel's
  positive-definiteness; R1 lands the seam factor as a
  density on the split (product) space. Whether the named
  operator is packaged on the split space or on a
  mid-layer space determines DB1's exact statements. This
  charter fixes the choice to **R2's reduction form**
  (the form in which positivity is a property of the
  object), and prices the residual risk as K-DB1(a). If
  the packaging fight exceeds the S–M ceiling, DB1
  re-prices in the open before building — never mid-build.
- **U2 — DB2's transport maps are not landed objects.**
  Configuration embeddings under layer insertion, and the
  relabeling of `wilsonActionZero`'s plaquette sum under
  them, are plumbing this charter prices inside DB2's M.
  If the plumbing prices beyond M, re-price before
  building.
- **U3 — the fragment's remainder after this charter.**
  After DB1 + DB2, the fragment's finite content is
  exhausted: what remains of it (generative boundary,
  charge-collapse dynamics, continuum confinement) is T5 /
  FRONTIER with no named finite seat, and stays so until a
  new finite statement is proposed and scoped on its own.
  The charter does not manufacture one.

— BONES, for the record. The fragment was audited against
the ledger before it was built on; what was already built
is cited, not re-queued; kills are registered before
builds, and negative verdicts ship at the same speed as
positive ones.
