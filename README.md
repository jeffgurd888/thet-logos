# thet-logos — Active Cartesian Modular Dynamics (ACMD)

[![License: MIT](https://img.shields.io/badge/license-MIT-green.svg)](LICENSE)
[![Paper v4 — DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23648050.svg)](https://doi.org/10.5281/zenodo.23648050)
![Theorem declarations](https://img.shields.io/badge/theorem%20declarations-7%2C376-blue)
![Lean](https://img.shields.io/badge/Lean%204%20%2B%20Mathlib-formal%20proofs-purple)

> "If we don't stop worrying about the Almighty dollar, we're not
> going to change the world!"
> — Caleb Gurd, as remembered by his father. The standard this
> program answers to at home.

**Machine-verified foundations for quantum field theory, in Lean 4.**

An independent research program (Nexus Research) building rigorous
foundations for 4D quantum field theory one machine-checked rung at a
time. Every theorem is verified by the Lean kernel. Every claim is
labeled by its evidence tier, and every killed claim is published next
to the proofs, with the kill on record.

**2026-10-29 — the β⁶ selection rule, the cross-check registry,
and the Q-ROOT decision.** B6-0 lands the order-6 weighted
selection rule FULL *as corrected*: the scoping's card-4 line was
FALSE under weighted sharing (an explicit N = 4 counterexample,
registered in the registry below), and the disjunctive corrected
statement is the landed one; no sign is asserted for β⁶, and its
general sign stays FRONTIER. BRIDGE-1 opens the Span 1
(Lean ↔ Python) cross-check registry (`whitepaper/
cross-check-registry.md`): every probe ships with the exact Lean
statement it checks and exact rational arithmetic at the verdict
line; simulations audit and probe — the registry asserts nothing
physical. And QR-D1 decides the Q-ROOT post at the owned level:
**NO** — the triad (−1, 0, 2) is not realized as weights by any
of the corpus's three canonical allocation modes, each fenced by
its landed positivity fact (`rootWeights_not_realized`; dossier
`whitepaper/qrd1-landing-2026-10-29.md`). The decision covers the
three owned modes only: Floor 1 (the triad as notation) stands,
Floors 2/3 stay killed, and a future signed allocation object
would enter as a new entry, not a retrofit. And A0 registers the
campaign's central sufficient target as a Lean proposition for
the first time: `LayerKernelPos` — "𝒜 ⪰ 0 on gauge-invariant
observables" in owned vocabulary, with the landed sufficiency
chain (β1 factorization + twirl reduction + Schur product)
assembled in its dossier (`whitepaper/a0-landing-2026-10-29.md`).
Registration only: no proof of 𝒜 ⪰ 0 is attempted there, and
clause (a) of the finite theory remains its last open clause.
B6-1 then lands the β⁶ definitions (`PlaneCrossingBeta6`):
`betaCoeff6`, the order-6 expansion with tail R₇, `kappa6Const`
over the 11 partitions of 6 — machine-audited to total M⁶ at
values-one — `kappa6dep`, and the raw channel expressions for
the (3,1,1,1) and (2,2,1,1) primitive-quad channels; no sign is
asserted for any of it, and the C6 / Θ(2,2,2) channel sums and
the assembly identity are the probe's and B6-2's work (dossier
`whitepaper/b61-landing-2026-10-29.md`). The probe has now run
(B6-PROBE): at both seats every new order-6 channel vanishes
identically on the joint kernel K = ker κ₄^dep — each channel
kernel is an exact positive multiple of the seat's κ₄ kernel —
so the pre-registered kill K-K6 does **not** fire and the
outcome is (ii): the regress continues, the β⁶ decision on K
is vacuous, and nothing general follows (dossier
`whitepaper/b6probe-landing-2026-10-29.md`; cross-check
registry entry BR1-004). B6-2 then closes the β⁶ line's
priced path with the assembly identity in its true form
(`kappa6dep_eq`): the κ₅ dressing factor is exactly
`4 + (M−4)·B` again; the κ₄ coefficient A₄ is *not* a
polynomial in M, B alone (it carries `½·(M−4)·μ₂/d²` from
the doubled-penta fiber); and one extra term survives —
`−d⁻⁶·e₁²·S4theta`, the quad-excess sum over Θ supports'
rectangle 4-subsets, which no corpus counting reduces to a
multiple of κ₄^dep. Both differences are on the module's
face (dossier `whitepaper/b62-landing-2026-10-29.md`); no
sign is asserted, and the β⁶ general sign stays FRONTIER.
This batch also carries BRIDGE-2: the cross-check registry
is now a mandatory item on every probe's landing checklist.
And A2-1 lays Route B's foundation stone: the
single-plaquette factor `exp(−β·wordDensity ρ g)` is a
positive-definite class function at general (G, ρ) for all
β ≥ 0 (`plaquetteFactor_posDef_classFn`) — proved by the
Gram route (the character kernel is a sum of squared entry
norms; the factor is its positive power series, closed by
the Schur product theorem), previously a paper argument
only. One lemma-level kill rides with it at full rank: the
bare product closure for the real-part PD predicate is
FALSE as stated (counterexample: the constant I function);
the closure landed in Hermitian-kernel form, which is what
the factor satisfies (dossier
`whitepaper/a21-landing-2026-10-29.md`). The telescoping
identity (A2-2) is unbuilt; 𝒜 ⪰ 0 is untouched. The
viscous line opens with VISC-0 (`ViscousLine`): a
registration pack assembling the diagonal one-signedness
of the owned heat/ternary step (diagonal multipliers in
(0, 1], generator values ≤ 0) from landed facts — a
formality brick, priced and labeled as such, with the
generator theorem (VISC-1) and the general-Hermitian
transport (VISC-2) to follow (dossier
`whitepaper/visc0-landing-2026-10-29.md`). VISC-1 has now
landed the generator theorem: `ternaryGenerator
lam X = −(ΛX + XΛ)` is the step's derivative at 0 (on
Hermitian inputs; in general applied to Xᴴ), its
matrix-unit spectrum is exactly `−(λᵢ + λⱼ)`, and it is
dissipative at the diagonal seat in trace form (dossier
`whitepaper/visc1-landing-2026-10-29.md`) — the one brick
shared with the parked TTK-2, built under this line only.
VISC-2 transports the whole picture to the
general-Hermitian seat: for Hermitian PSD K the step
`heatKernelGen K t · X · (heatKernelGen K t)ᴴ` has
eigenbasis multipliers `exp(−t(dᵢ + dⱼ)) ∈ (0, 1]`, equal
to 1 exactly on the ground-eigenspace units, with
generator `−(KX + XK)` dissipative in trace form; the PSD
hypothesis is load-bearing and on every statement's face,
and the master kill K-VISC does not fire inside that
scope (dossier `whitepaper/visc2-landing-2026-10-29.md`).
VISC-3 closes the line: the trace defect of a diagonal
state has the closed form `∑ i, w i·(1 − exp(−2t·λᵢ))`,
trapped sharply between its slowest and fastest occupied
modes' defects, both bounds attained — one pack-level
kill rides with it (the rate bound as first prescribed
ran the wrong way at the slowest mode; the counterexample
and the corrected pair are on the dossier's face,
`whitepaper/visc3-landing-2026-10-29.md`). BSD rung 2
opens with B2-0 (`BSDRefinedPin`): the refined-formula
pin for E2 stated in full — seams as named hypotheses
(Sha finiteness under the Gross–Zagier/Kolyvagin region
licence; the Tamagawa value as the study's Tate read-off),
the (c) value Props at their scoped bars, and `sha`
entering as a bound variable whose value the pin will
*derive*, never input. The refined formula is Wiles's
Remark 1, not the official statement: this rung closes
ZERO parts of the BSD statement even in full (dossier
`whitepaper/b20-landing-2026-10-29.md`). B2-1 follows:
the Nagell–Lutz criterion for E2 is refactored into the
board's single shared seam (`NagellLutzCriterionE2`,
sanctioned strength only) with rung 1's infinite-order
hypothesis *derived* from it as its (3, 5)-instance, and
the torsion sweep lands `Nat.card (torsion of E2.Point)
= 1` conditional on that seam — the study's eight
candidate ordinates and the x³ = 2 case excluded by
integer arithmetic (dossier
`whitepaper/b21-landing-2026-10-29.md`). NO CLAIM;
dials 0/4. Route B's telescoping brick is then scoped
and registered (A2-2a, `PlaquetteTelescoping`): the
statement that survives scoping is a revised entry —
the plaquette block (the joint corner-stratum integral
of four column factors around a column-graph plaquette)
factors through the two plaquette holonomies into a
kernel Ψ expected PSD and separately class in each
argument (`PlaqTelescoping` / `PlaqKernelPos`, stated,
unproved). The claim-path memo's literal quotient-form
sentence does not survive scoping; its death is
conditional on the seat probe (A2-2-PROBE, K-A2 armed)
certifying the counterexample, and no proof brick fires
before that probe passes (dossier
`whitepaper/a22a-landing-2026-10-29.md`). The S3-1 wall-identity
gate has also reported (paper): **DP-1 — two distinct
walls**; factorization ⇔ the LOC-3 bridge is one wall,
uniformity is another, and the campaigns do not merge
(dossier `whitepaper/s31-wall-identity-gate-2026-10-29.md`).
B7-0 lands the β⁷ selection rule FULL
(`OrderSevenSelection`): the new order-7 channels are
exactly (4,1,1,1), (3,2,1,1), (2,2,2,1) on primitive
quads, (2,1,1,1,1,1) on C6 and on Θ(2,2,2), and (1⁷) on
the new book support Θ(1,3,3); card 5 dies by erasure
exactly as scoped (distinctly-shared cards at order 7
are {4, 6, 7}), and the card-7 abstract types are
killed by proof, not prediction — no survivor beyond
Θ(1,3,3). No sign is asserted; the β⁷ sign stays
FRONTIER and B7-PROBE is held behind the
Gram-dominance discriminator (dossier
`whitepaper/b70-landing-2026-10-29.md`).

**2026-10-28 — the β⁴ endpoint and the β⁵ assembly.** PW-5 lands
its endpoint: the β⁴ dependent coefficient is nonnegative on the
diagonal for every irreducible ρ at even N ≥ 4
(`kappa4dep_diag_nonneg`) — explicitly NOT 𝒜 ⪰ 0: off-diagonal,
β⁵+, and N = 2 are untouched, and Φ is not bounded away from
zero, so there is no cushion. The β⁵ line then ran its priced
path: selection (B5-0), channel definitions (B5-1, landed
PARTIAL at its pre-named seam), a probe passing at both seats
(B5-PROBE: the κ₅ channel form vanishes exactly on
ker κ₄^dep and is a positive multiple of the κ₄ form — 2× and
4× at the probed seats), and the assembly identity in its true
form (B5-2): κ₅^dep = (4 + (M−4)·B)·κ₄^dep − (d⁻⁵/2)·κ₅^chanExcess
— the naive identity κ₅^dep = channel is FALSE in two named
ways. On the diagonal at irreducible ρ the dressing factor is
exactly M > 0, so the β⁵ sign reduces to one unproved
comparison: whether (d⁻⁵/2)·excess stays under M·κ₄^dep(u,u).
The sign stays FRONTIER (the triple twirls are unowned).
NO CLAIM on any Millennium statement — parts closed: 0;
dials 0/4.

**2026-10-23 — THE FINITE STANDARD MODEL LANDS.** Track 1 (the
gauge algebra) is CLOSED at T1 via Route B: one representation
carries faithfulness, the hypercharge ratios, and the full
spectral-triple compatibilities together, machine-checked
(`ThetLogos.Track1RouteB`; dossier
`whitepaper/track1-routeb-2026-10-23.md`). NO CLAIM on any
Millennium statement — parts of any official Clay statement
closed by this program: 0.

**2026-10-24 — the Gram clause, the third family, brick
F1: the single-plaquette word factorization.** The route
scoped clean this morning (the landed integrated criterion
fits the family verbatim) lands its first brick: the
exponential factor of one crossing plaquette, factored as
a `∑'` over word indices in the criterion's exact
`conj (B) * A` shape (`ThetLogos.LatticeGramWord`). The
factorization is basis-free by construction — an HS inner
product pairs the same entry path on both sides, so no
entry-selection step exists at which the (k, a)/(j, i)
mismatch of the dead factored family could enter — and
its d = 1 control resums to Route C's `fourier_exp_circle`
through the common value, so the family that closed U(1)
is this family's one-dimensional shadow. Entry bounds
enter only through the summability side conditions; the
domination package ships in criterion shape
(`summable_wordCA_mul` discharged) as the named interface
F2 consumes. Neither pre-registered kill fired. F1 asserts
nothing about marginals, Haar integrals, or positivity:
the Damping Lemma is F2's named seat, and Stage 1b-B at
general (G, ρ) remains open until F3 (dossier
`whitepaper/gram-third-family-f1-word-factorization-2026-10-24.md`;
charter `whitepaper/gram-third-family-scoping-2026-10-24.md`).

**2026-10-24 — the Gram clause, the transfer-matrix route.**
With factored and regrouped closures obstructed, the classical
route was scoped against the corpus: most of it was already T1
(the Stage 1b-D transfer package), and its two gaps were fenced
by one missing lemma — the layer factorization of the Gibbs
measure. Step S1 lands the route's first stone: the
**depth-one identification** (`ThetLogos.LatticeTransferID`).
At depth one the identification is a *symmetry* fact, not a
factorization fact: reflection pairs slice 0 with slice N−1,
and one composite symmetry — the axis reflection, reflection
after a one-step time shift — carries that pairing exactly onto
the transfer step's (0, 1) pairing, so the OS form of a slice
observable *equals* the transfer operator's quadratic form, at
general (G, ρ) and every real β, machine-checked. The layer
factorization is not consumed at this depth; it remains the
named question at depths above one (dossier
`whitepaper/gram-transfer-s1-depth-one-identification-2026-10-24.md`;
charter `whitepaper/gram-clause-transfer-matrix-scoping-2026-10-24.md`).
Stage 1b-B at general (G, ρ) remains open.

**2026-10-24 — the STEM bridge, brick B5: the zero-field
weld — the bridge's near bank is complete.** At the trivial
connection `θ ≡ 1`, the magnetic theory of B1–B3 contains
the Bridge exhibit's own theory as its zero-field special
case, end to end (`ThetLogos.BridgeMagneticWeld`). The
operator level cites B1's `magLap_one` and records its
linear and Euclidean forms; the matrix level gives
`magMat w 1` entrywise (row-sum diagonal, bare cast
conductances) and in spectral form
(`magMat_one_eq_conj`: conjugation by the rectangular weld
matrix `weldMat`, whose columns are the exhibit's cast
eigenbasis, onto `diagonal (lapEig)`). The heat level is
the eigenbasis identification, proved three agreeing
ways — on each cast eigenvector (`heatOp`'s own factor
`exp (−t • lapEig k)`), as a solution formula over ℂ, and
as a matrix identity (`magHeat_one_eq_conj`) — and the
trace welds to the exhibit datum at the exhibit's
eigenvalues (`magHeatTrace_one`). The Fiedler value is
the `θ = 1` spectral gap in the corpus's own terms: it
floors every nonzero welded eigenvalue and is attained
as one (`magMat_one_fiedler_floor`,
`magMat_one_fiedler_eigen`). One named seam, kept on the
module's face: the rectangular `weldMat` carries no
`star` in Mathlib — its adjoint is `conjTranspose`
throughout. With B1, B2, B3 and B5 landed, the bridge's
near bank is complete; remaining are B4′
(face-restricted flux-dependence; its landing leaves the
bridge at PARTIAL) and B4 (general flux-dependence —
needs cycle-space machinery the corpus does not yet
hold, a named remainder) (dossier
`whitepaper/stem-bridge-b5-zero-field-weld-2026-10-24.md`).
Finite graph bookkeeping — not Maxwell, not a
unification claim.

**2026-10-24 — the STEM bridge, brick B3: the heat
object.** B1's magnetic Laplacian now has its heat object
(`ThetLogos.BridgeMagneticHeat`): `magMat w θ`, the matrix
of `magLin w θ` in the canonical basis — tied to the
operator by proof (its `*ᵥ` action is `magLap`; its
`Matrix.toLin'` is `magLapFun`), Hermitian under B1's
hypotheses — fed to the corpus's general Hermitian heat
engine in the engine's own packaging:
`magHeat w θ t = heatKernelGen (magMat w θ) t =
exp (−t • L_{w,θ})`, with the semigroup law. The trace is
**proved equal to the datum form** `∑ i, exp (−t • λᵢ)`
over `L_{w,θ}`'s eigenvalues (`magHeatTrace_eq`) — datum,
not forged — and B2's deferred corollary lands with it at
trace level: the heat trace depends only on the gauge class
of `θ` (`magHeatTrace_gauge`, through the entrywise matrix
conjugation `magMat_gauge` and the engine's `exp_conj_star`).
`magMat` is positive semidefinite — its quadratic form is
S1's phased energy — so every `λᵢ ≥ 0`, and for `t ≥ 0` the
heat kernel contracts **at the quadratic-form level**
(`magHeat_contraction`; the operator-norm form is not
asserted — the mark is on the module's face). The
zero-field cheap half stands (at `θ ≡ 1` the matrix's
action is the exhibit's `laplacianOpC`); the full weld to
`BridgeCompletion.heatOp`'s eigenbasis form is brick B5
and is not asserted (dossier
`whitepaper/stem-bridge-b3-heat-object-2026-10-24.md`).
Bricks B4/B4′/B5 remain open. Finite graph bookkeeping —
not Maxwell, not a unification claim.

**2026-10-24 — the STEM bridge, brick B2: gauge
covariance.** B1's magnetic graph Laplacian is
gauge-covariant (`ThetLogos.BridgeMagneticGauge`): for a
vertex gauge transformation `g : V → Circle`, the conjugated
connection is forced to be `θ^g i j = g i · θ i j · (g j)⁻¹`
— the intertwining closes termwise iff `θ^g i j · g j =
g i · θ i j` — and the operator identity
`L_{w,θ^g} = U_g ∘ₗ L_{w,θ} ∘ₗ U_g*` stands
**hypothesis-free**, with `U_g*` proved the adjoint in both
senses the corpus carries. Corollaries: the phased Dirichlet
energy is gauge-invariant, and `μ` is an eigenvalue of
`L_{w,θ^g}` iff it is one of `L_{w,θ}`. The heat-trace half
of the charter's S3 belongs to brick B3 and is not asserted
(dossier
`whitepaper/stem-bridge-b2-gauge-covariance-2026-10-24.md`).
Bricks B3–B5 remain open.

**2026-10-24 — the STEM bridge, brick B1.** The
Spectral–Thermal ElectroMagnetic bridge (charter
`whitepaper/stem-bridge-scoping-2026-10-24.md`) joins the
spectral–thermal bank to the electromagnetic bank through the
heat kernel of a covariant operator; its first brick lands the
operator itself: the **magnetic graph Laplacian** `L_{w,θ}` on
the Bridge exhibit's own graph — the exhibit's conductances
unchanged, a Circle-valued U(1) connection seated in the Ohm
factor, complex potentials (`ThetLogos.BridgeMagnetic`).
Self-adjointness (S1a) and the phased energy identity (S1b)
stand, positivity stands, and at `θ ≡ 1` the operator is the
exhibit's landed `laplacianOp` verbatim (the definitional
weld; the full zero-field weld is brick B5). Finite graph
bookkeeping — not Maxwell, not a unification claim (dossier
`whitepaper/stem-bridge-b1-magnetic-laplacian-2026-10-24.md`).
Bricks B2–B5 remain open.

**2026-10-24 — gap queue Q1: the `posToSlice` marginal
identity.** `LatticeOSSpace` §7 named one unproved loose end
in its own text: the pushforward of the product Haar measure
on the strict positive half under the slice coordinatization
`posToSlice` had never been identified. It now stands
(`ThetLogos.LatticeOSMarginal`): the pushforward is the
product Haar measure on the slice — equivalently, the slice
measure at `β = 0`. A named, priced hole in a landed
module's fence, closed; the transfer route's R1/R3 rungs may
consume it (dossier
`whitepaper/gap-queue-q1-postoslice-2026-10-24.md`).

**2026-10-24 — gap queue Q2: pointwise positivity of
`T_β f`.** Stage 1b-D's dossier fenced a small hole: the
transfer operator's *form* positivity was proved, but
pointwise positivity — positive functions to positive
functions — "is not stated; it follows from the form
positivity by the standard indicator argument." That
argument is now formalized (`ThetLogos.LatticeTransferPointwise`):
a pointwise real nonnegative slice observable transfers to a
vector whose representative is a.e. real and nonnegative, at
every real `β` (dossier
`whitepaper/gap-queue-q2-pointwise-positivity-2026-10-24.md`).
Operator positivity on arbitrary vectors (the half-step
square) remains open.

**2026-10-24 — the Gram clause, transfer-matrix route R1:
the layer factorization.** The one lemma the transfer
route's two remaining gaps shared is landed
(`ThetLogos.LatticeLayerFactor`): in Stage 0's split
coordinatization, the Gibbs measure is `Z⁻¹` times the
product of the two half Gibbs-type measures — both built
from the *same* half-action function `halfActionP`, the
negative half read through the mirror — reweighted by the
layer Boltzmann factor `exp(−S₀)`, the crossing stratum's
weight. Pure finite density algebra on the landed action
split: no disintegration, and no basis expansion of the
Boltzmann weight (charter constraint D5 held; the priced
side door stays shut). The expectation-pairing and
Fubini-iteration forms the next rungs consume ship with it;
gap queue Q1's `posToSlice` was not consumed after all. The
half-step square (R2) and the depth-`N/2` identification
(R3) remain open, and Stage 1b-B at general (G, ρ) remains
open (dossier
`whitepaper/gram-transfer-r1-layer-factorization-2026-10-24.md`).

**2026-10-24 — the Gram clause, Route B (averaging).** Steps T2
(the averaging projection), T3 (word/tensor bookkeeping), T4a and
T4b (feature assembly and its mirror) stand. The word-entry closer
T4c stopped on a **proved obstruction**: a crossing plaquette's
closed-half arc is a stratum · strict · stratum sandwich, whose
monomials are occurrence (tensor) coefficients, not word entries,
so the pointwise Gram identity is false for the word-entry family
(dossier `whitepaper/gram-route-b-t4c-obstruction-2026-10-23.md`).
The repair on occurrence features landed its two halves — T4a′
(A side) and T4b′ (mirror side, sharing one strict-half feature)
(`ThetLogos.GramAssemblyOcc`, `ThetLogos.GramMirrorOcc`) — and the
closer T4c′ then stopped on a **second, deeper proved
obstruction**: the strict factor's two readings differ by the
index-pair swap (k, a) ↔ (j, i), invisible iff d = 1, so no
factored family instantiates the integrated criterion at d ≥ 2
(dossier `whitepaper/gram-route-b-t4cp-obstruction-2026-10-24.md`).
The clause at general (G, ρ) remains open. The regrouped route
was scoped, priced, and tested at its pre-registered R0 gate —
and it died there: symmetrized proportionality is false at the
T4c′ SU(2) instance (wedges 5/8 and −3/8; dossier
`whitepaper/gram-route-b-r0-obstruction-2026-10-24.md`). The
obstruction now covers the factored family and its
reflection-regrouping class; the criterion itself, Route C, and
T4a′/T4b′ stand untouched.

**2026-10-23 — the Gram clause, Route C.** The finite Gram
criterion of Stage 1b-B is proved to have a hypothesis the Wilson
weight cannot satisfy (T0); its replacement — the integrated,
series-form criterion — is proved at general (G, ρ), and
reflection positivity of the U(1) Wilson theory at every β ≥ 0 is
now T1 (`ThetLogos.LatticeGramSeries`; dossier
`whitepaper/gram-route-c-2026-10-23.md`). The clause at general
(G, ρ) remains open: Route B (averaging) is the named next brick.

**7,431 theorem declarations**\*
across 254 counted Lean modules, with whitepaper dossiers for every campaign.

\* *Theorem count and verification scope subject to reproducible build
and proof-dependency audit. Count method (adopted 2026-10-17):
theorem/lemma declarations whose keyword begins a source line at
column 0 (`^(theorem|lemma) ` on comment-stripped source) in the
program's counted modules, each verified by targeted `lake build`;
headline results additionally checked with `#print axioms` (only
`propext`, `Classical.choice`, `Quot.sound`). Sixty-seven declarations
carrying a same-line `@[simp]` attribute are not counted under this
rule — the earlier figure of fifteen was an undercount, corrected by
the full-corpus double-check sweep of 2026-10-18/19, which also
reconciled the counted chain at 116 modules (see
`whitepaper/double-check-sweep-2026-10-18.md`). Under the strict
rule (at the 2026-10-29 census an attribute-inclusive count
reads 7,509); earlier running
totals summed dossier figures made under mixed patterns — the full
reconciliation is printed in Paper v3, §0. A full proof-dependency
audit (2026-10-21/22) then inspected the complete axiom footprint of
every declaration in the counted corpus as it stood at 3,408: exactly
seven declarations depend on `sorryAx` — the seven tier-quarantined
open obligations, each containing its own `sorry`, with no transitive
contamination of any other declaration; a further 9–11 declarations
rest on the corpus's own explicitly stated T2 file axioms; the
remaining 3,390–3,392 carry footprints inside Lean's standard three
axioms alone (report:
`whitepaper/corpus-dependency-audit-2026-10-21.md`).*

## Credit

This program formalizes; it did not originate the ideas, the
problems, or most of the mathematics it verifies. The staircase is
named in [ACKNOWLEDGMENTS.md](ACKNOWLEDGMENTS.md) — Dirac, Connes,
Tomita–Takesaki, Wightman, Osterwalder–Schrader, Wilson, and the
Lean/Mathlib community among them. If this corpus is ever cited,
cite the originators first.

## The paper

**Active Cartesian Modular Dynamics: Machine-Verified Foundations**

- Current version (v4, 2026-10-25): [doi.org/10.5281/zenodo.23648050](https://doi.org/10.5281/zenodo.23648050)
- v3: [doi.org/10.5281/zenodo.23444600](https://doi.org/10.5281/zenodo.23444600)
- v2: [doi.org/10.5281/zenodo.23427964](https://doi.org/10.5281/zenodo.23427964)
- v1: [doi.org/10.5281/zenodo.23408680](https://doi.org/10.5281/zenodo.23408680)
- Author: Jeffrey Michael Gurd, Nexus Research —
  [ORCID 0009-0008-0188-5150](https://orcid.org/0009-0008-0188-5150)
- Paper license: CC BY 4.0. Code license: MIT.

## What stands (all T1 unless noted)

- **Rungs 1–8** — finite spectral triple with three-generation
  inheritance; almost-commutative product geometry; fermionic and
  bosonic Fock spaces with the CAR/CCR algebra proved. (Paper v2.)
- **Rungs 9–10** — second quantization Γ/dΓ for both statistics; the
  free Hamiltonian gap **derived**, not assumed (finite modes).
- **Standard Model match** — 3 MATCH + 1 PARTIAL, caveats *proved*,
  not hidden ([dossier](whitepaper/sm-match-2026-10-11.md)).
- **Pitch 2** — the free theory at **countably many modes**: the gap
  survives the infinite-mode limit, in the
  eigenvalue-on-finite-particle-domain sense
  ([A](whitepaper/pitch-2-campaign-a-2026-10-16.md),
  [B](whitepaper/pitch-2-campaign-b-2026-10-16.md)).
- **Pitch 3** — the program's **first interacting Hamiltonians**.
  Fermionic: complete, gap persistence proved at finite modes
  ([dossier](whitepaper/pitch-3-campaign-1-2026-10-16.md)). Bosonic:
  interaction calculus, exact diagonal gap, windowed persistence —
  with **essential self-adjointness still open and labeled as such**
  ([dossier](whitepaper/pitch-3-campaign-2-2026-10-17.md)).
- **Schrödinger dynamics** — time evolution, unitarity, picture
  equivalence; the interacting gap clusters proved invariant in time
  ([dossier](whitepaper/schrodinger-dynamics-2026-10-17.md)).
- **Rung 7 completion** — the free one-particle mass-shell measure is
  invariant under the **full restricted Lorentz group** (boosts
  discharged 2026-10-17)
  ([dossier](whitepaper/mass-shell-boost-discharge-2026-10-17.md)).
- **Bridge exhibit** — finite graph bridge algebra: L = dᵀσd,
  Kirchhoff's laws, the Fiedler variational bound
  ([dossier](whitepaper/bridge-laplacian-2026-10-17.md)).
- **Pitch 4, Stage 0** — **finite lattice gauge theory STANDS**:
  group-valued links, Wilson action, product-Haar measure, and
  **exact gauge invariance proved for every gauge transformation** —
  the corpus's first quantized gauge sector (finite lattice only;
  reflection positivity is Stage 1b, priced)
  ([dossier](whitepaper/pitch-4-stage-0-2026-10-17.md),
  [scoping](whitepaper/pitch-4-continuum-scoping-DRAFT-2026-10-17.md)).
- **Pitch 4, Stage 1a** — **lattice correlations STAND**: the Gibbs
  measure constructed, covariance and Cauchy–Schwarz proved, and
  **Elitzur's theorem**: gauge-variant insertions have expectation
  zero at every coupling, for a general gauge group
  ([dossier](whitepaper/pitch-4-stage-1a-2026-10-17.md)).
- **Pitch 4, Stage 1b-A** — **reflection structure STANDS**: the
  torus reflection built, its fixed link stratum characterized, the
  Gibbs measure proved reflection-invariant, and the Wilson action
  split S = S₊ + S₋ + S₀ across the reflection
  ([dossier](whitepaper/pitch-4-stage-1b-a-2026-10-17.md)).
- **Pitch 4, Stage 1b-B** — **reflection positivity: STANDS for
  U(1); PARTIAL at general (G, ρ)**: the Osterwalder–Schrader form
  is built in full (conjugate symmetry, sesquilinearity, exact
  kernel factorization) and positivity is **proved at zero
  coupling**. The original finite Gram criterion stands as proved,
  but its hypothesis is now **proved unsatisfiable for the Wilson
  weight** (T0, 2026-10-23); the replacement integrated
  (series-form) Gram criterion is proved at general (G, ρ), and
  the U(1) Wilson theory is **discharged at every β ≥ 0**
  (Route C). The general-group discharge is Route B — averaging
  over the stratum, no Peter–Weyl required: step T2, the
  averaging-projection lemma (the Haar average is the orthogonal
  projection onto the invariant subspace, with its finite Gram
  sum), and step T3, the word/tensor bookkeeping (crossing words
  are coefficients of the joint tensor representation, and the
  joint stratum integral is the averaging operator applied to
  it), **both landed 2026-10-23** (`ThetLogos.AveragingProjection`,
  `ThetLogos.GramWordTensor`); step T4 (assembly) remains
  ([dossier](whitepaper/pitch-4-stage-1b-b-2026-10-17.md),
  [Route C dossier](whitepaper/gram-route-c-2026-10-23.md),
  [Route B step T2 dossier](whitepaper/gram-route-b-t2-averaging-projection-2026-10-23.md),
  [Route B step T3 dossier](whitepaper/gram-route-b-t3-word-tensor-2026-10-23.md)).
- **Pitch 4, Stage 1b-C** — **the OS Hilbert space STANDS**: built
  by the time-slice L² route — the L² space of the Gibbs marginal
  measure on a time slice, at every coupling, with the vacuum vector
  (norm 1), vacuum expectation identified with the Gibbs
  expectation, and bounded slice observables acting as multiplication
  operators with adjoints by conjugation. No appeal to the open
  positivity clause: the clauses that would need it are stated
  conditionally on it, by name
  ([dossier](whitepaper/pitch-4-stage-1b-c-2026-10-17.md)).
- **Pitch 4, Stage 1b-D** — **the transfer matrix STANDS**: the
  one-step transfer operator on the Stage 1b-C space at every
  coupling — a contraction (norm ≤ 1), vacuum-fixing, self-adjoint
  at even extent, nonnegative on nonnegative observables. At zero
  coupling it is *exactly* the vacuum projection, so **the β = 0
  lattice gap is exactly 1**. The general-coupling gap is fenced
  (spectral input priced M–L); nothing in this stage routes
  through Stage 1b-B's open clause
  ([dossier](whitepaper/pitch-4-stage-1b-d-2026-10-17.md)).
- **Yukawa interaction** — **the first mixed fermion–boson
  interaction STANDS**: on the product of the fermionic and bosonic
  finite-mode stacks (made co-importable by the adag repair), a
  Yukawa-shaped coupling (fermion bilinear × boson field) with
  Wick-type calculus, explicit relative bounds, symmetry and
  sectorwise self-adjointness in Pitch 3's scoped senses, and gap
  persistence in windowed form (a band-N threshold with an explicit
  √(N+1) factor; no uniform claim — uniformity is false in
  general). Essential self-adjointness remains fenced as Pitch 3's
  priced remainder
  ([dossier](whitepaper/yukawa-interaction-2026-10-17.md)).

**Foundational results**

- **22-direction classification of the order-one commutant W₂₂** —
  `cf_kernel_classification_46_22`, zero `sorry`s, unconditional: the
  order-one constraint system admits exactly a 22-dimensional real
  solution space (10 SM + 12 exotic directions; the exotic directions
  are explicit non-claims). `lean/ThetLogos/CFKernel22.lean`.
- **Order-zero for all 144 generator pairs** — machine-checked, zero
  `sorry`s. `lean/ThetLogos/MartinettiRep.lean`.

**Background algebra (all T1)** — Weld duality (the boundary pair
algebra: idempotents, trace rigidity, resting-place theorems;
[dossier](whitepaper/weld-duality-2026-10-16.md)) · FluxTwist
(flux-twisted ring spectrum) · TritGrading (ℤ₃ grading) ·
SexagesimalClock (mod-60 CRT grading) · DiffusionDefect (the
finite diffusion law: for the 2D simple random walk, expected squared
displacement from a start (x, y) after t steps is exactly x² + y² + t —
time as the Pythagorean defect, in step units, coefficient pinned as
the walk's normalization;
[dossier](whitepaper/diffusion-defect-2026-10-18.md)) · SpectralClock
(the modular clock's master tick: a state with nondegenerate
`K = −ln ρ` spectrum of width `W` negates its widest coherence first
at exactly `t = π/W`, and at no earlier positive time;
[dossier](whitepaper/spectral-clock-2026-10-18.md)) · ThermalKernel
(the thermal spectral kernel of the modular generator, amortized mode
by mode: the diagonal heat kernel e^{−tK} has the semigroup law, its
trace is the sum of the modes' exponential schedules, each mode's
total payment over all time is exactly 1/λ, and at unit time the
kernel IS the state, e^{−K} = ρ; finite, diagonal case;
[dossier](whitepaper/thermal-kernel-2026-10-18.md)) · WindingRing
(winding numbers on a finite phase ring, as integer bookkeeping:
compound winding is addition in ℤ; a slip — one edge gaining a full
turn of ticks — raises the winding by exactly 1 while leaving every
visible phase unchanged modulo the turn; re-gauging a lift by
anything periodic cannot move it, so winding changes only at slips;
and winding 0 does not imply trivial, by an in-module counterexample;
cabinet tier — not an Abrikosov vortex, no knots, no continuum claim;
[dossier](whitepaper/winding-ring-2026-10-21.md)) · FibonacciReturn
(the golden angle against Fibonacci step counts: after F_{n+2}
golden-angle steps the signed residual from F_n whole turns is
exactly 2πψ^{n+2} — alternating in sign, shrinking geometrically,
tending to 0 — and exact finite return is FALSE for every n, the
kill proved in the same module; one scalar phase, no mass law, the
φ-tower kill untouched;
[dossier](whitepaper/fibonacci-return-2026-10-21.md)) · NoCloning
(qubit gates and the finite no-cloning theorem: any cloning datum
forces every inner product to be 0 or 1, and the pair |0⟩, |+⟩ with
inner product 1/√2 kills every cloning datum on ℂ²; Pauli X/Y/Z and
Hadamard verified unitary with their key actions; a stage theorem —
the composite pairing law is assumed, not derived;
[dossier](whitepaper/no-cloning-2026-10-21.md)) · HermitianReduction
(the general-Hermitian reduction: the shared remainder of the
resonance, clock, and kernel bricks discharged — for a general
Hermitian K, the spectrum, heat-kernel trace schedule, summed
payoff, stationarity, and master tick with firstness transport
along the spectral decomposition, the clock's statements in the
eigenbasis; the non-diagonal e^{−K} = ρ jewel and original-basis
entries are named remainders, not claimed;
[dossier](whitepaper/hermitian-reduction-2026-10-21.md)) ·
ThermalPreCompensation (the thermal instance of the
pre-compensation question: coherences damped by a factor of the
spectral gap; a target is exactly pre-compensable iff its
de-amplified candidate is a density matrix — positivity is the
whole question — and the maximally coherent pair across the
widest gap never is, its negative direction exactly
1 − exp(β · spectralWidth): the width prices the tooth; the
density theorem carries its gap-kernel positivity hypothesis on
its face, and the flow's own cosine factor is unconditional;
[dossier](whitepaper/thermal-pre-compensation-2026-10-21.md)). Theories intake, Round 1:
KMS/Tomita–Takesaki and classical Yang–Mills FIT at the finite level;
continuum claims NO-FIT, on record
([dossier](whitepaper/theories-intake-2026-10-11.md)).

**Exhibit (numerical, not a theorem)** — the
[vacuum portrait](exhibits/vacuum-portrait/EXHIBIT.md): six
portraits sampled from this corpus's own Stage 0/1a U(1) Gibbs
measure on a 6⁴ torus; reproducibility verified by an independent
byte-identical rerun
([shipment note](exhibits/vacuum-portrait/SHIPMENT-2026-10-18.md)).

## Not claimed

- **Not claimed: the continuum limit, interacting 4D QFT, the
  Yang–Mills mass gap.**
- Parts of any official Clay Millennium statement closed by this
  program: **0**. Yang–Mills is the program's horizon, not a result.
- The gap results above are finite-mode / finite-lattice statements in
  the eigenvalue sense stated in their dossiers — scaffolding toward
  the continuum problem, not the continuum problem solved.
- Masses and couplings in the Standard Model match are labeled inputs,
  not predictions.

## Verify it yourself

```bash
cd lean
export PATH="$HOME/.elan/bin:$PATH"
lake build ThetLogos.BridgeLaplacian   # any module, targeted build
```

Headline theorems carry `#print axioms` checks in their dossiers
(standard three axioms only). Tiers: **T1** machine-checked proof ·
**T2** axiomatized input, labeled · **T5** quarantined speculation ·
**KILL** tested and refuted, published as a result · **FRONTIER**
open, obstruction named. Strict rule: Theorem ≠ Simulation ≠
Experiment ≠ Device. (Numerical engines live in `python/` and are
numerical-tier, not proofs.)

## License

MIT — see [LICENSE](LICENSE).

## Support this research

Independent research, no institutional funding. Donations are voluntary
and never a toll — the work is free for everyone, forever:

- **Cash App:** [$Gurd888](https://cash.app/$Gurd888)

— Jeffrey Michael Gurd, Nexus Research
