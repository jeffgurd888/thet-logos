# THE STEM BRIDGE — SCOPING CHARTER

*Spectral–Thermal ElectroMagnetic bridge: the heat kernel of a covariant
operator, scoped for the finite corpus.*

Prepared 2026-10-24, at Jeff's commission ("we need to get that STEM bridge
Formalization" → "Spectral-thermal Electromagnetic bridge").
Status: **NO CLAIM.** This document scopes a bridge; it builds no span and
proves no theorem. Parts of any official Clay statement closed by anything
in this document: **0**. Form follows the Bridge Landing Pad
(`bridge-landing-pad-2026-10-20.md`): fixed ground, landing criteria,
verdict classes, priced spans. Every corpus citation below was verified
against the files by grep/read on 2026-10-24; where a seat is empty, the
charter says EMPTY rather than gesturing.

---

## 1. The pinned object

There is exactly one classical object that is honestly spectral, thermal,
and electromagnetic at once: **the heat kernel of a covariant operator**.
Take an operator built from a U(1) connection `A` — the electromagnetic
data. Its eigenvalues are spectral data. The semigroup `e^{−t·(operator)}`
and its trace `Tr e^{−t·(operator)}` are the thermal object (the heat
kernel / partition schedule). One operator, three banks: the connection is
the far bank, the spectrum and the heat trace are the near bank, and the
operator itself is the span.

**The finite seat (Seat 1, primary).** In the corpus's finite world the
candidate operator is the **magnetic graph Laplacian** on the Bridge
exhibit's own graph. The data:

- a finite vertex type `V` (`Fintype`, `DecidableEq` — the exhibit's own
  stage);
- conductances `w : V → V → ℝ`, symmetric — the Bridge exhibit's `σ`,
  unchanged;
- a **U(1) connection** `θ : V → V → Circle` with `θ j i = (θ i j)⁻¹`
  (the reverse edge carries the conjugate phase — a discrete connection:
  edge holonomies, with cycle holonomy the product around a closed path);
- complex potentials `F : V → ℂ`.

The operator, extending `BridgeLaplacian.laplacianOp`:

    (L_{w,θ} F) i = ∑ j, w i j • (F i − θ i j • F j)

At `θ ≡ 1` this is definitionally the landed plain Laplacian read over
`ℂ`. The corpus today has **no such definition** (grep: no magnetic /
covariant graph Laplacian anywhere in `lean/ThetLogos/`). Seat 1's
joining object is EMPTY; §3 inventories what each bank already holds.

**Seat 2 (named, not commissioned).** The Pitch-4 lattice corpus carries
genuine U(1) link data and a genuine thermal weight (the Gibbs measure),
but its dynamical operator is the transfer operator of Stage 1b-D, not a
covariant Laplacian, and no heat kernel of a link-carrying operator is
built there. Seat 2 is a different bridge; it is recorded here so nobody
conflates it with Seat 1, and it is **not** priced in this charter.

## 2. What a LANDED STEM bridge would assert

Five typed finite statements. Each is labeled with the bank pieces it
consumes; tiers are the tier the statement would carry *if proved in the
corpus*, not the tier of any current fragment.

- **S1 — Self-adjointness and dissipation (T1 target).** `L_{w,θ}`, as a
  linear operator on `EuclideanSpace ℂ V`, is self-adjoint, and its
  energy identity holds with phases:
  `⟨F, L_{w,θ} F⟩ = ∑ i j, w i j • |F i − θ i j • F j|²`-form, hence
  `0 ≤ ⟨F, L_{w,θ} F⟩` for `0 ≤ w`. *Needs:* Bridge exhibit's three maps
  (`dropVec` / `ohm` / `diverge`) ported to `ℂ` with the connection in
  the Ohm factor; the symmetrization pattern of `bilin_identity`.
- **S2 — The heat object (T1 target).** The semigroup `e^{−t L_{w,θ}}`
  exists (eigenbasis or matrix-exponential form), satisfies the
  semigroup law and the trace identity
  `Tr e^{−t L_{w,θ}} = ∑ k, exp (−t • λ_k(θ))`,
  and is a contraction for `t ≥ 0` (`λ_k(θ) ≥ 0` by S1). *Needs:* S1;
  `HermitianReduction.heatKernelGen` machinery (general Hermitian
  generator over `ℂ`: `heatKernelGen_add`, `heatKernelGen_trace`) or the
  eigenbasis pattern of `BridgeCompletion.heatOp`.
- **S3 — Gauge covariance (T1 target).** For a vertex gauge transformation
  `g : V → Circle`, with `θ^g` the conjugated connection and `U_g` the
  diagonal unitary `(U_g F) i = g i • F i`:
  `L_{w,θ^g} = U_g ∘L L_{w,θ} ∘L U_g*`. Hence the spectrum of `L_{w,θ}`
  and the heat trace of S2 depend only on the gauge class of `θ`.
  *Needs:* S1–S2; the diagonal-unitary conjugation pattern already
  landed at `FluxTwist.gaugeMatrix` / `twistedShift_mul_gaugeMatrix`
  (ring case) and the trace-cyclicity pattern of
  `ModularFlux.modularFlux_gaugeCovariant`.
- **S4 — Flux-dependence (T1 target).** The gauge class of `θ` — hence,
  by S3, the spectrum and heat trace — is determined by the cycle
  holonomies of `θ`: the products of `θ` around a basis of independent
  cycles (equivalently, fluxes through faces where face data is given).
  *Needs:* cycle-space / spanning-tree gauge-fixing machinery the corpus
  does **not** currently hold (see §3); the ring case is landed at
  `FluxTwist` and the face bookkeeping at `BridgeCompletion` §9, but
  neither is the general statement.
- **S5 — Zero-field weld (T1 target).** At `θ ≡ 1`, `L_{w,θ}` is the
  complex embedding of `BridgeLaplacian.laplacianOp` / `lapLin w`; its
  eigenvalues are `BridgeCompletion.lapEig`; its heat operator is
  `heatOp` read over `ℂ`; the Fiedler value is the `θ = 1` spectral gap.
  *Needs:* S1–S3 and the landed Bridge exhibit, unchanged.

A bridge is LANDED when S1–S5 stand at T1 in one module chain. Anything
less is reported at its partial verdict, by name.

## 3. Inventory — the two banks against the ledger

### Near bank: spectral–thermal (spectra + heat)

| Piece | Seat | Verdict |
|---|---|---|
| `ThermalKernel.heatKernel` (diagonal `exp (−tλ)`), `heatKernel_add` (semigroup law), `heatKernel_trace`, `heatKernel_trace_zero` | `ThermalKernel.lean` | **LANDED-T1** — but diagonal only: the spectrum is *given*, no operator is heated. |
| `HermitianReduction.heatKernelGen` (`NormedSpace.exp (−tK)`, general Hermitian `K` over `ℂ`), `heatKernelGen_add`, `heatKernelGen_trace` (= eigenvalue sum, via `heatKernelGen_eq_conj`) | `HermitianReduction.lean` §HeatKernel | **LANDED-T1** — the general-operator heat kernel at matrix level. The thermal engine S2 needs already exists. |
| `BridgeCompletion.heatOp` (eigenbasis heat semigroup of the graph Laplacian), `heatOp_zero`, `heatFlow_hasDerivAt` (`Ḟ = −L F`), `heatFlow_decay` (Fiedler rate) | `BridgeCompletion.lean` §§7–8 | **LANDED-T1** — a graph heat flow, but real weights and **zero field only**: no connection enters. |
| `DiffusionDefect` walk second moment `E‖·‖² = x² + y² + n` | `DiffusionDefect.lean` | **LANDED-T1** — thermal-adjacent bank furniture (a walk, not an operator heat kernel); not a seat of this bridge. |
| Continuum heat-kernel / Seeley–DeWitt expansion | `SpectralAction.lean`: `axiom heatKernelExpansion : True`, `axiom seely_dewitt_a0 : True`, `axiom seely_dewitt_a4 : True` | **EMPTY of content** — T5 scaffolding placeholders whose statements are literally `True`. No proved continuum heat expansion exists in the corpus, and these axioms may never be cited as one. |
| Heat trace of any *graph* operator | — | **EMPTY** — `heatOp` has no trace theorem; the weld would come from `heatKernelGen_trace` once S1 is in hand. |

### Far bank: electromagnetic (U(1) connection / field data)

| Piece | Seat | Verdict |
|---|---|---|
| The three maps `dropVec` (coboundary `d`), `ohm` (`σ` as pointwise factor), `diverge` (`dᵀ`); `laplacianOp_eq_diverge_ohm_drop` (`L = dᵀσd`); Kirchhoff voltage (`dropVec_telescope`, `dropVec_telescope_closed`) and current (`sum_laplacianOp_eq_zero`) laws; `energy_nonneg`; `fiedler` + `fiedler_nonneg` | `BridgeLaplacian.lean` | **LANDED-T1** — the exhibit itself. But: `w` is a real conductance. **No phase, no holonomy, no connection anywhere in the exhibit.** The EM seat *inside* the Bridge exhibit is EMPTY. |
| Graph faces + flux bookkeeping: `GraphFace`, `circulation`, `faceFluxOf`, `circulation_eq_zero` (the graph's `d² = 0`), `inducedEMF`, `faraday_package` | `BridgeCompletion.lean` §9 | **LANDED-T1 as bookkeeping** — an `ℝ`-valued flux per face and an EMF definition-theorem pair. Header-fenced by its own module: graph-Faraday, **not Maxwell theory**, no coupled induced-field dynamics. Flux data exists; it is not a U(1) connection. |
| The flux ring: `twistedShift` / `uniformShift` (unitary), `twistedShift_add_two_pi` (2π-periodicity in flux), `gaugeMatrix` + `twistedShift_mul_gaugeMatrix` (gauge redistribution), `hopping` (hopping Hamiltonian), `hopping_isHermitian`, `hopping_mulVec_twistedFourierVec` (eigenvalues `−cos ((θ + 2πm)/(n+1))` — the ring's spectrum reads the flux) | `FluxTwist.lean` | **LANDED-T1** — the one place in the corpus where a covariant operator's spectrum provably hears a flux: a magnetic Laplacian on the **cycle graph**, in hopping form. The general-graph version is EMPTY. Its own header fences it: not Maxwell, not a continuum Aharonov–Bohm theorem. |
| Lattice gauge data: `Config` / `Link`, `gaugeAction` (+ group laws), `plaquette` + `plaquette_gauge`, `wilsonAction` + `wilsonAction_gauge_invariant`, `loopProd` / `wilsonLoop` + `wilsonLoop_gauge_invariant`, Haar / Gibbs machinery (`configMeasure`, `gibbsExpect`) | `LatticeGauge.lean` (Pitch 4) | **LANDED-T1** — genuine EM data for a general compact group `G`; the U(1) instance is `Circle` (`LatticeGramSeries.repMatrix_circleRep`, `plaquetteDensity_circleRep`), with U(1) reflection positivity T1 at `LatticeGramSeries.osForm_circle_nonneg`. Thermal weight present (Gibbs); **no operator on a space of potentials is built from the links** — Seat 2, §1. |
| Finite-algebra connection: inner fluctuations `A`, represented curvature, `repCurvature_gauge_covariant` | `ClassicalYangMills.lean`, `InnerFluctuations.lean` | **LANDED-T1** — the spectral-triple seat of "connection", on the finite algebra (6-dim caveat carried by its own header). Its thermal companion is next row — and it is a kill. |
| Thermal state of the fluctuated Dirac: `ModularFlux.magnetophaseModularH` (`K_A = β • D_A²`, T2 def); **`magnetophaseFlux_vanishes`** | `ModularFlux.lean` | **KILLED at T1** — the modular flux of a state built from `D_A²` vanishes identically (`K_A` commutes with `D_A`). The "magnetophase as flux" concept is dead in the record; what survives is the entropy `S(ρ_{β,A})` as a magnetic imprint at **T4** (numerical, unformalized). This bridge does not route around the kill: its thermal object is a heat semigroup / heat trace (S2), never a modular flux. |

### The joining seats

- **Magnetic Laplacian on a general finite graph: EMPTY.** No definition,
  no complex potentials on the Bridge graph (the exhibit is `ℝ`
  throughout), no gauge action on graph connections.
- **Heat trace of a covariant operator on a graph: EMPTY** (would be
  S2∘S1).
- **Spectrum-sees-only-holonomies on a general graph: EMPTY** (would be
  S4). Ring case landed (`FluxTwist`); face bookkeeping landed
  (`BridgeCompletion` §9); the general theorem and its cycle-space
  machinery do not exist. (The corpus's only "cohomology" is
  `BRSTFinite`'s BRST/Lie-algebra cohomology — a different animal, not a
  graph cycle space.)
- **Continuum Maxwell equations: NO SEAT** — stated by the Bridge
  exhibits' own headers and by the Landing Pad's ground rules. Nothing
  in this charter changes that.

## 4. Landing criteria and verdict classes

Per the Pad, an incoming statement touches down only with all five:
**L1** typed statement (every symbol seated or declared an import);
**L2** derivation from the ground or an explicit import label — analogy
is not derivation; **L3** tier stated on the paperwork; **L4** a kill
condition named in advance; **L5** public form = machine-checkable form.

Bridge-specific admission rules, added for this span:

- **A1 — Name the connection.** Every statement must exhibit its
  connection data and its gauge action. A claim about "the field" with
  no `θ` and no gauge action is a flyover.
- **A2 — Check the weld.** Every general statement must state its
  `θ ≡ 1` specialization and that specialization must match the landed
  Bridge exhibit verbatim. No silent generalization past the exhibit.
- **A3 — Name the operator.** "The spectrum" means the eigenvalues of a
  named operator on a named space. Spectrum-talk without an operator
  does not land.

Verdict classes (the Pad's six): **LANDED-T1**, **LANDED-T2**, **PARTIAL**
(with the remainder named in the entry), **FLYOVER** (T5, uncounted),
**NO SEAT**, **KILLED**.

## 5. Fences — on the face

- **The EM-torsion bridge paste is KILLED and stays killed.** The
  corpus's torsion material (`DiracTorsionMap.lean`) is finite block
  bookkeeping whose own header states it carries no connection; nothing
  in this bridge is a torsion claim, and the killed paste returns only
  as a new entry by proof, per the house relabeling rule — not via this
  charter.
- **"Strong nuclear = electromagnetic" is KILLED and stays killed.**
  This bridge joins two banks of finite mathematics — spectral-thermal
  operator theory and U(1) gauge data on finite graphs. It is **not** a
  force-unification claim, asserts no identity between interactions,
  and its U(1) is the abelian toy seat, not electromagnetism itself.
- **The magnetophase flux is KILLED at T1**
  (`ModularFlux.magnetophaseFlux_vanishes`). Not revived, not routed
  around; see §3.
- **Continuum Maxwell theory has NO SEAT** in the finite corpus. What
  can land is the finite covariant-heat package of §2 — nothing more is
  claimed, priced, or gestured at.
- **NO CLAIM.** Parts of any official Clay statement closed: **0**. The
  Pitch-4 U(1) material in the inventory is finite-volume abelian
  lattice gauge theory; citing this bridge toward Yang–Mills existence
  or the mass gap is forbidden by the Concrete.

## 6. The brick ladder — priced, each with its kill condition

- **B1 — The magnetic Laplacian (M).** Definition `magLap w θ` on
  `V → ℂ` (connection in the Ohm factor), the linear-operator form on
  `EuclideanSpace ℂ V`, self-adjointness, the phased energy identity,
  positivity for `0 ≤ w`. *Templates:* `BridgeCompletion` §§1, 5 (the
  real proofs), ported to `ℂ`. **Kill condition:** the polarized
  identity fails to close under the corpus's symmetrization pattern, or
  self-adjointness needs hypotheses that exclude `θ ≡ 1` — then the
  definition is wrong, the obstruction is reported at full precision,
  and B1 is re-scoped in the open rather than weakened in silence.
- **B2 — Gauge covariance (S–M).** The gauge action on connections, the
  diagonal unitary `U_g`, the conjugation theorem of S3, and the
  spectrum corollary. *Templates:* `FluxTwist.gaugeMatrix` machinery,
  `ModularFlux` trace cyclicity. **Kill condition:** the intertwining
  `L_{w,θ^g} = U_g L_{w,θ} U_g*` fails for the B1 definition — a
  definition error, caught here, fixed in B1's terms or the brick dies.
- **B3 — The heat object (M).** `e^{−t L_{w,θ}}` via
  `HermitianReduction.heatKernelGen` (or the eigenbasis port of
  `heatOp`): semigroup law, the trace identity of S2, contraction for
  `t ≥ 0`. **Kill condition:** a genuine Mathlib gap in the
  complex-spectral path forces a detour larger than the brick — then
  B3 is re-priced in the open; it is never shrunk silently.
- **B4 — Flux-dependence (L).** S4 in full: gauge classes of `θ` are
  determined by cycle holonomies (spanning-tree gauge fixing; the
  spectrum and heat trace factor through the fluxes). This brick
  secretly needs graph cycle-space machinery the corpus lacks — priced
  L for exactly that reason, and it is the ladder's honest long pole.
  **Kill condition:** gauge fixing on a general finite graph cannot be
  carried in the corpus's explicit finite form — then B4 falls to its
  pre-named restriction and the restriction is recorded, not hidden.
  - **B4′ — Face-restricted flux-dependence (S, fallback named in
    advance).** S4 restricted to graphs equipped with the face data of
    `BridgeCompletion` §9: the gauge class is read from the face
    holonomies (products of `θ` around `GraphFace` boundaries). Landing
    B4′ alone leaves the bridge at **PARTIAL**, with B4 named as the
    remainder.
- **B5 — The zero-field weld (S).** S5: at `θ ≡ 1`, `magLap` is the
  complex `laplacianOp` / `lapLin`, eigenvalues `lapEig`, heat content
  `heatOp` over `ℂ`, Fiedler value as the zero-field gap. **Kill
  condition:** a normalization mismatch (a stray factor, a sign) that
  cannot be absorbed by B1's definitions — then the weld fails loudly
  and B1 is revisited; the exhibit is never edited to meet the bridge.

Clean run: M + (S–M) + M + L + S. With B4′ in place of B4: the bridge
stands **PARTIAL** at M + (S–M) + M + S + S, remainder named.

**Not in the ladder:** Seat 2 (the Pitch-4 lattice joining statement)
and anything continuum. Either requires its own charter and Jeff's word.

## 7. What the bridge would and would not establish

**Would establish** (if the ladder lands): a finite, machine-checked
covariant-heat package — one operator on a finite graph carrying a U(1)
connection, whose spectrum and heat trace are gauge-invariant and
determined by fluxes, specializing at zero field to the landed Bridge
exhibit. Bookkeeping-grade mathematics about finite graphs and
operators, at T1. In physical language it is the Aharonov–Bohm shadow —
*spectrum hears flux* — promoted from the ring (`FluxTwist`, landed) to
general finite graphs. That is a real theorem shape, and it is all it is.

**Would not establish:** Maxwell's equations; any continuum statement;
any unification of forces; any torsion content; any part of any Clay
statement; anything about real circuits, real materials, or real
magnetic fields (the Bridge exhibits' readings remain equation
identities, not claims about the world). T5 readings of the bridge —
including the ontological wiring in `FluxTwist`'s provenance — stay
Jeff's, labeled T5, and are not consequences of B1–B5.

## 8. The standing rule

The pad does not move, and neither does the exhibit: if a span cannot
land, the ledger says so at the same speed as a landing, and the bridge
gets built toward the banks one proved brick at a time. Commissioning
B1 is Jeff's word; this charter commissions nothing by itself.

— BONES, for the record. Tiers per the Concrete; NO CLAIM on the face;
kills at full rank, including this bridge's own if it earns one.
