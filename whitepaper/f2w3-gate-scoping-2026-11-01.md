# Scoping Dossier — F2-W3 GATE: discharging `seatSchurProductStepOpen`

**Date:** 2026-11-01. **Commission:** Jeff's unparking of the F2-W3 gate
for gate-work (2026-11-01 17:11 EST) + the full send; the parent
re-dispatch decision the gate was waiting on is superseded by that
unparking. **Read-only scoping:** every statement below verified on
disk 2026-11-01 in `~/workspace/thet-logos/lean/ThetLogos/` and
`~/workspace/routeb-general-scratch/`; no builds run, no tree edits.

**NO CLAIM on the face.** This dossier proves nothing. Completing
the gate would discharge one registered Prop inside the F2 weld;
completing the weld (W3) would prove an implication between two
open statements (`LayerKernelPos` ⇒ clause (a)). Parts of any
official Millennium statement closed by the gate, by W3, or by
this dossier: **0**. Dials stay **0/4**. FACT is not proved,
`𝒜 ⪰ 0` is not proved, clause (a) is not proved, uniformity is
untouched, continuum proof-distance stays **ZERO**.

---

## Verdict (up front, full rank)

**The gate does NOT price clean as a single brick. The gate stays
visibly gated.** It prices as a **four-brick sub-line,
≈ 120–235 strict plus a non-Lean falsity probe (S)**, with two
named blockers that are not owned anywhere in the corpus or in
the pinned Mathlib:

- **Blocker G-α (API, exact):** the spectral engine's keystone —
  the spectral theorem for a compact self-adjoint operator on an
  infinite-dimensional Hilbert space — **does not exist in the
  pinned Mathlib**. `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`
  carries the diagonalization/spectral theorems for
  **finite-dimensional** spaces only; the compact-operator files
  carry Fredholm alternative, not a spectral expansion. Building
  that theorem is L–XL research-scale analysis, not a weld brick.
  The gate must therefore run on the **compression engine**
  (finite-rank compressions `PₙTPₙ`), which avoids spectral
  theory but whose adapted HS-convergence lemma is also unlanded
  (§4, GATE-3).
- **Blocker G-β (mathematical, exact):** the factor pairings the
  product step consumes are pairings of **dressed** observables
  (twirled `f` times expansion factors). Landed stage-2 material
  gives factor positivity only for **pullbacks of gauge-invariant
  layer observables, in iterated-integral form**. That the dressed
  pairings are confined to exactly the class `LayerKernelPos`
  controls rests on one unproved lemma — **gauge-invariance of
  the fiber-average (conditional expectation onto layer
  coordinates) of a twirled observable dressed by a pulled-back
  factor** (§2.3, GATE-2). If that lemma is false, **K-F2-2 fires**
  and the weld route dies at full rank. Until GATE-2 decides it,
  no honest single price exists for the step behind it.

**What IS clean now:** GATE-0 (interface pin, S) and GATE-1
(the falsity probe, S, non-Lean) are bounded, owned, and
fire-able immediately, in parallel. GATE-2 (M–L) is the decision
brick: its invariance lemma is the gate's true fork. GATE-3/GATE-4
price only conditionally on GATE-2 landing FULL (§4). **F2-W3
does not fire on anything in this dossier**; its own price behind
a cleared gate is reaffirmed at **M (20–45)** (§5).

---

## §1 — The exact statement as landed

### 1.1 The open Prop

`Span3SeatSchur.lean:653-654` (module F2-W2, landed PARTIAL
2026-10-31; dossier `whitepaper/f2w2-landing-2026-10-31.md`):

```lean
def seatSchurProductStepOpen (hN : Even N) (β : ℝ) : Prop :=
  SeatSchurTarget μG ρ hN β
```

Section context (same module, inherited by the def): `G` a group
with measurable / topological-group / Borel / second-countable
structure; `μG : Measure G` with `[IsProbabilityMeasure μG]` and
left/right/inverse Haar invariance; `ρ : G →* ↥(Matrix.unitaryGroup
(Fin d) ℂ)`; `{N : ℕ} [NeZero N]`. The def is a **citation, not a
restatement**: it is definitionally the pin's Prop.

### 1.2 The cited Prop, verbatim-grade

`SeatSchurTarget`, `Span3A0AssemblyPost.lean` (F2-W0 pin):

```lean
def SeatSchurTarget (hN : Even N) (β : ℝ) : Prop :=
  0 ≤ β → LayerKernelPos (N := N) μG ρ β →
  ∀ f : (↥(posLinks (N := N)) → G) → ℂ,
    AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) →
    (∃ C : ℝ, ∀ z, ‖f z‖ ≤ C) →
    0 ≤ (planeAvgPairing μG ρ hN β (posGaugeAvg μG f)
        (mirrorGaugeAvg μG f)).re ∧
    0 ≤ (∫ r : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G),
        (posGaugeAvg μG f) r.1
          * (planeCrossingMarginal μG ρ hN β r.1 r.2
            * (starRingEnd ℂ) ((mirrorGaugeAvg μG f) r.2))
        ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))).re
```

In words, at the weld's actual seats: general `(G, ρ)`, Haar
**probability** measures on every configuration space, `Even N`,
`β ≥ 0`, **assuming** `LayerKernelPos μG ρ β` — for every bounded
a.e.-strongly-measurable strict-half observable `f`, the diagonal
pairing of its twirled representatives (`posGaugeAvg` /
`mirrorGaugeAvg`) is nonnegative, in both registered forms: the
averaged-kernel (`K̄`) form and the pointwise-product form with
`planeCrossingMarginal = A₁ · A₂` in the kernel slot, where
(β1, landed, `PlaneCrossingCube.lean:820`)

- `A₁(z, z') = 𝒜(τ⁺z, τ⁺z')` (`pullTopKernel`),
- `A₂(z, z') = 𝒜(τ₀z', τ₀z)` (`pullBotKernel`, slots swapped).

### 1.3 The hypothesis being consumed — read it narrowly

`LayerKernelPos` (`LayerKernelPos.lean:77`) is positivity of the
`𝒜`-pairing **only on gauge-invariant layer observables**:
`∀ F, GaugeInvariantLayerObs F → 0 ≤ (∬ conj(F u)·𝒜(u,u')·F u').re`.
It asserts nothing about non-gauge-invariant `F`, nothing about
strict-half observables directly, and carries no
measurability/boundedness side conditions of its own. Every
route below is audited against exactly this width — no wider
reading is available, and silently using a wider one is K-F2-2 /
K-F2-3 territory (§3).

---

## §2 — What discharging it requires

### 2.1 The landed conditional discharge — the sufficient shape

W2 stage 3 landed the algebraic core and a conditional discharge
(`Span3SeatSchur.lean`):

- `seatPairing_mul_nonneg_of_finiteRank` — **the finite-rank
  Schur core at the seat (T1, landed):** if `K₂ z z' = Σ i,
  (c i : ℂ) * (a i z * conj (b i z'))` over a `Fintype ι` with
  `c i ≥ 0` real, every dressed factor integrand integrable, and
  every dressed factor pairing `seatPairing K₁ (k₁·a i) (k₂·b i)`
  nonnegative in `.re`, then the product pairing is nonnegative.
- `seatSchurTarget_of_finiteRankProductStep` — **conditional
  discharge (T1, landed):** IF such an expansion exists for the
  concrete `pullBotKernel`, with factor pairings nonnegative and
  factor integrands integrable **in both** the twirled form and
  the half-action-folded form (four hypothesis families:
  `hIntMarg`, `hTermMarg`, `hIntFold`, `hTermFold`), THEN
  `SeatSchurTarget` holds in its exact registered form.

So one sufficient discharge is exactly: **produce the expansion
+ its two nonnegativity families + its two integrability
families, for the concrete bottom pullback, at general `(G, ρ)`.**
Note the landed conditional is **exact-finite**: it consumes an
equality `pullBotKernel = Σ …`, not a limit of expansions. Any
approximating-sequence route (§2.2) additionally needs a
limit-form conditional (GATE-4) — that lemma is **not** landed.

### 2.2 The expansion: what a proof consumes, and the fence

The expansion must be a **Gram factorization of a FACTOR**
(`pullBotKernel`, or symmetrically `pullTopKernel`), never a
Gram factorization of `𝒜` itself:

- A `MemLp` Gram factorization of `𝒜` would, via SHELF-3b's
  landed `posKernel_gram` (`IntegralKernelSchur.lean:503`) plus
  invariance transport, **prove `LayerKernelPos` outright** —
  that is the `𝒜 ⪰ 0` core, single-lane by standing directive,
  and any gate draft that factorizes `𝒜` is **void on sight**
  (K-F2-2 companion, weld memo §4).
- A *series/compression-limit* Gram of the factor does **not**
  back-transport to a `MemLp` Gram of `𝒜`: pulling the factor
  series back along extension sections of `τ₀` gives a series
  for `𝒜` whose Gram family need not be `MemLp` (the HS
  obstruction of §2.4: `Σ λₙ` may diverge even when `Σ λₙ² < ∞`),
  so `posKernel_gram` does not apply to it and the fence is
  intact. **Audit point for every gate landing, stated now:**
  if a produced factor Gram *does* satisfy the `MemLp`
  hypotheses after section pullback, the landing has proved a
  strictly stronger object than the weld assumes and must be
  re-tiered and re-audited as a core result, not shipped as a
  weld brick.

Two engines could produce the factor expansion; their true
state:

**(a) Spectral engine — NOT OWNED (Blocker G-α).** Run the HS
operator `T₂` of `pullBotKernel` on `L²` of strict-half
configurations: compact (`integralKernelOp_isCompactOperator`,
`IntegralKernelHS.lean:1596`, landed) — but self-adjointness of
`T₂` at this seat is **not a landed named lemma** (the corpus
lands symmetry/conjugation for the *marginal*, `PlaneCrossingSymm`,
not for `layerKernel` / its pullbacks), operator positivity of
`T₂` on all of `L²` is **not** available (only the confined
positivity of §2.3), and the infinite-dimensional compact
self-adjoint spectral theorem itself is **absent from the
pinned Mathlib** (finite-dimensional only, §Verdict). Three
unowned layers; the last alone is L–XL. **This engine is not
priced as a gate route.** It is named here so no future pack
quietly assumes it.

**(b) Compression engine — the only priced route.** Take
finite-dimensional subspaces `Vₙ` of the **gauge-invariant**
layer `L²` space, increasing to density in it; compress the
layer operator to `Vₙ`; the compressed kernel is a finite
PSD matrix kernel, whose Gram factorization is finite and
owned (`Matrix.PosSemidef` Gram + `Matrix.PosSemidef.hadamard`
machinery, used at `PlaquetteFactorPD` / `ThermalPreCompensation`);
pull the finite Gram back along `τ₀` to a finite Gram-shaped
expansion of an approximating kernel `A₂ₙ`; pass `n → ∞` in HS
norm. What this consumes that is **landed**: SHELF-3a-ii's HS
stock (`exists_tensor_approx_seq :688`, `kernelTrunc :1979`,
`integralKernel_tsum_norm_sq_eq :3014`,
`integralKernelOp_norm_le :1303`, the HS identity machinery of
`IntegralKernelHS.lean`); stage-1's bound (`layerKernel_norm_le`,
W2: `‖𝒜‖ ≤ Real.exp (|β| * layerBoundConst N)`, hence every
pullback is bounded on a probability space, hence `MemLp 2`,
hence HS — SHELF-3b's L² typecheck obstruction is provably
absent at this seat). What it consumes that is **not landed**:
HS-norm convergence of *these specific compressions* (adapted
to the gauge-invariant subspace and the pullback), as opposed
to the generic tensor approximation sequence — GATE-3's seam.

### 2.3 The factor pairings: the confinement gap (Blocker G-β)

The conditional's `hTerm` families demand
`seatPairing pullTopKernel (twirled f · a i) (twirled f · b i) ≥ 0`
(and the folded analogue) for the expansion's factors `a i, b i`.
Landed stage-2 material gives, **only**:

- `pullTopPairingIter_nonneg` / `pullBotPairingIter_nonneg`
  (W2 stage 2, T1): the pullback pairings in **iterated-integral**
  form are nonnegative for observables of the form `F ∘ τ⁺` /
  `F ∘ τ₀` with `F` a **gauge-invariant layer observable** —
  via `pullTopPairingIter_eq_layerPairing` /
  `pullBotPairingIter_eq_layerPairing` (landed; `integral_comp_emb`
  once per slot).
- `planeAvgPairing_twirled_eq` (W2, from landed
  `planeAvgPairing_averages`): the `K̄` pairing factors through
  the twirls. `planeAvgPairing_eq_seatPairing_marginal_fold`
  (W2): the `K̄` pairing is the marginal pairing of the
  half-action-folded observables.

Between the landed form and the consumed form sit three
precise sub-gaps — **this is the remaining mathematical gap,
stated exactly**:

- **G2a — product ↔ iterated identification.** `seatPairing`
  is a product-measure integral; stage 2's nonnegativity is for
  iterated integrals. At this bounded, probability-measure seat
  the identification is Fubini/Tonelli bookkeeping (bounded
  kernels ⇒ integrable integrands for bounded test functions) —
  expected routine, **not landed** for these pairings.
- **G2b — fiber-average reduction.** For a general bounded
  measurable `g` on strict-half configurations,
  `seatPairing pullTopKernel g g` should equal the `layerPairing`
  of `g`'s **fiber average** (conditional expectation onto the
  `τ⁺`-layer coordinates, integrating out the complementary
  strict-half links against the product probability measure).
  Stage 2 proves this only when `g` is already a pullback
  (fiber average = itself). The general identity is a
  product-measure disintegration — machinery partially owned
  (HS shuffle/section API, `integral_comp_emb`), assembly not
  landed.
- **G2c — gauge-invariance of the dressed fiber average
  (THE fork).** `LayerKernelPos` applies to the fiber average
  only if that average is a **gauge-invariant layer
  observable**. For `g =` twirled `f` this is plausible (twirling
  is gauge-averaging; the marginal's separate invariance is
  landed, `PlaneCrossingSeparate` §2/§5). For `g =` twirled `f`
  **dressed by an expansion factor** it holds only if the
  factors are themselves **pullbacks of layer functions**
  (so the dressing descends to the layer) **and** the two
  embeddings' coordinate sets interact as the product measure
  requires (top and bottom extractions land on disjoint link
  sets — the same disjointness the landed separate-invariance
  glue consumes). This is why GATE-3's expansion is specified
  **on the layer space, pulled back** (§2.2b): spectral
  eigenfunctions on strict-half configurations would NOT
  satisfy the pullback requirement, a second independent
  reason the spectral engine fails this seat even if its
  theorem existed. **G2c is unproved. If it is false, K-F2-2
  fires** (composing the pullbacks requires `𝒜`-positivity
  outside the gauge-invariant class; `LayerKernelPos` as
  registered does not suffice for the weld).

### 2.4 Integrability families — priced routine

`hIntMarg` / `hIntFold`: with `f` bounded, factors `a i, b i`
in `L²` (compressions give finite `L²` combinations), and
`pullTopKernel` uniformly bounded (stage-1 bound pulled back),
each dressed integrand is `L¹` by Cauchy–Schwarz on a
probability space. No new idea; carried inside GATE-4's price.
The genuine HS subtlety sits one level up (§2.2b): a positive
HS operator's square root need not be HS (`Σ λₙ² < ∞` does not
give `Σ λₙ < ∞`), which is exactly SHELF-3b item (3)'s
in-class obstruction, recorded on `IntegralKernelSchur`'s face.
At this seat it does **not** block the compression route
(compressions are finite at every stage; only the limit is
infinite, and pairings are HS-continuous), but it permanently
blocks any route that needs a single `MemLp` Gram family for
the factor — including any attempt to re-run `posKernel_gram`
on the factor.

### 2.5 Landed stock the gate consumes (all T1, verified)

| Stock | Name | Location |
|---|---|---|
| The pin | `SeatSchurTarget` + read-backs | `Span3A0AssemblyPost.lean` |
| Stage 1 bound | `layerKernel_norm_le`, `layerBoundConst`, `layerKernel_eq_ofReal` | `Span3SeatSchur.lean` |
| Stage 2 reduction | `planeCrossingMarginal_eq_pull_mul`, `pullTop/BotPairingIter_eq_layerPairing`, `pullTop/BotPairingIter_nonneg`, `planeAvgPairing_twirled_eq`, `planeAvgPairing_eq_seatPairing_marginal_fold` | `Span3SeatSchur.lean` |
| Finite-rank core | `seatPairing_mul_nonneg_of_finiteRank` | `Span3SeatSchur.lean` |
| Conditional discharge | `seatSchurTarget_of_finiteRankProductStep` | `Span3SeatSchur.lean` |
| Gram positivity (factors only) | `posKernel_gram`, `gramKernel_memLp` | `IntegralKernelSchur.lean:503/:403` |
| Composition positivity | `posKernel_comp_adj`, `integralKernelOp_comp` | `IntegralKernelSchur.lean:1050/:932` |
| HS machinery | `integralKernelOp`, `…_isCompactOperator`, `exists_tensor_approx_seq`, `kernelTrunc`, `integralKernel_tsum_norm_sq_eq` | `IntegralKernelHS.lean` |
| Finite Schur | `Matrix.PosSemidef.hadamard` (+ Gram PSD) | Mathlib; used `PlaquetteFactorPD`, `ThermalPreCompensation` |
| β1 factorization | `planeCrossingMarginal_layerKernel` | `PlaneCrossingCube.lean:820` |
| Twirl / invariance | `planeAvgPairing_averages`, `planeAvgPairing_gauge`, marginal separate invariance | `PlaneCrossingSeparate.lean` |
| Co-import seam | W1 rename landed; both chains co-import (probe passes) | `f2w1-landing-2026-10-31.md` |

**Absent (grep-/source-verified for this dossier):** no landed
limit-form conditional discharge; no landed fiber-average
identity for these pairings; no landed self-adjointness lemma
for `layerKernel` or its pullbacks; no infinite-dimensional
compact self-adjoint spectral theorem in the pinned Mathlib.

---

## §3 — Kills, armed at full rank

Inherited from the weld memo (they bind the gate unchanged):
**K-F2-2** (invariance confinement — §2.3 G2c is its live
trigger), **K-F2-3** (generality creep / vacuity: no abstract
`PosKernel` restatement, no finite-seat landing under the weld
headline), **K-F2-4** (buy inflation: no sentence may describe
gate or weld progress as progress on FACT, `𝒜 ⪰ 0`, clause (a),
or uniformity). K-F2-1 is retired (W1 landed FULL).

New gate kills:

- **K-GATE-1 (falsity of the step at the weld's seats — the
  kill this scoping was asked to price).** If the finite-seat
  probe (GATE-1) produces a finite abstract counterexample —
  finite layer/strict-half sets, finite gauge group acting as
  the corpus's actions do, top/bottom embeddings with the
  corpus's disjointness, a kernel `A` on the layer set positive
  **exactly** on gauge-invariant observables, twirls by group
  averaging — in which the product pairing of a twirled
  observable is **negative**, then: the implication
  "`LayerKernelPos` + formal pullback/twirl structure ⇒ seat
  Schur" is **FALSE**, every route using only those hypotheses
  dies at full rank, and the weld closes **PARTIAL permanently
  at W2's seam** unless and until a NEW entry re-scopes the
  weld under named extra hypotheses drawn from the concrete
  `layerKernel` (its reality `layerKernel_eq_ofReal`, the
  marginal's separate invariance, its exp-of-action form).
  **Scope fence, on the face:** such a counterexample kills the
  *route from `LayerKernelPos` alone*; it does not by itself
  falsify the concrete `SeatSchurTarget`, which could still
  follow from that extra concrete structure. Conversely, no
  counterexample found in the probe's search box is **not**
  evidence of truth — it only retires the cheap kill.
- **K-GATE-2 (spectral smuggling).** Any gate draft that
  cites a spectral expansion for a compact operator on an
  infinite-dimensional space as if it were Mathlib stock is
  void on sight (Blocker G-α); the theorem must be built as
  its own priced brick or not used.
- **K-GATE-3 (exact-finite smuggling).** Any draft that feeds
  an approximating sequence into
  `seatSchurTarget_of_finiteRankProductStep` as if it were the
  exact finite expansion that theorem consumes is void on
  sight; the limit form (GATE-4) is a separate named lemma or
  the step does not land.

---

## §4 — Decomposition into priced bricks

House bands (weld memo): S 5–15 / M 15–45 / L 45–120 strict.
Subdivision discipline: GATE-0 is the interface-first pin with
frozen names; GATE-0 and GATE-1 are independent and parallel;
GATE-2 is the single decision point; GATE-3/GATE-4 are priced
**conditionally** on GATE-2 FULL and re-price at full rank if
GATE-2 lands PARTIAL. At most two concurrent build lanes;
integration only through the parent ceremony.

| Brick | Content | Price | Gate |
|---|---|---|---|
| **F2-GATE-0** — interface pin (new module, working label `Span3SeatSchurGatePost.lean`) | Freeze, verbatim: (i) `SeatFactorApproxExpansion` — the approximating-expansion target for `pullBotKernel`: a sequence of finite Gram-shaped expansions with factors **pulled back from layer functions**, HS-norm convergence to `pullBotKernel`, coefficients ≥ 0; (ii) the fiber-average target Props of GATE-2 (product↔iterated identification; fiber-average identity; dressed fiber-average gauge-invariance) as named Props; (iii) the limit-form conditional stated as a target Prop; (iv) `seatSchurProductStepOpen` cited as the headline; NO CLAIM face + K-F2-2/3/4 + K-GATE-1/2/3 on the face; the §2.2 audit point (factor Gram vs `𝒜` Gram) on the face | **S** (6–12) | none — new entry |
| **F2-GATE-1** — falsity probe (non-Lean; house seat-check style, Python + memo) | Finite abstract seat search for K-GATE-1: small finite layer/strict-half sets, finite gauge actions, top/bot embeddings with disjoint coordinate sets, kernels positive exactly on the invariant class, twirl by averaging; random + structured (rank-structured / sign-pattern) search for a negative product pairing; report either a verified counterexample (recompute its pairings exactly, rationals) or the searched box's bounds | **S** (5–12; 0 strict) | none; parallel with GATE-0 |
| **F2-GATE-2** — fiber-average reduction + confinement decision (new module, working label `Span3SeatSchurGateFiber.lean`) | G2a product↔iterated identification for both pullback seat pairings at the bounded seat; G2b fiber-average identity `seatPairing pullTopKernel g g = layerPairing (fiberAvgTop g)` (and bot analogue); G2c the decision lemma: fiber average of a twirled observable dressed by a **pulled-back layer factor** is a gauge-invariant layer observable | **M–L** (35–70) | GATE-0 |
| **F2-GATE-3** — compression expansion (same or companion module) | Finite-rank PSD compressions of the layer operator on an increasing sequence of finite subspaces of the gauge-invariant layer `L²` space; finite Gram via `Matrix.PosSemidef` machinery; pullback along `τ₀` to approximating expansions of `pullBotKernel`; **HS-norm convergence** of the pulled-back expansions (the seam: generic tensor approximation is landed, this adapted convergence is not) | **L** (50–110) | GATE-2 FULL |
| **F2-GATE-4** — limit discharge + headline (gate module) | Limit-form conditional `seatSchurTarget_of_approxProductStep` (HS-continuity of the seat pairings in the kernel; nonnegativity is closed under the limit); integrability families (§2.4); assembly of GATE-2 + GATE-3 into the headline theorem discharging `seatSchurProductStepOpen` in its exact cited form | **M** (25–45) | GATE-3 |

**Total: ≈ 116–237 strict (≈ 120–235) + the S probe** — versus
W2's original M–L (40–90) estimate for the whole seat Schur,
whose bound + reduction stages landed inside that band and
whose product step is what remains. The gate alone is roughly
**2–3× the original W2 estimate**; that is the honest re-price,
stated at full rank, not a softening of the statement.

**Pre-named PARTIAL seams.**

- **GATE-2 seam (the fork):** G2a + G2b land but G2c fails or
  stalls — GATE-2 lands PARTIAL with the identities in and the
  invariance lemma named OPEN, **K-F2-2 is then the live
  question, not a fired kill** (a stall is not a
  counterexample); GATE-3 does not fire; the parent re-prices
  or commissions GATE-1-style analysis aimed at G2c itself.
  If G2c is **disproved** (a dressed fiber average that is
  provably not gauge-invariant, with a pairing witness), that
  is K-F2-2 **firing**: report at full rank, weld route dead,
  sequel only as a NEW entry under a strengthened hypothesis.
- **GATE-3 seam:** compressions built and finite Grams landed,
  HS convergence of the pulled-back sequence stalls — GATE-3
  PARTIAL, GATE-4 does not fire; a stall and a re-price, never
  a retreat to finite `G` or finite seats (K-F2-3).
- **GATE-4 seam:** limit-form conditional lands but an
  integrability family resists at the folded form only —
  PARTIAL with the marginal form of `SeatSchurTarget`
  discharged and the `K̄` form named open is **not** an
  available landing: `SeatSchurTarget` is a conjunction and
  `seatSchurProductStepOpen` is discharged whole or not at all.

### Pack-ready statement list (frozen for GATE-0; working labels — parent freezes final names at landing, per house rule)

New module `Span3SeatSchurGatePost.lean` (pin), then
`Span3SeatSchurGate.lean` / `Span3SeatSchurGateFiber.lean`:

1. `SeatFactorApproxExpansion (hN : Even N) (β : ℝ) : Prop` —
   ∃ approximating sequence: finite types `ι n`, `c : ι n → ℝ`,
   `0 ≤ c i`, layer functions `φ : ι n → (LayerLink N → G) → ℂ`,
   factors on strict-half configurations `a n i = φ n i ∘ tauBot hN`,
   with the HS norm of `(pullBotKernel − Σ i, c i • (a i ⊗ conj (a i)))`
   (as `MemLp 2` kernels on the product probability space) → 0.
2. `seatPairing_pullTop_eq_pullTopPairingIter` — product-integral
   `seatPairing` of `pullTopKernel` equals its iterated form for
   bounded measurable observables (bot analogue:
   `seatPairing_pullBot_eq_pullBotPairingIter`).
3. `seatPairing_pullTop_eq_layerPairing_fiberAvg` — for bounded
   measurable `g`, the pullTop seat pairing is the `layerPairing`
   of `fiberAvgTop g` (fiber average over the complementary
   strict-half links); bot analogue likewise.
4. `fiberAvgTop_gaugeInvariant_of_twirled_mul_pullback` —
   **the G2c decision lemma:** for bounded measurable `f` and
   layer function `φ`, the fiber average of
   `(posGaugeAvg f) · (φ ∘ tauBot)` (with the mirror/twirled
   variant stated alongside) is a `GaugeInvariantLayerObs`.
5. `pullBotKernel_seatFactorApproxExpansion (hN : Even N) (β : ℝ)
   (hβ : 0 ≤ β) (hLKP : LayerKernelPos μG ρ β) :
   SeatFactorApproxExpansion μG ρ hN β` — GATE-3 headline.
6. `seatSchurTarget_of_approxProductStep` — the limit-form
   conditional: `SeatFactorApproxExpansion` + GATE-2's factor
   pairing nonnegativity ⇒ `SeatSchurTarget μG ρ hN β`.
7. `seatSchurProductStepOpen_discharge (hN : Even N) (β : ℝ) :
   seatSchurProductStepOpen μG ρ hN β` — GATE-4 headline, type
   exactly the landed open Prop (hence, by its def,
   `SeatSchurTarget μG ρ hN β` in the pin's registered form).

---

## §5 — W3 behind the gate

**What W3 is** (weld memo §5, unchanged): the assembly, new
module working label `Span3A0Assembly.lean` — the first module
to hold both chains in one environment (possible since W1).
Chain: gate discharge (`SeatSchurTarget`) → `K̄`-pairing
positivity on the twirled class (W2's
`planeAvgPairing_eq_seatPairing_marginal_fold` + the pin's
read-backs) → `osForm` diagonal positivity on strict-half
observables via landed `osForm_eq_planeAvgKernel`
(`PlaneAvgKernel.lean:1251`; `Z > 0` is the corpus's standing
partition positivity) → `SliceHPosOne` for all `MemLp`
slice observables (bounded ⇒ `MemLp` density step on the
finite `sliceMeasure` space + slice-measure normalization
bookkeeping) → clause (a) via landed transport
`inner_transferOp_self_re_nonneg_of_sliceHPosOne`
(`LatticeSliceDescent.lean:132`).

**The exact statements W3 lands:**

```lean
theorem layerKernelPos_implies_sliceHPosOne_proved
    (hN : Even N) (hN2 : 2 ≤ N) (hρcont : Continuous fun g => repMatrix ρ g)
    (β : ℝ) (hβ : 0 ≤ β)
    (hLKP : LayerKernelPos (N := N) μG ρ β) :
    SliceHPosOne μG ρ hN2 hρcont β

theorem a0AssemblyTarget_proved (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d) :
    A0AssemblyTarget (N := N) μG ρ hN2 hρcont hd
```

i.e. the headline is a theorem **whose type is exactly**
`A0AssemblyTarget` as registered in `Span3FactLayerKernelPos.lean:296`:
`Even N → (∀ β ≥ 0, LayerKernelPos μG ρ β) → ∀ β ≥ 0,
TransferFormClauseA μG ρ β hN2 hρcont`, where
`TransferFormClauseA` is `∀ f : osSpace, 0 ≤ (inner ℂ f
(transferOp … f)).re`. The first theorem is the direct form of
W0's parameterized pin `layerKernelPos_implies_sliceHPosOne`
instantiated at `SlicePos := SliceHPosOne` — formable only
post-W1, as the pin's face states.

**Price: M (20–45 strict) — reaffirmed** from the weld memo,
conditional on the gate clearing FULL. **W3 seam (pre-named,
unchanged):** the bounded ⇒ `MemLp` passage for `SliceHPosOne`'s
quantifier and the `sliceMeasure` normalization; if it resists,
W3 lands PARTIAL with `SliceHPosOne` proved on the bounded
class named as such and the `A0AssemblyTarget` headline does
**not** land. W3 contains no new positivity mathematics; if
assembly uncovers a missing positivity step, that is a
re-price at full rank, not an in-flight expansion of W3.

---

## §6 — Bottom line for the parent

1. **Gate verdict: BLOCKED as a single brick; stays visibly
   gated.** Blockers: G-α (no infinite-dimensional compact
   self-adjoint spectral theorem in the pinned Mathlib — the
   spectral engine is unowned at three layers) and G-β (the
   dressed factor pairings' confinement to `LayerKernelPos`'s
   class rests on the unproved fiber-average invariance lemma
   G2c, whose failure is K-F2-2 firing).
2. **The priced sub-line:** GATE-0 (S, 6–12) + GATE-1 (S, 5–12,
   non-Lean falsity probe) fire clean now, in parallel.
   GATE-2 (M–L, 35–70) is the decision brick. GATE-3 (L,
   50–110) and GATE-4 (M, 25–45) are conditionally priced
   behind GATE-2 FULL. Total ≈ 120–235 strict + probe.
3. **F2-W3 does not fire** on this dossier, on a GATE-2
   PARTIAL, or on a GATE-3 PARTIAL. Behind a FULL gate it is
   **M (20–45)** and lands `A0AssemblyTarget` as a theorem
   (§5, exact statements above).
4. **What even a full gate + W3 buys, fenced (K-F2-4):** a
   machine link between two open statements at fixed `(β, N)`.
   FACT, `LayerKernelPos`, clause (a), and uniformity remain
   open; dials 0/4; continuum distance zero — before and after.

*End of dossier. Scoping only; no Lean built, no tree edited,
nothing committed.*
