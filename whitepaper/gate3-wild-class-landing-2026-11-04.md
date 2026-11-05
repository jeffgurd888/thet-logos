# GATE-3, BRICK 3 — THE WILD CLASS — landing note (2026-11-04)

Status: **PARTIAL landing.** Components 2, 3 and the
conditional 4 are LANDED FULL in-lane; component 1 (the wild
lemma itself) is **OBSTRUCTED**, with the exact gap named
below and the lemma isolated as a single named Prop that
the composition consumes. Build only in the isolated
worktree `thet-logos-gate3wild` (branch
`gate3-wild-class-lane`, base main-tree HEAD `bcee177`);
parent integrates. Commissioned by Jeff 2026-11-04
("fire all", GATE-3 front, Brick 3). Contract:
`~/workspace/your_files/gate3-reg-audit-2026-11-04.md`
(GATE3-REG-AUDIT, Workstream 2) and the landed Brick-2
dossier `whitepaper/gate3-meas-swap-landing-2026-11-04.md`.
Fences: **NO CLAIM; dials 0/4.**

## The landing

New module `lean/ThetLogos/Span3SeatSchurGateWild.lean`,
beside the landed statements, **nothing edited**: the frozen
GATE-3 statement `pullBotKernel_seatFactorApproxExpansion`
and the Brick-2 chain are untouched. **Strict count: 6
theorems + 1 def** — itemized:

| # | Declaration | Role |
|---|---|---|
| def | `Gate3WildLemma` | Component 1, isolated: the single remaining lemma of the wild class, as a named Prop (NOT proved). At a wild seat (`¬ Measurable fun g : G => repMatrix ρ g`) and every `β > 0`: the stratum Boltzmann factor is `¬ AEStronglyMeasurable` in the stratum variable, for all layer data `u u'`. |
| 1 | `layerKernel_eq_zero_of_not_aestronglyMeasurable` | Component 2, the vanishing: factor `¬ AEStronglyMeasurable` ∀ `u u'` ⇒ `layerKernel ≡ 0`, via `¬ Integrable` and the pinned convention `integral_undef`. |
| 2 | `pullBotKernel_eq_zero_of_not_aestronglyMeasurable` | The vanishing for the pullback kernel (plain pullback, audit (a): no ratio form). |
| 3 | `layerKernel_eq_zero_of_gate3WildLemma` | The vanishing at a wild seat, from the named lemma. |
| 4 | `layerKernelPos_of_layerKernel_eq_zero` | Component 3, audit (c) first half: at `layerKernel ≡ 0`, `LayerKernelPos` is `0 ≤ (0 : ℂ).re` by its verbatim def. |
| 5 | `seatFactorApproxExpansion_of_pullBotKernel_eq_zero` | Component 3, audit (c) second half: at `pullBotKernel ≡ 0`, the expansion is the explicit zero Gram family (`ι n = PUnit`, `c = 0`, `φ = 0`); difference kernel identically `0`, `MemLp 2` by `memLp_const`, HS norm constantly `0`. |
| 6 | `pullBotKernel_seatFactorApproxExpansion_of_gate3WildLemma` | Component 4 (conditional): **the frozen GATE-3 headline follows from `Gate3WildLemma`.** |

The composition (#6) is a three-way split, all branches
closed with landed material: `β = 0` by the probe fence
`seatFactorApproxExpansion_zero` (unconditional; the
`LayerKernelPos` hypothesis is not consumed — at `β = 0`
the factor is `≡ 1`, so no degeneracy is needed there);
`β > 0`, measurable `ρ`, by Brick 2
(`seatFactorApproxExpansion_of_layerKernelPos_meas`);
`β > 0`, wild `ρ`, by #3 + #5, which discharge the
conclusion outright (hypothesis again not consumed).

**Verification (in-lane).** Targeted build green
(`lake build ThetLogos.Span3SeatSchurGateWild`, 3,678 jobs)
with **zero warning/error lines naming the module** (the
section's unconsumed ambient instances are omitted at the
five affected declarations, the house pattern of Brick 2's
census #1; the Props proved are identical). Zero `sorry`
(source-checked), no `native_decide`. `#print axioms`: all
six theorems depend on exactly
`{propext, Classical.choice, Quot.sound}` — no `sorryAx`.

## Component 1 — OBSTRUCTED, with the exact gap

The audit's rigidity route is a four-step reduction.
Assume the Boltzmann factor is `AEStronglyMeasurable` for
all `u u'` at a wild seat, `β > 0`:

1. **A.e. sections** on the finite stratum product
   (`layerConfig`'s (0,ν)-plaquette word is exactly
   `α c · u' ℓ · (α (σ_ν c))⁻¹ · (u ℓ)⁻¹`, two stratum
   factors interleaved with `u u'`-constants) reduce the
   factor, after peeling `exp` and the finite sum, to
   trace functions `g ↦ tr (repMatrix ρ (g · B))` being
   `AEStronglyMeasurable`.
2. **Trace-form extraction**: as `u u'` vary, the constants
   `B` range over `range ρ`; nondegeneracy of the trace
   form on `span (range ρ)` (a finite-dimensional
   C*-algebra) then gives every entry of `repMatrix ρ`
   `AEStronglyMeasurable` w.r.t. `μG`.
3. — so `repMatrix ρ` is `AEStronglyMeasurable` w.r.t.
   the invariant probability `μG`.
4. **Automatic continuity**: `repMatrix ρ`, a group
   homomorphism `G → U(d)` a.e. equal (Haar) to a
   measurable function, is continuous — hence Borel
   measurable — contradicting wildness.

Steps 1–2 are analysis formalization (a.e.-section
technology on finite pi spaces, two-site word bookkeeping,
trace duality) — substantial but conceivable; they were
not attempted inside this brick's band because step 4 is
blocked outright:

* **The theorem is not in the pinned Mathlib.** Grep of
  the pinned Mathlib source this session: no occurrence
  of "automatic continuity", and no a.e.-measurable ⇒
  measurable (or ⇒ continuous) result for group
  homomorphisms. (Erratum, corrected in-lane before
  integration: this brick's first grep was truncated at
  five hits and misreported Steinhaus as Archive-only.
  In fact the library DOES carry the Steinhaus theorem
  for Haar measures —
  `Mathlib/MeasureTheory/Measure/Haar/Basic.lean`: if
  `E` has positive measure, then `E / E` contains a
  neighborhood of `1` — one leg of the classical proof.
  It does not close the gap: it is stated for
  `[IsHaarMeasure μ]` with inner-regularity side
  conditions the frozen context does not supply — the
  frozen `μG` is an abstract invariant probability with
  no `IsHaarMeasure` instance — and Steinhaus alone is
  not automatic continuity: the Lusin + density passage
  from a.e.-measurability of the homomorphism to its
  continuity is absent as a library result and remains
  research-scale to formalize.)
* **The classical proof's hypotheses are not all in the
  frozen context.** The Steinhaus + Lusin + density
  argument needs `μG` Haar–Radon on a locally compact
  Hausdorff group. This module's frozen section — shared
  verbatim with the frozen statement and Brick 2 — has
  `G` an abstract second-countable topological group
  (no `T2Space`, no `CompactSpace`, no local compactness)
  and `μG` an abstract invariant probability measure
  (no `IsHaarMeasure`, no regularity). So in the frozen
  generality the lemma is not merely unproved-in-band:
  the standard proof does not apply as-is, and the
  lemma's truth at that generality is not certified by
  the classical theorem.

**The lemma is NOT shown false.** No counterexample seat
is constructed or claimed. In the classical reading
(Hausdorff, locally compact `G`, Haar `μG`) the lemma is
TRUE, by the automatic-continuity theorem of step 4.
What is certified here is narrower and exact: the lemma
is the unique remaining gap of the vanishing route
(audit), everything downstream of it is proved (#1–#6),
and its proof requires an automatic-continuity input
that is absent from the pinned Mathlib and whose
classical hypotheses exceed the frozen context. A sequel
would be a research-scale infrastructure brick (formalize
automatic continuity — under added side hypotheses that
would themselves need a scoping decision, since the
frozen statement's context cannot silently grow them),
not a continuation of this band.

Edge seats need nothing (audit, rechecked): seats with
`d = 0` or finite/discrete `G` have empty wild class
(`repMatrix ρ` is constant, resp. everything is
measurable), and `β = 0` is fenced unconditionally by the
landed probe module.

## Accounting against the commission

* Components 2 + 3: LANDED as specified (#1, #2, #4, #5).
* Component 4: LANDED in its conditional form (#6 + #3):
  the frozen headline is proved from exactly one added
  hypothesis, the named Prop `Gate3WildLemma` — carried
  as a theorem hypothesis, never smuggled into any
  statement; no frozen statement was edited and no side
  condition was silently introduced anywhere.
* Component 1: OBSTRUCTED per the honesty gate's
  alternative — reported with the exact gap in place of
  a proof. It is not reported FALSE: the counterexample
  shape the gate asks for does not exist in the classical
  reading (the lemma is true there); the failure is
  proof-infrastructure, located precisely at step 4.
* Band: 6 strict + 1 def landed against the 15–40 band.
  The band was dominated by component 1's anticipated
  proof; the landed components came in light because the
  β = 0 probe module supplied the zero-family template
  and the vanishing is a one-line `integral_undef`
  discharge. The stop-line (45) was never approached.

## Scope fence

The frozen GATE-3 statement remains **OPEN** after this
brick. Along the vanishing route its remaining gap is now
exactly one named Prop, `Gate3WildLemma`. Even with that
lemma supplied and GATE-3 thereby discharged, the
discharge would close only this one hypothesis-gate
inside item 5's seam: it does **not** prove
`LayerKernelPos` (the `𝒜 ⪰ 0` core — which in the wild
branch of the composition is not even consumed), does
**not** close W3 at full generality, and moves **no
dial**. Kill status: **K-GATE-3 did NOT fire** — it fires
only on a seat with `LayerKernelPos` proved and the
expansion refuted; no such seat is produced or approached
here, and the wild lemma's obstruction is a gap in proof
infrastructure, not a refutation of anything.

NO CLAIM; dials 0/4.
