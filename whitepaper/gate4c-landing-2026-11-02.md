# GATE-4C LANDING DOSSIER — 2026-11-02

**Item:** GATE-4 conditional re-pin (F2 weld line) — register
the conditional form of GATE-0 item 6 as a NEW registry
entry (GATE-4C) and run it to verdict. **Commission:**
Jeff's decision 2026-11-02 00:48 EST ("conditional
re-pin") — the parent decision named in
`whitepaper/f2-gate-g2c-landing-2026-11-02.md` ("a
conditional form would be a NEW registry entry (parent
decision)").

## VERDICT: GATE-4C REGISTERED + DISCHARGED (FULL)

The conditional limit passage is a theorem. The frozen
item 6 is untouched and unproved (see K-GATE-4C-2
below). Census after landing: **12,750 strict / 13,276
total / 460 modules, zero sorrys** (see the census note
in the Census section: a sibling run's GATE-3 probe
landing intervened between this run's pin and discharge
commits); CI axiom fence PASS
35/35 (registry grew by the two headlines below; axioms
exactly `[propext, Classical.choice, Quot.sound]`
throughout). NO CLAIM; dials 0/4.

## The registration (pin: `lean/ThetLogos/Span3SeatSchurGate4C.lean`, strict 0 / defs 1)

`seatSchurTarget_of_approxProductStep_gate4c` — at every
even `N` with `4 ≤ N`, every `β`, at `0 < d`: given the
antecedents below, `SeatSchurTarget μG ρ hN β` in its
exact registered form. Landed and pushed as its own
commit (remote 28bee61b) BEFORE the proof bricks were
dispatched, per the interface-first discipline. The
frozen GATE-0 pin (`Span3SeatSchurGatePost.lean`,
item 6 `seatSchurTarget_of_approxProductStep`) stands
UNEDITED.

**Carried hypotheses, each with its reason (on the
pin's face):**

| Hypothesis | Why it is carried |
|---|---|
| `4 ≤ N` | The re-pinned gate's domain. GATE-2's kill stands at `N = 2` (embeddings coincide); the antecedent package is in prospect of discharge only at `4 ≤ N` (G2c discharged there). The passage's algebra does not consume `hN4`; the restriction is registry discipline. |
| `hd : 0 < d` | Consumed only by the folded form's weight bound: `GramAssemblyWord.abs_halfActionP_le` rests on `plaquetteDensity_mem_Icc`, landed only at `0 < d`. The marginal form does not need it; carried once for the conjunction. The same `hd` rides W3's registered headline (gate scoping §5). |
| Expansion data `(ι, c, φ)` explicit, item 1's clauses verbatim (`0 ≤ c n i`; difference kernel `MemLp 2`; `eLpNorm` → 0) | Item 1 packs the data existentially; `hIntStage` is quantified over the data's own factors, so the data is named. Factors are pulled back from layer functions (§2.2 audit point: no Gram of `𝒜`). |
| `hIntStage` (per `f`, stage `n`, factor `i`; marginal + folded) | The dressed factor integrands' product-seat integrability, in exactly the shapes the landed core's `hInt` family consumes (the landed conditional's `hIntMarg`/`hIntFold` shapes). Pin finding: item 1's frozen data carries no factor measurability and only a difference-kernel `MemLp` clause, which does not yield these integrands' integrability; joint measurability of `layerKernel` in its two arguments is landed nowhere at this generality (kernel-measurability lemmas carry `Continuous fun g => repMatrix ρ g`, absent here). Carried, not derived — the GATE-2 species. |
| `hIntLim` (per `f`; marginal + folded target integrands) | The limit identification's input: the passage writes the target pairing as a difference of Bochner integrals and takes the limit; if the target integrand were not integrable, the target pairing would be the junk value `0` and the limit statement about it would not be the registered one. |
| Factor pairings (item 6's second antecedent, VERBATIM) | Consumed at each finite stage by the landed core. |

**`hMarg` NOT carried — scoped on the face.** The
splice disintegration / fiber marginalization belongs
to the pairings' discharge route (G2b's fiber-average
identities), not to the limit passage: the passage
consumes the pairings as a hypothesis and never
re-derives them.

**Kills pre-registered on the pin's face, before any
build:** K-GATE-4C-1 (passage falsity: a counterexample
meeting ALL antecedents at some even `N ≥ 4`, `0 < d`,
with `SeatSchurTarget` failing, kills the limit route
at full rank); K-GATE-4C-2 (weakening smuggling, K-F2-3
species: landing this conditional under item 6's frozen
name, or describing it as discharging GATE-4 / item 6 /
any part of `seatSchurProductStepOpen`, is void);
K-F2-2 / K-F2-3 / K-F2-4 as registered; the
exact-finite-smuggling and spectral-smuggling
void-on-sight items from GATE-0's face.

## The discharge (two bricks, both parent-verified in the main tree)

1. **Limit engine** — `lean/ThetLogos/Span3SeatSchurGate4CLimit.lean`,
   strict 1 / defs 0. `seatPairing_pullTop_tendsto_of_kernel_approx`:
   the seat pairing is continuous in its second kernel
   factor along `L²` approximations of `pullBotKernel`
   (difference-of-integrals; pointwise bound
   `(C₁ · exp (|β| · layerBoundConst N) · C₂) · ‖D n‖`
   via `layerKernel_norm_le`; `∫ ‖D n‖ ≤ (eLpNorm (D n) 2 ·).toReal`
   on the probability product; squeeze). Analysis
   infrastructure at the concrete seat; proves no
   positivity.
2. **Assembly** — `lean/ThetLogos/Span3SeatSchurGate4CProof.lean`,
   strict 1 / defs 0. `seatSchurTarget_of_approxProductStep_gate4c_proved`:
   one pair lemma (per-stage `seatPairing_mul_nonneg_of_finiteRank`
   with that stage's exact finite Gram sum — never the
   limit fed to the exact-finite conditional; stage
   integrability from `hIntStage` by the finite-sum
   identity; the limit engine; `Complex.continuous_re`;
   closedness of `Ici 0`), applied to the twirled pair
   (marginal conjunct) and, through
   `planeAvgPairing_eq_seatPairing_marginal_fold`, to
   the half-action-folded pair (averaged conjunct; the
   weight bound via `abs_halfActionP_le` at `hd`).

**Pack slips, owned on the record** (all in the
coordinator's packs, none in the registered statement):
Limit brick — the pack prescribed the `integral_mono_ae`
majorant as an `AEStronglyMeasurable` term; in this pin
`integral_mono_ae` takes two `Integrable` arguments, and
the builder used the integrability form of the same
majorant (same route). Assembly brick — (i) the proved
theorem's statement annotates the pin constant with
`(N := N)`: the pack's bare `… μG ρ` does not elaborate
(the pin's `N` is implicit and underdetermined); the
same Prop at the section `N`, no hypothesis or
conclusion changed; (ii) the full name of the weight
lemma is `GramAssemblyWord.abs_halfActionP_le` and its
module `ThetLogos.LatticeGramAssembly` needed an
explicit import; (iii) the stage sums run under the
pin's intro'd `Fintype` data via a transparent `letI`
(opaque instances mismatch `Finset.univ`); (iv)
`norm_mul_le` for `norm_mul` at the observable bound
(`norm_mul` on `ℂ` is an equality in this pin). One
style-linter warning (the `letI`) remains; its
suggestion would break the proof, since `Fintype` is
data.

**Kill status.** K-GATE-4C-1 does NOT fire — the
conditional is proved, so no counterexample can meet
its antecedents; the kill stays on the pin's face as
the registration's falsity condition. K-GATE-4C-2
respected throughout: nothing in this landing is
stated under item 6's name or as its discharge.
K-F2-2 / K-F2-3 / K-F2-4: no trigger.

## What stands between here and W3 (named, not hidden)

GATE-4C discharges the limit passage ONLY.
`seatSchurProductStepOpen` at `4 ≤ N` additionally
requires, all still open:

- **GATE-3 / item 5** (`SeatFactorApproxExpansion` at
  `4 ≤ N`): NOT discharged, NOT fired here. Per the
  proceed-run scoping, its arbitrary-factor form is
  equivalent to positive-semidefiniteness of the
  layer-kernel operator on all of `L²(layer)` — a
  Gram/PSD fact about `𝒜` itself, a core-chain object.
  **GATE-3 remains Jeff's untaken decision**; the
  falsity probe Jeff ordered separately (00:49 EST)
  ran concurrently with this landing and EXHAUSTED —
  K-GATE-3 does NOT fire and stays dossier-grade
  (sibling commit 08737fc; its in-tree fence also
  landed `seatFactorApproxExpansion_zero`: item 5
  holds at `β = 0` at every seat unconditionally —
  failure to kill is not evidence item 5 is true at
  `β > 0`, per that dossier's squeeze argument).
- **Hypothesis 6's pairings for the expansion's
  factors**, as a package: unlanded. The landed stock
  covers the diagonal dressed pairings' route (G2b
  identities as re-pinned items 3, in their
  `hInt`/`hMarg` conditional forms; G2c's invariance
  DISCHARGED at `4 ≤ N`), but the item-6 form pairs the
  pos-dressed against the mirror-dressed observable —
  the off-diagonal assembly, and the `hInt`/`hMarg`
  instances at the seat, are unlanded work.
- **The `hIntStage` / `hIntLim` instances at the
  seat**: unlanded. (Whether they follow at the seat
  from kernel boundedness plus joint measurability
  under an added `Continuous repMatrix` hypothesis is
  a question for that future entry; the registered
  target carries no such hypothesis and none was
  silently assumed here.)

F2-W3 does not fire on this landing.

## The fence, restated

The discharged conditional is one weld lemma. The gate
+ W3, even completed, would prove neither FACT nor
clause (a); `LayerKernelPos`, `𝒜 ⪰ 0`, and uniformity
remain open. **NO CLAIM** — parts of any official
Millennium statement closed: 0. Dials: 0/4.

## Census

This run's contributions: pin +0 strict / +1 def
(12,745/13,271/457 at its commit) + Limit +1/+0 +
Proof +1/+0. Between the pin and discharge commits a
sibling run landed the GATE-3 falsity probe
(08737fc: +3 strict / +3 total / +1 module →
12,748/13,274/458), so the ledger at this landing
reads **12,750 strict / 13,276 total / 460 modules**,
zero sorrys. README census verified in HEAD at this
ship. Ledger record: `gate-4c-conditional-limit-passage`
(epistemic-ledger, validator re-run at this landing:
PASS, 7 records conform).

## BRIDGE-1

No Python/Lean interface changed by this landing; no
registry entries added by it. (The registry stands at
BR1-001…031 after the sibling probe run's BR1-031,
landed concurrently — not this landing's entry.)

*End of dossier.*
