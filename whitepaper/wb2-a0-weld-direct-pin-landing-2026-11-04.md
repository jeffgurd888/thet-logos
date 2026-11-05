# WB-2 — The A0 Weld in Direct Form: Landing Dossier (2026-11-04)

Brick WB-2 of the weld line (Jeff's "fire all welds",
2026-11-04). Lane: worktree `~/workspace/thet-logos-wb2`,
branch `wb2-lane`, base main-tree HEAD `798c680`. Module:
`lean/ThetLogos/Span3A0WeldDirect.lean` — **3 strict**
(`theorem`/`lemma` at column 0, comment-stripped) + 1 def,
zero sorry, no `native_decide`, warning-clean on a targeted
build (3,648 jobs); `#print axioms` NOT obtained in-lane
(six attempts starved by machine contention, zero Lean
diagnostics — see §5; parent to confirm at the integration
fence before admission).

**Verdict: LANDED (pin-grade).** The A0 weld is stated in
direct form in one environment importing both chains, and
the two pin-grade compositions around it are proved. The
weld itself is NOT proved — see the fence (§4).

---

## §1 — The 2026-10-31 formulation, quoted

The governing scoping memo
(`routeb-general-scratch/scoping-f2-weld-2026-10-31.md`,
§2 "Q1: The weld, exactly"):

> **What must be connected.** The implication registered
> as `A0AssemblyTarget`: at `Even N`, with `hρcont` (and
> `2 ≤ N`, `0 < d` where the route consumes them),
>
> > (∀ β ≥ 0, `LayerKernelPos μG ρ β`) ⇒ (∀ β ≥ 0, clause
> > (a) of `TransferFormPos`),
>
> where clause (a) is `∀ f : osSpace, 0 ≤ (inner ℂ f
> (transferOp … f)).re`. Since the transport
> `SliceHPosOne ⇒ clause (a)` is landed
> (`LatticeSliceDescent:132`), the weld's mathematical
> content is exactly the intermediate implication, at each
> `β ≥ 0`:
>
> > **`LayerKernelPos μG ρ β` ⇒ `SliceHPosOne μG ρ hN2
> > hρcont β`**,
>
> or, equivalently (the F2 header's own disjunction), the
> `osForm` / `planeAvgPairing` diagonal positivity on
> strict-half observables, transported through
> `osForm_eq_planeAvgKernel`.

The registered headline it serves, verbatim from
`Span3FactLayerKernelPos.lean:296`:

```lean
def A0AssemblyTarget (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (_hd : 0 < d) :
    Prop :=
  Even N →
  (∀ β : ℝ, 0 ≤ β → LayerKernelPos (N := N) μG ρ β) →
  ∀ β : ℝ, 0 ≤ β → TransferFormClauseA (N := N) μG ρ β hN2 hρcont
```

And the registered weld pin (F2-W0,
`Span3A0AssemblyPost.lean`, def
`layerKernelPos_implies_sliceHPosOne`), verbatim:

```lean
def layerKernelPos_implies_sliceHPosOne
    (SlicePos : (2 ≤ N) →
      (Continuous fun g : G => repMatrix ρ g) → ℝ → Prop) :
    Prop :=
  ∀ (hN : Even N) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ), 0 ≤ β →
    LayerKernelPos (N := N) μG ρ β → SlicePos hN2 hρcont β
```

F2-W0's header states why the pin is parameterized: at
registration the `LayerKernelPos` chain and the
`LatticeSliceDescent` chain "sat on opposite sides of the
`reflSite_eq_torusShift_zero` duplicate seam … and at
registration no single Lean environment could import both
chains", and "the direct statement of target (1), with
`SliceHPosOne` named in the code itself, becomes formable
only after F2-W1". F2-W1 landed 2026-10-31 (the
`PlaneCrossingFactor` copy renamed
`reflSite_eq_torusShift_zero_bot`; co-import probe
passed), and the weld scoping of 2026-11-04 (Map B, B-1)
re-verified the remediation at HEAD by grep. The seam has
been closed for four days; what was missing was the
direct statement itself. That is this brick.

The downstream end, verbatim signature
(`LatticeSliceDescent.lean`):

```lean
def SliceHPosOne (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) : Prop

theorem inner_transferOp_self_re_nonneg_of_sliceHPosOne (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f : osSpace (N := N) μG ρ β) :
    0 ≤ (inner ℂ f (transferOp μG ρ hN2 hρcont β f)).re
```

and clause (a), verbatim (`Span3FactLayerKernelPos.lean`):

```lean
def TransferFormClauseA (β : ℝ) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) : Prop :=
  ∀ f : osSpace (N := N) μG ρ β,
    0 ≤ (inner ℂ f (transferOp μG ρ hN2 hρcont β f)).re
```

## §2 — The direct statement

`Span3A0WeldDirect.lean` imports
`ThetLogos.Span3A0AssemblyPost` (which pulls
`Span3FactLayerKernelPos` and `PlaneCrossingSeparate` —
the `PlaneCrossingFactor` side of the retired seam) and
`ThetLogos.LatticeSliceDescent` (which pulls
`LatticeSlicePairing` → `LatticeReconZero` → the
`LatticeGramSeries` side) into ONE environment, and
states:

```lean
def A0WeldDirect : Prop :=
  ∀ (_hN : Even N) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ), 0 ≤ β →
    LayerKernelPos (N := N) μG ρ β → SliceHPosOne μG ρ hN2 hρcont β
```

(in the section context shared by both chains: general
`(G, ρ)`, `μG` Haar probability with both invariances,
`{N} [NeZero N]`). `SliceHPosOne` is named in the code —
the thing F2-W0 could only name in prose. The sole
deviation from the pin's binder text is `_hN` for `hN`
(the `Even N` hypothesis is not referenced in the body;
the rename is the unused-variable linter's own
prescription and changes nothing semantically).

## §3 — The composition map

Two theorems, both pin-grade (compositions of landed
objects, no new mathematics):

1. **`a0WeldDirect_iff`** — `A0WeldDirect μG ρ ↔
   layerKernelPos_implies_sliceHPosOne μG ρ (fun hN2
   hρcont β => SliceHPosOne μG ρ hN2 hρcont β)`, proved by
   `Iff.rfl`. The direct form is *definitionally* the
   registered pin at its intended instantiation: the
   restatement is checked against the registration, not
   against a paraphrase, and it neither strengthens nor
   weakens the weld by one hypothesis.
2. **`a0AssemblyTarget_of_a0WeldDirect`** — from
   `hW : A0WeldDirect μG ρ`, the registered headline
   `A0AssemblyTarget μG ρ hN2 hρcont hd` follows: unfold
   the headline to its `∀ β ≥ 0 → TransferFormClauseA`
   body, unfold clause (a) to its pointwise body
   `∀ f : osSpace, 0 ≤ (inner ℂ f (transferOp … f)).re`,
   and at each `β` apply the landed transport
   `inner_transferOp_self_re_nonneg_of_sliceHPosOne` to
   `hW hN hN2 hρcont β hβ (hLKP β hβ)`. Both unfoldings
   are definitional (clause (a) was *registered as* the
   transport's conclusion, quoted exactly in S3-1-F2), so
   the composition is exact: **the weld, where supplied,
   is the headline's only missing component — machine-
   checked, not argued.** A third headline,
   `a0WeldDirect_apply`, is the house-style read-back of
   the direct form at a single `β`.

What this converts (weld scoping, WB-2 pricing): W-A8's
form status goes from "unstatable as registered" to
"stated in direct form, in the environment where both
ends live, with the headline composition proved". The
weld's *status* is unchanged: CONDITIONAL, open.

## §4 — The fence

This pin does NOT prove the weld. The weld's two blockers
stand exactly as graded in the weld scoping (W-A8):

- **(i) Its input is open.** `LayerKernelPos` at every
  `β ≥ 0` in general is an open hypothesis. Its proved
  supports after LK-P0 (2026-11-04) are exactly:
  `layerKernelPos_zero` (β = 0, at general `(G, ρ)`) and
  `layerKernelPos_seat` (the single seat N = 2, ZMod 2,
  sign representation, at every `β ≥ 0`). The FACT route
  into it is refuted (K-FACT-SEAT, same day); the weld
  scoping's redrawn graph records that no proved path
  into `LayerKernelPos` at `β > 0` in general survives.
- **(ii) Its middle is missing.** No landed theorem
  derives `SliceHPosOne` from `LayerKernelPos`. The
  missing component is the integral-kernel Schur/product
  composition: at the seat it is F2-W0's target (2)
  (`SeatSchurTarget`, stated, not proved); in abstract
  form it is item (3) of `IntegralKernelSchur`, named
  OPEN on that module's face (items (1)(2)(4) landed).
  That composition belongs to its own line's pricing;
  nothing here prices it.

Consequently this module does NOT prove `LayerKernelPos`,
does NOT close clause (a) (the headline remains an
implication; its antecedent now factors through a named
direct-form weld instead of a parameterized pin), and
moves NO dial. Any sentence describing this landing as
progress on FACT, on the layer kernel's positivity, on
clause (a) itself, or on uniformity is the K-F2-4
buy-inflation failure and is void on sight. K-F2-2
(invariance confinement) and K-F2-3 (generality creep)
remain armed against the weld's proof, untouched by this
pin: the direct form is stated at exactly the registered
generality — general `(G, ρ)`, probability measure,
`Even N` — and at no other.

**NO CLAIM; dials 0/4; parts of the official statement
closed: 0.**

## §5 — Verification record

- Base: main-tree HEAD `798c680` (LK-P0 integration);
  lane branch `wb2-lane`.
- Targeted build `lake build ThetLogos.Span3A0WeldDirect`:
  green, 3,648 jobs; zero warning/error lines naming the
  module (the one linter note on the first pass — the
  unreferenced `hN` binder — was fixed by the `_hN`
  rename above and does not recur).
- Strict recount: 3 (`a0WeldDirect_iff`,
  `a0WeldDirect_apply`,
  `a0AssemblyTarget_of_a0WeldDirect`) + 1 def
  (`A0WeldDirect`). Inside the WB-2 band (S, 0–4); the
  stop-line (6) untouched.
- Axioms: **NOT CHECKED IN-LANE — parent to confirm at
  integration.** `#print axioms` on the three headlines
  was attempted six times (standalone `lake env lean` and
  scratch-module builds); every attempt was killed or
  starved with zero Lean diagnostics under extreme
  machine contention (three sibling lanes building
  concurrently, load average peaking at 15.6, ~135 MB RAM
  free, and one full VM reboot mid-storm that SIGTERM'd
  the in-flight attempts; the longest attempt ran the
  full 600 s timeout without producing output). No
  attempt ever reported an error in the module. Expected
  result, to be confirmed before fence admission:
  exactly {propext, Classical.choice, Quot.sound} each,
  no sorryAx. Source check (done in-lane): no `sorry`,
  no `admit`, no `native_decide` in the module.
- The module is not added to the root import list (the
  corpus pattern for pins); integration, if the parent
  runs it, admits the 3 headlines to the fence with the
  import, per house practice.
