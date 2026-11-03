# U-1 ONE KERNEL — Landing Dossier

**Brick:** U-1 "One Kernel", first brick of the unification line
(scoping: `your_files/unification-scoping-2026-11-03.md` §2).
Fired by Jeff by name, 2026-11-03 ("Fire U-1 ONE KERNEL").
**Lane:** worktree `~/workspace/thet-logos-u1`, branch
`u1-one-kernel-lane`, based on main-tree local HEAD 0289e82
(Triplets ceremony commit). NOT integrated — parent runs the
ceremony. (Note: main has since taken the GATE item 6 ceremony,
remote 8dbcba5e; integration must land on the new HEAD.)
**Module:** `lean/ThetLogos/OneKernel.lean`.

**NO CLAIM** — parts of any official Millennium statement closed
by this module: 0. **Dials: 0/4.** Unifying the corpus's finite
graph seats is not a unified theory of physics: this module
derives no measured number, contains no gravity object, proves
no continuum limit, predicts nothing external.

## Verdict: FULL

Both parts landed as scoped. Neither pre-registered kill fired.

| Part | Verdict | Headline |
|---|---|---|
| 0. Double count | FULL | `sum_adj_apply_eq_two_mul_sum_edgeFinset` |
| (a) Bridge↔AxiomTet dictionary | FULL | `bridge_energy_eq_breakEnergy` |
| (a) Strengthened Bridge corollary | FULL | `eq_const_of_bridge_energy_eq_zero` |
| (b) boxProd identification, energy form | FULL | `breakEnergy_boxProd_cycle_eq` |
| (b) boxProd identification, kernel form | FULL | `lapSum_eq_zero_iff_breakEnergy_boxProd` |
| (b) Demotion of O4+ | FULL | `lapSum_eq_zero_iff_via_oneKernel` |

Strict count: **20 theorems** (+ 1 def `denseWeight`, + 1
instance `Fintype ManifoldIndex`) — inside the scoping's M band
(est. strict 20–40), at its floor. Targeted build green;
zero errors and zero warnings attributable to OneKernel.lean;
zero sorrys. `#print axioms` on all headlines: exactly
{propext, Classical.choice, Quot.sound}, no sorryAx.

## Part (a) — the dictionary, at exact equality

The scoping priced the identification at proportionality /
kernel equality and named the load-bearing form accordingly.
What landed is stronger: with
`denseWeight G w i j := if G.Adj i j then w s(i, j) else 0`,

```
∑ i, f i * laplacianOp (denseWeight G w) f i = breakEnergy G w f
```

— the same number, factor 1. Route: Bridge's `energy_identity`
gives `2 * (Bridge form) = ∑ i, ∑ j, denseWeight * (f i - f j)^2`;
Part 0's double count reindexes the ordered adjacent sum onto
`2 * ∑ e ∈ G.edgeFinset` (the fiber of `p ↦ s(p.1, p.2)` over an
edge is exactly its two orientations); linarith closes.

**K-U1-DICT did NOT fire.** The Bridge energy reindexes onto
`edgeFinset` under `denseWeight` exactly; no convention mismatch.

**The corollary returns stronger, as the scoping directed.**
Bridge's `eq_const_of_energy_eq_zero` as landed requires ALL
off-diagonal conductances positive (complete support).
`eq_const_of_bridge_energy_eq_zero` proves constancy from
`G.Connected` plus per-edge positivity only — AZ-2W's
hypotheses — via the dictionary (`bridge_energy_eq_zero_iff`).
The PARTIAL seam the scoping pre-registered (dictionary only
supporting the weaker form) did not materialize.

## Part (b) — the Orthogonal identification and the demotion

The Orthogonal grid is `GridIndex = ManifoldIndex × ManifoldIndex`
with `lapSum = lap₁ + lap₂` built from the cycle steps
`succ`/`pred`. The graph is `(cycleGraph 21).boxProd (cycleGraph 21)`:

- Cycle adjacency is exactly the two steps (`cycle_adj_iff`,
  via `cycleGraph_adj'` and the uniform `Fin.val_sub` wrap
  formula): `Adj a a' ↔ a' = succ a ∨ a' = pred a`.
- Connectedness is Mathlib's: `boxProd_cycle_connected` is
  `SimpleGraph.Connected.boxProd` at `cycleGraph_connected`.
- At each grid point the ordered box-product neighbor sum is
  the four squared steps (`inner_adj_sum_boxProd`; the two
  boxProd adjacency cases are mutually exclusive by
  looplessness, so the indicator splits). Predecessor steps
  reindex onto successor steps (`pred_step_sum_fst/snd`, via
  Orthogonal's own `succEquiv₁/₂`), giving
  `ordered_adj_sum_boxProd`: the ordered sum is twice the
  step energy. Part 0's double count then gives the
  identification in energy form:
  `breakEnergy (boxProd) (fun _ => 1) f = ∑ (Δ₁f)² + ∑ (Δ₂f)²`,
  i.e. `∑ p, f p * (lapSum f) p = breakEnergy (boxProd) 1 f`
  (`lapSum_energy_eq_breakEnergy_boxProd`).

**K-U1-BOX did NOT fire.** The `lapSum` kernel is the
boxProd break-energy kernel:
`lapSum_eq_zero_iff_breakEnergy_boxProd`.

**Demotion.** `lapSum_eq_zero_iff_via_oneKernel` reproves the
exact statement of Orthogonal's O4+ (`lapSum f = 0 ↔ ∃ c, f =
fun _ => c`) routed entirely through the master theorem:
kernel identification, then AZ-2W
(`breakEnergy_eq_zero_iff_constant`) at the box product.
The original `lapSum_eq_zero_iff` keeps its name, statement,
and seat untouched in `MirrorTwentyOneOrthogonalSpectral` —
the corollary is an additional route; the standalone walk
argument of the original proof is no longer load-bearing.

## Demotion / identification map (after U-1)

- O4+ `lapSum_eq_zero_iff` ⇒ corollary of AZ-2W, via
  `lapSum_eq_zero_iff_breakEnergy_boxProd` +
  `boxProd_cycle_connected`.
- Bridge `eq_const_of_energy_eq_zero` ⇒ superseded in strength
  by `eq_const_of_bridge_energy_eq_zero` (connectedness form),
  via `bridge_energy_eq_breakEnergy` + AZ-2W.
- Bridge `energy_identity` at `denseWeight` ⇔ AZ-2W's form:
  the same quadratic form (`bridge_energy_eq_breakEnergy`).
- (Pre-existing, no work in this brick, per the scoping:)
  Mirror-21's cycle kernel is already an in-tree corollary of
  AZ-2W (`cycle_breakEnergy_eq_zero_iff_constant`); Partner
  SP-1 already consumes `breakEnergy` directly; Partner
  SP-2/SP-4 are already fully general over (G, w), not
  instances awaiting identification.

## What did NOT unify (fences, unchanged)

- The analytic line (LayerKernelPos / FACT / GATE / W3),
  SHELF-8B's general Banach-lattice clause, BSD, Hodge: do not
  unify with the finite seats; untouched by this brick.
- Dual-Current: unexamined here, not unified.
- Partner's operator-form kernel theorem was not re-derived
  through the dictionary; Partner was already welded to AZ-2W
  by construction (SP-1), so no identification was owed.
- Kernel dimension 1 (this brick's seats) vs fixed-function
  dimension 11 (Mirror-21): different theorems, fenced apart,
  neither touches the other.

## Build notes (for the ceremony)

- One new global instance ships in this module:
  `instance : Fintype ManifoldIndex`, proved by
  `show Fintype (Fin 21); infer_instance` — the same device
  Orthogonal's module uses for `GridIndex` (`ManifoldIndex` is
  a plain `def` for `Fin 21`, so typeclass search does not see
  through it). Flagged for the ceremony: it is global once
  imported.
- Proof-style note for future lanes: graph lemmas at
  `ManifoldIndex`-typed vertices are applied in term mode
  (`cycleGraph_adj'.mp/.mpr`, `Fin.val_sub` as a term +
  `omega`), because rewrite matching at implicit transparency
  cannot see through the alias; and `diffSq` at the box
  product is pinned with `(V := Fin 21 × Fin 21)` where a
  rewrite/linarith must match the fiber lemma's elaboration.
  Full detail in the module header comment.
- Suggested fence admissions at integration: the 12 checked
  headlines (dictionary pair, strengthened corollary, double
  count, cycle adjacency, boxProd connectedness, inner/ordered
  sums, the two identification forms, the demotion) — registry
  edit and module in the same commit, per the CI lesson.

**NO CLAIM. Dials 0/4.**

## CEREMONY (parent, main tree, 2026-11-03)

- Lane files copied byte-identical from worktree
  `~/workspace/thet-logos-u1` (branch `u1-one-kernel-lane`,
  commit `402eb88`) into the main tree at local HEAD
  `f57a107` (item-6 ceremony commit); identity verified by
  diff. The lane base predates the item-6 ceremony; both
  files are new to the tree, no merge was needed.
- Targeted main-tree build `lake build ThetLogos.OneKernel`:
  **green** (3155 jobs), zero sorrys (no `sorry` token in
  the module); zero errors and zero warnings attributable
  to OneKernel.lean (build warnings are pre-existing
  deprecation/linter warnings in dependency modules,
  BridgeLaplacian among them).
- Independent strict recount of the module (method of
  record: nesting-aware comment stripping, string-aware,
  `^(theorem|lemma)\s` at column 0): **20 strict + 1 def
  (`noncomputable def denseWeight`) + 1 instance**,
  matching the lane count exactly.
- **Global-instance note (flagged at the lane, recorded
  here, not hidden):** the module ships one new global
  instance, `instance : Fintype ManifoldIndex`, proved by
  `show Fintype (Fin 21); infer_instance` — the same
  device Orthogonal's module uses for `GridIndex`.
  `ManifoldIndex` is a plain `def` for `Fin 21`, so
  typeclass search does not see through it; the instance
  is global once OneKernel is imported. The ledger record
  carries this note on its face as well.
- Axiom fence: the 12 checked headlines admitted to
  `lean/scripts/axiom-fence.txt` WITH their import line
  (`import ThetLogos.OneKernel`) in the SAME commit as the
  module file, per the standing CI lesson. Official
  runner: **FENCE PASS 82/82** (70 → 82) — every admitted
  headline, old and new, on exactly {propext,
  Classical.choice, Quot.sound}, no sorryAx.
- Corpus census (method of record; shipped chain):
  12,922 / 13,448 / 468 → **12,942 strict / 13,468 total /
  469 modules**, zero sorrys. The chain carries the
  documented +2 ledger overstatement of
  census-reconciliation-2026-11-02, unchanged by this
  landing — restating the public census remains Jeff's
  open decision. README prose census updated (12,922 →
  12,942 declarations; 468 → 469 modules); the README
  badge was NOT touched (Jeff's pending decision).
- Ledger record `u1-one-kernel` (standing, T3) added with
  the FULL verdict, the demotion map, and the
  global-instance note on its face; validator PASS, 14
  records conform.
- Verdict stands as landed: **FULL** — dictionary at
  exact equality, Bridge corollary strengthened to
  connectedness, boxProd identification, O4+ demoted to
  a corollary of AZ-2W with the original untouched;
  K-U1-DICT and K-U1-BOX did not fire. Unifying the
  corpus's finite seats is not a unified theory of
  physics. NO CLAIM; dials 0/4.
- This dossier lands in the U-1 ceremony commit (module,
  dossier, registry, README, ledger in one commit); the
  commit hash and push verification are recorded in the
  pipeline log entry for this ceremony.
