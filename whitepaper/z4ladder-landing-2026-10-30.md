# Z4-LADDER — the 4-state Gibbs ladder, landed honest

**Date:** 2026-10-30 · **Brick:** Z4-LADDER (S–M), Jeff's commission
"build it" (2026-10-30 01:22 EDT), bounded by the parent per the
compile-check audit of the dropped file
(`audit-dropped-thermal-z4-2026-10-30.md`). New module:
`ThetLogos.ThermalZ4Ladder`. **Verdict: LANDED FULL.**

**Fences: NO CLAIM. Parts of any official statement closed: 0.
Dials: 0/4.**

## What landed (strict 5 / defs 3, parent-verified from disk)

`Fin 4` used directly; β explicit in every binder; no `variable`.

- `z4Energy (k : Fin 4) : ℝ := (k : ℝ) / 4` — the ladder
  E_k = k/4, declared on the module's face as a **CHOSEN INPUT,
  not derived**.
- `z4Partition β := ∑ k, exp(−β · z4Energy k)`;
  `z4Weight β k := exp(−β · z4Energy k) / z4Partition β`.
- `z4Partition_pos`, `z4Weight_pos` — positivity from `Real.exp_pos`.
- `z4Weight_sum_eq_one : ∑ k, z4Weight β k = 1` — normalization.
- `z4Weight_step_ratio (k : Fin 3) :
  z4Weight β k.succ = z4Weight β (Fin.castSucc k) * exp(−β/4)` —
  the within-ladder steps (0→1, 1→2, 2→3), general form.
- `z4Weight_wrap_ratio : z4Weight β 0 = z4Weight β 3 * exp(3β/4)` —
  the wrap step, stated plainly as its own clause.

The header prose says what the object is: a staircase that does
**not** close as a cycle — three equal within-ladder ratios
exp(−β/4) and one wrap ratio exp(+3β/4). No disjunction hides the
jump.

Axiom footprints (parent landing standard): all five theorems
exactly `[propext, Classical.choice, Quot.sound]`. Module and
full-tree builds green.

## What was refused, on the record

The dropped file's `InternalAlgebra` and
`ModularAutomorphismGroup` structures (content-free labels: no
instance, no use) and its `KMSState` structure are **NOT built**.
`KMSState` is **VACUOUS as defined** — audit-certified: satisfiable
for every σ and every normalized linear ω at every β ≠ 0, because
its boundary field asks only for a function taking two prescribed
values at two distinct points; the analyticity that gives KMS
content exists only in its docstring. This house does not land
degenerate pins. Where KMS is relevant, the module references the
corpus's owned finite KMS machinery (`ThetLogos.KMSBridge`) by
name. The dropped file itself does not compile (7 errors,
import-set failure among them); this module is a fresh build to
house standard, not a transplant — its import set
(`Mathlib.Tactic`, `Mathlib.Analysis.SpecialFunctions.Exp`) was
probe-verified against the names it uses.

## Fences kept

No entropy language anywhere in the brick (T-ENT gate — the tree
has no entropy definition yet). No claim that the brick touches
the C⁴ leg, W1/W2, or the G1/G2 refutation, in either direction:
it is **raw material for the Q7CR line's C⁴ factor**, and says
exactly that. BRIDGE-1: no Python side (closed-form arithmetic);
no registry entry — not a probe, per K-BR1.

**Census: 7,446 → 7,451 strict / 7,524 → 7,529
attribute-inclusive / 255 → 256 modules** (recounted from disk).

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you to
everyone reading the stream — the corpus is free for everyone,
forever.

*End of dossier.*
