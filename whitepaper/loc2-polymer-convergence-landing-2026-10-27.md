# LOC-2 — Polymer Species and the KS Criterion: Uniformity Is Born (at the Per-Column Series)

*Landing dossier, 2026-10-27. Module:
`lean/ThetLogos/PolymerConvergence.lean` (strict 35
total; Parts 2–4 add 8 defs; zero placeholders, zero
`native_decide`; main-tree build green, 3,484 jobs,
parent-verified; both headlines' axiom sets exactly
`[propext, Classical.choice, Quot.sound]`). **Parts of
the Clay Yang–Mills statement closed by this landing:
0.** Verdicts: Part 2 FULL; Part 3 FULL and
unconditional; Part 4 PARTIAL by its pre-registered
seam. This is the ladder's Step 3 (uniformity) earning
its first theorem-grade content.*

## What is proved

- **The animal bound, from owned geometry.**
  `animal_bound_729` — the number of connected
  column-supports of size n through a fixed column is
  at most **729ⁿ**, where 729 = 27² and 27 is the proved
  envelope bound on the column graph (degree ≤ 26,
  Part 1). Route: removable-vertex induction with a
  spanning closed step-walk of length 2n − 2, counted
  against the envelope. KL-1 (named-hypothesis fallback)
  was not needed — the bound is a theorem.
- **The Kirkwood–Salsburg / Kotecký–Preiss criterion,
  unconditional.** `ks_criterion_full` — for even N and
  continuous ρ, whenever |β| < **β₀ = (1/2)·ln(1 +
  1/(2·729·e))**, the per-column cluster sum is ≤ 1:
  the polymer activity series converges absolutely with
  a radius that depends on **nothing** — no N, no
  volume, no representation data (KL-2 checked and
  cleared; β₀ > 0 proved, `beta0_pos`, KL-3 cleared).
  The constants are the proved ones: the progress
  file's design estimates (degree ≤ 20, animal 441)
  stand superseded on the record by 26/729.
- The engine is LOC-1's landed majorant (2|β|)ᵏ/k! —
  the false (2β/d)ᵏ/k! form stays dead — summed per
  support by the degree-sum identity (e^{2|β|} − 1)^|S|.

## The named seam (Part 4, PARTIAL as pre-registered)

Convergence is proved for the **per-column activity
series itself**. The corpus has no polymer-gas
partition-function object, no `log Z` cluster-series
object, and no abstract KS implication (KP bound ⇒
log Z analytic) — so this brick does **not** yet say
the layer's free energy is analytic in β. LOC-3 is
priced accordingly: (i) a `Z_polymer` object over a
layer; (ii) a bridge theorem identifying log of the
layer weight with the polymer sum; (iii) the KS
implication brick transporting this criterion to
analyticity of that logarithm.

## Where this sits

Uniformity was the named absence on the frontier gate
("no spacing, no tuning/RG curve, no continuum
object"). The spacing side now has its first theorem:
a volume-uniform convergence radius for the activity
series at every finite volume simultaneously. That is
Dial 3's road (limits that don't degenerate as the box
grows) — it derives no measured number (Dial 1
unmoved) and builds no continuum object. NO CLAIM;
dials 0/4.

## Census effect

Strict 6,457 → **6,492**; attribute-inclusive 6,535 →
**6,570**; modules 224 → **225**; placeholders unchanged
at **7**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands
as recorded in `BACKERS.md`. Every gift is published with
the proof stream, named as the giver wishes, amounts only
with the giver's permission — the standing reciprocity of
this house.
