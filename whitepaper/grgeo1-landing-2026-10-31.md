# GR-GEO-1 — LANDED FULL: the cube graph is connected, and `geoDist` is the ℓ¹ cyclic sum (proved of `SimpleGraph.dist` at every N — the N = 2 watch does not fire)

**Verdict: GR-GEO-1 FULL. Both of the pin's registered targets are discharged at the pin's full generality: `(cubeGraph N).Connected`, and `geoDist N x y = ∑ i : Fin 4, cycDist N (x.1 i) (y.1 i)` — the ℓ¹ formula as a theorem about Mathlib's graph distance, exactly as the pin registered it (never the definition). The K-GR-STAB instance (iii) watch — a wrap failure at boundary N — does NOT fire: the proof is uniform in N, and the boundary behavior is recorded below and on the module's face. PROGRAM CEILING: finite combinatorics — seats NO gravity object; Dial 2 = 0 under every outcome. NO CLAIM. Dials 0/4.**

## What landed (`LayerCubeDistance.lean`, against the frozen pin)

- **`cubeGraph_connected : CubeGraphConnected N`** and **`geoDist_l1_formula : GeoDistL1Formula N`**, for general `N` with the pin's `[NeZero N]`.
- Proof shape: adjacency read off the landed head/tail data moves exactly one spatial coordinate by one cyclic step. Upper bound: a step-closer walk — move one differing coordinate along its shorter wrap arc (toward-step identities from `ZMod.val` arithmetic) — plus induction on the sum, giving a walk of exactly the formula's length (connectedness is its reachability half). Lower bound: per edge the ℓ¹ sum changes by at most 1; induction on walks, applied to the shortest walk from `SimpleGraph.Connected.exists_walk_length_eq_dist`.
- The module's one def is an auxiliary abbreviation for the formula's right-hand sum — not a distance definition; `geoDist` remains the pin's citation of `SimpleGraph.dist`, and the formula is proved *of* it (K-GR-SMUG (iv) respected in the landing's form).

## Boundary behavior (K-GR-STAB (iii), reported as required)

The formula does not fail at any boundary seat, and no quantifier was restricted anywhere:

- **N = 1:** the site type is a singleton; both sides are 0 (the differing-coordinate case is vacuous).
- **N = 2:** forward and backward wrap steps coincide; `cycDist` values are 0/1 and the step bounds and toward-step identities hold as proved for all N at once. No pair behaves specially; no differently-named restricted theorem was needed; the pin's targets stand as registered.

## Parent verification (from disk)

- Canonical counter: **strict=25, defs=1** (top of the S–M estimate 12–25); zero attribute-prefixed declarations, zero "sorry"/`native_decide` tokens; the pin module and all landed files unedited.
- Parent module build green, independently reproduced (3,669-job closure).
- Parent axiom check: `cubeGraph_connected`, `geoDist_l1_formula` each on exactly `[propext, Classical.choice, Quot.sound]`.

## Census

10,093 → **10,118 strict** / 10,170 → **10,195 attribute-inclusive** / 341 → **342 modules** (delta +25 strict, +1 module). README badge and body both updated at this landing and verified against the committed README.

## Backers since last landing

No change to the backer roll since the last landing.
