# REM-1 — LANDED FULL: the teeth are exact at N = 4, and `RemNaiveClosure` is KILLED at theorem grade — a K-GR-STAB finding, reported as the finding

**Verdict: REM-1 FULL — both decisions landed at the frozen seat (Even N, N = 4). (1) The single-plaquette excitation's angle is exactly its own value: `plaqAngle remSeatPlaq (singlePlaqExcitation remSeatPlaq t) = t` for every `t : ℝ` — balance can fail locally, by an exact amount, at a named plaquette. (2) `RemNaiveClosure` is DEAD at theorem grade: `remNaiveClosure_four_not : ¬ RemNaiveClosure 4`. The constant direction field is flat at every plaquette yet is not a gradient — its direction-1 wrap holonomy is exactly 4 at every base site, while every gradient's wrap holonomy telescopes to 0. This is the K-GR-STAB finding the pin registered in advance: flatness does not imply pure gauge on this base — the base carries a global remainder no plaquette can see. The seat was not narrowed to hide it; the counterexample's uniformity in N ≥ 2 is stated on the module's face labeled scoping-grade (the N = 4 theorem is the kill). Honest landing sentence, as registered: "On the finite base, balance can fail locally with an exact value at a named plaquette, and flatness does not imply pure gauge — the base carries a global remainder no plaquette can see." Finite seat values testify about finite seats (K-GR-LAUNDER). Dial 2 = 0, Dial 3 = 0. NO CLAIM.**

## What landed (`LayerCubeRemainderSeat.lean`)

- Decision 1: `remSeat_excitation_angle` (+ the general `plaqAngle_singlePlaqExcitation` at Even N, 4 ≤ N, any datum) via the landed edge-distinctness lemmas; corollary: the defect field attains exactly `t ≠ 0` at the seat plaquette. The seat-kill form (excitation angle = 0) did not occur.
- Decision 2: `constDirField` defined exactly; `plaqAngle_constDirField` (flat at every plaquette datum), `constDirField_flat_four` (the `allPlaqData 4` form), `wrapHolonomy1_constDirField` (= 4 at every base site), and the kill `remNaiveClosure_four_not`.
- **The telescoping lemma, in the general form REM-2 consumes:** `wrapHolonomy_gaugeAngle {N} [NeZero N] (φ : LayerSite N → ℝ) (ν : Fin 4) (hν : ν ≠ 0) (c) : wrapHolonomy (gaugeAngle φ) ν hν c = 0`, backed by the induction-form sum telescope and the coordinate formula for iterated `layerShift` (`(layerShift ν hν)^[N] c = c`).

## BRIDGE-1 (registry BR1-019)

Exact `Fraction` arithmetic, no floats: the seat plaquette's four edges pairwise distinct as link data; excitation angle = t exactly at t ∈ {0, 1, −3/2, 7/3}; the constant direction field flat at all 192 enumerated plaquettes; its direction-1 wrap sum = 4 at every base site; gradient wrap sums telescope to exactly 0 at all base sites in all three directions. **ALL PASS.**

## Parent verification (from disk)

- Canonical counter: **strict=20, defs=4** (inside the S–M estimate 12–25); zero "sorry"/`native_decide` tokens; the REM-0 pin and MAX/Plaquette modules unedited.
- Parent module build green, independently reproduced.
- Parent axiom checks: `remNaiveClosure_four_not`, `remSeat_excitation_angle`, `wrapHolonomy_gaugeAngle` — each on exactly `[propext, Classical.choice, Quot.sound]`.

## Census

10,311 → **10,331 strict** / 10,388 → **10,408 attribute-inclusive** / 348 → **349 modules** (delta +20 strict, +1 module). README badge and body both updated at this landing and verified against the committed README.

## Backers since last landing

No change to the backer roll since the last landing.
