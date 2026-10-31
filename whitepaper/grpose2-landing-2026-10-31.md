# GR-POSE-2 — LANDED FULL: the fluctuation-response law (the pose line completes)

**Verdict: GR-POSE-2 FULL — `PoseVarA` is discharged constructively, with named coefficients, both first variations as `deriv` theorems, and the degeneracy boundary named on the face. THE GRAVITY POSE LINE IS COMPLETE (pin, decision, response). CEILING, restated at its pinned grade: this is the finite shadow of the variational pose — a proved response law of the finite action's numbers under finite fluctuation along the pin's named path. It seats NO gravity object, and Dial 2 = 0 under every outcome of the line, including its complete success. The chair's emptiness is now itemized and, for the decision's class, proved — that is the line's whole buy, per its section-0 fence. NO CLAIM. Dials 0/4.**

## The response law (`GravityPoseResponse.lean`)

The pin's path is affine: `poseVarAPath_eq : poseVarAPath P t = poseVarAD0 P + (t:ℂ) • poseVarACoeffOp P`, where `poseVarAD0 P = smDirac P.yNu P.yE P.yU P.yD P.yR` and the coefficient operator is read off the landed construction (`fluctuatedDirac D_F A = D_F + A + oppositeOneForm A`): `poseVarACoeffOp P = P.oneForm + oppositeOneForm P.oneForm`. Hence, for all real `t`:

- **M2:** `poseVarA_trace_sq` — `trace ((poseVarAPath P t)^2) = c0 + c1 t + c2 t^2` with `c0 = tr(D0^2)`, `c1 = tr(D0·B + B·D0)`, `c2 = tr(B^2)`; `poseVarA_discharged : PoseVarA P` with exactly these witnesses.
- **M0:** `poseVarA_M0` — the trace of the zeroth power is 32 for all `t` (the dimension, constant).
- **M1:** `poseVarA_M1` — affine, `tr(D0) + (2 · tr P.oneForm) · t` (`poseVarA_M1_slope`: the slope is exactly `2 * trace P.oneForm`, via `trace_oppositeOneForm`). The slope vanishes exactly on the traceless-one-form locus — a named locus, stated not narrowed; **the M2 law does not flip there** (its coefficients are independent traces; `c1`/`c2` vanish only in the zero-form case below). Recorded here as disclosed boundary behavior, K-GR-STAB-aware: no flip of the headline law was found, and nothing was repaired.
- **First variations (the response law in `deriv` form):** `poseVarA_firstVariation_M2 : deriv (fun t => trace ((poseVarAPath P t)^2)) 0 = poseVarAC1 P`; `poseVarA_firstVariation_M1 : deriv (fun t => trace (poseVarAPath P t)) 0 = poseVarAM1C1 P` — agreeing with the coefficient read-backs.

## The boundary, as named on the module's face

The law is about trace functions of the defined matrix family, for all real `t`. Class membership is asserted only where landed results reach: `t = 1` restated from the pin (`poseVarA_boundary_one_orderOne`, `poseVarA_boundary_one_selfAdjoint`) and `t = 0` (`poseVarA_boundary_zero`). The algebraic one-form class's closure under scaling is explicitly NOT landed and NOT claimed. Named degenerate case, proved: `poseVarA_zeroForm_degenerate` — if `P.oneForm = 0` the coefficient operator and all response coefficients vanish and the path is constant at `D0`.

## BRIDGE-1 cross-check (BR1-017)

Mandatory for this brick; **AGREEMENT** in exact rational arithmetic at a matrix-level (n = 4) instance of the same `fluctuatedDirac` construction — the level stated precisely in the registry entry (not the 32×32 seat; the construction and trace identities are size-independent, and the Lean formulas quantify over any one-form; no algebraic-one-form condition is checked at this level; M0 = 4 at this level against the seat's 32). Python instance: c0 = 3377/720, c1 = 179/7, c2 = 1315729/88200; M1 const 17/12, slope 353/210 = 2·tr(A); direct evaluations at seven exact `t` values agree with the affine/quadratic forms throughout, and an independent quadratic fit reproduces (c0, c1, c2) exactly. Registry: `whitepaper/cross-check-registry.md`, entry BR1-017.

## Kills audit for the completed line

K-GR-VAC: never fired (PoseObjU registered with its grade). K-GR-SMUG: never fired (noun audits clean at all three bricks; the path parameterized rather than invented). K-GR-LAUNDER: never fired (ceilings kept at pinned grades in every dossier, including this one). K-GR-STAB: no undisclosed flip — the disclosed boundaries are the t ∈ {0, 1} class-membership reach, the unlanded scaling closure, the traceless-one-form M1 locus, and the zero-form degeneracy, all on the faces. K-GR-BUY: never fired — no landing in this line was described as seating or warming the chair, and none does.

## Parent verification (from disk)

- Canonical counter: **strict=15, defs=7** (inside the M estimate ~20–45 by the house rule — defs are not counted in the strict figure; total declarations 22); zero attribute-prefixed declarations, zero "sorry"/`native_decide` tokens; the frozen pin modules unedited.
- Parent module build green, independently reproduced.
- Parent axiom check: `poseVarA_discharged`, `poseVarA_trace_sq`, `poseVarA_firstVariation_M2`, `poseVarA_firstVariation_M1`, `poseVarA_zeroForm_degenerate` each on exactly `[propext, Classical.choice, Quot.sound]`.

## Census

9,971 → **9,986 strict** / 10,049 → **10,064 attribute-inclusive** / 334 → **335 modules** (delta +15 strict, +1 module). README badge and body both updated at this landing and verified against the committed README.

## Backers since last landing

No change to the backer roll since the last landing.
