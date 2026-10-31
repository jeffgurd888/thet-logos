# GR-POSE-0 — LANDED FULL: the gravity pose pin (the chair's questions, itemized; no object seated)

**Verdict: GR-POSE-0 FULL. The gravity pose line's interface is frozen as its own verified commit. The pin registers the four poses with their scoping grades and ceilings, the two unstatable poses as named absences, the decision's (class, predicate) pair verbatim, and the fluctuation path as a frozen parameterized family. SECTION-0 FENCE, restated on this dossier's face: the strongest landing this line could ever produce is a proved map of which gravity questions the corpus can and cannot pose; it seats NO gravity object, and Dial 2 = 0 under EVERY outcome of this line, including total success — including this landing. NO CLAIM. Dials 0/4.**

## What the pin registers (`GravityPosePost.lean`, new module; working label — Jeff names)

- **Discharged poses (the control cases):** `PoseVarR` (P-var-R, CLOSED — SA-FLIP-1's affine law IS the R-slot response; read-back `poseVarR_discharged` = the landed `seely_dewitt_a2_affine`) and `PoseCoef` (P-coef, CLOSED — `PoseVarR ∧ a2GravCoeff ≠ 0`; `poseCoef_discharged`). The stability split is on both faces: the coefficient's nonvanishing is convention-robust; its value is convention-carrying.
- **`PoseObjU`** (P-obj-U, STATABLE / VACUITY-ADJACENT): the sector-independence statement, with its vacuity grade adjacent in the same docstring — a definitional remark, not evidence; the read-back is named `poseObjU_definitional_readback` and its docstring exhibits the vacuity (the landed affine law applied twice; the constant takes no sector argument). K-GR-VAC does not fire: the pose is registered WITH its grade, never as a satisfiable predicate offered as evidence.
- **Named absences (no inhabitant supplied, no pose statement):** `PoseObjF` — the field-law pose is unstatable: it needs an owned spatial separation carrying a 1/r² law; Connes distance is named on the face as state-space distance, NOT spendable as `r` (K-GR-SMUG fence). `PoseObjB` — the bending pose is unstatable today: it needs a propagation object; `maxwellOp` is code-cited (`poseObjBNearestNeighbor`) and named as what it is — a registered finite static quadratic form — not the missing object.
- **`PoseVarA`** (P-var-A, SURVIVES-reduced): the response pose registered unasserted — there exist coefficients `c0 c1 c2 : ℂ` with `∀ t, trace ((poseVarAPath P t)^2) = c0 + c1 t + c2 t^2` — with GR-POSE-2's task and the brick's ceiling (the finite shadow of the variational pose) on its face.
- **The frozen decision pair:** `PoseKillClassC` (C = functionals factoring through the finite spectral data alone; read-back `poseKillClassC_iff`: membership ↔ R-independence), `PoseKillGravC` (ClassC ∧ affine R-response at the landed slope `a2GravCoeff`), and `PoseKill` itself — registered, **not proved, not asserted** (`poseKill_unfold`, `gilkeyA2_response_readback`). GR-POSE-1 builds against exactly these names.
- **The frozen path — PARAMETERIZED, with the reason on the face:** the landed fluctuation vocabulary (`fluctuatedDirac`, order-one preservation, the smDirac instance) determines the construction but names no fixed self-adjoint one-form to scale; choosing one would invent vocabulary to force uniqueness (K-GR-SMUG). The path is therefore the frozen family `poseVarAPath (P : PoseVarAPathData) t := fluctuatedDirac (smDirac ...) ((t:ℂ) • P.oneForm)`, `PoseVarAPathData` carrying the Yukawa parameters, the one-form, and its algebraic/self-adjoint fields as labeled pin fields. Boundary disclosure (K-GR-STAB / OP-1 lesson): read-backs are proved at `t = 0` (the path is the unfluctuated `smDirac`) and `t = 1` (exactly the landed fluctuated Dirac; order-one and self-adjointness via the landed theorems); for general `t` nothing is asserted — no landed theorem states the one-form class is closed under scaling — and the zero-one-form constant-path degeneracy is disclosed on the face.

## Noun audit (part of the brick, parent-noted)

Case-insensitive grep of the module for the fenced vocabulary: 7 hit lines — the header ceiling-fence list itself; `1/r^2` inside the PoseObjF named-absence docstring; `propagation` ×2 inside the PoseObjB named-absence docstring; `curvature` inside the frozen-pair registration where the memo's own GRAV_C wording is quoted under that section's fence. Every hit sits inside a named-absence registration or a ceiling fence. **K-GR-SMUG does not fire.**

## Parent verification (from disk)

- Canonical counter: **strict=11, defs=9** (inside the S estimate ~8–16), plus 3 registration structures; zero attribute-prefixed declarations, zero "sorry"/`native_decide` tokens; no landed file edited.
- Parent module build green, independently reproduced.
- Parent axiom check: all 11 read-back theorems on exactly `[propext, Classical.choice, Quot.sound]`.

## Census

9,952 → **9,963 strict** / 10,030 → **10,041 attribute-inclusive** / 332 → **333 modules** (delta +11 strict, +1 module). README badge and body both updated at this landing and verified against the committed README.

## Backers since last landing

No change to the backer roll since the last landing.
