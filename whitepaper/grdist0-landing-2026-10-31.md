# GR-DIST-0 — LANDED FULL: the Connes-distance registration pin (the corpus's first Lean Connes distance, defined; axiom table at exact grades)

**Verdict: GR-DIST-0 FULL. The GR-DIST line's interface is frozen as its own verified commit: the seat data, `connesDist` as an ℝ≥0∞-valued supremum, the five-row axiom table registered at exactly the scoping's grades, and `DistSeparates` registered for the Fin 4 cycle seat against the corpus's own named sector pair. This pin proves nothing about any distance — it makes the distance a house object about which theorems can now be stated and proved. PROGRAM CEILING, on this dossier's face: vocabulary — it seats NO gravity object; Dial 2 = 0 under every outcome. NO CLAIM. Dials 0/4.**

## The annex correction, carried at full volume

This pin begins the corpus's first **Lean (T1)** Connes distance — NOT its first Connes distance. A T4 Python implementation (`python/thet_logos/engine13_rsd.py`, `connes_distance`, Engine 13, commissioned 2026-10-01) exists in the corpus's own tree and generates the macroscope's Connes-distance-dynamics instrument data. The vocabulary scoping memo's "no Connes material" sentence was false at T4 and stands corrected by its annex; GR-DIST-2's mandatory BRIDGE-1 cross-check targets that implementation at formula/obstruction grade (same supremum formula, same commutant-kernel → ∞ behavior; the seats differ — density states over the 32-dim triple vs point evaluations of a diagonal algebra — so no same-seat numeric equality is promised).

## What the pin registers (`ConnesDistancePost.lean`, new module; working label — Jeff names)

- **Seat data:** `ConnesDistanceSeat` — a finite type `ι` (`Fintype`), `D : Matrix ι ι ℂ` with the labeled field `D_selfAdjoint : IsSelfAdjoint D`; the diagonal algebra `diagAlg a = Matrix.diagonal a`; pure states as point evaluations `pointEval`. The commutative-seat restriction is stated on the face.
- **The definition:** `commDiag D a = D * diagAlg a - diagAlg a * D`; `connesDist D i j : ℝ≥0∞` = the supremum over `‖commDiag D a‖ ≤ 1` of `ENNReal.ofReal ‖a i - a j‖` — total by type before any finiteness is proved. The norm is the ℓ² operator norm, the choice named on the face.
- **The axiom table, at exact grades (no row asserted):** `ConnesDistDiagZero`, `ConnesDistSymm`, `ConnesDistTriangle` registered as GENERAL target Props (DIST-1's to prove); `ConnesDistDefiniteConditional` — CONDITIONAL on `ConnesCommSeparates D` (commutators separate every distinct pair); `ConnesDistFiniteConditional` — CONDITIONAL on the absence of `HasCommutantObstruction D i j` (an element commuting with D yet separating i from j). Proved content is pin-grade: 9 unfold/evaluation read-backs.
- **`DistSeparates`:** seat = the Fin 4 cycle (the concrete operator is DIST-2's gated construction; none invented here); sector pair = **the corpus's already-named pair, consumed as registered from `ChargePumpPost`: `chargePumpSectorA = {0, 1}` / `chargePumpSectorB = {2, 3}`** — cited on the face as that module's chosen rung grading, not a derived object. Registered form: positivity AND finiteness of `connesDist` on every cross pair, in both cross directions. The face records why the alternative was not used: `sectorC4` are submodules of the factor space, not subsets of the seat points, so they cannot index a point-state distance.

## Fences on the face

The DIST ≠ GEO fence (K-GR-SMUG instance (i)): `connesDist` is a distance between states of an algebra, never a spatial separation, never spendable as the `r` of a field law; this pin does NOT make `PoseObjF` statable (that is GR-GEO's job, finite shadow only); the two sub-lines may not cite each other as evidence. One stated yield: GR-POSE-0's fence (`GravityPosePost.lean:213/:225`) — whose ruling stands — acquires a real T1 referent. Kills on the face: K-GR-VAC, K-GR-SMUG, K-GR-LAUNDER, K-GR-STAB, K-GR-BUY, K-DIST-DEG. Noun audit: 7 hits, all inside fences or citations, none operative.

## Parent verification (from disk)

- Canonical counter: **strict=9, defs=12** (inside the S estimate 8–14), plus the seat structure; zero attribute-prefixed declarations, zero "sorry"/`native_decide` tokens; no landed file edited.
- Parent module build green, independently reproduced.
- Parent axiom check: `connesDist_unfold`, `distSeparates_unfold` on exactly `[propext, Classical.choice, Quot.sound]` (builder checked all 9 read-backs likewise).

## Census

10,039 → **10,048 strict** / 10,117 → **10,126 attribute-inclusive** / 337 → **338 modules** (delta +9 strict, +1 module). README badge and body both updated at this landing and verified against the committed README.

## Backers since last landing

No change to the backer roll since the last landing.
