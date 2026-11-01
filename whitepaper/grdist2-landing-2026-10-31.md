# GR-DIST-2 — LANDED FULL, with a value-form FINDING at full rank: at the Fin 4 cycle seat the Connes distance is the DISCRETE metric — finite, definite, separating — and the constant × cyclic-distance form is DISPROVED at this seat

**Verdict: GR-DIST-2 FULL. Finiteness and definiteness at the seat are proved, and the distance's exact value is computed: `connesDist cycleDirac i j = if i = j then 0 else 1` (the discrete metric, ENNReal literals). FINDING, reported at the same volume: the value is NOT the scoping memo's anticipated "cyclic graph distance times a base constant" — that form is disproved at this seat by theorem (`not_exists_const_mul_cycDist4`: adjacent pairs force the constant to 1, opposite pairs force it to 1/2). The operator kept its natural unrescaled normalization; nothing was renormalized to rescue the anticipated form. The honest reading at the pinned grade: the corpus's first Lean Connes distance is axiom-complete at its first seat — and its metric there is COARSE (every two distinct points are distance 1 apart). That coarseness is a property of the seat, proved, and it is the fact DIST-3's decision inherits. No pair degenerates (no 0 or ∞ between distinct points), so K-DIST-DEG does not fire. PROGRAM CEILING: vocabulary — seats NO gravity object; Dial 2 = 0 under every outcome. NO CLAIM. Dials 0/4.**

## What landed (`ConnesDistanceCycle.lean`)

- **Seat operator:** `cycleDirac = shiftMat + shiftMatᴴ` — the 4-cycle adjacency (entries exactly 1, unrescaled), proved to act as both landed shifts (`z4ShiftOp`, `shiftC4C`), self-adjoint, packaged as `cycleSeat : ConnesDistanceSeat (Fin 4)`.
- **Finiteness FULL:** a diagonal element commuting with `cycleDirac` is constant (successor entries of the commutator), so no commutant obstruction exists at any pair — `connesDist_cycleDirac_lt_top` via DIST-1's criterion.
- **Definiteness FULL:**two explicit arc-indicator witnesses whose commutators are signed permutation matrices (operator norm ≤ 1 via the C-star identity) with point-difference norm exactly 1 on the pairs they cover — `ConnesCommSeparates cycleDirac`, hence definiteness via DIST-1's discharge.
- **Value:** the upper bound is sharp for every pair (adjacent: a single commutator entry via DIST-1's entry bound; opposite: a unit-pairing argument `⟨u, [D,a] v⟩ = 2(a 2 − a 0)` with even/odd probe vectors). Comparability bounds proved alongside the exact value: `(1/2)·cycDist4 ≤ connesDist ≤ 1·cycDist4` in `ENNReal.ofReal` form, `cycDist4` the locally defined Fin 4 cyclic distance (GEO's `cycDist` lives on `ZMod 4`; the coincidence is noted on the module's face).

## BRIDGE-1 (registry BR1-018)

Formula/obstruction grade vs the corpus's T4 Python Connes distance (engine13; seats differ — density states over the 32-dim triple vs point evaluations on Fin 4 — no same-seat numeric equality claimed). (a) Formula grade: an independent Python evaluation of the same supremum at this seat reproduces the Lean values on all 16 pairs — 0 diagonal, 1 at every distinct pair, including opposite pairs — independently confirming the discrete value and the non-proportionality. (b) Obstruction grade: D = 0 at pair (0,1) on the small seat returns `inf`; engine13's own seat at its designed dead-sector pair returns `inf` — both matching DIST-1's proved criterion. Disclosed in the registry: an engine13 D = 0 instance returned 0.0 through a degenerate SVD-cutoff path; the designed kernel-separated pair was used instead. **PASS.**

## Parent verification (from disk)

- Canonical counter: **strict=41, defs=10** (inside the M estimate 25–45); zero "sorry"/`native_decide` tokens; pin and DIST-1 theory unedited.
- Parent module build green, independently reproduced.
- Parent axiom checks: `connesDist_cycleDirac_eq`, `not_exists_const_mul_cycDist4`, `connesDist_cycleDirac_lt_top`, `connesDistDefiniteConditional_cycleDirac`, `cycleDirac_selfAdjoint` — each on exactly `[propext, Classical.choice, Quot.sound]`.

## Census

10,118 → **10,159 strict** / 10,195 → **10,236 attribute-inclusive** / 342 → **343 modules** (delta +41 strict, +1 module). README badge and body both updated at this landing and verified against the committed README.

## Backers since last landing

No change to the backer roll since the last landing.
