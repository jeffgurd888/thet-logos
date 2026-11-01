# GR-DIST-1 — LANDED FULL: the general theory of `connesDist` (all five rows discharged; the finiteness criterion closed in both directions — the pre-named seam did not hold)

**Verdict: GR-DIST-1 FULL. The pin's entire axiom table is now theorem: the three general rows hold unconditionally, both conditional rows are discharged in their registered conditional forms, and the commutant finiteness criterion is proved as a full iff at the pin's full generality — its hard direction (⇐), pre-named as this brick's PARTIAL seam, CLOSED with no restriction of the seat, the type, or the operator. Plus the scaling sanity law and the zero-operator degeneracy, the latter worded as a finding. PROGRAM CEILING, on this dossier's face: vocabulary-grade theory of a finite state-space distance — it seats NO gravity object; Dial 2 = 0 under every outcome. `connesDist` is a distance between states, never a spatial `r`. NO CLAIM. Dials 0/4.**

## What landed (`ConnesDistanceTheory.lean`, against the frozen pin)

- **General rows:** `connesDistDiagZero_proved : ConnesDistDiagZero D` (via `connesDist_self`); `connesDistSymm_proved : ConnesDistSymm D` (term-wise `norm_sub_rev`); `connesDistTriangle_proved : ConnesDistTriangle D` — the extended triangle inequality in ℝ≥0∞, via `ENNReal.ofReal_add` and supremum subadditivity, on the term bound `ofReal_norm_sub_le_connesDist`.
- **The criterion, both directions:** (⇒) `connesDist_eq_top_of_hasCommutantObstruction` — the obstruction element, scaled, keeps commutator 0 while its separation grows without bound, forcing the distance to ⊤. (⇐) `connesDist_lt_top_of_no_obstruction` — from `exists_norm_sub_le_of_no_obstruction`: with no obstruction at `(i, j)`, the point-difference form vanishes on the intersection of the finitely many commutator coordinate kernels, so the pin's `mem_span_of_iInf_ker_le_ker` puts it in their span; each commutator entry is bounded by the ℓ² operator norm, giving a concrete constant `C = ∑ p, ‖c p‖` with `‖a i − a j‖ ≤ C * ‖commDiag D a‖` for all `a` — finiteness. Assembled: **`connesDist_eq_top_iff_hasCommutantObstruction : connesDist D i j = ⊤ ↔ HasCommutantObstruction D i j`**, and row 5 as `connesDistFiniteConditional_proved` (the same seam, stated once, as registered).
- **Definiteness, conditional form:** `connesDistDefiniteConditional_proved` — under `ConnesCommSeparates D`, distance 0 forces `i = j`.
- **Scaling law:** `connesDist_smul : connesDist (c • D) i j = (ENNReal.ofReal c)⁻¹ * connesDist D i j` for real `c > 0` (the real scalar action read entrywise through `(c : ℂ)`), by the two inequalities and `ENNReal.inv_mul_cancel`.
- **Degeneracy, as a finding:** `connesDist_zero_eq_top_of_ne : i ≠ j → connesDist (0 : Matrix ι ι ℂ) i j = ⊤` — at the zero operator every pair of distinct states is at infinite distance (witness `Pi.single i 1` obstructs). Worded on the module's face as a K-DIST-DEG degeneracy finding — the extended trivial distance — never as a metric success.

## Parent verification (from disk)

- Canonical counter: **strict=25, defs=2** (inside the M estimate 20–40); zero attribute-prefixed declarations, zero "sorry"/`native_decide` tokens; the pin module and all landed files unedited.
- Parent module build green, independently reproduced (3,266-job closure).
- Parent axiom check: `connesDistDiagZero_proved`, `connesDistTriangle_proved`, `connesDist_eq_top_iff_hasCommutantObstruction`, `connesDistDefiniteConditional_proved`, `connesDistFiniteConditional_proved`, `connesDist_smul`, `connesDist_zero_eq_top_of_ne` each on exactly `[propext, Classical.choice, Quot.sound]`.

## Census

10,068 → **10,093 strict** / 10,145 → **10,170 attribute-inclusive** / 340 → **341 modules** (delta +25 strict, +1 module). README badge and body both updated at this landing and verified against the committed README.

## Backers since last landing

No change to the backer roll since the last landing.
