# XYZ Tripotent Campaign — Final Results (2026-09-28)

**Status: PARTIAL — banked, local only. Not committed, not pushed.**

Question: do three tripotent 32×32 matrices generate all twelve Standard-Model
generators (`smGen 0–11`) under ternary products? The campaign ran four waves of
Lean 4 attacks on 2026-09-28 and is now banked. This document is the ledger.

All work lives in `lean/ThetLogos/XYZTripotents.lean` (local, untracked).

---

## 1. The open statement (verbatim)

```lean
theorem xyz_tripotents_exist :
    ∃ X Y Z : Matrix I32 I32 ℂ,
      Tripotent X ∧ Tripotent Y ∧ Tripotent Z ∧
      ∀ g : Fin 12, MemGenTRO ({X, Y, Z} : Set (Matrix I32 I32 ℂ)) (smGen g) := by
  sorry
```

**Success criterion:** exhibit explicit tripotent matrices X, Y, Z such that every
`smGen g` (g : Fin 12) lies in the ternary-generated set `MemGenTRO {X, Y, Z}`.

**Failure criterion:** prove that no such triple of tripotents exists.

**Neither was achieved.** The `sorry` stands. Verdict: **PARTIAL** (see §5).

---

## 2. Inventory of proved tripotents (grep-verified names)

Each of the following is a machine-checked `Tripotent` proof in
`XYZTripotents.lean`:

| Theorem | Matrix | Idea |
|---|---|---|
| `tripotent_zero` | 0 | zero matrix |
| `tripotent_one` | 1 | identity |
| `tripotent_of_isProj` | any orthogonal projection | p² = p, pᴴ = p |
| `tripotent_cfMat` | `cfMat` | charge-conjugation flip matrix |
| `tripotent_one_sub_cfMat` | `1 − cfMat` | complementary projection |
| `tripotent_gammaF` | `gammaF` | grading operator |
| `tripotent_UJ` | `UJ` | real-structure unitary |
| `tripotent_UJ_conj` | `UJ * D * UJ` (D diagonal tripotent) | conjugation preserves tripotents |
| `tripotent_diagonal` | diagonal, entries ∈ {0,1} | 0/1 diagonal |
| `tripotent_diagonal_normSq` | diagonal, entries on unit circle | \|d\| = 1 diagonal |
| `tripotent_genC` | `genC` | diagonal ±1/0 |
| `tripotent_genH` | `genH k`, all k : Fin 3 | **new, fourth wave** |
| `tripotent_genM0` | `genM 0` | **new, fourth wave** |

New supporting lemmas (fourth wave): `tripotent_of_hermitian_sq_proj`
(uniform criterion: Hermitian + square a 0/1 support projector ⇒ tripotent),
`pauli_herm`, `genH_herm`, `genH_sq_diag`, `gellMann_zero_sq`,
`genM_zero_sq_diag`, `genM_seven_diagonal`, `genM_seven_diag_form`.

**Negative (also proved):** `not_tripotent_genM7` — `genM 7` is *not* a
tripotent. It is diagonal with the entry 1/√3 at (18,18), and the scalar
tripotent equation forces 1/√3 = (1/√3)³, i.e. (√3)² = 1, i.e. 3 = 1 —
contradiction. This closes the "irrational tripotent inside the natural pool"
escape from rubric R5.

---

## 3. The no-go rubric (R1–R5 + §16 kill)

| Rubric | Theorem(s) | Plain-language reason |
|---|---|---|
| **R1 diagonal trap** | `no_diagonal_xyz_tripotents`, `sector_triple_fails` | A diagonal triple's ternary products stay diagonal, but `smGen 1` is off-diagonal. The natural candidate `{cfMat, 1−cfMat, 1}` is provably dead. |
| **R2 conjugation trap** | `triple_gammaF_UJconj_one_fails` | The triple `{gammaF, UJ·D·UJ, 1}` still cannot reach `smGen 1`; UJ-conjugation of a diagonal tripotent does not create the right off-diagonal support. |
| **R3 sector trap** | `triple_genH_cannot_reach_genM` | `{genH k}`-style generators live in the 8×8 H-block; their ternary products cannot reach the 12×12 M-sector generator `genM 0`. |
| **R4 pair-support trap** | `no_UJ_diagonal_pair_reach` | `{UJ, D1, D2}` with D1, D2 diagonal: ternary products keep a "paired" support shape that `smGen 1` violates. Kills `{UJ, genC, cfMat}` and `{UJ, gammaF, genC}` for `smGen 1`. |
| **R5 Gaussian-integer trap** | `no_gaussInt_triple_reaches_genM7` | Ternary products preserve the Gaussian integers ℤ[i]; `smGen 11 = genM 7` has the entry 1/√3 ∉ ℤ[i]. Any ℤ[i]-valued triple provably misses `smGen 11`. |
| **§16 irrational kill** | `not_tripotent_genM7` | `genM 7` itself is not a tripotent (diagonal, entry 1/√3, scalar tripotent equation fails). So the one generator with irrational entries cannot even serve as a tripotent leg. |

Supporting infrastructure: `memGenTRO_diagonal`, `memGenTRO_supported`,
`memGenTRO_pairSupport`, `memGenTRO_gaussInt`, `gaussInt_ternary`,
`gaussInt_matrix_mul`, `gaussInt_matrix_star`.

---

## 4. Machine-proved partial positives

Reachability is always *by a specific proved triple*, never claimed in general.
Generator map: `smGen 0 = genC`, `1 = genH 0`, `2 = genH 1`, `3 = genH 2`,
`4 = genM 0`, `5–10 = genM 1–6`, `11 = genM 7`.

| Theorem | Triple | Reaches |
|---|---|---|
| `triple_genC_UJ_gammaF_reaches_smGen0` | `{genC, UJ, gammaF}` | `smGen 0` |
| `triple_genH0_UJ_genM0_reaches_1_4` | `{genH 0, UJ, genM 0}` | `smGen 1`, `smGen 4` — **first triple to reach an off-diagonal generator** |
| `triple_genH_reaches_123` | `{genH 0, genH 1, genH 2}` | `smGen 1`, `smGen 2`, `smGen 3` |

Sharp boundaries proved alongside:

- `triple_genC_UJ_gammaF_cannot_reach_smGen1` — the `smGen 0` triple provably
  cannot reach `smGen 1`.
- `triple_genH0_UJ_genM0_misses_11` — the mixed triple provably misses
  `smGen 11` (by R5: `genH 0`, `UJ`, `genM 0` are all ℤ[i]-valued;
  `genH_gaussInt`, `UJ_gaussInt`, `genM_zero_gaussInt` proved).

Reachability table (rows = generators, columns = proved triples):

| gen | `{genC,UJ,gammaF}` | `{genH0,UJ,genM0}` | `{genH0,genH1,genH2}` |
|---|---|---|---|
| smGen 0 | ✅ proved | — | — |
| smGen 1 | ❌ proved miss | ✅ proved | ✅ proved |
| smGen 2 | — | — | ✅ proved |
| smGen 3 | — | — | ✅ proved |
| smGen 4 | — | ✅ proved | — |
| smGen 5–10 | — | — | — |
| smGen 11 | — | ❌ proved miss (R5) | — |

"—" means not proved either way. No single triple reaches more than three
generators; no triple reaches `smGen 5–10` or `smGen 11`.

---

## 5. Verdict: PARTIAL

**The existential `xyz_tripotents_exist` is OPEN.** The fourth wave broke the
`smGen 1` barrier — the exact gap named in the task — via the new tripotents
`genH k` and `genM 0`, and it closed the irrational-entry escape with
`not_tripotent_genM7`. But no triple reaches all twelve generators, and no
proof of impossibility was found either.

**Precise remaining statement:** the verbatim `xyz_tripotents_exist` above —
∃ tripotents X Y Z with all twelve `smGen g ∈ MemGenTRO {X, Y, Z}` — still
carries its `sorry`.

**Suggested next angle** (concrete, in priority order):

1. **`genM 1–6` tripotent status.** Each Gell-Mann matrix λ₁–λ₆ squares to a
   0/1 diagonal (same shape as λ₀: e.g. λ₁² = λ₂² = λ₃² = diag(1,1,0));
   `tripotent_of_hermitian_sq_proj` should promote all six with the same proof
   pattern as `tripotent_genM0`. If they are tripotents, triples like
   `{genM 0, genM 1, genM 2}` reach `smGen 4–6` by membership, etc.
2. **The `smGen 11` crux.** R5 forces any triple reaching `genM 7` to contain a
   non-ℤ[i] tripotent, and `not_tripotent_genM7` removes `genM 7` itself from
   the candidate pool. The search space is: non-diagonal, non-ℤ[i] tripotents
   (e.g. diagonal unit-circle phases are tripotents by
   `tripotent_diagonal_normSq`, but R1/R4 constrain diagonal legs; UJ-conjugates
   of `genH`/`genM` stay ℤ[i]-valued).
3. **Conditional completeness.** If (1) succeeds, bank the disjunction: every
   generator except `smGen 11` is reached by some explicit tripotent triple,
   and `smGen 11` is provably missed by every ℤ[i]-valued triple — isolating
   the existence question to a single precisely-stated gap.

---

## 6. Honesty ledger

- **Tiers:** T1 0 · T2 0 (definitions only: `genM0supp`, `Tripotent`,
  `MemGenTRO` predate this wave) · **T3: all new theorems proved** · T4 0 ·
  T5 1 (the single `sorry` below). No numerical evidence, no experiments, no
  physical devices involved.
- **The single `sorry`:** `xyz_tripotents_exist` (line 492), the open
  existential. It is the only `sorry` in the file.
- **`#print axioms`:** every new fourth-wave theorem
  (`tripotent_of_hermitian_sq_proj`, `pauli_herm`, `genH_herm`,
  `genH_sq_diag`, `tripotent_genH`, `gellMann_zero_sq`,
  `gellMann_zero_sq_diag01`, `gellMann_zero_sq_of_ne`, `genM0supp_eq`,
  `genM0supp_none`, `genM_zero_sq_diag`, `tripotent_genM0`,
  `genM_seven_diagonal`, `genM_seven_diag_form`, `not_tripotent_genM7`,
  `gaussInt_neg_one`, `gaussInt_I`, `gaussInt_neg_I`, `pauli_gaussInt`,
  `genH_gaussInt`, `gellMann_zero_gaussInt`, `genM_zero_gaussInt`,
  `UJ_gaussInt`, `triple_genH0_UJ_genM0_reaches_1_4`,
  `triple_genH0_UJ_genM0_misses_11`, `triple_genH_reaches_123`)
  depends only on the standard trio `[propext, Classical.choice,
  Quot.sound]`. **No new axioms.** `xyz_tripotents_exist` additionally
  depends on `sorryAx`, as expected.
- **Final build:** `lake build ThetLogos.XYZTripotents` — **completed
  successfully (3124 jobs)**, 2026-09-28. File: 1278 lines, 90
  theorem/lemma declarations (up from 953 lines / 65 on 2026-09-28 pre-wave).
- **Scope note:** `MemGenTRO` closes under *ternary* products only
  (`a·bᴴ·c`), not under linear combinations or ordinary products. All
  reachability claims above are ternary-reachability; nothing here implies
  linear-span or algebra generation.
- **What was NOT proved:** no triple reaching 2+ sectors simultaneously beyond
  the table in §4; no classification of all tripotents; `genM 1–6` tripotent
  status unproved (conjectured, §5.1); `smGen 11` reachability by *any* triple
  neither proved nor refuted — only the ℤ[i]-valued case is killed (R5).

**Local only: not committed, not pushed.**
