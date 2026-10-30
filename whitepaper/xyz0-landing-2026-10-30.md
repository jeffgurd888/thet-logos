# XYZ-0 — gate confirmed; the tripotent campaign restated against the converted Prop

**Date:** 2026-10-30 · **Brick:** XYZ-0 (S, gate/registration,
no proof content), per
`scoping-xyz-tripotents-2026-10-30.md`. **Verdict: GATE
CONFIRMED.** The hard gate — SORRY-0-CONVERT landed, so the
target exists only in converted form — is satisfied and
verified on disk.

**Fences: NO CLAIM. Parts of any official statement closed: 0.
Dials: 0/4.** The question below is genuinely OPEN. "Failure
to find is not a kill" governs every brick of this line: only
the pre-registered kills (K-XYZ-1, an invariant obstruction of
the question; K-XYZ-2, exhaustion of a named family) close
anything, and they close different things.

## The target, verbatim from the tree

`ThetLogos.XYZTripotents` (line 489), converted by
SORRY-0-CONVERT from a sorry-post to a stated proposition:

```
def xyz_tripotents_exist : Prop :=
    ∃ X Y Z : Matrix I32 I32 ℂ,
      Tripotent X ∧ Tripotent Y ∧ Tripotent Z ∧
      ∀ g : Fin 12, MemGenTRO ({X, Y, Z} : Set (Matrix I32 I32 ℂ)) (smGen g)
```

Three tripotents in M₃₂(ℂ) whose generated ternary ring
contains all twelve `smGen` generators. Stated, unproved,
unrefuted.

## What is already proved around it (the fences, T1)

- **No diagonal triple works** (`no_diagonal_xyz_tripotents`):
  a diagonal triple generates only diagonal matrices;
  `smGen 1` is off-diagonal.
- **The sector-projection triple fails**
  (`sector_triple_fails`): (cfMat, 1 − cfMat, 1) are all
  tripotents and all diagonal — dead by the first fence.
- **Conjugation does not escape**: diagonal-unitary and
  UJ-conjugation preserve diagonality
  (`triple_gammaF_UJconj_one_fails`).
- **Single-sector triples are trapped** by the support
  invariant (`triple_genH_cannot_reach_genM`): a viable
  triple must mix sectors.
- **The screening rubric R1–R5** (module §12) is the standing
  intake: a candidate failing any rule is dead on arrival.
- **Partial positive on the record**: 1 of 12 generators is
  reached by the best documented candidate family — the
  distance to 12 is the campaign.

## The priced path from here

- **XYZ-1** (S–M): the named-pool family kill — every triple
  drawn from the 16 named tripotents fails at `smGen 11`
  (R5 assembly). Lands as **K-XYZ-2** (a family kill: the
  pool is dead; the question is not).
- **XYZ-2** (M): the boundary marker — one explicit tripotent
  with a 1/√3 entry (rank-one partial isometry from a
  triplet-normalized vector), the theorem that XYZ-1's
  species cannot extend to the question. A kill of the
  kill-route, recorded at the same volume as a win.
- **XYZ-3** (M): the first live family — {UJ, genH k,
  genM a (a ≠ 7)} × {XYZ-2 partial isometries and their
  conjugates/permutations}, exact word-closure search to
  depth ≤ 2 under BRIDGE-1, Lean certification of any find
  inside the brick. Outcomes pre-registered: 12/12 ⇒ promote
  (XYZ-5 territory); partial ⇒ scoreboard record; exhausted
  ⇒ K-XYZ-2 at the stated depth and list. **XYZ-3's outcome
  is reported out of band.**
- **XYZ-4 (L) and XYZ-K1 (M–L) are NOT queued**: they
  schedule only on XYZ-3's reported outcome, by parent
  decision.

**Census unchanged: 8,033 strict / 8,111 attribute-inclusive /
271 modules** (a gate/dossier brick lands no Lean).

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you to
everyone reading the stream — the corpus is free for everyone,
forever.

*End of dossier.*
