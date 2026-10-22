# Q4 Path B — Sectoral Charpoly Factorization: STANDS WHOLE (2026-10-22)

**Commission:** Jeff, via Idea acceptance 2026-10-22 ~00:03 EDT — settle the
charpoly factorization lemma blocking the Q4 Path B entry of the mass-gap run:
either a compiled machine-checked proof or a dated kill verdict with the exact
obstruction pinned.

**Verdict: STANDS (T1), in a stronger form than the amendment worded it.**

## The claim

From the Q4 amendment filed 2026-10-05 in `ThetLogos/BlockedQuestions.lean`:
the sectoral decomposition of `charpoly(D_F)` from the gauge/color symmetry —
"the claim that it splits into sector polynomials of degree ≤ 4 in `λ²`" —
was named the load-bearing unproved lemma of Q4. Nothing of this form existed
in the codebase (verified by grep, 2026-10-05).

## What is proved

Module: `lean/ThetLogos/CharpolyFactor.lean`, namespace
`ThetLogos.CharpolyFactorization` — **34 strict theorems/lemmas, 7 defs**.

For the corpus's actual finite Dirac operator, `MartinettiRep.smDirac
yNu yE yU yD yR` on ℂ³², at **arbitrary** complex parameters:

- `charpoly_smDirac`: the charpoly factors over the eight mode classes
  `k : Fin 8` of the corpus's own support lemma (`smDirac_supp_aux`: D_F
  couples only indices with the same mode `k = i mod 8`):

      charpoly (smDirac …) = ∏ k : Fin 8, modeFactor … k

- `modeFactor_sq_form` + `modeBlock_charpoly`: each mode factor is a
  **biquadratic**,

      modeFactor k = X⁴ − C(2•|aₖ|² + |eₖ|²)•X² + C(|aₖ|⁴),

  a polynomial in X² of λ²-degree **≤ 2** — half the amendment's claimed
  bound of 4. Here `aₖ` is the sector Yukawa value at mode k and `eₖ` the
  mode Majorana value (`yR` at the two ν-modes, else 0). A biquadratic is
  radical-solvable, so the "closed form per sector" half of Path B is
  discharged in-machine.
- `charpoly_smDirac_grouped`: the eight modes group into the four Yukawa
  sectors, each with multiplicity 2.
- General machinery proved en route: `charpoly_blockDiagonal` (charpoly of
  a block-diagonal matrix is the product of the block charpolys),
  `charpoly_fromBlocks_zero` (charpoly of the chiral off-diagonal block
  matrix `[[0, P], [Q, 0]]` is the charpoly of `−(Q*P)` composed with X²,
  by a unit-determinant triangularisation), `charpoly_two_by_two`.

## Verification (parent, on the exact shipped text)

- Independent recompile of the candidate bytes before shipping:
  `lake env lean` exit 0, warnings only, no "declaration uses sorry".
- Token scan (comment-stripped): sorry 0, admit 0, axiom declarations 0.
- `#print axioms` on `charpoly_smDirac`, `charpoly_smDirac_grouped`,
  `modeFactor_sq_form`, `charpoly_fromBlocks_zero`, `smDirac_reindex`:
  each exactly `[propext, Classical.choice, Quot.sound]`.
- In-tree targeted build of `ThetLogos.CharpolyFactor` on the shipped
  text: green (log archived with the landing records).

## Fences — what this does not do

- The corpus D_F is the **one-generation** `smDirac` ansatz (four Yukawa +
  one Majorana complex parameters). Nothing here addresses three
  generations; `blockedQ3_threeGenerations` is untouched.
- `blockedQ4_closedFormGap` **stays sorry** — by design. The lemma was the
  target, not the closed form. The amendment's Obstruction 2 stands
  untouched: per-sector closed forms do not survive the `min` selection,
  which is generically non-smooth at level crossings. What Path B now has
  in hand for that step is an explicit per-sector biquadratic (its λ²-roots
  are elementary in `|aₖ|`, `|eₖ|` — algebra, stated here, not a Lean
  theorem).
- This is a theorem about the finite toy's Dirac operator. It closes no
  part of any official Clay statement; the board remains NO CLAIM.

## Ledger effect

Q4 Path B's load-bearing lemma: **DISCHARGED**. Path B's remaining step is
the min-selection problem (Obstruction 2), which is a separate, harder
entry — the closed form over the full parameter space is still blocked,
now for one named reason instead of two.

Program census: 3,408 → **3,442 strict** / 3,448 → **3,482
attribute-inclusive**; counted modules 122 → **123**.
