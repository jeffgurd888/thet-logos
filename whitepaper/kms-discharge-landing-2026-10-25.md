# KMS DISCHARGE — LANDING DOSSIER (2026-10-25)

**Verdict: FULL (T1).** `ThetLogos.kms_identity_diagonal` in
`lean/ThetLogos/ModularTime.lean` is proved. The labeled placeholder it
carried (Tier T3) is replaced by a complete proof; the module builds green
on the main tree; the axiom check returns exactly the standard three
(`propext`, `Classical.choice`, `Quot.sound`). The corpus placeholder
census drops from **seven to six**.

## Statement integrity

The theorem's signature, conclusion, and docstring are
character-for-character unchanged (bench diff vs main: two hunks — the two
private helper lemmas and the proof body; nothing else). The relabeling
rule was honored: the original entry was discharged in place by proof, not
rewritten.

## The proof, in one paragraph

The pinned Mathlib (v4.35.0-rc3) carries `Matrix.exp_diagonal`, so the
diagonal modular exponentials are computed directly: `exp(diagModularK w)`
is the diagonal of `(w j : ℂ)⁻¹` and `exp(−diagModularK w)` the diagonal of
`(w j : ℂ)` (helpers `kms_exp_diagModularK`, `kms_exp_neg_diagModularK`),
with entries reduced by `Real.exp_log` at the positive weights. Conjugation
entries become `w k · B k j · (w j)⁻¹`; the diagonal trace expansion cancels
`w i · (w i)⁻¹` entrywise and the two double sums are reindexed
(`Finset.sum_comm`) into each other.

## Findings carried on the record

- **The normalization hypothesis was not needed.** `hw1` (Σw = 1) is unused
  — the build's only warning is its unused-variable linter note. The KMS
  identity at this seat holds for all positive weights; the hypothesis
  stays on the statement, per the relabeling rule.
- **Counts:** the strict census does not move (5,684 strict / 5,745
  attribute-inclusive / 183 modules) — the theorem was already counted as
  a declaration, and the two helpers are `private`, outside the strict
  rule's line-initial pattern. What moved is the placeholder census:
  **7 → 6** (remaining: `blockedQ1..Q5` in BlockedQuestions.lean, T5
  question-posts; `xyz_tripotents_exist` in XYZTripotents.lean, T5 Open
  Problem 2).
- The module header's tier line is flipped accordingly (T3 target →
  discharged 2026-10-25).

## Backers since last landing

The roll stands as it was: no new inscription since the battery landing.
The promise stands — every gift is published here, with its proof stream,
exactly as its giver wishes.

## Tier statement

T1 at the finite diagonal seat, inside ModularTime's existing frame. No
continuum KMS condition is claimed; no dial moves; NO CLAIM on any
Millennium Problem is affected by this landing.
