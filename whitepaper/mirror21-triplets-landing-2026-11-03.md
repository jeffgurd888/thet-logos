# Triplets of Correlations — Landing Dossier (2026-11-03)

**EXPECTATION VERDICT: EXPOSED.** Jeff's pre-registered expectation
(2026-11-02 21:56, "I expect the correlations to expose a unified
geometric structure"), under his sharpened bar (22:00, "exposed =
kernel proven"), is met: one T1 organizing law landed from which the
count, the mirror organization, and the family strata all fall out
as corollaries. The law is the Chinese remainder decomposition of
resonant triples,

`resTriplesCrtEquiv : ResTriples 21 ≃ ResTriples 3 × ResTriples 7`,

together with the forced-third-coordinate law
(`resonant_iff_third`, `resonantEquivPairs : ResTriples n ≃ ZMod n ×
ZMod n`). The 441 count is `21²` by the pair equivalence; the mirror
organization `441 = 2·220 + 1` is the involution count over the same
type; the strata `92 / 288` are the CRT shadows' own counts
transported back along the decomposition (shadow counts
`(n−1)(n−2)` at `n = 3, 7`, all-zero shadow unique). This is finite
combinatorics on `ZMod 21`, machine-checked. **NO CLAIM** — it
answers nothing about any Millennium problem; Jeff's P vs NP
suspicion (2026-11-02 22:01) is filed T5 and fenced out: a fixed
finite pattern is not an asymptotic complexity statement. Dials 0/4.

## Per-pin verdicts

- **TR-1 (bridge) — FULL at T1.** `resonant_center_iff`,
  `resonant_center_ext`: a resonant triple has zero in a slot iff the
  other two entries sum to zero, i.e. form a Mirror-21 doublet.
- **TR-2 (count) — FULL at T1.** `card_resonant` (general `n`:
  `card (ResTriples n) = n²`), `card_resonant_21 = 441`, proved by
  the pair equivalence, not by enumeration.
- **TR-3 (mirror closure) — FULL at T1.** `mirrorTriple` (entrywise
  negation) is an involution on resonant triples; its unique fixed
  point is the center `(0,0,0)` (`card_mirror_fixed = 1`, via
  `neg_eq_self_imp_eq_zero` in `ZMod 21`); `card_mirror_pairs = 220`
  and `mirror_organization_21 : 441 = 2·220 + 1`.
- **TR-4 (family strata, stretch, kill-armed) — FULL at T1;
  K-TR-4 does NOT fire.** Of the 380 all-nonzero resonant triples
  (`card_allNonzero_21`, from the general law `(n−1)(n−2)`), exactly
  **92** stay within one gcd family (`card_within_family`) and
  exactly **288** mix families (`card_mixing = 380 − 92`). On the
  product side the 92 decomposes as `1·30 + 2·1 + 2·30`
  (`card_withinProd`): each gcd class is a CRT vanishing pattern
  (mod 3 × mod 7), each shadow is all-zero (1 way) or all-nonzero
  (2 ways at 3, 30 ways at 7), and the both-zero pattern is excluded
  by all-nonzero-ness.

## One honesty note on the pattern definition

"Within one family" must be read **componentwise**: a residue's gcd
class mod 21 is a function of its vanishing pattern at the two CRT
components separately, *not* of vanishing in `ZMod 21` alone. The
triple `(3, 1, 17)` is all-nonzero mod 21 but its mod-3 shadow is
mixed, and its entries lie in different gcd classes. `UniformPattern`
in the module is the componentwise notion (`SamePattern`), and the
transport lemmas (`uniformPattern_transport`,
`withinFamily_transport`) are stated and proved for exactly it.

## Verification

- Module: `lean/ThetLogos/MirrorTwentyOneTriplets.lean`, built in
  the isolated worktree `~/workspace/thet-logos-triplets`, branch
  `triplets-lane` (base: main-tree local HEAD `74bfc08`; lane commit
  `a0d7398`). **Not integrated** — parent ceremony integrates.
- `lake build ThetLogos.MirrorTwentyOneTriplets`: **green,
  warning-clean** (0 errors, 0 warnings), **zero sorrys**.
- **Strict count: 32** (`theorem`/`lemma` at column 0,
  comment-stripped).
- `#print axioms` on the headlines — `resonant_center_iff`,
  `card_resonant_21`, `card_mirror_pairs`, `mirror_organization_21`,
  `card_within_family`, `card_mixing`, `card_withinProd`,
  `resTriplesCrtEquiv` — all within
  `{propext, Classical.choice, Quot.sound}`; **no sorryAx**.
- T2 companion `python/mirror21_triplets.py`: exit 0 — 441 total /
  61 with a zero slot / 380 all-nonzero / 324 all-distinct ordered /
  54 unordered sets / 92 within-family / 288 mixing / 220 mirror
  pairs + the lone center. A finite-enumeration checker (T2), not a
  proof; it agrees with the T1 counts at every point.

## Systemic-unification watch (standing note, no claim)

The pattern "unique center / unique zero mode" recurs once more:
the lone mirror-fixed triple is `(0,0,0)`, and each CRT shadow has
exactly one all-zero resonant triple. Logged as a recurrence beside
the Bridge / Mirror-21 / Orthogonal / Axiom Tet / Partner instances.
No unifying theorem is claimed; dials 0/4.

## CEREMONY (parent, main tree, 2026-11-03)

- Lane files copied byte-identical from worktree `~/workspace/thet-logos-triplets`
  (branch `triplets-lane`, commits `a0d7398` + `eb7bdc1`) into the main tree
  at local HEAD `459c3c5` (Brick 1 ceremony commit); identity verified by diff.
- Targeted main-tree build `lake build ThetLogos.MirrorTwentyOneTriplets`:
  **green** (1156 jobs, ~28s), zero sorrys (no `sorry` token in the module);
  no warnings in the build output.
- Independent strict recount of the module (method of record:
  comment/string-stripped, `^(theorem|lemma)\s` at column 0): **32**,
  matching the lane count exactly.
- Axiom fence: the 8 headlines admitted to `lean/scripts/axiom-fence.txt`
  WITH their import line (`import ThetLogos.MirrorTwentyOneTriplets`) in
  this same commit as the module — the CI lesson, applied after Brick 1
  Step B. Official runner: **FENCE PASS 55/55** (47 → 55), every headline
  on exactly {propext, Classical.choice, Quot.sound} (`resonant_center_iff`
  on {propext, Quot.sound}), no sorryAx.
- T2 companion re-run in the main tree: `python/mirror21_triplets.py`
  exit 0, all checks pass.
- Census effect: **12,875 → 12,907 strict / 13,401 → 13,433 total /
  466 → 467 modules** (shipped chain; +32 / +32 / +1). Cross-check,
  stated plainly: a fresh whole-tree count measures 13,574 strict over
  482 tree files; minus the frozen pre-ledger remainder (669, 15 files)
  that is 12,905 files-true — exactly the shipped figure minus the
  documented +2 ledger overstatement identified in
  `whitepaper/census-reconciliation-2026-11-02.md` (unlocated +3 gross /
  −1 located). The overstatement is unchanged by this landing; restating
  the public census to files-true numbers remains Jeff's open decision,
  not taken here.
- Ledger record `mirror-21-triplets-of-correlations` (standing, T3);
  validator PASS, 12 records conform.
- README census updated (12,907 declarations / 467 modules — the only
  README numbers changed by this ceremony; the shields badge at the top
  of the README still reads 12,725, a pre-existing staleness predating
  Brick 1, flagged in the ceremony report, not silently rewritten here).
- Landing verdict unchanged: **FULL** (TR-1..TR-4 at T1; K-TR-4 did not
  fire; expectation EXPOSED via the CRT organizing law). **NO CLAIM**;
  dials 0/4.
