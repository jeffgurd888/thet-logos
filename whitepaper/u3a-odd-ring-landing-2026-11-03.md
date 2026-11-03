# U-3a ODD RING — LANDING (2026-11-03)

## VERDICT: FULL

Both parts landed at full generality. **Part 1 (CRT transport): FULL** —
`resTriples_crtEquiv {m n : ℕ} (h : m.Coprime n) : ResTriples (m * n) ≃
ResTriples m × ResTriples n`, via Mathlib's `ZMod.chineseRemainder h`.
**Part 2 (mirror organization at every odd n): FULL** —
`mirror_organization_odd`: `(mirrorPairsN n).card = (n^2 - 1) / 2 ∧
mirrorFixedN n = {centerTripleN n}` for odd `n`, plus the additive form
`mirror_organization_odd_add`. **Kills: K-U3-CRT did NOT fire** (no
`ZMod (m*n)` vs `ZMod (n*m)` / cast-normal-form seam; the transport went
through the pin's own CRT directly). K-U3-REP concerns U-3b only — not
in this brick. **NO CLAIM; dials 0/4.**

Module: `lean/ThetLogos/OddRing.lean` — **strict 15 theorems + 7 defs**,
zero sorrys. Targeted build green (3152 jobs), zero warnings
attributable to the module. `#print axioms` on all 16 headlines:
exactly `{propext, Classical.choice, Quot.sound}` or a subset
(`mirrorTripleN_involutive`, `mirrorTripleN_center` use only
`{propext, Quot.sound}`), no sorryAx. Lane: worktree
`~/workspace/thet-logos-u3a`, branch `u3a-lane`, from main-tree HEAD
`4e35329` (item-5 ceremony commit). Not integrated — parent ceremony
follows.

## What landed

| Part | Status | Headline |
|---|---|---|
| CRT on triples, general | FULL | `tripleCrtEquivGen`, `resonant_tripleCrtEquivGen` |
| U-3a headline 1: CRT transport of `ResTriples` | FULL | `resTriples_crtEquiv` (+ `resTriples_crtEquiv_fst_val` / `_snd_val`, `card_resonant_mul`) |
| Self-negation at odd `n` | FULL | `neg_eq_self_imp_eq_zero_odd` (via AxiomTet `zmod_self_neg_iff`) |
| Mirror at general `n` | FULL | `mirrorTripleN`, `mirrorTripleN_involutive`, `centerTripleN`, `mirrorTripleN_center`, `mirrorTripleN_fixed` |
| U-3a headline 2: mirror organization, odd `n` | FULL | `mirrorFixedN_eq`, `card_mirrorFixedN`, `mirror_pair_fiberN`, `card_mirror_pairs_odd`, `mirror_organization_odd`, `mirror_organization_odd_add` |
| 21 as corollary | FULL | `resTriplesCrtEquiv_of_general`, `card_mirror_pairsN_21` |

## Demotion / corollary map (after U-3a)

All by addition — no statement in `MirrorTwentyOneTriplets.lean` was
edited, renamed, or re-proved; its frozen statements stand untouched.

- Triplets' `crt21` / `tripleCrtEquiv` / `resTriplesCrtEquiv`
  (hand-rolled at `21 = 3 * 7`) ⇒ the `(3, 7)` instance of the general
  theorem: `resTriplesCrtEquiv_of_general : ResTriples 21 ≃ ResTriples 3
  × ResTriples 7` is `resTriples_crtEquiv (by decide : Nat.Coprime 3 7)`
  itself, since `crt21` was already defined as `ZMod.chineseRemainder`.
  The bespoke construction is no longer load-bearing.
- Triplets' `neg_eq_self_imp_eq_zero` (21-only; proof by the numeral
  `11 * 2 = 22 = 1`) ⇒ superseded in scope by
  `neg_eq_self_imp_eq_zero_odd` at every odd `n`, routed through
  AxiomTet's already-general `zmod_self_neg_iff`.
- Triplets' `mirrorTriple` / `centerTriple` / `mirrorTriple_fixed` /
  `card_mirror_fixed` ⇒ general forms `mirrorTripleN` / `centerTripleN`
  / `mirrorTripleN_fixed` / `mirrorFixedN_eq` + `card_mirrorFixedN` at
  every odd `n`.
- Triplets' `card_mirror_pairs = 220` and `mirror_organization_21`
  (`441 = 2·220 + 1`) ⇒ instances of `card_mirror_pairs_odd` and
  `mirror_organization_odd` / `mirror_organization_odd_add` at `n = 21`;
  `card_mirror_pairsN_21` recovers the `220` as a one-line corollary.
- Triplets' `card_resonant` (count `n^2`, already general) is consumed,
  not re-proved; new here: `card_resonant_mul` — the count splits
  multiplicatively over a coprime product, via the CRT equiv.

Naming note: the general mirror objects carry the `N` suffix
(`mirrorTripleN`, `centerTripleN`, `mirrorPairsN`, `mirrorFixedN`)
because the un-suffixed names belong to Triplets' frozen 21-specific
definitions. The statements are the scoping's U-3a forms at general `n`.

## What did NOT land / fences (unchanged)

- **TR-4 strata are out of scope and untouched:** the gcd-class
  combinatorics of `21 = 3 * 7` (`UniformPattern`, 92 within / 288
  mixing) is *not* generalized by this brick. The CRT equiv above is
  the organizing law the strata hang from — no more is claimed.
- **U-3b is not in this brick:** the abstract finite-involution
  fixed-function theorem (`fixedEquivReps` 11 / `jointlyFixedEquivReps`
  121 as instances) remains its own priced item; K-U3-REP was not
  tested here.
- Kernel dimension `1` vs fixed-point counting remain different
  theorems, fenced apart; nothing here touches the analytic line
  (LayerKernelPos / FACT / GATE / W3), SHELF-8B, BSD, or Hodge.

**NO CLAIM. Dials 0/4.**

## CEREMONY (2026-11-03, parent integration)

Module and this dossier copied byte-identical from u3a-lane `516954c`
(diff-verified) into the main tree on HEAD `4e35329` (item-5 ceremony
commit). Targeted main-tree build of `ThetLogos.OddRing` green (3155
jobs), zero errors, zero warnings attributable to the module, zero
sorrys. Independent strict recount: module **15 strict + 7 defs** —
exact match with the lane. Fence admissions: the 16 checked headlines
admitted to `lean/scripts/axiom-fence.txt` WITH `import
ThetLogos.OddRing` in the same commit as the module (CI lesson) —
**FENCE PASS 111/111** (95 → 111), every headline's axiom set within
{propext, Classical.choice, Quot.sound}, no sorryAx. Census
(FILES-TRUE, method of record; counter re-validated in-run — spot
checks TritGrading 27, Triplets 32, Item-6 15, OneKernel 20, Item-5
40, OddRing 15 all exact): **12,980/470 → 12,995 strict / 471
modules**; README prose census and shields badge both updated to
12,995 / 471, kept equal. Ledger record `u3a-odd-ring` (standing,
T3), validator PASS, 17 records conform. Verdict stands FULL at full
rank: CRT transport at general coprime (m, n), mirror organization
at every odd n, K-U3-CRT did not fire, Triplets' frozen statements
untouched. NO CLAIM; dials 0/4.
