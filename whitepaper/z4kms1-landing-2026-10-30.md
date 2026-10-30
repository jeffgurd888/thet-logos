# Z4-KMS-1 — the clock defect, measured

**Date:** 2026-10-30 · **Brick:** Z4-KMS-1 (S), per
`scoping-z4-toothed-kms-2026-10-30.md` §3. New module:
`ThetLogos.ThermalZ4ClockDefect`. **Verdict: LANDED FULL**
(strict 2 / defs 2, parent-verified from disk — the specified
content is exactly the two headlines and two definitions; the
6–12 scoping estimate anticipated transport helpers the build
did not need).

**Fences: NO CLAIM. Parts of any official statement closed: 0.
Dials: 0/4.**

## What landed

With `z4Shift k := k + 1` (the clock turn on Fin 4) and
`z4ShiftedWeight β k := z4Weight β (z4Shift k)`:

- **Headline 3** `z4_clock_defect_factor`:
  `(∀ k : Fin 4, k.val < 3 → z4ShiftedWeight β k
      = Real.exp (−β/4) * z4Weight β k)
    ∧ z4ShiftedWeight β 3 = Real.exp (3β/4) * z4Weight β 3`
  — **transported** from Z4-LADDER's landed step ratios, consumed
  verbatim and re-expressed along two `Fin.ext` identifications;
  the ladder's theorems were not restated or re-derived.
  **K-Z4K-2 does not fire** (the landed form composed directly).
- **Headline 4** `z4_clock_not_invariant` (β > 0):
  `¬ (∀ k, z4ShiftedWeight β k = z4Weight β k)` — at k = 0 the
  defect factor forces `exp(−β/4) = 1` against `z4Weight_pos`,
  contradicting β > 0.

Both headlines: exactly `[propext, Classical.choice, Quot.sound]`;
module and full-tree builds green.

**The content in one line, as the module's face states it:** the
clock is a broken symmetry of the ladder's thermal state, and the
breaking is measured — exp(−β/4) per step, exp(+3β/4) at the
wrap; the defect is exactly the ladder's slope. On a flat ladder
the same statement shape is false (every factor would be 1), so
the identity is content about the slope, not a tautology about
finite sets.

## Bearing — labeled, no silent promotion

This theorem is **raw material for W2** (the C⁴ leg's surviving
weakened form): a measured state-asymmetry under the clock that a
grading could carry. It does **not** land W2 — it constructs no
irreversible step, no semigroup, no entropy production. It has
**no bearing on W1**. **G1/G2 are untouched**: the defect is a
fact about the clock acting on weights, fully compatible with
the landed verdict that the modular flow fixes its Gibbs state
(G2) — the C⁴ leg's strong form stays refuted-as-stated, and
this brick is not its exception. No entropy language appears
anywhere in the brick (T-ENT is not a dependency, by design).

**Census: 7,456 → 7,458 strict / 7,534 → 7,536
attribute-inclusive / 257 → 258 modules** (recounted from disk).

**The Z₄ line is closed:** Z4-LADDER + Z4-KMS-0 + Z4-KMS-1 all
landed FULL; every pre-registered kill in the line (K-Z4K-1/2/3)
was armed and none fired; the dropped file's vacuous `KMSState`
and content-free structures remain refused, unbuilt.

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you to
everyone reading the stream — the corpus is free for everyone,
forever.

*End of dossier.*
