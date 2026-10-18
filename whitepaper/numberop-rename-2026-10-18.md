# The `numberOp` rename — dossier (2026-10-18)

**Verdict: REPAIR STANDS.** A pure rename brick, item 1 of the unlock
chain Jeff ratified 2026-10-18 (`numberOp` rename → Fock-level Lorentz
→ Wightman re-pin). The second co-import fence — `BosonicAssembly`'s
`numberOp` / `numberOp_basis` colliding with `FermionicFock`'s
declarations of the same fully-qualified names — is discharged: the
bosonic assembly stack now co-imports with the full fermionic stack
in one Lean environment, certified by the extended smoke module
`FockCoImport.lean` building green. Zero proof-content changes;
strict theorem counts invariant per file and in total (program total
unchanged at 3,201 strict, ledger convention; whole-tree strict
recount 3,870 → 3,870). Executed to the standard of the `adag` repair
(2026-10-17, dossier `whitepaper/adag-repair-2026-10-17.md`).

## Census (BEFORE any edit)

Word-boundary grep (`\bnumberOp\b`, `\bnumberOp_basis\b`) over
`lean/ThetLogos/*.lean`, lines with matches:

**Bosonic side (the side renamed):**

| File | `numberOp` lines | `numberOp_basis` lines |
|---|---|---|
| `BosonicAssembly.lean` | 18 (header), 297 (def), 300, 313 (docstrings), 317 (stmt), 321 (proof), 341, 342 (in `numberOp_vacuum`) | 316 (theorem), 344 (proof of `numberOp_vacuum`) |
| `BosonicSecondQuant.lean` | 9, 17 (header), 119 (stmt of `dgammaBos_one`), 120 (`unfold`) | — |
| `BosonicLimitOps.lean` | 788, 795 (both in the intertwining theorem) | — |

Total: **16 lines in 3 files** — the ledger's standing count
("bosonic side 16 occurrences in 3 files") is **VERIFIED** exactly,
read as lines-with-matches including the files' own header/docstring
mentions. Code-only occurrences: 11 (9 `numberOp` + 2 `numberOp_basis`).

**Fermionic side (UNTOUCHED):** `FermionicFock.lean` 684 (def), 688
(`numberOp_basis` theorem), 700, 701, 703; `SecondQuantDGamma.lean`
81, 82, 164 (+ header mention :23); `FermionicLimitOps.lean` 548,
555; `FermionicInteraction.lean` 117 (`numberOp_basis`).

**Prose-only mentions elsewhere (not use sites; NOT edited — see
flagged item below):** `FockCoImport.lean:32`,
`YukawaInteraction.lean:72`, `FockPackaging.lean:13`,
`FockPackagingBos.lean:57`, `FockPackagingFerm.lean:16` — historical
narrative of the fence in module headers.

## The rename map

Bosonic side only (house pattern from the `adag` repair — fermionic
names are older and cited across Rung 5/8/9/10 and Pitch prose):

- `numberOp` → `numberOpBos`
- `numberOp_basis` → `numberOpBos_basis`

Applied word-boundary at the definitions in `BosonicAssembly.lean`
and at every bosonic use site in the census, including the three
files' own header/docstring mentions so each file is internally
consistent. **16 lines changed, 16 insertions / 16 deletions, nothing
else** (full `git diff` inspected: every changed line differs only by
the substitution).

Names deliberately NOT renamed (distinct declarations, no collision,
outside the map): `repr_numberOp_mode` and `numberOp_vacuum` in
`BosonicAssembly` (the latter's *statement* now references
`numberOpBos`; its name is unchanged and has no fermionic namesake),
`numberOpLimBos` in `BosonicLimitOps`, `numberOpLimFerm` on the
fermionic side.

## The smoke certificate

`FockCoImport.lean` extended: it now additionally imports
`BosonicAssembly`, `BosonicSecondQuant`, `BosonicInteraction`, and
`BosonicLimitOps` alongside the full fermionic stack
(`FermionicFock`, `SecondQuantDGamma`, `SecondQuantGamma`,
`FermionicInteraction`, `FermionicLimit`, `FermionicLimitOps`), and
exercises both statistics' number operators in the one environment:

- `#check`s: `@ThetLogos.numberOp`, `@ThetLogos.numberOp_basis`,
  `@ThetLogos.numberOp_apply_basis` (fermionic);
  `@ThetLogos.numberOpBos`, `@ThetLogos.numberOpBos_basis`,
  `@ThetLogos.numberOp_vacuum` (bosonic).
- Joint vacuum example (anonymous): `numberOp d (fockBasis d ∅) = 0 ∧
  numberOpBos d (vacDom d) = 0`.
- Joint basis-action example (anonymous): fermionic eigenvalue
  `S.card` and bosonic eigenvalue `∑ i, c i`, side by side, proved by
  `numberOp_apply_basis` and `numberOpBos_basis` respectively.

Anonymous `example`s by design — the smoke module still carries **no
named declarations**, so its strict count stays 0 and no count
anywhere moves. The module header's fence section is rewritten as
the discharged-fence record.

## Verification

**Builds** (`lake build`, targeted, all green, `.olean`s present):

| Target | Jobs |
|---|---|
| `ThetLogos.BosonicAssembly` | 2,452 |
| `ThetLogos.BosonicSecondQuant` | 2,453 |
| `ThetLogos.BosonicLimitOps` | 2,458 |
| `ThetLogos.FockCoImport` (the certificate) | 3,323 |
| `ThetLogos.FockPackagingBos` + `YukawaInteraction` + `BosonicGammaFunctor` (downstream spot-check) | 3,676 |

**Count invariance** (strict line-initial `^(theorem|lemma) ` on
comment-stripped source, before → after):

| File | Before | After |
|---|---|---|
| `BosonicAssembly.lean` | 31 | 31 |
| `BosonicSecondQuant.lean` | 25 | 25 |
| `BosonicLimitOps.lean` | 48 | 48 |
| `FockCoImport.lean` | 0 | 0 |
| `FermionicFock.lean` (untouched) | 43 | 43 |
| `BosonicInteraction.lean` (untouched) | 69 | 69 |
| `FockPackagingBos.lean` (untouched) | 99 | 99 |
| **whole tree** | **3,870** | **3,870** |

A full-tree before/after diff of per-file strict counts returned
**no changed file**. Program total by the ledger's canonical counted
set: **3,201 strict, unchanged** — as a pure repair must leave it.

## Process notes and flagged items

- One build iteration on the NEW smoke code only: the first
  `FockCoImport` build failed because the fermionic
  `numberOp_apply_basis` takes `d` explicitly (`numberOp_apply_basis
  d S`, not `… S`). Fixed in the smoke module; no renamed file was
  touched by the fix. Not a scope deviation.
- **Flagged stale prose (NOT edited — outside this brick's scope,
  belongs to the standing S-editorial stale-header list):** the
  headers at `YukawaInteraction.lean:72`, `FockPackaging.lean:13`,
  `FockPackagingBos.lean:57`, and `FockPackagingFerm.lean:16` still
  describe the `numberOp` collision as a standing fence. It is now
  historical — the two-module Fock packaging split it motivated is a
  fact of the build history, no longer a necessity.
- Deviations from the commission: **none.**
