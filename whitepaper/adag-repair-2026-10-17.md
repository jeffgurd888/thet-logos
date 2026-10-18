# The `adag` Namespace Repair — Dossier (2026-10-17)

**Verdict: STANDS at its scoped scope.** The bosonic-side rename is
complete, renames-only (proved byte-for-byte, §5), every touched
module builds green, and the deliverable — the co-import smoke module
`FockCoImport.lean` — builds green with both sides' creation and
annihilation operators named in one environment (§6). Program total
unchanged: **2,417** (strict line-start count, Jeff's adopted
convention). No physics claim is made or implied by this repair;
Yukawa is the next queue item, not this one.

**One correction to the gauntlet, recorded in the open (§2):** the
parked-fleet gauntlet (`gauntlet-parked-fleet-2026-10-17.md` §6)
scoped this repair correctly for the two Fock *parents*, but its
smoke-module sketch ("imports both Fock parents, transitively both
interactions") is **not achievable under the four-name repair** — a
second collision pair, `numberOp` / `numberOp_basis`
(`BosonicAssembly` vs `FermionicFock`), blocks the bosonic assembly
stack. It is censused and priced below as a separate follow-on
(§7) and was **not** improvised into this repair.

---

## 1. Collision inventory (re-derived, not copied)

Method: declaration names extracted from comment-stripped source,
allowing attribute/modifier prefixes (`@[simp]`, `noncomputable`,
…), for `FermionicFock.lean` (63 declarations) and `BosonicFock.lean`
(36 declarations). The intersection is exactly four constants, all
in `namespace ThetLogos`, same names, different types:

| name | fermionic (`FermionicFock.lean`) | bosonic (`BosonicFock.lean`) |
|---|---|---|
| `adag` | :361 — `Module.End ℂ (FermionicFock d)` | :186 — `Dom d →ₗ[ℂ] Dom d` |
| `ann` | same file pair | same file pair |
| `adag_basis` | theorem, both files | theorem, both files |
| `ann_basis` | theorem, both files | theorem, both files |

No other collisions exist between the two parents. Zero qualified
`ThetLogos.adag` / `ThetLogos.ann` uses exist anywhere in the tree
(all uses are bare, in-namespace), so the rename's blast radius is
exactly the files that use the bare names on the bosonic side —
four files (§3). The target names `adagBos`, `annBos`,
`adagBos_basis`, `annBos_basis` did not exist anywhere before the
repair (grep-verified).

## 2. The wider closure, and the `numberOp` correction

The same extraction run over both full stacks (bosonic: `BosonicFock`,
`BosonicAssembly`, `BosonicSecondQuant`, `BosonicGamma`,
`BosonicGammaFunctor`, `BosonicInteraction`, `BosonicLimit`,
`BosonicLimitOps`; fermionic: `FermionicFock`, `SecondQuantDGamma`,
`SecondQuantGamma`, `FermionicInteraction`, `FermionicLimit`,
`FermionicLimitOps`) gives a six-name cross-chain intersection: the
four repaired names, plus

| name | fermionic | bosonic |
|---|---|---|
| `numberOp` | `FermionicFock.lean:684`, `Module.End ℂ (FermionicFock d)` | `BosonicAssembly.lean:297`, `Dom d →ₗ[ℂ] Dom d` |
| `numberOp_basis` | theorem, `FermionicFock.lean:688` | theorem, `BosonicAssembly.lean:316` |

Kernel confirmation (probe file, post-repair, deleted after use):

```
error: import ThetLogos.BosonicAssembly failed, environment already
contains 'ThetLogos.numberOp' from ThetLogos.FermionicFock
```

Consequence: the gauntlet §6 sentence "the declaration-name
intersection of `FermionicInteraction.lean` ∩ `BosonicInteraction.lean`
is empty" is true file-vs-file but does not extend to the transitive
closure — the two interaction modules still cannot be co-imported
today. The repair below therefore certifies the two parents plus the
full fermionic stack (§6), and §7 prices the remaining door.

## 3. Use-site census (my grep, two methods)

Occurrences of `\b(adag|ann|adag_basis|ann_basis)\b` on the bosonic
side, pre-repair:

| file | `adag` | `ann` | `adag_basis` | `ann_basis` | occurrences | lines |
|---|---|---|---|---|---|---|
| `BosonicFock.lean` | 9 | 10 | 2 | 2 | 23 | 21 |
| `BosonicAssembly.lean` | 45 | 41 | 0 | 2 | 88 | 48 |
| `BosonicSecondQuant.lean` | 15 | 16 | 0 | 0 | 31 | 16 |
| `BosonicInteraction.lean` | 5 | 5 | 0 | 0 | 10 | 3 |
| **total** | | | | | **152** | **88** |

**Correction to the gauntlet's census:** its "82 sites in 4 files"
is the line count of the two short names only — re-running its exact
pattern (`\b(adag|ann)\b`, lines) reproduces 17 + 46 + 16 + 3 = 82
exactly. The same four files carry the full repair surface: 88
lines / 152 occurrences once the `_basis` names are included. The
fermionic side (untouched): `FermionicFock` 69 lines,
`FermionicInteraction` 24, `SecondQuantDGamma` 9.

## 4. Rename map (bosonic side only)

```
adag        →  adagBos
ann         →  annBos
adag_basis  →  adagBos_basis
ann_basis   →  annBos_basis
```

Applied by word-boundary substitution, longest names first, in the
four files of §3 — definitions and every bare use site, code and
doc-prose alike (no bosonic-file prose refers to the fermionic
operators by these bare names; grep-checked). Word boundaries leave
the house's existing suffixed variants (`adagC`/`annC` in
`BosonicAssembly`) and all compound names (`adag_apply`-style)
untouched. Replacement counts matched the §3 occurrence census
exactly per file and per name (23 / 88 / 31 / 10). Post-rename grep:
zero bare occurrences of the four old names remain in the bosonic
files; `git status` confirms the fermionic files are unmodified.

## 5. Invariants

Strict theorem/lemma counts (column-0 `^(theorem|lemma) `,
comment-stripped — the adopted canonical method) before → after:

| file | before | after |
|---|---|---|
| BosonicFock | 25 | 25 |
| BosonicAssembly | 31 | 31 |
| BosonicSecondQuant | 25 | 25 |
| BosonicGamma | 6 | 6 |
| BosonicGammaFunctor | 42 | 42 |
| BosonicInteraction | 69 | 69 |
| BosonicLimit | 27 | 27 |
| BosonicLimitOps | 48 | 48 |
| FermionicFock | 43 | 43 |
| FermionicInteraction | 58 | 58 |
| SecondQuantDGamma | 18 | 18 |
| SecondQuantGamma | 32 | 32 |
| FermionicLimit | 24 | 24 |
| FermionicLimitOps | 32 | 32 |
| **FockCoImport (new)** | — | **0** |

**Renames-only proof:** applying the inverse substitution to each
edited file reproduces its HEAD version byte-for-byte (all four
files). No theorem statement, proof, or definition body changed —
only the four names.

## 6. Builds and the smoke certificate

Targeted builds, all green (`lake build`, pinned Mathlib
v4.35.0-rc3):

| module | jobs |
|---|---|
| BosonicFock | 2,451 |
| BosonicAssembly | 2,452 |
| BosonicSecondQuant | 2,453 |
| BosonicGammaFunctor | 2,455 |
| BosonicLimitOps | 2,458 |
| BosonicInteraction (heaviest consumer) | 2,704 |
| FermionicInteraction (cross-check) | 3,317 |
| **FockCoImport (smoke)** | **3,313** |

**Smoke module** `lean/ThetLogos/FockCoImport.lean` — zero
declarations by design (so the program count is untouched); not
added to the root import list, per house pattern; its targeted
build is the certificate. Import set achieved:

```
ThetLogos.FermionicFock      ThetLogos.BosonicFock
ThetLogos.SecondQuantDGamma  ThetLogos.SecondQuantGamma
ThetLogos.FermionicInteraction
ThetLogos.FermionicLimit     ThetLogos.FermionicLimitOps
```

i.e. both Fock parents, both second-quantization tops, the
fermionic interaction, and both fermionic limit stacks — one
environment. Its eight `#check`s resolve with the expected,
distinct types, e.g.:

```
ThetLogos.adag    : (d : ℕ) → Fin d → Module.End ℂ (FermionicFock d)
ThetLogos.adagBos : (d : ℕ) → Fin d → ↥(Dom d) →ₗ[ℂ] ↥(Dom d)
```

and likewise `ann`/`annBos`, `adag_basis`/`adagBos_basis`,
`ann_basis`/`annBos_basis`. A mixed fermion–boson term is now
*statable* against the two parents — the exact prerequisite the
Yukawa campaign's product-config presentation
(`Finset (Fin df) × Config db`, both parents' construction) needs.

## 7. The remaining door (named, priced, NOT executed)

`numberOp` / `numberOp_basis`: bosonic side occurrences —
`BosonicAssembly` 10, `BosonicSecondQuant` 4, `BosonicLimitOps` 2
(16 in 3 files); fermionic side — `FermionicFock` 5,
`SecondQuantDGamma` 4, `FermionicLimitOps` 2, `FermionicInteraction`
1 (12 in 4 files). A rename on either side is **S**-sized by the
same mechanical pattern, but it is *not* in this repair's priced
scope, and which side renames is a scoping decision (the fermionic
`numberOp` is the older name, mirroring §6's rationale for keeping
fermionic `adag`). Until it is taken, `BosonicAssembly` and
everything above it cannot share an environment with the fermionic
stack. If the Yukawa campaign's build wants the assembled bosonic
space (as opposed to the parents' `Dom`/`Config` presentation), this
rename is its hard prerequisite and should be priced into its
scoping, exactly as this repair was priced into this one's.

## 8. Fences

- This repair is a namespace hygiene operation. It proves no
  theorem, states no interaction, and is not a physics claim of
  any tier.
- Yukawa (priced M–L by the gauntlet) is the next queue item; its
  inherited walls (essential self-adjointness; uniform persistence
  false by the ported collapse counterexample) are unchanged.
- The four pre-existing untracked whitepaper files in the working
  tree were not touched or swept into this commit.
