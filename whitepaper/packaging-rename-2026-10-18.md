# Packaging-module rename — the third co-import fence, discharged (2026-10-18)

**Verdict: STANDS as a pure repair.** The two Fock *packaging* modules,
`FockPackagingBos.lean` and `FockPackagingFerm.lean`, can now be imported
into a single Lean environment. The fence was **six** colliding helper
names, not one: the Fock-level Lorentz brick (unlock chain item 2) had
found `inner_linearCombination_mixed` and correctly recorded the fence,
but the compiler aborts at the first duplicate declaration, so the other
five were invisible until a dedicated census + joint-import probe. The
repair renames the **bosonic side only**, all six names, by the house
suffix pattern. Strict counts are invariant in every touched file; the
program total stays **3,229 strict**.

This is the third co-import fence discharged by rename: `adag`/`ann`
(2026-10-17), `numberOp`/`numberOp_basis` (2026-10-18, unlock chain
item 1), and now the packaging layer. The Fock *stacks* were already
co-importable; the packaging modules sit one level above them.

## §1 Census (word-boundary grep, whole `lean/` tree, verified before any edit)

| Name | Bos: `FockPackagingBos.lean` | Ferm: `FockPackagingFerm.lean` | Other files |
|---|---|---|---|
| `inner_linearCombination_mixed` | def :1803; uses :1821, :1874, :1875 | def :1281; uses :1300, :1351, :1352 | — |
| `exists_forall_mem_of_monotone` | def :1126; use :1158 | def :268; use :300 | — |
| `linearCombination_eq_sum` | def :1794; uses :1809, :2084, :2085, :2523 | def :1273; uses :1287, :1562, :1563, :1919 | `FockLorentzBos.lean:204` (Bos-side use); `FockLorentzFerm.lean:188` (Ferm-side use) |
| `ofReal_norm_sq` | def :862; use :1044 | def :333; use :580 | — |
| `summable_mul_of_summable_sq` | def :1227; uses :1411, :1600 | def :320; uses :894, :1071 | — |
| `tsum_eq_of_tendsto_sum_exhaustion` | def :1144; uses :1536, :1701 | def :286; uses :1039, :1189 | — |

Bos-side occurrence lines: **19** in `FockPackagingBos.lean` + **1** in
`FockLorentzBos.lean` = **20 lines**. No other file in the tree references
any of the six names. No drift from the first attempt's census.

Statement shapes (relevant to §3): the two `linearCombination`-family
names are genuinely *different* statements per statistic (bosonic index
type `ConfigLim`, fermionic `Finset ℕ`). The other four —
`exists_forall_mem_of_monotone`, `ofReal_norm_sq`,
`summable_mul_of_summable_sq`, `tsum_eq_of_tendsto_sum_exhaustion` — are
generic helpers whose statements (and, for `ofReal_norm_sq`, proof) are
**identical** in both modules.

## §2 The rename map (bosonic side only; fermionic files untouched)

| Old | New |
|---|---|
| `inner_linearCombination_mixed` | `inner_linearCombination_mixedBos` |
| `exists_forall_mem_of_monotone` | `exists_forall_mem_of_monotoneBos` |
| `linearCombination_eq_sum` | `linearCombination_eq_sumBos` |
| `ofReal_norm_sq` | `ofReal_norm_sqBos` |
| `summable_mul_of_summable_sq` | `summable_mul_of_summable_sqBos` |
| `tsum_eq_of_tendsto_sum_exhaustion` | `tsum_eq_of_tendsto_sum_exhaustionBos` |

Applied by word-boundary substitution at the definitions and every bare
bosonic use site, including docstrings: **20 lines changed, 20 insertions /
20 deletions, nothing else** (full diff inspected line by line; every change
is a name substitution). Files touched: `lean/ThetLogos/FockPackagingBos.lean`,
`lean/ThetLogos/FockLorentzBos.lean`, plus the certificate extension in
`lean/ThetLogos/FockCoImport.lean` (§4).

**Joint-import probe:** after the rename, a scratch module importing both
packaging modules compiled green on the first iteration and all twelve
names (six renamed Bos + six original Ferm) resolve in the one environment.
**No further collisions exist between the pair** — the final collision list
is exactly the six names above. (The probe file was deleted before
committing, per discipline.)

## §3 The declined alternative — deduplication, and why it was declined

Four of the six helpers are statement-identical generic lemmas, so the
obvious refactoring is to delete one copy of each and keep a single shared
declaration in the common base module `FockPackaging.lean`. **Declined.**
Deduplication would remove four declarations from the tree and move the
program total (3,229 → 3,225) for a pure repair — breaking the
repair-invariance rule that every fence repair so far has honored (the
`adag` and `numberOp` repairs both left every count untouched), and
falsifying the published count without any theorem having changed.
Renaming preserves both the counts and the published record; deduplication
remains available as a separate, explicitly-priced refactoring if it is
ever wanted on its own merits. It is not smuggled into a repair.

## §4 The certificate

`lean/ThetLogos/FockCoImport.lean` (the co-import smoke module; 0
declarations of its own, by design) now additionally imports
`ThetLogos.FockPackagingBos` and `ThetLogos.FockPackagingFerm` and
`#check`s all twelve helper names — the six renamed bosonic helpers and
the six original fermionic ones — in the single environment, alongside
the earlier `adag`/`numberOp` certificates. Its header records this third
fence alongside the first two. A green build of `FockCoImport` is the
machine-checked statement that all three fences are down: the fermionic
stack, the bosonic stack, and both packaging modules now share one
environment end to end.

## §5 Invariance (strict recount: line-initial `^(theorem|lemma) ` on comment-stripped source)

| File | Before | After |
|---|---|---|
| `FockPackaging.lean` | 38 | 38 |
| `FockPackagingBos.lean` | 99 | 99 |
| `FockPackagingFerm.lean` | 78 | 78 |
| `FockLorentzBos.lean` | 7 | 7 |
| `FockLorentzFerm.lean` | 7 | 7 |
| `FockCoImport.lean` | 0 | 0 |

A uniform recount over the whole `lean/ThetLogos/` tree is likewise
identical before and after. **Program total: 3,229 strict — unmoved, as a
pure repair must leave it.** No `sorry`/`admit` in any touched file.

## §6 Verification

- `lake build ThetLogos.FockPackagingBos ThetLogos.FockLorentzBos` — green,
  **3,672 jobs**, `.olean`s present.
- `lake build ThetLogos.FockCoImport` (both packaging modules in the one
  environment) — green, **3,681 jobs**, `.olean` present.
- Fermionic files unmodified (git diff confirms: only the two Bos files
  and `FockCoImport.lean` changed).

## §7 Fences

- Renames only: no statement, proof, or count changed anywhere.
- Nothing here is a physics claim; this is namespace hygiene that removes
  a build-level obstruction between two already-standing modules.
- Clay parts closed by this repair: **0**.
