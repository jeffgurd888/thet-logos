# Housekeeping bundle — dossier (2026-10-18)

Bench line item 3 (ratified by Jeff 2026-10-18; priced S). Two parts,
verdicts reported separately:

- **Part A — seven stale headers corrected in place: STANDS.** Editorial
  edits to header/docstring/comment text ONLY; no theorem, definition,
  or proof changed. Strict recount per file IDENTICAL before/after
  (below). Every flagged text was re-read fresh before editing; all
  seven were stale as commissioned. One additional instance of the
  same stale fence was found inside file 7 and corrected with it
  (item 7b); two further docstrings in file 1 were checked and left
  (item 1-note).
- **Part B — the ThermalClock matrix-level scalar-shift lemma:
  STANDS.** Four new T1 theorems appended as §7 of
  `lean/ThetLogos/ThermalClock.lean` (nothing existing modified),
  axioms the standard three (propext, Classical.choice, Quot.sound)
  on all four. ThermalClock 29 → 33 strict; **program total
  3,257 → 3,261 strict.**

Builds: `ThetLogos.ThermalClock` green (3,310 jobs); the seven Part A
modules green in one targeted build (3,690 jobs); all eight `.olean`s
present. Zero `sorry`/`admit` in every touched file before and after
(comment-stripped source).

---

## Part A — per-header old → new

### 1. `BosonicInteraction.lean` (module header, ~:43) — CORRECTED

The clause claiming Mathlib has no `LinearPMap` closure operator was
killed as stale (gauntlet K2): `LinearPMap.closure` exists in the
pinned Mathlib, and `BosonicESA.lean` / `BosonicESABeta.lean` build
essential self-adjointness on it.

OLD:
> Essential self-adjointness of the closure is **not** claimed: Mathlib
> has no closure operation for partial linear maps and no
> essential-self-adjointness criterion (no Kato–Rellich, no analytic
> vectors — grep-verified in the scoping), and the closure's domain is
> an ℓ²-growth condition across infinitely many sectors. That step is
> priced, unattempted.

NEW:
> Essential self-adjointness of the closure is **not** claimed in this
> module — it was discharged separately in `BosonicESA.lean` and
> `BosonicESABeta.lean`, building on `LinearPMap.closure`: the closure
> operation for partial linear maps DOES exist in the pinned Mathlib.
> (An earlier form of this header asserted that Mathlib has no closure
> operation for partial linear maps and no essential-self-adjointness
> criterion — that premise is stale; corrected 2026-10-18. The
> discharge route is the closure route, not a Mathlib Kato–Rellich or
> analytic-vector criterion, and the closure's domain remains an
> ℓ²-growth condition across infinitely many sectors.)

Item 1-note (checked, deliberately NOT edited): two docstrings deeper
in the same file also mention closure — at the sectorwise spectral
theorem ("the self-adjointness content available in current Mathlib;
see the module header for the precise scope (no
closure/essential-self-adjointness claim)") and at
`hamPMap_le_adjoint` ("the maximal self-adjointness statement the
`LinearPMap` API expresses without a closure operation"). Both
describe THIS module's own claim scope and formulation choice, which
are unchanged and true — the module itself still proves no ESA
statement; the discharge lives in BosonicESA/Beta. Left as-is.

### 2. `SpectralActionFinite.lean` (header :16 + §-comment ~:631) — CORRECTED (both spots)

`tr_DF_fourth_yukawa` was listed as open/stretch in two places; it is
PROVED in the same file (via `trace_buildDirac_fourth`, axioms
standard three). `tr_fluctuated_fourth` has no theorem anywhere and
correctly stays open — the correction moves only the proved item.

Header OLD:
> - D²-block q-lemmas (`pow2_buildDirac_blk_00` … `pow2_buildDirac_blk_33`, C=0):
>   infrastructure for the fourth power (stretch, not completed).
>
> Open (stretch):
> - `tr_DF_fourth_yukawa`: `Tr((smDirac …)^4)` as a Yukawa polynomial.
> - `tr_fluctuated_fourth`: `Tr((fluctuatedDirac D_F A)^4)`, symbolic in `A`.

Header NEW:
> - D²-block q-lemmas (`pow2_buildDirac_blk_00` … `pow2_buildDirac_blk_33`, C=0):
>   infrastructure for the fourth power.
> - `tr_DF_fourth_yukawa`: `Tr((smDirac …)^4)` as a Yukawa polynomial
>   (K4a; proved below via `trace_buildDirac_fourth`).
>
> Open (stretch):
> - `tr_fluctuated_fourth`: `Tr((fluctuatedDirac D_F A)^4)`, symbolic in `A`.

§-comment OLD:
> The full `tr_DF_fourth_yukawa` (Yukawa polynomial for the fourth power)
> and `tr_fluctuated_fourth` remain open: they require a
> `trace_buildDirac_fourth` block-expansion lemma (16 terms, 8 nonzero)
> analogous to `trace_buildDirac_sq`, which is mechanical but lengthy.

§-comment NEW:
> `tr_DF_fourth_yukawa` (Yukawa polynomial for the fourth power) is
> proved below via the `trace_buildDirac_fourth` block-expansion lemma
> (16 terms, 8 nonzero) analogous to `trace_buildDirac_sq`; only
> `tr_fluctuated_fourth` remains open. (An earlier form of this
> comment listed both as open; corrected 2026-10-18.)

(The 2026-09-30 numerical-verification lines in that comment —
coefficients `[4,4,4,4]`, momenta `[1,0,0,0]`, `Tr(D_F⁴) = 40` — were
kept verbatim.)

### 3. `WightmanAxioms.lean` (header, :19–22) — CORRECTED

The premise "Mathlib has no tempered distributions" is FALSE for the
pinned Mathlib v4.35.0-rc3, which ships `𝓢′` with Fourier theory;
the re-pins live in `WightmanRepin` (and `OSRepin` on the OS side).

OLD:
> Mathlib (2026) has no Schwartz distribution theory, no operator-valued
> distributions, no Poincaré representation theory adequate for quantum
> fields — those dependencies are logged below, not wished away.

NEW:
> Correction (2026-10-18): this header originally asserted that Mathlib
> (2026) has no Schwartz distribution theory. That premise is FALSE for
> the pinned Mathlib v4.35.0-rc3, which ships tempered distributions
> `𝓢′` with Fourier theory; the axioms are therefore re-pinned on
> genuine `𝓢′` in `ThetLogos.WightmanRepin` (OS side:
> `ThetLogos.OSRepin`), and this file stands as the historical
> opaque-field pin. What Mathlib still does not ship is an
> operator-valued distribution theory or a Poincaré representation
> theory adequate for quantum fields — those dependencies are logged
> below, not wished away.

The header's standing line "What this file is NOT. A construction of
any QFT." is unchanged — it remains true.

### 4. `YukawaInteraction.lean` (:71–77) — CORRECTED to historical

The `numberOp` collision was described as a standing fence; it was
discharged 2026-10-18 by the bosonic-side rename
`numberOp` → `numberOpBos`, and `FockCoImport.lean` imports
`BosonicInteraction` alongside the full fermionic stack, green.
Verified before editing: Yukawa's own imports contain no
`BosonicAssembly`, so "no statement is routed through
`BosonicAssembly`" remains true as a design fact and is kept.

OLD:
> - `BosonicInteraction` does NOT co-import with the fermionic stack
>   (the censused `numberOp` collision in `BosonicAssembly`, adag-repair
>   dossier 2026-10-17); the bosonic coefficient machinery above
>   `BosonicFock`'s parent API (monomial calculus, relative bounds,
>   windowed persistence) is therefore rebuilt inside this module on
>   the product configurations, in the same style. No statement is
>   routed through `BosonicAssembly`.

NEW:
> - `BosonicInteraction` did NOT co-import with the fermionic stack
>   when this module was built (the censused `numberOp` collision in
>   `BosonicAssembly`, adag-repair dossier 2026-10-17). That fence is
>   HISTORICAL: it was discharged 2026-10-18 by the bosonic-side rename
>   `numberOp` → `numberOpBos`, and `FockCoImport.lean` now imports
>   `BosonicInteraction` alongside the full fermionic stack. This
>   module's presentation is unchanged by design: the bosonic
>   coefficient machinery above `BosonicFock`'s parent API (monomial
>   calculus, relative bounds, windowed persistence) is rebuilt inside
>   this module on the product configurations, in the same style, and
>   no statement is routed through `BosonicAssembly`.

### 5. `FockPackaging.lean` (:11–14) — CORRECTED to historical

OLD:
> This module is the fence-neutral shell side, imported by both
> statistic modules (`FockPackagingBos`, `FockPackagingFerm`), which
> cannot be co-imported with each other (`numberOp`/`numberOp_basis`
> collide between `FermionicFock` and `BosonicAssembly` — a standing
> corpus fence; the rename is priced S and is not in this brick's
> scope).

NEW:
> This module is the fence-neutral shell side, imported by both
> statistic modules (`FockPackagingBos`, `FockPackagingFerm`). At
> packaging time the two could not be co-imported with each other
> (`numberOp`/`numberOp_basis` collided between `FermionicFock` and
> `BosonicAssembly`); that fence is HISTORICAL — discharged 2026-10-18
> by the `numberOpBos` rename, and the packaging-level helper
> collisions by the six-name packaging rename (dossiers
> `whitepaper/numberop-rename-2026-10-18.md` and
> `whitepaper/packaging-rename-2026-10-18.md`). `FockCoImport.lean`
> now imports both statistic modules in one environment.

### 6. `FockPackagingBos.lean` (:55–58) — CORRECTED to historical

OLD:
> * The fermionic half lives in `FockPackagingFerm.lean`: the two
>   statistic stacks cannot be co-imported in one module
>   (`numberOp`/`numberOp_basis` collide between `FermionicFock` and
>   `BosonicAssembly`).

NEW:
> * The fermionic half lives in `FockPackagingFerm.lean`. (Historical
>   note: at packaging time the two statistic stacks could not be
>   co-imported in one module — `numberOp`/`numberOp_basis` collided
>   between `FermionicFock` and `BosonicAssembly`. That fence was
>   discharged 2026-10-18; see `FockCoImport.lean` and the
>   packaging-rename dossier.)

(The same header's Lorentz bullet — "Lorentz strong continuity is
NOT part of this brick" — is true of the module itself and was not
flagged; left unchanged.)

### 7. `FockPackagingFerm.lean` (:14–20) — CORRECTED to historical

OLD:
> This module is the fermionic half of the packaging; the bosonic
> half is `ThetLogos.FockPackagingBos`. The two statistics live in
> separate modules under one dossier because the corpus's two
> second-quantization stacks cannot be co-imported in one
> environment (`numberOp`/`numberOp_basis` collide between
> `FermionicFock` and `BosonicAssembly`); neither stack is imported
> here — this module imports only `ThetLogos.FockPackaging` (the
> one-particle shell representation) and `ThetLogos.FermionicLimitOps`
> (the fermionic limit stack).

NEW:
> This module is the fermionic half of the packaging; the bosonic
> half is `ThetLogos.FockPackagingBos`. The two statistics live in
> separate modules under one dossier: at packaging time the corpus's
> two second-quantization stacks could not be co-imported in one
> environment (`numberOp`/`numberOp_basis` collided between
> `FermionicFock` and `BosonicAssembly`) — that fence is HISTORICAL,
> discharged 2026-10-18 (see the header note in
> `ThetLogos.FockPackaging` and the packaging-rename dossier);
> neither stack is imported here — this module imports only
> `ThetLogos.FockPackaging` (the one-particle shell representation)
> and `ThetLogos.FermionicLimitOps` (the fermionic limit stack).

Item 7b (second instance in the same file, §F3 note ~:263 — corrected
with the header, it is the same stale fence in the present tense):
OLD: "they are re-proved here because the bosonic module that owns
them cannot be co-imported with this one (see the header)."
NEW: "they were re-proved here because, at packaging time, the
bosonic module that owns them could not be co-imported with this one
(see the header; that fence was discharged 2026-10-18)."

---

## Part B — the scalar-shift lemma, matrix level

Source of the leftover: `whitepaper/thermal-clock-2026-10-17.md` §4 —
"A separate matrix-level lemma 'adding a scalar multiple of I to the
generator does not change `modularFlow`' was *not* formalized; the
scalar cancellation itself *is* formalized — in the eigenbasis
picture… If a future brick needs the matrix-level scalar-shift lemma,
it is priced S (route: `exp_add_of_commute` + scalar conjugation
triviality, cf. `scalar_conj_trivial`)."

Placement choice: appended to `lean/ThetLogos/ThermalClock.lean` as
§7 (the module owns `modularFlow`/`modularFlux`; a new module would
have had to re-import the same stack for four lemmas). Nothing
existing was modified.

The four theorems (all T1, axioms propext / Classical.choice /
Quot.sound):

1. `commutator_add_smul_one` — `(K + c • 1) * A - A * (K + c • 1)
   = K * A - A * K` for all matrices K, A and scalars c.
2. `modularFlux_add_smul_one` — `modularFlux (K + c • 1) D
   = modularFlux K D` (unfold + 1).
3. `modularFlow_add_smul_one` — **the headline**: `modularFlow
   (K + c • 1) s B = modularFlow K s B` for all K, c, s, B.
4. `gibbs_conversion_full_generator` — `modularFlow ((β : ℂ) • K
   + logZ • 1) s B = modularFlow K (β * s) B`: the conversion theorem
   for the FULL Gibbs generator `−ln ρ_{β,K} = β • K + (ln Z) • I`
   (the `GibbsClock` docstring states the true generator has this
   scalar part; `gibbs_conversion` was stated for `β • K` exactly —
   lemma 3 closes exactly that gap).

Route (as priced, with one honest deviation): the exponential of
the shifted generator splits by `Matrix.exp_add_of_commute` (the
scalar matrix is central; commutation discharged by
`Commute.one_right` + `Commute.smul_left`/`smul_right`), the scalar
exponential is evaluated by `Matrix.exp_diagonal`, and the two
scalar factors `exp(±z·c)` cancel by `NormedSpace.exp_add_of_commute`
+ `exp_zero`. Deviation from the dossier's sketch: the scalar
exponential evaluation could NOT go through
`NormedSpace.algebraMap_exp_comm` — that lemma sits in the normed
section of the exp API and demands a `NormedRing (Matrix …)`
instance, which pinned Mathlib does not provide globally (the
corpus's matrix exp lives in the topological section). The landed
route evaluates the Pi-type exponential in `Matrix.exp_diagonal`
pointwise instead, via `NormedSpace.exp_eq_tsum` +
`Pi.tsum_apply` + `NormedSpace.expSeries_summable'`. Same statement,
same price; the difference is recorded here per the commission.

Fences: finite matrices only (`Matrix (Fin N) (Fin N) ℂ`), exactly
the level `ThermalClock.lean`'s own objects support. The thermal
instance left open by PreCompensation (thermalization acting
through the clock's flow, not a Schur family) is a different
remainder and is NOT touched by this lemma.

---

## Recount table (strict line-initial `^(theorem|lemma) `, comment-stripped)

| File | Before | After | Δ |
|---|---|---|---|
| BosonicInteraction.lean | 69 | 69 | 0 |
| SpectralActionFinite.lean | 55 | 55 | 0 |
| WightmanAxioms.lean | 1 | 1 | 0 |
| YukawaInteraction.lean | 119 | 119 | 0 |
| FockPackaging.lean | 38 | 38 | 0 |
| FockPackagingBos.lean | 99 | 99 | 0 |
| FockPackagingFerm.lean | 78 | 78 | 0 |
| ThermalClock.lean | 29 | 33 | **+4** |
| **Program total** | **3,257** | **3,261** | **+4** |

Part A moved no count, as commissioned. Part B's delta is exactly
the four new theorems. NO CLAIM beyond the above: this bundle
corrects the record and closes one named S-priced leftover; it
closes no part of any official Millennium statement.
