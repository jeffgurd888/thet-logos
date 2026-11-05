# Rung 9 Task 4, Brick R9T4-B — The Re-Pinned Window Assembly: Landing Dossier (2026-11-04)

**Charter: NO CLAIM.** Nothing here is a claim toward any Millennium
statement, the interacting theory, or the mass gap. **Dials 0/4.**
Parts of the official statement closed by this brick: **0.**

Commission: Jeff's "fire all" (2026-11-04), Rung 9 Task 4 front,
brick R9T4-B. Contract: `rung9-task4-scoping-2026-11-04.md` (§1 re-pin
reading, §3 assembly price S, est. 4–10 strict conditional on audit)
and `rung9-task4-audit-2026-11-04.md` (brick R9T4-A). Lane: isolated
worktree `~/workspace/thet-logos-r9t4b`, branch `r9t4b-lane`, base
main-tree HEAD **78354e0** — the local commit whose tree the
GATE-3-swap integration verified identical to remote **6e77678b**
(the remote hash is not a local object; the tree is the base, and it
matches). Parent integrates.

## Verdict: LANDED FULL in-lane

New module `lean/ThetLogos/PoincareWindowRepinned.lean`:
**5 strict + 2 defs** — inside the audit's re-priced band (S, 4–10).
All six clauses of the re-pinned windows are assembled from landed
theorems; no clause obstructed; no new mathematics. Zero sorry, no
`native_decide`; forced targeted rebuild warning-clean (zero
warning/error lines name the module; wider-log warnings are
pre-existing dependency linter notes); targeted build 3,676 jobs;
`#print axioms` on all five headlines: exactly
{propext, Classical.choice, Quot.sound}, no sorryAx.

## K-R9T4 stands — reaffirmed

The audit (R9T4-A) fired **K-R9T4** (the scoping note's K-R9T4-1,
assembly mismatch): the original window Props
`OneParticleRep_window` (`PoincareAction.lean:293`) and
`SecondQuantization_window` (`PoincareAction.lean:323`) are
discharged **0 of 6 clauses exactly as stated** — every clause is
quantified over the unrestricted `PoincareGroup`, and the two
homomorphism clauses (W1.1, W2.1) write the composition law in the
order that, under Mathlib's `LinearIsometryEquiv.trans`
(`(e₂.trans e₁) x = e₁ (e₂ x)`), is the **anti-homomorphism law**,
while every landed representation law is the homomorphism law over
`RPoincare` in the opposite order. **The original windows are NOT
discharged as stated, permanently.** They are unedited by this brick
(`PoincareAction.lean` untouched in the lane diff); they stand as the
mismatch record. This brick closes only the re-pinned siblings.

## The three corrections (the re-pin, exactly)

1. **Group scope:** `PoincareGroup` → `RPoincare` throughout
   (Lorentz component `RestrictedLorentz` in place of the full
   `LorentzGroup`) — the group every landed representation is over,
   and the restricted pin the original windows' docstrings price as
   hypothesis (iv) without the Props incorporating it.
2. **Composition order:** `U (g₁ * g₂) = (U g₁).trans (U g₂)` →
   `U (g₁ * g₂) = (U g₂).trans (U g₁)` in both homomorphism clauses —
   the homomorphism law as the landed theorems prove it.
3. **W1.3 in a.e. form:** the pointwise representation formula
   (`∀ p`, equality at every shell point — verdicted by the audit
   **not closeable for an `L²` carrier**, since evaluation of a class
   at a point is a.e.-only) becomes equality of functions
   `=ᵐ[massShellMeasure m hm]`. Naming the measure forces one
   signature delta beyond the three corrections: the re-pinned
   one-particle Prop takes `hm : 0 < m`, which the original did not
   have. Recorded here so the delta is auditable.

One notation-level identification, not a correction: W2.2. The landed
identity laws end in `1` (the `One` of `≃ₗᵢ`); the window writes
`LinearIsometryEquiv.refl`. For `≃ₗᵢ`, `1` is definitionally `refl`
(verified `rfl` at both carriers); the assembly discharges R2.2 by
`Eq.trans` with `rfl` — a one-step shim, no content gap (the audit's
own grading).

## The landed statements

* `OneParticleRep_window_rp` (def) — re-pinned one-particle window:
  `(m : ℝ) (hm : 0 < m) (h) [NormedAddCommGroup h]
  [InnerProductSpace ℂ h] [CompleteSpace h]
  (U1 : RPoincare → (h ≃ₗᵢ[ℂ] h)) (wavefn : h → massShell m → ℂ)
  (planeWave : Minkowski → massShell m → ℂ)
  (shellAct : RPoincare → massShell m → massShell m) : Prop`, body
  R1.1 ∧ R1.2 ∧ R1.3 as in the corrections above. Each corrected
  clause is quoted beside its original in the def's docstring.
* `SecondQuantization_window_rp` (def) — re-pinned Fock window:
  same `FockMarker` shape as the original, `RPoincare` in place of
  `PoincareGroup`, body R2.1 ∧ R2.2 ∧ R2.3.
* `OneParticleRep_window_rp_proved`, `SecondQuantization_window_rp_bosonic`,
  `SecondQuantization_window_rp_fermionic` — the assemblies.
* `gammaFockU1_eq_gammaFock_shellU1`, `gammaFockFU1_eq_gammaFockF_shellU1`
  — the Γ-of-U1 link as named `rfl` theorems (see the `_U1` note).

Instantiations: `h := shellLp m hm` (the mass-shell `L²` space,
`FockPackaging.lean:70`); `wavefn` := the `Lp` coercion to a shell
function; `planeWave := phase` (`MassShellMeasure.lean:797`);
`shellAct g := shellActR g.lor⁻¹ m hm` (the window leaves `shellAct`
a free parameter; its docstring formula is `ψ(Λ⁻¹p)`);
`Fock := ⟨BosonicFockLim⟩` / `⟨FermionicFockLim⟩`;
`vac := boseVacLim` / `fockVacLim`. The carrier instances the window
demands on `Fock.carrier` synthesize through the marker projection at
both carriers (probe-verified before the build).

## Clause-by-clause assembly map

| Re-pinned clause | Discharging theorem | Citation |
|---|---|---|
| R1.1 homomorphism (corrected order) | `shellU1_mul` | `FockPackaging.lean:208` |
| R1.2 identity | `shellU1_one` (lands in `refl` form on the nose) | `FockPackaging.lean:231` |
| R1.3 formula, a.e. form | `shellU1_coeFn_ae`, RHS read through `oneParticleFun`'s definition | `FockPackaging.lean:194`; `MassShellMeasure.lean:878` |
| R2.1 homomorphism, bosonic | `gammaFockU1_mul` | `FockPackagingBos.lean:2204` |
| R2.1 homomorphism, fermionic | `gammaFockFU1_mul` | `FockPackagingFerm.lean:1654` |
| R2.2 identity, bosonic | `gammaFockU1_one` + `1 = refl` by `rfl` | `FockPackagingBos.lean:2213` |
| R2.2 identity, fermionic | `gammaFockFU1_one` + `1 = refl` by `rfl` | `FockPackagingFerm.lean:1663` |
| R2.3 vacuum, bosonic | `gammaFock_vacuum` at `W := shellU1 m hm g`, via the definition of `gammaFockU1` | `FockPackagingBos.lean:2179` (def `:2197`) |
| R2.3 vacuum, fermionic | `gammaFockF_vacuum` at `W := shellU1 m hm g`, via the definition of `gammaFockFU1` | `FockPackagingFerm.lean:1627` (def `:1647`) |

All six clauses: **assembled**. No clause needed more than assembly;
the stop-line (band breach at 12 strict) was not approached — the
landing is 5 strict.

## The `_U1` note (audit §2)

`SecondQuantization_window`'s parameter `_U1` is unused in its body:
no conjunct relates `GammaU` to `_U1`; the tensor-factor formula
`Γ(U1)(ψ₁ ⊗ ⋯ ⊗ ψₙ) = U1ψ₁ ⊗ ⋯ ⊗ U1ψₙ` appears only in its
docstring. The packaged actions *are* built from `shellU1` by
definition, so the link lives in the definitions, not in the Prop.
The re-pinned sibling **mirrors the original's shape** — `_U1`
present and unused — because the window is a statement about a
packaged action's group law and vacuum invariance, and widening its
content would exceed the audit's three corrections. The link is
stated in Lean in this brick as the two named `rfl` theorems
`gammaFockU1_eq_gammaFock_shellU1` and
`gammaFockFU1_eq_gammaFockF_shellU1`.

## Strong continuity — recorded in the dossier, a conjunct of NEITHER window

Strong continuity is a conjunct of **neither** the original windows
(docstring prose only) **nor** the re-pinned ones, and this brick
does not state a joint-continuity Prop: no topology on `RPoincare`
exists anywhere in-tree, and the choice of topology is a pin
decision, not assembly (scoping §2(c): the residue belongs to the
re-pin, not to these windows). What is landed (background, not
conjuncts): the corpus's narrower window `StrongContinuity_window`
(`MassShellMeasure.lean:976` — translations only, function level),
discharged by `strongContinuity_window_proved`
(`TranslationContinuity.lean:196`); packaged subgroup continuity
`shellU1_translation_tendsto` (`FockPackaging.lean:248`),
`shellU1_lorentz_tendsto` (`LorentzContinuity.lean:744`),
`gammaFockU1_lorentz_tendsto` (`FockLorentzBos.lean:222`),
`gammaFockFU1_lorentz_tendsto` (`FockLorentzFerm.lean:206`). The
narrower window's price, from `MassShellMeasure.lean`'s own face:
for translations, strong continuity is the dominated convergence
theorem — `tendsto_lintegral_of_dominated_convergence` applied to
`Fₙ(p) = ‖e^{iaₙ·p} − 1‖ₑ² · ‖ψ(p)‖ₑ²`, converging pointwise by
continuity of `exp`, dominated by `4‖ψ‖² ∈ L¹`; for the Lorentz part,
strong continuity needs density of `C_c` in `L²` and uniform
continuity on compacts — a longer analysis argument. **Joint**
strong continuity of the packaged action in a topology on the full
`RPoincare` is stated here as an **OPEN window at that price**:
research-scale (scoping §3(c)), not FRONTIER, not proved, not
claimed by this brick.

## Scope fence

K-R9T4 stands — the original windows are NOT discharged as stated,
permanently; this brick closes only the re-pinned siblings.
W1.3 in its pointwise form survives every re-pin: not closeable for
an `L²` carrier. Task 4 as literally stated in 2026-10 remains NOT
CLOSEABLE (its finite-mode boost item is a proved structural
negative). Task 4's continuum content — joint strong continuity of
the packaged action, and the interacting theory — remains
FRONTIER / OPEN, untouched by this brick. Nothing here touches the
mass gap, the gauge line (LayerKernelPos, GATE-3), or any dial.
**NO CLAIM; dials 0/4.**

## Deviations

* **Base commit naming:** the commission named main-tree HEAD
  6e77678b; that hash is the *remote* commit and is not a local
  object. The lane is built on local HEAD **78354e0**, whose tree
  the GATE-3-swap integration verified identical to the remote
  tree. Content deviation: none.
* **Kill status:** no new kills; **K-R9T4 reaffirmed** (not
  re-fired — it fired at the audit, R9T4-A, and this brick's whole
  design presupposes it).

---

## ADDENDUM (2026-11-04, integration): THE DOUBLE-`Config` LANDMINE AND ITS RESOLUTION

The first integration attempt of this brick stopped at the fence step —
before any commit, push, or ledger record — on a **pre-existing corpus
landmine, not caused by this brick**: `ThetLogos.Config` was defined
**twice** in the corpus —

* `lean/ThetLogos/BosonicFock.lean:58` —
  `abbrev Config (d : ℕ) := Finsupp (Fin d) ℕ` (the bosonic
  occupation-configuration type), and
* `lean/ThetLogos/LatticeGauge.lean:182` —
  `abbrev Config (Λ : Type*) (G : Type*) : Type _ := (Λ × Fin 4) → G`
  (the gauge configuration).

The two lineages cannot cohabit one Lean environment in either import
order (pair test reproduced `environment already contains
'ThetLogos.Config'` both ways). The axiom fence's single check file
loads the LatticeGauge lineage (via the Span3 modules); admitting this
Fock-lineage module made the whole fence run error out for all
declarations, and CI runs the same runner — appending would have turned
CI red corpus-wide. The registry had never before admitted a
Fock-lineage module. This brick's own verification was never in doubt:
builds green, census exact, and its 5 headlines PASS 5/5 against a
single-lineage registry, each on exactly {propext, Classical.choice,
Quot.sound}, no sorryAx.

**Resolution — CONFIG DISAMBIGUATION HYGIENE BRICK** (its own commit,
landed and CI-verified before this integration proceeded): the
BosonicFock lineage's `Config` was renamed **`BosonicConfig`**
(collision scan: zero pre-existing `BosonicConfig` in the tree); the
LatticeGauge `Config` is untouched. 12 files edited, 331 line-changes,
every one the single identifier rename (definition plus all
Fock-lineage references; per-file lineage decided by imports and by the
one-argument `Config d` shape; no file outside the BosonicFock lineage
edited; no dual-lineage importer exists). Post-rename verification:
full `lake build` green (3325 jobs), targeted
`ThetLogos.PoincareWindowRepinned` build green (3676 jobs), axiom
fence re-run at HEAD registry **PASS 429/429** — the rename admits and
removes no theorems (census unchanged by the rename alone). Hygiene
commit: local `296e935` → delta push → remote `62bda260` (tree
`fa32f2fa`, verified identical); **lean-ci run 41938264956 on
62bda260 completed success**.

**This integration then completed exactly as commissioned.** Census
(whole-tree recount post-rename, module included): whole-tree
14,065/513 − frozen remainder 669/15 = **13,396 strict / 498 modules**
(module = 5 strict exact); zero-sorry source gate PASS (513 files);
fence admissions (the 5 headlines) with `import
ThetLogos.PoincareWindowRepinned` in the same commit as the module —
**FENCE PASS 434/434** (429 → 434). Ledger record
`rung9-task4-repin-assembly` (standing, T3, kill_id K-R9T4); validator
PASS, 44 records. README prose census and badge updated to 13,396 /
498 (kept equal).

**Byte-identity:** module + dossier copied from lane `4a7943f`
byte-identical (module md5 `654855f6…`, dossier md5 `c2bfb9e9…`,
diff-verified against the lane copies) — **no byte-identity deviation
occurred**: this module contains no `Config` reference, so the rename
did not touch its text, and it builds green against the renamed tree.
The sole content divergence from the lane dossier is this addendum
itself. K-R9T4 stands; NO CLAIM; dials 0/4.
