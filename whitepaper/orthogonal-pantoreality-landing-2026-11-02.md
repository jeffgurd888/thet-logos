# ORTHOGONAL PANTOREALITY — scoping and landing dossier (2026-11-02)

**NO CLAIM** — parts of any official Millennium statement closed by this
landing: 0. Dials: 0/4.

Brick: ORTHOGONAL PANTOREALITY (working label; naming is Jeff's hand).
Commissioned by Jeff's fire word, 2026-11-02 21:45 EST. Scoping (frozen
pins, pre-registered kills):
`~/workspace/your_files/pantogram-construction-and-build-scoping-2026-11-02.md`,
Part 2. Foundation: tonight's MIRROR-21 landing (commit 74bfc08 / remote
177a2d1b) — the mirror involution `Θ` on `Fin 21` with unique fixed point
the center `0`, its pullback ring automorphism `Θ̂` on `Fin 21 → ℝ`, and
the fixed-functions equivalence `fixedEquivReps` (11 = 10 mirror pairs +
the unique center).

Dependency note, as scoped: the Mirror-21 SPECTRAL brick was NOT fired,
so pin O3 carries the mirror–operator weld itself, in pointwise operator
form (operators as functions on functions,
`(Lf)(i) = 2f(i) − f(i+1) − f(i−1)` over `Z_21` indices). No matrix form
was built, and Spectral's single-ring kernel pin (its P4) was NOT built
here.

## Verdict: FULL landing at the commissioned scope — including the
## kill-armed stretch pin O4+. No PARTIAL, no kills fired.

## Pins vs outcomes

- **O1 — arm pullbacks commute exactly: FULL (T1).**
  `ThetLogos.thetaHat₁_thetaHat₂ :
  thetaHat₁ (thetaHat₂ f) = thetaHat₂ (thetaHat₁ f)`, by `funext` and
  definitional unfolding — both composites are the double pullback
  `f (Θ a, Θ b)`. Pre-registered kill **K-O1 did not fire.** Each arm
  pullback is moreover a ring automorphism of the grid function algebra:
  `thetaEquiv₁`, `thetaEquiv₂` (`RingEquiv`s), with
  `thetaHatᵢ_involutive`, `thetaHatᵢ_mul`, `thetaHatᵢ_add`,
  `thetaEquivᵢ_apply`. Fixed-point characterizations:
  `thetaHat₁_fixed_iff`, `thetaHat₂_fixed_iff`.

- **O2 — jointly fixed dimension forced at 121 = 11²: FULL (T1).**
  `ThetLogos.jointlyFixedEquivReps :
  {f : GridIndex → ℝ // thetaHat₁ f = f ∧ thetaHat₂ f = f} ≃
  (Fin 11 × Fin 11 → ℝ)`, with
  `jointlyFixedEquivReps_bijective`. Construction: direct product of
  Mirror-21's rep machinery (coordinatewise `repOf₂`/`repEmbed₂`,
  extension `extendReps₂`), not a reuse of `fixedEquivReps` as a black
  box — the joint fixedness has to absorb one mirror per coordinate in
  the extension lemma (`fixed_apply_repEmbed₂_repOf₂`, four cases), and
  the coordinatewise build is the honest form of that. The jointly
  mirror-fixed grid functions are exactly those determined by their
  values on the 11 × 11 representative grid: dimension 121, forced as
  the product of Mirror-21's forced 11.

- **O3 — arm derivatives don't leak; the weld on both arms: FULL (T1).**
  Pointwise operators `lap₁`, `lap₂` (C_21 cycle Laplacian along each
  coordinate), `lapSum = lap₁ + lap₂`.
  - Operator commutation: `lap₁_lap₂_comm : lap₁ (lap₂ f) = lap₂ (lap₁ f)`
    (both sides the same nine-term 3×3-stencil expansion, closed by
    `ring`).
  - Own-mirror welds: `lap₁_thetaHat₁`, `lap₂_thetaHat₂` — via the
    conjugation facts `involution_succ : Θ (i+1) = pred (Θ i)` and
    `involution_pred : Θ (i−1) = succ (Θ i)` (the mirror reverses
    travel on the cycle; the Laplacian is symmetric under the
    reversal, which is why the weld closes only up to the neighbor-swap
    identity `x − y − z = x − z − y`, discharged by `ring`).
  - Cross welds: `lap₂_thetaHat₁`, `lap₁_thetaHat₂` — definitional
    (`rfl`): one coordinate's derivative does not see the other
    coordinate's mirror at all.

- **O4 — joint zero mode exists: FULL (T1).**
  `lapSum_const : lapSum (fun _ => c) = 0` for every constant `c`.

- **O4+ — kernel of `L₁ + L₂` is exactly the constants: FULL (T1).**
  Pre-registered kill **K-O4+ did not fire.**
  `ThetLogos.lapSum_eq_zero_iff :
  lapSum f = 0 ↔ ∃ c, f = fun _ => c`.
  Route, as scoped: the grid energy identity
  `lapSum_energy : ∑ p, f p * (lapSum f) p
    = ∑ p, (f (succ p.1, p.2) − f p)² + ∑ p, (f (p.1, succ p.2) − f p)²`,
  assembled from `lap₁_energy` and `lap₂_energy`. Each arm's identity
  reindexes by the coordinate successor permutation (`succEquiv₁` /
  `succEquiv₂`): the predecessor cross-term equals the successor
  cross-term, and the squared-successor term reindexes to the
  squared-self term. With `(L₁ + L₂) f = 0` the energy is 0; both
  square-sums are nonnegative, hence 0; hence every successor step of
  `f` vanishes in both coordinates; the walk-back lemma
  (`eq_const_of_succ_eq`, via the `shift` iteration
  `apply_succ_iterate_fst` / `apply_succ_iterate_snd` and
  `shift_full : shift x ((21 − x.val) % 21) = TethCenter`) walks each
  coordinate back to the center, so `f` is constant.

- **O5 — T2 companion, joint spectrum: FULL (T2).**
  `python/mirror21_orthogonal_heat.py` runs end-to-end (exit 0).
  Joint spectrum = the 441 pairwise sums of the arm spectrum
  (Kronecker-sum spectrum, exact for `L₁ + L₂`); zero-mode count
  DERIVED = 1 (counted from the floating-point spectrum, not
  inserted); joint gap 0.088854 = the arm gap `4 sin²(π/21)`;
  degeneracy profile: 66 distinct eigenvalues, multiplicities
  [1, then 4s and 8s] summing to 441, max multiplicity 8 (the product
  profile of the arm's [1, 2×10]: doublet+doublet sums give 4, sums
  colliding across pairs give 8, and 1 occurs only at 0). Heat trace
  factorization `K_joint(t) = K_arm(t)²` verified to 1.7e-13. Tier
  discipline on the face of the script: the count is T2; O4+ is the
  T1 statement; they agree on the record and neither is dressed as
  the other. Full output verbatim below.

- **K-OX (gate discipline): respected.** Nothing from the XYZ rhyme,
  the cosmos span, or continuum language entered any pin. The build
  is finite throughout.

## Modules and counts

Counting rule (house): comment-stripped, `theorem`/`lemma` at
column 0 = strict; verified by an independent raw grep (identical).

- `lean/ThetLogos/MirrorTwentyOneOrthogonal.lean` — **strict 18**,
  defs/abbrev 9 (`GridIndex`, `thetaHat₁`, `thetaHat₂`, `thetaEquiv₁`,
  `thetaEquiv₂`, `repOf₂`, `repEmbed₂`, `extendReps₂`,
  `jointlyFixedEquivReps`).
- `lean/ThetLogos/MirrorTwentyOneOrthogonalSpectral.lean` —
  **strict 22**, defs/instance 10 (the grid `Fintype` instance,
  `succ`, `pred`, `succEquiv`, `succEquiv₁`, `succEquiv₂`, `lap₁`,
  `lap₂`, `lapSum`, `shift`).
- Lane-side arithmetic if integrated as-is: strict +40 →
  **12,809**; modules +2 → **464**. (The parent re-derives at the
  ceremony; this dossier does not ship the number.)

## Verification scope (stated plainly)

- Targeted `lake build` of both modules in an isolated worktree
  (branch `orthogonal-pantoreality-lane`, from 74bfc08): green,
  warning-clean, zero sorrys (969 jobs including the foundation).
- `#print axioms` run on **all 40 theorems** of the two modules:
  every axiom set ⊆ {propext, Classical.choice, Quot.sound}; no
  `sorryAx` anywhere. The three pins' headlines:
  `thetaHat₁_thetaHat₂` (O1), `jointlyFixedEquivReps_bijective` (O2),
  `lapSum_eq_zero_iff` (O4+) — each on exactly the full fence trio
  [propext, Classical.choice, Quot.sound].
- Python companion re-run in the worktree: exit 0.
- A full-corpus rebuild is NOT part of this lane's verification; it
  belongs to the parent's landing ceremony, as with Mirror-21.

## What did NOT land, and why

- **The scoping's sketch-level language** ("the imposed figure", the
  Pantogram doctrine of Part 1): T5, Jeff's chair — filed, not built.
  This brick is the finite theorem-shape under item 5 only.
- **Mirror-21 SPECTRAL (the single-ring module)**: not fired, not
  built; its P4 (single-ring kernel) remains scoped separately,
  untouched by this landing.
- **The spectral gap as a theorem** (exact eigenvalue
  `4 sin²(π/21)` in Lean): not a pin of this brick; it remains T2
  (tonight's runs) and FRONTIER for the line, exactly as scoped.
- **A third arm / XYZ weld**: refused at the gate (K-OX), as scoped.

## Seams hit in-lane (owned on the record)

1. `Fintype` for the grid does not synthesize through the
   `ManifoldIndex := Fin 21` def-alias, and the product instance
   needed `Mathlib.Data.Fintype.Prod`; the spectral module carries
   an explicit `Fintype GridIndex` instance.
2. The own-mirror weld goals are not syntactic identities after the
   mirror rewrite — the neighbor terms land in swapped slots; closed
   by `ring`. (The Laplacian's symmetry under travel-reversal is
   exactly this swap.)
3. Sum binders over the grid need the explicit `: GridIndex`
   annotation in the energy lemmas (projection elaboration order).
4. The iteration lemmas were refactored onto a named `shift`
   function: rewrite matching against raw anonymous-constructor
   index terms `⟨(x + n) % 21, by decide⟩` fails (the terms are not
   stable under `implicit` transparency). No statement changed;
   only the formulation.
5. One rewrite-direction slip (`rw [← lapSum_energy]`) caught by the
   compiler and fixed.

## Python output (verbatim, `python/mirror21_orthogonal_heat.py`)

```
========================================================================
ORTHOGONAL PANTOREALITY — joint spectrum of L1 + L2 on the
21 x 21 grid, honest numerics (T2, pin O5).
Companion to ThetLogos.MirrorTwentyOneOrthogonal{,Spectral}.lean (T1).
This script illustrates the finite objects; it proves nothing.
========================================================================
Arm spectrum vs matrix eigensolver: max abs err = 1.554e-15
Joint spectrum size: 441 = 21^2 (pairwise sums lambda_i + lambda_j)

Joint zero modes DERIVED from the spectrum (lambda < 1e-10): 1
  (exactly 1: the constant functions on the grid — counted, not inserted)
Joint spectral gap = 0.088854  (= arm gap 0.088854; exact 4 sin^2(pi/21) = 0.088854)
Joint degeneracy profile: 66 distinct eigenvalues, multiplicities sum to 441, max multiplicity 8
  smallest eigenvalues (value, multiplicity): [(0.0, 1), (0.08885439, 4), (0.17770878, 4), (0.34752245, 4), (0.43637684, 8), (0.6950449, 4)]
  profile in full: [1, 4, 4, 4, 8, 4, 4, 8, 8, 4, 8, 4, 8, 4, 8, 8, 8, 4, 8, 4, 8, 8, 4, 8, 8, 8, 8, 4, 8, 4, 8, 8, 4, 8, 8, 4, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 4, 8, 8, 8, 8, 8, 8, 8, 4, 8, 8, 8, 8, 4, 8, 8, 4, 8, 4]

Joint Laplacian heat trace K(t) = Tr exp(-t(L1+L2))   [NOT a D^2 trace]
  K( 0.001) = 439.240402
  K(  0.01) = 423.792891
  K(   0.1) = 301.567869
  K(   0.5) = 95.667017
  K(   1.0) = 41.973227
  K(   5.0) = 7.206541
Factorization check K_joint(t) = K_arm(t)^2: max abs err = 1.705e-13

TIER NOTE (pin O5, on the record): the zero-mode count above is
T2 — derived from a floating-point spectrum. The T1 statement
'kernel of L1 + L2 is exactly the constants' is pin O4+ of the
Lean brick MirrorTwentyOneOrthogonalSpectral; this script
neither proves it nor upgrades this count to T1.
========================================================================
NO CLAIM; dials 0/4.
```

**NO CLAIM; dials 0/4.**

## CEREMONY — Brick 1 close, 2026-11-03 (parent ceremony, main tree)

This brick's ceremony ran as part of the joint Brick 1 close (Axiom Tet + Partner Sector + Orthogonal Pantoreality) after Jeff lifted all holds ("back to work open the gates and lift the holds").

- Main-tree build: full build green; targeted build of the staged modules green; Python companion re-run exit 0. This brick's three fence admissions (`thetaHat₁_thetaHat₂`, `jointlyFixedEquivReps_bijective`, `lapSum_eq_zero_iff`) passed already in the stopped first run (41/47).
- **Step B stop, on the record:** the ceremony first STOPPED at the axiom-fence step over the OTHER two bricks' registry defect — `lean/scripts/axiom-fence.txt` carried the six AxiomTet/AxiomTetPartner declarations with no `import ThetLogos.AxiomTet` / `import ThetLogos.AxiomTetPartner` lines (registry structural omission; the declarations themselves verified passing in a scratch check with the registry untouched). The parent authorized the exact repair — the two import lines added above their declaration groups — and the registry edit lands in the SAME commit as all the modules it names, this brick's included (the standing CI lesson).
- Fence after repair: **47/47 PASS** — every registered headline on exactly {propext, Classical.choice, Quot.sound}, no sorryAx anywhere.
- Census effect of this brick (recount, method of record): **+40 strict / +2 modules** (18 + 22). Joint ceremony census: **12,875 strict / 13,401 total / 466 modules**, zero sorrys. README updated to the joint figures; ledger record `orthogonal-pantoreality` (validator PASS, 11 records).
- Commit: the Brick 1 ceremony commit of 2026-11-03 — this dossier ships inside it; the hash is recorded in the pipeline log's Brick 1 completion entry.

**Verdict stands: FULL, incl. the O4+ stretch. NO CLAIM; dials 0/4.**
