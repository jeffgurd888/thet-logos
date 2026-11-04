# TCS T1 — THERMAL-PROFILE SEPARATION — LANDING DOSSIER — 2026-11-04

**Verdict: FULL.** Brick T1 of the thermal-charge-separation
scoping dossier (2026-11-04, §3/T1), fired by Jeff's word
("Go", 2026-11-04 09:00 EST). Lane: worktree
`~/workspace/thet-logos-tcs-t1`, branch `tcs-t1-lane`, cut from
main HEAD `d6f17cf` (census 13,248 strict / 488 modules, fence
286/286 at lane base — verified at cut). **Lane commit only:
no integration, no push.** NO CLAIM; dials 0/4.

## What landed

Module: `lean/ThetLogos/ThermalProfileSeparation.lean`
(**strict 18 + 6 defs**, measured by `theorem`/`def` at column 0;
the priced GO band was strict 8–18 — the landing sits exactly at
the band's ceiling, not over it; the two site-entropy corollaries
and the determination iff are what carry it to the ceiling).

The registered T1 statement set, item by item against the
scoping dossier's §3/T1:

1. **The profiled Gibbs weight, closed form.** `profPartition
   β E = ∑ i, exp (−β i · E i)` and `profWeight β E i =
   exp (−β i · E i) / profPartition β E` for a finite seat `ι`,
   energy levels `E : ι → ℝ` and a site-wise inverse-temperature
   profile `β : ι → ℝ`, both entered as data.
   `profPartition_pos`, `profWeight_pos`,
   `sum_profWeight_eq_one` (normalization: the weights sum to
   one for every profile), `isProbWeight_profWeight` (the weight
   is a probability weight in `FiniteEntropy`'s registered
   sense).
2. **The sector population imbalance as an explicit function of
   `(β, E)`.** `sectorPop β E B` (population of a chosen sector
   `B`), `profImbalance β E B = sectorPop β E B − sectorPop β E
   Bᶜ`; closed forms `sectorPop_eq_div` and
   `profImbalance_eq_div` (difference of the two sectors'
   exponential masses over the partition sum); grading form
   `profImbalance_eq_grading_sum`
   (`∑ i, w i · (2·1_B(i) − 1)`); sign criterion
   `profImbalance_pos_iff` (imbalance > 0 iff `B`'s exponential
   mass exceeds `Bᶜ`'s).
3. **Value at constant profile — the SEP-0 static fact,
   recovered, consumed not redefined.** On the `z4` seat:
   `profPartition_const_z4` and `profWeight_const_z4` (at a
   constant profile the profiled objects ARE the landed ladder's
   `z4Partition` / `z4Weight`); `profImbalance_z4_const` (the
   imbalance is SEP-0's registered `chargeSeparationExpectation`
   of the Gibbs weights, via the grading form at the seat where
   `sectorInd chargePumpSectorB` is PUMP-0's `χB`);
   `profImbalance_z4_const_closed` (SEP-1's proved value
   `(exp (−β/2) − 1) / (exp (−β/2) + 1)`, cited from
   `chargeSeparation_static_value`).
4. **Sign/monotonicity of the two-level response — the finite
   Seebeck statics.** `twoLevelProfile βA βB B` (level `βB` on
   `B`, `βA` off it); `sectorPop_twoLevel` (closed form: `B`'s
   mass at its own level over the two sector masses);
   `sectorPop_twoLevel_strictAnti` (for `B` and `Bᶜ` nonempty
   and energies on `B` positive, `B`'s population is strictly
   antitone in `B`'s own inverse temperature: cooling a sector
   strictly empties it, heating it strictly fills it — route:
   `Finset.sum_lt_sum_of_nonempty` on the sector mass, and
   strict monotonicity of `x ↦ x / (x + C)` for `C > 0`).

Beyond the registered four items, two honest strengthenings,
both fenced on the module's face:

5. **Determination at its exact strength**
   (`profWeight_eq_iff`): two profiles induce the same
   normalized weight iff their energy products differ by one
   additive constant, `∃ c, ∀ i, β' i · E i = β i · E i + c`
   (forward via log of weight ratios, the constant being
   `−log (Z' / Z)`; backward by factoring `exp (−c)` through
   the partition sum). Distinct profiles CAN induce the same
   partition — precisely along that family — and the theorem
   marks the boundary.
6. **The induced site entropy, bounded as registered**
   (`siteEntropy_profWeight_nonneg`,
   `siteEntropy_profWeight_le_log_card`): on a product seat the
   profiled weight's site-wise entropy map (T3's object,
   consumed from `SiteEntropyMap`) satisfies `0 ≤ S i ≤
   log (card (X i))`, by `isProbWeight_profWeight` composed
   with the landed `FiniteEntropy` bounds. Consumed, not
   extended.

## Kills — disposition

- **K-TCS-1 (armed, did not fire):** no statement in the module
  has a Gibbs state at a single `β` separating anything by its
  own action. Every theorem is about the weight *family as the
  imposed profile data varies*; at constant profile the module
  recovers SEP-1's static measured imbalance and attributes it
  to nothing.
- **K-TCS-2 (armed, did not fire):** its guard is discharged on
  the face as `profImbalance_twoLevel_diag` — a two-level
  profile with equal levels IS the constant profile and its
  imbalance is the constant-profile imbalance; the gradient
  response is a difference against that value and vanishes at
  zero gradient by construction. The module never claims a
  gradient-driven separation at constant profile. (What does
  not vanish at constant profile is SEP-1's static imbalance —
  a property of the state against the grading, recovered at
  item 3, not a response.)

## Fences standing (SEP-0 ruling, 2026-10-31)

Separation is packaged as a **profile**, never an operator; no
operator acts on any state anywhere in the module. The
separated quantity is population of energy sectors; the word
"charge" appears in no statement — **no charge operator exists
at the seat (K-SEP-3)** and no electromagnetic field object is
constructed or implied (K-PUMP-5). The profile is imposed data,
not generated by the state (K-PUMP-4 discipline). No dynamics,
no transport, no material Seebeck coefficient, no
self-organization, no continuum statement is claimed.

## Verification (lane, this run)

- Targeted build green: `lake build
  ThetLogos.ThermalProfileSeparation` — 3,248 jobs, lake exit
  code 0, module job ✔ (205 s).
- **Zero sorrys** in the module (grep-verified; and the axiom
  audit below excludes `sorryAx` everywhere).
- **Warning-clean for the module:** no warning or error in the
  build log names `ThermalProfileSeparation.lean`; all warnings
  in the log are replays from pre-existing corpus modules
  (`FiniteEntropy`, `ChargePumpPost`, `ChargeSeparationPost`,
  `ModularTime`). No `native_decide` (grep-verified).
- **Axiom audit:** `#print axioms` on all 18 headlines — every
  one on exactly `{propext, Classical.choice, Quot.sound}`.
- No landed module edited: the lane diff is exactly two new
  files (this dossier and the module); `git status` at commit
  time shows no tracked file modified.

## Build notes (for the integrator)

- The module compiles against the shared `.lake` hardlink copy
  of main at `d6f17cf`; integration will need the standard
  root-import + fence admission for the 18 headlines.
- Pin quirks recorded: `div_lt_div_iff` is `div_lt_div_iff₀`
  in Mathlib v4.35.0-rc3; `if_pos`/`if_neg` are deprecated in
  the pin (the module uses `simp [sectorInd, h]`-style proofs
  for indicator values); `omit [DecidableEq ι] in` must precede
  doc comments and was needed on the six partition-cluster
  theorems (`profPartition_pos`, `profWeight_pos`,
  `sum_profWeight_eq_one`, `isProbWeight_profWeight`,
  `profWeight_eq_iff`, `sectorPop_eq_div`).
- The two site-entropy corollaries pass the `Nonempty (∀ i, X i)`
  instance to `isProbWeight_profWeight` explicitly via
  `@isProbWeight_profWeight (∀ i, X i) _ ⟨fun j =>
  Classical.choice (hX j)⟩` — if integration restyles that
  theorem's binders, the `@` calls must be re-counted.

## Grade vs pre-registration

FULL — the registered statement set (closed form; imbalance as
explicit function of `(β, E)`; constant-profile value recovering
SEP-0's static fact by consumption; two-level sign/monotonicity)
landed as scoped, with K-TCS-1/K-TCS-2 armed and unfired, plus
the two fenced strengthenings at items 5–6. NO CLAIM; dials 0/4.

---

## INTEGRATION BLOCK (main tree, 2026-11-04)

Integrated from tcs-t1-lane commit `4cc7101` (lane base `d6f17cf`
= main-tree HEAD at integration). Module + this dossier copied
**byte-identical** (md5 `92a51402…` ThermalProfileSeparation,
`8d9bc784…` dossier; diff-verified). Declaration-level collision
scan of all 24 ThermalProfileSeparation declaration names plus
the module name against the main tree at HEAD found **zero
collisions** (confirmed by `git grep` at HEAD).

- Main-tree targeted build green (**3248 jobs**, matching the
  lane), zero sorrys (zero-sorry source gate PASS, 504 files),
  **module warning-clean** (no warning in the build log names
  `ThermalProfileSeparation`).
- Recount exact: ThermalProfileSeparation **strict 18 + 6 defs**
  (whole-tree 13,935/504 minus frozen remainder 669/15).
- Fence admissions: all **18 theorems** with
  `import ThetLogos.ThermalProfileSeparation` in the **same
  commit** as the module — **FENCE PASS 304/304** (286 → 304),
  every new theorem on exactly {propext, Classical.choice,
  Quot.sound}, no `sorryAx`.
- Ledger record `tcs-t1-thermal-profile-separation` (standing,
  T3, kill_id null — K-TCS-1 / K-TCS-2 did not fire); validator
  PASS, 35 records.
- Census (FILES-TRUE, method of record): **13,248/488 →
  13,266 strict / 489 modules**; README prose census and badge
  both 13,266 / 489, kept equal.
- Integration commit, remote hash, and CI verification are
  recorded in the pipeline log entry for this integration
  (`~/workspace/launch-pipeline-2026-10-29.md`) and in the
  commit message's own record chain. **Dial-ineligible by
  construction** (profile bookkeeping under SEP-0, not an
  object). NO CLAIM; dials 0/4.
