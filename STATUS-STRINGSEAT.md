# STATUS-STRINGSEAT — StringSeatPin (lane grade)

**NO CLAIM. Dial-ineligible. Dials 0/4.**
Scope (the pin of record):
`~/workspace/your_files/string-seat-pin-scope-2026-11-13.md`
(Zero's string thread, 2026-11-13 19:04–19:10 EST;
commissioned "scope it" 19:10 EST; bench tail after
AQFT-2). Module `ThetLogos.StringSeatPin`
(`lean/ThetLogos/StringSeatPin.lean`), branch
`stringseat` in `~/workspace/thet-logos-og0`.

## Step 0 — price / confirm (2026-11-15)

**Host choice: og0, new branch `stringseat` off
`aqft2` tip 7446cc4.** Evidence, all firsthand:

- The finite-Gibbs machinery the seat reuses is
  `ThetLogos.ModularVariance` (namespace
  `ThetLogos.ModularVariance`): `partSum`,
  `gibbsProb`, `gibbsExpect`, `meanEnergy`,
  `varEnergy` over a general finite index type
  `{ι : Type*} [Fintype ι] [Nonempty ι]`, with
  `partSum_pos`, `gibbsProb_pos`, `sum_gibbsProb`,
  `varEnergy_pos_iff` (`0 < Var_β(E) ↔ ∃ i j, E i ≠ E j`),
  `hasDerivAt_partSum` and `hasDerivAt_meanEnergy`
  (`d/dβ ⟨E⟩_β = −Var_β(E)`) already proved. The
  configuration type `Fin n → Fin (k+1)` carries the
  needed `Fintype`/`Nonempty` instances natively.
- `hotcold` is an ancestor of `aqft2`
  (`git merge-base --is-ancestor`), so this branch's
  tree also carries `HotColdLimits`,
  `ColdHeatDualityPin` (`coldPartition`/`coldWeight`),
  `GibbsSpan`, `ColdLimitConcentration`,
  `PartnerThermal` — verified in HEAD by
  `git cat-file -e` for each. Oleandisk check:
  `lean/.lake/build/lib/lean/ThetLogos/GibbsSpan.olean`
  present (the lake project root is `lean/`).
- `GibbsGapFloor` (GAPFLOOR-1's general Hermitian
  form, integrated in master via chunk 4, 2026-11-12)
  is NOT in this branch's ancestry. Per the GapLine /
  HotColdLimits precedent, S-4 is proved at this
  configuration seat and `GibbsGapFloor` is cited by
  name on the module's face, not imported.
- Ground check: `lake build ThetLogos.HotColdLimits
  ThetLogos.ModularVariance` on the fresh branch —
  PASS, complete log `build-stringseat-groundcheck.log`
  (9,003 jobs, BUILD_EXIT:0); oleans on disk
  (HotColdLimits 220,984 B, ModularVariance
  472,624 B); ModularVariance's own axiom trailer in
  the log shows exactly the standard three.

**Model (per the scope's seat):** bend states
`Fin (k+1)` with `0` = straight ahead; a configuration
is `c : Fin n → Fin (k+1)`; link bend cost is `0` at
the straight state and `1` at any bent state; energy
= total bend content `∑ i, bendCost (c i)`. The
straight configuration `fun _ => 0` is the unique
energy minimiser (energy `0`); every other
configuration has energy `≥ 1` (least bend cost `1`).
Gibbs weights are `ModularVariance.gibbsProb` at this
energy — the corpus's own finite-Gibbs machinery, no
parallel apparatus.

**Brick plan** (small-brick rule, ≤ ~10 new
declarations per build; bank per brick):

- Brick 1 (§1): the model — `bendCost`, `bendEnergy`,
  `straightConfig` + ground API (`bendCost_nonneg`,
  `bendEnergy_nonneg`, `bendEnergy_straightConfig`,
  `bendEnergy_eq_zero_iff`, `one_le_bendEnergy`,
  `bendEnergy_le`).
- Brick 2 (§2): S-3 hot uniformity + S-1 cold
  straightens (general helper
  `partSum_strictAnti_of_nonneg` via
  `hasDerivAt_partSum` and the mean value theorem;
  ground probability `= (partSum)⁻¹`, strictly
  increasing).
- Brick 3 (§3): S-2 heat excites (general helper:
  `meanEnergy` strictly antitone when the energy is
  nonconstant, via `hasDerivAt_meanEnergy` +
  `varEnergy_pos_iff`; applied at the seat).
- Brick 4 (§4): S-4 cold concentration — total
  excited weight `≤ (card − 1) · e^{−β}` for
  `β ≥ 0`, the GAPFLOOR-1 shape at this seat
  (cf. `HotColdLimits.offGround_weight_le`).
- Brick 5 (§5): S-5 the pair card — at `β = 0` no
  selection (S-3); at every `β > 0` the straight
  configuration is strictly the most probable, and
  the two states are different functions on the same
  configuration set.

Count note: the scope estimated 2 defs + 4–7 strict
for the menu items S-1–S-5 themselves; the model API
lemmas and the two general strictness helpers are
infrastructure on top of that estimate and are
counted openly in the brick ledger.

## Fidelity fences (from the scope's face, carried
onto the module's face)

- The pin's "knot" is BEND CONTENT — the countable
  shadow — NOT topological knot type.
  K-STRING-KNOT armed: any statement from this seat
  about actual knots is void.
- The pin is a finite toy; it does not model a
  physical string's mechanics. K-STRING-PHYS armed.
  No gravity (K-DENSITY-GRAV governs). No
  falling/drag/packing, no chord geometry, no
  continuum filament.
- Constructed-target exposure: the correspondence
  to the source picture is by construction of the
  model, disclosed wherever the pin is cited.
- NO CLAIM; dial-ineligible.

## Brick ledger

### Brick 1 — §1 the model — BANKED 2026-11-15

9 declarations (3 defs + 6 strict theorems), sorry 0:
`bendCost` (def), `bendEnergy` (def),
`straightConfig` (def), `bendCost_nonneg`,
`bendCost_eq_zero_iff`, `bendEnergy_nonneg`,
`bendEnergy_straightConfig`, `bendEnergy_eq_zero_iff`
(the straight configuration is the unique energy
minimiser), `one_le_bendEnergy` (least bend cost 1).

- Probe: probe-stringseat1.lean; R1 failed on one
  mechanical point (the `bendEnergy_straightConfig`
  statement needed a type ascription to pin the
  section variables), R2 clean (LEAN_EXIT:0).
- Targeted build PASS, complete log
  `build-stringseat-b1.log` (3,590 jobs,
  BUILD_EXIT:0); olean 67,928 B on disk.
- Axiom check `axioms-stringseat-b1.log`: 6/6 on
  exactly the standard three [propext,
  Classical.choice, Quot.sound]; no sorryAx.
- Hash check: MATCH — disk sha256 `24d86d63…`
  = committed blob sha256 `24d86d63…` (mechanical,
  one command, at commit 87b634b).

### Brick 2 — §2 hot uniformity (S-3) + cold straightens (S-1) — BANKED 2026-11-15

5 strict theorems, sorry 0:
`partSum_strictAnti_of_nonneg` (general helper:
nonnegative energies with a positive level have a
strictly antitone partition sum — via
`ModularVariance.hasDerivAt_partSum` and
`strictAnti_of_deriv_neg`), `card_config`
(`#configurations = (k+1)^n`), `gibbsProb_zero`
(**S-3**: at `β = 0` every configuration's Gibbs
weight is `(card)⁻¹`), `gibbsProb_straightConfig_eq`
(ground probability `= (partSum)⁻¹`),
`cold_straightens` (**S-1**: the straight
configuration's Gibbs probability is `StrictMono`
in `β`, for `0 < n`, `0 < k`).

- Probe: probe-stringseat2.lean; R1–R3 failed on
  mechanical points only, statements never weakened:
  (R1) `Finset.sum_pos` in this pin is the
  all-strict form — the ≤+∃ form is
  `Finset.sum_pos'`; (R1–R2) a bare `bendEnergy`
  passed to a `ModularVariance` function leaves its
  section implicits as unsolved metavariables in any
  standalone type — pinned by type ascription
  `(bendEnergy : (Fin n → Fin (k + 1)) → ℝ)` at those
  sites; (R3) the `StrictMono` goal keeps its lambda
  un-beta-reduced — a `show` fixes the rewrite
  pattern. R4 clean (LEAN_EXIT:0).
- Targeted build PASS, complete log
  `build-stringseat-b2.log` (3,590 jobs,
  BUILD_EXIT:0); olean 170,232 B on disk.
- Axiom check `axioms-stringseat-b2.log`: 5/5 on
  exactly the standard three; no sorryAx.
- Hash check: MATCH — disk sha256 `ab59b2af…`
  = committed blob sha256 `ab59b2af…` (mechanical,
  one command, at commit 5e0032c).

### Brick 3 — §3 heat excites (S-2) — BANKED 2026-11-15

2 strict theorems, sorry 0:
`meanEnergy_strictAnti_of_nonconstant` (general
helper: at a nonconstant energy the mean energy is
strictly antitone in `β` — via
`ModularVariance.hasDerivAt_meanEnergy`,
`d/dβ ⟨E⟩ = −Var(E)`, and
`ModularVariance.varEnergy_pos_iff`),
`heat_excites` (**S-2**: the Gibbs expected bend
content is `StrictAnti` in `β`, for `0 < n`,
`0 < k`).

- Probe: probe-stringseat3.lean clean on R1
  (LEAN_EXIT:0).
- Targeted build PASS, complete log
  `build-stringseat-b3.log` (3,590 jobs,
  BUILD_EXIT:0); olean 185,024 B on disk.
- Axiom check `axioms-stringseat-b3.log`: 2/2 on
  exactly the standard three; no sorryAx.
- Hash check: MATCH — disk sha256 `edf01dbd…`
  = committed blob sha256 `edf01dbd…` (mechanical,
  one command, at commit e711153).

### Brick 4 — §4 cold concentration (S-4) — BANKED 2026-11-15

1 strict theorem, sorry 0: `cold_concentration`
(**S-4**: for `β ≥ 0`, the total Gibbs weight on
non-straight configurations is
`≤ ((card : ℝ) − 1) · e^{−β}` — GAPFLOOR-1's bound
on the configuration spectrum, proved at this seat;
`GibbsGapFloor` cited by name, per the Step 0
record).

- Probe: probe-stringseat4.lean; R1 failed on two
  mechanical points (this pin's
  `le_mul_of_one_le_left` yields the `a * b` order —
  the `b * a` form is `le_mul_of_one_le_right`; this
  pin's `Finset.card_sdiff` is the intersection
  form, no subset hypothesis), R2 clean
  (LEAN_EXIT:0). Statements never weakened.
- Targeted build PASS, complete log
  `build-stringseat-b4.log` (3,590 jobs,
  BUILD_EXIT:0); olean 220,480 B on disk.
- Axiom check `axioms-stringseat-b4.log`: 1/1 on
  exactly the standard three; no sorryAx.
- Hash check: MATCH — disk sha256 `5b2a2c40…`
  = committed blob sha256 `5b2a2c40…` (mechanical,
  one command, at commit 7e32fa0).

### Brick 5 — §5 the pair card (S-5) — BANKED 2026-11-15 — CAMPAIGN COMPLETE

2 strict theorems, sorry 0:
`gibbsProb_straightConfig_gt` (S-5 selection half:
at every `β > 0` the straight configuration is
strictly more probable than any bent configuration),
`gibbsProb_pair_ne` (**S-5**: the `β = 0` Gibbs
state and any `β > 0` Gibbs state are different
functions on the same configuration set — they
differ at the straight configuration, since
`partSum β < card` for `β > 0`).

- Probe: probe-stringseat5.lean; R1 was killed by
  a service restart mid-run (empty log — NO
  VERDICT, logged as such and re-run from scratch);
  R2 found one mechanical point (`div_lt_div_right`
  is unknown in this pin — the step now goes through
  `div_lt_iff₀` + `one_div_mul_cancel`), R3 clean
  (LEAN_EXIT:0). Statements never weakened.
- Targeted build PASS, complete log
  `build-stringseat-b5.log` (3,590 jobs,
  BUILD_EXIT:0); olean 262,192 B on disk.
- Axiom check `axioms-stringseat-b5.log`: 2/2 on
  exactly the standard three; no sorryAx.
- Hash check: MATCH — disk sha256 `56a39903…`
  = committed blob sha256 `56a39903…` (mechanical,
  one command, at commit db2f5dc).

## Campaign completion (2026-11-15)

**StringSeatPin COMPLETE at lane grade: 19
declarations (3 defs + 16 strict theorems),
sorry 0** — mechanical count over the banked file.
The full menu landed: S-1 `cold_straightens`,
S-2 `heat_excites`, S-3 `gibbsProb_zero`,
S-4 `cold_concentration`, S-5
`gibbsProb_straightConfig_gt` + `gibbsProb_pair_ne`,
on the §1 model (Brick 1) with two general Gibbs
helpers (Bricks 2–3) proved once over
`ModularVariance`'s machinery and applied at the
seat. Every brick: targeted build PASS from a
complete log, olean verified on disk, axiom check
on exactly [propext, Classical.choice, Quot.sound]
(16/16 theorems across the five axiom logs), hash
MATCH disk == blob at each code commit. Branch
`stringseat` tip db2f5dc (code) — awaits parent
integration like the other lane modules; NOT
root-imported, census of record unchanged.

Count vs the scope's estimate (2 defs + 4–7 strict
for the menu): the overage is the third def
(`straightConfig`), the §1 ground API (5 theorems
the menu's proofs stand on), the two general
strictness helpers, `card_config`, and
`gibbsProb_straightConfig_eq` — infrastructure,
counted openly here and in the brick ledger.

Fences stand as on the module's face: bend content
is the countable shadow, NOT knot type
(K-STRING-KNOT armed); finite toy, no physical
string mechanics (K-STRING-PHYS armed); no gravity
(K-DENSITY-GRAV governs); constructed-target
exposure disclosed. NO CLAIM; dial-ineligible;
dials 0/4.
