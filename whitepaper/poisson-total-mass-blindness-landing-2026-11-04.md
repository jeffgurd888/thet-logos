# SHADOW-TEST-1 — the total-mass-blindness decision, landed

## VERDICT: FULL — the total-mass-blindness decision lands in the registered class shape; SR-4 is closed at T1 and SR-5's ceiling is kernel-fenced. Dial-ineligible by pre-registration: Dial 2 = 0.

**Item:** SHADOW-TEST-1 (working label — Jeff names), the cheapest
discriminating test of the Shadow Program, fired by Jeff's tap
2026-11-04 09:38 EST ("Build both priced bricks") as the first of
the two queued shadow bricks (SR-5 is the second, a separate lane).
Governing scoping: `~/workspace/your_files/dial2-shadow-scoping-2026-11-04.md`
§4 (registered statement class, price, outcome dispositions),
inside the gravity-object audit
(`gravity-object-audit-scoping-2026-11-04.md`: CT-1, P-D2).
Consumes T2 (`ThermalChargePoisson`, landed FULL) at its exact
landed shapes; no landed module edited.

Module: `lean/ThetLogos/PoissonTotalMassBlindness.lean` (NEW).
Lane: `shadow1-lane`, isolated worktree `~/workspace/thet-logos-shadow1`,
cut from main HEAD `d348bd5` (census 13,266 strict / 489 modules;
fence 304/304 — verified at cut). Targeted build green (**3,318
jobs**), **ZERO sorrys**, module **WARNING-CLEAN** (no build warning
names this module; the warnings in the build log belong to
pre-existing corpus dependency modules), **no `native_decide`**.
**Measured strict count: 18 theorems + 5 defs** — inside the priced
S–M band of **8–18**, **at its ceiling, not exceeded** (flagged per
instructions: the count sits at the top of the band because each of
the three class dialects — field, flow, projection — carries its
own class theorem *and* its own decision corollary, plus the
projection's fiber characterization; nothing was padded, and no
statement was merged to game the count). Axiom audit
(`#print axioms`, run against the built module): **all 18
theorems depend on exactly `{propext, Classical.choice,
Quot.sound}`** — no `sorryAx`, nothing outside the standard trio.
NO integration, NO push — lane commit only.

## What landed

**The projection (§1 of the module)** — `meanVal g = (∑ i, g i) /
card V`; `meanSub g = fun i => g i - meanVal g` (the
mean-subtracted source `ρ − ρ̄`):

| Declaration | Content |
|---|---|
| `meanVal_const` / `meanVal_add_const` | the mean of a constant is the constant; the mean shifts with a constant shift of the source |
| `sum_meanSub_eq_zero` | the projection always lands in T2's compatibility class: `∑ i, meanSub g i = 0`, for every finite `V` (empty seat discharged inside the proof) |
| `meanSub_of_sum_eq_zero` | the projection fixes mean-zero sources |
| **`meanSub_add_const`** | **the invariance: `meanSub (fun i => g i + c) = meanSub g`** — a constant shift (a pure change of total) is invisible to the projection |
| `meanSub_const` | a constant source projects to zero |
| `meanSub_meanSub` | the projection is idempotent |
| `meanSub_eq_iff` | fibers characterized: `meanSub g = meanSub g'` iff `g'` differs from `g` by a constant — the fibers are exactly the total-mass directions |

**T2's canonical output (§2)** — `poissonPotential` (a chosen
potential for `meanSub g`, by T2 existence via
`Classical.choose`; `laplacianOp_poissonPotential` is its spec),
`poissonField = dropVec ∘ poissonPotential`, `poissonFlow =
flowVec w ∘ poissonPotential`. The choice is immaterial: §3 rests
on T2's uniqueness of `dropVec`/`flowVec`, not on the choice.

**Dependence (§3)** — `poissonField_eq_of_meanSub_eq`,
`poissonFlow_eq_of_meanSub_eq`: the field and flow depend only on
the mean-subtracted source. `poissonField_add_const`: the field is
invariant under constant source shifts.

**The decision (§4)** — the class theorems at full strength, for
an **arbitrary** quantity `F` (any codomain) of the class data:

| Declaration | Content |
|---|---|
| `fieldFactor_add_const` | `F (poissonField (g + c)) = F (poissonField g)` for all `F, g, c` |
| `flowFactor_add_const` | the same for the Ohm flow |
| `meanSubFactor_add_const` | the same for the projection — the equivalent class dialect, since the field factors through it |
| `poissonField_const` | a uniform source (pure total mass, zero contrast) has **identically zero field** |
| `not_exists_fieldFactor_detects_totalMass` | **the decision**: no `F`, source `g`, and nonzero shift `c` exist with `F (poissonField (g + c)) ≠ F (poissonField g)` — *detecting total mass is impossible inside the class* |
| `not_exists_meanSubFactor_detects_totalMass` | the decision at the projection |

## The class, pinned exactly (no silent widening, no silent narrowing)

The scoping registers the class as "any construction factoring
through the pair (φ, dφ) (equivalently, through the mean-zero
source `ρ − ρ̄`, by T2's uniqueness mod constants)". The module
formalizes exactly that, in the two dialects the landed API
supports: arbitrary functions of the canonical field/flow data,
and arbitrary functions of the mean-subtracted source. One
boundary is stated on the module's face: **the potential `φ`
itself is not a class member's legitimate input** — `φ` is unique
only up to constants, so a bare function of a chosen `φ` is not a
quantity of the seat. What *is* unique (`dφ`, the flow, the
projection) is in, at full ∀-strength over `F`. A construction
that additionally reads the graph, the weights, or the
unprojected source does not factor through T2's output and is not
claimed either way — the scoping already names that escape
(source-dependent geometry) as SR-6's pin (i); this theorem
neither covers it nor pretends to.

## Outcome dispositions (scoping §4, executed as registered)

- **Lands (the expected outcome):** the invariance holds for the
  full registered class. Therefore:
  - **SR-4 (Poisson post-processing) is CLOSED at T1,
    permanently.** No quantity built from T2's output can satisfy
    the isolated-mass signature (SH-7 + SH-9 at Newtonian scope):
    it cannot respond to total mass at all. This is the
    pre-registered kill **K-SR-4**, fired by theorem.
  - **SR-5's ceiling is kernel-fenced:** the thermal-source
    composite, whatever source it feeds T2, is seen by T2 only as
    a contrast; its output potential inherits this blindness.
  - Any future Dial-2 candidate is now *proved* to require
    structure beyond (φ, dφ) — a variable geometry (SR-6), a
    boundary/open seat, or a new source channel — exactly the
    FRONTIER set the scoping left open.
  - Dividend to T2: this module is the precise statement of what
    T2's output contains.
- **The failure branch did NOT occur.** No leak exists inside the
  registered class: no T2-output quantity sees the constant. (Had
  invariance failed, the witness would have been reported at full
  rank as a class-definition leak pointing at SR-6, or — if it had
  contradicted T2's uniqueness — as a reopening of T2's audit.
  Neither happened; T2's uniqueness is what the proof consumes.)
- **Pre-registered Dial-INELIGIBLE, honored:** this is a fence
  theorem about the shadow, not an object. It seats no gravity,
  defines no response law, and moves no dial under any outcome.
  **Dial 2 = 0. NO CLAIM; dials 0/4.**

## Fences (standing, on the module's face)

Determination results only — no dynamics, no self-organization.
No operator acting on a thermal density matrix separates charge
by its own action (SEP-0); no charge operator and no
electromagnetic field object is claimed at any seat (K-SEP-3,
K-PUMP-5). β appears nowhere. Finite graph statics only.

*End of landing dossier. Lane artifact only — integration is the
parent's step, in its own commit, with fence admissions and the
ledger record made there.*

---

## INTEGRATION BLOCK (main tree, 2026-11-04)

Integrated from shadow1-lane commit `7051849` (lane base `d348bd5`
= main-tree HEAD) onto main-tree HEAD `d348bd5`. Module + this
dossier copied **byte-identical** (md5 `46038274…`
PoissonTotalMassBlindness, `9186a6ba…` dossier; diff-verified).
Declaration-level collision scan of all 23 module declaration
names plus the module name against the main tree at HEAD found
**zero collisions** (`git grep` at HEAD).

- Main-tree targeted build green (**3,318 jobs**, matching the
  lane), zero sorrys (zero-sorry gate PASS, 505 files), **module
  warning-clean**.
- Recount exact: **strict 18 + 5 defs** (whole-tree 13,953/505
  minus frozen remainder 669/15).
- Fence admissions: all **18 theorems** with
  `import ThetLogos.PoissonTotalMassBlindness` in the **same
  commit** as the module — **FENCE PASS 322/322** (304 → 322),
  every new theorem on exactly {propext, Classical.choice,
  Quot.sound}, no `sorryAx`.
- Ledger record `shadow-test-1-poisson-total-mass-blindness`
  (standing, T3, kill_id `K-SR-4` — fired by theorem: SR-4 closed
  at T1 permanently; SR-5's ceiling kernel-fenced); validator
  PASS, 36 records.
- Census (FILES-TRUE, method of record): **13,266/489 →
  13,284 strict / 490 modules**; README prose census and badge
  both 13,284 / 490, kept equal.
- Integration commit, remote hash, and CI verification are
  recorded in the pipeline log entry for this integration
  (`~/workspace/launch-pipeline-2026-10-29.md`). Pre-registered
  Dial-INELIGIBLE honored: Dial 2 = 0. NO CLAIM; dials 0/4.
