# SR-5 — the thermal-source composite, landed

## VERDICT: FULL — the registered composite and its ceiling land as scoped. Dial-ineligible by pre-registration: Dial 2 = 0.

**Item:** SR-5 (working label — Jeff names), the thermal-source
composite of the Shadow Program, fired by Jeff's tap 2026-11-04
09:38 EST ("Build both priced bricks") as the second of the two
queued shadow bricks (SHADOW-TEST-1 was the first, a separate
lane). Governing scoping:
`~/workspace/your_files/dial2-shadow-scoping-2026-11-04.md`
§2/SR-5 (registered shape, price S–M / est. strict 10–20,
pre-registered Dial-ineligibility, kill K-SR-5), inside the
gravity-object audit (`gravity-object-audit-scoping-2026-11-04.md`:
D2-0…D2-6, P-D2). Consumes landed stock at its exact landed
shapes — `ModularVariance` (the finite Gibbs state), T1
`ThermalProfileSeparation` (the profiled weight), T2
`ThermalChargePoisson` via SHADOW-TEST-1's canonical packaging
in `PoissonTotalMassBlindness`; no landed module edited.

Module: `lean/ThetLogos/ThermalSourceComposite.lean` (NEW).
Lane: `sr5-lane`, isolated worktree
`~/workspace/thet-logos-sr5`, cut from main HEAD `7567e28`
(census 13,284 strict / 490 modules; fence 322/322 — verified
at cut). Targeted build green (**3,602 jobs**), **ZERO
sorrys**, module **WARNING-CLEAN** (no build warning names
this module; the warnings in the build log belong to
pre-existing corpus dependency modules), **no
`native_decide`** (the header's prose mention is the phrase
"no `native_decide`", as in landed modules). **Measured
strict count: 17 theorems + 4 defs** — inside the priced S–M
band of **10–20**, not exceeded. Axiom audit (`#print
axioms`, run against the built module): **all 17 theorems
depend on exactly `{propext, Classical.choice,
Quot.sound}`** — no `sorryAx`, nothing outside the standard
trio. NO integration, NO push — lane commit only.

## What landed

**The source (§1 of the module)** — the SH-5 point, earned:
the source map is built from owned thermal data only.

| Declaration | Content |
|---|---|
| `thermalSource` (def) | the Gibbs state's site-energy density: `thermalSource E β i = gibbsProb E β i * E i` — the state's probability at site `i` times the site's energy |
| `thermalSource_apply` | its unfolding, on the nose |
| `gibbsProb_eq_profWeight_const` | **the T1 bridge**: `ModularVariance`'s Gibbs probability is exactly T1's profiled weight at the constant profile, `gibbsProb E β i = profWeight (fun _ => β) E i` — the two landed Gibbs dialects agree definitionally (`rfl`) |
| `thermalSource_eq_profWeight_mul` | the source in T1's dialect: constant-profile weight times site energy |
| `sum_thermalSource` | **the source's total is the state's mean energy**: `∑ i, thermalSource E β i = meanEnergy E β` — what the source's "total" is at this seat: a thermal expectation |
| `meanVal_thermalSource` | its mean is the mean energy spread over the seat: `meanVal (thermalSource E β) = meanEnergy E β / card V` — exactly the quantity the projection removes |

**The composite (§2)** — T2's canonical channel at the
thermal source, with its well-definedness stated in the
honest (projected) form required by the task: the composite
**is defined through the mean-subtraction projection**.

| Declaration | Content |
|---|---|
| `thermalPotential` / `thermalField` / `thermalFlow` (defs) | SHADOW-TEST-1's `poissonPotential` / `poissonField` / `poissonFlow` evaluated at `thermalSource E β` |
| `sum_meanSub_thermalSource` | compatibility of the fed source: `∑ i, meanSub (thermalSource E β) i = 0` — the projection always lands in T2's compatibility class (consumed: `sum_meanSub_eq_zero`) |
| `laplacianOp_thermalPotential` | **the composite's equation**: `L (thermalPotential) = meanSub (thermalSource)` — NOT the bare form `L φ = thermalSource`, which is false whenever the mean energy is nonzero (K-TCS-POIS's obstruction, inherited honestly) |

**Uniqueness, inherited from T2 (§3)** — the composite
potential is unique up to an additive constant
(`thermalPotential_unique_mod_const`, via T2's
`exists_add_const_of_laplacianOp_eq`); every potential for
the projected source — however produced — has the
composite's field (`dropVec_eq_thermalField`) and drives
the composite's flow (`flowVec_eq_thermalFlow`), via T2's
`dropVec_eq_of_laplacianOp_eq` / `flowVec_eq_of_laplacianOp_eq`;
`dropVec_thermalPotential` / `flowVec_thermalPotential` are
the definitional hinges (`rfl`) between the two packagings.

**The ceiling, as theorems (§4)** — SHADOW-TEST-1's class
theorem read at the composite's own source. This is the
module's fence, in kernel-checked form:

| Declaration | Content |
|---|---|
| `thermalField_eq_of_meanSub_eq` | **the composite field factors through the projection**: two thermal states (any `E, β`) whose sources share a mean-subtraction have the same composite field |
| `thermalFlow_eq_of_meanSub_eq` | the same factorization for the composite flow |
| `thermalField_shifted_source` | shift-blindness at the fed channel: `poissonField (thermalSource + c) = thermalField` for every constant `c` — changing the fed source's total at fixed contrast changes nothing the channel returns |
| `not_exists_thermalField_detects_sourceTotal` | **the decision, inherited**: no quantity `F` of the composite field data and no nonzero shift `c` exhibit a response to the shift (consumed: `not_exists_fieldFactor_detects_totalMass` at `g := thermalSource E β`) — the isolated-mass signature is unreachable by this composite |
| `thermalField_eq_zero_of_thermalSource_const` | the strongest single form: a constant thermal source (pure total, zero contrast) returns the identically zero field (consumed: `poissonField_const`) |

## The SH-5 earning, stated exactly

The route earns exactly one shadow check and nothing
downstream, as pre-registered:

- **SH-5 (source map, gravity-free): EARNED.** The source
  is specified as a map from the physical source data the
  seat owns — a Gibbs state's energies and inverse
  temperature — to T2's input, stated and defined without
  any gravitational vocabulary: `thermalSource` is an
  energy-expectation density of a thermal state. The word
  for the Dial-2 target appears in the module only inside
  its honesty ledger's NOT-CLAIMED fences (K-SR-5 armed,
  did not fire — no statement attaches it, or any synonym
  doing the same work, to the output potential).
- **SH-6: NOT EARNED, not claimed.** Nothing responds:
  graph, weights, and operator are fixtures chosen before
  the source; the potential is computed from the source
  and the composite defines no further use of it.
- **SH-8: NOT EARNED, not formable.** There is no test
  body at this seat; no universality statement is stated.
- **SH-9: NOT EARNED.** No attraction sign is derived or
  stated; no sign is discussed outside this paragraph's
  refusal.
- **The ceiling (CT-1) is inherited, not escaped:**
  total-mass blindness holds for the composite at T1
  (§4). The composite's field sees the thermal source
  only as a contrast; its total — the state's mean
  energy — is exactly what the channel discards.

## Disposition

- **Grade: FULL** against the scoping's pre-registered
  shapes: composite (defs + equation + compatibility),
  uniqueness inheritance, and the ceiling as theorems —
  all landed. Nothing was narrowed; the one formulation
  choice the task left open (compatibility *or*
  mean-subtraction definition) is resolved on the face:
  the composite is defined through the projection, and
  `laplacianOp_thermalPotential` says so.
- **Dial-INELIGIBLE, pre-registered and honored:** Dial 2
  = 0 before this landing and 0 after it. NO CLAIM; dials
  0/4. This is honest bookkeeping — the reachable segment
  of Jeff's TCS chain (thermal head + Poisson inversion)
  completed at its ceiling, with the ceiling proved, not
  narrated.
- SEP fences stand on the module's face (SEP-0, K-SEP-3,
  K-PUMP-5). Finite statics only; no dynamics, no
  response law, no self-organization is stated or implied.
- Lane commit only. Integration (fence admission, ledger
  record, census step) is the parent's ceremony, not this
  lane's.

---

## INTEGRATION BLOCK (main tree, 2026-11-04)

Integrated from sr5-lane commit `3e5fe23` (lane base `7567e28`)
onto main-tree HEAD `3f35ede` (TCS T4 integration). Module +
this dossier copied **byte-identical** (md5 `ec6ab19f…`
ThermalSourceComposite, `e1da50c1…` dossier; diff-verified).
Declaration-level collision scan of all 21
ThermalSourceComposite declaration names plus the module name
against the main tree at HEAD found **zero collisions** —
confirmed by `git grep` at HEAD; module + dossier are new
files. The concurrent primordials-exhibit lane was not touched.

- Main-tree targeted build green (**3,602 jobs**, matching
  the lane — `ModularVariance` built fresh in the main tree
  as in-lane; it was not previously in the root build graph),
  zero sorrys (zero-sorry source gate PASS, 507 files),
  **module warning-clean** (every warning in the build log
  belongs to pre-existing dependency modules).
- Recount exact: ThermalSourceComposite **strict 17 + 4
  defs** (whole-tree 13,993/507 minus frozen remainder
  669/15).
- Fence admissions: all **17 theorems** with
  `import ThetLogos.ThermalSourceComposite` in the **same
  commit** as the module — **FENCE PASS 362/362** (345 →
  362), every headline on exactly {propext,
  Classical.choice, Quot.sound}, no `sorryAx`.
- Ledger record `sr5-thermal-source-composite` (standing,
  T3, kill_id null — K-SR-5 did not fire); validator PASS,
  38 records.
- Census (FILES-TRUE, method of record): **13,307/491 →
  13,324 strict / 492 modules**; README prose census and
  badge both 13,324 / 492, kept equal.
- Integration commit, remote hash, and CI verification are
  recorded in the pipeline log entry for this integration
  (`~/workspace/launch-pipeline-2026-10-29.md`) and in the
  commit message's own record chain. NO CLAIM; dials 0/4.
