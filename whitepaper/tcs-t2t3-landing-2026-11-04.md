# TCS T2+T3 LANDING DOSSIER — Discrete Poisson + Site-Wise Entropy Map — 2026-11-04

**Item:** Thermal Charge Separation package, bricks T2 + T3 ONLY,
fired by Jeff's explicit tap 2026-11-04 02:14 EST ("Build T2 + T3
first (Poisson + entropy map)"), under the scoping dossier
`~/workspace/your_files/thermal-charge-separation-scoping-2026-11-04.md`,
which governs statements, prices, fences, and the pre-registered
kills K-TCS-POIS (T2) and K-TCS-ENT (T3). Lane: isolated worktree
`~/workspace/thet-logos-tcs`, branch `tcs-lane`, cut from main HEAD
8eaf57d (census 13,117 strict / 480 modules, fence 175/175 at cut).
Lane commits only — NO integration, NO push; the overnight
coordinator's main-tree integrations proceed independently and the
parent handles rebasing.

## VERDICT: T2 FULL · T3 FULL

**Artifacts:**
- `lean/ThetLogos/ThermalChargePoisson.lean` — **strict 17,
  defs 2** (scoped band 15–30 ✓).
- `lean/ThetLogos/SiteEntropyMap.lean` — **strict 19, defs 3**
  (scoped band 12–25 ✓).
- **Combined strict 36** (scoped combined band 27–55 ✓), defs 5.

**Verification:** targeted builds green
(`lake build ThetLogos.ThermalChargePoisson`,
`lake build ThetLogos.SiteEntropyMap`; combined run 3320 jobs),
**zero sorrys, no `native_decide`, warning-clean** for both modules
(all linter warnings discharged — `omit` placed before doc
comments, per corpus convention). `#print axioms` run on **all 36
theorems**: every one depends on exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no other
axioms.

## T2 — Discrete Poisson (FULL)

Seat: `BridgeLaplacian`'s finite graph (vertex type `V`, symmetric
real weights `w`), consuming `laplacianOp`, the energy route, and
`BridgeCompletion`'s linear packaging `lapLinFun` at their exact
landed shapes. Connectivity is carried in the seat's own landed
form: symmetry, nonnegativity, and strict positivity off the
diagonal (`i ≠ j → 0 < w i j`) — the hypotheses of
`eq_const_of_energy_eq_zero` (kernel = constants).

Headlines:
- `exists_potential_iff_sum_eq_zero` — **the Poisson theorem, iff
  form**: a potential `f` with `laplacianOp w f = g` exists iff
  `∑ i, g i = 0`. The ⇒ direction is the current law
  (`sum_laplacianOp_eq_zero`); the ⇐ direction is existence.
- `discrete_poisson` — the combined package (existence with
  compatibility, uniqueness modulo constants, uniqueness of the
  induced edge field and Ohm flow, existence with a prescribed
  value at a named vertex).
- `range_lapLinFun_eq_ker_chargeSum` — range of `L` is exactly the
  mean-zero subspace.
- `exists_add_const_of_laplacianOp_eq`, `dropVec_eq_of_laplacianOp_eq`,
  `flowVec_eq_of_laplacianOp_eq`,
  `potential_eq_of_laplacianOp_eq_of_apply_eq`,
  `exists_potential_with_value` — uniqueness side.

Existence route: the current law puts the image of `L` inside
`LinearMap.ker chargeSum` for **every** input (`lapLinFun_mapsTo_ker_chargeSum`
— stated at that full strength, since the law holds for all `F`,
not only mean-zero ones); the restriction `lapRestrict` to the
mean-zero subspace is built as codomain restriction precomposed
with the subtype inclusion (unfolding: `lapRestrict_coe`, proved by
`rfl`); it is injective because a mean-zero kernel element is
constant (energy route) and a mean-zero constant on a nonempty
vertex set is zero (`eq_zero_of_lapRestrict_eq_zero`,
`lapRestrict_injective`); injective endomorphism of a
finite-dimensional space is surjective
(`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`).
The empty-vertex case is split off inside the proofs (zero
potential; uniqueness vacuous), so no `Nonempty V` hypothesis
appears in any headline.

**K-TCS-POIS: DID NOT FIRE.** The bare ∀-form (a potential for
arbitrary `g`, no compatibility) is false — constant nonzero
charge admits no potential — and was never attempted. The
compatibility condition `∑ i, g i = 0` is IN the statements, as
scoped; the iff headline records both directions on the face.

## T3 — Site-Wise Entropy Map (FULL)

Seat: arbitrary finite index type `κ`, finite local state types
`X i`, weights on the configuration Pi type `(∀ i, X i)`,
consuming `FiniteEntropy`'s `entropyW` and `IsProbWeight` at their
exact landed shapes. Defs: `margWeight` (site marginal),
`siteEntropy w i = entropyW (margWeight w i)` (the map),
`siteProdWeight` (product weight).

Headlines:
- `siteEntropy_nonneg`, `siteEntropy_le_log_card` — the map's
  basic bounds, exact consumptions of `entropyW_nonneg` /
  `entropyW_le_log_card` at the marginal (marginals of a
  probability weight are probability weights:
  `isProbWeight_margWeight`).
- `entropyW_siteProdWeight` — **additivity for product weights**:
  `entropyW (siteProdWeight u) = ∑ i, entropyW (u i)`, with
  `margWeight_siteProdWeight` (the marginal of a product weight is
  its own factor) and the map form
  `entropyW_siteProdWeight_eq_sum_siteEntropy`. Engine:
  `sum_siteProdWeight_mul` — factorization for **arbitrary** site
  weights (no probability hypothesis), the other factors' total
  masses carried explicitly as the erase-product; the twisted
  family is built with `Function.update` (the dependent-safe way
  to change one factor).
- `entropyW_le_sum_siteEntropy` — **subadditivity in general**:
  `entropyW w ≤ ∑ i, siteEntropy w i`, by the pointwise Gibbs
  inequality (`Real.log_le_sub_one_of_pos`) against the product of
  the marginals — itself a probability weight by the product
  machinery — with both total masses `1` cancelling in the sum.

**K-TCS-ENT: DID NOT FIRE.** Additivity is stated ONLY under the
product hypothesis. Additivity without it is false (the dossier's
perfectly correlated two-site weight: site entropies `log 2` each,
total `log 2`, not `2 log 2`); the general theorem landed is
subadditivity. The counterexample and the guard are recorded in
the module header.

## Narrowings and deviations — honest list

1. T2's restriction is assembled from `LinearMap.codRestrict` +
   `Submodule.subtype` rather than `LinearMap.restrict` (the
   latter's implicit submodule arguments would not elaborate from
   the maps-to lambda). Internal device only; no statement is
   affected, and `lapRestrict_coe` pins its unfolding.
2. T2's maps-to lemma is stated for all `F` (stronger than the
   subspace formulation), because the current law is. No
   narrowing.
3. T3 states no `κ = Fin 3` special case: the general finite Pi
   type is the statement, per the scoping (Jeff's "3D" is the
   seat's index shape; the module header says the map lives on
   whatever finite index type the weight lives on, no geometry
   claimed). No narrowing.
4. Nothing else deviates from the scoping dossier: every scoped
   T2/T3 component landed at its scoped shape.

## Fences (standing, on both modules' faces)

Determination results only (data in ⇒ object out) — not
self-organization, no dynamics. No operator acting on a thermal
density matrix separates charge by its own action (SEP-0). No
charge operator and no electromagnetic field object is claimed at
any seat. β appears nowhere; β is data and moves nothing by
itself. The equivalence and division components of Jeff's
assertion are NOT in this fire and appear only as fences. Finite
statics / finite information bookkeeping only. **NO CLAIM;
dials 0/4.**

---

## INTEGRATION BLOCK (main tree, 2026-11-04)

Integrated from tcs-lane commit `99e50ac` (lane base `8eaf57d`)
onto main-tree HEAD `69bc5ec` (U-3b integration). Modules +
this dossier copied **byte-identical** (md5 `81501068…`
ThermalChargePoisson, `460f8692…` SiteEntropyMap, `32f24bfe…`
dossier; diff-verified). Declaration-level collision scan of
all 41 TCS declaration names against the current main tree
found **zero collisions** — confirmed independently by
`git grep` at HEAD (no TCS name, declared or mentioned, exists
in the main tree); modules + dossier are new files.

- Main-tree targeted build green (**3320 jobs**, matching the
  lane), zero sorrys (zero-sorry source gate PASS, 502 files),
  **both modules warning-clean** (every warning in the build
  log is pre-existing dependency replay, e.g. BridgeLaplacian).
- Recount exact: ThermalChargePoisson **strict 17 + 2 defs**,
  SiteEntropyMap **strict 19 + 3 defs** (whole-tree 13,912/502
  minus frozen remainder 669/15).
- Fence admissions: all **36 theorems** (17 + 19) with
  `import ThetLogos.ThermalChargePoisson` /
  `import ThetLogos.SiteEntropyMap` in the **same commit** as
  the modules — **FENCE PASS 281/281** (245 → 281), every new
  theorem on exactly {propext, Classical.choice, Quot.sound},
  no `sorryAx`.
- Ledger records `tcs-t2-discrete-poisson` and
  `tcs-t3-site-entropy-map` (standing, T3, kill_id null —
  K-TCS-POIS / K-TCS-ENT did not fire); validator PASS,
  33 records.
- Census (FILES-TRUE, method of record): **13,207/485 →
  13,243 strict / 487 modules**; README prose census and
  badge both 13,243 / 487, kept equal.
- Integration commit, remote hash, and CI verification are
  recorded in the pipeline log entry for this integration
  (`~/workspace/launch-pipeline-2026-10-29.md`) and in the
  commit message's own record chain. NO CLAIM; dials 0/4.

### G-READ — the dual readings of the Poisson theorem (documentation only)

Folded into this integration per the gravity-object audit
(`~/workspace/your_files/gravity-object-audit-scoping-2026-11-04.md`
§3): **G-READ is that audit's only GO — documentation only,
strict 0.** What follows are **READINGS, not theorems.** No
Lean wrapper corollaries exist: **G-WRAP**
(`poisson_electric` / `poisson_gravitational` as named
corollaries by substitution) was **killed by the audit** —
the wrappers would contain no proof content beyond
substitution into T2, and their names would let a label
impersonate an object.

**Audit decision, printed:** T2 is **pre-registered NOT
Dial-eligible. Dial 2 = 0.**

The dictionaries. Continuum anchors (standard sign
conventions, ∇² the ordinary Laplacian): electrostatics
∇²φ_e = −ρ_e/ε₀, force on a test charge **F** = −q∇φ_e;
Newtonian gravity ∇²Φ = 4πGρ_m, acceleration of any test
body **a** = −∇Φ. The graph operator `L` of T2 corresponds
to **−∇²** (that is why it is positive semidefinite). Under
that identification the two readings of `Lφ = s` differ in
exactly three places — **source dictionary, sign, and
response law** — and in nothing else:

| | Electrostatic reading | Gravitational reading |
|---|---|---|
| Source `s` fed to T2 | normalized charge density, `s ∝ ρ_e/ε₀` (graph weights/spacing absorb the constant) | normalized **sign-reversed mass contrast**, `s ∝ −4πG (ρ_m − ρ̄_m)` |
| Why the form | charge comes in both signs; net-zero source is physical (overall neutrality) | ordinary mass density is ≥ 0, so on a *closed finite* seat only its **fluctuation about the mean** satisfies `Σ s = 0`; T2 sees the contrast, never the total mass |
| Potential | φ_e, defined mod constant | Φ, defined mod constant |
| Field | `dφ` unique — the discrete field | `dφ` unique — the discrete field analogue |
| Response law (**not in T2**) | **F** = q**E**: depends on the test body's charge, both signs occur | **a** = −∇Φ: the same for every test body — universality is an *additional fact about the world*, not a corollary of inversion |

Two consequences, stated flatly:

1. **The sign difference is real and it is bookkeeping.**
   A positive charge concentration and a positive mass
   concentration feed *oppositely signed* sources into the
   same positive operator (repulsion of like charges vs
   universal attraction). The inversion theorem is
   indifferent to the sign; the physics is not — the sign
   is precisely where the two theories stop being the same
   theory, together with the response law.
2. **The gravitational reading is weaker than its continuum
   namesake in a way the electrostatic reading is not.**
   T2's gravitational potential is the potential of a
   *density contrast on a fixed finite graph* — the finite
   analogue of subtracting a uniform background — not the
   field of an isolated positive mass (which needs a
   boundary at infinity this closed seat does not have).

What the finite graph version does **NOT** have (each a
named missing mechanism in the audit's §4): no geometry
that responds (graph and weights fixed by fiat; nothing
curves); no nonlinearity (Poisson is linear; no
self-coupling, no route to one); no equivalence principle
(no test body exists in the theorem; universality is
imported by the reading, not proved); no dynamics of the
source (ρ is prescribed static data, no conservation law,
no back-reaction); no G (any coupling constant enters as a
rescaling of the source dictionary — a declared input, no
derivation, no measured value computed); no continuum
limit and no inverse-square law; no stress-energy, no
causal structure, no light — there is no time in the
statement at all.

**Dual-reading discipline (standing, applies here and to
any future use):** (i) one theorem, one proof — a reading
never mints a second theorem; (ii) every reading carries
its dictionary (units, sign, normalization) on its face;
(iii) the theorem's hypotheses travel with both readings —
connectedness, compatibility, gauge non-uniqueness;
(iv) no inference from *existence of the potential* to
*force, motion, geometry, or equivalence* is licensed by
the reading; (v) any response law added later is a new
model assumption, named as such, never retro-credited
to T2.

G-READ changes no theorem, no count, and no dial: census
effect strict 0, Dial 2 = 0, NO CLAIM; dials 0/4.
