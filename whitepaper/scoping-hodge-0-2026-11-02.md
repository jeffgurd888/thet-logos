# HODGE-0 — Shelf Audit + (1,1) Statement Scoping (Millennium Lane 3)

Date: 2026-11-02. Audit only: greps/reads only, no Lean files, no builds, no commits.
Corpus audited: `~/workspace/thet-logos/lean/ThetLogos/` (449 `.lean` files).
Pin audited: Mathlib at `leanprover/lean4:v4.35.0-rc3`
(`thet-logos/lean/.lake/packages/mathlib`, HEAD `516d31250e`).
Registration: `whitepaper/next-rotation-scoping-2026-11-01.md` §3.5; board charter:
`~/workspace/millennium-program/GAUNTLET-MAP.md` §5.

> **NO CLAIM.** Parts of the Hodge conjecture closed by this audit: **0**.
> This memo closes no part of the official statement. It prices the shelf, nothing else.

---

## K-HODGE-0 VERDICT — FIRES

**No non-vacuous Hodge board statement — not even the Lefschetz (1,1) case — is
statable in owned vocabulary at any price this lane can pay.**

Every load-bearing noun of the Clay statement ("Hodge class", the (p,p) part of
cohomology, the cycle-class map) has **no object** in the pinned Mathlib to pin
against (details §2–§3). A pin written today would be a Prop whose cohomology,
grading, and cycle map are all opaque types / labelled hypotheses — the house
definition of vacuous-by-substitution (the S3-3 / OSReconstruction lesson).
Per the pack, the deliverable therefore becomes the **infrastructure scoping**
in §4, not a pin. The full Hodge statement pin remains **UNPRICEABLE**, as
registered in the 2026-11-01 scoping, now audit-confirmed rather than assumed.

---

## 1. In-tree (the corpus): essentially zero — proved by the grep

Grep over `ThetLogos/` for `hodge|kähler|kahler|projective variety|algebraic
cycle|chow|cohomology`, plus `variety|scheme|divisor|chern|lefschetz`:

| Hit | What it actually is |
|---|---|
| `BRSTFinite.lean:46,57,180,251,284` — "cohomology" | Finite BRST / Lie-algebra cohomology of a finite spectral setup. Not sheaf, singular, or de Rham cohomology of a variety. |
| `BRSTFinite.lean:389` — "Hodge-dual candidate" | An ε-tensor (Levi-Civita) dual on a finite index set. Not Hodge theory. |
| `MaxwellQuadSpectrum.lean:54` — "Hodge" | A doc comment using "Hodge" colloquially for the curl-curl + div-grad Laplacian identity. No object. |
| `Chromatic.lean:30` — "Tripotent Variety" | A string label in a finite table. Not a variety. |

No algebraic geometry, no schemes, no manifolds-as-varieties, no cycles, no
Chow, no divisor class, no Chern class anywhere in the corpus. The board's
charter line — "OPENED — untouched by the corpus" (`millennium-program/INDEX.md:12`)
— is exact.

## 2. In-pin (Mathlib v4.35.0-rc3): itemised shelf

Paths below are relative to `Mathlib/` in the pin.

### Present (real, usable)

- **Schemes and their morphisms.** `AlgebraicGeometry/Scheme.lean`, with
  `AlgebraicGeometry/Morphisms/Smooth.lean` and `…/Proper.lean` — so *smooth*
  and *proper* exist as morphism properties, and `ProjectiveSpectrum/`
  (incl. `Proper.lean:372`, an `IsProper (Proj.toSpecZero 𝒜)` instance) gives
  Proj as a scheme. The *ingredients* of "smooth projective variety over ℂ"
  exist; no packaged variety type does (grep `ProjectiveVariety` /
  "projective variety": **0 hits**).
- **Abstract sheaf cohomology.** `CategoryTheory/Sites/SheafCohomology/Basic.lean:18,59`:
  `Sheaf.H F n` defined as Ext-groups of an abelian sheaf on an arbitrary site;
  plus Čech (`…/Cech.lean`) and Mayer–Vietoris (`…/MayerVietoris.lean`).
  Abstract and general — not instantiated as the Betti cohomology of a
  complex variety, and carrying no Hodge structure.
- **Singular homology** (homology, not cohomology).
  `AlgebraicTopology/SingularHomology/Basic.lean:36,52`:
  `singularChainComplexFunctor`, `singularHomologyFunctor`; H₀ computed,
  homotopy invariance present. This is the wrong variance for the Clay
  statement and has no ℚ-cohomology dual in the pin (see Absent).
- **ℓ-adic cohomology of schemes (new in this pin).**
  `AlgebraicGeometry/Sites/ElladicCohomology.lean:27-28,63`: pro-étale
  `Scheme.EllAdicCohomology` with `ℤ_[ℓ]` coefficients. A genuine scheme
  cohomology — but ℓ-adic, not Betti/de Rham, with no comparison theorem to
  singular cohomology and no Hodge grading. It does not state Hodge.
- **Algebraic cycles — seed form only (new in this pin).**
  `AlgebraicGeometry/AlgebraicCycle/Basic.lean` (whole file: 187 lines):
  `AlgebraicCycle X R` at `:44` is an *abbrev* for locally-finite-support
  functions `X → R` on scheme points; pushforward and the degree of a
  0-cycle are defined; `IsWeilDivisor` at `:143` and the subgroup
  `weilDivisors` at `:164` give codimension-1 cycles. That is where it stops
  (see Absent for what a cycle *class* needs beyond this).

### Partial / fragmentary

- **Complex manifolds.** The general manifold framework exists, and
  `Geometry/Manifold/Complex.lean` treats holomorphic functions on complex
  manifolds — containing exactly two closely-related results (maximum
  modulus / locally constant). Its own docstring, `:30`: *"There is a whole
  theory to develop here"* (TODO: holomorphic line bundles, sheaf theory of
  holomorphic functions — all future). No Kähler manifold structure exists:
  every "Kahler/Kähler" hit in the pin is either Kähler *differentials*
  (`RingTheory/Kaehler/Basic.lean:21` — the algebraic module `Ω[S⁄R]`) or a
  2-dimensional inner-product-space "Kahler form"
  (`Analysis/InnerProductSpace/TwoDim.lean:560`;
  `Geometry/Euclidean/Angle/Oriented/Rotation.lean:157,180,186`). Neither is
  a Kähler metric on a manifold.
- **Differential forms.** `Analysis/Calculus/DifferentialForm/` exists
  (forms on normed spaces) and an exterior derivative of functions exists
  (`Geometry/Manifold/MFDeriv/NormedSpace.lean:425ff`). There is no de Rham
  complex of a manifold and no de Rham cohomology group built from it.

### Absent (grep-empty, verified — not assumed)

- **Hodge decomposition / Hodge class / (p,p) grading — ABSENT entirely.**
  Grep `hodge (decomposition|class|structure)|HodgeDecomposition|hodgeClass`:
  0 defining hits. All "Hodge" hits in the pin are: the Hodge *star* on
  exterior powers (`LinearAlgebra/ExteriorPower/HodgeStar.lean:12-17` — pure
  linear algebra), *p-adic* Hodge theory references in the perfectoid files
  (`RingTheory/Perfectoid/BDeRham.lean:41-44` — Fontaine period rings,
  unrelated to the Clay statement), and a Deligne *Théorie de Hodge II*
  bibliographic citation (`CategoryTheory/Filtration/Basic.lean:29`).
  Grep `dolbeault|bigraded`: **0 hits**. No Dolbeault complex, no bigrading,
  no `H^{p,q}`.
- **De Rham cohomology — ABSENT.** Grep `deRham|DeRham|de_rham` returns only
  `RingTheory/Perfectoid/BDeRham.lean` (p-adic). No de Rham cohomology of any
  manifold or variety.
- **Singular cohomology — ABSENT.** Grep `singularCohomology|SingularCohomology`
  and `singular.*cohomolog|cohomolog.*singular`: no cohomology theory; only
  the homology functor above. Grep `\bbetti\b`: **0 hits**. No cup product,
  no Poincaré duality (grep `Poincaré duality|PoincareDuality`: 0 hits).
- **Chow groups / rational equivalence / cycle-class map — ABSENT.**
  Grep `\bchow\b`: **0 hits**. Grep `cycleClass|RationalEquivalence|
  rational equivalence`: the only hit is a *comment* in
  `AlgebraicGeometry/AlgebraicCycle/Basic.lean:91` noting pushforward
  "respects rational equivalence" — rational equivalence itself is not
  defined, so there is no quotient, no `CH^p(X)`, no codimension grading of
  cycle groups beyond the Weil (codim-1) subgroup, and no map from cycles
  to cohomology.
- **Divisor class group / Picard / Néron–Severi / first Chern class — ABSENT.**
  No divisor *class* group (Weil divisors exist unquotiented, §2 above);
  "Picard group" occurs only as prose in
  `AlgebraicGeometry/EllipticCurve/Weierstrass.lean:24,50,365`; grep
  `neron|Néron`: 0 objects. Grep `firstChern|ChernClass|chern`: only
  "Chernoff" (probability) and a Tactic substring — no Chern class, no `c₁`,
  no exponential sequence. The analytic `Analysis/Meromorphic/Divisor.lean`
  is the divisor of a meromorphic function on a subset of a normed field —
  not a divisor class theory on a variety.
- **Lefschetz (1,1) — ABSENT.** Grep `lefschetz` returns only the model-theory
  *Lefschetz principle* (`FieldTheory/AxGrothendieck.lean:31`;
  `ModelTheory/Algebra/Field/IsAlgClosed.lean:19-40,220,232`). No trace of
  the (1,1)-theorem, hard Lefschetz, or the Lefschetz hyperplane theorem.
- **Analytification — ABSENT.** Grep `analytification`: 0 hits. Nothing in the
  pin turns a scheme over ℂ into its complex manifold / topological space of
  ℂ-points, so even where both sides exist separately, they are not connected.

## 3. The (1,1) special case: still infrastructure-blocked

Lefschetz (1,1) says: on a smooth projective variety `X` over ℂ, the rational
(1,1)-classes in `H²(X, ℚ)` are exactly the ℚ-span of divisor classes, via the
cycle-class (first Chern) map. A statement-grade pin needs all of:

| Needed for a (1,1) pin | Shelf status |
|---|---|
| A smooth projective variety type over ℂ | **Assemblable, unassembled** — `Scheme` + `Smooth` + `Proper`/Proj exist separately; no bundled type, no API. The only piece anywhere near ownable. |
| `H²(X, ℚ)` as singular/Betti cohomology of `X` | **Absent** — singular homology only; no ℚ singular cohomology, no analytification to get the space whose cohomology this is. |
| The `(1,1)` part of `H²` | **Absent** — requires the Hodge decomposition of `H²`; no Hodge theory, no bigrading, no Dolbeault. |
| Algebraic divisor classes `Cl(X) ⊗ ℚ` | **Half a seed** — `weilDivisors` (raw codim-1 cycles) exists; the quotient by linear/rational equivalence that makes them *classes* does not. |
| The cycle-class map `cl : Cl(X)⊗ℚ → H²` (i.e. `c₁`) | **Absent** — no Chern class, no exponential sequence, no target cohomology. |

**Answer: no.** Even (1,1) is not ownable at statement grade at S–M or M
scale. Both sides of the (1,1) equality are missing objects, not just missing
proofs: the left side (the (1,1) subspace) and the map itself do not exist in
the pin. Owning the variety type and raw Weil divisors alone would let one
write a Prop in which `H²`, `(·)^{1,1}`, and `cl` are parameters — content
living entirely in labelled hypotheses, which is exactly the K-HODGE-0
trigger condition in the registration.

## 4. Infrastructure scoping (the deliverable, per K-HODGE-0)

Ordered dependency list for a real — non-vacuous — Hodge pin. Bands are
granularity-only (S < M < L < XL), judged against this lane's scale, and are
scoping estimates, not commitments. Items marked UNPRICEABLE have no honest
band at lane scale today.

1. **Variety package.** A bundled smooth projective variety over ℂ
   (`Scheme` + smoothness + projectivity/properness over `Spec ℂ`) with basic
   API. — **Band M–L.** The only item whose ingredients all exist in-pin.
2. **Analytification.** `X ↦ X(ℂ)` as a topological space / complex manifold,
   functorially, connecting item 1 to analysis. — **Band XL** (no bridge of
   this kind exists in the pin to imitate).
3. **Betti cohomology for varieties.** Singular cohomology
   `H*(X(ℂ), ℚ)` with cup product (dualising/complementing the existing
   singular *homology*), or sheaf cohomology of the constant sheaf ℚ
   identified with it (a comparison theorem). — **Band L–XL.**
4. **Kähler geometry + Hodge decomposition.** Kähler metrics on complex
   manifolds, harmonic forms / elliptic theory, and the decomposition
   `H^k ⊗ ℂ ≅ ⊕_{p+q=k} H^{p,q}` for compact Kähler manifolds. —
   **UNPRICEABLE at lane scale**; this is the deepest single gap (the pin's
   complex-manifold file is two results deep and says so itself).
5. **The (p,p) grading.** `H^{p,p}` as a defined subspace of `H^{2p}(X, ℚ)`
   via item 4, with rationality (`H^{2p}(X,ℚ) ∩ H^{p,p}`). — **Band M,
   conditional on item 4** (cheap once 4 exists; impossible before it).
6. **Chow groups.** Codimension grading of `AlgebraicCycle`, rational
   equivalence, the quotient `CH^p(X)`, functoriality. — **Band L**
   (the 187-line cycle file is a genuine seed, not a foundation).
7. **Cycle-class map.** `cl : CH^p(X) ⊗ ℚ → H^{2p}(X, ℚ)` landing in the
   (p,p) part — needs items 3, 5, 6 plus fundamental classes / Poincaré-type
   input, none in-pin. — **Band XL, borderline UNPRICEABLE** (depends on 4).
8. **The statement pin itself.** Given items 1–7, writing the Clay statement
   (and, separately, the (1,1) statement) as a checked Prop. — **Band S,
   conditional.** The pin was never the expensive part; the vocabulary is.
9. **Lefschetz (1,1) as a theorem** (beyond items 1–8): exponential sequence,
   `c₁` for line bundles, Picard/Néron–Severi. — **UNPRICEABLE today**
   (proof-scale, not statement-scale; listed so the (1,1) "theorem behind it"
   is not mistaken for a shortcut around items 2–5).

**Honest total picture.** This is a **years-scale gap in Mathlib itself**, not
a gap this lane can buy down brick by brick: items 4 and 7 sit on top of
essentially the whole of complex geometry and Hodge theory, of which the pin
contains fragments (manifold framework, abstract sheaf cohomology, a seed
cycle file, a new ℓ-adic theory) and none of the connective tissue (no
analytification, no Betti cohomology, no de Rham cohomology, no Kähler
geometry, no grading, no Chow quotient, no cycle map). The board's correct
posture remains: charter open, NO CLAIM, parts closed **0**, next honest
action = re-run this audit when the pin moves — the shelf *is* moving
(cycles and ℓ-adic cohomology both landed in this pin where earlier pins had
neither), so a future pin may reprice items 1, 3, and 6. Items 4, 5, and 7
have no visible motion.

## 5. Non-vacuous fragment check (pack Q5)

Contrary-to-expectation search, for completeness: the largest statable
fragment found is "raw Weil divisors form a subgroup of raw algebraic cycles
on a scheme" — which is already a Mathlib theorem
(`AlgebraicGeometry/AlgebraicCycle/Basic.lean:164`), is not a fragment of the
Hodge statement (it mentions no cohomology, no grading, no class map), and
pinning it on this board would be substitution, not progress. **No
non-vacuous fragment of the Clay statement is statable.** No pin is priced;
no new kill is registered beyond K-HODGE-0 itself, which FIRES above.

---

*Fence restated: NO CLAIM on the Hodge conjecture. Parts closed: 0. This memo
is an audit and a scoping, at audit tier — every "absent" above is a grep over
the named pin, reproducible from the citations given.*
