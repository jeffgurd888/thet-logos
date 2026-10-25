# FG-2c GATE — Pricing the identification `exp(−Ĥ) = T̂_c`

*Gate paper, 2026-10-25. Paper only — no Lean commissioned by this
document. It prices the third and final brick of the FG-2 line
(frontier-gate §2.2): the semigroup identification for the FG-2b
Friedrichs operator. Consumes the FG-2a dossier
(`stage2-fg2a-form-closed-partial-2026-10-25.md`), the FG-2b dossier
(`stage2-fg2b-friedrichs-2026-10-25.md`), and the FG-2b verdict memo
(whose closing flag — "price accordingly" — is this paper's
commission). All library claims below were grep-verified against the
pinned Mathlib v4.35.0-rc3 tree and the corpus on 2026-10-25.*

## Placement and fences (on the face)

Stage 2 completeness work (frontier-gate §2.2, FG-2 line). Fixed
volume, fixed lattice. **Not frontier progress; Items 3/4 untouched.
NO CLAIM. Dials 0/4.** Even a FULL FG-2c asserts nothing spectral
about Ĥ beyond the identification itself: no gap for Ĥ, no
uniformity in N or β, no continuum object. It closes Stage 2's
operator seat — the S2-4(b) residue — and nothing else.

## §1. The two objects, exactly as the record holds them

**Ĥ (FG-2b, landed).** `sliceHamOperator` in
`ThetLogos.LatticeSliceFriedrichs`: a LinearMap on its domain
D(Ĥ) = range R inside the carrier **H′ := `sliceFormClosure`** (the
topological closure of the form domain in `sliceHilbertSpace`), where
R = `sliceFriedrichsResolvent` is the resolvent **at λ = 1 only**:
the Riesz representative for the unit-weight form inner product
`sliceFormInner x y = ⟪x.val, y.val⟫ + sliceFormB x y`
(`LatticeSliceFormClosed.lean`, definition at unit weights — there
is no λ parameter anywhere in the slice tree; grep-verified). Landed
clauses: R linear, symmetric, ‖R f‖ ≤ ‖f‖, injective, CLM of bound 1;
Ĥ symmetric; ⟪Ĥu, u⟫ = the form value, hence Ĥ ≥ 0; the form identity
`sliceFormB û v = ⟪Ĥu, v⟫` (Kato's first representation theorem at
this seat); **Ĥ + 1 surjective onto H′** (self-adjointness in the
resolvent sense); Ω ∈ D(Ĥ), ĤΩ = 0. All under exactly
`SliceHPosOne`, with hypothesis-free U(1) (β ≥ 0) and β = 0 packages.

**T̂_c (S2-4(b) rung 1, landed).** `sliceHatCompleted`: a bounded
self-adjoint contraction (bound 1, vacuum fixed) on the **whole**
`sliceHilbertSpace`.

**The seat mismatch, named before any route is priced.** Ĥ lives on
H′; T̂_c lives on the whole space. FG-2a proves H′ ⊆ (ker T̂_c)^⊥;
the reverse inclusion is the FG-2b step-0 residue (unproved). And
whether T̂_c **preserves** H′ is not in the record at all. So the bare
string "exp(−Ĥ) = T̂_c" is not yet a well-seated statement: every
sense below is seated on H′, with T̂_c read as its restriction —
which is legitimate only once T̂_c-invariance of H′ is proved, or
once the carrier equality H′ = (ker T̂_c)^⊥ lands (T̂_c, being
self-adjoint, preserves (ker T̂_c)^⊥ automatically). This is the
first place the step-0 obstruction recurs (§3).

## §2. What "exp(−Ĥ) = T̂_c" can mean in the pinned Mathlib

**Library inventory (grep-verified, 2026-10-25).** Absent from
Mathlib v4.35.0-rc3: any Hille–Yosida theorem, any Yosida
approximation theorem, any Borel functional calculus, any spectral
theorem for unbounded operators, and any strong-operator topology
(the name does not occur — strong convergence must be stated
pointwise, as `∀ x, Filter.Tendsto (fun n => S_n x) atTop (nhds (S x))`).
Present, and load-bearing for the pricing:

* `cfc` / `cfcHom` — the continuous functional calculus for bounded
  star-normal elements of C*-algebras, continuous functions only.
  Continuous linear maps on a Hilbert space form a C*-algebra in
  this Mathlib (`Mathlib/Analysis/CStarAlgebra/ContinuousLinearMap.lean`),
  so `cfc` is *in principle* applicable to the self-adjoint
  contraction T̂_c — but it has **never been assembled for
  `sliceHatCompleted`**, and `cfc` cannot evaluate `−log` on a
  spectrum containing 0 (the function is not continuous there).
* `NormedSpace.exp` — the Banach-algebra exponential (power series).
  The exponential of a **bounded** operator therefore exists in the
  library today; only the unbounded case is missing.
* `NormedSpace.log` — a Banach-algebra logarithm defined by a power
  series convergent only near the identity, with exp/log inverse
  theorems only in that neighborhood. It cannot see spectrum
  point 0 of T̂_c. The backward route (define Ĥ := −log T̂_c) is
  therefore *not* available as a shortcut, exactly as the S2-4(b)
  dossier recorded.

**The candidate senses.** In this library the identity can honestly
mean one of:

* **Sense A — resolvent powers (Hille–Yosida shape).** With
  R_λ := (Ĥ + λ)⁻¹ on H′ for all λ > 0, the statement is:
  `(n • R_n)^n x → T̂_c x` strongly for every x ∈ H′, where the
  powers are iterates of the bounded operator n·R_n. The limit
  object is not defined by any library theorem; the convergence is
  the theorem.
* **Sense B — Yosida approximants.** With Ĥ_n := n(1 − n·R_n), a
  bounded operator on H′ (once the family R_λ exists), `exp(−Ĥ_n)`
  is defined by `NormedSpace.exp` in the CLM algebra, and the
  statement is: `exp(−Ĥ_n) x → T̂_c x` strongly for every x ∈ H′.
* **Sense C — uniqueness through the form (no exp constructed).**
  A characterization theorem: at most one self-adjoint contraction
  S on the seat satisfies (i) S preserves the seat and the form
  domain, (ii) the −log defect-series form of S equals
  `sliceHamFormC`, (iii) SΩ = Ω. T̂_c satisfies the clauses by
  construction (its own defect series *is* the form). Any Ĥ-side
  candidate produced by Sense A or B and shown to satisfy the
  clauses then equals T̂_c. Sense C alone constructs no exponential;
  it is the identification half that A and B both need.

**Factorization (the paper's main structural claim).** Every route
factors as CONSTRUCT × IDENTIFY: a candidate semigroup object built
from Ĥ (A or B), and an identification of that candidate with T̂_c
(C, or an equivalent direct argument). There is no route in this
library that skips IDENTIFY, because there is no functional calculus
in which both sides are the same function's values. Prices below are
given per brick so the factorization is visible on the invoice.

## §3. Where the FG-2b step-0 obstruction recurs

Step 0 (FG-2a residue, FG-2b memo): the mixed form inequality
`(⟪x, T̂_c A_c^j x⟫).re ≥ 0` — defect-pairing monotonicity, i.e.
form-order **T̂_c² ≤ T̂_c** — is unproved; the record carries pure
pairings only and no functional calculus for `sliceHatCompleted` is
assembled. It recurs in FG-2c at exactly three places:

1. **Seating (§1).** T̂_c-invariance of H′, hence the right to read
   T̂_c as an operator on the seat of Ĥ, is a mixed-pairing fact:
   finiteness of the form at T̂_c x is control of the shifted defect
   pairings.
2. **IDENTIFY (Sense C, clause (ii) for the Ĥ-side candidate).**
   Comparing a candidate's defect series against `sliceHamFormC`
   term-by-term runs into the same mixed pairings of T̂_c against
   powers of its own defect.
3. **Route A's convergence proof.** The standard Trotter–Kato /
   Chernoff arguments compare resolvent powers against the form on a
   core; the core estimates here are defect-series estimates, i.e.
   mixed pairings again.

**The counterweight that did not exist when step 0 was first named:**
the obstruction is, spectrum-side, the inequality μ² ≤ μ on
[0, 1] — a *polynomial* fact about a bounded self-adjoint operator.
Mathlib's `cfc` proves polynomial agreement (`cfc` of a polynomial
is the polynomial of the operator) and carries an order API for
real-valued functions on the spectrum. So a discharge of step 0 via
an assembled `cfc` for T̂_c plus an order-to-pairing bridge is a
concrete, priceable brick (FG-2c-0 below) — not a hope. It is also
the only brick that pays on every route simultaneously.

## §4. Bricks and prices

Sizes in the house scale (S/M/L/XL), at general (G, ρ), every real
β, under exactly `SliceHPosOne`, with the U(1) and β = 0 packages
replaying as in FG-2a/2b. (At β = 0 the identity is already true —
Ĥ = 0, T̂_c = id — and any brick may carry the β = 0 package as a
sanity clause at S marginal cost.)

* **FG-2c-0 — `cfc` assembly for T̂_c + step-0 discharge attempt.**
  Wire `sliceHatCompleted` into the C*-algebra `cfc` API; prove
  polynomial agreement instances as needed; build the
  order-to-pairing bridge (spectrum-side μ² ≤ μ on spectrum(T̂_c)
  ⊆ [0, 1] ⇒ form-order T̂_c² ≤ T̂_c ⇒ mixed pairings
  `(⟪x, T̂_c A_c^j x⟫).re ≥ 0`). On FULL: the FG-2a residue closes,
  the truncation argument of FG-2a/2b step 0 runs, carrier equality
  H′ = (ker T̂_c)^⊥ follows, seating (§1) is solved, and IDENTIFY's
  main cost (§3.2) collapses. **Price: M–L.** The uncertainty is the
  order bridge: `cfc`'s order API is stated for C*-algebra elements,
  and the corpus has no precedent for transporting it to form
  pairings of CLMs.
* **FG-2c-1 — the resolvent family at general λ > 0.** R_λ for all
  λ > 0, symmetric, ‖R_λ‖ ≤ 1/λ, in CLM form, plus ‖(λR_λ)^k‖ ≤ 1
  for all k (induction from the CLM bound — S once the family
  exists). Full analysis in §5: this is a **replay at a price**,
  not verbatim and not new analysis. **Price: M.**
* **FG-2c-2 — Route A CONSTRUCT.** Strong convergence of
  `(nR_n)^n x` for x ∈ H′ (pointwise `Filter.Tendsto`; no library
  Hille–Yosida to invoke — a bespoke Trotter–Kato-shaped argument
  through the form and a core). **Price: L–XL.** Depends on
  FG-2c-1; its core estimates consume §3.3.
* **FG-2c-3 — Route B CONSTRUCT.** Yosida approximants Ĥ_n as CLMs
  on H′ (self-adjoint, ≥ 0 bookkeeping in the CLM algebra),
  `exp(−Ĥ_n)` via `NormedSpace.exp`, strong convergence on H′.
  The exp step is library-real (bounded operators), so this is
  strictly cheaper than FG-2c-2 at the construction step; the
  strong-limit theorem is still bespoke. **Price: L.** Depends on
  FG-2c-1.
* **FG-2c-4 — IDENTIFY (Sense C).** The uniqueness-through-form
  theorem of §2 plus verification of its clauses for the candidate
  delivered by FG-2c-2 or FG-2c-3. **Price: M–L**, with the top of
  the band consumed exactly when FG-2c-0 has not discharged step 0
  (§3.2 at bespoke cost).

**Route totals.** Route A (0+1+2+4): **XL**. Route B (0+1+3+4):
**L–XL** — the recommended full route if FG-2c-0 lands FULL, since
its only bespoke analysis is one strong-limit theorem. Route C
standalone (0+4 without 2/3): **M–L**, but it delivers a uniqueness
theorem about T̂_c with no Ĥ-side candidate to identify — it does
*not* close FG-2c and is not recommended as a terminal brick.

## §5. The λ question — is the general-λ resolvent a replay?

**Verdict: a replay at a real price (M, FG-2c-1) — not verbatim,
not new analysis.** Verified from the FG-2b module itself:

* The landed construction is hard-wired at λ = 1 at the definitional
  level: `sliceFormInner` is *defined* as ambient inner product
  **plus** `sliceFormB` (unit weights), the functional fed to Riesz
  is `v ↦ ⟪f, v⟫`, and `InnerProductSpace.toDual` on the FG-2a form
  Hilbert space does the rest. No λ parameter exists to specialize.
* For λ > 0 the weak resolvent equation is
  `sliceFormB u v + λ⟪u, v⟫ = ⟪f, v⟫`. The Riesz step is *literally
  the same step* (`toDual` applied to the form Hilbert space with
  inner product J_λ(u, v) := sliceFormB u v + λ⟪u, v⟫).
* The one genuinely new lemma is **completeness transport**: J_λ is
  definite (diagonal ≥ λ‖u‖²) and its norm is equivalent to the
  landed J_1 norm (two-sided bound by max(1, λ)/min(1, λ), since the
  form diagonal is ≥ 0), so the form domain is complete in the J_λ
  norm because Cauchy sequences coincide under equivalent norms.
  FG-2a's completeness theorem is stated for J_1 only; transporting
  it is a single bounded lemma, routine but not free.
* Everything downstream in FG-2b §3 (linearity via uniqueness,
  symmetry, the bound — now ‖R_λ‖ ≤ 1/λ, CLM packaging, injectivity,
  range characterization) replays with λ weights through proofs that
  are long in the house's explicit-hypothesis style. The λ = 1
  module is 41 strict; a parameterized rebuild is honestly an M,
  dominated by mechanical re-derivation, with zero new ideas.
* Not needed at this scope, named so its absence is a decision and
  not an oversight: the resolvent identity
  R_λ − R_μ = (μ − λ) R_λ R_μ. Neither Sense A nor Sense B as priced
  consumes it.

## §6. Pre-registered kills

* **K-FG2c-0 (step-0 discharge).** If `cfc` polynomial agreement or
  the order-to-pairing bridge provably fails for
  `sliceHatCompleted` as carried (an instance-level obstruction, or
  a counterexample pairing to the bridge), step 0 stays obstructed.
  This is **not** a project kill: Routes A/B proceed with IDENTIFY
  at full bespoke price (FG-2c-4 at the top of its band).
* **K-FG2c-A (Sense A).** An exhibited x ∈ H′ on which
  `(nR_n)^n x` is not Cauchy, or converges to a limit ≠ T̂_c x
  (detected by a pairing computation), kills Sense A as stated.
* **K-FG2c-B (Sense B).** A named vector on which `exp(−Ĥ_n) x`
  converges strongly to something ≠ T̂_c x, or a failure of the
  self-adjoint / ≥ 0 bookkeeping for Ĥ_n in the CLM algebra that no
  re-seating repairs, kills Sense B as stated.
* **K-FG2c-C (Sense C).** A second self-adjoint contraction,
  ≠ T̂_c, exhibited satisfying clauses (i)–(iii) of §2 kills
  identification-through-form — and would wound the FG-2b reading
  (the form would no longer determine the seat's operator), so this
  kill, if it fires, is reported at corpus level, not brick level.
* **Global.** No kill is registered against the classical statement
  itself: Kato uniqueness for Ĥ and the classical semigroup theory
  are not in doubt. Every kill above is a kill of a *route in this
  library at this seat*, reported as such.

## §7. Recommendation — the first brick

**Commission FG-2c-0 first** (`cfc` assembly for T̂_c + step-0
discharge attempt, M–L). Three reasons, in order of weight:

1. It is on the critical path of *every* route: seating (§3.1),
   IDENTIFY (§3.2), and Route A's core estimates (§3.3) all consume
   the mixed pairings it would deliver; and its FULL verdict closes
   two standing residues as by-products — the FG-2a density residue
   and the carrier equality H′ = (ker T̂_c)^⊥.
2. Its PARTIAL still pays in full: an assembled `cfc` for
   `sliceHatCompleted` is a permanent corpus asset (the first
   functional calculus ever wired to the completed transfer
   operator), and it converts FG-2c-4's price from a band to a
   number.
3. It is the only brick whose verdict reprices all the others.
   FG-2c-1 (the λ family) is independent of it and is the natural
   second brick, in either order of completion.

**Verdicts FG-2c-0 can return.** **FULL** — mixed pairings proved,
step 0 discharged, carrier equality and seating in hand; FG-2c then
proceeds down Route B at L–XL total remaining. **PARTIAL** — `cfc`
assembled for T̂_c but the order-to-pairing bridge obstructed, with
the obstruction named exactly; routes proceed with IDENTIFY at
bespoke cost (FG-2c-4 top of band). **KILL** — `cfc` inapplicable
to `sliceHatCompleted` as carried, obstruction named at the instance
level; FG-2c re-scopes to Routes A/B with a bespoke IDENTIFY and
step 0 returns to the shelf as a named absence. No verdict of
FG-2c-0 touches FG-2a or FG-2b: both stand as landed under every
outcome above.

*End of gate paper. NO CLAIM. Dials 0/4.*
