# SCOPING — SHELF-8a GENERAL CONTOUR GATE — 2026-11-01

**Commission:** Jeff, 2026-11-01 17:11 EST — SHELF-8a's
general contour form unparked for GATE-WORK (scoping and
pricing only). This dossier is the deliverable. No Lean
was built, no tree file edited, nothing committed.
**NO CLAIM; dials 0/4.** Prices are planning estimates
(T2-grade), not theorems; every pin-content claim below
is cited to file:line in the vendored pin
(Mathlib v4.35.0-rc3, this tree) at probe time
2026-11-01 and is reproducible by grep.

**Background read:** `whitepaper/shelf8a-landing-2026-11-01.md`
(SHELF-8a PARTIAL: disc fragment `hfcDisc` FULL; named
open seam = general contour Dunford–Riesz calculus +
contour independence, reverse spectral inclusion,
spectralRadius sharpening, AlgHom bundle, circle-integral
identification) and `lean/ThetLogos/HolomorphicFunctionalCalculus.lean`.

---

## §0 VERDICT (up top, at full rank)

The gate does **not** split as one brick. It splits
three ways, and the three verdicts are different:

1. **For SHELF-8b as registered** (Riesz projections for
   isolated spectral *points*): the minimal honest gate
   is a **single-circle calculus** — no general contour
   is needed, because an isolated point is separated by
   ONE circle and the pin owns the annulus Cauchy–Goursat
   theorem that makes the radius irrelevant. This gate
   **prices clean as a two-brick M chain** (GATE-A1 +
   GATE-A2, §3), every dependency owned. It does **not**
   meet the steering's single-brick criterion literally
   (one M brick cannot carry both the interface and the
   idempotence double-integral); it meets it as a chain
   of two bounded M bricks with a pre-registered PARTIAL
   seam at idempotence. **Recommendation: fire A1, then
   A2, when the parent calls it — the pack-ready frozen
   statement list is §6.**
2. **For SHELF-7b as registered** ("continuous /
   holomorphic spectral mapping **in full**", per
   `shelf7a-landing-2026-11-01.md`): the minimal honest
   gate **is** the general neighbourhood calculus, and
   that **does NOT price clean — it is L–XL and
   pin-blocked** (§2, §5). The named blockers: no winding
   number anywhere in the pin; no Cauchy theorem beyond
   disc / concentric annulus / rectangle boundary; no
   contour-system type in whose vocabulary the general
   interface could even be frozen. **7b-in-full stays
   visibly gated, blocker named, no quiet firing.**
3. **A re-scoped SHELF-7b-disc** (spectral mapping for
   `f` holomorphic on a *disc* of radius
   `> spectralRadius ℂ a`, not an arbitrary neighbourhood)
   **prices clean as a three-brick chain** (GATE-B1/B2/B3,
   §3; total M–L, 52–100 strict est.). It is a genuine,
   citable theorem the house does not own. But it is
   **not** 7b as registered: re-scoping 7b is a
   registration decision for Jeff / the parent, not
   something this scoping fires or renames on its own.

**Registration audit (a stale row, flagged at full
rank):** the 2026-10-30 shelf map's rows for 7a/7b
(Cauchy–Binet / `Matrix.permanent`) are **superseded** —
the rotation as actually landed re-registered 7a as
rational spectral mapping (`shelf7a-landing-2026-11-01.md`)
and 7b as its holomorphic successor, and
`shelf11-landing-2026-11-01.md` records "SHELF-7b/8b,
both gated on SHELF-8a's general contour form." The
8b row of the map ("Riesz / spectral projections for
isolated spectral points of a CLM, from 8a", M, 20–35)
is still the operative registration. This dossier
prices the dependents **as currently registered**, not
as the stale map rows read.

---

## §1 What the "general contour form" actually requires

For `a` in a complex Banach algebra `A` (complete,
`NormOneClass`), `U ⊆ ℂ` open with `spectrum ℂ a ⊆ U`,
`f` holomorphic on `U`, the Dunford–Riesz value
`f(a) = (2πi)⁻¹ ∮_Γ f(z) (z − a)⁻¹ dz` requires, in
dependency order:

- **(R1) A contour-system type:** a finite family of
  closed rectifiable curves in `U ∖ spectrum ℂ a` with
  winding number `1` around every point of
  `spectrum ℂ a` and `0` around every point of `Uᶜ`,
  plus an integral of an `A`-valued integrand over such
  a system.
- **(R2) Contour independence:** the integral is the
  same for every admissible system — this is the Cauchy
  integral theorem for a general domain `U` (homotopy /
  homology invariance), and it is part of the
  definition's honesty (the 8a pack's own fence: a forced
  definition resting on unproved well-definedness is
  forbidden).
- **(R3) The homomorphism package on germs:** `1 ↦ 1`,
  additivity and multiplicativity for `f, g` holomorphic
  on a *common* neighbourhood (multiplicativity is the
  double-integral + resolvent-identity argument over two
  nested systems), hence an `AlgHom` from the germ
  algebra at `spectrum ℂ a` to `A`; plus the composition
  rule `g(f(a)) = (g ∘ f)(a)` at its grade.
- **(R4) Locality:** the value depends only on the germ
  of `f` at `spectrum ℂ a` (agreement on any smaller
  neighbourhood gives the same value) — a corollary of
  R2, and the load-bearing fact behind spectral mapping.
- **(R5) Agreement with owned calculi:** polynomials
  (`Polynomial.aeval`), the disc fragment `hfcDisc`
  where both apply, and the circle-integral
  identification of `hfcDisc`.
- **(R6) Spectral mapping, both directions:**
  `spectrum ℂ (f a) = f '' spectrum ℂ a`. Forward:
  factorisation `f(z) − f(λ) = (z − λ) h(z)` with `h`
  holomorphic on the *same* neighbourhood (germ-level
  `dslope`). Reverse: if `μ ∉ f '' spectrum ℂ a` then
  `f − μ` has a holomorphic reciprocal **on some
  neighbourhood of the spectrum** (not on any disc —
  see K-GELFAND, §4), and R3 turns it into a unit
  inverse of `f(a) − μ`.

Nothing in R1–R6 is exotic; it is the textbook package
(Rudin, *Functional Analysis*, ch. 18; Conway, *A Course
in Functional Analysis*, ch. VII). The question is only
what this pin can carry.

---

## §2 Pin inventory (Mathlib v4.35.0-rc3, file-level)

### Owned — and directly load-bearing for the gate

| Item | Evidence |
|---|---|
| `circleIntegral` for Banach-valued `f : ℂ → E`, full basic API (integrability, add/sub, `integral_smul_const`, norm bounds, congr on the sphere) | `Mathlib/MeasureTheory/Integral/CircleIntegral.lean` (def line 434; API lines 178–766) |
| **Cauchy–Goursat for a concentric annulus**: circle integrals over `C(c, R)` and `C(c, r)` agree for `f` continuous on the closed annulus and differentiable off a countable set inside it | `Mathlib/Analysis/Complex/CauchyIntegral.lean:352` (`circleIntegral_eq_of_differentiable_on_annulus_off_countable`); the `(z−c)⁻¹ • f` form at line 316 |
| **Cauchy integral formula on a disc**, Banach-valued, off-countable form and `DiffContOnCl` / `DifferentiableOn` forms | `CauchyIntegral.lean:497, 533, 544, 553, 564` |
| Cauchy–Goursat for a disc (integral `= 0`) | `CauchyIntegral.lean:441, 460` |
| Cauchy theorem for a **rectangle boundary**, Banach-valued | `CauchyIntegral.lean:267–296` (`integral_boundary_rect_eq_zero_of_differentiable_on` and variants) |
| Scalar circle integral `∮ (z − w)⁻¹ dz = 2πi` for `w` inside | `CircleIntegral.lean:747` (`integral_sub_inv_of_mem_ball`); `∮ (z−c)ⁿ = 0`, `n ≠ −1`, at lines 605–640 |
| Cauchy power series: coefficients of a holomorphic function **are** circle integrals; `HasSum` of the series to the Cauchy integral | `CircleIntegral.lean:641` (`cauchyPowerSeries`), `:652` (norm bound / Cauchy estimates), `:690, 718, 728` (`hasSum_cauchyPowerSeries_integral`) |
| Resolvent differentiability: `HasDerivAt (resolvent a) (− resolvent a k ^ 2) k` on the resolvent set | `Mathlib/Analysis/Normed/Algebra/GelfandFormula.lean:53` (`hasDerivAt_resolvent_const_left`) |
| Spectrum: nonempty, compact, closed; resolvent set open | `GelfandFormula.lean:146` (`spectrum.nonempty`); `Mathlib/Analysis/Normed/Algebra/Spectrum.lean:203` (`spectrum.isCompact`), `:165` (`isOpen_resolventSet`) |
| Spectral radius as `ℝ≥0∞` supremum over the spectrum; `spectralRadius ≤ ‖a‖`; membership criterion `spectralRadius ℂ a < ‖k‖₊ → k ∈ ρ a`; Gelfand formula `‖aⁿ‖^{1/n} → spectralRadius` | `Spectrum.lean:82, 129–143, 491`; `GelfandFormula.lean:122–133` |
| Polynomial spectral mapping (consumed by 7a/8a already) | `GelfandFormula.lean:175` (`spectrum.map_polynomial_aeval`) |
| Fubini for interval integrals | `Mathlib/MeasureTheory/Integral/Prod.lean:483, 495` (`intervalIntegral_integral_swap`, `intervalIntegral_intervalIntegral_swap`) |
| Multiplication as a continuous bilinear map on a normed algebra (the tool that pulls algebra products through Bochner integrals) | `Mathlib/Analysis/Normed/Operator/Mul.lean:40` (`ContinuousLinearMap.mul`) |
| **Finite factorisation of a meromorphic function on a compact set**: `f =ᶠ[codiscrete] (∏ᶠ u, (· − u)^(divisor f U u)) • g` with `g` analytic and nowhere zero; divisor support finite on compacts | `Mathlib/Analysis/Meromorphic/FactorizedRational.lean:296` (`MeromorphicOn.extract_zeros_poles`); `Mathlib/Analysis/Meromorphic/Divisor.lean:92–114` (`finiteSupport`); consumed in-pin at `Mathlib/Analysis/Complex/JensenFormula.lean:317` |
| Analytic machinery: `DifferentiableOn → AnalyticOnNhd`, analytic order / isolated zeros, `dslope`, composition of formal power series | `CauchyIntegral.lean:710`; `Mathlib/Analysis/Analytic/Order.lean:48`; `Mathlib/Analysis/Analytic/IsolatedZeros.lean:125`; `Mathlib/Analysis/Calculus/DSlope.lean:35`; `Mathlib/Analysis/Analytic/Composition.lean:237` (`FormalMultilinearSeries.comp`) |
| Normed Cauchy product of absolutely summable series (8a's engine, already consumed) | `Mathlib/Analysis/Normed/Ring/InfiniteSum.lean:118, 146` |

### Partially owned / owned only in a weaker form

- **First resolvent identity** (`R(z) − R(w) = (w − z) •
  R(z) R(w)` for the *same* `a`): **not in the pin by
  any name** (full-tree grep of `resolvent` theorems:
  only the two-element form `resolvent_sub_resolvent`,
  `Mathlib/Algebra/Algebra/Spectrum/Basic.lean:174`, and
  differentiability). It is a short derivation from
  `resolvent_eq` (`Basic.lean:168`) and Units algebra —
  an S-sized support lemma, frozen in §6 as
  `resolvent_sub_resolvent_eq`. Not a blocker.
- **`curveIntegral`** exists
  (`Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean`,
  560 lines) but is the integral of a **real differential
  1-form** `ω : E → E →L[𝕜] F` over a `Path` in a real
  normed space; its only invariance content is the
  Poincaré lemma on convex sets
  (`CurveIntegral/Poincare.lean`). It is **not** a
  complex contour integral of an `A`-valued integrand
  and yields no Cauchy theorem on a general `U`.
  See K-CURVE-NAME, §4.
- Rectangle Cauchy theorem is owned (above), so a
  *grid* contour is not logically impossible — what is
  missing is every piece of finite-grid bookkeeping
  (boundary of a union of rectangles, common refinements,
  oriented edge cancellation). No such API exists in
  the pin (grep: `BoxIntegral` is the real divergence
  theorem, not complex contour assembly).

### Absent — the blockers for the full form

- **Winding number: absent.** No `windingNumber` /
  winding / index definition or theorem anywhere in
  `Analysis/Complex` or the curve-integral files
  (grep ∅). R1 cannot be stated, let alone proved.
- **No Cauchy integral theorem for a general domain**,
  no homotopy/homology invariance of contour integrals,
  beyond the disc / concentric-annulus / rectangle cases
  itemised above.
- **No contour-system / rectifiable-curve integral for
  `ℂ → A` integrands** in contour form: `circleIntegral`
  is circles only; there is no sum-over-arcs or
  sum-over-segments contour type with a Cauchy theorem
  attached.
- **No Dunford / holomorphic functional calculus**
  (re-confirms 8a's probe): `Dunford` occurs only at
  `Mathlib/LinearAlgebra/JordanChevalley.lean` and one
  measure-theory citation.
- **No Runge / Mergelyan approximation** (grep ∅) — the
  approximation shortcut to R6 is not owned either
  (and is circular anyway, K-CIRCULAR-APPROX).
- **No Laurent-series API** for Banach-valued functions
  (Taylor only) — relevant to pricing A2 alternatives;
  the double-integral route does not need it.

---

## §3 Decomposition into priced bricks

Interface-first throughout: each brick's definitions
and statement pins freeze before its proofs are
attempted; a brick that hits its seam lands PARTIAL
there, never by weakening a headline silently.

### GATE-A — the minimal gate for SHELF-8b (isolated points)

Setting: `a : A`, `λ ∈ spectrum ℂ a` **isolated** in the
quantitative form `specIsolatedWithin a λ R` (§6):
every other spectral point is at distance `> R` from
`λ`. The Riesz projection is the single-circle integral
of the resolvent. Why one circle suffices: the closed
disc `closedBall λ R` meets the spectrum only at `λ`,
every circle `C(λ, r)`, `0 < r ≤ R`, lies in the
resolvent set, and any two such circles bound an
annulus **inside the resolvent set**, where the pin's
annulus Cauchy–Goursat applies to the resolvent
(differentiable there by `hasDerivAt_resolvent_const_left`).

- **GATE-A1 — interface + first properties.**
  Definitions `rieszProj`, `specIsolatedWithin`;
  support lemmas (first resolvent identity,
  resolvent commutation, circle-integrability of the
  resolvent); radius independence; commutation with
  `a`; non-vanishing (`rieszProj ≠ 0`, by the
  contrapositive argument: if the projection were `0`,
  the auxiliary integral `∮ (z−λ)⁻¹ • R(z) dz` would
  exhibit `algebraMap ℂ A λ − a` as a unit, contradicting
  `λ ∈ spectrum ℂ a`).
  **Price: S–M, 18–30 strict. Dependencies: all owned
  (§2). No seam expected.**
- **GATE-A2 — idempotence.** `P * P = P` by the standard
  two-radii double integral: radii `r₁ < r₂`, first
  resolvent identity, split, Fubini-swap one term
  (`intervalIntegral_intervalIntegral_swap`, owned),
  evaluate inner integrals by
  `integral_sub_inv_of_mem_ball` (owned) and disc
  Cauchy–Goursat for `(z − w)⁻¹` with `w` outside
  (owned); products pulled through integrals via
  `ContinuousLinearMap.mul` (owned).
  **Price: M, 20–35 strict. Pre-registered PARTIAL
  seam: A2 itself.** If A2 blows past M, GATE-A lands
  PARTIAL at exactly this seam — A1's content stands,
  and 8b stays gated on the named remainder
  "idempotence of the single-circle projection",
  not on "the general contour form."

**GATE-A total: 38–65 strict, M-chain.** This ungates
8b **as registered** (isolated points; the CLM seat is
`A := E →L[ℂ] E`, a normed algebra — seat transfer is
8b's own internal step). It does **not** ungate:
projections for arbitrary clopen spectral subsets
(a connected spectral subset needs a genuine contour
system — §5), nor any part of 7b.

### GATE-B — the chain for a RE-SCOPED 7b-disc (decision-gated)

Setting: `f` holomorphic on a disc `ball 0 R` with
`spectralRadius ℂ a < R` (real coercion; `spectralRadius
ℂ a ≤ ‖a‖₊ < ∞` is owned). Coefficients are the pin's
own `cauchyPowerSeries f 0 R` coefficients, so no new
function-space is invented.

- **GATE-B1 — spectral-radius sharpening + coefficient
  bridge.** `hfcDisc` summability under
  `spectralRadius ℂ a < R` in place of `‖a‖ ≤ R`
  (Gelfand formula + comparison against a geometric
  series at an intermediate scale); `DiscSummable s
  (discCoeff f R)` for every `s < R` (Cauchy estimates,
  `norm_cauchyPowerSeries_le`); `scalarEval (discCoeff
  f R) z = f z` on the disc (`hasSum_cauchyPowerSeries_integral`
  + the disc Cauchy integral formula).
  **Price: S–M, 15–30 strict. Owned dependencies.**
- **GATE-B2 — forward inclusion at the sharp scale.**
  8a's factorisation proof (`hfcDisc_sub_scalarEval`,
  `discTail`) re-run with B1's summability in place of
  the norm scale; the scalar bound `‖λ‖ ≤ spectralRadius`
  is lines from `spectralRadius_eq_of_unital`
  (`Spectrum.lean:129`).
  **Price: S–M, 12–25 strict.**
- **GATE-B3 — reverse inclusion, hence the full disc
  spectral mapping equality**
  `spectrum ℂ (hfcDisc a (discCoeff f R)) = f '' spectrum ℂ a`.
  Proof route (all engines owned): for `μ ∉ f '' spectrum ℂ a`,
  apply `MeromorphicOn.extract_zeros_poles` to `f − μ`
  on a closed disc `closedBall 0 R'`, `spectralRadius < R' < R`
  (divisor support finite on the compact disc; the
  constant case `f ≡ μ` split off first — it is an S
  case via `spectrum.nonempty`). The factorisation
  gives `f − μ = P · g` on the disc with `P` a finite
  product of linear factors `(· − u)`, `f u = μ`, hence
  `u ∉ spectrum ℂ a`, hence `aeval a P` a product of
  units; and `g` analytic and zero-free, so `1/g` is
  analytic on a neighbourhood of the closed disc, and
  `g(a) · (1/g)(a) = 1` by B1 + 8a's `hfcDisc_mul`.
  Codiscrete-to-everywhere promotion of the
  factorisation on the open disc is continuity +
  analyticity glue (S, inside the price).
  **Price: M, 25–45 strict. Pre-registered PARTIAL
  seam: forward inclusion + polynomial case stand
  (already landed in 8a); if the factorisation glue
  blows past M, B3 lands PARTIAL with the reverse
  inclusion as the named remainder.**

**GATE-B total: 52–100 strict, M–L chain.** Honest
scope note, on the face: B3's theorem is about
**disc-presented** functions. It does not prove
locality (R4) and does not touch `f` given only on a
non-disc neighbourhood.

### Non-gating remainders (priced, explicitly NOT in the gate)

- **REM-CIRCLE-ID** — `hfcDisc a c = (2πi)⁻¹ •
  ∮ z in C(0, R), scalarEval c z • resolvent a z` for
  `‖a‖ < R`: resolvent geometric series on the circle
  (`spectrum.hasFPowerSeriesOnBall_inverse_one_sub_smul`,
  `Spectrum.lean:354`), uniform convergence on the
  circle, `TendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn`
  (`CircleIntegral.lean:448`), coefficient extraction by
  `∮ zⁿ`. **M, 25–45.** Neither dependent needs it:
  8b's projection is *defined* by its circle, and
  7b-disc is proved series-side.
- **REM-ALGHOM-DISC** — the bundled homomorphism: the
  Wiener-type coefficient algebra at scale `r`
  (sequences with `∑' ‖c n‖ rⁿ < ∞`, `discConv` as
  multiplication) as a normed algebra, and the
  `AlgHom` to `A` for `‖a‖ ≤ r`. **M, 25–40.** 8a
  already landed the homomorphism *rules* as theorems;
  neither dependent consumes the bundled type.
- **REM-COMP** — composition `(g ∘ f)(a) = g(f(a))`
  for disc series, via `FormalMultilinearSeries.comp`
  (owned) and radius bookkeeping. **M, 20–35.**
  A headline of the *full* calculus (R3), not of
  either dependent as registered.

### FULL — the general neighbourhood form (for the record)

- **FULL-1** winding number + rectifiable contour
  integral for `ℂ → A`: **L–XL, pin-blocked** (absent, §2).
- **FULL-2** Cauchy theorem / contour independence for
  a general domain: **L–XL, pin-blocked** as packaged
  API; the rectangle engine exists but the grid
  assembly (FULL-3) is the actual cost.
- **FULL-3** finite rectangle/circle-arc contour
  systems + refinement combinatorics: **L, 60–110+,
  with genuine blow-up risk** — no owned API, and
  Lean grid-refinement bookkeeping is the classic
  unbounded tail.
- **FULL-4** germ algebra + `AlgHom` bundle + locality
  + composition on germs: **M–L on top of FULL-1–3.**
- **FULL total: XL (150+ strict, tail unpriceable).**
  The interface for the full form **cannot even be
  frozen** in this pin's vocabulary: there is no
  contour-system type to write the definition's
  signature with. That is the sharpest form of the
  blocker.

---

## §4 Kills (at full rank)

- **K-DISJOINT-COVER — "finitely many disjoint discs
  can replace a contour system." KILLED.** Take
  `spectrum ℂ a` = the unit circle (realised e.g. by
  the identity element of `C(sphere 0 1, ℂ)`, or a
  bilateral shift) and `U` the annulus
  `1/2 < ‖z‖ < 3/2`. A finite family of pairwise
  disjoint closed discs covering the circle: the discs
  are compact and pairwise disjoint, so their union is
  disconnected unless one disc does the covering; but
  any closed disc containing the whole unit circle
  contains `0` (convexity: it contains `z` and `−z`),
  and `0 ∉ U`, so its closure is not in `U`.
  Connected spectra force overlapping discs, and
  overlapping discs force boundary-of-union contours —
  i.e. FULL-3. The sum-over-a-disc-cover formula also
  double-counts spectral points in overlaps. No
  disjoint-disc shortcut exists.
- **K-GELFAND-SUBALGEBRA — "prove the reverse
  inclusion through characters of the closed algebra
  generated by `a`." KILLED.** That algebra's spectrum
  of `a` is the polynomially convex hull, not
  `spectrum ℂ a`: for the bilateral shift `U`,
  `spectrum U` is the unit circle, but characters of
  the closed polynomial algebra in `U` are evaluations
  on the whole closed disc (maximum modulus makes
  every interior evaluation continuous in `‖p(U)‖`).
  Character arguments there prove mapping for the
  *filled* spectrum — a strictly larger set — so this
  route cannot yield the reverse inclusion in `A`.
  (This is also why B3 must factor `f − μ` on a disc
  and use units in `A` itself.)
- **K-CIRCULAR-APPROX — "approximate `f` by
  polynomials uniformly and pass spectral mapping to
  the limit." KILLED as a proof route.** The step
  `μ ∉ pₙ '' spectrum ℂ a ⇒ (pₙ(a) − μ)` is a unit
  with usable inverse requires a bound on
  `‖(pₙ(a) − μ)⁻¹‖`; the natural candidate inverse is
  `q(a)` for `q = 1/(pₙ − μ)`, which is holomorphic
  only on a *neighbourhood* of the spectrum — i.e. the
  bound is exactly the neighbourhood calculus being
  constructed. Circular. (Runge is also absent, §2.)
- **K-CURVE-NAME — "`curveIntegral` is the missing
  contour integral." KILLED (naming trap, K-SHELF-RENAME
  adjacent).** The pin's `curveIntegral` integrates
  real 1-forms over real paths; its invariance theorem
  is Poincaré on convex sets. Citing it as contour
  infrastructure for Dunford–Riesz would be a rename,
  not a citation.

---

## §5 Verdict and firing recommendation

- **Minimal gate, 8b: GATE-A (A1 + A2). Prices clean
  as a chain** — two bounded bricks (S–M, then M),
  every dependency owned and cited in §2, one
  pre-registered PARTIAL seam (A2 idempotence).
  It does not satisfy a literal one-brick-M reading of
  the firing criterion; nothing smaller honestly
  ungates 8b, because a Riesz projection *is* its
  idempotence, and idempotence *is* the double
  integral. **The gate stays gated until the parent
  fires A1; this dossier is the pack source (§6).**
- **Minimal gate, 7b-in-full: none exists in this
  pin.** The blockers are named in §2 (no winding
  number; no general-domain Cauchy theorem; no
  contour-system type). FULL prices XL with an
  unpriceable tail. **7b-in-full stays visibly gated
  on FULL-1/FULL-2, no quiet firing, no redefinition
  of 7b to make the gate disappear.**
- **Decision for Jeff / parent (not taken here):**
  re-scope 7b to the disc form and fire GATE-B
  (three owned-dependency bricks, M–L total), **or**
  leave 7b gated on the full form. GATE-B is priced
  and pack-ready in outline (§3) either way; its
  frozen names should be fixed in its own pack if the
  re-scope is approved.
- REM-CIRCLE-ID / REM-ALGHOM-DISC / REM-COMP remain
  named remainders of 8a, priced above, fired by
  nothing in this gate.

---

## §6 GATE-A pack-ready frozen statement list

Working labels only (naming is Jeff's hand): proposed
module `lean/ThetLogos/RieszGate.lean`, namespace
`ThetLogos`. Context for all statements:
`{A : Type*} [NormedRing A] [NormOneClass A]
[NormedAlgebra ℂ A] [CompleteSpace A] (a : A)`.
No `sorry`, no `native_decide`, headlines on exactly
`[propext, Classical.choice, Quot.sound]`, ASCII `-`.

Definitions (freeze first):

```lean
def rieszProj (a : A) (lam : ℂ) (r : ℝ) : A :=
  (2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(lam, r), resolvent a z

def specIsolatedWithin (a : A) (lam : ℂ) (R : ℝ) : Prop :=
  lam ∈ spectrum ℂ a ∧
    ∀ z ∈ spectrum ℂ a, z ≠ lam → R < ‖z - lam‖
```

GATE-A1 headlines:

```lean
theorem resolvent_sub_resolvent_eq {z w : ℂ}
    (hz : z ∈ resolventSet ℂ a) (hw : w ∈ resolventSet ℂ a) :
    resolvent a z - resolvent a w
      = (w - z) • (resolvent a z * resolvent a w)

theorem commute_resolvent_resolvent {z w : ℂ}
    (hz : z ∈ resolventSet ℂ a) (hw : w ∈ resolventSet ℂ a) :
    Commute (resolvent a z) (resolvent a w)

theorem commute_a_resolvent {z : ℂ}
    (hz : z ∈ resolventSet ℂ a) : Commute a (resolvent a z)

theorem circleIntegrable_resolvent {lam : ℂ} {r : ℝ}
    (h : ∀ z ∈ Metric.sphere lam r, z ∈ resolventSet ℂ a) :
    CircleIntegrable (resolvent a) lam r

theorem rieszProj_eq_of_le {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (h₁ : r₁ ≤ R) (h₂ : r₂ ≤ R) :
    rieszProj a lam r₁ = rieszProj a lam r₂

theorem commute_a_rieszProj (lam : ℂ) (r : ℝ) :
    Commute a (rieszProj a lam r)

theorem rieszProj_ne_zero {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    rieszProj a lam r ≠ 0
```

GATE-A2 headline (the pre-registered seam):

```lean
theorem rieszProj_mul_self {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    rieszProj a lam r * rieszProj a lam r = rieszProj a lam r
```

Optional follow-on (NOT in the minimal gate; price
S–M separately if 8b wants finite families in one
step): orthogonality `rieszProj a lam₁ r₁ * rieszProj
a lam₂ r₂ = 0` for two distinct isolated points with
disjoint separating discs — same double-integral
engine as A2, both inner integrals vanishing.

---

*End of dossier. Scoping only — nothing built, nothing
fired. NO CLAIM; dials 0/4; the general contour form
remains a named, priced, pin-blocked remainder, and
SHELF-7b-in-full remains gated on it at full rank.*
