# SCOPING REFRESH — SHELF-7b — 2026-11-02

**Commission:** Jeff's order to build SHELF-7b ("build the two
missing bricks"; SHELF-8b already complete), scoped by the parent.
This dossier is the deliverable. No Lean was built, no tree file
edited, nothing committed. **NO CLAIM; dials 0/4.** Prices are
planning estimates (T2-grade). Every pin/tree claim below is
grep-verified in this tree (Mathlib v4.35.0-rc3, vendored at
`lean/.lake/packages/mathlib/`) on 2026-11-02.

**Governing prior audit:**
`thet-logos/whitepaper/shelf-contour-gate-scoping-2026-11-01.md`
(hereafter "the contour dossier"). Landed facts relied on, names
grep-verified, not re-derived: GATE-A1
`lean/ThetLogos/RieszGate.lean` (`rieszProj`, `specIsolatedWithin`,
`resolvent_sub_resolvent_eq`, `rieszProj_eq_of_le`,
`commute_a_rieszProj`, `rieszProj_ne_zero`); GATE-A2
`lean/ThetLogos/RieszGateIdem.lean` (`rieszProj_mul_self`,
`rieszProj_mul_rieszProj_of_lt`); 8B-1
`lean/ThetLogos/RieszComplementary.lean` (`rieszComplProj` + CLM
seat forms); 8B-2 `lean/ThetLogos/RieszOrthogonality.lean`
(`rieszProj_mul_rieszProj_of_isolated_ne`) — SHELF-8b COMPLETE as
registered (`whitepaper/8b2-landing-2026-11-02.md`).

---

## (a) 7b's registered content — verbatim, two layers

**Layer 1 — the 2026-10-30 shelf map row (STALE, superseded).**
`routeb-general-scratch/scoping-shelf-map-2026-10-30.md` §4, table
rows (the 7a row included, since the supersession is joint):

> | **SHELF-7a** | Cauchy–Binet formula | Rung-9 fence (dated; pin re-check at dispatch) | S, 8–15 | — |
> | **SHELF-7b** | `Matrix.permanent` over repeated indices | Rung-10 fence (dated; pin re-check at dispatch) | S, 6–12 | — |

These rows are **not** what 7b owes. The contour dossier §0
registration audit, verbatim in substance: "the 2026-10-30 shelf
map's rows for 7a/7b (Cauchy–Binet / `Matrix.permanent`) are
**superseded** — the rotation as actually landed re-registered 7a
as rational spectral mapping (`shelf7a-landing-2026-11-01.md`) and
7b as its holomorphic successor."

**Layer 2 — the operative registration (what 7b owes).**
`shelf7a-landing-2026-11-01.md`, Fences section, verbatim:

> "SHELF-7b (continuous/holomorphic spectral mapping in full) stays
> gated on SHELF-8a's general contour form — untouched here, as
> registered."

And `shelf11-landing-2026-11-01.md` records "SHELF-7b/8b, both
gated on SHELF-8a's general contour form." The contour dossier §0.2
states the same registration: 'For SHELF-7b as registered
("continuous / holomorphic spectral mapping **in full**")'.

**Exact statement content owed by 7b-in-full** (contour dossier §1,
R1–R6, restated as the debt list): for `a` in a complex Banach
algebra `A` (complete, `NormOneClass`), `U ⊆ ℂ` open with
`spectrum ℂ a ⊆ U`, `f` holomorphic on `U`:

- (R1) a contour-system type: finite family of closed rectifiable
  curves in `U ∖ spectrum ℂ a`, winding number 1 around every
  spectral point, 0 around every point of `Uᶜ`, and an integral of
  an `A`-valued integrand over such a system — defining
  `f(a) = (2πi)⁻¹ ∮_Γ f(z) (z − a)⁻¹ dz`;
- (R2) contour independence (the value is the same for every
  admissible system — Cauchy's theorem for a general domain);
- (R3) the homomorphism package on germs (`1 ↦ 1`, additivity,
  multiplicativity for `f, g` on a *common* neighbourhood), hence
  an `AlgHom` from the germ algebra at `spectrum ℂ a` to `A`, plus
  the composition rule `g(f(a)) = (g ∘ f)(a)` at its grade;
- (R4) locality (the value depends only on the germ of `f`);
- (R5) agreement with the owned calculi (polynomial `aeval`, the
  disc fragment `hfcDisc` where both apply, circle-integral
  identification of `hfcDisc`);
- (R6) spectral mapping, both directions:
  `spectrum ℂ (f a) = f '' spectrum ℂ a`.

7a's landed debt-discharge, for contrast (grep-verified in
`lean/ThetLogos/SpectralMapping.lean`): `ratEval`,
`spectrum_ratEval` (full rational spectral mapping),
`spectrum_ringInverse_aeval`, `spectrum_ringInverse`. 7b is the
holomorphic successor of exactly that headline shape.

---

## (b) Gate-clearance decision, item by item

The historical gate sentence ("7b/8b both gated on SHELF-8a's
general contour form") was **already split by the contour
dossier itself**: §0/§5 priced a *smaller* minimal gate for 8b
(GATE-A, single-circle) and priced 7b-in-full's minimal gate as
the general neighbourhood calculus itself, separately. GATE-A and
8B landed the 8b side of that split. The question here is only
whether they touch the 7b side. They do not, except as reusable
infrastructure at one point. Item by item against §(a) R1–R6 and
against the disc re-scope (GATE-B, §(c)):

| 7b content | Cleared by GATE-A1/A2 + 8B-1/2? | Why |
|---|---|---|
| R1 contour-system type / winding number | **NO — untouched** | GATE-A/8B define nothing of the kind. `rieszProj` is one circle `C(lam, r)` around one isolated point; no finite curve family, no winding number anywhere (re-grepped, §(d)). |
| R2 contour independence, general domain | **NO — one point-instance only** | `rieszProj_eq_of_le` is independence across *concentric circles around one point*, via the pin's annulus Cauchy–Goursat. It is a genuine instance of the pattern, at the one geometry the pin's theorem covers. It proves nothing for two different contour systems, a non-circular contour, or a connected spectral set. |
| R3 germ homomorphism package + composition | **NO** | No germ algebra, no `AlgHom`, no multiplicativity for `f(z)·resolvent` integrands, no composition rule was landed. A2's double integral is the same *proof pattern* (resolvent identity + Fubini + inner-integral evaluation) with the integrand `resolvent` alone, at one centre; the pattern is reusable know-how, not a theorem 7b can cite for R3. |
| R4 locality | **NO** | Never addressed; it is a corollary of R2, which is absent. |
| R5 agreement with owned calculi | **NO (for 7b)** | GATE-A/8B prove no statement about `hfcDisc`, `aeval`, or any `f(a)`. (8a itself landed polynomial agreement for `hfcDisc`; that predates GATE-A and is 8a's, not the gate's.) |
| R6 spectral mapping, either direction, any grade beyond polynomial/rational | **NO** | No spectral-mapping statement of any holomorphic grade was landed by GATE-A/8B. Their theorems are about one projection: radius independence, commutation with `a`, nonvanishing, idempotence, complement, two-point orthogonality. None mentions `spectrum ℂ (f a)` for holomorphic `f`. |
| 7b-disc (GATE-B1/B2/B3 content, §(c)) | **NO — zero of three bricks** | GATE-B is series-side (coefficients, Gelfand formula, factorisation of `f − μ` on a disc). GATE-A/8B are integral-side at a point. The only shared lemmas are pin-owned (annulus Goursat, Fubini, `ContinuousLinearMap.mul`) and one GATE-A support lemma (`resolvent_sub_resolvent_eq`) that no B brick consumes. |
| Infrastructure genuinely banked for a future FULL attempt | **PARTIAL, honestly labeled** | First resolvent identity, resolvent commutations, circle-integrability of the resolvent, and a worked two-radii double-integral/Fubini engine now exist in-tree at Banach-algebra generality. A future FULL-4 multiplicativity proof would reuse this engine's shape. This is tooling, not clearance: no R-item above moves. |

**Decision (b), at full rank:** GATE-A/8B clear **nothing** of
7b's registered content — neither 7b-in-full nor the 7b-disc
re-scope. 7b's historical gate does **not** clear for 7b's own
content. The gate that cleared was 8b's *separate, smaller* gate,
which the contour dossier had already severed from 7b's before
either landed. Any sentence of the form "the contour gate landed,
so 7b is ungated" is K-7B-GATE-TRANSFER, registered in §(e).

---

## (c) The DISC route re-audited against the current tree

### C.1 The contour dossier's GATE-B chain, restated exactly

Setting (dossier §3, GATE-B): "`f` holomorphic on a disc
`ball 0 R` with `spectralRadius ℂ a < R` (real coercion;
`spectralRadius ℂ a ≤ ‖a‖₊ < ∞` is owned). Coefficients are the
pin's own `cauchyPowerSeries f 0 R` coefficients."

- **GATE-B1 — spectral-radius sharpening + coefficient bridge.**
  "`hfcDisc` summability under `spectralRadius ℂ a < R` in place
  of `‖a‖ ≤ R` (Gelfand formula + comparison against a geometric
  series at an intermediate scale); `DiscSummable s
  (discCoeff f R)` for every `s < R` (Cauchy estimates,
  `norm_cauchyPowerSeries_le`); `scalarEval (discCoeff f R) z =
  f z` on the disc (`hasSum_cauchyPowerSeries_integral` + the disc
  Cauchy integral formula). **Price: S–M, 15–30 strict. Owned
  dependencies.**"
- **GATE-B2 — forward inclusion at the sharp scale.** "8a's
  factorisation proof (`hfcDisc_sub_scalarEval`, `discTail`)
  re-run with B1's summability in place of the norm scale; the
  scalar bound `‖λ‖ ≤ spectralRadius` is lines from
  `spectralRadius_eq_of_unital` (`Spectrum.lean:129`).
  **Price: S–M, 12–25 strict.**"
- **GATE-B3 — reverse inclusion, hence the full disc spectral
  mapping equality** `spectrum ℂ (hfcDisc a (discCoeff f R)) =
  f '' spectrum ℂ a`. Route: "for `μ ∉ f '' spectrum ℂ a`, apply
  `MeromorphicOn.extract_zeros_poles` to `f − μ` on a closed disc
  `closedBall 0 R'`, `spectralRadius < R' < R` … The factorisation
  gives `f − μ = P · g` on the disc with `P` a finite product of
  linear factors `(· − u)`, `f u = μ`, hence `u ∉ spectrum ℂ a`,
  hence `aeval a P` a product of units; and `g` analytic and
  zero-free, so `1/g` is analytic on a neighbourhood of the closed
  disc, and `g(a) · (1/g)(a) = 1` by B1 + 8a's `hfcDisc_mul`.
  Codiscrete-to-everywhere promotion … (S, inside the price).
  **Price: M, 25–45 strict. Pre-registered PARTIAL seam: forward
  inclusion + polynomial case stand (already landed in 8a); if the
  factorisation glue blows past M, B3 lands PARTIAL with the
  reverse inclusion as the named remainder.**"

**GATE-B total as priced 2026-11-01: 52–100 strict, M–L chain.**
Dossier's scope note, on its face: "B3's theorem is about
**disc-presented** functions. It does not prove locality (R4) and
does not touch `f` given only on a non-disc neighbourhood."

### C.2 Re-verification against the current tree (2026-11-02)

1. **Spectral radius formula / `spectralRadius` — OWNED, unchanged.**
   `Mathlib/Analysis/Normed/Algebra/Spectrum.lean:82`
   (`noncomputable def spectralRadius … : ℝ≥0∞`),
   `:129` `spectralRadius_eq_of_unital`,
   `:138` `mem_resolventSet_of_spectralRadius_lt`,
   `spectralRadius_le_nnnorm` (≤ ‖a‖). **Gelfand's formula —
   OWNED:** `Mathlib/Analysis/Normed/Algebra/GelfandFormula.lean:122`
   `pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` (alias
   `gelfand_formula`), `:133` the `‖a ^ n‖` form. B1's comparison
   route has its engine.
2. **Power-series convergence at the ‖a‖-vs-radius seam — OWNED,
   and sharper than the dossier cited.**
   `Spectrum.lean:354` `hasFPowerSeriesOnBall_inverse_one_sub_smul`
   and `GelfandFormula.lean:~83` `differentiableOn_inverse_one_sub_smul`
   (resolvent series differentiable on every closed ball of radius
   `r < (spectralRadius ℂ a)⁻¹`) — the pin already carries a
   spectral-radius-sharp power-series statement for the resolvent.
   It does not do B1's job (it is about `(1 − z • a)⁻¹`, not about
   `∑' c n • a ^ n` summability), but it confirms the
   intermediate-scale comparison pattern is pin-native.
3. **`cauchyPowerSeries` API — OWNED, as cited.**
   `Mathlib/MeasureTheory/Integral/CircleIntegral.lean:641` (def),
   `:652` `norm_cauchyPowerSeries_le`, `:690/:718`
   `hasSum_cauchyPowerSeries_integral`; plus
   `Mathlib/Analysis/Complex/CauchyIntegral.lean:671/:688`
   `HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R` forms
   and `:746` the radius-∞ form for everywhere-differentiable `f`.
   The `scalarEval = f` bridge (B1c) is if anything *cheaper* than
   the dossier's route: the `HasFPowerSeriesOnBall` packaging is
   already there.
4. **`discCoeff` — DOES NOT EXIST. (Refresh finding.)** Full grep
   of pin + corpus for `discCoeff`: **∅**. The dossier's
   `discCoeff f R` was a *proposed* name for "the
   `cauchyPowerSeries f 0 R` coefficients read as a sequence
   `ℕ → ℂ`", not an owned definition. B1 must therefore *define*
   it — the natural form is
   `discCoeff f R n := cauchyPowerSeries f 0 R n (fun _ => 1)` —
   and must prove the one fact the dossier silently used: the
   coefficients do not depend on the presenting radius (two
   circles inside the disc of holomorphicity bound an annulus in
   the domain; the pin's annulus Cauchy–Goursat,
   `CauchyIntegral.lean:352`, applied to `(z)⁻¹ⁿ⁺¹ • f` gives it —
   scalar case, S-sized). B3 needs B1 stated
   radius-parametrically: it works on an intermediate closed disc
   `R' < R` while `hfcDisc` consumes the coefficients of *other*
   functions (`g`, `1/g`) through B1 applied at their own radii,
   and radius-independence is what makes "the coefficients of
   `f`" a well-defined phrase on the pin's face. See
   K-DISCCOEFF-PHANTOM, §(e).
5. **Any existing disc functional calculus, Mathlib — NONE.**
   Re-grepped: `Dunford` in the pin occurs only at
   `Mathlib/LinearAlgebra/JordanChevalley.lean` and one
   measure-theory citation; the only functional calculus is `cfc`
   for *normal* C*-algebra elements. No disc holomorphic calculus
   exists in the pin to duplicate.
6. **8a's landed `hfcDisc` fragment — what it proves, exactly**
   (`lean/ThetLogos/HolomorphicFunctionalCalculus.lean`, grep- and
   read-verified): `DiscSummable r c := Summable fun n => ‖c n‖ *
   r ^ n`; `hfcDisc a c := ∑' n, c n • a ^ n`; `scalarEval c z :=
   ∑' n, c n * z ^ n`; summability + norm bound under the **norm
   scale** `‖a‖ ≤ r` (`summable_smul_pow`, `hfcDisc_norm_le`);
   values (zero/const/monomial); polynomial agreement
   (`hfcDisc_polynomial`); homomorphism rules as theorems
   (`hfcDisc_add`, `hfcDisc_smul`, `hfcDisc_mul` under
   `discConv`); commutations; `hfcDisc_exp`; **polynomial spectral
   mapping FULL** (`spectrum_hfcDisc_polynomial`); **forward
   inclusion at the norm scale** (`scalarEval_mem_spectrum`,
   hypotheses `0 < R`, `DiscSummable R c`, `‖a‖ < R`, via
   `hfcDisc_sub_scalarEval` / `discTail`). Its own face names the
   remainders: reverse inclusion; sharpening `‖a‖ ≤ r` to
   `spectralRadius ℂ a < r`; bundled `AlgHom`; circle-integral
   identification. Critically: **8a's input is a raw coefficient
   sequence `c` — there is no `f`-presentation layer at all.** No
   theorem of 8a mentions a holomorphic function `f : ℂ → ℂ`.
7. **Duplicate or extend? EXTEND — no headline duplication.**
   B1 = 8a's named remainder "spectral-radius sharpening" *plus*
   the missing `f`-presentation layer (`discCoeff`, `scalarEval
   (discCoeff f R) = f`) that 8a never attempted. B2 = the forward
   inclusion *re-proved at the sharp scale* — the theorem is new
   (8a's has `‖a‖ < R` on its face and does not imply it), though
   its proof is a re-run; the B2 pack should first try refactoring
   `hfcDisc_sub_scalarEval`/`scalarEval_mem_spectrum` to consume
   an abstract summability hypothesis so the sharp form *replaces*
   rather than duplicates the norm-scale proof (refactor risk is
   inside B2's band). B3 = 8a's named remainder "reverse
   inclusion", giving the equality neither 8a nor any B brick
   before it states. GATE-A/8B contribute nothing to any of this
   (§(b)).
8. **B3's remaining engines — all still owned.**
   `MeromorphicOn.extract_zeros_poles`,
   `Mathlib/Analysis/Meromorphic/FactorizedRational.lean:296`;
   divisor finite support on compacts (`Divisor.lean:92–114`);
   `spectrum.nonempty` (`GelfandFormula.lean:146`); 8a's
   `hfcDisc_mul` (landed, item 6). No engine has moved or been
   renamed since 2026-11-01.

### C.3 Refreshed prices

| Brick | 2026-11-01 price | Refreshed price | Reason |
|---|---|---|---|
| GATE-B1 | S–M, 15–30 | **S–M, 18–32** | +`discCoeff` definition + radius-independence lemma the dossier itemisation silently assumed (C.2.4); partly offset by the pin's packaged `HasFPowerSeriesOnBall` forms making the `scalarEval` bridge cheaper (C.2.3). Net: band shifts up slightly, upper end firmer. |
| GATE-B2 | S–M, 12–25 | **S–M, 12–25 (unchanged)** | All cited dependencies re-verified in place; refactor-first instruction added (C.2.7), risk inside band. |
| GATE-B3 | M, 25–45 | **M, 25–45 (unchanged)** | Factorisation engine, `spectrum.nonempty`, `hfcDisc_mul` all re-verified; pre-registered PARTIAL seam (reverse inclusion as named remainder) stands verbatim. |
| **GATE-B total** | **52–100, M–L** | **55–102, M–L** | Sum of the above. |

No discount is taken for GATE-A/8B: they share no consumed lemma
with the B chain beyond pin-owned API (§(b)).

---

## (d) The FULL form's gate, re-checked

Greps run 2026-11-02 over the vendored pin and the corpus tree:

- **Winding number: still absent from the pin.** Full-pin grep
  for `windingNumber` / `winding`: **∅** in
  `Analysis/Complex/` and the curve-integral files (and no
  definition anywhere in the pin). Corpus hits are **not** the
  complex winding number: `lean/ThetLogos/PhaseWinding.lean` is a
  finite-ring phase lift whose `w : ℤ` is *data of a lift*
  (route A, its own charter) — citing it for R1 would be a naming
  trap (K-WINDING-NAME, §(e)); `ChargePumpPost.lean` uses
  "winding" in prose about a 4-ring. Neither is a contour winding
  number, neither integrates anything.
- **Contour-system vocabulary: still absent.** Corpus grep for
  "contour": only the *prose header* of
  `HolomorphicFunctionalCalculus.lean` naming the general form as
  an open remainder. No contour-system type, no rectifiable-curve
  integral for `ℂ → A` integrands, exists in pin or corpus. The
  pin's `curveIntegral` is unchanged (real 1-forms over real
  paths; Poincaré on convex sets) — K-CURVE-NAME still binds.
- **New Cauchy-theorem forms since 2026-11-01: NONE.** The pin
  has not moved (v4.35.0-rc3). Git log since the contour dossier:
  the only contour-adjacent corpus landings are GATE-A1, GATE-A2,
  8B-1, 8B-2 — all single-circle resolvent integrals. The pin's
  Cauchy inventory is exactly what it was: disc Cauchy–Goursat,
  concentric-annulus Cauchy–Goursat (`CauchyIntegral.lean:352`),
  rectangle boundary (`:267–296`), disc Cauchy integral formula
  (`:497` ff.). No general-domain, homotopy, or homology Cauchy
  theorem has appeared in either tree.
- **Runge/Mergelyan: still absent** (grep ∅) — and circular
  anyway (K-CIRCULAR-APPROX).

**Verdict (d): FULL remains XL and pin-blocked, exactly as
priced 2026-11-01.** Missing pieces, itemised (contour dossier
§3, FULL block, restated and re-verified):

- **FULL-1** winding number + rectifiable contour integral for
  `ℂ → A`: **L–XL, pin-blocked** (absent).
- **FULL-2** Cauchy theorem / contour independence for a general
  domain: **L–XL, pin-blocked** as packaged API (rectangle engine
  exists; the assembly is FULL-3).
- **FULL-3** finite rectangle/circle-arc contour systems +
  refinement combinatorics: **L, 60–110+, genuine blow-up risk**,
  no owned API.
- **FULL-4** germ algebra + `AlgHom` bundle + locality +
  composition on germs: **M–L on top of FULL-1–3.**
- **FULL total: XL (150+ strict, tail unpriceable).** The
  interface for the full form still **cannot even be frozen** in
  this pin's vocabulary — there is no contour-system type to
  write the definition's signature with. That remains the
  sharpest form of the blocker, and GATE-A/8B changed none of it:
  they are the *one-circle* calculus the dossier severed from
  FULL, not a first instalment of it.

---

## (e) Kills

**From the shelf map:** the map itself registers no 7b kills; its
7b row is the stale `Matrix.permanent` row (§(a), Layer 1) —
struck as a registration by the contour dossier's audit, not a
kill. No map kill binds 7b.

**From the contour dossier §4 — all four bind 7b, restated:**

- **K-DISJOINT-COVER — "finitely many disjoint discs can replace
  a contour system." KILLED.** Spectrum = unit circle (e.g.
  identity of `C(sphere 0 1, ℂ)`), `U` the annulus
  `1/2 < ‖z‖ < 3/2`: pairwise-disjoint closed discs covering the
  circle have disconnected union unless one disc covers it, and
  any closed disc containing the whole circle contains `0 ∉ U`
  (convexity). Connected spectra force overlapping discs, hence
  boundary-of-union contours — i.e. FULL-3. Binds FULL (and any
  attempt to assemble 7b from per-point discs — including any
  attempt to assemble it from GATE-A projections at finitely many
  points).
- **K-GELFAND-SUBALGEBRA — "prove the reverse inclusion through
  characters of the closed algebra generated by `a`." KILLED.**
  That algebra sees the polynomially convex hull, not
  `spectrum ℂ a` (bilateral shift: spectrum = unit circle,
  characters = evaluations on the whole closed disc). Character
  arguments prove mapping for the *filled* spectrum — a strictly
  larger set. **Binds B3 directly:** this is why B3 factors
  `f − μ` on a disc and builds the inverse as a unit in `A`
  itself, and why no character shortcut may be substituted for
  B3's factorisation route.
- **K-CIRCULAR-APPROX — "approximate `f` by polynomials uniformly
  and pass spectral mapping to the limit." KILLED as a proof
  route.** The needed bound on `‖(pₙ(a) − μ)⁻¹‖` has as its
  natural candidate inverse `q(a)` for `q = 1/(pₙ − μ)`,
  holomorphic only on a *neighbourhood* of the spectrum — exactly
  the calculus being constructed. Circular. (Runge also absent.)
  Binds 7b-in-full and any proposed B-chain shortcut alike.
- **K-CURVE-NAME — "`curveIntegral` is the missing contour
  integral." KILLED (naming trap).** The pin's `curveIntegral`
  integrates real 1-forms over real paths; its invariance theorem
  is Poincaré on convex sets. Binds FULL-1: it may never be cited
  as contour infrastructure for Dunford–Riesz.

**New kills registered by this refresh:**

- **K-7B-GATE-TRANSFER — "GATE-A + 8B landing clears 7b's gate,
  because the shelf record gated 7b and 8b together." KILLED.**
  The joint gate sentence was severed by the contour dossier
  itself (§0/§5) *before* either chain landed: 8b's minimal gate
  priced as GATE-A (38–65, single-circle), 7b-in-full's as FULL
  (XL, pin-blocked), 7b-disc's as GATE-B — three separate gates.
  §(b) verifies item-by-item that the landed chains prove no
  R-item and no B-brick. Shared provenance in one scoping dossier
  is not shared content.
- **K-DISCCOEFF-PHANTOM — "`discCoeff f R` is owned API the B
  chain consumes." KILLED.** Grep ∅ over pin + corpus (§(c).C.2.4).
  It is a name the contour dossier *proposed*; B1 must define it
  and prove its radius independence. Quoting B1 as resting on an
  existing `discCoeff` would be a K-SHELF-RENAME-grade citation
  error.
- **K-WINDING-NAME — "`PhaseWinding` owns a winding number, so
  FULL-1's vocabulary partly exists." KILLED (naming trap,
  K-CURVE-NAME grade).** `PhaseWinding.lean`'s `w : ℤ` is lift
  data on a finite ring, with no curve, no integral, and no
  complex domain. It supplies no part of R1.

---

## (f) THE DECISION

Under Jeff's order to build 7b, "build 7b" honestly consists of
exactly this, and nothing else: **first a statement pin, 7B-PIN,
which (i) registers 7b-disc — spectral mapping
`spectrum ℂ (hfcDisc a (discCoeff f R)) = f '' spectrum ℂ a` for
`f` holomorphic on a disc `ball 0 R` with
`spectralRadius ℂ a < R` — as the buildable content Jeff's order
fires, under that name and never as "7b in full"; (ii) states the
GATE-B1/B2/B3 target Props at the refreshed prices (55–102 strict
total, M–L) as its frozen build list; and (iii) carries
7b-in-full's gate on its face, itemised as FULL-1–FULL-4 (XL,
150+ strict, tail unpriceable, interface unfreezable in the pin's
vocabulary) — because the record is unambiguous that 7b-in-full's
own gate did not clear: GATE-A/8B landed a different, severed
gate and prove no part of 7b's content (§(b)), and the full form
remains pin-blocked on the same three absences as on 2026-11-01
(§(d)).** Then the GATE-B chain fires brick by brick after the
pin, B1 → B2 → B3, with B3's pre-registered PARTIAL seam (reverse
inclusion as named remainder) carried verbatim. 7b-disc is a
genuine, citable theorem the house does not own — it discharges
two of 8a's own named remainders at the disc grade — and it is
**not** 7b as registered: the registration split (disc built now,
full form visibly gated on FULL-1/FULL-2) is stated on the pin's
face so no later sentence can quote the disc landing as the full
form. The pin asserts nothing; no dial moves (0/4); NO CLAIM.

---

## (g) Pack-ready frozen statement list for 7B-PIN + first brick outline

Working labels only (naming is Jeff's hand). Proposed module:
`lean/ThetLogos/Shelf7bPin.lean`, namespace `ThetLogos`.
Context for all statements:
`{A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A]
[CompleteSpace A] [Nontrivial A] (a : A)`.
Conventions: no `sorry`, no `native_decide`, ASCII `-`;
`spectralRadius ℂ a` is `ℝ≥0∞` — the pin freezes the real-scale
hypothesis in the form `(spectralRadius ℂ a).toReal < R`
(sane: `spectralRadius ℂ a ≤ ‖a‖₊ < ∞` is pin-owned).
**The pin contains definitions and `Prop`-valued target
statements only — it proves and asserts nothing.**
Pin price: **S, 4–8 strict.**

### Definitions (freeze first)

```lean
/-- Coefficients of `f` at `0`, presented at radius `R`:
the pin's `cauchyPowerSeries` read as a sequence. -/
def discCoeff (f : ℂ → ℂ) (R : ℝ) (n : ℕ) : ℂ :=
  cauchyPowerSeries f 0 R n (fun _ => 1)

/-- `f` presented holomorphically on the disc of radius `R`. -/
def DiscHolomorphic (f : ℂ → ℂ) (R : ℝ) : Prop :=
  0 < R ∧ DifferentiableOn ℂ f (Metric.ball 0 R)
```

### Frozen target Props (the GATE-B build list)

```lean
/-- B1a: the coefficients do not depend on the presenting radius. -/
def Shelf7bB1CoeffIndep (f : ℂ → ℂ) (R : ℝ) : Prop :=
  DiscHolomorphic f R →
    ∀ R₁ R₂ : ℝ, 0 < R₁ → R₁ < R → 0 < R₂ → R₂ < R →
      discCoeff f R₁ = discCoeff f R₂

/-- B1b: Cauchy-estimate summability at every interior scale. -/
def Shelf7bB1Summable (f : ℂ → ℂ) (R : ℝ) : Prop :=
  DiscHolomorphic f R →
    ∀ s : ℝ, 0 ≤ s → s < R → DiscSummable s (discCoeff f R)

/-- B1c: the scalar series value is `f` on the disc. -/
def Shelf7bB1ScalarEval (f : ℂ → ℂ) (R : ℝ) : Prop :=
  DiscHolomorphic f R →
    ∀ z : ℂ, ‖z‖ < R → scalarEval (discCoeff f R) z = f z

/-- B1d: `hfcDisc` summability at the spectral-radius scale
(the sharp form of 8a's `summable_smul_pow`). -/
def Shelf7bB1Sharp (a : A) (f : ℂ → ℂ) (R : ℝ) : Prop :=
  DiscHolomorphic f R → (spectralRadius ℂ a).toReal < R →
    Summable fun n => ‖discCoeff f R n • a ^ n‖

/-- B2: forward inclusion at the sharp scale. -/
def Shelf7bB2Forward (a : A) (f : ℂ → ℂ) (R : ℝ) : Prop :=
  DiscHolomorphic f R → (spectralRadius ℂ a).toReal < R →
    ∀ lam ∈ spectrum ℂ a, f lam ∈ spectrum ℂ (hfcDisc a (discCoeff f R))

/-- B3 (headline of 7b-disc): the disc spectral mapping equality. -/
def Shelf7bDisc (a : A) (f : ℂ → ℂ) (R : ℝ) : Prop :=
  DiscHolomorphic f R → (spectralRadius ℂ a).toReal < R →
    spectrum ℂ (hfcDisc a (discCoeff f R)) = f '' spectrum ℂ a
```

### On the pin's face (header, verbatim-grade, not formalised)

- The FULL gate list FULL-1–FULL-4 with prices (§(d)) and the
  sentence: "7b-in-full is UNSTATABLE in the pin's current
  vocabulary (no winding number, no contour-system type) and
  remains gated at XL; this pin freezes no target Prop for it,
  because there is no signature to freeze it in."
- The kills K-DISJOINT-COVER, K-GELFAND-SUBALGEBRA,
  K-CIRCULAR-APPROX, K-CURVE-NAME, K-7B-GATE-TRANSFER,
  K-DISCCOEFF-PHANTOM, K-WINDING-NAME, each in one line.
- The fence: "7b-disc is NOT 7b-in-full and may never be quoted
  as it. NO CLAIM; dials 0/4."

### First build brick after the pin — GATE-B1 pack outline

- **Module (working label):** `lean/ThetLogos/HfcDiscSharp.lean`
  (extends, does not edit, `HolomorphicFunctionalCalculus.lean`
  in v1; the B2 refactor question is B2's own pack decision).
- **Price: S–M, 18–32 strict.** Seam (pre-registered): if the
  Gelfand-comparison summability (B1d) blows past M, B1 lands
  PARTIAL there with B1a/B1b/B1c standing and B1d as the named
  remainder; B2/B3 do not fire off a PARTIAL B1d.
- **Contents, in order:** (1) `discCoeff` + `discCoeff_indep`
  (annulus Cauchy–Goursat `CauchyIntegral.lean:352` applied to
  the scalar kernel `(z)⁻¹ⁿ⁺¹ • f`; radius-independence of the
  defining circle integral); (2) `discSummable_discCoeff`
  (B1b; Cauchy estimates via `norm_cauchyPowerSeries_le`,
  `CircleIntegral.lean:652`); (3) `scalarEval_discCoeff_eq`
  (B1c; via `hasSum_cauchyPowerSeries_integral`, `:718`, or the
  `HasFPowerSeriesOnBall` forms `CauchyIntegral.lean:671/688`);
  (4) `summable_smul_pow_of_spectralRadius_lt` (B1d; Gelfand's
  formula `GelfandFormula.lean:122/133` + geometric comparison
  at an intermediate scale `ρ`, `(spectralRadius ℂ a).toReal <
  ρ < R`, consuming (2) at scale `ρ`).
- **Dependencies:** all pin-owned or 8a-landed, re-verified
  §(c).C.2. Consumes **nothing** from GATE-A/8B.
- **Axiom fence:** headlines on exactly
  `[propext, Classical.choice, Quot.sound]`.

---

*End of dossier. Scoping only — nothing built, nothing fired.
NO CLAIM; dials 0/4; 7b-disc is not 7b-in-full; SHELF-7b-in-full
remains gated on FULL-1/FULL-2 at full rank.*
