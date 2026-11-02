# SCOPING — GATE-B4: discharging DiscFactorisationHyp (SHELF-7b-disc chain)

Date: 2026-11-02. Pack: `pack-gate-b4-scoping.md`. Source landing:
`thet-logos/whitepaper/gate-b3-landing-2026-11-02.md`. Pin probed
read-only: Mathlib v4.35.0-rc3, rev `516d31250e96c4e8e76888c3d8e2e43a9642b9ee`
(`thet-logos/lean/.lake/packages/mathlib`). Scoping only: no Lean
files written, no builds run.

**NO CLAIM. The hypothesis is never quietly assumed. Dials 0/4.
7b-disc is NOT 7b-in-full.**

Band convention: S = direct applications / transport, one sitting;
M = new glue lemmas, one brick; L = new machinery. No step below
prices above M on the live route.

---

## 0. HEADLINE FINDING — the literal target is KILLED; the live target is its conditional form

`DiscFactorisationHyp` as frozen (`HfcDiscSpectralMapping.lean:112`)
carries **no** `DiscHolomorphic f R` and no
`(spectralRadius ℂ a).toReal < R` antecedent:

```
DiscFactorisationHyp a f R := ∀ R₀, sr < R₀ → R₀ < R →
  ∀ mu ∉ f '' spectrum ℂ a, ∃ lam hc, …
```

As stated it is **false**, by the counterexample already in-tree
(the GATE-B1 boundary witness). Take `A` nontrivial,
`a = 0`, `R = 2`, `R₀ = 1`,
`f = fun z => if ‖z‖ = 1 then (1:ℂ) else 0`, `mu = 1`:

* `(spectralRadius ℂ (0:A)).toReal = 0 < 1 < 2`
  (in-tree: `spectralRadius_zero_toReal_lt_one`, Shelf7bPin2).
* `spectrum ℂ (0:A) = {0}` (every spectral value has norm ≤ the
  spectral radius, in-tree `norm_le_spectralRadius_toReal`), so
  `f '' spectrum ℂ (0:A) = {f 0} = {0}` and `mu = 1 ∉ {0}`.
* `hfcDisc 0 (discCoeff f 1) = discCoeff f 1 0 • 1 = 1`
  (in-tree: `hfcDisc_at_zero` + `discCoeff_boundary_counterexample`,
  `discCoeff f 1 0 = 1`), so the factorisation's LHS is
  `1 - 1 • 1 = 0`.
* Its RHS is a product of units times a unit (B3′'s own
  `isUnit_list_prod` + `isUnit_a_sub_smul_one_of_notMem_spectrum`),
  hence a unit. `0` is not a unit in a nontrivial algebra.
  Contradiction.

**K-B4-LITERAL FIRES at scoping** against the unconditional
discharge. This is the B1c/B2 pattern one level up: the frozen
statement omits the hypothesis its content needs. Under the
relabeling rule the frozen `DiscFactorisationHyp` stands beside
this kill; the live discharge target is the NEW conditional entry

```
DiscFactorisationHyp' a f R := DiscHolomorphic f R →
  (spectralRadius ℂ a).toReal < R → DiscFactorisationHyp a f R
```

whose antecedents are exactly what `Shelf7bDiscInterior` itself
supplies. Everything in §§1–3 below prices the conditional form.
Consequence for the assembly (§3): B3′'s
`shelf7bDiscInterior_proved_of_factorisation` cannot be fed
verbatim — it demands the unconditional hyp before `hf` is
introduced. A small adapter (re-running B3′'s assembly with the
hyp applied after `intro hf hsr`, reusing
`notMem_spectrum_hfcDisc_of_factorisation` and B2′ forward
verbatim) closes it. Priced in §3 as B4-REPAIR, band S. The final
headline is then an unconditional theorem *stating*
`Shelf7bDiscInterior a f R` (a Prop itself conditional on
`hf`/`hsr` — no extra hypothesis remains).

All other hypotheses in the pack check out as stated:
`hfcDisc_mul_of_summable`, `discCoeff_const` (B3′);
`discConv_discFactor`, `discTail`, `hfcDisc_sub_scalarEval_sharp`,
`summable_norm_discTail_smul_pow` (8a/B2′) exist as cited.

**K-GELFAND-SUBALGEBRA binds every route below and is respected:**
no step routes through characters of the polynomial closure or a
Gelfand spectrum. (The Gelfand *formula* — a norm limit for
`spectralRadius` — is already consumed in-tree at B1d/B2′ for norm
comparison only; that is not the banned route and no new use is
proposed.)

---

## 1. INGREDIENT 3 — finiteness + coefficient-level factorisation of the zeros of `f − mu`

### Exact statement needed (conditional form)

Fix `a f R`, `hf : DiscHolomorphic f R`, `hsr`, an interior
`R₀` (`sr < R₀ < R`), and `mu ∉ f '' spectrum ℂ a`. Put
`g := fun z => f z - mu` (`DiscHolomorphic g R` by sub-const).
Produce `lam : List ℂ` (zeros **with multiplicity**) and
`hc : ℕ → ℂ` satisfying the four conjuncts of the frozen hyp at
`discCoeff f R₀`.

Radius juggling (licensed by B1a, `discCoeff_indep`,
`HfcDiscSharp`): pick `R₀ < R₂ < R₁ < R` (two `exists_between`
steps). Factor the zeros of `g` in the **closed** disc
`closedBall 0 R₂`; present all coefficients at `R₁`. B1a gives
`discCoeff g R₁ = discCoeff g R₀` (both `< R`), so the identity
proved at `R₁` is the identity the hyp demands at `R₀`.
Working at `R₂ > R₀` (not `R₀` itself) is what buys ingredient 2
its room: the remainder is zero-free on `closedBall 0 R₂`, hence
on the open ball of radius `R₂ > R₀ > sr`.

Spectrum-avoidance is **free**, not an extra constraint: every
zero `l` of `g` has `f l = mu` definitionally, so
`l ∈ spectrum ℂ a` would put `mu ∈ f '' spectrum ℂ a`,
contradicting the hypothesis on `mu`. One line, band S.

### Steps and prices

**3a. Not-identically-zero reduction — S. K-B4-IDENTZERO: SAFE.**
If `g` were `EqOn 0` on `ball 0 R`, then for any
`lam ∈ spectrum ℂ a` (nonempty: pin `spectrum.nonempty`),
`‖lam‖ ≤ sr.toReal < R` (in-tree `norm_le_spectralRadius_toReal`),
so `f lam = mu`, i.e. `mu ∈ f '' spectrum ℂ a` — contradiction.
Hence under the hyp's own assumptions the identically-zero case
**cannot occur**; the discharge only ever handles
`g` not identically zero. The constant subcase is independently
already landed unconditional in B3′ (`discFactorisationHyp_const`,
via `discCoeff_const`); a nonzero constant `g` also flows through
the general route with `lam = []`. **The pack's question is
answered: yes, the discharge needs only `g` not-identically-zero,
and that case split is discharged by vacuity, band S.**

**3b. Analyticity transport — S, pin-supported.**
`DifferentiableOn ℂ g (ball 0 R)` → `AnalyticOnNhd ℂ g (ball 0 R)`:
pin `DifferentiableOn.analyticOnNhd`
(`Mathlib/Analysis/Complex/CauchyIntegral.lean:710`, needs the set
open — `isOpen_ball`). Direct application, likewise on every
smaller ball by restriction (`discHolomorphic_of_lt`, in-tree).

**3c. Finiteness of zeros in a closed subdisc — M.
K-B4-FIN: DOES NOT FIRE at scoping (route exists in-pin).**
There is **no packaged** "finitely many zeros on a compactum"
theorem in the pin (grep of `Mathlib/Analysis/Analytic/*`,
`Mathlib/Analysis/Complex/*`: none). But the two halves exist and
compose in ~3 steps:

1. Isolated zeros, global form (pin
   `Mathlib/Analysis/Analytic/IsolatedZeros.lean`):
   `AnalyticOnNhd.eqOn_or_eventually_ne_zero_of_preconnected`
   on the preconnected `ball 0 R₁`. The `EqOn g 0` disjunct is
   excluded by 3a transported down (identity theorem,
   `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`
   / the `eqOn_…_of_eventuallyEq_zero` family in
   `Analytic/Uniqueness.lean`: vanishing on `ball 0 R₁` gives
   frequent vanishing at `0 ∈ ball 0 R`, hence `EqOn` on
   `ball 0 R`). Surviving disjunct:
   `{z ∈ ball 0 R₁ | g z ≠ 0} ∈ codiscreteWithin (ball 0 R₁)`.
2. Compact + codiscrete ⇒ finite (pin
   `Mathlib/Topology/DiscreteSubset.lean:527`):
   `IsCompact.finite_sdiff_of_mem_codiscreteWithin`:
   `IsCompact K → s ∈ codiscreteWithin K → (K \ s).Finite`;
   or equivalently `IsCompact.finite`
   (`Topology/Compactness/Compact.lean:1055`, compact + `IsDiscrete`).
3. Glue (the actual M content): transport the codiscreteWithin
   statement from `ball 0 R₁` to `K = closedBall 0 R₂`
   (`closedBall_subset_ball`, `R₂ < R₁`; codiscreteWithin
   restriction/monotonicity + `mem_codiscreteWithin_accPt`,
   `DiscreteSubset.lean:291`), giving
   `(closedBall 0 R₂ ∩ {z | g z = 0}).Finite`; extract a
   `Finset`/`List` of distinct zeros. `closedBall` compactness is
   pin-standard (`isCompact_closedBall`).

K-B4-FIN stays **armed at build**: if step 3's filter transport
resists, the kill fires there and the hyp stays named. At scoping
the route is concrete and every load-bearing lemma is cited
in-pin, so the kill does not fire.

**3d. Multiplicity iteration + tail identification — M (the
hardest glue in ingredient 3).**
Factor one zero at a time at the `hfcDisc` level, iterating B2′'s
landed `hfcDisc_sub_scalarEval_sharp`: at a zero `lam`,
`scalarEval c lam = 0`, so the identity collapses to
`hfcDisc a c = (a - lam • 1) * hfcDisc a (discTail c lam)`.
Two sub-lemmas are NOT in-tree and must be built:

* (i) *Identification:* the iterated coefficient tail is the
  `discCoeff` of a holomorphic function — the iterated `dslope`
  `hₖ` of `g` at the factored zeros. `dslope` holomorphicity is
  pin-supported (`Mathlib/Analysis/Complex/RemovableSingularity.lean:60`,
  `differentiableOn_dslope`, applicable since `ball 0 R ∈ 𝓝 lam`
  for `‖lam‖ < R`); the coefficient identification
  `discCoeff hₖ R₁ = iterated discTail (discCoeff g R₁)` goes by
  formal-series uniqueness
  (`HasFPowerSeriesAt.eq_formalMultilinearSeries` against
  `DifferentiableOn.hasFPowerSeriesOnBall` — the exact pattern
  B3′ already lands in `discCoeff_const`). This identification
  is also what hands ingredient 2 a *function* `h` (§2).
  Fallback route if dslope identification snags: define `hₖ`
  by its `scalarEval` series and prove the one-step identity
  `(z - lam) * scalarEval (discTail c lam) z
   = scalarEval c z - scalarEval c lam` from the in-tree
  recursions `scalarEval_eq` / `discTail_pred` (8a). Either
  route is M; neither needs new pin machinery.
* (ii) *Termination/multiplicity bookkeeping:* `lam` is the
  finite zero **set** of 3c expanded by order at each point
  (order API in-pin: `HasFPowerSeriesAt.order`,
  `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`,
  `eq_pow_order_mul_iterate_dslope`, `IsolatedZeros.lean`).
  Iterate (i) while the current tail still vanishes somewhere
  in `closedBall 0 R₂`; each `discTail` step at `lam` drops the
  order at `lam` by one and creates no new zeros in the closed
  disc, so the total order over the finite set strictly
  decreases. Formalising the measure argument is the brick's
  weight. Remainder `h := h_{|lam|}` is then zero-free on
  `closedBall 0 R₂` (a zero there would be a zero of `g` there,
  factored out to full order — via the `scalarEval` form of (i)
  and corrected B1c, `scalarEval_discCoeff_eq_of_lt`).

**3e. Sharp summability of iterated tails — S–M, transport.**
B2′'s `summable_norm_discTail_smul_pow` is stated only for tails
of `discCoeff f R₀`. Its proof is, however, generic: 8a's
`discSummable_discTail` (stated for arbitrary `DiscSummable S c`)
iterated for the `DiscSummable` side, plus B1d's Gelfand
comparison (`eventually_norm_pow_le_of_discSpectralRadius_lt`)
for the `a`-side. Generalise the B2′ lemma once to iterated
tails of an arbitrary coefficient sequence with
`DiscSummable S ·`, `sr < S`; each factorisation step then
consumes it directly.

**3f. Coefficient assembly — S.**
`discCoeff g R₀ = discCoeff f R₀ - (mu at 0, else 0)` by the
`discCoeff_const` pattern (formal-series uniqueness for
`f - mu`), and `hfcDisc a (discCoeff f R₀) - mu • 1
= hfcDisc a (discCoeff g R₀)` by B3′'s
`hfcDisc_add_of_summable`-family at the sharp scale (the exact
computation B3′ performs in `discFactorisationHyp_const`).
Iterating 3d's collapsed identity over `lam` (List induction,
noncommutative `List.prod` as in B3′) gives the hyp's identity
with `hc := discCoeff h R₀` (`= discCoeff h R₁` by B1a).

**Ingredient 3 verdict: PRICEABLE, total M–L across bricks
3c (M) + 3d (M) + 3e (S–M), with 3a/3b/3f at S.**
No unpriceable sub-step. K-B4-FIN does not fire; K-B4-IDENTZERO
confirmed safe.

---

## 2. INGREDIENT 2 — zero-free holomorphic factor ⇒ `IsUnit` of its calculus value

Given `h` from §1: `DiscHolomorphic h R` (iterated `dslope` of
`g`), zero-free on `closedBall 0 R₂`, `hc := discCoeff h R₀`,
sharp-summable at `a` by B2′
(`summable_norm_smul_pow_discCoeff_interior`, applied at
holomorphicity radius `R`).

**2a. Reciprocal holomorphicity — S, pin-supported in full.**
`1/h` (pointwise `h⁻¹`) is `DifferentiableOn ℂ` on the *open*
ball of radius `R₂` (which lies inside the zero-free closed
ball): pin `DifferentiableOn.inv`
(`Mathlib/Analysis/Calculus/FDeriv/Mul.lean:775`,
`∀ x ∈ S, h x ≠ 0`); analytic form `AnalyticOnNhd.inv`
(`Analytic/Constructions.lean:1044`) also in-pin. Hence
`DiscHolomorphic (h⁻¹) R₂` with `R₀ < R₂`, and B2′ gives sharp
summability of `discCoeff (h⁻¹) R₀` at `a` (holomorphicity
radius `R₂`).

**2b. The coefficient-product identity — ABSENT in-tree and
in-pin as a lemma; DERIVABLE in one M brick (B4-PROD). Status,
precisely:**

* *In-tree:* **absent.** Grep of the whole disc chain
  (`HolomorphicFunctionalCalculus`, `HfcDiscSharp`,
  `HfcDiscForward`, `HfcDiscSpectralMapping`, pins): the only
  `discCoeff` lemmas are `discCoeff_indep`, `norm_discCoeff_le`,
  `discSummable_discCoeff`, `hasSum/scalarEval_discCoeff_eq_*`,
  `discCoeff_boundary_counterexample`, `discCoeff_const`.
  `discConv_discFactor` is a one-factor identity against
  `discTail`, not a product formula. No
  `discCoeff (h * k) = discConv (discCoeff h) (discCoeff k)`
  in any form.
* *In-pin:* **absent as stated.** No `cauchyPowerSeries (f * g)`
  lemma exists (grep: `cauchyPowerSeries` occurs only in
  `CircleIntegral.lean` / `Complex/CauchyIntegral.lean`, with no
  product law). `FormalMultilinearSeries.prod`
  (`Analysis/Calculus/FormalMultilinearSeries.lean:99`) is the
  *Cartesian* product into `F × G`, not multiplication in `ℂ`;
  `AnalyticAt.mul` / `HasFPowerSeriesOnBall.prod`
  (`Analytic/Constructions.lean:314,650`) prove analyticity of
  products via `comp₂` and **do not expose the coefficient
  series** of the product.
* *Derivable route (≈5 steps, all patterns already in-tree):*
  for `h k` holomorphic on a disc of radius `> R'`, presenting
  at interior `R'`:
  (1) the scalar Cauchy product: for `‖z‖ < R'`,
  `∑' n, discConv (discCoeff h R') (discCoeff k R') n * z ^ n
   = h z * k z`, by the pin's
  `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`
  (the same lemma 8a/B3′ consume for `hfcDisc_mul`) applied to
  the scalar series, absolute summability from B1b
  (`DiscSummable` at an interior scale `> ‖z‖`) and corrected
  B1c (`scalarEval_discCoeff_eq_of_lt`) on both factors —
  i.e. `ofScalars (discConv …)` has the right `HasSum`
  everywhere on the ball;
  (2) promote to `HasFPowerSeriesOnBall (h * k)
  (ofScalars (discConv …)) 0 R''` for interior `R'' < R'`
  (radius lower bound from the `DiscSummable` majorant via the
  `ofScalars` radius API the pin uses for the geometric series,
  `FormalMultilinearSeries.inv_le_ofScalars_radius_of_tendsto`);
  (3) `DifferentiableOn.hasFPowerSeriesOnBall` for `h * k` on
  the closed ball (`DifferentiableOn.mul`) presents
  `cauchyPowerSeries (h * k) 0 R''`;
  (4) `HasFPowerSeriesAt.eq_formalMultilinearSeries` identifies
  the two series — the exact uniqueness pattern landed in-tree
  in `discCoeff_const`;
  (5) read off coefficients: `discCoeff (h * k) R' n
  = discConv (discCoeff h R') (discCoeff k R') n` via
  `FormalMultilinearSeries.coeff` / `ofScalars` coefficient
  unfolding and B1a re-presentation `R'' ↔ R'`.
  **Price: M.** The special case `k = h⁻¹` does **not** dodge
  this brick: concluding `hfcDisc` of the convolution is `1`
  still requires identifying the convolution with
  `discCoeff 1`; only steps (1)+(4) specialise, saving little.

**2c. Unit conclusion — S (given 2b).**
Apply 2b with `k = h⁻¹` at presenting radius `R₀`: on the circle
`|z| = R₀` (indeed on `closedBall 0 R₂ ⊇` that circle)
`h * h⁻¹ = 1` pointwise, and `discCoeff` at `R₀` depends only on
circle values, so `discConv (discCoeff h R₀) (discCoeff h⁻¹ R₀)
= discCoeff (fun _ => 1) R₀ = delta` (`discCoeff_const`).
B3′'s `hfcDisc_mul_of_summable` (both sharp summabilities from
§2 head / 2a) gives
`hfcDisc a (discCoeff h R₀) * hfcDisc a (discCoeff h⁻¹ R₀) = 1`
(`hfcDisc_one`, 8a). One-sided inverse suffices because
`hfcDisc` values commute (8a `commute_hfcDisc_hfcDisc`), so
`IsUnit (hfcDisc a hc)` by `isUnit_of_mul_eq_one` + commutativity.
No Gelfand/character route anywhere.

**Ingredient 2 verdict: PRICEABLE, total M** (2a S, 2b M =
the brick, 2c S). No unpriceable sub-step.

---

## 3. ASSEMBLY — firing order closing GATE-B

```
B4-REPAIR (S)   Formalise K-B4-LITERAL (counterexample above,
                ~30 lines from in-tree lemmas); state
                DiscFactorisationHyp'; conditional assembly
                adapter mirroring B3′ (reverse inclusion via
                notMem_spectrum_hfcDisc_of_factorisation +
                B2′ forward). Defines the live target.
   │
   ├─ B4-FIN   (M)   §1 steps 3a+3b+3c: not-identically-zero
   │                 vacuity; finiteness of the zero set of
   │                 g in closedBall 0 R₂ (distinct zeros as a
   │                 Finset, with orders). [K-B4-FIN armed]
   │
   └─ B4-PROD  (M)   §2 step 2b: discCoeff (h * k)
                     = discConv (discCoeff h) (discCoeff k)
                     at interior presentations.
        (B4-FIN ∥ B4-PROD: independent — the two build lanes;
         scoping/probe work around them unlimited-parallel.)
   │
B4-TAIL  (M)    §1 steps 3d+3e: iterated-tail identification
                (discCoeff of iterated dslope = iterated
                discTail), generalised sharp summability of
                iterated tails, multiplicity iteration over
                B4-FIN's list ⇒ factorisation identity at
                hfcDisc level + zero-free remainder h on
                closedBall 0 R₂ with hc = discCoeff h R₀.
                Needs B4-FIN only.
   │
B4-UNIT  (S–M)  §2 steps 2a+2c: DiscHolomorphic (h⁻¹) R₂;
                IsUnit (hfcDisc a hc) via B4-PROD +
                hfcDisc_mul_of_summable. Needs B4-PROD + B4-TAIL.
   │
B4-ASM   (S–M)  §1 step 3f + discharge theorem:
                DiscFactorisationHyp' proved (all mu, all
                interior R₀); feed B4-REPAIR's adapter ⇒
                shelf7bDiscInterior_proved :
                Shelf7bDiscInterior a f R, unconditional.
                GATE-B (7b-disc chain) CLOSES.
```

Total price: **S + M + M + M + (S–M) + (S–M) ≈ 3 M-bricks plus
transport** — an L-sized campaign in aggregate, no single brick
above M, **no named unpriceable sub-step on the conditional
route**.

Chain verdict on completion: B1a/B1b/B1d FULL, B1c
killed-and-corrected, B2′ FULL, B3′ PARTIAL → **FULL**,
`Shelf7bDiscInterior` discharged with no named hypothesis
remaining in the disc chain. Fences unchanged: this closes
GATE-B for the **disc chain only**; 7b-in-full (general contour
systems, winding, germ algebra) remains pin-blocked and
untouched; NO CLAIM; dials 0/4.

## Kill register (pre-registered / status)

* **K-B4-LITERAL** (new, this scoping): the frozen
  `DiscFactorisationHyp` without `DiscHolomorphic`/spectral
  antecedents is false — **FIRES** (§0, in-tree counterexample).
  Live target: `DiscFactorisationHyp'` (new entry; the frozen
  form stands with its kill, per the relabeling rule).
* **K-B4-FIN**: zero finiteness on a closed subdisc unreachable
  in the pin ⇒ discharge dies, hyp stays named. **Does not fire
  at scoping** (route: IsolatedZeros codiscrete form +
  `IsCompact.finite_sdiff_of_mem_codiscreteWithin`); remains
  armed inside B4-FIN at the codiscreteWithin transport step.
* **K-B4-IDENTZERO**: `f − mu` identically zero unhandled ⇒
  seam. **Confirmed safe at scoping**: the case is vacuous under
  `mu ∉ f '' spectrum ℂ a` (§1, 3a); the discharge only needs
  `g` not-identically-zero; constant functions independently
  landed in B3′.
* **K-GELFAND-SUBALGEBRA**: binds every route above; no route
  uses characters/Gelfand spectrum. Respected throughout.
