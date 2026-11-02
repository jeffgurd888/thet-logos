# SCOPING — SHELF-8b (Riesz projections, post-gate) — 2026-11-02

**Commission:** parent, 2026-11-01 — scope SHELF-8b now
that its gate (GATE-A1 + GATE-A2) is complete; pack-ready
dossier is the deliverable. No Lean built, no repo file
edited, nothing committed. **NO CLAIM; dials 0/4.**
Prices are planning estimates (T2-grade), not theorems.

**Sources read (targeted):**
- Shelf map: `routeb-general-scratch/scoping-shelf-map-2026-10-30.md:158`
  (the operative 8b registration; also cited at
  `whitepaper/shelf-contour-gate-scoping-2026-11-01.md:69-72`).
- Gate dossier: `whitepaper/shelf-contour-gate-scoping-2026-11-01.md`
  (§0 verdict, §3 GATE-A, §5, §6 frozen list).
- Gate landings: `whitepaper/gatea1-landing-2026-11-01.md`,
  `whitepaper/gatea2-landing-2026-11-01.md`.
- Landed modules: `lean/ThetLogos/HolomorphicFunctionalCalculus.lean`
  (SHELF-8a), `lean/ThetLogos/RieszGate.lean` (GATE-A1),
  `lean/ThetLogos/RieszGateIdem.lean` (GATE-A2).

## §0 VERDICT (up top, at full rank)

1. **The map's 8b row is one line, and it is thinner
   than every candidate expansion put to this scoping.**
   Verbatim (§a): "Riesz / spectral projections for
   isolated spectral points of a CLM, from 8a", **M,
   20–35**, dep SHELF-8a. It registers a *projection*,
   not a calculus: no local `f(a)`, no spectral
   splitting, no `f(λ)·P` decomposition, no
   multiplicativity is written in the row.
2. **The gate already delivered the row's mathematical
   core — and already overspent its band.** GATE-A1
   landed strict 13, GATE-A2 strict 28 (total **41 >
   20–35**), at *Banach-algebra* generality, which
   strictly subsumes the row's CLM seat
   (`A := E →L[ℂ] E`). What remains of 8b *as
   registered* is seat transfer + the complementary
   projection + two-point orthogonality: **8B-1 + 8B-2,
   25–48 strict** (§2).
3. **The candidate expansions are real mathematics and
   priceable, but they are EXTENSIONS beyond the row,
   not the row.** Local single-circle calculus at the
   isolated point (8B-3), algebra-level spectral
   splitting *inclusions* (8B-4), and the disc-calculus
   decomposition against 8a (8B-5) bring the full
   candidate programme to **87–163 strict, L-chain
   total**. Firing any of 8B-3/4/5 is a registration
   decision for the parent/Jeff, exactly as the 7b-disc
   re-scope was in the gate dossier — this scoping
   prices them, it does not fire or rename them.
4. **First brick is pack-ready: 8B-1** (complementary
   projection + CLM seat), **S, 10–18 strict, no seam
   expected**, frozen statements in §4. Every
   dependency is landed; the only integrability form
   any 8b statement may consume is the corrected
   `circleIntegrable_resolvent_of_nonneg`
   (`RieszGate.lean:135`) — the killed headline-4 form
   `circleIntegrable_resolvent` does not exist in the
   tree and must never be re-cited (§3, K-8B-KILLED-FORM).
5. **The fence (§5) is unchanged in kind:** 8b is not
   7b's general contour calculus, gives no projections
   for non-isolated / connected spectral subsets, and
   the disc re-scope of 7b stays a separate untaken
   decision.

## §1 (a) What 8b's statement content is, exactly

### The registration, verbatim

`scoping-shelf-map-2026-10-30.md:158`:

> | **SHELF-8b** | Riesz / spectral projections for
> isolated spectral points of a CLM, from 8a |
> Transport scoping's Mathlib-gap flag (1), second
> half; FG-2c Route A′ battery pairing | M, 20–35 |
> SHELF-8a |

The gate dossier re-confirmed this row as "still the
operative registration"
(`shelf-contour-gate-scoping-2026-11-01.md:69-72`), and
GATE-A2's landing states the remaining task in one
sentence (`gatea2-landing-2026-11-01.md:40-44`):
"SHELF-8b itself (the projection form of the general
contour statement at isolated points) is the follow-on
brick, to be scoped from the shelf map."

### What the gate already landed (consumed, never rebuilt)

Context for all: `{A : Type*} [NormedRing A]
[NormOneClass A] [NormedAlgebra ℂ A] [CompleteSpace A]`.

- `rieszProj a lam r := (2πi)⁻¹ • ∮ z in C(lam, r),
  resolvent a z` — `RieszGate.lean:60`.
- `specIsolatedWithin a lam R := lam ∈ spectrum ℂ a ∧
  ∀ z ∈ spectrum ℂ a, z ≠ lam → R < ‖z − lam‖` —
  `RieszGate.lean:66`.
- Radius independence `rieszProj_eq_of_le`
  (`RieszGate.lean:199`); `commute_a_rieszProj`
  (`:211`); `rieszProj_ne_zero` (`:232`) — all FULL.
- Idempotence `rieszProj_mul_self`
  (`RieszGateIdem.lean:596`), via the two-radii form
  `rieszProj_mul_rieszProj_of_lt` (`:563`) — FULL; its
  pre-registered PARTIAL seam did not trigger.
- Corrected integrability:
  `circleIntegrable_resolvent_of_nonneg`
  (`RieszGate.lean:135`). Headline 4 of GATE-A1 as
  frozen (`circleIntegrable_resolvent`, hypothesis over
  `Metric.sphere lam r`, vacuous for `r < 0`) was
  **KILLED AS STATED** — counterexample `A = ℂ, a = 1,
  lam = 0, r = −1` — and replaced by the corrected form
  (`gatea1-landing-2026-11-01.md`, K-A1-4).

So a bona fide Riesz projection at an isolated point
*already exists in the tree*. 8b's remaining content
is what turns that object into the registered
deliverable and — only if separately registered — into
a local calculus.

### Candidate adjudication (against the row, one by one)

| Candidate put to this scoping | In the row? | Disposition |
|---|---|---|
| Calculus of `f` holomorphic near an isolated point, evaluated via the Riesz projection (single-circle `∮ f(z)·R(z) dz`) | **No** — the row names projections, not a calculus of functions | Priced as EXTENSION 8B-3. Honest note: it needs no general contour — one circle + holomorphicity on a *disc* around `lam` suffices, same annulus engine as GATE-A1. |
| Spectral splitting — spectrum of `a` restricted to the projection's range | **No** | Priced as EXTENSION 8B-4, and only at algebra level (inclusions + `lam`-exclusion for ambient spectra of `a·P`, `a·(1−P)`). The CLM-restriction form (`spectrum` of `a` as an endomorphism of `range P`) is **not priceable clean** — §3, seam S-8B-4. |
| `f(a) = f(λ)·P +` (terms on the complementary projection) | **No** | Priced as EXTENSION 8B-5, and only for `f` already evaluated by 8a's *disc* calculus, where the identity is one multiplication of a landed factorisation by `P` (see 8B-5). The bare form `f(a) = f(λ)·P` is **false** — K-8B-SCALAR-ONLY, §3. The `(1−P)` term is carried unevaluated: no calculus on the complement exists without a contour around the rest of the spectrum. |
| Multiplicativity on the isolated part | **No** | Lives inside 8B-3 as its headline seam (double integral, GATE-A2's engine). Not a standalone registered item. |

**Plain statement of the gap:** if the parent wants
only what the map registered, 8b is 8B-1 + 8B-2 and
closes at S–M scale. Everything beyond that is new
registration, however standard the mathematics is.

### SHELF-8a's PARTIAL seam, exactly (what 8b inherits)

8a landed FULL its disc fragment and PARTIAL at its
pre-registered seam (`HolomorphicFunctionalCalculus.lean`,
module face; `shelf8a-landing-2026-11-01.md`):

- Landed: `DiscSummable` (`:143`), `hfcDisc a c :=
  ∑' n, c n • a ^ n` (`:153`), `scalarEval` (`:158`);
  values/const/monomial/polynomial agreement
  (`hfcDisc_polynomial`); `hfcDisc_add/smul/mul`
  (mul `:301`, via `discConv`); commutations
  (`commute_a_hfcDisc :316`); `hfcDisc_exp`;
  polynomial spectral mapping FULL; forward disc
  inclusion `scalarEval_mem_spectrum` (`:589`) via the
  factorisation `hfcDisc_sub_scalarEval` (`:553`):
  `hfcDisc a c − scalarEval c lam • 1 =
  (a − lam • 1) * hfcDisc a (discTail c lam)`.
- **Stayed open (named remainders, verbatim grade):**
  the general contour (Dunford–Riesz) definition +
  contour-system independence; the *reverse* spectral
  inclusion for the disc fragment; sharpening
  `‖a‖ ≤ r` to `spectralRadius ℂ a < r`; the bundled
  `AlgHom` package; the identification of `hfcDisc`
  with the circle integral of `f · resolvent`.
  8b consumes none of these except where 8B-5
  explicitly routes around the circle identification
  (series-side, §2).

## §2 (b) Brick decomposition, with prices

Dependencies are cited by landed theorem name /
file:line. All bricks: no `sorry`, no `native_decide`,
headlines on exactly
`[propext, Classical.choice, Quot.sound]`, ASCII `-`.

### Registered remainder (closes 8b as registered)

- **8B-1 — Complementary projection + CLM seat.**
  `rieszComplProj := 1 − rieszProj`; its idempotence,
  both orthogonality products against `rieszProj`,
  `P + (1−P) = 1`, commutation with `a`, the split
  `a = a·P + a·(1−P)`; then the CLM seat
  (`A := E →L[ℂ] E`, no new definition): commutation
  as an *application* identity and range-invariance of
  the projection. Pure algebra from
  `rieszProj_mul_self` (`RieszGateIdem.lean:596`) +
  `commute_a_rieszProj` (`RieszGate.lean:211`).
  **Price: S, 10–18 strict. No seam expected.**
  Pack-ready frozen list: §4.
- **8B-2 — Two-point orthogonality.** For distinct
  isolated points `lam₁ ≠ lam₂` with disjoint
  separating discs (`r₁ + r₂ < ‖lam₂ − lam₁‖` grade
  hypothesis, radii inside each isolation radius):
  `rieszProj a lam₁ r₁ * rieszProj a lam₂ r₂ = 0`.
  This is the gate dossier's "optional follow-on …
  same double-integral engine as A2, both inner
  integrals vanishing"
  (`shelf-contour-gate-scoping-2026-11-01.md`, §6
  tail), explicitly *not* attempted by GATE-A2.
  Engine: `rieszProj_mul_rieszProj_of_lt`'s proof
  pattern (`RieszGateIdem.lean:563`), first resolvent
  identity `resolvent_sub_resolvent_eq`
  (`RieszGate.lean:85`), Fubini swap + disc
  Cauchy–Goursat (both owned, gate §2).
  **Price: M, 15–30 strict. Seam: S-8B-2 (§3).**
  *Registered-total check: 8B-1 + 8B-2 = 25–48
  strict — i.e. even the thin remainder lands at or
  above the map's whole 20–35 band, which the gate's
  41 landed strict already exceeded. Flagged at full
  rank: the map band is spent; do not quote it as
  8b's remaining price.*

### Extensions (priced; NOT fired by this scoping)

- **8B-3 — Local single-circle calculus at `lam`.**
  Definition (working label) `rieszLocalFC a lam r f :=
  (2πi)⁻¹ • ∮ z in C(lam, r), f z • resolvent a z` for
  `f : ℂ → ℂ` differentiable on a disc around `lam`
  covering the circle. Headlines: radius independence
  (annulus Cauchy–Goursat, `CauchyIntegral.lean:352`
  in the pin, via GATE-A1's
  `circleIntegral_resolvent_eq_of_isolated`,
  `RieszGate.lean:179`); `f ≡ 1` gives `rieszProj`;
  `f = id` gives `a * rieszProj`; additivity / scalar
  rules; corner absorption `P * FC = FC = FC * P`;
  commutation with `a`. **Multiplicativity**
  `FC (f·g) = FC f * FC g` is the double-integral
  headline (GATE-A2 engine + `f, g` holomorphicity).
  Dependencies: corrected integrability only
  (`circleIntegrable_resolvent_of_nonneg`,
  `RieszGate.lean:135`, plus its `f`-weighted analogue
  proved inside the brick); `ContinuousLinearMap.mul`
  for pulling products through integrals (pin-owned,
  gate §2). **Price: M–L, 30–55 strict. Seam:
  S-8B-3 (multiplicativity).**
- **8B-4 — Algebra-level spectral splitting
  (inclusions only).** (i) Cheap half, no 8B-3 needed:
  `spectrum ℂ (a * P) ⊆ {0} ∪ spectrum ℂ a` and the
  same for `a * (1−P)` — candidate inverse for
  `μ ∉ spectrum ℂ a ∪ {0}` is
  `(algebraMap μ − a)⁻¹ * P − μ⁻¹ • (1−P)`, using only
  orthogonality (8B-1) + commutation. (ii) Sharp half,
  needs 8B-3: `spectrum ℂ (a * P) ⊆ {0, lam}` (for
  `μ ∈ spectrum ℂ a`, `μ ≠ lam`, invert `(a − μ)·P`
  inside the `P`-corner by 8B-3 applied to
  `z ↦ (z − μ)⁻¹`, holomorphic on a disc around `lam`
  avoiding `μ`); `lam ∉ spectrum ℂ (a * (1−P))`
  (corner inverse of `(a − lam)·(1−P)` from the
  `(z − lam)⁻¹`-weighted resolvent integral — the
  auxiliary-integral pattern already proved inside
  `rieszProj_ne_zero`, `RieszGate.lean:232`); corollary
  `spectrum ℂ ((a − lam • 1) * P) ⊆ {0}`.
  **Price: M, 20–35 strict ((i) S–M 8–15; (ii) M
  12–20, on top of 8B-3). Seam: S-8B-4 (§3) — full
  splitting *equalities* and CLM-restriction spectra
  are the named remainder, not part of this price.**
- **8B-5 — Disc-calculus decomposition at `lam`.**
  For `f` presented by 8a coefficients (`DiscSummable
  R c`, `‖a‖ < R`, `lam ∈ spectrum ℂ a` isolated):
  multiply the landed factorisation
  `hfcDisc_sub_scalarEval`
  (`HolomorphicFunctionalCalculus.lean:553`) by `P`:
  `(hfcDisc a c − scalarEval c lam • 1) * P =
  (a − lam • 1) * (hfcDisc a (discTail c lam) * P)`,
  i.e. `hfcDisc a c * P = scalarEval c lam • P +
  (a − lam • 1) * (hfcDisc a (discTail c lam) * P)`,
  plus `hfcDisc a c = hfcDisc a c * P + hfcDisc a c *
  (1 − P)` (8B-1 split). The `(1−P)` term is carried
  **unevaluated** (see §1 table). Optional stretch,
  separately priced and NOT in the band: identifying
  `hfcDisc a c * P` with 8B-3's `rieszLocalFC` of
  `scalarEval c` — that is the gate dossier's
  REM-CIRCLE-ID remainder (**M, 25–45**, gate §3),
  consumed by nothing here.
  **Price: S–M, 12–25 strict. No seam expected**
  (one landed identity + 8B-1 algebra; the risk is
  hypothesis bookkeeping between `specIsolatedWithin`
  radii and the disc scale `R`, which is clerical,
  not mathematical).

**Programme total:** registered remainder 25–48;
with all extensions 87–163 strict (L-chain:
8B-1 → 8B-2, 8B-1 → 8B-3 → 8B-4(ii), 8B-1 → 8B-5;
8B-4(i) needs only 8B-1).

## §3 (c) Pre-registered kills and PARTIAL seams

### Kills (at full rank)

- **K-8B-KILLED-FORM — any 8b statement consuming
  GATE-A1's original headline 4. KILLED in advance.**
  `circleIntegrable_resolvent` (no `0 ≤ r`) is false
  as stated (K-A1-4 counterexample, §1) and absent
  from the tree. Every 8b integrability hypothesis
  goes through `circleIntegrable_resolvent_of_nonneg`
  (`RieszGate.lean:135`) or an `f`-weighted analogue
  carrying `0 ≤ r` / `0 < r` on its face. Radii in 8b
  headlines are always `0 < r ≤ R`.
- **K-8B-SCALAR-ONLY — "`f(a) = f(λ)·P` on the
  isolated part." KILLED.** Counterexample: a Jordan
  block `a = [[λ, 1], [0, λ]]` (spectrum `{λ}`, so
  `P = 1`) and `f = id`: `f(a)·P = a ≠ λ·P = λ • 1`.
  The `(a − λ·1)`-term in 8B-3/8B-5 is load-bearing,
  not decoration; any brick whose proof "shows" the
  scalar-only form has proved a false statement and
  stops.
- **K-8B-COMPL-NONZERO — "`1 − P ≠ 0` as a headline."
  KILLED.** If `spectrum ℂ a = {lam}` (e.g.
  `a = lam • 1`), then `P = 1` and the complement is
  `0`. 8B-1 registers **no** non-vanishing for
  `rieszComplProj`; the asymmetry with
  `rieszProj_ne_zero` is the mathematics, not an
  omission.
- **K-8B-CLM-REPROOF — re-proving the gate at CLM
  generality. KILLED (K-SHELF-RENAME grade).** The
  gate is landed for a general Banach algebra `A`;
  the CLM seat is *instantiation* (`A := E →L[ℂ] E`),
  never a second proof. 8B-1's seat theorems are
  application-level corollaries only.
- **K-8B-EXHAUSTION — "finitely many isolated points'
  projections sum to `1`." KILLED as stated.**
  `∑ᵢ Pᵢ = 1` holds only if the `lamᵢ` exhaust
  `spectrum ℂ a`; a spectrum with any further point
  (isolated or not) is a counterexample (the missing
  point's projection is nonzero by
  `rieszProj_ne_zero`). The conditional form (finite
  spectrum, points enumerated) may be registered
  later as a corollary of 8B-2 + induction; the
  unconditional form may not.

### PARTIAL seams (pre-registered; land PARTIAL here, never weaken silently)

- **S-8B-2 (8B-2 orthogonality):** if the two-centre
  double integral blows past M, 8B-2 lands PARTIAL
  with radius independence + integrability for the
  two-point configuration standing and
  "orthogonality of distinct isolated points" as the
  named remainder. 8B-1 is unaffected; 8b-as-registered
  then closes PARTIAL at exactly this seam.
- **S-8B-3 (8B-3 multiplicativity):** if the
  `f`-weighted double integral blows past L, 8B-3
  lands PARTIAL: definition, radius independence,
  values at `1` and `id`, additivity, corner
  absorption stand; "multiplicativity of the local
  calculus" is the named remainder, and 8B-4(ii)
  stays gated on it (its corner-inverse route can
  alternatively be attempted directly — if that is
  done, the dependency is re-registered, not assumed).
- **S-8B-4 (8B-4 splitting):** the inclusions +
  `lam`-exclusion are the brick. **Full splitting is
  the seam, named in advance:** equalities
  `spectrum ℂ a = spectrum ℂ (a·P) ∪ spectrum ℂ
  (a·(1−P))`-with-`0`-bookkeeping, and any statement
  about the spectrum of `a` *as an endomorphism of
  the CLM range of `P`*, require a corner/restriction
  spectrum API (spectrum in a corner subalgebra vs
  ambient spectrum; restriction of a CLM to an
  invariant subspace as a spectrum-bearing object)
  that neither the pin nor the corpus packages.
  **This remainder is unpriceable clean in this
  scoping** — not because the mathematics is in
  doubt, but because its interface cannot be frozen
  until someone scopes the corner-spectrum API
  itself. It is 8b's analogue of the gate dossier's
  FULL verdict, at smaller scale.

## §4 (d) Pack-ready frozen statement list — first brick (8B-1)

Working labels only (naming is Jeff's hand). Proposed
module `lean/ThetLogos/RieszComplementary.lean`,
namespace `ThetLogos`, importing
`ThetLogos.RieszGate` and `ThetLogos.RieszGateIdem`.
Context for §§1–2:
`{A : Type*} [NormedRing A] [NormOneClass A]
[NormedAlgebra ℂ A] [CompleteSpace A] (a : A)`.
No `sorry`, no `native_decide`, headlines on exactly
`[propext, Classical.choice, Quot.sound]`, ASCII `-`.

Definition (freeze first):

```lean
def rieszComplProj (a : A) (lam : ℂ) (r : ℝ) : A :=
  1 - rieszProj a lam r
```

Headlines — complementary projection (no isolation
hypothesis needed except where marked; idempotence
and commutation of `rieszProj` are landed):

```lean
theorem rieszProj_add_rieszComplProj (lam : ℂ) (r : ℝ) :
    rieszProj a lam r + rieszComplProj a lam r = 1

theorem rieszComplProj_mul_self (lam : ℂ) (r : ℝ) :
    rieszComplProj a lam r * rieszComplProj a lam r
      = rieszComplProj a lam r

theorem rieszProj_mul_rieszComplProj (lam : ℂ) (r : ℝ) :
    rieszProj a lam r * rieszComplProj a lam r = 0

theorem rieszComplProj_mul_rieszProj (lam : ℂ) (r : ℝ) :
    rieszComplProj a lam r * rieszProj a lam r = 0

theorem commute_a_rieszComplProj (lam : ℂ) (r : ℝ) :
    Commute a (rieszComplProj a lam r)

theorem commute_rieszProj_rieszComplProj (lam : ℂ) (r : ℝ) :
    Commute (rieszProj a lam r) (rieszComplProj a lam r)

theorem a_eq_mul_rieszProj_add (lam : ℂ) (r : ℝ) :
    a = a * rieszProj a lam r + a * rieszComplProj a lam r
```

Headlines — radius transfer (the complement inherits
radius independence from `rieszProj_eq_of_le`,
`RieszGate.lean:199`):

```lean
theorem rieszComplProj_eq_of_le {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin a lam R) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (h₁ : r₁ ≤ R) (h₂ : r₂ ≤ R) :
    rieszComplProj a lam r₁ = rieszComplProj a lam r₂
```

Headlines — CLM seat. Context:
`{E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
[CompleteSpace E] (T : E →L[ℂ] E)`. These are
instantiations at `A := E →L[ℂ] E`; the `•`-free
application forms are the seat's deliverable
(`ContinuousLinearMap.mul_apply` is the only glue):

```lean
theorem rieszProj_clm_mul_self {lam : ℂ} {R : ℝ}
    (hR : specIsolatedWithin T lam R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    (rieszProj T lam r) * (rieszProj T lam r) = rieszProj T lam r

theorem rieszProj_clm_apply_commute (lam : ℂ) (r : ℝ) (x : E) :
    (rieszProj T lam r) (T x) = T ((rieszProj T lam r) x)

theorem rieszProj_clm_range_invariant (lam : ℂ) (r : ℝ) (x : E) :
    T ((rieszProj T lam r) x)
      = (rieszProj T lam r) (T ((rieszProj T lam r) x))
```

Explicitly **not** in this brick (fences on its face):
no `rieszComplProj ≠ 0` (K-8B-COMPL-NONZERO);
no two-point orthogonality (8B-2); no local calculus
(8B-3); no spectrum statement (8B-4).

**Price restated: S, 10–18 strict, defs 1. No seam
expected** — every headline is ring algebra over two
landed theorems or a one-step CLM instantiation; if
the count lands outside the band, report as counted
(GATE-A1 precedent: strict 13 against an 18–30 band,
reported, not padded).

## §5 (e) The honest fence — what 8b does NOT give

- **Not the general contour calculus.** Nothing in
  8b (registered or extended) defines `f(a)` for `f`
  holomorphic on an arbitrary neighbourhood of
  `spectrum ℂ a`, proves contour-system independence,
  or yields projections for arbitrary clopen spectral
  subsets. A connected spectral subset (e.g. the unit
  circle in an annulus neighbourhood) still needs a
  genuine contour system: the gate dossier's FULL
  chain (winding number, general-domain Cauchy
  theorem, contour-system type) remains **XL,
  pin-blocked, interface not freezable in this pin's
  vocabulary** (`shelf-contour-gate-scoping-2026-11-01.md`
  §§2–3). 8b works *because* an isolated point is
  separated by one circle; that trick does not
  generalise, and no 8b headline may be quoted as if
  it does.
- **Not SHELF-7b in full, and not the 7b-disc
  re-scope.** 7b-in-full ("continuous / holomorphic
  spectral mapping in full") stays gated on the
  general form. The disc re-scope (GATE-B chain,
  M–L, 52–100 strict, gate dossier §3) **stays a
  separate untaken decision** for Jeff/parent; 8B-5
  is not that re-scope — it is one factorisation
  identity against the already-landed disc fragment,
  with the reverse spectral inclusion for the disc
  fragment still open exactly where 8a left it.
- **Not a spectral theorem.** 8b gives one isolated
  point's projection (and, extended, its local
  calculus and ambient-spectrum inclusions). It gives
  no decomposition of `a` over its whole spectrum
  unless the spectrum is finite and K-8B-EXHAUSTION's
  conditional form is separately registered, no
  quasinilpotent *structure* theory beyond the
  `spectrum ⊆ {0}` corollary in 8B-4, and no
  finite-dimensional Jordan/Dunford decomposition
  (the pin's `Dunford` remains the unrelated
  Jordan–Chevalley name; citing it here would be
  K-CURVE-NAME grade).
- **Seat honesty.** The FG-2c Route A′ battery pairing
  named in the map row is a *use* of the CLM seat, not
  a consequence of 8b: 8B-1 delivers the projection as
  a CLM with range invariance; any battery statement
  consuming it is that line's own brick.
- **Tier fence.** This dossier is T2-grade scoping.
  NO CLAIM; dials 0/4; no Millennium part, no corpus
  claim, and no dial is touched by a projection
  existing — the gate landings' fence stands verbatim.

*End of dossier. Scoping only — nothing built, nothing
fired. The registered remainder (8B-1 + 8B-2) is
pack-ready at §4 for 8B-1; the extensions (8B-3/4/5)
are priced and await a registration decision.*
