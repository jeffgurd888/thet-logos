# REGISTRATION — SHELF 8B-3 / 8B-4 / 8B-5 (extensions beyond the 8b row) — 2026-11-02

**Commission:** Jeff's decision, 2026-11-01 23:23 EST — item 4 of the
chair list, read by the parent as UNSHELF: register and run 8B-3/4/5
(the correction door was stated to Jeff with that reading).
**SHELF-8b itself stands COMPLETE AS REGISTERED** (GATE-A chain +
8B-1 + 8B-2, all FULL). This dossier registers the three EXTENSIONS
scoped and priced in `whitepaper/shelf-8b-scoping-2026-11-02.md` —
that scoping is the source of every statement below; nothing here
invents content. Where the scoping names a seam, the seam is
registered with the brick. **NO CLAIM; dials 0/4.**

---

## Registered extensions

### 8B-3 — Local single-circle calculus at the isolated point λ

**Statement pin.** Definition (working label):
`rieszLocalFC a lam r f := (2πi)⁻¹ • ∮ z in C(lam, r), f z • resolvent a z`
for `f : ℂ → ℂ` differentiable on a disc around `lam` covering the
circle; same Banach-algebra context as the gate
(`{A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A]
[CompleteSpace A]`). Headlines: radius independence (via GATE-A1's
`circleIntegral_resolvent_eq_of_isolated`); `f ≡ 1` gives
`rieszProj`; `f = id` gives `a * rieszProj`; additivity / scalar
rules; corner absorption `P * FC = FC = FC * P`; commutation with
`a`; **multiplicativity** `FC (f·g) = FC f * FC g` (the
double-integral headline, GATE-A2 engine).
**Integrability fence:** only the corrected
`circleIntegrable_resolvent_of_nonneg` (`RieszGate.lean:135`) or an
`f`-weighted analogue carrying `0 ≤ r` / `0 < r` on its face.
**Pre-registered PARTIAL seam S-8B-3:** if the `f`-weighted double
integral blows past L, 8B-3 lands PARTIAL — definition, radius
independence, values at `1` and `id`, additivity, corner absorption
stand; "multiplicativity of the local calculus" is the named
remainder, and 8B-4(ii) stays gated on it (or its dependency is
re-registered, never assumed).
**Price (scoping): M–L, 30–55 strict.**

### 8B-4 — Algebra-level spectral splitting (inclusions only)

**Statement pin.** (i) Cheap half (needs only 8B-1):
`spectrum ℂ (a * P) ⊆ {0} ∪ spectrum ℂ a` and the same for
`a * (1−P)`. (ii) Sharp half (needs 8B-3): `spectrum ℂ (a * P) ⊆
{0, lam}`; `lam ∉ spectrum ℂ (a * (1−P))`; corollary
`spectrum ℂ ((a − lam • 1) * P) ⊆ {0}`.
**Pre-registered PARTIAL seam S-8B-4:** full splitting EQUALITIES
and any CLM-restriction spectrum statement are the named remainder
— **unpriceable clean** (they need a corner/restriction spectrum
API neither the pin nor the corpus packages). 8B-4 registers the
inclusions + `lam`-exclusion ONLY; a landing that claims an
equality has overrun its registration.
**Price (scoping): M, 20–35 strict ((i) S–M 8–15; (ii) M 12–20,
on top of 8B-3).**

### 8B-5 — Disc-calculus decomposition at λ

**Statement pin.** For `f` presented by 8a coefficients
(`DiscSummable R c`, `‖a‖ < R`, `lam ∈ spectrum ℂ a` isolated):
multiply the landed factorisation `hfcDisc_sub_scalarEval`
(`HolomorphicFunctionalCalculus.lean:553`) by `P`:
`hfcDisc a c * P = scalarEval c lam • P + (a − lam • 1) *
(hfcDisc a (discTail c lam) * P)`, plus
`hfcDisc a c = hfcDisc a c * P + hfcDisc a c * (1 − P)` (8B-1
split). The `(1−P)` term is carried **unevaluated** — no calculus
on the complement exists. The optional identification of
`hfcDisc a c * P` with 8B-3's `rieszLocalFC` (REM-CIRCLE-ID,
M 25–45) is **NOT** part of this registration.
**Seam: none expected** (one landed identity + 8B-1 algebra;
hypothesis bookkeeping is clerical).
**Price (scoping): S–M, 12–25 strict.**

## Kills, armed for all three (from the scoping, verbatim in substance)

- **K-8B-KILLED-FORM** — any statement consuming GATE-A1's killed
  headline-4 form `circleIntegrable_resolvent` (no `0 ≤ r`) is
  KILLED in advance (K-A1-4 counterexample stands).
- **K-8B-SCALAR-ONLY** — "`f(a) = f(λ)·P` on the isolated part"
  is KILLED (Jordan-block counterexample in the scoping); the
  `(a − λ·1)` term is load-bearing.
- **K-8B-COMPL-NONZERO** — no `1 − P ≠ 0` headline (spectrum
  `{lam}` gives `P = 1`).
- **K-8B-CLM-REPROOF** — no re-proving the gate at CLM generality;
  the CLM seat is instantiation only.
- **K-8B-EXHAUSTION** — "finitely many isolated points'
  projections sum to `1`" KILLED as stated; only the conditional
  finite-spectrum form may ever be registered, separately.

## Dependency order

8B-3 → 8B-4(ii); 8B-1 (landed) → 8B-4(i), 8B-5. 8B-5 is
independent of 8B-3. Programme total as scoped: 87–163 strict
for 8B-1…8B-5; 8B-1/8B-2 already landed, so the registered
remainder here is ≈ 62–115 strict.

## Fences

Not the general contour calculus; not SHELF-7b in full and not
the 7b-disc re-scope (a separate untaken decision); not a
spectral theorem. NO CLAIM; dials 0/4; parts of any official
statement closed: 0.

*Registration only at this step — builds fire under the same
order, in dependency order, each landing with its own dossier
and ceremony.*
