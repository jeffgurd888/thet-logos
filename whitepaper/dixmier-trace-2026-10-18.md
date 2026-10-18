# Dixmier Trace — Round 2 Intake (2026-10-18)

**Module:** `lean/ThetLogos/DixmierTrace.lean` (new; no existing file modified).
**Price:** S–M (parked-fleet gauntlet, `gauntlet-parked-fleet-2026-10-17.md` §8):
"Dixmier trace / noncommutative integration — stands as an intake, **S–M**. …
At finite level the Dixmier trace on the finite triple is a finite, computable
shadow (the noncommutative integral as a residue/trace functional on the finite
algebra) — a FIT-at-finite-level verdict is there to be tested with real
theorems; the continuum Dixmier trace (singular traces on compacts,
measurability) is the predictable NO-FIT/window half, needing the analytic
house Round 1 already fenced."

**Verdict: STANDS at the priced scope.** The finite-level FIT is real and is
now theorems — but its content is sharper than the gauntlet predicted (see
correction C1): the Dixmier trace of every finite spectrum is **identically
zero**, proved under every generalized limit, so the FIT verdict is "the
machinery pins cleanly and evaluates, and the evaluation is 0"; a nonzero
finite Dixmier trace is impossible in principle, not merely unbuilt. The
continuum half is NO-FIT/window exactly as predicted, now grep-backed rather
than expected. **No Dixmier trace on any operator is constructed. No
spectral-dimension claim is made for any object. Clay parts closed: 0.**

## Numbers

- **24 strict T1** (line-initial `^(theorem|lemma) ` on comment-stripped
  source), **0 `@[simp]`**, **0 sorry/admit** in code. Plus 6
  definitions/structures (the pin: `partialSum`, `logMean`, `GenLimit`,
  `dixmierTrace`, `padProfile`, `harmProfile`). Module: 419 lines.
- Targeted build green: `lake build ThetLogos.DixmierTrace`, **3,228 jobs**,
  `.olean` present.
- `#print axioms`: 10 headlines, each on exactly
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx` anywhere.
- Program total: 3,153 + 24 = **3,177 strict**.

## §1. The audit (grep-backed, pinned Mathlib v4.35.0-rc3)

| Searched | Where | Result |
|---|---|---|
| `dixmier` (case-insensitive) | all of `Mathlib/` | **0 hits** |
| `banach limit`, `banachLimit`, `singular trace`, `GenLimit`, `generalized limit` | all of `Mathlib/` | **0 hits** |
| `dixmier`, `banach` | `lean/ThetLogos/` | **0 hits** (corpus had none) |
| harmonic numbers / Euler–Mascheroni | `Mathlib/NumberTheory/Harmonic/` | **present**: `Real.tendsto_harmonic_sub_log_add_one` |
| ultrafilter limits | `Mathlib/Topology/` | `Ultrafilter.lim` exists — for **compact Hausdorff** targets only |
| Cesàro means | `Mathlib/Analysis/Asymptotics/` | present (`Filter.Tendsto.cesaro`); not used here |

Consequences. (i) There is no Dixmier trace, no singular-trace theory, no
operator ideal `L^{1,∞}`, and no Banach limit in the pinned Mathlib: the
continuum analytic house is absent, confirming Round 1's fence by direct
inspection rather than by expectation. (ii) `Ultrafilter.lim` does **not**
instantiate the pin below: `ℝ` is not compact, and no dilation-invariant
state on `ℓ∞(ℕ)` is available. The generalized limit therefore stays what
an intake pin should be — data with real conditions (T2), its existence a
Hahn–Banach fact of the literature (T4), unproved and unneeded here.

## §2. The pin (module §1)

- A **profile** is a sequence `μ : ℕ → ℝ` — the eigenvalue/singular-value
  profile of a positive compact operator, with the operator itself left in
  the (absent) continuum house.
- `logMean μ N = (∑_{n<N} μ n) / log (N + 2)` (the `+2` shift against the
  literature's `log (1 + N)` is an indexing convention; it changes no limit
  statement and keeps the denominator positive at every `N`).
- `GenLimit` (structure, T2): `toFun : (ℕ → ℝ) → ℝ`, additive, homogeneous,
  positive, and extending ordinary limits (`eq_of_tendsto'`). **Dilation
  invariance is deliberately not in the pin**: it is the extra axiom the
  continuum theory adds so the induced operator functional is a trace; no
  statement here needs it, and its exclusion is recorded in the module
  header as a scoping decision.
- `dixmierTrace ω μ := ω.toFun (logMean μ)`. Every theorem is universally
  quantified over `ω`.

## §3. What is proved (T1, by module section)

- **§2 — log-mean algebra (4).** `logMean_add`, `logMean_smul`,
  `logMean_nonneg`, `logMean_mono`.
- **§3 — vanishing (4 + 2 auxiliaries).** `tendsto_logMean_of_bdd_partialSum`
  (bounded partial sums ⇒ log-means → 0, by squeezing against
  `C / log (N+2)`), `tendsto_logMean_of_summable` (partial sums bounded by
  `∑' ‖μ‖`), `partialSum_eq_of_eventually_zero`,
  `tendsto_logMean_of_eventually_zero`.
- **§4 — measurability criterion + trace algebra (6).**
  `dixmierTrace_of_tendsto_logMean`: if the log-means converge to `a`, the
  trace is `a` under **every** `ω` — the sequence-level content of
  measurability (ω-independence). Corollaries:
  `dixmierTrace_eq_zero_of_eventually_zero`,
  `dixmierTrace_eq_zero_of_summable`, `dixmierTrace_add`,
  `dixmierTrace_smul`, `dixmierTrace_nonneg`.
- **§5 — finite-spectrum evaluation (3).** `padProfile v` zero-pads a
  finite list; `tendsto_logMean_padProfile`; **`dixmierTrace_padProfile`:
  every finite list `v : Fin n → ℝ` has Dixmier trace `0` under every `ω`.**
- **§6 — harmonic profile (5).** `partialSum_harmProfile_one` (partial sums
  are the harmonic numbers, via `Rat.cast_sum`);
  `tendsto_harmonic_sub_log_add_two` (`H_N − log (N+2) → γ`, from Mathlib's
  Euler–Mascheroni theorem plus `log (N+1) − log (N+2) → 0`);
  `tendsto_logMean_harmProfile_one`; `tendsto_logMean_harmProfile`;
  **`dixmierTrace_harmProfile`: the profile `n ↦ c/(n+1)` has Dixmier
  trace exactly `c` under every `ω`.**

## §4. Fit table

| Clause | Status |
|---|---|
| Dixmier trace, definition (sequence level) | **PINNED** as data (T2, §2 above) |
| Existence of a generalized limit | **OPEN** — literature T4 (Hahn–Banach); absent from pinned Mathlib (grep, §1); not needed by any theorem |
| Log-mean algebra | **STANDS** (T1, module §2) |
| Vanishing: bounded partial sums / summable / finite | **STANDS** (T1, module §3) |
| Measurability = ω-independence when log-means converge | **STANDS** (T1, module §4) |
| Dixmier trace of the finite triple | **T1: IDENTICALLY ZERO** (module §5) — FIT as pinned machinery with proved evaluation; **NO-FIT as a nonzero functional, in principle** |
| Noncommutative integral at finite level | The ordinary trace (partial-sum limit) — already corpus-owned: `SpectralActionFinite`, `Tr(D^{2k})` heat coefficients |
| Harmonic / `\|D\|^{-d}` model profile | **STANDS** (T1, module §6; sequence level only) |
| Dixmier trace on operators (ideal `L^{1,∞}`, singular traces on compacts, trace property via dilation invariance) | **ABSENT** — no such theory in pinned Mathlib or the corpus; the named open price is the analytic house (research-scale; Round 1's fence, now grep-confirmed) |
| Spectral dimension of any object | **NOT DEFINED, NOT CLAIMED** |

## §5. Correction (evidence-led, named)

**C1 — the gauntlet's finite-shadow identification is imprecise.** §8
predicted the finite Dixmier trace would be "a finite, computable shadow
(the noncommutative integral as a residue/trace functional on the finite
algebra)". Tested with theorems, the computable finite shadow of the
Dixmier trace proper is **zero** (module §5): a Dixmier trace is a singular
trace, finite-rank operators are its kernel, and at finite level every
operator is finite-rank. Nor is there a finite-level *residue* to appeal
to: the zeta function of a finite operator is a finite Dirichlet sum,
entire in `s`, with no pole and no residue. The functional that actually
occupies the noncommutative-integral slot at finite level is the ordinary
trace — the partial-sum limit — which the corpus already has and uses.
The FIT-at-finite-level verdict **stands**; what it fits is the machinery
and its (zero) evaluation, plus the ordinary trace as the finite integral.
Nothing downstream depended on the gauntlet's parenthetical, so the
correction is local to this intake's wording.

## §6. Fences

- No operator appears in the module. Profiles are sequences; there is no
  compact-operator theory, no ideal `L^{1,∞}`, no trace-class theory.
- `dixmierTrace_harmProfile` is a statement about the sequence
  `n ↦ c/(n+1)`. In the literature (T4) that is the eigenvalue profile of
  `|D|^{-d}` on a closed `d`-manifold; **no corpus operator is
  `|D|^{-d}` of anything**, and this module performs no computation on any
  corpus operator.
- `GenLimit` existence is not proved (Hahn–Banach, T4). If the type were
  empty, the universally-quantified theorems would be vacuous
  conditionals; the literature's existence theorem is what gives the pin
  its intended models, and it is cited here as literature, not as corpus
  content.
- Dilation invariance, and with it the trace property on operators, is
  outside the pin by recorded decision (§2).

## §7. Surprises

1. **Mathlib's Euler–Mascheroni file did the heavy lifting for §6**:
   `H_n − log (n+1) → γ` ships in the pinned Mathlib, so the harmonic
   evaluation — the intake's only genuinely analytic theorem — reduced to
   a denominator shift and a `div_atTop` squeeze.
2. **No cheap Banach-limit instance exists**: `Ultrafilter.lim` looks like
   a candidate and is not (compact Hausdorff targets only). The pin stays
   data — which the audit table now records as a checked fact, not an
   assumption.
3. **API churn, not content, was the friction**: the pinned Mathlib's
   SummationFilter refactor (`Summable.sum_le_tsum`, `summable_abs_iff`,
   `div_le_div_iff_of_pos_right`, `tendsto_atTop_add_const_right`) renamed
   every classical lemma this module touches. All were found by direct
   `#check` probes against the pinned tree; no statement was weakened to
   fit a name.
