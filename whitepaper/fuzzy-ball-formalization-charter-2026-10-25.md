# Fuzzy Ball Formalization Charter — the gauntlet's computation, promoted to T1

**Date:** 2026-10-25. **Commission:** Jeff Gurd — "formalize" (of the
Fuzzy Ball Gauntlet, run the same day). **Source of the claims:**
`whitepaper/fuzzy-ball-gauntlet-2026-10-25.md` (construction + C1–C5
verdicts) and `~/workspace/fuzzy-ball-gauntlet/results.json` (exact
figures; every rational figure below was re-checked against it in
this charter — the dossier and the JSON agree everywhere).

**Status: CHARTER ONLY.** No Lean code is written by this document
and no build is run under it. One builder executes it later, brick
by brick, in the order of §5. Suggested module:
`lean/ThetLogos/FuzzyBallShadow.lean`, `namespace ThetLogos`,
house header style (construction, status, fences — cf.
`BridgeMagneticHeat.lean`, `LatticeSliceHamiltonian.lean`).

## Fences (on the charter's face, to be carried into the module header)

- This formalizes **the gauntlet's declared finite model only**:
  a five-shell fuzzy-sphere stack with angular spectra and **no
  radial kinetic term**. It is an exhibit → T1 promotion of the
  *computation's* claims C1–C5. **No new physics is asserted.**
- **Zero gravity content.** "Quantum gravity shadow" remains Jeff's
  name for a heat-trace difference; the corpus holds zero gravity
  objects before this brick and zero after it. **Dial #2 unmoved.**
- **NO CLAIM.** Parts of any official (Clay) statement closed: 0.
- Float figures from the gauntlet (Θ values, shadow maxima, grid
  minima) are **not** theorem material and appear nowhere in the
  statements. Only rational data (multisets, cards, moments, gaps)
  and real-analytic inequalities are formalized.
- Axiom fence (house standard): the package's `#print axioms` must
  read exactly `[propext, Classical.choice, Quot.sound]`.
  **`native_decide` is FORBIDDEN** anywhere in the module (it
  imports `Lean.ofReduceBool`). Kernel `decide` is the only
  computation closer; see the performance pre-registration in §5.

---

## 1. The objects

### 1.1 Carrier choice: `Multiset ℚ` — chosen and justified

Spectra are carried as **`Multiset ℚ`**, for three reasons:

1. **Multiplicity is the content.** A spectrum is a multiset
   essentially — eigenvalues with degeneracies (2l+1). A `Finset`
   would dedup and destroy the degeneracies; a `List` would force
   permutation bookkeeping into every identity (C2 is an *equality*
   claim).
2. **Exactness.** Eigenvalues are rational (l(l+1)/r² with rational
   r). Carrying them in ℚ keeps every cross-check (card, moments,
   gap) a *decidable rational* statement — no floats, no ℝ
   noncomputability in the data layer. ℝ enters only in `shadow`,
   through one named coercion.
3. **Corpus precedent.** The corpus already carries heat traces as
   eigenvalue-sum data (`ThermalKernel.heatKernel_trace`, consumed
   as the datum form in `BridgeMagneticHeat.lean`'s
   `magHeatTrace_eq`), and finite sums over explicit index sets as
   its standard packaging (`LatticeSliceHamiltonian.lean`'s Finset
   approximant sums). `Multiset.sum`/`Multiset.map` are the same
   packaging at the level of the spectrum itself.

### 1.2 Definitions (exact signatures; the builder implements these verbatim in shape)

```lean
/-- The angular spectrum of one fuzzy shell of radius `r`, modes
`l = 0..L`: `(2l+1)` copies of `l(l+1)/r^2`. -/
def shellSpectrum (r : ℚ) (L : ℕ) : Multiset ℚ :=
  (Multiset.range (L + 1)).bind fun l =>
    Multiset.replicate (2 * l + 1) ((l * (l + 1) : ℚ) / r ^ 2)

/-- The fuzzy ball: shells `k = 1..K` at radii `r_k = k/K`, joined. -/
def ballSpectrum (K L : ℕ) : Multiset ℚ :=
  (Multiset.range K).bind fun k =>
    shellSpectrum (((k + 1 : ℕ) : ℚ) / (K : ℚ)) L

/-- The heat shadow of a removed multiset `R` at time `t`:
`Σ_{λ ∈ R} exp (-t λ)`. The coercion `ℚ → ℝ` is applied
elementwise, here and nowhere else. -/
def shadow (R : Multiset ℚ) (t : ℝ) : ℝ :=
  (R.map fun λ : ℚ => Real.exp (-t * (λ : ℝ))).sum

/-- Zeroth/first/second spectral moments of a removed multiset. -/
def modeCount (R : Multiset ℚ) : ℕ := R.card
def firstMoment (R : Multiset ℚ) : ℚ := R.sum
def secondMoment (R : Multiset ℚ) : ℚ := (R.map fun λ : ℚ => λ ^ 2).sum

/-- Gap, in statement form (no dependent `min'` in a definition):
`g` is the spectral gap of `s` if `g` occurs in `s` and no positive
element of `s` is smaller. Proved on explicit multisets by
`decide` (membership and the bounded `∀` over a `Multiset` are
decidable over ℚ) or by the shell-decomposition fallback of §5. -/
def IsSpectralGap (s : Multiset ℚ) (g : ℚ) : Prop :=
  g ∈ s ∧ ∀ λ ∈ s, 0 < λ → g ≤ λ
```

The gauntlet seat throughout: `ballSpectrum 5 8` (405 modes).

### 1.3 The breaks (exact multiset operations, mirroring the gauntlet §1)

```lean
/-- Lune removal at cutoff `L`, from a shell at `r = 1`: per `l`,
`l` copies of `l(l+1)` (the `m ≥ 1` half; `l = 0` removes none). -/
def removedLune (L : ℕ) : Multiset ℚ :=
  (Multiset.range (L + 1)).bind fun l =>
    Multiset.replicate l ((l * (l + 1) : ℚ))

def removedA : Multiset ℚ := removedLune 8   -- lune, m > 0
def removedB : Multiset ℚ := removedLune 8   -- mirror lune, m < 0
def removedC : Multiset ℚ := shellSpectrum 1 8        -- decapitation
def removedD : Multiset ℚ := shellSpectrum (3 / 5) 8  -- interior crack, shell k = 3
def removedE : Multiset ℚ :=                          -- same-count control
  Multiset.replicate 4 42 + Multiset.replicate 15 56 + Multiset.replicate 17 72
```

Design note (the C2 point, stated plainly): A and B are **the same
definition** because the spectrum is all the thermal record carries
— the gauntlet's geometric distinction (m > 0 vs m < 0) is *not
representable* in the removed multiset, and that non-representability
is the theorem, not a shortcut. `removedA = removedB` must hold by
`rfl`; if a future variant wants the breaks distinguished, it needs
a richer carrier than the spectrum, which is a new entry.

Broken spectra are multiset differences in the ambient ball:
`ballSpectrum 5 8 - removedX`, legitimate because each `removedX`
is a sub-multiset of the ball (A, B, E ⊆ outer shell; C = outer
shell; D = shell k = 3) — the builder proves `removedX ≤
ballSpectrum 5 8` as a §2 cross-check (by `decide` on counts per
element, or via the bind decomposition).

### 1.4 Rational cross-checks (charter-verified against `results.json`; the builder re-proves each by `decide`)

| Quantity | A | B | C | D | E |
|---|---|---|---|---|---|
| `modeCount` (Δa₀) | 36 | 36 | 81 | 81 | 36 |
| `firstMoment` (Δa₂) | 1500 | 1500 | 3240 | 9000 | 2232 |
| `secondMoment` | 80616 | 80616 | — | — | 142224 |

(second moments computed in this charter from the gauntlet's exact
removed multisets: A: Σ_l l·(l(l+1))² = 80616; E: 4·42² + 15·56² +
17·72² = 142224. C/D second moments are not consumed by any clause
and are not cross-checked.) Ball-level checks: `modeCount
(ballSpectrum 5 8) = 405`; `IsSpectralGap (ballSpectrum 5 8) 2`;
extra decide check `IsSpectralGap (ballSpectrum 5 8 - removedC)
(25/8)` (the gauntlet's one gap-moving break; a cross-check, not a
clause).

Removed-multiset normal forms (from `results.json`, for the
builder's `decide` targets): A = B: {2×1, 6×2, 12×3, 20×4, 30×5,
42×6, 56×7, 72×8}; C: {0×1, 2×3, 6×5, 12×7, 20×9, 30×11, 42×13,
56×15, 72×17}; D: {0×1, (50/9)×3, (50/3)×5, (100/3)×7, (500/9)×9,
(250/3)×11, (350/3)×13, (1400/9)×15, 200×17}; E: {42×4, 56×15,
72×17}.

---

## 2. Theorem statements C1–C5, in formal dress, with proof routes

Headline packaging follows the corpus pattern (cf.
`sliceHamiltonian_package`): one `fuzzyBall_package` theorem
conjoining the five clauses and the §1.4 cross-checks.

### C1 — every shadow is strictly positive. Price: **S**

```lean
theorem shadow_pos {R : Multiset ℚ} (hR : R ≠ 0) (t : ℝ) :
    0 < shadow R t
```

Route: every summand is `Real.exp _ > 0` (`Real.exp_pos`); a
multiset sum of strictly positive terms over a nonempty multiset is
strictly positive (`Multiset.sum_pos` — build-time check the exact
name/signature; fallback `Multiset.induction` with
`Multiset.sum_cons` and positivity of the head term). **Stronger
than the gauntlet:** no hypothesis on `t` and none on the signs in
`R` — positivity of the exponential does all of it. The gauntlet's
C1 is the corollary at `R ∈ {A,…,E}`, `t > 0`, nonemptiness from
the §1.4 cards (36/81 ≠ 0). Corollary worth stating in-module: for
`R ≤ S`, `shadow (S - R) t + shadow R t = shadow S t`
(`Multiset.map` over `S = (S - R) + R` via `Multiset.sub_add_cancel`
and `Multiset.sum_add`) — the formal form of "the shadow is the
heat-trace difference."

### C2 — the mirror casts the same shadow. Price: **S**

```lean
theorem removedA_eq_removedB : removedA = removedB := rfl
theorem shadow_A_eq_shadow_B (t : ℝ) : shadow removedA t = shadow removedB t
```

Route: congruence of `shadow` under the multiset identity — the
identity itself is `rfl` by §1.3's design (counts only; the removed
multisets are equal *by construction*, exactly as the gauntlet
verified symbolically over exact rationals). This is the formal
content of "the thermal matrix records the spectrum, not the
geometry."

### C3 — same count, different shadow. Price: **S** at level (i), **M** at level (ii)

```lean
-- (i) moment level, pure ℚ, by `decide`:
theorem C3_moments :
    modeCount removedA = modeCount removedE ∧
    firstMoment removedA ≠ firstMoment removedE   -- 36 = 36, 1500 ≠ 2232

-- (ii) function level:
theorem C3_shadow_ne : shadow removedA ≠ shadow removedE
```

Route for (ii): small-`t` expansion with an explicit remainder.
Two named analytic lemmas, proved once, used once:

- **L1** `∀ x : ℝ, 0 ≤ x → 1 - x ≤ Real.exp (-x)` — from
  `Real.add_one_le_exp : x + 1 ≤ Real.exp x` at `−x`. (Build-time
  check the name; it exists in current Mathlib as
  `Real.add_one_le_exp`.)
- **L2** `∀ x : ℝ, 0 ≤ x → Real.exp (-x) ≤ 1 - x + x ^ 2 / 2` —
  **the one genuinely analytic lemma of the brick.** Build-time
  check, in order: `Real.exp_bound` (Taylor-with-remainder for
  `Real.exp`, present in Mathlib's special-functions API in a
  sum-over-range form — massage to the quadratic case);
  `Real.exp_one_add_le`-family inequalities; if neither fits,
  prove L2 directly from `Real.exp_eq_tsum` majorization or by the
  calculus route. If L2 cannot be closed inside the brick's
  budget, **C3 descends** per §5 — it is not to be sorried.

Then, summing L1 over A and L2 over E, with the §1.4 moments:

```
shadow A t ≥ 36 − 1500·t                       (L1 termwise)
shadow E t ≤ 36 − 2232·t + (142224/2)·t²       (L2 termwise)
⟹ shadow A t − shadow E t ≥ 732·t − 71112·t²
```

Witness `t₀ = 1/100`: the bound gives `shadow A t₀ − shadow E t₀ ≥
732/100 − 71112/10000 = 0.2088 > 0`, hence the functions differ at
`t₀`, hence `shadow removedA ≠ shadow removedE` by `funext`-free
function inequality (`Function.ne_iff` / apply at `t₀`). All
arithmetic at the witness is `norm_num` over ℝ with the moment
values imported from level (i)'s `decide` results (cast ℚ → ℝ).

### C4 — decapitation's shadow strictly exceeds the crack's, at every `t > 0`. Price: **M**

First the scaling identity (by `rfl`/`decide` on the explicit
multisets):

```lean
theorem removedD_eq_map : removedD = removedC.map (· * (25 / 9 : ℚ))
```

(D's eigenvalues are C's pattern blue-shifted by 1/r₃² = 25/9, with
identical multiplicities — §1.4's normal forms.) Then:

```lean
theorem C4_shadow_lt (t : ℝ) (ht : 0 < t) :
    shadow removedD t < shadow removedC t
```

Route: separate the shared zero mode (both multisets contain `0`
exactly once; its shadow term is `exp 0 = 1` on both sides — this
is the gauntlet's "common floor of 1"). On the positive part,
pair terms through the map: each D-term is `exp (−t·(25/9)λ)` with
`λ > 0`, each C-term `exp (−t·λ)`, and `exp` is strictly
antitone in the exponent (`Real.exp_lt_exp` with `−t·(25/9)λ <
−t·λ` from `t > 0`, `λ > 0`, `25/9 > 1`). Implementation: present
both positive-part shadows as `Finset` sums over `l ∈
Finset.Icc 1 8` of `(2l+1) • exp (−t · l(l+1) [·25/9])` and close
by `Finset.sum_lt_sum` (≤ termwise, < at `l = 1`, index set
nonempty). The bridge `shadow (shellSpectrum r 8) t = Σ_{l ∈ range
9} (2l+1) * Real.exp (−t * (l(l+1)/r²))` is one named lemma
(`Multiset.sum_bind` + `Multiset.sum_replicate` — build-time check
names). **Note the strengthening:** the gauntlet pre-registered
the ordering at large `t` (asymptotic 3e^{−2t}); the formal
version proves it at *all* `t > 0`, because the termwise
domination is exact. The module header states the strengthening
as such — the computation's grid claim (min over the whole grid
at t = 10) is consistent with, and subsumed by, the theorem.

### C5 — the lune break preserves the gap. Price: **S–M**

```lean
theorem C5_gap :
    IsSpectralGap (ballSpectrum 5 8) 2 ∧
    IsSpectralGap (ballSpectrum 5 8 - removedA) 2
```

Route: `decide` over the explicit multisets (membership of `2`:
the l = 1, m ≤ 0 modes of the outer shell survive A — 3 copies
present, 1 removed; the bounded `∀`: every positive element of
the broken spectrum is ≥ 2, the binding cases being the outer
shell's surviving `2`s and shell 4's `25/8`). Performance
pre-registration: the broken spectrum has 369 elements; if kernel
`decide` over the joined 405-element normal form is too slow,
fall back to the **shell-decomposition proof**: gap of a join is
the min of the shell gaps; prove `IsSpectralGap (shellSpectrum r
8) (2/r²)` per shell generically (an S-sized real proof over the
bind/replicate form), A's effect confined to the outer shell
where `IsSpectralGap (shellSpectrum 1 8 - removedLune 8) 2` is a
one-shell `decide` (45 elements), and join. Either route is FULL;
the fallback is a route change, not a descent.

---

## 3. Mathlib API consumed (with build-time checks)

- `Multiset.range`, `Multiset.bind`, `Multiset.replicate`,
  `Multiset.map`, `Multiset.sum`, `Multiset.card` and their
  computation lemmas (`Multiset.sum_bind`, `Multiset.sum_replicate`,
  `Multiset.card_bind` — names to confirm by grep at build time).
- `Multiset.sum_pos` (C1) — confirm signature; fallback: induction.
- `Multiset.sub_add_cancel`, `Multiset.sum_add` (C1 corollary).
- Decidable equality / bounded-`∀` over `Multiset ℚ`
  (`Multiset.decidableEq`, `Multiset.decidableBAll`) — the engine
  under every `decide` in §1.4/§2; ℚ's `DecidableEq` and linear
  order are computable, no classical axioms leak through `decide`.
- `Real.exp_pos`, `Real.exp_lt_exp`, `Real.add_one_le_exp` (L1).
- **L2's source is the one open API question:** `Real.exp_bound`
  (Taylor bound) is the first candidate — confirm its exact form
  in the pinned Mathlib (v4.35.0-rc3) before pricing C3(ii) as M;
  if it is absent or unusable, L2 is proved in-module and C3(ii)
  grows within M, or C3 descends (§5).
- `Finset.sum_lt_sum` (C4), `Finset.sum_bind`-family bridge lemmas.

No `sorry`/`admit` anywhere; an unclosed clause is cut from the
module and named in its header + the landing memo, never sorried.

---

## 4. What is NOT in this brick

- No fuzzy *sphere* single-shell theorems beyond what the ball
  uses (the gauntlet's j = 4 / j = 8 sphere seats are subsumed as
  `shellSpectrum 1 L` data if wanted later — a new entry).
- No Θ (unbroken-trace) values, no grid statements, no float
  comparisons: the formal content is multiset identities, rational
  moments, one function inequality at one witness point (C3), one
  termwise domination (C4), and rational gap statements (C5).
- No continuum ball, no inter-shell coupling, no radial operator,
  no Morley/trisection structure, no gravity — the vision
  fragment's other legs are untouched by this brick.

---

## 5. Price and exits

**Module size: L overall** (one module; the data layer is
computation-heavy, the proof layer is five short routes and one
analytic lemma).

Per-clause prices: §1 objects + §1.4 cross-checks **M** (kernel
`decide` over ≤ 405-element rational multisets is the pacing
item); C1 **S**; C2 **S**; C3(i) **S**; C3(ii) **M** (lemma L2);
C4 **M** (the Finset bridge + `sum_lt_sum` pairing); C5 **S–M**
(`decide`, or S more via the shell-decomposition route).

**FULL:** C1, C2, C3(i)+(ii), C4 (all-`t>0` form), C5, the §1.4
cross-check table, and `fuzzyBall_package`, axioms exactly the
standard three.

**PARTIAL — descent order (pre-registered; descend in this order,
never silently):**

1. **C3(ii) descends first.** If L2 cannot be closed in budget:
   C3 stands at level (i) (moment level — itself a complete
   rational theorem: same count, different first moment), and the
   module header names the function-level inequality as the
   brick's single OPEN clause, with L2 stated exactly. Everything
   else is unaffected.
2. **C4's bridge descends second.** If the multiset↔Finset-sum
   bridge resists, C4 may be stated and proved at the level of
   the two Finset-sum presentations (named `shadowC_finset`,
   `shadowD_finset`) with the identification to `shadow removedC`
   / `shadow removedD` named as the open clause. The domination
   itself is not expected to be the failure point.
3. **C5 does not descend** — its fallback (shell decomposition)
   is a route change at equal content; only if *both* routes
   fail does C5 hold the brick at PARTIAL with the obstruction
   named (expected: `decide` normal-form blowup on the joined
   spectrum — in which case restructure `ballSpectrum`'s
   normal form, do not weaken the statement).

**KILL conditions:**

- Any §1.4 cross-check *disagrees* with `results.json` (a `decide`
  closes with the negation of the table's value): the Lean
  construction does not mirror the gauntlet — STOP, the charter's
  §1 is wrong somewhere; do not patch statements to fit.
- Kernel `decide` infeasible at *shell* level (81 elements) in
  both plain and decomposition presentations: the explicit-
  multiset design dies; re-charter on a pure Finset-sum
  presentation as a new entry. (Ball-level slowness alone is NOT
  a kill — the decomposition route exists precisely for it.)
- Any route found to need `native_decide` or a nonstandard axiom:
  that route is dead by the axiom fence; descend per above or
  stop. The axiom check on the package is part of the landing,
  not an afterthought.

**Landing protocol (parent, standard):** targeted build on the
shipped text, olean existence, strict recount, sorry grep,
`#print axioms` on `fuzzyBall_package`, dossier in `whitepaper/`,
census/README refresh, commit + push. Placement label on the
module's face: **exhibit formalization (the fuzzy-ball gauntlet's
finite model), NOT frontier progress, NO CLAIM, dials 0/4.**
