# Bridge Span 2 — the involutive twist pylon (dossier)

**Date:** 2026-10-07 · **Lead tier: T4** (numerical exploration) + **T1** (Lean extension, machine-checked)
**Instrument:** `scripts/involutive_twist_lab.py` (seeds 2026, 202607)
**Results:** `scripts/bridge-span-2-results.md`
**Predecessor:** `whitepaper/bridge-span-1-twist-2026-10-07.md` (twist-from-flow: KILLED)
**Lean:** `lean/ThetLogos/TwistedTriple.lean` §7 (extends Span 1's §1–§6, builds green, zero sorrys)
**Status:** dossier drafted 2026-10-07.

## What this span is

Bridge Span 1 killed twist-from-flow as a Connes–Moscovici twist (regularity,
preservation, J-compatibility, twisted order-one all failed for the generic
seed-2026 `K`) — but proved the structural lesson as a theorem:
**CM regularity wants involutive twists (`ρ² = id`), not one-parameter inner
groups** (`twistConj_CM_iff_centralSq`, T1). This span tests the natural
involutive candidate from the literature: the **Devastato–Lizzi–Martinetti
minimal twist by grading** — the flip automorphism on the doubled algebra
`A ⊗ ℂ²` (Devastato–Lizzi–Martinetti; Filaci–Martinetti, SIGMA 16 (2020) 109,
§2.3; survey arXiv:2301.08346 §4.2).

**Verdict up front (T4 + T1): the pylon STANDS.** The grading flip is the
first viable twist over the finite triple: CM regularity holds exactly,
algebra preservation holds by construction, the DLM J-intertwining is
verified, twisted commutators are tame (ratio ≤ 1), and the twisted
order-one condition holds over all 331,776 doubled pairs (max 0.000e+00 —
where Span 1 broke at 53.31). The one open piece is the twisted-fluctuation
reality prescription (same flag as Span 1, not a refutation).

---

## (a) Exact setup and conventions **(T4 — numerical; definitions are exact)**

### The grading (verified facts, reproduced in the lab §A.0)

- `Γ = gamma_F() = diag(+I₈, −I₈, −I₈, +I₈)` from
  `python/thet_logos/common.py` — 32×32, `Γ² = 1`, `Γᴴ = Γ`, `tr Γ = 0`
  (16+/16−), all exact.
- `[Γ, π(g)] = 0` **exactly** (max 0.000e+00 over all 24 generators) — Γ is a
  genuine grading of the represented triple.
- `{Γ, D_F} = 0` **exactly** — D_F is odd, as a Dirac operator must be.
- **Consequence (proved T1 as `twistByGrading_trivial`):** the naive
  "twist by conjugation" `ρ(a) = ΓaΓ` is **trivial** on even elements
  (`ΓaΓ = a` when `[Γ,a] = 0`). This is *why* DLM double the algebra instead
  of conjugating by Γ. The parent task's `ρ(a) = ΓaΓ` form is recorded here
  as the killed-triviality, not as the candidate.

### The DLM flip (precise formula, cited)

Grand algebra: pairs `(a, a′)` (modeling `A ⊗ ℂ²`).
Doubled representation: `π₂(a,a′) = P₊π(a) + P₋π(a′)`,
`P± = (1±Γ)/2` (rank 16 each).
**Twist: `ρ(a,a′) = (a′,a)` — the flip** (Filaci–Martinetti (9);
survey (66)). Involutive by construction: `ρ² = id`, `ρ⁻¹ = ρ`.
Twisted commutator:
`[D,(a,a′)]_ρ = D·π₂(a,a′) − π₂(a′,a)·D`.
Note: at `(a,a)` this reduces **exactly** to the ordinary commutator
(`grandRep Γ (a,a) = (P₊+P₋)a = a`; proved T1 as `twistedCommGrand_diag`,
unconditionally — needs only `P₊+P₋ = 1`).
Opposite/flip: `(a,a′)° = (a°,a′°)` componentwise via `piOp`;
`ρ°((a,a′)°) = (a′°,a°)` (since `ρ⁻¹ = ρ`).
Twisted outer commutator:
`[X,(b,b′)°]_{ρ°} = X·(b,b′)° − ρ°((b,b′)°)·X`.

### Convention table (carried from Span 1, binding)

`piOp` uses **transpose** (`U_J·Mᵀ·U_J`); the J-action `JXJ⁻¹` uses
**conjugate** (`U_J·conj(X)·U_Jᵀ`); they agree on Hermitian `X`, differ
otherwise. The order-one test (§B) used `piOp` (transpose-based) throughout;
any future work quoting these numbers must state this. Γ itself is real
(diag ±1), so conjugate/transpose agree on it.

### What the lab does not test

The ε/KO sign table; the full twisted spectral action; any continuum limit;
any Lorentzian-physics claim. The Krein probe (§D) is exploratory T4, not a
Krein construction. No "thermal phase transition" language anywhere (house
ban stands).

---

## (b) Preserve / break verdicts

### T1 — Lean (§7 of `TwistedTriple.lean`, machine-checked 2026-10-07)

`lake build ThetLogos.TwistedTriple` → **completed successfully (3244 jobs)**,
zero sorrys in proved parts,
`#print axioms = [propext, Classical.choice, Quot.sound]` throughout.

| # | Theorem | Statement | Status |
|---|---|---|---|
| T1-8 | `gradProj_add`, `gradProj_mul_orth`, `gradProjPlus_sq`, `gradProjMinus_sq`, `gradProjPlus_hermitian`, `gradProjMinus_hermitian` | `P₊+P₋ = 1`, `P₊P₋ = 0`, `P±² = P±`, `P±ᴴ = P±` | PROVED |
| T1-9 | `flipTwist_involutive` | `flipTwist (flipTwist x) = x` — the flip is its own inverse | PROVED |
| T1-10 | `flipTwist_mul`, `flipTwist_add`, `flipTwist_one` | flip is a `TwistAuto`-analog on the pair type | PROVED |
| T1-11 | **`flipTwist_CM_regular`** | `ρ(xᴴ) = (ρ⁻¹(x))ᴴ` **unconditionally** for the flip (since `ρ⁻¹ = ρ` and the flip commutes with `ᴴ` componentwise) — **the theorem Span 1 was missing** | PROVED |
| T1-12 | `twistByGrading_trivial` | `ΓaΓ = a` when `[Γ,a] = 0` — conjugation-by-grading is trivial; DLM must double the algebra | PROVED |
| T1-13 | `twistedCommGrand_diag` | `twistedCommGrand D Γ (a,a) = D·a − a·D` unconditionally | PROVED |
| T1-14 | `twistedCommGrand_leibniz` (+`_add`) | twisted Leibniz over the pair algebra, **conditional on evenness** (`Γ` commuting with all four components) — the physical case: numerics give `[Γ,π(g)] = 0` exactly | PROVED (conditional) |

**T5 pinned:** `TwistedFirstOrderCondGrand` (a `Prop`, not claimed). Exact
obstruction: the opposite involution for the doubled grand algebra is not
constructed in the file — no discharged instance of
`opp (flipTwist y) = flipTwist (opp y)`, and the untwisted first-order
condition for `grandRep` is not proved here (the ordinary one lives in
`OrderOne.lean`).

### T4 — numerical (`involutive_twist_lab.py`, seeds 2026/202607)

Pair set: 24×24 = 576 doubled elements; order-one grid 576×576 = 331,776.

| # | Test | Result | Verdict |
|---|---|---|---|
| A.0 | Γ sanity: `[Γ,π(g)]`, `{Γ,D_F}`, `Γ²=1`, `Γᴴ=Γ`, `tr Γ=0`, `(a,a)`-reduction | all 0.000e+00 exactly | verified |
| A.1 | CM regularity `‖ρ((a,a′)†) − (ρ⁻¹(a,a′))†‖_F`, 576 pairs | **0.000e+00** (Span 1: 0.866–2.02 REFUTED) | **HOLDS EXACTLY** |
| A.2 | preservation: `‖π₂(ρ(a,a′)) − π₂(a′,a)‖_F` | **0.000e+00**; preimage always in the pair set | **HOLDS BY CONSTRUCTION** |
| A.3 | J-compatibility | (i) `‖π₂(ρ) − Γπ₂Γ‖`: max 2.0 — flip ≠ conjugation, as expected; (ii) **`‖JP₊J⁻¹ − P₋‖ = 0.000e+00`** — **J swaps the grading sectors**; (iii) J-action preserves ±-block structure (0.000e+00) | **DLM intertwining verified**: the flip meets J by exchanging the copies |
| A.4 | `‖[D_F,(a,a′)]_ρ‖_F` vs untwisted | mean ratio **0.780**, max **1.000** (Span 1: 12–59× blow-up) | **TAME** |
| B | twisted order-one `[[D,(a,a′)]_ρ,(b,b′)°]_{ρ°}`, 331,776 pairs | max **0.000e+00**, mean 0.000e+00, **0 pairs > 1e−9** (Span 1: 53.31, 36 pairs broken) | **HOLDS** |
| C | twisted fluctuation `D_{A_ρ}` self-adjointness | residual **9.97e3** (random) / **2.087** (structured); twisted order-one on fluctuated D: **0.000e+00** | self-adjointness **not automatic** — same flag as Span 1; needs twist-corrected reality prescription |
| D | Krein probe: `‖ΓD_{A_ρ}Γ − D_{A_ρ}ᴴ‖` (Γ-product self-adjointness) | baseline **1.586e3 = 2‖D‖** (expected: `{Γ,D} = 0` ⟹ `ΓDΓ = −D`); fluctuated structured: 1.586e3 (unchanged) | exploratory: the naive Γ-product is **not** the Krein structure — D_F is Γ-skew, not Γ-self-adjoint. The DLM ρ-product construction remains unbuilt |

### Reading the verdicts

- **A.1:** involution kills the Span-1 obstruction at the root. CM regularity
  is not approximate here — it is exact, by construction, and now a T1
  theorem (`flipTwist_CM_regular`).
- **A.2:** unlike the flow twist, the flip *permutes* the doubled basis, so
  it cannot leave the represented algebra. Preservation is structural, not
  numerical luck.
- **A.3:** the J-sector swap (`JP₊J⁻¹ = P₋` exactly) is the DLM picture
  working as advertised: the real structure exchanges the two copies the
  flip exchanges. This is the first piece of the Lorentzian program that
  *fits* rather than breaks.
- **A.4:** tame commutators (ratio ≤ 1) mean the twisted calculus is not
  fighting the triple — the flip is a symmetry of the setup, not a
  deformation of it.
- **B:** the load test. 331,776 pairs, zero violations. The literature's
  claim (survey Prop 3.8: twist-by-grading preserves a first-order condition)
  is reproduced numerically on our triple.
- **C:** the honest remainder. Twisted 1-forms are not automatically
  self-adjoint; the fluctuation needs the twist-corrected reality
  prescription DLM develop in the follow-up papers. Flagged, not laundered —
  and note the twisted order-one *survives* fluctuation (0.000e+00).
- **D:** the naive Γ-product is not the Krein indefinite structure (D_F is
  Γ-skew). Crossing to the Lorentzian side needs the actual DLM ρ-product
  construction — named, unbuilt, in §(d).

---

## (c) Comparison table — flow twist (Span 1, KILLED) vs grading flip (Span 2)

| Axis | Span 1: `ρ_s` = flow (generic K) | Span 2: `ρ` = grading flip | Winner |
|---|---|---|---|
| CM regularity | 0.866–2.02, REFUTED (T4); characterized T1 (`U²` central) | 0.000e+00 exact (T4); proved unconditional T1 (`flipTwist_CM_regular`) | **flip** |
| Algebra preservation | 0.43–1.41, REFUTED — flow leaves `π(A_F)` | 0.000e+00 — holds by construction (permutes doubled basis) | **flip** |
| J-compatibility | `‖[K,U_J]‖` = 15.85, fails | J swaps sectors exactly (`JP₊J⁻¹ = P₋`); DLM intertwining verified | **flip** |
| Twisted-commutator norms | 12–59× blow-up vs untwisted | mean ratio 0.780, max 1.000 — tame | **flip** |
| Twisted order-one | max 53.31, 36/576 broken | max 0.000e+00, 0/331,776 broken | **flip** |
| Fluctuation self-adjointness | residual 2.92e4 / 36.1 — not automatic | residual 9.97e3 / 2.087 — not automatic | **tie (both flagged)** |
| Involutivity | no (`ρ_s⁻¹ = ρ_{−s} ≠ ρ_s`) | yes (`ρ² = id` by construction; T1) | **flip** |
| Lean status | 38 entries, green, 7 T1 groups | §7 added, green (3244 jobs), new T1-8–T1-14 | **flip** |

**Bottom line:** the flip wins every axis except the fluctuation reality
prescription, which is open for both. Span 1's kill was load-bearing: it
told us exactly what kind of twist to build, and the involutive candidate
passes every test the flow twist failed.

---

## (d) What this buys toward Lorentzian — and what remains canyon

### What the viable pylon buys

1. **A genuine CM twisted triple over the finite triple.** Regularity (T1),
   preservation, tame twisted calculus, and a first-order condition that
   survives (T4 over 331,776 pairs). The twisted-triple program now has a
   living instance here — not a killed one.
2. **The J-sector swap.** `JP₊J⁻¹ = P₋` exactly is the DLM mechanism's
   fingerprint: the real structure exchanging the doubled copies. In the
   DLM papers this is the hinge the Lorentzian signature turns on.
3. **A clean fluctuation laboratory.** Twisted 1-forms and the fluctuated
   Dirac with order-one intact — the arena in which the DLM
   Euclidean→Lorentzian fermionic-action argument would run, once the
   reality prescription is supplied.

### Remaining canyon (named, with admission prices)

| Gap | Status after Span 2 | Admission price |
|---|---|---|
| **Twist-corrected reality prescription** | flagged (C) — same as Span 1 | the DLM follow-up construction for self-adjoint twisted 1-forms, implemented and tested |
| **Krein / ρ-product structure** | naive Γ-product refuted as the Krein structure (D) | the actual DLM ρ-product: indefinite inner product + fundamental symmetry on the finite triple, with a tested signature-change claim in the fluctuated fermionic action |
| **Causality** | untouched | a cone/order on states respected by the flip — unbuilt |
| **Continuum** | untouched | a limit procedure — unbuilt; the thermal-phase-transition ban stands |
| **BW analog** | still quarantined (Span 1 §(c)) | a localization structure — does not exist |

### The Span-2 verdict: STAND, with the map updated

**STANDS:** the DLM grading flip as a Connes–Moscovici twisted triple over
the finite triple — regularity (T1+T4), preservation (T4), J-intertwining
(T4), tame commutators (T4), twisted order-one over 331,776 pairs (T4).
**OPEN (not killed):** the fluctuation reality prescription and the Krein
ρ-product — both named with admission prices, both the subject of DLM
follow-up literature, neither refuted here.
**KILLED (stays killed):** twist-from-flow (Span 1); the naive
`ρ(a) = ΓaΓ` conjugation twist (trivial by `twistByGrading_trivial` —
returns only as the flip, by proof, per the relabeling rule).

**Next live options:** (1) the twist-corrected reality prescription from
the DLM follow-ups, implemented on our triple; (2) the DLM ρ-product/Krein
construction — the actual Lorentzian hinge; (3) the engineered-K and
flow-orbit-algebra options from Span 1 §(d), unchanged.

---

## (e) T1 / T4 / T5 ledger for Span 2

### T1 — machine-checked (extends Span 1's T1-1–T1-7)

`lean/ThetLogos/TwistedTriple.lean` §7 — build green (3244 jobs), zero
sorrys, `#print axioms = [propext, Classical.choice, Quot.sound]`.

T1-8 (projector algebra), T1-9 (flip involutive), T1-10 (flip
`TwistAuto`-data), **T1-11 (`flipTwist_CM_regular` — unconditional CM
regularity for the flip)**, T1-12 (`twistByGrading_trivial`), T1-13
(`twistedCommGrand_diag`, unconditional), T1-14 (twisted Leibniz,
conditional on evenness = the physical case).

### T4 — numerical (this dossier's lead tier for the verdicts)

T4-10 (Γ sanity exact), T4-11 (regularity 0.000e+00), T4-12 (preservation
by construction), T4-13 (J sector-swap exact), T4-14 (commutator ratios ≤ 1),
T4-15 (twisted order-one 0/331,776), T4-16 (fluctuation residuals flagged),
T4-17 (Krein probe: naive Γ-product refuted as Krein structure).

### T5 — pinned / vision

- `TwistedFirstOrderCondGrand`: pinned with exact obstruction (opposite
  involution for the doubled algebra unconstructed).
- Lorentzian signature via the flip (DLM lineage): open — needs the
  ρ-product/Krein construction (admission priced in §(d)).
- BW analog: still quarantined (Span 1 §(c), unchanged).
- No Lorentzian-physics claims; no thermal-phase-transition language;
  killed claims (flow twist, conjugation twist) stay killed.

### T2 / T3

T2: `gradProjPlus/Minus`, `grandRep`, `flipTwist`, `twistedCommGrand`,
`TwistedFirstOrderCondGrand` (definitions). T3: none.

---

## Span verdict

Span 1 broke the pylon and told us what kind of twist to build. Span 2
built it: the DLM grading flip is the first viable twist over the finite
triple — regular, preserving, J-compatible, tame, order-one-holding, with
the Lean theorems to match. The expedition's discipline held throughout:
the flow twist stays killed, the trivial conjugation twist is proved
trivial (not merely abandoned), and the two genuinely open pieces — the
reality prescription and the Krein ρ-product — are named with their
admission prices instead of being paved over. The bridge now has one
standing pylon. The far shore is still canyon, and the map says exactly
which span goes up next.
