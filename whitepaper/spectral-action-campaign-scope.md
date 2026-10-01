# Spectral Action / Gravity Campaign — Scope (DRAFT)

**Status:** DRAFT — for Jeff's review. Not approved, not started.
**Date:** 2026-09-30
**Context:** The finite-triple half is machine-checked (`cf_kernel_classification_46_22`,
unconditional, full `lake build` green, 3323 jobs). This scopes the gravity half:
inner fluctuations → spectral action → Einstein–Hilbert + bosonic sector.

**Honesty doctrine for this campaign:** proved / sorry-stage / numerical / Tier-5
vision stay separated. No invented proofs. Old false statements stay flagged;
new results are new entries (relabeling rule).

---

## 1. What exists today (surveyed 2026-09-30, read-only)

### 1.1 `lean/ThetLogos/SpectralAction.lean` — T5 scaffolding (123 lines)

| Item | Kind | Status |
|---|---|---|
| `scalarCurv` | axiom (`String` placeholder for R) | T5, quarantined |
| `lichnerowicz` | axiom (`True`) | T5, quarantined |
| `heatKernelExpansion` | axiom (`True`) | T5, quarantined |
| `seely_dewitt_a0` | axiom (`True`) | T5, quarantined |
| `seely_dewitt_a4` | axiom (`True`) | T5, quarantined |
| `spectral_action_expansion` | axiom (`True`) | T5, quarantined |
| `endomorphismEA` | def returning `String` | placeholder, no content |
| `trace_scalar_mul_one` | theorem, proved | T3 (real finite-dim linear algebra) |
| `seely_dewitt_a2_formula` | theorem proving `True := trivial` | placeholder, **no content** |

### 1.2 `lean/ThetLogos/InnerFluctuations.lean` — T3, machine-checked (762 lines)

Zero axioms. (The single "sorry" grep hit is the word in a docstring, not a proof.)
Key items: `fluctuatedDirac (D_F A) := D_F + A + oppositeOneForm A` (the
D_A = D_F + A + JAJ⁻¹ machine), `IsAlgebraicOneForm`, `opposite_one_form_expand`,
`inner_fluctuation_preserves_order_one`, `inner_fluctuation_preserves_order_one_smDirac`,
`fluctuatedDirac_self_adjoint`, `inner_fluctuation_majorana_subspace`.
**Flag:** `majorana_Eblock_rigidity` is UNSOUND AS STATED (rests on the false-as-stated
`exotic_decomposition`); statement unmodified per relabeling rule. Nothing in this
campaign may depend on it.

### 1.3 `lean/ThetLogos/ProductTriple.lean` — continuum half, axiomatized (12 axioms)

`SpinorHilbert : Type` + operator axioms, `product_sum_of_squares : ∀ D_F, True`
(the D_A² = D_M²⊗1 + 1⊗D_F² identity, axiomatized), `productDirac` (returns `String`),
`product_cross_term_vanishes` (proved), `product_finite_part` (proves `True` — placeholder).

### 1.4 `lean/ThetLogos/ModularTime.lean` — T1 foothold

`modularFlux_selfAdjoint` (T1, zero sorrys), `eigenvalue_rigidity` (T1, zero sorrys:
⟨v|φ|v⟩ = 0 — first-order eigenvalue rigidity, "spectral flow, not spectral deformation").
`kms_identity_diagonal` is a labeled `sorry` (T3 target). These are the formal foothold
for any future thermal-time / emergent-spacetime claim — currently Tier-5 vision,
not results.

### 1.5 Open hypotheses (whitepaper/open-hypotheses-catalog.md)

- **H7 — Spectral action, built not assumed.** Kill/prove conditions set. Names the
  concrete first step: *"Finite heat-trace coefficients Tr(D_F^{2k}) as exact Yukawa
  polynomials — computable, T3-able, genuinely new Link 8 content."*
- **H8 — Gravity from the finite structure.** Einstein–Hilbert-type content derived
  from the finite triple via the spectral action, not asserted downstream.
- **Q2 (BlockedQuestions.lean)** — the controlled continuum limit, open `sorry`.

### 1.6 Mathlib capability check (2026-09-30)

| Needed | In Mathlib? |
|---|---|
| Matrix trace, Kronecker products, `Matrix.trace_kronecker` | YES |
| Finite-dim linear algebra, finrank | YES |
| Riemann zeta values at integers, Gamma function | YES |
| Heat kernel / heat equation | **NO** |
| Pseudodifferential calculus, elliptic regularity, parametrix | **NO** |
| Spin geometry on manifolds, Dirac operator analysis | **NO** |

**Consequence:** the finite part of the spectral action S_F = Tr(f(D_F^(A)/Λ)) is
genuinely formalizable (32×32 matrices). The continuum part (heat-kernel asymptotics,
Lichnerowicz on manifolds, Gilkey's universal formulas as theorems) requires elliptic
PDE theory that does not exist in Mathlib — a multi-year research program on its own.
That half stays quarantined (K2 boundary). This is a fact about the tools, not a
lack of effort.

---

## 2. Phased campaign

### Phase SA-1 — Finite heat-trace coefficients (H7 first step)

**Tier target:** T3 (proved), zero new axioms.
**Theorem targets (new file, e.g. `ThetLogos/SpectralActionFinite.lean`):**
- `finite_heat_trace_even` — framework: Tr(D^{2k}) for finite D, basic trace-power lemmas.
- `tr_DF_sq_yukawa (yNu yE yU yD yR : ℂ)` — Tr((smDirac …)²) as an explicit Yukawa
  polynomial with exact coefficients (the Higgs mass-term coefficient).
- `tr_DF_fourth_yukawa` — Tr((smDirac …)⁴) as a Yukawa polynomial (Higgs quartic term).
- `tr_fluctuated_sq` — Tr((fluctuatedDirac D_F A)²) for `IsAlgebraicOneForm A D_F`,
  symbolic in A.
- `tr_fluctuated_fourth` — Tr((fluctuatedDirac D_F A)⁴), symbolic in A (stretch goal).

**Prerequisites:** `smDirac` entry lemmas (exist), `Matrix.trace` pow lemmas (Mathlib),
the 22-direction basis (exists in CFKernel22.lean).

**Kill criteria (hard gates):**
- **K1 (no placeholders):** every target elaborates with a real statement. A
  `True := trivial`-style proof is an automatic phase fail.
- **K2 (zero new axioms):** `#print axioms` on every new theorem shows only
  `[propext, Classical.choice, Quot.sound]`.
- **K3 (SM cross-check):** Tr((smDirac …)²) must equal the known combination
  Σ|y|² with correct multiplicities (3× for u,d quarks, 1× for ν,e) — checked
  against the Phase-1 numerical census.
- **K4 (fluctuation sanity):** at A = 0, fluctuated traces reduce definitionally
  to the unfluctuated ones.
- **K5 (no continuum leakage):** no definition mentions manifolds, curvature,
  or heat kernels.

**Verdict rubric:** GO iff K1–K5 all pass with complete proofs. NO-GO if any kill
trips — partial lemmas banked as new entries per the relabeling rule, phase stops.

### Phase SA-2 — Algebraic Seeley–DeWitt a₂ (T3 modulo labeled T5)

**Tier target:** T3 proofs conditional on explicitly labeled T5 hypotheses.
**Theorem targets:**
- Real `seely_dewitt_a2_formula` with content:
  a₂ = (4π)⁻²·(64R/3 + 32R + 4·Tr₃₂((D_F^(A))²)), stated as
  `gilkey_a2_universal → <identity>` — the universal formula is an explicit
  hypothesis, never hidden.
- `endomorphismEA` replaced by a real definition (matrix/tensor expression,
  no `String`).
- `trace_kronecker` factorization of Tr₁₂₈(E_A) via `Matrix.trace_kronecker`
  (exists in Mathlib).
- Finite-matrix content of `product_sum_of_squares` (the algebraic expansion
  of the square; the operator-composition half stays axiomatized).

**Prerequisites:** SA-1 complete (Tr₃₂((D_F^(A))²) must be a real computed object).

**Kill criteria:**
- **K1 (no placeholders):** `endomorphismEA` becomes a real definition; the
  `String` version is deleted, not kept alongside.
- **K2 (explicit hypotheses):** Gilkey's universal formula appears as a named
  explicit hypothesis/axiom. Smuggling it into a proof is a phase fail.
- **K3 (constant tracking):** every (4π) prefactor tracked exactly. A dropped
  constant is a phase fail.
- **K4 (no axiom creep):** zero new axioms beyond the six already quarantined.
- **K5 (tier labels):** every theorem carries a machine-visible tier tag
  (T3 vs T5) in its docstring.

**Verdict rubric:** CONDITIONAL GO if the algebraic content is proved modulo
explicitly labeled T5 hypotheses. NO-GO if the universal formula cannot even be
*stated* without the continuum — then it remains an axiom and the phase banks
the negative result as a finding, not a failure.

### Phase SA-3 — Continuum gap assessment (assessment, not proof)

**Tier target:** none — this phase produces a gap ledger, not theorems.
**Targets:**
- A written gap ledger: exactly which lemmas the heat-kernel expansion,
  Lichnerowicz for the product triple, and Gilkey's formulas would require,
  mapped against what Mathlib has.
- Per-axiom decision for each of the six quarantined axioms: prove / keep
  quarantined / kill (if a proved obstruction exists).
- H7/H8 status update in the open-hypotheses catalog.

**Kill criteria:**
- **K1 (honesty):** any axiom that cannot be replaced gets a written gap entry,
  never a `sorry`.
- **K2 (no new sorrys):** assessment only — introducing a `sorry` in this phase
  is a phase fail.
- **K3 (no premature surrender):** if any single heat-kernel lemma proves
  formalizable, it must be proved, not waved at.

**Verdict rubric:** expected NO-GO on full formalization — documented, and the
gap ledger IS the deliverable (a NO-GO here is information, not defeat).
GO only if a genuine formalization path is found.

### Phase SA-4 — Numerical finite spectral action (T4, Engine-style)

**Tier target:** T4 (numerical evidence, honest ledger).
**Targets (Python, mirroring Engine #12 discipline):**
- Module computing S_F(Λ) = Tr(f(D_F^(A)/Λ)) over the 22-direction fluctuation
  space, for a choice of cutoff function f.
- Cross-check: numerics reproduce SA-1 symbolic polynomials.
- Higgs-potential shape: Tr((D_F^(A))⁴) as a function of fluctuation coefficients;
  locate minima numerically.

**Kill criteria (Engine #12 style):**
- **K1 (finiteness):** all traces finite — NaN/inf is a hard kill.
- **K2 (symbolic agreement):** at A = 0, numerics match SA-1 symbolic values to 1e-10.
- **K3 (gauge invariance):** traces constant along gauge orbits, numerically.
- **K4 (cutoff discipline):** varying f changes only the predicted momenta
  combinations, nothing else.
- **K5 (schema validation):** inputs validated à la Engine #12 (shapes, finiteness,
  known fluctuation labels raise, never silently default).

**Verdict rubric:** GO iff K1–K5 pass. NO-GO otherwise; failures banked with logs.

---

## 3. Feasibility read (honest)

1. **SA-1 is genuinely doable.** Finite matrix traces over 32×32 matrices with
   symbolic Yukawa parameters — Mathlib has every tool needed. This is the
   highest-value phase and H7's named first step.
2. **SA-2 is doable as conditional algebra.** The trace identities are real
   mathematics; the analytic universal formula stays an explicit hypothesis.
   Value: replaces `True`-placeholders with honest conditional theorems.
3. **SA-3 will almost certainly conclude NO-GO on the continuum half.**
   Heat-kernel asymptotics need elliptic theory absent from Mathlib. Budget it
   as a bounded assessment (days, not months) — the gap ledger is the product.
4. **SA-4 is routine** given Engine #12's infrastructure patterns.

**Biggest feasibility concern:** effort drift into the continuum half. The
spectral action's prestige lives in the heat-kernel expansion, which cannot be
formalized with current tools — the K2 quarantine boundary is a fact about
Mathlib, not effort. The kill criteria above are designed to force the stop:
SA-3 is time-boxed, introduces no sorrys, and its NO-GO is a pre-accepted outcome.
If SA-1 stalls (K3 cross-check fails — i.e., the traces don't match the SM
Yukawa structure), that is the real alarm: it would mean the finite Dirac's
content is misunderstood, and everything downstream stops.

**Explicit non-claims:** this campaign does not prove gravity emerges, does not
touch the continuum limit (Q2, still open), and does not promote Jeff's
emergent-spacetime vision (modular thermal phase time) past Tier-5 — the
φ-rigidity theorems are a foothold, not a bridge.

---

## 4. Sequencing and gates

SA-1 → SA-2 (needs SA-1's Tr₃₂ objects) → SA-3 (independent, can run in parallel
with SA-2) → SA-4 (needs SA-1's symbolic values for K2). No phase starts until
the previous phase's verdict is recorded. Jeff approves each phase's GO before
the next begins. Nothing is committed or pushed without his explicit go-ahead.

---

## 5. Numbering concordance — G-doc ↔ SA (single source of truth)

**Decision (2026-09-30, Jeff's approval): the SA numbering in this document is the
master.** A second draft campaign document uses G-numbering (G0/G1/G4/G5). To
prevent convention-fork bugs, the mapping is frozen here; the G-doc is read
through this table, not maintained in parallel.

| G-doc item | SA equivalent | Status |
|---|---|---|
| G0 convention freeze | `conventions.json` v1.0 (repo root, frozen 2026-09-30) | DONE |
| G1.1 exact M₂ | SA-1 `tr_DF_sq_yukawa` | PROVED (audited) |
| G1.2 exact M₄ | SA-1 `tr_DF_fourth_yukawa` | IN PROGRESS (finisher dispatched) |
| G1.3 fluctuated M₂ | SA-1 `tr_fluctuated_sq` | PROVED (audited) |
| G2 gauge-orbit audit | **SA-5** (new phase — see below) | SCOPED, not started |
| G2.1 positivity/stability audit | SA-5 (sub-item) | SCOPED, not started |
| G3 finite spectral action | SA-4 (scope expanded — see below) | SCOPED, not started |
| G3.1 potential reconstruction | SA-4 (sub-item) | SCOPED, not started |
| G3.2 numerical engine (Engine-SA) | SA-4 (sub-item) | SCOPED, not started |
| gap-cat G2 real structure & orientability | **SA-6** (new phase — see below) | SCOPED, not started |
| gap-cat G3 Poincaré duality | **SA-7** (new phase — see below) | SCOPED, not started |

**Collision warning (2026-09-30):** the label "G2"/"G3" now has two incompatible
definitions across two source documents — the campaign doc (gauge-orbit audit /
finite spectral action) and the gap catalog (real structure & orientability /
Poincaré duality). The campaign-doc mapping above was frozen first and stands.
Gap-catalog items are filed under distinct SA numbers below and always cited
with the `gap-cat` prefix. This is the exact failure mode the single-master
rule exists to prevent: never cite a bare "G2" again.
| G4 continuum hypotheses | SA-3 continuum gap assessment | SCOPED, not started |
| G5 Einstein–Hilbert matching | downstream of SA-2/SA-4 (future phase) | NOT SCOPED |

Rule: new work is filed under SA numbers. If the G-doc gains new items, they get
an SA row here before any work starts.

### SA-5 — Gauge-orbit and stability audit (from G2/G2.1)

Question: do inner fluctuations preserve the required structure? Tier T3.

Two separate claims, never substituted for each other:
1. **Abstract theorem** — the trace functional is invariant under unitary
   conjugation, formalised independently of the SM representation
   (\(D'_A = U D_A U^\dagger \Rightarrow \operatorname{Tr}f(D'_A/\Lambda) =
   \operatorname{Tr}f(D_A/\Lambda)\) for finite-dimensional unitary \(U\)).
2. **Model theorem** — the *implemented* fluctuation/gauge transformation maps
   the actual fluctuated Dirac operator into the required conjugacy class.

Positivity/stability (G2.1) kept as five separate checks — positivity of the
operator, positivity of the cutoff function, boundedness, convergence of the
finite trace, boundedness below of the numerical potential. Vacuum stability is
never inferred from \(D_A^2 \ge 0\) alone.

Sequencing: starts once SA-1 closes; independent of SA-2, may run in parallel.

### SA-4 scope expansion (absorbs G3/G3.1/G3.2)

SA-4 now covers the full finite spectral action, exact and numerical:
- **Cutoff classes (G3):** \(S_F(A;\Lambda)=\operatorname{Tr}f(D_A/\Lambda)\)
  evaluated for polynomial truncations, Gaussian \(e^{-x^2}\),
  rational/regularised test functions, and compactly supported approximations.
  Purpose is not cutoff independence — it is to separate moment-universal
  conclusions from cutoff-dependent ones from numerical artefacts. Where a
  justified expansion exists, \(S_F \sim f_0 M_0 + f_2\Lambda^{-2}M_2 +
  f_4\Lambda^{-4}M_4 + \cdots\) with exact \(f_k\) conventions recorded;
  builds directly on SA-1's exact moments.
- **Potential reconstruction (G3.1):** scalar/Higgs sector as inverse spectral
  problem — signs, stationary points, gauge equivalence, Hessian eigenvalues
  transverse to gauge orbits, flat directions (symmetry vs accidental
  cancellation). No Higgs mass inferred without an independent scale-setting map.
- **Engine-SA (G3.2):** deterministic numerical engine with explicit I/O
  schemas, convention hash, and mandatory tests (reproducibility, gauge-orbit
  invariance, \(A=0\) regression, basis-change invariance, cutoff-family
  comparison).

Tier T3/T4. Needs SA-1's symbolic moments (K2 gate for the numerical side).

### SA-6 — Real structure & orientability (gap catalog G2)

Verify the finite triple's real structure and orientability: the anti-unitary
involution \(J_F\) with \(J_F^2 = +1\) and \(J_F D_F J_F^{-1} = D_F\), plus the
Hochschild 0-cycle orientability condition \(\pi(c) = \gamma_F\).

Note: the repo already machine-checks adjacent facts — `UJ * UJ = 1` and
J-compatibility (`UJ * D.transpose * UJ = D`) are proved in
`InnerFluctuations.lean`. First step is an audit mapping what is proved vs.
what is open, not a from-scratch build. Tier T3 (finite-dimensional).

### SA-7 — Poincaré duality (gap catalog G3)

Non-degenerate K-theoretic pairing on \(K_0(\mathcal{A}_F) \cong \mathbb{Z}^3\):
the fundamental K-homology/K-theory duality for the finite spectral geometry.

Honest flag: K-theory/K-homology infrastructure in Mathlib is thin. Treat like
SA-3 until scoped — time-box the assessment and pre-accept a possible NO-GO
rather than letting it become an open-ended sink. Tier T3 aspirational.
