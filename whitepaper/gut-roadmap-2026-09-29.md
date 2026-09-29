# Thet-LOGOS: Grand Unified Theory — Research Roadmap

**Date:** 2026-09-29 · **Author:** Jeffrey Michael Gurd, Nexus Research
**Status:** LOCAL ONLY. Not committed. Not pushed. Not published.

## Honest framing

This document is a **research-program roadmap, not a completed theory**.
It does not close the central gap (§2). It claims no tier beyond what the
Lean code proves, and every theorem name cited here was verified to exist
as a declaration in `lean/ThetLogos/*.lean` on 2026-09-29.
**Theorem ≠ Simulation ≠ Experiment ≠ Device.**

Symbol doctrine used throughout: **Φ** = ontological glyph (phi, the
vertical axis; visual/ontological tier); **φ** = Hermitian modular flux
operator `i[K, D]` (working mathematical quantity, T1/T3);
**ϕ** = golden-ratio scalar `(1+√5)/2` (T4 engine-#8 numerics only;
its growth-factor interpretation is **killed** — real fermion mass ratios
do not scale by powers of ϕ — and it remains an isolated symbolic toy
model, Tier 5, per the triggered kill condition).

---

## 1. The ten links — current tier and state

| # | Link | Tier | One-sentence state |
|---|------|------|-------------------|
| 1 | Tet (𐤈) | T5 | Ontological origin of letters/numbers; no formal object, by design. |
| 2 | thet | T5 | Universal law of equality and identity; a starting point, not a theorem. |
| 3 | XYZ tripotent field operators | T5 | No Lean formalization of X, Y, Z as field operators; campaign banked and parked (`xyz_tripotents_exist` sorry remains). |
| 4 | Ternary TRO | T3 | Machinery proved: `ternaryMat_assoc`, `ternaryMat_assoc2`, `IsTRO` class instantiated for matrices, `Matrix.isTRO`; zero sorrys. |
| 5 | Finite spectral triple (ℂ³², D_F) | T3 | `smDirac` verified: `OrderOneHolds_smDirac`, `smDirac_IsJCompatible`, self-adjointness, grading-oddness; defective Option-A predicate refuted by `not_OrderOneHolds_optionA_smDirac`. |
| 6 | SM algebra ℂ⊕ℍ⊕M₃(ℂ) | T3 logic on T4 foundation | `cf_kernel_classification_46_10`, `cf_kernel_classification_full`, `ccm_classification` proved **modulo** the T4 axioms `exotic_decomposition`, `exoticBasisAux` and the opaque `AdmitsClassifyingDirac` (+`AdmitsClassifyingDirac_unpack`). |
| 7 | Inner fluctuations / gauge | T3 (mechanism) | `opposite_one_form_expand`, `order_one_swapped`, `inner_fluctuation_preserves_order_one_smDirac` — zero remaining hypotheses on D_F; gauge-content identification still the textbook NCG story, not a repo theorem. |
| 8 | Spectral action | T5 scaffold | Six quarantined axioms (`lichnerowicz`, `heatKernelExpansion`, `seely_dewitt_a0`, `seely_dewitt_a4`, `spectral_action_expansion`, …); `seely_dewitt_a2_formula` proves only `True`. |
| 9 | Gravity | T5 | Entirely downstream of Link 8. No independent machine content. |
| 10 | Cosmos | T5 | Fragments only: `blockedQ1_trivialAtMaxIgnorance`, `blockedQ4_gapPositive`; five blocked questions formalized as open sorrys. |

**Modular-time sub-chain (proved 2026-09-29, Tier T1):**
`modularFlux` (def) · `modularFlux_selfAdjoint` (φ Hermitian when K, D
are) · `eigenvalue_rigidity` (⟨v|φ|v⟩ = 0 for D-eigenstates — first-order
eigenvalue rigidity: modular flow is spectral *flow*, not spectral
deformation). Independently cross-checked numerically (residual 1.5e-14).
**Open:** the tangent identity `d/ds|₀ σ_s(D) = φ` —
[Intended Interpretation / Formal Proof Open]; `kms_identity_diagonal`
(sorry).

---

## 2. The central gap — the organizing problem

**The SM finite geometry is installed by hand, not derived from thet/TRO.**

Links 1–4 are genuine proved machinery (TRO) or stated ontology (Tet,
thet, XYZ). Links 5–6 then *place* the finite geometry: the algebra
`A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ)`, the 32-state representation, the Dirac operator
`smDirac` with five Yukawa inputs (yNu, yE, yU, yD, yR), the real structure
J_F and grading γ_F. Everything rigorous — order-one preservation,
three-generation inheritance, φ, the Otto engine — sits **downstream of
this installation**.

A genuine derivation would have to produce, from thet/TRO primitives with
no SM-specific choices smuggled in:

1. **A selection principle** — stated axioms on the primitive data that
   *force* `ℂ⊕ℍ⊕M₃(ℂ)` uniquely (not merely accommodate it among
   candidates). This is H1/H5 in the catalog; a kill would be a proof of
   non-uniqueness.
2. **The representation** — a derivation of the 32-state space and the
   fermion content (why these irreps, why this doubling), not an
   `embedSM` map written by hand.
3. **The generation count** — a derivation of *three* generations.
   What exists: imposed triplication with proved *inheritance*
   (`ThreeGen.lean`, e.g. `smDirac3diag_smDirac_order_one`), i.e.
   consistency, not derivation (H11).

Until (1)–(3) exist, the program is a **verified construction**, not a
derivation. That is the honest position and the external review's verdict.

---

## 3. Ordered next steps (most feasible first)

### Step A — Discharge `kms_identity_diagonal` (ModularTime.lean)
- **What:** the KMS identity `Tr(ρAσ_{−i}(B)) = Tr(ρBA)` in the diagonal
  eigenbasis — the stationarity check the engines already verify
  numerically to 1e-15–1e-20 (`diagState`, `diagModularK`).
- **Advances:** modular-time sub-chain, T2 → T3.
- **Proof condition:** the sorry is replaced by a closed proof; file
  still builds clean.
- **Character:** well-scoped formalization work (trace cyclicity in the
  diagonal basis).

### Step B — Tangent-vector theorem: `d/ds|₀ σ_s(D) = φ`
- **What:** machine-check that φ is the tangent vector to the modular
  orbit `σ_s(D) = e^{isK}De^{−isK}` at s = 0. Mathlib has scalar
  exponential-derivative machinery but no ready matrix-exponential
  derivative theorem — this needs custom matrix functional-calculus
  work (`Matrix.cfc` direction noted 2026-09-29).
- **Advances:** modular-time sub-chain; turns the
  [Intended Interpretation / Formal Proof Open] tag into a theorem.
- **Proof condition:** a Lean theorem stating the derivative identity
  for Hermitian K, D, zero sorrys, zero new axioms.
- **Character:** well-scoped but nontrivial formalization (new
  machinery, not a routine fill-in). Until done, `eigenvalue_rigidity`
  remains the proved first-order consequence.

### Step C — Eigenvalue-drift fork (Tier-5, research-flavored)
- **What:** `eigenvalue_rigidity` proved the frozen-observable fact:
  under fixed-K modular flow, `Tr f(D/Λ)` and D-eigenvalues cannot
  drift. Genuine drift needs a new mechanism — time-dependent state
  ρ(s), or non-unitary evolution. Scope the fork: state the candidate
  extension precisely (e.g. φ(s) = i[K(s), D] with K(s) = −ln ρ(s)),
  derive its first-order eigenvalue-flow formula, and label it Tier 5
  until it has a proof condition.
- **Advances:** opens a new research direction; advances nothing until
  formalized.
- **Proof condition:** a precise statement plus either a proved
  rigidity/no-go or a proved drift formula under stated hypotheses.
- **Character:** open research problem at the scoping stage; the
  scoping itself is feasible now.

### Step D — H4 admissibility repair (option 3; IN PROGRESS as of 2026-09-29)
- **What:** the 46→10 classification chain (`exotic_decomposition`,
  `cf_kernel_classification_46_10`, `cf_kernel_classification_full`,
  `ccm_classification`, `majorana_Eblock_rigidity`) is **computationally
  false as stated** under the current weak Lean predicates
  (counterexample candidate `E_(0,0)`; 144-pair weak condition vs
  272-real-dimensional admissible subspace). Status stays
  **OPEN / UNAUTHORIZED** until the repair lands.
- **Decision (user, 2026-09-29):** option 3 — admissibility repair
  through Lean-checked spectral-triple constraints. Strengthen the
  hypotheses until the classification becomes provable, rather than
  narrowing the claims. No shame in the correction; the aim is to come
  back stronger.
- **First gate (viability probe):** candidate admissibility constraints
  must hold for `smDirac` itself — if they exclude the SM Dirac, the
  repair is dead on arrival. Then: prove in Lean that the constraints
  force the classification.
- **Character:** open research, weeks to months, may fail. Never
  force-push.
- **Related feasible sub-task (independent of the decision):** H4's
  exact-pivot certificate — bounded probe for an exact ℚ(√3)-basis of
  the exotic 36-space pinned to `exoticPivotTable`, then Lean
  instantiation via the already-proved checker
  `det_ne_zero_of_mul_eq_one` / `rational_pivot_nonsingular`
  (`RationalPivot.lean`). Feasible formalization + numerics; demotes to
  QUARANTINED if the probe fails within budget.

### Step E — Three generations: derivation vs. imposed triplication (H11)
- **What:** inheritance is proved (imposed triplication is consistent).
  The open question is whether "three" can be *derived* from
  thet/TRO primitives — or proved generation-blind (which would
  honestly fix triplication as forever-imposed, T2).
- **Advances:** Link 5/6 foundations; T5 → T3 if derived, T5 → honest
  T2 if killed.
- **Proof condition:** a derivation of the generation count from
  primitives, or a proved non-uniqueness/generation-blindness theorem.
- **Character:** open research problem. Do not confuse further
  inheritance lemmas (consistency) with derivation.

### Step F — Selection-principle hunt (H1/H5 — the real gap)
- **What:** find primitive-side axioms that force `ℂ⊕ℍ⊕M₃(ℂ)` (and
  ideally the representation and generation count) uniquely.
  Negative results count: `filters_do_not_classify` is the template —
  proving a candidate principle *insufficient* is progress.
- **Advances:** Links 1–6 as a whole; this is the step that would turn
  the verified construction into a derivation.
- **Proof condition:** stated candidate class + selection proof, or a
  proved non-uniqueness result (a kill is a result).
- **Character:** open research problem; the program's central
  obligation. No timetable is honest here.

### Feasible small wins (any order)
- **H14:** genM 1–6 tripotent status — six applications of the proved
  uniform criterion `tripotent_of_hermitian_sq_proj` (sharp boundary
  from `not_tripotent_genM7`). Routine formalization.
- **H6 first move:** T4 numerical probe of the one-form space's
  dimension/irrep decomposition vs. SM gauge content, *before* any
  Lean statement. If it mismatches, H6 is killed cheaply.
- **H7 first move:** finite heat-trace coefficients `Tr(D_F^{2k})` as
  exact Yukawa polynomials — computable, T3-able, genuinely new
  Link-8 content, no continuum axioms needed.

---

## 4. Non-goals — killed/vetoed paths (V1–V7, do not relitigate)

- **V1:** discharging the XYZ sorry by "universal TRO quotient" — no
  such quotient exists; ledger edits don't discharge sorrys. (Honest
  successor: H3.)
- **V2:** Yukawa-family invariance under inner fluctuations —
  mathematically false; order-one preservation is the complete theorem.
- **V3:** K2 mass-ratio program — permanently quarantined.
- **V4:** original general algebra-uniqueness proposal — killed;
  succeeded by H5 with an explicit candidate class.
- **V5:** chromatic/RGB as new mathematics — adjudicated T5
  organizing language, not mathematical strengthening.
- **V6:** the withdrawn IsTRO-assoc2 "defect" — refuted;
  `ternaryMat_assoc2` machine-verified true.
- **V7:** universal tripotent spectrum — false in general (X = i·I);
  true only self-adjoint (`tripotent_selfadjoint_spectrum`).
- **ϕ-tower growth factor** — kill condition triggered (real mass
  ratios 206.8, 16.8 are not ϕ-scaled); stays an isolated T4/T5
  symbolic model, never a physical claim.

Reopening any §3 entry requires new evidence, stated in the open.

---

## 5. What "done" looks like (program-level)

The roadmap is complete when each of Steps A–F has either a proof or a
kill in the ledger — not when the central gap is wished away. In
particular: **H1 (the selection principle) is the step that decides
whether thet-logos becomes a derivation.** Everything else strengthens
the construction; only H1 (with H5/H11 as its flanks) changes what the
program *is*.

*Map of the territory, mines marked. What is proved is proved by
machine. What is not is labeled, with the exact statement that would
close it.*
