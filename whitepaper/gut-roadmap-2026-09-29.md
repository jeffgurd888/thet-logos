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
4. **The spectral gap Δ — the GUToE Gate.** The three-scale bridge
   (β⁻¹ ∼ Δ⁻¹, G_N ∼ Δ⁻², ω_modular ∼ Δ²) is a *correspondence* until
   Δ itself is an output of the structure rather than a fitted input.

   **GUToE Gate: can the axioms determine Δ without inserting
   empirical Yukawa data?**

   | Outcome | Interpretation |
   |---|---|
   | Δ uniquely fixed | Strong evidence for genuine parameter reduction |
   | Discrete allowed Δ's | Potential quantization/prediction mechanism |
   | Continuous family of Δ's | Δ-bridge remains parametrized |
   | Only experimental Yukawas fix Δ | Δ-bridge is a correspondence, not a first-principles derivation |

   *Provenance note (2026-09-30):* the exact three-scale formulas
   (β = Δ/c_H, G_N = 3π/(16f_2c_G²Δ²), ω_modular = c_TΔ²/ℏ) appear in
   neither the repo nor the GUToE whitepaper — they entered as
   audit/extension material (2026-09-29/30 scale-invariance analysis)
   and must not be attributed to either. The scale-invariant
   combination is G_N·ω_modular (dividing by β² breaks it, scaling
   k⁻² under D_F → kD_F); (G_N·ω·Δ²)/β² = 3πc_Tc_H²/(16f_2c_G²ℏ) is
   also invariant. Invariance does not establish parameter-free
   prediction while the c's are fitted — that is precisely what the
   Gate tests.

Until (1)–(4) exist, the program is a **verified construction**, not a
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
- **Step 0 census (done 2026-09-29, /tmp/h4-step0-census.txt):** fresh
  numerics in the current 144-pair formulation. CONFIRMED: 324 complex
  nullspace dims; 272 coordinate units; 272-real-dim admissible space;
  **46 real dims** (admissible + order one). CORRECTED: admissible +
  order one + `[D,cfMat]=0` gives **22 real dims, not 10** — the target
  is 46→22 under current constraints, not 46→10. The 200 figure is a
  coordinate-unit count, not a dimension. `E_(0,0)` confirmed as the
  counterexample to the unrestricted claim, excluded by admissibility.
- **Exact-pivot certificate route: NO-GO (definitive, 2026-09-29).**
  The weak nullspace has 52 genuinely non-coordinate complex directions
  and zero coordinate-unit directions survive all admissible conditions —
  a singleton-equation certificate cannot cover it. Retired; any future
  exact Lean certificate needs J-symmetrized multi-term basis vectors.
- **Constraint hunt (done 2026-09-29):** all three candidates NO-GO.
  Second-order `[[D²,a],b°]=0` is already implied by (admissible +
  order-one + commutant) — cuts 0 dims (real fact, useless as a cutter).
  Center exhausted: only the imposed `cfMat` direction survives the
  `smDirac` gate (`[D₀,P_C−P_H]=4.24≠0`). Orientability / Poincaré
  duality constrain `(π,J,γ)`, not `D` — wrong type. The standard
  spectral-triple axiom toolkit has no legitimate 22→10 cutter left.
- **Decision (user, 2026-09-29):** retarget to 46→22. The "10" is
  retired as a census artifact; the repaired classification targets the
  22-dim space (10 SM + 12 exotic survivors). Old theorems stand flagged
  unsound-as-stated per the relabeling rule; new theorems will be proved
  as new entries (e.g. `cf_kernel_classification_46_22`).
- **Phase 1 (done 2026-09-29):** the 10+12 split is exact and has
  closed form — the 12 exotic survivors are precisely the
  color-universal flavour-violating couplings the SM ansatz sets to
  zero (ν_L↔e_R, e_L↔ν_R, u_L↔d_R and d_L↔u_R color-universal, plus
  Majorana-type ν_R↔ē_R and e_R↔ē_R). SM and exotic supports are
  disjoint. Basis + characterization saved in h4-spike/ (untracked
  scratch).
- **Phase 2a (done 2026-09-29):** `CFKernelRetarget.lean` created and
  compiling with the 12 explicit exotic definitions + working proof
  pattern. The grading discrepancy is RESOLVED: Phase 1's closed form
  is correct — the agent's check used the wrong gammaF
  (particle/antiparticle split instead of the chiral
  diag(+1×8,−1×8,−1×8,+1×8)); the wrong operator reproduces the exact
  reported failure signature. All 12 satisfy all five W22 conditions.
- **Phase 2b (done 2026-09-30):** all 48 verification lemmas proved
  (self-adjoint, grading-odd, J-compatible, cfMat commutant × 12) with
  the correct chiral gammaF; `lake build ThetLogos.CFKernelRetarget`
  green, zero errors.
- **Phase 2c (reframed 2026-09-30 — positive result, not
  elimination):** Phase 1 verified the 12 exotic matrices satisfy
  order-one, so they are NOT candidates for commutator-witness
  elimination — pivot-killing them would be mathematically
  inappropriate. The correct questions are (a) prove each
  E_k ∈ ker[E ↦ [[E,π(a)],π°(b)]] (the 12 `OrderOneHolds` proofs;
  row-sparsity strategy), and (b) prove the 12 are linearly
  independent (Σc_kE_k = 0 ⟹ all c_k = 0 — a rank test, e.g. a
  nonzero 22×22 determinant for the full 10+12 set). Pivot-
  triangulation "kill the 12 via commutator witnesses": adjudicated
  NO-GO as stated (2026-09-29) — the pivots cannot exist for matrices
  in the nullspace by construction.

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
- **Test B → formal theorem:** `[D_F²,D_F] = 0` proved directly from
  matrix associativity — no hypothesis on D_F needed (structural
  mathematics, not a physical assumption). Then K = βD_F² + H_t gives
  Φ = i[H_t,D_F]: the equilibrium/thermal D_F² piece contributes no
  exchange flux; nonzero flux is entirely the torsion/nonthermal
  term. Clean separation: [D_F²,D_F]=0 is structural, [H_t,D_F]≠0 is
  the dynamical input. (ModularTime.lean; complements the proved
  `eigenvalue_rigidity`, which is the correct formal mechanism for
  exact Δ-preservation under unitary modular flow — the
  |H|_op < Δ/2 bound belongs to additive perturbations D_F+H, a
  different question.)
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
- **Pivot-triangulation "kill the 12 exotics" checklist** —
  adjudicated NO-GO as stated (2026-09-29): the 12 survivors satisfy
  order-one by construction (Phase 1), so nonzero commutator pivots
  cannot exist; linear independence is the correct question, proved
  by entry pivots/rank, not commutator witnesses.

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
