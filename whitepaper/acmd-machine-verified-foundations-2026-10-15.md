# Active Cartesian Modular Dynamics: Machine-Verified Foundations

**Jeffrey Michael Gurd — Nexus Research (independent)**
**2026-10-15. Review copy for the author. Not for publication.**

Repository: https://github.com/jeffgurd888/thet-logos

---

## Abstract

This paper states exactly what the machine has verified in the Active
Cartesian Modular Dynamics (ACMD) program through Rung 8, together with the
SM-Match program and the first round of the theories intake. Every theorem
named here is proved in Lean 4 (tier T1), explicitly axiomatized with proved
consequences (T2), stated as a labeled open target (T3/T5), or recorded as
refuted. The program is machine-verified mathematical *scaffolding toward* a
rigorous four-dimensional quantum field theory: a finite spectral triple and
its classification; the Connes–Kreimer Hopf algebra of renormalization; the
almost-commutative product with its twist derived rather than assumed;
analytic and Hilbert-space infrastructure for a concrete model; verdicts on
all six Wightman axioms in a one-mode fermionic model; genuine Schwartz
test-function machinery and a geometric Poincaré action; a finite-dimensional
Stone theorem and a joint functional calculus for commuting symmetric
operators; a Fock-space inner product with proved creation/annihilation
adjoints on the fermionic side; a structural match against the Standard
Model's gauge algebra, fermion content, classical Lagrangian sectors, and
Higgs breaking pattern; and fit verdicts for KMS theory, classical
Yang–Mills, Haag–Kastler algebraic QFT, and the finite spectral action.

**What this is not.** No continuum limit is claimed. No interacting 4D
quantum field theory is claimed. The Yang–Mills existence and mass gap
problem is the program's stated horizon and mission target; it is not
claimed, approached in the Clay sense, or implied by anything below. The
mass gap appears in this paper only as a fixed, quarantined target
statement against which future partial results can be measured.

**Tier key.** T1: proved in Lean 4, zero `sorry`s. T2: axiomatized, with
proved (T1) consequences. T3: theorem stated, proof open, labeled in-file.
T5: opaque, quarantined, or priced window — theorem-shaped, content not
established. KILL: refuted or withdrawn; returns only as a new entry by
proof.

**Verification status.** All verification claims in this paper were
re-checked on 2026-10-15 (§0). Two items did not survive re-checking
unchanged and are flagged where they occur: the finite spectral-action
proofs currently fail to compile under the pinned toolchain (§11,
verdict suspended), and the Morley gauntlet file could not be rebuilt to
completion today (§12, verdicts stand as the 2026-10-11 record).

---

## 0. Verification protocol and corpus inventory

**Counting method (uniform, reproducible).** All counts in this paper are
counts of `theorem` and `lemma` declarations, obtained by the regular
expression `^\s*(private\s+|protected\s+)?(theorem|lemma)\s` applied to
every file in `lean/ThetLogos/`. Counts include
auxiliary lemmas; they are counts of declarations, not of "importance."
**Inventory freeze:** the corpus was inventoried at commit `790c1e0` on
2026-10-15. Work landing after the freeze (a Rung 9 start and a ternary
substrate module, both in progress under separate directives) is outside
this paper's scope and is not assessed here.

**Corpus totals (exact).**

| Scope | Files | Theorem/lemma declarations |
|---|---|---|
| Whole Lean corpus (`lean/ThetLogos/`) | 77 | **2,016** |
| ACMD program files (Rungs 1–8, SM-Match, intake, Morley, targets/dossiers) | 64 | **1,352** |
| Earlier exploratory campaigns in the same repository (CF-kernel arc, exotic sectors, chromatic and related work) | 13 | 664 |

The figure "300+" that circulated in earlier drafts of program summaries
was never derived from a count of this corpus. It is withdrawn and replaced
by the exact counts above.

**Build (2026-10-15, reported exactly).** `cd lean && lake build`
completes successfully (3,324 jobs). Stated plainly: the root module
`ThetLogos.lean` imports only 14 core modules, so the remaining 63 modules
were additionally built one by one (`lake build ThetLogos.<Module>`).
Result: **74 of 77 modules build green.** The three exceptions:

- `SpectralActionFinite.lean` **fails**: four proof errors
  (`simp` made no progress / failed rewrite at lines 942, 1006, 1024,
  1074), all inside the a₂ trace-computation proofs and consistent with
  Mathlib deprecation drift since the file's 2026-10-11 verification.
  No statement was changed and no `sorry` introduced; the proofs no
  longer close under the pinned toolchain. See §11 for the suspended
  verdict this causes.
- `SpectralActionBridge.lean` fails transitively (it imports the file
  above).
- `EdgeSignature.lean` (the Morley gauntlet file, §12): two rebuild
  attempts on 2026-10-15 timed out (10 and 25 minutes, under heavy
  machine contention) without emitting any error — the build did not
  finish, so the file is **not re-verified today**. Its last full
  verification is the gauntlet dossier's green build of 2026-10-11.

A minor wart, recorded for completeness: two declaration names collide
across modules in the shared `ThetLogos` namespace (`vacuum_cyclic` in
`FreeField` and `FermionicFock`; `Dprod` in `ProductTriple` and
`CausalProduct`), so those module pairs cannot be imported into a single
environment. Each module builds and verifies on its own. Wiring the newer
modules into the root import list, and repairing the spectral-action
proofs, are queued mechanical follow-ups.

**Sorry hygiene (exact).** The corpus contains exactly **seven** `sorry`s,
all pre-existing, all labeled in-file, none introduced by Rungs 1–8,
SM-Match, or the intake:

| Location | Count | Tier | Content |
|---|---|---|---|
| `BlockedQuestions.lean` (lines 76, 108, 140, 194, 274) | 5 | T5 | Open conjectures Q1–Q5, filed as questions |
| `ModularTime.lean:206` | 1 | T3 | `kms_identity_diagonal`; numerically verified, proof open |
| `XYZTripotents.lean:492` | 1 | T5 | `xyz_tripotents_exist`; single documented target |

There is no `admit` anywhere in the corpus. Every other occurrence of the
word "sorry" in the sources is documentation prose, mostly statements that
a file contains none.

**Axiom footprint (spot-checked 2026-10-15).** `#print axioms` was run
on thirteen headline results. Eleven depend only on Lean's standard
axioms `[propext, Classical.choice, Quot.sound]` — no `sorryAx`:
`antipodeAxiomEval_proved`, `modularFlux_selfAdjoint`, `w5_span_true`,
`wick_four_point_operator`, `schwartzComplete_discharge`,
`jointFC_spectralMapping`, `higgs_stabilizer_is_Q`, `gibbs_kms_weight`,
`stone_finiteDim`, `ann_adjoint`, `adag_adjoint`. The two labeled
exceptions behave exactly as their labels say: `pauliBounded` depends
additionally on the one T2 axiom `pauli_compactResolvent`, and
`trace_collapse_hypothesis_fails` on the `CausalProduct` file-level T2
product axioms. And `kms_identity_diagonal` depends on `sorryAx` —
precisely its T3 label.

---

## 1. Rung 1 — The finite spectral triple (T1) — STANDS

The finite factor is a concrete matrix spectral triple; its classification
and constraint census are machine-checked.

- **Classification and census.** The generator family `smGen : Fin 12`
  gives 144 pairs; the order-zero condition is checked machine-side over
  147,456 complex components (`order_zero_comm`). Three-generation
  inheritance is proved in `ThreeGen.lean` (20 declarations), including
  `smGen3_order_zero` and the Kronecker-factorization identities. The
  576-pair order-one census is a T4 Python scan, not a Lean proof.
- **Modular dynamics.** `thermal_flux_vanishes`: the modular flux vanishes
  identically on Gibbs states for every inverse temperature β.
  `exists_activeDriver`: a non-equilibrium driver producing nonzero flux
  exists. `modularFlux_selfAdjoint`: the flux φ = i[K, D] is Hermitian.
  Gauge covariance and trace gauge-invariance of the flux are proved.
- **Ultimate reduction.** `UltimateReduction.lean` proves 6 T1 theorems,
  including `dynamicallyFrozen_of_noHeat_noGauge` and
  `equilibriumKillsFlux`. The same file records finite-level kills:
  micro-vortices (no vorticity operator exists in the finite triple) and
  the vortices→matter→gravity chain (needs continuum data).
- **Connes–Kreimer Hopf algebra.** `Renormalization.lean` (60 declarations)
  formalizes the Hopf algebra of rooted trees: coproduct, B₊ grafting,
  counity, coassociativity. The record on the antipode is two-sided and
  both sides are kept: the as-stated antipode axiom was **refuted**
  (`antipodeAxiom_false`), and the corrected evaluation version was
  **proved** (`antipodeAxiomEval_proved`, T5→T1). The refuted statement is
  not laundered into the proved one.

## 2. Rung 2 — The almost-commutative product (T1) — STANDS

`ProductTriple.lean` (63 declarations) builds the product of an axiomatized
manifold factor with the finite triple.

- **Product Dirac identity.** `Dprod_sq`: D_prod² = D_M² ⊗ 1 + 1 ⊗ D_F².
  The formerly axiomatized `product_sum_of_squares` was promoted to a
  proved T1 — upgraded, not resurrected.
- **Twist derived, not assumed.** The product twist is the flip on the
  doubled product algebra (`flipProd_involutive`,
  `flipProd_CM_regular`); the candidate ρ_M ⊗ ρ_F product twist was killed
  (it does not typecheck).
- **Fluctuation decomposition.** `prod_commutator_decomp` splits inner
  fluctuations into manifold and finite parts.
- **KO data.** `koProd_signs`: KO signs ⟨−1, 1, −1⟩ (`koDim_add`:
  (4 + 6) % 8 = 2).
- **Causality re-entry.** `CausalProduct.lean`: the finite-level Span-5
  causality obstruction does not carry to the product
  (`trace_collapse_hypothesis_fails`, `product_not_forced_central` — T1
  consequences of the T2 product axioms, footprint labeled in §0). Genuine
  causal order is pinned at its exact price: global hyperbolicity.
- **The 6-dimensional caveat.** The surviving finite *represented* gauge
  algebra is six real dimensions: Option-A kills the represented M₃(ℂ)
  summand. The full Standard Model gauge group is not claimed from the
  finite factor. This caveat stands and is revisited precisely in §10.

## 3. Rung 3 — Lorentzian-structure pins (T2+T1, one partial) — STANDS

- **Antilinear J — promoted (T2+T1).** The obstruction (bare ℂ-modules; J
  not even statable) was removed by explicit enrichment of `TripleData`
  (sesquilinear form; positivity, nondegeneracy, completeness explicitly
  *not* assumed; antilinear `Janti` with KO axioms). Product theorems
  proved T1: `Jprod_sq` (J² = −1), `Jprod_D` (JD = DJ), `Jprod_Γ`.
- **Krein inner product — promoted (T2+T1).** Fundamental symmetry η with
  η² = 1 and form-self-adjointness proved (`ηprod_sq`, `ηprod_selfadj`).
  No adjoint operator is constructed and no spacetime signature is
  claimed: η is an abstract fundamental symmetry.
- **Twisted first-order condition — PARTIAL.** The opposite representation
  is built in the `conjJ`-shadow of a° = Ja*J⁻¹ (multiplication reverses,
  T1); the diagonal reduction is proved (`prodTwistedFOC_diag_reduce`).
  The exact remaining obstruction is priced: no `Star` instance on
  `Module.End` over the tensor module in this setting, and factor-level
  order-one is absent from the abstract `TripleData`.
- **Continuum scoping — priced roadmap, no limit claimed.** "Finite triple
  converges" language is killed with reason; the continuum is scoped
  per-axiom as future work.
- **Promotion honesty.** The Rung 3 promotions are T2-axiomatization plus
  T1 consequences — not derivation from analysis. This paper repeats that
  qualification wherever the promotions are cited.

## 4. Rung 4 — The analytic house (T1 + one T2 bridge) — STANDS

Directive: "Build the house and use the gaps as windows."

- **Bounded-triple instance for the concrete Pauli model.**
  `pauliBounded : BoundedAnalyticTriple` forms. Its mathematical content
  is proved T1 underneath (`pauliD_sub_det`, `pauliD_resolvent`,
  `pauliD_resolvent_compact` — finite-dimensionality is the whole proof of
  compactness); one model-specific T2 axiom (`pauli_compactResolvent`)
  bridges the deliberately opaque `HasCompactResolvent` predicate. The
  window is eliminable only by redefining that predicate transparently —
  a design decision, priced in the dossier. The model stays analytically
  trivial (scalar representation, vanishing commutators); it discharges
  analytic debt, not gauge content.
- **Hilbert completion and bounded \*-representation (T1).** Completion of
  the model is trivial (`CompleteSpace (EuclideanSpace ℂ (Fin 2))`); the
  bounded \*-representation of the Pauli algebra is proved with the *true*
  adjoint star, transported from matrix conjugate-transpose
  (`repScal_is_star_rep`). The incorrect `star := conjJ` construction was
  explicitly refused earlier in the program and stays refused.
- **Smeared field operators (14 T1).** Creator-half canonical
  (anti)commutation relations for smeared fermionic and bosonic fields,
  smeared Pauli exclusion, and one-point vanishing
  (`FieldOperators.lean`).
- **Wightman targets framed (T5, unproved by design).** All six axioms are
  stated as structured propositions with exact hypotheses, conclusions,
  and per-axiom prices (`WightmanTargets.lean`). Stating them is not
  proving them; Rung 5 takes the verdicts.

## 5. Rung 5 — The Wightman ascent on a one-mode model — STANDS

On a one-mode fermionic Fock model (∧(ℂ) ≅ ℂ², Majorana field
ψ(c) = c • (a† + a)), all six targets received T1 verdicts. These are
verdicts about the toy model and about the framings — not about 4D QFT.

- **W1 (fields exist): PROVED** (`w1_majorana`).
- **W2 (covariance): PROVED for ℤ₂ fermion parity** (`w2_parity`). This is
  explicitly *not* Poincaré covariance; the group is `ZMod 2` acting by
  parity.
- **W3 (spectrum condition): PROVED for the trivial translation
  representation** (`w3_trivial`) — a frame-consistency check (spectrum
  {0} ⊆ forward light cone), not Stone's theorem.
- **W4 (locality): PROVED** at s = +1 (`w4_majorana`); the one-mode model
  has no spacetime, so the spacelike hypothesis is vacuous.
- **W5 (vacuum cyclicity): REFUTED as framed; corrected version PROVED.**
  Monomial-*range* density is false even for a free fermion
  (`w5_framed_false`); the linear-*span* density the literature means is
  true (`w5_span_true`). The Rung 4 framing was strictly stronger than
  the literature; the refutation is a framing correction recorded as a T1
  result.
- **W6 (non-triviality): bosonic form proved but fermion-blind; corrected
  version PROVED.** The bosonic-form criterion gives −2 ≠ 0 for the free
  Majorana field — a documented false positive (`w6_majorana`); the
  corrected Koszul-sign Wick criterion vanishes as it should
  (`w6_fermionic_wick`).

Rung 5 files: `OneModeFermion.lean` (37 declarations) and `Rung5W1–W6`
(39 declarations).

## 6. Rung 6 — Infinite modes — STANDS

- **Schwartz machinery — premise correction, then GO.** The Rung 4/5
  framing "Mathlib has no Schwartz space" was wrong: Mathlib ships the
  full Schwartz machine (Doll 2026). `SchwartzSpace.lean` proves 14 T1
  results on genuine 𝒮(ℝ⁴, ℂ) — closure under derivatives and polynomial
  multiplication, temperate growth, Fourier inversion — and discharges
  the earlier T2 test-function marker. One genuine gap remained at this
  rung: no `CompleteSpace 𝒮(E,F)` instance in Mathlib (discharged at
  Rung 7, §7).
- **Poincaré — geometric half GO.** `PoincareAction.lean` (11
  declarations): the Lorentz group O(1,3) and Poincaré group as
  `Group` instances; the field action `f ↦ f(Λ⁻¹(x−a))` satisfies the
  group-action laws and is ℂ-linear in the test function
  (`poincareAct_mul`, `poincareActLin`). The one-particle unitary
  representation and second quantization stayed priced at this rung.
- **Wick combinatorics — PARTIAL.** `WickSigns.lean` (31 declarations):
  complete pairings of `Fin (2n)`, the Koszul sign, its independence of
  pair ordering, and the four-point signs (+1, −1, +1)
  (`koszulSign_four_point`). The operator Wick identity stayed priced
  (discharged at Rung 7 in a two-mode model).
- **Stone — analytic core T1.** `continuous_char_lift`: a continuous
  norm-one character of (ℝ,+) is `exp(i·a·t)` — the analytic core of
  Stone's theorem. The full finite-dimensional Stone theorem hit Lean
  engineering friction at this rung (discharged at Rung 7).

## 7. Rung 7 — The frontier — STANDS

Four of the five outstanding prices were discharged T1; the fifth was
narrowed. This rung also marks where formalized analysis currently stops.

- **Schwartz completeness — T1.** `schwartzComplete_discharge`
  (`SchwartzComplete.lean`, 415 lines): 𝒮(ℝⁿ, ℂ) is Fréchet-complete —
  the genuine Mathlib gap from Rung 6, closed by a direct proof
  (countable uniformity basis → uniform convergence of all iterated
  derivatives → decay bounds pass to the limit).
- **Operator Wick identity — T1, with a correction.** In a concrete
  two-mode fermionic Fock model, `wick_four_point_operator`:
  ω(ψ₀ψ₁ψ₂ψ₃) = G₀₁G₂₃ − G₀₂G₁₃ + G₀₃G₁₂, with all Wick hypotheses
  *proved* (CAR, Hilbert adjoints, quasi-free move), and the Koszul signs
  discharged against Rung 6. Correction recorded in-file: Rung 6's priced
  hypothesis pair ({ψᵢ,ψⱼ} = 2Gᵢⱼ together with ω(ψᵢψⱼ) = Gᵢⱼ) is jointly
  false in the model; the identity holds with the full non-symmetric G.
  The n-point expansion remains priced (T5).
- **Stone / joint spectral ONB — T1.** `jointSpectral_orthonormalBasis`
  (commuting symmetric family ⇒ orthonormal basis of joint eigenvectors)
  and the full finite-dimensional Stone theorem `stone_finiteDim`
  (strongly continuous unitary one-parameter group ⇒ skew-adjoint
  generator diagonal in that basis, `(U t)(b k) = exp(i·a k·t) • b k`).
- **Joint functional calculus — T1.** For commuting bounded symmetric
  operators, `SpectralFrontier.lean` proves a joint functional calculus
  stronger than Mathlib's single-operator continuous functional calculus,
  with the spectral mapping theorem `jointFC_spectralMapping`.
- **Mass-shell track — PARTIAL.** The invariant measure d³p/2E_p is
  constructed as a density-weighted pushforward; its integral formula and
  rotation invariance are proved, and the restricted (proper
  orthochronous) Lorentz group is formed as a subgroup. Boost invariance
  is priced at exactly one missing lemma: the one-dimensional Jacobian
  identity |φ′| = E′/E for the x¹-boost. The one-particle representation
  law and unitarity-from-invariance are proved at function level;
  strong continuity and the linear-isometry packaging remain priced.
  Second quantization was blocked at this rung by the Fock inner-product
  gap — the subject of Rung 8.

## 8. Rung 8 — The Fock inner product — STANDS (fermionic) / PARTIAL (bosonic)

- **Fermionic — STANDS.** `FermionicFock.lean` (43 theorems, 1,064 lines):
  the Fock space as ℓ² over occupation subsets, with Pauli exclusion
  automatic from the subset guards. Proved T1: creation/annihilation
  adjoints (`ann_adjoint`, `adag_adjoint` — the fermionic discharge of
  the W0 inner-product gap), the canonical anticommutation relations,
  sector orthogonality, the number operator with eigenvalues `S.card`,
  and vacuum cyclicity. **Fermionic second quantization is unblocked.**
  Priced windows, stated in-file: unitary equivalence with exterior-power
  subspaces, the infinite-mode limit, and the general-n Gram determinant
  (base case and reassembly proved; inductive step priced).
- **Bosonic — PARTIAL.** `BosonicFock.lean` (25 theorems): ℓ² over
  finitely supported occupation configurations, with creation/annihilation
  as linear maps on a dense domain (the honest standard formulation for
  unbounded operators). The inner product, orthonormal basis, explicit
  basis actions, and the basis-level adjoint relation (`adjoint_basis` —
  the computational core of W0) are proved. The final linearity assembly
  of the full adjoint relation stalled on Mathlib API friction
  (submodule inner-product coercion handling) and is priced as
  engineering, not mathematics; the induction principle needed for the
  assembly is proved. CCR, number operator, and sector results follow
  from the basis actions by standard computations not yet formalized.

## 9. Rung 9 — Second quantization (out of scope)

Second quantization Γ(U) on the fermionic side — functorial lift of
one-particle unitaries, its representation laws, and the quantum Poincaré
implementation at the one-particle level — is the next rung the ladder
names. Work on it began after this paper's inventory freeze (§0); it is
not assessed here, and nothing in this paper depends on it.

## 10. SM-Match — structural match against the Standard Model (3 MATCH + 1 PARTIAL)

"Match" means: the formalized structures coincide with the Standard
Model's known algebraic structure — same gauge group, same fermion
quantum numbers, same classical Lagrangian shape, same breaking pattern.
Masses, couplings, and mixing angles are **inputs** (labeled T2), never
derived. This is a structural formalization result, not a new Standard
Model and not a derivation of any measured value. 95 theorem/lemma
declarations across four files (the program dossier's earlier estimate of
"~70" understated the count; the verified figure is 95).

- **Track 1 — Full finite gauge algebra: PARTIAL.** On the algebraic side,
  the match is proved T1: the unitary group of ℂ⊕ℍ⊕M₃(ℂ) is
  U(1)×SU(2)×U(3) (`quat_mem_specialUnitary_iff`: U(ℍ) = SU(2)), and its
  unimodular subgroup is exactly U(1)×SU(2)×SU(3)
  (`SMUnimodular_mem_iff`). On the represented side, the Rung 2 caveat is
  located exactly, not redefined: the kernel of the Option-A
  representation is characterized (`pi_ker_iff`); ℂ and ℍ survive
  faithfully; M₃(ℂ) survives only locked to the electroweak sector; pure
  color dies. And the priced gap is proved, not asserted:
  `pi_u1_eL_trivial` — the represented U(1) acts trivially on the left
  electron, so **the represented U(1) is not the Standard Model
  hypercharge U(1)**. A faithful representation of the full SM gauge
  group on the finite Hilbert space is not achieved; the gap is priced at
  the pre-Option-A representation or the manifold factor.
- **Track 2 — Fermion content: MATCH.** The eight fermion types carry the
  Standard Model's (Y, T³, color) assignments as labeled T2 inputs
  (hypercharges are not derived; generation triplication is imposed, per
  `ThreeGen.lean`). Proved T1: electric-charge consistency
  Q = T³ + Y/2 for all eight types (`charge_consistency`), and
  consistency of the index↔fermion mapping with the finite-triple
  embedding. Priced: full SU(3) color is unrepresented in the Option-A
  representation (Track 1's gap).
- **Track 3 — Classical Lagrangian sectors: MATCH.** 19 declarations:
  three-factor gauge kinetic term with joint gauge invariance proved
  (`smGaugeKinetic_gauge_invariant`), the correct −¼ sign, and
  nonnegativity; the fermion term's fluctuation split
  (`fermionTerm_split`); the Higgs potential's minima structure (pure
  algebra); the Yukawa sector *structure* with an input matrix and no
  values. Priced: the quantum Lagrangian, the continuum integral, the
  junk quotient, and all coupling values.
- **Track 4 — Symmetry breaking: MATCH.** 42 declarations. The VEV
  stabilizer is *exactly* span(Q) (`higgs_stabilizer_is_Q`) — the precise
  algebraic statement of SU(2)_L×U(1)_Y → U(1)_em; the VEV minimizes the
  potential; the photon direction is massless *because* Q is unbroken
  (`higgs_photon_direction_massless`); M_W = gv/2 and
  M_Z = √(g²+g′²)v/2 hold as formal relations among the input parameters
  (g, g′, v), with no numerical values anywhere.

## 11. Theories intake, Round 1 — fit verdicts

Standing rule: a theory is admitted only if its core structures map onto
the program's formalized objects with real theorems. Refusals are results.

- **KMS / Tomita–Takesaki: FIT at finite level.** 10 T1 theorems in
  `KMSBridge.lean`, including the finite-dimensional KMS identity for
  Gibbs states (`gibbs_kms_weight`) and the equivalence of KMS
  equilibrium with vanishing thermal flux; two previously pinned T5
  targets in the modular-flux file are discharged. Priced T5 window:
  unbounded Tomita–Takesaki theory and type-III factors — Mathlib has no
  von Neumann algebra theory.
- **Classical Yang–Mills: FIT classically; quantum NO-FIT.** 16 T1
  theorems in `ClassicalYangMills.lean`, including the represented
  curvature from 1-form data with *exact* gauge covariance
  (`repCurvature_gauge_covariant`) and gauge invariance of the
  Tr(F†F) action. The quantum theory — quantization, continuum, mass
  gap — is recorded NO-FIT and remains quarantined T5.
- **AQFT / Haag–Kastler: per-axiom.** In `HaagKastlerFree.lean` (14
  declarations): isotony FIT (T1); locality FIT at creator level and for
  fermionic even observables (T1), with the honest caveat that the
  spacelike hypothesis is vacuous at creator level; Poincaré covariance
  PARTIAL (geometric half T1, implementer priced); vacuum PARTIAL (cyclic
  vector T1, invariance priced); spectrum condition and irreducibility
  NO-FIT as theorems in the current setting (priced windows recorded).
- **Spectral action / finite index bridge: FIT at finite level (2026-10-11
  verification); build-suspended 2026-10-15 — see the correction below.**
  On the formalized `smDirac`: Tr(1) = 32; Tr(D_F²) as the explicit
  Yukawa-sum formula; the fluctuated trace expansion; vanishing of odd
  traces; the finite-dimensional Fredholm index and the chiral-compression
  index (zero). NO-FIT recorded: the continuum heat-kernel expansion and
  the Atiyah–Singer theorem (both need continuum elliptic analysis).
  **Correction (2026-10-15):** re-verification for this paper found that
  `SpectralActionFinite.lean` no longer compiles under the pinned
  toolchain — four proof failures (`simp` made no progress / failed
  rewrite at lines 942, 1006, 1024, 1074), all inside the a₂
  trace-computation proofs and consistent with Mathlib deprecation drift
  (`if_pos`/`if_neg` simp behavior). `SpectralActionBridge.lean` fails
  transitively. The theorem *statements* are unchanged and no `sorry` was
  introduced, but until the proofs are repaired this entry's T1 status is
  **not currently machine-verified** and the FIT verdict is suspended,
  not standing. Repair is a queued, well-localized job.

**Round 2 queue (not yet run):** BRST/anomalies; the
Osterwalder–Schrader reconstruction bridge; noncommutative integration /
Dixmier trace.

## 12. The Morley edge-signature gauntlet — PROMISING, with one precise kill

Hypothesis (Jeff): a 4D boundary carrying two 2D edge operators generates
the 3+1 split, with the torsion/twist in the D_F projection carried, not
assumed away. Steelmanned, then formalized in `EdgeSignature.lean`
(30 theorem/lemma declarations; the gauntlet dossier groups the core
results into four sections). Build status: verified green by the gauntlet
on 2026-10-11; not re-verified on 2026-10-15 (rebuild attempts timed out
without errors — see §0). The verdicts below are the 2026-10-11 record.

- **Morley core — T1.** Edge-pair ⟺ fundamental symmetry: from η² = 1,
  the operators E± = (1±η)/2 are idempotent, orthogonal, and
  complementary (`edgePair_of_symm`); conversely a perfect pair gives
  η = E₊ − E₋ with η² = 1 (`symm_of_edgePair`). The "arbitrary input →
  perfect structure" pattern has real formal content: perfection is
  forced by η² = 1 alone.
- **Flip twist carried — T1.** The doubled edge decomposition is
  flip-invariant for (η, η): the Rung 2 twist preserves the perfection.
- **Torsion carried exactly — T1.** (η+T)² = 1 + (ηT + Tη + T²)
  (`torsion_defect`); fluctuated edge operators miss idempotence by
  exactly (2⁻¹)² • (ηT + Tη + T²) (`edgePlus_torsion_defect`);
  perfection survives torsion iff ηT + Tη + T² = 0, a Maurer–Cartan-type
  flatness condition (`torsion_flat_iff`). (The earlier ℂ⁷-torsion claim
  remains killed and is not resurrected.)
- **Strong emergence — KILL, by T1 counterexample.**
  `signature_not_determined`: (1,1) and (1,−1) on ℂ×ℂ both square to 1,
  but one has vanishing minus-edge (signature (2,0)) and the other does
  not (signature (1,1)). η² = 1 does not determine the signature; the
  3+1 numbers are extra data. The kill is itself a theorem.
- **Analogy assessment:** real formal content at the algebraic level; the
  "miracle" grading (maximal symmetry from no symmetry) remains
  philosophy, labeled NEEDS-WORK as an analogy.

Priced next steps: a D_F-specific torsion map (η built from Dirac data,
defect computed under inner fluctuations); the dimensional reading —
"two 2D" suggests neutral signature (2,2), and what breaks it to (3,1)
is open; integration with the twisted first-order condition; a boundary
spectral triple as the formal home of the "4D boundary."

## 13. Frontier and priced windows

The following are named, framed, and priced — not claimed.

1. **Unbounded operator theory in Mathlib.** Densely defined closed
   operators, the unbounded adjoint, von Neumann's A** theorem, the
   Cayley transform, projection-valued measures, the unbounded spectral
   theorem, and Borel functional calculus are absent from Mathlib
   (surveyed 2026-10-11; five checkable window statements are filed in
   `SpectralFrontier.lean`). This is the boundary of formalized analysis
   on the spectral prong.
2. **Second quantization (bosonic).** Blocked on the bosonic
   `adjoint_relation` assembly (§8) and Γ(U) functoriality.
3. **Boost invariance** of the mass-shell measure: one Jacobian identity.
4. **Strong continuity** of the one-particle representation: a dominated
   convergence argument with the dominating function identified.
5. **n-point Wick expansion:** the Wick recursion at 2n points.
6. **Faithful SM gauge representation** (§10, Track 1): priced at the
   pre-Option-A representation or the manifold factor.
7. **Continuum limit and interacting 4D QFT.** No construction exists in
   this corpus. The Wightman verdicts of Rung 5 are toy-model verdicts;
   the general theory is not formalized.
8. **Yang–Mills existence and mass gap.** Quarantined T5. The Clay
   statement is formalized as a fixed target (`ClayStatement.lean`), and
   the dossier discipline records why finite-level gaps do not transfer:
   Osterwalder–Seiler's strong-coupling lattice gap excludes the
   continuum limit; Balaban's renormalization-group work is not a
   mass-gap proof; φ⁴₄ triviality says nothing directly about Yang–Mills;
   spectral-gap undecidability results concern families of Hamiltonians,
   not the single Yang–Mills Hamiltonian.

## 14. Kill ledger (selected)

Killed claims return only as new entries by proof; the originals stand.

- As-stated Connes–Kreimer antipode axiom — refuted; corrected version
  proved (different claim).
- ρ_M ⊗ ρ_F as product twist — does not typecheck.
- Strong Morley emergence (edge data determine 3+1) — T1 counterexample.
- p/n as a fundamental gauge-coupled ± pair; electron as an interaction
  product of that sector — killed by standard physics (isospin is an
  approximate global symmetry; lepton number, spin, and statistics all
  fail for the composite-electron reading). The honest survivors:
  approximate global isospin, the electron as a separate lepton field,
  beta decay as weak charged current.
- W5 monomial-range cyclicity as framed — false; span version proved.
- Bosonic-form W6 criterion for fermions — fermion-blind; Koszul version
  proved.
- "Finite triple converges" (continuum language) — killed; priced roadmap
  instead.
- The φ-tower (golden-ratio mass hierarchy) — killed against measured
  mass ratios.
- ℂ⁷ torsion — killed; not resurrected by the Morley gauntlet.

## 15. What is NOT claimed (the immune system)

- **No 4D QFT.** The finite triple is zero-dimensional; the Wightman
  verdicts are one-mode toy verdicts; no interacting theory is
  constructed.
- **No continuum limit.** The continuum is a priced roadmap throughout.
- **No mass gap.** The Clay target is fixed and quarantined; nothing here
  is a step in a Clay proof, only infrastructure such a proof would need.
- **No full SM gauge group from the finite representation.** The
  represented U(1) is provably not hypercharge (§10). The algebraic
  match holds at the level of the full finite algebra and its unimodular
  subgroup.
- **No derived masses, couplings, or mixing angles.** All are labeled
  inputs wherever they appear.
- **No physical predictions.** Spectral, thermal, and trace numbers in
  this corpus are properties of the mathematical models, not measurements
  of nature.
- **No derivation from analysis where axiomatization was used.** Rung 3's
  promotions and Rung 4's bridge axiom are labeled T2 at every citation.

## 16. Reproducibility

- **Source:** https://github.com/jeffgurd888/thet-logos (Lean sources in
  `lean/ThetLogos/`; verdict dossiers in `whitepaper/`).
- **Build:** with Lean 4 / Mathlib per `lean/lean-toolchain` and
  `lean/lake-manifest.json`: `cd lean && lake build` (green; covers the
  14 root-imported modules). The remaining modules build individually:
  `lake build ThetLogos.<Module>` — 2026-10-15 status per module is
  reported in §0, including the two failures and one non-completion.
- **Counts:** the counting command of §0 reproduces every number in this
  paper from the sources.
- **Axioms:** `#print axioms <theorem>` in any module reproduces the
  footprints reported in §0.

---

*Notation.* φ denotes the modular flux i[K, D] (Hermitian,
`modularFlux_selfAdjoint`). Φ is reserved for the ontological glyph and is
not used in this paper. Tet (the narrator of the companion books) and thet
(the law) are distinct; neither is a mathematical object of this paper.
