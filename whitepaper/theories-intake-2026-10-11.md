# Theories Intake — living dossier (2026-10-11)

Standing program per Jeff's directive ("keep adding all the theories that fit inside ACMD").
**Fit test:** a theory is admitted only if its core structures map onto ACMD's *formalized*
objects with real theorems. Analogies are not fit. NO-FIT verdicts are recorded with exact
reasons — a refused theory is a result.

Standing rules: zero new sorrys; tier honesty; `satisfiesDestruction` untouched;
existing files unmodified; local commits only; nothing pushed public.
Second quantization is owned by Rung 7 — intake does not touch it.

---

## Candidate 4 — Spectral action + index theory: FIT (2026-10-11)

**File:** `lean/ThetLogos/SpectralActionBridge.lean` (commit `e16a0ad`).
Build green, zero sorrys, zero new axioms; all headline footprints
`[propext, Classical.choice, Quot.sound]`.

**Bridge (a) — finite spectral action: FIT.** Real T1s on the formalized objects
(`smDirac`, `gammaF`, `fluctuatedDirac`):
- `sa_finite_a0` — Tr₃₂(1) = 32.
- `sa_finite_a2_yukawa` — Tr(D_F²) = 4·(|yν|²+|ye|²+3|yu|²+3|yd|²) + 2|yR|².
- `sa_finite_a2_fluctuated` — fluctuated trace expansion (Higgs/gauge content in A-terms).
- `trace_odd_pow_vanishes` / `trace_smDirac_odd_vanishes` — Tr(D^{2k+1}) = 0.
- `finite_spectral_action_expansion` — Tr(p(D/Λ)) for even cutoff polynomials.
- Priced window: a₄ needs Tr(D_F⁴) (open computation).
- **NO-FIT (recorded):** full continuum heat-kernel expansion — needs
  continuum/lattice limit (4-manifold Dirac, elliptic analysis).

**Bridge (b) — index theory: FIT at finite level.**
- `fredholm_index_fin_dim` (T1) — finite shadow of AS deformation-invariance.
- `card_chiPlus`/`card_chiMinus` — dim H⁺ = dim H⁻ = 16; supertrace Tr(γ_F) = 0.
- `chiral_compression_index_zero` — every D⁺ : H⁺→H⁻ has index 0.
- **NO-FIT (recorded):** Atiyah–Singer on manifolds — needs elliptic PDE theory.

No physical predictions claimed; coefficients are model properties.

---

## Pending

- Candidate 5 — Second quantization: owned by Rung 7; intake skips.

## Candidate 1 — KMS / Tomita-Takesaki: FIT (finite-dim) / T5 window (infinite-dim) (2026-10-11)

**File:** `lean/ThetLogos/KMSBridge.lean` (commit `7f7c588`).
Build green, zero sorrys, zero new axioms. `kms_identity_diagonal`
(ModularTime.lean:206, T3) untouched.

**FIT:** 10 T1 theorems — `gibbs_kms_weight` (finite-dim KMS identity
`Tr(Ω_β A σ_{iβ}(B)) = Tr(Ω_β B A)`), `gibbs_kms` (normalized Gibbs state),
`gibbsKMSAtOwnBeta_witness` / `magnetophaseKMS_witness` (discharge the two
pinned T5 targets in ModularFlux.lean), `gibbs_kms_flux_stationary` (KMS
equilibrium = flux-stationary: KMS **and** `thermal_flux_vanishes`),
`thermal_flux_observable_vanishing`, `gibbsWeight_stationary`.
T2 defs: `gibbsWeight`, `gibbsZ`, `gibbsState`, `modularFlowImag`, `KMSCondition`.

**T5 priced window (recorded):** `TomitaTakesakiWindow` — unbounded Tomita
involution, modular operator Δ, Araki perturbation, type-III factors;
Mathlib has no von Neumann algebra theory.

## Candidate 3 — AQFT (Haag-Kastler): per-axiom verdicts (2026-10-11)

**File:** `lean/ThetLogos/HaagKastlerFree.lean` (commit `7f7c588`).
Build green, 0 errors/warnings, zero sorrys, no `sorryAx` in 14 axiom prints.
`HaagKastler.lean` (interacting targets) unmodified.

- **Isotony — FIT (T1):** `localAlgBoson_isotone`, `localAlgFermion_isotone`,
  `localObsFermion_isotone` (conditional on explicit monotone `supp` marker).
- **Locality — FIT at creator level (T1):** bosonic elementwise commutativity
  (`localAlgBoson_commute`, `haagKastler_locality_boson`); fermionic even
  observables commute (`localObsFermion_commute`, `haagKastler_locality_fermion`
  via `anticomm_pair_mul_comm`). Honest caveat: spacelike hypothesis vacuous
  at creator level; full-field (anti)commutator needs the annihilation half.
- **Poincaré covariance — PARTIAL:** geometric half T1 (`poincareActPoint`,
  `spacelikeSeparated_poincare`); implementer half priced T5
  (`covariantNet_window`).
- **Spectrum condition — NO-FIT as theorem; T5 window**
  (`spectrumCondition_window`).
- **Vacuum — PARTIAL:** cyclic vector T1 (`localAlgBoson_univ`,
  `localAlgFermion_univ`); invariance priced.
- **Irreducibility / weak additivity — NO-FIT** (behind the W0 Fock gap).
- **Interacting net — T5, untouched** (`HaagKastlerExistence` not a witness).

## Candidate 2 — Classical Yang-Mills: FIT (classical) / NO-FIT (quantum) (2026-10-11)

**File:** `lean/ThetLogos/ClassicalYangMills.lean` (commit `cd56dee`).
Build green, zero sorrys, zero new axioms. (Worker errored on output-token cap;
coordinator completed the bridge: §§3–5.)

**FIT (classical):** 16 T1 theorems on the formalized objects —
- gauge group action: `gaugeAct_mul/comp/one/inv/selfAdjoint/pow/trace/trace_pow`.
- `repCurvature` (T2 def): represented 2-form `F = ∑ᵢ[D,aᵢ][D,bᵢ] + A²` from
  1-form data, with **exact** gauge covariance `repCurvature_gauge_covariant`
  (T1) under simultaneous unitary conjugation of the data.
- `ymAction F = Tr(F†F)` (T2 structured target) with T1 gauge invariance
  `ymAction_gauge_invariant`.
- `commutator_jacobi` (T1): algebraic core of the Bianchi identity.
- 6-dim caveat carried; junk-ideal quotient and continuum `∫_M Tr(F∧⋆F)`
  priced as windows; inhomogeneous `u[D,u*]` piece priced.

**NO-FIT (recorded):** quantum Yang-Mills mass gap — quarantined T5
(`MassGapDossier`); no quantization, no continuum, no gap claimed or touched.

## Intake queue (next candidates to test)

- BRST / anomalies (fit test against the gauge/fluctuation structure).
- Osterwalder-Schrader reconstruction bridge to the Wightman verdicts
  (`OsterwalderSchrader.lean` exists as structured targets).
- Noncommutative integration / Dixmier trace (needs the analytic house).
