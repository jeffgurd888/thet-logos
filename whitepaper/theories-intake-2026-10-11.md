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

**Repair note (2026-10-15) — FIT verdict SUSPENDED, then RESTORED.** The
2026-10-15 paper-rebuild audit found `SpectralActionFinite.lean` BUILD-RED:
4 proof errors in `tr_DF_fourth_yukawa` (blocks e3, e5, e6, e8), all from
Mathlib/Lean drift since the 2026-10-11 verification — current `simp_rw`
processes its lemmas strictly in sequence and errors on any that makes no
progress, where the October pipeline reached a joint fixpoint. Repairs
(proof-local only; no statement changed, no sorry/admit/axiom added):
(i) e3/e8 — after the local `diagonal_add_eq` merges two diagonals, the
product of the merged diagonals must be reduced before `Matrix.trace_diagonal`
gets its turn: re-apply `Matrix.diagonal_mul_diagonal` after
`diagonal_add_eq` in the chain; (ii) e5 — the local `hsum` was stated with
`(starRingEnd ℂ) ·` where the pipeline now produces `star ·`; restated to
match (`starRingEnd_apply` is `rfl`, so the asserted equation is identical);
(iii) e3/e6/e8 — simp lemmas whose patterns no longer occur at that point
(`starRingEnd_apply`, `normSq_starRingEnd`, and the dead one of
`mul_star_eq_normSq`/`star_mul_eq_normSq` per block) trimmed to the single
live lemma per site. Re-verified 2026-10-15: `SpectralActionFinite` and
`SpectralActionBridge` build green; root `lake build` green (3325 jobs);
`#print axioms` on the headline theorems (`finite_heat_trace_even`,
`tr_DF_sq_yukawa`, `tr_fluctuated_sq`, `tr_DF_fourth_yukawa`, …) unchanged —
exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
**The spectral-action FIT verdict stands restored.**

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

## Candidate 6 — Morley-miracle edge signature: PROMISING with one precise kill (2026-10-11)

Jeff's hypothesis: a 4D boundary carrying two 2D edge operators generates
the 3+1 split — Lorentzian signature emergent from boundary/edge data, with
the torsion twist in the D_F projection carried (never assumed away);
inspired by Morley's miracle ("the perfect triangle inside any triangle
from the projection"). Gentle gauntlet requested (steelman first).
Full verdict: `whitepaper/gauntlet-morley-3plus1-2026-10-11.md`.

**File:** `lean/ThetLogos/EdgeSignature.lean` (commit `8eac400`).
Build green, 21 theorems, zero sorrys, zero new axioms; `#print axioms`
confirms only `[propext, Classical.choice, Quot.sound]` throughout.
**Re-verification attempted 2026-10-15 — INCOMPLETE.** Standalone
`lake build ThetLogos.EdgeSignature` exceeded both a 1200 s and a 1500 s
budget on this VM, with no errors emitted in either attempt and no olean
produced. (The module imports all of Mathlib, making it the repo's most
expensive standalone check, and the VM was shared with other build jobs
throughout.) The file's green status therefore remains its 2026-10-11
record above; the paper-rebuild audit's open item stays open pending a
longer build window. Verdict unchanged.

**FIT (PROMISING) — edge-pair ⟺ fundamental symmetry (Morley core, T1):**
the "two 2D edge operators" as a complementary orthogonal idempotent pair
`(E₊, E₋)` — the abstract self-dual/anti-self-dual decomposition — and the
"4D boundary signature data" as a fundamental symmetry `η` with `η² = 1`
(the Krein structure's algebraic core, Rung 3). Perfection (idempotence,
orthogonality, complementarity) is FORCED by `η² = 1` alone, for arbitrary
`η` — the genuine "arbitrary input → perfect structure" pattern
(`edgePair_of_symm`, `symm_of_edgePair`).

**FIT (PROMISING) — flip-twist equivariance (T1):** the doubled edge
decomposition is flip-invariant — the Rung-2 twist preserves the perfection.

**FIT (PROMISING) — torsion as exact defect (T1):**
`(η+T)² = 1 + (ηT + Tη + T²)` exactly (`torsion_defect`); fluctuated edges
miss idempotence by exactly `(2⁻¹)² • (ηT + Tη + T²)`; perfection survives
torsion iff `ηT + Tη + T² = 0` (Maurer–Cartan-type flatness). The killed
ℂ⁷-torsion claim is NOT resurrected.

**NO-GO (recorded) — strong emergence, by T1 counterexample:**
`signature_not_determined` — `(1,1)` and `(1,−1)` on `ℂ × ℂ` both square
to 1, but one's minus-edge vanishes (signature (2,0)) and the other's
doesn't (signature (1,1)). The signature *numbers* do not emerge from the
edge data; they are extra input. The mechanism (edge operators encode
signature via the fundamental symmetry) is real; the strong claim is dead,
and its death is itself a T1 theorem.

**Morley analogy: NEEDS-WORK** — real formal content at the algebraic level;
the "miracle" grading (maximal symmetry from no symmetry) stays philosophy.

**Priced windows:** D_F-specific torsion map (η built from Dirac data, defect
under inner fluctuations `D ↦ D_A`); the dimensional reading — "two 2D"
suggests neutral (2,2), not (3,1): what breaks it to (3,1); twisted-FOC
integration of the flatness condition; a boundary spectral triple as the
honest home for the "4D boundary".

## Intake queue (next candidates to test)

- BRST / anomalies (fit test against the gauge/fluctuation structure).
- Osterwalder-Schrader reconstruction bridge to the Wightman verdicts
  (`OsterwalderSchrader.lean` exists as structured targets).
- Noncommutative integration / Dixmier trace (needs the analytic house).
