# The Weld — WeldDuality Dossier (2026-10-16)

Labels (pre-agreed, holding): **T1 finite linear algebra.** The finite shadow of the
Morley idea Jeff proposed welding (2026-10-16): dimension counted by traces of spectral
projections. "2D holography" does NOT survive into the module — only the finite shadow
does. NOT a Yang–Mills rung. Jeff's dial setting: **"both in duality"** — both weld
configurations built as two faces of one module, ℂ⁴ arena, with linker theorems.
The Nested Resting Place pin (2026-10-16) anchors the design: the welded object rests —
its projections are fixed sets.

## Deliverable
- `lean/ThetLogos/WeldDuality.lean` — **893 lines; 73 theorems; 18 definitions.**
  New file only. EdgeSignature is NOT imported (its import chain is the Mathlib root;
  the small §1 pair algebra is restated locally — disclosed in the file header).

## Verification
- Targeted build: **"Build completed successfully (3120 jobs)"** (re-run by the parent agent).
- Zero `sorry`/`admit`/`native_decide` in code.
- Axiom spot-checks (parent agent, 7 headlines): `trace_weldPlus`, `conj_weldPlus`,
  `joint_fixed_iff_range`, `etaCorr_sq`, `weldPlus_etaDirac`, `signature_etaDirac`,
  `trace_weldPlus_etaCorr` — ALL exactly `[propext, Classical.choice, Quot.sound]`.

## What was proved
- **§1 Common core (whole):** for η² = 1, `weldPlus`/`weldMinus` = (1±η)/2 are
  complementary orthogonal idempotents; η = P₊ − P₋; trace formula
  `tr P₊ = (n + tr η)/2`; conjugation rigidity (signature is a unitary invariant);
  **resting place:** `fixed_iff_range_weldPlus` (ηv = v ↔ v ∈ range P₊), the −1 twin,
  and the stretch that landed: **`joint_fixed_iff_range`** — for two commuting
  involutions, the joint fixed set is the range of P₊(η₁)·P₊(η₂) (the pin's
  intersection-of-fixed-sets, proved).
- **§2 Face A — grading + correction (both forms):** parametrized corrected involution
  `corrInv c η A = c⁻¹ • (η + A)`, an involution when η² = A² = 1, ηA + Aη = 0, c² = 2.
  Concrete ℂ⁴: arena η = diag(1,1,1,−1); the corrected involution `etaCorr` carries a
  Hadamard block (1/√2)[[1,1],[1,−1]] on the mixed directions (`etaCorr_sq : etaCorr² = 1`).
- **§3 Face B — Dirac sign + gap split (whole):** D = diag(2,1,−1,−3); η_D its sign
  involution (Hermitian, η_D² = 1); `weldPlus_etaDirac` — P₊(η_D) = diag(1,1,0,0), the
  positive spectral subspace, by computation. H = D² = diag(4,1,1,9); gap split at
  Δ² = 2: complementary orthogonal idempotents; `gap_eigen`; `gap_dichotomy`
  (every eigenvalue is 1 or ≥ 2 — the gap is the empty interval (1,2)).
- **§4 Linkers (the duality, proved):** L1 `signature_etaDirac` — Face B is an
  instance of Face A; the (2,2) count for D and the (3,1) count for the arena both
  follow the INPUT (the `signature_not_determined` kill stands untouched, echoed in
  the file's comments). L2 `trace_weldPlus_etaCorr` — the corrected and uncorrected
  P₊ traces are EQUAL (= 3), while `weldPlus_etaCorr_ne` proves the projections
  genuinely DIFFER (stability is not vacuity). L3 resting places on both faces.

## Recorded adjustments
- §2b's arena correction has A² = the block support projection, not 1 globally —
  forced: a global anticommuting A with A² = 1 implies tr η = 0, impossible for the
  (3,1) arena (tr η = 2). The global form lives in §2a; the arena realizes the block form.
- Priced, not attempted (as pre-agreed): the general correction-stability theorem
  (finrank of P₊ constant along a general correction, arbitrary n) — only the
  worked-arena instance L2 is proved. Counts are carried by ℂ trace identities;
  no separate finrank restatement.

## Ledger labels
T1 finite linear algebra, both faces plus their duality linkers. Buys: a proved,
machine-checked unification of the grading/correction and Dirac-sign/gap pictures of
a spectral split, with the resting-place (fixed-set) characterization the pin asked
for. Buys NO holography, NO emergence of (3,1) (input, never derived), NO credit
toward Yang–Mills or any Millennium item.
