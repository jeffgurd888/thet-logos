# Pitch 4, Stage 1b-D — The Transfer Matrix on the OS Space

**Date:** 2026-10-17
**Module:** `lean/ThetLogos/LatticeTransfer.lean` (1,610 lines;
58 T1 theorems/lemmas + 13 definitions by column-0 grep
`^(theorem|lemma) ` / `^(noncomputable )?def `; zero
`sorry`/`admit` anywhere in the file)
**Build:** `lake build ThetLogos.LatticeTransfer` green,
3,551 jobs; `.olean` verified present
(`.lake/build/lib/lean/ThetLogos/LatticeTransfer.olean`,
1,809,000 bytes).
**Verdict: STANDS** — the strongest of the three pre-named
landing shapes in the commission: the full operator package
(form identity, contraction, vacuum fixed, self-adjointness,
form positivity — all at every real β) **plus** an exact gap
at β = 0 (`T₀` is exactly the vacuum projection, gap exactly
1), with the general-β gap precisely fenced below.
**PARTIAL-δ is NOT claimed** (δ needs Stage 1b-B's positivity,
which still waits on the Gram clause — priced XL,
Mathlib-blocked; this stage neither spends nor discharges it).
**Clay parts closed: 0** (before and after; no statement in
this module touches the Clay statement).
**Program total:** 2,369 + 58 = **2,427**.

## What stands (all T1, machine-checked)

The operator is the adjoint compression
`T_β = A*† ∘L B* : osSpace β →L[ℂ] osSpace β`, where `A*`
(`slicePull`) pulls a slice observable back to configuration
space along the time-0 restriction and `B*` (`nextPull`) does
the same along the time-1 restriction transported back to the
time-0 slice. Both legs are linear isometries into the same
`L²(ν)` (ν = the Gibbs measure).

- **§1 The next slice.** `slice1Links` (time-1 link stratum),
  disjoint from `sliceLinks`; the stratum transport
  `slice01Equiv` (base-site update `x ↦ update x 0 1`; needs
  `2 ≤ N`); the content transports `sliceStep`/`sliceStepBack`
  (mutual inverses); the next-slice reading `nextConfig`.
- **§2 Translation invariance.** For any site permutation
  commuting with the torus shifts, `shiftConfig` preserves the
  plaquette, the Wilson action, the Gibbs density, and hence
  the Gibbs measure (`gibbsMeasure_map_shiftConfig`,
  `Measure.map` form) — Stage 1b-A's reflection argument run
  for translations. Commutation facts for the unit shifts and
  products of commuting permutations.
- **§3 Stationarity identifications.** The time-1 marginal
  `slice1Measure` is a probability measure and equals the
  pushforward of the slice measure along `sliceStepBack`
  (`slice1Measure_eq_sliceMeasure`, via the −1 shift);
  consequently both readings are measure-preserving into
  `L²(ν)`: `ν.map (restrictConfig sliceLinks) = sliceMeasure β`
  and **`ν.map nextConfig = sliceMeasure β` at every real β**
  (`measurePreserving_nextConfig`).
- **§4 The operator.** `eq_of_forall_inner_left`
  (extensionality on the OS space); `slicePull`, `nextPull` as
  `Lp.compMeasurePreserving` linear isometries with their
  a.e. representative identities; `transferOp` and its
  application form `transferOp_apply`.
- **§5 Operator package I (every real β).**
  **Form identity** `transferOp_inner`:
  `⟪g, T_β f⟫ = ∫ conj(g∘restr₀) · (f∘nextConfig) dν` — the
  quadratic form of `T` *is* the two-slice Gibbs kernel
  pairing, as an identity.
  **Contraction** `transferOp_norm_le`: `‖T_β‖ ≤ 1`
  (Cauchy–Schwarz against the two isometries:
  `‖T f‖² = re ⟪B* f, A* (T f)⟫ ≤ ‖f‖·‖T f‖`).
  **Vacuum fixed** `transferOp_vacuum`: `T_β Ω = Ω`
  (via `coeFn_nextPull_osVacuum` and
  `slicePull_adjoint_of_coeFn_one`).
- **§6 The reflection step.** `Ψ` = (shift by −2 in time) ∘
  (Stage 1b-A's reflection): `Ψ` preserves the Gibbs measure
  (`gibbsMeasure_map_reflStepConfig`, needs `Even N`) and
  exchanges the two slices:
  `restr₀ (Ψ U) = sliceStep (restr₁ U)`,
  `restr₁ (Ψ U) = sliceStepBack (restr₀ U)`, and
  `nextConfig (Ψ U) = restr₀ U`
  (`nextConfig_reflStepConfig`). The site computation runs
  through `torusShift_symm_two_eq` (the double inverse shift
  subtracts 2 from the time coordinate) and the two
  `reflSite_torusShift_symm_two(_of_one)` identities
  (`reflSite (e₋₂ x) = update x 0 1` at time 0;
  `= update y 0 0` at time 1).
- **§7 Operator package II (every real β).**
  **Kernel symmetry** `transferOp_inner_symm`:
  `⟪T_β f, g⟫ = ⟪f, T_β g⟫` — composing the kernel integrand
  with the measure-preserving `Ψ` exchanges the slices.
  **Self-adjointness** `transferOp_adjoint` (`T_β† = T_β`)
  and `transferOp_isSelfAdjoint`, at `Even N`, from 1b-A's
  *proved* reflection invariance — no clause spent.
  **Form positivity** `transferOp_form_nonneg`: for slice
  observables `f, g` that are pointwise real and nonnegative,
  `⟪sliceState g, T_β (sliceState f)⟫` is real and
  nonnegative — the kernel integrand is pointwise a product
  of two real nonnegative numbers, and the conclusion follows
  by `integral_re`/`integral_im` and a.e. nonnegativity of
  the integral. Proved from the Gibbs measure's positivity
  alone; **no appeal to OS-form positivity or the Gram
  clause**.
- **§8 The exact gap at β = 0.** Vacuum pairings
  (`inner_osVacuum_left/right`); **factorization**
  `transferOp_zero_inner`: at β = 0 the kernel pairing splits
  as the product of the two one-slice expectations (Stage
  1a's `gibbsExpect_zero_mul_of_disjoint_dependsOnlyOn`
  applied to the disjoint slices, transported through
  Stage 1a's `gibbsExpect_eq_integral`);
  **rank-one formula** `transferOp_zero_apply`:
  `T₀ f = ⟪Ω, f⟫ • Ω` — `T₀` is *exactly* the orthogonal
  projection onto the vacuum line;
  `transferOp_zero_of_inner_vacuum_eq_zero` (`T₀` kills the
  vacuum-orthogonal complement) and
  `transferOp_zero_comp_self` (`T₀ ∘L T₀ = T₀`).
  **The lattice gap at β = 0 is therefore exactly 1:** the
  spectrum of `T₀` is `{1}` on the vacuum line and `{0}` on
  its complement. This is the free/infinite-temperature
  point; it is exact, and it is all the gap this stage
  claims.

## Axiom audit

`#print axioms` on the headlines — each exactly
`[propext, Classical.choice, Quot.sound]`, no others:
`transferOp_inner`, `transferOp_norm_le`, `transferOp_vacuum`,
`transferOp_adjoint`, `transferOp_isSelfAdjoint`,
`transferOp_form_nonneg`, `transferOp_zero_inner`,
`transferOp_zero_apply`, `transferOp_zero_comp_self`,
`slice1Measure_eq_sliceMeasure`, `measurePreserving_nextConfig`.

## The fences (what is NOT claimed)

- **General-β gap: NOT claimed, NOT proved.** Missing,
  named: (i) spectral input on `T_β` at fixed β > 0 —
  classically `T_β` is shown compact (continuous-kernel) and
  the gap is read off its spectrum; neither compactness nor
  a spectral theorem for this operator is formalized in this
  corpus (priced **M–L**). (ii) A gap uniform in volume and
  coupling along a continuum trajectory is Stage 3c's
  uniform estimates — research-scale, open in print. The
  exact β = 0 gap extends by no argument in this file.
- **Identification of `T`'s form with 1b-B's `osForm`:
  FENCED at every β.** It would need a time-direction
  Markov/layer factorization of the Gibbs measure, not
  formalized in this corpus (priced **M–L**). Consequently
  nothing here is a statement about OS-form positivity, and
  **PARTIAL-δ remains NOT claimed**.
- **Pointwise positivity of `T_β f`** (positive functions to
  positive functions) is not stated; it follows from the
  form positivity by the standard indicator argument
  (priced **S**, not formalized here).
- Hypotheses: `2 ≤ N` wherever the time-1 slice is
  identified with the time-0 slice (a one-step transfer on
  a one-slice torus is degenerate); `Even N` only where
  reflection symmetry is consumed (self-adjointness),
  matching Stage 1b-A; `transferOp`/`nextPull` carry the
  standing `hρcont` (continuity of the representation
  matrices) because Gibbs shift-invariance routes through
  density measurability — the same hypothesis the corpus's
  other Gibbs-invariance theorems carry. It is a Prop-level
  hypothesis; the operator carries no computational content
  from it.

## Consumption map (what this stage stands on)

Stage 0 (Wilson action, Gibbs data, `gibbsExpect_zero`),
Stage 1a (the Gibbs measure as a real measure,
`gibbsExpect_eq_integral`, disjoint-support factorization at
β = 0), Stage 1b-A (Gibbs reflection invariance
`gibbsMeasure_map_reflConfig`, reflection calculus), Stage
1b-C (`osSpace`, `sliceMeasure`, `osVacuum`, `sliceState`,
`integral_sliceMeasure`). Nothing routes through Stage
1b-B's OS form or its Gram clause.

## Tier summary

- T1: everything in the module (58 theorems/lemmas, 13
  definitions; zero sorry/admit; axioms exactly the standard
  three on all audited headlines).
- Fenced/priced, not claimed: general-β gap (M–L spectral
  input; Stage 3c uniform estimates), form = `osForm`
  identification (M–L), pointwise positivity (S),
  PARTIAL-δ (waits on 1b-B's Gram clause, XL/Mathlib-blocked).
- Clay statement parts closed: **0**.
