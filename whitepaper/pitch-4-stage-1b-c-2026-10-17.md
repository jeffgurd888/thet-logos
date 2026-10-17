# Pitch 4, Stage 1b-C — The OS Hilbert Space (Time-Slice L² Route)

**Date:** 2026-10-17
**Module:** `lean/ThetLogos/LatticeOSSpace.lean` (1,065 lines)
**Verdict: STANDS** — the deliverable as scoped by the parked-fleet
gauntlet (dossier `whitepaper/gauntlet-parked-fleet-2026-10-17.md`,
§Stage 1b): the Osterwalder–Schrader Hilbert space, built by the
*time-slice L² route*, at every real β, unconditionally.
**PARTIAL-δ is NOT claimed** (δ = Stages 1b-A + 1b-B with B's
positivity proved; B's Gram clause remains open — see the fence).
**Clay parts closed: 0** (before and after; no statement in this
module touches the Clay statement).

## What stands (all T1, machine-checked)

- **§1 Marginals.** For a finite index set `s`, the restriction map
  `restrictConfig`, its measurability/continuity, the marginal
  measure `marginalMeasure μ s = μ.map (restrictConfig s)`, the
  integral identity `integral_marginalMeasure`, and the product
  factorization `marginalMeasure_pi` (via Stage 1a's `splitEquiv`):
  the marginal of a product measure is the product over `s`.
- **§2 β = 0 collapse of the Gibbs side.** `gibbsMeasure_zero`:
  at β = 0 the Gibbs measure *is* the configuration (product Haar)
  measure (density ≡ 1, partition = 1).
- **§3 The time slice.** `sliceLinks` (spatial links at time 0),
  `reflSliceLinks` (spatial links at time N−1), the reflection
  equivalence `sliceReflEquiv` between them, and
  `sliceLinks_subset_posLinks` at even N: slice links are strict
  positive-half links, so slice observables are `posLinks`
  observables for Stage 1b-B's form.
- **§4 The slice measure.** `sliceMeasure μG ρ β` = the slice
  marginal of the Gibbs measure; a probability measure at every
  real β (`isProbabilityMeasure_sliceMeasure`); the integral and
  Gibbs-expectation identities (`integral_sliceMeasure`,
  `gibbsExpect_slice`); at β = 0 it is exactly the product Haar
  measure over the slice (`sliceMeasure_zero` — the gauntlet's
  "slice Haar measure"); and the reflection-transport identity
  `sliceMeasure_map_transport`: the reflected slice's marginal is
  the transport of the slice marginal along the slice reflection
  (through Stage 1a's Gibbs reflection invariance, Stage 1b-A).
- **§5 The space.** `osSpace μG ρ β := Lp ℂ 2 (sliceMeasure μG ρ β)`,
  with completeness and the inner-product-space structure as
  Mathlib `Lp` instances (`osSpace_completeSpace`,
  `osSpace_innerProductSpace`), the inner product as the slice
  integral (`inner_osSpace`), the vacuum `osVacuum` (constant 1,
  norm 1: `norm_osVacuum`), slice states from L² representatives
  (`sliceState`, `inner_sliceState`), bounded observables are L²
  (`memLp_of_bounded`), the vacuum expectation identity
  (`vacuum_expectation`: ⟨1, f⟩ = ∫ f d(slice measure) = the Gibbs
  expectation of the pulled-back observable), and the norm bound
  `norm_sliceState_le`.
- **§6 Multiplication operators.** A bounded slice observable F
  (L∞ membership `hFinf` as hypothesis; discharged by
  `memLp_top_of_bounded` under the standing `hρcont`, `hd`)
  acts by pointwise multiplication as a continuous linear map
  `sliceMul` on the OS space, via the L∞·L² → L² Hölder estimate
  (`norm_mul_toLp_le`, `memLp_mul_slice`); operator norm ≤ the
  bound (`norm_sliceMul_le`); the algebra laws `sliceMul_one`
  (identity), `sliceMul_mul` (composition = pointwise product),
  `sliceMul_congr` (independence of the boundedness data); the
  adjoint is pointwise conjugation (`sliceMul_adjoint`), and a
  real-valued observable gives a self-adjoint operator
  (`sliceMul_selfAdjoint`).
- **§7 The conditional bridge (see the fence).**
  `osForm_nonneg_of_gramClause` and
  `osForm_slice_nonneg_of_gramClause`, and the unconditional
  β = 0 positivity for slice observables `osForm_slice_zero`.

## The fence (what is NOT claimed, and why)

Stage 1b-B landed PARTIAL: the OS form stands and is positive at
β = 0, but positivity at general β is reduced to one open clause —
the Gram/character-expansion factorization of the Wilson weight,
whose standard proof needs Peter–Weyl/Schur orthogonality for a
general compact group, absent from pinned Mathlib v4.35.0-rc3
(priced XL / Mathlib-blocked in the 1b-B dossier).

This module does not spend that clause:

- The slice L² space is positive **by construction**; nothing in
  §§1–6 routes through OS-form positivity at general β.
- The clause is named once, as `GramClause` (shape copied verbatim
  from 1b-B's `osForm_nonneg_of_gram` hypothesis). The two bridge
  theorems of §7 are **conditional on it as an explicit
  hypothesis**: IF the Gram clause holds at β, THEN 1b-B's OS form
  is positive on positive-half observables, in particular on slice
  observables. This is 1b-B's proved criterion fed with the named
  clause — no new positivity is proved.
- An identification of the OS form with the slice L² inner product
  at general β is **not asserted** (it would route through the
  same clause, or through the transfer matrix); it is fenced to
  Stage 1b-D / future work.
- The `posToSlice` marginal identity — `Measure.map (posToSlice hN)
  (π over posLinks) = π over sliceLinks` — is **named, unproved,
  priced S**. It would identify the β = 0 representative integral
  in 1b-B's `osForm_zero_eq` with the slice integral of §5, and
  transfer measurability from the slice measure to the product
  measure; neither use is made. `osForm_slice_nonneg_of_gramClause`
  accordingly takes the representative's product-measure
  measurability as a hypothesis.

## Verification

- Build: `lake build ThetLogos.LatticeOSSpace` — **green, 3,550
  jobs**; `.olean` present (1,237,064 bytes). (Sibling modules
  re-verified transitively; the module is NOT in root imports —
  disclosed, consistent with Stages 1a/1b-A/1b-B.)
- Counts (column-0 grep convention `^(theorem|lemma) `):
  **42 theorems/lemmas, 16 definitions/abbrevs**, 1,065 lines.
  Zero `sorry`, zero `admit` (grep-verified).
- Axiom checks (`#print axioms`, 11 headline results):
  `isProbabilityMeasure_sliceMeasure`, `sliceMeasure_zero`,
  `sliceMeasure_map_transport`, `inner_osSpace`, `norm_osVacuum`,
  `vacuum_expectation`, `norm_sliceMul_le`, `sliceMul_adjoint`,
  `sliceMul_selfAdjoint`, `osForm_nonneg_of_gramClause`,
  `osForm_slice_zero` — each depends on exactly
  **[propext, Classical.choice, Quot.sound]**.
- Program total after this landing: 2,327 + 42 = **2,369**
  theorem/lemma declarations.

## Accommodations (disclosed)

- `[MeasurableInv G]` is inherited from Stage 1b-A's reflection
  section (its `measurable_reflConfig` consumes it); several §4–§7
  statements pass `hρcont` (continuity of the representation) and
  `hd : 0 < d` as explicit hypotheses where the Gibbs measure's
  probability property is consumed — the same convention as
  Stages 1a/1b-A/1b-B.
- In §6 the L∞ membership of an observable is a hypothesis
  (`hFinf`), because `MemLp.of_bound` needs a finite-measure
  instance that the slice measure carries only conditionally;
  `memLp_top_of_bounded` discharges it under `hρcont`, `hd`.
- `Even N` is required exactly where reflection/positivity enter
  (slice ⊂ positive half, the Gram clause); the space, vacuum,
  and operators of §§5–6 need only `[NeZero N]`.

## Next

Stage 1b-D (transfer matrix + lattice gap, priced M in the
gauntlet) consumes: reflection invariance of the Gibbs measure
(1b-A), the slice space and its vacuum (§§4–5 here), and the
multiplication-operator algebra (§6 here). PARTIAL-δ remains
blocked on exactly one clause: `GramClause` (XL / Mathlib-blocked).
