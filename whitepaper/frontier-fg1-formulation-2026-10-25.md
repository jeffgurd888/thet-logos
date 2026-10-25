# FG-1 — The Uniform Estimates at the U(1) Seat: Formulation

**Date:** 2026-10-25. **Status:** brick FG-1 of the frontier
gate (`frontier-gate-scoping-2026-10-25.md` §2.1), priced M
(paper formulation + dependency audit + Lean statement
module), **landed as a formulation**. Companion module:
`lean/ThetLogos/LatticeUniformGap.lean` (build green;
6 strict theorems, 9 definitions; axiom-clean; zero
sorry/admit).

**NO CLAIM.** Parts of any Clay statement closed by this
paper: **0**. Dials: **0/4**. Nothing in (U-vol) or (U-traj)
below is proved, priced for proof, or implied provable.
Formulability is not truth, and §4 records a [T4] reason to
doubt (U-traj) at this very seat.

---

## 1. Dependency audit (D-1), in Lean terms

The gate's dependency D-1 asked whether Stage 2's output
discharges the hypothesis Stage 3c's source consumes. The
parent resolved it from the definitions on disk; this audit
confirms the resolution in Lean terms and sharpens it by one
clause.

**What Q12 consumes.**
`TransferFormPos` (`LatticeTransferCompact.lean:2191`) is,
verbatim, the conjunction over the **whole** OS space
`osSpace (N := N) μG ρ β` of

- **(a)** `∀ f : osSpace, 0 ≤ (inner ℂ f (transferOp μG ρ
  hN2 hρcont β f)).re` — the transfer form's diagonal is
  nonnegative at every vector; and
- **(b)** `∀ v, transferOp μG ρ hN2 hρcont β v = v → v ∈
  Submodule.span ℂ {osVacuum μG ρ hρcont hd β}` — the
  vacuum eigenvalue is simple on `osSpace`.

`transfer_gap_of_formPos` (`:2209`) turns that package (plus
`Even N` and compactness of `transferOp`) into
`∃ δ > 0, ∀ lam ∈ spectrum ℂ (transferOp …), lam ≠ 1 →
‖lam‖ ≤ 1 − δ`. Note what the corpus does **not** have: `δ`
is not a function of `(β, N)` anywhere; it exists only inside
this packaged conclusion. Every statement in §3 is therefore
written over the packaged existence form.

**What Stage 2 discharged.** `SliceHPosOne`
(`LatticeSliceDescent.lean:101`) is the one-step diagonal
condition for slice observables, and S2-3's
`sliceHPosOne_circle` (`LatticeSliceCircle.lean:134`)
discharges it at the circle seat — `(haarProb Circle,
circleRep)`, every even `N`, every `β ≥ 0` — with no
positivity hypothesis, via Route C.

**The audit finding — the gap is one clause narrower than
"slice vs whole space" suggests, and it is clause (b).**
Clause (a) at the seat *is* supplied by landed theorems,
composed in the companion module as
`transferDiagU1_circle`:

> S2-3's `sliceHPosOne_circle`, composed with the descent
> brick's transport theorem
> `inner_transferOp_self_re_nonneg_of_sliceHPosOne`
> (`LatticeSliceDescent.lean`, §A), gives
> `TransferDiagU1 β hN2` — clause (a) at the seat, every
> `β ≥ 0`.

The composition is one line, and the reason is structural:
`osSpace` is *defined* as `Lp ℂ 2 (sliceMeasure …)`
(`LatticeOSSpace.lean:510`) and `sliceState` is
`MemLp.toLp` (`:555`), hence surjective onto `osSpace`.
"Slice observables" and "the whole space" are the same
vectors here; the transport theorem is the identity of
representations, not an extension argument. The module also
records the distinction as definitions, so the audit is
checkable rather than prose: `TransferDiagU1` (clause (a),
whole space), `SliceTransferDiagU1` (clause (a) at slice
states), `sliceTransferDiagU1_iff_sliceHPosOne` (the slice
form *is* `SliceHPosOne`, `slicePairOne` unfolded), and
`transferFormPosU1_iff` (`TransferFormPos` at the seat *is*
(a) ∧ (b)).

**What remains unbridged.** Clause **(b)**, vacuum
simplicity for `transferOp` on `osSpace` at `β > 0`, is
touched by no Stage 2 brick. The engine's vacuum clauses
live on the Π₁-quotient for the descended operator `T̂`
(S2-5's weld measures exactly the distance between these
worlds: `Q₁(x) = ‖x‖² − ‖Wx‖²`). Clause (b) is
Perron–Frobenius content — simplicity of the top eigenvalue
of a positivity-improving operator — and the corpus's only
`osSpace`-side positivity theorem,
`transferOp_form_nonneg` (`LatticeTransfer.lean:1302`), is
nonnegativity of the form at nonnegative real observables:
no strictness, no simplicity. And no landed theorem
concludes the conjunction `TransferFormPos` itself, at any
seat. Compactness rides as a second, independent hypothesis
(Q12: conditional on `HDen` at general `β`; unconditional
at `β = 0` given a Hilbert basis).

**Branch taken (parent-resolved, confirmed):** FG-1
formulates **under the named hypothesis "TransferFormPos
at U(1)"**, carried on the face of every statement in §3
through the per-instance package `GapPackageU1`
(compactness ∧ `TransferFormPosU1`). Per kill K-FG-1 this
brick's verdict is **PARTIAL-as-formulation**. The missing
connector is named, and is the next brick after FG-1:
**whole-space OS positivity at U(1) as the package Q12
consumes it — concretely its simplicity conjunct (b) —
proved from the landed seats** (the slice discharge, the
transport identity, and the weld). That is a proof brick,
not a formulation brick, and it is not priced here.

## 2. Trajectory language [T2]

Adopted by this brick, as convention, per gate §2.1:

- **Units.** Unit physical volume: the torus has `N` sites
  per side and physical size 1, so the lattice spacing is
  `a = 1/N`. A spectral gap `δ(β, N)` at the second
  eigenvalue corresponds to a physical mass
  `m = −log|λ₂| / a ≈ δ / a = N · δ` for small `δ`.
  (U-traj)'s floor `m ≤ N · δ` is this reading.
- **Trajectories.** A tuning curve is a function
  `βt : ℕ → ℝ`, read at even `N ≥ 2`. No assertion is made
  that any curve gives a continuum limit; the statements
  are about floors along curves, not about convergence.
  Writing this language required **no** projective-family
  or new measure machinery — curves are plain functions —
  so kill K-FG-1's total branch does not fire.
- **Admissibility, with the degenerate trajectory fenced
  by name.** `AdmissibleTrajectoryU1 βt` := `βt` is
  nonnegative everywhere, **and** `βt` takes a positive
  value at arbitrarily large even `N`. The second clause
  exists to fence out **the degenerate constant trajectory
  `β ≡ 0` — the β = 0 shadow**: at `β = 0` the per-instance
  gap is T1 with `δ = 1` at every `N`
  (`transfer_gap_zero`; restated in the module as
  `gapBoundU1_zero`), uniform, true, and vacuous — `T₀` is
  the vacuum projection, the degenerate theory. The fence
  also excludes every eventually-zero curve. No floor
  quantified over the admissible class can be witnessed
  by the shadow.

## 3. The statements — FORMULATION ONLY

At the circle seat `(haarProb Circle, circleRep)`, over the
packaged gap of §1. In the module: `GapBoundU1 β hN2 δ`
(the packaged spectral bound), `GapPackageU1 β hN2`
(compactness ∧ TransferFormPos at U(1)).

> **(U-vol) — volume uniformity at fixed coupling.**
> *Under TransferFormPos at U(1)*: if the per-instance
> package holds at every even `N ≥ 2`, then there is a
> single normalized bound `0 < δ ≤ 1` that is a gap bound
> at every even `N ≥ 2`. The fixed-coupling gap does not
> close as the torus grows.
> Module: `UniformVolumeGapU1`. **FORMULATION ONLY.**

> **(U-traj) — trajectory uniformity as `a → 0`.**
> *Under TransferFormPos at U(1)*: for every admissible
> trajectory `βt`, if the per-instance package holds at
> every point `(βt N, N)`, then there is a physical floor
> `m > 0` such that at every even `N ≥ 2` the packaged
> gap can be chosen normalized (`δ ≤ 1`) with
> `m ≤ N · δ`. The gap closes at most linearly in `a`.
> Module: `UniformTrajectoryGapU1`. **FORMULATION ONLY.**

Both statements quantify over the `δ` the package provides
per `(β, N)`; neither invents a gap function. (U-vol)'s
normalization `δ ≤ 1` is licensed by downward closure of
gap bounds (`gapBoundU1_of_le`, module).

## 4. Truth status

- **(U-vol) at `β = 0`:** the per-instance content is
  **T1 and vacuous** — `δ = 1` at every `N`
  (`gapBoundU1_zero`), the shadow of §2. (The module does
  not assemble the full packaged Prop at `β = 0`; the
  per-instance bound is what is T1.)
- **(U-vol) at `β > 0`, and (U-traj): OPEN.** No proof is
  scoped, priced, or implied. The hypothesis they are
  stated under is itself open at `β > 0` (§1, clause (b)).
- **The Coulomb doubt, stated plainly [T4].** At this
  seat, standard lattice lore expects 4D U(1) gauge theory
  to sit in a Coulomb phase whose continuum limit is a
  **free photon theory — gapless**: the physical mass is
  `0`, and along any trajectory entering that phase no
  floor `m > 0` of (U-traj)'s form exists. (U-traj) is
  therefore not merely unproved at the U(1) seat; its
  truth is **doubted on T4 grounds**. It is formulated
  here because the seat is where the corpus's language
  reaches and because Item 3's content had to be written
  somewhere checkable — the U(1) statements are the
  formulation's test bench, not its expected home.
  **Formulability ≠ truth.**

## 5. What this brick is, and the next brick

FG-1 converts gate §2.1's prose into checkable objects: an
audit that locates the D-1 gap at exactly one conjunct, a
trajectory language with the vacuity fence built into its
definition, and two statements a future proof — or a
future kill — can be aimed at without re-litigating what
was meant. **Verdict: PARTIAL-as-formulation** (K-FG-1's
PARTIAL branch: stated under the named hypothesis
"TransferFormPos at U(1)"; the total branch did not fire —
no projective machinery was needed).

**Named next brick (not commissioned here):** the D-1
weld — whole-space OS positivity at U(1) as Q12 consumes
it, concretely vacuum simplicity (clause (b)) for
`transferOp` on `osSpace` at `β > 0`, from the landed
seats. Until that lands, (U-vol) and (U-traj) remain
conditional formulations, and Item 3 remains a wall with
a now-exact address.

**NO CLAIM; 0 parts closed; dials 0/4.** Stage 1b-B at
general `(G, ρ)` remains OPEN and untouched by this brick.
