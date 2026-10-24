# Gram clause, transfer-matrix route, step S1 — the depth-one identification

**Date:** 2026-10-24. **Verdict: LANDED, parent-verified.**
Module: `lean/ThetLogos/LatticeTransferID.lean` (343 lines; imports
`ThetLogos.LatticeTransfer` only; no proved file edited). Parent
verification: fresh targeted build EXIT 0 (3,552 jobs — the same
job count the builder reported), recount **9 strict / 1 def**,
0 sorry / 0 admit, 0 same-line `@[simp]` declarations, parent-run
`#print axioms` on L1, L2 (a/b/c), the headline and the companion:
standard-only (`propext`, `Classical.choice`, `Quot.sound`) —
no `sorryAx`.

Program census: **4,348 strict / 4,397 attribute-inclusive / 144
counted modules** (re-derived at landing: whole tree 5,017 strict
minus the 669-strict non-chain remainder of the 2026-10-18/19
double-check sweep; 49 same-line `@[simp]` declarations
corpus-wide, none in this module).

Charter: `whitepaper/gram-clause-transfer-matrix-scoping-2026-10-24.md`.
Gate memo: `routeb-general-scratch/verdict-memo-tm-r0.md`;
builder memo: `routeb-general-scratch/verdict-memo-tm-s1.md`.

## The R0 → S1 story

The transfer-matrix charter named two gaps between the corpus's
landed transfer package (Stage 1b-D) and Stage 1b-B's open
clause: (i) operator positivity of the transfer operator `T` on
arbitrary vectors, and (ii) the identification of `T`'s quadratic
form with the Osterwalder–Schrader form `osForm`. Both were
fenced by one missing lemma — the layer/Markov factorization of
the Gibbs measure, priced M–L by Stage 1b-D's own dossier. The
charter's first rung, R0, was a pre-registered paper gate: work
the depth-one identification (a slice observable, `N = 4`) by
hand from landed statements only, with a kill criterion — the
route dies if the identification fails at depth one, or if the
first non-landed identity the chain needs cannot be stated as a
finite lemma about the corpus's own measures and maps.

**R0 PASSED**, and its finding was sharper than the charter
priced: at depth one the identification is a **symmetry fact**,
not a measure-factorization fact. Only two adjacent slices are
involved; reflection pairs slice `0` with slice `N−1`, and one
composite symmetry — the axis reflection, reflection after a
one-step forward time shift — carries that pairing exactly onto
the transfer step's `(0, 1)` pairing. The layer factorization is
**not consumed** at depth one. The chain closed modulo two
finite plumbing lemmas, L1 and L2, both statable in the corpus's
own language.

Step S1 is that paper chain, formalized exactly. No statement was
weakened, restated, or given extra hypotheses; the memo's one
route refinement is preserved — the chain runs through the
landed `osForm_eq_integral`, not the split-space kernel form
`osForm_eq_kernel`, so no factorization-type cost enters at the
first step either.

## What was built

All statements at general `(G, ρ)` (Haar probability measure `μG`
with the corpus's invariance instances, `ρ : G →* unitaryGroup
(Fin d) ℂ`), `N` even, on the `Fin 4 → ZMod N` torus.

1. **L1 — the slice reading of the reflection**
   (`restrict_sliceLinks_reflConfig`):
   `restrictConfig sliceLinks (reflConfig U) = fun ℓ =>
   restrictConfig reflSliceLinks U (sliceReflEquiv ℓ)` —
   the mirror image of the landed `restrict_reflConfig_eq`,
   computing the other restriction. A pointwise identity; it
   needed no even-`N` hypothesis.
2. **L2 — the axis reflection.** New definition
   `axisRefl := reflConfig ∘ shiftConfig (torusShift N 0)` —
   as a configuration map it reads `U` at time `-(x 0)`, the
   reflection about the axis through slices `0` and `N/2`.
   - (a) `gibbsMeasure_map_axisRefl` (`hρcont`, `Even N`, every
     real `β`): `Measure.map axisRefl gibbsMeasure = gibbsMeasure`
     — `map_map` composed from the two landed invariances (shift
     invariance via the landed `torusShift_one_hcomm`; reflection
     invariance `gibbsMeasure_map_reflConfig`).
   - (b) `restrict_sliceLinks_axisRefl`: the axis reflection
     fixes the slice reading — a slice link has time `0`, and
     `-(0) = 0`.
   - (c) `reflectedSliceReading_axisRefl` (`2 ≤ N`): the
     transported reflected-slice reading of `axisRefl U` is
     `nextConfig hN2 U` — at a slice link the axis reflection's
     source time is `-(-1) = 1`. Helpers:
     `measurable_axisRefl`, `torusShift_zero_reflSite` (the site
     arithmetic), `axisRefl_apply_of_ne`.
3. **HEADLINE — the depth-one identification**
   (`osForm_depthOne_transfer`; `hρcont`, `Even N`, `2 ≤ N`,
   `0 < d`, every real `β`, `φ` an `L²` slice observable,
   `hφ : MemLp φ 2 (sliceMeasure μG ρ β)`):
   `osForm μG ρ β F F = ⟪sliceState μG ρ β φ hφ,
   transferOp μG ρ hN2 hρcont β (sliceState μG ρ β φ hφ)⟫`
   for `F U = φ (restrictConfig sliceLinks U)` — the OS form's
   diagonal at a slice observable **is** the depth-one transfer
   quadratic form at the prepared slice state.
   Assembly, as formalized: `osForm_eq_integral` exposes the
   integral → reflection substitution (`integral_comp_reflConfig`
   + `reflObs_reflConfig`) turns the integrand into the conjugate
   slice factor × reflected slice factor → axis-reflection
   substitution (`integral_map` under L2 (a); pointwise L2 (b)
   on the first factor, L1 then L2 (c) on the second) turns it
   into the transfer kernel pairing → the landed
   `transferOp_inner` reads the pairing as the inner product,
   with the two AE kernel replacements (`ae_of_ae_map` of
   `MemLp.coeFn_toLp`, the second through
   `measurePreserving_nextConfig`) identifying the `Lp`
   representatives with `φ` itself.
4. **Companion at β = 0** (`osForm_depthOne_zero`): the
   depth-one diagonal at zero coupling is real and `≥ 0` — via
   the headline and the landed `transferOp_zero_apply`
   (`T₀ = ⟪Ω, ·⟫ • Ω`), so the diagonal is
   `|⟪Ω, ψ_F⟫|²`-shaped. This is the gate memo's β = 0
   cross-check, landed as a corollary.

## The fence (unchanged)

- The identification is closed at **depth one, slice subclass
  only**. Nothing is asserted about deeper observables or other
  depths.
- Gap (i) — positivity of `T` on arbitrary vectors (charter R2,
  the half-step square `T = V†V`) — is **untouched**.
- Whether depth `N/2` (charter R3) needs the layer factorization
  remains open; this gate does not decide it. The factorization
  question now sits at R2/R3 only — it is no longer a fence in
  front of the identification's first step.
- Stage 1b-B label unchanged: **positivity T1 for U(1) at every
  β ≥ 0 (Route C); general `(G, ρ)` OPEN.**

**NO CLAIM.** Parts of any official Clay statement closed: 0.
