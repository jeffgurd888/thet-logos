import ThetLogos.NullStart
import ThetLogos.LatticeBoundaryOp

/-!
# ThetLogos.LatticeContainment — the containment package

A **synthesis brick**, commissioned by the Grand Unified 0 gauntlet
(`your_files/grand-unified-0-gauntlet-2026-10-24.md`, claim set C4/C5):
the three already-landed T1 anchors of the containment reading,
packaged as **one citable conjunction** — the headline theorem
`containment_package`. This module proves **nothing new**: every
component is proved by direct application of a landed result, named
at each step. It makes the anchors one object.

The three anchors:

1. **Silence at the null** (`ThetLogos.NullStart`, STANDS WHOLE):
   at the degenerate state (constant weights) the modular flux
   vanishes for every Dirac operator —
   `NullStart.flux_zero_of_diagModularK_const`.
2. **The boundary at zero** (`ThetLogos.LatticeBoundaryOp`, DB1):
   the boundary operator at `β = 0` is identically `1`
   (`bdry_zero`), and the Gibbs measure in split coordinates
   decouples into the normalizing scalar times the product of the
   two halves' product Haar measures
   (`gibbsMeasure_map_splitEquiv_zero`).
3. **Pairing only through the container** (`LatticeBoundaryOp` §6):
   every Gibbs pairing of a two-half observable runs through the
   boundary operator — expectation form
   (`integral_splitEquiv_factor_bdry`) and iterated Fubini form
   (`pairing_through_bdry`).

**Fences.** **NO CLAIM** — parts of any official Clay statement
closed by this module: **0**. Stage 1b-B positivity at general
`(G, ρ)` remains **OPEN**; this module asserts **no positivity of
`Bdry`** on any vector class (its positive-definiteness is Item 1's
open question, fenced off in DB1 and fenced off here). The doctrine
reading of these anchors — the Grand Unified 0 dossier,
"1 split into 2 contained in 0" — is **T5** and lives in the
dossier (`your_files/grand-unified-0-2026-10-24.md`), **not** in
this module: this module proves finite statements only, and the
conjunction below is exactly those finite statements, no more.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section Containment

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## The three anchors, restated for citation -/

/-- **Anchor 1 — silence at the null.** At the degenerate state
(constant weights `c`), the modular flux at the built modular
Hamiltonian vanishes for **every** Dirac operator `D`, at every
matrix size `M`. Direct restatement of
`NullStart.flux_zero_of_diagModularK_const` (itself proved there by
the scalar route: constant weights make `K` a scalar matrix, and
scalars are flux-silent against everything). -/
theorem containment_flux_silent (M : ℕ) (c : ℝ)
    (D : Matrix (Fin M) (Fin M) ℂ) :
    modularFlux (diagModularK (fun _ : Fin M => c)) D = 0 :=
  NullStart.flux_zero_of_diagModularK_const c D

/-- **Anchor 2a — the boundary at zero coupling is trivial.** The
boundary operator at `β = 0` is identically `1`: the container
holds without gripping. Direct restatement of `bdry_zero`. -/
theorem containment_bdry_zero
    (p : (↥(halfLinks (N := N)) → G)
      × (↥(negLinks (N := N)) → G)) :
    Bdry ρ 0 p = 1 :=
  bdry_zero ρ p

/-- **Anchor 2b — decoupling at zero coupling.** With the boundary
operator trivial, the Gibbs measure in split coordinates is the
normalizing scalar times the plain product of the two halves'
product Haar measures: at `β = 0` the halves are independent.
Direct restatement of `gibbsMeasure_map_splitEquiv_zero`. -/
theorem containment_decouple_zero
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) :
    (gibbsMeasure (torusShift N) μG ρ 0).map
        (splitEquiv (halfLinks (N := N)))
      = (ENNReal.ofReal (gibbsPartition (torusShift N) μG ρ 0))⁻¹ •
        ((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) :=
  gibbsMeasure_map_splitEquiv_zero μG ρ hρcont hN

/-- **Anchor 3a — pairing through the boundary, expectation form.**
The Gibbs expectation of a split-coordinate observable is the
boundary-operator pairing of the observable under the product of
the two half Gibbs-type measures (with the normalizing scalar).
Direct restatement of `integral_splitEquiv_factor_bdry`. -/
theorem containment_pairing_expectation
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (Φ : ((↥(halfLinks (N := N)) → G)
      × (↥(negLinks (N := N)) → G)) → ℂ)
    (hΦ : StronglyMeasurable Φ) :
    ∫ U, Φ ((splitEquiv (halfLinks (N := N))) U)
        ∂(gibbsMeasure (torusShift N) μG ρ β)
      = ∫ p, (Bdry ρ β p) • Φ p
          ∂((ENNReal.ofReal
              (gibbsPartition (torusShift N) μG ρ β))⁻¹ •
            ((halfGibbsPlus μG ρ β).prod
              (halfGibbsMinus μG ρ hN β))) :=
  integral_splitEquiv_factor_bdry μG ρ hρcont hN β Φ hΦ

/-- **Anchor 3b — pairing through the boundary, iterated form.**
The boundary-operator pairing iterates over the two halves: first
the negative half against the kernel, then the closed half.
Direct restatement of `pairing_through_bdry`. -/
theorem containment_pairing_iterated (hN : Even N) (β : ℝ)
    (Φ : ((↥(halfLinks (N := N)) → G)
      × (↥(negLinks (N := N)) → G)) → ℂ)
    (hΦ : Integrable (fun p => (Bdry ρ β p) • Φ p)
      ((halfGibbsPlus μG ρ β).prod (halfGibbsMinus μG ρ hN β))) :
    ∫ p, (Bdry ρ β p) • Φ p
        ∂((halfGibbsPlus μG ρ β).prod (halfGibbsMinus μG ρ hN β))
      = ∫ y, ∫ u, (Bdry ρ β
            ((y, u) : (↥(halfLinks (N := N)) → G)
              × (↥(negLinks (N := N)) → G))) • Φ
            ((y, u) : (↥(halfLinks (N := N)) → G)
              × (↥(negLinks (N := N)) → G))
          ∂(halfGibbsMinus μG ρ hN β) ∂(halfGibbsPlus μG ρ β) :=
  pairing_through_bdry μG ρ hN β Φ hΦ

/-! ## The package -/

/-- **THE CONTAINMENT PACKAGE.** The three landed anchors as one
citable conjunction, at their natural generality: for a finite
gauge theory `(G, ρ)` on the even lattice `N` (with the standing
Haar probability measure `μG` and representation-continuity
hypothesis where the landed statements carry it),

1. **silence at the null** — at constant weights the modular flux
   vanishes for every Dirac operator, at every matrix size;
2. **the boundary at zero** — `Bdry` at `β = 0` is identically `1`,
   and the split Gibbs measure decouples as the normalizing scalar
   times the product of the two halves' product Haar measures;
3. **pairing only through the container** — the boundary-operator
   pairing of any integrable two-half observable iterates over the
   two halves through `Bdry` and nothing else.

This is a packaging theorem: the proof is the four landed results
above, applied. It asserts nothing beyond them — in particular no
positivity of `Bdry`, no Stage 1b-B progress, and no doctrine:
the T5 reading of this conjunction is the Grand Unified 0
dossier's, and it is not part of this statement. -/
theorem containment_package
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) :
    (∀ (M : ℕ) (c : ℝ) (D : Matrix (Fin M) (Fin M) ℂ),
        modularFlux (diagModularK (fun _ : Fin M => c)) D = 0)
      ∧ (∀ p : (↥(halfLinks (N := N)) → G)
          × (↥(negLinks (N := N)) → G), Bdry ρ 0 p = 1)
      ∧ ((gibbsMeasure (torusShift N) μG ρ 0).map
            (splitEquiv (halfLinks (N := N)))
          = (ENNReal.ofReal (gibbsPartition (torusShift N) μG ρ 0))⁻¹ •
            ((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
              (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)))
      ∧ (∀ (β : ℝ)
          (Φ : ((↥(halfLinks (N := N)) → G)
            × (↥(negLinks (N := N)) → G)) → ℂ),
          Integrable (fun p => (Bdry ρ β p) • Φ p)
            ((halfGibbsPlus μG ρ β).prod (halfGibbsMinus μG ρ hN β)) →
          ∫ p, (Bdry ρ β p) • Φ p
              ∂((halfGibbsPlus μG ρ β).prod (halfGibbsMinus μG ρ hN β))
            = ∫ y, ∫ u, (Bdry ρ β
                  ((y, u) : (↥(halfLinks (N := N)) → G)
                    × (↥(negLinks (N := N)) → G))) • Φ
                  ((y, u) : (↥(halfLinks (N := N)) → G)
                    × (↥(negLinks (N := N)) → G))
                ∂(halfGibbsMinus μG ρ hN β)
                ∂(halfGibbsPlus μG ρ β)) :=
  ⟨fun M c D => containment_flux_silent M c D,
   fun p => containment_bdry_zero ρ p,
   containment_decouple_zero μG ρ hρcont hN,
   fun β Φ hΦ => containment_pairing_iterated μG ρ hN β Φ hΦ⟩

end Containment

end ThetLogos
