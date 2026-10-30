/-
# S3-0 (companion): the stratum factorization and margin pins

Companion to `Span3GapPins` (brick S3-0 of the Span-3 first
pier). This module states, from landed definitions only:

* `StratumColumnFactorization` — LOC-3's named missing object
  in its product form, in the form of the S3-1 wall-identity
  gate dossier §1(i)
  (`whitepaper/s31-wall-identity-gate-2026-10-29.md`), and
* `UniformMarginFactorization` — the gate's §5 statement pin,
  riding inside brick S3-0 per the gate's §7 recommendation:
  one normalized margin `δ` welded to the factorized volumes.

This is a separate module because of the pre-existing tree
defect recorded in `Span3GapPins`' header (the duplicate
declaration `ThetLogos.reflSite_eq_torusShift_zero` in
`LatticeGramSeries` and `PlaneCrossingFactor`): the
factorization's definitions live on the `PolymerPartition`
chain, the U(1) regression (in `Span3GapPinsU1`) lives on the
`LatticeUniformGap` chain, and no single environment can hold
both chains.

**Both Props below are TARGET pins, labeled:** not results,
not premises, and neither is assumed anywhere in this module.
Nothing is proved here about factorization, uniformity, or
gaps at any `β > 0` seat. Proof-grade distance toward the
continuum is ZERO. NO CLAIM, parts 0, dials 0/4.
-/

import ThetLogos.Span3GapPins
import ThetLogos.PolymerPartition

namespace ThetLogos

open MeasureTheory

section Span3Factorization

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **Stratum column factorization at `(β, N)`** — LOC-3's
named missing object in its product form, stated here from
landed definitions only (`layerKernel`, `PlaneCrossingCube`;
`colZ`, `zPolymer`, `PolymerPartition`), in the form of the
S3-1 gate dossier §1(i): the layer kernel `𝒜` equals the
factorized polymer partition function, as a complex cast of a
real number,

  `layerKernel μG ρ β u u' = ((zPolymer ρ μG β u u' : ℝ) : ℂ)`

for every pair of layer data `u u'`. (The gate's §1(i)
quantifies `β` universally; this is the per-`β` form its §5
pin consumes — the universal form is the conjunction of these
over `β`.) The integrand of `𝒜` already factorizes over
columns pointwise (`exp_neg_layerAction_eq_prod`, landed);
what this statement asserts is that the integral over the
shared stratum variable factorizes — `∫∏ = ∏∫` for this
integrand family. It asserts no positivity, no spectral
content, and no uniformity in anything: one scalar identity
per `(β, N, u, u')`.

**Consumer, named on the face:** brick S3-1-F1 consumes and
reconciles this definition next in the block (it states this
Prop and `BridgeLOC3` and proves their equivalence from the
gate's §2.1 bookkeeping). This is a TARGET pin: not a result,
not a premise, and it is not assumed anywhere in this
module. -/
def StratumColumnFactorization (β : ℝ) : Prop :=
  ∀ u u' : LayerLink N → G,
    layerKernel μG ρ β u u' = ((zPolymer ρ μG β u u' : ℝ) : ℂ)

end Span3Factorization

section Span3MarginPin

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)

/-- **Uniform margin factorization at `(G, ρ)`, at fixed
`β`** — the statement pin of the S3-1 wall-identity gate §5,
verbatim in substance. There is a single normalized margin
`δ ∈ (0, 1]` such that at every even `N ≥ 2` the stratum
column factorization holds at `β` AND the per-instance
package yields that same `δ` as a gap bound:

  `∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (N : ℕ) [NeZero N] (hN2 : 2 ≤ N)`
  `(hN : Even N), StratumColumnFactorization μG ρ β ∧`
  `(GapPackage μG ρ hρcont hd β hN2 → GapBound μG ρ hρcont β hN2 δ)`.

Its truth would imply the factorization at every volume and
(U-vol)'s consequent under (U-vol)'s antecedent, by
construction; it is strictly stronger than the two walls'
conjunction in one respect — it welds the *same* `δ` to the
factorized volumes — and that weld is precisely the content
the corpus does not own in any form (gate §2.3: no landed
statement converts per-`(β, N)` conclusions into an
`N`-uniform margin).

**This pin is a TARGET, labeled:** it is not a result, not a
premise, and it is not assumed anywhere in this module or,
per the gate, anywhere in the campaign. Its proof is
FRONTIER and is not priced. -/
def UniformMarginFactorization (β : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
    ∀ (N : ℕ) [NeZero N] (hN2 : 2 ≤ N) (_hN : Even N),
      StratumColumnFactorization (N := N) μG ρ β ∧
      (GapPackage μG ρ hρcont hd β hN2 →
        GapBound μG ρ hρcont β hN2 δ)

end Span3MarginPin

end ThetLogos
