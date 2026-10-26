import ThetLogos.PlaneAvgKernel
import ThetLogos.PlaneAvgKernelCircle

/-!
# ThetLogos.HaarAvgKernelReceipt — item 8 closes as COLLAPSED into item 7

**A naming receipt, not a new kernel.** The record carries two
names for one object. The seat-kernel gate dossier
(`whitepaper/seat-kernel-gate-kill-2026-10-24.md`, §3) says of the
kernel `osForm` actually pairs through:

> "its plane links are Haar-averaged by the Gibbs measure, so its
> effective kernel is a **third object** (the plane-averaged
> kernel), computed nowhere yet."

The Curiosity Ledger then split that one description into two
lines: item 7, the plane-averaged kernel `K̄` (`planeAvgKernel`,
landed 2026-10-26), and item 8, "the Haar-averaged OS kernel — the
third, uncomputed object." The scoping memo
(`haar-kernel-scoping-2026-10-26.md`) settled the provenance: item
8's phrase is the gate dossier's shorthand for the same `K̄`; no
primary source gives item 8 a formula, domain, group action, or
question distinct from `K̄`. This module is the formal receipt of
that collapse: `haarAvgKernel` is defined as an **alias** of
`planeAvgKernel`, and the landed statements are restated under the
alias, proved by the landed theorems.

**No distinct group-twirl kernel is defined here, or anywhere in
the corpus.** The corpus does own genuine Haar averages —
`averagingOperator` (representation vectors), `haarTwirl` and
`twirlEndo` (finite matrices) — but none is an OS kernel on
strict-half configuration pairs, and no theorem identifies any of
them with `K̄`. A conjugation/twirl-averaged OS kernel would be a
new object requiring a new name, statement, and ledger entry; it
inherits nothing from item 8.

What this receipt does NOT touch: positivity of `K̄` at general
`(G, ρ)` remains **L+ / open** — its sign sits in
`planeCrossingMarginal`, and Stage 1b-B at general `(G, ρ)` remains
OPEN. At the U(1) seat the pairing sign is landed and is transported
here. This receipt adds no theorems about the world — only the
identification.

NO CLAIM: this module closes **0** parts of the Clay Yang–Mills
statement, and 0 parts of any other official statement. Curiosity
Ledger item 8 closes as COLLAPSED into item 7.

This module is NOT in the root import list of the library (the
corpus pattern for recent exhibits); it is verified by a targeted
build.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped ComplexConjugate

section GeneralSeat

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- **The Haar-averaged OS kernel** — the record's second name for
`planeAvgKernel`. Defined as an alias, deliberately: the gate
record's "Haar-averaged" phrase and the plane name pick out the
same object (see the module header). Nothing new is computed;
the plane-link variables are marginalized by the product-Haar /
Gibbs integration inside `planeAvgKernel` itself. -/
noncomputable def haarAvgKernel (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) : ℂ :=
  planeAvgKernel μG ρ hN β z z'

/-- The collapse, as an equation: the two names denote one kernel. -/
theorem haarAvgKernel_eq_planeAvgKernel (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) :
    haarAvgKernel μG ρ hN β z z' = planeAvgKernel μG ρ hN β z z' :=
  rfl

/-- **The reduction identity under the alias**: `osForm`'s diagonal
is `Z⁻¹` times the strict-half pairing against the
Haar-averaged-named kernel — the landed
`osForm_eq_planeAvgKernel`, restated. Positivity of the pairing is
NOT asserted at general `(G, ρ)`. -/
theorem osForm_eq_haarAvgKernel
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (hd : 0 < d) (β : ℝ)
    (F : Config (Fin 4 → ZMod N) G → ℂ)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (hF : ∀ U, F U = f (fun ℓ : ↥(posLinks (N := N)) => U ℓ.1))
    (hfmeas : AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (hfbdd : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C) :
    osForm μG ρ β F F
      = ((gibbsPartition (torusShift N) μG ρ β : ℂ))⁻¹
        * ∫ r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G),
            (starRingEnd ℂ) (f r.2)
              * (haarAvgKernel μG ρ hN β r.1 r.2 * f r.1)
            ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
              (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) :=
  osForm_eq_planeAvgKernel μG ρ hρcont hN hd β F f hF hfmeas hfbdd

/-- **Symmetry under the alias**, transported from
`planeAvgKernel_symm`. -/
theorem haarAvgKernel_symm (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) :
    haarAvgKernel μG ρ hN β z z' = haarAvgKernel μG ρ hN β z' z :=
  planeAvgKernel_symm μG ρ hN β z z'

/-- **The β = 0 anchor under the alias**, transported from
`planeAvgKernel_zero`. -/
theorem haarAvgKernel_zero (hN : Even N)
    (z z' : ↥(posLinks (N := N)) → G) :
    haarAvgKernel μG ρ hN 0 z z' = 1 :=
  planeAvgKernel_zero μG ρ hN z z'

end GeneralSeat

section CircleSeat

variable {N : ℕ} [NeZero N]

/-- **Pairing nonnegativity at the U(1) seat under the alias**,
transported from `planeAvgKernel_circle_pairing_nonneg`: the
diagonal pairing of the Haar-averaged-named kernel on every bounded
AE-strongly-measurable strict-half observable is a nonnegative
real. This is the U(1) seat only; the general-`(G, ρ)` sign is not
asserted here or anywhere in this receipt. -/
theorem haarAvgKernel_circle_pairing_nonneg
    (hN : Even N) (β : ℝ) (hβ : 0 ≤ β)
    (f : (↥(posLinks (N := N)) → Circle) → ℂ)
    (hfA : AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb Circle))
    (Cf : ℝ) (hfB : ∀ z, ‖f z‖ ≤ Cf) :
    0 ≤ (∫ r, (starRingEnd ℂ) (f r.2)
          * (haarAvgKernel (haarProb Circle) circleRep hN β r.1 r.2
             * f r.1)
        ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb Circle).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb Circle))).re
    ∧ (∫ r, (starRingEnd ℂ) (f r.2)
          * (haarAvgKernel (haarProb Circle) circleRep hN β r.1 r.2
             * f r.1)
        ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb Circle).prod
          (Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb Circle))).im
        = 0 :=
  planeAvgKernel_circle_pairing_nonneg hN β hβ f hfA Cf hfB

end CircleSeat

end ThetLogos
