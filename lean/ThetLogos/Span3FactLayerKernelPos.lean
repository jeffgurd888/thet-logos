/-
# S3-1-F2: FACT ⇒ `LayerKernelPos`, and the A0 assembly (PARTIAL)

Brick S3-1-F2 of the Span-3 first pier, per the S3-1
wall-identity gate dossier
(`whitepaper/s31-wall-identity-gate-2026-10-29.md`) §2.2 and
§7 (F2 spec, with its recommendation to fold the A0 assembly
into the same brick).

## What lands here (theorem (1), FULL)

**FACT ⇒ `LayerKernelPos`.** At fixed `(β, N)` with
`hN : Even N` and `hρcont`, the stratum column factorization
`StratumColumnFactorization μG ρ β` (S3-0's pin,
`ThetLogos.Span3MarginPin`) implies `LayerKernelPos μG ρ β`
(brick A0, `ThetLogos.LayerKernelPos`). The gate's §2.2
computation, formalized: by FACT the kernel value at each
`(u, u')` is `((zPolymer ρ μG β u u' : ℝ) : ℂ)`, and by
`colZ_independent` that real number is the SAME at every
`(u, u')` — the constant `c = zPolymer ρ μG β (fun _ : LayerLink N => 1)
(fun _ : LayerLink N => 1)`, positive by `zpolymer_pos`. The pairing
therefore separates: it equals
`(c : ℂ) * ((∫ F) * conj (∫ F))`, whose real part is
`c * ‖∫ F‖² ≥ 0`. Gauge invariance of `F` is NOT consumed —
the computation works for every `F`, and the proof below
says so by never using the invariance hypothesis. (No
integrability hypothesis on `F` is needed either: the
integral manipulations used — pulling a constant factor out
of a Bochner integral and commuting it with conjugation —
hold for arbitrary `F`, with both sides reading `0` on a
non-integrable representative.)

## What does NOT land here (item (2), PARTIAL at full rank)

The gate's recommendation was to fold in the A0 assembly as
ONE Lean theorem:

  `(∀ β ≥ 0, LayerKernelPos β) ⇒ clause (a) of TransferFormPos`

Clause (a), quoted exactly from `TransferFormPos`
(`LatticeTransferCompact`), is its first component:

  `∀ f : osSpace (N := N) μG ρ β,`
  `  0 ≤ (inner ℂ f (transferOp μG ρ hN2 hρcont β f)).re`

It is registered below as `TransferFormClauseA`, with the
landed projection `transferFormPos_clauseA` recording that
it is exactly clause (a), and the assembly itself is
registered as the TARGET pin `A0AssemblyTarget` — **stated,
not proved**. The named missing component, at full rank:

**MISSING COMPONENT — the `LayerKernelPos`-to-slice weld.**
No landed theorem derives `SliceHPosOne μG ρ hN2 hρcont β`
(the Stage-2 hypothesis whose transport along `sliceState`
is the only landed route to clause (a) on all of `osSpace`,
`inner_transferOp_self_re_nonneg_of_sliceHPosOne`,
`LatticeSliceDescent`) — or, equivalently, the
`osForm` / `planeAvgPairing` diagonal positivity on
strict-half observables — from `LayerKernelPos`. Of the A0
chain's three named components, the β1 factorization
(`planeCrossingMarginal_layerKernel`, landed) expresses the
crossing marginal as a PRODUCT of two `𝒜`-evaluations (top
extraction, and bottom extraction with arguments swapped),
and the α-remainder twirl reduction
(`planeAvgPairing_averages`, landed) reduces the `K̄`
pairing to gauge-averaged observables; but the Schur product
step exists in the corpus only as the finite-matrix
`Matrix.PosSemidef.hadamard` (`PlaquetteFactorPD`,
`ThermalPreCompensation`). There is **no landed
integral-kernel Schur/product theorem** composing the two
`𝒜`-pairings into positivity of the `K̄` pairing, and no
landed statement of that composition. The assembly
therefore cannot be formed from landed components, and it
is not papered over here.

**Seam note (the tree defect, checked for this brick).**
This module's imports (`Span3MarginPin`, `LayerKernelPos`)
sit on the `PlaneCrossingFactor` side of the duplicate
declaration `ThetLogos.reflSite_eq_torusShift_zero`
(`LatticeGramSeries` vs `PlaneCrossingFactor`), and the
`LatticeTransferCompact` chain reached through
`Span3GapPins` is seam-neutral, so theorem (1) and the
clause-(a) registration above build in one environment.
The transport chain on the other side of the weld
(`LatticeSliceDescent`, via `LatticeReconZero`) pulls in
`LatticeGramSeries` — the other side of the seam — so that
chain cannot be co-imported with this module's
`LayerKernelPos` chain in any case: verified empirically
for this brick, a probe module importing both chains fails
at import with "environment already contains
'ThetLogos.reflSite_eq_torusShift_zero' from
ThetLogos.PlaneCrossingFactor" (the probe was deleted after
the check; it is not part of this landing). No landed file
was edited to work around the seam.

**Buy, stated in the gate's substance:** a FACT landing
would now machine-discharge `LayerKernelPos` with no prose
link; discharging clause (a) from there still waits on the
named missing weld above, so the "no prose link in the
chain" buy for clause (a) is NOT yet achieved. FACT itself
remains unproved; `LayerKernelPos` (the `𝒜 ⪰ 0` core at
general `(G, ρ)`) is NOT proved by this brick — this is an
implication BETWEEN open statements, both ends open.

**Fences.** Pier block: proof-grade distance toward the
continuum ZERO; uniformity arrows untouched. NO CLAIM,
parts 0, dials 0/4. Fenced vocabulary unspent.
-/

import ThetLogos.Span3MarginPin
import ThetLogos.LayerKernelPos

namespace ThetLogos

open MeasureTheory

section Span3FactLayerKernelPos

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **Constancy of the factorized weight**: under column
independence (`colZ_independent`, Even `N`), `zPolymer` takes
the same value at every pair of layer data — the constant
`c` of the gate's §2.2, read at the base pair
`(fun _ : LayerLink N => 1, fun _ : LayerLink N => 1)`. -/
theorem zpolymer_eq_const (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (u u' : LayerLink N → G) :
    zPolymer ρ μG β u u'
      = zPolymer ρ μG β (fun _ : LayerLink N => 1) (fun _ : LayerLink N => 1) := by
  unfold zPolymer
  exact Finset.prod_congr rfl fun P _ =>
    colZ_independent ρ μG hN hρcont β u u' _ _ P P

/-- **FACT ⇒ `LayerKernelPos`** — theorem (1) of brick
S3-1-F2, the gate dossier's §2.2 computation (arrow A3, first
leg). With FACT at `(β, N)`, the kernel is the constant
positive real `c = zPolymer ρ μG β (fun _ : LayerLink N => 1) (fun _ : LayerLink N => 1)`
cast to `ℂ` (FACT + `zpolymer_eq_const`), and the pairing
separates:

  `∫∫ conj (F u) * c * F u' = c * ((∫ F) * conj (∫ F))`,

whose real part is `c * ‖∫ F‖² ≥ 0` since `c > 0`
(`zpolymer_pos`). Gauge invariance of `F` is not consumed:
the conclusion holds for every `F`, invariant or not, and
no integrability hypothesis on `F` is used. -/
theorem fact_implies_layerKernelPos (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (hfact : StratumColumnFactorization (N := N) μG ρ β) :
    LayerKernelPos (N := N) μG ρ β := by
  intro F _hF
  have hcpos : 0 < zPolymer ρ μG β (fun _ : LayerLink N => 1) (fun _ : LayerLink N => 1) :=
    zpolymer_pos ρ μG hρcont β _ _
  have hker : ∀ u u' : LayerLink N → G,
      layerKernel μG ρ β u u'
        = ((zPolymer ρ μG β (fun _ : LayerLink N => 1) (fun _ : LayerLink N => 1) : ℝ) : ℂ) := by
    intro u u'
    rw [hfact u u', zpolymer_eq_const μG ρ hN hρcont β u u']
  -- Replace the kernel by the constant `c` under both integrals.
  have hmain : (∫ u, ∫ u', (starRingEnd ℂ) (F u)
        * layerKernel μG ρ β u u' * F u'
        ∂(Measure.pi fun _ : LayerLink N => μG)
      ∂(Measure.pi fun _ : LayerLink N => μG))
      = ∫ u, ∫ u', (starRingEnd ℂ) (F u)
          * ((zPolymer ρ μG β (fun _ : LayerLink N => 1) (fun _ : LayerLink N => 1) : ℝ) : ℂ)
          * F u'
          ∂(Measure.pi fun _ : LayerLink N => μG)
        ∂(Measure.pi fun _ : LayerLink N => μG) :=
    integral_congr_ae (ae_of_all _ fun u =>
      integral_congr_ae (ae_of_all _ fun u' => by simp only [hker u u']))
  rw [hmain]
  -- Separate the double integral: it is `c * ((∫ F) * conj (∫ F))`.
  have hsep : (∫ u, ∫ u', (starRingEnd ℂ) (F u)
        * ((zPolymer ρ μG β (fun _ : LayerLink N => 1) (fun _ : LayerLink N => 1) : ℝ) : ℂ)
        * F u'
        ∂(Measure.pi fun _ : LayerLink N => μG)
      ∂(Measure.pi fun _ : LayerLink N => μG))
      = ((zPolymer ρ μG β (fun _ : LayerLink N => 1) (fun _ : LayerLink N => 1) : ℝ) : ℂ)
        * ((∫ u', F u' ∂(Measure.pi fun _ : LayerLink N => μG))
          * (starRingEnd ℂ)
            (∫ u, F u ∂(Measure.pi fun _ : LayerLink N => μG))) := by
    have hinner : ∀ u : LayerLink N → G,
        (∫ u', (starRingEnd ℂ) (F u)
            * ((zPolymer ρ μG β (fun _ : LayerLink N => 1) (fun _ : LayerLink N => 1) : ℝ) : ℂ)
            * F u' ∂(Measure.pi fun _ : LayerLink N => μG))
          = ((starRingEnd ℂ) (F u)
              * ((zPolymer ρ μG β (fun _ : LayerLink N => 1) (fun _ : LayerLink N => 1) : ℝ) : ℂ))
            * ∫ u', F u' ∂(Measure.pi fun _ : LayerLink N => μG) :=
      fun u => integral_const_mul _ _
    rw [integral_congr_ae (ae_of_all _ hinner)]
    have hpt : ∀ u : LayerLink N → G,
        ((starRingEnd ℂ) (F u)
            * ((zPolymer ρ μG β (fun _ : LayerLink N => 1) (fun _ : LayerLink N => 1) : ℝ) : ℂ))
          * ∫ u', F u' ∂(Measure.pi fun _ : LayerLink N => μG)
        = (((zPolymer ρ μG β (fun _ : LayerLink N => 1) (fun _ : LayerLink N => 1) : ℝ) : ℂ)
            * ∫ u', F u' ∂(Measure.pi fun _ : LayerLink N => μG))
          * (starRingEnd ℂ) (F u) := fun u => by ring
    have hconj : (∫ u, (starRingEnd ℂ) (F u)
          ∂(Measure.pi fun _ : LayerLink N => μG))
        = (starRingEnd ℂ)
          (∫ u, F u ∂(Measure.pi fun _ : LayerLink N => μG)) :=
      integral_conj
    rw [integral_congr_ae (ae_of_all _ hpt), integral_const_mul,
      mul_assoc, hconj]
  rw [hsep]
  -- The real part is `c * ‖∫ F‖²`, a product of nonnegatives.
  have hJre : ((∫ u, F u ∂(Measure.pi fun _ : LayerLink N => μG))
        * (starRingEnd ℂ)
          (∫ u, F u ∂(Measure.pi fun _ : LayerLink N => μG))).re
      = ‖∫ u, F u ∂(Measure.pi fun _ : LayerLink N => μG)‖ ^ 2 := by
    rw [RCLike.mul_conj
      (∫ u, F u ∂(Measure.pi fun _ : LayerLink N => μG)),
      ← RCLike.ofReal_pow, RCLike.ofReal_eq_complex_ofReal,
      Complex.ofReal_re]
  have hfin : (((zPolymer ρ μG β (fun _ : LayerLink N => 1)
          (fun _ : LayerLink N => 1) : ℝ) : ℂ)
        * ((∫ u, F u ∂(Measure.pi fun _ : LayerLink N => μG))
          * (starRingEnd ℂ)
            (∫ u, F u ∂(Measure.pi fun _ : LayerLink N => μG)))).re
      = zPolymer ρ μG β (fun _ : LayerLink N => 1)
          (fun _ : LayerLink N => 1)
        * ‖∫ u, F u ∂(Measure.pi fun _ : LayerLink N => μG)‖ ^ 2 := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hJre]
    ring
  rw [hfin]
  exact mul_nonneg hcpos.le (pow_nonneg (norm_nonneg _) 2)

end Span3FactLayerKernelPos

section Span3A0Assembly

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **Clause (a) of `TransferFormPos`, quoted exactly** — the
first component of `TransferFormPos`
(`LatticeTransferCompact`):

  `(∀ f : osSpace (N := N) μG ρ β,`
  `  0 ≤ (inner ℂ f (transferOp μG ρ hN2 hρcont β f)).re)`

registered here as a standalone predicate so the A0
assembly's target is a Lean statement, not prose. (Clause
(b), vacuum simplicity, is the second component; it is
discharged at general `(G, ρ)` by `fixed_mem_span` and is
not this brick's target.) -/
def TransferFormClauseA (β : ℝ) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) : Prop :=
  ∀ f : osSpace (N := N) μG ρ β,
    0 ≤ (inner ℂ f (transferOp μG ρ hN2 hρcont β f)).re

/-- Clause (a) is exactly the first projection of
`TransferFormPos` — a landed triviality, recorded so the
registration above is checked against the definition, not
against a paraphrase. -/
theorem transferFormPos_clauseA (β : ℝ) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hPF : TransferFormPos μG ρ β hN2 hρcont hd) :
    TransferFormClauseA (N := N) μG ρ β hN2 hρcont :=
  hPF.1

/-- **The A0 assembly, as a TARGET pin (PARTIAL — stated,
not proved).** The statement the gate's §7/F2 spec asked
this brick to land as one Lean theorem:

  at `Even N`, `LayerKernelPos` at every `β ≥ 0` implies
  clause (a) of `TransferFormPos` at every `β ≥ 0`.

**This pin is not a result and is not proved anywhere in
this module.** The named missing component is the
`LayerKernelPos`-to-slice weld recorded in the module
header: no landed integral-kernel Schur/product theorem
composes the β1 factorization's two `𝒜`-pairings into
positivity of the `K̄` / `osForm` pairing, and no landed
theorem derives `SliceHPosOne` (the only landed route to
clause (a) on all of `osSpace`, via
`inner_transferOp_self_re_nonneg_of_sliceHPosOne`) from
`LayerKernelPos`. That route's chain (`LatticeSliceDescent`)
also sits on the `LatticeGramSeries` side of the
`reflSite_eq_torusShift_zero` duplicate seam and cannot be
co-imported with this module's `LayerKernelPos` chain, so
the weld cannot even be stated in this environment. The
assembly stays dossier-grade until that component lands. -/
def A0AssemblyTarget (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (_hd : 0 < d) :
    Prop :=
  Even N →
  (∀ β : ℝ, 0 ≤ β → LayerKernelPos (N := N) μG ρ β) →
  ∀ β : ℝ, 0 ≤ β → TransferFormClauseA (N := N) μG ρ β hN2 hρcont

end Span3A0Assembly

end ThetLogos
