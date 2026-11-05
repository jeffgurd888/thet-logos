/-
# WB-2: the A0 weld in DIRECT form (restatement pin)

Brick WB-2 of the weld line, per the weld scoping of
2026-11-04 (`your_files/weld-scoping-2026-11-04.md`, Map A
row W-A8 and the WB-2 pricing there), the governing scoping
memo `routeb-general-scratch/scoping-f2-weld-2026-10-31.md`
(section 2, the weld exactly), and the registration pin
F2-W0 (`ThetLogos.Span3A0AssemblyPost`).

**What this module is.** The A0 weld — the intermediate
implication of memo section 2, at each `beta >= 0`,

  `LayerKernelPos muG rho beta`
    -> `SliceHPosOne muG rho hN2 h-rho-cont beta`

— restated in DIRECT form: `SliceHPosOne`
(`ThetLogos.LatticeSliceDescent`) is named in the code
itself, in a single module that imports BOTH chains the
weld connects. F2-W0 registered this implication only in
parameterized pin form
(`layerKernelPos_implies_sliceHPosOne`, with the slice
endpoint carried as an explicit parameter `SlicePos`),
because at registration time (2026-10-31) the two chains
sat on opposite sides of the
`reflSite_eq_torusShift_zero` duplicate-declaration seam
and no single Lean environment could import both. That
seam CLOSED on 2026-10-31 (F2-W1: the
`PlaneCrossingFactor` copy renamed
`reflSite_eq_torusShift_zero_bot`; co-import probe passed;
weld scoping 2026-11-04 re-verified at HEAD). This module
is the co-import, by construction: it imports
`ThetLogos.Span3A0AssemblyPost` (the `LayerKernelPos`
chain, `PlaneCrossingFactor` side) and
`ThetLogos.LatticeSliceDescent` (the slice chain,
`LatticeGramSeries` side) into one environment, and the
direct statement below typechecks in it.

**What is proved here — pin-grade only.** (i) The direct
form is exactly the registered parameterized pin at its
intended instantiation (`a0WeldDirect_iff`, a
definition-level identity). (ii) The direct form composes
with the landed transport
`inner_transferOp_self_re_nonneg_of_sliceHPosOne`
(`LatticeSliceDescent`) to give the registered headline
`A0AssemblyTarget` (`a0AssemblyTarget_of_a0WeldDirect`):
the weld, where it is supplied, closes the headline with
no further component. Both are compositions of landed
objects; there is no new mathematics in this module.

**What is NOT proved here — the fence, on the face.** The
weld itself is NOT proved. Its two blockers stand exactly
as the weld scoping graded them (W-A8, CONDITIONAL):
(i) its input — `LayerKernelPos` at every `beta >= 0` in
general — is OPEN (proved supports: `beta = 0` at general
`(G, rho)`, `layerKernelPos_zero`, and the single smallest
seat at `beta >= 0`, `layerKernelPos_seat`, both LK-P0,
2026-11-04; K-FACT-SEAT refuted the FACT route into it the
same day); (ii) its mathematical middle — no landed
theorem derives `SliceHPosOne` from `LayerKernelPos`; the
missing component is the integral-kernel Schur/product
composition (the seat Schur of F2-W0 target (2); the
abstract form is item (3) of `ThetLogos.IntegralKernelSchur`,
named OPEN on that module's face). This pin therefore does
NOT prove `LayerKernelPos`, does NOT close clause (a)
(the headline remains an implication whose antecedent is
the weld, which remains a hypothesis), and any reading of
this module as progress on FACT, on the layer kernel's
positivity, on clause (a) itself, or on uniformity is the
K-F2-4 buy-inflation failure, void on sight.

**NO CLAIM** — parts of any official Millennium statement
closed by this module: 0. Dials: 0/4. Proof-grade distance
toward the continuum: ZERO, before and after this pin.

This module is NOT in the root import list of the library
(the corpus pattern for pins); it is verified by a
targeted build.
-/

import ThetLogos.Span3A0AssemblyPost
import ThetLogos.LatticeSliceDescent

namespace ThetLogos

open MeasureTheory

section Span3A0WeldDirect

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **The A0 weld — DIRECT FORM (WB-2, stated, not
proved).** The intermediate implication of the F2 weld
memo's section 2, with the slice endpoint named in the
code: at `Even N`, `hN2 : 2 <= N`, continuity of the
representation, and each `beta >= 0`, `LayerKernelPos`
(`ThetLogos.LayerKernelPos`) implies `SliceHPosOne`
(`ThetLogos.LatticeSliceDescent`) — the one-step slice
diagonal positivity whose landed transport
`inner_transferOp_self_re_nonneg_of_sliceHPosOne` gives
clause (a) of `TransferFormPos` on all of `osSpace`. This
is exactly F2-W0's parameterized pin
`layerKernelPos_implies_sliceHPosOne` at its intended
instantiation `SlicePos hN2 h-rho-cont beta =
SliceHPosOne muG rho hN2 h-rho-cont beta` — an instantiation
that was nameable only in prose before F2-W1 closed the
duplicate seam, and is stated here in one environment
importing both chains. No instance of this statement is
asserted to hold: the weld is open at both its blockers
(module header). -/
def A0WeldDirect : Prop :=
  ∀ (_hN : Even N) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ), 0 ≤ β →
    LayerKernelPos (N := N) μG ρ β → SliceHPosOne μG ρ hN2 hρcont β

/-- **Direct form = the registered pin at its intended
instantiation.** The direct statement above is F2-W0's
parameterized pin `layerKernelPos_implies_sliceHPosOne`
with its endpoint parameter instantiated to
`SliceHPosOne` itself — a definition-level identity, no
content added, no instance discharged. This is the check
that the direct form restates the registered weld and
nothing else. -/
theorem a0WeldDirect_iff :
    A0WeldDirect (N := N) μG ρ ↔
      layerKernelPos_implies_sliceHPosOne (N := N) μG ρ
        (fun hN2 hρcont β => SliceHPosOne μG ρ hN2 hρcont β) :=
  Iff.rfl

/-- **Pin read-back for the direct form.** The weld in
direct form, applied: under it, `LayerKernelPos` at a
single `beta >= 0` yields `SliceHPosOne` at that `beta`.
Pin-grade projection only. -/
theorem a0WeldDirect_apply (hW : A0WeldDirect (N := N) μG ρ)
    (hN : Even N) (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (hβ : 0 ≤ β)
    (hLKP : LayerKernelPos (N := N) μG ρ β) :
    SliceHPosOne μG ρ hN2 hρcont β :=
  hW hN hN2 hρcont β hβ hLKP

/-- **The composition: direct weld => the registered
headline.** Where the weld in direct form is supplied,
the registered headline `A0AssemblyTarget`
(`ThetLogos.Span3FactLayerKernelPos`) follows by
composing it with the landed transport
`inner_transferOp_self_re_nonneg_of_sliceHPosOne`
(`ThetLogos.LatticeSliceDescent`): the weld gives
`SliceHPosOne` at each `beta >= 0` from `LayerKernelPos`
there, and the transport is clause (a) of
`TransferFormPos` at that `beta`, pointwise on
`osSpace` — which is `TransferFormClauseA` by its
registered definition. This closes the headline AS AN
IMPLICATION only: `LayerKernelPos` at every `beta >= 0`
remains the headline's antecedent, the weld remains an
unproved hypothesis, and clause (a) itself is not
asserted (module header, K-F2-4). -/
theorem a0AssemblyTarget_of_a0WeldDirect (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (hW : A0WeldDirect (N := N) μG ρ) :
    A0AssemblyTarget (N := N) μG ρ hN2 hρcont hd := by
  intro hN hLKP β hβ f
  exact inner_transferOp_self_re_nonneg_of_sliceHPosOne μG ρ hN2 hρcont β
    (hW hN hN2 hρcont β hβ (hLKP β hβ)) f

end Span3A0WeldDirect

end ThetLogos
