/-
# DeltaGramGapAttackPin — Route B registration pin (DGG-0)

Banked in Phase 2 (worktree thet-logos-dgg, branch dgg) on
the parent's slot clearance, under the standard discipline.
Drafted in Phase 1 staging (~/workspace/dgg-route-b/).

Registration pin for the DeltaGramGap factorization attack,
Route B (PSD-lift), scoped at
`~/workspace/your_files/deltagramgap-factorization-attack-scope-2026-11-24.md`
and fired by Zero, 2026-11-24 04:00 EST.  Band-S form:
definitions and statement pins only — **0 strict by design**;
this module proves nothing.

**THE WALL.**  The target is the corpus's own named Prop
`DeltaGramGap` (`LayerKernelGramCertFinite.lean`, line 156): a
finite Gram / sum-of-squares factorization existence statement
about one explicit finite sum — the contracted layer kernel
written in the δ-basis coefficient system.  It is **not** a
spectral gap: no operator's spectrum, no eigenvalue isolation,
no mass gap, no Yang–Mills content.  The word "gap" in this
line names exactly one thing — the absence, to date, of a proof
of this factorization.  No statement in this line states,
approximates, or gestures at a continuum limit, a spectral
threshold, or a physical mass.

**What Route B is.**  Every weight in the Prop is strictly
positive (`deltaCoeff ρ β t = exp (-β • gramDens ρ t) > 0` at
every `β`, `deltaCoeff_pos`, cited), so the feature map rescales
by `√w_j` freely: the Prop is equivalent to the finite kernel
matrix being positive semidefinite, given the index count
(`|ι| = |G|^{4N³}` against `rank ≤ |G|^{3N³}` — the scope's
audit).  Route B converts the already-owned positivity
(`LayerKernelPos`, character route, `layerKernelPos_char`,
CITED — never re-proved in this line, K-DGG-DUP) into that PSD,
then lifts a Gram factorization back over the padded index.
**The feature map Route B produces is an EIGENBASIS feature
map**: it uses `(α, t)` only as a large enough index set, it
exhibits no column separation, and it teaches nothing about
the δ-basis structure.  The constructive column-respecting
feature map is Route C — not fired, not claimed anywhere in
this line.

**Fences.**  Priced range `β ≥ 0`; even `N` only (the
identification of `layerKernel` with the contracted sum,
`layerKernel_eq_contracted`, is an even-`N` identity); `β < 0`
is the K-DGG-FAIL hunting ground (DGG-K, not fired).  Dial 2
stays 0 under every outcome, including total success — this
line closes (or kills) one named finite Prop inside the
𝒜 ⪰ 0 / M-U3 positivity joint, and `LayerKernelPos` is already
owned by another route, so even total success buys a second,
independent discharge of an owned theorem plus the completion
of the δ-certificate — not new positivity, not a dial.  No
FACT-shaped routing: nothing here routes through
`StratumColumnFactorization` (false at the binary seat).

**Kills registered.**  K-DGG-FAIL (shape pinned below as
`dggKillFAIL`): a seat and a `β` at which the contracted kernel
is provably not PSD, hence `¬ DeltaGramGap β` there.
K-DGG-DUP: owned content is cited, never re-proved or
double-counted — `LayerKernelPos` and `layerKernelPos_char`,
the G-0 discharge `LayerKernelSOSCert.layerKernelPos`, the
finite-sum and contracted forms, and every closed `kernel_eq`
in the instance ladder; any brick whose target is one of these
shrinks to citation on sight.  K-DGG-DEGEN (shapes pinned
below as `dggDegenerate`): an instance closed only at a
degenerate shape does not count as closing the gap.

Working module names only (`DeltaGramGapAttackPin`,
`LayerKernelGramCertPSD`); final naming is Zero's hand.

NO CLAIM; dials 0/4.
-/

import ThetLogos.LayerKernelGramCertChar
-- The pinned path of `Matrix.PosSemidef`, verified on disk
-- 2026-11-24 at Mathlib/LinearAlgebra/Matrix/PosDef.lean
-- (def line 62, `posSemidef_iff_dotProduct_mulVec` line 300,
-- `PosSemidef.of_dotProduct_mulVec_nonneg` line 311).
-- No import-order conflict with the corpus imports.
import Mathlib.LinearAlgebra.Matrix.PosDef

open MeasureTheory Finset
-- Environment repair (disclosed, 2026-11-24): `Matrix.PosSemidef`
-- over `ℂ` needs `ℂ`'s partial order, which this Mathlib pin
-- keeps as the scoped instance `Complex.partialOrder`
-- (`Mathlib/Analysis/Complex/Order.lean`), available only under
-- `open scoped ComplexOrder` — the house idiom, cf.
-- `PartnerThermal.lean`.  No statement is changed by this line.
open scoped Matrix ENNReal NNReal ComplexOrder

namespace ThetLogos

section DGGRegistration

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] [DiscreteTopology G]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N] [DecidableEq (LayerLink N)]

/-- The finite kernel matrix of the line: the layer kernel read
as a matrix on the configuration type `(LayerLink N → G)`.
DGG-1's target object; the PSD side of `dggEquiv`. -/
noncomputable def dggKernelMatrix (β : ℝ) :
    Matrix (LayerLink N → G) (LayerLink N → G) ℂ :=
  Matrix.of (layerKernel μG ρ β)

/-- **The priced target, registered.**  `DeltaGramGap` at every
`β ≥ 0`, at the ambient finite `(G, ρ)`, even `N`.  This is
DGG-3's headline, stated here as a pin; the `hN` argument is
the even-`N` fence on the face, not an input to the Prop
(the Prop itself is stated for every `N` and every `β` —
its priced range is what is fenced). -/
def dggTarget (hN : Even N) : Prop :=
  ∀ β : ℝ, 0 ≤ β → DeltaGramGap (ρ := ρ) (N := N) β

/-- **The working equivalence, registered** — the conversion
bricks' lemma-to-be: at even `N`, the named Prop is the
positive semidefiniteness of the finite kernel matrix, at
every `β`.  Both directions pass through
`layerKernel_eq_contracted` (the Prop's left side is the
contracted sum; the matrix is `layerKernel`), which is an
even-`N` identity — hence the `hN` fence on the face.
Direction `⇒` is DGG-1's output read backwards through the
rescaling (weights strictly positive at every `β`);
direction `⇐` is DGG-2's padding lift, which is `β`-agnostic
once the kernel is identified with the contracted sum. -/
def dggEquiv (hN : Even N) : Prop :=
  ∀ β : ℝ, DeltaGramGap (ρ := ρ) (N := N) β
    ↔ (dggKernelMatrix (N := N) μG ρ β).PosSemidef

/-- **K-DGG-FAIL, registered shape.**  A `β` at the ambient
seat where the named Prop is false.  The priced hunting
ground is `β < 0` (DGG-K, not fired): the Prop is stated for
all `β`, but positivity is owned only at `β ≥ 0`.  If this
shape is ever inhabited, the Prop dies at that seat at full
rank and its surviving range is whatever the record then
supports. -/
def dggKillFAIL : Prop :=
  ∃ β : ℝ, ¬ DeltaGramGap (ρ := ρ) (N := N) β

/-- The degenerate shapes of **K-DGG-DEGEN**: a `DeltaGramGap`
instance closed only at one of these shapes (the `β = 0`
shape; the `N = 1` shape, whose kernel is constant; the
trivial-representation shape, named in prose) proves nothing
about the gap at `β > 0` and does not count as closing it.
Instances at such seats are banked labeled degenerate, or
not banked. -/
def dggDegenerate (β : ℝ) : Prop :=
  β = 0 ∨ N = 1

end DGGRegistration

end ThetLogos
