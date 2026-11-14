/-
# AdmissibilityPin — the admissibility core of an
admissible grid-transfer continuation method, pinned
at one finite seat

**Scoping-grade pin. NO CLAIM. Dial-ineligible.**
Commissioned by Zero (2026-11-12): "can we advance it" →
scope on paper first → "build it". Scope of record:
`philipbar-admissibility-rung-scope-2026-11-12.md`.
Object: Brad M. Philipbar, *Admissible Coarse-to-Fine
Continuation of Reacting Hypersonic Flow on Native
Hexahedral Grids* — prepublication abstract, LinkedIn
post, published 2026-10-06.

## What this pin is, and is not

The abstract's load-bearing word is **admissibility**:
a developed reacting-air solution is transferred to a
fresh grid of ≈ 42 million hexahedra, and the method's
promise is that the transfer never produces an illegal
state — native recovery "admits every receiver node".
This pin formalizes that promise's GENERIC algebraic
skeleton at a finite seat: a finite node set, a
per-node state of physical quantities, an admissibility
predicate, and a transfer operator that interpolates
where an inverse map locates a receiver node and keeps
a prior accepted state where it does not. The statement
forms R1/R2/R3 are pinned below as `Prop`-valued
definitions; the theorem bricks that discharge them
follow in this same module.

This pin is NOT Philipbar's method, NOT his code, NOT
his data, and NOT a theorem about hypersonic flow, the
continuum, any PDE, or convergence (his own diagnostics
mark his transferred state as still relaxing). It
advances no dial and closes no part of any official
statement. NO CLAIM; dials 0/4.

## Fidelity — the gaps stay on the face

- **FIDELITY GAP #1.** The abstract never states
  Philipbar's exact admissibility predicate. The
  predicate pinned here — positivity of the
  density-like scalars and the two thermal energies,
  species mass fractions on the simplex, turbulence
  scalars nonnegative — is OUR generic form, chosen
  because it is the convex shape the abstract's
  language supports. His true predicate may couple
  species and energies nonlinearly through the
  equation of state.
- **FIDELITY GAP #2.** The exact interpolation and
  acceptance formulas are not in the abstract. The
  transfer pinned here is the generic skeleton:
  convex combination where located (nonnegative
  weights summing to 1 — the form density-weighted
  interpolation with positive densities normalizes
  to), prior accepted state where not.

Two pre-registered kills stay armed; both concern
fidelity to Philipbar's actual definitions, never this
skeleton's internal truth:

- **K-ADM-CONVEX** fires if his actual admissibility
  set is non-convex; then preservation, if true, lives
  in his recovery step, not the interpolation, and any
  fidelity rung re-pins around recovery.
- **K-ADM-FIDELITY** fires if his definitions cannot
  be obtained; then this skeleton stays generic
  forever, is never described as his method, and its
  register entry carries "correspondence unexamined"
  permanently.

As of this pin, correspondence to Philipbar's own
definitions is UNEXAMINED. This skeleton is ours.

## Use — take it and run it

This module is written to be downloaded and used
directly, by Philipbar first and by anyone else on
the same terms. It is self-contained within the
repo: its imports are Mathlib modules only — the
narrow `Mathlib.Tactic` root, the corpus's most
common import, chosen because this environment's
full-library import load outruns its reboot
cadence; the definitions below use nothing beyond
it — it depends on no other ThetLogos module, and
a fresh clone builds it alone.

- **Environment (the repo's pins, as carried):**
  Lean toolchain `leanprover/lean4:v4.35.0-rc3`
  (`lean-toolchain`); Mathlib at revision
  `516d31250e96c4e8e76888c3d8e2e43a9642b9ee`
  (`lean/lake-manifest.json`).
- **Build (from the repo's `lean/` directory):**
  `lake exe cache get` once, then
  `lake build ThetLogos.AdmissibilityPin`
  builds this module alone.
- **Download:** the file lives at
  `lean/ThetLogos/AdmissibilityPin.lean` in the
  public repo `github.com/jeffgurd888/thet-logos`
  (clone the repo, or take the raw file). The
  corpus data set is free to clone and share
  always, as a starting data set, for free (Zero's
  standing policy, 2026-11-01) — this module
  included, no permission needed and none to ask.

## The R1 fence

R1 (roundtrip identity) is the algebraic skeleton
under the abstract's roundtrip errors
(2.08 × 10⁻¹⁴, 1.44 × 10⁻¹⁴). Those numbers are
floating-point evidence about his implementation;
they are NOT the theorem. The theorem shape is:
exact inverse maps in, identity out — over the
reals, where no roundoff exists.
-/

import Mathlib.Tactic

namespace ThetLogos

namespace AdmissibilityPin

/-- A per-node physical state at the finite seat:
a density-like scalar, two thermal energies, seven
species mass fractions, and two turbulence scalars.
Abstract reals throughout — the seat is a shape, not
a simulation. -/
@[ext]
structure NodeState where
  /-- Density-like positive scalar. -/
  density : ℝ
  /-- First thermal energy. -/
  energyOne : ℝ
  /-- Second thermal energy. -/
  energyTwo : ℝ
  /-- Species mass fractions, one per species
  (seven at the source seat). -/
  species : Fin 7 → ℝ
  /-- First turbulence scalar (nonnegative when
  admissible). -/
  turbKin : ℝ
  /-- Second turbulence scalar (nonnegative when
  admissible). -/
  turbDiss : ℝ

/-- Admissibility at the finite seat, GENERIC form
(see FIDELITY GAP #1 in the header): the positive
quantities are strictly positive, species fractions
lie in `[0, 1]` and sum to `1` (the simplex), and the
turbulence scalars are nonnegative. -/
def Admissible (s : NodeState) : Prop :=
  0 < s.density ∧ 0 < s.energyOne ∧ 0 < s.energyTwo ∧
    (∀ i, 0 ≤ s.species i) ∧ (∀ i, s.species i ≤ 1) ∧
    (∑ i, s.species i) = 1 ∧ 0 ≤ s.turbKin ∧ 0 ≤ s.turbDiss

/-- Convex weights over a finite index type:
every weight nonnegative, weights summing to `1`. -/
def ConvexWeights {ι : Type*} [Fintype ι] (w : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1

/-- The fieldwise convex combination of a family of
states: every field of the combination is the
weighted sum of that field. -/
def convexMix {ι : Type*} [Fintype ι] (w : ι → ℝ) (s : ι → NodeState) :
    NodeState where
  density := ∑ i, w i * (s i).density
  energyOne := ∑ i, w i * (s i).energyOne
  energyTwo := ∑ i, w i * (s i).energyTwo
  species := fun j => ∑ i, w i * (s i).species j
  turbKin := ∑ i, w i * (s i).turbKin
  turbDiss := ∑ i, w i * (s i).turbDiss

/-- The delta weight concentrated at a single index:
`1` there, `0` elsewhere. The weight form of an exact
point location. -/
def deltaWeight {Node : Type*} [DecidableEq Node] (m : Node) :
    Node → ℝ :=
  fun d => if d = m then 1 else 0

/-- The transfer operator, GENERIC form (see
FIDELITY GAP #2 in the header): at a located receiver
node, the convex combination of the donor field under
that node's weights; at an unlocated node, the prior
accepted state for that node. -/
def Transfer {Node Donor : Type*} [Fintype Donor] (located : Node → Prop)
    [DecidablePred located] (w : Node → Donor → ℝ)
    (donor : Donor → NodeState) (accepted : Node → NodeState) :
    Node → NodeState :=
  fun n => if located n then convexMix (w n) donor else accepted n

/-- **R3 statement form (pinned, not asserted):**
fallback soundness. If every receiver's weights are
convex, every donor state is admissible, and every
accepted state is admissible, then the transfer is
admissible at every receiver node — the exact shape
of the abstract's "admits every receiver node". -/
def R3Form {Node Donor : Type*} [Fintype Donor] (located : Node → Prop)
    [DecidablePred located] (w : Node → Donor → ℝ)
    (donor : Donor → NodeState) (accepted : Node → NodeState) : Prop :=
  (∀ n, ConvexWeights (w n)) → (∀ d, Admissible (donor d)) →
    (∀ n, Admissible (accepted n)) →
    ∀ n, Admissible (Transfer located w donor accepted n)

/-- **R1 statement form (pinned, not asserted):**
roundtrip identity. Both grids are modelled over one
finite node type — the maps carry the distinction.
At a donor node `d` whose forward image is located,
if the inverse map undoes the forward map at `d`,
then transferring with delta weights (each receiver
takes its located donor's state outright) and
returning with delta weights reproduces `donor d`
exactly. The abstract's 10⁻¹⁴ roundtrip errors are
the floating-point shadow of this identity; see the
R1 fence in the header. -/
def R1Form {Node : Type*} [Fintype Node] [DecidableEq Node]
    (located : Node → Prop) (invMap fwdMap : Node → Node)
    (donor : Node → NodeState) : Prop :=
  ∀ d, located (fwdMap d) → invMap (fwdMap d) = d →
    convexMix (deltaWeight (fwdMap d))
      (fun r => convexMix (deltaWeight (invMap r)) donor) = donor d

/-- **R2 statement form (pinned, not asserted):**
preservation under convex interpolation. A convex
combination of admissible states is admissible,
because strict positivity and the simplex are convex
conditions. The heart of the rung — and the form
K-ADM-CONVEX is armed against, at the level of
fidelity to the source method. -/
def R2Form {ι : Type*} [Fintype ι] (w : ι → ℝ) (s : ι → NodeState) :
    Prop :=
  ConvexWeights w → (∀ i, Admissible (s i)) → Admissible (convexMix w s)

/-! ## Brick R3 — fallback soundness, proved

The proof needs the convexity core first: a convex
combination of admissible states is admissible. That
lemma is the mathematical content of R2 as well;
it is banked here because R3's located branch
depends on it, and the R2 brick discharges `R2Form`
from it. -/

/-- **Convexity core:** a convex combination of
admissible states is admissible. Strict positivity
of the mixed densities and energies comes from the
weights summing to `1`: some weight is positive,
its term is strictly positive, and no term is
negative. The species fractions stay on the
simplex: nonnegativity and the sum are immediate,
and the upper bound uses each fraction `≤ 1`
against the weights summing to `1`. -/
theorem convexMix_admissible {ι : Type*} [Fintype ι] {w : ι → ℝ}
    {s : ι → NodeState} (hw : ConvexWeights w)
    (hs : ∀ i, Admissible (s i)) : Admissible (convexMix w s) := by
  obtain ⟨hw0, hw1⟩ := hw
  have hex : ∃ i, 0 < w i := by
    by_contra h
    push_neg at h
    have hsum : ∑ i, w i = 0 :=
      Finset.sum_eq_zero (fun i _ => le_antisymm (h i) (hw0 i))
    rw [hsum] at hw1
    exact zero_ne_one hw1
  obtain ⟨i₀, hi₀⟩ := hex
  have hpos : ∀ g : NodeState → ℝ, (∀ i, 0 < g (s i)) →
      0 < ∑ i, w i * g (s i) := by
    intro g hg
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (hw0 i) (le_of_lt (hg i))
    · exact ⟨i₀, Finset.mem_univ i₀, mul_pos hi₀ (hg i₀)⟩
  unfold Admissible
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hpos _ (fun i => (hs i).1)
  · exact hpos _ (fun i => (hs i).2.1)
  · exact hpos _ (fun i => (hs i).2.2.1)
  · intro j
    show 0 ≤ ∑ i, w i * (s i).species j
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hw0 i) ((hs i).2.2.2.1 j)
  · intro j
    show (∑ i, w i * (s i).species j) ≤ 1
    calc (∑ i, w i * (s i).species j) ≤ ∑ i, w i * 1 := by
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_of_nonneg_left ((hs i).2.2.2.2.1 j) (hw0 i)
      _ = 1 := by simp [hw1]
  · show (∑ j, ∑ i, w i * (s i).species j) = 1
    rw [Finset.sum_comm]
    have hterm : ∀ i : ι, (∑ j, w i * (s i).species j) = w i := by
      intro i
      rw [← Finset.mul_sum, (hs i).2.2.2.2.2.1, mul_one]
    trans (∑ i, w i)
    · exact Finset.sum_congr rfl (fun i _ => hterm i)
    · exact hw1
  · show 0 ≤ ∑ i, w i * (s i).turbKin
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hw0 i) (hs i).2.2.2.2.2.2.1
  · show 0 ≤ ∑ i, w i * (s i).turbDiss
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hw0 i) (hs i).2.2.2.2.2.2.2

/-- **R3 holds (fallback soundness):** with convex
weights at every receiver, admissible donors, and
admissible accepted states, the transfer is
admissible at every receiver node — by the
convexity core on located nodes, and by hypothesis
on the rest. This is the form's entire content; no
convergence or accuracy statement is made or
implied. -/
theorem r3_holds {Node Donor : Type*} [Fintype Donor]
    (located : Node → Prop) [DecidablePred located]
    (w : Node → Donor → ℝ) (donor : Donor → NodeState)
    (accepted : Node → NodeState) : R3Form located w donor accepted := by
  intro hw hdonor haccepted n
  show Admissible (if located n then convexMix (w n) donor else accepted n)
  split_ifs with h
  · exact convexMix_admissible (hw n) hdonor
  · exact haccepted n

/-! ## Brick R1 — roundtrip identity, proved -/

/-- **Delta weights pick their node:** mixing with
the weights that are `1` at `m` and `0` elsewhere
returns the state at `m` itself, field by field.
This is the exact-arithmetic content of a
grid-to-grid roundtrip whose return interpolation
is the identity at the node. -/
theorem convexMix_deltaWeight {Node : Type*} [Fintype Node]
    [DecidableEq Node] (m : Node) (s : Node → NodeState) :
    convexMix (deltaWeight m) s = s m := by
  have hsum : ∀ f : Node → ℝ, (∑ i, deltaWeight m i * f i) = f m := by
    intro f
    have hterm : ∀ i : Node, deltaWeight m i * f i =
        if i = m then f i else 0 := by
      intro i
      unfold deltaWeight
      by_cases h : i = m
      · simp only [h, eq_self_iff_true, if_true, one_mul]
      · simp only [h, if_false, zero_mul]
    calc (∑ i, deltaWeight m i * f i) = ∑ i, (if i = m then f i else 0) :=
            Finset.sum_congr rfl (fun i _ => hterm i)
      _ = f m := by rw [Finset.sum_ite_eq']; simp
  apply NodeState.ext
  · exact hsum (fun i => (s i).density)
  · exact hsum (fun i => (s i).energyOne)
  · exact hsum (fun i => (s i).energyTwo)
  · funext j
    exact hsum (fun i => (s i).species j)
  · exact hsum (fun i => (s i).turbKin)
  · exact hsum (fun i => (s i).turbDiss)

/-- **R1 holds (roundtrip identity):** at a donor
node whose forward image is located, if the inverse
map undoes the forward map there, then transferring
out and back with delta weights reproduces the
donor state exactly. The pinned form's locatedness
hypothesis is carried for fidelity to the method's
shape; the identity itself uses only the
inverse-map hypothesis and the delta lemma. The
abstract's 10⁻¹⁴ roundtrip errors are this
identity's floating-point shadow — evidence about
an implementation, not this theorem. -/
theorem r1_holds {Node : Type*} [Fintype Node] [DecidableEq Node]
    (located : Node → Prop) (invMap fwdMap : Node → Node)
    (donor : Node → NodeState) : R1Form located invMap fwdMap donor := by
  intro d _ hinv
  calc convexMix (deltaWeight (fwdMap d))
        (fun r => convexMix (deltaWeight (invMap r)) donor)
      = convexMix (deltaWeight (invMap (fwdMap d))) donor :=
        convexMix_deltaWeight _ _
    _ = convexMix (deltaWeight d) donor := by rw [hinv]
    _ = donor d := convexMix_deltaWeight _ _

/-! ## Brick R2 — preservation under convex interpolation, proved -/

/-- **R2 holds (preservation under convex
interpolation):** a convex combination of admissible
states is admissible. The mathematical content is
the convexity core `convexMix_admissible`, banked
with the R3 brick because R3's located branch
depends on it; this theorem discharges the pinned
`R2Form` from it, so the rung's three forms are
each closed by a named theorem. -/
theorem r2_holds {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (s : ι → NodeState) : R2Form w s := by
  intro hw hs
  exact convexMix_admissible hw hs

end AdmissibilityPin

end ThetLogos
