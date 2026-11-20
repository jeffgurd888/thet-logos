import Mathlib.Tactic
import ThetLogos.ThermalLiftFallPin

/-!
# ThetLogos.ThermalLiftSurface — THERMAL LIFT, brick ST-1

**Surface tension form.** The interface energy of the
thermal potential across a region's cut — frozen as
`cutEnergy` in `ThermalLiftPin` (LIFT-0a) — is the
conductance-weighted sum of the composite's *field* over
the same cut (`cutFieldForm_holds`): the interface energy
is the field, integrated over the boundary. The form's
elementary faces: blind to constant shifts of the
potential; zero on the empty cut and on the whole seat
(no boundary, no interface); reversing the region
reverses the sign (`cutFlipForm_holds` — an interface
has two sides and one tension, read in opposite
directions); and nonnegative wherever the potential does
not decrease across the cut outward — the interface
energy is paid exactly where the gradient points out of
the region.

**What this is and is not.** This is the seat form of an
interface energy of the thermal state on a region's
boundary: an interface is where a gradient concentrates,
and the cut energy is that concentration, summed. It is
NOT a Young–Laplace law (no curvature object exists on
this seat — FRONTIER, flagged on the pin's face), not a
minimization theorem (no variational statement is made),
and not a gravity statement (K-GR-LAUNDER stands;
surface tension as a gravity *identity* was graded
NO-GO in the 2026-11-17 electrogravitic investigation —
this brick is a seat mechanism, a different question,
and it answers only the seat question).

**Dial 2 = 0 under every outcome. NO CLAIM; dials 0/4.**
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- **The interface energy is the field over the cut.**
The cut energy of the profiled thermal potential is the
conductance-weighted sum of the profiled thermal field
over the same cut — definitional, because the field *is*
the potential's edge drop (the channel's hinge, read at
the profiled source). -/
theorem cutEnergy_profThermalPotential (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (β : V → ℝ)
    (E : V → ℝ) (S : Finset V) :
    cutEnergy w (profThermalPotential w hw hw0 hpos β E) S
      = ∑ i ∈ S, ∑ j ∈ Sᶜ, w i j
        * profThermalField w hw hw0 hpos β E i j :=
  rfl

/-- **ST-1, the field form (frozen target, proved).** -/
theorem cutFieldForm_holds (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (β : V → ℝ)
    (E : V → ℝ) (S : Finset V) :
    CutFieldForm w hw hw0 hpos β E S :=
  cutEnergy_profThermalPotential w hw hw0 hpos β E S

/-- **Blind to constant shifts.** Shifting the potential
by a constant changes no drop, hence no interface
energy — the interface reads the contrast, as every
channel of this line does (K-LIFT-BLIND's face here). -/
theorem cutEnergy_add_const (w : V → V → ℝ) (φ : V → ℝ)
    (c : ℝ) (S : Finset V) :
    cutEnergy w (fun i => φ i + c) S = cutEnergy w φ S := by
  unfold cutEnergy dropVec
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  show w i j * ((φ j + c) - (φ i + c)) = w i j * (φ j - φ i)
  ring

/-- **No region, no interface.** The empty cut has zero
interface energy. -/
theorem cutEnergy_empty (w : V → V → ℝ) (φ : V → ℝ) :
    cutEnergy w φ ∅ = 0 := by
  simp [cutEnergy]

/-- **No boundary, no interface.** The whole seat has no
cut — its complement is empty — so its interface energy
is zero. -/
theorem cutEnergy_univ (w : V → V → ℝ) (φ : V → ℝ) :
    cutEnergy w φ Finset.univ = 0 := by
  unfold cutEnergy
  simp [Finset.compl_univ]

/-- **The flip.** Reversing a region reverses its
interface energy: with symmetric conductances, the cut
energy of the complement is the negative of the cut
energy of the region — the two sides of one interface,
read in opposite directions. -/
theorem cutEnergy_compl (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (φ : V → ℝ) (S : Finset V) :
    cutEnergy w φ Sᶜ = - cutEnergy w φ S := by
  have hswap : (∑ i ∈ Sᶜ, ∑ j ∈ S, w i j * dropVec φ i j)
      = ∑ j ∈ S, ∑ i ∈ Sᶜ, w i j * dropVec φ i j :=
    Finset.sum_comm
  have hsym : (∑ j ∈ S, ∑ i ∈ Sᶜ, w i j * dropVec φ i j)
      = ∑ j ∈ S, ∑ i ∈ Sᶜ, w j i * dropVec φ i j := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hw b a]
  have hneg : (∑ j ∈ S, ∑ i ∈ Sᶜ, w j i * dropVec φ i j)
      = - ∑ j ∈ S, ∑ i ∈ Sᶜ, w j i * dropVec φ j i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [dropVec, dropVec]
    ring
  unfold cutEnergy
  rw [compl_compl, hswap, hsym, hneg]

/-- **ST-1, the flip form (frozen target, proved).** -/
theorem cutFlipForm_holds (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (φ : V → ℝ) (S : Finset V) :
    CutFlipForm w hw φ S :=
  cutEnergy_compl w hw φ S

/-- **The outward face.** Wherever the potential does
not decrease across the cut outward — every site outside
sits at or above every site inside — the interface
energy is nonnegative: the interface is paid exactly
where the gradient points out of the region. -/
theorem cutEnergy_nonneg_of_le_across (w : V → V → ℝ)
    (hw0 : ∀ i j, 0 ≤ w i j) (φ : V → ℝ) (S : Finset V)
    (h : ∀ i ∈ S, ∀ j ∈ Sᶜ, φ i ≤ φ j) :
    0 ≤ cutEnergy w φ S := by
  unfold cutEnergy dropVec
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (hw0 i j) (sub_nonneg.mpr (h i hi j hj))

end ThetLogos
