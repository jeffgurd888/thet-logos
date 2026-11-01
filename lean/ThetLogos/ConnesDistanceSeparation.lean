import Mathlib.Tactic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import ThetLogos.ConnesDistancePost
import ThetLogos.ConnesDistanceCycle

open scoped Matrix.Norms.L2Operator ENNReal

namespace ThetLogos

/-!
# ThetLogos.ConnesDistanceSeparation - GR-DIST-3: the separation
decision at the Fin 4 cycle seat

**Working label only.** The module name
`ConnesDistanceSeparation` and the line name GR-DIST are
working labels; Jeff names.

**Program ceiling, on the face.** This module decides a shadow
predicate at one named seat - vocabulary. It seats NO gravity
object; Dial 2 = 0. The distance decided here is a distance
between point states of the Fin 4 diagonal algebra; it is never
a spatial separation and is never spent as a spatial `r`
(K-GR-SMUG instance (i)).

## The decision, and its coarseness, on the face

The pin `ConnesDistancePost` registered the predicate
`DistSeparates` for the Fin 4 cycle seat and the corpus's named
sector pair `chargePumpSectorA = {0, 1}` /
`chargePumpSectorB = {2, 3}`, with the seat operator left as
the predicate's argument. DIST-2 built that seat:
`cycleSeat : ConnesDistanceSeat (Fin 4)` with operator
`cycleDirac`, and proved the exact value
`connesDist cycleDirac i j = if i = j then 0 else 1`
(`connesDist_cycleDirac_eq`).

**Decision: TRUE in the registered form.**
`distSeparates_cycleSeat : DistSeparates cycleDirac` holds:
on every cross pair the distance is positive and finite, in
both cross directions, exactly as the pin states them.

**The coarseness, verbatim-grade.** The decision holds with
every cross-pair distance exactly `1`
(`connesDist_cycleDirac_cross_eq_one` below): the registered
form is satisfied by the discrete metric and does NOT
distinguish cyclic distance `1` from `2` - the adjacent cross
pair `(1, 2)` and the opposite cross pair `(0, 2)` both carry
distance exactly `1`. The Item-7-shadow question at THIS seat
is decided TRUE in its registered form, and the registered form
is weak. Selling this as a fine-grained distance separation
would be K-GR-LAUNDER - void on sight.

**Scope fence.** This decision closes the Item-7-shadow at
THIS seat only - the Fin 4 cycle seat with operator
`cycleDirac`. The composite seat (the R^448 factor space) stays
a separate future entry; nothing here touches it or claims it.
-/

/-- **Cross pairs are distinct.** A point of the low sector
`chargePumpSectorA = {0, 1}` is never a point of the high
sector `chargePumpSectorB = {2, 3}`. -/
theorem ne_of_mem_sectorA_mem_sectorB {i j : Fin 4}
    (hi : i ∈ chargePumpSectorA) (hj : j ∈ chargePumpSectorB) :
    i ≠ j := by
  simp only [chargePumpSectorA, Finset.mem_insert, Finset.mem_singleton]
    at hi
  simp only [chargePumpSectorB, Finset.mem_insert, Finset.mem_singleton]
    at hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> decide

/-- **Every cross-pair distance at the cycle seat is exactly
`1`.** Both cross directions: low-to-high and high-to-low.
This is the coarseness on the face: the value does not
distinguish cyclic distance `1` (e.g. the pair `1, 2`) from
cyclic distance `2` (e.g. the pair `0, 2`). -/
theorem connesDist_cycleDirac_cross_eq_one :
    (∀ i ∈ chargePumpSectorA, ∀ j ∈ chargePumpSectorB,
      connesDist cycleDirac i j = 1) ∧
    (∀ j ∈ chargePumpSectorB, ∀ i ∈ chargePumpSectorA,
      connesDist cycleDirac i j = 1) := by
  constructor
  · intro i hi j hj
    rw [connesDist_cycleDirac_eq, if_neg (ne_of_mem_sectorA_mem_sectorB hi hj)]
  · intro j hj i hi
    rw [connesDist_cycleDirac_eq,
      if_neg (ne_of_mem_sectorA_mem_sectorB hi hj)]

/-- **THE DECISION (GR-DIST-3).** At the Fin 4 cycle seat -
operator `cycleDirac`, the operator of DIST-2's `cycleSeat` -
the registered predicate `DistSeparates` of the pin
`ConnesDistancePost` HOLDS for the named sector pair
`chargePumpSectorA = {0, 1}` / `chargePumpSectorB = {2, 3}`:
on every cross pair the Connes distance is positive and
finite, in both cross directions, in the pin's exact
registered form. The value on every such pair is exactly `1`
(see `connesDist_cycleDirac_cross_eq_one`): the registered
form is satisfied by the discrete metric and does not
distinguish cyclic distance `1` from `2`. -/
theorem distSeparates_cycleSeat : DistSeparates cycleDirac := by
  obtain ⟨hAB, hBA⟩ := connesDist_cycleDirac_cross_eq_one
  constructor
  · intro i hi j hj
    rw [hAB i hi j hj]
    exact ⟨zero_lt_one, ENNReal.one_lt_top⟩
  · intro j hj i hi
    rw [hBA j hj i hi]
    exact ⟨zero_lt_one, ENNReal.one_lt_top⟩

end ThetLogos
