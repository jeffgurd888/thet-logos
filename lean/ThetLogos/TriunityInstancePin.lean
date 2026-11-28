import Mathlib.Tactic
import ThetLogos.TriunityFacesPin
import ThetLogos.ThreeRoutesBrick1

/-!
# ThetLogos.TriunityInstancePin — the capstone has an instance (T5 charter; NO CLAIM)

Working label only — naming is Zero's hand. The Triunity
Capstone line's first charge, from `TriunityFacesPin`'s
face: exhibit ONE concrete `CrystalMatrix` — concrete
charge, exchange, core, landscape, temperature, jump
relation, and grain, with the grain's separation CHECKED
— or K-CAPSTONE-EMPTY fires (its falsity form:
`routeSeparated` unsatisfiable on `Fin 3`).

## The exhibit

- **Seat** (`instanceSeat`): the `Fin 3` cycle seat with
  charge `![1, -1, 2]`, distant component `{2}`, and
  exchange `![2, 1, 0]` (0 and 2 swapped, 1 fixed).
- **Pearl** (`instancePearl`): the DERIVED sphere seat
  over it — `RouteSphereSeat.ofGibbs` from Three Routes
  Brick 1, core `{0, 1}` (the shell is its complement
  `{2}`, which is the seat's distant component, as
  `routeSeparated` demands), landscape `![0, 0, 0]`,
  inverse temperature `1`. The jump relation is the
  derived one, not bare data: this matrix's pearl
  carries Brick 1's discharge in its field.
- **Grain** (`instanceGrain`): `![1, 0, -1/2]`. Its
  separation is checked below, not assumed: the charge
  on the distant component is `(-1/2) * 2 = -1 ≠ 0`; the
  charge on the complement is `1 * 1 + 0 * (-1) = 1`;
  the two cancel across the pair. The distant-heat
  witness is `![0, 0, 1]`: supported on `{2}` alone,
  carrying charge `2 ≠ 0`.
- **Matrix** (`instanceMatrix`): the pearl, its own
  geometry (`geomOf` of its seat, coherence by `rfl`),
  and the grain with its checked separation.

`instanceDischarges` closes the brick: `capstoneHasInstance`
— the proposition Brick 3 of the capstone stated and
deliberately did not exhibit — is TRUE. **K-CAPSTONE-EMPTY
does not fire**: the pearl has a grain on the smallest
seat. What this does NOT do: it proves none of the
capstone's three faces and none of the bridge — the
instance exists; whether the faces hold OF it is the
later bricks' question, exactly as the capstone's face
registers.

## Walls named on the face

- **K-SHADOW-IDENTITY** (standing tension, unsoftened):
  shadows hold for every weighting and pick out no
  gravity object. This line does not dissolve it and
  claims no gravity object.
- Per Zero's register (2026-11-24): a completed finite
  theorem is not a continuum theorem. T5 charter,
  NO CLAIM; dials 0/4.
-/

namespace ThetLogos

/-- **The instance seat.** A concrete cycle seat on the
`Fin 3` ring: charge `![1, -1, 2]`, distant component
`{2}`, exchange swapping 0 and 2 and fixing 1. -/
def instanceSeat : CycleSeat (Fin 3) :=
  { charge := ![1, -1, 2], distant := {2}, exch := ![2, 1, 0] }

/-- **The instance pearl.** The derived sphere seat over
`instanceSeat`: core `{0, 1}`, flat landscape, inverse
temperature `1`, and — by `RouteSphereSeat.ofGibbs` —
the DERIVED jump relation of Three Routes Brick 1 in
the owed field. -/
def instancePearl : RouteSphereSeat :=
  RouteSphereSeat.ofGibbs instanceSeat {0, 1} ![0, 0, 0] 1

/-- **The grain.** The configuration at the pearl's
centre: weight `1` at position 0, `0` at position 1,
`-1/2` at position 2 — chosen so its charge splits
across the pair (see the checked proof below). -/
noncomputable def instanceGrain : Fin 3 → ℝ :=
  ![1, 0, -1/2]

/-- **The grain's separation, CHECKED.** All three
clauses of `routeSeparated` on the instance pearl, by
computation: the distant component is the core's
complement; the grain's charge is split across the
pair (distant charge `-1 ≠ 0`, complement charge `1`,
sum `0`); and a distant-heat datum exists (the witness
`![0, 0, 1]`, supported on the distant component alone
with charge `2 ≠ 0`). -/
theorem instanceGrain_separated :
    routeSeparated instancePearl instanceGrain := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · show cycleChargeSplit instanceSeat instanceGrain
    constructor
    · simp [cycleChargeOn, instanceSeat, instanceGrain]
    · have hcompl : ({2} : Finset (Fin 3))ᶜ = {0, 1} := by decide
      simp [cycleChargeOn, instanceSeat, instanceGrain, hcompl]
  · show ∃ h : Fin 3 → ℝ, cycleDistantHeat instanceSeat h
    refine ⟨![0, 0, 1], ?_, ?_⟩
    · intro i hi
      fin_cases i
      · simp
      · simp
      · simp [instanceSeat] at hi
    · simp [nedZeroCharge, nedCharge, instanceSeat, Fin.sum_univ_three]

/-- **The instance matrix.** One concrete
`CrystalMatrix`: the derived pearl, its own geometry
carried with `rfl` coherence, and the grain with its
checked separation. -/
noncomputable def instanceMatrix : CrystalMatrix :=
  { pearl := instancePearl,
    geometry := geomOf instancePearl.cycle,
    geometry_is := rfl,
    grain := instanceGrain,
    grain_separated := instanceGrain_separated }

/-- **K-CAPSTONE-EMPTY does not fire.** The proposition
the capstone's Brick 3 stated without exhibiting —
`capstoneHasInstance`, `Nonempty CrystalMatrix` — is
discharged by the concrete matrix above. The pearl has
a grain on the smallest seat. -/
theorem instanceDischarges : capstoneHasInstance :=
  ⟨instanceMatrix⟩

end ThetLogos
