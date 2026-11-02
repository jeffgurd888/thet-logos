import Mathlib.Tactic
import ThetLogos.WaveFamilyPost
import ThetLogos.LayerCubeDistance

namespace ThetLogos

/-!
# ThetLogos.WavePathShadowDecision - GR-PROP-4: the path-shadow decided at a small seat

**Working label only.** The module name
`WavePathShadowDecision` and the line name GR-PROP are
working labels; Jeff names.

**Status: GR-PROP-4 landing brick (optional, registered).
NO CLAIM. Dial 2 = 0 under every outcome of this line,
including total success. No gravity object is defined,
constructed, or asserted to exist.**

## GRAVITY-VOCABULARY CEILING (binding, on the face)

This brick is graph bookkeeping: shortest cube-graph paths
under a named perturbation, decided at a named seat. No
continuous path, no angle, no deflection law. The word
"bending" may appear only inside this fence, as a fenced
word for a change in the graph's shortest-path length, and
for nothing else. **It seats NO gravity object; Dial 2 = 0
under every outcome.** Kills armed for the line:
K-GR-SMUG / K-GR-VAC / K-GR-LAUNDER / K-GR-STAB
(pre-registered in the vocabulary scoping).

## The candidate seat, named in advance (first write)

- Seat size: `N = 2` (the layer cube has 8 sites).
- Named sites: `seatX` = the zero layer site, and
  `seatY` = the zero layer site shifted in spatial
  direction `1` (`layerShift 1`). The pair `(seatX, seatY)`
  is an edge of `cubeGraph 2`.
- Named site-perturbation (`seatPerturbation`, an owned
  definition below): the weight of the single named edge
  `{seatX, seatY}` - the direction-`1` edge at the zero
  site - is changed from `1` to `2`; every other step keeps
  weight `1`. The increase is exactly the rational number
  `1` (`2 - 1 = 1` in `ℚ`). No other edge is touched.
- Perturbed distance: `pertDist x y`, the shortest-path
  distance produced by that perturbation, defined below as
  the infimum over all cube-graph walks from `x` to `y` of
  the walk's perturbed cost (sum of step weights). It is
  NOT defined by importing any formula's answer
  (K-GR-SMUG instance (iv) discipline, applied to the
  perturbed side): its seat value is proved from the walk
  definition - an exhibited walk for the upper bound, and
  for the lower bound a walk-length estimate (cost at
  least length at least the unperturbed distance) plus
  the length-`1` uniqueness of the direct walk.
- Named stated length: `statedLength = 2`, the perturbed
  distance at the seat, named here in advance.

## Verdict (proved below)

**HOLDS at the named seat, with the perturbation's effect
reported as the arithmetic fact it is:**

- Unperturbed: `geoDist 2 seatX seatY = 1` (GR-GEO-1's
  landed `geoDist`, via its l1 formula).
- Perturbed: `pertDist seatX seatY = 2`.
- Effect: **lengthened by exactly `1`** - the direct edge
  now costs `2`, and every route avoiding it costs at
  least `3` at this pair (in fact every walk from `seatX`
  to `seatY` costs at least `2`).
- The frozen predicate at the stated length:
  `PoseObjBPathShadow 2 pertDist seatX seatY 2` HOLDS
  (`2 = pertDist seatX seatY` and `geoDist 2 seatX seatY
  = 1 ≤ 2`).
- The same predicate at the unperturbed length `1` is
  FALSE, proved below at full rank: its first clause
  would read `1 = pertDist seatX seatY = 2`. The stated
  length was NOT re-chosen after any failure - `2` was
  named in advance above, and the `1`-instance is
  reported as the refutation it is (K-GR-STAB discipline:
  findings reported, not repaired).

## Inputs consumed, and not consumed

- GR-PROP-0 (`WaveFamilyPost.lean`): the frozen predicate
  `PoseObjBPathShadow` and its read-back
  `poseObjBPathShadow_unfold`, imported, never redefined.
  The predicate is NOT repaired, weakened, or
  re-registered.
- GR-GEO-1 (`LayerCubeDistance.lean` +
  `LayerCubeDistancePost.lean`): `geoDist`, its l1
  formula `geoDist_l1_formula`, `coordDistSum`, `cycDist`,
  and the `layerShift` coordinate lemmas, imported, never
  redefined.

## Fences (binding)

- Graph bookkeeping only: a statement about a registered
  finite predicate at a named seat - not gravity, not a
  deflection law, not propagation-as-physics.
- The perturbed distance function and the stated length
  are named/supplied, never existentially quantified
  inside the predicate (K-GR-VAC).
- Ceiling on the face: Dial 2 unmoved by anything in
  this brick; NO CLAIM.
-/

section Seat

/-- **The named seat site `x`**: the zero layer site at
seat size `N = 2` (all coordinates `0`; its time
coordinate has value `0`, as a layer site requires). -/
def seatX : LayerSite 2 :=
  ⟨0, by simp⟩

/-- The seat direction `1` is a spatial (nonzero)
direction in `Fin 4`. -/
theorem seatDir_ne_zero : (1 : Fin 4) ≠ 0 := by decide

/-- **The named seat site `y`**: the zero layer site
shifted in spatial direction `1` - the other endpoint of
the named perturbed edge. -/
def seatY : LayerSite 2 :=
  layerShift (1 : Fin 4) seatDir_ne_zero seatX

/-- The `1`-coordinate of `seatX` is `0`. -/
theorem seatX_coord_one : seatX.1 (1 : Fin 4) = 0 := rfl

/-- The `1`-coordinate of `seatY` is `1`: the shift gains
exactly `1` at its own coordinate (GR-GEO-1's
`layerShift_coord_self`), on top of `seatX`'s `0`. -/
theorem seatY_coord_one : seatY.1 (1 : Fin 4) = 1 := by
  have h := layerShift_coord_self (N := 2) seatDir_ne_zero seatX
  rw [seatX_coord_one] at h
  exact h

/-- The two named seat sites are distinct (their
`1`-coordinates are `0` and `1` in `ZMod 2`). -/
theorem seatX_ne_seatY : seatX ≠ seatY := by
  intro h
  have h1 : seatX.1 (1 : Fin 4) = seatY.1 (1 : Fin 4) :=
    congrFun (congrArg Subtype.val h) (1 : Fin 4)
  rw [seatX_coord_one, seatY_coord_one] at h1
  exact (by decide : (0 : ZMod 2) ≠ 1) h1

/-- The tail of the direction-`1` layer link at `seatX`
is `seatX` itself (the link's base site, by the landed
`linkTail` definition). -/
theorem seat_linkTail :
    linkTail (layerLinkOf seatX (1 : Fin 4) seatDir_ne_zero)
      = seatX :=
  Subtype.ext rfl

/-- The head of the direction-`1` layer link at `seatX`
is `seatY` (the shifted base site, by the landed
`linkHead` definition and the definition of `seatY`). -/
theorem seat_linkHead :
    linkHead (layerLinkOf seatX (1 : Fin 4) seatDir_ne_zero)
      = seatY :=
  rfl

/-- **The named seat pair is an edge of the cube graph**:
`seatY` is the head of the direction-`1` layer link at
`seatX`, by the pin's adjacency construction. -/
theorem seat_adj : (cubeGraph 2).Adj seatX seatY := by
  have hadj := cubeGraph_adj_of_link
    (layerLinkOf seatX (1 : Fin 4) seatDir_ne_zero) (by
      rw [seat_linkTail, seat_linkHead]
      exact seatX_ne_seatY)
  rwa [seat_linkTail, seat_linkHead] at hadj

end Seat

section Unperturbed

/-- **The unperturbed coordinate sum at the seat is `1`**:
over the four coordinates, only coordinate `1`
contributes, and there `cycDist 2 0 1 = 1` (at `N = 2`
both wrap readings of `0` vs `1` are `1`). -/
theorem coordDistSum_seat : coordDistSum 2 seatX seatY = 1 := by
  have hcoord : ∀ i : Fin 4,
      cycDist 2 (seatX.1 i) (seatY.1 i)
        = (if i = 1 then 1 else 0) := by
    intro i
    by_cases hi : i = 1
    · subst hi
      rw [if_pos rfl, seatX_coord_one, seatY_coord_one]
      decide
    · rw [if_neg hi]
      show cycDist 2 (seatX.1 i)
          ((layerShift (1 : Fin 4) seatDir_ne_zero seatX).1 i) = 0
      rw [layerShift_coord_of_ne (N := 2) seatDir_ne_zero seatX hi]
      exact cycDist_self ..
  unfold coordDistSum
  rw [Finset.sum_congr rfl (fun i _ => hcoord i)]
  simp

/-- **The unperturbed distance at the seat.**
`geoDist 2 seatX seatY = 1`, by GR-GEO-1's landed l1
formula (`geoDist_l1_formula`) read through the pin's
unfolding. `geoDist` is imported from GR-GEO-1, never
redefined here. -/
theorem geoDist_seat : geoDist 2 seatX seatY = 1 := by
  have h := (geoDistL1Formula_unfold).mp
    (geoDist_l1_formula 2) seatX seatY
  rw [h]
  exact coordDistSum_seat

end Unperturbed

section Perturbation

/-- **THE NAMED SITE-PERTURBATION (owned definition).**
The step weight of the perturbed cube graph at seat
`N = 2`: a step between the two named sites `seatX` and
`seatY`, in either order - the direction-`1` edge at the
zero site - costs `2`; every other step costs `1`. The
perturbation is exactly this: the named edge's weight is
changed from `1` to `2`, an increase of exactly the
rational number `1`. Nothing else is perturbed. -/
noncomputable def pertStepCost (a b : LayerSite 2) : ℕ :=
  if (a = seatX ∧ b = seatY) ∨ (a = seatY ∧ b = seatX)
    then 2 else 1

/-- Every step costs at least `1` under the perturbation. -/
theorem pertStepCost_ge_one (a b : LayerSite 2) :
    1 ≤ pertStepCost a b := by
  unfold pertStepCost
  split_ifs <;> norm_num

/-- The named edge's step, in the seat direction, costs
exactly `2` under the perturbation. -/
theorem pertStepCost_seat : pertStepCost seatX seatY = 2 := by
  unfold pertStepCost
  rw [if_pos (Or.inl ⟨rfl, rfl⟩)]

/-- **The perturbed cost of a walk**: the sum of the
perturbed step weights along the walk. Defined by
recursion on the walk itself - no shortest-path value is
imported into this definition. -/
noncomputable def pertWalkCost {x y : LayerSite 2} :
    (cubeGraph 2).Walk x y → ℕ
  | .nil => 0
  | .cons (u := a) (v := b) _h p => pertWalkCost p + pertStepCost a b

/-- Read-back: the empty walk costs `0`. -/
theorem pertWalkCost_nil {x : LayerSite 2} :
    pertWalkCost (SimpleGraph.Walk.nil :
      (cubeGraph 2).Walk x x) = 0 :=
  rfl

/-- Read-back: a step costs its perturbed step weight
plus the cost of the rest of the walk. -/
theorem pertWalkCost_cons {x y z : LayerSite 2}
    (h : (cubeGraph 2).Adj x y) (p : (cubeGraph 2).Walk y z) :
    pertWalkCost (SimpleGraph.Walk.cons h p)
      = pertWalkCost p + pertStepCost x y :=
  rfl

/-- **The perturbed distance function `Dp`** supplied to
the frozen predicate: the shortest-path distance under
the named perturbation, defined as the infimum over all
cube-graph walks of the perturbed walk cost. A genuine
infimum over walks (the graph is finite and connected,
so the infimum is attained at the seat); no formula's
answer is imported (K-GR-SMUG instance (iv) discipline
on the perturbed side). -/
noncomputable def pertDist (x y : LayerSite 2) : ℕ :=
  sInf {c : ℕ | ∃ p : (cubeGraph 2).Walk x y, pertWalkCost p = c}

/-- The exhibited direct walk along the named edge costs
exactly `2` under the perturbation. -/
theorem pertWalkCost_direct :
    pertWalkCost (SimpleGraph.Walk.cons seat_adj
      SimpleGraph.Walk.nil) = 2 := by
  rw [pertWalkCost_cons, pertWalkCost_nil, pertStepCost_seat]

/-- **Every walk's perturbed cost is at least its
length** (each step costs at least `1`). -/
theorem pertWalkCost_ge_length {x y : LayerSite 2}
    (p : (cubeGraph 2).Walk x y) :
    p.length ≤ pertWalkCost p := by
  induction p with
  | nil => exact Nat.zero_le _
  | cons h p ih =>
      rw [pertWalkCost_cons, SimpleGraph.Walk.length_cons]
      exact Nat.add_le_add ih (pertStepCost_ge_one _ _)

/-- **Lower bound at the seat.** Every walk from `seatX`
to `seatY` costs at least `2` under the perturbation:
its length is at least the unperturbed distance `1`
(Mathlib's `dist_le` plus `geoDist_seat`) and its cost
is at least its length; and the length-`1` case is the
direct walk itself (two walks of length `≤ 1` between
the same endpoints are equal, Mathlib's
`Walk.eq_of_length_le_one`), whose cost is exactly `2`
because its single step is the named edge. -/
theorem pertWalkCost_seat_ge
    (p : (cubeGraph 2).Walk seatX seatY) :
    2 ≤ pertWalkCost p := by
  have hlen := pertWalkCost_ge_length p
  have hdist : (1 : ℕ) ≤ p.length := by
    have h : geoDist 2 seatX seatY ≤ p.length :=
      SimpleGraph.dist_le p
    rwa [geoDist_seat] at h
  by_cases h1 : p.length = 1
  · have hpq : p = SimpleGraph.Walk.cons seat_adj
        SimpleGraph.Walk.nil :=
      SimpleGraph.Walk.eq_of_length_le_one (le_of_eq h1)
        (by exact Nat.le_refl _)
    rw [hpq, pertWalkCost_direct]
  · omega

/-- **The perturbed distance at the seat.**
`pertDist seatX seatY = 2`: the exhibited direct walk
gives the upper bound `2` (`Nat.sInf_le`), and the
infimum is itself the cost of some walk
(`Nat.sInf_mem`, the cost set being nonempty), which
the lower bound `pertWalkCost_seat_ge` bounds below
by `2`. -/
theorem pertDist_seat : pertDist seatX seatY = 2 := by
  apply le_antisymm
  · exact Nat.sInf_le
      ⟨SimpleGraph.Walk.cons seat_adj SimpleGraph.Walk.nil,
        pertWalkCost_direct⟩
  · have hmem : pertDist seatX seatY
        ∈ {c : ℕ | ∃ p : (cubeGraph 2).Walk seatX seatY,
            pertWalkCost p = c} :=
      Nat.sInf_mem
        ⟨2, SimpleGraph.Walk.cons seat_adj SimpleGraph.Walk.nil,
          pertWalkCost_direct⟩
    obtain ⟨p, hp⟩ := hmem
    rw [← hp]
    exact pertWalkCost_seat_ge p

end Perturbation

section Decision

/-- **The named stated length, named in advance on this
module's face: `2`** - the perturbed distance at the
seat. It was not re-chosen after any computation: the
predicate at the unperturbed length `1` is refuted
below at full rank and reported, not repaired. -/
def statedLength : ℕ := 2

/-- **Read-back at the seat.** The frozen predicate at
the named seat is exactly its registered statement,
unfolded, by the pin's own `poseObjBPathShadow_unfold`.
The decision below is visibly about the registered
object (`PoseObjBPathShadow` is imported from the
GR-PROP-0 pin, never redefined). -/
theorem pathShadow_seat_readback :
    PoseObjBPathShadow 2 pertDist seatX seatY statedLength
      ↔ statedLength = pertDist seatX seatY
          ∧ geoDist 2 seatX seatY ≤ statedLength :=
  poseObjBPathShadow_unfold _ _ _ _

/-- **The perturbation's effect at the seat, as an
arithmetic fact: LENGTHENED by exactly `1`.**
`pertDist seatX seatY = geoDist 2 seatX seatY + 1`
(`2 = 1 + 1`). Inside the fence on this module's face,
that change in shortest-path length is the only sense
in which any "bending" word could be used here, and no
such word is used for anything else. -/
theorem pertDist_lengthens_seat :
    pertDist seatX seatY = geoDist 2 seatX seatY + 1 := by
  rw [pertDist_seat, geoDist_seat]

/-- **HEADLINE - THE DECISION: HOLDS at the named seat.**
The frozen path-shadow predicate `PoseObjBPathShadow`
holds at the seat named on this module's face: seat
size `N = 2`, sites `seatX` (zero layer site) and
`seatY` (direction-`1` shift of it), perturbed distance
function `pertDist` (the named site-perturbation: the
`{seatX, seatY}` edge's weight `1 → 2`), stated length
`statedLength = 2`, named in advance. Both clauses are
the seat computations above: `2 = pertDist seatX seatY`
and `geoDist 2 seatX seatY = 1 ≤ 2`. Graph bookkeeping
only; NO CLAIM; Dial 2 = 0. -/
theorem pathShadow_holds_at_seat :
    PoseObjBPathShadow 2 pertDist seatX seatY statedLength :=
  ⟨by rw [show statedLength = 2 from rfl, pertDist_seat],
   by rw [geoDist_seat]; show (1 : ℕ) ≤ 2; norm_num⟩

/-- **The same predicate at the unperturbed length `1`
is FALSE at the seat, at full rank.** Its first clause
would read `1 = pertDist seatX seatY`, but the perturbed
distance is `2`. Reported as the refutation it is: the
predicate has teeth, and the stated length was not
re-chosen to hide this (K-GR-STAB discipline). -/
theorem pathShadow_fails_at_unperturbed_length :
    ¬ PoseObjBPathShadow 2 pertDist seatX seatY 1 := by
  intro h
  rw [poseObjBPathShadow_unfold] at h
  obtain ⟨h1, -⟩ := h
  rw [pertDist_seat] at h1
  exact (by norm_num : (1 : ℕ) ≠ 2) h1

end Decision

/-! ## Axiom audit

Headlines checked on exactly
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms geoDist_seat
#print axioms pertDist_seat
#print axioms pertDist_lengthens_seat
#print axioms pathShadow_seat_readback
#print axioms pathShadow_holds_at_seat
#print axioms pathShadow_fails_at_unperturbed_length

end ThetLogos
