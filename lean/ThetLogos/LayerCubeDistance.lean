import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import ThetLogos.LayerCubeDistancePost
import ThetLogos.LatticeReflection

namespace ThetLogos

open Finset

/-!
# ThetLogos.LayerCubeDistance - GR-GEO-1: connectedness + the l1 formula

**Working label only.** The module name `LayerCubeDistance`
and the line name GR-GEO are working labels; Jeff names.

**Status: GR-GEO-1 landing. Both registered targets of the
pin `LayerCubeDistancePost` are discharged at the pin's
generality, for every `N` with `[NeZero N]`, with no
restriction added anywhere: `CubeGraphConnected N` and
`GeoDistL1Formula N`. NO CLAIM. Program ceiling on the face:
finite combinatorics - a graph distance on a finite site
type and its value formula. This module seats NO object;
Dial 2 = 0.**

Governing text: `routeb-general-scratch/scoping-gravity-vocabulary-2026-10-31.md`
(sections 2, 3 and 8), brick GR-GEO-1. The interface is the
landed pin: `cubeGraph`, `geoDist` (the pin's citation of
`SimpleGraph.dist`), `cycDist`, and the two target Props are
used in their registered forms, unrenamed and unextended.

## The DIST-not-GEO fence, from this side (on the face)

`geoDist` lives on SITES of the layer cube. `connesDist`
(GR-DIST) lives on STATES of an algebra. Nothing in this
module is about `connesDist`, and this graph distance says
nothing about states.

## Boundary behaviour, on the face (K-GR-STAB instance (iii))

The l1 formula was watched at the boundary seats named by
the governing memo. It does NOT fail there: the proof below
is uniform in `N`. At `N = 1` the site type is a singleton
and both sides are `0`. At `N = 2` each coordinate wrap
identifies the forward and backward steps, and the cyclic
coordinate distance is `0` or `1` accordingly; the per-edge
step bounds and the toward-step identities below are proved
for all `N` at once, so no seat is excluded and no
quantifier is restricted. The registered targets stand as
registered.

## Proof outline

Adjacency in `cubeGraph N` moves exactly one spatial
coordinate by one cyclic step (read off the landed link
head/tail data). Upper bound: from any site, some neighbour
is one step closer to the target in the l1 sum (move one
differing coordinate along its shorter wrap arc); induction
on the sum exhibits a walk of exactly the sum's length, and
connectedness is the reachability half of that statement.
Lower bound: along any single edge the l1 sum changes by at
most `1` (a one-coordinate cyclic step changes that
coordinate's `cycDist` by at most `1`), so induction on a
walk bounds the sum by every walk's length, in particular
by the shortest walk supplied by Mathlib's distance theory
for a connected graph.
-/

section Aux

variable {N : ℕ} [NeZero N]

/-- Auxiliary notation for the pin target's right-hand side:
the sum over the four coordinates of the cyclic coordinate
distances. This is only a local abbreviation for the sum
registered in `GeoDistL1Formula`; it is not a distance
definition. -/
def coordDistSum (N : ℕ) [NeZero N] (x y : LayerSite N) : ℕ :=
  ∑ i : Fin 4, cycDist N (x.1 i) (y.1 i)

/-- A `ZMod N` element with value `0` is `0`. -/
theorem zmod_eq_zero_of_val_eq_zero (z : ZMod N) (h : z.val = 0) :
    z = 0 := by
  rw [← ZMod.natCast_zmod_val z, h]
  exact Nat.cast_zero

/-- The value of `0` in `ZMod N` is `0`. -/
theorem zmod_val_zero : (0 : ZMod N).val = 0 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  rw [← Nat.cast_zero]
  exact ZMod.val_natCast_of_lt hN

/-- The value of a negation in `ZMod N`. -/
theorem zmod_val_neg (z : ZMod N) :
    (-z).val = if z = 0 then 0 else N - z.val := by
  by_cases hz : z = 0
  · simp [hz, zmod_val_zero]
  · have hd0 : z.val ≠ 0 := by
      intro h
      exact hz (zmod_eq_zero_of_val_eq_zero z h)
    have hdN : z.val < N := ZMod.val_lt z
    have hcast : ((N - z.val : ℕ) : ZMod N) = -z := by
      conv_rhs => rw [← ZMod.natCast_zmod_val z]
      apply eq_neg_of_add_eq_zero_left
      rw [← Nat.cast_add, show N - z.val + z.val = N by omega,
        ZMod.natCast_self]
    rw [if_neg hz, ← hcast]
    exact ZMod.val_natCast_of_lt (by omega)

/-- The cyclic coordinate distance, read off the value of
the forward difference: `cycDist N a b = min d (N - d)` with
`d = (b - a).val`. -/
theorem cycDist_eq_min (a b : ZMod N) :
    cycDist N a b = min (b - a).val (N - (b - a).val) := by
  have hneg : (a - b).val
      = if b - a = 0 then 0 else N - (b - a).val := by
    have h : a - b = -(b - a) := by ring
    rw [h]
    exact zmod_val_neg (b - a)
  unfold cycDist
  by_cases hz : b - a = 0
  · have hab : a - b = 0 := by
      have h2 : b = a := sub_eq_zero.mp hz
      rw [h2]; exact sub_self a
    rw [hz, hab, zmod_val_zero]
    omega
  · rw [if_neg hz] at hneg
    rw [hneg, min_comm]

/-- The value of a difference stepped down by `1`. -/
theorem cycStepValSubOne {z : ZMod N} (hz : z ≠ 0) :
    (z - 1).val = z.val - 1 := by
  have hd0 : z.val ≠ 0 := by
    intro h
    exact hz (zmod_eq_zero_of_val_eq_zero z h)
  have hdN : z.val < N := ZMod.val_lt z
  have hcast : z - 1 = ((z.val - 1 : ℕ) : ZMod N) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ z.val)]
  rw [hcast]
  exact ZMod.val_natCast_of_lt (by omega)

/-- The value of a sum stepped up by `1`. -/
theorem zmod_val_add_one (z : ZMod N) :
    (z + 1).val = if z.val + 1 < N then z.val + 1 else 0 := by
  have hdN : z.val < N := ZMod.val_lt z
  have hcast : z + 1 = ((z.val + 1 : ℕ) : ZMod N) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [← Nat.cast_one, ← Nat.cast_add]
  rw [hcast]
  by_cases h : z.val + 1 < N
  · rw [if_pos h]
    exact ZMod.val_natCast_of_lt h
  · rw [if_neg h]
    have hN' : z.val + 1 = N := by omega
    rw [hN', ZMod.natCast_self]
    exact zmod_val_zero

/-- One cyclic step up changes the cyclic distance by at
most `1`, upper direction. -/
theorem cycDist_add_one_le (a b : ZMod N) :
    cycDist N (a + 1) b ≤ cycDist N a b + 1 := by
  rw [cycDist_eq_min a b, cycDist_eq_min (a + 1) b]
  have hdN : (b - a).val < N := ZMod.val_lt _
  have hstep : b - (a + 1) = (b - a) - 1 := by ring
  rw [hstep]
  by_cases hz : b - a = 0
  · have hd : (b - a).val = 0 := by rw [hz]; exact zmod_val_zero
    have h1 : ((b - a) - 1).val = N - 1 := by
      rw [hz]
      have hcast : (0 : ZMod N) - 1 = ((N - 1 : ℕ) : ZMod N) := by
        have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
        have key : ((N - 1 : ℕ) : ZMod N) + 1 = 0 := by
          have e1 : ((N - 1 : ℕ) : ZMod N) + ((1 : ℕ) : ZMod N)
              = ((N : ℕ) : ZMod N) := by
            rw [← Nat.cast_add, show (N - 1) + 1 = N by omega]
          rw [Nat.cast_one, ZMod.natCast_self] at e1
          exact e1
        rw [zero_sub]
        exact (eq_neg_of_add_eq_zero_left key).symm
      rw [hcast]
      exact ZMod.val_natCast_of_lt (by omega)
    rw [hd, h1]
    omega
  · rw [cycStepValSubOne hz]
    omega

/-- One cyclic step up changes the cyclic distance by at
most `1`, lower direction. -/
theorem cycDist_le_add_one (a b : ZMod N) :
    cycDist N a b ≤ cycDist N (a + 1) b + 1 := by
  rw [cycDist_eq_min a b, cycDist_eq_min (a + 1) b]
  have hdN : (b - a).val < N := ZMod.val_lt _
  have hstep : b - (a + 1) = (b - a) - 1 := by ring
  rw [hstep]
  by_cases hz : b - a = 0
  · have hd : (b - a).val = 0 := by rw [hz]; exact zmod_val_zero
    rw [hd]
    omega
  · rw [cycStepValSubOne hz]
    omega

/-- Stepping up toward the target along the shorter arc
(when the forward reading is the shorter one) drops the
cyclic distance by exactly `1`. -/
theorem cycDist_add_one_eq_of_le {a b : ZMod N}
    (h1 : 1 ≤ (b - a).val) (hle : (b - a).val ≤ (a - b).val) :
    cycDist N (a + 1) b + 1 = cycDist N a b := by
  have hz : b - a ≠ 0 := by
    intro h
    rw [h, zmod_val_zero] at h1
    omega
  have he : (a - b).val = N - (b - a).val := by
    have h : a - b = -(b - a) := by ring
    rw [h, zmod_val_neg, if_neg hz]
  have hdN : (b - a).val < N := ZMod.val_lt _
  rw [cycDist_eq_min a b, cycDist_eq_min (a + 1) b]
  have hstep : b - (a + 1) = (b - a) - 1 := by ring
  rw [hstep, cycStepValSubOne hz]
  omega

/-- Stepping down toward the target along the shorter arc
(when the backward reading is strictly shorter) drops the
cyclic distance by exactly `1`. -/
theorem cycDist_sub_one_eq_of_lt {a b : ZMod N}
    (h1 : 1 ≤ (a - b).val) (hlt : (a - b).val < (b - a).val) :
    cycDist N (a - 1) b + 1 = cycDist N a b := by
  have hz : a - b ≠ 0 := by
    intro h
    rw [h, zmod_val_zero] at h1
    omega
  have he : (a - b).val = N - (b - a).val := by
    have h : b - a = -(a - b) := by ring
    have h2 := zmod_val_neg (a - b)
    rw [if_neg hz] at h2
    have h4 : (b - a).val = N - (a - b).val := by
      rw [h]
      exact h2
    have hlt2 : (a - b).val < N := ZMod.val_lt _
    omega
  have hdN : (b - a).val < N := ZMod.val_lt _
  rw [cycDist_eq_min a b, cycDist_eq_min (a - 1) b]
  have hstep : b - (a - 1) = (b - a) + 1 := by ring
  rw [hstep, zmod_val_add_one]
  by_cases h : (b - a).val + 1 < N
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    omega

/-- The cyclic distance vanishes only at equal points. -/
theorem zmod_eq_of_cycDist_eq_zero {a b : ZMod N}
    (h : cycDist N a b = 0) : a = b := by
  unfold cycDist at h
  have h01 : (a - b).val = 0 ∨ (b - a).val = 0 := by omega
  rcases h01 with h0 | h0
  · exact sub_eq_zero.mp (zmod_eq_zero_of_val_eq_zero _ h0)
  · exact (sub_eq_zero.mp (zmod_eq_zero_of_val_eq_zero _ h0)).symm

end Aux

section Graph

variable {N : ℕ} [NeZero N]

/-- Coordinates of a layer shift: the shifted coordinate
gains `1`, the others are unchanged (read off
`torusShift_apply_coord`). -/
theorem layerShift_coord {ν : Fin 4} (hν : ν ≠ 0) (c : LayerSite N)
    (j : Fin 4) :
    (layerShift ν hν c).1 j
      = (Pi.single ν 1 : Fin 4 → ZMod N) j + c.1 j :=
  torusShift_apply_coord ν j c.1

/-- The shifted coordinate of a layer shift. -/
theorem layerShift_coord_self {ν : Fin 4} (hν : ν ≠ 0)
    (c : LayerSite N) :
    (layerShift ν hν c).1 ν = c.1 ν + 1 := by
  rw [layerShift_coord, Pi.single_eq_same, add_comm]

/-- The unshifted coordinates of a layer shift. -/
theorem layerShift_coord_of_ne {ν : Fin 4} (hν : ν ≠ 0)
    (c : LayerSite N) {j : Fin 4} (hj : j ≠ ν) :
    (layerShift ν hν c).1 j = c.1 j := by
  rw [layerShift_coord, Pi.single_eq_of_ne hj, zero_add]

/-- Adjacency in the cube graph moves exactly one spatial
coordinate by one cyclic step: adjacent sites agree away
from one spatial direction `ν`, and at `ν` one is the other
plus `1`. Read off the landed link head/tail data. -/
theorem adj_coord {x y : LayerSite N}
    (h : (cubeGraph N).Adj x y) :
    ∃ ν : Fin 4, ∃ _ : ν ≠ 0,
      (∀ j : Fin 4, j ≠ ν → x.1 j = y.1 j) ∧
        (y.1 ν = x.1 ν + 1 ∨ x.1 ν = y.1 ν + 1) := by
  obtain ⟨hne, ℓ, hℓ | hℓ⟩ := (cubeGraph_adj x y).mp h
  · have key : ∀ j : Fin 4, (linkHead ℓ).1 j
        = (Pi.single ℓ.1.2 1 : Fin 4 → ZMod N) j + (linkTail ℓ).1 j :=
      fun j => torusShift_apply_coord _ _ _
    have e1 : ∀ j : Fin 4, y.1 j
        = (Pi.single ℓ.1.2 1 : Fin 4 → ZMod N) j + x.1 j := by
      intro j
      rw [← hℓ.2, ← hℓ.1]
      exact key j
    refine ⟨ℓ.1.2, ℓ.2.2, ?_, ?_⟩
    · intro j hj
      rw [e1 j, Pi.single_eq_of_ne hj, zero_add]
    · have eν := e1 ℓ.1.2
      rw [Pi.single_eq_same] at eν
      exact Or.inl (by rw [eν, add_comm])
  · have key : ∀ j : Fin 4, (linkHead ℓ).1 j
        = (Pi.single ℓ.1.2 1 : Fin 4 → ZMod N) j + (linkTail ℓ).1 j :=
      fun j => torusShift_apply_coord _ _ _
    have e1 : ∀ j : Fin 4, x.1 j
        = (Pi.single ℓ.1.2 1 : Fin 4 → ZMod N) j + y.1 j := by
      intro j
      rw [← hℓ.2, ← hℓ.1]
      exact key j
    refine ⟨ℓ.1.2, ℓ.2.2, ?_, ?_⟩
    · intro j hj
      rw [e1 j, Pi.single_eq_of_ne hj, zero_add]
    · have eν := e1 ℓ.1.2
      rw [Pi.single_eq_same] at eν
      exact Or.inr (by rw [eν, add_comm])

/-- The l1 sum splits at one coordinate. -/
theorem coordDistSum_split (x y : LayerSite N) (ν : Fin 4) :
    coordDistSum N x y = cycDist N (x.1 ν) (y.1 ν)
      + ∑ i ∈ Finset.univ.erase ν, cycDist N (x.1 i) (y.1 i) := by
  unfold coordDistSum
  exact (Finset.add_sum_erase Finset.univ _
    (Finset.mem_univ ν)).symm

/-- Along one cube edge the l1 sum changes by at most `1`:
the per-edge lower bound. -/
theorem coordDistSum_le_of_adj {x z y : LayerSite N}
    (h : (cubeGraph N).Adj x z) :
    coordDistSum N x y ≤ coordDistSum N z y + 1 := by
  obtain ⟨ν, hν, hoff, hstep⟩ := adj_coord h
  rw [coordDistSum_split x y ν, coordDistSum_split z y ν]
  have herase : ∑ i ∈ Finset.univ.erase ν, cycDist N (x.1 i) (y.1 i)
      = ∑ i ∈ Finset.univ.erase ν, cycDist N (z.1 i) (y.1 i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiν : i ≠ ν := (Finset.mem_erase.mp hi).1
    rw [hoff i hiν]
  rw [herase]
  rcases hstep with hs | hs
  · have h1 := cycDist_le_add_one (x.1 ν) (y.1 ν)
    rw [← hs] at h1
    omega
  · have h1 := cycDist_add_one_le (z.1 ν) (y.1 ν)
    rw [← hs] at h1
    omega

/-- In `ZMod N`, a point differing from another point is
not fixed by `+1` (the `N = 1` case is vacuous: there all
points agree). -/
theorem zmod_add_one_ne_of_ne {a b : ZMod N} (h : a ≠ b) :
    a + 1 ≠ a := by
  intro hcon
  have h1 : (1 : ZMod N) = 0 := by
    have hc := congrArg (fun t : ZMod N => t - a) hcon
    simpa using hc
  have hdvd : N ∣ 1 := by
    have h2 : ((1 : ℕ) : ZMod N) = 0 := by
      rw [Nat.cast_one]; exact h1
    exact (ZMod.natCast_eq_zero_iff 1 N).mp h2
  have hN : N = 1 := Nat.dvd_one.mp hdvd
  subst hN
  have ha : a = 0 := zmod_eq_zero_of_val_eq_zero a (by
    have hlt := ZMod.val_lt a
    omega)
  have hb : b = 0 := zmod_eq_zero_of_val_eq_zero b (by
    have hlt := ZMod.val_lt b
    omega)
  exact h (ha.trans hb.symm)

/-- The predecessor site: the site differing from `x` only
at the spatial coordinate `i`, where it is one step down. -/
theorem exists_site_sub_one (x : LayerSite N) {i : Fin 4}
    (hi0 : i ≠ 0) :
    ∃ z : LayerSite N, ∀ j : Fin 4,
      z.1 j = if j = i then x.1 i - 1 else x.1 j := by
  refine ⟨⟨Function.update (x.1) i (x.1 i - 1), ?_⟩, ?_⟩
  · have h0 : (Function.update (x.1) i (x.1 i - 1)) 0 = x.1 0 :=
      Function.update_of_ne (Ne.symm hi0) _ _
    rw [h0]
    exact x.2
  · intro j
    show Function.update (x.1) i (x.1 i - 1) j
      = if j = i then x.1 i - 1 else x.1 j
    rw [Function.update_apply]

/-- One step closer: if the l1 sum to the target is
positive, some neighbour of `x` has l1 sum to the target
exactly one less. The step moves one differing coordinate
along its shorter wrap arc. -/
theorem exists_adj_coordDistSum {x y : LayerSite N}
    (h : 0 < coordDistSum N x y) :
    ∃ z : LayerSite N, (cubeGraph N).Adj x z ∧
      coordDistSum N z y + 1 = coordDistSum N x y := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, x.1 i ≠ y.1 i := by
    by_contra hcon
    push_neg at hcon
    have hxy : x = y := Subtype.ext (funext hcon)
    rw [hxy] at h
    have h0 : coordDistSum N y y = 0 := by
      simp [coordDistSum, cycDist_self]
    omega
  have hi0 : i ≠ 0 := by
    intro h0
    apply hi
    rw [h0, layerSite_zero x, layerSite_zero y]
  have hd1 : 1 ≤ (y.1 i - x.1 i).val := by
    by_contra hc
    push_neg at hc
    have hv : (y.1 i - x.1 i).val = 0 := by omega
    exact hi (sub_eq_zero.mp
      (zmod_eq_zero_of_val_eq_zero _ hv)).symm
  have he1 : 1 ≤ (x.1 i - y.1 i).val := by
    by_contra hc
    push_neg at hc
    have hv : (x.1 i - y.1 i).val = 0 := by omega
    exact hi (sub_eq_zero.mp (zmod_eq_zero_of_val_eq_zero _ hv))
  by_cases hcase : (y.1 i - x.1 i).val ≤ (x.1 i - y.1 i).val
  · -- forward step: shift coordinate `i` up
    refine ⟨layerShift i hi0 x, ?_, ?_⟩
    · have hne : linkTail (layerLinkOf x i hi0)
          ≠ linkHead (layerLinkOf x i hi0) := by
        intro hcon
        have e := congrFun (congrArg Subtype.val hcon) i
        have e1 : (linkTail (layerLinkOf x i hi0)).1 i
            = x.1 i := rfl
        have e2 : (linkHead (layerLinkOf x i hi0)).1 i
            = x.1 i + 1 := layerShift_coord_self hi0 x
        rw [e1, e2] at e
        exact zmod_add_one_ne_of_ne hi e.symm
      exact cubeGraph_adj_of_link _ hne
    · rw [coordDistSum_split x y i,
        coordDistSum_split (layerShift i hi0 x) y i]
      have herase : ∑ j ∈ Finset.univ.erase i,
            cycDist N ((layerShift i hi0 x).1 j) (y.1 j)
          = ∑ j ∈ Finset.univ.erase i,
            cycDist N (x.1 j) (y.1 j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjν : j ≠ i := (Finset.mem_erase.mp hj).1
        rw [layerShift_coord_of_ne hi0 x hjν]
      have hν : cycDist N ((layerShift i hi0 x).1 i) (y.1 i) + 1
          = cycDist N (x.1 i) (y.1 i) := by
        rw [layerShift_coord_self hi0 x]
        exact cycDist_add_one_eq_of_le hd1 hcase
      omega
  · -- backward step: move coordinate `i` down
    push_neg at hcase
    obtain ⟨z, hz1⟩ := exists_site_sub_one x hi0
    have hzi : z.1 i = x.1 i - 1 := by
      rw [hz1 i, if_pos rfl]
    have hshift : layerShift i hi0 z = x := by
      apply Subtype.ext
      funext j
      rw [layerShift_coord, hz1 j]
      by_cases hj : j = i
      · subst hj
        rw [Pi.single_eq_same, if_pos rfl]
        ring
      · rw [Pi.single_eq_of_ne hj, if_neg hj, zero_add]
    refine ⟨z, ?_, ?_⟩
    · have hne : x ≠ z := by
        intro hcon
        have e := congrFun (congrArg Subtype.val hcon) i
        rw [hzi] at e
        have e2 := congrArg (fun t : ZMod N => t + 1) e
        rw [sub_add_cancel] at e2
        exact zmod_add_one_ne_of_ne hi e2
      exact (cubeGraph_adj x z).mpr
        ⟨hne, layerLinkOf z i hi0, Or.inr ⟨rfl, hshift⟩⟩
    · rw [coordDistSum_split x y i, coordDistSum_split z y i]
      have herase : ∑ j ∈ Finset.univ.erase i,
            cycDist N (z.1 j) (y.1 j)
          = ∑ j ∈ Finset.univ.erase i,
            cycDist N (x.1 j) (y.1 j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjν : j ≠ i := (Finset.mem_erase.mp hj).1
        rw [hz1 j, if_neg hjν]
      have hν : cycDist N (z.1 i) (y.1 i) + 1
          = cycDist N (x.1 i) (y.1 i) := by
        rw [hzi]
        exact cycDist_sub_one_eq_of_lt he1 hcase
      omega

/-- Sites at l1 sum `0` agree. -/
theorem site_eq_of_coordDistSum_eq_zero {x y : LayerSite N}
    (h0 : coordDistSum N x y = 0) : x = y := by
  apply Subtype.ext
  funext j
  have hj : cycDist N (x.1 j) (y.1 j) = 0 := by
    unfold coordDistSum at h0
    have hsum := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Nat.zero_le (cycDist N (x.1 i) (y.1 i)))).mp h0
    exact hsum j (Finset.mem_univ j)
  exact zmod_eq_of_cycDist_eq_zero hj

/-- A walk of exactly the l1 sum's length, by induction on
the sum: the upper bound, and reachability with it. -/
theorem exists_walk_length_eq (n : ℕ) (x y : LayerSite N)
    (h : coordDistSum N x y ≤ n) :
    ∃ p : (cubeGraph N).Walk x y, p.length = coordDistSum N x y := by
  induction n generalizing x y with
  | zero =>
    have h0 : coordDistSum N x y = 0 := by omega
    have hxy : x = y := site_eq_of_coordDistSum_eq_zero h0
    subst hxy
    exact ⟨SimpleGraph.Walk.nil, by
      rw [SimpleGraph.Walk.length_nil]
      exact h0.symm⟩
  | succ n ih =>
    by_cases h0 : coordDistSum N x y = 0
    · have hxy : x = y := site_eq_of_coordDistSum_eq_zero h0
      subst hxy
      exact ⟨SimpleGraph.Walk.nil, by
        rw [SimpleGraph.Walk.length_nil]
        exact h0.symm⟩
    · have hpos : 0 < coordDistSum N x y := by omega
      obtain ⟨z, hadj, hsum⟩ := exists_adj_coordDistSum hpos
      have hle : coordDistSum N z y ≤ n := by omega
      obtain ⟨p, hp⟩ := ih z y hle
      exact ⟨SimpleGraph.Walk.cons hadj p, by
        rw [SimpleGraph.Walk.length_cons, hp]
        exact hsum⟩

/-- The l1 sum is a lower bound for every walk's length:
induction on the walk, with the per-edge bound at each
step. -/
theorem coordDistSum_le_walk_length {x y : LayerSite N}
    (p : (cubeGraph N).Walk x y) :
    coordDistSum N x y ≤ p.length := by
  induction p with
  | nil =>
    have h0 : ∀ w : LayerSite N, coordDistSum N w w = 0 :=
      fun w => by simp [coordDistSum, cycDist_self]
    rw [h0]
    exact Nat.zero_le _
  | cons h p ih =>
    rw [SimpleGraph.Walk.length_cons]
    refine le_trans (coordDistSum_le_of_adj h) ?_
    omega

end Graph

section Headlines

/-- **GR-GEO-1 target 1, discharged.** The cube graph is
connected, at the pin's generality (every `N` with
`[NeZero N]`): the walk of `exists_walk_length_eq` reaches
every pair, and the site type is inhabited. -/
theorem cubeGraph_connected (N : ℕ) [NeZero N] :
    CubeGraphConnected N := by
  rw [cubeGraphConnected_unfold]
  refine { preconnected := ?_, nonempty := ?_ }
  · intro u v
    obtain ⟨p, _hp⟩ := exists_walk_length_eq
      (coordDistSum N u v) u v (le_refl _)
    show Nonempty ((cubeGraph N).Walk u v)
    exact ⟨p⟩
  · exact ⟨⟨fun _ => 0, by exact zmod_val_zero⟩⟩

/-- **GR-GEO-1 target 2, discharged.** The l1 formula for
`geoDist`, as a theorem about `SimpleGraph.dist` at the
pin's generality (every `N` with `[NeZero N]`, boundary
seats included): the upper bound is the exhibited walk of
the sum's length; the lower bound is the per-edge step
bound applied to a shortest walk from Mathlib's distance
theory for the connected cube graph. -/
theorem geoDist_l1_formula (N : ℕ) [NeZero N] :
    GeoDistL1Formula N := by
  rw [geoDistL1Formula_unfold]
  intro x y
  have hconn : (cubeGraph N).Connected :=
    cubeGraphConnected_unfold.mp (cubeGraph_connected N)
  obtain ⟨p, hp⟩ := SimpleGraph.Connected.exists_walk_length_eq_dist
    hconn x y
  have hle1 : (cubeGraph N).dist x y ≤ coordDistSum N x y := by
    obtain ⟨q, hq⟩ := exists_walk_length_eq
      (coordDistSum N x y) x y (le_refl _)
    have h2 := SimpleGraph.dist_le q
    rw [hq] at h2
    exact h2
  have hle2 : coordDistSum N x y ≤ (cubeGraph N).dist x y := by
    have h2 := coordDistSum_le_walk_length p
    rw [hp] at h2
    exact h2
  rw [geoDist_unfold]
  show (cubeGraph N).dist x y = coordDistSum N x y
  exact le_antisymm hle1 hle2

end Headlines

end ThetLogos
