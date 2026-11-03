/-
# MIRROR-21 — the function algebra and the pullback automorphism

Brick: MIRROR-21 algebra (Jeff's commission, 2026-11-02
20:09 EST). Companion to `MirrorTwentyOne` (the mirror
involution `Θ` on `Fin 21`, its unique fixed point the
center `0`).

The dropped sketch's `CentralInvolutionAlgebra` class
asserted a "21-dimensional algebra with central involution"
but defined no multiplication and no algebra at all — its
axioms were structure fields, assumed rather than derived.
This module supplies the honest object the sketch named:
the algebra of real-valued functions on the 21 points,
`Fin 21 → ℝ`, with the pointwise (Pi) ring structure, and
the pullback of `Θ` on it.

**What this module proves — and all it proves:** the
pullback `Θ̂ f = f ∘ Θ` is a ring automorphism of
`Fin 21 → ℝ` (packaged as a `RingEquiv`, with the pointwise
hom properties also stated individually); `Θ̂` fixes the
value at the center; and a function is fixed by `Θ̂` iff it
is mirror-symmetric, `f (-i) = f i` for all `i`. The fixed
functions are exactly the functions determined by their
values on the 11 representatives `{0, …, 10}` (10 mirror
pairs + the unique center) — the restriction equivalence
`fixedEquivReps`. All of it is finite, elementary, and
kernel-checked; no spectrum, no operator, no physics is
asserted here.

**NO CLAIM** — parts of any official Millennium statement
closed by this module: 0. Dials: 0/4.
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Ring.Equiv
import ThetLogos.MirrorTwentyOne

namespace ThetLogos

/-- The pullback of the mirror involution on functions:
`Θ̂ f i = f (Θ i)`. -/
def thetaHat (f : ManifoldIndex → ℝ) : ManifoldIndex → ℝ :=
  fun i => f (involution i)

/-- The pullback is an involution on functions. -/
theorem thetaHat_involutive (f : ManifoldIndex → ℝ) :
    thetaHat (thetaHat f) = f := by
  funext i
  show f (involution (involution i)) = f i
  rw [involution_involutive]

/-- The pullback preserves multiplication (pointwise). -/
theorem thetaHat_mul (f g : ManifoldIndex → ℝ) :
    thetaHat (f * g) = thetaHat f * thetaHat g := rfl

/-- The pullback preserves addition (pointwise). -/
theorem thetaHat_add (f g : ManifoldIndex → ℝ) :
    thetaHat (f + g) = thetaHat f + thetaHat g := rfl

/-- The pullback preserves zero. -/
theorem thetaHat_zero : thetaHat 0 = 0 := rfl

/-- The pullback preserves one. -/
theorem thetaHat_one : thetaHat 1 = 1 := rfl

/-- The pullback as a ring automorphism of `Fin 21 → ℝ`. -/
def thetaEquiv : (ManifoldIndex → ℝ) ≃+* (ManifoldIndex → ℝ) where
  toFun := thetaHat
  invFun := thetaHat
  left_inv := thetaHat_involutive
  right_inv := thetaHat_involutive
  map_mul' := thetaHat_mul
  map_add' := thetaHat_add

/-- The automorphism's underlying map is the pullback. -/
theorem thetaEquiv_apply (f : ManifoldIndex → ℝ) :
    thetaEquiv f = thetaHat f := rfl

/-- The pullback fixes the value at the center. -/
theorem thetaHat_center (f : ManifoldIndex → ℝ) :
    thetaHat f TethCenter = f TethCenter := by
  show f (involution TethCenter) = f TethCenter
  rw [involution_center_fixed]

/-- Characterization: `Θ̂ f = f` iff `f` is mirror-symmetric. -/
theorem thetaHat_fixed_iff (f : ManifoldIndex → ℝ) :
    thetaHat f = f ↔ ∀ i, f (involution i) = f i := by
  constructor
  · intro h i
    have hcongr := congrFun h i
    exact hcongr
  · intro h
    funext i
    exact h i

/-- The 11 representatives `{0, …, 10}` — the center and one point
from each mirror pair — embedded into the 21 points. -/
def repEmbed (k : Fin 11) : ManifoldIndex :=
  ⟨k.val, lt_trans k.isLt (by decide)⟩

/-- The representative index of a point: its own index if it lies
in `{0, …, 10}`, else its mirror's index. -/
def repOf (i : ManifoldIndex) : Fin 11 :=
  ⟨if i.val ≤ 10 then i.val else 21 - i.val, by
    have hi := i.isLt
    split_ifs with h <;> omega⟩

/-- The value of the representative index, by definition. -/
theorem repOf_val (i : ManifoldIndex) :
    (repOf i).val = if i.val ≤ 10 then i.val else 21 - i.val := rfl

/-- The value of an embedded representative is its own index. -/
theorem repEmbed_val (k : Fin 11) : (repEmbed k).val = k.val := rfl

/-- A point and its mirror have the same representative. -/
theorem repOf_involution (i : ManifoldIndex) :
    repOf (involution i) = repOf i := by
  apply Fin.ext
  rw [repOf_val, repOf_val, involution_val]
  have hi := i.isLt
  split_ifs with h1 h2 h3 <;> omega

/-- The representative of an embedded representative is itself. -/
theorem repOf_repEmbed (k : Fin 11) : repOf (repEmbed k) = k := by
  apply Fin.ext
  rw [repOf_val, repEmbed_val]
  have hk := k.isLt
  split_ifs with h
  · rfl
  · omega

/-- An embedded representative of a point is the point itself or
its mirror. -/
theorem repEmbed_repOf (i : ManifoldIndex) :
    repEmbed (repOf i) = i ∨ repEmbed (repOf i) = involution i := by
  have hval : (repEmbed (repOf i)).val = (repOf i).val := rfl
  rw [repOf_val] at hval
  have hi := i.isLt
  by_cases h : i.val ≤ 10
  · left
    apply Fin.ext
    rw [hval]
    split_ifs; omega
  · right
    apply Fin.ext
    rw [hval, involution_val]
    split_ifs; omega

/-- Extend values on the representatives to a function on all
21 points by mirror symmetry. -/
def extendReps (g : Fin 11 → ℝ) : ManifoldIndex → ℝ :=
  fun i => g (repOf i)

/-- The extension of representative values is mirror-symmetric. -/
theorem thetaHat_extendReps (g : Fin 11 → ℝ) :
    thetaHat (extendReps g) = extendReps g := by
  apply (thetaHat_fixed_iff _).mpr
  intro i
  show extendReps g (involution i) = extendReps g i
  simp only [extendReps, repOf_involution]

/-- The fixed functions are exactly the functions determined by
their values on the 11 representatives: restriction to the
representatives is a bijection between `Θ̂`-fixed functions and
arbitrary values on `Fin 11` (10 mirror pairs + the unique
center = 11 degrees of freedom). -/
def fixedEquivReps :
    {f : ManifoldIndex → ℝ // thetaHat f = f} ≃ (Fin 11 → ℝ) where
  toFun := fun f k => f.1 (repEmbed k)
  invFun := fun g => ⟨extendReps g, thetaHat_extendReps g⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext i
    show f.1 (repEmbed (repOf i)) = f.1 i
    rcases repEmbed_repOf i with h | h
    · rw [h]
    · rw [h]
      exact (thetaHat_fixed_iff _).mp f.2 i
  right_inv := by
    intro g
    funext k
    show g (repOf (repEmbed k)) = g k
    rw [repOf_repEmbed]

/-- The restriction-to-representatives map is bijective. -/
theorem fixedEquivReps_bijective :
    Function.Bijective fixedEquivReps := fixedEquivReps.bijective

end ThetLogos
