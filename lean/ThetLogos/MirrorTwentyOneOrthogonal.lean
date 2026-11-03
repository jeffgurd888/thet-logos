/-
# ORTHOGONAL PANTOREALITY — two mirror arms on independent coordinates

Brick: ORTHOGONAL PANTOREALITY, algebra module (Jeff's fire
word, 2026-11-02 21:45 EST; scoping:
`whitepaper/../your_files/pantogram-construction-and-build-scoping-2026-11-02.md`,
Part 2). Companion foundation: `MirrorTwentyOne` (the mirror
involution `Θ` on `Fin 21`, unique fixed point the center `0`)
and `MirrorTwentyOneAlgebra` (the pullback `Θ̂` as a ring
automorphism of `Fin 21 → ℝ`; fixed functions ≃ values on the
11 representatives).

This module takes the scoping's item 5 ("orthogonal
pantoreality") literally at finite size: TWO copies of the
mirror system on independent coordinates — grid functions
`Fin 21 × Fin 21 → ℝ`, with an arm pullback `Θ̂₁` mirroring
the first coordinate only and an arm pullback `Θ̂₂` mirroring
the second coordinate only.

**What this module proves — and all it proves (pins O1, O2):**
- O1: the arm pullbacks commute exactly,
  `Θ̂₁ (Θ̂₂ f) = Θ̂₂ (Θ̂₁ f)` — the arms act independently,
  proved, not asserted (kill K-O1 armed against this and did
  not fire).
- Each arm pullback is a ring automorphism of the grid
  function algebra (packaged as `RingEquiv`s).
- O2: the jointly mirror-fixed functions — fixed by both arms
  — are exactly the functions determined by their values on
  the 11 × 11 grid of representatives:
  `jointlyFixedEquivReps : {f // Θ̂₁ f = f ∧ Θ̂₂ f = f} ≃
  (Fin 11 × Fin 11 → ℝ)`. The joint fixed dimension is
  121 = 11², FORCED as the product of Mirror-21's 11.

Finite, elementary, kernel-checked. No operator, no spectrum,
no physics is asserted here (the operator weld is the
companion brick `MirrorTwentyOneOrthogonalSpectral`; the
numerics are `python/mirror21_orthogonal_heat.py`).

**NO CLAIM** — parts of any official Millennium statement
closed by this module: 0. Dials: 0/4.
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Ring.Equiv
import ThetLogos.MirrorTwentyOneAlgebra

namespace ThetLogos

/-- The grid: points of the two-arm system, two independent
21-point coordinates. -/
abbrev GridIndex := ManifoldIndex × ManifoldIndex

/-- The first arm's pullback: mirror the first coordinate only,
`Θ̂₁ f (a, b) = f (Θ a, b)`. -/
def thetaHat₁ (f : GridIndex → ℝ) : GridIndex → ℝ :=
  fun p => f (involution p.1, p.2)

/-- The second arm's pullback: mirror the second coordinate
only, `Θ̂₂ f (a, b) = f (a, Θ b)`. -/
def thetaHat₂ (f : GridIndex → ℝ) : GridIndex → ℝ :=
  fun p => f (p.1, involution p.2)

/-- The first arm's pullback is an involution on functions. -/
theorem thetaHat₁_involutive (f : GridIndex → ℝ) :
    thetaHat₁ (thetaHat₁ f) = f := by
  funext ⟨a, b⟩
  show f (involution (involution a), b) = f (a, b)
  rw [involution_involutive]

/-- The second arm's pullback is an involution on functions. -/
theorem thetaHat₂_involutive (f : GridIndex → ℝ) :
    thetaHat₂ (thetaHat₂ f) = f := by
  funext ⟨a, b⟩
  show f (a, involution (involution b)) = f (a, b)
  rw [involution_involutive]

/-- The first arm's pullback preserves multiplication. -/
theorem thetaHat₁_mul (f g : GridIndex → ℝ) :
    thetaHat₁ (f * g) = thetaHat₁ f * thetaHat₁ g := rfl

/-- The second arm's pullback preserves multiplication. -/
theorem thetaHat₂_mul (f g : GridIndex → ℝ) :
    thetaHat₂ (f * g) = thetaHat₂ f * thetaHat₂ g := rfl

/-- The first arm's pullback preserves addition. -/
theorem thetaHat₁_add (f g : GridIndex → ℝ) :
    thetaHat₁ (f + g) = thetaHat₁ f + thetaHat₁ g := rfl

/-- The second arm's pullback preserves addition. -/
theorem thetaHat₂_add (f g : GridIndex → ℝ) :
    thetaHat₂ (f + g) = thetaHat₂ f + thetaHat₂ g := rfl

/-- The first arm's pullback as a ring automorphism. -/
def thetaEquiv₁ : (GridIndex → ℝ) ≃+* (GridIndex → ℝ) where
  toFun := thetaHat₁
  invFun := thetaHat₁
  left_inv := thetaHat₁_involutive
  right_inv := thetaHat₁_involutive
  map_mul' := thetaHat₁_mul
  map_add' := thetaHat₁_add

/-- The second arm's pullback as a ring automorphism. -/
def thetaEquiv₂ : (GridIndex → ℝ) ≃+* (GridIndex → ℝ) where
  toFun := thetaHat₂
  invFun := thetaHat₂
  left_inv := thetaHat₂_involutive
  right_inv := thetaHat₂_involutive
  map_mul' := thetaHat₂_mul
  map_add' := thetaHat₂_add

/-- The first automorphism's underlying map is its pullback. -/
theorem thetaEquiv₁_apply (f : GridIndex → ℝ) :
    thetaEquiv₁ f = thetaHat₁ f := rfl

/-- The second automorphism's underlying map is its pullback. -/
theorem thetaEquiv₂_apply (f : GridIndex → ℝ) :
    thetaEquiv₂ f = thetaHat₂ f := rfl

/-- **O1 — the arms are truly orthogonal:** the two arm
pullbacks commute exactly, `Θ̂₁ (Θ̂₂ f) = Θ̂₂ (Θ̂₁ f)`. The
arms act on independent coordinates, so the composite in
either order is the double pullback
`f (Θ a, Θ b)`. (Pre-registered kill K-O1 armed against this
statement; it did not fire.) -/
theorem thetaHat₁_thetaHat₂ (f : GridIndex → ℝ) :
    thetaHat₁ (thetaHat₂ f) = thetaHat₂ (thetaHat₁ f) := by
  funext ⟨a, b⟩
  rfl

/-- Characterization: `Θ̂₁ f = f` iff `f` is mirror-symmetric
in its first coordinate. -/
theorem thetaHat₁_fixed_iff (f : GridIndex → ℝ) :
    thetaHat₁ f = f ↔
      ∀ p, f (involution p.1, p.2) = f p := by
  constructor
  · intro h p
    exact congrFun h p
  · intro h
    funext p
    exact h p

/-- Characterization: `Θ̂₂ f = f` iff `f` is mirror-symmetric
in its second coordinate. -/
theorem thetaHat₂_fixed_iff (f : GridIndex → ℝ) :
    thetaHat₂ f = f ↔
      ∀ p, f (p.1, involution p.2) = f p := by
  constructor
  · intro h p
    exact congrFun h p
  · intro h
    funext p
    exact h p

/-- The representative pair of a grid point: the representative
of each coordinate, `Fin 11 × Fin 11`-valued. -/
def repOf₂ (p : GridIndex) : Fin 11 × Fin 11 :=
  (repOf p.1, repOf p.2)

/-- The embedding of a representative pair into the grid. -/
def repEmbed₂ (q : Fin 11 × Fin 11) : GridIndex :=
  (repEmbed q.1, repEmbed q.2)

/-- Mirroring the first coordinate does not change a point's
representative pair. -/
theorem repOf₂_involution_fst (p : GridIndex) :
    repOf₂ (involution p.1, p.2) = repOf₂ p := by
  show (repOf (involution p.1), repOf p.2) = (repOf p.1, repOf p.2)
  rw [repOf_involution]

/-- Mirroring the second coordinate does not change a point's
representative pair. -/
theorem repOf₂_involution_snd (p : GridIndex) :
    repOf₂ (p.1, involution p.2) = repOf₂ p := by
  show (repOf p.1, repOf (involution p.2)) = (repOf p.1, repOf p.2)
  rw [repOf_involution]

/-- The representative pair of an embedded representative pair
is itself. -/
theorem repOf₂_repEmbed₂ (q : Fin 11 × Fin 11) :
    repOf₂ (repEmbed₂ q) = q := by
  obtain ⟨k, l⟩ := q
  show (repOf (repEmbed k), repOf (repEmbed l)) = (k, l)
  rw [repOf_repEmbed, repOf_repEmbed]

/-- Extend values on the 11 × 11 representative grid to a grid
function by mirror symmetry in both coordinates. -/
def extendReps₂ (g : Fin 11 × Fin 11 → ℝ) : GridIndex → ℝ :=
  fun p => g (repOf₂ p)

/-- The two-arm extension is fixed by the first arm. -/
theorem thetaHat₁_extendReps₂ (g : Fin 11 × Fin 11 → ℝ) :
    thetaHat₁ (extendReps₂ g) = extendReps₂ g := by
  apply (thetaHat₁_fixed_iff _).mpr
  intro p
  show extendReps₂ g (involution p.1, p.2) = extendReps₂ g p
  simp only [extendReps₂, repOf₂_involution_fst]

/-- The two-arm extension is fixed by the second arm. -/
theorem thetaHat₂_extendReps₂ (g : Fin 11 × Fin 11 → ℝ) :
    thetaHat₂ (extendReps₂ g) = extendReps₂ g := by
  apply (thetaHat₂_fixed_iff _).mpr
  intro p
  show extendReps₂ g (p.1, involution p.2) = extendReps₂ g p
  simp only [extendReps₂, repOf₂_involution_snd]

/-- A jointly fixed function takes the same value at the
embedded representative pair of a point as at the point
itself: each coordinate of the embedded pair is the coordinate
or its mirror, and joint fixedness absorbs both mirrors. -/
theorem fixed_apply_repEmbed₂_repOf₂ (f : GridIndex → ℝ)
    (h₁ : thetaHat₁ f = f) (h₂ : thetaHat₂ f = f) (p : GridIndex) :
    f (repEmbed₂ (repOf₂ p)) = f p := by
  have e1 : ∀ x y, f (involution x, y) = f (x, y) :=
    fun x y => (thetaHat₁_fixed_iff f).mp h₁ (x, y)
  have e2 : ∀ x y, f (x, involution y) = f (x, y) :=
    fun x y => (thetaHat₂_fixed_iff f).mp h₂ (x, y)
  obtain ⟨a, b⟩ := p
  show f (repEmbed (repOf a), repEmbed (repOf b)) = f (a, b)
  rcases repEmbed_repOf a with ha | ha <;>
    rcases repEmbed_repOf b with hb | hb
  · rw [ha, hb]
  · rw [ha, hb]; exact e2 a b
  · rw [ha, hb]; exact e1 a b
  · rw [ha, hb]; rw [e2 (involution a) b]; exact e1 a b

/-- **O2 — the combined figure is imposed, not chosen:** the
jointly mirror-fixed grid functions are exactly the functions
determined by their values on the 11 × 11 representative
grid. Restriction to the representatives is a bijection
between jointly fixed functions and arbitrary values on
`Fin 11 × Fin 11` — the joint fixed dimension is exactly
121 = 11², forced as the product of Mirror-21's 11
(10 mirror pairs + the unique center, per coordinate). -/
def jointlyFixedEquivReps :
    {f : GridIndex → ℝ // thetaHat₁ f = f ∧ thetaHat₂ f = f} ≃
      (Fin 11 × Fin 11 → ℝ) where
  toFun := fun f q => f.1 (repEmbed₂ q)
  invFun := fun g =>
    ⟨extendReps₂ g, thetaHat₁_extendReps₂ g, thetaHat₂_extendReps₂ g⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext p
    show f.1 (repEmbed₂ (repOf₂ p)) = f.1 p
    exact fixed_apply_repEmbed₂_repOf₂ f.1 f.2.1 f.2.2 p
  right_inv := by
    intro g
    funext q
    show g (repOf₂ (repEmbed₂ q)) = g q
    rw [repOf₂_repEmbed₂]

/-- The restriction-to-representatives map for jointly fixed
functions is bijective. -/
theorem jointlyFixedEquivReps_bijective :
    Function.Bijective jointlyFixedEquivReps :=
  jointlyFixedEquivReps.bijective

end ThetLogos
