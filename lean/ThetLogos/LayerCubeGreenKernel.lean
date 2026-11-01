import Mathlib.Tactic
import ThetLogos.MaxwellQuadAssembly
import ThetLogos.LayerCubeDistance

namespace ThetLogos

open Finset

/-!
# ThetLogos.LayerCubeGreenKernel - GR-GEO-2: the Green weld

**Working label only.** The module name
`LayerCubeGreenKernel` and the line name GR-GEO are working
labels; Jeff names.

**Status: GR-GEO-2 landing. NO CLAIM. No gravity object is
defined, constructed, or asserted to exist. Dial 2 = 0 under
every outcome of this line, including total success. The
Green kernel below is a finite matrix inverse on a chosen
finite operator - instrument bookkeeping (K-GR-LAUNDER /
K-GR-SMUG fence, on the face). No falloff-law sentence is
proved, claimed, or decided by this module: the module
delivers the shadow predicate's SEAT VALUES at one named
seat, and evaluates the predicate instance there, as a seat
fact only.**

Governing texts: the GR-GEO-0 pin `LayerCubeDistancePost`
(`PoseObjFShadow` registered verbatim there, with
`linkGeoDist` the `geoDist` between link tails), GR-GEO-1
(`LayerCubeDistance`: `cubeGraph_connected`,
`geoDist_l1_formula`), MAX-2 (`MaxwellQuadAssembly`:
`maxwellM1_proved` - the form identity and positivity of
`maxwellOp`), and the scoping memo
`routeb-general-scratch/scoping-gravity-vocabulary-2026-10-31.md`
sections 2-3.

## Contents

1. **The Green kernel (general `N`, named `m > 0`).**
   `greenKernel N m hm l l' := <e_l, (maxwellOp N + m^2)^{-1}
   e_l'>` in coordinate form: the `l`-component of the
   shifted operator's inverse applied to the basis angle at
   `l'`. Invertibility of the shift is PROVED from MAX-2's
   M1: the form of `maxwellOp N` is nonnegative, so the
   `m^2` shift is strictly positive on every nonzero angle,
   hence injective, hence bijective in finite dimension.
   It is never assumed.
2. **Symmetry and diagonal positivity** of the kernel, from
   the symmetry and positivity of the shifted form.
3. **Seat values at the named seat `N = 2`, `m = 1`.** The
   kernel's entries there are computed exactly (a Fourier
   candidate on the `ZMod 2` cube, verified against the
   operator in the proof of `shiftedOp_greenCand`), the
   values are classified by the pin's `linkGeoDist` class
   (`greenKernel_seat_cases`), and the pin's registered
   `PoseObjFShadow` instance is evaluated at the named
   supplied constant `C = 1/2`: it HOLDS at this seat
   (`poseObjFShadow_seat`). That is a seat fact about the
   instance `(N = 2, m = 1, C = 1/2)` only; the falloff LAW
   is not proved, claimed, or decided here, and no sentence
   beyond the seat may be drawn from it.

## Kills and fences (binding, on the face)

- K-GR-VAC / constant discipline: `C = 1/2` and `m = 1` are
  supplied and named on the face; nothing is existentially
  quantified inside the predicate.
- K-GR-STAB: the seat values are reported exactly as
  computed; no seat, mass, or constant was re-named after
  the fact.
- K-GR-SMUG / K-GR-LAUNDER: this kernel is a finite matrix
  inverse on a chosen finite operator. It is not a gravity
  object and not a spacetime two-point function, and the
  seat instance of the shadow comparison holding at
  `N = 2` is not a falloff law.
-/

section General

variable {N : ℕ} [NeZero N]

/-- **The shifted Maxwell operator** `maxwellOp N + m^2` (as
the linear endomorphism `maxwellOp N + m^2 • id`) on the
link-angle space. The shift is the mass term of the Green
weld: for `m ≠ 0` it makes the operator invertible, proved
below from M1. -/
noncomputable def shiftedOp (N : ℕ) [NeZero N] (m : ℝ) :
    Module.End ℝ (linkAngle N) :=
  maxwellOp N + (m ^ 2) • LinearMap.id

/-- The shifted operator, pointwise:
`(shiftedOp N m θ) l = (maxwellOp N θ) l + m^2 * θ l`. -/
theorem shiftedOp_apply (m : ℝ) (θ : linkAngle N)
    (ℓ : LayerLink N) :
    (shiftedOp N m θ) ℓ = (maxwellOp N θ) ℓ + m ^ 2 * θ ℓ := by
  simp [shiftedOp, smul_eq_mul]

/-- **The bilinear form of the shifted operator**: the
plaquette form of MAX-2 plus `m^2` times the plain pairing.
This is the polarization output of M1, shifted. -/
theorem shiftedOp_form (m : ℝ) (θ η : linkAngle N) :
    (∑ ℓ, θ ℓ * (shiftedOp N m η) ℓ)
      = (∑ P ∈ allPlaqData N, plaqAngle P θ * plaqAngle P η)
        + m ^ 2 * (∑ ℓ, θ ℓ * η ℓ) := by
  have h1 : (∑ ℓ, θ ℓ * (shiftedOp N m η) ℓ)
      = (∑ ℓ, θ ℓ * (maxwellOp N η) ℓ)
        + m ^ 2 * (∑ ℓ, θ ℓ * η ℓ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ℓ _
    rw [shiftedOp_apply]; ring
  rw [h1, maxwellOp_form]

/-- **The diagonal of the shifted form**: the quadratic
form of MAX-2's M1 plus `m^2` times the sum of squares.
In particular it is strictly positive on nonzero angles
when `m ≠ 0` - the invertibility input. -/
theorem shiftedOp_form_self (m : ℝ) (θ : linkAngle N) :
    (∑ ℓ, θ ℓ * (shiftedOp N m θ) ℓ)
      = maxwellQuad N θ + m ^ 2 * (∑ ℓ, θ ℓ ^ 2) := by
  have h := maxwellOp_form_self (N := N) θ
  rw [maxwellOp_form] at h
  have h2 : (∑ ℓ, θ ℓ * θ ℓ) = ∑ ℓ, θ ℓ ^ 2 :=
    Finset.sum_congr rfl (fun ℓ _ => by ring)
  rw [shiftedOp_form, h, h2]

/-- **Injectivity of the shift, from M1.** If
`shiftedOp N m θ = shiftedOp N m η` with `m ≠ 0`, the
difference angle has vanishing shifted form; by
`shiftedOp_form_self` that form is a sum of two nonnegative
terms, the second a positive multiple of a sum of squares,
so the difference is zero. -/
theorem shiftedOp_injective {m : ℝ} (hm : m ≠ 0) :
    Function.Injective (shiftedOp N m) := by
  intro θ η h
  have hd : shiftedOp N m (θ - η) = 0 := by
    rw [map_sub, h, sub_self]
  have hform := shiftedOp_form_self (N := N) m (θ - η)
  rw [hd] at hform
  have hsum0 : (∑ ℓ, (θ - η) ℓ * ((0 : linkAngle N) ℓ)) = 0 := by
    simp
  rw [hsum0] at hform
  have hquad : 0 ≤ maxwellQuad N (θ - η) := maxwellQuad_nonneg _
  have hsum : 0 ≤ ∑ ℓ, (θ - η) ℓ ^ 2 :=
    Finset.sum_nonneg (fun ℓ _ => sq_nonneg _)
  have hm2 : 0 < m ^ 2 := sq_pos_of_ne_zero hm
  have hsum0' : (∑ ℓ, (θ - η) ℓ ^ 2) = 0 := by
    by_contra hc
    have hpos : 0 < m ^ 2 * (∑ ℓ, (θ - η) ℓ ^ 2) :=
      mul_pos hm2 (lt_of_le_of_ne hsum (Ne.symm hc))
    linarith
  have hzero : ∀ ℓ, (θ - η) ℓ = 0 := by
    intro ℓ
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sq_nonneg ((θ - η) i))).mp hsum0' ℓ
      (Finset.mem_univ ℓ)
    exact (pow_eq_zero_iff (show (2 : ℕ) ≠ 0 by norm_num)).mp h0
  have hθη : θ - η = 0 := by
    funext ℓ
    simpa using hzero ℓ
  exact sub_eq_zero.mp hθη

/-- **Bijectivity of the shift** at `m ≠ 0`: injective
endomorphisms of a finite-dimensional space are bijective. -/
theorem shiftedOp_bijective {m : ℝ} (hm : m ≠ 0) :
    Function.Bijective (shiftedOp N m) :=
  ⟨shiftedOp_injective hm,
    LinearMap.injective_iff_surjective.mp
      (shiftedOp_injective hm)⟩

open Classical in
/-- **The basis angle at `l'`**: the link angle that is `1`
at `l'` and `0` elsewhere (the coordinate basis vector
`e_{l'}` of the weld formula). Defined under classical
decidability, as link equality carries no decidable
instance in the corpus. -/
noncomputable def greenBasis (ℓ' : LayerLink N) : linkAngle N :=
  fun j => if j = ℓ' then 1 else 0

/-- The basis angle at its own link is `1`. -/
theorem greenBasis_self (ℓ' : LayerLink N) :
    greenBasis ℓ' ℓ' = 1 := by
  classical
  simp [greenBasis]

/-- The basis angle vanishes off its own link. -/
theorem greenBasis_of_ne {j ℓ' : LayerLink N} (h : j ≠ ℓ') :
    greenBasis ℓ' j = 0 := by
  classical
  simp [greenBasis, h]

/-- Pairing against a basis angle picks out the component:
`∑ j, θ j * e_{l'} j = θ l'`. -/
theorem sum_mul_greenBasis (θ : linkAngle N) (ℓ' : LayerLink N) :
    (∑ j, θ j * greenBasis ℓ' j) = θ ℓ' := by
  classical
  rw [Finset.sum_eq_single ℓ']
  · rw [greenBasis_self, mul_one]
  · intro j _ hj; rw [greenBasis_of_ne hj, mul_zero]
  · simp

/-- **The shift as a linear equivalence**, for named
`m > 0`: the bijectivity above packaged. The inverse in
the weld formula is this equivalence's inverse - proved,
not assumed. -/
noncomputable def greenEquiv (N : ℕ) [NeZero N] (m : ℝ)
    (hm : 0 < m) :
    linkAngle N ≃ₗ[ℝ] linkAngle N :=
  LinearEquiv.ofBijective (shiftedOp N m)
    (shiftedOp_bijective (ne_of_gt hm))

/-- **The Green kernel** (the weld, in the governing memo's
registered form): for named `m > 0`,
`greenKernel N m hm l l' = <e_l, (maxwellOp N + m^2)^{-1}
e_l'>`, read in coordinates as the `l`-component of the
shifted operator's inverse applied to the basis angle at
`l'`. A finite matrix inverse on a finite operator:
instrument bookkeeping, nothing more (see the face). -/
noncomputable def greenKernel (N : ℕ) [NeZero N] (m : ℝ)
    (hm : 0 < m) (ℓ ℓ' : LayerLink N) : ℝ :=
  ((greenEquiv N m hm).symm (greenBasis ℓ')) ℓ

/-- The defining characterization of the kernel's columns:
the shifted operator applied to the `l'`-column of
`greenKernel` is the basis angle at `l'`. -/
theorem greenKernel_spec (m : ℝ) (hm : 0 < m)
    (ℓ' : LayerLink N) :
    shiftedOp N m (fun ℓ => greenKernel N m hm ℓ ℓ')
      = greenBasis ℓ' := by
  have h1 : (fun ℓ => greenKernel N m hm ℓ ℓ')
      = (greenEquiv N m hm).symm (greenBasis ℓ') := rfl
  rw [h1]
  have h2 : shiftedOp N m ((greenEquiv N m hm).symm
        (greenBasis ℓ'))
      = (greenEquiv N m hm) ((greenEquiv N m hm).symm
        (greenBasis ℓ')) := rfl
  rw [h2]
  exact LinearEquiv.apply_symm_apply _ _

/-- **Uniqueness of kernel columns**: any angle whose
shifted image is the basis angle at `l'` is the `l'`-column
of the kernel. This is the verification principle for the
seat computation below. -/
theorem greenKernel_eq_of (m : ℝ) (hm : 0 < m)
    (θ : linkAngle N) (ℓ' : LayerLink N)
    (hθ : shiftedOp N m θ = greenBasis ℓ') (ℓ : LayerLink N) :
    θ ℓ = greenKernel N m hm ℓ ℓ' := by
  have h1 : (greenEquiv N m hm).symm (greenBasis ℓ') = θ := by
    rw [LinearEquiv.symm_apply_eq]
    have h3 : (greenEquiv N m hm) θ = shiftedOp N m θ := rfl
    rw [h3, hθ]
  show θ ℓ = ((greenEquiv N m hm).symm (greenBasis ℓ')) ℓ
  rw [h1]

/-- **Symmetry of the Green kernel**:
`greenKernel m l l' = greenKernel m l' l`, from the symmetry
of the shifted operator's bilinear form (MAX-2's
polarization output, shifted). -/
theorem greenKernel_symm (m : ℝ) (hm : 0 < m)
    (ℓ ℓ' : LayerLink N) :
    greenKernel N m hm ℓ ℓ' = greenKernel N m hm ℓ' ℓ := by
  have h1 : (∑ j, ((greenEquiv N m hm).symm (greenBasis ℓ')) j
        * (shiftedOp N m
          ((greenEquiv N m hm).symm (greenBasis ℓ))) j)
      = greenKernel N m hm ℓ ℓ' := by
    have hSx : shiftedOp N m
          ((greenEquiv N m hm).symm (greenBasis ℓ))
        = greenBasis ℓ := by
      have h2 : shiftedOp N m ((greenEquiv N m hm).symm
            (greenBasis ℓ))
          = (greenEquiv N m hm) ((greenEquiv N m hm).symm
            (greenBasis ℓ)) := rfl
      rw [h2]
      exact LinearEquiv.apply_symm_apply _ _
    rw [hSx, sum_mul_greenBasis]
    rfl
  have h2 : (∑ j, ((greenEquiv N m hm).symm (greenBasis ℓ)) j
        * (shiftedOp N m
          ((greenEquiv N m hm).symm (greenBasis ℓ'))) j)
      = greenKernel N m hm ℓ' ℓ := by
    have hSx : shiftedOp N m
          ((greenEquiv N m hm).symm (greenBasis ℓ'))
        = greenBasis ℓ' := by
      have h2 : shiftedOp N m ((greenEquiv N m hm).symm
            (greenBasis ℓ'))
          = (greenEquiv N m hm) ((greenEquiv N m hm).symm
            (greenBasis ℓ')) := rfl
      rw [h2]
      exact LinearEquiv.apply_symm_apply _ _
    rw [hSx, sum_mul_greenBasis]
    rfl
  have hsymm : (∑ j, ((greenEquiv N m hm).symm
          (greenBasis ℓ')) j
        * (shiftedOp N m
          ((greenEquiv N m hm).symm (greenBasis ℓ))) j)
      = ∑ j, ((greenEquiv N m hm).symm (greenBasis ℓ)) j
        * (shiftedOp N m
          ((greenEquiv N m hm).symm (greenBasis ℓ'))) j := by
    rw [shiftedOp_form, shiftedOp_form]
    congr 1
    · apply Finset.sum_congr rfl
      intro P _
      ring
    · congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
  rw [← h1, ← h2]
  exact hsymm

/-- **Diagonal positivity of the Green kernel**:
`0 ≤ greenKernel m l l`, from the positivity of the shifted
form (M1 plus the `m^2` sum of squares) evaluated on the
kernel's own column. -/
theorem greenKernel_diag_nonneg (m : ℝ) (hm : 0 < m)
    (ℓ : LayerLink N) :
    0 ≤ greenKernel N m hm ℓ ℓ := by
  have h1 : (∑ j, ((greenEquiv N m hm).symm (greenBasis ℓ)) j
        * (shiftedOp N m
          ((greenEquiv N m hm).symm (greenBasis ℓ))) j)
      = greenKernel N m hm ℓ ℓ := by
    have hSx : shiftedOp N m
          ((greenEquiv N m hm).symm (greenBasis ℓ))
        = greenBasis ℓ := by
      have h2 : shiftedOp N m ((greenEquiv N m hm).symm
            (greenBasis ℓ))
          = (greenEquiv N m hm) ((greenEquiv N m hm).symm
            (greenBasis ℓ)) := rfl
      rw [h2]
      exact LinearEquiv.apply_symm_apply _ _
    rw [hSx, sum_mul_greenBasis]
    rfl
  rw [← h1, shiftedOp_form_self]
  exact add_nonneg (maxwellQuad_nonneg _)
    (mul_nonneg (sq_nonneg m)
      (Finset.sum_nonneg (fun j _ => sq_nonneg _)))

end General

/-! ## Seat infrastructure: signs and characters on `ZMod 2` -/

section SeatSigns

/-- An element of `ZMod 2` is `0` or `1`. -/
theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : a.val = 0 ∨ a.val = 1 := by
    have h2 := ZMod.val_lt a
    omega
  rcases h with h | h
  · left
    exact zmod_eq_zero_of_val_eq_zero a h
  · right
    rw [← ZMod.natCast_zmod_val a, h]
    exact Nat.cast_one

/-- **The sign of a `ZMod 2` element**, as a real number:
`1` at `0`, `-1` at `1` - the character value `(-1)^a`. -/
def greenSgn (a : ZMod 2) : ℝ := if a = 0 then 1 else -1

/-- The sign at `0` is `1`. -/
theorem greenSgn_zero : greenSgn 0 = 1 := by simp [greenSgn]

/-- The sign at `1` is `-1`. -/
theorem greenSgn_one : greenSgn 1 = -1 := by
  simp [greenSgn, show (1 : ZMod 2) ≠ 0 by decide]

/-- The sign is `1` or `-1`. -/
theorem greenSgn_eq (a : ZMod 2) :
    greenSgn a = 1 ∨ greenSgn a = -1 := by
  rcases zmod2_cases a with rfl | rfl
  · exact Or.inl greenSgn_zero
  · exact Or.inr greenSgn_one

/-- The sign squares to `1`. -/
theorem greenSgn_sq (a : ZMod 2) : (greenSgn a) ^ 2 = 1 := by
  rcases greenSgn_eq a with h | h <;> rw [h] <;> norm_num

/-- The sign of a sum is the product of the signs
(the `ZMod 2` character law). -/
theorem greenSgn_add (x y : ZMod 2) :
    greenSgn (x + y) = greenSgn x * greenSgn y := by
  rcases zmod2_cases x with rfl | rfl <;>
    rcases zmod2_cases y with rfl | rfl <;>
    simp [greenSgn_zero, greenSgn_one,
      show (1 : ZMod 2) + 1 = 0 by decide]

/-- The sign law under a scalar factor:
`greenSgn (a * (x + y)) = greenSgn (a * x) * greenSgn (a * y)`. -/
theorem greenSgn_mul_add (a x y : ZMod 2) :
    greenSgn (a * (x + y)) = greenSgn (a * x) * greenSgn (a * y) := by
  rcases zmod2_cases a with rfl | rfl <;>
    rcases zmod2_cases x with rfl | rfl <;>
    rcases zmod2_cases y with rfl | rfl <;>
    simp [greenSgn_zero, greenSgn_one,
      show (1 : ZMod 2) + 1 = 0 by decide]

/-- The product of two character factors at the same
momentum: `greenSgn (a * x) * greenSgn (a * y)` is `1` when
`x = y` and `greenSgn a` otherwise. -/
theorem greenSgn_factor (a x y : ZMod 2) :
    greenSgn (a * x) * greenSgn (a * y)
      = if x = y then 1 else greenSgn a := by
  rcases zmod2_cases a with rfl | rfl <;>
    rcases zmod2_cases x with rfl | rfl <;>
    rcases zmod2_cases y with rfl | rfl <;>
    simp [greenSgn_zero, greenSgn_one,
      show (1 : ZMod 2) + 1 = 0 by decide]

/-- A sum over `ZMod 2` is the sum of its two values. -/
theorem sum_zmod2 (f : ZMod 2 → ℝ) :
    (∑ a : ZMod 2, f a) = f 0 + f 1 := by
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by
    decide
  rw [huniv, Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]

/-- The named site of the `N = 2` seat with spatial
coordinates `(a, b, c)`: time coordinate `0`, and Fin
coordinates `1, 2, 3` reading `a, b, c`. -/
def siteOf (a b c : ZMod 2) : LayerSite 2 :=
  ⟨fun i => if i = 1 then a else if i = 2 then b
    else if i = 3 then c else 0, by simp⟩

/-- The coordinates of a named site, read back. -/
theorem siteOf_coord (a b c : ZMod 2) (i : Fin 4) :
    (siteOf a b c).1 i
      = if i = 1 then a else if i = 2 then b
        else if i = 3 then c else 0 :=
  rfl

/-- **The coordinate equivalence** of the seat:
`LayerSite 2` is the triple of its spatial coordinates. -/
def siteEquiv : LayerSite 2 ≃ ZMod 2 × ZMod 2 × ZMod 2 where
  toFun k := (k.1 1, k.1 2, k.1 3)
  invFun t := siteOf t.1 t.2.1 t.2.2
  left_inv k := by
    have hk0 : k.1 0 = 0 := zmod_eq_zero_of_val_eq_zero (k.1 0) k.2
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [siteOf_coord, hk0]
  right_inv t := by
    obtain ⟨a, b, c⟩ := t
    simp [siteOf_coord]

end SeatSigns

/-! ## The seat candidate at `N = 2`, `m = 1` -/

section SeatCandidate

/-- **The character of the seat**: for momentum and site
`k s : LayerSite 2`, the product over the four coordinates
of the signs `greenSgn (k_i * s_i)` - the `ZMod 2` Fourier
character, real-valued. The time coordinate contributes
`1`, as every layer site has time coordinate `0`. -/
def greenChi (k s : LayerSite 2) : ℝ :=
  ∏ i : Fin 4, greenSgn ((k.1 i) * (s.1 i))

/-- **The momentum factor** `u_d(k) = 1 - greenSgn (k_d)`:
`0` when the momentum vanishes in direction `d`, `2` when
it does not. -/
def greenU (k : LayerSite 2) (d : Fin 4) : ℝ :=
  1 - greenSgn (k.1 d)

/-- The momentum factor in the time direction vanishes:
every momentum is a layer site, so its time coordinate
is `0`. -/
theorem greenU_time (k : LayerSite 2) : greenU k 0 = 0 := by
  unfold greenU
  rw [zmod_eq_zero_of_val_eq_zero (k.1 0) k.2, greenSgn_zero]
  norm_num

/-- The momentum factor squares to twice itself:
`(1 - s)^2 = 2 * (1 - s)` since `s^2 = 1` for a sign. -/
theorem greenU_sq (k : LayerSite 2) (d : Fin 4) :
    (greenU k d) ^ 2 = 2 * greenU k d := by
  unfold greenU
  have hs := greenSgn_sq (k.1 d)
  linear_combination hs

/-- **The shifted eigenvalue denominator at momentum `k`**:
`1 + ∑ i, u_i(k)^2` - this is `L_k + 1` with
`L_k = ∑ i, u_i(k)^2` the `maxwellOp 2` eigenvalue on the
transverse part of the `k`-block. It is at least `1`. -/
def greenDenom (k : LayerSite 2) : ℝ :=
  1 + ∑ i, (greenU k i) ^ 2

/-- The denominator is positive (it is `1` plus a sum of
squares). -/
theorem greenDenom_pos (k : LayerSite 2) :
    0 < greenDenom k := by
  unfold greenDenom
  have h : 0 ≤ ∑ i, (greenU k i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  linarith

/-- The denominator is nonzero. -/
theorem greenDenom_ne_zero (k : LayerSite 2) :
    greenDenom k ≠ 0 :=
  ne_of_gt (greenDenom_pos k)

/-- **The candidate Green kernel at the seat** (`N = 2`,
`m = 1`): the Fourier sum over the eight momenta of the
seat,
`(1/8) * ∑ k, chi_k(tail l) * chi_k(tail l') *
  (([l.dir = l'.dir] + u_{l.dir}(k) * u_{l'.dir}(k))
    / (L_k + 1))`.
This is the inverse of the shifted operator on each
momentum block: on the `k`-block the shifted operator is
`(L_k + 1) * I - u u^T` and this candidate is
`(I + u u^T) / (L_k + 1)`, its inverse there. The theorem
`shiftedOp_greenCand` verifies it against the operator
itself; no Fourier machinery is assumed. -/
noncomputable def greenCand (ℓ ℓ' : LayerLink 2) : ℝ :=
  (1 / 8) * ∑ k : LayerSite 2,
    greenChi k (linkTail ℓ) * greenChi k (linkTail ℓ')
      * (((if ℓ.1.2 = ℓ'.1.2 then (1 : ℝ) else 0)
          + greenU k ℓ.1.2 * greenU k ℓ'.1.2)
        / greenDenom k)

/-- **Character shift law**: shifting the site by one step
in a spatial direction `ν` multiplies the character by the
sign of the momentum in that direction. -/
theorem greenChi_shift (k s : LayerSite 2) (ν : Fin 4)
    (hν : ν ≠ 0) :
    greenChi k (layerShift ν hν s)
      = greenChi k s * greenSgn (k.1 ν) := by
  have h1 : ∀ i : Fin 4,
      greenSgn ((k.1 i) * ((layerShift ν hν s).1 i))
        = greenSgn ((k.1 i)
            * (Pi.single ν 1 : Fin 4 → ZMod 2) i)
          * greenSgn ((k.1 i) * (s.1 i)) := by
    intro i
    rw [layerShift_coord hν s i, mul_add]
    exact greenSgn_add _ _
  have step1 : (∏ i : Fin 4,
        greenSgn ((k.1 i) * ((layerShift ν hν s).1 i)))
      = ∏ i : Fin 4,
        (greenSgn ((k.1 i)
            * (Pi.single ν 1 : Fin 4 → ZMod 2) i)
          * greenSgn ((k.1 i) * (s.1 i))) :=
    Finset.prod_congr rfl (fun i _ => h1 i)
  have hsingle : (∏ i : Fin 4, greenSgn ((k.1 i)
        * (Pi.single ν 1 : Fin 4 → ZMod 2) i))
      = greenSgn (k.1 ν) := by
    rw [Finset.prod_eq_single ν]
    · rw [Pi.single_eq_same, mul_one]
    · intro i _ hi
      rw [Pi.single_eq_of_ne hi, mul_zero]
      exact greenSgn_zero
    · intro h
      exact absurd (Finset.mem_univ ν) h
  unfold greenChi
  rw [step1, Finset.prod_mul_distrib, hsingle, mul_comm]

end SeatCandidate

section SeatOrthogonality

/-- In `ZMod 2`, `x + x = 0`. -/
theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_cases x with rfl | rfl <;> decide

/-- In `ZMod 2`, `x + y = 0` forces `x = y`. -/
theorem zmod2_add_eq_zero {x y : ZMod 2} (h : x + y = 0) :
    x = y := by
  rcases zmod2_cases x with rfl | rfl <;>
    rcases zmod2_cases y with rfl | rfl <;>
    simp_all [show (1 : ZMod 2) + 1 = 0 by decide]

/-- One momentum-coordinate character sum:
`∑ a : ZMod 2, greenSgn (a * t)` is `2` at `t = 0` and
`0` otherwise. -/
theorem greenSgn_sum (t : ZMod 2) :
    (∑ a : ZMod 2, greenSgn (a * t)) = if t = 0 then 2 else 0 := by
  rw [sum_zmod2, zero_mul, greenSgn_zero, one_mul]
  by_cases ht : t = 0
  · rw [if_pos ht, ht, greenSgn_zero]
    norm_num
  · rw [if_neg ht]
    have ht1 : t = 1 := by
      rcases zmod2_cases t with h | h
      · exact absurd h ht
      · exact h
    rw [ht1, greenSgn_one]
    norm_num

/-- **Character orthogonality at the seat**:
`∑ k, greenChi k s * greenChi k s' = 8` when `s = s'`, and
`0` otherwise - the `ZMod 2` Fourier orthogonality on the
eight sites of the seat, proved by factoring the sum over
the three spatial coordinates of the momentum. -/
theorem greenChi_sum (s s' : LayerSite 2) :
    (∑ k : LayerSite 2, greenChi k s * greenChi k s')
      = if s = s' then 8 else 0 := by
  have hfac : ∀ k : LayerSite 2, greenChi k s * greenChi k s'
      = ∏ i : Fin 4, greenSgn ((k.1 i) * (s.1 i + s'.1 i)) := by
    intro k
    unfold greenChi
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    exact (greenSgn_mul_add _ _ _).symm
  have step1 : (∑ k : LayerSite 2, greenChi k s * greenChi k s')
      = ∑ k : LayerSite 2, ∏ i : Fin 4,
          greenSgn ((k.1 i) * (s.1 i + s'.1 i)) :=
    Finset.sum_congr rfl (fun k _ => hfac k)
  have htime : ∀ k : LayerSite 2,
      greenSgn ((k.1 0) * (s.1 0 + s'.1 0)) = 1 := by
    intro k
    rw [zmod_eq_zero_of_val_eq_zero (k.1 0) k.2, zero_mul]
    exact greenSgn_zero
  have step2 : ∀ k : LayerSite 2,
      (∏ i : Fin 4, greenSgn ((k.1 i) * (s.1 i + s'.1 i)))
        = greenSgn ((k.1 1) * (s.1 1 + s'.1 1))
          * (greenSgn ((k.1 2) * (s.1 2 + s'.1 2))
            * greenSgn ((k.1 3) * (s.1 3 + s'.1 3))) := by
    intro k
    rw [Fin.prod_univ_four, htime k, one_mul, mul_assoc]
  have step2' : (∑ k : LayerSite 2, ∏ i : Fin 4,
        greenSgn ((k.1 i) * (s.1 i + s'.1 i)))
      = ∑ k : LayerSite 2,
        greenSgn ((k.1 1) * (s.1 1 + s'.1 1))
          * (greenSgn ((k.1 2) * (s.1 2 + s'.1 2))
            * greenSgn ((k.1 3) * (s.1 3 + s'.1 3))) :=
    Finset.sum_congr rfl (fun k _ => step2 k)
  have step3 : (∑ k : LayerSite 2,
        greenSgn ((k.1 1) * (s.1 1 + s'.1 1))
          * (greenSgn ((k.1 2) * (s.1 2 + s'.1 2))
            * greenSgn ((k.1 3) * (s.1 3 + s'.1 3))))
      = ∑ t : ZMod 2 × ZMod 2 × ZMod 2,
        greenSgn (t.1 * (s.1 1 + s'.1 1))
          * (greenSgn (t.2.1 * (s.1 2 + s'.1 2))
            * greenSgn (t.2.2 * (s.1 3 + s'.1 3))) :=
    siteEquiv.sum_comp (fun t : ZMod 2 × ZMod 2 × ZMod 2 =>
      greenSgn (t.1 * (s.1 1 + s'.1 1))
        * (greenSgn (t.2.1 * (s.1 2 + s'.1 2))
          * greenSgn (t.2.2 * (s.1 3 + s'.1 3))))
  have step4 : (∑ t : ZMod 2 × ZMod 2 × ZMod 2,
        greenSgn (t.1 * (s.1 1 + s'.1 1))
          * (greenSgn (t.2.1 * (s.1 2 + s'.1 2))
            * greenSgn (t.2.2 * (s.1 3 + s'.1 3))))
      = (∑ a : ZMod 2, greenSgn (a * (s.1 1 + s'.1 1)))
        * ((∑ b : ZMod 2, greenSgn (b * (s.1 2 + s'.1 2)))
          * (∑ c : ZMod 2, greenSgn (c * (s.1 3 + s'.1 3)))) := by
    rw [Fintype.sum_prod_type]
    dsimp only
    rw [← Finset.sum_mul_sum, Fintype.sum_prod_type]
    dsimp only
    rw [← Finset.sum_mul_sum]
  have hprod : (∑ k : LayerSite 2, greenChi k s * greenChi k s')
      = (if s.1 1 + s'.1 1 = 0 then (2 : ℝ) else 0)
        * ((if s.1 2 + s'.1 2 = 0 then (2 : ℝ) else 0)
          * (if s.1 3 + s'.1 3 = 0 then (2 : ℝ) else 0)) := by
    rw [step1, step2', step3, step4, greenSgn_sum, greenSgn_sum,
      greenSgn_sum]
  have ht1 : (s.1 1 + s'.1 1 = 0) ↔ s.1 1 = s'.1 1 :=
    ⟨fun h => zmod2_add_eq_zero h, fun h => by
      rw [← h]; exact zmod2_add_self _⟩
  have ht2 : (s.1 2 + s'.1 2 = 0) ↔ s.1 2 = s'.1 2 :=
    ⟨fun h => zmod2_add_eq_zero h, fun h => by
      rw [← h]; exact zmod2_add_self _⟩
  have ht3 : (s.1 3 + s'.1 3 = 0) ↔ s.1 3 = s'.1 3 :=
    ⟨fun h => zmod2_add_eq_zero h, fun h => by
      rw [← h]; exact zmod2_add_self _⟩
  have hseq : s = s' ↔ s.1 1 = s'.1 1 ∧ s.1 2 = s'.1 2
      ∧ s.1 3 = s'.1 3 := by
    constructor
    · intro h
      exact ⟨by rw [h], by rw [h], by rw [h]⟩
    · rintro ⟨h1, h2, h3⟩
      apply Subtype.ext
      funext i
      fin_cases i
      · show s.1 0 = s'.1 0
        rw [zmod_eq_zero_of_val_eq_zero (s.1 0) s.2,
          zmod_eq_zero_of_val_eq_zero (s'.1 0) s'.2]
      · exact h1
      · exact h2
      · exact h3
  have e1 : (if s.1 1 + s'.1 1 = 0 then (2 : ℝ) else 0)
      = if s.1 1 = s'.1 1 then 2 else 0 := by
    by_cases h : s.1 1 = s'.1 1
    · rw [if_pos h, if_pos (ht1.mpr h)]
    · rw [if_neg h, if_neg (fun hh => h (ht1.mp hh))]
  have e2 : (if s.1 2 + s'.1 2 = 0 then (2 : ℝ) else 0)
      = if s.1 2 = s'.1 2 then 2 else 0 := by
    by_cases h : s.1 2 = s'.1 2
    · rw [if_pos h, if_pos (ht2.mpr h)]
    · rw [if_neg h, if_neg (fun hh => h (ht2.mp hh))]
  have e3 : (if s.1 3 + s'.1 3 = 0 then (2 : ℝ) else 0)
      = if s.1 3 = s'.1 3 then 2 else 0 := by
    by_cases h : s.1 3 = s'.1 3
    · rw [if_pos h, if_pos (ht3.mpr h)]
    · rw [if_neg h, if_neg (fun hh => h (ht3.mp hh))]
  rw [hprod, e1, e2, e3]
  by_cases h1 : s.1 1 = s'.1 1 <;> by_cases h2 : s.1 2 = s'.1 2 <;>
    by_cases h3 : s.1 3 = s'.1 3
  · rw [if_pos h1, if_pos h2, if_pos h3,
      if_pos (hseq.mpr ⟨h1, h2, h3⟩)]
    norm_num
  · rw [if_pos h1, if_pos h2, if_neg h3,
      if_neg (fun h => h3 (hseq.mp h).2.2)]
    norm_num
  · rw [if_pos h1, if_neg h2, if_pos h3,
      if_neg (fun h => h2 (hseq.mp h).2.1)]
    norm_num
  · rw [if_pos h1, if_neg h2, if_neg h3,
      if_neg (fun h => h2 (hseq.mp h).2.1)]
    norm_num
  · rw [if_neg h1, if_pos h2, if_pos h3,
      if_neg (fun h => h1 (hseq.mp h).1)]
    norm_num
  · rw [if_neg h1, if_pos h2, if_neg h3,
      if_neg (fun h => h1 (hseq.mp h).1)]
    norm_num
  · rw [if_neg h1, if_neg h2, if_pos h3,
      if_neg (fun h => h1 (hseq.mp h).1)]
    norm_num
  · rw [if_neg h1, if_neg h2, if_neg h3,
      if_neg (fun h => h1 (hseq.mp h).1)]
    norm_num

end SeatOrthogonality

section PlaqAngleCand

/-- **The plaquette bracket of the candidate**: the
per-momentum combination
`chi c * chi s' * ([u_nu * delta_mu - u_mu * delta_nu] / D)`
that the plaquette angle of a candidate column will be
shown to equal. `plaqBk k l' c mu nu` is the bracket at
plaquette datum `(c, mu, nu)`. -/
noncomputable def plaqBk (k : LayerSite 2) (ℓ' : LayerLink 2)
    (c : LayerSite 2) (μ ν : Fin 4) : ℝ :=
  greenChi k c * greenChi k (linkTail ℓ')
    * ((greenU k ν * (if μ = ℓ'.1.2 then (1 : ℝ) else 0)
        - greenU k μ * (if ν = ℓ'.1.2 then (1 : ℝ) else 0))
      / greenDenom k)

/-- **The bracket identity**: the four edge contributions
of one momentum to a plaquette angle - bottom and left at
the base, right and top at the shifted corners, with the
character shift factors - collapse to the bracket
`[u_nu * delta_mu - u_mu * delta_nu] / D`: the
`u`-cross-terms cancel, since `u_mu * u_nu` appears with
both signs. -/
theorem greenCoeff_bracket (k : LayerSite 2) (ℓ' : LayerLink 2)
    (μ ν : Fin 4) :
    ((if μ = ℓ'.1.2 then (1 : ℝ) else 0)
        + greenU k μ * greenU k ℓ'.1.2) / greenDenom k
      + greenSgn (k.1 μ)
        * (((if ν = ℓ'.1.2 then (1 : ℝ) else 0)
            + greenU k ν * greenU k ℓ'.1.2) / greenDenom k)
      - greenSgn (k.1 ν)
        * (((if μ = ℓ'.1.2 then (1 : ℝ) else 0)
            + greenU k μ * greenU k ℓ'.1.2) / greenDenom k)
      - ((if ν = ℓ'.1.2 then (1 : ℝ) else 0)
          + greenU k ν * greenU k ℓ'.1.2) / greenDenom k
    = (greenU k ν * (if μ = ℓ'.1.2 then (1 : ℝ) else 0)
        - greenU k μ * (if ν = ℓ'.1.2 then (1 : ℝ) else 0))
      / greenDenom k := by
  have hD := greenDenom_ne_zero k
  field_simp
  unfold greenU
  ring

/-- The candidate column at the bottom edge of a
plaquette: the base-tail, `mu`-direction term. -/
theorem greenCand_plaqEdgeB (P : PlaqDatum 2) (ℓ' : LayerLink 2) :
    greenCand (plaqEdgeB P) ℓ'
      = (1 / 8) * ∑ k : LayerSite 2,
        greenChi k P.base * greenChi k (linkTail ℓ')
          * (((if P.mu = ℓ'.1.2 then (1 : ℝ) else 0)
              + greenU k P.mu * greenU k ℓ'.1.2)
            / greenDenom k) := by
  unfold greenCand
  congr 1

/-- The candidate column at the right edge of a plaquette:
the `mu`-shifted tail (character shift factor
`greenSgn (k_mu)`), `nu`-direction term. -/
theorem greenCand_plaqEdgeR (P : PlaqDatum 2) (ℓ' : LayerLink 2) :
    greenCand (plaqEdgeR P) ℓ'
      = (1 / 8) * ∑ k : LayerSite 2,
        (greenChi k P.base * greenSgn (k.1 P.mu))
          * greenChi k (linkTail ℓ')
          * (((if P.nu = ℓ'.1.2 then (1 : ℝ) else 0)
              + greenU k P.nu * greenU k ℓ'.1.2)
            / greenDenom k) := by
  unfold greenCand
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have h1 : linkTail (plaqEdgeR P)
      = layerShift P.mu P.hmu P.base := linkTail_plaqEdgeR P
  have h2 : (plaqEdgeR P).1.2 = P.nu := rfl
  rw [h1, greenChi_shift, h2]

/-- The candidate column at the top edge of a plaquette:
the `nu`-shifted tail (character shift factor
`greenSgn (k_nu)`), `mu`-direction term. -/
theorem greenCand_plaqEdgeT (P : PlaqDatum 2) (ℓ' : LayerLink 2) :
    greenCand (plaqEdgeT P) ℓ'
      = (1 / 8) * ∑ k : LayerSite 2,
        (greenChi k P.base * greenSgn (k.1 P.nu))
          * greenChi k (linkTail ℓ')
          * (((if P.mu = ℓ'.1.2 then (1 : ℝ) else 0)
              + greenU k P.mu * greenU k ℓ'.1.2)
            / greenDenom k) := by
  unfold greenCand
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have h1 : linkTail (plaqEdgeT P)
      = layerShift P.nu P.hnu P.base := linkTail_plaqEdgeT P
  have h2 : (plaqEdgeT P).1.2 = P.mu := rfl
  rw [h1, greenChi_shift, h2]

/-- The candidate column at the left edge of a plaquette:
the base-tail, `nu`-direction term. -/
theorem greenCand_plaqEdgeL (P : PlaqDatum 2) (ℓ' : LayerLink 2) :
    greenCand (plaqEdgeL P) ℓ'
      = (1 / 8) * ∑ k : LayerSite 2,
        greenChi k P.base * greenChi k (linkTail ℓ')
          * (((if P.nu = ℓ'.1.2 then (1 : ℝ) else 0)
              + greenU k P.nu * greenU k ℓ'.1.2)
            / greenDenom k) := by
  unfold greenCand
  congr 1

/-- **The plaquette angle of a candidate column** is the
momentum sum of the plaquette bracket: the four edge terms
combine over the momentum sum, and the bracket identity
collapses each momentum's contribution. -/
theorem plaqAngle_greenCand (P : PlaqDatum 2) (ℓ' : LayerLink 2) :
    plaqAngle P (fun ℓ => greenCand ℓ ℓ')
      = (1 / 8) * ∑ k : LayerSite 2,
        plaqBk k ℓ' P.base P.mu P.nu := by
  have hcomb : ∀ (f g : LayerSite 2 → ℝ),
      (1 / 8 : ℝ) * (∑ k, f k) + (1 / 8) * (∑ k, g k)
        = (1 / 8) * ∑ k, (f k + g k) := by
    intro f g
    have h : (1 / 8 : ℝ) * (∑ k, f k) + (1 / 8) * (∑ k, g k)
        = (1 / 8) * ((∑ k, f k) + (∑ k, g k)) := by ring
    rw [h, Finset.sum_add_distrib]
  have hcomb' : ∀ (f g : LayerSite 2 → ℝ),
      (1 / 8 : ℝ) * (∑ k, f k) - (1 / 8) * (∑ k, g k)
        = (1 / 8) * ∑ k, (f k - g k) := by
    intro f g
    have h : (1 / 8 : ℝ) * (∑ k, f k) - (1 / 8) * (∑ k, g k)
        = (1 / 8) * ((∑ k, f k) - (∑ k, g k)) := by ring
    rw [h, Finset.sum_sub_distrib]
  show greenCand (plaqEdgeB P) ℓ' + greenCand (plaqEdgeR P) ℓ'
      - greenCand (plaqEdgeT P) ℓ' - greenCand (plaqEdgeL P) ℓ'
    = (1 / 8) * ∑ k : LayerSite 2,
      plaqBk k ℓ' P.base P.mu P.nu
  rw [greenCand_plaqEdgeB, greenCand_plaqEdgeR,
    greenCand_plaqEdgeT, greenCand_plaqEdgeL, hcomb, hcomb',
    hcomb']
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have hb := greenCoeff_bracket k ℓ' P.mu P.nu
  unfold plaqBk
  rw [← hb]
  ring

end PlaqAngleCand


section OperatorAction

/-- **The extended plaquette sign**: the sign of a link
`l` in the plaquette `(c, mu, nu)`, extended to ALL
direction pairs `(mu, nu)` (no datum hypotheses): `+1` on
the bottom and right edges, `-1` on the top and left
edges, `0` elsewhere, read off the link's underlying
lattice link `(tail, direction)`. For an actual datum it
agrees with the pin's `plaqSign` (next lemma); the
extension is what makes the `(mu, nu)`-symmetry of the
operator computation visible. -/
noncomputable def plaqEsign (ℓ : LayerLink 2) (c : LayerSite 2)
    (μ ν : Fin 4) : ℝ :=
  (if ℓ.1 = (c.1, μ) then (1 : ℝ) else 0)
    + (if ℓ.1 = (torusShift 2 μ c.1, ν) then (1 : ℝ) else 0)
    - (if ℓ.1 = (torusShift 2 ν c.1, μ) then (1 : ℝ) else 0)
    - (if ℓ.1 = (c.1, ν) then (1 : ℝ) else 0)

/-- The extended sign at an actual plaquette datum is the
pin's `plaqSign`: each edge of the datum has the
underlying link used in the extension (bottom `(c, mu)`,
right `(shift_mu c, nu)`, top `(shift_nu c, mu)`, left
`(c, nu)`). -/
theorem plaqSign_esig (P : PlaqDatum 2) (ℓ : LayerLink 2) :
    plaqSign P ℓ = plaqEsign ℓ P.base P.mu P.nu := by
  have eB : (ℓ = plaqEdgeB P) ↔ ℓ.1 = (P.base.1, P.mu) := by
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      exact Subtype.ext h
  have eR : (ℓ = plaqEdgeR P)
      ↔ ℓ.1 = (torusShift 2 P.mu P.base.1, P.nu) := by
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      exact Subtype.ext h
  have eT : (ℓ = plaqEdgeT P)
      ↔ ℓ.1 = (torusShift 2 P.nu P.base.1, P.mu) := by
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      exact Subtype.ext h
  have eL : (ℓ = plaqEdgeL P) ↔ ℓ.1 = (P.base.1, P.nu) := by
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      exact Subtype.ext h
  unfold plaqSign plaqEsign
  simp only [eB, eR, eT, eL]

/-- The extended sign is antisymmetric in the direction
pair: swapping `(mu, nu)` swaps bottom with left and
right with top, with signs. -/
theorem plaqEsign_swap (ℓ : LayerLink 2) (c : LayerSite 2)
    (μ ν : Fin 4) :
    plaqEsign ℓ c ν μ = -plaqEsign ℓ c μ ν := by
  unfold plaqEsign
  ring

/-- The extended sign vanishes on the diagonal direction
pair: bottom cancels left and right cancels top. -/
theorem plaqEsign_diag (ℓ : LayerLink 2) (c : LayerSite 2)
    (μ : Fin 4) :
    plaqEsign ℓ c μ μ = 0 := by
  unfold plaqEsign
  ring

/-- **The rest factor of the bracket**: `plaqBk` with the
base character factored out,
`plaqBk k l' c mu nu = greenChi k c * plaqRest k l' mu nu`. -/
noncomputable def plaqRest (k : LayerSite 2) (ℓ' : LayerLink 2)
    (μ ν : Fin 4) : ℝ :=
  greenChi k (linkTail ℓ')
    * ((greenU k ν * (if μ = ℓ'.1.2 then (1 : ℝ) else 0)
        - greenU k μ * (if ν = ℓ'.1.2 then (1 : ℝ) else 0))
      / greenDenom k)

/-- The bracket factors through the rest factor. -/
theorem plaqBk_eq (k : LayerSite 2) (ℓ' : LayerLink 2)
    (c : LayerSite 2) (μ ν : Fin 4) :
    plaqBk k ℓ' c μ ν = greenChi k c * plaqRest k ℓ' μ ν := by
  unfold plaqBk plaqRest
  ring

/-- The bracket is antisymmetric in the direction pair. -/
theorem plaqBk_swap (k : LayerSite 2) (ℓ' : LayerLink 2)
    (c : LayerSite 2) (μ ν : Fin 4) :
    plaqBk k ℓ' c ν μ = -plaqBk k ℓ' c μ ν := by
  unfold plaqBk
  ring

/-- The rest factor vanishes at `mu = 0`: both bracket
terms die - the direction indicator of `0` against the
link direction `l'.2` (which is nonzero) and the time
momentum factor `greenU k 0 = 0`. -/
theorem plaqRest_zero_mu (k : LayerSite 2) (ℓ' : LayerLink 2)
    (ν : Fin 4) :
    plaqRest k ℓ' 0 ν = 0 := by
  unfold plaqRest
  rw [greenU_time, if_neg (fun h : (0 : Fin 4) = ℓ'.1.2 =>
    ℓ'.2.2 h.symm)]
  ring

/-- The rest factor vanishes at `nu = 0`, by the same two
facts. -/
theorem plaqRest_zero_nu (k : LayerSite 2) (ℓ' : LayerLink 2)
    (μ : Fin 4) :
    plaqRest k ℓ' μ 0 = 0 := by
  unfold plaqRest
  rw [greenU_time, if_neg (fun h : (0 : Fin 4) = ℓ'.1.2 =>
    ℓ'.2.2 h.symm)]
  ring

/-- The product `H k l l' c mu nu = plaqEsign * plaqBk`
(the summand of the operator computation at fixed
momentum) is symmetric in the direction pair: both
factors are antisymmetric. -/
theorem plaqH_symm (k : LayerSite 2) (ℓ ℓ' : LayerLink 2)
    (c : LayerSite 2) (μ ν : Fin 4) :
    plaqEsign ℓ c μ ν * plaqBk k ℓ' c μ ν
      = plaqEsign ℓ c ν μ * plaqBk k ℓ' c ν μ := by
  rw [plaqEsign_swap, plaqBk_swap]
  ring

/-- The product `H` vanishes on the diagonal direction
pair (the extended sign does). -/
theorem plaqH_diag (k : LayerSite 2) (ℓ ℓ' : LayerLink 2)
    (c : LayerSite 2) (μ : Fin 4) :
    plaqEsign ℓ c μ μ * plaqBk k ℓ' c μ μ = 0 := by
  rw [plaqEsign_diag, zero_mul]

/-- The product `H` vanishes when either direction is
`0` (the bracket's rest factor does). -/
theorem plaqH_zero (k : LayerSite 2) (ℓ ℓ' : LayerLink 2)
    (c : LayerSite 2) (μ ν : Fin 4) (h : μ = 0 ∨ ν = 0) :
    plaqEsign ℓ c μ ν * plaqBk k ℓ' c μ ν = 0 := by
  rcases h with rfl | rfl
  · rw [plaqBk_eq, plaqRest_zero_mu, mul_zero, mul_zero]
  · rw [plaqBk_eq, plaqRest_zero_nu, mul_zero, mul_zero]

end OperatorAction


section PlaqSumDecomp

/-- **The plaquette-enumeration sum, decomposed**: a sum
over `allPlaqData 2` is the triple sum over base sites and
ordered direction pairs `mu < nu` (both nonzero), with the
datum rebuilt from the triple. Proved by unfolding the
pin's `biUnion` enumeration and applying
`Finset.sum_biUnion` at each of the three levels; the
disjointness at each level is the injectivity of the
datum's `(base, mu, nu)` projections. -/
theorem allPlaqData_sum (F : PlaqDatum 2 → ℝ) :
    (∑ P ∈ allPlaqData 2, F P)
      = ∑ c : LayerSite 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
        if h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
          then F ⟨c, μ, ν, h.1, h.2.1, ne_of_lt h.2.2⟩
          else 0 := by
  classical
  have disjν : ∀ (c : LayerSite 2) (μ ν₁ ν₂ : Fin 4),
      ν₁ ≠ ν₂ →
      Disjoint
        (if h : μ ≠ 0 ∧ ν₁ ≠ 0 ∧ μ < ν₁ then
          ({⟨c, μ, ν₁, h.1, h.2.1, ne_of_lt h.2.2⟩} : Finset (PlaqDatum 2)) else ∅)
        (if h : μ ≠ 0 ∧ ν₂ ≠ 0 ∧ μ < ν₂ then
          ({⟨c, μ, ν₂, h.1, h.2.1, ne_of_lt h.2.2⟩} : Finset (PlaqDatum 2)) else ∅) := by
    intro c μ ν₁ ν₂ hne
    rw [Finset.disjoint_left]
    intro P hP₁ hP₂
    by_cases h₁ : μ ≠ 0 ∧ ν₁ ≠ 0 ∧ μ < ν₁ <;>
      by_cases h₂ : μ ≠ 0 ∧ ν₂ ≠ 0 ∧ μ < ν₂
    · rw [dif_pos h₁, Finset.mem_singleton] at hP₁
      rw [dif_pos h₂, Finset.mem_singleton] at hP₂
      exact hne (congrArg PlaqDatum.nu (hP₁.symm.trans hP₂))
    · rw [dif_neg h₂] at hP₂
      exact absurd hP₂ (Finset.notMem_empty P)
    · rw [dif_neg h₁] at hP₁
      exact absurd hP₁ (Finset.notMem_empty P)
    · rw [dif_neg h₁] at hP₁
      exact absurd hP₁ (Finset.notMem_empty P)
  have disjμ : ∀ (c : LayerSite 2) (μ₁ μ₂ : Fin 4),
      μ₁ ≠ μ₂ →
      Disjoint
        (Finset.univ.biUnion (fun ν : Fin 4 =>
          if h : μ₁ ≠ 0 ∧ ν ≠ 0 ∧ μ₁ < ν then
            ({⟨c, μ₁, ν, h.1, h.2.1, ne_of_lt h.2.2⟩} : Finset (PlaqDatum 2)) else ∅))
        (Finset.univ.biUnion (fun ν : Fin 4 =>
          if h : μ₂ ≠ 0 ∧ ν ≠ 0 ∧ μ₂ < ν then
            ({⟨c, μ₂, ν, h.1, h.2.1, ne_of_lt h.2.2⟩} : Finset (PlaqDatum 2)) else ∅)) := by
    intro c μ₁ μ₂ hne
    rw [Finset.disjoint_left]
    intro P hP₁ hP₂
    obtain ⟨ν₁, -, hν₁⟩ := Finset.mem_biUnion.mp hP₁
    obtain ⟨ν₂, -, hν₂⟩ := Finset.mem_biUnion.mp hP₂
    by_cases h₁ : μ₁ ≠ 0 ∧ ν₁ ≠ 0 ∧ μ₁ < ν₁ <;>
      by_cases h₂ : μ₂ ≠ 0 ∧ ν₂ ≠ 0 ∧ μ₂ < ν₂
    · rw [dif_pos h₁, Finset.mem_singleton] at hν₁
      rw [dif_pos h₂, Finset.mem_singleton] at hν₂
      exact hne (congrArg PlaqDatum.mu (hν₁.symm.trans hν₂))
    · rw [dif_neg h₂] at hν₂
      exact absurd hν₂ (Finset.notMem_empty P)
    · rw [dif_neg h₁] at hν₁
      exact absurd hν₁ (Finset.notMem_empty P)
    · rw [dif_neg h₁] at hν₁
      exact absurd hν₁ (Finset.notMem_empty P)
  have disjc : ∀ (c₁ c₂ : LayerSite 2), c₁ ≠ c₂ →
      Disjoint
        (Finset.univ.biUnion (fun μ : Fin 4 =>
          Finset.univ.biUnion (fun ν : Fin 4 =>
            if h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν then
              ({⟨c₁, μ, ν, h.1, h.2.1, ne_of_lt h.2.2⟩} : Finset (PlaqDatum 2)) else ∅)))
        (Finset.univ.biUnion (fun μ : Fin 4 =>
          Finset.univ.biUnion (fun ν : Fin 4 =>
            if h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν then
              ({⟨c₂, μ, ν, h.1, h.2.1, ne_of_lt h.2.2⟩} : Finset (PlaqDatum 2)) else ∅))) := by
    intro c₁ c₂ hne
    rw [Finset.disjoint_left]
    intro P hP₁ hP₂
    obtain ⟨μ₁, -, hμ₁⟩ := Finset.mem_biUnion.mp hP₁
    obtain ⟨ν₁, -, hν₁⟩ := Finset.mem_biUnion.mp hμ₁
    obtain ⟨μ₂, -, hμ₂⟩ := Finset.mem_biUnion.mp hP₂
    obtain ⟨ν₂, -, hν₂⟩ := Finset.mem_biUnion.mp hμ₂
    by_cases h₁ : μ₁ ≠ 0 ∧ ν₁ ≠ 0 ∧ μ₁ < ν₁ <;>
      by_cases h₂ : μ₂ ≠ 0 ∧ ν₂ ≠ 0 ∧ μ₂ < ν₂
    · rw [dif_pos h₁, Finset.mem_singleton] at hν₁
      rw [dif_pos h₂, Finset.mem_singleton] at hν₂
      exact hne (congrArg PlaqDatum.base (hν₁.symm.trans hν₂))
    · rw [dif_neg h₂] at hν₂
      exact absurd hν₂ (Finset.notMem_empty P)
    · rw [dif_neg h₁] at hν₁
      exact absurd hν₁ (Finset.notMem_empty P)
    · rw [dif_neg h₁] at hν₁
      exact absurd hν₁ (Finset.notMem_empty P)
  unfold allPlaqData
  rw [Finset.sum_biUnion (fun c₁ _ c₂ _ h => disjc c₁ c₂ h)]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_biUnion (fun μ₁ _ μ₂ _ h => disjμ c μ₁ μ₂ h)]
  apply Finset.sum_congr rfl
  intro μ _
  rw [Finset.sum_biUnion (fun ν₁ _ ν₂ _ h => disjν c μ ν₁ ν₂ h)]
  apply Finset.sum_congr rfl
  intro ν _
  by_cases h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν <;> simp [h]

end PlaqSumDecomp


section Doubling

/-- **Doubling**: for a `(mu, nu)`-symmetric family `H`
vanishing on the diagonal and at `mu = 0`, the ordered
triple sum of `H` over `mu < nu` (both nonzero) is half the
full triple sum. The `mu = 0` / `nu = 0` vanishing is what
makes the ordered sum with the nonzero side conditions
equal the plain `mu < nu` sum. -/
theorem dite_triple_double (H : LayerSite 2 → Fin 4 → Fin 4 → ℝ)
    (hsymm : ∀ c μ ν, H c ν μ = H c μ ν)
    (hdiag : ∀ c μ, H c μ μ = 0)
    (hzero : ∀ c ν, H c 0 ν = 0) :
    (∑ c : LayerSite 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
      if h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν then H c μ ν else 0)
      = (1 / 2) * ∑ c : LayerSite 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
        H c μ ν := by
  have stepA : ∀ c μ ν,
      (if h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν then H c μ ν else 0)
        = if μ < ν then H c μ ν else 0 := by
    intro c μ ν
    by_cases hμ : μ = 0
    · subst hμ
      by_cases hν : ν = 0
      · subst hν
        simp
      · rw [dif_neg (fun h => h.1 rfl),
          if_pos (Fin.pos_iff_ne_zero.mpr hν), hzero]
    · by_cases hν : ν = 0
      · subst hν
        rw [dif_neg (fun h => h.2.1 rfl), if_neg (by simp)]
      · by_cases hlt : μ < ν
        · rw [dif_pos ⟨hμ, hν, hlt⟩, if_pos hlt]
        · rw [dif_neg (fun h => hlt h.2.2), if_neg hlt]
  have point3 : ∀ c μ ν, H c μ ν
      = (if μ < ν then H c μ ν else 0)
        + (if ν < μ then H c μ ν else 0) := by
    intro c μ ν
    by_cases h1 : μ < ν
    · rw [if_pos h1,
        if_neg (fun h2 => absurd (lt_trans h2 h1) (lt_irrefl ν)),
        add_zero]
    · by_cases h2 : ν < μ
      · rw [if_neg h1, if_pos h2, zero_add]
      · have hμν : μ = ν :=
          le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
        subst hμν
        rw [if_neg (lt_irrefl μ), hdiag, add_zero]
  have split3 : ∀ c : LayerSite 2,
      (∑ μ : Fin 4, ∑ ν : Fin 4, H c μ ν)
        = (∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then H c μ ν else 0)
          + (∑ μ : Fin 4, ∑ ν : Fin 4,
            if ν < μ then H c μ ν else 0) := by
    intro c
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro μ _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ν _
    exact point3 c μ ν
  have gteq : ∀ c : LayerSite 2,
      (∑ μ : Fin 4, ∑ ν : Fin 4, if ν < μ then H c μ ν else 0)
        = ∑ μ : Fin 4, ∑ ν : Fin 4,
          if μ < ν then H c μ ν else 0 := by
    intro c
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ν _
    apply Finset.sum_congr rfl
    intro μ _
    by_cases h : ν < μ
    · rw [if_pos h, if_pos h, hsymm]
    · rw [if_neg h, if_neg h]
  have full2 : ∀ c : LayerSite 2,
      (∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then H c μ ν else 0)
        + (∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then H c μ ν else 0)
        = ∑ μ : Fin 4, ∑ ν : Fin 4, H c μ ν := by
    intro c
    rw [split3 c, gteq c]
  have e1 : (∑ c : LayerSite 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
        if h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν then H c μ ν else 0)
      = ∑ c : LayerSite 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
        if μ < ν then H c μ ν else 0 :=
    Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl
      (fun μ _ => Finset.sum_congr rfl (fun ν _ => stepA c μ ν)))
  rw [e1,
    show (∑ c : LayerSite 2, ∑ μ : Fin 4, ∑ ν : Fin 4, H c μ ν)
        = ∑ c : LayerSite 2, ((∑ μ : Fin 4, ∑ ν : Fin 4,
            if μ < ν then H c μ ν else 0)
          + (∑ μ : Fin 4, ∑ ν : Fin 4,
            if μ < ν then H c μ ν else 0))
      from Finset.sum_congr rfl (fun c _ => (full2 c).symm),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

end Doubling


section ShiftTools

/-- **Double shift is the identity at `N = 2`**: shifting
one coordinate twice adds `1 + 1 = 0` in `ZMod 2`. -/
theorem torusShift_two (μ : Fin 4) (x : Fin 4 → ZMod 2) :
    torusShift 2 μ (torusShift 2 μ x) = x := by
  rw [torusShift_apply, torusShift_apply]
  funext j
  rw [Pi.add_apply, Pi.add_apply]
  by_cases hj : j = μ
  · subst hj
    rw [Pi.single_eq_same]
    have h2 : (1 : ZMod 2) + 1 = 0 := by decide
    calc (1 : ZMod 2) + (1 + x j) = (1 + 1) + x j := by
          rw [← add_assoc]
      _ = x j := by rw [h2, zero_add]
  · rw [Pi.single_eq_of_ne hj, zero_add, zero_add]

/-- The layer shift at `N = 2` as an equivalence of the
site type (it is its own inverse). -/
def layerShiftEquiv (μ : Fin 4) (hμ : μ ≠ 0) :
    LayerSite 2 ≃ LayerSite 2 where
  toFun := layerShift μ hμ
  invFun := layerShift μ hμ
  left_inv c := Subtype.ext (torusShift_two μ c.1)
  right_inv c := Subtype.ext (torusShift_two μ c.1)

/-- **Indicator collapse**: summing a family against the
link indicator `l.1 = (c.1, mu)` over `(c, mu)` evaluates
the family at the link's own tail and direction. -/
theorem sum_link_indicator (ℓ : LayerLink 2)
    (G : LayerSite 2 → Fin 4 → ℝ) :
    (∑ c : LayerSite 2, ∑ μ : Fin 4,
      (if ℓ.1 = (c.1, μ) then (1 : ℝ) else 0) * G c μ)
      = G (linkTail ℓ) ℓ.1.2 := by
  have ind : ∀ c μ,
      (if ℓ.1 = (c.1, μ) then (1 : ℝ) else 0) * G c μ
        = if (c, μ) = (linkTail ℓ, ℓ.1.2) then G c μ else 0 := by
    intro c μ
    by_cases h : ℓ.1 = (c.1, μ)
    · have hc : c = linkTail ℓ :=
        Subtype.ext (congrArg Prod.fst h).symm
      have hμ : μ = ℓ.1.2 := (congrArg Prod.snd h).symm
      rw [if_pos h, one_mul, if_pos (Prod.ext hc hμ)]
    · have hne : (c, μ) ≠ (linkTail ℓ, ℓ.1.2) := by
        intro hce
        apply h
        have hc : c = linkTail ℓ := congrArg Prod.fst hce
        have hμ : μ = ℓ.1.2 := congrArg Prod.snd hce
        show ℓ.1 = (c.1, μ)
        rw [Prod.ext_iff]
        constructor
        · exact (congrArg Subtype.val hc).symm
        · exact hμ.symm
      rw [if_neg h, zero_mul, if_neg hne]
  rw [Finset.sum_congr rfl (fun c _ =>
    Finset.sum_congr rfl (fun μ _ => ind c μ))]
  have inner : ∀ c : LayerSite 2,
      (∑ μ : Fin 4, if (c, μ) = (linkTail ℓ, ℓ.1.2)
        then G c μ else 0)
        = if c = linkTail ℓ then G c ℓ.1.2 else 0 := by
    intro c
    by_cases hc : c = linkTail ℓ
    · subst hc
      rw [if_pos rfl]
      have e : ∀ μ : Fin 4,
          (if (linkTail ℓ, μ) = (linkTail ℓ, ℓ.1.2)
            then G (linkTail ℓ) μ else 0)
            = if μ = ℓ.1.2 then G (linkTail ℓ) μ else 0 := by
        intro μ
        by_cases hμ : μ = ℓ.1.2
        · have hpp : (linkTail ℓ, μ) = (linkTail ℓ, ℓ.1.2) := by
            rw [Prod.ext_iff]
            exact ⟨rfl, hμ⟩
          rw [if_pos hpp, if_pos hμ]
        · have hnn : ¬ (linkTail ℓ, μ) = (linkTail ℓ, ℓ.1.2) := by
            rw [Prod.ext_iff]
            exact fun h => hμ h.2
          rw [if_neg hnn, if_neg hμ]
      rw [Finset.sum_congr rfl (fun μ _ => e μ),
        Finset.sum_ite_eq']
      simp
    · rw [if_neg hc]
      apply Finset.sum_eq_zero
      intro μ _
      exact if_neg (fun hce => hc (congrArg Prod.fst hce))
  rw [Finset.sum_congr rfl (fun c _ => inner c),
    Finset.sum_ite_eq']
  simp

/-- The denominator in `U`-form: at `N = 2` each
`greenU k i` is `0` or `2`, so its square is twice itself
and `greenDenom k = 1 + 2 * U`. -/
theorem greenDenom_eq (k : LayerSite 2) :
    greenDenom k = 1 + 2 * ∑ i : Fin 4, greenU k i := by
  unfold greenDenom
  rw [show (∑ i : Fin 4, (greenU k i) ^ 2)
      = ∑ i : Fin 4, 2 * greenU k i from
    Finset.sum_congr rfl (fun i _ => greenU_sq k i),
    ← Finset.mul_sum]

/-- The signed `U`-sum: `greenSgn * greenU = greenSgn - 1`
pointwise (since `greenU = 1 - greenSgn` and
`greenSgn ^ 2 = 1`), so the signed sum of `greenU k` over
all directions is `-U`. -/
theorem sum_sgn_greenU (k : LayerSite 2) :
    (∑ μ : Fin 4, greenSgn (k.1 μ) * greenU k μ)
      = -∑ μ : Fin 4, greenU k μ := by
  have pt : ∀ μ : Fin 4, greenSgn (k.1 μ) * greenU k μ
      = greenSgn (k.1 μ) - 1 := by
    intro μ
    unfold greenU
    have h := greenSgn_sq (k.1 μ)
    nlinarith [h]
  rw [Finset.sum_congr rfl (fun μ _ => pt μ),
    Finset.sum_sub_distrib]
  simp [greenU, Finset.sum_sub_distrib]

end ShiftTools


section RestSums

/-- **Rest sum, bottom/left form**: the `nu`-sum of the
rest factor at fixed `mu = d` (the row link's direction):
`U * delta - u_d` against the denominator, where `U` is
the sum of `greenU k` over all directions and `delta` is
the direction indicator of the two links. -/
theorem restSumB (k : LayerSite 2) (ℓ ℓ' : LayerLink 2) :
    (∑ ν : Fin 4, plaqRest k ℓ' ℓ.1.2 ν)
      = greenChi k (linkTail ℓ')
        * (((∑ i : Fin 4, greenU k i)
            * (if ℓ.1.2 = ℓ'.1.2 then (1 : ℝ) else 0)
            - greenU k ℓ.1.2) / greenDenom k) := by
  have hexp : ∀ ν : Fin 4, plaqRest k ℓ' ℓ.1.2 ν
      = greenChi k (linkTail ℓ')
        * ((greenU k ν * (if ℓ.1.2 = ℓ'.1.2 then (1 : ℝ) else 0)
            - greenU k ℓ.1.2
              * (if ν = ℓ'.1.2 then (1 : ℝ) else 0))
          / greenDenom k) := by
    intro ν
    unfold plaqRest
    ring
  rw [Finset.sum_congr rfl (fun ν _ => hexp ν), ← Finset.mul_sum,
    ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, mul_one]

/-- **Rest sum, left form**: the `mu`-sum of the rest
factor at fixed `nu = d`: the negative of the bottom
form. -/
theorem restSumL (k : LayerSite 2) (ℓ ℓ' : LayerLink 2) :
    (∑ μ : Fin 4, plaqRest k ℓ' μ ℓ.1.2)
      = greenChi k (linkTail ℓ')
        * ((greenU k ℓ.1.2
            - (∑ i : Fin 4, greenU k i)
              * (if ℓ.1.2 = ℓ'.1.2 then (1 : ℝ) else 0))
          / greenDenom k) := by
  have hexp : ∀ μ : Fin 4, plaqRest k ℓ' μ ℓ.1.2
      = greenChi k (linkTail ℓ')
        * ((greenU k ℓ.1.2 * (if μ = ℓ'.1.2 then (1 : ℝ) else 0)
            - greenU k μ
              * (if ℓ.1.2 = ℓ'.1.2 then (1 : ℝ) else 0))
          / greenDenom k) := by
    intro μ
    unfold plaqRest
    ring
  rw [Finset.sum_congr rfl (fun μ _ => hexp μ), ← Finset.mul_sum,
    ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, mul_one]

/-- **Rest sum, right form**: the signed `mu`-sum of the
rest factor at fixed `nu = d`; the signed `greenU` sum is
`-U` (by `sum_sgn_greenU`), and the signed indicator sum
picks out `greenSgn (k.1 d')`. -/
theorem restSumR (k : LayerSite 2) (ℓ ℓ' : LayerLink 2) :
    (∑ μ : Fin 4, greenSgn (k.1 μ) * plaqRest k ℓ' μ ℓ.1.2)
      = greenChi k (linkTail ℓ')
        * ((greenU k ℓ.1.2 * greenSgn (k.1 ℓ'.1.2)
            - (-(∑ i : Fin 4, greenU k i))
              * (if ℓ.1.2 = ℓ'.1.2 then (1 : ℝ) else 0))
          / greenDenom k) := by
  have hind : ∀ μ : Fin 4,
      greenSgn (k.1 μ) * (if μ = ℓ'.1.2 then (1 : ℝ) else 0)
        = if μ = ℓ'.1.2 then greenSgn (k.1 μ) else 0 := by
    intro μ
    by_cases h : μ = ℓ'.1.2 <;> simp [h]
  have hexp : ∀ μ : Fin 4, greenSgn (k.1 μ) * plaqRest k ℓ' μ ℓ.1.2
      = greenChi k (linkTail ℓ')
        * ((greenSgn (k.1 μ)
              * (greenU k ℓ.1.2
                * (if μ = ℓ'.1.2 then (1 : ℝ) else 0))
            - (greenSgn (k.1 μ) * greenU k μ)
              * (if ℓ.1.2 = ℓ'.1.2 then (1 : ℝ) else 0))
          / greenDenom k) := by
    intro μ
    unfold plaqRest
    ring
  have regroup : ∀ μ : Fin 4,
      greenSgn (k.1 μ)
          * (greenU k ℓ.1.2 * (if μ = ℓ'.1.2 then (1 : ℝ) else 0))
        = greenU k ℓ.1.2
          * (greenSgn (k.1 μ)
            * (if μ = ℓ'.1.2 then (1 : ℝ) else 0)) := by
    intro μ
    ring
  rw [Finset.sum_congr rfl (fun μ _ => hexp μ), ← Finset.mul_sum,
    ← Finset.sum_div, Finset.sum_sub_distrib,
    Finset.sum_congr rfl (fun μ _ => regroup μ), ← Finset.mul_sum,
    ← Finset.sum_mul, sum_sgn_greenU,
    Finset.sum_congr rfl (fun μ _ => hind μ), Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]

/-- **Rest sum, top form**: the signed `nu`-sum of the
rest factor at fixed `mu = d`. -/
theorem restSumT (k : LayerSite 2) (ℓ ℓ' : LayerLink 2) :
    (∑ ν : Fin 4, greenSgn (k.1 ν) * plaqRest k ℓ' ℓ.1.2 ν)
      = greenChi k (linkTail ℓ')
        * (((-(∑ i : Fin 4, greenU k i))
              * (if ℓ.1.2 = ℓ'.1.2 then (1 : ℝ) else 0)
            - greenU k ℓ.1.2 * greenSgn (k.1 ℓ'.1.2))
          / greenDenom k) := by
  have hind : ∀ ν : Fin 4,
      greenSgn (k.1 ν) * (if ν = ℓ'.1.2 then (1 : ℝ) else 0)
        = if ν = ℓ'.1.2 then greenSgn (k.1 ν) else 0 := by
    intro ν
    by_cases h : ν = ℓ'.1.2 <;> simp [h]
  have hexp : ∀ ν : Fin 4, greenSgn (k.1 ν) * plaqRest k ℓ' ℓ.1.2 ν
      = greenChi k (linkTail ℓ')
        * (((greenSgn (k.1 ν) * greenU k ν)
              * (if ℓ.1.2 = ℓ'.1.2 then (1 : ℝ) else 0)
            - greenU k ℓ.1.2
              * (greenSgn (k.1 ν)
                * (if ν = ℓ'.1.2 then (1 : ℝ) else 0)))
          / greenDenom k) := by
    intro ν
    unfold plaqRest
    ring
  rw [Finset.sum_congr rfl (fun ν _ => hexp ν), ← Finset.mul_sum,
    ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_sgn_greenU, ← Finset.mul_sum,
    Finset.sum_congr rfl (fun ν _ => hind ν), Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]

end RestSums


section Families

/-- The right/top indicator at direction `0` never
fires: the shifted site has time coordinate `1`, while a
layer link's tail has time coordinate `0`. -/
theorem indR_zero (ℓ : LayerLink 2) (c : LayerSite 2)
    (ν : Fin 4) :
    (if ℓ.1 = (torusShift 2 0 c.1, ν) then (1 : ℝ) else 0)
      = 0 := by
  rw [if_neg]
  intro h
  have h0 : ℓ.1.1 0 = (torusShift 2 0 c.1) 0 :=
    congrFun (congrArg Prod.fst h) 0
  rw [torusShift_apply_coord, Pi.single_eq_same] at h0
  have e2 : c.1 0 = 0 :=
    zmod_eq_zero_of_val_eq_zero (c.1 0) c.2
  have e3 : ℓ.1.1 0 = 0 :=
    zmod_eq_zero_of_val_eq_zero (ℓ.1.1 0) ℓ.2.1
  rw [e2, add_zero, e3] at h0
  exact zero_ne_one h0

/-- **Splitting the operator summand**: at fixed momentum,
the `H`-sum over base sites and direction pairs splits
into the four edge families (bottom, right, top, left)
against the rest factor. -/
theorem hsum_split (k : LayerSite 2) (ℓ ℓ' : LayerLink 2) :
    (∑ c : LayerSite 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
        plaqEsign ℓ c μ ν * plaqBk k ℓ' c μ ν)
      = (∑ c : LayerSite 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
          (if ℓ.1 = (c.1, μ) then (1 : ℝ) else 0)
            * (greenChi k c * plaqRest k ℓ' μ ν))
        + (∑ c : LayerSite 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
          (if ℓ.1 = (torusShift 2 μ c.1, ν) then (1 : ℝ) else 0)
            * (greenChi k c * plaqRest k ℓ' μ ν))
        - (∑ c : LayerSite 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
          (if ℓ.1 = (torusShift 2 ν c.1, μ) then (1 : ℝ) else 0)
            * (greenChi k c * plaqRest k ℓ' μ ν))
        - (∑ c : LayerSite 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
          (if ℓ.1 = (c.1, ν) then (1 : ℝ) else 0)
            * (greenChi k c * plaqRest k ℓ' μ ν)) := by
  have pt : ∀ c μ ν, plaqEsign ℓ c μ ν * plaqBk k ℓ' c μ ν
      = (if ℓ.1 = (c.1, μ) then (1 : ℝ) else 0)
          * (greenChi k c * plaqRest k ℓ' μ ν)
        + (if ℓ.1 = (torusShift 2 μ c.1, ν) then (1 : ℝ) else 0)
          * (greenChi k c * plaqRest k ℓ' μ ν)
        - (if ℓ.1 = (torusShift 2 ν c.1, μ) then (1 : ℝ) else 0)
          * (greenChi k c * plaqRest k ℓ' μ ν)
        - (if ℓ.1 = (c.1, ν) then (1 : ℝ) else 0)
          * (greenChi k c * plaqRest k ℓ' μ ν) := by
    intro c μ ν
    unfold plaqEsign
    rw [plaqBk_eq]
    ring
  rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl
    (fun μ _ => Finset.sum_congr rfl (fun ν _ => pt c μ ν)))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- **Bottom family**: the indicator pins `(c, mu)` to the
row link's tail and direction, leaving the `nu`-sum of
the rest factor at `mu = d`. -/
theorem famB (k : LayerSite 2) (ℓ ℓ' : LayerLink 2) :
    (∑ c : LayerSite 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
      (if ℓ.1 = (c.1, μ) then (1 : ℝ) else 0)
        * (greenChi k c * plaqRest k ℓ' μ ν))
      = greenChi k (linkTail ℓ)
        * (∑ ν : Fin 4, plaqRest k ℓ' ℓ.1.2 ν) := by
  have e1 : ∀ c μ, (∑ ν : Fin 4,
        (if ℓ.1 = (c.1, μ) then (1 : ℝ) else 0)
          * (greenChi k c * plaqRest k ℓ' μ ν))
      = (if ℓ.1 = (c.1, μ) then (1 : ℝ) else 0)
        * (greenChi k c * ∑ ν : Fin 4, plaqRest k ℓ' μ ν) := by
    intro c μ
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun c _ =>
    Finset.sum_congr rfl (fun μ _ => e1 c μ))]
  exact sum_link_indicator ℓ
    (fun c μ => greenChi k c * ∑ ν : Fin 4, plaqRest k ℓ' μ ν)

/-- **Left family**: the indicator pins `(c, nu)` to the
row link's tail and direction, leaving the `mu`-sum of
the rest factor at `nu = d`. -/
theorem famL (k : LayerSite 2) (ℓ ℓ' : LayerLink 2) :
    (∑ c : LayerSite 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
      (if ℓ.1 = (c.1, ν) then (1 : ℝ) else 0)
        * (greenChi k c * plaqRest k ℓ' μ ν))
      = greenChi k (linkTail ℓ)
        * (∑ μ : Fin 4, plaqRest k ℓ' μ ℓ.1.2) := by
  have e0 : ∀ c : LayerSite 2, (∑ μ : Fin 4, ∑ ν : Fin 4,
        (if ℓ.1 = (c.1, ν) then (1 : ℝ) else 0)
          * (greenChi k c * plaqRest k ℓ' μ ν))
      = ∑ ν : Fin 4, ∑ μ : Fin 4,
        (if ℓ.1 = (c.1, ν) then (1 : ℝ) else 0)
          * (greenChi k c * plaqRest k ℓ' μ ν) :=
    fun c => Finset.sum_comm
  have e1 : ∀ c ν, (∑ μ : Fin 4,
        (if ℓ.1 = (c.1, ν) then (1 : ℝ) else 0)
          * (greenChi k c * plaqRest k ℓ' μ ν))
      = (if ℓ.1 = (c.1, ν) then (1 : ℝ) else 0)
        * (greenChi k c * ∑ μ : Fin 4, plaqRest k ℓ' μ ν) := by
    intro c ν
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun c _ => e0 c),
    Finset.sum_congr rfl (fun c _ =>
      Finset.sum_congr rfl (fun ν _ => e1 c ν))]
  exact sum_link_indicator ℓ
    (fun c ν => greenChi k c * ∑ μ : Fin 4, plaqRest k ℓ' μ ν)

/-- **Right family**: at `mu = 0` the indicator never
fires and the rest factor vanishes; at `mu` nonzero the
base site is reindexed by the layer shift (the character
gains the sign factor), and the indicator then pins
`(c, nu)` to the row link. -/
theorem famR (k : LayerSite 2) (ℓ ℓ' : LayerLink 2) :
    (∑ c : LayerSite 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
      (if ℓ.1 = (torusShift 2 μ c.1, ν) then (1 : ℝ) else 0)
        * (greenChi k c * plaqRest k ℓ' μ ν))
      = greenChi k (linkTail ℓ)
        * (∑ μ : Fin 4, greenSgn (k.1 μ)
          * plaqRest k ℓ' μ ℓ.1.2) := by
  have step : ∀ μ : Fin 4, (∑ c : LayerSite 2, ∑ ν : Fin 4,
        (if ℓ.1 = (torusShift 2 μ c.1, ν) then (1 : ℝ) else 0)
          * (greenChi k c * plaqRest k ℓ' μ ν))
      = greenChi k (linkTail ℓ)
        * (greenSgn (k.1 μ) * plaqRest k ℓ' μ ℓ.1.2) := by
    intro μ
    by_cases hμ : μ = 0
    · subst hμ
      rw [plaqRest_zero_mu, mul_zero, mul_zero]
      apply Finset.sum_eq_zero
      intro c _
      apply Finset.sum_eq_zero
      intro ν _
      rw [indR_zero, zero_mul]
    · have reindex : (∑ c : LayerSite 2, ∑ ν : Fin 4,
          (if ℓ.1 = (torusShift 2 μ (layerShift μ hμ c).1, ν)
            then (1 : ℝ) else 0)
            * (greenChi k (layerShift μ hμ c)
              * plaqRest k ℓ' μ ν))
        = ∑ c : LayerSite 2, ∑ ν : Fin 4,
          (if ℓ.1 = (torusShift 2 μ c.1, ν) then (1 : ℝ) else 0)
            * (greenChi k c * plaqRest k ℓ' μ ν) :=
        (layerShiftEquiv μ hμ).sum_comp
          (fun c => ∑ ν : Fin 4,
            (if ℓ.1 = (torusShift 2 μ c.1, ν) then (1 : ℝ) else 0)
              * (greenChi k c * plaqRest k ℓ' μ ν))
      rw [← reindex]
      have pt : ∀ c ν, (if ℓ.1 = (torusShift 2 μ
              (layerShift μ hμ c).1, ν) then (1 : ℝ) else 0)
            * (greenChi k (layerShift μ hμ c)
              * plaqRest k ℓ' μ ν)
          = greenSgn (k.1 μ)
            * ((if ℓ.1 = (c.1, ν) then (1 : ℝ) else 0)
              * (greenChi k c * plaqRest k ℓ' μ ν)) := by
        intro c ν
        show (if ℓ.1 = (torusShift 2 μ (torusShift 2 μ c.1), ν)
              then (1 : ℝ) else 0)
            * (greenChi k (layerShift μ hμ c)
              * plaqRest k ℓ' μ ν) = _
        rw [torusShift_two, greenChi_shift k c μ hμ]
        ring
      rw [Finset.sum_congr rfl (fun c _ =>
        Finset.sum_congr rfl (fun ν _ => pt c ν))]
      simp only [← Finset.mul_sum]
      have hcol := sum_link_indicator ℓ
        (fun c ν => greenChi k c * plaqRest k ℓ' μ ν)
      rw [hcol]
      ring
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun μ _ => step μ)

/-- **Top family**: at `nu = 0` the indicator never fires
and the rest factor vanishes; at `nu` nonzero the base
site is reindexed by the layer shift, and the indicator
then pins `(c, mu)` to the row link. -/
theorem famT (k : LayerSite 2) (ℓ ℓ' : LayerLink 2) :
    (∑ c : LayerSite 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
      (if ℓ.1 = (torusShift 2 ν c.1, μ) then (1 : ℝ) else 0)
        * (greenChi k c * plaqRest k ℓ' μ ν))
      = greenChi k (linkTail ℓ)
        * (∑ ν : Fin 4, greenSgn (k.1 ν)
          * plaqRest k ℓ' ℓ.1.2 ν) := by
  have step : ∀ ν : Fin 4, (∑ c : LayerSite 2, ∑ μ : Fin 4,
        (if ℓ.1 = (torusShift 2 ν c.1, μ) then (1 : ℝ) else 0)
          * (greenChi k c * plaqRest k ℓ' μ ν))
      = greenChi k (linkTail ℓ)
        * (greenSgn (k.1 ν) * plaqRest k ℓ' ℓ.1.2 ν) := by
    intro ν
    by_cases hν : ν = 0
    · subst hν
      rw [plaqRest_zero_nu, mul_zero, mul_zero]
      apply Finset.sum_eq_zero
      intro c _
      apply Finset.sum_eq_zero
      intro μ _
      rw [indR_zero, zero_mul]
    · have reindex : (∑ c : LayerSite 2, ∑ μ : Fin 4,
          (if ℓ.1 = (torusShift 2 ν (layerShift ν hν c).1, μ)
            then (1 : ℝ) else 0)
            * (greenChi k (layerShift ν hν c)
              * plaqRest k ℓ' μ ν))
        = ∑ c : LayerSite 2, ∑ μ : Fin 4,
          (if ℓ.1 = (torusShift 2 ν c.1, μ) then (1 : ℝ) else 0)
            * (greenChi k c * plaqRest k ℓ' μ ν) :=
        (layerShiftEquiv ν hν).sum_comp
          (fun c => ∑ μ : Fin 4,
            (if ℓ.1 = (torusShift 2 ν c.1, μ) then (1 : ℝ) else 0)
              * (greenChi k c * plaqRest k ℓ' μ ν))
      rw [← reindex]
      have pt : ∀ c μ, (if ℓ.1 = (torusShift 2 ν
              (layerShift ν hν c).1, μ) then (1 : ℝ) else 0)
            * (greenChi k (layerShift ν hν c)
              * plaqRest k ℓ' μ ν)
          = greenSgn (k.1 ν)
            * ((if ℓ.1 = (c.1, μ) then (1 : ℝ) else 0)
              * (greenChi k c * plaqRest k ℓ' μ ν)) := by
        intro c μ
        show (if ℓ.1 = (torusShift 2 ν (torusShift 2 ν c.1), μ)
              then (1 : ℝ) else 0)
            * (greenChi k (layerShift ν hν c)
              * plaqRest k ℓ' μ ν) = _
        rw [torusShift_two, greenChi_shift k c ν hν]
        ring
      rw [Finset.sum_congr rfl (fun c _ =>
        Finset.sum_congr rfl (fun μ _ => pt c μ))]
      simp only [← Finset.mul_sum]
      have hcol := sum_link_indicator ℓ
        (fun c μ => greenChi k c * plaqRest k ℓ' μ ν)
      rw [hcol]
      ring
  have e0 : ∀ c : LayerSite 2, (∑ μ : Fin 4, ∑ ν : Fin 4,
        (if ℓ.1 = (torusShift 2 ν c.1, μ) then (1 : ℝ) else 0)
          * (greenChi k c * plaqRest k ℓ' μ ν))
      = ∑ ν : Fin 4, ∑ μ : Fin 4,
        (if ℓ.1 = (torusShift 2 ν c.1, μ) then (1 : ℝ) else 0)
          * (greenChi k c * plaqRest k ℓ' μ ν) :=
    fun c => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun c _ => e0 c), Finset.sum_comm,
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun ν _ => step ν)

/-- **The `H`-sum at fixed momentum, evaluated**: the four
families and the four rest sums combine to
`chi * chi' * (4 * U * delta + 2 * u_d * s' - 2 * u_d) / D`. -/
theorem hsum_value (k : LayerSite 2) (ℓ ℓ' : LayerLink 2) :
    (∑ c : LayerSite 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
        plaqEsign ℓ c μ ν * plaqBk k ℓ' c μ ν)
      = greenChi k (linkTail ℓ) * greenChi k (linkTail ℓ')
        * ((4 * ((∑ i : Fin 4, greenU k i)
              * (if ℓ.1.2 = ℓ'.1.2 then (1 : ℝ) else 0))
            + 2 * (greenU k ℓ.1.2 * greenSgn (k.1 ℓ'.1.2))
            - 2 * greenU k ℓ.1.2) / greenDenom k) := by
  rw [hsum_split, famB, famL, famR, famT, restSumB, restSumL,
    restSumR, restSumT]
  have hD := greenDenom_ne_zero k
  field_simp
  ring

end Families


section SeatFormula

/-- **The plaquette sum at fixed momentum, halved**: by
the enumeration decomposition and the doubling lemma,
the signed plaquette sum of the bracket is half the full
`H`-sum. -/
theorem greenHsum (k : LayerSite 2) (ℓ ℓ' : LayerLink 2) :
    (∑ P ∈ allPlaqData 2, plaqSign P ℓ * plaqBk k ℓ' P.base
        P.mu P.nu)
      = (1 / 2) * ∑ c : LayerSite 2, ∑ μ : Fin 4, ∑ ν : Fin 4,
          plaqEsign ℓ c μ ν * plaqBk k ℓ' c μ ν := by
  rw [allPlaqData_sum]
  refine (Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl
    (fun μ _ => Finset.sum_congr rfl (fun ν _ => ?_)))).trans
    (dite_triple_double
      (fun c μ ν => plaqEsign ℓ c μ ν * plaqBk k ℓ' c μ ν)
      (fun c μ ν => (plaqH_symm k ℓ ℓ' c μ ν).symm)
      (plaqH_diag k ℓ ℓ')
      (fun c ν => plaqH_zero k ℓ ℓ' c 0 ν (Or.inl rfl)))
  show (if h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
      then plaqSign ⟨c, μ, ν, h.1, h.2.1, ne_of_lt h.2.2⟩ ℓ
        * plaqBk k ℓ' c μ ν else 0)
    = if h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
      then plaqEsign ℓ c μ ν * plaqBk k ℓ' c μ ν else 0
  by_cases h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν
  · rw [dif_pos h, dif_pos h, plaqSign_esig]
  · rw [dif_neg h, dif_neg h]

/-- **The operator applied to the candidate, swapped**:
the plaquette sum and the momentum sum exchange, at the
price of the `(1/8)` momentum average. -/
theorem maxwellOp_greenCand (ℓ ℓ' : LayerLink 2) :
    (maxwellOp 2 (fun l => greenCand l ℓ')) ℓ
      = (1 / 8) * ∑ k : LayerSite 2, ∑ P ∈ allPlaqData 2,
          plaqSign P ℓ * plaqBk k ℓ' P.base P.mu P.nu := by
  have per : ∀ P : PlaqDatum 2,
      plaqSign P ℓ * plaqAngle P (fun l => greenCand l ℓ')
        = (1 / 8) * ∑ k : LayerSite 2,
            plaqSign P ℓ * plaqBk k ℓ' P.base P.mu P.nu := by
    intro P
    rw [plaqAngle_greenCand, ← mul_assoc, Finset.mul_sum,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [maxwellOp_apply,
    Finset.sum_congr rfl (fun P _ => per P), ← Finset.mul_sum,
    Finset.sum_comm]

/-- **The candidate inverts the shifted operator at the
seat**: at `N = 2`, `m = 1`, the shifted operator applied
to the candidate column `l'` is the basis angle at `l'`.
The per-momentum identity is
`(delta + u u') + (4 U delta + 2 u s' - 2 u) / 2
= delta * (1 + 2 U) = delta * D`, using `u' = 1 - s'`. -/
theorem shiftedOp_greenCand (ℓ ℓ' : LayerLink 2) :
    shiftedOp 2 1 (fun l => greenCand l ℓ') ℓ
      = greenBasis ℓ' ℓ := by
  classical
  have cand_rw : (1 : ℝ) ^ 2 * greenCand ℓ ℓ'
      = (1 / 8) * ∑ k : LayerSite 2,
          greenChi k (linkTail ℓ) * greenChi k (linkTail ℓ')
            * (((if ℓ.1.2 = ℓ'.1.2 then (1 : ℝ) else 0)
                + greenU k ℓ.1.2 * greenU k ℓ'.1.2)
              / greenDenom k) := by
    unfold greenCand
    rw [one_pow, one_mul]
  have pk : ∀ k : LayerSite 2,
      (∑ P ∈ allPlaqData 2, plaqSign P ℓ * plaqBk k ℓ' P.base
          P.mu P.nu)
        + greenChi k (linkTail ℓ) * greenChi k (linkTail ℓ')
          * (((if ℓ.1.2 = ℓ'.1.2 then (1 : ℝ) else 0)
              + greenU k ℓ.1.2 * greenU k ℓ'.1.2)
            / greenDenom k)
      = greenChi k (linkTail ℓ) * greenChi k (linkTail ℓ')
        * (if ℓ.1.2 = ℓ'.1.2 then (1 : ℝ) else 0) := by
    intro k
    have hD := greenDenom_ne_zero k
    have hD2 : (1 : ℝ) + 2 * ∑ i : Fin 4, greenU k i ≠ 0 := by
      rw [← greenDenom_eq k]
      exact hD
    rw [greenHsum, hsum_value, greenDenom_eq,
      show greenU k ℓ'.1.2 = 1 - greenSgn (k.1 ℓ'.1.2) from rfl]
    field_simp
    ring
  rw [shiftedOp_apply]
  show (maxwellOp 2 (fun l => greenCand l ℓ')) ℓ
      + (1 : ℝ) ^ 2 * greenCand ℓ ℓ' = greenBasis ℓ' ℓ
  rw [maxwellOp_greenCand, cand_rw, ← mul_add,
    ← Finset.sum_add_distrib,
    Finset.sum_congr rfl (fun k _ => pk k)]
  by_cases hδ : ℓ.1.2 = ℓ'.1.2
  · rw [Finset.sum_congr rfl (fun k _ =>
      show greenChi k (linkTail ℓ) * greenChi k (linkTail ℓ')
          * (if ℓ.1.2 = ℓ'.1.2 then (1 : ℝ) else 0)
        = greenChi k (linkTail ℓ) * greenChi k (linkTail ℓ')
        from by rw [if_pos hδ, mul_one]), greenChi_sum]
    by_cases ht : linkTail ℓ = linkTail ℓ'
    · have hℓ : ℓ = ℓ' := by
        apply Subtype.ext
        rw [Prod.ext_iff]
        exact ⟨congrArg Subtype.val ht, hδ⟩
      rw [if_pos ht, hℓ, greenBasis_self]
      norm_num
    · rw [if_neg ht,
        greenBasis_of_ne (fun h => ht (congrArg linkTail h))]
      norm_num
  · rw [Finset.sum_congr rfl (fun k _ =>
      show greenChi k (linkTail ℓ) * greenChi k (linkTail ℓ')
          * (if ℓ.1.2 = ℓ'.1.2 then (1 : ℝ) else 0) = 0
        from by rw [if_neg hδ, mul_zero]),
      Finset.sum_const_zero,
      greenBasis_of_ne (fun h => hδ
        (congrArg Prod.snd (congrArg Subtype.val h)))]
    norm_num

/-- **The seat formula**: at `N = 2`, `m = 1`, the Green
kernel is the candidate - the kernel entry is the
momentum average of the block inverse. -/
theorem greenKernel_seat_formula (hm : 0 < (1 : ℝ))
    (ℓ ℓ' : LayerLink 2) :
    greenKernel 2 1 hm ℓ ℓ' = greenCand ℓ ℓ' := by
  symm
  exact greenKernel_eq_of 1 hm
    (fun l => greenCand l ℓ') ℓ'
    (funext fun ℓ => shiftedOp_greenCand ℓ ℓ') ℓ

end SeatFormula


section SeatValues

/-- The cyclic distance at `N = 2` is the inequality
indicator. -/
theorem cycDist_two (x y : ZMod 2) :
    cycDist 2 x y = if x = y then 0 else 1 := by
  rcases zmod2_cases x with rfl | rfl <;>
    rcases zmod2_cases y with rfl | rfl <;> decide

/-- The character of a named site: the time coordinate
contributes the trivial factor. -/
theorem greenChi_siteOf (a b c : ZMod 2) (s : LayerSite 2) :
    greenChi (siteOf a b c) s
      = greenSgn (a * s.1 1) * greenSgn (b * s.1 2)
        * greenSgn (c * s.1 3) := by
  have h0 : (siteOf a b c).1 0 = 0 := by simp [siteOf_coord]
  have h1 : (siteOf a b c).1 1 = a := by simp [siteOf_coord]
  have h2 : (siteOf a b c).1 2 = b := by simp [siteOf_coord]
  have h3 : (siteOf a b c).1 3 = c := by simp [siteOf_coord]
  unfold greenChi
  rw [Fin.prod_univ_four, h0, h1, h2, h3, zero_mul,
    greenSgn_zero, one_mul]

/-- **The character pair product**: at a named momentum,
the product of the two column characters is the product
over spatial coordinates of the seat's sign factor -
`1` where the tails agree, `greenSgn` of the momentum
coordinate where they differ. -/
theorem greenChi_pair (a b c : ZMod 2) (s s' : LayerSite 2) :
    greenChi (siteOf a b c) s * greenChi (siteOf a b c) s'
      = (if s.1 1 = s'.1 1 then (1 : ℝ) else greenSgn a)
        * (if s.1 2 = s'.1 2 then (1 : ℝ) else greenSgn b)
        * (if s.1 3 = s'.1 3 then (1 : ℝ) else greenSgn c) := by
  rw [greenChi_siteOf, greenChi_siteOf]
  have e : (greenSgn (a * s.1 1) * greenSgn (b * s.1 2)
        * greenSgn (c * s.1 3))
      * (greenSgn (a * s'.1 1) * greenSgn (b * s'.1 2)
        * greenSgn (c * s'.1 3))
    = ((greenSgn (a * s.1 1) * greenSgn (a * s'.1 1))
      * (greenSgn (b * s.1 2) * greenSgn (b * s'.1 2)))
      * (greenSgn (c * s.1 3) * greenSgn (c * s'.1 3)) := by
    ring
  rw [e, greenSgn_factor, greenSgn_factor, greenSgn_factor]

/-- The `greenU` factor of a named site in direction
`1`. -/
theorem greenU_siteOf_one (a b c : ZMod 2) :
    greenU (siteOf a b c) 1 = 1 - greenSgn a := by
  have h1 : (siteOf a b c).1 1 = a := by simp [siteOf_coord]
  unfold greenU
  rw [h1]

/-- The `greenU` factor of a named site in direction
`2`. -/
theorem greenU_siteOf_two (a b c : ZMod 2) :
    greenU (siteOf a b c) 2 = 1 - greenSgn b := by
  have h2 : (siteOf a b c).1 2 = b := by simp [siteOf_coord]
  unfold greenU
  rw [h2]

/-- The `greenU` factor of a named site in direction
`3`. -/
theorem greenU_siteOf_three (a b c : ZMod 2) :
    greenU (siteOf a b c) 3 = 1 - greenSgn c := by
  have h3 : (siteOf a b c).1 3 = c := by simp [siteOf_coord]
  unfold greenU
  rw [h3]

/-- The denominator of a named site. -/
theorem greenDenom_siteOf (a b c : ZMod 2) :
    greenDenom (siteOf a b c)
      = 1 + (1 - greenSgn a) ^ 2 + (1 - greenSgn b) ^ 2
        + (1 - greenSgn c) ^ 2 := by
  unfold greenDenom
  rw [Fin.sum_univ_four, greenU_time, greenU_siteOf_one,
    greenU_siteOf_two, greenU_siteOf_three]
  ring

/-- The candidate as a triple sum over the named
momenta of the seat. -/
theorem greenCand_eq_sum3 (ℓ ℓ' : LayerLink 2) :
    greenCand ℓ ℓ'
      = (1 / 8) * ∑ a : ZMod 2, ∑ b : ZMod 2, ∑ c : ZMod 2,
          greenChi (siteOf a b c) (linkTail ℓ)
            * greenChi (siteOf a b c) (linkTail ℓ')
            * (((if ℓ.1.2 = ℓ'.1.2 then (1 : ℝ) else 0)
                + greenU (siteOf a b c) ℓ.1.2
                  * greenU (siteOf a b c) ℓ'.1.2)
              / greenDenom (siteOf a b c)) := by
  have esymm : ∀ t : ZMod 2 × ZMod 2 × ZMod 2,
      siteEquiv.symm t = siteOf t.1 t.2.1 t.2.2 := fun t => rfl
  unfold greenCand
  rw [← siteEquiv.symm.sum_comp]
  simp only [Fintype.sum_prod_type, esymm]

/-- **The seat values of the kernel**: at `N = 2`, `m = 1`,
every kernel entry, grouped by the `linkGeoDist` class
of its two links. These are seat facts at the named
seat only: the computation decides the entries there,
and nothing here is a falloff law. -/
theorem greenKernel_seat_cases (hm : 0 < (1 : ℝ))
    (ℓ ℓ' : LayerLink 2) :
    (linkGeoDist 2 ℓ ℓ' = 0
      ∧ (greenKernel 2 1 hm ℓ ℓ' = 293 / 585
        ∨ greenKernel 2 1 hm ℓ ℓ' = 11 / 117))
    ∨ (linkGeoDist 2 ℓ ℓ' = 1
      ∧ (greenKernel 2 1 hm ℓ ℓ' = 22 / 117
        ∨ greenKernel 2 1 hm ℓ ℓ' = -8 / 65
        ∨ greenKernel 2 1 hm ℓ ℓ' = -11 / 117
        ∨ greenKernel 2 1 hm ℓ ℓ' = 2 / 117))
    ∨ (linkGeoDist 2 ℓ ℓ' = 2
      ∧ (greenKernel 2 1 hm ℓ ℓ' = 8 / 65
        ∨ greenKernel 2 1 hm ℓ ℓ' = 4 / 117
        ∨ greenKernel 2 1 hm ℓ ℓ' = 11 / 117
        ∨ greenKernel 2 1 hm ℓ ℓ' = -2 / 117))
    ∨ (linkGeoDist 2 ℓ ℓ' = 3
      ∧ (greenKernel 2 1 hm ℓ ℓ' = 32 / 585
        ∨ greenKernel 2 1 hm ℓ ℓ' = 2 / 117)) := by
  classical
  have h00 : (linkTail ℓ).1 0 = (linkTail ℓ').1 0 := by
    rw [show (linkTail ℓ).1 0 = 0 from
      zmod_eq_zero_of_val_eq_zero _ ℓ.2.1,
      show (linkTail ℓ').1 0 = 0 from
      zmod_eq_zero_of_val_eq_zero _ ℓ'.2.1]
  have hrw : linkGeoDist 2 ℓ ℓ'
      = ∑ i : Fin 4, cycDist 2 ((linkTail ℓ).1 i)
          ((linkTail ℓ').1 i) :=
    geoDist_l1_formula 2 (linkTail ℓ) (linkTail ℓ')
  have hd4 : ℓ.1.2 = 0 ∨ ℓ.1.2 = 1 ∨ ℓ.1.2 = 2
      ∨ ℓ.1.2 = 3 := by
    have h := Finset.mem_univ ℓ.1.2
    rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3}
      from by decide] at h
    simpa using h
  have hd4' : ℓ'.1.2 = 0 ∨ ℓ'.1.2 = 1 ∨ ℓ'.1.2 = 2
      ∨ ℓ'.1.2 = 3 := by
    have h := Finset.mem_univ ℓ'.1.2
    rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3}
      from by decide] at h
    simpa using h
  by_cases h1 : (linkTail ℓ).1 1 = (linkTail ℓ').1 1 <;>
  by_cases h2 : (linkTail ℓ).1 2 = (linkTail ℓ').1 2 <;>
  by_cases h3 : (linkTail ℓ).1 3 = (linkTail ℓ').1 3 <;>
  rcases hd4 with (hde | hde | hde | hde) <;>
  rcases hd4' with (hde' | hde' | hde' | hde') <;>
    (try exact (ℓ.2.2 hde).elim) <;>
    (try exact (ℓ'.2.2 hde').elim) <;>
    norm_num [greenKernel_seat_formula hm, greenCand_eq_sum3,
      sum_zmod2, greenChi_pair, greenU_siteOf_one,
      greenU_siteOf_two, greenU_siteOf_three,
      greenDenom_siteOf, greenSgn_zero, greenSgn_one, hrw,
      Fin.sum_univ_four, cycDist_two, h00, h1, h2, h3, hde,
      hde']

/-- **The diagonal seat value**: at `N = 2`, `m = 1`, every
diagonal kernel entry is `293 / 585`. -/
theorem greenKernel_seat_diag (hm : 0 < (1 : ℝ))
    (ℓ : LayerLink 2) :
    greenKernel 2 1 hm ℓ ℓ = 293 / 585 := by
  classical
  have hd4 : ℓ.1.2 = 0 ∨ ℓ.1.2 = 1 ∨ ℓ.1.2 = 2
      ∨ ℓ.1.2 = 3 := by
    have h := Finset.mem_univ ℓ.1.2
    rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3}
      from by decide] at h
    simpa using h
  rcases hd4 with (hde | hde | hde | hde) <;>
    (try exact (ℓ.2.2 hde).elim) <;>
    norm_num [greenKernel_seat_formula hm, greenCand_eq_sum3,
      sum_zmod2, greenChi_pair, greenU_siteOf_one,
      greenU_siteOf_two, greenU_siteOf_three,
      greenDenom_siteOf, greenSgn_zero, greenSgn_one, hde]

/-- **The pin's shadow predicate at the seat**: at
`N = 2`, `m = 1`, with the supplied constant `C = 1 / 2`,
the predicate instance `PoseObjFShadow 2 (greenKernel 2 1)
(1 / 2)` holds - a seat fact about this instance at this
seat, recorded with the seat values, not a law. The
per-class checks are the seat bounds: class `1` entries
are at most `22 / 117` in absolute value against the
bound `1 / 2`; class `2` entries at most `8 / 65`
against `1 / 8` (`64` against `65`); class `3` entries
at most `32 / 585` against `1 / 18` (`576` against
`585`). -/
theorem poseObjFShadow_seat (hm : 0 < (1 : ℝ)) :
    PoseObjFShadow 2 (greenKernel 2 1 hm) (1 / 2) := by
  rw [poseObjFShadow_unfold]
  refine ⟨by norm_num, ?_⟩
  intro l l' hr
  rcases greenKernel_seat_cases hm l l' with
    (h | h | h | h)
  · rw [h.1] at hr
    norm_num at hr
  · rw [h.1]
    rcases h.2 with (hv | hv | hv | hv) <;> rw [hv] <;>
      norm_num
  · rw [h.1]
    rcases h.2 with (hv | hv | hv | hv) <;> rw [hv] <;>
      norm_num
  · rw [h.1]
    rcases h.2 with (hv | hv) <;> rw [hv] <;> norm_num

end SeatValues

end ThetLogos
