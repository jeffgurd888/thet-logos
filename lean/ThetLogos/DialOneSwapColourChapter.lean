import Mathlib.Tactic
import Mathlib.Analysis.Real.Pi.Irrational
import ThetLogos.DialOneSwapOrbitBase

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneDoubleFlipPin
open ThetLogos.DialOneGammaTraceChecks
open ThetLogos.DialOneGammaFamilyPin
open ThetLogos.DialOneGammaFamilyChecks
open ThetLogos.DialOneClassificationPin
open ThetLogos.DialOneSwapOrbit
open ThetLogos.DialOneSwapOrbitBase

/-!
# CLS-3b — the single-colour quark-swap chapter (Dial-1 lane)

Per colour `c ∈ {0, 1, 2}`, the full status of the
single-colour quark swap `piSwap c` (π₁ with the
conjugation toggles at colour `c`'s quark-R pair
`(uSeat c, dSeat c) = (10 + 2c, 11 + 2c)`), at each
condition-set grade. Each colour is proved SEPARATELY
below (per-colour theorems for `0`, `1`, `2`); the
generic-`c` lemmas they cite are the landed FAM-check
lemmas, themselves proved per colour in that module
(`not_base_piSwap0/1/2`). No symmetry across colours is
assumed anywhere.

## Verdicts (all T1, machine-checked below)

* **FAMILY holds, every colour**: `GammaFamily (piSwap c)`
  (`gammaFamily_piSwap`, landed): a swap is invisible to
  every clean functional — against `colProj c` the two
  singles contribute `+2α·i` and `−2α·i` and cancel;
  against every other projection they vanish.
* **BASE fails, every colour, at order-zero**:
  `¬ DialOneBase (piSwap c)` (landed per colour:
  `not_base_piSwap0/1/2`). The witness entry differs per
  colour, against `rho1`'s colour-matrix quark block:
  colour 0 — entry `(uSeat 0, uSeat 1)`, `b` carrying the
  colour single `single 1 0 1` (`star i = −i` vs `+i`);
  colour 1 — entry `(uSeat 1, uSeat 2)`, colour single
  `single 2 1 1`; colour 2 — entry `(uSeat 2, uSeat 0)`,
  colour single `single 0 2 1`.
* **STRENGTHENED fails, every colour**:
  `¬ DialOneStrengthenedFam (piSwap c)`, assembled
  explicitly from the Base failure (Base is the first
  conjunct). **The exclusion of a single-colour swap is
  by BASE (order-zero) — NOT by the family and NOT by
  weightlessness.**
* **WEIGHTS**: `piSwap c` is NOT weightless. Its own
  swapped weight vector `swappedWeightVector c` — the
  common vector with the `u_R`/`d_R` entries at colour
  `c` exchanged (both the particle seats `uSeat c` /
  `dSeat c` and their partner seats, whose lifted
  weights are the same numbers) — IS realized:
  `weightAt (piSwap c) (swappedWeightVector c)` along
  the primitive direction `(3, -1)`, where the swapped
  seats carry `-2` (the `d_R` table value) at the `u_R`
  seats and `4` (the `u_R` table value) at the `d_R`
  seats. And the common vector is NOT carried:
  `¬ weightAt (piSwap c) commonWeightVector` — along any
  primitive det-1 direction (forced to `±(3, -1)` by the
  determinant, exactly as for π₁) the lifted character
  at `uSeat c` is `exp (∓2 · t · i)`, never the common
  `exp (4 · t · i)`.

## Chapter boundary

The uniform triple swap contrasts on every axis
(CLS-2b, landed, cited in `swap_colour_chapter`):
`orbitRep allSwapBits` lies IN base + family
(`allSwap_mem_strengthened`) with the WRONG weights
(`allSwap_not_weightAt_common`). Singly, a colour swap
is out by Base; uniformly, the triple swap is in and
merely mis-weighted.

**K-CMP-F1 stays silent**: no single-colour swap is in
base+family, so no forcing consequence is claimed
either way from this chapter (the landed
`kCMP_F1_does_not_fire` is the FAM module's statement;
nothing here re-opens it).

**NO CLAIM; Dial 1 = 0; all dials 0/4. Classification
data only: parts of any official statement closed by
this module: 0.**
-/

namespace ThetLogos.DialOneSwapColourChapter

/-! ## The swapped weight vector -/

/-- **The swapped A-weight**: π₁'s `pi1AVal` with the
`u_R^c` seat's weight `1` and the `d_R^c` seat's weight
`-1` exchanged — the diagonal of `piSwap c` in
exponential form (see `updDiag_exp_gen`). -/
def swapA (c : Fin 3) (s : Fin 32) : ℤ :=
  if s = uSeat c then -1
  else if s = dSeat c then 1
  else pi1AVal s.val

/-- **The swap's own weight vector**: the common weight
vector with the `u_R`/`d_R` entries at colour `c`
exchanged. The exchange seats are the particle seats
`uSeat c`, `dSeat c` AND their partner seats — the
lifted weight `W s + W (partner s)` is partner-symmetric
(`commonWeightVector_partner`), so the partner seats
carry the same table values (`4` at the `u_R` pair,
`-2` at the `d_R` pair) and swap with them. -/
def swappedWeightVector (c : Fin 3) : Fin 32 → ℤ :=
  fun s =>
    if s = uSeat c ∨ s = partner (uSeat c) then
      commonWeightVector (dSeat c)
    else if s = dSeat c ∨ s = partner (dSeat c) then
      commonWeightVector (uSeat c)
    else commonWeightVector s

/-! ## Seat and weight read-backs -/

/-- The partner of the down seat is the literal
`27 + 2c` seat (the `dSeat` analogue of the landed
`partner_uSeat`). -/
theorem partner_dSeat (c : Fin 3) :
    partner (dSeat c) = ⟨27 + 2 * c.val, by have h := c.isLt; omega⟩ := by
  apply Fin.ext
  show (partner (dSeat c)).val = 27 + 2 * c.val
  rw [partner_val_eq]
  have hv : (dSeat c).val = 11 + 2 * c.val := rfl
  rw [hv]
  have hc3 := c.isLt
  rw [if_pos (by omega : 11 + 2 * c.val < 16)]
  omega

/-- The common weight vector is partner-symmetric:
the lifted weight at a seat equals that at its
partner. -/
theorem commonWeightVector_partner (s : Fin 32) :
    commonWeightVector (partner s) = commonWeightVector s := by
  show ThetLogos.Track1RouteB.W (partner s)
      + ThetLogos.Track1RouteB.W (partner (partner s))
    = ThetLogos.Track1RouteB.W s + ThetLogos.Track1RouteB.W (partner s)
  rw [partner_involutive]
  exact add_comm _ _

/-- The common weight at the up seat of any colour
is `4` (the table's `u_R` lifted weight). -/
theorem commonWeightVector_uSeat (c : Fin 3) :
    commonWeightVector (uSeat c) = 4 := by
  fin_cases c <;> decide

/-- The common weight at the down seat of any colour
is `-2` (the table's `d_R` lifted weight). -/
theorem commonWeightVector_dSeat (c : Fin 3) :
    commonWeightVector (dSeat c) = -2 := by
  fin_cases c <;> decide

/-- `updDiag` at the partner of the down seat is
`star μ` (the `dSeat` analogue of the landed
`updDiag_partner_uSeat`). -/
theorem updDiag_partner_dSeat (c : Fin 3) (lam μ : ℂ) :
    updDiag c lam μ (partner (dSeat c)) = star μ := by
  rw [partner_dSeat]
  have h1 : (⟨27 + 2 * c.val, by have h := c.isLt; omega⟩ : Fin 32)
      ≠ uSeat c := by
    intro h
    have hv := congrArg Fin.val h
    simp [uSeat] at hv
  have h2 : (⟨27 + 2 * c.val, by have h := c.isLt; omega⟩ : Fin 32)
      ≠ dSeat c := by
    intro h
    have hv := congrArg Fin.val h
    simp [dSeat] at hv
  rw [updDiag_eq_pi1Diag_of_ne c lam μ _ h1 h2]
  show pi1DiagVal lam μ (27 + 2 * c.val) = star μ
  have h3 : pi1DiagVal lam μ (26 + 2 * c.val + 1) = star μ := by
    simpa using pi1DiagVal_quarkRc lam μ c 1
  have e : 27 + 2 * c.val = 26 + 2 * c.val + 1 := by omega
  rw [e]
  exact h3

/-- `swapA` at the up seat is `-1` (π₁'s `d_R` A-value). -/
theorem swapA_uSeat (c : Fin 3) : swapA c (uSeat c) = -1 := by
  simp [swapA]

/-- `swapA` at the down seat is `1` (π₁'s `u_R` A-value). -/
theorem swapA_dSeat (c : Fin 3) : swapA c (dSeat c) = 1 := by
  have hne : dSeat c ≠ uSeat c := dSeat_ne_uSeat c
  simp [swapA, hne]

/-- `swapA` away from the two swapped seats is π₁'s
own A-value. -/
theorem swapA_of_ne (c : Fin 3) (s : Fin 32)
    (h1 : s ≠ uSeat c) (h2 : s ≠ dSeat c) :
    swapA c s = pi1AVal s.val := by
  simp [swapA, h1, h2]

/-- `swapA` at the partner of the up seat is `0`:
the partner seat is untouched and its A-value
(`26 + 2c ≥ 26`) is `0`. -/
theorem swapA_partner_uSeat (c : Fin 3) :
    swapA c (partner (uSeat c)) = 0 := by
  have h1 : partner (uSeat c) ≠ uSeat c := by
    intro h
    have hv := congrArg Fin.val h
    have hv2 : (partner (uSeat c)).val = 26 + 2 * c.val := by
      rw [partner_uSeat]
    have hv3 : (uSeat c).val = 10 + 2 * c.val := rfl
    rw [hv2, hv3] at hv
    omega
  have h2 : partner (uSeat c) ≠ dSeat c := by
    intro h
    have hv := congrArg Fin.val h
    have hv2 : (partner (uSeat c)).val = 26 + 2 * c.val := by
      rw [partner_uSeat]
    have hv3 : (dSeat c).val = 11 + 2 * c.val := rfl
    rw [hv2, hv3] at hv
    omega
  rw [swapA_of_ne c _ h1 h2, partner_uSeat]
  fin_cases c <;> decide

/-- `swapA` at the partner of the down seat is `0`:
the partner seat is untouched and its A-value
(`27 + 2c ≥ 26`) is `0`. -/
theorem swapA_partner_dSeat (c : Fin 3) :
    swapA c (partner (dSeat c)) = 0 := by
  have h1 : partner (dSeat c) ≠ uSeat c := by
    intro h
    have hv := congrArg Fin.val h
    have hv2 : (partner (dSeat c)).val = 27 + 2 * c.val := by
      rw [partner_dSeat]
    have hv3 : (uSeat c).val = 10 + 2 * c.val := rfl
    rw [hv2, hv3] at hv
    omega
  have h2 : partner (dSeat c) ≠ dSeat c := by
    intro h
    have hv := congrArg Fin.val h
    have hv2 : (partner (dSeat c)).val = 27 + 2 * c.val := by
      rw [partner_dSeat]
    have hv3 : (dSeat c).val = 11 + 2 * c.val := rfl
    rw [hv2, hv3] at hv
    omega
  rw [swapA_of_ne c _ h1 h2, partner_dSeat]
  fin_cases c <;> decide

/-- The B-value at the up seat is `0` (quark-R block). -/
theorem pi1BVal_uSeat (c : Fin 3) : pi1BVal (uSeat c).val = 0 := by
  fin_cases c <;> decide

/-- The B-value at the down seat is `0` (quark-R block). -/
theorem pi1BVal_dSeat (c : Fin 3) : pi1BVal (dSeat c).val = 0 := by
  fin_cases c <;> decide

/-- The B-value at the partner of the up seat is `-1`
(antiquark block). -/
theorem pi1BVal_partner_uSeat (c : Fin 3) :
    pi1BVal (partner (uSeat c)).val = -1 := by
  rw [partner_uSeat]
  fin_cases c <;> decide

/-- The B-value at the partner of the down seat is
`-1` (antiquark block). -/
theorem pi1BVal_partner_dSeat (c : Fin 3) :
    pi1BVal (partner (dSeat c)).val = -1 := by
  rw [partner_dSeat]
  fin_cases c <;> decide

/-- The B-values sum to `-12` over the 32 seats
(π₁'s landed `sum_B`, restated over `Fin 32`). -/
theorem sum_pi1BVal : ∑ s : Fin 32, pi1BVal s.val = -12 :=
  sum_B

/-- `swapA` sums to `-4` over the 32 seats, exactly as
π₁'s A-values do (exchanging `1` and `-1` preserves
the sum) — the determinant exponent is unchanged. -/
theorem sum_swapA (c : Fin 3) : ∑ s : Fin 32, swapA c s = -4 := by
  fin_cases c <;> decide

/-! ## The swap diagonal in exponential form -/

/-- **The swap diagonal in exponential form**: along
the two-parameter family, `updDiag c` at seat `s` is
the pure character with exponent
`swapA c s · α + pi1BVal s · β` — π₁'s landed
`pi1Diag_exp_gen` with the two quark-R A-values at
colour `c` exchanged. -/
theorem updDiag_exp_gen (c : Fin 3) (α β : ℤ) (t : ℝ) (s : Fin 32) :
    updDiag c (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
        (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) s
      = Complex.exp
          (((swapA c s * α + pi1BVal s.val * β : ℤ) : ℂ)
            * ((t : ℂ) * Complex.I)) := by
  by_cases hd : s = dSeat c
  · subst hd
    rw [updDiag_dSeat, swapA_dSeat, pi1BVal_dSeat]
    congr 1
    push_cast
    ring
  · by_cases hu : s = uSeat c
    · subst hu
      rw [updDiag_uSeat, star_exp_int, swapA_uSeat, pi1BVal_uSeat]
      congr 1
      push_cast
      ring
    · rw [updDiag_eq_pi1Diag_of_ne c _ _ s hu hd,
        pi1Diag_exp_gen, swapA_of_ne c s hu hd]

/-- **The swap determinant along the family** is
π₁'s own: `exp ((-4α - 12β) · t · i)` — the A-sum is
preserved by the exchange and the B-values are
untouched. -/
theorem piSwap_det_gen (c : Fin 3) (α β : ℤ) (t : ℝ) :
    (piSwap c (u1ParamGen α β t)).det
      = Complex.exp (((-4 * α + -12 * β : ℤ) : ℂ)
          * ((t : ℂ) * Complex.I)) := by
  have hsum : ∑ i : Fin 32, (swapA c i * α + pi1BVal i.val * β)
      = -4 * α + -12 * β := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      sum_swapA, sum_pi1BVal]
  rw [piSwap_eq_diagonal, Matrix.det_diagonal,
    Finset.prod_congr rfl (fun i _ => updDiag_exp_gen c α β t i),
    ← Complex.exp_sum, ← Finset.sum_mul, ← Int.cast_sum, hsum]

/-- **The swap's lifted entry in exponential form**:
the lifted eigenvalue at seat `s` is the pure
character whose exponent is the sum of the seat's and
its partner's `updDiag` exponents. -/
theorem piSwap_lifted_exp_gen (c : Fin 3) (α β : ℤ) (t : ℝ)
    (s : Fin 32) :
    (piSwap c (u1ParamGen α β t)
        * piOp (piSwap c (u1ParamGen α β t))) s s
      = Complex.exp
          ((((swapA c s + swapA c (partner s)) * α
              + (pi1BVal s.val + pi1BVal (partner s).val) * β : ℤ) : ℂ)
            * ((t : ℂ) * Complex.I)) := by
  rw [piSwap_lifted_entry, updDiag_exp_gen, updDiag_exp_gen,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The swapped vector is the `(3, -1)` exponent**:
at the surviving direction, the lifted exponent of
`piSwap c` at every seat is exactly
`swappedWeightVector c s`. -/
theorem swappedWeightVector_eq (c : Fin 3) (s : Fin 32) :
    swappedWeightVector c s
      = (swapA c s + swapA c (partner s)) * 3
        + (pi1BVal s.val + pi1BVal (partner s).val) * (-1) := by
  fin_cases c <;> fin_cases s <;> decide

/-! ## Weights: the swap is not weightless -/

/-- **The swap's own weights are realized**: along the
primitive direction `(3, -1)` (gcd `1`, determinant
`1` by `piSwap_det_gen`), `piSwap c` carries its
swapped weight vector. -/
theorem weightAt_piSwap_swapped (c : Fin 3) :
    weightAt (piSwap c) (swappedWeightVector c) := by
  refine ⟨3, -1, by decide, ?_, ?_⟩
  · intro t
    have h0 : (-4 * (3 : ℤ) + -12 * (-1) : ℤ) = 0 := rfl
    rw [piSwap_det_gen, h0, Int.cast_zero, zero_mul, Complex.exp_zero]
  · intro t s
    rw [piSwap_lifted_exp_gen, swappedWeightVector_eq]
    congr 1
    push_cast
    ring

/-- **The swap's lifted entry at its own up seat**:
the character is `exp ((-α - β) · t · i)` — against
π₁'s `exp ((α - β) · t · i)` there. -/
theorem piSwap_lifted_uSeat (c : Fin 3) (α β : ℤ) (t : ℝ) :
    (piSwap c (u1ParamGen α β t)
        * piOp (piSwap c (u1ParamGen α β t)))
        (uSeat c) (uSeat c)
      = Complex.exp (((-α - β : ℤ) : ℂ) * (t : ℂ) * Complex.I) := by
  rw [piSwap_lifted_exp_gen, swapA_uSeat, swapA_partner_uSeat,
    pi1BVal_uSeat, pi1BVal_partner_uSeat]
  congr 1
  push_cast
  ring

/-- **The swap does NOT carry the common weights**:
along any primitive det-1 direction the determinant
forces `(α, β) = ±(3, -1)` (as for π₁, via
`piSwap_det_gen`), so the up-seat character is
`exp (∓2 · t · i)`, never the common `exp (4 · t · i)`
— character rigidity (`exp_char_rigidity`, landed for
the all-swap read-back) closes it. -/
theorem not_weightAt_piSwap_common (c : Fin 3) :
    ¬ weightAt (piSwap c) commonWeightVector := by
  rintro ⟨α, β, hgcd, hdet, hlift⟩
  have hdet2 : Complex.exp (((-4 * α + -12 * β : ℤ) : ℂ)
      * Complex.I) = 1 := by
    have h := hdet 1
    rw [piSwap_det_gen] at h
    simpa only [Complex.ofReal_one, one_mul] using h
  obtain ⟨n, hn⟩ := (Complex.exp_eq_one_iff).mp hdet2
  have him : ((-4 * α + -12 * β : ℤ) : ℝ)
      = (n : ℝ) * (2 * Real.pi) :=
    im_int_mul_I (-4 * α + -12 * β) n hn
  have hαβ : α = -3 * β := by
    by_cases hn0 : n = 0
    · rw [hn0] at him
      simp at him
      have h5 : -4 * α + -12 * β = 0 := by
        have hR : ((-4 * α + -12 * β : ℤ) : ℝ) = 0 := by
          push_cast
          linarith [him]
        exact_mod_cast hR
      omega
    · exfalso
      apply irrational_pi.ne_rational (-4 * α + -12 * β) (2 * n)
      rw [eq_div_iff (by simp [hn0] : ((2 * n : ℤ) : ℝ) ≠ 0)]
      push_cast
      push_cast at him
      linarith [him]
  have hβ : β = 1 ∨ β = -1 := by
    have h1 : β.natAbs = 1 := by
      have hα : α.natAbs = 3 * β.natAbs := by
        rw [hαβ]
        simp [Int.natAbs_mul]
      have hdvd : β.natAbs ∣ 1 := by
        rw [← hgcd, hα]
        exact dvd_gcd (dvd_mul_left _ _) dvd_rfl
      exact Nat.dvd_one.mp hdvd
    exact Int.isUnit_iff.mp (Int.isUnit_iff_natAbs_eq.mpr h1)
  have hentry : ∀ t : ℝ,
      Complex.exp (((-α - β : ℤ) : ℂ) * (t : ℂ) * Complex.I)
        = Complex.exp (((4 : ℤ) : ℂ) * (t : ℂ) * Complex.I) := by
    intro t
    have h := hlift t (uSeat c)
    rwa [commonWeightVector_uSeat, piSwap_lifted_uSeat] at h
  rcases hβ with hβ1 | hβ1
  · have hα : α = -3 := by omega
    apply exp_char_rigidity (w := 2) (by norm_num)
    intro t
    have h := hentry t
    rwa [show ((-α - β : ℤ) : ℂ) = ((2 : ℤ) : ℂ) by
      rw [hα, hβ1]; norm_num] at h
  · have hα : α = 3 := by omega
    apply exp_char_rigidity (w := -2) (by norm_num)
    intro t
    have h := hentry t
    rwa [show ((-α - β : ℤ) : ℂ) = ((-2 : ℤ) : ℂ) by
      rw [hα, hβ1]; norm_num] at h

/-! ## Per-colour status: colour 0 -/

/-- Colour 0 — FAMILY holds. -/
theorem family_piSwap0 : GammaFamily (piSwap 0) :=
  gammaFamily_piSwap 0

/-- Colour 0 — BASE fails at order-zero (landed
witness: entry `(uSeat 0, uSeat 1)`, colour single
`single 1 0 1`; `star i` vs `i`). -/
theorem not_base_piSwap0_ch : ¬ DialOneBase (piSwap 0) :=
  not_base_piSwap0

/-- Colour 0 — STRENGTHENED fails, by Base. -/
theorem not_strengthened_piSwap0_ch :
    ¬ DialOneStrengthenedFam (piSwap 0) :=
  fun h => not_base_piSwap0 h.1

/-- Colour 0 — its own swapped weights are realized. -/
theorem weightAt_piSwap0_swapped :
    weightAt (piSwap 0) (swappedWeightVector 0) :=
  weightAt_piSwap_swapped 0

/-- Colour 0 — the common weights are NOT carried. -/
theorem not_weightAt_piSwap0_common :
    ¬ weightAt (piSwap 0) commonWeightVector :=
  not_weightAt_piSwap_common 0

/-- **Colour 0 — the full status assembly.** -/
theorem swap_colour0_status :
    GammaFamily (piSwap 0)
      ∧ ¬ DialOneBase (piSwap 0)
      ∧ ¬ DialOneStrengthenedFam (piSwap 0)
      ∧ weightAt (piSwap 0) (swappedWeightVector 0)
      ∧ ¬ weightAt (piSwap 0) commonWeightVector :=
  ⟨family_piSwap0, not_base_piSwap0_ch, not_strengthened_piSwap0_ch,
    weightAt_piSwap0_swapped, not_weightAt_piSwap0_common⟩

/-! ## Per-colour status: colour 1 -/

/-- Colour 1 — FAMILY holds. -/
theorem family_piSwap1 : GammaFamily (piSwap 1) :=
  gammaFamily_piSwap 1

/-- Colour 1 — BASE fails at order-zero (landed
witness: entry `(uSeat 1, uSeat 2)`, colour single
`single 2 1 1`; `star i` vs `i`). -/
theorem not_base_piSwap1_ch : ¬ DialOneBase (piSwap 1) :=
  not_base_piSwap1

/-- Colour 1 — STRENGTHENED fails, by Base. -/
theorem not_strengthened_piSwap1_ch :
    ¬ DialOneStrengthenedFam (piSwap 1) :=
  fun h => not_base_piSwap1 h.1

/-- Colour 1 — its own swapped weights are realized. -/
theorem weightAt_piSwap1_swapped :
    weightAt (piSwap 1) (swappedWeightVector 1) :=
  weightAt_piSwap_swapped 1

/-- Colour 1 — the common weights are NOT carried. -/
theorem not_weightAt_piSwap1_common :
    ¬ weightAt (piSwap 1) commonWeightVector :=
  not_weightAt_piSwap_common 1

/-- **Colour 1 — the full status assembly.** -/
theorem swap_colour1_status :
    GammaFamily (piSwap 1)
      ∧ ¬ DialOneBase (piSwap 1)
      ∧ ¬ DialOneStrengthenedFam (piSwap 1)
      ∧ weightAt (piSwap 1) (swappedWeightVector 1)
      ∧ ¬ weightAt (piSwap 1) commonWeightVector :=
  ⟨family_piSwap1, not_base_piSwap1_ch, not_strengthened_piSwap1_ch,
    weightAt_piSwap1_swapped, not_weightAt_piSwap1_common⟩

/-! ## Per-colour status: colour 2 -/

/-- Colour 2 — FAMILY holds. -/
theorem family_piSwap2 : GammaFamily (piSwap 2) :=
  gammaFamily_piSwap 2

/-- Colour 2 — BASE fails at order-zero (landed
witness: entry `(uSeat 2, uSeat 0)`, colour single
`single 0 2 1`; `star i` vs `i`). -/
theorem not_base_piSwap2_ch : ¬ DialOneBase (piSwap 2) :=
  not_base_piSwap2

/-- Colour 2 — STRENGTHENED fails, by Base. -/
theorem not_strengthened_piSwap2_ch :
    ¬ DialOneStrengthenedFam (piSwap 2) :=
  fun h => not_base_piSwap2 h.1

/-- Colour 2 — its own swapped weights are realized. -/
theorem weightAt_piSwap2_swapped :
    weightAt (piSwap 2) (swappedWeightVector 2) :=
  weightAt_piSwap_swapped 2

/-- Colour 2 — the common weights are NOT carried. -/
theorem not_weightAt_piSwap2_common :
    ¬ weightAt (piSwap 2) commonWeightVector :=
  not_weightAt_piSwap_common 2

/-- **Colour 2 — the full status assembly.** -/
theorem swap_colour2_status :
    GammaFamily (piSwap 2)
      ∧ ¬ DialOneBase (piSwap 2)
      ∧ ¬ DialOneStrengthenedFam (piSwap 2)
      ∧ weightAt (piSwap 2) (swappedWeightVector 2)
      ∧ ¬ weightAt (piSwap 2) commonWeightVector :=
  ⟨family_piSwap2, not_base_piSwap2_ch, not_strengthened_piSwap2_ch,
    weightAt_piSwap2_swapped, not_weightAt_piSwap2_common⟩

/-! ## The chapter assembly -/

/-- **The per-colour status, uniform form**: for
every colour, family holds, Base fails, the
strengthened set fails (by Base), the swap's own
swapped weights are realized, and the common weights
are not carried. -/
theorem swap_colour_status (c : Fin 3) :
    GammaFamily (piSwap c)
      ∧ ¬ DialOneBase (piSwap c)
      ∧ ¬ DialOneStrengthenedFam (piSwap c)
      ∧ weightAt (piSwap c) (swappedWeightVector c)
      ∧ ¬ weightAt (piSwap c) commonWeightVector :=
  ⟨gammaFamily_piSwap c, not_base_piSwap c,
    fun h => not_base_piSwap c h.1,
    weightAt_piSwap_swapped c, not_weightAt_piSwap_common c⟩

/-- **THE CHAPTER (CLS-3b)**: the three per-colour
assemblies, one per colour, proved separately above —
plus the chapter boundary: the uniform triple swap's
contrasting landed status (IN the strengthened set,
with the wrong weights), cited from CLS-2b. The
single-colour exclusion is by BASE (order-zero), not
by the family and not by weightlessness. K-CMP-F1
stays silent: no forcing consequence is claimed. -/
theorem swap_colour_chapter :
    (GammaFamily (piSwap 0)
      ∧ ¬ DialOneBase (piSwap 0)
      ∧ ¬ DialOneStrengthenedFam (piSwap 0)
      ∧ weightAt (piSwap 0) (swappedWeightVector 0)
      ∧ ¬ weightAt (piSwap 0) commonWeightVector)
    ∧ (GammaFamily (piSwap 1)
      ∧ ¬ DialOneBase (piSwap 1)
      ∧ ¬ DialOneStrengthenedFam (piSwap 1)
      ∧ weightAt (piSwap 1) (swappedWeightVector 1)
      ∧ ¬ weightAt (piSwap 1) commonWeightVector)
    ∧ (GammaFamily (piSwap 2)
      ∧ ¬ DialOneBase (piSwap 2)
      ∧ ¬ DialOneStrengthenedFam (piSwap 2)
      ∧ weightAt (piSwap 2) (swappedWeightVector 2)
      ∧ ¬ weightAt (piSwap 2) commonWeightVector)
    ∧ DialOneStrengthenedFam (orbitRep allSwapBits)
    ∧ ¬ weightAt (orbitRep allSwapBits) commonWeightVector :=
  ⟨swap_colour0_status, swap_colour1_status, swap_colour2_status,
    allSwap_mem_strengthened, allSwap_not_weightAt_common⟩

-- Axiom audit for the assembly headlines (expected:
-- [propext, Classical.choice, Quot.sound] throughout).
#print axioms weightAt_piSwap_swapped
#print axioms not_weightAt_piSwap_common
#print axioms swap_colour0_status
#print axioms swap_colour1_status
#print axioms swap_colour2_status
#print axioms swap_colour_chapter

end ThetLogos.DialOneSwapColourChapter
