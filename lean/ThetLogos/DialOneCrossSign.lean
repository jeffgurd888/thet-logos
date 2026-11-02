import Mathlib.Tactic
import ThetLogos.DialOneExtraction

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneDoubleFlipPin
open ThetLogos.DialOneGammaFamilyPin
open ThetLogos.DialOneClassificationPin
open ThetLogos.DialOneExtraction

namespace ThetLogos.DialOneCrossSign

/-!
# ThetLogos.DialOneCrossSign — CLS-1a-X: the cross-sign fragment of diagonality

**What this brick is.** CLS-1 (`DialOneExtraction`) named
`ExtractionLemma π` open: along one primitive determinant-one
direction, the lifted product `liftedProd π α β t` is diagonal
in the seat basis, and its diagonal entries are differentiable
at `0`. The CLS-1a scoping split that diagonality clause in
two. This module proves, at T1, the **cross-sign half** of it:

  for every `π` with `DialOneBase π`, every primitive
  direction `(α, β)` (`Nat.gcd α.natAbs β.natAbs = 1`, in the
  sense of `DialOneExtraction`), every `t`, and every ordered
  seat pair `(s, s')` whose γ-signs DIFFER
  (`gammaF s s ≠ gammaF s' s'`):
  `liftedProd π α β t s s' = 0`.

That is 512 ordered pairs on the 32-seat space: the γ-sign
classes are `V₊ = {0..7, 24..31}` and `V₋ = {8..23}`, 16 seats
each (`gammaF = diag(+1⁸, −1⁸, −1⁸, +1⁸)`), so the cross-sign
ordered pairs number `16 × 16 × 2 = 512`. The ONLY base input
is **clause 7 (grading)** alone, via the landed projection
`DialOneExtraction.base_gamma`: `gammaF * π a = π a * gammaF`.
Entrywise that reads `γ_s · (π a) s s' = (π a) s s' · γ_{s'}`,
which forces `(π a) s s' = 0` when `γ_s ≠ γ_{s'}`; `piOp`
preserves the block form because `partner` flips the γ-sign
(`gammaF_partner_flip`); products of block-form matrices keep
the block form. Primitivity of `(α, β)` is in fact not used —
the vanishing holds for every direction — but the headline
is stated for the primitive directions of the extraction
seam, as registered.

**What this brick is NOT.** This is the cross-sign half of
`ExtractionLemma`'s diagonality ONLY. **Within-sign
diagonality is untouched and remains the named hypothesis
`DiagLift`**: seats `8` and `9`, for example, both carry
γ-sign `-1` (`DialOneExtraction.gamma_seats_eight_nine`), so
no statement here separates them, and the 480 within-sign
ordered off-diagonal pairs remain exactly as open as before.
**K-CLS-1a stays armed** at the seat pair `(8, 9)`. After
this brick, `ExtractionLemma`'s diagonality content is
within-sign only (together with the regularity half, which
is likewise untouched). NO CLAIM; Dial 1 = 0; all dials 0/4.
-/

/-! ## §1. γ-sign bookkeeping -/

/-- The diagonal of `gammaF`, read off its landed definition:
`+1` on seats `0–7` and `24–31`, `-1` on seats `8–23`. -/
theorem gammaF_diag_apply (i : Fin 32) :
    gammaF i i = if i.val < 8 then (1 : ℂ)
      else if i.val < 16 then -1
      else if i.val < 24 then -1 else 1 := by
  unfold gammaF
  simp

/-- Every γ-sign is `±1`. -/
theorem gammaF_diag_eq_one_or_neg_one (i : Fin 32) :
    gammaF i i = 1 ∨ gammaF i i = -1 := by
  rw [gammaF_diag_apply]
  split_ifs <;> simp_all

/-! ## §2. Clause 7 transported to entries -/

/-- **Clause 7 entrywise**: any matrix commuting with
`gammaF` vanishes at every cross-sign entry. From
`γ_s · M s s' = M s s' · γ_{s'}` with `γ_s, γ_{s'} ∈ {±1}`
distinct, `M s s' = -M s s'`, hence `M s s' = 0`. -/
theorem entry_eq_zero_of_gamma_ne {M : Matrix (Fin 32) (Fin 32) ℂ}
    (hcomm : gammaF * M = M * gammaF) {s s' : Fin 32}
    (hne : gammaF s s ≠ gammaF s' s') : M s s' = 0 := by
  have hentry : gammaF s s * M s s' = M s s' * gammaF s' s' := by
    have h := congrArg (fun X : Matrix (Fin 32) (Fin 32) ℂ => X s s') hcomm
    rwa [gammaF_mul_apply, mul_gammaF_apply] at h
  rcases gammaF_diag_eq_one_or_neg_one s with hs | hs <;>
    rcases gammaF_diag_eq_one_or_neg_one s' with hs' | hs'
  · exact absurd (hs.trans hs'.symm) hne
  · rw [hs, hs', one_mul, mul_neg, mul_one] at hentry
    have h2 : (2 : ℂ) * M s s' = 0 := by linear_combination hentry
    rcases mul_eq_zero.mp h2 with h20 | hx
    · norm_num at h20
    · exact hx
  · rw [hs, hs', neg_mul, one_mul, mul_one] at hentry
    have h2 : (2 : ℂ) * M s s' = 0 := by linear_combination -hentry
    rcases mul_eq_zero.mp h2 with h20 | hx
    · norm_num at h20
    · exact hx
  · exact absurd (hs.trans hs'.symm) hne

/-- **Clause 7 for `π` itself**: for a base `π` (only its
clause-7 projection `base_gamma` is used), every entry of
every `π a` at a cross-sign seat pair vanishes. -/
theorem pi_entry_eq_zero_of_gamma_ne
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) (h : DialOneBase π)
    (a : AF) {s s' : Fin 32} (hne : gammaF s s ≠ gammaF s' s') :
    π a s s' = 0 :=
  entry_eq_zero_of_gamma_ne (base_gamma π h a) hne

/-- **`piOp` preserves the γ-block form**: `piOp M s s'`
reads `M (partner s') (partner s)`, and `partner` flips
both γ-signs (`gammaF_partner_flip`), so the cross-sign
condition on `(s, s')` is the cross-sign condition on
`(partner s', partner s)`. -/
theorem piOp_entry_eq_zero_of_gamma_ne
    {M : Matrix (Fin 32) (Fin 32) ℂ}
    (hcomm : gammaF * M = M * gammaF) {s s' : Fin 32}
    (hne : gammaF s s ≠ gammaF s' s') : piOp M s s' = 0 := by
  rw [piOp_apply]
  apply entry_eq_zero_of_gamma_ne hcomm
  rw [gammaF_partner_flip, gammaF_partner_flip]
  intro hcon
  apply hne
  have h2 : gammaF s' s' = gammaF s s := by
    have h3 := congrArg Neg.neg hcon
    simpa using h3
  exact h2.symm

/-! ## §3. The lifted product: products preserve the block form -/

/-- The lifted product vanishes at cross-sign pairs, from
the grading commutation alone (stated for an arbitrary
commutation hypothesis, so the transport is visible): in
the sum `∑ k, (π g) s k * piOp (π g) k s'`, every middle
seat `k` shares its γ-sign with at most one of `s, s'`, so
every summand has a vanishing factor. -/
theorem liftedProd_eq_zero_of_gamma_comm
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (hgamma : ∀ a, gammaF * π a = π a * gammaF)
    (α β : ℤ) (t : ℝ) {s s' : Fin 32}
    (hne : gammaF s s ≠ gammaF s' s') :
    liftedProd π α β t s s' = 0 := by
  unfold liftedProd
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : gammaF k k = gammaF s' s'
  · have hsk : gammaF s s ≠ gammaF k k := by
      intro hcon
      exact hne (hcon.trans hk)
    rw [entry_eq_zero_of_gamma_ne (hgamma _) hsk, zero_mul]
  · rw [piOp_entry_eq_zero_of_gamma_ne (hgamma _) (s := k) (s' := s') hk,
      mul_zero]

/-- **THE HEADLINE (CLS-1a-X).** The cross-sign half of
`ExtractionLemma`'s diagonality, proved from
`DialOneBase`'s clause 7 (grading) alone: for every base
`π`, every primitive direction `(α, β)`, every `t`, and
every ordered seat pair `(s, s')` with DIFFERENT γ-signs,
`liftedProd π α β t s s' = 0` — 512 ordered pairs on the
32-seat space. Within-sign diagonality (e.g. seats `8`/`9`,
both sign `-1`) is NOT touched by this theorem and remains
the named hypothesis `DiagLift`; K-CLS-1a stays armed. -/
theorem liftedProd_eq_zero_of_gamma_sign_ne
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) (h : DialOneBase π)
    (α β : ℤ) (hgcd : Nat.gcd α.natAbs β.natAbs = 1) (t : ℝ)
    (s s' : Fin 32) (hne : gammaF s s ≠ gammaF s' s') :
    liftedProd π α β t s s' = 0 :=
  liftedProd_eq_zero_of_gamma_comm π (base_gamma π h) α β t hne

end ThetLogos.DialOneCrossSign
