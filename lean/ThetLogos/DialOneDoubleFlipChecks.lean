import Mathlib.Tactic
import ThetLogos.DialOneDoubleFlipPin
import ThetLogos.DialOneGammaTraceChecks

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneDoubleFlipPin
open ThetLogos.DialOneGammaTraceChecks

namespace ThetLogos.DialOneDoubleFlipChecks

/-!
# ThetLogos.DialOneDoubleFlipChecks — D1-CMP: the K-ESC-6 confirmation

Governing text: the compensator scoping dossier
(`routeb-general-scratch/scoping-d1-compensator-2026-11-01.md`),
which fired **K-ESC-6 at scoping level (T2)** and pre-registered
the kills K-CMP-1 (base transport failure at a named clause),
K-CMP-2 (proportionality arithmetic), K-CMP-3 (C3 gate failure)
against this T1 confirmation. The candidate `piDouble` and the
three confirmation statements `C3PiDoubleCheck`,
`BasePiDoubleCheck`, `NonProportionalCheck` are pinned in
`ThetLogos.DialOneDoubleFlipPin`; this module proves exactly
those statements.

## Verdicts (all three confirmations LAND; K-ESC-6 fires at T1)

* **(i) `C3 piDouble` HOLDS.** The γ_F-trace at `u1Gen α β` is
  `0` (π₁'s landed trace) `+ 2α·i` (seat 8, landed in D1-C3)
  `- 2α·i` (seat 9: `gammaF s9 s9 = -1` against the
  un-conjugation perturbation value `α·i - star (α·i) = +2α·i`).
  The seat-9 contribution computed here is exactly `-2α·i`.
  K-CMP-3 does NOT fire.
* **(ii) `DialOneBase piDouble` HOLDS**, clause by clause by
  transport off piFlip's landed base proofs
  (`piDouble = piFlip + Matrix.single s9 s9 (a.u1 - star a.u1)`,
  the seat-9 mirror perturbation over piFlip's seat-9 value
  `star a.u1`), with first-order transported over the
  `(1 ↔ 9)` Dirac pairing: `md s9 = s1`, `md s1 = s9`,
  `Dval s9 = Dval s1` (both `Ye`), the correction
  `single s1 s9 + single s9 s1` commuting with `rho1` (the
  ρ-diagonals at seats 1 and 9 are both `star b.u1`), with
  `rhoFlip` (disjoint seat-24 single), and with the seat-25
  single of `rhoDouble` (disjoint indices), and
  `[DF, piFlip a]` commuting with the seat-25 single (its
  row/column 25 vanish, transported from the landed
  row/column-24 vanishing at seats 17/25). K-CMP-1 does NOT
  fire at any clause.
* **(iii) `NonProportionalCheck` HOLDS.** Along `(3, -1)` the
  lifted eigenvalue at the ν_R sector is
  `star (exp (3t·i)) * star (exp (3t·i))` — the swapped e_R
  weight: at `t = π / 6` it is exactly `-1`, while the COMMON
  HYPERCHARGE MATRIX entry at ν_R is `0`, forcing the
  proportional value `1` for every `κ`. K-CMP-2 does NOT fire.

## The registered conclusion

`kESC6_fires_at_T1`: **`DialOneBase piDouble ∧ C3 piDouble`**
holds in Lean and piDouble's lifted weights are **not**
proportional to the COMMON HYPERCHARGE MATRIX's — **base + C3
forcing is FALSE in Lean, permanently**. D1-C3's landed
exclusion of piFlip stands untouched (C3 is a real condition;
it is one equation short, and now provably so).

**NO CLAIM. Dial 1 = 0; all dials 0/4** — on every outcome,
including this firing (a kill is not a dial move).
-/

/-! ## Seats used by the seat-9 transport -/

/-- The e_L slot (seat 1), the Dirac partner of `s9`. -/
abbrev s1 : Fin 32 := ⟨1, by omega⟩

/-- The e_L antiparticle slot (seat 17), the Dirac partner
of `s25`. -/
abbrev s17 : Fin 32 := ⟨17, by omega⟩

/-- The e_R antiparticle slot (seat 25), the J-partner
of `s9`. -/
abbrev s25 : Fin 32 := ⟨25, by omega⟩

/-! ## The step from piFlip to piDouble -/

/-- **The step identity**: `piDouble` is `piFlip` plus the
seat-9 mirror single. Everything below transports piFlip's
landed proofs along this one step. -/
theorem piDouble_eq_piFlip_add (a : AF) :
    piDouble a
      = piFlip a + Matrix.single s9 s9 (a.u1 - star a.u1) :=
  rfl

/-- **The opposite step**: `piOp ∘ piDouble` is `rhoFlip`
plus the seat-25 single (the J-partner seat of 9), with the
same coefficient (`piOp_single` preserves it). -/
theorem rhoDouble_eq_step (b : AF) :
    piOp (piDouble b)
      = rhoFlip b + Matrix.single s25 s25 (b.u1 - star b.u1) := by
  have hps9 : partner s9 = s25 := by
    apply Fin.ext
    simp [partner_val_eq]
  have h : piOp (piFlip b) = rhoFlip b := rfl
  rw [piDouble_eq_piFlip_add, piOp_add, piOp_single, hps9, h]

/-! ## Confirmation (i): the C3 trace -/

/-- **The γ_F-trace of `piDouble` at the generator is `0`**:
π₁'s landed trace `0`, the seat-8 contribution `+2α·i`
(landed, D1-C3), and the seat-9 contribution `-2α·i`
(`gammaF s9 s9 = -1` against `α·i - star (α·i) = +2α·i`)
cancel exactly. -/
theorem trace_gammaF_piDouble_u1Gen (α β : ℤ) :
    Matrix.trace (gammaF * piDouble (u1Gen α β)) = 0 := by
  have hsingle9 : ∀ c : ℂ,
      Matrix.trace (gammaF * Matrix.single s9 s9 c) = -c := by
    intro c
    rw [trace_gammaF_mul]
    have h9 : gammaF s9 s9 = -1 := by
      unfold gammaF
      simp [ThetLogos.DialOneDoubleFlipPin.s9]
    rw [Finset.sum_eq_single s9]
    · rw [h9]
      simp
    · intro i _ hi
      have hne : ¬ (s9 = i ∧ s9 = i) := fun h => hi h.1.symm
      have hsingle : Matrix.single s9 s9 c i i = 0 := by
        simp only [Matrix.single_apply, hne, ite_false]
      rw [hsingle, mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  have hu1 : (u1Gen α β).u1 = (α : ℂ) * Complex.I := rfl
  have hstar : star (u1Gen α β).u1 = -((α : ℂ) * Complex.I) := by
    rw [hu1]
    simp
  rw [ThetLogos.DialOneDoubleFlipPin.piDouble_unfold, mul_add,
    mul_add, Matrix.trace_add, Matrix.trace_add,
    trace_gammaF_pi1_u1Gen, trace_gammaF_single_s8, hsingle9,
    hstar, hu1]
  ring

/-- **Confirmation (i) — `C3PiDoubleCheck` HOLDS**:
`C3 piDouble`. K-CMP-3 does NOT fire. -/
theorem c3_piDouble_holds : C3PiDoubleCheck :=
  fun α β => trace_gammaF_piDouble_u1Gen α β

/-! ## Confirmation (ii): the base set, clause by clause -/

/-- **Clause `afMul` for `piDouble`**, transported from
`piFlip_afMul`: the seat-9 coefficient
`d(a) = a.u1 - star a.u1` over piFlip's seat-9 value
`star a.u1` satisfies the mirror identity
`d(ab) = star a.u1 * d(b) + (d(a) * star b.u1 + d(a) * d(b))`
(both sides `a.u1 * b.u1 - star a.u1 * star b.u1`). -/
theorem piDouble_afMul (a b : AF) :
    piDouble (afMul a b) = piDouble a * piDouble b := by
  have hpi1row9 : ∀ (x : AF) (j : Fin 32),
      pi1 x s9 j = if j = s9 then star x.u1 else 0 := by
    intro x j
    by_cases hj : j = s9
    · rw [if_pos hj, hj, pi1_entry_eR]
    · rw [if_neg hj]
      exact pi1_vanish_eR x j
        (fun h => absurd (Finset.mem_singleton.mp h) hj)
  have hpi1col9 : ∀ (x : AF) (i : Fin 32),
      pi1 x i s9 = if i = s9 then star x.u1 else 0 := by
    intro x i
    by_cases hi : i = s9
    · rw [if_pos hi, hi, pi1_entry_eR]
    · rw [if_neg hi]
      exact pi1_vanish_col_eR x i
        (fun h => absurd (Finset.mem_singleton.mp h) hi)
  have hrow9 : ∀ (x : AF) (j : Fin 32),
      piFlip x s9 j = if j = s9 then star x.u1 else 0 := by
    intro x j
    have hx : piFlip x s9 j = pi1 x s9 j := by
      rw [piFlip_apply,
        if_neg (fun hh : s9 = s8 ∧ j = s8 => absurd hh.1 (by decide))]
    rw [hx, hpi1row9]
  have hcol9 : ∀ (x : AF) (i : Fin 32),
      piFlip x i s9 = if i = s9 then star x.u1 else 0 := by
    intro x i
    have hx : piFlip x i s9 = pi1 x i s9 := by
      rw [piFlip_apply,
        if_neg (fun hh : i = s8 ∧ s9 = s8 => absurd hh.2 (by decide))]
    rw [hx, hpi1col9]
  have hsingle_mul : ∀ (c : ℂ) (x : AF),
      Matrix.single s9 s9 c * piFlip x
        = Matrix.single s9 s9 (c * star x.u1) := by
    intro c x
    ext i' j'
    rw [single_mul_apply, Matrix.single_apply, hrow9]
    by_cases hi : s9 = i'
    · rw [if_pos hi]
      by_cases hj : j' = s9
      · rw [if_pos hj, if_pos ⟨hi, hj.symm⟩]
      · rw [if_neg hj,
          if_neg (fun h : s9 = i' ∧ s9 = j' => hj h.2.symm),
          mul_zero]
    · rw [if_neg hi, if_neg (fun h : s9 = i' ∧ s9 = j' => hi h.1)]
  have hmul_single : ∀ (x : AF) (c : ℂ),
      piFlip x * Matrix.single s9 s9 c
        = Matrix.single s9 s9 (star x.u1 * c) := by
    intro x c
    ext i' j'
    rw [mul_single_apply, Matrix.single_apply, hcol9]
    by_cases hj : s9 = j'
    · rw [if_pos hj]
      by_cases hi : i' = s9
      · rw [if_pos hi, if_pos ⟨hi.symm, hj⟩]
      · rw [if_neg hi,
          if_neg (fun h : s9 = i' ∧ s9 = j' => hi h.1.symm),
          zero_mul]
    · rw [if_neg hj, if_neg (fun h : s9 = i' ∧ s9 = j' => hj h.2)]
  have hcoef : (afMul a b).u1 - star (afMul a b).u1
      = star a.u1 * (b.u1 - star b.u1)
        + ((a.u1 - star a.u1) * star b.u1
          + (a.u1 - star a.u1) * (b.u1 - star b.u1)) := by
    rw [afMul_u1, star_mul]
    ring
  rw [piDouble_eq_piFlip_add (afMul a b), piDouble_eq_piFlip_add a,
    piDouble_eq_piFlip_add b, add_mul, mul_add, mul_add,
    piFlip_afMul, hmul_single, hsingle_mul, single_mul_single,
    if_pos rfl, add_assoc, ← Matrix.single_add,
    ← Matrix.single_add, hcoef]

/-- **Clause `afAdd` for `piDouble`**, transported from
`piFlip_afAdd` (`star` is additive, so `d` is). -/
theorem piDouble_afAdd (a b : AF) :
    piDouble (afAdd a b) = piDouble a + piDouble b := by
  have hcoef : (afAdd a b).u1 - star (afAdd a b).u1
      = (a.u1 - star a.u1) + (b.u1 - star b.u1) := by
    rw [afAdd_u1, star_add]
    ring
  rw [piDouble_eq_piFlip_add (afAdd a b), piDouble_eq_piFlip_add a,
    piDouble_eq_piFlip_add b, piFlip_afAdd, add_add_add_comm,
    ← Matrix.single_add, hcoef]

/-- **Clause `afStar` for `piDouble`**, transported from
`piFlip_afStar`: `d(afStar a) = star (d a)`. -/
theorem piDouble_afStar (a : AF) :
    piDouble (afStar a) = (piDouble a)ᴴ := by
  have hcoef : (afStar a).u1 - star (afStar a).u1
      = star (a.u1 - star a.u1) := by
    rw [afStar_u1, star_sub, star_star]
  have hsingle : (Matrix.single s9 s9 (a.u1 - star a.u1))ᴴ
      = Matrix.single s9 s9 (star (a.u1 - star a.u1)) := by
    ext i j
    rw [Matrix.conjTranspose_apply, Matrix.single_apply,
      Matrix.single_apply]
    by_cases h : s9 = j ∧ s9 = i
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
    · rw [if_neg h,
        if_neg (fun hh : s9 = i ∧ s9 = j => h ⟨hh.2, hh.1⟩),
        star_zero]
  rw [piDouble_eq_piFlip_add (afStar a), piDouble_eq_piFlip_add a,
    Matrix.conjTranspose_add, piFlip_afStar, hsingle, hcoef]

/-- **Clause `afOne` for `piDouble`**: the seat-9 coefficient
vanishes at `a.u1 = 1`. -/
theorem piDouble_one : piDouble afOne = 1 := by
  have h0 : (afOne).u1 - star (afOne).u1 = 0 := by
    rw [afOne_u1]
    simp
  have hsingle0 : ∀ x : ℂ, x = 0 → Matrix.single s9 s9 x = 0 := by
    intro x hx
    subst hx
    ext i j
    simp [Matrix.single_apply]
  rw [piDouble_eq_piFlip_add, hsingle0 _ h0, add_zero, piFlip_one]

/-- **Clause `afZero` for `piDouble`**: the seat-9
coefficient vanishes at `a.u1 = 0`. -/
theorem piDouble_zero : piDouble afZero = 0 := by
  have h0 : (afZero).u1 - star (afZero).u1 = 0 := by
    rw [afZero_u1]
    simp
  have hsingle0 : ∀ x : ℂ, x = 0 → Matrix.single s9 s9 x = 0 := by
    intro x hx
    subst hx
    ext i j
    simp [Matrix.single_apply]
  rw [piDouble_eq_piFlip_add, hsingle0 _ h0, add_zero, piFlip_zero]

/-- **Clause injectivity for `piDouble`**: seat 9 now gives
`a.u1` directly (piFlip recovered it there via `star`); the
ℍ and colour recovery seats are untouched by either single. -/
theorem piDouble_injective : Function.Injective piDouble := by
  intro a b h
  obtain ⟨ua, qa, ma⟩ := a
  obtain ⟨ub, qb, mb⟩ := b
  have hflip9 : ∀ x : AF, piFlip x s9 s9 = star x.u1 := by
    intro x
    rw [piFlip_apply,
      if_neg (fun hh : s9 = s8 ∧ s9 = s8 => absurd hh.1 (by decide)),
      pi1_entry_eR]
  have he9 : ∀ x : AF, piDouble x s9 s9 = x.u1 := by
    intro x
    rw [piDouble_eq_piFlip_add, Matrix.add_apply,
      Matrix.single_apply, if_pos ⟨rfl, rfl⟩, hflip9]
    ring
  have happly : ∀ (x : AF) (i j : Fin 32),
      ¬ (i = s9 ∧ j = s9) → piDouble x i j = piFlip x i j := by
    intro x i j hh
    rw [piDouble_eq_piFlip_add, Matrix.add_apply,
      Matrix.single_apply,
      if_neg (fun hh' : s9 = i ∧ s9 = j => hh ⟨hh'.1.symm, hh'.2.symm⟩),
      add_zero]
  have hu1 : ua = ub := by
    have h9 := congrFun (congrFun h s9) s9
    rw [he9, he9] at h9
    exact h9
  have hq : qa = qb := by
    ext s t
    have hst := congrFun (congrFun h ⟨s.val, by omega⟩)
      ⟨t.val, by omega⟩
    have hh9 : ¬ ((⟨s.val, by omega⟩ : Fin 32) = s9
        ∧ (⟨t.val, by omega⟩ : Fin 32) = s9) := by
      rintro ⟨hh, -⟩
      have hval : s.val = 9 := congrArg Fin.val hh
      have hs := s.isLt
      omega
    rw [happly _ _ _ hh9, happly _ _ _ hh9, piFlip_apply,
      piFlip_apply] at hst
    have hne : ¬ ((⟨s.val, by omega⟩ : Fin 32) = s8
        ∧ (⟨t.val, by omega⟩ : Fin 32) = s8) := by
      rintro ⟨hh, -⟩
      have hval : s.val = 8 := congrArg Fin.val hh
      have hs := s.isLt
      omega
    rw [if_neg hne, if_neg hne, pi1_entry_leptonL,
      pi1_entry_leptonL] at hst
    exact hst
  have hcolor : ma = mb := by
    ext k l
    have hkl := congrFun (congrFun h
      ⟨18 + 2 * k.val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩)
      ⟨18 + 2 * l.val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩
    have hh9 : ¬ ((⟨18 + 2 * k.val + (⟨0, by omega⟩ : Fin 2).val,
          by omega⟩ : Fin 32) = s9
        ∧ (⟨18 + 2 * l.val + (⟨0, by omega⟩ : Fin 2).val,
          by omega⟩ : Fin 32) = s9) := by
      rintro ⟨hh, -⟩
      have hval : 18 + 2 * k.val + (⟨0, by omega⟩ : Fin 2).val = 9 :=
        congrArg Fin.val hh
      omega
    rw [happly _ _ _ hh9, happly _ _ _ hh9, piFlip_apply,
      piFlip_apply] at hkl
    have hne : ¬ ((⟨18 + 2 * k.val + (⟨0, by omega⟩ : Fin 2).val,
          by omega⟩ : Fin 32) = s8
        ∧ (⟨18 + 2 * l.val + (⟨0, by omega⟩ : Fin 2).val,
          by omega⟩ : Fin 32) = s8) := by
      rintro ⟨hh, -⟩
      have hval : 18 + 2 * k.val + (⟨0, by omega⟩ : Fin 2).val = 8 :=
        congrArg Fin.val hh
      omega
    rw [if_neg hne, if_neg hne,
      pi1_entry_quarkLc _ _ _ ⟨0, by omega⟩ ⟨0, by omega⟩,
      pi1_entry_quarkLc _ _ _ ⟨0, by omega⟩ ⟨0, by omega⟩] at hkl
    rw [if_pos rfl, if_pos rfl] at hkl
    have h2 := congrArg star hkl
    simp only [star_star] at h2
    exact h2
  simp [hu1, hq, hcolor]

/-- **Clause grading for `piDouble`**: a diagonal single at
seat 9 commutes with the diagonal `gammaF`, by the landed
seat-8 pattern. -/
theorem piDouble_grading_even (a : AF) :
    gammaF * piDouble a = piDouble a * gammaF := by
  have hsingle : gammaF * Matrix.single s9 s9 (a.u1 - star a.u1)
      = Matrix.single s9 s9 (a.u1 - star a.u1) * gammaF := by
    ext i j
    rw [gammaF_mul_apply, mul_gammaF_apply, Matrix.single_apply]
    by_cases h : s9 = i ∧ s9 = j
    · obtain ⟨rfl, rfl⟩ : i = s9 ∧ j = s9 := ⟨h.1.symm, h.2.symm⟩
      exact mul_comm _ _
    · rw [if_neg h, mul_zero, zero_mul]
  rw [piDouble_eq_piFlip_add, mul_add, add_mul,
    piFlip_grading_even, hsingle]

/-- **Clause order-zero for `piDouble`**, transported from
`piFlip_order_zero`: the seat-9 single commutes with
`rhoFlip` (both ρ-diagonals at seat 9 are `star b.u1`), the
seat-25 single of `rhoDouble` commutes with `piFlip` (both
seat-25 values are `star a.u1`), and the two singles are
disjoint. -/
theorem piDouble_order_zero (a b : AF) :
    piDouble a * piOp (piDouble b)
      = piOp (piDouble b) * piDouble a := by
  have hps25 : partner s25 = s9 := by
    apply Fin.ext
    simp [partner_val_eq]
  have hps9 : partner s9 = s25 := by
    apply Fin.ext
    simp [partner_val_eq]
  have hrho1row9 : ∀ j : Fin 32,
      rho1 b s9 j = if j = s9 then star b.u1 else 0 := by
    intro j
    by_cases hj : j = s9
    · rw [if_pos hj, hj]
      exact rho1_entry_eR b
    · rw [if_neg hj, rho1_entry, hps9]
      have hne : partner j ≠ s25 := by
        intro h1
        apply hj
        have h2 := congrArg partner h1
        rwa [partner_involutive, hps25] at h2
      exact pi1_vanish_col_eRc b (partner j)
        (fun hmem => hne (Finset.mem_singleton.mp hmem))
  have hrho1col9 : ∀ i : Fin 32,
      rho1 b i s9 = if i = s9 then star b.u1 else 0 := by
    intro i
    by_cases hi : i = s9
    · rw [if_pos hi, hi]
      exact rho1_entry_eR b
    · rw [if_neg hi, rho1_entry, hps9]
      have hne : partner i ≠ s25 := by
        intro h1
        apply hi
        have h2 := congrArg partner h1
        rwa [partner_involutive, hps25] at h2
      exact pi1_vanish_eRc b (partner i)
        (fun hmem => hne (Finset.mem_singleton.mp hmem))
  have hrhofliprow9 : ∀ j : Fin 32,
      rhoFlip b s9 j = if j = s9 then star b.u1 else 0 := by
    intro j
    have hx : rhoFlip b s9 j = rho1 b s9 j := by
      rw [rhoFlip_apply,
        if_neg (fun hh : s9 = s24 ∧ j = s24 =>
          absurd hh.1 (by decide))]
    rw [hx, hrho1row9]
  have hrhoflipcol9 : ∀ i : Fin 32,
      rhoFlip b i s9 = if i = s9 then star b.u1 else 0 := by
    intro i
    have hx : rhoFlip b i s9 = rho1 b i s9 := by
      rw [rhoFlip_apply,
        if_neg (fun hh : i = s24 ∧ s9 = s24 =>
          absurd hh.2 (by decide))]
    rw [hx, hrho1col9]
  have hpi1row25 : ∀ (x : AF) (j : Fin 32),
      pi1 x s25 j = if j = s25 then star x.u1 else 0 := by
    intro x j
    by_cases hj : j = s25
    · rw [if_pos hj, hj, pi1_entry_eRc]
    · rw [if_neg hj]
      exact pi1_vanish_eRc x j
        (fun h => absurd (Finset.mem_singleton.mp h) hj)
  have hpi1col25 : ∀ (x : AF) (i : Fin 32),
      pi1 x i s25 = if i = s25 then star x.u1 else 0 := by
    intro x i
    by_cases hi : i = s25
    · rw [if_pos hi, hi, pi1_entry_eRc]
    · rw [if_neg hi]
      exact pi1_vanish_col_eRc x i
        (fun h => absurd (Finset.mem_singleton.mp h) hi)
  have hfliprow25 : ∀ (x : AF) (j : Fin 32),
      piFlip x s25 j = if j = s25 then star x.u1 else 0 := by
    intro x j
    have hx : piFlip x s25 j = pi1 x s25 j := by
      rw [piFlip_apply,
        if_neg (fun hh : s25 = s8 ∧ j = s8 =>
          absurd hh.1 (by decide))]
    rw [hx, hpi1row25]
  have hflipcol25 : ∀ (x : AF) (i : Fin 32),
      piFlip x i s25 = if i = s25 then star x.u1 else 0 := by
    intro x i
    have hx : piFlip x i s25 = pi1 x i s25 := by
      rw [piFlip_apply,
        if_neg (fun hh : i = s8 ∧ s25 = s8 =>
          absurd hh.2 (by decide))]
    rw [hx, hpi1col25]
  have hsingle25_mul : ∀ (c : ℂ) (x : AF),
      Matrix.single s25 s25 c * piFlip x
        = Matrix.single s25 s25 (c * star x.u1) := by
    intro c x
    ext i' j'
    rw [single_mul_apply, Matrix.single_apply, hfliprow25]
    by_cases hi : s25 = i'
    · rw [if_pos hi]
      by_cases hj : j' = s25
      · rw [if_pos hj, if_pos ⟨hi, hj.symm⟩]
      · rw [if_neg hj,
          if_neg (fun h : s25 = i' ∧ s25 = j' => hj h.2.symm),
          mul_zero]
    · rw [if_neg hi,
        if_neg (fun h : s25 = i' ∧ s25 = j' => hi h.1)]
  have hmul_single25 : ∀ (x : AF) (c : ℂ),
      piFlip x * Matrix.single s25 s25 c
        = Matrix.single s25 s25 (star x.u1 * c) := by
    intro x c
    ext i' j'
    rw [mul_single_apply, Matrix.single_apply, hflipcol25]
    by_cases hj : s25 = j'
    · rw [if_pos hj]
      by_cases hi : i' = s25
      · rw [if_pos hi, if_pos ⟨hi.symm, hj⟩]
      · rw [if_neg hi,
          if_neg (fun h : s25 = i' ∧ s25 = j' => hi h.1.symm),
          zero_mul]
    · rw [if_neg hj,
        if_neg (fun h : s25 = i' ∧ s25 = j' => hj h.2)]
  have hsingle9_mul : ∀ (c : ℂ) (y : AF),
      Matrix.single s9 s9 c * rhoFlip y
        = Matrix.single s9 s9 (c * star y.u1) := by
    intro c y
    ext i' j'
    rw [single_mul_apply, Matrix.single_apply]
    have hrow : ∀ j : Fin 32,
        rhoFlip y s9 j = if j = s9 then star y.u1 else 0 := by
      intro j
      have hx : rhoFlip y s9 j = rho1 y s9 j := by
        rw [rhoFlip_apply,
          if_neg (fun hh : s9 = s24 ∧ j = s24 =>
            absurd hh.1 (by decide))]
      rw [hx]
      by_cases hj : j = s9
      · rw [if_pos hj, hj]
        exact rho1_entry_eR y
      · rw [if_neg hj, rho1_entry, hps9]
        have hne : partner j ≠ s25 := by
          intro h1
          apply hj
          have h2 := congrArg partner h1
          rwa [partner_involutive, hps25] at h2
        exact pi1_vanish_col_eRc y (partner j)
          (fun hmem => hne (Finset.mem_singleton.mp hmem))
    rw [hrow]
    by_cases hi : s9 = i'
    · rw [if_pos hi]
      by_cases hj : j' = s9
      · rw [if_pos hj, if_pos ⟨hi, hj.symm⟩]
      · rw [if_neg hj,
          if_neg (fun h : s9 = i' ∧ s9 = j' => hj h.2.symm),
          mul_zero]
    · rw [if_neg hi, if_neg (fun h : s9 = i' ∧ s9 = j' => hi h.1)]
  have hmul_single9 : ∀ (y : AF) (c : ℂ),
      rhoFlip y * Matrix.single s9 s9 c
        = Matrix.single s9 s9 (star y.u1 * c) := by
    intro y c
    ext i' j'
    rw [mul_single_apply, Matrix.single_apply]
    have hcol : ∀ i : Fin 32,
        rhoFlip y i s9 = if i = s9 then star y.u1 else 0 := by
      intro i
      have hx : rhoFlip y i s9 = rho1 y i s9 := by
        rw [rhoFlip_apply,
          if_neg (fun hh : i = s24 ∧ s9 = s24 =>
            absurd hh.2 (by decide))]
      rw [hx]
      by_cases hi : i = s9
      · rw [if_pos hi, hi]
        exact rho1_entry_eR y
      · rw [if_neg hi, rho1_entry, hps9]
        have hne : partner i ≠ s25 := by
          intro h1
          apply hi
          have h2 := congrArg partner h1
          rwa [partner_involutive, hps25] at h2
        exact pi1_vanish_eRc y (partner i)
          (fun hmem => hne (Finset.mem_singleton.mp hmem))
    rw [hcol]
    by_cases hj : s9 = j'
    · rw [if_pos hj]
      by_cases hi : i' = s9
      · rw [if_pos hi, if_pos ⟨hi.symm, hj⟩]
      · rw [if_neg hi,
          if_neg (fun h : s9 = i' ∧ s9 = j' => hi h.1.symm),
          zero_mul]
    · rw [if_neg hj, if_neg (fun h : s9 = i' ∧ s9 = j' => hj h.2)]
  have hXY : Matrix.single s9 s9 (a.u1 - star a.u1)
        * Matrix.single s25 s25 (b.u1 - star b.u1) = 0 := by
    rw [single_mul_single, if_neg (by decide : ¬ s9 = s25)]
  have hYX : Matrix.single s25 s25 (b.u1 - star b.u1)
        * Matrix.single s9 s9 (a.u1 - star a.u1) = 0 := by
    rw [single_mul_single, if_neg (by decide : ¬ s25 = s9)]
  have e1 : piFlip a * Matrix.single s25 s25 (b.u1 - star b.u1)
      = Matrix.single s25 s25 (b.u1 - star b.u1) * piFlip a := by
    rw [hmul_single25, hsingle25_mul, mul_comm]
  have e2 : Matrix.single s9 s9 (a.u1 - star a.u1) * rhoFlip b
      = rhoFlip b * Matrix.single s9 s9 (a.u1 - star a.u1) := by
    rw [hsingle9_mul, hmul_single9, mul_comm]
  rw [piDouble_eq_piFlip_add, rhoDouble_eq_step, add_mul, add_mul,
    mul_add, mul_add, mul_add, mul_add, piFlip_order_zero, hXY,
    hYX, e1, e2]
  abel

/-- **The double-flip determinant is π₁'s exactly**: the
seat-8 factor `star λ` and the seat-9 factor `λ` are π₁'s
seat-9 and seat-8 factors swapped, so the diagonal product
is unchanged and
`det (piDouble (u1ParamGen α β t)) = exp ((-4α - 12β) · t · i)`. -/
theorem piDouble_det_gen (α β : ℤ) (t : ℝ) :
    (piDouble (u1ParamGen α β t)).det
      = Complex.exp (((-4 * α + -12 * β : ℤ) : ℂ)
          * ((t : ℂ) * Complex.I)) := by
  have hU : u1ParamGen α β t
      = ⟨Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)), 1,
        Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))
          • (1 : Matrix I3 I3 ℂ)⟩ := rfl
  have hd8 : pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
        (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) s8
      = Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)) :=
    pi1DiagVal_nuR _ _
  have hd9 : pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
        (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) s9
      = star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))) :=
    pi1DiagVal_eR _ _
  have hu : (⟨Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)), 1,
        Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))
          • (1 : Matrix I3 I3 ℂ)⟩ : AF).u1
      = Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)) := rfl
  have hdiag : piDouble (u1ParamGen α β t)
      = Matrix.diagonal
          (Function.update
            (Function.update
              (pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
                (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))))
              s8 (star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))))
            s9 (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))) := by
    rw [hU, ThetLogos.DialOneDoubleFlipPin.piDouble_unfold,
      pi1_eq_diagonal, diagonal_add_single_diag,
      diagonal_add_single_diag]
    congr 1
    funext i
    by_cases hi9 : i = s9
    · subst hi9
      simp only [Function.update_self,
        Function.update_of_ne (show s9 ≠ s8 by decide), hd9, hu]
      ring
    · by_cases hi8 : i = s8
      · subst hi8
        simp only [Function.update_of_ne (show s8 ≠ s9 by decide),
          Function.update_self, hd8, hu]
        ring
      · simp only [Function.update_of_ne hi9,
          Function.update_of_ne hi8]
  have hpt : ∀ i : Fin 32,
      Function.update
          (Function.update
            (pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
              (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))))
            s8 (star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))))
          s9 (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))) i
        = pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
            (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I)))
            (Equiv.swap s8 s9 i) := by
    intro i
    by_cases hi8 : i = s8
    · subst hi8
      rw [Function.update_of_ne (by decide : s8 ≠ s9),
        Function.update_self, Equiv.swap_apply_left, hd9]
    · by_cases hi9 : i = s9
      · subst hi9
        rw [Function.update_self, Equiv.swap_apply_right, hd8]
      · rw [Function.update_of_ne hi9, Function.update_of_ne hi8,
          Equiv.swap_apply_of_ne_of_ne hi8 hi9]
  have hprod : ∏ i : Fin 32,
        Function.update
          (Function.update
            (pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
              (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))))
            s8 (star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))))
          s9 (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))) i
      = ∏ i : Fin 32,
          pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
            (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i :=
    Fintype.prod_equiv (Equiv.swap s8 s9) _ _ hpt
  calc (piDouble (u1ParamGen α β t)).det
      = ∏ i : Fin 32,
          Function.update
            (Function.update
              (pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
                (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))))
              s8 (star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))))
            s9 (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))) i := by
        rw [hdiag, Matrix.det_diagonal]
    _ = ∏ i : Fin 32,
          pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
            (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i := hprod
    _ = (pi1 (u1ParamGen α β t)).det := by
        rw [hU, pi1_eq_diagonal, Matrix.det_diagonal]
    _ = Complex.exp (((-4 * α + -12 * β : ℤ) : ℂ)
          * ((t : ℂ) * Complex.I)) := pi1_det_gen α β t

/-- **Clause first-order for `piDouble`**, transported from
`piFlip_first_order` over the `(1 ↔ 9)` Dirac pairing:
`md s9 = s1`, `md s1 = s9`, `Dval s9 = Dval s1` (both `Ye`),
and the ρ-diagonals at seats 1 and 9 are both `star b.u1`, so
the seat-9 correction `single s1 s9 + single s9 s1` commutes
with `rho1`, hence with `rhoFlip` (seat-24 single disjoint),
and with the seat-25 single of `rhoDouble` (disjoint
indices); `[DF, piFlip a]` commutes with the seat-25 single
because its row/column 25 vanish (transported from the
landed row/column-24 vanishing via seats 17/25). -/
theorem piDouble_first_order (Ynu Ye Yu Yd : ℝ) (a b : AF)
    (i j : Fin 32) :
    ((DF_oneGen Ynu Ye Yu Yd * piDouble a
        - piDouble a * DF_oneGen Ynu Ye Yu Yd) * piOp (piDouble b)
      - piOp (piDouble b) * (DF_oneGen Ynu Ye Yu Yd * piDouble a
        - piDouble a * DF_oneGen Ynu Ye Yu Yd)) i j = 0 := by
  have hps9 : partner s9 = s25 := by
    apply Fin.ext
    simp [partner_val_eq]
  have hps25 : partner s25 = s9 := by
    apply Fin.ext
    simp [partner_val_eq]
  have hps1 : partner s1 = s17 := by
    apply Fin.ext
    simp [partner_val_eq]
  have hps17 : partner s17 = s1 := by
    apply Fin.ext
    simp [partner_val_eq]
  have hmd1 : md s1 = s9 := by
    ext
    simp [md_val]
  have hmd9 : md s9 = s1 := by
    ext
    simp [md_val]
  have hmd17 : md s17 = s25 := by
    ext
    simp [md_val]
  have hmd25 : md s25 = s17 := by
    ext
    simp [md_val]
  have hDval9 : Dval Ynu Ye Yu Yd s9 = Dval Ynu Ye Yu Yd s1 := by
    have h : Dval Ynu Ye Yu Yd s9
        = Y8 Ynu Ye Yu Yd ⟨1, by omega⟩ :=
      Dval_apply Ynu Ye Yu Yd 9 1 (by omega) (by omega)
    have h1 : Dval Ynu Ye Yu Yd s1
        = Y8 Ynu Ye Yu Yd ⟨1, by omega⟩ :=
      Dval_apply Ynu Ye Yu Yd 1 1 (by omega) (by omega)
    rw [h, h1]
  have hflip9 : piFlip a s9 s9 = star a.u1 := by
    rw [piFlip_apply,
      if_neg (fun hh : s9 = s8 ∧ s9 = s8 => absurd hh.1 (by decide)),
      pi1_entry_eR]
  have hrho1row9 : ∀ j : Fin 32,
      rho1 b s9 j = if j = s9 then star b.u1 else 0 := by
    intro j
    by_cases hj : j = s9
    · rw [if_pos hj, hj]
      exact rho1_entry_eR b
    · rw [if_neg hj, rho1_entry, hps9]
      have hne : partner j ≠ s25 := by
        intro h1
        apply hj
        have h2 := congrArg partner h1
        rwa [partner_involutive, hps25] at h2
      exact pi1_vanish_col_eRc b (partner j)
        (fun hmem => hne (Finset.mem_singleton.mp hmem))
  have hrho1col9 : ∀ x : Fin 32,
      rho1 b x s9 = if x = s9 then star b.u1 else 0 := by
    intro x
    by_cases hx : x = s9
    · rw [if_pos hx, hx]
      exact rho1_entry_eR b
    · rw [if_neg hx, rho1_entry, hps9]
      have hne : partner x ≠ s25 := by
        intro h1
        apply hx
        have h2 := congrArg partner h1
        rwa [partner_involutive, hps25] at h2
      exact pi1_vanish_eRc b (partner x)
        (fun hmem => hne (Finset.mem_singleton.mp hmem))
  have hcol17 : ∀ k : Fin 32, k ≠ s17 → pi1 b k s17 = 0 := by
    intro k hk
    by_cases hk16 : k = ⟨16, by omega⟩
    · subst hk16
      have h := pi1_entry_leptonLc b ⟨0, by omega⟩ ⟨1, by omega⟩
      rwa [if_neg (by decide : (⟨0, by omega⟩ : Fin 2)
        ≠ ⟨1, by omega⟩)] at h
    · exact pi1_vanish_col_leptonLc b ⟨1, by omega⟩ k
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hk16, hk⟩)
  have hrow17 : ∀ k : Fin 32, k ≠ s17 → pi1 b s17 k = 0 := by
    intro k hk
    by_cases hk16 : k = ⟨16, by omega⟩
    · subst hk16
      have h := pi1_entry_leptonLc b ⟨1, by omega⟩ ⟨0, by omega⟩
      rwa [if_neg (by decide : (⟨1, by omega⟩ : Fin 2)
        ≠ ⟨0, by omega⟩)] at h
    · exact pi1_vanish_leptonLc b ⟨1, by omega⟩ k
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hk16, hk⟩)
  have hrho1row1 : ∀ j : Fin 32,
      rho1 b s1 j = if j = s1 then star b.u1 else 0 := by
    intro j
    by_cases hj : j = s1
    · rw [if_pos hj, hj, rho1_entry, hps1]
      have h := pi1_entry_leptonLc b ⟨1, by omega⟩ ⟨1, by omega⟩
      rwa [if_pos rfl] at h
    · rw [if_neg hj, rho1_entry, hps1]
      exact hcol17 (partner j) (by
        intro h1
        apply hj
        have h2 := congrArg partner h1
        rwa [partner_involutive, hps17] at h2)
  have hrho1col1 : ∀ x : Fin 32,
      rho1 b x s1 = if x = s1 then star b.u1 else 0 := by
    intro x
    by_cases hx : x = s1
    · rw [if_pos hx, hx, rho1_entry, hps1]
      have h := pi1_entry_leptonLc b ⟨1, by omega⟩ ⟨1, by omega⟩
      rwa [if_pos rfl] at h
    · rw [if_neg hx, rho1_entry, hps1]
      exact hrow17 (partner x) (by
        intro h1
        apply hx
        have h2 := congrArg partner h1
        rwa [partner_involutive, hps17] at h2)
  have hsingle19 : ∀ c : ℂ,
      Matrix.single s1 s9 c * rho1 b
        = rho1 b * Matrix.single s1 s9 c := by
    intro c
    ext i' j'
    rw [single_mul_apply, mul_single_apply, hrho1row9, hrho1col1]
    by_cases hi : s1 = i'
    · by_cases hj : s9 = j'
      · rw [if_pos hi, if_pos hj.symm, if_pos hj, if_pos hi.symm,
          mul_comm]
      · rw [if_pos hi,
          if_neg (fun h : j' = s9 => hj h.symm), if_neg hj,
          mul_zero]
    · by_cases hj : s9 = j'
      · rw [if_neg hi, if_pos hj,
          if_neg (fun h : i' = s1 => hi h.symm), zero_mul]
      · rw [if_neg hi, if_neg hj]
  have hsingle91 : ∀ c : ℂ,
      Matrix.single s9 s1 c * rho1 b
        = rho1 b * Matrix.single s9 s1 c := by
    intro c
    ext i' j'
    rw [single_mul_apply, mul_single_apply, hrho1row1, hrho1col9]
    by_cases hi : s9 = i'
    · by_cases hj : s1 = j'
      · rw [if_pos hi, if_pos hj.symm, if_pos hj, if_pos hi.symm,
          mul_comm]
      · rw [if_pos hi,
          if_neg (fun h : j' = s1 => hj h.symm), if_neg hj,
          mul_zero]
    · by_cases hj : s1 = j'
      · rw [if_neg hi, if_pos hj,
          if_neg (fun h : i' = s9 => hi h.symm), zero_mul]
      · rw [if_neg hi, if_neg hj]
  have hsingle19F : ∀ c : ℂ,
      Matrix.single s1 s9 c * rhoFlip b
        = rhoFlip b * Matrix.single s1 s9 c := by
    intro c
    have hd1 : Matrix.single s1 s9 c
          * Matrix.single s24 s24 (star b.u1 - b.u1) = 0 := by
      rw [single_mul_single, if_neg (by decide : ¬ s9 = s24)]
    have hd2 : Matrix.single s24 s24 (star b.u1 - b.u1)
          * Matrix.single s1 s9 c = 0 := by
      rw [single_mul_single, if_neg (by decide : ¬ s24 = s1)]
    rw [rhoFlip_eq]
    simp only [add_mul, mul_add, hsingle19, hd1, hd2, add_zero]
  have hsingle91F : ∀ c : ℂ,
      Matrix.single s9 s1 c * rhoFlip b
        = rhoFlip b * Matrix.single s9 s1 c := by
    intro c
    have hd1 : Matrix.single s9 s1 c
          * Matrix.single s24 s24 (star b.u1 - b.u1) = 0 := by
      rw [single_mul_single, if_neg (by decide : ¬ s1 = s24)]
    have hd2 : Matrix.single s24 s24 (star b.u1 - b.u1)
          * Matrix.single s9 s1 c = 0 := by
      rw [single_mul_single, if_neg (by decide : ¬ s24 = s9)]
    rw [rhoFlip_eq]
    simp only [add_mul, mul_add, hsingle91, hd1, hd2, add_zero]
  have hpi1col25 : ∀ x : Fin 32,
      pi1 a x s25 = if x = s25 then star a.u1 else 0 := by
    intro x
    by_cases hx : x = s25
    · rw [if_pos hx, hx, pi1_entry_eRc]
    · rw [if_neg hx]
      exact pi1_vanish_col_eRc a x
        (fun h => absurd (Finset.mem_singleton.mp h) hx)
  have hpi1row25 : ∀ x : Fin 32,
      pi1 a s25 x = if x = s25 then star a.u1 else 0 := by
    intro x
    by_cases hx : x = s25
    · rw [if_pos hx, hx, pi1_entry_eRc]
    · rw [if_neg hx]
      exact pi1_vanish_eRc a x
        (fun h => absurd (Finset.mem_singleton.mp h) hx)
  have hcommCol25 : ∀ x : Fin 32,
      (DF_oneGen Ynu Ye Yu Yd * pi1 a
        - pi1 a * DF_oneGen Ynu Ye Yu Yd) x s25 = 0 := by
    intro x
    rw [comm_entry, hpi1col25, hmd25]
    by_cases hx : x = s17
    · subst hx
      have h := pi1_entry_leptonLc a ⟨1, by omega⟩ ⟨1, by omega⟩
      rw [if_pos rfl] at h
      have h2 : pi1 a s17 s17 = star a.u1 := h
      rw [hmd17, if_pos rfl, h2]
      exact sub_eq_zero.mpr (mul_comm _ _)
    · by_cases hx16 : x = ⟨16, by omega⟩
      · subst hx16
        have hmdi : md (⟨16, by omega⟩ : Fin 32) ≠ s25 := by
          intro hcon
          have h2 := congrArg md hcon
          rw [md_involutive, hmd25] at h2
          exact absurd h2 (by decide)
        have hpi : pi1 a (⟨16, by omega⟩ : Fin 32) s17 = 0 := by
          have h := pi1_entry_leptonLc a ⟨0, by omega⟩
            ⟨1, by omega⟩
          rwa [if_neg (by decide : (⟨0, by omega⟩ : Fin 2)
            ≠ ⟨1, by omega⟩)] at h
        rw [if_neg hmdi, hpi, mul_zero, zero_mul, sub_zero]
      · have hmdi : md x ≠ s25 := by
          intro hcon
          have h2 := congrArg md hcon
          rw [md_involutive, hmd25] at h2
          exact hx h2
        have hpi : pi1 a x s17 = 0 :=
          pi1_vanish_col_leptonLc a ⟨1, by omega⟩ x
            (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hx16, hx⟩)
        rw [if_neg hmdi, hpi, mul_zero, zero_mul, sub_zero]
  have hcommRow25 : ∀ x : Fin 32,
      (DF_oneGen Ynu Ye Yu Yd * pi1 a
        - pi1 a * DF_oneGen Ynu Ye Yu Yd) s25 x = 0 := by
    intro x
    rw [comm_entry, hmd25, hpi1row25]
    by_cases hx : x = s17
    · subst hx
      have h := pi1_entry_leptonLc a ⟨1, by omega⟩ ⟨1, by omega⟩
      rw [if_pos rfl] at h
      have h2 : pi1 a s17 s17 = star a.u1 := h
      rw [hmd17, if_pos rfl, h2]
      exact sub_eq_zero.mpr (mul_comm _ _)
    · by_cases hx16 : x = ⟨16, by omega⟩
      · subst hx16
        have h1 : pi1 a s17 (⟨16, by omega⟩ : Fin 32) = 0 := by
          have h := pi1_entry_leptonLc a ⟨1, by omega⟩
            ⟨0, by omega⟩
          rwa [if_neg (by decide : (⟨1, by omega⟩ : Fin 2)
            ≠ ⟨0, by omega⟩)] at h
        have hmd16 : md (⟨16, by omega⟩ : Fin 32) ≠ s25 := by
          decide
        rw [h1, if_neg hmd16, mul_zero, zero_mul, sub_zero]
      · have h1 : pi1 a s17 x = 0 :=
          pi1_vanish_leptonLc a ⟨1, by omega⟩ x
            (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hx16, hx⟩)
        have hmdx : md x ≠ s25 := by
          intro hcon
          have h2 := congrArg md hcon
          rw [md_involutive, hmd25] at h2
          exact hx h2
        rw [h1, if_neg hmdx, mul_zero, zero_mul, sub_zero]
  have hcommFlipCol25 : ∀ x : Fin 32,
      (DF_oneGen Ynu Ye Yu Yd * piFlip a
        - piFlip a * DF_oneGen Ynu Ye Yu Yd) x s25 = 0 := by
    intro x
    rw [piFlip_comm_entry, hcommCol25,
      if_neg (fun h : x = s0 ∧ s25 = s8 => absurd h.2 (by decide)),
      if_neg (fun h : x = s8 ∧ s25 = s0 => absurd h.2 (by decide)),
      add_zero]
  have hcommFlipRow25 : ∀ x : Fin 32,
      (DF_oneGen Ynu Ye Yu Yd * piFlip a
        - piFlip a * DF_oneGen Ynu Ye Yu Yd) s25 x = 0 := by
    intro x
    rw [piFlip_comm_entry, hcommRow25,
      if_neg (fun h : s25 = s0 ∧ x = s8 => absurd h.1 (by decide)),
      if_neg (fun h : s25 = s8 ∧ x = s0 => absurd h.1 (by decide)),
      add_zero]
  have hcommFlipS25 :
      (DF_oneGen Ynu Ye Yu Yd * piFlip a
          - piFlip a * DF_oneGen Ynu Ye Yu Yd)
        * Matrix.single s25 s25 (b.u1 - star b.u1)
      = Matrix.single s25 s25 (b.u1 - star b.u1)
        * (DF_oneGen Ynu Ye Yu Yd * piFlip a
          - piFlip a * DF_oneGen Ynu Ye Yu Yd) := by
    ext i' j'
    rw [mul_single_apply, single_mul_apply]
    by_cases hj : s25 = j'
    · by_cases hi : s25 = i'
      · rw [if_pos hj, if_pos hi, hcommFlipCol25, hcommFlipRow25,
          zero_mul, mul_zero]
      · rw [if_pos hj, if_neg hi, hcommFlipCol25, zero_mul]
    · by_cases hi : s25 = i'
      · rw [if_neg hj, if_pos hi, hcommFlipRow25, mul_zero]
      · rw [if_neg hj, if_neg hi]
  have hz1 : Matrix.single s1 s9
        (Dval Ynu Ye Yu Yd s1 * (a.u1 - star a.u1))
        * Matrix.single s25 s25 (b.u1 - star b.u1) = 0 := by
    rw [single_mul_single, if_neg (by decide : ¬ s9 = s25)]
  have hz2 : Matrix.single s9 s1
        (-(Dval Ynu Ye Yu Yd s1 * (a.u1 - star a.u1)))
        * Matrix.single s25 s25 (b.u1 - star b.u1) = 0 := by
    rw [single_mul_single, if_neg (by decide : ¬ s1 = s25)]
  have hz3 : Matrix.single s25 s25 (b.u1 - star b.u1)
        * Matrix.single s1 s9
          (Dval Ynu Ye Yu Yd s1 * (a.u1 - star a.u1)) = 0 := by
    rw [single_mul_single, if_neg (by decide : ¬ s25 = s1)]
  have hz4 : Matrix.single s25 s25 (b.u1 - star b.u1)
        * Matrix.single s9 s1
          (-(Dval Ynu Ye Yu Yd s1 * (a.u1 - star a.u1))) = 0 := by
    rw [single_mul_single, if_neg (by decide : ¬ s25 = s9)]
  have hDFDouble : ∀ x y : Fin 32,
      (DF_oneGen Ynu Ye Yu Yd * piDouble a) x y
        = Dval Ynu Ye Yu Yd x * piDouble a (md x) y := by
    intro x y
    rw [Matrix.mul_apply, Finset.sum_eq_single (md x)]
    · rw [DF_oneGen_entry, if_pos rfl]
    · intro k _ hk
      rw [DF_oneGen_entry, if_neg hk, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ (md x)) hcon
  have hDoubleDF : ∀ x y : Fin 32,
      (piDouble a * DF_oneGen Ynu Ye Yu Yd) x y
        = piDouble a x (md y) * Dval Ynu Ye Yu Yd (md y) := by
    intro x y
    rw [Matrix.mul_apply, Finset.sum_eq_single (md y)]
    · rw [DF_oneGen_entry, md_involutive, if_pos rfl]
    · intro k _ hk
      rw [DF_oneGen_entry, if_neg, mul_zero]
      intro hjk
      apply hk
      have hkj : md y = k := by
        rw [show md y = md (md k) from congrArg md hjk]
        exact md_involutive k
      exact hkj.symm
    · intro hcon
      exact absurd (Finset.mem_univ (md y)) hcon
  have hstepApply : ∀ x y : Fin 32,
      piDouble a x y
        = if x = s9 ∧ y = s9 then a.u1 else piFlip a x y := by
    intro x y
    rw [piDouble_eq_piFlip_add, Matrix.add_apply,
      Matrix.single_apply]
    by_cases h : x = s9 ∧ y = s9
    · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
      obtain ⟨rfl, rfl⟩ := h
      rw [hflip9]
      ring
    · rw [if_neg h,
        if_neg (fun hh : s9 = x ∧ s9 = y =>
          h ⟨hh.1.symm, hh.2.symm⟩), add_zero]
  have hcommStep : ∀ x y : Fin 32,
      (DF_oneGen Ynu Ye Yu Yd * piDouble a
          - piDouble a * DF_oneGen Ynu Ye Yu Yd) x y
        = (DF_oneGen Ynu Ye Yu Yd * piFlip a
            - piFlip a * DF_oneGen Ynu Ye Yu Yd) x y
          + (if x = s1 ∧ y = s9
              then Dval Ynu Ye Yu Yd s1 * (a.u1 - star a.u1)
              else if x = s9 ∧ y = s1
                then -(Dval Ynu Ye Yu Yd s1 * (a.u1 - star a.u1))
                else 0) := by
    intro x y
    rw [Matrix.sub_apply, Matrix.sub_apply, hDFDouble, hDoubleDF,
      DF_mul_piFlip_entry, piFlip_mul_DF_entry, hstepApply,
      hstepApply]
    by_cases hA : md x = s9 ∧ y = s9
    · have hx : x = s1 := by
        have h2 := congrArg md hA.1
        rwa [md_involutive, hmd9] at h2
      have hB : ¬ (x = s9 ∧ md y = s9) := by
        rintro ⟨h1, -⟩
        rw [hx] at h1
        exact absurd h1 (by decide)
      rw [if_pos hA, if_neg hB, if_pos ⟨hx, hA.2⟩, hx, hA.2, hmd1,
        hflip9]
      ring
    · by_cases hB : x = s9 ∧ md y = s9
      · have hy : y = s1 := by
          have h2 := congrArg md hB.2
          rwa [md_involutive, hmd9] at h2
        have hA' : ¬ (x = s1 ∧ y = s9) := by
          rintro ⟨h1, -⟩
          exact absurd (h1.symm.trans hB.1) (by decide)
        rw [if_neg hA, if_pos hB, if_neg hA', if_pos ⟨hB.1, hy⟩,
          hy, hB.1, hmd1, hflip9, hDval9]
        ring
      · have hA' : ¬ (x = s1 ∧ y = s9) := by
          rintro ⟨h1, h2⟩
          exact hA ⟨by rw [h1, hmd1], h2⟩
        have hB' : ¬ (x = s9 ∧ y = s1) := by
          rintro ⟨h1, h2⟩
          exact hB ⟨h1, by rw [h2, hmd1]⟩
        rw [if_neg hA, if_neg hB, if_neg hA', if_neg hB', add_zero]
  have hM : DF_oneGen Ynu Ye Yu Yd * piDouble a
        - piDouble a * DF_oneGen Ynu Ye Yu Yd
      = (DF_oneGen Ynu Ye Yu Yd * piFlip a
          - piFlip a * DF_oneGen Ynu Ye Yu Yd)
        + (Matrix.single s1 s9
              (Dval Ynu Ye Yu Yd s1 * (a.u1 - star a.u1))
            + Matrix.single s9 s1
              (-(Dval Ynu Ye Yu Yd s1 * (a.u1 - star a.u1)))) := by
    ext x y
    rw [hcommStep, Matrix.add_apply, Matrix.add_apply,
      Matrix.single_apply, Matrix.single_apply]
    by_cases h1 : x = s1 ∧ y = s9
    · rw [if_pos h1, if_pos ⟨h1.1.symm, h1.2.symm⟩,
        if_neg (fun h : s9 = x ∧ s1 = y => by
          rw [h1.1] at h
          exact absurd h.1 (by decide)),
        add_zero]
    · by_cases h2 : x = s9 ∧ y = s1
      · rw [if_neg h1, if_pos h2,
          if_neg (fun h : s1 = x ∧ s9 = y =>
            h1 ⟨h.1.symm, h.2.symm⟩),
          if_pos ⟨h2.1.symm, h2.2.symm⟩, zero_add]
      · rw [if_neg h1, if_neg h2,
          if_neg (fun h : s1 = x ∧ s9 = y =>
            h1 ⟨h.1.symm, h.2.symm⟩),
          if_neg (fun h : s9 = x ∧ s1 = y =>
            h2 ⟨h.1.symm, h.2.symm⟩)]
        simp
  have hD : (DF_oneGen Ynu Ye Yu Yd * piFlip a
        - piFlip a * DF_oneGen Ynu Ye Yu Yd) * rhoFlip b
      = rhoFlip b * (DF_oneGen Ynu Ye Yu Yd * piFlip a
        - piFlip a * DF_oneGen Ynu Ye Yu Yd) := by
    ext x y
    have h := piFlip_first_order Ynu Ye Yu Yd a b x y
    rwa [Matrix.sub_apply, sub_eq_zero] at h
  have hTot : (DF_oneGen Ynu Ye Yu Yd * piDouble a
        - piDouble a * DF_oneGen Ynu Ye Yu Yd) * piOp (piDouble b)
      = piOp (piDouble b) * (DF_oneGen Ynu Ye Yu Yd * piDouble a
        - piDouble a * DF_oneGen Ynu Ye Yu Yd) := by
    rw [hM, rhoDouble_eq_step]
    simp only [add_mul, mul_add]
    rw [hD, hcommFlipS25, hsingle19F, hsingle91F, hz1, hz2, hz3,
      hz4]
    abel
  rw [Matrix.sub_apply, hTot, sub_self]

/-- **Confirmation (ii) — `BasePiDoubleCheck` HOLDS**:
`DialOneBase piDouble`, assembled clause by clause from the
transports above, with the primitive unimodular direction
`(3, -1)` — π₁'s own, since the determinant is π₁'s exactly
(`piDouble_det_gen`). K-CMP-1 does NOT fire at any clause. -/
theorem dialOneBase_piDouble : BasePiDoubleCheck :=
  ⟨piDouble_afMul,
   piDouble_afAdd,
   piDouble_afStar,
   piDouble_one,
   piDouble_zero,
   piDouble_injective,
   piDouble_grading_even,
   fun a b => piDouble_order_zero a b,
   fun Ynu Ye Yu Yd a b i j =>
     piDouble_first_order Ynu Ye Yu Yd a b i j,
   ⟨3, -1, by norm_num, fun t => by
     rw [piDouble_det_gen]
     norm_num⟩⟩

/-! ## Confirmation (iii): non-proportionality at ν_R -/

/-- **The double-flipped ν_R lifted entry**: along the
one-parameter family, the lifted eigenvalue at the ν_R seat
is `star λ * star λ` — seat 8 is flipped, and its J-partner
seat 24 is untouched by the seat-25 single of `rhoDouble`,
so the value is piFlip's shape with piDouble's own `λ`. -/
theorem piDouble_lifted_nuR (α β : ℤ) (t : ℝ) :
    (piDouble (u1ParamGen α β t)
        * piOp (piDouble (u1ParamGen α β t))) s8 s8
      = star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
        * star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))) := by
  have hu : (u1ParamGen α β t).u1
      = Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)) := rfl
  have he8 : ∀ x : AF, piDouble x s8 s8 = star x.u1 := by
    intro x
    rw [piDouble_eq_piFlip_add, Matrix.add_apply,
      Matrix.single_apply,
      if_neg (fun hh : s9 = s8 ∧ s9 = s8 =>
        absurd hh.1 (by decide)),
      piFlip_apply, if_pos ⟨rfl, rfl⟩, add_zero]
  have hrow8 : ∀ (x : AF) (k : Fin 32), k ≠ s8
      → piDouble x s8 k = 0 := by
    intro x k hk
    rw [piDouble_eq_piFlip_add, Matrix.add_apply,
      Matrix.single_apply,
      if_neg (fun hh : s9 = s8 ∧ s9 = k =>
        absurd hh.1 (by decide)),
      piFlip_apply,
      if_neg (fun hh : s8 = s8 ∧ k = s8 => hk hh.2),
      pi1_vanish_nuR x k
        (fun hmem => hk (Finset.mem_singleton.mp hmem)),
      add_zero]
  have hN : piOp (piDouble (u1ParamGen α β t)) s8 s8
      = star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))) := by
    rw [rhoDouble_eq_step, Matrix.add_apply, rhoFlip_apply,
      if_neg (fun hh : s8 = s24 ∧ s8 = s24 =>
        absurd hh.1 (by decide)),
      rho1_row_s8, if_pos rfl, Matrix.single_apply,
      if_neg (fun hh : s25 = s8 ∧ s25 = s8 =>
        absurd hh.1 (by decide)),
      add_zero, hu]
  rw [Matrix.mul_apply, Finset.sum_eq_single s8]
  · rw [he8, hN, hu]
  · intro k _ hk
    rw [hrow8 _ k hk, zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ s8) hcon

/-- **The ν_R lifted value at `(3, -1)`, `t = π / 6` is
exactly `-1`**: `λ = exp (π·i / 2) = i`, so the lifted value
is `star i * star i = (-i) * (-i) = -1` — the swapped e_R
weight `-6` along `(3, -1)` evaluated at this `t`
(`exp (-6 * (π/6) * i) = -1`), against the COMMON
HYPERCHARGE MATRIX's forced `1` at ν_R. -/
theorem piDouble_lifted_nuR_neg_one :
    (piDouble (u1ParamGen 3 (-1) (Real.pi / 6))
        * piOp (piDouble (u1ParamGen 3 (-1) (Real.pi / 6))))
        (fermionIndex SMFermion.nuR 0) (fermionIndex SMFermion.nuR 0)
      = -1 := by
  have hidx : fermionIndex SMFermion.nuR 0 = s8 := rfl
  rw [hidx, piDouble_lifted_nuR, ← star_mul, ← Complex.exp_add]
  have he : (((3 : ℤ) : ℂ) * (((Real.pi / 6 : ℝ) : ℂ) * Complex.I))
      + (((3 : ℤ) : ℂ) * (((Real.pi / 6 : ℝ) : ℂ) * Complex.I))
      = (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_pi_mul_I]
  simp

/-- **Confirmation (iii) — `NonProportionalCheck` HOLDS**:
no `κ` makes piDouble's lifted eigenvalues along `(3, -1)`
proportional to the COMMON HYPERCHARGE MATRIX — at ν_R the
matrix entry is `0`, forcing `1`, while piDouble's value at
`t = π / 6` is `-1` (`piDouble_lifted_nuR_neg_one`).
K-CMP-2 does NOT fire. -/
theorem nonProportional_piDouble : NonProportionalCheck := by
  intro hcon
  obtain ⟨κ, hκ⟩ := hcon
  have h := hκ SMFermion.nuR (Real.pi / 6)
  have hc : commonHyperchargeMatrix (fermionIndex SMFermion.nuR 0)
      (fermionIndex SMFermion.nuR 0) = 0 := by
    rw [commonHyperchargeMatrix_diag]
    norm_num [hypercharge]
  rw [hc] at h
  simp only [mul_zero, zero_mul, Complex.exp_zero] at h
  rw [piDouble_lifted_nuR_neg_one] at h
  exact absurd h (by norm_num)

/-- **K-ESC-6 FIRES AT T1.** `piDouble` satisfies the landed
base set and the C3 escape condition, and its lifted weights
along its unimodular direction `(3, -1)` are not proportional
to the COMMON HYPERCHARGE MATRIX's (the ν_R ↔ e_R swap,
`(-3, -3, 1, 1, -6, 0, 4, -2)` against the table's
`(-3, -3, 1, 1, 0, -6, 4, -2)`). **Base + C3 forcing is
FALSE in Lean, permanently.** D1-C3's landed exclusion of
piFlip stands untouched: C3 is a real condition — it is one
equation short, and now provably so. **Dial 1 = 0** (a kill
is not a dial move). -/
theorem kESC6_fires_at_T1 :
    DialOneBase piDouble ∧ C3 piDouble ∧ NonProportionalCheck :=
  ⟨dialOneBase_piDouble, c3_piDouble_holds,
   nonProportional_piDouble⟩

#print axioms c3_piDouble_holds
#print axioms dialOneBase_piDouble
#print axioms nonProportional_piDouble
#print axioms kESC6_fires_at_T1

end ThetLogos.DialOneDoubleFlipChecks
