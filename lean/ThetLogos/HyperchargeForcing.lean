import Mathlib.Tactic
import ThetLogos.Track1RouteB

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation

namespace ThetLogos.HyperchargeForcing

/-!
# ThetLogos.HyperchargeForcing — D1-A: the forcing claim, KILLED

Scoping: `whitepaper`-side memo
`routeb-general-scratch/dial1-derived-number-scoping-2026-10-27.md`
§§3–4 (brick D1-A). **Verdict: K-D1A-1 — the forcing claim is
FALSE at the landed condition set.** This module constructs the
counterexample and verifies it against every clause.

## The claim that dies

For every `π : AF → Matrix (Fin 32) (Fin 32) ℂ` satisfying the
landed condition set — unital `*`-representation laws, faithfulness,
grading-evenness, order-zero against its own `J`-opposite
`ρπ := piOp ∘ π`, first-order against the landed `DF_oneGen` with
the Yukawa data **universally quantified**, and unimodularity of
the `U(1)` lift (some primitive torus direction `(α, β)` has
`det π(u1ParamGen α β t) = 1` for all `t`) — the lifted sector
weights along the unimodular direction are proportional to
`3 • Y_f`, with `Y_f` occurring only in the conclusion.

The direction is deliberately NOT fixed to `(3, -1)` in the
hypotheses: `(3, -1)` is π₁'s own total-weight ratio, and fixing
it would smuggle the conclusion into the condition set (the
memo's K-D1A-3 vacuity trap).

## The counterexample

`piFlip`: π₁ with exactly one seat value changed — the ν_R seat
(slot 8) acts by `star a.u1` instead of `a.u1`. Every other entry
is π₁'s. It satisfies the entire condition set (proved below,
mostly by perturbation off π₁'s landed theorems), its unimodular
directions are exactly the multiples of `(-2, 1)`, and its
sector weights along `(-2, 1)` are
`(2, 2, -1, -1, 4, 4, -3, 1)` — at ν_R the weight is `4 ≠ 0`
while `3 • Y_νR = 0`. Not proportional, for any scale.

Mechanism, in one line: the first-order condition's teeth are
the *antiparticle* agreement ties (it forces the three
antiparticle ℂ seats to share one conjugation choice, and the
two antiparticle M₃ seats to share one); the *particle* seats
are not tied to anything, so a single particle-seat flip passes
every condition while moving the weight pattern off the table.

## Fences

Even the (false) claim was conditional on `(A_F; the H_F sector
decomposition)` and yielded ratios only. This kill is at the
landed condition set exactly as scoped: a strengthened condition
set is a NEW entry under the relabeling rule, argued from
scratch — nothing here pre-judges one. NO CLAIM; dials 0/4.
-/

/-- The ν_R slot. -/
abbrev s8 : Fin 32 := ⟨8, by omega⟩

/-- The ν_R antiparticle slot (partner of `s8`). -/
abbrev s24 : Fin 32 := ⟨24, by omega⟩

theorem partner_s8 : partner s8 = s24 := by
  apply Fin.ext
  simp [partner_val_eq]

theorem partner_s24 : partner s24 = s8 := by
  apply Fin.ext
  simp [partner_val_eq]

/-! ## Matrix-unit machinery (`Matrix.single`) -/

theorem single_mul_apply {i j : Fin 32} (c : ℂ)
    (M : Matrix (Fin 32) (Fin 32) ℂ) (i' j' : Fin 32) :
    (Matrix.single i j c * M) i' j'
      = if i = i' then c * M j j' else 0 := by
  rw [Matrix.mul_apply]
  by_cases hi : i = i'
  · rw [Finset.sum_eq_single j]
    · simp [Matrix.single_apply, hi]
    · intro k _ hk
      simp [Matrix.single_apply, hk.symm]
    · simp
  · rw [Finset.sum_eq_zero (fun k _ => by
      simp [Matrix.single_apply, hi] :
      ∀ k ∈ (Finset.univ : Finset (Fin 32)),
        Matrix.single i j c i' k * M k j' = 0), if_neg hi]

theorem mul_single_apply (M : Matrix (Fin 32) (Fin 32) ℂ)
    {i j : Fin 32} (c : ℂ) (i' j' : Fin 32) :
    (M * Matrix.single i j c) i' j'
      = if j = j' then M i' i * c else 0 := by
  rw [Matrix.mul_apply]
  by_cases hj : j = j'
  · rw [Finset.sum_eq_single i]
    · simp [Matrix.single_apply, hj]
    · intro k _ hk
      simp only [Matrix.single_apply,
        if_neg (fun h : i = k ∧ j = j' => hk h.1.symm), mul_zero]
    · simp
  · rw [Finset.sum_eq_zero (fun k _ => by
      simp [Matrix.single_apply, hj] :
      ∀ k ∈ (Finset.univ : Finset (Fin 32)),
        M i' k * Matrix.single i j c k j' = 0), if_neg hj]

theorem single_mul_single {i j k l : Fin 32} (c d : ℂ) :
    Matrix.single i j c * Matrix.single k l d
      = if j = k then Matrix.single i l (c * d) else 0 := by
  ext i' j'
  rw [single_mul_apply]
  by_cases hjk : j = k
  · subst hjk
    by_cases hi : i = i' <;> by_cases hl : l = j' <;>
      simp [Matrix.single_apply, hi, hl]
  · rw [if_neg hjk]
    have hkj : ¬ (k = j) := fun h => hjk h.symm
    by_cases hi : i = i'
    · rw [if_pos hi]
      simp [Matrix.single_apply, hkj]
    · rw [if_neg hi]
      simp

theorem piOp_add (M N : Matrix (Fin 32) (Fin 32) ℂ) :
    piOp (M + N) = piOp M + piOp N := by
  ext i j
  simp [piOp_apply, Matrix.add_apply]

theorem piOp_single {i j : Fin 32} (x : ℂ) :
    piOp (Matrix.single i j x)
      = Matrix.single (partner j) (partner i) x := by
  ext i' j'
  rw [piOp_apply, Matrix.single_apply, Matrix.single_apply]
  have key1 : (partner j = i') ↔ (j = partner i') := by
    constructor
    · intro h
      have h2 := congrArg partner h
      rwa [partner_involutive] at h2
    · intro h
      have h2 := congrArg partner h
      rwa [partner_involutive] at h2
  have key2 : (partner i = j') ↔ (i = partner j') := by
    constructor
    · intro h
      have h2 := congrArg partner h
      rwa [partner_involutive] at h2
    · intro h
      have h2 := congrArg partner h
      rwa [partner_involutive] at h2
  by_cases hR : partner j = i' ∧ partner i = j'
  · have hL : i = partner j' ∧ j = partner i' :=
      ⟨key2.mp hR.2, key1.mp hR.1⟩
    rw [if_pos hL, if_pos hR]
  · have hL : ¬ (i = partner j' ∧ j = partner i') :=
      fun h => hR ⟨key1.mpr h.2, key2.mpr h.1⟩
    rw [if_neg hL, if_neg hR]

/-! ## Row/column characterisations at the two ν slots -/

theorem pi1_row_s8 (a : AF) (j : Fin 32) :
    pi1 a s8 j = if j = s8 then a.u1 else 0 := by
  by_cases hj : j = s8
  · rw [if_pos hj, hj, pi1_entry_nuR]
  · rw [if_neg hj]
    exact pi1_vanish_nuR a j (fun h => by exact absurd (Finset.mem_singleton.mp h) (by assumption))

theorem pi1_col_s8 (a : AF) (i : Fin 32) :
    pi1 a i s8 = if i = s8 then a.u1 else 0 := by
  by_cases hi : i = s8
  · rw [if_pos hi, hi, pi1_entry_nuR]
  · rw [if_neg hi]
    exact pi1_vanish_col_nuR a i (fun h => by exact absurd (Finset.mem_singleton.mp h) (by assumption))

theorem pi1_row_s24 (a : AF) (j : Fin 32) :
    pi1 a s24 j = if j = s24 then star a.u1 else 0 := by
  by_cases hj : j = s24
  · rw [if_pos hj, hj, pi1_entry_nuRc]
  · rw [if_neg hj]
    exact pi1_vanish_nuRc a j (fun h => by exact absurd (Finset.mem_singleton.mp h) (by assumption))

theorem pi1_col_s24 (a : AF) (i : Fin 32) :
    pi1 a i s24 = if i = s24 then star a.u1 else 0 := by
  by_cases hi : i = s24
  · rw [if_pos hi, hi, pi1_entry_nuRc]
  · rw [if_neg hi]
    exact pi1_vanish_col_nuRc a i (fun h => by exact absurd (Finset.mem_singleton.mp h) (by assumption))

theorem rho1_row_s8 (b : AF) (j : Fin 32) :
    rho1 b s8 j = if j = s8 then star b.u1 else 0 := by
  rw [rho1_entry, partner_s8]
  by_cases hj : j = s8
  · rw [if_pos hj, hj, partner_s8, pi1_entry_nuRc]
  · rw [if_neg hj]
    apply pi1_vanish_col_nuRc
    intro h
    have h := Finset.mem_singleton.mp h
    apply hj
    have h2 := congrArg partner h
    rw [partner_involutive] at h2
    exact h2.trans partner_s24

theorem rho1_col_s8 (b : AF) (i : Fin 32) :
    rho1 b i s8 = if i = s8 then star b.u1 else 0 := by
  rw [rho1_entry, partner_s8]
  by_cases hi : i = s8
  · rw [if_pos hi, hi, partner_s8, pi1_entry_nuRc]
  · rw [if_neg hi]
    apply pi1_vanish_nuRc
    intro h
    have h := Finset.mem_singleton.mp h
    apply hi
    have h2 := congrArg partner h
    rw [partner_involutive] at h2
    exact h2.trans partner_s24

theorem rho1_row_s24 (b : AF) (j : Fin 32) :
    rho1 b s24 j = if j = s24 then b.u1 else 0 := by
  rw [rho1_entry, partner_s24]
  by_cases hj : j = s24
  · rw [if_pos hj, hj, partner_s24, pi1_entry_nuR]
  · rw [if_neg hj]
    apply pi1_vanish_col_nuR
    intro h
    have h := Finset.mem_singleton.mp h
    apply hj
    have h2 := congrArg partner h
    rw [partner_involutive] at h2
    exact h2.trans partner_s8

theorem rho1_col_s24 (b : AF) (i : Fin 32) :
    rho1 b i s24 = if i = s24 then b.u1 else 0 := by
  rw [rho1_entry, partner_s24]
  by_cases hi : i = s24
  · rw [if_pos hi, hi, partner_s24, pi1_entry_nuR]
  · rw [if_neg hi]
    apply pi1_vanish_nuR
    intro h
    have h := Finset.mem_singleton.mp h
    apply hi
    have h2 := congrArg partner h
    rw [partner_involutive] at h2
    exact h2.trans partner_s8

/-! ## Unit action lemmas -/

theorem single_s8_mul_pi1 (c : ℂ) (a : AF) :
    Matrix.single s8 s8 c * pi1 a = Matrix.single s8 s8 (c * a.u1) := by
  ext i' j'
  rw [single_mul_apply, Matrix.single_apply, pi1_row_s8]
  by_cases hi : s8 = i'
  · rw [if_pos hi]
    by_cases hj : j' = s8
    · rw [if_pos hj, if_pos ⟨hi, hj.symm⟩]
    · rw [if_neg hj, if_neg (fun h : s8 = i' ∧ s8 = j' => hj h.2.symm),
        mul_zero]
  · rw [if_neg hi, if_neg (fun h : s8 = i' ∧ s8 = j' => hi h.1)]

theorem pi1_mul_single_s8 (a : AF) (c : ℂ) :
    pi1 a * Matrix.single s8 s8 c = Matrix.single s8 s8 (a.u1 * c) := by
  ext i' j'
  rw [mul_single_apply, Matrix.single_apply, pi1_col_s8]
  by_cases hj : s8 = j'
  · rw [if_pos hj]
    by_cases hi : i' = s8
    · rw [if_pos hi, if_pos ⟨hi.symm, hj⟩]
    · rw [if_neg hi, if_neg (fun h : s8 = i' ∧ s8 = j' => hi h.1.symm),
        zero_mul]
  · rw [if_neg hj, if_neg (fun h : s8 = i' ∧ s8 = j' => hj h.2)]

theorem single_s24_mul_pi1 (c : ℂ) (a : AF) :
    Matrix.single s24 s24 c * pi1 a
      = Matrix.single s24 s24 (c * star a.u1) := by
  ext i' j'
  rw [single_mul_apply, Matrix.single_apply, pi1_row_s24]
  by_cases hi : s24 = i'
  · rw [if_pos hi]
    by_cases hj : j' = s24
    · rw [if_pos hj, if_pos ⟨hi, hj.symm⟩]
    · rw [if_neg hj, if_neg (fun h : s24 = i' ∧ s24 = j' => hj h.2.symm),
        mul_zero]
  · rw [if_neg hi, if_neg (fun h : s24 = i' ∧ s24 = j' => hi h.1)]

theorem pi1_mul_single_s24 (a : AF) (c : ℂ) :
    pi1 a * Matrix.single s24 s24 c
      = Matrix.single s24 s24 (star a.u1 * c) := by
  ext i' j'
  rw [mul_single_apply, Matrix.single_apply, pi1_col_s24]
  by_cases hj : s24 = j'
  · rw [if_pos hj]
    by_cases hi : i' = s24
    · rw [if_pos hi, if_pos ⟨hi.symm, hj⟩]
    · rw [if_neg hi, if_neg (fun h : s24 = i' ∧ s24 = j' => hi h.1.symm),
        zero_mul]
  · rw [if_neg hj, if_neg (fun h : s24 = i' ∧ s24 = j' => hj h.2)]

theorem single_s8_mul_rho1 (c : ℂ) (b : AF) :
    Matrix.single s8 s8 c * rho1 b = Matrix.single s8 s8 (c * star b.u1) := by
  ext i' j'
  rw [single_mul_apply, Matrix.single_apply, rho1_row_s8]
  by_cases hi : s8 = i'
  · rw [if_pos hi]
    by_cases hj : j' = s8
    · rw [if_pos hj, if_pos ⟨hi, hj.symm⟩]
    · rw [if_neg hj, if_neg (fun h : s8 = i' ∧ s8 = j' => hj h.2.symm),
        mul_zero]
  · rw [if_neg hi, if_neg (fun h : s8 = i' ∧ s8 = j' => hi h.1)]

theorem rho1_mul_single_s8 (b : AF) (c : ℂ) :
    rho1 b * Matrix.single s8 s8 c = Matrix.single s8 s8 (star b.u1 * c) := by
  ext i' j'
  rw [mul_single_apply, Matrix.single_apply, rho1_col_s8]
  by_cases hj : s8 = j'
  · rw [if_pos hj]
    by_cases hi : i' = s8
    · rw [if_pos hi, if_pos ⟨hi.symm, hj⟩]
    · rw [if_neg hi, if_neg (fun h : s8 = i' ∧ s8 = j' => hi h.1.symm),
        zero_mul]
  · rw [if_neg hj, if_neg (fun h : s8 = i' ∧ s8 = j' => hj h.2)]

theorem single_s24_mul_rho1 (c : ℂ) (b : AF) :
    Matrix.single s24 s24 c * rho1 b
      = Matrix.single s24 s24 (c * b.u1) := by
  ext i' j'
  rw [single_mul_apply, Matrix.single_apply, rho1_row_s24]
  by_cases hi : s24 = i'
  · rw [if_pos hi]
    by_cases hj : j' = s24
    · rw [if_pos hj, if_pos ⟨hi, hj.symm⟩]
    · rw [if_neg hj, if_neg (fun h : s24 = i' ∧ s24 = j' => hj h.2.symm),
        mul_zero]
  · rw [if_neg hi, if_neg (fun h : s24 = i' ∧ s24 = j' => hi h.1)]

theorem rho1_mul_single_s24 (b : AF) (c : ℂ) :
    rho1 b * Matrix.single s24 s24 c
      = Matrix.single s24 s24 (b.u1 * c) := by
  ext i' j'
  rw [mul_single_apply, Matrix.single_apply, rho1_col_s24]
  by_cases hj : s24 = j'
  · rw [if_pos hj]
    by_cases hi : i' = s24
    · rw [if_pos hi, if_pos ⟨hi.symm, hj⟩]
    · rw [if_neg hi, if_neg (fun h : s24 = i' ∧ s24 = j' => hi h.1.symm),
        zero_mul]
  · rw [if_neg hj, if_neg (fun h : s24 = i' ∧ s24 = j' => hj h.2)]

/-! ## The counterexample `piFlip` -/

/-- **The counterexample representation**: π₁ with the ν_R seat
(slot 8) acting by `star a.u1` instead of `a.u1`; every other
entry is π₁'s. -/
def piFlip (a : AF) : Matrix (Fin 32) (Fin 32) ℂ :=
  pi1 a + Matrix.single s8 s8 (star a.u1 - a.u1)

/-- The opposite of the counterexample, `piOp ∘ piFlip`. -/
def rhoFlip (b : AF) : Matrix (Fin 32) (Fin 32) ℂ := piOp (piFlip b)

theorem piFlip_apply (a : AF) (i j : Fin 32) :
    piFlip a i j
      = if i = s8 ∧ j = s8 then star a.u1 else pi1 a i j := by
  rw [piFlip, Matrix.add_apply, Matrix.single_apply]
  by_cases h : i = s8 ∧ j = s8
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
    obtain ⟨rfl, rfl⟩ := h
    rw [pi1_entry_nuR]
    ring
  · rw [if_neg h, if_neg (fun hh : s8 = i ∧ s8 = j =>
      h ⟨hh.1.symm, hh.2.symm⟩), add_zero]

theorem rhoFlip_eq (b : AF) :
    rhoFlip b = rho1 b + Matrix.single s24 s24 (star b.u1 - b.u1) := by
  unfold rhoFlip piFlip rho1
  rw [piOp_add, piOp_single, partner_s8]

theorem piFlip_afMul (a b : AF) :
    piFlip (afMul a b) = piFlip a * piFlip b := by
  have hcoef : star (afMul a b).u1 - (afMul a b).u1
      = a.u1 * (star b.u1 - b.u1)
        + ((star a.u1 - a.u1) * b.u1
          + (star a.u1 - a.u1) * (star b.u1 - b.u1)) := by
    rw [afMul_u1, star_mul]
    ring
  unfold piFlip
  rw [add_mul, mul_add, mul_add, pi1_afMul, pi1_mul_single_s8,
    single_s8_mul_pi1, single_mul_single, if_pos rfl,
    add_assoc, ← Matrix.single_add, ← Matrix.single_add, hcoef]

theorem piFlip_afAdd (a b : AF) :
    piFlip (afAdd a b) = piFlip a + piFlip b := by
  have hcoef : star (afAdd a b).u1 - (afAdd a b).u1
      = (star a.u1 - a.u1) + (star b.u1 - b.u1) := by
    rw [afAdd_u1, star_add]
    ring
  unfold piFlip
  rw [pi1_afAdd, add_add_add_comm, ← Matrix.single_add, hcoef]

theorem piFlip_single_zero (x : ℂ) (hx : x = 0) :
    Matrix.single s8 s8 x = 0 := by
  subst hx
  ext i j
  simp [Matrix.single_apply]

theorem piFlip_zero : piFlip afZero = 0 := by
  have h0 : star (afZero).u1 - (afZero).u1 = 0 := by
    rw [afZero_u1]
    simp
  unfold piFlip
  rw [piFlip_single_zero _ h0, add_zero, pi1_zero]

theorem piFlip_one : piFlip afOne = 1 := by
  have h0 : star (afOne).u1 - (afOne).u1 = 0 := by
    rw [afOne_u1]
    simp
  unfold piFlip
  rw [piFlip_single_zero _ h0, add_zero, pi1_one]

theorem piFlip_afStar (a : AF) : piFlip (afStar a) = (piFlip a)ᴴ := by
  have hcoef : star (afStar a).u1 - (afStar a).u1
      = star (star a.u1 - a.u1) := by
    rw [afStar_u1, star_sub, star_star]
  have hsingle : (Matrix.single s8 s8 (star a.u1 - a.u1))ᴴ
      = Matrix.single s8 s8 (star (star a.u1 - a.u1)) := by
    ext i j
    rw [Matrix.conjTranspose_apply, Matrix.single_apply,
      Matrix.single_apply]
    by_cases h : s8 = j ∧ s8 = i
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
    · rw [if_neg h, if_neg (fun hh : s8 = i ∧ s8 = j =>
        h ⟨hh.2, hh.1⟩), star_zero]
  unfold piFlip
  rw [Matrix.conjTranspose_add, pi1_afStar, hsingle, hcoef]

theorem piFlip_injective : Function.Injective piFlip := by
  intro a b h
  obtain ⟨ua, qa, ma⟩ := a
  obtain ⟨ub, qb, mb⟩ := b
  have hu1 : ua = ub := by
    have h9 := congrFun (congrFun h ⟨9, by omega⟩) ⟨9, by omega⟩
    rw [piFlip_apply, piFlip_apply] at h9
    have hne : ¬ ((⟨9, by omega⟩ : Fin 32) = s8
        ∧ (⟨9, by omega⟩ : Fin 32) = s8) := by
      rintro ⟨hh, -⟩
      exact absurd (Fin.ext_iff.mp hh) (by norm_num)
    rw [if_neg hne, if_neg hne, pi1_entry_eR, pi1_entry_eR] at h9
    have := congrArg star h9
    rwa [star_star, star_star] at this
  have hq : qa = qb := by
    ext s t
    have hst := congrFun (congrFun h ⟨s.val, by omega⟩) ⟨t.val, by omega⟩
    rw [piFlip_apply, piFlip_apply] at hst
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
    rw [piFlip_apply, piFlip_apply] at hkl
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

theorem piFlip_grading_even (a : AF) :
    gammaF * piFlip a = piFlip a * gammaF := by
  have hsingle : gammaF * Matrix.single s8 s8 (star a.u1 - a.u1)
      = Matrix.single s8 s8 (star a.u1 - a.u1) * gammaF := by
    ext i j
    rw [gammaF_mul_apply, mul_gammaF_apply, Matrix.single_apply]
    by_cases h : s8 = i ∧ s8 = j
    · obtain ⟨rfl, rfl⟩ : i = s8 ∧ j = s8 := ⟨h.1.symm, h.2.symm⟩
      exact mul_comm _ _
    · rw [if_neg h, mul_zero, zero_mul]
  unfold piFlip
  rw [mul_add, add_mul, pi1_grading_even, hsingle]

theorem rhoFlip_apply (b : AF) (i j : Fin 32) :
    rhoFlip b i j
      = if i = s24 ∧ j = s24 then star b.u1 else rho1 b i j := by
  rw [rhoFlip_eq, Matrix.add_apply, Matrix.single_apply]
  by_cases h : i = s24 ∧ j = s24
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
    obtain ⟨rfl, rfl⟩ := h
    rw [rho1_col_s24, if_pos rfl]
    ring
  · rw [if_neg h, if_neg (fun hh : s24 = i ∧ s24 = j =>
      h ⟨hh.1.symm, hh.2.symm⟩), add_zero]

theorem piFlip_order_zero (a b : AF) :
    piFlip a * rhoFlip b = rhoFlip b * piFlip a := by
  have hXY : Matrix.single s8 s8 (star a.u1 - a.u1)
        * Matrix.single s24 s24 (star b.u1 - b.u1) = 0 := by
    rw [single_mul_single, if_neg (by decide : ¬ s8 = s24)]
  have hYX : Matrix.single s24 s24 (star b.u1 - b.u1)
        * Matrix.single s8 s8 (star a.u1 - a.u1) = 0 := by
    rw [single_mul_single, if_neg (by decide : ¬ s24 = s8)]
  have e1 : pi1 a * Matrix.single s24 s24 (star b.u1 - b.u1)
      = Matrix.single s24 s24 (star b.u1 - b.u1) * pi1 a := by
    rw [pi1_mul_single_s24, single_s24_mul_pi1, mul_comm]
  have e2 : Matrix.single s8 s8 (star a.u1 - a.u1) * rho1 b
      = rho1 b * Matrix.single s8 s8 (star a.u1 - a.u1) := by
    rw [single_s8_mul_rho1, rho1_mul_single_s8, mul_comm]
  rw [rhoFlip_eq]
  unfold piFlip
  rw [add_mul, add_mul, mul_add, mul_add, mul_add, mul_add,
    pi1_order_zero, hXY, hYX, e1, e2]
  abel

/-! ## First-order infrastructure -/

/-- Slot `0` (the ν_L seat) as a `Fin 32` literal. -/
abbrev s0 : Fin 32 := ⟨0, by omega⟩

theorem partner_s0 : partner s0 = ⟨16, by omega⟩ := by
  ext
  simp [partner_val_eq]

theorem md_s0 : md s0 = s8 := by
  ext
  simp [md_val]

theorem md_s8 : md s8 = s0 := by
  ext
  simp [md_val]

theorem md_s24 : md s24 = ⟨16, by omega⟩ := by
  ext
  simp [md_val]

theorem md_s16 : md (⟨16, by omega⟩ : Fin 32) = s24 := by
  ext
  simp [md_val]

theorem rho1_row_zero (b : AF) (j : Fin 32) :
    rho1 b s0 j = if j = s0 then star b.u1 else 0 := by
  rw [rho1_entry, partner_s0]
  by_cases hj : j = s0
  · rw [if_pos hj, hj, partner_s0]
    have h := pi1_entry_leptonLc b (⟨0, by omega⟩ : Fin 2)
      (⟨0, by omega⟩ : Fin 2)
    rwa [if_pos rfl] at h
  · rw [if_neg hj]
    by_cases h17 : partner j = ⟨17, by omega⟩
    · rw [h17]
      have h := pi1_entry_leptonLc b (⟨1, by omega⟩ : Fin 2)
        (⟨0, by omega⟩ : Fin 2)
      rwa [if_neg (by decide : (⟨1, by omega⟩ : Fin 2)
        ≠ ⟨0, by omega⟩)] at h
    · apply pi1_vanish_col_leptonLc b (⟨0, by omega⟩ : Fin 2)
        (partner j)
      rw [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      constructor
      · intro h
        apply hj
        have h2 := congrArg partner h
        rw [partner_involutive] at h2
        have hp16 : partner ⟨16 + (⟨0, by omega⟩ : Fin 2).val,
            by omega⟩ = s0 := by
          ext
          simp [partner_val_eq]
        rwa [hp16] at h2
      · exact h17

theorem rho1_col_zero (b : AF) (i : Fin 32) :
    rho1 b i s0 = if i = s0 then star b.u1 else 0 := by
  rw [rho1_entry, partner_s0]
  by_cases hi : i = s0
  · rw [if_pos hi, hi, partner_s0]
    have h := pi1_entry_leptonLc b (⟨0, by omega⟩ : Fin 2)
      (⟨0, by omega⟩ : Fin 2)
    rwa [if_pos rfl] at h
  · rw [if_neg hi]
    by_cases h17 : partner i = ⟨17, by omega⟩
    · rw [h17]
      have h := pi1_entry_leptonLc b (⟨0, by omega⟩ : Fin 2)
        (⟨1, by omega⟩ : Fin 2)
      rwa [if_neg (by decide : (⟨0, by omega⟩ : Fin 2)
        ≠ ⟨1, by omega⟩)] at h
    · apply pi1_vanish_leptonLc b (⟨0, by omega⟩ : Fin 2)
        (partner i)
      rw [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      constructor
      · intro h
        apply hi
        have h2 := congrArg partner h
        rw [partner_involutive] at h2
        have hp16 : partner ⟨16 + (⟨0, by omega⟩ : Fin 2).val,
            by omega⟩ = s0 := by
          ext
          simp [partner_val_eq]
        rwa [hp16] at h2
      · exact h17

/-- The landed commutator `[DF, π₁ a]` has vanishing column `24`:
the only possibly nonzero entry would pair `Dval 16` against
`Dval (md 24) = Dval 16`, and `Dval` is mod-8 periodic. -/
theorem comm_col_s24 (Ynu Ye Yu Yd : ℝ) (a : AF) (i : Fin 32) :
    (DF_oneGen Ynu Ye Yu Yd * pi1 a
      - pi1 a * DF_oneGen Ynu Ye Yu Yd) i s24 = 0 := by
  rw [comm_entry, pi1_col_s24, md_s24]
  by_cases hi : i = ⟨16, by omega⟩
  · subst hi
    have h := pi1_entry_leptonLc a (⟨0, by omega⟩ : Fin 2)
      (⟨0, by omega⟩ : Fin 2)
    rw [if_pos rfl] at h
    have h2 : pi1 a (⟨16, by omega⟩ : Fin 32) (⟨16, by omega⟩ : Fin 32)
        = star a.u1 := h
    rw [md_s16, if_pos rfl, h2]
    exact sub_eq_zero.mpr (mul_comm _ _)
  · by_cases hi17 : i = ⟨17, by omega⟩
    · subst hi17
      have hmdi : md (⟨17, by omega⟩ : Fin 32) ≠ s24 := by
        intro h
        have h2 := congrArg md h
        rw [md_involutive, md_s24] at h2
        exact absurd h2 (by decide)
      have hpi : pi1 a (⟨17, by omega⟩ : Fin 32)
          ⟨16, by omega⟩ = 0 := by
        have h := pi1_entry_leptonLc a (⟨1, by omega⟩ : Fin 2)
          (⟨0, by omega⟩ : Fin 2)
        rwa [if_neg (by decide : (⟨1, by omega⟩ : Fin 2)
          ≠ ⟨0, by omega⟩)] at h
      rw [if_neg hmdi, hpi, mul_zero, zero_mul, sub_zero]
    · have hmdi : md i ≠ s24 := by
        intro h
        have h2 := congrArg md h
        rw [md_involutive, md_s24] at h2
        exact hi h2
      have hpi : pi1 a i ⟨16, by omega⟩ = 0 := by
        apply pi1_vanish_col_leptonLc a (⟨0, by omega⟩ : Fin 2) i
        rw [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨fun h => hi h, fun h => hi17 h⟩
      rw [if_neg hmdi, hpi, mul_zero, zero_mul, sub_zero]

/-- The landed commutator `[DF, π₁ a]` has vanishing row `24`. -/
theorem comm_row_s24 (Ynu Ye Yu Yd : ℝ) (a : AF) (j : Fin 32) :
    (DF_oneGen Ynu Ye Yu Yd * pi1 a
      - pi1 a * DF_oneGen Ynu Ye Yu Yd) s24 j = 0 := by
  rw [comm_entry, md_s24, pi1_row_s24]
  by_cases hj : j = ⟨16, by omega⟩
  · subst hj
    have h := pi1_entry_leptonLc a (⟨0, by omega⟩ : Fin 2)
      (⟨0, by omega⟩ : Fin 2)
    rw [if_pos rfl] at h
    have h2 : pi1 a (⟨16, by omega⟩ : Fin 32) (⟨16, by omega⟩ : Fin 32)
        = star a.u1 := h
    rw [md_s16, if_pos rfl, h2]
    exact sub_eq_zero.mpr (mul_comm _ _)
  · by_cases hj17 : j = ⟨17, by omega⟩
    · subst hj17
      have h1 : pi1 a (⟨16, by omega⟩ : Fin 32)
          (⟨17, by omega⟩ : Fin 32) = 0 := by
        have h := pi1_entry_leptonLc a (⟨0, by omega⟩ : Fin 2)
          (⟨1, by omega⟩ : Fin 2)
        rwa [if_neg (by decide : (⟨0, by omega⟩ : Fin 2)
          ≠ ⟨1, by omega⟩)] at h
      have hmd17 : md (⟨17, by omega⟩ : Fin 32) ≠ s24 := by decide
      rw [h1, if_neg hmd17, mul_zero, zero_mul, sub_zero]
    · have h1 : pi1 a (⟨16, by omega⟩ : Fin 32) j = 0 := by
        apply pi1_vanish_leptonLc a (⟨0, by omega⟩ : Fin 2) j
        rw [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨fun h => hj h, fun h => hj17 h⟩
      have hmdj : md j ≠ s24 := by
        intro h
        have h2 := congrArg md h
        rw [md_involutive, md_s24] at h2
        exact hj h2
      rw [h1, if_neg hmdj, mul_zero, zero_mul, sub_zero]

theorem DF_mul_piFlip_entry (Ynu Ye Yu Yd : ℝ) (a : AF) (i j : Fin 32) :
    (DF_oneGen Ynu Ye Yu Yd * piFlip a) i j
      = Dval Ynu Ye Yu Yd i * piFlip a (md i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (md i)]
  · rw [DF_oneGen_entry, if_pos rfl]
  · intro k _ hk
    rw [DF_oneGen_entry, if_neg hk, zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ (md i)) hcon

theorem piFlip_mul_DF_entry (Ynu Ye Yu Yd : ℝ) (a : AF) (i j : Fin 32) :
    (piFlip a * DF_oneGen Ynu Ye Yu Yd) i j
      = piFlip a i (md j) * Dval Ynu Ye Yu Yd (md j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (md j)]
  · rw [DF_oneGen_entry, md_involutive, if_pos rfl]
  · intro k _ hk
    rw [DF_oneGen_entry, if_neg, mul_zero]
    intro hjk
    apply hk
    have hkj : md j = k := by
      rw [show md j = md (md k) from congrArg md hjk]
      exact md_involutive k
    exact hkj.symm
  · intro hcon
    exact absurd (Finset.mem_univ (md j)) hcon

theorem Dval_s8 (Ynu Ye Yu Yd : ℝ) :
    Dval Ynu Ye Yu Yd s8 = Dval Ynu Ye Yu Yd s0 := by
  have h : Dval Ynu Ye Yu Yd s8
      = Y8 Ynu Ye Yu Yd ⟨0, by omega⟩ :=
    Dval_apply Ynu Ye Yu Yd 8 0 (by omega) (by omega)
  have h0 : Dval Ynu Ye Yu Yd s0
      = Y8 Ynu Ye Yu Yd ⟨0, by omega⟩ :=
    Dval_apply Ynu Ye Yu Yd 0 0 (by omega) (by omega)
  rw [h, h0]

/-- **The commutator entry identity**: `[DF, piFlip a]` differs
from `[DF, π₁ a]` only at the two entries `(0, 8)` and `(8, 0)`,
by `± Dval 0 · (star a.u1 − a.u1)`. -/
theorem piFlip_comm_entry (Ynu Ye Yu Yd : ℝ) (a : AF) (i j : Fin 32) :
    (DF_oneGen Ynu Ye Yu Yd * piFlip a
        - piFlip a * DF_oneGen Ynu Ye Yu Yd) i j
      = (DF_oneGen Ynu Ye Yu Yd * pi1 a
          - pi1 a * DF_oneGen Ynu Ye Yu Yd) i j
        + (if i = s0 ∧ j = s8
            then Dval Ynu Ye Yu Yd s0 * (star a.u1 - a.u1)
            else if i = s8 ∧ j = s0
              then -(Dval Ynu Ye Yu Yd s0 * (star a.u1 - a.u1))
              else 0) := by
  rw [comm_entry, Matrix.sub_apply, DF_mul_piFlip_entry,
    piFlip_mul_DF_entry, piFlip_apply, piFlip_apply]
  by_cases hA : md i = s8 ∧ j = s8
  · have hi : i = s0 := by
      have h2 := congrArg md hA.1
      rwa [md_involutive, md_s8] at h2
    have hB : ¬ (i = s8 ∧ md j = s8) := by
      rintro ⟨h1, -⟩
      rw [hi] at h1
      exact absurd h1 (by decide)
    rw [if_pos hA, if_neg hB, if_pos ⟨hi, hA.2⟩, hi, hA.2, md_s0,
      pi1_entry_nuR]
    ring
  · by_cases hB : i = s8 ∧ md j = s8
    · have hj : j = s0 := by
        have h2 := congrArg md hB.2
        rwa [md_involutive, md_s8] at h2
      have hA' : ¬ (i = s0 ∧ j = s8) := by
        rintro ⟨h1, -⟩
        exact absurd (h1.symm.trans hB.1) (by decide)
      rw [if_neg hA, if_pos hB, if_neg hA', if_pos ⟨hB.1, hj⟩,
        hj, hB.1, md_s0, pi1_entry_nuR, Dval_s8]
      ring
    · have hA' : ¬ (i = s0 ∧ j = s8) := by
        rintro ⟨h1, h2⟩
        exact hA ⟨by rw [h1, md_s0], h2⟩
      have hB' : ¬ (i = s8 ∧ j = s0) := by
        rintro ⟨h1, h2⟩
        exact hB ⟨h1, by rw [h2, md_s0]⟩
      rw [if_neg hA, if_neg hB, if_neg hA', if_neg hB', add_zero]

theorem single_s0_s8_comm_rho1 (c : ℂ) (b : AF) :
    Matrix.single s0 s8 c * rho1 b = rho1 b * Matrix.single s0 s8 c := by
  ext i' j'
  rw [single_mul_apply, mul_single_apply, rho1_row_s8, rho1_col_zero]
  by_cases hi : s0 = i'
  · by_cases hj : s8 = j'
    · rw [if_pos hi, if_pos hj.symm, if_pos hj, if_pos hi.symm,
        mul_comm]
    · rw [if_pos hi, if_neg (fun h : j' = s8 => hj h.symm),
        if_neg hj, mul_zero]
  · by_cases hj : s8 = j'
    · rw [if_neg hi, if_pos hj,
        if_neg (fun h : i' = s0 => hi h.symm), zero_mul]
    · rw [if_neg hi, if_neg hj]

theorem single_s8_s0_comm_rho1 (c : ℂ) (b : AF) :
    Matrix.single s8 s0 c * rho1 b = rho1 b * Matrix.single s8 s0 c := by
  ext i' j'
  rw [single_mul_apply, mul_single_apply, rho1_row_zero, rho1_col_s8]
  by_cases hi : s8 = i'
  · by_cases hj : s0 = j'
    · rw [if_pos hi, if_pos hj.symm, if_pos hj, if_pos hi.symm,
        mul_comm]
    · rw [if_pos hi, if_neg (fun h : j' = s0 => hj h.symm),
        if_neg hj, mul_zero]
  · by_cases hj : s0 = j'
    · rw [if_neg hi, if_pos hj,
        if_neg (fun h : i' = s8 => hi h.symm), zero_mul]
    · rw [if_neg hi, if_neg hj]

/-- The correction matrix commutes with `rho1 b`. -/
theorem correction_comm_rho1 (Ynu Ye Yu Yd : ℝ) (a b : AF) :
    (Matrix.single s0 s8 (Dval Ynu Ye Yu Yd s0 * (star a.u1 - a.u1))
      + Matrix.single s8 s0 (-(Dval Ynu Ye Yu Yd s0
          * (star a.u1 - a.u1)))) * rho1 b
    = rho1 b * (Matrix.single s0 s8
        (Dval Ynu Ye Yu Yd s0 * (star a.u1 - a.u1))
      + Matrix.single s8 s0 (-(Dval Ynu Ye Yu Yd s0
          * (star a.u1 - a.u1)))) := by
  rw [add_mul, mul_add, single_s0_s8_comm_rho1, single_s8_s0_comm_rho1]

/-- The correction matrix commutes with the `(24,24)` unit:
both products are zero. -/
theorem correction_comm_s24 (Ynu Ye Yu Yd : ℝ) (a b : AF) :
    (Matrix.single s0 s8 (Dval Ynu Ye Yu Yd s0 * (star a.u1 - a.u1))
      + Matrix.single s8 s0 (-(Dval Ynu Ye Yu Yd s0
          * (star a.u1 - a.u1))))
      * Matrix.single s24 s24 (star b.u1 - b.u1)
    = Matrix.single s24 s24 (star b.u1 - b.u1)
      * (Matrix.single s0 s8 (Dval Ynu Ye Yu Yd s0 * (star a.u1 - a.u1))
      + Matrix.single s8 s0 (-(Dval Ynu Ye Yu Yd s0
          * (star a.u1 - a.u1)))) := by
  rw [add_mul, mul_add,
    single_mul_single, single_mul_single, single_mul_single,
    single_mul_single,
    if_neg (by decide : ¬ s8 = s24), if_neg (by decide : ¬ s0 = s24),
    if_neg (by decide : ¬ s24 = s0), if_neg (by decide : ¬ s24 = s8),
    add_zero]

/-- The landed commutator commutes with the `(24,24)` unit:
both products are zero by the row/column vanishing. -/
theorem comm_comm_s24 (Ynu Ye Yu Yd : ℝ) (a b : AF) :
    (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
      * Matrix.single s24 s24 (star b.u1 - b.u1)
    = Matrix.single s24 s24 (star b.u1 - b.u1)
      * (DF_oneGen Ynu Ye Yu Yd * pi1 a
        - pi1 a * DF_oneGen Ynu Ye Yu Yd) := by
  ext i' j'
  rw [mul_single_apply, single_mul_apply]
  by_cases hj : s24 = j'
  · by_cases hi : s24 = i'
    · rw [if_pos hj, if_pos hi, comm_col_s24, comm_row_s24,
        zero_mul, mul_zero]
    · rw [if_pos hj, if_neg hi, comm_col_s24, zero_mul]
  · by_cases hi : s24 = i'
    · rw [if_neg hj, if_pos hi, comm_row_s24, mul_zero]
    · rw [if_neg hj, if_neg hi]

/-- **First-order condition for the counterexample** (T1): for all
real Yukawa parameters and all `a b`, the first-order commutator
against `rhoFlip` vanishes entrywise. -/
theorem piFlip_first_order (Ynu Ye Yu Yd : ℝ) (a b : AF) (i j : Fin 32) :
    ((DF_oneGen Ynu Ye Yu Yd * piFlip a
        - piFlip a * DF_oneGen Ynu Ye Yu Yd) * rhoFlip b
      - rhoFlip b * (DF_oneGen Ynu Ye Yu Yd * piFlip a
        - piFlip a * DF_oneGen Ynu Ye Yu Yd)) i j = 0 := by
  have hM : DF_oneGen Ynu Ye Yu Yd * piFlip a
        - piFlip a * DF_oneGen Ynu Ye Yu Yd
      = (DF_oneGen Ynu Ye Yu Yd * pi1 a
          - pi1 a * DF_oneGen Ynu Ye Yu Yd)
        + (Matrix.single s0 s8 (Dval Ynu Ye Yu Yd s0
              * (star a.u1 - a.u1))
            + Matrix.single s8 s0 (-(Dval Ynu Ye Yu Yd s0
              * (star a.u1 - a.u1)))) := by
    ext i' j'
    rw [piFlip_comm_entry, Matrix.add_apply, Matrix.add_apply,
      Matrix.single_apply, Matrix.single_apply]
    by_cases h1 : i' = s0 ∧ j' = s8
    · rw [if_pos h1, if_pos ⟨h1.1.symm, h1.2.symm⟩,
        if_neg (fun h : s8 = i' ∧ s0 = j' => by
          rw [h1.1] at h
          exact absurd h.1 (by decide)),
        add_zero]
    · by_cases h2 : i' = s8 ∧ j' = s0
      · rw [if_neg h1, if_pos h2,
          if_neg (fun h : s0 = i' ∧ s8 = j' =>
            h1 ⟨h.1.symm, h.2.symm⟩),
          if_pos ⟨h2.1.symm, h2.2.symm⟩, zero_add]
      · rw [if_neg h1, if_neg h2,
          if_neg (fun h : s0 = i' ∧ s8 = j' =>
            h1 ⟨h.1.symm, h.2.symm⟩),
          if_neg (fun h : s8 = i' ∧ s0 = j' =>
            h2 ⟨h.1.symm, h.2.symm⟩)]
        simp
  have hD : (DF_oneGen Ynu Ye Yu Yd * pi1 a
        - pi1 a * DF_oneGen Ynu Ye Yu Yd) * rho1 b
      = rho1 b * (DF_oneGen Ynu Ye Yu Yd * pi1 a
        - pi1 a * DF_oneGen Ynu Ye Yu Yd) := by
    ext i' j'
    have h := pi1_first_order Ynu Ye Yu Yd a b i' j'
    rwa [Matrix.sub_apply, sub_eq_zero] at h
  have hYE1 : Matrix.single s24 s24 (star b.u1 - b.u1)
        * Matrix.single s0 s8 (Dval Ynu Ye Yu Yd s0
          * (star a.u1 - a.u1)) = 0 := by
    rw [single_mul_single, if_neg (by decide : ¬ s24 = s0)]
  have hYE2 : Matrix.single s24 s24 (star b.u1 - b.u1)
        * Matrix.single s8 s0 (-(Dval Ynu Ye Yu Yd s0
          * (star a.u1 - a.u1))) = 0 := by
    rw [single_mul_single, if_neg (by decide : ¬ s24 = s8)]
  have hE1Y : Matrix.single s0 s8 (Dval Ynu Ye Yu Yd s0
        * (star a.u1 - a.u1))
        * Matrix.single s24 s24 (star b.u1 - b.u1) = 0 := by
    rw [single_mul_single, if_neg (by decide : ¬ s8 = s24)]
  have hE2Y : Matrix.single s8 s0 (-(Dval Ynu Ye Yu Yd s0
        * (star a.u1 - a.u1)))
        * Matrix.single s24 s24 (star b.u1 - b.u1) = 0 := by
    rw [single_mul_single, if_neg (by decide : ¬ s0 = s24)]
  have hTot : (DF_oneGen Ynu Ye Yu Yd * piFlip a
        - piFlip a * DF_oneGen Ynu Ye Yu Yd) * rhoFlip b
      = rhoFlip b * (DF_oneGen Ynu Ye Yu Yd * piFlip a
        - piFlip a * DF_oneGen Ynu Ye Yu Yd) := by
    rw [hM, rhoFlip_eq]
    simp only [add_mul, mul_add]
    rw [hD, comm_comm_s24, single_s0_s8_comm_rho1,
      single_s8_s0_comm_rho1, hE1Y, hE2Y, hYE1, hYE2]
    abel
  rw [Matrix.sub_apply, hTot, sub_self]

/-! ## Brick 5: determinant, unimodularity, weights -/

theorem diagonal_add_single_diag (d : Fin 32 → ℂ) (x : ℂ) (s : Fin 32) :
    Matrix.diagonal d + Matrix.single s s x
      = Matrix.diagonal (Function.update d s (d s + x)) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.diagonal_apply,
    Matrix.single_apply]
  by_cases h : i = j
  · subst h
    by_cases hs : i = s
    · subst hs
      simp
    · have hne : ¬ (s = i ∧ s = i) := fun hh => hs hh.1.symm
      rw [if_neg hne, if_pos rfl, Function.update_of_ne hs, add_zero,
        if_pos rfl]
  · have hne : ¬ (s = i ∧ s = j) := fun hh => h (hh.1.symm.trans hh.2)
    rw [if_neg h, if_neg hne, add_zero, if_neg h]

theorem prod_update_diag (d : Fin 32 → ℂ) (v : ℂ) (s : Fin 32) :
    ∏ i, Function.update d s v i
      = v * ∏ i ∈ Finset.univ \ {s}, d i := by
  rw [Finset.prod_eq_mul_prod_sdiff_singleton s
    (Function.update d s v)
    (fun h => absurd (Finset.mem_univ s) h), Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
  exact Function.update_of_ne hi.2 v d

/-- **The flipped determinant**: `det (piFlip (u1ParamGen α β t))`
picks up exactly one extra factor `exp(−2α·t·i)` against the landed
`pi1_det_gen` — the flipped ν_R seat contributes `star λ` where
π₁ contributed `λ`. -/
theorem piFlip_det_gen (α β : ℤ) (t : ℝ) :
    (piFlip (u1ParamGen α β t)).det
      = Complex.exp (((-6 * α + -12 * β : ℤ) : ℂ)
          * ((t : ℂ) * Complex.I)) := by
  have hU : u1ParamGen α β t
      = ⟨Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)), 1,
        Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))
          • (1 : Matrix I3 I3 ℂ)⟩ := rfl
  have hdet : (piFlip (u1ParamGen α β t)).det
      = Complex.exp (-((α : ℂ) * ((t : ℂ) * Complex.I)))
        * ∏ i ∈ (Finset.univ \ {s8} : Finset (Fin 32)),
          pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
            (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i := by
    rw [hU]
    unfold piFlip
    rw [pi1_eq_diagonal, diagonal_add_single_diag, Matrix.det_diagonal,
      prod_update_diag]
    congr 1
    have h8 : pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
          (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) s8
        = Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)) :=
      pi1DiagVal_nuR _ _
    rw [h8, star_exp_int]
    ring
  have hdet1 : (pi1 (u1ParamGen α β t)).det
      = Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))
        * ∏ i ∈ (Finset.univ \ {s8} : Finset (Fin 32)),
          pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
            (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i := by
    have h8 : pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
          (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) s8
        = Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)) :=
      pi1DiagVal_nuR _ _
    rw [hU, pi1_eq_diagonal, Matrix.det_diagonal,
      Finset.prod_eq_mul_prod_sdiff_singleton s8 _
        (fun h => absurd (Finset.mem_univ s8) h), h8]
  have hstar : Complex.exp (-((α : ℂ) * ((t : ℂ) * Complex.I)))
      = Complex.exp (((-2 * α : ℤ) : ℂ) * ((t : ℂ) * Complex.I))
        * Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hdet, hstar, mul_assoc, ← hdet1, pi1_det_gen,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The flipped unimodular direction**: along `(α, β) = (−2, 1)`,
`det (piFlip (u1ParamGen α β t)) = 1` for every real `t`. -/
theorem piFlip_unimodular_direction (t : ℝ) :
    (piFlip (u1ParamGen (-2) 1 t)).det = 1 := by
  rw [piFlip_det_gen]
  norm_num

/-- **The flipped ν_R lifted entry**: along the flipped
one-parameter family, the lifted eigenvalue at the ν_R seat is
`star λ · star λ` — the `star` being the whole counterexample. -/
theorem piFlip_lifted_nuR (α β : ℤ) (t : ℝ) :
    (piFlip (u1ParamGen α β t) * piOp (piFlip (u1ParamGen α β t)))
        s8 s8
      = star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
        * star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))) := by
  show (piFlip (u1ParamGen α β t) * rhoFlip (u1ParamGen α β t))
      s8 s8 = _
  rw [Matrix.mul_apply, Finset.sum_eq_single s8]
  · have hu : (u1ParamGen α β t).u1
        = Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)) := rfl
    have hM : piFlip (u1ParamGen α β t) s8 s8
        = star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))) := by
      rw [piFlip_apply, if_pos ⟨rfl, rfl⟩, hu]
    have hN : rhoFlip (u1ParamGen α β t) s8 s8
        = star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))) := by
      rw [rhoFlip_apply,
        if_neg (fun h : s8 = s24 ∧ s8 = s24 => absurd h.1 (by decide)),
        rho1_row_s8, if_pos rfl, hu]
    rw [hM, hN]
  · intro k _ hk
    have hMk : piFlip (u1ParamGen α β t) s8 k = 0 := by
      rw [piFlip_apply, if_neg (fun h : s8 = s8 ∧ k = s8 => hk h.2)]
      exact pi1_vanish_nuR _ k (fun h => hk (Finset.mem_singleton.mp h))
    rw [hMk, zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ s8) hcon

/-- **The flipped weights are not proportional to `3 · Y`**:
at `f = ν_R` (where `Y = 0`, forcing lifted eigenvalue `1`) and
`t = π / 4`, the flipped lifted eigenvalue is `−1`. -/
theorem piFlip_weights_not_proportional :
    ¬ ∃ κ : ℝ, ∀ (f : SMFermion) (t : ℝ),
      (piFlip (u1ParamGen (-2) 1 t)
          * piOp (piFlip (u1ParamGen (-2) 1 t)))
        (fermionIndex f 0) (fermionIndex f 0)
        = Complex.exp (↑(κ * 3 * (hypercharge f : ℝ) * t)
            * Complex.I) := by
  rintro ⟨κ, hκ⟩
  have h := hκ SMFermion.nuR (Real.pi / 4)
  have hidx : fermionIndex SMFermion.nuR 0 = s8 := rfl
  rw [hidx, piFlip_lifted_nuR] at h
  have hL : star (Complex.exp (((-2 : ℤ) : ℂ)
        * (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)))
      * star (Complex.exp (((-2 : ℤ) : ℂ)
        * (((Real.pi / 4 : ℝ) : ℂ) * Complex.I))) = -1 := by
    rw [← star_mul, ← Complex.exp_add]
    have he : (((-2 : ℤ) : ℂ) * (((Real.pi / 4 : ℝ) : ℂ) * Complex.I))
        + (((-2 : ℤ) : ℂ) * (((Real.pi / 4 : ℝ) : ℂ) * Complex.I))
        = -((Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [he, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  have hR : Complex.exp (↑(κ * 3 * (hypercharge SMFermion.nuR : ℝ)
      * (Real.pi / 4)) * Complex.I) = 1 := by
    have hY : hypercharge SMFermion.nuR = 0 := rfl
    rw [hY]
    simp
  rw [hL, hR] at h
  exact absurd h (by norm_num)

/-- **K-D1A-1 FIRES — the forcing statement is false at the
landed condition set.** The statement below is the registered
forcing statement verbatim in shape: every representation of
`A_F` on the landed sector decomposition satisfying the landed
condition set (representation laws in the corpus's componentwise
form, faithfulness, grading, order-zero, first-order with the
Yukawa data universally quantified, `ρπ = piOp ∘ π`, and a
primitive unimodular direction) was to have its `U(1)` weights
along every unimodular direction proportional to `3 · Y_f`.
`piFlip` satisfies every hypothesis and violates the conclusion
at the direction `(−2, 1)`, seat `ν_R`. -/
theorem dial1_forcing_killed :
    ¬ ∀ (π : AF → Matrix (Fin 32) (Fin 32) ℂ),
      (∀ a b, π (afMul a b) = π a * π b) →
      (∀ a b, π (afAdd a b) = π a + π b) →
      (∀ a, π (afStar a) = (π a)ᴴ) →
      π afOne = 1 →
      π afZero = 0 →
      Function.Injective π →
      (∀ a, gammaF * π a = π a * gammaF) →
      (∀ a b, π a * piOp (π b) = piOp (π b) * π a) →
      (∀ (Ynu Ye Yu Yd : ℝ) (a b : AF) (i j : Fin 32),
        ((DF_oneGen Ynu Ye Yu Yd * π a
            - π a * DF_oneGen Ynu Ye Yu Yd) * piOp (π b)
          - piOp (π b) * (DF_oneGen Ynu Ye Yu Yd * π a
            - π a * DF_oneGen Ynu Ye Yu Yd)) i j = 0) →
      (∃ (α β : ℤ), Nat.gcd α.natAbs β.natAbs = 1
        ∧ ∀ t, (π (u1ParamGen α β t)).det = 1) →
      ∀ (α β : ℤ), (∀ t, (π (u1ParamGen α β t)).det = 1) →
        ∃ κ : ℝ, ∀ (f : SMFermion) (t : ℝ),
          (π (u1ParamGen α β t) * piOp (π (u1ParamGen α β t)))
            (fermionIndex f 0) (fermionIndex f 0)
            = Complex.exp (↑(κ * 3 * (hypercharge f : ℝ) * t)
                * Complex.I) := by
  intro h
  have hcon := h piFlip piFlip_afMul piFlip_afAdd piFlip_afStar
    piFlip_one piFlip_zero piFlip_injective piFlip_grading_even
    piFlip_order_zero piFlip_first_order
    ⟨-2, 1, by norm_num, piFlip_unimodular_direction⟩
    (-2) 1 piFlip_unimodular_direction
  exact piFlip_weights_not_proportional hcon
