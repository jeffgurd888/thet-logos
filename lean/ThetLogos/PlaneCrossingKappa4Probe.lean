import Mathlib.Tactic

/-!
# κ₄ probe: exact dependent β⁴ coefficient at two uncovered seats

NO CLAIM.  This module is a seat computation for the β2 corridor
(𝒜 ⪰ 0 on gauge-invariant observables at general (G, ρ)); it proves
nothing about β2 itself and moves no dial.  It discharges the κ₄
probe priced in the β2-core scoping memo (2026-10-27): compute the
dependent part κ₄^dep of the β⁴ coefficient of the layer kernel at
(S1) the non-self-dual seat (C₃, faithful complex character, d = 1),
smallest even N, where only mixed pairings survive; and
(S2) (S₃, std) at N = 2, including the same-site-pair extra blocks
that the N ≥ 3 theory fences out.

Kill condition K-K4 (pre-registered): a certified negative
eigenvalue of κ₄^dep at either seat would make 𝒜 indefinite for all
small β > 0 at that seat and β2 false as posed.  Verdict of this
module: NO negative eigenvalue at either seat — the explicitly
computed blocks below are positive semidefinite, with the
certificates stated as theorems (form identities as exact sums of
squares / rank-one squares, plus character-basis evaluations).
A pass at two seats is not a general proof; it clears the way for
the general-(G, ρ) κ₄ closed-form brick.

Provenance, stated once and fenced: for seat S1 the identification
of the kernel `FC3` below with the per-plaquette factor of κ₄^dep
is proved in this module end-to-end (the ζ-weighted character-sum
argument): `FC3_eq` identifies the α-averaged plaquette monomial
with `(1/8) · reChi(h − h′)`, the holonomy class kernel.  For seat
S2 the face-block matrix `PhiS3` is SBP-1's class matrix Φ (an
exact-arithmetic T4 computation, recomputed for this probe with an
independent second reading agreeing), and the pair-block matrix
`PsiS3` is this probe's exact enumeration (T4); the assembly
justifying that the Gram matrix of κ₄^dep on the named observable
space (plaquette-reading and straight pair-loop observables, in
characters sgn and std) is block-diagonal with these blocks is the
margin argument rechecked in the probe script (the dependent part
is the cumulant over distinct-column support partitions; the pair
block's constant split is subtracted, and every margin of the
resulting blocks is exactly zero — the margins are theorems below
for the pair block).  The Lean content for S2 is exact algebra
about the computed matrices: outer-product structure, form
identities, character-basis evaluations, margins, positivity.

House fences: everything here is at finite seats; no statement in
this module is about general (G, ρ), about all β, or about the
continuum.  β2 remains open.
-/

namespace ThetLogos

open Finset

/-- Sum over `ZMod 3` evaluated at the three numerals. -/
theorem sum_zmod3 {α : Type*} [AddCommMonoid α] (f : ZMod 3 → α) :
    ∑ a, f a = f 0 + f 1 + f 2 :=
  Fin.sum_univ_three f

/-- Trichotomy on `ZMod 3`. -/
theorem zmod3_cases : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide

section C3Character

/-- A fixed primitive cube root of unity, ζ = e^{2πi/3}, as an
explicit complex number. -/
noncomputable def zetaC3 : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

theorem zetaC3_sq_add : zetaC3 ^ 2 + zetaC3 + 1 = 0 := by
  simp only [zetaC3, Complex.ext_iff, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
    pow_two, Complex.mul_re, Complex.mul_im]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  constructor <;> nlinarith [h3]

theorem zetaC3_sq : zetaC3 ^ 2 = -zetaC3 - 1 := by
  linear_combination zetaC3_sq_add

theorem zetaC3_cube : zetaC3 ^ 3 = 1 := by
  calc zetaC3 ^ 3 = zetaC3 ^ 2 * zetaC3 := by ring
    _ = (-zetaC3 - 1) * zetaC3 := by rw [zetaC3_sq]
    _ = -(zetaC3 ^ 2) - zetaC3 := by ring
    _ = -(-zetaC3 - 1) - zetaC3 := by rw [zetaC3_sq]
    _ = 1 := by ring

theorem zetaC3_ne_one : zetaC3 ≠ 1 := by
  intro h
  have h0 := zetaC3_sq_add
  rw [h] at h0
  have hre := congrArg Complex.re h0
  norm_num at hre

/-- The faithful complex character of C₃ = ZMod 3, χ(w) = ζ^{val w}. -/
noncomputable def chiC3 (w : ZMod 3) : ℂ := zetaC3 ^ w.val

theorem zetaC3_pow_mod (k : ℕ) : zetaC3 ^ (k % 3) = zetaC3 ^ k := by
  conv_rhs => rw [← Nat.div_add_mod k 3]
  rw [pow_add, pow_mul, zetaC3_cube, one_pow, one_mul]

theorem chiC3_add (a b : ZMod 3) : chiC3 (a + b) = chiC3 a * chiC3 b := by
  unfold chiC3
  rw [ZMod.val_add, ← pow_add]
  exact zetaC3_pow_mod _

theorem chiC3_zero : chiC3 0 = 1 := by simp [chiC3]

theorem chiC3_one : chiC3 1 = zetaC3 := by
  show zetaC3 ^ (1 : ZMod 3).val = zetaC3
  rw [show (1 : ZMod 3).val = 1 from rfl]; exact pow_one zetaC3

theorem chiC3_two : chiC3 2 = zetaC3 ^ 2 := by
  show zetaC3 ^ (2 : ZMod 3).val = zetaC3 ^ 2
  rw [show (2 : ZMod 3).val = 2 from rfl]

/-- Orthogonality of the faithful character against its powers:
`∑ a, χ(c·a)` is the full period sum, zero unless `c = 0`. -/
theorem chiC3_sum (c : ZMod 3) :
    ∑ a, chiC3 (c * a) = if c = 0 then 3 else 0 := by
  by_cases hc : c = 0
  · simp only [hc, ite_eq_left]
    simp [chiC3]
  · rw [ite_eq_right hc]
    rcases zmod3_cases c with h | h | h
    · exact absurd h hc
    · subst h
      rw [sum_zmod3]
      have e0 : chiC3 ((1 : ZMod 3) * 0) = 1 := by simp [chiC3]
      have e1 : chiC3 ((1 : ZMod 3) * 1) = zetaC3 := by
        show zetaC3 ^ ((1 : ZMod 3) * 1).val = zetaC3
        rw [show ((1 : ZMod 3) * 1).val = 1 from rfl]; exact pow_one zetaC3
      have e2 : chiC3 ((1 : ZMod 3) * 2) = zetaC3 ^ 2 := by
        show zetaC3 ^ ((1 : ZMod 3) * 2).val = zetaC3 ^ 2
        rw [show ((1 : ZMod 3) * 2).val = 2 from rfl]
      rw [e0, e1, e2]
      linear_combination zetaC3_sq_add
    · subst h
      rw [sum_zmod3]
      have e0 : chiC3 ((2 : ZMod 3) * 0) = 1 := by simp [chiC3]
      have e1 : chiC3 ((2 : ZMod 3) * 1) = zetaC3 ^ 2 := by
        show zetaC3 ^ ((2 : ZMod 3) * 1).val = zetaC3 ^ 2
        rw [show ((2 : ZMod 3) * 1).val = 2 from rfl]
      have e2 : chiC3 ((2 : ZMod 3) * 2) = zetaC3 := by
        show zetaC3 ^ ((2 : ZMod 3) * 2).val = zetaC3
        rw [show ((2 : ZMod 3) * 2).val = 1 from rfl]; exact pow_one zetaC3
      rw [e0, e1, e2]
      linear_combination zetaC3_sq_add

/-- `χ` of a finite sum is the product of the `χ` values. -/
theorem chiC3_sum_prod {ι : Type*} (s : Finset ι) (f : ι → ZMod 3) :
    chiC3 (∑ i ∈ s, f i) = ∏ i ∈ s, chiC3 (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [chiC3_zero]
  | insert a s has ih => rw [Finset.sum_insert has, Finset.prod_insert has, chiC3_add, ih]

/-- The real character of C₃: `reChi(w) = Re χ(w) ∈ {1, -1/2}`. -/
def reChi3 (w : ZMod 3) : ℚ := if w = 0 then 1 else -1 / 2

theorem reChi3_zero : reChi3 0 = 1 := if_pos rfl

theorem reChi3_one : reChi3 1 = -1 / 2 := if_neg (by decide)

theorem reChi3_two : reChi3 2 = -1 / 2 := if_neg (by decide)

theorem reChi3_sub (a b : ZMod 3) :
    reChi3 (a - b) = if a = b then 1 else -1 / 2 := by
  by_cases h : a = b
  · subst h; rw [sub_self, if_pos rfl]; exact reChi3_zero
  · rw [if_neg h]; exact if_neg (sub_ne_zero.mpr h)

/-- The rational real character is the average of `χ` and `χ̄`:
this is the bridge that lets the α-integral be done in ℂ. -/
theorem reChi3_cast (w : ZMod 3) :
    ((reChi3 w : ℚ) : ℂ) = (chiC3 w + chiC3 (-w)) / 2 := by
  rcases zmod3_cases w with h | h | h <;> subst h
  · have e1 : chiC3 (-(0 : ZMod 3)) = 1 := by simp [chiC3]
    rw [reChi3_zero, chiC3_zero, e1]; norm_num
  · have e1 : chiC3 (1 : ZMod 3) = zetaC3 := chiC3_one
    have e2 : chiC3 (-(1 : ZMod 3)) = zetaC3 ^ 2 := by
      show zetaC3 ^ (-(1 : ZMod 3)).val = zetaC3 ^ 2
      rw [show (-(1 : ZMod 3)).val = 2 from rfl]
    have hsum : chiC3 1 + chiC3 (-1) = -1 := by
      rw [e1, e2]; linear_combination zetaC3_sq_add
    rw [reChi3_one, hsum]; norm_num
  · have e1 : chiC3 (2 : ZMod 3) = zetaC3 ^ 2 := chiC3_two
    have e2 : chiC3 (-(2 : ZMod 3)) = zetaC3 := by
      show zetaC3 ^ (-(2 : ZMod 3)).val = zetaC3
      rw [show (-(2 : ZMod 3)).val = 1 from rfl]; exact pow_one zetaC3
    have hsum : chiC3 2 + chiC3 (-2) = -1 := by
      rw [e1, e2]; linear_combination zetaC3_sq_add
    rw [reChi3_two, hsum]; norm_num

end C3Character

section C3Kernel

/-- The α-part of the plaquette's four column words at the C₃ seat,
read off the fixed plaquette `P₀ = ((0,0,0), x)`: with column words
`W₁ = α_a · u'_{b} · α_b⁻¹ · u_a⁻¹` etc. and the additive notation of
`ZMod 3`, the four words are `Aᵢ(α) + (vᵢ − uᵢ)` where the boundary
letters are `uᵢ = u eᵢ`, `vᵢ = u' eᵢ` and
`A = (α₀ − α₁, α₁ − α₂, α₃ − α₂, α₀ − α₃)`. -/
def alphaPart (α : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  ![α 0 - α 1, α 1 - α 2, α 3 - α 2, α 0 - α 3]

/-- The plaquette's four column words (additive C₃ notation). -/
def wordC3 (α u v : Fin 4 → ZMod 3) (i : Fin 4) : ZMod 3 :=
  alphaPart α i + (v i - u i)

/-- The boundary phase `h(u) = u₃ + u₂ − u₁ − u₀`. -/
def hC3 (u : Fin 4 → ZMod 3) : ZMod 3 := u 3 + u 2 - u 1 - u 0

/-- The per-plaquette kernel factor at the C₃ seat: the uniform
α-average of the product of the four mixed pairings
`x_P = reChi(W_P)` (d = 1, so `x_P = Re χ(W_P)`).  This is exactly
the `(1/4!)`-weighted, one-plaquette monomial expectation whose sum
over spatial plaquettes and orientations is κ₄^dep's plaquette
block at N = 2 (multinomial weight 1; the block structure is the
provenance fence in the header). -/
def FC3 (u v : Fin 4 → ZMod 3) : ℚ :=
  (1 / 81) * ∑ α, ∏ i, reChi3 (wordC3 α u v i)

/-- Sign vector of a subset `t ⊆ Fin 4`: `+1` on `t`, `−1` off it. -/
def sgnT (t : Finset (Fin 4)) (i : Fin 4) : ZMod 3 := if i ∈ t then 1 else -1

theorem sgnT_mul (t : Finset (Fin 4)) (i : Fin 4) (w : ZMod 3) :
    sgnT t i * w = if i ∈ t then w else -w := by
  by_cases hi : i ∈ t <;> simp [sgnT, hi]

/-- The α-coefficients of the signed word sum `∑ᵢ σᵢ Wᵢ`:
`∑ᵢ σᵢ Wᵢ α = ∑ₛ cCoeff(t)ₛ · αₛ + pC3(t)`. -/
def cCoeff (t : Finset (Fin 4)) : Fin 4 → ZMod 3 :=
  ![sgnT t 0 + sgnT t 3, -sgnT t 0 + sgnT t 1,
    -sgnT t 1 - sgnT t 2, sgnT t 2 - sgnT t 3]

/-- The boundary part of the signed word sum. -/
def pC3 (t : Finset (Fin 4)) (u v : Fin 4 → ZMod 3) : ZMod 3 :=
  ∑ i, sgnT t i * (v i - u i)

private theorem vec4_apply (x : Fin 4 → ZMod 3) (a b c d : ZMod 3)
    (h : x = ![a, b, c, d]) :
    x 0 = a ∧ x 1 = b ∧ x 2 = c ∧ x 3 = d := by
  subst h
  exact ⟨by simp [Matrix.cons_val_zero],
    by simp [Matrix.cons_val_one, Matrix.head_cons],
    by simp [Matrix.cons_val_two, Matrix.head_cons],
    by simp [Matrix.cons_val_three, Matrix.head_cons]⟩

theorem wordC3_sum_id (t : Finset (Fin 4)) (α u v : Fin 4 → ZMod 3) :
    ∑ i, sgnT t i * wordC3 α u v i
      = ∑ s, cCoeff t s * α s + pC3 t u v := by
  have hA := vec4_apply (alphaPart α) _ _ _ _ rfl
  have hC := vec4_apply (cCoeff t) _ _ _ _ rfl
  have key : ∀ F : Fin 4 → ZMod 3,
      (∑ i, sgnT t i * F i) = sgnT t 0 * F 0 + sgnT t 1 * F 1
        + sgnT t 2 * F 2 + sgnT t 3 * F 3 :=
    fun F => Fin.sum_univ_four _
  rw [show (∑ i, sgnT t i * wordC3 α u v i)
      = ∑ i, (sgnT t i * alphaPart α i + sgnT t i * (v i - u i)) from
    Finset.sum_congr rfl (fun i _ => by rw [wordC3]; ring)]
  rw [Finset.sum_add_distrib, key, key, pC3, key, Fin.sum_univ_four]
  rw [hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, hC.1, hC.2.1, hC.2.2.1, hC.2.2.2]
  ring

/-- The signed word product is `χ` of the signed word sum. -/
theorem prod_split (t : Finset (Fin 4)) (α u v : Fin 4 → ZMod 3) :
    (∏ i ∈ t, chiC3 (wordC3 α u v i))
        * (∏ i ∈ univ \ t, chiC3 (-wordC3 α u v i))
      = chiC3 (∑ i, sgnT t i * wordC3 α u v i) := by
  have hsum : (∑ i ∈ t, wordC3 α u v i)
        + (∑ i ∈ univ \ t, -wordC3 α u v i)
      = ∑ i, sgnT t i * wordC3 α u v i := by
    have hA : ∑ i, (if i ∈ t then wordC3 α u v i else 0)
        = ∑ i ∈ t, wordC3 α u v i := by
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp [Finset.mem_filter]
    have hB : ∑ i, (if i ∈ t then (0 : ZMod 3) else -wordC3 α u v i)
        = ∑ i ∈ univ \ t, -wordC3 α u v i := by
      have e1 : (univ.filter (fun i => i ∉ t)) = univ \ t := by
        ext i
        simp [Finset.mem_sdiff]
      rw [← e1, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ t <;> simp [hi]
    rw [← hA, ← hB, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [sgnT_mul]
    by_cases hi : i ∈ t <;> simp [hi]
  rw [← chiC3_sum_prod t (fun i => wordC3 α u v i),
    ← chiC3_sum_prod (univ \ t) (fun i => -wordC3 α u v i), ← chiC3_add]
  exact congrArg chiC3 hsum

end C3Kernel

section C3Identification

/-- The α-integral of a single signed word: the character sum
factorizes over the four stratum sites of the plaquette, and only
the zero coefficient vector survives. -/
theorem alpha_sum (c : Fin 4 → ZMod 3) (p : ZMod 3) :
    ∑ α : Fin 4 → ZMod 3, chiC3 (∑ s, c s * α s + p)
      = if (∀ s, c s = 0) then 81 * chiC3 p else 0 := by
  have step1 : ∀ α : Fin 4 → ZMod 3,
      chiC3 (∑ s, c s * α s + p) = chiC3 p * ∏ s, chiC3 (c s * α s) := by
    intro α
    rw [chiC3_add, chiC3_sum_prod]
    ring
  have factor : (∑ α : Fin 4 → ZMod 3, ∏ s, chiC3 (c s * α s))
      = ∏ s, ∑ a, chiC3 (c s * a) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [Finset.sum_congr rfl (fun α _ => step1 α), ← Finset.mul_sum, factor]
  rw [Finset.prod_congr rfl (fun s _ => chiC3_sum (c s))]
  by_cases hall : ∀ s, c s = 0
  · rw [if_pos hall]
    have h3 : ∏ s : Fin 4, (if c s = 0 then (3 : ℂ) else 0) = 81 := by
      rw [Finset.prod_congr rfl (fun s _ => if_pos (hall s))]
      simp [Finset.prod_const, Finset.card_univ]
      norm_num
    rw [h3]; ring
  · rw [if_neg hall]
    push_neg at hall
    obtain ⟨s₀, hs₀⟩ := hall
    rw [Finset.prod_eq_zero (Finset.mem_univ s₀) (if_neg hs₀)]
    simp

/-- Survival classification: the coefficient vector `cCoeff t`
vanishes identically only for the two pure sign patterns
`t = {0, 1}` (signs `+, +, −, −`) and `t = {2, 3}`.  This is the
heart of the C₃ seat: a plaquette monomial survives the α-integral
only when its four columns pair into two conjugate pairs.
(Decided by exhaustive evaluation over the 16 subsets.) -/
theorem survivors : ∀ t : Finset (Fin 4), (∀ s, cCoeff t s = 0)
    ↔ t = {0, 1} ∨ t = {2, 3} := by decide

theorem sgnT_pair01 : ∀ i, sgnT ({0, 1} : Finset (Fin 4)) i
    = ![1, 1, -1, -1] i := by decide

theorem sgnT_pair23 : ∀ i, sgnT ({2, 3} : Finset (Fin 4)) i
    = ![-1, -1, 1, 1] i := by decide

theorem pC3_pair01 (u v : Fin 4 → ZMod 3) :
    pC3 {0, 1} u v = hC3 u - hC3 v := by
  unfold pC3 hC3
  rw [Fin.sum_univ_four, sgnT_pair01 0, sgnT_pair01 1, sgnT_pair01 2,
    sgnT_pair01 3]
  have e := vec4_apply (![1, 1, -1, -1] : Fin 4 → ZMod 3) _ _ _ _ rfl
  rw [e.1, e.2.1, e.2.2.1, e.2.2.2]
  ring

theorem pC3_pair23 (u v : Fin 4 → ZMod 3) :
    pC3 {2, 3} u v = -(hC3 u - hC3 v) := by
  unfold pC3 hC3
  rw [Fin.sum_univ_four, sgnT_pair23 0, sgnT_pair23 1, sgnT_pair23 2,
    sgnT_pair23 3]
  have e := vec4_apply (![-1, -1, 1, 1] : Fin 4 → ZMod 3) _ _ _ _ rfl
  rw [e.1, e.2.1, e.2.2.1, e.2.2.2]
  ring

/-- Per-α expansion of the plaquette monomial over sign patterns. -/
theorem per_alpha (α u v : Fin 4 → ZMod 3) :
    ∏ i, ((reChi3 (wordC3 α u v i) : ℚ) : ℂ)
      = (1 / 16) * ∑ t : Finset (Fin 4),
          chiC3 (∑ s, cCoeff t s * α s + pC3 t u v) := by
  have hpow : (univ : Finset (Fin 4)).powerset = univ :=
    Finset.eq_univ_of_forall (fun t =>
      Finset.mem_powerset.mpr (Finset.subset_univ t))
  calc ∏ i, ((reChi3 (wordC3 α u v i) : ℚ) : ℂ)
      = ∏ i, ((chiC3 (wordC3 α u v i) + chiC3 (-wordC3 α u v i)) / 2) :=
        Finset.prod_congr rfl (fun i _ => reChi3_cast _)
    _ = (∏ i, (chiC3 (wordC3 α u v i) + chiC3 (-wordC3 α u v i))) / 16 := by
        rw [Finset.prod_div_distrib]
        simp [Finset.prod_const, Finset.card_univ]
        ring
    _ = (1 / 16) * ∑ t ∈ univ.powerset,
          (∏ i ∈ t, chiC3 (wordC3 α u v i))
            * ∏ i ∈ univ \ t, chiC3 (-wordC3 α u v i) := by
        rw [Finset.prod_add]
        ring
    _ = (1 / 16) * ∑ t : Finset (Fin 4),
          chiC3 (∑ s, cCoeff t s * α s + pC3 t u v) := by
        rw [hpow]
        congr 1
        apply Finset.sum_congr rfl
        intro t _
        rw [prod_split, wordC3_sum_id]

/-- **Seat S1 identification (T1).**  The per-plaquette kernel
factor at (C₃, faithful χ) is the holonomy class kernel
`F(u, u′) = (1/8) · reChi(h(u) − h(u′))` — the two surviving sign
patterns contribute conjugate phases whose sum is `2·reChi` of the
holonomy difference, and the `81` α-configurations cancel the
normalization. -/
theorem FC3_eq (u v : Fin 4 → ZMod 3) :
    FC3 u v = (1 / 8) * reChi3 (hC3 u - hC3 v) := by
  have key : ((FC3 u v : ℚ) : ℂ)
      = (1 / 16 : ℂ) * (chiC3 (hC3 u - hC3 v) + chiC3 (-(hC3 u - hC3 v))) := by
    have hfil : Finset.filter (fun t : Finset (Fin 4) => ∀ s, cCoeff t s = 0)
        univ = {{0, 1}, {2, 3}} := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      exact survivors t
    calc ((FC3 u v : ℚ) : ℂ)
        = (1 / 81) * ∑ α, ∏ i, ((reChi3 (wordC3 α u v i) : ℚ) : ℂ) := by
          rw [FC3]; push_cast; ring
      _ = (1 / 81) * ∑ α : Fin 4 → ZMod 3, ((1 / 16) * ∑ t : Finset (Fin 4),
            chiC3 (∑ s, cCoeff t s * α s + pC3 t u v)) := by
          congr 1
          exact Finset.sum_congr rfl (fun α _ => per_alpha α u v)
      _ = (1 / 81) * ((1 / 16) * ∑ α : Fin 4 → ZMod 3, ∑ t : Finset (Fin 4),
            chiC3 (∑ s, cCoeff t s * α s + pC3 t u v)) := by
          congr 1
          rw [Finset.mul_sum]
      _ = (1 / 81) * ((1 / 16) * ∑ t : Finset (Fin 4),
            ∑ α : Fin 4 → ZMod 3, chiC3 (∑ s, cCoeff t s * α s + pC3 t u v)) := by
          congr 1
          rw [Finset.sum_comm]
      _ = (1 / 81) * ((1 / 16) * ∑ t : Finset (Fin 4),
            if (∀ s, cCoeff t s = 0) then 81 * chiC3 (pC3 t u v) else 0) := by
          congr 1; congr 1
          apply Finset.sum_congr rfl
          intro t _
          exact alpha_sum _ _
      _ = (1 / 81) * ((1 / 16) * (81 * chiC3 (hC3 u - hC3 v)
            + 81 * chiC3 (-(hC3 u - hC3 v)))) := by
          congr 1; congr 1
          rw [← Finset.sum_filter, hfil,
            Finset.sum_insert (by decide), Finset.sum_singleton,
            pC3_pair01, pC3_pair23]
      _ = (1 / 16 : ℂ) * (chiC3 (hC3 u - hC3 v)
            + chiC3 (-(hC3 u - hC3 v))) := by ring
  have h2 : (((1 / 8) * reChi3 (hC3 u - hC3 v) : ℚ) : ℂ)
      = (1 / 16 : ℂ) * (chiC3 (hC3 u - hC3 v) + chiC3 (-(hC3 u - hC3 v))) := by
    rw [show (((1 / 8) * reChi3 (hC3 u - hC3 v) : ℚ) : ℂ)
        = (1 / 8 : ℂ) * ((reChi3 (hC3 u - hC3 v) : ℚ) : ℂ) by push_cast; ring,
      reChi3_cast]
    ring
  exact Rat.cast_injective (key.trans h2.symm)

end C3Identification

section C3FiberForm

/-- Reparametrization moving the holonomy phase to the first
coordinate: every fiber of `hC3` has exactly `27` elements. -/
def EC3 : (Fin 4 → ZMod 3) ≃ (Fin 4 → ZMod 3) where
  toFun u := ![hC3 u, u 0, u 1, u 2]
  invFun w := ![w 1, w 2, w 3, w 0 - w 3 + w 2 + w 1]
  left_inv u := by
    funext i
    fin_cases i <;> simp [hC3, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three] <;> ring
  right_inv w := by
    funext i
    fin_cases i <;> simp [hC3, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three] <;> ring

theorem EC3_zero (u : Fin 4 → ZMod 3) : EC3 u 0 = hC3 u := by
  simp [EC3, Matrix.cons_val_zero]

theorem sum_fst (f : ZMod 3 → ℚ) :
    ∑ w : Fin 4 → ZMod 3, f (w 0) = 27 * ∑ a, f a := by
  have hstep : ∀ w : Fin 4 → ZMod 3,
      ((Fin.insertNthEquiv (fun _ : Fin 4 => ZMod 3) 0).symm w).1 = w 0 :=
    fun w => rfl
  have h := Equiv.sum_comp (Fin.insertNthEquiv (fun _ : Fin 4 => ZMod 3) 0).symm
    (fun p : ZMod 3 × (∀ i : Fin 3, (fun _ : Fin 4 => ZMod 3) (Fin.succAbove 0 i))
      => f p.1)
  calc ∑ w : Fin 4 → ZMod 3, f (w 0)
      = ∑ w : Fin 4 → ZMod 3,
          f ((Fin.insertNthEquiv (fun _ : Fin 4 => ZMod 3) 0).symm w).1 :=
        Finset.sum_congr rfl (fun w _ => by rw [hstep w])
    _ = ∑ p : ZMod 3 × (∀ i : Fin 3, (fun _ : Fin 4 => ZMod 3)
          (Fin.succAbove 0 i)), f p.1 := h
    _ = ∑ a, ∑ _g : (∀ i : Fin 3, (fun _ : Fin 4 => ZMod 3)
          (Fin.succAbove 0 i)), f a := Fintype.sum_prod_type _
    _ = 27 * ∑ a, f a := by
        rw [Finset.sum_congr rfl (g := fun a => (27 : ℚ) * f a) (fun a _ => by
          rw [Finset.sum_const, Finset.card_univ]
          have hcard : Fintype.card (∀ i : Fin 3, (fun _ : Fin 4 => ZMod 3)
              (Fin.succAbove 0 i)) = 27 := by simp [Fintype.card_pi]
          rw [hcard, nsmul_eq_mul]; norm_num)]
        rw [Finset.mul_sum]

/-- The fiber lemma: summing a class function over boundary values
factors through `hC3` with fiber size `27`. -/
theorem sum_hC3 (f : ZMod 3 → ℚ) :
    ∑ u : Fin 4 → ZMod 3, f (hC3 u) = 27 * ∑ a, f a := by
  calc ∑ u : Fin 4 → ZMod 3, f (hC3 u)
      = ∑ u : Fin 4 → ZMod 3, f (EC3 u 0) :=
        Finset.sum_congr rfl (fun u _ => by rw [EC3_zero])
    _ = ∑ w : Fin 4 → ZMod 3, f (w 0) := Equiv.sum_comp EC3 (fun w => f (w 0))
    _ = 27 * ∑ a, f a := sum_fst f

/-- The finite form identity behind seat S1's positivity:
pairing the class kernel `reChi(a − b)` over `ZMod 3`. -/
theorem reChi3_form (φ : ZMod 3 → ℚ) :
    ∑ a, φ a * (∑ b, reChi3 (a - b) * φ b)
      = (1 / 2) * ((φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2 + (φ 1 - φ 2) ^ 2) := by
  rw [sum_zmod3 (fun a => φ a * (∑ b, reChi3 (a - b) * φ b)),
    sum_zmod3 (fun b => reChi3 ((0 : ZMod 3) - b) * φ b),
    sum_zmod3 (fun b => reChi3 ((1 : ZMod 3) - b) * φ b),
    sum_zmod3 (fun b => reChi3 ((2 : ZMod 3) - b) * φ b)]
  rw [show ((0 : ZMod 3) - 0) = 0 from rfl, show ((0 : ZMod 3) - 1) = 2 from rfl,
    show ((0 : ZMod 3) - 2) = 1 from rfl, show ((1 : ZMod 3) - 0) = 1 from rfl,
    show ((1 : ZMod 3) - 1) = 0 from rfl, show ((1 : ZMod 3) - 2) = 2 from rfl,
    show ((2 : ZMod 3) - 0) = 2 from rfl, show ((2 : ZMod 3) - 1) = 1 from rfl,
    show ((2 : ZMod 3) - 2) = 0 from rfl,
    reChi3_zero, reChi3_one, reChi3_two]
  ring

/-- **Seat S1 quadratic form (T1).**  The pairing of κ₄^dep's
plaquette block at (C₃, χ) with a test observable depending only on
the boundary holonomy, summed over all boundary values, is an
explicit positive multiple of a sum of squares of differences —
the form is PSD and vanishes exactly on constants. -/
theorem FC3_form (φ : ZMod 3 → ℚ) :
    ∑ u, ∑ v, φ (hC3 u) * FC3 u v * φ (hC3 v)
      = (729 / 16) * ((φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2 + (φ 1 - φ 2) ^ 2) := by
  have stepA : ∀ u : Fin 4 → ZMod 3,
      ∑ v, φ (hC3 u) * FC3 u v * φ (hC3 v)
        = (27 / 8) * (φ (hC3 u) * (∑ b, reChi3 (hC3 u - b) * φ b)) := by
    intro u
    calc ∑ v, φ (hC3 u) * FC3 u v * φ (hC3 v)
        = ∑ v, ((1 / 8) * φ (hC3 u))
            * (reChi3 (hC3 u - hC3 v) * φ (hC3 v)) :=
          Finset.sum_congr rfl (fun v _ => by rw [FC3_eq]; ring)
      _ = ((1 / 8) * φ (hC3 u))
            * ∑ v, reChi3 (hC3 u - hC3 v) * φ (hC3 v) := by
          rw [Finset.mul_sum]
      _ = ((1 / 8) * φ (hC3 u))
            * (27 * ∑ b, reChi3 (hC3 u - b) * φ b) := by
          rw [sum_hC3 (fun b => reChi3 (hC3 u - b) * φ b)]
      _ = (27 / 8) * (φ (hC3 u) * (∑ b, reChi3 (hC3 u - b) * φ b)) := by ring
  calc ∑ u, ∑ v, φ (hC3 u) * FC3 u v * φ (hC3 v)
      = ∑ u, (27 / 8) * (φ (hC3 u) * (∑ b, reChi3 (hC3 u - b) * φ b)) :=
        Finset.sum_congr rfl (fun u _ => stepA u)
    _ = (27 / 8) * ∑ u, (φ (hC3 u) * (∑ b, reChi3 (hC3 u - b) * φ b)) := by
        rw [Finset.mul_sum]
    _ = (27 / 8) * (27 * ∑ a, φ a * (∑ b, reChi3 (a - b) * φ b)) := by
        congr 1
        exact sum_hC3 (fun a => φ a * (∑ b, reChi3 (a - b) * φ b))
    _ = (729 / 16) * ((φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2
        + (φ 1 - φ 2) ^ 2) := by
        rw [reChi3_form]
        ring

theorem FC3_form_nonneg (φ : ZMod 3 → ℚ) :
    0 ≤ ∑ u, ∑ v, φ (hC3 u) * FC3 u v * φ (hC3 v) := by
  rw [FC3_form]
  apply mul_nonneg (by norm_num)
  exact add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)

end C3FiberForm

section C3Blocks

/-- Seat S1's plaquette block as a class kernel on `ZMod 3`:
`Φ₁(a, b) = (1/8) · reChi(a − b)`; by `FC3_eq` this is the
`(u, u′) ↦ F` kernel grouped by holonomy. -/
def PhiC3 (a b : ZMod 3) : ℚ := (1 / 8) * reChi3 (a - b)

theorem PhiC3_eq (a b : ZMod 3) :
    PhiC3 a b = if a = b then 1 / 8 else -1 / 16 := by
  by_cases h : a = b
  · simp only [PhiC3, reChi3_sub, if_pos h]; norm_num
  · simp only [PhiC3, reChi3_sub, if_neg h]; norm_num

/-- `Φ₁ = (3/16) I − (1/16) J`: spectrum `{0, 3/16, 3/16}` — zero
on constants, `3/16` on both nontrivial character directions. -/
theorem PhiC3_IJ (a b : ZMod 3) :
    PhiC3 a b = (3 / 16) * (if a = b then 1 else 0) - 1 / 16 := by
  by_cases h : a = b
  · rw [PhiC3_eq, if_pos h, if_pos h]; norm_num
  · rw [PhiC3_eq, if_neg h, if_neg h]; norm_num

theorem PhiC3_margins (a : ZMod 3) : ∑ b, PhiC3 a b = 0 := by
  have hite : ∑ b, (if a = b then (1 : ℚ) else 0) = 1 := by
    rw [Finset.sum_ite_eq]; simp
  rw [Finset.sum_congr rfl (fun b _ => PhiC3_IJ a b), Finset.sum_sub_distrib,
    ← Finset.mul_sum, hite]
  simp [Finset.sum_const, Finset.card_univ]
  norm_num

/-- Seat S1's pair block (the N = 2 same-site extras, dependent
part): `Ψ₁ = (5/64)(3I − J)` on holonomy classes, i.e.
`Ψ₁(a, b) = 5/32` on the diagonal, `−5/64` off it. -/
def PsiC3 (a b : ZMod 3) : ℚ := if a = b then 5 / 32 else -5 / 64

theorem PsiC3_form (φ : ZMod 3 → ℚ) :
    ∑ a, ∑ b, φ a * (3 * PsiC3 a b * 3) * φ b
      = (45 / 64) * ((φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2 + (φ 1 - φ 2) ^ 2) := by
  have e00 : PsiC3 0 0 = 5 / 32 := if_pos rfl
  have e01 : PsiC3 0 1 = -5 / 64 := if_neg (by decide)
  have e02 : PsiC3 0 2 = -5 / 64 := if_neg (by decide)
  have e10 : PsiC3 1 0 = -5 / 64 := if_neg (by decide)
  have e11 : PsiC3 1 1 = 5 / 32 := if_pos rfl
  have e12 : PsiC3 1 2 = -5 / 64 := if_neg (by decide)
  have e20 : PsiC3 2 0 = -5 / 64 := if_neg (by decide)
  have e21 : PsiC3 2 1 = -5 / 64 := if_neg (by decide)
  have e22 : PsiC3 2 2 = 5 / 32 := if_pos rfl
  rw [sum_zmod3 (fun a => ∑ b, φ a * (3 * PsiC3 a b * 3) * φ b),
    sum_zmod3 (fun b => φ 0 * (3 * PsiC3 0 b * 3) * φ b),
    sum_zmod3 (fun b => φ 1 * (3 * PsiC3 1 b * 3) * φ b),
    sum_zmod3 (fun b => φ 2 * (3 * PsiC3 2 b * 3) * φ b),
    e00, e01, e02, e10, e11, e12, e20, e21, e22]
  ring

theorem PsiC3_margins (a : ZMod 3) : ∑ b, PsiC3 a b = 0 := by
  have hite : ∑ b, (if a = b then (1 : ℚ) else 0) = 1 := by
    rw [Finset.sum_ite_eq]; simp
  have hIJ : ∀ b : ZMod 3, PsiC3 a b
      = (15 / 64) * (if a = b then 1 else 0) - 5 / 64 := by
    intro b
    by_cases h : a = b
    · rw [if_pos h]; rw [show PsiC3 a b = 5 / 32 from if_pos h]; norm_num
    · rw [if_neg h]; rw [show PsiC3 a b = -5 / 64 from if_neg h]; norm_num
  rw [Finset.sum_congr rfl (fun b _ => hIJ b), Finset.sum_sub_distrib,
    ← Finset.mul_sum, hite]
  simp [Finset.sum_const, Finset.card_univ]
  norm_num

theorem PsiC3_form_nonneg (φ : ZMod 3 → ℚ) :
    0 ≤ ∑ a, ∑ b, φ a * (3 * PsiC3 a b * 3) * φ b := by
  rw [PsiC3_form]
  apply mul_nonneg (by norm_num)
  exact add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)

end C3Blocks

section S3Blocks

/-- Conjugacy-class index for S₃: `0` = identity class,
`1` = transpositions, `2` = 3-cycles.  Character table of S₃,
rows indexed by class, columns by `(triv, sgn, std)`. -/
def XS3 : Matrix (Fin 3) (Fin 3) ℚ := ![![1, 1, 2], ![1, -1, 0], ![1, 1, -1]]

/-- The transpose of `XS3`, as an explicit table (proved equal to
`Matrix.transpose XS3` below). -/
def XS3t : Matrix (Fin 3) (Fin 3) ℚ := ![![1, 1, 1], ![1, -1, 1], ![2, 0, -1]]

theorem XS3t_eq : XS3t = Matrix.transpose XS3 := by
  ext a b
  rw [Matrix.transpose_apply]
  fin_cases a <;> fin_cases b <;> simp [XS3, XS3t, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons] <;> norm_num

/-- Seat S2's face block: SBP-1's class matrix
`Φ = [[1/64, 0, −1/128], [0, 0, 0], [−1/128, 0, 1/256]]`
(recomputed exactly for this probe; a second reading from the
opposite base point gives the same class kernel). -/
def PhiS3 : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![1 / 64, 0, -1 / 128], ![0, 0, 0], ![-1 / 128, 0, 1 / 256]]

/-- The fiber sizes of the three classes: `(216, 648, 432)`. -/
def nS3 : Fin 3 → ℚ := ![216, 648, 432]

/-- The rank-one vector of the face block: `Φ₂ = w wᵀ`. -/
def wS3 : Fin 3 → ℚ := ![1 / 8, 0, -1 / 16]

/-- Seat S2's pair block (dependent part, the N = 2 same-site
extras): `Ψ₂` on conjugacy classes. -/
def PsiS3 : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![3 / 32, -1 / 64, -3 / 128], ![-1 / 64, 1 / 64, -1 / 64],
    ![-3 / 128, -1 / 64, 9 / 256]]

/-- Pair-holonomy fiber sizes: `(6, 18, 12)`. -/
def nPS3 : Fin 3 → ℚ := ![6, 18, 12]

/-- The face block is the outer square `w wᵀ`. -/
theorem PhiS3_outer (a b : Fin 3) : PhiS3 a b = wS3 a * wS3 b := by
  fin_cases a <;> fin_cases b <;> simp [PhiS3, wS3, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three] <;> norm_num

/-- The face block's quadratic form is a perfect square. -/
theorem formS3_face (φ : Fin 3 → ℚ) :
    ∑ a, ∑ b, φ a * (nS3 a * PhiS3 a b * nS3 b) * φ b
      = (∑ a, φ a * nS3 a * wS3 a) ^ 2 := by
  rw [pow_two, Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [PhiS3_outer]; ring

theorem formS3_face_nonneg (φ : Fin 3 → ℚ) :
    0 ≤ ∑ a, ∑ b, φ a * (nS3 a * PhiS3 a b * nS3 b) * φ b := by
  rw [formS3_face]; exact sq_nonneg _

/-- The face form's matrix in class coordinates: `D Φ₂ D`. -/
def DS3 : Matrix (Fin 3) (Fin 3) ℚ := fun a b => nS3 a * PhiS3 a b * nS3 b

/-- Character-basis evaluation of the face form:
`Xᵀ (D Φ₂ D) X = diag(0, 0, 6561)` — the plaquette block sees only
the std direction, with eigenvalue `6561 = 3⁸`. -/
theorem BS3_face :
    XS3t * DS3 * XS3
      = ![![0, 0, 0], ![0, 0, 0], ![0, 0, 6561]] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    rw [Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three] <;>
    simp only [XS3, XS3t, DS3, PhiS3, nS3, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons] <;> norm_num

theorem PhiS3_margins (a : Fin 3) : ∑ b, nS3 b * PhiS3 a b = 0 := by
  fin_cases a <;> rw [Fin.sum_univ_three] <;> simp [PhiS3, nS3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- The pair form's matrix in class coordinates: `D Ψ₂ D`. -/
def DPS3 : Matrix (Fin 3) (Fin 3) ℚ := fun a b => nPS3 a * PsiS3 a b * nPS3 b

/-- The pair block's margins vanish exactly (the dependent-part
check that fixes the cumulant assembly). -/
theorem PsiS3_margins (a : Fin 3) : ∑ b, nPS3 b * PsiS3 a b = 0 := by
  fin_cases a <;> rw [Fin.sum_univ_three] <;> simp [PsiS3, nPS3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- Character-basis evaluation of the pair form:
`Xᵀ (D Ψ₂ D) X = diag(0, 81/4, 405/16)` — the N = 2 extras are
positive on both nontrivial character directions. -/
theorem BS3_pair :
    XS3t * DPS3 * XS3
      = ![![0, 0, 0], ![0, 81 / 4, 0], ![0, 0, 405 / 16]] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    rw [Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three] <;>
    simp only [XS3, XS3t, DPS3, PsiS3, nPS3, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons] <;> norm_num

/-- The pair block's quadratic form is an explicit sum of two
squares (the character components `θ_sgn`, `θ_std`). -/
theorem formS3_pair (ψ : Fin 3 → ℚ) :
    ∑ a, ∑ b, ψ a * (nPS3 a * PsiS3 a b * nPS3 b) * ψ b
      = (81 / 4) * ((ψ 0 - 3 * ψ 1 + 2 * ψ 2) / 6) ^ 2
        + (405 / 16) * ((ψ 0 - ψ 2) / 3) ^ 2 := by
  rw [Fin.sum_univ_three (fun a => ∑ b, ψ a * (nPS3 a * PsiS3 a b * nPS3 b) * ψ b),
    Fin.sum_univ_three (fun b => ψ 0 * (nPS3 0 * PsiS3 0 b * nPS3 b) * ψ b),
    Fin.sum_univ_three (fun b => ψ 1 * (nPS3 1 * PsiS3 1 b * nPS3 b) * ψ b),
    Fin.sum_univ_three (fun b => ψ 2 * (nPS3 2 * PsiS3 2 b * nPS3 b) * ψ b)]
  simp only [PsiS3, nPS3, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons]
  ring

theorem formS3_pair_nonneg (ψ : Fin 3 → ℚ) :
    0 ≤ ∑ a, ∑ b, ψ a * (nPS3 a * PsiS3 a b * nPS3 b) * ψ b := by
  rw [formS3_pair]
  exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg (by norm_num) (sq_nonneg _))

end S3Blocks

end ThetLogos
