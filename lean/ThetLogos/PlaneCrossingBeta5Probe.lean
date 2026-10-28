import ThetLogos.PlaneCrossingBeta5
import ThetLogos.PlaneCrossingKappa4Probe

/-!
# β⁵ probe: the joint (κ₄^dep, κ₅ channel) seat evaluation at N = 4

NO CLAIM.  Parts of the Clay Yang–Mills statement closed by
this module: **0**.  Dials 0/4.  This is a seat computation
for the β2 corridor, in the pattern of the κ₄ probe
(`PlaneCrossingKappa4Probe`): exact finite arithmetic at two
seats, **(C₃, faithful χ)** at `d = 1` and **(S₃, std)** at
`d = 2`, both at **N = 4** — the smallest volume in the
`3 ≤ N` regime, where primitive quads are plaquettes and
straight wrap chains (PQ-0: `primitive_pattern_eq_C4`; the
generating census at N = 4 is 192 plaquettes and 48 wrap
chains, 240 quads, hence 960 doubled channel terms — the
census is the scoping's count, cited as provenance; what is
proved here is every per-term factor and every form).

**What is evaluated.**  The order-5 channel form is
`kappa5chan2111` (owned by `PlaneCrossingBeta5`): the sum
over primitive quads `C` and doubled columns `P ∈ C` of
`doubledQuadReMoment C P`.  FENCE (the B5-2 seam, stated
exactly): the channel form stands for `kappa5dep`'s
dependent content **modulo B5-2's assembly identity** —
`kappa5dep = (normalization) · (channel sum − baseline)` —
which is named in `PlaneCrossingBeta5` and **not** asserted
there or here.  This module evaluates the channel form
itself, on the diagonal pairing of the kernel (the
quadratic-form diagonal of the κ₄ probe: profiles paired
against the (u, u′) kernel), jointly with κ₄^dep's form.

**Pre-registered kill K-K5** (β⁵ scoping, 2026-10-28): a
certified negative value of the κ₅ channel form at a vector
in `ker κ₄^dep`, at either seat, kills the β2 small-β route
at order 5.  A negative off the kernel decides nothing.

**Verdict of this module: K-K5 does NOT fire — PASS at both
seats, with the restriction exactly zero.**  At each seat
and for each quad type (plaquette and wrap chain), the
channel kernel is a positive multiple of the κ₄ kernel
(×2 at (C₃, χ); ×4 at (S₃, std)), hence has the same kernel
and vanishes on it: the joint kernel (constant profiles at
C₃; `{ψ₀ = ψ₂}` at S₃) is untouched at order 5, with margin
exactly zero — the degenerate-perturbation regress of the
β⁵ scoping, one order further: the decision along the joint
kernel moves to β⁶.  A pass at two seats is seat evidence,
not a general sign: β⁵'s sign at general (G, ρ) remains
FRONTIER (the (2,1) triple twirl is not owned), and nothing
here is a statement about 𝒜 ⪰ 0 in the large, about all β,
or about the continuum.

**Provenance.**  Seat (C₃, χ) is proved end-to-end in this
module (character sums over `ZMod 3`, in the κ₄ probe's
machinery, which is imported and reused): the doubled
plaquette factor is `(1/16)·reChi(h − h′)` for every doubled
column, the doubled wrap factor is `(1/16)·reChi(H − H′)`,
and the κ₄ factors `(1/8)·reChi` are the probe's `FC3_eq`
(plaquette) and this module's `FW_eq` (wrap chain).  Seat
(S₃, std) follows the κ₄ probe's S2 pattern: the per-quad
kernels are exact-arithmetic T4 inputs (this probe's exact
enumeration over `S₃⁴` stratum configurations, all
`6⁴ × 6⁴` boundary pairs reduced by the proved class-kernel
constancy checks of the probe script), **calibrated** in
Lean against the κ₄ probe: the plaquette κ₄ kernel computed
here in the `colRe = Re χ` convention is exactly
`16 • PhiS3` (`K4S3_calibration` below; the factor
`16 = d⁴` is the density-vs-`colRe` convention factor
between `PlaneCrossingBeta5`'s `colRe`-based channel and
the κ₄ probe's density-based blocks).  The Lean content at
S₃ is exact algebra about those matrices: outer-product
structure, form identities, character-basis evaluations,
margins, positivity, and the joint verdict.  Everything is
at finite seats; β2 remains open.
-/

namespace ThetLogos

open Finset

section B5C3Basic

/-- The square of the real C₃ character is affine in it:
`reChi(w)² = (1 + reChi(w))/2`.  This is the order-5
miracle at `d = 1`: doubling a column folds back onto the
undoubled moment, because `2w = −w` in `ZMod 3`. -/
theorem reChi3_sq (w : ZMod 3) : reChi3 w ^ 2 = (1 + reChi3 w) / 2 := by
  rcases zmod3_cases w with rfl | rfl | rfl
  · rw [reChi3_zero]; norm_num
  · rw [reChi3_one]; norm_num
  · rw [reChi3_two]; norm_num

/-- The per-plaquette **doubled** factor at (C₃, χ): the
uniform α-average of `reChi(W_k)² · ∏_{i ≠ k} reChi(W_i)`
over the plaquette's four stratum variables — the seat
avatar of one summand of `kappa5chan2111`'s inner sum
(`doubledQuadReMoment` at a plaquette, doubled column
`k`). -/
def GD3 (k : Fin 4) (u v : Fin 4 → ZMod 3) : ℚ :=
  (1 / 81) * ∑ α, (reChi3 (wordC3 α u v k)) ^ 2
    * ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)

end B5C3Basic

section B5Gen

/-- Component values of a `Fin 4`-vector given as a matrix
literal (this module's own copy of the probe's helper). -/
private theorem apply4 {α : Type*} (x : Fin 4 → α) (a b c d : α)
    (h : x = ![a, b, c, d]) :
    x 0 = a ∧ x 1 = b ∧ x 2 = c ∧ x 3 = d := by
  subst h
  exact ⟨by simp [Matrix.cons_val_zero],
    by simp [Matrix.cons_val_one, Matrix.head_cons],
    by simp [Matrix.cons_val_two, Matrix.head_cons],
    by simp [Matrix.cons_val_three, Matrix.head_cons]⟩

/-- The α-coefficient vector of a general signed word sum
`∑ᵢ sᵢ Wᵢ` over the plaquette words: `cGen s` is `cCoeff`
with the sign function `sgnT t` replaced by an arbitrary
coefficient function `s`. -/
def cGen (s : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  ![s 0 + s 3, -s 0 + s 1, -s 1 - s 2, s 2 - s 3]

theorem cGen_apply (s : Fin 4 → ZMod 3) :
    cGen s 0 = s 0 + s 3 ∧ cGen s 1 = -s 0 + s 1
      ∧ cGen s 2 = -s 1 - s 2 ∧ cGen s 3 = s 2 - s 3 :=
  apply4 _ _ _ _ _ rfl

/-- The signed word sum, general coefficients (plaquette):
`∑ᵢ sᵢ Wᵢ = ∑ₓ cGen(s)ₓ αₓ + ∑ᵢ sᵢ (vᵢ − uᵢ)`. -/
theorem wordC3_sum_gen (s α u v : Fin 4 → ZMod 3) :
    ∑ i, s i * wordC3 α u v i
      = ∑ x, cGen s x * α x + ∑ i, s i * (v i - u i) := by
  have hA := apply4 (alphaPart α) _ _ _ _ rfl
  have hC := cGen_apply s
  rw [Fin.sum_univ_four (fun i => s i * wordC3 α u v i),
    Fin.sum_univ_four (fun x => cGen s x * α x),
    Fin.sum_univ_four (fun i => s i * (v i - u i))]
  simp only [wordC3, hA.1, hA.2.1, hA.2.2.1, hA.2.2.2,
    hC.1, hC.2.1, hC.2.2.1, hC.2.2.2]
  ring

/-- The wrap chain's α-part: sites in a line, the last
column closing the cycle. -/
def alphaPartW (α : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  ![α 0 - α 1, α 1 - α 2, α 2 - α 3, α 3 - α 0]

/-- The wrap chain's four column words (additive C₃
notation), columns `(s, s+e), (s+e, s+2e), (s+2e, s+3e),
(s+3e, s)` at N = 4. -/
def wordW (α u v : Fin 4 → ZMod 3) (i : Fin 4) : ZMod 3 :=
  alphaPartW α i + (v i - u i)

/-- The wrap chain's holonomy: the total boundary sum. -/
def HW (u : Fin 4 → ZMod 3) : ZMod 3 := u 0 + u 1 + u 2 + u 3

/-- The α-coefficient vector of a general signed word sum
over the wrap-chain words. -/
def cGenW (s : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  ![s 0 - s 3, s 1 - s 0, s 2 - s 1, s 3 - s 2]

theorem cGenW_apply (s : Fin 4 → ZMod 3) :
    cGenW s 0 = s 0 - s 3 ∧ cGenW s 1 = s 1 - s 0
      ∧ cGenW s 2 = s 2 - s 1 ∧ cGenW s 3 = s 3 - s 2 :=
  apply4 _ _ _ _ _ rfl

/-- The signed word sum, general coefficients (wrap
chain). -/
theorem wordW_sum_gen (s α u v : Fin 4 → ZMod 3) :
    ∑ i, s i * wordW α u v i
      = ∑ x, cGenW s x * α x + ∑ i, s i * (v i - u i) := by
  have hA := apply4 (alphaPartW α) _ _ _ _ rfl
  have hC := cGenW_apply s
  rw [Fin.sum_univ_four (fun i => s i * wordW α u v i),
    Fin.sum_univ_four (fun x => cGenW s x * α x),
    Fin.sum_univ_four (fun i => s i * (v i - u i))]
  simp only [wordW, hA.1, hA.2.1, hA.2.2.1, hA.2.2.2,
    hC.1, hC.2.1, hC.2.2.1, hC.2.2.2]
  ring

/-- The sign pattern of a doubled moment: `sgnT t` with
the doubled column's sign replaced by `0` — the pattern
whose α-average must vanish (three surviving factors). -/
def sPat (k : Fin 4) (t : Finset (Fin 4)) : Fin 4 → ZMod 3 :=
  fun i => if i = k then 0 else sgnT t i

theorem sPat_self (k : Fin 4) (t : Finset (Fin 4)) :
    sPat k t k = 0 := if_pos rfl

theorem sPat_of_ne {k i : Fin 4} (t : Finset (Fin 4)) (h : i ≠ k) :
    sPat k t i = sgnT t i := if_neg h

theorem sgnT_ne_zero (t : Finset (Fin 4)) (i : Fin 4) :
    sgnT t i ≠ 0 := by
  by_cases hi : i ∈ t
  · rw [sgnT, if_pos hi]; decide
  · rw [sgnT, if_neg hi]; decide

theorem fin4_cases : ∀ k : Fin 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
  decide

/-- Private-site coefficients, plaquette: for each doubled
column `k`, the pattern `sPat k t` has a nonzero
α-coefficient at a site covered by exactly one of the
three surviving words (`k=0,1`: site 1; `k=2`: site 2;
`k=3`: site 3).  Hence no signed three-word sum survives
the α-average. -/
theorem cGen_sPat_ne (k : Fin 4) (t : Finset (Fin 4)) :
    ∃ x, cGen (sPat k t) x ≠ 0 := by
  rcases fin4_cases k with rfl | rfl | rfl | rfl
  · refine ⟨1, ?_⟩
    rw [(cGen_apply _).2.1, sPat_self, sPat_of_ne t (by decide : (1 : Fin 4) ≠ 0)]
    simpa using sgnT_ne_zero t 1
  · refine ⟨1, ?_⟩
    rw [(cGen_apply _).2.1, sPat_self, sPat_of_ne t (by decide : (0 : Fin 4) ≠ 1)]
    simpa using sgnT_ne_zero t 0
  · refine ⟨2, ?_⟩
    rw [(cGen_apply _).2.2.1, sPat_self, sPat_of_ne t (by decide : (1 : Fin 4) ≠ 2)]
    simpa using sgnT_ne_zero t 1
  · refine ⟨3, ?_⟩
    rw [(cGen_apply _).2.2.2, sPat_self, sPat_of_ne t (by decide : (2 : Fin 4) ≠ 3)]
    simpa using sgnT_ne_zero t 2

/-- Private-site coefficients, wrap chain: same statement
for `cGenW` (`k=0,1`: site 1; `k=2`: site 2; `k=3`:
site 3). -/
theorem cGenW_sPat_ne (k : Fin 4) (t : Finset (Fin 4)) :
    ∃ x, cGenW (sPat k t) x ≠ 0 := by
  rcases fin4_cases k with rfl | rfl | rfl | rfl
  · refine ⟨1, ?_⟩
    rw [(cGenW_apply _).2.1, sPat_self, sPat_of_ne t (by decide : (1 : Fin 4) ≠ 0)]
    simpa using sgnT_ne_zero t 1
  · refine ⟨1, ?_⟩
    rw [(cGenW_apply _).2.1, sPat_self, sPat_of_ne t (by decide : (0 : Fin 4) ≠ 1)]
    simpa using sgnT_ne_zero t 0
  · refine ⟨2, ?_⟩
    rw [(cGenW_apply _).2.2.1, sPat_self, sPat_of_ne t (by decide : (1 : Fin 4) ≠ 2)]
    simpa using sgnT_ne_zero t 1
  · refine ⟨3, ?_⟩
    rw [(cGenW_apply _).2.2.2, sPat_self, sPat_of_ne t (by decide : (2 : Fin 4) ≠ 3)]
    simpa using sgnT_ne_zero t 2

end B5Gen

section B5Expand

/-- The signed character product splits as the character
of the signed sum — the probe's `prod_split`, for an
arbitrary word function. -/
theorem prod_split_gen (W : Fin 4 → ZMod 3) (t : Finset (Fin 4)) :
    (∏ i ∈ t, chiC3 (W i)) * (∏ i ∈ univ \ t, chiC3 (-W i))
      = chiC3 (∑ i, sgnT t i * W i) := by
  have hsum : (∑ i ∈ t, W i) + (∑ i ∈ univ \ t, -W i)
      = ∑ i, sgnT t i * W i := by
    have hA : ∑ i, (if i ∈ t then W i else 0) = ∑ i ∈ t, W i := by
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp [Finset.mem_filter]
    have hB : ∑ i, (if i ∈ t then (0 : ZMod 3) else -W i)
        = ∑ i ∈ univ \ t, -W i := by
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
  rw [← chiC3_sum_prod t W, ← chiC3_sum_prod (univ \ t) (fun i => -W i),
    ← chiC3_add]
  exact congrArg chiC3 hsum

/-- The four-factor real-character product expands over
sign patterns — the probe's `per_alpha`, for an arbitrary
word function. -/
theorem per_alpha_gen (W : Fin 4 → ZMod 3) :
    ∏ i, ((reChi3 (W i) : ℚ) : ℂ)
      = (1 / 16) * ∑ t : Finset (Fin 4), chiC3 (∑ i, sgnT t i * W i) := by
  have hpow : (univ : Finset (Fin 4)).powerset = univ :=
    Finset.eq_univ_of_forall (fun t =>
      Finset.mem_powerset.mpr (Finset.subset_univ t))
  calc ∏ i, ((reChi3 (W i) : ℚ) : ℂ)
      = ∏ i, ((chiC3 (W i) + chiC3 (-W i)) / 2) :=
        Finset.prod_congr rfl (fun i _ => reChi3_cast _)
    _ = (∏ i, (chiC3 (W i) + chiC3 (-W i))) / 16 := by
        rw [Finset.prod_div_distrib]
        simp [Finset.prod_const, Finset.card_univ]
        ring
    _ = (1 / 16) * ∑ t ∈ univ.powerset,
          (∏ i ∈ t, chiC3 (W i)) * ∏ i ∈ univ \ t, chiC3 (-W i) := by
        rw [Finset.prod_add]
        ring
    _ = (1 / 16) * ∑ t : Finset (Fin 4), chiC3 (∑ i, sgnT t i * W i) := by
        rw [hpow]
        congr 1
        apply Finset.sum_congr rfl
        intro t _
        exact prod_split_gen W t

end B5Expand

section B5ChainFace

/-- The per-chain κ₄ factor at (C₃, χ): the uniform
α-average of the product of the four chain words' real
characters. -/
def FW (u v : Fin 4 → ZMod 3) : ℚ :=
  (1 / 81) * ∑ α, ∏ i, reChi3 (wordW α u v i)

/-- The α-coefficients of the signed chain word sum:
`cCoeffW t = cGenW (sgnT t)` (by definition). -/
def cCoeffW (t : Finset (Fin 4)) : Fin 4 → ZMod 3 :=
  ![sgnT t 0 - sgnT t 3, sgnT t 1 - sgnT t 0,
    sgnT t 2 - sgnT t 1, sgnT t 3 - sgnT t 2]

theorem cCoeffW_eq (t : Finset (Fin 4)) :
    cCoeffW t = cGenW (sgnT t) := rfl

/-- Survival classification for the chain: the coefficient
vector vanishes only for the two constant sign patterns.
(Decided by exhaustive evaluation over the 16 subsets.) -/
theorem survivorsW : ∀ t : Finset (Fin 4), (∀ s, cCoeffW t s = 0)
    ↔ t = ∅ ∨ t = univ := by decide

theorem sgnT_empty : ∀ i, sgnT (∅ : Finset (Fin 4)) i = -1 := by decide

theorem sgnT_univ : ∀ i, sgnT (univ : Finset (Fin 4)) i = 1 := by decide

theorem pC3_empty (u v : Fin 4 → ZMod 3) :
    pC3 ∅ u v = HW u - HW v := by
  unfold pC3 HW
  rw [Fin.sum_univ_four, sgnT_empty 0, sgnT_empty 1, sgnT_empty 2,
    sgnT_empty 3]
  ring

theorem pC3_univ (u v : Fin 4 → ZMod 3) :
    pC3 univ u v = HW v - HW u := by
  unfold pC3 HW
  rw [Fin.sum_univ_four, sgnT_univ 0, sgnT_univ 1, sgnT_univ 2,
    sgnT_univ 3]
  ring

/-- **Chain identification (T1).**  The per-chain κ₄
factor at (C₃, χ) is the holonomy class kernel
`(1/8) · reChi(H(u) − H(u′))` — the two constant sign
patterns survive the α-average, exactly as the two
paired patterns survive for the plaquette. -/
theorem FW_eq (u v : Fin 4 → ZMod 3) :
    FW u v = (1 / 8) * reChi3 (HW u - HW v) := by
  have key : ((FW u v : ℚ) : ℂ)
      = (1 / 16 : ℂ) * (chiC3 (HW u - HW v) + chiC3 (-(HW u - HW v))) := by
    have hfil : Finset.filter (fun t : Finset (Fin 4) => ∀ s, cCoeffW t s = 0)
        univ = {∅, univ} := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      exact survivorsW t
    calc ((FW u v : ℚ) : ℂ)
        = (1 / 81) * ∑ α, ∏ i, ((reChi3 (wordW α u v i) : ℚ) : ℂ) := by
          rw [FW]; push_cast; ring
      _ = (1 / 81) * ∑ α : Fin 4 → ZMod 3, ((1 / 16) * ∑ t : Finset (Fin 4),
            chiC3 (∑ s, cCoeffW t s * α s + pC3 t u v)) := by
          congr 1
          refine Finset.sum_congr rfl (fun α _ => ?_)
          rw [per_alpha_gen (wordW α u v)]
          congr 1
          refine Finset.sum_congr rfl (fun t _ => ?_)
          rw [wordW_sum_gen (sgnT t) α u v, ← cCoeffW_eq]
          rfl
      _ = (1 / 81) * ((1 / 16) * ∑ α : Fin 4 → ZMod 3,
            ∑ t : Finset (Fin 4),
            chiC3 (∑ s, cCoeffW t s * α s + pC3 t u v)) := by
          congr 1
          rw [Finset.mul_sum]
      _ = (1 / 81) * ((1 / 16) * ∑ t : Finset (Fin 4),
            ∑ α : Fin 4 → ZMod 3,
            chiC3 (∑ s, cCoeffW t s * α s + pC3 t u v)) := by
          congr 1
          rw [Finset.sum_comm]
      _ = (1 / 81) * ((1 / 16) * ∑ t : Finset (Fin 4),
            if (∀ s, cCoeffW t s = 0) then 81 * chiC3 (pC3 t u v)
            else 0) := by
          congr 1; congr 1
          apply Finset.sum_congr rfl
          intro t _
          exact alpha_sum _ _
      _ = (1 / 81) * ((1 / 16) * (81 * chiC3 (HW u - HW v)
            + 81 * chiC3 (-(HW u - HW v)))) := by
          congr 1; congr 1
          rw [← Finset.sum_filter, hfil,
            Finset.sum_insert (by decide), Finset.sum_singleton,
            pC3_empty, pC3_univ,
            show HW v - HW u = -(HW u - HW v) from by ring]
      _ = (1 / 16 : ℂ) * (chiC3 (HW u - HW v)
            + chiC3 (-(HW u - HW v))) := by ring
  have h2 : (((1 / 8) * reChi3 (HW u - HW v) : ℚ) : ℂ)
      = (1 / 16 : ℂ) * (chiC3 (HW u - HW v) + chiC3 (-(HW u - HW v))) := by
    rw [show (((1 / 8) * reChi3 (HW u - HW v) : ℚ) : ℂ)
        = (1 / 8 : ℂ) * ((reChi3 (HW u - HW v) : ℚ) : ℂ) by push_cast; ring,
      reChi3_cast]
    ring
  exact Rat.cast_injective (key.trans h2.symm)

end B5ChainFace

section B5Doubled

/-- The signed character product over a subset `S`:
`prod_split_gen` with ambient set `S`. -/
theorem prod_split_genS (W : Fin 4 → ZMod 3) (S t : Finset (Fin 4))
    (ht : t ⊆ S) :
    (∏ i ∈ t, chiC3 (W i)) * (∏ i ∈ S \ t, chiC3 (-W i))
      = chiC3 (∑ i ∈ S, sgnT t i * W i) := by
  have hsum : (∑ i ∈ t, W i) + (∑ i ∈ S \ t, -W i)
      = ∑ i ∈ S, sgnT t i * W i := by
    have hA : ∑ i ∈ S, (if i ∈ t then W i else 0) = ∑ i ∈ t, W i := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.mpr ht]
    have hB : ∑ i ∈ S, (if i ∈ t then (0 : ZMod 3) else -W i)
        = ∑ i ∈ S \ t, -W i := by
      have e1 : (S.filter (fun i => i ∉ t)) = S \ t := by
        ext i
        simp [Finset.mem_sdiff, Finset.mem_filter]
      rw [← e1, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ t <;> simp [hi]
    rw [← hA, ← hB, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [sgnT_mul]
    by_cases hii : i ∈ t <;> simp [hii]
  rw [← chiC3_sum_prod t W, ← chiC3_sum_prod (S \ t) (fun i => -W i),
    ← chiC3_add]
  exact congrArg chiC3 hsum

/-- The three-factor real-character product over a
3-subset expands over its sign patterns. -/
theorem prod3_expand_gen (W : Fin 4 → ZMod 3) (S : Finset (Fin 4))
    (hS : S.card = 3) :
    ∏ i ∈ S, ((reChi3 (W i) : ℚ) : ℂ)
      = (1 / 8) * ∑ t ∈ S.powerset, chiC3 (∑ i ∈ S, sgnT t i * W i) := by
  calc ∏ i ∈ S, ((reChi3 (W i) : ℚ) : ℂ)
      = ∏ i ∈ S, ((chiC3 (W i) + chiC3 (-W i)) / 2) :=
        Finset.prod_congr rfl (fun i _ => reChi3_cast _)
    _ = (∏ i ∈ S, (chiC3 (W i) + chiC3 (-W i))) / 8 := by
        rw [Finset.prod_div_distrib, Finset.prod_const, hS]
        norm_num
    _ = (1 / 8) * ∑ t ∈ S.powerset,
          (∏ i ∈ t, chiC3 (W i)) * ∏ i ∈ S \ t, chiC3 (-W i) := by
        rw [Finset.prod_add]
        ring
    _ = (1 / 8) * ∑ t ∈ S.powerset, chiC3 (∑ i ∈ S, sgnT t i * W i) := by
        congr 1
        refine Finset.sum_congr rfl (fun t ht => ?_)
        exact prod_split_genS W S t (Finset.mem_powerset.mp ht)

/-- The `sPat k t` signed sum is the erase-signed sum:
the doubled column's sign is switched off. -/
theorem sum_sPat (k : Fin 4) (t : Finset (Fin 4)) (F : Fin 4 → ZMod 3) :
    ∑ i, sPat k t i * F i = ∑ i ∈ univ.erase k, sgnT t i * F i := by
  have h := Finset.add_sum_erase univ (fun i => sPat k t i * F i)
    (Finset.mem_univ k)
  rw [sPat_self, zero_mul, zero_add] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [sPat_of_ne t (Finset.mem_erase.mp hi).1]

/-- **Three-factor vanishing, plaquette.**  The α-average
of any three of the four plaquette factors is zero: in
every signed expansion some stratum variable survives
with coefficient `±1` (the private site), and the
character average over it vanishes. -/
theorem T3_eq_zero (k : Fin 4) (u v : Fin 4 → ZMod 3) :
    (1 / 81 : ℚ) * ∑ α, ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)
      = 0 := by
  have hS : (univ.erase k).card = 3 := by
    simp [Finset.card_erase_of_mem (Finset.mem_univ k)]
  have hterm : ∀ t : Finset (Fin 4),
      ∑ α, chiC3 (∑ i ∈ univ.erase k, sgnT t i * wordC3 α u v i)
        = 0 := by
    intro t
    have e : ∀ α : Fin 4 → ZMod 3,
        chiC3 (∑ i ∈ univ.erase k, sgnT t i * wordC3 α u v i)
          = chiC3 (∑ x, cGen (sPat k t) x * α x
              + ∑ i, sPat k t i * (v i - u i)) := by
      intro α
      rw [← sum_sPat, wordC3_sum_gen]
    rw [Finset.sum_congr rfl (fun α _ => e α), alpha_sum]
    obtain ⟨x, hx⟩ := cGen_sPat_ne k t
    rw [if_neg (fun h => hx (h x))]
  have key : (((1 / 81 : ℚ)
      * ∑ α, ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i) : ℚ) : ℂ)
      = 0 := by
    calc (((1 / 81 : ℚ)
        * ∑ α, ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i) : ℚ) : ℂ)
        = (1 / 81) * ∑ α, ∏ i ∈ univ.erase k,
            ((reChi3 (wordC3 α u v i) : ℚ) : ℂ) := by
          push_cast
          ring
      _ = (1 / 81) * ∑ α, ((1 / 8) * ∑ t ∈ (univ.erase k).powerset,
            chiC3 (∑ i ∈ univ.erase k, sgnT t i * wordC3 α u v i)) := by
          congr 1
          refine Finset.sum_congr rfl (fun α _ => ?_)
          exact prod3_expand_gen (wordC3 α u v) (univ.erase k) hS
      _ = (1 / 81) * ((1 / 8) * ∑ α, ∑ t ∈ (univ.erase k).powerset,
            chiC3 (∑ i ∈ univ.erase k,
              sgnT t i * wordC3 α u v i)) := by
          congr 1
          rw [Finset.mul_sum]
      _ = (1 / 81) * ((1 / 8) * ∑ t ∈ (univ.erase k).powerset,
            ∑ α, chiC3 (∑ i ∈ univ.erase k,
              sgnT t i * wordC3 α u v i)) := by
          congr 1
          rw [Finset.sum_comm]
      _ = (1 / 81) * ((1 / 8) * ∑ t ∈ (univ.erase k).powerset, 0) := by
          congr 1; congr 1
          refine Finset.sum_congr rfl (fun t _ => hterm t)
      _ = 0 := by simp
  have h0 : (((1 / 81 : ℚ)
      * ∑ α, ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i) : ℚ) : ℂ)
      = ((0 : ℚ) : ℂ) := by
    rw [key]; simp
  exact Rat.cast_injective h0

/-- **Three-factor vanishing, wrap chain.**  Same
statement for the chain words. -/
theorem TW3_eq_zero (k : Fin 4) (u v : Fin 4 → ZMod 3) :
    (1 / 81 : ℚ) * ∑ α, ∏ i ∈ univ.erase k, reChi3 (wordW α u v i)
      = 0 := by
  have hS : (univ.erase k).card = 3 := by
    simp [Finset.card_erase_of_mem (Finset.mem_univ k)]
  have hterm : ∀ t : Finset (Fin 4),
      ∑ α, chiC3 (∑ i ∈ univ.erase k, sgnT t i * wordW α u v i)
        = 0 := by
    intro t
    have e : ∀ α : Fin 4 → ZMod 3,
        chiC3 (∑ i ∈ univ.erase k, sgnT t i * wordW α u v i)
          = chiC3 (∑ x, cGenW (sPat k t) x * α x
              + ∑ i, sPat k t i * (v i - u i)) := by
      intro α
      rw [← sum_sPat, wordW_sum_gen]
    rw [Finset.sum_congr rfl (fun α _ => e α), alpha_sum]
    obtain ⟨x, hx⟩ := cGenW_sPat_ne k t
    rw [if_neg (fun h => hx (h x))]
  have key : (((1 / 81 : ℚ)
      * ∑ α, ∏ i ∈ univ.erase k, reChi3 (wordW α u v i) : ℚ) : ℂ)
      = 0 := by
    calc (((1 / 81 : ℚ)
        * ∑ α, ∏ i ∈ univ.erase k, reChi3 (wordW α u v i) : ℚ) : ℂ)
        = (1 / 81) * ∑ α, ∏ i ∈ univ.erase k,
            ((reChi3 (wordW α u v i) : ℚ) : ℂ) := by
          push_cast
          ring
      _ = (1 / 81) * ∑ α, ((1 / 8) * ∑ t ∈ (univ.erase k).powerset,
            chiC3 (∑ i ∈ univ.erase k, sgnT t i * wordW α u v i)) := by
          congr 1
          refine Finset.sum_congr rfl (fun α _ => ?_)
          exact prod3_expand_gen (wordW α u v) (univ.erase k) hS
      _ = (1 / 81) * ((1 / 8) * ∑ α, ∑ t ∈ (univ.erase k).powerset,
            chiC3 (∑ i ∈ univ.erase k,
              sgnT t i * wordW α u v i)) := by
          congr 1
          rw [Finset.mul_sum]
      _ = (1 / 81) * ((1 / 8) * ∑ t ∈ (univ.erase k).powerset,
            ∑ α, chiC3 (∑ i ∈ univ.erase k,
              sgnT t i * wordW α u v i)) := by
          congr 1
          rw [Finset.sum_comm]
      _ = (1 / 81) * ((1 / 8) * ∑ t ∈ (univ.erase k).powerset, 0) := by
          congr 1; congr 1
          refine Finset.sum_congr rfl (fun t _ => hterm t)
      _ = 0 := by simp
  have h0 : (((1 / 81 : ℚ)
      * ∑ α, ∏ i ∈ univ.erase k, reChi3 (wordW α u v i) : ℚ) : ℂ)
      = ((0 : ℚ) : ℂ) := by
    rw [key]; simp
  exact Rat.cast_injective h0

end B5Doubled

section B5DoubledId

/-- The per-chain **doubled** factor at (C₃, χ): the seat
avatar of `doubledQuadReMoment` at a wrap chain. -/
def GW3 (k : Fin 4) (u v : Fin 4 → ZMod 3) : ℚ :=
  (1 / 81) * ∑ α, (reChi3 (wordW α u v k)) ^ 2
    * ∏ i ∈ univ.erase k, reChi3 (wordW α u v i)

/-- **Doubled plaquette identification (T1).**  For every
doubled column `k`, the doubled plaquette factor is
exactly half the κ₄ factor:
`GD3 k u v = (1/16) · reChi(h(u) − h(v))`.  The proof is
the fold `reChi(w)² = (1 + reChi(w))/2`: the `1` part
averages three factors and vanishes (`T3_eq_zero`), the
`reChi(w)` part restores the full four-factor moment
(`FC3_eq`). -/
theorem GD3_eq (k : Fin 4) (u v : Fin 4 → ZMod 3) :
    GD3 k u v = (1 / 16) * reChi3 (hC3 u - hC3 v) := by
  have hpt : ∀ α : Fin 4 → ZMod 3,
      (reChi3 (wordC3 α u v k)) ^ 2
          * ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)
        = (1 / 2) * (∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)
            + ∏ i, reChi3 (wordC3 α u v i)) := by
    intro α
    rw [reChi3_sq]
    have hprod : ∏ i, reChi3 (wordC3 α u v i)
        = reChi3 (wordC3 α u v k)
          * ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i) :=
      (Finset.mul_prod_erase univ (fun i => reChi3 (wordC3 α u v i))
        (Finset.mem_univ k)).symm
    rw [hprod]
    ring
  have e1 : GD3 k u v
      = (1 / 81) * ∑ α, (1 / 2)
          * (∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)
            + ∏ i, reChi3 (wordC3 α u v i)) := by
    unfold GD3
    congr 1
    exact Finset.sum_congr rfl (fun α _ => hpt α)
  have e2 : (1 / 81 : ℚ)
        * ((1 / 2) * (∑ α, ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)
          + ∑ α, ∏ i, reChi3 (wordC3 α u v i)))
      = (1 / 2) * ((1 / 81)
          * ∑ α, ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)
          + (1 / 81) * ∑ α, ∏ i, reChi3 (wordC3 α u v i)) := by
    ring
  rw [e1, ← Finset.mul_sum, Finset.sum_add_distrib, e2, T3_eq_zero k u v,
    zero_add]
  show (1 / 2 : ℚ) * FC3 u v = (1 / 16) * reChi3 (hC3 u - hC3 v)
  rw [FC3_eq]
  ring

/-- **Doubled wrap-chain identification (T1).**  Same
fold, at the wrap chain: `GW3 k u v = (1/16) ·
reChi(H(u) − H(v))` for every doubled column. -/
theorem GW3_eq (k : Fin 4) (u v : Fin 4 → ZMod 3) :
    GW3 k u v = (1 / 16) * reChi3 (HW u - HW v) := by
  have hpt : ∀ α : Fin 4 → ZMod 3,
      (reChi3 (wordW α u v k)) ^ 2
          * ∏ i ∈ univ.erase k, reChi3 (wordW α u v i)
        = (1 / 2) * (∏ i ∈ univ.erase k, reChi3 (wordW α u v i)
            + ∏ i, reChi3 (wordW α u v i)) := by
    intro α
    rw [reChi3_sq]
    have hprod : ∏ i, reChi3 (wordW α u v i)
        = reChi3 (wordW α u v k)
          * ∏ i ∈ univ.erase k, reChi3 (wordW α u v i) :=
      (Finset.mul_prod_erase univ (fun i => reChi3 (wordW α u v i))
        (Finset.mem_univ k)).symm
    rw [hprod]
    ring
  have e1 : GW3 k u v
      = (1 / 81) * ∑ α, (1 / 2)
          * (∏ i ∈ univ.erase k, reChi3 (wordW α u v i)
            + ∏ i, reChi3 (wordW α u v i)) := by
    unfold GW3
    congr 1
    exact Finset.sum_congr rfl (fun α _ => hpt α)
  have e2 : (1 / 81 : ℚ)
        * ((1 / 2) * (∑ α, ∏ i ∈ univ.erase k, reChi3 (wordW α u v i)
          + ∑ α, ∏ i, reChi3 (wordW α u v i)))
      = (1 / 2) * ((1 / 81)
          * ∑ α, ∏ i ∈ univ.erase k, reChi3 (wordW α u v i)
          + (1 / 81) * ∑ α, ∏ i, reChi3 (wordW α u v i)) := by
    ring
  rw [e1, ← Finset.mul_sum, Finset.sum_add_distrib, e2, TW3_eq_zero k u v,
    zero_add]
  show (1 / 2 : ℚ) * FW u v = (1 / 16) * reChi3 (HW u - HW v)
  rw [FW_eq]
  ring

end B5DoubledId

section B5C3Verdict

/-- The per-plaquette channel total at (C₃, χ): summing
the four doubled columns, the channel kernel is
`(1/4) · reChi(h − h′)` — exactly **twice** the κ₄
plaquette kernel `(1/8) · reChi(h − h′)`. -/
theorem GD3_total (u v : Fin 4 → ZMod 3) :
    ∑ k, GD3 k u v = (1 / 4) * reChi3 (hC3 u - hC3 v) := by
  rw [Fin.sum_univ_four, GD3_eq, GD3_eq, GD3_eq, GD3_eq]
  ring

/-- The per-chain channel total at (C₃, χ): likewise
twice the κ₄ chain kernel. -/
theorem GW3_total (u v : Fin 4 → ZMod 3) :
    ∑ k, GW3 k u v = (1 / 4) * reChi3 (HW u - HW v) := by
  rw [Fin.sum_univ_four, GW3_eq, GW3_eq, GW3_eq, GW3_eq]
  ring

/-- Seat S1's per-quad channel kernel on holonomy
classes: `K₅(a, b) = (1/4) · reChi(a − b)`. -/
def K5C3 (a b : ZMod 3) : ℚ := (1 / 4) * reChi3 (a - b)

theorem K5C3_entry (a b : ZMod 3) :
    K5C3 a b = if a = b then 1 / 4 else -1 / 8 := by
  by_cases h : a = b
  · rw [if_pos h]; subst h; norm_num [K5C3, reChi3_zero]
  · rw [if_neg h]; simp only [K5C3, reChi3_sub, if_neg h]; norm_num

/-- `K₅ = (3/8) I − (1/8) J` on holonomy classes:
spectrum `{0, 3/8, 3/8}` — zero on constants, `3/8` on
both nontrivial character directions. -/
theorem K5C3_IJ (a b : ZMod 3) :
    K5C3 a b = (3 / 8) * (if a = b then 1 else 0) - 1 / 8 := by
  by_cases h : a = b
  · rw [K5C3_entry, if_pos h, if_pos h]; norm_num
  · rw [K5C3_entry, if_neg h, if_neg h]; norm_num

/-- The channel kernel's margins vanish exactly (the
dependent-part check). -/
theorem K5C3_margins (a : ZMod 3) : ∑ b, K5C3 a b = 0 := by
  have hite : ∑ b, (if a = b then (1 : ℚ) else 0) = 1 := by
    rw [Finset.sum_ite_eq]; simp
  rw [Finset.sum_congr rfl (fun b _ => K5C3_IJ a b), Finset.sum_sub_distrib,
    ← Finset.mul_sum, hite]
  simp [Finset.sum_const, Finset.card_univ]
  norm_num

/-- The channel form at S1 is `(1/8)` of the sum of
squared holonomy differences — a sum of squares,
positive semidefinite with the same kernel as κ₄'s
form. -/
theorem K5C3_form (φ : ZMod 3 → ℚ) :
    ∑ a, ∑ b, φ a * K5C3 a b * φ b
      = (1 / 8) * ((φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2
          + (φ 1 - φ 2) ^ 2) := by
  have e00 : K5C3 0 0 = 1 / 4 := by rw [K5C3_entry, if_pos rfl]
  have e01 : K5C3 0 1 = -1 / 8 := by rw [K5C3_entry, if_neg (by decide)]
  have e02 : K5C3 0 2 = -1 / 8 := by rw [K5C3_entry, if_neg (by decide)]
  have e10 : K5C3 1 0 = -1 / 8 := by rw [K5C3_entry, if_neg (by decide)]
  have e11 : K5C3 1 1 = 1 / 4 := by rw [K5C3_entry, if_pos rfl]
  have e12 : K5C3 1 2 = -1 / 8 := by rw [K5C3_entry, if_neg (by decide)]
  have e20 : K5C3 2 0 = -1 / 8 := by rw [K5C3_entry, if_neg (by decide)]
  have e21 : K5C3 2 1 = -1 / 8 := by rw [K5C3_entry, if_neg (by decide)]
  have e22 : K5C3 2 2 = 1 / 4 := by rw [K5C3_entry, if_pos rfl]
  rw [sum_zmod3 (fun a => ∑ b, φ a * K5C3 a b * φ b),
    sum_zmod3 (fun b => φ 0 * K5C3 0 b * φ b),
    sum_zmod3 (fun b => φ 1 * K5C3 1 b * φ b),
    sum_zmod3 (fun b => φ 2 * K5C3 2 b * φ b),
    e00, e01, e02, e10, e11, e12, e20, e21, e22]
  ring

theorem K5C3_form_nonneg (φ : ZMod 3 → ℚ) :
    0 ≤ ∑ a, ∑ b, φ a * K5C3 a b * φ b := by
  rw [K5C3_form]
  apply mul_nonneg (by norm_num)
  exact add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)

/-- Seat S1's κ₄ form in class coordinates (the probe's
`PhiC3`): `(1/16)` of the same sum of squares. -/
theorem PhiC3_form_class (φ : ZMod 3 → ℚ) :
    ∑ a, ∑ b, φ a * PhiC3 a b * φ b
      = (1 / 16) * ((φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2
          + (φ 1 - φ 2) ^ 2) := by
  have e00 : PhiC3 0 0 = 1 / 8 := by rw [PhiC3_eq, if_pos rfl]
  have e01 : PhiC3 0 1 = -1 / 16 := by rw [PhiC3_eq, if_neg (by decide)]
  have e02 : PhiC3 0 2 = -1 / 16 := by rw [PhiC3_eq, if_neg (by decide)]
  have e10 : PhiC3 1 0 = -1 / 16 := by rw [PhiC3_eq, if_neg (by decide)]
  have e11 : PhiC3 1 1 = 1 / 8 := by rw [PhiC3_eq, if_pos rfl]
  have e12 : PhiC3 1 2 = -1 / 16 := by rw [PhiC3_eq, if_neg (by decide)]
  have e20 : PhiC3 2 0 = -1 / 16 := by rw [PhiC3_eq, if_neg (by decide)]
  have e21 : PhiC3 2 1 = -1 / 16 := by rw [PhiC3_eq, if_neg (by decide)]
  have e22 : PhiC3 2 2 = 1 / 8 := by rw [PhiC3_eq, if_pos rfl]
  rw [sum_zmod3 (fun a => ∑ b, φ a * PhiC3 a b * φ b),
    sum_zmod3 (fun b => φ 0 * PhiC3 0 b * φ b),
    sum_zmod3 (fun b => φ 1 * PhiC3 1 b * φ b),
    sum_zmod3 (fun b => φ 2 * PhiC3 2 b * φ b),
    e00, e01, e02, e10, e11, e12, e20, e21, e22]
  ring

/-- The kernel of S1's κ₄ form is exactly the constant
profiles. -/
theorem kappa4C3_form_eq_zero_iff (φ : ZMod 3 → ℚ) :
    (∑ a, ∑ b, φ a * PhiC3 a b * φ b) = 0
      ↔ φ 0 = φ 1 ∧ φ 1 = φ 2 := by
  rw [PhiC3_form_class]
  constructor
  · intro h
    have hS : (φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2 + (φ 1 - φ 2) ^ 2
        = 0 := by linarith
    have h1 : (φ 0 - φ 1) ^ 2 = 0 := by
      have g1 : 0 ≤ (φ 0 - φ 1) ^ 2 := sq_nonneg _
      have g2 : 0 ≤ (φ 0 - φ 2) ^ 2 := sq_nonneg _
      have g3 : 0 ≤ (φ 1 - φ 2) ^ 2 := sq_nonneg _
      linarith
    have h2 : (φ 1 - φ 2) ^ 2 = 0 := by
      have g1 : 0 ≤ (φ 0 - φ 1) ^ 2 := sq_nonneg _
      have g2 : 0 ≤ (φ 0 - φ 2) ^ 2 := sq_nonneg _
      have g3 : 0 ≤ (φ 1 - φ 2) ^ 2 := sq_nonneg _
      linarith
    refine ⟨sub_eq_zero.mp
      ((pow_eq_zero_iff (show (2 : ℕ) ≠ 0 by norm_num)).mp h1),
      sub_eq_zero.mp
      ((pow_eq_zero_iff (show (2 : ℕ) ≠ 0 by norm_num)).mp h2)⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    simp

/-- **Joint verdict at (C₃, χ), N = 4 (K-K5 check).**
Every profile in the kernel of κ₄^dep's form evaluates
to **exactly 0** under the κ₅ channel form: the channel
form is twice the κ₄ form in class coordinates, so the
restriction to `ker κ₄` vanishes identically.  K-K5
does not fire at this seat; the joint kernel (constants)
is untouched at order 5, with margin exactly zero. -/
theorem verdict_C3 (φ : ZMod 3 → ℚ)
    (h4 : ∑ a, ∑ b, φ a * PhiC3 a b * φ b = 0) :
    ∑ a, ∑ b, φ a * K5C3 a b * φ b = 0 := by
  rw [PhiC3_form_class] at h4
  rw [K5C3_form]
  have hS : (φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2 + (φ 1 - φ 2) ^ 2
      = 0 := by linarith
  rw [hS]; norm_num

/-- The channel form in the probe's fiber coordinates:
the per-plaquette channel fiber form is twice the κ₄
fiber form (`FC3_form`), `(729/8)` of the difference
squares. -/
theorem chanC3_fiber_form (φ : ZMod 3 → ℚ) :
    ∑ u, ∑ v, φ (hC3 u) * (∑ k, GD3 k u v) * φ (hC3 v)
      = (729 / 8) * ((φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2
          + (φ 1 - φ 2) ^ 2) := by
  have e : ∀ u v : Fin 4 → ZMod 3,
      φ (hC3 u) * (∑ k, GD3 k u v) * φ (hC3 v)
        = 2 * (φ (hC3 u) * FC3 u v * φ (hC3 v)) := by
    intro u v
    rw [GD3_total, FC3_eq]
    ring
  calc ∑ u, ∑ v, φ (hC3 u) * (∑ k, GD3 k u v) * φ (hC3 v)
      = ∑ u, ∑ v, 2 * (φ (hC3 u) * FC3 u v * φ (hC3 v)) :=
        Finset.sum_congr rfl (fun u _ =>
          Finset.sum_congr rfl (fun v _ => e u v))
    _ = 2 * ∑ u, ∑ v, φ (hC3 u) * FC3 u v * φ (hC3 v) := by
        simp only [Finset.mul_sum]
    _ = (729 / 8) * ((φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2
          + (φ 1 - φ 2) ^ 2) := by
        rw [FC3_form]
        ring

end B5C3Verdict

section B5S3Verdict

/-- Seat S2's per-quad κ₄ kernel in the `colRe`
convention (this is `16 × PhiS3`: the factor `d⁴ = 16`
between the density convention of SBP-1 and the
unnormalised column-character convention of B5-1,
calibrated externally before this build).  Computed
here from `kappa5chan2111`'s per-term factors — every
doubled factor at both quad types equals this kernel
divided by 4, i.e. the per-term evaluation of the
channel's stratum integrals at this seat. -/
def K4S3 : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![1 / 4, 0, -1 / 8], ![0, 0, 0], ![-1 / 8, 0, 1 / 16]]

/-- The rank-one vector of S2's per-quad kernel:
`K₄ = w′ w′ᵀ` with `w′ = (1/2, 0, −1/4)`. -/
def w4S3 : Fin 3 → ℚ := ![1 / 2, 0, -1 / 4]

/-- S2's κ₄ form matrix in class coordinates,
two-sided fiber weighting as in the κ₄ probe:
`D₄ = diag(n) K₄ diag(n)`. -/
def D4S3 : Matrix (Fin 3) (Fin 3) ℚ :=
  fun a b => nS3 a * K4S3 a b * nS3 b

/-- Seat S2's per-quad **channel** kernel: the sum of
the four doubled factors of `kappa5chan2111` at either
primitive quad type. -/
def K5S3 : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![1, 0, -1 / 2], ![0, 0, 0], ![-1 / 2, 0, 1 / 4]]

/-- The rank-one vector of S2's channel kernel:
`K₅ = w″ w″ᵀ` with `w″ = (1, 0, −1/2) = 2 w′`. -/
def w5S3 : Fin 3 → ℚ := ![1, 0, -1 / 2]

/-- S2's channel form matrix in class coordinates. -/
def D5S3 : Matrix (Fin 3) (Fin 3) ℚ :=
  fun a b => nS3 a * K5S3 a b * nS3 b

theorem K4S3_outer (a b : Fin 3) : K4S3 a b = w4S3 a * w4S3 b := by
  fin_cases a <;> fin_cases b <;> simp [K4S3, w4S3, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three] <;> norm_num

/-- The convention calibration, in the corpus:
`K₄ = 16 · Φ` entrywise. -/
theorem K4S3_calibration (a b : Fin 3) : K4S3 a b = 16 * PhiS3 a b := by
  fin_cases a <;> fin_cases b <;> simp [K4S3, PhiS3, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three] <;> norm_num

/-- At S2 the channel kernel is exactly **four times**
the κ₄ kernel, entrywise. -/
theorem K5S3_eq (a b : Fin 3) : K5S3 a b = 4 * K4S3 a b := by
  fin_cases a <;> fin_cases b <;> simp [K5S3, K4S3, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three] <;> norm_num

theorem K5S3_outer (a b : Fin 3) : K5S3 a b = w5S3 a * w5S3 b := by
  fin_cases a <;> fin_cases b <;> simp [K5S3, w5S3, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three] <;> norm_num

/-- The linear form of S2's κ₄ block:
`∑ φₐ nₐ w′ₐ = 108 (φ₀ − φ₂)`. -/
theorem linS3_k4 (φ : Fin 3 → ℚ) :
    (∑ a, φ a * nS3 a * w4S3 a) = 108 * (φ 0 - φ 2) := by
  rw [Fin.sum_univ_three]
  simp only [nS3, w4S3, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_fin_const]
  ring

/-- The linear form of S2's channel block:
`∑ φₐ nₐ w″ₐ = 216 (φ₀ − φ₂)`. -/
theorem linS3_k5 (φ : Fin 3 → ℚ) :
    (∑ a, φ a * nS3 a * w5S3 a) = 216 * (φ 0 - φ 2) := by
  rw [Fin.sum_univ_three]
  simp only [nS3, w5S3, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_fin_const]
  ring

/-- S2's κ₄ per-quad form is a perfect square (the
κ₄ probe's `formS3_face` pattern, at the N = 4
per-quad kernel). -/
theorem formS3_k4 (φ : Fin 3 → ℚ) :
    ∑ a, ∑ b, φ a * (nS3 a * K4S3 a b * nS3 b) * φ b
      = (∑ a, φ a * nS3 a * w4S3 a) ^ 2 := by
  rw [pow_two, Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [K4S3_outer]; ring

theorem formS3_k4_sq (φ : Fin 3 → ℚ) :
    ∑ a, ∑ b, φ a * (nS3 a * K4S3 a b * nS3 b) * φ b
      = (108 * (φ 0 - φ 2)) ^ 2 := by
  rw [formS3_k4, linS3_k4]

theorem formS3_k4_nonneg (φ : Fin 3 → ℚ) :
    0 ≤ ∑ a, ∑ b, φ a * (nS3 a * K4S3 a b * nS3 b) * φ b := by
  rw [formS3_k4]; exact sq_nonneg _

/-- S2's channel per-quad form is a perfect square. -/
theorem formS3_k5 (φ : Fin 3 → ℚ) :
    ∑ a, ∑ b, φ a * (nS3 a * K5S3 a b * nS3 b) * φ b
      = (∑ a, φ a * nS3 a * w5S3 a) ^ 2 := by
  rw [pow_two, Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [K5S3_outer]; ring

theorem formS3_k5_sq (φ : Fin 3 → ℚ) :
    ∑ a, ∑ b, φ a * (nS3 a * K5S3 a b * nS3 b) * φ b
      = (216 * (φ 0 - φ 2)) ^ 2 := by
  rw [formS3_k5, linS3_k5]

theorem formS3_k5_nonneg (φ : Fin 3 → ℚ) :
    0 ≤ ∑ a, ∑ b, φ a * (nS3 a * K5S3 a b * nS3 b) * φ b := by
  rw [formS3_k5]; exact sq_nonneg _

/-- S2 κ₄ kernel margins vanish exactly (the
dependent-part check). -/
theorem K4S3_margins (a : Fin 3) : ∑ b, nS3 b * K4S3 a b = 0 := by
  fin_cases a <;> rw [Fin.sum_univ_three] <;> simp [K4S3, nS3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- S2 channel kernel margins vanish exactly. -/
theorem K5S3_margins (a : Fin 3) : ∑ b, nS3 b * K5S3 a b = 0 := by
  fin_cases a <;> rw [Fin.sum_univ_three] <;> simp [K5S3, nS3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- Character-basis evaluation of S2's κ₄ form:
`Xᵀ D₄ X = diag(0, 0, 104976)` — only the std
direction is seen, eigenvalue `104976 = 324²`
(`= 16 ×` the density convention's `6561`). -/
theorem BS3_k4 :
    XS3t * D4S3 * XS3
      = ![![0, 0, 0], ![0, 0, 0], ![0, 0, 104976]] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    rw [Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three] <;>
    simp only [XS3, XS3t, D4S3, K4S3, nS3, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons] <;> norm_num

/-- Character-basis evaluation of S2's channel form:
`Xᵀ D₅ X = diag(0, 0, 419904)`, eigenvalue
`419904 = 648² = 4 × 104976`. -/
theorem BS3_k5 :
    XS3t * D5S3 * XS3
      = ![![0, 0, 0], ![0, 0, 0], ![0, 0, 419904]] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    rw [Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three] <;>
    simp only [XS3, XS3t, D5S3, K5S3, nS3, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons] <;> norm_num

/-- The kernel of S2's κ₄ per-quad form is exactly
`{φ₀ = φ₂}` — two-dimensional in class space (the
trivial and sign character directions). -/
theorem kappa4S3_form_eq_zero_iff (φ : Fin 3 → ℚ) :
    (∑ a, ∑ b, φ a * (nS3 a * K4S3 a b * nS3 b) * φ b) = 0
      ↔ φ 0 = φ 2 := by
  rw [formS3_k4_sq]
  constructor
  · intro h
    have h1 : (108 : ℚ) * (φ 0 - φ 2) = 0 :=
      (pow_eq_zero_iff (show (2 : ℕ) ≠ 0 by norm_num)).mp h
    have h2 : φ 0 - φ 2 = 0 := by linarith
    exact sub_eq_zero.mp h2
  · intro h
    rw [sub_eq_zero.mpr h]
    norm_num

/-- **Joint verdict at (S₃, std), N = 4 (K-K5 check).**
Every class profile in the kernel of κ₄^dep's per-quad
form evaluates to **exactly 0** under the κ₅ channel
form: both forms are squares of proportional linear
forms (`216 = 2 × 108`), so the restriction to
`ker κ₄ = {φ₀ = φ₂}` vanishes identically.  K-K5 does
not fire at this seat; the joint kernel is untouched
at order 5, with margin exactly zero. -/
theorem verdict_S3 (φ : Fin 3 → ℚ)
    (h4 : ∑ a, ∑ b, φ a * (nS3 a * K4S3 a b * nS3 b) * φ b = 0) :
    ∑ a, ∑ b, φ a * (nS3 a * K5S3 a b * nS3 b) * φ b = 0 := by
  have h02 : φ 0 = φ 2 := (kappa4S3_form_eq_zero_iff φ).mp h4
  rw [formS3_k5_sq, sub_eq_zero.mpr h02]
  norm_num

end B5S3Verdict

end ThetLogos
