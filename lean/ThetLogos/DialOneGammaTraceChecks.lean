import Mathlib.Tactic
import ThetLogos.DialOneGammaTracePin

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.DialOneGammaTracePin

namespace ThetLogos.DialOneGammaTraceChecks

/-!
# ThetLogos.DialOneGammaTraceChecks — D1-C3: the pre-check gauntlet

Governing text: the escape scoping dossier §4.3
(`routeb-general-scratch/scoping-d1-escape-2026-11-01.md`) and
the pin module `ThetLogos.DialOneGammaTracePin`, which pinned
the γ_F-trace condition `C3` and registered the two
pre-checks as the named Props `C3Pi1Check` / `C3PiFlipCheck`,
with kills K-ESC-4 (π₁ fails ⇒ mis-posed) and K-ESC-5 (piFlip
passes ⇒ no discrimination) armed against them.

## Verdicts (both pre-checks PASS; neither kill fires)

* **Pre-check (i): `C3 pi1` HOLDS.** The γ-weighted trace sums
  over the landed `pi1AVal`/`pi1BVal` tables are
  `(α-coefficient, β-coefficient) = (0, 0)`: the integer sums
  `∑ᵢ γᵢ·Aᵢ = 0` and `∑ᵢ γᵢ·Bᵢ = 0` are discharged by
  `decide` over the `Fin 32` tables (ℤ shadows, per the house
  rule against kernel `decide` on Rat goals). K-ESC-4 does
  NOT fire.
* **Pre-check (ii): `¬ C3 piFlip` HOLDS.** piFlip differs
  from π₁ only at seat 8 (the landed `Matrix.single`
  perturbation), `gammaF s8 s8 = -1`, and the perturbation's
  value at `u1Gen α β` is `star (α·i) - α·i = -2α·i`; the
  trace at piFlip is therefore exactly
  `Tr (γ_F · piFlip (u1Gen α β)) = 2α·i`, which at
  `(α, β) = (1, 0)` is `2·i ≠ 0`. K-ESC-5 does NOT fire.

## The exclusion corollary (this entry's whole positive content)

The strengthened set `DialOneBase ∧ C3`
(`DialOneStrengthenedC3`) holds for π₁ and **excludes
piFlip** — the first Dial-1 condition set to do so. Stated
at exactly that rank, no higher: NO forcing is attempted
(K-ESC-6, pre-registered in the pin, stands armed against
any forcing claim at base + C3).

**NO CLAIM. Dial 1 = 0; all dials 0/4.**
-/

/-! ## The γ_F sign table, as an integer shadow -/

/-- The diagonal sign of `gammaF` at seat value `v`, as an
integer: `+1` on `H_L` and `H_R^c`, `-1` on `H_R` and
`H_L^c` — the landed grading `diag(+I₈, −I₈, −I₈, +I₈)`. -/
def gammaVal (v : ℕ) : ℤ :=
  if v < 8 then 1
  else if v < 16 then -1
  else if v < 24 then -1
  else 1

/-- Read-back: `gammaF`'s diagonal is the cast of `gammaVal`,
seat by seat (32-case exhaustion over the landed tables). -/
theorem gammaF_diag_eq (i : Fin 32) :
    gammaF i i = (gammaVal i.val : ℂ) := by
  obtain ⟨v, hv⟩ := i
  interval_cases v <;> simp [gammaF, gammaVal]

/-! ## Trace of a γ_F-weighted matrix, reduced to its diagonal -/

/-- `gammaF` is diagonal, so the trace of `gammaF * M` is the
γ-weighted sum of `M`'s diagonal entries. -/
theorem trace_gammaF_mul (M : Matrix (Fin 32) (Fin 32) ℂ) :
    Matrix.trace (gammaF * M) = ∑ i : Fin 32, gammaF i i * M i i := by
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro k _ hk
    rw [gammaF_apply_ne hk.symm, zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-! ## Pre-check (i): the π₁ diagonal at the generator, and the sums -/

/-- **The diagonal of `π₁ (u1Gen α β)`**, seat by seat: at
seat `i` it is `i · (Aᵢ·α + Bᵢ·β)` for the landed
`pi1AVal`/`pi1BVal` tables. (At the `H_L` seats both tables
vanish and the ℍ-component of `u1Gen` is `0`, so the entry
is `0` there.) Proved by 32-case exhaustion over the landed
entry definition. -/
theorem pi1_diag_u1Gen (α β : ℤ) (i : Fin 32) :
    pi1 (u1Gen α β) i i
      = Complex.I * ((pi1AVal i.val * α + pi1BVal i.val * β : ℤ) : ℂ) := by
  obtain ⟨v, hv⟩ := i
  interval_cases v <;>
    simp [pi1, u1Gen, pi1AVal, pi1BVal] <;> ring

/-- The γ-weighted α-coefficient sum over the 32 seats is
`0` (dossier §4.3: seats 8; 9; 10–15 alternating; 16–17;
24–25). ℤ shadow, discharged by `decide`. -/
theorem gamma_weighted_sum_A :
    ∑ i : Fin 32, gammaVal i.val * pi1AVal i.val = 0 := by decide

/-- The γ-weighted β-coefficient sum over the 32 seats is
`0` (dossier §4.3: seats 18–23 contribute `+6`, seats 26–31
contribute `−6`). ℤ shadow, discharged by `decide`. -/
theorem gamma_weighted_sum_B :
    ∑ i : Fin 32, gammaVal i.val * pi1BVal i.val = 0 := by decide

/-- **The γ-weighted trace of π₁ at the generator is `0`**,
for every direction `(α, β)`: the trace is
`i · ((∑ γ·A)·α + (∑ γ·B)·β) = i · (0·α + 0·β)`. -/
theorem trace_gammaF_pi1_u1Gen (α β : ℤ) :
    Matrix.trace (gammaF * pi1 (u1Gen α β)) = 0 := by
  rw [trace_gammaF_mul]
  have hterm : ∀ i : Fin 32, gammaF i i * pi1 (u1Gen α β) i i
      = Complex.I
        * ((gammaVal i.val * (pi1AVal i.val * α + pi1BVal i.val * β) : ℤ) : ℂ) := by
    intro i
    rw [gammaF_diag_eq, pi1_diag_u1Gen]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum,
    ← Int.cast_sum]
  have hsum : ∑ i : Fin 32,
        gammaVal i.val * (pi1AVal i.val * α + pi1BVal i.val * β) = 0 := by
    have h1 : ∀ i : Fin 32, gammaVal i.val * (pi1AVal i.val * α + pi1BVal i.val * β)
        = (gammaVal i.val * pi1AVal i.val) * α
          + (gammaVal i.val * pi1BVal i.val) * β := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, gamma_weighted_sum_A,
      gamma_weighted_sum_B]
    simp
  rw [hsum]
  simp

/-- **Pre-check (i) — `C3Pi1Check` HOLDS**: `C3 pi1`, the
γ_F-trace condition at the corpus's one landed model.
K-ESC-4 does NOT fire. -/
theorem c3_pi1_holds : C3Pi1Check :=
  fun α β => trace_gammaF_pi1_u1Gen α β

/-! ## Pre-check (ii): the piFlip perturbation's trace -/

/-- The γ-weighted trace of the seat-8 perturbation:
`gammaF s8 s8 = -1` picks out exactly the `single` entry. -/
theorem trace_gammaF_single_s8 (c : ℂ) :
    Matrix.trace (gammaF
      * Matrix.single ThetLogos.HyperchargeForcing.s8
          ThetLogos.HyperchargeForcing.s8 c) = -c := by
  rw [trace_gammaF_mul]
  have h8 : gammaF ThetLogos.HyperchargeForcing.s8
      ThetLogos.HyperchargeForcing.s8 = -1 := by
    unfold gammaF
    simp [ThetLogos.HyperchargeForcing.s8]
  rw [Finset.sum_eq_single ThetLogos.HyperchargeForcing.s8]
  · rw [h8]
    simp
  · intro i _ hi
    have hne : ¬ (ThetLogos.HyperchargeForcing.s8 = i
        ∧ ThetLogos.HyperchargeForcing.s8 = i) :=
      fun h => hi h.1.symm
    have hsingle : Matrix.single ThetLogos.HyperchargeForcing.s8
        ThetLogos.HyperchargeForcing.s8 c i i = 0 := by
      simp only [Matrix.single_apply, hne, ite_false]
    rw [hsingle, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- **The γ-weighted trace of piFlip at the generator is
exactly `2α·i`**: the π₁ trace (`0`, pre-check (i)) plus the
perturbation's contribution `(−1)·(−iα − iα) = +2iα`. -/
theorem trace_gammaF_piFlip_u1Gen (α β : ℤ) :
    Matrix.trace (gammaF * ThetLogos.HyperchargeForcing.piFlip (u1Gen α β))
      = 2 * (α : ℂ) * Complex.I := by
  have hu1 : (u1Gen α β).u1 = (α : ℂ) * Complex.I := rfl
  have hstar : star (u1Gen α β).u1 = -((α : ℂ) * Complex.I) := by
    rw [hu1]
    simp
  unfold ThetLogos.HyperchargeForcing.piFlip
  rw [mul_add, Matrix.trace_add, trace_gammaF_pi1_u1Gen,
    trace_gammaF_single_s8, hstar, hu1]
  ring

/-- **Pre-check (ii) — `C3PiFlipCheck` HOLDS**: `¬ C3 piFlip`,
witnessed at `(α, β) = (1, 0)`, where the trace is
`2·i ≠ 0`. K-ESC-5 does NOT fire. -/
theorem c3_piFlip_fails : C3PiFlipCheck := by
  intro hC
  have h := hC 1 0
  rw [trace_gammaF_piFlip_u1Gen] at h
  simp only [Int.cast_one, mul_one] at h
  have hI : (2 : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by norm_num) Complex.I_ne_zero
  exact hI h

/-! ## The exclusion corollary -/

/-- **`DialOneBase pi1`**: π₁ satisfies the landed D1-A base
set, assembled clause by clause from π₁'s landed theorems
(`pi1_afMul`, `pi1_afAdd`, `pi1_afStar`, `pi1_one`,
`pi1_zero`, `pi1_injective`, `pi1_grading_even`,
`pi1_order_zero`, `pi1_first_order`), with the primitive
unimodular direction `(3, -1)` (`pi1_det_gen`). -/
theorem dialOneBase_pi1 :
    ThetLogos.DialOneSeatTiePin.DialOneBase pi1 :=
  ⟨pi1_afMul,
   pi1_afAdd,
   pi1_afStar,
   pi1_one,
   pi1_zero,
   pi1_injective,
   pi1_grading_even,
   fun a b => pi1_order_zero a b,
   fun Ynu Ye Yu Yd a b i j => pi1_first_order Ynu Ye Yu Yd a b i j,
   ⟨3, -1, by norm_num, fun t => by
     rw [pi1_det_gen]
     norm_num⟩⟩

/-- **The strengthened set holds for π₁**:
`DialOneStrengthenedC3 pi1` (base ∧ C3). -/
theorem dialOneStrengthenedC3_pi1 :
    DialOneStrengthenedC3 pi1 :=
  (dialOneStrengthenedC3_unfold pi1).mpr ⟨dialOneBase_pi1, c3_pi1_holds⟩

/-- **The strengthened set EXCLUDES piFlip**:
`¬ DialOneStrengthenedC3 piFlip` — piFlip satisfies the
base set (landed, `DialOneSeatTieChecks.dialOneBase_piFlip`)
but fails `C3`. This exclusion is D1-C3's whole positive
content, stated at exactly that rank. -/
theorem dialOneStrengthenedC3_piFlip_excluded :
    ¬ DialOneStrengthenedC3 ThetLogos.HyperchargeForcing.piFlip :=
  fun h => c3_piFlip_fails
    ((dialOneStrengthenedC3_unfold _).mp h).2

end ThetLogos.DialOneGammaTraceChecks
