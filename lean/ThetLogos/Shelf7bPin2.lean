import ThetLogos.HfcDiscSharp

/-!
# SHELF-7b repair pin (7B-PIN-2) — interior presentations + the decision on the frozen B2/B3

Brick 7B-PIN-2 of the SHELF line (pack
`routeb-general-scratch/pack-7b-pin2.md`). Governing record:
GATE-B1 landed PARTIAL (`whitepaper/gateb1-landing-2026-11-02.md`):
B1a/B1b/B1d FULL; `Shelf7bB1ScalarEval` KILLED as frozen — the pin
presented coefficients at the boundary radius while
`DiscHolomorphic` constrains only the open ball — with the
counterexample in-tree (`discCoeff_boundary_counterexample`,
`shelf7bB1ScalarEval_not` in `ThetLogos.HfcDiscSharp`) and the
corrected interior form landed (`scalarEval_discCoeff_eq_of_lt`,
`scalarEval_discCoeff_eq_of_indep`). The frozen
`Shelf7bB2Forward` / `Shelf7bDisc` evaluate `hfcDisc` at the same
boundary presentation and stand under the same cloud.

## Part 1 — the repair pin (a NEW entry under the relabeling rule)

The frozen Props in `ThetLogos.Shelf7bPin` stand untouched beside
their verdicts. Frozen below are the B2/B3 targets re-stated
against an INTERIOR presenting radius `R₀` with
`(spectralRadius ℂ a).toReal < R₀ < R`. These are the chain's
live forms from here: GATE-B2′ (12–25) and GATE-B3′ (25–45, its
PARTIAL seam as registered for B3) are priced against them. The
interior quantification is the whole repair — at any interior
`R₀`, B1a makes the coefficients the honest ones and the
corrected B1c makes their scalar values `f`'s.

## Part 2 — the decision on the frozen forms

`Shelf7bB2Forward` as frozen is REFUTED in-tree
(`shelf7bB2Forward_not`), by GATE-B1's landed counterexample
witness at `a = 0`, and the frozen `Shelf7bDisc` falls with it by
contraposition (`shelf7bDisc_not`, via the one-step derivation
`shelf7bDisc_imp_forward`).

Face fence: 7b-disc is NOT 7b-in-full. NO CLAIM; dials 0/4.
-/

namespace ThetLogos

noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A]
  [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A]

/-! ## Part 1 — the re-frozen targets (pin content) -/

/-- B2′ (live form): forward inclusion at the sharp scale, with
the coefficients presented at an interior radius `R₀`. -/
def Shelf7bB2ForwardInterior (a : A) (f : ℂ → ℂ) (R : ℝ) : Prop :=
  DiscHolomorphic f R → (spectralRadius ℂ a).toReal < R →
    ∀ R₀ : ℝ, (spectralRadius ℂ a).toReal < R₀ → R₀ < R →
      ∀ lam ∈ spectrum ℂ a, f lam ∈ spectrum ℂ (hfcDisc a (discCoeff f R₀))

/-- B3′ (live form): the disc spectral mapping equality, with
the coefficients presented at an interior radius `R₀`. -/
def Shelf7bDiscInterior (a : A) (f : ℂ → ℂ) (R : ℝ) : Prop :=
  DiscHolomorphic f R → (spectralRadius ℂ a).toReal < R →
    ∀ R₀ : ℝ, (spectralRadius ℂ a).toReal < R₀ → R₀ < R →
      spectrum ℂ (hfcDisc a (discCoeff f R₀)) = f '' spectrum ℂ a

/-! ## Part 2 — the decision on the frozen forms -/

/-- GATE-B1's boundary counterexample is holomorphic on the open
unit disc: it is identically `0` there (the `1` values live only
on the circle `‖z‖ = 1`). -/
theorem discHolomorphic_boundary_counterexample :
    DiscHolomorphic (fun z : ℂ => if ‖z‖ = 1 then (1 : ℂ) else 0) 1 := by
  refine ⟨one_pos, ?_⟩
  refine (differentiableOn_const (0 : ℂ)).congr (fun z hz => ?_)
  rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
  rw [show (if ‖z‖ = 1 then (1 : ℂ) else 0) = 0 by simp [ne_of_lt hz]]

/-- `0` lies in the spectrum of `0`. -/
theorem zero_mem_spectrum_zero : (0 : ℂ) ∈ spectrum ℂ (0 : A) :=
  spectrum.zero_mem ℂ (by simp)

/-- `0` does not lie in the spectrum of `1`. -/
theorem zero_notMem_spectrum_one : (0 : ℂ) ∉ spectrum ℂ (1 : A) :=
  spectrum.zero_notMem ℂ isUnit_one

/-- The sharp-scale hypothesis at `a = 0`, `R = 1`: the spectral
radius of `0` is `0`. -/
theorem spectralRadius_zero_toReal_lt_one :
    (spectralRadius ℂ (0 : A)).toReal < 1 := by
  simp [spectrum.spectralRadius_zero]

/-- `hfcDisc` at `a = 0` reads only the constant coefficient:
every higher term carries a factor `(0 : A) ^ n = 0`. -/
theorem hfcDisc_at_zero (c : ℕ → ℂ) :
    hfcDisc (0 : A) c = c 0 • (1 : A) := by
  rw [hfcDisc, tsum_eq_single 0]
  · simp
  · intro n hn
    rw [zero_pow hn, smul_zero]

/-- KILL, at full rank: the frozen pin Prop `Shelf7bB2Forward`
is false as stated (boundary presentation of the coefficients),
by GATE-B1's witness at `a = 0`: `spectrum ℂ (0 : A)` contains
`0` and `f 0 = 0`, while `hfcDisc 0 (discCoeff f 1) = 1` — its
constant boundary coefficient is `discCoeff f 1 0 = 1`
(`discCoeff_boundary_counterexample`) and the higher terms
vanish at `0` — whose spectrum does not contain `0`. -/
theorem shelf7bB2Forward_not :
    ¬ Shelf7bB2Forward (0 : A)
      (fun z : ℂ => if ‖z‖ = 1 then (1 : ℂ) else 0) 1 := by
  intro h
  have hmem := h discHolomorphic_boundary_counterexample
    spectralRadius_zero_toReal_lt_one 0 zero_mem_spectrum_zero
  have hf0 : (fun z : ℂ => if ‖z‖ = 1 then (1 : ℂ) else 0) 0 = 0 := by simp
  rw [hf0, hfcDisc_at_zero, discCoeff_boundary_counterexample] at hmem
  simp only [one_smul] at hmem
  exact zero_notMem_spectrum_one hmem

/-- The one-step derivation: the frozen Disc equality implies
the frozen forward inclusion. -/
theorem shelf7bDisc_imp_forward (a : A) (f : ℂ → ℂ) (R : ℝ) :
    Shelf7bDisc a f R → Shelf7bB2Forward a f R := by
  intro hDisc hf hsr lam hlam
  rw [hDisc hf hsr]
  exact ⟨lam, hlam, rfl⟩

/-- KILL, at full rank: the frozen pin Prop `Shelf7bDisc` is
false as stated — it falls with the frozen forward inclusion by
contraposition through `shelf7bDisc_imp_forward`. -/
theorem shelf7bDisc_not :
    ¬ Shelf7bDisc (0 : A)
      (fun z : ℂ => if ‖z‖ = 1 then (1 : ℂ) else 0) 1 :=
  fun h => shelf7bB2Forward_not (shelf7bDisc_imp_forward _ _ _ h)

end

end ThetLogos
