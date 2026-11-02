import ThetLogos.Shelf7bPin2

/-!
# GATE-B2′ — forward spectral inclusion at interior presentations (SHELF-7b-disc, brick 2)

Brick GATE-B2′ of the SHELF line (pack
`routeb-general-scratch/pack-gate-b2.md`). Headline:
`Shelf7bB2ForwardInterior a f R` (the live target frozen in
7B-PIN-2) is DISCHARGED: for `DiscHolomorphic f R` and
`(spectralRadius ℂ a).toReal < R`, at every interior presenting
radius `R₀` and every `lam ∈ spectrum ℂ a`,
`f lam ∈ spectrum ℂ (hfcDisc a (discCoeff f R₀))`.

Route: `‖lam‖ < R₀` from the spectral-radius bound (step 1);
the scalar identity `scalarEval (discCoeff f R₀) lam = f lam`
from GATE-B1's corrected B1c (step 2, direct application);
sharp summability of the coefficient series and of the tail
series at `R₀` from GATE-B1's B1d transported by restriction
of holomorphicity from `R` to `R₀`, plus a Gelfand comparison
for the tail (step 3, transport); 8a's §8 coefficient-level
`(z − lam)` factorisation (`discConv_discFactor`,
`hfcDisc_discFactor`, direct applications) with its two
`hfcDisc` algebra steps (`hfcDisc_mul`, `hfcDisc_add`)
re-proved at the sharp scale from the summabilities of
step 3 in place of 8a's norm scale `‖a‖ < R` (step 4,
transport); the unit-contradiction conclusion in 8a's landed
argument shape (step 5).

The REFUTED frozen boundary forms (`Shelf7bB2Forward`,
`Shelf7bDisc`) are neither consumed nor cited as live here.

Face fence: 7b-disc is NOT 7b-in-full. NO CLAIM; dials 0/4.
-/

namespace ThetLogos

open Filter
open scoped NNReal ENNReal

noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A]
  [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A]

/-! ## Step 1 — the spectral-radius bound on spectral values -/

omit [Nontrivial A] in
/-- Every spectral value is bounded by the spectral radius:
`‖lam‖₊` is one term of the supremum defining
`spectralRadius ℂ a` (`spectralRadius_eq_of_unital`). -/
theorem norm_le_spectralRadius_toReal {a : A} {lam : ℂ}
    (hlam : lam ∈ spectrum ℂ a) :
    ‖lam‖ ≤ (spectralRadius ℂ a).toReal := by
  have hle : (‖lam‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ a := by
    rw [spectralRadius_eq_of_unital]
    exact le_iSup_of_le lam (le_iSup_of_le hlam le_rfl)
  have h := (ENNReal.toReal_le_toReal (by simp) (discSpectralRadius_ne_top a)).mpr hle
  simpa using h

/-- Step 1, interior form: a spectral value lies strictly
inside every interior presenting radius. -/
theorem norm_lt_of_mem_spectrum_of_spectralRadius_lt {a : A} {lam : ℂ}
    (hlam : lam ∈ spectrum ℂ a) {R₀ : ℝ}
    (hR₀ : (spectralRadius ℂ a).toReal < R₀) :
    ‖lam‖ < R₀ :=
  (norm_le_spectralRadius_toReal hlam).trans_lt hR₀

/-! ## Step 3 (preparation) — restriction of holomorphicity -/

/-- Holomorphicity on the disc of radius `R` restricts to
every smaller disc. -/
theorem discHolomorphic_of_lt {f : ℂ → ℂ} {R R₀ : ℝ}
    (hf : DiscHolomorphic f R) (hR₀ : 0 < R₀) (h : R₀ < R) :
    DiscHolomorphic f R₀ :=
  ⟨hR₀, hf.2.mono (Metric.ball_subset_ball h.le)⟩

/-- Interior DiscSummable: B1b (`discSummable_discCoeff`)
at the interior presenting radius `R₀`, by restriction. -/
theorem discSummable_discCoeff_interior {f : ℂ → ℂ} {R R₀ S : ℝ}
    (hf : DiscHolomorphic f R) (hR₀R : R₀ < R)
    (hS : 0 ≤ S) (hSR₀ : S < R₀) :
    DiscSummable S (discCoeff f R₀) :=
  discSummable_discCoeff
    (discHolomorphic_of_lt hf (hS.trans_lt hSR₀) hR₀R) hS hSR₀

/-- Sharp summability of the interior-presented coefficient
series: B1d (`summable_smul_pow_of_spectralRadius_lt`)
transported to the interior radius `R₀` by restriction. -/
theorem summable_norm_smul_pow_discCoeff_interior (a : A)
    {f : ℂ → ℂ} {R R₀ : ℝ}
    (hf : DiscHolomorphic f R) (hR₀R : R₀ < R)
    (hsr₀ : (spectralRadius ℂ a).toReal < R₀) :
    Summable fun n => ‖discCoeff f R₀ n • a ^ n‖ :=
  summable_smul_pow_of_spectralRadius_lt
    (discHolomorphic_of_lt hf (ENNReal.toReal_nonneg.trans_lt hsr₀) hR₀R) a hsr₀

/-- Sharp summability of the tail series: the tail
coefficients are `DiscSummable` at an intermediate scale
`ρ` between the spectral radius and an interior scale `S`
(8a's `discSummable_discTail`), and Gelfand's comparison
(`eventually_norm_pow_le_of_discSpectralRadius_lt`, B1d's
ingredient) bounds `‖a ^ n‖` by `ρ ^ n` eventually. -/
theorem summable_norm_discTail_smul_pow (a : A)
    {f : ℂ → ℂ} {R R₀ : ℝ} {lam : ℂ}
    (hf : DiscHolomorphic f R) (hR₀R : R₀ < R)
    (hsr₀ : (spectralRadius ℂ a).toReal < R₀)
    (hlam : lam ∈ spectrum ℂ a) :
    Summable fun n => ‖discTail (discCoeff f R₀) lam n • a ^ n‖ := by
  obtain ⟨S, hsrS, hSR₀⟩ := exists_between hsr₀
  obtain ⟨ρ, hsrρ, hρS⟩ := exists_between hsrS
  have hS0 : 0 < S := ENNReal.toReal_nonneg.trans_lt hsrS
  have hρ0 : 0 ≤ ρ := ENNReal.toReal_nonneg.trans hsrρ.le
  have hcS : DiscSummable S (discCoeff f R₀) :=
    discSummable_discCoeff_interior hf hR₀R hS0.le hSR₀
  have hlamS : ‖lam‖ ≤ S := (norm_le_spectralRadius_toReal hlam).trans hsrS.le
  have hDiscρ : DiscSummable ρ (discTail (discCoeff f R₀) lam) :=
    discSummable_discTail hS0 hρ0 hρS hcS hlamS
  refine Summable.of_norm_bounded_eventually_nat hDiscρ ?_
  filter_upwards [eventually_norm_pow_le_of_discSpectralRadius_lt hsrρ]
    with n hn
  show ‖‖discTail (discCoeff f R₀) lam n • a ^ n‖‖
    ≤ ‖discTail (discCoeff f R₀) lam n‖ * ρ ^ n
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  calc ‖discTail (discCoeff f R₀) lam n • a ^ n‖
      ≤ ‖discTail (discCoeff f R₀) lam n‖ * ‖a ^ n‖ := norm_smul_le _ _
    _ ≤ ‖discTail (discCoeff f R₀) lam n‖ * ρ ^ n :=
        mul_le_mul_of_nonneg_left hn (norm_nonneg _)

/-! ## Step 4 — 8a's factorisation transported to the sharp scale -/

/-- Additivity of `hfcDisc` at the sharp scale: 8a's
`hfcDisc_add` with its norm-scale summabilities replaced by
the sharp ones (its proof uses nothing else). -/
theorem hfcDisc_add_of_summable {a : A} {c d : ℕ → ℂ}
    (hc : Summable fun n => c n • a ^ n)
    (hd : Summable fun n => d n • a ^ n) :
    hfcDisc a (fun n => c n + d n) = hfcDisc a c + hfcDisc a d := by
  have hs := hc.hasSum.add hd.hasSum
  show ∑' n, (c n + d n) • a ^ n = (∑' n, c n • a ^ n) + ∑' n, d n • a ^ n
  rw [← hs.tsum_eq]
  exact tsum_congr fun n => add_smul _ _ _

/-- The factor coefficients `discFactor lam` are supported
on `{0, 1}`, so their series converges at every element. -/
theorem summable_norm_discFactor_smul_pow (a : A) (lam : ℂ) :
    Summable fun n => ‖discFactor lam n • a ^ n‖ := by
  refine summable_of_ne_finset_zero (s := {0, 1}) (fun n hn => ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  simp [discFactor, hn.1, hn.2]

/-- Multiplication by the factor series at the sharp scale:
8a's `hfcDisc_mul` specialised to the finite factor
`discFactor lam`, with the norm-scale summability of the
second factor replaced by the sharp one (its proof, the
antidiagonal `tsum` product, uses nothing else). -/
theorem hfcDisc_mul_discFactor_of_summable {a : A} {g : ℕ → ℂ}
    (lam : ℂ) (hg : Summable fun n => ‖g n • a ^ n‖) :
    hfcDisc a (discConv (discFactor lam) g)
      = (a - lam • (1 : A)) * hfcDisc a g := by
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (f := fun n => discFactor lam n • a ^ n) (g := fun n => g n • a ^ n)
    (summable_norm_discFactor_smul_pow a lam) hg
  rw [← hfcDisc_discFactor (a := a) lam]
  show ∑' n, discConv (discFactor lam) g n • a ^ n
    = (∑' n, discFactor lam n • a ^ n) * ∑' n, g n • a ^ n
  rw [hprod]
  refine tsum_congr fun n => ?_
  rw [discConv, Finset.sum_smul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
  rw [← hsum, pow_add, smul_mul_assoc, mul_smul_comm, smul_smul]

/-- The factorisation at the sharp scale: 8a's
`hfcDisc_sub_scalarEval` with its norm-scale hypotheses
(`‖a‖ < R`, summability at `‖a‖`) replaced by the sharp
summabilities of the coefficient and tail series. The
coefficient-level identity is 8a's `discConv_discFactor`
(direct application). -/
theorem hfcDisc_sub_scalarEval_sharp {a : A} {c : ℕ → ℂ}
    {S : ℝ} (hS : 0 < S) (hc : DiscSummable S c)
    {lam : ℂ} (hlam : ‖lam‖ ≤ S)
    (hsum_c : Summable fun n => ‖c n • a ^ n‖)
    (hsum_tail : Summable fun n => ‖discTail c lam n • a ^ n‖) :
    hfcDisc a c - scalarEval c lam • (1 : A)
      = (a - lam • (1 : A)) * hfcDisc a (discTail c lam) := by
  have key := hfcDisc_mul_discFactor_of_summable lam hsum_tail
  have hfun : discConv (discFactor lam) (discTail c lam)
      = fun n => c n - (if n = 0 then scalarEval c lam else 0) :=
    funext fun n => discConv_discFactor hS hc hlam n
  have hfun2 : (fun n => c n - (if n = 0 then scalarEval c lam else (0 : ℂ)))
      = (fun n => c n + (if n = 0 then -scalarEval c lam else 0)) := by
    funext n
    by_cases h0 : n = 0 <;> simp [h0, sub_eq_add_neg]
  rw [hfun, hfun2] at key
  have hsum_const : Summable
      fun n => (if n = 0 then -scalarEval c lam else (0 : ℂ)) • a ^ n :=
    summable_of_ne_finset_zero (s := {0}) (by
      intro n hn
      have hn0 : n ≠ 0 := by simpa using hn
      simp [hn0])
  have hadd := hfcDisc_add_of_summable hsum_c.of_norm hsum_const
  rw [hadd, hfcDisc_const] at key
  rw [← key]
  simp [neg_smul, sub_eq_add_neg]

/-! ## Step 5 — the unit-contradiction conclusion (8a's shape) -/

/-- Forward spectral inclusion at the sharp scale: 8a's
`scalarEval_mem_spectrum` with its norm-scale factorisation
replaced by `hfcDisc_sub_scalarEval_sharp`; the
unit-contradiction argument is 8a's, verbatim in shape. -/
theorem scalarEval_mem_spectrum_sharp {a : A} {c : ℕ → ℂ}
    {S : ℝ} (hS : 0 < S) (hc : DiscSummable S c)
    {lam : ℂ} (hlamS : ‖lam‖ ≤ S)
    (hsum_c : Summable fun n => ‖c n • a ^ n‖)
    (hsum_tail : Summable fun n => ‖discTail c lam n • a ^ n‖)
    (hlam : lam ∈ spectrum ℂ a) :
    scalarEval c lam ∈ spectrum ℂ (hfcDisc a c) := by
  rw [spectrum.mem_iff] at hlam ⊢
  intro hunit
  apply hlam
  have hfact := hfcDisc_sub_scalarEval_sharp hS hc hlamS hsum_c hsum_tail
  have hc1 : Commute (algebraMap ℂ A lam) (hfcDisc a (discTail c lam)) :=
    Algebra.commutes lam _
  have hcomm : Commute (algebraMap ℂ A lam - a) (hfcDisc a (discTail c lam)) :=
    hc1.sub_left (commute_a_hfcDisc _)
  have hunit2 : IsUnit ((algebraMap ℂ A lam - a) * hfcDisc a (discTail c lam)) := by
    have h3 : (algebraMap ℂ A lam - a) * hfcDisc a (discTail c lam)
        = -((a - lam • (1 : A)) * hfcDisc a (discTail c lam)) := by
      rw [Algebra.algebraMap_eq_smul_one,
        show lam • (1 : A) - a = -(a - lam • (1 : A)) from (neg_sub a _).symm,
        neg_mul]
    rw [h3, ← hfact, neg_sub]
    have h2 : algebraMap ℂ A (scalarEval c lam) = scalarEval c lam • (1 : A) :=
      Algebra.algebraMap_eq_smul_one _
    rw [← h2]
    exact hunit
  exact ((hcomm.isUnit_mul_iff).mp hunit2).1

/-! ## The headline -/

/-- GATE-B2′: discharges the live target
`Shelf7bB2ForwardInterior` of 7B-PIN-2. Step 2 is GATE-B1's
corrected B1c (`scalarEval_discCoeff_eq_of_lt`, direct
application at `‖lam‖ < R₀`); steps 1, 3–5 are as above. -/
theorem shelf7bB2ForwardInterior_proved (a : A) (f : ℂ → ℂ) (R : ℝ) :
    Shelf7bB2ForwardInterior a f R := by
  intro hf hsr R₀ hsr₀ hR₀R lam hlam
  have hR₀ : 0 < R₀ := ENNReal.toReal_nonneg.trans_lt hsr₀
  have hlam_lt : ‖lam‖ < R₀ :=
    norm_lt_of_mem_spectrum_of_spectralRadius_lt hlam hsr₀
  have hscalar : scalarEval (discCoeff f R₀) lam = f lam :=
    scalarEval_discCoeff_eq_of_lt hf hR₀ hR₀R hlam_lt
  obtain ⟨S, hsrS, hSR₀⟩ := exists_between hsr₀
  have hS0 : 0 < S := ENNReal.toReal_nonneg.trans_lt hsrS
  have hcS : DiscSummable S (discCoeff f R₀) :=
    discSummable_discCoeff_interior hf hR₀R hS0.le hSR₀
  have hlamS : ‖lam‖ ≤ S := (norm_le_spectralRadius_toReal hlam).trans hsrS.le
  have hsum_c : Summable fun n => ‖discCoeff f R₀ n • a ^ n‖ :=
    summable_norm_smul_pow_discCoeff_interior a hf hR₀R hsr₀
  have hsum_tail : Summable fun n => ‖discTail (discCoeff f R₀) lam n • a ^ n‖ :=
    summable_norm_discTail_smul_pow a hf hR₀R hsr₀ hlam
  have hmem := scalarEval_mem_spectrum_sharp hS0 hcS hlamS hsum_c hsum_tail hlam
  rwa [hscalar] at hmem

end

end ThetLogos
