import Mathlib.Analysis.Analytic.CPolynomialDef
import ThetLogos.HfcDiscFactorisationRepair
import ThetLogos.DiscFactorisationTail
import ThetLogos.DiscZeroFreeUnit

/-!
# B4-ASM — discharge of `DiscFactorisationHyp'` and the close of GATE-B
(SHELF-7b-disc chain)

Brick B4-ASM of the GATE-B4 discharge campaign (scoping
`whitepaper/scoping-gate-b4-2026-11-02.md`; pack
`routeb-general-scratch/pack-gate-b4-asm.md`). This is the
final GATE-B campaign brick.

## GATE-B chain verdict (the header record)

* B1a / B1b / B1d FULL; B1c KILLED-and-corrected (the frozen
  boundary form is false; the interior form is the live one).
* B2′ FULL (forward inclusion at interior presentations).
* B3′ PARTIAL, superseded by this discharge: its assembly
  (`shelf7bDiscInterior_proved_of_factorisation`) is consumed
  here through B4-REPAIR's adapter, with the factorisation
  hypothesis now proved rather than assumed.
* REPAIR / FIN / PROD / TAIL / UNIT FULL.
* The frozen `DiscFactorisationHyp` stays REFUTED on the
  record (B4-REPAIR's `discFactorisationHyp_not`); the primed
  conditional form `DiscFactorisationHyp'` is the one
  discharged here, in full.
* K-GELFAND-SUBALGEBRA never used: nothing in the chain
  routes through characters of the polynomial closure or the
  Gelfand spectrum.

## Content

1. `discFactorisationHyp'_proved`: the primed factorisation
   hypothesis, assembled from the landed pieces. The
   identically-zero case is vacuous (the spectrum is
   nonempty and the spectral-radius bound puts a spectral
   value inside the disc, where `f = mu`, contradicting
   `mu ∉ f '' spectrum ℂ a`). In the main case, at an
   intermediate radius `R₂` with `R₀ < R₂ < R`, B4-TAIL's
   `discFactorisationTail` supplies the zero list `lam`
   (with multiplicity) and the zero-free tail `h`; every
   `l ∈ lam` is off the spectrum since `f l = mu`; the unit
   clause is B4-UNIT; the summability clause is B2′
   transport; the identity clause is TAIL's coefficient
   identity (B4-PROD) + B3′ multiplicativity
   (`hfcDisc_mul_of_summable`) + coefficient additivity for
   `f - mu` + the polynomial-value join
   (`hfcDisc_prod_linear`: `hfcDisc` of the coefficients of
   the linear-factor product function is the product of the
   factors `a - l • 1`, by induction over `lam` through 8a's
   `hfcDisc_discFactor`).
2. `shelf7bDiscInterior_proved`: the unconditional disc
   spectral mapping equality, via B4-REPAIR's adapter.

Face fence: this closes the DISC chain, under its own name.
7b-in-full is still pin-blocked (FULL-1..4) and is NOT
claimed here. 7b-disc is NOT 7b-in-full. NO CLAIM; dials 0/4.
-/

namespace ThetLogos

open Filter
open scoped NNReal ENNReal

noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A]
  [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A]

/-! ## 1. Coefficients of a function presented by a finite scalar series -/

/-- If `F` is the sum of a finitely supported scalar series
`c`, then the disc coefficients of `F` at any positive
presenting radius are exactly `c`: the finite series
`FormalMultilinearSeries.ofScalars ℂ c` is a
`HasFPowerSeriesOnBall` for `F` at every radius
(`FormalMultilinearSeries.hasFiniteFPowerSeriesOnBall_of_finite`),
and `DifferentiableOn.hasFPowerSeriesOnBall` presents `F` by
its Cauchy series; uniqueness
(`HasFPowerSeriesAt.eq_formalMultilinearSeries`) identifies
the two series. -/
theorem discCoeff_ofScalars_of_finite {c : ℕ → ℂ} {N : ℕ}
    (hfin : ∀ n, N ≤ n → c n = 0) {F : ℂ → ℂ}
    (hFsum : ∀ z, (∑' n, c n • z ^ n) = F z)
    (hFdiff : Differentiable ℂ F) {R₀ : ℝ} (hR₀ : 0 < R₀) :
    discCoeff F R₀ = c := by
  classical
  set q := FormalMultilinearSeries.ofScalars ℂ c with hq_def
  have hqfin : ∀ m, N ≤ m → q m = 0 :=
    fun m hm => (FormalMultilinearSeries.ofScalars_eq_zero ℂ m).mpr (hfin m hm)
  have hqsum : q.sum = F := by
    funext z
    have hHas : HasSum (fun n => c n • z ^ n) (q.sum z) := by
      have h := q.hasSum_of_finite hqfin z
      have hterm : (fun n => q n fun _ => z) = (fun n => c n • z ^ n) :=
        funext fun n => FormalMultilinearSeries.ofScalars_apply_eq c z n
      rwa [hterm] at h
    rw [← hFsum z]
    exact hHas.tsum_eq.symm
  have hqHas : HasFPowerSeriesAt F q 0 := by
    rw [← hqsum]
    exact (q.hasFiniteFPowerSeriesOnBall_of_finite hqfin).toHasFPowerSeriesOnBall
      |>.hasFPowerSeriesAt
  let rnn : ℝ≥0 := ⟨R₀, hR₀.le⟩
  have hrnnR : (rnn : ℝ) = R₀ := rfl
  have hcauchy : HasFPowerSeriesOnBall F (cauchyPowerSeries F 0 (rnn : ℝ)) 0
      (rnn : ℝ≥0∞) :=
    DifferentiableOn.hasFPowerSeriesOnBall
      (hFdiff.differentiableOn.mono (Set.subset_univ _)) hR₀
  have heq : cauchyPowerSeries F 0 (rnn : ℝ) = q :=
    hcauchy.hasFPowerSeriesAt.eq_formalMultilinearSeries hqHas
  funext n
  show cauchyPowerSeries F 0 R₀ n (fun _ => (1 : ℂ)) = c n
  rw [← hrnnR, heq]
  rw [FormalMultilinearSeries.ofScalars_apply_eq c (1 : ℂ) n]
  simp

/-- The disc coefficients of the identity function are the
`n = 1` delta sequence. -/
theorem discCoeff_id_seq {R₀ : ℝ} (hR₀ : 0 < R₀) :
    discCoeff (fun z : ℂ => z) R₀ = fun n => if n = 1 then (1 : ℂ) else 0 := by
  refine discCoeff_ofScalars_of_finite (N := 2) (fun n hn => ?_)
    (fun z => ?_) differentiable_id hR₀
  · have hn1 : n ≠ 1 := by omega
    simp [hn1]
  · rw [tsum_eq_single 1]
    · simp
    · intro n hn
      simp [hn]

/-- The disc coefficients of a linear factor `z - l` are
8a's `discFactor l` sequence. -/
theorem discCoeff_linear_seq (l : ℂ) {R₀ : ℝ} (hR₀ : 0 < R₀) :
    discCoeff (fun z : ℂ => z - l) R₀ = discFactor l := by
  refine discCoeff_ofScalars_of_finite (N := 2) (fun n hn => ?_)
    (fun z => ?_) (differentiable_id.sub_const l) hR₀
  · have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    simp [discFactor, hn0, hn1]
  · rw [tsum_eq_sum (s := Finset.range 2) (fun n hn => ?_)]
    · simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton]
      simp [discFactor]
      ring
    · have hn0 : n ≠ 0 :=
        fun h => hn (h ▸ Finset.mem_range.mpr (by norm_num))
      have hn1 : n ≠ 1 :=
        fun h => hn (h ▸ Finset.mem_range.mpr (by norm_num))
      simp [discFactor, hn0, hn1]

/-! ## 2. Coefficient additivity -/

/-- Additivity of `discCoeff` at an interior presenting
radius: the Cauchy series of a sum of two disc-holomorphic
functions is the sum of the Cauchy series, by
`HasFPowerSeriesOnBall.add` and uniqueness. -/
theorem discCoeff_add {f g : ℂ → ℂ} {R R₀ : ℝ}
    (hf : DiscHolomorphic f R) (hg : DiscHolomorphic g R)
    (hR₀ : 0 < R₀) (hR₀R : R₀ < R) :
    discCoeff (fun z => f z + g z) R₀
      = fun n => discCoeff f R₀ n + discCoeff g R₀ n := by
  let rnn : ℝ≥0 := ⟨R₀, hR₀.le⟩
  have hrnnR : (rnn : ℝ) = R₀ := rfl
  have hfR : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 (rnn : ℝ)) 0
      (rnn : ℝ≥0∞) :=
    DifferentiableOn.hasFPowerSeriesOnBall
      (hf.2.mono (Metric.closedBall_subset_ball hR₀R)) hR₀
  have hgR : HasFPowerSeriesOnBall g (cauchyPowerSeries g 0 (rnn : ℝ)) 0
      (rnn : ℝ≥0∞) :=
    DifferentiableOn.hasFPowerSeriesOnBall
      (hg.2.mono (Metric.closedBall_subset_ball hR₀R)) hR₀
  have hsumR : HasFPowerSeriesOnBall (fun z => f z + g z)
      (cauchyPowerSeries (fun z => f z + g z) 0 (rnn : ℝ)) 0 (rnn : ℝ≥0∞) :=
    DifferentiableOn.hasFPowerSeriesOnBall
      ((hf.2.add hg.2).mono (Metric.closedBall_subset_ball hR₀R)) hR₀
  have hadd : HasFPowerSeriesOnBall (fun z => f z + g z)
      (cauchyPowerSeries f 0 (rnn : ℝ) + cauchyPowerSeries g 0 (rnn : ℝ)) 0
      (rnn : ℝ≥0∞) := hfR.add hgR
  have heq : cauchyPowerSeries (fun z => f z + g z) 0 (rnn : ℝ)
      = cauchyPowerSeries f 0 (rnn : ℝ) + cauchyPowerSeries g 0 (rnn : ℝ) :=
    hsumR.hasFPowerSeriesAt.eq_formalMultilinearSeries hadd.hasFPowerSeriesAt
  funext n
  show cauchyPowerSeries (fun z => f z + g z) 0 R₀ n (fun _ => (1 : ℂ))
    = discCoeff f R₀ n + discCoeff g R₀ n
  rw [← hrnnR, heq]
  show (cauchyPowerSeries f 0 (rnn : ℝ) + cauchyPowerSeries g 0 (rnn : ℝ)) n
      (fun _ => (1 : ℂ)) = _
  rw [FormalMultilinearSeries.add_apply, add_apply]
  rfl

/-- Coefficients of `f - mu`: additivity against the constant
function `-mu`, whose coefficients are B3′'s
`discCoeff_const`. -/
theorem discCoeff_sub_const {f : ℂ → ℂ} {R R₀ : ℝ} {mu : ℂ}
    (hf : DiscHolomorphic f R) (hR₀ : 0 < R₀) (hR₀R : R₀ < R) :
    discCoeff (fun z => f z - mu) R₀
      = fun n => discCoeff f R₀ n + (if n = 0 then -mu else 0) := by
  have hfun : (fun z => f z - mu) = (fun z => f z + (fun _ => -mu) z) := by
    funext z
    rw [sub_eq_add_neg]
  rw [hfun, discCoeff_add hf ⟨hf.1, differentiableOn_const (-mu)⟩ hR₀ hR₀R]
  funext n
  rw [discCoeff_const (-mu) hR₀ n]

/-! ## 3. The polynomial-value join -/

/-- **The polynomial-value join.** `hfcDisc` of the
coefficients of the linear-factor product function
`z ↦ ∏ l ∈ lam, (z - l)` is the product of the algebra
factors `a - l • 1`: induction over `lam`, the step being
B4-PROD (`discCoeff_mul`) at the interior radius, the
coefficient identification `discCoeff_linear_seq`, B3′
multiplicativity (`hfcDisc_mul_of_summable`) at the sharp
summabilities (B2′ transport), and 8a's
`hfcDisc_discFactor`. -/
theorem hfcDisc_prod_linear (a : A) (lam : List ℂ) {R R₀ : ℝ}
    (hfR : 0 < R) (hR₀ : 0 < R₀) (hR₀R : R₀ < R)
    (hsr₀ : (spectralRadius ℂ a).toReal < R₀) :
    hfcDisc a (discCoeff (fun z => (lam.map fun l => z - l).prod) R₀)
      = (lam.map fun l => a - l • (1 : A)).prod := by
  induction lam with
  | nil =>
    have hfun : (fun z : ℂ => (([] : List ℂ).map fun l => z - l).prod)
        = (fun _ => (1 : ℂ)) := by
      funext z
      simp
    rw [hfun, show discCoeff (fun _ => (1 : ℂ)) R₀
        = (fun n => if n = 0 then (1 : ℂ) else 0) from
      funext (discCoeff_const 1 hR₀), hfcDisc_one]
    simp
  | cons l lam' ih =>
    have htail : DiscHolomorphic (fun z => (lam'.map fun l => z - l).prod) R :=
      discHolomorphic_prod_sub_linear lam' hfR
    have hlin : DiscHolomorphic (fun z : ℂ => z - l) R :=
      ⟨hfR, (differentiable_id.sub_const l).differentiableOn⟩
    have hfun : (fun z => ((l :: lam').map fun l => z - l).prod)
        = (fun z => (z - l) * (lam'.map fun l => z - l).prod) := by
      funext z
      simp [List.map_cons, List.prod_cons]
    have hsum_lin : Summable fun n => ‖discFactor l n • a ^ n‖ := by
      rw [← discCoeff_linear_seq l hR₀]
      exact summable_norm_smul_pow_discCoeff_interior a hlin hR₀R hsr₀
    have hsum_tail : Summable
        fun n => ‖discCoeff (fun z => (lam'.map fun l => z - l).prod) R₀ n
          • a ^ n‖ :=
      summable_norm_smul_pow_discCoeff_interior a htail hR₀R hsr₀
    rw [hfun, discCoeff_mul hlin htail hR₀ hR₀R, discCoeff_linear_seq l hR₀,
      hfcDisc_mul_of_summable hsum_lin hsum_tail, hfcDisc_discFactor, ih]
    simp [List.map_cons, List.prod_cons]

/-! ## 4. The discharge -/

/-- **Headline 1 (B4-ASM).** The primed factorisation
hypothesis `DiscFactorisationHyp'`, discharged in full from
the landed pieces of the GATE-B chain; see the module face
for the assembly. The frozen `DiscFactorisationHyp` stays
refuted on the record (B4-REPAIR); this is its corrected
conditional replacement, proved. -/
theorem discFactorisationHyp'_proved (a : A) (f : ℂ → ℂ) (R : ℝ) :
    DiscFactorisationHyp' a f R := by
  intro hf hsr R₀ hsr₀ hR₀R mu hmu
  by_cases hne : Set.EqOn (fun z => f z - mu) 0 (Metric.ball 0 R)
  · -- Identically-zero case: vacuous, by contradiction.
    exfalso
    obtain ⟨lam₀, hlam₀⟩ := spectrum.nonempty a
    have hnorm : ‖lam₀‖ ≤ (spectralRadius ℂ a).toReal :=
      norm_le_spectralRadius_toReal hlam₀
    have hball : lam₀ ∈ Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      exact hnorm.trans_lt hsr
    have hEq := hne hball
    have hfl : f lam₀ = mu := by
      have h1 : f lam₀ - mu = 0 := by simpa using hEq
      exact sub_eq_zero.mp h1
    exact hmu ⟨lam₀, hlam₀, hfl⟩
  · -- Main case: B4-TAIL at an intermediate radius `R₂`.
    have hR₀pos : 0 < R₀ := ENNReal.toReal_nonneg.trans_lt hsr₀
    obtain ⟨R₂, hR₀₂, hR₂R⟩ := exists_between hR₀R
    obtain ⟨lam, h, -, hmem, hhhol, hhfree, hfact⟩ :=
      discFactorisationTail hf hne hR₀pos hR₀₂.le hR₂R
    have hsum_h : Summable fun n => ‖discCoeff h R₀ n • a ^ n‖ :=
      summable_norm_smul_pow_discCoeff_interior a hhhol hR₀R hsr₀
    refine ⟨lam, discCoeff h R₀, ?_, hsum_h,
      isUnit_hfcDisc_of_zeroFree a h hsr₀ hR₀₂ hhhol hR₂R hhfree, ?_⟩
    · -- Every `l ∈ lam` is off the spectrum: `f l = mu`.
      intro l hl hlsp
      apply hmu
      have hlz : l ∈ zeroFinsetClosedBall hf hR₂R hne := (hmem l).mp hl
      have hfl : f l = mu :=
        ((mem_zeroFinsetClosedBall hf hR₂R hne l).mp hlz).2
      exact ⟨l, hlsp, hfl⟩
    · -- The identity clause.
      have hP : DiscHolomorphic (fun z => (lam.map fun l => z - l).prod) R :=
        discHolomorphic_prod_sub_linear lam hf.1
      have hcoeff : discCoeff (fun z => f z - mu) R₀
          = discConv (discCoeff (fun z => (lam.map fun l => z - l).prod) R₀)
              (discCoeff h R₀) := by
        have hfun : (fun z => f z - mu)
            = (fun z => (lam.map fun l => z - l).prod * h z) :=
          funext hfact
        rw [hfun]
        exact discCoeff_mul hP hhhol hR₀pos hR₀R
      have hsumP : Summable
          fun n => ‖discCoeff (fun z => (lam.map fun l => z - l).prod) R₀ n
            • a ^ n‖ :=
        summable_norm_smul_pow_discCoeff_interior a hP hR₀R hsr₀
      have hval_g : hfcDisc a (discCoeff (fun z => f z - mu) R₀)
          = (lam.map fun l => a - l • (1 : A)).prod
            * hfcDisc a (discCoeff h R₀) := by
        rw [hcoeff, hfcDisc_mul_of_summable hsumP hsum_h,
          hfcDisc_prod_linear a lam hf.1 hR₀pos hR₀R hsr₀]
      have hsum_f : Summable fun n => ‖discCoeff f R₀ n • a ^ n‖ :=
        summable_norm_smul_pow_discCoeff_interior a hf hR₀R hsr₀
      have hsum_d : Summable
          fun n => ‖(if n = 0 then -mu else (0 : ℂ)) • a ^ n‖ :=
        summable_of_ne_finset_zero (s := {0}) (by
          intro n hn
          have hn0 : n ≠ 0 := by simpa using hn
          simp [hn0])
      have hval_f : hfcDisc a (discCoeff (fun z => f z - mu) R₀)
          = hfcDisc a (discCoeff f R₀) - mu • (1 : A) := by
        rw [discCoeff_sub_const hf hR₀pos hR₀R,
          hfcDisc_add_of_summable hsum_f.of_norm hsum_d.of_norm, hfcDisc_const]
        rw [neg_smul, ← sub_eq_add_neg]
      rw [hval_f] at hval_g
      exact hval_g

/-- **Headline 2 (B4-ASM).** The unconditional disc spectral
mapping equality `Shelf7bDiscInterior`, from headline 1 via
B4-REPAIR's adapter feeding B3′'s landed assembly. This
closes the DISC chain under its own name; it is not
7b-in-full. -/
theorem shelf7bDiscInterior_proved (a : A) (f : ℂ → ℂ) (R : ℝ) :
    Shelf7bDiscInterior a f R :=
  shelf7bDiscInterior_proved_of_factorisation' a f R
    (discFactorisationHyp'_proved a f R)

end

end ThetLogos
