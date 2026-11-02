import ThetLogos.HfcDiscForward

/-!
# GATE-B3′ — disc spectral mapping equality (SHELF-7b-disc chain)

Brick GATE-B3′ of the SHELF line (pack
`routeb-general-scratch/pack-gate-b3.md`). Target: the live
B3′ Prop `Shelf7bDiscInterior` frozen in 7B-PIN-2
(`Shelf7bPin2.lean`), i.e.
`spectrum ℂ (hfcDisc a (discCoeff f R₀)) = f '' spectrum ℂ a`
at every interior presenting radius `R₀`.

## Verdict: PARTIAL at the pack's pre-named seam

The forward inclusion (⊇) is GATE-B2′
(`shelf7bB2ForwardInterior_proved`, `HfcDiscForward.lean`).
This module lands:

* Ingredient 1 of the registered factorisation route, in
  FULL: general sharp-scale multiplicativity of `hfcDisc`
  under the Cauchy product (`hfcDisc_mul_of_summable`) —
  B2′ had only the `discFactor` special case.
* A hypothesis-free fragment: the equality for constant
  functions (`shelf7bDiscInterior_const`), via
  `discCoeff_const` (formal-series uniqueness) and the
  empty factorisation (`discFactorisationHyp_const`).
* The reverse inclusion (⊆), hence the equality, PROVED
  under the single named hypothesis `DiscFactorisationHyp`
  below, which states exactly the output of ingredients 2+3
  of the registered route: for `mu ∉ f '' spectrum ℂ a`, the
  element `hfcDisc a (discCoeff f R₀) - mu • 1` factorises
  as a finite product of factors `(a - lamᵢ • 1)` with
  `lamᵢ ∉ spectrum ℂ a`, times the `hfcDisc` value of a
  coefficient sequence whose value is a unit (the zero-free
  factor's value). The assembly from that factorisation to
  `mu ∉ spectrum ℂ (hfcDisc a (discCoeff f R₀))` is proved
  here in full (each `(a - lamᵢ • 1)` is a unit since
  `lamᵢ ∉ spectrum ℂ a`; a finite product of units times a
  unit is a unit).

## Named open remainder (the seam)

Discharging `DiscFactorisationHyp` in general — i.e.
ingredients 2 (zero-free on a closed subdisc ⇒ unit, via
the reciprocal series) and 3 (finiteness and factorisation
of the zeros of `f - mu` in a closed subdisc) of the pack's
registered route — is OPEN. The general (unconditional)
`Shelf7bDiscInterior` is therefore NOT discharged here.

Binding kill respected: K-GELFAND-SUBALGEBRA — nothing here
routes through characters of the polynomial closure or the
Gelfand spectrum. The REFUTED frozen forms (`Shelf7bDisc`,
`Shelf7bB2Forward`) are never consumed.

Face fence: 7b-disc is NOT 7b-in-full. NO CLAIM; dials 0/4.
-/

namespace ThetLogos

open Filter
open scoped NNReal ENNReal

noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A]
  [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A]

/-! ## Ingredient 1 — general sharp-scale multiplicativity -/

/-- Ingredient 1, in FULL: `hfcDisc` of a Cauchy product of
two coefficient sequences whose series are summable at the
sharp (spectral-radius) scale is the product of the
`hfcDisc` values. This is 8a's `hfcDisc_mul` with its
norm-scale `DiscSummable` hypotheses replaced by the sharp
summabilities, and B2′'s `discFactor` special case
(`hfcDisc_mul_discFactor_of_summable`) with the finite
factor replaced by an arbitrary second sequence; the
antidiagonal `tsum` product argument is the same. -/
theorem hfcDisc_mul_of_summable {a : A} {c d : ℕ → ℂ}
    (hc : Summable fun n => ‖c n • a ^ n‖)
    (hd : Summable fun n => ‖d n • a ^ n‖) :
    hfcDisc a (discConv c d) = hfcDisc a c * hfcDisc a d := by
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (f := fun n => c n • a ^ n) (g := fun n => d n • a ^ n) hc hd
  show ∑' n, discConv c d n • a ^ n
    = (∑' n, c n • a ^ n) * ∑' n, d n • a ^ n
  rw [hprod]
  refine tsum_congr fun n => ?_
  rw [discConv, Finset.sum_smul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
  rw [← hsum, pow_add, smul_mul_assoc, mul_smul_comm, smul_smul]

/-! ## The named hypothesis (ingredients 2+3, stated exactly) -/

/-- The named factorisation hypothesis at the resisting
ingredients 2+3 of the registered route, stated exactly:
for every interior presenting radius `R₀` and every
`mu ∉ f '' spectrum ℂ a`, the element
`hfcDisc a (discCoeff f R₀) - mu • 1` factorises as a
finite product of linear factors `(a - lamᵢ • 1)` with
every `lamᵢ ∉ spectrum ℂ a` (these are the zeros of
`f - mu` in the closed subdisc, none of which lies in the
spectrum), times `hfcDisc a hc` for a coefficient sequence
`hc` (the zero-free factor's coefficients) whose series is
sharp-summable and whose `hfcDisc` value is a unit.

Discharging this hypothesis in general is the named open
remainder: it is exactly ingredients 2 (zero-free ⇒ unit
via the reciprocal series) and 3 (finite factorisation of
the zeros of `f - mu` in a closed subdisc) of the pack. -/
def DiscFactorisationHyp (a : A) (f : ℂ → ℂ) (R : ℝ) : Prop :=
  ∀ R₀ : ℝ, (spectralRadius ℂ a).toReal < R₀ → R₀ < R →
    ∀ mu : ℂ, mu ∉ f '' spectrum ℂ a →
      ∃ (lam : List ℂ) (hc : ℕ → ℂ),
        (∀ l ∈ lam, l ∉ spectrum ℂ a) ∧
        (Summable fun n => ‖hc n • a ^ n‖) ∧
        IsUnit (hfcDisc a hc) ∧
        hfcDisc a (discCoeff f R₀) - mu • (1 : A)
          = (lam.map fun l => a - l • (1 : A)).prod * hfcDisc a hc

/-! ## Assembly — reverse inclusion from the factorisation -/

/-- A linear factor at a non-spectral point is a unit:
`lam ∉ spectrum ℂ a` unfolds (via `spectrum.mem_iff`) to
`IsUnit (algebraMap ℂ A lam - a)`, and
`a - lam • 1 = -(algebraMap ℂ A lam - a)`. -/
theorem isUnit_a_sub_smul_one_of_notMem_spectrum {a : A} {lam : ℂ}
    (hlam : lam ∉ spectrum ℂ a) :
    IsUnit (a - lam • (1 : A)) := by
  have hlam' : IsUnit (algebraMap ℂ A lam - a) := by
    by_contra hcon
    exact hlam (spectrum.mem_iff.mpr hcon)
  have h2 : algebraMap ℂ A lam = lam • (1 : A) :=
    Algebra.algebraMap_eq_smul_one _
  rw [h2] at hlam'
  have h3 : a - lam • (1 : A) = -(lam • (1 : A) - a) := (neg_sub _ _).symm
  rw [h3]
  exact hlam'.neg

/-- An ordered product of units is a unit (the ambient ring
is not assumed commutative, so this is a `List.prod`
induction, not a `Finset.prod` lemma). -/
theorem isUnit_list_prod {l : List A} (h : ∀ x ∈ l, IsUnit x) :
    IsUnit l.prod := by
  induction l with
  | nil => exact isUnit_one
  | cons x xs ih =>
    rw [List.prod_cons]
    exact (h x (by simp)).mul (ih fun y hy => h y (by simp [hy]))

/-- The reverse inclusion, proved from the factorisation
data for a single `mu`: an ordered product of units (the
linear factors at the zeros of `f - mu`, all off the
spectrum) times a unit (the zero-free factor's value) is a
unit, so `mu ∉ spectrum ℂ (hfcDisc a (discCoeff f R₀))`. -/
theorem notMem_spectrum_hfcDisc_of_factorisation {a : A} {f : ℂ → ℂ}
    {R₀ : ℝ} {mu : ℂ}
    (lam : List ℂ) (hc : ℕ → ℂ)
    (hlam : ∀ l ∈ lam, l ∉ spectrum ℂ a)
    (hunit : IsUnit (hfcDisc a hc))
    (hfact : hfcDisc a (discCoeff f R₀) - mu • (1 : A)
      = (lam.map fun l => a - l • (1 : A)).prod * hfcDisc a hc) :
    mu ∉ spectrum ℂ (hfcDisc a (discCoeff f R₀)) := by
  intro hmem
  rw [spectrum.mem_iff] at hmem
  apply hmem
  have hprod : IsUnit (lam.map fun l => a - l • (1 : A)).prod := by
    apply isUnit_list_prod
    intro x hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    exact isUnit_a_sub_smul_one_of_notMem_spectrum (hlam l hl)
  have hunit2 : IsUnit (hfcDisc a (discCoeff f R₀) - mu • (1 : A)) := by
    rw [hfact]
    exact hprod.mul hunit
  have h2 : algebraMap ℂ A mu = mu • (1 : A) :=
    Algebra.algebraMap_eq_smul_one _
  rw [h2]
  have h3 : mu • (1 : A) - hfcDisc a (discCoeff f R₀)
      = -(hfcDisc a (discCoeff f R₀) - mu • (1 : A)) := (neg_sub _ _).symm
  rw [h3]
  exact hunit2.neg

/-- The reverse inclusion under the named hypothesis. -/
theorem spectrum_hfcDisc_subset_of_factorisation (a : A) (f : ℂ → ℂ)
    (R : ℝ) (hfact : DiscFactorisationHyp a f R) :
    ∀ R₀ : ℝ, (spectralRadius ℂ a).toReal < R₀ → R₀ < R →
      spectrum ℂ (hfcDisc a (discCoeff f R₀)) ⊆ f '' spectrum ℂ a := by
  intro R₀ hsr₀ hR₀R mu hmu
  by_contra hcon
  obtain ⟨lam, hc, hlam, -, hunit, hfact'⟩ :=
    hfact R₀ hsr₀ hR₀R mu hcon
  exact notMem_spectrum_hfcDisc_of_factorisation lam hc hlam hunit hfact' hmu

/-! ## The headline, at the pre-named PARTIAL seam -/

/-- GATE-B3′, PARTIAL at the pack's pre-named seam: the
disc spectral mapping equality `Shelf7bDiscInterior`,
assembled from GATE-B2′ (forward inclusion) and the
reverse inclusion proved above under the single named
hypothesis `DiscFactorisationHyp` (ingredients 2+3 of the
registered factorisation route). The general case —
discharging `DiscFactorisationHyp` — is named open at
exactly that hypothesis; see the module face. -/
theorem shelf7bDiscInterior_proved_of_factorisation (a : A) (f : ℂ → ℂ)
    (R : ℝ) (hfact : DiscFactorisationHyp a f R) :
    Shelf7bDiscInterior a f R := by
  intro hf hsr R₀ hsr₀ hR₀R
  apply Set.Subset.antisymm
  · exact spectrum_hfcDisc_subset_of_factorisation a f R hfact R₀ hsr₀ hR₀R
  · intro mu hmu
    obtain ⟨lam, hlam, rfl⟩ := hmu
    exact shelf7bB2ForwardInterior_proved a f R hf hsr R₀ hsr₀ hR₀R lam hlam

/-! ## A hypothesis-free fragment: constant functions

For constant `f` the factorisation is empty (`lam = []`):
the zeros list is vacuous, the zero-free factor is the
constant `c₀ - mu` itself, and its unit is elementary. This
discharges `DiscFactorisationHyp` — hence the equality —
for constant functions with no hypothesis. -/

/-- The coefficients of a constant function, by uniqueness
of formal power series (`HasFPowerSeriesAt.
eq_formalMultilinearSeries` against
`constFormalMultilinearSeries`). -/
theorem discCoeff_const (c₀ : ℂ) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    discCoeff (fun _ => c₀) R n = if n = 0 then c₀ else 0 := by
  let rnn : ℝ≥0 := ⟨R, hR.le⟩
  have hrnnR : (rnn : ℝ) = R := rfl
  have hdiff : DifferentiableOn ℂ (fun _ => c₀)
      (Metric.closedBall (0 : ℂ) (rnn : ℝ)) :=
    differentiableOn_const c₀
  have h1 : HasFPowerSeriesOnBall (fun _ => c₀)
      (cauchyPowerSeries (fun _ => c₀) 0 (rnn : ℝ)) 0 (rnn : ℝ≥0∞) :=
    DifferentiableOn.hasFPowerSeriesOnBall hdiff hR
  have heq : cauchyPowerSeries (fun _ => c₀) 0 (rnn : ℝ)
      = constFormalMultilinearSeries ℂ ℂ c₀ :=
    h1.hasFPowerSeriesAt.eq_formalMultilinearSeries
      (hasFPowerSeriesOnBall_const (𝕜 := ℂ) (E := ℂ) (c := c₀)
        (e := (0 : ℂ))).hasFPowerSeriesAt
  have h3 : cauchyPowerSeries (fun _ => c₀) 0 (rnn : ℝ) n (fun _ => (1 : ℂ))
      = constFormalMultilinearSeries ℂ ℂ c₀ n (fun _ => (1 : ℂ)) := by
    rw [heq]
  rw [hrnnR] at h3
  show (cauchyPowerSeries (fun _ => c₀) 0 R n) (fun _ => (1 : ℂ)) = _
  rw [h3]
  by_cases hn : n = 0
  · subst hn
    simp [constFormalMultilinearSeries]
  · simp [constFormalMultilinearSeries, hn]

/-- `hfcDisc` of a constant function's coefficients is the
constant scalar. -/
theorem hfcDisc_discCoeff_const (a : A) (c₀ : ℂ) {R₀ : ℝ} (hR₀ : 0 < R₀) :
    hfcDisc a (discCoeff (fun _ => c₀) R₀) = c₀ • (1 : A) := by
  have hfun : discCoeff (fun _ => c₀) R₀
      = fun n => if n = 0 then c₀ else 0 :=
    funext (discCoeff_const c₀ hR₀)
  rw [hfun]
  exact hfcDisc_const c₀

/-- `DiscFactorisationHyp` discharged for constant
functions: the factor list is empty and the zero-free
factor is the nonzero constant `c₀ - mu`. -/
theorem discFactorisationHyp_const (a : A) (c₀ : ℂ) (R : ℝ) :
    DiscFactorisationHyp a (fun _ => c₀) R := by
  intro R₀ hsr₀ hR₀R mu hmu
  have hR₀ : 0 < R₀ := ENNReal.toReal_nonneg.trans_lt hsr₀
  have hR : 0 < R := hR₀.trans hR₀R
  have hf : DiscHolomorphic (fun _ => c₀) R :=
    ⟨hR, differentiableOn_const c₀⟩
  obtain ⟨lam₀, hlam₀⟩ := spectrum.nonempty a
  have hmu_ne : mu ≠ c₀ := by
    intro h
    exact hmu ⟨lam₀, hlam₀, h.symm⟩
  have hsum_c : Summable fun n => ‖discCoeff (fun _ => c₀) R₀ n • a ^ n‖ :=
    summable_norm_smul_pow_discCoeff_interior a hf hR₀R hsr₀
  have hsum_d : Summable
      fun n => ‖(if n = 0 then -mu else (0 : ℂ)) • a ^ n‖ :=
    summable_of_ne_finset_zero (s := {0}) (by
      intro n hn
      have hn0 : n ≠ 0 := by simpa using hn
      simp [hn0])
  have hval : hfcDisc a
        (fun n => discCoeff (fun _ => c₀) R₀ n
          + (if n = 0 then -mu else 0))
      = (c₀ - mu) • (1 : A) := by
    rw [hfcDisc_add_of_summable hsum_c.of_norm hsum_d.of_norm,
      hfcDisc_const, hfcDisc_discCoeff_const a c₀ hR₀, sub_smul,
      neg_smul, sub_eq_add_neg]
  refine ⟨[], (fun n => discCoeff (fun _ => c₀) R₀ n
      + (if n = 0 then -mu else 0)), ?_, ?_, ?_, ?_⟩
  · intro l hl
    simp at hl
  · refine Summable.of_norm_bounded (hsum_c.add hsum_d) (fun n => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _), add_smul]
    exact norm_add_le _ _
  · rw [hval, ← Algebra.algebraMap_eq_smul_one]
    exact (isUnit_iff_ne_zero.mpr
      (sub_ne_zero.mpr (Ne.symm hmu_ne))).map (algebraMap ℂ A)
  · simp only [List.map_nil, List.prod_nil, one_mul]
    rw [hval, hfcDisc_discCoeff_const a c₀ hR₀, sub_smul]

/-- GATE-B3′ for constant functions, unconditional: the
disc spectral mapping equality holds for `f = fun _ => c₀`
(the spectrum of `c₀ • 1` is `{c₀}`, and the image of the
nonempty spectrum under a constant map is `{c₀}`). -/
theorem shelf7bDiscInterior_const (a : A) (c₀ : ℂ) (R : ℝ) :
    Shelf7bDiscInterior a (fun _ => c₀) R :=
  shelf7bDiscInterior_proved_of_factorisation a (fun _ => c₀) R
    (discFactorisationHyp_const a c₀ R)

end

end ThetLogos
