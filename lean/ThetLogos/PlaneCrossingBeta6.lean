/-
# ThetLogos.PlaneCrossingBeta6 — the β⁶ coefficient at
general (G, ρ): core definitions only (B6-1a)

**Fences, up front.** NO CLAIM. Parts of the Clay
Yang–Mills statement closed by this module: **0**. Dials
0/4. This is a DEFINITION brick (B6-1a): it owns the sixth
Taylor coefficient of the layer kernel `𝒜 = layerKernel`
at general `(G, ρ)`, its constant part in the assembly's
pattern values, and its dependent part `κ₆^dep` under the
same distinct-support cumulant fence as orders 4 and 5.
Definitions and Taylor-coefficient identities only.
**No sign is asserted for `betaCoeff6`, `kappa6dep`, or
any part of them anywhere in this module**, and no
positivity of `𝒜` at any `β` follows: the β⁶ general
sign is FRONTIER — its new channels carry four entry
factors at a site (quadruple twirls), on top of the
still-unowned (2,1) triple twirl that already blocks
the β⁵ general sign, and no twirl theory for either
exists in the tree.

**What is NOT here.** The channel content of
`kappa6dep` — the C6 moments, the Θ(2,2,2) moments, and
the (2,2,1,1) / (3,1,1,1) channels on primitive quads
named by B6-0's landed selection — is B6-1b / B6-2
territory and is **not** asserted here. No assembly
identity expressing `kappa6dep` through dressings and
channel excesses is asserted here; that identity is
B6-2's seam, named here only as a seam. The channel
definitions themselves follow in B6-1b, into this same
module's later sections.

**The named-space fence (inherited).** "Dependent
part" means the cumulant over partitions of the
DISTINCT-column support, exactly as at orders 4 and 5:
patterns on at most 3 distinct columns factor into
constants at arbitrary exponents, so the constant
assembly below carries their full values; patterns on
4, 5 and 6 distinct columns enter the constant part
only through their fully-split baselines, and their
dependent excesses are the content of `kappa6dep`.
The `N = 2` sector and the `N = 4` wrap sector are
fenced exactly as at orders 4 and 5.

**What this module (B6-1a) proves.** (i) The order-6
expansion of the stratum average, real form, with tail
`R₇`. (ii) The coefficient audit of the constant
assembly: under all pattern values `1`, `kappa6Const`
totals `M⁶`, the number of ordered 6-tuples of columns.
-/

import ThetLogos.PlaneCrossingBeta5

open MeasureTheory Finset

namespace ThetLogos

section Coeff6

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- The sixth β-coefficient of `𝒜`: `∫ layerDensSum⁶ / 720`
(so `𝒜 = 1 − βC₁ + β²C₂ − β³C₃ + β⁴C₄ − β⁵C₅ + β⁶C₆ + O(β⁷)`).
Defined by the same construction as `betaCoeff5`. -/
noncomputable def betaCoeff6 (u u' : LayerLink N → G) : ℝ :=
  ∫ α, (layerDensSum ρ α u u') ^ 6 / 720
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- **The expansion, real form, at order 6.** For every
real `β`, the stratum average of the layer exponential
is `1 − βC₁ + β²C₂ − β³C₃ + β⁴C₄ − β⁵C₅ + β⁶C₆ + R₇(β)` with
`R₇` the displayed tail series. FENCE: a Taylor
coefficient identity; no positivity of `𝒜` at any
`β > 0` follows, and no sign for `betaCoeff6` or any
part of it is asserted. Proved by the order-5 pattern
(`layerKernel_real_expansion5`) with one more term
split off. -/
theorem layerKernel_real_expansion6 (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) :
    ∫ α, Real.exp (-(β * layerDensSum ρ α u u'))
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = 1 - β * betaCoeff1 ρ μG u u' + β ^ 2 * betaCoeff2 ρ μG u u'
        - β ^ 3 * betaCoeff3 ρ μG u u'
        + β ^ 4 * betaCoeff4 ρ μG u u'
        - β ^ 5 * betaCoeff5 ρ μG u u'
        + β ^ 6 * betaCoeff6 ρ μG u u'
        + ∑' (k : ℕ), ∫ α, (-β * layerDensSum ρ α u u') ^ (k + 7)
            / ((Nat.factorial (k + 7) : ℝ))
            ∂(Measure.pi fun _ : LayerSite N => μG) := by
  have hexp : ∀ α : LayerSite N → G,
      Real.exp (-(β * layerDensSum ρ α u u'))
        = ∑' n : ℕ, (-β * layerDensSum ρ α u u') ^ n
            / ((Nat.factorial n : ℝ)) := by
    intro α
    have h1 : Real.exp (-(β * layerDensSum ρ α u u'))
        = NormedSpace.exp (-(β * layerDensSum ρ α u u')) :=
      congrFun Real.exp_eq_exp_ℝ _
    rw [h1, congrFun (NormedSpace.exp_eq_tsum ℝ) _]
    apply tsum_congr
    intro n
    rw [neg_mul, smul_eq_mul, div_eq_inv_mul]
  have hSumm : Summable fun n => ∫ α,
        (-β * layerDensSum ρ α u u') ^ n / ((Nat.factorial n : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG) :=
    (summable_norm_term_int ρ μG hN hρcont β u u').of_norm_bounded
      (fun n => norm_integral_le_integral_norm _)
  have ht0 : (∫ α, (-β * layerDensSum ρ α u u') ^ 0
        / ((Nat.factorial 0 : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG)) = 1 := by
    have hpt : ∀ α : LayerSite N → G,
        (-β * layerDensSum ρ α u u') ^ 0 / ((Nat.factorial 0 : ℝ))
          = 1 :=
      fun α => by norm_num
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_const, probReal_univ, one_smul]
  have ht1 : (∫ α, (-β * layerDensSum ρ α u u') ^ 1
        / ((Nat.factorial 1 : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = -β * betaCoeff1 ρ μG u u' := by
    have hpt : ∀ α : LayerSite N → G,
        (-β * layerDensSum ρ α u u') ^ 1 / ((Nat.factorial 1 : ℝ))
          = -β * layerDensSum ρ α u u' :=
      fun α => by
        simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_const_mul _ _
  have ht2 : (∫ α, (-β * layerDensSum ρ α u u') ^ 2
        / ((Nat.factorial 2 : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = β ^ 2 * betaCoeff2 ρ μG u u' := by
    have hpt : ∀ α : LayerSite N → G,
        (-β * layerDensSum ρ α u u') ^ 2 / ((Nat.factorial 2 : ℝ))
          = β ^ 2 * ((layerDensSum ρ α u u') ^ 2 / 2) := by
      intro α
      have h2 : ((Nat.factorial 2 : ℝ)) = 2 := by
        norm_num [Nat.factorial]
      rw [h2]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_const_mul _ _
  have ht3 : (∫ α, (-β * layerDensSum ρ α u u') ^ 3
        / ((Nat.factorial 3 : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = -β ^ 3 * betaCoeff3 ρ μG u u' := by
    have hpt : ∀ α : LayerSite N → G,
        (-β * layerDensSum ρ α u u') ^ 3 / ((Nat.factorial 3 : ℝ))
          = -β ^ 3 * ((layerDensSum ρ α u u') ^ 3 / 6) := by
      intro α
      have h3 : ((Nat.factorial 3 : ℝ)) = 6 := by
        norm_num [Nat.factorial]
      rw [h3]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_const_mul _ _
  have ht4 : (∫ α, (-β * layerDensSum ρ α u u') ^ 4
        / ((Nat.factorial 4 : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = β ^ 4 * betaCoeff4 ρ μG u u' := by
    have hpt : ∀ α : LayerSite N → G,
        (-β * layerDensSum ρ α u u') ^ 4 / ((Nat.factorial 4 : ℝ))
          = β ^ 4 * ((layerDensSum ρ α u u') ^ 4 / 24) := by
      intro α
      have h4 : ((Nat.factorial 4 : ℝ)) = 24 := by
        norm_num [Nat.factorial]
      rw [h4]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_const_mul _ _
  have ht5 : (∫ α, (-β * layerDensSum ρ α u u') ^ 5
        / ((Nat.factorial 5 : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = -β ^ 5 * betaCoeff5 ρ μG u u' := by
    have hpt : ∀ α : LayerSite N → G,
        (-β * layerDensSum ρ α u u') ^ 5 / ((Nat.factorial 5 : ℝ))
          = -β ^ 5 * ((layerDensSum ρ α u u') ^ 5 / 120) := by
      intro α
      have h5 : ((Nat.factorial 5 : ℝ)) = 120 := by
        norm_num [Nat.factorial]
      rw [h5]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_const_mul _ _
  have ht6 : (∫ α, (-β * layerDensSum ρ α u u') ^ 6
        / ((Nat.factorial 6 : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = β ^ 6 * betaCoeff6 ρ μG u u' := by
    have hpt : ∀ α : LayerSite N → G,
        (-β * layerDensSum ρ α u u') ^ 6 / ((Nat.factorial 6 : ℝ))
          = β ^ 6 * ((layerDensSum ρ α u u') ^ 6 / 720) := by
      intro α
      have h6 : ((Nat.factorial 6 : ℝ)) = 720 := by
        norm_num [Nat.factorial]
      rw [h6]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_const_mul _ _
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
    ← (hasSum_integral_of_summable_integral_norm
      (fun n => integrable_term ρ μG hN hρcont β u u' n)
      (summable_norm_term_int ρ μG hN hρcont β u u')).tsum_eq,
    ← hSumm.sum_add_tsum_nat_add 7,
    Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ,
    Finset.sum_range_zero,
    ht0, ht1, ht2, ht3, ht4, ht5, ht6]
  ring

end Coeff6

section ClosedForm6

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- The constant part of the sixth coefficient, in the
assembly's pattern values: with `M = colCount N`,
`B = 1 − e₁/d`, `Aⱼ = densMomentValue j`:
`M·A₆ + 6M(M−1)·A₅B + 15M(M−1)·A₄A₂
+ 15M(M−1)(M−2)·A₄B² + 10M(M−1)·A₃²
+ 60M(M−1)(M−2)·A₃A₂B + 20M(M−1)(M−2)(M−3)·A₃B³
+ 15M(M−1)(M−2)·A₂³ + 45M(M−1)(M−2)(M−3)·A₂²B²
+ 15M(M−1)(M−2)(M−3)(M−4)·A₂B⁴
+ M(M−1)(M−2)(M−3)(M−4)(M−5)·B⁶`.
The coefficients are the ordered-tuple counts of the
exponent patterns of `(Σ_P x_P)⁶` over the eleven
partitions of `6`, in the same un-divided assembly
shape as `kappa5Const`. The patterns on at most 3
distinct columns — `(6)`, `(5,1)`, `(4,2)`, `(4,1,1)`,
`(3,3)`, `(3,2,1)`, `(2,2,2)` — enter at their full
values (they factor into constants at arbitrary
exponents). The patterns `(3,1,1,1)`, `(2,2,1,1)`,
`(2,1,1,1,1)` and `(1,1,1,1,1,1)` enter only through
their fully-split baselines `A₃B³` resp. `A₂²B²`
resp. `A₂B⁴` resp. `B⁶`: their dependent excesses are
the content of `kappa6dep`, whose channel content is
B6-1b / B6-2 territory and is not asserted here. -/
noncomputable def kappa6Const : ℝ :=
  colCount N * densMomentValue ρ μG 6
    + 6 * colCount N * (colCount N - 1)
      * densMomentValue ρ μG 5 * (1 - e1 ρ μG / (d : ℝ))
    + 15 * colCount N * (colCount N - 1)
      * densMomentValue ρ μG 4 * densMomentValue ρ μG 2
    + 15 * colCount N * (colCount N - 1) * (colCount N - 2)
      * densMomentValue ρ μG 4 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
    + 10 * colCount N * (colCount N - 1)
      * (densMomentValue ρ μG 3) ^ 2
    + 60 * colCount N * (colCount N - 1) * (colCount N - 2)
      * densMomentValue ρ μG 3 * densMomentValue ρ μG 2
      * (1 - e1 ρ μG / (d : ℝ))
    + 20 * colCount N * (colCount N - 1) * (colCount N - 2)
      * (colCount N - 3)
      * densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
    + 15 * colCount N * (colCount N - 1) * (colCount N - 2)
      * (densMomentValue ρ μG 2) ^ 3
    + 45 * colCount N * (colCount N - 1) * (colCount N - 2)
      * (colCount N - 3)
      * (densMomentValue ρ μG 2) ^ 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
    + 15 * colCount N * (colCount N - 1) * (colCount N - 2)
      * (colCount N - 3) * (colCount N - 4)
      * densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 4
    + colCount N * (colCount N - 1) * (colCount N - 2)
      * (colCount N - 3) * (colCount N - 4) * (colCount N - 5)
      * (1 - e1 ρ μG / (d : ℝ)) ^ 6

/-- **Coefficient audit of the constant assembly.** If
every pattern value is `1` (`Aⱼ = 1` for all `j` and
`B = 1`), the assembly totals `M⁶` — the number of
ordered 6-tuples of columns. This checks the eleven
pattern coefficients and falling-factorial factors of
`kappa6Const` against the raw tuple count, in the
same way the order-5 assembly's coefficients total
`M⁵`. -/
theorem kappa6Const_eq_pow_six_of_moments_one
    (hA : ∀ j, densMomentValue ρ μG j = 1)
    (hB : 1 - e1 ρ μG / (d : ℝ) = 1) :
    kappa6Const (N := N) ρ μG = (colCount N) ^ 6 := by
  unfold kappa6Const
  rw [hA 6, hA 5, hA 4, hA 3, hA 2, hB]
  ring

/-- **κ₆^dep**, the dependent part of the β⁶
coefficient: what remains of `betaCoeff6` after the
closed constant part is removed. Its content is the
new channels named in the header (C6 / Θ(2,2,2) /
(2,2,1,1) / (3,1,1,1)); the channel definitions are
B6-1b's content and the assembly identity expressing
`kappa6dep` through dressings and those channels is
B6-2's seam, named in the header and **not** asserted
here. No sign is asserted for it anywhere. -/
noncomputable def kappa6dep (u u' : LayerLink N → G) : ℝ :=
  betaCoeff6 ρ μG u u' - kappa6Const (N := N) ρ μG / 720

/-- `κ₆^dep` unfolds to its defining difference. -/
theorem kappa6dep_def (u u' : LayerLink N → G) :
    kappa6dep ρ μG u u'
      = betaCoeff6 ρ μG u u' - kappa6Const (N := N) ρ μG / 720 :=
  rfl

end ClosedForm6

section Distinct6

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- The character moment of a finite set of columns at
order 6: `∫ ∏_{P ∈ C} Re χ(word_P)`, the raw
(un-cumulanted) moment of the all-distinct
`(1,1,1,1,1,1)` channel when `C` has six elements.
Defined by the same construction as `pentaReMoment`
(which is the same integral at any support size). The
channel expressions as sums over the card-6 supports
named by B6-0 — the `C₆` and `Θ(2,2,2)` patterns — are
B6-2's work and are **not** asserted here. -/
noncomputable def hexaReMoment (C : Finset (LayerColumn N))
    (u u' : LayerLink N → G) : ℝ :=
  ∫ α, ∏ P ∈ C, colRe ρ u u' P α
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- The order-6 distinct moment is `quadReMoment`
itself: the moment construction is support-size
blind, and the order-4 machinery applies verbatim. -/
theorem hexaReMoment_eq_quadReMoment
    (C : Finset (LayerColumn N)) (u u' : LayerLink N → G) :
    hexaReMoment ρ μG C u u' = quadReMoment ρ μG C u u' :=
  rfl

end Distinct6

section Channel6

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- The raw `(3,1,1,1)` moment at a 4-support `C` with
distinguished tripled column `P`: the stratum integral
of `(colRe P)³ · ∏_{Q ∈ C.erase P} colRe Q` — the
character moment of the multiset `C + {P, P}` (the
support `C` with `P` counted three times). This is the
order-6 analogue of `doubledQuadReMoment`: at order 6
the surviving dependent supports on primitive quads
carry the `(3,1,1,1)` and `(2,2,1,1)` patterns
(B6-0). -/
noncomputable def tripledQuadReMoment
    (C : Finset (LayerColumn N)) (P : LayerColumn N)
    (u u' : LayerLink N → G) : ℝ :=
  ∫ α, (colRe ρ u u' P α) ^ 3
      * ∏ Q ∈ C.erase P, colRe ρ u u' Q α
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- The raw `(2,2,1,1)` moment at a 4-support `C` with
distinguished doubled columns `P` and `Q`: the stratum
integral of
`(colRe P)² · (colRe Q)² · ∏_{R ∈ (C.erase P).erase Q}
colRe R` — the character moment of the multiset
`C + {P, Q}` (the support `C` with each of `P`, `Q`
counted twice). -/
noncomputable def doubledDoubledQuadReMoment
    (C : Finset (LayerColumn N)) (P Q : LayerColumn N)
    (u u' : LayerLink N → G) : ℝ :=
  ∫ α, (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
      * ∏ R ∈ (C.erase P).erase Q, colRe ρ u u' R α
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- The tripled moment is the multiset moment: for
`P ∈ C` it equals the integral of the full support
product times two more factors of the tripled column,
`∫ (∏_{Q ∈ C} colRe Q) · (colRe P)²`. -/
theorem tripledQuadReMoment_eq_mul
    {C : Finset (LayerColumn N)} {P : LayerColumn N}
    (hPC : P ∈ C) (u u' : LayerLink N → G) :
    tripledQuadReMoment ρ μG C P u u'
      = ∫ α, (∏ Q ∈ C, colRe ρ u u' Q α) * (colRe ρ u u' P α) ^ 2
        ∂(Measure.pi fun _ : LayerSite N => μG) := by
  refine integral_congr_ae
    (Filter.Eventually.of_forall fun α => ?_)
  show (colRe ρ u u' P α) ^ 3
      * ∏ Q ∈ C.erase P, colRe ρ u u' Q α
      = (∏ Q ∈ C, colRe ρ u u' Q α) * (colRe ρ u u' P α) ^ 2
  rw [← Finset.mul_prod_erase C (fun Q => colRe ρ u u' Q α) hPC]
  ring

/-- The doubled-doubled moment is the multiset moment:
for distinct `P, Q ∈ C` it equals the integral of the
full support product times one more factor of each
doubled column,
`∫ (∏_{R ∈ C} colRe R) · colRe P · colRe Q`. -/
theorem doubledDoubledQuadReMoment_eq_mul
    {C : Finset (LayerColumn N)} {P Q : LayerColumn N}
    (hPC : P ∈ C) (hQC : Q ∈ C) (hQP : Q ≠ P)
    (u u' : LayerLink N → G) :
    doubledDoubledQuadReMoment ρ μG C P Q u u'
      = ∫ α, (∏ R ∈ C, colRe ρ u u' R α)
          * colRe ρ u u' P α * colRe ρ u u' Q α
        ∂(Measure.pi fun _ : LayerSite N => μG) := by
  have hQmem : Q ∈ C.erase P :=
    Finset.mem_erase.mpr ⟨hQP, hQC⟩
  refine integral_congr_ae
    (Filter.Eventually.of_forall fun α => ?_)
  show (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
      * ∏ R ∈ (C.erase P).erase Q, colRe ρ u u' R α
      = (∏ R ∈ C, colRe ρ u u' R α)
        * colRe ρ u u' P α * colRe ρ u u' Q α
  rw [← Finset.mul_prod_erase C (fun R => colRe ρ u u' R α) hPC,
    ← Finset.mul_prod_erase (C.erase P)
      (fun R => colRe ρ u u' R α) hQmem]
  ring

/-- **The `(3,1,1,1)` channel expression**: the sum,
over primitive quads `C` and distinguished columns
`P ∈ C`, of the tripled-column moments. This is a raw
channel expression only: the assembly identity
expressing `kappa6dep` through dressings and channel
excesses is B6-2's seam and is **not** asserted here,
and no baseline is subtracted inside this definition
(excess formation is B6-2's). No sign is asserted for
this sum. -/
noncomputable def kappa6chan3111 (u u' : LayerLink N → G) : ℝ :=
  ∑ C ∈ primitiveQuads, ∑ P ∈ C,
    tripledQuadReMoment ρ μG C P u u'

/-- **The `(2,2,1,1)` channel expression**: the sum,
over primitive quads `C` and ordered pairs of distinct
distinguished columns `P ∈ C`, `Q ∈ C.erase P`, of the
doubled-doubled moments. Raw channel expression only,
on the same fence as `kappa6chan3111`: no assembly
identity and no sign is asserted here. The
adjacent/opposite split of the pair `(P, Q)` within a
quad is the B6-PROBE's seat-level concern and is not
defined here: the corpus owns no column adjacency
predicate for quads (the `colAdj` of the polymer line
is a base-site adjacency, not a quad adjacency), so
the split is deferred to the probe. -/
noncomputable def kappa6chan2211 (u u' : LayerLink N → G) : ℝ :=
  ∑ C ∈ primitiveQuads, ∑ P ∈ C, ∑ Q ∈ C.erase P,
    doubledDoubledQuadReMoment ρ μG C P Q u u'

/-- **Strip at the tripled column.** If the tripled
column `P` itself has a private site `s` within the
support `C` (no other column of `C` reads `s`), the
tripled moment splits off the third real moment:
`tripledQuadReMoment C P = realMoment 3 ·
quadReMoment (C.erase P)`. The exponent-blind strip
`integral_colRe_pow_split_finset` at exponents
`(1, 3)`, following `doubledQuadReMoment_strip_doubled`
verbatim with the doubled exponent replaced by `3`.
So a tripled column at a private site carries no
dependent content: the channel's content needs the
tripled column's sites shared. -/
theorem tripledQuadReMoment_strip_tripled (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    {P : LayerColumn N} {s : LayerSite N}
    (hsP : s ∈ colSites P)
    (hpriv : ∀ Y ∈ C, Y ≠ P → s ∉ colSites Y) :
    tripledQuadReMoment ρ μG C P u u'
      = realMoment ρ μG 3 * quadReMoment ρ μG (C.erase P) u u' := by
  classical
  have hPF : P ∉ C.erase P :=
    fun h => (Finset.mem_erase.mp h).1 rfl
  have hsF : ∀ Q ∈ C.erase P, s ∉ colSites Q :=
    fun Q hQ => hpriv Q (Finset.mem_erase.mp hQ).2
      (Finset.mem_erase.mp hQ).1
  have hpt : ∀ α : LayerSite N → G,
      (colRe ρ u u' P α) ^ 3
          * ∏ Q ∈ C.erase P, colRe ρ u u' Q α
        = (∏ Q ∈ C.erase P,
            (colRe ρ u u' Q α) ^ ((fun _ : LayerColumn N => 1) Q))
          * (colRe ρ u u' P α) ^ (3 : ℕ) := fun α => by
    simp only [pow_one]
    ring
  calc tripledQuadReMoment ρ μG C P u u'
      = ∫ α : LayerSite N → G,
          (∏ Q ∈ C.erase P,
            (colRe ρ u u' Q α) ^ ((fun _ : LayerColumn N => 1) Q))
            * (colRe ρ u u' P α) ^ (3 : ℕ)
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = realMoment ρ μG 3
          * ∫ α : LayerSite N → G, ∏ Q ∈ C.erase P,
              (colRe ρ u u' Q α) ^ ((fun _ : LayerColumn N => 1) Q)
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_colRe_pow_split_finset ρ μG hN hN3 hρcont u u'
          (C.erase P) (fun _ => 1) P hPF s hsP hsF 3
    _ = realMoment ρ μG 3
          * quadReMoment ρ μG (C.erase P) u u' := by
        refine congrArg _ ?_
        refine integral_congr_ae
          (Filter.Eventually.of_forall fun α => ?_)
        exact Finset.prod_congr rfl fun Q _ => pow_one _

/-- **Strip at a single column.** If a single (untripled)
column `Q ∈ C`, `Q ≠ P`, has a private site `s` within
the support `C`, the tripled moment splits off the
single-site mean:
`tripledQuadReMoment C P = e₁ · tripledQuadReMoment
(C.erase Q) P`. The exponent-blind strip at exponent
function `(3 at P, 1 elsewhere)` and `k = 1`, following
`doubledQuadReMoment_strip_single` verbatim with the
doubled exponent replaced by `3`. Together with
`tripledQuadReMoment_strip_tripled`: at a non-primitive
support every tripled moment reduces to lower content,
so the `(3,1,1,1)` channel's dependent content is
carried by the primitive quads — exactly the supports
`kappa6chan3111` sums over. -/
theorem tripledQuadReMoment_strip_single (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    {P Q : LayerColumn N} (hPC : P ∈ C) (hQC : Q ∈ C)
    (hQP : Q ≠ P) {s : LayerSite N}
    (hsQ : s ∈ colSites Q)
    (hpriv : ∀ Y ∈ C, Y ≠ Q → s ∉ colSites Y) :
    tripledQuadReMoment ρ μG C P u u'
      = e1 ρ μG * tripledQuadReMoment ρ μG (C.erase Q) P u u' := by
  classical
  set a : LayerColumn N → ℕ := fun R => if R = P then 3 else 1
    with ha_def
  have haP : a P = 3 := by
    rw [ha_def]
    exact if_pos rfl
  have haR : ∀ R ∈ (C.erase Q).erase P, a R = 1 := by
    intro R hR
    rw [ha_def]
    exact if_neg (Finset.mem_erase.mp hR).1
  have hPF : P ∉ (C.erase Q).erase P :=
    fun h => (Finset.mem_erase.mp h).1 rfl
  have hQF : Q ∉ insert P ((C.erase Q).erase P) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hQP h
    · exact (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).1 rfl
  have hsF : ∀ R ∈ insert P ((C.erase Q).erase P),
      s ∉ colSites R := by
    intro R hR
    apply hpriv R _ _
    · rcases Finset.mem_insert.mp hR with rfl | hR
      · exact hPC
      · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).2
    · rintro rfl
      exact hQF hR
  have hcomm : (C.erase P).erase Q = (C.erase Q).erase P := by
    ext R
    simp only [Finset.mem_erase]
    tauto
  have hQmemP : Q ∈ C.erase P := Finset.mem_erase.mpr ⟨hQP, hQC⟩
  have h1 : ∀ α : LayerSite N → G,
      ∏ R ∈ C.erase P, colRe ρ u u' R α
        = colRe ρ u u' Q α
          * ∏ R ∈ (C.erase Q).erase P, colRe ρ u u' R α := by
    intro α
    rw [← hcomm]
    exact (Finset.mul_prod_erase (C.erase P)
      (fun R => colRe ρ u u' R α) hQmemP).symm
  have h2 : ∀ α : LayerSite N → G,
      ∏ R ∈ insert P ((C.erase Q).erase P),
          (colRe ρ u u' R α) ^ (a R)
        = (colRe ρ u u' P α) ^ 3
          * ∏ R ∈ (C.erase Q).erase P, colRe ρ u u' R α := by
    intro α
    rw [Finset.prod_insert hPF, haP]
    refine congrArg _ ?_
    exact Finset.prod_congr rfl fun R hR => by rw [haR R hR, pow_one]
  have hpt1 : ∀ α : LayerSite N → G,
      (colRe ρ u u' P α) ^ 3 * ∏ R ∈ C.erase P, colRe ρ u u' R α
        = (∏ R ∈ insert P ((C.erase Q).erase P),
            (colRe ρ u u' R α) ^ (a R))
          * (colRe ρ u u' Q α) ^ (1 : ℕ) := by
    intro α
    rw [h1 α, h2 α]
    simp only [pow_one]
    ring
  calc tripledQuadReMoment ρ μG C P u u'
      = ∫ α : LayerSite N → G,
          (∏ R ∈ insert P ((C.erase Q).erase P),
            (colRe ρ u u' R α) ^ (a R))
            * (colRe ρ u u' Q α) ^ (1 : ℕ)
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt1)
    _ = realMoment ρ μG 1
          * ∫ α : LayerSite N → G,
              ∏ R ∈ insert P ((C.erase Q).erase P),
                (colRe ρ u u' R α) ^ (a R)
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_colRe_pow_split_finset ρ μG hN hN3 hρcont u u'
          (insert P ((C.erase Q).erase P)) a Q hQF s hsQ hsF 1
    _ = e1 ρ μG * tripledQuadReMoment ρ μG (C.erase Q) P u u' := by
        rw [realMoment_one]
        refine congrArg _ ?_
        exact integral_congr_ae (Filter.Eventually.of_forall h2)

/-- **Strip at the first doubled column.** If the
doubled column `P` has a private site `s` within the
support `C`, the doubled-doubled moment splits off the
second real moment, leaving the `(2,1,1)` moment of
the erased support at `Q`:
`doubledDoubledQuadReMoment C P Q = realMoment 2 ·
doubledQuadReMoment (C.erase P) Q`. The exponent-blind
strip at exponent function `(2 at Q, 1 elsewhere)` on
`C.erase P` and `k = 2` — the exponent-function form of
the Beta5 strip pattern (as in
`doubledQuadReMoment_strip_single`). -/
theorem doubledDoubledQuadReMoment_strip_first (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    {P Q : LayerColumn N} (hQC : Q ∈ C) (hQP : Q ≠ P)
    {s : LayerSite N}
    (hsP : s ∈ colSites P)
    (hpriv : ∀ Y ∈ C, Y ≠ P → s ∉ colSites Y) :
    doubledDoubledQuadReMoment ρ μG C P Q u u'
      = realMoment ρ μG 2
        * doubledQuadReMoment ρ μG (C.erase P) Q u u' := by
  classical
  set a : LayerColumn N → ℕ := fun R => if R = Q then 2 else 1
    with ha_def
  have haQ : a Q = 2 := by
    rw [ha_def]
    exact if_pos rfl
  have haR : ∀ R ∈ (C.erase P).erase Q, a R = 1 := by
    intro R hR
    rw [ha_def]
    exact if_neg (Finset.mem_erase.mp hR).1
  have hPF : P ∉ C.erase P :=
    fun h => (Finset.mem_erase.mp h).1 rfl
  have hsF : ∀ Y ∈ C.erase P, s ∉ colSites Y :=
    fun Y hY => hpriv Y (Finset.mem_erase.mp hY).2
      (Finset.mem_erase.mp hY).1
  have hQmem : Q ∈ C.erase P := Finset.mem_erase.mpr ⟨hQP, hQC⟩
  have hprod : ∀ α : LayerSite N → G,
      ∏ Y ∈ C.erase P, (colRe ρ u u' Y α) ^ (a Y)
        = (colRe ρ u u' Q α) ^ 2
          * ∏ R ∈ (C.erase P).erase Q, colRe ρ u u' R α := by
    intro α
    rw [← Finset.mul_prod_erase (C.erase P)
      (fun Y => (colRe ρ u u' Y α) ^ (a Y)) hQmem, haQ]
    refine congrArg _ ?_
    exact Finset.prod_congr rfl fun R hR => by
      rw [haR R hR, pow_one]
  have hpt : ∀ α : LayerSite N → G,
      (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
          * ∏ R ∈ (C.erase P).erase Q, colRe ρ u u' R α
        = (∏ Y ∈ C.erase P, (colRe ρ u u' Y α) ^ (a Y))
          * (colRe ρ u u' P α) ^ (2 : ℕ) := fun α => by
    rw [hprod α]
    ring
  calc doubledDoubledQuadReMoment ρ μG C P Q u u'
      = ∫ α : LayerSite N → G,
          (∏ Y ∈ C.erase P, (colRe ρ u u' Y α) ^ (a Y))
            * (colRe ρ u u' P α) ^ (2 : ℕ)
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = realMoment ρ μG 2
          * ∫ α : LayerSite N → G,
              ∏ Y ∈ C.erase P, (colRe ρ u u' Y α) ^ (a Y)
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_colRe_pow_split_finset ρ μG hN hN3 hρcont u u'
          (C.erase P) a P hPF s hsP hsF 2
    _ = realMoment ρ μG 2
          * doubledQuadReMoment ρ μG (C.erase P) Q u u' := by
        refine congrArg _ ?_
        exact integral_congr_ae (Filter.Eventually.of_forall hprod)

/-- **Strip at the second doubled column.** If the
doubled column `Q` has a private site `s` within the
support `C`, the doubled-doubled moment splits off the
second real moment, leaving the `(2,1,1)` moment of
the erased support at `P`:
`doubledDoubledQuadReMoment C P Q = realMoment 2 ·
doubledQuadReMoment (C.erase Q) P`. The same strip as
`doubledDoubledQuadReMoment_strip_first` with the two
doubled columns exchanged (the erase factors commute). -/
theorem doubledDoubledQuadReMoment_strip_second (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    {P Q : LayerColumn N} (hPC : P ∈ C) (hQP : Q ≠ P)
    {s : LayerSite N}
    (hsQ : s ∈ colSites Q)
    (hpriv : ∀ Y ∈ C, Y ≠ Q → s ∉ colSites Y) :
    doubledDoubledQuadReMoment ρ μG C P Q u u'
      = realMoment ρ μG 2
        * doubledQuadReMoment ρ μG (C.erase Q) P u u' := by
  classical
  set a : LayerColumn N → ℕ := fun R => if R = P then 2 else 1
    with ha_def
  have haP : a P = 2 := by
    rw [ha_def]
    exact if_pos rfl
  have haR : ∀ R ∈ (C.erase Q).erase P, a R = 1 := by
    intro R hR
    rw [ha_def]
    exact if_neg (Finset.mem_erase.mp hR).1
  have hQF : Q ∉ C.erase Q :=
    fun h => (Finset.mem_erase.mp h).1 rfl
  have hsF : ∀ Y ∈ C.erase Q, s ∉ colSites Y :=
    fun Y hY => hpriv Y (Finset.mem_erase.mp hY).2
      (Finset.mem_erase.mp hY).1
  have hPmem : P ∈ C.erase Q :=
    Finset.mem_erase.mpr ⟨fun h => hQP h.symm, hPC⟩
  have hcomm : (C.erase P).erase Q = (C.erase Q).erase P := by
    ext R
    simp only [Finset.mem_erase]
    tauto
  have hprod : ∀ α : LayerSite N → G,
      ∏ Y ∈ C.erase Q, (colRe ρ u u' Y α) ^ (a Y)
        = (colRe ρ u u' P α) ^ 2
          * ∏ R ∈ (C.erase Q).erase P, colRe ρ u u' R α := by
    intro α
    rw [← Finset.mul_prod_erase (C.erase Q)
      (fun Y => (colRe ρ u u' Y α) ^ (a Y)) hPmem, haP]
    refine congrArg _ ?_
    exact Finset.prod_congr rfl fun R hR => by
      rw [haR R hR, pow_one]
  have hpt : ∀ α : LayerSite N → G,
      (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
          * ∏ R ∈ (C.erase P).erase Q, colRe ρ u u' R α
        = (∏ Y ∈ C.erase Q, (colRe ρ u u' Y α) ^ (a Y))
          * (colRe ρ u u' Q α) ^ (2 : ℕ) := fun α => by
    rw [hcomm, hprod α]
    ring
  calc doubledDoubledQuadReMoment ρ μG C P Q u u'
      = ∫ α : LayerSite N → G,
          (∏ Y ∈ C.erase Q, (colRe ρ u u' Y α) ^ (a Y))
            * (colRe ρ u u' Q α) ^ (2 : ℕ)
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = realMoment ρ μG 2
          * ∫ α : LayerSite N → G,
              ∏ Y ∈ C.erase Q, (colRe ρ u u' Y α) ^ (a Y)
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_colRe_pow_split_finset ρ μG hN hN3 hρcont u u'
          (C.erase Q) a Q hQF s hsQ hsF 2
    _ = realMoment ρ μG 2
          * doubledQuadReMoment ρ μG (C.erase Q) P u u' := by
        refine congrArg _ ?_
        exact integral_congr_ae (Filter.Eventually.of_forall hprod)

/-- **Strip at a single column.** If a single (undoubled)
column `R ∈ C`, distinct from both doubled columns,
has a private site `s` within the support `C`, the
doubled-doubled moment splits off the single-site
mean:
`doubledDoubledQuadReMoment C P Q = e₁ ·
doubledDoubledQuadReMoment (C.erase R) P Q`. The
exponent-blind strip at exponent function `(2 at P,
2 at Q, 1 elsewhere)` and `k = 1`, following
`doubledQuadReMoment_strip_single` with a second
doubled column carried through the exponent function.
Together with the two doubled-column strips: at a
non-primitive support every doubled-doubled moment
reduces to lower content, so the `(2,2,1,1)` channel's
dependent content is carried by the primitive quads —
exactly the supports `kappa6chan2211` sums over. -/
theorem doubledDoubledQuadReMoment_strip_single (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    {P Q R : LayerColumn N} (hPC : P ∈ C) (hQC : Q ∈ C)
    (hRC : R ∈ C) (hRP : R ≠ P) (hRQ : R ≠ Q) (hQP : Q ≠ P)
    {s : LayerSite N}
    (hsR : s ∈ colSites R)
    (hpriv : ∀ Y ∈ C, Y ≠ R → s ∉ colSites Y) :
    doubledDoubledQuadReMoment ρ μG C P Q u u'
      = e1 ρ μG
        * doubledDoubledQuadReMoment ρ μG (C.erase R) P Q u u' := by
  classical
  set T0 : Finset (LayerColumn N) :=
    ((C.erase R).erase P).erase Q with hT0_def
  set a : LayerColumn N → ℕ :=
    fun Y => if Y = P then 2 else if Y = Q then 2 else 1
    with ha_def
  have haP : a P = 2 := by
    rw [ha_def]
    exact if_pos rfl
  have haQ : a Q = 2 := by
    rw [ha_def]
    exact (if_neg hQP).trans (if_pos rfl)
  have haT0 : ∀ Y ∈ T0, a Y = 1 := by
    intro Y hY
    have hYP : Y ≠ P :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hY).2).1
    have hYQ : Y ≠ Q := (Finset.mem_erase.mp hY).1
    rw [ha_def]
    exact (if_neg hYP).trans (if_neg hYQ)
  have hQnotT0 : Q ∉ T0 :=
    fun h => (Finset.mem_erase.mp h).1 rfl
  have hPnotT1 : P ∉ insert Q T0 := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hQP h.symm
    · exact (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).1 rfl
  have hRnotT : R ∉ insert P (insert Q T0) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hRP h
    · rcases Finset.mem_insert.mp h with h | h
      · exact hRQ h
      · exact (Finset.mem_erase.mp
          (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).2).1 rfl
  have hsF : ∀ Y ∈ insert P (insert Q T0), s ∉ colSites Y := by
    intro Y hY
    apply hpriv Y _ _
    · rcases Finset.mem_insert.mp hY with rfl | hY
      · exact hPC
      · rcases Finset.mem_insert.mp hY with rfl | hY
        · exact hQC
        · exact (Finset.mem_erase.mp
            (Finset.mem_erase.mp (Finset.mem_erase.mp hY).2).2).2
    · rintro rfl
      exact hRnotT hY
  have hcommR : ((C.erase P).erase Q).erase R = T0 := by
    rw [hT0_def]
    ext Z
    simp only [Finset.mem_erase]
    tauto
  have hRmem : R ∈ (C.erase P).erase Q :=
    Finset.mem_erase.mpr ⟨hRQ, Finset.mem_erase.mpr ⟨hRP, hRC⟩⟩
  have hsplit : ∀ α : LayerSite N → G,
      ∏ Z ∈ (C.erase P).erase Q, colRe ρ u u' Z α
        = colRe ρ u u' R α
          * ∏ Z ∈ T0, colRe ρ u u' Z α := by
    intro α
    rw [← hcommR]
    exact (Finset.mul_prod_erase ((C.erase P).erase Q)
      (fun Z => colRe ρ u u' Z α) hRmem).symm
  have hprodT : ∀ α : LayerSite N → G,
      ∏ Y ∈ insert P (insert Q T0), (colRe ρ u u' Y α) ^ (a Y)
        = (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
          * ∏ Z ∈ T0, colRe ρ u u' Z α := by
    intro α
    have hT0prod : ∏ Z ∈ T0, (colRe ρ u u' Z α) ^ (a Z)
        = ∏ Z ∈ T0, colRe ρ u u' Z α :=
      Finset.prod_congr rfl fun Z hZ => by
        rw [haT0 Z hZ, pow_one]
    rw [Finset.prod_insert hPnotT1, Finset.prod_insert hQnotT0,
      haP, haQ, hT0prod]
    ring
  have hpt1 : ∀ α : LayerSite N → G,
      (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
          * ∏ Z ∈ (C.erase P).erase Q, colRe ρ u u' Z α
        = (∏ Y ∈ insert P (insert Q T0),
            (colRe ρ u u' Y α) ^ (a Y))
          * (colRe ρ u u' R α) ^ (1 : ℕ) := by
    intro α
    rw [hsplit α, hprodT α]
    simp only [pow_one]
    ring
  calc doubledDoubledQuadReMoment ρ μG C P Q u u'
      = ∫ α : LayerSite N → G,
          (∏ Y ∈ insert P (insert Q T0),
            (colRe ρ u u' Y α) ^ (a Y))
            * (colRe ρ u u' R α) ^ (1 : ℕ)
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt1)
    _ = realMoment ρ μG 1
          * ∫ α : LayerSite N → G,
              ∏ Y ∈ insert P (insert Q T0),
                (colRe ρ u u' Y α) ^ (a Y)
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_colRe_pow_split_finset ρ μG hN hN3 hρcont u u'
          (insert P (insert Q T0)) a R hRnotT s hsR hsF 1
    _ = e1 ρ μG
          * doubledDoubledQuadReMoment ρ μG (C.erase R) P Q
            u u' := by
        rw [realMoment_one]
        refine congrArg _ ?_
        exact integral_congr_ae (Filter.Eventually.of_forall hprodT)

end Channel6

end ThetLogos
