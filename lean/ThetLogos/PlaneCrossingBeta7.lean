/-
# ThetLogos.PlaneCrossingBeta7 — the β⁷ coefficient at
general (G, ρ): core definitions only (B7-1a)

**Fences, up front.** NO CLAIM. Parts of the Clay
Yang–Mills statement closed by this module: **0**. Dials
0/4. This is a DEFINITION brick (B7-1a): it owns the seventh
Taylor coefficient of the layer kernel `𝒜 = layerKernel`
at general `(G, ρ)`, its constant part in the assembly's
pattern values, and its dependent part `κ₇^dep` under the
same distinct-support cumulant fence as orders 4, 5 and 6.
Definitions and Taylor-coefficient identities only.
**No sign is asserted for `betaCoeff7`, `kappa7dep`, or
any part of them anywhere in this module**, and no
positivity of `𝒜` at any `β` follows: the β⁷ general
sign is FRONTIER — its new channels carry still higher
entry multiplicities at a site than the order-6 channels,
on top of the still-unowned (2,1) triple twirl that
already blocks the β⁵ general sign, and no twirl theory
for any of these exists in the tree.

**The decision kernel.** The probe that will read this
order works on
`K₆ := ker κ₄^dep ∩ ker κ₅^dep ∩ ker κ₆^dep`,
the joint kernel on which every dressing of orders 4, 5
and 6 vanishes by construction, so that β⁷ is the first
order that can decide those directions. That probe
(B7-PROBE) is held behind GD-PROBE and is **not** part
of this brick; nothing here fires, discharges, or
prejudges it, and no K-K7 verdict is asserted here.

**What is NOT here.** The channel content of
`kappa7dep` — the order-7 channels named by B7-0's
landed selection (`ThetLogos.OrderSevenSelection`):
`(4,1,1,1)`, `(3,2,1,1)` (adjacent / opposite) and
`(2,2,2,1)` on primitive quads, `(2,1,1,1,1,1)` on the
`C₆` and `Θ(2,2,2)` supports, and `(1⁷)` on the
`Θ(1,3,3)` book support — is B7-1b / B7-2 territory and
is **not** asserted here. No assembly identity
expressing `kappa7dep` through dressings and channel
excesses is asserted here; that identity is B7-2's
seam, named here only as a seam. The channel
definitions themselves follow in B7-1b, into this same
module's later sections.

**The named-space fence (inherited).** "Dependent
part" means the cumulant over partitions of the
DISTINCT-column support, exactly as at orders 4, 5
and 6: patterns on at most 3 distinct columns factor
into constants at arbitrary exponents, so the constant
assembly below carries their full values; patterns on
4, 5, 6 and 7 distinct columns enter the constant part
only through their fully-split baselines, and their
dependent excesses are the content of `kappa7dep`.
The `N = 2` sector and the `N = 4` wrap sector are
fenced exactly as at orders 4, 5 and 6.

**What this module (B7-1a) proves.** (i) The order-7
expansion of the stratum average, real form, with tail
`R₈`. (ii) The coefficient audit of the constant
assembly: under all pattern values `1`, `kappa7Const`
totals `M⁷`, the number of ordered 7-tuples of columns.
-/

import ThetLogos.PlaneCrossingBeta6
import ThetLogos.OrderSevenSelection

open MeasureTheory Finset

namespace ThetLogos

section Coeff7

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- The seventh β-coefficient of `𝒜`: `∫ layerDensSum⁷ / 5040`
(so `𝒜 = 1 − βC₁ + β²C₂ − β³C₃ + β⁴C₄ − β⁵C₅ + β⁶C₆
− β⁷C₇ + O(β⁸)`).
Defined by the same construction as `betaCoeff6`. -/
noncomputable def betaCoeff7 (u u' : LayerLink N → G) : ℝ :=
  ∫ α, (layerDensSum ρ α u u') ^ 7 / 5040
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- **The expansion, real form, at order 7.** For every
real `β`, the stratum average of the layer exponential
is `1 − βC₁ + β²C₂ − β³C₃ + β⁴C₄ − β⁵C₅ + β⁶C₆ − β⁷C₇
+ R₈(β)` with `R₈` the displayed tail series. FENCE: a
Taylor coefficient identity; no positivity of `𝒜` at
any `β > 0` follows, and no sign for `betaCoeff7` or
any part of it is asserted. Proved by the order-6
pattern (`layerKernel_real_expansion6`) with one more
term split off. -/
theorem layerKernel_real_expansion7 (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) :
    ∫ α, Real.exp (-(β * layerDensSum ρ α u u'))
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = 1 - β * betaCoeff1 ρ μG u u' + β ^ 2 * betaCoeff2 ρ μG u u'
        - β ^ 3 * betaCoeff3 ρ μG u u'
        + β ^ 4 * betaCoeff4 ρ μG u u'
        - β ^ 5 * betaCoeff5 ρ μG u u'
        + β ^ 6 * betaCoeff6 ρ μG u u'
        - β ^ 7 * betaCoeff7 ρ μG u u'
        + ∑' (k : ℕ), ∫ α, (-β * layerDensSum ρ α u u') ^ (k + 8)
            / ((Nat.factorial (k + 8) : ℝ))
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
  have ht7 : (∫ α, (-β * layerDensSum ρ α u u') ^ 7
        / ((Nat.factorial 7 : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = -β ^ 7 * betaCoeff7 ρ μG u u' := by
    have hpt : ∀ α : LayerSite N → G,
        (-β * layerDensSum ρ α u u') ^ 7 / ((Nat.factorial 7 : ℝ))
          = -β ^ 7 * ((layerDensSum ρ α u u') ^ 7 / 5040) := by
      intro α
      have h7 : ((Nat.factorial 7 : ℝ)) = 5040 := by
        norm_num [Nat.factorial]
      rw [h7]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_const_mul _ _
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
    ← (hasSum_integral_of_summable_integral_norm
      (fun n => integrable_term ρ μG hN hρcont β u u' n)
      (summable_norm_term_int ρ μG hN hρcont β u u')).tsum_eq,
    ← hSumm.sum_add_tsum_nat_add 8,
    Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero,
    ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7]
  ring

end Coeff7

section ClosedForm7

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- The constant part of the seventh coefficient, in the
assembly's pattern values: with `M = colCount N`,
`B = 1 − e₁/d`, `Aⱼ = densMomentValue j`:
`M·A₇ + 7M(M−1)·A₆B + 21M(M−1)·A₅A₂
+ 21M(M−1)(M−2)·A₅B² + 35M(M−1)·A₄A₃
+ 105M(M−1)(M−2)·A₄A₂B + 35M(M−1)(M−2)(M−3)·A₄B³
+ 70M(M−1)(M−2)·A₃²B + 105M(M−1)(M−2)·A₃A₂²
+ 210M(M−1)(M−2)(M−3)·A₃A₂B²
+ 35M(M−1)(M−2)(M−3)(M−4)·A₃B⁴
+ 105M(M−1)(M−2)(M−3)·A₂³B
+ 105M(M−1)(M−2)(M−3)(M−4)·A₂²B³
+ 21M(M−1)(M−2)(M−3)(M−4)(M−5)·A₂B⁵
+ M(M−1)(M−2)(M−3)(M−4)(M−5)(M−6)·B⁷`.
The coefficients are the ordered-tuple counts of the
exponent patterns of `(Σ_P x_P)⁷` over the fifteen
partitions of `7`, in the same un-divided assembly
shape as `kappa6Const`. The patterns on at most 3
distinct columns — `(7)`, `(6,1)`, `(5,2)`, `(5,1,1)`,
`(4,3)`, `(4,2,1)`, `(3,3,1)`, `(3,2,2)` — enter at
their full values (they factor into constants at
arbitrary exponents). The patterns `(4,1,1,1)`,
`(3,2,1,1)`, `(3,1,1,1,1)`, `(2,2,2,1)`,
`(2,2,1,1,1)`, `(2,1,1,1,1,1)` and `(1,1,1,1,1,1,1)`
enter only through their fully-split baselines
`A₄B³` resp. `A₃A₂B²` resp. `A₃B⁴` resp. `A₂³B`
resp. `A₂²B³` resp. `A₂B⁵` resp. `B⁷`: their dependent
excesses are the content of `kappa7dep`, whose channel
content is B7-1b / B7-2 territory and is not asserted
here. -/
noncomputable def kappa7Const : ℝ :=
  colCount N * densMomentValue ρ μG 7
    + 7 * colCount N * (colCount N - 1)
      * densMomentValue ρ μG 6 * (1 - e1 ρ μG / (d : ℝ))
    + 21 * colCount N * (colCount N - 1)
      * densMomentValue ρ μG 5 * densMomentValue ρ μG 2
    + 21 * colCount N * (colCount N - 1) * (colCount N - 2)
      * densMomentValue ρ μG 5 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
    + 35 * colCount N * (colCount N - 1)
      * densMomentValue ρ μG 4 * densMomentValue ρ μG 3
    + 105 * colCount N * (colCount N - 1) * (colCount N - 2)
      * densMomentValue ρ μG 4 * densMomentValue ρ μG 2
      * (1 - e1 ρ μG / (d : ℝ))
    + 35 * colCount N * (colCount N - 1) * (colCount N - 2)
      * (colCount N - 3)
      * densMomentValue ρ μG 4 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
    + 70 * colCount N * (colCount N - 1) * (colCount N - 2)
      * (densMomentValue ρ μG 3) ^ 2 * (1 - e1 ρ μG / (d : ℝ))
    + 105 * colCount N * (colCount N - 1) * (colCount N - 2)
      * densMomentValue ρ μG 3 * (densMomentValue ρ μG 2) ^ 2
    + 210 * colCount N * (colCount N - 1) * (colCount N - 2)
      * (colCount N - 3)
      * densMomentValue ρ μG 3 * densMomentValue ρ μG 2
      * (1 - e1 ρ μG / (d : ℝ)) ^ 2
    + 35 * colCount N * (colCount N - 1) * (colCount N - 2)
      * (colCount N - 3) * (colCount N - 4)
      * densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 4
    + 105 * colCount N * (colCount N - 1) * (colCount N - 2)
      * (colCount N - 3)
      * (densMomentValue ρ μG 2) ^ 3 * (1 - e1 ρ μG / (d : ℝ))
    + 105 * colCount N * (colCount N - 1) * (colCount N - 2)
      * (colCount N - 3) * (colCount N - 4)
      * (densMomentValue ρ μG 2) ^ 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
    + 21 * colCount N * (colCount N - 1) * (colCount N - 2)
      * (colCount N - 3) * (colCount N - 4) * (colCount N - 5)
      * densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 5
    + colCount N * (colCount N - 1) * (colCount N - 2)
      * (colCount N - 3) * (colCount N - 4) * (colCount N - 5)
      * (colCount N - 6)
      * (1 - e1 ρ μG / (d : ℝ)) ^ 7

/-- **Coefficient audit of the constant assembly.** If
every pattern value is `1` (`Aⱼ = 1` for all `j` and
`B = 1`), the assembly totals `M⁷` — the number of
ordered 7-tuples of columns. This checks the fifteen
pattern coefficients and falling-factorial factors of
`kappa7Const` against the raw tuple count, in the
same way the order-6 assembly's coefficients total
`M⁶`. -/
theorem kappa7Const_eq_pow_seven_of_moments_one
    (hA : ∀ j, densMomentValue ρ μG j = 1)
    (hB : 1 - e1 ρ μG / (d : ℝ) = 1) :
    kappa7Const (N := N) ρ μG = (colCount N) ^ 7 := by
  unfold kappa7Const
  rw [hA 7, hA 6, hA 5, hA 4, hA 3, hA 2, hB]
  ring

/-- **κ₇^dep**, the dependent part of the β⁷
coefficient: what remains of `betaCoeff7` after the
closed constant part is removed. Its content is the
new channels named in the header (the primitive-quad
patterns `(4,1,1,1)` / `(3,2,1,1)` / `(2,2,2,1)`, the
`(2,1,1,1,1,1)` patterns on the `C₆` and `Θ(2,2,2)`
supports, and the `(1⁷)` pattern on the `Θ(1,3,3)`
book support); the channel definitions are B7-1b's
content and the assembly identity expressing
`kappa7dep` through dressings and those channels is
B7-2's seam, named in the header and **not** asserted
here. No sign is asserted for it anywhere. -/
noncomputable def kappa7dep (u u' : LayerLink N → G) : ℝ :=
  betaCoeff7 ρ μG u u' - kappa7Const (N := N) ρ μG / 5040

/-- `κ₇^dep` unfolds to its defining difference. -/
theorem kappa7dep_def (u u' : LayerLink N → G) :
    kappa7dep ρ μG u u'
      = betaCoeff7 ρ μG u u' - kappa7Const (N := N) ρ μG / 5040 :=
  rfl

end ClosedForm7

/-! ## B7-1b: channel definitions for the β⁷ LIVE list

The sections below are B7-1b's append to this module
(B7-1a's core above is unaltered). They own the raw
channel machinery and the channel expressions for
exactly the LIVE list of `ThetLogos.OrderSevenSelection`
(B7-0, landed): the primitive-quad patterns `(4,1,1,1)`,
`(3,2,1,1)` and `(2,2,2,1)`; the `(2,1,1,1,1,1)` pattern
on the `C₆` and `Θ(2,2,2)` supports; and the `(1⁷)`
pattern on the `Θ(1,3,3)` book support. Fences
unchanged: NO CLAIM, parts 0, dials 0/4, the β⁷ sign
FRONTIER, no sign asserted for any channel sum below,
and no excess defined here (excess formation is
assembly / B7-2 territory, as at B6-1).

**Deferral, on the face.** The primitive-quad channels
are sums over the owned family `primitiveQuads`. The
`C₆` / `Θ(2,2,2)` / `Θ(1,3,3)` support families are
**not** constructed here: their construction by
`univ.filter` over the B7-0 pattern predicates is
B7-2 territory (B6 precedent: B6-2a constructed
`c6Supports` / `thetaSupports`), so the channels on
those supports are given in raw per-support form
below, and the sums over the constructed families are
deferred to B7-2. No family is half-built here. -/

section Distinct7

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- The character moment of a finite set of columns at
order 7: `∫ ∏_{P ∈ C} Re χ(word_P)`, the raw
(un-cumulanted) moment of the all-distinct `(1⁷)`
channel when `C` has seven elements — the
multiplicity-free moment at the `Θ(1,3,3)` book
support. Defined by the same construction as
`hexaReMoment` (which is the same integral at any
support size). The channel expression as a sum over
the card-7 supports named by B7-0 is B7-2's work and
is **not** asserted here. -/
noncomputable def heptaReMoment (C : Finset (LayerColumn N))
    (u u' : LayerLink N → G) : ℝ :=
  ∫ α, ∏ P ∈ C, colRe ρ u u' P α
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- The order-7 distinct moment is `quadReMoment`
itself: the moment construction is support-size
blind, and the order-4 machinery applies verbatim. -/
theorem heptaReMoment_eq_quadReMoment
    (C : Finset (LayerColumn N)) (u u' : LayerLink N → G) :
    heptaReMoment ρ μG C u u' = quadReMoment ρ μG C u u' :=
  rfl

/-- The raw `(2,1,1,1,1,1)` moment at a 6-support `C`
with distinguished doubled column `P`: the stratum
integral of `(colRe P)² · ∏_{Q ∈ C.erase P} colRe Q`
— the character moment of the multiset `C + {P}` (the
support `C` with `P` counted twice). This is the
order-7 raw machinery on 6-supports, mirroring
`hexaReMoment`'s support at multiplicity pattern
`(2,1,1,1,1,1)`: at order 7 the LIVE 6-supports are
the `C₆` and `Θ(2,2,2)` patterns (B7-0), each carrying
exactly one doubled column. -/
noncomputable def doubledHexaReMoment
    (C : Finset (LayerColumn N)) (P : LayerColumn N)
    (u u' : LayerLink N → G) : ℝ :=
  ∫ α, (colRe ρ u u' P α) ^ 2
      * ∏ Q ∈ C.erase P, colRe ρ u u' Q α
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- The doubled 6-support moment is the multiset
moment: for `P ∈ C` it equals the integral of the
full support product times one more factor of the
doubled column,
`∫ (∏_{Q ∈ C} colRe Q) · colRe P`. -/
theorem doubledHexaReMoment_eq_mul
    {C : Finset (LayerColumn N)} {P : LayerColumn N}
    (hPC : P ∈ C) (u u' : LayerLink N → G) :
    doubledHexaReMoment ρ μG C P u u'
      = ∫ α, (∏ Q ∈ C, colRe ρ u u' Q α) * colRe ρ u u' P α
        ∂(Measure.pi fun _ : LayerSite N => μG) := by
  refine integral_congr_ae
    (Filter.Eventually.of_forall fun α => ?_)
  show (colRe ρ u u' P α) ^ 2
      * ∏ Q ∈ C.erase P, colRe ρ u u' Q α
      = (∏ Q ∈ C, colRe ρ u u' Q α) * colRe ρ u u' P α
  rw [← Finset.mul_prod_erase C (fun Q => colRe ρ u u' Q α) hPC]
  ring

/-- **The `(2,1,1,1,1,1)` channel on `C₆` supports, raw
per-support form**: for a single 6-support `C`, the
sum over its distinguished doubled columns `P ∈ C` of
the doubled 6-support moments. RAW FORM ONLY: the
`C₆` support family is not constructed in this brick
— its construction (B7-2, by `univ.filter` over
`HasSixPatternC6`) and the sum over that family are
deferred to B7-2, exactly as the `C₆` channel sums
were deferred at B6-1b. No sign is asserted. -/
noncomputable def kappa7chan211111C6
    (C : Finset (LayerColumn N)) (u u' : LayerLink N → G) : ℝ :=
  ∑ P ∈ C, doubledHexaReMoment ρ μG C P u u'

/-- **The `(2,1,1,1,1,1)` channel on `Θ(2,2,2)`
supports, raw per-support form**: for a single
6-support `C`, the sum over its distinguished doubled
columns `P ∈ C` of the doubled 6-support moments. The
raw moment does not see the support's site-degree
pattern, so this is the same raw form as
`kappa7chan211111C6` at a `Θ(2,2,2)` support; the
`Θ(2,2,2)` support family (B7-2, by `univ.filter` over
`HasSixPatternTheta`) and the sum over it are deferred
to B7-2. No sign is asserted. -/
noncomputable def kappa7chan211111Theta
    (C : Finset (LayerColumn N)) (u u' : LayerLink N → G) : ℝ :=
  ∑ P ∈ C, doubledHexaReMoment ρ μG C P u u'

/-- **The `(1⁷)` channel on the `Θ(1,3,3)` book
support, raw per-support form**: for a single
7-support `C`, the multiplicity-free moment
`heptaReMoment C`. RAW FORM ONLY: the `Θ(1,3,3)`
support family is not constructed in this brick —
its construction (B7-2, by `univ.filter` over
`HasSevenPatternTheta133`) and the sum over that
family are deferred to B7-2. No sign is asserted. -/
noncomputable def kappa7chanTheta133
    (C : Finset (LayerColumn N)) (u u' : LayerLink N → G) : ℝ :=
  heptaReMoment ρ μG C u u'

/-- **Strip at the doubled column.** If the doubled
column `P` itself has a private site `s` within the
support `C`, the doubled 6-support moment splits off
the second real moment:
`doubledHexaReMoment C P = realMoment 2 ·
quadReMoment (C.erase P)`. The exponent-blind strip
`integral_colRe_pow_split_finset` at exponents
`(1, 2)`, following `doubledQuadReMoment_strip_doubled`
verbatim with the support size changed. So a doubled
column at a private site carries no dependent
content: the `(2,1,1,1,1,1)` channel's content needs
the doubled column's sites shared — on the LIVE
supports (`C₆` / `Θ(2,2,2)`) they are. -/
theorem doubledHexaReMoment_strip_doubled (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    {P : LayerColumn N} {s : LayerSite N}
    (hsP : s ∈ colSites P)
    (hpriv : ∀ Y ∈ C, Y ≠ P → s ∉ colSites Y) :
    doubledHexaReMoment ρ μG C P u u'
      = realMoment ρ μG 2 * quadReMoment ρ μG (C.erase P) u u' := by
  classical
  have hPF : P ∉ C.erase P :=
    fun h => (Finset.mem_erase.mp h).1 rfl
  have hsF : ∀ Q ∈ C.erase P, s ∉ colSites Q :=
    fun Q hQ => hpriv Q (Finset.mem_erase.mp hQ).2
      (Finset.mem_erase.mp hQ).1
  have hpt : ∀ α : LayerSite N → G,
      (colRe ρ u u' P α) ^ 2
          * ∏ Q ∈ C.erase P, colRe ρ u u' Q α
        = (∏ Q ∈ C.erase P,
            (colRe ρ u u' Q α) ^ ((fun _ : LayerColumn N => 1) Q))
          * (colRe ρ u u' P α) ^ (2 : ℕ) := fun α => by
    simp only [pow_one]
    ring
  calc doubledHexaReMoment ρ μG C P u u'
      = ∫ α : LayerSite N → G,
          (∏ Q ∈ C.erase P,
            (colRe ρ u u' Q α) ^ ((fun _ : LayerColumn N => 1) Q))
            * (colRe ρ u u' P α) ^ (2 : ℕ)
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = realMoment ρ μG 2
          * ∫ α : LayerSite N → G, ∏ Q ∈ C.erase P,
              (colRe ρ u u' Q α) ^ ((fun _ : LayerColumn N => 1) Q)
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_colRe_pow_split_finset ρ μG hN hN3 hρcont u u'
          (C.erase P) (fun _ => 1) P hPF s hsP hsF 2
    _ = realMoment ρ μG 2
          * quadReMoment ρ μG (C.erase P) u u' := by
        refine congrArg _ ?_
        refine integral_congr_ae
          (Filter.Eventually.of_forall fun α => ?_)
        exact Finset.prod_congr rfl fun Q _ => pow_one _

/-- **Strip at a single column.** If a single (undoubled)
column `Q ∈ C`, `Q ≠ P`, has a private site `s` within
the support `C`, the doubled 6-support moment splits
off the single-site mean:
`doubledHexaReMoment C P = e₁ · doubledHexaReMoment
(C.erase Q) P`. The exponent-blind strip at exponent
function `(2 at P, 1 elsewhere)` and `k = 1`, following
`doubledQuadReMoment_strip_single` verbatim with the
support size changed. -/
theorem doubledHexaReMoment_strip_single (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    {P Q : LayerColumn N} (hPC : P ∈ C) (hQC : Q ∈ C)
    (hQP : Q ≠ P) {s : LayerSite N}
    (hsQ : s ∈ colSites Q)
    (hpriv : ∀ Y ∈ C, Y ≠ Q → s ∉ colSites Y) :
    doubledHexaReMoment ρ μG C P u u'
      = e1 ρ μG * doubledHexaReMoment ρ μG (C.erase Q) P u u' := by
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
        = (colRe ρ u u' P α) ^ 2
          * ∏ R ∈ (C.erase Q).erase P, colRe ρ u u' R α := by
    intro α
    rw [Finset.prod_insert hPF, haP]
    refine congrArg _ ?_
    exact Finset.prod_congr rfl fun R hR => by rw [haR R hR, pow_one]
  have hpt1 : ∀ α : LayerSite N → G,
      (colRe ρ u u' P α) ^ 2 * ∏ R ∈ C.erase P, colRe ρ u u' R α
        = (∏ R ∈ insert P ((C.erase Q).erase P),
            (colRe ρ u u' R α) ^ (a R))
          * (colRe ρ u u' Q α) ^ (1 : ℕ) := by
    intro α
    rw [h1 α, h2 α]
    simp only [pow_one]
    ring
  calc doubledHexaReMoment ρ μG C P u u'
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
    _ = e1 ρ μG * doubledHexaReMoment ρ μG (C.erase Q) P u u' := by
        rw [realMoment_one]
        refine congrArg _ ?_
        exact integral_congr_ae (Filter.Eventually.of_forall h2)

end Distinct7

section Channel7

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- Two columns are ADJACENT (share a site): the left
side of B7-0's dichotomy
`columns_adjacent_or_opposite`. This is a
quad-internal site-sharing predicate on the two
columns themselves, stated here for the `(3,2,1,1)`
heavy pair; it is not the polymer line's `colAdj`
(base-site adjacency). -/
def ColsShareSite (P Q : LayerColumn N) : Prop :=
  ∃ s, s ∈ colSites P ∧ s ∈ colSites Q

/-- Two columns are OPPOSITE (disjoint site pairs):
the right side of B7-0's dichotomy
`columns_adjacent_or_opposite`. -/
def ColsDisjointSites (P Q : LayerColumn N) : Prop :=
  ∀ s, s ∈ colSites P → s ∉ colSites Q

/-- Classical decidability for the ADJACENT predicate,
so the `(3,2,1,1)` channel can be filtered by it at
the definition level. -/
noncomputable instance (P Q : LayerColumn N) :
    Decidable (ColsShareSite P Q) :=
  Classical.propDecidable _

/-- Classical decidability for the OPPOSITE predicate,
the twin of the ADJACENT instance above. -/
noncomputable instance (P Q : LayerColumn N) :
    Decidable (ColsDisjointSites P Q) :=
  Classical.propDecidable _

/-- The ADJACENT / OPPOSITE dichotomy for the heavy
pair of a `(3,2,1,1)` configuration, consumed from
B7-0's landed `columns_adjacent_or_opposite`: the two
heavy columns either share a site or have disjoint
site pairs, with no third case. -/
theorem colsShareSite_or_disjointSites (P Q : LayerColumn N) :
    ColsShareSite P Q ∨ ColsDisjointSites P Q :=
  columns_adjacent_or_opposite P Q

/-- Disjointness is exactly the failure of sharing:
the two sides of the dichotomy are complementary. -/
theorem colsDisjointSites_iff_not_share (P Q : LayerColumn N) :
    ColsDisjointSites P Q ↔ ¬ ColsShareSite P Q := by
  constructor
  · intro h ⟨s, hsP, hsQ⟩
    exact h s hsP hsQ
  · intro h s hsP hsQ
    exact h ⟨s, hsP, hsQ⟩

/-- The raw `(4,1,1,1)` moment at a 4-support `C` with
distinguished quadrupled column `P`: the stratum
integral of `(colRe P)⁴ · ∏_{Q ∈ C.erase P} colRe Q`
— the character moment of the multiset `C + {P, P, P}`
(the support `C` with `P` counted four times). This
is the order-7 analogue of `tripledQuadReMoment`: at
order 7 the surviving dependent supports on primitive
quads carry the `(4,1,1,1)`, `(3,2,1,1)` and
`(2,2,2,1)` patterns (B7-0). -/
noncomputable def quadrupledQuadReMoment
    (C : Finset (LayerColumn N)) (P : LayerColumn N)
    (u u' : LayerLink N → G) : ℝ :=
  ∫ α, (colRe ρ u u' P α) ^ 4
      * ∏ Q ∈ C.erase P, colRe ρ u u' Q α
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- The quadrupled moment is the multiset moment: for
`P ∈ C` it equals the integral of the full support
product times three more factors of the quadrupled
column, `∫ (∏_{Q ∈ C} colRe Q) · (colRe P)³`. -/
theorem quadrupledQuadReMoment_eq_mul
    {C : Finset (LayerColumn N)} {P : LayerColumn N}
    (hPC : P ∈ C) (u u' : LayerLink N → G) :
    quadrupledQuadReMoment ρ μG C P u u'
      = ∫ α, (∏ Q ∈ C, colRe ρ u u' Q α) * (colRe ρ u u' P α) ^ 3
        ∂(Measure.pi fun _ : LayerSite N => μG) := by
  refine integral_congr_ae
    (Filter.Eventually.of_forall fun α => ?_)
  show (colRe ρ u u' P α) ^ 4
      * ∏ Q ∈ C.erase P, colRe ρ u u' Q α
      = (∏ Q ∈ C, colRe ρ u u' Q α) * (colRe ρ u u' P α) ^ 3
  rw [← Finset.mul_prod_erase C (fun Q => colRe ρ u u' Q α) hPC]
  ring

/-- **The `(4,1,1,1)` channel expression**: the sum,
over primitive quads `C` and distinguished columns
`P ∈ C`, of the quadrupled-column moments. This is a
raw channel expression only: the assembly identity
expressing `kappa7dep` through dressings and channel
excesses is B7-2's seam and is **not** asserted here,
and no baseline is subtracted inside this definition
(excess formation is B7-2's). No sign is asserted for
this sum. -/
noncomputable def kappa7chan4111 (u u' : LayerLink N → G) : ℝ :=
  ∑ C ∈ primitiveQuads, ∑ P ∈ C,
    quadrupledQuadReMoment ρ μG C P u u'

/-- **Strip at the quadrupled column.** If the
quadrupled column `P` itself has a private site `s`
within the support `C`, the quadrupled moment splits
off the fourth real moment:
`quadrupledQuadReMoment C P = realMoment 4 ·
quadReMoment (C.erase P)`. The exponent-blind strip
`integral_colRe_pow_split_finset` at exponents
`(1, 4)`, following `tripledQuadReMoment_strip_tripled`
with the tripled exponent replaced by `4`. So a
quadrupled column at a private site carries no
dependent content: the channel's content needs the
quadrupled column's sites shared. -/
theorem quadrupledQuadReMoment_strip_quadrupled (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    {P : LayerColumn N} {s : LayerSite N}
    (hsP : s ∈ colSites P)
    (hpriv : ∀ Y ∈ C, Y ≠ P → s ∉ colSites Y) :
    quadrupledQuadReMoment ρ μG C P u u'
      = realMoment ρ μG 4 * quadReMoment ρ μG (C.erase P) u u' := by
  classical
  have hPF : P ∉ C.erase P :=
    fun h => (Finset.mem_erase.mp h).1 rfl
  have hsF : ∀ Q ∈ C.erase P, s ∉ colSites Q :=
    fun Q hQ => hpriv Q (Finset.mem_erase.mp hQ).2
      (Finset.mem_erase.mp hQ).1
  have hpt : ∀ α : LayerSite N → G,
      (colRe ρ u u' P α) ^ 4
          * ∏ Q ∈ C.erase P, colRe ρ u u' Q α
        = (∏ Q ∈ C.erase P,
            (colRe ρ u u' Q α) ^ ((fun _ : LayerColumn N => 1) Q))
          * (colRe ρ u u' P α) ^ (4 : ℕ) := fun α => by
    simp only [pow_one]
    ring
  calc quadrupledQuadReMoment ρ μG C P u u'
      = ∫ α : LayerSite N → G,
          (∏ Q ∈ C.erase P,
            (colRe ρ u u' Q α) ^ ((fun _ : LayerColumn N => 1) Q))
            * (colRe ρ u u' P α) ^ (4 : ℕ)
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = realMoment ρ μG 4
          * ∫ α : LayerSite N → G, ∏ Q ∈ C.erase P,
              (colRe ρ u u' Q α) ^ ((fun _ : LayerColumn N => 1) Q)
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_colRe_pow_split_finset ρ μG hN hN3 hρcont u u'
          (C.erase P) (fun _ => 1) P hPF s hsP hsF 4
    _ = realMoment ρ μG 4
          * quadReMoment ρ μG (C.erase P) u u' := by
        refine congrArg _ ?_
        refine integral_congr_ae
          (Filter.Eventually.of_forall fun α => ?_)
        exact Finset.prod_congr rfl fun Q _ => pow_one _

/-- **Strip at a single column.** If a single
(unquadrupled) column `Q ∈ C`, `Q ≠ P`, has a private
site `s` within the support `C`, the quadrupled moment
splits off the single-site mean:
`quadrupledQuadReMoment C P = e₁ ·
quadrupledQuadReMoment (C.erase Q) P`. The
exponent-blind strip at exponent function `(4 at P,
1 elsewhere)` and `k = 1`, following
`tripledQuadReMoment_strip_single` with the tripled
exponent replaced by `4`. Together with
`quadrupledQuadReMoment_strip_quadrupled`: at a
non-primitive support every quadrupled moment reduces
to lower content, so the `(4,1,1,1)` channel's
dependent content is carried by the primitive quads —
exactly the supports `kappa7chan4111` sums over. -/
theorem quadrupledQuadReMoment_strip_single (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    {P Q : LayerColumn N} (hPC : P ∈ C) (hQC : Q ∈ C)
    (hQP : Q ≠ P) {s : LayerSite N}
    (hsQ : s ∈ colSites Q)
    (hpriv : ∀ Y ∈ C, Y ≠ Q → s ∉ colSites Y) :
    quadrupledQuadReMoment ρ μG C P u u'
      = e1 ρ μG * quadrupledQuadReMoment ρ μG (C.erase Q) P u u' := by
  classical
  set a : LayerColumn N → ℕ := fun R => if R = P then 4 else 1
    with ha_def
  have haP : a P = 4 := by
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
        = (colRe ρ u u' P α) ^ 4
          * ∏ R ∈ (C.erase Q).erase P, colRe ρ u u' R α := by
    intro α
    rw [Finset.prod_insert hPF, haP]
    refine congrArg _ ?_
    exact Finset.prod_congr rfl fun R hR => by rw [haR R hR, pow_one]
  have hpt1 : ∀ α : LayerSite N → G,
      (colRe ρ u u' P α) ^ 4 * ∏ R ∈ C.erase P, colRe ρ u u' R α
        = (∏ R ∈ insert P ((C.erase Q).erase P),
            (colRe ρ u u' R α) ^ (a R))
          * (colRe ρ u u' Q α) ^ (1 : ℕ) := by
    intro α
    rw [h1 α, h2 α]
    simp only [pow_one]
    ring
  calc quadrupledQuadReMoment ρ μG C P u u'
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
    _ = e1 ρ μG * quadrupledQuadReMoment ρ μG (C.erase Q) P u u' := by
        rw [realMoment_one]
        refine congrArg _ ?_
        exact integral_congr_ae (Filter.Eventually.of_forall h2)

/-- The raw `(3,2,1,1)` moment at a 4-support `C` with
distinguished tripled column `P` and distinguished
doubled column `Q`: the stratum integral of
`(colRe P)³ · (colRe Q)² · ∏_{R ∈ (C.erase P).erase Q}
colRe R` — the character moment of the multiset
`C + {P, P, Q}` (the support `C` with `P` counted
three times and `Q` counted twice). The pair `(P, Q)`
is the pattern's heavy pair, whose relative position
is the ADJACENT / OPPOSITE split below. -/
noncomputable def tripledDoubledQuadReMoment
    (C : Finset (LayerColumn N)) (P Q : LayerColumn N)
    (u u' : LayerLink N → G) : ℝ :=
  ∫ α, (colRe ρ u u' P α) ^ 3 * (colRe ρ u u' Q α) ^ 2
      * ∏ R ∈ (C.erase P).erase Q, colRe ρ u u' R α
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- The tripled-doubled moment is the multiset moment:
for distinct `P, Q ∈ C` it equals the integral of the
full support product times two more factors of the
tripled column and one more factor of the doubled
column,
`∫ (∏_{R ∈ C} colRe R) · (colRe P)² · colRe Q`. -/
theorem tripledDoubledQuadReMoment_eq_mul
    {C : Finset (LayerColumn N)} {P Q : LayerColumn N}
    (hPC : P ∈ C) (hQC : Q ∈ C) (hQP : Q ≠ P)
    (u u' : LayerLink N → G) :
    tripledDoubledQuadReMoment ρ μG C P Q u u'
      = ∫ α, (∏ R ∈ C, colRe ρ u u' R α)
          * (colRe ρ u u' P α) ^ 2 * colRe ρ u u' Q α
        ∂(Measure.pi fun _ : LayerSite N => μG) := by
  have hQmem : Q ∈ C.erase P :=
    Finset.mem_erase.mpr ⟨hQP, hQC⟩
  refine integral_congr_ae
    (Filter.Eventually.of_forall fun α => ?_)
  show (colRe ρ u u' P α) ^ 3 * (colRe ρ u u' Q α) ^ 2
      * ∏ R ∈ (C.erase P).erase Q, colRe ρ u u' R α
      = (∏ R ∈ C, colRe ρ u u' R α)
        * (colRe ρ u u' P α) ^ 2 * colRe ρ u u' Q α
  rw [← Finset.mul_prod_erase C (fun R => colRe ρ u u' R α) hPC,
    ← Finset.mul_prod_erase (C.erase P)
      (fun R => colRe ρ u u' R α) hQmem]
  ring

/-- **The `(3,2,1,1)` channel expression**: the sum,
over primitive quads `C` and ordered pairs of distinct
distinguished columns `P ∈ C` (tripled),
`Q ∈ C.erase P` (doubled), of the tripled-doubled
moments. Raw channel expression only, on the same
fence as `kappa7chan4111`: no assembly identity and
no sign is asserted here. -/
noncomputable def kappa7chan3211 (u u' : LayerLink N → G) : ℝ :=
  ∑ C ∈ primitiveQuads, ∑ P ∈ C, ∑ Q ∈ C.erase P,
    tripledDoubledQuadReMoment ρ μG C P Q u u'

/-- **The ADJACENT `(3,2,1,1)` channel expression**:
the part of `kappa7chan3211` whose heavy pair
`(P, Q)` shares a site (`ColsShareSite P Q`). The
split is B7-0's dichotomy, landed at the definition
level via the two complementary filters; the two
split expressions partition the unsplit channel by
`kappa7chan3211_adj_add_opp` below. Raw channel
expression only; no sign is asserted. -/
noncomputable def kappa7chan3211Adj (u u' : LayerLink N → G) : ℝ :=
  ∑ C ∈ primitiveQuads, ∑ P ∈ C,
    ∑ Q ∈ (C.erase P).filter (fun Q => ColsShareSite P Q),
      tripledDoubledQuadReMoment ρ μG C P Q u u'

/-- **The OPPOSITE `(3,2,1,1)` channel expression**:
the part of `kappa7chan3211` whose heavy pair
`(P, Q)` has disjoint site pairs
(`ColsDisjointSites P Q`). The complement of
`kappa7chan3211Adj` in `kappa7chan3211`. Raw channel
expression only; no sign is asserted. -/
noncomputable def kappa7chan3211Opp (u u' : LayerLink N → G) : ℝ :=
  ∑ C ∈ primitiveQuads, ∑ P ∈ C,
    ∑ Q ∈ (C.erase P).filter (fun Q => ColsDisjointSites P Q),
      tripledDoubledQuadReMoment ρ μG C P Q u u'

/-- **The split partitions the channel.** The
ADJACENT and OPPOSITE `(3,2,1,1)` channel expressions
sum to the unsplit channel: at every heavy pair the
dichotomy `colsShareSite_or_disjointSites` is
exhaustive and the two sides are complementary
(`colsDisjointSites_iff_not_share`), so the
complementary-filter sum identity applies at every
`(C, P)`. A definition-level partition only — no
assembly identity and no sign is asserted. -/
theorem kappa7chan3211_adj_add_opp (u u' : LayerLink N → G) :
    kappa7chan3211Adj ρ μG u u' + kappa7chan3211Opp ρ μG u u'
      = kappa7chan3211 ρ μG u u' := by
  classical
  unfold kappa7chan3211Adj kappa7chan3211Opp kappa7chan3211
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun P _ => ?_
  have hnot : (C.erase P).filter (fun Q => ColsDisjointSites P Q)
      = (C.erase P).filter (fun Q => ¬ ColsShareSite P Q) :=
    Finset.filter_congr fun Q _ =>
      colsDisjointSites_iff_not_share P Q
  rw [hnot, Finset.sum_filter_add_sum_filter_not]

/-- **Strip at the tripled column.** If the tripled
column `P` has a private site `s` within the support
`C`, the tripled-doubled moment splits off the third
real moment, leaving the `(2,1,1)` moment of the
erased support at `Q`:
`tripledDoubledQuadReMoment C P Q = realMoment 3 ·
doubledQuadReMoment (C.erase P) Q`. The exponent-blind
strip at exponent function `(2 at Q, 1 elsewhere)` on
`C.erase P` and `k = 3`, following
`doubledDoubledQuadReMoment_strip_first` with the
stripped exponent raised to `3`. -/
theorem tripledDoubledQuadReMoment_strip_tripled (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    {P Q : LayerColumn N} (hQC : Q ∈ C) (hQP : Q ≠ P)
    {s : LayerSite N}
    (hsP : s ∈ colSites P)
    (hpriv : ∀ Y ∈ C, Y ≠ P → s ∉ colSites Y) :
    tripledDoubledQuadReMoment ρ μG C P Q u u'
      = realMoment ρ μG 3
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
      (colRe ρ u u' P α) ^ 3 * (colRe ρ u u' Q α) ^ 2
          * ∏ R ∈ (C.erase P).erase Q, colRe ρ u u' R α
        = (∏ Y ∈ C.erase P, (colRe ρ u u' Y α) ^ (a Y))
          * (colRe ρ u u' P α) ^ (3 : ℕ) := fun α => by
    rw [hprod α]
    ring
  calc tripledDoubledQuadReMoment ρ μG C P Q u u'
      = ∫ α : LayerSite N → G,
          (∏ Y ∈ C.erase P, (colRe ρ u u' Y α) ^ (a Y))
            * (colRe ρ u u' P α) ^ (3 : ℕ)
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = realMoment ρ μG 3
          * ∫ α : LayerSite N → G,
              ∏ Y ∈ C.erase P, (colRe ρ u u' Y α) ^ (a Y)
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_colRe_pow_split_finset ρ μG hN hN3 hρcont u u'
          (C.erase P) a P hPF s hsP hsF 3
    _ = realMoment ρ μG 3
          * doubledQuadReMoment ρ μG (C.erase P) Q u u' := by
        refine congrArg _ ?_
        exact integral_congr_ae (Filter.Eventually.of_forall hprod)

/-- **Strip at the doubled column.** If the doubled
column `Q` has a private site `s` within the support
`C`, the tripled-doubled moment splits off the second
real moment, leaving the `(3,1,1)` moment of the
erased support at `P`:
`tripledDoubledQuadReMoment C P Q = realMoment 2 ·
tripledQuadReMoment (C.erase Q) P`. The same strip as
`tripledDoubledQuadReMoment_strip_tripled` with the
two heavy columns' roles exchanged (the erase factors
commute). -/
theorem tripledDoubledQuadReMoment_strip_doubled (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    {P Q : LayerColumn N} (hPC : P ∈ C) (hQP : Q ≠ P)
    {s : LayerSite N}
    (hsQ : s ∈ colSites Q)
    (hpriv : ∀ Y ∈ C, Y ≠ Q → s ∉ colSites Y) :
    tripledDoubledQuadReMoment ρ μG C P Q u u'
      = realMoment ρ μG 2
        * tripledQuadReMoment ρ μG (C.erase Q) P u u' := by
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
        = (colRe ρ u u' P α) ^ 3
          * ∏ R ∈ (C.erase Q).erase P, colRe ρ u u' R α := by
    intro α
    rw [← Finset.mul_prod_erase (C.erase Q)
      (fun Y => (colRe ρ u u' Y α) ^ (a Y)) hPmem, haP]
    refine congrArg _ ?_
    exact Finset.prod_congr rfl fun R hR => by
      rw [haR R hR, pow_one]
  have hpt : ∀ α : LayerSite N → G,
      (colRe ρ u u' P α) ^ 3 * (colRe ρ u u' Q α) ^ 2
          * ∏ R ∈ (C.erase P).erase Q, colRe ρ u u' R α
        = (∏ Y ∈ C.erase Q, (colRe ρ u u' Y α) ^ (a Y))
          * (colRe ρ u u' Q α) ^ (2 : ℕ) := fun α => by
    rw [hcomm, hprod α]
    ring
  calc tripledDoubledQuadReMoment ρ μG C P Q u u'
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
          * tripledQuadReMoment ρ μG (C.erase Q) P u u' := by
        refine congrArg _ ?_
        exact integral_congr_ae (Filter.Eventually.of_forall hprod)

/-- **Strip at a single column.** If a single column
`R ∈ C`, distinct from both heavy columns, has a
private site `s` within the support `C`, the
tripled-doubled moment splits off the single-site
mean:
`tripledDoubledQuadReMoment C P Q = e₁ ·
tripledDoubledQuadReMoment (C.erase R) P Q`. The
exponent-blind strip at exponent function `(3 at P,
2 at Q, 1 elsewhere)` and `k = 1`, following
`doubledDoubledQuadReMoment_strip_single` with the
first doubled exponent raised to `3`. Together with
the two heavy-column strips: at a non-primitive
support every tripled-doubled moment reduces to lower
content, so the `(3,2,1,1)` channel's dependent
content is carried by the primitive quads — exactly
the supports `kappa7chan3211` sums over. -/
theorem tripledDoubledQuadReMoment_strip_single (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    {P Q R : LayerColumn N} (hPC : P ∈ C) (hQC : Q ∈ C)
    (hRC : R ∈ C) (hRP : R ≠ P) (hRQ : R ≠ Q) (hQP : Q ≠ P)
    {s : LayerSite N}
    (hsR : s ∈ colSites R)
    (hpriv : ∀ Y ∈ C, Y ≠ R → s ∉ colSites Y) :
    tripledDoubledQuadReMoment ρ μG C P Q u u'
      = e1 ρ μG
        * tripledDoubledQuadReMoment ρ μG (C.erase R) P Q u u' := by
  classical
  set T0 : Finset (LayerColumn N) :=
    ((C.erase R).erase P).erase Q with hT0_def
  set a : LayerColumn N → ℕ :=
    fun Y => if Y = P then 3 else if Y = Q then 2 else 1
    with ha_def
  have haP : a P = 3 := by
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
        = (colRe ρ u u' P α) ^ 3 * (colRe ρ u u' Q α) ^ 2
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
      (colRe ρ u u' P α) ^ 3 * (colRe ρ u u' Q α) ^ 2
          * ∏ Z ∈ (C.erase P).erase Q, colRe ρ u u' Z α
        = (∏ Y ∈ insert P (insert Q T0),
            (colRe ρ u u' Y α) ^ (a Y))
          * (colRe ρ u u' R α) ^ (1 : ℕ) := by
    intro α
    rw [hsplit α, hprodT α]
    simp only [pow_one]
    ring
  calc tripledDoubledQuadReMoment ρ μG C P Q u u'
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
          * tripledDoubledQuadReMoment ρ μG (C.erase R) P Q
            u u' := by
        rw [realMoment_one]
        refine congrArg _ ?_
        exact integral_congr_ae (Filter.Eventually.of_forall hprodT)

/-- The raw `(2,2,2,1)` moment at a 4-support `C` with
distinguished doubled columns `P`, `Q` and `R`: the
stratum integral of
`(colRe P)² · (colRe Q)² · (colRe R)² ·
∏_{S ∈ ((C.erase P).erase Q).erase R} colRe S`
— the character moment of the multiset `C + {P, Q, R}`
(the support `C` with each of `P`, `Q`, `R` counted
twice). -/
noncomputable def doubledDoubledDoubledQuadReMoment
    (C : Finset (LayerColumn N)) (P Q R : LayerColumn N)
    (u u' : LayerLink N → G) : ℝ :=
  ∫ α, (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
      * (colRe ρ u u' R α) ^ 2
      * ∏ S ∈ ((C.erase P).erase Q).erase R, colRe ρ u u' S α
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- The triple-doubled moment is the multiset moment:
for pairwise distinct `P, Q, R ∈ C` it equals the
integral of the full support product times one more
factor of each doubled column,
`∫ (∏_{S ∈ C} colRe S) · colRe P · colRe Q · colRe R`. -/
theorem doubledDoubledDoubledQuadReMoment_eq_mul
    {C : Finset (LayerColumn N)} {P Q R : LayerColumn N}
    (hPC : P ∈ C) (hQC : Q ∈ C) (hRC : R ∈ C)
    (hQP : Q ≠ P) (hRP : R ≠ P) (hRQ : R ≠ Q)
    (u u' : LayerLink N → G) :
    doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
      = ∫ α, (∏ S ∈ C, colRe ρ u u' S α)
          * colRe ρ u u' P α * colRe ρ u u' Q α
          * colRe ρ u u' R α
        ∂(Measure.pi fun _ : LayerSite N => μG) := by
  have hQmem : Q ∈ C.erase P :=
    Finset.mem_erase.mpr ⟨hQP, hQC⟩
  have hRmem : R ∈ (C.erase P).erase Q :=
    Finset.mem_erase.mpr ⟨hRQ, Finset.mem_erase.mpr ⟨hRP, hRC⟩⟩
  refine integral_congr_ae
    (Filter.Eventually.of_forall fun α => ?_)
  show (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
      * (colRe ρ u u' R α) ^ 2
      * ∏ S ∈ ((C.erase P).erase Q).erase R, colRe ρ u u' S α
      = (∏ S ∈ C, colRe ρ u u' S α)
        * colRe ρ u u' P α * colRe ρ u u' Q α
        * colRe ρ u u' R α
  rw [← Finset.mul_prod_erase C (fun S => colRe ρ u u' S α) hPC,
    ← Finset.mul_prod_erase (C.erase P)
      (fun S => colRe ρ u u' S α) hQmem,
    ← Finset.mul_prod_erase ((C.erase P).erase Q)
      (fun S => colRe ρ u u' S α) hRmem]
  ring

/-- **The `(2,2,2,1)` channel expression**: the sum,
over primitive quads `C` and ordered triples of
pairwise distinct distinguished columns `P ∈ C`,
`Q ∈ C.erase P`, `R ∈ (C.erase P).erase Q`, of the
triple-doubled moments. Raw channel expression only,
on the same fence as `kappa7chan4111`: no assembly
identity and no sign is asserted here. -/
noncomputable def kappa7chan2221 (u u' : LayerLink N → G) : ℝ :=
  ∑ C ∈ primitiveQuads, ∑ P ∈ C, ∑ Q ∈ C.erase P,
    ∑ R ∈ (C.erase P).erase Q,
      doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'

/-- **Strip at the first doubled column.** If the
doubled column `P` has a private site `s` within the
support `C`, the triple-doubled moment splits off the
second real moment, leaving the `(2,2,1,1)` moment of
the erased support at `Q`, `R`:
`doubledDoubledDoubledQuadReMoment C P Q R =
realMoment 2 · doubledDoubledQuadReMoment
(C.erase P) Q R`. The exponent-blind strip at exponent
function `(2 at Q, 2 at R, 1 elsewhere)` on
`C.erase P` and `k = 2`. -/
theorem doubledDoubledDoubledQuadReMoment_strip_first
    (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    {P Q R : LayerColumn N} (hQC : Q ∈ C) (hRC : R ∈ C)
    (hQP : Q ≠ P) (hRP : R ≠ P) (hRQ : R ≠ Q)
    {s : LayerSite N}
    (hsP : s ∈ colSites P)
    (hpriv : ∀ Y ∈ C, Y ≠ P → s ∉ colSites Y) :
    doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
      = realMoment ρ μG 2
        * doubledDoubledQuadReMoment ρ μG (C.erase P) Q R u u' := by
  classical
  set a : LayerColumn N → ℕ :=
    fun Y => if Y = Q then 2 else if Y = R then 2 else 1
    with ha_def
  have haQ : a Q = 2 := by
    rw [ha_def]
    exact if_pos rfl
  have haR : a R = 2 := by
    rw [ha_def]
    exact (if_neg hRQ).trans (if_pos rfl)
  have haT0 : ∀ Y ∈ ((C.erase P).erase Q).erase R, a Y = 1 := by
    intro Y hY
    have hYQ : Y ≠ Q :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hY).2).1
    have hYR : Y ≠ R := (Finset.mem_erase.mp hY).1
    rw [ha_def]
    exact (if_neg hYQ).trans (if_neg hYR)
  have hPF : P ∉ C.erase P :=
    fun h => (Finset.mem_erase.mp h).1 rfl
  have hsF : ∀ Y ∈ C.erase P, s ∉ colSites Y :=
    fun Y hY => hpriv Y (Finset.mem_erase.mp hY).2
      (Finset.mem_erase.mp hY).1
  have hQmem : Q ∈ C.erase P := Finset.mem_erase.mpr ⟨hQP, hQC⟩
  have hRmem : R ∈ (C.erase P).erase Q :=
    Finset.mem_erase.mpr ⟨hRQ, Finset.mem_erase.mpr ⟨hRP, hRC⟩⟩
  have hT0prod : ∀ α : LayerSite N → G,
      ∏ Z ∈ ((C.erase P).erase Q).erase R,
          (colRe ρ u u' Z α) ^ (a Z)
        = ∏ Z ∈ ((C.erase P).erase Q).erase R,
            colRe ρ u u' Z α :=
    fun α => Finset.prod_congr rfl fun Z hZ => by
      rw [haT0 Z hZ, pow_one]
  have hprod : ∀ α : LayerSite N → G,
      ∏ Y ∈ C.erase P, (colRe ρ u u' Y α) ^ (a Y)
        = (colRe ρ u u' Q α) ^ 2 * (colRe ρ u u' R α) ^ 2
          * ∏ Z ∈ ((C.erase P).erase Q).erase R,
              colRe ρ u u' Z α := by
    intro α
    calc ∏ Y ∈ C.erase P, (colRe ρ u u' Y α) ^ (a Y)
        = (colRe ρ u u' Q α) ^ 2
            * ((colRe ρ u u' R α) ^ 2
              * ∏ Z ∈ ((C.erase P).erase Q).erase R,
                  (colRe ρ u u' Z α) ^ (a Z)) := by
          rw [← Finset.mul_prod_erase (C.erase P)
            (fun Y => (colRe ρ u u' Y α) ^ (a Y)) hQmem,
            ← Finset.mul_prod_erase ((C.erase P).erase Q)
            (fun Y => (colRe ρ u u' Y α) ^ (a Y)) hRmem,
            haQ, haR]
      _ = (colRe ρ u u' Q α) ^ 2 * (colRe ρ u u' R α) ^ 2
            * ∏ Z ∈ ((C.erase P).erase Q).erase R,
                colRe ρ u u' Z α := by
          rw [hT0prod α]
          ring
  have hpt : ∀ α : LayerSite N → G,
      (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
          * (colRe ρ u u' R α) ^ 2
          * ∏ Z ∈ ((C.erase P).erase Q).erase R,
              colRe ρ u u' Z α
        = (∏ Y ∈ C.erase P, (colRe ρ u u' Y α) ^ (a Y))
          * (colRe ρ u u' P α) ^ (2 : ℕ) := fun α => by
    rw [hprod α]
    ring
  calc doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
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
          * doubledDoubledQuadReMoment ρ μG (C.erase P) Q R
            u u' := by
        refine congrArg _ ?_
        exact integral_congr_ae (Filter.Eventually.of_forall hprod)

/-- **Strip at the second doubled column.** If the
doubled column `Q` has a private site `s` within the
support `C`, the triple-doubled moment splits off the
second real moment, leaving the `(2,2,1,1)` moment of
the erased support at `P`, `R`:
`doubledDoubledDoubledQuadReMoment C P Q R =
realMoment 2 · doubledDoubledQuadReMoment
(C.erase Q) P R`. The same strip as
`doubledDoubledDoubledQuadReMoment_strip_first` with
the stripped column exchanged (the erase factors
commute). -/
theorem doubledDoubledDoubledQuadReMoment_strip_second
    (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    {P Q R : LayerColumn N} (hPC : P ∈ C) (hRC : R ∈ C)
    (hQP : Q ≠ P) (hRP : R ≠ P) (hRQ : R ≠ Q)
    {s : LayerSite N}
    (hsQ : s ∈ colSites Q)
    (hpriv : ∀ Y ∈ C, Y ≠ Q → s ∉ colSites Y) :
    doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
      = realMoment ρ μG 2
        * doubledDoubledQuadReMoment ρ μG (C.erase Q) P R u u' := by
  classical
  set a : LayerColumn N → ℕ :=
    fun Y => if Y = P then 2 else if Y = R then 2 else 1
    with ha_def
  have haP : a P = 2 := by
    rw [ha_def]
    exact if_pos rfl
  have haR : a R = 2 := by
    rw [ha_def]
    exact (if_neg hRP).trans (if_pos rfl)
  have haT0 : ∀ Y ∈ ((C.erase Q).erase P).erase R, a Y = 1 := by
    intro Y hY
    have hYP : Y ≠ P :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hY).2).1
    have hYR : Y ≠ R := (Finset.mem_erase.mp hY).1
    rw [ha_def]
    exact (if_neg hYP).trans (if_neg hYR)
  have hQF : Q ∉ C.erase Q :=
    fun h => (Finset.mem_erase.mp h).1 rfl
  have hsF : ∀ Y ∈ C.erase Q, s ∉ colSites Y :=
    fun Y hY => hpriv Y (Finset.mem_erase.mp hY).2
      (Finset.mem_erase.mp hY).1
  have hPmem : P ∈ C.erase Q :=
    Finset.mem_erase.mpr ⟨fun h => hQP h.symm, hPC⟩
  have hRmem : R ∈ (C.erase Q).erase P :=
    Finset.mem_erase.mpr ⟨hRP, Finset.mem_erase.mpr ⟨hRQ, hRC⟩⟩
  have hcommT : ((C.erase P).erase Q).erase R
      = ((C.erase Q).erase P).erase R := by
    ext Z
    simp only [Finset.mem_erase]
    tauto
  have hT0prod : ∀ α : LayerSite N → G,
      ∏ Z ∈ ((C.erase Q).erase P).erase R,
          (colRe ρ u u' Z α) ^ (a Z)
        = ∏ Z ∈ ((C.erase Q).erase P).erase R,
            colRe ρ u u' Z α :=
    fun α => Finset.prod_congr rfl fun Z hZ => by
      rw [haT0 Z hZ, pow_one]
  have hprod : ∀ α : LayerSite N → G,
      ∏ Y ∈ C.erase Q, (colRe ρ u u' Y α) ^ (a Y)
        = (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' R α) ^ 2
          * ∏ Z ∈ ((C.erase Q).erase P).erase R,
              colRe ρ u u' Z α := by
    intro α
    calc ∏ Y ∈ C.erase Q, (colRe ρ u u' Y α) ^ (a Y)
        = (colRe ρ u u' P α) ^ 2
            * ((colRe ρ u u' R α) ^ 2
              * ∏ Z ∈ ((C.erase Q).erase P).erase R,
                  (colRe ρ u u' Z α) ^ (a Z)) := by
          rw [← Finset.mul_prod_erase (C.erase Q)
            (fun Y => (colRe ρ u u' Y α) ^ (a Y)) hPmem,
            ← Finset.mul_prod_erase ((C.erase Q).erase P)
            (fun Y => (colRe ρ u u' Y α) ^ (a Y)) hRmem,
            haP, haR]
      _ = (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' R α) ^ 2
            * ∏ Z ∈ ((C.erase Q).erase P).erase R,
                colRe ρ u u' Z α := by
          rw [hT0prod α]
          ring
  have hpt : ∀ α : LayerSite N → G,
      (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
          * (colRe ρ u u' R α) ^ 2
          * ∏ Z ∈ ((C.erase P).erase Q).erase R,
              colRe ρ u u' Z α
        = (∏ Y ∈ C.erase Q, (colRe ρ u u' Y α) ^ (a Y))
          * (colRe ρ u u' Q α) ^ (2 : ℕ) := fun α => by
    rw [hcommT, hprod α]
    ring
  calc doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
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
          * doubledDoubledQuadReMoment ρ μG (C.erase Q) P R
            u u' := by
        refine congrArg _ ?_
        exact integral_congr_ae (Filter.Eventually.of_forall hprod)

/-- **Strip at the third doubled column.** If the
doubled column `R` has a private site `s` within the
support `C`, the triple-doubled moment splits off the
second real moment, leaving the `(2,2,1,1)` moment of
the erased support at `P`, `Q`:
`doubledDoubledDoubledQuadReMoment C P Q R =
realMoment 2 · doubledDoubledQuadReMoment
(C.erase R) P Q`. The same strip as
`doubledDoubledDoubledQuadReMoment_strip_first` with
the stripped column exchanged. -/
theorem doubledDoubledDoubledQuadReMoment_strip_third
    (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    {P Q R : LayerColumn N} (hPC : P ∈ C) (hQC : Q ∈ C)
    (hQP : Q ≠ P) (hRP : R ≠ P) (hRQ : R ≠ Q)
    {s : LayerSite N}
    (hsR : s ∈ colSites R)
    (hpriv : ∀ Y ∈ C, Y ≠ R → s ∉ colSites Y) :
    doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
      = realMoment ρ μG 2
        * doubledDoubledQuadReMoment ρ μG (C.erase R) P Q u u' := by
  classical
  set a : LayerColumn N → ℕ :=
    fun Y => if Y = P then 2 else if Y = Q then 2 else 1
    with ha_def
  have haP : a P = 2 := by
    rw [ha_def]
    exact if_pos rfl
  have haQ : a Q = 2 := by
    rw [ha_def]
    exact (if_neg hQP).trans (if_pos rfl)
  have haT0 : ∀ Y ∈ ((C.erase R).erase P).erase Q, a Y = 1 := by
    intro Y hY
    have hYP : Y ≠ P :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hY).2).1
    have hYQ : Y ≠ Q := (Finset.mem_erase.mp hY).1
    rw [ha_def]
    exact (if_neg hYP).trans (if_neg hYQ)
  have hRF : R ∉ C.erase R :=
    fun h => (Finset.mem_erase.mp h).1 rfl
  have hsF : ∀ Y ∈ C.erase R, s ∉ colSites Y :=
    fun Y hY => hpriv Y (Finset.mem_erase.mp hY).2
      (Finset.mem_erase.mp hY).1
  have hPmem : P ∈ C.erase R :=
    Finset.mem_erase.mpr ⟨fun h => hRP h.symm, hPC⟩
  have hQmem : Q ∈ (C.erase R).erase P :=
    Finset.mem_erase.mpr ⟨hQP, Finset.mem_erase.mpr
      ⟨fun h => hRQ h.symm, hQC⟩⟩
  have hcommT : ((C.erase P).erase Q).erase R
      = ((C.erase R).erase P).erase Q := by
    ext Z
    simp only [Finset.mem_erase]
    tauto
  have hT0prod : ∀ α : LayerSite N → G,
      ∏ Z ∈ ((C.erase R).erase P).erase Q,
          (colRe ρ u u' Z α) ^ (a Z)
        = ∏ Z ∈ ((C.erase R).erase P).erase Q,
            colRe ρ u u' Z α :=
    fun α => Finset.prod_congr rfl fun Z hZ => by
      rw [haT0 Z hZ, pow_one]
  have hprod : ∀ α : LayerSite N → G,
      ∏ Y ∈ C.erase R, (colRe ρ u u' Y α) ^ (a Y)
        = (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
          * ∏ Z ∈ ((C.erase R).erase P).erase Q,
              colRe ρ u u' Z α := by
    intro α
    calc ∏ Y ∈ C.erase R, (colRe ρ u u' Y α) ^ (a Y)
        = (colRe ρ u u' P α) ^ 2
            * ((colRe ρ u u' Q α) ^ 2
              * ∏ Z ∈ ((C.erase R).erase P).erase Q,
                  (colRe ρ u u' Z α) ^ (a Z)) := by
          rw [← Finset.mul_prod_erase (C.erase R)
            (fun Y => (colRe ρ u u' Y α) ^ (a Y)) hPmem,
            ← Finset.mul_prod_erase ((C.erase R).erase P)
            (fun Y => (colRe ρ u u' Y α) ^ (a Y)) hQmem,
            haP, haQ]
      _ = (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
            * ∏ Z ∈ ((C.erase R).erase P).erase Q,
                colRe ρ u u' Z α := by
          rw [hT0prod α]
          ring
  have hpt : ∀ α : LayerSite N → G,
      (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
          * (colRe ρ u u' R α) ^ 2
          * ∏ Z ∈ ((C.erase P).erase Q).erase R,
              colRe ρ u u' Z α
        = (∏ Y ∈ C.erase R, (colRe ρ u u' Y α) ^ (a Y))
          * (colRe ρ u u' R α) ^ (2 : ℕ) := fun α => by
    rw [hcommT, hprod α]
    ring
  calc doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
      = ∫ α : LayerSite N → G,
          (∏ Y ∈ C.erase R, (colRe ρ u u' Y α) ^ (a Y))
            * (colRe ρ u u' R α) ^ (2 : ℕ)
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = realMoment ρ μG 2
          * ∫ α : LayerSite N → G,
              ∏ Y ∈ C.erase R, (colRe ρ u u' Y α) ^ (a Y)
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_colRe_pow_split_finset ρ μG hN hN3 hρcont u u'
          (C.erase R) a R hRF s hsR hsF 2
    _ = realMoment ρ μG 2
          * doubledDoubledQuadReMoment ρ μG (C.erase R) P Q
            u u' := by
        refine congrArg _ ?_
        exact integral_congr_ae (Filter.Eventually.of_forall hprod)

/-- **Strip at the single column.** If the single
(undoubled) column `S ∈ C`, distinct from all three
doubled columns, has a private site `s` within the
support `C`, the triple-doubled moment splits off the
single-site mean:
`doubledDoubledDoubledQuadReMoment C P Q R = e₁ ·
doubledDoubledDoubledQuadReMoment (C.erase S) P Q R`.
The exponent-blind strip at exponent function
`(2 at P, 2 at Q, 2 at R, 1 elsewhere)` and `k = 1`,
following `doubledDoubledQuadReMoment_strip_single`
with a third doubled column carried through the
exponent function. Together with the three
doubled-column strips: at a non-primitive support
every triple-doubled moment reduces to lower content,
so the `(2,2,2,1)` channel's dependent content is
carried by the primitive quads — exactly the supports
`kappa7chan2221` sums over. -/
theorem doubledDoubledDoubledQuadReMoment_strip_single
    (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    {P Q R S : LayerColumn N} (hPC : P ∈ C) (hQC : Q ∈ C)
    (hRC : R ∈ C) (hSC : S ∈ C) (hSP : S ≠ P) (hSQ : S ≠ Q)
    (hSR : S ≠ R) (hQP : Q ≠ P) (hRP : R ≠ P) (hRQ : R ≠ Q)
    {s : LayerSite N}
    (hsS : s ∈ colSites S)
    (hpriv : ∀ Y ∈ C, Y ≠ S → s ∉ colSites Y) :
    doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
      = e1 ρ μG
        * doubledDoubledDoubledQuadReMoment ρ μG (C.erase S)
          P Q R u u' := by
  classical
  set T0 : Finset (LayerColumn N) :=
    (((C.erase S).erase P).erase Q).erase R with hT0_def
  set a : LayerColumn N → ℕ :=
    fun Y => if Y = P then 2 else if Y = Q then 2
      else if Y = R then 2 else 1
    with ha_def
  have haP : a P = 2 := by
    rw [ha_def]
    exact if_pos rfl
  have haQ : a Q = 2 := by
    rw [ha_def]
    exact (if_neg hQP).trans (if_pos rfl)
  have haR : a R = 2 := by
    rw [ha_def]
    exact (if_neg hRP).trans ((if_neg hRQ).trans (if_pos rfl))
  have haT0 : ∀ Y ∈ T0, a Y = 1 := by
    intro Y hY
    have hYP : Y ≠ P :=
      (Finset.mem_erase.mp
        (Finset.mem_erase.mp (Finset.mem_erase.mp hY).2).2).1
    have hYQ : Y ≠ Q :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hY).2).1
    have hYR : Y ≠ R := (Finset.mem_erase.mp hY).1
    rw [ha_def]
    exact (if_neg hYP).trans ((if_neg hYQ).trans (if_neg hYR))
  have hRnotT0 : R ∉ T0 :=
    fun h => (Finset.mem_erase.mp h).1 rfl
  have hQnotT1 : Q ∉ insert R T0 := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hRQ h.symm
    · exact (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).1 rfl
  have hPnotT2 : P ∉ insert Q (insert R T0) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hQP h.symm
    · rcases Finset.mem_insert.mp h with h | h
      · exact hRP h.symm
      · exact (Finset.mem_erase.mp
          (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).2).1 rfl
  have hSnotT : S ∉ insert P (insert Q (insert R T0)) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hSP h
    · rcases Finset.mem_insert.mp h with h | h
      · exact hSQ h
      · rcases Finset.mem_insert.mp h with h | h
        · exact hSR h
        · exact (Finset.mem_erase.mp
            (Finset.mem_erase.mp
              (Finset.mem_erase.mp
                (Finset.mem_erase.mp h).2).2).2).1 rfl
  have hsF : ∀ Y ∈ insert P (insert Q (insert R T0)),
      s ∉ colSites Y := by
    intro Y hY
    apply hpriv Y _ _
    · rcases Finset.mem_insert.mp hY with rfl | hY
      · exact hPC
      · rcases Finset.mem_insert.mp hY with rfl | hY
        · exact hQC
        · rcases Finset.mem_insert.mp hY with rfl | hY
          · exact hRC
          · exact (Finset.mem_erase.mp
              (Finset.mem_erase.mp
                (Finset.mem_erase.mp
                  (Finset.mem_erase.mp hY).2).2).2).2
    · rintro rfl
      exact hSnotT hY
  have hcommS : (((C.erase P).erase Q).erase R).erase S = T0 := by
    rw [hT0_def]
    ext Z
    simp only [Finset.mem_erase]
    tauto
  have hSmem : S ∈ ((C.erase P).erase Q).erase R :=
    Finset.mem_erase.mpr ⟨hSR, Finset.mem_erase.mpr ⟨hSQ,
      Finset.mem_erase.mpr ⟨hSP, hSC⟩⟩⟩
  have hsplit : ∀ α : LayerSite N → G,
      ∏ Z ∈ ((C.erase P).erase Q).erase R, colRe ρ u u' Z α
        = colRe ρ u u' S α
          * ∏ Z ∈ T0, colRe ρ u u' Z α := by
    intro α
    rw [← hcommS]
    exact (Finset.mul_prod_erase (((C.erase P).erase Q).erase R)
      (fun Z => colRe ρ u u' Z α) hSmem).symm
  have hprodT : ∀ α : LayerSite N → G,
      ∏ Y ∈ insert P (insert Q (insert R T0)),
          (colRe ρ u u' Y α) ^ (a Y)
        = (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
          * (colRe ρ u u' R α) ^ 2
          * ∏ Z ∈ T0, colRe ρ u u' Z α := by
    intro α
    have hT0prod : ∏ Z ∈ T0, (colRe ρ u u' Z α) ^ (a Z)
        = ∏ Z ∈ T0, colRe ρ u u' Z α :=
      Finset.prod_congr rfl fun Z hZ => by
        rw [haT0 Z hZ, pow_one]
    rw [Finset.prod_insert hPnotT2, Finset.prod_insert hQnotT1,
      Finset.prod_insert hRnotT0, haP, haQ, haR, hT0prod]
    ring
  have hpt1 : ∀ α : LayerSite N → G,
      (colRe ρ u u' P α) ^ 2 * (colRe ρ u u' Q α) ^ 2
          * (colRe ρ u u' R α) ^ 2
          * ∏ Z ∈ ((C.erase P).erase Q).erase R,
              colRe ρ u u' Z α
        = (∏ Y ∈ insert P (insert Q (insert R T0)),
            (colRe ρ u u' Y α) ^ (a Y))
          * (colRe ρ u u' S α) ^ (1 : ℕ) := by
    intro α
    rw [hsplit α, hprodT α]
    simp only [pow_one]
    ring
  calc doubledDoubledDoubledQuadReMoment ρ μG C P Q R u u'
      = ∫ α : LayerSite N → G,
          (∏ Y ∈ insert P (insert Q (insert R T0)),
            (colRe ρ u u' Y α) ^ (a Y))
            * (colRe ρ u u' S α) ^ (1 : ℕ)
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt1)
    _ = realMoment ρ μG 1
          * ∫ α : LayerSite N → G,
              ∏ Y ∈ insert P (insert Q (insert R T0)),
                (colRe ρ u u' Y α) ^ (a Y)
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_colRe_pow_split_finset ρ μG hN hN3 hρcont u u'
          (insert P (insert Q (insert R T0))) a S hSnotT s hsS hsF 1
    _ = e1 ρ μG
          * doubledDoubledDoubledQuadReMoment ρ μG (C.erase S)
            P Q R u u' := by
        rw [realMoment_one]
        refine congrArg _ ?_
        exact integral_congr_ae (Filter.Eventually.of_forall hprodT)

end Channel7

end ThetLogos
