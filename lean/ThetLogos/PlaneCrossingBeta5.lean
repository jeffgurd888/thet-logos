/-
# ThetLogos.PlaneCrossingBeta5 — κ₅^dep at general (G, ρ):
the β⁵ dependent coefficient as an owned object, the death
of the all-distinct channel, and the (2,1,1,1) channel named

**Fences, up front.** NO CLAIM. Parts of the Clay
Yang–Mills statement closed by this module: **0**. Dials
0/4. This is a DEFINITION brick (B5-1): it owns the fifth
Taylor coefficient of the layer kernel `𝒜 = layerKernel`
at general `(G, ρ)`, its constant part in the assembly's
pattern values, and its dependent part `κ₅^dep` under the
same fence as order 4. The assembly identity expressing
`κ₅^dep` through the (2,1,1,1) channel (normalization and
baseline) is B5-2's content and is **named here as a seam,
not asserted**. **No sign is asserted for `κ₅^dep`
anywhere in this module**: the sign question at order 5 is
FRONTIER — its surviving channel has degree-(2,1) sites,
whose triple twirl `∫ ρ(g) ρ(g) ρ̄(g)` is not owned by any
module in the tree (PW-1/PW-3 are pair twirls), and no
exhibited-square form for the doubled moment is known.

**The named-space fence (K-K4G-2, inherited).**
"Dependent part" means the cumulant over partitions of
the DISTINCT-column support, exactly as at order 4:
patterns on at most 3 distinct columns factor into
constants at arbitrary exponents (the private-site strip
`integral_colRe_pow_split_finset` is exponent-blind, two
distinct columns are independent at every degree, and a
3-column support always has a private site at even `N`),
so the constant assembly below carries their full values;
the two patterns on 4 and 5 distinct columns enter the
constant part only through their fully-split baselines,
and their dependent excesses are the content of
`κ₅^dep`. The `N = 2` sector and the `N = 4` wrap sector
are fenced exactly as at order 4 (`3 ≤ N` throughout).

**The β⁴ endpoint, at its exact scope (restated, not
extended).** `phi_diag_nonneg` + `kappa4dep_diag_nonneg`
(`PhiAssembly`) give the DIAGONAL `u' = u` sign of the
β⁴ dependent coefficient `κ₄^dep` only, at (Even `N`,
`3 ≤ N`), `RepIrreducible ρ`. β⁵, off-diagonal κ₄,
reducible ρ, and `𝒜 ⪰ 0` in the large are untouched by
it — and untouched here.

**What this module proves.** (i) The order-5 expansion of
the stratum average, real form, with tail `R₆`.
(ii) The all-distinct `(1,1,1,1,1)` channel carries no
genuinely fivefold dependent content: by B5-0
(`OrderFiveSelection.no_primitive_five_support_sharing`)
every 5-column set has a column with a private site
within the set, and the private-site strip then factors
its character moment as `e₁` times an order-4 moment
(`pentaReMoment_factors_of_card_five`). (iii) The
(2,1,1,1) channel's raw moment is defined
(`doubledQuadReMoment`), its channel sum is named
(`kappa5chan2111`), and its private-site strips are
proved: a doubled column or a single column sitting at
a private site of a 4-support strips off against
`realMoment 2` resp. `e₁`, so the channel's dependent
content is carried by primitive quads — the input B5-2's
assembly consumes.
-/

import ThetLogos.PlaneCrossingBeta4
import ThetLogos.OrderFiveSelection

open MeasureTheory Finset

namespace ThetLogos

section Coeff5

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- The fifth β-coefficient of `𝒜`: `∫ layerDensSum⁵ / 120`
(so `𝒜 = 1 − βC₁ + β²C₂ − β³C₃ + β⁴C₄ − β⁵C₅ + O(β⁶)`).
Defined by the same construction as `betaCoeff4`. -/
noncomputable def betaCoeff5 (u u' : LayerLink N → G) : ℝ :=
  ∫ α, (layerDensSum ρ α u u') ^ 5 / 120
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- **The expansion, real form, at order 5.** For every
real `β`, the stratum average of the layer exponential
is `1 − βC₁ + β²C₂ − β³C₃ + β⁴C₄ − β⁵C₅ + R₆(β)` with
`R₆` the displayed tail series. FENCE: a Taylor
coefficient identity; no positivity of `𝒜` at any
`β > 0` follows, and no sign for `betaCoeff5` or any
part of it is asserted. Proved by the order-4 pattern
(`layerKernel_real_expansion4`) with one more term
split off. -/
theorem layerKernel_real_expansion5 (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) :
    ∫ α, Real.exp (-(β * layerDensSum ρ α u u'))
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = 1 - β * betaCoeff1 ρ μG u u' + β ^ 2 * betaCoeff2 ρ μG u u'
        - β ^ 3 * betaCoeff3 ρ μG u u'
        + β ^ 4 * betaCoeff4 ρ μG u u'
        - β ^ 5 * betaCoeff5 ρ μG u u'
        + ∑' (k : ℕ), ∫ α, (-β * layerDensSum ρ α u u') ^ (k + 6)
            / ((Nat.factorial (k + 6) : ℝ))
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
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
    ← (hasSum_integral_of_summable_integral_norm
      (fun n => integrable_term ρ μG hN hρcont β u u' n)
      (summable_norm_term_int ρ μG hN hρcont β u u')).tsum_eq,
    ← hSumm.sum_add_tsum_nat_add 6,
    Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero,
    ht0, ht1, ht2, ht3, ht4, ht5]
  ring

end Coeff5

section ClosedForm5

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- The constant part of the fifth coefficient, in the
assembly's pattern values: with `M = colCount N`,
`B = 1 − e₁/d`, `Aⱼ = densMomentValue j`:
`M·A₅ + 5M(M−1)·A₄B + 10M(M−1)·A₃A₂
+ 10M(M−1)(M−2)·A₃B² + 15M(M−1)(M−2)·A₂²B
+ 10M(M−1)(M−2)(M−3)·A₂B³
+ M(M−1)(M−2)(M−3)(M−4)·B⁵`.
The coefficients are the ordered-tuple counts of the
exponent patterns of `(Σ_P x_P)⁵`, in the same
un-divided assembly shape as `kappa4Const`. The
patterns on at most 3 distinct columns — `(5)`, `(4,1)`,
`(3,2)`, `(3,1,1)`, `(2,2,1)` — enter at their full
values (they factor into constants at arbitrary
exponents). The patterns `(2,1,1,1)` and `(1,1,1,1,1)`
enter only through their fully-split baselines
`A₂B³` resp. `B⁵`: their dependent excesses are the
content of `kappa5dep` — the `(1,1,1,1,1)` excess is
killed in §Distinct below, the `(2,1,1,1)` excess is
the channel of §Channel. -/
noncomputable def kappa5Const : ℝ :=
  colCount N * densMomentValue ρ μG 5
    + 5 * colCount N * (colCount N - 1)
      * densMomentValue ρ μG 4 * (1 - e1 ρ μG / (d : ℝ))
    + 10 * colCount N * (colCount N - 1)
      * densMomentValue ρ μG 3 * densMomentValue ρ μG 2
    + 10 * colCount N * (colCount N - 1) * (colCount N - 2)
      * densMomentValue ρ μG 3 * (1 - e1 ρ μG / (d : ℝ)) ^ 2
    + 15 * colCount N * (colCount N - 1) * (colCount N - 2)
      * (densMomentValue ρ μG 2) ^ 2 * (1 - e1 ρ μG / (d : ℝ))
    + 10 * colCount N * (colCount N - 1) * (colCount N - 2)
      * (colCount N - 3)
      * densMomentValue ρ μG 2 * (1 - e1 ρ μG / (d : ℝ)) ^ 3
    + colCount N * (colCount N - 1) * (colCount N - 2)
      * (colCount N - 3) * (colCount N - 4)
      * (1 - e1 ρ μG / (d : ℝ)) ^ 5

/-- **Coefficient audit of the constant assembly.** If
every pattern value is `1` (`Aⱼ = 1` for all `j` and
`B = 1`), the assembly totals `M⁵` — the number of
ordered 5-tuples of columns. This checks the seven
pattern coefficients and falling-factorial factors of
`kappa5Const` against the raw tuple count, in the
same way the order-4 assembly's coefficients total
`M⁴`. -/
theorem kappa5Const_eq_pow_five_of_moments_one
    (hA : ∀ j, densMomentValue ρ μG j = 1)
    (hB : 1 - e1 ρ μG / (d : ℝ) = 1) :
    kappa5Const (N := N) ρ μG = (colCount N) ^ 5 := by
  unfold kappa5Const
  rw [hA 5, hA 4, hA 3, hA 2, hB]
  ring

/-- **κ₅^dep**, the dependent part of the β⁵
coefficient: what remains of `betaCoeff5` after the
closed constant part is removed. Its content is the
`(2,1,1,1)` channel (§Channel); the assembly identity
expressing it through that channel is B5-2's seam,
named in the header and **not** asserted here. No sign
is asserted for it anywhere. -/
noncomputable def kappa5dep (u u' : LayerLink N → G) : ℝ :=
  betaCoeff5 ρ μG u u' - kappa5Const (N := N) ρ μG / 120

/-- `κ₅^dep` unfolds to its defining difference. -/
theorem kappa5dep_def (u u' : LayerLink N → G) :
    kappa5dep ρ μG u u'
      = betaCoeff5 ρ μG u u' - kappa5Const (N := N) ρ μG / 120 :=
  rfl

end ClosedForm5

section Distinct

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- The character moment of a finite set of columns at
order 5: `∫ ∏_{P ∈ C} Re χ(word_P)`, the raw
(un-cumulanted) moment of the all-distinct
`(1,1,1,1,1)` channel when `C` has five elements.
Defined by the same construction as `quadReMoment`
(which is the same integral at any support size). -/
noncomputable def pentaReMoment (C : Finset (LayerColumn N))
    (u u' : LayerLink N → G) : ℝ :=
  ∫ α, ∏ P ∈ C, colRe ρ u u' P α
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- The order-5 distinct moment is `quadReMoment`
itself: the moment construction is support-size
blind, and the order-4 machinery applies verbatim. -/
theorem pentaReMoment_eq_quadReMoment
    (C : Finset (LayerColumn N)) (u u' : LayerLink N → G) :
    pentaReMoment ρ μG C u u' = quadReMoment ρ μG C u u' :=
  rfl

/-- **Every 5-column set has a private-site column.**
At (Even `N`, `3 ≤ N`), any five distinct columns
contain a column `X` and a site `s ∈ colSites X` read
by no other column of the set. This is the
contrapositive of B5-0's
`no_primitive_five_support_sharing`: the sharing
property for a 5-set is uninhabited, so its negation —
a private site — is inhabited. -/
theorem exists_private_column_of_card_five (hN : Even N)
    (hN3 : 3 ≤ N) {C : Finset (LayerColumn N)} (hC : C.card = 5) :
    ∃ X ∈ C, ∃ s ∈ colSites X,
      ∀ Y ∈ C, Y ≠ X → s ∉ colSites Y := by
  classical
  by_contra hcon
  push_neg at hcon
  exact no_primitive_five_support_sharing hN hN3 C hC hcon

/-- **The all-distinct channel factors (its dependent
content vanishes).** At (Even `N`, `3 ≤ N`), for every
set `C` of five distinct columns there is a column
`X ∈ C` whose moment splits off against the single-site
mean: `pentaReMoment C = e₁ · quadReMoment (C.erase X)`.
So no genuinely fivefold moment survives at order 5:
every `(1,1,1,1,1)` contribution reduces to order-4
content times `e₁`, and the `(1,1,1,1,1)` pattern
enters `kappa5Const` at its fully-split baseline `B⁵`
with dependent excess exactly zero in the cumulant
fence's sense. (The naive difference
`pentaReMoment C − e₁⁵` does **not** vanish — a
plaquette plus a disjoint column gives
`e₁ · quadReMoment(plaquette)`; what vanishes is the
irreducible fivefold part, killed by the private-site
factorization.) Proof: the private column of
`exists_private_column_of_card_five`, stripped by the
exponent-blind engine `integral_colRe_pow_split_finset`
at exponents `1, 1`. -/
theorem pentaReMoment_factors_of_card_five (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    (hC : C.card = 5) :
    ∃ X ∈ C, pentaReMoment ρ μG C u u'
      = e1 ρ μG * quadReMoment ρ μG (C.erase X) u u' := by
  classical
  obtain ⟨X, hXC, s, hsX, hpriv⟩ :=
    exists_private_column_of_card_five (N := N) hN hN3 hC
  refine ⟨X, hXC, ?_⟩
  have hXF : X ∉ C.erase X :=
    fun h => (Finset.mem_erase.mp h).1 rfl
  have hsF : ∀ P ∈ C.erase X, s ∉ colSites P :=
    fun P hP => hpriv P (Finset.mem_erase.mp hP).2
      (Finset.mem_erase.mp hP).1
  have hsplit : pentaReMoment ρ μG C u u'
      = ∫ α : LayerSite N → G,
          (∏ P ∈ C.erase X,
            (colRe ρ u u' P α) ^ ((fun _ : LayerColumn N => 1) P))
            * (colRe ρ u u' X α) ^ (1 : ℕ)
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
    refine integral_congr_ae
      (Filter.Eventually.of_forall fun α => ?_)
    show (∏ P ∈ C, colRe ρ u u' P α) = _
    rw [← Finset.mul_prod_erase C (fun P => colRe ρ u u' P α) hXC]
    simp only [pow_one]
    ring
  calc pentaReMoment ρ μG C u u'
      = ∫ α : LayerSite N → G,
          (∏ P ∈ C.erase X,
            (colRe ρ u u' P α) ^ ((fun _ : LayerColumn N => 1) P))
            * (colRe ρ u u' X α) ^ (1 : ℕ)
          ∂(Measure.pi fun _ : LayerSite N => μG) := hsplit
    _ = realMoment ρ μG 1
          * ∫ α : LayerSite N → G, ∏ P ∈ C.erase X,
              (colRe ρ u u' P α) ^ ((fun _ : LayerColumn N => 1) P)
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_colRe_pow_split_finset ρ μG hN hN3 hρcont u u'
          (C.erase X) (fun _ => 1) X hXF s hsX hsF 1
    _ = e1 ρ μG * quadReMoment ρ μG (C.erase X) u u' := by
        rw [realMoment_one]
        refine congrArg _ ?_
        refine integral_congr_ae
          (Filter.Eventually.of_forall fun α => ?_)
        exact Finset.prod_congr rfl fun P _ => pow_one _

end Distinct

section Channel

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- The raw `(2,1,1,1)` moment at a 4-support `C` with
distinguished doubled column `P`: the stratum integral
of `(colRe P)² · ∏_{Q ∈ C.erase P} colRe Q` — the
character moment of the multiset `C + {P}` (the support
`C` with `P` counted twice). This is the order-5
analogue of `quadReMoment`: at order 4 the dependent
support is a set of distinct columns; at order 5 the
surviving dependent support is a set with one column
doubled (B5-0). -/
noncomputable def doubledQuadReMoment
    (C : Finset (LayerColumn N)) (P : LayerColumn N)
    (u u' : LayerLink N → G) : ℝ :=
  ∫ α, (colRe ρ u u' P α) ^ 2
      * ∏ Q ∈ C.erase P, colRe ρ u u' Q α
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- **The `(2,1,1,1)` channel expression**: the sum,
over primitive quads `C` and distinguished columns
`P ∈ C`, of the doubled-column moments. This is the
expression `kappa5dep` is expected to reduce to in
B5-2's assembly (with the assembly's normalization
and the fully-split baseline `A₂B³` of `kappa5Const`
accounted); that identity is the named seam and is
**not** asserted here. No sign is asserted for this
sum: at the doubled column's sites the moment carries
degree-(2,1) site factors, whose triple twirl is not
owned (see the header). -/
noncomputable def kappa5chan2111 (u u' : LayerLink N → G) : ℝ :=
  ∑ C ∈ primitiveQuads, ∑ P ∈ C,
    doubledQuadReMoment ρ μG C P u u'

/-- The doubled moment is the multiset moment: for
`P ∈ C` it equals the integral of the full support
product times one more factor of the doubled column,
`∫ (∏_{Q ∈ C} colRe Q) · colRe P`. -/
theorem doubledQuadReMoment_eq_mul
    {C : Finset (LayerColumn N)} {P : LayerColumn N}
    (hPC : P ∈ C) (u u' : LayerLink N → G) :
    doubledQuadReMoment ρ μG C P u u'
      = ∫ α, (∏ Q ∈ C, colRe ρ u u' Q α) * colRe ρ u u' P α
        ∂(Measure.pi fun _ : LayerSite N => μG) := by
  refine integral_congr_ae
    (Filter.Eventually.of_forall fun α => ?_)
  show (colRe ρ u u' P α) ^ 2
      * ∏ Q ∈ C.erase P, colRe ρ u u' Q α
      = (∏ Q ∈ C, colRe ρ u u' Q α) * colRe ρ u u' P α
  rw [← Finset.mul_prod_erase C (fun Q => colRe ρ u u' Q α) hPC]
  ring

/-- **Strip at the doubled column.** If the doubled
column `P` itself has a private site `s` within the
support `C` (no other column of `C` reads `s`), the
doubled moment splits off the second real moment:
`doubledQuadReMoment C P = realMoment 2 ·
quadReMoment (C.erase P)`. The exponent-blind strip
`integral_colRe_pow_split_finset` at exponents
`(1, 2)`. So a doubled column at a private site
carries no dependent content: the channel's content
needs the doubled column's sites shared. -/
theorem doubledQuadReMoment_strip_doubled (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    {P : LayerColumn N} {s : LayerSite N}
    (hsP : s ∈ colSites P)
    (hpriv : ∀ Y ∈ C, Y ≠ P → s ∉ colSites Y) :
    doubledQuadReMoment ρ μG C P u u'
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
  calc doubledQuadReMoment ρ μG C P u u'
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
the support `C`, the doubled moment splits off the
single-site mean:
`doubledQuadReMoment C P = e₁ · doubledQuadReMoment
(C.erase Q) P`. The exponent-blind strip at exponent
function `(2 at P, 1 elsewhere)` and `k = 1`. Together
with `doubledQuadReMoment_strip_doubled`: at a
non-primitive support every doubled moment reduces to
lower content, so the `(2,1,1,1)` channel's dependent
content is carried by the primitive quads — exactly
the supports `kappa5chan2111` sums over. -/
theorem doubledQuadReMoment_strip_single (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {C : Finset (LayerColumn N)}
    {P Q : LayerColumn N} (hPC : P ∈ C) (hQC : Q ∈ C)
    (hQP : Q ≠ P) {s : LayerSite N}
    (hsQ : s ∈ colSites Q)
    (hpriv : ∀ Y ∈ C, Y ≠ Q → s ∉ colSites Y) :
    doubledQuadReMoment ρ μG C P u u'
      = e1 ρ μG * doubledQuadReMoment ρ μG (C.erase Q) P u u' := by
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
  calc doubledQuadReMoment ρ μG C P u u'
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
    _ = e1 ρ μG * doubledQuadReMoment ρ μG (C.erase Q) P u u' := by
        rw [realMoment_one]
        refine congrArg _ ?_
        exact integral_congr_ae (Filter.Eventually.of_forall h2)

end Channel

end ThetLogos
