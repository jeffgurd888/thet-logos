/-
# ThetLogos.PolymerActivity — LOC-1: the polymer activity brick

**Fences, up front.** NO CLAIM. Parts of the Clay Yang–Mills
statement closed by this module: **0**. Uniformity across N
remains open. This module owns polymer *activities* and
their majorants at fixed even `N`; the Kirkwood–Salsburg
convergence (LOC-2) and the `(U-vol)` regime theorem
(LOC-3) are later bricks that consume the majorant proved
here. Cross-column statements need `3 ≤ N`, as in β2-1b
(`N = 2` is fenced out there too).

## What this module proves

The polymer species of the LOC-0 scoping
(`loc0-polymer-scoping-2026-10-26.md` §1, §3):
character-labeled connected column clusters, targeted at
the layer kernel `𝒜`. A label, in the labeling the
corpus's landed expansion (β2-1b) actually uses, is a
Taylor degree of a column's density factor
`dens_P = 1 - r_P/d`, `r_P = Re χ(word_P)`.

1. **The activity, defined and closed.** The degree-`k`
   activity `colActivity` is the α-integrated Taylor
   coefficient `∫ (-β)ᵏ/k! · dens_Pᵏ`. It is a function of
   the label alone: `colActivity_closed` expresses it
   through the real Haar moments `μₐ = ∫ (Re χ)ᵃ`
   (`μ₀ = 1`, `μ₁ = e₁`, `μ₂ = q₂`), and
   `colActivity_independent` removes the column (base
   site and direction alike) and the boundary links.
   β2-1b's `C₁`, `C₂` are restated as activity statements
   (`betaCoeff1_activity`, `betaCoeff2_activity`), and
   `κ₂` as the constant `(1/(4d²)) · Re m₂`
   (`activity_kappa2`) — no irreducibility hypothesis
   anywhere.
2. **The two-column theory.** Distinct columns are fully
   independent under the stratum measure: every mixed
   character moment factors, `∫ r_Pʲ r_Qᵏ = μⱼ μₖ`
   (`integral_colRe_pow_mul`, by the private-site
   mechanism of β2-1b's P₀-collapse, extended to all
   degrees), hence every density moment factors
   (`integral_colDens_pow_mul`) and **every connected
   two-column activity vanishes identically**
   (`connectedActivity_eq_zero`; named cases
   `connectedActivity11_eq_zero`, `...21...`, `...22...`).
   The pair activities themselves are exactly the
   products of the single-column forms
   (`pairActivity21`, `pairActivity22`).
3. **The scalar majorant** (what LOC-2 consumes):
   `|ζₖ| ≤ (2|β|)ᵏ/k!`, via contraction numbers
   `|μₐ|/dᵃ ≤ 1` (`abs_colActivity_le_contraction`,
   `abs_colActivity_le`), and the total single-column
   bound `∑_{k≥1} |ζₖ| ≤ exp(2β) - 1` for `β ≥ 0`
   (`total_colActivity_le`).
4. **The dependent sector starts at degree 3**:
   β2-1b's vanishing of the `(u, u')`-dependent part
   through degree 2 and its `O(β³)` tail bound are
   restated as `activity_dep_part_degree_le_two_zero` and
   `dependent_sector_majorant`; the single-column
   activities are `(u, u')`-free at every degree
   (`colActivity_independent`), so the tail *is* the
   dependent sector.

## Two corrections to the scoping memo, on the face

- The memo expected the first nonzero connected
  two-column activities at degrees `(2,1)` and `(2,2)`.
  On the landed mathematics the connected parts are
  **zero at every degree pair**: the private-site
  factorization is exact, not a second-order accident.
  The memo's pre-named PARTIAL seam (land `(2,2)` as a
  bounded-but-uncomputed contraction) is therefore
  **not taken** — the contraction was computed, and it
  is the product form with zero connected part.
- The memo's majorant constant `(2β/d)ᵏ/k!` belongs to a
  per-leg character normalization. For the density
  activity it is false: at `d = 2`, `ρ = sign ⊕ sign`,
  `∫ densᵏ = 2ᵏ⁻¹ > (2/d)ᵏ = 1` for `k ≥ 2`. The
  majorant proved here is `(2|β|)ᵏ/k!` in the density
  normalization, with the contraction-number form —
  group data only `d` and the moments, entering only
  through numbers `≤ 1` — in
  `abs_colActivity_le_contraction`.

Conventions follow `PlaneCrossingBeta2`: `ρ` a bare
`MonoidHom` into a unitary group; moment statements carry
the standing continuity hypothesis `hρcont`.
-/

import ThetLogos.PlaneCrossingBeta2

namespace ThetLogos

open Finset MeasureTheory

section Activity

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- The `j`-th real Haar moment of the character of `ρ`:
`μⱼ = ∫ (Re χ)ʲ dμG`. The group data a single column's
activity can see, beyond `d` itself. `μ₀ = 1`, `μ₁ = e₁`,
`μ₂ = q₂`. -/
noncomputable def realMoment (j : ℕ) : ℝ :=
  ∫ g, ((charFn ρ g).re) ^ j ∂μG

theorem realMoment_zero : realMoment ρ μG 0 = 1 := by
  unfold realMoment
  simp

theorem realMoment_one : realMoment ρ μG 1 = e1 ρ μG := by
  simp [realMoment, e1]

theorem realMoment_two : realMoment ρ μG 2 = q2 ρ μG := by
  simp [realMoment, q2]

/-- Integrability of the moment integrand: `(Re χ)ʲ` is
bounded by `dʲ`. -/
theorem integrable_reCharFn_pow
    (hρcont : Continuous fun g : G => repMatrix ρ g) (j : ℕ) :
    Integrable (fun g => ((charFn ρ g).re) ^ j) μG :=
  Integrable.of_bound
    (((Complex.measurable_re.comp
      (measurable_charFn ρ hρcont)).pow_const j)).aestronglyMeasurable
    ((d : ℝ) ^ j) (Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_re_charFn_le ρ g) j)

/-- Every real moment is bounded by the trivial contraction:
`|μⱼ| ≤ dʲ`. -/
theorem abs_realMoment_le
    (hρcont : Continuous fun g : G => repMatrix ρ g) (j : ℕ) :
    |realMoment ρ μG j| ≤ (d : ℝ) ^ j := by
  unfold realMoment
  calc |∫ g, ((charFn ρ g).re) ^ j ∂μG|
      ≤ ∫ g, |((charFn ρ g).re) ^ j| ∂μG :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _g, (d : ℝ) ^ j ∂μG :=
        integral_mono_ae (integrable_reCharFn_pow ρ μG hρcont j).abs
          (integrable_const _)
          (Filter.Eventually.of_forall fun g => by
            show |((charFn ρ g).re) ^ j| ≤ (d : ℝ) ^ j
            rw [abs_pow]
            exact pow_le_pow_left₀ (abs_nonneg _)
              (abs_re_charFn_le ρ g) j)
    _ = (d : ℝ) ^ j := by simp

/-- The normalized contraction number of the `j`-th moment:
`|μⱼ| / dʲ`. -/
noncomputable def contractionNumber (j : ℕ) : ℝ :=
  |realMoment ρ μG j| / (d : ℝ) ^ j

/-- **Every contraction number is at most `1`** — the only
fact about the moments the scalar majorant consumes. -/
theorem contractionNumber_le_one
    (hρcont : Continuous fun g : G => repMatrix ρ g) (j : ℕ) :
    contractionNumber ρ μG j ≤ 1 := by
  by_cases hj : j = 0
  · subst hj
    simp [contractionNumber, realMoment_zero]
  · by_cases hd : (d : ℝ) = 0
    · simp [contractionNumber, hd, zero_pow hj]
    · have hdpos : (0 : ℝ) < (d : ℝ) ^ j :=
        pow_pos (lt_of_le_of_ne (Nat.cast_nonneg d) (Ne.symm hd)) j
      rw [contractionNumber, div_le_one hdpos]
      exact abs_realMoment_le ρ μG hρcont j

/-- A column's `j`-th character moment: the stratum integral
of `r_Pʲ`, where `r_P = colRe` is the column's real
character. A priori a function of the column, the boundary
links, and `j`; the next theorem removes all but `j`. -/
noncomputable def colMoment (u u' : LayerLink N → G)
    (P : LayerColumn N) (j : ℕ) : ℝ :=
  ∫ α, (colRe ρ u u' P α) ^ j
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- Powers of a column's real character are integrable
(bounded by `dʲ`). -/
theorem integrable_colRe_pow
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P : LayerColumn N) (j : ℕ) :
    Integrable (fun α => (colRe ρ u u' P α) ^ j)
      (Measure.pi fun _ : LayerSite N => μG) :=
  Integrable.of_bound
    ((measurable_colRe ρ hρcont u u' P).pow_const j).aestronglyMeasurable
    ((d : ℝ) ^ j) (Filter.Eventually.of_forall fun α => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_re_charFn_le ρ _) j)

/-- **A column's character moment is the Haar moment.** For
every column `P`, every boundary links `(u, u')`, and every
`j`: the word is a translate of the base coordinate, hence
Haar-uniform (β2-1b's `integral_word_moment_re`). The moment
depends on the label `j` alone — not on the column's base
site `c`, not on its direction `ν`, not on `(u, u')`. -/
theorem colMoment_eq (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P : LayerColumn N) (j : ℕ) :
    colMoment ρ μG u u' P j = realMoment ρ μG j :=
  integral_word_moment_re ρ μG hN hρcont (F := fun x : ℝ => x ^ j)
    (by exact continuous_id.pow j) (C := (d : ℝ) ^ j)
    (fun x hx => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg x) hx j)
    u u' P.1 P.2.1 P.2.2

/-- The density of a column, split as vacuum plus character
part: `dens = 1 + (-d⁻¹) · r_P`. Holds also at `d = 0`
(both sides are `1` there, since `χ ≡ 0`). -/
theorem colDensC_eq_one_add (u u' : LayerLink N → G)
    (P : LayerColumn N) (α : LayerSite N → G) :
    colDensC ρ u u' P α
      = 1 + (-(d : ℝ)⁻¹) * colRe ρ u u' P α := by
  rw [colDensC_eq, div_eq_inv_mul]
  ring

/-- Binomial expansion of `(1 + x)ʲ` in the form the activity
consumes. -/
theorem one_add_pow_expand (x : ℝ) (j : ℕ) :
    (1 + x) ^ j
      = ∑ a ∈ Finset.range (j + 1), ((j.choose a : ℝ)) * x ^ a := by
  rw [add_comm (1 : ℝ) x, add_pow]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [one_pow, mul_one]
  ring

/-- Pointwise binomial expansion of a column density power. -/
theorem colDensC_pow_expand (u u' : LayerLink N → G)
    (P : LayerColumn N) (α : LayerSite N → G) (j : ℕ) :
    (colDensC ρ u u' P α) ^ j
      = ∑ a ∈ Finset.range (j + 1), ((j.choose a : ℝ))
          * ((-(d : ℝ)⁻¹) * colRe ρ u u' P α) ^ a := by
  rw [colDensC_eq_one_add ρ u u' P α, one_add_pow_expand]

/-- A column's `j`-th density moment: the stratum integral
of `dens_Pʲ`. -/
noncomputable def colDensMoment (u u' : LayerLink N → G)
    (P : LayerColumn N) (j : ℕ) : ℝ :=
  ∫ α, (colDensC ρ u u' P α) ^ j
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- **Closed form of the density moment.** Only the label
`j` and the Haar moments enter:
`∫ dens_Pʲ = ∑_{a ≤ j} (j choose a) (-d⁻¹)ᵃ μₐ`. In
particular the value is the same for every column and every
`(u, u')`. -/
theorem colDensMoment_closed (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P : LayerColumn N) (j : ℕ) :
    colDensMoment ρ μG u u' P j
      = ∑ a ∈ Finset.range (j + 1), ((j.choose a : ℝ))
          * (-(d : ℝ)⁻¹) ^ a * realMoment ρ μG a := by
  unfold colDensMoment
  rw [integral_congr_ae (Filter.Eventually.of_forall fun α =>
      colDensC_pow_expand ρ u u' P α j), integral_finsetSum]
  · refine Finset.sum_congr rfl fun a _ => ?_
    have hpt : ∀ α : LayerSite N → G,
        ((-(d : ℝ)⁻¹) * colRe ρ u u' P α) ^ a
          = (-(d : ℝ)⁻¹) ^ a * (colRe ρ u u' P α) ^ a :=
      fun α => mul_pow _ _ _
    rw [integral_const_mul,
      integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_const_mul]
    have h2 : (∫ α, (colRe ρ u u' P α) ^ a
          ∂(Measure.pi fun _ : LayerSite N => μG))
        = realMoment ρ μG a :=
      colMoment_eq ρ μG hN hρcont u u' P a
    rw [h2]
    ring
  · intro a _
    have hfun : (fun α : LayerSite N → G =>
          ((j.choose a : ℝ)) * ((-(d : ℝ)⁻¹) * colRe ρ u u' P α) ^ a)
        = (fun α : LayerSite N → G =>
          (((j.choose a : ℝ)) * (-(d : ℝ)⁻¹) ^ a)
            * (colRe ρ u u' P α) ^ a) := by
      funext α
      rw [mul_pow, mul_assoc]
    rw [hfun]
    exact (integrable_colRe_pow ρ μG hρcont u u' P a).const_mul _

/-- Degree 1: `∫ dens_P = 1 - e₁/d` (β2-1b's first moment,
as an activity value). -/
theorem colDensMoment_one (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P : LayerColumn N) :
    colDensMoment ρ μG u u' P 1 = 1 - e1 ρ μG / (d : ℝ) := by
  rw [colDensMoment_closed ρ μG hN hρcont u u' P 1]
  norm_num [Finset.sum_range_succ, realMoment_zero, realMoment_one,
    div_eq_inv_mul]
  ring

/-- Degree 2, self-paired: `∫ dens_P² = 1 - 2e₁/d + q₂/d²`
(β2-1b's diagonal form). -/
theorem colDensMoment_two (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P : LayerColumn N) :
    colDensMoment ρ μG u u' P 2
      = 1 - 2 * e1 ρ μG / (d : ℝ) + q2 ρ μG / (d : ℝ) ^ 2 := by
  rw [colDensMoment_closed ρ μG hN hρcont u u' P 2]
  norm_num [Finset.sum_range_succ, realMoment_zero, realMoment_one,
    realMoment_two, div_eq_inv_mul, inv_pow]
  ring

/-- **The activity of a single column's degree-`k` label**:
the α-integrated Taylor coefficient of the column's
Boltzmann factor, `∫ (-β)ᵏ/k! · dens_Pᵏ`. -/
noncomputable def colActivity (β : ℝ) (k : ℕ)
    (u u' : LayerLink N → G) (P : LayerColumn N) : ℝ :=
  ∫ α, (-β) ^ k / ((Nat.factorial k : ℝ)) * (colDensC ρ u u' P α) ^ k
    ∂(Measure.pi fun _ : LayerSite N => μG)

theorem colActivity_eq (β : ℝ) (k : ℕ)
    (u u' : LayerLink N → G) (P : LayerColumn N) :
    colActivity ρ μG β k u u' P
      = (-β) ^ k / ((Nat.factorial k : ℝ)) * colDensMoment ρ μG u u' P k := by
  unfold colActivity colDensMoment
  exact integral_const_mul _ _

/-- **The activity in closed form** — a function of the
label `k` and the Haar moments alone. -/
theorem colActivity_closed (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (k : ℕ) (u u' : LayerLink N → G) (P : LayerColumn N) :
    colActivity ρ μG β k u u' P
      = (-β) ^ k / ((Nat.factorial k : ℝ))
        * ∑ a ∈ Finset.range (k + 1), ((k.choose a : ℝ))
            * (-(d : ℝ)⁻¹) ^ a * realMoment ρ μG a := by
  rw [colActivity_eq, colDensMoment_closed ρ μG hN hρcont]

/-- **The activity is a function of the label alone**
(spec item 1): it does not depend on the column — neither
its base site `c` (translation) nor its direction `ν` — nor
on the boundary links `(u, u')`. -/
theorem colActivity_independent (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (k : ℕ) (u u' v v' : LayerLink N → G)
    (P Q : LayerColumn N) :
    colActivity ρ μG β k u u' P = colActivity ρ μG β k v v' Q := by
  rw [colActivity_closed ρ μG hN hρcont,
    colActivity_closed ρ μG hN hρcont]

/-- **C₁ as an activity statement**: β2-1b's first
coefficient of `𝒜` is the column count times the
degree-1 single-column activity density. -/
theorem betaCoeff1_activity (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P : LayerColumn N) :
    betaCoeff1 ρ μG u u'
      = colCount N * colDensMoment ρ μG u u' P 1 := by
  rw [betaCoeff1_closed ρ μG hN hρcont,
    colDensMoment_one ρ μG hN hρcont]

/-- The two-column density moment `∫ dens_P · dens_Q`. -/
noncomputable def colDensPairMoment (u u' : LayerLink N → G)
    (P Q : LayerColumn N) : ℝ :=
  ∫ α, colDensC ρ u u' P α * colDensC ρ u u' Q α
    ∂(Measure.pi fun _ : LayerSite N => μG)

theorem colDensPairMoment_self (u u' : LayerLink N → G)
    (P : LayerColumn N) :
    colDensPairMoment ρ μG u u' P P
      = colDensMoment ρ μG u u' P 2 := by
  unfold colDensPairMoment colDensMoment
  refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
  exact (pow_two (colDensC ρ u u' P α)).symm

/-- The cross pair moment at distinct columns (β2-1b's
`integral_colDens_mul_ne`, restated): the `e₁²` form. -/
theorem colDensPairMoment_eq_ne (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {P Q : LayerColumn N} (hPQ : P ≠ Q) :
    colDensPairMoment ρ μG u u' P Q
      = 1 - 2 * e1 ρ μG / (d : ℝ) + (e1 ρ μG) ^ 2 / (d : ℝ) ^ 2 :=
  integral_colDens_mul_ne ρ μG hN hN3 hρcont u u' hPQ

/-- **C₂ as an activity statement**: β2-1b's second
coefficient of `𝒜` is `(M · A₂^self + M(M-1) · A₂^cross)/2`
in terms of the degree-2 activity densities. -/
theorem betaCoeff2_activity (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {P Q : LayerColumn N} (hPQ : P ≠ Q) :
    betaCoeff2 ρ μG u u'
      = (colCount N * colDensMoment ρ μG u u' P 2
        + colCount N * (colCount N - 1)
          * colDensPairMoment ρ μG u u' P Q) / 2 := by
  rw [betaCoeff2_closed ρ μG hN hN3 hρcont,
    colDensMoment_two ρ μG hN hρcont,
    colDensPairMoment_eq_ne ρ μG hN hN3 hρcont u u' hPQ]

/-- **κ₂ as an activity statement** (β2-1b's `kappa2_eq_const`,
restated): the degree-2 self-paired dependent form is the
constant `(1/(4d²)) · Re m₂` — no `(u, u')`-dependence, no
self-duality hypothesis. -/
theorem activity_kappa2 (u u' : G) :
    kappa2 ρ μG u u'
      = (1 / (4 * (d : ℝ) ^ 2)) * (m2 ρ μG).re :=
  kappa2_eq_const ρ μG u u'

/-- Haar power moment under right translation:
`∫ (Re χ(gK))ʲ = μⱼ`. -/
theorem integral_reCharFn_mul_pow (K : G) (j : ℕ) :
    ∫ g, ((charFn ρ (g * K)).re) ^ j ∂μG = realMoment ρ μG j :=
  integral_mul_right_eq_self (fun g => ((charFn ρ g).re) ^ j) K

/-- Haar power moment under inversion and translation:
`∫ (Re χ(g⁻¹K))ʲ = μⱼ`. -/
theorem integral_reCharFn_inv_mul_pow (K : G) (j : ℕ) :
    ∫ g, ((charFn ρ (g⁻¹ * K)).re) ^ j ∂μG = realMoment ρ μG j := by
  have h1 : ∫ g, ((charFn ρ (g⁻¹ * K)).re) ^ j ∂μG
      = ∫ g, ((charFn ρ (g * K)).re) ^ j ∂μG :=
    integral_inv_eq_self (fun g => ((charFn ρ (g * K)).re) ^ j) μG
  rw [h1]
  exact integral_reCharFn_mul_pow ρ μG K j

/-- **The inner integral at the split site, power form.**
Integrating the `j`-th power of a column's real character
over the split coordinate at one of its own sites gives
`μⱼ`, whatever the other coordinates are: at the base site
by right translation; at the far site by cyclicity,
inversion, and right translation. The `j = 1` case is
β2-1b's `integral_split_inner`. -/
theorem integral_split_inner_pow (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P : LayerColumn N) (s : LayerSite N)
    (hsP : s ∈ colSites P)
    (w : ↥({s}ᶜ : Finset (LayerSite N)) → G) (j : ℕ) :
    ∫ v : ↥({s} : Finset (LayerSite N)) → G,
        (colRe ρ u u' P (splitRecomb s (v, w))) ^ j
        ∂(Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG)
      = realMoment ρ μG j := by
  classical
  rw [mem_colSites] at hsP
  set ℓ := layerLinkOf P.1 P.2.1 P.2.2 with hℓ
  set ℓ₀ : ↥({s} : Finset (LayerSite N)) :=
    ⟨s, Finset.mem_singleton_self s⟩ with hℓ₀
  rcases hsP with hs | hs
  · -- s is the base site
    have hfP : layerShift P.2.1 P.2.2 P.1 ≠ s :=
      fun h => layerShift_ne_self hN P.2.1 P.2.2 P.1 (h.trans hs)
    set wval : G := w ⟨layerShift P.2.1 P.2.2 P.1,
      Finset.mem_compl.mpr (fun hmem =>
        hfP (Finset.mem_singleton.mp hmem))⟩ with hwval
    have hw : ∀ v : ↥({s} : Finset (LayerSite N)) → G,
        colWord u u' P.1 P.2.1 P.2.2 (splitRecomb s (v, w))
          = (v ℓ₀) * (u' ℓ) * (wval)⁻¹ * (u ℓ)⁻¹ := by
      intro v
      have h1 : splitRecomb s (v, w) P.1 = v ℓ₀ := by
        have h2 := splitRecomb_fst s (v, w)
          (⟨P.1, Finset.mem_singleton.mpr hs.symm⟩ :
            ↥({s} : Finset (LayerSite N)))
        have h3 : (⟨P.1, Finset.mem_singleton.mpr hs.symm⟩ :
            ↥({s} : Finset (LayerSite N))) = ℓ₀ := Subtype.ext hs.symm
        rw [h3] at h2
        calc splitRecomb s (v, w) P.1 = splitRecomb s (v, w) s :=
              (congrArg (splitRecomb s (v, w)) hs).symm
          _ = v ℓ₀ := h2
      have hfar : splitRecomb s (v, w) (layerShift P.2.1 P.2.2 P.1)
          = wval :=
        splitRecomb_snd s (v, w) ⟨layerShift P.2.1 P.2.2 P.1,
          Finset.mem_compl.mpr (fun hmem =>
            hfP (Finset.mem_singleton.mp hmem))⟩
      show splitRecomb s (v, w) P.1 * (u' ℓ)
          * (splitRecomb s (v, w) (layerShift P.2.1 P.2.2 P.1))⁻¹
          * (u ℓ)⁻¹ = (v ℓ₀) * (u' ℓ) * (wval)⁻¹ * (u ℓ)⁻¹
      rw [h1, hfar]
    have hRe : ∀ v : ↥({s} : Finset (LayerSite N)) → G,
        (colRe ρ u u' P (splitRecomb s (v, w))) ^ j
          = (fun g => ((charFn ρ
              (g * (u' ℓ) * (wval)⁻¹ * (u ℓ)⁻¹)).re) ^ j) (v ℓ₀) :=
      fun v => congrArg (fun g => ((charFn ρ g).re) ^ j) (hw v)
    rw [integral_congr_ae (Filter.Eventually.of_forall hRe),
      integral_eval_coord_real μG (s := ℓ₀)
        (F := fun g => ((charFn ρ
          (g * (u' ℓ) * (wval)⁻¹ * (u ℓ)⁻¹)).re) ^ j)
        (by
          have hword : Continuous fun g : G =>
              g * (u' ℓ) * (wval)⁻¹ * (u ℓ)⁻¹ :=
            ((continuous_id.mul continuous_const).mul
              continuous_const.inv).mul continuous_const
          exact ((Complex.continuous_re.comp
            ((continuous_charFn ρ hρcont).comp hword)).pow j
            ).aestronglyMeasurable)]
    have hK : ∫ g, ((charFn ρ
          (g * (u' ℓ) * (wval)⁻¹ * (u ℓ)⁻¹)).re) ^ j ∂μG
        = ∫ g, ((charFn ρ
            (g * ((u' ℓ) * (wval)⁻¹ * (u ℓ)⁻¹))).re) ^ j ∂μG := by
      apply integral_congr_ae
      filter_upwards with g
      congr 2
      simp only [mul_assoc]
    rw [hK]
    exact integral_reCharFn_mul_pow ρ μG _ j
  · -- s is the far site
    have hbP : P.1 ≠ s :=
      fun h => layerShift_ne_self hN P.2.1 P.2.2 P.1 (h.trans hs).symm
    set wval : G := w ⟨P.1,
      Finset.mem_compl.mpr (fun hmem =>
        hbP (Finset.mem_singleton.mp hmem))⟩ with hwval
    have hw : ∀ v : ↥({s} : Finset (LayerSite N)) → G,
        colWord u u' P.1 P.2.1 P.2.2 (splitRecomb s (v, w))
          = (wval) * (u' ℓ) * (v ℓ₀)⁻¹ * (u ℓ)⁻¹ := by
      intro v
      have h1 : splitRecomb s (v, w) (layerShift P.2.1 P.2.2 P.1)
          = v ℓ₀ := by
        have h2 := splitRecomb_fst s (v, w)
          (⟨layerShift P.2.1 P.2.2 P.1,
            Finset.mem_singleton.mpr hs.symm⟩ :
            ↥({s} : Finset (LayerSite N)))
        have h3 : (⟨layerShift P.2.1 P.2.2 P.1,
            Finset.mem_singleton.mpr hs.symm⟩ :
            ↥({s} : Finset (LayerSite N))) = ℓ₀ := Subtype.ext hs.symm
        rw [h3] at h2
        calc splitRecomb s (v, w) (layerShift P.2.1 P.2.2 P.1)
            = splitRecomb s (v, w) s :=
              (congrArg (splitRecomb s (v, w)) hs).symm
          _ = v ℓ₀ := h2
      have hbase : splitRecomb s (v, w) P.1 = wval :=
        splitRecomb_snd s (v, w) ⟨P.1,
          Finset.mem_compl.mpr (fun hmem =>
            hbP (Finset.mem_singleton.mp hmem))⟩
      show splitRecomb s (v, w) P.1 * (u' ℓ)
          * (splitRecomb s (v, w) (layerShift P.2.1 P.2.2 P.1))⁻¹
          * (u ℓ)⁻¹ = (wval) * (u' ℓ) * (v ℓ₀)⁻¹ * (u ℓ)⁻¹
      rw [hbase, h1]
    have hRe : ∀ v : ↥({s} : Finset (LayerSite N)) → G,
        (colRe ρ u u' P (splitRecomb s (v, w))) ^ j
          = (fun g => ((charFn ρ
              ((wval) * (u' ℓ) * g⁻¹ * (u ℓ)⁻¹)).re) ^ j) (v ℓ₀) :=
      fun v => congrArg (fun g => ((charFn ρ g).re) ^ j) (hw v)
    rw [integral_congr_ae (Filter.Eventually.of_forall hRe),
      integral_eval_coord_real μG (s := ℓ₀)
        (F := fun g => ((charFn ρ
          ((wval) * (u' ℓ) * g⁻¹ * (u ℓ)⁻¹)).re) ^ j)
        (by
          have hword : Continuous fun g : G =>
              (wval) * (u' ℓ) * g⁻¹ * (u ℓ)⁻¹ :=
            ((continuous_const.mul continuous_const).mul
              continuous_id.inv).mul continuous_const
          exact ((Complex.continuous_re.comp
            ((continuous_charFn ρ hρcont).comp hword)).pow j
            ).aestronglyMeasurable)]
    have e1' : ∀ g : G,
        ((charFn ρ ((wval) * (u' ℓ) * g⁻¹ * (u ℓ)⁻¹)).re) ^ j
          = ((charFn ρ (g⁻¹ * ((u ℓ)⁻¹ * (wval) * (u' ℓ)))).re) ^ j := by
      intro g
      have h1 : (wval) * (u' ℓ) * g⁻¹ * (u ℓ)⁻¹
          = ((wval) * (u' ℓ)) * (g⁻¹ * (u ℓ)⁻¹) := by
        simp only [mul_assoc]
      have h2 : (g⁻¹ * (u ℓ)⁻¹) * ((wval) * (u' ℓ))
          = g⁻¹ * ((u ℓ)⁻¹ * (wval) * (u' ℓ)) := by
        simp only [mul_assoc]
      have hw2 : charFn ρ ((wval) * (u' ℓ) * g⁻¹ * (u ℓ)⁻¹)
          = charFn ρ (g⁻¹ * ((u ℓ)⁻¹ * (wval) * (u' ℓ))) := by
        rw [h1, charFn_mul_comm, h2]
      rw [hw2]
    rw [integral_congr_ae (Filter.Eventually.of_forall e1')]
    exact integral_reCharFn_inv_mul_pow ρ μG _ j

/-- Products of column character powers are integrable
(bounded by `dʲ⁺ᵏ` entrywise). -/
theorem integrable_colRe_pow_mul
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P Q : LayerColumn N) (j k : ℕ) :
    Integrable (fun α => (colRe ρ u u' P α) ^ j
        * (colRe ρ u u' Q α) ^ k)
      (Measure.pi fun _ : LayerSite N => μG) :=
  Integrable.of_bound
    (((measurable_colRe ρ hρcont u u' P).pow_const j).mul
      ((measurable_colRe ρ hρcont u u' Q).pow_const k)
      ).aestronglyMeasurable
    ((d : ℝ) ^ j * (d : ℝ) ^ k)
    (Filter.Eventually.of_forall fun α => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_pow]
      exact mul_le_mul
        (pow_le_pow_left₀ (abs_nonneg _) (abs_re_charFn_le ρ _) j)
        (pow_le_pow_left₀ (abs_nonneg _) (abs_re_charFn_le ρ _) k)
        (pow_nonneg (abs_nonneg _) k)
        (pow_nonneg (Nat.cast_nonneg d) j))

/-- **The directed mixed moment.** If `s` is a site of `P`
but not of `Q`, the mixed moment factors completely:
`∫ r_Pʲ r_Qᵏ = μⱼ μₖ`. The private coordinate `α s` is a
Haar translate inside `P`'s word and absent from `Q`'s. -/
theorem integral_colRe_pow_mul_of_site (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P Q : LayerColumn N) (s : LayerSite N)
    (hsP : s ∈ colSites P) (hsQ : s ∉ colSites Q) (j k : ℕ) :
    ∫ α : LayerSite N → G, (colRe ρ u u' P α) ^ j
          * (colRe ρ u u' Q α) ^ k
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = realMoment ρ μG j * realMoment ρ μG k := by
  classical
  have hbQ : Q.1 ≠ s := by
    intro h
    apply hsQ
    have hmem : Q.1 ∈ colSites Q := mem_colSites.mpr (Or.inl rfl)
    rw [h] at hmem
    exact hmem
  have hfQ : layerShift Q.2.1 Q.2.2 Q.1 ≠ s := by
    intro h
    apply hsQ
    have hmem : layerShift Q.2.1 Q.2.2 Q.1 ∈ colSites Q :=
      mem_colSites.mpr (Or.inr rfl)
    rw [h] at hmem
    exact hmem
  have hInt : Integrable
      (fun z : (↥({s} : Finset (LayerSite N)) → G)
          × (↥({s}ᶜ : Finset (LayerSite N)) → G) =>
        (colRe ρ u u' P (splitRecomb s z)) ^ j
          * (colRe ρ u u' Q (splitRecomb s z)) ^ k)
      ((Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG).prod
        (Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG)) := by
    refine Integrable.of_bound ?_ ((d : ℝ) ^ j * (d : ℝ) ^ k)
      (Filter.Eventually.of_forall fun z => ?_)
    · have hmP : Measurable
          (fun z : (↥({s} : Finset (LayerSite N)) → G)
            × (↥({s}ᶜ : Finset (LayerSite N)) → G) =>
            colRe ρ u u' P (splitRecomb s z)) :=
          (measurable_colRe ρ hρcont u u' P).comp
            (splitEquiv ({s} : Finset (LayerSite N))).symm.measurable
      have hmQ : Measurable
          (fun z : (↥({s} : Finset (LayerSite N)) → G)
            × (↥({s}ᶜ : Finset (LayerSite N)) → G) =>
            colRe ρ u u' Q (splitRecomb s z)) :=
          (measurable_colRe ρ hρcont u u' Q).comp
            (splitEquiv ({s} : Finset (LayerSite N))).symm.measurable
      exact ((hmP.pow_const j).mul (hmQ.pow_const k)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_pow]
      exact mul_le_mul
        (pow_le_pow_left₀ (abs_nonneg _) (abs_re_charFn_le ρ _) j)
        (pow_le_pow_left₀ (abs_nonneg _) (abs_re_charFn_le ρ _) k)
        (pow_nonneg (abs_nonneg _) k)
        (pow_nonneg (Nat.cast_nonneg d) j)
  have htrans : ∫ α : LayerSite N → G,
        (colRe ρ u u' P α) ^ j * (colRe ρ u u' Q α) ^ k
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ z : (↥({s} : Finset (LayerSite N)) → G)
          × (↥({s}ᶜ : Finset (LayerSite N)) → G),
          (colRe ρ u u' P (splitRecomb s z)) ^ j
            * (colRe ρ u u' Q (splitRecomb s z)) ^ k
          ∂((Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG).prod
            (Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG)) := by
    have h := (measurePreserving_splitEquiv μG
      ({s} : Finset (LayerSite N))).integral_comp
      (splitEquiv ({s} : Finset (LayerSite N))).measurableEmbedding
      (fun z => (colRe ρ u u' P (splitRecomb s z)) ^ j
        * (colRe ρ u u' Q (splitRecomb s z)) ^ k)
    have hL : ∫ U : LayerSite N → G,
          (fun z => (colRe ρ u u' P (splitRecomb s z)) ^ j
            * (colRe ρ u u' Q (splitRecomb s z)) ^ k)
            (splitEquiv ({s} : Finset (LayerSite N)) U)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = ∫ U : LayerSite N → G, (colRe ρ u u' P U) ^ j
            * (colRe ρ u u' Q U) ^ k
            ∂(Measure.pi fun _ : LayerSite N => μG) := by
      apply integral_congr_ae
      filter_upwards with U
      show (colRe ρ u u' P (splitRecomb s
            (splitEquiv ({s} : Finset (LayerSite N)) U))) ^ j
          * (colRe ρ u u' Q (splitRecomb s
            (splitEquiv ({s} : Finset (LayerSite N)) U))) ^ k
        = (colRe ρ u u' P U) ^ j * (colRe ρ u u' Q U) ^ k
      rw [splitRecomb_apply_split]
    rw [hL] at h
    exact h
  calc ∫ α : LayerSite N → G, (colRe ρ u u' P α) ^ j
          * (colRe ρ u u' Q α) ^ k
          ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ z : (↥({s} : Finset (LayerSite N)) → G)
            × (↥({s}ᶜ : Finset (LayerSite N)) → G),
            (colRe ρ u u' P (splitRecomb s z)) ^ j
              * (colRe ρ u u' Q (splitRecomb s z)) ^ k
            ∂((Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG).prod
              (Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG)) :=
        htrans
    _ = ∫ w : ↥({s}ᶜ : Finset (LayerSite N)) → G,
            ∫ v : ↥({s} : Finset (LayerSite N)) → G,
              (colRe ρ u u' P (splitRecomb s (v, w))) ^ j
                * (colRe ρ u u' Q (splitRecomb s (v, w))) ^ k
              ∂(Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG)
            ∂(Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG) :=
        integral_prod_symm _ hInt
    _ = ∫ w : ↥({s}ᶜ : Finset (LayerSite N)) → G,
            (realMoment ρ μG j)
              * (colRe ρ u u' Q (splitRecomb s (fun _ => 1, w))) ^ k
            ∂(Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG) := by
        apply integral_congr_ae
        filter_upwards with w
        have hQc : ∀ v : ↥({s} : Finset (LayerSite N)) → G,
            colRe ρ u u' Q (splitRecomb s (v, w))
              = colRe ρ u u' Q (splitRecomb s (fun _ => 1, w)) := by
          intro v
          have h1 : splitRecomb s (v, w) Q.1
              = splitRecomb s (fun _ => 1, w) Q.1 :=
            (splitRecomb_snd s (v, w) ⟨Q.1,
              Finset.mem_compl.mpr (fun hmem =>
                hbQ (Finset.mem_singleton.mp hmem))⟩).trans
              (splitRecomb_snd s (fun _ => 1, w) ⟨Q.1,
                Finset.mem_compl.mpr (fun hmem =>
                  hbQ (Finset.mem_singleton.mp hmem))⟩).symm
          have h2 : splitRecomb s (v, w) (layerShift Q.2.1 Q.2.2 Q.1)
              = splitRecomb s (fun _ => 1, w)
                  (layerShift Q.2.1 Q.2.2 Q.1) :=
            (splitRecomb_snd s (v, w) ⟨layerShift Q.2.1 Q.2.2 Q.1,
              Finset.mem_compl.mpr (fun hmem =>
                hfQ (Finset.mem_singleton.mp hmem))⟩).trans
              (splitRecomb_snd s (fun _ => 1, w)
                ⟨layerShift Q.2.1 Q.2.2 Q.1,
                  Finset.mem_compl.mpr (fun hmem =>
                    hfQ (Finset.mem_singleton.mp hmem))⟩).symm
          exact congrArg (fun g => (charFn ρ g).re)
            (colWord_eq_of_agree u u' Q.1 Q.2.1 Q.2.2 h1 h2)
        calc ∫ v : ↥({s} : Finset (LayerSite N)) → G,
                (colRe ρ u u' P (splitRecomb s (v, w))) ^ j
                  * (colRe ρ u u' Q (splitRecomb s (v, w))) ^ k
                ∂(Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG)
            = ∫ v : ↥({s} : Finset (LayerSite N)) → G,
                  (colRe ρ u u' P (splitRecomb s (v, w))) ^ j
                    * (colRe ρ u u' Q (splitRecomb s (fun _ => 1, w))) ^ k
                  ∂(Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG) :=
              integral_congr_ae (Filter.Eventually.of_forall fun v => by
                show (colRe ρ u u' P (splitRecomb s (v, w))) ^ j
                    * (colRe ρ u u' Q (splitRecomb s (v, w))) ^ k
                  = (colRe ρ u u' P (splitRecomb s (v, w))) ^ j
                    * (colRe ρ u u' Q (splitRecomb s (fun _ => 1, w))) ^ k
                rw [hQc v])
          _ = (∫ v : ↥({s} : Finset (LayerSite N)) → G,
                    (colRe ρ u u' P (splitRecomb s (v, w))) ^ j
                    ∂(Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG))
                  * (colRe ρ u u' Q (splitRecomb s (fun _ => 1, w))) ^ k :=
              integral_mul_const _ _
          _ = (realMoment ρ μG j)
                  * (colRe ρ u u' Q (splitRecomb s (fun _ => 1, w))) ^ k := by
              rw [integral_split_inner_pow ρ μG hN hρcont u u' P s hsP w j]
    _ = realMoment ρ μG j * realMoment ρ μG k := by
        rw [integral_const_mul]
        congr 1
        have hrestr : ∫ w : ↥({s}ᶜ : Finset (LayerSite N)) → G,
              (colRe ρ u u' Q (splitRecomb s (fun _ => 1, w))) ^ k
              ∂(Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG)
            = ∫ α : LayerSite N → G, (colRe ρ u u' Q α) ^ k
                ∂(Measure.pi fun _ : LayerSite N => μG) := by
          rw [← integral_pi_restrict_real μG ({s}ᶜ : Finset (LayerSite N))
            (fun w => (colRe ρ u u' Q (splitRecomb s (fun _ => 1, w))) ^ k)]
          apply integral_congr_ae
          filter_upwards with U
          have h1 : splitRecomb s
                (fun _ => 1, fun ℓ : ↥({s}ᶜ : Finset (LayerSite N)) =>
                  U ℓ.1) Q.1 = U Q.1 :=
            splitRecomb_snd s _ ⟨Q.1,
              Finset.mem_compl.mpr (fun hmem =>
                hbQ (Finset.mem_singleton.mp hmem))⟩
          have h2 : splitRecomb s
                (fun _ => 1, fun ℓ : ↥({s}ᶜ : Finset (LayerSite N)) =>
                  U ℓ.1) (layerShift Q.2.1 Q.2.2 Q.1)
              = U (layerShift Q.2.1 Q.2.2 Q.1) :=
            splitRecomb_snd s _ ⟨layerShift Q.2.1 Q.2.2 Q.1,
              Finset.mem_compl.mpr (fun hmem =>
                hfQ (Finset.mem_singleton.mp hmem))⟩
          have h3 : colRe ρ u u' Q (splitRecomb s
                (fun _ => 1, fun ℓ : ↥({s}ᶜ : Finset (LayerSite N)) =>
                  U ℓ.1)) = colRe ρ u u' Q U :=
            congrArg (fun g => (charFn ρ g).re)
              (colWord_eq_of_agree u u' Q.1 Q.2.1 Q.2.2 h1 h2)
          exact congrArg (· ^ k) h3
        rw [hrestr]
        exact colMoment_eq ρ μG hN hρcont u u' Q k

/-- **Distinct columns are fully independent as random
variables** under the stratum measure: every mixed
character moment factors. The `(j, k) = (1, 1)` case is
β2-1b's P₀-collapse (`integral_cross`); this is its
extension to all degrees, by the same private-site
mechanism. In particular no adjacency restriction is
needed: site-sharing columns factor too, because for
`3 ≤ N` distinct columns always have a private site
(`exists_site_of_ne`). -/
theorem integral_colRe_pow_mul (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {P Q : LayerColumn N} (hPQ : P ≠ Q)
    (j k : ℕ) :
    ∫ α : LayerSite N → G, (colRe ρ u u' P α) ^ j
          * (colRe ρ u u' Q α) ^ k
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = realMoment ρ μG j * realMoment ρ μG k := by
  obtain ⟨s, hs | hs⟩ := exists_site_of_ne hN hN3 hPQ
  · exact integral_colRe_pow_mul_of_site ρ μG hN hN3 hρcont u u'
      P Q s hs.1 hs.2 j k
  · have h := integral_colRe_pow_mul_of_site ρ μG hN hN3 hρcont u u'
      Q P s hs.1 hs.2 k j
    rw [integral_congr_ae (Filter.Eventually.of_forall fun α =>
      mul_comm ((colRe ρ u u' P α) ^ j) ((colRe ρ u u' Q α) ^ k))]
    exact h.trans (mul_comm _ _)

/-- **Distinct columns are independent at the density
level too**: `∫ dens_Pʲ dens_Qᵏ = (∫ dens_Pʲ)(∫ dens_Qᵏ)`,
by binomial expansion into character moments and
`integral_colRe_pow_mul`. -/
theorem integral_colDens_pow_mul (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {P Q : LayerColumn N} (hPQ : P ≠ Q)
    (j k : ℕ) :
    ∫ α : LayerSite N → G, (colDensC ρ u u' P α) ^ j
          * (colDensC ρ u u' Q α) ^ k
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = colDensMoment ρ μG u u' P j * colDensMoment ρ μG u u' Q k := by
  classical
  have hInt : ∀ a ∈ Finset.range (j + 1), ∀ b ∈ Finset.range (k + 1),
      Integrable (fun α => ((j.choose a : ℝ) * (k.choose b : ℝ))
          * (((-(d : ℝ)⁻¹) * colRe ρ u u' P α) ^ a
            * ((-(d : ℝ)⁻¹) * colRe ρ u u' Q α) ^ b))
        (Measure.pi fun _ : LayerSite N => μG) := by
    intro a _ b _
    have hfun : (fun α : LayerSite N → G =>
          ((j.choose a : ℝ) * (k.choose b : ℝ))
            * (((-(d : ℝ)⁻¹) * colRe ρ u u' P α) ^ a
              * ((-(d : ℝ)⁻¹) * colRe ρ u u' Q α) ^ b))
        = (fun α : LayerSite N → G =>
          (((j.choose a : ℝ) * (k.choose b : ℝ))
            * ((-(d : ℝ)⁻¹) ^ a * (-(d : ℝ)⁻¹) ^ b))
            * ((colRe ρ u u' P α) ^ a * (colRe ρ u u' Q α) ^ b)) := by
      funext α
      rw [mul_pow, mul_pow]
      ring
    rw [hfun]
    exact (integrable_colRe_pow_mul ρ μG hρcont u u' P Q a b).const_mul _
  have hpt : ∀ α : LayerSite N → G,
      (colDensC ρ u u' P α) ^ j * (colDensC ρ u u' Q α) ^ k
        = ∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (k + 1),
            ((j.choose a : ℝ) * (k.choose b : ℝ))
              * (((-(d : ℝ)⁻¹) * colRe ρ u u' P α) ^ a
                * ((-(d : ℝ)⁻¹) * colRe ρ u u' Q α) ^ b) := by
    intro α
    rw [colDensC_pow_expand ρ u u' P α j,
      colDensC_pow_expand ρ u u' Q α k, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    ring
  have hterm : ∀ a ∈ Finset.range (j + 1), ∀ b ∈ Finset.range (k + 1),
      ∫ α : LayerSite N → G, ((j.choose a : ℝ) * (k.choose b : ℝ))
            * (((-(d : ℝ)⁻¹) * colRe ρ u u' P α) ^ a
              * ((-(d : ℝ)⁻¹) * colRe ρ u u' Q α) ^ b)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = (j.choose a : ℝ) * (k.choose b : ℝ)
            * ((-(d : ℝ)⁻¹) ^ a * (-(d : ℝ)⁻¹) ^ b)
            * (realMoment ρ μG a * realMoment ρ μG b) := by
    intro a _ b _
    have hpt2 : ∀ α : LayerSite N → G,
        ((j.choose a : ℝ) * (k.choose b : ℝ))
            * (((-(d : ℝ)⁻¹) * colRe ρ u u' P α) ^ a
              * ((-(d : ℝ)⁻¹) * colRe ρ u u' Q α) ^ b)
          = ((j.choose a : ℝ) * (k.choose b : ℝ)
              * ((-(d : ℝ)⁻¹) ^ a * (-(d : ℝ)⁻¹) ^ b))
              * ((colRe ρ u u' P α) ^ a * (colRe ρ u u' Q α) ^ b) := by
      intro α
      rw [mul_pow, mul_pow]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt2),
      integral_const_mul,
      integral_colRe_pow_mul ρ μG hN hN3 hρcont u u' hPQ a b]
  calc ∫ α : LayerSite N → G, (colDensC ρ u u' P α) ^ j
          * (colDensC ρ u u' Q α) ^ k
          ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (k + 1),
            (j.choose a : ℝ) * (k.choose b : ℝ)
              * ((-(d : ℝ)⁻¹) ^ a * (-(d : ℝ)⁻¹) ^ b)
              * (realMoment ρ μG a * realMoment ρ μG b) := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
          integral_finsetSum _
            (fun a ha => integrable_finsetSum _
              (fun b hb => hInt a ha b hb))]
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [integral_finsetSum _ (fun b hb => hInt a ha b hb)]
        exact Finset.sum_congr rfl fun b hb => hterm a ha b hb
    _ = (∑ a ∈ Finset.range (j + 1), ((j.choose a : ℝ))
            * (-(d : ℝ)⁻¹) ^ a * realMoment ρ μG a)
          * (∑ b ∈ Finset.range (k + 1), ((k.choose b : ℝ))
            * (-(d : ℝ)⁻¹) ^ b * realMoment ρ μG b) := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring
    _ = colDensMoment ρ μG u u' P j * colDensMoment ρ μG u u' Q k := by
        rw [colDensMoment_closed ρ μG hN hρcont,
          colDensMoment_closed ρ μG hN hρcont]

/-- **The connected (truncated) two-column activity** at
degrees `(j, k)`, with its Taylor weight: the pair moment
minus the product of the one-column moments. -/
noncomputable def connectedActivity (β : ℝ) (j k : ℕ)
    (u u' : LayerLink N → G) (P Q : LayerColumn N) : ℝ :=
  (-β) ^ (j + k) / ((Nat.factorial j : ℝ) * (Nat.factorial k : ℝ))
    * (∫ α, (colDensC ρ u u' P α) ^ j * (colDensC ρ u u' Q α) ^ k
        ∂(Measure.pi fun _ : LayerSite N => μG)
      - colDensMoment ρ μG u u' P j * colDensMoment ρ μG u u' Q k)

/-- **Every two-column connected activity vanishes
identically**, at every degree pair, for every pair of
distinct columns — adjacent or not. This corrects the
LOC-0 scoping memo, which expected the first nonzero
connected activities at degrees `(2,1)` and `(2,2)`: on
the corpus's landed mathematics the private-site
factorization (`integral_colRe_pow_mul`) is exact at all
degrees, so the pair activity is *precisely* the product
of the single-column activities (see `pairActivity21`,
`pairActivity22` for the explicit values). -/
theorem connectedActivity_eq_zero (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (j k : ℕ) (u u' : LayerLink N → G)
    {P Q : LayerColumn N} (hPQ : P ≠ Q) :
    connectedActivity ρ μG β j k u u' P Q = 0 := by
  unfold connectedActivity
  rw [integral_colDens_pow_mul ρ μG hN hN3 hρcont u u' hPQ j k,
    sub_self, mul_zero]

/-- **The (1,1) connected activity is zero** — the named
form of the P₀-collapse for activities. -/
theorem connectedActivity11_eq_zero (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G)
    {P Q : LayerColumn N} (hPQ : P ≠ Q) :
    connectedActivity ρ μG β 1 1 u u' P Q = 0 :=
  connectedActivity_eq_zero ρ μG hN hN3 hρcont β 1 1 u u' hPQ

/-- The (2,1) connected activity is zero. -/
theorem connectedActivity21_eq_zero (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G)
    {P Q : LayerColumn N} (hPQ : P ≠ Q) :
    connectedActivity ρ μG β 2 1 u u' P Q = 0 :=
  connectedActivity_eq_zero ρ μG hN hN3 hρcont β 2 1 u u' hPQ

/-- The (2,2) connected activity is zero. -/
theorem connectedActivity22_eq_zero (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G)
    {P Q : LayerColumn N} (hPQ : P ≠ Q) :
    connectedActivity ρ μG β 2 2 u u' P Q = 0 :=
  connectedActivity_eq_zero ρ μG hN hN3 hρcont β 2 2 u u' hPQ

/-- **The (2,1) pair activity, explicitly**: the product
of the degree-2 self form and the degree-1 form. This —
not a nonzero connected part — is the two-column content
at degrees `(2,1)`. -/
theorem pairActivity21 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {P Q : LayerColumn N} (hPQ : P ≠ Q) :
    ∫ α : LayerSite N → G, (colDensC ρ u u' P α) ^ 2
          * (colDensC ρ u u' Q α) ^ 1
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (1 - 2 * e1 ρ μG / (d : ℝ) + q2 ρ μG / (d : ℝ) ^ 2)
        * (1 - e1 ρ μG / (d : ℝ)) := by
  rw [integral_colDens_pow_mul ρ μG hN hN3 hρcont u u' hPQ 2 1,
    colDensMoment_two ρ μG hN hρcont,
    colDensMoment_one ρ μG hN hρcont]

/-- **The (2,2) pair activity, explicitly**: the square of
the degree-2 self form. -/
theorem pairActivity22 (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {P Q : LayerColumn N} (hPQ : P ≠ Q) :
    ∫ α : LayerSite N → G, (colDensC ρ u u' P α) ^ 2
          * (colDensC ρ u u' Q α) ^ 2
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (1 - 2 * e1 ρ μG / (d : ℝ) + q2 ρ μG / (d : ℝ) ^ 2) ^ 2 := by
  rw [integral_colDens_pow_mul ρ μG hN hN3 hρcont u u' hPQ 2 2,
    colDensMoment_two ρ μG hN hρcont,
    colDensMoment_two ρ μG hN hρcont]
  exact (pow_two _).symm

/-- One term of the closed form, in absolute value, is
exactly the binomial coefficient times the contraction
number. -/
theorem abs_moment_term (k a : ℕ) :
    |((k.choose a : ℝ)) * (-(d : ℝ)⁻¹) ^ a * realMoment ρ μG a|
      = (k.choose a : ℝ) * contractionNumber ρ μG a := by
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_inv,
    abs_of_nonneg (a := (d : ℝ)) (Nat.cast_nonneg d),
    abs_of_nonneg (a := ((k.choose a : ℝ))) (Nat.cast_nonneg _),
    contractionNumber, inv_pow, div_eq_inv_mul]
  ring

/-- **The scalar majorant, contraction form.** The only
group data the bound sees is `d` — through contraction
numbers `|μₐ|/dᵃ`, each `≤ 1` — and the label's binomial
weights. -/
theorem abs_colActivity_le_contraction (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (k : ℕ) (u u' : LayerLink N → G) (P : LayerColumn N) :
    |colActivity ρ μG β k u u' P|
      ≤ |β| ^ k / (Nat.factorial k : ℝ)
        * ∑ a ∈ Finset.range (k + 1), ((k.choose a : ℝ))
            * contractionNumber ρ μG a := by
  rw [colActivity_closed ρ μG hN hρcont]
  calc |(-β) ^ k / (Nat.factorial k : ℝ)
          * ∑ a ∈ Finset.range (k + 1), ((k.choose a : ℝ))
              * (-(d : ℝ)⁻¹) ^ a * realMoment ρ μG a|
      = |β| ^ k / (Nat.factorial k : ℝ)
          * |∑ a ∈ Finset.range (k + 1), ((k.choose a : ℝ))
              * (-(d : ℝ)⁻¹) ^ a * realMoment ρ μG a| := by
        rw [abs_mul, abs_div, abs_pow, abs_neg,
          abs_of_nonneg (a := ((Nat.factorial k : ℝ)))
            (Nat.cast_nonneg _)]
    _ ≤ |β| ^ k / (Nat.factorial k : ℝ)
          * ∑ a ∈ Finset.range (k + 1),
              |((k.choose a : ℝ)) * (-(d : ℝ)⁻¹) ^ a
                * realMoment ρ μG a| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
          (div_nonneg (pow_nonneg (abs_nonneg _) _)
            (Nat.cast_nonneg _))
    _ = |β| ^ k / (Nat.factorial k : ℝ)
          * ∑ a ∈ Finset.range (k + 1), ((k.choose a : ℝ))
              * contractionNumber ρ μG a :=
        congrArg _ (Finset.sum_congr rfl fun a _ =>
          abs_moment_term ρ μG k a)

/-- **The scalar majorant** (spec item 4): for every label
of degree `k`,
`|ζ(label)| ≤ (2β)ᵏ/k!` for `β ≥ 0` (stated with `|β|`,
all real `β`), the contraction number being `≤ 1` and the
binomial weights summing to `2ᵏ`. In the corpus's density
normalization this — not the scoping memo's `(2β/d)ᵏ` —
is the sharp form: at `d = 2` with `ρ = sign ⊕ sign` one
has `∫ densᵏ = 2ᵏ⁻¹`, which violates `(2/d)ᵏ = 1` for
`k ≥ 2`; the memo's constant belongs to a per-leg
character normalization the landed expansion does not
use. -/
theorem abs_colActivity_le (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (k : ℕ) (u u' : LayerLink N → G) (P : LayerColumn N) :
    |colActivity ρ μG β k u u' P|
      ≤ (2 * |β|) ^ k / (Nat.factorial k : ℝ) := by
  calc |colActivity ρ μG β k u u' P|
      ≤ |β| ^ k / (Nat.factorial k : ℝ)
          * ∑ a ∈ Finset.range (k + 1), ((k.choose a : ℝ))
              * contractionNumber ρ μG a :=
        abs_colActivity_le_contraction ρ μG hN hρcont β k u u' P
    _ ≤ |β| ^ k / (Nat.factorial k : ℝ)
          * ∑ a ∈ Finset.range (k + 1), ((k.choose a : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun a _ =>
            mul_le_mul_of_nonneg_left
              (contractionNumber_le_one ρ μG hρcont a)
              (Nat.cast_nonneg _))
          (div_nonneg (pow_nonneg (abs_nonneg _) _)
            (Nat.cast_nonneg _))
    _ = (2 * |β|) ^ k / (Nat.factorial k : ℝ) := by
        have hsum : ∑ a ∈ Finset.range (k + 1),
              ((k.choose a : ℝ)) * 1 = (2 : ℝ) ^ k := by
          simp only [mul_one]
          exact_mod_cast Nat.sum_range_choose k
        rw [hsum, mul_pow]
        ring

/-- The single-column activities are summable in the
degree, with the exponential majorant. -/
theorem summable_abs_colActivity (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) (P : LayerColumn N) :
    Summable fun k => |colActivity ρ μG β (k + 1) u u' P| :=
  Summable.of_norm_bounded
    ((summable_nat_add_iff 1).mpr
      (Real.summable_pow_div_factorial (2 * |β|)))
    (fun k => by
      rw [Real.norm_eq_abs, abs_abs]
      exact abs_colActivity_le ρ μG hN hρcont β (k + 1) u u' P)

/-- **Total single-column activity**: summed over all
non-vacuum degrees, `∑_{k ≥ 1} |ζₖ| ≤ exp(2β) - 1` for
`β ≥ 0` — the normalization sector's total weight. -/
theorem total_colActivity_le (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hβ : 0 ≤ β) (u u' : LayerLink N → G) (P : LayerColumn N) :
    ∑' k, |colActivity ρ μG β (k + 1) u u' P|
      ≤ Real.exp (2 * β) - 1 := by
  have hb : Summable fun k =>
      (2 * β) ^ (k + 1) / ((Nat.factorial (k + 1) : ℝ)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial _)
  calc ∑' k, |colActivity ρ μG β (k + 1) u u' P|
      ≤ ∑' k, (2 * β) ^ (k + 1) / ((Nat.factorial (k + 1) : ℝ)) :=
        (summable_abs_colActivity ρ μG hN hρcont β u u' P).tsum_le_tsum
          (fun k => by
            have h := abs_colActivity_le ρ μG hN hρcont β (k + 1) u u' P
            rwa [abs_of_nonneg hβ] at h) hb
    _ = Real.exp (2 * β) - 1 := by
        have hsplit :=
          (Real.summable_pow_div_factorial (2 * β)).sum_add_tsum_nat_add 1
        have h0 : ∑ i ∈ Finset.range 1,
              (2 * β) ^ i / ((Nat.factorial i : ℝ)) = 1 := by
          simp
        have hexp : (∑' i, (2 * β) ^ i / ((Nat.factorial i : ℝ)))
            = Real.exp (2 * β) := by
          have h1 : Real.exp (2 * β)
              = NormedSpace.exp (2 * β) :=
            congrFun Real.exp_eq_exp_ℝ _
          rw [h1, congrFun (NormedSpace.exp_eq_tsum ℝ) (2 * β)]
          apply tsum_congr
          intro n
          rw [smul_eq_mul, div_eq_inv_mul, mul_comm]
        rw [h0, hexp] at hsplit
        linarith

/-- **The dependent sector starts at degree 3** — the
β-coefficient form (β2-1b's headline, restated as an
activity statement): the `(u, u')`-dependent part of
`𝒜` vanishes through degree 2, and the single-column
activities themselves are `(u, u')`-free at *every*
degree (`colActivity_independent`). What remains is the
tail, majorized by `dependent_sector_majorant`. -/
theorem activity_dep_part_degree_le_two_zero (hN : Even N)
    (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' v v' : LayerLink N → G) :
    betaCoeff1 ρ μG u u' = betaCoeff1 ρ μG v v'
      ∧ betaCoeff2 ρ μG u u' = betaCoeff2 ρ μG v v' :=
  layerKernel_dep_beta2_zero ρ μG hN hN3 hρcont u u' v v'

/-- **The dependent-sector majorant** (β2-1b's tail bound,
restated): everything in `𝒜` beyond degree 2 — which by
the previous theorem is exactly the `(u, u')`-dependent
sector — is `O(β³)` with the explicit constant
`(2M|β|)³/6 · exp(2M|β|)`, `M = colCount N`. -/
theorem dependent_sector_majorant (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) :
    ‖∑' (k : ℕ), ∫ α, (-β * layerDensSum ρ α u u') ^ (k + 3)
          / ((Nat.factorial (k + 3) : ℝ))
          ∂(Measure.pi fun _ : LayerSite N => μG)‖
      ≤ (2 * colCount N * |β|) ^ 3 / 6
        * Real.exp (2 * colCount N * |β|) :=
  layerKernel_tail_bound ρ μG hN hρcont β u u'

end Activity

end ThetLogos
