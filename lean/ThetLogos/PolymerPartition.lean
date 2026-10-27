import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import ThetLogos.PolymerConvergence

/-!
# LOC-3 — the polymer partition function, the bridge, and the KS implication

The LOC-2 seam, priced there and closed here as far as the owned
vocabulary honestly reaches. Three parts:

(i) **The object.** `colZ` is the single-column activity sum
`∑' k, colActivity β k` — a column's own partition sum, equal to
`1 +` its non-vacuum activity sum since the `k = 0` activity is `1`.
`zPolymer` is the product over all columns of the layer,
`∏ P, colZ P`: the **factorized (decoupled) polymer partition
function over a layer**, in the owned vocabulary.

(ii) **The bridge.** For `zPolymer` the bridge is a theorem, in two
forms: the log form, `log zPolymer = ∑ P, log (colZ P)`
(= `colCount N * log (colZ P)` for any column `P`, by the landed
column-independence of the activities), and the expansion form,
`zPolymer = ∑_{S ⊆ columns} ∑' j, supportActivity S j`, tying the
object to LOC-2's support activities, the quantities `clusterSum`
sums. The column bridge underneath both: `colZ` is the column's
Boltzmann average, `∫ exp (-β * dens_P)`.

**KL3-1, on the face.** The bridge is NOT proved for the layer
kernel `𝒜` (`layerKernel` of `PlaneCrossingCube`), and no sentence
in this module asserts it. `𝒜` is the integral of
`exp (-layerAction)` over the *shared* stratum variable `α`; the
columns are correlated through `α`, and no owned theorem
factorizes that integral, or `log 𝒜`, over columns — only the
integrated single-column moments factor (LOC-1). The missing
definition, named exactly: a column-factorization of the stratum
integral (a product form of `𝒜` over columns, or an independence
hypothesis on the stratum measure with respect to the column
filtration). Until such an object exists in the corpus, the bridge
to `𝒜` is the honest open seam of this line, and `zPolymer` — not
`𝒜` — is the layer weight whose logarithm this module identifies
with the polymer sum.

(iii) **The KS implication.** Inside the landed radius
`|β| < beta0`, `ks_criterion_full` gives `clusterSum ≤ 1` at every
column, and the per-volume free-energy density of `zPolymer`,
`(log zPolymer) / colCount N`, equals the single N-independent
number `log (colZ P)`, whose defining series (the logarithm series
of the activity sum) converges absolutely with a majorant
depending only on `|β|` — uniform in `N`, in the volume, and in
the boundary links. Every sum in sight is a finite-volume sum;
no infinite-volume or continuum object is defined or claimed
(KL3-2 respected).

NO CLAIM. No continuum, thermodynamic-limit, or Clay statement
is made anywhere in this file.
-/

namespace ThetLogos

open Finset MeasureTheory

noncomputable section

section PolymerPartition

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- The single-column activity sum: the column's own partition
sum `∑' k, colActivity β k`, vacuum degree included. -/
noncomputable def colZ (β : ℝ) (u u' : LayerLink N → G)
    (P : LayerColumn N) : ℝ :=
  ∑' k, colActivity ρ μG β k u u' P

/-- **The factorized polymer partition function over a layer**:
the product over all columns of the column activity sums,
`∏ P, colZ P = ∏ P, (1 + non-vacuum activity sum at P)`. The
decoupled layer weight of the LOC line — see the header for
exactly how it differs from the layer kernel `𝒜`. -/
noncomputable def zPolymer (β : ℝ) (u u' : LayerLink N → G) : ℝ :=
  ∏ P : LayerColumn N, colZ ρ μG β u u' P

/-- The vacuum activity is `1`: the `k = 0` term of a column's
activity series is the integral of `1` over a probability
stratum. -/
theorem colActivity_zero (β : ℝ) (u u' : LayerLink N → G)
    (P : LayerColumn N) :
    colActivity ρ μG β 0 u u' P = 1 := by
  simp [colActivity]

/-- The full activity series of a column is summable (the landed
shifted absolute summability of LOC-1, unshifted). -/
theorem summable_colActivity (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) (P : LayerColumn N) :
    Summable fun k => colActivity ρ μG β k u u' P :=
  (summable_nat_add_iff 1).mp
    ((summable_abs_colActivity ρ μG hN hρcont β u u' P).of_abs)

theorem summable_abs_colActivity_full (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) (P : LayerColumn N) :
    Summable fun k => |colActivity ρ μG β k u u' P| :=
  (summable_nat_add_iff 1).mp
    (summable_abs_colActivity ρ μG hN hρcont β u u' P)

/-- The column sum splits as vacuum plus non-vacuum tail:
`colZ = 1 + ∑' k, colActivity β (k+1)`. -/
theorem colZ_eq_one_add (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) (P : LayerColumn N) :
    colZ ρ μG β u u' P
      = 1 + ∑' k, colActivity ρ μG β (k + 1) u u' P := by
  have h := (summable_colActivity ρ μG hN hρcont β u u' P).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at h
  rw [colActivity_zero ρ μG β u u' P] at h
  rw [colZ, ← h]

/-- **The column sum is a function of `β` alone** — not of the
column, not of the boundary links (LOC-1's
`colActivity_independent`, summed). -/
theorem colZ_independent (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' v v' : LayerLink N → G)
    (P Q : LayerColumn N) :
    colZ ρ μG β u u' P = colZ ρ μG β v v' Q :=
  tsum_congr fun k =>
    colActivity_independent ρ μG hN hρcont β k u u' v v' P Q

/-- The exponential series of the majorant, summed: the engine
estimate behind the column bridge. -/
theorem tsum_pow_div_factorial (β : ℝ) :
    ∑' k, (2 * |β|) ^ k / ((Nat.factorial k : ℝ))
      = Real.exp (2 * |β|) := by
  have h1 : Real.exp (2 * |β|) = NormedSpace.exp (2 * |β|) :=
    congrFun Real.exp_eq_exp_ℝ _
  rw [h1, congrFun (NormedSpace.exp_eq_tsum ℝ) (2 * |β|)]
  exact tsum_congr fun n => by
    rw [smul_eq_mul, div_eq_inv_mul, mul_comm]

/-- **The column bridge**: the column activity sum is the
column's Boltzmann average — the activity series sums, under the
stratum integral, to `∫ exp (-β * dens_P)`. The interchange is
dominated by the landed majorant `(2|β|)ᵏ/k!`. -/
theorem colZ_eq_integral_exp
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) (P : LayerColumn N) :
    colZ ρ μG β u u' P
      = ∫ α, Real.exp (-β * colDensC ρ u u' P α)
          ∂(Measure.pi fun _ : LayerSite N => μG) := by
  classical
  set μ : Measure (LayerSite N → G) :=
    Measure.pi fun _ : LayerSite N => μG with hμ
  have hmeas : Measurable fun α => colDensC ρ u u' P α := by
    have hfun : (fun α => colDensC ρ u u' P α)
        = fun α => 1 - colRe ρ u u' P α / (d : ℝ) :=
      funext fun α => colDensC_eq ρ u u' P α
    rw [hfun]
    exact measurable_const.sub
      ((measurable_colRe ρ hρcont u u' P).div_const _)
  have hdens0 : ∀ α, 0 ≤ colDensC ρ u u' P α :=
    fun α => colDens_nonneg ρ u u' P.1 P.2.1 P.2.2 α
  have hdens2 : ∀ α, colDensC ρ u u' P α ≤ 2 :=
    fun α => colDens_le_two ρ u u' P.1 P.2.1 P.2.2 α
  have hbound : ∀ (k : ℕ) (α : LayerSite N → G),
      |(-β) ^ k / ((Nat.factorial k : ℝ))
        * (colDensC ρ u u' P α) ^ k|
      ≤ (2 * |β|) ^ k / ((Nat.factorial k : ℝ)) := by
    intro k α
    have hk : (0:ℝ) < (Nat.factorial k : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos k)
    rw [abs_mul, abs_div, abs_pow, abs_neg, abs_pow,
      abs_of_pos hk, abs_of_nonneg (hdens0 α)]
    have h1 : (colDensC ρ u u' P α) ^ k ≤ 2 ^ k :=
      pow_le_pow_left₀ (hdens0 α) (hdens2 α) k
    have h2 : |β| ^ k * (colDensC ρ u u' P α) ^ k
        ≤ (2 * |β|) ^ k := by
      rw [mul_pow, mul_comm (|β| ^ k) ((colDensC ρ u u' P α) ^ k)]
      exact mul_le_mul_of_nonneg_right h1
        (pow_nonneg (abs_nonneg β) k)
    calc |β| ^ k / (Nat.factorial k : ℝ)
          * (colDensC ρ u u' P α) ^ k
        = |β| ^ k * (colDensC ρ u u' P α) ^ k
            / (Nat.factorial k : ℝ) := by ring
      _ ≤ (2 * |β|) ^ k / (Nat.factorial k : ℝ) :=
          div_le_div_of_nonneg_right h2 (le_of_lt hk)
  have hf : ∀ k, AEStronglyMeasurable
      (fun α => (-β) ^ k / ((Nat.factorial k : ℝ))
        * (colDensC ρ u u' P α) ^ k) μ :=
    fun k => (measurable_const.mul
      (hmeas.pow_const k)).aestronglyMeasurable
  have hf' : ∑' k, ∫⁻ α, ‖(-β) ^ k / ((Nat.factorial k : ℝ))
        * (colDensC ρ u u' P α) ^ k‖ₑ ∂μ ≠ ⊤ := by
    have hterm : ∀ k, ∫⁻ α, ‖(-β) ^ k / ((Nat.factorial k : ℝ))
          * (colDensC ρ u u' P α) ^ k‖ₑ ∂μ
        ≤ ENNReal.ofReal ((2 * |β|) ^ k
            / ((Nat.factorial k : ℝ))) := by
      intro k
      calc ∫⁻ α, ‖(-β) ^ k / ((Nat.factorial k : ℝ))
              * (colDensC ρ u u' P α) ^ k‖ₑ ∂μ
          ≤ ∫⁻ _α, ENNReal.ofReal ((2 * |β|) ^ k
              / ((Nat.factorial k : ℝ))) ∂μ :=
            lintegral_mono_ae (Filter.Eventually.of_forall fun α => by
              rw [Real.enorm_eq_ofReal_abs]
              exact ENNReal.ofReal_le_ofReal (hbound k α))
        _ = ENNReal.ofReal ((2 * |β|) ^ k
              / ((Nat.factorial k : ℝ))) := by
            rw [lintegral_const, measure_univ, mul_one]
    have hsum : (∑' k, ∫⁻ α, ‖(-β) ^ k / ((Nat.factorial k : ℝ))
          * (colDensC ρ u u' P α) ^ k‖ₑ ∂μ)
        ≤ ENNReal.ofReal (Real.exp (2 * |β|)) := by
      calc (∑' k, ∫⁻ α, ‖(-β) ^ k / ((Nat.factorial k : ℝ))
              * (colDensC ρ u u' P α) ^ k‖ₑ ∂μ)
          ≤ ∑' k, ENNReal.ofReal ((2 * |β|) ^ k
              / ((Nat.factorial k : ℝ))) :=
            ENNReal.tsum_le_tsum hterm
        _ = ENNReal.ofReal (Real.exp (2 * |β|)) := by
            rw [← tsum_pow_div_factorial β,
              ENNReal.ofReal_tsum_of_nonneg
                (fun k => by positivity)
                (Real.summable_pow_div_factorial _)]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum
  have hpt : ∀ α : LayerSite N → G,
      ∑' k, (-β) ^ k / ((Nat.factorial k : ℝ))
          * (colDensC ρ u u' P α) ^ k
        = Real.exp (-β * colDensC ρ u u' P α) := by
    intro α
    have hterm : ∀ k, (-β) ^ k / ((Nat.factorial k : ℝ))
          * (colDensC ρ u u' P α) ^ k
        = (-β * colDensC ρ u u' P α) ^ k
            / ((Nat.factorial k : ℝ)) := by
      intro k
      rw [mul_pow, div_mul_eq_mul_div]
    rw [tsum_congr hterm]
    have h1 : Real.exp (-β * colDensC ρ u u' P α)
        = NormedSpace.exp (-β * colDensC ρ u u' P α) :=
      congrFun Real.exp_eq_exp_ℝ _
    rw [h1, congrFun (NormedSpace.exp_eq_tsum ℝ)
      (-β * colDensC ρ u u' P α)]
    exact tsum_congr fun n => by
      rw [smul_eq_mul, div_eq_inv_mul, mul_comm]
  calc colZ ρ μG β u u' P
      = ∑' k, ∫ α, (-β) ^ k / ((Nat.factorial k : ℝ))
          * (colDensC ρ u u' P α) ^ k ∂μ := rfl
    _ = ∫ α, ∑' k, (-β) ^ k / ((Nat.factorial k : ℝ))
          * (colDensC ρ u u' P α) ^ k ∂μ :=
        (integral_tsum hf hf').symm
    _ = ∫ α, Real.exp (-β * colDensC ρ u u' P α) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)

/-- The column's Boltzmann factor, integrated: a lower bound on
`colZ` from `0 ≤ dens ≤ 2`. -/
theorem colZ_pos
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) (P : LayerColumn N) :
    0 < colZ ρ μG β u u' P := by
  classical
  set μ : Measure (LayerSite N → G) :=
    Measure.pi fun _ : LayerSite N => μG with hμ
  have hmeas : Measurable fun α => colDensC ρ u u' P α := by
    have hfun : (fun α => colDensC ρ u u' P α)
        = fun α => 1 - colRe ρ u u' P α / (d : ℝ) :=
      funext fun α => colDensC_eq ρ u u' P α
    rw [hfun]
    exact measurable_const.sub
      ((measurable_colRe ρ hρcont u u' P).div_const _)
  have hdens0 : ∀ α, 0 ≤ colDensC ρ u u' P α :=
    fun α => colDens_nonneg ρ u u' P.1 P.2.1 P.2.2 α
  have hdens2 : ∀ α, colDensC ρ u u' P α ≤ 2 :=
    fun α => colDens_le_two ρ u u' P.1 P.2.1 P.2.2 α
  have hInt : Integrable
      (fun α => Real.exp (-β * colDensC ρ u u' P α)) μ := by
    refine Integrable.of_bound
      ((Real.continuous_exp.measurable.comp
        (hmeas.const_mul (-β))).aestronglyMeasurable)
      (Real.exp (2 * |β|)) (Filter.Eventually.of_forall fun α => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have habs : |β * colDensC ρ u u' P α| ≤ 2 * |β| := by
      rw [abs_mul, abs_of_nonneg (hdens0 α)]
      have hh := mul_le_mul_of_nonneg_left (hdens2 α)
        (abs_nonneg β)
      rwa [mul_comm |β| 2] at hh
    linarith [neg_le_abs (β * colDensC ρ u u' P α)]
  have hge : Real.exp (-2 * |β|)
      ≤ ∫ α, Real.exp (-β * colDensC ρ u u' P α) ∂μ := by
    have hle : ∀ α, Real.exp (-2 * |β|)
        ≤ Real.exp (-β * colDensC ρ u u' P α) := by
      intro α
      apply Real.exp_le_exp.mpr
      have habs : |β * colDensC ρ u u' P α| ≤ 2 * |β| := by
        rw [abs_mul, abs_of_nonneg (hdens0 α)]
        have hh := mul_le_mul_of_nonneg_left (hdens2 α)
          (abs_nonneg β)
        rwa [mul_comm |β| 2] at hh
      linarith [le_abs_self (β * colDensC ρ u u' P α)]
    have hconst : ∫ _α : LayerSite N → G, Real.exp (-2 * |β|) ∂μ
        = Real.exp (-2 * |β|) := by simp
    rw [← hconst]
    exact integral_mono_ae (integrable_const _) hInt
      (Filter.Eventually.of_forall hle)
  rw [colZ_eq_integral_exp ρ μG hρcont β u u' P]
  exact lt_of_lt_of_le (Real.exp_pos _) hge

/-- **The activity tail bound, all signs of `β`**: the column
sum sits within `exp (2|β|) − 1` of the vacuum value `1`. -/
theorem abs_colZ_sub_one_le (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) (P : LayerColumn N) :
    |colZ ρ μG β u u' P - 1| ≤ Real.exp (2 * |β|) - 1 := by
  have hsplit := colZ_eq_one_add ρ μG hN hρcont β u u' P
  have hsub : colZ ρ μG β u u' P - 1
      = ∑' k, colActivity ρ μG β (k + 1) u u' P := by
    rw [hsplit]; ring
  rw [hsub]
  calc |∑' k, colActivity ρ μG β (k + 1) u u' P|
      ≤ ∑' k, |colActivity ρ μG β (k + 1) u u' P| := by
        have h := norm_tsum_le_tsum_norm
          (f := fun k => colActivity ρ μG β (k + 1) u u' P)
          (by simpa [Real.norm_eq_abs] using
            summable_abs_colActivity ρ μG hN hρcont β u u' P)
        simpa [Real.norm_eq_abs] using h
    _ ≤ ∑' k, (2 * |β|) ^ (k + 1)
          / ((Nat.factorial (k + 1) : ℝ)) :=
        (summable_abs_colActivity ρ μG hN hρcont β u u' P).tsum_le_tsum
          (fun k => abs_colActivity_le ρ μG hN hρcont β (k + 1) u u' P)
          (by
            have h := degMajorant_summable_shift β
            exact h.congr fun k => degMajorant_succ β k)
    _ = Real.exp (2 * |β|) - 1 := by
        have h := tsum_degMajorant_shift β
        exact (tsum_congr fun k => (degMajorant_succ β k).symm).trans h

/-- The factorized partition function is positive: a product of
positive column sums. -/
theorem zpolymer_pos
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) :
    0 < zPolymer ρ μG β u u' :=
  Finset.prod_pos fun P _ => colZ_pos ρ μG hρcont β u u' P

/-- **The bridge, log form**: the logarithm of the factorized
layer weight is the sum over columns of the logarithms of the
column activity sums — the polymer sum in logarithmic form. -/
theorem log_zpolymer
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) :
    Real.log (zPolymer ρ μG β u u')
      = ∑ P, Real.log (colZ ρ μG β u u' P) := by
  rw [zPolymer, Real.log_prod fun P _ =>
    ne_of_gt (colZ_pos ρ μG hρcont β u u' P)]

/-- **The bridge, density form**: by column-independence the log
sum is the column count times any single column's log — the
per-volume free-energy density of `zPolymer` is the
`N`-independent number `log (colZ P)`. -/
theorem log_zpolymer_eq (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) (P : LayerColumn N) :
    Real.log (zPolymer ρ μG β u u')
      = colCount N * Real.log (colZ ρ μG β u u' P) := by
  rw [log_zpolymer ρ μG hρcont β u u']
  calc ∑ Q, Real.log (colZ ρ μG β u u' Q)
      = ∑ _Q : LayerColumn N, Real.log (colZ ρ μG β u u' P) :=
        Finset.sum_congr rfl fun Q _ => congrArg Real.log
          (colZ_independent ρ μG hN hρcont β u u' u u' Q P)
    _ = colCount N * Real.log (colZ ρ μG β u u' P) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          colCount]

/-- A support's total absolute activity is majorized by the
degree-majorant product (LOC-1's bound, supportwise — the
estimate inside LOC-2's `supportActivity_tsum_abs_le`). -/
theorem abs_supportActivity_le (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G)
    (S : Finset (LayerColumn N)) (j : ↥S → ℕ) :
    |supportActivity ρ μG β u u' S j|
      ≤ ∏ x : ↥S, degMajorant β (j x + 1) := by
  rw [supportActivity, Finset.abs_prod]
  refine Finset.prod_le_prod₀ (fun x _ => abs_nonneg _)
    fun x _ => ?_
  rw [degMajorant_succ]
  exact abs_colActivity_le ρ μG hN hρcont β (j x + 1) u u' x.1

/-- The support activity over `insert c S`, split along
`degAssignEquiv` (LOC-2's assignment equivalence): the factor at
the inserted column times the support activity over `S`. The
proof is LOC-2's `degProd_split` argument with the activity in
place of the majorant. -/
theorem supportActivity_split {c : LayerColumn N}
    {S : Finset (LayerColumn N)} (hcS : c ∉ S)
    (β : ℝ) (u u' : LayerLink N → G) (j : ℕ) (k' : ↥S → ℕ) :
    supportActivity ρ μG β u u' (insert c S)
        ((degAssignEquiv hcS).symm (j, k'))
      = colActivity ρ μG β (j + 1) u u' c
        * supportActivity ρ μG β u u' S k' := by
  classical
  set e := (degAssignEquiv hcS).symm (j, k') with he
  set G' : LayerColumn N → ℝ := fun y =>
    if hy : y ∈ insert c S
    then colActivity ρ μG β (e ⟨y, hy⟩ + 1) u u' y
    else 1 with hG'
  have hGc : G' c = colActivity ρ μG β (j + 1) u u' c := by
    show (if hy : c ∈ insert c S
        then colActivity ρ μG β (e ⟨c, hy⟩ + 1) u u' c
        else 1) = colActivity ρ μG β (j + 1) u u' c
    rw [dif_pos (Finset.mem_insert_self c S), he,
      degAssignEquiv_symm_fst hcS j k']
  have hGS : ∀ x : ↥S, G' x.1
      = colActivity ρ μG β (k' x + 1) u u' x.1 := by
    intro x
    show (if hy : x.1 ∈ insert c S
        then colActivity ρ μG β (e ⟨x.1, hy⟩ + 1) u u' x.1
        else 1) = colActivity ρ μG β (k' x + 1) u u' x.1
    rw [dif_pos (Finset.mem_insert_of_mem x.2), he,
      degAssignEquiv_symm_of_mem hcS j k' x.1 x.2]
  have hGtop : ∀ x : ↥(insert c S), G' x.1
      = colActivity ρ μG β (e x + 1) u u' x.1 := by
    intro x
    show (if hy : x.1 ∈ insert c S
        then colActivity ρ μG β (e ⟨x.1, hy⟩ + 1) u u' x.1
        else 1) = colActivity ρ μG β (e x + 1) u u' x.1
    rw [dif_pos x.2]
  show (∏ x : ↥(insert c S),
      colActivity ρ μG β (e x + 1) u u' x.1)
    = colActivity ρ μG β (j + 1) u u' c
      * ∏ x : ↥S, colActivity ρ μG β (k' x + 1) u u' x.1
  calc ∏ x : ↥(insert c S),
        colActivity ρ μG β (e x + 1) u u' x.1
      = ∏ x : ↥(insert c S), G' x.1 :=
        Finset.prod_congr rfl fun x _ => (hGtop x).symm
    _ = ∏ y ∈ insert c S, G' y := by
        rw [← Finset.prod_attach (insert c S) G',
          Finset.univ_eq_attach]
    _ = G' c * ∏ y ∈ S, G' y := Finset.prod_insert hcS
    _ = colActivity ρ μG β (j + 1) u u' c
          * ∏ x : ↥S, colActivity ρ μG β (k' x + 1) u u' x.1 := by
        rw [hGc, ← Finset.prod_attach S G',
          Finset.univ_eq_attach]
        congr 1
        exact Finset.prod_congr rfl fun x _ => hGS x

/-- **The per-support expansion identity**: over any finite
support, the product of the columns' non-vacuum activity sums is
the total support activity — the degree-assignment sum of
LOC-2's `supportActivity`. -/
theorem prod_colZ_sub_one_eq (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) :
    ∀ S : Finset (LayerColumn N),
      ∏ P ∈ S, (colZ ρ μG β u u' P - 1)
        = ∑' j : ↥S → ℕ, supportActivity ρ μG β u u' S j := by
  have hb : ∀ P : LayerColumn N, colZ ρ μG β u u' P - 1
      = ∑' k, colActivity ρ μG β (k + 1) u u' P := by
    intro P
    have h := colZ_eq_one_add ρ μG hN hρcont β u u' P
    linarith
  intro S
  induction S using Finset.induction with
  | empty =>
    have hU : Unique (↥(∅ : Finset (LayerColumn N)) → ℕ) :=
      ⟨⟨fun _ => 0⟩, fun k => funext fun x =>
        (Finset.notMem_empty x.1 x.2).elim⟩
    haveI := hU
    have h := (hasSum_unique
      (fun j : ↥(∅ : Finset (LayerColumn N)) → ℕ =>
        supportActivity ρ μG β u u' ∅ j)).tsum_eq
    rw [h]
    simp [supportActivity]
  | @insert c S hcS ih =>
    have hf : Summable fun j =>
        colActivity ρ μG β (j + 1) u u' c :=
      (summable_abs_colActivity ρ μG hN hρcont β u u' c).of_abs
    have hg : Summable fun k' : ↥S → ℕ =>
        supportActivity ρ μG β u u' S k' :=
      Summable.of_norm_bounded (degProd_hasSum β S).summable
        (fun k' => abs_supportActivity_le ρ μG hN hρcont β u u' S k')
    have hmaj : Summable (fun p : ℕ × (↥S → ℕ) =>
        degMajorant β (p.1 + 1)
          * ∏ x : ↥S, degMajorant β (p.2 x + 1)) := by
      have h2 := ((degAssignEquiv hcS).symm.summable_iff).mpr
        (degProd_hasSum β (insert c S)).summable
      refine h2.congr fun p => ?_
      obtain ⟨j, k'⟩ := p
      exact degProd_split hcS β j k'
    have hprod : Summable (fun p : ℕ × (↥S → ℕ) =>
        colActivity ρ μG β (p.1 + 1) u u' c
          * supportActivity ρ μG β u u' S p.2) := by
      refine Summable.of_norm_bounded hmaj fun p => ?_
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul
        (by rw [degMajorant_succ]; exact
          abs_colActivity_le ρ μG hN hρcont β (p.1 + 1) u u' c)
        (abs_supportActivity_le ρ μG hN hρcont β u u' S p.2)
        (abs_nonneg _) (degMajorant_nonneg β _)
    calc ∏ P ∈ insert c S, (colZ ρ μG β u u' P - 1)
        = (colZ ρ μG β u u' c - 1)
            * ∏ P ∈ S, (colZ ρ μG β u u' P - 1) :=
          Finset.prod_insert hcS
      _ = (∑' j, colActivity ρ μG β (j + 1) u u' c)
            * ∑' k' : ↥S → ℕ, supportActivity ρ μG β u u' S k' := by
          rw [hb c, ih]
      _ = ∑' p : ℕ × (↥S → ℕ),
            colActivity ρ μG β (p.1 + 1) u u' c
              * supportActivity ρ μG β u u' S p.2 :=
          Summable.tsum_mul_tsum hf hg hprod
      _ = ∑' p : ℕ × (↥S → ℕ), supportActivity ρ μG β u u'
            (insert c S) ((degAssignEquiv hcS).symm p) :=
          tsum_congr fun p => by
            obtain ⟨j, k'⟩ := p
            exact (supportActivity_split ρ μG hcS β u u' j k').symm
      _ = ∑' j : ↥(insert c S) → ℕ,
            supportActivity ρ μG β u u' (insert c S) j :=
          (degAssignEquiv hcS).symm.tsum_eq _

/-- **The KS implication (LOC-3 headline).** Inside the landed
Kotecky–Preiss radius, everything the criterion exists for, at
the generality the owned objects support:

- the per-column cluster sum is `≤ 1` at every column
  (LOC-2's `ks_criterion_full`, transported verbatim);
- the bridge identifies `log zPolymer` with
  `colCount N * log (colZ P)` — so the per-volume free-energy
  density of the factorized layer weight is the single
  `N`-independent number `log (colZ P)`;
- that number's defining series — the logarithm series of the
  column activity sum — converges **absolutely**, with total
  majorant `(exp (2|β|) − 1)/(1 − (exp (2|β|) − 1))`, a bound
  depending only on `|β|`: the convergence is uniform in `N`,
  in the volume, and in the boundary links;
- and the series sums to `log (colZ P)`.

All sums are finite-volume sums; no infinite-volume or
continuum object is asserted (KL3-2). -/
theorem ks_implication (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (hβ : |β| < beta0) (u u' : LayerLink N → G)
    (P : LayerColumn N) :
    (∀ x, clusterSum ρ μG β u u' x ≤ 1)
      ∧ Real.log (zPolymer ρ μG β u u')
          = colCount N * Real.log (colZ ρ μG β u u' P)
      ∧ Summable (fun n : ℕ => |colZ ρ μG β u u' P - 1| ^ (n + 1)
          / ((n : ℝ) + 1))
      ∧ (∑' n : ℕ, |colZ ρ μG β u u' P - 1| ^ (n + 1)
          / ((n : ℝ) + 1))
          ≤ (Real.exp (2 * |β|) - 1)
            / (1 - (Real.exp (2 * |β|) - 1))
      ∧ HasSum (fun n : ℕ => -((1 - colZ ρ μG β u u' P) ^ (n + 1)
          / ((n : ℝ) + 1))) (Real.log (colZ ρ μG β u u' P)) := by
  set w : ℝ := Real.exp (2 * |β|) - 1 with hw
  have hw0 : 0 ≤ w := by
    have h := Real.exp_le_exp.mpr
      (show (0:ℝ) ≤ 2 * |β| by positivity)
    rw [Real.exp_zero] at h
    linarith
  have hw1 : w < 1 := by
    have hlt := cluster_weight_lt β hβ
    have he : (1:ℝ) < Real.exp 1 :=
      Real.one_lt_exp_iff.mpr zero_lt_one
    have h729 : 729 * w ≤ 729 * (Real.exp 1 * w) := by
      have h1 : w ≤ Real.exp 1 * w := by
        calc w = 1 * w := (one_mul w).symm
          _ ≤ Real.exp 1 * w :=
            mul_le_mul_of_nonneg_right he.le hw0
      exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    linarith
  have hc1 : |colZ ρ μG β u u' P - 1| ≤ w :=
    abs_colZ_sub_one_le ρ μG hN hρcont β u u' P
  have hlt : |1 - colZ ρ μG β u u' P| < 1 := by
    rw [abs_sub_comm]
    exact lt_of_le_of_lt hc1 hw1
  have hgeom : Summable fun n => w ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr
      (summable_geometric_of_lt_one hw0 hw1)
  have hbound : ∀ n : ℕ, |colZ ρ μG β u u' P - 1| ^ (n + 1)
        / ((n : ℝ) + 1) ≤ w ^ (n + 1) := by
    intro n
    calc |colZ ρ μG β u u' P - 1| ^ (n + 1) / ((n : ℝ) + 1)
        ≤ |colZ ρ μG β u u' P - 1| ^ (n + 1) :=
          div_le_self (pow_nonneg (abs_nonneg _) _)
            (le_add_of_nonneg_left (Nat.cast_nonneg n))
      _ ≤ w ^ (n + 1) :=
          pow_le_pow_left₀ (abs_nonneg _) hc1 _
  have hsumm : Summable (fun n : ℕ =>
      |colZ ρ μG β u u' P - 1| ^ (n + 1) / ((n : ℝ) + 1)) :=
    Summable.of_nonneg_of_le
      (g := fun n : ℕ => |colZ ρ μG β u u' P - 1| ^ (n + 1)
        / ((n : ℝ) + 1))
      (fun n => by positivity) hbound hgeom
  have hgeo : ∑' n, w ^ (n + 1) = w / (1 - w) := by
    have hs := (summable_geometric_of_lt_one hw0 hw1).sum_add_tsum_nat_add 1
    rw [tsum_geometric_of_lt_one hw0 hw1] at hs
    simp only [Finset.sum_range_one, pow_zero] at hs
    have hsh : ∑' n, w ^ (n + 1) = (1 - w)⁻¹ - 1 := by linarith
    rw [hsh, eq_div_iff (sub_ne_zero.mpr hw1.ne'), sub_mul,
      inv_mul_cancel₀ (sub_ne_zero.mpr hw1.ne'), one_mul]
    ring
  have hlog : HasSum (fun n : ℕ =>
        -((1 - colZ ρ μG β u u' P) ^ (n + 1) / ((n : ℝ) + 1)))
      (Real.log (colZ ρ μG β u u' P)) := by
    have h := (Real.hasSum_pow_div_log_of_abs_lt_one
      (x := 1 - colZ ρ μG β u u' P) hlt).neg
    have harg : (1:ℝ) - (1 - colZ ρ μG β u u' P)
        = colZ ρ μG β u u' P := by ring
    rw [harg, neg_neg] at h
    exact h
  refine ⟨fun x => ks_criterion_full ρ μG hN hρcont β hβ u u' x,
    log_zpolymer_eq ρ μG hN hρcont β u u' P, hsumm, ?_, hlog⟩
  calc (∑' n : ℕ, |colZ ρ μG β u u' P - 1| ^ (n + 1) / ((n : ℝ) + 1))
      ≤ ∑' n, w ^ (n + 1) := hsumm.tsum_le_tsum hbound hgeom
    _ = w / (1 - w) := hgeo

theorem zpolymer_eq_sum_supports (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) :
    zPolymer ρ μG β u u'
      = ∑ S ∈ Finset.univ.powerset,
          ∑' j : ↥S → ℕ, supportActivity ρ μG β u u' S j := by
  have h1 : ∀ P : LayerColumn N, colZ ρ μG β u u' P
      = (colZ ρ μG β u u' P - 1) + 1 := fun P => by ring
  calc zPolymer ρ μG β u u'
      = ∏ P : LayerColumn N, ((colZ ρ μG β u u' P - 1) + 1) :=
        Finset.prod_congr rfl fun P _ => h1 P
    _ = ∑ S ∈ Finset.univ.powerset,
          ∏ P ∈ S, (colZ ρ μG β u u' P - 1) := by
        rw [Finset.prod_add]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.prod_const_one, mul_one]
    _ = ∑ S ∈ Finset.univ.powerset,
          ∑' j : ↥S → ℕ, supportActivity ρ μG β u u' S j :=
        Finset.sum_congr rfl fun S _ =>
          prod_colZ_sub_one_eq ρ μG hN hρcont β u u' S

end PolymerPartition

end

end ThetLogos
