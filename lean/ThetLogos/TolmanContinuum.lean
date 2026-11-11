import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import ThetLogos.TolmanExhibit

namespace ThetLogos

open MeasureTheory

/-!
# ThetLogos.TolmanContinuum — MQ3-T1, the continuum Tolman equilibrium

Bench queue position 15 (Zero's ratified queue, 2026-11-08: "build and
run any and all"), the last brick of the M-Q3 continuum lane.
**Pin:** `~/workspace/your_files/m-q3-scope-2026-11-08.md` §2(d) + §4 —
a refinement system for Tolman seats (domains at spacing `1/N`, weight
and occupation embeddings — design inside the rung) under which finite
equilibria converge, and the limit pair `(x, a)` on the continuum
domain satisfies the slope identity `occSlope (x i) = λ · a i` a.e. at
one global `λ` — the landed finite characterization
(`tolman_characterization`) transported through the limit, both
directions. **Price: M–L, est. 15–30 strict. NO CLAIM. Dials 0/4.
Dial 3 = 0, Dial 2 = 0. Pre-registered DIAL-INELIGIBLE** (a parallel
line, independent of MQ3-1..6; it is not the §1 event — K-MQ3-PROXY
stands over any summary that sells it as one).

## The refinement system (the rung's design, on the face)

The continuum domain is `[0, 1]`. At level `n` the finite seat is
`Fin (n + 1)` with sites at the grid points `i / (n + 1)`; the weight
and occupation embeddings are **sampling**: the finite configuration
at level `n` is the continuum pair `(x, a)` read at the grid points.
A continuum pair is a refinement-limit equilibrium when its samples
are finite Tolman equilibria at *every* level. Convergence in this
system is exact on grids (the finite equilibrium at each level is the
limit pair's own restriction); the transported content is that the
per-level slope witnesses `λ_n` — a priori one per level — collapse
to a single global `λ` (they are all read off at the shared grid
point `0`), and that grid agreement plus continuity forces the slope
identity at every point of `[0, 1]` (the grids are dense), hence a.e.

## Charter note — what is NOT in this brick

The §5 joint insertion (the metric-carrier design: the limit weight
proved to be a metric component `√g_tt`, with the metric determined
by the construction) is **not** built here. Its inclusion in this
rung's charter is §6 decision 3 of the scoping — Zero's open chair,
never ruled — and statement-level additions are never taken silently.
This brick builds the §4 pin in its pure continuum-equilibrium form;
the weight `a` remains a bare positive site weight at every level and
in the limit (**K-TOL-PROXY does not fire**: no statement names or
treats it as a metric, a metric component, or a redshift factor).
The audit brick MQ3-J remains for whenever an object is put to it.

## Kill register

- **K-MQ3-TOLMAN-LIMIT** — fires if finite equilibria fail to
  converge under refinement, or the limit equilibrium is not
  characterized by the slope identity. The characterization below is
  an iff, proved; the kill does not fire.
- **K-MQ3-PROXY** — armed over any presentation of this rung as
  Dial-3 motion or as the §1 event. It is neither.
- **K-TOL-VAC (inherited discipline)** — the continuum
  characterization is an iff, with a named continuum equilibrium
  certified (`tolman_continuum_witness`) and a named pair certified
  NOT one (`tolman_continuum_nonwitness`).
-/

/-- **The refinement grid** (rung design): at level `n` the finite
seat `Fin (n + 1)` sits in the continuum domain `[0, 1]` at the
points `i / (n + 1)`, spacing `1 / (n + 1)`. Tier T1 (definition). -/
noncomputable def tolmanGrid (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  (i : ℝ) / ((n + 1 : ℕ) : ℝ)

/-- Grid points lie in the continuum domain. Tier T1. -/
theorem tolmanGrid_mem_Icc {n : ℕ} {i : Fin (n + 1)} :
    tolmanGrid n i ∈ Set.Icc (0 : ℝ) 1 := by
  have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hnpos.le
  · have h1 : (i : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.lt_succ_iff.mp i.2
    have h2 : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one]
      linarith
    exact (div_le_one hnpos).mpr (le_trans h1 h2)

/-- The grid point at site `0` is the domain's left endpoint, at
every level — the shared point that pins one global `λ`. Tier T1. -/
theorem tolmanGrid_zero {n : ℕ} : tolmanGrid n 0 = 0 := by
  simp [tolmanGrid]

/-- Every rational in `[0, 1)` is a grid point (at the level given by
its denominator). Tier T1. -/
theorem exists_tolmanGrid_eq_rat {q : ℚ} (h0 : 0 ≤ q) (h1 : q < 1) :
    ∃ (n : ℕ) (i : Fin (n + 1)), tolmanGrid n i = (q : ℝ) := by
  have hden : 0 < q.den := q.den_pos
  have hnum0 : 0 ≤ q.num := Rat.num_nonneg.mpr h0
  have hnumlt : q.num < (q.den : ℤ) := by
    have hcast : (q.num : ℚ) < (q.den : ℚ) := by
      have h := h1
      rw [← Rat.num_div_den q] at h
      have hd : (0 : ℚ) < (q.den : ℚ) := by exact_mod_cast hden
      exact (div_lt_one hd).mp h
    exact_mod_cast hcast
  refine ⟨q.den - 1, ⟨q.num.toNat, ?_⟩, ?_⟩
  · have htn : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg hnum0
    have h3 : q.num.toNat < q.den := by
      have h4 : (q.num.toNat : ℤ) < (q.den : ℤ) := by
        rw [htn]; exact hnumlt
      exact_mod_cast h4
    have h5 : q.den - 1 + 1 = q.den := Nat.sub_add_cancel hden
    omega
  · have h5 : q.den - 1 + 1 = q.den := Nat.sub_add_cancel hden
    simp only [tolmanGrid, h5]
    have htn : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum0]
    rw [htn]
    have hcast : ((q.num : ℝ)) / ((q.den : ℕ) : ℝ) = (q : ℝ) := by
      have e1 : ((q.num : ℝ)) = ((q.num : ℚ) : ℝ) := by exact_mod_cast rfl
      have e2 : (((q.den : ℕ) : ℝ)) = ((q.den : ℚ) : ℝ) := by
        exact_mod_cast rfl
      rw [e1, e2, ← Rat.cast_div, Rat.num_div_den]
    exact hcast

/-- **The grids are dense in `[0, 1]`:** every point of the domain is
approximated arbitrarily well by grid points (through the rationals
in `[0, 1)`, each of which is a grid point). Tier T1. -/
theorem tolmanGrid_eventually_close {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (i : Fin (n + 1)), |t - tolmanGrid n i| < ε := by
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨q, hq0, hq1, hqε⟩ :
      ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) < 1 ∧ |t - (q : ℝ)| < ε := by
    by_cases hte : t = 1
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
        (show max (1 - ε) (1 / 2 : ℝ) < 1 from
          max_lt (by linarith) (by norm_num))
      refine ⟨q, ?_, hq2, ?_⟩
      · have h3 : (1 / 2 : ℝ) < (q : ℝ) :=
          lt_of_le_of_lt (le_max_right _ _) hq1
        linarith
      · have h4 : (1 : ℝ) - ε < (q : ℝ) :=
          lt_of_le_of_lt (le_max_left _ _) hq1
        subst hte
        rw [abs_of_pos (by linarith : (0 : ℝ) < 1 - (q : ℝ))]
        linarith
    · have ht1' : t < 1 := lt_of_le_of_ne ht1 hte
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
        (show t < min (t + ε) 1 from lt_min (by linarith) ht1')
      refine ⟨q, by linarith, lt_of_lt_of_le hq2 (min_le_right _ _), ?_⟩
      have h5 : (q : ℝ) < t + ε := lt_of_lt_of_le hq2 (min_le_left _ _)
      rw [abs_sub_comm, abs_of_pos (by linarith : (0 : ℝ) < (q : ℝ) - t)]
      linarith
  obtain ⟨n, i, hi⟩ := exists_tolmanGrid_eq_rat
    (by exact_mod_cast hq0) (by exact_mod_cast hq1)
  exact ⟨n, i, hi ▸ hqε⟩

/-- **The occupation/weight embedding at level `n`** (rung design):
sampling the continuum function at the grid points. Tier T1
(definition). -/
noncomputable def tolmanSample (f : ℝ → ℝ) (n : ℕ) : Fin (n + 1) → ℝ :=
  fun i => f (tolmanGrid n i)

/-- **Refinement-limit equilibrium** (rung design): the continuum
pair `(a, x)` is an equilibrium of the refinement system when its
samples are finite Tolman equilibria at every level. Tier T1
(definition). -/
def IsRefinementLimitEquilibrium (a x : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, IsTolmanEquilibrium (tolmanSample a n) (tolmanSample x n)

/-- **Continuity of the slope along a continuum occupation:** on
`[0, 1]`, `t ↦ occSlope (x t)` is continuous wherever `x` is
continuous and interior — the logarithm is continuous at the
positive arguments `x t` and `1 - x t`. Tier T1. -/
theorem continuousOn_occSlope_comp {x : ℝ → ℝ}
    (hx : ContinuousOn x (Set.Icc 0 1))
    (hx01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < x t ∧ x t < 1) :
    ContinuousOn (fun t => occSlope (x t)) (Set.Icc 0 1) := by
  have h1 : ContinuousOn (fun t => Real.log (1 - x t)) (Set.Icc 0 1) := by
    apply ContinuousOn.log (continuousOn_const.sub hx)
    intro t ht
    have h2 : x t < 1 := (hx01 t ht).2
    exact ne_of_gt (by linarith : (0 : ℝ) < 1 - x t)
  have h2 : ContinuousOn (fun t => Real.log (x t)) (Set.Icc 0 1) :=
    hx.log (fun t ht => ne_of_gt (hx01 t ht).1)
  exact h1.sub h2

/-- **One global `λ` on all grids (the λ-collapse):** if the samples
of `(a, x)` are finite equilibria at every level, then a *single*
`λ` — read off at the grid point `0` shared by every level —
witnesses the finite slope condition at every grid point of every
level. Each level's own witness is forced to agree with it at site
`0`, where the sampled weight and occupation are the same at all
levels. This is the transport's engine. Tier T1. -/
theorem slope_eq_on_grid_of_refinementLimit {a x : ℝ → ℝ}
    (ha0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < a t)
    (h : IsRefinementLimitEquilibrium a x) :
    ∃ lam : ℝ, ∀ (n : ℕ) (i : Fin (n + 1)),
      occSlope (x (tolmanGrid n i)) = lam * a (tolmanGrid n i) := by
  have hpos : ∀ n : ℕ, ∀ i : Fin (n + 1), 0 < tolmanSample a n i :=
    fun n i => ha0 _ tolmanGrid_mem_Icc
  have key : ∀ n : ℕ, ∃ lam : ℝ, ∀ i : Fin (n + 1),
      occSlope (tolmanSample x n i) = lam * tolmanSample a n i := by
    intro n
    exact ((tolman_characterization (a := tolmanSample a n)
      (x₀ := tolmanSample x n) (hpos n)).mp (h n)).2
  refine ⟨occSlope (x 0) / a 0, fun n i => ?_⟩
  obtain ⟨lamn, hlamn⟩ := key n
  have ha00 : (0 : ℝ) < a 0 :=
    ha0 0 ⟨le_refl 0, zero_le_one⟩
  have h0 := hlamn 0
  simp only [tolmanSample, tolmanGrid_zero] at h0
  have hlam : lamn = occSlope (x 0) / a 0 := by
    rw [eq_div_iff (ne_of_gt ha00)]
    exact h0.symm
  have hi := hlamn i
  simp only [tolmanSample] at hi
  rw [hlam] at hi
  exact hi

/-- **The transported characterization (the rung's headline, both
directions):** for a continuum pair `(a, x)` on `[0, 1]` with `x, a`
continuous, `x` interior, and `a` positive, the pair is a
refinement-limit equilibrium iff one global `λ` gives the slope
identity `occSlope (x t) = λ · a t` at *every* point of the domain.
Forward: the finite characterizations at all levels collapse to one
`λ` on the grids (`slope_eq_on_grid_of_refinementLimit`), and grid
agreement of two continuous functions on a dense set is agreement
everywhere. Converse: the identity at grid points is the finite
slope condition at each level, and the finite characterization's
converse (`equilibrium_of_slope_condition`) makes each sampled pair
an equilibrium. Tier T1. -/
theorem tolman_continuum_characterization {a x : ℝ → ℝ}
    (hx : ContinuousOn x (Set.Icc 0 1)) (ha : ContinuousOn a (Set.Icc 0 1))
    (hx01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < x t ∧ x t < 1)
    (ha0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < a t) :
    IsRefinementLimitEquilibrium a x ↔
      ∃ lam : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, occSlope (x t) = lam * a t := by
  constructor
  · intro h
    obtain ⟨lam, hgrid⟩ := slope_eq_on_grid_of_refinementLimit ha0 h
    refine ⟨lam, fun t ht => ?_⟩
    by_contra hne
    have hfC : ContinuousOn (fun s => occSlope (x s)) (Set.Icc 0 1) :=
      continuousOn_occSlope_comp hx hx01
    have hgC : ContinuousOn (fun s => lam * a s) (Set.Icc 0 1) :=
      continuousOn_const.mul ha
    rw [Metric.continuousOn_iff] at hfC hgC
    have hδ : (0 : ℝ) < |occSlope (x t) - lam * a t| :=
      abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨δ₁, hδ₁, hfδ⟩ := hfC t ht _ (by positivity : (0 : ℝ) <
      |occSlope (x t) - lam * a t| / 3)
    obtain ⟨δ₂, hδ₂, hgδ⟩ := hgC t ht _ (by positivity : (0 : ℝ) <
      |occSlope (x t) - lam * a t| / 3)
    obtain ⟨n, i, hi⟩ := tolmanGrid_eventually_close ht
      (show (0 : ℝ) < min δ₁ δ₂ from lt_min hδ₁ hδ₂)
    have hgi : tolmanGrid n i ∈ Set.Icc (0 : ℝ) 1 := tolmanGrid_mem_Icc
    have hdist : dist (tolmanGrid n i) t < min δ₁ δ₂ := by
      rw [Real.dist_eq, abs_sub_comm]
      exact hi
    have e1 : dist (occSlope (x (tolmanGrid n i))) (occSlope (x t)) <
        |occSlope (x t) - lam * a t| / 3 :=
      hfδ _ hgi (lt_of_lt_of_le hdist (min_le_left _ _))
    have e2 : dist (lam * a (tolmanGrid n i)) (lam * a t) <
        |occSlope (x t) - lam * a t| / 3 :=
      hgδ _ hgi (lt_of_lt_of_le hdist (min_le_right _ _))
    have e0 : occSlope (x (tolmanGrid n i)) = lam * a (tolmanGrid n i) :=
      hgrid n i
    have hlt : |occSlope (x t) - lam * a t| <
        |occSlope (x t) - lam * a t| := by
      calc |occSlope (x t) - lam * a t|
          = |(occSlope (x t) - occSlope (x (tolmanGrid n i)))
              + (lam * a (tolmanGrid n i) - lam * a t)| := by
            rw [← e0]; ring
        _ ≤ |occSlope (x t) - occSlope (x (tolmanGrid n i))|
              + |lam * a (tolmanGrid n i) - lam * a t| := abs_add_le _ _
        _ = dist (occSlope (x (tolmanGrid n i))) (occSlope (x t))
              + dist (lam * a (tolmanGrid n i)) (lam * a t) := by
            rw [Real.dist_eq, Real.dist_eq, abs_sub_comm
              (occSlope (x t)) (occSlope (x (tolmanGrid n i)))]
        _ < |occSlope (x t) - lam * a t| / 3
              + |occSlope (x t) - lam * a t| / 3 := add_lt_add e1 e2
        _ < |occSlope (x t) - lam * a t| := by linarith
    exact lt_irrefl _ hlt
  · rintro ⟨lam, hlam⟩ n
    exact equilibrium_of_slope_condition
      (fun i => ha0 _ tolmanGrid_mem_Icc)
      (fun i => hx01 _ tolmanGrid_mem_Icc) lam
      (fun i => hlam _ tolmanGrid_mem_Icc)

/-- **The pin's conclusion form (a.e.):** a refinement-limit
equilibrium's limit pair satisfies the slope identity almost
everywhere on the continuum domain at one global `λ` — the
everywhere identity of `tolman_continuum_characterization`,
restricted to the a.e. quantifier of the pin's statement. Tier T1. -/
theorem tolman_continuum_slope_ae {a x : ℝ → ℝ}
    (hx : ContinuousOn x (Set.Icc 0 1)) (ha : ContinuousOn a (Set.Icc 0 1))
    (hx01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < x t ∧ x t < 1)
    (ha0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < a t)
    (h : IsRefinementLimitEquilibrium a x) :
    ∃ lam : ℝ, ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      occSlope (x t) = lam * a t := by
  obtain ⟨lam, hlam⟩ :=
    (tolman_continuum_characterization hx ha hx01 ha0).mp h
  exact ⟨lam, ae_restrict_of_forall_mem measurableSet_Icc
    (fun t ht => hlam t ht)⟩

/-- **The product, transported:** at a continuum slope identity with
witness `λ ≠ 0`, the reciprocal slope times the weight is the one
global constant `λ⁻¹` at every point of the domain — the finite
`tolman_product` read in the limit. (Stated with the reciprocal
slope written out: the finite package's `localTemp` is a finite-seat
definition, over a `Fintype` seat.) Tier T1. -/
theorem tolman_continuum_product {a x : ℝ → ℝ} {lam : ℝ}
    (ha0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < a t)
    (hlam : ∀ t ∈ Set.Icc (0 : ℝ) 1, occSlope (x t) = lam * a t)
    (hlam0 : lam ≠ 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, (occSlope (x t))⁻¹ * a t = lam⁻¹ := by
  intro t ht
  have hai : a t ≠ 0 := ne_of_gt (ha0 t ht)
  calc (occSlope (x t))⁻¹ * a t = (lam * a t)⁻¹ * a t := by
        rw [hlam t ht]
    _ = (a t)⁻¹ * lam⁻¹ * a t := by rw [mul_inv_rev]
    _ = lam⁻¹ * ((a t)⁻¹ * a t) := by ring
    _ = lam⁻¹ := by rw [inv_mul_cancel₀ hai, mul_one]

/-- **The `λ = 0` fence, transported:** if the continuum slope
identity holds at witness `λ = 0`, the limit occupation is the
half-occupation configuration `x ≡ 1/2` on the whole domain — the
infinite-temperature configuration of the pin's form (3), in the
limit. Tier T1. -/
theorem tolman_continuum_lambda_zero {a x : ℝ → ℝ}
    (hx01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < x t ∧ x t < 1)
    (hlam : ∀ t ∈ Set.Icc (0 : ℝ) 1, occSlope (x t) = 0 * a t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, x t = 1 / 2 := by
  intro t ht
  have h0 : occSlope (x t) = 0 := by
    have := hlam t ht
    rwa [zero_mul] at this
  exact (occSlope_eq_zero_iff (hx01 t ht).1 (hx01 t ht).2).mp h0

/-- **The `λ` regimes, transported (positive side):** a positive
witness puts every limit occupation below `1/2`, with positive
reciprocal slope — the pin's form (4), first half, in the limit.
Tier T1. -/
theorem tolman_continuum_regime_pos {a x : ℝ → ℝ} {lam : ℝ}
    (hx01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < x t ∧ x t < 1)
    (ha0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < a t)
    (hlam : ∀ t ∈ Set.Icc (0 : ℝ) 1, occSlope (x t) = lam * a t)
    (hlampos : 0 < lam) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, x t < 1 / 2 ∧ 0 < (occSlope (x t))⁻¹ := by
  intro t ht
  have hsp : 0 < occSlope (x t) := by
    rw [hlam t ht]
    exact mul_pos hlampos (ha0 t ht)
  exact ⟨(occSlope_pos_iff (hx01 t ht).1 (hx01 t ht).2).mp hsp,
    inv_pos.mpr hsp⟩

/-- **The `λ` regimes, transported (negative side):** a negative
witness puts every limit occupation past `1/2`, with signed
(negative) reciprocal slope — the population-inversion side of the
pin's form (4), in the limit. Tier T1. -/
theorem tolman_continuum_regime_neg {a x : ℝ → ℝ} {lam : ℝ}
    (hx01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < x t ∧ x t < 1)
    (ha0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < a t)
    (hlam : ∀ t ∈ Set.Icc (0 : ℝ) 1, occSlope (x t) = lam * a t)
    (hlamneg : lam < 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, 1 / 2 < x t ∧ (occSlope (x t))⁻¹ < 0 := by
  intro t ht
  have hsn : occSlope (x t) < 0 := by
    rw [hlam t ht]
    exact mul_neg_of_neg_of_pos hlamneg (ha0 t ht)
  exact ⟨(occSlope_neg_iff (hx01 t ht).1 (hx01 t ht).2).mp hsn,
    inv_lt_zero'.mpr hsn⟩

/-- The slope at occupation `1/4` is `log 3` (the finite witnesses'
computation, reused for the continuum witnesses). Tier T1. -/
theorem occSlope_one_fourth : occSlope (1 / 4 : ℝ) = Real.log 3 := by
  have e2 : (1 : ℝ) - 1 / 4 = 3 / 4 := by norm_num
  have e3 : (3 / 4 : ℝ) / (1 / 4) = 3 := by norm_num
  show Real.log (1 - 1 / 4) - Real.log (1 / 4) = Real.log 3
  rw [e2, ← Real.log_div (by norm_num) (by norm_num), e3]

/-- **Continuum non-vacuity, positive side:** the constant pair
`a ≡ 1`, `x ≡ 1/4` is a refinement-limit equilibrium — at every
level its samples are the constant finite configuration, an
equilibrium by the finite characterization's converse with witness
`λ = log 3`. Tier T1. -/
theorem tolman_continuum_witness :
    IsRefinementLimitEquilibrium (fun _ => (1 : ℝ)) (fun _ => (1 / 4 : ℝ)) := by
  intro n
  exact equilibrium_of_slope_condition (a := tolmanSample (fun _ => (1 : ℝ)) n)
    (x₀ := tolmanSample (fun _ => (1 / 4 : ℝ)) n)
    (fun _ => one_pos)
    (fun _ => ⟨by show (0 : ℝ) < 1 / 4; norm_num,
      by show (1 / 4 : ℝ) < 1; norm_num⟩) (Real.log 3)
    (fun _ => by
      show occSlope (1 / 4 : ℝ) = Real.log 3 * 1
      rw [occSlope_one_fourth, mul_one])

/-- **Continuum non-vacuity, negative side:** the pair `a t = 1 + t`,
`x ≡ 1/4` is NOT a refinement-limit equilibrium: already at level
`1` (sites `0` and `1/2`) the finite characterization would force
one `λ` to satisfy both `log 3 = λ · 1` and `log 3 = λ · (3/2)`,
impossible since `log 3 > 0`. The transported characterization is
an iff with named pairs on both sides (K-TOL-VAC's discipline).
Tier T1. -/
theorem tolman_continuum_nonwitness :
    ¬ IsRefinementLimitEquilibrium (fun t => 1 + t) (fun _ => (1 / 4 : ℝ)) := by
  intro h
  have hpos : ∀ i : Fin 2, 0 < tolmanSample (fun t => 1 + t) 1 i := by
    intro i
    have hgi : tolmanGrid 1 i ∈ Set.Icc (0 : ℝ) 1 := tolmanGrid_mem_Icc
    show (0 : ℝ) < 1 + tolmanGrid 1 i
    linarith [hgi.1]
  obtain ⟨-, lam, hlam⟩ :=
    ((tolman_characterization (a := tolmanSample (fun t => 1 + t) 1)
      (x₀ := tolmanSample (fun _ => (1 / 4 : ℝ)) 1) hpos).mp (h 1))
  have g1 : tolmanGrid 1 (1 : Fin 2) = 1 / 2 := by
    simp only [tolmanGrid]
    norm_num
  have e0 := hlam 0
  have e1 := hlam 1
  simp only [tolmanSample, tolmanGrid_zero, occSlope_one_fourth] at e0
  simp only [tolmanSample, g1, occSlope_one_fourth] at e1
  norm_num at e0
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  linarith

end ThetLogos
