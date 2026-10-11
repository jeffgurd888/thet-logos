import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import ThetLogos.SchwartzSpace

/-!
# Rung 7, Prong 1 — Fréchet completeness of Schwartz space (T1)

**Goal.** Prove `CompleteSpace (SchwartzTest n)`: the Schwartz space `𝒮(ℝⁿ, ℂ)`
is complete for its seminorm topology — i.e. it is a Fréchet space. This
discharges the priced window `schwartzComplete_window` from
`ThetLogos.SchwartzSpace` (Rung 6, Price 2): Mathlib 2026 ships the
locally-convex metrizable topology but no `CompleteSpace` instance.

**Strategy** (the classical Fréchet-space argument, inside Mathlib's API).
The entourage sequence `schwartzEnt` — one seminorm ball per `N`, using the
finite sup over all indices `≤ (N, N)` — generates the uniformity
(`schwartzEnt_isCountablyGenerated`), so
`UniformSpace.complete_of_convergent_controlled_sequences` applies. A
sequence `u` controlled by `schwartzEnt` is Cauchy in every Schwartz seminorm
(`hcauchy`). For each derivative order `m'`, the maps
`x ↦ iteratedFDeriv ℝ m' (u i) x` are uniformly Cauchy in `x` (the `(0, m')`
seminorm bounds them uniformly), hence converge — pointwise to `D m'`,
uniformly by `hunif`. The uniform-limit-of-derivatives lemma
`hasFDerivAt_of_tendstoUniformly` identifies `D (m+1)` as the derivative of
`D m` (`hHas`), so the scalar limit `g` built from `D 0` is smooth with
`iteratedFDeriv ℝ m' g = D m'` (`hderiv`, `hsmooth`). The seminorm estimates
pass to the limit (`le_of_tendsto`), so `g` satisfies the Schwartz decay
bounds (`hdecay`) and `u → s` in every seminorm, i.e. in the Schwartz
topology (`WithSeminorms.tendsto_nhds`).

**Tiers.** Everything in this file is **T1** (proved, zero sorrys). Axiom
footprint is Mathlib's standard three (`propext`, `Classical.choice`,
`Quot.sound`); see `#print axioms` at the end. No 4D interacting QFT, no mass
gap, nothing about the Yang–Mills target beyond this analytic prerequisite.
-/

namespace ThetLogos

open scoped SchwartzMap ContDiff Uniformity
open Filter Topology

/-- The controlling entourage sequence for Schwartz space: `schwartzEnt n N`
is the `(N+1)⁻¹`-ball of the finite sup of all seminorms with indices
`≤ (N, N)`. -/
private def schwartzEnt (n N : ℕ) : Set (SchwartzTest n × SchwartzTest n) :=
  {pr : SchwartzTest n × SchwartzTest n |
    ((Finset.Iic (N, N)).sup (schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ)) (pr.1 - pr.2)
      < ((N : ℝ) + 1)⁻¹}

/-- **T1:** the uniformity has the standard comap basis from the seminorm
family's zero-basis. -/
private theorem schwartz_uniformity_hasBasis (n : ℕ) :
    (𝓤 (SchwartzTest n)).HasBasis (fun sr : Finset (ℕ × ℕ) × ℝ => 0 < sr.2)
      (fun sr => (fun pr : SchwartzTest n × SchwartzTest n => pr.2 - pr.1) ⁻¹'
        ((sr.1.sup (schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ)).ball 0 sr.2)) := by
  rw [uniformity_eq_comap_nhds_zero]
  exact Filter.HasBasis.comap _
    (schwartz_withSeminorms ℝ (Fin n → ℝ) ℂ).hasBasis_zero_ball

/-- **T1:** each `schwartzEnt n N` is a uniformity entourage. -/
private theorem schwartzEnt_mem (n N : ℕ) : schwartzEnt n N ∈ 𝓤 (SchwartzTest n) := by
  have hball : (((Finset.Iic (N, N)).sup
      (schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ)).ball 0 (((N : ℝ) + 1)⁻¹))
      ∈ 𝓝 (0 : SchwartzTest n) := by
    rw [(schwartz_withSeminorms ℝ (Fin n → ℝ) ℂ).hasBasis_zero_ball.mem_iff]
    exact ⟨(Finset.Iic (N, N), ((N : ℝ) + 1)⁻¹), by positivity, le_rfl⟩
  have hpre : (fun pr : SchwartzTest n × SchwartzTest n => pr.2 - pr.1) ⁻¹'
      (((Finset.Iic (N, N)).sup (schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ)).ball
        0 (((N : ℝ) + 1)⁻¹)) ∈ 𝓤 (SchwartzTest n) := by
    rw [uniformity_eq_comap_nhds_zero]
    exact Filter.preimage_mem_comap hball
  have heq : (fun pr : SchwartzTest n × SchwartzTest n => pr.2 - pr.1) ⁻¹'
      (((Finset.Iic (N, N)).sup (schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ)).ball
        0 (((N : ℝ) + 1)⁻¹))
      = schwartzEnt n N := by
    ext ⟨a, b⟩
    simp only [schwartzEnt, Set.mem_preimage, Set.mem_ofPred_eq,
      Seminorm.mem_ball_zero]
    rw [show a - b = -(b - a) by abel, map_neg_eq_map]
  rw [heq] at hpre
  exact hpre

/-- **T1:** the `schwartzEnt` sequence is a (countable) basis of the
uniformity. -/
private theorem schwartzEnt_hasBasis (n : ℕ) :
    (𝓤 (SchwartzTest n)).HasBasis (fun _ : ℕ => True) (schwartzEnt n) := by
  constructor
  intro V
  constructor
  · intro hV
    obtain ⟨⟨F, r⟩, hr, hsub⟩ :=
      (schwartz_uniformity_hasBasis n).mem_iff.mp hV
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (r⁻¹)
    set N := max (F.sup (fun m => m.1 + m.2)) N₀ with hNdef
    refine ⟨N, trivial, ?_⟩
    intro pr hpr
    apply hsub
    show pr.2 - pr.1 ∈
      ((F.sup (schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ)).ball 0 r)
    rw [Seminorm.mem_ball_zero]
    have hle : (F.sup (schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ)) (pr.2 - pr.1)
        ≤ ((N : ℝ) + 1)⁻¹ := by
      have hle_sup : (F.sup (schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ))
          ≤ ((Finset.Iic (N, N)).sup (schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ)) := by
        apply Finset.sup_mono
        intro m hm
        rw [Finset.mem_Iic]
        have h1 : m.1 ≤ F.sup (fun m => m.1 + m.2) :=
          le_trans (Nat.le_add_right _ _)
            (Finset.le_sup (f := fun m : ℕ × ℕ => m.1 + m.2) (b := m) hm)
        have h2 : m.2 ≤ F.sup (fun m => m.1 + m.2) :=
          le_trans (Nat.le_add_left _ _)
            (Finset.le_sup (f := fun m : ℕ × ℕ => m.1 + m.2) (b := m) hm)
        have h3 : F.sup (fun m => m.1 + m.2) ≤ N := by
          rw [hNdef]; exact le_max_left _ _
        exact Prod.mk_le_mk.mpr ⟨le_trans h1 h3, le_trans h2 h3⟩
      rw [Seminorm.le_def] at hle_sup
      have h2 := hle_sup (pr.2 - pr.1)
      simp only [schwartzEnt, Set.mem_ofPred_eq] at hpr
      have h3 : ((Finset.Iic (N, N)).sup
          (schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ)) (pr.2 - pr.1)
          ≤ ((N : ℝ) + 1)⁻¹ := by
        have e : pr.2 - pr.1 = -(pr.1 - pr.2) := by abel
        rw [e, map_neg_eq_map]
        exact le_of_lt hpr
      linarith [h2, h3]
    have hrN : (((N : ℝ) + 1)⁻¹) < r := by
      have hle2 : (N₀ : ℝ) ≤ (N : ℝ) := by
        rw [hNdef]
        exact_mod_cast le_max_right _ _
      have h1 : r⁻¹ < ((N : ℝ) + 1) := by
        have hlt : (N₀ : ℝ) < (N : ℝ) + 1 := by linarith
        linarith [hN₀]
      have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have h := (inv_lt_inv₀ hpos (inv_pos.mpr hr)).mpr h1
      rwa [inv_inv] at h
    linarith [hle, hrN]
  · rintro ⟨N, _, hsub⟩
    exact mem_of_superset (schwartzEnt_mem n N) hsub

/-- **T1:** the Schwartz uniformity is countably generated. -/
private instance schwartzEnt_isCountablyGenerated (n : ℕ) :
    IsCountablyGenerated (𝓤 (SchwartzTest n)) :=
  Filter.HasBasis.isCountablyGenerated (schwartzEnt_hasBasis n)

/-- **T1:** a sequence controlled by `schwartzEnt` converges in Schwartz
space. This is the analytic heart: Cauchy in all seminorms → uniform
convergence of all derivatives → smooth Schwartz limit. -/
private theorem schwartzEnt_tendsto {n : ℕ} {u : ℕ → SchwartzTest n}
    (hu : ∀ N m k : ℕ, N ≤ m → N ≤ k → (u m, u k) ∈ schwartzEnt n N) :
    ∃ s : SchwartzTest n, Tendsto u atTop (𝓝 s) := by
  -- Step 1: controlled → Cauchy in every Schwartz seminorm.
  have hcauchy : ∀ k m' : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ i j, N ≤ i → N ≤ j →
      SchwartzMap.seminorm ℂ k m' (u i - u j) < ε := by
    intro k m' ε hε
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (ε⁻¹)
    refine ⟨max (max k m') N₀, fun i j hi hj => ?_⟩
    set M := max (max k m') N₀ with hM
    have hmem := hu M i j hi hj
    simp only [schwartzEnt, Set.mem_ofPred_eq] at hmem
    have hle : SchwartzMap.seminorm ℝ k m' ((u i, u j).1 - (u i, u j).2)
        ≤ ((M : ℝ) + 1)⁻¹ := by
      have h1 : SchwartzMap.seminorm ℝ k m'
          ≤ ((Finset.Iic (M, M)).sup (schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ)) := by
        rw [← SchwartzMap.schwartzSeminormFamily_apply]
        refine Finset.le_sup (Finset.mem_Iic.mpr (Prod.mk_le_mk.mpr ⟨?_, ?_⟩))
        · exact le_trans (le_max_left k m') (le_max_left _ _)
        · exact le_trans (le_max_right k m') (le_max_left _ _)
      rw [Seminorm.le_def] at h1
      have h2 := h1 ((u i, u j).1 - (u i, u j).2)
      have h3 : ((Finset.Iic (M, M)).sup
          (schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ)) ((u i, u j).1 - (u i, u j).2)
          < ((M : ℝ) + 1)⁻¹ := hmem
      linarith [h2, h3]
    have hrw : SchwartzMap.seminorm ℂ k m' (u i - u j)
        = SchwartzMap.seminorm ℝ k m' ((u i, u j).1 - (u i, u j).2) := rfl
    rw [hrw]
    have h4 : (((M : ℝ) + 1)⁻¹) < ε := by
      have hle2 : (N₀ : ℝ) ≤ (M : ℝ) := by
        rw [hM]; exact_mod_cast le_max_right _ _
      have h1 : ε⁻¹ < ((M : ℝ) + 1) := by
        have hlt : (N₀ : ℝ) < (M : ℝ) + 1 := by linarith
        linarith [hN₀]
      have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
      have h := (inv_lt_inv₀ hpos (inv_pos.mpr hε)).mpr h1
      rwa [inv_inv] at h
    linarith [hle, h4]
  -- Step 2: iterated derivatives are linear in the function.
  have hsub : ∀ (m' i j : ℕ) (x : Fin n → ℝ),
      iteratedFDeriv ℝ m' (((u i - u j : SchwartzTest n)) : (Fin n → ℝ) → ℂ) x
        = iteratedFDeriv ℝ m' (u i : (Fin n → ℝ) → ℂ) x
          - iteratedFDeriv ℝ m' (u j : (Fin n → ℝ) → ℂ) x := by
    intro m' i j x
    have hco : (((u i - u j : SchwartzTest n)) : (Fin n → ℝ) → ℂ)
        = (u i : (Fin n → ℝ) → ℂ) - (u j : (Fin n → ℝ) → ℂ) := rfl
    have h1 : ContDiffAt ℝ m' (u i : (Fin n → ℝ) → ℂ) x :=
      ContDiffAt.of_le ((u i).smooth'.contDiffAt) (by simp)
    have h2 : ContDiffAt ℝ m' (-(u j : (Fin n → ℝ) → ℂ)) x :=
      ContDiffAt.of_le (((u j).smooth'.neg).contDiffAt) (by simp)
    rw [hco, sub_eq_add_neg, iteratedFDeriv_add_apply h1 h2,
      iteratedFDeriv_neg_apply, sub_eq_add_neg]
  -- Step 3: for each derivative order, the derivatives converge pointwise.
  have hlim : ∀ m' : ℕ, ∃ D : (Fin n → ℝ) →
      ContinuousMultilinearMap ℝ (fun _ : Fin m' => Fin n → ℝ) ℂ,
      ∀ x, Tendsto (fun i => iteratedFDeriv ℝ m' (u i : (Fin n → ℝ) → ℂ) x)
        atTop (𝓝 (D x)) := by
    intro m'
    have hcau : ∀ x : Fin n → ℝ,
        CauchySeq (fun i => iteratedFDeriv ℝ m' (u i : (Fin n → ℝ) → ℂ) x) := by
      intro x
      rw [cauchySeq_iff]
      intro V hV
      obtain ⟨ε, hε, hsubV⟩ := Metric.mem_uniformity_dist.mp hV
      obtain ⟨N, hN⟩ := hcauchy 0 m' ε hε
      refine ⟨N, fun k hk l hl => hsubV ?_⟩
      show dist (iteratedFDeriv ℝ m' (u k : (Fin n → ℝ) → ℂ) x)
        (iteratedFDeriv ℝ m' (u l : (Fin n → ℝ) → ℂ) x) < ε
      rw [dist_eq_norm, ← hsub m' k l x]
      have e2 := SchwartzMap.le_seminorm ℂ 0 m' (u k - u l) x
      simp only [pow_zero, one_mul] at e2
      exact lt_of_le_of_lt e2 (hN k l hk hl)
    choose D hD using fun x => cauchySeq_tendsto_of_complete (hcau x)
    exact ⟨D, hD⟩
  choose D hD using hlim
  -- Step 4: the convergence of derivatives is uniform in `x`.
  have hunif : ∀ m' : ℕ, TendstoUniformly
      (fun i (x : Fin n → ℝ) => iteratedFDeriv ℝ m' (u i : (Fin n → ℝ) → ℂ) x)
      (D m') atTop := by
    intro m'
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy 0 m' (ε / 2) (half_pos hε)
    filter_upwards [eventually_ge_atTop N] with i hi x
    have hconv : Tendsto (fun j => dist
        (iteratedFDeriv ℝ m' (u j : (Fin n → ℝ) → ℂ) x)
        (iteratedFDeriv ℝ m' (u i : (Fin n → ℝ) → ℂ) x)) atTop
        (𝓝 (dist (D m' x) (iteratedFDeriv ℝ m' (u i : (Fin n → ℝ) → ℂ) x))) :=
      (hD m' x).dist tendsto_const_nhds
    have hev : ∀ᶠ j in atTop, dist
        (iteratedFDeriv ℝ m' (u j : (Fin n → ℝ) → ℂ) x)
        (iteratedFDeriv ℝ m' (u i : (Fin n → ℝ) → ℂ) x) ≤ ε / 2 := by
      filter_upwards [eventually_ge_atTop N] with j hj
      rw [dist_eq_norm, ← hsub m' j i x]
      have e2 := SchwartzMap.le_seminorm ℂ 0 m' (u j - u i) x
      simp only [pow_zero, one_mul] at e2
      exact le_trans e2 (le_of_lt (hN j i hj hi))
    have hle := le_of_tendsto hconv hev
    linarith
  -- Step 5: the scalar limit function, via the 0-th derivative.
  set g : (Fin n → ℝ) → ℂ :=
    fun x => (continuousMultilinearCurryFin0 ℝ (Fin n → ℝ) ℂ) (D 0 x) with hg
  -- Step 6: each `D m` is differentiable with derivative `D (m+1)`,
  -- by the uniform-limit-of-derivatives lemma.
  have hHas : ∀ (m : ℕ) (x : Fin n → ℝ), HasFDerivAt (D m)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Fin n → ℝ) ℂ)
        (D (m + 1) x)) x := by
    intro m x
    refine hasFDerivAt_of_tendstoUniformly (l := atTop)
      (f := fun i (y : Fin n → ℝ) => iteratedFDeriv ℝ m (u i : (Fin n → ℝ) → ℂ) y)
      (g := D m)
      (f' := fun i (y : Fin n → ℝ) =>
        fderiv ℝ (fun z => iteratedFDeriv ℝ m (u i : (Fin n → ℝ) → ℂ) z) y)
      (g' := fun y => (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (m + 1) => Fin n → ℝ) ℂ) (D (m + 1) y)) ?_ ?_ ?_ x
    · rw [Metric.tendstoUniformly_iff]
      intro ε hε
      have hU := (Metric.tendstoUniformly_iff.mp (hunif (m + 1))) ε hε
      filter_upwards [hU] with i hi y
      have hfi : fderiv ℝ (fun z => iteratedFDeriv ℝ m (u i : (Fin n → ℝ) → ℂ) z) y
          = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Fin n → ℝ) ℂ)
            (iteratedFDeriv ℝ (m + 1) (u i : (Fin n → ℝ) → ℂ) y) := rfl
      show dist ((continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (m + 1) => Fin n → ℝ) ℂ) (D (m + 1) y))
        (fderiv ℝ (fun z => iteratedFDeriv ℝ m (u i : (Fin n → ℝ) → ℂ) z) y) < ε
      rw [hfi, LinearIsometryEquiv.dist_map]
      exact hi y
    · intro i y
      exact ((((u i).smooth ⊤).differentiable_iteratedFDeriv
        (mod_cast ENat.natCast_lt_top m)).differentiableAt).hasFDerivAt
    · intro y
      exact hD m y
  -- Step 7: the iterated derivatives of `g` are exactly the `D m`.
  have hderiv : ∀ m' : ℕ, iteratedFDeriv ℝ m' g = D m' := by
    intro m'
    induction m' with
    | zero =>
      funext x
      have h0 : iteratedFDeriv ℝ 0 g x
          = (continuousMultilinearCurryFin0 ℝ (Fin n → ℝ) ℂ).symm (g x) := by
        rw [iteratedFDeriv_zero_eq_comp]; rfl
      rw [h0, hg]
      show (continuousMultilinearCurryFin0 ℝ (Fin n → ℝ) ℂ).symm
        ((continuousMultilinearCurryFin0 ℝ (Fin n → ℝ) ℂ) (D 0 x)) = D 0 x
      exact (continuousMultilinearCurryFin0 ℝ (Fin n → ℝ) ℂ).symm_apply_apply (D 0 x)
    | succ m ih =>
      have h1 : iteratedFDeriv ℝ (m + 1) g
          = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Fin n → ℝ) ℂ).symm
            ∘ fderiv ℝ (D m) := by
        rw [iteratedFDeriv_succ_eq_comp_left, ih]
      have h2 : fderiv ℝ (D m)
          = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Fin n → ℝ) ℂ)
            ∘ D (m + 1) := by
        funext y
        have h3 := hHas m y
        rw [h3.fderiv]
        rfl
      rw [h1, h2]
      funext y
      simp only [Function.comp_apply]
      exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (m + 1) => Fin n → ℝ) ℂ).symm_apply_apply (D (m + 1) y)
  -- Step 8: `g` is smooth.
  have hsmooth : ContDiff ℝ ∞ g := by
    have h := contDiff_of_differentiable_iteratedFDeriv (𝕜 := ℝ) (n := (⊤ : ℕ∞))
      (f := g) (fun m _ => by rw [hderiv m]; exact fun x => (hHas m x).differentiableAt)
    exact h
  -- Step 9: the Schwartz decay estimates pass to the limit.
  have hdecay : ∀ k m' : ℕ, ∃ C : ℝ, ∀ x : Fin n → ℝ,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ m' g x‖ ≤ C := by
    intro k m'
    obtain ⟨N, hN⟩ := hcauchy k m' 1 one_pos
    refine ⟨SchwartzMap.seminorm ℂ k m' (u N) + 1, fun x => ?_⟩
    rw [hderiv m']
    have hnorm : Tendsto
        (fun i => ‖x‖ ^ k * ‖iteratedFDeriv ℝ m' (u i : (Fin n → ℝ) → ℂ) x‖)
        atTop (𝓝 (‖x‖ ^ k * ‖D m' x‖)) :=
      tendsto_const_nhds.mul (hD m' x).norm
    apply le_of_tendsto hnorm
    filter_upwards [eventually_ge_atTop N] with i hi
    have htri : SchwartzMap.seminorm ℂ k m' (u i)
        ≤ SchwartzMap.seminorm ℂ k m' (u i - u N)
          + SchwartzMap.seminorm ℂ k m' (u N) := by
      have h2 := map_add_le_add (SchwartzMap.seminorm ℂ k m') (u i - u N) (u N)
      rwa [show (u i - u N) + u N = u i from by abel] at h2
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ m' (u i : (Fin n → ℝ) → ℂ) x‖
          ≤ SchwartzMap.seminorm ℂ k m' (u i) :=
          SchwartzMap.le_seminorm ℂ k m' (u i) x
        _ ≤ SchwartzMap.seminorm ℂ k m' (u N) + 1 := by
          have h1 := hN i N hi le_rfl
          linarith [htri]
  -- Step 10: the limit is a Schwartz function.
  set s : SchwartzTest n := ⟨g, hsmooth, hdecay⟩ with hs_def
  have hs_deriv : ∀ m', iteratedFDeriv ℝ m' (s : (Fin n → ℝ) → ℂ) = D m' := by
    intro m'
    have hco : (s : (Fin n → ℝ) → ℂ) = g := rfl
    rw [hco]; exact hderiv m'
  -- Step 11: `u → s` in every seminorm, hence in the Schwartz topology.
  have hconv : Tendsto u atTop (𝓝 s) := by
    rw [(schwartz_withSeminorms ℝ (Fin n → ℝ) ℂ).tendsto_nhds]
    rintro ⟨k, m'⟩ ε hε
    rw [SchwartzMap.schwartzSeminormFamily_apply]
    obtain ⟨N, hN⟩ := hcauchy k m' (ε / 2) (half_pos hε)
    filter_upwards [eventually_ge_atTop N] with i hi
    have hle : SchwartzMap.seminorm ℝ k m' (u i - s) ≤ ε / 2 := by
      apply SchwartzMap.seminorm_le_bound ℝ k m' (u i - s) (le_of_lt (half_pos hε))
      intro x
      have hdiff : ∀ y : Fin n → ℝ,
          iteratedFDeriv ℝ m' (((u i - s : SchwartzTest n)) : (Fin n → ℝ) → ℂ) y
            = iteratedFDeriv ℝ m' (u i : (Fin n → ℝ) → ℂ) y - D m' y := by
        intro y
        have hco : (((u i - s : SchwartzTest n)) : (Fin n → ℝ) → ℂ)
            = (u i : (Fin n → ℝ) → ℂ) - (s : (Fin n → ℝ) → ℂ) := rfl
        have h1 : ContDiffAt ℝ m' (u i : (Fin n → ℝ) → ℂ) y :=
          ContDiffAt.of_le ((u i).smooth'.contDiffAt) (by simp)
        have h2 : ContDiffAt ℝ m' (-(s : (Fin n → ℝ) → ℂ)) y :=
          ContDiffAt.of_le (((s.smooth').neg).contDiffAt) (by simp)
        rw [hco, sub_eq_add_neg, iteratedFDeriv_add_apply h1 h2,
          iteratedFDeriv_neg_apply, hs_deriv m', sub_eq_add_neg]
      rw [hdiff x]
      have hnorm : Tendsto
          (fun j => ‖x‖ ^ k * ‖iteratedFDeriv ℝ m' (u i : (Fin n → ℝ) → ℂ) x
            - iteratedFDeriv ℝ m' (u j : (Fin n → ℝ) → ℂ) x‖) atTop
          (𝓝 (‖x‖ ^ k * ‖iteratedFDeriv ℝ m' (u i : (Fin n → ℝ) → ℂ) x - D m' x‖)) := by
        have h1 : Tendsto (fun j => iteratedFDeriv ℝ m' (u i : (Fin n → ℝ) → ℂ) x
            - iteratedFDeriv ℝ m' (u j : (Fin n → ℝ) → ℂ) x) atTop
            (𝓝 (iteratedFDeriv ℝ m' (u i : (Fin n → ℝ) → ℂ) x - D m' x)) :=
          tendsto_const_nhds.sub (hD m' x)
        exact tendsto_const_nhds.mul h1.norm
      apply le_of_tendsto hnorm
      filter_upwards [eventually_ge_atTop N] with j hj
      have e1 : iteratedFDeriv ℝ m' (u i : (Fin n → ℝ) → ℂ) x
          - iteratedFDeriv ℝ m' (u j : (Fin n → ℝ) → ℂ) x
          = iteratedFDeriv ℝ m'
            ((((u i - u j : SchwartzTest n))) : (Fin n → ℝ) → ℂ) x :=
        (hsub m' i j x).symm
      rw [e1]
      have e2 := SchwartzMap.le_seminorm ℂ k m' (u i - u j) x
      have e3 := hN i j hi hj
      exact le_of_lt (lt_of_le_of_lt e2 e3)
    have hrw : SchwartzMap.seminorm ℝ k m' (u i - s)
        = SchwartzMap.seminorm ℂ k m' (u i - s) := rfl
    rw [hrw] at hle
    linarith
  exact ⟨s, hconv⟩

/-- **T1:** Schwartz space `𝒮(ℝⁿ, ℂ)` is complete — a Fréchet space.
Proved via `UniformSpace.complete_of_convergent_controlled_sequences`
with the entourage sequence `schwartzEnt`. -/
theorem schwartzComplete (n : ℕ) : CompleteSpace (SchwartzTest n) :=
  UniformSpace.complete_of_convergent_controlled_sequences (schwartzEnt n)
    (fun N => schwartzEnt_mem n N) (fun _ hu => schwartzEnt_tendsto hu)

/-- **T1:** the completeness as a typeclass instance. -/
instance schwartzCompleteSpace (n : ℕ) : CompleteSpace (SchwartzTest n) :=
  schwartzComplete n

/-- **T1:** discharges the priced window `schwartzComplete_window`
(Rung 6, Price 2): Fréchet completeness is now proved, not priced. -/
theorem schwartzComplete_discharge (n : ℕ) : schwartzComplete_window n :=
  schwartzComplete n

#print axioms schwartzComplete
#print axioms schwartzCompleteSpace
#print axioms schwartzComplete_discharge

end ThetLogos
