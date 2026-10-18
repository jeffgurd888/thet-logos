import ThetLogos.FockPackagingBos
import ThetLogos.LorentzContinuity

/-!
# ThetLogos.FockLorentzBos — FOCK-LEVEL LORENTZ STRONG CONTINUITY,
# bosonic half (unlock chain item 2, ratified 2026-10-18)

The Lorentz half of the Rung 7 strong-continuity window at the
Fock level. `FockPackagingBos` packaged the one-particle Poincaré
action `shellU1` through second quantization Γ to the bosonic
limit Fock space `BosonicFockLim`, and transported strong
continuity of the **translation** subgroup only; the Lorentz
brick (`LorentzContinuity`, 28 T1) discharged the one-particle
Lorentz input and named the Fock-level transport as its fenced
remainder ("a new per-statistic proof"). This module is that
proof for the bosonic statistic.

## What is proved (T1)

* `gammaFockU1_lorentz_tendsto`: for every `z : BosonicFockLim`,
  `Λ ↦ gammaFockU1 m hm ⟨0, Λ⟩ z` tends to `z` as `Λ → 1` in
  `RestrictedLorentz` (topology of pointwise action convergence,
  from `LorentzContinuity`).
* `gammaFockU1_lorentz_tendsto_at`: the same at every `Λ₀`, by
  the group law and `tendsto_restricted_inv_mul`.

## Route

The translation transport of `FockPackagingBos`, generalized:
the kernel-continuity lemma there
(`gammaKernelRect_tendsto_of_tendsto_filter`) is already
filter-general, so the whole chain — entry continuity, diagonal
kernel, basis vectors (`2 - 2 Re γ`), finite-particle squeeze,
ε/3 extension by unitarity — replays with the one-particle input
`shellU1_translation_tendsto` replaced by
`shellU1_lorentz_tendsto` and the translation filter `𝓝 0` on
`Minkowski` replaced by `𝓝 1` on `RestrictedLorentz`. The
finite-particle vectors `DomLim` are the dense class; no tensor
power of the one-particle space is ever formed — the Γ kernel
*is* the finite tensor data, in the concrete basis `shellONB`.

## Fences

* Free bosonic Fock space only; no interacting statement.
* Subgroup-wise: no joint topology on `RPoincare` is introduced;
  translations and Lorentz stand separately, as at the
  one-particle level.
* The fermionic half lives in `FockLorentzFerm.lean`.
-/

namespace ThetLogos

open scoped InnerProductSpace
open scoped Matrix
open Filter Topology

/-- Entry continuity under the Lorentz subgroup (T1): the
one-particle matrix entries of the shell basis are continuous at
the identity of `RestrictedLorentz`, from the discharged
one-particle Lorentz strong continuity. -/
theorem Umat_lorentz_tendsto (m : ℝ) (hm : 0 < m) (i j : ℕ) :
    Tendsto (fun Λ : RestrictedLorentz =>
        Umat m hm (shellU1 m hm ⟨0, Λ⟩) i j) (𝓝 1)
      (𝓝 (Umat m hm 1 i j)) := by
  have h : Tendsto (fun Λ : RestrictedLorentz =>
        ⟪shellONB m hm i, shellU1 m hm ⟨0, Λ⟩ (shellONB m hm j)⟫_ℂ)
        (𝓝 1) (𝓝 ⟪shellONB m hm i, shellONB m hm j⟫_ℂ) :=
    Filter.Tendsto.inner tendsto_const_nhds
      (shellU1_lorentz_tendsto m hm (shellONB m hm j))
  exact h

/-- The diagonal kernel is continuous at the identity of the
Lorentz subgroup, with value `1` (T1): at a fixed configuration
the kernel is a fixed finite permanent in the entries. -/
theorem gammaKernelLim_diag_lorentz_tendsto (m : ℝ) (hm : 0 < m)
    (c : ConfigLim) :
    Tendsto (fun Λ : RestrictedLorentz =>
        gammaKernelLim m hm (shellU1 m hm ⟨0, Λ⟩) c c) (𝓝 1)
      (𝓝 1) := by
  obtain ⟨d, c₀, hc⟩ := config_factor c
  have heq : ∀ Λ : RestrictedLorentz,
      gammaKernelLim m hm (shellU1 m hm ⟨0, Λ⟩) c c
        = gammaKernelRect (fun i j : Fin d =>
            Umat m hm (shellU1 m hm ⟨0, Λ⟩) i.val j.val) c₀ c₀ := by
    intro Λ
    rw [← hc]
    show gammaKernelLimOf (Umat m hm (shellU1 m hm ⟨0, Λ⟩))
        (configEmbLim d c₀) (configEmbLim d c₀) = _
    exact gammaKernelLimOf_configEmbLim _ d d c₀ c₀
  have hval : gammaKernelRect (fun i j : Fin d =>
        Umat m hm (1 : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) i.val j.val)
        c₀ c₀ = 1 := by
    have h1 : gammaKernelLim m hm
          (1 : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm)
          (configEmbLim d c₀) (configEmbLim d c₀)
        = gammaKernelRect (fun i j : Fin d =>
            Umat m hm (1 : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm)
              i.val j.val) c₀ c₀ := by
      show gammaKernelLimOf (Umat m hm 1) (configEmbLim d c₀)
        (configEmbLim d c₀) = _
      exact gammaKernelLimOf_configEmbLim _ d d c₀ c₀
    rw [← h1, gammaKernelLim_one, if_pos rfl]
  have hlim : Tendsto (fun Λ : RestrictedLorentz => gammaKernelRect
        (fun i j : Fin d =>
          Umat m hm (shellU1 m hm ⟨0, Λ⟩) i.val j.val) c₀ c₀) (𝓝 1)
      (𝓝 (gammaKernelRect (fun i j : Fin d =>
          Umat m hm (1 : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm)
            i.val j.val) c₀ c₀)) :=
    gammaKernelRect_tendsto_of_tendsto_filter _ _
      (fun i j => Umat_lorentz_tendsto m hm i.val j.val) c₀ c₀
  rw [hval] at hlim
  exact Filter.Tendsto.congr (fun Λ => (heq Λ).symm) hlim

/-- The packaged action on a basis vector, along a Lorentz
parameter (T1). -/
theorem gammaFockU1_boseELim_lorentz (m : ℝ) (hm : 0 < m)
    (Λ : RestrictedLorentz) (c : ConfigLim) :
    gammaFockU1 m hm ⟨0, Λ⟩ (boseELim c)
      = colVec m hm (shellU1 m hm ⟨0, Λ⟩) c := by
  show gammaFock m hm (shellU1 m hm ⟨0, Λ⟩) (boseELim c) = _
  rw [gammaFock_apply]
  exact gammaIsometry_boseELim m hm _ c

/-- Basis vectors are strongly continuous under the packaged
Lorentz action (T1): the squared distance is `2 - 2 Re γ`. -/
theorem gammaFockU1_basis_lorentz_tendsto (m : ℝ) (hm : 0 < m)
    (c : ConfigLim) :
    Tendsto (fun Λ : RestrictedLorentz =>
        ‖gammaFockU1 m hm ⟨0, Λ⟩ (boseELim c) - boseELim c‖)
      (𝓝 1) (𝓝 0) := by
  have hnorme : ‖boseELim c‖ = 1 := boseELim_orthonormal.1 c
  have hnorm : ∀ Λ : RestrictedLorentz,
      ‖gammaFockU1 m hm ⟨0, Λ⟩ (boseELim c) - boseELim c‖ ^ 2
        = 2 - 2 * (gammaKernelLim m hm (shellU1 m hm ⟨0, Λ⟩) c c).re := by
    intro Λ
    rw [gammaFockU1_boseELim_lorentz]
    have hnormV : ‖colVec m hm (shellU1 m hm ⟨0, Λ⟩) c‖ = 1 := by
      calc ‖colVec m hm (shellU1 m hm ⟨0, Λ⟩) c‖
          = ‖gammaIsometry m hm (shellU1 m hm ⟨0, Λ⟩)
              (boseELim c)‖ := by rw [gammaIsometry_boseELim]
        _ = ‖boseELim c‖ := LinearIsometry.norm_map _ _
        _ = 1 := hnorme
    calc ‖colVec m hm (shellU1 m hm ⟨0, Λ⟩) c - boseELim c‖ ^ 2
        = ‖colVec m hm (shellU1 m hm ⟨0, Λ⟩) c‖ ^ 2
          - 2 * (⟪colVec m hm (shellU1 m hm ⟨0, Λ⟩) c,
              boseELim c⟫_ℂ).re
          + ‖boseELim c‖ ^ 2 := norm_sub_sq (𝕜 := ℂ) _ _
      _ = 1 - 2 * (star (gammaKernelLim m hm
              (shellU1 m hm ⟨0, Λ⟩) c c)).re + 1 := by
          rw [inner_colVec_boseELim, hnormV, hnorme]
          ring
      _ = 2 - 2 * (gammaKernelLim m hm (shellU1 m hm ⟨0, Λ⟩)
            c c).re := by
          have hre : ∀ z : ℂ, (star z).re = z.re := fun z => by simp
          rw [hre]
          ring
  have hsq : Tendsto (fun Λ : RestrictedLorentz =>
        ‖gammaFockU1 m hm ⟨0, Λ⟩ (boseELim c) - boseELim c‖ ^ 2)
      (𝓝 1) (𝓝 0) := by
    have hre' : Tendsto (fun Λ : RestrictedLorentz =>
        (gammaKernelLim m hm (shellU1 m hm ⟨0, Λ⟩) c c).re)
          (𝓝 1) (𝓝 1) := by
      have h := (Complex.continuous_re.tendsto (1 : ℂ)).comp
        (gammaKernelLim_diag_lorentz_tendsto m hm c)
      exact h.congr (fun Λ => rfl)
    have key : Tendsto (fun Λ : RestrictedLorentz => 2 - 2
        * (gammaKernelLim m hm (shellU1 m hm ⟨0, Λ⟩) c c).re)
          (𝓝 1) (𝓝 0) := by
      have h2 : Tendsto (fun Λ : RestrictedLorentz => (2 : ℝ) - 2
            * (gammaKernelLim m hm (shellU1 m hm ⟨0, Λ⟩) c c).re)
          (𝓝 1) (𝓝 ((2 : ℝ) - 2 * 1)) :=
        tendsto_const_nhds.sub (tendsto_const_nhds.mul hre')
      have h3 : (2 : ℝ) - 2 * 1 = 0 := by norm_num
      rwa [h3] at h2
    exact Filter.Tendsto.congr (fun Λ => (hnorm Λ).symm) key
  have hfin := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  rw [Real.sqrt_zero] at hfin
  exact hfin.congr (fun Λ => Real.sqrt_sq (norm_nonneg _))

/-- Finite-particle vectors are strongly continuous under the
packaged Lorentz action (T1): the distance is squeezed by a
finite sum of basis distances. -/
theorem gammaFockU1_dom_lorentz_tendsto (m : ℝ) (hm : 0 < m)
    (u : DomLim) :
    Tendsto (fun Λ : RestrictedLorentz =>
        ‖gammaFockU1 m hm ⟨0, Λ⟩ (u : BosonicFockLim)
          - (u : BosonicFockLim)‖) (𝓝 1) (𝓝 0) := by
  obtain ⟨φ, rfl⟩ : ∃ φ, bosEquivLim φ = u :=
    ⟨bosReprLim u, LinearEquiv.apply_symm_apply bosEquivLim u⟩
  refine squeeze_zero
    (g := fun Λ : RestrictedLorentz => ∑ c ∈ φ.support, ‖φ c‖
      * ‖gammaFockU1 m hm ⟨0, Λ⟩ (boseELim c) - boseELim c‖)
    (fun Λ => norm_nonneg _) (fun Λ => ?_) ?_
  · have hΓ : gammaFockU1 m hm ⟨0, Λ⟩
          ((bosEquivLim φ : DomLim) : BosonicFockLim)
        = Finsupp.linearCombination ℂ
            (colVec m hm (shellU1 m hm ⟨0, Λ⟩)) φ := by
      show gammaFock m hm (shellU1 m hm ⟨0, Λ⟩)
          ((bosEquivLim φ : DomLim) : BosonicFockLim) = _
      rw [gammaFock_apply, gammaIsometry_apply_dom,
        gammaDomLim_bosEquivLim]
    have hu : ((bosEquivLim φ : DomLim) : BosonicFockLim)
        = Finsupp.linearCombination ℂ boseELim φ := bosEquivLim_coe φ
    rw [hΓ, hu, linearCombination_eq_sumBos, linearCombination_eq_sumBos,
      ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun c _ => ?_))
    rw [← smul_sub, norm_smul, gammaFockU1_boseELim_lorentz]
  · have hfac : ∀ c ∈ φ.support, Tendsto
        (fun Λ : RestrictedLorentz =>
          ‖φ c‖ * ‖gammaFockU1 m hm ⟨0, Λ⟩ (boseELim c)
            - boseELim c‖) (𝓝 1) (𝓝 (‖φ c‖ * 0)) :=
      fun c _ => tendsto_const_nhds.mul
        (gammaFockU1_basis_lorentz_tendsto m hm c)
    have hsum := tendsto_finsetSum φ.support hfac
    simpa using hsum

/-- **Lorentz strong continuity of the packaged action (T1):**
for every vector `z` of the bosonic Fock space, the packaged
Lorentz action is continuous at the identity — transported from
the discharged one-particle continuity through the
finite-particle density, with the uniform isometry bound. -/
theorem gammaFockU1_lorentz_tendsto (m : ℝ) (hm : 0 < m)
    (z : BosonicFockLim) :
    Tendsto (fun Λ : RestrictedLorentz => gammaFockU1 m hm ⟨0, Λ⟩ z)
      (𝓝 1) (𝓝 z) := by
  rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  have hzmem : z ∈ closure (DomLim : Set BosonicFockLim) := by
    rw [dense_DomLim.closure_eq]
    exact Set.mem_univ z
  obtain ⟨u, hu, hdist⟩ :=
    (Metric.mem_closure_iff.1 hzmem) (ε / 3) (by linarith)
  have hev : ∀ᶠ Λ : RestrictedLorentz in 𝓝 1,
      ‖gammaFockU1 m hm ⟨0, Λ⟩ u - u‖ < ε / 3 := by
    have hT := gammaFockU1_dom_lorentz_tendsto m hm ⟨u, hu⟩
    have h2 := (Metric.tendsto_nhds.1 hT) (ε / 3) (by linarith)
    filter_upwards [h2] with Λ hΛ
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hΛ
  filter_upwards [hev] with Λ hΛ
  have htri : ‖gammaFockU1 m hm ⟨0, Λ⟩ z - z‖
      ≤ ‖z - u‖ + ‖gammaFockU1 m hm ⟨0, Λ⟩ u - u‖ + ‖u - z‖ := by
    calc ‖gammaFockU1 m hm ⟨0, Λ⟩ z - z‖
        = ‖(gammaFockU1 m hm ⟨0, Λ⟩ z - gammaFockU1 m hm ⟨0, Λ⟩ u)
            + ((gammaFockU1 m hm ⟨0, Λ⟩ u - u) + (u - z))‖ := by
          congr 1
          abel
      _ ≤ ‖gammaFockU1 m hm ⟨0, Λ⟩ z - gammaFockU1 m hm ⟨0, Λ⟩ u‖
            + ‖gammaFockU1 m hm ⟨0, Λ⟩ u - u‖ + ‖u - z‖ := by
          have h1 := norm_add_le
            (gammaFockU1 m hm ⟨0, Λ⟩ z - gammaFockU1 m hm ⟨0, Λ⟩ u)
            ((gammaFockU1 m hm ⟨0, Λ⟩ u - u) + (u - z))
          have h2 := norm_add_le (gammaFockU1 m hm ⟨0, Λ⟩ u - u)
            (u - z)
          linarith
      _ = ‖z - u‖ + ‖gammaFockU1 m hm ⟨0, Λ⟩ u - u‖ + ‖u - z‖ := by
          congr 1
          rw [← map_sub, LinearIsometryEquiv.norm_map]
  have e1 : ‖z - u‖ = dist z u := (dist_eq_norm z u).symm
  have e2 : ‖u - z‖ = dist z u := by
    rw [norm_sub_rev]
    exact (dist_eq_norm z u).symm
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  rw [e1, e2] at htri
  linarith

/-- **Lorentz strong continuity at every point (T1):** by the
representation law and continuity of `Λ ↦ Λ₀⁻¹ * Λ` at `Λ₀`,
continuity at the identity transports to every `Λ₀`. -/
theorem gammaFockU1_lorentz_tendsto_at (m : ℝ) (hm : 0 < m)
    (Λ₀ : RestrictedLorentz) (z : BosonicFockLim) :
    Tendsto (fun Λ : RestrictedLorentz => gammaFockU1 m hm ⟨0, Λ⟩ z)
      (𝓝 Λ₀) (𝓝 (gammaFockU1 m hm ⟨0, Λ₀⟩ z)) := by
  have hfac : ∀ Λ : RestrictedLorentz, gammaFockU1 m hm ⟨0, Λ⟩ z
      = gammaFockU1 m hm ⟨0, Λ₀⟩
          (gammaFockU1 m hm ⟨0, Λ₀⁻¹ * Λ⟩ z) := by
    intro Λ
    have hgrp : (⟨0, Λ₀⟩ : RPoincare) * ⟨0, Λ₀⁻¹ * Λ⟩ = ⟨0, Λ⟩ := by
      apply RPoincare.ext
      · show (0 : Minkowski) + (Λ₀ : LorentzGroup).toLin 0 = 0
        rw [map_zero, add_zero]
      · show Λ₀ * (Λ₀⁻¹ * Λ) = Λ
        rw [← mul_assoc, mul_inv_cancel, one_mul]
    calc gammaFockU1 m hm ⟨0, Λ⟩ z
        = gammaFockU1 m hm ((⟨0, Λ₀⟩ : RPoincare)
            * ⟨0, Λ₀⁻¹ * Λ⟩) z := by
          rw [hgrp]
      _ = gammaFockU1 m hm ⟨0, Λ₀⟩
            (gammaFockU1 m hm ⟨0, Λ₀⁻¹ * Λ⟩ z) := by
          rw [gammaFockU1_mul, LinearIsometryEquiv.trans_apply]
  have hcomp : Tendsto (fun Λ : RestrictedLorentz =>
      gammaFockU1 m hm ⟨0, Λ₀⟩ (gammaFockU1 m hm ⟨0, Λ₀⁻¹ * Λ⟩ z))
      (𝓝 Λ₀) (𝓝 (gammaFockU1 m hm ⟨0, Λ₀⟩ z)) := by
    have h1 : Tendsto (fun Λ : RestrictedLorentz =>
        gammaFockU1 m hm ⟨0, Λ₀⁻¹ * Λ⟩ z) (𝓝 Λ₀) (𝓝 z) :=
      (gammaFockU1_lorentz_tendsto m hm z).comp
        (tendsto_restricted_inv_mul Λ₀)
    exact ((gammaFockU1 m hm ⟨0, Λ₀⟩).continuous.tendsto z).comp h1
  exact Tendsto.congr (fun Λ => (hfac Λ).symm) hcomp

end ThetLogos
