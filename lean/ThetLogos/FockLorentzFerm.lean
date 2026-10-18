import ThetLogos.FockPackagingFerm
import ThetLogos.LorentzContinuity

/-!
# ThetLogos.FockLorentzFerm — FOCK-LEVEL LORENTZ STRONG
# CONTINUITY, fermionic half (unlock chain item 2, ratified
# 2026-10-18)

The fermionic half of the Fock-level Lorentz transport named as
the fenced remainder of the Lorentz brick
(`LorentzContinuity.lean`, dossier
`whitepaper/lorentz-continuity-2026-10-18.md`).
`FockPackagingFerm` packaged the one-particle Poincaré action
`shellU1` through second quantization Γ to the fermionic limit
Fock space `FermionicFockLim`, transporting strong continuity of
the translation subgroup only; this module transports the
Lorentz subgroup's strong continuity from the discharged
one-particle input `shellU1_lorentz_tendsto`.

## What is proved (T1)

* `gammaFockFU1_lorentz_tendsto`: for every
  `z : FermionicFockLim`, `Λ ↦ gammaFockFU1 m hm ⟨0, Λ⟩ z` tends
  to `z` as `Λ → 1` in `RestrictedLorentz` (topology of
  pointwise action convergence, from `LorentzContinuity`).
* `gammaFockFU1_lorentz_tendsto_at`: the same at every `Λ₀`, by
  the group law and `tendsto_restricted_inv_mul`.

## Route

The translation transport of `FockPackagingFerm`, generalized:
the determinant-continuity lemma there
(`minorDet_tendsto_of_tendsto`) is already filter-general, so
the chain — entry continuity, diagonal kernel, basis vectors
(`2 - 2 Re γ`), finite-particle squeeze, ε/3 extension by
unitarity — replays with `shellU1_translation_tendsto` replaced
by `shellU1_lorentz_tendsto` and the filter `𝓝 0` on `Minkowski`
replaced by `𝓝 1` on `RestrictedLorentz`. The finite-particle
vectors `fermDomLim` are the dense class; no tensor power of
the one-particle space is ever formed — the Γ kernel *is* the
finite tensor data, in the concrete basis `shellONB`.

## Fences

* Free fermionic Fock space only; no interacting statement.
* Subgroup-wise: no joint topology on `RPoincare` is
  introduced; translations and Lorentz stand separately, as at
  the one-particle level.
* The bosonic half lives in `FockLorentzBos.lean`.
-/

namespace ThetLogos

open scoped InnerProductSpace
open scoped Matrix
open Filter Topology

/-- Entry continuity under the Lorentz subgroup (T1): the
one-particle matrix entries of the shell basis are continuous
at the identity of `RestrictedLorentz`, from the discharged
one-particle Lorentz strong continuity. -/
theorem UmatF_lorentz_tendsto (m : ℝ) (hm : 0 < m) (i j : ℕ) :
    Tendsto (fun Λ : RestrictedLorentz =>
        UmatF m hm (shellU1 m hm ⟨0, Λ⟩) i j) (𝓝 1)
      (𝓝 (UmatF m hm 1 i j)) := by
  have h : Tendsto (fun Λ : RestrictedLorentz =>
        ⟪shellONB m hm i, shellU1 m hm ⟨0, Λ⟩ (shellONB m hm j)⟫_ℂ)
        (𝓝 1) (𝓝 ⟪shellONB m hm i, shellONB m hm j⟫_ℂ) :=
    Filter.Tendsto.inner tendsto_const_nhds
      (shellU1_lorentz_tendsto m hm (shellONB m hm j))
  exact h

/-- The diagonal kernel is continuous at the identity of the
Lorentz subgroup, with value `1` (T1): at a fixed configuration
the kernel is a fixed finite determinant in the entries. -/
theorem gammaKernelFermLim_diag_lorentz_tendsto (m : ℝ) (hm : 0 < m)
    (S : Finset ℕ) :
    Tendsto (fun Λ : RestrictedLorentz =>
        gammaKernelFermLim m hm (shellU1 m hm ⟨0, Λ⟩) S S)
      (𝓝 1) (𝓝 1) := by
  obtain ⟨d, S₀, hS⟩ := fermConfig_factor S
  have hval : minorDet d (UmatRectF m hm 1 d) S₀ S₀ = 1 := by
    rw [UmatRectF_one, minorDet_one, if_pos rfl]
  have heq : ∀ Λ : RestrictedLorentz,
      minorDet d (UmatRectF m hm (shellU1 m hm ⟨0, Λ⟩) d) S₀ S₀
        = gammaKernelFermLim m hm (shellU1 m hm ⟨0, Λ⟩) S S := by
    intro Λ
    rw [← hS]
    exact (gammaKernelFermLim_fermConfigEmbLim m hm _ d S₀ S₀).symm
  rw [← hval]
  refine Filter.Tendsto.congr (fun Λ => heq Λ) ?_
  exact minorDet_tendsto_of_tendsto _ _
    (fun i j => UmatF_lorentz_tendsto m hm i.val j.val) S₀ S₀

/-- The packaged action on a basis vector, along a Lorentz
parameter (T1). -/
theorem gammaFockFU1_fockBasisLim_lorentz (m : ℝ) (hm : 0 < m)
    (Λ : RestrictedLorentz) (S : Finset ℕ) :
    gammaFockFU1 m hm ⟨0, Λ⟩ (fockBasisLim S)
      = colVecF m hm (shellU1 m hm ⟨0, Λ⟩) S := by
  show gammaFockF m hm (shellU1 m hm ⟨0, Λ⟩) (fockBasisLim S) = _
  rw [gammaFockF_apply]
  exact gammaIsometryF_fockBasisLim m hm _ S

/-- Basis vectors are strongly continuous under the packaged
Lorentz action (T1): the squared distance is `2 - 2 Re γ`. -/
theorem gammaFockFU1_basis_lorentz_tendsto (m : ℝ) (hm : 0 < m)
    (S : Finset ℕ) :
    Tendsto (fun Λ : RestrictedLorentz =>
        ‖gammaFockFU1 m hm ⟨0, Λ⟩ (fockBasisLim S) - fockBasisLim S‖)
      (𝓝 1) (𝓝 0) := by
  have hnorme : ‖fockBasisLim S‖ = 1 := fockBasisLim_orthonormal.1 S
  have hnorm : ∀ Λ : RestrictedLorentz,
      ‖gammaFockFU1 m hm ⟨0, Λ⟩ (fockBasisLim S) - fockBasisLim S‖ ^ 2
        = 2 - 2 * (gammaKernelFermLim m hm (shellU1 m hm ⟨0, Λ⟩)
            S S).re := by
    intro Λ
    rw [gammaFockFU1_fockBasisLim_lorentz]
    have hnormV : ‖colVecF m hm (shellU1 m hm ⟨0, Λ⟩) S‖ = 1 := by
      calc ‖colVecF m hm (shellU1 m hm ⟨0, Λ⟩) S‖
          = ‖gammaIsometryF m hm (shellU1 m hm ⟨0, Λ⟩)
              (fockBasisLim S)‖ := by
            rw [gammaIsometryF_fockBasisLim]
        _ = ‖fockBasisLim S‖ := LinearIsometry.norm_map _ _
        _ = 1 := hnorme
    calc ‖colVecF m hm (shellU1 m hm ⟨0, Λ⟩) S - fockBasisLim S‖ ^ 2
        = ‖colVecF m hm (shellU1 m hm ⟨0, Λ⟩) S‖ ^ 2
          - 2 * (⟪colVecF m hm (shellU1 m hm ⟨0, Λ⟩) S,
              fockBasisLim S⟫_ℂ).re
          + ‖fockBasisLim S‖ ^ 2 := norm_sub_sq (𝕜 := ℂ) _ _
      _ = 1 - 2 * (star (gammaKernelFermLim m hm
              (shellU1 m hm ⟨0, Λ⟩) S S)).re + 1 := by
          rw [inner_colVecF_fockBasisLim, hnormV, hnorme]
          ring
      _ = 2 - 2 * (gammaKernelFermLim m hm (shellU1 m hm ⟨0, Λ⟩)
            S S).re := by
          have hre : ∀ z : ℂ, (star z).re = z.re := fun z => by simp
          rw [hre]
          ring
  have hsq : Tendsto (fun Λ : RestrictedLorentz =>
        ‖gammaFockFU1 m hm ⟨0, Λ⟩ (fockBasisLim S) - fockBasisLim S‖ ^ 2)
      (𝓝 1) (𝓝 0) := by
    have hre' : Tendsto (fun Λ : RestrictedLorentz =>
        (gammaKernelFermLim m hm (shellU1 m hm ⟨0, Λ⟩) S S).re)
          (𝓝 1) (𝓝 1) := by
      have h := (Complex.continuous_re.tendsto (1 : ℂ)).comp
        (gammaKernelFermLim_diag_lorentz_tendsto m hm S)
      exact h.congr (fun Λ => rfl)
    have key : Tendsto (fun Λ : RestrictedLorentz => 2 - 2
        * (gammaKernelFermLim m hm (shellU1 m hm ⟨0, Λ⟩) S S).re)
          (𝓝 1) (𝓝 0) := by
      have h2 : Tendsto (fun Λ : RestrictedLorentz => (2 : ℝ) - 2
            * (gammaKernelFermLim m hm (shellU1 m hm ⟨0, Λ⟩) S S).re)
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
theorem gammaFockFU1_dom_lorentz_tendsto (m : ℝ) (hm : 0 < m)
    (u : fermDomLim) :
    Tendsto (fun Λ : RestrictedLorentz =>
        ‖gammaFockFU1 m hm ⟨0, Λ⟩ (u : FermionicFockLim)
          - (u : FermionicFockLim)‖) (𝓝 1) (𝓝 0) := by
  obtain ⟨φ, rfl⟩ : ∃ φ, fermEquivLim φ = u :=
    ⟨fermReprLim u, LinearEquiv.apply_symm_apply fermEquivLim u⟩
  refine squeeze_zero
    (g := fun Λ : RestrictedLorentz => ∑ S ∈ φ.support, ‖φ S‖
      * ‖gammaFockFU1 m hm ⟨0, Λ⟩ (fockBasisLim S) - fockBasisLim S‖)
    (fun Λ => norm_nonneg _) (fun Λ => ?_) ?_
  · have hΓ : gammaFockFU1 m hm ⟨0, Λ⟩
          ((fermEquivLim φ : fermDomLim) : FermionicFockLim)
        = Finsupp.linearCombination ℂ
            (colVecF m hm (shellU1 m hm ⟨0, Λ⟩)) φ := by
      show gammaFockF m hm (shellU1 m hm ⟨0, Λ⟩)
          ((fermEquivLim φ : fermDomLim) : FermionicFockLim) = _
      rw [gammaFockF_apply, gammaIsometryF_apply_dom,
        gammaDomF_fermEquivLim]
    have hu : ((fermEquivLim φ : fermDomLim) : FermionicFockLim)
        = Finsupp.linearCombination ℂ fockBasisLim φ :=
      fermEquivLim_coe φ
    rw [hΓ, hu, linearCombination_eq_sum, linearCombination_eq_sum,
      ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun S _ => ?_))
    rw [← smul_sub, norm_smul, gammaFockFU1_fockBasisLim_lorentz]
  · have hfac : ∀ S ∈ φ.support, Tendsto
        (fun Λ : RestrictedLorentz =>
          ‖φ S‖ * ‖gammaFockFU1 m hm ⟨0, Λ⟩ (fockBasisLim S)
            - fockBasisLim S‖) (𝓝 1) (𝓝 (‖φ S‖ * 0)) :=
      fun S _ => tendsto_const_nhds.mul
        (gammaFockFU1_basis_lorentz_tendsto m hm S)
    have hsum := tendsto_finsetSum φ.support hfac
    simpa using hsum

/-- **Lorentz strong continuity of the packaged action (T1):**
for every vector `z` of the fermionic Fock space, the packaged
Lorentz action is continuous at the identity — transported from
the discharged one-particle continuity through the
finite-particle density, with the uniform isometry bound. -/
theorem gammaFockFU1_lorentz_tendsto (m : ℝ) (hm : 0 < m)
    (z : FermionicFockLim) :
    Tendsto (fun Λ : RestrictedLorentz => gammaFockFU1 m hm ⟨0, Λ⟩ z)
      (𝓝 1) (𝓝 z) := by
  rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  have hzmem : z ∈ closure (fermDomLim : Set FermionicFockLim) := by
    rw [dense_fermDomLim.closure_eq]
    exact Set.mem_univ z
  obtain ⟨u, hu, hdist⟩ :=
    (Metric.mem_closure_iff.1 hzmem) (ε / 3) (by linarith)
  have hev : ∀ᶠ Λ : RestrictedLorentz in 𝓝 1,
      ‖gammaFockFU1 m hm ⟨0, Λ⟩ u - u‖ < ε / 3 := by
    have hT := gammaFockFU1_dom_lorentz_tendsto m hm ⟨u, hu⟩
    have h2 := (Metric.tendsto_nhds.1 hT) (ε / 3) (by linarith)
    filter_upwards [h2] with Λ hΛ
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hΛ
  filter_upwards [hev] with Λ hΛ
  have htri : ‖gammaFockFU1 m hm ⟨0, Λ⟩ z - z‖
      ≤ ‖z - u‖ + ‖gammaFockFU1 m hm ⟨0, Λ⟩ u - u‖ + ‖u - z‖ := by
    calc ‖gammaFockFU1 m hm ⟨0, Λ⟩ z - z‖
        = ‖(gammaFockFU1 m hm ⟨0, Λ⟩ z - gammaFockFU1 m hm ⟨0, Λ⟩ u)
            + ((gammaFockFU1 m hm ⟨0, Λ⟩ u - u) + (u - z))‖ := by
          congr 1
          abel
      _ ≤ ‖gammaFockFU1 m hm ⟨0, Λ⟩ z - gammaFockFU1 m hm ⟨0, Λ⟩ u‖
            + ‖gammaFockFU1 m hm ⟨0, Λ⟩ u - u‖ + ‖u - z‖ := by
          have h1 := norm_add_le
            (gammaFockFU1 m hm ⟨0, Λ⟩ z - gammaFockFU1 m hm ⟨0, Λ⟩ u)
            ((gammaFockFU1 m hm ⟨0, Λ⟩ u - u) + (u - z))
          have h2 := norm_add_le (gammaFockFU1 m hm ⟨0, Λ⟩ u - u)
            (u - z)
          linarith
      _ = ‖z - u‖ + ‖gammaFockFU1 m hm ⟨0, Λ⟩ u - u‖ + ‖u - z‖ := by
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
theorem gammaFockFU1_lorentz_tendsto_at (m : ℝ) (hm : 0 < m)
    (Λ₀ : RestrictedLorentz) (z : FermionicFockLim) :
    Tendsto (fun Λ : RestrictedLorentz => gammaFockFU1 m hm ⟨0, Λ⟩ z)
      (𝓝 Λ₀) (𝓝 (gammaFockFU1 m hm ⟨0, Λ₀⟩ z)) := by
  have hfac : ∀ Λ : RestrictedLorentz, gammaFockFU1 m hm ⟨0, Λ⟩ z
      = gammaFockFU1 m hm ⟨0, Λ₀⟩
          (gammaFockFU1 m hm ⟨0, Λ₀⁻¹ * Λ⟩ z) := by
    intro Λ
    have hgrp : (⟨0, Λ₀⟩ : RPoincare) * ⟨0, Λ₀⁻¹ * Λ⟩ = ⟨0, Λ⟩ := by
      apply RPoincare.ext
      · show (0 : Minkowski) + (Λ₀ : LorentzGroup).toLin 0 = 0
        rw [map_zero, add_zero]
      · show Λ₀ * (Λ₀⁻¹ * Λ) = Λ
        rw [← mul_assoc, mul_inv_cancel, one_mul]
    calc gammaFockFU1 m hm ⟨0, Λ⟩ z
        = gammaFockFU1 m hm ((⟨0, Λ₀⟩ : RPoincare)
            * ⟨0, Λ₀⁻¹ * Λ⟩) z := by
          rw [hgrp]
      _ = gammaFockFU1 m hm ⟨0, Λ₀⟩
            (gammaFockFU1 m hm ⟨0, Λ₀⁻¹ * Λ⟩ z) := by
          rw [gammaFockFU1_mul, LinearIsometryEquiv.trans_apply]
  have hcomp : Tendsto (fun Λ : RestrictedLorentz =>
      gammaFockFU1 m hm ⟨0, Λ₀⟩ (gammaFockFU1 m hm ⟨0, Λ₀⁻¹ * Λ⟩ z))
      (𝓝 Λ₀) (𝓝 (gammaFockFU1 m hm ⟨0, Λ₀⟩ z)) := by
    have h1 : Tendsto (fun Λ : RestrictedLorentz =>
        gammaFockFU1 m hm ⟨0, Λ₀⁻¹ * Λ⟩ z) (𝓝 Λ₀) (𝓝 z) :=
      (gammaFockFU1_lorentz_tendsto m hm z).comp
        (tendsto_restricted_inv_mul Λ₀)
    exact ((gammaFockFU1 m hm ⟨0, Λ₀⟩).continuous.tendsto z).comp h1
  exact Tendsto.congr (fun Λ => (hfac Λ).symm) hcomp

end ThetLogos
