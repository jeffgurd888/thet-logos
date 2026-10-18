/-
# Lorentz/rotation strong continuity of the one-particle representation

COMMISSION — LORENTZ/ROTATION STRONG CONTINUITY (Rung 7 remainder, last
joint), ratified build line, priced **S–M** in the parked-fleet gauntlet
(`whitepaper/gauntlet-parked-fleet-2026-10-17.md`, §4a). Dossier:
`whitepaper/lorentz-continuity-2026-10-18.md`.

The translation half of the window was discharged in
`TranslationContinuity.lean` (10 T1) by dominated convergence with
dominator `4‖ψ‖²` — a route that rests on the shell action being
*trivial* for pure translations, and therefore provably does not extend
to the Lorentz subgroup, whose action moves points on the shell. This
module discharges the Lorentz half.

**What IS proved here (T1, zero sorrys):**

* A topology on `LorentzGroup`: the topology of pointwise convergence
  of the action on `Minkowski` (equivalently entrywise convergence of
  the representing matrices in the standard basis — the two are
  identified by `tendsto_lorentz_iff`). `RestrictedLorentz` carries the
  subspace topology. Both are first countable.
* **Strong continuity at the identity** of the packaged one-particle
  action of the Lorentz subgroup: for every `Ψ : shellLp m hm`,
  `Λ ↦ shellU1 m hm ⟨0, Λ⟩ Ψ` tends to `Ψ` as `Λ → 1`
  (`shellU1_lorentz_tendsto`), and by the group law the same at every
  `Λ₀` (`shellU1_lorentz_tendsto_at`). This closes the strong-continuity
  window of `MassShellMeasure.lean` at the one-particle level: the
  translations half (discharged) plus this Lorentz half give strong
  continuity of both subgroup actions of `RPoincare` separately.

**Route (as scoped in the commission).** Density + uniform control, on
the spatial side of the graph parametrization. The shell `L²` space is
transported along `shellLpEquiv` to `spatialLp m` (the `L²` space of
the density-weighted Lebesgue measure `d³u/(2E_u)` on `ℝ³`), where the
Lorentz action becomes the composition operator `F ↦ F ∘ spAct Λ` for
an explicit measure-preserving spatial action `spAct`. For `F`
continuous with compact support, the squared norm of the difference is
computed as an integral, the substitution `u ↦ spAct Λ⁻¹ u` moves the
group element onto the *fixed* factor of the cross term, and dominated
convergence (dominator `B·‖F‖`, from the sup bound `B` of `F`) closes
the cross term. Compactly supported continuous functions are dense in
`spatialLp m` by Mathlib's `MemLp.exists_hasCompactSupport_eLpNorm_sub_le`
(the spatial measure is regular: it is locally finite on a σ-compact
metric space), and the standard ε/3 argument with unitarity
(`spU Λ` is a linear isometry) extends continuity from the dense class
to every `L²` element.

**Fences.**

* One-particle level only. The Fock-level transport of Lorentz strong
  continuity is NOT landed here: the transport machinery of
  `FockPackagingBos`/`FockPackagingFerm` is stated for the translation
  parameterization (the kernel-level filter lemma is generic, but the
  entrywise matrix-element continuity for the Lorentz family is a new
  proof in each statistic module, and the two statistic modules cannot
  be co-imported). What this brick discharges is exactly the
  one-particle input those transports consume.
* No joint topology on `RPoincare` is introduced; the statement is
  strong continuity of the Lorentz subgroup action (and, previously,
  of the translation subgroup action), not of the combined action in a
  product topology.
* Free theory, one particle, fixed mass shell. No interacting, no
  continuum-limit, and no Yang–Mills statement is made or implied.
  Clay parts closed by this brick: **0**.
-/

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import ThetLogos.FockPackaging

namespace ThetLogos

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

/-!
## The topology of pointwise convergence on the Lorentz group
-/

/-- The coordinate functions of a Lorentz transformation in the standard
basis of `Minkowski = Fin 4 → ℝ`: `lorentzCoord Λ i j = (Λ eⱼ)ᵢ`. The
topology on `LorentzGroup` below is the one induced by these
coordinates (entrywise matrix convergence). -/
def lorentzCoord (Λ : LorentzGroup) : Fin 4 → Fin 4 → ℝ :=
  fun i j => Λ.toLin (Pi.single j 1) i

/-- The topology of pointwise convergence on `LorentzGroup`: `Λ → Λ₀`
iff `Λ p → Λ₀ p` for every `p : Minkowski` (proved in
`tendsto_lorentz_iff` below). In finite dimensions this is the usual
Lie-group topology of the Lorentz group. -/
instance : TopologicalSpace LorentzGroup :=
  TopologicalSpace.induced lorentzCoord inferInstance

/-- The pointwise-convergence topology on the Lorentz group is first
countable (it is induced from a finite product of copies of `ℝ`). -/
instance : FirstCountableTopology LorentzGroup where
  nhds_generated_countable Λ := by
    rw [nhds_induced]
    infer_instance

/-- The restricted Lorentz group, with the subspace topology, is first
countable. -/
instance : FirstCountableTopology RestrictedLorentz :=
  Topology.IsInducing.subtypeVal.firstCountableTopology

/-- **T1:** convergence in the Lorentz topology is entrywise convergence
of the representing matrices. -/
theorem tendsto_lorentzCoord_iff {ι : Type*} {f : ι → LorentzGroup} {l : Filter ι}
    {Λ₀ : LorentzGroup} :
    Tendsto f l (𝓝 Λ₀) ↔ ∀ i j, Tendsto (fun t => (f t).toLin (Pi.single j 1) i) l
      (𝓝 (Λ₀.toLin (Pi.single j 1) i)) := by
  have h1 : Tendsto f l (𝓝 Λ₀)
      ↔ Tendsto (lorentzCoord ∘ f) l (𝓝 (lorentzCoord Λ₀)) := by
    rw [nhds_induced]
    exact Filter.tendsto_comap_iff
  rw [h1, tendsto_pi_nhds]
  constructor
  · intro h i j
    exact (tendsto_pi_nhds.1 (h i)) j
  · intro h
    exact fun i => tendsto_pi_nhds.2 fun j => h i j

/-- **T1:** a Lorentz transformation applied to a vector, in coordinates:
`(Λ p)ᵢ = ∑ⱼ pⱼ (Λ eⱼ)ᵢ` (expansion of `p` in the standard basis). -/
theorem lorentz_apply_coord (Λ : LorentzGroup) (p : Minkowski) (i : Fin 4) :
    Λ.toLin p i = ∑ j, p j * Λ.toLin (Pi.single j 1) i := by
  have hp : p = ∑ j, (p j) • Pi.single j (1 : ℝ) := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  conv_lhs => rw [hp]
  rw [map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, Pi.smul_apply, smul_eq_mul]

/-- **T1:** convergence in the Lorentz topology is pointwise convergence
of the action on Minkowski space. -/
theorem tendsto_lorentz_iff {ι : Type*} {f : ι → LorentzGroup} {l : Filter ι}
    {Λ₀ : LorentzGroup} :
    Tendsto f l (𝓝 Λ₀) ↔ ∀ p, Tendsto (fun t => (f t).toLin p) l
      (𝓝 (Λ₀.toLin p)) := by
  constructor
  · intro h p
    rw [tendsto_pi_nhds]
    intro i
    have e1 : (fun t => (f t).toLin p i)
        = (fun t => ∑ j, p j * (f t).toLin (Pi.single j 1) i) := by
      funext t
      exact lorentz_apply_coord (f t) p i
    rw [e1, lorentz_apply_coord Λ₀ p i]
    exact tendsto_finsetSum _ fun j _ =>
      Tendsto.const_mul (p j) ((tendsto_lorentzCoord_iff.1 h) i j)
  · intro h
    rw [tendsto_lorentzCoord_iff]
    intro i j
    exact (tendsto_pi_nhds.1 (h (Pi.single j 1))) i

/-- **T1:** convergence in the restricted Lorentz group is pointwise
convergence of the action on Minkowski space. -/
theorem tendsto_restricted_iff {ι : Type*} {f : ι → RestrictedLorentz} {l : Filter ι}
    {Λ₀ : RestrictedLorentz} :
    Tendsto f l (𝓝 Λ₀) ↔ ∀ p, Tendsto (fun t => ((f t : LorentzGroup)).toLin p) l
      (𝓝 ((Λ₀ : LorentzGroup).toLin p)) := by
  rw [tendsto_subtype_rng]
  exact tendsto_lorentz_iff

/-- **T1:** the shell-side evaluation is continuous at the identity of
the restricted group: for fixed `p`, `Λ ↦ Λ p → p` as `Λ → 1`. -/
theorem tendsto_restricted_apply (p : Minkowski) :
    Tendsto (fun Λ : RestrictedLorentz => (Λ : LorentzGroup).toLin p) (𝓝 1)
      (𝓝 p) := by
  have h := (tendsto_restricted_iff (f := fun Λ : RestrictedLorentz => Λ)
    (Λ₀ := 1)).1 tendsto_id p
  simpa using h

/-- **T1:** left multiplication by a fixed inverse is continuous at the
diagonal: `Λ₀⁻¹ * Λ → 1` as `Λ → Λ₀` in the restricted group (pointwise
in the action: `(Λ₀⁻¹ * Λ) p = Λ₀⁻¹ (Λ p)`, and `Λ p → Λ₀ p` with
`Λ₀⁻¹` a fixed continuous linear map). -/
theorem tendsto_restricted_inv_mul (Λ₀ : RestrictedLorentz) :
    Tendsto (fun Λ : RestrictedLorentz => Λ₀⁻¹ * Λ) (𝓝 Λ₀) (𝓝 1) := by
  rw [tendsto_restricted_iff]
  intro p
  have hcont : Continuous (((Λ₀⁻¹ : RestrictedLorentz) : LorentzGroup).toLin :
      Minkowski → Minkowski) :=
    (((Λ₀⁻¹ : RestrictedLorentz) : LorentzGroup).toLin.toLinearMap).continuous_of_finiteDimensional
  have hΛ : Tendsto (fun Λ : RestrictedLorentz => (Λ : LorentzGroup).toLin p)
      (𝓝 Λ₀) (𝓝 ((Λ₀ : LorentzGroup).toLin p)) :=
    tendsto_restricted_iff.1 tendsto_id p
  have h : Tendsto (fun Λ : RestrictedLorentz =>
      ((Λ₀⁻¹ : RestrictedLorentz) : LorentzGroup).toLin
        ((Λ : LorentzGroup).toLin p)) (𝓝 Λ₀)
      (𝓝 (((Λ₀⁻¹ : RestrictedLorentz) : LorentzGroup).toLin
        ((Λ₀ : LorentzGroup).toLin p))) :=
    (hcont.tendsto _).comp hΛ
  have hfun : (fun Λ : RestrictedLorentz =>
        ((Λ₀⁻¹ * Λ : RestrictedLorentz) : LorentzGroup).toLin p)
      = (fun Λ : RestrictedLorentz =>
        ((Λ₀⁻¹ : RestrictedLorentz) : LorentzGroup).toLin
          ((Λ : LorentzGroup).toLin p)) := by
    funext Λ
    rw [Subgroup.coe_mul, LorentzGroup.mul_toLin, LinearEquiv.trans_apply]
  have hval : ((Λ₀⁻¹ : RestrictedLorentz) : LorentzGroup).toLin
        ((Λ₀ : LorentzGroup).toLin p) = ((1 : RestrictedLorentz) : LorentzGroup).toLin p := by
    have h1 : ((Λ₀⁻¹ : RestrictedLorentz) : LorentzGroup).toLin
          ((Λ₀ : LorentzGroup).toLin p)
        = ((Λ₀⁻¹ * Λ₀ : RestrictedLorentz) : LorentzGroup).toLin p := by
      rw [Subgroup.coe_mul, LorentzGroup.mul_toLin, LinearEquiv.trans_apply]
    rw [h1, inv_mul_cancel]
  rw [← hfun, hval] at h
  exact h

/-!
## The spatial action of the restricted Lorentz group

Under the graph parametrization `shellParam : ℝ³ → shell`, the Lorentz
action on the shell transports to an action on `ℝ³` itself:
`spAct Λ u = spatialOf (Λ⁻¹ (shellParam u))`. This is the spatial shadow
of the shell action of `Λ⁻¹` — exactly the element the one-particle
operator `shellU1 ⟨0, Λ⟩` pulls back along (see
`shellLpEquiv_shellU1` below).
-/

/-- **T1:** reading off the spatial part of a Minkowski vector is the
continuous linear map `spatialPartLin`, as a function. -/
theorem spatialOf_eq_spatialPartLin : spatialOf = ⇑spatialPartLin := by
  funext p
  apply PiLp.ext
  intro i
  rw [spatialOf_apply, spatialPartLin_apply]

/-- **T1:** `spatialOf : Minkowski → ℝ³` is continuous. -/
theorem continuous_spatialOf : Continuous spatialOf := by
  rw [spatialOf_eq_spatialPartLin]
  exact LinearMap.continuous_of_finiteDimensional spatialPartLin

/-- **T1:** the graph parametrization `shellParam m : ℝ³ → Minkowski`
is continuous (its energy component is `shellEnergy_continuous`). -/
theorem continuous_shellParam (m : ℝ) : Continuous (shellParam m) := by
  have hfun : shellParam m
      = finFourEquiv.symm ∘ (fun u => (shellEnergy m u, u)) := by
    funext u
    rfl
  rw [hfun]
  exact (LinearMap.continuous_of_finiteDimensional
    finFourEquiv.symm.toLinearMap).comp
    ((shellEnergy_continuous m).prodMk continuous_id)

/-- The spatial action of a restricted Lorentz element: the spatial
shadow of the shell action of its inverse,
`spAct m Λ u = spatialOf (Λ⁻¹ (shellParam m u))`. -/
noncomputable def spAct (m : ℝ) (Λ : RestrictedLorentz)
    (u : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  spatialOf ((Λ : LorentzGroup)⁻¹.toLin (shellParam m u))

/-- **T1:** the spatial action is continuous in the spatial variable. -/
theorem continuous_spAct (m : ℝ) (Λ : RestrictedLorentz) :
    Continuous (spAct m Λ) := by
  have h1 : Continuous (((Λ : LorentzGroup)⁻¹).toLin : Minkowski → Minkowski) :=
    (((Λ : LorentzGroup)⁻¹).toLin.toLinearMap).continuous_of_finiteDimensional
  exact continuous_spatialOf.comp (h1.comp (continuous_shellParam m))

/-- **T1:** the spatial action is a group anti-action in the
composition sense matching the operator pullback:
`spAct (Λ₁ * Λ₂) = spAct Λ₂ ∘ spAct Λ₁` (the inverse in the definition
reverses the order, as it must for a pullback representation). -/
theorem spAct_comp (m : ℝ) (hm : 0 < m) (Λ₁ Λ₂ : RestrictedLorentz) :
    spAct m (Λ₁ * Λ₂) = spAct m Λ₂ ∘ spAct m Λ₁ := by
  funext u
  have hmem : (Λ₁ : LorentzGroup)⁻¹.toLin (shellParam m u) ∈ massShell m :=
    restricted_preserves_shell Λ₁⁻¹ _ m hm (shellParam_mem m hm u)
  show spatialOf (((Λ₁ * Λ₂ : RestrictedLorentz) : LorentzGroup)⁻¹.toLin
      (shellParam m u))
    = spatialOf ((Λ₂ : LorentzGroup)⁻¹.toLin (shellParam m
      (spatialOf ((Λ₁ : LorentzGroup)⁻¹.toLin (shellParam m u)))))
  rw [Subgroup.coe_mul, mul_inv_rev, LorentzGroup.mul_toLin,
    LinearEquiv.trans_apply, shellParam_spatialOf m hm hmem]

/-- **T1:** the spatial action of the identity is the identity. -/
theorem spAct_one (m : ℝ) : spAct m 1 = id := by
  funext u
  show spatialOf (((1 : RestrictedLorentz) : LorentzGroup)⁻¹.toLin
    (shellParam m u)) = u
  rw [Subgroup.coe_one, inv_one, LorentzGroup.one_toLin, LinearEquiv.refl_apply]
  exact spatialOf_shellParam m u

/-- **T1:** the spatial action is invertible: `spAct Λ⁻¹ ∘ spAct Λ = id`. -/
theorem spAct_inv_comp_self (m : ℝ) (hm : 0 < m) (Λ : RestrictedLorentz) :
    spAct m Λ⁻¹ ∘ spAct m Λ = id := by
  rw [← spAct_comp m hm Λ Λ⁻¹, mul_inv_cancel, spAct_one]

/-- **T1:** the spatial action is invertible: `spAct Λ ∘ spAct Λ⁻¹ = id`. -/
theorem spAct_comp_inv_self (m : ℝ) (hm : 0 < m) (Λ : RestrictedLorentz) :
    spAct m Λ ∘ spAct m Λ⁻¹ = id := by
  rw [← spAct_comp m hm Λ⁻¹ Λ, inv_mul_cancel, spAct_one]

/-- The shell action of a restricted Lorentz element, packaged as a
measurable equivalence of the mass shell (its inverse is the action
of the inverse element). -/
noncomputable def shellActREquiv (Λ : RestrictedLorentz) (m : ℝ) (hm : 0 < m) :
    massShell m ≃ᵐ massShell m where
  toFun := shellActR Λ m hm
  invFun := shellActR Λ⁻¹ m hm
  left_inv := by
    intro p
    have h : shellActR Λ⁻¹ m hm (shellActR Λ m hm p)
        = shellActR (Λ⁻¹ * Λ) m hm p :=
      congrFun (shellActR_mul Λ⁻¹ Λ m hm) p
    rw [h, inv_mul_cancel, shellActR_one]
    rfl
  right_inv := by
    intro p
    have h : shellActR Λ m hm (shellActR Λ⁻¹ m hm p)
        = shellActR (Λ * Λ⁻¹) m hm p :=
      congrFun (shellActR_mul Λ Λ⁻¹ m hm) p
    rw [h, mul_inv_cancel, shellActR_one]
    rfl
  measurable_toFun := by
    unfold shellActR
    apply Measurable.subtype_mk
    exact ((Λ : LorentzGroup).toLin.toLinearMap).continuous_of_finiteDimensional.measurable.comp
      measurable_subtype_coe
  measurable_invFun := by
    unfold shellActR
    apply Measurable.subtype_mk
    exact (((Λ⁻¹ : RestrictedLorentz) : LorentzGroup).toLin.toLinearMap).continuous_of_finiteDimensional.measurable.comp
      measurable_subtype_coe

/-- The spatial action, packaged as a measurable equivalence of `ℝ³`:
`spActEquiv Λ = shellParamEquiv ≫ shellActR Λ⁻¹ ≫ shellParamEquiv.symm`. -/
noncomputable def spActEquiv (m : ℝ) (hm : 0 < m) (Λ : RestrictedLorentz) :
    EuclideanSpace ℝ (Fin 3) ≃ᵐ EuclideanSpace ℝ (Fin 3) :=
  (shellParamEquiv m hm).trans
    ((shellActREquiv Λ⁻¹ m hm).trans (shellParamEquiv m hm).symm)

/-- **T1:** the packaged spatial equivalence acts as `spAct`. -/
theorem spActEquiv_apply (m : ℝ) (hm : 0 < m) (Λ : RestrictedLorentz)
    (u : EuclideanSpace ℝ (Fin 3)) :
    spActEquiv m hm Λ u = spAct m Λ u := rfl

/-- **T1:** the spatial action preserves the spatial measure
`d³u/(2E_u)` — the transport, along the graph parametrization, of the
shell measure invariance `measurePreserving_shellActR`. -/
theorem measurePreserving_spAct (m : ℝ) (hm : 0 < m) (Λ : RestrictedLorentz) :
    MeasurePreserving (spAct m Λ) (spatialMeasure m) (spatialMeasure m) := by
  have hfun : spAct m Λ = ⇑(shellParamEquiv m hm).symm
      ∘ shellActR Λ⁻¹ m hm ∘ ⇑(shellParamEquiv m hm) := by
    funext u
    rfl
  rw [hfun]
  exact (measurePreserving_shellParamEquiv_symm m hm).comp
    ((measurePreserving_shellActR Λ⁻¹ m hm).comp
      (measurePreserving_shellParamEquiv m hm))

/-- **T1:** the spatial action is a measurable embedding. -/
theorem measurableEmbedding_spAct (m : ℝ) (hm : 0 < m)
    (Λ : RestrictedLorentz) : MeasurableEmbedding (spAct m Λ) := by
  have h : ⇑(spActEquiv m hm Λ) = spAct m Λ :=
    funext (spActEquiv_apply m hm Λ)
  rw [← h]
  exact (spActEquiv m hm Λ).measurableEmbedding

/-!
## The spatial unitary and the intertwining identity
-/

/-- The spatial one-particle operator of a restricted Lorentz element:
pullback along the spatial action, as a linear isometry of
`spatialLp m` (it is one because `spAct` preserves `spatialMeasure m`). -/
noncomputable def spU (m : ℝ) (hm : 0 < m) (Λ : RestrictedLorentz) :
    spatialLp m →ₗᵢ[ℂ] spatialLp m where
  toFun := Lp.compMeasurePreserving (spAct m Λ) (measurePreserving_spAct m hm Λ)
  map_add' := fun X Y => map_add _ X Y
  map_smul' := fun c X => compMeasurePreserving_smul _ c X
  norm_map' := fun X => Lp.norm_compMeasurePreserving X _

/-- **T1:** the representative of the spatial unitary is the composed
representative, almost everywhere. -/
theorem spU_coeFn_ae (m : ℝ) (hm : 0 < m) (Λ : RestrictedLorentz)
    (X : spatialLp m) :
    (spU m hm Λ X : EuclideanSpace ℝ (Fin 3) → ℂ)
      =ᵐ[spatialMeasure m] X ∘ spAct m Λ :=
  Lp.coeFn_compMeasurePreserving X _

/-- **T1:** for a pure Lorentz element `⟨0, Λ⟩` (zero translation), the
one-particle function is the plain shell pullback along `Λ⁻¹`: the
phase factor is `exp (I·⟪0, p⟫) = 1`. -/
theorem oneParticleFun_zero (Λ : RestrictedLorentz) (m : ℝ) (hm : 0 < m)
    (ψ : massShell m → ℂ) (p : massShell m) :
    oneParticleFun ⟨0, Λ⟩ m hm ψ p = ψ (shellActR Λ⁻¹ m hm p) := by
  have h1 : oneParticleFun ⟨0, Λ⟩ m hm ψ p
      = phase (⟨0, Λ⟩ : RPoincare).trans p
        * ψ (shellActR (⟨0, Λ⟩ : RPoincare).lor⁻¹ m hm p) := rfl
  rw [h1]
  simp [phase, minkowskiInner]

/-- **T1 (the intertwining identity):** the graph parametrization
conjugates the shell Lorentz operator to the spatial unitary:
`shellLpEquiv (shellU1 ⟨0, Λ⟩ Ψ) = spU Λ (shellLpEquiv Ψ)`. Lorentz
strong continuity on the shell is therefore equivalent to Lorentz
strong continuity on the spatial side. -/
theorem shellLpEquiv_shellU1 (m : ℝ) (hm : 0 < m) (Λ : RestrictedLorentz)
    (Ψ : shellLp m hm) :
    shellLpEquiv m hm (shellU1 m hm ⟨0, Λ⟩ Ψ)
      = spU m hm Λ (shellLpEquiv m hm Ψ) := by
  apply Subtype.ext
  apply AEEqFun.ext
  have hpt : (oneParticleFun ⟨0, Λ⟩ m hm Ψ) ∘ ⇑(shellParamEquiv m hm)
      = (Ψ ∘ ⇑(shellParamEquiv m hm)) ∘ spAct m Λ := by
    funext u
    simp only [Function.comp_apply]
    rw [oneParticleFun_zero]
    have hmem : (Λ : LorentzGroup)⁻¹.toLin (shellParam m u) ∈ massShell m :=
      restricted_preserves_shell Λ⁻¹ _ m hm (shellParam_mem m hm u)
    have hsub : shellActR Λ⁻¹ m hm (shellParamEquiv m hm u)
        = shellParamEquiv m hm (spAct m Λ u) := by
      apply Subtype.ext
      show (Λ : LorentzGroup)⁻¹.toLin (shellParam m u)
        = shellParam m (spAct m Λ u)
      rw [show spAct m Λ u
          = spatialOf ((Λ : LorentzGroup)⁻¹.toLin (shellParam m u)) from rfl,
        shellParam_spatialOf m hm hmem]
    rw [hsub]
  calc (shellLpEquiv m hm (shellU1 m hm ⟨0, Λ⟩ Ψ) :
        EuclideanSpace ℝ (Fin 3) → ℂ)
      =ᵐ[spatialMeasure m] (shellU1 m hm ⟨0, Λ⟩ Ψ : massShell m → ℂ)
        ∘ ⇑(shellParamEquiv m hm) :=
        Lp.coeFn_compMeasurePreserving _ _
    _ =ᵐ[spatialMeasure m] (oneParticleFun ⟨0, Λ⟩ m hm Ψ)
        ∘ ⇑(shellParamEquiv m hm) :=
        (measurePreserving_shellParamEquiv m hm).quasiMeasurePreserving.ae_eq_comp
          (shellU1_coeFn_ae m hm ⟨0, Λ⟩ Ψ)
    _ =ᵐ[spatialMeasure m] (Ψ ∘ ⇑(shellParamEquiv m hm)) ∘ spAct m Λ :=
        Filter.EventuallyEq.of_eq hpt
    _ =ᵐ[spatialMeasure m] (shellLpEquiv m hm Ψ :
        EuclideanSpace ℝ (Fin 3) → ℂ) ∘ spAct m Λ :=
        (measurePreserving_spAct m hm Λ).quasiMeasurePreserving.ae_eq_comp
          (Lp.coeFn_compMeasurePreserving Ψ _).symm
    _ =ᵐ[spatialMeasure m] (spU m hm Λ (shellLpEquiv m hm Ψ) :
        EuclideanSpace ℝ (Fin 3) → ℂ) :=
        (spU_coeFn_ae m hm Λ _).symm

/-!
## The spatial measure is locally finite, and the `L²` norm as an integral
-/

/-- **T1:** the spatial measure `d³u/(2E_u)` is locally finite: it is the
Lebesgue measure with the continuous density `(2E_u)⁻¹`. (Local
finiteness on the σ-compact space `ℝ³` makes the measure regular,
which is what the `C_c`-density theorem consumes.) -/
theorem isLocallyFiniteMeasure_spatialMeasure (m : ℝ) (hm : 0 < m) :
    IsLocallyFiniteMeasure (spatialMeasure m) := by
  have hcong : spatialMeasure m
      = volume.withDensity (fun u => ENNReal.ofReal (2 * shellEnergy m u)⁻¹) := by
    apply withDensity_congr_ae
    refine Filter.Eventually.of_forall fun u => ?_
    exact (ENNReal.ofReal_inv_of_pos
      (mul_pos (by norm_num) (shellEnergy_pos hm u))).symm
  rw [hcong]
  exact IsLocallyFiniteMeasure.withDensity_ofReal
    ((continuous_const.mul (shellEnergy_continuous m)).inv₀
      (fun u => ne_of_gt (mul_pos (by norm_num) (shellEnergy_pos hm u))))

/-- **T1 (bridge):** for an `L²` element, the square of the norm is the
integral of the squared pointwise norm of any representative. -/
theorem lp_norm_sq_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (X : Lp ℂ 2 μ) : ‖X‖ ^ 2 = ∫ v, ‖(X : α → ℂ) v‖ ^ 2 ∂μ := by
  have hA : (∫ v, ‖(X : α → ℂ) v‖ ^ 2 ∂μ)
      = (∫⁻ v, ‖(X : α → ℂ) v‖ₑ ^ (2 : ℝ) ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun v => sq_nonneg ‖(X : α → ℂ) v‖)
      (((Lp.aestronglyMeasurable X).norm).pow 2)]
    congr 1
    apply lintegral_congr_ae
    refine Filter.Eventually.of_forall fun v => ?_
    show ENNReal.ofReal (‖(X : α → ℂ) v‖ ^ 2) = ‖(X : α → ℂ) v‖ₑ ^ (2 : ℝ)
    have e1 : ‖(X : α → ℂ) v‖ₑ ^ (2 : ℝ)
        = ENNReal.ofReal ‖(X : α → ℂ) v‖ * ENNReal.ofReal ‖(X : α → ℂ) v‖ := by
      rw [ENNReal.rpow_two, ← ofReal_norm, pow_two]
    rw [e1, ← ENNReal.ofReal_mul (norm_nonneg _), ← pow_two]
  have h12 : (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 := by norm_num
  rw [hA, Lp.norm_def,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (Lp.aestronglyMeasurable X), ENNReal.toReal_ofNat, ← ENNReal.toReal_rpow,
    ← Real.rpow_natCast ((∫⁻ v, ‖(X : α → ℂ) v‖ₑ ^ (2 : ℝ) ∂μ).toReal ^ (1 / 2 : ℝ)) 2,
    ← Real.rpow_mul ENNReal.toReal_nonneg, h12, Real.rpow_one]

/-!
## Pointwise continuity of the spatial action and the cross term
-/

/-- **T1:** for fixed `v`, the spatial action is continuous at the
identity in the inverted variable: `spAct Λ⁻¹ v → v` as `Λ → 1`. (This
is the pointwise input of the dominated convergence below; it holds
because `Λ ↦ Λ p` is continuous at `1` in the topology of pointwise
convergence, by definition of that topology.) -/
theorem tendsto_spAct_inv (m : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    Tendsto (fun Λ : RestrictedLorentz => spAct m Λ⁻¹ v) (𝓝 1) (𝓝 v) := by
  have h1 : Tendsto (fun Λ : RestrictedLorentz =>
      (Λ : LorentzGroup).toLin (shellParam m v)) (𝓝 1) (𝓝 (shellParam m v)) := by
    have h := (tendsto_restricted_iff (f := fun Λ : RestrictedLorentz => Λ)
      (Λ₀ := 1)).1 tendsto_id (shellParam m v)
    simpa using h
  have h2 := (continuous_spatialOf.tendsto _).comp h1
  rw [spatialOf_shellParam] at h2
  have hfun : (fun Λ : RestrictedLorentz => spAct m Λ⁻¹ v)
      = (fun Λ : RestrictedLorentz =>
        spatialOf ((Λ : LorentzGroup).toLin (shellParam m v))) := by
    funext Λ
    show spatialOf ((((Λ⁻¹ : RestrictedLorentz) : LorentzGroup)⁻¹).toLin
      (shellParam m v)) = _
    rw [Subgroup.coe_inv, inv_inv]
  rwa [hfun]

/-- **T1 (the dominated-convergence heart):** for `F` continuous with
compact support, the cross term of the squared-norm expansion is
continuous at the identity. The dominator is `B·‖F‖` with `B` a sup
bound of `F`: after the change of variables of `hnorm` (in
`spU_tendsto_of_continuous`), the integrand is `(starRingEnd ℂ) (F v) · F (spAct Λ⁻¹ v)`,
whose modulus is at most `B·‖F v‖`, and whose pointwise limit as
`Λ → 1` is `‖F v‖²` by `tendsto_spAct_inv`. No domination in `Λ` of the
moved factor is ever needed: this is the coefficient trick that makes
the Lorentz case work where the translations dominator `4‖ψ‖²` does
not. -/
theorem integral_cross_tendsto (m : ℝ) (hm : 0 < m)
    (F : EuclideanSpace ℝ (Fin 3) → ℂ) (hF : Continuous F)
    (hFc : HasCompactSupport F) :
    Tendsto (fun Λ : RestrictedLorentz =>
      ∫ v, ((starRingEnd ℂ) (F v) * F (spAct m Λ⁻¹ v)).re ∂(spatialMeasure m))
      (𝓝 1) (𝓝 (∫ v, ‖F v‖ ^ 2 ∂(spatialMeasure m))) := by
  obtain ⟨B, hB⟩ := hF.bounded_above_of_compact_support hFc
  haveI := isLocallyFiniteMeasure_spatialMeasure m hm
  have hFint : Integrable F (spatialMeasure m) :=
    hF.integrable_of_hasCompactSupport hFc
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun v => B * ‖F v‖)
  · refine Filter.Eventually.of_forall fun Λ => ?_
    exact (Complex.continuous_re.comp ((Complex.continuous_conj.comp hF).mul
      (hF.comp (continuous_spAct m Λ⁻¹)))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun Λ =>
      Filter.Eventually.of_forall fun v => ?_
    rw [Real.norm_eq_abs]
    calc |((starRingEnd ℂ) (F v) * F (spAct m Λ⁻¹ v)).re|
        ≤ ‖(starRingEnd ℂ) (F v) * F (spAct m Λ⁻¹ v)‖ := Complex.abs_re_le_norm _
      _ = ‖F v‖ * ‖F (spAct m Λ⁻¹ v)‖ := by rw [norm_mul, RCLike.norm_conj]
      _ ≤ ‖F v‖ * B := mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
      _ = B * ‖F v‖ := mul_comm _ _
  · exact hFint.norm.const_mul B
  · refine Filter.Eventually.of_forall fun v => ?_
    have hpt : Tendsto (fun Λ : RestrictedLorentz => spAct m Λ⁻¹ v) (𝓝 1)
        (𝓝 v) := tendsto_spAct_inv m v
    have h1 : Tendsto (fun Λ : RestrictedLorentz =>
        (starRingEnd ℂ) (F v) * F (spAct m Λ⁻¹ v)) (𝓝 1) (𝓝 ((starRingEnd ℂ) (F v) * F v)) :=
      tendsto_const_nhds.mul ((hF.tendsto v).comp hpt)
    have h2 := (Complex.continuous_re.tendsto _).comp h1
    have h3 : ((starRingEnd ℂ) (F v) * F v).re = ‖F v‖ ^ 2 := by
      rw [mul_comm ((starRingEnd ℂ) (F v)) (F v), Complex.mul_conj,
        Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    rw [h3] at h2
    exact h2

/-!
## Strong continuity: dense class first, then the ε/3 extension
-/

/-- **T1 (continuity on the dense class):** for `F` continuous with
compact support, `spU Λ Ǧ → Ǧ` as `Λ → 1`, where `Ǧ` is the `L²`
element of `F`. Proved by the squared-norm identity
`‖spU Λ Ǧ − Ǧ‖² = ∫ ‖F v − F (spAct Λ⁻¹ v)‖²` (one change of variables
moves `Λ` onto the fixed factor), the expansion of the square, and
`integral_cross_tendsto`. -/
theorem spU_tendsto_of_continuous (m : ℝ) (hm : 0 < m)
    (F : EuclideanSpace ℝ (Fin 3) → ℂ) (hF : Continuous F)
    (hFc : HasCompactSupport F) (hFmem : MemLp F 2 (spatialMeasure m)) :
    Tendsto (fun Λ : RestrictedLorentz => spU m hm Λ (hFmem.toLp F)) (𝓝 1)
      (𝓝 (hFmem.toLp F)) := by
  haveI := isLocallyFiniteMeasure_spatialMeasure m hm
  obtain ⟨B, hB⟩ := hF.bounded_above_of_compact_support hFc
  have hFint : Integrable F (spatialMeasure m) :=
    hF.integrable_of_hasCompactSupport hFc
  have hnorm : ∀ Λ : RestrictedLorentz,
      ‖spU m hm Λ (hFmem.toLp F) - hFmem.toLp F‖ ^ 2
        = ∫ v, ‖F v - F (spAct m Λ⁻¹ v)‖ ^ 2 ∂(spatialMeasure m) := by
    intro Λ
    have hrep : ((spU m hm Λ (hFmem.toLp F) - hFmem.toLp F : spatialLp m) :
        EuclideanSpace ℝ (Fin 3) → ℂ)
        =ᵐ[spatialMeasure m] fun v => F (spAct m Λ v) - F v := by
      calc ((spU m hm Λ (hFmem.toLp F) - hFmem.toLp F : spatialLp m) :
            EuclideanSpace ℝ (Fin 3) → ℂ)
          =ᵐ[spatialMeasure m] (spU m hm Λ (hFmem.toLp F) :
              EuclideanSpace ℝ (Fin 3) → ℂ)
              - ((hFmem.toLp F : spatialLp m) : EuclideanSpace ℝ (Fin 3) → ℂ) :=
            Lp.coeFn_sub _ _
        _ =ᵐ[spatialMeasure m] fun v => F (spAct m Λ v) - F v := by
            apply Filter.EventuallyEq.sub
            · exact (spU_coeFn_ae m hm Λ (hFmem.toLp F)).trans
                ((measurePreserving_spAct m hm Λ).quasiMeasurePreserving.ae_eq_comp
                  (MemLp.coeFn_toLp hFmem))
            · exact MemLp.coeFn_toLp hFmem
    have hsub : (∫ v, ‖F (spAct m Λ v) - F v‖ ^ 2 ∂(spatialMeasure m))
        = ∫ v, ‖F v - F (spAct m Λ⁻¹ v)‖ ^ 2 ∂(spatialMeasure m) := by
      have h := (measurePreserving_spAct m hm Λ).integral_comp
        (measurableEmbedding_spAct m hm Λ)
        (g := fun u => ‖F u - F (spAct m Λ⁻¹ u)‖ ^ 2)
      rw [← h]
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      have hv : spAct m Λ⁻¹ (spAct m Λ v) = v :=
        congrFun (spAct_inv_comp_self m hm Λ) v
      show ‖F (spAct m Λ v) - F v‖ ^ 2
        = ‖F (spAct m Λ v) - F (spAct m Λ⁻¹ (spAct m Λ v))‖ ^ 2
      rw [hv]
    rw [lp_norm_sq_eq_integral,
      integral_congr_ae (hrep.mono fun v hv => by rw [hv])]
    exact hsub
  have hexp : ∀ Λ : RestrictedLorentz,
      (∫ v, ‖F v - F (spAct m Λ⁻¹ v)‖ ^ 2 ∂(spatialMeasure m))
        = (∫ v, ‖F v‖ ^ 2 ∂(spatialMeasure m))
          - 2 * (∫ v, ((starRingEnd ℂ) (F v) * F (spAct m Λ⁻¹ v)).re ∂(spatialMeasure m))
          + (∫ v, ‖F v‖ ^ 2 ∂(spatialMeasure m)) := by
    intro Λ
    have hI1 : Integrable (fun v => ‖F v‖ ^ 2) (spatialMeasure m) := by
      have h := hFmem.integrable_norm_rpow (by norm_num) (by norm_num)
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
    have hI3 : Integrable (fun v => ‖F (spAct m Λ⁻¹ v)‖ ^ 2)
        (spatialMeasure m) := by
      have h := (hFmem.comp_measurePreserving
        (measurePreserving_spAct m hm Λ⁻¹)).integrable_norm_rpow
        (by norm_num) (by norm_num)
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Function.comp_apply] using h
    have hI2 : Integrable (fun v => ((starRingEnd ℂ) (F v) * F (spAct m Λ⁻¹ v)).re)
        (spatialMeasure m) := by
      apply Integrable.mono' (g := fun v => ‖F v‖ * B)
      · exact hFint.norm.mul_const B
      · exact (Complex.continuous_re.comp
          ((Complex.continuous_conj.comp hF).mul
            (hF.comp (continuous_spAct m Λ⁻¹)))).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun v => ?_
        calc ‖((starRingEnd ℂ) (F v) * F (spAct m Λ⁻¹ v)).re‖
            = |((starRingEnd ℂ) (F v) * F (spAct m Λ⁻¹ v)).re| := Real.norm_eq_abs _
          _ ≤ ‖(starRingEnd ℂ) (F v) * F (spAct m Λ⁻¹ v)‖ := Complex.abs_re_le_norm _
          _ = ‖F v‖ * ‖F (spAct m Λ⁻¹ v)‖ := by rw [norm_mul, RCLike.norm_conj]
          _ ≤ ‖F v‖ * B := mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
    have hpt : ∀ v, ‖F v - F (spAct m Λ⁻¹ v)‖ ^ 2
        = ‖F v‖ ^ 2 - 2 * ((starRingEnd ℂ) (F v) * F (spAct m Λ⁻¹ v)).re
          + ‖F (spAct m Λ⁻¹ v)‖ ^ 2 := by
      intro v
      have hre : RCLike.re ((starRingEnd ℂ) (F v) * F (spAct m Λ⁻¹ v))
          = ((starRingEnd ℂ) (F v) * F (spAct m Λ⁻¹ v)).re := rfl
      rw [norm_sub_sq (𝕜 := ℂ) (F v) (F (spAct m Λ⁻¹ v)), RCLike.inner_apply', hre]
    have hI12 : Integrable (fun a => ‖F a‖ ^ 2
        - 2 * ((starRingEnd ℂ) (F a) * F (spAct m Λ⁻¹ a)).re)
        (spatialMeasure m) := hI1.sub (hI2.const_mul 2)
    nth_rewrite 2 [((measurePreserving_spAct m hm Λ⁻¹).integral_comp
      (measurableEmbedding_spAct m hm Λ⁻¹) (fun v => ‖F v‖ ^ 2)).symm]
    rw [← integral_const_mul, ← integral_sub hI1 (hI2.const_mul 2),
      ← integral_add hI12 hI3]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have key : Tendsto (fun Λ : RestrictedLorentz =>
      ‖spU m hm Λ (hFmem.toLp F) - hFmem.toLp F‖ ^ 2) (𝓝 1) (𝓝 0) := by
    have hC := integral_cross_tendsto m hm F hF hFc
    have hlim : Tendsto (fun Λ : RestrictedLorentz =>
        (∫ v, ‖F v‖ ^ 2 ∂(spatialMeasure m))
          - 2 * (∫ v, ((starRingEnd ℂ) (F v) * F (spAct m Λ⁻¹ v)).re ∂(spatialMeasure m))
          + (∫ v, ‖F v‖ ^ 2 ∂(spatialMeasure m))) (𝓝 1) (𝓝 0) := by
      have h0 : (∫ v, ‖F v‖ ^ 2 ∂(spatialMeasure m))
          - 2 * (∫ v, ‖F v‖ ^ 2 ∂(spatialMeasure m))
          + (∫ v, ‖F v‖ ^ 2 ∂(spatialMeasure m)) = 0 := by ring
      rw [← h0]
      exact ((tendsto_const_nhds.sub
        ((tendsto_const_nhds (x := (2 : ℝ))).mul hC)).add tendsto_const_nhds)
    exact hlim.congr' (Filter.Eventually.of_forall fun Λ =>
      ((hnorm Λ).trans (hexp Λ)).symm)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm0 : Tendsto (fun Λ : RestrictedLorentz =>
      ‖spU m hm Λ (hFmem.toLp F) - hFmem.toLp F‖) (𝓝 1) (𝓝 0) := by
    have h : Tendsto (fun Λ : RestrictedLorentz =>
        Real.sqrt (‖spU m hm Λ (hFmem.toLp F) - hFmem.toLp F‖ ^ 2)) (𝓝 1)
        (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp key
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h
  exact hnorm0

/-- **T1 (spatial strong continuity at the identity):** for every
`Φ : spatialLp m`, `spU Λ Φ → Φ` as `Λ → 1` in the restricted Lorentz
group. The ε/3 extension from the dense class of continuous
compactly-supported functions (`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`,
using regularity of the spatial measure) by unitarity: every `spU Λ`
is a linear isometry, so the approximation error is transported, not
amplified. -/
theorem spU_tendsto (m : ℝ) (hm : 0 < m) (Φ : spatialLp m) :
    Tendsto (fun Λ : RestrictedLorentz => spU m hm Λ Φ) (𝓝 1) (𝓝 Φ) := by
  haveI := isLocallyFiniteMeasure_spatialMeasure m hm
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨G, hGc, hGle, hGcont, hGmem⟩ :=
    (Lp.memLp Φ).exists_hasCompactSupport_eLpNorm_sub_le (p := 2) (by norm_num)
      (ε := ENNReal.ofReal (ε / 3))
      ((ENNReal.ofReal_pos.mpr (by linarith)).ne')
  have hΦG : ‖Φ - hGmem.toLp G‖ ≤ ε / 3 := by
    have h2 : ‖Φ - hGmem.toLp G‖
        = (eLpNorm (⇑Φ - G) 2 (spatialMeasure m)).toReal := by
      conv_lhs => rw [← Lp.toLp_coeFn Φ (Lp.memLp Φ)]
      rw [← MemLp.toLp_sub, Lp.norm_toLp]
    rw [h2]
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hGle).trans_eq ?_
    rw [ENNReal.toReal_ofReal (by linarith)]
  have hev : ∀ᶠ Λ in 𝓝 (1 : RestrictedLorentz),
      ‖spU m hm Λ (hGmem.toLp G) - hGmem.toLp G‖ < ε / 3 := by
    have h := (Metric.tendsto_nhds.1 (tendsto_iff_norm_sub_tendsto_zero.1
      (spU_tendsto_of_continuous m hm G hGcont hGc hGmem))) (ε / 3) (by linarith)
    simpa using h
  filter_upwards [hev] with Λ hΛ
  calc dist (spU m hm Λ Φ) Φ = ‖spU m hm Λ Φ - Φ‖ := dist_eq_norm _ _
    _ ≤ ‖spU m hm Λ Φ - spU m hm Λ (hGmem.toLp G)‖
        + ‖spU m hm Λ (hGmem.toLp G) - hGmem.toLp G‖ + ‖hGmem.toLp G - Φ‖ := by
        have e : spU m hm Λ Φ - Φ = (spU m hm Λ Φ - spU m hm Λ (hGmem.toLp G))
            + (spU m hm Λ (hGmem.toLp G) - hGmem.toLp G) + (hGmem.toLp G - Φ) := by
          abel
        rw [e]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖Φ - hGmem.toLp G‖ + ‖spU m hm Λ (hGmem.toLp G) - hGmem.toLp G‖
        + ‖hGmem.toLp G - Φ‖ := by
        rw [← map_sub, (spU m hm Λ).norm_map]
    _ < ε / 3 + ε / 3 + ε / 3 :=
        add_lt_add_of_lt_of_le (add_lt_add_of_le_of_lt hΦG hΛ)
          (by rwa [norm_sub_rev])
    _ = ε := by ring

/-!
## The headline theorems, back on the mass shell
-/

/-- **T1 — HEADLINE (Lorentz strong continuity at the identity):** for
every one-particle state `Ψ` on the mass shell, the Lorentz subgroup
action is strongly continuous at the identity: `shellU1 ⟨0, Λ⟩ Ψ → Ψ`
as `Λ → 1` in the restricted Lorentz group (topology of pointwise
convergence). Together with `TranslationContinuity` (translations),
this discharges the strong-continuity window of the one-particle
Poincaré representation at the subgroup level. -/
theorem shellU1_lorentz_tendsto (m : ℝ) (hm : 0 < m) (Ψ : shellLp m hm) :
    Tendsto (fun Λ : RestrictedLorentz => shellU1 m hm ⟨0, Λ⟩ Ψ) (𝓝 1)
      (𝓝 Ψ) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ Λ : RestrictedLorentz,
      ‖shellU1 m hm ⟨0, Λ⟩ Ψ - Ψ‖
        = ‖spU m hm Λ (shellLpEquiv m hm Ψ) - shellLpEquiv m hm Ψ‖ := by
    intro Λ
    have h1 : shellU1 m hm ⟨0, Λ⟩ Ψ - Ψ
        = (shellLpEquiv m hm).symm
          (spU m hm Λ (shellLpEquiv m hm Ψ) - shellLpEquiv m hm Ψ) := by
      rw [map_sub, ← shellLpEquiv_shellU1 m hm Λ Ψ,
        LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply]
    rw [h1, LinearIsometryEquiv.norm_map]
  exact (tendsto_iff_norm_sub_tendsto_zero.1
    (spU_tendsto m hm (shellLpEquiv m hm Ψ))).congr (fun Λ => (hnorm Λ).symm)

/-- **T1 — HEADLINE (Lorentz strong continuity at every point):** the
group law transports continuity at the identity to every `Λ₀`:
`shellU1 ⟨0, Λ⟩ Ψ → shellU1 ⟨0, Λ₀⟩ Ψ` as `Λ → Λ₀`, via the
factorization `⟨0, Λ⟩ = ⟨0, Λ₀⟩ * ⟨0, Λ₀⁻¹ * Λ⟩` and
`tendsto_restricted_inv_mul`. -/
theorem shellU1_lorentz_tendsto_at (m : ℝ) (hm : 0 < m) (Λ₀ : RestrictedLorentz)
    (Ψ : shellLp m hm) :
    Tendsto (fun Λ : RestrictedLorentz => shellU1 m hm ⟨0, Λ⟩ Ψ) (𝓝 Λ₀)
      (𝓝 (shellU1 m hm ⟨0, Λ₀⟩ Ψ)) := by
  have hfac : ∀ Λ : RestrictedLorentz, shellU1 m hm ⟨0, Λ⟩ Ψ
      = shellU1 m hm ⟨0, Λ₀⟩ (shellU1 m hm ⟨0, Λ₀⁻¹ * Λ⟩ Ψ) := by
    intro Λ
    have hgrp : (⟨0, Λ₀⟩ : RPoincare) * ⟨0, Λ₀⁻¹ * Λ⟩ = ⟨0, Λ⟩ := by
      apply RPoincare.ext
      · show (0 : Minkowski) + (Λ₀ : LorentzGroup).toLin 0 = 0
        rw [map_zero, add_zero]
      · show Λ₀ * (Λ₀⁻¹ * Λ) = Λ
        rw [← mul_assoc, mul_inv_cancel, one_mul]
    calc shellU1 m hm ⟨0, Λ⟩ Ψ
        = shellU1 m hm ((⟨0, Λ₀⟩ : RPoincare) * ⟨0, Λ₀⁻¹ * Λ⟩) Ψ := by
          rw [hgrp]
      _ = shellU1 m hm ⟨0, Λ₀⟩ (shellU1 m hm ⟨0, Λ₀⁻¹ * Λ⟩ Ψ) :=
          shellU1_apply_mul m hm _ _ _
  have hcomp : Tendsto (fun Λ : RestrictedLorentz =>
      shellU1 m hm ⟨0, Λ₀⟩ (shellU1 m hm ⟨0, Λ₀⁻¹ * Λ⟩ Ψ)) (𝓝 Λ₀)
      (𝓝 (shellU1 m hm ⟨0, Λ₀⟩ Ψ)) := by
    have h1 : Tendsto (fun Λ : RestrictedLorentz =>
        shellU1 m hm ⟨0, Λ₀⁻¹ * Λ⟩ Ψ) (𝓝 Λ₀) (𝓝 Ψ) :=
      (shellU1_lorentz_tendsto m hm Ψ).comp (tendsto_restricted_inv_mul Λ₀)
    exact ((shellU1 m hm ⟨0, Λ₀⟩).continuous.tendsto Ψ).comp h1
  exact Tendsto.congr (fun Λ => (hfac Λ).symm) hcomp

end ThetLogos
