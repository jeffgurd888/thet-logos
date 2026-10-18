/-
# Fock packaging, step 0 + step (ii): the one-particle unitary and its ONB

COMMISSION — FOCK PACKAGING (Rung 7 remainder, packaging half), gauntlet
`whitepaper/gauntlet-parked-fleet-2026-10-17.md` §4b: STANDS at price M,
route pinned to the **concrete ONB port**. Kill K4 stands permanently:
the abstract `SymmetricAlgebra` route is dead (Mathlib has no inner
product on `SymmetricAlgebra ℂ V` satisfying the permanent formula) and
is NOT revived anywhere in this campaign.

This module is the fence-neutral shell side, imported by both statistic
modules (`FockPackagingBos`, `FockPackagingFerm`). At packaging time
the two could not be co-imported with each other
(`numberOp`/`numberOp_basis` collided between `FermionicFock` and
`BosonicAssembly`); that fence is HISTORICAL — discharged 2026-10-18
by the `numberOpBos` rename, and the packaging-level helper
collisions by the six-name packaging rename (dossiers
`whitepaper/numberop-rename-2026-10-18.md` and
`whitepaper/packaging-rename-2026-10-18.md`). `FockCoImport.lean`
now imports both statistic modules in one environment.

CONTENTS.
* Step (i) (gauntlet price S, mechanical): the one-particle action
  `oneParticleFun` of `MassShellMeasure.lean` packaged as a genuine
  linear isometry equivalence `shellU1 g : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm`
  of the mass-shell L² space, via `MemLp.toLp` exactly as the blocked
  note at the end of `MassShellMeasure.lean` prescribes. The measure
  preservation input is discharged for the FULL restricted Lorentz group
  by `boostInvariance_window_proved` (MassShellBoost, T1).
  Representation law `shellU1_mul`, identity `shellU1_one`.
* Strong continuity of the translation subgroup, transported from the
  discharged one-particle window (`TranslationContinuity.lean`, T1):
  `shellU1_translation_tendsto`.
* Step (ii) (gauntlet price S): a concrete `HilbertBasis ℕ ℂ` of the
  shell space: `shellONB`. Concreteness: the basis is indexed by `ℕ`
  (the mode index of the Pitch 2 Fock carriers) and is obtained from the
  maximal-orthonormal-set basis by an explicit cardinality transport
  (`ℕ ≃ ↥w` from separability + infinite-dimensionality, both proved
  here for the shell space).

FENCES.
* The group is `RPoincare` (translations ⋊ RESTRICTED Lorentz group) —
  the group the corpus's shell representation actually lives on. The
  T5 window `SecondQuantization_window` of `PoincareAction.lean` is
  stated over the unrestricted `PoincareGroup`; no corpus one-particle
  representation over the full group exists, so the packaging is over
  `RPoincare` and the window is NOT discharged as stated (see dossier).
* Lorentz strong continuity is NOT proved here and is NOT implied by
  the translation transport (the dominated-convergence argument rests
  on the shell action being trivial for pure translations). It remains
  its own priced line item (S–M) in the ratified queue.
-/

import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.l2Space
import ThetLogos.MassShellMeasure
import ThetLogos.MassShellBoost
import ThetLogos.TranslationContinuity

namespace ThetLogos

open MeasureTheory Filter Topology
open scoped InnerProductSpace

/-- The mass-shell one-particle space: `L²` of the invariant shell
measure. (An abbreviation for the corpus's own `Lp` space, not a new
carrier.) -/
abbrev shellLp (m : ℝ) (hm : 0 < m) : Type :=
  Lp ℂ 2 (massShellMeasure m hm)

/-- **T1:** the shell action of every restricted Lorentz element is
measure-preserving for the shell measure. The rotation factors are T1
in `MassShellMeasure`; the boost factor and the assembly over the full
restricted group are `boostInvariance_window_proved` (MassShellBoost). -/
theorem measurePreserving_shellActR (Λ : RestrictedLorentz) (m : ℝ) (hm : 0 < m) :
    MeasurePreserving (shellActR Λ m hm) (massShellMeasure m hm)
      (massShellMeasure m hm) :=
  boostInvariance_window_proved m hm Λ

/-- The `MemLp` witness for the one-particle action applied to an `Lp`
element: `oneParticleFun` preserves the shell `L²` class because the
shell action is measure-preserving. -/
theorem memLp_oneParticleFun_Lp (g : RPoincare) (m : ℝ) (hm : 0 < m)
    (Ψ : shellLp m hm) :
    MemLp (oneParticleFun g m hm Ψ) 2 (massShellMeasure m hm) :=
  memLp_oneParticleFun g m hm
    (measurePreserving_shellActR g.lor⁻¹ m hm) Ψ (Lp.memLp Ψ)

/-- **T1 (a.e. congruence):** `oneParticleFun` respects a.e. equality of
its input — the measure-preserving shell action pulls a.e. equality
back along itself. -/
theorem oneParticleFun_congr_ae (g : RPoincare) (m : ℝ) (hm : 0 < m)
    {ψ φ : massShell m → ℂ} (h : ψ =ᵐ[massShellMeasure m hm] φ) :
    oneParticleFun g m hm ψ =ᵐ[massShellMeasure m hm] oneParticleFun g m hm φ := by
  have h' := (measurePreserving_shellActR g.lor⁻¹ m hm).quasiMeasurePreserving.ae_eq_comp h
  -- h' : ψ ∘ shellActR g.lor⁻¹ =ᵐ φ ∘ shellActR g.lor⁻¹
  filter_upwards [h'] with p hp
  simp only [Function.comp_apply] at hp
  simp only [oneParticleFun, hp]

/-- **T1:** `oneParticleFun` is additive in the wavefunction (pointwise). -/
theorem oneParticleFun_add (g : RPoincare) (m : ℝ) (hm : 0 < m)
    (ψ φ : massShell m → ℂ) :
    oneParticleFun g m hm (ψ + φ) = oneParticleFun g m hm ψ + oneParticleFun g m hm φ := by
  funext p
  simp only [oneParticleFun, Pi.add_apply, mul_add]

/-- **T1:** `oneParticleFun` is homogeneous in the wavefunction (pointwise). -/
theorem oneParticleFun_smul (g : RPoincare) (m : ℝ) (hm : 0 < m) (c : ℂ)
    (ψ : massShell m → ℂ) :
    oneParticleFun g m hm (c • ψ) = c • oneParticleFun g m hm ψ := by
  funext p
  simp only [oneParticleFun, Pi.smul_apply, smul_eq_mul]
  ring

/-- **T1:** the identity group element acts as the identity function. -/
theorem oneParticleFun_one (m : ℝ) (hm : 0 < m) (ψ : massShell m → ℂ) :
    oneParticleFun (1 : RPoincare) m hm ψ = ψ := by
  funext p
  have hlor : (1 : RPoincare).lor = 1 := rfl
  have htrans : (1 : RPoincare).trans = 0 := rfl
  simp only [oneParticleFun, hlor, htrans, inv_one]
  rw [shellActR_one]
  simp [phase, minkowskiInner]

/-- **Step (i) — T1:** the packaged one-particle unitary. For
`g : RPoincare`, `shellU1 g` is the linear isometry equivalence of the
mass-shell `L²` space induced by `oneParticleFun g`, built with
`MemLp.toLp` per the `MassShellMeasure` blocked note. Its underlying
function is a.e. `oneParticleFun g` applied to any representative
(`shellU1_coeFn_ae`). -/
noncomputable def shellU1 (m : ℝ) (hm : 0 < m) (g : RPoincare) :
    shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm where
  toLinearEquiv :=
    { toFun := fun Ψ => (memLp_oneParticleFun_Lp g m hm Ψ).toLp _
      invFun := fun Ψ => (memLp_oneParticleFun_Lp g⁻¹ m hm Ψ).toLp _
      map_add' := by
        intro Ψ Φ
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        calc oneParticleFun g m hm (Ψ + Φ : shellLp m hm)
            =ᵐ[massShellMeasure m hm] oneParticleFun g m hm (Ψ + Φ : massShell m → ℂ) :=
              oneParticleFun_congr_ae g m hm (Lp.coeFn_add Ψ Φ)
          _ = oneParticleFun g m hm Ψ + oneParticleFun g m hm Φ :=
              oneParticleFun_add g m hm Ψ Φ
      map_smul' := by
        intro c Ψ
        simp only [RingHom.id_apply]
        conv_rhs => rw [← Lp.toLp_coeFn (c • (memLp_oneParticleFun_Lp g m hm Ψ).toLp _)
          (Lp.memLp _)]
        apply MemLp.toLp_congr
        calc oneParticleFun g m hm (c • Ψ : shellLp m hm)
            =ᵐ[massShellMeasure m hm] oneParticleFun g m hm (c • (Ψ : massShell m → ℂ)) :=
              oneParticleFun_congr_ae g m hm (Lp.coeFn_smul c Ψ)
          _ = c • oneParticleFun g m hm Ψ := oneParticleFun_smul g m hm c Ψ
          _ =ᵐ[massShellMeasure m hm]
              c • ((memLp_oneParticleFun_Lp g m hm Ψ).toLp _ : massShell m → ℂ) := by
              filter_upwards [MemLp.coeFn_toLp (memLp_oneParticleFun_Lp g m hm Ψ)] with p hp
              simp only [Pi.smul_apply, smul_eq_mul, hp]
          _ =ᵐ[massShellMeasure m hm]
              (c • (memLp_oneParticleFun_Lp g m hm Ψ).toLp _ : shellLp m hm) :=
              (Lp.coeFn_smul c _).symm
      left_inv := by
        intro Ψ
        conv_rhs => rw [← Lp.toLp_coeFn Ψ (Lp.memLp Ψ)]
        apply MemLp.toLp_congr
        calc oneParticleFun g⁻¹ m hm ((memLp_oneParticleFun_Lp g m hm Ψ).toLp _)
            =ᵐ[massShellMeasure m hm] oneParticleFun g⁻¹ m hm (oneParticleFun g m hm Ψ) :=
              oneParticleFun_congr_ae g⁻¹ m hm (MemLp.coeFn_toLp _)
          _ = oneParticleFun (g⁻¹ * g) m hm Ψ := (oneParticleFun_mul g⁻¹ g m hm Ψ).symm
          _ = Ψ := by rw [inv_mul_cancel, oneParticleFun_one]
      right_inv := by
        intro Ψ
        conv_rhs => rw [← Lp.toLp_coeFn Ψ (Lp.memLp Ψ)]
        apply MemLp.toLp_congr
        calc oneParticleFun g m hm ((memLp_oneParticleFun_Lp g⁻¹ m hm Ψ).toLp _)
            =ᵐ[massShellMeasure m hm] oneParticleFun g m hm (oneParticleFun g⁻¹ m hm Ψ) :=
              oneParticleFun_congr_ae g m hm (MemLp.coeFn_toLp _)
          _ = oneParticleFun (g * g⁻¹) m hm Ψ := (oneParticleFun_mul g g⁻¹ m hm Ψ).symm
          _ = Ψ := by rw [mul_inv_cancel, oneParticleFun_one] }
  norm_map' := by
    intro Ψ
    show ‖(memLp_oneParticleFun_Lp g m hm Ψ).toLp (oneParticleFun g m hm Ψ)‖ = ‖Ψ‖
    rw [Lp.norm_toLp,
      eLpNorm_oneParticleFun g m hm (measurePreserving_shellActR g.lor⁻¹ m hm) Ψ
        (Lp.memLp Ψ)]
    conv_rhs => rw [← Lp.toLp_coeFn Ψ (Lp.memLp Ψ), Lp.norm_toLp]

/-- **T1:** the packaged operator's representative is a.e. the corpus's
one-particle function. This is the bridge identity used by every
downstream computation. -/
theorem shellU1_coeFn_ae (m : ℝ) (hm : 0 < m) (g : RPoincare) (Ψ : shellLp m hm) :
    (shellU1 m hm g Ψ : massShell m → ℂ) =ᵐ[massShellMeasure m hm]
      oneParticleFun g m hm Ψ :=
  MemLp.coeFn_toLp (memLp_oneParticleFun_Lp g m hm Ψ)

/-- **T1 (representation law, packaged):** `shellU1` is a homomorphism
in the group argument. Stated in Mathlib's `LinearIsometryEquiv.trans`
order: `(e₂.trans e₁) x = e₁ (e₂ x)`, so the trans form of
`U (g₁ * g₂) = U g₁ ∘ U g₂` is `(shellU1 g₂).trans (shellU1 g₁)`.
(Noted for the dossier: the T5 window `SecondQuantization_window` in
`PoincareAction.lean` writes the trans factors in the opposite order;
read literally with Mathlib's `trans`, that clause is the
anti-homomorphism law. The representation content is the applied law
proved here and in `shellU1_apply_mul`.) -/
theorem shellU1_mul (m : ℝ) (hm : 0 < m) (g₁ g₂ : RPoincare) :
    shellU1 m hm (g₁ * g₂) = (shellU1 m hm g₂).trans (shellU1 m hm g₁) := by
  apply LinearIsometryEquiv.ext
  intro Ψ
  rw [LinearIsometryEquiv.trans_apply]
  conv_rhs => rw [← Lp.toLp_coeFn (shellU1 m hm g₁ (shellU1 m hm g₂ Ψ)) (Lp.memLp _)]
  apply MemLp.toLp_congr (memLp_oneParticleFun_Lp (g₁ * g₂) m hm Ψ) (Lp.memLp _)
  calc oneParticleFun (g₁ * g₂) m hm Ψ
      = oneParticleFun g₁ m hm (oneParticleFun g₂ m hm Ψ) :=
        oneParticleFun_mul g₁ g₂ m hm Ψ
    _ =ᵐ[massShellMeasure m hm] oneParticleFun g₁ m hm (shellU1 m hm g₂ Ψ) :=
        oneParticleFun_congr_ae g₁ m hm (shellU1_coeFn_ae m hm g₂ Ψ).symm
    _ =ᵐ[massShellMeasure m hm] (shellU1 m hm g₁ (shellU1 m hm g₂ Ψ) : massShell m → ℂ) :=
        (shellU1_coeFn_ae m hm g₁ _).symm

/-- **T1 (representation law, applied form):**
`shellU1 (g₁ * g₂) Ψ = shellU1 g₁ (shellU1 g₂ Ψ)`. -/
theorem shellU1_apply_mul (m : ℝ) (hm : 0 < m) (g₁ g₂ : RPoincare) (Ψ : shellLp m hm) :
    shellU1 m hm (g₁ * g₂) Ψ = shellU1 m hm g₁ (shellU1 m hm g₂ Ψ) := by
  have h := shellU1_mul m hm g₁ g₂
  rw [h, LinearIsometryEquiv.trans_apply]

/-- **T1:** the packaged operator of the identity is the identity. -/
theorem shellU1_one (m : ℝ) (hm : 0 < m) :
    shellU1 m hm (1 : RPoincare) = LinearIsometryEquiv.refl ℂ (shellLp m hm) := by
  apply LinearIsometryEquiv.ext
  intro Ψ
  show (memLp_oneParticleFun_Lp 1 m hm Ψ).toLp (oneParticleFun 1 m hm Ψ) = Ψ
  conv_rhs => rw [← Lp.toLp_coeFn Ψ (Lp.memLp Ψ)]
  apply MemLp.toLp_congr
  rw [oneParticleFun_one]

/-- **T1 (strong continuity of translations, transported):** for every
one-particle state `Ψ`, the packaged translation action
`a ↦ shellU1 ⟨a, 1⟩ Ψ` is continuous at `a = 0`. Transport of the
discharged window `strongContinuity_window_proved`
(`TranslationContinuity.lean`) through the `MemLp.toLp` packaging: the
`eLpNorm` of the difference representative is exactly the window's
integrand. The Lorentz half of strong continuity does NOT follow and is
not claimed (see header fence). -/
theorem shellU1_translation_tendsto (m : ℝ) (hm : 0 < m) (Ψ : shellLp m hm) :
    Tendsto (fun a : Minkowski => shellU1 m hm ⟨a, 1⟩ Ψ) (nhds 0) (nhds Ψ) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- It suffices that the norm of the difference tends to 0.
  have key : Tendsto (fun a : Minkowski =>
      eLpNorm ((shellU1 m hm ⟨a, 1⟩ Ψ - Ψ : shellLp m hm) : massShell m → ℂ)
        2 (massShellMeasure m hm)) (nhds 0) (nhds 0) := by
    have hwin := strongContinuity_window_proved m hm Ψ (Lp.memLp Ψ)
    apply Tendsto.congr' _ hwin
    filter_upwards with a
    apply eLpNorm_congr_ae
    filter_upwards [shellU1_coeFn_ae m hm ⟨a, 1⟩ Ψ,
      Lp.coeFn_sub (shellU1 m hm ⟨a, 1⟩ Ψ) Ψ] with p hp hsub
    rw [hsub, Pi.sub_apply, hp]
  -- Convert eLpNorm convergence to norm convergence in `Lp`
  -- (`‖X‖ = (eLpNorm ⇑X 2 μ).toReal` for `Lp` elements).
  have hnorm : ∀ X : shellLp m hm, ‖X‖ =
      (eLpNorm (X : massShell m → ℂ) 2 (massShellMeasure m hm)).toReal := by
    intro X
    conv_lhs => rw [← Lp.toLp_coeFn X (Lp.memLp X), Lp.norm_toLp]
  have step1 : Tendsto (fun a : Minkowski =>
      (eLpNorm ((shellU1 m hm ⟨a, 1⟩ Ψ - Ψ : shellLp m hm) : massShell m → ℂ)
        2 (massShellMeasure m hm)).toReal) (nhds 0) (nhds 0) := by
    have h2 := (ENNReal.tendsto_toReal (by simp)).comp key
    exact h2
  exact step1.congr fun a => (hnorm _).symm

/-!
## Step (ii): a concrete `ℕ`-indexed Hilbert basis of the shell space

Route: the graph parametrization `shellParam : ℝ³ → Hₘ⁺` is a measurable
equivalence between `ℝ³` (with the density-weighted Lebesgue measure)
and the mass shell (with `massShellMeasure`). Pullback along it is a
linear isometry equivalence of the two `L²` spaces; separability is
free on the `ℝ³` side (Mathlib instances: a countably generated space
with an s-finite measure is a separable measure, and `Lp` over a
separable measure has second-countable, hence separable, topology) and
transports along the equivalence. Infinite-dimensionality is proved
from an explicit orthonormal family of indicator functions of disjoint
spatial balls. A maximal orthonormal set is then countable (disjoint
`√2`-balls argument against a countable dense set) and infinite, hence
in bijection with `ℕ` by cardinality, and the maximal-set Hilbert
basis transports along that bijection.
-/

section ONB

/-- The density-weighted Lebesgue measure on `ℝ³`: the measure whose
pushforward along `shellParam` is `massShellMeasure` (by definition). -/
noncomputable abbrev spatialMeasure (m : ℝ) : Measure (EuclideanSpace ℝ (Fin 3)) :=
  Measure.withDensity volume (fun u => (ENNReal.ofReal (2 * shellEnergy m u))⁻¹)

/-- The one-particle space over the spatial parametrization. -/
abbrev spatialLp (m : ℝ) : Type := Lp ℂ 2 (spatialMeasure m)

/-- The spatial part of a Minkowski vector, as a point of `ℝ³`. -/
def spatialOf (p : Minkowski) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i => p (Fin.succ i))

theorem spatialOf_apply (p : Minkowski) (i : Fin 3) :
    spatialOf p i = p (Fin.succ i) :=
  rfl

/-- **T1:** the spatial part of the graph parametrization is the
original spatial momentum. -/
theorem spatialOf_shellParam (m : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    spatialOf (shellParam m u) = u := by
  apply PiLp.ext
  intro i
  fin_cases i
  · show (shellParam m u) (Fin.succ 0) = u 0
    rw [show Fin.succ (0 : Fin 3) = (1 : Fin 4) from rfl, shellParam_comp1]
  · show (shellParam m u) (Fin.succ 1) = u 1
    rw [show Fin.succ (1 : Fin 3) = (2 : Fin 4) from rfl, shellParam_comp2]
  · show (shellParam m u) (Fin.succ 2) = u 2
    rw [show Fin.succ (2 : Fin 3) = (3 : Fin 4) from rfl, shellParam_comp3]

/-- **T1:** on the mass shell, the energy is the shell energy of the
spatial part (the shell equation, solved for `p 0` using `0 < p 0`). -/
theorem shellEnergy_spatialOf (m : ℝ) {p : Minkowski} (hp : p ∈ massShell m) :
    shellEnergy m (spatialOf p) = p 0 := by
  obtain ⟨h1, h2⟩ := hp
  have hnorm : ‖spatialOf p‖ ^ 2 = (p 1) ^ 2 + (p 2) ^ 2 + (p 3) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    have e0 : spatialOf p 0 = p 1 := rfl
    have e1 : spatialOf p 1 = p 2 := rfl
    have e2 : spatialOf p 2 = p 3 := rfl
    rw [e0, e1, e2]
    simp only [Real.norm_eq_abs, sq_abs]
  have hsq : (p 0) ^ 2 = m ^ 2 + ‖spatialOf p‖ ^ 2 := by
    have h1' : p 0 * p 0 - p 1 * p 1 - p 2 * p 2 - p 3 * p 3 = m ^ 2 := h1
    have e : ∀ x : ℝ, x ^ 2 = x * x := fun x => by ring
    rw [e (p 0), hnorm, e (p 1), e (p 2), e (p 3)]
    linarith
  unfold shellEnergy
  rw [← hsq, Real.sqrt_sq (le_of_lt h2)]

/-- **T1:** the graph parametrization of the spatial part of a shell
point is the point itself. -/
theorem shellParam_spatialOf (m : ℝ) (hm : 0 < m) {p : Minkowski}
    (hp : p ∈ massShell m) :
    shellParam m (spatialOf p) = p := by
  funext i
  fin_cases i
  · show (shellParam m (spatialOf p)) 0 = p 0
    rw [shellParam_comp0, shellEnergy_spatialOf m hp]
  · show (shellParam m (spatialOf p)) 1 = p 1
    rw [shellParam_comp1]
    exact spatialOf_apply p 0
  · show (shellParam m (spatialOf p)) 2 = p 2
    rw [shellParam_comp2]
    exact spatialOf_apply p 1
  · show (shellParam m (spatialOf p)) 3 = p 3
    rw [shellParam_comp3]
    exact spatialOf_apply p 2

/-- **T1:** the graph parametrization is a measurable equivalence
`ℝ³ ≃ᵐ Hₘ⁺` (inverse: the spatial part). -/
noncomputable def shellParamEquiv (m : ℝ) (hm : 0 < m) :
    EuclideanSpace ℝ (Fin 3) ≃ᵐ massShell m where
  toFun := fun u => ⟨shellParam m u, shellParam_mem m hm u⟩
  invFun := fun p => spatialOf p.1
  left_inv := fun u => spatialOf_shellParam m u
  right_inv := fun p => Subtype.ext (shellParam_spatialOf m hm p.2)
  measurable_toFun := measurable_shellParam_subtype m hm
  measurable_invFun := by
    show Measurable (fun p : massShell m => spatialOf p.1)
    have hcomp : (fun p : massShell m => spatialOf p.1)
        = WithLp.toLp 2 ∘ (fun p : massShell m => fun i => p.1 (Fin.succ i)) := rfl
    rw [hcomp]
    apply Measurable.comp (WithLp.measurable_toLp 2 (Fin 3 → ℝ))
    apply Measurable.of_eval
    intro i
    exact ((continuous_apply (Fin.succ i)).comp continuous_subtype_val).measurable

/-- **T1:** the graph parametrization is measure-preserving (its
pushforward of the density-weighted Lebesgue measure is the definition
of `massShellMeasure`). -/
theorem measurePreserving_shellParamEquiv (m : ℝ) (hm : 0 < m) :
    MeasurePreserving (shellParamEquiv m hm) (spatialMeasure m)
      (massShellMeasure m hm) := by
  refine ⟨measurable_shellParam_subtype m hm, ?_⟩
  rfl

/-- **T1:** the inverse parametrization is measure-preserving. -/
theorem measurePreserving_shellParamEquiv_symm (m : ℝ) (hm : 0 < m) :
    MeasurePreserving (shellParamEquiv m hm).symm (massShellMeasure m hm)
      (spatialMeasure m) := by
  refine ⟨(shellParamEquiv m hm).symm.measurable_toFun, ?_⟩
  apply Measure.ext
  intro s hs
  have hf1 : Measurable (shellParamEquiv m hm).symm :=
    (shellParamEquiv m hm).measurable_invFun
  have hf2 : Measurable (shellParamEquiv m hm) :=
    (shellParamEquiv m hm).measurable_toFun
  rw [Measure.map_apply hf1 hs, ← (measurePreserving_shellParamEquiv m hm).map_eq,
    Measure.map_apply hf2 (hf1 hs)]
  congr 1
  ext u
  simp only [Set.mem_preimage, (shellParamEquiv m hm).symm_apply_apply]

/-- **T1 (scalar linearity of the Lp pullback):** Mathlib's
`Lp.compMeasurePreserving` is packaged as an additive isometry; it is
also homogeneous, by the representative computation. -/
theorem compMeasurePreserving_smul {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {μb : Measure β} {f : α → β}
    (hf : MeasurePreserving f μ μb) (c : ℂ) (X : Lp ℂ 2 μb) :
    Lp.compMeasurePreserving f hf (c • X) =
      c • Lp.compMeasurePreserving f hf X := by
  conv_lhs => rw [← Lp.toLp_coeFn (Lp.compMeasurePreserving f hf (c • X)) (Lp.memLp _)]
  conv_rhs => rw [← Lp.toLp_coeFn (c • Lp.compMeasurePreserving f hf X) (Lp.memLp _)]
  apply MemLp.toLp_congr
  have h3 := hf.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_smul c X)
  filter_upwards [Lp.coeFn_compMeasurePreserving (c • X) hf,
    Lp.coeFn_compMeasurePreserving X hf, h3,
    Lp.coeFn_smul c (Lp.compMeasurePreserving f hf X)] with u h1 h2 h3' h4
  rw [h1, h4]
  simp only [Pi.smul_apply, Function.comp_apply] at h3' ⊢
  rw [h3', h2]
  simp only [Function.comp_apply]

/-- **T1:** pullback along the graph parametrization, as a linear
isometry `L²(Hₘ⁺) →ₗᵢ L²(ℝ³)`. -/
noncomputable def shellPullback (m : ℝ) (hm : 0 < m) :
    shellLp m hm →ₗᵢ[ℂ] spatialLp m where
  toFun := Lp.compMeasurePreserving (shellParamEquiv m hm)
    (measurePreserving_shellParamEquiv m hm)
  map_add' := fun X Y => map_add _ X Y
  map_smul' := fun c X => compMeasurePreserving_smul _ c X
  norm_map' := fun X => Lp.norm_compMeasurePreserving X _

/-- **T1:** pullback along the inverse parametrization, as a linear
isometry `L²(ℝ³) →ₗᵢ L²(Hₘ⁺)`. -/
noncomputable def spatialPullback (m : ℝ) (hm : 0 < m) :
    spatialLp m →ₗᵢ[ℂ] shellLp m hm where
  toFun := Lp.compMeasurePreserving (shellParamEquiv m hm).symm
    (measurePreserving_shellParamEquiv_symm m hm)
  map_add' := fun X Y => map_add _ X Y
  map_smul' := fun c X => compMeasurePreserving_smul _ c X
  norm_map' := fun X => Lp.norm_compMeasurePreserving X _

/-- **T1:** the two pullbacks are mutually inverse (both composites are
the identity, by the `Lp.compMeasurePreserving` composition law and the
bijection identities). -/
theorem shellPullback_spatialPullback (m : ℝ) (hm : 0 < m) (Y : spatialLp m) :
    shellPullback m hm (spatialPullback m hm Y) = Y := by
  have hfun : (shellParamEquiv m hm).symm ∘ (shellParamEquiv m hm) = id :=
    funext fun u => (shellParamEquiv m hm).symm_apply_apply u
  calc shellPullback m hm (spatialPullback m hm Y)
      = Lp.compMeasurePreserving
          ((shellParamEquiv m hm).symm ∘ (shellParamEquiv m hm))
          ((measurePreserving_shellParamEquiv_symm m hm).comp
            (measurePreserving_shellParamEquiv m hm)) Y :=
        (Lp.compMeasurePreserving_comp_apply Y _ _).symm
    _ = Y := by
        apply Subtype.ext
        apply AEEqFun.ext
        calc (Lp.compMeasurePreserving
              ((shellParamEquiv m hm).symm ∘ (shellParamEquiv m hm)) _ Y :
              EuclideanSpace ℝ (Fin 3) → ℂ)
            =ᵐ[spatialMeasure m] Y ∘ ((shellParamEquiv m hm).symm
                ∘ (shellParamEquiv m hm)) :=
              Lp.coeFn_compMeasurePreserving Y _
          _ = Y := by rw [hfun, Function.comp_id]

/-- **T1:** the other composite is the identity. -/
theorem spatialPullback_shellPullback (m : ℝ) (hm : 0 < m) (X : shellLp m hm) :
    spatialPullback m hm (shellPullback m hm X) = X := by
  have hfun : (shellParamEquiv m hm) ∘ (shellParamEquiv m hm).symm = id :=
    funext fun p => (shellParamEquiv m hm).apply_symm_apply p
  calc spatialPullback m hm (shellPullback m hm X)
      = Lp.compMeasurePreserving
          ((shellParamEquiv m hm) ∘ (shellParamEquiv m hm).symm)
          ((measurePreserving_shellParamEquiv m hm).comp
            (measurePreserving_shellParamEquiv_symm m hm)) X :=
        (Lp.compMeasurePreserving_comp_apply X _ _).symm
    _ = X := by
        apply Subtype.ext
        apply AEEqFun.ext
        calc (Lp.compMeasurePreserving
              ((shellParamEquiv m hm) ∘ (shellParamEquiv m hm).symm) _ X :
              massShell m → ℂ)
            =ᵐ[massShellMeasure m hm] X ∘ ((shellParamEquiv m hm)
                ∘ (shellParamEquiv m hm).symm) :=
              Lp.coeFn_compMeasurePreserving X _
          _ = X := by rw [hfun, Function.comp_id]

/-- **T1:** the shell `L²` space and the spatial `L²` space are
linearly isometric. -/
noncomputable def shellLpEquiv (m : ℝ) (hm : 0 < m) :
    shellLp m hm ≃ₗᵢ[ℂ] spatialLp m :=
  LinearIsometryEquiv.ofLinearIsometry (shellPullback m hm)
    (spatialPullback m hm).toLinearMap
    (by
      apply LinearMap.ext
      intro Y
      exact shellPullback_spatialPullback m hm Y)
    (by
      apply LinearMap.ext
      intro X
      exact spatialPullback_shellPullback m hm X)

/-- **T1:** the mass-shell one-particle space is separable. Transported
along `shellLpEquiv` from the spatial side, where separability is a
Mathlib instance (separable measure ⇒ second-countable `Lp` topology ⇒
separable). -/
instance separableSpace_shellLp (m : ℝ) (hm : 0 < m) :
    TopologicalSpace.SeparableSpace (shellLp m hm) := by
  haveI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  obtain ⟨s, hs_count, hs_dense⟩ :=
    TopologicalSpace.SeparableSpace.exists_countable_dense (α := spatialLp m)
  refine ⟨⟨(spatialPullback m hm) '' s, hs_count.image _, ?_⟩⟩
  -- the image of a dense set under a continuous surjection with a
  -- continuous inverse is dense: `x = T (T⁻¹ x)`, `T⁻¹ x ∈ closure s`,
  -- and continuity gives `T '' closure s ⊆ closure (T '' s)`
  intro x
  have hx : x = spatialPullback m hm (shellPullback m hm x) :=
    (spatialPullback_shellPullback m hm x).symm
  have hmem : shellPullback m hm x ∈ closure s := hs_dense _
  rw [hx]
  exact image_closure_subset_closure_image (spatialPullback m hm).continuous
    ⟨shellPullback m hm x, hmem, rfl⟩

end ONB


/-! ============================================================
    §B1. Patches on the spatial side: disjoint unit balls about
    the points `3k` of the first axis, with two-sided bounds on
    the shell measure of each patch.
    ============================================================ -/

/-- The patch centres: the point `3k` on the first spatial axis. -/
def patchCenter (k : ℕ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i => if i = 0 then 3 * (k : ℝ) else 0)

theorem patchCenter_apply (k : ℕ) (i : Fin 3) :
    patchCenter k i = if i = 0 then 3 * (k : ℝ) else 0 := rfl

/-- The `k`-th patch: the open unit ball about `patchCenter k`. -/
def patch (k : ℕ) : Set (EuclideanSpace ℝ (Fin 3)) := Metric.ball (patchCenter k) 1

/-- **T1:** distinct patches are disjoint (centres are `≥ 3` apart,
radii are `1`). -/
theorem patch_disjoint (j k : ℕ) (hjk : j ≠ k) : Disjoint (patch j) (patch k) := by
  have hdist : dist (patchCenter j) (patchCenter k) = 3 * |(j : ℝ) - (k : ℝ)| := by
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_three]
    have h1 : ∀ i : Fin 3, i ≠ 0 →
        dist (patchCenter j i) (patchCenter k i) = 0 := by
      intro i hi
      rw [patchCenter_apply, patchCenter_apply, if_neg hi, if_neg hi, dist_self]
    rw [h1 1 (by decide), h1 2 (by decide), patchCenter_apply, patchCenter_apply,
      if_pos rfl, if_pos rfl, Real.dist_eq, ← mul_sub, abs_mul]
    simp [Real.sqrt_sq (show (0:ℝ) ≤ 3 * |(j:ℝ) - (k:ℝ)| by positivity)]
  have hge : (1:ℝ) ≤ |(j:ℝ) - (k:ℝ)| := by
    rcases Nat.lt_or_gt_of_ne hjk with h | h
    · have h1 : (j:ℝ) + 1 ≤ (k:ℝ) := by
        have h2 : j + 1 ≤ k := Nat.succ_le_of_lt h
        have h3 : ((j + 1 : ℕ) : ℝ) ≤ (k:ℝ) := by exact_mod_cast h2
        simpa using h3
      rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ (k:ℝ) - (j:ℝ))]
      linarith
    · have h1 : (k:ℝ) + 1 ≤ (j:ℝ) := by
        have h2 : k + 1 ≤ j := Nat.succ_le_of_lt h
        have h3 : ((k + 1 : ℕ) : ℝ) ≤ (j:ℝ) := by exact_mod_cast h2
        simpa using h3
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (j:ℝ) - (k:ℝ))]
      linarith
  rw [Set.disjoint_left]
  rintro a ha hb
  have h1 : dist a (patchCenter j) < 1 := ha
  have h2 : dist a (patchCenter k) < 1 := hb
  have htri : dist (patchCenter j) (patchCenter k)
      ≤ dist (patchCenter j) a + dist a (patchCenter k) := dist_triangle _ _ _
  rw [dist_comm (patchCenter j) a] at htri
  linarith

/-- **T1:** the square of the shell energy on the spatial side. -/
theorem shellEnergy_sq_spatial (m : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    (shellEnergy m u) ^ 2 = m ^ 2 + ‖u‖ ^ 2 :=
  Real.sq_sqrt (by positivity : (0:ℝ) ≤ m ^ 2 + ‖u‖ ^ 2)

/-- **T1:** the spatial norm is bounded by the shell energy. -/
theorem norm_le_shellEnergy (m : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    ‖u‖ ≤ shellEnergy m u := by
  show ‖u‖ ≤ Real.sqrt (m ^ 2 + ‖u‖ ^ 2)
  conv_lhs => rw [← Real.sqrt_sq (norm_nonneg u)]
  exact Real.sqrt_le_sqrt (by linarith [sq_nonneg m])

/-- **T1:** the mass is bounded by the shell energy. -/
theorem mass_le_shellEnergy (m : ℝ) (hm : 0 < m) (u : EuclideanSpace ℝ (Fin 3)) :
    m ≤ shellEnergy m u := by
  show m ≤ Real.sqrt (m ^ 2 + ‖u‖ ^ 2)
  conv_lhs => rw [← Real.sqrt_sq hm.le]
  exact Real.sqrt_le_sqrt (by linarith [sq_nonneg ‖u‖])

/-- **T1:** the shell energy is `1`-Lipschitz in the spatial variable:
the energy of `(m, u)` is the Euclidean norm of a point at distance
`‖u - v‖` from that of `(m, v)`, proved here from
`(E u - E v)(E u + E v) = ‖u‖² - ‖v‖²`. -/
theorem shellEnergy_sub_le (m : ℝ) (u v : EuclideanSpace ℝ (Fin 3)) :
    shellEnergy m u - shellEnergy m v ≤ ‖u - v‖ := by
  by_cases hS : shellEnergy m u + shellEnergy m v = 0
  · have hu : shellEnergy m u = 0 :=
      (add_eq_zero_iff_of_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp hS |>.1
    have hv : shellEnergy m v = 0 :=
      (add_eq_zero_iff_of_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp hS |>.2
    rw [hu, hv, sub_zero]
    exact norm_nonneg _
  · have hpos : 0 < shellEnergy m u + shellEnergy m v :=
      lt_of_le_of_ne (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Ne.symm hS)
    have hkey : (shellEnergy m u + shellEnergy m v) * (shellEnergy m u - shellEnergy m v)
        = ‖u‖ ^ 2 - ‖v‖ ^ 2 := by
      have h1 : (shellEnergy m u + shellEnergy m v) * (shellEnergy m u - shellEnergy m v)
          = (shellEnergy m u) ^ 2 - (shellEnergy m v) ^ 2 := by ring
      rw [h1, shellEnergy_sq_spatial, shellEnergy_sq_spatial]
      ring
    have hbound : ‖u‖ ^ 2 - ‖v‖ ^ 2
        ≤ (shellEnergy m u + shellEnergy m v) * ‖u - v‖ := by
      have h1 : ‖u‖ ^ 2 - ‖v‖ ^ 2 ≤ |‖u‖ ^ 2 - ‖v‖ ^ 2| := le_abs_self _
      have h2 : |‖u‖ ^ 2 - ‖v‖ ^ 2| = (‖u‖ + ‖v‖) * |‖u‖ - ‖v‖| := by
        rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      have h3 : (‖u‖ + ‖v‖) * |‖u‖ - ‖v‖|
          ≤ (shellEnergy m u + shellEnergy m v) * ‖u - v‖ :=
        mul_le_mul (add_le_add (norm_le_shellEnergy m u) (norm_le_shellEnergy m v))
          (abs_norm_sub_norm_le u v) (abs_nonneg _)
          (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      exact h1.trans (h2 ▸ h3)
    rw [← hkey] at hbound
    exact le_of_mul_le_mul_left hbound hpos

/-- **T1:** the density defining the spatial measure is measurable. -/
theorem measurable_spatialDensity (m : ℝ) :
    Measurable (fun u => (ENNReal.ofReal (2 * shellEnergy m u))⁻¹) := by
  have hcont : Continuous (shellEnergy m) :=
    Real.continuous_sqrt.comp (continuous_const.add (continuous_norm.pow 2))
  exact measurable_inv.comp (ENNReal.measurable_ofReal.comp
    (measurable_const.mul hcont.measurable))

/-- The volume of a patch, in closed form. -/
theorem volume_patch (k : ℕ) :
    volume (patch k)
      = ENNReal.ofReal (√(Real.pi) ^ 3 / Real.Gamma (3 / 2 + 1)) := by
  rw [patch, EuclideanSpace.volume_ball]
  simp [Fintype.card_fin]

theorem volume_patch_pos (k : ℕ) : 0 < volume (patch k) := by
  rw [volume_patch]
  rw [ENNReal.ofReal_pos]
  exact div_pos (pow_pos (Real.sqrt_pos_of_pos Real.pi_pos) 3)
    (Real.Gamma_pos_of_pos (by norm_num))

theorem volume_patch_ne_top (k : ℕ) : volume (patch k) ≠ ⊤ := by
  rw [volume_patch]
  exact ENNReal.ofReal_ne_top

/-- **T1:** every patch has positive spatial measure: on the patch the
density is bounded below by its value at energy `E(centre) + 1`. -/
theorem spatialMeasure_patch_pos (m : ℝ) (hm : 0 < m) (k : ℕ) :
    0 < spatialMeasure m (patch k) := by
  have hC : (0:ℝ) < (2 * (shellEnergy m (patchCenter k) + 1))⁻¹ := by
    apply inv_pos_of_pos
    have h0 : (0:ℝ) ≤ shellEnergy m (patchCenter k) := Real.sqrt_nonneg _
    linarith
  have hbound : ∀ u ∈ patch k,
      ENNReal.ofReal ((2 * (shellEnergy m (patchCenter k) + 1))⁻¹)
        ≤ (ENNReal.ofReal (2 * shellEnergy m u))⁻¹ := by
    intro u hu
    have hu1 : dist u (patchCenter k) < 1 := hu
    rw [dist_eq_norm] at hu1
    have hEu : shellEnergy m u ≤ shellEnergy m (patchCenter k) + 1 := by
      have h := shellEnergy_sub_le m u (patchCenter k)
      linarith
    have hE0 : (0:ℝ) ≤ shellEnergy m (patchCenter k) := Real.sqrt_nonneg _
    rw [ENNReal.ofReal_inv_of_pos
      (show (0:ℝ) < 2 * (shellEnergy m (patchCenter k) + 1) by linarith)]
    exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal (by linarith))
  have hstep : ENNReal.ofReal ((2 * (shellEnergy m (patchCenter k) + 1))⁻¹)
        * volume (patch k) ≤ spatialMeasure m (patch k) := by
    calc ENNReal.ofReal ((2 * (shellEnergy m (patchCenter k) + 1))⁻¹)
          * volume (patch k)
        = ∫⁻ _ in patch k, ENNReal.ofReal ((2 * (shellEnergy m (patchCenter k) + 1))⁻¹)
            ∂volume := by
          rw [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ]
      _ ≤ ∫⁻ u in patch k, (ENNReal.ofReal (2 * shellEnergy m u))⁻¹ ∂volume :=
          MeasureTheory.lintegral_mono_ae (by
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with u hu
            exact hbound u hu)
      _ = spatialMeasure m (patch k) :=
          (MeasureTheory.withDensity_apply _ measurableSet_ball).symm
  by_contra hcon
  push_neg at hcon
  have h0 : spatialMeasure m (patch k) = 0 := le_antisymm hcon zero_le
  rw [h0] at hstep
  exact mul_ne_zero (ENNReal.ofReal_pos.mpr hC).ne' (volume_patch_pos k).ne'
    (le_antisymm hstep zero_le)

/-- **T1:** every patch has finite spatial measure: on the patch the
density is bounded above by its value at energy `m`. -/
theorem spatialMeasure_patch_ne_top (m : ℝ) (hm : 0 < m) (k : ℕ) :
    spatialMeasure m (patch k) ≠ ⊤ := by
  have hbound : ∀ u ∈ patch k,
      (ENNReal.ofReal (2 * shellEnergy m u))⁻¹
        ≤ ENNReal.ofReal ((2 * m)⁻¹) := by
    intro u _
    have hpos1 : (0:ℝ) < 2 * m := mul_pos (by norm_num) hm
    rw [ENNReal.ofReal_inv_of_pos hpos1]
    exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal
      (by linarith [mass_le_shellEnergy m hm u]))
  have hstep : spatialMeasure m (patch k)
      ≤ ENNReal.ofReal ((2 * m)⁻¹) * volume (patch k) := by
    calc spatialMeasure m (patch k)
        = ∫⁻ u in patch k, (ENNReal.ofReal (2 * shellEnergy m u))⁻¹ ∂volume :=
          MeasureTheory.withDensity_apply _ measurableSet_ball
      _ ≤ ∫⁻ _ in patch k, ENNReal.ofReal ((2 * m)⁻¹) ∂volume :=
          MeasureTheory.lintegral_mono_ae (by
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with u hu
            exact hbound u hu)
      _ = ENNReal.ofReal ((2 * m)⁻¹) * volume (patch k) := by
          rw [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ]
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (volume_patch_ne_top k)) hstep
/-! ============================================================
    §B2. The patch orthonormal family and infinite dimensionality
    of the one-particle space.
    ============================================================ -/

/-- The (unnormalised) patch vector: the constant function `1` on
the `k`-th patch, as an element of the spatial `L²` space. -/
noncomputable def patchVec (m : ℝ) (hm : 0 < m) (k : ℕ) : spatialLp m :=
  MeasureTheory.indicatorConstLp 2 measurableSet_ball
    (spatialMeasure_patch_ne_top m hm k) 1

/-- **T1:** the inner product of two patch vectors is the spatial
measure of the intersection of the patches. -/
theorem inner_patchVec (m : ℝ) (hm : 0 < m) (j k : ℕ) :
    ⟪patchVec m hm j, patchVec m hm k⟫_ℂ
      = ((spatialMeasure m (patch j ∩ patch k)).toReal : ℂ) := by
  rw [MeasureTheory.L2.inner_def]
  have hj : ⇑(patchVec m hm j)
      =ᵐ[spatialMeasure m] (patch j).indicator (fun _ => (1 : ℂ)) :=
    MeasureTheory.indicatorConstLp_coeFn
  have hk : ⇑(patchVec m hm k)
      =ᵐ[spatialMeasure m] (patch k).indicator (fun _ => (1 : ℂ)) :=
    MeasureTheory.indicatorConstLp_coeFn
  have hcongr : (fun u => ⟪patchVec m hm j u, patchVec m hm k u⟫_ℂ)
      =ᵐ[spatialMeasure m] (patch j ∩ patch k).indicator (fun _ => (1 : ℂ)) := by
    filter_upwards [hj, hk] with u hu1 hu2
    rw [hu1, hu2]
    by_cases hju : u ∈ patch j <;> by_cases hku : u ∈ patch k <;>
      simp [Set.indicator_apply, hju, hku, Set.mem_inter_iff, RCLike.inner_apply]
  rw [MeasureTheory.integral_congr_ae hcongr, MeasureTheory.integral_indicator_const,
    Complex.real_smul, mul_one]
  · rfl
  · exact MeasurableSet.inter measurableSet_ball measurableSet_ball

/-- The normalised patch vector: the `k`-th member of the explicit
orthonormal family. -/
noncomputable def patchBasis (m : ℝ) (hm : 0 < m) (k : ℕ) : spatialLp m :=
  (((Real.sqrt (spatialMeasure m (patch k)).toReal)⁻¹ : ℝ) : ℂ) • patchVec m hm k

/-- **T1:** the patch vectors form an orthonormal family in the
spatial `L²` space. -/
theorem orthonormal_patchBasis (m : ℝ) (hm : 0 < m) :
    Orthonormal ℂ (patchBasis m hm) := by
  rw [orthonormal_iff_ite]
  intro j k
  have hμk : 0 < (spatialMeasure m (patch k)).toReal :=
    ENNReal.toReal_pos (spatialMeasure_patch_pos m hm k).ne'
      (spatialMeasure_patch_ne_top m hm k)
  unfold patchBasis
  rw [inner_smul_left, inner_smul_right, inner_patchVec]
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl, Set.inter_self]
    have hc : (starRingEnd ℂ) (((Real.sqrt (spatialMeasure m (patch j)).toReal)⁻¹ : ℝ) : ℂ)
        = (((Real.sqrt (spatialMeasure m (patch j)).toReal)⁻¹ : ℝ) : ℂ) := by simp
    rw [hc]
    have key : (Real.sqrt (spatialMeasure m (patch j)).toReal)⁻¹
        * ((Real.sqrt (spatialMeasure m (patch j)).toReal)⁻¹
          * (spatialMeasure m (patch j)).toReal) = 1 := by
      rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt ENNReal.toReal_nonneg,
        inv_mul_cancel₀ (ne_of_gt hμk)]
    calc ((((Real.sqrt (spatialMeasure m (patch j)).toReal)⁻¹ : ℝ) : ℂ))
          * (((((Real.sqrt (spatialMeasure m (patch j)).toReal)⁻¹ : ℝ) : ℂ))
            * (((spatialMeasure m (patch j)).toReal : ℝ) : ℂ))
        = (((Real.sqrt (spatialMeasure m (patch j)).toReal)⁻¹
            * ((Real.sqrt (spatialMeasure m (patch j)).toReal)⁻¹
              * (spatialMeasure m (patch j)).toReal) : ℝ) : ℂ) := by push_cast; ring
      _ = 1 := by rw [key]; exact Complex.ofReal_one
  · rw [if_neg hjk]
    have hdisj : patch j ∩ patch k = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp (patch_disjoint j k hjk)
    rw [hdisj]
    simp

/-- **T1:** the spatial `L²` space is infinite-dimensional: it
carries an orthonormal family indexed by `ℕ`. -/
theorem not_finiteDimensional_spatialLp (m : ℝ) (hm : 0 < m) :
    ¬ FiniteDimensional ℂ (spatialLp m) := by
  intro hFD
  haveI : FiniteDimensional ℂ (spatialLp m) := hFD
  have hli : LinearIndependent ℂ
      (fun i : Fin (Module.finrank ℂ (spatialLp m) + 1) =>
        patchBasis m hm (i : ℕ)) :=
    (orthonormal_patchBasis m hm).linearIndependent.comp _ Fin.val_injective
  have hle := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at hle
  omega

/-- **T1:** the mass-shell one-particle space is
infinite-dimensional. -/
theorem not_finiteDimensional_shellLp (m : ℝ) (hm : 0 < m) :
    ¬ FiniteDimensional ℂ (shellLp m hm) := by
  intro hFD
  haveI : Module.Finite ℂ (shellLp m hm) := hFD
  exact not_finiteDimensional_spatialLp m hm
    (Module.Finite.equiv (shellLpEquiv m hm).toLinearEquiv)


/-! ============================================================
    §B3. The concrete Hilbert basis of the one-particle space:
    a maximal orthonormal set is countable (separability) and
    infinite (infinite dimensionality), hence reindexes to `ℕ`.
    ============================================================ -/

/-- **T1:** the index set of any Hilbert basis of the shell space
is countable: distinct basis vectors are `√2` apart, so choosing a
point of the fixed countable dense set within `1/2` of each is
injective. -/
theorem countable_hilbertBasis_index {w : Set (shellLp m hm)}
    (b : HilbertBasis w ℂ (shellLp m hm)) (hb : ⇑b = ((↑) : w → shellLp m hm)) :
    Countable w := by
  obtain ⟨s, hs_count, hs_dense⟩ :=
    TopologicalSpace.SeparableSpace.exists_countable_dense (α := shellLp m hm)
  haveI : Countable s := hs_count
  have hex : ∀ x : w, ∃ y : s, dist (x : shellLp m hm) (y : shellLp m hm) < 1 / 2 := by
    intro x
    obtain ⟨y, hy_mem, hy_dist⟩ :=
      hs_dense.exists_dist_lt (x : shellLp m hm) (by norm_num : (0:ℝ) < 1 / 2)
    exact ⟨⟨y, hy_mem⟩, hy_dist⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hinner : ⟪(x : shellLp m hm), (y : shellLp m hm)⟫_ℂ = 0 := by
      have h := b.orthonormal.2 hne
      rw [hb] at h
      exact h
    have hnormx : ‖(x : shellLp m hm)‖ = 1 := by
      have h := b.orthonormal.1 x
      rw [hb] at h
      exact h
    have hnormy : ‖(y : shellLp m hm)‖ = 1 := by
      have h := b.orthonormal.1 y
      rw [hb] at h
      exact h
    have hsq : ‖(x : shellLp m hm) - (y : shellLp m hm)‖ ^ 2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℂ), hinner, hnormx, hnormy]
      norm_num
    have hdist : dist (x : shellLp m hm) (y : shellLp m hm) = Real.sqrt 2 := by
      rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _), hsq]
    have htri : dist (x : shellLp m hm) (y : shellLp m hm)
        ≤ dist (x : shellLp m hm) (f x : shellLp m hm)
          + dist (f y : shellLp m hm) (y : shellLp m hm) := by
      calc dist (x : shellLp m hm) (y : shellLp m hm)
          ≤ dist (x : shellLp m hm) (f x : shellLp m hm)
            + dist (f x : shellLp m hm) (y : shellLp m hm) := dist_triangle _ _ _
        _ = dist (x : shellLp m hm) (f x : shellLp m hm)
            + dist (f y : shellLp m hm) (y : shellLp m hm) := by
            rw [congrArg Subtype.val hxy]
    have hsqrt : (1:ℝ) < Real.sqrt 2 := by
      rw [Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 1)]
      norm_num
    have h1 : dist (x : shellLp m hm) (y : shellLp m hm) < 1 := by
      refine lt_of_le_of_lt htri ?_
      rw [dist_comm (f y : shellLp m hm) (y : shellLp m hm)]
      have hfx := hf x
      have hfy := hf y
      linarith
    rw [hdist] at h1
    linarith
  exact Function.Injective.countable hinj

/-- **T1:** the index set of any Hilbert basis of the shell space
is infinite: a finite one would span a closed dense subspace,
making the shell space finite-dimensional. -/
theorem infinite_hilbertBasis_index {w : Set (shellLp m hm)}
    (b : HilbertBasis w ℂ (shellLp m hm)) (hb : ⇑b = ((↑) : w → shellLp m hm)) :
    Infinite w := by
  by_contra hfin
  haveI : Finite w := Finite.of_not_infinite hfin
  have hdense : (Submodule.span ℂ (Set.range ((↑) : w → shellLp m hm))).topologicalClosure
      = ⊤ := by
    have h := b.dense_span
    rw [hb] at h
    exact h
  haveI : FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range ((↑) : w → shellLp m hm))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hclosed : IsClosed ((Submodule.span ℂ (Set.range ((↑) : w → shellLp m hm))
      : Submodule ℂ (shellLp m hm)) : Set (shellLp m hm)) :=
    Submodule.closed_of_finiteDimensional _
  have htop : Submodule.span ℂ (Set.range ((↑) : w → shellLp m hm)) = ⊤ := by
    have h1 : closure ((Submodule.span ℂ (Set.range ((↑) : w → shellLp m hm))
        : Submodule ℂ (shellLp m hm)) : Set (shellLp m hm)) = Set.univ := by
      rw [← Submodule.topologicalClosure_coe, hdense]
      rfl
    have h2 : ((Submodule.span ℂ (Set.range ((↑) : w → shellLp m hm))
        : Submodule ℂ (shellLp m hm)) : Set (shellLp m hm)) = Set.univ := by
      rw [← hclosed.closure_eq]
      exact h1
    refine le_antisymm le_top (fun x _ => ?_)
    show x ∈ ((Submodule.span ℂ (Set.range ((↑) : w → shellLp m hm))
      : Submodule ℂ (shellLp m hm)) : Set (shellLp m hm))
    rw [h2]
    exact Set.mem_univ x
  have hfin2 : Module.Finite ℂ (shellLp m hm) := by
    classical
    haveI : Fintype w := Fintype.ofFinite _
    apply Module.Finite.of_fg_top
    refine ⟨Finset.univ.image ((↑) : w → shellLp m hm), ?_⟩
    have hcoe : ((Finset.univ.image ((↑) : w → shellLp m hm) : Finset (shellLp m hm))
        : Set (shellLp m hm)) = Set.range ((↑) : w → shellLp m hm) := by simp
    rw [hcoe]
    exact htop
  exact not_finiteDimensional_shellLp m hm hfin2

/-- **T1 (the concrete ONB port):** the mass-shell one-particle
space has a Hilbert basis indexed by `ℕ`. -/
noncomputable def shellONB (m : ℝ) (hm : 0 < m) : HilbertBasis ℕ ℂ (shellLp m hm) :=
  let ex := exists_hilbertBasis ℂ (shellLp m hm)
  let w := Classical.choose ex
  let b := Classical.choose (Classical.choose_spec ex)
  let hb := Classical.choose_spec (Classical.choose_spec ex)
  let e : w ≃ ℕ := Classical.choice (by
    haveI : Countable w := countable_hilbertBasis_index b hb
    haveI : Infinite w := infinite_hilbertBasis_index b hb
    rw [← Cardinal.eq, Cardinal.mk_eq_aleph0, Cardinal.mk_eq_aleph0])
  HilbertBasis.mk (b.orthonormal.comp e.symm e.symm.injective) (by
    rw [Function.Surjective.range_comp e.symm.surjective]
    exact le_of_eq b.dense_span.symm)


end ThetLogos
