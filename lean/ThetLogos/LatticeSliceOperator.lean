/-
# S2-4 half (b) — THE OPERATOR BRICK: completion, form closure, and
# the named stop at the unbounded operator

Brick S2-4(b), priced L, under the Stage 2 charter
(`whitepaper/stage2-reconstruction-scoping-2026-10-24.md`) and the
exact residue of the S2-4 form dossier
(`whitepaper/stage2-s24-hamiltonian-form-2026-10-24.md`) and the
S2-5 weld dossier (`whitepaper/stage2-s25-weld-partial-2026-10-24.md`):

(i) the completed Hilbert space of the S2-2 engine's pre-Hilbert
`Π₁`-quotient, with `T̂` extended by continuity as a self-adjoint
contraction, vacuum preserved;
(ii) the Hamiltonian form of S2-4(a) transported to the completion,
its identities persisting by continuity;
(iii) a self-adjoint `Ĥ ≥ 0` with `‖Ĥ^{1/2} x‖² = sliceHamForm x`
and `exp(-Ĥ) = T̂` — **not landed**: it stops at the named
obstruction recorded in the verdict memo (bounded `exp` is
invertible, `-log` is unbounded at spectrum point `0`, and Mathlib
carries no Friedrichs representation theorem, no unbounded
functional calculus, and no semigroup generation theorem).
Rungs (i) and (ii) land in full; the stop at (iii) is the charter's
own pre-registered PARTIAL shape, not a silent shrink.

Design note (the S2-2c diamond, applied): no `→L[ℂ]` type over the
engine quotient is ever ascribed in this file — bare CLM ascriptions
there select the generic quotient topology over the engine's norm
topology. The extension is built at function level
(`UniformSpace.Completion.extension`) and packaged as a CLM only
over the completion, whose instances are Mathlib's own.

Fences: no `osForm` positivity is asserted anywhere; factored-form
labels stay factored; TM R2 untouched; Stage 1b-B untouched.
NO CLAIM; Clay parts closed: 0.
-/

import ThetLogos.LatticeSliceWeld
import Mathlib.Analysis.InnerProductSpace.Completion

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct

section SliceOperator

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §1. The completed Hilbert space and its dense embedding -/

/-- **The completed Hilbert space** `Ĥspace` of the S2-2 engine:
the uniform-space completion of the pre-Hilbert `Π₁`-quotient.
Mathlib's `UniformSpace.Completion.innerProductSpace` makes it an
`InnerProductSpace ℂ`, and it is complete by construction. All
engine parameters are read off the quotient type. -/
abbrev sliceHilbertSpace (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) : Type _ :=
  UniformSpace.Completion
    (sliceQuotient μG ρ hN2 hρcont hN β hpos)

/-- **The canonical embedding** of the engine space into its
completion: Mathlib's linear isometry `toComplₗᵢ`, whose
underlying function is the completion coercion. -/
noncomputable def sliceEmbed (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceQuotient μG ρ hN2 hρcont hN β hpos →ₗᵢ[ℂ]
      sliceHilbertSpace μG ρ hN2 hρcont hN β hpos :=
  UniformSpace.Completion.toComplₗᵢ

/-- The embedding, applied, is the completion coercion. -/
theorem sliceEmbed_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceEmbed μG ρ hN2 hρcont hN β hpos x
      = ((x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)) := by
  rw [sliceEmbed, UniformSpace.Completion.coe_toComplₗᵢ]

/-- The embedding has dense range in the completed space. -/
theorem sliceEmbed_denseRange (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    DenseRange (sliceEmbed μG ρ hN2 hρcont hN β hpos) := by
  rw [sliceEmbed, UniformSpace.Completion.coe_toComplₗᵢ]
  exact UniformSpace.Completion.denseRange_coe

/-- The embedding is an isometry on norms. -/
theorem sliceEmbed_norm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    ‖sliceEmbed μG ρ hN2 hρcont hN β hpos x‖ = ‖x‖ :=
  LinearIsometry.norm_map _ x

/-- The embedding preserves the inner product. -/
theorem sliceEmbed_inner (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    inner ℂ (sliceEmbed μG ρ hN2 hρcont hN β hpos x)
        (sliceEmbed μG ρ hN2 hρcont hN β hpos y)
      = inner ℂ x y :=
  LinearIsometry.inner_map_map _ x y

/-! ## §2. `T̂` extended by continuity (function level) -/

/-- The engine operator is uniformly continuous (it is the
landed CLM `sliceHatCLM`, read at function level). -/
theorem sliceHat_uniformContinuous (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    UniformContinuous
      (sliceHat μG ρ hN2 hρcont hN β hpos) := by
  have h := (sliceHatCLM μG ρ hN2 hρcont hN β
    hpos).uniformContinuous
  have hfun : ⇑(sliceHatCLM μG ρ hN2 hρcont hN β hpos)
      = ⇑(sliceHat μG ρ hN2 hρcont hN β hpos) :=
    funext (sliceHatCLM_apply μG ρ hN2 hρcont hN β hpos)
  rwa [hfun] at h

/-- **`T̂` on the completed space, as a function:** the
completion extension of `x ↦ ↑(T̂ x)`. (Named `sliceHatCompletedFun`:
the engine module already owns the name `sliceHatFun` for its own
quotient-level function.) -/
noncomputable def sliceHatCompletedFun (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceHilbertSpace μG ρ hN2 hρcont hN β hpos →
      sliceHilbertSpace μG ρ hN2 hρcont hN β hpos :=
  UniformSpace.Completion.extension
    (((↑) : sliceQuotient μG ρ hN2 hρcont hN β hpos →
        sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) ∘
      ⇑(sliceHat μG ρ hN2 hρcont hN β hpos))

/-- The extended function is continuous. -/
theorem sliceHatCompletedFun_continuous (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    Continuous (sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos) := by
  unfold sliceHatCompletedFun
  exact UniformSpace.Completion.continuous_extension

/-- **Agreement on the dense copy:** the extended operator sends
the embedded class of `x` to the embedded class of `T̂ x`. -/
theorem sliceHatCompletedFun_embed (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos
        (sliceEmbed μG ρ hN2 hρcont hN β hpos x)
      = sliceEmbed μG ρ hN2 hρcont hN β hpos
          (sliceHat μG ρ hN2 hρcont hN β hpos x) := by
  have h1 : UniformContinuous
      ((↑) : sliceQuotient μG ρ hN2 hρcont hN β hpos →
        sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :=
    UniformSpace.Completion.uniformContinuous_coe
      (sliceQuotient μG ρ hN2 hρcont hN β hpos)
  have huc : UniformContinuous
      (((↑) : sliceQuotient μG ρ hN2 hρcont hN β hpos →
          sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) ∘
        ⇑(sliceHat μG ρ hN2 hρcont hN β hpos)) :=
    h1.comp (sliceHat_uniformContinuous μG ρ hN2 hρcont hN β hpos)
  rw [sliceEmbed_apply μG ρ hN2 hρcont hN β hpos x,
    sliceEmbed_apply μG ρ hN2 hρcont hN β hpos
      (sliceHat μG ρ hN2 hρcont hN β hpos x)]
  unfold sliceHatCompletedFun
  rw [UniformSpace.Completion.extension_coe huc x]
  rfl

/-! ## §3. Linearity and the continuous-linear packaging -/

/-- The extended function is additive (density + closedness of the
    equality locus, the standard completion argument). -/
theorem sliceHatCompletedFun_add (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u v : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos (u + v)
      = sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos u
        + sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos v := by
  refine UniformSpace.Completion.induction_on₂ u v ?_ ?_
  · exact isClosed_eq
      ((sliceHatCompletedFun_continuous μG ρ hN2 hρcont hN β
        hpos).comp (continuous_fst.add continuous_snd))
      (((sliceHatCompletedFun_continuous μG ρ hN2 hρcont hN β
        hpos).comp continuous_fst).add
        ((sliceHatCompletedFun_continuous μG ρ hN2 hρcont hN β
          hpos).comp continuous_snd))
  · intro a b
    rw [← UniformSpace.Completion.coe_add,
      ← sliceEmbed_apply μG ρ hN2 hρcont hN β hpos (a + b),
      ← sliceEmbed_apply μG ρ hN2 hρcont hN β hpos a,
      ← sliceEmbed_apply μG ρ hN2 hρcont hN β hpos b,
      sliceHatCompletedFun_embed μG ρ hN2 hρcont hN β hpos (a + b),
      sliceHatCompletedFun_embed μG ρ hN2 hρcont hN β hpos a,
      sliceHatCompletedFun_embed μG ρ hN2 hρcont hN β hpos b,
      ← map_add (sliceEmbed μG ρ hN2 hρcont hN β hpos),
      map_add (sliceHat μG ρ hN2 hρcont hN β hpos)]

/-- The extended function is homogeneous. -/
theorem sliceHatCompletedFun_smul (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (c : ℂ)
    (u : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos (c • u)
      = c • sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos u := by
  refine UniformSpace.Completion.induction_on u ?_ ?_
  · exact isClosed_eq
      ((sliceHatCompletedFun_continuous μG ρ hN2 hρcont hN β
        hpos).comp (continuous_id.const_smul c))
      ((sliceHatCompletedFun_continuous μG ρ hN2 hρcont hN β
        hpos).const_smul c)
  · intro a
    rw [← UniformSpace.Completion.coe_smul,
      ← sliceEmbed_apply μG ρ hN2 hρcont hN β hpos (c • a),
      ← sliceEmbed_apply μG ρ hN2 hρcont hN β hpos a,
      sliceHatCompletedFun_embed μG ρ hN2 hρcont hN β hpos (c • a),
      sliceHatCompletedFun_embed μG ρ hN2 hρcont hN β hpos a,
      ← map_smul (sliceEmbed μG ρ hN2 hρcont hN β hpos),
      map_smul (sliceHat μG ρ hN2 hρcont hN β hpos)]

/-- The extended function kills `0`. -/
theorem sliceHatCompletedFun_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos 0 = 0 := by
  rw [← map_zero (sliceEmbed μG ρ hN2 hρcont hN β hpos),
    sliceHatCompletedFun_embed μG ρ hN2 hρcont hN β hpos 0,
    map_zero, map_zero]

/-- **`T̂` on the completed space, as a linear map.** -/
noncomputable def sliceHatLin (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceHilbertSpace μG ρ hN2 hρcont hN β hpos →ₗ[ℂ]
      sliceHilbertSpace μG ρ hN2 hρcont hN β hpos where
  toFun := sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos
  map_add' := sliceHatCompletedFun_add μG ρ hN2 hρcont hN β hpos
  map_smul' := sliceHatCompletedFun_smul μG ρ hN2 hρcont hN β hpos

/-- The linear map applies as the extended function. -/
theorem sliceHatLin_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceHatLin μG ρ hN2 hρcont hN β hpos u
      = sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos u :=
  rfl

/-- **Contraction on the completion:** the extension is norm
    non-increasing at every point of the completed space. -/
theorem sliceHatCompletedFun_norm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    ‖sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos u‖ ≤ ‖u‖ := by
  refine UniformSpace.Completion.induction_on u ?_ ?_
  · exact isClosed_le
      (continuous_norm.comp
        (sliceHatCompletedFun_continuous μG ρ hN2 hρcont hN β hpos))
      continuous_norm
  · intro a
    rw [← sliceEmbed_apply μG ρ hN2 hρcont hN β hpos a,
      sliceHatCompletedFun_embed μG ρ hN2 hρcont hN β hpos a,
      sliceEmbed_norm μG ρ hN2 hρcont hN β hpos a,
      sliceEmbed_norm μG ρ hN2 hρcont hN β hpos
        (sliceHat μG ρ hN2 hρcont hN β hpos a)]
    exact sliceHat_norm_le μG ρ hN2 hρcont hN β hpos a

/-- **`T̂` on the completed space, as a continuous linear map** —
    the rung-1 operator. Built from the linear map with bound `1`. -/
noncomputable def sliceHatCompleted (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceHilbertSpace μG ρ hN2 hρcont hN β hpos →L[ℂ]
      sliceHilbertSpace μG ρ hN2 hρcont hN β hpos :=
  (sliceHatLin μG ρ hN2 hρcont hN β hpos).mkContinuous 1
    (fun u => by
      rw [sliceHatLin_apply μG ρ hN2 hρcont hN β hpos u]
      simpa using sliceHatCompletedFun_norm_le μG ρ hN2 hρcont hN β
        hpos u)

/-- The continuous linear map applies as the extended function. -/
theorem sliceHatCompleted_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceHatCompleted μG ρ hN2 hρcont hN β hpos u
      = sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos u :=
  rfl

/-! ## §4. Rung-1 properties on the completion -/

/-- The completed space is complete (it is a uniform-space
    completion). -/
theorem sliceHilbertSpace_completeSpace (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    CompleteSpace (sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :=
  inferInstance

/-- **Self-adjointness on the completion:** the extended operator
    is symmetric at every pair of points of the completed space
    (bounded and everywhere defined, so symmetric = self-adjoint). -/
theorem sliceHatCompletedFun_symmetric (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u v : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    inner ℂ (sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos u) v
      = inner ℂ u
          (sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos v) := by
  refine UniformSpace.Completion.induction_on₂ u v ?_ ?_
  · exact isClosed_eq
      (UniformSpace.Completion.continuous_inner.comp
        ((sliceHatCompletedFun_continuous μG ρ hN2 hρcont hN β
          hpos).prodMap continuous_id))
      (UniformSpace.Completion.continuous_inner.comp
        (continuous_id.prodMap
          (sliceHatCompletedFun_continuous μG ρ hN2 hρcont hN β
            hpos)))
  · intro a b
    rw [← sliceEmbed_apply μG ρ hN2 hρcont hN β hpos a,
      ← sliceEmbed_apply μG ρ hN2 hρcont hN β hpos b,
      sliceHatCompletedFun_embed μG ρ hN2 hρcont hN β hpos a,
      sliceHatCompletedFun_embed μG ρ hN2 hρcont hN β hpos b,
      sliceEmbed_inner μG ρ hN2 hρcont hN β hpos
        (sliceHat μG ρ hN2 hρcont hN β hpos a) b,
      sliceEmbed_inner μG ρ hN2 hρcont hN β hpos a
        (sliceHat μG ρ hN2 hρcont hN β hpos b)]
    exact sliceHat_isSymmetric μG ρ hN2 hρcont hN β hpos a b

/-- **Factored-form positivity on the completion:** the paired form
    `⟪u, T̂ u⟫` keeps a nonnegative real part at every point of the
    completed space. (Factored Π-form positivity, transported by
    continuity — NOT osForm positivity; see the charter fences.) -/
theorem sliceHatCompletedFun_inner_nonneg (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (u : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    0 ≤ (inner ℂ u
      (sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos u)).re := by
  refine UniformSpace.Completion.induction_on u ?_ ?_
  · have hcont : Continuous
        fun u : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos =>
          (inner ℂ u
            (sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos
              u)).re :=
      Complex.continuous_re.comp
        (continuous_id.inner
          (sliceHatCompletedFun_continuous μG ρ hN2 hρcont hN β
            hpos))
    exact isClosed_le continuous_const hcont
  · intro a
    rw [← sliceEmbed_apply μG ρ hN2 hρcont hN β hpos a,
      sliceHatCompletedFun_embed μG ρ hN2 hρcont hN β hpos a,
      sliceEmbed_inner μG ρ hN2 hρcont hN β hpos a
        (sliceHat μG ρ hN2 hρcont hN β hpos a)]
    exact sliceHat_inner_nonneg μG ρ hN2 hρcont hN β hpos a

/-- **The vacuum of the completed space:** the embedded engine
    vacuum. -/
noncomputable def sliceOmegaCompleted (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceHilbertSpace μG ρ hN2 hρcont hN β hpos :=
  sliceEmbed μG ρ hN2 hρcont hN β hpos
    (sliceOmega μG ρ hN2 hρcont hN β hpos hd)

/-- The completed vacuum is a unit vector. -/
theorem sliceOmegaCompleted_norm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    ‖sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd‖ = 1 := by
  show ‖sliceEmbed μG ρ hN2 hρcont hN β hpos
      (sliceOmega μG ρ hN2 hρcont hN β hpos hd)‖ = 1
  rw [sliceEmbed_norm μG ρ hN2 hρcont hN β hpos
    (sliceOmega μG ρ hN2 hρcont hN β hpos hd),
    sliceOmega_norm μG ρ hN2 hρcont hN β hpos hd]

/-- The extended operator fixes the completed vacuum. -/
theorem sliceHatCompletedFun_omega (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos
        (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd)
      = sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd := by
  show sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos
      (sliceEmbed μG ρ hN2 hρcont hN β hpos
        (sliceOmega μG ρ hN2 hρcont hN β hpos hd))
    = sliceEmbed μG ρ hN2 hρcont hN β hpos
        (sliceOmega μG ρ hN2 hρcont hN β hpos hd)
  rw [sliceHatCompletedFun_embed μG ρ hN2 hρcont hN β hpos
      (sliceOmega μG ρ hN2 hρcont hN β hpos hd),
    sliceHat_sliceOmega μG ρ hN2 hρcont hN β hpos hd]

/-- The operator norm of the completed operator is at most `1`. -/
theorem sliceHatCompleted_norm_le_one (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    ‖sliceHatCompleted μG ρ hN2 hρcont hN β hpos‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u => by
    rw [sliceHatCompleted_apply μG ρ hN2 hρcont hN β hpos u]
    simpa using sliceHatCompletedFun_norm_le μG ρ hN2 hρcont hN β
      hpos u)

/-- **RUNG 1 PACKAGE (the operator package).** On the completed
    Hilbert space `sliceHilbertSpace`, the continuous linear map
    `sliceHatCompleted` (= `T̂` extended by continuity) is a
    self-adjoint contraction preserving the factored-form
    positivity, agreeing with `T̂` on the dense embedded copy of
    the engine space, and fixing a unit vacuum. -/
def sliceOperatorPackage (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) : Prop :=
  (∀ u : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos,
    ‖sliceHatCompleted μG ρ hN2 hρcont hN β hpos u‖ ≤ ‖u‖) ∧
  (∀ u v : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos,
    inner ℂ (sliceHatCompleted μG ρ hN2 hρcont hN β hpos u) v
      = inner ℂ u (sliceHatCompleted μG ρ hN2 hρcont hN β hpos v)) ∧
  (∀ u : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos,
    0 ≤ (inner ℂ u
      (sliceHatCompleted μG ρ hN2 hρcont hN β hpos u)).re) ∧
  (∀ x : sliceQuotient μG ρ hN2 hρcont hN β hpos,
    sliceHatCompleted μG ρ hN2 hρcont hN β hpos
        (sliceEmbed μG ρ hN2 hρcont hN β hpos x)
      = sliceEmbed μG ρ hN2 hρcont hN β hpos
          (sliceHat μG ρ hN2 hρcont hN β hpos x)) ∧
  (sliceHatCompleted μG ρ hN2 hρcont hN β hpos
      (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd)
    = sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd) ∧
  (‖sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd‖ = 1) ∧
  (‖sliceHatCompleted μG ρ hN2 hρcont hN β hpos‖ ≤ 1)

/-- **RUNG 1 STANDS:** the operator package holds for the completed
    transfer operator at every seat where the engine stands. -/
theorem sliceOperator_package (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceOperatorPackage μG ρ hN2 hρcont hN β hpos hd := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    rw [sliceHatCompleted_apply μG ρ hN2 hρcont hN β hpos u]
    exact sliceHatCompletedFun_norm_le μG ρ hN2 hρcont hN β hpos u
  · intro u v
    rw [sliceHatCompleted_apply μG ρ hN2 hρcont hN β hpos u,
      sliceHatCompleted_apply μG ρ hN2 hρcont hN β hpos v]
    exact sliceHatCompletedFun_symmetric μG ρ hN2 hρcont hN β hpos
      u v
  · intro u
    rw [sliceHatCompleted_apply μG ρ hN2 hρcont hN β hpos u]
    exact sliceHatCompletedFun_inner_nonneg μG ρ hN2 hρcont hN β
      hpos u
  · intro x
    rw [sliceHatCompleted_apply μG ρ hN2 hρcont hN β hpos
      (sliceEmbed μG ρ hN2 hρcont hN β hpos x)]
    exact sliceHatCompletedFun_embed μG ρ hN2 hρcont hN β hpos x
  · rw [sliceHatCompleted_apply μG ρ hN2 hρcont hN β hpos
      (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd)]
    exact sliceHatCompletedFun_omega μG ρ hN2 hρcont hN β hpos hd
  · exact sliceOmegaCompleted_norm μG ρ hN2 hρcont hN β hpos hd
  · exact sliceHatCompleted_norm_le_one μG ρ hN2 hρcont hN β hpos

/-! ## §5. The defect on the completion (S2-4 replay) -/

theorem sliceCompleted_inner_self_re (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (inner ℂ x x).re = ‖x‖ ^ 2 := by
  rw [inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

theorem sliceCompleted_inner_self_im (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (inner ℂ x x).im = 0 := by
  rw [inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-- Iterates of the completed operator move across the inner
    product. -/
theorem sliceHatCompletedFun_iter_inner (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (u v : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    inner ℂ u
        ((sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos)^[n]
          v)
      = inner ℂ
          ((sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos)^[n]
            u) v := by
  induction n generalizing u v with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih,
      ← sliceHatCompletedFun_symmetric μG ρ hN2 hρcont hN β
        hpos _ v,
      ← Function.iterate_succ_apply'
        (sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos) n u]

theorem sliceHatCompletedFun_iter_diag_im (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (u : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (inner ℂ u
      ((sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos)^[n]
        u)).im = 0 := by
  have hstar : (starRingEnd ℂ) (inner ℂ u
        ((sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos)^[n]
          u))
      = inner ℂ u
        ((sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos)^[n]
          u) := by
    rw [inner_conj_symm]
    exact (sliceHatCompletedFun_iter_inner μG ρ hN2 hρcont
      hN β hpos n u u).symm
  exact Complex.conj_eq_iff_im.mp hstar

/-- Iterates of the completed operator are contractions. -/
theorem sliceHatCompletedFun_iter_norm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (u : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    ‖(sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos)^[n] u‖
      ≤ ‖u‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact le_trans
      (sliceHatCompletedFun_norm_le μG ρ hN2 hρcont hN β hpos
        _) ih

/-- The CLM's iterates agree with the function's iterates. -/
theorem sliceHatCompleted_iterate (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (u : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (⇑(sliceHatCompleted μG ρ hN2 hρcont hN β hpos))^[n] u
      = (sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos)^[n]
          u := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih,
      sliceHatCompleted_apply μG ρ hN2 hρcont hN β hpos,
      Function.iterate_succ_apply']

/-- **The defect on the completion** `A_c = 1 - T̂_c`. -/
noncomputable def sliceHamCompletedDefect (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceHilbertSpace μG ρ hN2 hρcont hN β hpos →ₗ[ℂ]
    sliceHilbertSpace μG ρ hN2 hρcont hN β hpos :=
  LinearMap.id - sliceHatLin μG ρ hN2 hρcont hN β hpos

theorem sliceHamCompletedDefect_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceHamCompletedDefect μG ρ hN2 hρcont hN β hpos x
      = x - sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos
          x := by
  have h : sliceHamCompletedDefect μG ρ hN2 hρcont hN β
        hpos x
      = x - sliceHatLin μG ρ hN2 hρcont hN β hpos x := by
    simp [sliceHamCompletedDefect]
  rwa [sliceHatLin_apply μG ρ hN2 hρcont hN β hpos x] at h

/-- The completed defect is symmetric. -/
theorem sliceHamCompletedDefect_inner (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    inner ℂ (sliceHamCompletedDefect μG ρ hN2 hρcont hN β
        hpos x) y
      = inner ℂ x (sliceHamCompletedDefect μG ρ hN2 hρcont
          hN β hpos y) := by
  rw [sliceHamCompletedDefect_apply,
    sliceHamCompletedDefect_apply, inner_sub_left,
    inner_sub_right,
    sliceHatCompletedFun_symmetric μG ρ hN2 hρcont hN β hpos
      x y]

/-- Iterates of the completed defect move across the inner
    product. -/
theorem sliceHamCompletedDefect_iter_inner (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    inner ℂ x
        ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
          hpos))^[j] y)
      = inner ℂ
          ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN
            β hpos))^[j] x) y := by
  induction j generalizing x y with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih,
      ← sliceHamCompletedDefect_inner μG ρ hN2 hρcont hN β
        hpos _ y,
      ← Function.iterate_succ_apply'
        (⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
          hpos)) j x]

/-- Iterates of the completed defect are additive. -/
theorem sliceHamCompletedDefect_iter_add (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
        hpos))^[j] (x + y)
      = (⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
          hpos))^[j] x
        + (⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
            hpos))^[j] y := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply' _ _ (x + y), ih, map_add,
      Function.iterate_succ_apply' _ _ x,
      Function.iterate_succ_apply' _ _ y]

/-- Iterates of the completed defect are homogeneous. -/
theorem sliceHamCompletedDefect_iter_smul (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (c : ℂ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
        hpos))^[j] (c • x)
      = c • (⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN
          β hpos))^[j] x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply' _ _ (c • x), ih, map_smul,
      Function.iterate_succ_apply' _ _ x]

theorem sliceHamCompletedDefect_iter_sub (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
        hpos))^[j] (x - y)
      = (⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
          hpos))^[j] x
        - (⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
            hpos))^[j] y := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply' _ _ (x - y), ih, map_sub,
      Function.iterate_succ_apply' _ _ x,
      Function.iterate_succ_apply' _ _ y]

theorem sliceHamCompletedDefect_iter_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ) :
    (⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
        hpos))^[j]
        (0 : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
      = 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, map_zero, ih]

/-- The one-step completed-defect pairing is real and
    nonnegative (term positivity, depth one). -/
theorem sliceHamCompletedDefect_self (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (inner ℂ y (sliceHamCompletedDefect μG ρ hN2 hρcont
        hN β hpos y)).im = 0
      ∧ 0 ≤ (inner ℂ y
          (sliceHamCompletedDefect μG ρ hN2 hρcont hN β
            hpos y)).re
      ∧ (inner ℂ y (sliceHamCompletedDefect μG ρ hN2
          hρcont hN β hpos y)).re
        = ‖y‖ ^ 2
          - (inner ℂ y (sliceHatCompletedFun μG ρ hN2
              hρcont hN β hpos y)).re := by
  have hsym : (inner ℂ y
        (sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos
          y)).im = 0 := by
    have hstar : (starRingEnd ℂ) (inner ℂ y
          (sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos
            y))
        = inner ℂ y (sliceHatCompletedFun μG ρ hN2 hρcont
          hN β hpos y) := by
      rw [inner_conj_symm]
      exact sliceHatCompletedFun_symmetric μG ρ hN2 hρcont
        hN β hpos y y
    exact Complex.conj_eq_iff_im.mp hstar
  refine ⟨?_, ?_, ?_⟩
  · rw [sliceHamCompletedDefect_apply, inner_sub_right,
      Complex.sub_im, hsym, sliceCompleted_inner_self_im μG ρ hN2 hρcont hN β hpos y]
    simp
  · rw [sliceHamCompletedDefect_apply, inner_sub_right,
      Complex.sub_re, sliceCompleted_inner_self_re μG ρ hN2 hρcont hN β hpos y]
    refine sub_nonneg.mpr ?_
    refine le_trans
      (le_trans
        (le_abs_self (inner ℂ y
          (sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos
            y)).re)
        (Complex.abs_re_le_norm _)) ?_
    refine le_trans (norm_inner_le_norm y _) ?_
    calc ‖y‖ * ‖sliceHatCompletedFun μG ρ hN2 hρcont hN β
            hpos y‖
        ≤ ‖y‖ * ‖y‖ :=
        mul_le_mul_of_nonneg_left
          (sliceHatCompletedFun_norm_le μG ρ hN2 hρcont hN β
            hpos y)
          (norm_nonneg y)
      _ = ‖y‖ ^ 2 := by ring
  · rw [sliceHamCompletedDefect_apply, inner_sub_right,
      Complex.sub_re, sliceCompleted_inner_self_re μG ρ hN2 hρcont hN β hpos y]

/-- **Term positivity on the completion.** Every Taylor
    summand's diagonal pairing is a nonnegative real. -/
theorem sliceHamCompletedDefect_iter_diag (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    (inner ℂ x
        ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
          hpos))^[j] x)).im = 0
      ∧ 0 ≤ (inner ℂ x
          ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN
            β hpos))^[j] x)).re := by
  rcases Nat.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hsplit :
        (⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
            hpos))^[j] x
          = (⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN
              β hpos))^[m]
            ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont
              hN β hpos))^[m] x) := by
      rw [hm, Function.iterate_add_apply]
    rw [hsplit,
      sliceHamCompletedDefect_iter_inner μG ρ hN2 hρcont
        hN β hpos m x
        ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
          hpos))^[m] x)]
    exact ⟨sliceCompleted_inner_self_im μG ρ hN2 hρcont hN β hpos _,
      by rw [sliceCompleted_inner_self_re μG ρ hN2 hρcont hN β hpos]; exact sq_nonneg _⟩
  · have hsplit :
        (⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
            hpos))^[j] x
          = (⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN
              β hpos))^[m]
            (sliceHamCompletedDefect μG ρ hN2 hρcont hN β
              hpos
              ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont
                hN β hpos))^[m] x)) := by
      have hjm : j = m + (m + 1) := by omega
      rw [hjm, Function.iterate_add_apply,
        Function.iterate_succ_apply']
    rw [hsplit,
      sliceHamCompletedDefect_iter_inner μG ρ hN2 hρcont
        hN β hpos m x
        (sliceHamCompletedDefect μG ρ hN2 hρcont hN β hpos
          ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN
            β hpos))^[m] x))]
    exact ⟨(sliceHamCompletedDefect_self μG ρ hN2 hρcont
        hN β hpos _).1,
      (sliceHamCompletedDefect_self μG ρ hN2 hρcont hN β
        hpos _).2.1⟩

/-- Per-term parallelogram identity on the completion. -/
theorem sliceHamCompletedDefect_iter_parallelogram
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    inner ℂ (x + y)
        ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
          hpos))^[j] (x + y))
      + inner ℂ (x - y)
        ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
          hpos))^[j] (x - y))
    = 2 * inner ℂ x
        ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
          hpos))^[j] x)
      + 2 * inner ℂ y
        ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
          hpos))^[j] y) := by
  simp only [sliceHamCompletedDefect_iter_add,
    sliceHamCompletedDefect_iter_sub, inner_add_left,
    inner_add_right, inner_sub_left, inner_sub_right]
  ring

/-! ## §6. The form on the completion -/

/-- **The approximant forms on the completion** `q_K`. -/
noncomputable def sliceHamFormApproxC (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) : ℝ :=
  ∑ j ∈ Finset.Icc 1 K, (j : ℝ)⁻¹
    * (inner ℂ x
      ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
        hpos))^[j] x)).re

theorem sliceHamFormApproxC_nonneg (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    0 ≤ sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K
        x := by
  unfold sliceHamFormApproxC
  refine Finset.sum_nonneg fun j _ => ?_
  refine mul_nonneg (by positivity)
    (sliceHamCompletedDefect_iter_diag μG ρ hN2 hρcont hN
      β hpos j x).2

theorem sliceHamFormApproxC_mono (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    Monotone (sliceHamFormApproxC μG ρ hN2 hρcont hN β
      hpos · x) := by
  intro K K' hKK'
  unfold sliceHamFormApproxC
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl hKK') fun j _ _ => ?_
  refine mul_nonneg (by positivity)
    (sliceHamCompletedDefect_iter_diag μG ρ hN2 hρcont hN
      β hpos j x).2

theorem sliceHamFormApproxC_parallelogram (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K (x + y)
        + sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K
          (x - y)
      = 2 * sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos
          K x
        + 2 * sliceHamFormApproxC μG ρ hN2 hρcont hN β
            hpos K y := by
  have hterm : ∀ j ∈ Finset.Icc 1 K,
      (j : ℝ)⁻¹ * (inner ℂ (x + y)
          ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN
            β hpos))^[j] (x + y))).re
        + (j : ℝ)⁻¹ * (inner ℂ (x - y)
          ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN
            β hpos))^[j] (x - y))).re
      = 2 * ((j : ℝ)⁻¹ * (inner ℂ x
          ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN
            β hpos))^[j] x)).re)
        + 2 * ((j : ℝ)⁻¹ * (inner ℂ y
          ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN
            β hpos))^[j] y)).re) := by
    intro j _
    rw [sliceHamCompletedDefect_iter_add,
      sliceHamCompletedDefect_iter_sub]
    have h := congrArg Complex.re
      (sliceHamCompletedDefect_iter_parallelogram μG ρ
        hN2 hρcont hN β hpos j x y)
    norm_num [Complex.add_re, Complex.mul_re] at h
    linear_combination (j : ℝ)⁻¹ * h
  calc sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K
          (x + y)
          + sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos
            K (x - y)
      = ∑ j ∈ Finset.Icc 1 K,
          ((j : ℝ)⁻¹ * (inner ℂ (x + y)
              ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont
                hN β hpos))^[j] (x + y))).re
            + (j : ℝ)⁻¹ * (inner ℂ (x - y)
              ((⇑(sliceHamCompletedDefect μG ρ hN2
                hρcont hN β hpos))^[j] (x - y))).re) := by
        unfold sliceHamFormApproxC
        rw [Finset.sum_add_distrib]
    _ = ∑ j ∈ Finset.Icc 1 K,
          (2 * ((j : ℝ)⁻¹ * (inner ℂ x
              ((⇑(sliceHamCompletedDefect μG ρ hN2
                hρcont hN β hpos))^[j] x)).re)
            + 2 * ((j : ℝ)⁻¹ * (inner ℂ y
              ((⇑(sliceHamCompletedDefect μG ρ hN2
                hρcont hN β hpos))^[j] y)).re)) :=
        Finset.sum_congr rfl hterm
    _ = 2 * sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos
            K x
          + 2 * sliceHamFormApproxC μG ρ hN2 hρcont hN β
              hpos K y := by
        unfold sliceHamFormApproxC
        rw [Finset.sum_add_distrib, Finset.mul_sum,
          Finset.mul_sum]

theorem sliceHamFormApproxC_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ) :
    sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K 0
      = 0 := by
  unfold sliceHamFormApproxC
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [sliceHamCompletedDefect_iter_zero]
  simp

theorem sliceHamFormApproxC_smul (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (c : ℂ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K (c • x)
      = ‖c‖ ^ 2 * sliceHamFormApproxC μG ρ hN2 hρcont hN β
          hpos K x := by
  have hterm : ∀ j : ℕ,
      (inner ℂ (c • x)
          ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN
            β hpos))^[j] (c • x))).re
        = ‖c‖ ^ 2 * (inner ℂ x
            ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont
              hN β hpos))^[j] x)).re := by
    intro j
    have hC : (inner ℂ (c • x)
          ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN
            β hpos))^[j] (c • x)))
        = ((‖c‖ ^ 2 : ℝ) : ℂ) * inner ℂ x
            ((⇑(sliceHamCompletedDefect μG ρ hN2 hρcont
              hN β hpos))^[j] x) := by
      rw [sliceHamCompletedDefect_iter_smul, inner_smul_left,
        inner_smul_right, ← mul_assoc, Complex.conj_mul',
        Complex.ofReal_pow]
    rw [hC, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im,
      (sliceHamCompletedDefect_iter_diag μG ρ hN2 hρcont
        hN β hpos j x).1]
    simp
  unfold sliceHamFormApproxC
  trans (∑ j ∈ Finset.Icc 1 K, ‖c‖ ^ 2 * ((j : ℝ)⁻¹
    * (inner ℂ x ((⇑(sliceHamCompletedDefect μG ρ hN2
        hρcont hN β hpos))^[j] x)).re))
  · exact Finset.sum_congr rfl fun j _ => by
      rw [hterm]; ring
  · rw [Finset.mul_sum]

theorem sliceHamFormApproxC_zero_depth (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos 0 x
      = 0 := by
  unfold sliceHamFormApproxC
  simp

/-- **The Hamiltonian form on the completion**: the
    `ℝ≥0∞`-valued supremum of the completed approximants —
    `sliceHamForm` transported to `Ĥspace`. -/
noncomputable def sliceHamFormC (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    ℝ≥0∞ :=
  ⨆ K : ℕ, ENNReal.ofReal
    (sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K x)

theorem sliceHamFormApproxC_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    ENNReal.ofReal
        (sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K
          x)
      ≤ sliceHamFormC μG ρ hN2 hρcont hN β hpos x :=
  le_iSup (fun K => ENNReal.ofReal
    (sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K x)) K

/-- Defect iterates kill the completed vacuum in positive
    degree. -/
theorem sliceHamCompletedDefect_iter_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d)
    {j : ℕ} (hj : 1 ≤ j) :
    (⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
        hpos))^[j]
        (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd)
      = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Function.iterate_succ_apply,
    sliceHamCompletedDefect_apply,
    sliceHatCompletedFun_omega μG ρ hN2 hρcont hN β hpos
      hd, sub_self, sliceHamCompletedDefect_iter_zero]

theorem sliceHamFormApproxC_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d)
    (K : ℕ) :
    sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K
        (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd)
      = 0 := by
  unfold sliceHamFormApproxC
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  rw [sliceHamCompletedDefect_iter_vacuum μG ρ hN2 hρcont
    hN β hpos hd hj.1]
  simp

/-- The completed Hamiltonian form vanishes at the completed
    vacuum. -/
theorem sliceHamFormC_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceHamFormC μG ρ hN2 hρcont hN β hpos
        (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd)
      = 0 := by
  have hK : ∀ K : ℕ, ENNReal.ofReal
      (sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K
        (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
          hd)) = 0 := by
    intro K
    rw [sliceHamFormApproxC_vacuum μG ρ hN2 hρcont hN β
      hpos hd K]
    simp
  unfold sliceHamFormC
  simp only [hK]
  exact iSup_const

/-- Fixed vectors of the completed operator are invisible to
    the completed form. -/
theorem sliceHamFormC_eq_zero_of_hat_fixed (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos)
    (hx : sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos x
      = x) :
    sliceHamFormC μG ρ hN2 hρcont hN β hpos x = 0 := by
  have hA : sliceHamCompletedDefect μG ρ hN2 hρcont hN β
        hpos x = 0 := by
    rw [sliceHamCompletedDefect_apply, hx, sub_self]
  have hK : ∀ K : ℕ,
      sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K x
        = 0 := by
    intro K
    unfold sliceHamFormApproxC
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [Function.iterate_succ_apply, hA,
      sliceHamCompletedDefect_iter_zero]
    simp
  unfold sliceHamFormC
  simp only [hK]
  rw [ENNReal.ofReal_zero]
  exact iSup_const

/-- **Completed form-domain characterization.** -/
theorem sliceHamFormC_ne_top_iff (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceHamFormC μG ρ hN2 hρcont hN β hpos x ≠ ⊤
      ↔ BddAbove (Set.range fun K =>
          sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K
            x) := by
  constructor
  · intro hfin
    by_contra hnb
    have hunb : ∀ C : ℝ, ∃ K, C
        < sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K
          x := by
      intro C
      by_contra hcon
      push_neg at hcon
      exact hnb ⟨C, fun z hz => by
        obtain ⟨K, rfl⟩ := hz
        exact hcon K⟩
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hfin
    obtain ⟨K, hK⟩ := hunb n
    have h1 : ENNReal.ofReal
          (sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos
            K x)
        ≤ sliceHamFormC μG ρ hN2 hρcont hN β hpos x :=
      sliceHamFormApproxC_le μG ρ hN2 hρcont hN β hpos K x
    have h2 : (n : ℝ≥0∞) < ENNReal.ofReal
        (sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K
          x) := by
      have h3 : ENNReal.ofReal (n : ℝ) < ENNReal.ofReal
          (sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos
            K x) :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
          (Nat.cast_nonneg n)).mpr hK
      rwa [ENNReal.ofReal_natCast] at h3
    exact absurd (h2.trans_le h1) (not_lt_of_gt hn)
  · rintro ⟨C, hC⟩
    have hle : sliceHamFormC μG ρ hN2 hρcont hN β hpos x
        ≤ ENNReal.ofReal C := by
      refine iSup_le fun K => ?_
      exact ENNReal.ofReal_le_ofReal
        (hC (Set.mem_range_self K))
    exact fun htop => ENNReal.ofReal_ne_top
      (top_unique (htop ▸ hle))

/-- **The form domain on the completion**: the finiteness
    locus of `sliceHamFormC`, as a submodule of the completed
    space. -/
noncomputable def sliceHamFormDomainC (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    Submodule ℂ (sliceHilbertSpace μG ρ hN2 hρcont hN β
      hpos) where
  carrier := {x | BddAbove (Set.range fun K =>
    sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K x)}
  add_mem' := by
    intro x y hx hy
    obtain ⟨Cx, hCx⟩ := hx
    obtain ⟨Cy, hCy⟩ := hy
    refine ⟨2 * (Cx + Cy), fun z hz => ?_⟩
    obtain ⟨K, rfl⟩ := hz
    have hpar := sliceHamFormApproxC_parallelogram μG ρ
      hN2 hρcont hN β hpos K x y
    have hnn := sliceHamFormApproxC_nonneg μG ρ hN2
      hρcont hN β hpos K (x - y)
    have hbx := hCx (Set.mem_range_self K)
    have hby := hCy (Set.mem_range_self K)
    linarith
  smul_mem' := by
    intro c x hx
    obtain ⟨C, hC⟩ := hx
    refine ⟨‖c‖ ^ 2 * C, fun z hz => ?_⟩
    obtain ⟨K, rfl⟩ := hz
    show sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K
        (c • x) ≤ ‖c‖ ^ 2 * C
    rw [sliceHamFormApproxC_smul]
    exact mul_le_mul_of_nonneg_left
      (hC (Set.mem_range_self K)) (sq_nonneg ‖c‖)
  zero_mem' := by
    refine ⟨0, fun z hz => ?_⟩
    obtain ⟨K, rfl⟩ := hz
    show sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K 0
      ≤ 0
    rw [sliceHamFormApproxC_zero]

theorem sliceHamC_mem_domain_iff (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    x ∈ sliceHamFormDomainC μG ρ hN2 hρcont hN β hpos
      ↔ sliceHamFormC μG ρ hN2 hρcont hN β hpos x ≠ ⊤ :=
  (sliceHamFormC_ne_top_iff μG ρ hN2 hρcont hN β hpos
    x).symm

theorem sliceHamC_vacuum_mem_domain (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd
      ∈ sliceHamFormDomainC μG ρ hN2 hρcont hN β hpos := by
  rw [sliceHamC_mem_domain_iff,
    sliceHamFormC_vacuum μG ρ hN2 hρcont hN β hpos hd]
  exact ENNReal.zero_ne_top

/-- **The discrete energy forms on the completion**
    `Q_n(u) = ‖u‖² - ⟪u, T̂_cⁿ u⟫`. -/
noncomputable def sliceEnergyFormC (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) : ℝ :=
  ‖x‖ ^ 2 - (inner ℂ x
    ((sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos)^[n]
      x)).re

theorem sliceEnergyFormC_nonneg (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    0 ≤ sliceEnergyFormC μG ρ hN2 hρcont hN β hpos n
        x := by
  unfold sliceEnergyFormC
  refine sub_nonneg.mpr ?_
  refine le_trans
    (le_trans
      (le_abs_self (inner ℂ x
        ((sliceHatCompletedFun μG ρ hN2 hρcont hN β
          hpos)^[n] x)).re)
      (Complex.abs_re_le_norm _)) ?_
  refine le_trans (norm_inner_le_norm x _) ?_
  calc ‖x‖ * ‖(sliceHatCompletedFun μG ρ hN2 hρcont hN β
          hpos)^[n] x‖
      ≤ ‖x‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_left
        (sliceHatCompletedFun_iter_norm_le μG ρ hN2 hρcont
          hN β hpos n x) (norm_nonneg x)
    _ = ‖x‖ ^ 2 := by ring

theorem sliceEnergyFormC_vacuum (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d)
    (n : ℕ) :
    sliceEnergyFormC μG ρ hN2 hρcont hN β hpos n
        (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd)
      = 0 := by
  have hfix : (sliceHatCompletedFun μG ρ hN2 hρcont hN β
        hpos)^[n]
        (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd)
      = sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos
        hd :=
    Function.iterate_fixed
      (sliceHatCompletedFun_omega μG ρ hN2 hρcont hN β
        hpos hd) n
  unfold sliceEnergyFormC
  rw [hfix, sliceCompleted_inner_self_re μG ρ hN2 hρcont hN β hpos,
    sliceOmegaCompleted_norm μG ρ hN2 hρcont hN β hpos hd]
  simp

/-- **Tying identity on the completion:** `Q_1 = q_1`. -/
theorem sliceEnergyFormC_one_eq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    sliceEnergyFormC μG ρ hN2 hρcont hN β hpos 1 x
      = sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos 1
          x := by
  unfold sliceEnergyFormC sliceHamFormApproxC
  rw [Finset.Icc_self, Finset.sum_singleton]
  have hA1 : (⇑(sliceHamCompletedDefect μG ρ hN2 hρcont
        hN β hpos))^[1] x
      = x - sliceHatCompletedFun μG ρ hN2 hρcont hN β
          hpos x := by
    rw [Function.iterate_one]
    exact sliceHamCompletedDefect_apply μG ρ hN2 hρcont
      hN β hpos x
  have hT1 : (sliceHatCompletedFun μG ρ hN2 hρcont hN β
        hpos)^[1] x
      = sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos
          x := by
    rw [Function.iterate_one]
  rw [hA1, hT1, inner_sub_right, Complex.sub_re,
    sliceCompleted_inner_self_re μG ρ hN2 hρcont hN β hpos x]
  simp

/-- **Tying inequality on the completion:** `Q_1` sits
    under the completed form. -/
theorem sliceEnergyFormC_one_le_hamFormC (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos) :
    ENNReal.ofReal
        (sliceEnergyFormC μG ρ hN2 hρcont hN β hpos 1 x)
      ≤ sliceHamFormC μG ρ hN2 hρcont hN β hpos x := by
  rw [sliceEnergyFormC_one_eq]
  exact sliceHamFormApproxC_le μG ρ hN2 hρcont hN β hpos
    1 x

/-! ## §7. Agreement: the completed form extends the S2-4 form -/

/-- Defect iterates intertwine the embedding. -/
theorem sliceHamCompletedDefect_iter_embed (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (j : ℕ)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    (⇑(sliceHamCompletedDefect μG ρ hN2 hρcont hN β
        hpos))^[j]
        (sliceEmbed μG ρ hN2 hρcont hN β hpos x)
      = sliceEmbed μG ρ hN2 hρcont hN β hpos
          ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β
            hpos))^[j] x) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih,
      sliceHamCompletedDefect_apply,
      sliceHatCompletedFun_embed μG ρ hN2 hρcont hN β
        hpos _, ← map_sub,
      ← sliceHamDefect_apply μG ρ hN2 hρcont hN β hpos,
      Function.iterate_succ_apply']

/-- The completed approximants restrict to the S2-4
    approximants on the dense copy. -/
theorem sliceHamFormApproxC_embed (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (K : ℕ)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K
        (sliceEmbed μG ρ hN2 hρcont hN β hpos x)
      = sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K
          x := by
  unfold sliceHamFormApproxC sliceHamFormApprox
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sliceHamCompletedDefect_iter_embed μG ρ hN2 hρcont
    hN β hpos j x,
    sliceEmbed_inner μG ρ hN2 hρcont hN β hpos x
      ((⇑(sliceHamDefect μG ρ hN2 hρcont hN β hpos))^[j]
        x)]

/-- **Transport of the form:** the completed Hamiltonian
    form extends the S2-4 form along the embedding. -/
theorem sliceHamFormC_embed (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceHamFormC μG ρ hN2 hρcont hN β hpos
        (sliceEmbed μG ρ hN2 hρcont hN β hpos x)
      = sliceHamForm μG ρ hN2 hρcont hN β hpos x := by
  unfold sliceHamFormC sliceHamForm
  refine iSup_congr fun K => ?_
  rw [sliceHamFormApproxC_embed μG ρ hN2 hρcont hN β hpos
    K x]

/-- The completed energy forms restrict to the S2-4 energy
    forms on the dense copy. -/
theorem sliceEnergyFormC_embed (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (n : ℕ)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceEnergyFormC μG ρ hN2 hρcont hN β hpos n
        (sliceEmbed μG ρ hN2 hρcont hN β hpos x)
      = sliceEnergyForm μG ρ hN2 hρcont hN β hpos n
          x := by
  have hiter : ∀ n : ℕ,
      (sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos)^[n]
          (sliceEmbed μG ρ hN2 hρcont hN β hpos x)
        = sliceEmbed μG ρ hN2 hρcont hN β hpos
            ((⇑(sliceHat μG ρ hN2 hρcont hN β hpos))^[n]
              x) := by
    intro n
    induction n generalizing x with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih,
        sliceHatCompletedFun_embed μG ρ hN2 hρcont hN β
          hpos _, Function.iterate_succ_apply']
  unfold sliceEnergyFormC sliceEnergyForm
  rw [hiter n, sliceEmbed_inner μG ρ hN2 hρcont hN β hpos
    x _, sliceEmbed_norm μG ρ hN2 hρcont hN β hpos x]

/-- Domain transport: a quotient vector is in the S2-4 form
    domain iff its embedded copy is in the completed domain. -/
theorem sliceEmbed_mem_domainC_iff (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceEmbed μG ρ hN2 hρcont hN β hpos x
        ∈ sliceHamFormDomainC μG ρ hN2 hρcont hN β hpos
      ↔ x ∈ sliceHamFormDomain μG ρ hN2 hρcont hN β
          hpos := by
  rw [sliceHamC_mem_domain_iff, sliceHamFormC_embed,
    sliceHam_mem_domain_iff]

/-! ## §8. The rung-2 form package -/

/-- **The completed Hamiltonian form package**: the S2-4
    form package replayed on the completion, plus the
    transport clauses identifying the completed form with
    the S2-4 form on the dense embedded copy. -/
def sliceCompletedFormPackage (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    Prop :=
  (∀ K (x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos),
      0 ≤ sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos
        K x)
  ∧ (∀ K (x : sliceHilbertSpace μG ρ hN2 hρcont hN β
        hpos),
      sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K x
        ≤ sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos
            (K + 1) x)
  ∧ (∀ K (x y : sliceHilbertSpace μG ρ hN2 hρcont hN β
        hpos),
      sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K
          (x + y)
        + sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K
            (x - y)
        = 2 * sliceHamFormApproxC μG ρ hN2 hρcont hN β
              hpos K x
          + 2 * sliceHamFormApproxC μG ρ hN2 hρcont hN β
              hpos K y)
  ∧ (∀ K (c : ℂ) (x : sliceHilbertSpace μG ρ hN2 hρcont
        hN β hpos),
      sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K
          (c • x)
        = ‖c‖ ^ 2 * sliceHamFormApproxC μG ρ hN2 hρcont
            hN β hpos K x)
  ∧ (∀ K, sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos
      K 0 = 0)
  ∧ (∀ x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos,
      sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos 0 x
        = 0)
  ∧ sliceHamFormC μG ρ hN2 hρcont hN β hpos
      (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd)
      = 0
  ∧ sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd
      ∈ sliceHamFormDomainC μG ρ hN2 hρcont hN β hpos
  ∧ (∀ x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos,
      x ∈ sliceHamFormDomainC μG ρ hN2 hρcont hN β hpos
        ↔ sliceHamFormC μG ρ hN2 hρcont hN β hpos x ≠ ⊤)
  ∧ (∀ n (x : sliceHilbertSpace μG ρ hN2 hρcont hN β
        hpos),
      0 ≤ sliceEnergyFormC μG ρ hN2 hρcont hN β hpos n x)
  ∧ (∀ n, sliceEnergyFormC μG ρ hN2 hρcont hN β hpos n
      (sliceOmegaCompleted μG ρ hN2 hρcont hN β hpos hd)
      = 0)
  ∧ (∀ x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos,
      sliceEnergyFormC μG ρ hN2 hρcont hN β hpos 1 x
        = sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos
            1 x)
  ∧ (∀ x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos,
      ENNReal.ofReal (sliceEnergyFormC μG ρ hN2 hρcont hN
          β hpos 1 x)
        ≤ sliceHamFormC μG ρ hN2 hρcont hN β hpos x)
  ∧ (∀ x : sliceHilbertSpace μG ρ hN2 hρcont hN β hpos,
      sliceHatCompletedFun μG ρ hN2 hρcont hN β hpos x = x
        → sliceHamFormC μG ρ hN2 hρcont hN β hpos x = 0)
  ∧ (∀ K (x : sliceHilbertSpace μG ρ hN2 hρcont hN β
        hpos),
      ENNReal.ofReal (sliceHamFormApproxC μG ρ hN2 hρcont
          hN β hpos K x)
        ≤ sliceHamFormC μG ρ hN2 hρcont hN β hpos x)
  ∧ (∀ K (x : sliceQuotient μG ρ hN2 hρcont hN β hpos),
      sliceHamFormApproxC μG ρ hN2 hρcont hN β hpos K
          (sliceEmbed μG ρ hN2 hρcont hN β hpos x)
        = sliceHamFormApprox μG ρ hN2 hρcont hN β hpos K
            x)
  ∧ (∀ x : sliceQuotient μG ρ hN2 hρcont hN β hpos,
      sliceHamFormC μG ρ hN2 hρcont hN β hpos
          (sliceEmbed μG ρ hN2 hρcont hN β hpos x)
        = sliceHamForm μG ρ hN2 hρcont hN β hpos x)
  ∧ (∀ n (x : sliceQuotient μG ρ hN2 hρcont hN β hpos),
      sliceEnergyFormC μG ρ hN2 hρcont hN β hpos n
          (sliceEmbed μG ρ hN2 hρcont hN β hpos x)
        = sliceEnergyForm μG ρ hN2 hρcont hN β hpos n x)
  ∧ (∀ x : sliceQuotient μG ρ hN2 hρcont hN β hpos,
      sliceEmbed μG ρ hN2 hρcont hN β hpos x
          ∈ sliceHamFormDomainC μG ρ hN2 hρcont hN β hpos
        ↔ x ∈ sliceHamFormDomain μG ρ hN2 hρcont hN β
            hpos)

/-- **RUNG 2 STANDS:** the completed form package holds at
    every seat where the engine stands. -/
theorem sliceCompletedForm_package (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceCompletedFormPackage μG ρ hN2 hρcont hN β hpos
      hd :=
  ⟨fun K x => sliceHamFormApproxC_nonneg μG ρ hN2 hρcont
      hN β hpos K x,
   fun K x => (sliceHamFormApproxC_mono μG ρ hN2 hρcont
      hN β hpos x) (Nat.le_succ K),
   fun K x y => sliceHamFormApproxC_parallelogram μG ρ
      hN2 hρcont hN β hpos K x y,
   fun K c x => sliceHamFormApproxC_smul μG ρ hN2 hρcont
      hN β hpos K c x,
   fun K => sliceHamFormApproxC_zero μG ρ hN2 hρcont hN
      β hpos K,
   fun x => sliceHamFormApproxC_zero_depth μG ρ hN2
      hρcont hN β hpos x,
   sliceHamFormC_vacuum μG ρ hN2 hρcont hN β hpos hd,
   sliceHamC_vacuum_mem_domain μG ρ hN2 hρcont hN β hpos
      hd,
   fun x => sliceHamC_mem_domain_iff μG ρ hN2 hρcont hN
      β hpos x,
   fun n x => sliceEnergyFormC_nonneg μG ρ hN2 hρcont
      hN β hpos n x,
   fun n => sliceEnergyFormC_vacuum μG ρ hN2 hρcont hN β
      hpos hd n,
   fun x => sliceEnergyFormC_one_eq μG ρ hN2 hρcont hN
      β hpos x,
   fun x => sliceEnergyFormC_one_le_hamFormC μG ρ hN2
      hρcont hN β hpos x,
   fun x hx => sliceHamFormC_eq_zero_of_hat_fixed μG ρ
      hN2 hρcont hN β hpos x hx,
   fun K x => sliceHamFormApproxC_le μG ρ hN2 hρcont hN
      β hpos K x,
   fun K x => sliceHamFormApproxC_embed μG ρ hN2 hρcont
      hN β hpos K x,
   fun x => sliceHamFormC_embed μG ρ hN2 hρcont hN β
      hpos x,
   fun n x => sliceEnergyFormC_embed μG ρ hN2 hρcont
      hN β hpos n x,
   fun x => sliceEmbed_mem_domainC_iff μG ρ hN2 hρcont
      hN β hpos x⟩

/-! ## §9. Specializations -/

/-- **U(1) seat, operator package, hypothesis-free:** at the
    circle seat the completed operator package holds for
    every `β ≥ 0` (via S2-3's `sliceHPosOne_circle`). -/
theorem sliceOperator_circle_package (hN2 : 2 ≤ N)
    (hN : Even N) (β : ℝ) (hβ : 0 ≤ β) :
    sliceOperatorPackage (haarProb Circle) circleRep hN2
      circleRep_continuous hN β
      (sliceHPosOne_circle hN2 hN β hβ) zero_lt_one :=
  sliceOperator_package (haarProb Circle) circleRep hN2
    circleRep_continuous hN β
    (sliceHPosOne_circle hN2 hN β hβ) zero_lt_one

/-- **U(1) seat, form package, hypothesis-free.** -/
theorem sliceCompletedForm_circle_package (hN2 : 2 ≤ N)
    (hN : Even N) (β : ℝ) (hβ : 0 ≤ β) :
    sliceCompletedFormPackage (haarProb Circle) circleRep
      hN2 circleRep_continuous hN β
      (sliceHPosOne_circle hN2 hN β hβ) zero_lt_one :=
  sliceCompletedForm_package (haarProb Circle) circleRep
    hN2 circleRep_continuous hN β
    (sliceHPosOne_circle hN2 hN β hβ) zero_lt_one

/-- **β = 0 on the completion:** the extended operator is
    the identity on the whole completed space (the quotient
    regression `T̂ = id` transported by density). -/
theorem sliceHatCompletedFun_beta_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d)
    (u : sliceHilbertSpace μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)) :
    sliceHatCompletedFun μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) u
      = u := by
  refine UniformSpace.Completion.induction_on u ?_ ?_
  · exact isClosed_eq
      (sliceHatCompletedFun_continuous μG ρ hN2 hρcont hN
        0 (sliceHPosOne_zero μG ρ hN2 hρcont hN hd))
      continuous_id
  · intro x
    have h0 : sliceHat μG ρ hN2 hρcont hN 0
          (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) x
        = x := by
      simp only [sliceRegression_hat_eq_id μG ρ hN2
        hρcont hN hd, LinearMap.id_apply]
    rw [← sliceEmbed_apply μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) x,
      sliceHatCompletedFun_embed μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) x, h0]

/-- **β = 0, CLM form:** the completed transfer operator is
    the identity continuous linear map. -/
theorem sliceHatCompleted_beta_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) :
    sliceHatCompleted μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)
      = ContinuousLinearMap.id ℂ
          (sliceHilbertSpace μG ρ hN2 hρcont hN 0
            (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)) := by
  apply ContinuousLinearMap.ext
  intro u
  simp [sliceHatCompleted_apply μG ρ hN2 hρcont hN 0
    (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) u,
    sliceHatCompletedFun_beta_zero μG ρ hN2 hρcont hN hd
      u]

/-- **β = 0 on the completion, form level:** the completed
    Hamiltonian form is identically zero, for general
    `(G, ρ)` — every vector of the completed space is a
    fixed vector of the identity operator. -/
theorem sliceHamFormC_beta_zero (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d)
    (u : sliceHilbertSpace μG ρ hN2 hρcont hN 0
      (sliceHPosOne_zero μG ρ hN2 hρcont hN hd)) :
    sliceHamFormC μG ρ hN2 hρcont hN 0
        (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) u
      = 0 :=
  sliceHamFormC_eq_zero_of_hat_fixed μG ρ hN2 hρcont hN
    0 (sliceHPosOne_zero μG ρ hN2 hρcont hN hd) u
    (sliceHatCompletedFun_beta_zero μG ρ hN2 hρcont hN hd
      u)

end SliceOperator

end ThetLogos
