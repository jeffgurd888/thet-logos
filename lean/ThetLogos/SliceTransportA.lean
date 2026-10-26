/-
# Route A′ — the `osSpace` form-gap by compact spectral
# decomposition, and the completion-transport assembly

`SliceTransport` landed A1 (the completed weld) and A3
(the moment step) of the completion transport and stopped
A2 at the scoping memo's slip condition: the `cfc` step
at `transferOp` over `osSpace` does not synthesize in the
pinned Mathlib (v4.35.0-rc3) — the generic instance's
`StarRing`-derived star is not defeq to
`ContinuousLinearMap.instStarId` — so the continuous
functional calculus at `transferOp` is NOT used anywhere
in this module. Route A′ (the scoping memo's fallback)
replaces it by the compact spectral decomposition:

* the transfer operator at the seat is compact
  (`transferOp_compact_of_HDen` + `hden_seat`, modulo the
  carried Hilbert basis) and self-adjoint;
* its restriction `S` to the vacuum-orthogonal subspace
  `H₀ = (ℂ ∙ Ω)ᗮ` is again compact self-adjoint; the
  eigenvalues of `S` are eigenvalues of `transferOp`,
  never `1` (the `1`-eigenspace is the vacuum line, by
  `fixed_mem_span`), so `GapBoundU1` bounds them all by
  `1 − δ` in norm, through the Fredholm bridge
  `IsCompactOperator.hasEigenvalue_iff_mem_spectrum`
  (and `HasEigenvalue.mem_spectrum` at `μ = 0`);
* for `δ ≤ 1` the spectral radius of `S` — which for a
  self-adjoint operator is its norm — is therefore at
  most `1 − δ`, and the Rayleigh quotient of `S` at `z`
  is exactly the pairing `⟪z, transferOp z⟫.re / ‖z‖²`;
* for `δ > 1` the gap bound leaves no room for any
  eigenspace but the vacuum line: the compact spectral
  theorem (`orthogonalComplement_iSup_eigenspaces_eq_bot`)
  then forces `H₀ = ⊥`, so the only `z ⊥ Ω` is `0`.

The headline is the form-gap itself. With A1 + A3
already landed, the battery's gap conjunct
(`sliceTransport_gap_pairing`) is the memo's three
lines, and with `sliceBattery_jensen` the full
`SliceSpectralCorrespondence` becomes a theorem at the
seat (`sliceSpectralCorrespondence_of_transport`),
modulo exactly the seat's carried data: `β > 0`, the
gap bound `GapBoundU1`, `δ ≤ 1`, and a Hilbert basis of
`osSpace` (separability carried as data, FG-1's
convention — the same data `sliceBattery_gap_exists`
carries).

Fences: fixed volume; per-instance `δ = δ(β, N)`;
Items 3 (uniform estimates) and 4 (continuum) untouched.
NO CLAIM; Clay parts closed: 0.
-/

import ThetLogos.SliceTransport
import ThetLogos.LatticeVacuumSimple
import ThetLogos.LatticeHdenSeat
import ThetLogos.LatticeTransferCompact

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct

section SliceTransportA

variable {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) (hN : Even N)
  (β : ℝ)
  (hpos : SliceHPosOne (haarProb Circle) circleRep hN2
    circleRep_continuous β)

/-! ## Seat facts: symmetry, vacuum invariance -/

/-- The circle seat's transfer operator is symmetric
(self-adjointness, read as a pairing identity). -/
theorem transferOp_isSymmetric_circle (hN' : Even N) :
    (transferOp (haarProb Circle) circleRep hN2
      circleRep_continuous β).IsSymmetric :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (transferOp_isSelfAdjoint (haarProb Circle) circleRep
      hN2 circleRep_continuous hN' β)

/-- `transferOp` preserves the vacuum-orthogonal
subspace `H₀ = (ℂ ∙ Ω)ᗮ` at the seat: the vacuum is
fixed and the operator is symmetric. -/
theorem transferOp_mem_vacuumOrthogonal_circle
    (hN' : Even N)
    (v : osSpace (N := N) (haarProb Circle) circleRep β)
    (hv : v ∈ (Submodule.span ℂ {osVacuum (N := N) (haarProb Circle) circleRep circleRep_continuous zero_lt_one β})ᗮ) :
    transferOp (haarProb Circle) circleRep hN2
        circleRep_continuous β v
      ∈ (Submodule.span ℂ {osVacuum (N := N) (haarProb Circle) circleRep circleRep_continuous zero_lt_one β})ᗮ := by
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
  have h1 : inner ℂ (osVacuum (haarProb Circle) circleRep
        circleRep_continuous zero_lt_one β)
      (transferOp (haarProb Circle) circleRep hN2
        circleRep_continuous β v) = 0 := by
    have hsymm := transferOp_isSymmetric_circle hN2 β hN'
    have h2 : inner ℂ (transferOp (haarProb Circle)
          circleRep hN2 circleRep_continuous β
          (osVacuum (haarProb Circle) circleRep
            circleRep_continuous zero_lt_one β)) v
        = inner ℂ (osVacuum (haarProb Circle) circleRep
            circleRep_continuous zero_lt_one β)
          (transferOp (haarProb Circle) circleRep hN2
            circleRep_continuous β v) :=
      hsymm (osVacuum (haarProb Circle) circleRep
        circleRep_continuous zero_lt_one β) v
    rw [transferOp_vacuum (haarProb Circle) circleRep hN2
        circleRep_continuous zero_lt_one β] at h2
    rw [← h2]
    exact hv (osVacuum (haarProb Circle) circleRep
      circleRep_continuous zero_lt_one β)
      (Submodule.subset_span (Set.mem_singleton _))
  rw [inner_smul_left, h1, mul_zero]

/-- The `1`-eigenspace of the seat's transfer operator
lies in the vacuum line (fixed vectors are vacuum
multiples, `fixed_mem_span`). -/
theorem transferOp_eigenspace_one_le_span_circle :
    Module.End.eigenspace
        (transferOp (haarProb Circle) circleRep hN2
          circleRep_continuous β).toLinearMap 1
      ≤ Submodule.span ℂ {osVacuum (N := N) (haarProb Circle) circleRep circleRep_continuous zero_lt_one β} := by
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv
  apply fixed_mem_span (haarProb Circle) circleRep hN2
    circleRep_continuous zero_lt_one β v
  simpa using hv

/-! ## The compression to the vacuum-orthogonal subspace -/

/-- **The compression** `S` of the seat's transfer
operator to the vacuum-orthogonal subspace `H₀`: the
restriction along the invariance of `H₀`. -/
noncomputable def sliceTransportRestrict (hN' : Even N) :
    ↥(Submodule.span ℂ {osVacuum (N := N) (haarProb Circle) circleRep circleRep_continuous zero_lt_one β})ᗮ
      →L[ℂ]
    ↥(Submodule.span ℂ {osVacuum (N := N) (haarProb Circle) circleRep circleRep_continuous zero_lt_one β})ᗮ :=
  (transferOp (haarProb Circle) circleRep hN2
    circleRep_continuous β).restrict
      (transferOp_mem_vacuumOrthogonal_circle hN2 β hN')

/-- The compression's ambient value is the transfer
operator applied to the ambient vector. -/
theorem sliceTransportRestrict_coe (hN' : Even N)
    (w : ↥(Submodule.span ℂ {osVacuum (N := N) (haarProb Circle) circleRep circleRep_continuous zero_lt_one β})ᗮ) :
    ((sliceTransportRestrict hN2 β hN' w :
      ↥(Submodule.span ℂ {osVacuum (N := N) (haarProb Circle) circleRep circleRep_continuous zero_lt_one β})ᗮ) :
        osSpace (N := N) (haarProb Circle) circleRep β)
      = transferOp (haarProb Circle) circleRep hN2
          circleRep_continuous β
          (w : osSpace (N := N) (haarProb Circle)
            circleRep β) :=
  ContinuousLinearMap.coe_restrict_apply _ _

/-- The compression is compact: the seat's transfer
operator is compact (`transferOp_compact_of_HDen` at
`hden_seat`, modulo the carried Hilbert basis), and
compactness restricts to an invariant complete
subspace. -/
theorem sliceTransportRestrict_isCompact (hN' : Even N)
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (osSpace (N := N)
      (haarProb Circle) circleRep β)) :
    IsCompactOperator ⇑(sliceTransportRestrict hN2 β
      hN') := by
  have hcomp : IsCompactOperator ⇑(transferOp
      (haarProb Circle) circleRep hN2
        circleRep_continuous β) :=
    transferOp_compact_of_HDen (haarProb Circle)
      circleRep β hN2 circleRep_continuous zero_lt_one
      (hden_seat hN2 β) b
  exact hcomp.restrict'
    (transferOp_mem_vacuumOrthogonal_circle hN2 β hN')

/-- The compression is symmetric: its pairings are the
transfer operator's pairings, read in the ambient
space. -/
theorem sliceTransportRestrict_isSymmetric
    (hN' : Even N) :
    (sliceTransportRestrict hN2 β hN').IsSymmetric := by
  intro a b
  show inner ℂ ((sliceTransportRestrict hN2 β hN' a :
        ↥(Submodule.span ℂ {osVacuum (N := N) (haarProb Circle) circleRep circleRep_continuous zero_lt_one β})ᗮ) :
          osSpace (N := N) (haarProb Circle) circleRep β)
      ((b : ↥(Submodule.span ℂ {osVacuum (N := N) (haarProb Circle) circleRep circleRep_continuous zero_lt_one β})ᗮ) :
          osSpace (N := N) (haarProb Circle) circleRep β)
    = inner ℂ ((a : ↥(Submodule.span ℂ {osVacuum (N := N) (haarProb Circle) circleRep circleRep_continuous zero_lt_one β})ᗮ) :
          osSpace (N := N) (haarProb Circle) circleRep β)
      ((sliceTransportRestrict hN2 β hN' b :
        ↥(Submodule.span ℂ {osVacuum (N := N) (haarProb Circle) circleRep circleRep_continuous zero_lt_one β})ᗮ) :
          osSpace (N := N) (haarProb Circle) circleRep β)
  rw [sliceTransportRestrict_coe, sliceTransportRestrict_coe]
  exact transferOp_isSymmetric_circle hN2 β hN' a b

/-- **Norm of the compression.** Every spectral point
of the compression `S` of `transferOp` to the
vacuum-orthogonal subspace is an eigenvalue of
`transferOp` itself, never `1` (the `1`-eigenspace is
the vacuum line, by vacuum simplicity), so `GapBoundU1`
bounds the whole spectrum of `S` by `1 − δ`; since `S`
is self-adjoint, its spectral radius is its norm. -/
theorem sliceTransportRestrict_norm_le
    (hN' : Even N) (δ : ℝ) (hδ : δ ≤ 1)
    (hgap : GapBoundU1 β hN2 δ)
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (osSpace (N := N)
      (haarProb Circle) circleRep β)) :
    ‖sliceTransportRestrict hN2 β hN'‖ ≤ 1 - δ := by
    have hSsa : IsSelfAdjoint (sliceTransportRestrict
        hN2 β hN') :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
        (sliceTransportRestrict_isSymmetric hN2 β hN')
    have hScomp : IsCompactOperator
        ⇑(sliceTransportRestrict hN2 β hN') :=
      sliceTransportRestrict_isCompact hN2 β hN' b
    -- Every spectral point of the compression is `≤ 1 − δ`
    -- in norm: it is an eigenvalue, hence an eigenvalue of
    -- `transferOp`, never `1`, so `GapBoundU1` applies.
    have hspecbound : ∀ k ∈ spectrum ℂ
        (sliceTransportRestrict hN2 β hN'),
        ‖k‖ ≤ 1 - δ := by
      intro k hk
      by_cases hk0 : k = 0
      · rw [hk0, norm_zero]
        linarith
      · have heigS : Module.End.HasEigenvalue
            (sliceTransportRestrict hN2 β
              hN').toLinearMap k :=
          (IsCompactOperator.hasEigenvalue_iff_mem_spectrum
            hScomp hk0).mpr hk
        obtain ⟨v, hv⟩ := heigS.exists_hasEigenvector
        have hTeq : transferOp (haarProb Circle) circleRep
              hN2 circleRep_continuous β
              (v : osSpace (N := N) (haarProb Circle)
                circleRep β)
            = k • (v : osSpace (N := N) (haarProb Circle)
                circleRep β) := by
          have h' : sliceTransportRestrict hN2 β hN' v
              = k • v := hv.apply_eq_smul
          have h2 := congrArg (fun w :
              ↥(Submodule.span ℂ {osVacuum (N := N) (haarProb Circle) circleRep circleRep_continuous zero_lt_one β})ᗮ =>
              (w : osSpace (N := N) (haarProb Circle)
                circleRep β)) h'
          rwa [sliceTransportRestrict_coe hN2 β hN' v,
            Submodule.coe_smul] at h2
        have heigT : Module.End.HasEigenvalue
            (transferOp (haarProb Circle) circleRep hN2
              circleRep_continuous β).toLinearMap k :=
          Module.End.hasEigenvalue_of_hasEigenvector
            ⟨(Module.End.mem_eigenspace_iff).mpr hTeq, by
              intro h0
              apply hv.2
              exact Subtype.ext h0⟩
        have hspec : k ∈ spectrum ℂ (transferOp
            (haarProb Circle) circleRep hN2
              circleRep_continuous β) := by
          rw [ContinuousLinearMap.spectrum_eq]
          exact heigT.mem_spectrum
        have hk1 : k ≠ 1 := by
          intro hk1
          have hfix : transferOp (haarProb Circle)
                circleRep hN2 circleRep_continuous β
                (v : osSpace (N := N) (haarProb Circle)
                  circleRep β)
              = (v : osSpace (N := N) (haarProb Circle)
                  circleRep β) := by
            rw [hk1, one_smul] at hTeq
            exact hTeq
          have hmem := fixed_mem_span (haarProb Circle)
            circleRep hN2 circleRep_continuous zero_lt_one
            β (v : osSpace (N := N) (haarProb Circle)
              circleRep β) hfix
          have hvv : inner ℂ
              (v : osSpace (N := N) (haarProb Circle)
                circleRep β)
              (v : osSpace (N := N) (haarProb Circle)
                circleRep β) = 0 := by
            have hvH := v.2
            rw [Submodule.mem_orthogonal] at hvH
            exact hvH (v : osSpace (N := N) (haarProb
              Circle) circleRep β) hmem
          have hvE : (v : osSpace (N := N) (haarProb
              Circle) circleRep β) = 0 :=
            inner_self_eq_zero.mp hvv
          exact hv.2 (Subtype.ext hvE)
        exact hgap k hspec hk1
    -- The spectral radius of `S` — its norm, by
    -- self-adjointness — is at most `1 − δ`.
    set hδnn : ℝ≥0 := ⟨1 - δ, by linarith⟩ with hδnn_eq
    have hrad : spectralRadius ℂ
          (sliceTransportRestrict hN2 β hN')
        ≤ (hδnn : ℝ≥0∞) := by
      rw [spectralRadius_eq_of_unital]
      refine iSup_le fun k => iSup_le fun hk => ?_
      have hbound := hspecbound k hk
      rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe,
        hδnn_eq]
      exact_mod_cast hbound
    have hnorm := ContinuousLinearMap.spectralRadius_eq_nnnorm
      (sliceTransportRestrict hN2 β hN') hSsa
    rw [hnorm] at hrad
    have h2 : ‖sliceTransportRestrict hN2 β hN'‖₊
        ≤ hδnn := ENNReal.coe_le_coe.mp hrad
    have h4 : (‖sliceTransportRestrict hN2 β hN'‖₊ : ℝ)
        ≤ (hδnn : ℝ) := h2
    rw [coe_nnnorm, hδnn_eq] at h4
    exact_mod_cast h4

/-- **Collapse above the gap edge.** If `δ > 1`, the
gap bound leaves no eigenspace of `transferOp` alive
except possibly the vacuum eigenspace at `1`: every
other eigenspace is `⊥` (an eigenvalue there would lie
in the spectrum with norm `≤ 1 − δ < 0`). The compact
spectral theorem then forces every `z ⊥ Ω` to be `0`. -/
theorem transferOp_vacuumOrthogonal_eq_zero_circle
    (hN' : Even N) (δ : ℝ) (hδ : 1 < δ)
    (hgap : GapBoundU1 β hN2 δ)
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (osSpace (N := N)
      (haarProb Circle) circleRep β))
    (z : osSpace (N := N) (haarProb Circle) circleRep β)
    (hz : inner ℂ z (osVacuum (haarProb Circle) circleRep
        circleRep_continuous zero_lt_one β) = 0) :
    z = 0 := by
  have hcomp : IsCompactOperator ⇑(transferOp
      (haarProb Circle) circleRep hN2
        circleRep_continuous β) :=
    transferOp_compact_of_HDen (haarProb Circle)
      circleRep β hN2 circleRep_continuous zero_lt_one
      (hden_seat hN2 β) b
  have hsymm := transferOp_isSymmetric_circle hN2 β hN'
  have hzH : z ∈ (Submodule.span ℂ {osVacuum (N := N) (haarProb Circle) circleRep circleRep_continuous zero_lt_one β})ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [inner_smul_left, ← inner_conj_symm, hz]
    simp
  have heig : ∀ μ : ℂ, μ ≠ 1 →
      Module.End.eigenspace (transferOp (haarProb Circle)
        circleRep hN2 circleRep_continuous
          β).toLinearMap μ = ⊥ := by
    intro μ hμ
    by_contra hne
    have hev : Module.End.HasEigenvalue (transferOp
        (haarProb Circle) circleRep hN2
          circleRep_continuous β).toLinearMap μ :=
      Module.End.hasEigenvalue_iff.mpr hne
    have hspec : μ ∈ spectrum ℂ (transferOp (haarProb
        Circle) circleRep hN2 circleRep_continuous β) := by
      rw [ContinuousLinearMap.spectrum_eq]
      exact hev.mem_spectrum
    have hle := hgap μ hspec hμ
    have hnorm := norm_nonneg μ
    linarith
  have hbot : (⨆ μ, Module.End.eigenspace (transferOp
      (haarProb Circle) circleRep hN2
        circleRep_continuous β).toLinearMap μ)ᗮ = ⊥ :=
    ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
      hcomp hsymm
  have hzS : z ∈ (⨆ μ, Module.End.eigenspace (transferOp
      (haarProb Circle) circleRep hN2
        circleRep_continuous β).toLinearMap μ)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.iSup_induction _ hu
      (motive := fun u => inner ℂ u z = 0) ?_
      (inner_zero_left z) ?_
    · intro μ w hw
      by_cases hμ : μ = 1
      · subst hμ
        exact Submodule.inner_right_of_mem_orthogonal
          (transferOp_eigenspace_one_le_span_circle
            hN2 β hw) hzH
      · rw [heig μ hμ] at hw
        rw [(Submodule.mem_bot ℂ).mp hw]
        exact inner_zero_left z
    · intro x y hx hy
      rw [inner_add_left, hx, hy, add_zero]
  rw [hbot] at hzS
  exact (Submodule.mem_bot ℂ).mp hzS


/-! ## The form-gap (Route A′) -/

/-- **The `osSpace` form-gap — Route A′.** At the U(1)
seat (`β > 0`, even `N ≥ 2`), for every `z ⊥ Ω` in
`osSpace`,
`⟪z, transferOp z⟫.re ≤ (1 − δ)‖z‖²`, where `δ` is a
Q12 gap bound (`GapBoundU1`). Proved by compact spectral
decomposition — compression to the vacuum-orthogonal
subspace, the Fredholm eigenvalue/spectrum bridge, and
the Rayleigh quotient — with no functional calculus at
`transferOp`. The Hilbert basis is the seat's carried
separability data (as in `sliceBattery_gap_exists`). -/
theorem transferOp_form_gap_circle
    (hN' : Even N)
    (hβ : 0 < β) (δ : ℝ) (hgap : GapBoundU1 β hN2 δ)
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (osSpace (N := N)
      (haarProb Circle) circleRep β))
    (z : osSpace (N := N) (haarProb Circle) circleRep β)
    (hz : inner ℂ z (osVacuum (haarProb Circle) circleRep
        circleRep_continuous zero_lt_one β) = 0) :
    (inner ℂ z (transferOp (haarProb Circle) circleRep
        hN2 circleRep_continuous β z)).re
      ≤ (1 - δ) * ‖z‖ ^ 2 := by
  have hcomp : IsCompactOperator ⇑(transferOp
      (haarProb Circle) circleRep hN2
        circleRep_continuous β) :=
    transferOp_compact_of_HDen (haarProb Circle)
      circleRep β hN2 circleRep_continuous zero_lt_one
      (hden_seat hN2 β) b
  have hsymm := transferOp_isSymmetric_circle hN2 β hN'
  -- `z` lies in the vacuum-orthogonal subspace `H₀`.
  have hzH : z ∈ (Submodule.span ℂ {osVacuum (N := N) (haarProb Circle) circleRep circleRep_continuous zero_lt_one β})ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [inner_smul_left, ← inner_conj_symm, hz]
    simp
  by_cases hδ : δ ≤ 1
  · -- **Case `δ ≤ 1`:** compression, spectral radius, Rayleigh.
    have hSnorm := sliceTransportRestrict_norm_le
      hN2 β hN' δ hδ hgap b
    -- Rayleigh's quotient at `z` is the claimed pairing.
    by_cases hz0 : z = 0
    · rw [hz0]; simp
    · set w : ↥(Submodule.span ℂ {osVacuum (N := N) (haarProb Circle) circleRep circleRep_continuous zero_lt_one β})ᗮ :=
        ⟨z, hzH⟩ with hw
      have hrq : (inner ℂ z (transferOp (haarProb Circle)
            circleRep hN2 circleRep_continuous β z)).re
          = (sliceTransportRestrict hN2 β
              hN').rayleighQuotient w * ‖z‖ ^ 2 := by
        have hpairC : inner ℂ
              (sliceTransportRestrict hN2 β hN' w) w
            = inner ℂ z (transferOp (haarProb Circle)
                circleRep hN2 circleRep_continuous β z) := by
          have hs : inner ℂ (sliceTransportRestrict hN2
                β hN' w) w
              = inner ℂ w (sliceTransportRestrict hN2 β
                  hN' w) :=
            (sliceTransportRestrict_isSymmetric hN2 β
              hN') w w
          rw [hs]
          show inner ℂ
              ((w : osSpace (N := N) (haarProb Circle)
                  circleRep β))
              ((sliceTransportRestrict hN2 β hN' w :
                ↥(Submodule.span ℂ {osVacuum (N := N) (haarProb Circle) circleRep circleRep_continuous zero_lt_one β})ᗮ) :
                  osSpace (N := N) (haarProb Circle)
                    circleRep β)
            = inner ℂ z (transferOp (haarProb Circle)
                circleRep hN2 circleRep_continuous β z)
          rw [sliceTransportRestrict_coe]
        have hpair : RCLike.re (inner ℂ
              (sliceTransportRestrict hN2 β hN' w) w)
            = (inner ℂ z (transferOp (haarProb Circle)
                circleRep hN2 circleRep_continuous β
                  z)).re := congrArg RCLike.re hpairC
        show (inner ℂ z (transferOp (haarProb Circle)
              circleRep hN2 circleRep_continuous β z)).re
          = (ContinuousLinearMap.reApplyInnerSelf
              (sliceTransportRestrict hN2 β hN') w)
              / ‖w‖ ^ 2 * ‖z‖ ^ 2
        rw [ContinuousLinearMap.reApplyInnerSelf_apply,
          hpair]
        have hnormw : ‖w‖ = ‖z‖ := rfl
        have h2 : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2
          (norm_ne_zero_iff.mpr hz0)
        rw [hnormw]
        exact (div_mul_cancel₀ _ h2).symm
      have hle : (sliceTransportRestrict hN2 β
            hN').rayleighQuotient w ≤ 1 - δ :=
        le_trans (le_abs_self _)
          (le_trans ((sliceTransportRestrict hN2 β
            hN').rayleighQuotient_le_norm w) hSnorm)
      rw [hrq]
      exact mul_le_mul_of_nonneg_right hle (sq_nonneg ‖z‖)
  · -- **Case `δ > 1`:** no eigenspace but the vacuum line
    -- survives the gap bound; the compact spectral theorem
    -- then leaves no room for `z ⊥ Ω` but `z = 0`.
    have hz0 := transferOp_vacuumOrthogonal_eq_zero_circle
      hN2 β hN' δ (not_le.mp hδ) hgap b z hz
    rw [hz0]; simp

/-! ## Assembly: the battery's gap conjunct -/

/-- **The battery's gap conjunct, discharged.** For a
unit domain state `x ⊥ Ω` of the circle seat's
Hamiltonian, the completed transfer pairing is at most
`1 − δ`: A1's moments (`b₁ = ‖W_c x‖²`,
`b₂ = ⟪W_c x, transferOp (W_c x)⟫.re`) and A3's moment
step (`b₁² ≤ b₂`) meet the form-gap
(`b₂ ≤ (1 − δ) b₁`); divide by `b₁ > 0`, or read
`b₁ = 0 ≤ 1 − δ` directly. -/
theorem sliceTransport_gap_pairing
    (hβ : 0 < β) (δ : ℝ) (hδ1 : δ ≤ 1)
    (hgap : GapBoundU1 β hN2 δ)
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (osSpace (N := N)
      (haarProb Circle) circleRep β))
    (x : ↥(sliceHamOperatorDomain (haarProb Circle)
        circleRep hN2 circleRep_continuous hN β hpos))
    (hx : ‖x.1‖ = 1)
    (horth : inner ℂ x.1 (sliceBatteryVacuum
        (haarProb Circle) circleRep hN2
          circleRep_continuous hN β hpos zero_lt_one)
      = 0) :
    (inner ℂ (x.1).1 (sliceTc (haarProb Circle)
        circleRep hN2 circleRep_continuous hN β hpos
          (x.1).1)).re ≤ 1 - δ := by
  have hy : ‖(x.1).1‖ = 1 := hx
  have horth' : inner ℂ (x.1).1 (sliceOmegaCompleted
      (haarProb Circle) circleRep hN2 circleRep_continuous
        hN β hpos zero_lt_one) = 0 := horth
  have horthW : inner ℂ (sliceWeldCompleted hN2 hN β hpos
        (x.1).1)
      (osVacuum (haarProb Circle) circleRep
        circleRep_continuous zero_lt_one β) = 0 :=
    sliceWeldCompleted_orthogonal hN2 hN β hpos (x.1).1
      horth'
  have hfg := transferOp_form_gap_circle hN2 β hN hβ δ
    hgap b (sliceWeldCompleted hN2 hN β hpos (x.1).1)
    horthW
  rw [sliceWeldCompleted_second_moment hN2 hN β hpos
      (x.1).1,
    sliceWeldCompleted_norm_sq hN2 hN β hpos (x.1).1]
    at hfg
  have hA3 := sliceTransport_moment_sq hN2 hN β hpos
    (x.1).1 hy
  have hb1nn : 0 ≤ (inner ℂ (x.1).1 (sliceTc (haarProb
      Circle) circleRep hN2 circleRep_continuous hN β
        hpos (x.1).1)).re := by
    rw [← sliceWeldCompleted_norm_sq hN2 hN β hpos
      (x.1).1]
    exact sq_nonneg _
  by_cases hb1 : (inner ℂ (x.1).1 (sliceTc (haarProb
      Circle) circleRep hN2 circleRep_continuous hN β
        hpos (x.1).1)).re = 0
  · rw [hb1]; linarith
  · have hb1pos : 0 < (inner ℂ (x.1).1 (sliceTc (haarProb
        Circle) circleRep hN2 circleRep_continuous hN β
          hpos (x.1).1)).re :=
      lt_of_le_of_ne hb1nn (Ne.symm hb1)
    have hchain : (inner ℂ (x.1).1 (sliceTc (haarProb
          Circle) circleRep hN2 circleRep_continuous hN
            β hpos (x.1).1)).re
        * (inner ℂ (x.1).1 (sliceTc (haarProb Circle)
            circleRep hN2 circleRep_continuous hN β hpos
              (x.1).1)).re
        ≤ (1 - δ) * (inner ℂ (x.1).1 (sliceTc (haarProb
            Circle) circleRep hN2 circleRep_continuous hN
              β hpos (x.1).1)).re :=
      le_trans (by rwa [pow_two] at hA3) hfg
    exact (mul_le_mul_iff_left₀ hb1pos).mp hchain

/-- **The spectral correspondence at the seat — the
battery's one named hypothesis, discharged.** Jensen
(FG-2c-4) below, the transported gap above: under the
seat's carried data (`β > 0`, a Q12 gap bound with
`δ ∈ (0, 1)`, a Hilbert basis of `osSpace`),
`SliceSpectralCorrespondence` is a theorem, and T4's
smallest-quantum bound (`sliceBattery_smallest_quantum`)
loses its last hypothesis. -/
theorem sliceSpectralCorrespondence_of_transport
    (hβ : 0 < β) (δ : ℝ) (_hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hgap : GapBoundU1 β hN2 δ)
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (osSpace (N := N)
      (haarProb Circle) circleRep β)) :
    SliceSpectralCorrespondence β hN2 hN δ hpos := by
  intro x hx horth
  exact ⟨sliceBattery_jensen β hN2 hN hpos x hx,
    sliceTransport_gap_pairing hN2 hN β hpos hβ δ hδ1.le
      hgap b x hx horth⟩

end SliceTransportA

end ThetLogos
