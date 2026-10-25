/-
# S2-5 — THE WELD (Stage 2, Brick S2-5, charter price M)

The weld between the S2-2 engine space (the `Π₁`-quotient
pre-Hilbert space over `𝔸_slice`, with its reconstructed step
operator `T̂`) and the landed slice picture (S1: `sliceState` /
`transferOp` on `osSpace = L²(sliceMeasure)`).

Charter: `whitepaper/stage2-reconstruction-scoping-2026-10-24.md`
§S2-5, as revised by
`whitepaper/stage2-s22-gate-revision-2026-10-24.md`. Surviving
objects only: `𝔸_slice`, `Π₁`/`Π₂`. NOT consumed (dead): `𝔸⁺`,
the `P₂` pairing, `twoPointOp`.

**The shape of the weld (kill K-S2-5, fired in its anticipated
form).** The engine norm on a class is the *transfer-form* norm
`‖[a]‖² = (⟪s a, T (s a)⟫).re`, NOT the `L²` norm
`(⟪s a, s a⟫).re` of the slice state: `sliceState` itself does
not descend to the `Π₁`-quotient. What descends is the *stepped*
state `a ↦ T (sliceState a)` — its kernel contains the `Π₁`
radical, because `Π₂(a, a) = ‖T (s a)‖²` and the diagonal
domination `Π₂(a,a).re ≤ Π₁(a,a).re` kills it on the radical.
The descended map `W` intertwines `T̂` with `transferOp`
exactly, is a contraction, and is an isometry for the
`T̂`-twisted form: `⟪W x, W y⟫ = ⟪x, T̂ y⟫`. The weld therefore
lands as the charter's form-level shadow, labeled PARTIAL with
the norm discrepancy named (§5). Fences: no completion, no
operator `Ĥ`, no `exp(−Ĥ) = T̂`; positivity of `T̂` comes from
OS positivity of the pairings, never from `transferOp` on
arbitrary vectors (TM R2 fence). NO CLAIM.
-/

import ThetLogos.LatticeSliceEngine
import ThetLogos.LatticeSlicePairing
import ThetLogos.LatticeSliceHamiltonian
import ThetLogos.LatticeTransferID

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct

section SliceWeld

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §1. The stepped state map on observables -/

/-- **The stepped state map** on slice observables:
`a ↦ T (sliceState a)` — the slice state pushed one transfer
step into the bulk. This composite, not `sliceState` itself,
is what descends to the `Π₁`-quotient (§2). -/
noncomputable def sliceStepStateMap (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    ↥(sliceObsSubmodule (N := N) μG ρ β) →ₗ[ℂ]
    osSpace (N := N) μG ρ β where
  toFun a := transferOp μG ρ hN2 hρcont β
    (sliceState μG ρ β a.1 a.2)
  map_add' := by
    intro a b
    show transferOp μG ρ hN2 hρcont β
        (sliceState μG ρ β (a.1 + b.1) (a.2.add b.2))
      = transferOp μG ρ hN2 hρcont β (sliceState μG ρ β a.1 a.2)
        + transferOp μG ρ hN2 hρcont β
          (sliceState μG ρ β b.1 b.2)
    rw [sliceState_add μG ρ β a.1 b.1 a.2 b.2, map_add]
  map_smul' := by
    intro c a
    show transferOp μG ρ hN2 hρcont β
        (sliceState μG ρ β (c • a.1) (a.2.const_smul c))
      = c • transferOp μG ρ hN2 hρcont β
          (sliceState μG ρ β a.1 a.2)
    rw [sliceState_smul μG ρ β c a.1 a.2, map_smul]

/-- The stepped state map applies as its defining composite
(definitional). -/
theorem sliceStepStateMap_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (a : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    sliceStepStateMap μG ρ hN2 hρcont β a
      = transferOp μG ρ hN2 hρcont β
        (sliceState μG ρ β a.1 a.2) :=
  rfl

/-! ## §2. Descent: the radical lies in the kernel -/

/-- **Descent of the stepped state:** a `Π₁`-null observable
has vanishing stepped state. The chain is `Π₂`'s two readings:
`Π₂(a, a) = ‖T (s a)‖²` (2a's stepped reading of `Π₂`) and the
diagonal domination `Π₂(a,a).re ≤ Π₁(a,a).re` (2b's
(D-bdd)ʳ), so `Π₁(a, a) = 0` forces `‖T (s a)‖² ≤ 0`. This is
the exact point where the un-stepped `sliceState` fails to
descend and the stepped one succeeds. -/
theorem sliceStepStateMap_eq_zero_of_mem_null (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (a : ↥(sliceObsSubmodule (N := N) μG ρ β))
    (ha : a ∈ sliceNullSubmodule μG ρ hN2 hρcont hN β hpos) :
    sliceStepStateMap μG ρ hN2 hρcont β a = 0 := by
  have h1 : slicePairOne μG ρ hN2 hρcont β a.1 a.2 a.1 a.2 = 0 :=
    (mem_sliceNullSubmodule μG ρ a).mp ha
  have h2 := slicePairTwo_self_re_le μG ρ hN2 hρcont hN β hpos
    a.1 a.2
  rw [h1] at h2
  have h2' : (slicePairTwo μG ρ hN2 hρcont β a.1 a.2 a.1 a.2).re
      ≤ 0 := by simpa using h2
  have h3 : slicePairTwo μG ρ hN2 hρcont β a.1 a.2 a.1 a.2
      = ((‖transferOp μG ρ hN2 hρcont β
          (sliceState μG ρ β a.1 a.2)‖ ^ 2 : ℝ) : ℂ) := by
    rw [slicePairTwo_eq_inner_steps μG ρ hN2 hρcont hN β
      a.1 a.1 a.2 a.2, inner_self_eq_norm_sq_to_K]
    norm_cast
  have h3re : (slicePairTwo μG ρ hN2 hρcont β
        a.1 a.2 a.1 a.2).re
      = ‖transferOp μG ρ hN2 hρcont β
          (sliceState μG ρ β a.1 a.2)‖ ^ 2 := by
    rw [h3, Complex.ofReal_re]
  have h4 : ‖transferOp μG ρ hN2 hρcont β
        (sliceState μG ρ β a.1 a.2)‖ ^ 2 = 0 :=
    le_antisymm (h3re ▸ h2') (sq_nonneg _)
  have h5 : transferOp μG ρ hN2 hρcont β
        (sliceState μG ρ β a.1 a.2) = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp h4)
  exact h5

/-! ## §3. The weld map -/

/-- **The weld map** `W`: the descended stepped state, a
linear map from the engine space (the `Π₁`-quotient) to the
slice picture's space `osSpace`. -/
noncomputable def sliceWeldMap (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :
    sliceQuotient μG ρ hN2 hρcont hN β hpos →ₗ[ℂ]
    osSpace (N := N) μG ρ β :=
  (sliceNullSubmodule μG ρ hN2 hρcont hN β hpos).liftQ
    (sliceStepStateMap μG ρ hN2 hρcont β) (by
      intro a ha
      rw [LinearMap.mem_ker]
      exact sliceStepStateMap_eq_zero_of_mem_null μG ρ hN2
        hρcont hN β hpos a ha)

/-- **The weld on a class** is the stepped state of any
representative: `W [a] = T (sliceState a)`. -/
theorem sliceWeldMap_mk (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (a : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    sliceWeldMap μG ρ hN2 hρcont hN β hpos
        (sliceMk μG ρ hN2 hρcont hN β hpos a)
      = transferOp μG ρ hN2 hρcont β
        (sliceState μG ρ β a.1 a.2) :=
  Submodule.liftQ_apply _ _ _

/-- **The form identity of the weld:** `W` transports the
engine's inner product to the `T̂`-twisted form —
`⟪W x, W y⟫ = ⟪x, T̂ y⟫` for all classes. Both sides are
`Π₂` of representatives: the left by 2a's stepped reading of
`Π₂`, the right by the engine's pairing characterization of
`T̂`. So `W` is an isometry from the engine space carrying
the twisted form `(x, y) ↦ ⟪x, T̂ y⟫` onto its image in
`osSpace` with its `L²` inner product. -/
theorem sliceWeldMap_inner (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x y : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    inner ℂ (sliceWeldMap μG ρ hN2 hρcont hN β hpos x)
        (sliceWeldMap μG ρ hN2 hρcont hN β hpos y)
      = inner ℂ x (sliceHat μG ρ hN2 hρcont hN β hpos y) := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro a
  refine Submodule.Quotient.induction_on _ y ?_
  intro b
  rw [sliceWeldMap_mk, sliceWeldMap_mk,
    ← slicePairTwo_eq_inner_steps μG ρ hN2 hρcont hN β
      a.1 b.1 a.2 b.2]
  exact (sliceHat_pairing μG ρ hN2 hρcont hN β hpos b a).symm

/-! ## §4. The weld is a contraction -/

/-- **Squared norm of the weld on a class:**
`‖W [a]‖² = (Π₂(a, a)).re` — the `L²` norm of the stepped
state is the two-step pairing's diagonal. -/
theorem sliceWeldMap_mk_norm_sq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (a : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    ‖sliceWeldMap μG ρ hN2 hρcont hN β hpos
        (sliceMk μG ρ hN2 hρcont hN β hpos a)‖ ^ 2
      = (slicePairTwoObs μG ρ hN2 hρcont β a a).re := by
  rw [sliceWeldMap_mk]
  have h3 : slicePairTwo μG ρ hN2 hρcont β a.1 a.2 a.1 a.2
      = ((‖transferOp μG ρ hN2 hρcont β
          (sliceState μG ρ β a.1 a.2)‖ ^ 2 : ℝ) : ℂ) := by
    rw [slicePairTwo_eq_inner_steps μG ρ hN2 hρcont hN β
      a.1 a.1 a.2 a.2, inner_self_eq_norm_sq_to_K]
    norm_cast
  show ‖transferOp μG ρ hN2 hρcont β
        (sliceState μG ρ β a.1 a.2)‖ ^ 2
      = (slicePairTwo μG ρ hN2 hρcont β a.1 a.2 a.1 a.2).re
  rw [h3, Complex.ofReal_re]

/-- **The weld contracts:** `‖W x‖² ≤ ‖x‖²` on the whole
engine space — 2b's diagonal domination
`Π₂(a,a).re ≤ Π₁(a,a).re` read through the two norm
identities. -/
theorem sliceWeldMap_norm_sq_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    ‖sliceWeldMap μG ρ hN2 hρcont hN β hpos x‖ ^ 2
      ≤ ‖x‖ ^ 2 := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro a
  rw [sliceWeldMap_mk_norm_sq, sliceQuotient_norm_sq,
    sliceQuotient_inner_mk]
  exact slicePairTwo_self_re_le μG ρ hN2 hρcont hN β hpos
    a.1 a.2

/-- **The weld is a contraction** (operator norm `≤ 1`)
from the engine space to `osSpace`, at every real `β`,
under H-pos(1)ʳ. -/
theorem sliceWeldMap_norm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    ‖sliceWeldMap μG ρ hN2 hρcont hN β hpos x‖ ≤ ‖x‖ :=
  le_of_pow_le_pow_left₀ (by norm_num) (norm_nonneg x)
    (sliceWeldMap_norm_sq_le μG ρ hN2 hρcont hN β hpos x)

/-- **`W` as a continuous linear map** (operator norm
`≤ 1`): the weld, bundled with its contraction bound. -/
noncomputable def sliceWeldCLM (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) :=
  LinearMap.mkContinuous (sliceWeldMap μG ρ hN2 hρcont hN
    β hpos) 1 (fun x => by
      have h := sliceWeldMap_norm_le μG ρ hN2 hρcont hN β
        hpos x
      simpa using h)

/-- The continuous linear map `W` applies as the linear
map `W`. -/
theorem sliceWeldCLM_apply (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceWeldCLM μG ρ hN2 hρcont hN β hpos x
      = sliceWeldMap μG ρ hN2 hρcont hN β hpos x :=
  rfl

/-! ## §5. Intertwining -/

/-- **Intertwining:** the weld carries the reconstructed
operator to the landed one — `W ∘ T̂ = transferOp ∘ W` on
the whole engine space. On a class this is
`sliceState_sliceStepObs` (S1's step read on observables)
transported through the descent: S1's depth-one identity,
extended from quadratic forms to the operators themselves. -/
theorem sliceWeldMap_sliceHat (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceWeldMap μG ρ hN2 hρcont hN β hpos
        (sliceHat μG ρ hN2 hρcont hN β hpos x)
      = transferOp μG ρ hN2 hρcont β
        (sliceWeldMap μG ρ hN2 hρcont hN β hpos x) := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro a
  rw [sliceHat_apply_mk, sliceWeldMap_mk, sliceWeldMap_mk,
    sliceState_sliceStepObs μG ρ hN2 hρcont β a]

/-- **Intertwining, CLM form:** `W ∘L T̂ = transferOp ∘ W`
with both operators as continuous linear maps. -/
theorem sliceWeldCLM_sliceHatCLM (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceWeldCLM μG ρ hN2 hρcont hN β hpos
        (sliceHatCLM μG ρ hN2 hρcont hN β hpos x)
      = transferOp μG ρ hN2 hρcont β
        (sliceWeldCLM μG ρ hN2 hρcont hN β hpos x) := by
  rw [sliceHatCLM_apply, sliceWeldCLM_apply, sliceWeldCLM_apply]
  exact sliceWeldMap_sliceHat μG ρ hN2 hρcont hN β hpos x

/-! ## §6. The depth-one identity on classes -/

/-- **S1's depth-one identity, on classes:** the engine's
inner product of two classes is the slice picture's pairing
of the first representative's state against the second's
weld image — `⟪[a], [b]⟫ = ⟪s a, W [b]⟫`. This is exactly
`Π₁ = ⟪s ·, T (s ·)⟫` (S1) with the quotient's inner product
on the left and the descended map on the right. -/
theorem sliceQuotient_inner_eq_state_weld (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (a b : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    inner ℂ (sliceMk μG ρ hN2 hρcont hN β hpos a)
        (sliceMk μG ρ hN2 hρcont hN β hpos b)
      = inner ℂ (sliceState μG ρ β a.1 a.2)
        (sliceWeldMap μG ρ hN2 hρcont hN β hpos
          (sliceMk μG ρ hN2 hρcont hN β hpos b)) := by
  rw [sliceQuotient_inner_mk, sliceWeldMap_mk]
  rfl

/-- **S1's identity in its original `osForm` dress, on
classes:** `⟪[a], [b]⟫ = osForm (sliceObs a) (sliceObs b)`
— the engine's inner product IS the OS form of the pulled-
back slice observables (2a's `slicePairOne_eq_osForm`,
descended). -/
theorem sliceQuotient_inner_eq_osForm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d)
    (a b : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    inner ℂ (sliceMk μG ρ hN2 hρcont hN β hpos a)
        (sliceMk μG ρ hN2 hρcont hN β hpos b)
      = osForm μG ρ β (sliceObs a.1) (sliceObs b.1) := by
  rw [sliceQuotient_inner_mk]
  exact slicePairOne_eq_osForm μG ρ hN2 hρcont hN hd β
    a.1 b.1 a.2 b.2

/-! ## §7. The vacuum -/

/-- **The weld sends vacuum to vacuum:** `W Ω = Ω₀`, the
OS vacuum — the stepped state of the constant observable is
the vacuum, which `transferOp` fixes (stationarity). -/
theorem sliceWeldMap_sliceOmega (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceWeldMap μG ρ hN2 hρcont hN β hpos
        (sliceOmega μG ρ hN2 hρcont hN β hpos hd)
      = osVacuum μG ρ hρcont hd β := by
  show sliceWeldMap μG ρ hN2 hρcont hN β hpos
      (sliceMk μG ρ hN2 hρcont hN β hpos
        (sliceOneObs μG ρ β hd hρcont)) = _
  rw [sliceWeldMap_mk]
  show transferOp μG ρ hN2 hρcont β
      (sliceState μG ρ β 1
        (memLp_one_slice μG ρ β hd hρcont)) = _
  rw [sliceState_one_eq_osVacuum μG ρ hρcont hd β
    (memLp_one_slice μG ρ β hd hρcont),
    transferOp_vacuum μG ρ hN2 hρcont hd β]

/-! ## §8. The Hamiltonian form against the slice picture -/

/-- **The depth-one energy form is the weld's norm
defect:** S2-4's `Q₁ x = ‖x‖² − ⟪x, T̂ x⟫.re` reads,
through the weld's form identity, as
`Q₁ x = ‖x‖² − ‖W x‖²` — the one-step energy of a class is
exactly the norm its weld image loses in `osSpace`. -/
theorem sliceEnergyForm_one_eq_weldNorm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    sliceEnergyForm μG ρ hN2 hρcont hN β hpos 1 x
      = ‖x‖ ^ 2 - ‖sliceWeldMap μG ρ hN2 hρcont hN β hpos x‖
          ^ 2 := by
  have hdiag : (inner ℂ
        (sliceWeldMap μG ρ hN2 hρcont hN β hpos x)
        (sliceWeldMap μG ρ hN2 hρcont hN β hpos x)).re
      = ‖sliceWeldMap μG ρ hN2 hρcont hN β hpos x‖ ^ 2 := by
    have h3 : inner ℂ
          (sliceWeldMap μG ρ hN2 hρcont hN β hpos x)
          (sliceWeldMap μG ρ hN2 hρcont hN β hpos x)
        = ((‖sliceWeldMap μG ρ hN2 hρcont hN β hpos x‖
            ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [h3, Complex.ofReal_re]
  show ‖x‖ ^ 2 - (inner ℂ x
      ((⇑(sliceHat μG ρ hN2 hρcont hN β hpos))^[1] x)).re
    = ‖x‖ ^ 2 - ‖sliceWeldMap μG ρ hN2 hρcont hN β hpos x‖
        ^ 2
  rw [Function.iterate_one,
    ← sliceWeldMap_inner μG ρ hN2 hρcont hN β hpos x x,
    hdiag]

/-- **The weld's norm defect sits under the Hamiltonian
form:** S2-4's tying inequality `ofReal Q₁ ≤ Ĥ`-form,
restated against the slice picture —
`ENNReal.ofReal (‖x‖² − ‖W x‖²) ≤ sliceHamForm x`. -/
theorem sliceEnergyForm_one_le_hamForm_of_weld (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (x : sliceQuotient μG ρ hN2 hρcont hN β hpos) :
    ENNReal.ofReal (‖x‖ ^ 2
        - ‖sliceWeldMap μG ρ hN2 hρcont hN β hpos x‖ ^ 2)
      ≤ sliceHamForm μG ρ hN2 hρcont hN β hpos x := by
  rw [← sliceEnergyForm_one_eq_weldNorm μG ρ hN2 hρcont
    hN β hpos x]
  exact sliceEnergyForm_one_le_hamForm μG ρ hN2 hρcont hN
    β hpos x

/-! ## §9. The norm comparison (kill K-S2-5's clause) -/

/-- **The engine norm is the transfer-form norm:** for a
class, `‖[a]‖² = (⟪s a, W [a]⟫).re` — the slice state
paired against its own transfer step, through the weld. -/
theorem sliceQuotient_norm_sq_eq_state_weld (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (a : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    ‖sliceMk μG ρ hN2 hρcont hN β hpos a‖ ^ 2
      = (inner ℂ (sliceState μG ρ β a.1 a.2)
          (sliceWeldMap μG ρ hN2 hρcont hN β hpos
            (sliceMk μG ρ hN2 hρcont hN β hpos a))).re := by
  rw [sliceQuotient_norm_sq,
    sliceQuotient_inner_eq_state_weld μG ρ hN2 hρcont hN
      β hpos a a]

/-- **The slice state's own `L²` norm, for contrast:**
`‖s a‖² = (⟪s a, s a⟫).re` — the self-pairing, with no
transfer step. The pair
(`sliceQuotient_norm_sq_eq_state_weld`, this) is the named
K-S2-5 discrepancy: the quotient norm pairs the state with
its *step*, the `L²` norm pairs it with *itself*; the two
agree only where `transferOp` acts trivially on the state,
which is why no unitary or `L²`-isometric weld exists at
this generality and the weld lands at form level. -/
theorem sliceState_norm_sq_eq (β : ℝ)
    (a : ↥(sliceObsSubmodule (N := N) μG ρ β)) :
    ‖sliceState μG ρ β a.1 a.2‖ ^ 2
      = (inner ℂ (sliceState μG ρ β a.1 a.2)
          (sliceState μG ρ β a.1 a.2)).re := by
  have h3 : inner ℂ (sliceState μG ρ β a.1 a.2)
        (sliceState μG ρ β a.1 a.2)
      = ((‖sliceState μG ρ β a.1 a.2‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h3, Complex.ofReal_re]

/-! ## §10. The bundled package -/

/-- **The weld package** (S2-5): the full list of
weld-level properties, as one Prop for the Stage 2 closing
summary to consume. Form-level throughout (K-S2-5): no
unitary, no `L²`-isometry, the norm discrepancy carried
openly as clauses 7–8's pair of identities (clause 7 here
is the transfer-form identity; the contrasting `L²`
self-pairing identity is `sliceState_norm_sq_eq`). -/
def sliceWeldPackage (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    Prop :=
  (∀ a : ↥(sliceObsSubmodule (N := N) μG ρ β),
    sliceWeldMap μG ρ hN2 hρcont hN β hpos
        (sliceMk μG ρ hN2 hρcont hN β hpos a)
      = transferOp μG ρ hN2 hρcont β
        (sliceState μG ρ β a.1 a.2))
  ∧ (∀ x : sliceQuotient μG ρ hN2 hρcont hN β hpos,
      ‖sliceWeldMap μG ρ hN2 hρcont hN β hpos x‖ ≤ ‖x‖)
  ∧ (∀ x : sliceQuotient μG ρ hN2 hρcont hN β hpos,
      sliceWeldMap μG ρ hN2 hρcont hN β hpos
          (sliceHat μG ρ hN2 hρcont hN β hpos x)
        = transferOp μG ρ hN2 hρcont β
          (sliceWeldMap μG ρ hN2 hρcont hN β hpos x))
  ∧ (∀ x y : sliceQuotient μG ρ hN2 hρcont hN β hpos,
      inner ℂ (sliceWeldMap μG ρ hN2 hρcont hN β hpos x)
          (sliceWeldMap μG ρ hN2 hρcont hN β hpos y)
        = inner ℂ x (sliceHat μG ρ hN2 hρcont hN β hpos y))
  ∧ (∀ a b : ↥(sliceObsSubmodule (N := N) μG ρ β),
      inner ℂ (sliceMk μG ρ hN2 hρcont hN β hpos a)
          (sliceMk μG ρ hN2 hρcont hN β hpos b)
        = inner ℂ (sliceState μG ρ β a.1 a.2)
          (sliceWeldMap μG ρ hN2 hρcont hN β hpos
            (sliceMk μG ρ hN2 hρcont hN β hpos b)))
  ∧ (∀ a b : ↥(sliceObsSubmodule (N := N) μG ρ β),
      inner ℂ (sliceMk μG ρ hN2 hρcont hN β hpos a)
          (sliceMk μG ρ hN2 hρcont hN β hpos b)
        = osForm μG ρ β (sliceObs a.1) (sliceObs b.1))
  ∧ (∀ a : ↥(sliceObsSubmodule (N := N) μG ρ β),
      ‖sliceMk μG ρ hN2 hρcont hN β hpos a‖ ^ 2
        = (inner ℂ (sliceState μG ρ β a.1 a.2)
            (sliceWeldMap μG ρ hN2 hρcont hN β hpos
              (sliceMk μG ρ hN2 hρcont hN β hpos a))).re)
  ∧ sliceWeldMap μG ρ hN2 hρcont hN β hpos
        (sliceOmega μG ρ hN2 hρcont hN β hpos hd)
      = osVacuum μG ρ hρcont hd β
  ∧ (∀ x : sliceQuotient μG ρ hN2 hρcont hN β hpos,
      sliceEnergyForm μG ρ hN2 hρcont hN β hpos 1 x
        = ‖x‖ ^ 2 - ‖sliceWeldMap μG ρ hN2 hρcont hN
            β hpos x‖ ^ 2)
  ∧ (∀ x : sliceQuotient μG ρ hN2 hρcont hN β hpos,
      ENNReal.ofReal (‖x‖ ^ 2
          - ‖sliceWeldMap μG ρ hN2 hρcont hN β hpos x‖ ^ 2)
        ≤ sliceHamForm μG ρ hN2 hρcont hN β hpos x)
  ∧ (∀ x : sliceQuotient μG ρ hN2 hρcont hN β hpos,
      sliceWeldCLM μG ρ hN2 hρcont hN β hpos x
        = sliceWeldMap μG ρ hN2 hρcont hN β hpos x)

/-- **S2-5 headline (conditional, general `(G, ρ)`):** the
weld package holds between the S2-2 engine space and the
landed slice picture at every real `β`, under the engine's
one hypothesis `SliceHPosOne`. Form-level (K-S2-5): the
weld is the descended stepped state — intertwining,
contractive, an isometry for the `T̂`-twisted form — not a
unitary onto the slice states' `L²` closure. -/
theorem sliceWeld_package (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β) (hd : 0 < d) :
    sliceWeldPackage μG ρ hN2 hρcont hN β hpos hd :=
  ⟨sliceWeldMap_mk μG ρ hN2 hρcont hN β hpos,
    sliceWeldMap_norm_le μG ρ hN2 hρcont hN β hpos,
    sliceWeldMap_sliceHat μG ρ hN2 hρcont hN β hpos,
    sliceWeldMap_inner μG ρ hN2 hρcont hN β hpos,
    sliceQuotient_inner_eq_state_weld μG ρ hN2 hρcont hN
      β hpos,
    sliceQuotient_inner_eq_osForm μG ρ hN2 hρcont hN β hpos
      hd,
    sliceQuotient_norm_sq_eq_state_weld μG ρ hN2 hρcont
      hN β hpos,
    sliceWeldMap_sliceOmega μG ρ hN2 hρcont hN β hpos hd,
    sliceEnergyForm_one_eq_weldNorm μG ρ hN2 hρcont hN
      β hpos,
    sliceEnergyForm_one_le_hamForm_of_weld μG ρ hN2
      hρcont hN β hpos,
    sliceWeldCLM_apply μG ρ hN2 hρcont hN β hpos⟩

end SliceWeld

end ThetLogos
