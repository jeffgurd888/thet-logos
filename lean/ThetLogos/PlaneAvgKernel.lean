import ThetLogos.LatticePositivity
import ThetLogos.LatticeBoundaryOp

/-!
# ThetLogos.PlaneAvgKernel — the plane-averaged kernel of `osForm`

**A new entry under the relabeling rule.** This module is not a
continuation of Option 1 and does not touch the gate-kill modules.
Option 1's kernel `𝒦̃` held the plane-link variables fixed as shared
parameters of a two-sided kernel, and died at the gate (not
symmetric, indefinite). The kernel `osForm` actually pairs through
is different: in its kernel form (`osForm_eq_kernel`), the
plane-link variables — the reflection-fixed stratum — are
*integrated out* by the Gibbs/product-Haar integration. The
**plane-averaged kernel** `K̄_β` built here is that effective
two-sided kernel: the marginal of the Boltzmann weight over the
plane coordinates of both halves. It is a third object, distinct
from `𝒦̃` (plane held fixed) and from the frozen `𝒦̃₀` (plane
frozen at identity).

What stands in this module (all finite-lattice, fixed volume,
per-instance):

- the definition of `K̄_β` at general `(G, ρ)`, even `N`, real `β`;
- the **reduction identity**: for an observable supported on the
  strict half with factor `f` (under the same measurability and
  boundedness side conditions the corpus's Gram criterion
  consumes), `osForm β F F = Z⁻¹ · ⟨f, K̄_β f⟩` over the
  strict-half product Haar — `K̄` is `osForm`'s effective kernel;
- the **factorization** of `K̄` as the two half-action folds times
  the crossing-action marginal (the folded seam kernel, averaged);
- **symmetry** `K̄ z z' = K̄ z' z` and **conjugate symmetry**
  `conj (K̄ z z') = K̄ z' z`;
- the **β = 0 anchor** `K̄_0 ≡ 1`.

What does NOT stand: positivity (PSD) of `K̄` at any `β > 0` seat.
That is the (H-PF)-strength question, separately priced and
deliberately fenced out of this module; no statement here asserts
or implies it. Stage 1b-B at general `(G, ρ)` remains OPEN.

NO CLAIM: this module closes **0** parts of the Clay Yang–Mills
statement, and 0 parts of any other official statement.

This module is NOT in the root import list of the library (the
corpus pattern for recent exhibits); it is verified by a targeted
build.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

section Stratum

variable {G : Type*} [Group G] {N : ℕ} [NeZero N]

/-- The plane stratum inside the closed half: the links that are
both reflection-fixed and based in the closed half. The closed
half splits as `posLinks ⊔ planeHalfLinks`. -/
def planeHalfLinks : Finset (Link (Fin 4 → ZMod N)) :=
  planeLinks ∩ halfLinks

theorem mem_planeHalfLinks {ℓ : Link (Fin 4 → ZMod N)} :
    ℓ ∈ planeHalfLinks ↔ reflLink ℓ = ℓ ∧ (ℓ.1 0).val < N / 2 := by
  rw [planeHalfLinks, Finset.mem_inter, mem_planeLinks, mem_halfLinks]

/-- The plane stratum inside the negative half. -/
def planeNegLinks : Finset (Link (Fin 4 → ZMod N)) :=
  planeLinks ∩ negLinks

theorem mem_planeNegLinks {ℓ : Link (Fin 4 → ZMod N)} :
    ℓ ∈ planeNegLinks ↔ reflLink ℓ = ℓ ∧ N / 2 ≤ (ℓ.1 0).val := by
  rw [planeNegLinks, Finset.mem_inter, mem_planeLinks, mem_negLinks]

/-- A closed-half link that is not in the strict half is a plane
link of the closed half (the splitting dichotomy). -/
theorem halfLinks_mem_planeHalf_of_not_pos {ℓ : Link (Fin 4 → ZMod N)}
    (hℓ : ℓ ∈ halfLinks) (h : ℓ ∉ posLinks) : ℓ ∈ planeHalfLinks := by
  rw [posLinks, Finset.mem_sdiff] at h
  rw [mem_planeHalfLinks]
  push_neg at h
  exact ⟨mem_planeLinks.mp (h hℓ), mem_halfLinks.mp hℓ⟩

/-- A negative-half link that is a plane link lies in the negative
plane stratum. -/
theorem negLinks_mem_planeNeg_of_plane {ℓ : Link (Fin 4 → ZMod N)}
    (hℓ : ℓ ∈ negLinks) (h : ℓ ∈ planeLinks) : ℓ ∈ planeNegLinks :=
  Finset.mem_inter.mpr ⟨h, hℓ⟩

end Stratum

section Assembly

variable {G : Type*} [Group G] {N : ℕ} [NeZero N]

/-- Assemble a closed-half configuration from its strict-half part
`z` and its plane part `a`. -/
def joinHalf (z : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G) :
    ↥(halfLinks (N := N)) → G :=
  fun ℓ => if h : ℓ.1 ∈ posLinks
    then z ⟨ℓ.1, h⟩
    else a ⟨ℓ.1, halfLinks_mem_planeHalf_of_not_pos ℓ.2 h⟩

theorem planeHalfLinks_subset_halfLinks :
    planeHalfLinks (N := N) ⊆ halfLinks :=
  Finset.inter_subset_right

/-- The restriction of a closed-half configuration to its plane
part. -/
def restrictPlaneHalf (y : ↥(halfLinks (N := N)) → G) :
    ↥(planeHalfLinks (N := N)) → G :=
  fun ℓ => y ⟨ℓ.1, planeHalfLinks_subset_halfLinks ℓ.2⟩

/-- Assemble a negative-half configuration from a strict-half
configuration `z'` (read through the mirror) and a plane part
`a'`. The non-plane coordinates are placed so that
`mirrorP hN (joinNeg hN z' a') = z'` (see `mirrorP_joinNeg`). -/
def joinNeg (hN : Even N) (z' : ↥(posLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) :
    ↥(negLinks (N := N)) → G :=
  fun m => if h : m.1 ∈ planeLinks
    then a' ⟨m.1, negLinks_mem_planeNeg_of_plane m.2 h⟩
    else if (reflLink m.1).2 = 0
      then (z' ⟨reflLink m.1, reflLink_mem_posLinks hN m.2 h⟩)⁻¹
      else z' ⟨reflLink m.1, reflLink_mem_posLinks hN m.2 h⟩

theorem planeNegLinks_subset_negLinks :
    planeNegLinks (N := N) ⊆ negLinks :=
  Finset.inter_subset_right

/-- The restriction of a negative-half configuration to its plane
part. -/
def restrictPlaneNeg (w : ↥(negLinks (N := N)) → G) :
    ↥(planeNegLinks (N := N)) → G :=
  fun ℓ => w ⟨ℓ.1, planeNegLinks_subset_negLinks ℓ.2⟩

/-- The direction of a reflected link is the link's own direction. -/
theorem reflLink_snd (ℓ : Link (Fin 4 → ZMod N)) :
    (reflLink ℓ).2 = ℓ.2 := by
  obtain ⟨x, μ⟩ := ℓ
  by_cases h : μ = 0
  · subst h; rw [reflLink_zero]
  · rw [reflLink_of_ne h]

theorem restrictPos_joinHalf (z : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G) :
    restrictPos (joinHalf z a) = z := by
  funext ℓ
  show joinHalf z a ⟨ℓ.1, posLinks_subset_halfLinks ℓ.2⟩ = z ℓ
  rw [joinHalf, dif_pos ℓ.2]

theorem restrictPlaneHalf_joinHalf (z : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G) :
    restrictPlaneHalf (joinHalf z a) = a := by
  funext ℓ
  show joinHalf z a ⟨ℓ.1, planeHalfLinks_subset_halfLinks ℓ.2⟩ = a ℓ
  have hnot : ℓ.1 ∉ posLinks := by
    intro hpos
    exact (mem_posLinks.mp hpos).2 (mem_planeHalfLinks.mp ℓ.2).1
  rw [joinHalf, dif_neg hnot]

theorem joinHalf_restrict (y : ↥(halfLinks (N := N)) → G) :
    joinHalf (restrictPos y) (restrictPlaneHalf y) = y := by
  funext ℓ
  by_cases h : ℓ.1 ∈ posLinks
  · show joinHalf (restrictPos y) (restrictPlaneHalf y) ℓ = y ℓ
    rw [joinHalf, dif_pos h]
    rfl
  · show joinHalf (restrictPos y) (restrictPlaneHalf y) ℓ = y ℓ
    rw [joinHalf, dif_neg h]
    rfl

/-- `joinNeg` at a plane coordinate reads the plane part. -/
theorem joinNeg_apply_plane (hN : Even N) (z' : ↥(posLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) {m : ↥(negLinks (N := N))}
    (hm : m.1 ∈ planeLinks) :
    joinNeg hN z' a' m
      = a' ⟨m.1, negLinks_mem_planeNeg_of_plane m.2 hm⟩ := by
  rw [joinNeg, dif_pos hm]

/-- `joinNeg` at a non-plane coordinate reads the mirrored
strict-half part, with inversion on time links — the exact mirror
of `mirrorP`'s formula. -/
theorem joinNeg_apply_not_plane (hN : Even N)
    (z' : ↥(posLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) {m : ↥(negLinks (N := N))}
    (hm : m.1 ∉ planeLinks) :
    joinNeg hN z' a' m
      = if (reflLink m.1).2 = 0
        then (z' ⟨reflLink m.1, reflLink_mem_posLinks hN m.2 hm⟩)⁻¹
        else z' ⟨reflLink m.1, reflLink_mem_posLinks hN m.2 hm⟩ := by
  rw [joinNeg, dif_neg hm]

/-- `mirrorP` at a time-direction strict-half coordinate. -/
theorem mirrorP_apply_of_dir_zero (hN : Even N)
    (w : ↥(negLinks (N := N)) → G) {ℓ : ↥(posLinks (N := N))}
    (h : ℓ.1.2 = 0) :
    mirrorP hN w ℓ
      = (w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩)⁻¹ :=
  if_pos h

/-- `mirrorP` at a spatial-direction strict-half coordinate. -/
theorem mirrorP_apply_of_dir_ne (hN : Even N)
    (w : ↥(negLinks (N := N)) → G) {ℓ : ↥(posLinks (N := N))}
    (h : ℓ.1.2 ≠ 0) :
    mirrorP hN w ℓ
      = w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩ :=
  if_neg h

theorem mirrorP_joinNeg (hN : Even N) (z' : ↥(posLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) :
    mirrorP hN (joinNeg hN z' a') = z' := by
  funext ℓ
  by_cases h : ℓ.1.2 = 0
  · rw [mirrorP_apply_of_dir_zero hN _ h,
      joinNeg_apply_not_plane hN z' a' (reflLink_not_mem_planeLinks ℓ.2)]
    split_ifs with hc
    · rw [inv_inv]
      congr 1
      exact Subtype.ext (reflLink_involutive ℓ.1)
    · exfalso
      apply hc
      show (reflLink (reflLink ℓ.1)).2 = 0
      rw [reflLink_involutive ℓ.1]
      exact h
  · rw [mirrorP_apply_of_dir_ne hN _ h,
      joinNeg_apply_not_plane hN z' a' (reflLink_not_mem_planeLinks ℓ.2)]
    split_ifs with hc
    · exfalso
      apply h
      have hc' : (reflLink (reflLink ℓ.1)).2 = 0 := hc
      rw [reflLink_involutive ℓ.1] at hc'
      exact hc'
    · congr 1
      exact Subtype.ext (reflLink_involutive ℓ.1)

theorem restrictPlaneNeg_joinNeg (hN : Even N)
    (z' : ↥(posLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) :
    restrictPlaneNeg (joinNeg hN z' a') = a' := by
  funext ℓ
  show joinNeg hN z' a' ⟨ℓ.1, planeNegLinks_subset_negLinks ℓ.2⟩ = a' ℓ
  rw [joinNeg_apply_plane hN z' a'
    (mem_planeLinks.mpr (mem_planeNegLinks.mp ℓ.2).1)]

theorem joinNeg_restrict (hN : Even N) (w : ↥(negLinks (N := N)) → G) :
    joinNeg hN (mirrorP hN w) (restrictPlaneNeg w) = w := by
  funext m
  by_cases hpl : m.1 ∈ planeLinks
  · rw [joinNeg_apply_plane hN _ _ hpl]
    rfl
  · rw [joinNeg_apply_not_plane hN _ _ hpl]
    split_ifs with hc
    · rw [mirrorP_apply_of_dir_zero hN w hc, inv_inv]
      congr 1
      exact Subtype.ext (reflLink_involutive m.1)
    · rw [mirrorP_apply_of_dir_ne hN w hc]
      congr 1
      exact Subtype.ext (reflLink_involutive m.1)

end Assembly

section Transports

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  {N : ℕ} [NeZero N]

theorem measurable_restrictPos' :
    Measurable (restrictPos (G := G) (N := N)) := by
  rw [measurable_pi_iff]
  intro ℓ
  exact measurable_pi_apply
    (⟨ℓ.1, posLinks_subset_halfLinks ℓ.2⟩ : ↥(halfLinks (N := N)))

theorem measurable_restrictPlaneHalf :
    Measurable (restrictPlaneHalf (G := G) (N := N)) := by
  rw [measurable_pi_iff]
  intro ℓ
  show Measurable fun y : ↥(halfLinks (N := N)) → G =>
    y ⟨ℓ.1, planeHalfLinks_subset_halfLinks ℓ.2⟩
  exact measurable_pi_apply _

theorem measurable_restrictPlaneNeg :
    Measurable (restrictPlaneNeg (G := G) (N := N)) := by
  rw [measurable_pi_iff]
  intro ℓ
  show Measurable fun w : ↥(negLinks (N := N)) → G =>
    w ⟨ℓ.1, planeNegLinks_subset_negLinks ℓ.2⟩
  exact measurable_pi_apply _

theorem measurable_joinHalf :
    Measurable (fun q : (↥(posLinks (N := N)) → G)
      × (↥(planeHalfLinks (N := N)) → G) => joinHalf q.1 q.2) := by
  rw [measurable_pi_iff]
  intro ℓ
  by_cases h : ℓ.1 ∈ posLinks
  · have hfun : (fun q : (↥(posLinks (N := N)) → G)
          × (↥(planeHalfLinks (N := N)) → G) => joinHalf q.1 q.2 ℓ)
        = fun q => q.1 ⟨ℓ.1, h⟩ :=
      funext fun q => dif_pos h
    rw [hfun]
    exact (measurable_pi_apply (⟨ℓ.1, h⟩ : ↥(posLinks (N := N)))).comp measurable_fst
  · have hfun : (fun q : (↥(posLinks (N := N)) → G)
          × (↥(planeHalfLinks (N := N)) → G) => joinHalf q.1 q.2 ℓ)
        = fun q => q.2 ⟨ℓ.1, halfLinks_mem_planeHalf_of_not_pos ℓ.2 h⟩ :=
      funext fun q => dif_neg h
    rw [hfun]
    exact (measurable_pi_apply
      (⟨ℓ.1, halfLinks_mem_planeHalf_of_not_pos ℓ.2 h⟩ :
        ↥(planeHalfLinks (N := N)))).comp measurable_snd

theorem measurable_joinNeg (hN : Even N) :
    Measurable (fun q : (↥(posLinks (N := N)) → G)
      × (↥(planeNegLinks (N := N)) → G) => joinNeg hN q.1 q.2) := by
  rw [measurable_pi_iff]
  intro m
  by_cases hpl : m.1 ∈ planeLinks
  · have hfun : (fun q : (↥(posLinks (N := N)) → G)
          × (↥(planeNegLinks (N := N)) → G) => joinNeg hN q.1 q.2 m)
        = fun q => q.2 ⟨m.1, negLinks_mem_planeNeg_of_plane m.2 hpl⟩ :=
      funext fun q => joinNeg_apply_plane hN q.1 q.2 hpl
    rw [hfun]
    exact (measurable_pi_apply
      (⟨m.1, negLinks_mem_planeNeg_of_plane m.2 hpl⟩ :
        ↥(planeNegLinks (N := N)))).comp measurable_snd
  · by_cases h0 : (reflLink m.1).2 = 0
    · have hfun : (fun q : (↥(posLinks (N := N)) → G)
            × (↥(planeNegLinks (N := N)) → G) => joinNeg hN q.1 q.2 m)
          = fun q => (q.1 ⟨reflLink m.1,
              reflLink_mem_posLinks hN m.2 hpl⟩)⁻¹ :=
        funext fun q => (joinNeg_apply_not_plane hN q.1 q.2 hpl).trans
          (if_pos h0)
      rw [hfun]
      exact ((measurable_pi_apply
        (⟨reflLink m.1, reflLink_mem_posLinks hN m.2 hpl⟩ :
          ↥(posLinks (N := N)))).comp measurable_fst).inv
    · have hfun : (fun q : (↥(posLinks (N := N)) → G)
            × (↥(planeNegLinks (N := N)) → G) => joinNeg hN q.1 q.2 m)
          = fun q => q.1 ⟨reflLink m.1,
              reflLink_mem_posLinks hN m.2 hpl⟩ :=
        funext fun q => (joinNeg_apply_not_plane hN q.1 q.2 hpl).trans
          (if_neg h0)
      rw [hfun]
      exact (measurable_pi_apply
        (⟨reflLink m.1, reflLink_mem_posLinks hN m.2 hpl⟩ :
          ↥(posLinks (N := N)))).comp measurable_fst

/-- The closed half's coordinate split as a measurable equiv:
restriction to the strict half and to the plane stratum. -/
def halfPlaneEquiv : (↥(halfLinks (N := N)) → G)
    ≃ᵐ (↥(posLinks (N := N)) → G) × (↥(planeHalfLinks (N := N)) → G) :=
  { toFun := fun y => (restrictPos y, restrictPlaneHalf y)
    invFun := fun q => joinHalf q.1 q.2
    left_inv := fun y => joinHalf_restrict y
    right_inv := fun q => Prod.ext (restrictPos_joinHalf q.1 q.2)
      (restrictPlaneHalf_joinHalf q.1 q.2)
    measurable_toFun := Measurable.prodMk
      measurable_restrictPos' measurable_restrictPlaneHalf
    measurable_invFun := measurable_joinHalf }

/-- The negative half's coordinate split as a measurable equiv:
the mirror and the plane stratum. -/
def negPlaneEquiv (hN : Even N) : (↥(negLinks (N := N)) → G)
    ≃ᵐ (↥(posLinks (N := N)) → G) × (↥(planeNegLinks (N := N)) → G) :=
  { toFun := fun w => (mirrorP hN w, restrictPlaneNeg w)
    invFun := fun q => joinNeg hN q.1 q.2
    left_inv := fun w => joinNeg_restrict hN w
    right_inv := fun q => Prod.ext (mirrorP_joinNeg hN q.1 q.2)
      (restrictPlaneNeg_joinNeg hN q.1 q.2)
    measurable_toFun := Measurable.prodMk
      (measurePreserving_mirrorP μG hN).measurable measurable_restrictPlaneNeg
    measurable_invFun := measurable_joinNeg hN }

/-- The strict-half part of the closed half, as a finset of the
closed half's index type. -/
def halfSplitIdx : Finset ↥(halfLinks (N := N)) :=
  Finset.univ.filter (fun ℓ => ℓ.1 ∈ posLinks)

def halfSplitEquivPos : ↥(halfSplitIdx (N := N)) ≃ ↥(posLinks (N := N)) :=
  { toFun := fun ℓ => ⟨ℓ.1.1, (Finset.mem_filter.mp ℓ.2).2⟩
    invFun := fun m => ⟨⟨m.1, posLinks_subset_halfLinks m.2⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, m.2⟩⟩
    left_inv := fun ℓ => Subtype.ext (Subtype.ext rfl)
    right_inv := fun m => Subtype.ext rfl }

def halfSplitEquivPlane :
    ↥(halfSplitIdx (N := N))ᶜ ≃ ↥(planeHalfLinks (N := N)) :=
  { toFun := fun m => ⟨m.1.1, halfLinks_mem_planeHalf_of_not_pos m.1.2 (by
      have h2 : m.1 ∉ halfSplitIdx (N := N) := Finset.mem_compl.mp m.2
      exact fun h => h2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))⟩
    invFun := fun a => ⟨⟨a.1, planeHalfLinks_subset_halfLinks a.2⟩, by
      rw [Finset.mem_compl]
      intro h
      have h2 := Finset.mem_filter.mp h
      exact (mem_posLinks.mp h2.2).2 (mem_planeHalfLinks.mp a.2).1⟩
    left_inv := fun m => Subtype.ext (Subtype.ext rfl)
    right_inv := fun a => Subtype.ext rfl }

theorem measurePreserving_halfPlaneEquiv :
    MeasurePreserving halfPlaneEquiv
      (Measure.pi fun _ : ↥(halfLinks (N := N)) => μG)
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG)) := by
  have hchain : MeasurePreserving
      (((MeasurableEquiv.piCongrLeft (fun _ : ↥(posLinks (N := N)) => G)
          halfSplitEquivPos).prodCongr
        (MeasurableEquiv.piCongrLeft (fun _ : ↥(planeHalfLinks (N := N)) => G)
          halfSplitEquivPlane)) ∘ (splitEquiv (halfSplitIdx (N := N))))
      (Measure.pi fun _ : ↥(halfLinks (N := N)) => μG)
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG)) :=
    ((measurePreserving_piCongrLeft (fun _ : ↥(posLinks (N := N)) => μG)
        halfSplitEquivPos).prod
      (measurePreserving_piCongrLeft (fun _ : ↥(planeHalfLinks (N := N)) => μG)
        halfSplitEquivPlane)).comp
      (measurePreserving_splitEquiv μG (halfSplitIdx (N := N)))
  have hfun : (((MeasurableEquiv.piCongrLeft (fun _ : ↥(posLinks (N := N)) => G)
        halfSplitEquivPos).prodCongr
      (MeasurableEquiv.piCongrLeft (fun _ : ↥(planeHalfLinks (N := N)) => G)
        halfSplitEquivPlane)) ∘ (splitEquiv (halfSplitIdx (N := N))))
      = halfPlaneEquiv := by
    funext y
    apply Prod.ext
    · funext m
      have h2 : (MeasurableEquiv.piCongrLeft
            (fun _ : ↥(posLinks (N := N)) => G) halfSplitEquivPos)
          ((splitEquiv (halfSplitIdx (N := N))) y).1
          (halfSplitEquivPos (halfSplitEquivPos.symm m))
          = ((splitEquiv (halfSplitIdx (N := N))) y).1
            (halfSplitEquivPos.symm m) :=
        MeasurableEquiv.piCongrLeft_apply_apply
          (β := fun _ : ↥(posLinks (N := N)) => G) halfSplitEquivPos
          ((splitEquiv (halfSplitIdx (N := N))) y).1 (halfSplitEquivPos.symm m)
      rw [halfSplitEquivPos.apply_symm_apply] at h2
      show (MeasurableEquiv.piCongrLeft
          (fun _ : ↥(posLinks (N := N)) => G) halfSplitEquivPos)
        ((splitEquiv (halfSplitIdx (N := N))) y).1 m = restrictPos y m
      rw [h2, splitEquiv_fst]
      rfl
    · funext a
      have h2 : (MeasurableEquiv.piCongrLeft
            (fun _ : ↥(planeHalfLinks (N := N)) => G) halfSplitEquivPlane)
          ((splitEquiv (halfSplitIdx (N := N))) y).2
          (halfSplitEquivPlane (halfSplitEquivPlane.symm a))
          = ((splitEquiv (halfSplitIdx (N := N))) y).2
            (halfSplitEquivPlane.symm a) :=
        MeasurableEquiv.piCongrLeft_apply_apply
          (β := fun _ : ↥(planeHalfLinks (N := N)) => G) halfSplitEquivPlane
          ((splitEquiv (halfSplitIdx (N := N))) y).2 (halfSplitEquivPlane.symm a)
      rw [halfSplitEquivPlane.apply_symm_apply] at h2
      show (MeasurableEquiv.piCongrLeft
          (fun _ : ↥(planeHalfLinks (N := N)) => G) halfSplitEquivPlane)
        ((splitEquiv (halfSplitIdx (N := N))) y).2 a = restrictPlaneHalf y a
      rw [h2, splitEquiv_snd]
      rfl
  rwa [hfun] at hchain

/-- **Split integral, closed half**: integrating over the closed
half is integrating over the strict half and the plane stratum
jointly. Unconditional (a measure-preserving transport). -/
theorem integral_half_split (Ψ : (↥(halfLinks (N := N)) → G) → ℂ) :
    ∫ y, Ψ y ∂(Measure.pi fun _ : ↥(halfLinks (N := N)) => μG)
      = ∫ q : (↥(posLinks (N := N)) → G)
          × (↥(planeHalfLinks (N := N)) → G), Ψ (joinHalf q.1 q.2)
          ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
            (Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG)) := by
  have h := (measurePreserving_halfPlaneEquiv μG).symm.integral_comp
    (MeasurableEquiv.measurableEmbedding halfPlaneEquiv.symm) Ψ
  rw [← h]
  apply integral_congr_ae
  exact ae_of_all _ fun q => congrArg Ψ rfl

/-- The per-coordinate inversion map on strict-half
configurations (inversion on time-direction coordinates only) —
the second factor of the mirror transport. -/
def posInvMap : (↥(posLinks (N := N)) → G) → (↥(posLinks (N := N)) → G) :=
  fun z ℓ => if ℓ.1.2 = 0 then (z ℓ)⁻¹ else z ℓ

theorem posInvMap_involutive :
    Function.Involutive (posInvMap (G := G) (N := N)) := by
  intro z
  funext ℓ
  by_cases h : ℓ.1.2 = 0
  · rw [show posInvMap (posInvMap z) ℓ = ((posInvMap z) ℓ)⁻¹ from if_pos h,
      show posInvMap z ℓ = (z ℓ)⁻¹ from if_pos h, inv_inv]
  · rw [show posInvMap (posInvMap z) ℓ = posInvMap z ℓ from if_neg h,
      show posInvMap z ℓ = z ℓ from if_neg h]

theorem measurable_posInvMap :
    Measurable (posInvMap (G := G) (N := N)) := by
  rw [measurable_pi_iff]
  intro ℓ
  by_cases h : ℓ.1.2 = 0
  · have hfun : (fun z : ↥(posLinks (N := N)) → G => posInvMap z ℓ)
        = fun z => (z ℓ)⁻¹ := funext fun z => if_pos h
    rw [hfun]
    exact (measurable_pi_apply ℓ).inv
  · have hfun : (fun z : ↥(posLinks (N := N)) → G => posInvMap z ℓ)
        = fun z => z ℓ := funext fun z => if_neg h
    rw [hfun]
    exact measurable_pi_apply ℓ

def posInvEquiv : (↥(posLinks (N := N)) → G) ≃ᵐ (↥(posLinks (N := N)) → G) :=
  { toEquiv := ⟨posInvMap, posInvMap, posInvMap_involutive,
      posInvMap_involutive⟩
    measurable_toFun := measurable_posInvMap
    measurable_invFun := measurable_posInvMap }

theorem measurePreserving_posInvEquiv :
    MeasurePreserving posInvEquiv
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG) := by
  refine measurePreserving_pi
    (f := fun (ℓ : ↥(posLinks (N := N))) (g : G) =>
      if ℓ.1.2 = 0 then g⁻¹ else g)
    (fun _ : ↥(posLinks (N := N)) => μG)
    (fun _ : ↥(posLinks (N := N)) => μG) fun ℓ => ?_
  show MeasurePreserving (fun g : G => if ℓ.1.2 = 0 then g⁻¹ else g) μG μG
  by_cases hℓ : ℓ.1.2 = 0
  · rw [show (fun g : G => if ℓ.1.2 = 0 then g⁻¹ else g) = Inv.inv from
      funext fun g => if_pos hℓ]
    exact Measure.measurePreserving_inv μG
  · rw [show (fun g : G => if ℓ.1.2 = 0 then g⁻¹ else g) = id from
      funext fun g => if_neg hℓ]
    exact MeasurePreserving.id μG

/-- The non-plane part of the negative half, as a finset of its
index type. -/
def negSplitIdx : Finset ↥(negLinks (N := N)) :=
  Finset.univ.filter (fun ℓ => ℓ.1 ∉ planeLinks)

def negSplitEquivPos (hN : Even N) :
    ↥(posLinks (N := N)) ≃ ↥(negSplitIdx (N := N)) :=
  { toFun := fun ℓ => ⟨⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        reflLink_not_mem_planeLinks ℓ.2⟩⟩
    invFun := fun m => ⟨reflLink m.1.1, reflLink_mem_posLinks hN m.1.2
      (Finset.mem_filter.mp m.2).2⟩
    left_inv := fun ℓ => Subtype.ext (reflLink_involutive ℓ.1)
    right_inv := fun m => Subtype.ext (Subtype.ext
      (reflLink_involutive m.1.1)) }

def negSplitEquivPlane :
    ↥(negSplitIdx (N := N))ᶜ ≃ ↥(planeNegLinks (N := N)) :=
  { toFun := fun m => ⟨m.1.1, negLinks_mem_planeNeg_of_plane m.1.2 (by
      have h2 : m.1 ∉ negSplitIdx (N := N) := Finset.mem_compl.mp m.2
      by_contra hcon
      exact h2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩))⟩
    invFun := fun a => ⟨⟨a.1, planeNegLinks_subset_negLinks a.2⟩, by
      rw [Finset.mem_compl]
      intro h
      have h2 := Finset.mem_filter.mp h
      exact absurd (mem_planeLinks.mpr (mem_planeNegLinks.mp a.2).1) h2.2⟩
    left_inv := fun m => Subtype.ext (Subtype.ext rfl)
    right_inv := fun a => Subtype.ext rfl }

theorem measurePreserving_negPlaneEquiv (hN : Even N) :
    MeasurePreserving (negPlaneEquiv μG hN)
      (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)) := by
  have hchain : MeasurePreserving
      ((((MeasurableEquiv.piCongrLeft (fun _ : ↥(posLinks (N := N)) => G)
            (negSplitEquivPos hN).symm).trans posInvEquiv).prodCongr
        (MeasurableEquiv.piCongrLeft (fun _ : ↥(planeNegLinks (N := N)) => G)
          negSplitEquivPlane)) ∘ (splitEquiv (negSplitIdx (N := N))))
      (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)) :=
    ((measurePreserving_posInvEquiv μG).comp
        (measurePreserving_piCongrLeft (fun _ : ↥(posLinks (N := N)) => μG)
          (negSplitEquivPos hN).symm) |>.prod
      (measurePreserving_piCongrLeft (fun _ : ↥(planeNegLinks (N := N)) => μG)
        negSplitEquivPlane)).comp
      (measurePreserving_splitEquiv μG (negSplitIdx (N := N)))
  have hfun : ((((MeasurableEquiv.piCongrLeft
          (fun _ : ↥(posLinks (N := N)) => G)
          (negSplitEquivPos hN).symm).trans posInvEquiv).prodCongr
        (MeasurableEquiv.piCongrLeft (fun _ : ↥(planeNegLinks (N := N)) => G)
          negSplitEquivPlane)) ∘ (splitEquiv (negSplitIdx (N := N))))
      = negPlaneEquiv μG hN := by
    funext w
    apply Prod.ext
    · -- The first component is the mirror, via the corpus's
      -- factorization (LatticePositivity's `integral_mirrorP`).
      funext ℓ
      have hcong : (MeasurableEquiv.piCongrLeft
            (fun _ : ↥(posLinks (N := N)) => G) (negSplitEquivPos hN).symm)
          ((splitEquiv (negSplitIdx (N := N))) w).1
          = fun ℓ : ↥(posLinks (N := N)) => w (negSplitEquivPos hN ℓ).1 := by
        funext ℓ
        have h2 : (MeasurableEquiv.piCongrLeft
              (fun _ : ↥(posLinks (N := N)) => G) (negSplitEquivPos hN).symm)
            ((splitEquiv (negSplitIdx (N := N))) w).1
            ((negSplitEquivPos hN).symm (negSplitEquivPos hN ℓ))
            = ((splitEquiv (negSplitIdx (N := N))) w).1
              (negSplitEquivPos hN ℓ) :=
          MeasurableEquiv.piCongrLeft_apply_apply
            (β := fun _ : ↥(posLinks (N := N)) => G) (negSplitEquivPos hN).symm
            ((splitEquiv (negSplitIdx (N := N))) w).1 (negSplitEquivPos hN ℓ)
        rw [Equiv.symm_apply_apply] at h2
        rw [h2, splitEquiv_fst]
      show posInvMap ((MeasurableEquiv.piCongrLeft
          (fun _ : ↥(posLinks (N := N)) => G) (negSplitEquivPos hN).symm)
        ((splitEquiv (negSplitIdx (N := N))) w).1) ℓ = mirrorP hN w ℓ
      rw [hcong]
      by_cases h : ℓ.1.2 = 0
      · rw [show posInvMap
              (fun ℓ : ↥(posLinks (N := N)) => w (negSplitEquivPos hN ℓ).1) ℓ
            = (w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩)⁻¹ from
            if_pos h,
          show mirrorP hN w ℓ
            = (w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩)⁻¹ from
            if_pos h]
      · rw [show posInvMap
              (fun ℓ : ↥(posLinks (N := N)) => w (negSplitEquivPos hN ℓ).1) ℓ
            = w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩ from if_neg h,
          show mirrorP hN w ℓ
            = w ⟨reflLink ℓ.1, reflLink_mem_negLinks hN ℓ.2⟩ from if_neg h]
    · funext a
      have h2 : (MeasurableEquiv.piCongrLeft
            (fun _ : ↥(planeNegLinks (N := N)) => G) negSplitEquivPlane)
          ((splitEquiv (negSplitIdx (N := N))) w).2
          (negSplitEquivPlane (negSplitEquivPlane.symm a))
          = ((splitEquiv (negSplitIdx (N := N))) w).2
            (negSplitEquivPlane.symm a) :=
        MeasurableEquiv.piCongrLeft_apply_apply
          (β := fun _ : ↥(planeNegLinks (N := N)) => G) negSplitEquivPlane
          ((splitEquiv (negSplitIdx (N := N))) w).2 (negSplitEquivPlane.symm a)
      rw [negSplitEquivPlane.apply_symm_apply] at h2
      show (MeasurableEquiv.piCongrLeft
          (fun _ : ↥(planeNegLinks (N := N)) => G) negSplitEquivPlane)
        ((splitEquiv (negSplitIdx (N := N))) w).2 a = restrictPlaneNeg w a
      rw [h2, splitEquiv_snd]
      rfl
  rwa [hfun] at hchain

/-- **Split integral, negative half**: integrating over the
negative half is integrating over the strict half (through the
mirror) and the plane stratum jointly. Unconditional. -/
theorem integral_neg_split (hN : Even N)
    (Ψ : (↥(negLinks (N := N)) → G) → ℂ) :
    ∫ w, Ψ w ∂(Measure.pi fun _ : ↥(negLinks (N := N)) => μG)
      = ∫ q : (↥(posLinks (N := N)) → G)
          × (↥(planeNegLinks (N := N)) → G), Ψ (joinNeg hN q.1 q.2)
          ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
            (Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)) := by
  have h := (measurePreserving_negPlaneEquiv μG hN).symm.integral_comp
    (MeasurableEquiv.measurableEmbedding (negPlaneEquiv μG hN).symm) Ψ
  rw [← h]
  apply integral_congr_ae
  exact ae_of_all _ fun q => congrArg Ψ rfl

end Transports

section Kernel

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-- The full configuration assembled from strict-half data
`z`, mirrored strict data `z'`, and the plane strata `a`, `a'`
of the two halves. -/
noncomputable def planeAssemble (hN : Even N) (z z' : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) : Config (Fin 4 → ZMod N) G :=
  (splitEquiv (halfLinks (N := N))).symm (joinHalf z a, joinNeg hN z' a')

theorem measurable_planeAssemble (hN : Even N)
    (z z' : ↥(posLinks (N := N)) → G) :
    Measurable (fun p : (↥(planeHalfLinks (N := N)) → G)
        × (↥(planeNegLinks (N := N)) → G) =>
      planeAssemble hN z z' p.1 p.2) :=
  (splitEquiv (halfLinks (N := N))).symm.measurable.comp
    (Measurable.prodMk
      (measurable_joinHalf.comp
        (Measurable.prodMk measurable_const measurable_fst))
      ((measurable_joinNeg hN).comp
        (Measurable.prodMk measurable_const measurable_snd)))

/-- **The plane-averaged kernel** `K̄_β(z, z')`: `osForm`'s
effective two-sided kernel after the plane-link variables of
both halves are marginalized under the same product-Haar
integration `osForm` performs. A NEW entry: not the
fixed-plane kernel of the killed Option 1 line, and not a
frozen-section kernel. No positivity is asserted or implied. -/
noncomputable def planeAvgKernel (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) : ℂ :=
  ∫ a, ∫ a', (Real.exp (-(wilsonAction (torusShift N) ρ β
      (planeAssemble hN z z' a a'))) : ℂ)
    ∂(Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)
    ∂(Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG)

/-- The crossing marginal: the plane-stratum average of the
crossing (`S₀`) Gibbs factor alone. -/
noncomputable def planeCrossingMarginal (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) : ℂ :=
  ∫ a, ∫ a', (Real.exp (-(wilsonActionZero ρ β
      (planeAssemble hN z z' a a'))) : ℂ)
    ∂(Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)
    ∂(Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG)

/-- **Factorization**: the corpus's three-way action split,
read through the assembly, separates the two strict halves'
own actions from the crossing marginal. -/
theorem planeAvgKernel_factor (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) :
    planeAvgKernel μG ρ hN β z z'
      = (Real.exp (-(halfActionP ρ β z)) : ℂ)
        * (Real.exp (-(halfActionP ρ β z')) : ℂ)
        * planeCrossingMarginal μG ρ hN β z z' := by
  have hpt : ∀ (a : ↥(planeHalfLinks (N := N)) → G)
      (a' : ↥(planeNegLinks (N := N)) → G),
      (Real.exp (-(wilsonAction (torusShift N) ρ β
        (planeAssemble hN z z' a a'))) : ℂ)
        = (Real.exp (-(halfActionP ρ β z)) : ℂ)
          * (Real.exp (-(halfActionP ρ β z')) : ℂ)
          * (Real.exp (-(wilsonActionZero ρ β
            (planeAssemble hN z z' a a'))) : ℂ) := by
    intro a a'
    unfold planeAssemble
    rw [wilsonAction_split_half ρ hN β (joinHalf z a, joinNeg hN z' a'),
      restrictPos_joinHalf, mirrorP_joinNeg]
    have hsum : (-(halfActionP ρ β z + halfActionP ρ β z'
        + wilsonActionZero ρ β ((splitEquiv (halfLinks (N := N))).symm
          (joinHalf z a, joinNeg hN z' a'))))
      = (-(halfActionP ρ β z)) + (-(halfActionP ρ β z'))
        + (-(wilsonActionZero ρ β ((splitEquiv (halfLinks (N := N))).symm
          (joinHalf z a, joinNeg hN z' a')))) := by ring
    rw [hsum, Real.exp_add, Real.exp_add, Complex.ofReal_mul,
      Complex.ofReal_mul]
  unfold planeAvgKernel planeCrossingMarginal
  rw [integral_congr_ae (ae_of_all _ fun a =>
    integral_congr_ae (ae_of_all _ fun a' => hpt a a'))]
  simp only [integral_const_mul]

/-- **The β = 0 anchor**: at zero coupling the action vanishes
and the kernel is identically `1`. -/
theorem planeAvgKernel_zero (hN : Even N)
    (z z' : ↥(posLinks (N := N)) → G) :
    planeAvgKernel μG ρ hN 0 z z' = 1 := by
  unfold planeAvgKernel
  simp [wilsonAction]

/-- Per-coordinate inversion on the plane stratum of the closed
half, on time-direction coordinates only — the plane part of
the reflection substitution. -/
def planeInvHalf : (↥(planeHalfLinks (N := N)) → G)
    → (↥(planeHalfLinks (N := N)) → G) :=
  fun a m => if m.1.2 = 0 then (a m)⁻¹ else a m

/-- Per-coordinate inversion on the plane stratum of the
negative half. -/
def planeInvNeg : (↥(planeNegLinks (N := N)) → G)
    → (↥(planeNegLinks (N := N)) → G) :=
  fun a' m => if m.1.2 = 0 then (a' m)⁻¹ else a' m

theorem planeInvHalf_involutive :
    Function.Involutive (planeInvHalf (G := G) (N := N)) := by
  intro a
  funext m
  by_cases h : m.1.2 = 0
  · rw [show planeInvHalf (planeInvHalf a) m = ((planeInvHalf a) m)⁻¹
        from if_pos h,
      show planeInvHalf a m = (a m)⁻¹ from if_pos h, inv_inv]
  · rw [show planeInvHalf (planeInvHalf a) m = planeInvHalf a m
        from if_neg h,
      show planeInvHalf a m = a m from if_neg h]

theorem planeInvNeg_involutive :
    Function.Involutive (planeInvNeg (G := G) (N := N)) := by
  intro a'
  funext m
  by_cases h : m.1.2 = 0
  · rw [show planeInvNeg (planeInvNeg a') m = ((planeInvNeg a') m)⁻¹
        from if_pos h,
      show planeInvNeg a' m = (a' m)⁻¹ from if_pos h, inv_inv]
  · rw [show planeInvNeg (planeInvNeg a') m = planeInvNeg a' m
        from if_neg h,
      show planeInvNeg a' m = a' m from if_neg h]

theorem measurable_planeInvHalf :
    Measurable (planeInvHalf (G := G) (N := N)) := by
  rw [measurable_pi_iff]
  intro m
  by_cases h : m.1.2 = 0
  · have hfun : (fun a : ↥(planeHalfLinks (N := N)) → G =>
          planeInvHalf a m) = fun a => (a m)⁻¹ :=
      funext fun a => if_pos h
    rw [hfun]
    exact (measurable_pi_apply m).inv
  · have hfun : (fun a : ↥(planeHalfLinks (N := N)) → G =>
          planeInvHalf a m) = fun a => a m :=
      funext fun a => if_neg h
    rw [hfun]
    exact measurable_pi_apply m

theorem measurable_planeInvNeg :
    Measurable (planeInvNeg (G := G) (N := N)) := by
  rw [measurable_pi_iff]
  intro m
  by_cases h : m.1.2 = 0
  · have hfun : (fun a' : ↥(planeNegLinks (N := N)) → G =>
          planeInvNeg a' m) = fun a' => (a' m)⁻¹ :=
      funext fun a' => if_pos h
    rw [hfun]
    exact (measurable_pi_apply m).inv
  · have hfun : (fun a' : ↥(planeNegLinks (N := N)) → G =>
          planeInvNeg a' m) = fun a' => a' m :=
      funext fun a' => if_neg h
    rw [hfun]
    exact measurable_pi_apply m

def planeInvHalfEquiv : (↥(planeHalfLinks (N := N)) → G)
    ≃ᵐ (↥(planeHalfLinks (N := N)) → G) :=
  { toEquiv := ⟨planeInvHalf, planeInvHalf, planeInvHalf_involutive,
      planeInvHalf_involutive⟩
    measurable_toFun := measurable_planeInvHalf
    measurable_invFun := measurable_planeInvHalf }

def planeInvNegEquiv : (↥(planeNegLinks (N := N)) → G)
    ≃ᵐ (↥(planeNegLinks (N := N)) → G) :=
  { toEquiv := ⟨planeInvNeg, planeInvNeg, planeInvNeg_involutive,
      planeInvNeg_involutive⟩
    measurable_toFun := measurable_planeInvNeg
    measurable_invFun := measurable_planeInvNeg }

theorem measurePreserving_planeInvHalfEquiv :
    MeasurePreserving planeInvHalfEquiv
      (Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG)
      (Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG) := by
  refine measurePreserving_pi
    (f := fun (m : ↥(planeHalfLinks (N := N))) (g : G) =>
      if m.1.2 = 0 then g⁻¹ else g)
    (fun _ : ↥(planeHalfLinks (N := N)) => μG)
    (fun _ : ↥(planeHalfLinks (N := N)) => μG) fun m => ?_
  show MeasurePreserving (fun g : G => if m.1.2 = 0 then g⁻¹ else g) μG μG
  by_cases hm : m.1.2 = 0
  · rw [show (fun g : G => if m.1.2 = 0 then g⁻¹ else g) = Inv.inv from
      funext fun g => if_pos hm]
    exact Measure.measurePreserving_inv μG
  · rw [show (fun g : G => if m.1.2 = 0 then g⁻¹ else g) = id from
      funext fun g => if_neg hm]
    exact MeasurePreserving.id μG

theorem measurePreserving_planeInvNegEquiv :
    MeasurePreserving planeInvNegEquiv
      (Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)
      (Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG) := by
  refine measurePreserving_pi
    (f := fun (m : ↥(planeNegLinks (N := N))) (g : G) =>
      if m.1.2 = 0 then g⁻¹ else g)
    (fun _ : ↥(planeNegLinks (N := N)) => μG)
    (fun _ : ↥(planeNegLinks (N := N)) => μG) fun m => ?_
  show MeasurePreserving (fun g : G => if m.1.2 = 0 then g⁻¹ else g) μG μG
  by_cases hm : m.1.2 = 0
  · rw [show (fun g : G => if m.1.2 = 0 then g⁻¹ else g) = Inv.inv from
      funext fun g => if_pos hm]
    exact Measure.measurePreserving_inv μG
  · rw [show (fun g : G => if m.1.2 = 0 then g⁻¹ else g) = id from
      funext fun g => if_neg hm]
    exact MeasurePreserving.id μG

/-- Pointwise value of the split configuration on the `s` side
(the corpus's `splitEquiv_symm_apply_mem`, restated locally —
`LatticeGramSeries` is not imported here). -/
theorem splitSymm_apply_mem {s : Finset (Link (Fin 4 → ZMod N))}
    (y : ↥s → G) (u : ↥sᶜ → G) {ℓ : Link (Fin 4 → ZMod N)}
    (hℓ : ℓ ∈ s) :
    (splitEquiv s).symm (y, u) ℓ = y ⟨ℓ, hℓ⟩ := by
  have h1 : (splitEquiv s) ((splitEquiv s).symm (y, u)) = (y, u) :=
    MeasurableEquiv.apply_symm_apply _ _
  have h2 := congrFun (splitEquiv_fst s ((splitEquiv s).symm (y, u)))
    ⟨ℓ, hℓ⟩
  rw [h1] at h2
  exact h2.symm

/-- Pointwise value of the split configuration on the
complement side. -/
theorem splitSymm_apply_not_mem {s : Finset (Link (Fin 4 → ZMod N))}
    (y : ↥s → G) (u : ↥sᶜ → G) {ℓ : Link (Fin 4 → ZMod N)}
    (hℓ : ℓ ∈ sᶜ) :
    (splitEquiv s).symm (y, u) ℓ = u ⟨ℓ, hℓ⟩ := by
  have h1 : (splitEquiv s) ((splitEquiv s).symm (y, u)) = (y, u) :=
    MeasurableEquiv.apply_symm_apply _ _
  have h2 := congrFun (splitEquiv_snd s ((splitEquiv s).symm (y, u)))
    ⟨ℓ, hℓ⟩
  rw [h1] at h2
  exact h2.symm

/-- **The reflection identity**: reflecting the assembly with
swapped halves and plane-inverted strata returns the original
assembly. Checked stratum by stratum. -/
theorem planeAssemble_reflConfig (hN : Even N)
    (z z' : ↥(posLinks (N := N)) → G)
    (a : ↥(planeHalfLinks (N := N)) → G)
    (a' : ↥(planeNegLinks (N := N)) → G) :
    reflConfig (planeAssemble hN z' z (planeInvHalf a) (planeInvNeg a'))
      = planeAssemble hN z z' a a' := by
  funext ℓ
  by_cases hhalf : ℓ ∈ halfLinks (N := N)
  · rw [show planeAssemble hN z z' a a' ℓ
        = joinHalf z a ⟨ℓ, hhalf⟩ from
      splitSymm_apply_mem _ _ hhalf]
    by_cases hpos : ℓ ∈ posLinks (N := N)
    · rw [joinHalf, dif_pos hpos]
      show (if ℓ.2 = 0
          then (planeAssemble hN z' z (planeInvHalf a) (planeInvNeg a')
            (reflLink ℓ))⁻¹
          else planeAssemble hN z' z (planeInvHalf a) (planeInvNeg a')
            (reflLink ℓ)) = z ⟨ℓ, hpos⟩
      rw [show planeAssemble hN z' z (planeInvHalf a) (planeInvNeg a')
            (reflLink ℓ)
          = joinNeg hN z (planeInvNeg a')
            ⟨reflLink ℓ, reflLink_mem_negLinks hN hpos⟩ from
        splitSymm_apply_not_mem _ _ (reflLink_mem_negLinks hN hpos),
        joinNeg_apply_not_plane hN z (planeInvNeg a')
          (reflLink_not_mem_planeLinks hpos)]
      by_cases hd : ℓ.2 = 0
      · rw [if_pos hd]
        have hd2 : (reflLink (reflLink ℓ)).2 = 0 := by
          rw [reflLink_involutive]; exact hd
        rw [if_pos hd2, inv_inv]
        congr 1
        exact Subtype.ext (reflLink_involutive ℓ)
      · rw [if_neg hd]
        have hd2 : (reflLink (reflLink ℓ)).2 ≠ 0 := by
          rw [reflLink_involutive]; exact hd
        rw [if_neg hd2]
        congr 1
        exact Subtype.ext (reflLink_involutive ℓ)
    · have hmem : ℓ ∈ planeHalfLinks (N := N) :=
        halfLinks_mem_planeHalf_of_not_pos hhalf hpos
      have hfix : reflLink ℓ = ℓ := (mem_planeHalfLinks.mp hmem).1
      rw [joinHalf, dif_neg hpos]
      show (if ℓ.2 = 0
          then (planeAssemble hN z' z (planeInvHalf a) (planeInvNeg a')
            (reflLink ℓ))⁻¹
          else planeAssemble hN z' z (planeInvHalf a) (planeInvNeg a')
            (reflLink ℓ)) = a ⟨ℓ, hmem⟩
      rw [hfix,
        show planeAssemble hN z' z (planeInvHalf a) (planeInvNeg a') ℓ
          = joinHalf z' (planeInvHalf a) ⟨ℓ, hhalf⟩ from
        splitSymm_apply_mem _ _ hhalf, joinHalf, dif_neg hpos]
      by_cases hd : ℓ.2 = 0
      · rw [if_pos hd,
          show planeInvHalf a ⟨ℓ, hmem⟩ = (a ⟨ℓ, hmem⟩)⁻¹ from if_pos hd,
          inv_inv]
      · rw [if_neg hd,
          show planeInvHalf a ⟨ℓ, hmem⟩ = a ⟨ℓ, hmem⟩ from if_neg hd]
  · have hneg : ℓ ∈ negLinks (N := N) := Finset.mem_compl.mpr hhalf
    rw [show planeAssemble hN z z' a a' ℓ
        = joinNeg hN z' a' ⟨ℓ, hneg⟩ from
      splitSymm_apply_not_mem _ _ hneg]
    by_cases hpl : ℓ ∈ planeLinks (N := N)
    · have hfix : reflLink ℓ = ℓ := mem_planeLinks.mp hpl
      have hmem : ℓ ∈ planeNegLinks (N := N) :=
        negLinks_mem_planeNeg_of_plane hneg hpl
      rw [joinNeg_apply_plane hN z' a' hpl]
      show (if ℓ.2 = 0
          then (planeAssemble hN z' z (planeInvHalf a) (planeInvNeg a')
            (reflLink ℓ))⁻¹
          else planeAssemble hN z' z (planeInvHalf a) (planeInvNeg a')
            (reflLink ℓ)) = a' ⟨ℓ, hmem⟩
      rw [hfix,
        show planeAssemble hN z' z (planeInvHalf a) (planeInvNeg a') ℓ
          = joinNeg hN z (planeInvNeg a') ⟨ℓ, hneg⟩ from
        splitSymm_apply_not_mem _ _ hneg,
        joinNeg_apply_plane hN z (planeInvNeg a') hpl]
      by_cases hd : ℓ.2 = 0
      · rw [if_pos hd,
          show planeInvNeg a' ⟨ℓ, hmem⟩ = (a' ⟨ℓ, hmem⟩)⁻¹ from if_pos hd,
          inv_inv]
      · rw [if_neg hd,
          show planeInvNeg a' ⟨ℓ, hmem⟩ = a' ⟨ℓ, hmem⟩ from if_neg hd]
    · rw [joinNeg_apply_not_plane hN z' a' hpl]
      show (if ℓ.2 = 0
          then (planeAssemble hN z' z (planeInvHalf a) (planeInvNeg a')
            (reflLink ℓ))⁻¹
          else planeAssemble hN z' z (planeInvHalf a) (planeInvNeg a')
            (reflLink ℓ))
        = (if (reflLink ℓ).2 = 0
            then (z' ⟨reflLink ℓ, reflLink_mem_posLinks hN hneg hpl⟩)⁻¹
            else z' ⟨reflLink ℓ, reflLink_mem_posLinks hN hneg hpl⟩)
      rw [show planeAssemble hN z' z (planeInvHalf a) (planeInvNeg a')
            (reflLink ℓ)
          = joinHalf z' (planeInvHalf a)
            ⟨reflLink ℓ, posLinks_subset_halfLinks
              (reflLink_mem_posLinks hN hneg hpl)⟩ from
        splitSymm_apply_mem _ _
          (posLinks_subset_halfLinks (reflLink_mem_posLinks hN hneg hpl)),
        joinHalf, dif_pos (reflLink_mem_posLinks hN hneg hpl)]
      by_cases hd : ℓ.2 = 0
      · have hd2 : (reflLink ℓ).2 = 0 := by
          rw [reflLink_snd]; exact hd
        rw [if_pos hd, if_pos hd2]
      · have hd2 : (reflLink ℓ).2 ≠ 0 := by
          rw [reflLink_snd]; exact hd
        rw [if_neg hd, if_neg hd2]

/-- **Symmetry of the plane-averaged kernel**: reflection
invariance of the action, transported through the plane
strata by the inversion substitution. -/
theorem planeAvgKernel_symm (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) :
    planeAvgKernel μG ρ hN β z z' = planeAvgKernel μG ρ hN β z' z := by
  have hpt : ∀ (a : ↥(planeHalfLinks (N := N)) → G)
      (a' : ↥(planeNegLinks (N := N)) → G),
      (Real.exp (-(wilsonAction (torusShift N) ρ β
        (planeAssemble hN z' z (planeInvHalf a) (planeInvNeg a')))) : ℂ)
      = (Real.exp (-(wilsonAction (torusShift N) ρ β
          (planeAssemble hN z z' a a'))) : ℂ) := by
    intro a a'
    rw [← planeAssemble_reflConfig hN z z' a a', wilsonAction_reflConfig ρ hN]
  symm
  calc planeAvgKernel μG ρ hN β z' z
      = ∫ a, ∫ a', (Real.exp (-(wilsonAction (torusShift N) ρ β
            (planeAssemble hN z' z a (planeInvNeg a')))) : ℂ)
          ∂(Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)
          ∂(Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG) := by
        unfold planeAvgKernel
        apply integral_congr_ae
        exact ae_of_all _ fun a =>
          ((measurePreserving_planeInvNegEquiv μG).integral_comp
            planeInvNegEquiv.measurableEmbedding _).symm
    _ = ∫ a, ∫ a', (Real.exp (-(wilsonAction (torusShift N) ρ β
            (planeAssemble hN z' z (planeInvHalf a) (planeInvNeg a')))) : ℂ)
          ∂(Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)
          ∂(Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG) :=
        ((measurePreserving_planeInvHalfEquiv μG).integral_comp
          planeInvHalfEquiv.measurableEmbedding _).symm
    _ = ∫ a, ∫ a', (Real.exp (-(wilsonAction (torusShift N) ρ β
            (planeAssemble hN z z' a a'))) : ℂ)
          ∂(Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)
          ∂(Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG) := by
        exact integral_congr_ae (ae_of_all _ fun a =>
          integral_congr_ae (ae_of_all _ fun a' => hpt a a'))
    _ = planeAvgKernel μG ρ hN β z z' := rfl

/-- **Reality of the plane-averaged kernel**: the integrand is
real-valued, so the kernel is a real number. -/
theorem planeAvgKernel_conj (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) :
    (starRingEnd ℂ) (planeAvgKernel μG ρ hN β z z')
      = planeAvgKernel μG ρ hN β z z' := by
  unfold planeAvgKernel
  rw [starRingEnd_apply, RCLike.star_def, ← integral_conj]
  apply integral_congr_ae
  refine ae_of_all _ fun a => ?_
  dsimp only
  rw [← integral_conj]
  apply integral_congr_ae
  exact ae_of_all _ fun a' => by
    dsimp only
    rw [starRingEnd_apply, RCLike.star_def]
    exact RCLike.conj_ofReal _

/-- **Conjugate symmetry of the plane-averaged kernel**:
symmetry composed with reality. -/
theorem planeAvgKernel_conj_symm (hN : Even N) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) :
    (starRingEnd ℂ) (planeAvgKernel μG ρ hN β z z')
      = planeAvgKernel μG ρ hN β z' z := by
  rw [planeAvgKernel_conj μG ρ hN β z z', planeAvgKernel_symm μG ρ hN β z z']

/-- The regrouping of the four factor spaces:
`((z, a), (z', a')) ↦ ((z, z'), (a, a'))`, as a measurable
equiv (a composite of associators and one commutation). -/
def regroupEquiv : ((↥(posLinks (N := N)) → G)
    × (↥(planeHalfLinks (N := N)) → G))
    × ((↥(posLinks (N := N)) → G) × (↥(planeNegLinks (N := N)) → G))
    ≃ᵐ ((↥(posLinks (N := N)) → G) × (↥(posLinks (N := N)) → G))
    × ((↥(planeHalfLinks (N := N)) → G)
      × (↥(planeNegLinks (N := N)) → G)) :=
  MeasurableEquiv.prodAssoc.trans
    (((MeasurableEquiv.refl _).prodCongr
      (MeasurableEquiv.prodAssoc.symm.trans
        ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl _)).trans
          MeasurableEquiv.prodAssoc))).trans
      MeasurableEquiv.prodAssoc.symm)

theorem measurePreserving_prodAssoc' {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ]
    (μa : Measure α) (μb : Measure β) (μc : Measure γ)
    [SFinite μa] [SFinite μb] [SFinite μc] :
    MeasurePreserving MeasurableEquiv.prodAssoc
      ((μa.prod μb).prod μc) (μa.prod (μb.prod μc)) :=
  ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩

theorem measurePreserving_regroup :
    MeasurePreserving regroupEquiv
      (((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG)).prod
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)))
      (((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)).prod
        ((Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG))) :=
  (measurePreserving_prodAssoc' _ _ _).trans
    (((MeasurePreserving.id _).prod
      ((measurePreserving_prodAssoc' _ _ _).symm.trans
        ((MeasurePreserving.prod Measure.measurePreserving_swap (MeasurePreserving.id _)).trans
          (measurePreserving_prodAssoc' _ _ _)))).trans
      (measurePreserving_prodAssoc' _ _ _).symm)

/-- Integrability of the kernel-form integrand of
`osForm_eq_kernel`, under the Gram-criterion side conditions
on the factor `f` (AE strong measurability and boundedness —
the same side conditions the corpus's own kernel route
carries). -/
theorem integrable_osKernelIntegrand
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (hd : 0 < d) (β : ℝ) (f : (↥(posLinks (N := N)) → G) → ℂ)
    (hfmeas : AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (hfbdd : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C) :
    Integrable (fun p : (↥(halfLinks (N := N)) → G)
        × (↥(negLinks (N := N)) → G) =>
      (Real.exp (-(wilsonAction (torusShift N) ρ β
        ((splitEquiv (halfLinks (N := N))).symm p))) : ℂ)
      * ((starRingEnd ℂ) (f (mirrorP hN p.2)) * f (restrictPos p.1)))
      ((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) := by
  obtain ⟨C, hC⟩ := hfbdd
  have hmapA : Measure.map (fun p : (↥(halfLinks (N := N)) → G)
        × (↥(negLinks (N := N)) → G) => mirrorP hN p.2)
      ((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(negLinks (N := N)) => μG))
      = Measure.pi fun _ : ↥(posLinks (N := N)) => μG :=
    ((measurePreserving_mirrorP μG hN).comp measurePreserving_snd).map_eq
  have hmapB : Measure.map (fun p : (↥(halfLinks (N := N)) → G)
        × (↥(negLinks (N := N)) → G) => restrictPos p.1)
      ((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(negLinks (N := N)) => μG))
      = Measure.pi fun _ : ↥(posLinks (N := N)) => μG :=
    (measurePreserving_fst.comp
      ((measurePreserving_halfPlaneEquiv μG).comp
        measurePreserving_fst)).map_eq
  refine Integrable.of_bound ?_
    (Real.exp (|β| * (2 * (16 * (Fintype.card (Fin 4 → ZMod N) : ℝ))))
      * (|C| * |C|)) (ae_of_all _ fun p => ?_)
  · apply AEStronglyMeasurable.mul
    · exact (Complex.continuous_ofReal.measurable.comp
        (Real.continuous_exp.measurable.comp
          ((measurable_wilsonAction (torusShift N) ρ hρcont β).comp
            (splitEquiv (halfLinks (N := N))).symm.measurable).neg)).aestronglyMeasurable
    · apply AEStronglyMeasurable.mul
      · have hfA : AEStronglyMeasurable f
            (Measure.map (fun p : (↥(halfLinks (N := N)) → G)
              × (↥(negLinks (N := N)) → G) => mirrorP hN p.2)
              ((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
                (Measure.pi fun _ : ↥(negLinks (N := N)) => μG))) :=
          hmapA ▸ hfmeas
        exact RCLike.continuous_conj.comp_aestronglyMeasurable
          (hfA.comp_measurable
            ((measurePreserving_mirrorP μG hN).measurable.comp measurable_snd))
      · have hfB : AEStronglyMeasurable f
            (Measure.map (fun p : (↥(halfLinks (N := N)) → G)
              × (↥(negLinks (N := N)) → G) => restrictPos p.1)
              ((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
                (Measure.pi fun _ : ↥(negLinks (N := N)) => μG))) :=
          hmapB ▸ hfmeas
        exact hfB.comp_measurable (measurable_restrictPos'.comp measurable_fst)
  · rw [norm_mul, norm_mul]
    have hS : ‖(Real.exp (-(wilsonAction (torusShift N) ρ β
        ((splitEquiv (halfLinks (N := N))).symm p))) : ℂ)‖
        ≤ Real.exp (|β| * (2 * (16 * (Fintype.card (Fin 4 → ZMod N) : ℝ)))) := by
      rw [show ‖(Real.exp (-(wilsonAction (torusShift N) ρ β
            ((splitEquiv (halfLinks (N := N))).symm p))) : ℂ)‖
          = |Real.exp (-(wilsonAction (torusShift N) ρ β
            ((splitEquiv (halfLinks (N := N))).symm p)))| from
        RCLike.norm_ofReal _, Real.abs_exp]
      exact Real.exp_le_exp.mpr ((neg_le_abs _).trans
        (wilsonAction_abs_le (torusShift N) ρ hd β _))
    have hf1 : ‖f (mirrorP hN p.2)‖ ≤ |C| := (hC _).trans (le_abs_self C)
    have hf2 : ‖f (restrictPos p.1)‖ ≤ |C| := (hC _).trans (le_abs_self C)
    have hstar : ‖(starRingEnd ℂ) (f (mirrorP hN p.2))‖ ≤ |C| := by
      rw [starRingEnd_apply, norm_star]
      exact hf1
    exact mul_le_mul hS (mul_le_mul hstar hf2 (norm_nonneg _) (abs_nonneg C))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.exp_nonneg _)

/-- Integrability of the assembled Gibbs weight over the
plane strata (the marginalization's inner integrand). -/
theorem integrable_exp_assemble
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (hd : 0 < d) (β : ℝ)
    (z z' : ↥(posLinks (N := N)) → G) :
    Integrable (fun s : (↥(planeHalfLinks (N := N)) → G)
        × (↥(planeNegLinks (N := N)) → G) =>
      (Real.exp (-(wilsonAction (torusShift N) ρ β
        (planeAssemble hN z z' s.1 s.2))) : ℂ))
      ((Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)) := by
  refine Integrable.of_bound ?_
    (Real.exp (|β| * (2 * (16 * (Fintype.card (Fin 4 → ZMod N) : ℝ)))))
    (ae_of_all _ fun s => ?_)
  · exact (Complex.continuous_ofReal.measurable.comp
      (Real.continuous_exp.measurable.comp
        ((measurable_wilsonAction (torusShift N) ρ hρcont β).comp
          (measurable_planeAssemble hN z z')).neg)).aestronglyMeasurable
  · rw [show ‖(Real.exp (-(wilsonAction (torusShift N) ρ β
          (planeAssemble hN z z' s.1 s.2))) : ℂ)‖
        = |Real.exp (-(wilsonAction (torusShift N) ρ β
          (planeAssemble hN z z' s.1 s.2)))| from
      RCLike.norm_ofReal _, Real.abs_exp]
    exact Real.exp_le_exp.mpr ((neg_le_abs _).trans
      (wilsonAction_abs_le (torusShift N) ρ hd β _))

/-- The assembly map (strict data and plane strata to the two
halves) is measure-preserving: it is the product of the two
split equivs' inverses. -/
theorem measurePreserving_assemblyPair (hN : Even N) :
    MeasurePreserving
      (fun w : ((↥(posLinks (N := N)) → G)
          × (↥(planeHalfLinks (N := N)) → G))
          × ((↥(posLinks (N := N)) → G)
            × (↥(planeNegLinks (N := N)) → G)) =>
        (joinHalf w.1.1 w.1.2, joinNeg hN w.2.1 w.2.2))
      (((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG)).prod
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG)))
      ((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(negLinks (N := N)) => μG)) :=
  (measurePreserving_halfPlaneEquiv μG).symm.prod
    (measurePreserving_negPlaneEquiv μG hN).symm

/-- **The reduction identity** (the charter's pairing): for an
observable supported on the strict half with factor `f`, the
OS diagonal is `Z⁻¹` times the strict-half pairing of `f`
against `K̄_β f`. The side conditions on `f` are the
Gram-criterion-style ones the corpus's own kernel route
carries (AE strong measurability and boundedness), named
here, not hidden. Positivity of the pairing is NOT asserted:
it is exactly the fenced PSD question about `K̄_β`. -/
theorem osForm_eq_planeAvgKernel
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hN : Even N)
    (hd : 0 < d) (β : ℝ)
    (F : Config (Fin 4 → ZMod N) G → ℂ)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (hF : ∀ U, F U = f (fun ℓ : ↥(posLinks (N := N)) => U ℓ.1))
    (hfmeas : AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (hfbdd : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C) :
    osForm μG ρ β F F
      = ((gibbsPartition (torusShift N) μG ρ β : ℂ))⁻¹
        * ∫ r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G),
            (starRingEnd ℂ) (f r.2)
              * (planeAvgKernel μG ρ hN β r.1 r.2 * f r.1)
            ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
              (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
  rw [osForm_eq_kernel μG ρ hρcont hN hd β F f hF]
  congr 1
  have hΦ := integrable_osKernelIntegrand μG ρ hρcont hN hd β f hfmeas hfbdd
  have hĜ : Integrable (fun w : ((↥(posLinks (N := N)) → G)
        × (↥(planeHalfLinks (N := N)) → G))
        × ((↥(posLinks (N := N)) → G)
          × (↥(planeNegLinks (N := N)) → G)) =>
      (Real.exp (-(wilsonAction (torusShift N) ρ β
        ((splitEquiv (halfLinks (N := N))).symm
          (joinHalf w.1.1 w.1.2, joinNeg hN w.2.1 w.2.2)))) : ℂ)
      * ((starRingEnd ℂ) (f (mirrorP hN (joinNeg hN w.2.1 w.2.2)))
        * f (restrictPos (joinHalf w.1.1 w.1.2))))
      (((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG)).prod
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG))) :=
    (measurePreserving_assemblyPair μG hN).integrable_comp_of_integrable hΦ
  have hĜB : Integrable (Function.uncurry
      (fun (q : (↥(posLinks (N := N)) → G)
          × (↥(planeHalfLinks (N := N)) → G))
        (q' : (↥(posLinks (N := N)) → G)
          × (↥(planeNegLinks (N := N)) → G)) =>
        (starRingEnd ℂ) (f q'.1)
          * ((Real.exp (-(wilsonAction (torusShift N) ρ β
              (planeAssemble hN q.1 q'.1 q.2 q'.2))) : ℂ)
            * f q.1)))
      (((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG)).prod
        ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG))) :=
    hĜ.congr (ae_of_all _ fun w => by
      dsimp only [Function.uncurry]
      unfold planeAssemble
      rw [mirrorP_joinNeg, restrictPos_joinHalf]
      ring)
  have hĜC : Integrable (fun w : ((↥(posLinks (N := N)) → G)
        × (↥(posLinks (N := N)) → G))
        × ((↥(planeHalfLinks (N := N)) → G)
          × (↥(planeNegLinks (N := N)) → G)) =>
      (starRingEnd ℂ) (f w.1.2)
        * ((Real.exp (-(wilsonAction (torusShift N) ρ β
            (planeAssemble hN w.1.1 w.1.2 w.2.1 w.2.2))) : ℂ)
          * f w.1.1))
      (((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)).prod
        ((Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG).prod
          (Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG))) :=
    (measurePreserving_regroup μG).symm.integrable_comp_of_integrable hĜB
  calc ∫ p : (↥(halfLinks (N := N)) → G) × (↥(negLinks (N := N)) → G),
          (Real.exp (-(wilsonAction (torusShift N) ρ β
            ((splitEquiv (halfLinks (N := N))).symm p))) : ℂ)
          * ((starRingEnd ℂ) (f (mirrorP hN p.2)) * f (restrictPos p.1))
          ∂((Measure.pi fun _ : ↥(halfLinks (N := N)) => μG).prod
            (Measure.pi fun _ : ↥(negLinks (N := N)) => μG))
      = ∫ q : (↥(posLinks (N := N)) → G)
            × (↥(planeHalfLinks (N := N)) → G),
          ∫ q' : (↥(posLinks (N := N)) → G)
              × (↥(planeNegLinks (N := N)) → G),
            (Real.exp (-(wilsonAction (torusShift N) ρ β
              ((splitEquiv (halfLinks (N := N))).symm
                (joinHalf q.1 q.2, joinNeg hN q'.1 q'.2)))) : ℂ)
            * ((starRingEnd ℂ) (f (mirrorP hN (joinNeg hN q'.1 q'.2)))
              * f (restrictPos (joinHalf q.1 q.2)))
            ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
              (Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG))
            ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
              (Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG)) := by
        rw [integral_prod _ hΦ, integral_half_split]
        apply integral_congr_ae
        exact ae_of_all _ fun q => integral_neg_split μG hN _
    _ = ∫ q : (↥(posLinks (N := N)) → G)
            × (↥(planeHalfLinks (N := N)) → G),
          ∫ q' : (↥(posLinks (N := N)) → G)
              × (↥(planeNegLinks (N := N)) → G),
            (starRingEnd ℂ) (f q'.1)
            * ((Real.exp (-(wilsonAction (torusShift N) ρ β
                (planeAssemble hN q.1 q'.1 q.2 q'.2))) : ℂ) * f q.1)
            ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
              (Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG))
            ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
              (Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG)) := by
        apply integral_congr_ae
        refine ae_of_all _ fun q => ?_
        apply integral_congr_ae
        refine ae_of_all _ fun q' => ?_
        dsimp only
        unfold planeAssemble
        rw [mirrorP_joinNeg, restrictPos_joinHalf]
        ring
    _ = ∫ w : ((↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G))
          × ((↥(planeHalfLinks (N := N)) → G)
            × (↥(planeNegLinks (N := N)) → G)),
          (starRingEnd ℂ) (f w.1.2)
          * ((Real.exp (-(wilsonAction (torusShift N) ρ β
              (planeAssemble hN w.1.1 w.1.2 w.2.1 w.2.2))) : ℂ)
            * f w.1.1)
          ∂(((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
              (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)).prod
            ((Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG).prod
              (Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG))) := by
        rw [integral_integral hĜB]
        exact (measurePreserving_regroup μG).integral_comp
          regroupEquiv.measurableEmbedding
          (fun w : ((↥(posLinks (N := N)) → G)
              × (↥(posLinks (N := N)) → G))
              × ((↥(planeHalfLinks (N := N)) → G)
                × (↥(planeNegLinks (N := N)) → G)) =>
            (starRingEnd ℂ) (f w.1.2)
              * ((Real.exp (-(wilsonAction (torusShift N) ρ β
                  (planeAssemble hN w.1.1 w.1.2 w.2.1 w.2.2))) : ℂ)
                * f w.1.1))
    _ = ∫ r : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G),
          (starRingEnd ℂ) (f r.2)
            * (planeAvgKernel μG ρ hN β r.1 r.2 * f r.1)
          ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
            (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
        rw [integral_prod _ hĜC]
        apply integral_congr_ae
        refine ae_of_all _ fun r => ?_
        dsimp only
        have hŴ := integrable_exp_assemble μG ρ hρcont hN hd β r.1 r.2
        have hprod : ∫ s : (↥(planeHalfLinks (N := N)) → G)
              × (↥(planeNegLinks (N := N)) → G),
              (Real.exp (-(wilsonAction (torusShift N) ρ β
                (planeAssemble hN r.1 r.2 s.1 s.2))) : ℂ)
              ∂((Measure.pi fun _ : ↥(planeHalfLinks (N := N)) => μG).prod
                (Measure.pi fun _ : ↥(planeNegLinks (N := N)) => μG))
            = planeAvgKernel μG ρ hN β r.1 r.2 :=
          integral_prod _ hŴ
        have hpt : ∀ s : (↥(planeHalfLinks (N := N)) → G)
            × (↥(planeNegLinks (N := N)) → G),
            (starRingEnd ℂ) (f r.2)
              * ((Real.exp (-(wilsonAction (torusShift N) ρ β
                  (planeAssemble hN r.1 r.2 s.1 s.2))) : ℂ) * f r.1)
            = ((starRingEnd ℂ) (f r.2) * f r.1)
              * (Real.exp (-(wilsonAction (torusShift N) ρ β
                  (planeAssemble hN r.1 r.2 s.1 s.2))) : ℂ) :=
          fun s => by ring
        rw [integral_congr_ae (ae_of_all _ hpt), integral_const_mul, hprod]
        ring

end Kernel

