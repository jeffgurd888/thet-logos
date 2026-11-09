/-
# MQ3-3: positivity transport through the projective limit

Rung MQ3-3 of the M-Q3 continuum ladder
(`m-q3-scope-2026-11-08.md` §4). Lane STATUS: `STATUS.md` at the
worktree root — the design (§3 there) was frozen before this
content, including the faced fact (§2 there) that the finite
integrated Gram criterion `osForm_nonneg_of_gram_integrated`
lives on the torus seats `Config (Fin 4 → ZMod N) G` and cannot be
applied verbatim to MQ3-2's ℤ⁴ window limit: what transports is
its content — reflection positivity of cylinder observables on a
strict half, whose diagonal at the free point is `W * conj W`
(the criterion's β = 0 collapse, landed on the torus as
`osForm_zero_nonneg`). The limit system's OS form is therefore
DEFINED here in the corpus's own shape, with a ℤ⁴ reflection
built for the purpose; the transport theorems are the content.

## What is built

Consuming MQ3-2 (`ProjectiveGibbsFamily.lean`: window Gibbs
family `windowGibbs μG ρ β` over `LinkZ = SiteZ × Fin 4`,
projective at β = 0 unconditionally, at general β conditionally
on the named Prop `WindowGibbsProjective`; K-MQ3-BOND fired at
general β ≠ 0 there):

* a time reflection `reflLinkZ` on `LinkZ` (`t ↦ -t - 1` on base
  sites, corpus orientation convention: inversion on time
  links), involutive, sending the strict positive half
  `{ℓ | 0 ≤ ℓ.1 0}` into the negative region — a positive window
  and its reflection are disjoint, no plane stratum intervenes;
* the **limit OS form** `limitOSForm μ F = ∫ U, conj (F
  (reflConfigZ U)) * F U ∂μ` and the **window OS form**
  `windowOSForm` on the reflection-closed hull of a window —
  definitions (design, STATUS §3);
* **(TIER β, conditional) the transport identity:** for any
  projective limit `μ` of the window family at coupling `β`,
  the limit OS form of a cylinder observable supported on a
  positive window `J` EQUALS the window OS form at the hull
  seat `K = J ∪ reflLinkZ '' J` — the limit's `K`-marginal is
  the window seat, by `IsProjectiveLimit`. Nonnegativity
  transports with the identity. Positivity of the window form
  at `β ≠ 0` is NOT claimed (not in the tree).
* **(TIER 0, unconditional) positivity at the free point:** the
  hull seat at β = 0 is the product Haar measure, the split /
  mirror marginal identities give `windowOSForm = W * conj W`,
  and transport yields `0 ≤ (limitOSForm μ (cylObs J f)).re ∧
  (limitOSForm μ (cylObs J f)).im = 0` for MQ3-2's unconditional
  β = 0 limit measure. **K-MQ3-TRANSPORT does not fire.**

NO CLAIM. Scaffolding (scope §2(b)): no tie to
`ScalingLimitOfLattice` is proved or asserted; this is not the
M-Q3 event (MQ3-6) and moves no dial. Dials 0/4; Dial 3 = 0.
-/

import ThetLogos.ProjectiveGibbsFamily
import Mathlib.Probability.ProductMeasure

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal

/-! ## §1. The ℤ⁴ time reflection -/

/-- Reflection of a site across the time plane between `-1` and
`0`: time coordinate `t ↦ -t - 1`, spatial coordinates fixed. -/
def reflSiteZ (x : SiteZ) : SiteZ :=
  Function.update x 0 (-(x 0) - 1)

theorem reflSiteZ_zero (x : SiteZ) : reflSiteZ x 0 = -(x 0) - 1 :=
  Function.update_self _ _ _

theorem reflSiteZ_of_ne (x : SiteZ) {μ : Fin 4} (hμ : μ ≠ 0) :
    reflSiteZ x μ = x μ :=
  Function.update_of_ne hμ _ _

/-- Reflection of a link: a spatial link `(x, μ)`, `μ ≠ 0`, goes
to `(reflSiteZ x, μ)`; a time link `(x, 0)` goes to the time link
based at `-(x 0) - 2` (the reflection of its head). -/
def reflLinkZ (ℓ : LinkZ) : LinkZ :=
  if ℓ.2 = 0 then (Function.update ℓ.1 0 (-(ℓ.1 0) - 2), 0)
  else (reflSiteZ ℓ.1, ℓ.2)

theorem reflLinkZ_snd (ℓ : LinkZ) : (reflLinkZ ℓ).2 = ℓ.2 := by
  unfold reflLinkZ
  split_ifs with h
  · exact h.symm
  · rfl

theorem reflLinkZ_involutive : Function.Involutive reflLinkZ := by
  intro ℓ
  obtain ⟨x, μ⟩ := ℓ
  by_cases hμ : μ = 0
  · subst hμ
    have h1 : reflLinkZ (x, 0)
        = (Function.update x 0 (-(x 0) - 2), 0) := if_pos rfl
    rw [h1]
    have h2 : reflLinkZ (Function.update x 0 (-(x 0) - 2), 0)
        = (Function.update (Function.update x 0 (-(x 0) - 2)) 0
            (-((Function.update x 0 (-(x 0) - 2)) 0) - 2), 0) :=
      if_pos rfl
    rw [h2, Function.update_self]
    congr 1
    funext ν
    by_cases hν : ν = 0
    · subst hν
      simp only [Function.update_self]
      ring
    · rw [Function.update_of_ne hν, Function.update_of_ne hν]
  · have h1 : reflLinkZ (x, μ) = (reflSiteZ x, μ) := if_neg hμ
    rw [h1]
    have h2 : reflLinkZ (reflSiteZ x, μ) = (reflSiteZ (reflSiteZ x), μ) :=
      if_neg hμ
    rw [h2]
    congr 1
    funext ν
    by_cases hν : ν = 0
    · subst hν
      show reflSiteZ (reflSiteZ x) 0 = x 0
      rw [reflSiteZ_zero, reflSiteZ_zero]
      ring
    · rw [reflSiteZ_of_ne _ hν, reflSiteZ_of_ne _ hν]

/-- The reflected link's base time, for a link based at nonnegative
time, is at most `-1`: the reflection sends the strict positive
half into the negative region. -/
theorem reflLinkZ_fst_zero_le (ℓ : LinkZ) (hℓ : 0 ≤ ℓ.1 0) :
    (reflLinkZ ℓ).1 0 ≤ -1 := by
  obtain ⟨x, μ⟩ := ℓ
  have hℓ : 0 ≤ x 0 := hℓ
  by_cases hμ : μ = 0
  · subst hμ
    have h1 : reflLinkZ (x, 0)
        = (Function.update x 0 (-(x 0) - 2), 0) := if_pos rfl
    rw [h1]
    show (Function.update x 0 (-(x 0) - 2)) 0 ≤ -1
    rw [Function.update_self]
    omega
  · have h1 : reflLinkZ (x, μ) = (reflSiteZ x, μ) := if_neg hμ
    rw [h1]
    show reflSiteZ x 0 ≤ -1
    rw [reflSiteZ_zero]
    omega

section Seats

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [MeasurableInv G] [BorelSpace G] [SecondCountableTopology G]
  [PolishSpace G]
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-! ## §2. The reflection-closed hull and its closure -/

/-- The reflection of a window, as a finset of links. -/
def reflFinset (J : Finset LinkZ) : Finset LinkZ :=
  J.map ⟨reflLinkZ, reflLinkZ_involutive.injective⟩

theorem mem_reflFinset {J : Finset LinkZ} {ℓ : LinkZ} :
    ℓ ∈ reflFinset J ↔ ∃ m ∈ J, reflLinkZ m = ℓ := by
  rw [reflFinset, Finset.mem_map]
  exact ⟨fun ⟨m, hm, h⟩ => ⟨m, hm, h⟩, fun ⟨m, hm, h⟩ => ⟨m, hm, h⟩⟩

/-- The reflection-closed hull of a window: itself plus its
reflection. -/
def reflHull (J : Finset LinkZ) : Finset LinkZ := J ∪ reflFinset J

/-- A window is contained in its hull (with the hull's own
membership form, for elaboration hygiene). -/
def hull_subset_self (J : Finset LinkZ) : J ⊆ reflHull J :=
  fun ℓ hℓ => Finset.mem_union_left _ hℓ

/-- The reflection of a window link lies in the hull. -/
theorem reflLinkZ_mem_hull_of_mem {J : Finset LinkZ} {m : LinkZ}
    (hm : m ∈ J) : reflLinkZ m ∈ reflHull J :=
  Finset.mem_union_right _ (mem_reflFinset.mpr ⟨m, hm, rfl⟩)

/-- A positive window is disjoint from its reflection. -/
theorem reflLinkZ_not_mem_of_pos {J : Finset LinkZ}
    (hJ : ∀ ℓ ∈ J, 0 ≤ ℓ.1 0) {m : LinkZ} (hm : m ∈ J) :
    reflLinkZ m ∉ J := by
  intro hmem
  have h1 := hJ _ hmem
  have h2 := reflLinkZ_fst_zero_le m (hJ m hm)
  omega

/-- The hull is closed under the reflection. -/
theorem reflLinkZ_mem_reflHull {J : Finset LinkZ}
    (hJ : ∀ ℓ ∈ J, 0 ≤ ℓ.1 0) (ℓ : LinkZ) (hℓ : ℓ ∈ reflHull J) :
    reflLinkZ ℓ ∈ reflHull J := by
  rw [reflHull, Finset.mem_union] at hℓ ⊢
  rcases hℓ with h | h
  · exact Or.inr (mem_reflFinset.mpr ⟨ℓ, h, rfl⟩)
  · rw [mem_reflFinset] at h
    obtain ⟨m, hm, rfl⟩ := h
    exact Or.inl (by rw [reflLinkZ_involutive]; exact hm)

/-! ## §3. Reflected configurations and the two OS forms -/

/-- The reflected configuration, in the corpus's `reflConfig`
convention: pull back along the link reflection, with inversion
on time links. -/
def reflConfigZ (U : LinkZ → G) : LinkZ → G :=
  fun ℓ => if ℓ.2 = 0 then (U (reflLinkZ ℓ))⁻¹ else U (reflLinkZ ℓ)

/-- A cylinder observable: `f` read on the window `J` of a full
configuration. -/
def cylObs (J : Finset LinkZ) (f : (∀ j : J, G) → ℂ) :
    (LinkZ → G) → ℂ :=
  fun U => f (fun j : J => U j.1)

/-- **The limit OS form** (definition, STATUS §3): the expectation
under `μ` of the reflected observable times the observable, in
the corpus's `osForm` shape. -/
noncomputable def limitOSForm (μ : Measure (LinkZ → G))
    (F : (LinkZ → G) → ℂ) : ℂ :=
  ∫ U, (starRingEnd ℂ) (F (reflConfigZ U)) * F U ∂μ

/-- The window reflection on hull configurations: the corpus
formula, transported along hull closure. -/
def windowReflConfig (K : Finset LinkZ)
    (hK : ∀ ℓ ∈ K, reflLinkZ ℓ ∈ K) (U : ∀ k : K, G) :
    ∀ k : K, G :=
  fun k => if k.1.2 = 0
    then (U ⟨reflLinkZ k.1, hK k.1 k.2⟩)⁻¹
    else U ⟨reflLinkZ k.1, hK k.1 k.2⟩

/-- Restriction of a hull configuration to the window. -/
def hullRestr (J K : Finset LinkZ) (hJK : J ⊆ K)
    (U : ∀ k : K, G) : ∀ j : J, G :=
  fun j => U ⟨j.1, hJK j.2⟩

/-- **The window OS form** (definition, STATUS §3): the OS form of
the cylinder observable `f` at the window seat `ν` on the
reflection-closed hull `K`. -/
noncomputable def windowOSForm (J K : Finset LinkZ) (hJK : J ⊆ K)
    (hK : ∀ ℓ ∈ K, reflLinkZ ℓ ∈ K) (ν : Measure (∀ k : K, G))
    (f : (∀ j : J, G) → ℂ) : ℂ :=
  ∫ U, (starRingEnd ℂ) (f (hullRestr J K hJK (windowReflConfig K hK U)))
    * f (hullRestr J K hJK U) ∂ν

/-! ## §4. The restriction and mirror maps on hull configurations -/

variable {J : Finset LinkZ} (hJ : ∀ ℓ ∈ J, 0 ≤ ℓ.1 0)

/-- The window `J` as a finset of the hull's index type. -/
def hullFinset (J : Finset LinkZ) : Finset (reflHull J) :=
  Finset.univ.filter (fun k : reflHull J => k.1 ∈ J)

/-- The identification `↥(hullFinset J) ≃ ↥J`. -/
def hullFinsetEquiv (J : Finset LinkZ) : ↥(hullFinset J) ≃ ↥J :=
  { toFun := fun k => ⟨k.1.1, (Finset.mem_filter.mp k.2).2⟩
    invFun := fun j => ⟨⟨j.1, (hull_subset_self J) j.2⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.2⟩⟩
    left_inv := fun k => Subtype.ext (Subtype.ext rfl)
    right_inv := fun j => Subtype.ext rfl }

/-- The mirror identification `↥J ≃ ↥(hullFinset J)ᶜ` by the link
reflection. -/
def hullMirrorEquiv (J : Finset LinkZ) (hJ : ∀ ℓ ∈ J, 0 ≤ ℓ.1 0) :
    ↥J ≃ ↥(hullFinset J)ᶜ :=
  { toFun := fun j => ⟨⟨reflLinkZ j.1,
        reflLinkZ_mem_hull_of_mem j.2⟩,
      Finset.mem_compl.mpr (fun hmem =>
        reflLinkZ_not_mem_of_pos hJ j.2 (Finset.mem_filter.mp hmem).2)⟩
    invFun := fun k => ⟨reflLinkZ k.1.1, by
      have hk2 : k.1.1 ∉ J := by
        intro hj
        exact (Finset.mem_compl.mp k.2)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
      have hk1 : k.1.1 ∈ J ∨ k.1.1 ∈ reflFinset J := by
        have h : k.1.1 ∈ J ∪ reflFinset J := k.1.2
        rwa [Finset.mem_union] at h
      rcases hk1 with h | h
      · exact absurd h hk2
      · rw [mem_reflFinset] at h
        obtain ⟨m, hm, hmk⟩ := h
        have : reflLinkZ k.1.1 = m := by
          rw [← hmk, reflLinkZ_involutive]
        rw [this]
        exact hm⟩
    left_inv := fun j => Subtype.ext (reflLinkZ_involutive j.1)
    right_inv := fun k => Subtype.ext (Subtype.ext
      (reflLinkZ_involutive k.1.1)) }

/-- The mirror map on hull configurations: the reflected window
read off the negative coordinates. -/
def hullMirror (J : Finset LinkZ)
    (U : ∀ k : reflHull J, G) : ∀ j : J, G :=
  fun j => if j.1.2 = 0
    then (U ⟨reflLinkZ j.1,
      reflLinkZ_mem_hull_of_mem j.2⟩)⁻¹
    else U ⟨reflLinkZ j.1,
      reflLinkZ_mem_hull_of_mem j.2⟩

/-- The window integrand's two factors read off a hull
configuration: restriction (positive coordinates) and mirror
(negative coordinates). The restriction transport is
measure-preserving from the hull product measure. -/
theorem measurePreserving_hullRestr :
    MeasurePreserving (hullRestr J (reflHull J) (hull_subset_self J))
      (Measure.pi fun _ : reflHull J => μG)
      (Measure.pi fun _ : J => μG) := by
  classical
  have hfun : hullRestr J (reflHull J) (hull_subset_self J)
      = (MeasurableEquiv.piCongrLeft (fun _ : J => G) (hullFinsetEquiv J))
        ∘ (Prod.fst ∘ (splitEquiv (hullFinset J))) := by
    funext U j
    show U ⟨j.1, Finset.mem_union_left _ j.2⟩
      = (MeasurableEquiv.piCongrLeft (fun _ : J => G) (hullFinsetEquiv J))
          ((splitEquiv (hullFinset J) U).1) j
    have h2 : (MeasurableEquiv.piCongrLeft (fun _ : J => G)
          (hullFinsetEquiv J)) ((splitEquiv (hullFinset J) U).1)
          ((hullFinsetEquiv J) ((hullFinsetEquiv J).symm j))
        = (splitEquiv (hullFinset J) U).1 ((hullFinsetEquiv J).symm j) :=
      MeasurableEquiv.piCongrLeft_apply_apply _ _ _
    have h3 : (hullFinsetEquiv J) ((hullFinsetEquiv J).symm j) = j :=
      Equiv.apply_symm_apply _ _
    rw [h3] at h2
    rw [h2, splitEquiv_fst]
    rfl
  rw [hfun]
  exact (measurePreserving_piCongrLeft (fun _ : J => μG)
    (hullFinsetEquiv J)).comp (MeasureTheory.measurePreserving_fst.comp
      (measurePreserving_splitEquiv μG (hullFinset J)))

include hJ in
/-- The mirror transport is measure-preserving from the hull
product measure: a coordinate permutation (the link reflection)
composed with per-coordinate inversion on time links — the
corpus's `measurePreserving_mirrorP` pattern. -/
theorem measurePreserving_hullMirror :
    MeasurePreserving (hullMirror J)
      (Measure.pi fun _ : reflHull J => μG)
      (Measure.pi fun _ : J => μG) := by
  classical
  set e := hullMirrorEquiv J hJ with he
  set congrMap : (∀ k : ↥(hullFinset J)ᶜ, G) → ∀ j : J, G :=
    fun v j => v (e j) with hcongr
  set invMap : (∀ j : J, G) → ∀ j : J, G :=
    fun z j => if j.1.2 = 0 then (z j)⁻¹ else z j with hinv
  have hfun : ∀ v : ∀ k : ↥(hullFinset J)ᶜ, G, ∀ j : J,
      (MeasurableEquiv.piCongrLeft (fun _ : J => G) e.symm) v j
        = v (e j) := by
    intro v j
    have h2 : (MeasurableEquiv.piCongrLeft (fun _ : J => G) e.symm) v
          (e.symm (e j)) = v (e j) :=
      MeasurableEquiv.piCongrLeft_apply_apply _ _ _
    have h3 : e.symm (e j) = j := Equiv.symm_apply_apply e j
    rw [h3] at h2
    exact h2
  have hcongrEq : congrMap
      = (MeasurableEquiv.piCongrLeft (fun _ : J => G) e.symm) := by
    funext v j
    exact (hfun v j).symm
  have hcongrMP : MeasurePreserving congrMap
      (Measure.pi fun _ : ↥(hullFinset J)ᶜ => μG)
      (Measure.pi fun _ : J => μG) := by
    rw [hcongrEq]
    exact measurePreserving_piCongrLeft (fun _ : J => μG) e.symm
  have hinvMP : MeasurePreserving invMap
      (Measure.pi fun _ : J => μG) (Measure.pi fun _ : J => μG) := by
    refine measurePreserving_pi
      (f := fun (j : J) (g : G) => if j.1.2 = 0 then g⁻¹ else g)
      (fun _ : J => μG) (fun _ : J => μG) fun j => ?_
    show MeasurePreserving (fun g : G => if j.1.2 = 0 then g⁻¹ else g)
      μG μG
    by_cases hj : j.1.2 = 0
    · rw [show (fun g : G => if j.1.2 = 0 then g⁻¹ else g) = Inv.inv from
        funext fun g => if_pos hj]
      exact Measure.measurePreserving_inv μG
    · rw [show (fun g : G => if j.1.2 = 0 then g⁻¹ else g) = id from
        funext fun g => if_neg hj]
      exact MeasurePreserving.id μG
  have hdecomp : hullMirror J
      = invMap ∘ (congrMap ∘ (Prod.snd ∘ (splitEquiv (hullFinset J)))) := by
    funext U j
    show hullMirror J U j
      = invMap (congrMap ((splitEquiv (hullFinset J) U).2)) j
    have hsnd : (splitEquiv (hullFinset J) U).2
        = fun k : ↥(hullFinset J)ᶜ => U k.1 := splitEquiv_snd _ _
    rw [hsnd]
    by_cases hj : j.1.2 = 0
    · rw [show hullMirror J U j
          = (U ⟨reflLinkZ j.1, reflLinkZ_mem_hull_of_mem j.2⟩)⁻¹ from if_pos hj,
        show invMap (congrMap (fun k : ↥(hullFinset J)ᶜ => U k.1)) j
          = (U ⟨reflLinkZ j.1, reflLinkZ_mem_hull_of_mem j.2⟩)⁻¹ from if_pos hj]
    · rw [show hullMirror J U j
          = U ⟨reflLinkZ j.1, reflLinkZ_mem_hull_of_mem j.2⟩ from if_neg hj,
        show invMap (congrMap (fun k : ↥(hullFinset J)ᶜ => U k.1)) j
          = U ⟨reflLinkZ j.1, reflLinkZ_mem_hull_of_mem j.2⟩ from if_neg hj]
  rw [hdecomp]
  exact hinvMP.comp (hcongrMP.comp
    (MeasureTheory.measurePreserving_snd.comp
      (measurePreserving_splitEquiv μG (hullFinset J))))

end Seats

/-! ## §5. The window integrand: reflected factor is the mirror -/

section Transport

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [MeasurableInv G] [BorelSpace G] [SecondCountableTopology G]
  [PolishSpace G]
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
variable {J : Finset LinkZ} (hJ : ∀ ℓ ∈ J, 0 ≤ ℓ.1 0)

/-- The per-coordinate inversion map on window configurations
(time links inverted), the mirror's second factor. -/
def hullInvMap (J : Finset LinkZ) (z : ∀ j : J, G) : ∀ j : J, G :=
  fun j => if j.1.2 = 0 then (z j)⁻¹ else z j

theorem measurePreserving_hullInvMap :
    MeasurePreserving (hullInvMap J)
      (Measure.pi fun _ : J => μG) (Measure.pi fun _ : J => μG) := by
  refine measurePreserving_pi
    (f := fun (j : J) (g : G) => if j.1.2 = 0 then g⁻¹ else g)
    (fun _ : J => μG) (fun _ : J => μG) fun j => ?_
  show MeasurePreserving (fun g : G => if j.1.2 = 0 then g⁻¹ else g)
    μG μG
  by_cases hj : j.1.2 = 0
  · rw [show (fun g : G => if j.1.2 = 0 then g⁻¹ else g) = Inv.inv from
      funext fun g => if_pos hj]
    exact Measure.measurePreserving_inv μG
  · rw [show (fun g : G => if j.1.2 = 0 then g⁻¹ else g) = id from
      funext fun g => if_neg hj]
    exact MeasurePreserving.id μG

theorem measurableEmbedding_hullInvMap :
    MeasurableEmbedding (hullInvMap (G := G) J) := by
  have hmeas : Measurable (hullInvMap (G := G) J) := by
    rw [measurable_pi_iff]
    intro j
    by_cases hj : j.1.2 = 0
    · have hfun : (fun z : ∀ j : J, G => hullInvMap J z j)
          = fun z => (z j)⁻¹ := funext fun z => if_pos hj
      rw [hfun]
      exact (measurable_pi_apply j).inv
    · have hfun : (fun z : ∀ j : J, G => hullInvMap J z j)
          = fun z => z j := funext fun z => if_neg hj
      rw [hfun]
      exact measurable_pi_apply j
  have hinv : Function.Involutive (hullInvMap (G := G) J) := by
    intro z
    funext j
    by_cases hj : j.1.2 = 0
    · show (if j.1.2 = 0 then ((hullInvMap J z) j)⁻¹ else (hullInvMap J z) j)
        = z j
      rw [if_pos hj, show hullInvMap J z j = (z j)⁻¹ from if_pos hj, inv_inv]
    · show (if j.1.2 = 0 then ((hullInvMap J z) j)⁻¹ else (hullInvMap J z) j)
        = z j
      rw [if_neg hj, show hullInvMap J z j = z j from if_neg hj]
  let e : (∀ j : J, G) ≃ᵐ ∀ j : J, G :=
    { toEquiv := ⟨hullInvMap J, hullInvMap J, hinv, hinv⟩
      measurable_toFun := hmeas
      measurable_invFun := hmeas }
  exact e.measurableEmbedding

/-- The reflected hull restriction is the mirror of the hull
configuration. -/
theorem hullRestr_windowReflConfig (V : ∀ k : reflHull J, G) :
    hullRestr J (reflHull J) (hull_subset_self J)
        (windowReflConfig (reflHull J) (reflLinkZ_mem_reflHull hJ) V)
      = hullMirror J V := by
  funext j
  by_cases hj : j.1.2 = 0
  · show (windowReflConfig (reflHull J) (reflLinkZ_mem_reflHull hJ) V
        ⟨j.1, (hull_subset_self J) j.2⟩)
      = hullMirror J V j
    rw [show windowReflConfig (reflHull J) (reflLinkZ_mem_reflHull hJ) V
          ⟨j.1, (hull_subset_self J) j.2⟩
        = (V ⟨reflLinkZ j.1,
            reflLinkZ_mem_reflHull hJ _ ((hull_subset_self J) j.2)⟩)⁻¹
        from if_pos hj,
      show hullMirror J V j
        = (V ⟨reflLinkZ j.1, reflLinkZ_mem_hull_of_mem j.2⟩)⁻¹ from if_pos hj]
  · show (windowReflConfig (reflHull J) (reflLinkZ_mem_reflHull hJ) V
        ⟨j.1, (hull_subset_self J) j.2⟩)
      = hullMirror J V j
    rw [show windowReflConfig (reflHull J) (reflLinkZ_mem_reflHull hJ) V
          ⟨j.1, (hull_subset_self J) j.2⟩
        = V ⟨reflLinkZ j.1,
            reflLinkZ_mem_reflHull hJ _ ((hull_subset_self J) j.2)⟩
        from if_neg hj,
      show hullMirror J V j
        = V ⟨reflLinkZ j.1, reflLinkZ_mem_hull_of_mem j.2⟩ from if_neg hj]

/-- The window OS integrand, as a function of a hull
configuration. -/
noncomputable def windowIntegrand (J : Finset LinkZ)
    (f : (∀ j : J, G) → ℂ) (V : ∀ k : reflHull J, G) : ℂ :=
  (starRingEnd ℂ) (f (hullMirror J V))
    * f (hullRestr J (reflHull J) (hull_subset_self J) V)

include hJ in
theorem aestronglyMeasurable_windowIntegrand
    (f : (∀ j : J, G) → ℂ)
    (hfA : AEStronglyMeasurable f (Measure.pi fun _ : J => μG)) :
    AEStronglyMeasurable (windowIntegrand J f)
      (Measure.pi fun _ : reflHull J => μG) := by
  have h1 : AEStronglyMeasurable (fun V : ∀ k : reflHull J, G =>
        (starRingEnd ℂ) (f (hullMirror J V)))
      (Measure.pi fun _ : reflHull J => μG) :=
    (RCLike.continuous_conj).comp_aestronglyMeasurable
      (hfA.comp_measurePreserving (measurePreserving_hullMirror μG hJ))
  have h2 : AEStronglyMeasurable (fun V : ∀ k : reflHull J, G =>
        f (hullRestr J (reflHull J) (hull_subset_self J) V))
      (Measure.pi fun _ : reflHull J => μG) :=
    hfA.comp_measurePreserving (measurePreserving_hullRestr μG)
  exact h1.mul h2

include hJ in
/-- AEStronglyMeasurability transfers from the product Haar
measure to any window Gibbs seat (same null sets up to the
Gibbs density and the scalar). -/
theorem aestronglyMeasurable_windowIntegrand_gibbs (β : ℝ)
    (f : (∀ j : J, G) → ℂ)
    (hfA : AEStronglyMeasurable f (Measure.pi fun _ : J => μG)) :
    AEStronglyMeasurable (windowIntegrand J f)
      (windowGibbs μG ρ β (reflHull J)) := by
  have h := aestronglyMeasurable_windowIntegrand μG hJ f hfA
  have h2 : AEStronglyMeasurable (windowIntegrand J f)
      ((Measure.pi fun _ : reflHull J => μG).withDensity
        (fun U => (windowDensity ρ β (reflHull J) U : ℝ≥0∞))) :=
    h.mono_ac (withDensity_absolutelyContinuous _ _)
  have h3 : AEStronglyMeasurable (windowIntegrand J f)
      ((ENNReal.ofReal (windowPartition μG ρ β (reflHull J)))⁻¹ •
        (Measure.pi fun _ : reflHull J => μG).withDensity
          (fun U => (windowDensity ρ β (reflHull J) U : ℝ≥0∞))) :=
    h2.mono_ac (fun s hs => by
      rw [Measure.smul_apply, hs, smul_eq_mul, mul_zero])
  exact h3

/-! ## §6. The transport identity (Tier β machinery, any β) -/

/-- The window OS form is the integral of the window integrand
(the reflected hull restriction is the mirror). -/
theorem windowOSForm_eq_windowIntegrand (β : ℝ)
    (f : (∀ j : J, G) → ℂ) :
    windowOSForm J (reflHull J) (hull_subset_self J)
        (reflLinkZ_mem_reflHull hJ) (windowGibbs μG ρ β (reflHull J)) f
      = ∫ V, windowIntegrand J f V
          ∂(windowGibbs μG ρ β (reflHull J)) := by
  show ∫ V, (starRingEnd ℂ)
        (f (hullRestr J (reflHull J) (hull_subset_self J)
          (windowReflConfig (reflHull J) (reflLinkZ_mem_reflHull hJ) V)))
      * f (hullRestr J (reflHull J) (hull_subset_self J) V)
      ∂(windowGibbs μG ρ β (reflHull J)) = _
  exact integral_congr_ae (ae_of_all _ fun V => by
    simp only [hullRestr_windowReflConfig hJ V, windowIntegrand])

/-- **Transport identity.** For any projective limit `μ` of the
window Gibbs family at coupling `β`, the limit OS form of a
cylinder observable supported on a positive window `J` equals
the window OS form at the reflection-closed hull seat — the
limit's hull marginal is the window seat, by `IsProjectiveLimit`.
No projectivity hypothesis is consumed beyond `hμ` itself. -/
theorem limitOSForm_eq_windowOSForm (β : ℝ)
    (μ : Measure (LinkZ → G))
    (hμ : IsProjectiveLimit μ (windowGibbs μG ρ β))
    (f : (∀ j : J, G) → ℂ)
    (hfA : AEStronglyMeasurable f (Measure.pi fun _ : J => μG)) :
    limitOSForm μ (cylObs J f)
      = windowOSForm J (reflHull J) (hull_subset_self J)
          (reflLinkZ_mem_reflHull hJ) (windowGibbs μG ρ β (reflHull J)) f := by
  classical
  have hΦ : AEStronglyMeasurable (windowIntegrand J f)
      (μ.map (Finset.restrict (reflHull J))) := by
    rw [hμ (reflHull J)]
    exact aestronglyMeasurable_windowIntegrand_gibbs μG ρ hJ β f hfA
  have hmeas : Measurable (Finset.restrict (reflHull J) :
      (LinkZ → G) → ∀ k : reflHull J, G) :=
    measurable_pi_iff.mpr fun k => measurable_pi_apply k.1
  have step1 : ∫ V, windowIntegrand J f V
        ∂(μ.map (Finset.restrict (reflHull J)))
      = ∫ U, windowIntegrand J f (Finset.restrict (reflHull J) U) ∂μ :=
    integral_map hmeas.aemeasurable hΦ
  have hpt : ∀ U : LinkZ → G,
      windowIntegrand J f (Finset.restrict (reflHull J) U)
        = (starRingEnd ℂ) (cylObs J f (reflConfigZ U))
          * cylObs J f U := by
    intro U
    show (starRingEnd ℂ)
          (f (hullMirror J (Finset.restrict (reflHull J) U)))
        * f (hullRestr J (reflHull J) (hull_subset_self J)
            (Finset.restrict (reflHull J) U))
      = (starRingEnd ℂ) (cylObs J f (reflConfigZ U)) * cylObs J f U
    have e1 : hullRestr J (reflHull J) (hull_subset_self J)
          (Finset.restrict (reflHull J) U)
        = (fun j : J => U j.1) := rfl
    have e2 : hullMirror J (Finset.restrict (reflHull J) U)
        = (fun j : J => reflConfigZ U j.1) := by
      funext j
      by_cases hj : j.1.2 = 0
      · show (if j.1.2 = 0
            then ((Finset.restrict (reflHull J) U)
              ⟨reflLinkZ j.1, _⟩)⁻¹
            else (Finset.restrict (reflHull J) U) ⟨reflLinkZ j.1, _⟩)
          = reflConfigZ U j.1
        rw [if_pos hj,
          show reflConfigZ U j.1 = (U (reflLinkZ j.1))⁻¹ from if_pos hj]
        rfl
      · show (if j.1.2 = 0
            then ((Finset.restrict (reflHull J) U)
              ⟨reflLinkZ j.1, _⟩)⁻¹
            else (Finset.restrict (reflHull J) U) ⟨reflLinkZ j.1, _⟩)
          = reflConfigZ U j.1
        rw [if_neg hj,
          show reflConfigZ U j.1 = U (reflLinkZ j.1) from if_neg hj]
        rfl
    rw [e1, e2]
    rfl
  calc limitOSForm μ (cylObs J f)
      = ∫ U, windowIntegrand J f (Finset.restrict (reflHull J) U) ∂μ :=
        integral_congr_ae (ae_of_all _ fun U => (hpt U).symm)
    _ = ∫ V, windowIntegrand J f V
          ∂(μ.map (Finset.restrict (reflHull J))) := step1.symm
    _ = ∫ V, windowIntegrand J f V
          ∂(windowGibbs μG ρ β (reflHull J)) := by
        rw [hμ (reflHull J)]
    _ = windowOSForm J (reflHull J) (hull_subset_self J)
          (reflLinkZ_mem_reflHull hJ) (windowGibbs μG ρ β (reflHull J))
          f :=
        (windowOSForm_eq_windowIntegrand μG ρ hJ β f).symm

/-! ## §7. The finite β = 0 computation on the hull seat -/

/-- **The window OS form at β = 0 is `W * conj W`** — the
integrated Gram criterion's β = 0 content (STATUS §2) on the
window seat: the seat is the product Haar measure, the split
integral factors over the window and its reflection, and the
mirror marginal identifies both factors with `W = ∫ f`. -/
theorem windowOSForm_zero_eq
    (f : (∀ j : J, G) → ℂ)
    (hfA : AEStronglyMeasurable f (Measure.pi fun _ : J => μG)) :
    windowOSForm J (reflHull J) (hull_subset_self J)
        (reflLinkZ_mem_reflHull hJ) (windowGibbs μG ρ 0 (reflHull J)) f
      = (∫ z, f z ∂(Measure.pi fun _ : J => μG))
        * (starRingEnd ℂ) (∫ z, f z ∂(Measure.pi fun _ : J => μG)) := by
  classical
  set s := hullFinset J with hs
  set eJ := hullFinsetEquiv J with heJ
  set eM := hullMirrorEquiv J hJ with heM
  have hseat : windowGibbs μG ρ 0 (reflHull J)
      = Measure.pi (fun _ : reflHull J => μG) := windowGibbs_zero μG ρ _
  -- The integrand, factored through the split.
  have hfact : ∀ V : ∀ k : reflHull J, G,
      windowIntegrand J f V
        = f ((MeasurableEquiv.piCongrLeft (fun _ : J => G) eJ)
              (fun k : s => V k.1))
          * (starRingEnd ℂ) (f (hullInvMap J
              (fun j : J => (fun k : ↥sᶜ => V k.1) (eM j)))) := by
    intro V
    show (starRingEnd ℂ) (f (hullMirror J V))
        * f (hullRestr J (reflHull J) (hull_subset_self J) V) = _
    have er : hullRestr J (reflHull J) (hull_subset_self J) V
        = (MeasurableEquiv.piCongrLeft (fun _ : J => G) eJ)
            (fun k : s => V k.1) := by
      funext j
      have h2 : (MeasurableEquiv.piCongrLeft (fun _ : J => G) eJ)
            (fun k : s => V k.1) (eJ (eJ.symm j))
          = (fun k : s => V k.1) (eJ.symm j) :=
        MeasurableEquiv.piCongrLeft_apply_apply _ _ _
      have h3 : eJ (eJ.symm j) = j := Equiv.apply_symm_apply _ _
      rw [h3] at h2
      rw [h2]
      rfl
    have em : hullMirror J V
        = hullInvMap J (fun j : J => (fun k : ↥sᶜ => V k.1) (eM j)) := by
      funext j
      by_cases hj : j.1.2 = 0
      · show hullMirror J V j = hullInvMap J _ j
        rw [show hullMirror J V j
            = (V ⟨reflLinkZ j.1, reflLinkZ_mem_hull_of_mem j.2⟩)⁻¹ from if_pos hj,
          show hullInvMap J (fun j : J => (fun k : ↥sᶜ => V k.1) (eM j)) j
            = (V ⟨reflLinkZ j.1, reflLinkZ_mem_hull_of_mem j.2⟩)⁻¹ from if_pos hj]
      · show hullMirror J V j = hullInvMap J _ j
        rw [show hullMirror J V j
            = V ⟨reflLinkZ j.1, reflLinkZ_mem_hull_of_mem j.2⟩ from if_neg hj,
          show hullInvMap J (fun j : J => (fun k : ↥sᶜ => V k.1) (eM j)) j
            = V ⟨reflLinkZ j.1, reflLinkZ_mem_hull_of_mem j.2⟩ from if_neg hj]
    rw [er, em, mul_comm]
  -- Assemble: transport to the integrand, change the seat, factor.
  rw [windowOSForm_eq_windowIntegrand μG ρ hJ 0 f, hseat,
    integral_congr_ae (ae_of_all _ hfact),
    integral_pi_split_mul μG s
      (fun v => f ((MeasurableEquiv.piCongrLeft (fun _ : J => G) eJ) v))
      (fun w => (starRingEnd ℂ) (f (hullInvMap J (fun j : J => w (eM j)))))]
  congr 1
  · exact (measurePreserving_piCongrLeft (fun _ : J => μG)
      eJ).integral_comp (MeasurableEquiv.measurableEmbedding _) f
  · -- The mirror factor: conjugate out, then two measure-preserving
    -- transports (congruence, then inversion).
    have hcong : ∀ w : ∀ k : ↥sᶜ, G, ∀ j : J,
        (MeasurableEquiv.piCongrLeft (fun _ : J => G) eM.symm) w j
          = w (eM j) := by
      intro w j
      have h2 : (MeasurableEquiv.piCongrLeft (fun _ : J => G) eM.symm) w
            (eM.symm (eM j)) = w (eM j) :=
        MeasurableEquiv.piCongrLeft_apply_apply _ _ _
      have h3 : eM.symm (eM j) = j := Equiv.symm_apply_apply _ _
      rw [h3] at h2
      exact h2
    calc ∫ w, (starRingEnd ℂ) (f (hullInvMap J (fun j : J => w (eM j))))
          ∂(Measure.pi fun _ : ↥sᶜ => μG)
        = (starRingEnd ℂ) (∫ w, f (hullInvMap J
              ((MeasurableEquiv.piCongrLeft (fun _ : J => G) eM.symm) w))
            ∂(Measure.pi fun _ : ↥sᶜ => μG)) := by
          rw [← integral_conj]
          apply congrArg
          funext w
          exact congrArg (fun z : ∀ j : J, G =>
              (starRingEnd ℂ) (f (hullInvMap J z)))
            (funext fun j => (hcong w j).symm)
      _ = (starRingEnd ℂ) (∫ z, f (hullInvMap J z)
            ∂(Measure.pi fun _ : J => μG)) := by
          congr 1
          exact (measurePreserving_piCongrLeft (fun _ : J => μG)
            eM.symm).integral_comp (MeasurableEquiv.measurableEmbedding _)
            (fun z => f (hullInvMap J z))
      _ = (starRingEnd ℂ) (∫ z, f z
            ∂(Measure.pi fun _ : J => μG)) :=
          congrArg _ ((measurePreserving_hullInvMap μG).integral_comp
            (measurableEmbedding_hullInvMap) f)

/-- **Tier-0 window corollary:** the window OS form at β = 0 is a
nonnegative real. -/
theorem windowOSForm_zero_nonneg
    (f : (∀ j : J, G) → ℂ)
    (hfA : AEStronglyMeasurable f (Measure.pi fun _ : J => μG)) :
    0 ≤ (windowOSForm J (reflHull J) (hull_subset_self J)
        (reflLinkZ_mem_reflHull hJ) (windowGibbs μG ρ 0 (reflHull J))
        f).re
      ∧ (windowOSForm J (reflHull J) (hull_subset_self J)
          (reflLinkZ_mem_reflHull hJ) (windowGibbs μG ρ 0 (reflHull J))
          f).im = 0 := by
  set W := ∫ z, f z ∂(Measure.pi fun _ : J => μG) with hW
  have hform := windowOSForm_zero_eq μG ρ hJ f hfA
  constructor
  · have hre : (windowOSForm J (reflHull J) (hull_subset_self J)
          (reflLinkZ_mem_reflHull hJ) (windowGibbs μG ρ 0 (reflHull J))
          f).re = W.re ^ 2 + W.im ^ 2 := by
      rw [hform]
      simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im]
      ring
    rw [hre]
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  · have him : (windowOSForm J (reflHull J) (hull_subset_self J)
          (reflLinkZ_mem_reflHull hJ) (windowGibbs μG ρ 0 (reflHull J))
          f).im = 0 := by
      rw [hform]
      simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im]
      ring
    exact him

end Transport

/-! ## §8. The two tier headlines -/

section Headlines

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [MeasurableInv G] [BorelSpace G] [SecondCountableTopology G]
  [PolishSpace G]
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- **TIER 0 HEADLINE (unconditional).** MQ3-2's unconditional
β = 0 projective limit measure carries the integrated Gram
criterion's nonnegativity for cylinder observables: the limit
system's OS form of every cylinder observable supported on a
positive window is a nonnegative real. **K-MQ3-TRANSPORT does
not fire at Tier 0.** -/
theorem limitOSForm_zero_nonneg
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    {J : Finset LinkZ} (hJ : ∀ ℓ ∈ J, 0 ≤ ℓ.1 0)
    (f : (∀ j : J, G) → ℂ)
    (hfA : AEStronglyMeasurable f (Measure.pi fun _ : J => μG)) :
    ∃ μ : Measure (LinkZ → G),
      IsProjectiveLimit μ (windowGibbs μG ρ 0)
        ∧ 0 ≤ (limitOSForm μ (cylObs J f)).re
        ∧ (limitOSForm μ (cylObs J f)).im = 0 := by
  obtain ⟨μ, hμ⟩ := exists_isProjectiveLimit_windowGibbs_zero μG ρ hρcont hd
  refine ⟨μ, hμ, ?_, ?_⟩
  · rw [limitOSForm_eq_windowOSForm μG ρ hJ 0 μ hμ f hfA]
    exact (windowOSForm_zero_nonneg μG ρ hJ f hfA).1
  · rw [limitOSForm_eq_windowOSForm μG ρ hJ 0 μ hμ f hfA]
    exact (windowOSForm_zero_nonneg μG ρ hJ f hfA).2

/-- **TIER β HEADLINE (conditional on `WindowGibbsProjective`).**
Under MQ3-2's named hypothesis at coupling `β`, a projective
limit measure exists and the transport identity holds for every
cylinder observable on a positive window; nonnegativity of the
limit form follows from nonnegativity of the window form
(whose positivity at `β ≠ 0` is not claimed — STATUS §4). -/
theorem limitOSForm_eq_windowOSForm_of_projective
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (β : ℝ) (h : WindowGibbsProjective μG ρ β)
    {J : Finset LinkZ} (hJ : ∀ ℓ ∈ J, 0 ≤ ℓ.1 0)
    (f : (∀ j : J, G) → ℂ)
    (hfA : AEStronglyMeasurable f (Measure.pi fun _ : J => μG)) :
    ∃ μ : Measure (LinkZ → G),
      IsProjectiveLimit μ (windowGibbs μG ρ β)
        ∧ limitOSForm μ (cylObs J f)
          = windowOSForm J (reflHull J) (hull_subset_self J)
              (reflLinkZ_mem_reflHull hJ)
              (windowGibbs μG ρ β (reflHull J)) f
        ∧ (0 ≤ (windowOSForm J (reflHull J) (hull_subset_self J)
              (reflLinkZ_mem_reflHull hJ)
              (windowGibbs μG ρ β (reflHull J)) f).re
            → (windowOSForm J (reflHull J) (hull_subset_self J)
                (reflLinkZ_mem_reflHull hJ)
                (windowGibbs μG ρ β (reflHull J)) f).im = 0
            → 0 ≤ (limitOSForm μ (cylObs J f)).re
              ∧ (limitOSForm μ (cylObs J f)).im = 0) := by
  obtain ⟨μ, hμ⟩ := exists_isProjectiveLimit_windowGibbs μG ρ hρcont hd β h
  have hid := limitOSForm_eq_windowOSForm μG ρ hJ β μ hμ f hfA
  exact ⟨μ, hμ, hid, fun hre him => by rw [hid]; exact ⟨hre, him⟩⟩

end Headlines

end ThetLogos
