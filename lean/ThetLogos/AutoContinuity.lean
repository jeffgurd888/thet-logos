import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Topology.Algebra.Group.Neighborhood
import Mathlib.Tactic

/-!
# ThetLogos.AutoContinuity — automatic continuity of measurable homomorphisms (W-1)

Brick **W-1** of the Gate3Wild package, scoped in
`q3-2-gate3wild-scoping-2026-11-06.md` §3 and confirmed as closable
item 4 in `q3-closable-scope-2026-11-08.md`. **NO CLAIM; dials 0/4.**

## What stands here

The classical automatic-continuity theorem, absent from the pinned
Mathlib (v4.35.0-rc3), at the scoped generality:

* **T1** `MonoidHom.continuous_of_measurable` — a measurable
  homomorphism from a locally compact second-countable topological
  group, equipped with a Haar measure, into a second-countable
  topological group is continuous.
* **T2a** `MonoidHom.continuous_of_ae_eq_measurable` — the a.e.
  variant at the same generality, with no extra hypothesis on the
  target: a homomorphism a.e. equal (w.r.t. Haar) to a measurable
  function is continuous (hence measurable, T2a′).
* **T2b** `MonoidHom.continuous_of_aestronglyMeasurable` — the form
  the W-3 assembly consumes: from an `AEStronglyMeasurable` input
  to `Continuous`. Passing from an a.e.-strongly-measurable
  representative to a measurable one uses the pin's
  `StronglyMeasurable.measurable`, which requires
  `[TopologicalSpace.PseudoMetrizableSpace H]`; that side condition is stated on
  T2b's face (the unitary-group target of W-3 satisfies it).

## Route

Steinhaus, not Lusin/Pettis. Measurability is used in exactly one
place (`key_of_measurable_of_ae_eq`): a countable dense set of
right translates of a small identity neighbourhood `V` covers the
target; a fixed compact closed set of positive finite Haar measure
in the source therefore has a positive-measure piece on which the
map lands in a single translate of `V`. Steinhaus
(`MeasureTheory.Measure.div_mem_nhds_one_of_haar_pos_ne_top`, in-pin) turns
that piece's difference set into an identity neighbourhood, and the
homomorphism transports it into `V / V`, which is arranged inside
any prescribed identity neighbourhood (continuity of division at
`(1, 1)`). Continuity at `1` then gives continuity everywhere by
`continuous_of_continuousAt_one` (in-pin). The inner-regularity
side condition of Steinhaus is discharged from Haar regularity on
a second-countable locally compact group
(`MeasureTheory.Measure.regular_of_isMulLeftInvariant`), not assumed.
-/

open Set Filter MeasureTheory Topology
open scoped Pointwise

namespace ThetLogos.AutoContinuity

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-! ## (a) The Steinhaus engine

From the key property — every identity neighbourhood in `H`
contains the image-normalisation of a positive-finite-measure set
in `G` — conclude continuity at `1`. -/

private lemma continuousAt_one_of_key (μ : Measure G) [Measure.IsHaarMeasure μ] {φ : G →* H}
    (hkey : ∀ V : Set H, IsOpen V → (1 : H) ∈ V →
      ∃ (E : Set G) (d : H), MeasurableSet E ∧ 0 < μ E ∧ μ E ≠ ⊤ ∧
        ∀ x ∈ E, φ x * d⁻¹ ∈ V) :
    ContinuousAt φ 1 := by
  -- (a′) Haar regularity on a second-countable locally compact group,
  -- discharging Steinhaus's inner-regularity side condition.
  obtain ⟨K₀, hK₀, hK₀nhd⟩ := exists_compact_mem_nhds (1 : G)
  haveI : μ.Regular :=
    MeasureTheory.Measure.regular_of_isMulLeftInvariant hK₀
      ⟨1, mem_interior_iff_mem_nhds.mpr hK₀nhd⟩ (hK₀.measure_lt_top).ne
  have hpre : ∀ U : Set H, U ∈ 𝓝 (1 : H) → φ ⁻¹' U ∈ 𝓝 (1 : G) := by
    intro U hU
    -- Shrink: continuity of division at `(1, 1)`.
    have hcont : Continuous (fun p : H × H => p.1 / p.2) := continuous_div'
    have hW : (fun p : H × H => p.1 / p.2) ⁻¹' U ∈ 𝓝 ((1, 1) : H × H) := by
      apply hcont.continuousAt.preimage_mem_nhds
      simpa using hU
    obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hW
    set V := interior A ∩ interior B with hVdef
    have hVopen : IsOpen V := isOpen_interior.inter isOpen_interior
    have hV1 : (1 : H) ∈ V :=
      ⟨mem_interior_iff_mem_nhds.mpr hA, mem_interior_iff_mem_nhds.mpr hB⟩
    obtain ⟨E, d, hEmeas, hEpos, hEfin, hEV⟩ := hkey V hVopen hV1
    have hstein : E / E ∈ 𝓝 (1 : G) :=
      MeasureTheory.Measure.div_mem_nhds_one_of_haar_pos_ne_top μ E hEmeas hEpos hEfin
    apply mem_of_superset hstein
    intro x hx
    rw [Set.mem_div] at hx
    obtain ⟨a, haE, b, hbE, rfl⟩ := hx
    have hvaA : φ a * d⁻¹ ∈ A := interior_subset (hEV a haE).1
    have hvbB : φ b * d⁻¹ ∈ B := interior_subset (hEV b hbE).2
    have hpair : (φ a * d⁻¹) / (φ b * d⁻¹) ∈ U := hAB (Set.mk_mem_prod hvaA hvbB)
    have heq : φ a / φ b = (φ a * d⁻¹) / (φ b * d⁻¹) := by
      rw [← div_eq_mul_inv (φ a) d, ← div_eq_mul_inv (φ b) d, div_div_div_cancel_right]
    show φ (a / b) ∈ U
    rw [map_div, heq]
    exact hpair
  show Tendsto φ (𝓝 1) (𝓝 (φ 1))
  rw [map_one]
  exact Filter.tendsto_def.mpr hpre

/-! ## (b) The key property from a measurable representative

`f` is measurable, `T` is a measurable null set, and `φ = f` off
`T`. The case `f = φ`, `T = ∅` is T1; the general case is T2. -/

private lemma key_of_measurable_of_ae_eq (μ : Measure G) [Measure.IsHaarMeasure μ] {φ : G →* H}
    {f : G → H} (hf : Measurable f) {T : Set G} (hT : MeasurableSet T) (hTμ : μ T = 0)
    (hφf : ∀ x ∉ T, φ x = f x) :
    ∀ V : Set H, IsOpen V → (1 : H) ∈ V →
      ∃ (E : Set G) (d : H), MeasurableSet E ∧ 0 < μ E ∧ μ E ≠ ⊤ ∧
        ∀ x ∈ E, φ x * d⁻¹ ∈ V := by
  intro V hVopen hV1
  -- A compact closed set of positive finite measure: the closure of
  -- a compact identity neighbourhood (closed, hence measurable,
  -- without any T2 assumption on `G`).
  obtain ⟨K₀, hK₀, hK₀nhd⟩ := exists_compact_mem_nhds (1 : G)
  set K := closure K₀ with hKdef
  have hKcomp : IsCompact K := hK₀.closure
  have hKmeas : MeasurableSet K := isClosed_closure.measurableSet
  have hKfin : μ K ≠ ⊤ := hKcomp.measure_lt_top.ne
  have hKpos : 0 < μ K :=
    MeasureTheory.Measure.measure_pos_of_nonempty_interior μ
      ⟨1, interior_mono subset_closure
        (mem_interior_iff_mem_nhds.mpr hK₀nhd)⟩
  -- Countable dense set of right translates covering `H`.
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense H
  haveI : Countable D := hDcount.to_subtype
  have hcover : ∀ h : H, ∃ d ∈ D, h * d⁻¹ ∈ V := by
    intro h
    have hopen : IsOpen ((fun x : H => h * x⁻¹) ⁻¹' V) :=
      (continuous_const.mul continuous_inv).isOpen_preimage _ hVopen
    have hne : ((fun x : H => h * x⁻¹) ⁻¹' V).Nonempty :=
      ⟨h, by simpa using hV1⟩
    obtain ⟨d, hdD, hdV⟩ := hDdense.exists_mem_open hopen hne
    exact ⟨d, hdD, hdV⟩
  -- The pieces, indexed by the countable dense set.
  set P : D → Set G := fun d => K ∩ f ⁻¹' {y : H | y * (d : H)⁻¹ ∈ V} with hPdef
  have hPmeas : ∀ d : D, MeasurableSet (P d) := by
    intro d
    apply hKmeas.inter
    apply hf
    -- `{y | y * d⁻¹ ∈ V}` is open, hence measurable.
    have : IsOpen {y : H | y * (d : H)⁻¹ ∈ V} :=
      (continuous_id.mul_const _).isOpen_preimage _ hVopen
    exact this.measurableSet
  have hKsub : K ⊆ ⋃ d : D, P d := by
    intro x hxK
    obtain ⟨d, hdD, hdV⟩ := hcover (f x)
    simp only [mem_iUnion]
    exact ⟨⟨d, hdD⟩, hxK, hdV⟩
  -- Some piece has positive measure.
  obtain ⟨d, hdpos⟩ : ∃ d : D, μ (P d) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have : μ (⋃ d : D, P d) = 0 := measure_iUnion_null hcon
    exact absurd (measure_mono_null hKsub this) (ne_of_gt hKpos)
  refine ⟨P d \ T, (d : H), (hPmeas d).diff hT, ?_, ?_, ?_⟩
  · -- positivity survives removing a null set
    have hdiff : μ (P d \ T) = μ (P d) := measure_sdiff_null hTμ
    rw [hdiff]
    exact pos_iff_ne_zero.mpr hdpos
  · exact ne_top_of_le_ne_top hKfin
      (measure_mono (Set.sdiff_subset.trans inter_subset_left))
  · intro x hx
    have hxP : x ∈ P d := hx.1
    have hxT : x ∉ T := hx.2
    rw [hφf x hxT]
    exact hxP.2

/-! ## (c)+(d) The frozen theorems -/

/-- **T1 — automatic continuity.** A measurable homomorphism from a
locally compact second-countable topological group (with Haar
measure) into a second-countable topological group is continuous. -/
theorem MonoidHom.continuous_of_measurable (μ : Measure G) [Measure.IsHaarMeasure μ]
    {φ : G →* H} (hφ : Measurable φ) : Continuous φ :=
  continuous_of_continuousAt_one φ <|
    continuousAt_one_of_key μ <|
      key_of_measurable_of_ae_eq μ hφ MeasurableSet.empty (by simp)
        (fun x _ => rfl)

/-- **T2a — the a.e. variant.** A homomorphism a.e. equal (w.r.t.
Haar) to a measurable function is continuous. No extra hypothesis
on the target. -/
theorem MonoidHom.continuous_of_ae_eq_measurable (μ : Measure G) [Measure.IsHaarMeasure μ]
    {φ : G →* H} {f : G → H} (hf : Measurable f) (h : (φ : G → H) =ᵐ[μ] f) :
    Continuous φ := by
  -- A measurable null superset of the disagreement set.
  have hbad : μ {x : G | φ x ≠ f x} = 0 := by
    have hmem : {x : G | φ x = f x} ∈ ae μ := h
    rw [mem_ae_iff] at hmem
    have : ({x : G | φ x = f x}ᶜ) = {x : G | φ x ≠ f x} := by
      ext x; simp
    rwa [this] at hmem
  obtain ⟨T, hsub, hTmeas, hTμ⟩ := exists_measurable_superset_of_null hbad
  apply continuous_of_continuousAt_one φ
  apply continuousAt_one_of_key μ
  apply key_of_measurable_of_ae_eq μ hf hTmeas hTμ
  intro x hxT
  by_contra hne
  exact hxT (hsub hne)

/-- **T2a′.** Under the T2a hypotheses, the homomorphism is itself
measurable. -/
theorem MonoidHom.measurable_of_ae_eq_measurable (μ : Measure G) [Measure.IsHaarMeasure μ]
    {φ : G →* H} {f : G → H} (hf : Measurable f) (h : (φ : G → H) =ᵐ[μ] f) :
    Measurable φ :=
  (MonoidHom.continuous_of_ae_eq_measurable μ hf h).measurable

/-- **T2b — the assembly form.** A homomorphism whose underlying
function is `AEStronglyMeasurable` w.r.t. Haar is continuous.
The `[TopologicalSpace.PseudoMetrizableSpace H]` side condition is what the pin's
`StronglyMeasurable.measurable` requires to produce a measurable
representative; it holds for the unitary-group targets this form
is consumed at. -/
theorem MonoidHom.continuous_of_aestronglyMeasurable (μ : Measure G) [Measure.IsHaarMeasure μ]
    [TopologicalSpace.PseudoMetrizableSpace H] {φ : G →* H}
    (hφ : AEStronglyMeasurable (φ : G → H) μ) :
    Continuous φ :=
  MonoidHom.continuous_of_ae_eq_measurable μ hφ.measurable_mk hφ.ae_eq_mk

end ThetLogos.AutoContinuity
