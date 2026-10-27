/-
# ThetLogos.PlaneCrossingBeta2 — Brick β2-1b: the β² expansion
of `layerKernel` 𝒜 at general (G, ρ)

**Fences, up front.** NO CLAIM. Parts of the Clay Yang–Mills
statement closed by this module: **0**. β2 (`𝒜 ⪰ 0`) and
(H-PF) at general (G, ρ) remain **L+ / open**: this module is
an *expansion* theorem about 𝒜's β-dependence, and **no
positivity conclusion at any β > 0 follows from it** — the
module says so again at its headline. N = 2 is fenced **out**
(the cross-term collapse needs 3 ≤ N; with the corpus's even
N this is N ≥ 4): at N = 2 there are extra paired cross terms
(β2-1a computed them genuinely (u, u′)-dependent).

## The question and the answer

At the seat (S₃, std), β2-1a computed the O(β²) form κ₂ of 𝒜
and found it a *constant* kernel, (1/16)·J₆: its
(u, u′)-dependent part vanished identically, because
E[χ(W)²] = 1 for every column word W at that seat. This module
proves the vanishing is a **theorem at general (G, ρ)**, with
**no self-duality hypothesis**: the mechanism is Haar
uniformity of the column word.

- Same column: for fixed far stratum value, the word
  `W = α_c · (u′ α_{σc}⁻¹ u⁻¹)` is a right translate of `α_c`,
  hence Haar-uniform. Every one-column moment is the
  corresponding Haar moment of `G` — a (u, u′)-free constant.
  In particular E[χ(W)²] = m₂ := ∫ (tr ρ)² dμG for *every*
  word, and E[(Re χ(W))²] = q₂ := ∫ (Re tr ρ)² dμG.
- Distinct columns (3 ≤ N): some site lies in exactly one
  column's site pair (the crossed matching would force
  1 or 2 ≡ 0 in ZMod N). Conditioning on the other
  coordinates, that site's integral of Re χ(word) is the
  constant e₁ := ∫ Re tr ρ dμG — the analytic form of the
  scoping memo's P₀-collapse — so E[r_P r_Q] = e₁².

Consequently the β² coefficient of 𝒜 is the closed form
`K₂ = (M·(1 − 2e₁/d + q₂/d²) + M(M−1)·(1 − 2e₁/d + e₁²/d²))/2`
(M = 3N³ columns), manifestly (u, u′)-independent: **𝒜's
(u, u′)-dependence is O(β³)**. The κ₂ criterion is exact at
the level of the Haar integral: κ₂ ≡ 0 iff m₂ = 0 (m₂ is
real, proved below). Classically m₂ = mult(𝟙 ⊂ ρ⊗ρ) — for
irreducible ρ, κ₂ ≡ 0 iff ρ is not self-dual — but that
identification is character orthogonality for ρ⊗ρ, which the
corpus does not own at general (G, ρ); it is recorded here as
prose, and the Lean criterion stops at m₂.

Conventions follow the corpus: ρ is a bare `MonoidHom` into a
unitary group, and the moment theory carries the explicit
hypothesis `hρcont : Continuous fun g => repMatrix ρ g`,
exactly as in the Haar-intertwiner section of `LatticeGauge`.
-/

import ThetLogos.PlaneCrossingCube
import ThetLogos.PlaneCrossingColumn
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.Exponential

namespace ThetLogos

open Finset MeasureTheory

section Setup

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- The character of `ρ`: the trace of the represented group
element. -/
noncomputable def charFn (g : G) : ℂ := Matrix.trace (repMatrix ρ g)

@[simp]
theorem charFn_one : charFn ρ 1 = (d : ℂ) := by
  rw [charFn, repMatrix_one, Matrix.trace_one, Fintype.card_fin]

/-- Cyclicity of the character: `χ(ab) = χ(ba)`. -/
theorem charFn_mul_comm (a b : G) : charFn ρ (a * b) = charFn ρ (b * a) := by
  rw [charFn, charFn, repMatrix_mul, repMatrix_mul, Matrix.trace_mul_comm]

/-- The character at the inverse is the conjugate:
`χ(g⁻¹) = conj (χ g)` (unitarity). -/
theorem charFn_inv (g : G) : charFn ρ g⁻¹ = starRingEnd ℂ (charFn ρ g) := by
  have hstar : ∀ z : ℂ, starRingEnd ℂ z = star z :=
    fun z => (congrFun RCLike.star_def z).symm
  rw [charFn, repMatrix_inv, hstar]
  simp only [Matrix.trace, Matrix.diag, Matrix.star_apply, charFn, star_sum]

/-- The trace bound: `‖χ g‖ ≤ d` (diagonal entries of a unitary
matrix have norm ≤ 1). -/
theorem norm_charFn_le (g : G) : ‖charFn ρ g‖ ≤ (d : ℝ) := by
  show ‖Matrix.trace (repMatrix ρ g)‖ ≤ (d : ℝ)
  rw [Matrix.trace]
  calc ‖∑ i : Fin d, Matrix.diag (repMatrix ρ g) i‖
      ≤ ∑ i : Fin d, ‖Matrix.diag (repMatrix ρ g) i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ =>
          abs_entry_of_mem_unitaryGroup (repMatrix_mem ρ g) i i
    _ = (d : ℝ) := by simp

/-- Measurability of the character (under the corpus's standing
continuity hypothesis on `ρ`). -/
theorem measurable_charFn (hρcont : Continuous fun g : G => repMatrix ρ g) :
    Measurable (charFn ρ) := by
  show Measurable fun g : G => ∑ i : Fin d, repMatrix ρ g i i
  apply Finset.measurable_sum
  intro i _
  exact (measurable_pi_apply i).comp ((measurable_pi_apply i).comp
    hρcont.measurable)

/-- Integrability of the character against a Haar probability
measure: continuous and bounded by `d`. -/
theorem integrable_charFn (μG : Measure G) [IsProbabilityMeasure μG]
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    Integrable (charFn ρ) μG :=
  Integrable.of_bound (measurable_charFn ρ hρcont).aestronglyMeasurable
    (d : ℝ) (Filter.Eventually.of_forall fun g => norm_charFn_le ρ g)

/-- **The column word** at column `(c, ν)`: the one-layer word
`α c * u' ℓ * (α (σ_ν c))⁻¹ * (u ℓ)⁻¹`, with
`ℓ = layerLinkOf c ν hν` and `σ_ν c = layerShift ν hν c`. -/
def colWord (u u' : LayerLink N → G) (c : LayerSite N) (ν : Fin 4)
    (hν : ν ≠ 0) (α : LayerSite N → G) : G :=
  α c * u' (layerLinkOf c ν hν) * (α (layerShift ν hν c))⁻¹
    * (u (layerLinkOf c ν hν))⁻¹

/-- **The column density**: the Wilson density of the column
word — `plaquetteDensity` of the layer configuration at
`(c, ν)`, read through the word (`plaquetteDensity_layerConfig_word`). -/
noncomputable def colDens (u u' : LayerLink N → G) (c : LayerSite N)
    (ν : Fin 4) (hν : ν ≠ 0) (α : LayerSite N → G) : ℝ :=
  wordDensity ρ (colWord u u' c ν hν α)

theorem colDens_eq (u u' : LayerLink N → G) (c : LayerSite N)
    (ν : Fin 4) (hν : ν ≠ 0) (α : LayerSite N → G) :
    colDens ρ u u' c ν hν α
      = 1 - (charFn ρ (colWord u u' c ν hν α)).re / (d : ℝ) :=
  rfl

/-- Column densities lie in `[0, 2]`: `|Re χ| ≤ d`. -/
theorem colDens_nonneg (u u' : LayerLink N → G) (c : LayerSite N)
    (ν : Fin 4) (hν : ν ≠ 0) (α : LayerSite N → G) :
    0 ≤ colDens ρ u u' c ν hν α := by
  rw [colDens_eq]
  have h1 : (charFn ρ (colWord u u' c ν hν α)).re ≤ (d : ℝ) :=
    re_trace_le_of_mem_unitaryGroup (repMatrix_mem ρ _)
  have h2 : -(d : ℝ) ≤ (charFn ρ (colWord u u' c ν hν α)).re :=
    neg_re_trace_le_of_mem_unitaryGroup (repMatrix_mem ρ _)
  by_cases hd : (d : ℝ) = 0
  · have hd0 : d = 0 := by exact_mod_cast hd
    subst hd0
    simp [charFn]
  · have hdpos : (0 : ℝ) < d := lt_of_le_of_ne (Nat.cast_nonneg d) (Ne.symm hd)
    rw [sub_nonneg, div_le_one hdpos]
    exact h1

theorem colDens_le_two (u u' : LayerLink N → G) (c : LayerSite N)
    (ν : Fin 4) (hν : ν ≠ 0) (α : LayerSite N → G) :
    colDens ρ u u' c ν hν α ≤ 2 := by
  rw [colDens_eq]
  have h2 : -(d : ℝ) ≤ (charFn ρ (colWord u u' c ν hν α)).re :=
    neg_re_trace_le_of_mem_unitaryGroup (repMatrix_mem ρ _)
  by_cases hd : (d : ℝ) = 0
  · have hd0 : d = 0 := by exact_mod_cast hd
    subst hd0
    simp [charFn]
  · have hdpos : (0 : ℝ) < d := lt_of_le_of_ne (Nat.cast_nonneg d) (Ne.symm hd)
    have h3 : (-1 : ℝ) ≤ (charFn ρ (colWord u u' c ν hν α)).re / (d : ℝ) := by
      rw [le_div_iff₀ hdpos]
      calc (-1 : ℝ) * (d : ℝ) = -(d : ℝ) := by ring
        _ ≤ (charFn ρ (colWord u u' c ν hν α)).re := h2
    linarith

/-- The column word only reads the stratum at its two sites:
the base `c` and the shifted site `σ_ν c`. -/
theorem colWord_eq_of_agree (u u' : LayerLink N → G) (c : LayerSite N)
    (ν : Fin 4) (hν : ν ≠ 0) {α β : LayerSite N → G}
    (h1 : α c = β c) (h2 : α (layerShift ν hν c) = β (layerShift ν hν c)) :
    colWord u u' c ν hν α = colWord u u' c ν hν β := by
  rw [colWord, colWord, h1, h2]

/-- The β-free layer density sum: `layerAction ρ β = β * this`,
definitionally. -/
noncomputable def layerDensSum (α : LayerSite N → G)
    (u u' : LayerLink N → G) : ℝ :=
  ∑ c : LayerSite N, ∑ ν ∈ Finset.Ioi (0 : Fin 4),
    plaquetteDensity (torusShift N) ρ (layerConfig α u u') c.1 0 ν

theorem layerAction_eq (β : ℝ) (α : LayerSite N → G)
    (u u' : LayerLink N → G) :
    layerAction ρ β α u u' = β * layerDensSum ρ α u u' := rfl

/-- The layer's columns as one index type: a base site and a
spatial direction. (Its `Fintype` instance is the ambient
product/subtype one, so cardinalities below are the sums'
own.) -/
abbrev LayerColumn (N : ℕ) : Type := LayerSite N × {ν : Fin 4 // ν ≠ 0}

instance : Fintype (LayerColumn N) := by classical infer_instance

/-- The column density, indexed by a column. -/
noncomputable def colDensC (u u' : LayerLink N → G) (P : LayerColumn N)
    (α : LayerSite N → G) : ℝ :=
  colDens ρ u u' P.1 P.2.1 P.2.2 α

/-- The number of columns, as a real: `M = 3 · N³` in value
(kept symbolic as the cardinality). -/
noncomputable def colCount (N : ℕ) [NeZero N] : ℝ :=
  (Fintype.card (LayerColumn N) : ℝ)

theorem layerDensSum_eq_sum_columns (hN : Even N)
    (α : LayerSite N → G) (u u' : LayerLink N → G) :
    layerDensSum ρ α u u'
      = ∑ P : LayerColumn N, colDensC ρ u u' P α := by
  have hIoi : (Finset.univ.filter (fun ν : Fin 4 => ν ≠ 0))
      = Finset.Ioi (0 : Fin 4) := by
    ext ν
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ioi]
    exact Fin.pos_iff_ne_zero.symm
  have step : ∀ c : LayerSite N,
      (∑ ν ∈ Finset.Ioi (0 : Fin 4),
        plaquetteDensity (torusShift N) ρ (layerConfig α u u') c.1 0 ν)
      = ∑ ν : {ν : Fin 4 // ν ≠ 0}, colDens ρ u u' c ν.1 ν.2 α := by
    intro c
    refine Finset.sum_bij
      (fun ν hν => (⟨ν, Fin.pos_iff_ne_zero.mp (Finset.mem_Ioi.mp hν)⟩ :
        {ν : Fin 4 // ν ≠ 0})) ?_ ?_ ?_ ?_
    · intro ν _
      exact Finset.mem_univ _
    · intro ν₁ _ ν₂ _ hij
      exact Subtype.ext_iff.mp hij
    · intro P _
      exact ⟨P.1, Finset.mem_Ioi.mpr (Fin.pos_iff_ne_zero.mpr P.2),
        Subtype.ext rfl⟩
    · intro ν hν
      exact plaquetteDensity_layerConfig_word ρ hN α u u' c ν
        (Fin.pos_iff_ne_zero.mp (Finset.mem_Ioi.mp hν))
  show (∑ c : LayerSite N, ∑ ν ∈ Finset.Ioi (0 : Fin 4),
        plaquetteDensity (torusShift N) ρ (layerConfig α u u') c.1 0 ν)
      = ∑ P : LayerColumn N, colDens ρ u u' P.1 P.2.1 P.2.2 α
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun c _ => step c

/-- The density sum is bounded: `0 ≤ layerDensSum ≤ 2M`. -/
theorem layerDensSum_nonneg (hN : Even N) (α : LayerSite N → G)
    (u u' : LayerLink N → G) : 0 ≤ layerDensSum ρ α u u' := by
  rw [layerDensSum_eq_sum_columns ρ hN α u u']
  exact Finset.sum_nonneg fun P _ =>
    colDens_nonneg ρ u u' P.1 P.2.1 P.2.2 α

theorem layerDensSum_le (hN : Even N) (α : LayerSite N → G)
    (u u' : LayerLink N → G) :
    layerDensSum ρ α u u' ≤ 2 * colCount N := by
  rw [layerDensSum_eq_sum_columns ρ hN α u u']
  calc ∑ P : LayerColumn N, colDensC ρ u u' P α
      ≤ ∑ _P : LayerColumn N, (2 : ℝ) :=
        Finset.sum_le_sum fun P _ =>
          colDens_le_two ρ u u' P.1 P.2.1 P.2.2 α
    _ = 2 * colCount N := by
        rw [Finset.sum_const, nsmul_eq_mul]
        unfold colCount
        rw [← Finset.card_univ]
        ring

/-- The stratum of one layer, as a measure space: the product
Haar probability over layer sites. -/
noncomputable abbrev stratumMeasure (μG : Measure G) :
    Measure (LayerSite N → G) := Measure.pi fun _ : LayerSite N => μG

end Setup

section PiLemmas

variable {ι : Type*} [Fintype ι] {G : Type*} [Group G]
  [MeasurableSpace G] (μG : Measure G) [IsProbabilityMeasure μG]

/-- **One-coordinate marginal**: integrating a function of one
coordinate of a product probability measure is integrating it
over that coordinate's measure. -/
theorem integral_eval_coord {F : G → ℂ} (hF : AEStronglyMeasurable F μG)
    (s : ι) :
    ∫ α : ι → G, F (α s) ∂(Measure.pi fun _ : ι => μG) = ∫ g, F g ∂μG := by
  have hmp : MeasurePreserving (fun α : ι → G => α s)
      (Measure.pi fun _ : ι => μG) μG :=
    measurePreserving_eval (fun _ : ι => μG) s
  have hF' : AEStronglyMeasurable F
      ((Measure.pi fun _ : ι => μG).map (fun α : ι → G => α s)) := by
    rw [hmp.map_eq]
    exact hF
  have key := (integral_map (φ := fun α : ι → G => α s) (f := F)
    (measurable_pi_apply s : Measurable fun α : ι → G => α s).aemeasurable hF').symm
  rwa [hmp.map_eq] at key

/-- **Two-coordinate iterated integral**: integrating a function
of two distinct coordinates of a product probability measure
is the iterated integral over the two coordinates. -/
theorem integral_two_coord [DecidableEq ι] {s t : ι} (hst : s ≠ t)
    {F : G → G → ℂ} (hF : Integrable (Function.uncurry F) (μG.prod μG)) :
    ∫ α : ι → G, F (α s) (α t) ∂(Measure.pi fun _ : ι => μG)
      = ∫ a, ∫ b, F a b ∂μG ∂μG := by
  classical
  set e : Fin 2 → ι := ![s, t] with he
  have hinj : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [e, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, hst, Ne.symm hst]
  have step1 : ∫ α : ι → G, F (α s) (α t) ∂(Measure.pi fun _ : ι => μG)
      = ∫ β : Fin 2 → G, F (β 0) (β 1)
          ∂(Measure.pi fun _ : Fin 2 => μG) := by
    rw [← integral_comp_emb μG e hinj (fun β => F (β 0) (β 1))]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro α
    show F (α s) (α t) = F ((α ∘ e) 0) ((α ∘ e) 1)
    simp only [Function.comp_apply, he, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
  have step2 : ∫ β : Fin 2 → G, F (β 0) (β 1)
        ∂(Measure.pi fun _ : Fin 2 => μG)
      = ∫ z : G × G, F z.1 z.2 ∂(μG.prod μG) := by
    rw [← (measurePreserving_piFinTwo (fun _ : Fin 2 => μG)).integral_comp
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => G)).measurableEmbedding
      (fun z : G × G => F z.1 z.2)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro β
    show F (β 0) (β 1)
      = F ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => G) β).1)
          ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => G) β).2)
    rw [MeasurableEquiv.piFinTwo_apply]
  rw [step1, step2]
  exact integral_prod _ hF

end PiLemmas

section PiLemmasReal

variable {ι : Type*} [Fintype ι] {G : Type*} [Group G]
  [MeasurableSpace G] [MeasurableInv G] (μG : Measure G)
  [IsProbabilityMeasure μG]

/-- Real-valued one-coordinate marginal (the complex proof,
copied with `ℝ` in place of `ℂ`). -/
theorem integral_eval_coord_real {F : G → ℝ}
    (hF : AEStronglyMeasurable F μG) (s : ι) :
    ∫ α : ι → G, F (α s) ∂(Measure.pi fun _ : ι => μG)
      = ∫ g, F g ∂μG := by
  have hmp : MeasurePreserving (fun α : ι → G => α s)
      (Measure.pi fun _ : ι => μG) μG :=
    measurePreserving_eval (fun _ : ι => μG) s
  have hF' : AEStronglyMeasurable F
      ((Measure.pi fun _ : ι => μG).map (fun α : ι → G => α s)) := by
    rw [hmp.map_eq]
    exact hF
  have key := (integral_map (φ := fun α : ι → G => α s) (f := F)
    (measurable_pi_apply s : Measurable fun α : ι → G => α s).aemeasurable
    hF').symm
  rwa [hmp.map_eq] at key

/-- Real-valued marginal over a coordinate restriction (the
corpus proof of `integral_pi_restrict`, copied with `ℝ`). -/
theorem integral_pi_restrict_real [DecidableEq ι] (s : Finset ι)
    (f : (↥s → G) → ℝ) :
    ∫ U : ι → G, f (fun ℓ : ↥s => U ℓ.1) ∂(Measure.pi fun _ : ι => μG)
      = ∫ v, f v ∂(Measure.pi fun _ : ↥s => μG) := by
  have step : ∫ U : ι → G, f (fun ℓ : ↥s => U ℓ.1)
        ∂(Measure.pi fun _ : ι => μG)
      = ∫ z : (↥s → G) × (↥sᶜ → G), f z.1
          ∂((Measure.pi fun _ : ↥s => μG).prod
            (Measure.pi fun _ : ↥sᶜ => μG)) := by
    rw [← (measurePreserving_splitEquiv μG s).integral_comp
      (splitEquiv s).measurableEmbedding]
    apply integral_congr_ae
    filter_upwards with U
    show f (fun ℓ : ↥s => U ℓ.1) = f (splitEquiv s U).1
    rw [splitEquiv_fst]
  rw [step]
  have h1 : ∫ z : (↥s → G) × (↥sᶜ → G), f z.1
        ∂((Measure.pi fun _ : ↥s => μG).prod
          (Measure.pi fun _ : ↥sᶜ => μG))
      = (∫ v, f v ∂(Measure.pi fun _ : ↥s => μG))
        * (∫ _w : ↥sᶜ → G, (1 : ℝ) ∂(Measure.pi fun _ : ↥sᶜ => μG)) := by
    rw [← integral_prod_mul f (fun _ => (1 : ℝ))]
    apply integral_congr_ae
    filter_upwards with z
    exact (mul_one (f z.1)).symm
  rw [h1, integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
    one_smul, mul_one]

/-- Real-valued pi-measure transport along an embedding (the
corpus proof of `integral_comp_emb`, copied with `ℝ`). -/
theorem integral_comp_emb_real {J : Type*} [Fintype J] [DecidableEq ι]
    (e : J → ι) (he : Function.Injective e) (F : (J → G) → ℝ) :
    (∫ a : ι → G, F (a ∘ e) ∂(Measure.pi fun _ : ι => μG))
      = ∫ α : J → G, F α ∂(Measure.pi fun _ : J => μG) := by
  classical
  have hcomp : ∀ a : ι → G, a ∘ e
      = (fun ℓ : ↥(Finset.image e Finset.univ) => a ℓ.1)
        ∘ (embEquiv e he) := by
    intro a
    funext j
    show a (e j) = a ((embEquiv e he) j).1
    rw [embEquiv_apply]
  rw [integral_congr_ae (ae_of_all _ fun a => by rw [hcomp a])]
  rw [integral_pi_restrict_real μG (Finset.image e Finset.univ)
    (fun v => F (v ∘ (embEquiv e he)))]
  have hE : ∀ α : J → G,
      (MeasurableEquiv.piCongrLeft
        (fun _ : ↥(Finset.image e Finset.univ) => G)
        (embEquiv e he)) α ∘ (embEquiv e he) = α := by
    intro α
    funext j
    exact MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : ↥(Finset.image e Finset.univ) => G)
      (embEquiv e he) α j
  have hmp := MeasureTheory.measurePreserving_piCongrLeft
    (μ := fun _ : ↥(Finset.image e Finset.univ) => μG)
    (f := embEquiv e he)
  rw [← hmp.integral_comp
    (MeasurableEquiv.piCongrLeft
      (fun _ : ↥(Finset.image e Finset.univ) => G)
      (embEquiv e he)).measurableEmbedding
    (fun v => F (v ∘ (embEquiv e he)))]
  apply integral_congr_ae
  exact ae_of_all _ fun α => congrArg F (hE α)

/-- Real-valued two-coordinate iterated integral. -/
theorem integral_two_coord_real [DecidableEq ι] {s t : ι} (hst : s ≠ t)
    {F : G → G → ℝ} (hF : Integrable (Function.uncurry F) (μG.prod μG)) :
    ∫ α : ι → G, F (α s) (α t) ∂(Measure.pi fun _ : ι => μG)
      = ∫ a, ∫ b, F a b ∂μG ∂μG := by
  classical
  set e : Fin 2 → ι := ![s, t] with he
  have hinj : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [e, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, hst, Ne.symm hst]
  have step1 : ∫ α : ι → G, F (α s) (α t) ∂(Measure.pi fun _ : ι => μG)
      = ∫ β : Fin 2 → G, F (β 0) (β 1)
          ∂(Measure.pi fun _ : Fin 2 => μG) := by
    rw [← integral_comp_emb_real μG e hinj (fun β => F (β 0) (β 1))]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro α
    show F (α s) (α t) = F ((α ∘ e) 0) ((α ∘ e) 1)
    simp only [Function.comp_apply, he, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
  have step2 : ∫ β : Fin 2 → G, F (β 0) (β 1)
        ∂(Measure.pi fun _ : Fin 2 => μG)
      = ∫ z : G × G, F z.1 z.2 ∂(μG.prod μG) := by
    rw [← (measurePreserving_piFinTwo (fun _ : Fin 2 => μG)).integral_comp
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => G)).measurableEmbedding
      (fun z : G × G => F z.1 z.2)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro β
    show F (β 0) (β 1)
      = F ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => G) β).1)
          ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => G) β).2)
    rw [MeasurableEquiv.piFinTwo_apply]
  rw [step1, step2]
  exact integral_prod _ hF

end PiLemmasReal

section Moments

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- The first Haar moment of the character, as a real number:
`e₁ = ∫ Re χ`. -/
noncomputable def e1 : ℝ := ∫ g, (charFn ρ g).re ∂μG

/-- The second complex Haar moment of the character:
`m₂ = ∫ χ²`. (Proved real below.) -/
noncomputable def m2 : ℂ := ∫ g, (charFn ρ g) ^ 2 ∂μG

/-- The second absolute Haar moment: `a₂ = ∫ ‖χ‖²`. -/
noncomputable def a2 : ℝ := ∫ g, ‖charFn ρ g‖ ^ 2 ∂μG

/-- The second real Haar moment: `q₂ = ∫ (Re χ)²`. -/
noncomputable def q2 : ℝ := ∫ g, ((charFn ρ g).re) ^ 2 ∂μG

/-- The first β-coefficient of `𝒜`: `∫ layerDensSum`. -/
noncomputable def betaCoeff1 (u u' : LayerLink N → G) : ℝ :=
  ∫ α, layerDensSum ρ α u u' ∂(Measure.pi fun _ : LayerSite N => μG)

/-- The second β-coefficient of `𝒜`: `∫ layerDensSum² / 2`
(so `𝒜 = 1 - β·betaCoeff1 + β²·betaCoeff2 + O(β³)`). -/
noncomputable def betaCoeff2 (u u' : LayerLink N → G) : ℝ :=
  ∫ α, (layerDensSum ρ α u u') ^ 2 / 2
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- The character is continuous under the corpus's standing
continuity hypothesis on `ρ`. -/
theorem continuous_charFn (hρcont : Continuous fun g : G => repMatrix ρ g) :
    Continuous (charFn ρ) := by
  show Continuous fun g : G => ∑ i : Fin d, repMatrix ρ g i i
  exact continuous_finsetSum _ fun i _ =>
    (continuous_apply i).comp ((continuous_apply i).comp hρcont)

/-- The shifted site's underlying function is the torus shift. -/
theorem layerShift_coe (ν : Fin 4) (hν : ν ≠ 0) (c : LayerSite N) :
    (layerShift ν hν c).1 = torusShift N ν c.1 := rfl

/-- The shifted site is never the base site (any even `N ≥ 2`:
the shifted coordinate differs by `1 ≠ 0` in `ZMod N`). -/
theorem layerShift_ne_self (hN : Even N) (ν : Fin 4) (hν : ν ≠ 0)
    (c : LayerSite N) : layerShift ν hν c ≠ c := by
  intro h
  have h2 : (layerShift ν hν c).1 ν = c.1 ν := by rw [h]
  rw [layerShift_coe, torusShift_apply_coord] at h2
  simp only [Pi.single_eq_same] at h2
  have h4 : (1 : ZMod N) = 0 := by
    have h2' : (1 : ZMod N) + c.1 ν = 0 + c.1 ν := by
      rw [zero_add]; exact h2
    exact add_right_cancel_iff.mp h2'
  have h5 : N ∣ 1 :=
    (CharP.cast_eq_zero_iff (ZMod N) N 1).mp (by
      rw [Nat.cast_one]; exact h4)
  exact Nat.not_even_one (Nat.dvd_one.mp h5 ▸ hN)

/-- `|Re χ g| ≤ d`. -/
theorem abs_re_charFn_le (g : G) : |(charFn ρ g).re| ≤ (d : ℝ) :=
  abs_le.mpr ⟨neg_re_trace_le_of_mem_unitaryGroup (repMatrix_mem ρ g),
    re_trace_le_of_mem_unitaryGroup (repMatrix_mem ρ g)⟩

/-- The column word, as a function of the stratum, is
measurable. -/
theorem measurable_colWord (u u' : LayerLink N → G) (c : LayerSite N)
    (ν : Fin 4) (hν : ν ≠ 0) :
    Measurable fun α : LayerSite N → G => colWord u u' c ν hν α := by
  show Measurable fun α : LayerSite N → G =>
    α c * u' (layerLinkOf c ν hν) * (α (layerShift ν hν c))⁻¹
      * (u (layerLinkOf c ν hν))⁻¹
  exact ((((continuous_apply (A := fun _ : LayerSite N => G) c).mul
    continuous_const).mul
    (continuous_apply (A := fun _ : LayerSite N => G)
      (layerShift ν hν c)).inv).mul continuous_const).measurable

/-- The character of the column word is integrable over the
stratum (bounded by `d`). -/
theorem integrable_word_charFn (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (c : LayerSite N) (ν : Fin 4) (hν : ν ≠ 0) :
    Integrable (fun α : LayerSite N → G =>
      charFn ρ (colWord u u' c ν hν α))
      (Measure.pi fun _ : LayerSite N => μG) :=
  Integrable.of_bound
    ((measurable_charFn ρ hρcont).comp
      (measurable_colWord u u' c ν hν)).aestronglyMeasurable
    (d : ℝ) (Filter.Eventually.of_forall fun α => norm_charFn_le ρ _)

/-- A column density is integrable over the stratum (bounded
by `2`). -/
theorem integrable_colDens (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (c : LayerSite N) (ν : Fin 4) (hν : ν ≠ 0) :
    Integrable (fun α : LayerSite N → G => colDens ρ u u' c ν hν α)
      (Measure.pi fun _ : LayerSite N => μG) := by
  have hmeas : Measurable fun α : LayerSite N → G =>
      colDens ρ u u' c ν hν α := by
    show Measurable fun α : LayerSite N → G =>
      1 - (charFn ρ (colWord u u' c ν hν α)).re / (d : ℝ)
    exact measurable_const.sub
      ((Complex.measurable_re.comp ((measurable_charFn ρ hρcont).comp
        (measurable_colWord u u' c ν hν))).div_const _)
  refine Integrable.of_bound hmeas.aestronglyMeasurable (2 : ℝ)
    (Filter.Eventually.of_forall fun α => ?_)
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [colDens_nonneg ρ u u' c ν hν α],
    colDens_le_two ρ u u' c ν hν α⟩

/-- Integrability of a one-column moment over `G × G`: the
uncurried word moment is bounded, because the character is. -/
theorem integrable_uncurry_word (hρcont : Continuous fun g : G => repMatrix ρ g)
    {F : ℂ → ℂ} (hFcont : Continuous F) {C : ℝ}
    (hFC : ∀ z : ℂ, ‖z‖ ≤ (d : ℝ) → ‖F z‖ ≤ C) (X Y : G) :
    Integrable (Function.uncurry fun a b : G =>
      F (charFn ρ (b * X * a⁻¹ * Y))) (μG.prod μG) := by
  have h1 : Measurable fun p : G × G => p.2 * X :=
    measurable_snd.mul measurable_const
  have h2 : Measurable fun p : G × G => (p.2 * X) * p.1⁻¹ :=
    h1.mul measurable_fst.inv
  have h3 : Measurable fun p : G × G => ((p.2 * X) * p.1⁻¹) * Y :=
    h2.mul measurable_const
  refine Integrable.of_bound ?_ C
    (Filter.Eventually.of_forall fun p => hFC _ (norm_charFn_le ρ _))
  exact (hFcont.measurable.comp
    ((measurable_charFn ρ hρcont).comp h3)).aestronglyMeasurable

/-- The real version of the uncurried integrability. -/
theorem integrable_uncurry_word_re
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    {F : ℝ → ℝ} (hFcont : Continuous F) {C : ℝ}
    (hFC : ∀ x : ℝ, ‖x‖ ≤ (d : ℝ) → ‖F x‖ ≤ C) (X Y : G) :
    Integrable (Function.uncurry fun a b : G =>
      F ((charFn ρ (b * X * a⁻¹ * Y)).re)) (μG.prod μG) := by
  have h1 : Measurable fun p : G × G => p.2 * X :=
    measurable_snd.mul measurable_const
  have h2 : Measurable fun p : G × G => (p.2 * X) * p.1⁻¹ :=
    h1.mul measurable_fst.inv
  have h3 : Measurable fun p : G × G => ((p.2 * X) * p.1⁻¹) * Y :=
    h2.mul measurable_const
  have h4 : Measurable fun p : G × G =>
      F ((charFn ρ (((p.2 * X) * p.1⁻¹) * Y)).re) :=
    hFcont.measurable.comp (Complex.measurable_re.comp
      ((measurable_charFn ρ hρcont).comp h3))
  refine Integrable.of_bound h4.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun p => ?_)
  exact hFC _ (by rw [Real.norm_eq_abs]; exact abs_re_charFn_le ρ _)

/-- **Same-column moment, complex form.** Every one-column
moment of the character is the corresponding Haar moment of
`G`: the word is a right translate of the base coordinate,
hence Haar-uniform. No hypothesis on `ρ` beyond continuity. -/
theorem integral_word_moment (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    {F : ℂ → ℂ} (hFcont : Continuous F) {C : ℝ}
    (hFC : ∀ z : ℂ, ‖z‖ ≤ (d : ℝ) → ‖F z‖ ≤ C)
    (u u' : LayerLink N → G) (c : LayerSite N) (ν : Fin 4) (hν : ν ≠ 0) :
    ∫ α : LayerSite N → G, F (charFn ρ (colWord u u' c ν hν α))
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ g, F (charFn ρ g) ∂μG := by
  classical
  have h2 := integral_two_coord μG
    (s := layerShift ν hν c) (t := c) (layerShift_ne_self hN ν hν c)
    (F := fun a b => F (charFn ρ (b * u' (layerLinkOf c ν hν)
      * a⁻¹ * (u (layerLinkOf c ν hν))⁻¹)))
    (integrable_uncurry_word ρ μG hρcont hFcont hFC
      (u' (layerLinkOf c ν hν)) ((u (layerLinkOf c ν hν))⁻¹))
  refine h2.trans ?_
  have hin : ∀ a : G, ∫ b, F (charFn ρ (b * u' (layerLinkOf c ν hν)
        * a⁻¹ * (u (layerLinkOf c ν hν))⁻¹)) ∂μG
      = ∫ g, F (charFn ρ g) ∂μG := by
    intro a
    have e1 : ∫ b, F (charFn ρ (b * u' (layerLinkOf c ν hν)
          * a⁻¹ * (u (layerLinkOf c ν hν))⁻¹)) ∂μG
        = ∫ b, F (charFn ρ (b * (u' (layerLinkOf c ν hν)
          * a⁻¹ * (u (layerLinkOf c ν hν))⁻¹))) ∂μG := by
      apply integral_congr_ae
      filter_upwards with b
      congr 2
      simp only [mul_assoc]
    rw [e1]
    exact integral_mul_right_eq_self (fun g => F (charFn ρ g)) _
  calc ∫ a, ∫ b, F (charFn ρ (b * u' (layerLinkOf c ν hν)
          * a⁻¹ * (u (layerLinkOf c ν hν))⁻¹)) ∂μG ∂μG
      = ∫ _a, ∫ g, F (charFn ρ g) ∂μG ∂μG :=
        integral_congr_ae (Filter.Eventually.of_forall hin)
    _ = ∫ g, F (charFn ρ g) ∂μG := by simp [integral_const]

/-- **Same-column moment, real form.** -/
theorem integral_word_moment_re (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    {F : ℝ → ℝ} (hFcont : Continuous F) {C : ℝ}
    (hFC : ∀ x : ℝ, ‖x‖ ≤ (d : ℝ) → ‖F x‖ ≤ C)
    (u u' : LayerLink N → G) (c : LayerSite N) (ν : Fin 4) (hν : ν ≠ 0) :
    ∫ α : LayerSite N → G, F ((charFn ρ (colWord u u' c ν hν α)).re)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ g, F ((charFn ρ g).re) ∂μG := by
  classical
  have h2 := integral_two_coord_real μG
    (s := layerShift ν hν c) (t := c) (layerShift_ne_self hN ν hν c)
    (F := fun a b => F ((charFn ρ (b * u' (layerLinkOf c ν hν)
      * a⁻¹ * (u (layerLinkOf c ν hν))⁻¹)).re))
    (integrable_uncurry_word_re ρ μG hρcont hFcont hFC
      (u' (layerLinkOf c ν hν)) ((u (layerLinkOf c ν hν))⁻¹))
  refine h2.trans ?_
  have hin : ∀ a : G, ∫ b, F ((charFn ρ (b * u' (layerLinkOf c ν hν)
        * a⁻¹ * (u (layerLinkOf c ν hν))⁻¹)).re) ∂μG
      = ∫ g, F ((charFn ρ g).re) ∂μG := by
    intro a
    have e1 : ∫ b, F ((charFn ρ (b * u' (layerLinkOf c ν hν)
          * a⁻¹ * (u (layerLinkOf c ν hν))⁻¹)).re) ∂μG
        = ∫ b, F ((charFn ρ (b * (u' (layerLinkOf c ν hν)
          * a⁻¹ * (u (layerLinkOf c ν hν))⁻¹))).re) ∂μG := by
      apply integral_congr_ae
      filter_upwards with b
      congr 2
      simp only [mul_assoc]
    rw [e1]
    exact integral_mul_right_eq_self (fun g => F ((charFn ρ g).re)) _
  calc ∫ a, ∫ b, F ((charFn ρ (b * u' (layerLinkOf c ν hν)
          * a⁻¹ * (u (layerLinkOf c ν hν))⁻¹)).re) ∂μG ∂μG
      = ∫ _a, ∫ g, F ((charFn ρ g).re) ∂μG ∂μG :=
        integral_congr_ae (Filter.Eventually.of_forall hin)
    _ = ∫ g, F ((charFn ρ g).re) ∂μG := by simp [integral_const]

/-- **(S2) First moment of the character over a column:**
`∫ χ(word) = ∫ χ` — a (u, u′)-free constant. -/
theorem integral_colChar (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (c : LayerSite N) (ν : Fin 4) (hν : ν ≠ 0) :
    ∫ α : LayerSite N → G, charFn ρ (colWord u u' c ν hν α)
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ g, charFn ρ g ∂μG :=
  integral_word_moment ρ μG hN hρcont continuous_id (C := (d : ℝ))
    (fun z hz => hz) u u' c ν hν

/-- **(S2) First moment of a column density:**
`∫ dens = 1 - e₁/d` — a (u, u′)-free constant. -/
theorem integral_colDens (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (c : LayerSite N) (ν : Fin 4) (hν : ν ≠ 0) :
    ∫ α : LayerSite N → G, colDens ρ u u' c ν hν α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = 1 - e1 ρ μG / (d : ℝ) := by
  have hI := integrable_word_charFn ρ μG hρcont u u' c ν hν
  have hIre : Integrable (fun α : LayerSite N → G =>
      (charFn ρ (colWord u u' c ν hν α)).re)
      (Measure.pi fun _ : LayerSite N => μG) := hI.re
  have step1 : ∫ α : LayerSite N → G, colDens ρ u u' c ν hν α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ α : LayerSite N → G,
          (1 - (charFn ρ (colWord u u' c ν hν α)).re / (d : ℝ))
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
    integral_congr_ae (Filter.Eventually.of_forall fun α =>
      colDens_eq ρ u u' c ν hν α)
  have step2 : ∫ α : LayerSite N → G,
        (1 - (charFn ρ (colWord u u' c ν hν α)).re / (d : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = 1 - (∫ α : LayerSite N → G,
          (charFn ρ (colWord u u' c ν hν α)).re
          ∂(Measure.pi fun _ : LayerSite N => μG)) / (d : ℝ) := by
    have hdiv : (fun α : LayerSite N → G =>
          (1 - (charFn ρ (colWord u u' c ν hν α)).re / (d : ℝ)))
        = fun α : LayerSite N → G =>
          1 - (d : ℝ)⁻¹ * (charFn ρ (colWord u u' c ν hν α)).re := by
      funext α
      rw [div_eq_inv_mul]
    rw [hdiv, integral_sub (integrable_const (1 : ℝ)) (hIre.const_mul _),
      integral_const_mul]
    congr 1
    · simp [integral_const]
    · rw [div_eq_inv_mul]
  have step3 : ∫ α : LayerSite N → G,
        (charFn ρ (colWord u u' c ν hν α)).re
        ∂(Measure.pi fun _ : LayerSite N => μG) = e1 ρ μG := by
    have h1 : ∫ α : LayerSite N → G,
          (charFn ρ (colWord u u' c ν hν α)).re
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = (∫ α : LayerSite N → G, charFn ρ (colWord u u' c ν hν α)
            ∂(Measure.pi fun _ : LayerSite N => μG)).re :=
      integral_re hI
    rw [h1, integral_colChar ρ μG hN hρcont u u' c ν hν]
    exact (integral_re (integrable_charFn ρ μG hρcont)).symm
  rw [step1, step2, step3]

/-- **(S2) The first β-coefficient is closed and
(u, u′)-independent:** `betaCoeff1 = M · (1 - e₁/d)`. -/
theorem betaCoeff1_closed (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    betaCoeff1 ρ μG u u' = colCount N * (1 - e1 ρ μG / (d : ℝ)) := by
  unfold betaCoeff1
  rw [integral_congr_ae (Filter.Eventually.of_forall fun α =>
    layerDensSum_eq_sum_columns ρ hN α u u')]
  rw [integral_finsetSum]
  · refine (Finset.sum_congr rfl fun P _ =>
      integral_colDens ρ μG hN hρcont u u' P.1 P.2.1 P.2.2).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    unfold colCount
    rw [← Finset.card_univ]
  · intro P _
    exact integrable_colDens ρ μG hρcont u u' P.1 P.2.1 P.2.2

/-- The pointwise identity behind `q₂`:
`(Re z)² = (‖z‖² + Re(z²))/2`. -/
theorem re_sq_eq (z : ℂ) :
    (z.re) ^ 2 = (‖z‖ ^ 2 + RCLike.re (z ^ 2)) / 2 := by
  have h1 : ‖z‖ ^ 2 = (z.re) ^ 2 + (z.im) ^ 2 := by
    have h := Complex.normSq_apply z
    rw [Complex.normSq_eq_norm_sq] at h
    rw [h]
    ring
  have h2 : RCLike.re (z ^ 2) = (z.re) ^ 2 - (z.im) ^ 2 := by
    show (z ^ 2).re = (z.re) ^ 2 - (z.im) ^ 2
    rw [pow_two, Complex.mul_re]
    ring
  rw [h1, h2]
  ring

/-- **(S3) Same-column second moment, complex:**
`∫ χ(word)² = m₂` — for *every* word, at *every* seat.
This is the general-(G, ρ) form of β2-1a's seat observation
`E[χ(W)²] = 1 ∀W`: the common value is the Haar moment
`m₂`, constant whether or not it vanishes. -/
theorem integral_colChar_sq (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (c : LayerSite N) (ν : Fin 4) (hν : ν ≠ 0) :
    ∫ α : LayerSite N → G, (charFn ρ (colWord u u' c ν hν α)) ^ 2
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = m2 ρ μG :=
  integral_word_moment ρ μG hN hρcont (F := fun z : ℂ => z ^ 2)
    (by exact continuous_id.pow 2)
    (C := (d : ℝ) ^ 2)
    (fun z hz => by
      show ‖z ^ 2‖ ≤ (d : ℝ) ^ 2
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg z) hz 2) u u' c ν hν

/-- **(S3) Same-column second moment, real:**
`∫ (Re χ(word))² = q₂`. -/
theorem integral_colReSq (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (c : LayerSite N) (ν : Fin 4) (hν : ν ≠ 0) :
    ∫ α : LayerSite N → G, ((charFn ρ (colWord u u' c ν hν α)).re) ^ 2
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = q2 ρ μG :=
  integral_word_moment_re ρ μG hN hρcont (F := fun x : ℝ => x ^ 2)
    (by exact continuous_id.pow 2)
    (C := (d : ℝ) ^ 2)
    (fun x hx => by
      show ‖x ^ 2‖ ≤ (d : ℝ) ^ 2
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg x) hx 2) u u' c ν hν

/-- **(S3)** `q₂ = (a₂ + Re m₂)/2`, from the pointwise
identity integrated over `G`. -/
theorem q2_eq (hρcont : Continuous fun g : G => repMatrix ρ g) :
    q2 ρ μG = (a2 ρ μG + (m2 ρ μG).re) / 2 := by
  have hI2 : Integrable (fun g => (charFn ρ g) ^ 2) μG :=
    Integrable.of_bound
      (((measurable_charFn ρ hρcont).pow_const 2)).aestronglyMeasurable
      ((d : ℝ) ^ 2) (Filter.Eventually.of_forall fun g => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_charFn_le ρ g) 2)
  have hIn : Integrable (fun g => ‖charFn ρ g‖ ^ 2) μG :=
    Integrable.of_bound
      (((continuous_norm.pow 2).comp
        (continuous_charFn ρ hρcont)).measurable).aestronglyMeasurable
      ((d : ℝ) ^ 2) (Filter.Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 2)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_charFn_le ρ g) 2)
  have key : ∀ g, ((charFn ρ g).re) ^ 2
      = (1 / 2) * (‖charFn ρ g‖ ^ 2 + RCLike.re ((charFn ρ g) ^ 2)) := by
    intro g
    rw [re_sq_eq]
    ring
  rw [show (m2 ρ μG).re = RCLike.re (m2 ρ μG) from rfl]
  unfold q2 a2 m2
  rw [integral_congr_ae (Filter.Eventually.of_forall key),
    integral_const_mul, integral_add hIn hI2.re, integral_re hI2]
  ring

/-- **(S3) Same-column absolute second moment:**
`∫ ‖χ(word)‖² = a₂`. -/
theorem integral_colNormSq (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (c : LayerSite N) (ν : Fin 4) (hν : ν ≠ 0) :
    ∫ α : LayerSite N → G, ‖charFn ρ (colWord u u' c ν hν α)‖ ^ 2
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = a2 ρ μG := by
  have hpt2 : ∀ z : ℂ, ‖z‖ ^ 2 = 2 * (z.re) ^ 2 - RCLike.re (z ^ 2) := by
    intro z
    have h := re_sq_eq z
    linarith [h]
  have hI2pi : Integrable (fun α : LayerSite N → G =>
        (charFn ρ (colWord u u' c ν hν α)) ^ 2)
      (Measure.pi fun _ : LayerSite N => μG) :=
    Integrable.of_bound
      (((measurable_charFn ρ hρcont).comp
        (measurable_colWord u u' c ν hν)).pow_const 2).aestronglyMeasurable
      ((d : ℝ) ^ 2) (Filter.Eventually.of_forall fun α => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_charFn_le ρ _) 2)
  have hIre2pi : Integrable (fun α : LayerSite N → G =>
        ((charFn ρ (colWord u u' c ν hν α)).re) ^ 2)
      (Measure.pi fun _ : LayerSite N => μG) :=
    Integrable.of_bound
      ((Complex.measurable_re.comp ((measurable_charFn ρ hρcont).comp
        (measurable_colWord u u' c ν hν))).pow_const 2).aestronglyMeasurable
      ((d : ℝ) ^ 2) (Filter.Eventually.of_forall fun α => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_re_charFn_le ρ _) 2)
  calc ∫ α : LayerSite N → G, ‖charFn ρ (colWord u u' c ν hν α)‖ ^ 2
          ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ α : LayerSite N → G, (2 * ((charFn ρ
            (colWord u u' c ν hν α)).re) ^ 2
          - RCLike.re ((charFn ρ (colWord u u' c ν hν α)) ^ 2))
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_congr_ae (Filter.Eventually.of_forall fun α => hpt2 _)
    _ = 2 * (∫ α : LayerSite N → G,
            ((charFn ρ (colWord u u' c ν hν α)).re) ^ 2
            ∂(Measure.pi fun _ : LayerSite N => μG))
          - (∫ α : LayerSite N → G,
            RCLike.re ((charFn ρ (colWord u u' c ν hν α)) ^ 2)
            ∂(Measure.pi fun _ : LayerSite N => μG)) := by
        rw [integral_sub (hIre2pi.const_mul 2) hI2pi.re,
          integral_const_mul]
    _ = 2 * q2 ρ μG - (m2 ρ μG).re := by
        rw [integral_colReSq ρ μG hN hρcont u u' c ν hν]
        congr 1
        have h1 : ∫ α : LayerSite N → G,
              RCLike.re ((charFn ρ (colWord u u' c ν hν α)) ^ 2)
              ∂(Measure.pi fun _ : LayerSite N => μG)
            = (∫ α : LayerSite N → G,
                (charFn ρ (colWord u u' c ν hν α)) ^ 2
                ∂(Measure.pi fun _ : LayerSite N => μG)).re :=
          integral_re hI2pi
        rw [h1, integral_colChar_sq ρ μG hN hρcont u u' c ν hν]
    _ = a2 ρ μG := by
        rw [q2_eq ρ μG hρcont]
        ring

/-- **(S4) The single-link form κ₂** of the scoping memo: the
`(u, u′)`-dependent part of `𝒜`'s β² coefficient, as a
double Haar integral of the squared character of the
one-link word `a * u' * b⁻¹ * u⁻¹`. -/
noncomputable def kappa2 (u u' : G) : ℝ :=
  (1 / (4 * (d : ℝ) ^ 2)) * (∫ a, ∫ b,
    (charFn ρ (a * u' * b⁻¹ * u⁻¹)) ^ 2 ∂μG ∂μG).re

/-- **(S4) κ₂ is a constant kernel.** Its (u, u′)-dependent
part vanishes identically at general (G, ρ), with **no
hypothesis** — in particular no self-duality: inversion,
then right translation, then left translation successively
strip `b`, `u⁻¹`, and `a * u'` from the word. -/
theorem kappa2_eq_const (u u' : G) :
    kappa2 ρ μG u u' = (1 / (4 * (d : ℝ) ^ 2)) * (m2 ρ μG).re := by
  have hin : ∀ a : G, ∫ b, (charFn ρ (a * u' * b⁻¹ * u⁻¹)) ^ 2 ∂μG
      = ∫ g, (charFn ρ g) ^ 2 ∂μG := by
    intro a
    have e1 : ∫ b, (charFn ρ (a * u' * b⁻¹ * u⁻¹)) ^ 2 ∂μG
        = ∫ b, (charFn ρ (a * u' * b * u⁻¹)) ^ 2 ∂μG :=
      integral_inv_eq_self (fun w => (charFn ρ (a * u' * w * u⁻¹)) ^ 2) μG
    have e2 : ∫ b, (charFn ρ (a * u' * b * u⁻¹)) ^ 2 ∂μG
        = ∫ b, (charFn ρ ((a * u') * (b * u⁻¹))) ^ 2 ∂μG := by
      apply integral_congr_ae
      filter_upwards with b
      rw [show a * u' * b * u⁻¹ = (a * u') * (b * u⁻¹)
        from mul_assoc _ _ _]
    have e3 : ∫ b, (charFn ρ ((a * u') * (b * u⁻¹))) ^ 2 ∂μG
        = ∫ b, (charFn ρ ((a * u') * b)) ^ 2 ∂μG :=
      integral_mul_right_eq_self
        (fun w => (charFn ρ ((a * u') * w)) ^ 2) (u⁻¹)
    have e4 : ∫ b, (charFn ρ ((a * u') * b)) ^ 2 ∂μG
        = ∫ g, (charFn ρ g) ^ 2 ∂μG :=
      integral_mul_left_eq_self (fun w => (charFn ρ w) ^ 2) (a * u')
    rw [e1, e2, e3, e4]
  unfold kappa2 m2
  rw [integral_congr_ae (Filter.Eventually.of_forall hin)]
  simp [integral_const]

/-- **(S4)** `m₂` is real: inversion invariance plus
`χ(g⁻¹) = conj (χ g)`. -/
theorem m2_real : starRingEnd ℂ (m2 ρ μG) = m2 ρ μG := by
  have e1 : starRingEnd ℂ (m2 ρ μG)
      = ∫ g, starRingEnd ℂ ((charFn ρ g) ^ 2) ∂μG := by
    have h := (integral_conj (μ := μG)
      (f := fun g => (charFn ρ g) ^ 2)).symm
    simpa [m2] using h
  have e2 : ∫ g, starRingEnd ℂ ((charFn ρ g) ^ 2) ∂μG
      = ∫ g, (charFn ρ g⁻¹) ^ 2 ∂μG := by
    apply integral_congr_ae
    filter_upwards with g
    rw [map_pow, ← charFn_inv]
  have e3 : ∫ g, (charFn ρ g⁻¹) ^ 2 ∂μG = m2 ρ μG :=
    integral_inv_eq_self (fun g => (charFn ρ g) ^ 2) μG
  rw [e1, e2, e3]

/-- **(S4) The vanishing criterion, exact at the level of
the Haar integral:** `κ₂ ≡ 0 ↔ m₂ = 0`. Classically
`m₂ = mult(𝟙 ⊂ ρ ⊗ ρ)` — for irreducible `ρ`, `κ₂ ≡ 0`
iff `ρ` is not self-dual — but that identification is
character orthogonality for `ρ ⊗ ρ`, which the corpus does
not own at general (G, ρ); the Lean criterion stops at
`m₂`, exactly. **No positivity conclusion at any β > 0
follows from anything in this section.** -/
theorem kappa2_eq_zero_iff :
    (∀ u u' : G, kappa2 ρ μG u u' = 0) ↔ m2 ρ μG = 0 := by
  constructor
  · intro h
    by_cases hd : d = 0
    · have hz : ∀ g, charFn ρ g = 0 := by
        intro g
        subst hd
        simp [charFn, Matrix.trace]
      unfold m2
      simp [hz]
    · have hdpos : (0 : ℝ) < (d : ℝ) :=
        by exact_mod_cast Nat.pos_of_ne_zero hd
      have h0 := h 1 1
      rw [kappa2_eq_const] at h0
      have hne : (1 : ℝ) / (4 * (d : ℝ) ^ 2) ≠ 0 :=
        div_ne_zero one_ne_zero
          (ne_of_gt (mul_pos (by norm_num) (pow_pos hdpos 2)))
      have hre : (m2 ρ μG).re = 0 := by
        rcases mul_eq_zero.mp h0 with h1 | h1
        · exact absurd h1 hne
        · exact h1
      have him : (m2 ρ μG).im = 0 := by
        have hr := m2_real ρ μG
        have hci : (starRingEnd ℂ (m2 ρ μG)).im
            = -((m2 ρ μG).im) := Complex.conj_im _
        rw [hr] at hci
        linarith [hci]
      exact Complex.ext hre him
  · intro h u u'
    rw [kappa2_eq_const, h]
    simp

/-- The character vanishes identically in dimension `0`. -/
theorem charFn_eq_zero (hd : d = 0) (g : G) : charFn ρ g = 0 := by
  subst hd
  simp [charFn, Matrix.trace]

/-- **(S5 infrastructure)** The real character of a column:
`colRe ρ u u' P α = Re χ(word_P α)`. -/
noncomputable def colRe (u u' : LayerLink N → G) (P : LayerColumn N)
    (α : LayerSite N → G) : ℝ :=
  (charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)).re

theorem measurable_colRe (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P : LayerColumn N) :
    Measurable fun α : LayerSite N → G => colRe ρ u u' P α :=
  Complex.measurable_re.comp ((measurable_charFn ρ hρcont).comp
    (measurable_colWord u u' P.1 P.2.1 P.2.2))

theorem measurable_colDens (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (c : LayerSite N) (ν : Fin 4) (hν : ν ≠ 0) :
    Measurable fun α : LayerSite N → G => colDens ρ u u' c ν hν α := by
  show Measurable fun α : LayerSite N → G =>
    1 - (charFn ρ (colWord u u' c ν hν α)).re / (d : ℝ)
  exact measurable_const.sub
    ((Complex.measurable_re.comp ((measurable_charFn ρ hρcont).comp
      (measurable_colWord u u' c ν hν))).div_const _)

theorem colDensC_eq (u u' : LayerLink N → G) (P : LayerColumn N)
    (α : LayerSite N → G) :
    colDensC ρ u u' P α = 1 - colRe ρ u u' P α / (d : ℝ) :=
  colDens_eq ρ u u' P.1 P.2.1 P.2.2 α

theorem integrable_colRe (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P : LayerColumn N) :
    Integrable (fun α : LayerSite N → G => colRe ρ u u' P α)
      (Measure.pi fun _ : LayerSite N => μG) :=
  Integrable.of_bound
    (measurable_colRe ρ hρcont u u' P).aestronglyMeasurable
    (d : ℝ) (Filter.Eventually.of_forall fun α => by
      rw [Real.norm_eq_abs]
      exact abs_re_charFn_le ρ _)

/-- The marginal of a column's real character is `e₁`. -/
theorem integral_colRe (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P : LayerColumn N) :
    ∫ α : LayerSite N → G, colRe ρ u u' P α
        ∂(Measure.pi fun _ : LayerSite N => μG) = e1 ρ μG := by
  have h1 : ∫ α : LayerSite N → G, colRe ρ u u' P α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = (∫ α : LayerSite N → G, charFn ρ (colWord u u' P.1 P.2.1 P.2.2 α)
          ∂(Measure.pi fun _ : LayerSite N => μG)).re :=
    integral_re (integrable_word_charFn ρ μG hρcont u u' P.1 P.2.1 P.2.2)
  rw [h1, integral_colChar ρ μG hN hρcont u u' P.1 P.2.1 P.2.2]
  exact (integral_re (integrable_charFn ρ μG hρcont)).symm

/-- One Haar integral used repeatedly below: integrating
`Re χ(g · K)` over `g` gives `e₁` (right translation). -/
theorem integral_re_charFn_mul_right
    (hρcont : Continuous fun g : G => repMatrix ρ g) (K : G) :
    ∫ g, (charFn ρ (g * K)).re ∂μG = e1 ρ μG := by
  have hI : Integrable (fun g => charFn ρ (g * K)) μG :=
    Integrable.of_bound
      (((measurable_charFn ρ hρcont).comp
        ((continuous_id.mul continuous_const).measurable)).aestronglyMeasurable)
      (d : ℝ) (Filter.Eventually.of_forall fun g => norm_charFn_le ρ _)
  have h1 : ∫ g, (charFn ρ (g * K)).re ∂μG
      = (∫ g, charFn ρ (g * K) ∂μG).re := integral_re hI
  rw [h1, integral_mul_right_eq_self (fun g => charFn ρ g) K]
  exact (integral_re (integrable_charFn ρ μG hρcont)).symm

noncomputable instance : DecidableEq (LayerSite N) := Classical.decEq _

noncomputable instance : DecidableEq (LayerColumn N) := Classical.decEq _

/-- The two sites a column reads. -/
noncomputable def colSites (P : LayerColumn N) : Finset (LayerSite N) :=
  {P.1, layerShift P.2.1 P.2.2 P.1}

theorem mem_colSites {P : LayerColumn N} {i : LayerSite N} :
    i ∈ colSites P ↔ i = P.1 ∨ i = layerShift P.2.1 P.2.2 P.1 := by
  simp [colSites]

/-- Columns in the same direction at the same base have the
same shift: the sites determine the direction. -/
theorem layerShift_inj_dir (hN : Even N) {ν₁ ν₂ : Fin 4}
    (h₁ : ν₁ ≠ 0) (h₂ : ν₂ ≠ 0) (c : LayerSite N)
    (h : layerShift ν₁ h₁ c = layerShift ν₂ h₂ c) : ν₁ = ν₂ := by
  have h2 : (layerShift ν₁ h₁ c).1 ν₁ = (layerShift ν₂ h₂ c).1 ν₁ := by
    rw [h]
  rw [layerShift_coe, layerShift_coe, torusShift_apply_coord,
    torusShift_apply_coord] at h2
  simp only [Pi.single_eq_same, Pi.single_apply] at h2
  by_cases hν : ν₁ = ν₂
  · exact hν
  · rw [if_neg hν, zero_add] at h2
    have h4 : (1 : ZMod N) = 0 := by
      have h2' : (1 : ZMod N) + c.1 ν₁ = 0 + c.1 ν₁ := by
        rw [zero_add]; exact h2
      exact add_right_cancel_iff.mp h2'
    have h5 : N ∣ 1 :=
      (CharP.cast_eq_zero_iff (ZMod N) N 1).mp (by
        rw [Nat.cast_one]; exact h4)
    exact absurd (Nat.dvd_one.mp h5 ▸ hN) Nat.not_even_one

/-- A double shift never returns to the base site when
`3 ≤ N`: the displaced coordinate is `1` or `2`, both
nonzero in `ZMod N`. -/
theorem layerShift_comp_ne (hN3 : 3 ≤ N) {ν₁ ν₂ : Fin 4}
    (h₁ : ν₁ ≠ 0) (h₂ : ν₂ ≠ 0) (c : LayerSite N) :
    layerShift ν₁ h₁ (layerShift ν₂ h₂ c) ≠ c := by
  intro h
  have h2 : (layerShift ν₁ h₁ (layerShift ν₂ h₂ c)).1 ν₁ = c.1 ν₁ := by
    rw [h]
  rw [layerShift_coe, torusShift_apply_coord, layerShift_coe,
    torusShift_apply_coord] at h2
  simp only [Pi.single_eq_same, Pi.single_apply] at h2
  have key : (1 : ZMod N) + (if ν₁ = ν₂ then (1 : ZMod N) else 0) = 0 := by
    have h2' : ((1 : ZMod N) + (if ν₁ = ν₂ then (1 : ZMod N) else 0))
        + c.1 ν₁ = 0 + c.1 ν₁ := by
      rw [zero_add]
      calc ((1 : ZMod N) + (if ν₁ = ν₂ then (1 : ZMod N) else 0))
            + c.1 ν₁
          = 1 + ((if ν₁ = ν₂ then (1 : ZMod N) else 0) + c.1 ν₁) := by
            ring
        _ = c.1 ν₁ := h2
    exact add_right_cancel_iff.mp h2'
  by_cases hν : ν₁ = ν₂
  · rw [if_pos hν] at key
    have h5 : N ∣ 2 :=
      (CharP.cast_eq_zero_iff (ZMod N) N 2).mp (by
        have h6 : ((2 : ℕ) : ZMod N) = (1 : ZMod N) + 1 := by
          norm_num
        rw [h6]
        exact key)
    have := Nat.le_of_dvd (by norm_num) h5
    omega
  · rw [if_neg hν] at key
    simp only [add_zero] at key
    have h5 : N ∣ 1 :=
      (CharP.cast_eq_zero_iff (ZMod N) N 1).mp (by
        rw [Nat.cast_one]; exact key)
    have := Nat.le_of_dvd (by norm_num) h5
    omega

/-- **(S5) Site combinatorics:** for `3 ≤ N`, a column is
determined by its two sites. -/
theorem colSites_eq_imp (hN : Even N) (hN3 : 3 ≤ N)
    {P Q : LayerColumn N} (h : colSites P = colSites Q) : P = Q := by
  have hc : Q.1 ∈ colSites P := by
    rw [h, mem_colSites]
    exact Or.inl rfl
  have hσ : layerShift Q.2.1 Q.2.2 Q.1 ∈ colSites P := by
    rw [h, mem_colSites]
    exact Or.inr rfl
  rw [mem_colSites] at hc hσ
  rcases hc with hc | hc <;> rcases hσ with hσ | hσ
  · exact absurd (hσ.trans hc.symm)
      (layerShift_ne_self hN Q.2.1 Q.2.2 Q.1)
  · have hσ' : layerShift Q.2.1 Q.2.2 Q.1
        = layerShift P.2.1 P.2.2 Q.1 := by
      conv_rhs => rw [hc]
      exact hσ
    have hν : Q.2.1 = P.2.1 :=
      layerShift_inj_dir hN Q.2.2 P.2.2 Q.1 hσ'
    exact Prod.ext hc.symm (Subtype.ext hν.symm)
  · exfalso
    apply layerShift_comp_ne hN3 Q.2.2 P.2.2 P.1
    rw [← hc]
    exact hσ
  · exact absurd (hσ.trans hc.symm)
      (layerShift_ne_self hN Q.2.1 Q.2.2 Q.1)

/-- For distinct columns (and `3 ≤ N`), some site is read by
exactly one of them. -/
theorem exists_site_of_ne (hN : Even N) (hN3 : 3 ≤ N)
    {P Q : LayerColumn N} (hPQ : P ≠ Q) :
    ∃ s, (s ∈ colSites P ∧ s ∉ colSites Q)
      ∨ (s ∈ colSites Q ∧ s ∉ colSites P) := by
  by_cases h1 : ∃ s, s ∈ colSites P ∧ s ∉ colSites Q
  · obtain ⟨s, hs⟩ := h1
    exact ⟨s, Or.inl hs⟩
  · by_cases h2 : ∃ s, s ∈ colSites Q ∧ s ∉ colSites P
    · obtain ⟨s, hs⟩ := h2
      exact ⟨s, Or.inr hs⟩
    · exfalso
      apply hPQ
      apply colSites_eq_imp hN hN3
      apply Finset.Subset.antisymm
      · intro s hs
        by_contra hns
        exact h1 ⟨s, hs, hns⟩
      · intro s hs
        by_contra hns
        exact h2 ⟨s, hs, hns⟩

/-- The recombination of a split configuration: the inverse
of `splitEquiv` at the singleton `{s}`. -/
noncomputable def splitRecomb (s : LayerSite N)
    (z : (↥({s} : Finset (LayerSite N)) → G)
      × (↥({s}ᶜ : Finset (LayerSite N)) → G)) : LayerSite N → G :=
  (splitEquiv ({s} : Finset (LayerSite N))).symm z

theorem splitRecomb_fst (s : LayerSite N)
    (z : (↥({s} : Finset (LayerSite N)) → G)
      × (↥({s}ᶜ : Finset (LayerSite N)) → G))
    (ℓ : ↥({s} : Finset (LayerSite N))) :
    splitRecomb s z ℓ.1 = z.1 ℓ := by
  have h1 : (splitEquiv ({s} : Finset (LayerSite N))
      (splitRecomb s z)).1 = z.1 :=
    congrArg Prod.fst (MeasurableEquiv.apply_symm_apply _ z)
  have h2 := splitEquiv_fst ({s} : Finset (LayerSite N)) (splitRecomb s z)
  rw [h1] at h2
  exact (congrFun h2 ℓ).symm

theorem splitRecomb_snd (s : LayerSite N)
    (z : (↥({s} : Finset (LayerSite N)) → G)
      × (↥({s}ᶜ : Finset (LayerSite N)) → G))
    (ℓ : ↥({s}ᶜ : Finset (LayerSite N))) :
    splitRecomb s z ℓ.1 = z.2 ℓ := by
  have h1 : (splitEquiv ({s} : Finset (LayerSite N))
      (splitRecomb s z)).2 = z.2 :=
    congrArg Prod.snd (MeasurableEquiv.apply_symm_apply _ z)
  have h2 := splitEquiv_snd ({s} : Finset (LayerSite N)) (splitRecomb s z)
  rw [h1] at h2
  exact (congrFun h2 ℓ).symm

theorem splitRecomb_apply_split (s : LayerSite N)
    (U : LayerSite N → G) :
    splitRecomb s (splitEquiv ({s} : Finset (LayerSite N)) U) = U :=
  MeasurableEquiv.symm_apply_apply _ U

/-- **(S5) The inner integral at the split site.** Integrating
a column's real character over the split coordinate at one of
its own sites gives `e₁`, whatever the other coordinates
are: at the base site by right translation; at the far site
by cyclicity, inversion, and right translation. -/
theorem integral_split_inner (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P : LayerColumn N) (s : LayerSite N)
    (hsP : s ∈ colSites P)
    (w : ↥({s}ᶜ : Finset (LayerSite N)) → G) :
    ∫ v : ↥({s} : Finset (LayerSite N)) → G,
        colRe ρ u u' P (splitRecomb s (v, w))
        ∂(Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG)
      = e1 ρ μG := by
  classical
  rw [mem_colSites] at hsP
  set ℓ := layerLinkOf P.1 P.2.1 P.2.2 with hℓ
  set ℓ₀ : ↥({s} : Finset (LayerSite N)) :=
    ⟨s, Finset.mem_singleton_self s⟩ with hℓ₀
  rcases hsP with hs | hs
  · -- s is the base site
    have hfP : layerShift P.2.1 P.2.2 P.1 ≠ s :=
      fun h => layerShift_ne_self hN P.2.1 P.2.2 P.1 (h.trans hs)
    set wval : G := w ⟨layerShift P.2.1 P.2.2 P.1,
      Finset.mem_compl.mpr (fun hmem =>
        hfP (Finset.mem_singleton.mp hmem))⟩ with hwval
    have hw : ∀ v : ↥({s} : Finset (LayerSite N)) → G,
        colWord u u' P.1 P.2.1 P.2.2 (splitRecomb s (v, w))
          = (v ℓ₀) * (u' ℓ) * (wval)⁻¹ * (u ℓ)⁻¹ := by
      intro v
      have h1 : splitRecomb s (v, w) P.1 = v ℓ₀ := by
        have h2 := splitRecomb_fst s (v, w)
          (⟨P.1, Finset.mem_singleton.mpr hs.symm⟩ :
            ↥({s} : Finset (LayerSite N)))
        have h3 : (⟨P.1, Finset.mem_singleton.mpr hs.symm⟩ :
            ↥({s} : Finset (LayerSite N))) = ℓ₀ := Subtype.ext hs.symm
        rw [h3] at h2
        calc splitRecomb s (v, w) P.1 = splitRecomb s (v, w) s :=
              (congrArg (splitRecomb s (v, w)) hs).symm
          _ = v ℓ₀ := h2
      have hfar : splitRecomb s (v, w) (layerShift P.2.1 P.2.2 P.1)
          = wval :=
        splitRecomb_snd s (v, w) ⟨layerShift P.2.1 P.2.2 P.1,
          Finset.mem_compl.mpr (fun hmem =>
            hfP (Finset.mem_singleton.mp hmem))⟩
      show splitRecomb s (v, w) P.1 * (u' ℓ)
          * (splitRecomb s (v, w) (layerShift P.2.1 P.2.2 P.1))⁻¹
          * (u ℓ)⁻¹ = (v ℓ₀) * (u' ℓ) * (wval)⁻¹ * (u ℓ)⁻¹
      rw [h1, hfar]
    have hRe : ∀ v : ↥({s} : Finset (LayerSite N)) → G,
        colRe ρ u u' P (splitRecomb s (v, w))
          = (fun g => (charFn ρ (g * (u' ℓ) * (wval)⁻¹ * (u ℓ)⁻¹)).re)
            (v ℓ₀) :=
      fun v => congrArg (fun g => (charFn ρ g).re) (hw v)
    rw [integral_congr_ae (Filter.Eventually.of_forall hRe),
      integral_eval_coord_real μG (s := ℓ₀)
        (F := fun g => (charFn ρ (g * (u' ℓ) * (wval)⁻¹ * (u ℓ)⁻¹)).re)
        (by
          have hword : Continuous fun g : G =>
              g * (u' ℓ) * (wval)⁻¹ * (u ℓ)⁻¹ :=
            ((continuous_id.mul continuous_const).mul
              continuous_const.inv).mul continuous_const
          exact (Complex.continuous_re.comp
            ((continuous_charFn ρ hρcont).comp
              hword)).aestronglyMeasurable)]
    have hK : ∫ g, (charFn ρ (g * (u' ℓ) * (wval)⁻¹ * (u ℓ)⁻¹)).re ∂μG
        = ∫ g, (charFn ρ (g * ((u' ℓ) * (wval)⁻¹ * (u ℓ)⁻¹))).re
            ∂μG := by
      apply integral_congr_ae
      filter_upwards with g
      congr 2
      simp only [mul_assoc]
    rw [hK]
    exact integral_re_charFn_mul_right ρ μG hρcont _
  · -- s is the far site
    have hbP : P.1 ≠ s :=
      fun h => layerShift_ne_self hN P.2.1 P.2.2 P.1 (h.trans hs).symm
    set wval : G := w ⟨P.1,
      Finset.mem_compl.mpr (fun hmem =>
        hbP (Finset.mem_singleton.mp hmem))⟩ with hwval
    have hw : ∀ v : ↥({s} : Finset (LayerSite N)) → G,
        colWord u u' P.1 P.2.1 P.2.2 (splitRecomb s (v, w))
          = (wval) * (u' ℓ) * (v ℓ₀)⁻¹ * (u ℓ)⁻¹ := by
      intro v
      have h1 : splitRecomb s (v, w) (layerShift P.2.1 P.2.2 P.1)
          = v ℓ₀ := by
        have h2 := splitRecomb_fst s (v, w)
          (⟨layerShift P.2.1 P.2.2 P.1,
            Finset.mem_singleton.mpr hs.symm⟩ :
            ↥({s} : Finset (LayerSite N)))
        have h3 : (⟨layerShift P.2.1 P.2.2 P.1,
            Finset.mem_singleton.mpr hs.symm⟩ :
            ↥({s} : Finset (LayerSite N))) = ℓ₀ := Subtype.ext hs.symm
        rw [h3] at h2
        calc splitRecomb s (v, w) (layerShift P.2.1 P.2.2 P.1)
            = splitRecomb s (v, w) s :=
              (congrArg (splitRecomb s (v, w)) hs).symm
          _ = v ℓ₀ := h2
      have hbase : splitRecomb s (v, w) P.1 = wval :=
        splitRecomb_snd s (v, w) ⟨P.1,
          Finset.mem_compl.mpr (fun hmem =>
            hbP (Finset.mem_singleton.mp hmem))⟩
      show splitRecomb s (v, w) P.1 * (u' ℓ)
          * (splitRecomb s (v, w) (layerShift P.2.1 P.2.2 P.1))⁻¹
          * (u ℓ)⁻¹ = (wval) * (u' ℓ) * (v ℓ₀)⁻¹ * (u ℓ)⁻¹
      rw [hbase, h1]
    have hRe : ∀ v : ↥({s} : Finset (LayerSite N)) → G,
        colRe ρ u u' P (splitRecomb s (v, w))
          = (fun g => (charFn ρ ((wval) * (u' ℓ) * g⁻¹ * (u ℓ)⁻¹)).re)
            (v ℓ₀) :=
      fun v => congrArg (fun g => (charFn ρ g).re) (hw v)
    rw [integral_congr_ae (Filter.Eventually.of_forall hRe),
      integral_eval_coord_real μG (s := ℓ₀)
        (F := fun g => (charFn ρ ((wval) * (u' ℓ) * g⁻¹ * (u ℓ)⁻¹)).re)
        (by
          have hword : Continuous fun g : G =>
              (wval) * (u' ℓ) * g⁻¹ * (u ℓ)⁻¹ :=
            ((continuous_const.mul continuous_const).mul
              continuous_id.inv).mul continuous_const
          exact (Complex.continuous_re.comp
            ((continuous_charFn ρ hρcont).comp
              hword)).aestronglyMeasurable)]
    have e1' : ∀ g : G,
        (charFn ρ ((wval) * (u' ℓ) * g⁻¹ * (u ℓ)⁻¹)).re
          = (charFn ρ (g⁻¹ * ((u ℓ)⁻¹ * (wval) * (u' ℓ)))).re := by
      intro g
      have h1 : (wval) * (u' ℓ) * g⁻¹ * (u ℓ)⁻¹
          = ((wval) * (u' ℓ)) * (g⁻¹ * (u ℓ)⁻¹) := by
        simp only [mul_assoc]
      have h2 : (g⁻¹ * (u ℓ)⁻¹) * ((wval) * (u' ℓ))
          = g⁻¹ * ((u ℓ)⁻¹ * (wval) * (u' ℓ)) := by
        simp only [mul_assoc]
      have hw2 : charFn ρ ((wval) * (u' ℓ) * g⁻¹ * (u ℓ)⁻¹)
          = charFn ρ (g⁻¹ * ((u ℓ)⁻¹ * (wval) * (u' ℓ))) := by
        rw [h1, charFn_mul_comm, h2]
      exact congrArg Complex.re hw2
    rw [integral_congr_ae (Filter.Eventually.of_forall e1'),
      integral_inv_eq_self
        (fun g => (charFn ρ (g * ((u ℓ)⁻¹ * (wval) * (u' ℓ)))).re) μG]
    exact integral_re_charFn_mul_right ρ μG hρcont _

/-- **(S5) The directed cross term.** If `s` is a site of
`P` but not of `Q` (needs `3 ≤ N` through the site
combinatorics that produces such an `s`), the cross moment
factors: `∫ Re χ_P · Re χ_Q = e₁²` — the analytic
P₀-collapse. -/
theorem integral_cross_of_site (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P Q : LayerColumn N) (s : LayerSite N)
    (hsP : s ∈ colSites P) (hsQ : s ∉ colSites Q) :
    ∫ α : LayerSite N → G, colRe ρ u u' P α * colRe ρ u u' Q α
        ∂(Measure.pi fun _ : LayerSite N => μG) = (e1 ρ μG) ^ 2 := by
  classical
  have hbQ : Q.1 ≠ s := by
    intro h
    apply hsQ
    have hmem : Q.1 ∈ colSites Q := mem_colSites.mpr (Or.inl rfl)
    rw [h] at hmem
    exact hmem
  have hfQ : layerShift Q.2.1 Q.2.2 Q.1 ≠ s := by
    intro h
    apply hsQ
    have hmem : layerShift Q.2.1 Q.2.2 Q.1 ∈ colSites Q :=
      mem_colSites.mpr (Or.inr rfl)
    rw [h] at hmem
    exact hmem
  -- transport to the split product
  have hInt : Integrable
      (fun z : (↥({s} : Finset (LayerSite N)) → G)
          × (↥({s}ᶜ : Finset (LayerSite N)) → G) =>
        colRe ρ u u' P (splitRecomb s z)
          * colRe ρ u u' Q (splitRecomb s z))
      ((Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG).prod
        (Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG)) := by
    refine Integrable.of_bound ?_ ((d : ℝ) ^ 2)
      (Filter.Eventually.of_forall fun z => ?_)
    · exact (((measurable_colRe ρ hρcont u u' P).comp
        (splitEquiv ({s} : Finset (LayerSite N))).symm.measurable).mul
        ((measurable_colRe ρ hρcont u u' Q).comp
          (splitEquiv ({s} : Finset (LayerSite N))).symm.measurable)
        ).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, pow_two]
      exact mul_le_mul (abs_re_charFn_le ρ _) (abs_re_charFn_le ρ _)
        (abs_nonneg _) (Nat.cast_nonneg d)
  have htrans : ∫ α : LayerSite N → G,
        colRe ρ u u' P α * colRe ρ u u' Q α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ z : (↥({s} : Finset (LayerSite N)) → G)
          × (↥({s}ᶜ : Finset (LayerSite N)) → G),
          colRe ρ u u' P (splitRecomb s z)
            * colRe ρ u u' Q (splitRecomb s z)
          ∂((Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG).prod
            (Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG)) := by
    have h := (measurePreserving_splitEquiv μG
      ({s} : Finset (LayerSite N))).integral_comp
      (splitEquiv ({s} : Finset (LayerSite N))).measurableEmbedding
      (fun z => colRe ρ u u' P (splitRecomb s z)
        * colRe ρ u u' Q (splitRecomb s z))
    have hL : ∫ U : LayerSite N → G,
          (fun z => colRe ρ u u' P (splitRecomb s z)
            * colRe ρ u u' Q (splitRecomb s z))
            (splitEquiv ({s} : Finset (LayerSite N)) U)
          ∂(Measure.pi fun _ : LayerSite N => μG)
        = ∫ U : LayerSite N → G, colRe ρ u u' P U * colRe ρ u u' Q U
            ∂(Measure.pi fun _ : LayerSite N => μG) := by
      apply integral_congr_ae
      filter_upwards with U
      show colRe ρ u u' P (splitRecomb s
            (splitEquiv ({s} : Finset (LayerSite N)) U))
          * colRe ρ u u' Q (splitRecomb s
            (splitEquiv ({s} : Finset (LayerSite N)) U))
        = colRe ρ u u' P U * colRe ρ u u' Q U
      rw [splitRecomb_apply_split]
    rw [hL] at h
    exact h
  calc ∫ α : LayerSite N → G, colRe ρ u u' P α * colRe ρ u u' Q α
          ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∫ z : (↥({s} : Finset (LayerSite N)) → G)
            × (↥({s}ᶜ : Finset (LayerSite N)) → G),
            colRe ρ u u' P (splitRecomb s z)
              * colRe ρ u u' Q (splitRecomb s z)
            ∂((Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG).prod
              (Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG)) :=
        htrans
    _ = ∫ w : ↥({s}ᶜ : Finset (LayerSite N)) → G,
            ∫ v : ↥({s} : Finset (LayerSite N)) → G,
              colRe ρ u u' P (splitRecomb s (v, w))
                * colRe ρ u u' Q (splitRecomb s (v, w))
              ∂(Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG)
            ∂(Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG) :=
        integral_prod_symm _ hInt
    _ = ∫ w : ↥({s}ᶜ : Finset (LayerSite N)) → G,
            (e1 ρ μG) * colRe ρ u u' Q (splitRecomb s (fun _ => 1, w))
            ∂(Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG) := by
        apply integral_congr_ae
        filter_upwards with w
        have hQc : ∀ v : ↥({s} : Finset (LayerSite N)) → G,
            colRe ρ u u' Q (splitRecomb s (v, w))
              = colRe ρ u u' Q (splitRecomb s (fun _ => 1, w)) := by
          intro v
          have h1 : splitRecomb s (v, w) Q.1
              = splitRecomb s (fun _ => 1, w) Q.1 :=
            (splitRecomb_snd s (v, w) ⟨Q.1,
              Finset.mem_compl.mpr (fun hmem =>
                hbQ (Finset.mem_singleton.mp hmem))⟩).trans
              (splitRecomb_snd s (fun _ => 1, w) ⟨Q.1,
                Finset.mem_compl.mpr (fun hmem =>
                  hbQ (Finset.mem_singleton.mp hmem))⟩).symm
          have h2 : splitRecomb s (v, w) (layerShift Q.2.1 Q.2.2 Q.1)
              = splitRecomb s (fun _ => 1, w)
                  (layerShift Q.2.1 Q.2.2 Q.1) :=
            (splitRecomb_snd s (v, w) ⟨layerShift Q.2.1 Q.2.2 Q.1,
              Finset.mem_compl.mpr (fun hmem =>
                hfQ (Finset.mem_singleton.mp hmem))⟩).trans
              (splitRecomb_snd s (fun _ => 1, w)
                ⟨layerShift Q.2.1 Q.2.2 Q.1,
                  Finset.mem_compl.mpr (fun hmem =>
                    hfQ (Finset.mem_singleton.mp hmem))⟩).symm
          exact congrArg (fun g => (charFn ρ g).re)
            (colWord_eq_of_agree u u' Q.1 Q.2.1 Q.2.2 h1 h2)
        calc ∫ v : ↥({s} : Finset (LayerSite N)) → G,
                colRe ρ u u' P (splitRecomb s (v, w))
                  * colRe ρ u u' Q (splitRecomb s (v, w))
                ∂(Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG)
            = ∫ v : ↥({s} : Finset (LayerSite N)) → G,
                  colRe ρ u u' P (splitRecomb s (v, w))
                    * colRe ρ u u' Q (splitRecomb s (fun _ => 1, w))
                  ∂(Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG) :=
              integral_congr_ae (Filter.Eventually.of_forall fun v => by
                show colRe ρ u u' P (splitRecomb s (v, w))
                    * colRe ρ u u' Q (splitRecomb s (v, w))
                  = colRe ρ u u' P (splitRecomb s (v, w))
                    * colRe ρ u u' Q (splitRecomb s (fun _ => 1, w))
                rw [hQc v])
          _ = (∫ v : ↥({s} : Finset (LayerSite N)) → G,
                    colRe ρ u u' P (splitRecomb s (v, w))
                    ∂(Measure.pi fun _ : ↥({s} : Finset (LayerSite N)) => μG))
                  * colRe ρ u u' Q (splitRecomb s (fun _ => 1, w)) :=
              integral_mul_const _ _
          _ = (e1 ρ μG)
                  * colRe ρ u u' Q (splitRecomb s (fun _ => 1, w)) := by
              rw [integral_split_inner ρ μG hN hρcont u u' P s hsP w]
    _ = (e1 ρ μG) * (e1 ρ μG) := by
        rw [integral_const_mul]
        congr 1
        have hrestr : ∫ w : ↥({s}ᶜ : Finset (LayerSite N)) → G,
              colRe ρ u u' Q (splitRecomb s (fun _ => 1, w))
              ∂(Measure.pi fun _ : ↥({s}ᶜ : Finset (LayerSite N)) => μG)
            = ∫ α : LayerSite N → G, colRe ρ u u' Q α
                ∂(Measure.pi fun _ : LayerSite N => μG) := by
          rw [← integral_pi_restrict_real μG ({s}ᶜ : Finset (LayerSite N))
            (fun w => colRe ρ u u' Q (splitRecomb s (fun _ => 1, w)))]
          apply integral_congr_ae
          filter_upwards with U
          have h1 : splitRecomb s
                (fun _ => 1, fun ℓ : ↥({s}ᶜ : Finset (LayerSite N)) =>
                  U ℓ.1) Q.1 = U Q.1 :=
            splitRecomb_snd s _ ⟨Q.1,
              Finset.mem_compl.mpr (fun hmem =>
                hbQ (Finset.mem_singleton.mp hmem))⟩
          have h2 : splitRecomb s
                (fun _ => 1, fun ℓ : ↥({s}ᶜ : Finset (LayerSite N)) =>
                  U ℓ.1) (layerShift Q.2.1 Q.2.2 Q.1)
              = U (layerShift Q.2.1 Q.2.2 Q.1) :=
            splitRecomb_snd s _ ⟨layerShift Q.2.1 Q.2.2 Q.1,
              Finset.mem_compl.mpr (fun hmem =>
                hfQ (Finset.mem_singleton.mp hmem))⟩
          exact congrArg (fun g => (charFn ρ g).re)
            (colWord_eq_of_agree u u' Q.1 Q.2.1 Q.2.2 h1 h2)
        rw [hrestr]
        exact integral_colRe ρ μG hN hρcont u u' Q
    _ = (e1 ρ μG) ^ 2 := by rw [pow_two]

/-- **(S5) The cross term:** distinct columns are
uncorrelated at second order. -/
theorem integral_cross (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {P Q : LayerColumn N} (hPQ : P ≠ Q) :
    ∫ α : LayerSite N → G, colRe ρ u u' P α * colRe ρ u u' Q α
        ∂(Measure.pi fun _ : LayerSite N => μG) = (e1 ρ μG) ^ 2 := by
  obtain ⟨s, hs | hs⟩ := exists_site_of_ne hN hN3 hPQ
  · exact integral_cross_of_site ρ μG hN hN3 hρcont u u' P Q s hs.1 hs.2
  · have h := integral_cross_of_site ρ μG hN hN3 hρcont u u' Q P s hs.1 hs.2
    rw [integral_congr_ae (Filter.Eventually.of_forall fun α =>
      mul_comm (colRe ρ u u' P α) (colRe ρ u u' Q α))]
    exact h

/-- **(S5) Diagonal density product:** a column against
itself. -/
theorem integral_colDens_mul_self (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) (P : LayerColumn N) :
    ∫ α : LayerSite N → G, colDensC ρ u u' P α * colDensC ρ u u' P α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = 1 - 2 * e1 ρ μG / (d : ℝ) + q2 ρ μG / (d : ℝ) ^ 2 := by
  classical
  have hIP := integrable_colRe ρ μG hρcont u u' P
  have hIPQ : Integrable
      (fun α => colRe ρ u u' P α * colRe ρ u u' P α)
      (Measure.pi fun _ : LayerSite N => μG) := by
    refine Integrable.of_bound ?_ ((d : ℝ) ^ 2)
      (Filter.Eventually.of_forall fun α => ?_)
    · exact ((measurable_colRe ρ hρcont u u' P).mul
        (measurable_colRe ρ hρcont u u' P)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, pow_two]
      exact mul_le_mul (abs_re_charFn_le ρ _) (abs_re_charFn_le ρ _)
        (abs_nonneg _) (Nat.cast_nonneg d)
  have hsq : ∫ α : LayerSite N → G,
        colRe ρ u u' P α * colRe ρ u u' P α
        ∂(Measure.pi fun _ : LayerSite N => μG) = q2 ρ μG := by
    have h := integral_colReSq ρ μG hN hρcont u u' P.1 P.2.1 P.2.2
    rw [integral_congr_ae (Filter.Eventually.of_forall fun α =>
      (pow_two (colRe ρ u u' P α)).symm)]
    exact h
  have hexp : ∀ α : LayerSite N → G,
      colDensC ρ u u' P α * colDensC ρ u u' P α
        = 1 - (d : ℝ)⁻¹ * colRe ρ u u' P α - (d : ℝ)⁻¹ * colRe ρ u u' P α
          + (d : ℝ)⁻¹ * ((d : ℝ)⁻¹ *
            (colRe ρ u u' P α * colRe ρ u u' P α)) := by
    intro α
    rw [colDensC_eq]
    by_cases hd : (d : ℝ) = 0
    · have hd0 : d = 0 := by exact_mod_cast hd
      have hz : colRe ρ u u' P α = 0 := by
        show (charFn ρ _).re = 0
        rw [charFn_eq_zero ρ hd0]
        simp
      rw [hz, hd]
      norm_num
    · field_simp
      ring
  have hA1 : Integrable (fun α => (1 : ℝ) - (d : ℝ)⁻¹ * colRe ρ u u' P α)
      (Measure.pi fun _ : LayerSite N => μG) :=
    (integrable_const (1 : ℝ)).sub (hIP.const_mul _)
  have hAB : Integrable (fun α => (1 : ℝ) - (d : ℝ)⁻¹ * colRe ρ u u' P α
        - (d : ℝ)⁻¹ * colRe ρ u u' P α)
      (Measure.pi fun _ : LayerSite N => μG) :=
    hA1.sub (hIP.const_mul _)
  have hC : Integrable (fun α => (d : ℝ)⁻¹ * ((d : ℝ)⁻¹ *
        (colRe ρ u u' P α * colRe ρ u u' P α)))
      (Measure.pi fun _ : LayerSite N => μG) :=
    (hIPQ.const_mul _).const_mul _
  have hsum : ∫ α : LayerSite N → G,
        1 - (d : ℝ)⁻¹ * colRe ρ u u' P α - (d : ℝ)⁻¹ * colRe ρ u u' P α
          + (d : ℝ)⁻¹ * ((d : ℝ)⁻¹ *
            (colRe ρ u u' P α * colRe ρ u u' P α))
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = 1 - (d : ℝ)⁻¹ * e1 ρ μG - (d : ℝ)⁻¹ * e1 ρ μG
          + (d : ℝ)⁻¹ * ((d : ℝ)⁻¹ * q2 ρ μG) := by
    rw [integral_add hAB hC, integral_sub hA1 (hIP.const_mul _),
      integral_sub (integrable_const (1 : ℝ)) (hIP.const_mul _)]
    simp only [integral_const_mul,
      integral_colRe ρ μG hN hρcont u u' P, hsq, integral_const,
      probReal_univ, one_smul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp), hsum]
  by_cases hd : (d : ℝ) = 0
  · have hd0 : d = 0 := by exact_mod_cast hd
    have he1 : e1 ρ μG = 0 := by
      unfold e1
      simp [charFn_eq_zero ρ hd0]
    have hq2 : q2 ρ μG = 0 := by
      unfold q2
      simp [charFn_eq_zero ρ hd0]
    rw [he1, hq2, hd]
    norm_num
  · field_simp
    ring

/-- **(S5) Off-diagonal density product:** distinct
columns. -/
theorem integral_colDens_mul_ne (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) {P Q : LayerColumn N} (hPQ : P ≠ Q) :
    ∫ α : LayerSite N → G, colDensC ρ u u' P α * colDensC ρ u u' Q α
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = 1 - 2 * e1 ρ μG / (d : ℝ) + (e1 ρ μG) ^ 2 / (d : ℝ) ^ 2 := by
  classical
  have hIP := integrable_colRe ρ μG hρcont u u' P
  have hIQ := integrable_colRe ρ μG hρcont u u' Q
  have hIPQ : Integrable
      (fun α => colRe ρ u u' P α * colRe ρ u u' Q α)
      (Measure.pi fun _ : LayerSite N => μG) := by
    refine Integrable.of_bound ?_ ((d : ℝ) ^ 2)
      (Filter.Eventually.of_forall fun α => ?_)
    · exact ((measurable_colRe ρ hρcont u u' P).mul
        (measurable_colRe ρ hρcont u u' Q)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, pow_two]
      exact mul_le_mul (abs_re_charFn_le ρ _) (abs_re_charFn_le ρ _)
        (abs_nonneg _) (Nat.cast_nonneg d)
  have hexp : ∀ α : LayerSite N → G,
      colDensC ρ u u' P α * colDensC ρ u u' Q α
        = 1 - (d : ℝ)⁻¹ * colRe ρ u u' P α - (d : ℝ)⁻¹ * colRe ρ u u' Q α
          + (d : ℝ)⁻¹ * ((d : ℝ)⁻¹ *
            (colRe ρ u u' P α * colRe ρ u u' Q α)) := by
    intro α
    rw [colDensC_eq, colDensC_eq]
    by_cases hd : (d : ℝ) = 0
    · have hd0 : d = 0 := by exact_mod_cast hd
      have hzP : colRe ρ u u' P α = 0 := by
        show (charFn ρ _).re = 0
        rw [charFn_eq_zero ρ hd0]
        simp
      have hzQ : colRe ρ u u' Q α = 0 := by
        show (charFn ρ _).re = 0
        rw [charFn_eq_zero ρ hd0]
        simp
      rw [hzP, hzQ, hd]
      norm_num
    · field_simp
      ring
  have hA1 : Integrable (fun α => (1 : ℝ) - (d : ℝ)⁻¹ * colRe ρ u u' P α)
      (Measure.pi fun _ : LayerSite N => μG) :=
    (integrable_const (1 : ℝ)).sub (hIP.const_mul _)
  have hAB : Integrable (fun α => (1 : ℝ) - (d : ℝ)⁻¹ * colRe ρ u u' P α
        - (d : ℝ)⁻¹ * colRe ρ u u' Q α)
      (Measure.pi fun _ : LayerSite N => μG) :=
    hA1.sub (hIQ.const_mul _)
  have hC : Integrable (fun α => (d : ℝ)⁻¹ * ((d : ℝ)⁻¹ *
        (colRe ρ u u' P α * colRe ρ u u' Q α)))
      (Measure.pi fun _ : LayerSite N => μG) :=
    (hIPQ.const_mul _).const_mul _
  have hsum : ∫ α : LayerSite N → G,
        1 - (d : ℝ)⁻¹ * colRe ρ u u' P α - (d : ℝ)⁻¹ * colRe ρ u u' Q α
          + (d : ℝ)⁻¹ * ((d : ℝ)⁻¹ *
            (colRe ρ u u' P α * colRe ρ u u' Q α))
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = 1 - (d : ℝ)⁻¹ * e1 ρ μG - (d : ℝ)⁻¹ * e1 ρ μG
          + (d : ℝ)⁻¹ * ((d : ℝ)⁻¹ * (e1 ρ μG) ^ 2) := by
    rw [integral_add hAB hC, integral_sub hA1 (hIQ.const_mul _),
      integral_sub (integrable_const (1 : ℝ)) (hIP.const_mul _)]
    simp only [integral_const_mul,
      integral_colRe ρ μG hN hρcont u u' P,
      integral_colRe ρ μG hN hρcont u u' Q,
      integral_cross ρ μG hN hN3 hρcont u u' hPQ, integral_const,
      probReal_univ, one_smul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp), hsum]
  by_cases hd : (d : ℝ) = 0
  · have hd0 : d = 0 := by exact_mod_cast hd
    have he1 : e1 ρ μG = 0 := by
      unfold e1
      simp [charFn_eq_zero ρ hd0]
    rw [he1, hd]
    norm_num
  · field_simp
    ring

end Moments

section Expansion

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- The layer density sum is measurable. -/
theorem measurable_layerDensSum (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    Measurable fun α : LayerSite N → G => layerDensSum ρ α u u' := by
  have hfun : (fun α : LayerSite N → G => layerDensSum ρ α u u')
      = fun α => ∑ P : LayerColumn N, colDensC ρ u u' P α :=
    funext fun α => layerDensSum_eq_sum_columns ρ hN α u u'
  rw [hfun]
  exact Finset.measurable_sum _ fun P _ =>
    measurable_colDens ρ hρcont u u' P.1 P.2.1 P.2.2

/-- **(S6) The second coefficient in closed form.** With
`M = colCount N` columns: the diagonal pairs contribute the
`q₂` form, the `M(M−1)` ordered off-diagonal pairs the
`e₁²` form (P₀-collapse). In particular `betaCoeff2` does
not depend on `(u, u')` at all. -/
theorem betaCoeff2_closed (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' : LayerLink N → G) :
    betaCoeff2 ρ μG u u'
      = (colCount N * (1 - 2 * e1 ρ μG / (d : ℝ) + q2 ρ μG / (d : ℝ) ^ 2)
        + colCount N * (colCount N - 1)
          * (1 - 2 * e1 ρ μG / (d : ℝ) + (e1 ρ μG) ^ 2 / (d : ℝ) ^ 2)) / 2 := by
  classical
  have hInt : ∀ P : LayerColumn N,
      Integrable (fun α => colDensC ρ u u' P α)
        (Measure.pi fun _ : LayerSite N => μG) :=
    fun P => integrable_colDens ρ μG hρcont u u' P.1 P.2.1 P.2.2
  have hIntMul : ∀ P Q : LayerColumn N,
      Integrable (fun α => colDensC ρ u u' P α * colDensC ρ u u' Q α)
        (Measure.pi fun _ : LayerSite N => μG) := by
    intro P Q
    refine Integrable.of_bound ?_ (4 : ℝ)
      (Filter.Eventually.of_forall fun α => ?_)
    · exact ((measurable_colDens ρ hρcont u u' P.1 P.2.1 P.2.2).mul
        (measurable_colDens ρ hρcont u u' Q.1 Q.2.1 Q.2.2)).aestronglyMeasurable
    · have h0P : (0 : ℝ) ≤ colDensC ρ u u' P α :=
        colDens_nonneg ρ u u' P.1 P.2.1 P.2.2 α
      have h2P : colDensC ρ u u' P α ≤ 2 :=
        colDens_le_two ρ u u' P.1 P.2.1 P.2.2 α
      have h0Q : (0 : ℝ) ≤ colDensC ρ u u' Q α :=
        colDens_nonneg ρ u u' Q.1 Q.2.1 Q.2.2 α
      have h2Q : colDensC ρ u u' Q α ≤ 2 :=
        colDens_le_two ρ u u' Q.1 Q.2.1 Q.2.2 α
      have h1 : |colDensC ρ u u' P α| ≤ 2 :=
        abs_le.mpr ⟨by linarith, h2P⟩
      have h2 : |colDensC ρ u u' Q α| ≤ 2 :=
        abs_le.mpr ⟨by linarith, h2Q⟩
      rw [Real.norm_eq_abs, abs_mul]
      calc |colDensC ρ u u' P α| * |colDensC ρ u u' Q α|
          ≤ 2 * 2 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        _ = 4 := by norm_num
  have hdiv : ∀ X : (LayerSite N → G) → ℝ,
      (∫ α, X α / 2 ∂(Measure.pi fun _ : LayerSite N => μG))
        = (∫ α, X α ∂(Measure.pi fun _ : LayerSite N => μG)) / 2 := by
    intro X
    have h1 : (∫ α, X α / 2 ∂(Measure.pi fun _ : LayerSite N => μG))
        = ∫ α, (2 : ℝ)⁻¹ * X α ∂(Measure.pi fun _ : LayerSite N => μG) :=
      integral_congr_ae (Filter.Eventually.of_forall fun α => by ring)
    rw [h1, integral_const_mul]
    ring
  have hpt : ∀ α : LayerSite N → G,
      (layerDensSum ρ α u u') ^ 2 / 2
        = (∑ P : LayerColumn N, ∑ Q : LayerColumn N,
            colDensC ρ u u' P α * colDensC ρ u u' Q α) / 2 := by
    intro α
    rw [layerDensSum_eq_sum_columns ρ hN α u u', sq, Finset.sum_mul_sum]
  unfold betaCoeff2
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), hdiv]
  congr 1
  calc ∫ α : LayerSite N → G, ∑ P : LayerColumn N, ∑ Q : LayerColumn N,
          colDensC ρ u u' P α * colDensC ρ u u' Q α
          ∂(Measure.pi fun _ : LayerSite N => μG)
      = ∑ P : LayerColumn N, ∫ α : LayerSite N → G,
            ∑ Q : LayerColumn N, colDensC ρ u u' P α * colDensC ρ u u' Q α
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_finsetSum Finset.univ (fun P _ =>
          integrable_finsetSum Finset.univ (fun Q _ => hIntMul P Q))
    _ = ∑ P : LayerColumn N, ∑ Q : LayerColumn N,
            ∫ α : LayerSite N → G, colDensC ρ u u' P α * colDensC ρ u u' Q α
              ∂(Measure.pi fun _ : LayerSite N => μG) :=
        Finset.sum_congr rfl fun P _ =>
          integral_finsetSum Finset.univ (fun Q _ => hIntMul P Q)
    _ = ∑ P : LayerColumn N,
          ((1 - 2 * e1 ρ μG / (d : ℝ) + q2 ρ μG / (d : ℝ) ^ 2)
            + ∑ Q ∈ Finset.univ.erase P,
              (1 - 2 * e1 ρ μG / (d : ℝ)
                + (e1 ρ μG) ^ 2 / (d : ℝ) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro P _
        rw [← Finset.add_sum_erase Finset.univ
          (fun Q => ∫ α : LayerSite N → G,
            colDensC ρ u u' P α * colDensC ρ u u' Q α
            ∂(Measure.pi fun _ : LayerSite N => μG)) (Finset.mem_univ P)]
        congr 1
        · exact integral_colDens_mul_self ρ μG hN hρcont u u' P
        · apply Finset.sum_congr rfl
          intro Q hQ
          exact integral_colDens_mul_ne ρ μG hN hN3 hρcont u u'
            (Finset.ne_of_mem_erase hQ).symm
    _ = colCount N * (1 - 2 * e1 ρ μG / (d : ℝ) + q2 ρ μG / (d : ℝ) ^ 2)
          + colCount N * (colCount N - 1)
            * (1 - 2 * e1 ρ μG / (d : ℝ)
              + (e1 ρ μG) ^ 2 / (d : ℝ) ^ 2) := by
        have hpos : 1 ≤ Fintype.card (LayerColumn N) :=
          Fintype.card_pos_iff.mpr ⟨⟨⟨fun _ => 0, by simp⟩, ⟨1, by decide⟩⟩⟩
        have hcard : ∀ P : LayerColumn N,
            (Finset.univ.erase P).card = Fintype.card (LayerColumn N) - 1 :=
          fun P => by
            rw [Finset.card_erase_of_mem (Finset.mem_univ P),
              Finset.card_univ]
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            show colCount N = (Fintype.card (LayerColumn N) : ℝ) from rfl]
        · calc ∑ P : LayerColumn N, ∑ _Q ∈ Finset.univ.erase P,
                (1 - 2 * e1 ρ μG / (d : ℝ) + (e1 ρ μG) ^ 2 / (d : ℝ) ^ 2)
              = ∑ _P : LayerColumn N,
                  (colCount N - 1)
                    * (1 - 2 * e1 ρ μG / (d : ℝ)
                      + (e1 ρ μG) ^ 2 / (d : ℝ) ^ 2) := by
                apply Finset.sum_congr rfl
                intro P _
                rw [Finset.sum_const, hcard P, nsmul_eq_mul]
                congr 1
                rw [Nat.cast_sub hpos, Nat.cast_one]
                rfl
            _ = colCount N * (colCount N - 1)
                  * (1 - 2 * e1 ρ μG / (d : ℝ)
                    + (e1 ρ μG) ^ 2 / (d : ℝ) ^ 2) := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
                  show colCount N = (Fintype.card (LayerColumn N) : ℝ) from rfl]
                ring

/-- **Headline (β¹ and β² dependence vanish).** At general
`(G, ρ)`, for `N` even and `N ≥ 3`, both expansion
coefficients of `𝒜` are independent of the boundary links
`(u, u')`: the `(u, u')`-dependence of `𝒜` is `O(β³)`.
(The `β¹` half is `betaCoeff1_closed`; the `β²` half is
the content of this brick.) -/
theorem layerKernel_dep_beta2_zero (hN : Even N) (hN3 : 3 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (u u' v v' : LayerLink N → G) :
    betaCoeff1 ρ μG u u' = betaCoeff1 ρ μG v v'
      ∧ betaCoeff2 ρ μG u u' = betaCoeff2 ρ μG v v' :=
  ⟨by rw [betaCoeff1_closed ρ μG hN hρcont,
      betaCoeff1_closed ρ μG hN hρcont],
   by rw [betaCoeff2_closed ρ μG hN hN3 hρcont,
      betaCoeff2_closed ρ μG hN hN3 hρcont]⟩

/-- Pointwise bound on the `n`-th Taylor term of the layer
exponential: `|layerDensSum| ≤ 2M` controls everything. -/
theorem norm_term_le (hN : Even N) (β : ℝ) (u u' : LayerLink N → G)
    (n : ℕ) (α : LayerSite N → G) :
    ‖(-β * layerDensSum ρ α u u') ^ n / ((Nat.factorial n : ℝ))‖
      ≤ (|β| * (2 * colCount N)) ^ n / (Nat.factorial n : ℝ) := by
  have hS : 0 ≤ layerDensSum ρ α u u' :=
    layerDensSum_nonneg ρ hN α u u'
  have hS2 : layerDensSum ρ α u u' ≤ 2 * colCount N :=
    layerDensSum_le ρ hN α u u'
  have hfact : |((Nat.factorial n : ℝ))| = (Nat.factorial n : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg _)
  rw [Real.norm_eq_abs, abs_div, abs_pow, hfact]
  apply (div_le_div_iff_of_pos_right
    (Nat.cast_pos.mpr (Nat.factorial_pos n))).mpr
  apply pow_le_pow_left₀ (abs_nonneg _) _ n
  rw [abs_mul, abs_neg, abs_of_nonneg hS]
  exact mul_le_mul_of_nonneg_left hS2 (abs_nonneg β)

/-- Every Taylor term of the layer exponential is
integrable. -/
theorem integrable_term (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) (n : ℕ) :
    Integrable (fun α => (-β * layerDensSum ρ α u u') ^ n / ((Nat.factorial n : ℝ)))
      (Measure.pi fun _ : LayerSite N => μG) := by
  refine Integrable.of_bound ?_ ((|β| * (2 * colCount N)) ^ n / (Nat.factorial n : ℝ))
    (Filter.Eventually.of_forall fun α =>
      norm_term_le ρ hN β u u' n α)
  exact ((((measurable_layerDensSum ρ hN hρcont u u').const_mul
    (-β)).pow_const n).div_const ((Nat.factorial n : ℝ))).aestronglyMeasurable

/-- The Taylor terms' norm-integrals are summable, by
comparison with the exponential series. -/
theorem summable_norm_term_int (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) :
    Summable fun n => ∫ α, ‖(-β * layerDensSum ρ α u u') ^ n / ((Nat.factorial n : ℝ))‖
        ∂(Measure.pi fun _ : LayerSite N => μG) := by
  refine Summable.of_norm_bounded
    (Real.summable_pow_div_factorial (|β| * (2 * colCount N))) fun n => ?_
  rw [Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun α => norm_nonneg _)]
  calc ∫ α, ‖(-β * layerDensSum ρ α u u') ^ n / ((Nat.factorial n : ℝ))‖
          ∂(Measure.pi fun _ : LayerSite N => μG)
      ≤ ∫ _α : LayerSite N → G, (|β| * (2 * colCount N)) ^ n / (Nat.factorial n : ℝ)
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
        integral_mono_ae (integrable_term ρ μG hN hρcont β u u' n).norm
          (integrable_const _)
          (Filter.Eventually.of_forall fun α =>
            norm_term_le ρ hN β u u' n α)
    _ = (|β| * (2 * colCount N)) ^ n / (Nat.factorial n : ℝ) := by
        rw [integral_const, probReal_univ, one_smul]

/-- **(S6) The expansion, real form.** For every real `β`,
the stratum average of the layer exponential is
`1 − β·C₁ + β²·C₂ + R(β)` with `C₁, C₂` the closed
coefficients above and `R(β)` the displayed tail series.
FENCE: this is an identity of Taylor coefficients. It
implies NO positivity of `𝒜` at any `β > 0`; `β2` and
(H-PF) remain open. -/
theorem layerKernel_real_expansion (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) :
    ∫ α, Real.exp (-(β * layerDensSum ρ α u u'))
        ∂(Measure.pi fun _ : LayerSite N => μG)
      = 1 - β * betaCoeff1 ρ μG u u' + β ^ 2 * betaCoeff2 ρ μG u u'
        + ∑' (k : ℕ), ∫ α, (-β * layerDensSum ρ α u u') ^ (k + 3)
            / ((Nat.factorial (k + 3) : ℝ))
            ∂(Measure.pi fun _ : LayerSite N => μG) := by
  have hexp : ∀ α : LayerSite N → G,
      Real.exp (-(β * layerDensSum ρ α u u'))
        = ∑' n : ℕ, (-β * layerDensSum ρ α u u') ^ n / ((Nat.factorial n : ℝ)) := by
    intro α
    have h1 : Real.exp (-(β * layerDensSum ρ α u u'))
        = NormedSpace.exp (-(β * layerDensSum ρ α u u')) :=
      congrFun Real.exp_eq_exp_ℝ _
    rw [h1, congrFun (NormedSpace.exp_eq_tsum ℝ) _]
    apply tsum_congr
    intro n
    rw [neg_mul, smul_eq_mul, div_eq_inv_mul]
  have hSumm : Summable fun n => ∫ α,
        (-β * layerDensSum ρ α u u') ^ n / ((Nat.factorial n : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG) :=
    (summable_norm_term_int ρ μG hN hρcont β u u').of_norm_bounded
      (fun n => norm_integral_le_integral_norm _)
  have ht0 : (∫ α, (-β * layerDensSum ρ α u u') ^ 0 / ((Nat.factorial 0 : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG)) = 1 := by
    have hpt : ∀ α : LayerSite N → G,
        (-β * layerDensSum ρ α u u') ^ 0 / ((Nat.factorial 0 : ℝ)) = 1 :=
      fun α => by norm_num
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_const, probReal_univ, one_smul]
  have ht1 : (∫ α, (-β * layerDensSum ρ α u u') ^ 1 / ((Nat.factorial 1 : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = -β * betaCoeff1 ρ μG u u' := by
    have hpt : ∀ α : LayerSite N → G,
        (-β * layerDensSum ρ α u u') ^ 1 / ((Nat.factorial 1 : ℝ))
          = -β * layerDensSum ρ α u u' :=
      fun α => by
        simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_const_mul _ _
  have ht2 : (∫ α, (-β * layerDensSum ρ α u u') ^ 2 / ((Nat.factorial 2 : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = β ^ 2 * betaCoeff2 ρ μG u u' := by
    have hpt : ∀ α : LayerSite N → G,
        (-β * layerDensSum ρ α u u') ^ 2 / ((Nat.factorial 2 : ℝ))
          = β ^ 2 * ((layerDensSum ρ α u u') ^ 2 / 2) := by
      intro α
      have h2 : ((Nat.factorial 2 : ℝ)) = 2 := by norm_num [Nat.factorial]
      rw [h2]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_const_mul _ _
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
    ← (hasSum_integral_of_summable_integral_norm
      (fun n => integrable_term ρ μG hN hρcont β u u' n)
      (summable_norm_term_int ρ μG hN hρcont β u u')).tsum_eq,
    ← hSumm.sum_add_tsum_nat_add 3,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, ht0, ht1, ht2]
  ring

/-- **(S6) The expansion of `𝒜` itself** (the ℂ-valued
layer kernel is the cast of the real expansion). Same
fence: no positivity conclusion. -/
theorem layerKernel_expansion (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) :
    layerKernel μG ρ β u u'
      = ((1 - β * betaCoeff1 ρ μG u u' + β ^ 2 * betaCoeff2 ρ μG u u'
          + ∑' (k : ℕ), ∫ α, (-β * layerDensSum ρ α u u') ^ (k + 3)
              / ((Nat.factorial (k + 3) : ℝ))
              ∂(Measure.pi fun _ : LayerSite N => μG) : ℝ) : ℂ) := by
  have hreal : (∫ α, Real.exp (-(layerAction ρ β α u u'))
        ∂(Measure.pi fun _ : LayerSite N => μG))
      = ∫ α, Real.exp (-(β * layerDensSum ρ α u u'))
          ∂(Measure.pi fun _ : LayerSite N => μG) :=
    integral_congr_ae (Filter.Eventually.of_forall fun α => by
      show Real.exp (-(layerAction ρ β α u u'))
        = Real.exp (-(β * layerDensSum ρ α u u'))
      rw [layerAction_eq])
  calc layerKernel μG ρ β u u'
      = ((∫ α, Real.exp (-(layerAction ρ β α u u'))
          ∂(Measure.pi fun _ : LayerSite N => μG) : ℝ) : ℂ) := by
        show (∫ α, (Real.exp (-(layerAction ρ β α u u')) : ℂ)
            ∂(Measure.pi fun _ : LayerSite N => μG)) = _
        exact integral_ofReal
    _ = ((1 - β * betaCoeff1 ρ μG u u' + β ^ 2 * betaCoeff2 ρ μG u u'
          + ∑' (k : ℕ), ∫ α, (-β * layerDensSum ρ α u u') ^ (k + 3)
              / ((Nat.factorial (k + 3) : ℝ))
              ∂(Measure.pi fun _ : LayerSite N => μG) : ℝ) : ℂ) := by
        rw [hreal, layerKernel_real_expansion ρ μG hN hρcont β u u']

/-- **(S6) The tail bound:** `|R(β)| ≤ (2M|β|)³/6 ·
exp(2M|β|)`, from `(k+3)! ≥ 6·k!` termwise. So the
remainder is genuinely `O(β³)` as `β → 0`, with an
explicit constant. (Still no positivity conclusion.) -/
theorem layerKernel_tail_bound (hN : Even N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (u u' : LayerLink N → G) :
    ‖∑' (k : ℕ), ∫ α, (-β * layerDensSum ρ α u u') ^ (k + 3)
        / ((Nat.factorial (k + 3) : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG)‖
      ≤ (2 * colCount N * |β|) ^ 3 / 6
        * Real.exp (2 * colCount N * |β|) := by
  set X : ℝ := 2 * colCount N * |β| with hX
  have hc : (0 : ℝ) ≤ colCount N := Nat.cast_nonneg _
  have hXnn : 0 ≤ X :=
    mul_nonneg (mul_nonneg (by norm_num) hc) (abs_nonneg β)
  have hXeq : |β| * (2 * colCount N) = X := by rw [hX]; ring
  have hsumN : Summable fun k => ∫ α,
        ‖(-β * layerDensSum ρ α u u') ^ (k + 3) / ((Nat.factorial (k + 3) : ℝ))‖
        ∂(Measure.pi fun _ : LayerSite N => μG) :=
    (summable_nat_add_iff 3).mpr
      (summable_norm_term_int ρ μG hN hρcont β u u')
  have hsumN' : Summable fun k => ‖∫ α,
        (-β * layerDensSum ρ α u u') ^ (k + 3) / ((Nat.factorial (k + 3) : ℝ))
        ∂(Measure.pi fun _ : LayerSite N => μG)‖ :=
    hsumN.of_norm_bounded (fun k => by
      have h : ‖∫ α, (-β * layerDensSum ρ α u u') ^ (k + 3)
              / ((Nat.factorial (k + 3) : ℝ))
              ∂(Measure.pi fun _ : LayerSite N => μG)‖
          ≤ ∫ α, ‖(-β * layerDensSum ρ α u u') ^ (k + 3)
              / ((Nat.factorial (k + 3) : ℝ))‖
              ∂(Measure.pi fun _ : LayerSite N => μG) :=
        norm_integral_le_integral_norm _
      have h2 : ‖‖∫ α, (-β * layerDensSum ρ α u u') ^ (k + 3)
              / ((Nat.factorial (k + 3) : ℝ))
              ∂(Measure.pi fun _ : LayerSite N => μG)‖‖
          = ‖∫ α, (-β * layerDensSum ρ α u u') ^ (k + 3)
              / ((Nat.factorial (k + 3) : ℝ))
              ∂(Measure.pi fun _ : LayerSite N => μG)‖ :=
        Real.norm_of_nonneg (norm_nonneg _)
      rw [h2]
      exact h)
  have hfact : ∀ k : ℕ, (Nat.factorial (k + 3) : ℝ)
      = ((k : ℝ) + 1) * (((k : ℝ) + 2) * (((k : ℝ) + 3) * (Nat.factorial k : ℝ))) := by
    intro k
    have h : Nat.factorial (k + 3) = (k + 3) * ((k + 2) * ((k + 1) * Nat.factorial k)) := by
      simp only [Nat.factorial_succ]
    calc (Nat.factorial (k + 3) : ℝ)
        = (((k + 3) * ((k + 2) * ((k + 1) * Nat.factorial k)) : ℕ) : ℝ) := by rw [h]
      _ = ((k : ℝ) + 1) * (((k : ℝ) + 2) * (((k : ℝ) + 3) * (Nat.factorial k : ℝ))) := by
          push_cast
          ring
  have hterm : ∀ k : ℕ, X ^ (k + 3) / (Nat.factorial (k + 3) : ℝ)
      ≤ (X ^ 3 / 6) * (X ^ k / (Nat.factorial k : ℝ)) := by
    intro k
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h6 : (6 : ℝ) ≤ ((k : ℝ) + 1) * (((k : ℝ) + 2) * ((k : ℝ) + 3)) := by
      nlinarith [hk, sq_nonneg ((k : ℝ)),
        mul_nonneg hk (sq_nonneg ((k : ℝ)))]
    have hpos : (0 : ℝ) < (Nat.factorial (k + 3) : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hX3 : (0 : ℝ) ≤ X ^ 3 * X ^ k :=
      mul_nonneg (pow_nonneg hXnn 3) (pow_nonneg hXnn k)
    rw [div_le_iff₀ hpos]
    have hRHS : ((X ^ 3 / 6) * (X ^ k / (Nat.factorial k : ℝ))) * (Nat.factorial (k + 3) : ℝ)
        = (X ^ 3 / 6) * X ^ k
          * (((k : ℝ) + 1) * (((k : ℝ) + 2) * ((k : ℝ) + 3))) := by
      rw [hfact k]
      field_simp
    rw [hRHS]
    calc X ^ (k + 3) = X ^ 3 * X ^ k := by ring
      _ ≤ (X ^ 3 / 6) * X ^ k
            * (((k : ℝ) + 1) * (((k : ℝ) + 2) * ((k : ℝ) + 3))) := by
          have hP : (0 : ℝ) ≤ ((k : ℝ) + 1)
              * (((k : ℝ) + 2) * ((k : ℝ) + 3)) :=
            le_trans (by norm_num) h6
          have hrw : (X ^ 3 / 6) * X ^ k
                * (((k : ℝ) + 1) * (((k : ℝ) + 2) * ((k : ℝ) + 3)))
              = (X ^ 3 * X ^ k)
                * ((((k : ℝ) + 1) * (((k : ℝ) + 2) * ((k : ℝ) + 3))) / 6) := by
            ring
          rw [hrw]
          exact le_mul_of_one_le_right hX3
            ((one_le_div (by norm_num)).mpr h6)
  calc ‖∑' (k : ℕ), ∫ α, (-β * layerDensSum ρ α u u') ^ (k + 3)
          / ((Nat.factorial (k + 3) : ℝ)) ∂(Measure.pi fun _ : LayerSite N => μG)‖
      ≤ ∑' (k : ℕ), ‖∫ α, (-β * layerDensSum ρ α u u') ^ (k + 3)
          / ((Nat.factorial (k + 3) : ℝ)) ∂(Measure.pi fun _ : LayerSite N => μG)‖ :=
        norm_tsum_le_tsum_norm hsumN'
    _ ≤ ∑' (k : ℕ), ∫ α,
            ‖(-β * layerDensSum ρ α u u') ^ (k + 3) / ((Nat.factorial (k + 3) : ℝ))‖
            ∂(Measure.pi fun _ : LayerSite N => μG) :=
        hsumN'.tsum_le_tsum (fun k => norm_integral_le_integral_norm _) hsumN
    _ ≤ ∑' (k : ℕ), X ^ (k + 3) / (Nat.factorial (k + 3) : ℝ) :=
        hsumN.tsum_le_tsum
          (fun k => by
            calc ∫ α, ‖(-β * layerDensSum ρ α u u') ^ (k + 3)
                    / ((Nat.factorial (k + 3) : ℝ))‖
                    ∂(Measure.pi fun _ : LayerSite N => μG)
                ≤ ∫ _α : LayerSite N → G,
                    X ^ (k + 3) / ((Nat.factorial (k + 3) : ℝ))
                    ∂(Measure.pi fun _ : LayerSite N => μG) :=
                  integral_mono_ae
                    (integrable_term ρ μG hN hρcont β u u' (k + 3)).norm
                    (integrable_const _)
                    (Filter.Eventually.of_forall fun α => by
                      have hb := norm_term_le ρ hN β u u' (k + 3) α
                      rwa [hXeq] at hb)
              _ = X ^ (k + 3) / ((Nat.factorial (k + 3) : ℝ)) := by
                  rw [integral_const, probReal_univ, one_smul])
          ((summable_nat_add_iff 3).mpr (Real.summable_pow_div_factorial X))
    _ ≤ ∑' (k : ℕ), (X ^ 3 / 6) * (X ^ k / (Nat.factorial k : ℝ)) :=
        ((summable_nat_add_iff 3).mpr
          (Real.summable_pow_div_factorial X)).tsum_le_tsum hterm
          ((Real.summable_pow_div_factorial X).mul_left _)
    _ = (X ^ 3 / 6) * Real.exp X := by
        rw [tsum_mul_left]
        congr 1
        have h1 : Real.exp X = NormedSpace.exp X :=
          congrFun Real.exp_eq_exp_ℝ _
        rw [h1, congrFun (NormedSpace.exp_eq_tsum ℝ) _]
        apply tsum_congr
        intro n
        rw [smul_eq_mul, div_eq_inv_mul]

end Expansion

end ThetLogos
