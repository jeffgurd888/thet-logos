/-
# Assembly, part 1: instantiation + features (Route B, step T4a)

Companion brick to the Gram-clause campaign (Pitch 4, Stage 1b-B).
Charter: `whitepaper/gram-clause-scoping-2026-10-23.md`, §4 Route B,
step **T4** — split by the parent into **T4a** (this module:
instantiation + features) and **T4b** (series domination + the final
discharge through the integrated criterion). Steps T1 (the
integrated criterion, `ThetLogos.LatticeGramSeries`), T2 (the
averaging projection, `ThetLogos.AveragingProjection`) and T3 (the
word/tensor bookkeeping, `ThetLogos.GramWordTensor`) are landed.

## Content

* **Instantiation.** The stratum of the closed half is
  `stratumLinks = halfLinks ∩ planeLinks`; the closed half splits as
  `halfLinks = posLinks ∪ stratumLinks` (disjoint), and the split is
  a measure-preserving measurable equiv at the corpus's Haar
  probability `haarProb G`. T3's two integral headlines are
  specialized to this stratum group and measure: a stratum word
  entry integrates to T3's `A`-coefficient (`stratum_integral_word_entry`).
* **Features.** For one crossing-word datum (length, slot map into
  the stratum, sign flags, endpoints) and a strict-half scalar
  factor `φ₀`, the positive-half feature is
  `featA y = φ₀ (restrictPos y) · (word entry at stratPart y)` —
  continuous (a polynomial in link entries), bounded by `‖φ₀‖∞`
  (unitary entries have norm `≤ 1`), and its stratum marginal is
  the criterion's `hmargA` shape with damping factor `1` and
  strict-half feature `featXi z = γ • φ₀ z`, where `γ` is T3's
  `A`-coefficient of the word (`featA_marginal`).

## What remains for T4b

The concrete crossing features from the expansion of
`exp (-S₀)` (the plaquette word data and sandwich factors of
`wilsonActionZero`), the common-feature identification of the two
marginals under the reflection, the Gram series identity `hgram`,
the domination `hsum`, and the final application of
`osForm_nonneg_of_gram_integrated`.

## Fences

Finite volume only; the corpus's unitary-valued `ρ` throughout
(tensor unitarity definitional); `β` appears only as the criterion
carries it — no sign condition is used in this module. **NO CLAIM**
— parts of any official Clay statement closed by this module: 0.
-/

import ThetLogos.LatticeGramSeries
import ThetLogos.LatticePositivity
import ThetLogos.GramWordTensor
import ThetLogos.AveragingProjection

open MeasureTheory
open scoped InnerProductSpace

namespace ThetLogos

namespace GramAssembly

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] [CompactSpace G] [LocallyCompactSpace G]
  {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- The **plane stratum inside the closed half**: the plane links
that lie in `halfLinks` (the time links based at `N/2 - 1`). These
are the free variables of the closed half once the strict half
`posLinks` is fixed. -/
def stratumLinks : Finset (Link (Fin 4 → ZMod N)) :=
  halfLinks ∩ planeLinks

theorem mem_stratumLinks {ℓ : Link (Fin 4 → ZMod N)} :
    ℓ ∈ stratumLinks (N := N) ↔ (ℓ.1 0).val < N / 2 ∧ reflLink ℓ = ℓ := by
  simp [stratumLinks, mem_halfLinks, mem_planeLinks]

theorem stratumLinks_subset_halfLinks :
    stratumLinks (N := N) ⊆ halfLinks := fun ℓ hℓ =>
  (Finset.mem_inter.mp hℓ).1

/-- The closed half is the disjoint union of the strict half and
the stratum. -/
theorem posLinks_union_stratumLinks :
    posLinks (N := N) ∪ stratumLinks = halfLinks := by
  ext ℓ
  simp only [Finset.mem_union, mem_posLinks, mem_stratumLinks, mem_halfLinks]
  constructor
  · rintro (⟨h1, -⟩ | ⟨h1, -⟩) <;> exact h1
  · intro h1
    by_cases h2 : reflLink ℓ = ℓ
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩

theorem disjoint_posLinks_stratumLinks :
    Disjoint (posLinks (N := N)) (stratumLinks) := by
  rw [Finset.disjoint_left]
  intro ℓ hℓ hℓ'
  exact (mem_posLinks.mp hℓ).2 (mem_stratumLinks.mp hℓ').2

/-- The index equiv between the closed half and the disjoint union
of the strict half and the stratum (a plain equiv, so its
components compute). -/
def halfIndexEquiv :
    ↥(posLinks (N := N) ∪ stratumLinks) ≃ ↥(halfLinks (N := N)) :=
  ⟨fun x => ⟨x.1, by rw [← posLinks_union_stratumLinks]; exact x.2⟩,
   fun x => ⟨x.1, by rw [posLinks_union_stratumLinks]; exact x.2⟩,
   fun x => Subtype.ext rfl, fun x => Subtype.ext rfl⟩

/-- The stratum part of a closed-half configuration. -/
def stratPart (y : ↥(halfLinks (N := N)) → G) :
    ↥(stratumLinks (N := N)) → G :=
  fun ℓ => y ⟨ℓ.1, stratumLinks_subset_halfLinks ℓ.2⟩

/-- **The half split**: a closed-half configuration is the pair of
its strict-half restriction and its stratum part, as a measurable
equiv (the corpus's `splitEquiv` pattern at the finset level). -/
noncomputable def splitHalfEquiv :
    (↥(halfLinks (N := N)) → G) ≃ᵐ
      ((↥(posLinks (N := N)) → G) × (↥(stratumLinks (N := N)) → G)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : ↥(halfLinks (N := N)) => G)
    halfIndexEquiv).symm.trans
    (MeasurableEquiv.piFinsetUnion (fun _ : Link (Fin 4 → ZMod N) => G)
      disjoint_posLinks_stratumLinks).symm

theorem splitHalfEquiv_fst (y : ↥(halfLinks (N := N)) → G) :
    (splitHalfEquiv y).1 = restrictPos y := by
  funext ℓ
  rfl

theorem splitHalfEquiv_snd (y : ↥(halfLinks (N := N)) → G) :
    (splitHalfEquiv y).2 = stratPart y := by
  funext ℓ
  rfl

/-- The half split preserves the product Haar measure. -/
theorem measurePreserving_splitHalfEquiv (μG : Measure G)
    [IsProbabilityMeasure μG] :
    MeasurePreserving (splitHalfEquiv (N := N)) (Measure.pi fun _ : ↥(halfLinks (N := N)) => μG)
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(stratumLinks (N := N)) => μG)) :=
  (measurePreserving_piFinsetUnion disjoint_posLinks_stratumLinks
    (fun _ : Link (Fin 4 → ZMod N) => μG)).symm.comp
    (measurePreserving_piCongrLeft (fun _ : ↥(halfLinks (N := N)) => μG)
      halfIndexEquiv).symm

/-! ## §2. Instantiation at `haarProb G`: T3 on the corpus stratum -/

/-- **T3 headline 1 at the corpus stratum**: an occurrence
coefficient of the stratum product group `(↥stratumLinks → G)`,
integrated against the product Haar probability, is T2's averaging
operator applied to the joint occurrence CLM. -/
theorem stratum_integral_occMat {κ : Type*} [Fintype κ] [DecidableEq κ]
    (slot : κ → ↥(stratumLinks (N := N)))
    (Ψ : κ → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
    (hΨcont : ∀ occ, Continuous fun g : G => repMatrix (Ψ occ) g)
    (A B : κ → Fin d) :
    (∫ s, GramWordTensor.occMat slot Ψ s A B
      ∂(Measure.pi fun _ : ↥(stratumLinks (N := N)) => haarProb G))
    = ⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) A,
        AveragingProjection.averagingOperator
          (Measure.pi fun _ : ↥(stratumLinks (N := N)) => haarProb G)
          (GramWordTensor.occRepCLM slot Ψ)
          (GramWordTensor.occRepCLM_continuous slot Ψ hΨcont)
          (GramWordTensor.occRepCLM_unitary slot Ψ)
          ((EuclideanSpace.basisFun (κ → Fin d) ℂ) B)⟫_ℂ :=
  GramWordTensor.integral_occMat_eq_averaging (μG := haarProb G)
    slot Ψ hΨcont A B

/-- The **word entry** as a function of the stratum configuration:
the `(a, b)` entry of the representation matrix of the stratum
word. This is the integrand of `wordGamma`. -/
def wordEntry {n : ℕ} (slot : Fin n → ↥(stratumLinks (N := N)))
    (flag : Fin n → Bool) (a b : Fin d)
    (s : ↥(stratumLinks (N := N)) → G) : ℂ :=
  (repMatrix ρ (GramWordTensor.wordGroup
    (fun j => if flag j then s (slot j) else (s (slot j))⁻¹))) a b

/-- **T3's `A`-coefficient of a stratum word**: the stratum integral
of the word entry — a bare complex number, defined as the integral
and computed by `wordGamma_eq` as T3's finite path sum of
averaging-operator coefficients. -/
noncomputable def wordGamma {n : ℕ}
    (slot : Fin n → ↥(stratumLinks (N := N))) (flag : Fin n → Bool)
    (a b : Fin d) : ℂ :=
  ∫ s, wordEntry ρ slot flag a b s
    ∂(Measure.pi fun _ : ↥(stratumLinks (N := N)) => haarProb G)

/-- **T3 headline 2 at the corpus stratum**: the `A`-coefficient is
the finite path sum of T2-averaging coefficients at the path
endpoints. -/
theorem wordGamma_eq {n : ℕ}
    (slot : Fin n → ↥(stratumLinks (N := N))) (flag : Fin n → Bool)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (a b : Fin d) :
    wordGamma ρ slot flag a b
    = ∑ p : Fin (n + 1) → Fin d,
        (if p 0 = a ∧ p (Fin.last n) = b then
          ⟪(EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
              (GramWordTensor.pathA flag p),
            AveragingProjection.averagingOperator
              (Measure.pi fun _ : ↥(stratumLinks (N := N)) => haarProb G)
              (GramWordTensor.occRepCLM slot
                (fun j => GramWordTensor.flavRep ρ (flag j)))
              (GramWordTensor.occRepCLM_continuous slot _
                (fun j => GramWordTensor.flavRep_continuous ρ flag
                  hρcont j))
              (GramWordTensor.occRepCLM_unitary slot _)
              ((EuclideanSpace.basisFun (Fin n → Fin d) ℂ)
                (GramWordTensor.pathB flag p))⟫_ℂ
        else 0) :=
  GramWordTensor.integral_word_entry (μG := haarProb G) (ρ := ρ)
    slot flag hρcont a b

/-! ## §3. Word-entry analysis: continuity and the unit bound -/

/-- Entries of a unitary matrix have norm `≤ 1` (a row of `M * star M`
is a unit vector). -/
theorem repMatrix_entry_norm_le_one (g : G) (a b : Fin d) :
    ‖(repMatrix ρ g) a b‖ ≤ 1 := by
  have hM : repMatrix ρ g * star (repMatrix ρ g) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (repMatrix_mem ρ g)
  have hbb : ∑ k, (repMatrix ρ g) a k * star ((repMatrix ρ g) a k)
      = 1 := by
    have h := congrFun (congrFun hM a) a
    simpa only [Matrix.mul_apply, Matrix.star_apply,
      Matrix.one_apply_eq] using h
  have hterm : ∀ k, (repMatrix ρ g) a k * star ((repMatrix ρ g) a k)
      = ((‖(repMatrix ρ g) a k‖ : ℂ) ^ 2) :=
    fun k => RCLike.mul_conj _
  rw [Finset.sum_congr rfl (fun k _ => hterm k)] at hbb
  have hsum : ∑ k, ‖(repMatrix ρ g) a k‖ ^ 2 = 1 := by
    have h2 : ((∑ k, ‖(repMatrix ρ g) a k‖ ^ 2 : ℝ) : ℂ) = 1 := by
      push_cast
      exact hbb
    exact Complex.ofReal_injective h2
  have hle : ‖(repMatrix ρ g) a b‖ ^ 2 ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum
      (f := fun k => ‖(repMatrix ρ g) a k‖ ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ b)
  have hle' : ‖(repMatrix ρ g) a b‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
    simpa using hle
  have habs := abs_le_of_sq_le_sq hle' (by norm_num)
  rw [abs_of_nonneg (norm_nonneg _)] at habs
  simpa using habs

/-- Finite products of continuous factors are continuous, in the
ordered (`List.ofFn`) form used by `wordGroup`. -/
theorem continuous_prod_ofFn {ι : Type*} :
    ∀ {n : ℕ} (φ : Fin n → (ι → G) → G), (∀ j, Continuous (φ j)) →
      Continuous fun s : ι → G => (List.ofFn (fun j => φ j s)).prod
  | 0, φ, _ => by
      simp only [List.ofFn_zero, List.prod_nil]
      exact continuous_const
  | n + 1, φ, hφ => by
      have e : (fun s : ι → G => (List.ofFn (fun j => φ j s)).prod)
          = fun s => φ 0 s
            * (List.ofFn (fun j : Fin n => φ j.succ s)).prod :=
        funext fun s => by rw [List.ofFn_succ, List.prod_cons]
      rw [e]
      exact (hφ 0).mul
        (continuous_prod_ofFn (fun j => φ j.succ) (fun j => hφ j.succ))

/-- The stratum word, as a group element, depends continuously on
the stratum configuration. -/
theorem continuous_wordGroup {ι : Type*} {n : ℕ}
    (slot : Fin n → ι) (flag : Fin n → Bool) :
    Continuous fun s : ι → G => GramWordTensor.wordGroup
      (fun j => if flag j then s (slot j) else (s (slot j))⁻¹) := by
  refine continuous_prod_ofFn
    (fun j s => if flag j then s (slot j) else (s (slot j))⁻¹) fun j => ?_
  show Continuous fun s : ι → G =>
    if flag j then s (slot j) else (s (slot j))⁻¹
  by_cases hf : flag j = true
  · rw [show (fun s : ι → G => if flag j then s (slot j)
        else (s (slot j))⁻¹) = fun s => s (slot j) from
      funext fun s => if_pos hf]
    exact continuous_apply (slot j)
  · rw [show (fun s : ι → G => if flag j then s (slot j)
        else (s (slot j))⁻¹) = fun s => (s (slot j))⁻¹ from
      funext fun s => if_neg hf]
    exact (continuous_apply (slot j)).inv

/-- The word entry is continuous in the stratum configuration (a
polynomial in the link entries, through `repMatrix`). -/
theorem wordEntry_continuous {n : ℕ}
    (slot : Fin n → ↥(stratumLinks (N := N))) (flag : Fin n → Bool)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (a b : Fin d) :
    Continuous (wordEntry ρ slot flag a b) := by
  have hentry : Continuous fun M : Matrix (Fin d) (Fin d) ℂ => M a b :=
    (continuous_apply b).comp (continuous_apply a)
  exact hentry.comp (hρcont.comp (continuous_wordGroup slot flag))

/-- The word entry is bounded by `1` (unitarity). -/
theorem wordEntry_norm_le_one {n : ℕ}
    (slot : Fin n → ↥(stratumLinks (N := N))) (flag : Fin n → Bool)
    (a b : Fin d) (s : ↥(stratumLinks (N := N)) → G) :
    ‖wordEntry ρ slot flag a b s‖ ≤ 1 :=
  repMatrix_entry_norm_le_one ρ _ a b

/-! ## §4. Features on the positive half, and the A-side marginal -/

/-- Restriction to the positive links is continuous. -/
theorem continuous_restrictPos :
    Continuous fun y : ↥(halfLinks (N := N)) → G => restrictPos y :=
  continuous_pi fun ℓ => continuous_apply _

/-- The stratum part is continuous. -/
theorem continuous_stratPart :
    Continuous fun y : ↥(halfLinks (N := N)) → G => stratPart y :=
  continuous_pi fun ℓ => continuous_apply _

/-- **The positive-half feature of one crossing-word datum**
(the criterion's `𝒜`-side feature shape): a positive-half
observable `φ₀` times the word entry of the stratum part. -/
def featA {n : ℕ} (slot : Fin n → ↥(stratumLinks (N := N)))
    (flag : Fin n → Bool) (a b : Fin d)
    (φ₀ : (↥(posLinks (N := N)) → G) → ℂ)
    (y : ↥(halfLinks (N := N)) → G) : ℂ :=
  φ₀ (restrictPos y) * wordEntry ρ slot flag a b (stratPart y)

/-- **The strict-half feature of one crossing-word datum**
(the criterion's `Ξ`-side shape): the `A`-coefficient of the word
times the observable. -/
noncomputable def featXi {n : ℕ} (slot : Fin n → ↥(stratumLinks (N := N)))
    (flag : Fin n → Bool) (a b : Fin d)
    (φ₀ : (↥(posLinks (N := N)) → G) → ℂ)
    (z : ↥(posLinks (N := N)) → G) : ℂ :=
  wordGamma ρ slot flag a b * φ₀ z

/-- Features are continuous (polynomials in the link entries,
through `repMatrix`). -/
theorem featA_continuous {n : ℕ}
    (slot : Fin n → ↥(stratumLinks (N := N))) (flag : Fin n → Bool)
    (a b : Fin d) (φ₀ : (↥(posLinks (N := N)) → G) → ℂ)
    (hφ₀ : Continuous φ₀)
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    Continuous (featA ρ slot flag a b φ₀) :=
  (hφ₀.comp continuous_restrictPos).mul
    ((wordEntry_continuous ρ slot flag hρcont a b).comp
      continuous_stratPart)

/-- Features are bounded by the observable's bound (the word entry
contributes a factor `≤ 1`). -/
theorem featA_norm_le {n : ℕ}
    (slot : Fin n → ↥(stratumLinks (N := N))) (flag : Fin n → Bool)
    (a b : Fin d) (φ₀ : (↥(posLinks (N := N)) → G) → ℂ)
    {Cφ : ℝ} (hφ₀ : ∀ z, ‖φ₀ z‖ ≤ Cφ)
    (y : ↥(halfLinks (N := N)) → G) :
    ‖featA ρ slot flag a b φ₀ y‖ ≤ Cφ := by
  have h1 : ‖φ₀ (restrictPos y)
      * wordEntry ρ slot flag a b (stratPart y)‖
      = ‖φ₀ (restrictPos y)‖
        * ‖wordEntry ρ slot flag a b (stratPart y)‖ := norm_mul _ _
  rw [featA, h1]
  have h2 := mul_le_mul (hφ₀ (restrictPos y))
    (wordEntry_norm_le_one ρ slot flag a b (stratPart y))
    (norm_nonneg _) (le_trans (norm_nonneg _) (hφ₀ (restrictPos y)))
  simpa using h2

/-- Features are almost-everywhere strongly measurable against the
positive-half product measure (the criterion's `hAA`-side shape,
per feature). -/
theorem featA_aestronglyMeasurable {n : ℕ}
    (slot : Fin n → ↥(stratumLinks (N := N))) (flag : Fin n → Bool)
    (a b : Fin d) (φ₀ : (↥(posLinks (N := N)) → G) → ℂ)
    (hφ₀ : Continuous φ₀)
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    AEStronglyMeasurable (featA ρ slot flag a b φ₀)
      (Measure.pi fun _ : ↥(halfLinks (N := N)) => haarProb G) :=
  (featA_continuous ρ slot flag a b φ₀ hφ₀ hρcont).aestronglyMeasurable

/-- **The A-side marginal (the criterion's `hmargA` shape, for one
word datum, per-word factor `dA = 1`)**: integrating the feature
against a positive-half observable over the positive half leaves
the strict-half feature paired with the same observable. The
transport is `splitHalfEquiv` at `haarProb`; factorization is
`integral_prod_mul` (unconditional, junk-value convention); the
stratum integral is, by definition, `wordGamma`. -/
theorem featA_marginal {n : ℕ}
    (slot : Fin n → ↥(stratumLinks (N := N))) (flag : Fin n → Bool)
    (a b : Fin d) (φ₀ : (↥(posLinks (N := N)) → G) → ℂ)
    (f : (↥(posLinks (N := N)) → G) → ℂ) :
    ∫ y, featA ρ slot flag a b φ₀ y * f (restrictPos y)
        ∂(Measure.pi fun _ : ↥(halfLinks (N := N)) => haarProb G)
      = ((1 : ℝ) : ℂ) * ∫ z, featXi ρ slot flag a b φ₀ z * f z
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G) := by
  classical
  have hcomp : ∫ y, featA ρ slot flag a b φ₀ y * f (restrictPos y)
        ∂(Measure.pi fun _ : ↥(halfLinks (N := N)) => haarProb G)
      = ∫ y, (φ₀ ((splitHalfEquiv y).1) * f ((splitHalfEquiv y).1))
          * wordEntry ρ slot flag a b (splitHalfEquiv y).2
        ∂(Measure.pi fun _ : ↥(halfLinks (N := N)) => haarProb G) := by
    congr 1
    funext y
    show featA ρ slot flag a b φ₀ y * f (restrictPos y)
      = (φ₀ ((splitHalfEquiv y).1)
          * f ((splitHalfEquiv y).1))
        * wordEntry ρ slot flag a b (splitHalfEquiv y).2
    rw [splitHalfEquiv_fst, splitHalfEquiv_snd]
    simp only [featA]
    ring
  calc ∫ y, featA ρ slot flag a b φ₀ y * f (restrictPos y)
          ∂(Measure.pi fun _ : ↥(halfLinks (N := N)) => haarProb G)
      = ∫ y, (φ₀ ((splitHalfEquiv y).1) * f ((splitHalfEquiv y).1))
          * wordEntry ρ slot flag a b (splitHalfEquiv y).2
          ∂(Measure.pi fun _ : ↥(halfLinks (N := N)) => haarProb G) :=
        hcomp
    _ = ∫ p, (φ₀ p.1 * f p.1) * wordEntry ρ slot flag a b p.2
          ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G).prod
            (Measure.pi fun _ : ↥(stratumLinks (N := N))
              => haarProb G)) := by
        rw [← (measurePreserving_splitHalfEquiv (haarProb G)).integral_comp
          (MeasurableEquiv.measurableEmbedding _)
          (fun p : (↥(posLinks (N := N)) → G)
            × (↥(stratumLinks (N := N)) → G) => (φ₀ p.1 * f p.1)
            * wordEntry ρ slot flag a b p.2)]
    _ = (∫ z, φ₀ z * f z
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G))
        * wordGamma ρ slot flag a b :=
        MeasureTheory.integral_prod_mul (fun z => φ₀ z * f z)
          (wordEntry ρ slot flag a b)
    _ = ((1 : ℝ) : ℂ) * ∫ z, featXi ρ slot flag a b φ₀ z * f z
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G) := by
        have e : (∫ z, featXi ρ slot flag a b φ₀ z * f z
              ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G))
            = wordGamma ρ slot flag a b * ∫ z, φ₀ z * f z
              ∂(Measure.pi fun _ : ↥(posLinks (N := N))
                => haarProb G) := by
          rw [show (fun z => featXi ρ slot flag a b φ₀ z * f z)
              = fun z => wordGamma ρ slot flag a b * (φ₀ z * f z) from
            funext fun z => by simp only [featXi]; ring]
          exact MeasureTheory.integral_const_mul _ _
        rw [e, Complex.ofReal_one, one_mul, mul_comm]

/-! ## §5. The B-side marginal: split verdict (scoped, not built)

The criterion's second marginal (`hmargB`) pairs features
`B i : (↥(negLinks) → G) → ℂ` on the *negative* half with the
*same* strict-half features `Ξ i`, through the corpus's mirror
map `mirrorP hN : (↥(negLinks) → G) → (↥(posLinks) → G)`
(measure-preserving: `measurePreserving_mirrorP`, landed with
the criterion). Mirroring §1–§4 to the negative half is a second
construction of the same size; it is NOT built in T4a. The exact
missing pieces, in dependency order, are:

1. **Mirror stratum anatomy** (mechanical mirror of §1):
   `negStratumLinks` (the stratum links seen from the negative
   half) and a measure-preserving
   `splitNegEquiv : (↥(negLinks (N := N)) → G) ≃ᵐ
     (↥(mirrorStrictLinks) → G) × (↥(negStratumLinks) → G)`
   at `haarProb G`, splitting off the mirror of `posLinks`.
2. **The dual-word `γ` identity** (the content): for the mirror
   word datum — slots transported by the mirror, flags flipped
   under `Fin.rev` order-reversal, endpoints swapped — the
   conjugated stratum integral of the dual word entry equals the
   A-side coefficient:
   `∫ u, (starRingEnd ℂ) (wordEntry ρ slotᴮ flagᴮ b a u)
      = wordGamma ρ slot flag a b`.
   Its proof needs `mirrorP`'s linkwise definition, T3 applied
   to the dual word, self-adjointness of `A` (T2), and
   `integral_conj`. This identity is what forces the *same* `Ξ`
   out of both marginals.
3. **`featB` and `featB_marginal`** (mirror of §4, given 1–2):
   the `hmargB` shape with damping factor `dB = 1`, plus the
   `hBA`/`hBB`-side measurability and bound, which mirror
   `featA_aestronglyMeasurable` / `featA_norm_le`.

T4b consumes: §2 (`wordGamma_eq`), §4 (`featA_marginal`,
`featA_aestronglyMeasurable`, `featA_norm_le`) for the A family;
items 1–3 above for the B family; then the word-data family
from the `exp (-S₀)` expansion, `hgram`, `hsum`, and the final
application of `osForm_nonneg_of_gram_integrated`. -/

end GramAssembly

end ThetLogos
