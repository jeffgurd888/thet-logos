/-
# Assembly, part 1′: occurrence features (Route B, step T4a′)

Companion brick to the Gram-clause campaign (Pitch 4, Stage 1b-B).
Charter: the T4c obstruction dossier
(`whitepaper/gram-route-b-t4c-obstruction-2026-10-23.md`) and its §4
repair pricing. Steps T4a (`ThetLogos.GramAssembly` — instantiation
+ word-entry features) and T4b (the mirror side) stand entire; the
word-entry closer T4c stopped on a proved obstruction: a crossing
plaquette's closed-half arc is a **stratum · strict · stratum
sandwich**, whose monomials are *occurrence* (tensor) coefficients,
not word entries, so the pointwise Gram identity fails for the
word-entry family. This module builds the repair's A side:
occurrence features, following the obstruction memo's §4.

## Content

* **The arc datum (§1).** Per crossing plaquette at the lower
  plane, the two-slot occurrence datum on the corpus stratum:
  slots `(linkC, linkA)` into `↥stratumLinks`, flavors
  `(flavRep ρ false, flavRep ρ true)` (the `C` factor enters
  inverted, the `A` factor direct). The endpoint convention is
  pinned by proof (`occArc_apply`): at endpoint functions
  `(![k, a], ![j, i])` the occurrence coefficient is the arc
  monomial `(ρC⁻¹)_{j k} · (ρA)_{a i}` — the pair `(k, a)` is
  exactly the strict factor's index pair, carried by `φ₀` (§3);
  `(j, i)` is the negative-half pair. Tensor powers are the same
  datum over `Fin k × Fin 2` (`arcSlotPow`, `arcΨPow`): the generic
  features of §2 quantify over all occurrence data, so the closer
  (T4c′) instantiates them per plaquette and per tensor power.
* **Occurrence features (§2).** For a general occurrence datum
  `(κ, slot, Ψ, A, B)` and a strict-half scalar factor `φ₀`, the
  positive-half feature `featAOcc y = φ₀ (restrictPos y) ·
  (occMat coefficient at stratPart y)` — continuous, bounded by
  `‖φ₀‖∞` (an occurrence coefficient is a product of unitary
  entries, each of norm `≤ 1`), with stratum marginal in the
  criterion's `hmargA` shape at damping factor `1` and strict-half
  feature `featXiOcc z = γᵒᶜᶜ • φ₀ z`, where `γᵒᶜᶜ` is the
  averaging coefficient of the datum, computed by the landed
  `GramAssembly.stratum_integral_occMat`. The marginal's proof is
  T4a's template verbatim — it never used word-ness.
* **The strict factor `φ₀ᴰ` (§3).** The concrete scalar factor of
  one crossing plaquette:
  `φ₀ᴰ(z) = (repMatrix ρ ((z at linkD)⁻¹))_{k a} ·
  exp (−halfActionP ρ β z) · (series weight)^{1/2}`, in the
  obstruction memo's shape. **Design decision (documented, per the
  brief):** the series weight enters as an explicit real parameter
  `w : ℝ` (the closer instantiates `w` per tensor power from the
  exponential series); its square root enters as a real cast.
  `φ₀ᴰ` is strongly measurable (the strict action is measurable:
  §3's `measurable_halfActionP`, from the landed entry
  measurability), and `‖φ₀ᴰ z‖ ≤ √w · exp (−halfActionP ρ β z)`
  with **no** sign condition on `β`.

## What remains

T4b′ (the B side, via the landed occMat dual transport
`GramMirror.integral_occMat_dual` / `coeff_dual`), then T4c′ (the
closer on the `ᵒᶜᶜ` family: assembly, `hgram` by construction,
`hsum`, discharge). This module does no B side, no series
assembly, no domination, and no discharge.

## Fences

Finite volume only; the corpus's unitary-valued `ρ` throughout.
**NO CLAIM** — parts of any official Clay statement closed by
this module: 0.
-/

import ThetLogos.GramAssembly

open MeasureTheory
open scoped InnerProductSpace

namespace ThetLogos

namespace GramAssemblyOcc

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] [CompactSpace G] [LocallyCompactSpace G]
  {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-! ## §1. The arc datum of a crossing plaquette -/

/-- The **flavor pattern of the arc datum**: slot `0` (the `C`
factor) enters inverted — the conjugate flavor; slot `1` (the `A`
factor) enters direct. -/
def arcFlag : Fin 2 → Bool := ![false, true]

/-- The **flavor family of the arc datum**: per-slot representations
`flavRep ρ false` (at `linkC`) and `flavRep ρ true` (at `linkA`). -/
def arcΨ : Fin 2 → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ) :=
  fun j => GramWordTensor.flavRep ρ (arcFlag j)

/-- The arc flavor family is continuous in the group element, per
slot (T3's `flavRep_continuous` verbatim). -/
theorem arcΨ_continuous
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    ∀ occ, Continuous fun g : G => repMatrix (arcΨ ρ occ) g :=
  fun occ => GramWordTensor.flavRep_continuous ρ arcFlag hρcont occ

/-- Slot `0` of the arc flavor family is the conjugated
representation (the `flavRep ρ false` seat at `linkC`). -/
theorem arcΨ_zero : arcΨ ρ 0 = GramWordTensor.conjRep ρ := rfl

/-- Slot `1` of the arc flavor family is `ρ` itself (the
`flavRep ρ true` seat at `linkA`). -/
theorem arcΨ_one : arcΨ ρ 1 = ρ := rfl

section Plaquette

variable {p : (Fin 4 → ZMod N) × Fin 4 × Fin 4}

/-- The **slot map of the arc datum**: slot `0` is `linkC`, slot `1`
is `linkA`, as elements of the corpus stratum. -/
def arcSlot (hpC : linkC p ∈ GramAssembly.stratumLinks (N := N))
    (hpA : linkA p ∈ GramAssembly.stratumLinks (N := N)) :
    Fin 2 → ↥(GramAssembly.stratumLinks (N := N)) :=
  ![⟨linkC p, hpC⟩, ⟨linkA p, hpA⟩]

/-- At the lower plane, `linkA` lies in the stratum (the corpus's
link pattern, `zero_link_pattern`). -/
theorem linkA_mem_stratumLinks (hN : Even N) (hp : p ∈ zeroFinset)
    (hlow : (p.1 0).val = N / 2 - 1) :
    linkA p ∈ GramAssembly.stratumLinks (N := N) := by
  rcases zero_link_pattern hN p hp with h | h
  · exact Finset.mem_inter.mpr ⟨h.2.1, h.2.2.1⟩
  · exfalso
    obtain ⟨r, hr⟩ := hN
    have hN0 : N ≠ 0 := NeZero.ne N
    omega

/-- At the lower plane, `linkC` lies in the stratum. -/
theorem linkC_mem_stratumLinks (hN : Even N) (hp : p ∈ zeroFinset)
    (hlow : (p.1 0).val = N / 2 - 1) :
    linkC p ∈ GramAssembly.stratumLinks (N := N) := by
  rcases zero_link_pattern hN p hp with h | h
  · exact Finset.mem_inter.mpr ⟨h.2.2.2.1, h.2.2.2.2.1⟩
  · exfalso
    obtain ⟨r, hr⟩ := hN
    have hN0 : N ≠ 0 := NeZero.ne N
    omega

/-- At the lower plane, `linkD` lies in the strict half (it carries
the strict factor of the sandwich). -/
theorem linkD_mem_posLinks (hN : Even N) (hp : p ∈ zeroFinset)
    (hlow : (p.1 0).val = N / 2 - 1) :
    linkD p ∈ posLinks (N := N) := by
  rcases zero_link_pattern hN p hp with h | h
  · exact h.2.2.2.2.2.1
  · exfalso
    obtain ⟨r, hr⟩ := hN
    have hN0 : N ≠ 0 := NeZero.ne N
    omega

/-- **The endpoint convention, pinned by proof**: the occurrence
coefficient of the arc datum at endpoint functions
`(![k, a], ![j, i])` is the arc monomial
`(ρC⁻¹)_{j k} · (ρA)_{a i}` — the two stratum factors share no
index; they are joined only through the strict factor
`(ρD⁻¹)_{k a}` carried by `φ₀ᴰ` (§3), whose index pair is exactly
`(k, a)`. -/
theorem occArc_apply (hpC : linkC p ∈ GramAssembly.stratumLinks (N := N))
    (hpA : linkA p ∈ GramAssembly.stratumLinks (N := N))
    (k a j i : Fin d) (s : ↥(GramAssembly.stratumLinks (N := N)) → G) :
    GramWordTensor.occMat (arcSlot hpC hpA) (arcΨ ρ) s ![k, a] ![j, i]
      = (repMatrix ρ (s ⟨linkC p, hpC⟩)⁻¹) j k
        * (repMatrix ρ (s ⟨linkA p, hpA⟩)) a i := by
  rw [GramWordTensor.occMat_apply, Fin.prod_univ_two]
  simp only [arcSlot, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [arcΨ_zero, arcΨ_one, ← GramWordTensor.repMatrix_inv_entry]

/-- The **power-`k` slot datum**: the arc slots repeated along
`Fin k` (the occurrence datum of the `k`-th tensor power of one
crossing plaquette's Boltzmann factor). Data only — the generic
features of §2 quantify over it. -/
def arcSlotPow (hpC : linkC p ∈ GramAssembly.stratumLinks (N := N))
    (hpA : linkA p ∈ GramAssembly.stratumLinks (N := N)) (k : ℕ) :
    Fin k × Fin 2 → ↥(GramAssembly.stratumLinks (N := N)) :=
  fun q => arcSlot hpC hpA q.2

/-- The **power-`k` flavor datum**, companion to `arcSlotPow`. -/
def arcΨPow (k : ℕ) :
    Fin k × Fin 2 → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ) :=
  fun q => arcΨ ρ q.2

end Plaquette

/-! ## §2. Occurrence features on the positive half -/

section OccFeatures

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
  (slot : κ → ↥(GramAssembly.stratumLinks (N := N)))
  (Ψ : κ → G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  (A B : κ → Fin d)

/-- The **occurrence coefficient** of a stratum configuration: the
`(A, B)` entry of the joint occurrence matrix — a product of
per-slot unitary entries. This is the stratum factor of an
occurrence feature (the repair of T4a's `wordEntry`, whose path
monomials cannot express the sandwich). -/
def occEntry (s : ↥(GramAssembly.stratumLinks (N := N)) → G) : ℂ :=
  GramWordTensor.occMat slot Ψ s A B

/-- The occurrence coefficient is continuous in the stratum
configuration (a finite product of representation entries). -/
theorem occEntry_continuous
    (hΨcont : ∀ occ, Continuous fun g : G => repMatrix (Ψ occ) g) :
    Continuous (occEntry slot Ψ A B) := by
  show Continuous fun s : ↥(GramAssembly.stratumLinks (N := N)) → G =>
    GramWordTensor.occMat slot Ψ s A B
  simp only [GramWordTensor.occMat_apply]
  refine continuous_finsetProd _ fun occ _ => ?_
  exact (continuous_apply (B occ)).comp ((continuous_apply (A occ)).comp
    ((hΨcont occ).comp (continuous_apply (slot occ))))

/-- The occurrence coefficient is bounded by `1`: a product of
unitary entries, each of norm `≤ 1` (T4a's entry bound, applied per
slot). -/
theorem occEntry_norm_le_one (s : ↥(GramAssembly.stratumLinks (N := N)) → G) :
    ‖occEntry slot Ψ A B s‖ ≤ 1 := by
  rw [occEntry, GramWordTensor.occMat_apply, norm_prod]
  refine Finset.prod_le_one₀ (fun occ _ => norm_nonneg _) fun occ _ => ?_
  exact GramAssembly.repMatrix_entry_norm_le_one (Ψ occ) _ _ _

/-- **The averaging coefficient of an occurrence datum** (the
repair's `γᵒᶜᶜ`): the stratum integral of the occurrence
coefficient — a bare complex number, defined as the integral and
computed by `occGamma_eq` as T2's averaging operator applied to
the joint occurrence representation. -/
noncomputable def occGamma : ℂ :=
  ∫ s, occEntry slot Ψ A B s
    ∂(Measure.pi fun _ : ↥(GramAssembly.stratumLinks (N := N))
      => haarProb G)

/-- **The stratum integral of an occurrence coefficient is T2's
averaging operator applied** — the landed
`GramAssembly.stratum_integral_occMat`, restated for `occGamma`. -/
theorem occGamma_eq
    (hΨcont : ∀ occ, Continuous fun g : G => repMatrix (Ψ occ) g) :
    occGamma slot Ψ A B
      = ⟪(EuclideanSpace.basisFun (κ → Fin d) ℂ) A,
          AveragingProjection.averagingOperator
            (Measure.pi fun _ : ↥(GramAssembly.stratumLinks (N := N))
              => haarProb G)
            (GramWordTensor.occRepCLM slot Ψ)
            (GramWordTensor.occRepCLM_continuous slot Ψ hΨcont)
            (GramWordTensor.occRepCLM_unitary slot Ψ)
            ((EuclideanSpace.basisFun (κ → Fin d) ℂ) B)⟫_ℂ :=
  GramAssembly.stratum_integral_occMat slot Ψ hΨcont A B

/-- **The positive-half occurrence feature** (the criterion's
`𝒜`-side shape, repaired): a strict-half scalar factor `φ₀` times
the occurrence coefficient of the stratum part. -/
def featAOcc (φ₀ : (↥(posLinks (N := N)) → G) → ℂ)
    (y : ↥(halfLinks (N := N)) → G) : ℂ :=
  φ₀ (restrictPos y) * occEntry slot Ψ A B (GramAssembly.stratPart y)

/-- **The strict-half occurrence feature** (the criterion's
`Ξ`-side shape): the averaging coefficient of the datum times the
scalar factor. -/
noncomputable def featXiOcc (φ₀ : (↥(posLinks (N := N)) → G) → ℂ)
    (z : ↥(posLinks (N := N)) → G) : ℂ :=
  occGamma slot Ψ A B * φ₀ z

/-- Occurrence features are continuous (mirrors T4a's
`featA_continuous`). -/
theorem featAOcc_continuous (φ₀ : (↥(posLinks (N := N)) → G) → ℂ)
    (hφ₀ : Continuous φ₀)
    (hΨcont : ∀ occ, Continuous fun g : G => repMatrix (Ψ occ) g) :
    Continuous (featAOcc slot Ψ A B φ₀) :=
  (hφ₀.comp GramAssembly.continuous_restrictPos).mul
    ((occEntry_continuous slot Ψ A B hΨcont).comp
      GramAssembly.continuous_stratPart)

/-- Occurrence features are bounded by the scalar factor's bound
(the occurrence coefficient contributes a factor `≤ 1`; mirrors
T4a's `featA_norm_le`). -/
theorem featAOcc_norm_le (φ₀ : (↥(posLinks (N := N)) → G) → ℂ)
    {Cφ : ℝ} (hφ₀ : ∀ z, ‖φ₀ z‖ ≤ Cφ)
    (y : ↥(halfLinks (N := N)) → G) :
    ‖featAOcc slot Ψ A B φ₀ y‖ ≤ Cφ := by
  have h1 : ‖φ₀ (restrictPos y)
      * occEntry slot Ψ A B (GramAssembly.stratPart y)‖
      = ‖φ₀ (restrictPos y)‖
        * ‖occEntry slot Ψ A B (GramAssembly.stratPart y)‖ :=
    norm_mul _ _
  rw [featAOcc, h1]
  have h2 := mul_le_mul (hφ₀ (restrictPos y))
    (occEntry_norm_le_one slot Ψ A B (GramAssembly.stratPart y))
    (norm_nonneg _) (le_trans (norm_nonneg _) (hφ₀ (restrictPos y)))
  simpa using h2

/-- Occurrence features are almost-everywhere strongly measurable
against the positive-half product measure (the criterion's
`hAA`-side shape, per feature; mirrors T4a's
`featA_aestronglyMeasurable`). -/
theorem featAOcc_aestronglyMeasurable
    (φ₀ : (↥(posLinks (N := N)) → G) → ℂ)
    (hφ₀ : Continuous φ₀)
    (hΨcont : ∀ occ, Continuous fun g : G => repMatrix (Ψ occ) g) :
    AEStronglyMeasurable (featAOcc slot Ψ A B φ₀)
      (Measure.pi fun _ : ↥(halfLinks (N := N)) => haarProb G) :=
  (featAOcc_continuous slot Ψ A B φ₀ hφ₀ hΨcont).aestronglyMeasurable

/-- **The A-side occurrence marginal (the criterion's `hmargA`
shape, for one occurrence datum, per-datum factor `dA = 1`)**:
integrating the feature against a strict-half observable over the
positive half leaves the strict-half feature paired with the same
observable. The proof is T4a's `featA_marginal` template verbatim
— `splitHalfEquiv` transport, `integral_prod_mul` factorization,
and the stratum integral is, by definition, `occGamma`; word-ness
is never used. -/
theorem featAOcc_marginal (φ₀ : (↥(posLinks (N := N)) → G) → ℂ)
    (f : (↥(posLinks (N := N)) → G) → ℂ) :
    ∫ y, featAOcc slot Ψ A B φ₀ y * f (restrictPos y)
        ∂(Measure.pi fun _ : ↥(halfLinks (N := N)) => haarProb G)
      = ((1 : ℝ) : ℂ) * ∫ z, featXiOcc slot Ψ A B φ₀ z * f z
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G) := by
  classical
  have hcomp : ∫ y, featAOcc slot Ψ A B φ₀ y * f (restrictPos y)
        ∂(Measure.pi fun _ : ↥(halfLinks (N := N)) => haarProb G)
      = ∫ y, (φ₀ ((GramAssembly.splitHalfEquiv y).1)
          * f ((GramAssembly.splitHalfEquiv y).1))
          * occEntry slot Ψ A B (GramAssembly.splitHalfEquiv y).2
        ∂(Measure.pi fun _ : ↥(halfLinks (N := N)) => haarProb G) := by
    congr 1
    funext y
    show featAOcc slot Ψ A B φ₀ y * f (restrictPos y)
      = (φ₀ ((GramAssembly.splitHalfEquiv y).1)
          * f ((GramAssembly.splitHalfEquiv y).1))
        * occEntry slot Ψ A B (GramAssembly.splitHalfEquiv y).2
    rw [GramAssembly.splitHalfEquiv_fst, GramAssembly.splitHalfEquiv_snd]
    simp only [featAOcc]
    ring
  calc ∫ y, featAOcc slot Ψ A B φ₀ y * f (restrictPos y)
          ∂(Measure.pi fun _ : ↥(halfLinks (N := N)) => haarProb G)
      = ∫ y, (φ₀ ((GramAssembly.splitHalfEquiv y).1)
          * f ((GramAssembly.splitHalfEquiv y).1))
          * occEntry slot Ψ A B (GramAssembly.splitHalfEquiv y).2
          ∂(Measure.pi fun _ : ↥(halfLinks (N := N)) => haarProb G) :=
        hcomp
    _ = ∫ p, (φ₀ p.1 * f p.1) * occEntry slot Ψ A B p.2
          ∂((Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G).prod
            (Measure.pi fun _ : ↥(GramAssembly.stratumLinks (N := N))
              => haarProb G)) := by
        rw [← (GramAssembly.measurePreserving_splitHalfEquiv
          (haarProb G)).integral_comp
          (MeasurableEquiv.measurableEmbedding _)
          (fun p : (↥(posLinks (N := N)) → G)
            × (↥(GramAssembly.stratumLinks (N := N)) → G) =>
            (φ₀ p.1 * f p.1) * occEntry slot Ψ A B p.2)]
    _ = (∫ z, φ₀ z * f z
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G))
        * occGamma slot Ψ A B :=
        MeasureTheory.integral_prod_mul (fun z => φ₀ z * f z)
          (occEntry slot Ψ A B)
    _ = ((1 : ℝ) : ℂ) * ∫ z, featXiOcc slot Ψ A B φ₀ z * f z
          ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G) := by
        have e : (∫ z, featXiOcc slot Ψ A B φ₀ z * f z
              ∂(Measure.pi fun _ : ↥(posLinks (N := N)) => haarProb G))
            = occGamma slot Ψ A B * ∫ z, φ₀ z * f z
              ∂(Measure.pi fun _ : ↥(posLinks (N := N))
                => haarProb G) := by
          rw [show (fun z => featXiOcc slot Ψ A B φ₀ z * f z)
              = fun z => occGamma slot Ψ A B * (φ₀ z * f z) from
            funext fun z => by simp only [featXiOcc]; ring]
          exact MeasureTheory.integral_const_mul _ _
        rw [e, Complex.ofReal_one, one_mul, mul_comm]

end OccFeatures

/-! ## §3. The strict factor `φ₀ᴰ` of a crossing plaquette -/

section PhiD

/-- The extension of a strict-half configuration by `1` off the
half is measurable (pointwise: evaluation on the half, constant
off it). -/
theorem measurable_extendP :
    Measurable fun z : ↥(posLinks (N := N)) → G => extendP z := by
  refine Measurable.of_eval fun ℓ => ?_
  by_cases hℓ : ℓ ∈ posLinks (N := N)
  · have e : (fun z : ↥(posLinks (N := N)) → G => extendP z ℓ)
        = fun z => z ⟨ℓ, hℓ⟩ := funext fun z => extendP_apply hℓ
    rw [e]
    exact measurable_pi_apply _
  · have e : (fun z : ↥(posLinks (N := N)) → G => extendP z ℓ)
        = fun _ => (1 : G) := by
      funext z
      show (if h : ℓ ∈ posLinks (N := N) then z ⟨ℓ, h⟩ else 1) = 1
      exact dif_neg hℓ
    rw [e]
    exact measurable_const

/-- A single plaquette density is measurable in the ambient
configuration (the trace is a sum of diagonal entries, each a
representation entry of a plaquette — the corpus's
`measurable_wilsonAction` pattern, for one density). -/
theorem measurable_plaquetteDensity
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (x : Fin 4 → ZMod N) (μ ν : Fin 4) :
    Measurable fun U : Config (Fin 4 → ZMod N) G =>
      plaquetteDensity (torusShift N) ρ U x μ ν := by
  have htr : Measurable fun U : Config (Fin 4 → ZMod N) G =>
      (Matrix.trace (repMatrix ρ (plaquette (torusShift N) U x μ ν))).re := by
    refine Complex.measurable_re.comp ?_
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (measurable_pi_apply i).comp ((measurable_pi_apply i).comp
      (hρcont.measurable.comp (measurable_plaquette (torusShift N) x μ ν)))
  unfold plaquetteDensity
  exact measurable_const.sub (htr.div_const _)

/-- The positive Wilson action is measurable in the ambient
configuration. -/
theorem measurable_wilsonActionPlus
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    Measurable fun U : Config (Fin 4 → ZMod N) G =>
      wilsonActionPlus ρ β U := by
  unfold wilsonActionPlus
  exact (Finset.measurable_sum _ fun p _ =>
    measurable_plaquetteDensity ρ hρcont p.1 p.2.1 p.2.2).const_mul β

/-- **The strict action is measurable** at general `(G, ρ)`: the
positive action of the trivially extended strict configuration.
(The corpus previously carried the strict action's regularity
only for the circle representation.) -/
theorem measurable_halfActionP
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    Measurable fun z : ↥(posLinks (N := N)) → G => halfActionP ρ β z :=
  (measurable_wilsonActionPlus ρ hρcont β).comp measurable_extendP

variable {p : (Fin 4 → ZMod N) × Fin 4 × Fin 4}

/-- **The strict factor of one crossing plaquette**, in the
obstruction memo's shape: the strict entry `(ρD⁻¹)_{k a}` times
the positive-half Boltzmann factor of the strict configuration,
times the square root of the series weight `w` (an explicit real
parameter — the design decision recorded in the header; the
closer instantiates it per tensor power). -/
noncomputable def phiD (hpD : linkD p ∈ posLinks (N := N)) (k a : Fin d) (w : ℝ)
    (β : ℝ) (z : ↥(posLinks (N := N)) → G) : ℂ :=
  (repMatrix ρ ((z ⟨linkD p, hpD⟩)⁻¹)) k a
    * ((Real.exp (-(halfActionP ρ β z)) : ℝ) : ℂ)
    * ((Real.sqrt w : ℝ) : ℂ)

/-- The strict factor's bound: the entry contributes a factor
`≤ 1`, so `‖φ₀ᴰ z‖ ≤ √w · exp (−halfActionP ρ β z)` — with **no**
sign condition on `β` or on the action. -/
theorem phiD_norm_le (hpD : linkD p ∈ posLinks (N := N)) (k a : Fin d)
    (w : ℝ) (β : ℝ) (z : ↥(posLinks (N := N)) → G) :
    ‖phiD ρ hpD k a w β z‖
      ≤ Real.sqrt w * Real.exp (-(halfActionP ρ β z)) := by
  have h1 : ‖(repMatrix ρ ((z ⟨linkD p, hpD⟩)⁻¹)) k a‖ ≤ 1 :=
    GramAssembly.repMatrix_entry_norm_le_one ρ _ k a
  have h2 : ‖((Real.exp (-(halfActionP ρ β z)) : ℝ) : ℂ)‖
      = Real.exp (-(halfActionP ρ β z)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h3 : ‖((Real.sqrt w : ℝ) : ℂ)‖ = Real.sqrt w := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg w)]
  unfold phiD
  rw [norm_mul, norm_mul, h2, h3]
  calc ‖(repMatrix ρ ((z ⟨linkD p, hpD⟩)⁻¹)) k a‖
        * Real.exp (-(halfActionP ρ β z)) * Real.sqrt w
      ≤ 1 * Real.exp (-(halfActionP ρ β z)) * Real.sqrt w :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _))
          (Real.sqrt_nonneg w)
    _ = Real.sqrt w * Real.exp (-(halfActionP ρ β z)) := by ring

/-- The strict factor is strongly measurable (its action factor
is measurable by `measurable_halfActionP`, at general `(G, ρ)`). -/
theorem phiD_stronglyMeasurable (hpD : linkD p ∈ posLinks (N := N))
    (k a : Fin d) (w : ℝ) (β : ℝ)
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    StronglyMeasurable (phiD ρ hpD k a w β) := by
  have hentry : Continuous fun z : ↥(posLinks (N := N)) → G =>
      (repMatrix ρ ((z ⟨linkD p, hpD⟩)⁻¹)) k a :=
    ((continuous_apply a).comp (continuous_apply k)).comp
      (hρcont.comp
        (continuous_apply (⟨linkD p, hpD⟩ : ↥(posLinks (N := N)))).inv)
  have hexp : Measurable fun z : ↥(posLinks (N := N)) → G =>
      ((Real.exp (-(halfActionP ρ β z)) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.measurable.comp
      ((Real.continuous_exp.measurable).comp
        (measurable_halfActionP ρ hρcont β).neg)
  unfold phiD
  exact (hentry.stronglyMeasurable.mul hexp.stronglyMeasurable).mul
    stronglyMeasurable_const

/-- **The concrete A-side occurrence feature of one crossing
plaquette is strongly measurable**: the §2 feature at the arc
datum (`arcSlot`, `arcΨ`), endpoint functions `(![k, a], ![j, i])`
— `(k, a)` the strict pair, `(j, i)` the mirror pair — with
strict factor `φ₀ᴰ`. This is the shape the closer (T4c′)
integrates. -/
theorem featAOccD_stronglyMeasurable
    (hpC : linkC p ∈ GramAssembly.stratumLinks (N := N))
    (hpA : linkA p ∈ GramAssembly.stratumLinks (N := N))
    (hpD : linkD p ∈ posLinks (N := N)) (k a j i : Fin d) (w : ℝ)
    (β : ℝ) (hρcont : Continuous fun g : G => repMatrix ρ g) :
    StronglyMeasurable (featAOcc (arcSlot hpC hpA) (arcΨ ρ) ![k, a]
      ![j, i] (phiD ρ hpD k a w β)) := by
  unfold featAOcc
  refine StronglyMeasurable.mul ?_ ?_
  · exact (phiD_stronglyMeasurable ρ hpD k a w β hρcont).comp_measurable
      GramAssembly.continuous_restrictPos.measurable
  · exact ((occEntry_continuous (arcSlot hpC hpA) (arcΨ ρ) ![k, a]
      ![j, i] (arcΨ_continuous ρ hρcont)).comp
        GramAssembly.continuous_stratPart).stronglyMeasurable

end PhiD

end GramAssemblyOcc

end ThetLogos
