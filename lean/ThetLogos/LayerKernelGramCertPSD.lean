/-
# LayerKernelGramCertPSD — Route B conversion bricks (DGG-1)

Banked in Phase 2 (worktree thet-logos-dgg, branch dgg) on
the parent's slot clearance, under the standard discipline.
Drafted in Phase 1 staging (~/workspace/dgg-route-b/).

Route B of the DeltaGramGap factorization attack, scoped at
`~/workspace/your_files/deltagramgap-factorization-attack-scope-2026-11-24.md`,
fired by Zero, 2026-11-24 04:00 EST.  This file currently
carries **DGG-1 only** (the pairing ⇒ matrix-PSD conversion);
DGG-2 (PSD ⇒ Gram factorization over the padded index) and
DGG-3 (assembly: `DeltaGramGap` at `β ≥ 0`) land in this same
module in their own bricks.

**DGG-1's statement.**  At every finite `(G, ρ)`, every even
`N`, every `β ≥ 0`: the finite kernel matrix
`Matrix.of (layerKernel μG ρ β)` on the configuration type
`(LayerLink N → G)` is `Matrix.PosSemidef`.

**How the conversion actually goes (drafting finding, at full
rank).**  Bare `LayerKernelPos` does **not** suffice as the
input: it quantifies over gauge-invariant observables only
(`LayerKernelPos` in `LayerKernelPos.lean` — `∀ F,
GaugeInvariantLayerObs F → …`), while `Matrix.PosSemidef`
needs the quadratic form at **every** vector.  The cited
input that does suffice is the character certificate's
`kernel_eq` field — `gramCharCert.kernel_eq`, the owned
identity `LayerKernelPos` itself rests on, listed verbatim in
K-DGG-DUP's citation set ("every closed `kernel_eq` in the
instance ladder").  From it, both halves of `PosSemidef` are
direct: Hermitian-ness is entrywise (a Gram sum with real
weights is Hermitian), and the quadratic form is the finite
pairing sum, evaluated by the already-proved `gram_pairing_eq`
to the cast of a nonnegative real.  `layerKernelPos_char` is
cited as the owned positivity headline throughout; nothing in
this brick re-proves `LayerKernelPos` or any certificate
field — fields are *applied*, not re-derived.

**The WALL (inherited).**  This is a finite factorization
line.  No spectral-gap, eigenvalue-isolation, mass-gap, or
continuum language anywhere; "gap" names the missing proof of
`DeltaGramGap` and nothing else.  The feature map Route B
eventually produces is an **EIGENBASIS feature map** (DGG-2's
spectral step), never the constructive column SOS — that is
Route C, not fired.  Dial 2 stays 0 under every outcome.

NO CLAIM; dials 0/4.
-/

import ThetLogos.DeltaGramGapAttackPin
import ThetLogos.LayerKernelGramCertChar
-- The pinned path of `Matrix.PosSemidef` and
-- `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg`, verified
-- on disk 2026-11-24 (Mathlib/LinearAlgebra/Matrix/
-- PosDef.lean, lines 62 and 311).
import Mathlib.LinearAlgebra.Matrix.PosDef
-- DGG-2 (2026-11-24): the spectral theorem
-- (`Matrix.IsHermitian.spectral_theorem`), the PSD eigenvalue
-- sign (`Matrix.PosSemidef.eigenvalues_nonneg`) and
-- `Unitary.conjStarAlgAut_apply` live in the Analysis files,
-- not in the previous import chain (verified on disk in the
-- pinned Mathlib: Analysis/Matrix/Spectrum.lean,
-- Analysis/Matrix/PosDef.lean, Algebra/Star/
-- UnitaryStarAlgAut.lean).  No statement is changed.
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

open MeasureTheory Finset
-- Environment repair (disclosed, 2026-11-24): as in the
-- registration pin — `Matrix.PosSemidef` over `ℂ` needs the
-- scoped instance `Complex.partialOrder`, available only
-- under `open scoped ComplexOrder` (house idiom, cf.
-- `PartnerThermal.lean`).  No statement is changed.
open scoped Matrix ENNReal NNReal ComplexOrder

namespace ThetLogos

section DGGPSD

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] [DiscreteTopology G]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N] [DecidableEq (LayerLink N)]

variable (β : ℝ) {τ ι : Type*} [Fintype τ] [Fintype ι]

/-- **Finite-sum pairing of an SOS certificate** — the
sum-level analogue of `LayerKernelSOSCert.gram_form` (which is
the same computation for the integral pairing): the double sum
over configurations against a certified kernel is the cast of
the real `∑ j, weight_j • ‖Z_j‖²`.  Cited inputs only: the
certificate's `kernel_eq` field and `gram_pairing_eq`
(K-DGG-DUP). -/
theorem sosCert_sum_pairing_eq
    (cert : LayerKernelSOSCert (N := N) (τ := τ) (ι := ι) μG ρ β)
    (F : (LayerLink N → G) → ℂ) :
    (∑ u, ∑ u', (starRingEnd ℂ) (F u) * layerKernel μG ρ β u u' * F u')
      = ((∑ j, gramColWeight cert.coeff cert.τof j
          * ‖gramObs cert.feat F j‖ ^ 2 : ℝ) : ℂ) := by
  have h : ∀ u u' : LayerLink N → G,
      (starRingEnd ℂ) (F u) * layerKernel μG ρ β u u' * F u'
        = (starRingEnd ℂ) (F u)
          * (∑ j, ((gramColWeight cert.coeff cert.τof j : ℝ) : ℂ)
              * cert.feat j u * star (cert.feat j u')) * F u' := by
    intro u u'
    rw [cert.kernel_eq u u']
  exact (Finset.sum_congr rfl fun u _ =>
    Finset.sum_congr rfl fun u' _ => h u u').trans
      (gram_pairing_eq _ _ _)

/-- **The finite kernel matrix is Hermitian** (even `N`,
`β ≥ 0`), by the character certificate's `kernel_eq` (cited,
K-DGG-DUP): entrywise, a Gram sum with real weights is
Hermitian.  Fallback route if the `star` simp set fights at
build time: `layerKernel_symm` (even `N`) plus real-valuedness
of the integral of real casts — noted in the line's STATE
file, not needed if this draft elaborates. -/
theorem layerKernel_isHermitian (hN : Even N) {β : ℝ} (hβ : 0 ≤ β) :
    (Matrix.of (layerKernel (N := N) μG ρ β)).IsHermitian := by
  classical
  have hmat : (Matrix.of (layerKernel (N := N) μG ρ β))ᴴ
      = Matrix.of (layerKernel (N := N) μG ρ β) := by
    ext u u'
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply,
      (gramCharCert μG ρ hN β hβ).kernel_eq u' u,
      (gramCharCert μG ρ hN β hβ).kernel_eq u u']
    -- API resolution (Phase 2, 2026-11-24): `star_sum`
    -- verified in the pinned Mathlib
    -- (Mathlib/Algebra/Star/BigOperators.lean line 27); the
    -- `star` of a real cast is discharged by `by simp` in
    -- the ∀-form `hw` below (the draft's inline cast
    -- cascade for this fact did not parse; the ∀-form was
    -- verified in a standalone probe).
    rw [star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hw : ∀ w : ℝ, star ((w : ℂ)) = (w : ℂ) :=
      fun w => by simp
    rw [star_mul, star_mul, star_star, hw]
    ring
  exact hmat

/-- The `PosSemidef` quadratic form of the kernel matrix **is**
the finite pairing sum — pure algebra (dot product and
matrix–vector unfolding), no hypotheses, no cited input. -/
theorem dotProduct_mulVec_eq_sum_pairing
    (x : (LayerLink N → G) → ℂ) :
    star x ⬝ᵥ ((Matrix.of (layerKernel μG ρ β)) *ᵥ x)
      = ∑ u, ∑ u', (starRingEnd ℂ) (x u)
          * layerKernel μG ρ β u u' * x u' := by
  classical
  -- API resolution (Phase 2, 2026-11-24): in this pin the
  -- dot product is the root-level `dotProduct`
  -- (Mathlib/Data/Matrix/Mul.lean — its DotProduct section
  -- sits outside `namespace Matrix`, so `Matrix.dotProduct`
  -- is an unknown constant), and `*ᵥ` unfolds by the named
  -- lemma `Matrix.mulVec_apply_eq_sum`.  Verified in a
  -- standalone probe against the pinned Mathlib.
  simp only [dotProduct, Matrix.mulVec_apply_eq_sum,
    Matrix.of_apply, Pi.star_apply, starRingEnd_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun u' _ => by ring

/-- The finite pairing sum has nonnegative real part (even
`N`, `β ≥ 0`): the character certificate's assembled weights
are nonnegative (`gramColWeight_nonneg` of its `coeff_nonneg`,
both cited), spent through `sosCert_sum_pairing_eq`.  Same
closing shape as `LayerKernelSOSCert.gram_form`. -/
theorem layerKernel_sum_pairing_re_nonneg (hN : Even N) {β : ℝ}
    (hβ : 0 ≤ β) (F : (LayerLink N → G) → ℂ) :
    0 ≤ (∑ u, ∑ u', (starRingEnd ℂ) (F u)
        * layerKernel μG ρ β u u' * F u').re := by
  rw [sosCert_sum_pairing_eq μG ρ β (gramCharCert μG ρ hN β hβ) F,
    Complex.ofReal_re]
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (gramColWeight_nonneg _ _
      (gramCharCert μG ρ hN β hβ).coeff_nonneg j)
      (pow_nonneg (norm_nonneg _) _)

/-- **DGG-1 headline.**  The finite kernel matrix is positive
semidefinite (even `N`, `β ≥ 0`) — Route B, brick 1: the
pairing ⇒ PSD conversion.  Assembled from
`layerKernel_isHermitian` and the pairing computation through
the pinned Mathlib's
`Matrix.PosSemidef.of_dotProduct_mulVec_nonneg`
(verified on disk, PosDef.lean). -/
theorem layerKernel_posSemidef (hN : Even N) {β : ℝ} (hβ : 0 ≤ β) :
    (Matrix.of (layerKernel (N := N) μG ρ β)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (layerKernel_isHermitian μG ρ hN hβ) (fun x => ?_)
  rw [dotProduct_mulVec_eq_sum_pairing μG ρ β x,
    sosCert_sum_pairing_eq μG ρ β (gramCharCert μG ρ hN β hβ) x,
    ← Complex.ofReal_zero]
  -- The cast-order iff `RCLike.ofReal_le_ofReal` does not
  -- rewrite here: the goal's `≤` is
  -- `Complex.partialOrder.toLE` (scoped instance), the
  -- lemma's is `RCLike.toPartialOrder.toLE`, and `rw`
  -- matches instance arguments only up to reducible defeq.
  -- `exact_mod_cast` performs the cast elimination
  -- through the norm_cast machinery instead.
  exact_mod_cast Finset.sum_nonneg fun j _ =>
    mul_nonneg (gramColWeight_nonneg _ _
      (gramCharCert μG ρ hN β hβ).coeff_nonneg j)
      (pow_nonneg (norm_nonneg _) _)

/-- DGG-1 headline in the registration pin's vocabulary
(`dggKernelMatrix` is `Matrix.of (layerKernel …)` by
definition). -/
theorem dggKernelMatrix_posSemidef (hN : Even N) {β : ℝ}
    (hβ : 0 ≤ β) :
    (dggKernelMatrix (N := N) μG ρ β).PosSemidef :=
  layerKernel_posSemidef μG ρ hN hβ

end DGGPSD

/-! ## DGG-2 — PSD ⇒ Gram factorization over the padded index

Route B, second brick (fired by Zero 2026-11-24 04:00 EST,
"close DeltaGramGap at β ≥ 0").  The factorization produced
here is the **EIGENBASIS** factorization: the feature map is
the kernel matrix's own eigenvector basis, square-rooted
eigenvalues attached.  It is NOT the constructive column SOS
of Route C, which remains open and unfired.  The general
lemmas are stated for an arbitrary finite index type and an
arbitrary complex PSD matrix; the layer headline instantiates
them at `layerKernel_posSemidef` (DGG-1, cited) and pads
along `configEmbedding` into the certificate's own feature
index type with the certificate's own weights. -/

section DGGFactor

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] [DiscreteTopology G]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N] [DecidableEq (LayerLink N)]

/-- **Spectral Gram factorization (EIGENBASIS).**  Every
complex positive semidefinite matrix is a Gram matrix: its
own eigendecomposition, square-rooted, is a feature map.
The feature map is the eigenvector basis of `K` — an
EIGENBASIS factorization, not a constructive column SOS.
(There is no `PosSemidef.sqrt` in this Mathlib pin; the
route is `Matrix.IsHermitian.spectral_theorem` plus
`Matrix.PosSemidef.eigenvalues_nonneg`.) -/
theorem posSemidef_gram_factor {n : Type*} [Fintype n] [DecidableEq n]
    {K : Matrix n n ℂ} (hK : K.PosSemidef) :
    ∃ feat₀ : n → n → ℂ, ∀ u u', K u u' = ∑ x, feat₀ x u * star (feat₀ x u') := by
  classical
  have hA : Matrix.IsHermitian K := hK.isHermitian
  have hspec : K = (hA.eigenvectorUnitary : Matrix n n ℂ)
      * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
      * star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  refine ⟨fun x u => ((Real.sqrt (hA.eigenvalues x) : ℝ) : ℂ)
    * (hA.eigenvectorUnitary : Matrix n n ℂ) u x, fun u u' => ?_⟩
  rw [congrArg (fun M : Matrix n n ℂ => M u u') hspec, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hsum : (∑ y, (hA.eigenvectorUnitary : Matrix n n ℂ) u y
        * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) y x)
      = (hA.eigenvectorUnitary : Matrix n n ℂ) u x
        * ((hA.eigenvalues x : ℝ) : ℂ) := by
    rw [Finset.sum_eq_single x]
    · rw [Matrix.diagonal_apply, if_pos rfl, Function.comp_apply,
        RCLike.ofReal_eq_complex_ofReal]
    · intro y _ hyx
      rw [Matrix.diagonal_apply, if_neg hyx, mul_zero]
    · simp
  rw [Matrix.mul_apply, hsum, Matrix.star_apply]
  have hstar : ∀ r : ℝ, star ((r : ℂ)) = (r : ℂ) := fun r => by simp
  have hsq : ((Real.sqrt (hA.eigenvalues x) : ℂ))
      * ((Real.sqrt (hA.eigenvalues x) : ℂ))
      = ((hA.eigenvalues x : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hK.eigenvalues_nonneg x)]
  simp only [star_mul, hstar]
  rw [← hsq]
  ring

open Classical in
/-- Zero-padding of a feature family along an embedding of
index types, rescaled by the inverse square roots of the
target weights: on the image of `e` the feature at `e x` is
`feat₀ x / √(w (e x))`; off the image it is zero. -/
noncomputable def gramPadFeat {n ι : Type*} (e : n ↪ ι) (w : ι → ℝ)
    (feat₀ : n → n → ℂ) (j : ι) (u : n) : ℂ :=
  if h : j ∈ Set.range e then
    ((Real.sqrt (w j) : ℂ))⁻¹ * feat₀ (Classical.choose h) u
  else 0

/-- The padded feature vanishes off the embedding's image. -/
theorem gramPadFeat_of_not_mem {n ι : Type*} {e : n ↪ ι} {w : ι → ℝ}
    {feat₀ : n → n → ℂ} {j : ι} (hj : j ∉ Set.range e) (u : n) :
    gramPadFeat e w feat₀ j u = 0 := dif_neg hj

/-- On the image, the padded feature is the rescaled original
(the chosen preimage is the point itself, by injectivity). -/
theorem gramPadFeat_apply_embedding {n ι : Type*} {e : n ↪ ι} {w : ι → ℝ}
    {feat₀ : n → n → ℂ} (x : n) (u : n) :
    gramPadFeat e w feat₀ (e x) u
      = ((Real.sqrt (w (e x)) : ℂ))⁻¹ * feat₀ x u := by
  have hmem : e x ∈ Set.range e := ⟨x, rfl⟩
  have hchoose : Classical.choose hmem = x :=
    e.injective (Classical.choose_spec hmem)
  unfold gramPadFeat
  rw [dif_pos hmem, hchoose]

/-- **Gram factorization transport.**  A Gram factorization
of `K` over the index type `n` pads along any embedding
`e : n ↪ ι` to a weighted Gram factorization over `ι`, for
any strictly positive weight function `w`: the padded
features are the original features rescaled by `1/√(w j)` on
the image of `e` and zero off it, so each weight cancels
against its two rescalings. -/
theorem gram_factor_pad {n ι : Type*} [Fintype n] [Fintype ι]
    {K : Matrix n n ℂ} {feat₀ : n → n → ℂ}
    (hfact : ∀ u u', K u u' = ∑ x, feat₀ x u * star (feat₀ x u'))
    (e : n ↪ ι) {w : ι → ℝ} (hw : ∀ j, 0 < w j) :
    ∃ feat : ι → n → ℂ, ∀ u u',
      K u u' = ∑ j, ((w j : ℂ)) * feat j u * star (feat j u') := by
  classical
  refine ⟨gramPadFeat e w feat₀, fun u u' => ?_⟩
  rw [hfact u u']
  have h1 : (∑ j ∈ Finset.univ.map e, ((w j : ℂ)) * gramPadFeat e w feat₀ j u
        * star (gramPadFeat e w feat₀ j u'))
      = ∑ j, ((w j : ℂ)) * gramPadFeat e w feat₀ j u
        * star (gramPadFeat e w feat₀ j u') := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    rw [Finset.mem_map] at hj
    push_neg at hj
    have hjr : j ∉ Set.range e := by
      rintro ⟨x, hx⟩
      exact hj x (Finset.mem_univ x) hx
    simp [gramPadFeat_of_not_mem hjr]
  rw [← h1, Finset.sum_map]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [gramPadFeat_apply_embedding x u, gramPadFeat_apply_embedding x u']
  have hstar : ∀ r : ℝ, star ((r : ℂ)) = (r : ℂ) := fun r => by simp
  rw [star_mul, star_inv₀, hstar]
  have hne : ((w (e x) : ℂ)) ≠ 0 := by exact_mod_cast (hw (e x)).ne'
  have hsq : ((Real.sqrt (w (e x)) : ℂ)) * ((Real.sqrt (w (e x)) : ℂ))
      = (w (e x) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hw (e x)).le]
  have hone : (w (e x) : ℂ) * ((Real.sqrt (w (e x)) : ℂ))⁻¹
      * ((Real.sqrt (w (e x)) : ℂ))⁻¹ = 1 := by
    rw [mul_assoc, ← mul_inv_rev, hsq, mul_inv_cancel₀ hne]
  calc feat₀ x u * star (feat₀ x u')
      = ((w (e x) : ℂ) * ((Real.sqrt (w (e x)) : ℂ))⁻¹
          * ((Real.sqrt (w (e x)) : ℂ))⁻¹)
          * (feat₀ x u * star (feat₀ x u')) := by rw [hone, one_mul]
    _ = (w (e x) : ℂ) * (((Real.sqrt (w (e x)) : ℂ))⁻¹ * feat₀ x u)
          * (star (feat₀ x u') * ((Real.sqrt (w (e x)) : ℂ))⁻¹) := by ring

/-- The configuration embedding: a link configuration embeds
into the certificate's feature index type (site configurations
× column configurations) — the site component reads the
configuration along a fixed nonzero direction at each site;
the column component reads it along each column's own link.
Injectivity is the column component's: `colLink` has the
section `wordColumn`.  (No such embedding exists in-tree;
constructed here, as the scope directed.) -/
noncomputable def configEmbedding :
    (LayerLink N → G) ↪ (LayerSite N → G) × (LayerColumn N → G) where
  toFun u := (fun s => u (layerLinkOf s 1 (by decide)), fun P => u (colLink P))
  inj' := by
    intro u u' h
    funext ℓ
    have h2 : (fun P => u (colLink P)) = (fun P => u' (colLink P)) :=
      congrArg Prod.snd h
    have h3 := congrFun h2 (wordColumn (N := N) ℓ)
    rwa [colLink_wordColumn] at h3

/-- **DGG-2 headline (EIGENBASIS).**  At even `N` and
`β ≥ 0`, the layer kernel admits a weighted Gram
factorization over the certificate's own feature index type,
with the certificate's own weights
`gramColWeight (deltaCoeff ρ β) (·.2)`: the spectral
(EIGENBASIS) factorization of `layerKernel_posSemidef`
(DGG-1, cited — K-DGG-DUP), zero-padded along
`configEmbedding`.  The weights are strictly positive
because every `deltaCoeff` is (`deltaCoeff_pos`). -/
theorem layerKernel_gram_factor_padded (hN : Even N) {β : ℝ} (hβ : 0 ≤ β) :
    ∃ feat : ((LayerSite N → G) × (LayerColumn N → G)) → (LayerLink N → G) → ℂ,
      ∀ u u' : LayerLink N → G,
        layerKernel μG ρ β u u'
          = ∑ j, ((gramColWeight (deltaCoeff ρ β)
              (fun j : (LayerSite N → G) × (LayerColumn N → G) => j.2) j : ℝ) : ℂ)
            * feat j u * star (feat j u') := by
  classical
  obtain ⟨feat₀, hfact₀⟩ := posSemidef_gram_factor (layerKernel_posSemidef μG ρ hN hβ)
  obtain ⟨feat, hfeat⟩ := gram_factor_pad hfact₀ configEmbedding
    (w := fun j => gramColWeight (deltaCoeff ρ β)
      (fun j : (LayerSite N → G) × (LayerColumn N → G) => j.2) j)
    (fun j => Finset.prod_pos (fun P _ => deltaCoeff_pos ρ β _))
  refine ⟨feat, fun u u' => ?_⟩
  have h := hfeat u u'
  rwa [Matrix.of_apply] at h

/-! ## DGG-3 — assembly: `DeltaGramGap` at `β ≥ 0`

The Prop's contracted sum is `layerKernel` itself
(`layerKernel_eq_contracted`, even `N`, cited — K-DGG-DUP),
and DGG-2 factors `layerKernel` over the certificate's own
index type with the certificate's own weights.  Assembling
the two closes the named gap at every finite `(G, ρ)`, every
even `N`, every `β ≥ 0`.  What this is: the Gram
factorization existence statement of
`LayerKernelGramCertFinite`, proved by the EIGENBASIS route.
What it is not: a spectral gap, a continuum statement, or a
mass gap — "gap" names the formerly missing proof of this
Prop only.  Route C (the constructive column SOS) remains
open and unfired; `LayerKernelPos` was already owned by the
character route and gains a second proof through the
factorization (`layerKernelPos_via_deltaGramGap`). -/

include μG in
/-- **DGG-3 headline: `DeltaGramGap` at `β ≥ 0`.**  At every
finite `(G, ρ)`, every even `N`, every `β ≥ 0`, the
contracted δ-kernel sum admits the Gram factorization over
the joint index `(α, t)` with the assembled `gramColWeight`
weights.  (The Prop does not mention the measure; the proof
routes through `layerKernel`, so `μG` is included.) -/
theorem deltaGramGap_beta_nonneg (hN : Even N) {β : ℝ} (hβ : 0 ≤ β) :
    DeltaGramGap (ρ := ρ) (N := N) β := by
  obtain ⟨feat, hfeat⟩ := layerKernel_gram_factor_padded μG ρ hN hβ
  refine ⟨feat, fun u u' => ?_⟩
  rw [← layerKernel_eq_contracted μG ρ hN β u u']
  exact hfeat u u'

include μG in
/-- The DGG-0 target, discharged: `dggTarget` — `DeltaGramGap`
at every `β ≥ 0` (even `N`).  `dggKillFAIL` is thereby
confined to its hunting ground `β < 0`, where the kernel is
not PSD and the factorization provably cannot exist by this
route; no claim about `β < 0` is made here. -/
theorem dggTarget_proved (hN : Even N) : dggTarget ρ hN :=
  fun β hβ => deltaGramGap_beta_nonneg μG ρ hN hβ

/-- The δ-certificate, unconditional at `β ≥ 0` (even `N`):
`gramDeltaCert` with its `kernel_eq` hypothesis — the gap
itself — discharged by `deltaGramGap_beta_nonneg`.  The
certificate is cited, not re-proved (K-DGG-DUP). -/
noncomputable def gramDeltaCert_unconditional (hN : Even N) (β : ℝ)
    (hβ : 0 ≤ β) :
    LayerKernelSOSCert (N := N) (τ := G)
      (ι := (LayerSite N → G) × (LayerColumn N → G)) μG ρ β :=
  gramDeltaCert μG ρ hN β (deltaGramGap_beta_nonneg μG ρ hN hβ)

/-- `LayerKernelPos` at `β ≥ 0` via the δ-route: the cited
discharge `layerKernelPos_of_deltaGramGap` applied to the
proved gap.  Positivity was already owned at census grade
by the character route (`gramCharCert`); this is its second
proof, through the factorization. -/
theorem layerKernelPos_via_deltaGramGap (hN : Even N) {β : ℝ} (hβ : 0 ≤ β) :
    LayerKernelPos (N := N) μG ρ β :=
  layerKernelPos_of_deltaGramGap μG ρ hN hβ
    (deltaGramGap_beta_nonneg μG ρ hN hβ)

end DGGFactor

end ThetLogos
