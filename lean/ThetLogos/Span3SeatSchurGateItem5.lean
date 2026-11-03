/-
# F2-GATE-3 / GATE-0 ITEM 5 — the core-chain run: the compression
route, run as far as it honestly goes

Brick: GATE-0 item 5 (`pullBotKernel_seatFactorApproxExpansion`,
frozen in `ThetLogos/Span3SeatSchurGatePost.lean`), commissioned
by Jeff 2026-11-02 ("run them" — the core-chain chair option,
previously untaken) and re-fired 2026-11-03. The `𝒜 ⪰ 0` core
chain is SINGLE LANE ALWAYS; this module is that lane's landing.
Built in the isolated worktree `~/workspace/thet-logos-item5`,
branch `item5-lane`, from main-tree HEAD `f57a107` (the item-6
ceremony commit); NOT integrated — the parent runs the ceremony.

## VERDICT (on the face): PARTIAL

The headline `pullBotKernel_seatFactorApproxExpansion` is NOT
discharged. What IS discharged here, at full rank:

1. **The compression route is built and its HS convergence is
   PROVED** — at the level of a general `L²` kernel carrying two
   explicit hypotheses: positivity on ALL of `L²`
   (`PosKernel`, SHELF-3b's registered notion) and
   self-adjointness of its integral operator. Finite-rank
   compressions along a Hilbert basis are finite Gram sums
   (finite-dimensional `Matrix.PosSemidef` factorization —
   owned Mathlib stock, NOT an infinite-dimensional spectral
   expansion), and their HS distance to the kernel is at most
   the sum of the operator and adjoint HS tails, hence tends
   to `0` along finite sets. The pre-named GATE-3 seam
   ("compressions built + finite Grams landed, HS convergence
   stalls") does NOT stall: the adapted convergence lands.
2. **The seat assembly is PROVED conditionally**: under the
   corpus's kernel-measurability input
   (`Continuous fun g => repMatrix ρ g`, the same hypothesis
   item 6's `hIntStage`/`hIntLim` instances carry) and the
   explicitly named all-of-`L²` positivity hypothesis
   `LayerKernelPosAll` below, the frozen
   `SeatFactorApproxExpansion μG ρ hN β` HOLDS, at every
   `Even N` (hence in particular on GATE-4C's re-pinned
   `4 ≤ N` domain).

## The seam, named exactly (why this is PARTIAL, not FULL)

Item 5 as frozen assumes only `LayerKernelPos` — positivity
of the `𝒜`-pairing on GAUGE-INVARIANT layer observables. The
compression route consumes positivity on ALL of `L²(layer)`:
the finite compressions are compressions of the layer operator
to spans of a general Hilbert basis of `L²(layer)`, whose
vectors are not gauge-invariant, and `LayerKernelPos` says
nothing about them. This is the proceed-run equivalence, now
touched from the sufficient side: this module proves
`LayerKernelPosAll ⇒ SeatFactorApproxExpansion` (under
`hρcont`), where `LayerKernelPosAll` is positivity of the
layer-kernel operator on all of `L²(layer)` — a Gram/PSD fact
about `𝒜` itself, strictly stronger than `LayerKernelPos`,
proved NOWHERE in the corpus. The invariant-subspace variant
of the route cannot substitute: Gram sums built from
gauge-invariant factors are invariant in the first kernel slot
separately, and HS limits preserve that invariance, while
`layerKernel` is not separately first-slot invariant in
general (G2c dossier obstruction, on record). No step of this
module proves, refutes, or uses `LayerKernelPos` itself.

## Kills — status

- **K-GATE-3** (exact-finite smuggling): NOT fired, NOT
  committed. No approximating sequence is fed to the exact-
  finite conditional `seatSchurTarget_of_finiteRankProductStep`;
  that theorem is not cited anywhere in this module.
- **K-GATE-2** (spectral smuggling): NOT committed. No
  infinite-dimensional spectral theorem is cited. The only
  diagonalization consumed is the finite-dimensional
  `Matrix.posSemidef_iff_eq_sum_vecMulVec` factorization of a
  finite compression matrix — the scoping's prescribed
  compression engine.
- **K-F2-2** (a `MemLp` Gram of `𝒜` itself): the audit point
  is met head-on and reported, not shipped as a weld brick:
  this module's conditional headline is exactly a Gram/PSD
  fact about `𝒜` (through `LayerKernelPosAll`), re-tiered
  here as a CORE-CHAIN result — the item-5 lane is the core
  chain's own lane, and the landing is reported as core work,
  not as weld progress. Note the fence inside the route
  itself: the expansion produced is a LIMIT of finite Grams;
  no single `MemLp` Gram family for `𝒜` is produced (a
  positive HS operator's square root need not be HS), so
  `posKernel_gram` does not apply to it and `LayerKernelPos`
  is not proved by this module.
- **K-F2-3** (generality creep): no seat is narrowed; the
  conditional headline is at general `(G, ρ)`, every `Even N`.
- **K-F2-4** (buy inflation): nothing here is progress on
  FACT, `𝒜 ⪰ 0`, clause (a), or uniformity beyond what the
  theorems literally state. `LayerKernelPosAll` is a
  hypothesis, not a result.

**NO CLAIM** — parts of any official Millennium statement
closed by this module: 0. Dials: 0/4.

This module is NOT in the root import list of the library;
it is verified by a targeted build.
-/

import ThetLogos.Span3SeatSchurGatePost
import ThetLogos.Span3SeatSchurGateItem6
import ThetLogos.IntegralKernelSchur
import ThetLogos.HilbertSchmidt
import Mathlib.Analysis.InnerProductSpace.Positive

namespace ThetLogos

open MeasureTheory Finset Filter Topology ComplexInnerProductSpace
open scoped Matrix ENNReal NNReal ComplexOrder

/-! ## General helpers -/

/- Two vectors in a Hilbert space agreeing against every test
vector are equal (the inner-product extensionality step used
throughout the compression identifications). -/
theorem eq_of_forall_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {v w : E}
    (h : ∀ g : E, ⟪g, v⟫ = ⟪g, w⟫) : v = w := by
  have h2 : ⟪v - w, v - w⟫ = 0 := by
    rw [inner_sub_right, h (v - w), sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h2)

/- Summability passes to a subtype for a nonnegative real
family (the tail families of the HS bound are all of this
shape). -/
theorem summable_subtype_of_nonneg {ι : Type*} {f : ι → ℝ}
    (hf : Summable f) (h0 : ∀ i, 0 ≤ f i) (s : Set ι) :
    Summable (fun i : s => f i) := by
  classical
  have hle : ∑' i : s, ENNReal.ofReal (f i)
      ≤ ∑' i, ENNReal.ofReal (f i) := by
    have hsupp : Function.support
        (fun i => if i ∈ s then ENNReal.ofReal (f i) else 0)
        ⊆ s := by
      intro i hi
      by_contra his
      exact hi (by simp [his])
    have h1 : ∑' i : s, ENNReal.ofReal (f i)
        = ∑' i : s, (fun j => if j ∈ s then ENNReal.ofReal (f j)
            else 0) i := by
      refine tsum_congr fun i => ?_
      simp [i.2]
    rw [h1, tsum_subtype_eq_of_support_subset hsupp]
    refine ENNReal.tsum_le_tsum fun i => ?_
    by_cases hi : i ∈ s <;> simp [hi]
  have hne : ∑' i : s, ENNReal.ofReal (f i) ≠ ∞ :=
    ne_top_of_le_ne_top
      (Summable.tsum_ofReal_ne_top hf) hle
  exact (ENNReal.summable_toReal hne).congr
    (fun i => ENNReal.toReal_ofReal (h0 i))

/-! ## The compression engine (general kernel level)

Fix a probability space `(α, μ)`, an `L²` kernel `K` with its
integral operator `T`, a Hilbert basis `b` of `L²(μ)`, and a
finite set `F` of basis indices. The compression matrix is the
matrix of `T` in the basis over `F`; under positivity on all
of `L²` plus self-adjointness it is a positive semidefinite
matrix, hence a finite Gram sum, and the associated Gram
kernel is the kernel of the compression `P_F T P_F`. -/

/-- Splitting an `ℝ≥0∞` sum over a finite set and its
complement (subtype form). -/
theorem tsum_eq_add_tsum_subtype_compl_ENN {ι : Type*}
    (g : ι → ℝ≥0∞) (F : Finset ι) :
    (∑' i : F, g (i : ι)) + (∑' i : ↥(F : Set ι)ᶜ, g (i : ι))
      = ∑' i, g i := by
  rw [tsum_fintype, Finset.univ_eq_attach, Finset.sum_attach]
  exact ENNReal.sum_add_tsum_compl F g

/-- An `ℝ≥0∞` sum over a finite subtype is bounded by the
full sum. -/
theorem tsum_subtype_le_full_ENN {ι : Type*} (g : ι → ℝ≥0∞)
    (F : Finset ι) :
    (∑' i : F, g (i : ι)) ≤ ∑' i, g i := by
  conv_rhs => rw [← tsum_eq_add_tsum_subtype_compl_ENN g F]
  exact le_add_right le_rfl

/-- An `ℝ≥0∞` sum over a cofinite subtype is bounded by the
full sum. -/
theorem tsum_compl_subtype_le_full_ENN {ι : Type*}
    (g : ι → ℝ≥0∞) (F : Finset ι) :
    (∑' i : ↥(F : Set ι)ᶜ, g (i : ι)) ≤ ∑' i, g i := by
  conv_rhs => rw [← ENNReal.sum_add_tsum_compl F g]
  exact le_add_left le_rfl

section Compression

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ]
  {K : α × α → ℂ} (hK : MemLp K 2 (μ.prod μ))
  {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 μ))

/- **The compression matrix**: the matrix of the kernel
operator `T = integralKernelOp hK` in the Hilbert basis `b`,
compressed to the finite index set `F`:
`A i j = ⟪b i, T (b j)⟫`. -/
noncomputable def compressionMatrix (F : Finset ι) :
    Matrix F F ℂ :=
  Matrix.of fun i j =>
    ⟪(b (i : ι) : Lp ℂ 2 μ), integralKernelOp hK (b (j : ι))⟫

/-- **The compression matrix is positive semidefinite.**
Hermitian by the self-adjointness hypothesis (conjugate
symmetry of the inner product plus `⟪T x, y⟫ = ⟪x, T y⟫`);
the quadratic form at `v` is the `T`-pairing of the basis
combination `∑ j, v j • b j` with itself, nonnegative in real
part by `PosKernel`, with vanishing imaginary part again by
self-adjointness. This is the finite-dimensional heart of
the compression route: no infinite-dimensional spectral
input anywhere (K-GATE-2 respected). -/
theorem compressionMatrix_posSemidef (F : Finset ι)
    (hPos : PosKernel K hK)
    (hSA : ∀ f g : Lp ℂ 2 μ,
      ⟪integralKernelOp hK f, g⟫ = ⟪f, integralKernelOp hK g⟫) :
    (compressionMatrix hK b F).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, compressionMatrix,
      Matrix.of_apply]
    show (starRingEnd ℂ)
        ⟪(b (j : ι) : Lp ℂ 2 μ), integralKernelOp hK (b (i : ι))⟫
      = ⟪(b (i : ι) : Lp ℂ 2 μ), integralKernelOp hK (b (j : ι))⟫
    rw [inner_conj_symm]
    exact hSA (b (i : ι)) (b (j : ι))
  · intro v
    have hS : (star v) ⬝ᵥ
          ((compressionMatrix hK b F) *ᵥ v)
        = ⟪(∑ j : F, v j • (b (j : ι) : Lp ℂ 2 μ)),
            integralKernelOp hK
              (∑ j : F, v j • (b (j : ι) : Lp ℂ 2 μ))⟫ := by
      have hIn : ⟪(∑ j : F, v j • (b (j : ι) : Lp ℂ 2 μ)),
              integralKernelOp hK
                (∑ j : F, v j • (b (j : ι) : Lp ℂ 2 μ))⟫
          = ∑ i : F, ∑ j : F, (starRingEnd ℂ) (v i)
              * (⟪(b (i : ι) : Lp ℂ 2 μ),
                  integralKernelOp hK (b (j : ι))⟫ * v j) := by
        rw [map_sum, sum_inner]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [inner_smul_left, inner_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, inner_smul_right]
        ring
      rw [hIn]
      simp only [dotProduct, Matrix.mulVec, compressionMatrix,
        Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      show star (v i) * (⟪(b (i : ι) : Lp ℂ 2 μ),
          integralKernelOp hK (b (j : ι))⟫ * v j)
        = (starRingEnd ℂ) (v i) * (⟪(b (i : ι) : Lp ℂ 2 μ),
          integralKernelOp hK (b (j : ι))⟫ * v j)
      rw [starRingEnd_apply, RCLike.star_def]
    rw [hS]
    refine RCLike.nonneg_iff.mpr ⟨hPos _, ?_⟩
    have hconj : (starRingEnd ℂ)
        ⟪(∑ j : F, v j • (b (j : ι) : Lp ℂ 2 μ)),
          integralKernelOp hK
            (∑ j : F, v j • (b (j : ι) : Lp ℂ 2 μ))⟫
      = ⟪(∑ j : F, v j • (b (j : ι) : Lp ℂ 2 μ)),
          integralKernelOp hK
            (∑ j : F, v j • (b (j : ι) : Lp ℂ 2 μ))⟫ := by
      rw [inner_conj_symm]
      exact hSA _ _
    exact Complex.conj_eq_iff_im.mp hconj

/-- **Finite Gram factorization of the compression**: a
positive semidefinite matrix over `ℂ` is a finite sum of
rank-one Gram matrices `vecMulVec (v k) (star (v k))`
(Mathlib's finite-dimensional factorization — the owned
stock the GATE-3 scoping prescribes). -/
theorem exists_compression_gram (F : Finset ι)
    (hPos : PosKernel K hK)
    (hSA : ∀ f g : Lp ℂ 2 μ,
      ⟪integralKernelOp hK f, g⟫ = ⟪f, integralKernelOp hK g⟫) :
    ∃ (m : ℕ) (v : Fin m → (F → ℂ)),
      compressionMatrix hK b F
        = ∑ k, Matrix.vecMulVec (v k) (star (v k)) :=
  Matrix.posSemidef_iff_eq_sum_vecMulVec.mp
    (compressionMatrix_posSemidef hK b F hPos hSA)

/-- **The Gram factors of a compression**, as `L²` vectors:
the `k`-th factor is the basis combination with coefficients
`v k`. -/
noncomputable def gramFactor (F : Finset ι) {m : ℕ}
    (v : Fin m → (F → ℂ)) (k : Fin m) : Lp ℂ 2 μ :=
  ∑ j : F, v k j • (b (j : ι) : Lp ℂ 2 μ)

/-- **The Gram kernel of a compression**: the finite
Gram-shaped kernel `∑ k, φ k (x) * conj (φ k (y))` built
from the Gram factors — with the corpus's kernel convention
(`integralKernelFun ν K f x = ∫ y, K (x, y) * f y`) its
operator is the projection-shaped sum `f ↦ ∑ k, ⟪φ k, f⟫ • φ k`
(`inner_integralKernelOp_gramKernelOf` below). -/
noncomputable def gramKernelOf (F : Finset ι) {m : ℕ}
    (v : Fin m → (F → ℂ)) : α × α → ℂ :=
  fun p => ∑ k, (gramFactor b F v k) p.1
    * (starRingEnd ℂ) ((gramFactor b F v k) p.2)

/-- **One Gram summand is `MemLp 2`**: the separated tensor
`φ (x) * conj (φ (y))` of an `L²` factor with itself, via
the landed tensor `MemLp` and a pointwise conjugation
identity. -/
theorem gramTerm_memLp (F : Finset ι) {m : ℕ}
    (v : Fin m → (F → ℂ)) (k : Fin m) :
    MemLp (fun p : α × α => (gramFactor b F v k) p.1
      * (starRingEnd ℂ) ((gramFactor b F v k) p.2))
      2 (μ.prod μ) := by
  have hterm : MemLp
      (fun p : α × α => star ((gramFactor b F v k) p.1)
        * (gramFactor b F v k) p.2) 2 (μ.prod μ) :=
    memLp_tensor_fin _ _
  have hstar := hterm.star
  refine (memLp_congr_ae (Filter.Eventually.of_forall fun p => ?_)).mp
    hstar
  show star (star ((gramFactor b F v k) p.1)
        * (gramFactor b F v k) p.2)
    = (gramFactor b F v k) p.1
      * (starRingEnd ℂ) ((gramFactor b F v k) p.2)
  rw [star_mul, star_star]
  exact mul_comm _ _

/-- **The Gram kernel of a compression is `MemLp 2`**: a
finite sum of its `MemLp` summands. -/
theorem gramKernelOf_memLp (F : Finset ι) {m : ℕ}
    (v : Fin m → (F → ℂ)) :
    MemLp (gramKernelOf b F v) 2 (μ.prod μ) := by
  have hdef : gramKernelOf b F v
      = fun p : α × α => ∑ k, (gramFactor b F v k) p.1
        * (starRingEnd ℂ) ((gramFactor b F v k) p.2) := rfl
  rw [hdef]
  exact memLp_finsetSum Finset.univ
    (fun k _ => gramTerm_memLp b F v k)

omit [IsProbabilityMeasure μ] in
/-- The `Lp` inner product as an integral of the pointwise
conjugate product, in the `star` form the kernel lemmas use. -/
theorem inner_eq_integral_star (g h : Lp ℂ 2 μ) :
    ⟪g, h⟫ = ∫ x, star (⇑g x) * ⇑h x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ⟪⇑g x, ⇑h x⟫ = star (⇑g x) * ⇑h x
  rw [RCLike.inner_apply]
  exact mul_comm _ _

/- **The Gram operator is the projection-shaped sum**:
pairing the Gram kernel's operator against test vectors
separates over the Gram factors.  This is the finite-rank
identity the whole compression route rests on; it is proved
from the landed Fubini separation (`integral_prod_mul`) and
the kernel pairing formula, with no spectral input. -/
theorem inner_integralKernelOp_gramKernelOf (F : Finset ι) {m : ℕ}
    (v : Fin m → (F → ℂ)) (g f : Lp ℂ 2 μ) :
    ⟪g, integralKernelOp (gramKernelOf_memLp b F v) f⟫
      = ∑ k, ⟪g, gramFactor b F v k⟫
          * ⟪gramFactor b F v k, f⟫ := by
  have hrhs : ∀ k : Fin m,
      ⟪g, gramFactor b F v k⟫ * ⟪gramFactor b F v k, f⟫
        = (∫ x, star (⇑g x) * (gramFactor b F v k) x ∂μ)
          * (∫ y, (starRingEnd ℂ) ((gramFactor b F v k) y)
              * ⇑f y ∂μ) := by
    intro k
    rw [inner_eq_integral_star g (gramFactor b F v k),
      inner_eq_integral_star (gramFactor b F v k) f]
    congr 1
  have hInt : ∀ k ∈ Finset.univ,
      Integrable (fun p : α × α =>
        (star (⇑g p.1) * (gramFactor b F v k) p.1)
          * ((starRingEnd ℂ) ((gramFactor b F v k) p.2)
            * ⇑f p.2)) (μ.prod μ) := by
    intro k _
    exact (integrable_kernel_pairing_gen (gramTerm_memLp b F v k)
      g f).congr (Filter.Eventually.of_forall fun p => by ring)
  have hpt : ∀ p : α × α,
      star (⇑g p.1) * ((gramKernelOf b F v) p * ⇑f p.2)
        = ∑ k, (star (⇑g p.1) * (gramFactor b F v k) p.1)
          * ((starRingEnd ℂ) ((gramFactor b F v k) p.2)
            * ⇑f p.2) := by
    intro p
    show star (⇑g p.1)
        * (((∑ k, (gramFactor b F v k) p.1
            * (starRingEnd ℂ) ((gramFactor b F v k) p.2)))
          * ⇑f p.2) = _
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [integralKernelOp_inner,
    integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum Finset.univ hInt]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_prod_mul
    (fun x => star (⇑g x) * (gramFactor b F v k) x)
    (fun y => (starRingEnd ℂ) ((gramFactor b F v k) y) * ⇑f y)]
  exact (hrhs k).symm

omit [IsProbabilityMeasure μ] in
/-- Coefficients of a Gram factor against a test vector:
linear in the second slot, no conjugation. -/
theorem inner_gramFactor_right (F : Finset ι) {m : ℕ}
    (v : Fin m → (F → ℂ)) (k : Fin m) (g : Lp ℂ 2 μ) :
    ⟪g, gramFactor b F v k⟫
      = ∑ j : F, v k j * ⟪g, (b (j : ι) : Lp ℂ 2 μ)⟫ := by
  unfold gramFactor
  rw [inner_sum]
  exact Finset.sum_congr rfl fun j _ => inner_smul_right _ _ _

/- Coefficients of a Gram factor in the first slot:
conjugate-linearity produces the conjugated coefficients
against the basis–basis Gram matrix. -/
omit [IsProbabilityMeasure μ] in
theorem inner_gramFactor_basis (F : Finset ι) {m : ℕ}
    (v : Fin m → (F → ℂ)) (k : Fin m) (i : ι) :
    ⟪gramFactor b F v k, (b i : Lp ℂ 2 μ)⟫
      = ∑ j : F, (starRingEnd ℂ) (v k j)
          * ⟪(b (j : ι) : Lp ℂ 2 μ), (b i : Lp ℂ 2 μ)⟫ := by
  unfold gramFactor
  rw [sum_inner]
  exact Finset.sum_congr rfl fun j _ => inner_smul_left _ _ _

omit [IsProbabilityMeasure μ] in
/-- At a basis index inside `F`, the first-slot coefficient
of a Gram factor is the conjugated Gram coefficient. -/
theorem inner_gramFactor_basis_of_mem (F : Finset ι) {m : ℕ}
    (v : Fin m → (F → ℂ)) (k : Fin m) {i : ι} (hi : i ∈ F) :
    ⟪gramFactor b F v k, (b i : Lp ℂ 2 μ)⟫
      = (starRingEnd ℂ) (v k ⟨i, hi⟩) := by
  classical
  rw [inner_gramFactor_basis]
  have hortho : ∀ j : F,
      ⟪(b (j : ι) : Lp ℂ 2 μ), (b i : Lp ℂ 2 μ)⟫
        = if (j : ι) = i then 1 else 0 :=
    fun j => orthonormal_iff_ite.mp b.orthonormal (j : ι) i
  rw [Finset.sum_congr rfl (fun j _ => by rw [hortho j])]
  have hterm : ∀ j ∈ (Finset.univ : Finset F),
      (starRingEnd ℂ) (v k j) * (if (j : ι) = i then (1 : ℂ) else 0)
        = if j = ⟨i, hi⟩ then (starRingEnd ℂ) (v k j) else 0 := by
    intro j _
    by_cases h : (j : ι) = i
    · have hj : j = ⟨i, hi⟩ := Subtype.ext h
      simp [hj]
    · have hj : j ≠ ⟨i, hi⟩ :=
        fun hj => h (Subtype.ext_iff.mp hj)
      simp [h, hj]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  simp

omit [IsProbabilityMeasure μ] in
/-- At a basis index outside `F`, the first-slot coefficient
of a Gram factor vanishes. -/
theorem inner_gramFactor_basis_of_not_mem (F : Finset ι) {m : ℕ}
    (v : Fin m → (F → ℂ)) (k : Fin m) {i : ι} (hi : i ∉ F) :
    ⟪gramFactor b F v k, (b i : Lp ℂ 2 μ)⟫ = 0 := by
  classical
  rw [inner_gramFactor_basis]
  apply Finset.sum_eq_zero
  intro j _
  have hji : (j : ι) ≠ i := fun h => hi (by rw [← h]; exact j.2)
  simp [orthonormal_iff_ite.mp b.orthonormal (j : ι) i, hji]

/-- The entries of the compression matrix in terms of the
Gram coefficients from
`Matrix.posSemidef_iff_eq_sum_vecMulVec`. -/
theorem compressionMatrix_apply (F : Finset ι) {m : ℕ}
    (v : Fin m → (F → ℂ))
    (hv : compressionMatrix hK b F
      = ∑ k, Matrix.vecMulVec (v k) (star (v k)))
    (j i' : F) :
    (compressionMatrix hK b F) j i'
      = ∑ k, v k j * (starRingEnd ℂ) (v k i') := by
  have h := congrArg (fun M : Matrix F F ℂ => M j i') hv
  rw [h, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  show (Matrix.vecMulVec (v k) (star (v k))) j i'
    = v k j * (starRingEnd ℂ) (v k i')
  rfl

/-- **The Gram operator at a basis vector inside `F` is the
finite basis projection of the operator**: the compression
at `F` reproduces `T` exactly on the `F`-directions after
projection.  Proved by pairing against arbitrary test
vectors and expanding both sides into the compression
matrix entries. -/
theorem integralKernelOp_gramKernelOf_apply_basis_mem
    (F : Finset ι) {m : ℕ} (v : Fin m → (F → ℂ))
    (hv : compressionMatrix hK b F
      = ∑ k, Matrix.vecMulVec (v k) (star (v k)))
    {i : ι} (hi : i ∈ F) :
    integralKernelOp (gramKernelOf_memLp b F v) (b i)
      = hsProjSum b F (integralKernelOp hK (b i)) := by
  apply eq_of_forall_inner
  intro g
  calc ⟪g, integralKernelOp (gramKernelOf_memLp b F v) (b i)⟫
      = ∑ k, (∑ j : F, v k j * ⟪g, (b (j : ι) : Lp ℂ 2 μ)⟫)
          * (starRingEnd ℂ) (v k ⟨i, hi⟩) := by
        rw [inner_integralKernelOp_gramKernelOf]
        exact Finset.sum_congr rfl fun k _ => by
          rw [inner_gramFactor_right,
            inner_gramFactor_basis_of_mem b F v k hi]
    _ = ∑ k, ∑ j : F, (v k j * (starRingEnd ℂ) (v k ⟨i, hi⟩))
          * ⟪g, (b (j : ι) : Lp ℂ 2 μ)⟫ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j : F, ∑ k, (v k j * (starRingEnd ℂ) (v k ⟨i, hi⟩))
          * ⟪g, (b (j : ι) : Lp ℂ 2 μ)⟫ :=
        Finset.sum_comm
    _ = ∑ j : F, (compressionMatrix hK b F) j ⟨i, hi⟩
          * ⟪g, (b (j : ι) : Lp ℂ 2 μ)⟫ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have e : (∑ k, v k j * (starRingEnd ℂ) (v k ⟨i, hi⟩))
            = (compressionMatrix hK b F) j ⟨i, hi⟩ :=
          (compressionMatrix_apply hK b F v hv j ⟨i, hi⟩).symm
        rw [← e, Finset.sum_mul]
    _ = ∑ j : F, ⟪(b (j : ι) : Lp ℂ 2 μ),
            integralKernelOp hK (b i)⟫
          * ⟪g, (b (j : ι) : Lp ℂ 2 μ)⟫ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rfl
    _ = ∑ j ∈ F, ⟪(b j : Lp ℂ 2 μ),
            integralKernelOp hK (b i)⟫
          * ⟪g, (b j : Lp ℂ 2 μ)⟫ :=
        Finset.sum_attach F
          (fun j => ⟪(b j : Lp ℂ 2 μ),
            integralKernelOp hK (b i)⟫ * ⟪g, (b j : Lp ℂ 2 μ)⟫)
    _ = ⟪g, hsProjSum b F (integralKernelOp hK (b i))⟫ := by
        rw [hsProjSum_apply, inner_sum]
        exact Finset.sum_congr rfl fun j _ =>
          (inner_smul_right _ _ _).symm

/-- **The Gram operator kills basis vectors outside `F`**:
the finite compression sees only its own directions. -/
theorem integralKernelOp_gramKernelOf_apply_basis_not_mem
    (F : Finset ι) {m : ℕ} (v : Fin m → (F → ℂ))
    {i : ι} (hi : i ∉ F) :
    integralKernelOp (gramKernelOf_memLp b F v) (b i) = 0 := by
  apply eq_of_forall_inner
  intro g
  rw [inner_integralKernelOp_gramKernelOf, inner_zero_right]
  exact Finset.sum_eq_zero fun k _ => by
    rw [inner_gramFactor_basis_of_not_mem b F v k hi, mul_zero]

/-- **The difference operator is the operator difference**:
the kernel `K - G` (pointwise) induces `T - T_G` as a
continuous linear map, checked on pairings. -/
theorem integralKernelOp_sub_apply (F : Finset ι) {m : ℕ}
    (v : Fin m → (F → ℂ)) (f : Lp ℂ 2 μ) :
    integralKernelOp (hK.sub (gramKernelOf_memLp b F v)) f
      = integralKernelOp hK f
        - integralKernelOp (gramKernelOf_memLp b F v) f := by
  apply eq_of_forall_inner
  intro g
  rw [inner_sub_right]
  simp only [integralKernelOp_inner]
  rw [← integral_sub (integrable_kernel_pairing_gen hK g f)
    (integrable_kernel_pairing_gen (gramKernelOf_memLp b F v) g f)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [Pi.sub_apply]
  ring

open Classical in
/-- **The coefficient majorant**: the `ℝ≥0∞` size of the
difference operator's `(j, i)` Fourier coefficient is
controlled by the corresponding coefficient of `T` itself,
except in the `F × F` block, where it vanishes exactly. -/
noncomputable def gramMajorant (F : Finset ι) (i j : ι) : ℝ≥0∞ :=
  if i ∈ F then
    (if j ∈ F then 0
      else ENNReal.ofReal (‖⟪(b j : Lp ℂ 2 μ),
        integralKernelOp hK (b i)⟫‖ ^ 2))
  else ENNReal.ofReal (‖⟪(b j : Lp ℂ 2 μ),
      integralKernelOp hK (b i)⟫‖ ^ 2)

theorem gramMajorant_of_mem_of_mem (F : Finset ι) {i j : ι}
    (hi : i ∈ F) (hj : j ∈ F) :
    gramMajorant hK b F i j = 0 := by
  unfold gramMajorant
  rw [ite_eq_left hi, ite_eq_left hj]

theorem gramMajorant_of_mem_of_not_mem (F : Finset ι) {i j : ι}
    (hi : i ∈ F) (hj : j ∉ F) :
    gramMajorant hK b F i j
      = ENNReal.ofReal (‖⟪(b j : Lp ℂ 2 μ),
          integralKernelOp hK (b i)⟫‖ ^ 2) := by
  unfold gramMajorant
  rw [ite_eq_left hi, ite_eq_right hj]

theorem gramMajorant_of_not_mem (F : Finset ι) {i j : ι}
    (hi : i ∉ F) :
    gramMajorant hK b F i j
      = ENNReal.ofReal (‖⟪(b j : Lp ℂ 2 μ),
          integralKernelOp hK (b i)⟫‖ ^ 2) := by
  unfold gramMajorant
  rw [ite_eq_right hi]

/-- **The difference coefficients are the majorant**: the
Fourier coefficients of `T - T_G` agree with `gramMajorant`
exactly — zero on the `F × F` block (the residual's
coefficients vanish inside `F`), and equal to `T`'s
coefficients elsewhere (the projection does not touch the
outside coefficients, and the Gram operator kills outside
directions). -/
theorem enn_coe_eq (F : Finset ι) {m : ℕ} (v : Fin m → (F → ℂ))
    (hv : compressionMatrix hK b F
      = ∑ k, Matrix.vecMulVec (v k) (star (v k)))
    (i j : ι) :
    ENNReal.ofReal (‖⟪(b j : Lp ℂ 2 μ),
        integralKernelOp (hK.sub (gramKernelOf_memLp b F v))
          (b i)⟫‖ ^ 2)
      = gramMajorant hK b F i j := by
  classical
  have hTD := integralKernelOp_sub_apply hK b F v (b i)
  by_cases hi : i ∈ F
  · rw [hTD,
      integralKernelOp_gramKernelOf_apply_basis_mem hK b F v hv hi]
    by_cases hj : j ∈ F
    · rw [gramMajorant_of_mem_of_mem hK b F hi hj,
        hs_inner_projSum_residual_of_mem b F _ hj]
      simp
    · rw [gramMajorant_of_mem_of_not_mem hK b F hi hj,
        hs_inner_projSum_residual_of_not_mem b F _ hj]
  · rw [gramMajorant_of_not_mem hK b F hi, hTD,
      integralKernelOp_gramKernelOf_apply_basis_not_mem b F v hi]
    simp

omit [IsProbabilityMeasure μ] in
/-- Parseval in `ℝ≥0∞` form: the `ofReal`-sum of squared
Fourier coefficients of a vector is `ofReal` of its squared
norm. -/
theorem enn_ofReal_tsum_inner_eq (x : Lp ℂ 2 μ) :
    (∑' j, ENNReal.ofReal (‖⟪(b j : Lp ℂ 2 μ), x⟫‖ ^ 2))
      = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← hsParseval_tsum b x]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _)
    (hsSummable_inner_sq b x)).symm

/-- The `ℝ≥0∞` HS summand is `ofReal` of the squared norm
of the operator's value. -/
theorem hsSummandENN_eq_ofReal {D : α × α → ℂ}
    (hD : MemLp D 2 (μ.prod μ)) (i : ι) :
    hsSummandENN hD b i
      = ENNReal.ofReal (‖integralKernelOp hD (b i)‖ ^ 2) := by
  show (eLpNorm ⇑(integralKernelOp hD (b i)) 2 μ) ^ 2 = _
  have e1 : eLpNorm ⇑(integralKernelOp hD (b i)) 2 μ
      = ENNReal.ofReal ‖integralKernelOp hD (b i)‖ := by
    rw [← ENNReal.ofReal_toReal
      (MeasureTheory.Lp.memLp _).eLpNorm_lt_top.ne, Lp.norm_def]
  rw [e1, ← ENNReal.ofReal_pow (norm_nonneg _) 2]

omit [IsProbabilityMeasure μ] in
/-- The `ℝ≥0∞` tail is `hsTailSq` after `toReal`. -/
theorem tailENN_toReal (S : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ))
    (F : Finset ι) :
    (∑' i : ↥(F : Set ι)ᶜ, ENNReal.ofReal
      (‖S (b (i : ι))‖ ^ 2)).toReal = hsTailSq S b F := by
  show (∑' i : ↥(F : Set ι)ᶜ, ENNReal.ofReal
      (‖S (b (i : ι))‖ ^ 2)).toReal
    = ∑' i : ↥(F : Set ι)ᶜ, ‖S (b (i : ι))‖ ^ 2
  rw [ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_ne_top)]
  exact tsum_congr fun i => ENNReal.toReal_ofReal (sq_nonneg _)

/-- **The HS bound for one compression stage**: the squared
`L²` distance from `K` to its `F`-compression Gram kernel is
at most the sum of the two HS tails of `T` outside `F` —
`T`'s own tail and its adjoint's.  This is the quantitative
form of the compression seam: the bound is small exactly
when the tails are, and both tails vanish along `atTop` by
the landed `hs_tailSq_tendsto_zero`. -/
theorem eLpNorm_sub_gram_sq_le (F : Finset ι) {m : ℕ}
    (v : Fin m → (F → ℂ))
    (hv : compressionMatrix hK b F
      = ∑ k, Matrix.vecMulVec (v k) (star (v k))) :
    (eLpNorm (fun p => K p - gramKernelOf b F v p)
      2 (μ.prod μ)).toReal ^ 2
      ≤ hsTailSq (integralKernelOp hK) b F
        + hsTailSq (ContinuousLinearMap.adjoint
            (integralKernelOp hK)) b F := by
  classical
  have hBi : ∀ i : ↥(F : Set ι)ᶜ,
      hsSummandENN (hK.sub (gramKernelOf_memLp b F v)) b (i : ι)
        = ENNReal.ofReal
            (‖integralKernelOp hK (b (i : ι))‖ ^ 2) := by
    intro i
    calc hsSummandENN (hK.sub (gramKernelOf_memLp b F v)) b (i : ι)
        = ∑' j, ENNReal.ofReal (‖⟪(b j : Lp ℂ 2 μ),
            integralKernelOp (hK.sub (gramKernelOf_memLp b F v))
              (b (i : ι))⟫‖ ^ 2) := by
          rw [hsSummandENN_eq_ofReal, ← enn_ofReal_tsum_inner_eq]
      _ = ∑' j, gramMajorant hK b F (i : ι) j :=
          tsum_congr fun j => enn_coe_eq hK b F v hv (i : ι) j
      _ = ∑' j, ENNReal.ofReal (‖⟪(b j : Lp ℂ 2 μ),
            integralKernelOp hK (b (i : ι))⟫‖ ^ 2) :=
          tsum_congr fun j =>
            gramMajorant_of_not_mem hK b F (show (i : ι) ∉ F from i.2)
      _ = ENNReal.ofReal
            (‖integralKernelOp hK (b (i : ι))‖ ^ 2) :=
          enn_ofReal_tsum_inner_eq b _
  have hAeq : ∀ i : F,
      hsSummandENN (hK.sub (gramKernelOf_memLp b F v)) b (i : ι)
        = ∑' j : ↥(F : Set ι)ᶜ, ENNReal.ofReal
            (‖⟪(b (j : ι) : Lp ℂ 2 μ),
              integralKernelOp hK (b (i : ι))⟫‖ ^ 2) := by
    intro i
    calc hsSummandENN (hK.sub (gramKernelOf_memLp b F v)) b (i : ι)
        = ∑' j, gramMajorant hK b F (i : ι) j := by
          rw [hsSummandENN_eq_ofReal, ← enn_ofReal_tsum_inner_eq]
          exact tsum_congr fun j =>
            enn_coe_eq hK b F v hv (i : ι) j
      _ = (∑' j : ↥(F : Set ι)ᶜ, gramMajorant hK b F (i : ι) (j : ι))
          + (∑' j : F, gramMajorant hK b F (i : ι) (j : ι)) := by
          rw [add_comm]
          exact (tsum_eq_add_tsum_subtype_compl_ENN _ F).symm
      _ = (∑' j : ↥(F : Set ι)ᶜ, ENNReal.ofReal
            (‖⟪(b (j : ι) : Lp ℂ 2 μ),
              integralKernelOp hK (b (i : ι))⟫‖ ^ 2)) + 0 := by
          congr 1
          · exact tsum_congr fun j =>
              gramMajorant_of_mem_of_not_mem hK b F i.2
                (show (j : ι) ∉ F from j.2)
          · rw [tsum_congr (fun j : F =>
              gramMajorant_of_mem_of_mem hK b F i.2 j.2), tsum_zero]
      _ = ∑' j : ↥(F : Set ι)ᶜ, ENNReal.ofReal
            (‖⟪(b (j : ι) : Lp ℂ 2 μ),
              integralKernelOp hK (b (i : ι))⟫‖ ^ 2) :=
          add_zero _
  have hA : (∑' i : F, ∑' j : ↥(F : Set ι)ᶜ, ENNReal.ofReal
        (‖⟪(b (j : ι) : Lp ℂ 2 μ),
          integralKernelOp hK (b (i : ι))⟫‖ ^ 2))
      ≤ ∑' j : ↥(F : Set ι)ᶜ, ENNReal.ofReal
          (‖(ContinuousLinearMap.adjoint (integralKernelOp hK))
            (b (j : ι))‖ ^ 2) := by
    rw [ENNReal.tsum_comm]
    refine ENNReal.tsum_le_tsum fun j => ?_
    calc (∑' i : F, ENNReal.ofReal
          (‖⟪(b (j : ι) : Lp ℂ 2 μ),
            integralKernelOp hK (b (i : ι))⟫‖ ^ 2))
        = ∑' i : F, ENNReal.ofReal
            (‖⟪(b (i : ι) : Lp ℂ 2 μ),
              (ContinuousLinearMap.adjoint (integralKernelOp hK))
                (b (j : ι))⟫‖ ^ 2) :=
          tsum_congr fun i => by
            rw [hs_norm_inner_adjoint (integralKernelOp hK) b b
              (i : ι) (j : ι)]
      _ ≤ ∑' i, ENNReal.ofReal
            (‖⟪(b i : Lp ℂ 2 μ),
              (ContinuousLinearMap.adjoint (integralKernelOp hK))
                (b (j : ι))⟫‖ ^ 2) :=
          tsum_subtype_le_full_ENN
            (fun y => ENNReal.ofReal (‖⟪(b y : Lp ℂ 2 μ),
              (ContinuousLinearMap.adjoint (integralKernelOp hK))
                (b (j : ι))⟫‖ ^ 2)) F
      _ = ENNReal.ofReal
            (‖(ContinuousLinearMap.adjoint (integralKernelOp hK))
              (b (j : ι))‖ ^ 2) :=
          enn_ofReal_tsum_inner_eq b _
  have hTstar : Summable (fun i =>
      ‖(ContinuousLinearMap.adjoint (integralKernelOp hK))
        (b i)‖ ^ 2) :=
    (isHilbertSchmidt_iff _ b).mp
      (integralKernel_isHilbertSchmidt hK).adjoint
  have htailTne : (∑' i : ↥(F : Set ι)ᶜ, ENNReal.ofReal
      (‖integralKernelOp hK (b (i : ι))‖ ^ 2)) ≠ ∞ := by
    refine ne_top_of_le_ne_top
      (b := ∑' i, hsSummandENN hK b i) ?_ ?_
    · rw [integralKernel_hs_identity_enn hK b]
      exact ENNReal.pow_ne_top hK.eLpNorm_lt_top.ne
    · calc (∑' i : ↥(F : Set ι)ᶜ, ENNReal.ofReal
          (‖integralKernelOp hK (b (i : ι))‖ ^ 2))
          = ∑' i : ↥(F : Set ι)ᶜ, hsSummandENN hK b (i : ι) :=
            tsum_congr fun i =>
              (hsSummandENN_eq_ofReal b hK (i : ι)).symm
        _ ≤ ∑' i, hsSummandENN hK b i :=
            tsum_compl_subtype_le_full_ENN _ F
  have htailStne : (∑' j : ↥(F : Set ι)ᶜ, ENNReal.ofReal
      (‖(ContinuousLinearMap.adjoint (integralKernelOp hK))
        (b (j : ι))‖ ^ 2)) ≠ ∞ := by
    refine ne_top_of_le_ne_top
      (b := ∑' j, ENNReal.ofReal
        (‖(ContinuousLinearMap.adjoint (integralKernelOp hK))
          (b j)‖ ^ 2)) ?_ ?_
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
        hTstar]
      exact ENNReal.ofReal_ne_top
    · exact tsum_compl_subtype_le_full_ENN
        (fun j => ENNReal.ofReal
          (‖(ContinuousLinearMap.adjoint (integralKernelOp hK))
            (b j)‖ ^ 2)) F
  have htotal : (∑' i, hsSummandENN
        (hK.sub (gramKernelOf_memLp b F v)) b i)
      ≤ (∑' i : ↥(F : Set ι)ᶜ, ENNReal.ofReal
          (‖integralKernelOp hK (b (i : ι))‖ ^ 2))
        + (∑' j : ↥(F : Set ι)ᶜ, ENNReal.ofReal
            (‖(ContinuousLinearMap.adjoint (integralKernelOp hK))
              (b (j : ι))‖ ^ 2)) := by
    calc (∑' i, hsSummandENN
          (hK.sub (gramKernelOf_memLp b F v)) b i)
        = (∑' i : ↥(F : Set ι)ᶜ, hsSummandENN
              (hK.sub (gramKernelOf_memLp b F v)) b (i : ι))
          + (∑' i : F, hsSummandENN
              (hK.sub (gramKernelOf_memLp b F v)) b (i : ι)) := by
          rw [add_comm]
          exact (tsum_eq_add_tsum_subtype_compl_ENN _ F).symm
      _ = (∑' i : ↥(F : Set ι)ᶜ, ENNReal.ofReal
              (‖integralKernelOp hK (b (i : ι))‖ ^ 2))
          + (∑' i : F, ∑' j : ↥(F : Set ι)ᶜ, ENNReal.ofReal
              (‖⟪(b (j : ι) : Lp ℂ 2 μ),
                integralKernelOp hK (b (i : ι))⟫‖ ^ 2)) := by
          rw [tsum_congr hBi, tsum_congr hAeq]
      _ ≤ (∑' i : ↥(F : Set ι)ᶜ, ENNReal.ofReal
              (‖integralKernelOp hK (b (i : ι))‖ ^ 2))
          + (∑' j : ↥(F : Set ι)ᶜ, ENNReal.ofReal
              (‖(ContinuousLinearMap.adjoint (integralKernelOp hK))
                (b (j : ι))‖ ^ 2)) :=
          add_le_add le_rfl hA
  have hne : (∑' i, hsSummandENN
      (hK.sub (gramKernelOf_memLp b F v)) b i) ≠ ∞ := by
    rw [integralKernel_hs_identity_enn]
    exact ENNReal.pow_ne_top
      (hK.sub (gramKernelOf_memLp b F v)).eLpNorm_lt_top.ne
  have htoReal := (ENNReal.toReal_le_toReal hne
    (ENNReal.add_ne_top.mpr ⟨htailTne, htailStne⟩)).mpr htotal
  rw [integralKernel_hs_identity_enn, ENNReal.toReal_pow,
    ENNReal.toReal_add htailTne htailStne, tailENN_toReal,
    tailENN_toReal] at htoReal
  have hfun : (K - gramKernelOf b F v)
      = (fun p => K p - gramKernelOf b F v p) :=
    funext fun p => rfl
  rwa [hfun] at htoReal

/-- **One compression stage within `ε`**: under positivity
of the kernel operator on all of `L²` plus self-adjointness,
some finite stage's Gram kernel is within `ε` of `K` in the
HS (`L²`) distance.  The stage is produced by taking both
HS tails below `ε²/2`, which the landed tail-vanishing
theorem supplies along `atTop`. -/
theorem exists_approx_stage (hPos : PosKernel K hK)
    (hSA : ∀ f g : Lp ℂ 2 μ, ⟪integralKernelOp hK f, g⟫
      = ⟪f, integralKernelOp hK g⟫) {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : Finset ι) (m : ℕ) (v : Fin m → (F → ℂ)),
      (eLpNorm (fun p => K p - gramKernelOf b F v p)
        2 (μ.prod μ)).toReal < ε := by
  have hT0 := hs_tailSq_tendsto_zero
    (integralKernel_isHilbertSchmidt hK) b
  have hTs0 := hs_tailSq_tendsto_zero
    (integralKernel_isHilbertSchmidt hK).adjoint b
  have hε2 : (0 : ℝ) < ε ^ 2 / 2 := by
    have h := pow_pos hε 2
    linarith
  obtain ⟨F, hF1, hF2⟩ :=
    ((hT0.eventually (eventually_lt_nhds hε2)).and
      (hTs0.eventually (eventually_lt_nhds hε2))).exists
  obtain ⟨m, v, hv⟩ := exists_compression_gram hK b F hPos hSA
  refine ⟨F, m, v, ?_⟩
  have hb := eLpNorm_sub_gram_sq_le hK b F v hv
  have hlt : (eLpNorm (fun p => K p - gramKernelOf b F v p)
      2 (μ.prod μ)).toReal ^ 2 < ε ^ 2 :=
    lt_of_le_of_lt hb (by linarith)
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt

/-- **HS convergence of the compressions**: under positivity
of the kernel operator on all of `L²` plus self-adjointness,
there is a sequence of finite Gram kernels, built from
finite compressions, whose HS distance to `K` tends to
zero.  This is the adapted convergence that the generic
tensor approximation of `IntegralKernelHS` does not provide:
the approximants are Gram kernels of compressions of `T`
itself. -/
theorem exists_seq_tendsto (hPos : PosKernel K hK)
    (hSA : ∀ f g : Lp ℂ 2 μ, ⟪integralKernelOp hK f, g⟫
      = ⟪f, integralKernelOp hK g⟫) :
    ∃ (Fseq : ℕ → Finset ι) (mseq : ℕ → ℕ)
      (vseq : ∀ n, Fin (mseq n) → (↥(Fseq n) → ℂ)),
      Filter.Tendsto (fun n =>
        (eLpNorm (fun p => K p - gramKernelOf b (Fseq n)
            (vseq n) p) 2 (μ.prod μ)).toReal)
        Filter.atTop (nhds 0) := by
  have hex : ∀ n : ℕ, ∃ (F : Finset ι) (m : ℕ)
      (v : Fin m → (↥F → ℂ)),
      (eLpNorm (fun p => K p - gramKernelOf b F v p)
        2 (μ.prod μ)).toReal < 1 / ((n : ℝ) + 1) :=
    fun n => exists_approx_stage hK b hPos hSA
      (by positivity)
  choose Fseq mseq vseq hbound using hex
  refine ⟨Fseq, mseq, vseq, ?_⟩
  refine squeeze_zero (fun n => ENNReal.toReal_nonneg)
    (fun n => le_of_lt (hbound n)) ?_
  exact tendsto_one_div_add_atTop_nhds_zero_nat

end Compression

/-! ## Seat level: the layer kernel as an `L²` kernel

The compression theorem is applied to the layer kernel
itself. The seat-level inputs built here: the layer kernel
is `MemLp` on the product layer space (under the corpus's
representation-regularity hypothesis, threaded exactly as
item 6 threads it); its integral operator is self-adjoint
(the kernel is real and symmetric); and the bottom
extraction `tauBot hN` is measure-preserving, so `L²` data
transports along the swapped pullback with `MemLp` and
`eLpNorm` preserved. The all-of-`L²` positivity hypothesis
is named `LayerKernelPosAll`; it is a hypothesis, proved
nowhere in the corpus. -/

section Seat

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG]
  [Measure.IsMulRightInvariant μG] [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- The layer kernel `𝒜` as a kernel on pairs of layer
configurations. -/
noncomputable def layerKernelFun (β : ℝ) :
    (LayerLink N → G) × (LayerLink N → G) → ℂ :=
  fun p => layerKernel μG ρ β p.1 p.2

/-- The layer kernel is `MemLp 2` on the product layer
space, under the representation-regularity hypothesis
`Continuous fun g => repMatrix ρ g` — the same hypothesis
item 6's regular-case `hIntStage`/`hIntLim` instances
carry. Joint measurability of the Boltzmann factor is item
6's `measurable_layerAction`; the pointwise bound is
`layerKernel_norm_le`. -/
theorem layerKernelFun_memLp
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    MemLp (layerKernelFun μG ρ β) 2
      ((Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)) := by
  classical
  have hAsm : Measurable (fun q :
      ((LayerLink N → G) × (LayerLink N → G))
        × (LayerSite N → G) =>
      (q.2, q.1.1, q.1.2)) :=
    measurable_snd.prodMk
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.comp measurable_fst))
  have h1 : Measurable (fun q : (LayerSite N → G)
        × (LayerLink N → G) × (LayerLink N → G) =>
      (Real.exp (-(layerAction ρ β q.1 q.2.1 q.2.2)) : ℂ)) :=
    Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp
        ((measurable_layerAction ρ hρcont β).neg))
  have hF : Measurable
      ((fun q : (LayerSite N → G) × (LayerLink N → G)
            × (LayerLink N → G) =>
          (Real.exp (-(layerAction ρ β q.1 q.2.1 q.2.2)) : ℂ)) ∘
        (fun q : ((LayerLink N → G) × (LayerLink N → G))
              × (LayerSite N → G) =>
          (q.2, q.1.1, q.1.2))) :=
    h1.comp hAsm
  have hA := hF.aestronglyMeasurable.integral_prod_right'
    (μ := (Measure.pi fun _ : LayerLink N => μG).prod
      (Measure.pi fun _ : LayerLink N => μG))
    (ν := Measure.pi fun _ : LayerSite N => μG)
  refine MemLp.of_bound (hA.congr (ae_of_all
    ((Measure.pi fun _ : LayerLink N => μG).prod
      (Measure.pi fun _ : LayerLink N => μG)) fun p => ?_)) _
    (ae_of_all _ fun p => layerKernel_norm_le μG ρ β p.1 p.2)
  rfl

/-- The layer kernel is real and symmetric: conjugating
swaps the two slots. Reality is `layerKernel_eq_ofReal`;
symmetry is `layerKernel_symm` (at `Even N`). -/
theorem layerKernelFun_conj_swap (hN : Even N) (β : ℝ)
    (p : (LayerLink N → G) × (LayerLink N → G)) :
    (starRingEnd ℂ) (layerKernelFun μG ρ β p)
      = layerKernelFun μG ρ β (p.2, p.1) := by
  have hself : (starRingEnd ℂ) (layerKernelFun μG ρ β p)
      = layerKernelFun μG ρ β p := by
    show (starRingEnd ℂ) (layerKernel μG ρ β p.1 p.2)
      = layerKernel μG ρ β p.1 p.2
    rw [layerKernel_eq_ofReal, Complex.conj_ofReal]
  rw [hself]
  show layerKernel μG ρ β p.1 p.2
    = layerKernel μG ρ β p.2 p.1
  exact layerKernel_symm μG ρ hN β p.1 p.2

/-- **Self-adjointness of the layer operator**: at `Even N`
the layer kernel's integral operator satisfies the
self-adjointness hypothesis of the compression section.
Pointwise this is the conjugate-symmetry
`layerKernelFun_conj_swap`, transported through the pairing
formula `integralKernelOp_inner`, conjugation of the
integral, and the product swap. -/
theorem layerKernelFun_selfAdjoint (hN : Even N) (β : ℝ)
    (hK : MemLp (layerKernelFun μG ρ β) 2
      ((Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)))
    (f g : Lp ℂ 2 (Measure.pi fun _ : LayerLink N => μG)) :
    ⟪integralKernelOp hK f, g⟫
      = ⟪f, integralKernelOp hK g⟫ := by
  have hker : ∀ p : (LayerLink N → G) × (LayerLink N → G),
      (starRingEnd ℂ) (layerKernelFun μG ρ β (p.2, p.1))
        = layerKernelFun μG ρ β p :=
    fun p => layerKernelFun_conj_swap μG ρ hN β (p.2, p.1)
  have hswap : (∫ p : (LayerLink N → G) × (LayerLink N → G),
        (starRingEnd ℂ)
          (star (⇑g p.1)
            * (layerKernelFun μG ρ β p * ⇑f p.2))
        ∂((Measure.pi fun _ : LayerLink N => μG).prod
          (Measure.pi fun _ : LayerLink N => μG)))
      = ∫ p : (LayerLink N → G) × (LayerLink N → G),
        (starRingEnd ℂ)
          (star (⇑g p.2)
            * (layerKernelFun μG ρ β (p.2, p.1) * ⇑f p.1))
        ∂((Measure.pi fun _ : LayerLink N => μG).prod
          (Measure.pi fun _ : LayerLink N => μG)) :=
    (integral_prod_swap _).symm
  rw [← inner_conj_symm]
  rw [integralKernelOp_inner, integralKernelOp_inner,
    ← integral_conj, hswap]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  show (starRingEnd ℂ) (star (⇑g p.2)
      * (layerKernelFun μG ρ β (p.2, p.1) * ⇑f p.1))
    = star (⇑f p.1) * (layerKernelFun μG ρ β p * ⇑g p.2)
  rw [map_mul, map_mul, hker p]
  simp only [starRingEnd_apply, star_star]
  ring

/-- **The all-of-`L²` positivity hypothesis** — the item-5
seam, named on the face: the layer-kernel operator is
positive on ALL of `L²(layer)`, in SHELF-3b's `PosKernel`
sense. Strictly stronger than `LayerKernelPos`
(positivity of the pairing on gauge-invariant layer
observables only); proved nowhere in the corpus. -/
def LayerKernelPosAll
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    Prop :=
  PosKernel (layerKernelFun (N := N) μG ρ β)
    (layerKernelFun_memLp (N := N) μG ρ hρcont β)

omit [MeasurableInv G] [IsTopologicalGroup G] [BorelSpace G]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  [μG.IsInvInvariant] in
/-- The bottom extraction is measure-preserving: it factors
as the coordinate split at the image finset of
`embLayerBot hN`, the first projection, and the
pi-congruence along the embedding equivalence — the same
factorization pattern as `measurePreserving_restrictPos`. -/
theorem measurePreserving_tauBot (hN : Even N) :
    MeasurePreserving (tauBot hN)
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
      (Measure.pi fun _ : LayerLink N => μG) := by
  classical
  set s : Finset ↥(posLinks (N := N)) :=
    Finset.image (embLayerBot hN) Finset.univ with hs
  set e : ↥s ≃ LayerLink N :=
    (embEquiv (embLayerBot hN)
      (embLayerBot_injective hN)).symm with he
  have key : ∀ (v : ↥s → G) (ℓ : LayerLink N),
      (MeasurableEquiv.piCongrLeft (fun _ : LayerLink N => G)
        e) v ℓ = v (e.symm ℓ) := by
    intro v ℓ
    have h2 := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : LayerLink N => G) e v (e.symm ℓ)
    rwa [e.apply_symm_apply] at h2
  have hfun : tauBot hN
      = (MeasurableEquiv.piCongrLeft (fun _ : LayerLink N => G)
          e) ∘ (Prod.fst ∘ (splitEquiv s)) := by
    funext z ℓ
    show z (embLayerBot hN ℓ)
      = (MeasurableEquiv.piCongrLeft (fun _ : LayerLink N => G)
          e) ((splitEquiv s z).1) ℓ
    rw [key, splitEquiv_fst]
    show z (embLayerBot hN ℓ) = z ((e.symm ℓ).1)
    have hval : (e.symm ℓ).1 = embLayerBot hN ℓ := rfl
    rw [hval]
  rw [hfun]
  exact (measurePreserving_piCongrLeft
    (fun _ : LayerLink N => μG) e).comp
    (MeasureTheory.measurePreserving_fst.comp
      (measurePreserving_splitEquiv μG s))

omit [MeasurableInv G] [IsTopologicalGroup G] [BorelSpace G]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  [μG.IsInvInvariant] in
/-- The swapped double pullback along `tauBot hN` is
measure-preserving from the product seat measure to the
product layer measure. -/
theorem measurePreserving_swapTauBot (hN : Even N) :
    MeasurePreserving
      (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        (tauBot hN p.2, tauBot hN p.1))
      ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
      ((Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)) := by
  have hfun : (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        (tauBot hN p.2, tauBot hN p.1))
      = Prod.map (tauBot hN) (tauBot hN) ∘ Prod.swap := by
    funext p
    rfl
  rw [hfun]
  exact ((measurePreserving_tauBot μG hN).prod
    (measurePreserving_tauBot μG hN)).comp
    (MeasureTheory.Measure.measurePreserving_swap
      (μ := Measure.pi fun _ : ↥(posLinks (N := N)) => μG)
      (ν := Measure.pi fun _ : ↥(posLinks (N := N)) => μG))

/-- **The stage identity**: one compression stage's seat
difference kernel is the conjugate of the layer difference
kernel pulled back along the swapped `tauBot` map. The
conjugation is the slot bookkeeping of `pullBotKernel`
(it evaluates the layer kernel at the swapped extractions)
composed with the Gram kernel's own conjugation; the layer
kernel's reality removes it on the kernel part. -/
theorem seatDiff_eq (hN : Even N) (β : ℝ)
    {ι : Type*} (b : HilbertBasis ι ℂ
      (Lp ℂ 2 (Measure.pi fun _ : LayerLink N => μG)))
    (F : Finset ι) {m : ℕ} (v : Fin m → (↥F → ℂ))
    (p : (↥(posLinks (N := N)) → G)
      × (↥(posLinks (N := N)) → G)) :
    (starRingEnd ℂ) ((fun q => layerKernelFun μG ρ β q
        - gramKernelOf b F v q)
      (tauBot hN p.2, tauBot hN p.1))
    = pullBotKernel μG ρ hN β p.1 p.2
      - ∑ k, ((1 : ℝ) : ℂ)
        * (⇑(gramFactor b F v k) (tauBot hN p.1)
          * (starRingEnd ℂ)
            (⇑(gramFactor b F v k) (tauBot hN p.2))) := by
  show (starRingEnd ℂ)
      (layerKernel μG ρ β (tauBot hN p.2) (tauBot hN p.1)
        - ∑ k, ⇑(gramFactor b F v k) (tauBot hN p.2)
          * (starRingEnd ℂ)
            (⇑(gramFactor b F v k) (tauBot hN p.1)))
    = pullBotKernel μG ρ hN β p.1 p.2
      - ∑ k, ((1 : ℝ) : ℂ)
        * (⇑(gramFactor b F v k) (tauBot hN p.1)
          * (starRingEnd ℂ)
            (⇑(gramFactor b F v k) (tauBot hN p.2)))
  rw [map_sub, map_sum]
  congr 1
  · show (starRingEnd ℂ)
        (layerKernel μG ρ β (tauBot hN p.2) (tauBot hN p.1))
      = layerKernel μG ρ β (tauBot hN p.2) (tauBot hN p.1)
    rw [layerKernel_eq_ofReal, Complex.conj_ofReal]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, starRingEnd_self_apply, Complex.ofReal_one,
      one_mul, mul_comm]

/-- The stage identity as an equality of kernel functions
on the seat product space: the seat difference kernel is
the conjugate of the pulled-back layer difference kernel. -/
theorem seat_stage_fun_eq (hN : Even N) (β : ℝ)
    {ι : Type*} (b : HilbertBasis ι ℂ
      (Lp ℂ 2 (Measure.pi fun _ : LayerLink N => μG)))
    (F : Finset ι) {m : ℕ} (v : Fin m → (↥F → ℂ)) :
    (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        pullBotKernel μG ρ hN β p.1 p.2
          - ∑ k, ((1 : ℝ) : ℂ)
            * (⇑(gramFactor b F v k) (tauBot hN p.1)
              * (starRingEnd ℂ)
                (⇑(gramFactor b F v k) (tauBot hN p.2))))
    = star ((fun q => layerKernelFun μG ρ β q
          - gramKernelOf b F v q)
        ∘ (fun p : (↥(posLinks (N := N)) → G)
            × (↥(posLinks (N := N)) → G) =>
          (tauBot hN p.2, tauBot hN p.1))) := by
  funext p
  exact (seatDiff_eq μG ρ hN β b F v p).symm

/-- **One stage at the seat is `MemLp 2`**: the layer
stage's `MemLp` transports along the measure-preserving
swapped pullback, and conjugation preserves `MemLp`. -/
theorem seat_stage_memLp
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    {ι : Type*} (b : HilbertBasis ι ℂ
      (Lp ℂ 2 (Measure.pi fun _ : LayerLink N => μG)))
    (F : Finset ι) {m : ℕ} (v : Fin m → (↥F → ℂ)) :
    MemLp (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        pullBotKernel μG ρ hN β p.1 p.2
          - ∑ k, ((1 : ℝ) : ℂ)
            * (⇑(gramFactor b F v k) (tauBot hN p.1)
              * (starRingEnd ℂ)
                (⇑(gramFactor b F v k) (tauBot hN p.2))))
      2 ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG)) := by
  rw [seat_stage_fun_eq μG ρ hN β b F v]
  exact (((layerKernelFun_memLp μG ρ hρcont β).sub
    (gramKernelOf_memLp b F v)).comp_measurePreserving
    (measurePreserving_swapTauBot μG hN)).star

/-- **One stage's HS distance is the same at the seat as
at the layer**: conjugation preserves `eLpNorm`, and the
measure-preserving swapped pullback preserves it. -/
theorem seat_stage_eLpNorm
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    {ι : Type*} (b : HilbertBasis ι ℂ
      (Lp ℂ 2 (Measure.pi fun _ : LayerLink N => μG)))
    (F : Finset ι) {m : ℕ} (v : Fin m → (↥F → ℂ)) :
    (eLpNorm (fun p : (↥(posLinks (N := N)) → G)
          × (↥(posLinks (N := N)) → G) =>
        pullBotKernel μG ρ hN β p.1 p.2
          - ∑ k, ((1 : ℝ) : ℂ)
            * (⇑(gramFactor b F v k) (tauBot hN p.1)
              * (starRingEnd ℂ)
                (⇑(gramFactor b F v k) (tauBot hN p.2))))
      2 ((Measure.pi fun _ : ↥(posLinks (N := N)) => μG).prod
        (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))).toReal
    = (eLpNorm (fun q => layerKernelFun μG ρ β q
          - gramKernelOf b F v q)
        2 ((Measure.pi fun _ : LayerLink N => μG).prod
          (Measure.pi fun _ : LayerLink N => μG))).toReal := by
  have hDiff : MemLp (fun q => layerKernelFun μG ρ β q
        - gramKernelOf b F v q) 2
      ((Measure.pi fun _ : LayerLink N => μG).prod
        (Measure.pi fun _ : LayerLink N => μG)) :=
    (layerKernelFun_memLp μG ρ hρcont β).sub
      (gramKernelOf_memLp b F v)
  rw [seat_stage_fun_eq μG ρ hN β b F v, eLpNorm_star,
    eLpNorm_comp_measurePreserving hDiff.aestronglyMeasurable
      (measurePreserving_swapTauBot μG hN)]

/-- **ITEM 5, conditional headline**: under the
representation-regularity hypothesis and the all-of-`L²`
positivity hypothesis `LayerKernelPosAll`, the frozen
`SeatFactorApproxExpansion` holds — the compression
route's HS convergence, transported from the layer to the
seat along `tauBot hN`. At every `Even N`. This is an
implication whose new hypothesis is a Gram/PSD fact about
`𝒜` itself, proved nowhere; it is NOT a discharge of item
5 as frozen, which assumes only `LayerKernelPos`. -/
theorem seatFactorApproxExpansion_of_layerKernelPosAll
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) {β : ℝ}
    (hAll : LayerKernelPosAll (N := N) μG ρ hρcont β) :
    SeatFactorApproxExpansion μG ρ hN β := by
  obtain ⟨ι, b, -⟩ := exists_hilbertBasis ℂ
    (Lp ℂ 2 (Measure.pi fun _ : LayerLink N => μG))
  obtain ⟨Fseq, mseq, vseq, hlim⟩ := exists_seq_tendsto
    (layerKernelFun_memLp μG ρ hρcont β) b hAll
    (layerKernelFun_selfAdjoint μG ρ hN β
      (layerKernelFun_memLp μG ρ hρcont β))
  refine ⟨fun n => Fin (mseq n), fun n => inferInstance,
    fun _ _ => 1,
    fun n k => ⇑(gramFactor b (Fseq n) (vseq n) k),
    fun n _i => zero_le_one, ?_, ?_⟩
  · intro n
    exact seat_stage_memLp μG ρ hρcont hN β b (Fseq n) (vseq n)
  · exact hlim.congr fun n =>
      (seat_stage_eLpNorm μG ρ hρcont hN β b (Fseq n)
        (vseq n)).symm

/-- The conditional headline on GATE-4C's re-pinned domain
`4 ≤ N` (with `Even N`, as the frozen target requires). -/
theorem seatFactorApproxExpansion_of_layerKernelPosAll_of_four_le
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (_h4 : 4 ≤ N) {β : ℝ}
    (hAll : LayerKernelPosAll (N := N) μG ρ hρcont β) :
    SeatFactorApproxExpansion μG ρ hN β :=
  seatFactorApproxExpansion_of_layerKernelPosAll μG ρ hρcont
    hN hAll

end Seat

end ThetLogos
