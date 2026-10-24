import ThetLogos.LatticeGramWord
import ThetLogos.LatticeLayerFactor

/-!
# Third family, brick F2: assembly of the word family over the seam

**Brick statement.** Assemble F1's single-plaquette word
factorization (`ThetLogos.GramWord.exp_re_hsInner_word`) over the
finitely many crossing plaquettes of the reflection seam into the
hypotheses of the landed integrated Gram criterion
`osForm_nonneg_of_gram_integrated` (`LatticeGramSeries`): the
global index is a choice of one two-factor word index per
crossing plaquette; the features are the products of the
per-plaquette features, folded with the two one-sided half-action
weights (the same `halfActionP` on both sides, by Stage 1b-A's
split). This module proves: the criterion's pointwise Gram
identity `hgram` for the assembled family, the measurability of
both feature families, and the domination package (pointwise
bounds with summable `CA · CB`).

**What this module does NOT prove: the marginals.** The
criterion's two marginal identities (`hmargA`/`hmargB` through a
common strict-half feature `Ξ` with nonnegative real dampings)
are the Damping Lemma of the charter §1.4. They are FALSE for
this family: see the F2 verdict memo
(`routeb-general-scratch/verdict-memo-third-family-f2.md`) for
the exhibited mechanism (pre-registered kills K-F2(b)/(c)).
No `Ξ`, `dA`, `dB` are defined or asserted anywhere in this
module.

**NO CLAIM** — parts of any official Clay statement closed by
this module: **0**. Stage 1b-B positivity: T1 for U(1) at all
β ≥ 0 (Route C); general (G, ρ) **OPEN** — this brick does not
change the label.
-/

open scoped Matrix

noncomputable section GramAssemblyWord

namespace ThetLogos

namespace GramAssemblyWord

open MeasureTheory

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## §1. Reads, arcs, and the assembled features -/

/-- Extension of a closed-half configuration by `1`
(general-group form of Route C's `extHalf`). -/
def extHalfG (y : ↥(halfLinks (N := N)) → G) :
    Config (Fin 4 → ZMod N) G :=
  fun ℓ => if h : ℓ ∈ halfLinks then y ⟨ℓ, h⟩ else 1

/-- Extension of a negative-half configuration by `1`. -/
def extNegG (u : ↥(negLinks (N := N)) → G) :
    Config (Fin 4 → ZMod N) G :=
  fun ℓ => if h : ℓ ∈ negLinks then u ⟨ℓ, h⟩ else 1

theorem extHalfG_apply (y : ↥(halfLinks (N := N)) → G)
    {ℓ : Link (Fin 4 → ZMod N)} (hℓ : ℓ ∈ halfLinks) :
    extHalfG y ℓ = y ⟨ℓ, hℓ⟩ := dif_pos hℓ

theorem extNegG_apply (u : ↥(negLinks (N := N)) → G)
    {ℓ : Link (Fin 4 → ZMod N)} (hℓ : ℓ ∈ negLinks) :
    extNegG u ℓ = u ⟨ℓ, hℓ⟩ := dif_pos hℓ

/-- The **A-side arc** of a crossing plaquette, read on the
closed half: at the lower layer (`(p.1 0).val = N / 2 - 1`) the
arc `A⁻¹ · D · C` through the plaquette's two plane links and
its strict link; at the upper layer the inverse of the
plaquette's single strict link `B`. Together with `arcUg` this
is the unique split of the plaquette holonomy (a cyclic
rotation of `A · B · C⁻¹ · D⁻¹`) into a closed-half part and a
negative-half part: `B` is the lower plaquette's only negative
link and the upper plaquette's only positive link. -/
def arcXg (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4)
    (y : ↥(halfLinks (N := N)) → G) : G :=
  if (p.1 0).val = N / 2 - 1 then
    (extHalfG y (linkA p))⁻¹ * extHalfG y (linkD p)
      * extHalfG y (linkC p)
  else (extHalfG y (linkB p))⁻¹

/-- The **B-side arc** of a crossing plaquette, read on the
negative half: at the lower layer the single link `B`; at the
upper layer the arc `C⁻¹ · D⁻¹ · A`. -/
def arcUg (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4)
    (u : ↥(negLinks (N := N)) → G) : G :=
  if (p.1 0).val = N / 2 - 1 then extNegG u (linkB p)
  else (extNegG u (linkC p))⁻¹ * (extNegG u (linkD p))⁻¹
    * extNegG u (linkA p)

/-- The A-side arc as a representation matrix. -/
def Xmat (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4)
    (y : ↥(halfLinks (N := N)) → G) : Matrix (Fin d) (Fin d) ℂ :=
  repMatrix ρ (arcXg p y)

/-- The B-side arc as a representation matrix. -/
def Umat (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4)
    (u : ↥(negLinks (N := N)) → G) : Matrix (Fin d) (Fin d) ℂ :=
  repMatrix ρ (arcUg p u)

/-- The global word index over the seam: one two-factor word
index per crossing plaquette. -/
def SeamIdx : Type :=
  ↥(zeroFinset (N := N)) → GramWord.WordIdx d

instance : Countable (SeamIdx (d := d) (N := N)) := by
  unfold SeamIdx
  infer_instance

/-- The assembled A-feature: the positive one-sided weight and
the zero-stratum constant, times the product over crossing
plaquettes of F1's A-features at the arc matrices (with the
trivial plane split `P₁ = P₂ = 1`). -/
noncomputable def featGA (β : ℝ) (i : SeamIdx (d := d) (N := N))
    (y : ↥(halfLinks (N := N)) → G) : ℂ :=
  ((Real.exp (- halfActionP ρ β (restrictPos y)) : ℂ)
    * (Real.exp (-β * ((zeroFinset (N := N)).card : ℝ)) : ℂ))
    * ∏ p : ↥(zeroFinset (N := N)),
        GramWord.featA (β / d) (i p) (Xmat ρ p y) 1 1

/-- The assembled B-feature: the negative one-sided weight (the
same `halfActionP`, read through the mirror) times the product
of F1's B-features at the arc matrices. -/
noncomputable def featGB (hN : Even N) (β : ℝ)
    (i : SeamIdx (d := d) (N := N))
    (u : ↥(negLinks (N := N)) → G) : ℂ :=
  (Real.exp (- halfActionP ρ β (mirrorP hN u)) : ℂ)
    * ∏ p : ↥(zeroFinset (N := N)),
        GramWord.featB (i p) (Umat ρ p u)

/-- The assembled A-side domination bound: a constant (the
one-sided weight bound, absorbing the zero-stratum factor)
times the product of F1's per-plaquette `wordCA` bounds. -/
noncomputable def boundCA (β : ℝ) (i : SeamIdx (d := d) (N := N)) :
    ℝ :=
  Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ)
      + ((zeroFinset (N := N)).card : ℝ)))
    * ∏ p : ↥(zeroFinset (N := N)),
        GramWord.wordCA (β / d) 1 (i p)

/-- The assembled B-side domination bound. -/
noncomputable def boundCB (β : ℝ) (i : SeamIdx (d := d) (N := N)) :
    ℝ :=
  Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ)))
    * ∏ p : ↥(zeroFinset (N := N)), GramWord.wordCB 1 (i p)

/-! ## §2. The per-plaquette trace identity -/

/-- One-factor rotation of a four-factor trace. -/
theorem trace_repMatrix_rotate1 (a b c e : G) :
    (repMatrix ρ (a * b * c * e)).trace
      = (repMatrix ρ (e * a * b * c)).trace := by
  have h1 : repMatrix ρ (a * b * c * e)
      = (repMatrix ρ (a * b * c)) * (repMatrix ρ e) :=
    repMatrix_mul ρ _ _
  have h2 : repMatrix ρ (e * a * b * c)
      = (repMatrix ρ e) * (repMatrix ρ (a * b * c)) := by
    rw [show e * a * b * c = e * (a * b * c) from by
      simp only [mul_assoc]]
    exact repMatrix_mul ρ _ _
  rw [h1, h2, Matrix.trace_mul_comm]

/-- Two-factor rotation of a four-factor trace. -/
theorem trace_repMatrix_rotate4 (a b c e : G) :
    (repMatrix ρ (a * b * c * e)).trace
      = (repMatrix ρ (c * e * a * b)).trace :=
  (trace_repMatrix_rotate1 ρ a b c e).trans
    (trace_repMatrix_rotate1 ρ e a b c)

/-- Three-factor rotation of a four-factor trace (the first
factor moves to the end). -/
theorem trace_repMatrix_rotate3 (a b c e : G) :
    (repMatrix ρ (a * b * c * e)).trace
      = (repMatrix ρ (b * c * e * a)).trace :=
  ((trace_repMatrix_rotate1 ρ a b c e).trans
    (trace_repMatrix_rotate1 ρ e a b c)).trans
    (trace_repMatrix_rotate1 ρ c e a b)

/-- The Hilbert–Schmidt pairing of two representation matrices
is a single trace: `⟨ρ x, ρ y⟩_HS = tr ρ(x⁻¹ y)`. -/
theorem hsInner_repMatrix (x y : G) :
    GramWord.hsInner (repMatrix ρ x) (repMatrix ρ y)
      = (repMatrix ρ (x⁻¹ * y)).trace := by
  classical
  rw [GramWord.hsInner_eq_trace, ← Matrix.star_eq_conjTranspose,
    ← repMatrix_inv, ← repMatrix_mul]

/-- The plaquette holonomy in link form. -/
theorem plaquette_eq_links (U : Config (Fin 4 → ZMod N) G)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) :
    plaquette (torusShift N) U p.1 0 p.2.2
      = U (linkA p) * U (linkB p) * (U (linkC p))⁻¹
        * (U (linkD p))⁻¹ := rfl

/-- The unsplit configuration reads a closed-half link through
`y` and a negative-half link through `u`. -/
theorem unsplit_apply_half (y : ↥(halfLinks (N := N)) → G)
    (u : ↥(negLinks (N := N)) → G)
    {ℓ : Link (Fin 4 → ZMod N)} (hℓ : ℓ ∈ halfLinks) :
    (splitEquiv (halfLinks (N := N))).symm (y, u) ℓ
      = y ⟨ℓ, hℓ⟩ :=
  splitEquiv_symm_apply_mem y u hℓ

theorem unsplit_apply_neg (y : ↥(halfLinks (N := N)) → G)
    (u : ↥(negLinks (N := N)) → G)
    {ℓ : Link (Fin 4 → ZMod N)} (hℓ : ℓ ∈ negLinks) :
    (splitEquiv (halfLinks (N := N))).symm (y, u) ℓ
      = u ⟨ℓ, hℓ⟩ :=
  splitEquiv_symm_apply_not_mem y u hℓ

/-- **The arc trace identity.** For a crossing plaquette, the
trace of the plaquette holonomy of the unsplit configuration
is the Hilbert–Schmidt pairing of the two arc matrices:
`tr ρ(U_p) = ⟨X_p, U_p⟩_HS`. The proof is the cyclic rotation
of the holonomy onto the arc split, at both layers. -/
theorem trace_plaquette_eq_hsInner (hN : Even N)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) (hp : p ∈ zeroFinset)
    (y : ↥(halfLinks (N := N)) → G)
    (u : ↥(negLinks (N := N)) → G) :
    (repMatrix ρ (plaquette (torusShift N)
        ((splitEquiv (halfLinks (N := N))).symm (y, u))
        p.1 0 p.2.2)).trace
      = GramWord.hsInner (Xmat ρ p y) (Umat ρ p u) := by
  classical
  rcases zero_link_pattern hN p hp with
    ⟨hval, hAhalf, -, hChalf, -, hDpos, hBneg⟩
    | ⟨hval, hAneg, -, hCneg, -, hBpos, hDneg⟩
  · -- Lower layer: X = ρ(A⁻¹ D C), U = ρ(B).
    have hX : Xmat ρ p y
        = repMatrix ρ ((y ⟨linkA p, hAhalf⟩)⁻¹
            * y ⟨linkD p, posLinks_subset_halfLinks hDpos⟩
            * y ⟨linkC p, hChalf⟩) := by
      unfold Xmat arcXg
      rw [if_pos hval, extHalfG_apply y hAhalf,
        extHalfG_apply y (posLinks_subset_halfLinks hDpos),
        extHalfG_apply y hChalf]
    have hU : Umat ρ p u = repMatrix ρ (u ⟨linkB p, hBneg⟩) := by
      unfold Umat arcUg
      rw [if_pos hval, extNegG_apply u hBneg]
    have hplaq : plaquette (torusShift N)
          ((splitEquiv (halfLinks (N := N))).symm (y, u)) p.1 0 p.2.2
        = y ⟨linkA p, hAhalf⟩ * u ⟨linkB p, hBneg⟩
          * (y ⟨linkC p, hChalf⟩)⁻¹
          * (y ⟨linkD p, posLinks_subset_halfLinks hDpos⟩)⁻¹ := by
      rw [plaquette_eq_links, unsplit_apply_half y u hAhalf,
        unsplit_apply_neg y u hBneg, unsplit_apply_half y u hChalf,
        unsplit_apply_half y u (posLinks_subset_halfLinks hDpos)]
    rw [hplaq]
    calc (repMatrix ρ (y ⟨linkA p, hAhalf⟩ * u ⟨linkB p, hBneg⟩
            * (y ⟨linkC p, hChalf⟩)⁻¹
            * (y ⟨linkD p,
                posLinks_subset_halfLinks hDpos⟩)⁻¹)).trace
        = (repMatrix ρ ((y ⟨linkC p, hChalf⟩)⁻¹
            * (y ⟨linkD p,
                posLinks_subset_halfLinks hDpos⟩)⁻¹
            * y ⟨linkA p, hAhalf⟩
            * u ⟨linkB p, hBneg⟩)).trace :=
      (trace_repMatrix_rotate4 ρ _ _ _ _).symm
      _ = GramWord.hsInner (Xmat ρ p y) (Umat ρ p u) := by
          rw [hX, hU, hsInner_repMatrix]
          congr 1
          group
  · -- Upper layer: X = ρ(B⁻¹), U = ρ(C⁻¹ D⁻¹ A).
    have hne : ¬ (p.1 0).val = N / 2 - 1 := by
      obtain ⟨r, hr⟩ := hN
      have hN0 : N ≠ 0 := NeZero.ne N
      omega
    have hX : Xmat ρ p y
        = repMatrix ρ ((y ⟨linkB p,
            posLinks_subset_halfLinks hBpos⟩)⁻¹) := by
      unfold Xmat arcXg
      rw [if_neg hne, extHalfG_apply y
        (posLinks_subset_halfLinks hBpos)]
    have hU : Umat ρ p u
        = repMatrix ρ ((u ⟨linkC p, hCneg⟩)⁻¹
            * (u ⟨linkD p, hDneg⟩)⁻¹ * u ⟨linkA p, hAneg⟩) := by
      unfold Umat arcUg
      rw [if_neg hne, extNegG_apply u hAneg,
        extNegG_apply u hCneg, extNegG_apply u hDneg]
    have hplaq : plaquette (torusShift N)
          ((splitEquiv (halfLinks (N := N))).symm (y, u)) p.1 0 p.2.2
        = u ⟨linkA p, hAneg⟩
          * y ⟨linkB p, posLinks_subset_halfLinks hBpos⟩
          * (u ⟨linkC p, hCneg⟩)⁻¹ * (u ⟨linkD p, hDneg⟩)⁻¹ := by
      rw [plaquette_eq_links, unsplit_apply_neg y u hAneg,
        unsplit_apply_half y u (posLinks_subset_halfLinks hBpos),
        unsplit_apply_neg y u hCneg, unsplit_apply_neg y u hDneg]
    rw [hplaq]
    calc (repMatrix ρ (u ⟨linkA p, hAneg⟩
            * y ⟨linkB p, posLinks_subset_halfLinks hBpos⟩
            * (u ⟨linkC p, hCneg⟩)⁻¹
            * (u ⟨linkD p, hDneg⟩)⁻¹)).trace
        = (repMatrix ρ ((y ⟨linkB p,
                posLinks_subset_halfLinks hBpos⟩)
            * (u ⟨linkC p, hCneg⟩)⁻¹
            * (u ⟨linkD p, hDneg⟩)⁻¹
            * u ⟨linkA p, hAneg⟩)).trace :=
      trace_repMatrix_rotate3 ρ _ _ _ _
      _ = GramWord.hsInner (Xmat ρ p y) (Umat ρ p u) := by
          rw [hX, hU, hsInner_repMatrix]
          congr 1
          group

/-! ## §3. Finite products of summable families over a pi type -/

/-- Norm of a finite product is at most the product of the
norms. -/
theorem norm_prod_le_prod {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {ι : Type*} (s : Finset ι) (f : ι → 𝕜) :
    ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.prod_insert has, Finset.prod_insert has, norm_mul]
      exact mul_le_mul (le_refl _) ih (norm_nonneg _)
        (norm_nonneg _)

/-- Monotonicity of finite products of nonnegative reals. -/
theorem prod_le_prod_nonneg {ι : Type*} (s : Finset ι)
    (f g : ι → ℝ) :
    (∀ i ∈ s, 0 ≤ f i) → (∀ i ∈ s, f i ≤ g i) →
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction with
  | empty => intro _ _; simp
  | insert a s has ih =>
      intro h0 h1
      rw [Finset.prod_insert has, Finset.prod_insert has]
      exact mul_le_mul (h1 a (Finset.mem_insert_self a s))
        (ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
          (fun i hi => h1 i (Finset.mem_insert_of_mem hi)))
        (Finset.prod_nonneg fun i hi =>
          h0 i (Finset.mem_insert_of_mem hi))
        (le_trans (h0 a (Finset.mem_insert_self a s))
          (h1 a (Finset.mem_insert_self a s)))

/-- Sums over a pi rectangle are products of sums (any
normed field; used inside `hasSum_pi_prod` at both `ℂ` and
`ℝ`). -/
theorem sum_piFinset_prod {ι W 𝕜' : Type*} [Fintype ι]
    [DecidableEq ι] [NontriviallyNormedField 𝕜']
    (S : Finset W) (F' : ι → W → 𝕜') :
    (∑ x ∈ Fintype.piFinset (fun _ : ι => S), ∏ i, F' i (x i))
      = ∏ i, ∑ w ∈ S, F' i w :=
  (Finset.prod_univ_sum (fun _ : ι => S) fun i w => F' i w).symm

/-- **Finite products of summable families over a pi type**
(the rectangle lemma). If each `F i` is dominated by a
summable nonnegative family `C i`, then the product family
over the pi type sums to the product of the sums. Proof:
diagonal rectangles `piFinset (fun _ => S)` are cofinal among
finsets of the pi type, partial sums over rectangles factor
(`Finset.prod_univ_sum`), and the norm tails are dominated by
the tails of the dominating product family, whose rectangle
sums exhaust it. -/
theorem hasSum_pi_prod {ι : Type*} [Fintype ι] {W : Type*}
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (hW : Nonempty W)
    (F : ι → W → 𝕜) (C : ι → W → ℝ)
    (hC : ∀ i w, 0 ≤ C i w) (hF : ∀ i w, ‖F i w‖ ≤ C i w)
    (hCs : ∀ i, Summable (C i)) :
    HasSum (fun x : ι → W => ∏ i, F i (x i))
      (∏ i, ∑' w, F i w) := by
  classical
  haveI := hW
  -- The dominating product family is summable (rectangle bound
  -- on every finite partial sum).
  have hBnn : ∀ x : ι → W, 0 ≤ ∏ i, C i (x i) := fun x =>
    Finset.prod_nonneg fun i _ => hC i (x i)
  have hBsum : Summable fun x : ι → W => ∏ i, C i (x i) := by
    refine summable_of_sum_le (c := ∏ i, ∑' w, C i w) hBnn ?_
    intro s
    let t : ι → Finset W := fun i => s.image (fun x => x i)
    have hsub : s ⊆ Fintype.piFinset t := by
      intro x hx
      rw [Fintype.mem_piFinset]
      exact fun i => Finset.mem_image.2 ⟨x, hx, rfl⟩
    calc ∑ x ∈ s, ∏ i, C i (x i)
        ≤ ∑ x ∈ Fintype.piFinset t, ∏ i, C i (x i) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            fun x _ _ => hBnn x
      _ = ∏ i, ∑ w ∈ t i, C i w :=
          (Finset.prod_univ_sum t fun i w => C i w).symm
      _ ≤ ∏ i, ∑' w, C i w :=
          prod_le_prod_nonneg Finset.univ _ _
            (fun i _ => Finset.sum_nonneg fun w _ => hC i w)
            (fun i _ => (hCs i).sum_le_tsum (t i)
              (fun w _ => hC i w))
  have hFs : ∀ i, Summable (F i) := fun i =>
    (hCs i).of_norm_bounded fun w => hF i w
  -- Summability of the product family, by domination.
  have hgB : ∀ x : ι → W, ‖∏ i, F i (x i)‖ ≤ ∏ i, C i (x i) :=
    fun x =>
      (norm_prod_le_prod Finset.univ fun i => F i (x i)).trans
        (prod_le_prod_nonneg Finset.univ _ _
          (fun i _ => norm_nonneg _)
          (fun i _ => hF i (x i)))
  have hgsum : Summable fun x : ι → W => ∏ i, F i (x i) :=
    hBsum.of_norm_bounded hgB
  -- Rectangle partial sums factor.
  have hrect : ∀ (S : Finset W) (F' : ι → W → 𝕜),
      ∑ x ∈ Fintype.piFinset (fun _ : ι => S), ∏ i, F' i (x i)
        = ∏ i, ∑ w ∈ S, F' i w := fun S F' =>
    sum_piFinset_prod S F'
  -- Diagonal rectangles are cofinal.
  have hRtendsto : Filter.Tendsto
      (fun S : Finset W => Fintype.piFinset (fun _ : ι => S))
      Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro s
    refine ⟨s.biUnion fun x => Finset.univ.image (fun i => x i),
      fun S hS x hx => ?_⟩
    rw [Fintype.mem_piFinset]
    intro i
    exact (Finset.le_iff_subset.1 hS) (Finset.mem_biUnion.2 ⟨x, hx,
      Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩⟩)
  -- Rectangle sums of the dominating family, and its total.
  have hBrect : Filter.Tendsto
      (fun S : Finset W => ∑ x ∈ Fintype.piFinset (fun _ : ι => S),
        ∏ i, C i (x i))
      Filter.atTop (nhds (∏ i, ∑' w, C i w)) := by
    refine Filter.Tendsto.congr
      (fun S => (sum_piFinset_prod S C).symm) ?_
    exact tendsto_finsetProd Finset.univ fun i _ => (hCs i).hasSum
  have hBval : (∑' x : ι → W, ∏ i, C i (x i))
      = ∏ i, ∑' w, C i w :=
    tendsto_nhds_unique (Filter.Tendsto.comp hBsum.hasSum hRtendsto)
      hBrect
  have hBtail : Filter.Tendsto
      (fun S : Finset W => (∑' x : ι → W, ∏ i, C i (x i))
        - ∑ x ∈ Fintype.piFinset (fun _ : ι => S), ∏ i, C i (x i))
      Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto
        (fun S : Finset W => (∏ i, ∑' w, C i w)
          - ∑ x ∈ Fintype.piFinset (fun _ : ι => S), ∏ i, C i (x i))
        Filter.atTop (nhds ((∏ i, ∑' w, C i w)
          - (∏ i, ∑' w, C i w))) :=
      tendsto_const_nhds.sub hBrect
    rw [sub_self, ← hBval] at h
    exact h
  have hFrect : Filter.Tendsto
      (fun S : Finset W => ∑ x ∈ Fintype.piFinset (fun _ : ι => S),
        ∏ i, F i (x i))
      Filter.atTop (nhds (∏ i, ∑' w, F i w)) := by
    refine Filter.Tendsto.congr (fun S => (hrect S F).symm) ?_
    exact tendsto_finsetProd Finset.univ fun i _ => (hFs i).hasSum
  -- The squeeze: partial sums over any finset above a large
  -- rectangle are close to the product of the sums.
  have hT : Filter.Tendsto
      (fun s : Finset (ι → W) => ∑ x ∈ s, ∏ i, F i (x i))
      Filter.atTop (nhds (∏ i, ∑' w, F i w)) := by
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    obtain ⟨S₁, hS₁⟩ := Metric.tendsto_atTop.1 hFrect (ε / 2)
      (by positivity)
    obtain ⟨S₂, hS₂⟩ := Metric.tendsto_atTop.1 hBtail (ε / 2)
      (by positivity)
    refine ⟨Fintype.piFinset (fun _ : ι => S₁ ∪ S₂), fun s hs => ?_⟩
    have hdist₂ : dist
          (∑ x ∈ Fintype.piFinset (fun _ : ι => S₁ ∪ S₂),
            ∏ i, F i (x i))
          (∏ i, ∑' w, F i w) < ε / 2 :=
      hS₁ (S₁ ∪ S₂) Finset.subset_union_left
    have hdist₁ : dist (∑ x ∈ s, ∏ i, F i (x i))
          (∑ x ∈ Fintype.piFinset (fun _ : ι => S₁ ∪ S₂),
            ∏ i, F i (x i)) < ε / 2 := by
      have hsub : (∑ x ∈ s, ∏ i, F i (x i))
          - ∑ x ∈ Fintype.piFinset (fun _ : ι => S₁ ∪ S₂),
              ∏ i, F i (x i)
        = ∑ x ∈ s \ Fintype.piFinset (fun _ : ι => S₁ ∪ S₂),
            ∏ i, F i (x i) := by
        rw [sub_eq_iff_eq_add', add_comm]
        exact (Finset.sum_sdiff hs).symm
      rw [dist_eq_norm, hsub]
      refine ((norm_sum_le _ _).trans
        (Finset.sum_le_sum fun x _ => hgB x)).trans_lt ?_
      have hsd : ∑ x ∈ s \ Fintype.piFinset (fun _ : ι => S₁ ∪ S₂),
            ∏ i, C i (x i)
          = (∑ x ∈ s, ∏ i, C i (x i))
            - ∑ x ∈ Fintype.piFinset (fun _ : ι => S₁ ∪ S₂),
                ∏ i, C i (x i) :=
        Finset.sum_sdiff_eq_sub hs
      rw [hsd]
      refine (sub_le_sub_right
        (hBsum.sum_le_tsum s (fun x _ => hBnn x)) _).trans_lt ?_
      have hS₂' := hS₂ (S₁ ∪ S₂) Finset.subset_union_right
      rwa [dist_eq_norm, sub_zero, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.2
          (hBsum.sum_le_tsum _ (fun x _ => hBnn x)))] at hS₂'
    have hfin := (dist_triangle (∑ x ∈ s, ∏ i, F i (x i))
      (∑ x ∈ Fintype.piFinset (fun _ : ι => S₁ ∪ S₂), ∏ i, F i (x i))
      (∏ i, ∑' w, F i w)).trans_lt (add_lt_add hdist₁ hdist₂)
    rwa [add_halves] at hfin
  exact hT

/-! ## §4. The assembled Gram identity -/

/-- Entries of the identity matrix are bounded by `1`. -/
theorem norm_one_entry (i j : Fin d) :
    ‖(1 : Matrix (Fin d) (Fin d) ℂ) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]
  split <;> simp

/-- Entries of a unitary representation matrix have norm
`≤ 1` (a row of `M * star M` is a unit vector). The proof is
the corpus's (`GramAssembly.repMatrix_entry_norm_le_one`),
restated here because that module's ambient carries a
compactness hypothesis this brick's ambient does not. -/
theorem norm_repMatrix_entry_le_one (g : G) (a b : Fin d) :
    ‖repMatrix ρ g a b‖ ≤ 1 := by
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

/-- The `K = 1` entry bound for the A-side arc matrix. -/
theorem norm_Xmat_entry (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4)
    (y : ↥(halfLinks (N := N)) → G) (i j : Fin d) :
    ‖Xmat ρ p y i j‖ ≤ 1 :=
  norm_repMatrix_entry_le_one ρ _ _ _

/-- The `K = 1` entry bound for the B-side arc matrix. -/
theorem norm_Umat_entry (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4)
    (u : ↥(negLinks (N := N)) → G) (i j : Fin d) :
    ‖Umat ρ p u i j‖ ≤ 1 :=
  norm_repMatrix_entry_le_one ρ _ _ _

/-- The per-plaquette word family on the seam: F1's integrand
at the arc matrices, with the trivial plane split. -/
def plaqFam (β : ℝ) (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4)
    (y : ↥(halfLinks (N := N)) → G) (u : ↥(negLinks (N := N)) → G) :
    GramWord.WordIdx d → ℂ :=
  fun w => star (GramWord.featB w (Umat ρ p u))
    * GramWord.featA (β / d) w (Xmat ρ p y) 1 1

/-- The per-plaquette domination bound, from F1's package. -/
theorem norm_plaqFam_le (β : ℝ)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4)
    (y : ↥(halfLinks (N := N)) → G) (u : ↥(negLinks (N := N)) → G)
    (w : GramWord.WordIdx d) :
    ‖plaqFam ρ β p y u w‖
      ≤ GramWord.wordCA (β / d) 1 w * GramWord.wordCB 1 w := by
  unfold plaqFam
  rw [norm_mul]
  refine (mul_le_mul
    (GramWord.norm_featB_le 1 (by norm_num) (Umat ρ p u)
      (fun i j => norm_Umat_entry ρ p u i j) w)
    (GramWord.norm_featA_le (β / d) 1 (by norm_num) (Xmat ρ p y) 1 1
      (fun i j => norm_Xmat_entry ρ p y i j)
      (fun i j => norm_one_entry i j)
      (fun i j => norm_one_entry i j) w)
    (norm_nonneg _)
    (le_trans (norm_nonneg _) (GramWord.norm_featB_le 1 (by norm_num)
      (Umat ρ p u) (fun i j => norm_Umat_entry ρ p u i j) w))).trans_eq
    (mul_comm _ _)

/-- **The per-plaquette exponential factor.** One crossing
plaquette's Gibbs factor is `exp (-β)` times the sum of its
word family: F1's factorization at the arc matrices, with the
trace identity of §2 turning the Hilbert–Schmidt pairing into
the plaquette holonomy trace inside `plaquetteDensity`. -/
theorem plaq_factor (hN : Even N) (hd : 0 < d) (β : ℝ)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) (hp : p ∈ zeroFinset)
    (y : ↥(halfLinks (N := N)) → G) (u : ↥(negLinks (N := N)) → G) :
    ((Real.exp (-β * plaquetteDensity (torusShift N) ρ
        ((splitEquiv (halfLinks (N := N))).symm (y, u))
        p.1 p.2.1 p.2.2) : ℝ) : ℂ)
      = ((Real.exp (-β) : ℝ) : ℂ) * (∑' w, plaqFam ρ β p y u w) := by
  classical
  obtain ⟨hpI, hz⟩ := Finset.mem_filter.mp hp
  have hμ : p.2.1 = 0 := ((isZeroPlaq_iff hN p hpI).mp hz).1
  have hF1 := GramWord.exp_re_hsInner_word (β / d) 1 (by norm_num)
    (Xmat ρ p y) 1 1 (Umat ρ p u)
    (fun i j => norm_Xmat_entry ρ p y i j)
    (fun i j => norm_one_entry i j)
    (fun i j => norm_one_entry i j)
    (fun i j => norm_Umat_entry ρ p u i j)
  rw [one_mul, mul_one,
    ← trace_plaquette_eq_hsInner ρ hN p hp y u] at hF1
  unfold plaquetteDensity
  rw [hμ]
  show ((Real.exp (-β * (1 - (repMatrix ρ (plaquette (torusShift N)
        ((splitEquiv (halfLinks (N := N))).symm (y, u))
        p.1 0 p.2.2)).trace.re / (d : ℝ))) : ℝ) : ℂ)
      = ((Real.exp (-β) : ℝ) : ℂ)
        * (∑' w, star (GramWord.featB w (Umat ρ p u))
            * GramWord.featA (β / d) w (Xmat ρ p y) 1 1)
  calc ((Real.exp (-β * (1 - (repMatrix ρ (plaquette (torusShift N)
          ((splitEquiv (halfLinks (N := N))).symm (y, u))
          p.1 0 p.2.2)).trace.re / (d : ℝ))) : ℝ) : ℂ)
      = ((Real.exp (-β) : ℝ) : ℂ)
          * ((Real.exp ((β / d) * (repMatrix ρ (plaquette (torusShift N)
              ((splitEquiv (halfLinks (N := N))).symm (y, u))
              p.1 0 p.2.2)).trace.re) : ℝ) : ℂ) := by
        rw [show (-β * (1 - (repMatrix ρ (plaquette (torusShift N)
              ((splitEquiv (halfLinks (N := N))).symm (y, u))
              p.1 0 p.2.2)).trace.re / (d : ℝ)) : ℝ)
            = -β + (β / d) * (repMatrix ρ (plaquette (torusShift N)
              ((splitEquiv (halfLinks (N := N))).symm (y, u))
              p.1 0 p.2.2)).trace.re from by
          have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
          field_simp
          ring, Real.exp_add, Complex.ofReal_mul]
    _ = ((Real.exp (-β) : ℝ) : ℂ)
          * Complex.exp (((β / d : ℝ) : ℂ)
            * ((repMatrix ρ (plaquette (torusShift N)
              ((splitEquiv (halfLinks (N := N))).symm (y, u))
              p.1 0 p.2.2)).trace.re : ℂ)) := by
        congr 1
        rw [Complex.ofReal_exp, ← Complex.ofReal_mul]
    _ = ((Real.exp (-β) : ℝ) : ℂ)
          * (∑' w, star (GramWord.featB w (Umat ρ p u))
              * GramWord.featA (β / d) w (Xmat ρ p y) 1 1) := by
        rw [← hF1]

/-- The criterion's conjugation of the assembled B-feature:
the real one-sided weight is self-conjugate and `star`
distributes over the plaquette product. -/
theorem starRingEnd_featGB (hN : Even N) (β : ℝ)
    (i : SeamIdx (N := N)) (u : ↥(negLinks (N := N)) → G) :
    (starRingEnd ℂ) (featGB ρ hN β i u)
      = ((Real.exp (- halfActionP ρ β (mirrorP hN u)) : ℂ))
        * ∏ p : ↥(zeroFinset (N := N)),
            star (GramWord.featB (i p) (Umat ρ p u)) := by
  unfold featGB
  rw [map_mul, map_prod]
  congr 1
  rw [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]

/-- One global index's integrand, rearranged: the scalar
weights factor out of the plaquette product. -/
theorem integrand_factor (hN : Even N) (β : ℝ)
    (i : SeamIdx (N := N))
    (y : ↥(halfLinks (N := N)) → G) (u : ↥(negLinks (N := N)) → G) :
    (starRingEnd ℂ) (featGB ρ hN β i u) * featGA ρ β i y
      = (((Real.exp (- halfActionP ρ β (restrictPos y)) : ℂ)
          * (Real.exp (- halfActionP ρ β (mirrorP hN u)) : ℂ)
          * (Real.exp (-β * ((zeroFinset (N := N)).card : ℝ)) : ℂ)))
        * ∏ p : ↥(zeroFinset (N := N)), plaqFam ρ β p.1 y u (i p) := by
  have hprod : (∏ p : ↥(zeroFinset (N := N)),
        star (GramWord.featB (i p) (Umat ρ p u)))
      * (∏ p : ↥(zeroFinset (N := N)),
          GramWord.featA (β / d) (i p) (Xmat ρ p y) 1 1)
    = ∏ p : ↥(zeroFinset (N := N)), plaqFam ρ β p.1 y u (i p) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => rfl
  rw [starRingEnd_featGB ρ hN β i u]
  unfold featGA
  calc ((Real.exp (- halfActionP ρ β (mirrorP hN u)) : ℂ)
        * ∏ p : ↥(zeroFinset (N := N)),
            star (GramWord.featB (i p) (Umat ρ p u)))
      * (((Real.exp (- halfActionP ρ β (restrictPos y)) : ℂ)
          * (Real.exp (-β * ((zeroFinset (N := N)).card : ℝ)) : ℂ))
        * ∏ p : ↥(zeroFinset (N := N)),
            GramWord.featA (β / d) (i p) (Xmat ρ p y) 1 1)
      = (((Real.exp (- halfActionP ρ β (restrictPos y)) : ℂ)
          * (Real.exp (- halfActionP ρ β (mirrorP hN u)) : ℂ)
          * (Real.exp (-β * ((zeroFinset (N := N)).card : ℝ)) : ℂ)))
        * ((∏ p : ↥(zeroFinset (N := N)),
              star (GramWord.featB (i p) (Umat ρ p u)))
          * ∏ p : ↥(zeroFinset (N := N)),
              GramWord.featA (β / d) (i p) (Xmat ρ p y) 1 1) := by
        ring
    _ = (((Real.exp (- halfActionP ρ β (restrictPos y)) : ℂ)
          * (Real.exp (- halfActionP ρ β (mirrorP hN u)) : ℂ)
          * (Real.exp (-β * ((zeroFinset (N := N)).card : ℝ)) : ℂ)))
        * ∏ p : ↥(zeroFinset (N := N)), plaqFam ρ β p.1 y u (i p) := by
        rw [hprod]

/-- **The assembled Gram identity** (the criterion's `hgram`
for the seam family). The Gibbs weight of the unsplit
configuration is the sum over global word indices of
`conj (B-feature) · (A-feature)`. -/
theorem assembly_hgram (hN : Even N) (hd : 0 < d) (β : ℝ)
    (y : ↥(halfLinks (N := N)) → G) (u : ↥(negLinks (N := N)) → G) :
    ((Real.exp (- wilsonAction (torusShift N) ρ β
        ((splitEquiv (halfLinks (N := N))).symm (y, u))) : ℝ) : ℂ)
      = ∑' i : SeamIdx (N := N), (starRingEnd ℂ) (featGB ρ hN β i u)
          * featGA ρ β i y := by
  classical
  -- The zero-stratum factor as a product of per-plaquette sums.
  have hzero : ((Real.exp (- wilsonActionZero ρ β
        ((splitEquiv (halfLinks (N := N))).symm (y, u))) : ℝ) : ℂ)
      = ((Real.exp (-β * ((zeroFinset (N := N)).card : ℝ)) : ℂ))
        * ∏ p : ↥(zeroFinset (N := N)),
            (∑' w, plaqFam ρ β p.1 y u w) := by
    have hzeroR : Real.exp (- wilsonActionZero ρ β
          ((splitEquiv (halfLinks (N := N))).symm (y, u)))
        = ∏ p ∈ zeroFinset (N := N),
            Real.exp (-β * plaquetteDensity (torusShift N) ρ
              ((splitEquiv (halfLinks (N := N))).symm (y, u))
              p.1 p.2.1 p.2.2) := by
      unfold wilsonActionZero
      rw [show (-(β * ∑ p ∈ plaqIndex.filter IsZeroPlaq,
            plaquetteDensity (torusShift N) ρ
              ((splitEquiv (halfLinks (N := N))).symm (y, u))
              p.1 p.2.1 p.2.2) : ℝ)
          = ∑ p ∈ plaqIndex.filter IsZeroPlaq,
            (-β * plaquetteDensity (torusShift N) ρ
              ((splitEquiv (halfLinks (N := N))).symm (y, u))
              p.1 p.2.1 p.2.2) from by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun p _ => by ring]
      rw [Real.exp_sum, zeroFinset_eq]
    have h1 : ((Real.exp (- wilsonActionZero ρ β
          ((splitEquiv (halfLinks (N := N))).symm (y, u))) : ℝ) : ℂ)
        = ∏ p ∈ zeroFinset (N := N),
            ((Real.exp (-β * plaquetteDensity (torusShift N) ρ
              ((splitEquiv (halfLinks (N := N))).symm (y, u))
              p.1 p.2.1 p.2.2) : ℝ) : ℂ) := by
      rw [hzeroR, Complex.ofReal_prod]
    rw [h1]
    refine Eq.trans (Finset.prod_congr rfl fun p hp =>
      plaq_factor ρ hN hd β p hp y u) ?_
    rw [Finset.prod_mul_distrib]
    congr 1
    · -- ∏ p ∈ zeroFinset, (exp (-β) : ℂ) = (exp (-β * card) : ℂ)
      rw [Finset.prod_const, ← Complex.ofReal_pow,
        ← Real.exp_nat_mul, mul_comm _ (-β)]
    · exact (Finset.prod_coe_sort (zeroFinset (N := N))
        fun p => ∑' w, plaqFam ρ β p y u w).symm
  -- The summed side, factored.
  have hW : Nonempty (GramWord.WordIdx d) :=
    ⟨(⟨0, fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩,
      ⟨0, fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩)⟩
  have hRHS : (∑' i : SeamIdx (N := N),
        (starRingEnd ℂ) (featGB ρ hN β i u) * featGA ρ β i y)
      = (((Real.exp (- halfActionP ρ β (restrictPos y)) : ℂ)
          * (Real.exp (- halfActionP ρ β (mirrorP hN u)) : ℂ)
          * (Real.exp (-β * ((zeroFinset (N := N)).card : ℝ)) : ℂ)))
        * ∏ p : ↥(zeroFinset (N := N)),
            (∑' w, plaqFam ρ β p.1 y u w) := by
    have hCnn : ∀ p : ↥(zeroFinset (N := N)),
        ∀ w : GramWord.WordIdx d,
        0 ≤ GramWord.wordCA (β / d) 1 w
          * GramWord.wordCB 1 w :=
      fun p w => mul_nonneg
        (by simp only [GramWord.wordCA]; positivity)
        (by simp only [GramWord.wordCB]; positivity)
    have hprod : (∑' i : SeamIdx (N := N),
          ∏ p : ↥(zeroFinset (N := N)), plaqFam ρ β p.1 y u (i p))
        = ∏ p : ↥(zeroFinset (N := N)),
            (∑' w, plaqFam ρ β p.1 y u w) :=
      (hasSum_pi_prod (ι := ↥(zeroFinset (N := N))) hW
        (fun p w => plaqFam ρ β p.1 y u w)
        (fun p w => GramWord.wordCA (β / d) 1 w
          * GramWord.wordCB 1 w)
        hCnn
        (fun p w => norm_plaqFam_le ρ β p.1 y u w)
        (fun _ => GramWord.summable_wordCA_mul (β / d) 1
          (by norm_num))).tsum_eq
    rw [tsum_congr (fun i => integrand_factor ρ hN β i y u),
      tsum_mul_left, hprod]
  -- The Gibbs side, split.
  have hsplit : wilsonAction (torusShift N) ρ β
        ((splitEquiv (halfLinks (N := N))).symm (y, u))
      = halfActionP ρ β (restrictPos y)
        + halfActionP ρ β (mirrorP hN u)
        + wilsonActionZero ρ β
            ((splitEquiv (halfLinks (N := N))).symm (y, u)) :=
    wilsonAction_split_half ρ hN β (y, u)
  rw [hsplit]
  rw [show (-(halfActionP ρ β (restrictPos y)
        + halfActionP ρ β (mirrorP hN u)
        + wilsonActionZero ρ β
          ((splitEquiv (halfLinks (N := N))).symm (y, u))) : ℝ)
      = (- halfActionP ρ β (restrictPos y))
        + (- halfActionP ρ β (mirrorP hN u))
        + (- wilsonActionZero ρ β
            ((splitEquiv (halfLinks (N := N))).symm (y, u))) by ring,
    Real.exp_add, Real.exp_add, Complex.ofReal_mul,
    Complex.ofReal_mul, hzero, hRHS]
  ring

/-! ## §5. Measurability of the features -/

/-- Evaluation of the closed-half extension is continuous. -/
theorem continuous_extHalfG_apply (ℓ : Link (Fin 4 → ZMod N)) :
    Continuous fun y : ↥(halfLinks (N := N)) → G =>
      extHalfG y ℓ := by
  by_cases hℓ : ℓ ∈ halfLinks (N := N)
  · have e : (fun y : ↥(halfLinks (N := N)) → G => extHalfG y ℓ)
        = fun y => y ⟨ℓ, hℓ⟩ :=
      funext fun y => extHalfG_apply y hℓ
    rw [e]; exact continuous_apply _
  · have e : (fun y : ↥(halfLinks (N := N)) → G => extHalfG y ℓ)
        = fun _ => (1 : G) := by
      funext y
      show (if h : ℓ ∈ halfLinks (N := N) then y ⟨ℓ, h⟩ else 1) = 1
      exact dif_neg hℓ
    rw [e]; exact continuous_const

/-- Evaluation of the negative-half extension is continuous. -/
theorem continuous_extNegG_apply (ℓ : Link (Fin 4 → ZMod N)) :
    Continuous fun u : ↥(negLinks (N := N)) → G =>
      extNegG u ℓ := by
  by_cases hℓ : ℓ ∈ negLinks (N := N)
  · have e : (fun u : ↥(negLinks (N := N)) → G => extNegG u ℓ)
        = fun u => u ⟨ℓ, hℓ⟩ :=
      funext fun u => extNegG_apply u hℓ
    rw [e]; exact continuous_apply _
  · have e : (fun u : ↥(negLinks (N := N)) → G => extNegG u ℓ)
        = fun _ => (1 : G) := by
      funext u
      show (if h : ℓ ∈ negLinks (N := N) then u ⟨ℓ, h⟩ else 1) = 1
      exact dif_neg hℓ
    rw [e]; exact continuous_const

/-- The A-side arc is continuous in the closed-half
configuration. -/
theorem continuous_arcXg (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) :
    Continuous fun y : ↥(halfLinks (N := N)) → G =>
      arcXg p y := by
  by_cases h : (p.1 0).val = N / 2 - 1
  · have e : (fun y : ↥(halfLinks (N := N)) → G => arcXg p y)
        = fun y => (extHalfG y (linkA p))⁻¹ * extHalfG y (linkD p)
            * extHalfG y (linkC p) := by
      funext y
      unfold arcXg
      rw [if_pos h]
    rw [e]
    exact ((continuous_extHalfG_apply _).inv.mul
      (continuous_extHalfG_apply _)).mul
      (continuous_extHalfG_apply _)
  · have e : (fun y : ↥(halfLinks (N := N)) → G => arcXg p y)
        = fun y => (extHalfG y (linkB p))⁻¹ := by
      funext y
      unfold arcXg
      rw [if_neg h]
    rw [e]
    exact (continuous_extHalfG_apply _).inv

/-- The B-side arc is continuous in the negative-half
configuration. -/
theorem continuous_arcUg (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) :
    Continuous fun u : ↥(negLinks (N := N)) → G =>
      arcUg p u := by
  by_cases h : (p.1 0).val = N / 2 - 1
  · have e : (fun u : ↥(negLinks (N := N)) → G => arcUg p u)
        = fun u => extNegG u (linkB p) := by
      funext u
      unfold arcUg
      rw [if_pos h]
    rw [e]
    exact continuous_extNegG_apply _
  · have e : (fun u : ↥(negLinks (N := N)) → G => arcUg p u)
        = fun u => (extNegG u (linkC p))⁻¹
            * (extNegG u (linkD p))⁻¹ * extNegG u (linkA p) := by
      funext u
      unfold arcUg
      rw [if_neg h]
    rw [e]
    exact ((continuous_extNegG_apply _).inv.mul
      (continuous_extNegG_apply _).inv).mul
      (continuous_extNegG_apply _)

/-- Entries of the A-side arc matrix are continuous. -/
theorem continuous_Xmat_apply
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) (i j : Fin d) :
    Continuous fun y : ↥(halfLinks (N := N)) → G =>
      Xmat ρ p y i j :=
  (continuous_apply j).comp
    ((continuous_apply i).comp (hρcont.comp (continuous_arcXg p)))

/-- Entries of the B-side arc matrix are continuous. -/
theorem continuous_Umat_apply
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) (i j : Fin d) :
    Continuous fun u : ↥(negLinks (N := N)) → G =>
      Umat ρ p u i j :=
  (continuous_apply j).comp
    ((continuous_apply i).comp (hρcont.comp (continuous_arcUg p)))

/-- The A-side arc matrix is continuous. -/
theorem continuous_Xmat
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) :
    Continuous fun y : ↥(halfLinks (N := N)) → G =>
      Xmat ρ p y :=
  continuous_pi fun i => continuous_pi fun j =>
    continuous_Xmat_apply ρ hρcont p i j

/-- The B-side arc matrix is continuous. -/
theorem continuous_Umat
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) :
    Continuous fun u : ↥(negLinks (N := N)) → G =>
      Umat ρ p u :=
  continuous_pi fun i => continuous_pi fun j =>
    continuous_Umat_apply ρ hρcont p i j

/-- A word is continuous in its matrix. -/
theorem continuous_word {n : ℕ} (α : Fin n → Fin d × Fin d) :
    Continuous fun M : Matrix (Fin d) (Fin d) ℂ =>
      GramWord.word α M := by
  unfold GramWord.word
  refine continuous_finset_prod Finset.univ fun j _ => ?_
  exact (continuous_apply _).comp (continuous_apply _)

/-- F1's B-feature is continuous in the negative-half
configuration through the arc matrix. -/
theorem continuous_featB
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (w : GramWord.WordIdx d)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) :
    Continuous fun u : ↥(negLinks (N := N)) → G =>
      GramWord.featB w (Umat ρ p u) := by
  unfold GramWord.featB GramWord.featB1 GramWord.featB2
  exact ((continuous_word _).comp
    (continuous_Umat ρ hρcont p)).mul
    (((continuous_word _).comp
      (continuous_Umat ρ hρcont p)).star)

/-- F1's A-feature (trivial plane split) is continuous in the
closed-half configuration through the arc matrix. -/
theorem continuous_featA
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (c : ℝ) (w : GramWord.WordIdx d)
    (p : (Fin 4 → ZMod N) × Fin 4 × Fin 4) :
    Continuous fun y : ↥(halfLinks (N := N)) → G =>
      GramWord.featA c w (Xmat ρ p y) 1 1 := by
  unfold GramWord.featA GramWord.featA1 GramWord.featA2
  exact ((continuous_const.mul
      ((continuous_word _).comp
        (continuous_Xmat ρ hρcont p))).mul
      continuous_const).mul
    ((continuous_const.mul
      (((continuous_word _).comp
        (continuous_Xmat ρ hρcont p)).star)).mul
      continuous_const)

/-- The assembled A-feature is almost-everywhere strongly
measurable against the product Haar measure (the criterion's
`hAA` for this family). -/
theorem aestronglyMeasurable_featGA
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (β : ℝ) (i : SeamIdx (N := N)) :
    AEStronglyMeasurable (featGA ρ β i)
      (Measure.pi fun _ : ↥(halfLinks (N := N)) => μG) := by
  have hA : Measurable fun y : ↥(halfLinks (N := N)) → G =>
      halfActionP ρ β (restrictPos y) :=
    (measurable_halfActionP_lf ρ hρcont β).comp
      measurable_restrictPos_lf
  have hscal : Measurable fun y : ↥(halfLinks (N := N)) → G =>
      ((Real.exp (- halfActionP ρ β (restrictPos y)) : ℂ)
        * (Real.exp (-β * ((zeroFinset (N := N)).card : ℝ)) : ℂ)) :=
    ((Complex.continuous_ofReal.measurable).comp
      ((Real.continuous_exp.measurable).comp hA.neg)).mul
      measurable_const
  have hprod : Continuous fun y : ↥(halfLinks (N := N)) → G =>
      ∏ p : ↥(zeroFinset (N := N)),
        GramWord.featA (β / d) (i p) (Xmat ρ p y) 1 1 :=
    continuous_finset_prod Finset.univ fun p _ =>
      continuous_featA ρ hρcont (β / d) (i p) p.1
  unfold featGA
  exact (hscal.aestronglyMeasurable).mul
    hprod.aestronglyMeasurable

/-- The assembled B-feature is almost-everywhere strongly
measurable against the product Haar measure (the criterion's
`hBA` for this family). -/
theorem aestronglyMeasurable_featGB
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ) (i : SeamIdx (N := N)) :
    AEStronglyMeasurable (featGB ρ hN β i)
      (Measure.pi fun _ : ↥(negLinks (N := N)) => μG) := by
  have hA : Measurable fun u : ↥(negLinks (N := N)) → G =>
      halfActionP ρ β (mirrorP hN u) :=
    (measurable_halfActionP_lf ρ hρcont β).comp
      (measurable_mirrorP_lf (N := N) hN)
  have hscal : Measurable fun u : ↥(negLinks (N := N)) → G =>
      ((Real.exp (- halfActionP ρ β (mirrorP hN u)) : ℂ)) :=
    (Complex.continuous_ofReal.measurable).comp
      ((Real.continuous_exp.measurable).comp hA.neg)
  have hprod : Continuous fun u : ↥(negLinks (N := N)) → G =>
      ∏ p : ↥(zeroFinset (N := N)),
        GramWord.featB (i p) (Umat ρ p u) :=
    continuous_finset_prod Finset.univ fun p _ =>
      continuous_featB ρ hρcont (i p) p.1
  unfold featGB
  exact (hscal.aestronglyMeasurable).mul
    hprod.aestronglyMeasurable

/-! ## §6. Domination -/

/-- F1's A-side bound is nonnegative. -/
theorem wordCA_nonneg (c : ℝ) (w : GramWord.WordIdx d) :
    0 ≤ GramWord.wordCA c 1 w := by
  simp only [GramWord.wordCA]
  positivity

/-- F1's B-side bound is nonnegative. -/
theorem wordCB_nonneg (w : GramWord.WordIdx d) :
    0 ≤ GramWord.wordCB 1 w := by
  simp only [GramWord.wordCB]
  positivity

/-- The half action is bounded by the total plaquette count
times the maximal density `2`. -/
theorem abs_halfActionP_le (hd : 0 < d) (β : ℝ)
    (z : ↥(posLinks (N := N)) → G) :
    |halfActionP ρ β z|
      ≤ |β| * (2 * ((plaqIndex (N := N)).card : ℝ)) := by
  have hd2 : ∀ p : (Fin 4 → ZMod N) × Fin 4 × Fin 4,
      |plaquetteDensity (torusShift N) ρ (extendP z)
        p.1 p.2.1 p.2.2| ≤ 2 := fun p =>
    abs_le.mpr
      ⟨by linarith [(Set.mem_Icc.mp
          (plaquetteDensity_mem_Icc (torusShift N) ρ hd
            (extendP z) p.1 p.2.1 p.2.2)).1],
       (Set.mem_Icc.mp (plaquetteDensity_mem_Icc (torusShift N) ρ
          hd (extendP z) p.1 p.2.1 p.2.2)).2⟩
  unfold halfActionP wilsonActionPlus
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg β)
  refine ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun p _ => hd2 p)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : (((plaqIndex (N := N)).filter IsPosPlaq).card : ℝ)
      ≤ ((plaqIndex (N := N)).card : ℝ) :=
    by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  linarith [hc]

/-- The assembled A-side domination constant is nonnegative
(the criterion's `hCA`). -/
theorem boundCA_nonneg (β : ℝ) (i : SeamIdx (d := d) (N := N)) :
    0 ≤ boundCA β i := by
  unfold boundCA
  exact mul_nonneg (Real.exp_nonneg _)
    (Finset.prod_nonneg fun p _ => wordCA_nonneg _ _)

/-- The assembled B-side domination constant is nonnegative. -/
theorem boundCB_nonneg (β : ℝ) (i : SeamIdx (d := d) (N := N)) :
    0 ≤ boundCB β i := by
  unfold boundCB
  exact mul_nonneg (Real.exp_nonneg _)
    (Finset.prod_nonneg fun p _ => wordCB_nonneg _)

/-- The per-plaquette A-bound, packaged with a general
matrix. (F1's application is elaborated once, here, with the
matrix a plain variable: composing it directly at `Xmat`
terms over the seam subtype blows up the elaborator's
defeq.) -/
theorem norm_featA_le_of_entries (β : ℝ) (w : GramWord.WordIdx d)
    (X : Matrix (Fin d) (Fin d) ℂ) (hX : ∀ a b, ‖X a b‖ ≤ 1) :
    ‖GramWord.featA (β / d) w X 1 1‖
      ≤ GramWord.wordCA (β / d) 1 w :=
  GramWord.norm_featA_le (β / d) 1 (by norm_num) X 1 1 hX
    (fun a b => norm_one_entry a b)
    (fun a b => norm_one_entry a b) w

/-- The per-plaquette B-bound, packaged with a general
matrix. -/
theorem norm_featB_le_of_entries (w : GramWord.WordIdx d)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : ∀ a b, ‖U a b‖ ≤ 1) :
    ‖GramWord.featB w U‖ ≤ GramWord.wordCB 1 w := by
  have h := GramWord.norm_featB_le 1 (by norm_num) U hU w
  rwa [norm_star] at h

/-- The per-plaquette A-bound at a seam plaquette, stated
over the raw plaquette with its seam membership (no subtype
coercion in the statement: with `↑p` inside `featA`, the
elaborator's defeq blows up). -/
theorem norm_featA_factor (β : ℝ) (i : SeamIdx (d := d) (N := N))
    (y : ↥(halfLinks (N := N)) → G)
    (q : (Fin 4 → ZMod N) × Fin 4 × Fin 4)
    (hq : q ∈ zeroFinset (N := N)) :
    ‖GramWord.featA (β / d) (i ⟨q, hq⟩) (Xmat ρ q y) 1 1‖
      ≤ GramWord.wordCA (β / d) 1 (i ⟨q, hq⟩) :=
  norm_featA_le_of_entries β (i ⟨q, hq⟩) (Xmat ρ q y)
    (fun a b => norm_Xmat_entry ρ q y a b)

/-- The per-plaquette B-bound at a seam plaquette. -/
theorem norm_featB_factor (i : SeamIdx (d := d) (N := N))
    (u : ↥(negLinks (N := N)) → G)
    (q : (Fin 4 → ZMod N) × Fin 4 × Fin 4)
    (hq : q ∈ zeroFinset (N := N)) :
    ‖GramWord.featB (i ⟨q, hq⟩) (Umat ρ q u)‖
      ≤ GramWord.wordCB 1 (i ⟨q, hq⟩) :=
  norm_featB_le_of_entries (i ⟨q, hq⟩) (Umat ρ q u)
    (fun a b => norm_Umat_entry ρ q u a b)

set_option maxHeartbeats 1600000 in
/-- The assembled A-feature bound (the criterion's `hAB`). -/
theorem norm_featGA_le (hd : 0 < d) (β : ℝ) (i : SeamIdx (N := N))
    (y : ↥(halfLinks (N := N)) → G) :
    ‖featGA ρ β i y‖ ≤ boundCA β i := by
  have h1 : Real.exp (- halfActionP ρ β (restrictPos y))
      ≤ Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))) :=
    (Real.exp_le_exp.mpr (neg_le_abs _)).trans
      (Real.exp_le_exp.mpr (abs_halfActionP_le ρ hd β _))
  have h2 : Real.exp (-β * ((zeroFinset (N := N)).card : ℝ))
      ≤ Real.exp (|β| * ((zeroFinset (N := N)).card : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_abs β)
      (by positivity))
  have hscal : ‖((Real.exp (- halfActionP ρ β (restrictPos y)) : ℂ)
        * (Real.exp (-β * ((zeroFinset (N := N)).card : ℝ)) : ℂ))‖
      ≤ Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ)
          + ((zeroFinset (N := N)).card : ℝ))) := by
    rw [norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_nonneg _),
      abs_of_nonneg (Real.exp_nonneg _)]
    refine (mul_le_mul h1 h2 (Real.exp_nonneg _)
      (le_trans (Real.exp_nonneg _) h1)).trans ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (le_of_eq (by ring))
  have hprod : ‖∏ p : ↥(zeroFinset (N := N)),
        GramWord.featA (β / d) (i p) (Xmat ρ p y) 1 1‖
      ≤ ∏ p : ↥(zeroFinset (N := N)),
          GramWord.wordCA (β / d) 1 (i p) := by
    refine (norm_prod_le_prod Finset.univ _).trans
      (prod_le_prod_nonneg Finset.univ _ _
        (fun p _ => norm_nonneg _)
        (fun p _ => ?_))
    exact norm_featA_factor ρ β i y p.1 p.2
  unfold featGA boundCA
  refine (norm_mul_le _ _).trans ?_
  exact mul_le_mul hscal hprod (norm_nonneg _) (Real.exp_nonneg _)

/-- The assembled B-feature bound (the criterion's `hBB`). -/
theorem norm_featGB_le (hd : 0 < d) (hN : Even N) (β : ℝ)
    (i : SeamIdx (N := N)) (u : ↥(negLinks (N := N)) → G) :
    ‖featGB ρ hN β i u‖ ≤ boundCB β i := by
  have h1 : Real.exp (- halfActionP ρ β (mirrorP hN u))
      ≤ Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))) :=
    (Real.exp_le_exp.mpr (neg_le_abs _)).trans
      (Real.exp_le_exp.mpr (abs_halfActionP_le ρ hd β _))
  have hscal : ‖((Real.exp (- halfActionP ρ β (mirrorP hN u)) : ℂ))‖
      ≤ Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_nonneg _)]
    exact h1
  have hprod : ‖∏ p : ↥(zeroFinset (N := N)),
        GramWord.featB (i p) (Umat ρ p u)‖
      ≤ ∏ p : ↥(zeroFinset (N := N)), GramWord.wordCB 1 (i p) := by
    refine (norm_prod_le_prod Finset.univ _).trans
      (prod_le_prod_nonneg Finset.univ _ _
        (fun p _ => norm_nonneg _)
        (fun p _ => ?_))
    exact norm_featB_factor ρ i u p.1 p.2
  unfold featGB boundCB
  refine (norm_mul_le _ _).trans ?_
  exact mul_le_mul hscal hprod (norm_nonneg _) (Real.exp_nonneg _)

/-- The assembled domination product is summable (the
criterion's `hsum`): a constant times the product over the
seam of F1's per-plaquette summable bound products. -/
theorem summable_boundCA_mul_boundCB (β : ℝ) :
    Summable fun i : SeamIdx (d := d) (N := N) =>
      boundCA β i * boundCB β i := by
  have hW : Nonempty (GramWord.WordIdx d) :=
    ⟨(⟨0, fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩,
      ⟨0, fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩)⟩
  have h : Summable fun x : SeamIdx (d := d) (N := N) =>
      ∏ p : ↥(zeroFinset (N := N)),
        (GramWord.wordCA (β / d) 1 (x p)
          * GramWord.wordCB 1 (x p)) :=
    (hasSum_pi_prod (ι := ↥(zeroFinset (N := N))) hW
    (fun p w => GramWord.wordCA (β / d) 1 w
      * GramWord.wordCB 1 w)
    (fun p w => GramWord.wordCA (β / d) 1 w
      * GramWord.wordCB 1 w)
    (fun p w => mul_nonneg (wordCA_nonneg _ _) (wordCB_nonneg _))
    (fun p w => by
      rw [Real.norm_eq_abs]
      exact le_of_eq (abs_of_nonneg
        (mul_nonneg (wordCA_nonneg _ _) (wordCB_nonneg _))))
    (fun _ => GramWord.summable_wordCA_mul (β / d) 1
      (by norm_num))).summable
  have h2 : Summable fun i : SeamIdx (d := d) (N := N) =>
      (Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ)
          + ((zeroFinset (N := N)).card : ℝ)))
        * Real.exp (|β| * (2 * ((plaqIndex (N := N)).card : ℝ))))
      * ∏ p : ↥(zeroFinset (N := N)),
          (GramWord.wordCA (β / d) 1 (i p)
            * GramWord.wordCB 1 (i p)) :=
    h.mul_left _
  refine h2.congr fun i => ?_
  unfold boundCA boundCB
  rw [Finset.prod_mul_distrib]
  ring

/-! ## §7. The package for F3 -/

/-- **Brick F2's package.** Everything the integrated Gram
criterion `osForm_nonneg_of_gram_integrated` asks of its
family — measurability of both features, the domination
constants' nonnegativity, the pointwise bounds, the
summability of the bound product, and the pointwise Gram
identity `hgram` for the seam kernel — assembled for the word
family of §1. NOT included: the criterion's two marginal
identities (`hmargA`/`hmargB` through a common `Ξ` with
nonnegative dampings — the Damping Lemma), which are FALSE
for this family; see the F2 verdict memo for the exhibited
mechanism (pre-registered kills K-F2(b)/(c)). -/
theorem assembly_package
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (hd : 0 < d) (β : ℝ) :
    (∀ i, AEStronglyMeasurable (featGA ρ β i)
      (Measure.pi fun _ : ↥(halfLinks (N := N)) => μG))
    ∧ (∀ i, AEStronglyMeasurable (featGB ρ hN β i)
      (Measure.pi fun _ : ↥(negLinks (N := N)) => μG))
    ∧ (∀ i : SeamIdx (d := d) (N := N), 0 ≤ boundCA β i)
    ∧ (∀ (i : SeamIdx (d := d) (N := N))
        (y : ↥(halfLinks (N := N)) → G),
        ‖featGA ρ β i y‖ ≤ boundCA β i)
    ∧ (∀ (i : SeamIdx (d := d) (N := N))
        (u : ↥(negLinks (N := N)) → G),
        ‖featGB ρ hN β i u‖ ≤ boundCB β i)
    ∧ (Summable fun i : SeamIdx (d := d) (N := N) =>
        boundCA β i * boundCB β i)
    ∧ (∀ (y : ↥(halfLinks (N := N)) → G)
        (u : ↥(negLinks (N := N)) → G),
      ((Real.exp (- wilsonAction (torusShift N) ρ β
          ((splitEquiv (halfLinks (N := N))).symm (y, u))) : ℝ) : ℂ)
        = ∑' i, (starRingEnd ℂ) (featGB ρ hN β i u)
            * featGA ρ β i y) :=
  ⟨fun i => aestronglyMeasurable_featGA μG ρ hρcont β i,
   fun i => aestronglyMeasurable_featGB μG ρ hρcont hN β i,
   fun i => boundCA_nonneg β i,
   fun i y => norm_featGA_le ρ hd β i y,
   fun i u => norm_featGB_le ρ hd hN β i u,
   summable_boundCA_mul_boundCB β,
   fun y u => assembly_hgram ρ hN hd β y u⟩

end GramAssemblyWord

end ThetLogos
