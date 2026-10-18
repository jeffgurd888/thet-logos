import ThetLogos.FockPackaging
import ThetLogos.FermionicLimitOps

/-!
# Fock packaging — fermionic statistics

Commission: FOCK PACKAGING (Rung 7 remainder, packaging half),
gauntlet verdict STANDS-AS-PRICED (M), **concrete ONB port only**
(Kill K4 permanent: the abstract SymmetricAlgebra route is dead
and is not used).

This module is the fermionic half of the packaging; the bosonic
half is `ThetLogos.FockPackagingBos`. The two statistics live in
separate modules under one dossier: at packaging time the corpus's
two second-quantization stacks could not be co-imported in one
environment (`numberOp`/`numberOp_basis` collided between
`FermionicFock` and `BosonicAssembly`) — that fence is HISTORICAL,
discharged 2026-10-18 (see the header note in
`ThetLogos.FockPackaging` and the packaging-rename dossier);
neither stack is imported here — this module imports only
`ThetLogos.FockPackaging` (the one-particle shell representation)
and `ThetLogos.FermionicLimitOps` (the fermionic limit stack).

Route (concrete ONB port). The one-particle side is the corpus's
mass-shell representation `shellU1` on `shellLp m hm`, with the
concrete orthonormal basis `shellONB`. For a one-particle unitary
`W`, the second-quantized operator `Γ(W)` on the fermionic Fock
space `FermionicFockLim` is assembled from the **limit minor
kernel**: the determinant minor of the matrix of `W` in the shell
basis, between finite occupation sets `S T : Finset ℕ`,
normalized by nothing (fermionic minors carry no norm factors).

Contents.

* §F1: the limit minor kernel at the limit (`minorDetLimOf`,
  `gammaKernelFermLim`), the cardinality guard, the adjoint
  identity of the entries.
* §F2: transport along the tower embeddings: at configurations
  embedded from finite levels, the limit kernel is the corpus's
  rectangular/square minor determinant (`minorDetRect`,
  `minorDet`); the kernel adjoint identity at the limit.
* §F3: entry Gram limits, the determinant bound, and the column
  bound (B0F) giving `Summable` columns — the analytic input for
  the assembled operator.
* §F4: the three limit theorems: the kernel of the identity is
  the Kronecker delta (L1F), column orthonormality (L3′F), and
  the functor law at the limit (L2F), all by finite-level
  exhaustion through `minorDet_mul` (Cauchy–Binet) at a common
  level, with enumeration coherence `fermConfigEmb_orderEmbOfFin`.
* §F5: assembly: columns as Fock vectors, the operator on the
  finite-particle domain `fermDomLim`, inner preservation,
  extension by density to a linear isometry of the whole space,
  the global adjoint identity, and `gammaFockF`, the packaged
  unitary.
* §F6: the packaged Poincaré representation `gammaFockFU1`, its
  group law, vacuum invariance, sector preservation, and strong
  continuity of the translation subgroup (transported from
  `shellU1_translation_tendsto`).

Fences (in writing):

* The group is the corpus's restricted Poincaré group
  `RPoincare`, the group of `shellU1`.
* The representation law holds in the corrected order forced by
  Mathlib's `LinearIsometryEquiv.trans` convention (first factor
  acts first): `Γ(g₁ * g₂) = Γ(g₂) ⋙ Γ(g₁)`.
* Lorentz/rotation strong continuity is NOT part of this brick:
  only the translation subgroup's strong continuity is packaged,
  transported from the one-particle input. The full-group
  operator-level statement makes no continuity claim.
-/


open scoped InnerProductSpace
open scoped Matrix
open Filter Topology

namespace ThetLogos

/-! ## §F1. The limit minor kernel -/

/-- The entry matrix of a one-particle unitary `W` in the
concrete shell basis: `UmatF W j i = ⟪b j, W (b i)⟫`. -/
noncomputable def UmatF (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (j i : ℕ) : ℂ :=
  ⟪shellONB m hm j, W (shellONB m hm i)⟫_ℂ

/-- The finite compression of the entry matrix to level `d`. -/
noncomputable def UmatRectF (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i j => UmatF m hm W i.val j.val

/-- **The limit minor determinant (T1):** the determinant minor
of the entry kernel `A : ℕ → ℕ → ℂ` between a source
configuration `S` and a target configuration `T` (finite
occupation sets of modes), with the enumeration
`Finset.orderEmbOfFin`, and the cardinality guard. -/
noncomputable def minorDetLimOf (A : ℕ → ℕ → ℂ) (S T : Finset ℕ) : ℂ :=
  if h : S.card = T.card then
    Matrix.det (fun a b : Fin T.card =>
      A (T.orderEmbOfFin rfl a) (S.orderEmbOfFin h b))
  else 0

/-- The limit kernel in (target, source) order (T1). -/
noncomputable def gammaKernelFermLimOf (A : ℕ → ℕ → ℂ)
    (T S : Finset ℕ) : ℂ :=
  minorDetLimOf A S T

/-- The kernel vanishes off the cardinality diagonal (T1). -/
theorem minorDetLimOf_of_card_ne (A : ℕ → ℕ → ℂ) (S T : Finset ℕ)
    (h : S.card ≠ T.card) : minorDetLimOf A S T = 0 := dif_neg h

/-- **The fermionic Γ-kernel at the limit (T1):**
`gammaKernelFermLim W T S` is the `T`-row, `S`-column of the
packaged operator. -/
noncomputable def gammaKernelFermLim (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (T S : Finset ℕ) : ℂ :=
  gammaKernelFermLimOf (UmatF m hm W) T S

/-- The fermionic kernel vanishes off the cardinality diagonal
(T1). -/
theorem gammaKernelFermLim_of_card_ne (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (T S : Finset ℕ)
    (h : S.card ≠ T.card) : gammaKernelFermLim m hm W T S = 0 :=
  minorDetLimOf_of_card_ne _ _ _ h

/-- Pairing against an inverse is the adjoint pairing (T1). -/
theorem inner_symm_apply {m : ℝ} {hm : 0 < m}
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (x y : shellLp m hm) :
    ⟪x, W.symm y⟫_ℂ = ⟪W x, y⟫_ℂ := by
  rw [← LinearIsometryEquiv.inner_map_map W x (W.symm y),
    LinearIsometryEquiv.apply_symm_apply]

/-- The entries of `W.symm` are the conjugate-transposed entries
of `W` (T1). -/
theorem UmatF_symm (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (j i : ℕ) :
    UmatF m hm W.symm j i = star (UmatF m hm W i j) := by
  unfold UmatF
  rw [inner_symm_apply]
  simp only [inner_conj_symm, RCLike.star_def]

/-! ## §F2. Finite-level transport -/

/-- Enumeration coherence for the limit embedding (T1): the
order-embedding of an embedded configuration is the embedding of
its order-embedding, for any cardinality proof. Proved by the
uniqueness of `Finset.orderEmbOfFin`, mirroring the corpus's
`fermConfigEmb_orderEmbOfFin`. -/
theorem orderEmbOfFin_fermConfigEmbLim {d : ℕ} (S : Finset (Fin d))
    {n : ℕ} (h : (fermConfigEmbLim d S).card = n) (hS : S.card = n)
    (a : Fin n) :
    (fermConfigEmbLim d S).orderEmbOfFin h a
      = ((S.orderEmbOfFin hS a : Fin d) : ℕ) := by
  have hunique : (fun a : Fin n => ((S.orderEmbOfFin hS a : Fin d)
        : ℕ))
      = (fermConfigEmbLim d S).orderEmbOfFin h := by
    apply Finset.orderEmbOfFin_unique h
    · intro a
      show ((S.orderEmbOfFin hS a : Fin d) : ℕ)
        ∈ Finset.map Fin.valEmbedding S
      exact Finset.mem_map.mpr ⟨S.orderEmbOfFin hS a,
        Finset.orderEmbOfFin_mem _ _ _, rfl⟩
    · intro a b hab
      exact (S.orderEmbOfFin hS).strictMono hab
  exact (congrFun hunique a).symm

/-- Enumeration transport across cardinality proofs (T1): the
order-embedding of a finset, read at a transported index, is the
order-embedding at the other cardinality. By uniqueness of
`Finset.orderEmbOfFin`. -/
theorem orderEmbOfFin_card_transport {α : Type*} [LinearOrder α]
    {s : Finset α} {n m : ℕ} (h₁ : s.card = n) (h₂ : s.card = m)
    (a : Fin n) :
    s.orderEmbOfFin h₁ a
      = s.orderEmbOfFin h₂ (finCongr (h₁.symm.trans h₂) a) := by
  have hunique : (fun a : Fin n =>
        s.orderEmbOfFin h₂ (finCongr (h₁.symm.trans h₂) a))
      = s.orderEmbOfFin h₁ := by
    apply Finset.orderEmbOfFin_unique h₁
    · intro a
      exact Finset.orderEmbOfFin_mem _ _ _
    · intro a b hab
      exact (s.orderEmbOfFin h₂).strictMono hab
  exact congrFun hunique a

/-- **Transport of the limit minor (T1):** at configurations
embedded from finite levels, the limit minor of `A` is the
corpus's rectangular minor determinant of the compressed
matrix. -/
theorem minorDetLimOf_fermConfigEmbLim (A : ℕ → ℕ → ℂ) (d e : ℕ)
    (S : Finset (Fin d)) (T : Finset (Fin e)) :
    minorDetLimOf A (fermConfigEmbLim d S) (fermConfigEmbLim e T)
      = minorDetRect (fun i j => A (i : ℕ) (j : ℕ)) S T := by
  unfold minorDetLimOf minorDetRect
  by_cases h : S.card = T.card
  · have h' : (fermConfigEmbLim d S).card
        = (fermConfigEmbLim e T).card := by
      rw [fermConfigEmbLim_card, fermConfigEmbLim_card, h]
    rw [dif_pos h', dif_pos h]
    have hcardT : (fermConfigEmbLim e T).card = T.card :=
      fermConfigEmbLim_card e T
    rw [← Matrix.det_submatrix_equiv_self (finCongr hcardT)
      (fun a b : Fin T.card => A (T.orderEmbOfFin rfl a)
        (S.orderEmbOfFin h b))]
    congr 1
    funext a b
    show A ((fermConfigEmbLim e T).orderEmbOfFin rfl a)
        ((fermConfigEmbLim d S).orderEmbOfFin h' b)
      = A (T.orderEmbOfFin rfl (finCongr hcardT a))
        (S.orderEmbOfFin h (finCongr hcardT b))
    rw [orderEmbOfFin_fermConfigEmbLim T rfl hcardT.symm,
      orderEmbOfFin_card_transport hcardT.symm rfl,
      orderEmbOfFin_fermConfigEmbLim S h' (h.trans hcardT.symm),
      orderEmbOfFin_card_transport (h.trans hcardT.symm) h]
  · have h' : (fermConfigEmbLim d S).card
        ≠ (fermConfigEmbLim e T).card := by
      rwa [fermConfigEmbLim_card, fermConfigEmbLim_card]
    rw [dif_neg h', dif_neg h]

/-- **Square transport (T1):** at a common finite level, the
limit kernel is the corpus's square minor determinant of the
compressed entry matrix. -/
theorem gammaKernelFermLim_fermConfigEmbLim (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (d : ℕ)
    (S T : Finset (Fin d)) :
    gammaKernelFermLim m hm W (fermConfigEmbLim d T)
        (fermConfigEmbLim d S)
      = minorDet d (UmatRectF m hm W d) S T := by
  unfold gammaKernelFermLim gammaKernelFermLimOf UmatRectF
  rw [minorDetLimOf_fermConfigEmbLim]
  exact minorDetRect_eq_minorDet _ _ _

/-- The compressed matrix of `W.symm` is the conjugate transpose
of the compressed matrix of `W` (T1). -/
theorem UmatRectF_symm (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (d : ℕ) :
    UmatRectF m hm W.symm d = (UmatRectF m hm W d)ᴴ := by
  funext i j
  show UmatF m hm W.symm i.val j.val
    = star (UmatF m hm W j.val i.val)
  exact UmatF_symm m hm W i.val j.val

/-- **Kernel adjoint identity at the limit (T1):** the kernel of
`W.symm` is the conjugate transpose of the kernel of `W`. -/
theorem gammaKernelFermLim_symm (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (T S : Finset ℕ) :
    gammaKernelFermLim m hm W.symm T S
      = star (gammaKernelFermLim m hm W S T) := by
  obtain ⟨d₁, S₀, hS⟩ := fermConfig_factor S
  obtain ⟨d₂, T₀, hT⟩ := fermConfig_factor T
  set D := max d₁ d₂ with hD
  set S₁ := fermConfigEmb (le_max_left d₁ d₂) S₀ with hS₁
  set T₁ := fermConfigEmb (le_max_right d₁ d₂) T₀ with hT₁
  have hSD : fermConfigEmbLim D S₁ = S := by
    rw [hS₁, fermConfigEmbLim_comp, hS]
  have hTD : fermConfigEmbLim D T₁ = T := by
    rw [hT₁, fermConfigEmbLim_comp, hT]
  rw [← hSD, ← hTD, gammaKernelFermLim_fermConfigEmbLim,
    gammaKernelFermLim_fermConfigEmbLim, UmatRectF_symm,
    minorDet_conjTranspose]
/-! ## §F3. Entry Gram limits, the determinant bound, B0F

The three generic exhaustion helpers below are statistic-free;
they were re-proved here because, at packaging time, the bosonic
module that owns them could not be co-imported with this one (see
the header; that fence was discharged 2026-10-18). -/

/-- Finite sets are absorbed by a monotone exhaustion (T1). -/
theorem exists_forall_mem_of_monotone {α : Type*} (s : ℕ → Finset α)
    (hmono : Monotone s) (t : Finset α)
    (hcov : ∀ a ∈ t, ∃ e, a ∈ s e) : ∃ e, ∀ a ∈ t, a ∈ s e := by
  classical
  induction t using Finset.induction with
  | empty => exact ⟨0, fun a ha => absurd ha (Finset.notMem_empty a)⟩
  | insert a t _ ih =>
      obtain ⟨e₁, he₁⟩ := ih (fun a ha => hcov a (Finset.mem_insert_of_mem ha))
      obtain ⟨e₂, he₂⟩ := hcov a (Finset.mem_insert_self a t)
      exact ⟨max e₁ e₂, fun x hx => by
        rw [Finset.mem_insert] at hx
        cases hx with
        | inl hx => exact hmono (le_max_right _ _) (hx ▸ he₂)
        | inr hx => exact hmono (le_max_left _ _) (he₁ x hx)⟩

/-- **Exhaustion (T1):** if a summable function's partial sums over
a monotone exhaustion — covering every index where the function is
nonzero — converge to `L`, then `L` is the `tsum`. -/
theorem tsum_eq_of_tendsto_sum_exhaustion {α : Type*} {f : α → ℂ}
    (hf : Summable f) (s : ℕ → Finset α) (hmono : Monotone s)
    (hcov : ∀ a, f a ≠ 0 → ∃ e, a ∈ s e)
    {L : ℂ} (hL : Tendsto (fun e => ∑ a ∈ s e, f a) atTop (𝓝 L)) :
    ∑' a, f a = L := by
  classical
  have hT : Tendsto (fun e => ∑ a ∈ s e, f a) atTop (𝓝 (∑' a, f a)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨t₀, ht₀⟩ := by
      have hε := (Metric.tendsto_nhds.1 hf.hasSum) (ε / 2) (by linarith)
      rw [SummationFilter.unconditional_filter] at hε
      exact mem_atTop_sets.1 hε
    -- The support part of `t₀` is absorbed by the exhaustion.
    obtain ⟨E, hE⟩ := exists_forall_mem_of_monotone s hmono
      (t₀.filter (fun a => f a ≠ 0))
      (fun a ha => hcov a (Finset.mem_filter.1 ha).2)
    refine ⟨E, fun e he => ?_⟩
    have hunion : ∑ a ∈ s e ∪ t₀, f a = ∑ a ∈ s e, f a := by
      refine (Finset.sum_subset Finset.subset_union_left ?_).symm
      intro a ha hae
      by_contra hfa
      have ha₀ : a ∈ t₀ := (Finset.mem_union.1 ha).resolve_left hae
      have haA : a ∈ t₀.filter (fun a => f a ≠ 0) :=
        Finset.mem_filter.2 ⟨ha₀, hfa⟩
      exact hae (hmono he (hE a haA))
    have hdist : dist (∑ a ∈ s e ∪ t₀, f a) (∑' a, f a) < ε / 2 :=
      ht₀ (s e ∪ t₀) Finset.subset_union_right
    rw [hunion] at hdist
    exact hdist.trans (half_lt_self hε)
  exact tendsto_nhds_unique hT hL

/-- **Product of two `ℓ²` families is summable (T1):** the
`AM–GM` bound against the two square-summable families. -/
theorem summable_mul_of_summable_sq {α : Type*} {f g : α → ℂ}
    (hf : Summable (fun a => ‖f a‖ ^ 2))
    (hg : Summable (fun a => ‖g a‖ ^ 2)) :
    Summable (fun a => f a * g a) := by
  refine Summable.of_norm_bounded (g := fun a => (‖f a‖ ^ 2 + ‖g a‖ ^ 2) / 2)
    ((hf.add hg).div_const 2) ?_
  intro a
  rw [norm_mul]
  have h := two_mul_le_add_sq ‖f a‖ ‖g a‖
  linarith


/-- The squared norm as a conjugate product (T1). -/
theorem ofReal_norm_sq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
  simpa using (RCLike.conj_mul z).symm

/-- Conjugate of an entry (T1). -/
theorem star_UmatF (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (k i : ℕ) :
    star (UmatF m hm W k i)
      = ⟪W (shellONB m hm i), shellONB m hm k⟫_ℂ := by
  rw [UmatF]
  exact inner_conj_symm _ _

/-- **Entry Gram convergence (T1):** partial column-Gram sums of
the entries converge to the one-particle inner product,
Parseval's identity in the shell basis. -/
theorem UmatF_partial_tendsto (m : ℝ) (hm : 0 < m)
    (W₁ W₂ : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (i j : ℕ) :
    Tendsto (fun e => ∑ k ∈ Finset.range e,
        star (UmatF m hm W₁ k i) * UmatF m hm W₂ k j)
      atTop (𝓝 ⟪W₁ (shellONB m hm i), W₂ (shellONB m hm j)⟫_ℂ) := by
  have h := ((shellONB m hm).hasSum_inner_mul_inner
    (W₁ (shellONB m hm i)) (W₂ (shellONB m hm j))).tendsto_sum_nat
  refine Filter.Tendsto.congr ?_ h
  intro e
  apply Finset.sum_congr rfl
  intro k _
  symm
  rw [star_UmatF m hm W₁ k i, UmatF]

/-- **Entry Gram convergence, composed form (T1):** the partial
sums of the composed entries converge to the entries of the
composition. -/
theorem UmatF_partial_tendsto_mid (m : ℝ) (hm : 0 < m)
    (W₁ W₂ : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (i j : ℕ) :
    Tendsto (fun e => ∑ k ∈ Finset.range e, UmatF m hm W₂ i k
        * UmatF m hm W₁ k j) atTop
      (𝓝 ⟪shellONB m hm i, (W₁.trans W₂) (shellONB m hm j)⟫_ℂ) := by
  have h : Tendsto (fun e => ∑ k ∈ Finset.range e,
      ⟪W₂.symm (shellONB m hm i), shellONB m hm k⟫_ℂ
        * ⟪shellONB m hm k, W₁ (shellONB m hm j)⟫_ℂ) atTop
      (𝓝 ⟪W₂.symm (shellONB m hm i), W₁ (shellONB m hm j)⟫_ℂ) :=
    ((shellONB m hm).hasSum_inner_mul_inner _ _).tendsto_sum_nat
  have hlim : ⟪W₂.symm (shellONB m hm i), W₁ (shellONB m hm j)⟫_ℂ
      = ⟪shellONB m hm i, (W₁.trans W₂) (shellONB m hm j)⟫_ℂ := by
    have h2 : ⟪W₂.symm (shellONB m hm i), W₁ (shellONB m hm j)⟫_ℂ
        = ⟪W₂ (W₂.symm (shellONB m hm i)), W₂ (W₁ (shellONB m hm j))⟫_ℂ :=
      (LinearIsometryEquiv.inner_map_map W₂ _ _).symm
    rw [LinearIsometryEquiv.trans_apply, h2,
      LinearIsometryEquiv.apply_symm_apply]
  rw [← hlim]
  refine Filter.Tendsto.congr (fun e => ?_) h
  apply Finset.sum_congr rfl
  intro k _
  have e1 : ⟪W₂.symm (shellONB m hm i), shellONB m hm k⟫_ℂ
      = UmatF m hm W₂ i k := by
    have h3 : ⟪W₂.symm (shellONB m hm i), shellONB m hm k⟫_ℂ
        = ⟪W₂ (W₂.symm (shellONB m hm i)), W₂ (shellONB m hm k)⟫_ℂ :=
      (LinearIsometryEquiv.inner_map_map W₂ _ _).symm
    rw [h3, LinearIsometryEquiv.apply_symm_apply]
    rfl
  rw [e1]
  rfl

/-- **Bessel bound for finite partial sums (T1):** the squared
moduli of the first `e` entries of any column of `UmatF W` sum
to at most `1`. -/
theorem sum_sq_UmatF_le (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (e j : ℕ) :
    ∑ k : Fin e, ‖UmatF m hm W k.val j‖ ^ 2 ≤ 1 := by
  have hb := (shellONB m hm).orthonormal.sum_inner_products_le
    (W (shellONB m hm j)) (s := Finset.range e)
  rw [LinearIsometryEquiv.norm_map, (shellONB m hm).orthonormal.norm_eq_one j,
    one_pow] at hb
  show ∑ k : Fin e, ‖⟪shellONB m hm k.val, W (shellONB m hm j)⟫_ℂ‖ ^ 2 ≤ 1
  have h2 : (∑ k : Fin e, ‖⟪shellONB m hm k.val, W (shellONB m hm j)⟫_ℂ‖ ^ 2)
      = ∑ i ∈ Finset.range e, ‖⟪shellONB m hm i, W (shellONB m hm j)⟫_ℂ‖ ^ 2 :=
    Fin.sum_univ_eq_sum_range (fun i => ‖⟪shellONB m hm i,
      W (shellONB m hm j)⟫_ℂ‖ ^ 2) e
  rw [h2]
  exact hb

/-- **Cauchy–Schwarz for Gram sums (T1).** -/
theorem norm_UmatGramF_le (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (E : ℕ) (i j : ℕ) :
    ‖∑ k : Fin E, star (UmatF m hm W k.val i) * UmatF m hm W k.val j‖
      ≤ Real.sqrt (∑ k : Fin E, ‖UmatF m hm W k.val i‖ ^ 2)
        * Real.sqrt (∑ k : Fin E, ‖UmatF m hm W k.val j‖ ^ 2) := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin E))
    (fun k => ‖UmatF m hm W k.val i‖) (fun k => ‖UmatF m hm W k.val j‖)
  have hsum : ‖∑ k : Fin E, star (UmatF m hm W k.val i) * UmatF m hm W k.val j‖
      ≤ ∑ k : Fin E, ‖UmatF m hm W k.val i‖ * ‖UmatF m hm W k.val j‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    apply Finset.sum_le_sum
    intro k _
    rw [norm_mul, norm_star]
  refine le_trans hsum ?_
  have hnn : (0 : ℝ) ≤ ∑ k : Fin E, ‖UmatF m hm W k.val i‖
      * ‖UmatF m hm W k.val j‖ :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have h1 : ∑ k : Fin E, ‖UmatF m hm W k.val i‖ * ‖UmatF m hm W k.val j‖
      ≤ Real.sqrt ((∑ k : Fin E, ‖UmatF m hm W k.val i‖ ^ 2)
          * (∑ k : Fin E, ‖UmatF m hm W k.val j‖ ^ 2)) := by
    rw [Real.le_sqrt hnn (by positivity)]
    exact hCS
  refine le_trans h1 ?_
  rw [Real.sqrt_mul (Finset.sum_nonneg (fun k _ => sq_nonneg _))]

/-- Entries of the finite Gram matrix of `UmatF W` (T1). -/
theorem UmatRectF_gram_apply (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (E : ℕ) (i j : Fin E) :
    ((UmatRectF m hm W E)ᴴ * (UmatRectF m hm W E)) i j
      = ∑ k : Fin E, star (UmatF m hm W k.val i.val)
          * UmatF m hm W k.val j.val := by
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.conjTranspose_apply]
  rfl

/-- **Gram entries are at most `1` in modulus (T1).** -/
theorem norm_UmatRectF_gram_entry_le (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (E : ℕ) (i j : Fin E) :
    ‖((UmatRectF m hm W E)ᴴ * (UmatRectF m hm W E)) i j‖ ≤ 1 := by
  rw [UmatRectF_gram_apply]
  refine le_trans (norm_UmatGramF_le m hm W E i.val j.val) ?_
  have hv : ∀ j : ℕ, Real.sqrt (∑ k : Fin E, ‖UmatF m hm W k.val j‖ ^ 2)
      ≤ 1 := fun j => by
    simpa using Real.sqrt_le_sqrt (sum_sq_UmatF_le m hm W E j)
  refine le_trans (mul_le_mul (hv _) (hv _) (Real.sqrt_nonneg _)
    (by norm_num)) ?_
  norm_num

/-- **Determinant bound (T1):** a minor determinant of a matrix
with all entries of modulus at most `1` has modulus at most the
factorial of the minor's size — the Leibniz expansion, the
triangle inequality, and `Fintype.card_perm`. -/
theorem norm_minorDet_le {e : ℕ} (M : Matrix (Fin e) (Fin e) ℂ)
    (hM : ∀ i j, ‖M i j‖ ≤ 1) (S T : Finset (Fin e))
    (h : S.card = T.card) :
    ‖minorDet e M S T‖ ≤ (Nat.factorial T.card : ℝ) := by
  suffices hsuff : ∀ (A : Matrix (Fin T.card) (Fin T.card) ℂ),
      (∀ a b, ‖A a b‖ ≤ 1) → ‖A.det‖ ≤ (Nat.factorial T.card : ℝ) by
    rw [minorDet_apply e h M]
    exact hsuff _ (fun a b => hM _ _)
  intro A hA
  calc ‖A.det‖ = ‖∑ σ, ((Equiv.Perm.sign σ : ℤ) : ℂ)
        * ∏ i, A (σ i) i‖ := by rw [Matrix.det_apply']
    _ ≤ ∑ σ, ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A (σ i) i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin T.card), (1 : ℝ) := by
        refine Finset.sum_le_sum (fun σ _ => ?_)
        have hε : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
          have h3 : |(Equiv.Perm.sign σ : ℤ)| = 1 := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
              <;> rw [h1] <;> rfl
          rw [norm_intCast_eq_abs_mul_norm_one, norm_one, mul_one, h3]
          norm_num
        refine (norm_mul_le _ _).trans ?_
        rw [hε, one_mul]
        refine (Finset.norm_prod_le _ _).trans ?_
        exact Finset.prod_le_one₀ (fun b _ => norm_nonneg _)
          (fun b _ => hA _ _)
    _ = (Nat.factorial T.card : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
          Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- The deterministic factorization of a configuration through
its `attachFin` representative (T1). -/
theorem fermConfigEmbLim_attachFin (T : Finset ℕ) :
    fermConfigEmbLim (T.sup id + 1)
        (T.attachFin (fun m hm =>
          Nat.lt_succ_of_le (Finset.le_sup (f := id) hm))) = T := by
  ext n
  simp only [fermConfigEmbLim_apply, Finset.mem_map, Finset.mem_attachFin]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hn
    exact ⟨⟨n, Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)⟩, hn, rfl⟩

/-- **Column bound B0F (T1):** for every finite set of target
configurations, the sum of squared kernel entries in the column
over a fixed source `S` is at most `(S.card)!`. Factorization at
a common level `E`, Cauchy–Binet (`minorDet_mul`) read backwards,
and the determinant bound. -/
theorem gammaKernelFermLim_col_sum_le (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (S : Finset ℕ)
    (s : Finset (Finset ℕ)) :
    ∑ T ∈ s, ‖gammaKernelFermLim m hm W T S‖ ^ 2
      ≤ (Nat.factorial S.card : ℝ) := by
  classical
  set E := (S.sup id + 1) + ∑ T ∈ s, (T.sup id + 1) with hEdef
  have hlev : ∀ T ∈ s, T.sup id + 1 ≤ E := by
    intro T hT
    have h1 := Finset.single_le_sum (f := fun T => T.sup id + 1)
      (fun x _ => Nat.zero_le _) hT
    rw [hEdef]
    omega
  have hlevS : S.sup id + 1 ≤ E := by rw [hEdef]; omega
  -- Step 1: only matching cardinalities contribute.
  have step1 : ∑ T ∈ s, ‖gammaKernelFermLim m hm W T S‖ ^ 2
      = ∑ T ∈ s.filter (fun T => T.card = S.card),
        ‖gammaKernelFermLim m hm W T S‖ ^ 2 := by
    refine (Finset.sum_filter_of_ne (fun T _ hT => ?_)).symm
    by_contra hne
    apply hT
    rw [gammaKernelFermLim_of_card_ne m hm W T S
      (fun hh => hne hh.symm)]
    simp
  -- Step 2: representatives at level `E`, chosen non-dependently.
  set S₀E := fermConfigEmb hlevS (S.attachFin (fun m hm =>
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hm))) with hS₀E
  have hSE : fermConfigEmbLim E S₀E = S := by
    rw [hS₀E, fermConfigEmbLim_comp, fermConfigEmbLim_attachFin]
  have hcardSE : S₀E.card = S.card := by
    have h := fermConfigEmbLim_card E S₀E
    rw [hSE] at h
    exact h.symm
  have hfac : ∀ T : Finset ℕ, ∃ T₀ : Finset (Fin E),
      T ∈ s.filter (fun T => T.card = S.card)
        → fermConfigEmbLim E T₀ = T := by
    intro T
    by_cases hT : T ∈ s.filter (fun T => T.card = S.card)
    · have hTm := (Finset.mem_filter.1 hT).1
      exact ⟨fermConfigEmb (hlev T hTm) (T.attachFin (fun m hm =>
        Nat.lt_succ_of_le (Finset.le_sup (f := id) hm))),
        fun _ => by rw [fermConfigEmbLim_comp,
          fermConfigEmbLim_attachFin]⟩
    · exact ⟨∅, fun h => absurd h hT⟩
  set φ : Finset ℕ → Finset (Fin E) := fun T => (hfac T).choose with hφdef
  have hφ : ∀ T ∈ s.filter (fun T => T.card = S.card),
      fermConfigEmbLim E (φ T) = T :=
    fun T hT => (hfac T).choose_spec hT
  have hterm : ∀ T ∈ s.filter (fun T => T.card = S.card),
      ‖gammaKernelFermLim m hm W T S‖ ^ 2
        = ‖minorDet E (UmatRectF m hm W E) S₀E (φ T)‖ ^ 2 := by
    intro T hT
    have hγ := gammaKernelFermLim_fermConfigEmbLim m hm W E S₀E (φ T)
    rw [hφ T hT, hSE] at hγ
    rw [hγ]
  -- Step 3: the full level-`E` sum is the Gram determinant.
  have hid : ((∑ T₀ : Finset (Fin E),
        ‖minorDet E (UmatRectF m hm W E) S₀E T₀‖ ^ 2 : ℝ) : ℂ)
      = minorDet E ((UmatRectF m hm W E)ᴴ * (UmatRectF m hm W E))
          S₀E S₀E := by
    rw [Complex.ofReal_sum, minorDet_mul]
    refine Finset.sum_congr rfl (fun T₀ _ => ?_)
    rw [minorDet_conjTranspose]
    exact ofReal_norm_sq _
  have hfull : ∑ T₀ : Finset (Fin E),
        ‖minorDet E (UmatRectF m hm W E) S₀E T₀‖ ^ 2
      ≤ (Nat.factorial S.card : ℝ) := by
    calc ∑ T₀ : Finset (Fin E),
          ‖minorDet E (UmatRectF m hm W E) S₀E T₀‖ ^ 2
        = ‖((∑ T₀ : Finset (Fin E),
            ‖minorDet E (UmatRectF m hm W E) S₀E T₀‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg
            (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
      _ = ‖minorDet E ((UmatRectF m hm W E)ᴴ * (UmatRectF m hm W E))
            S₀E S₀E‖ := by rw [hid]
      _ ≤ (Nat.factorial S₀E.card : ℝ) :=
          norm_minorDet_le _ (fun i j =>
            norm_UmatRectF_gram_entry_le m hm W E i j) _ _ rfl
      _ = (Nat.factorial S.card : ℝ) := by rw [hcardSE]
  -- Assemble.
  have hsumimg : ∑ T ∈ s.filter (fun T => T.card = S.card),
        ‖minorDet E (UmatRectF m hm W E) S₀E (φ T)‖ ^ 2
      = ∑ T₀ ∈ (s.filter (fun T => T.card = S.card)).image φ,
        ‖minorDet E (UmatRectF m hm W E) S₀E T₀‖ ^ 2 := by
    apply Finset.sum_bij (fun T _ => φ T)
    · intro T hT
      exact Finset.mem_image.mpr ⟨T, hT, rfl⟩
    · intro x hx y hy hxy
      have hx' : x ∈ s.filter (fun T => T.card = S.card) := hx
      have hy' : y ∈ s.filter (fun T => T.card = S.card) := hy
      have h1 := hφ x hx'
      have h2 := hφ y hy'
      rw [← h1, ← h2, hxy]
    · intro T₀ hT₀
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hT₀
      exact ⟨T, hT, rfl⟩
    · intro T _
      rfl
  rw [step1]
  calc ∑ T ∈ s.filter (fun T => T.card = S.card),
        ‖gammaKernelFermLim m hm W T S‖ ^ 2
      = ∑ T ∈ s.filter (fun T => T.card = S.card),
          ‖minorDet E (UmatRectF m hm W E) S₀E (φ T)‖ ^ 2 :=
        Finset.sum_congr rfl hterm
    _ = ∑ T₀ ∈ (s.filter (fun T => T.card = S.card)).image φ,
          ‖minorDet E (UmatRectF m hm W E) S₀E T₀‖ ^ 2 :=
        hsumimg
    _ ≤ ∑ T₀ : Finset (Fin E),
          ‖minorDet E (UmatRectF m hm W E) S₀E T₀‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun T₀ _ _ => sq_nonneg _)
    _ ≤ (Nat.factorial S.card : ℝ) := hfull

/-- **Column summability (T1),** from B0F. -/
theorem gammaKernelFermLim_summable_col (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (S : Finset ℕ) :
    Summable (fun T => ‖gammaKernelFermLim m hm W T S‖ ^ 2) :=
  summable_of_sum_le (fun T => by positivity)
    (fun s => gammaKernelFermLim_col_sum_le m hm W S s)

/-- **Row summability (T1),** via the adjoint identity. -/
theorem gammaKernelFermLim_summable_row (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (T : Finset ℕ) :
    Summable (fun S => ‖gammaKernelFermLim m hm W T S‖ ^ 2) := by
  apply Summable.congr (gammaKernelFermLim_summable_col m hm W.symm T)
  intro S
  rw [gammaKernelFermLim_symm, norm_star]

/-! ## §F4. The three limit theorems -/

/-- Determinant continuity at a fixed finite level (T1): the
determinant is a finite sum of finite products of entries. -/
theorem det_tendsto_of_tendsto {ι : Type*} {l : Filter ι}
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (X : ι → Matrix κ κ ℂ) (Y : Matrix κ κ ℂ)
    (hXY : ∀ i j, Tendsto (fun t => X t i j) l (𝓝 (Y i j))) :
    Tendsto (fun t => (X t).det) l (𝓝 Y.det) := by
  have hX' : ∀ t, (X t).det = ∑ σ, ((Equiv.Perm.sign σ : ℤ) : ℂ)
      * ∏ i, X t (σ i) i := fun t => Matrix.det_apply' _
  have hY' : Y.det = ∑ σ, ((Equiv.Perm.sign σ : ℤ) : ℂ)
      * ∏ i, Y (σ i) i := Matrix.det_apply' _
  rw [hY']
  refine Filter.Tendsto.congr (fun t => (hX' t).symm) ?_
  refine tendsto_finsetSum _ (fun σ _ => Tendsto.mul tendsto_const_nhds ?_)
  refine tendsto_finsetProd _ (fun a _ => ?_)
  exact hXY _ _

/-- Minor continuity at a fixed finite level, along any filter
(T1). -/
theorem minorDet_tendsto_of_tendsto {ι : Type*} {l : Filter ι}
    {e : ℕ} (X : ι → Matrix (Fin e) (Fin e) ℂ)
    (Y : Matrix (Fin e) (Fin e) ℂ)
    (hXY : ∀ i j, Tendsto (fun t => X t i j) l (𝓝 (Y i j)))
    (S T : Finset (Fin e)) :
    Tendsto (fun t => minorDet e (X t) S T) l
      (𝓝 (minorDet e Y S T)) := by
  by_cases h : S.card = T.card
  · have key : ∀ t, minorDet e (X t) S T = Matrix.det
        (fun a b : Fin T.card => X t (T.orderEmbOfFin rfl a)
          (S.orderEmbOfFin h b)) :=
      fun t => minorDet_apply e h (X t)
    have keyY : minorDet e Y S T = Matrix.det
        (fun a b : Fin T.card => Y (T.orderEmbOfFin rfl a)
          (S.orderEmbOfFin h b)) := minorDet_apply e h Y
    rw [keyY]
    refine Filter.Tendsto.congr (fun t => (key t).symm) ?_
    exact det_tendsto_of_tendsto _ _ (fun a b => hXY _ _)
  · have key : (fun t => minorDet e (X t) S T) = fun _ => (0 : ℂ) :=
      funext (fun t => minorDet_of_card_ne _ (X t) h)
    rw [key, minorDet_of_card_ne _ Y h]
    exact tendsto_const_nhds

/-- The compressed matrix of the identity is the identity
matrix (T1). -/
theorem UmatRectF_one (m : ℝ) (hm : 0 < m) (d : ℕ) :
    UmatRectF m hm 1 d = (1 : Matrix (Fin d) (Fin d) ℂ) := by
  funext i j
  have h1 : ((1 : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm)
      (shellONB m hm j.val)) = shellONB m hm j.val := rfl
  show UmatF m hm 1 i.val j.val = (1 : Matrix (Fin d) (Fin d) ℂ) i j
  unfold UmatF
  rw [h1, Matrix.one_apply,
    orthonormal_iff_ite.1 (shellONB m hm).orthonormal i.val j.val]
  exact (if_congr Fin.ext_iff rfl rfl).symm

/-- **L1F (T1):** the kernel of the identity is the Kronecker
delta. -/
theorem gammaKernelFermLim_one (m : ℝ) (hm : 0 < m)
    (T S : Finset ℕ) :
    gammaKernelFermLim m hm 1 T S = if T = S then 1 else 0 := by
  by_cases hTS : T = S
  · subst hTS
    rw [if_pos rfl]
    obtain ⟨d, T₀, hT⟩ := fermConfig_factor T
    rw [← hT, gammaKernelFermLim_fermConfigEmbLim, UmatRectF_one,
      minorDet_one, if_pos rfl]
  · by_cases hcard : S.card = T.card
    · obtain ⟨d₁, S₀, hS⟩ := fermConfig_factor S
      obtain ⟨d₂, T₀, hT⟩ := fermConfig_factor T
      set D := max d₁ d₂ with hD
      set S₁ := fermConfigEmb (le_max_left d₁ d₂) S₀ with hS₁
      set T₁ := fermConfigEmb (le_max_right d₁ d₂) T₀ with hT₁
      have hSD : fermConfigEmbLim D S₁ = S := by
        rw [hS₁, fermConfigEmbLim_comp, hS]
      have hTD : fermConfigEmbLim D T₁ = T := by
        rw [hT₁, fermConfigEmbLim_comp, hT]
      have hne : S₁ ≠ T₁ := by
        intro hcon
        apply hTS
        rw [← hSD, ← hTD, hcon]
      have hne2 : fermConfigEmbLim D T₁ ≠ fermConfigEmbLim D S₁ :=
        fun hh => hTS (hTD.symm.trans (hh.trans hSD))
      rw [← hSD, ← hTD, gammaKernelFermLim_fermConfigEmbLim,
        UmatRectF_one, minorDet_one, if_neg hne, if_neg hne2]
    · rw [gammaKernelFermLim_of_card_ne m hm 1 T S hcard, if_neg hTS]

/-- **The vacuum kernel (T1).** -/
theorem gammaKernelFermLim_empty (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (T : Finset ℕ) :
    gammaKernelFermLim m hm W T ∅ = if T = ∅ then 1 else 0 := by
  by_cases hT : T = ∅
  · subst hT
    rw [if_pos rfl]
    show minorDetLimOf (UmatF m hm W) ∅ ∅ = 1
    unfold minorDetLimOf
    rw [dif_pos rfl]
    exact Matrix.det_fin_zero
  · have hcard : (∅ : Finset ℕ).card ≠ T.card := by
      rw [Finset.card_empty]
      exact (Finset.card_pos.2
        (Finset.nonempty_iff_ne_empty.2 hT)).ne
    rw [if_neg hT, gammaKernelFermLim_of_card_ne m hm W T ∅ hcard]

/-- **Stage convergence (T1):** a minor determinant at the
growing level `max e d`, of configurations embedded from the
fixed level `d`, converges to the level-`d` minor of the entry
limit, when the matrix entries depend only on the mode values
and converge levelwise at fixed modes. -/
theorem minorDet_stage_tendsto {d : ℕ} (S₀ T₀ : Finset (Fin d))
    (h0 : S₀.card = T₀.card)
    (x : ℕ → ℕ → ℕ → ℂ) (Y : ℕ → ℕ → ℂ)
    (hx : ∀ i j : ℕ, Tendsto (fun e => x (max e d) i j) atTop
      (𝓝 (Y i j)))
    (X : (E : ℕ) → Matrix (Fin E) (Fin E) ℂ)
    (hX : ∀ (E : ℕ) (i j : Fin E), X E i j = x E i.val j.val) :
    Tendsto (fun e => minorDet (max e d) (X (max e d))
        (fermConfigEmb (le_max_right e d) S₀)
        (fermConfigEmb (le_max_right e d) T₀))
      atTop (𝓝 (minorDet d (fun i j => Y i.val j.val) S₀ T₀)) := by
  classical
  set A : ℕ → Matrix (Fin T₀.card) (Fin T₀.card) ℂ := fun e a b =>
    x (max e d) ((T₀.orderEmbOfFin rfl a : Fin d) : ℕ)
      ((S₀.orderEmbOfFin h0 b : Fin d) : ℕ) with hAdef
  have htarget : minorDet d (fun i j => Y i.val j.val) S₀ T₀
      = Matrix.det (fun a b : Fin T₀.card =>
          Y ((T₀.orderEmbOfFin rfl a : Fin d) : ℕ)
            ((S₀.orderEmbOfFin h0 b : Fin d) : ℕ)) :=
    minorDet_apply d h0 _
  have hstage : ∀ e, minorDet (max e d) (X (max e d))
        (fermConfigEmb (le_max_right e d) S₀)
        (fermConfigEmb (le_max_right e d) T₀) = (A e).det := by
    intro e
    have hcardS : (fermConfigEmb (le_max_right e d) S₀).card
        = S₀.card := fermConfigEmb_card ..
    have hcardT : (fermConfigEmb (le_max_right e d) T₀).card
        = T₀.card := fermConfigEmb_card ..
    have hcard : (fermConfigEmb (le_max_right e d) S₀).card
        = (fermConfigEmb (le_max_right e d) T₀).card := by
      rw [hcardS, hcardT, h0]
    set B : Matrix (Fin T₀.card) (Fin T₀.card) ℂ := fun a b =>
      X (max e d) ⟨(T₀.orderEmbOfFin rfl a).val,
        lt_of_lt_of_le (T₀.orderEmbOfFin rfl a).isLt
          (le_max_right e d)⟩
        ⟨(S₀.orderEmbOfFin h0 b).val,
          lt_of_lt_of_le (S₀.orderEmbOfFin h0 b).isLt
            (le_max_right e d)⟩ with hBdef
    have hBA : B = A e := by
      funext a b
      exact hX _ _ _
    rw [minorDet_apply _ hcard _, ← hBA,
      ← Matrix.det_submatrix_equiv_self (finCongr hcardT) B]
    congr 1
    funext a b
    show X (max e d) ((fermConfigEmb (le_max_right e d) T₀).orderEmbOfFin
          rfl a) ((fermConfigEmb (le_max_right e d) S₀).orderEmbOfFin
          hcard b)
      = X (max e d) ⟨(T₀.orderEmbOfFin rfl (finCongr hcardT a)).val,
          lt_of_lt_of_le (T₀.orderEmbOfFin rfl (finCongr hcardT a)).isLt
            (le_max_right e d)⟩
        ⟨(S₀.orderEmbOfFin h0 (finCongr hcardT b)).val,
          lt_of_lt_of_le (S₀.orderEmbOfFin h0 (finCongr hcardT b)).isLt
            (le_max_right e d)⟩
    rw [hX, hX]
    have valT : ((fermConfigEmb (le_max_right e d) T₀).orderEmbOfFin
          rfl a).val
        = (T₀.orderEmbOfFin rfl (finCongr hcardT a)).val := by
      have h1 : (fermConfigEmb (le_max_right e d) T₀).orderEmbOfFin rfl a
          = Fin.castLE (le_max_right e d)
            (T₀.orderEmbOfFin hcardT.symm a) :=
        fermConfigEmb_orderEmbOfFin (le_max_right e d) T₀ _ rfl
          hcardT.symm a
      have h2 : T₀.orderEmbOfFin hcardT.symm a
          = T₀.orderEmbOfFin rfl (finCongr hcardT a) := by
        have h := orderEmbOfFin_card_transport hcardT.symm rfl a
        rwa [show finCongr (hcardT.trans rfl) a
          = finCongr hcardT a from Fin.ext rfl] at h
      rw [h1, h2]
      rfl
    have valS : ((fermConfigEmb (le_max_right e d) S₀).orderEmbOfFin
          hcard b).val
        = (S₀.orderEmbOfFin h0 (finCongr hcardT b)).val := by
      have h0' : (fermConfigEmb (le_max_right e d) S₀).orderEmbOfFin
            hcard b
          = (fermConfigEmb (le_max_right e d) S₀).orderEmbOfFin rfl
            (finCongr (hcard.symm.trans rfl.symm) b) :=
        orderEmbOfFin_card_transport hcard rfl b
      have h1 : (fermConfigEmb (le_max_right e d) S₀).orderEmbOfFin rfl
            (finCongr (hcard.symm.trans rfl.symm) b)
          = Fin.castLE (le_max_right e d)
            (S₀.orderEmbOfFin hcardS.symm
              (finCongr (hcard.symm.trans rfl.symm) b)) :=
        fermConfigEmb_orderEmbOfFin (le_max_right e d) S₀ _ rfl
          hcardS.symm _
      have h2 : S₀.orderEmbOfFin hcardS.symm
            (finCongr (hcard.symm.trans rfl.symm) b)
          = S₀.orderEmbOfFin h0 (finCongr hcardT b) := by
        have h := orderEmbOfFin_card_transport hcardS.symm h0
          (finCongr (hcard.symm.trans rfl.symm) b)
        rwa [show finCongr (hcardS.trans h0)
            (finCongr (hcard.symm.trans rfl.symm) b)
          = finCongr hcardT b from Fin.ext rfl] at h
      rw [h0', h1, h2]
      rfl
    rw [valT, valS]
  rw [htarget]
  refine Filter.Tendsto.congr (fun e => (hstage e).symm) ?_
  exact det_tendsto_of_tendsto _ _ (fun a b => hx _ _)

/-- The stage levels tend to infinity (T1). -/
theorem tendsto_max_atTop (d : ℕ) :
    Tendsto (fun e => max e d) atTop atTop :=
  tendsto_atTop_mono (fun a => le_max_left a d) tendsto_id

/-- **L3′F (T1): column orthonormality of the limit kernel.**
The `T`-sum of conjugate pairs is the Kronecker delta on source
configurations. By exhaustion: partial sums over configurations
embedded from the growing level are, by Cauchy–Binet
(`minorDet_mul` at the square level), Gram minors of the entry
matrix, whose entries converge by Parseval. -/
theorem gammaKernelFermLim_column_orthonormal (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (S₁ S₂ : Finset ℕ) :
    ∑' T, star (gammaKernelFermLim m hm W T S₁)
        * gammaKernelFermLim m hm W T S₂
      = if S₁ = S₂ then 1 else 0 := by
  classical
  obtain ⟨d₁, S₁₀', hS₁'⟩ := fermConfig_factor S₁
  obtain ⟨d₂, S₂₀', hS₂'⟩ := fermConfig_factor S₂
  set D := max d₁ d₂ with hD
  set S₁₀ := fermConfigEmb (le_max_left d₁ d₂) S₁₀' with hS₁₀def
  set S₂₀ := fermConfigEmb (le_max_right d₁ d₂) S₂₀' with hS₂₀def
  have hS₁ : fermConfigEmbLim D S₁₀ = S₁ := by
    rw [hS₁₀def, fermConfigEmbLim_comp, hS₁']
  have hS₂ : fermConfigEmbLim D S₂₀ = S₂ := by
    rw [hS₂₀def, fermConfigEmbLim_comp, hS₂']
  have hcard₁₀ : S₁₀.card = S₁.card := by
    have h := fermConfigEmbLim_card D S₁₀
    rw [hS₁] at h
    exact h.symm
  have hcard₂₀ : S₂₀.card = S₂.card := by
    have h := fermConfigEmbLim_card D S₂₀
    rw [hS₂] at h
    exact h.symm
  -- Summability of the product.
  have hf : Summable (fun T => ‖star (gammaKernelFermLim m hm W T S₁)‖ ^ 2) := by
    simpa only [norm_star] using gammaKernelFermLim_summable_col m hm W S₁
  have hsum : Summable (fun T => star (gammaKernelFermLim m hm W T S₁)
      * gammaKernelFermLim m hm W T S₂) :=
    summable_mul_of_summable_sq hf (gammaKernelFermLim_summable_col m hm W S₂)
  -- The exhaustion.
  set s : ℕ → Finset (Finset ℕ) := fun e =>
    (Finset.univ : Finset (Finset (Fin (max e D)))).image
      (fermConfigEmbLim (max e D)) with hsdef
  have hmono : Monotone s := by
    intro e₁ e₂ h12 T hT
    obtain ⟨T₀, _, rfl⟩ := Finset.mem_image.1 hT
    exact Finset.mem_image.mpr ⟨fermConfigEmb
      (max_le_max h12 (le_refl D)) T₀, Finset.mem_univ _,
      fermConfigEmbLim_comp _ _⟩
  have hcov : ∀ T : Finset ℕ, star (gammaKernelFermLim m hm W T S₁)
      * gammaKernelFermLim m hm W T S₂ ≠ 0 → ∃ e, T ∈ s e := by
    intro T _
    obtain ⟨ℓ, T₀, hT₀⟩ := fermConfig_factor T
    exact ⟨ℓ, Finset.mem_image.mpr ⟨fermConfigEmb (le_max_left ℓ D) T₀,
      Finset.mem_univ _, by rw [fermConfigEmbLim_comp, hT₀]⟩⟩
  -- The partial identity at each stage.
  have hS₁e : ∀ e, fermConfigEmbLim (max e D)
      (fermConfigEmb (le_max_right e D) S₁₀) = S₁ := by
    intro e
    rw [fermConfigEmbLim_comp, hS₁]
  have hS₂e : ∀ e, fermConfigEmbLim (max e D)
      (fermConfigEmb (le_max_right e D) S₂₀) = S₂ := by
    intro e
    rw [fermConfigEmbLim_comp, hS₂]
  have hpartial : ∀ e, (∑ T ∈ s e, star (gammaKernelFermLim m hm W T S₁)
        * gammaKernelFermLim m hm W T S₂)
      = minorDet (max e D) ((UmatRectF m hm W (max e D))ᴴ
          * UmatRectF m hm W (max e D))
        (fermConfigEmb (le_max_right e D) S₂₀)
        (fermConfigEmb (le_max_right e D) S₁₀) := by
    intro e
    have hbij : (∑ T₀ : Finset (Fin (max e D)),
          star (gammaKernelFermLim m hm W
              (fermConfigEmbLim (max e D) T₀) S₁)
            * gammaKernelFermLim m hm W
              (fermConfigEmbLim (max e D) T₀) S₂)
        = ∑ T ∈ s e, star (gammaKernelFermLim m hm W T S₁)
            * gammaKernelFermLim m hm W T S₂ := by
      apply Finset.sum_bij (fun T₀ _ => fermConfigEmbLim (max e D) T₀)
      · intro T₀ _
        exact Finset.mem_image.mpr ⟨T₀, Finset.mem_univ _, rfl⟩
      · intro x _ y _ hxy
        exact (fermConfigEmbLim (max e D)).injective hxy
      · intro T hT
        obtain ⟨T₀, _, hT₀⟩ := Finset.mem_image.1 hT
        exact ⟨T₀, Finset.mem_univ _, hT₀⟩
      · intro T₀ _
        rfl
    rw [← hbij]
    have hγ₁ : ∀ T₀ : Finset (Fin (max e D)),
        gammaKernelFermLim m hm W (fermConfigEmbLim (max e D) T₀) S₁
          = minorDet (max e D) (UmatRectF m hm W (max e D))
            (fermConfigEmb (le_max_right e D) S₁₀) T₀ := by
      intro T₀
      rw [← hS₁e e]
      exact gammaKernelFermLim_fermConfigEmbLim m hm W (max e D) _ T₀
    have hγ₂ : ∀ T₀ : Finset (Fin (max e D)),
        gammaKernelFermLim m hm W (fermConfigEmbLim (max e D) T₀) S₂
          = minorDet (max e D) (UmatRectF m hm W (max e D))
            (fermConfigEmb (le_max_right e D) S₂₀) T₀ := by
      intro T₀
      rw [← hS₂e e]
      exact gammaKernelFermLim_fermConfigEmbLim m hm W (max e D) _ T₀
    have hsum : (∑ T₀ : Finset (Fin (max e D)),
          star (gammaKernelFermLim m hm W
              (fermConfigEmbLim (max e D) T₀) S₁)
            * gammaKernelFermLim m hm W
              (fermConfigEmbLim (max e D) T₀) S₂)
        = ∑ T₀ : Finset (Fin (max e D)),
            minorDet (max e D) ((UmatRectF m hm W (max e D))ᴴ) T₀
                (fermConfigEmb (le_max_right e D) S₁₀)
              * minorDet (max e D) (UmatRectF m hm W (max e D))
                (fermConfigEmb (le_max_right e D) S₂₀) T₀ :=
      Finset.sum_congr rfl (fun T₀ _ => by
        rw [hγ₁ T₀, hγ₂ T₀, minorDet_conjTranspose])
    rw [hsum]
    exact (minorDet_mul _ _ _ _ _).symm
  -- The stage limit.
  have hlim : Tendsto (fun e => ∑ T ∈ s e,
        star (gammaKernelFermLim m hm W T S₁)
          * gammaKernelFermLim m hm W T S₂)
      atTop (𝓝 (if S₁ = S₂ then 1 else 0)) := by
    by_cases hcard : S₁.card = S₂.card
    · have hcard₀ : S₂₀.card = S₁₀.card := by
        rw [hcard₂₀, hcard₁₀, hcard]
      have hstage := minorDet_stage_tendsto S₂₀ S₁₀ hcard₀
        (x := fun (E : ℕ) (i j : ℕ) => ∑ k : Fin E,
          star (UmatF m hm W k.val i) * UmatF m hm W k.val j)
        (Y := fun i j => if i = j then (1 : ℂ) else 0)
        (by
          intro i j
          have hval : ⟪W (shellONB m hm i), W (shellONB m hm j)⟫_ℂ
              = if i = j then (1 : ℂ) else 0 := by
            rw [LinearIsometryEquiv.inner_map_map]
            exact orthonormal_iff_ite.1 (shellONB m hm).orthonormal i j
          rw [← hval]
          refine Filter.Tendsto.congr (fun e => ?_)
            ((UmatF_partial_tendsto m hm W W i j).comp
              (tendsto_max_atTop D))
          exact (Fin.sum_univ_eq_sum_range
            (fun k => star (UmatF m hm W k i) * UmatF m hm W k j)
            (max e D)).symm)
        (X := fun E => (UmatRectF m hm W E)ᴴ * UmatRectF m hm W E)
        (fun E i j => UmatRectF_gram_apply m hm W E i j)
      -- the stage limit value: the minor of the identity kernel
      have hvalue : minorDet D (fun i j : Fin D =>
            (if (i : ℕ) = (j : ℕ) then (1 : ℂ) else 0)) S₂₀ S₁₀
          = if S₁ = S₂ then 1 else 0 := by
        have hm : (fun i j : Fin D => (if (i : ℕ) = (j : ℕ)
              then (1 : ℂ) else 0))
            = (1 : Matrix (Fin D) (Fin D) ℂ) := by
          funext i j
          show (if (i : ℕ) = (j : ℕ) then (1 : ℂ) else 0)
            = (1 : Matrix (Fin D) (Fin D) ℂ) i j
          rw [Matrix.one_apply]
          exact (if_congr Fin.ext_iff rfl rfl).symm
        rw [hm, minorDet_one]
        by_cases h : S₁ = S₂
        · have h2010 : S₂₀ = S₁₀ := by
            apply (fermConfigEmbLim D).injective
            rw [hS₂, hS₁, h]
          rw [if_pos h, if_pos h2010]
        · have h2010 : S₂₀ ≠ S₁₀ := by
            intro hh
            apply h
            rw [← hS₁, ← hS₂, hh]
          rw [if_neg h, if_neg h2010]
      rw [hvalue] at hstage
      exact Filter.Tendsto.congr (fun e => (hpartial e).symm) hstage
    · -- Card mismatch: every partial sum vanishes.
      have hzero : ∀ e, (∑ T ∈ s e, star (gammaKernelFermLim m hm W T S₁)
          * gammaKernelFermLim m hm W T S₂) = 0 := by
        intro e
        refine Finset.sum_eq_zero (fun T _ => ?_)
        by_cases hT1 : T.card = S₁.card
        · have hT2 : T.card ≠ S₂.card := fun hh => hcard (hT1 ▸ hh)
          rw [gammaKernelFermLim_of_card_ne m hm W T S₂
            (fun hh => hT2 hh.symm), mul_zero]
        · rw [gammaKernelFermLim_of_card_ne m hm W T S₁
            (fun hh => hT1 hh.symm), star_zero, zero_mul]
      have hne : S₁ ≠ S₂ := fun hh => hcard (by rw [hh])
      rw [if_neg hne]
      exact tendsto_const_nhds.congr (fun e => (hzero e).symm)
  exact tsum_eq_of_tendsto_sum_exhaustion hsum s hmono hcov hlim

/-- **L2F (T1): the functor law at the limit.** The kernel of a
composition is the `tsum` of the product of the kernels, in the
order forced by the `trans` convention. By exhaustion:
Cauchy–Binet (`minorDet_mul`) at the growing square level, and
Parseval entry convergence for the composed entries. -/
theorem gammaKernelFermLim_comp (m : ℝ) (hm : 0 < m)
    (W₁ W₂ : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (T S : Finset ℕ) :
    ∑' R, gammaKernelFermLim m hm W₂ T R
        * gammaKernelFermLim m hm W₁ R S
      = gammaKernelFermLim m hm (W₁.trans W₂) T S := by
  classical
  obtain ⟨d₁, T₀', hT'⟩ := fermConfig_factor T
  obtain ⟨d₂, S₀', hS'⟩ := fermConfig_factor S
  set D := max d₁ d₂ with hD
  set T₀ := fermConfigEmb (le_max_left d₁ d₂) T₀' with hT₀def
  set S₀ := fermConfigEmb (le_max_right d₁ d₂) S₀' with hS₀def
  have hT : fermConfigEmbLim D T₀ = T := by
    rw [hT₀def, fermConfigEmbLim_comp, hT']
  have hS : fermConfigEmbLim D S₀ = S := by
    rw [hS₀def, fermConfigEmbLim_comp, hS']
  have hcardT₀ : T₀.card = T.card := by
    have h := fermConfigEmbLim_card D T₀
    rw [hT] at h
    exact h.symm
  have hcardS₀ : S₀.card = S.card := by
    have h := fermConfigEmbLim_card D S₀
    rw [hS] at h
    exact h.symm
  have hsum : Summable (fun R => gammaKernelFermLim m hm W₂ T R
      * gammaKernelFermLim m hm W₁ R S) :=
    summable_mul_of_summable_sq (gammaKernelFermLim_summable_row m hm W₂ T)
      (gammaKernelFermLim_summable_col m hm W₁ S)
  set s : ℕ → Finset (Finset ℕ) := fun e =>
    (Finset.univ : Finset (Finset (Fin (max e D)))).image
      (fermConfigEmbLim (max e D)) with hsdef
  have hmono : Monotone s := by
    intro e₁ e₂ h12 R hR
    obtain ⟨R₀, _, rfl⟩ := Finset.mem_image.1 hR
    exact Finset.mem_image.mpr ⟨fermConfigEmb
      (max_le_max h12 (le_refl D)) R₀, Finset.mem_univ _,
      fermConfigEmbLim_comp _ _⟩
  have hcov : ∀ R : Finset ℕ, gammaKernelFermLim m hm W₂ T R
      * gammaKernelFermLim m hm W₁ R S ≠ 0 → ∃ e, R ∈ s e := by
    intro R _
    obtain ⟨ℓ, R₀, hR₀⟩ := fermConfig_factor R
    exact ⟨ℓ, Finset.mem_image.mpr ⟨fermConfigEmb (le_max_left ℓ D) R₀,
      Finset.mem_univ _, by rw [fermConfigEmbLim_comp, hR₀]⟩⟩
  have hTe : ∀ e, fermConfigEmbLim (max e D)
      (fermConfigEmb (le_max_right e D) T₀) = T := by
    intro e
    rw [fermConfigEmbLim_comp, hT]
  have hSe : ∀ e, fermConfigEmbLim (max e D)
      (fermConfigEmb (le_max_right e D) S₀) = S := by
    intro e
    rw [fermConfigEmbLim_comp, hS]
  have hpartial : ∀ e, (∑ R ∈ s e, gammaKernelFermLim m hm W₂ T R
        * gammaKernelFermLim m hm W₁ R S)
      = minorDet (max e D) (UmatRectF m hm W₂ (max e D)
          * UmatRectF m hm W₁ (max e D))
        (fermConfigEmb (le_max_right e D) S₀)
        (fermConfigEmb (le_max_right e D) T₀) := by
    intro e
    have hbij : (∑ R₀ : Finset (Fin (max e D)),
          gammaKernelFermLim m hm W₂ T (fermConfigEmbLim (max e D) R₀)
            * gammaKernelFermLim m hm W₁
              (fermConfigEmbLim (max e D) R₀) S)
        = ∑ R ∈ s e, gammaKernelFermLim m hm W₂ T R
            * gammaKernelFermLim m hm W₁ R S := by
      apply Finset.sum_bij (fun R₀ _ => fermConfigEmbLim (max e D) R₀)
      · intro R₀ _
        exact Finset.mem_image.mpr ⟨R₀, Finset.mem_univ _, rfl⟩
      · intro x _ y _ hxy
        exact (fermConfigEmbLim (max e D)).injective hxy
      · intro R hR
        obtain ⟨R₀, _, hR₀⟩ := Finset.mem_image.1 hR
        exact ⟨R₀, Finset.mem_univ _, hR₀⟩
      · intro R₀ _
        rfl
    rw [← hbij]
    have hγ₂ : ∀ R₀ : Finset (Fin (max e D)),
        gammaKernelFermLim m hm W₂ T (fermConfigEmbLim (max e D) R₀)
          = minorDet (max e D) (UmatRectF m hm W₂ (max e D)) R₀
            (fermConfigEmb (le_max_right e D) T₀) := by
      intro R₀
      rw [← hTe e]
      exact gammaKernelFermLim_fermConfigEmbLim m hm W₂ (max e D) R₀ _
    have hγ₁ : ∀ R₀ : Finset (Fin (max e D)),
        gammaKernelFermLim m hm W₁ (fermConfigEmbLim (max e D) R₀) S
          = minorDet (max e D) (UmatRectF m hm W₁ (max e D))
            (fermConfigEmb (le_max_right e D) S₀) R₀ := by
      intro R₀
      rw [← hSe e]
      exact gammaKernelFermLim_fermConfigEmbLim m hm W₁ (max e D) _ R₀
    have hsum' : (∑ R₀ : Finset (Fin (max e D)),
          gammaKernelFermLim m hm W₂ T (fermConfigEmbLim (max e D) R₀)
            * gammaKernelFermLim m hm W₁
              (fermConfigEmbLim (max e D) R₀) S)
        = ∑ R₀ : Finset (Fin (max e D)),
            minorDet (max e D) (UmatRectF m hm W₂ (max e D)) R₀
                (fermConfigEmb (le_max_right e D) T₀)
              * minorDet (max e D) (UmatRectF m hm W₁ (max e D))
                (fermConfigEmb (le_max_right e D) S₀) R₀ :=
      Finset.sum_congr rfl (fun R₀ _ => by rw [hγ₂ R₀, hγ₁ R₀])
    rw [hsum']
    exact (minorDet_mul _ _ _ _ _).symm
  have hlim : Tendsto (fun e => ∑ R ∈ s e,
        gammaKernelFermLim m hm W₂ T R
          * gammaKernelFermLim m hm W₁ R S)
      atTop (𝓝 (gammaKernelFermLim m hm (W₁.trans W₂) T S)) := by
    by_cases hcard : S.card = T.card
    · have hcard₀ : S₀.card = T₀.card := by
        rw [hcardS₀, hcardT₀, hcard]
      have hstage := minorDet_stage_tendsto S₀ T₀ hcard₀
        (x := fun (E : ℕ) (i j : ℕ) => ∑ k : Fin E,
          UmatF m hm W₂ i k.val * UmatF m hm W₁ k.val j)
        (Y := fun i j => UmatF m hm (W₁.trans W₂) i j)
        (by
          intro i j
          refine Filter.Tendsto.congr (fun e => ?_)
            ((UmatF_partial_tendsto_mid m hm W₁ W₂ i j).comp
              (tendsto_max_atTop D))
          exact (Fin.sum_univ_eq_sum_range
            (fun k => UmatF m hm W₂ i k * UmatF m hm W₁ k j)
            (max e D)).symm)
        (X := fun E => UmatRectF m hm W₂ E * UmatRectF m hm W₁ E)
        (fun E i j => by
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl (fun k _ => rfl))
      have htarget : minorDet D (fun i j =>
            UmatF m hm (W₁.trans W₂) i.val j.val) S₀ T₀
          = gammaKernelFermLim m hm (W₁.trans W₂) T S := by
        rw [← hS, ← hT]
        exact (gammaKernelFermLim_fermConfigEmbLim m hm (W₁.trans W₂)
          D S₀ T₀).symm
      rw [htarget] at hstage
      exact Filter.Tendsto.congr (fun e => (hpartial e).symm) hstage
    · have hzero : ∀ e, (∑ R ∈ s e, gammaKernelFermLim m hm W₂ T R
          * gammaKernelFermLim m hm W₁ R S) = 0 := by
        intro e
        refine Finset.sum_eq_zero (fun R _ => ?_)
        by_cases hR : R.card = S.card
        · have hRT : R.card ≠ T.card := fun hh => hcard (hR ▸ hh)
          rw [gammaKernelFermLim_of_card_ne m hm W₂ T R
            (fun hh => hRT hh), zero_mul]
        · rw [gammaKernelFermLim_of_card_ne m hm W₁ R S
            (fun hh => hR hh.symm), mul_zero]
      rw [gammaKernelFermLim_of_card_ne m hm (W₁.trans W₂) T S hcard]
      exact tendsto_const_nhds.congr (fun e => (hzero e).symm)
  exact tsum_eq_of_tendsto_sum_exhaustion hsum s hmono hcov hlim

/-! ## §F5. Assembly -/

/-- The coercion of the representation equivalence is the
linear combination (T1, definitional). -/
theorem fermEquivLim_coe (l : Finset ℕ →₀ ℂ) :
    ((fermEquivLim l : fermDomLim) : FermionicFockLim)
      = Finsupp.linearCombination ℂ fockBasisLim l := rfl

/-- **Kernel column (T1):** the would-be image of a basis vector
under `Γ(W)`, as an element of the limit fermionic Fock space;
its coordinates are the kernel column, in `ℓ²` by B0F. -/
noncomputable def colVecF (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (S : Finset ℕ) :
    FermionicFockLim :=
  ⟨fun T => gammaKernelFermLim m hm W T S, memℓp_gen (by
    have h := gammaKernelFermLim_summable_col m hm W S
    simpa using h)⟩

/-- Coordinates of a kernel column (T1, definitional). -/
theorem colVecF_apply (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (S T : Finset ℕ) :
    colVecF m hm W S T = gammaKernelFermLim m hm W T S := rfl

/-- The packaged operator on the finite-particle domain (T1). -/
noncomputable def gammaDomF (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) :
    fermDomLim →ₗ[ℂ] FermionicFockLim :=
  (Finsupp.linearCombination ℂ (colVecF m hm W))
    ∘ₗ fermReprLim.toLinearMap

/-- The packaged operator sends basis vectors to kernel columns
(T1). -/
theorem gammaDomF_fermEquivLim (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (φ : Finset ℕ →₀ ℂ) :
    gammaDomF m hm W (fermEquivLim φ)
      = Finsupp.linearCombination ℂ (colVecF m hm W) φ := by
  unfold gammaDomF
  rw [LinearMap.comp_apply]
  congr 1
  exact LinearEquiv.symm_apply_apply fermEquivLim φ

/-- Inner product of two kernel columns (T1): L3′F restated. -/
theorem inner_colVecF (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (S₁ S₂ : Finset ℕ) :
    ⟪colVecF m hm W S₁, colVecF m hm W S₂⟫_ℂ
      = if S₁ = S₂ then 1 else 0 := by
  calc ⟪colVecF m hm W S₁, colVecF m hm W S₂⟫_ℂ
      = ∑' T, ⟪gammaKernelFermLim m hm W T S₁,
          gammaKernelFermLim m hm W T S₂⟫_ℂ := by
        rw [lp.inner_eq_tsum]
        exact tsum_congr (fun T => by
          rw [colVecF_apply m hm W S₁ T, colVecF_apply m hm W S₂ T])
    _ = ∑' T, star (gammaKernelFermLim m hm W T S₁)
          * gammaKernelFermLim m hm W T S₂ := by
        refine tsum_congr (fun T => ?_)
        simp only [RCLike.inner_apply, RCLike.star_def]
        exact mul_comm _ _
    _ = if S₁ = S₂ then 1 else 0 :=
        gammaKernelFermLim_column_orthonormal m hm W S₁ S₂

/-- Inner product of a kernel column against a basis vector
(T1). -/
theorem inner_colVecF_fockBasisLim (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (S₁ S₂ : Finset ℕ) :
    ⟪colVecF m hm W S₁, fockBasisLim S₂⟫_ℂ
      = star (gammaKernelFermLim m hm W S₂ S₁) := by
  unfold fockBasisLim
  rw [lp.inner_single_right, colVecF_apply, RCLike.inner_apply,
    RCLike.star_def]
  simp

/-- Inner product of a basis vector against a kernel column
(T1). -/
theorem inner_fockBasisLim_colVecF (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (S₁ S₂ : Finset ℕ) :
    ⟪fockBasisLim S₁, colVecF m hm W S₂⟫_ℂ
      = gammaKernelFermLim m hm W S₁ S₂ := by
  unfold fockBasisLim
  rw [lp.inner_single_left, colVecF_apply, RCLike.inner_apply]
  simp

/-- A linear combination is its support sum (T1). -/
theorem linearCombination_eq_sum (v : Finset ℕ → FermionicFockLim)
    (φ : Finset ℕ →₀ ℂ) :
    Finsupp.linearCombination ℂ v φ
      = ∑ a ∈ φ.support, φ a • v a := by
  rw [Finsupp.linearCombination_apply]
  rfl

/-- **Finite-expansion inner formula (T1).** -/
theorem inner_linearCombination_mixed
    (v w : Finset ℕ → FermionicFockLim) (φ ψ : Finset ℕ →₀ ℂ) :
    ⟪Finsupp.linearCombination ℂ v φ,
        Finsupp.linearCombination ℂ w ψ⟫_ℂ
      = ∑ a ∈ φ.support, ∑ b ∈ ψ.support,
          starRingEnd ℂ (φ a) * (ψ b * ⟪v a, w b⟫_ℂ) := by
  rw [linearCombination_eq_sum, linearCombination_eq_sum, sum_inner]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [inner_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [inner_smul_left, inner_smul_right]

/-- Column combinations: the double sum collapses by L3′F (T1). -/
theorem inner_linearCombination_colVecF (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm)
    (φ ψ : Finset ℕ →₀ ℂ) :
    ⟪Finsupp.linearCombination ℂ (colVecF m hm W) φ,
        Finsupp.linearCombination ℂ (colVecF m hm W) ψ⟫_ℂ
      = ∑ c ∈ φ.support, starRingEnd ℂ (φ c) * ψ c := by
  rw [inner_linearCombination_mixed]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hterm : ∀ b ∈ ψ.support, starRingEnd ℂ (φ a)
        * (ψ b * ⟪colVecF m hm W a, colVecF m hm W b⟫_ℂ)
      = starRingEnd ℂ (φ a)
        * (ψ b * (if a = b then (1 : ℂ) else 0)) := by
    intro b _
    congr 1
    congr 1
    exact inner_colVecF m hm W a b
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  by_cases ha : a ∈ ψ.support
  · rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      rw [if_neg (fun h => hb h.symm), mul_zero]
    · exact fun h => (h ha).elim
  · have hψa : ψ a = 0 := Finsupp.notMem_support_iff.1 ha
    rw [hψa]
    refine Finset.sum_eq_zero (fun b hb => ?_)
    rw [if_neg (fun h : a = b => ha (h.symm ▸ hb)), mul_zero]

/-- **Isometry on the domain (T1):** the packaged operator
preserves inner products of finite-particle vectors. -/
theorem inner_gammaDomF (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (u v : fermDomLim) :
    ⟪gammaDomF m hm W u, gammaDomF m hm W v⟫_ℂ = ⟪u, v⟫_ℂ := by
  obtain ⟨φ, rfl⟩ : ∃ φ, fermEquivLim φ = u :=
    ⟨fermReprLim u, LinearEquiv.apply_symm_apply fermEquivLim u⟩
  obtain ⟨ψ, rfl⟩ : ∃ ψ, fermEquivLim ψ = v :=
    ⟨fermReprLim v, LinearEquiv.apply_symm_apply fermEquivLim v⟩
  have hφ : fermReprLim (fermEquivLim φ) = φ :=
    LinearEquiv.symm_apply_apply fermEquivLim φ
  have hψ : fermReprLim (fermEquivLim ψ) = ψ :=
    LinearEquiv.symm_apply_apply fermEquivLim ψ
  rw [gammaDomF_fermEquivLim, gammaDomF_fermEquivLim,
    inner_linearCombination_colVecF]
  rw [fermInner_expand_of_subset _ _ φ.support (by rw [hφ])]
  rw [hφ, hψ]

/-- **Adjoint identity on the domain (T1).** -/
theorem inner_gammaDomF_adjoint (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (u v : fermDomLim) :
    ⟪gammaDomF m hm W u, (v : FermionicFockLim)⟫_ℂ
      = ⟪(u : FermionicFockLim), gammaDomF m hm W.symm v⟫_ℂ := by
  obtain ⟨φ, rfl⟩ : ∃ φ, fermEquivLim φ = u :=
    ⟨fermReprLim u, LinearEquiv.apply_symm_apply fermEquivLim u⟩
  obtain ⟨ψ, rfl⟩ : ∃ ψ, fermEquivLim ψ = v :=
    ⟨fermReprLim v, LinearEquiv.apply_symm_apply fermEquivLim v⟩
  rw [gammaDomF_fermEquivLim, gammaDomF_fermEquivLim, fermEquivLim_coe,
    fermEquivLim_coe, inner_linearCombination_mixed,
    inner_linearCombination_mixed]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [inner_colVecF_fockBasisLim, inner_fockBasisLim_colVecF,
    gammaKernelFermLim_symm]

/-- The finite-particle domain is dense, as a set (T1). -/
theorem dense_fermDomLim : Dense (fermDomLim : Set FermionicFockLim) := by
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
    fermDomLim_topologicalClosure]
  ext x
  simp

/-- Density in `DenseRange` form for the subtype inclusion (T1). -/
theorem denseRange_subtype_fermDomLim :
    DenseRange (fermDomLim.subtype :
      ↥fermDomLim →ₗ[ℂ] FermionicFockLim) := by
  have h1 : Set.range (⇑(fermDomLim.subtype))
      = (fermDomLim : Set FermionicFockLim) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  show Dense (Set.range ⇑(fermDomLim.subtype))
  rw [h1]
  exact dense_fermDomLim

/-- The packaged operator preserves norms on the domain (T1). -/
theorem norm_gammaDomF (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (u : fermDomLim) :
    ‖gammaDomF m hm W u‖ = ‖fermDomLim.subtype u‖ := by
  have h := inner_gammaDomF m hm W u u
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖gammaDomF m hm W u‖ ^ 2 = ‖(u : FermionicFockLim)‖ ^ 2 := by
    exact_mod_cast h
  calc ‖gammaDomF m hm W u‖
      = Real.sqrt (‖gammaDomF m hm W u‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖(u : FermionicFockLim)‖ ^ 2) := by rw [h2]
    _ = ‖(u : FermionicFockLim)‖ := Real.sqrt_sq (norm_nonneg _)
    _ = ‖fermDomLim.subtype u‖ := rfl

/-- **The packaged operator (T1):** `Γ(W)` as a linear isometry
of the whole fermionic Fock space, extended from the
finite-particle domain by `extendOfIsometry`. -/
noncomputable def gammaIsometryF (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) :
    FermionicFockLim →ₗᵢ[ℂ] FermionicFockLim :=
  (gammaDomF m hm W).extendOfIsometry denseRange_subtype_fermDomLim
    (fun u => norm_gammaDomF m hm W u)

/-- The extension agrees with the domain operator on the domain
(T1). -/
theorem gammaIsometryF_apply_dom (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (u : fermDomLim) :
    gammaIsometryF m hm W (u : FermionicFockLim)
      = gammaDomF m hm W u :=
  LinearMap.extendOfIsometry_eq _ _ _ _

/-- **Adjoint identity on the whole space (T1):** `Γ(W.symm)` is
the adjoint of `Γ(W)`. Proved from the domain identity by two
closed-set density arguments. -/
theorem gammaIsometryF_adjoint (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm)
    (x y : FermionicFockLim) :
    ⟪gammaIsometryF m hm W x, y⟫_ℂ
      = ⟪x, gammaIsometryF m hm W.symm y⟫_ℂ := by
  have key : ∀ v : fermDomLim, ∀ x : FermionicFockLim,
      ⟪gammaIsometryF m hm W x, (v : FermionicFockLim)⟫_ℂ
        = ⟪x, gammaIsometryF m hm W.symm (v : FermionicFockLim)⟫_ℂ := by
    intro v
    have hclosed : IsClosed {x : FermionicFockLim |
        ⟪gammaIsometryF m hm W x, (v : FermionicFockLim)⟫_ℂ
          = ⟪x, gammaIsometryF m hm W.symm (v : FermionicFockLim)⟫_ℂ} :=
      isClosed_eq
        ((gammaIsometryF m hm W).continuous.inner continuous_const)
        (continuous_id.inner continuous_const)
    have hsub : (fermDomLim : Set FermionicFockLim)
        ⊆ {x : FermionicFockLim |
          ⟪gammaIsometryF m hm W x, (v : FermionicFockLim)⟫_ℂ
            = ⟪x, gammaIsometryF m hm W.symm
              (v : FermionicFockLim)⟫_ℂ} := by
      intro x hx
      show ⟪gammaIsometryF m hm W ((⟨x, hx⟩ : fermDomLim)
          : FermionicFockLim), (v : FermionicFockLim)⟫_ℂ
        = ⟪((⟨x, hx⟩ : fermDomLim) : FermionicFockLim),
          gammaIsometryF m hm W.symm (v : FermionicFockLim)⟫_ℂ
      rw [gammaIsometryF_apply_dom, gammaIsometryF_apply_dom]
      exact inner_gammaDomF_adjoint m hm W ⟨x, hx⟩ v
    have hfin := closure_minimal hsub hclosed
    rw [dense_fermDomLim.closure_eq] at hfin
    exact fun x => hfin (Set.mem_univ x)
  have hclosed : IsClosed {y : FermionicFockLim |
      ⟪gammaIsometryF m hm W x, y⟫_ℂ
        = ⟪x, gammaIsometryF m hm W.symm y⟫_ℂ} :=
    isClosed_eq (continuous_const.inner continuous_id)
      (continuous_const.inner (gammaIsometryF m hm W.symm).continuous)
  have hsub : (fermDomLim : Set FermionicFockLim)
      ⊆ {y : FermionicFockLim | ⟪gammaIsometryF m hm W x, y⟫_ℂ
          = ⟪x, gammaIsometryF m hm W.symm y⟫_ℂ} := by
    intro y hy
    exact key ⟨y, hy⟩ x
  have hfin := closure_minimal hsub hclosed
  rw [dense_fermDomLim.closure_eq] at hfin
  exact hfin (Set.mem_univ y)

/-- The packaged isometry is surjective (T1). -/
theorem gammaIsometryF_surjective (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) :
    Function.Surjective (gammaIsometryF m hm W) := by
  intro y
  refine ⟨gammaIsometryF m hm W.symm y, ?_⟩
  refine ext_inner_right ℂ (fun v => ?_)
  rw [gammaIsometryF_adjoint, LinearIsometry.inner_map_map]

/-- **The packaged unitary (T1):** `Γ(W)` as a unitary operator
(a linear isometry equivalence) on the fermionic Fock space. -/
noncomputable def gammaFockF (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) :
    FermionicFockLim ≃ₗᵢ[ℂ] FermionicFockLim :=
  LinearIsometryEquiv.ofSurjective (gammaIsometryF m hm W)
    (gammaIsometryF_surjective m hm W)

/-! ## §F6. The packaged Poincaré action -/

/-- Pairing with a basis vector reads off the coordinate (T1). -/
theorem inner_fockBasisLim_apply (T : Finset ℕ) (v : FermionicFockLim) :
    ⟪fockBasisLim T, v⟫_ℂ = v T := by
  unfold fockBasisLim
  rw [lp.inner_single_left, RCLike.inner_apply]
  simp

/-- `gammaFockF` applies as its underlying isometry (T1, `rfl`). -/
theorem gammaFockF_apply (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (z : FermionicFockLim) :
    gammaFockF m hm W z = gammaIsometryF m hm W z := rfl

/-- The packaged operator sends a basis vector to its kernel
column (T1). -/
theorem gammaIsometryF_fockBasisLim (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (S : Finset ℕ) :
    gammaIsometryF m hm W (fockBasisLim S) = colVecF m hm W S := by
  have hmem : fockBasisLim S
      = ((⟨fockBasisLim S, Submodule.subset_span ⟨S, rfl⟩⟩ : fermDomLim)
        : FermionicFockLim) := rfl
  rw [hmem, gammaIsometryF_apply_dom, ← fermEquivLim_basis,
    gammaDomF_fermEquivLim, Finsupp.linearCombination_single]
  simp

/-- **Coordinate formula (T1):** the `T`-coordinate of `Γ(W) z`
is the kernel transform of the coordinates of `z`. -/
theorem gammaIsometryF_coordinate (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (z : FermionicFockLim)
    (T : Finset ℕ) :
    (gammaIsometryF m hm W z) T
      = ∑' S, gammaKernelFermLim m hm W T S * z S := by
  have h1 : ⟪fockBasisLim T, gammaIsometryF m hm W z⟫_ℂ
      = ⟪gammaIsometryF m hm W.symm (fockBasisLim T), z⟫_ℂ := by
    have h := gammaIsometryF_adjoint m hm W.symm (fockBasisLim T) z
    rw [LinearIsometryEquiv.symm_symm] at h
    exact h.symm
  rw [← inner_fockBasisLim_apply T (gammaIsometryF m hm W z), h1,
    gammaIsometryF_fockBasisLim, lp.inner_eq_tsum]
  refine tsum_congr (fun S => ?_)
  rw [colVecF_apply, gammaKernelFermLim_symm, RCLike.inner_apply]
  simp only [RCLike.star_def]
  rw [Complex.conj_conj, mul_comm]

/-- The coordinate formula for the packaged unitary (T1). -/
theorem gammaFockF_coordinate (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (z : FermionicFockLim)
    (T : Finset ℕ) :
    (gammaFockF m hm W z) T
      = ∑' S, gammaKernelFermLim m hm W T S * z S := by
  rw [gammaFockF_apply]
  exact gammaIsometryF_coordinate m hm W z T

/-- The packaged operator maps kernel columns to kernel columns,
with the composed one-particle operator (T1). -/
theorem gammaIsometryF_colVecF (m : ℝ) (hm : 0 < m)
    (W₁ W₂ : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (S : Finset ℕ) :
    gammaIsometryF m hm W₂ (colVecF m hm W₁ S)
      = colVecF m hm (W₁.trans W₂) S := by
  apply Subtype.ext
  funext T
  calc (gammaIsometryF m hm W₂ (colVecF m hm W₁ S)) T
      = ∑' S', gammaKernelFermLim m hm W₂ T S'
          * gammaKernelFermLim m hm W₁ S' S := by
        rw [gammaIsometryF_coordinate]
        exact tsum_congr (fun S' => by rw [colVecF_apply m hm W₁ S S'])
    _ = gammaKernelFermLim m hm (W₁.trans W₂) T S :=
        gammaKernelFermLim_comp m hm W₁ W₂ T S
    _ = (colVecF m hm (W₁.trans W₂) S) T :=
        (colVecF_apply m hm (W₁.trans W₂) S T).symm

/-- The domain operator is the finite combination of columns at
the coordinates of `fermReprLim u` (T1). -/
theorem gammaDomF_apply (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (u : fermDomLim) :
    gammaDomF m hm W u
      = Finsupp.linearCombination ℂ (colVecF m hm W)
        (fermReprLim u) := rfl

/-- Composition on the domain (T1). -/
theorem gammaIsometryF_comp_apply (m : ℝ) (hm : 0 < m)
    (W₁ W₂ : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (u : fermDomLim) :
    gammaIsometryF m hm W₂ (gammaDomF m hm W₁ u)
      = gammaDomF m hm (W₁.trans W₂) u := by
  rw [gammaDomF_apply, gammaDomF_apply, linearCombination_eq_sum,
    map_sum, linearCombination_eq_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [map_smul, gammaIsometryF_colVecF]

/-- **Functor law on the whole space (T1),** by density from the
domain computation. -/
theorem gammaIsometryF_trans (m : ℝ) (hm : 0 < m)
    (W₁ W₂ : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (z : FermionicFockLim) :
    gammaIsometryF m hm (W₁.trans W₂) z
      = gammaIsometryF m hm W₂ (gammaIsometryF m hm W₁ z) := by
  have hclosed : IsClosed {z : FermionicFockLim |
      gammaIsometryF m hm (W₁.trans W₂) z
        = gammaIsometryF m hm W₂ (gammaIsometryF m hm W₁ z)} :=
    isClosed_eq (gammaIsometryF m hm (W₁.trans W₂)).continuous
      ((gammaIsometryF m hm W₂).continuous.comp
        (gammaIsometryF m hm W₁).continuous)
  have hsub : (fermDomLim : Set FermionicFockLim)
      ⊆ {z : FermionicFockLim |
        gammaIsometryF m hm (W₁.trans W₂) z
          = gammaIsometryF m hm W₂ (gammaIsometryF m hm W₁ z)} := by
    intro z hz
    show gammaIsometryF m hm (W₁.trans W₂) ((⟨z, hz⟩ : fermDomLim)
        : FermionicFockLim)
      = gammaIsometryF m hm W₂
          (gammaIsometryF m hm W₁ ((⟨z, hz⟩ : fermDomLim)
            : FermionicFockLim))
    rw [gammaIsometryF_apply_dom, gammaIsometryF_apply_dom]
    exact (gammaIsometryF_comp_apply m hm W₁ W₂ ⟨z, hz⟩).symm
  have hfin := closure_minimal hsub hclosed
  rw [dense_fermDomLim.closure_eq] at hfin
  exact hfin (Set.mem_univ z)

/-- **Functor law for the packaged unitary (T1):**
`Γ(W₁ ⋙ W₂) = Γ(W₁) ⋙ Γ(W₂)` in `LinearIsometryEquiv.trans`
order. -/
theorem gammaFockF_comp (m : ℝ) (hm : 0 < m)
    (W₁ W₂ : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) :
    gammaFockF m hm (W₁.trans W₂)
      = (gammaFockF m hm W₁).trans (gammaFockF m hm W₂) := by
  apply LinearIsometryEquiv.ext
  intro z
  rw [LinearIsometryEquiv.trans_apply, gammaFockF_apply, gammaFockF_apply,
    gammaFockF_apply]
  exact gammaIsometryF_trans m hm W₁ W₂ z

/-- The packaged operator of the identity is the identity (T1). -/
theorem gammaFockF_one (m : ℝ) (hm : 0 < m) :
    gammaFockF m hm (1 : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) = 1 := by
  apply LinearIsometryEquiv.ext
  intro z
  change gammaFockF m hm 1 z = z
  apply Subtype.ext
  funext T
  rw [gammaFockF_coordinate]
  rw [tsum_eq_single T (fun b hb => by
    rw [gammaKernelFermLim_one, if_neg (fun h => hb h.symm), zero_mul])]
  rw [gammaKernelFermLim_one]
  simp

/-- **Vacuum invariance (T1):** every one-particle unitary fixes
the fermionic vacuum. -/
theorem gammaFockF_vacuum (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) :
    gammaFockF m hm W fockVacLim = fockVacLim := by
  have hvac : ∀ T : Finset ℕ, (fockVacLim) T
      = if T = ∅ then (1 : ℂ) else 0 := by
    intro T
    rw [← inner_fockBasisLim_apply]
    show ⟪fockBasisLim T, fockBasisLim ∅⟫_ℂ
      = if T = ∅ then 1 else 0
    exact orthonormal_iff_ite.1 fockBasisLim_orthonormal T ∅
  apply Subtype.ext
  funext T
  rw [gammaFockF_coordinate, hvac T]
  rw [tsum_eq_single ∅ (fun S hS => by
    rw [hvac S, if_neg hS, mul_zero])]
  rw [gammaKernelFermLim_empty, hvac ∅, if_pos rfl, mul_one]

/-- **The packaged Poincaré representation, fermionic (T1):**
the second quantization of the corpus's one-particle mass-shell
representation `shellU1`. -/
noncomputable def gammaFockFU1 (m : ℝ) (hm : 0 < m) (g : RPoincare) :
    FermionicFockLim ≃ₗᵢ[ℂ] FermionicFockLim :=
  gammaFockF m hm (shellU1 m hm g)

/-- **Representation law (T1):** `Γ(U₁(g₁ * g₂)) = Γ(U₁ g₂) ⋙
Γ(U₁ g₁)` — the corrected order forced by the `trans`
convention (see the header). -/
theorem gammaFockFU1_mul (m : ℝ) (hm : 0 < m) (g₁ g₂ : RPoincare) :
    gammaFockFU1 m hm (g₁ * g₂)
      = (gammaFockFU1 m hm g₂).trans (gammaFockFU1 m hm g₁) := by
  unfold gammaFockFU1
  rw [shellU1_mul]
  exact gammaFockF_comp m hm _ _

/-- The packaged representation of the identity is the identity
(T1). -/
theorem gammaFockFU1_one (m : ℝ) (hm : 0 < m) :
    gammaFockFU1 m hm 1 = 1 := by
  unfold gammaFockFU1
  rw [shellU1_one]
  exact gammaFockF_one m hm

/-- The limit basis vectors as a Hilbert basis of the fermionic
Fock space (T1), assembled from the corpus's orthonormality and
the density of `fermDomLim`. -/
noncomputable def fermBasisLim :
    HilbertBasis (Finset ℕ) ℂ FermionicFockLim :=
  HilbertBasis.mk fockBasisLim_orthonormal
    (top_le_iff.mpr fermDomLim_topologicalClosure)

/-- The Hilbert basis is the basis-vector family (T1). -/
theorem fermBasisLim_coe : ⇑fermBasisLim = fockBasisLim :=
  HilbertBasis.coe_mk _ _

/-- The **closed `n`-particle sector** (T1, definition): the
vectors whose coordinates vanish off cardinality `n`. This is
the closure of `fermSectorLim n`, proved below. -/
def closedSectorF (n : ℕ) : Set FermionicFockLim :=
  {z | ∀ T, T.card ≠ n → z T = 0}

/-- The packaged operator preserves the closed sector (T1), by
the coordinate formula and the cardinality guard of the
kernel. -/
theorem gammaFockF_mem_closedSectorF (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (n : ℕ)
    {z : FermionicFockLim} (hz : z ∈ closedSectorF n) :
    gammaFockF m hm W z ∈ closedSectorF n := by
  intro T hT
  rw [gammaFockF_coordinate]
  refine (tsum_congr (fun S => ?_)).trans tsum_zero
  by_cases hTS : T.card = S.card
  · rw [hz S (fun h => hT (hTS.trans h)), mul_zero]
  · rw [gammaKernelFermLim_of_card_ne m hm W T S
      (fun hh => hTS hh.symm), zero_mul]

/-- The corpus sector is contained in the closed sector (T1), by
span induction. -/
theorem fermSectorLim_subset_closedSectorF (n : ℕ) :
    (fermSectorLim n : Set FermionicFockLim) ⊆ closedSectorF n := by
  intro z hz
  have hz' : z ∈ Submodule.span ℂ
      (fockBasisLim '' {S : Finset ℕ | S.card = n}) := hz
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz'
  · intro x hx
    obtain ⟨S, hS, rfl⟩ := hx
    intro T hT
    rw [← inner_fockBasisLim_apply]
    have h := orthonormal_iff_ite.1 fockBasisLim_orthonormal T S
    rwa [if_neg (fun h : T = S => hT ((h ▸ hS) : T.card = n))] at h
  · intro T _
    rfl
  · intro x y _ _ hx hy
    intro T hT
    have hxx : x T = 0 := hx T hT
    have hyy : y T = 0 := hy T hT
    have hxy : (x + y) T = x T + y T := Complex.ext rfl rfl
    rw [hxy, hxx, hyy, add_zero]
  · intro a x _ hx
    intro T hT
    have hxx : x T = 0 := hx T hT
    have hax : (a • x) T = a * x T := Complex.ext rfl rfl
    rw [hax, hxx, mul_zero]

/-- The closed sector is closed (T1): it is an intersection of
coordinate kernels. -/
theorem isClosed_closedSectorF (n : ℕ) :
    IsClosed (closedSectorF n) := by
  have heq : closedSectorF n
      = ⋂ T, ⋂ _ : T.card ≠ n,
          {z : FermionicFockLim | ⟪fockBasisLim T, z⟫_ℂ = 0} := by
    ext z
    simp [closedSectorF, inner_fockBasisLim_apply, Set.mem_iInter]
  rw [heq]
  exact isClosed_iInter (fun T => isClosed_iInter (fun _ =>
    IsClosed.preimage (continuous_const.inner continuous_id)
      isClosed_singleton))

/-- The closed sector is contained in the closure of the corpus
sector (T1): the Hilbert-basis partial sums of a vector in the
closed sector lie in `fermSectorLim n` and converge to it. -/
theorem closedSectorF_subset_closure (n : ℕ) :
    closedSectorF n ⊆ closure (fermSectorLim n : Set FermionicFockLim) := by
  intro z hz
  have hr : ∀ S, (fermBasisLim.repr z) S = z S := by
    intro S
    rw [HilbertBasis.repr_apply_apply, fermBasisLim_coe,
      inner_fockBasisLim_apply]
  have hsum : HasSum (fun S : Finset ℕ => z S • fockBasisLim S) z := by
    have h0 := fermBasisLim.hasSum_repr z
    simpa only [hr, fermBasisLim_coe] using h0
  rw [mem_closure_iff]
  intro o ho hzo
  have hev : ∀ᶠ F : Finset (Finset ℕ) in atTop,
      (∑ S ∈ F, z S • fockBasisLim S) ∈ o :=
    hsum.eventually (ho.mem_nhds hzo)
  obtain ⟨F₀, hF₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨∑ S ∈ F₀, z S • fockBasisLim S, hF₀ F₀ le_rfl, ?_⟩
  apply sum_mem
  intro S _
  by_cases hS : S.card = n
  · exact Submodule.smul_mem _ _ (fockBasisLim_mem_sector hS)
  · rw [hz S hS, zero_smul]
    exact Submodule.zero_mem _

/-- **Sector preservation (T1):** the packaged operator maps
the closure of the `n`-particle sector into itself. -/
theorem gammaFockF_mem_sectorClosure (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (n : ℕ)
    (z : FermionicFockLim)
    (hz : z ∈ (fermSectorLim n).topologicalClosure) :
    gammaFockF m hm W z ∈ (fermSectorLim n).topologicalClosure := by
  have hz2 : z ∈ closure (fermSectorLim n : Set FermionicFockLim) := by
    have h : z ∈ ((fermSectorLim n).topologicalClosure
      : Set FermionicFockLim) := hz
    rwa [Submodule.topologicalClosure_coe] at h
  have hzn : z ∈ closedSectorF n :=
    closure_minimal (fermSectorLim_subset_closedSectorF n)
      (isClosed_closedSectorF n) hz2
  have hfin : gammaFockF m hm W z
      ∈ ((fermSectorLim n).topologicalClosure
        : Set FermionicFockLim) := by
    rw [Submodule.topologicalClosure_coe]
    exact closedSectorF_subset_closure n
      (gammaFockF_mem_closedSectorF m hm W n hzn)
  exact hfin

/-- Entries are continuous along translations at the identity
(T1), transported from `shellU1_translation_tendsto`. -/
theorem UmatF_translation_tendsto (m : ℝ) (hm : 0 < m) (i j : ℕ) :
    Tendsto (fun a : Minkowski =>
        UmatF m hm (shellU1 m hm ⟨a, 1⟩) i j) (𝓝 0)
      (𝓝 (UmatF m hm 1 i j)) := by
  have h : Tendsto (fun a : Minkowski =>
        ⟪shellONB m hm i, shellU1 m hm ⟨a, 1⟩ (shellONB m hm j)⟫_ℂ)
        (𝓝 0) (𝓝 ⟪shellONB m hm i, shellONB m hm j⟫_ℂ) :=
    Filter.Tendsto.inner tendsto_const_nhds
      (shellU1_translation_tendsto m hm (shellONB m hm j))
  exact h

/-- The diagonal kernel is continuous at the identity along
translations, with value `1` (T1): at a fixed configuration the
kernel is a fixed finite determinant in the entries. -/
theorem gammaKernelFermLim_diag_translation_tendsto (m : ℝ) (hm : 0 < m)
    (S : Finset ℕ) :
    Tendsto (fun a : Minkowski =>
        gammaKernelFermLim m hm (shellU1 m hm ⟨a, 1⟩) S S)
      (𝓝 0) (𝓝 1) := by
  obtain ⟨d, S₀, hS⟩ := fermConfig_factor S
  have hval : minorDet d (UmatRectF m hm 1 d) S₀ S₀ = 1 := by
    rw [UmatRectF_one, minorDet_one, if_pos rfl]
  have heq : ∀ a : Minkowski,
      minorDet d (UmatRectF m hm (shellU1 m hm ⟨a, 1⟩) d) S₀ S₀
        = gammaKernelFermLim m hm (shellU1 m hm ⟨a, 1⟩) S S := by
    intro a
    rw [← hS]
    exact (gammaKernelFermLim_fermConfigEmbLim m hm _ d S₀ S₀).symm
  rw [← hval]
  refine Filter.Tendsto.congr (fun a => heq a) ?_
  exact minorDet_tendsto_of_tendsto _ _
    (fun i j => UmatF_translation_tendsto m hm i.val j.val) S₀ S₀

/-- The packaged action on a basis vector, along a translation
parameter (T1). -/
theorem gammaFockFU1_fockBasisLim (m : ℝ) (hm : 0 < m) (a : Minkowski)
    (S : Finset ℕ) :
    gammaFockFU1 m hm ⟨a, 1⟩ (fockBasisLim S)
      = colVecF m hm (shellU1 m hm ⟨a, 1⟩) S := by
  show gammaFockF m hm (shellU1 m hm ⟨a, 1⟩) (fockBasisLim S) = _
  rw [gammaFockF_apply]
  exact gammaIsometryF_fockBasisLim m hm _ S

/-- Basis vectors are strongly continuous under the packaged
translation action (T1): the squared distance is
`2 - 2 Re γ`. -/
theorem gammaFockFU1_basis_tendsto (m : ℝ) (hm : 0 < m)
    (S : Finset ℕ) :
    Tendsto (fun a : Minkowski =>
        ‖gammaFockFU1 m hm ⟨a, 1⟩ (fockBasisLim S) - fockBasisLim S‖)
      (𝓝 0) (𝓝 0) := by
  have hnorme : ‖fockBasisLim S‖ = 1 := fockBasisLim_orthonormal.1 S
  have hnorm : ∀ a : Minkowski,
      ‖gammaFockFU1 m hm ⟨a, 1⟩ (fockBasisLim S) - fockBasisLim S‖ ^ 2
        = 2 - 2 * (gammaKernelFermLim m hm (shellU1 m hm ⟨a, 1⟩)
            S S).re := by
    intro a
    rw [gammaFockFU1_fockBasisLim]
    have hnormV : ‖colVecF m hm (shellU1 m hm ⟨a, 1⟩) S‖ = 1 := by
      calc ‖colVecF m hm (shellU1 m hm ⟨a, 1⟩) S‖
          = ‖gammaIsometryF m hm (shellU1 m hm ⟨a, 1⟩)
              (fockBasisLim S)‖ := by
            rw [gammaIsometryF_fockBasisLim]
        _ = ‖fockBasisLim S‖ := LinearIsometry.norm_map _ _
        _ = 1 := hnorme
    calc ‖colVecF m hm (shellU1 m hm ⟨a, 1⟩) S - fockBasisLim S‖ ^ 2
        = ‖colVecF m hm (shellU1 m hm ⟨a, 1⟩) S‖ ^ 2
          - 2 * (⟪colVecF m hm (shellU1 m hm ⟨a, 1⟩) S,
              fockBasisLim S⟫_ℂ).re
          + ‖fockBasisLim S‖ ^ 2 := norm_sub_sq (𝕜 := ℂ) _ _
      _ = 1 - 2 * (star (gammaKernelFermLim m hm
              (shellU1 m hm ⟨a, 1⟩) S S)).re + 1 := by
          rw [inner_colVecF_fockBasisLim, hnormV, hnorme]
          ring
      _ = 2 - 2 * (gammaKernelFermLim m hm (shellU1 m hm ⟨a, 1⟩)
            S S).re := by
          have hre : ∀ z : ℂ, (star z).re = z.re := fun z => by simp
          rw [hre]
          ring
  have hsq : Tendsto (fun a : Minkowski =>
        ‖gammaFockFU1 m hm ⟨a, 1⟩ (fockBasisLim S) - fockBasisLim S‖ ^ 2)
      (𝓝 0) (𝓝 0) := by
    have hre' : Tendsto (fun a : Minkowski =>
        (gammaKernelFermLim m hm (shellU1 m hm ⟨a, 1⟩) S S).re)
          (𝓝 0) (𝓝 1) := by
      have h := (Complex.continuous_re.tendsto (1 : ℂ)).comp
        (gammaKernelFermLim_diag_translation_tendsto m hm S)
      exact h.congr (fun a => rfl)
    have key : Tendsto (fun a : Minkowski => 2 - 2
        * (gammaKernelFermLim m hm (shellU1 m hm ⟨a, 1⟩) S S).re)
          (𝓝 0) (𝓝 0) := by
      have h2 : Tendsto (fun a : Minkowski => (2 : ℝ) - 2
            * (gammaKernelFermLim m hm (shellU1 m hm ⟨a, 1⟩) S S).re)
          (𝓝 0) (𝓝 ((2 : ℝ) - 2 * 1)) :=
        tendsto_const_nhds.sub (tendsto_const_nhds.mul hre')
      have h3 : (2 : ℝ) - 2 * 1 = 0 := by norm_num
      rwa [h3] at h2
    exact Filter.Tendsto.congr (fun a => (hnorm a).symm) key
  have hfin := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  rw [Real.sqrt_zero] at hfin
  exact hfin.congr (fun a => Real.sqrt_sq (norm_nonneg _))

/-- Finite-particle vectors are strongly continuous under the
packaged translation action (T1): the distance is squeezed by a
finite sum of basis distances. -/
theorem gammaFockFU1_dom_tendsto (m : ℝ) (hm : 0 < m)
    (u : fermDomLim) :
    Tendsto (fun a : Minkowski =>
        ‖gammaFockFU1 m hm ⟨a, 1⟩ (u : FermionicFockLim)
          - (u : FermionicFockLim)‖) (𝓝 0) (𝓝 0) := by
  obtain ⟨φ, rfl⟩ : ∃ φ, fermEquivLim φ = u :=
    ⟨fermReprLim u, LinearEquiv.apply_symm_apply fermEquivLim u⟩
  refine squeeze_zero
    (g := fun a : Minkowski => ∑ S ∈ φ.support, ‖φ S‖
      * ‖gammaFockFU1 m hm ⟨a, 1⟩ (fockBasisLim S) - fockBasisLim S‖)
    (fun a => norm_nonneg _) (fun a => ?_) ?_
  · have hΓ : gammaFockFU1 m hm ⟨a, 1⟩
          ((fermEquivLim φ : fermDomLim) : FermionicFockLim)
        = Finsupp.linearCombination ℂ
            (colVecF m hm (shellU1 m hm ⟨a, 1⟩)) φ := by
      show gammaFockF m hm (shellU1 m hm ⟨a, 1⟩)
          ((fermEquivLim φ : fermDomLim) : FermionicFockLim) = _
      rw [gammaFockF_apply, gammaIsometryF_apply_dom,
        gammaDomF_fermEquivLim]
    have hu : ((fermEquivLim φ : fermDomLim) : FermionicFockLim)
        = Finsupp.linearCombination ℂ fockBasisLim φ :=
      fermEquivLim_coe φ
    rw [hΓ, hu, linearCombination_eq_sum, linearCombination_eq_sum,
      ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun S _ => ?_))
    rw [← smul_sub, norm_smul, gammaFockFU1_fockBasisLim]
  · have hfac : ∀ S ∈ φ.support, Tendsto (fun a : Minkowski =>
          ‖φ S‖ * ‖gammaFockFU1 m hm ⟨a, 1⟩ (fockBasisLim S)
            - fockBasisLim S‖) (𝓝 0) (𝓝 (‖φ S‖ * 0)) :=
      fun S _ => tendsto_const_nhds.mul
        (gammaFockFU1_basis_tendsto m hm S)
    have hsum := tendsto_finsetSum φ.support hfac
    simpa using hsum

/-- **Translation strong continuity of the packaged action
(T1):** for every vector `z` of the fermionic Fock space, the
packaged translation action is continuous at the identity —
transported from the discharged one-particle continuity through
the finite-particle density, with the uniform isometry bound. -/
theorem gammaFockFU1_translation_tendsto (m : ℝ) (hm : 0 < m)
    (z : FermionicFockLim) :
    Tendsto (fun a : Minkowski => gammaFockFU1 m hm ⟨a, 1⟩ z)
      (𝓝 0) (𝓝 z) := by
  rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  have hzmem : z ∈ closure (fermDomLim : Set FermionicFockLim) := by
    rw [dense_fermDomLim.closure_eq]
    exact Set.mem_univ z
  obtain ⟨u, hu, hdist⟩ :=
    (Metric.mem_closure_iff.1 hzmem) (ε / 3) (by linarith)
  have hev : ∀ᶠ a : Minkowski in 𝓝 0,
      ‖gammaFockFU1 m hm ⟨a, 1⟩ u - u‖ < ε / 3 := by
    have hT := gammaFockFU1_dom_tendsto m hm ⟨u, hu⟩
    have h2 := (Metric.tendsto_nhds.1 hT) (ε / 3) (by linarith)
    filter_upwards [h2] with a ha
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at ha
  filter_upwards [hev] with a ha
  have htri : ‖gammaFockFU1 m hm ⟨a, 1⟩ z - z‖
      ≤ ‖z - u‖ + ‖gammaFockFU1 m hm ⟨a, 1⟩ u - u‖ + ‖u - z‖ := by
    calc ‖gammaFockFU1 m hm ⟨a, 1⟩ z - z‖
        = ‖(gammaFockFU1 m hm ⟨a, 1⟩ z - gammaFockFU1 m hm ⟨a, 1⟩ u)
            + ((gammaFockFU1 m hm ⟨a, 1⟩ u - u) + (u - z))‖ := by
          congr 1
          abel
      _ ≤ ‖gammaFockFU1 m hm ⟨a, 1⟩ z - gammaFockFU1 m hm ⟨a, 1⟩ u‖
            + ‖gammaFockFU1 m hm ⟨a, 1⟩ u - u‖ + ‖u - z‖ := by
          have h1 := norm_add_le
            (gammaFockFU1 m hm ⟨a, 1⟩ z - gammaFockFU1 m hm ⟨a, 1⟩ u)
            ((gammaFockFU1 m hm ⟨a, 1⟩ u - u) + (u - z))
          have h2 := norm_add_le (gammaFockFU1 m hm ⟨a, 1⟩ u - u)
            (u - z)
          linarith
      _ = ‖z - u‖ + ‖gammaFockFU1 m hm ⟨a, 1⟩ u - u‖ + ‖u - z‖ := by
          congr 1
          rw [← map_sub, LinearIsometryEquiv.norm_map]
  have e1 : ‖z - u‖ = dist z u := (dist_eq_norm z u).symm
  have e2 : ‖u - z‖ = dist z u := by
    rw [norm_sub_rev]
    exact (dist_eq_norm z u).symm
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  rw [e1, e2] at htri
  linarith
