import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import ThetLogos.FermionicFock
import ThetLogos.SecondQuantDGamma

namespace ThetLogos

open scoped InnerProductSpace
open scoped Matrix

/-!
# ThetLogos.SecondQuantGamma — the Γ lift, unitarity, and the finite-mode
  quantum Poincaré implementation (Rung 9, Tasks 1 and 4)

The **Γ lift** (second quantization of a one-particle operator): for a matrix
`M` on the mode space `Fin d → ℂ`, `Γ(M)` acts on the fermionic Fock space of
Rung 8 (`FermionicFock.lean`) by the compound-matrix (minor) formula

    (Γ(M) x) T = ∑ S, minorDet M S T * x S,

where `minorDet M S T = det M[T-rows, S-cols]` (increasing order), `0` when
`|S| ≠ |T|`. This is `U e_{i₁} ∧ ⋯ ∧ U e_{iₙ}` in occupation coordinates.

**T1 proved here (the determinant core).**
- `minorDet_conjTranspose`, `minorDet_one` — the minor calculus.
- `det_mul_expansion` — expansion of `det (A * B)` over intermediate indices.
- `cauchy_binet_rect` — rectangular Cauchy–Binet over finset minors
  (Mathlib 2026 has no Cauchy–Binet; proved here from `Matrix.det_apply'`).
- `minorDet_mul` — `minorDet (M * N) S T = ∑ R, minorDet M R T * minorDet N S R`:
  the compound-matrix multiplicativity that makes `Γ` a functor.
-/

variable (d : ℕ)

/-- The `(T, S)` minor of `M`: rows indexed by `T`, columns by `S`, both in
    increasing order; `0` if the cardinalities differ. -/
noncomputable def minorDet (M : Matrix (Fin d) (Fin d) ℂ) (S T : Finset (Fin d)) : ℂ :=
  if h : S.card = T.card then
    Matrix.det (fun a b : Fin T.card => M (T.orderEmbOfFin rfl a) (S.orderEmbOfFin h b))
  else 0

/-- Minors vanish when the two finsets have different cardinalities (T1). -/
theorem minorDet_of_card_ne (M : Matrix (Fin d) (Fin d) ℂ) {S T : Finset (Fin d)}
    (h : S.card ≠ T.card) : minorDet d M S T = 0 := by
  simp only [minorDet, dif_neg h]

/-- Unfolding a minor at matching cardinalities (T1). -/
theorem minorDet_apply {S T : Finset (Fin d)} (h : S.card = T.card)
    (M : Matrix (Fin d) (Fin d) ℂ) :
    minorDet d M S T
      = Matrix.det (fun a b : Fin T.card =>
          M (T.orderEmbOfFin rfl a) (S.orderEmbOfFin h b)) := by
  simp only [minorDet, dif_pos h]

/-- Transport of `orderEmbOfFin` along a cardinality equality (T1 helper):
    the increasing enumeration depends only on the finset and the index value. -/
theorem orderEmbOfFin_cast {S : Finset (Fin d)} {n m : ℕ} (hm : S.card = m)
    (hn : S.card = n) (i : Fin m) :
    S.orderEmbOfFin hm i = S.orderEmbOfFin hn (Fin.cast (hm.symm.trans hn) i) := by
  rw [Finset.orderEmbOfFin_apply, Finset.orderEmbOfFin_apply]
  congr 1

/-- The minor of the conjugate transpose is the conjugate of the transposed
    minor (T1). -/
theorem minorDet_conjTranspose (M : Matrix (Fin d) (Fin d) ℂ)
    (S T : Finset (Fin d)) :
    minorDet d Mᴴ S T = star (minorDet d M T S) := by
  by_cases h : S.card = T.card
  · have hSside : ∀ b : Fin T.card, S.orderEmbOfFin h b
        = S.orderEmbOfFin rfl ((finCongr h).symm b) :=
      fun b => orderEmbOfFin_cast d h rfl b
    have hTside : ∀ a : Fin T.card, T.orderEmbOfFin h.symm ((finCongr h).symm a)
        = T.orderEmbOfFin rfl a := by
      intro a
      have hcast : Fin.cast (h.symm.symm.trans rfl) ((finCongr h).symm a) = a := by
        have e1 : (finCongr h).symm a = Fin.cast h.symm a := rfl
        rw [e1]
        apply Fin.ext
        simp [Fin.val_cast]
      have hstep := orderEmbOfFin_cast d h.symm rfl ((finCongr h).symm a)
      rwa [hcast] at hstep
    have key : Matrix.det (fun a b : Fin T.card =>
          Mᴴ (T.orderEmbOfFin rfl a) (S.orderEmbOfFin h b))
        = star (Matrix.det (fun a b : Fin S.card =>
            M (S.orderEmbOfFin rfl a) (T.orderEmbOfFin h.symm b))) := by
      have hmat : (fun a b : Fin T.card =>
            Mᴴ (T.orderEmbOfFin rfl a) (S.orderEmbOfFin h b))
          = Matrix.submatrix ((fun x y : Fin S.card =>
              star (M (S.orderEmbOfFin rfl y) (T.orderEmbOfFin h.symm x))) :
              Matrix (Fin S.card) (Fin S.card) ℂ)
              (finCongr h).symm (finCongr h).symm := by
        ext a b
        show Mᴴ (T.orderEmbOfFin rfl a) (S.orderEmbOfFin h b)
          = star (M (S.orderEmbOfFin rfl ((finCongr h).symm b))
              (T.orderEmbOfFin h.symm ((finCongr h).symm a)))
        rw [Matrix.conjTranspose_apply, hSside b, hTside a]
      have hWY : (fun x y : Fin S.card =>
            star (M (S.orderEmbOfFin rfl y) (T.orderEmbOfFin h.symm x)))
          = (fun a b : Fin S.card =>
              M (S.orderEmbOfFin rfl a) (T.orderEmbOfFin h.symm b))ᴴ :=
        rfl
      calc Matrix.det (fun a b : Fin T.card =>
              Mᴴ (T.orderEmbOfFin rfl a) (S.orderEmbOfFin h b))
          = Matrix.det (Matrix.submatrix ((fun x y : Fin S.card =>
                star (M (S.orderEmbOfFin rfl y) (T.orderEmbOfFin h.symm x))) :
                Matrix (Fin S.card) (Fin S.card) ℂ)
                (finCongr h).symm (finCongr h).symm) :=
            congrArg Matrix.det hmat
        _ = Matrix.det ((fun x y : Fin S.card =>
                star (M (S.orderEmbOfFin rfl y) (T.orderEmbOfFin h.symm x))) :
                Matrix (Fin S.card) (Fin S.card) ℂ) :=
            Matrix.det_submatrix_equiv_self (finCongr h).symm _
        _ = Matrix.det ((fun a b : Fin S.card =>
                M (S.orderEmbOfFin rfl a) (T.orderEmbOfFin h.symm b))ᴴ) :=
            congrArg Matrix.det hWY
        _ = star (Matrix.det (fun a b : Fin S.card =>
                M (S.orderEmbOfFin rfl a) (T.orderEmbOfFin h.symm b))) :=
            Matrix.det_conjTranspose _
    rw [minorDet_apply d h Mᴴ, minorDet_apply d h.symm M, key]
  · rw [minorDet_of_card_ne d Mᴴ h, minorDet_of_card_ne d M (Ne.symm h), star_zero]

/-- The minors of the identity matrix are the Kronecker delta on finsets (T1). -/
theorem minorDet_one (S T : Finset (Fin d)) :
    minorDet d (1 : Matrix (Fin d) (Fin d) ℂ) S T = if S = T then 1 else 0 := by
  by_cases hST : S = T
  · rw [if_pos hST]
    subst hST
    rw [minorDet_apply d rfl (1 : Matrix (Fin d) (Fin d) ℂ)]
    have hmat : (fun a b : Fin S.card =>
          (1 : Matrix (Fin d) (Fin d) ℂ) (S.orderEmbOfFin rfl a) (S.orderEmbOfFin rfl b))
        = (1 : Matrix (Fin S.card) (Fin S.card) ℂ) := by
      ext a b
      simp only [Matrix.one_apply, OrderEmbedding.eq_iff_eq]
    rw [hmat, Matrix.det_one]
  · rw [if_neg hST]
    by_cases hcard : S.card = T.card
    · obtain ⟨i, hiT, hiS⟩ : ∃ i, i ∈ T ∧ i ∉ S := by
        by_contra hc
        push Not at hc
        exact hST (Finset.eq_of_subset_of_card_le hc (le_of_eq hcard)).symm
      obtain ⟨a₀, ha₀⟩ : ∃ a₀ : Fin T.card, T.orderEmbOfFin rfl a₀ = i := by
        refine ⟨(T.orderIsoOfFin rfl).symm ⟨i, hiT⟩, ?_⟩
        rw [← Finset.coe_orderIsoOfFin_apply, (T.orderIsoOfFin rfl).apply_symm_apply]
      rw [minorDet_apply d hcard (1 : Matrix (Fin d) (Fin d) ℂ)]
      apply Matrix.det_eq_zero_of_row_eq_zero a₀
      intro b
      show (1 : Matrix (Fin d) (Fin d) ℂ) (T.orderEmbOfFin rfl a₀)
        (S.orderEmbOfFin hcard b) = 0
      rw [ha₀]
      exact Matrix.one_apply_ne (fun hcon => hiS
        (hcon.symm ▸ Finset.orderEmbOfFin_mem S hcard b))
    · exact minorDet_of_card_ne d _ hcard

/-! ### The determinant core: expansion, Cauchy–Binet, minor multiplicativity -/

/-- Expansion of `det (A * B)` over intermediate indices (T1):
    `det (A * B) = ∑ f, (∏ i, B (f i) i) * det (a ↦ A a (f ·))`,
    from `Matrix.det_apply'` and the product-of-sums expansion. -/
theorem det_mul_expansion {n : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (B : Matrix (Fin d) (Fin n) ℂ) :
    (A * B).det
      = ∑ f : Fin n → Fin d, (∏ i, B (f i) i) * Matrix.det (fun a b => A a (f b)) := by
  have prodsum : ∀ σ : Equiv.Perm (Fin n),
      (∏ i, ∑ k : Fin d, A (σ i) k * B k i)
        = ∑ f : Fin n → Fin d, ∏ i, A (σ i) (f i) * B (f i) i := by
    intro σ
    rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset (Fin d)))
      (fun i k => A (σ i) k * B k i), Fintype.piFinset_univ]
  have per_f : ∀ f : Fin n → Fin d,
      (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ)
          * ((∏ i, A (σ i) (f i)) * (∏ i, B (f i) i)))
        = (∏ i, B (f i) i) * Matrix.det (fun a b => A a (f b)) := by
    intro f
    rw [Matrix.det_apply' (fun a b => A a (f b)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  calc (A * B).det
      = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ)
          * ∏ i, (A * B) (σ i) i := Matrix.det_apply' _
    _ = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ)
          * ∏ i, ∑ k : Fin d, A (σ i) k * B k i := by
          apply Finset.sum_congr rfl
          intro σ _
          exact congrArg _ (Finset.prod_congr rfl
            (fun i _ => Matrix.mul_apply))
    _ = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ)
          * ∑ f : Fin n → Fin d, ∏ i, A (σ i) (f i) * B (f i) i := by
          apply Finset.sum_congr rfl
          intro σ _
          exact congrArg _ (prodsum σ)
    _ = ∑ σ : Equiv.Perm (Fin n), ∑ f : Fin n → Fin d,
          ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A (σ i) (f i) * B (f i) i := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [Finset.mul_sum]
    _ = ∑ f : Fin n → Fin d, ∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A (σ i) (f i) * B (f i) i :=
        Finset.sum_comm
    _ = ∑ f : Fin n → Fin d, ∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : ℂ)
            * ((∏ i, A (σ i) (f i)) * (∏ i, B (f i) i)) := by
          apply Finset.sum_congr rfl
          intro f _
          apply Finset.sum_congr rfl
          intro σ _
          rw [Finset.prod_mul_distrib]
    _ = ∑ f : Fin n → Fin d, (∏ i, B (f i) i) * Matrix.det (fun a b => A a (f b)) :=
        Finset.sum_congr rfl (fun f _ => per_f f)

/-- The row-minor of a rectangular matrix `B : Matrix (Fin d) (Fin n) ℂ` at `R`:
    `det` of the submatrix with rows `R` (increasing) and all columns; `0` if
    `R.card ≠ n`. -/
noncomputable def minorRows {n : ℕ} (B : Matrix (Fin d) (Fin n) ℂ)
    (R : Finset (Fin d)) : ℂ :=
  if h : R.card = n then
    Matrix.det (fun a b : Fin n => B (R.orderEmbOfFin h a) b)
  else 0

/-- The column-minor of a rectangular matrix `A : Matrix (Fin n) (Fin d) ℂ`
    at `R`: `det` of the submatrix with all rows and columns `R` (increasing);
    `0` if `R.card ≠ n`. -/
noncomputable def minorCols {n : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (R : Finset (Fin d)) : ℂ :=
  if h : R.card = n then
    Matrix.det (fun a b : Fin n => A a (R.orderEmbOfFin h b))
  else 0

/-- The Cauchy–Binet summand: for `R` with `R.card = n` and a permutation `τ`,
    the `τ`-term of the row-minor expansion times the column-minor determinant. -/
noncomputable def binetTerm {n : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (B : Matrix (Fin d) (Fin n) ℂ) (R : Finset (Fin d)) (hR : R.card = n)
    (τ : Equiv.Perm (Fin n)) : ℂ :=
  (∏ i, B (R.orderEmbOfFin hR (τ i)) i)
    * (((Equiv.Perm.sign τ : ℤ) : ℂ)
        * Matrix.det (fun a b => A a (R.orderEmbOfFin hR b)))

/-- An injective index map uses exactly `n` distinct values (T1). -/
theorem image_card_of_injective {n : ℕ} (f : Fin n → Fin d) (hf : Function.Injective f) :
    (Finset.image f Finset.univ).card = n := by
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]

/-- **The ordering permutation (T1 construction).** For an injective index map
    `f : Fin n → Fin d`, the unique permutation `π` with
    `f = (image f).orderEmbOfFin ∘ π`: `π` sends a position to the position of
    its value in the increasing enumeration of the image. -/
noncomputable def orderingPerm {n : ℕ} (f : Fin n → Fin d) (hf : Function.Injective f) :
    Equiv.Perm (Fin n) :=
  (Equiv.ofBijective
      (fun i => ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
      ⟨fun i₁ i₂ h => hf (congrArg Subtype.val h),
       fun ⟨x, hx⟩ => by
         obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hx
         exact ⟨i, Subtype.ext hi⟩⟩).trans
    ((Finset.image f Finset.univ).orderIsoOfFin
      (image_card_of_injective d f hf)).symm.toEquiv

/-- The ordering permutation unfolds to the inverse enumeration (T1). -/
theorem orderingPerm_apply {n : ℕ} (f : Fin n → Fin d) (hf : Function.Injective f)
    (i : Fin n) :
    orderingPerm d f hf i
      = ((Finset.image f Finset.univ).orderIsoOfFin
          (image_card_of_injective d f hf)).symm
            ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩ :=
  rfl

/-- `orderEmbOfFin` does not depend on the cardinality proof (T1). -/
theorem orderEmbOfFin_proof_irrel {S : Finset (Fin d)} {k : ℕ}
    (h₁ h₂ : S.card = k) : S.orderEmbOfFin h₁ = S.orderEmbOfFin h₂ := by
  apply DFunLike.ext
  intro i
  rw [Finset.orderEmbOfFin_apply]

/-- The defining property of the ordering permutation (T1):
    enumerating the image of `f` at position `π i` returns `f i`. -/
theorem image_orderEmbOfFin_orderingPerm {n : ℕ} (f : Fin n → Fin d)
    (hf : Function.Injective f) (i : Fin n) :
    (Finset.image f Finset.univ).orderEmbOfFin (image_card_of_injective d f hf)
        (orderingPerm d f hf i) = f i := by
  rw [orderingPerm_apply, ← Finset.coe_orderIsoOfFin_apply,
    OrderIso.apply_symm_apply]

/-- The ordering-permutation identity over an arbitrary name for the image
    (T1): if `R` is the image of `f`, enumerating `R` at `π i` returns `f i`. -/
theorem orderingPerm_key {n : ℕ} (f : Fin n → Fin d) (hf : Function.Injective f)
    (R : Finset (Fin d)) (hR : R.card = n) (hRf : R = Finset.image f Finset.univ)
    (i : Fin n) :
    R.orderEmbOfFin hR (orderingPerm d f hf i) = f i := by
  subst hRf
  rw [orderEmbOfFin_proof_irrel d hR (image_card_of_injective d f hf)]
  exact image_orderEmbOfFin_orderingPerm d f hf i

/-- **Rectangular Cauchy–Binet (T1).**
    `det (A * B) = ∑ R, minorCols A R * minorRows B R`.
    Not in Mathlib (2026); proved here from `det_mul_expansion` by grouping
    the intermediate index functions `f : Fin n → Fin d` according to their
    image `R` and the ordering permutation `τ` (non-injective `f` contribute
    `0` by the column-duplication vanishing of `det`). -/
theorem cauchy_binet_rect {n : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (B : Matrix (Fin d) (Fin n) ℂ) :
    (A * B).det = ∑ R : Finset (Fin d), minorCols d A R * minorRows d B R := by
  classical
  have hinj : ∀ (f : Fin n → Fin d),
      f ∈ Finset.univ.filter (fun f : Fin n → Fin d => Function.Injective f) →
      Function.Injective f :=
    fun f hf => (Finset.mem_filter.mp hf).2
  -- Non-injective intermediate maps contribute zero.
  have hG0 : ∀ f : Fin n → Fin d, ¬ Function.Injective f →
      (∏ i, B (f i) i) * Matrix.det (fun a b => A a (f b)) = 0 := by
    intro f hf
    obtain ⟨i, j, hij, hfeq⟩ : ∃ i j, i ≠ j ∧ f i = f j := by
      by_contra hc
      push Not at hc
      exact hf (fun a b hab => by
        by_contra hne
        exact hc a b hne hab)
    have hdet : Matrix.det (fun a b => A a (f b)) = 0 :=
      Matrix.det_zero_of_column_eq hij (fun k => by
        show A k (f i) = A k (f j)
        exact congrArg (A k) hfeq)
    rw [hdet, mul_zero]
  -- Minors vanish off the diagonal cardinality.
  have vanish : ∀ R : Finset (Fin d), R.card ≠ n →
      minorCols d A R * minorRows d B R = 0 := by
    intro R hR
    simp only [minorCols, dif_neg hR, zero_mul]
  -- The subtype universe of `n`-subsets is the subtype finset.
  have huniv : (Finset.univ : Finset {R : Finset (Fin d) // R.card = n})
      = Finset.subtype (fun R : Finset (Fin d) => R.card = n) Finset.univ := by
    ext ⟨R, hR⟩
    simp
  calc (A * B).det
      = ∑ f : Fin n → Fin d, (∏ i, B (f i) i) * Matrix.det (fun a b => A a (f b)) :=
        det_mul_expansion d A B
    _ = ∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin d => Function.Injective f),
          (∏ i, B (f i) i) * Matrix.det (fun a b => A a (f b)) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro f _
          by_cases hf : Function.Injective f
          · rw [if_pos hf]
          · rw [if_neg hf, hG0 f hf]
    _ = ∑ x ∈ (Finset.univ : Finset {R : Finset (Fin d) // R.card = n}).sigma
          (fun _ => (Finset.univ : Finset (Equiv.Perm (Fin n)))),
          binetTerm d A B x.1.1 x.1.2 x.2 := by
          -- The bijection: injective `f` ↦ (image of `f`, ordering permutation).
          apply Finset.sum_bij
            (fun f hf => ⟨⟨Finset.image f Finset.univ,
              image_card_of_injective d f (hinj f hf)⟩,
              orderingPerm d f (hinj f hf)⟩)
          · intro f _
            exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
          · intro f₁ hf₁ f₂ hf₂ hij
            obtain ⟨hsub, hπ⟩ := Sigma.ext_iff.mp hij
            have himg : Finset.image f₁ Finset.univ
                = Finset.image f₂ Finset.univ := congrArg Subtype.val hsub
            have hπ' : orderingPerm d f₁ (hinj f₁ hf₁)
                = orderingPerm d f₂ (hinj f₂ hf₂) := eq_of_heq hπ
            funext i
            have hcp₂ : (Finset.image f₁ Finset.univ).card = n :=
              himg.symm ▸ image_card_of_injective d f₂ (hinj f₂ hf₂)
            have k₁ := orderingPerm_key d f₁ (hinj f₁ hf₁)
              (Finset.image f₁ Finset.univ)
              (image_card_of_injective d f₁ (hinj f₁ hf₁)) rfl i
            have k₂ := orderingPerm_key d f₂ (hinj f₂ hf₂)
              (Finset.image f₁ Finset.univ) hcp₂ himg i
            calc f₁ i
                = (Finset.image f₁ Finset.univ).orderEmbOfFin
                    (image_card_of_injective d f₁ (hinj f₁ hf₁))
                    (orderingPerm d f₁ (hinj f₁ hf₁) i) := k₁.symm
              _ = (Finset.image f₁ Finset.univ).orderEmbOfFin
                    (image_card_of_injective d f₁ (hinj f₁ hf₁))
                    (orderingPerm d f₂ (hinj f₂ hf₂) i) := by rw [hπ']
              _ = f₂ i := (DFunLike.congr_fun (orderEmbOfFin_proof_irrel d
                    (image_card_of_injective d f₁ (hinj f₁ hf₁)) hcp₂)
                    (orderingPerm d f₂ (hinj f₂ hf₂) i)).trans k₂
          · intro b _
            obtain ⟨⟨R, hR⟩, τ⟩ := b
            refine ⟨fun a => R.orderEmbOfFin hR (τ a),
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
            · exact (R.orderEmbOfFin hR).strictMono.injective.comp
                (Equiv.injective τ)
            · have himg₀ : Finset.image (fun a => R.orderEmbOfFin hR (τ a))
                  Finset.univ = R := by
                have h1 : (fun a => R.orderEmbOfFin hR (τ a))
                    = (R.orderEmbOfFin hR) ∘ τ := rfl
                rw [h1, ← Finset.image_image]
                have h2 : Finset.image τ Finset.univ = Finset.univ := by
                  apply Finset.eq_univ_of_forall
                  intro x
                  obtain ⟨y, hy⟩ := Equiv.surjective τ x
                  exact Finset.mem_image.mpr ⟨y, Finset.mem_univ y, hy⟩
                rw [h2, Finset.image_orderEmbOfFin_univ]
              have hπ₀ : orderingPerm d (fun a => R.orderEmbOfFin hR (τ a))
                  ((R.orderEmbOfFin hR).strictMono.injective.comp
                    (Equiv.injective τ)) = τ := by
                apply Equiv.ext
                intro a
                apply (R.orderEmbOfFin hR).strictMono.injective
                rw [orderingPerm_key d _ _ R hR himg₀.symm a]
              exact Sigma.ext_iff.mpr ⟨Subtype.ext himg₀, heq_of_eq hπ₀⟩
          · intro f hf
            have hinjf := hinj f hf
            show (∏ i, B (f i) i) * Matrix.det (fun a b => A a (f b))
              = (∏ i, B ((Finset.image f Finset.univ).orderEmbOfFin
                    (image_card_of_injective d f hinjf)
                    (orderingPerm d f hinjf i)) i)
                * (((Equiv.Perm.sign (orderingPerm d f hinjf) : ℤ) : ℂ)
                    * Matrix.det (fun a b => A a ((Finset.image f Finset.univ).orderEmbOfFin (image_card_of_injective d f hinjf) b)))
            congr 1
            · exact Finset.prod_congr rfl (fun i _ => by
                rw [image_orderEmbOfFin_orderingPerm])
            · have hmat : (fun a b => A a (f b))
                  = Matrix.submatrix (fun a b => A a
                      ((Finset.image f Finset.univ).orderEmbOfFin
                        (image_card_of_injective d f hinjf) b)) id
                      (orderingPerm d f hinjf) := by
                ext a b
                show A a (f b) = A a ((Finset.image f Finset.univ).orderEmbOfFin
                    (image_card_of_injective d f hinjf)
                    (orderingPerm d f hinjf b))
                rw [image_orderEmbOfFin_orderingPerm]
              calc Matrix.det (fun a b => A a (f b))
                  = (Matrix.submatrix (fun a b => A a
                        ((Finset.image f Finset.univ).orderEmbOfFin
                          (image_card_of_injective d f hinjf) b)) id
                        (orderingPerm d f hinjf)).det :=
                    congrArg Matrix.det hmat
                _ = ((Equiv.Perm.sign (orderingPerm d f hinjf) : ℤ) : ℂ)
                      * Matrix.det (fun a b => A a ((Finset.image f Finset.univ).orderEmbOfFin (image_card_of_injective d f hinjf) b)) :=
                    Matrix.det_permute' _ _
    _ = ∑ R' : {R : Finset (Fin d) // R.card = n},
          ∑ τ : Equiv.Perm (Fin n), binetTerm d A B R'.1 R'.2 τ :=
by
          rw [Finset.sum_sigma']
    _ = ∑ R' : {R : Finset (Fin d) // R.card = n},
          minorCols d A R'.1 * minorRows d B R'.1 := by
          apply Finset.sum_congr rfl
          intro R' _
          have hR : R'.1.card = n := R'.2
          simp only [minorCols, minorRows, dif_pos hR]
          rw [Matrix.det_apply' (fun a b : Fin n => B (R'.1.orderEmbOfFin hR a) b),
            Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro τ _
          show (∏ i, B (R'.1.orderEmbOfFin hR (τ i)) i)
              * (((Equiv.Perm.sign τ : ℤ) : ℂ)
                  * Matrix.det (fun a b => A a (R'.1.orderEmbOfFin hR b)))
            = Matrix.det (fun a b => A a (R'.1.orderEmbOfFin hR b))
              * (((Equiv.Perm.sign τ : ℤ) : ℂ)
                  * ∏ a, B (R'.1.orderEmbOfFin hR (τ a)) a)
          ring
    _ = ∑ R ∈ Finset.univ.filter (fun R : Finset (Fin d) => R.card = n),
          minorCols d A R * minorRows d B R := by
          rw [huniv]
          exact Finset.sum_subtype_eq_sum_filter
            (fun R => minorCols d A R * minorRows d B R)
    _ = ∑ R : Finset (Fin d), minorCols d A R * minorRows d B R := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro R _
          by_cases hR : R.card = n
          · rw [if_pos hR]
          · rw [if_neg hR, vanish R hR]

/-- **Minor multiplicativity (T1):** `minorDet (M * N) S T
    = ∑ R, minorDet M R T * minorDet N S R` — the compound-matrix identity,
    via rectangular Cauchy–Binet applied to the two rectangular blocks. -/
theorem minorDet_mul (M N : Matrix (Fin d) (Fin d) ℂ) (S T : Finset (Fin d)) :
    minorDet d (M * N) S T
      = ∑ R : Finset (Fin d), minorDet d M R T * minorDet d N S R := by
  by_cases hST : S.card = T.card
  · set A' : Matrix (Fin T.card) (Fin d) ℂ :=
      fun a k => M (T.orderEmbOfFin rfl a) k with hA'
    set B' : Matrix (Fin d) (Fin T.card) ℂ :=
      fun k b => N k (S.orderEmbOfFin hST b) with hB'
    have hminor : minorDet d (M * N) S T = Matrix.det (A' * B') := by
      rw [minorDet_apply d hST (M * N)]
      congr 1
    rw [hminor, cauchy_binet_rect]
    apply Finset.sum_congr rfl
    intro R _
    by_cases hR : R.card = T.card
    · have hA : minorCols d A' R = minorDet d M R T := by
        have e1 : minorCols d A' R
            = Matrix.det (fun a b : Fin T.card =>
                M (T.orderEmbOfFin rfl a) (R.orderEmbOfFin hR b)) := by
          simp only [minorCols, dif_pos hR, hA']
        rw [e1]
        exact (minorDet_apply d hR M).symm
      have hB : minorRows d B' R = minorDet d N S R := by
        have hSR : S.card = R.card := hST.trans hR.symm
        have hRside : ∀ a : Fin T.card, R.orderEmbOfFin hR a
            = R.orderEmbOfFin rfl ((finCongr hR).symm a) :=
          fun a => orderEmbOfFin_cast d hR rfl a
        have hSside : ∀ b : Fin T.card,
            S.orderEmbOfFin hSR ((finCongr hR).symm b)
              = S.orderEmbOfFin hST b := by
          intro b
          have hcast : Fin.cast (hSR.symm.trans hST) ((finCongr hR).symm b)
              = b := by
            have e1 : (finCongr hR).symm b = Fin.cast hR.symm b := rfl
            rw [e1]
            apply Fin.ext
            simp [Fin.val_cast]
          have hstep := orderEmbOfFin_cast d hSR hST ((finCongr hR).symm b)
          rwa [hcast] at hstep
        have hmat : (fun a b : Fin T.card =>
              N (R.orderEmbOfFin hR a) (S.orderEmbOfFin hST b))
            = Matrix.submatrix ((fun x y : Fin R.card =>
                N (R.orderEmbOfFin rfl x) (S.orderEmbOfFin hSR y)) :
                Matrix (Fin R.card) (Fin R.card) ℂ)
                (finCongr hR).symm (finCongr hR).symm := by
          ext a b
          show N (R.orderEmbOfFin hR a) (S.orderEmbOfFin hST b)
            = N (R.orderEmbOfFin rfl ((finCongr hR).symm a))
                (S.orderEmbOfFin hSR ((finCongr hR).symm b))
          rw [hRside a, hSside b]
        have e1 : minorRows d B' R
            = Matrix.det (fun a b : Fin T.card =>
                N (R.orderEmbOfFin hR a) (S.orderEmbOfFin hST b)) := by
          simp only [minorRows, dif_pos hR, hB']
        rw [e1]
        calc Matrix.det (fun a b : Fin T.card =>
                N (R.orderEmbOfFin hR a) (S.orderEmbOfFin hST b))
            = Matrix.det (Matrix.submatrix ((fun x y : Fin R.card =>
                  N (R.orderEmbOfFin rfl x) (S.orderEmbOfFin hSR y)) :
                  Matrix (Fin R.card) (Fin R.card) ℂ)
                  (finCongr hR).symm (finCongr hR).symm) :=
              congrArg Matrix.det hmat
          _ = Matrix.det (fun x y : Fin R.card =>
                N (R.orderEmbOfFin rfl x) (S.orderEmbOfFin hSR y)) :=
              Matrix.det_submatrix_equiv_self (finCongr hR).symm _
          _ = minorDet d N S R := (minorDet_apply d hSR N).symm
      rw [hA, hB]
    · have h1 : minorCols d A' R = 0 := by
        simp only [minorCols, dif_neg hR]
      have h2 : minorDet d M R T = 0 := minorDet_of_card_ne d M hR
      rw [h1, h2, zero_mul, zero_mul]
  · have hL : minorDet d (M * N) S T = 0 := minorDet_of_card_ne d _ hST
    rw [hL]
    symm
    apply Finset.sum_eq_zero
    intro R _
    by_cases hR : R.card = T.card
    · have hne : S.card ≠ R.card := by omega
      rw [minorDet_of_card_ne d N hne, mul_zero]
    · rw [minorDet_of_card_ne d M hR, zero_mul]

/-! ### The Γ operator -/

/-- **The Pi-side Γ operator (T1 construction).** `(Γ(M) x) T = ∑ S,
    minorDet M S T * x S`: the compound-matrix action on occupation
    coordinates — the `(S, T)` matrix element of `Γ(M)` is the minor of
    `M` on rows `T`, columns `S`. -/
noncomputable def gammaPi (M : Matrix (Fin d) (Fin d) ℂ) :
    (Π S : Finset (Fin d), ℂ) →ₗ[ℂ] (Π S : Finset (Fin d), ℂ) where
  toFun x T := ∑ S, minorDet d M S T * x S
  map_add' x y := by
    funext T
    show (∑ S, minorDet d M S T * (x + y) S)
      = (∑ S, minorDet d M S T * x S) + ∑ S, minorDet d M S T * y S
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S _
    rw [Pi.add_apply, mul_add]
  map_smul' c x := by
    funext T
    show (∑ S, minorDet d M S T * (c • x) S)
      = c • ∑ S, minorDet d M S T * x S
    rw [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    rw [Pi.smul_apply, smul_eq_mul]
    ring

/-- **The Γ lift (T1 construction).** Second quantization of a one-particle
    matrix `M`, transported from the Pi side via the Rung-8 Fock
    equivalence, exactly as the creation/annihilation operators were. -/
noncomputable def gamma (M : Matrix (Fin d) (Fin d) ℂ) :
    Module.End ℂ (FermionicFock d) :=
  (fockEquiv d).conj (gammaPi d M)

/-- Coordinates of `Γ(M)` (T1): `(Γ(M) x) T = ∑ S, minorDet M S T * x S`. -/
@[simp] theorem gamma_apply (M : Matrix (Fin d) (Fin d) ℂ) (x : FermionicFock d)
    (T : Finset (Fin d)) :
    ((gamma d M) x).ofLp T = ∑ S, minorDet d M S T * x.ofLp S := rfl

/-- `Γ(1) = 1` (T1). -/
theorem gamma_one : gamma d (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro T
  rw [gamma_apply, Module.End.one_apply, Finset.sum_eq_single T]
  · rw [minorDet_one, if_pos rfl, one_mul]
  · intro S _ hST
    rw [minorDet_one, if_neg hST, zero_mul]
  · intro hT
    exact absurd (Finset.mem_univ T) hT

/-- `Γ(M * N) = Γ(M) * Γ(N)` (T1) — the homomorphism property, from minor
    multiplicativity and the exchange of sums. -/
theorem gamma_mul (M N : Matrix (Fin d) (Fin d) ℂ) :
    gamma d (M * N) = (gamma d M) * (gamma d N) := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro T
  rw [gamma_apply, Module.End.mul_apply]
  simp only [gamma_apply, minorDet_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro R _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- `Γ(Mᴴ)` is the adjoint of `Γ(M)` (T1), in the inner-product form used
    throughout the ladder: `⟪Γ(M) x, y⟫ = ⟪x, Γ(Mᴴ) y⟫`. -/
theorem gamma_adjoint (M : Matrix (Fin d) (Fin d) ℂ) (x y : FermionicFock d) :
    ⟪(gamma d M) x, y⟫_ℂ = ⟪x, (gamma d Mᴴ) y⟫_ℂ := by
  have step : ∀ T : Finset (Fin d),
      y.ofLp T * star (∑ S, minorDet d M S T * x.ofLp S)
        = ∑ S, (minorDet d Mᴴ T S * star (x.ofLp S)) * y.ofLp T := by
    intro T
    rw [star_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    rw [star_mul, ← minorDet_conjTranspose]
    ring
  simp only [PiLp.inner_apply, RCLike.inner_apply, gamma_apply,
    starRingEnd_apply]
  calc (∑ T, y.ofLp T * star (∑ S, minorDet d M S T * x.ofLp S))
      = ∑ T, ∑ S, (minorDet d Mᴴ T S * star (x.ofLp S)) * y.ofLp T :=
        Finset.sum_congr rfl (fun T _ => step T)
    _ = ∑ S, ∑ T, (minorDet d Mᴴ T S * star (x.ofLp S)) * y.ofLp T :=
        Finset.sum_comm
    _ = ∑ T, (∑ S, minorDet d Mᴴ S T * y.ofLp S) * star (x.ofLp T) := by
        apply Finset.sum_congr rfl
        intro S _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro T _
        ring

/-- `Γ(M)` fixes the vacuum (T1). -/
theorem gamma_vacuum (M : Matrix (Fin d) (Fin d) ℂ) :
    (gamma d M) (fockVac d) = fockVac d := by
  apply PiLp.ext
  intro T
  rw [gamma_apply]
  have hvac : ∀ S : Finset (Fin d), (fockVac d).ofLp S
      = if S = ∅ then 1 else 0 := by
    intro S
    show (fockBasis d ∅).ofLp S = if S = ∅ then 1 else 0
    rw [fockBasis_ofLp]
  have hsum : (∑ S, minorDet d M S T * (fockVac d).ofLp S)
      = minorDet d M ∅ T := by
    rw [Finset.sum_eq_single ∅]
    · rw [hvac ∅, if_pos rfl, mul_one]
    · intro S _ hS
      rw [hvac S, if_neg hS, mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ ∅) hmem
  rw [hsum, hvac T]
  by_cases hT : T = ∅
  · subst hT
    rw [if_pos rfl, minorDet_apply d rfl M]
    exact Matrix.det_fin_zero
  · rw [if_neg hT]
    apply minorDet_of_card_ne
    rw [Finset.card_empty]
    exact (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT)).ne

/-- Sector membership is coordinate support (T1): `x ∈ sector d n` iff the
    coordinates of `x` vanish off the finsets of cardinality `n`. -/
theorem mem_sector_iff (n : ℕ) (x : FermionicFock d) :
    x ∈ sector d n ↔ ∀ T, T.card ≠ n → x.ofLp T = 0 := by
  constructor
  · intro hx
    have hle : sector d n ≤
        { carrier := {x : FermionicFock d | ∀ T, T.card ≠ n → x.ofLp T = 0}
          add_mem' := by
            intro a b ha hb T hT
            simp only [Set.mem_setOf_eq] at ha hb
            show (a + b).ofLp T = 0
            rw [PiLp.add_apply, ha T hT, hb T hT, add_zero]
          zero_mem' := by
            intro T _
            show (0 : FermionicFock d).ofLp T = 0
            simp
          smul_mem' := by
            intro c a ha T hT
            simp only [Set.mem_setOf_eq] at ha
            show (c • a).ofLp T = 0
            rw [PiLp.smul_apply, ha T hT, smul_zero] } :=
      Submodule.span_le.mpr (by
        intro a ha
        obtain ⟨S, hS, rfl⟩ := ha
        intro T hT
        rw [fockBasis_ofLp]
        exact if_neg (fun hTS => hT ((congrArg Finset.card hTS).trans hS)))
    exact hle hx
  · intro hx
    have hexp : x = ∑ T ∈ Finset.univ.filter (fun T => T.card = n),
        x.ofLp T • fockBasis d T := by
      calc x = ∑ T, x.ofLp T • fockBasis d T := fock_expand d x
        _ = ∑ T ∈ Finset.univ.filter (fun T => T.card = n),
            x.ofLp T • fockBasis d T := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro T _ hT
          rw [hx T (fun h => hT (Finset.mem_filter.mpr
            ⟨Finset.mem_univ T, h⟩)), zero_smul]
    rw [hexp]
    apply Submodule.sum_mem
    intro T hT
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨T, (Finset.mem_filter.mp hT).2, rfl⟩)

/-- `Γ(M)` preserves every n-particle sector (T1). -/
theorem gamma_sector (M : Matrix (Fin d) (Fin d) ℂ) {n : ℕ}
    {x : FermionicFock d} (hx : x ∈ sector d n) :
    (gamma d M) x ∈ sector d n := by
  rw [mem_sector_iff] at hx ⊢
  intro T hT
  rw [gamma_apply]
  apply Finset.sum_eq_zero
  intro S _
  by_cases hS : S.card = n
  · rw [minorDet_of_card_ne d M (by omega : S.card ≠ T.card), zero_mul]
  · rw [hx S hS, mul_zero]

/-- For `Mᴴ * M = 1`, the Γ-lift is a left inverse pair (T1):
    `Γ(Mᴴ) * Γ(M) = 1` as operators. -/
theorem gamma_comp_self (M : Matrix (Fin d) (Fin d) ℂ) (hM : Mᴴ * M = 1) :
    (gamma d Mᴴ) * (gamma d M) = 1 := by
  rw [← gamma_mul, hM, gamma_one]

/-- For `M * Mᴴ = 1`, the Γ-lift is a right inverse pair (T1):
    `Γ(M) * Γ(Mᴴ) = 1` as operators. -/
theorem gamma_self_comp (M : Matrix (Fin d) (Fin d) ℂ) (hM : M * Mᴴ = 1) :
    (gamma d M) * (gamma d Mᴴ) = 1 := by
  rw [← gamma_mul, hM, gamma_one]

/-- **Unitarity of the Γ lift (T1):** for `Mᴴ * M = 1`, `Γ(M)` preserves
    the Fock inner product. With `gamma_comp_self`/`gamma_self_comp` this
    is the operator-level statement that `Γ(M)` is unitary for unitary
    `M`. -/
theorem gamma_inner (M : Matrix (Fin d) (Fin d) ℂ) (hM : Mᴴ * M = 1)
    (x y : FermionicFock d) :
    ⟪(gamma d M) x, (gamma d M) y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [gamma_adjoint]
  have h : (gamma d Mᴴ) ((gamma d M) y) = y := by
    calc (gamma d Mᴴ) ((gamma d M) y)
        = ((gamma d Mᴴ) * (gamma d M)) y := (Module.End.mul_apply _ _ _).symm
      _ = y := by rw [gamma_comp_self d M hM, Module.End.one_apply]
  rw [h]

/-- Minors of a diagonal matrix (T1): the Kronecker delta on finsets
    against the product of the selected diagonal entries. -/
theorem minorDet_diagonal (v : Fin d → ℂ) (S T : Finset (Fin d)) :
    minorDet d (Matrix.diagonal v) S T
      = if T = S then ∏ i ∈ S, v i else 0 := by
  by_cases hST : T = S
  · subst hST
    rw [if_pos rfl, minorDet_apply d rfl]
    have hmat : (fun a b : Fin T.card =>
          (Matrix.diagonal v) (T.orderEmbOfFin rfl a) (T.orderEmbOfFin rfl b))
        = Matrix.diagonal (fun a => v (T.orderEmbOfFin rfl a)) := by
      ext a b
      simp only [Matrix.diagonal_apply, OrderEmbedding.eq_iff_eq]
    have hprod : (∏ a : Fin T.card, v (T.orderEmbOfFin rfl a))
        = ∏ i ∈ T, v i := by
      conv_rhs => rw [← Finset.image_orderEmbOfFin_univ T rfl]
      exact (Finset.prod_image (f := v)
        ((T.orderEmbOfFin rfl).strictMono.injective.injOn)).symm
    rw [hmat, Matrix.det_diagonal]
    exact hprod
  · rw [if_neg hST]
    by_cases hcard : S.card = T.card
    · obtain ⟨i, hiT, hiS⟩ : ∃ i, i ∈ T ∧ i ∉ S := by
        by_contra hc
        push Not at hc
        exact hST (Finset.eq_of_subset_of_card_le (fun i hi => hc i hi)
          (le_of_eq hcard))
      obtain ⟨a₀, ha₀⟩ : ∃ a₀ : Fin T.card, T.orderEmbOfFin rfl a₀ = i := by
        refine ⟨(T.orderIsoOfFin rfl).symm ⟨i, hiT⟩, ?_⟩
        rw [← Finset.coe_orderIsoOfFin_apply, (T.orderIsoOfFin rfl).apply_symm_apply]
      rw [minorDet_apply d hcard (Matrix.diagonal v)]
      apply Matrix.det_eq_zero_of_row_eq_zero a₀
      intro b
      show (Matrix.diagonal v) (T.orderEmbOfFin rfl a₀)
        (S.orderEmbOfFin hcard b) = 0
      rw [ha₀]
      exact Matrix.diagonal_apply_ne v (fun hcon => hiS
        (hcon.symm ▸ Finset.orderEmbOfFin_mem S hcard b))
    · exact minorDet_of_card_ne d _ hcard

/-- `Γ` of a diagonal matrix acts on a basis vector by the product of the
    selected phases (T1) — the concrete form used by the lattice
    translation representation. -/
theorem gamma_diagonal_basis (v : Fin d → ℂ) (S : Finset (Fin d)) :
    (gamma d (Matrix.diagonal v)) (fockBasis d S)
      = (∏ i ∈ S, v i) • fockBasis d S := by
  apply PiLp.ext
  intro T
  rw [gamma_apply]
  have hsum : (∑ S', minorDet d (Matrix.diagonal v) S' T * (fockBasis d S).ofLp S')
      = minorDet d (Matrix.diagonal v) S T := by
    rw [Finset.sum_eq_single S]
    · rw [fockBasis_ofLp, if_pos rfl, mul_one]
    · intro S' _ hS'
      rw [fockBasis_ofLp, if_neg hS', mul_zero]
    · intro hS
      exact absurd (Finset.mem_univ S) hS
  rw [hsum, minorDet_diagonal]
  by_cases hTS : T = S
  · subst hTS
    rw [if_pos rfl, PiLp.smul_apply, fockBasis_ofLp, if_pos rfl, smul_eq_mul,
      mul_one]
  · rw [if_neg hTS, PiLp.smul_apply, fockBasis_ofLp, if_neg hTS, smul_eq_mul,
      mul_zero]


/-! ### The representation lift and the lattice translation representation -/

/-- **The Γ representation lift (T1).** Let `ρ : G → Matrix` be a
    one-particle unitary representation of a group `G`: a homomorphism
    with `ρ g` unitary for every `g`. Then `Γ ∘ ρ` is a unitary
    representation of `G` on Fock space: it respects multiplication and
    the identity, fixes the vacuum, preserves every sector, and preserves
    the inner product. This discharges, at finite modes, the *form* of
    the Rung-6 `SecondQuantization_window`. -/
theorem gamma_rep (G : Type*) [Group G] (ρ : G → Matrix (Fin d) (Fin d) ℂ)
    (hρ1 : ρ 1 = 1) (hρ_mul : ∀ g h, ρ (g * h) = ρ g * ρ h)
    (hρU : ∀ g, (ρ g)ᴴ * ρ g = 1 ∧ ρ g * (ρ g)ᴴ = 1) :
    (∀ g h, gamma d (ρ (g * h)) = (gamma d (ρ g)) * (gamma d (ρ h)))
      ∧ gamma d (ρ 1) = 1
      ∧ (∀ g, (gamma d (ρ g)) (fockVac d) = fockVac d)
      ∧ (∀ g n, ∀ x ∈ sector d n, (gamma d (ρ g)) x ∈ sector d n)
      ∧ (∀ g x y, ⟪(gamma d (ρ g)) x, (gamma d (ρ g)) y⟫_ℂ = ⟪x, y⟫_ℂ) :=
  ⟨fun g h => by rw [hρ_mul, gamma_mul],
   by rw [hρ1, gamma_one],
   fun g => gamma_vacuum d _,
   fun g n x hx => gamma_sector d _ hx,
   fun g x y => gamma_inner d _ (hρU g).1 x y⟩

/-- The conjugate transpose of a diagonal matrix is the diagonal of the
    entrywise conjugates (T1). -/
theorem diagonal_conjTranspose (v : Fin d → ℂ) :
    (Matrix.diagonal v)ᴴ = Matrix.diagonal (fun i => star (v i)) := by
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

/-- The lattice-translation angle: mode `j` rotates by `2π k j / d` under
    `k` steps of the lattice translation group `Multiplicative ℤ`. -/
noncomputable def latticeAngle (k : Multiplicative ℤ) (j : Fin d) : ℝ :=
  2 * Real.pi * (((Multiplicative.toAdd k : ℤ) : ℝ) * (j.val : ℝ)) / (d : ℝ)

/-- The lattice-translation phase `exp(2πi k j / d)` of mode `j`. -/
noncomputable def latticePhase (k : Multiplicative ℤ) (j : Fin d) : ℂ :=
  Complex.exp ((latticeAngle d k j : ℂ) * Complex.I)

/-- The one-particle lattice translation representation: the diagonal
    matrix of translation phases. -/
noncomputable def latticeRho (k : Multiplicative ℤ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun j => latticePhase d k j)

/-- Each translation phase has unit modulus, conjugate-first form (T1). -/
theorem latticePhase_star_mul (k : Multiplicative ℤ) (j : Fin d) :
    star (latticePhase d k j) * latticePhase d k j = 1 := by
  have hstar : star (latticePhase d k j)
      = Complex.exp (-((latticeAngle d k j : ℂ) * Complex.I)) := by
    show star (Complex.exp ((latticeAngle d k j : ℂ) * Complex.I)) = _
    rw [show star (Complex.exp ((latticeAngle d k j : ℂ) * Complex.I))
        = (starRingEnd ℂ) (Complex.exp ((latticeAngle d k j : ℂ) * Complex.I))
        from rfl, ← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hph : latticePhase d k j
      = Complex.exp ((latticeAngle d k j : ℂ) * Complex.I) := rfl
  rw [hstar, hph, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

/-- Each translation phase has unit modulus, phase-first form (T1). -/
theorem latticePhase_mul_star (k : Multiplicative ℤ) (j : Fin d) :
    latticePhase d k j * star (latticePhase d k j) = 1 := by
  rw [mul_comm]
  exact latticePhase_star_mul d k j

/-- The lattice translation matrices are unitary (T1). -/
theorem latticeRho_unitary (k : Multiplicative ℤ) :
    (latticeRho d k)ᴴ * latticeRho d k = 1
      ∧ latticeRho d k * (latticeRho d k)ᴴ = 1 := by
  constructor
  · show (Matrix.diagonal (fun j => latticePhase d k j))ᴴ
        * Matrix.diagonal (fun j => latticePhase d k j) = 1
    rw [diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext j
    exact latticePhase_star_mul d k j
  · show Matrix.diagonal (fun j => latticePhase d k j)
        * (Matrix.diagonal (fun j => latticePhase d k j))ᴴ = 1
    rw [diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext j
    exact latticePhase_mul_star d k j

/-- The zero lattice translation is the identity matrix (T1). -/
theorem latticeRho_one : latticeRho d 1 = 1 := by
  show Matrix.diagonal (fun j => latticePhase d 1 j) = 1
  rw [← Matrix.diagonal_one]
  congr 1
  funext j
  simp [latticePhase, latticeAngle, toAdd_one]

/-- The lattice translation matrices form a representation of
    `Multiplicative ℤ` (T1): phases add under lattice-step composition. -/
theorem latticeRho_mul (k₁ k₂ : Multiplicative ℤ) :
    latticeRho d (k₁ * k₂) = latticeRho d k₁ * latticeRho d k₂ := by
  show Matrix.diagonal (fun j => latticePhase d (k₁ * k₂) j)
    = Matrix.diagonal (fun j => latticePhase d k₁ j)
      * Matrix.diagonal (fun j => latticePhase d k₂ j)
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  have hθ : latticeAngle d (k₁ * k₂) j
      = latticeAngle d k₁ j + latticeAngle d k₂ j := by
    show 2 * Real.pi * (((Multiplicative.toAdd (k₁ * k₂) : ℤ) : ℝ)
          * (j.val : ℝ)) / (d : ℝ)
      = 2 * Real.pi * (((Multiplicative.toAdd k₁ : ℤ) : ℝ) * (j.val : ℝ))
          / (d : ℝ)
        + 2 * Real.pi * (((Multiplicative.toAdd k₂ : ℤ) : ℝ) * (j.val : ℝ))
          / (d : ℝ)
    rw [toAdd_mul]
    push_cast
    ring
  show Complex.exp ((latticeAngle d (k₁ * k₂) j : ℂ) * Complex.I)
    = Complex.exp ((latticeAngle d k₁ j : ℂ) * Complex.I)
      * Complex.exp ((latticeAngle d k₂ j : ℂ) * Complex.I)
  rw [hθ, Complex.ofReal_add, add_mul, Complex.exp_add]

/-- **The finite-mode quantum translation representation (T1).** The
    lattice translations `Multiplicative ℤ` act on the fermionic Fock
    space through the Γ lift of the diagonal phase representation: a
    unitary representation fixing the vacuum and preserving every
    n-particle sector. This is the honestly-liftable part of the Rung-6
    Poincaré structure at finite modes: the translation subgroup that
    preserves the finite mode set `Fin d`, acting by phases. Boosts,
    rotations mixing infinitely many modes, and the mass-shell
    representation itself do not preserve any finite mode set and remain
    priced T5 (see the Rung 9 dossier). -/
theorem lattice_translation_rep :
    (∀ g h : Multiplicative ℤ,
        gamma d (latticeRho d (g * h))
          = (gamma d (latticeRho d g)) * (gamma d (latticeRho d h)))
      ∧ gamma d (latticeRho d 1) = 1
      ∧ (∀ g : Multiplicative ℤ,
          (gamma d (latticeRho d g)) (fockVac d) = fockVac d)
      ∧ (∀ (g : Multiplicative ℤ) (n : ℕ) (x : FermionicFock d),
          x ∈ sector d n → (gamma d (latticeRho d g)) x ∈ sector d n)
      ∧ (∀ (g : Multiplicative ℤ) (x y : FermionicFock d),
          ⟪(gamma d (latticeRho d g)) x, (gamma d (latticeRho d g)) y⟫_ℂ
            = ⟪x, y⟫_ℂ) :=
  gamma_rep d (Multiplicative ℤ) (latticeRho d) (latticeRho_one d)
    (latticeRho_mul d) (latticeRho_unitary d)


-- Axiom audit (Rung 9): the headline results depend only on the three
-- standard axioms.
#print axioms minorDet_mul
#print axioms gamma_one
#print axioms gamma_mul
#print axioms gamma_adjoint
#print axioms gamma_inner
#print axioms gamma_vacuum
#print axioms gamma_sector
#print axioms lattice_translation_rep


end ThetLogos
