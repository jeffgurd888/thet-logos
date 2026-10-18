import ThetLogos.FockPackaging
import ThetLogos.BosonicLimitOps

/-!
# ThetLogos.FockPackagingBos — FOCK PACKAGING, bosonic half
# (Rung 7 remainder, packaging half; gauntlet 2026-10-17: STANDS at M,
# concrete ONB port only; Kill K4 stands — no SymmetricAlgebra route)

The one-particle unitary representation `shellU1` of `RPoincare` on
the mass-shell space `shellLp m hm` (module `FockPackaging`, steps
(i)–(ii)) is ported through second quantization Γ to a unitary
representation `gammaFockU1` of the same group on the bosonic limit
Fock space `BosonicFockLim` of `BosonicLimit`.

## Route

Everything is built on the corpus's own Γ kernel, widened from finite
matrices to the concrete `ℕ`-indexed ONB `shellONB m hm`:

* `perMinorLimOf A c' c` — the permanent minor of an abstract
  one-particle matrix `A : ℕ → ℕ → ℂ` between limit configurations,
  over the sorted enumerations `enumLim` of the configurations
  (the limit analog of `perMinor`); `gammaKernelLimOf` divides by the
  normalization factors `normFactorLim`.
* The three kernel facts are proved by **finite-level reduction plus
  Parseval limits**: at any finite level `e` the kernel restricts to
  the corpus's rectangular kernel `gammaKernelRect` of the compressed
  matrix (`perMinorLimOf_configEmbLim`); the corpus's permanent
  Cauchy–Binet (`perMinor_mul`, ported here to rectangular matrices
  as `perMinorRect_mul`) evaluates the finite partial sums; the
  entries of the compressed Gram/product matrices converge by
  one-particle Parseval (`HilbertBasis.tsum_inner_mul_inner`); and an
  exhaustion over levels gives the `tsum` identities:
  - `gammaKernelLimOf_one` — the identity kernel is `δ` (fiber
    counting, via `permanent_indicator` transported to `ℕ`);
  - `gammaKernelLim_column_orthonormal` — exact column
    orthonormality of the kernel of a unitary (the ℓ² identity);
  - `gammaKernelLim_comp` — the functor (convolution) law.
* `gammaFock W` is assembled from the densely defined isometry
  `gammaDomLim W` on `DomLim` by continuous extension, the inverse
  supplied by `gammaFock W.symm` through the adjoint identity on the
  dense domain. Capstones: the group law `gammaFockU1_mul` in the
  same `trans` order as `shellU1_mul`, `gammaFockU1_one`, vacuum
  preservation, sector preservation, and strong continuity of the
  translation subgroup transported from
  `shellU1_translation_tendsto` by the dense-domain ε/3 argument.

## Fences (in writing, per the commission)

* The group is `RPoincare`, the group of the corpus's shell
  representation — not an unrestricted Poincaré group.
* **Lorentz strong continuity is NOT part of this brick.** Only the
  translation subgroup's strong continuity is transported; the
  Lorentz half remains its own priced line item.
* The fermionic half lives in `FockPackagingFerm.lean`: the two
  statistic stacks cannot be co-imported in one module
  (`numberOp`/`numberOp_basis` collide between `FermionicFock` and
  `BosonicAssembly`).
* T1 throughout: free theory, no interaction, no continuum limit, no
  Yang–Mills claim.
-/

namespace ThetLogos

open scoped InnerProductSpace
open scoped Matrix
open Filter Topology

/-! ## 1. Limit enumerations, fiber counts, and `configOfLim` -/

/-- The sorted list of occupied positions of a limit configuration:
the limit analog of `enumList`. -/
noncomputable def enumLimList (c : ConfigLim) : List ℕ :=
  (Finsupp.toMultiset c).sort (· ≤ ·)

/-- The enumeration list of a limit configuration has length
`totLim c`. -/
theorem enumLimList_length (c : ConfigLim) : (enumLimList c).length = totLim c := by
  have hcard : Multiset.card (Finsupp.toMultiset c) = c.sum (fun _ => id) :=
    Finsupp.card_toMultiset c
  rw [enumLimList, Multiset.length_sort]
  exact hcard

/-- The sorted enumeration of the occupied positions of a limit
configuration: position `k` holds the mode sitting there, repetitions
included. The limit analog of `configEnum`. -/
noncomputable def enumLim (c : ConfigLim) (k : Fin (totLim c)) : ℕ :=
  (enumLimList c).get ⟨k.val, by rw [enumLimList_length]; exact k.isLt⟩

/-- `enumLim` is the `get` of `enumLimList` (definitional). -/
theorem enumLim_apply (c : ConfigLim) (k : Fin (totLim c)) :
    enumLim c k
      = (enumLimList c).get ⟨k.val, by rw [enumLimList_length]; exact k.isLt⟩ :=
  rfl

/-- Two `get` terms over equal lists at indices of equal value agree. -/
theorem get_congr_list {α : Type*} {l₁ l₂ : List α} (h : l₁ = l₂)
    {i₁ : Fin l₁.length} {i₂ : Fin l₂.length} (hi : i₁.val = i₂.val) :
    l₁.get i₁ = l₂.get i₂ := by
  cases h
  congr 1
  exact Fin.ext hi

/-- `enumLim` depends only on the value of the position index. -/
theorem enumLim_congr_val {c : ConfigLim} {k₁ k₂ : Fin (totLim c)}
    (h : k₁.val = k₂.val) : enumLim c k₁ = enumLim c k₂ := by
  rw [show k₁ = k₂ from Fin.ext h]

/-- Position counting for a list of naturals (the `positions_count`
argument, at target `ℕ`): the number of positions of `l` holding the
value `i` is the multiset count of `i` in `l`. -/
theorem positions_count_lim (l : List ℕ) (i : ℕ) :
    (Finset.univ.filter (fun k : Fin l.length => l.get k = i)).card
      = Multiset.count i ↑l := by
  induction l with
  | nil =>
      simp
  | cons a l ih =>
      rw [Finset.card_filter]
      show (∑ k : Fin (l.length + 1), if (a :: l).get k = i then (1 : ℕ) else 0)
        = Multiset.count i ↑(a :: l)
      rw [Fin.sum_univ_succ]
      have hhead : (a :: l).get (0 : Fin (l.length + 1)) = a := rfl
      have hsucc : ∀ k : Fin l.length,
          (a :: l).get (Fin.succ k) = l.get k := fun k => rfl
      rw [hhead]
      simp only [hsucc]
      rw [← Finset.card_filter, ih]
      show (if a = i then (1 : ℕ) else 0) + Multiset.count i ↑l
        = Multiset.count i (a ::ₘ (↑l : Multiset ℕ))
      rw [Multiset.count_cons]
      by_cases h : a = i
      · rw [if_pos h, if_pos h.symm]; omega
      · rw [if_neg h, if_neg (fun hi => h hi.symm)]; omega

/-- The fiber count of a position function `ι : Fin n → ℕ`: the number
of positions holding mode `i`. Limit analog of `fiberCount`. -/
def fiberCountLim {n : ℕ} (ι : Fin n → ℕ) (i : ℕ) : ℕ :=
  (Finset.univ.filter (fun a => ι a = i)).card

/-- **Fiber cardinality of the limit enumeration (T1):** mode `i`
occupies exactly `c i` positions in `enumLim c`. -/
theorem fiberCountLim_enumLim (c : ConfigLim) (i : ℕ) :
    fiberCountLim (enumLim c) i = c i := by
  have hstep : fiberCountLim (enumLim c) i
      = (Finset.univ.filter
          (fun k : Fin (enumLimList c).length => (enumLimList c).get k = i)).card := by
    unfold fiberCountLim
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    apply Fintype.card_congr
    apply Equiv.subtypeEquiv (finCongr (enumLimList_length c)).symm
    intro k
    have hidx : (finCongr (enumLimList_length c)).symm k
        = ⟨k.val, by rw [enumLimList_length]; exact k.isLt⟩ := Fin.ext rfl
    rw [enumLim_apply, hidx]
  rw [hstep, positions_count_lim]
  have h2 : Multiset.count i ↑((Finsupp.toMultiset c).sort (· ≤ ·)) = c i := by
    rw [Multiset.sort_eq, Finsupp.count_toMultiset]
  exact h2

/-- The limit configuration of a position function: its occupation
counts. Limit analog of `configOf`. -/
noncomputable def configOfLim {n : ℕ} (f : Fin n → ℕ) : ConfigLim :=
  ∑ a, Finsupp.single (f a) 1

/-- `configOfLim` reads off fiber counts (T1). -/
theorem configOfLim_apply {n : ℕ} (f : Fin n → ℕ) (i : ℕ) :
    configOfLim f i = fiberCountLim f i := by
  unfold configOfLim fiberCountLim
  rw [Finsupp.finsetSum_apply, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finsupp.single_apply]

/-- The total count of `configOfLim f` is the number of positions. -/
theorem totLim_configOfLim {n : ℕ} (f : Fin n → ℕ) :
    totLim (configOfLim f) = n := by
  have hsupp : (configOfLim f).support ⊆ Finset.univ.image f := by
    intro i hi
    rw [Finsupp.mem_support_iff, configOfLim_apply] at hi
    have hpos : 0 < (Finset.univ.filter (fun a => f a = i)).card :=
      Nat.pos_of_ne_zero hi
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at ha
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha.2⟩
  calc totLim (configOfLim f)
      = ∑ i ∈ Finset.univ.image f, configOfLim f i :=
        Finsupp.sum_of_support_subset (configOfLim f) hsupp _ (fun _ _ => rfl)
    _ = ∑ i ∈ Finset.univ.image f, fiberCountLim f i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [configOfLim_apply]
    _ = ∑ i ∈ Finset.univ.image f,
          (Finset.univ.filter (fun a => f a = i)).card := rfl
    _ = Finset.univ.card :=
        (Finset.card_eq_sum_card_fiberwise
          (fun a _ => Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)).symm
    _ = n := by rw [Finset.card_univ, Fintype.card_fin]

/-- `configOfLim` of the enumeration of `c` is `c` itself (T1). -/
theorem configOfLim_enumLim (c : ConfigLim) :
    configOfLim (enumLim c) = c := by
  ext i
  rw [configOfLim_apply, fiberCountLim_enumLim]

/-! ## 2. The limit kernel over an abstract one-particle matrix -/

/-- The limit permanent minor of an abstract one-particle matrix
`A : ℕ → ℕ → ℂ` between limit configurations `c'` (rows) and `c`
(columns): the permanent of the `tot × tot` matrix of entries between
the sorted enumerations; `0` when the total counts differ. -/
noncomputable def perMinorLimOf (A : ℕ → ℕ → ℂ) (c' c : ConfigLim) : ℂ :=
  if h : totLim c' = totLim c then
    Matrix.permanent (fun a b : Fin (totLim c) =>
      A (enumLim c' (finCongr h.symm a)) (enumLim c b))
  else 0

/-- Limit permanent minors vanish between different total counts. -/
theorem perMinorLimOf_of_tot_ne (A : ℕ → ℕ → ℂ) (c' c : ConfigLim)
    (h : totLim c' ≠ totLim c) : perMinorLimOf A c' c = 0 :=
  dif_neg h

/-- The limit normalization factor `√(∏ i, (c i)!)` (product over the
support of `c`). -/
noncomputable def normFactorLim (c : ConfigLim) : ℝ :=
  Real.sqrt (c.prod (fun _ n => (Nat.factorial n : ℝ)))

/-- The limit Γ kernel of an abstract one-particle matrix: permanent
minor over the product of normalization factors. -/
noncomputable def gammaKernelLimOf (A : ℕ → ℕ → ℂ) (c' c : ConfigLim) : ℂ :=
  perMinorLimOf A c' c / ((normFactorLim c * normFactorLim c' : ℝ) : ℂ)

/-- The limit normalization factor is positive (T1). -/
theorem normFactorLim_pos (c : ConfigLim) : 0 < normFactorLim c := by
  unfold normFactorLim
  apply Real.sqrt_pos_of_pos
  rw [Finsupp.prod]
  apply Finset.prod_pos
  intro i _
  exact_mod_cast Nat.factorial_pos (c i)

/-- The squared limit normalization is the factorial weight (T1). -/
theorem normFactorLim_sq (c : ConfigLim) :
    ((normFactorLim c : ℂ)) ^ 2
      = c.prod (fun _ n => ((Nat.factorial n : ℕ) : ℂ)) := by
  have hP : (0 : ℝ) ≤ c.prod (fun _ n => (Nat.factorial n : ℝ)) := by
    rw [Finsupp.prod]
    apply Finset.prod_nonneg
    intro i _
    exact Nat.cast_nonneg _
  unfold normFactorLim
  rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt hP]
  rw [Finsupp.prod, Finsupp.prod]
  push_cast
  rfl

/-- The conjugate-transpose law for limit permanent minors (T1):
the minor of the conjugate-transpose matrix is the conjugate of the
transposed minor. Port of `perMinor_conjTranspose`. -/
theorem perMinorLimOf_conjTranspose (A : ℕ → ℕ → ℂ) (c' c : ConfigLim) :
    perMinorLimOf (fun i j => star (A j i)) c' c
      = star (perMinorLimOf A c c') := by
  by_cases htot : totLim c' = totLim c
  · have e1 : perMinorLimOf (fun i j => star (A j i)) c' c = Matrix.permanent
        (fun a b : Fin (totLim c) => star (A (enumLim c b)
          (enumLim c' (finCongr htot.symm a)))) := by
      unfold perMinorLimOf
      rw [dif_pos htot]
    have e2 : perMinorLimOf A c c' = Matrix.permanent
        (fun a b : Fin (totLim c') => A (enumLim c (finCongr htot a))
          (enumLim c' b)) := by
      unfold perMinorLimOf
      rw [dif_pos htot.symm]
    rw [e1, e2, permanent_star (fun a b : Fin (totLim c) => A (enumLim c b)
      (enumLim c' (finCongr htot.symm a)))]
    congr 1
    calc Matrix.permanent (fun a b : Fin (totLim c) => A (enumLim c b)
          (enumLim c' (finCongr htot.symm a)))
        = Matrix.permanent (Matrix.submatrix
            (fun a b : Fin (totLim c') => A (enumLim c (finCongr htot a))
              (enumLim c' b))ᵀ
            (finCongr htot.symm) (finCongr htot.symm)) := rfl
      _ = Matrix.permanent (fun a b : Fin (totLim c') =>
            A (enumLim c (finCongr htot a)) (enumLim c' b))ᵀ :=
          permanent_submatrix_equiv _ _
      _ = Matrix.permanent (fun a b : Fin (totLim c') =>
            A (enumLim c (finCongr htot a)) (enumLim c' b)) :=
          Matrix.permanent_transpose _
  · rw [perMinorLimOf_of_tot_ne _ c' c htot,
      perMinorLimOf_of_tot_ne _ c c' (fun h => htot h.symm), star_zero]

/-- The conjugate-transpose law for the limit kernel (T1). -/
theorem gammaKernelLimOf_conjTranspose (A : ℕ → ℕ → ℂ) (c' c : ConfigLim) :
    gammaKernelLimOf (fun i j => star (A j i)) c' c
      = star (gammaKernelLimOf A c c') := by
  unfold gammaKernelLimOf
  rw [perMinorLimOf_conjTranspose, star_div₀]
  congr 1
  rw [show star ((normFactorLim c' * normFactorLim c : ℝ) : ℂ)
      = ((normFactorLim c' * normFactorLim c : ℝ) : ℂ) from by simp]
  rw [mul_comm]

/-! ## 3. Finite-level transport of the limit kernel -/

/-- `Multiset.map` commutes with `ℕ`-multiples of a singleton. -/
theorem map_nsmul_singleton {α β : Type*} (f : α → β) (m : ℕ) (a : α) :
    Multiset.map f (m • {a}) = m • {f a} := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [succ_nsmul, succ_nsmul, Multiset.map_add, ih, Multiset.map_singleton]

/-- Congruence of permanents under entrywise equality. -/
theorem permanent_congr {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ a b, M a b = N a b) : Matrix.permanent M = Matrix.permanent N := by
  unfold Matrix.permanent
  exact Finset.sum_congr rfl (fun σ _ => Finset.prod_congr rfl (fun i _ => h _ _))

/-- The multiset of an embedded configuration is the map of the
original multiset (T1). -/
theorem toMultiset_configEmbLim (d : ℕ) (c₀ : Config d) :
    Finsupp.toMultiset (configEmbLim d c₀)
      = (Finsupp.toMultiset c₀).map Fin.valEmbedding := by
  induction c₀ using Finsupp.induction with
  | zero => simp [Finsupp.toMultiset_zero]
  | single_add a m c₀ _ _ ih =>
      rw [configEmbLim_apply, Finsupp.embDomain_add, Finsupp.embDomain_single,
        ← configEmbLim_apply, Finsupp.toMultiset_add, Finsupp.toMultiset_add,
        ih, Multiset.map_add, Finsupp.toMultiset_single, Finsupp.toMultiset_single]
      congr 1
      exact (map_nsmul_singleton (⇑Fin.valEmbedding) m a).symm

/-- The cast of a finite enumeration list to a list of naturals. -/
noncomputable def enumListCast (d : ℕ) (c₀ : Config d) : List ℕ :=
  (enumList d c₀).map (fun i : Fin d => (i : ℕ))

/-- The enumeration list of an embedded configuration is the cast of
the finite enumeration list (T1): sorting commutes with the monotone
embedding `Fin.val`. -/
theorem enumLimList_configEmbLim (d : ℕ) (c₀ : Config d) :
    enumLimList (configEmbLim d c₀) = enumListCast d c₀ := by
  have hmap : Multiset.map (⇑Fin.valEmbedding) (Finsupp.toMultiset c₀)
      = Multiset.map (fun i : Fin d => (i : ℕ)) (Finsupp.toMultiset c₀) := by
    congr 1
  calc enumLimList (configEmbLim d c₀)
      = ((Finsupp.toMultiset c₀).map (⇑Fin.valEmbedding)).sort (· ≤ ·) := by
        rw [enumLimList, toMultiset_configEmbLim]
    _ = ((Finsupp.toMultiset c₀).map (fun i : Fin d => (i : ℕ))).sort (· ≤ ·) :=
        congrArg (fun s => Multiset.sort s (· ≤ ·)) hmap
    _ = ((Finsupp.toMultiset c₀).sort (· ≤ ·)).map (fun i : Fin d => (i : ℕ)) :=
        (Multiset.map_sort (fun i : Fin d => (i : ℕ)) (Finsupp.toMultiset c₀)
          (· ≤ ·) (· ≤ ·) (fun a _ b _ => Fin.le_iff_val_le_val)).symm
    _ = enumListCast d c₀ := rfl

/-- The limit enumeration of an embedded configuration is the finite
enumeration, cast to `ℕ` (T1). -/
theorem enumLim_configEmbLim (d : ℕ) (c₀ : Config d) (k : Fin (tot c₀)) :
    enumLim (configEmbLim d c₀) (finCongr (totLim_configEmbLim d c₀).symm k)
      = ((configEnum d c₀ k : Fin d) : ℕ) := by
  have s1 : enumLim (configEmbLim d c₀)
        (finCongr (totLim_configEmbLim d c₀).symm k)
      = (enumLimList (configEmbLim d c₀)).get ⟨k.val, by
          rw [enumLimList_length, totLim_configEmbLim]; exact k.isLt⟩ :=
    enumLim_apply _ _
  have s2 : (enumLimList (configEmbLim d c₀)).get ⟨k.val, by
        rw [enumLimList_length, totLim_configEmbLim]; exact k.isLt⟩
      = (enumListCast d c₀).get ⟨k.val, by
          show k.val < ((enumList d c₀).map (fun i : Fin d => (i : ℕ))).length
          rw [List.length_map, enumList_length]; exact k.isLt⟩ :=
    get_congr_list (enumLimList_configEmbLim d c₀) rfl
  have s3 : (enumListCast d c₀).get ⟨k.val, by
        show k.val < ((enumList d c₀).map (fun i : Fin d => (i : ℕ))).length
        rw [List.length_map, enumList_length]; exact k.isLt⟩
      = ((configEnum d c₀ k : Fin d) : ℕ) := by
    have h1 : ((enumList d c₀).map (fun i : Fin d => (i : ℕ))).get ⟨k.val, by
          rw [List.length_map, enumList_length]; exact k.isLt⟩
        = (fun i : Fin d => (i : ℕ)) ((enumList d c₀).get ⟨k.val, by
            rw [enumList_length]; exact k.isLt⟩) := by
      rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_map]
    exact h1.trans (congrArg (fun i : Fin d => (i : ℕ))
      (configEnum_apply d c₀ k)).symm
  exact s1.trans (s2.trans s3)

/-- The limit normalization factor of an embedded configuration is
the finite normalization factor (T1). -/
theorem normFactorLim_configEmbLim (d : ℕ) (c₀ : Config d) :
    normFactorLim (configEmbLim d c₀) = normFactor d c₀ := by
  unfold normFactorLim normFactor
  congr 1
  rw [configEmbLim_apply, Finsupp.prod_embDomain]
  exact Finsupp.prod_fintype c₀ (fun _ n => ((Nat.factorial n : ℕ) : ℝ))
    (fun _ => by simp)

/-- **Transport of the limit permanent minor (T1):** at configurations
embedded from finite levels `e` and `d`, the limit permanent minor of
`A` is the corpus's rectangular permanent minor of the compressed
matrix. -/
theorem perMinorLimOf_configEmbLim (A : ℕ → ℕ → ℂ) (e d : ℕ)
    (c'₀ : Config e) (c₀ : Config d) :
    perMinorLimOf A (configEmbLim e c'₀) (configEmbLim d c₀)
      = perMinorRect (fun i j => A (i : ℕ) (j : ℕ)) c'₀ c₀ := by
  by_cases h : tot c'₀ = tot c₀
  · have h' : totLim (configEmbLim e c'₀) = totLim (configEmbLim d c₀) := by
      rw [totLim_configEmbLim, totLim_configEmbLim]; exact h
    unfold perMinorLimOf perMinorRect
    rw [dif_pos h', dif_pos h]
    have hsub : Matrix.permanent (fun a b : Fin (tot c₀) =>
          A (enumLim (configEmbLim e c'₀) (finCongr h'.symm
              (finCongr (totLim_configEmbLim d c₀).symm a)))
            (enumLim (configEmbLim d c₀)
              (finCongr (totLim_configEmbLim d c₀).symm b)))
        = Matrix.permanent (fun a b : Fin (totLim (configEmbLim d c₀)) =>
            A (enumLim (configEmbLim e c'₀) (finCongr h'.symm a))
              (enumLim (configEmbLim d c₀) b)) :=
      permanent_submatrix_equiv (finCongr (totLim_configEmbLim d c₀).symm)
        (fun a b : Fin (totLim (configEmbLim d c₀)) =>
          A (enumLim (configEmbLim e c'₀) (finCongr h'.symm a))
            (enumLim (configEmbLim d c₀) b))
    rw [← hsub]
    apply permanent_congr
    intro a b
    show A (enumLim (configEmbLim e c'₀)
        (finCongr h'.symm (finCongr (totLim_configEmbLim d c₀).symm a)))
        (enumLim (configEmbLim d c₀)
          (finCongr (totLim_configEmbLim d c₀).symm b))
      = A ((configEnum e c'₀ (finCongr h.symm a) : Fin e) : ℕ)
          ((configEnum d c₀ b : Fin d) : ℕ)
    congr 2
    · rw [enumLim_congr_val (c := configEmbLim e c'₀)
        (k₁ := finCongr h'.symm (finCongr (totLim_configEmbLim d c₀).symm a))
        (k₂ := finCongr (totLim_configEmbLim e c'₀).symm (finCongr h.symm a)) rfl]
      exact enumLim_configEmbLim e c'₀ (finCongr h.symm a)
    · exact enumLim_configEmbLim d c₀ b
  · have h' : totLim (configEmbLim e c'₀) ≠ totLim (configEmbLim d c₀) := by
      rw [totLim_configEmbLim, totLim_configEmbLim]; exact h
    unfold perMinorLimOf perMinorRect
    rw [dif_neg h', dif_neg h]

/-- **Transport of the limit kernel (T1):** at embedded configurations
the limit kernel is the corpus's rectangular kernel of the compressed
matrix. -/
theorem gammaKernelLimOf_configEmbLim (A : ℕ → ℕ → ℂ) (e d : ℕ)
    (c'₀ : Config e) (c₀ : Config d) :
    gammaKernelLimOf A (configEmbLim e c'₀) (configEmbLim d c₀)
      = gammaKernelRect (fun i j => A (i : ℕ) (j : ℕ)) c'₀ c₀ := by
  unfold gammaKernelLimOf gammaKernelRect
  rw [perMinorLimOf_configEmbLim, normFactorLim_configEmbLim,
    normFactorLim_configEmbLim]

/-! ## 4. Rectangular ports of the functor laws

The corpus's functor laws (`perMinor_mul`, `gammaKernel_mul`,
`perMinor_conjTranspose`, `gammaKernel_conjTranspose`) are stated for
square matrices at one level. The limit arguments need them for
rectangular matrices between two levels — target level `e`, source
level `d`, intermediate level `f` — where the corpus's
`perMinorRect`/`gammaKernelRect` live. The proofs are ports of the
square proofs: the combinatorics (`permanent_mul_expansion`, the
fiber-counting lemmas of `BosonicGammaFunctor`) is already stated at
a generic intermediate level. -/

/-- Rectangular permanent minors vanish between different total
counts (T1). -/
theorem perMinorRect_of_tot_ne {d e : ℕ} (M : Matrix (Fin e) (Fin d) ℂ)
    (c' : Config e) (c : Config d) (h : tot c' ≠ tot c) :
    perMinorRect M c' c = 0 :=
  dif_neg h

/-- **Rectangular conjugate-transpose of permanent minors (T1):**
port of `perMinor_conjTranspose`. -/
theorem perMinorRect_conjTranspose {d e : ℕ} (M : Matrix (Fin e) (Fin d) ℂ)
    (c' : Config e) (c : Config d) :
    perMinorRect Mᴴ c c' = star (perMinorRect M c' c) := by
  by_cases htot : tot c' = tot c
  · have e1 : perMinorRect Mᴴ c c' = Matrix.permanent
        (fun a b : Fin (tot c') => star (M (configEnum e c' b)
          (configEnum d c (finCongr htot a)))) := by
      unfold perMinorRect
      rw [dif_pos htot.symm]
      congr 1
    have e2 : perMinorRect M c' c = Matrix.permanent
        (fun a b : Fin (tot c) => M (configEnum e c' (finCongr htot.symm a))
          (configEnum d c b)) := by
      unfold perMinorRect
      rw [dif_pos htot]
    rw [e1, e2, permanent_star (fun a b : Fin (tot c') =>
      M (configEnum e c' b) (configEnum d c (finCongr htot a)))]
    congr 1
    calc Matrix.permanent (fun a b : Fin (tot c') =>
            M (configEnum e c' b) (configEnum d c (finCongr htot a)))
        = Matrix.permanent (Matrix.submatrix
            (fun a b : Fin (tot c) => M (configEnum e c' (finCongr htot.symm a))
              (configEnum d c b))ᵀ
            (finCongr htot) (finCongr htot)) := rfl
      _ = Matrix.permanent (fun a b : Fin (tot c) =>
            M (configEnum e c' (finCongr htot.symm a))
              (configEnum d c b))ᵀ :=
          permanent_submatrix_equiv (finCongr htot) _
      _ = Matrix.permanent (fun a b : Fin (tot c) =>
            M (configEnum e c' (finCongr htot.symm a))
              (configEnum d c b)) :=
          Matrix.permanent_transpose _
  · rw [perMinorRect_of_tot_ne Mᴴ c c' (Ne.symm htot),
      perMinorRect_of_tot_ne M c' c htot, star_zero]

/-- **Rectangular conjugate-transpose of the kernel (T1):** port of
`gammaKernel_conjTranspose`. -/
theorem gammaKernelRect_conjTranspose {d e : ℕ} (M : Matrix (Fin e) (Fin d) ℂ)
    (c' : Config e) (c : Config d) :
    gammaKernelRect Mᴴ c c' = star (gammaKernelRect M c' c) := by
  unfold gammaKernelRect
  rw [perMinorRect_conjTranspose, star_div₀]
  congr 1
  rw [show star ((normFactor d c * normFactor e c' : ℝ) : ℂ)
      = ((normFactor d c * normFactor e c' : ℝ) : ℂ) from by simp]
  rw [mul_comm]

/-- **Rectangular permanent Cauchy–Binet (T1):** port of
`perMinor_mul` — composition of permanent minors over an intermediate
configuration at level `e`, with the same `1 / ∏ i, (c' i)!`
multiplicity weights. -/
theorem perMinorRect_mul {d e g : ℕ} (M : Matrix (Fin g) (Fin e) ℂ)
    (N : Matrix (Fin e) (Fin d) ℂ) (c'' : Config g) (c : Config d) :
    perMinorRect (M * N) c'' c
      = ∑ c' ∈ configsOfTot e (tot c), perMinorRect M c'' c'
          * perMinorRect N c' c
          / ∏ i, ((Nat.factorial (c' i) : ℕ) : ℂ) := by
  by_cases htot : tot c'' = tot c
  · have hLHS : perMinorRect (M * N) c'' c = Matrix.permanent
        (fun a b : Fin (tot c) => (M * N)
          (configEnum g c'' (finCongr htot.symm a)) (configEnum d c b)) := by
      unfold perMinorRect
      rw [dif_pos htot]
    rw [hLHS]
    have hmat : (fun a b : Fin (tot c) => (M * N)
          (configEnum g c'' (finCongr htot.symm a)) (configEnum d c b))
        = (fun a b => ∑ k, M (configEnum g c'' (finCongr htot.symm a)) k
            * N k (configEnum d c b)) := by
      funext a b
      rw [Matrix.mul_apply]
    rw [hmat, permanent_mul_expansion
      (fun a k => M (configEnum g c'' (finCongr htot.symm a)) k)
      (fun k b => N k (configEnum d c b))]
    have hmaps0 : ∀ f ∈ (Finset.univ : Finset (Fin (tot c) → Fin e)),
        configOf f ∈ configsOfTot e (tot c) := fun f _ => by
      rw [mem_configsOfTot]
      exact tot_configOf f
    rw [← Finset.sum_fiberwise_of_maps_to hmaps0]
    apply Finset.sum_congr rfl
    intro c' hc'
    rw [mem_configsOfTot] at hc'
    -- Notation for this fiber class: `hc' : tot c' = tot c`.
    have h'' : tot c'' = tot c' := htot.trans hc'.symm
    have hK : (∏ i, ((Nat.factorial (c' i) : ℕ) : ℂ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      exact Nat.cast_ne_zero.mpr (Nat.factorial_pos (c' i)).ne'
    have hperM : perMinorRect M c'' c' = Matrix.permanent
        (fun a b : Fin (tot c') => M (configEnum g c'' (finCongr h''.symm a))
          (configEnum e c' b)) := by
      unfold perMinorRect
      rw [dif_pos h'']
    have hperN : perMinorRect N c' c = Matrix.permanent
        (fun a b : Fin (tot c) => N (configEnum e c' (finCongr hc'.symm a))
          (configEnum d c b)) := by
      unfold perMinorRect
      rw [dif_pos hc']
    -- Step 2: the `N`-side sum over the class is the minor over the
    -- class multiplicity.
    have hstepN : perMinorRect N c' c
        = (∏ i, ((Nat.factorial (c' i) : ℕ) : ℂ))
          * ∑ f ∈ Finset.univ.filter
              (fun f : Fin (tot c) → Fin e => configOf f = c'),
            ∏ b, N (f b) (configEnum d c b) := by
      rw [hperN]
      show (∑ ρ : Equiv.Perm (Fin (tot c)),
          ∏ b, N (configEnum e c' (finCongr hc'.symm (ρ b)))
            (configEnum d c b)) = _
      have hmaps : ∀ ρ ∈ (Finset.univ : Finset (Equiv.Perm (Fin (tot c)))),
          (fun b => configEnum e c' (finCongr hc'.symm b)) ∘ ρ
            ∈ Finset.univ.filter
              (fun f : Fin (tot c) → Fin e => configOf f = c') := by
        intro ρ _
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        apply Finsupp.ext
        intro i
        rw [configOf_apply, fiberCount_comp_equiv]
        exact fiberCount_configEnum_finCongr e hc'.symm i
      rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      rw [Finset.mem_filter] at hf
      have hfiber : ∀ i, fiberCount f i = c' i := fun i => by
        rw [← configOf_apply f i, hf.2]
      have hsumconst : ∀ ρ ∈ Finset.univ.filter
          (fun ρ : Equiv.Perm (Fin (tot c)) =>
            (fun b => configEnum e c' (finCongr hc'.symm b)) ∘ ρ = f),
          (∏ b, N (configEnum e c' (finCongr hc'.symm (ρ b)))
            (configEnum d c b))
            = ∏ b, N (f b) (configEnum d c b) := by
        intro ρ hρ
        rw [Finset.mem_filter] at hρ
        apply Finset.prod_congr rfl
        intro b _
        rw [show configEnum e c' (finCongr hc'.symm (ρ b))
            = ((fun b => configEnum e c' (finCongr hc'.symm b)) ∘ ρ) b
            from rfl, hρ.2]
      rw [Finset.sum_congr rfl hsumconst, Finset.sum_const]
      have hfil : (Finset.univ.filter
          (fun ρ : Equiv.Perm (Fin (tot c)) =>
            (fun b => configEnum e c' (finCongr hc'.symm b)) ∘ ρ = f))
          = Finset.univ.filter (fun ρ : Equiv.Perm (Fin (tot c)) =>
            ∀ b, configEnum e c' (finCongr hc'.symm (ρ b)) = f b) := by
        apply Finset.filter_congr
        intro ρ _
        constructor
        · intro h b
          exact congrFun h b
        · intro h
          funext b
          exact h b
      rw [hfil, card_filter_perm_apply_eq
        (fun i => (fiberCount_configEnum_finCongr e hc'.symm i).trans
          (hfiber i).symm), nsmul_eq_mul, Nat.cast_prod,
        Finset.prod_congr rfl (fun i _ => congrArg
          (fun n : ℕ => ((Nat.factorial n : ℕ) : ℂ)) (hfiber i))]
    have hsum : (∑ f ∈ Finset.univ.filter
        (fun f : Fin (tot c) → Fin e => configOf f = c'),
        ∏ b, N (f b) (configEnum d c b))
        = perMinorRect N c' c / ∏ i, ((Nat.factorial (c' i) : ℕ) : ℂ) := by
      rw [eq_div_iff hK, mul_comm, ← hstepN]
    -- Step 1: the `M`-side permanent is constant on the class.
    have hstepM : ∀ f ∈ Finset.univ.filter
        (fun f : Fin (tot c) → Fin e => configOf f = c'),
        Matrix.permanent (fun a b => M (configEnum g c'' (finCongr htot.symm a))
            (f b))
          = perMinorRect M c'' c' := by
      intro f hf
      rw [Finset.mem_filter] at hf
      have hfiber : ∀ i, fiberCount f i = c' i := fun i => by
        rw [← configOf_apply f i, hf.2]
      obtain ⟨σ, hσ⟩ := exists_perm_of_fiberCount_eq (d := e) (ι := f)
        (κ := fun b => configEnum e c' (finCongr hc'.symm b))
        (fun i => (hfiber i).trans
          (fiberCount_configEnum_finCongr e hc'.symm i).symm)
      calc Matrix.permanent (fun a b => M (configEnum g c'' (finCongr htot.symm a))
              (f b))
          = Matrix.permanent (fun a b => M (configEnum g c'' (finCongr htot.symm a))
              (configEnum e c' (finCongr hc'.symm (σ b)))) := by
            congr 1
            funext a b
            rw [hσ b]
        _ = Matrix.permanent (fun a b => M (configEnum g c'' (finCongr htot.symm a))
              (configEnum e c' (finCongr hc'.symm b))) := by
            rw [show (fun a b => M (configEnum g c'' (finCongr htot.symm a))
                  (configEnum e c' (finCongr hc'.symm (σ b))))
                = Matrix.submatrix (fun a b => M (configEnum g c'' (finCongr htot.symm a))
                    (configEnum e c' (finCongr hc'.symm b))) id σ from rfl]
            exact Matrix.permanent_permute_rows σ _
        _ = Matrix.permanent (Matrix.submatrix (fun a b : Fin (tot c') =>
              M (configEnum g c'' (finCongr h''.symm a)) (configEnum e c' b))
                (finCongr hc'.symm) (finCongr hc'.symm)) := by
            rfl
        _ = Matrix.permanent (fun a b : Fin (tot c') =>
              M (configEnum g c'' (finCongr h''.symm a)) (configEnum e c' b)) :=
            permanent_submatrix_equiv (finCongr hc'.symm) _
        _ = perMinorRect M c'' c' := hperM.symm
    -- Assembly of the class sum.
    trans (∑ f ∈ Finset.univ.filter
        (fun f : Fin (tot c) → Fin e => configOf f = c'),
        (∏ b, N (f b) (configEnum d c b)) * perMinorRect M c'' c')
    · apply Finset.sum_congr rfl
      intro f hf
      rw [hstepM f hf]
    · rw [← Finset.sum_mul, hsum, div_mul_eq_mul_div,
        mul_comm (perMinorRect N c' c) (perMinorRect M c'' c')]
  · rw [perMinorRect_of_tot_ne (M * N) c'' c htot]
    symm
    apply Finset.sum_eq_zero
    intro c' hc'
    rw [mem_configsOfTot] at hc'
    rw [perMinorRect_of_tot_ne M c'' c' (by omega), zero_mul, zero_div]

/-- **Rectangular kernel multiplicativity (T1):** port of
`gammaKernel_mul` — the kernel of a product is the convolution of the
kernels over the intermediate sector; the `perMinorRect_mul` weights
cancel exactly against the normalizations. -/
theorem gammaKernelRect_mul {d e g : ℕ} (M : Matrix (Fin g) (Fin e) ℂ)
    (N : Matrix (Fin e) (Fin d) ℂ) (c'' : Config g) (c : Config d) :
    gammaKernelRect (M * N) c'' c
      = ∑ c' ∈ configsOfTot e (tot c), gammaKernelRect M c'' c'
          * gammaKernelRect N c' c := by
  have key : ∀ c' : Config e,
        ((normFactor e c' * normFactor g c'' : ℝ) : ℂ)
          * ((normFactor d c * normFactor e c' : ℝ) : ℂ)
        = (∏ i, ((Nat.factorial (c' i) : ℕ) : ℂ))
          * ((normFactor d c * normFactor g c'' : ℝ) : ℂ) := by
    intro c'
    have key' : (normFactor e c' * normFactor g c'')
          * (normFactor d c * normFactor e c')
        = (normFactor e c') ^ 2 * (normFactor d c * normFactor g c'') := by
      ring
    calc ((normFactor e c' * normFactor g c'' : ℝ) : ℂ)
          * ((normFactor d c * normFactor e c' : ℝ) : ℂ)
        = (((normFactor e c' * normFactor g c'')
            * (normFactor d c * normFactor e c') : ℝ) : ℂ) :=
          (Complex.ofReal_mul _ _).symm
      _ = (((normFactor e c') ^ 2
            * (normFactor d c * normFactor g c'') : ℝ) : ℂ) := by rw [key']
      _ = ((normFactor e c' : ℂ)) ^ 2
            * ((normFactor d c * normFactor g c'' : ℝ) : ℂ) := by
          rw [Complex.ofReal_mul, Complex.ofReal_pow]
      _ = (∏ i, ((Nat.factorial (c' i) : ℕ) : ℂ))
            * ((normFactor d c * normFactor g c'' : ℝ) : ℂ) := by
          rw [normFactor_sq]
  unfold gammaKernelRect
  rw [perMinorRect_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c' _
  rw [div_mul_div_comm, key c', div_div]

/-- **The kernel of the identity (T1):** the finite-level diagonal —
the value that both limit arguments land on. -/
theorem gammaKernel_one (d : ℕ) (c' c : Config d) :
    gammaKernel d 1 c' c = if c' = c then 1 else 0 := by
  unfold gammaKernel
  rw [perMinor_one]
  by_cases h : c' = c
  · have hnf : normFactor d c' = normFactor d c := congrArg (normFactor d) h
    rw [if_pos h, if_pos h, hnf]
    have hD : ((normFactor d c * normFactor d c : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos (normFactor_pos d c) (normFactor_pos d c)).ne'
    rw [div_eq_one_iff_eq hD, ← normFactor_sq, sq, ← Complex.ofReal_mul]
  · rw [if_neg h, if_neg h, zero_div]

/-- **Level coherence of the limit embedding (T1):** embedding a
configuration first along the finite tower and then into the limit is
embedding it into the limit directly. -/
theorem configEmbLim_configEmb {d e : ℕ} (h : d ≤ e) (c : Config d) :
    configEmbLim e (configEmb h c) = configEmbLim d c := by
  induction c using Finsupp.induction with
  | zero => rw [configEmb_zero, configEmbLim_zero, configEmbLim_zero]
  | single_add a m c₀ _ _ ih =>
      simp only [configEmb_apply, configEmbLim_apply, Finsupp.embDomain_add,
        Finsupp.embDomain_single]
      have hidx : Fin.valEmbedding ((Fin.castLEEmb h) a) = Fin.valEmbedding a :=
        rfl
      rw [← configEmb_apply, ← configEmbLim_apply, ih, ← configEmbLim_apply,
        hidx]

/-! ## 5. The one-particle matrix and its entry limits

For `W` a unitary of the shell space, `Umat W` is its matrix in the
concrete basis `shellONB`. The analytic inputs of the limit arguments
are: the adjoint relation (`Umat_symm`), Parseval convergence of the
finite Gram sums (`Umat_partial_tendsto`), and Bessel's inequality
for finite partial sums (`sum_sq_Umat_le`). -/

/-- The matrix of a one-particle unitary in the concrete shell basis:
row `j`, column `i`. -/
noncomputable def Umat (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (j i : ℕ) : ℂ :=
  ⟪shellONB m hm j, W (shellONB m hm i)⟫_ℂ

/-- The square compression of `Umat W` to the first `e` modes. -/
noncomputable def UmatFin (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (e : ℕ) :
    Matrix (Fin e) (Fin e) ℂ :=
  fun i j => Umat m hm W i.val j.val

/-- The rectangular compression of `Umat W`: rows at level `e`,
columns at level `d`. -/
noncomputable def UmatRect (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (e d : ℕ) :
    Matrix (Fin e) (Fin d) ℂ :=
  fun i j => Umat m hm W i.val j.val

/-- The Γ-kernel of `W` on limit configurations. -/
noncomputable def gammaKernelLim (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (c' c : ConfigLim) : ℂ :=
  gammaKernelLimOf (Umat m hm W) c' c

/-- The kernel vanishes between different total counts (T1). -/
theorem gammaKernelLim_of_tot_ne (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (c' c : ConfigLim)
    (h : totLim c' ≠ totLim c) :
    gammaKernelLim m hm W c' c = 0 := by
  unfold gammaKernelLim gammaKernelLimOf
  rw [perMinorLimOf_of_tot_ne (Umat m hm W) c' c h, zero_div]

/-- The conjugated matrix entry is the flipped inner product (T1). -/
theorem star_Umat (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (k i : ℕ) :
    star (Umat m hm W k i)
      = ⟪W (shellONB m hm i), shellONB m hm k⟫_ℂ := by
  rw [Umat]
  exact inner_conj_symm _ _

/-- **The matrix of the inverse is the conjugate transpose (T1).** -/
theorem Umat_symm (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (j i : ℕ) :
    Umat m hm W.symm j i = star (Umat m hm W i j) := by
  unfold Umat
  calc ⟪shellONB m hm j, W.symm (shellONB m hm i)⟫_ℂ
      = ⟪W (shellONB m hm j), W (W.symm (shellONB m hm i))⟫_ℂ :=
        (LinearIsometryEquiv.inner_map_map W _ _).symm
    _ = ⟪W (shellONB m hm j), shellONB m hm i⟫_ℂ := by
        rw [LinearIsometryEquiv.apply_symm_apply]
    _ = star ⟪shellONB m hm i, W (shellONB m hm j)⟫_ℂ :=
        (inner_conj_symm _ _).symm

/-- **Adjoint identity for the limit kernel (T1):** the kernel of
`W.symm` is the conjugate kernel with arguments swapped. -/
theorem gammaKernelLim_symm (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (c' c : ConfigLim) :
    gammaKernelLim m hm W.symm c' c
      = star (gammaKernelLim m hm W c c') := by
  unfold gammaKernelLim
  rw [← gammaKernelLimOf_conjTranspose]
  congr 1
  funext j i
  exact Umat_symm m hm W j i

/-- **Parseval convergence of the finite Gram sums (T1):** the
partial sums of `star (Umat W₁ · i) * Umat W₂ · j` over the first `e`
modes converge to the inner product of the images. -/
theorem Umat_partial_tendsto (m : ℝ) (hm : 0 < m)
    (W₁ W₂ : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (i j : ℕ) :
    Tendsto (fun e => ∑ k ∈ Finset.range e,
        star (Umat m hm W₁ k i) * Umat m hm W₂ k j)
      atTop (𝓝 ⟪W₁ (shellONB m hm i), W₂ (shellONB m hm j)⟫_ℂ) := by
  have h := ((shellONB m hm).hasSum_inner_mul_inner
    (W₁ (shellONB m hm i)) (W₂ (shellONB m hm j))).tendsto_sum_nat
  refine Filter.Tendsto.congr ?_ h
  intro e
  apply Finset.sum_congr rfl
  intro k _
  symm
  rw [star_Umat m hm W₁ k i, Umat]

/-- **Bessel bound for finite partial sums (T1):** the squared
moduli of the first `e` entries of any column of `Umat W` sum to at
most `1`. -/
theorem sum_sq_Umat_le (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (e j : ℕ) :
    ∑ k : Fin e, ‖Umat m hm W k.val j‖ ^ 2 ≤ 1 := by
  have hb := (shellONB m hm).orthonormal.sum_inner_products_le
    (W (shellONB m hm j)) (s := Finset.range e)
  rw [LinearIsometryEquiv.norm_map, (shellONB m hm).orthonormal.norm_eq_one j,
    one_pow] at hb
  show ∑ k : Fin e, ‖⟪shellONB m hm k.val, W (shellONB m hm j)⟫_ℂ‖ ^ 2 ≤ 1
  have h2 : (∑ k : Fin e, ‖⟪shellONB m hm k.val, W (shellONB m hm j)⟫_ℂ‖ ^ 2)
      = ∑ i ∈ Finset.range e, ‖⟪shellONB m hm i, W (shellONB m hm j)⟫_ℂ‖ ^ 2 :=
    Fin.sum_univ_eq_sum_range
      (fun i => ‖⟪shellONB m hm i, W (shellONB m hm j)⟫_ℂ‖ ^ 2) e
  rw [h2]
  exact hb

/-- The squared norm of a complex number as a conjugate product
(T1). -/
theorem ofReal_norm_sq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
  simpa using (RCLike.conj_mul z).symm

/-- The squared normalization factor, as a real identity (T1). -/
theorem normFactor_sq_real (d : ℕ) (c : Config d) :
    (normFactor d c) ^ 2 = ∏ i, ((Nat.factorial (c i) : ℕ) : ℝ) := by
  have hP : (0 : ℝ) ≤ ∏ i, ((Nat.factorial (c i) : ℕ) : ℝ) :=
    Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)
  unfold normFactor
  rw [sq, Real.mul_self_sqrt hP]

/-- Entries of the finite Gram matrix of `Umat W` (T1). -/
theorem UmatGram_apply (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (E d : ℕ) (i j : Fin d) :
    ((UmatRect m hm W E d)ᴴ * (UmatRect m hm W E d)) i j
      = ∑ k : Fin E, star (Umat m hm W k.val i.val)
          * Umat m hm W k.val j.val := by
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.conjTranspose_apply]
  rfl

/-- **Finite Cauchy–Schwarz for Gram entries (T1).** -/
theorem norm_UmatGram_le (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (E : ℕ) (i j : ℕ) :
    ‖∑ k : Fin E, star (Umat m hm W k.val i) * Umat m hm W k.val j‖
      ≤ Real.sqrt (∑ k : Fin E, ‖Umat m hm W k.val i‖ ^ 2)
        * Real.sqrt (∑ k : Fin E, ‖Umat m hm W k.val j‖ ^ 2) := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin E))
    (fun k => ‖Umat m hm W k.val i‖) (fun k => ‖Umat m hm W k.val j‖)
  have hsum : ‖∑ k : Fin E, star (Umat m hm W k.val i) * Umat m hm W k.val j‖
      ≤ ∑ k : Fin E, ‖Umat m hm W k.val i‖ * ‖Umat m hm W k.val j‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    apply Finset.sum_le_sum
    intro k _
    rw [norm_mul, norm_star]
  refine le_trans hsum ?_
  have hnn : (0 : ℝ) ≤ ∑ k : Fin E, ‖Umat m hm W k.val i‖
      * ‖Umat m hm W k.val j‖ :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have h1 : ∑ k : Fin E, ‖Umat m hm W k.val i‖ * ‖Umat m hm W k.val j‖
      ≤ Real.sqrt ((∑ k : Fin E, ‖Umat m hm W k.val i‖ ^ 2)
          * (∑ k : Fin E, ‖Umat m hm W k.val j‖ ^ 2)) := by
    rw [Real.le_sqrt hnn (by positivity)]
    exact hCS
  refine le_trans h1 ?_
  rw [Real.sqrt_mul (Finset.sum_nonneg (fun k _ => sq_nonneg _))]

/-- **Permanent Gram bound (T1):** a permanent of Gram entries of
`Umat W` over positions with occupation profile `c₀` is at most
`(tot c₀)!` in norm — every column has Bessel norm at most `1`, and
there are `(tot c₀)!` permutations. -/
theorem permanent_gram_le (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (E d : ℕ) (c₀ : Config d)
    (ι κ : Fin (tot c₀) → Fin d)
    (hι : ∀ i, fiberCount ι i = c₀ i) (hκ : ∀ i, fiberCount κ i = c₀ i) :
    ‖Matrix.permanent (fun a b => ((UmatRect m hm W E d)ᴴ
        * (UmatRect m hm W E d)) (ι a) (κ b))‖
      ≤ (Nat.factorial (tot c₀) : ℝ) := by
  have hv : ∀ j : ℕ, Real.sqrt (∑ k : Fin E, ‖Umat m hm W k.val j‖ ^ 2)
      ≤ 1 := fun j => by
    simpa using Real.sqrt_le_sqrt (sum_sq_Umat_le m hm W E j)
  have hfac : ∀ (σ : Equiv.Perm (Fin (tot c₀))) (b : Fin (tot c₀)),
      ‖((UmatRect m hm W E d)ᴴ * (UmatRect m hm W E d))
        (ι (σ b)) (κ b)‖ ≤ 1 := by
    intro σ b
    rw [UmatGram_apply]
    refine le_trans (norm_UmatGram_le m hm W E _ _) ?_
    refine le_trans (mul_le_mul (hv _) (hv _) (Real.sqrt_nonneg _)
      (by norm_num)) ?_
    norm_num
  have hcard : ∑ σ : Equiv.Perm (Fin (tot c₀)), (1 : ℝ)
      = (Nat.factorial (tot c₀) : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  calc ‖Matrix.permanent (fun a b => ((UmatRect m hm W E d)ᴴ
          * (UmatRect m hm W E d)) (ι a) (κ b))‖
      ≤ ∑ σ : Equiv.Perm (Fin (tot c₀)),
          ∏ b, ‖((UmatRect m hm W E d)ᴴ * (UmatRect m hm W E d))
            (ι (σ b)) (κ b)‖ := by
        show ‖∑ σ : Equiv.Perm (Fin (tot c₀)), ∏ b,
            ((UmatRect m hm W E d)ᴴ * (UmatRect m hm W E d))
              (ι (σ b)) (κ b)‖ ≤ _
        refine le_trans (norm_sum_le _ _) ?_
        apply Finset.sum_le_sum
        intro σ _
        exact Finset.norm_prod_le Finset.univ _
    _ ≤ ∑ σ : Equiv.Perm (Fin (tot c₀)), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro σ _
        apply Finset.prod_le_one₀
        · intro b _
          exact norm_nonneg _
        · intro b _
          exact hfac σ b
    _ = (Nat.factorial (tot c₀) : ℝ) := hcard

/-- **B0 — the column bound (T1):** for every limit configuration
`c` and every finite set of output configurations, the squared
kernel entries in the column of `c` sum to at most
`(totLim c)! / ∏ (c i)!`. This is the `ℓ²` input for the column
vectors of `Γ(W)`. -/
theorem gammaKernelLim_col_sum_le (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (c : ConfigLim)
    (s : Finset ConfigLim) :
    ∑ c' ∈ s, ‖gammaKernelLim m hm W c' c‖ ^ 2
      ≤ (Nat.factorial (totLim c) : ℝ)
        / c.prod (fun _ n => (Nat.factorial n : ℝ)) := by
  classical
  obtain ⟨d, c₀, hc⟩ := config_factor c
  have htot₀ : tot c₀ = totLim c := by
    rw [← totLim_configEmbLim, hc]
  -- The finite level bounding every factorization in play.
  set E := d + ∑ c' ∈ s, (if totLim c' = totLim c
    then (config_factor c').choose else 0) with hE
  have hdE : d ≤ E := by rw [hE]; omega
  have hsup : ∀ c' ∈ s, (if totLim c' = totLim c
      then (config_factor c').choose else 0) ≤ E := by
    intro c' hc'
    have h1 := Finset.single_le_sum
      (f := fun c' => if totLim c' = totLim c
        then (config_factor c').choose else 0)
      (fun x _ => Nat.zero_le _) hc'
    rw [hE]
    omega
  -- Step 1: only matching totals contribute.
  have step1 : ∑ c' ∈ s, ‖gammaKernelLim m hm W c' c‖ ^ 2
      = ∑ c' ∈ s.filter (fun c' => totLim c' = totLim c),
        ‖gammaKernelLim m hm W c' c‖ ^ 2 :=
    (Finset.sum_subset (Finset.filter_subset _ _)
      (fun c' hc' hcT => by
        simp only [Finset.mem_filter, not_and] at hcT
        rw [gammaKernelLim_of_tot_ne m hm W c' c (hcT hc')]
        simp)).symm
  -- Step 2: the filtered set embeds into the level-`E` configurations.
  have hTU : s.filter (fun c' => totLim c' = totLim c)
      ⊆ (configsOfTot E (totLim c)).map (configEmbLim E) := by
    intro c' hc'
    rw [Finset.mem_filter] at hc'
    set e' := (config_factor c').choose with he'
    set c'₀ := (config_factor c').choose_spec.choose with hc'₀
    have he'c' : configEmbLim e' c'₀ = c' :=
      (config_factor c').choose_spec.choose_spec
    have heE : e' ≤ E := by
      have h := hsup c' hc'.1
      rwa [if_pos hc'.2] at h
    rw [Finset.mem_map]
    refine ⟨configEmb heE c'₀, ?_, ?_⟩
    · rw [mem_configsOfTot, tot_configEmb, ← totLim_configEmbLim, he'c',
        hc'.2]
    · rw [configEmbLim_configEmb, he'c']
  have step2 : ∑ c' ∈ s.filter (fun c' => totLim c' = totLim c),
        ‖gammaKernelLim m hm W c' c‖ ^ 2
      ≤ ∑ c' ∈ (configsOfTot E (totLim c)).map (configEmbLim E),
        ‖gammaKernelLim m hm W c' c‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hTU
      (fun c' _ _ => by positivity)
  -- Step 3: unwind the embedding — the sum is a finite rectangular sum.
  have hterm : ∀ c'₁ : Config E,
      gammaKernelLim m hm W (configEmbLim E c'₁) c
        = gammaKernelRect (UmatRect m hm W E d) c'₁ c₀ := by
    intro c'₁
    rw [← hc]
    exact gammaKernelLimOf_configEmbLim (Umat m hm W) E d c'₁ c₀
  have step3 : ∑ c' ∈ (configsOfTot E (totLim c)).map (configEmbLim E),
        ‖gammaKernelLim m hm W c' c‖ ^ 2
      = ∑ c'₁ ∈ configsOfTot E (tot c₀),
        ‖gammaKernelRect (UmatRect m hm W E d) c'₁ c₀‖ ^ 2 := by
    rw [Finset.sum_map, ← htot₀]
    apply Finset.sum_congr rfl
    intro c'₁ _
    rw [hterm]
  -- Step 4: the sum is the diagonal Gram kernel entry.
  have step4 : ((∑ c'₁ ∈ configsOfTot E (tot c₀),
        ‖gammaKernelRect (UmatRect m hm W E d) c'₁ c₀‖ ^ 2 : ℝ) : ℂ)
      = gammaKernelRect ((UmatRect m hm W E d)ᴴ * (UmatRect m hm W E d))
          c₀ c₀ := by
    rw [Complex.ofReal_sum]
    rw [Finset.sum_congr rfl (g := fun c'₁ =>
      gammaKernelRect ((UmatRect m hm W E d)ᴴ) c₀ c'₁
        * gammaKernelRect (UmatRect m hm W E d) c'₁ c₀)
      (fun c'₁ _ => by rw [ofReal_norm_sq, gammaKernelRect_conjTranspose])]
    exact (gammaKernelRect_mul ((UmatRect m hm W E d)ᴴ)
      (UmatRect m hm W E d) c₀ c₀).symm
  -- Step 5: bound the Gram entry by the permanent bound.
  have hSnn : (0 : ℝ) ≤ ∑ c'₁ ∈ configsOfTot E (tot c₀),
      ‖gammaKernelRect (UmatRect m hm W E d) c'₁ c₀‖ ^ 2 :=
    Finset.sum_nonneg (fun c'₁ _ => by positivity)
  have hnormD : ∀ x : ℝ, 0 ≤ x → ‖((x : ℝ) : ℂ)‖ = x := fun x hx => by
    simp [abs_of_nonneg hx]
  have step5 : ∑ c'₁ ∈ configsOfTot E (tot c₀),
        ‖gammaKernelRect (UmatRect m hm W E d) c'₁ c₀‖ ^ 2
      ≤ (Nat.factorial (tot c₀) : ℝ) / ∏ i, ((Nat.factorial (c₀ i) : ℕ) : ℝ) := by
    have hGK : gammaKernelRect ((UmatRect m hm W E d)ᴴ * (UmatRect m hm W E d))
          c₀ c₀
        = perMinorRect ((UmatRect m hm W E d)ᴴ * (UmatRect m hm W E d)) c₀ c₀
          / ((normFactor d c₀ * normFactor d c₀ : ℝ) : ℂ) := rfl
    have hper : ‖perMinorRect ((UmatRect m hm W E d)ᴴ
          * (UmatRect m hm W E d)) c₀ c₀‖
        ≤ (Nat.factorial (tot c₀) : ℝ) := by
      unfold perMinorRect
      rw [dif_pos rfl]
      exact permanent_gram_le m hm W E d c₀
        (fun a => configEnum d c₀ (finCongr (rfl : tot c₀ = tot c₀).symm a))
        (configEnum d c₀)
        (fun i => fiberCount_configEnum_finCongr d rfl i)
        (fun i => configEnum_fiber_card d c₀ i)
    have hDpos : (0 : ℝ) < normFactor d c₀ * normFactor d c₀ :=
      mul_pos (normFactor_pos d c₀) (normFactor_pos d c₀)
    have hnf2 : normFactor d c₀ * normFactor d c₀
        = ∏ i, ((Nat.factorial (c₀ i) : ℕ) : ℝ) := by
      rw [← pow_two]
      exact normFactor_sq_real d c₀
    have hbound : ‖gammaKernelRect ((UmatRect m hm W E d)ᴴ
          * (UmatRect m hm W E d)) c₀ c₀‖
        ≤ (Nat.factorial (tot c₀) : ℝ)
          / ∏ i, ((Nat.factorial (c₀ i) : ℕ) : ℝ) := by
      rw [hGK, norm_div, hnormD _ hDpos.le, hnf2]
      exact (div_le_div_iff_of_pos_right (Finset.prod_pos
        (fun i _ => by exact_mod_cast Nat.factorial_pos (c₀ i)))).mpr hper
    calc ∑ c'₁ ∈ configsOfTot E (tot c₀),
          ‖gammaKernelRect (UmatRect m hm W E d) c'₁ c₀‖ ^ 2
        = ‖gammaKernelRect ((UmatRect m hm W E d)ᴴ
            * (UmatRect m hm W E d)) c₀ c₀‖ := by
          rw [← step4, hnormD _ hSnn]
      _ ≤ (Nat.factorial (tot c₀) : ℝ)
            / ∏ i, ((Nat.factorial (c₀ i) : ℕ) : ℝ) := hbound
  -- Assemble, converting the bound back to limit form.
  have hprod : c.prod (fun _ n => (Nat.factorial n : ℝ))
      = ∏ i, ((Nat.factorial (c₀ i) : ℕ) : ℝ) := by
    rw [← hc, configEmbLim_apply, Finsupp.prod_embDomain]
    exact Finsupp.prod_fintype c₀ (fun _ n => (Nat.factorial n : ℝ))
      (fun i => by simp)
  rw [step1]
  refine le_trans step2 (le_trans step3.le ?_)
  rw [hprod, ← htot₀]
  exact step5

/-- **Column summability (T1):** the squared kernel entries in any
column are summable — the columns of `Γ(W)` are `ℓ²` vectors. -/
theorem gammaKernelLim_summable_col (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (c : ConfigLim) :
    Summable (fun c' => ‖gammaKernelLim m hm W c' c‖ ^ 2) :=
  summable_of_sum_le (fun c' => by positivity)
    (fun s => gammaKernelLim_col_sum_le m hm W c s)

/-- **Row summability (T1),** via the adjoint identity. -/
theorem gammaKernelLim_summable_row (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (c : ConfigLim) :
    Summable (fun c' => ‖gammaKernelLim m hm W c c'‖ ^ 2) := by
  apply Summable.congr (gammaKernelLim_summable_col m hm W.symm c)
  intro c'
  rw [gammaKernelLim_symm, norm_star]

/-! ## 6. The three limit theorems

The functor law and the column orthonormality at the limit are
proved by exhaustion: partial sums over the embedded finite
configurations are finite rectangular kernel expressions (§4), whose
entries converge by Parseval (§5); the tail is controlled by B0 (§5).
The exhaustion lemma below is the bridge. -/

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

/-- **Entry-limit for rectangular kernels (T1):** if the entries of
a sequence of rectangular matrices converge, so do the kernel
values — the kernel is a fixed finite polynomial in the entries. -/
theorem gammaKernelRect_tendsto_of_tendsto {e' d' : ℕ}
    (X : ℕ → Matrix (Fin e') (Fin d') ℂ) (Y : Matrix (Fin e') (Fin d') ℂ)
    (hXY : ∀ i j, Tendsto (fun e => X e i j) atTop (𝓝 (Y i j)))
    (c'₀ : Config e') (c₀ : Config d') :
    Tendsto (fun e => gammaKernelRect (X e) c'₀ c₀) atTop
      (𝓝 (gammaKernelRect Y c'₀ c₀)) := by
  by_cases htot : tot c'₀ = tot c₀
  · have hper : ∀ Z : Matrix (Fin e') (Fin d') ℂ, gammaKernelRect Z c'₀ c₀
        = Matrix.permanent
            (fun a b => Z (configEnum e' c'₀ (finCongr htot.symm a))
              (configEnum d' c₀ b))
          / ((normFactor d' c₀ * normFactor e' c'₀ : ℝ) : ℂ) := by
      intro Z
      unfold gammaKernelRect perMinorRect
      rw [dif_pos htot]
    have h1 : (fun e => gammaKernelRect (X e) c'₀ c₀)
        = fun e => Matrix.permanent
            (fun a b => X e (configEnum e' c'₀ (finCongr htot.symm a))
              (configEnum d' c₀ b))
          / ((normFactor d' c₀ * normFactor e' c'₀ : ℝ) : ℂ) :=
      funext (fun e => hper (X e))
    rw [h1, hper Y]
    refine Filter.Tendsto.div ?_ tendsto_const_nhds
      (by exact_mod_cast (mul_pos (normFactor_pos d' c₀)
        (normFactor_pos e' c'₀)).ne')
    unfold Matrix.permanent
    refine tendsto_finsetSum _ (fun σ _ => ?_)
    refine tendsto_finsetProd _ (fun b _ => ?_)
    exact hXY _ _
  · have hper0 : ∀ Z : Matrix (Fin e') (Fin d') ℂ,
        gammaKernelRect Z c'₀ c₀ = 0 := by
      intro Z
      unfold gammaKernelRect perMinorRect
      rw [dif_neg htot, zero_div]
    rw [hper0 Y]
    exact Filter.Tendsto.congr (fun e => (hper0 (X e)).symm)
      tendsto_const_nhds

/-- Rectangular kernels at equal levels are the square kernels
(T1). -/
theorem gammaKernelRect_eq (d : ℕ) (X : Matrix (Fin d) (Fin d) ℂ)
    (c' c : Config d) :
    gammaKernelRect X c' c = gammaKernel d X c' c := by
  unfold gammaKernelRect gammaKernel
  rw [perMinorRect_eq_perMinor]

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

/-- Enumerated modes lie below the support bound (T1). -/
theorem enumLim_lt (c : ConfigLim) (k : Fin (totLim c)) :
    enumLim c k < c.support.sup id + 1 := by
  have hpos : 0 < c (enumLim c k) := by
    rw [← fiberCountLim_enumLim c (enumLim c k)]
    unfold fiberCountLim
    rw [Finset.card_pos]
    exact ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ k, rfl⟩⟩
  have hsupp : enumLim c k ∈ c.support :=
    Finsupp.mem_support_iff.2 (by omega)
  have hle : enumLim c k ≤ c.support.sup id := Finset.le_sup (f := id) hsupp
  omega

/-- Fiber cardinality of a transported limit enumeration (T1). -/
theorem fiberCountLim_comp_equiv {n m : ℕ} (e : Fin m ≃ Fin n)
    (g : Fin n → ℕ) (v : ℕ) :
    fiberCountLim (g ∘ e) v = fiberCountLim g v := by
  unfold fiberCountLim
  rw [Finset.card_filter, Finset.card_filter]
  exact Equiv.sum_comp e (fun b => if g b = v then (1 : ℕ) else 0)

/-- **L1 at the abstract kernel (T1):** the identity matrix's limit
kernel is the Kronecker delta on limit configurations. Proved by the
indicator permanent (`permanent_indicator`) at the common level
`e` bounding both supports: the numerator is the squared
normalization factor when the fiber counts agree — which happens
exactly for equal configurations. -/
theorem gammaKernelLimOf_id (c' c : ConfigLim) :
    gammaKernelLimOf (fun j i => if j = i then (1 : ℂ) else 0) c' c
      = if c' = c then 1 else 0 := by
  by_cases htot : totLim c' = totLim c
  · -- Common level above both supports.
    set e := (c.support.sup id + 1) ⊔ (c'.support.sup id + 1) with he
    have hlt' : ∀ a : Fin (totLim c), enumLim c' (finCongr htot.symm a) < e :=
      fun a => lt_of_lt_of_le (enumLim_lt c' _) le_sup_right
    have hlt : ∀ b : Fin (totLim c), enumLim c b < e :=
      fun b => lt_of_lt_of_le (enumLim_lt c b) le_sup_left
    have hι : ∀ i : Fin e, fiberCount
        (fun a => (⟨enumLim c' (finCongr htot.symm a), hlt' a⟩ : Fin e)) i
        = c' i.val := by
      intro i
      have hset : (Finset.univ.filter
          (fun a => (⟨enumLim c' (finCongr htot.symm a), hlt' a⟩ : Fin e) = i))
          = Finset.univ.filter
            (fun a => enumLim c' (finCongr htot.symm a) = i.val) :=
        Finset.filter_congr (fun a _ => by rw [Fin.ext_iff])
      unfold fiberCount
      rw [hset]
      show fiberCountLim (enumLim c' ∘ finCongr htot.symm) i.val = c' i.val
      rw [fiberCountLim_comp_equiv, fiberCountLim_enumLim]
    have hκ : ∀ i : Fin e, fiberCount
        (fun b => (⟨enumLim c b, hlt b⟩ : Fin e)) i = c i.val := by
      intro i
      have hset : (Finset.univ.filter
          (fun b => (⟨enumLim c b, hlt b⟩ : Fin e) = i))
          = Finset.univ.filter (fun b => enumLim c b = i.val) :=
        Finset.filter_congr (fun b _ => by rw [Fin.ext_iff])
      unfold fiberCount
      rw [hset]
      show fiberCountLim (enumLim c) i.val = c i.val
      exact fiberCountLim_enumLim c i.val
    have hper : perMinorLimOf (fun j i => if j = i then (1 : ℂ) else 0) c' c
        = Matrix.permanent (fun a b =>
            if (⟨enumLim c' (finCongr htot.symm a), hlt' a⟩ : Fin e)
                = ⟨enumLim c b, hlt b⟩
              then (fun _ : Fin e => (1 : ℂ)) ⟨enumLim c b, hlt b⟩
              else 0) := by
      unfold perMinorLimOf
      rw [dif_pos htot]
      apply permanent_congr
      intro a b
      show (if enumLim c' (finCongr htot.symm a) = enumLim c b
          then (1 : ℂ) else 0)
        = (if (⟨enumLim c' (finCongr htot.symm a), hlt' a⟩ : Fin e)
            = ⟨enumLim c b, hlt b⟩
            then (fun _ : Fin e => (1 : ℂ)) ⟨enumLim c b, hlt b⟩ else 0)
      by_cases h : (⟨enumLim c' (finCongr htot.symm a), hlt' a⟩ : Fin e)
          = ⟨enumLim c b, hlt b⟩
      · rw [if_pos h, if_pos (Fin.ext_iff.1 h)]
      · rw [if_neg h, if_neg (fun hv => h (Fin.ext hv))]
    by_cases hfib : ∀ i : Fin e, fiberCount
        (fun a => (⟨enumLim c' (finCongr htot.symm a), hlt' a⟩ : Fin e)) i
        = fiberCount (fun b => (⟨enumLim c b, hlt b⟩ : Fin e)) i
    · -- Fiber counts agree: the configurations are equal.
      have hcc : c' = c := by
        apply Finsupp.ext
        intro v
        by_cases hv : v < e
        · have hvv := hfib ⟨v, hv⟩
          rw [hι ⟨v, hv⟩, hκ ⟨v, hv⟩] at hvv
          exact hvv
        · have h1 : c' v = 0 := by
            by_contra hne
            have hmem : v ∈ c'.support := Finsupp.mem_support_iff.2 hne
            have hle : v ≤ c'.support.sup id := Finset.le_sup (f := id) hmem
            have he2 : c'.support.sup id + 1 ≤ e := le_sup_right
            omega
          have h2 : c v = 0 := by
            by_contra hne
            have hmem : v ∈ c.support := Finsupp.mem_support_iff.2 hne
            have hle : v ≤ c.support.sup id := Finset.le_sup (f := id) hmem
            have he1 : c.support.sup id + 1 ≤ e := le_sup_left
            omega
          rw [h1, h2]
      have hnum : ((∏ i, Nat.factorial (fiberCount
            (fun a => (⟨enumLim c' (finCongr htot.symm a), hlt' a⟩ : Fin e))
            i) : ℕ) : ℂ) = ((normFactorLim c' : ℂ)) ^ 2 := by
        calc ((∏ i, Nat.factorial (fiberCount
                (fun a => (⟨enumLim c' (finCongr htot.symm a), hlt' a⟩
                  : Fin e)) i) : ℕ) : ℂ)
            = ∏ i : Fin e, ((Nat.factorial (c' i.val) : ℕ) : ℂ) := by
              rw [Nat.cast_prod]
              exact Finset.prod_congr rfl (fun i _ => by rw [hι i])
          _ = ∏ i ∈ Finset.range e, ((Nat.factorial (c' i) : ℕ) : ℂ) :=
              Fin.prod_univ_eq_prod_range
                (fun v => ((Nat.factorial (c' v) : ℕ) : ℂ)) e
          _ = ∏ i ∈ c'.support, ((Nat.factorial (c' i) : ℕ) : ℂ) := by
              refine (Finset.prod_subset ?_ ?_).symm
              · intro i hi
                have hle : i ≤ c'.support.sup id := Finset.le_sup (f := id) hi
                have he2 : c'.support.sup id + 1 ≤ e := le_sup_right
                exact Finset.mem_range.2 (by omega)
              · intro i _ hi
                simp [Finsupp.notMem_support_iff.1 hi]
          _ = c'.prod (fun _ n => ((Nat.factorial n : ℕ) : ℂ)) := rfl
          _ = ((normFactorLim c' : ℂ)) ^ 2 := (normFactorLim_sq c').symm
      have hden : ((normFactorLim c * normFactorLim c' : ℝ) : ℂ)
          = ((normFactorLim c' : ℂ)) ^ 2 := by
        rw [← hcc, Complex.ofReal_mul, ← pow_two]
      unfold gammaKernelLimOf
      rw [hper, permanent_indicator (w := fun _ => (1 : ℂ)), if_pos hfib, hnum,
        Finset.prod_const_one, mul_one, hden, if_pos hcc]
      exact div_self (pow_ne_zero 2
        (by exact_mod_cast (normFactorLim_pos c').ne'))
    · obtain ⟨i, hi⟩ := not_forall.1 hfib
      have hcc : c' ≠ c := by
        intro h
        apply hi
        rw [hι i, hκ i, h]
      unfold gammaKernelLimOf
      rw [hper, permanent_indicator (w := fun _ => (1 : ℂ)), if_neg hfib, if_neg hcc, zero_div]
  · have hcc : c' ≠ c := fun h => htot (by rw [h])
    unfold gammaKernelLimOf
    rw [perMinorLimOf_of_tot_ne _ _ _ htot, if_neg hcc, zero_div]

/-- **L1 (T1):** the identity unitary's limit kernel is the
Kronecker delta — `Γ(1) = 1` at the kernel level. -/
theorem gammaKernelLim_one (c' c : ConfigLim) :
    gammaKernelLim m hm (1 : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) c' c
      = if c' = c then 1 else 0 := by
  have hU : Umat m hm (1 : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm)
      = fun j i => if j = i then (1 : ℂ) else 0 := by
    funext j i
    show ⟪shellONB m hm j, shellONB m hm i⟫_ℂ = _
    exact orthonormal_iff_ite.mp (shellONB m hm).orthonormal j i
  unfold gammaKernelLim
  rw [hU]
  exact gammaKernelLimOf_id c' c

/-- **L3′ (T1): column orthonormality of the limit kernel.** For
every unitary `W`, the columns of `gammaKernelLim W` are orthonormal
in `ℓ²(ConfigLim)`: proved by exhaustion (§6α) — the partial sums
are the finite rectangular composition law (§4) applied to the
Gram matrix of the truncated one-particle matrix, whose entries
converge to the identity by Parseval (§5). -/
theorem gammaKernelLim_column_orthonormal (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (c₁ c₂ : ConfigLim) :
    ∑' c', star (gammaKernelLim m hm W c' c₁) * gammaKernelLim m hm W c' c₂
      = if c₁ = c₂ then 1 else 0 := by
  classical
  set f : ConfigLim → ℂ := fun c' => star (gammaKernelLim m hm W c' c₁)
    * gammaKernelLim m hm W c' c₂ with hf_def
  have hf : Summable f := by
    refine summable_mul_of_summable_sq (f := fun c' =>
      star (gammaKernelLim m hm W c' c₁)) (g := fun c' =>
      gammaKernelLim m hm W c' c₂) ?_ (gammaKernelLim_summable_col m hm W c₂)
    refine Summable.congr (gammaKernelLim_summable_col m hm W c₁) ?_
    intro a
    rw [norm_star]
  by_cases htot : totLim c₁ = totLim c₂
  · -- Factor both configurations and assemble at `D = max d₁ d₂`.
    obtain ⟨d₁, c₁₀, hc₁₀⟩ := config_factor c₁
    obtain ⟨d₂, c₂₀, hc₂₀⟩ := config_factor c₂
    set D := max d₁ d₂ with hD
    set c₁₁ : Config D := configEmb (le_max_left d₁ d₂) c₁₀ with hc₁₁def
    set c₂₁ : Config D := configEmb (le_max_right d₁ d₂) c₂₀ with hc₂₁def
    have hc₁ : configEmbLim D c₁₁ = c₁ :=
      (configEmbLim_configEmb _ c₁₀).trans hc₁₀
    have hc₂ : configEmbLim D c₂₁ = c₂ :=
      (configEmbLim_configEmb _ c₂₀).trans hc₂₀
    have htot₂₁ : tot c₂₁ = totLim c₁ := by
      have h1 : totLim (configEmbLim D c₂₁) = tot c₂₁ :=
        totLim_configEmbLim D c₂₁
      rw [hc₂] at h1
      rw [← h1, htot]
    set n := totLim c₁ with hn
    set s : ℕ → Finset ConfigLim := fun e =>
      (configsOfTot e n).map (configEmbLim e) with hs_def
    have hset : ∀ e, configsOfTot e n = configsOfTot e (tot c₂₁) := by
      intro e
      congr 1
      exact htot₂₁.symm
    have hmono : Monotone s := by
      intro e₁ e₂ he a ha
      simp only [hs_def, Finset.mem_map] at ha ⊢
      obtain ⟨a₁, ha₁, rfl⟩ := ha
      refine ⟨configEmb he a₁, ?_, ?_⟩
      · rw [mem_configsOfTot] at ha₁ ⊢
        rwa [tot_configEmb]
      · exact configEmbLim_configEmb he a₁
    have hcov : ∀ a, f a ≠ 0 → ∃ e, a ∈ s e := by
      intro a ha
      have ha' : star (gammaKernelLim m hm W a c₁)
          * gammaKernelLim m hm W a c₂ ≠ 0 := ha
      have ha₁ : gammaKernelLim m hm W a c₁ ≠ 0 :=
        star_ne_zero.1 (mul_ne_zero_iff.1 ha').1
      have hta : totLim a = n := by
        by_contra hne
        exact ha₁ (gammaKernelLim_of_tot_ne m hm W a c₁ hne)
      obtain ⟨d, a₀, ha₀⟩ := config_factor a
      refine ⟨d, ?_⟩
      simp only [hs_def, Finset.mem_map]
      refine ⟨configEmb (le_refl d) a₀, ?_, ?_⟩
      · rw [mem_configsOfTot, tot_configEmb]
        have h3 : totLim (configEmbLim d a₀) = tot a₀ :=
          totLim_configEmbLim d a₀
        rw [ha₀] at h3
        rw [← h3, hta]
      · rw [configEmbLim_configEmb, ha₀]
    -- The partial sums are Gram-kernel values.
    have hpartial : ∀ e, ∑ a ∈ s e, f a
        = gammaKernelRect ((UmatRect m hm W e D)ᴴ * UmatRect m hm W e D)
            c₁₁ c₂₁ := by
      intro e
      have hterm : ∀ a₁ : Config e, f (configEmbLim e a₁)
          = gammaKernelRect ((UmatRect m hm W e D)ᴴ) c₁₁ a₁
            * gammaKernelRect (UmatRect m hm W e D) a₁ c₂₁ := by
        intro a₁
        have e1 : gammaKernelLim m hm W (configEmbLim e a₁) c₁
            = gammaKernelRect (UmatRect m hm W e D) a₁ c₁₁ := by
          rw [← hc₁]
          exact gammaKernelLimOf_configEmbLim (Umat m hm W) e D a₁ c₁₁
        have e2 : gammaKernelLim m hm W (configEmbLim e a₁) c₂
            = gammaKernelRect (UmatRect m hm W e D) a₁ c₂₁ := by
          rw [← hc₂]
          exact gammaKernelLimOf_configEmbLim (Umat m hm W) e D a₁ c₂₁
        rw [hf_def]
        simp only []
        rw [e1, e2, ← gammaKernelRect_conjTranspose]
      have h1 : ∑ a ∈ s e, f a
          = ∑ a₁ ∈ configsOfTot e n, f (configEmbLim e a₁) :=
        Finset.sum_map _ _ _
      rw [h1]
      refine (Finset.sum_congr rfl (fun a₁ _ => hterm a₁)).trans ?_
      rw [hset e]
      exact (gammaKernelRect_mul _ _ c₁₁ c₂₁).symm
    -- The Gram entries converge to the identity matrix.
    have hentry : ∀ i j : Fin D, Tendsto
        (fun e => ((UmatRect m hm W e D)ᴴ * UmatRect m hm W e D) i j)
        atTop (𝓝 ((1 : Matrix (Fin D) (Fin D) ℂ) i j)) := by
      intro i j
      have hlim : ⟪W (shellONB m hm i.val), W (shellONB m hm j.val)⟫_ℂ
          = (1 : Matrix (Fin D) (Fin D) ℂ) i j := by
        rw [LinearIsometryEquiv.inner_map_map, Matrix.one_apply]
        by_cases h : i = j
        · rw [if_pos h,
            orthonormal_iff_ite.mp (shellONB m hm).orthonormal i.val j.val,
            if_pos (Fin.ext_iff.1 h)]
        · rw [if_neg h,
            orthonormal_iff_ite.mp (shellONB m hm).orthonormal i.val j.val,
            if_neg (fun hv => h (Fin.ext hv))]
      rw [← hlim]
      refine Filter.Tendsto.congr (fun e => ?_)
        (Umat_partial_tendsto m hm W W i.val j.val)
      have h2 : (∑ k : Fin e, star (Umat m hm W k.val i.val)
            * Umat m hm W k.val j.val)
          = ∑ k ∈ Finset.range e, star (Umat m hm W k i.val)
            * Umat m hm W k j.val :=
        Fin.sum_univ_eq_sum_range
          (fun k => star (Umat m hm W k i.val) * Umat m hm W k j.val) e
      rw [UmatGram_apply, h2]
    have hval : gammaKernelRect (1 : Matrix (Fin D) (Fin D) ℂ) c₁₁ c₂₁
        = if c₁ = c₂ then 1 else 0 := by
      rw [gammaKernelRect_eq, gammaKernel_one]
      by_cases h : c₁ = c₂
      · have hcc : c₁₁ = c₂₁ :=
          (configEmbLim D).injective (hc₁.trans (h.trans hc₂.symm))
        rw [if_pos h, if_pos hcc]
      · have hcc : c₁₁ ≠ c₂₁ := fun hc =>
          h (hc₁.symm.trans ((congrArg (configEmbLim D) hc).trans hc₂))
        rw [if_neg h, if_neg hcc]
    have hL : Tendsto (fun e => ∑ a ∈ s e, f a) atTop
        (𝓝 (if c₁ = c₂ then 1 else 0)) := by
      have hT := gammaKernelRect_tendsto_of_tendsto
        (fun e => (UmatRect m hm W e D)ᴴ * UmatRect m hm W e D)
        (1 : Matrix (Fin D) (Fin D) ℂ) hentry c₁₁ c₂₁
      rw [hval] at hT
      exact Filter.Tendsto.congr (fun e => (hpartial e).symm) hT
    exact tsum_eq_of_tendsto_sum_exhaustion hf s hmono hcov hL
  · -- Different totals: every term vanishes.
    have hzero : ∀ c', f c' = 0 := by
      intro c'
      by_cases h' : totLim c' = totLim c₁
      · have h2 : totLim c' ≠ totLim c₂ := fun hh => htot (h'.symm.trans hh)
        rw [hf_def]
        simp only []
        rw [gammaKernelLim_of_tot_ne m hm W c' c₂ h2, mul_zero]
      · rw [hf_def]
        simp only []
        rw [gammaKernelLim_of_tot_ne m hm W c' c₁ h', star_zero, zero_mul]
    have hcc : c₁ ≠ c₂ := fun h => htot (by rw [h])
    rw [if_neg hcc]
    exact (tsum_congr hzero).trans tsum_zero

/-- **Mid Parseval limit (T1):** the truncated matrix product of
two one-particle matrices converges to the matrix of the composite
unitary. -/
theorem Umat_partial_tendsto_mid (m : ℝ) (hm : 0 < m)
    (W₁ W₂ : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (i j : ℕ) :
    Tendsto (fun e => ∑ k ∈ Finset.range e, Umat m hm W₂ i k
        * Umat m hm W₁ k j) atTop
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
      = Umat m hm W₂ i k := by
    have h3 : ⟪W₂.symm (shellONB m hm i), shellONB m hm k⟫_ℂ
        = ⟪W₂ (W₂.symm (shellONB m hm i)), W₂ (shellONB m hm k)⟫_ℂ :=
      (LinearIsometryEquiv.inner_map_map W₂ _ _).symm
    rw [h3, LinearIsometryEquiv.apply_symm_apply]
    rfl
  rw [e1]
  rfl

/-- **Functor law at the limit kernel (T1):**
`Γ(W₁.trans W₂) = Γ(W₂) ∘ Γ(W₁)` at the kernel level — the kernel
of the composite is the `ℓ²` matrix product of the kernels. Proved
by exhaustion exactly as L3′: partial sums are the finite
rectangular composition law (§4), and the entries converge by the
mid Parseval limit above. -/
theorem gammaKernelLim_comp (m : ℝ) (hm : 0 < m)
    (W₁ W₂ : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (c' c : ConfigLim) :
    gammaKernelLim m hm (W₁.trans W₂) c' c
      = ∑' c'', gammaKernelLim m hm W₂ c' c''
        * gammaKernelLim m hm W₁ c'' c := by
  classical
  set f : ConfigLim → ℂ := fun c'' => gammaKernelLim m hm W₂ c' c''
    * gammaKernelLim m hm W₁ c'' c with hf_def
  have hf : Summable f := summable_mul_of_summable_sq
    (gammaKernelLim_summable_row m hm W₂ c')
    (gammaKernelLim_summable_col m hm W₁ c)
  by_cases htot : totLim c' = totLim c
  · obtain ⟨d', c'₀, hc'₀⟩ := config_factor c'
    obtain ⟨d, c₀, hc₀⟩ := config_factor c
    set n := totLim c with hn
    set s : ℕ → Finset ConfigLim := fun e =>
      (configsOfTot e n).map (configEmbLim e) with hs_def
    have hmono : Monotone s := by
      intro e₁ e₂ he a ha
      simp only [hs_def, Finset.mem_map] at ha ⊢
      obtain ⟨a₁, ha₁, rfl⟩ := ha
      refine ⟨configEmb he a₁, ?_, ?_⟩
      · rw [mem_configsOfTot] at ha₁ ⊢
        rwa [tot_configEmb]
      · exact configEmbLim_configEmb he a₁
    have hcov : ∀ a, f a ≠ 0 → ∃ e, a ∈ s e := by
      intro a ha
      have ha' : gammaKernelLim m hm W₂ c' a
          * gammaKernelLim m hm W₁ a c ≠ 0 := ha
      have ha₁ : gammaKernelLim m hm W₁ a c ≠ 0 :=
        (mul_ne_zero_iff.1 ha').2
      have hta : totLim a = n := by
        by_contra hne
        exact ha₁ (gammaKernelLim_of_tot_ne m hm W₁ a c hne)
      obtain ⟨dd, a₀, ha₀⟩ := config_factor a
      refine ⟨dd, ?_⟩
      simp only [hs_def, Finset.mem_map]
      refine ⟨configEmb (le_refl dd) a₀, ?_, ?_⟩
      · rw [mem_configsOfTot, tot_configEmb]
        have h3 : totLim (configEmbLim dd a₀) = tot a₀ :=
          totLim_configEmbLim dd a₀
        rw [ha₀] at h3
        rw [← h3, hta]
      · rw [configEmbLim_configEmb, ha₀]
    have hpartial : ∀ e, ∑ a ∈ s e, f a
        = gammaKernelRect (UmatRect m hm W₂ d' e * UmatRect m hm W₁ e d)
            c'₀ c₀ := by
      intro e
      have hterm : ∀ a₁ : Config e, f (configEmbLim e a₁)
          = gammaKernelRect (UmatRect m hm W₂ d' e) c'₀ a₁
            * gammaKernelRect (UmatRect m hm W₁ e d) a₁ c₀ := by
        intro a₁
        have e1 : gammaKernelLim m hm W₂ c' (configEmbLim e a₁)
            = gammaKernelRect (UmatRect m hm W₂ d' e) c'₀ a₁ := by
          rw [← hc'₀]
          exact gammaKernelLimOf_configEmbLim (Umat m hm W₂) d' e c'₀ a₁
        have e2 : gammaKernelLim m hm W₁ (configEmbLim e a₁) c
            = gammaKernelRect (UmatRect m hm W₁ e d) a₁ c₀ := by
          rw [← hc₀]
          exact gammaKernelLimOf_configEmbLim (Umat m hm W₁) e d a₁ c₀
        rw [hf_def]
        simp only []
        rw [e1, e2]
      have hset : configsOfTot e n = configsOfTot e (tot c₀) := by
        have h1 : totLim (configEmbLim d c₀) = tot c₀ :=
          totLim_configEmbLim d c₀
        rw [hc₀] at h1
        congr 1
      have h1 : ∑ a ∈ s e, f a
          = ∑ a₁ ∈ configsOfTot e n, f (configEmbLim e a₁) :=
        Finset.sum_map _ _ _
      rw [h1]
      refine (Finset.sum_congr rfl (fun a₁ _ => hterm a₁)).trans ?_
      rw [hset]
      exact (gammaKernelRect_mul _ _ c'₀ c₀).symm
    have hentry : ∀ i : Fin d', ∀ j : Fin d, Tendsto
        (fun e => (UmatRect m hm W₂ d' e * UmatRect m hm W₁ e d) i j)
        atTop (𝓝 (UmatRect m hm (W₁.trans W₂) d' d i j)) := by
      intro i j
      have hmul : ∀ e, (UmatRect m hm W₂ d' e * UmatRect m hm W₁ e d) i j
          = ∑ k : Fin e, Umat m hm W₂ i.val k.val
            * Umat m hm W₁ k.val j.val := by
        intro e
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro k _
        rfl
      have hlim : ⟪shellONB m hm i.val,
            (W₁.trans W₂) (shellONB m hm j.val)⟫_ℂ
          = UmatRect m hm (W₁.trans W₂) d' d i j := rfl
      rw [← hlim]
      refine Filter.Tendsto.congr (fun e => ?_)
        (Umat_partial_tendsto_mid m hm W₁ W₂ i.val j.val)
      rw [hmul e]
      exact (Fin.sum_univ_eq_sum_range
        (fun k => Umat m hm W₂ i.val k * Umat m hm W₁ k j.val) e).symm
    have hL : Tendsto (fun e => ∑ a ∈ s e, f a) atTop
        (𝓝 (gammaKernelLim m hm (W₁.trans W₂) c' c)) := by
      have hT := gammaKernelRect_tendsto_of_tendsto
        (fun e => UmatRect m hm W₂ d' e * UmatRect m hm W₁ e d)
        (UmatRect m hm (W₁.trans W₂) d' d) hentry c'₀ c₀
      have hback : gammaKernelRect (UmatRect m hm (W₁.trans W₂) d' d)
            c'₀ c₀
          = gammaKernelLim m hm (W₁.trans W₂) c' c := by
        rw [← hc'₀, ← hc₀]
        exact (gammaKernelLimOf_configEmbLim
          (Umat m hm (W₁.trans W₂)) d' d c'₀ c₀).symm
      rw [hback] at hT
      exact Filter.Tendsto.congr (fun e => (hpartial e).symm) hT
    exact (tsum_eq_of_tendsto_sum_exhaustion hf s hmono hcov hL).symm
  · -- Different totals: both sides vanish.
    have hLHS : gammaKernelLim m hm (W₁.trans W₂) c' c = 0 :=
      gammaKernelLim_of_tot_ne m hm (W₁.trans W₂) c' c htot
    rw [hLHS]
    have hzero : ∀ a, f a = 0 := by
      intro a
      by_cases h' : totLim c' = totLim a
      · have h2 : totLim a ≠ totLim c := fun hh => htot (h'.trans hh)
        rw [hf_def]
        simp only []
        rw [gammaKernelLim_of_tot_ne m hm W₁ a c h2, mul_zero]
      · rw [hf_def]
        simp only []
        rw [gammaKernelLim_of_tot_ne m hm W₂ c' a h', zero_mul]
    exact ((tsum_congr hzero).trans tsum_zero).symm

/-! ## 7. Assembly: the packaged operator

The column vectors of the kernel are `ℓ²` vectors (§5); the packaged
operator is defined on the finite-particle domain as the
corresponding finite combination, proved isometric there from L3′,
and extended to the whole space by `extendOfIsometry`. -/

/-- The `c`-th column of the limit kernel, as a Fock vector (T1). -/
noncomputable def colVec (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (c : ConfigLim) :
    BosonicFockLim :=
  ⟨fun c' => gammaKernelLim m hm W c' c, memℓp_gen (by
    have h := gammaKernelLim_summable_col m hm W c
    simpa using h)⟩

/-- Coordinates of a kernel column (T1, definitional). -/
theorem colVec_apply (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (c c' : ConfigLim) :
    colVec m hm W c c' = gammaKernelLim m hm W c' c := rfl

/-- The packaged operator on the finite-particle domain (T1). -/
noncomputable def gammaDomLim (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) :
    DomLim →ₗ[ℂ] BosonicFockLim :=
  (Finsupp.linearCombination ℂ (colVec m hm W)) ∘ₗ bosReprLim.toLinearMap

/-- The packaged operator sends basis vectors to kernel columns
(T1). -/
theorem gammaDomLim_bosEquivLim (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (φ : ConfigLim →₀ ℂ) :
    gammaDomLim m hm W (bosEquivLim φ)
      = Finsupp.linearCombination ℂ (colVec m hm W) φ := by
  unfold gammaDomLim
  rw [LinearMap.comp_apply]
  congr 1
  exact LinearEquiv.symm_apply_apply bosEquivLim φ

/-- Inner product of two kernel columns (T1): L3′ restated. -/
theorem inner_colVec (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (c₁ c₂ : ConfigLim) :
    ⟪colVec m hm W c₁, colVec m hm W c₂⟫_ℂ
      = if c₁ = c₂ then 1 else 0 := by
  calc ⟪colVec m hm W c₁, colVec m hm W c₂⟫_ℂ
      = ∑' c', ⟪gammaKernelLim m hm W c' c₁,
          gammaKernelLim m hm W c' c₂⟫_ℂ := by
        rw [lp.inner_eq_tsum]
        exact tsum_congr (fun c' => by
          rw [colVec_apply m hm W c₁ c', colVec_apply m hm W c₂ c'])
    _ = ∑' c', star (gammaKernelLim m hm W c' c₁)
          * gammaKernelLim m hm W c' c₂ :=
        tsum_congr (fun c' => by
          simp only [RCLike.inner_apply, RCLike.star_def]
          exact mul_comm _ _)
    _ = if c₁ = c₂ then 1 else 0 :=
        gammaKernelLim_column_orthonormal m hm W c₁ c₂

/-- Inner product of a kernel column against a basis vector (T1). -/
theorem inner_colVec_boseELim (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (c₁ c₂ : ConfigLim) :
    ⟪colVec m hm W c₁, boseELim c₂⟫_ℂ
      = star (gammaKernelLim m hm W c₂ c₁) := by
  unfold boseELim
  rw [lp.inner_single_right, colVec_apply, RCLike.inner_apply,
    RCLike.star_def]
  simp

/-- Inner product of a basis vector against a kernel column (T1). -/
theorem inner_boseELim_colVec (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (c₁ c₂ : ConfigLim) :
    ⟪boseELim c₁, colVec m hm W c₂⟫_ℂ
      = gammaKernelLim m hm W c₁ c₂ := by
  unfold boseELim
  rw [lp.inner_single_left, colVec_apply, RCLike.inner_apply]
  simp

/-- A linear combination is its support sum (T1). -/
theorem linearCombination_eq_sum (v : ConfigLim → BosonicFockLim)
    (φ : ConfigLim →₀ ℂ) :
    Finsupp.linearCombination ℂ v φ = ∑ a ∈ φ.support, φ a • v a := by
  rw [Finsupp.linearCombination_apply]
  rfl

/-- **Finite-expansion inner formula (T1):** the inner product of
two finite combinations is the finite double sum of the pairwise
inner products. -/
theorem inner_linearCombination_mixed (v w : ConfigLim → BosonicFockLim)
    (φ ψ : ConfigLim →₀ ℂ) :
    ⟪Finsupp.linearCombination ℂ v φ,
        Finsupp.linearCombination ℂ w ψ⟫_ℂ
      = ∑ a ∈ φ.support, ∑ b ∈ ψ.support,
          starRingEnd ℂ (φ a) * (ψ b * ⟪v a, w b⟫_ℂ) := by
  rw [linearCombination_eq_sum, linearCombination_eq_sum, sum_inner]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [inner_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [inner_smul_left, inner_smul_right]

/-- Column combinations: the double sum collapses by L3′ (T1). -/
theorem inner_linearCombination_colVec (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (φ ψ : ConfigLim →₀ ℂ) :
    ⟪Finsupp.linearCombination ℂ (colVec m hm W) φ,
        Finsupp.linearCombination ℂ (colVec m hm W) ψ⟫_ℂ
      = ∑ c ∈ φ.support, starRingEnd ℂ (φ c) * ψ c := by
  rw [inner_linearCombination_mixed]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hterm : ∀ b ∈ ψ.support, starRingEnd ℂ (φ a)
        * (ψ b * ⟪colVec m hm W a, colVec m hm W b⟫_ℂ)
      = starRingEnd ℂ (φ a) * (ψ b * (if a = b then (1 : ℂ) else 0)) := by
    intro b _
    congr 1
    congr 1
    exact inner_colVec m hm W a b
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
theorem inner_gammaDomLim (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (u v : DomLim) :
    ⟪gammaDomLim m hm W u, gammaDomLim m hm W v⟫_ℂ = ⟪u, v⟫_ℂ := by
  obtain ⟨φ, rfl⟩ : ∃ φ, bosEquivLim φ = u :=
    ⟨bosReprLim u, LinearEquiv.apply_symm_apply bosEquivLim u⟩
  obtain ⟨ψ, rfl⟩ : ∃ ψ, bosEquivLim ψ = v :=
    ⟨bosReprLim v, LinearEquiv.apply_symm_apply bosEquivLim v⟩
  have hφ : bosReprLim (bosEquivLim φ) = φ :=
    LinearEquiv.symm_apply_apply bosEquivLim φ
  have hψ : bosReprLim (bosEquivLim ψ) = ψ :=
    LinearEquiv.symm_apply_apply bosEquivLim ψ
  rw [gammaDomLim_bosEquivLim, gammaDomLim_bosEquivLim,
    inner_linearCombination_colVec]
  rw [bosInner_expand_of_subset _ _ φ.support (by rw [hφ])]
  rw [hφ, hψ]

/-- **Adjoint identity on the domain (T1):** against finite-particle
vectors, the packaged operator for `W.symm` is the adjoint of the
one for `W` — the finite double sums agree termwise by the kernel
adjoint identity of §5. -/
theorem inner_gammaDomLim_adjoint (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (u v : DomLim) :
    ⟪gammaDomLim m hm W u, (v : BosonicFockLim)⟫_ℂ
      = ⟪(u : BosonicFockLim), gammaDomLim m hm W.symm v⟫_ℂ := by
  obtain ⟨φ, rfl⟩ : ∃ φ, bosEquivLim φ = u :=
    ⟨bosReprLim u, LinearEquiv.apply_symm_apply bosEquivLim u⟩
  obtain ⟨ψ, rfl⟩ : ∃ ψ, bosEquivLim ψ = v :=
    ⟨bosReprLim v, LinearEquiv.apply_symm_apply bosEquivLim v⟩
  rw [gammaDomLim_bosEquivLim, gammaDomLim_bosEquivLim, bosEquivLim_coe,
    bosEquivLim_coe, inner_linearCombination_mixed,
    inner_linearCombination_mixed]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [inner_colVec_boseELim, inner_boseELim_colVec,
    gammaKernelLim_symm]

/-- The finite-particle domain is dense, as a set (T1). -/
theorem dense_DomLim : Dense (DomLim : Set BosonicFockLim) := by
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
    DomLim_topologicalClosure]
  ext x
  simp

/-- Density in `DenseRange` form for the subtype inclusion (T1). -/
theorem denseRange_subtype_DomLim :
    DenseRange (DomLim.subtype : ↥DomLim →ₗ[ℂ] BosonicFockLim) := by
  have h1 : Set.range (⇑(DomLim.subtype))
      = (DomLim : Set BosonicFockLim) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  show Dense (Set.range ⇑(DomLim.subtype))
  rw [h1]
  exact dense_DomLim

/-- The packaged operator preserves norms on the domain (T1). -/
theorem norm_gammaDomLim (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (u : DomLim) :
    ‖gammaDomLim m hm W u‖ = ‖DomLim.subtype u‖ := by
  have h := inner_gammaDomLim m hm W u u
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖gammaDomLim m hm W u‖ ^ 2 = ‖(u : BosonicFockLim)‖ ^ 2 := by
    exact_mod_cast h
  calc ‖gammaDomLim m hm W u‖
      = Real.sqrt (‖gammaDomLim m hm W u‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖(u : BosonicFockLim)‖ ^ 2) := by rw [h2]
    _ = ‖(u : BosonicFockLim)‖ := Real.sqrt_sq (norm_nonneg _)
    _ = ‖DomLim.subtype u‖ := rfl

/-- **The packaged operator (T1):** `Γ(W)` as a linear isometry of
the whole bosonic Fock space, extended from the finite-particle
domain by `extendOfIsometry`. -/
noncomputable def gammaIsometry (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) :
    BosonicFockLim →ₗᵢ[ℂ] BosonicFockLim :=
  (gammaDomLim m hm W).extendOfIsometry denseRange_subtype_DomLim
    (fun u => norm_gammaDomLim m hm W u)

/-- The extension agrees with the domain operator on the domain
(T1). -/
theorem gammaIsometry_apply_dom (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (u : DomLim) :
    gammaIsometry m hm W (u : BosonicFockLim) = gammaDomLim m hm W u :=
  LinearMap.extendOfIsometry_eq _ _ _ _

/-- **Adjoint identity on the whole space (T1):** `Γ(W.symm)` is
the adjoint of `Γ(W)`. Proved from the domain identity by two
closed-set density arguments. -/
theorem gammaIsometry_adjoint (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (x y : BosonicFockLim) :
    ⟪gammaIsometry m hm W x, y⟫_ℂ
      = ⟪x, gammaIsometry m hm W.symm y⟫_ℂ := by
  have key : ∀ v : DomLim, ∀ x : BosonicFockLim,
      ⟪gammaIsometry m hm W x, (v : BosonicFockLim)⟫_ℂ
        = ⟪x, gammaIsometry m hm W.symm (v : BosonicFockLim)⟫_ℂ := by
    intro v
    have hclosed : IsClosed {x : BosonicFockLim |
        ⟪gammaIsometry m hm W x, (v : BosonicFockLim)⟫_ℂ
          = ⟪x, gammaIsometry m hm W.symm (v : BosonicFockLim)⟫_ℂ} :=
      isClosed_eq
        ((gammaIsometry m hm W).continuous.inner continuous_const)
        (continuous_id.inner continuous_const)
    have hsub : (DomLim : Set BosonicFockLim)
        ⊆ {x : BosonicFockLim |
          ⟪gammaIsometry m hm W x, (v : BosonicFockLim)⟫_ℂ
            = ⟪x, gammaIsometry m hm W.symm (v : BosonicFockLim)⟫_ℂ} := by
      intro x hx
      show ⟪gammaIsometry m hm W ((⟨x, hx⟩ : DomLim) : BosonicFockLim),
          (v : BosonicFockLim)⟫_ℂ
        = ⟪((⟨x, hx⟩ : DomLim) : BosonicFockLim),
          gammaIsometry m hm W.symm (v : BosonicFockLim)⟫_ℂ
      rw [gammaIsometry_apply_dom, gammaIsometry_apply_dom]
      exact inner_gammaDomLim_adjoint m hm W ⟨x, hx⟩ v
    have hfin := closure_minimal hsub hclosed
    rw [dense_DomLim.closure_eq] at hfin
    exact fun x => hfin (Set.mem_univ x)
  have hclosed : IsClosed {y : BosonicFockLim |
      ⟪gammaIsometry m hm W x, y⟫_ℂ
        = ⟪x, gammaIsometry m hm W.symm y⟫_ℂ} :=
    isClosed_eq (continuous_const.inner continuous_id)
      (continuous_const.inner (gammaIsometry m hm W.symm).continuous)
  have hsub : (DomLim : Set BosonicFockLim)
      ⊆ {y : BosonicFockLim | ⟪gammaIsometry m hm W x, y⟫_ℂ
          = ⟪x, gammaIsometry m hm W.symm y⟫_ℂ} := by
    intro y hy
    exact key ⟨y, hy⟩ x
  have hfin := closure_minimal hsub hclosed
  rw [dense_DomLim.closure_eq] at hfin
  exact hfin (Set.mem_univ y)

/-- The packaged isometry is surjective (T1): its inverse is the
packaged operator of `W.symm`, by the adjoint identity and inner
preservation. -/
theorem gammaIsometry_surjective (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) :
    Function.Surjective (gammaIsometry m hm W) := by
  intro y
  refine ⟨gammaIsometry m hm W.symm y, ?_⟩
  refine ext_inner_right ℂ (fun v => ?_)
  rw [gammaIsometry_adjoint, LinearIsometry.inner_map_map]

/-- **The packaged unitary (T1):** `Γ(W)` as a unitary operator
(a linear isometry equivalence) on the bosonic Fock space. -/
noncomputable def gammaFock (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) :
    BosonicFockLim ≃ₗᵢ[ℂ] BosonicFockLim :=
  LinearIsometryEquiv.ofSurjective (gammaIsometry m hm W)
    (gammaIsometry_surjective m hm W)

/-! ## §8. The packaged Poincaré action -/

/-- Pairing with a basis vector reads off the coordinate (T1). -/
theorem inner_boseELim_apply (c : ConfigLim) (v : BosonicFockLim) :
    ⟪boseELim c, v⟫_ℂ = v c := by
  unfold boseELim
  rw [lp.inner_single_left, RCLike.inner_apply]
  simp

/-- `gammaFock` applies as its underlying isometry (T1, `rfl`). -/
theorem gammaFock_apply (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (z : BosonicFockLim) :
    gammaFock m hm W z = gammaIsometry m hm W z := rfl

/-- The packaged operator sends a basis vector to its kernel
column (T1). -/
theorem gammaIsometry_boseELim (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (c : ConfigLim) :
    gammaIsometry m hm W (boseELim c) = colVec m hm W c := by
  have hmem : boseELim c
      = ((⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩ : DomLim)
        : BosonicFockLim) := rfl
  rw [hmem, gammaIsometry_apply_dom, ← bosEquivLim_basis,
    gammaDomLim_bosEquivLim, Finsupp.linearCombination_single]
  simp

/-- **Coordinate formula (T1):** the `c'`-coordinate of `Γ(W) z`
is the kernel transform of the coordinates of `z`. -/
theorem gammaIsometry_coordinate (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (z : BosonicFockLim)
    (c' : ConfigLim) :
    (gammaIsometry m hm W z) c'
      = ∑' c'', gammaKernelLim m hm W c' c'' * z c'' := by
  have h1 : ⟪boseELim c', gammaIsometry m hm W z⟫_ℂ
      = ⟪gammaIsometry m hm W.symm (boseELim c'), z⟫_ℂ := by
    have h := gammaIsometry_adjoint m hm W.symm (boseELim c') z
    rw [LinearIsometryEquiv.symm_symm] at h
    exact h.symm
  rw [← inner_boseELim_apply c' (gammaIsometry m hm W z), h1,
    gammaIsometry_boseELim, lp.inner_eq_tsum]
  refine tsum_congr (fun c'' => ?_)
  rw [colVec_apply, gammaKernelLim_symm, RCLike.inner_apply]
  simp only [RCLike.star_def]
  rw [Complex.conj_conj, mul_comm]

/-- The coordinate formula for the packaged unitary (T1). -/
theorem gammaFock_coordinate (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (z : BosonicFockLim)
    (c' : ConfigLim) :
    (gammaFock m hm W z) c'
      = ∑' c'', gammaKernelLim m hm W c' c'' * z c'' := by
  rw [gammaFock_apply]
  exact gammaIsometry_coordinate m hm W z c'

/-- The packaged operator maps kernel columns to kernel columns,
with the composed one-particle operator (T1) — the computational
heart of the functor law. -/
theorem gammaIsometry_colVec (m : ℝ) (hm : 0 < m)
    (W₁ W₂ : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (c : ConfigLim) :
    gammaIsometry m hm W₂ (colVec m hm W₁ c)
      = colVec m hm (W₁.trans W₂) c := by
  apply Subtype.ext
  funext c'
  calc (gammaIsometry m hm W₂ (colVec m hm W₁ c)) c'
      = ∑' c'', gammaKernelLim m hm W₂ c' c''
          * gammaKernelLim m hm W₁ c'' c := by
        rw [gammaIsometry_coordinate]
        exact tsum_congr (fun c'' => by rw [colVec_apply m hm W₁ c c''])
    _ = gammaKernelLim m hm (W₁.trans W₂) c' c :=
        (gammaKernelLim_comp m hm W₁ W₂ c' c).symm
    _ = (colVec m hm (W₁.trans W₂) c) c' :=
        (colVec_apply m hm (W₁.trans W₂) c c').symm

/-- The domain operator is the finite combination of columns at
the coordinates of `bosReprLim u` (T1). -/
theorem gammaDomLim_apply (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (u : DomLim) :
    gammaDomLim m hm W u
      = Finsupp.linearCombination ℂ (colVec m hm W) (bosReprLim u) := rfl

/-- Composition on the domain (T1): `Γ(W₂)` of a finite column
combination is the finite combination of the composed columns. -/
theorem gammaIsometry_comp_apply (m : ℝ) (hm : 0 < m)
    (W₁ W₂ : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (u : DomLim) :
    gammaIsometry m hm W₂ (gammaDomLim m hm W₁ u)
      = gammaDomLim m hm (W₁.trans W₂) u := by
  rw [gammaDomLim_apply, gammaDomLim_apply, linearCombination_eq_sum,
    map_sum, linearCombination_eq_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [map_smul, gammaIsometry_colVec]

/-- **Functor law on the whole space (T1):** the packaged
operator of a composite is the composite of the packaged
operators, by density from the domain computation. -/
theorem gammaIsometry_trans (m : ℝ) (hm : 0 < m)
    (W₁ W₂ : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (z : BosonicFockLim) :
    gammaIsometry m hm (W₁.trans W₂) z
      = gammaIsometry m hm W₂ (gammaIsometry m hm W₁ z) := by
  have hclosed : IsClosed {z : BosonicFockLim |
      gammaIsometry m hm (W₁.trans W₂) z
        = gammaIsometry m hm W₂ (gammaIsometry m hm W₁ z)} :=
    isClosed_eq (gammaIsometry m hm (W₁.trans W₂)).continuous
      ((gammaIsometry m hm W₂).continuous.comp
        (gammaIsometry m hm W₁).continuous)
  have hsub : (DomLim : Set BosonicFockLim) ⊆ {z : BosonicFockLim |
      gammaIsometry m hm (W₁.trans W₂) z
        = gammaIsometry m hm W₂ (gammaIsometry m hm W₁ z)} := by
    intro z hz
    show gammaIsometry m hm (W₁.trans W₂) ((⟨z, hz⟩ : DomLim)
        : BosonicFockLim)
      = gammaIsometry m hm W₂
          (gammaIsometry m hm W₁ ((⟨z, hz⟩ : DomLim) : BosonicFockLim))
    rw [gammaIsometry_apply_dom, gammaIsometry_apply_dom]
    exact (gammaIsometry_comp_apply m hm W₁ W₂ ⟨z, hz⟩).symm
  have hfin := closure_minimal hsub hclosed
  rw [dense_DomLim.closure_eq] at hfin
  exact hfin (Set.mem_univ z)

/-- **Functor law for the packaged unitary (T1):**
`Γ(W₁ ⋙ W₂) = Γ(W₁) ⋙ Γ(W₂)` in `LinearIsometryEquiv.trans`
order. -/
theorem gammaFock_comp (m : ℝ) (hm : 0 < m)
    (W₁ W₂ : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) :
    gammaFock m hm (W₁.trans W₂)
      = (gammaFock m hm W₁).trans (gammaFock m hm W₂) := by
  apply LinearIsometryEquiv.ext
  intro z
  rw [LinearIsometryEquiv.trans_apply, gammaFock_apply, gammaFock_apply,
    gammaFock_apply]
  exact gammaIsometry_trans m hm W₁ W₂ z

/-- The packaged operator of the identity is the identity (T1). -/
theorem gammaFock_one (m : ℝ) (hm : 0 < m) :
    gammaFock m hm (1 : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) = 1 := by
  apply LinearIsometryEquiv.ext
  intro z
  change gammaFock m hm 1 z = z
  apply Subtype.ext
  funext c'
  rw [gammaFock_coordinate]
  rw [tsum_eq_single c' (fun b hb => by
    rw [gammaKernelLim_one, if_neg (fun h => hb h.symm), zero_mul])]
  rw [gammaKernelLim_one]
  simp

/-- The kernel against the vacuum configuration is the Kronecker
delta (T1): every one-particle unitary fixes the vacuum column. -/
theorem gammaKernelLim_zero_config (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (c' : ConfigLim) :
    gammaKernelLim m hm W c' 0 = if c' = 0 then 1 else 0 := by
  by_cases hc : c' = 0
  · subst hc
    rw [if_pos rfl]
    have h00 : configEmbLim 0 (0 : Config 0) = (0 : ConfigLim) := by
      ext i
      simp [configEmbLim]
    rw [← h00]
    show gammaKernelLimOf (Umat m hm W) (configEmbLim 0 (0 : Config 0))
      (configEmbLim 0 (0 : Config 0)) = 1
    rw [gammaKernelLimOf_configEmbLim]
    simp [gammaKernelRect, perMinorRect, normFactor, Matrix.permanent]
    show (∑ x : Equiv.Perm (Fin 0), ∏ x_1 : Fin 0,
      Umat m hm W ↑(configEnum 0 0 (x x_1)) ↑(configEnum 0 0 x_1)) = 1
    simp
  · rw [if_neg hc]
    apply gammaKernelLim_of_tot_ne
    have htot0 : totLim (0 : ConfigLim) = 0 := by simp [totLim]
    rw [htot0]
    intro hcon
    apply hc
    have hsum : totLim c' = ∑ i ∈ c'.support, c' i := rfl
    ext i
    by_cases hi : i ∈ c'.support
    · exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => Nat.zero_le _)).1 (hsum ▸ hcon) i hi
    · exact Finsupp.notMem_support_iff.1 hi

/-- **Vacuum invariance (T1):** every packaged operator fixes the
Fock vacuum. -/
theorem gammaFock_vacuum (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) :
    gammaFock m hm W boseVacLim = boseVacLim := by
  have hvac : ∀ c, (boseVacLim : BosonicFockLim) c
      = if c = 0 then 1 else 0 := by
    intro c
    rw [← inner_boseELim_apply]
    show ⟪boseELim c, boseELim 0⟫_ℂ = if c = 0 then 1 else 0
    exact orthonormal_iff_ite.1 boseELim_orthonormal c 0
  apply Subtype.ext
  funext c'
  rw [gammaFock_coordinate]
  rw [tsum_eq_single 0 (fun b hb => by
    rw [hvac b, if_neg hb, mul_zero])]
  rw [gammaKernelLim_zero_config, hvac c', hvac 0, if_pos rfl, mul_one]

/-- **The packaged Poincaré representation, bosonic (T1):**
`Γ` of the one-particle Poincaré action `shellU1`. -/
noncomputable def gammaFockU1 (m : ℝ) (hm : 0 < m) (g : RPoincare) :
    BosonicFockLim ≃ₗᵢ[ℂ] BosonicFockLim :=
  gammaFock m hm (shellU1 m hm g)

/-- **Representation law, bosonic (T1):** the packaged action is
a homomorphism of `RPoincare` in the corrected order forced by
`LinearIsometryEquiv.trans`: `Γ(g₁ g₂) = Γ(g₂) ⋙ Γ(g₁)`. -/
theorem gammaFockU1_mul (m : ℝ) (hm : 0 < m) (g₁ g₂ : RPoincare) :
    gammaFockU1 m hm (g₁ * g₂)
      = (gammaFockU1 m hm g₂).trans (gammaFockU1 m hm g₁) := by
  unfold gammaFockU1
  rw [shellU1_mul]
  exact gammaFock_comp m hm (shellU1 m hm g₂) (shellU1 m hm g₁)

/-- The packaged action of the group identity is the identity
(T1). -/
theorem gammaFockU1_one (m : ℝ) (hm : 0 < m) :
    gammaFockU1 m hm 1 = 1 := by
  unfold gammaFockU1
  rw [shellU1_one]
  exact gammaFock_one m hm

/-- The limit basis vectors as a Hilbert basis of the bosonic
Fock space (T1), assembled from the corpus's orthonormality and
the density of `DomLim`. -/
noncomputable def boseBasisLim : HilbertBasis ConfigLim ℂ BosonicFockLim :=
  HilbertBasis.mk boseELim_orthonormal
    (top_le_iff.mpr DomLim_topologicalClosure)

/-- The Hilbert basis is the basis-vector family (T1). -/
theorem boseBasisLim_coe : ⇑boseBasisLim = boseELim :=
  HilbertBasis.coe_mk _ _

/-- The **closed `n`-particle sector** (T1, definition): the
vectors whose coordinates vanish off total occupation `n`. This
is the closure of `sectorSubLim n`, proved below. -/
def closedSectorLim (n : ℕ) : Set BosonicFockLim :=
  {z | ∀ c', totLim c' ≠ n → z c' = 0}

/-- The packaged operator preserves the closed sector (T1), by
the coordinate formula and the total-occupation guard of the
kernel. -/
theorem gammaFock_mem_closedSectorLim (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (n : ℕ) {z : BosonicFockLim}
    (hz : z ∈ closedSectorLim n) :
    gammaFock m hm W z ∈ closedSectorLim n := by
  intro c' hc'
  rw [gammaFock_coordinate]
  refine (tsum_congr (fun c'' => ?_)).trans tsum_zero
  by_cases hcc : totLim c' = totLim c''
  · rw [hz c'' (fun h => hc' (hcc.trans h)), mul_zero]
  · rw [gammaKernelLim_of_tot_ne m hm W c' c'' hcc, zero_mul]

/-- The corpus sector is contained in the closed sector (T1), by
span induction. -/
theorem sectorSubLim_subset_closedSectorLim (n : ℕ) :
    (sectorSubLim n : Set BosonicFockLim) ⊆ closedSectorLim n := by
  intro z hz
  have hz' : z ∈ Submodule.span ℂ
      (boseELim '' {c : ConfigLim | totLim c = n}) := hz
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz'
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := hx
    intro c' hc'
    rw [← inner_boseELim_apply]
    have h := orthonormal_iff_ite.1 boseELim_orthonormal c' c
    rwa [if_neg (fun h : c' = c => hc' ((h ▸ hc) : totLim c' = n))] at h
  · intro c' _
    rfl
  · intro x y _ _ hx hy
    intro c' hc'
    have hxx : x c' = 0 := hx c' hc'
    have hyy : y c' = 0 := hy c' hc'
    have hxy : (x + y) c' = x c' + y c' := Complex.ext rfl rfl
    rw [hxy, hxx, hyy, add_zero]
  · intro a x _ hx
    intro c' hc'
    have hxx : x c' = 0 := hx c' hc'
    have hax : (a • x) c' = a * x c' := Complex.ext rfl rfl
    rw [hax, hxx, mul_zero]

/-- The closed sector is closed (T1): it is an intersection of
coordinate kernels. -/
theorem isClosed_closedSectorLim (n : ℕ) :
    IsClosed (closedSectorLim n) := by
  have heq : closedSectorLim n
      = ⋂ c', ⋂ _ : totLim c' ≠ n,
          {z : BosonicFockLim | ⟪boseELim c', z⟫_ℂ = 0} := by
    ext z
    simp [closedSectorLim, inner_boseELim_apply, Set.mem_iInter]
  rw [heq]
  exact isClosed_iInter (fun c' => isClosed_iInter (fun _ =>
    IsClosed.preimage (continuous_const.inner continuous_id)
      isClosed_singleton))

/-- The closed sector is contained in the closure of the corpus
sector (T1): the Hilbert-basis partial sums of a vector in the
closed sector lie in `sectorSubLim n` and converge to it. -/
theorem closedSectorLim_subset_closure (n : ℕ) :
    closedSectorLim n ⊆ closure (sectorSubLim n : Set BosonicFockLim) := by
  intro z hz
  have hr : ∀ c, (boseBasisLim.repr z) c = z c := by
    intro c
    rw [HilbertBasis.repr_apply_apply, boseBasisLim_coe,
      inner_boseELim_apply]
  have hsum : HasSum (fun c : ConfigLim => z c • boseELim c) z := by
    have h0 := boseBasisLim.hasSum_repr z
    simpa only [hr, boseBasisLim_coe] using h0
  rw [mem_closure_iff]
  intro o ho hzo
  have hev : ∀ᶠ F : Finset ConfigLim in atTop,
      (∑ c ∈ F, z c • boseELim c) ∈ o :=
    hsum.eventually (ho.mem_nhds hzo)
  obtain ⟨F₀, hF₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨∑ c ∈ F₀, z c • boseELim c, hF₀ F₀ le_rfl, ?_⟩
  apply sum_mem
  intro c _
  by_cases hc : totLim c = n
  · exact Submodule.smul_mem _ _ (boseELim_mem_sector hc)
  · rw [hz c hc, zero_smul]
    exact Submodule.zero_mem _

/-- **Sector preservation (T1):** the packaged operator maps
the closure of the `n`-particle sector into itself. -/
theorem gammaFock_mem_sectorClosure (m : ℝ) (hm : 0 < m)
    (W : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) (n : ℕ) (z : BosonicFockLim)
    (hz : z ∈ (sectorSubLim n).topologicalClosure) :
    gammaFock m hm W z ∈ (sectorSubLim n).topologicalClosure := by
  have hz2 : z ∈ closure (sectorSubLim n : Set BosonicFockLim) := by
    have h : z ∈ ((sectorSubLim n).topologicalClosure
      : Set BosonicFockLim) := hz
    rwa [Submodule.topologicalClosure_coe] at h
  have hzn : z ∈ closedSectorLim n :=
    closure_minimal (sectorSubLim_subset_closedSectorLim n)
      (isClosed_closedSectorLim n) hz2
  have hfin : gammaFock m hm W z
      ∈ ((sectorSubLim n).topologicalClosure : Set BosonicFockLim) := by
    rw [Submodule.topologicalClosure_coe]
    exact closedSectorLim_subset_closure n
      (gammaFock_mem_closedSectorLim m hm W n hzn)
  exact hfin

/-- The rectangular-kernel limit at an arbitrary filter (T1);
the proof of `gammaKernelRect_tendsto_of_tendsto` is
filter-general. -/
theorem gammaKernelRect_tendsto_of_tendsto_filter {ι : Type*}
    {l : Filter ι} {e' d' : ℕ} (X : ι → Matrix (Fin e') (Fin d') ℂ)
    (Y : Matrix (Fin e') (Fin d') ℂ)
    (hXY : ∀ i j, Tendsto (fun t => X t i j) l (𝓝 (Y i j)))
    (c'₀ : Config e') (c₀ : Config d') :
    Tendsto (fun t => gammaKernelRect (X t) c'₀ c₀) l
      (𝓝 (gammaKernelRect Y c'₀ c₀)) := by
  by_cases htot : tot c'₀ = tot c₀
  · have hper : ∀ Z : Matrix (Fin e') (Fin d') ℂ, gammaKernelRect Z c'₀ c₀
        = Matrix.permanent
            (fun a b => Z (configEnum e' c'₀ (finCongr htot.symm a))
              (configEnum d' c₀ b))
          / ((normFactor d' c₀ * normFactor e' c'₀ : ℝ) : ℂ) := by
      intro Z
      unfold gammaKernelRect perMinorRect
      rw [dif_pos htot]
    have h1 : (fun t => gammaKernelRect (X t) c'₀ c₀)
        = fun t => Matrix.permanent
            (fun a b => X t (configEnum e' c'₀ (finCongr htot.symm a))
              (configEnum d' c₀ b))
          / ((normFactor d' c₀ * normFactor e' c'₀ : ℝ) : ℂ) :=
      funext (fun t => hper (X t))
    rw [h1, hper Y]
    refine Filter.Tendsto.div ?_ tendsto_const_nhds
      (by exact_mod_cast (mul_pos (normFactor_pos d' c₀)
        (normFactor_pos e' c'₀)).ne')
    unfold Matrix.permanent
    refine tendsto_finsetSum _ (fun σ _ => ?_)
    refine tendsto_finsetProd _ (fun b _ => ?_)
    exact hXY _ _
  · have hper0 : ∀ Z : Matrix (Fin e') (Fin d') ℂ,
        gammaKernelRect Z c'₀ c₀ = 0 := by
      intro Z
      unfold gammaKernelRect perMinorRect
      rw [dif_neg htot, zero_div]
    rw [hper0 Y]
    exact Filter.Tendsto.congr (fun t => (hper0 (X t)).symm)
      tendsto_const_nhds

/-- Entry continuity under translations (T1): the one-particle
matrix entries of the shell basis are continuous at the identity,
from the discharged one-particle strong continuity. -/
theorem Umat_translation_tendsto (m : ℝ) (hm : 0 < m) (i j : ℕ) :
    Tendsto (fun a : Minkowski =>
        Umat m hm (shellU1 m hm ⟨a, 1⟩) i j) (𝓝 0)
      (𝓝 (Umat m hm 1 i j)) := by
  have h : Tendsto (fun a : Minkowski =>
        ⟪shellONB m hm i, shellU1 m hm ⟨a, 1⟩ (shellONB m hm j)⟫_ℂ)
        (𝓝 0) (𝓝 ⟪shellONB m hm i, shellONB m hm j⟫_ℂ) :=
    Filter.Tendsto.inner tendsto_const_nhds
      (shellU1_translation_tendsto m hm (shellONB m hm j))
  exact h

/-- The diagonal kernel is continuous at the identity along
translations, with value `1` (T1): at a fixed configuration the
kernel is a fixed finite permanent in the entries. -/
theorem gammaKernelLim_diag_translation_tendsto (m : ℝ) (hm : 0 < m)
    (c : ConfigLim) :
    Tendsto (fun a : Minkowski =>
        gammaKernelLim m hm (shellU1 m hm ⟨a, 1⟩) c c) (𝓝 0) (𝓝 1) := by
  obtain ⟨d, c₀, hc⟩ := config_factor c
  have heq : ∀ a : Minkowski,
      gammaKernelLim m hm (shellU1 m hm ⟨a, 1⟩) c c
        = gammaKernelRect (fun i j : Fin d =>
            Umat m hm (shellU1 m hm ⟨a, 1⟩) i.val j.val) c₀ c₀ := by
    intro a
    rw [← hc]
    show gammaKernelLimOf (Umat m hm (shellU1 m hm ⟨a, 1⟩))
        (configEmbLim d c₀) (configEmbLim d c₀) = _
    exact gammaKernelLimOf_configEmbLim _ d d c₀ c₀
  have hval : gammaKernelRect (fun i j : Fin d =>
        Umat m hm (1 : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm) i.val j.val)
        c₀ c₀ = 1 := by
    have h1 : gammaKernelLim m hm
          (1 : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm)
          (configEmbLim d c₀) (configEmbLim d c₀)
        = gammaKernelRect (fun i j : Fin d =>
            Umat m hm (1 : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm)
              i.val j.val) c₀ c₀ := by
      show gammaKernelLimOf (Umat m hm 1) (configEmbLim d c₀)
        (configEmbLim d c₀) = _
      exact gammaKernelLimOf_configEmbLim _ d d c₀ c₀
    rw [← h1, gammaKernelLim_one, if_pos rfl]
  have hlim : Tendsto (fun a : Minkowski => gammaKernelRect
        (fun i j : Fin d =>
          Umat m hm (shellU1 m hm ⟨a, 1⟩) i.val j.val) c₀ c₀) (𝓝 0)
      (𝓝 (gammaKernelRect (fun i j : Fin d =>
          Umat m hm (1 : shellLp m hm ≃ₗᵢ[ℂ] shellLp m hm)
            i.val j.val) c₀ c₀)) :=
    gammaKernelRect_tendsto_of_tendsto_filter _ _
      (fun i j => Umat_translation_tendsto m hm i.val j.val) c₀ c₀
  rw [hval] at hlim
  exact Filter.Tendsto.congr (fun a => (heq a).symm) hlim

/-- The packaged action on a basis vector, along a translation
parameter (T1). -/
theorem gammaFockU1_boseELim (m : ℝ) (hm : 0 < m) (a : Minkowski)
    (c : ConfigLim) :
    gammaFockU1 m hm ⟨a, 1⟩ (boseELim c)
      = colVec m hm (shellU1 m hm ⟨a, 1⟩) c := by
  show gammaFock m hm (shellU1 m hm ⟨a, 1⟩) (boseELim c) = _
  rw [gammaFock_apply]
  exact gammaIsometry_boseELim m hm _ c

/-- Basis vectors are strongly continuous under the packaged
translation action (T1): the squared distance is `2 - 2 Re γ`. -/
theorem gammaFockU1_basis_tendsto (m : ℝ) (hm : 0 < m)
    (c : ConfigLim) :
    Tendsto (fun a : Minkowski =>
        ‖gammaFockU1 m hm ⟨a, 1⟩ (boseELim c) - boseELim c‖)
      (𝓝 0) (𝓝 0) := by
  have hnorme : ‖boseELim c‖ = 1 := boseELim_orthonormal.1 c
  have hnorm : ∀ a : Minkowski,
      ‖gammaFockU1 m hm ⟨a, 1⟩ (boseELim c) - boseELim c‖ ^ 2
        = 2 - 2 * (gammaKernelLim m hm (shellU1 m hm ⟨a, 1⟩) c c).re := by
    intro a
    rw [gammaFockU1_boseELim]
    have hnormV : ‖colVec m hm (shellU1 m hm ⟨a, 1⟩) c‖ = 1 := by
      calc ‖colVec m hm (shellU1 m hm ⟨a, 1⟩) c‖
          = ‖gammaIsometry m hm (shellU1 m hm ⟨a, 1⟩)
              (boseELim c)‖ := by rw [gammaIsometry_boseELim]
        _ = ‖boseELim c‖ := LinearIsometry.norm_map _ _
        _ = 1 := hnorme
    calc ‖colVec m hm (shellU1 m hm ⟨a, 1⟩) c - boseELim c‖ ^ 2
        = ‖colVec m hm (shellU1 m hm ⟨a, 1⟩) c‖ ^ 2
          - 2 * (⟪colVec m hm (shellU1 m hm ⟨a, 1⟩) c,
              boseELim c⟫_ℂ).re
          + ‖boseELim c‖ ^ 2 := norm_sub_sq (𝕜 := ℂ) _ _
      _ = 1 - 2 * (star (gammaKernelLim m hm
              (shellU1 m hm ⟨a, 1⟩) c c)).re + 1 := by
          rw [inner_colVec_boseELim, hnormV, hnorme]
          ring
      _ = 2 - 2 * (gammaKernelLim m hm (shellU1 m hm ⟨a, 1⟩)
            c c).re := by
          have hre : ∀ z : ℂ, (star z).re = z.re := fun z => by simp
          rw [hre]
          ring
  have hsq : Tendsto (fun a : Minkowski =>
        ‖gammaFockU1 m hm ⟨a, 1⟩ (boseELim c) - boseELim c‖ ^ 2)
      (𝓝 0) (𝓝 0) := by
    have hre' : Tendsto (fun a : Minkowski =>
        (gammaKernelLim m hm (shellU1 m hm ⟨a, 1⟩) c c).re)
          (𝓝 0) (𝓝 1) := by
      have h := (Complex.continuous_re.tendsto (1 : ℂ)).comp
        (gammaKernelLim_diag_translation_tendsto m hm c)
      exact h.congr (fun a => rfl)
    have key : Tendsto (fun a : Minkowski => 2 - 2
        * (gammaKernelLim m hm (shellU1 m hm ⟨a, 1⟩) c c).re)
          (𝓝 0) (𝓝 0) := by
      have h2 : Tendsto (fun a : Minkowski => (2 : ℝ) - 2
            * (gammaKernelLim m hm (shellU1 m hm ⟨a, 1⟩) c c).re)
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
theorem gammaFockU1_dom_tendsto (m : ℝ) (hm : 0 < m) (u : DomLim) :
    Tendsto (fun a : Minkowski =>
        ‖gammaFockU1 m hm ⟨a, 1⟩ (u : BosonicFockLim)
          - (u : BosonicFockLim)‖) (𝓝 0) (𝓝 0) := by
  obtain ⟨φ, rfl⟩ : ∃ φ, bosEquivLim φ = u :=
    ⟨bosReprLim u, LinearEquiv.apply_symm_apply bosEquivLim u⟩
  refine squeeze_zero
    (g := fun a : Minkowski => ∑ c ∈ φ.support, ‖φ c‖
      * ‖gammaFockU1 m hm ⟨a, 1⟩ (boseELim c) - boseELim c‖)
    (fun a => norm_nonneg _) (fun a => ?_) ?_
  · have hΓ : gammaFockU1 m hm ⟨a, 1⟩
          ((bosEquivLim φ : DomLim) : BosonicFockLim)
        = Finsupp.linearCombination ℂ
            (colVec m hm (shellU1 m hm ⟨a, 1⟩)) φ := by
      show gammaFock m hm (shellU1 m hm ⟨a, 1⟩)
          ((bosEquivLim φ : DomLim) : BosonicFockLim) = _
      rw [gammaFock_apply, gammaIsometry_apply_dom,
        gammaDomLim_bosEquivLim]
    have hu : ((bosEquivLim φ : DomLim) : BosonicFockLim)
        = Finsupp.linearCombination ℂ boseELim φ := bosEquivLim_coe φ
    rw [hΓ, hu, linearCombination_eq_sum, linearCombination_eq_sum,
      ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun c _ => ?_))
    rw [← smul_sub, norm_smul, gammaFockU1_boseELim]
  · have hfac : ∀ c ∈ φ.support, Tendsto (fun a : Minkowski =>
          ‖φ c‖ * ‖gammaFockU1 m hm ⟨a, 1⟩ (boseELim c)
            - boseELim c‖) (𝓝 0) (𝓝 (‖φ c‖ * 0)) :=
      fun c _ => tendsto_const_nhds.mul
        (gammaFockU1_basis_tendsto m hm c)
    have hsum := tendsto_finsetSum φ.support hfac
    simpa using hsum

/-- **Translation strong continuity of the packaged action
(T1):** for every vector `z` of the bosonic Fock space, the
packaged translation action is continuous at the identity —
transported from the discharged one-particle continuity through
the finite-particle density, with the uniform isometry bound. -/
theorem gammaFockU1_translation_tendsto (m : ℝ) (hm : 0 < m)
    (z : BosonicFockLim) :
    Tendsto (fun a : Minkowski => gammaFockU1 m hm ⟨a, 1⟩ z)
      (𝓝 0) (𝓝 z) := by
  rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  have hzmem : z ∈ closure (DomLim : Set BosonicFockLim) := by
    rw [dense_DomLim.closure_eq]
    exact Set.mem_univ z
  obtain ⟨u, hu, hdist⟩ :=
    (Metric.mem_closure_iff.1 hzmem) (ε / 3) (by linarith)
  have hev : ∀ᶠ a : Minkowski in 𝓝 0,
      ‖gammaFockU1 m hm ⟨a, 1⟩ u - u‖ < ε / 3 := by
    have hT := gammaFockU1_dom_tendsto m hm ⟨u, hu⟩
    have h2 := (Metric.tendsto_nhds.1 hT) (ε / 3) (by linarith)
    filter_upwards [h2] with a ha
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at ha
  filter_upwards [hev] with a ha
  have htri : ‖gammaFockU1 m hm ⟨a, 1⟩ z - z‖
      ≤ ‖z - u‖ + ‖gammaFockU1 m hm ⟨a, 1⟩ u - u‖ + ‖u - z‖ := by
    calc ‖gammaFockU1 m hm ⟨a, 1⟩ z - z‖
        = ‖(gammaFockU1 m hm ⟨a, 1⟩ z - gammaFockU1 m hm ⟨a, 1⟩ u)
            + ((gammaFockU1 m hm ⟨a, 1⟩ u - u) + (u - z))‖ := by
          congr 1
          abel
      _ ≤ ‖gammaFockU1 m hm ⟨a, 1⟩ z - gammaFockU1 m hm ⟨a, 1⟩ u‖
            + ‖gammaFockU1 m hm ⟨a, 1⟩ u - u‖ + ‖u - z‖ := by
          have h1 := norm_add_le
            (gammaFockU1 m hm ⟨a, 1⟩ z - gammaFockU1 m hm ⟨a, 1⟩ u)
            ((gammaFockU1 m hm ⟨a, 1⟩ u - u) + (u - z))
          have h2 := norm_add_le (gammaFockU1 m hm ⟨a, 1⟩ u - u)
            (u - z)
          linarith
      _ = ‖z - u‖ + ‖gammaFockU1 m hm ⟨a, 1⟩ u - u‖ + ‖u - z‖ := by
          congr 1
          rw [← map_sub, LinearIsometryEquiv.norm_map]
  have e1 : ‖z - u‖ = dist z u := (dist_eq_norm z u).symm
  have e2 : ‖u - z‖ = dist z u := by
    rw [norm_sub_rev]
    exact (dist_eq_norm z u).symm
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  rw [e1, e2] at htri
  linarith
