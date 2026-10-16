import ThetLogos.BosonicGamma

/-!
# Bosonic Γ functor package (Rung 10, Task 3 — CLOSED)

Companion to `ThetLogos.BosonicGamma`, which defined the bosonic
Γ lift `gammaBos` from permanent minors and proved the kernel formula,
sector preservation, and vacuum preservation — but left Task 3
**PARTIAL**, pricing the missing pieces exactly:

1. the **fiber-permanent counting lemma** (the permanent of the
   fiber-indicator matrix of a configuration enumeration equals
   `∏ i, (c i)!`), needed for `Γ(1) = 1` and the diagonal action;
2. the **permanent Cauchy–Binet identity for repeated indices**,
   needed for multiplicativity and unitarity.

This file proves both, with their consequences:

- `permanent_fiberIndicator_configEnum` — the counting lemma (Task 1
  of the campaign): the permanent of the fiber-indicator matrix of
  `configEnum d c` is `∏ i, (c i)!`;
- `gammaBos_one` — `Γ(1) = 1` on `Dom d` (Task 2);
- `gammaBos_diagonal_basis` — `Γ(diag λ) e_c = (∏ i, λ i ^ (c i)) • e_c`
  (Task 3);
- `perMinor_mul` — permanent Cauchy–Binet for repeated indices, at
  the kernel level, with the exact `1 / ∏ i, (c' i)!` multiplicity
  weights (Task 4);
- `gammaBos_mul` — `Γ(M * N) = Γ(M) ∘ₗ Γ(N)` (Task 5);
- the **unitarity package** (Task 6): `perMinor_conjTranspose`,
  `gammaBos_adjoint` (the inner-product adjoint relation on `Dom d`),
  and the algebraic unitarity identities
  `gammaBos_comp_conjTranspose` / `gammaBos_conjTranspose_comp` with
  the isometry corollary `gammaBos_isometry`.

With this file, Rung 10 Task 3 is closed: `gammaBos` is a verified
functor (identity, multiplicativity, adjoint) on finite modes.

**Honesty labels.** Everything is T1, finite modes `Fin d`, dense
domain `Dom d`, **free** bosonic theory scaffolding — not interacting
Yang–Mills, not a Millennium claim. The infinite-mode limit and the
continuum remain priced, unattempted (Rung 10 dossier).
-/

namespace ThetLogos

open scoped InnerProductSpace
open scoped Matrix

/-! ## 1. The enumeration list and its fibers

`configEnum d c` is the `get` of the sorted list of the multiset
`Finsupp.toMultiset c`. We name that list `enumList` and compute the
fiber cardinalities of the enumeration: mode `i` occupies exactly
`c i` positions. -/

/-- The sorted list of occupied positions underlying `configEnum`. -/
noncomputable def enumList (d : ℕ) (c : Config d) : List (Fin d) :=
  (Finsupp.toMultiset c).sort (· ≤ ·)

/-- The enumeration list has length `tot c` (T1). -/
theorem enumList_length (d : ℕ) (c : Config d) :
    (enumList d c).length = tot c := by
  have hcard : Multiset.card (Finsupp.toMultiset c) = c.sum (fun _ => id) :=
    Finsupp.card_toMultiset c
  have hsum : c.sum (fun _ => id) = tot c :=
    Finsupp.sum_fintype c (fun _ => id) (fun _ => rfl)
  rw [enumList, Multiset.length_sort]
  exact hcard.trans hsum

/-- `configEnum` is the `get` of `enumList` (T1, definitional). -/
theorem configEnum_apply (d : ℕ) (c : Config d) (k : Fin (tot c)) :
    configEnum d c k
      = (enumList d c).get ⟨k.val, by rw [enumList_length]; exact k.isLt⟩ :=
  rfl

/-- Position counting for a list (T1): the number of positions of `l`
holding the value `i` is the multiset count of `i` in `l`. -/
theorem positions_count (d : ℕ) (l : List (Fin d)) (i : Fin d) :
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
        = Multiset.count i (a ::ₘ (↑l : Multiset (Fin d)))
      rw [Multiset.count_cons]
      by_cases h : a = i
      · rw [if_pos h, if_pos h.symm]; omega
      · rw [if_neg h, if_neg (fun hi => h hi.symm)]; omega

/-- **Fiber cardinality of the enumeration (T1):** mode `i` occupies
exactly `c i` positions among the `tot c` positions of `configEnum`. -/
theorem configEnum_fiber_card (d : ℕ) (c : Config d) (i : Fin d) :
    (Finset.univ.filter (fun k : Fin (tot c) => configEnum d c k = i)).card
      = c i := by
  have hstep : (Finset.univ.filter (fun k : Fin (tot c) => configEnum d c k = i)).card
      = (Finset.univ.filter
          (fun k : Fin (enumList d c).length => (enumList d c).get k = i)).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    apply Fintype.card_congr
    apply Equiv.subtypeEquiv (finCongr (enumList_length d c)).symm
    intro k
    have hidx : (finCongr (enumList_length d c)).symm k
        = ⟨k.val, by rw [enumList_length]; exact k.isLt⟩ := Fin.ext rfl
    rw [configEnum_apply, hidx]
  rw [hstep, positions_count]
  have h2 : Multiset.count i ↑((Finsupp.toMultiset c).sort (· ≤ ·)) = c i := by
    rw [Multiset.sort_eq, Finsupp.count_toMultiset]
  exact h2

/-- **Product over the enumeration (T1):**
`∏ b, g (configEnum c b) = ∏ i, g i ^ (c i)` — grouping the positions
by their mode fibers. -/
theorem prod_configEnum (d : ℕ) (c : Config d) (g : Fin d → ℂ) :
    ∏ b : Fin (tot c), g (configEnum d c b) = ∏ i, g i ^ (c i) := by
  rw [← Finset.prod_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin (tot c)))) (t := (Finset.univ : Finset (Fin d)))
    (g := configEnum d c) (fun b _ => Finset.mem_univ _)
    (f := fun b => g (configEnum d c b))]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.prod_congr rfl (g := fun _ : Fin (tot c) => g i)
    (fun b hb => by
      rw [Finset.mem_filter] at hb
      rw [hb.2])]
  rw [Finset.prod_const, configEnum_fiber_card]

/-! ## 2. Abstract counting: fibers of a position map

For a position map `ι : Fin n → Fin d` (`n` positions, `d` modes), the
permanent of a matrix constant on fibers will be counted by splitting
permutations into fiber-preserving ones. `fiberCount ι i` is the size
of the `i`-fiber. -/

/-- Fiber cardinality of a position map (T1). -/
def fiberCount {n : ℕ} (ι : Fin n → Fin d) (i : Fin d) : ℕ :=
  (Finset.univ.filter (fun k => ι k = i)).card

/-- Reordering positions through the fiber decomposition (T1):
conjugation by `sigmaFiberEquiv`. -/
def permCongrSigma {n : ℕ} (ι : Fin n → Fin d) :
    Equiv.Perm (Fin n) ≃ Equiv.Perm (Σ i, {k // ι k = i}) where
  toFun σ := (Equiv.sigmaFiberEquiv ι).trans
    (σ.trans (Equiv.sigmaFiberEquiv ι).symm)
  invFun τ := (Equiv.sigmaFiberEquiv ι).symm.trans
    (τ.trans (Equiv.sigmaFiberEquiv ι))
  left_inv σ := by
    apply Equiv.ext
    intro b
    show (Equiv.sigmaFiberEquiv ι)
      ((Equiv.sigmaFiberEquiv ι).symm
        (σ ((Equiv.sigmaFiberEquiv ι)
          ((Equiv.sigmaFiberEquiv ι).symm b)))) = σ b
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  right_inv τ := by
    apply Equiv.ext
    intro x
    show (Equiv.sigmaFiberEquiv ι).symm
      ((Equiv.sigmaFiberEquiv ι)
        (τ ((Equiv.sigmaFiberEquiv ι).symm
          ((Equiv.sigmaFiberEquiv ι) x)))) = τ x
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- Application formula for `permCongrSigma` (T1, definitional). -/
theorem permCongrSigma_apply {n : ℕ} (ι : Fin n → Fin d)
    (σ : Equiv.Perm (Fin n)) (x : Σ i, {k // ι k = i}) :
    permCongrSigma ι σ x = ⟨ι (σ x.2.1), ⟨σ x.2.1, rfl⟩⟩ :=
  rfl

/-- First component of `permCongrSigma` (T1, definitional). -/
theorem permCongrSigma_fst {n : ℕ} (ι : Fin n → Fin d)
    (σ : Equiv.Perm (Fin n)) (x : Σ i, {k // ι k = i}) :
    (permCongrSigma ι σ x).1 = ι (σ x.2.1) :=
  rfl

/-- Gluing a fiber element back into the total space (T1): a sigma
element with prescribed first component. -/
theorem sigma_mk_fiber {n : ℕ} (ι : Fin n → Fin d) (i : Fin d)
    (y : Σ j, {k // ι k = j}) (hy : y.1 = i) :
    (⟨i, ⟨y.2.1, y.2.2.trans hy⟩⟩ : Σ j, {k // ι k = j}) = y := by
  cases y with
  | mk j yj => cases hy; rfl

/-- Restriction of a fiber-preserving permutation of the total space
to one fiber (T1). -/
def fiberPermRestrict {n : ℕ} (ι : Fin n → Fin d)
    (τ : Equiv.Perm (Σ i, {k // ι k = i})) (hτ : ∀ x, (τ x).1 = x.1)
    (i : Fin d) : Equiv.Perm {k // ι k = i} where
  toFun x := ⟨(τ ⟨i, x⟩).2.1, (τ ⟨i, x⟩).2.2.trans (hτ ⟨i, x⟩)⟩
  invFun x := ⟨(τ.symm ⟨i, x⟩).2.1, (τ.symm ⟨i, x⟩).2.2.trans
    ((hτ (τ.symm ⟨i, x⟩)).symm.trans
      (congrArg Sigma.fst (τ.apply_symm_apply ⟨i, x⟩)))⟩
  left_inv x := by
    apply Subtype.ext
    have hSig : (⟨i, ⟨(τ ⟨i, x⟩).2.1, (τ ⟨i, x⟩).2.2.trans (hτ ⟨i, x⟩)⟩⟩ :
        Σ j, {k // ι k = j}) = τ ⟨i, x⟩ :=
      sigma_mk_fiber ι i (τ ⟨i, x⟩) (hτ ⟨i, x⟩)
    show (τ.symm ⟨i, ⟨(τ ⟨i, x⟩).2.1,
      (τ ⟨i, x⟩).2.2.trans (hτ ⟨i, x⟩)⟩⟩).2.1 = x.1
    rw [hSig, Equiv.symm_apply_apply]
  right_inv x := by
    apply Subtype.ext
    have hSig : (⟨i, ⟨(τ.symm ⟨i, x⟩).2.1, (τ.symm ⟨i, x⟩).2.2.trans
        ((hτ (τ.symm ⟨i, x⟩)).symm.trans
          (congrArg Sigma.fst (τ.apply_symm_apply ⟨i, x⟩)))⟩⟩ :
        Σ j, {k // ι k = j}) = τ.symm ⟨i, x⟩ :=
      sigma_mk_fiber ι i (τ.symm ⟨i, x⟩)
        ((hτ (τ.symm ⟨i, x⟩)).symm.trans
          (congrArg Sigma.fst (τ.apply_symm_apply ⟨i, x⟩)))
    show (τ ⟨i, ⟨(τ.symm ⟨i, x⟩).2.1, (τ.symm ⟨i, x⟩).2.2.trans
      ((hτ (τ.symm ⟨i, x⟩)).symm.trans
        (congrArg Sigma.fst (τ.apply_symm_apply ⟨i, x⟩)))⟩⟩).2.1 = x.1
    rw [hSig, Equiv.apply_symm_apply]

/-- Application formula for `fiberPermRestrict` (T1, definitional). -/
theorem fiberPermRestrict_apply {n : ℕ} (ι : Fin n → Fin d)
    (τ : Equiv.Perm (Σ i, {k // ι k = i})) (hτ : ∀ x, (τ x).1 = x.1)
    (i : Fin d) (x : {k // ι k = i}) :
    (fiberPermRestrict ι τ hτ i) x
      = ⟨(τ ⟨i, x⟩).2.1, (τ ⟨i, x⟩).2.2.trans (hτ ⟨i, x⟩)⟩ :=
  rfl

/-- Fiber-preserving permutations of the total space are exactly the
families of fiber permutations (T1). -/
noncomputable def fiberPermEquivSigma {n : ℕ} (ι : Fin n → Fin d) :
    {τ : Equiv.Perm (Σ i, {k // ι k = i}) // ∀ x, (τ x).1 = x.1}
      ≃ (∀ i, Equiv.Perm {k // ι k = i}) where
  toFun τ := fiberPermRestrict ι τ.1 τ.2
  invFun e := ⟨Equiv.sigmaCongrRight e, fun x => rfl⟩
  left_inv τ := by
    apply Subtype.ext
    apply Equiv.ext
    intro ⟨i, x⟩
    show (Equiv.sigmaCongrRight (fiberPermRestrict ι τ.1 τ.2)) ⟨i, x⟩
      = τ.1 ⟨i, x⟩
    rw [Equiv.sigmaCongrRight_apply, fiberPermRestrict_apply]
    exact sigma_mk_fiber ι i (τ.1 ⟨i, x⟩) (τ.2 ⟨i, x⟩)
  right_inv e := by
    funext i
    apply Equiv.ext
    intro x
    apply Subtype.ext
    show ((Equiv.sigmaCongrRight e) ⟨i, x⟩).2.1 = (e i x).1
    rfl

/-- Fiber-preserving permutations of positions are exactly the
families of fiber permutations (T1). -/
noncomputable def fiberPermEquiv {n : ℕ} (ι : Fin n → Fin d) :
    {σ : Equiv.Perm (Fin n) // ∀ b, ι (σ b) = ι b}
      ≃ (∀ i, Equiv.Perm {k // ι k = i}) :=
  (Equiv.subtypeEquiv (permCongrSigma ι) (fun σ => by
    constructor
    · intro h x
      rw [permCongrSigma_fst, h x.2.1]
      exact x.2.2
    · intro h b
      have hb := h ⟨ι b, ⟨b, rfl⟩⟩
      rw [permCongrSigma_fst] at hb
      exact hb)).trans (fiberPermEquivSigma ι)

/-- **Cardinality of fiber-preserving permutations (T1):**
there are `∏ i, (fiberCount ι i)!` permutations of the positions that
preserve every fiber of `ι`. -/
theorem card_fiberPreserving {n : ℕ} (ι : Fin n → Fin d) :
    Fintype.card {σ : Equiv.Perm (Fin n) // ∀ b, ι (σ b) = ι b}
      = ∏ i, Nat.factorial (fiberCount ι i) := by
  rw [Fintype.card_congr (fiberPermEquiv ι), Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.card_perm, Fintype.card_subtype]
  rfl

/-- **Existence of a fiber-matching permutation (T1):** two position
maps with the same fiber cardinalities differ by a permutation of
positions. -/
theorem exists_perm_of_fiberCount_eq {n : ℕ} {ι κ : Fin n → Fin d}
    (h : ∀ i, fiberCount ι i = fiberCount κ i) :
    ∃ σ : Equiv.Perm (Fin n), ∀ b, κ (σ b) = ι b := by
  have hcard : ∀ i, Fintype.card {k // ι k = i}
      = Fintype.card {k // κ k = i} := fun i => by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact h i
  refine ⟨(Equiv.sigmaFiberEquiv ι).symm.trans
    ((Equiv.sigmaCongrRight (fun i => Fintype.equivOfCardEq (hcard i))).trans
      (Equiv.sigmaFiberEquiv κ)), fun b => ?_⟩
  have hcomp : ((Equiv.sigmaFiberEquiv ι).symm.trans
      ((Equiv.sigmaCongrRight (fun i => Fintype.equivOfCardEq (hcard i))).trans
        (Equiv.sigmaFiberEquiv κ))) b
      = (Fintype.equivOfCardEq (hcard (ι b)) ⟨b, rfl⟩).1 := rfl
  rw [hcomp]
  exact (Fintype.equivOfCardEq (hcard (ι b)) ⟨b, rfl⟩).2

/-- **Torsor equivalence (T1):** right translation by a fixed
fiber-matching permutation identifies the permutations sending `ι` to
`κ` with the fiber-preserving permutations of `κ`. -/
def permTorsorEquiv {n : ℕ} {ι κ : Fin n → Fin d} (σ₀ : Equiv.Perm (Fin n))
    (hσ₀ : ∀ b, ι (σ₀ b) = κ b) :
    {σ : Equiv.Perm (Fin n) // ∀ b, ι (σ b) = κ b}
      ≃ {τ : Equiv.Perm (Fin n) // ∀ b, κ (τ b) = κ b} where
  toFun σ := ⟨σ.1.trans σ₀.symm, fun b => by
    have h1 := hσ₀ (σ₀.symm (σ.1 b))
    rw [Equiv.apply_symm_apply] at h1
    rw [Equiv.trans_apply, ← h1, σ.2]⟩
  invFun τ := ⟨τ.1.trans σ₀, fun b => by
    rw [Equiv.trans_apply, hσ₀, τ.2]⟩
  left_inv σ := by
    apply Subtype.ext
    ext b
    simp [Equiv.trans_apply, Equiv.apply_symm_apply]
  right_inv τ := by
    apply Subtype.ext
    ext b
    simp [Equiv.trans_apply, Equiv.symm_apply_apply]

/-- **Torsor count (T1):** if `ι` and `κ` have the same fiber
cardinalities, the number of permutations `σ` with `ι ∘ σ = κ` is
`∏ i, (fiberCount κ i)!`. -/
theorem card_filter_perm_apply_eq {n : ℕ} {ι κ : Fin n → Fin d}
    (h : ∀ i, fiberCount ι i = fiberCount κ i) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ b, ι (σ b) = κ b)).card
      = ∏ i, Nat.factorial (fiberCount κ i) := by
  obtain ⟨σ₀, hσ₀⟩ := exists_perm_of_fiberCount_eq (d := d) (ι := κ) (κ := ι)
    (fun i => (h i).symm)
  rw [← Fintype.card_subtype, Fintype.card_congr (permTorsorEquiv σ₀ hσ₀)]
  exact card_fiberPreserving κ

/-! ## 3. Indicator permanents

The permanent of a matrix that is constant on the fibers of two
position maps: each permutation either matches the fibers everywhere
(contributing the common value) or contributes zero; the matching
permutations are counted by the torsor count of §2. -/

/-- Product of fiber-indicator terms over positions (T1). -/
theorem prod_ite_indicator {n : ℕ} {ι κ : Fin n → Fin d} (w : Fin d → ℂ)
    (σ : Equiv.Perm (Fin n)) :
    (∏ b, if ι (σ b) = κ b then w (κ b) else 0)
      = if (∀ b, ι (σ b) = κ b) then ∏ b, w (κ b) else 0 := by
  by_cases h : ∀ b, ι (σ b) = κ b
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro b _
    rw [if_pos (h b)]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨b, hb⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ b)
    rw [if_neg hb]

/-- **The indicator permanent (T1):** the permanent of the
fiber-indicator matrix of two position maps is the product of the
fiber factorials times the common value, when the fiber cardinalities
agree, and zero otherwise. -/
theorem permanent_indicator {n : ℕ} {ι κ : Fin n → Fin d} (w : Fin d → ℂ) :
    Matrix.permanent (fun a b => if ι a = κ b then w (κ b) else 0)
      = if (∀ i, fiberCount ι i = fiberCount κ i)
        then ((∏ i, Nat.factorial (fiberCount ι i) : ℕ) : ℂ) * ∏ b, w (κ b)
        else 0 := by
  show (∑ σ : Equiv.Perm (Fin n),
      ∏ b, if ι (σ b) = κ b then w (κ b) else 0) = _
  rw [Finset.sum_congr rfl (fun σ _ => prod_ite_indicator w σ)]
  by_cases h : ∀ i, fiberCount ι i = fiberCount κ i
  · rw [if_pos h, ← Finset.sum_filter, Finset.sum_const,
      card_filter_perm_apply_eq h, nsmul_eq_mul,
      show (∏ i, Nat.factorial (fiberCount κ i))
        = ∏ i, Nat.factorial (fiberCount ι i) from
        Finset.prod_congr rfl (fun i _ => congrArg Nat.factorial (h i).symm)]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro σ _
    by_cases hσ : ∀ b, ι (σ b) = κ b
    · exfalso
      apply h
      intro i
      have hcalc : (Finset.univ.filter (fun b => κ b = i)).card
          = (Finset.univ.filter (fun b => ι b = i)).card := by
        calc (Finset.univ.filter (fun b => κ b = i)).card
            = ∑ b, if κ b = i then (1 : ℕ) else 0 :=
              Finset.card_filter _ _
          _ = ∑ b, if ι (σ b) = i then (1 : ℕ) else 0 := by
              apply Finset.sum_congr rfl
              intro b _
              rw [hσ b]
          _ = ∑ b, if ι b = i then (1 : ℕ) else 0 :=
              Equiv.sum_comp σ (fun b => if ι b = i then (1 : ℕ) else 0)
          _ = (Finset.univ.filter (fun b => ι b = i)).card :=
              (Finset.card_filter _ _).symm
      exact hcalc.symm
    · rw [if_neg hσ]

/-- Fiber cardinality of a transported enumeration (T1). -/
theorem fiberCount_comp_equiv {n m : ℕ} (e : Fin m ≃ Fin n)
    (ι : Fin n → Fin d) (i : Fin d) :
    fiberCount (ι ∘ e) i = fiberCount ι i := by
  unfold fiberCount
  rw [Finset.card_filter, Finset.card_filter]
  show (∑ b : Fin m, if ι (e b) = i then (1 : ℕ) else 0)
    = ∑ b : Fin n, if ι b = i then (1 : ℕ) else 0
  exact Equiv.sum_comp e (fun b => if ι b = i then (1 : ℕ) else 0)

/-- Fiber cardinality of the enumeration transported along
`finCongr` (T1): still `c' i`. -/
theorem fiberCount_configEnum_finCongr (d : ℕ) {c' : Config d} {m : ℕ}
    (h : m = tot c') (i : Fin d) :
    fiberCount (fun a : Fin m => configEnum d c' (finCongr h a)) i = c' i := by
  rw [show (fun a : Fin m => configEnum d c' (finCongr h a))
      = configEnum d c' ∘ finCongr h from rfl,
    fiberCount_comp_equiv]
  exact configEnum_fiber_card d c' i

/-- **Fiber-permanent counting lemma (T1) — campaign Task 1:** the
permanent of the fiber-indicator matrix of a configuration
enumeration is `∏ i, (c i)!`. -/
theorem permanent_fiberIndicator_configEnum (d : ℕ) (c : Config d) :
    Matrix.permanent (fun a b : Fin (tot c) =>
      if configEnum d c a = configEnum d c b then (1 : ℂ) else 0)
      = ∏ i, ((Nat.factorial (c i) : ℕ) : ℂ) := by
  have hfc : ∀ i, fiberCount (configEnum d c) i = c i :=
    fun i => configEnum_fiber_card d c i
  rw [permanent_indicator (w := fun _ => (1 : ℂ)), if_pos (fun i => rfl),
    Finset.prod_const_one, mul_one, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [hfc i]

/-! ## 4. `perMinor` of the identity and of a diagonal -/

/-- **`perMinor` of the identity (T1):** the permanent minor of `1`
between two configurations is the factorial weight when they agree
and zero otherwise. -/
theorem perMinor_one (d : ℕ) (c' c : Config d) :
    perMinor d (1 : Matrix (Fin d) (Fin d) ℂ) c' c
      = if c' = c then ∏ i, ((Nat.factorial (c i) : ℕ) : ℂ) else 0 := by
  rcases eq_or_ne c' c with rfl | hne
  · rw [if_pos rfl]
    unfold perMinor
    rw [dif_pos rfl]
    have hmat : (fun a b : Fin (tot c') => (1 : Matrix (Fin d) (Fin d) ℂ)
          (configEnum d c' (finCongr (Eq.refl (tot c')).symm a)) (configEnum d c' b))
        = (fun a b => if configEnum d c' (finCongr (Eq.refl (tot c')).symm a)
            = configEnum d c' b then (1 : ℂ) else 0) := by
      funext a b
      rw [Matrix.one_apply]
    rw [hmat, permanent_indicator (w := fun _ => (1 : ℂ)),
      if_pos (fun i => by
        rw [fiberCount_configEnum_finCongr d (Eq.refl (tot c')).symm i]
        exact (configEnum_fiber_card d c' i).symm),
      Finset.prod_const_one, mul_one, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [fiberCount_configEnum_finCongr d (Eq.refl (tot c')).symm i]
  · rw [if_neg hne]
    by_cases htot : tot c' = tot c
    · unfold perMinor
      rw [dif_pos htot]
      have hmat : (fun a b : Fin (tot c) => (1 : Matrix (Fin d) (Fin d) ℂ)
            (configEnum d c' (finCongr htot.symm a)) (configEnum d c b))
          = (fun a b => if configEnum d c' (finCongr htot.symm a)
              = configEnum d c b then (1 : ℂ) else 0) := by
        funext a b
        rw [Matrix.one_apply]
      rw [hmat, permanent_indicator (w := fun _ => (1 : ℂ)), if_neg]
      intro hall
      apply hne
      apply Finsupp.ext
      intro i
      have hi := hall i
      rw [fiberCount_configEnum_finCongr d htot.symm i] at hi
      have hfc : fiberCount (configEnum d c) i = c i :=
        configEnum_fiber_card d c i
      rw [hfc] at hi
      exact hi
    · exact perMinor_of_tot_ne d 1 c' c htot

/-- **`perMinor` of a diagonal (T1):** the permanent minor of
`diagonal lam` is the factorial weight times the occupation monomial
on the diagonal, zero off it. -/
theorem perMinor_diagonal (d : ℕ) (lam : Fin d → ℂ) (c' c : Config d) :
    perMinor d (Matrix.diagonal lam) c' c
      = if c' = c then (∏ i, ((Nat.factorial (c i) : ℕ) : ℂ))
          * ∏ i, lam i ^ (c i) else 0 := by
  rcases eq_or_ne c' c with rfl | hne
  · rw [if_pos rfl]
    unfold perMinor
    rw [dif_pos rfl]
    have hmat : (fun a b : Fin (tot c') => Matrix.diagonal lam
          (configEnum d c' (finCongr (Eq.refl (tot c')).symm a)) (configEnum d c' b))
        = (fun a b => if configEnum d c' (finCongr (Eq.refl (tot c')).symm a)
            = configEnum d c' b then lam (configEnum d c' b) else 0) := by
      funext a b
      rw [Matrix.diagonal_apply]
      split_ifs with h
      · rw [h]
      · rfl
    rw [hmat, permanent_indicator (w := lam),
      if_pos (fun i => by
        rw [fiberCount_configEnum_finCongr d (Eq.refl (tot c')).symm i]
        exact (configEnum_fiber_card d c' i).symm),
      Nat.cast_prod, prod_configEnum]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [fiberCount_configEnum_finCongr d (Eq.refl (tot c')).symm i]
  · rw [if_neg hne]
    by_cases htot : tot c' = tot c
    · unfold perMinor
      rw [dif_pos htot]
      have hmat : (fun a b : Fin (tot c) => Matrix.diagonal lam
            (configEnum d c' (finCongr htot.symm a)) (configEnum d c b))
          = (fun a b => if configEnum d c' (finCongr htot.symm a)
              = configEnum d c b then lam (configEnum d c b) else 0) := by
        funext a b
        rw [Matrix.diagonal_apply]
        split_ifs with h
        · rw [h]
        · rfl
      rw [hmat, permanent_indicator (w := lam), if_neg]
      intro hall
      apply hne
      apply Finsupp.ext
      intro i
      have hi := hall i
      rw [fiberCount_configEnum_finCongr d htot.symm i] at hi
      have hfc : fiberCount (configEnum d c) i = c i :=
        configEnum_fiber_card d c i
      rw [hfc] at hi
      exact hi
    · exact perMinor_of_tot_ne d (Matrix.diagonal lam) c' c htot

/-! ## 5. Permanent Cauchy–Binet for repeated indices

The product permanent expands over intermediate index functions
`f : Fin (tot c) → Fin d`; grouping by the occupation configuration
`configOf f` gives the Cauchy–Binet identity: on each fiber class
the `M`-side permanent is constant (the class is a single orbit
under column permutation, by §2), and the `N`-side sum over the
class is the `N`-minor divided by the class multiplicity
`∏ i, (c' i)!` (the torsor count of §2). -/

/-- **Permanent expansion over intermediate index functions (T1):**
the sign-free analogue of `det_mul_expansion`. -/
theorem permanent_mul_expansion {n : ℕ} (A : Fin n → Fin d → ℂ)
    (B : Fin d → Fin n → ℂ) :
    Matrix.permanent (fun a b => ∑ k, A a k * B k b)
      = ∑ f : Fin n → Fin d, (∏ b, B (f b) b)
          * Matrix.permanent (fun a b => A a (f b)) := by
  have prodsum : ∀ σ : Equiv.Perm (Fin n),
      (∏ i, ∑ k : Fin d, A (σ i) k * B k i)
        = ∑ f : Fin n → Fin d, ∏ i, A (σ i) (f i) * B (f i) i := by
    intro σ
    rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset (Fin d)))
      (fun i k => A (σ i) k * B k i), Fintype.piFinset_univ]
  show (∑ σ : Equiv.Perm (Fin n), ∏ i, ∑ k : Fin d, A (σ i) k * B k i)
      = ∑ f : Fin n → Fin d, (∏ b, B (f b) b)
          * ∑ σ : Equiv.Perm (Fin n), ∏ b, A (σ b) (f b)
  rw [Finset.sum_congr rfl (fun σ _ => prodsum σ), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.prod_mul_distrib, mul_comm]

/-- Permanents are invariant under simultaneous reindexing of rows
and columns by an equivalence of position types (T1). -/
theorem permanent_submatrix_equiv {n m : ℕ} (e : Fin n ≃ Fin m)
    (P : Matrix (Fin m) (Fin m) ℂ) :
    Matrix.permanent (P.submatrix e e) = Matrix.permanent P := by
  show (∑ σ : Equiv.Perm (Fin n), ∏ i, P (e (σ i)) (e i))
      = ∑ τ : Equiv.Perm (Fin m), ∏ j, P (τ j) j
  rw [← Equiv.sum_comp (Equiv.permCongr e)
    (fun τ : Equiv.Perm (Fin m) => ∏ j, P (τ j) j)]
  apply Finset.sum_congr rfl
  intro σ _
  show ∏ i, P (e (σ i)) (e i) = ∏ j, P ((Equiv.permCongr e σ) j) j
  rw [← Equiv.prod_comp e (fun j => P ((Equiv.permCongr e σ) j) j)]
  apply Finset.prod_congr rfl
  intro i _
  rw [show (Equiv.permCongr e σ) (e i) = e (σ i) from by
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]]

/-- The occupation configuration of an index function (T1): the
configuration whose occupation at mode `i` is the fiber cardinality
of `f` at `i`. -/
noncomputable def configOf {n : ℕ} (f : Fin n → Fin d) : Config d :=
  Finsupp.equivFunOnFinite.symm (fun i => fiberCount f i)

/-- `configOf f` has occupation `fiberCount f i` at `i` (T1). -/
theorem configOf_apply {n : ℕ} (f : Fin n → Fin d) (i : Fin d) :
    configOf f i = fiberCount f i :=
  rfl

/-- `configOf f` has total occupation `n` (T1). -/
theorem tot_configOf {n : ℕ} (f : Fin n → Fin d) : tot (configOf f) = n := by
  have h2 : (Finset.univ : Finset (Fin n)).card = ∑ i, fiberCount f i :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
  show ∑ i, configOf f i = n
  rw [Finset.sum_congr rfl (fun i _ => configOf_apply f i), ← h2,
    Finset.card_univ, Fintype.card_fin]

/-- **Permanent Cauchy–Binet for repeated indices (T1) — campaign
Task 4:** composition of permanent minors over an intermediate
configuration, with the exact `1 / ∏ i, (c' i)!` multiplicity weights
that the `gammaBos` normalization requires. -/
theorem perMinor_mul (d : ℕ) (M N : Matrix (Fin d) (Fin d) ℂ)
    (c'' c : Config d) :
    perMinor d (M * N) c'' c
      = ∑ c' ∈ configsOfTot d (tot c), perMinor d M c'' c' * perMinor d N c' c
          / ∏ i, ((Nat.factorial (c' i) : ℕ) : ℂ) := by
  by_cases htot : tot c'' = tot c
  · have hLHS : perMinor d (M * N) c'' c = Matrix.permanent
        (fun a b : Fin (tot c) => (M * N)
          (configEnum d c'' (finCongr htot.symm a)) (configEnum d c b)) := by
      unfold perMinor
      rw [dif_pos htot]
    rw [hLHS]
    have hmat : (fun a b : Fin (tot c) => (M * N)
          (configEnum d c'' (finCongr htot.symm a)) (configEnum d c b))
        = (fun a b => ∑ k, M (configEnum d c'' (finCongr htot.symm a)) k
            * N k (configEnum d c b)) := by
      funext a b
      rw [Matrix.mul_apply]
    rw [hmat, permanent_mul_expansion
      (fun a k => M (configEnum d c'' (finCongr htot.symm a)) k)
      (fun k b => N k (configEnum d c b))]
    have hmaps0 : ∀ f ∈ (Finset.univ : Finset (Fin (tot c) → Fin d)),
        configOf f ∈ configsOfTot d (tot c) := fun f _ => by
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
    have hperM : perMinor d M c'' c' = Matrix.permanent
        (fun a b : Fin (tot c') => M (configEnum d c'' (finCongr h''.symm a))
          (configEnum d c' b)) := by
      unfold perMinor
      rw [dif_pos h'']
    have hperN : perMinor d N c' c = Matrix.permanent
        (fun a b : Fin (tot c) => N (configEnum d c' (finCongr hc'.symm a))
          (configEnum d c b)) := by
      unfold perMinor
      rw [dif_pos hc']
    -- Step 2: the `N`-side sum over the class is the minor over the
    -- class multiplicity.
    have hstepN : perMinor d N c' c
        = (∏ i, ((Nat.factorial (c' i) : ℕ) : ℂ))
          * ∑ f ∈ Finset.univ.filter
              (fun f : Fin (tot c) → Fin d => configOf f = c'),
            ∏ b, N (f b) (configEnum d c b) := by
      rw [hperN]
      show (∑ ρ : Equiv.Perm (Fin (tot c)),
          ∏ b, N (configEnum d c' (finCongr hc'.symm (ρ b)))
            (configEnum d c b)) = _
      have hmaps : ∀ ρ ∈ (Finset.univ : Finset (Equiv.Perm (Fin (tot c)))),
          (fun b => configEnum d c' (finCongr hc'.symm b)) ∘ ρ
            ∈ Finset.univ.filter
              (fun f : Fin (tot c) → Fin d => configOf f = c') := by
        intro ρ _
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        apply Finsupp.ext
        intro i
        rw [configOf_apply, fiberCount_comp_equiv]
        exact fiberCount_configEnum_finCongr d hc'.symm i
      rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      rw [Finset.mem_filter] at hf
      have hfiber : ∀ i, fiberCount f i = c' i := fun i => by
        rw [← configOf_apply f i, hf.2]
      have hsumconst : ∀ ρ ∈ Finset.univ.filter
          (fun ρ : Equiv.Perm (Fin (tot c)) =>
            (fun b => configEnum d c' (finCongr hc'.symm b)) ∘ ρ = f),
          (∏ b, N (configEnum d c' (finCongr hc'.symm (ρ b)))
            (configEnum d c b))
            = ∏ b, N (f b) (configEnum d c b) := by
        intro ρ hρ
        rw [Finset.mem_filter] at hρ
        apply Finset.prod_congr rfl
        intro b _
        rw [show configEnum d c' (finCongr hc'.symm (ρ b))
            = ((fun b => configEnum d c' (finCongr hc'.symm b)) ∘ ρ) b
            from rfl, hρ.2]
      rw [Finset.sum_congr rfl hsumconst, Finset.sum_const]
      have hfil : (Finset.univ.filter
          (fun ρ : Equiv.Perm (Fin (tot c)) =>
            (fun b => configEnum d c' (finCongr hc'.symm b)) ∘ ρ = f))
          = Finset.univ.filter (fun ρ : Equiv.Perm (Fin (tot c)) =>
            ∀ b, configEnum d c' (finCongr hc'.symm (ρ b)) = f b) := by
        apply Finset.filter_congr
        intro ρ _
        constructor
        · intro h b
          exact congrFun h b
        · intro h
          funext b
          exact h b
      rw [hfil, card_filter_perm_apply_eq
        (fun i => (fiberCount_configEnum_finCongr d hc'.symm i).trans
          (hfiber i).symm), nsmul_eq_mul, Nat.cast_prod,
        Finset.prod_congr rfl (fun i _ => congrArg
          (fun n : ℕ => ((Nat.factorial n : ℕ) : ℂ)) (hfiber i))]
    have hsum : (∑ f ∈ Finset.univ.filter
        (fun f : Fin (tot c) → Fin d => configOf f = c'),
        ∏ b, N (f b) (configEnum d c b))
        = perMinor d N c' c / ∏ i, ((Nat.factorial (c' i) : ℕ) : ℂ) := by
      rw [eq_div_iff hK, mul_comm, ← hstepN]
    -- Step 1: the `M`-side permanent is constant on the class.
    have hstepM : ∀ f ∈ Finset.univ.filter
        (fun f : Fin (tot c) → Fin d => configOf f = c'),
        Matrix.permanent (fun a b => M (configEnum d c'' (finCongr htot.symm a))
            (f b))
          = perMinor d M c'' c' := by
      intro f hf
      rw [Finset.mem_filter] at hf
      have hfiber : ∀ i, fiberCount f i = c' i := fun i => by
        rw [← configOf_apply f i, hf.2]
      obtain ⟨σ, hσ⟩ := exists_perm_of_fiberCount_eq (d := d) (ι := f)
        (κ := fun b => configEnum d c' (finCongr hc'.symm b))
        (fun i => (hfiber i).trans (fiberCount_configEnum_finCongr d hc'.symm i).symm)
      calc Matrix.permanent (fun a b => M (configEnum d c'' (finCongr htot.symm a))
              (f b))
          = Matrix.permanent (fun a b => M (configEnum d c'' (finCongr htot.symm a))
              (configEnum d c' (finCongr hc'.symm (σ b)))) := by
            congr 1
            funext a b
            rw [hσ b]
        _ = Matrix.permanent (fun a b => M (configEnum d c'' (finCongr htot.symm a))
              (configEnum d c' (finCongr hc'.symm b))) := by
            rw [show (fun a b => M (configEnum d c'' (finCongr htot.symm a))
                  (configEnum d c' (finCongr hc'.symm (σ b))))
                = Matrix.submatrix (fun a b => M (configEnum d c'' (finCongr htot.symm a))
                    (configEnum d c' (finCongr hc'.symm b))) id σ from rfl]
            exact Matrix.permanent_permute_rows σ _
        _ = Matrix.permanent (Matrix.submatrix (fun a b : Fin (tot c') =>
              M (configEnum d c'' (finCongr h''.symm a)) (configEnum d c' b))
                (finCongr hc'.symm) (finCongr hc'.symm)) := by
            rfl
        _ = Matrix.permanent (fun a b : Fin (tot c') =>
              M (configEnum d c'' (finCongr h''.symm a)) (configEnum d c' b)) :=
            permanent_submatrix_equiv (finCongr hc'.symm) _
        _ = perMinor d M c'' c' := hperM.symm
    -- Assembly of the class sum.
    trans (∑ f ∈ Finset.univ.filter
        (fun f : Fin (tot c) → Fin d => configOf f = c'),
        (∏ b, N (f b) (configEnum d c b)) * perMinor d M c'' c')
    · apply Finset.sum_congr rfl
      intro f hf
      rw [hstepM f hf]
    · rw [← Finset.sum_mul, hsum, div_mul_eq_mul_div,
        mul_comm (perMinor d N c' c) (perMinor d M c'' c')]
  · rw [perMinor_of_tot_ne d (M * N) c'' c htot]
    symm
    apply Finset.sum_eq_zero
    intro c' hc'
    rw [mem_configsOfTot] at hc'
    rw [perMinor_of_tot_ne d M c'' c' (by omega), zero_mul, zero_div]

/-! ## 6. The kernel and operator functor laws

The normalization `normFactor` was chosen exactly so that the
kernel of a product is the convolution of the kernels: the
`∏ i, (c' i)!` weight of `perMinor_mul` is the square of the
intermediate normalization. Transported through `gammaC` and
`gammaBos`, this gives the functor laws, the identity law, and the
diagonal action. -/

/-- The normalization factor is positive (T1). -/
theorem normFactor_pos (d : ℕ) (c : Config d) : 0 < normFactor d c := by
  unfold normFactor
  apply Real.sqrt_pos_of_pos
  apply Finset.prod_pos
  intro i _
  exact_mod_cast Nat.factorial_pos (c i)

/-- The squared normalization is the factorial weight (T1):
`(√(∏ i, (c i)!))² = ∏ i, (c i)!` in `ℂ`. -/
theorem normFactor_sq (d : ℕ) (c : Config d) :
    ((normFactor d c : ℂ)) ^ 2 = ∏ i, ((Nat.factorial (c i) : ℕ) : ℂ) := by
  have hP : (0 : ℝ) ≤ ∏ i, (Nat.factorial (c i) : ℝ) :=
    Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)
  unfold normFactor
  rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt hP]
  push_cast
  rfl

/-- **Kernel multiplicativity (T1):** the kernel of a product is the
convolution of the kernels over the intermediate sector — the
`perMinor_mul` weights cancel exactly against the normalizations. -/
theorem gammaKernel_mul (d : ℕ) (M N : Matrix (Fin d) (Fin d) ℂ)
    (c'' c : Config d) :
    gammaKernel d (M * N) c'' c
      = ∑ c' ∈ configsOfTot d (tot c), gammaKernel d M c'' c'
          * gammaKernel d N c' c := by
  have key : ∀ c' : Config d,
        ((normFactor d c' * normFactor d c'' : ℝ) : ℂ)
          * ((normFactor d c * normFactor d c' : ℝ) : ℂ)
        = (∏ i, ((Nat.factorial (c' i) : ℕ) : ℂ))
          * ((normFactor d c * normFactor d c'' : ℝ) : ℂ) := by
    intro c'
    have key' : (normFactor d c' * normFactor d c'')
          * (normFactor d c * normFactor d c')
        = (normFactor d c') ^ 2 * (normFactor d c * normFactor d c'') := by
      ring
    calc ((normFactor d c' * normFactor d c'' : ℝ) : ℂ)
          * ((normFactor d c * normFactor d c' : ℝ) : ℂ)
        = (((normFactor d c' * normFactor d c'')
            * (normFactor d c * normFactor d c') : ℝ) : ℂ) :=
          (Complex.ofReal_mul _ _).symm
      _ = (((normFactor d c') ^ 2
            * (normFactor d c * normFactor d c'') : ℝ) : ℂ) := by rw [key']
      _ = ((normFactor d c' : ℂ)) ^ 2
            * ((normFactor d c * normFactor d c'' : ℝ) : ℂ) := by
          rw [Complex.ofReal_mul, Complex.ofReal_pow]
      _ = (∏ i, ((Nat.factorial (c' i) : ℕ) : ℂ))
            * ((normFactor d c * normFactor d c'' : ℝ) : ℂ) := by
          rw [normFactor_sq]
  unfold gammaKernel
  rw [perMinor_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c' _
  rw [div_mul_div_comm, key c', div_div]

/-- Coefficients of the kernel finsupp (T1). -/
theorem gammaKernelFinsupp_apply (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ)
    (c c' : Config d) :
    (gammaKernelFinsupp d M c) c' = gammaKernel d M c' c := by
  unfold gammaKernelFinsupp
  rw [Finsupp.finset_sum_apply]
  by_cases hc' : c' ∈ configsOfTot d (tot c)
  · rw [Finset.sum_eq_single c' (fun c'' _ hc'' => by
        rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg hc'', smul_zero])
        (fun h => absurd hc' h), Finsupp.smul_apply, Finsupp.single_apply,
      if_pos rfl, smul_eq_mul, mul_one]
  · have htot' : tot c' ≠ tot c := by
      intro h
      apply hc'
      rw [mem_configsOfTot]
      exact h
    have hk0 : gammaKernel d M c' c = 0 := by
      unfold gammaKernel
      rw [perMinor_of_tot_ne d M c' c htot', zero_div]
    rw [hk0]
    apply Finset.sum_eq_zero
    intro c'' hc''
    rw [mem_configsOfTot] at hc''
    have hne : c'' ≠ c' := fun h => htot' (by rw [← h]; exact hc'')
    rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg hne, smul_zero]

/-- `gammaC` on a basis vector (T1). -/
theorem gammaC_single_one (d : ℕ) (P : Matrix (Fin d) (Fin d) ℂ)
    (c : Config d) :
    gammaC d P (Finsupp.single c (1 : ℂ)) = gammaKernelFinsupp d P c := by
  unfold gammaC
  rw [Finsupp.linearCombination_apply,
    Finsupp.sum_single_index (by simp), one_smul]

/-- **Multiplicativity at coefficient level (T1).** -/
theorem gammaC_mul (d : ℕ) (M N : Matrix (Fin d) (Fin d) ℂ) :
    gammaC d (M * N) = (gammaC d M) ∘ₗ (gammaC d N) := by
  apply Finsupp.lhom_ext
  intro c a
  have hsingle : Finsupp.single c a = a • Finsupp.single c (1 : ℂ) := by
    ext x
    simp only [Finsupp.single_apply, Finsupp.smul_apply, smul_eq_mul]
    split_ifs with h
    · rw [mul_one]
    · rw [mul_zero]
  have hcore : gammaC d (M * N) (Finsupp.single c (1 : ℂ))
      = ((gammaC d M) ∘ₗ (gammaC d N)) (Finsupp.single c (1 : ℂ)) := by
    rw [LinearMap.comp_apply, gammaC_single_one, gammaC_single_one]
    apply Finsupp.ext
    intro c''
    have e2 : (gammaC d M (gammaKernelFinsupp d N c)) c''
        = ∑ c' ∈ configsOfTot d (tot c), gammaKernel d N c' c
            * gammaKernel d M c'' c' := by
      unfold gammaKernelFinsupp
      rw [map_sum, Finsupp.finset_sum_apply]
      apply Finset.sum_congr rfl
      intro c' _
      rw [map_smul, gammaC_single_one, Finsupp.smul_apply,
        gammaKernelFinsupp_apply, smul_eq_mul]
    rw [gammaKernelFinsupp_apply, e2, gammaKernel_mul]
    apply Finset.sum_congr rfl
    intro c' _
    rw [mul_comm]
  rw [hsingle, map_smul, map_smul, hcore]

/-- **Identity at coefficient level (T1).** -/
theorem gammaC_one (d : ℕ) : gammaC d 1 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro c a
  have hsingle : Finsupp.single c a = a • Finsupp.single c (1 : ℂ) := by
    ext x
    simp only [Finsupp.single_apply, Finsupp.smul_apply, smul_eq_mul]
    split_ifs with h
    · rw [mul_one]
    · rw [mul_zero]
  have hcore : gammaC d 1 (Finsupp.single c (1 : ℂ))
      = Finsupp.single c (1 : ℂ) := by
    rw [gammaC_single_one]
    apply Finsupp.ext
    intro c'
    rw [gammaKernelFinsupp_apply]
    unfold gammaKernel
    rw [perMinor_one]
    by_cases h : c' = c
    · rw [if_pos h, Finsupp.single_apply, if_pos h.symm]
      rw [show ((normFactor d c * normFactor d c' : ℝ) : ℂ)
          = ∏ i, ((Nat.factorial (c i) : ℕ) : ℂ) from by
        rw [h, Complex.ofReal_mul, ← pow_two, normFactor_sq]]
      exact div_self (Finset.prod_ne_zero_iff.mpr
        (fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_pos (c i)).ne'))
    · rw [if_neg h, zero_div, Finsupp.single_apply,
        if_neg (fun hc => h hc.symm)]
  rw [hsingle, LinearMap.id_apply, map_smul, hcore]

/-- **Multiplicativity of `gammaBos` (T1) — campaign Task 5:**
`Γ(M * N) = Γ(M) ∘ₗ Γ(N)` on `Dom d`. -/
theorem gammaBos_mul (d : ℕ) (M N : Matrix (Fin d) (Fin d) ℂ) :
    gammaBos d (M * N) = (gammaBos d M) ∘ₗ (gammaBos d N) := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, gammaBos_apply, gammaBos_apply, gammaBos_apply,
    show boseRepr d = (boseEquiv d).symm from rfl,
    LinearEquiv.symm_apply_apply, gammaC_mul, LinearMap.comp_apply]

/-- **Identity of `gammaBos` (T1) — campaign Task 2:** `Γ(1) = 1` on
`Dom d`. -/
theorem gammaBos_one (d : ℕ) : gammaBos d 1 = LinearMap.id := by
  apply LinearMap.ext
  intro x
  rw [gammaBos_apply, gammaC_one, LinearMap.id_apply,
    show boseRepr d = (boseEquiv d).symm from rfl]
  exact LinearEquiv.apply_symm_apply (boseEquiv d) x

/-- **Diagonal action (T1) — campaign Task 3:**
`Γ(diag λ) e_c = (∏ i, λ i ^ (c i)) • e_c`. -/
theorem gammaBos_diagonal_basis (d : ℕ) (lam : Fin d → ℂ) (c : Config d) :
    gammaBos d (Matrix.diagonal lam)
        ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = (∏ i, lam i ^ (c i))
        • ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩ := by
  have hcmem : c ∈ configsOfTot d (tot c) := by rw [mem_configsOfTot]
  rw [gammaBos_apply_basis]
  rw [Finset.sum_eq_single c (fun c' _ hc' => by
        have hk0 : gammaKernel d (Matrix.diagonal lam) c' c = 0 := by
          unfold gammaKernel
          rw [perMinor_diagonal, if_neg hc', zero_div]
        rw [hk0, zero_smul])
      (fun h => absurd hcmem h)]
  congr 1
  unfold gammaKernel
  rw [perMinor_diagonal, if_pos rfl,
    show ((normFactor d c * normFactor d c : ℝ) : ℂ)
        = ∏ i, ((Nat.factorial (c i) : ℕ) : ℂ) from by
      rw [Complex.ofReal_mul, ← pow_two, normFactor_sq]]
  exact mul_div_cancel_left₀ _ (Finset.prod_ne_zero_iff.mpr
    (fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_pos (c i)).ne'))

/-! ## 7. The unitarity package

`perMinor` intertwines conjugate-transposition with `star`, exactly
as for determinant minors; the kernel inherits it, and the adjoint
relation on `Dom d` follows by double induction over the basis.
For unitary `M` this gives `Γ(Mᴴ) ∘ₗ Γ(M) = Γ(M) ∘ₗ Γ(Mᴴ) = 1` as
linear maps, and `Γ(M)` is an isometry of the `Dom d` inner
product. -/

/-- Permanents commute with entrywise `star` (T1). -/
theorem permanent_star {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.permanent (fun a b => star (P a b)) = star (Matrix.permanent P) := by
  show (∑ σ : Equiv.Perm (Fin n), ∏ i, star (P (σ i) i))
      = star (∑ σ : Equiv.Perm (Fin n), ∏ i, P (σ i) i)
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [star_prod]

/-- **Conjugate-transpose of a permanent minor (T1):**
`perMinor Mᴴ c' c = conj (perMinor M c c')` — the permanent analogue
of the fermionic `minorDet_conjTranspose`. -/
theorem perMinor_conjTranspose (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ)
    (c' c : Config d) :
    perMinor d Mᴴ c' c = star (perMinor d M c c') := by
  by_cases htot : tot c' = tot c
  · have e1 : perMinor d Mᴴ c' c = Matrix.permanent
        (fun a b : Fin (tot c) => star (M (configEnum d c b)
          (configEnum d c' (finCongr htot.symm a)))) := by
      unfold perMinor
      rw [dif_pos htot]
      congr 1
    have e2 : perMinor d M c c' = Matrix.permanent
        (fun a b : Fin (tot c') => M (configEnum d c (finCongr htot a))
          (configEnum d c' b)) := by
      unfold perMinor
      rw [dif_pos htot.symm]
    rw [e1, e2, permanent_star (fun a b : Fin (tot c) => M (configEnum d c b)
      (configEnum d c' (finCongr htot.symm a)))]
    congr 1
    calc Matrix.permanent (fun a b : Fin (tot c) => M (configEnum d c b)
          (configEnum d c' (finCongr htot.symm a)))
        = Matrix.permanent (Matrix.submatrix
            (fun a b : Fin (tot c') => M (configEnum d c (finCongr htot a))
              (configEnum d c' b))ᵀ
            (finCongr htot.symm) (finCongr htot.symm)) := rfl
      _ = Matrix.permanent (fun a b : Fin (tot c') =>
            M (configEnum d c (finCongr htot a)) (configEnum d c' b))ᵀ :=
          permanent_submatrix_equiv _ _
      _ = Matrix.permanent (fun a b : Fin (tot c') =>
            M (configEnum d c (finCongr htot a)) (configEnum d c' b)) :=
          Matrix.permanent_transpose _
  · rw [perMinor_of_tot_ne d Mᴴ c' c htot,
      perMinor_of_tot_ne d M c c' (fun h => htot h.symm), star_zero]

/-- **Conjugate-transpose of the kernel (T1).** -/
theorem gammaKernel_conjTranspose (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ)
    (c' c : Config d) :
    gammaKernel d Mᴴ c' c = star (gammaKernel d M c c') := by
  unfold gammaKernel
  rw [perMinor_conjTranspose, star_div₀]
  congr 1
  rw [show star ((normFactor d c' * normFactor d c : ℝ) : ℂ)
      = ((normFactor d c' * normFactor d c : ℝ) : ℂ) from by simp]
  rw [mul_comm]

/-- **Adjoint identity on basis pairs (T1):** the `Dom d` inner
product of `Γ(M) e_c` against `e_{c'}` is the conjugate kernel. -/
theorem gammaBos_adjoint_basis (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ)
    (c c' : Config d) :
    ⟪(((gammaBos d M ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩)
        : Dom d) : BosonicFock d),
      ((⟨boseE d c', Submodule.subset_span (Set.mem_range_self c')⟩
        : Dom d) : BosonicFock d)⟫_ℂ
      = star (gammaKernel d M c' c) := by
  rw [gammaBos_apply_basis, Submodule.coe_sum, sum_inner]
  by_cases h : c' ∈ configsOfTot d (tot c)
  · rw [Finset.sum_eq_single c' (fun c'' _ hc'' => by
        rw [Submodule.coe_smul, inner_smul_left]
        show (starRingEnd ℂ) (gammaKernel d M c'' c)
            * ⟪boseE d c'', boseE d c'⟫_ℂ = 0
        rw [boseE_inner, if_neg hc'', mul_zero]) (fun hh => absurd h hh)]
    rw [Submodule.coe_smul, inner_smul_left]
    show (starRingEnd ℂ) (gammaKernel d M c' c)
        * ⟪boseE d c', boseE d c'⟫_ℂ = star (gammaKernel d M c' c)
    rw [boseE_inner, if_pos rfl, mul_one, starRingEnd_apply]
  · have htot' : tot c' ≠ tot c := by
      intro hh
      apply h
      rw [mem_configsOfTot]
      exact hh
    have hk0 : gammaKernel d M c' c = 0 := by
      unfold gammaKernel
      rw [perMinor_of_tot_ne d M c' c htot', zero_div]
    rw [hk0, star_zero]
    apply Finset.sum_eq_zero
    intro c'' hc''
    rw [mem_configsOfTot] at hc''
    rw [Submodule.coe_smul, inner_smul_left]
    show (starRingEnd ℂ) (gammaKernel d M c'' c)
        * ⟪boseE d c'', boseE d c'⟫_ℂ = 0
    rw [boseE_inner, if_neg (fun he => htot' (by rw [← he]; exact hc'')),
      mul_zero]

/-- **Adjoint relation for `Γ` (T1) — campaign Task 6, adjoint part:**
on the dense domain, `Γ(M)` has adjoint `Γ(Mᴴ)` for the `Dom d`
inner product (coerced to the Fock space), mirroring
`dgammaBos_adjoint`. -/
theorem gammaBos_adjoint (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) (x y : Dom d) :
    ⟪(((gammaBos d M x) : Dom d) : BosonicFock d), (y : BosonicFock d)⟫_ℂ
      = ⟪(x : BosonicFock d), (((gammaBos d Mᴴ y) : Dom d) : BosonicFock d)⟫_ℂ := by
  apply Dom_induction₂ d (P := fun x y =>
    ⟪(((gammaBos d M x) : Dom d) : BosonicFock d), (y : BosonicFock d)⟫_ℂ
      = ⟪(x : BosonicFock d), (((gammaBos d Mᴴ y) : Dom d) : BosonicFock d)⟫_ℂ)
    _ _ _ _ _ _ _ x y
  · intro c c'
    calc ⟪(((gammaBos d M ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩)
            : Dom d) : BosonicFock d),
          ((⟨boseE d c', Submodule.subset_span (Set.mem_range_self c')⟩
            : Dom d) : BosonicFock d)⟫_ℂ
        = star (gammaKernel d M c' c) := gammaBos_adjoint_basis d M c c'
      _ = star (star (gammaKernel d Mᴴ c c')) := by
          rw [gammaKernel_conjTranspose, star_star]
      _ = ⟪((⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
              : Dom d) : BosonicFock d),
            (((gammaBos d Mᴴ ⟨boseE d c', Submodule.subset_span
              (Set.mem_range_self c')⟩) : Dom d) : BosonicFock d)⟫_ℂ := by
          rw [← gammaBos_adjoint_basis d Mᴴ c' c]
          show (starRingEnd ℂ)
              ⟪(((gammaBos d Mᴴ ⟨boseE d c', Submodule.subset_span
                  (Set.mem_range_self c')⟩) : Dom d) : BosonicFock d),
                ((⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
                  : Dom d) : BosonicFock d)⟫_ℂ
            = ⟪((⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
                  : Dom d) : BosonicFock d),
                (((gammaBos d Mᴴ ⟨boseE d c', Submodule.subset_span
                  (Set.mem_range_self c')⟩) : Dom d) : BosonicFock d)⟫_ℂ
          exact inner_conj_symm _ _
  · intro x x' y h1 h2
    rw [map_add, Submodule.coe_add, Submodule.coe_add, inner_add_left,
      inner_add_left, h1, h2]
  · intro y
    simp
  · intro a x y h
    rw [map_smul, Submodule.coe_smul, Submodule.coe_smul, inner_smul_left,
      inner_smul_left, h]
  · intro x y y' h1 h2
    rw [map_add, Submodule.coe_add, Submodule.coe_add, inner_add_right,
      inner_add_right, h1, h2]
  · intro x
    simp
  · intro a x y h
    rw [map_smul, Submodule.coe_smul, Submodule.coe_smul, inner_smul_right,
      inner_smul_right, h]

/-- **Algebraic unitarity I (T1):** if `M * Mᴴ = 1` then
`Γ(M) ∘ₗ Γ(Mᴴ) = 1` as linear maps on `Dom d`. -/
theorem gammaBos_comp_conjTranspose (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ)
    (hM : M * Mᴴ = 1) :
    (gammaBos d M) ∘ₗ (gammaBos d Mᴴ) = LinearMap.id := by
  rw [← gammaBos_mul, hM, gammaBos_one]

/-- **Algebraic unitarity II (T1):** if `Mᴴ * M = 1` then
`Γ(Mᴴ) ∘ₗ Γ(M) = 1` as linear maps on `Dom d`. -/
theorem gammaBos_conjTranspose_comp (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ)
    (hM : Mᴴ * M = 1) :
    (gammaBos d Mᴴ) ∘ₗ (gammaBos d M) = LinearMap.id := by
  rw [← gammaBos_mul, hM, gammaBos_one]

/-- **Isometry (T1) — campaign Task 6, isometry part:** for
`Mᴴ * M = 1`, `Γ(M)` preserves the `Dom d` inner product of a vector
with itself. -/
theorem gammaBos_isometry (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ)
    (hM : Mᴴ * M = 1) (x : Dom d) :
    ⟪(((gammaBos d M x) : Dom d) : BosonicFock d),
      (((gammaBos d M x) : Dom d) : BosonicFock d)⟫_ℂ
      = ⟪(x : BosonicFock d), (x : BosonicFock d)⟫_ℂ := by
  rw [gammaBos_adjoint,
    show gammaBos d Mᴴ (gammaBos d M x)
        = (((gammaBos d Mᴴ) ∘ₗ (gammaBos d M)) x) from rfl,
    gammaBos_conjTranspose_comp d M hM, LinearMap.id_apply]

end ThetLogos
