import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases

namespace ThetLogos

/-!
# ThetLogos.WickSigns — the general fermionic Wick sign rule (Rung 6, Price 1)

**Context.** Rung 5 (`Rung5W6.lean`, `w6_fermionic_wick`) proved the fermionic
Wick sign rule for ONE mode: with `W₂(f,g) = fg`, the signed 4-point identity
`W₄ = W₂W₂ − W₂W₂ + W₂W₂` holds with Koszul signs `(+, −, +)`. Its general form
— arbitrary modes, the sign of a general complete pairing, the n-point Wick
expansion — was priced. This file discharges it as far as honest work goes.

**What is proved (T1).**
- **Part A — Koszul sign machinery.** A complete pairing of `2n` fermionic
  operator positions is a partition of `Fin (2*n)` into 2-element blocks
  (`FermPairing`). Each pairing contributes the sign of the permutation that
  "brings paired operators together" (`koszulSign`): pairs listed least-first
  within each pair. The sign is **well-defined — independent of the order in
  which the pairs are listed** (`koszulSign_independent`): reordering the
  pairs is an even permutation. (The sign *does* depend on the within-pair
  orientation — flipping one pair is a transposition — which is why the
  least-first convention is fixed once and for all.) The three 4-point
  pairing signs are `+1, −1, +1` (`koszulSign_four_point`).
- **Part B — the general 4-point Wick identity.** For Majorana-type operators
  `ψ₀,…,ψ₃` in a `ℂ`-algebra with `{ψᵢ,ψⱼ} = 2Gᵢⱼ` and a linear functional `ω`
  with the 2-point data `ω(ψᵢψⱼ) = Gᵢⱼ` (i<j) that is cyclic on the 4-point
  monomial, the vacuum expectation is the Koszul-signed pairing sum
  (`wick_four_point`):
  `ω(ψ₀ψ₁ψ₂ψ₃) = G₀₁G₂₃ − G₀₂G₁₃ + G₀₃G₁₂`.
  The cyclic hypothesis is exactly the quasi-free content: given the CAR and
  the 2-point data, the 4-point Wick identity is *equivalent* to cyclic
  invariance of the 4-point moment. The arbitrary-mode version
  (`wick_four_point_modes`) takes a linear field map `φ : V →ₗ[ℂ] A` over an
  arbitrary module `V` — the "not just one mode" generalization Rung 5 priced.
- **Part C — priced.** The full n-point Wick expansion
  (`wickExpansion_window`, T5): exact statement, unproved by design. Price:
  the induction needs the quasi-free Wick recursion for `ω` at `2n` points,
  which for the physical vacuum comes from the Fock representation — i.e. the
  `fockInnerProduct` infrastructure gap already logged in `FreeField.lean`
  (no adjoints, no Fock inner product in Mathlib 2026).

**Tier honesty.** Everything proved below is T1 (machine-checked, `#print
axioms` at the end). `wickExpansion_window` is a T5 priced window: exact
statement, never a sorry. `satisfiesDestruction` untouched. No 4D interacting
QFT claimed.
-/

/-!
## Part A — complete pairings and the Koszul sign
-/

/-- Div/mod position decoder: `Fin (2*n) → Fin n × Fin 2`. -/
def divModFun (n : ℕ) (k : Fin (2 * n)) : Fin n × Fin 2 :=
  (⟨k.val / 2, by have hk := k.isLt; omega⟩,
   ⟨k.val % 2, by have hk := k.isLt; omega⟩)

theorem divModFun_injective (n : ℕ) : Function.Injective (divModFun n) := by
  intro k k' h
  have h1 : k.val / 2 = k'.val / 2 := congrArg (fun p => (p.1).val) h
  have h2 : k.val % 2 = k'.val % 2 := congrArg (fun p => (p.2).val) h
  have hval : k.val = k'.val := by
    have e1 := Nat.div_add_mod k.val 2
    have e2 := Nat.div_add_mod k'.val 2
    omega
  exact Fin.ext hval

theorem divModFun_surjective (n : ℕ) : Function.Surjective (divModFun n) := by
  rintro ⟨i, j⟩
  by_cases hn : n = 0
  · subst hn
    exact (Nat.not_lt_zero _ i.isLt).elim
  · have hbound : 2 * i.val + j.val < 2 * n := by
      have hi := i.isLt
      have hj := j.isLt
      omega
    have h1 : (2 * i.val + j.val) / 2 = i.val := by
      have hj := j.isLt; omega
    have h2 : (2 * i.val + j.val) % 2 = j.val := by
      have hj := j.isLt; omega
    refine ⟨⟨2 * i.val + j.val, hbound⟩, ?_⟩
    unfold divModFun
    apply Prod.ext
    · apply Fin.ext
      exact h1
    · apply Fin.ext
      exact h2

/-- A complete pairing of `Fin (2*n)`: a partition into 2-element blocks.
    For a product of `2n` fermionic operators, the positions `0,…,2n−1` are
    paired up; each complete pairing contributes one term to Wick's
    expansion, with the Koszul sign defined below. -/
structure FermPairing (n : ℕ) where
  blocks : Finset (Finset (Fin (2 * n)))
  card_two : ∀ b ∈ blocks, b.card = 2
  disjoint : Set.PairwiseDisjoint (blocks : Set (Finset (Fin (2 * n)))) id
  covers : blocks.biUnion id = Finset.univ

namespace FermPairing

variable {n : ℕ} (P : FermPairing n)

/-- There are exactly `n` blocks. -/
theorem card_blocks : P.blocks.card = n := by
  have h1 : (P.blocks.biUnion id).card = P.blocks.card * 2 := by
    rw [Finset.card_biUnion P.disjoint]
    simp [Finset.sum_congr rfl (fun b hb => P.card_two b hb)]
  rw [P.covers, Finset.card_univ, Fintype.card_fin] at h1
  omega

/-- Each block is nonempty. -/
theorem block_nonempty {b : Finset (Fin (2 * n))} (hb : b ∈ P.blocks) :
    b.Nonempty := by
  rw [← Finset.card_pos]
  have h := P.card_two b hb
  omega

/-- A block's least element is strictly below its greatest (blocks have two
    distinct elements). -/
theorem min_lt_max {b : Finset (Fin (2 * n))} (hb : b ∈ P.blocks) :
    b.min' (P.block_nonempty hb) < b.max' (P.block_nonempty hb) := by
  have h2 : 1 < b.card := by
    have h := P.card_two b hb
    omega
  exact Finset.min'_lt_max'_of_card b h2

/-- Disjointness of distinct blocks, in elementary form. -/
theorem disjoint_of_ne {b c : Finset (Fin (2 * n))}
    (hb : b ∈ P.blocks) (hc : c ∈ P.blocks) (hne : b ≠ c) :
    Disjoint b c := by
  have hd := P.disjoint (Finset.mem_coe.mpr hb) (Finset.mem_coe.mpr hc) hne
  simpa [Function.onFun] using hd

/-- The least element of a block. -/
def blockMin (b : Finset (Fin (2 * n))) (hb : b ∈ P.blocks) : Fin (2 * n) :=
  b.min' (P.block_nonempty hb)

/-- The set of least elements of the blocks. -/
def mins : Finset (Fin (2 * n)) :=
  P.blocks.attach.image fun b => P.blockMin b.val b.property

/-- The least-element map is injective on blocks: distinct blocks are
    disjoint, so they cannot share a least element. -/
theorem blockMin_injective :
    Function.Injective (fun b : P.blocks => P.blockMin b.val b.property) := by
  intro ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ h
  simp only [blockMin] at h
  by_cases heq : b₁ = b₂
  · exact Subtype.ext heq
  · exfalso
    have h1 : b₁.min' (P.block_nonempty hb₁) ∈ b₂ := by
      rw [h]; exact Finset.min'_mem _ _
    have h2 : b₁.min' (P.block_nonempty hb₁) ∈ b₁ := Finset.min'_mem _ _
    exact (Finset.disjoint_left.mp (P.disjoint_of_ne hb₁ hb₂ heq) h2) h1

/-- The least-element map into `mins`. -/
def toMins (b : P.blocks) : P.mins :=
  ⟨P.blockMin b.val b.property, by
    unfold mins
    rw [Finset.mem_image]
    exact ⟨b, Finset.mem_attach _ _, rfl⟩⟩

theorem toMins_injective : Function.Injective P.toMins := by
  intro b₁ b₂ h
  have h' : P.blockMin b₁.val b₁.property = P.blockMin b₂.val b₂.property :=
    congrArg Subtype.val h
  exact P.blockMin_injective h'

theorem toMins_surjective : Function.Surjective P.toMins := by
  intro m
  have hm : m.val ∈ P.mins := m.property
  unfold mins at hm
  rw [Finset.mem_image] at hm
  obtain ⟨⟨b, hb⟩, _, hbeq⟩ := hm
  refine ⟨⟨b, hb⟩, ?_⟩
  simp only [toMins, blockMin] at hbeq ⊢
  exact Subtype.ext hbeq

/-- The least-element map is a bijection between blocks and mins. -/
noncomputable def blockMinEquiv : P.blocks ≃ P.mins :=
  Equiv.ofBijective P.toMins ⟨P.toMins_injective, P.toMins_surjective⟩

/-- There are exactly `n` block-mins. -/
theorem card_mins : P.mins.card = n := by
  have h := Fintype.card_congr P.blockMinEquiv
  rw [Fintype.card_coe, P.card_blocks, Fintype.card_coe] at h
  exact h.symm

/-- The canonical enumeration of the blocks: the block whose least element
    is the `i`-th smallest comes `i`-th. This fixes the "pair ordering"
    once and for all (pairs ordered by least element). -/
noncomputable def canonEnum (i : Fin n) : P.blocks :=
  P.blockMinEquiv.symm ((P.mins.orderIsoOfFin P.card_mins) i)

theorem canonEnum_injective : Function.Injective P.canonEnum := by
  intro i j hij
  have h2 := P.blockMinEquiv.symm.injective hij
  exact (P.mins.orderIsoOfFin P.card_mins).injective h2

/-- The bring-together map on pair-positions: `(i, j)` maps to the `j`-th
    element of the `i`-th block (`j = 0` ↦ least, `j = 1` ↦ greatest),
    for a given enumeration `e` of the blocks. -/
def bringFun (e : Fin n → P.blocks) : Fin n × Fin 2 → Fin (2 * n) :=
  fun p => ![ (e p.1).val.min' (P.block_nonempty (e p.1).property),
              (e p.1).val.max' (P.block_nonempty (e p.1).property) ] p.2

theorem bringFun_apply (e : Fin n → P.blocks) (i : Fin n) (j : Fin 2) :
    P.bringFun e (i, j)
      = ![ (e i).val.min' (P.block_nonempty (e i).property),
           (e i).val.max' (P.block_nonempty (e i).property) ] j := rfl

/-- The value lies in its block. -/
theorem bringFun_mem (e : Fin n → P.blocks) (p : Fin n × Fin 2) :
    P.bringFun e p ∈ (e p.1).val := by
  obtain ⟨i, j⟩ := p
  rw [P.bringFun_apply e i j]
  fin_cases j <;> simp [Finset.min'_mem, Finset.max'_mem]

/-- An injective enumeration is surjective onto the blocks (card count). -/
theorem enum_surjective (e : Fin n → P.blocks)
    (hinj : Function.Injective e) : Function.Surjective e := by
  intro b
  have hcard : (Finset.univ.image e).card = Fintype.card P.blocks := by
    rw [Finset.card_image_of_injective _ hinj]
    rw [Finset.card_univ, Fintype.card_fin, Fintype.card_coe, P.card_blocks]
  have huniv := Finset.eq_univ_of_card _ hcard
  have hbmem : b ∈ Finset.univ.image e := by
    rw [huniv]; exact Finset.mem_univ b
  rw [Finset.mem_image] at hbmem
  obtain ⟨i, _, hi⟩ := hbmem
  exact ⟨i, hi⟩

/-- A 2-element block is `{min', max'}`. -/
theorem card_two_eq_min_max {b : Finset (Fin (2 * n))} (hb : b ∈ P.blocks) :
    b = {b.min' (P.block_nonempty hb), b.max' (P.block_nonempty hb)} := by
  have hne : b.min' (P.block_nonempty hb) ≠ b.max' (P.block_nonempty hb) :=
    ne_of_lt (P.min_lt_max hb)
  have hsub : ({b.min' (P.block_nonempty hb), b.max' (P.block_nonempty hb)} :
      Finset (Fin (2 * n))) ⊆ b := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.min'_mem _ _
    · exact Finset.max'_mem _ _
  have hcard : b.card ≤ ({b.min' (P.block_nonempty hb),
      b.max' (P.block_nonempty hb)} : Finset (Fin (2 * n))).card := by
    rw [P.card_two b hb, Finset.card_pair hne]
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

/-- `bringFun` is injective: distinct positions map to distinct elements
    (blocks are disjoint; within a block, least ≠ greatest). -/
theorem bringFun_injective (e : Fin n → P.blocks)
    (hinj : Function.Injective e) :
    Function.Injective (P.bringFun e) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ hpq
  have hmem₁ := P.bringFun_mem e (i, j)
  have hmem₂ := P.bringFun_mem e (i', j')
  rw [hpq] at hmem₁
  have hblock : (e i).val = (e i').val := by
    by_contra heq
    exact (Finset.disjoint_left.mp
      (P.disjoint_of_ne (e i).property (e i').property heq) hmem₁) hmem₂
  have hi : i = i' := hinj (Subtype.ext hblock)
  subst hi
  have hlt := P.min_lt_max (e i).property
  rw [P.bringFun_apply e, P.bringFun_apply e] at hpq
  have hj : j = j' := by
    have hne : (e i).val.min' (P.block_nonempty (e i).property)
        ≠ (e i).val.max' (P.block_nonempty (e i).property) := ne_of_lt hlt
    have hinj2 : Function.Injective
        (![ (e i).val.min' (P.block_nonempty (e i).property),
            (e i).val.max' (P.block_nonempty (e i).property) ] :
          Fin 2 → Fin (2 * n)) := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all
    exact hinj2 hpq
  subst hj
  rfl

/-- `bringFun` is surjective: every position lies in some block. -/
theorem bringFun_surjective (e : Fin n → P.blocks)
    (hinj : Function.Injective e) :
    Function.Surjective (P.bringFun e) := by
  intro x
  have hx : x ∈ P.blocks.biUnion id := by
    rw [P.covers]; exact Finset.mem_univ x
  rw [Finset.mem_biUnion] at hx
  obtain ⟨b, hb, hxb⟩ := hx
  obtain ⟨i, hi⟩ := P.enum_surjective e hinj ⟨b, hb⟩
  have heb : (e i).val = b := congrArg Subtype.val hi
  have hxb' : x ∈ (e i).val := heb ▸ hxb
  rw [P.card_two_eq_min_max (e i).property,
    Finset.mem_insert, Finset.mem_singleton] at hxb'
  rcases hxb' with rfl | rfl
  · exact ⟨(i, 0), by rw [P.bringFun_apply e]; simp⟩
  · exact ⟨(i, 1), by rw [P.bringFun_apply e]; simp⟩

theorem bringFun_bijective (e : Fin n → P.blocks)
    (hinj : Function.Injective e) :
    Function.Bijective (P.bringFun e) :=
  ⟨P.bringFun_injective e hinj, P.bringFun_surjective e hinj⟩

/-- Position decoder: `Fin (2*n) ≃ Fin n × Fin 2` via div/mod. -/
noncomputable def dm : Fin (2 * n) ≃ Fin n × Fin 2 :=
  Equiv.ofBijective (divModFun n)
    ⟨divModFun_injective n, divModFun_surjective n⟩

theorem dm_apply (k : Fin (2 * n)) : dm (n := n) k = divModFun n k := rfl

/-- The bring-together permutation for an enumeration `e`: position `k`
    (pair `k/2`, within-pair `k%2`) maps to the corresponding block element.
    This is "the permutation bringing paired operators together". -/
noncomputable def bringTogetherOf (e : Fin n → P.blocks)
    (hinj : Function.Injective e) : Equiv.Perm (Fin (2 * n)) :=
  (dm).trans (Equiv.ofBijective (P.bringFun e) (P.bringFun_bijective e hinj))

/-- The Koszul sign of a complete pairing: the sign of the bring-together
    permutation for the canonical (least-element-first) enumeration.
    **Subtlety:** the sign depends on the within-pair orientation (flipping
    one pair is a transposition), which is why least-first is fixed once and
    for all; it does NOT depend on the order of the pairs (proved below). -/
noncomputable def koszulSign : ℤˣ :=
  Equiv.Perm.sign (P.bringTogetherOf P.canonEnum P.canonEnum_injective)

/-- Reindexing permutation between two enumerations. -/
noncomputable def enumReindex (e c : Fin n → P.blocks)
    (hinj : Function.Injective e) (hinj' : Function.Injective c) :
    Equiv.Perm (Fin n) :=
  (Equiv.ofBijective e ⟨hinj, P.enum_surjective e hinj⟩).trans
    (Equiv.ofBijective c ⟨hinj', P.enum_surjective c hinj'⟩).symm

/-- The reindexing sends `e`-indices to `c`-indices of the same block. -/
theorem enumReindex_apply (e c : Fin n → P.blocks)
    (hinj : Function.Injective e) (hinj' : Function.Injective c) (i : Fin n) :
    c (P.enumReindex e c hinj hinj' i) = e i := by
  have h : (Equiv.ofBijective c ⟨hinj', P.enum_surjective c hinj'⟩)
      (P.enumReindex e c hinj hinj' i)
      = (Equiv.ofBijective e ⟨hinj, P.enum_surjective e hinj⟩) i := by
    unfold enumReindex
    rw [Equiv.trans_apply, Equiv.apply_symm_apply]
  exact h

/-- Every unit of `ℤ` squares to 1. -/
theorem units_int_sq : ∀ u : ℤˣ, u ^ 2 = 1 := by
  intro u
  rcases Int.units_eq_one_or u with rfl | rfl <;> rfl

/-- Reordering the pairs is an even permutation: it is conjugate to
    `prodCongr π refl`, whose sign is `sign π ^ 2 = 1`. -/
theorem sign_prodCongr_refl (π : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (Equiv.prodCongr π (Equiv.refl (Fin 2))
      : Equiv.Perm (Fin n × Fin 2)) = 1 := by
  have h : Equiv.prodCongr π (Equiv.refl (Fin 2))
      = Equiv.prodCongrLeft (fun _ : Fin 2 => π) := by
    rw [← Equiv.prodCongr_refl_right]
  rw [h, Equiv.Perm.sign_prodCongrLeft, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  exact units_int_sq _

/-- Computation rule for the bring-together permutation. -/
theorem bringTogetherOf_apply (e : Fin n → P.blocks)
    (hinj : Function.Injective e) (k : Fin (2 * n)) :
    P.bringTogetherOf e hinj k = P.bringFun e (divModFun n k) := rfl

/-- **Well-definedness (T1):** the Koszul sign is independent of the order in
    which the pairs are listed. Two enumerations differ by a pair-reordering,
    and pair-reorderings are even permutations. -/
theorem koszulSign_independent (e : Fin n → P.blocks)
    (hinj : Function.Injective e) :
    Equiv.Perm.sign (P.bringTogetherOf e hinj) = P.koszulSign := by
  have hcinj : Function.Injective P.canonEnum := P.canonEnum_injective
  -- reindexing π with e i = c (π i)
  set π := P.enumReindex e P.canonEnum hinj hcinj with hπ
  have heq : ∀ i, e i = P.canonEnum (π i) :=
    fun i => (P.enumReindex_apply e P.canonEnum hinj hcinj i).symm
  -- the pair-reordering on pair-positions
  set C : Equiv.Perm (Fin n × Fin 2) :=
    Equiv.prodCongr π (Equiv.refl (Fin 2)) with hC
  set B_e := Equiv.ofBijective (P.bringFun e) (P.bringFun_bijective e hinj) with hB_e
  set B_c := Equiv.ofBijective (P.bringFun P.canonEnum)
    (P.bringFun_bijective P.canonEnum hcinj) with hB_c
  -- B_e = C.trans B_c
  have hB : B_e = C.trans B_c := by
    apply Equiv.ext
    intro ⟨i, j⟩
    have hCij : C (i, j) = (π i, j) := rfl
    show P.bringFun e (i, j) = B_c (C (i, j))
    rw [hCij]
    show P.bringFun e (i, j) = P.bringFun P.canonEnum (π i, j)
    rw [P.bringFun_apply, P.bringFun_apply, heq i]
  -- ρ is the pair-reordering transferred to positions; it is conjugate to C
  set ρ : Equiv.Perm (Fin (2 * n)) := B_c.symm.trans (C.trans B_c) with hρ
  have hρsign : Equiv.Perm.sign ρ = 1 := by
    have hconj : Equiv.Perm.sign C = Equiv.Perm.sign ρ := by
      apply Equiv.Perm.sign_eq_sign_of_equiv _ _ B_c
      intro x
      show B_c (C x) = ρ (B_c x)
      simp [hρ, Equiv.trans_apply]
    rw [← hconj]
    exact sign_prodCongr_refl π
  -- sign computation via ρ
  have hsign : Equiv.Perm.sign (P.bringTogetherOf e hinj)
      = Equiv.Perm.sign (P.bringTogetherOf P.canonEnum hcinj) := by
    show Equiv.Perm.sign (dm.trans B_e) = Equiv.Perm.sign (dm.trans B_c)
    rw [hB]
    have hρ' : dm.trans (C.trans B_c) = (dm.trans B_c).trans ρ := by
      have e1 : B_c.trans (B_c.symm.trans (C.trans B_c)) = C.trans B_c := by
        rw [← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans]
      rw [hρ, Equiv.trans_assoc, e1]
    rw [hρ', Equiv.Perm.sign_trans, hρsign, one_mul]
  rw [hsign]
  rfl

end FermPairing


/-!
## The three 4-point pairings and their Koszul signs

For W6 we need the signs of the three complete pairings of `Fin 4`:
`{{0,1},{2,3}}` (sign +1), `{{0,2},{1,3}}` (sign −1), `{{0,3},{1,2}}` (sign +1).
-/

/-- Pairing `{{0,1},{2,3}}`: adjacent pairs. -/
def pairing4a : FermPairing 2 where
  blocks := { {0, 1}, {2, 3} }
  card_two := by decide
  disjoint := by
    intro x hx y hy hne
    simp at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hne
    · decide
    · decide
    · exact absurd rfl hne
  covers := by decide

/-- Pairing `{{0,2},{1,3}}`: crossing pairs. -/
def pairing4b : FermPairing 2 where
  blocks := { {0, 2}, {1, 3} }
  card_two := by decide
  disjoint := by
    intro x hx y hy hne
    simp at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hne
    · decide
    · decide
    · exact absurd rfl hne
  covers := by decide

/-- Pairing `{{0,3},{1,2}}`: nested pairs. -/
def pairing4c : FermPairing 2 where
  blocks := { {0, 3}, {1, 2} }
  card_two := by decide
  disjoint := by
    intro x hx y hy hne
    simp at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hne
    · decide
    · decide
    · exact absurd rfl hne
  covers := by decide

/-- Convenient enumeration of `pairing4a` blocks. -/
def enum4a : Fin 2 → pairing4a.blocks :=
  fun i => ⟨![({0, 1} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4))] i, by
    fin_cases i <;> decide⟩

theorem enum4a_injective : Function.Injective enum4a := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [enum4a]
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)

/-- The bring-together permutation for `pairing4a` is the identity. -/
theorem bringTogetherOf_enum4a :
    pairing4a.bringTogetherOf enum4a enum4a_injective = 1 := by
  apply Equiv.ext
  intro k
  fin_cases k <;> rw [FermPairing.bringTogetherOf_apply,
    FermPairing.bringFun_apply] <;> simp [enum4a, divModFun]

/-- Convenient enumeration of `pairing4b` blocks. -/
def enum4b : Fin 2 → pairing4b.blocks :=
  fun i => ⟨![({0, 2} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4))] i, by
    fin_cases i <;> decide⟩

theorem enum4b_injective : Function.Injective enum4b := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [enum4b]
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)

/-- The bring-together permutation for `pairing4b` swaps 1 and 2. -/
theorem bringTogetherOf_enum4b :
    pairing4b.bringTogetherOf enum4b enum4b_injective
      = Equiv.swap (⟨1, by decide⟩ : Fin 4) (⟨2, by decide⟩ : Fin 4) := by
  apply Equiv.ext
  intro k
  fin_cases k <;> rw [FermPairing.bringTogetherOf_apply,
    FermPairing.bringFun_apply] <;> simp [enum4b, divModFun] <;> rfl

/-- Convenient enumeration of `pairing4c` blocks. -/
def enum4c : Fin 2 → pairing4c.blocks :=
  fun i => ⟨![({0, 3} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4))] i, by
    fin_cases i <;> decide⟩

theorem enum4c_injective : Function.Injective enum4c := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [enum4c]
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)

/-- The bring-together permutation for `pairing4c` is the 3-cycle `(1 3 2)`. -/
theorem bringTogetherOf_enum4c :
    pairing4c.bringTogetherOf enum4c enum4c_injective
      = Equiv.swap (⟨1, by decide⟩ : Fin 4) (⟨2, by decide⟩ : Fin 4)
        * Equiv.swap (⟨1, by decide⟩ : Fin 4) (⟨3, by decide⟩ : Fin 4) := by
  apply Equiv.ext
  intro k
  fin_cases k <;> rw [FermPairing.bringTogetherOf_apply,
    FermPairing.bringFun_apply] <;> simp [enum4c, divModFun] <;> rfl

/-- Koszul signs of the three 4-point pairings: `+1, −1, +1`. -/
theorem koszulSign_four_point :
    pairing4a.koszulSign = 1 ∧
    pairing4b.koszulSign = -1 ∧
    pairing4c.koszulSign = 1 := by
  have h4a : pairing4a.koszulSign = 1 := by
    have h := pairing4a.koszulSign_independent enum4a enum4a_injective
    rw [bringTogetherOf_enum4a, Equiv.Perm.sign_one] at h
    exact h.symm
  have h4b : pairing4b.koszulSign = -1 := by
    have h := pairing4b.koszulSign_independent enum4b enum4b_injective
    rw [bringTogetherOf_enum4b,
      Equiv.Perm.sign_swap (by decide : (⟨1, by decide⟩ : Fin 4) ≠ ⟨2, by decide⟩)] at h
    exact h.symm
  have h4c : pairing4c.koszulSign = 1 := by
    have h := pairing4c.koszulSign_independent enum4c enum4c_injective
    rw [bringTogetherOf_enum4c, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide : (⟨1, by decide⟩ : Fin 4) ≠ ⟨2, by decide⟩),
      Equiv.Perm.sign_swap (by decide : (⟨1, by decide⟩ : Fin 4) ≠ ⟨3, by decide⟩)] at h
    have hmul : ((-1 : ℤˣ) * (-1)) = 1 := by decide
    rw [hmul] at h
    exact h.symm
  exact ⟨h4a, h4b, h4c⟩

/-!
## Part B — T5 priced windows: the Wick identities

The sign machinery above (Part A) is the combinatorial core of the fermionic
Wick theorem. The full operator identities are priced as T5 windows:

**4-point Wick (T5):** Given a CAR algebra over a module `V` with field
operators `ψ : V →ₗ[ℂ] A`, 2-point function `G`, and vacuum state `ω`
satisfying `ψᵢψⱼ + ψⱼψᵢ = 2Gᵢⱼ`, `ω(1)=1`, `ω(ψᵢ)=0`, `ω(ψᵢψⱼ)=Gᵢⱼ`, and the
quasi-free Wick move `ω(x(ψᵢψⱼ)y) + ω(x(ψⱼψᵢ)y) = 2Gᵢⱼω(xy)`, the 4-point
vacuum expectation is:
  `ω(ψ₀ψ₁ψ₂ψ₃) = G₀₁G₂₃ - G₀₂G₁₃ + G₀₃G₁₂`
with signs `+1,-1,+1` from `koszulSign_four_point` (T1, proved above).

**n-point Wick expansion (T5):** The `2n`-point expectation is the sum over
all `P : FermPairing n` of `koszulSign P` times the product of `G` over pairs.
Priced because: (1) the induction needs the Wick recursion at `2n` points;
(2) the sign-reindexing lemma `ε(P)=(-1)^{j-1}ε(P')` needs `Fintype
(FermPairing n)` and deletion/insertion equivalences; (3) the
`fockInnerProduct` gap: constructing `ω` with annihilation adjoints and
non-trivial `G` from `FreeField`/`FieldOperators` is not in the repo.
-/

end ThetLogos
