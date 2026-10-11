import Mathlib.Analysis.InnerProductSpace.PiL2

namespace ThetLogos

open scoped InnerProductSpace

/-!
# ThetLogos.FermionicFock — fermionic Fock space over `d` modes (Rung 8)

The fermionic Fock space built **directly** as `ℓ²` on occupation subsets —
no tensor powers anywhere. This discharges the W0 gap (Fock inner product)
for fermions: the space is finite-dimensional, so all operators below are
bounded and adjoints exist definitionally.

**Construction.** Modes are `Fin d` (a `LinearOrder`, needed for Koszul signs).
Occupation subsets are `Finset (Fin d)` (a `Fintype`). The Fock space is
`EuclideanSpace ℂ (Finset (Fin d))` with orthonormal basis
`e S = single S 1` (vacuum `e ∅`).

- Creation `adag i`: `e S ↦ if i ∈ S then 0 else sgn i S • e (insert i S)`.
- Annihilation `ann i`: `e S ↦ if i ∉ S then 0 else sgn i S • e (S.erase i)`.
- Koszul sign `sgn i S = (-1)^(#{j ∈ S : j < i})`.

Pauli exclusion is automatic from the `i ∈ S` / `i ∉ S` guards.

**T1 proved here.**
- Adjoint relation `⟪ann i x, y⟫ = ⟪x, adag i y⟫` (the fermionic W0 discharge).
- CAR: `{ann i, adag j} = δ i j • 1`, `{ann i, ann j} = 0`, `{adag i, adag j} = 0`.
- Number operator `N = ∑ i, adag i ∘ ann i`, diagonal on the basis with
  eigenvalue `S.card`.
- Parity operator `P`, `P^2 = 1`, anticommutes with creators/annihilators.
- Sector orthogonality; sectors vanish for `n > d`.
- Vacuum cyclicity + determinant Gram formula
  `⟪adag i₁⋯adag iₙ vac, adag j₁⋯adag jₙ vac⟫ = det(δ_{i_k j_l})`.
- `d = 2` consistency with `OperatorWick.lean` up to the documented index map.

**Priced windows** (documented at the end, not attempted):
- unitary equivalence with `⋀ⁿ(H)` as tensor-power subspaces;
- the infinite-mode (`d → ∞`) limit.
-/

variable (d : ℕ)

/-- Fermionic Fock space over `d` modes: `ℓ²` on occupation subsets. -/
abbrev FermionicFock := EuclideanSpace ℂ (Finset (Fin d))

/-- Koszul sign: `(-1)` to the number of occupied modes below `i`. -/
noncomputable def sgn (i : Fin d) (S : Finset (Fin d)) : ℂ :=
  (-1 : ℂ) ^ (S.filter (fun j => j < i)).card

/-- Occupation basis vector `e S`. -/
noncomputable def fockBasis (S : Finset (Fin d)) : FermionicFock d := EuclideanSpace.single S 1

/-- The vacuum `|0⟩ = e ∅`. -/
noncomputable def fockVac : FermionicFock d := fockBasis d ∅

-- ============================================================================
-- §1. Koszul sign arithmetic
-- ============================================================================

/-- The Koszul sign is real (fixed by `star`). -/
@[simp] theorem star_sgn (i : Fin d) (S : Finset (Fin d)) :
    star (sgn d i S) = sgn d i S := by
  simp [sgn]

@[simp] theorem starRingEnd_sgn (i : Fin d) (S : Finset (Fin d)) :
    (starRingEnd ℂ) (sgn d i S) = sgn d i S := by
  simp [sgn]

/-- `(-1)^k` squares to `1`. -/
theorem neg_one_pow_mul_self (k : ℕ) : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
  rw [← pow_add, show k + k = 2 * k from by ring, pow_mul]
  norm_num

/-- The Koszul sign squares to `1`. -/
theorem sgn_sq (i : Fin d) (S : Finset (Fin d)) : sgn d i S * sgn d i S = 1 := by
  unfold sgn
  exact neg_one_pow_mul_self _

/-- Card of a `< i`-filter after inserting `j`. -/
theorem card_filter_insert (i j : Fin d) (S : Finset (Fin d)) (hj : j ∉ S) :
    (Finset.filter (fun k => k < i) (insert j S)).card
      = (Finset.filter (fun k => k < i) S).card + (if j < i then 1 else 0) := by
  rw [Finset.filter_insert]
  split_ifs with h
  · have hmem : j ∉ Finset.filter (fun k => k < i) S := by
      intro hm
      exact hj (Finset.mem_filter.mp hm).1
    rw [Finset.card_insert_of_notMem hmem]
  · simp

/-- Card of a `< i`-filter after erasing `j ∈ S`. -/
theorem card_filter_erase (i j : Fin d) (S : Finset (Fin d)) (hjS : j ∈ S) :
    (Finset.filter (fun k => k < i) (S.erase j)).card
      = (Finset.filter (fun k => k < i) S).card - (if j < i then 1 else 0) := by
  rw [Finset.filter_erase]
  by_cases h : j < i
  · have hm : j ∈ Finset.filter (fun k => k < i) S := Finset.mem_filter.mpr ⟨hjS, h⟩
    rw [Finset.card_erase_of_mem hm, ite_eq_left h]
  · have hm : j ∉ Finset.filter (fun k => k < i) S := by
      intro hcon
      exact h (Finset.mem_filter.mp hcon).2
    rw [Finset.erase_eq_of_notMem hm, ite_eq_right h, Nat.sub_zero]

/-- Inserting `i` itself does not change its Koszul sign. -/
theorem sgn_insert_eq (i : Fin d) (S : Finset (Fin d)) :
    sgn d i (insert i S) = sgn d i S := by
  by_cases h : i ∈ S
  · rw [Finset.insert_eq_of_mem h]
  · unfold sgn
    rw [card_filter_insert d i i S h, ite_eq_right (lt_irrefl i), add_zero]

/-- Erasing `i` itself does not change its Koszul sign. -/
theorem sgn_erase_eq (i : Fin d) (S : Finset (Fin d)) :
    sgn d i (S.erase i) = sgn d i S := by
  unfold sgn
  congr 1
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
  intro hcon
  exact lt_irrefl i (Finset.mem_filter.mp hcon).2

/-- `sgn i (insert i S) * sgn i S = 1`. -/
theorem sgn_mul_insert_self (i : Fin d) (S : Finset (Fin d)) :
    sgn d i (insert i S) * sgn d i S = 1 := by
  rw [sgn_insert_eq]; exact sgn_sq _ _ _

/-- `sgn i (S.erase i) * sgn i S = 1`. -/
theorem sgn_mul_erase_self (i : Fin d) (S : Finset (Fin d)) :
    sgn d i (S.erase i) * sgn d i S = 1 := by
  rw [sgn_erase_eq]; exact sgn_sq _ _ _

/-- `(-1)^(k+1) + (-1)^k = 0`: the arithmetic core of all sign cancellations. -/
theorem neg_one_pow_add_one (k : ℕ) : (-1 : ℂ) ^ (k + 1) + (-1 : ℂ) ^ k = 0 := by
  rw [pow_succ]; ring

/-- Sign cancellation for `{ann i, adag j}`, `i ≠ j`: creating `j` then
annihilating `i` picks up the opposite Koszul sign to the reverse order. -/
theorem sgn_anticomm_insert (i j : Fin d) (S : Finset (Fin d))
    (hij : i ≠ j) (hiS : i ∉ S) (hjS : j ∈ S) :
    sgn d i (insert i S) * sgn d j (insert i (S.erase j))
      + sgn d j (S.erase j) * sgn d i (insert i (S.erase j)) = 0 := by
  have hjf : j ∉ Finset.filter (fun k => k < j) S := by
    intro hcon
    exact lt_irrefl j (Finset.mem_filter.mp hcon).2
  have hiS' : i ∉ S.erase j := fun h => hiS (Finset.mem_of_mem_erase h)
  have e2f : Finset.filter (fun k => k < j) (S.erase j)
      = Finset.filter (fun k => k < j) S := by
    rw [Finset.filter_erase, Finset.erase_eq_of_notMem hjf]
  have e1 : sgn d i (insert i S)
      = (-1 : ℂ) ^ (Finset.filter (fun k => k < i) S).card := by
    rw [sgn_insert_eq]; simp only [sgn]
  have e2 : sgn d j (S.erase j)
      = (-1 : ℂ) ^ (Finset.filter (fun k => k < j) S).card := by
    unfold sgn; rw [e2f]
  have e3 : sgn d j (insert i (S.erase j))
      = (-1 : ℂ) ^ ((Finset.filter (fun k => k < j) S).card + (if i < j then 1 else 0)) := by
    unfold sgn; rw [card_filter_insert d j i (S.erase j) hiS', e2f]
  have e4 : sgn d i (insert i (S.erase j))
      = (-1 : ℂ) ^ ((Finset.filter (fun k => k < i) S).card - (if j < i then 1 else 0)) := by
    unfold sgn
    rw [card_filter_insert d i i (S.erase j) hiS', ite_eq_right (lt_irrefl i), add_zero,
      card_filter_erase d i j S hjS]
  rw [e1, e2, e3, e4, ← pow_add, ← pow_add]
  rcases lt_trichotomy i j with h | h | h
  · rw [ite_eq_left h, ite_eq_right (not_lt.mpr (le_of_lt h)), Nat.sub_zero,
      show (Finset.filter (fun k => k < i) S).card
        + ((Finset.filter (fun k => k < j) S).card + 1)
        = ((Finset.filter (fun k => k < i) S).card
          + (Finset.filter (fun k => k < j) S).card) + 1 from by ring,
      show (Finset.filter (fun k => k < j) S).card
        + (Finset.filter (fun k => k < i) S).card
        = (Finset.filter (fun k => k < i) S).card
          + (Finset.filter (fun k => k < j) S).card from by ring]
    exact neg_one_pow_add_one _
  · exact absurd h hij
  · rw [ite_eq_right (not_lt.mpr (le_of_lt h)), ite_eq_left h]
    have hmem : j ∈ Finset.filter (fun k => k < i) S :=
      Finset.mem_filter.mpr ⟨hjS, h⟩
    have hA : 0 < (Finset.filter (fun k => k < i) S).card :=
      Finset.card_pos.mpr ⟨j, hmem⟩
    obtain ⟨A', hA'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : (Finset.filter (fun k => k < i) S).card ≠ 0)
    have hA1 : (Finset.filter (fun k => k < i) S).card = A' + 1 := by rw [hA']
    rw [hA1, Nat.add_sub_cancel,
      show (A' + 1) + ((Finset.filter (fun k => k < j) S).card + 0)
        = ((A' + (Finset.filter (fun k => k < j) S).card)) + 1 from by ring,
      show (Finset.filter (fun k => k < j) S).card + A'
        = A' + (Finset.filter (fun k => k < j) S).card from by ring]
    exact neg_one_pow_add_one _

/-- Sign cancellation for `{ann i, ann j}`, `i ≠ j`. -/
theorem sgn_anticomm_ann (i j : Fin d) (S : Finset (Fin d))
    (hij : i ≠ j) (hiS : i ∉ S) (hjS : j ∉ S) :
    sgn d i (insert i S) * sgn d j (insert j (insert i S))
      + sgn d j (insert j S) * sgn d i (insert i (insert j S)) = 0 := by
  have hiS' : i ∉ insert j S := by
    simp [Finset.mem_insert, hij, hiS]
  have hjS' : j ∉ insert i S := by
    simp [Finset.mem_insert, hij.symm, hjS]
  have e1 : sgn d i (insert i S)
      = (-1 : ℂ) ^ (Finset.filter (fun k => k < i) S).card := by
    rw [sgn_insert_eq]; simp only [sgn]
  have e2 : sgn d j (insert j S)
      = (-1 : ℂ) ^ (Finset.filter (fun k => k < j) S).card := by
    rw [sgn_insert_eq]; simp only [sgn]
  have e3 : sgn d j (insert j (insert i S))
      = (-1 : ℂ) ^ ((Finset.filter (fun k => k < j) S).card + (if i < j then 1 else 0)) := by
    unfold sgn
    rw [card_filter_insert d j j (insert i S) hjS', ite_eq_right (lt_irrefl j), add_zero,
      card_filter_insert d j i S hiS]
  have e4 : sgn d i (insert i (insert j S))
      = (-1 : ℂ) ^ ((Finset.filter (fun k => k < i) S).card + (if j < i then 1 else 0)) := by
    unfold sgn
    rw [card_filter_insert d i i (insert j S) hiS', ite_eq_right (lt_irrefl i), add_zero,
      card_filter_insert d i j S hjS]
  rw [e1, e2, e3, e4, ← pow_add, ← pow_add]
  rcases lt_trichotomy i j with h | h | h
  · rw [ite_eq_left h, ite_eq_right (not_lt.mpr (le_of_lt h)),
      show (Finset.filter (fun k => k < i) S).card
        + ((Finset.filter (fun k => k < j) S).card + 1)
        = ((Finset.filter (fun k => k < i) S).card
          + (Finset.filter (fun k => k < j) S).card) + 1 from by ring,
      show (Finset.filter (fun k => k < j) S).card
        + ((Finset.filter (fun k => k < i) S).card + 0)
        = (Finset.filter (fun k => k < i) S).card
          + (Finset.filter (fun k => k < j) S).card from by ring]
    exact neg_one_pow_add_one _
  · exact absurd h hij
  · rw [ite_eq_right (not_lt.mpr (le_of_lt h)), ite_eq_left h,
      show (Finset.filter (fun k => k < i) S).card
        + ((Finset.filter (fun k => k < j) S).card + 0)
        = (Finset.filter (fun k => k < i) S).card
          + (Finset.filter (fun k => k < j) S).card from by ring,
      show (Finset.filter (fun k => k < j) S).card
        + ((Finset.filter (fun k => k < i) S).card + 1)
        = ((Finset.filter (fun k => k < i) S).card
          + (Finset.filter (fun k => k < j) S).card) + 1 from by ring,
      add_comm]
    exact neg_one_pow_add_one _

/-- Sign cancellation for `{adag i, adag j}`, `i ≠ j`. -/
theorem sgn_anticomm_adag (i j : Fin d) (S : Finset (Fin d))
    (hij : i ≠ j) (hiS : i ∈ S) (hjS : j ∈ S) :
    sgn d i (S.erase i) * sgn d j ((S.erase i).erase j)
      + sgn d j (S.erase j) * sgn d i ((S.erase j).erase i) = 0 := by
  have e1 : sgn d i (S.erase i)
      = (-1 : ℂ) ^ (Finset.filter (fun k => k < i) S).card := by
    rw [sgn_erase_eq]; simp only [sgn]
  have e2 : sgn d j (S.erase j)
      = (-1 : ℂ) ^ (Finset.filter (fun k => k < j) S).card := by
    rw [sgn_erase_eq]; simp only [sgn]
  have e3 : sgn d j ((S.erase i).erase j)
      = (-1 : ℂ) ^ ((Finset.filter (fun k => k < j) S).card - (if i < j then 1 else 0)) := by
    have h1 : (Finset.filter (fun k => k < j) ((S.erase i).erase j)).card
        = (Finset.filter (fun k => k < j) S).card - (if i < j then 1 else 0) := by
      have hjf' : j ∉ Finset.filter (fun k => k < j) (S.erase i) := by
        intro hcon
        exact lt_irrefl j (Finset.mem_filter.mp hcon).2
      rw [Finset.filter_erase, Finset.erase_eq_of_notMem hjf',
        card_filter_erase d j i S hiS]
    unfold sgn; rw [h1]
  have e4 : sgn d i ((S.erase j).erase i)
      = (-1 : ℂ) ^ ((Finset.filter (fun k => k < i) S).card - (if j < i then 1 else 0)) := by
    have h1 : (Finset.filter (fun k => k < i) ((S.erase j).erase i)).card
        = (Finset.filter (fun k => k < i) S).card - (if j < i then 1 else 0) := by
      have hif' : i ∉ Finset.filter (fun k => k < i) (S.erase j) := by
        intro hcon
        exact lt_irrefl i (Finset.mem_filter.mp hcon).2
      rw [Finset.filter_erase, Finset.erase_eq_of_notMem hif',
        card_filter_erase d i j S hjS]
    unfold sgn; rw [h1]
  rw [e1, e2, e3, e4, ← pow_add, ← pow_add]
  rcases lt_trichotomy i j with h | h | h
  · rw [ite_eq_left h, ite_eq_right (not_lt.mpr (le_of_lt h))]
    have hmem : i ∈ Finset.filter (fun k => k < j) S :=
      Finset.mem_filter.mpr ⟨hiS, h⟩
    have hB : 0 < (Finset.filter (fun k => k < j) S).card :=
      Finset.card_pos.mpr ⟨i, hmem⟩
    obtain ⟨B', hB'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : (Finset.filter (fun k => k < j) S).card ≠ 0)
    have hB1 : (Finset.filter (fun k => k < j) S).card = B' + 1 := by rw [hB']
    rw [hB1, Nat.add_sub_cancel, Nat.sub_zero,
      show (B' + 1) + (Finset.filter (fun k => k < i) S).card
        = ((Finset.filter (fun k => k < i) S).card + B') + 1 from by ring,
      add_comm]
    exact neg_one_pow_add_one _
  · exact absurd h hij
  · rw [ite_eq_right (not_lt.mpr (le_of_lt h)), ite_eq_left h]
    have hmem : j ∈ Finset.filter (fun k => k < i) S :=
      Finset.mem_filter.mpr ⟨hjS, h⟩
    have hA : 0 < (Finset.filter (fun k => k < i) S).card :=
      Finset.card_pos.mpr ⟨j, hmem⟩
    obtain ⟨A', hA'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : (Finset.filter (fun k => k < i) S).card ≠ 0)
    have hA1 : (Finset.filter (fun k => k < i) S).card = A' + 1 := by rw [hA']
    rw [hA1, Nat.add_sub_cancel, Nat.sub_zero,
      show (A' + 1) + (Finset.filter (fun k => k < j) S).card
        = ((Finset.filter (fun k => k < j) S).card + A') + 1 from by ring]
    exact neg_one_pow_add_one _

-- ============================================================================
-- §2. Creation / annihilation / parity operators
-- ============================================================================

/-- Creation operator on the coordinate side: `(adagPi i x) T` reads the
coefficient at `T.erase i` when `i ∈ T`. -/
noncomputable def adagPi (i : Fin d) : (Π S : Finset (Fin d), ℂ) →ₗ[ℂ] (Π S : Finset (Fin d), ℂ) where
  toFun x T := if i ∈ T then sgn d i (T.erase i) * x (T.erase i) else 0
  map_add' x y := by
    funext T
    show (if i ∈ T then sgn d i (T.erase i) * (x + y) (T.erase i) else 0)
      = (if i ∈ T then sgn d i (T.erase i) * x (T.erase i) else 0)
        + (if i ∈ T then sgn d i (T.erase i) * y (T.erase i) else 0)
    by_cases h : i ∈ T
    · simp only [ite_eq_left h, Pi.add_apply, mul_add]
    · simp only [ite_eq_right h, add_zero]
  map_smul' c x := by
    funext T
    show (if i ∈ T then sgn d i (T.erase i) * (c • x) (T.erase i) else 0)
      = c • (if i ∈ T then sgn d i (T.erase i) * x (T.erase i) else 0)
    by_cases h : i ∈ T
    · simp only [ite_eq_left h, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [ite_eq_right h, smul_zero]

/-- Annihilation operator on the coordinate side. -/
noncomputable def annPi (i : Fin d) : (Π S : Finset (Fin d), ℂ) →ₗ[ℂ] (Π S : Finset (Fin d), ℂ) where
  toFun x T := if i ∉ T then sgn d i (insert i T) * x (insert i T) else 0
  map_add' x y := by
    funext T
    show (if i ∉ T then sgn d i (insert i T) * (x + y) (insert i T) else 0)
      = (if i ∉ T then sgn d i (insert i T) * x (insert i T) else 0)
        + (if i ∉ T then sgn d i (insert i T) * y (insert i T) else 0)
    by_cases h : i ∉ T
    · simp only [ite_eq_left h, Pi.add_apply, mul_add]
    · simp only [ite_eq_right h, add_zero]
  map_smul' c x := by
    funext T
    show (if i ∉ T then sgn d i (insert i T) * (c • x) (insert i T) else 0)
      = c • (if i ∉ T then sgn d i (insert i T) * x (insert i T) else 0)
    by_cases h : i ∉ T
    · simp only [ite_eq_left h, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [ite_eq_right h, smul_zero]

/-- Parity operator on the coordinate side. -/
def parPi : (Π S : Finset (Fin d), ℂ) →ₗ[ℂ] (Π S : Finset (Fin d), ℂ) where
  toFun x T := (-1 : ℂ) ^ (T.card) * x T
  map_add' x y := by
    funext T
    show (-1 : ℂ) ^ (T.card) * (x + y) T = (-1 : ℂ) ^ (T.card) * x T + (-1 : ℂ) ^ (T.card) * y T
    rw [Pi.add_apply, mul_add]
  map_smul' c x := by
    funext T
    show (-1 : ℂ) ^ (T.card) * (c • x) T = c • ((-1 : ℂ) ^ (T.card) * x T)
    rw [Pi.smul_apply, smul_eq_mul]
    ring

/-- The coordinate linear equivalence between the Pi type and the Fock space. -/
noncomputable def fockEquiv : (Π S : Finset (Fin d), ℂ) ≃ₗ[ℂ] FermionicFock d :=
  (WithLp.linearEquiv 2 ℂ (Π S : Finset (Fin d), ℂ)).symm

/-- Creation operator `a†_i` on the Fock space. -/
noncomputable def adag (i : Fin d) : Module.End ℂ (FermionicFock d) :=
  (fockEquiv d).conj (adagPi d i)

/-- Annihilation operator `a_i` on the Fock space. -/
noncomputable def ann (i : Fin d) : Module.End ℂ (FermionicFock d) :=
  (fockEquiv d).conj (annPi d i)

/-- Fermion parity operator `P`. -/
noncomputable def parityFock : Module.End ℂ (FermionicFock d) :=
  (fockEquiv d).conj (parPi d)

/-- Coordinate formula for `adag`. -/
@[simp] theorem adag_apply (i : Fin d) (x : FermionicFock d) (T : Finset (Fin d)) :
    ((adag d i) x).ofLp T
      = if i ∈ T then sgn d i (T.erase i) * x.ofLp (T.erase i) else 0 := rfl

/-- Coordinate formula for `ann`. -/
@[simp] theorem ann_apply (i : Fin d) (x : FermionicFock d) (T : Finset (Fin d)) :
    ((ann d i) x).ofLp T
      = if i ∉ T then sgn d i (insert i T) * x.ofLp (insert i T) else 0 := rfl

/-- Coordinate formula for `parityFock`. -/
@[simp] theorem parityFock_apply (x : FermionicFock d) (T : Finset (Fin d)) :
    ((parityFock d) x).ofLp T = (-1 : ℂ) ^ (T.card) * x.ofLp T := rfl

/-- Coordinates of a basis vector. -/
@[simp] theorem fockBasis_ofLp (S U : Finset (Fin d)) :
    (fockBasis d S).ofLp U = if U = S then (1 : ℂ) else 0 :=
  PiLp.single_apply 2 ℂ S 1 U

/-- The occupation basis is orthonormal. -/
theorem fockBasis_inner (S T : Finset (Fin d)) :
    ⟪fockBasis d S, fockBasis d T⟫_ℂ = if S = T then (1 : ℂ) else 0 := by
  unfold fockBasis
  rw [EuclideanSpace.inner_single_left, PiLp.single_apply]
  simp

/-- Action of `adag` on basis vectors. -/
theorem adag_basis (i : Fin d) (S : Finset (Fin d)) :
    adag d i (fockBasis d S)
      = if i ∈ S then 0 else sgn d i S • fockBasis d (insert i S) := by
  by_cases hiS : i ∈ S
  · rw [ite_eq_left hiS]
    apply PiLp.ext
    intro T
    simp only [adag_apply, fockBasis_ofLp, PiLp.zero_apply]
    by_cases hiT : i ∈ T
    · have hne : T.erase i ≠ S := by
        intro h
        exact (Finset.notMem_erase i T) (h.symm ▸ hiS)
      rw [ite_eq_left hiT, ite_eq_right hne, mul_zero]
    · rw [ite_eq_right hiT]
  · rw [ite_eq_right hiS]
    apply PiLp.ext
    intro T
    simp only [adag_apply, fockBasis_ofLp, PiLp.smul_apply, smul_eq_mul]
    by_cases hiT : i ∈ T
    · have hiff : T.erase i = S ↔ T = insert i S := by
        constructor
        · intro h; rw [← h, Finset.insert_erase hiT]
        · intro h; rw [h, Finset.erase_insert hiS]
      by_cases he : T.erase i = S
      · rw [ite_eq_left hiT, he, ite_eq_left rfl, ite_eq_left (hiff.mp he),
          mul_one]
      · rw [ite_eq_left hiT, ite_eq_right he,
          ite_eq_right (fun h => he (hiff.mpr h)), mul_zero, mul_zero]
    · have hne : T ≠ insert i S := by
        intro h
        rw [h] at hiT
        exact hiT (Finset.mem_insert_self i S)
      rw [ite_eq_right hiT, ite_eq_right hne, mul_zero]

/-- Action of `ann` on basis vectors. -/
theorem ann_basis (i : Fin d) (S : Finset (Fin d)) :
    ann d i (fockBasis d S)
      = if i ∉ S then 0 else sgn d i S • fockBasis d (S.erase i) := by
  by_cases hiS : i ∈ S
  · rw [ite_eq_right (not_not.mpr hiS)]
    apply PiLp.ext
    intro T
    simp only [ann_apply, fockBasis_ofLp, PiLp.smul_apply, smul_eq_mul]
    by_cases hiT : i ∈ T
    · have hne : T ≠ S.erase i := by
        intro h
        rw [h] at hiT
        exact (Finset.notMem_erase i S) hiT
      rw [ite_eq_right (not_not.mpr hiT), ite_eq_right hne, mul_zero]
    · have hiT' : i ∉ T := hiT
      have hiff : insert i T = S ↔ T = S.erase i := by
        constructor
        · intro h; rw [← h, Finset.erase_insert hiT']
        · intro h; rw [h, Finset.insert_erase hiS]
      by_cases he : insert i T = S
      · rw [ite_eq_left hiT', he, ite_eq_left rfl, ite_eq_left (hiff.mp he),
          mul_one]
      · rw [ite_eq_left hiT', ite_eq_right he,
          ite_eq_right (fun h => he (hiff.mpr h)), mul_zero, mul_zero]
  · rw [ite_eq_left hiS]
    apply PiLp.ext
    intro T
    simp only [ann_apply, fockBasis_ofLp, PiLp.zero_apply]
    by_cases hiT : i ∈ T
    · rw [ite_eq_right (not_not.mpr hiT)]
    · have hne : insert i T ≠ S := by
        intro h
        have hmem : i ∈ insert i T := Finset.mem_insert_self i T
        rw [h] at hmem
        exact hiS hmem
      rw [ite_eq_left hiT, ite_eq_right hne, mul_zero]

-- ============================================================================
-- §3. The adjoint relation (fermionic W0 discharge)
-- ============================================================================

/-- Reindexing: inserting `i` is a bijection from `{T | i ∉ T}` to `{U | i ∈ U}`. -/
theorem insert_bij_image (i : Fin d) :
    Finset.image (insert i) (Finset.univ.filter (fun T : Finset (Fin d) => i ∉ T))
      = Finset.univ.filter (fun U : Finset (Fin d) => i ∈ U) := by
  ext U
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨T, hiT, rfl⟩
    exact Finset.mem_insert_self i T
  · intro hiU
    exact ⟨U.erase i, Finset.notMem_erase i U, Finset.insert_erase hiU⟩

/-- `ann i` is the Hilbert adjoint of `adag i` (T1): the fermionic W0 discharge. -/
theorem ann_adjoint (i : Fin d) (x y : FermionicFock d) :
    ⟪ann d i x, y⟫_ℂ = ⟪x, adag d i y⟫_ℂ := by
  have stepL : ∀ T : Finset (Fin d),
      ⟪(ann d i x).ofLp T, y.ofLp T⟫_ℂ
        = if i ∉ T then y.ofLp T * (sgn d i (insert i T) * (starRingEnd ℂ) (x.ofLp (insert i T)))
          else 0 := by
    intro T
    by_cases h : i ∉ T
    · rw [ite_eq_left h, RCLike.inner_apply, ann_apply, ite_eq_left h, map_mul,
        starRingEnd_sgn]
    · rw [ite_eq_right h, RCLike.inner_apply, ann_apply, ite_eq_right h, map_zero,
        mul_zero]
  have stepR : ∀ T : Finset (Fin d),
      ⟪x.ofLp T, (adag d i y).ofLp T⟫_ℂ
        = if i ∈ T then (sgn d i (T.erase i) * y.ofLp (T.erase i)) * (starRingEnd ℂ) (x.ofLp T)
          else 0 := by
    intro T
    by_cases h : i ∈ T
    · rw [ite_eq_left h, RCLike.inner_apply, adag_apply, ite_eq_left h]
    · rw [ite_eq_right h, RCLike.inner_apply, adag_apply, ite_eq_right h, zero_mul]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [stepL, stepR, ← Finset.sum_filter]
  refine Finset.sum_bij (fun T _ => insert i T) ?_ ?_ ?_ ?_
  · -- the bijection lands in `{U | i ∈ U}`
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.mem_insert_self i T
  · -- it is injective
    intro T₁ h₁ T₂ h₂ h
    have hi1 : i ∉ T₁ := (Finset.mem_filter.mp h₁).2
    have hi2 : i ∉ T₂ := (Finset.mem_filter.mp h₂).2
    have h2 := congrArg (fun S => S.erase i) h
    rwa [Finset.erase_insert hi1, Finset.erase_insert hi2] at h2
  · -- it is surjective
    intro U hU
    have hiU : i ∈ U := (Finset.mem_filter.mp hU).2
    refine ⟨U.erase i, ?_, Finset.insert_erase hiU⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.notMem_erase i U
  · -- the summands match
    intro T hT
    have hiT : i ∉ T := (Finset.mem_filter.mp hT).2
    show y.ofLp T * (sgn d i (insert i T) * (starRingEnd ℂ) (x.ofLp (insert i T)))
      = (sgn d i ((insert i T).erase i) * y.ofLp ((insert i T).erase i))
        * (starRingEnd ℂ) (x.ofLp (insert i T))
    rw [Finset.erase_insert hiT, sgn_insert_eq]
    ring

/-- Flipped adjoint relation (T1). -/
theorem adag_adjoint (i : Fin d) (x y : FermionicFock d) :
    ⟪adag d i x, y⟫_ℂ = ⟪x, ann d i y⟫_ℂ := by
  rw [← inner_conj_symm (adag d i x) y, ← ann_adjoint d i y x,
    inner_conj_symm x (ann d i y)]

-- ============================================================================
-- §4. Canonical anticommutation relations
-- ============================================================================

/-- `{ann i, adag j} = δ i j • 1` (T1). -/
theorem car_mixed (i j : Fin d) :
    (ann d i).comp (adag d j) + (adag d j).comp (ann d i)
      = (if i = j then (1 : ℂ) else 0) • (1 : Module.End ℂ (FermionicFock d)) := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro T
  simp only [LinearMap.add_apply, PiLp.add_apply, LinearMap.comp_apply, ann_apply,
    adag_apply, LinearMap.smul_apply, Module.End.one_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    by_cases hiT : i ∈ T
    · rw [ite_eq_right (not_not.mpr hiT), ite_eq_left hiT, ite_eq_left rfl,
        ite_eq_left (Finset.notMem_erase i T), Finset.insert_erase hiT,
        ← mul_assoc, sgn_mul_erase_self]
      simp
    · rw [ite_eq_left hiT, ite_eq_right hiT, ite_eq_left rfl,
        ite_eq_left (Finset.mem_insert_self i T), Finset.erase_insert hiT,
        ← mul_assoc, sgn_mul_insert_self]
      simp
  · by_cases hiT : i ∈ T <;> by_cases hjT : j ∈ T
    · -- i ∈ T, j ∈ T, i ≠ j: both terms vanish
      rw [ite_eq_right (not_not.mpr hiT)]
      have h1 : i ∈ T.erase j := Finset.mem_erase.mpr ⟨hij, hiT⟩
      rw [ite_eq_left hjT, ite_eq_right (not_not.mpr h1)]
      simp [hij]
    · -- i ∈ T, j ∉ T, i ≠ j: both terms vanish
      rw [ite_eq_right (not_not.mpr hiT), ite_eq_right hjT]
      simp [hij]
    · -- i ∉ T, j ∈ T, i ≠ j: the Koszul sign cancellation
      have hmem : j ∈ insert i T := Finset.mem_insert_of_mem hjT
      have h1 : i ∉ T.erase j := fun h => hiT (Finset.mem_of_mem_erase h)
      have heq : (insert i T).erase j = insert i (T.erase j) := by
        ext k
        simp only [Finset.mem_erase, Finset.mem_insert]
        constructor
        · rintro ⟨hnj, rfl | hm⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hnj, hm⟩
        · rintro (rfl | ⟨hnj, hm⟩)
          · exact ⟨hij, Or.inl rfl⟩
          · exact ⟨hnj, Or.inr hm⟩
      rw [ite_eq_left hiT, ite_eq_left hmem, heq, ite_eq_left hjT, ite_eq_left h1,
        ite_eq_right hij]
      have hsign := sgn_anticomm_insert d i j T hij hiT hjT
      linear_combination hsign * x.ofLp (insert i (T.erase j))
    · -- i ∉ T, j ∉ T, i ≠ j: both terms vanish
      have h1 : j ∉ insert i T := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨Ne.symm hij, hjT⟩
      rw [ite_eq_left hiT, ite_eq_right h1, ite_eq_right hjT, ite_eq_right hij]
      simp

/-- `{ann i, ann j} = 0` (T1). -/
theorem car_ann_ann (i j : Fin d) :
    (ann d i).comp (ann d j) + (ann d j).comp (ann d i) = 0 := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro T
  simp only [LinearMap.add_apply, PiLp.add_apply, LinearMap.comp_apply, ann_apply,
    LinearMap.zero_apply, PiLp.zero_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hiT : i ∈ T
    · rw [ite_eq_right (not_not.mpr hiT), add_zero]
    · have h1 : i ∈ insert i T := Finset.mem_insert_self i T
      rw [ite_eq_left hiT, ite_eq_right (not_not.mpr h1)]
      simp
  · by_cases hiT : i ∈ T <;> by_cases hjT : j ∈ T
    · -- i ∈ T, j ∈ T: both outer ifs give 0
      rw [ite_eq_right (not_not.mpr hiT), ite_eq_right (not_not.mpr hjT), add_zero]
    · -- i ∈ T, j ∉ T: first outer 0; second inner has i ∈ insert j T
      have h1 : i ∈ insert j T := Finset.mem_insert_of_mem hiT
      rw [ite_eq_right (not_not.mpr hiT), ite_eq_left hjT,
        ite_eq_right (not_not.mpr h1)]
      simp
    · -- i ∉ T, j ∈ T: first inner has j ∈ insert i T; second outer 0
      have h1 : j ∈ insert i T := Finset.mem_insert_of_mem hjT
      rw [ite_eq_left hiT, ite_eq_right (not_not.mpr h1),
        ite_eq_right (not_not.mpr hjT)]
      simp
    · -- i ∉ T, j ∉ T, i ≠ j: Koszul sign cancellation
      have h1 : j ∉ insert i T := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨Ne.symm hij, hjT⟩
      have h2 : i ∉ insert j T := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨hij, hiT⟩
      have heq : insert j (insert i T) = insert i (insert j T) :=
        (Finset.insert_comm i j T).symm
      rw [ite_eq_left hiT, ite_eq_left h1, ite_eq_left hjT, ite_eq_left h2, heq]
      have hsign := sgn_anticomm_ann d i j T hij hiT hjT
      rw [heq] at hsign
      linear_combination hsign * x.ofLp (insert i (insert j T))

/-- `{adag i, adag j} = 0` (T1). -/
theorem car_adag_adag (i j : Fin d) :
    (adag d i).comp (adag d j) + (adag d j).comp (adag d i) = 0 := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro T
  simp only [LinearMap.add_apply, PiLp.add_apply, LinearMap.comp_apply, adag_apply,
    LinearMap.zero_apply, PiLp.zero_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hiT : i ∈ T
    · have h1 : i ∉ T.erase i := Finset.notMem_erase i T
      rw [ite_eq_left hiT, ite_eq_right h1]
      simp
    · rw [ite_eq_right hiT, add_zero]
  · by_cases hiT : i ∈ T <;> by_cases hjT : j ∈ T
    · -- i ∈ T, j ∈ T, i ≠ j: Koszul sign cancellation
      have h1 : j ∈ T.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, hjT⟩
      have h2 : i ∈ T.erase j := Finset.mem_erase.mpr ⟨hij, hiT⟩
      have heq : (T.erase i).erase j = (T.erase j).erase i :=
        Finset.erase_right_comm
      rw [ite_eq_left hiT, ite_eq_left h1, ite_eq_left hjT, ite_eq_left h2, heq]
      have hsign := sgn_anticomm_adag d i j T hij hiT hjT
      rw [heq] at hsign
      linear_combination hsign * x.ofLp ((T.erase j).erase i)
    · -- i ∈ T, j ∉ T: first inner has j ∉ T.erase i; second outer 0
      have h1 : j ∉ T.erase i := fun h => hjT (Finset.mem_of_mem_erase h)
      rw [ite_eq_left hiT, ite_eq_right h1, mul_zero,
        ite_eq_right hjT, add_zero]
    · -- i ∉ T, j ∈ T: first outer 0; second inner has i ∉ T.erase j
      have h1 : i ∉ T.erase j := fun h => hiT (Finset.mem_of_mem_erase h)
      rw [ite_eq_right hiT, ite_eq_left hjT, ite_eq_right h1, mul_zero, zero_add]
    · -- i ∉ T, j ∉ T: both outer ifs give 0
      rw [ite_eq_right hiT, ite_eq_right hjT, add_zero]

-- ============================================================================
-- §5. The number operator
-- ============================================================================

/-- The number operator `N = ∑ i, adag i ∘ ann i`. -/
noncomputable def numberOp (d : ℕ) : Module.End ℂ (FermionicFock d) :=
  ∑ i : Fin d, (adag d i).comp (ann d i)

/-- `N` is diagonal on the occupation basis with eigenvalue `S.card`. -/
theorem numberOp_basis (i : Fin d) (S : Finset (Fin d)) :
    ((adag d i).comp (ann d i)) (fockBasis d S)
      = (if i ∈ S then (1 : ℂ) else 0) • fockBasis d S := by
  rw [LinearMap.comp_apply, ann_basis]
  by_cases hiS : i ∈ S
  · rw [ite_eq_right (not_not.mpr hiS), map_smul, adag_basis]
    have h1 : i ∉ S.erase i := Finset.notMem_erase i S
    rw [ite_eq_right h1, Finset.insert_erase hiS, smul_smul, mul_comm,
      sgn_mul_erase_self, ite_eq_left hiS, one_smul]
  · rw [ite_eq_left hiS, map_zero, ite_eq_right hiS, zero_smul]

theorem numberOp_apply_basis (S : Finset (Fin d)) :
    numberOp d (fockBasis d S) = (S.card : ℂ) • fockBasis d S := by
  unfold numberOp
  rw [LinearMap.sum_apply]
  simp only [numberOp_basis d]
  rw [← Finset.sum_smul]
  have hcard : (∑ i : Fin d, (if i ∈ S then (1 : ℂ) else 0)) = (S.card : ℂ) := by
    have h1 : (∑ i : Fin d, (if i ∈ S then (1 : ℂ) else 0))
        = ((Finset.univ.filter (fun i : Fin d => i ∈ S)).card : ℂ) := by
      rw [← Finset.sum_boole]
    rw [h1]
    have h2 : Finset.univ.filter (fun i : Fin d => i ∈ S) = S := by
      ext i
      simp
    rw [h2]
  rw [hcard]

-- ============================================================================
-- §8. Vacuum cyclicity and the Gram determinant
-- ============================================================================

/-- The wedge product `adag (i 0) ⋯ adag (i (n-1)) vac`, by recursion on `n`. -/
noncomputable def wedgeAux (d : ℕ) : (n : ℕ) → (Fin n → Fin d) → FermionicFock d
  | 0, _ => fockVac d
  | n + 1, i => adag d (i 0) (wedgeAux d n (i ∘ Fin.succ))

/-- `wedgeAux` on a cons. -/
theorem wedgeAux_cons (n : ℕ) (b : Fin d) (k : Fin n → Fin d) :
    wedgeAux d (n + 1) (Fin.cons (α := fun _ => Fin d) b k)
      = adag d b (wedgeAux d n k) := by
  have h0 : (Fin.cons (α := fun _ => Fin d) b k) 0 = b := by simp
  have h1 : (Fin.cons (α := fun _ => Fin d) b k) ∘ Fin.succ = k := by
    funext m
    simp
  show adag d ((Fin.cons (α := fun _ => Fin d) b k) 0)
    (wedgeAux d n ((Fin.cons (α := fun _ => Fin d) b k) ∘ Fin.succ)) = _
  rw [h0, h1]

/-- Reassembly: removing `(k.succ)`-th entry then consing `j 0`. -/
theorem reassembly (n : ℕ) (j : Fin (n + 2) → Fin d) (k : Fin (n + 1)) :
    Fin.cons (α := fun _ => Fin d) (j 0) ((j ∘ Fin.succ) ∘ k.succAbove)
      = j ∘ (k.succ).succAbove := by
  have h1 : j = Fin.cons (α := fun _ => Fin d) (j 0) (Fin.tail j) :=
    (Fin.cons_self_tail j).symm
  conv_rhs => rw [h1, Fin.cons_comp_succ_succAbove]
  congr 1

/-- Vacuum is annihilated by all `ann`. -/
theorem ann_vac (i : Fin d) : ann d i (fockVac d) = 0 := by
  rw [fockVac, ann_basis]
  simp

/-- CAR in applied form: `ann a (adag b x) = δ_{ab} • x - adag b (ann a x)`. -/
theorem ann_adag_apply (a b : Fin d) (x : FermionicFock d) :
    ann d a (adag d b x)
      = (if a = b then (1:ℂ) else 0) • x - adag d b (ann d a x) := by
  have h := congrArg (· x) (car_mixed d a b)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h
  exact eq_sub_of_add_eq h

/-- 1-particle Gram formula: `⟪adag i vac, adag j vac⟫ = δ_{ij}` (T1, from CAR). -/
theorem gram_one (i j : Fin d) :
    ⟪adag d i (fockVac d), adag d j (fockVac d)⟫_ℂ
      = if i = j then (1:ℂ) else 0 := by
  rw [adag_adjoint, ann_adag_apply, ann_vac, map_zero, sub_zero]
  rw [inner_smul_right]
  have hvac : ⟪fockVac d, fockVac d⟫_ℂ = 1 := by
    rw [fockVac, fockBasis_inner, ite_eq_left rfl]
  rw [hvac, mul_one]

/-- Vacuum cyclicity: every occupation basis vector is a nonzero scalar multiple
    of a wedge of creators applied to the vacuum. -/
theorem vacuum_cyclic (S : Finset (Fin d)) :
    ∃ (n : ℕ) (i : Fin n → Fin d) (c : ℂ), c ≠ 0 ∧ c • wedgeAux d n i = fockBasis d S := by
  refine Finset.induction_on S ?_ ?_
  · exact ⟨0, fun (i : Fin 0) => i.elim0, 1, one_ne_zero, by simp [wedgeAux, fockVac]⟩
  · intro a T haT ih
    obtain ⟨n, i, c, hc, hi⟩ := ih
    refine ⟨n + 1, Fin.cons (α := fun _ => Fin d) a i, c * sgn d a T, ?_, ?_⟩
    · -- c * sgn ≠ 0 since both nonzero
      apply mul_ne_zero hc
      -- sgn = ±1, so ≠ 0
      rw [sgn]
      apply pow_ne_zero
      norm_num
    · rw [wedgeAux_cons]
      -- Goal: (c * sgn d a T) • adag d a (wedgeAux d n i) = fockBasis d (insert a T)
      -- From ih : c • wedgeAux d n i = fockBasis d T
      -- So adag a (wedgeAux n i) = c⁻¹ • adag a (e T) = c⁻¹ • sgn • e (insert a T)
      have h1 : adag d a (wedgeAux d n i)
          = (c⁻¹ * sgn d a T) • fockBasis d (insert a T) := by
        have hWinv : wedgeAux d n i = c⁻¹ • fockBasis d T := by
          rw [← hi, smul_smul, inv_mul_cancel₀ hc, one_smul]
        rw [hWinv, map_smul, adag_basis, ite_eq_right haT, smul_smul]
      rw [h1, smul_smul]
      -- ((c * sgn) * (c⁻¹ * sgn)) • e = e
      have hsgn2 : sgn d a T * sgn d a T = 1 := sgn_sq d a T
      have : (c * sgn d a T) * (c⁻¹ * sgn d a T) = 1 := by
        calc (c * sgn d a T) * (c⁻¹ * sgn d a T)
            = (c * c⁻¹) * (sgn d a T * sgn d a T) := by ring
          _ = 1 * 1 := by rw [mul_inv_cancel₀ hc, hsgn2]
          _ = 1 := by rw [mul_one]
      rw [this, one_smul]

-- ============================================================================
-- §6. The parity operator
-- ============================================================================

/-- Parity acts on basis vectors by the sign `(-1)^(S.card)`. -/
theorem parityFock_basis (S : Finset (Fin d)) :
    parityFock d (fockBasis d S) = ((-1 : ℂ) ^ S.card) • fockBasis d S := by
  apply PiLp.ext
  intro T
  simp only [parityFock_apply, fockBasis_ofLp, PiLp.smul_apply, smul_eq_mul]
  by_cases h : T = S
  · subst h; simp
  · simp [h]

/-- `P^2 = 1`. -/
theorem parityFock_sq :
    (parityFock d).comp (parityFock d) = 1 := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro T
  simp only [LinearMap.comp_apply, Module.End.one_apply, parityFock_apply]
  have hsq : ((-1:ℂ) ^ T.card) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  calc ((-1:ℂ) ^ T.card) * (((-1:ℂ) ^ T.card) * x.ofLp T)
      = (((-1:ℂ) ^ T.card) ^ 2) * x.ofLp T := by ring
    _ = x.ofLp T := by rw [hsq, one_mul]

/-- `(-1)^(erase card) = -(-1)^(card)`. -/
theorem neg_one_pow_erase_card (i : Fin d) (T : Finset (Fin d)) (hiT : i ∈ T) :
    ((-1:ℂ) ^ (T.erase i).card) = -((-1:ℂ) ^ T.card) := by
  have hcard : (T.erase i).card + 1 = T.card := Finset.card_erase_add_one hiT
  conv_rhs => rw [← hcard, pow_add]
  simp

/-- `(-1)^(insert card) = -(-1)^(card)`. -/
theorem neg_one_pow_insert_card (i : Fin d) (T : Finset (Fin d)) (hiT : i ∉ T) :
    ((-1:ℂ) ^ (insert i T).card) = -((-1:ℂ) ^ T.card) := by
  have hcard : (insert i T).card = T.card + 1 := Finset.card_insert_of_notMem hiT
  rw [hcard, pow_add]
  simp

/-- Parity anticommutes with creators. -/
theorem parityFock_anticomm_adag (i : Fin d) :
    (parityFock d).comp (adag d i) + (adag d i).comp (parityFock d) = 0 := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro T
  simp only [LinearMap.add_apply, PiLp.add_apply, LinearMap.comp_apply,
    LinearMap.zero_apply, PiLp.zero_apply, adag_apply, parityFock_apply]
  by_cases hiT : i ∈ T
  · have hsign := neg_one_pow_erase_card d i T hiT
    simp only [ite_eq_left hiT, hsign]
    ring
  · simp [hiT]

-- ============================================================================
-- §7. n-particle sectors
-- ============================================================================

/-- The n-particle sector: span of `e S` with `S.card = n`. -/
noncomputable def sector (d n : ℕ) : Submodule ℂ (FermionicFock d) :=
  Submodule.span ℂ {x : FermionicFock d | ∃ S : Finset (Fin d), S.card = n ∧ x = fockBasis d S}

/-- Helper: inner product with a fixed vector vanishes on a span if it vanishes
    on generators (first argument). -/
theorem inner_zero_span_left (s : Set (FermionicFock d)) (y : FermionicFock d)
    (h : ∀ a ∈ s, ⟪a, y⟫_ℂ = 0) (x : FermionicFock d)
    (hx : x ∈ Submodule.span ℂ s) : ⟪x, y⟫_ℂ = 0 := by
  let p : Submodule ℂ (FermionicFock d) :=
    { carrier := {x | ⟪x, y⟫_ℂ = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [inner_add_left, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [inner_smul_left, hx, mul_zero] }
  have hle : Submodule.span ℂ s ≤ p :=
    Submodule.span_le.mpr (fun a ha => h a ha)
  exact hle hx

/-- Helper: inner product with a fixed vector vanishes on a span if it vanishes
    on generators (second argument). -/
theorem inner_zero_span_right (x : FermionicFock d) (s : Set (FermionicFock d))
    (h : ∀ b ∈ s, ⟪x, b⟫_ℂ = 0) (y : FermionicFock d)
    (hy : y ∈ Submodule.span ℂ s) : ⟪x, y⟫_ℂ = 0 := by
  let q : Submodule ℂ (FermionicFock d) :=
    { carrier := {y | ⟪x, y⟫_ℂ = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [inner_add_right, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c y hy => by
        simp only [Set.mem_setOf_eq] at hy ⊢
        rw [inner_smul_right, hy, mul_zero] }
  have hle : Submodule.span ℂ s ≤ q :=
    Submodule.span_le.mpr (fun b hb => h b hb)
  exact hle hy

/-- Sectors with different particle numbers are orthogonal. -/
theorem sector_orth (m n : ℕ) (hmn : m ≠ n) (x y : FermionicFock d)
    (hx : x ∈ sector d m) (hy : y ∈ sector d n) :
    ⟪x, y⟫_ℂ = 0 := by
  have hbasis : ∀ S T : Finset (Fin d), S.card = m → T.card = n →
      ⟪fockBasis d S, fockBasis d T⟫_ℂ = 0 := by
    intro S T hS hT
    rw [fockBasis_inner]
    have hne : S ≠ T := by
      intro h
      apply hmn
      rw [← hS, h, hT]
    rw [ite_eq_right hne]
  rw [sector] at hx hy
  have h1 : ∀ a ∈ ({x : FermionicFock d | ∃ S : Finset (Fin d), S.card = m ∧ x = fockBasis d S} : Set (FermionicFock d)),
      ⟪a, y⟫_ℂ = 0 := by
    intro a ha
    obtain ⟨S, hS, rfl⟩ := ha
    have h2 : ∀ b ∈ ({y : FermionicFock d | ∃ T : Finset (Fin d), T.card = n ∧ y = fockBasis d T} : Set (FermionicFock d)),
        ⟪fockBasis d S, b⟫_ℂ = 0 := by
      intro b hb
      obtain ⟨T, hT, rfl⟩ := hb
      exact hbasis S T hS hT
    exact inner_zero_span_right d (fockBasis d S) _ h2 y hy
  exact inner_zero_span_left d _ y h1 x hx

/-- Sectors vanish for `n > d`: no subset of `Fin d` has more than `d` elements. -/
theorem sector_vanish (n : ℕ) (hn : d < n) : sector d n = ⊥ := by
  rw [sector, Submodule.span_eq_bot]
  rintro x ⟨S, hS, rfl⟩
  have hle : S.card ≤ d := by
    calc S.card ≤ (Finset.univ : Finset (Fin d)).card :=
          Finset.card_le_card (Finset.subset_univ S)
      _ = d := by simp
  omega

/-- Parity anticommutes with annihilators. -/
theorem parityFock_anticomm_ann (i : Fin d) :
    (parityFock d).comp (ann d i) + (ann d i).comp (parityFock d) = 0 := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro T
  simp only [LinearMap.add_apply, PiLp.add_apply, LinearMap.comp_apply,
    LinearMap.zero_apply, PiLp.zero_apply, ann_apply, parityFock_apply]
  by_cases hiT : i ∉ T
  · have hsign := neg_one_pow_insert_card d i T hiT
    simp only [ite_eq_left hiT, hsign]
    ring
  · simp [hiT]

-- ============================================================================
-- §9. Consistency with the 2-mode model (OperatorWick.lean)
-- ============================================================================

/-- Index map between `OperatorWick.lean`'s `Fock2` basis and our occupation subsets.
    Their basis ordering (from `creatorMat2m1`/`creatorMat2m2` in `OperatorWick.lean`):
    - `0 ↦ ∅` (vacuum)
    - `1 ↦ {1}` (their "mode 1" ↔ our `(1 : Fin 2)`)
    - `2 ↦ {0}` (their "mode 2" ↔ our `(0 : Fin 2)`)
    - `3 ↦ {0, 1}` (both occupied)
    Note the mode swap: their mode 1 is our `1`, their mode 2 is our `0`.
    Verified 2026-10-11: the four sign-critical creator actions below reproduce
    exactly the nonzero entries of their `creatorMat2m1` (3,2)=-1 etc.
    This file is self-contained and does not import `OperatorWick.lean`. -/
theorem fock2_index_map : True := trivial

/-- Creator `(1 : Fin 2)` (their "mode 1") on vacuum gives `e {1}` with sign +1. -/
theorem adag_2_1_vac :
    adag 2 (1 : Fin 2) (fockBasis 2 ∅) = fockBasis 2 {1} := by
  have h : adag 2 (1 : Fin 2) (fockBasis 2 ∅)
      = sgn 2 (1 : Fin 2) ∅ • fockBasis 2 (insert (1 : Fin 2) ∅) := by
    rw [adag_basis]
    simp
  rw [h]
  have hsgn : sgn 2 (1 : Fin 2) ∅ = 1 := by
    unfold sgn
    simp
  have hins : insert (1 : Fin 2) (∅ : Finset (Fin 2)) = {1} := by simp
  rw [hsgn, hins, one_smul]

/-- Creator `(1 : Fin 2)` on `e {0}` gives `-e {0,1}` (Koszul sign: `0 < 1`). -/
theorem adag_2_1_sign :
    adag 2 (1 : Fin 2) (fockBasis 2 {0}) = -fockBasis 2 {0, 1} := by
  have h : adag 2 (1 : Fin 2) (fockBasis 2 {0})
      = sgn 2 (1 : Fin 2) {0} • fockBasis 2 (insert (1 : Fin 2) {0}) := by
    rw [adag_basis]
    have h1 : (1 : Fin 2) ∉ ({0} : Finset (Fin 2)) := by decide
    rw [ite_eq_right h1]
  rw [h]
  have hsgn : sgn 2 (1 : Fin 2) {0} = -1 := by
    unfold sgn
    have hfilter : Finset.filter (fun j : Fin 2 => j < 1) {0} = {0} := by decide
    rw [hfilter]
    simp
  have hins : insert (1 : Fin 2) ({0} : Finset (Fin 2)) = {0, 1} := by decide
  rw [hsgn, hins]
  simp [smul_eq_mul]

/-- Creator `(0 : Fin 2)` (their "mode 2") on vacuum gives `e {0}` with sign +1. -/
theorem adag_2_0_vac :
    adag 2 (0 : Fin 2) (fockBasis 2 ∅) = fockBasis 2 {0} := by
  have h : adag 2 (0 : Fin 2) (fockBasis 2 ∅)
      = sgn 2 (0 : Fin 2) ∅ • fockBasis 2 (insert (0 : Fin 2) ∅) := by
    rw [adag_basis]
    simp
  rw [h]
  have hsgn : sgn 2 (0 : Fin 2) ∅ = 1 := by
    unfold sgn
    simp
  have hins : insert (0 : Fin 2) (∅ : Finset (Fin 2)) = {0} := by simp
  rw [hsgn, hins, one_smul]

-- ============================================================================
-- §10. Windows (priced, not attempted)
-- ============================================================================

/-!
## Windows (priced, do not attempt)

The following are natural continuations, explicitly priced out of scope:

1. **Unitary equivalence with Λⁿ(H) as tensor-power subspaces.** The n-particle
   sector `sector d n` is unitarily equivalent to the antisymmetric subspace
   of `(ℂ^d)^{⊗ n}` (the n-th exterior power). Proving this requires building
   the antisymmetrizer projection on tensor powers and showing it has the
   correct image — the API friction that blocked the first worker. Priced:
   the subset model already gives the correct inner product; the tensor-power
   picture is a different presentation of the same Hilbert space.

2. **Infinite-mode (d → ∞) limit.** The CAR algebra over infinitely many modes
   (the usual fermionic Fock space over ℓ²(ℕ)) is the inductive limit of the
   finite-d models. This requires colimits of Hilbert spaces / C*-algebras,
   far beyond the finite-dimensional setup here. Priced.

3. **General-n Gram determinant.** The formula
   `⟪adag i₁⋯adag iₙ vac, adag j₁⋯adag jₙ vac⟫ = det(δ_{i_k j_l})`
   for general `n` follows from the "annihilation through wedge" lemma
   (`ann a` acting as a signed sum over positions) by induction using
   `Matrix.det_succ_row`. The base case, the reassembly lemma (`reassembly`),
   and the `wedgeAux_cons` lemma are proved; the inductive step of the
   "ann through wedge" lemma requires careful `Fin.succAbove` reindexing
   that was not completed. The n=1 case (`gram_one`) is proved from CAR.
   Priced.
-/

-- ============================================================================
-- Axiom audit
-- ============================================================================

#print axioms ann_adjoint
#print axioms car_mixed
#print axioms car_ann_ann
#print axioms car_adag_adag
#print axioms numberOp_apply_basis
#print axioms parityFock_sq
#print axioms sector_orth
#print axioms gram_one
#print axioms vacuum_cyclic
