import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import ThetLogos.ThermalZ4Ladder

namespace ThetLogos

/-!
# ThetLogos.FiniteEntropy — finite von Neumann entropy, weight form (T-ENT)

**Status: DEFINITION + finite theorems. NO CLAIM. Dials 0/4. No measured
number.** Governing pack: `routeb-general-scratch/pack-t-ent.md` (line:
Q7CR trifecta support). This is the tree's first entropy definition.

## What is defined, and the conventions on its face

For a finite index type `ι` and weights `w : ι → ℝ`, the (finite von
Neumann / Shannon) entropy in weight form is

`entropyW w := -∑ i, w i * Real.log (w i)`,

log base `e` (`Real.log`). The convention `0 * log 0 = 0` is not an extra
axiom: Mathlib's `Real.log 0 = 0`, so the summand at a zero weight is
`0 * 0 = 0` on the nose (registered as `mul_log_self_eq_zero_of_eq_zero`
below). A probability weight is registered as `IsProbWeight`:
`0 ≤ w i` for all `i`, and `∑ i, w i = 1`.

## Sibling discipline

The continuous differential entropy of the SE line
(`ThetLogos.DiffEntropy`) is a DIFFERENT object. This module does not
import it, does not cite it, and neither line gates the other.

## The concavity route, named

The upper bound `entropyW w ≤ log (card ι)` and BOTH saturation
directions are proved by the Gibbs route: the pointwise inequality
`Real.log t ≤ t - 1` for `t > 0` (Mathlib's
`Real.log_le_sub_one_of_pos`), applied at `t = (card * w i)⁻¹`, summed
against the weights; the (⇒) saturation direction uses its strict form
`Real.log_lt_sub_one_of_pos` (strict off `t = 1`). No Jensen lemma is
used. Item 2's saturation clause is therefore landed in FULL, both
directions — the PARTIAL fallback the pack authorized at that clause
was not needed.

## Fences

Finite definition-and-theorem brick only: no physical claim, no
Second-Law language. Basis-independence of the density form beyond the
eigenvalue list is NOT claimed (item 5 registers the list form only).
-/

/-- Finite von Neumann entropy in weight form:
    `entropyW w = -∑ i, w i * log (w i)`, log base `e`. Tier T1
    (definition). -/
noncomputable def entropyW {ι : Type*} [Fintype ι] (w : ι → ℝ) : ℝ :=
  -∑ i, w i * Real.log (w i)

/-- A probability weight on a finite type: every weight nonnegative,
    weights summing to one. Tier T1 (definition). -/
def IsProbWeight {ι : Type*} [Fintype ι] (w : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1

/-- The `0 * log 0 = 0` convention is Mathlib's own: at a zero weight
    the entropy summand vanishes because `Real.log 0 = 0`. Tier T1. -/
theorem mul_log_self_eq_zero_of_eq_zero {x : ℝ} (hx : x = 0) :
    x * Real.log x = 0 := by
  rw [hx, Real.log_zero, mul_zero]

/-- A probability weight forces the index type to be nonempty:
    `0 < Fintype.card ι`. Tier T1. -/
theorem IsProbWeight.card_pos {ι : Type*} [Fintype ι] {w : ι → ℝ}
    (hw : IsProbWeight w) : 0 < Fintype.card ι := by
  rw [Fintype.card_pos_iff]
  by_contra hne
  haveI : IsEmpty ι := not_nonempty_iff.mp hne
  have h2 := hw.2
  rw [Finset.univ_eq_empty, Finset.sum_empty] at h2
  exact zero_ne_one h2

/-- Every probability weight is at most one: `w i ≤ ∑ j, w j = 1`.
    Tier T1. -/
theorem IsProbWeight.le_one {ι : Type*} [Fintype ι] {w : ι → ℝ}
    (hw : IsProbWeight w) (i : ι) : w i ≤ 1 := by
  have h := Finset.single_le_sum (f := w) (fun j _ => hw.1 j)
    (Finset.mem_univ i)
  rw [hw.2] at h
  exact h

/-- Each entropy summand of a probability weight is nonnegative in the
    `-w log w` form: for `0 ≤ w ≤ 1`, `0 ≤ -(w * log w)`. Tier T1. -/
theorem neg_mul_log_nonneg_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 ≤ -(x * Real.log x) := by
  rcases eq_or_lt_of_le h0 with rfl | hpos
  · simp
  · have hlog : Real.log x ≤ 0 := Real.log_nonpos hpos.le h1
    have : x * Real.log x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpos.le hlog
    linarith

/-- **Lower bound:** entropy of a probability weight is nonnegative.
    Tier T1. -/
theorem entropyW_nonneg {ι : Type*} [Fintype ι] {w : ι → ℝ}
    (hw : IsProbWeight w) : 0 ≤ entropyW w := by
  unfold entropyW
  rw [neg_nonneg]
  apply Finset.sum_nonpos
  intro i _
  have h := neg_mul_log_nonneg_of_mem (hw.1 i) (hw.le_one i)
  linarith

/-- Deficit of the Gibbs bound at one weight, with `n = card ι`:
    `w * log (n * w) - w + 1 / n ≥ 0` for `0 ≤ w` and `0 < n`. This is
    `Real.log_le_sub_one_of_pos` at `(n * w)⁻¹`, multiplied by `w`;
    at `w = 0` the deficit is `1 / n`. Tier T1. -/
theorem deficit_nonneg {n x : ℝ} (hn : 0 < n) (hx : 0 ≤ x) :
    0 ≤ x * Real.log (n * x) - x + 1 / n := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · rw [← h0]
    simp only [mul_zero, Real.log_zero, sub_zero, zero_add]
    exact div_nonneg zero_le_one hn.le
  · have hnx : 0 < n * x := mul_pos hn hpos
    have h := Real.log_le_sub_one_of_pos (x := (n * x)⁻¹)
      (by positivity : (0:ℝ) < (n * x)⁻¹)
    rw [Real.log_inv] at h
    have hfrac : x * (n * x)⁻¹ = 1 / n := by
      field_simp
    have hmul : x * (1 - (n * x)⁻¹) = x - 1 / n := by
      rw [mul_sub, mul_one, hfrac]
    have hge : x - 1 / n ≤ x * Real.log (n * x) := by
      rw [← hmul]
      exact mul_le_mul_of_nonneg_left (by linarith) hpos.le
    linarith

/-- The log-card defect of a probability weight, as a sum:
    `∑ i, w i * log (card * w i) = log card - entropyW w`. Tier T1. -/
theorem IsProbWeight.sum_mul_log_card_mul {ι : Type*} [Fintype ι]
    {w : ι → ℝ} (hw : IsProbWeight w) :
    ∑ i, w i * Real.log ((Fintype.card ι : ℝ) * w i)
      = Real.log (Fintype.card ι : ℝ) - entropyW w := by
  have hn : (0:ℝ) < Fintype.card ι := by
    exact_mod_cast hw.card_pos
  have hterm : ∀ i, w i * Real.log ((Fintype.card ι : ℝ) * w i)
      = w i * Real.log (Fintype.card ι : ℝ) + w i * Real.log (w i) := by
    intro i
    rcases eq_or_lt_of_le (hw.1 i) with h0 | hpos
    · rw [← h0]; simp
    · rw [Real.log_mul hn.ne' hpos.ne', mul_add]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, ← Finset.sum_mul,
    hw.2, one_mul]
  unfold entropyW
  ring

/-- **Upper bound (Gibbs):** entropy of a probability weight is at most
    `log (card ι)`. Route: sum of the pointwise deficits
    (`deficit_nonneg`) equals `log card - entropyW w`. Tier T1. -/
theorem entropyW_le_log_card {ι : Type*} [Fintype ι] {w : ι → ℝ}
    (hw : IsProbWeight w) :
    entropyW w ≤ Real.log (Fintype.card ι : ℝ) := by
  have hn : (0:ℝ) < Fintype.card ι := by
    exact_mod_cast hw.card_pos
  have hconst : ∑ _i : ι, (1 / (Fintype.card ι : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one_div_cancel hn.ne']
  have hsum : ∑ i, (w i * Real.log ((Fintype.card ι : ℝ) * w i) - w i
        + 1 / (Fintype.card ι : ℝ))
      = Real.log (Fintype.card ι : ℝ) - entropyW w := by
    have hsplit : ∀ i, w i * Real.log ((Fintype.card ι : ℝ) * w i) - w i
          + 1 / (Fintype.card ι : ℝ)
        = (w i * Real.log ((Fintype.card ι : ℝ) * w i)
          + 1 / (Fintype.card ι : ℝ)) - w i := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_sub_distrib,
      Finset.sum_add_distrib, hw.sum_mul_log_card_mul, hw.2, hconst]
    ring
  have hnonneg := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => deficit_nonneg hn (hw.1 i) (x := w i))
  rw [hsum] at hnonneg
  linarith

/-- **Saturation, both directions (FULL):** for a probability weight,
    `entropyW w = log (card ι)` iff `w` is maximally mixed,
    `w i = 1 / card ι` for all `i`. The (⇒) direction uses the strict
    Gibbs inequality `Real.log_lt_sub_one_of_pos`: equality forces
    every deficit to vanish, which forces `card * w i = 1`. Tier T1. -/
theorem entropyW_eq_log_card_iff {ι : Type*} [Fintype ι] {w : ι → ℝ}
    (hw : IsProbWeight w) :
    entropyW w = Real.log (Fintype.card ι : ℝ)
      ↔ ∀ i, w i = 1 / (Fintype.card ι : ℝ) := by
  have hn : (0:ℝ) < Fintype.card ι := by
    exact_mod_cast hw.card_pos
  constructor
  · intro heq i
    have hconst : ∑ _i : ι, (1 / (Fintype.card ι : ℝ)) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one_div_cancel hn.ne']
    have hsum : ∑ i, (w i * Real.log ((Fintype.card ι : ℝ) * w i) - w i
          + 1 / (Fintype.card ι : ℝ)) = 0 := by
      have hsplit : ∀ i, w i * Real.log ((Fintype.card ι : ℝ) * w i) - w i
            + 1 / (Fintype.card ι : ℝ)
          = (w i * Real.log ((Fintype.card ι : ℝ) * w i)
            + 1 / (Fintype.card ι : ℝ)) - w i := fun i => by ring
      rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_sub_distrib,
        Finset.sum_add_distrib, hw.sum_mul_log_card_mul, hw.2, hconst, heq]
      ring
    have hdi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => deficit_nonneg hn (hw.1 j) (x := w j))).mp hsum i
      (Finset.mem_univ i)
    -- `w i ≠ 0`: at a zero weight the deficit is `1 / card ≠ 0`.
    have hpos : 0 < w i := by
      rcases eq_or_lt_of_le (hw.1 i) with h0 | hpos
      · exfalso
        rw [← h0] at hdi
        simp only [mul_zero, Real.log_zero, sub_zero, zero_add] at hdi
        exact (one_div_pos.mpr hn).ne' hdi
      · exact hpos
    -- Equality in the Gibbs step forces `(card * w i)⁻¹ = 1`.
    have hinv : ((Fintype.card ι : ℝ) * w i)⁻¹ = 1 := by
      by_contra hne
      have hnx : 0 < (Fintype.card ι : ℝ) * w i := mul_pos hn hpos
      have hlt := Real.log_lt_sub_one_of_pos
        (x := ((Fintype.card ι : ℝ) * w i)⁻¹) (by positivity) hne
      rw [Real.log_inv] at hlt
      have hfrac : w i * ((Fintype.card ι : ℝ) * w i)⁻¹
          = 1 / (Fintype.card ι : ℝ) := by
        field_simp
      have hgt : w i * (1 - ((Fintype.card ι : ℝ) * w i)⁻¹)
          < w i * Real.log ((Fintype.card ι : ℝ) * w i) :=
        mul_lt_mul_of_pos_left (by linarith) hpos
      rw [mul_sub, mul_one, hfrac] at hgt
      linarith
    have hmul : (Fintype.card ι : ℝ) * w i = 1 := by
      have := inv_eq_one.mp hinv
      exact this
    exact eq_one_div_of_mul_eq_one_left (by rw [mul_comm]; exact hmul)
  · intro hunif
    have hterm : ∀ i, w i * Real.log (w i)
        = (1 / (Fintype.card ι : ℝ))
          * Real.log (1 / (Fintype.card ι : ℝ)) := by
      intro i; rw [hunif i]
    unfold entropyW
    have h1 : (Fintype.card ι : ℝ) * ((1 / (Fintype.card ι : ℝ))
        * Real.log (1 / (Fintype.card ι : ℝ)))
        = Real.log (1 / (Fintype.card ι : ℝ)) := by
      calc (Fintype.card ι : ℝ) * ((1 / (Fintype.card ι : ℝ))
            * Real.log (1 / (Fintype.card ι : ℝ)))
          = ((Fintype.card ι : ℝ) * (1 / (Fintype.card ι : ℝ)))
            * Real.log (1 / (Fintype.card ι : ℝ)) := by ring
        _ = Real.log (1 / (Fintype.card ι : ℝ)) := by
            rw [mul_one_div_cancel hn.ne', one_mul]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, h1, one_div, Real.log_inv, neg_neg]

/-- A basis (pure) weight at `a`: mass `1` at `a`, `0` elsewhere.
    Tier T1 (definition). -/
def IsBasisWeight {ι : Type*} [DecidableEq ι] (w : ι → ℝ) (a : ι) : Prop :=
  ∀ i, w i = if i = a then 1 else 0

/-- A basis weight is a probability weight. Tier T1. -/
theorem IsBasisWeight.isProbWeight {ι : Type*} [Fintype ι] [DecidableEq ι] {w : ι → ℝ}
    {a : ι} (h : IsBasisWeight w a) : IsProbWeight w := by
  constructor
  · intro i
    rw [h i]
    split <;> norm_num
  · have : ∑ i, w i = ∑ i, (if i = a then (1:ℝ) else 0) :=
      Finset.sum_congr rfl (fun i _ => h i)
    rw [this, Finset.sum_ite_eq' Finset.univ a (fun _ => (1:ℝ))]
    simp

/-- **Pure weights, forward:** a basis weight has entropy zero.
    Tier T1. -/
theorem entropyW_eq_zero_of_isBasisWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w : ι → ℝ} {a : ι} (h : IsBasisWeight w a) : entropyW w = 0 := by
  unfold entropyW
  rw [neg_eq_zero]
  apply Finset.sum_eq_zero
  intro i _
  rw [h i]
  split_ifs with hi
  · simp
  · exact mul_log_self_eq_zero_of_eq_zero rfl

/-- **Pure weights, iff:** for a probability weight, `entropyW w = 0`
    iff `w` is a basis weight. (⇒): every summand `-w log w` is
    nonnegative and they sum to zero, so each `w i * log (w i) = 0`,
    forcing `w i ∈ {0, 1}`; the total mass `1` then sits at a single
    index. Tier T1. -/
theorem entropyW_eq_zero_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {w : ι → ℝ}
    (hw : IsProbWeight w) :
    entropyW w = 0 ↔ ∃ a, IsBasisWeight w a := by
  constructor
  · intro hS
    have hsum : ∑ i, w i * Real.log (w i) = 0 := by
      have := hS
      unfold entropyW at this
      simpa using this
    have hterm : ∀ i, w i * Real.log (w i) = 0 := by
      have hnonpos : ∀ i ∈ Finset.univ, w i * Real.log (w i) ≤ 0 := by
        intro i _
        have h := neg_mul_log_nonneg_of_mem (hw.1 i) (hw.le_one i)
        linarith
      exact fun i => (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp hsum i
        (Finset.mem_univ i)
    have hdich : ∀ i, w i = 0 ∨ w i = 1 := by
      intro i
      rcases mul_eq_zero.mp (hterm i) with h0 | hlog
      · exact Or.inl h0
      · rcases (Real.log_eq_zero.mp hlog) with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exfalso; linarith [hw.1 i]
    obtain ⟨a, ha⟩ : ∃ a, w a ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have h2 := hw.2
      rw [Finset.sum_eq_zero (fun i _ => hcon i)] at h2
      exact zero_ne_one h2
    have ha1 : w a = 1 := (hdich a).resolve_left ha
    refine ⟨a, fun i => ?_⟩
    by_cases hi : i = a
    · rw [hi, if_pos rfl]; exact ha1
    · rw [if_neg hi]
      have herase : ∑ j ∈ Finset.univ.erase a, w j = 0 := by
        have hadd := Finset.add_sum_erase Finset.univ w
          (Finset.mem_univ a)
        rw [hw.2, ha1] at hadd
        linarith
      have hnonneg : ∀ j ∈ Finset.univ.erase a, 0 ≤ w j :=
        fun j _ => hw.1 j
      exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp herase i
        (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
  · rintro ⟨a, ha⟩
    exact entropyW_eq_zero_of_isBasisWeight ha

/-- **Permutation invariance (relabeling):** for an equivalence
    `e : ι ≃ ι'`, `entropyW (w ∘ e) = entropyW w`. This is the finite
    owned form of modular-flow invariance in weight form: a
    weight-preserving evolution that only relabels (phases / basis
    permutation) does not change the entropy. Tier T1. -/
theorem entropyW_comp_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (w : ι → ℝ) (e : ι' ≃ ι) :
    entropyW (fun j => w (e j)) = entropyW w := by
  unfold entropyW
  congr 1
  exact Equiv.sum_comp e (fun i => w i * Real.log (w i))

/-- Permutation invariance, same-type form. Tier T1. -/
theorem entropyW_comp_perm {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (e : Equiv.Perm ι) : entropyW (fun j => w (e j)) = entropyW w :=
  entropyW_comp_equiv w e

/-- The Z4 ladder weights are probability weights, from the ladder's
    landed positivity and normalization. Tier T1. -/
theorem isProbWeight_z4Weight (β : ℝ) : IsProbWeight (z4Weight β) :=
  ⟨fun k => (z4Weight_pos β k).le, z4Weight_sum_eq_one β⟩

/-- **Gibbs instance of permutation invariance:** the entropy of the
    Z4 Gibbs weights is unchanged by any relabeling of the four rungs —
    in particular by the cyclic shift of the ladder. Tier T1. -/
theorem entropyW_z4Weight_comp_perm (β : ℝ) (e : Equiv.Perm (Fin 4)) :
    entropyW (fun j => z4Weight β (e j)) = entropyW (z4Weight β) :=
  entropyW_comp_perm _ e

/-- Entropy of a diagonal density, defined AS the entropy of its
    weights: `entropyD w := entropyW w`. (Item 5's density form; the
    operator-side content enters only through the eigenvalue list
    below.) Tier T1 (definition). -/
noncomputable def entropyD {n : ℕ} (w : Fin n → ℝ) : ℝ := entropyW w

/-- `entropyD` is `entropyW` of the weights, by definition. Tier T1. -/
theorem entropyD_eq_entropyW {n : ℕ} (w : Fin n → ℝ) :
    entropyD w = entropyW w := rfl

/-- Entropy of an eigenvalue list (the trace form's finite content):
    `entropyOfList l = -∑_{x ∈ l} x * log x`. For a self-adjoint
    density operator with a landed diagonalization, this is
    `S = -∑ λ log λ` over its eigenvalue list. Basis-independence
    beyond the list is NOT claimed. Tier T1 (definition). -/
noncomputable def entropyOfList (l : List ℝ) : ℝ :=
  -(l.map (fun x => x * Real.log x)).sum

/-- The list form equals `entropyW` of the list's weight function,
    Fin-indexed. Tier T1. -/
theorem entropyOfList_eq_entropyW (l : List ℝ) :
    entropyOfList l
      = entropyW (fun i : Fin l.length => l.get i) := by
  unfold entropyOfList entropyW
  rw [← List.sum_ofFn]
  congr 1
  conv_lhs => rw [← List.ofFn_get l, List.map_ofFn, Function.comp_def]

/-- At `β = 0` the Z4 partition sum is `4`. Tier T1. -/
theorem z4Partition_zero : z4Partition 0 = 4 := by
  unfold z4Partition
  simp

/-- At `β = 0` every Z4 Gibbs weight is `1 / 4`: the maximally mixed
    weight on four rungs. Tier T1. -/
theorem z4Weight_zero (k : Fin 4) : z4Weight 0 k = 1 / 4 := by
  unfold z4Weight
  rw [z4Partition_zero]
  simp

/-- **Gibbs instance of saturation:** the `β = 0` Z4 Gibbs entropy is
    exactly `log 4`, the upper bound of item 2, saturated by the
    maximally mixed weight. Tier T1. -/
theorem entropyW_z4Weight_zero : entropyW (z4Weight 0) = Real.log 4 := by
  have hunif : ∀ k, z4Weight 0 k
      = 1 / (Fintype.card (Fin 4) : ℝ) := by
    intro k
    rw [Fintype.card_fin, Nat.cast_ofNat]
    exact z4Weight_zero k
  have h := (entropyW_eq_log_card_iff (isProbWeight_z4Weight 0)).mpr hunif
  rwa [Fintype.card_fin, Nat.cast_ofNat] at h

/-- The Z4 Gibbs entropy in closed form:
    `entropyW (z4Weight β) = log (z4Partition β) + β * ∑ k, z4Weight β k * z4Energy k`,
    from `log (z4Weight β k) = -β * z4Energy k - log (z4Partition β)`.
    Tier T1. -/
theorem entropyW_z4Weight_eq (β : ℝ) :
    entropyW (z4Weight β) = Real.log (z4Partition β)
      + β * ∑ k, z4Weight β k * z4Energy k := by
  have hlog : ∀ k, Real.log (z4Weight β k)
      = -β * z4Energy k - Real.log (z4Partition β) := by
    intro k
    unfold z4Weight
    rw [Real.log_div (Real.exp_pos _).ne' (z4Partition_pos β).ne',
      Real.log_exp]
  have hterm : ∀ k, z4Weight β k * Real.log (z4Weight β k)
      = -(β * (z4Weight β k * z4Energy k))
        - z4Weight β k * Real.log (z4Partition β) := by
    intro k
    rw [hlog k]
    ring
  unfold entropyW
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    z4Weight_sum_eq_one, one_mul]
  ring

/-- The Z4 partition function is continuous in `β`. Tier T1. -/
theorem continuous_z4Partition : Continuous z4Partition := by
  unfold z4Partition
  apply continuous_finsetSum
  intro k _
  exact Real.continuous_exp.comp
    (continuous_id.neg.mul continuous_const)

/-- Each Z4 Gibbs weight is continuous in `β` (the partition sum never
    vanishes). Tier T1. -/
theorem continuous_z4Weight (k : Fin 4) :
    Continuous (fun β => z4Weight β k) := by
  unfold z4Weight
  apply Continuous.div
  · exact Real.continuous_exp.comp
      (continuous_id.neg.mul continuous_const)
  · exact continuous_z4Partition
  · intro β
    exact (z4Partition_pos β).ne'

/-- **Gibbs limit:** the Z4 Gibbs entropy tends to `log 4` as
    `β → 0`. Route: the closed form `entropyW_z4Weight_eq` — the
    `log (z4Partition β)` term tends to `log 4` by continuity of the
    partition sum and of `log` at `4`, and the `β * (mean energy)`
    term tends to `0`. Tier T1. -/
theorem tendsto_entropyW_z4Weight :
    Filter.Tendsto (fun β => entropyW (z4Weight β))
      (nhds 0) (nhds (Real.log 4)) := by
  have hZ : Filter.Tendsto z4Partition (nhds 0) (nhds 4) := by
    have h := continuous_z4Partition.tendsto 0
    rwa [z4Partition_zero] at h
  have hlog : Filter.Tendsto (fun β => Real.log (z4Partition β))
      (nhds 0) (nhds (Real.log 4)) :=
    (Real.continuousAt_log (show (4:ℝ) ≠ 0 by norm_num)).tendsto.comp hZ
  have hA : Filter.Tendsto
      (fun β => ∑ k, z4Weight β k * z4Energy k) (nhds 0)
      (nhds (∑ k, z4Weight 0 k * z4Energy k)) := by
    have hcont : Continuous
        (fun β => ∑ k, z4Weight β k * z4Energy k) := by
      apply continuous_finsetSum
      intro k _
      exact (continuous_z4Weight k).mul continuous_const
    exact hcont.tendsto 0
  have hmul : Filter.Tendsto
      (fun β => β * ∑ k, z4Weight β k * z4Energy k) (nhds 0) (nhds 0) := by
    have h := Filter.Tendsto.mul Filter.tendsto_id hA
    simpa using h
  have hsum := Filter.Tendsto.add hlog hmul
  rw [add_zero] at hsum
  have hfun : (fun β => entropyW (z4Weight β))
      = (fun β => Real.log (z4Partition β)
        + β * ∑ k, z4Weight β k * z4Energy k) :=
    funext fun β => entropyW_z4Weight_eq β
  rwa [hfun]

/-- **Gibbs strictness for `β > 0`:** the Z4 Gibbs entropy is strictly
    below `log 4`. From item 2's bound plus saturation (⇒): equality
    would force the maximally mixed weight, but the ladder's first
    step ratio `exp (-β / 4) < 1` makes rung `1` strictly lighter than
    rung `0`. Tier T1. -/
theorem entropyW_z4Weight_lt_log_four {β : ℝ} (hβ : 0 < β) :
    entropyW (z4Weight β) < Real.log 4 := by
  have hle : entropyW (z4Weight β) ≤ Real.log 4 := by
    have h := entropyW_le_log_card (isProbWeight_z4Weight β)
    rwa [Fintype.card_fin, Nat.cast_ofNat] at h
  have hne : entropyW (z4Weight β) ≠ Real.log 4 := by
    intro heq
    have heq' : entropyW (z4Weight β)
        = Real.log (Fintype.card (Fin 4) : ℝ) := by
      rwa [Fintype.card_fin, Nat.cast_ofNat]
    have hunif := (entropyW_eq_log_card_iff
      (isProbWeight_z4Weight β)).mp heq'
    have h0 := hunif 0
    have h1 := hunif 1
    have hr : z4Weight β 1 = z4Weight β 0 * Real.exp (-β / 4) :=
      z4Weight_step_ratio β 0
    have hexp : Real.exp (-β / 4) < 1 := by
      have h : Real.exp (-β / 4) < Real.exp 0 :=
        Real.exp_lt_exp.mpr (by linarith)
      simpa using h
    have hpos := z4Weight_pos β 0
    have hlt : z4Weight β 1 < z4Weight β 0 := by
      rw [hr]
      have := mul_lt_mul_of_pos_left hexp hpos
      simpa using this
    rw [h0] at hlt
    rw [h1] at hlt
    exact lt_irrefl _ hlt
  exact lt_of_le_of_ne hle hne

end ThetLogos
