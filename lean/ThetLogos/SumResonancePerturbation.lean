import Mathlib.Tactic
import ThetLogos.SumResonanceCore

/-!
# Sum resonance: single-tone perturbation finiteness (RES-2b, (a4))

Optional sub-brick of the resonance line, per the coordinator pack
`routeb-general-scratch/pack-res-2b.md` and the ratified scoping memo
`routeb-general-scratch/scoping-resonance-2026-10-30.md` (§2 (a4),
deferred expressly by RES-2's landing). RES-0/RES-1 vocabulary
(`ThetLogos.SumResonance`, `ThetLogos.SumResonanceCore`: `sumFam`,
`collCount`) is cited, never forked.

**Frozen form (the scoping's (a4), two equivalent-strength faces).**
Fix `a`, `b`, and an index `j₀`; `pertTone b j₀ t` is `b` with the
single tone `b j₀` replaced by `b j₀ + t`. Both of the scoping's
phrasings are frozen and proved finite:
- the increase form: `pertExcSet a b j₀ = {t : ℚ | collCount a b <
  collCount a (pertTone b j₀ t)}` is finite (`pertExcSet_finite`);
- the new-collision form: `newCollSet a b j₀ = {t | a collision
  through j₀ exists for the perturbed family that is not already a
  collision of `b}` is finite (`newCollSet_finite`).
The two are tied by `new_collision_form`: ANY collision of the
perturbed family that is not already a collision of `b` automatically
involves `j₀` on exactly one side, so "through a collision involving
`j₀`" is not an extra restriction — it is forced. Both exceptional
sets are trapped inside the one explicit finite candidate set
`pertCandFinset a b j₀`.

**DEGENERATE-CASE AUDIT (named finding, on the face).** A candidate
collision is one linear equation in `t`. The cross collisions
(exactly one side equal to `j₀`) give
`t = a i' + b j' - a i - b j₀` (`pertCand`): the coefficient of `t`
is exactly `1`, so each cross candidate has exactly one solution
(`cross_solution_singleton`) — the pre-registered expectation of a
non-degenerate `t = (a i - b j)`-shaped equation is VERIFIED, not
assumed. The only `t`-independent candidate equations are the
both-`j₀` collisions, where `t` cancels (`0 * t = a i - a i'`):
those hold for all `t` or for none, but by
`both_j0_t_independent` they hold for the perturbed family iff they
hold for `b` itself — they are never new and never raise the count.
Hence the finiteness claim needs NO extra non-degeneracy hypothesis;
the degenerate case is real but inert, and it is discharged here
rather than hidden.

**K-RES-1 (pre-registered framing kill), noted on the face:** this
is a theorem ABOUT the counting (the stability of `collCount` under
a one-tone perturbation), not a seat report; no raw count at any
seat is the content. **K-RES-2:** no measured-mass harmonics appear
anywhere in this brick — tones are abstract rationals; any slide
toward measured values would void it. NO CLAIM beyond the abstract
finite-ℚ statements proved below. Dial 1 untouched; dials 0/4.
-/

namespace ThetLogos

open Finset

variable {m n : ℕ}

/-- The single-tone perturbation of `b` at `j₀` by `t`: the tone
`b j₀` is replaced by `b j₀ + t`, all other tones unchanged.
Memo §2 (a4)'s `b'`. -/
def pertTone (b : Fin n → ℚ) (j₀ : Fin n) (t : ℚ) : Fin n → ℚ :=
  fun j => if j = j₀ then b j₀ + t else b j

/-- The candidate exceptional value of a cross collision: for
indices `i i' : Fin m` and `j' : Fin n`, the unique `t` at which
the perturbed tone `(i, j₀)` can collide with `(i', j')`. This is
the value `t = a i' + b j' - a i - b j₀` — one linear equation in
`t` with coefficient exactly `1` (see the header audit). -/
def pertCand (a : Fin m → ℚ) (b : Fin n → ℚ) (j₀ : Fin n)
    (i i' : Fin m) (j' : Fin n) : ℚ :=
  a i' + b j' - a i - b j₀

/-- The finite candidate set: all `pertCand` values over all index
triples. Both exceptional sets of (a4) are subsets of it. -/
def pertCandFinset (a : Fin m → ℚ) (b : Fin n → ℚ) (j₀ : Fin n) :
    Finset ℚ :=
  (Finset.univ ×ˢ Finset.univ ×ˢ Finset.univ).image
    (fun q : Fin m × Fin m × Fin n => pertCand a b j₀ q.1 q.2.1 q.2.2)

/-- The exceptional set of (a4), increase form: the perturbation
sizes `t` at which the collision count strictly rises. -/
def pertExcSet (a : Fin m → ℚ) (b : Fin n → ℚ) (j₀ : Fin n) : Set ℚ :=
  {t : ℚ | collCount a b < collCount a (pertTone b j₀ t)}

/-- The exceptional set of (a4), new-collision form: the
perturbation sizes `t` at which some collision through `j₀` of the
perturbed family is not already a collision of `b`. -/
def newCollSet (a : Fin m → ℚ) (b : Fin n → ℚ) (j₀ : Fin n) : Set ℚ :=
  {t : ℚ | ∃ p p' : Fin m × Fin n,
    sumFam a (pertTone b j₀ t) p = sumFam a (pertTone b j₀ t) p' ∧
    ¬ sumFam a b p = sumFam a b p' ∧ (p.2 = j₀ ∨ p'.2 = j₀)}

/-- The perturbed tone at the perturbed index. -/
theorem pertTone_self (b : Fin n → ℚ) (j₀ : Fin n) (t : ℚ) :
    pertTone b j₀ t j₀ = b j₀ + t := by
  simp [pertTone]

/-- The perturbed tone away from the perturbed index. -/
theorem pertTone_of_ne (b : Fin n → ℚ) (j₀ : Fin n) (t : ℚ)
    {j : Fin n} (hj : j ≠ j₀) : pertTone b j₀ t j = b j := by
  simp [pertTone, hj]

/-- Perturbing by `0` is the identity: `pertTone b j₀ 0 = b`. -/
theorem pertTone_zero (b : Fin n → ℚ) (j₀ : Fin n) :
    pertTone b j₀ 0 = b := by
  funext j
  by_cases hj : j = j₀
  · subst hj
    simp [pertTone]
  · simp [pertTone, hj]

-- ============================================================================
-- The candidate equations: cross (non-degenerate), both-`j₀` (inert), neither
-- ============================================================================

/-- **Cross collision equation.** For `j' ≠ j₀`, the perturbed tone
`(i, j₀)` collides with `(i', j')` iff `t` is exactly the candidate
value — one linear equation in `t`, coefficient `1`, a unique
solution. The degenerate `0 = 0` case does not occur here. -/
theorem cross_collision_iff (a : Fin m → ℚ) (b : Fin n → ℚ)
    (j₀ : Fin n) (t : ℚ) (i i' : Fin m) {j' : Fin n} (hj' : j' ≠ j₀) :
    sumFam a (pertTone b j₀ t) (i, j₀) = sumFam a (pertTone b j₀ t) (i', j')
      ↔ t = pertCand a b j₀ i i' j' := by
  have h : a i + pertTone b j₀ t j₀ = a i' + pertTone b j₀ t j'
      ↔ t = a i' + b j' - a i - b j₀ := by
    rw [pertTone_self, pertTone_of_ne b j₀ t hj']
    constructor <;> intro hEq <;> linarith [hEq]
  exact h

/-- The cross collision equation, other orientation: `(i', j')`
against `(i, j₀)` gives the same candidate value. -/
theorem cross_collision_iff_swap (a : Fin m → ℚ) (b : Fin n → ℚ)
    (j₀ : Fin n) (t : ℚ) (i i' : Fin m) {j' : Fin n} (hj' : j' ≠ j₀) :
    sumFam a (pertTone b j₀ t) (i', j') = sumFam a (pertTone b j₀ t) (i, j₀)
      ↔ t = pertCand a b j₀ i i' j' := by
  rw [eq_comm]
  exact cross_collision_iff a b j₀ t i i' hj'

/-- The solution set of one cross candidate equation is the
singleton of its candidate value: each candidate collision happens
at exactly one perturbation size. -/
theorem cross_solution_singleton (a : Fin m → ℚ) (b : Fin n → ℚ)
    (j₀ : Fin n) (i i' : Fin m) {j' : Fin n} (hj' : j' ≠ j₀) :
    {t : ℚ | sumFam a (pertTone b j₀ t) (i, j₀)
        = sumFam a (pertTone b j₀ t) (i', j')} = {pertCand a b j₀ i i' j'} := by
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact cross_collision_iff a b j₀ t i i' hj'

/-- **The degenerate case, audited.** A both-`j₀` collision is
`t`-independent: `(i, j₀)` collides with `(i', j₀)` in the perturbed
family iff `a i = a i'` — for all `t` or for none. Crucially it is
the same condition as in `b` itself, so these collisions are never
new and never raise the count; the `0 = 0` shape is inert. -/
theorem both_j0_t_independent (a : Fin m → ℚ) (b : Fin n → ℚ)
    (j₀ : Fin n) (t : ℚ) (i i' : Fin m) :
    sumFam a (pertTone b j₀ t) (i, j₀) = sumFam a (pertTone b j₀ t) (i', j₀)
      ↔ a i = a i' := by
  have h : a i + pertTone b j₀ t j₀ = a i' + pertTone b j₀ t j₀
      ↔ a i = a i' := by
    rw [pertTone_self]
    constructor <;> intro hEq <;> linarith [hEq]
  exact h

/-- A collision involving `j₀` on neither side is unchanged by the
perturbation: it holds for the perturbed family iff it holds
for `b`. -/
theorem neither_j0_iff (a : Fin m → ℚ) (b : Fin n → ℚ) (j₀ : Fin n)
    (t : ℚ) (i i' : Fin m) {j j' : Fin n} (hj : j ≠ j₀) (hj' : j' ≠ j₀) :
    sumFam a (pertTone b j₀ t) (i, j) = sumFam a (pertTone b j₀ t) (i', j')
      ↔ sumFam a b (i, j) = sumFam a b (i', j') := by
  have h : a i + pertTone b j₀ t j = a i' + pertTone b j₀ t j'
      ↔ a i + b j = a i' + b j' := by
    rw [pertTone_of_ne b j₀ t hj, pertTone_of_ne b j₀ t hj']
  exact h

/-- **Form of a new collision.** If a pair collides for the
perturbed family but not for `b`, then `j₀` occurs on exactly one
side of the pair and `t` is the corresponding candidate value.
In particular every new collision is automatically "through `j₀`",
and its size lies in the finite candidate range. -/
theorem new_collision_form (a : Fin m → ℚ) (b : Fin n → ℚ) (j₀ : Fin n)
    (t : ℚ) (p p' : Fin m × Fin n)
    (hT : sumFam a (pertTone b j₀ t) p = sumFam a (pertTone b j₀ t) p')
    (hB : ¬ sumFam a b p = sumFam a b p') :
    (p.2 = j₀ ∧ p'.2 ≠ j₀ ∧ t = pertCand a b j₀ p.1 p'.1 p'.2) ∨
      (p'.2 = j₀ ∧ p.2 ≠ j₀ ∧ t = pertCand a b j₀ p'.1 p.1 p.2) := by
  obtain ⟨i, j⟩ := p
  obtain ⟨i', j'⟩ := p'
  have hT' : a i + pertTone b j₀ t j = a i' + pertTone b j₀ t j' := hT
  have hB' : ¬ (a i + b j = a i' + b j') := hB
  by_cases hj : j = j₀
  · by_cases hj' : j' = j₀
    · -- Both sides at `j₀`: `t` cancels; the collision is old.
      have e1 : pertTone b j₀ t j = b j₀ + t := by
        rw [hj]; exact pertTone_self b j₀ t
      have e2 : pertTone b j₀ t j' = b j₀ + t := by
        rw [hj']; exact pertTone_self b j₀ t
      rw [e1, e2] at hT'
      rw [hj, hj'] at hB'
      exact absurd (by linarith [hT']) hB'
    · have e1 : pertTone b j₀ t j = b j₀ + t := by
        rw [hj]; exact pertTone_self b j₀ t
      rw [e1, pertTone_of_ne b j₀ t hj'] at hT'
      exact Or.inl ⟨hj, hj',
        by show t = a i' + b j' - a i - b j₀; linarith [hT']⟩
  · by_cases hj' : j' = j₀
    · have e2 : pertTone b j₀ t j' = b j₀ + t := by
        rw [hj']; exact pertTone_self b j₀ t
      rw [pertTone_of_ne b j₀ t hj, e2] at hT'
      exact Or.inr ⟨hj', hj,
        by show t = a i + b j - a i' - b j₀; linarith [hT']⟩
    · -- Neither side at `j₀`: the collision is unchanged, hence old.
      rw [pertTone_of_ne b j₀ t hj, pertTone_of_ne b j₀ t hj'] at hT'
      exact absurd hT' hB'

-- ============================================================================
-- Finiteness of the exceptional sets
-- ============================================================================

/-- If the collision count strictly rises under the perturbation,
some collision of the perturbed family is not a collision of `b`
(a subset cannot have larger card). -/
theorem exists_new_collision_of_collCount_lt (a : Fin m → ℚ)
    (b : Fin n → ℚ) (j₀ : Fin n) (t : ℚ)
    (h : collCount a b < collCount a (pertTone b j₀ t)) :
    ∃ p p' : Fin m × Fin n,
      sumFam a (pertTone b j₀ t) p = sumFam a (pertTone b j₀ t) p' ∧
      ¬ sumFam a b p = sumFam a b p' := by
  have hnot : ¬ (Finset.univ.filter
        (fun p : (Fin m × Fin n) × (Fin m × Fin n) =>
          sumFam a (pertTone b j₀ t) p.1 = sumFam a (pertTone b j₀ t) p.2)) ⊆
      (Finset.univ.filter
        (fun p : (Fin m × Fin n) × (Fin m × Fin n) =>
          sumFam a b p.1 = sumFam a b p.2)) := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    have h' : (Finset.univ.filter
          (fun p : (Fin m × Fin n) × (Fin m × Fin n) =>
            sumFam a b p.1 = sumFam a b p.2)).card
        < (Finset.univ.filter
          (fun p : (Fin m × Fin n) × (Fin m × Fin n) =>
            sumFam a (pertTone b j₀ t) p.1
              = sumFam a (pertTone b j₀ t) p.2)).card := h
    omega
  obtain ⟨p, hpT, hpB⟩ := Finset.not_subset.mp hnot
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpT hpB
  exact ⟨p.1, p.2, hpT, hpB⟩

/-- Every new-collision size is a candidate value: the new-collision
exceptional set is contained in the finite candidate finset. -/
theorem newCollSet_subset_candFinset (a : Fin m → ℚ) (b : Fin n → ℚ)
    (j₀ : Fin n) :
    newCollSet a b j₀ ⊆ ↑(pertCandFinset a b j₀) := by
  intro t ht
  obtain ⟨p, p', hT, hB, _⟩ := ht
  rw [Finset.mem_coe]
  rcases new_collision_form a b j₀ t p p' hT hB with
    ⟨-, -, htc⟩ | ⟨-, -, htc⟩
  · simp only [pertCandFinset, Finset.mem_image, Finset.mem_product,
      Finset.mem_univ, true_and]
    exact ⟨(p.1, p'.1, p'.2), htc.symm⟩
  · simp only [pertCandFinset, Finset.mem_image, Finset.mem_product,
      Finset.mem_univ, true_and]
    exact ⟨(p'.1, p.1, p.2), htc.symm⟩

/-- The increase exceptional set is contained in the new-collision
set: a strict rise in the count is always witnessed by a new
collision through `j₀`. -/
theorem pertExcSet_subset_newCollSet (a : Fin m → ℚ) (b : Fin n → ℚ)
    (j₀ : Fin n) :
    pertExcSet a b j₀ ⊆ newCollSet a b j₀ := by
  intro t ht
  have hlt : collCount a b < collCount a (pertTone b j₀ t) := ht
  obtain ⟨p, p', hT, hB⟩ :=
    exists_new_collision_of_collCount_lt a b j₀ t hlt
  refine ⟨p, p', hT, hB, ?_⟩
  rcases new_collision_form a b j₀ t p p' hT hB with
    ⟨hp, -, -⟩ | ⟨hp', -, -⟩
  · exact Or.inl hp
  · exact Or.inr hp'

/-- **(a4) Single-tone perturbation finiteness, new-collision form**
(memo §2 (a4)): the set of `t : ℚ` for which a collision through
`j₀` appears that is not already a collision of `b` is finite —
coincidences are accidents of finite codimension. -/
theorem newCollSet_finite (a : Fin m → ℚ) (b : Fin n → ℚ) (j₀ : Fin n) :
    (newCollSet a b j₀).Finite :=
  (pertCandFinset a b j₀).finite_toSet.subset
    (newCollSet_subset_candFinset a b j₀)

/-- **(a4) Single-tone perturbation finiteness, increase form**
(memo §2 (a4), the scoping's exact phrasing): the set of `t : ℚ`
for which `collCount a (pertTone b j₀ t) > collCount a b` through a
collision involving `j₀` is finite. By `new_collision_form` every
witnessing new collision involves `j₀` automatically. -/
theorem pertExcSet_finite (a : Fin m → ℚ) (b : Fin n → ℚ) (j₀ : Fin n) :
    (pertExcSet a b j₀).Finite :=
  (newCollSet_finite a b j₀).subset (pertExcSet_subset_newCollSet a b j₀)

/-- The unperturbed size is never exceptional: at `t = 0` the
count does not rise. -/
theorem zero_not_mem_pertExcSet (a : Fin m → ℚ) (b : Fin n → ℚ)
    (j₀ : Fin n) : (0 : ℚ) ∉ pertExcSet a b j₀ := by
  intro h
  have hlt : collCount a b < collCount a (pertTone b j₀ 0) := h
  rw [pertTone_zero] at hlt
  exact (lt_irrefl _ hlt).elim

-- ============================================================================
-- Read-backs at RES-0's named examples
-- ============================================================================

/-- Read-back: perturbing `exB = {1, 2}` at index `0` by `1` gives
the family `{2, 2}`. -/
theorem rb_pertTone_one : pertTone exB 0 1 = ![2, 2] := by
  funext i
  fin_cases i <;> simp [pertTone, exB] <;> norm_num

/-- Read-back, (a4) at the examples: `t = 1` IS exceptional for
`exA = {0, 1}` against `exB = {1, 2}` perturbed at `0` — the sums
become `2, 2, 3, 3`, with `8` collision pairs against the original
`6` (RES-1's `rb_collCount`). -/
theorem rb_pertExcSet_mem_one : (1 : ℚ) ∈ pertExcSet exA exB 0 := by
  have hpert : collCount exA (pertTone exB 0 1) = 8 := by
    rw [rb_pertTone_one]
    simp only [collCount, Finset.card_filter, Fintype.sum_prod_type,
      Fin.sum_univ_two]
    norm_num [sumFam, exA, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
  have hbase : collCount exA exB = 6 := rb_collCount
  show collCount exA exB < collCount exA (pertTone exB 0 1)
  omega

end ThetLogos

#print axioms ThetLogos.pertExcSet_finite
#print axioms ThetLogos.newCollSet_finite
#print axioms ThetLogos.new_collision_form
#print axioms ThetLogos.cross_collision_iff
#print axioms ThetLogos.both_j0_t_independent
