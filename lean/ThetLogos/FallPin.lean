import Mathlib.Tactic
import ThetLogos.BoundarySeat

/-!
# ThetLogos.FallPin — FALL-1: the descent lemma over the grounded potential (T1)

HONESTY LEDGER (read before citing):

- **Working label only.** FALL-1 and this module name are working
  labels from the gravity fall pin scoping
  (`~/workspace/your_files/gravity-fall-pin-scope-2026-11-17.md`,
  §2 F1-field, §3 FALL-1); Zero names. Commissioned by Zero
  2026-11-17 12:38 EST ("Fire FALL-1"). FALL-2 and FALL-3 are
  separate bricks and are NOT in this module.
- **What this is.** The field-side descent content of the grounded
  seat (UA-2, `BoundarySeat`, in census), over
  `φ = groundedPotential w hw hw0 hpos b ρ`:
  (i) **the descent step** — at any ungrounded site where the
  source is positive (`ρ i > 0`), some site sits strictly lower
  in `φ`. Proved FROM the grounded Poisson identity
  (`laplacianOp_groundedPotential`): the data consumed is
  `(w, ρ, the grounding)` via the landed inversion, and no
  notion of falling, motion, or response is used or defined.
  (ii) **termination** — iterated strict descent of an arbitrary
  potential on a finite seat reaches a descent minimum in
  finitely many steps (pure finite combinatorics; the measure
  is the count of strictly-lower sites, and it strictly drops
  at every step). (iii) **the ground is a descent minimum**
  for `ρ ≥ 0`, via the minimum principle
  (`groundedPotential_nonneg`). (iv) **the failure
  countermodel** — an explicit `Fin 3` seat with a
  sign-indefinite source (`ρ 1 = -1`) whose grounded potential
  is `(0, -2/3, -1/3)`: descent from the ground strands at the
  ungrounded site `1`, and the ground is not a descent
  minimum. The `ρ ≥ 0` hypothesis of (iii) is load-bearing,
  exhibited, not assumed away.
- **DEVIATION FROM THE SCOPE, AT FULL RANK.** The scope priced
  the countermodel as "an ungrounded local minimum of `φ` that
  is not the global minimum". On the landed seat that statement
  is unprovable, for a structural reason: `BoundarySeat`'s
  hypothesis `hpos` makes every off-diagonal weight strictly
  positive — the seat graph is complete, every site is adjacent
  to every other — so a descent (local) minimum is automatically
  a global minimum, for a source of ANY sign. The countermodel
  in §4 therefore exhibits the true load-bearing failure at the
  same joint: with sign-indefinite `ρ` the GROUND stops being a
  minimum and descent strands at an ungrounded minimum. The
  hypothesis is exhibited as load-bearing exactly where the
  scope demanded; the impossible stronger wording is not
  shipped. (Recorded in STATUS-FALL1.md before the build.)
- **What this is not.** No body falls in this module. There is
  no test body, no trajectory, no time, no acceleration, no
  force, no inertia law; the descent is a property of the
  FIELD's values on a finite seat, and `FallPath` is
  bookkeeping for the termination statement (its step rule is
  a definition, on its face). F1-body — "the body's fall IS
  the descent path" — was KILLED at scoping and is not shipped
  in any dress. Presenting this module as a falling body,
  dynamics, a gravity object, or Dial evidence fires
  **K-FALL-SCOPE** (pre-registered, scope §4). **NO CLAIM;
  dials 0/4. Dial 2 = 0.**
- **Kills standing over this brick.** K-FALL-CIRCULAR: does
  not fire — the descent is a THEOREM from fall-free data
  (the grounded inversion and the sign of `ρ`), not a
  definition of falling. K-FALL-SIGN: does not fire — every
  direction is derived from `laplacianOp`'s landed sign
  conventions and the inversion; no sign is chosen here.
  K-FALL-VAC: does not fire — the step carries its hypotheses
  (ungrounded site, `ρ i > 0`) on its face, and the
  countermodel exhibits where the `ρ ≥ 0` form stops.
  K-FALL-COARSE: not touched — everything runs on the full
  field `φ`, never on the coarse triple.
- Zero sorrys, no `native_decide`; headline axioms exactly
  the standard three (`propext`, `Classical.choice`,
  `Quot.sound`).
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. Descent minima and descent paths (bookkeeping) -/

/-- A **descent minimum** of a potential `φ`: no site sits
strictly below `m`. (On the grounded seat every site is
adjacent to every other — `hpos` — so this is also the global
minimum; it is stated in descent language because descent is
what this brick is about.) -/
def IsFallMin (φ : V → ℝ) (m : V) : Prop :=
  ∀ j ≠ m, φ m ≤ φ j

/-- A **descent path** from `i` to `k`: a finite chain of
strict decreases of `φ`. Bookkeeping for the termination
statement; the step rule is a definition, and no dynamics is
claimed for it. -/
inductive FallPath (φ : V → ℝ) : V → V → Prop
  | refl (i : V) : FallPath φ i i
  | step {i j k : V} (hji : φ j < φ i) (hjk : FallPath φ j k) :
      FallPath φ i k

/-! ## §2. The descent step and termination -/

/-- **The descent step (FALL-1 headline).** At an ungrounded
site where the source is positive, some site sits strictly
lower in the grounded potential. The grounded Poisson identity
writes `ρ i` as the `w`-weighted sum of the drops
`φ i - φ j`; were no site strictly lower, every drop would be
`≤ 0` and — the weights being nonnegative — the sum would be
`≤ 0`, against `ρ i > 0`. The data consumed is `(w, ρ, the
grounding)` via the landed inversion; no notion of falling is
used. -/
theorem groundedPotential_descent_step (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (ρ : V → ℝ)
    {i : V} (hi : i ≠ b) (hρ : 0 < ρ i) :
    ∃ j ≠ i, groundedPotential w hw hw0 hpos b ρ j
      < groundedPotential w hw hw0 hpos b ρ i := by
  classical
  have hL : laplacianOp w (groundedPotential w hw hw0 hpos b ρ) i
      = ρ i :=
    laplacianOp_groundedPotential w hw hw0 hpos b ρ hi
  by_contra hcon
  push_neg at hcon
  have hterm : ∀ j ∈ Finset.univ,
      w i j * (groundedPotential w hw hw0 hpos b ρ i
        - groundedPotential w hw hw0 hpos b ρ j) ≤ 0 := by
    intro j _
    have hle : groundedPotential w hw hw0 hpos b ρ i
        ≤ groundedPotential w hw hw0 hpos b ρ j := by
      by_cases hji : j = i
      · rw [hji]
      · exact hcon j hji
    exact mul_nonpos_of_nonneg_of_nonpos (hw0 i j) (by linarith)
  have hsum : ∑ j, w i j * (groundedPotential w hw hw0 hpos b ρ i
      - groundedPotential w hw hw0 hpos b ρ j) ≤ 0 :=
    Finset.sum_nonpos hterm
  rw [laplacianOp_apply] at hL
  linarith

/-- **Descent terminates.** From any site, iterated strict
descent of an arbitrary potential on a finite seat reaches a
descent minimum in finitely many steps. Pure finite
combinatorics: the induction measure is the number of sites
sitting strictly below the current one — the next site is
itself strictly below the current one and not below itself,
so the measure strictly drops at every step. No field data
is used; termination is not where this brick's content is —
the step lemma is. -/
theorem fallPath_terminates (φ : V → ℝ) (i : V) :
    ∃ m, IsFallMin φ m ∧ FallPath φ i m := by
  classical
  have key : ∀ n : ℕ, ∀ i : V,
      (Finset.univ.filter (fun j => φ j < φ i)).card ≤ n →
      ∃ m, IsFallMin φ m ∧ FallPath φ i m := by
    intro n
    induction n with
    | zero =>
      intro i hi
      refine ⟨i, ?_, FallPath.refl i⟩
      intro j hj
      by_contra hlt
      push_neg at hlt
      have hmem : j ∈ Finset.univ.filter (fun j => φ j < φ i) := by
        simp [hlt]
      have hpos : 0 < (Finset.univ.filter
          (fun j => φ j < φ i)).card :=
        Finset.card_pos.mpr ⟨j, hmem⟩
      omega
    | succ n ih =>
      intro i hi
      by_cases hmin : IsFallMin φ i
      · exact ⟨i, hmin, FallPath.refl i⟩
      · have hstep : ∃ j ≠ i, φ j < φ i := by
          have h := hmin
          unfold IsFallMin at h
          push_neg at h
          exact h
        obtain ⟨j, -, hjlt⟩ := hstep
        have hsub : Finset.univ.filter (fun k => φ k < φ j)
            ⊆ Finset.univ.filter (fun k => φ k < φ i) := by
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            at hk ⊢
          exact lt_trans hk hjlt
        have hjmem : j ∈ Finset.univ.filter
            (fun k => φ k < φ i) := by
          simp [hjlt]
        have hjnot : j ∉ Finset.univ.filter
            (fun k => φ k < φ j) := by
          simp
        have hcard : (Finset.univ.filter
              (fun k => φ k < φ j)).card
            < (Finset.univ.filter
              (fun k => φ k < φ i)).card :=
          Finset.card_lt_card
            (Finset.ssubset_iff.mpr
              ⟨j, hjnot, Finset.insert_subset hjmem hsub⟩)
        obtain ⟨m, hm, hpath⟩ := ih j (by omega)
        exact ⟨m, hm, FallPath.step hjlt hpath⟩
  exact key _ i le_rfl

/-- **Termination, grounded form.** The descent of the
grounded potential from any site reaches a descent minimum —
§2's combinatorics applied to `φ = groundedPotential`. -/
theorem groundedPotential_fallPath_terminates (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (ρ : V → ℝ)
    (i : V) :
    ∃ m, IsFallMin (groundedPotential w hw hw0 hpos b ρ) m
      ∧ FallPath (groundedPotential w hw hw0 hpos b ρ) i m :=
  fallPath_terminates _ i

/-! ## §3. The minimum principle: the ground is a descent minimum -/

/-- **The minimum principle for the grounded seat.** For a
nonnegative source, the grounded potential is nonnegative
everywhere. At a global minimizer `m` off the ground, every
term of the Poisson sum is `≤ 0` (weights nonnegative, drops
`≤ 0`) while the sum is `ρ m ≥ 0`; so every term vanishes,
and the term at the ground — whose weight is positive —
forces `φ m = φ b = 0`; a negative minimum is impossible. -/
theorem groundedPotential_nonneg (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (ρ : V → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (j : V) :
    0 ≤ groundedPotential w hw hw0 hpos b ρ j := by
  classical
  haveI : Nonempty V := ⟨b⟩
  obtain ⟨m, hm⟩ := Finite.exists_min
    (groundedPotential w hw hw0 hpos b ρ)
  have hφb : groundedPotential w hw hw0 hpos b ρ b = 0 :=
    groundedPotential_at_ground w hw hw0 hpos b ρ
  suffices h : 0 ≤ groundedPotential w hw hw0 hpos b ρ m from
    le_trans h (hm j)
  by_contra hneg
  push_neg at hneg
  have hmb : m ≠ b := by
    rintro rfl
    rw [hφb] at hneg
    exact lt_irrefl 0 hneg
  have hL : laplacianOp w (groundedPotential w hw hw0 hpos b ρ) m
      = ρ m :=
    laplacianOp_groundedPotential w hw hw0 hpos b ρ hmb
  have hterm : ∀ k ∈ Finset.univ,
      w m k * (groundedPotential w hw hw0 hpos b ρ m
        - groundedPotential w hw hw0 hpos b ρ k) ≤ 0 := by
    intro k _
    exact mul_nonpos_of_nonneg_of_nonpos (hw0 m k) (by
      have := hm k
      linarith)
  have hsum0 : ∑ k, w m k * (groundedPotential w hw hw0 hpos b ρ m
      - groundedPotential w hw hw0 hpos b ρ k) = 0 := by
    have h1 : ∑ k, w m k * (groundedPotential w hw hw0 hpos b ρ m
        - groundedPotential w hw hw0 hpos b ρ k) ≤ 0 :=
      Finset.sum_nonpos hterm
    rw [laplacianOp_apply] at hL
    linarith [hρ m]
  have hzero : ∀ k ∈ Finset.univ,
      w m k * (groundedPotential w hw hw0 hpos b ρ m
        - groundedPotential w hw hw0 hpos b ρ k) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos hterm).mp hsum0
  have hbk := hzero b (Finset.mem_univ b)
  rw [hφb, sub_zero] at hbk
  have hm0 : groundedPotential w hw hw0 hpos b ρ m = 0 := by
    rcases mul_eq_zero.mp hbk with h | h
    · exact absurd h (ne_of_gt (hpos m b hmb))
    · exact h
  linarith

/-- **The ground is a descent minimum** (for a nonnegative
source): its value is `0`, and by the minimum principle no
site sits below `0`. -/
theorem groundedPotential_ground_isFallMin (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (ρ : V → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) :
    IsFallMin (groundedPotential w hw hw0 hpos b ρ) b := by
  intro j _
  rw [groundedPotential_at_ground]
  exact groundedPotential_nonneg w hw hw0 hpos b ρ hρ j

/-! ## §4. The failure countermodel: `ρ ≥ 0` is load-bearing -/

/-- **The countermodel.** On the `Fin 3` seat with unit
off-diagonal weights, ground `0`, and the sign-indefinite
source `ρ = ![0, -1, 0]`, the grounded potential is
`![0, -2/3, -1/3]`: descent from the ground steps to the
ungrounded site `1` and strands there (site `1` is a descent
minimum), and the ground is NOT a descent minimum. So the
`ρ ≥ 0` hypothesis of §3 cannot be dropped: it is
load-bearing, exhibited. (The scope's stronger wording — a
local minimum that is not global — is impossible on this
seat for any source, since `hpos` makes the seat complete;
see the header's deviation note.) -/
theorem fall_countermodel_strands :
    ∃ (w : Fin 3 → Fin 3 → ℝ) (hw : ∀ i j, w i j = w j i)
      (hw0 : ∀ i j, 0 ≤ w i j) (hpos : ∀ i j, i ≠ j → 0 < w i j)
      (ρ : Fin 3 → ℝ), ρ 1 < 0
      ∧ IsFallMin (groundedPotential w hw hw0 hpos 0 ρ) 1
      ∧ ¬ IsFallMin (groundedPotential w hw hw0 hpos 0 ρ) 0
      ∧ FallPath (groundedPotential w hw hw0 hpos 0 ρ) 0 1 := by
  classical
  have hwA : ∀ i j : Fin 3,
      ((![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]] : Fin 3 → Fin 3 → ℝ) i j)
        = ((![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]]
            : Fin 3 → Fin 3 → ℝ) j i) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two]
  have hw0A : ∀ i j : Fin 3,
      0 ≤ ((![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]]
        : Fin 3 → Fin 3 → ℝ) i j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two]
  have hposA : ∀ i j : Fin 3, i ≠ j →
      0 < ((![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]]
        : Fin 3 → Fin 3 → ℝ) i j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two]
  have hpot : groundedPotential
        ![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]] hwA hw0A hposA 0
        ![0, -1, 0]
      = ![0, -2/3, -1/3] := by
    refine groundedPotential_unique _ hwA hw0A hposA 0 ![0, -1, 0]
      (groundedPotential _ hwA hw0A hposA 0 ![0, -1, 0]) _ ?_ ?_ ?_ ?_
    · exact groundedPotential_at_ground _ _ _ _ _ _
    · simp [Matrix.cons_val_zero]
    · intro i hi
      exact laplacianOp_groundedPotential _ _ _ _ _ _ hi
    · intro i hi
      have h3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
      rcases h3 i with rfl | rfl | rfl
      · exact absurd rfl hi
      · rw [laplacianOp_apply, Fin.sum_univ_three]
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two]
      · rw [laplacianOp_apply, Fin.sum_univ_three]
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two]
  refine ⟨![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]], hwA, hw0A, hposA,
    ![0, -1, 0], ?_, ?_, ?_, ?_⟩
  · norm_num [Matrix.cons_val_one, Matrix.head_cons]
  · rw [hpot]
    intro j hj
    have h3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
    rcases h3 j with rfl | rfl | rfl
    · norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
    · exact absurd rfl hj
    · norm_num [Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two]
  · rw [hpot]
    intro h
    have hle := h 1 one_ne_zero
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at hle
  · rw [hpot]
    refine FallPath.step ?_ (FallPath.refl 1)
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]

end ThetLogos
