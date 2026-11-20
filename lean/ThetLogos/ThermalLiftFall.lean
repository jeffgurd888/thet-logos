import Mathlib.Tactic
import ThetLogos.ThermalLiftFallPin

/-!
# ThetLogos.ThermalLiftFall — THERMAL LIFT, brick LIFT-2

**Fall inside the gradient.** The frozen forms of
`ThermalLiftFallPin` (LIFT-0b), proved over the grounded
thermal potential — the grounded seat's potential for the
thermal contrast: a strictly lower neighbour wherever the
contrast is positive; finite descent terminates; the
ground is a fall minimum under the sign condition; and a
countermodel exhibiting the sign condition as
load-bearing.

The proof architecture is FALL-1's (descent over the
grounded potential), with the source instantiated to the
thermal contrast and FALL-1 cited at its grade: at the
time of writing FALL-1 is lane grade, so nothing here
imports or depends on it — the arguments are re-derived
from the landed inversion
(`BoundarySeat.laplacianOp_groundedPotential`), exactly
as the scope's gate prescribes (BoundarySeat + composite
in census; FALL-1 never a dependency).

**K-LIFT-SIGN fires in its registered form — as a
boundary, not a failure.** The countermodel (§4): on the
`Fin 3` seat with unit weights, constant profile
`β = 1` and energies `![0, -1, 0]`, the thermal contrast
at site `1` is negative, the grounded thermal potential
is `![0, -e/(3(2+e)), 0]` (with `e = Real.exp 1`), site
`1` sits strictly below the ground and is a fall minimum,
and the ground is not a fall minimum. So "fall" over heat
data holds exactly under the stated sign condition —
the contrast nonnegative off the ground — and this brick
reports that boundary as its result.

**Fences.** Descent is bookkeeping over a potential:
statics, not dynamics; no motion, no response, no test
body is defined or claimed. The gravity word attaches to
nothing here (K-GR-LAUNDER). **Dial 2 = 0 under every
outcome. NO CLAIM; dials 0/4.**
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## §1. The descent step -/

/-- **The descent step (LIFT-2 headline).** At an
ungrounded site where the thermal contrast is positive,
some site sits strictly lower in the grounded thermal
potential. The grounded Poisson identity writes the
contrast at `i` as the `w`-weighted sum of the drops;
were no site strictly lower, every drop would be `≤ 0`
and the sum would be `≤ 0`, against the contrast's
positivity. The data consumed is `(w, the contrast, the
grounding)` via the landed inversion; no notion of
falling is used. -/
theorem groundedThermal_descent_step (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (β : V → ℝ)
    (E : V → ℝ) {i : V} (hi : i ≠ b)
    (h : 0 < thermalContrast β E i) :
    ∃ j ≠ i, groundedThermalPotential w hw hw0 hpos b β E j
      < groundedThermalPotential w hw hw0 hpos b β E i := by
  classical
  have hL : laplacianOp w
        (groundedThermalPotential w hw hw0 hpos b β E) i
      = thermalContrast β E i :=
    laplacianOp_groundedPotential w hw hw0 hpos b
      (thermalContrast β E) hi
  by_contra hcon
  push_neg at hcon
  have hterm : ∀ j ∈ Finset.univ,
      w i j * (groundedThermalPotential w hw hw0 hpos b β E i
        - groundedThermalPotential w hw hw0 hpos b β E j)
        ≤ 0 := by
    intro j _
    have hle : groundedThermalPotential w hw hw0 hpos b β E i
        ≤ groundedThermalPotential w hw hw0 hpos b β E j := by
      by_cases hji : j = i
      · rw [hji]
      · exact hcon j hji
    exact mul_nonpos_of_nonneg_of_nonpos (hw0 i j) (by linarith)
  have hsum : ∑ j, w i j
      * (groundedThermalPotential w hw hw0 hpos b β E i
        - groundedThermalPotential w hw hw0 hpos b β E j)
        ≤ 0 :=
    Finset.sum_nonpos hterm
  rw [laplacianOp_apply] at hL
  linarith

/-- **LIFT-2, the descent form (frozen target, proved).** -/
theorem thermalDescentForm_holds (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (β : V → ℝ)
    (E : V → ℝ) :
    ThermalDescentForm w hw hw0 hpos b β E :=
  groundedThermal_descent_step w hw hw0 hpos b β E

/-! ## §2. Termination -/

/-- **Descent terminates.** From any site, iterated
strict descent of an arbitrary potential on a finite
seat reaches a fall minimum in finitely many steps.
Pure finite combinatorics: the induction measure is the
number of sites sitting strictly below the current one.
No thermal data is used; termination is not where this
brick's content is — the step lemma is. -/
theorem thermalFallPath_terminates (φ : V → ℝ) (i : V) :
    ∃ m, IsThermalFallMin φ m ∧ ThermalFallPath φ i m := by
  classical
  have key : ∀ n : ℕ, ∀ i : V,
      (Finset.univ.filter (fun j => φ j < φ i)).card ≤ n →
      ∃ m, IsThermalFallMin φ m ∧ ThermalFallPath φ i m := by
    intro n
    induction n with
    | zero =>
      intro i hi
      refine ⟨i, ?_, ThermalFallPath.refl i⟩
      intro j hj
      by_contra hlt
      push_neg at hlt
      have hmem : j ∈ Finset.univ.filter
          (fun j => φ j < φ i) := by
        simp [hlt]
      have hpos : 0 < (Finset.univ.filter
          (fun j => φ j < φ i)).card :=
        Finset.card_pos.mpr ⟨j, hmem⟩
      omega
    | succ n ih =>
      intro i hi
      by_cases hmin : IsThermalFallMin φ i
      · exact ⟨i, hmin, ThermalFallPath.refl i⟩
      · have hstep : ∃ j ≠ i, φ j < φ i := by
          have h := hmin
          unfold IsThermalFallMin at h
          push_neg at h
          exact h
        obtain ⟨j, -, hjlt⟩ := hstep
        have hsub : Finset.univ.filter (fun k => φ k < φ j)
            ⊆ Finset.univ.filter (fun k => φ k < φ i) := by
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ,
            true_and] at hk ⊢
          exact lt_trans hk hjlt
        have hjmem : j ∈ Finset.univ.filter
            (fun k => φ k < φ i) := by
          simp [hjlt]
        have hjnot : j ∉ Finset.univ.filter
            (fun k => φ k < φ j) := by
          simp
        have hins : insert j (Finset.univ.filter
              (fun k => φ k < φ j))
            ⊆ Finset.univ.filter (fun k => φ k < φ i) := by
          intro k hk
          simp only [Finset.mem_insert, Finset.mem_filter,
            Finset.mem_univ, true_and] at hk ⊢
          rcases hk with rfl | hk
          · exact hjlt
          · exact lt_trans hk hjlt
        have hcard : (Finset.univ.filter
              (fun k => φ k < φ j)).card
            < (Finset.univ.filter
              (fun k => φ k < φ i)).card :=
          Finset.card_lt_card
            (Finset.ssubset_iff.mpr ⟨j, hjnot, hins⟩)
        obtain ⟨m, hm, hpath⟩ := ih j (by omega)
        exact ⟨m, hm, ThermalFallPath.step hjlt hpath⟩
  exact key _ i le_rfl

/-- **LIFT-2, the termination form (frozen target,
proved).** -/
theorem thermalTerminationForm_holds (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (β : V → ℝ)
    (E : V → ℝ) :
    ThermalTerminationForm w hw hw0 hpos b β E :=
  fun i => thermalFallPath_terminates _ i

/-! ## §3. The minimum principle: the ground is a fall minimum -/

/-- **The minimum principle for the grounded thermal
potential.** Wherever the thermal contrast is
nonnegative off the ground, the grounded thermal
potential is nonnegative everywhere. At a global
minimizer `m` off the ground, every term of the Poisson
sum is `≤ 0` while the sum is the contrast at `m`,
which is `≥ 0`; so every term vanishes, and the term at
the ground — whose weight is positive — forces
`φ m = φ b = 0`; a negative minimum is impossible. -/
theorem groundedThermal_nonneg (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (β : V → ℝ)
    (E : V → ℝ)
    (h : ∀ i, i ≠ b → 0 ≤ thermalContrast β E i) (j : V) :
    0 ≤ groundedThermalPotential w hw hw0 hpos b β E j := by
  classical
  obtain ⟨m, hm⟩ := Finite.exists_min
    (groundedThermalPotential w hw hw0 hpos b β E)
  have hφb : groundedThermalPotential w hw hw0 hpos b β E b
      = 0 :=
    groundedPotential_at_ground w hw hw0 hpos b
      (thermalContrast β E)
  suffices hs : 0 ≤ groundedThermalPotential w hw hw0 hpos
      b β E m from
    le_trans hs (hm j)
  by_contra hneg
  push_neg at hneg
  have hmb : m ≠ b := by
    rintro rfl
    rw [hφb] at hneg
    exact lt_irrefl 0 hneg
  have hL : laplacianOp w
        (groundedThermalPotential w hw hw0 hpos b β E) m
      = thermalContrast β E m :=
    laplacianOp_groundedPotential w hw hw0 hpos b
      (thermalContrast β E) hmb
  have hterm : ∀ k ∈ Finset.univ,
      w m k * (groundedThermalPotential w hw hw0 hpos b β E m
        - groundedThermalPotential w hw hw0 hpos b β E k)
        ≤ 0 := by
    intro k _
    exact mul_nonpos_of_nonneg_of_nonpos (hw0 m k) (by
      have hmk := hm k
      linarith)
  have hsum0 : ∑ k, w m k
      * (groundedThermalPotential w hw hw0 hpos b β E m
        - groundedThermalPotential w hw hw0 hpos b β E k)
        = 0 := by
    have h1 : ∑ k, w m k
        * (groundedThermalPotential w hw hw0 hpos b β E m
          - groundedThermalPotential w hw hw0 hpos b β E k)
          ≤ 0 :=
      Finset.sum_nonpos hterm
    rw [laplacianOp_apply] at hL
    linarith [h m hmb]
  have hzero : ∀ k ∈ Finset.univ,
      w m k * (groundedThermalPotential w hw hw0 hpos b β E m
        - groundedThermalPotential w hw hw0 hpos b β E k)
        = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos hterm).mp hsum0
  have hbk := hzero b (Finset.mem_univ b)
  rw [hφb, sub_zero] at hbk
  have hm0 : groundedThermalPotential w hw hw0 hpos b β E m
      = 0 := by
    rcases mul_eq_zero.mp hbk with hh | hh
    · exact absurd hh (ne_of_gt (hpos m b hmb))
    · exact hh
  linarith

/-- **LIFT-2, the ground form (frozen target, proved).**
Under the sign condition the ground is a thermal fall
minimum: its value is `0`, and by the minimum principle
no site sits below `0`. -/
theorem thermalGroundForm_holds (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (β : V → ℝ)
    (E : V → ℝ) :
    ThermalGroundForm w hw hw0 hpos b β E := by
  intro h j _
  have hb : groundedThermalPotential w hw hw0 hpos b β E b
      = 0 :=
    groundedPotential_at_ground w hw hw0 hpos b
      (thermalContrast β E)
  rw [hb]
  exact groundedThermal_nonneg w hw hw0 hpos b β E h j

/-! ## §4. The failure countermodel: the sign condition is load-bearing -/

/-- **The countermodel (K-LIFT-SIGN's boundary,
exhibited).** On the `Fin 3` seat with unit off-diagonal
weights, ground `0`, constant profile `β = 1` and
energies `![0, -1, 0]`, the thermal contrast at site `1`
is negative, the grounded thermal potential is
`![0, -e/(3(2+e)), 0]` with `e = Real.exp 1`: descent
from the ground steps to site `1` and strands there
(site `1` is a fall minimum), and the ground is NOT a
fall minimum. So the sign hypothesis of §3 cannot be
dropped: it is load-bearing, exhibited — the mirror of
FALL-1's shipped countermodel, at the thermal source. -/
theorem thermal_countermodel_strands :
    ∃ (w : Fin 3 → Fin 3 → ℝ) (hw : ∀ i j, w i j = w j i)
      (hw0 : ∀ i j, 0 ≤ w i j)
      (hpos : ∀ i j, i ≠ j → 0 < w i j)
      (β : Fin 3 → ℝ) (E : Fin 3 → ℝ),
      thermalContrast β E 1 < 0
      ∧ IsThermalFallMin
          (groundedThermalPotential w hw hw0 hpos 0 β E) 1
      ∧ ¬ IsThermalFallMin
          (groundedThermalPotential w hw hw0 hpos 0 β E) 0
      ∧ ThermalFallPath
          (groundedThermalPotential w hw hw0 hpos 0 β E)
          0 1 := by
  classical
  have hwA : ∀ i j : Fin 3,
      ((![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]]
        : Fin 3 → Fin 3 → ℝ) i j)
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
  -- The thermal data of the countermodel, computed.
  have hZ : profPartition (fun _ => (1 : ℝ)) ![0, -1, 0]
      = 2 + Real.exp 1 := by
    unfold profPartition
    rw [Fin.sum_univ_three]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Real.exp_zero]
    try ring
  have hs1 : profThermalSource (fun _ => (1 : ℝ)) ![0, -1, 0] 1
      = -Real.exp 1 / (2 + Real.exp 1) := by
    unfold profThermalSource profWeight
    rw [hZ]
    norm_num [Matrix.cons_val_one, Matrix.head_cons]
    try field_simp
    try ring
  have hs0 : profThermalSource (fun _ => (1 : ℝ)) ![0, -1, 0] 0
      = 0 := by
    unfold profThermalSource
    norm_num [Matrix.cons_val_zero]
  have hs2 : profThermalSource (fun _ => (1 : ℝ)) ![0, -1, 0] 2
      = 0 := by
    unfold profThermalSource
    norm_num [Matrix.cons_val_two, Matrix.head_cons]
  have hsum : ∑ k, profThermalSource (fun _ => (1 : ℝ))
        ![0, -1, 0] k
      = -Real.exp 1 / (2 + Real.exp 1) := by
    rw [Fin.sum_univ_three, hs0, hs1, hs2]
    ring
  have hg1 : thermalContrast (fun _ => (1 : ℝ)) ![0, -1, 0] 1
      = -2 * Real.exp 1 / (3 * (2 + Real.exp 1)) := by
    unfold thermalContrast meanSub meanVal
    rw [hsum, hs1]
    norm_num [Fintype.card_fin]
    try field_simp
    try ring
  have hg2 : thermalContrast (fun _ => (1 : ℝ)) ![0, -1, 0] 2
      = Real.exp 1 / (3 * (2 + Real.exp 1)) := by
    unfold thermalContrast meanSub meanVal
    rw [hsum, hs2]
    norm_num [Fintype.card_fin]
    try field_simp
    try ring
  have hpot : groundedThermalPotential
        ![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]] hwA hw0A hposA 0
        (fun _ => (1 : ℝ)) ![0, -1, 0]
      = ![0, -Real.exp 1 / (3 * (2 + Real.exp 1)), 0] := by
    refine groundedPotential_unique
      ![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]] hwA hw0A hposA 0
      (thermalContrast (fun _ => (1 : ℝ)) ![0, -1, 0]) _ _
      ?_ ?_ ?_ ?_
    · exact groundedPotential_at_ground _ _ _ _ _ _
    · simp [Matrix.cons_val_zero]
    · intro i hi
      exact laplacianOp_groundedPotential _ _ _ _ _ _ hi
    · intro i hi
      have h3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
      rcases h3 i with rfl | rfl | rfl
      · exact absurd rfl hi
      · rw [laplacianOp_apply, Fin.sum_univ_three, hg1]
        simp [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.tail_cons,
          Matrix.cons_val_two]
        try field_simp
        try ring
      · rw [laplacianOp_apply, Fin.sum_univ_three, hg2]
        simp [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.tail_cons,
          Matrix.cons_val_two]
        try field_simp
        try ring
  refine ⟨![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]], hwA, hw0A,
    hposA, (fun _ => (1 : ℝ)), ![0, -1, 0], ?_, ?_, ?_, ?_⟩
  · rw [hg1]
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    have hden : 0 < 3 * (2 + Real.exp 1) := by positivity
    exact div_neg_of_neg_of_pos (by linarith) hden
  · rw [hpot]
    intro j hj
    have h3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
    rcases h3 j with rfl | rfl | rfl
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
      have he : 0 < Real.exp 1 := Real.exp_pos 1
      have hden : 0 < 3 * (2 + Real.exp 1) := by positivity
      exact (div_neg_of_neg_of_pos (by linarith) hden).le
    · exact absurd rfl hj
    · simp only [Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two]
      have he : 0 < Real.exp 1 := Real.exp_pos 1
      have hden : 0 < 3 * (2 + Real.exp 1) := by positivity
      exact (div_neg_of_neg_of_pos (by linarith) hden).le
  · rw [hpot]
    intro h
    have hle := h 1 one_ne_zero
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at hle
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    have hden : 0 < 3 * (2 + Real.exp 1) := by positivity
    have hneg : -Real.exp 1 / (3 * (2 + Real.exp 1)) < 0 :=
      div_neg_of_neg_of_pos (by linarith) hden
    linarith
  · rw [hpot]
    refine ThermalFallPath.step ?_ (ThermalFallPath.refl 1)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    have hden : 0 < 3 * (2 + Real.exp 1) := by positivity
    exact div_neg_of_neg_of_pos (by linarith) hden

end ThetLogos
