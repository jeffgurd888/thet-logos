/-
# AntiGravitySeatPin — the Newton seat at flipped coupling, and its
ill-posed inverse (finite ℚ seat)

Zero's imagining of 2026-11-16 23:54 EST — "constructing anti-gravity
Il-posed inverse object" — fired by his word at 23:59 EST ("yes
absolutely please"). This pin builds the two halves of that name, as
finite algebra:

- **the flip** (Brick 1): the Newton seat's pair energy at coupling
  `−G` instead of `G`. The flipped energy is the EXACT NEGATION of
  the Newton seat's (`antiPairU = −pairU`), it is positive, and it
  strictly DECREASES as the pair separates — the fleeing direction,
  as an energy statement. Translation invariance is inherited.
- **the thermal inversion** (Brick 2): over the Newton seat's finite
  separation ladder, the flipped energy's Gibbs seat concentrates in
  the cold limit at the LARGEST allowed separation — anti-collapse,
  the mirror of the Newton seat's cold collapse, with the same
  GAPFLOOR bound shape at the ladder's top gap.
- **the ill-posed inverse** (Brick 3): the seat's coarse data map
  (source ↦ (total mass, center of mass, total potential)) is NOT
  injective, by an explicit rational witness: two unit masses at
  (0, 2) and the three masses (1/7, 12/7, 1/7) at (0, 1, 2) have the
  same total mass 2, the same center of mass 1, and the same total
  potential −G/2, at every coupling G.

FENCES (read before citing):
- This is a sign flip in a finite seat's algebra. It is NOT negative
  mass as physics, NOT exotic matter, NOT a device: the physical
  anti-gravity object stays FRONTIER (the energy conditions stand
  against it; no known route exists). Nothing here constructs one.
- The Bondi runaway pair (Bondi 1957) is DYNAMICS — Register-2
  prose, cited as prose. This seat is statics: its fleeing direction
  is an energy monotonicity statement only; no motion, no orbits,
  no time is seated here.
- The ill-posedness witness covers the seat's COARSE data triple
  only — the honest finite shadow of inverse-gravimetry
  non-uniqueness (the shell theorem / equivalent strata are
  Register 2). It does not claim the field-theoretic statement.
- `G` stays the Newton seat's bare positive parameter — never a
  measured value. Not a derivation of gravity; the corpus holds
  zero gravity objects, Dial 2 = 0 stands. NO CLAIM.

Charter: T5 for the seeing; the theorems below are T1 lane grade
when proved. Working label only — the public name is Zero's to coin.
STATUS: STATUS-ANTIGRAVSEAT.md.
-/

import Mathlib
import ThetLogos.CenterBridgePin
import ThetLogos.NewtonSeatPin
import ThetLogos.ModularVariance

namespace ThetLogos.AntiGravitySeatPin

open Finset

variable {k : ℕ}

/-! ## Brick 1 — the flip -/

/-- The flipped pair energy as a function of separation alone:
`+G·a·b/d` — the Newton seat's `sepU` at coupling `−G`. -/
def antiSepU (G a b d : ℚ) : ℚ :=
  G * a * b / d

/-- **Flipped pair potential energy** of two masses on a line:
`+G·m₀·m₁/|x₁ − x₀|` — the Newton seat's `pairU` with the
coupling's sign flipped. -/
def antiPairU (G : ℚ) (m x : Fin 2 → ℚ) : ℚ :=
  antiSepU G (m 0) (m 1) |x 1 - x 0|

/-- The flipped separation energy is the exact negation of the
Newton seat's, at the ladder level. -/
theorem antiSepU_eq_neg_sepU (G a b d : ℚ) :
    antiSepU G a b d = - NewtonSeatPin.sepU G a b d := by
  unfold antiSepU NewtonSeatPin.sepU
  ring

/-- **THE INVERSION IDENTITY.** The flipped pair energy is the
exact negation of the Newton pair energy — every energy statement
of the Newton seat inverts through this one equality. -/
theorem antiPairU_eq_neg_pairU (G : ℚ) (m x : Fin 2 → ℚ) :
    antiPairU G m x = - NewtonSeatPin.pairU G m x := by
  unfold antiPairU NewtonSeatPin.pairU
  exact antiSepU_eq_neg_sepU G (m 0) (m 1) |x 1 - x 0|

/-- **The flipped pair is unbound**: at distinct positions, with
positive masses and positive `G`, the flipped pair energy is
strictly positive — where the Newton pair's energy is negative. -/
theorem antiPairU_pos {G : ℚ} {m x : Fin 2 → ℚ} (hG : 0 < G)
    (hm : ∀ i, 0 < m i) (hx : x 0 ≠ x 1) : 0 < antiPairU G m x := by
  rw [antiPairU_eq_neg_pairU]
  exact neg_pos.mpr (NewtonSeatPin.pairU_neg hG hm hx)

/-- **Repulsion, separation form**: for positive masses and
positive `G`, the flipped pair energy strictly decreases with the
separation — farther is strictly lower. This is the fleeing
direction as an energy statement; no force vector, no motion. -/
theorem antiSepU_repulsion {G a b d₁ d₂ : ℚ} (hG : 0 < G)
    (ha : 0 < a) (hb : 0 < b) (hd₁ : 0 < d₁) (hdd : d₁ < d₂) :
    antiSepU G a b d₂ < antiSepU G a b d₁ := by
  rw [antiSepU_eq_neg_sepU, antiSepU_eq_neg_sepU]
  exact neg_lt_neg (NewtonSeatPin.sepU_lt_sepU hG ha hb hd₁ hdd)

/-- **Repulsion, position form**: of two placements of the same
two masses, the one with the larger separation has strictly lower
flipped pair energy — the mirror of the Newton seat's attraction. -/
theorem antiPairU_repulsion {G : ℚ} {m x y : Fin 2 → ℚ} (hG : 0 < G)
    (hm : ∀ i, 0 < m i) (hx : x 0 ≠ x 1)
    (hsep : |x 1 - x 0| < |y 1 - y 0|) :
    antiPairU G m y < antiPairU G m x := by
  rw [antiPairU_eq_neg_pairU, antiPairU_eq_neg_pairU]
  exact neg_lt_neg (NewtonSeatPin.pairU_attract hG hm hx hsep)

/-- **Translation invariance** (inherited): shifting both
positions by the same `t` leaves the flipped pair energy
unchanged — only the separation matters, as in the Newton seat. -/
theorem antiPairU_translation (G : ℚ) (m x : Fin 2 → ℚ) (t : ℚ) :
    antiPairU G m (fun i => x i + t) = antiPairU G m x := by
  rw [antiPairU_eq_neg_pairU, antiPairU_eq_neg_pairU,
    NewtonSeatPin.pairU_translation]

/-! ## Brick 2 — the thermal inversion -/

/-- **Flipped separation energy** (real form, for the Gibbs seat):
the negation of the Newton seat's `sepEnergy` — the thermal leg
inverts with the pair energy, by definition. -/
noncomputable def antiSepEnergy (G m₀ m₁ : ℚ) (D : Fin k → ℚ)
    (j : Fin k) : ℝ :=
  - NewtonSeatPin.sepEnergy G m₀ m₁ D j

/-- The flipped ladder energy is the exact negation of the Newton
seat's ladder energy. -/
theorem antiSepEnergy_eq_neg_sepEnergy (G m₀ m₁ : ℚ)
    (D : Fin k → ℚ) (j : Fin k) :
    antiSepEnergy G m₀ m₁ D j
      = - NewtonSeatPin.sepEnergy G m₀ m₁ D j :=
  rfl

/-- **The flipped ladder runs downhill**: at positive masses and
positive `G`, the flipped separation energy is strictly
antitone in the separation — a strictly increasing separation
ladder has a strictly decreasing flipped-energy ladder. -/
theorem antiSepEnergy_strictAnti {G m₀ m₁ : ℚ} (hG : 0 < G)
    (hm₀ : 0 < m₀) (hm₁ : 0 < m₁) {D : Fin k → ℚ}
    (hDpos : ∀ j, 0 < D j) (hD : StrictMono D) :
    StrictAnti (antiSepEnergy G m₀ m₁ D) :=
  fun a b hab =>
    neg_lt_neg (NewtonSeatPin.sepEnergy_strictMono hG hm₀ hm₁ hDpos hD hab)

/-- **The ground state is the widest separation**: every other
allowed separation has strictly higher flipped energy than the
maximal one — the maximal separation is the unique energy
minimiser of the flipped seat, where the Newton seat's minimiser
is the closest approach. -/
theorem antiSepEnergy_top_strict {G m₀ m₁ : ℚ} (hG : 0 < G)
    (hm₀ : 0 < m₀) (hm₁ : 0 < m₁) {D : Fin k → ℚ}
    (hDpos : ∀ j, 0 < D j) (hD : StrictMono D) (hk : 2 ≤ k)
    {j : Fin k} (hj : j ≠ ⟨k - 1, by omega⟩) :
    antiSepEnergy G m₀ m₁ D ⟨k - 1, by omega⟩
      < antiSepEnergy G m₀ m₁ D j := by
  apply antiSepEnergy_strictAnti hG hm₀ hm₁ hDpos hD
  rw [Fin.lt_iff_val_lt_val]
  show j.val < k - 1
  have hval : j.val ≠ k - 1 := fun h => hj (Fin.ext h)
  have hjk : j.val < k := j.2
  omega

/-- **The top gap**: the flipped-energy step from the widest
separation down to the next one, `antiU(D (k−2)) − antiU(D (k−1))`
— the gap the cold anti-collapse concentrates across. -/
noncomputable def antiSepGap (G m₀ m₁ : ℚ) (D : Fin k → ℚ)
    (hk : 2 ≤ k) : ℝ :=
  antiSepEnergy G m₀ m₁ D ⟨k - 2, by omega⟩
    - antiSepEnergy G m₀ m₁ D ⟨k - 1, by omega⟩

/-- **The top gap is positive**: the step down from the widest
separation costs strictly positive flipped energy. -/
theorem antiSepGap_pos {G m₀ m₁ : ℚ} (hG : 0 < G) (hm₀ : 0 < m₀)
    (hm₁ : 0 < m₁) {D : Fin k → ℚ} (hDpos : ∀ j, 0 < D j)
    (hD : StrictMono D) (hk : 2 ≤ k) :
    0 < antiSepGap G m₀ m₁ D hk := by
  unfold antiSepGap
  rw [sub_pos]
  exact antiSepEnergy_strictAnti hG hm₀ hm₁ hDpos hD
    (by
      rw [Fin.lt_iff_val_lt_val]
      show k - 2 < k - 1
      omega)

/-- **COLD ANTI-COLLAPSE** (GAPFLOOR shape, the mirror of the
Newton seat's cold collapse): for `β ≥ 0`, the Gibbs weight on
the maximal separation is at least `1 − (k−1)·e^{−β·gap}` — cold
concentrates the flipped pair at the LARGEST allowed separation.
The anti pair's cold ground state is as far apart as the seat
allows: anti-collapse. -/
theorem cold_anti_collapse {G m₀ m₁ : ℚ} (hG : 0 < G)
    (hm₀ : 0 < m₀) (hm₁ : 0 < m₁) {D : Fin k → ℚ}
    (hDpos : ∀ j, 0 < D j) (hD : StrictMono D) (hk : 2 ≤ k)
    {β : ℝ} (hβ : 0 ≤ β) :
    1 - ((k : ℝ) - 1) * Real.exp (-(β * antiSepGap G m₀ m₁ D hk))
      ≤ ModularVariance.gibbsProb (antiSepEnergy G m₀ m₁ D) β
          ⟨k - 1, by omega⟩ := by
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  set E := antiSepEnergy G m₀ m₁ D with hE
  set z : Fin k := ⟨k - 1, by omega⟩ with hz
  have hanti : StrictAnti E :=
    antiSepEnergy_strictAnti hG hm₀ hm₁ hDpos hD
  have hgap : antiSepGap G m₀ m₁ D hk
      = E ⟨k - 2, by omega⟩ - E z := rfl
  have hstep : ∀ j : Fin k, j ≠ z → E ⟨k - 2, by omega⟩ ≤ E j := by
    intro j hj
    rcases eq_or_ne j ⟨k - 2, by omega⟩ with rfl | hne
    · exact le_rfl
    · have hjz : j.val ≠ k - 1 := fun h => hj (Fin.ext h)
      have hne2 : j.val ≠ k - 2 := fun h => hne (Fin.ext h)
      have hjk : j.val < k := j.2
      have hlt : j < ⟨k - 2, by omega⟩ := by
        rw [Fin.lt_iff_val_lt_val]
        show j.val < k - 2
        omega
      exact (hanti hlt).le
  have hEj : ∀ j : Fin k, j ≠ z → E z + antiSepGap G m₀ m₁ D hk ≤ E j := by
    intro j hj
    have hs := hstep j hj
    have hgap' : antiSepGap G m₀ m₁ D hk
        = E ⟨k - 2, by omega⟩ - E z := hgap
    linarith
  have hZ : Real.exp (-(β * E z)) ≤ ModularVariance.partSum E β := by
    show Real.exp (-(β * E z)) ≤ ∑ i, Real.exp (-(β * E i))
    exact Finset.single_le_sum (f := fun i => Real.exp (-(β * E i)))
      (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ z)
  have hterm : ∀ j ∈ Finset.univ \ {z},
      ModularVariance.gibbsProb E β j
        ≤ Real.exp (-(β * antiSepGap G m₀ m₁ D hk)) := by
    intro j hj
    rw [Finset.mem_sdiff] at hj
    have hjne : j ≠ z := fun h => hj.2 (Finset.mem_singleton.mpr h)
    have hEj' := hEj j hjne
    unfold ModularVariance.gibbsProb
    rw [div_le_iff₀ (ModularVariance.partSum_pos E β)]
    calc Real.exp (-(β * E j))
        ≤ Real.exp (-(β * antiSepGap G m₀ m₁ D hk))
            * Real.exp (-(β * E z)) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hmul : β * (E z + antiSepGap G m₀ m₁ D hk) ≤ β * E j :=
            mul_le_mul_of_nonneg_left hEj' hβ
          linarith
      _ ≤ Real.exp (-(β * antiSepGap G m₀ m₁ D hk))
            * ModularVariance.partSum E β :=
          mul_le_mul_of_nonneg_left hZ (Real.exp_pos _).le
  have hsum : ∑ j ∈ Finset.univ \ {z}, ModularVariance.gibbsProb E β j
      ≤ ((k : ℝ) - 1) * Real.exp (-(β * antiSepGap G m₀ m₁ D hk)) := by
    calc ∑ j ∈ Finset.univ \ {z}, ModularVariance.gibbsProb E β j
        ≤ ∑ j ∈ Finset.univ \ {z},
            Real.exp (-(β * antiSepGap G m₀ m₁ D hk)) :=
          Finset.sum_le_sum hterm
      _ = ((k : ℝ) - 1) * Real.exp (-(β * antiSepGap G m₀ m₁ D hk)) := by
          rw [Finset.sum_const, Finset.card_sdiff, Finset.card_univ,
            Fintype.card_fin, Finset.inter_univ, Finset.card_singleton,
            nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hsplit : ModularVariance.gibbsProb E β z
      + ∑ j ∈ Finset.univ \ {z}, ModularVariance.gibbsProb E β j
      = 1 := by
    rw [Finset.sdiff_singleton_eq_erase]
    exact (Finset.add_sum_erase _ _
      (Finset.mem_univ z)).trans (ModularVariance.sum_gibbsProb E β)
  linarith

/-- **HOT WASHOUT**: at `β = 0` the Gibbs distribution over the
separations is uniform — every allowed separation carries weight
`1/k`, the widest no more than the narrowest. Heat erases the
anti-collapse, as it erases the collapse. -/
theorem hot_washout_anti {G m₀ m₁ : ℚ} {D : Fin k → ℚ}
    (hk : 0 < k) (j : Fin k) :
    ModularVariance.gibbsProb (antiSepEnergy G m₀ m₁ D) 0 j
      = 1 / (k : ℝ) := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  unfold ModularVariance.gibbsProb ModularVariance.partSum
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-! ## Brick 3 — the ill-posedness witness -/

/-- **The seat's coarse data** of a finite source at coupling
`G`: total mass, center of mass (the bridge pin's `centerMass`),
and total potential (the Newton seat's `totalU`). This is the
data map whose inverse problem the witness below shows to be
ill-posed: the data do not determine the source. -/
def dataOf {n : ℕ} [Nonempty (Fin n)] (G : ℚ) (m x : Fin n → ℚ) :
    ℚ × ℚ × ℚ :=
  (∑ i, m i, CenterBridgePin.centerMass m x, NewtonSeatPin.totalU G m x)

/-- **Witness A, data**: two unit masses at positions (0, 2) have
total mass 2, center of mass 1, and total potential `−G/2`, at
every coupling `G`. -/
theorem witnessA_data (G : ℚ) :
    dataOf G ![1, 1] ![0, 2] = (2, 1, -G / 2) := by
  unfold dataOf
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · norm_num [Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
  · unfold CenterBridgePin.centerMass CenterBridgePin.wCenter
    norm_num [Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
  · rw [NewtonSeatPin.totalU_fin_two]
    norm_num [NewtonSeatPin.pairU, NewtonSeatPin.sepU,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- **Witness B, data**: the three masses (1/7, 12/7, 1/7) at
positions (0, 1, 2) have total mass 2, center of mass 1, and
total potential `−G/2`, at every coupling `G` — the same data
triple as witness A, from a different source. (Pair sum:
12/49 + 1/98 + 12/49 = 1/2.) -/
theorem witnessB_data (G : ℚ) :
    dataOf G ![1/7, 12/7, 1/7] ![0, 1, 2] = (2, 1, -G / 2) := by
  have hset : (Finset.univ.filter
        (fun p : Fin 3 × Fin 3 => p.1 < p.2))
      = {(0, 1), (0, 2), (1, 2)} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    obtain ⟨a, b⟩ := p
    fin_cases a <;> fin_cases b <;> simp_all
  unfold dataOf
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · norm_num [Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
  · unfold CenterBridgePin.centerMass CenterBridgePin.wCenter
    norm_num [Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
  · unfold NewtonSeatPin.totalU
    rw [hset, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_singleton]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    norm_num
    ring

/-- **THE INVERSE PROBLEM IS ILL-POSED AT THIS SEAT.** The
seat's coarse data map (at any fixed coupling `G`, read over
three-site sources) is not injective: the padded witness A
(masses (1, 1, 0) at (0, 2, 5) — witness A with a zero-mass site
added, which moves none of the data) and witness B (masses
(1/7, 12/7, 1/7) at (0, 1, 2)) carry the SAME data triple
(2, 1, −G/2), yet they are different sources (their mass
functions differ at site 2: 0 ≠ 1/7). Together with
`witnessA_data` — the unpadded two-site witness A has the same
triple — the seat's data do not determine the source: across
arities, and already at fixed arity. This is the finite shadow
of inverse-gravimetry non-uniqueness, stated for the coarse
triple only. -/
theorem data_not_injective (G : ℚ) :
    ¬ Function.Injective
      (fun p : (Fin 3 → ℚ) × (Fin 3 → ℚ) => dataOf G p.1 p.2) := by
  intro hinj
  have hpad : dataOf G ![1, 1, 0] ![0, 2, 5] = (2, 1, -G / 2) := by
    have hset : (Finset.univ.filter
          (fun p : Fin 3 × Fin 3 => p.1 < p.2))
        = {(0, 1), (0, 2), (1, 2)} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      obtain ⟨a, b⟩ := p
      fin_cases a <;> fin_cases b <;> simp_all
    unfold dataOf
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · norm_num [Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
    · unfold CenterBridgePin.centerMass CenterBridgePin.wCenter
      norm_num [Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
    · unfold NewtonSeatPin.totalU
      rw [hset, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        Finset.sum_singleton]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      try norm_num
      try ring
  have hdata : dataOf G ![1, 1, 0] ![0, 2, 5]
      = dataOf G ![1/7, 12/7, 1/7] ![0, 1, 2] := by
    rw [hpad, witnessB_data]
  have hdata' : (fun p : (Fin 3 → ℚ) × (Fin 3 → ℚ) => dataOf G p.1 p.2)
        (![1, 1, 0], ![0, 2, 5])
      = (fun p : (Fin 3 → ℚ) × (Fin 3 → ℚ) => dataOf G p.1 p.2)
        (![1/7, 12/7, 1/7], ![0, 1, 2]) := hdata
  have h := hinj hdata'
  have h2 := congrArg (fun p : (Fin 3 → ℚ) × (Fin 3 → ℚ) => p.1 2) h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h2
  norm_num at h2

end ThetLogos.AntiGravitySeatPin
