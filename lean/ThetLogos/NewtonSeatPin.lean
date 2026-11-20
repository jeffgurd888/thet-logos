/-
# NewtonSeatPin — the finite Newtonian seat and its thermal leg

Zero's gravity wish (2026-11-16 23:11 EST) and his dropped
Newton-vs-Einstein poster with "connect them thermally" (23:45 EST)
stand behind this pin. The corpus held NO Newtonian seat — no
inverse-square object at all. This pin builds the finite seat: sites
on a line with masses, Newton's pairwise potential
`U = −G·Σ mᵢmⱼ/dᵢⱼ` with `G` a bare positive parameter, in three legs:

- **the pair law** (Brick 1): the pair energy is negative, symmetric
  under relabelling the sites, translation invariant, and depends on
  the positions only through the separation; ATTRACTION is the exact
  energy statement — closer is strictly lower — and the pair's balance
  point is the bridge pin's center of mass, lying between the sites;
- **the crowd** (Brick 2): the total pair energy over all unordered
  pairs is translation invariant and strictly negative at distinct
  positions; the weighted center is equivariant under global shifts
  (the bridge pin's `wCenter` algebra);
- **the thermal leg** (Brick 3): over a finite set of allowed
  separations, the Gibbs seat at energy `U(d) = −G·m₀m₁/d` — the
  minimal separation is the unique ground state with a positive gap,
  the COLD COLLAPSE concentrates the Gibbs weight on it
  (GAPFLOOR shape), and at `β = 0` the distribution is uniform
  (hot washout). "Cold is forced to find center," in miniature, as a
  theorem of the finite seat.

FENCES (read before citing):
- `G` is a bare positive parameter — this pin never states Newton's
  constant's measured value, and `U` is a finite seat's energy
  function, not a field.
- Attraction is proved as an energy monotonicity statement; no force
  vector, no dynamics, no orbits, no time.
- Negative heat capacity and the gravothermal catastrophe are NOT
  finite-stated here — they are Register-2 prose; the finite shadow
  is Brick 3's cold collapse, labeled as a shadow.
- The Einstein side is untouched (no metric, no curvature); the
  Tolman seat elsewhere in the tree is the GR-side thermal bridge —
  this pin is the Newton-side seat, and the two are not identified.
- Not a derivation of gravity; the corpus holds zero gravity
  objects, Dial 2 = 0 stands. NO CLAIM.

Charter: T5 for the seeing; the theorems below are T1 lane grade
when proved. Working label only — the public name is Zero's to coin.
STATUS: STATUS-NEWTONSEAT.md.
-/

import Mathlib
import ThetLogos.CenterBridgePin
import ThetLogos.ModularVariance

namespace ThetLogos.NewtonSeatPin

open Finset

variable {n k : ℕ}

/-! ## Brick 1 — the pair -/

/-- The pair energy as a function of separation alone:
`−G·a·b/d` for masses `a`, `b` at separation `d`. -/
def sepU (G a b d : ℚ) : ℚ :=
  -G * a * b / d

/-- **Pair potential energy** of two masses on a line:
`−G·m₀·m₁/|x₁ − x₀|` — a function of the separation only,
by definition. -/
def pairU (G : ℚ) (m x : Fin 2 → ℚ) : ℚ :=
  sepU G (m 0) (m 1) |x 1 - x 0|

/-- **Bound pairs have negative energy**: at distinct positions,
with positive masses and positive `G`, the pair energy is
strictly negative. -/
theorem pairU_neg {G : ℚ} {m x : Fin 2 → ℚ} (hG : 0 < G)
    (hm : ∀ i, 0 < m i) (hx : x 0 ≠ x 1) : pairU G m x < 0 := by
  have hd : 0 < |x 1 - x 0| := abs_pos.mpr (sub_ne_zero.mpr hx.symm)
  have hP : 0 < G * m 0 * m 1 := mul_pos (mul_pos hG (hm 0)) (hm 1)
  unfold pairU sepU
  have e : -G * m 0 * m 1 / |x 1 - x 0|
      = -((G * m 0 * m 1) / |x 1 - x 0|) := by ring
  rw [e, neg_lt_zero]
  exact div_pos hP hd

/-- **Symmetry**: relabelling the two sites (the swapped pair
`(![m 1, m 0], ![x 1, x 0])`) leaves the pair energy unchanged —
the numerator product commutes and the separation is the same
absolute difference. -/
theorem pairU_swap (G : ℚ) (m x : Fin 2 → ℚ) :
    pairU G ![m 1, m 0] ![x 1, x 0] = pairU G m x := by
  unfold pairU sepU
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [abs_sub_comm]
  ring

/-- **Attraction, separation form**: for positive masses and
positive `G`, the pair energy strictly increases with the
separation — closer is strictly lower. This is the force's
direction as an energy statement; no force vector is seated. -/
theorem sepU_lt_sepU {G a b d₁ d₂ : ℚ} (hG : 0 < G) (ha : 0 < a)
    (hb : 0 < b) (hd₁ : 0 < d₁) (hdd : d₁ < d₂) :
    sepU G a b d₁ < sepU G a b d₂ := by
  have hd₂ : 0 < d₂ := hd₁.trans hdd
  have hP : 0 < G * a * b := mul_pos (mul_pos hG ha) hb
  have hcore : G * a * b / d₂ < G * a * b / d₁ := by
    rw [div_lt_div_iff₀ hd₂ hd₁]
    exact mul_lt_mul_of_pos_left hdd hP
  unfold sepU
  have e : ∀ d : ℚ, -G * a * b / d = -((G * a * b) / d) := fun d => by ring
  rw [e d₁, e d₂, neg_lt_neg_iff]
  exact hcore

/-- **Attraction, position form**: of two placements of the same
two masses, the one with the smaller separation has strictly
lower pair energy. -/
theorem pairU_attract {G : ℚ} {m x y : Fin 2 → ℚ} (hG : 0 < G)
    (hm : ∀ i, 0 < m i) (hx : x 0 ≠ x 1)
    (hsep : |x 1 - x 0| < |y 1 - y 0|) : pairU G m x < pairU G m y :=
  sepU_lt_sepU hG (hm 0) (hm 1)
    (abs_pos.mpr (sub_ne_zero.mpr hx.symm)) hsep

/-- **Translation invariance**: shifting both positions by the
same `t` leaves the pair energy unchanged — only the separation
matters. -/
theorem pairU_translation (G : ℚ) (m x : Fin 2 → ℚ) (t : ℚ) :
    pairU G m (fun i => x i + t) = pairU G m x := by
  unfold pairU
  show sepU G (m 0) (m 1) |x 1 + t - (x 0 + t)|
    = sepU G (m 0) (m 1) |x 1 - x 0|
  rw [show x 1 + t - (x 0 + t) = x 1 - x 0 by ring]

/-- **Separation only**: two placements with the same separation
have the same pair energy. -/
theorem pairU_eq_of_sep_eq (G : ℚ) (m x y : Fin 2 → ℚ)
    (h : |x 1 - x 0| = |y 1 - y 0|) : pairU G m x = pairU G m y := by
  unfold pairU
  rw [h]

/-- **The balance point**: the pair's center of mass (the bridge
pin's `centerMass`) lies between the two positions — tonight's
thread made literal: the seat's balance point is the mass-weighted
center, and the pair energy sees only the separation around it. -/
theorem centerMass_pair_between {m x : Fin 2 → ℚ}
    (hm : ∀ i, 0 < m i) (hx : x 0 ≤ x 1) :
    x 0 ≤ CenterBridgePin.centerMass m x
      ∧ CenterBridgePin.centerMass m x ≤ x 1 := by
  have hS : (0 : ℚ) < m 0 + m 1 := add_pos (hm 0) (hm 1)
  have hcm : CenterBridgePin.centerMass m x
      = (m 0 * x 0 + m 1 * x 1) / (m 0 + m 1) := by
    unfold CenterBridgePin.centerMass CenterBridgePin.wCenter
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
  rw [hcm]
  constructor
  · rw [le_div_iff₀ hS]
    nlinarith [mul_le_mul_of_nonneg_left hx (hm 1).le]
  · rw [div_le_iff₀ hS]
    nlinarith [mul_le_mul_of_nonneg_left hx (hm 0).le]

/-! ## Brick 2 — the crowd -/

/-- **Total pair energy**: Newton's pairwise potential summed
over all unordered pairs `i < j` (the filter form over
`Fin n × Fin n` — the disclosed finite form of `Σ_{i<j}`). -/
def totalU (G : ℚ) (m x : Fin n → ℚ) : ℚ :=
  ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
    -G * m p.1 * m p.2 / |x p.2 - x p.1|

/-- **Total translation invariance**: shifting every position by
the same `t` leaves the total pair energy unchanged. -/
theorem totalU_translation (G : ℚ) (m x : Fin n → ℚ) (t : ℚ) :
    totalU G m (fun i => x i + t) = totalU G m x := by
  unfold totalU
  apply Finset.sum_congr rfl
  intro p _
  show -G * m p.1 * m p.2 / |x p.2 + t - (x p.1 + t)|
    = -G * m p.1 * m p.2 / |x p.2 - x p.1|
  rw [show x p.2 + t - (x p.1 + t) = x p.2 - x p.1 by ring]

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **Weighted-center equivariance** (the bridge pin's `wCenter`
algebra): shifting every position by `t` shifts the weighted
center by exactly `t`. -/
theorem wCenter_shift {w x : ι → ℚ} (hw : ∀ i, 0 < w i) (t : ℚ) :
    CenterBridgePin.wCenter w (fun i => x i + t)
      = CenterBridgePin.wCenter w x + t := by
  have hS : (∑ i, w i) ≠ 0 :=
    ne_of_gt (CenterBridgePin.sum_pos_of_pos hw)
  have hnum : (∑ i, w i * (x i + t))
      = (∑ i, w i * x i) + (∑ i, w i) * t := by
    calc (∑ i, w i * (x i + t))
        = ∑ i, (w i * x i + w i * t) :=
          Finset.sum_congr rfl (fun i _ => by ring)
      _ = (∑ i, w i * x i) + ∑ i, w i * t := Finset.sum_add_distrib
      _ = (∑ i, w i * x i) + (∑ i, w i) * t := by rw [Finset.sum_mul]
  unfold CenterBridgePin.wCenter
  show (∑ i, w i * (x i + t)) / (∑ i, w i)
    = (∑ i, w i * x i) / (∑ i, w i) + t
  rw [hnum, add_div, mul_div_cancel_left₀ _ hS]

/-- **Center-of-mass equivariance**: shifting every position by
`t` shifts the center of mass by exactly `t`. -/
theorem centerMass_shift {m x : ι → ℚ} (hm : ∀ i, 0 < m i) (t : ℚ) :
    CenterBridgePin.centerMass m (fun i => x i + t)
      = CenterBridgePin.centerMass m x + t :=
  wCenter_shift hm t

/-- **The crowd is bound**: with at least two sites at pairwise
distinct positions, every pair term is strictly negative and at
least one pair exists, so the total pair energy is strictly
negative. -/
theorem totalU_neg {G : ℚ} {m x : Fin n → ℚ} (hn : 2 ≤ n)
    (hG : 0 < G) (hm : ∀ i, 0 < m i)
    (hdist : ∀ i j, i ≠ j → x i ≠ x j) : totalU G m x < 0 := by
  have hterm : ∀ p ∈ Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2),
      -G * m p.1 * m p.2 / |x p.2 - x p.1| < 0 := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hne : p.1 ≠ p.2 := ne_of_lt hp.2
    have hd : 0 < |x p.2 - x p.1| :=
      abs_pos.mpr (sub_ne_zero.mpr (hdist p.2 p.1 (Ne.symm hne)))
    have hP : 0 < G * m p.1 * m p.2 :=
      mul_pos (mul_pos hG (hm p.1)) (hm p.2)
    have e : -G * m p.1 * m p.2 / |x p.2 - x p.1|
        = -((G * m p.1 * m p.2) / |x p.2 - x p.1|) := by ring
    rw [e, neg_lt_zero]
    exact div_pos hP hd
  have hne : (Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 < p.2)).Nonempty := by
    refine ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by
      rw [Fin.lt_iff_val_lt_val]; exact one_pos⟩
  unfold totalU
  exact Finset.sum_neg hterm hne

/-- **The crowd of two is the pair**: on `Fin 2` the total pair
energy is the pair energy of Brick 1. -/
theorem totalU_fin_two (G : ℚ) (m x : Fin 2 → ℚ) :
    totalU G m x = pairU G m x := by
  have hset : (Finset.univ.filter
        (fun p : Fin 2 × Fin 2 => p.1 < p.2)) = {(0, 1)} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hp
      obtain ⟨a, b⟩ := p
      fin_cases a <;> fin_cases b <;> simp_all
    · intro hp
      rw [hp]
      exact Fin.zero_lt_one
  unfold totalU pairU sepU
  rw [hset, Finset.sum_singleton]

/-! ## Brick 3 — the thermal leg -/

/-- **Separation energy** (real form, for the Gibbs seat): the
pair energy at separation `D j`, as a real number —
`−(G·m₀·m₁)/D j` with the rational data cast to `ℝ`. -/
noncomputable def sepEnergy (G m₀ m₁ : ℚ) (D : Fin k → ℚ)
    (j : Fin k) : ℝ :=
  -(↑(G * m₀ * m₁)) / ↑(D j)

/-- **Attraction along the separations**: at positive masses and
positive `G`, the separation energy is strictly monotone in the
separation — a strictly increasing separation ladder has a
strictly increasing energy ladder. -/
theorem sepEnergy_strictMono {G m₀ m₁ : ℚ} (hG : 0 < G)
    (hm₀ : 0 < m₀) (hm₁ : 0 < m₁) {D : Fin k → ℚ}
    (hDpos : ∀ j, 0 < D j) (hD : StrictMono D) :
    StrictMono (sepEnergy G m₀ m₁ D) := by
  intro a b hab
  have hP : (0 : ℝ) < ↑(G * m₀ * m₁) := by
    exact_mod_cast mul_pos (mul_pos hG hm₀) hm₁
  have hd : (D a : ℝ) < (D b : ℝ) := by exact_mod_cast hD hab
  have hda : (0 : ℝ) < (D a : ℝ) := by exact_mod_cast hDpos a
  have hdb : (0 : ℝ) < (D b : ℝ) := by exact_mod_cast hDpos b
  have hcore : ↑(G * m₀ * m₁) / (D b : ℝ)
      < ↑(G * m₀ * m₁) / (D a : ℝ) := by
    rw [div_lt_div_iff₀ hdb hda]
    exact mul_lt_mul_of_pos_left hd hP
  unfold sepEnergy
  have e : ∀ d : ℚ, -(↑(G * m₀ * m₁)) / (d : ℝ)
      = -((↑(G * m₀ * m₁)) / (d : ℝ)) := fun d => by rw [neg_div]
  rw [e (D a), e (D b), neg_lt_neg_iff]
  exact hcore

/-- **The ground state is the closest approach**: every other
allowed separation has strictly higher energy than the minimal
one — the minimal separation is the unique energy minimiser. -/
theorem sepEnergy_ground_strict {G m₀ m₁ : ℚ} (hG : 0 < G)
    (hm₀ : 0 < m₀) (hm₁ : 0 < m₁) {D : Fin k → ℚ}
    (hDpos : ∀ j, 0 < D j) (hD : StrictMono D) {hk : 0 < k}
    {j : Fin k} (hj : j ≠ ⟨0, hk⟩) :
    sepEnergy G m₀ m₁ D ⟨0, hk⟩ < sepEnergy G m₀ m₁ D j := by
  apply sepEnergy_strictMono hG hm₀ hm₁ hDpos hD
  rw [Fin.lt_iff_val_lt_val]
  show (0 : ℕ) < j.val
  exact Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))

/-- **The gap**: the energy step from the minimal separation to
the next one, `U(D 1) − U(D 0)` — the finite seat's spectral gap
at this ladder. -/
noncomputable def sepGap (G m₀ m₁ : ℚ) (D : Fin k → ℚ) (hk : 2 ≤ k) :
    ℝ :=
  sepEnergy G m₀ m₁ D ⟨1, by omega⟩ - sepEnergy G m₀ m₁ D ⟨0, by omega⟩

/-- **The gap is positive**: the first step up the separation
ladder costs strictly positive energy. -/
theorem sepGap_pos {G m₀ m₁ : ℚ} (hG : 0 < G) (hm₀ : 0 < m₀)
    (hm₁ : 0 < m₁) {D : Fin k → ℚ} (hDpos : ∀ j, 0 < D j)
    (hD : StrictMono D) (hk : 2 ≤ k) : 0 < sepGap G m₀ m₁ D hk := by
  unfold sepGap
  rw [sub_pos]
  exact sepEnergy_ground_strict hG hm₀ hm₁ hDpos hD
    (by
      intro h
      have h2 := congrArg Fin.val h
      change (1 : ℕ) = 0 at h2
      exact one_ne_zero h2)

/-- **COLD COLLAPSE** (the finite shadow of the gravothermal
story, GAPFLOOR shape): for `β ≥ 0`, the Gibbs weight on the
minimal separation is at least `1 − (k−1)·e^{−β·gap}` — cold
concentrates the pair at its closest approach. The gravothermal
catastrophe itself is Register-2 prose and is NOT stated here;
this is its finite shadow, labeled as such. -/
theorem cold_collapse {G m₀ m₁ : ℚ} (hG : 0 < G) (hm₀ : 0 < m₀)
    (hm₁ : 0 < m₁) {D : Fin k → ℚ} (hDpos : ∀ j, 0 < D j)
    (hD : StrictMono D) (hk : 2 ≤ k) {β : ℝ} (hβ : 0 ≤ β) :
    1 - ((k : ℝ) - 1) * Real.exp (-(β * sepGap G m₀ m₁ D hk))
      ≤ ModularVariance.gibbsProb (sepEnergy G m₀ m₁ D) β
          ⟨0, by omega⟩ := by
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  set E := sepEnergy G m₀ m₁ D with hE
  set z : Fin k := ⟨0, by omega⟩ with hz
  have hmono : StrictMono E := sepEnergy_strictMono hG hm₀ hm₁ hDpos hD
  have hgap : sepGap G m₀ m₁ D hk = E ⟨1, by omega⟩ - E z := rfl
  have hstep : ∀ j : Fin k, j ≠ z → E ⟨1, by omega⟩ ≤ E j := by
    intro j hj
    rcases eq_or_ne j ⟨1, by omega⟩ with rfl | hne
    · exact le_rfl
    · have h1j : (⟨1, by omega⟩ : Fin k) < j := by
        rw [Fin.lt_iff_val_lt_val]
        show (1 : ℕ) < j.val
        have hj0 : j ≠ z := hj
        have hval : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
        have hne1 : j.val ≠ 1 := fun h => hne (Fin.ext h)
        omega
      exact (hmono h1j).le
  have hEj : ∀ j : Fin k, j ≠ z → E z + sepGap G m₀ m₁ D hk ≤ E j := by
    intro j hj
    have hs := hstep j hj
    have hgap' : sepGap G m₀ m₁ D hk = E ⟨1, by omega⟩ - E z := hgap
    linarith
  have hZ : Real.exp (-(β * E z)) ≤ ModularVariance.partSum E β := by
    show Real.exp (-(β * E z)) ≤ ∑ i, Real.exp (-(β * E i))
    exact Finset.single_le_sum (f := fun i => Real.exp (-(β * E i)))
      (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ z)
  have hterm : ∀ j ∈ Finset.univ \ {z},
      ModularVariance.gibbsProb E β j
        ≤ Real.exp (-(β * sepGap G m₀ m₁ D hk)) := by
    intro j hj
    rw [Finset.mem_sdiff] at hj
    have hjne : j ≠ z := fun h => hj.2 (Finset.mem_singleton.mpr h)
    have hEj' := hEj j hjne
    unfold ModularVariance.gibbsProb
    rw [div_le_iff₀ (ModularVariance.partSum_pos E β)]
    calc Real.exp (-(β * E j))
        ≤ Real.exp (-(β * sepGap G m₀ m₁ D hk))
            * Real.exp (-(β * E z)) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hmul : β * (E z + sepGap G m₀ m₁ D hk) ≤ β * E j :=
            mul_le_mul_of_nonneg_left hEj' hβ
          linarith
      _ ≤ Real.exp (-(β * sepGap G m₀ m₁ D hk))
            * ModularVariance.partSum E β :=
          mul_le_mul_of_nonneg_left hZ (Real.exp_pos _).le
  have hsum : ∑ j ∈ Finset.univ \ {z}, ModularVariance.gibbsProb E β j
      ≤ ((k : ℝ) - 1) * Real.exp (-(β * sepGap G m₀ m₁ D hk)) := by
    calc ∑ j ∈ Finset.univ \ {z}, ModularVariance.gibbsProb E β j
        ≤ ∑ j ∈ Finset.univ \ {z},
            Real.exp (-(β * sepGap G m₀ m₁ D hk)) :=
          Finset.sum_le_sum hterm
      _ = ((k : ℝ) - 1) * Real.exp (-(β * sepGap G m₀ m₁ D hk)) := by
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
`1/k`. Heat spreads the pair over all its separations evenly. -/
theorem hot_washout {G m₀ m₁ : ℚ} {D : Fin k → ℚ} (hk : 0 < k)
    (j : Fin k) :
    ModularVariance.gibbsProb (sepEnergy G m₀ m₁ D) 0 j
      = 1 / (k : ℝ) := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  unfold ModularVariance.gibbsProb ModularVariance.partSum
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

end ThetLogos.NewtonSeatPin
