import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Metric
import ThetLogos.RLP1PhiLayer

/-!
# ThetLogos.RLP1Stationarity — RL-P1, Brick 2: the stationarity chain
(TW-S1 → TW-U1 → TW-S2 → TW-S3 → TW-S4 → TW-S5)

## STATUS — READ FIRST (the closure is on the face)

This module formalizes, as corpus mathematics, the **stationarity
layer** of the mechanics registered as **RL-P1** (Gate 1
pre-registration v1, frozen 2026-11-05; v2,
`rl-p1-gate1-preregistration-v2-2026-11-05.md`). The theorems here
are the stationarity theorems-in-waiting of the Gate 4 derivation
report (`rl-p1-gate4-derivation-2026-11-05.md`, §1, §3, and §8 item
2), in §8's dependency order: **TW-S1** (stationarity, divided
form) → **TW-U1** (m-independence of the stationary sets; target
(b)) → **TW-S2** (existence) → **TW-S3** (free case = midpoint
condition) → **TW-S4** (balance form) → **TW-S5** (rest criterion).
They build on Brick 1 (`ThetLogos.RLP1PhiLayer`: the seat package
and TW-P1..TW-P7).

**The gravity candidacy of RL-P1 is CLOSED.** At Gate 4 the frozen
shadow test (v2 §2) was run exactly as frozen, in exact rational
arithmetic, and shape agreement failed on both registered cases:
**K-RLP1-SHADOW FIRED.** The recorded verdict (v1 §6, pre-written)
is:

> **RL-P1 is a mechanics, not a gravity candidate.**

Per the registration (P-D2), that kill is final for RL-P1 as
registered; Gates 5–8 do not run on it. This module is built — on
Jeff's explicit decision of 2026-11-05 — **as corpus mechanics
only**, decoupled from any Dial-2 candidacy. There is **no Dial-2
language anywhere in this module**: no statement here is evidence
for, or a step toward, any gravity claim, and no statement here is
a response law. **NO CLAIM; dials 0/4; Dial 2 = 0.**

Register discipline (v1 §1, §2): everything below is **Register A
vocabulary only** — the seat of Brick 1, the step cost
`ι(x', x) = d(x', x)² / (2τ²)`, the action `S`, and the coupling
sum `Φ`. Per rider **R-G2F2** (v2 §3): the minus sign in `Φ` and
the stationarity-as-local-minimization form are **declared
conventions** of the primitive; nothing in this module presents
any lean of the stationary set as derived attraction. Two further
scope facts are part of the registration and are kept on the face:
stationarity (ST) is a **system of inequalities, not an evolution
law** — this module defines stationary *sets* of paths, never a
trajectory, an acceleration, or a response function; and **target
(a) is UNGRADED — DESIGN PENDING** (ODP-RLP1-FRAME): no frame
data, variation class, or Euler-realization content occurs here,
and K-RLP1-EULER is not armed.

## What is here

Paths are functions `x : ℕ → V`; the action at horizon `T` reads
only the values `x 0, …, x T`, exactly as registered
(`S[ρ, m](x) = Σ_{t=0}^{T−1} [ m·ι(x_{t+1}, x_t) + m·Φ(ρ, x_t) ]`).
Stationarity at an interior index `t` is defined in the action
form — no single-site variation at `t` decreases `S` — and TW-S1
proves it is exactly the registered divided form (ST): the
variation of `S` at `t` is `m` times the local expression, whose
`x_t`-dependence is the three terms of Gate 4 §1.1, and `m > 0`
divides out.

- §1: step cost, action, local expression, stationarity.
- §2: the variation computation and **TW-S1**; the homogeneity
  `S[ρ, m] = m · S[ρ, 1]` and **TW-U1**.
- §3: **TW-S2** (a global minimizer of `S` over the finite path
  space is stationary).
- §4: the seat-distance midpoint facts and **TW-S3**. The
  attainment set is stated *exactly*: for even `d(a, b)` the
  midpoint is unique; for odd `d(a, b)` **both** symmetric
  midpoints (distances `⌊d/2⌋, ⌈d/2⌉` in the two orders) attain —
  the registered text names the first of the two.
- §5: **TW-S4** (balance form) and **TW-S5** (rest criterion: at
  an interior index of the constant path; the path-level form
  follows whenever an interior index exists, `2 ≤ T`), with the
  registered sufficient condition (a global minimizer of `Φ`
  rests).

NOT here: **TW-S6** (the rest-start successor exhibit, secondary
and ungraded) is Brick 3, fired separately; target (a) in any form
(see above); any shadow/dictionary object (that was the audit's
comparison standard, closed at Gate 4).

Axiom audit: headline theorems are checked at the end of the file
against the standard three (`propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## §1. Step cost, action, local expression, stationarity -/

/-- The step cost (v1 §2.6): `ι(x', x) = d(x', x)² / (2τ²)`, with
`d` the seat distance of Brick 1. A declared quadratic penalty on
the step `x → x'`; no direction is read into it (R-G2F2). -/
noncomputable def rlp1Iota (s : RLP1Seat V) (τ : ℝ) (x' x : V) : ℝ :=
  (s.dist x' x : ℝ) ^ 2 / (2 * τ ^ 2)

/-- The summand of the action at step `i` for the path `x`:
`m·ι(x_{i+1}, x_i) + m·Φ(ρ, x_i)`. -/
noncomputable def rlp1ActionTerm (s : RLP1Seat V) (q τ m : ℝ)
    (ρ : V → ℝ) (x : ℕ → V) (i : ℕ) : ℝ :=
  m * rlp1Iota s τ (x (i + 1)) (x i) + m * rlp1Phi s q ρ (x i)

/-- The action (v1 §2.6): at background `ρ`, body scalar `m`,
horizon `T`,
`S[ρ, m](x) = Σ_{t=0}^{T−1} [ m·ι(x_{t+1}, x_t) + m·Φ(ρ, x_t) ]`.
Only the values `x 0, …, x T` are read. -/
noncomputable def rlp1Action (s : RLP1Seat V) (q τ m : ℝ) (ρ : V → ℝ)
    (T : ℕ) (x : ℕ → V) : ℝ :=
  ∑ i ∈ Finset.range T, rlp1ActionTerm s q τ m ρ x i

/-- The local expression of (ST) (Gate 4 §1.1): at neighbours
`a = x_{t−1}`, `b = x_{t+1}`, the value at a varied site `u` is
`ι(u, a) + ι(b, u) + Φ(ρ, u)`. This is the `x_t`-dependent part of
the action, with `m` divided out. -/
noncomputable def rlp1LocalExpr (s : RLP1Seat V) (q τ : ℝ) (ρ : V → ℝ)
    (a b u : V) : ℝ :=
  rlp1Iota s τ u a + rlp1Iota s τ b u + rlp1Phi s q ρ u

/-- Stationarity at an interior index `t`, in the action form of
v1 §2.6: no single-site variation at `t` decreases the action.
The endpoints `x₀, x_T` carry no stationarity condition (Gate 3,
G3-F5); interior means `1 ≤ t` and `t < T`. -/
def rlp1StationaryAt (s : RLP1Seat V) (q τ m : ℝ) (ρ : V → ℝ)
    (T : ℕ) (x : ℕ → V) (t : ℕ) : Prop :=
  ∀ z : V, rlp1Action s q τ m ρ T x
    ≤ rlp1Action s q τ m ρ T (Function.update x t z)

/-- A stationary path: (ST)'s action form holds at every interior
index. -/
def rlp1Stationary (s : RLP1Seat V) (q τ m : ℝ) (ρ : V → ℝ)
    (T : ℕ) (x : ℕ → V) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t < T → rlp1StationaryAt s q τ m ρ T x t

/-! ## §2. The variation computation, TW-S1, TW-U1 -/

/-- The variation of the action under a single-site change at an
interior index: only terms `t−1` and `t` of the sum move, and
their total change is `m` times the change of the local
expression. This is Gate 4 §1.1's derivation step, as an
equation. -/
theorem rlp1Action_update (s : RLP1Seat V) (q τ m : ℝ) (ρ : V → ℝ)
    (T : ℕ) (x : ℕ → V) {t : ℕ} (ht1 : 1 ≤ t) (htT : t < T)
    (z : V) :
    rlp1Action s q τ m ρ T (Function.update x t z)
      = rlp1Action s q τ m ρ T x
        + m * (rlp1LocalExpr s q τ ρ (x (t - 1)) (x (t + 1)) z
            - rlp1LocalExpr s q τ ρ (x (t - 1)) (x (t + 1)) (x t)) := by
  have hupd_self : Function.update x t z t = z := Function.update_self ..
  have hupd_ne : ∀ i : ℕ, i ≠ t → Function.update x t z i = x i :=
    fun i hi => Function.update_of_ne hi ..
  have hupd_succ : Function.update x t z (t + 1) = x (t + 1) :=
    hupd_ne _ (by omega)
  have htsub : t - 1 + 1 = t := Nat.sub_add_cancel ht1
  have hterm_t : rlp1ActionTerm s q τ m ρ (Function.update x t z) t
      = m * rlp1Iota s τ (x (t + 1)) z + m * rlp1Phi s q ρ z := by
    unfold rlp1ActionTerm
    rw [hupd_self, hupd_succ]
  have hterm_tm1 : rlp1ActionTerm s q τ m ρ (Function.update x t z)
        (t - 1)
      = m * rlp1Iota s τ z (x (t - 1)) + m * rlp1Phi s q ρ (x (t - 1)) := by
    unfold rlp1ActionTerm
    rw [htsub, hupd_self, hupd_ne _ (by omega)]
  have hterm_same : ∀ i : ℕ, i ≠ t - 1 → i ≠ t →
      rlp1ActionTerm s q τ m ρ (Function.update x t z) i
        = rlp1ActionTerm s q τ m ρ x i := by
    intro i hi1 hi2
    unfold rlp1ActionTerm
    rw [hupd_ne _ hi2, hupd_ne _ (show i + 1 ≠ t by omega)]
  have hdiff : (∑ i ∈ Finset.range T,
        rlp1ActionTerm s q τ m ρ (Function.update x t z) i)
      - (∑ i ∈ Finset.range T, rlp1ActionTerm s q τ m ρ x i)
      = (rlp1ActionTerm s q τ m ρ (Function.update x t z) (t - 1)
          - rlp1ActionTerm s q τ m ρ x (t - 1))
        + (rlp1ActionTerm s q τ m ρ (Function.update x t z) t
          - rlp1ActionTerm s q τ m ρ x t) := by
    rw [← Finset.sum_sub_distrib]
    have hpair : (∑ i ∈ ({t - 1, t} : Finset ℕ),
          (rlp1ActionTerm s q τ m ρ (Function.update x t z) i
            - rlp1ActionTerm s q τ m ρ x i))
        = (rlp1ActionTerm s q τ m ρ (Function.update x t z) (t - 1)
            - rlp1ActionTerm s q τ m ρ x (t - 1))
          + (rlp1ActionTerm s q τ m ρ (Function.update x t z) t
            - rlp1ActionTerm s q τ m ρ x t) :=
      Finset.sum_pair (show t - 1 ≠ t by omega)
    rw [← hpair]
    symm
    apply Finset.sum_subset
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      exact Finset.mem_range.mpr (by rcases hi with rfl | rfl <;> omega)
    · intro i _ hi
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      exact sub_eq_zero.mpr (hterm_same i hi.1 hi.2)
  have hsum' : ∀ (y : ℕ → V), rlp1Action s q τ m ρ T y
        = ∑ i ∈ Finset.range T, (m * rlp1Iota s τ (y (i + 1)) (y i)
            + m * rlp1Phi s q ρ (y i)) :=
    fun y => Finset.sum_congr rfl fun i _ => rfl
  rw [hsum', hsum']
  rw [hterm_t, hterm_tm1] at hdiff
  unfold rlp1ActionTerm at hdiff
  rw [htsub] at hdiff
  unfold rlp1LocalExpr
  linarith [hdiff]

/-- **TW-S1 (stationarity, divided form).** For an interior index
`t`, with `a := x_{t−1}`, `b := x_{t+1}`: `x` is stationary at `t`
for the action `S[ρ, m]` iff (ST) holds —
`ι(z, a) + ι(b, z) + Φ(ρ, z) ≥ ι(x_t, a) + ι(b, x_t) + Φ(ρ, x_t)`
for all `z`. *Proof (Gate 4 §1.1):* the local expression is the
`x_t`-dependent part of `S` (`rlp1Action_update`); `m > 0`
divides out. It is a system of inequalities, not an evolution
law. -/
theorem rlp1StationaryAt_iff (s : RLP1Seat V) (q τ m : ℝ)
    (hm : 0 < m) (ρ : V → ℝ) (T : ℕ) (x : ℕ → V) {t : ℕ}
    (ht1 : 1 ≤ t) (htT : t < T) :
    rlp1StationaryAt s q τ m ρ T x t
      ↔ ∀ z : V, rlp1LocalExpr s q τ ρ (x (t - 1)) (x (t + 1)) (x t)
          ≤ rlp1LocalExpr s q τ ρ (x (t - 1)) (x (t + 1)) z := by
  constructor
  · intro h z
    have hle := h z
    rw [rlp1Action_update s q τ m ρ T x ht1 htT z] at hle
    have hD : 0 ≤ rlp1LocalExpr s q τ ρ (x (t - 1)) (x (t + 1)) z
        - rlp1LocalExpr s q τ ρ (x (t - 1)) (x (t + 1)) (x t) := by
      by_contra hneg
      push_neg at hneg
      have hmul := mul_neg_of_pos_of_neg hm hneg
      linarith
    linarith
  · intro h z
    rw [rlp1Action_update s q τ m ρ T x ht1 htT z]
    have hD : 0 ≤ rlp1LocalExpr s q τ ρ (x (t - 1)) (x (t + 1)) z
        - rlp1LocalExpr s q τ ρ (x (t - 1)) (x (t + 1)) (x t) :=
      sub_nonneg.mpr (h z)
    have hmul : 0 ≤ m * (rlp1LocalExpr s q τ ρ (x (t - 1)) (x (t + 1)) z
        - rlp1LocalExpr s q τ ρ (x (t - 1)) (x (t + 1)) (x t)) :=
      mul_nonneg hm.le hD
    linarith

/-- The action is homogeneous of degree 1 in `m`:
`S[ρ, m] = m · S[ρ, 1]` (both terms of v1 §2.6 carry the single
factor `m`, which occurs nowhere else — Gate 4 §3). -/
theorem rlp1Action_smul_one (s : RLP1Seat V) (q τ m : ℝ) (ρ : V → ℝ)
    (T : ℕ) (x : ℕ → V) :
    rlp1Action s q τ m ρ T x
      = m * rlp1Action s q τ 1 ρ T x := by
  unfold rlp1Action rlp1ActionTerm
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **TW-U1 (target (b)), at one interior index.** Stationarity
at `t` does not depend on the value of `m > 0`: by TW-S1 both
sides are the same divided form (ST), in which `m` does not
occur. -/
theorem rlp1StationaryAt_indep_m (s : RLP1Seat V) (q τ : ℝ)
    (ρ : V → ℝ) (T : ℕ) (x : ℕ → V) {t : ℕ} (ht1 : 1 ≤ t)
    (htT : t < T) {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    rlp1StationaryAt s q τ m₁ ρ T x t
      ↔ rlp1StationaryAt s q τ m₂ ρ T x t := by
  rw [rlp1StationaryAt_iff s q τ m₁ hm₁ ρ T x ht1 htT,
    rlp1StationaryAt_iff s q τ m₂ hm₂ ρ T x ht1 htT]

/-- **TW-U1 (target (b), as registered in v1 §4(b)).** For all
backgrounds `ρ` and all `m₁, m₂ > 0`, the stationary-path sets of
`S[ρ, m₁]` and `S[ρ, m₂]` are equal. Graded at Gate 4 as
discharged on paper for §2 as written, at the weight Gate 3
assigned it (G3-F4): within the registered definitions the
statement cannot fail; its discriminating content is across
candidate space, and K-RLP1-UNIV does not fire. -/
theorem rlp1Stationary_m_indep (s : RLP1Seat V) (q τ : ℝ)
    (ρ : V → ℝ) (T : ℕ) (x : ℕ → V) {m₁ m₂ : ℝ} (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) :
    rlp1Stationary s q τ m₁ ρ T x
      ↔ rlp1Stationary s q τ m₂ ρ T x := by
  constructor
  · intro h t ht1 htT
    exact (rlp1StationaryAt_indep_m s q τ ρ T x ht1 htT hm₁ hm₂).mp
      (h t ht1 htT)
  · intro h t ht1 htT
    exact (rlp1StationaryAt_indep_m s q τ ρ T x ht1 htT hm₁ hm₂).mpr
      (h t ht1 htT)

/-- The action reads only the values `x 0, …, x T`: paths
agreeing on that prefix have the same action. -/
theorem rlp1Action_congr_prefix (s : RLP1Seat V) (q τ m : ℝ)
    (ρ : V → ℝ) (T : ℕ) {x y : ℕ → V}
    (h : ∀ i : ℕ, i ≤ T → x i = y i) :
    rlp1Action s q τ m ρ T x = rlp1Action s q τ m ρ T y := by
  unfold rlp1Action
  apply Finset.sum_congr rfl
  intro i hi
  have hiT : i < T := Finset.mem_range.mp hi
  unfold rlp1ActionTerm
  rw [h i (le_of_lt hiT), h (i + 1) (by omega)]

/-! ## §3. TW-S2 — existence -/

/-- **TW-S2 (existence).** For every `(ρ, m, q, τ, T)` a
stationary path exists. *Proof (Gate 4 §1.2):* the path space
`V^{T+1}` is finite, so `S` attains its minimum at some `x*`;
varying one interior state of `x*` changes `S` only through the
local expression, so `x*` is stationary. (No sign condition on
`m` is needed: a global minimizer of `S` is stationary in the
action form by definition.) -/
theorem rlp1Stationary_exists (s : RLP1Seat V) (q τ m : ℝ)
    (ρ : V → ℝ) (T : ℕ) :
    ∃ x : ℕ → V, rlp1Stationary s q τ m ρ T x := by
  classical
  obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
  obtain ⟨y, -, hy⟩ := Finset.exists_min_image Finset.univ
    (fun y : Fin (T + 1) → V => rlp1Action s q τ m ρ T
      (fun n => if h : n ≤ T then y ⟨n, Nat.lt_succ_of_le h⟩ else v₀))
    Finset.univ_nonempty
  refine ⟨(fun n => if h : n ≤ T then y ⟨n, Nat.lt_succ_of_le h⟩
    else v₀), ?_⟩
  intro t ht1 htT
  have htT' : t ≤ T := le_of_lt htT
  intro z
  have hpre : ∀ i : ℕ, i ≤ T →
      Function.update
          (fun n => if h : n ≤ T then y ⟨n, Nat.lt_succ_of_le h⟩
            else v₀) t z i
        = (fun n => if h : n ≤ T then
            (Function.update y ⟨t, Nat.lt_succ_of_le htT'⟩ z)
              ⟨n, Nat.lt_succ_of_le h⟩ else v₀) i := by
    intro i hi
    by_cases hit : i = t
    · subst hit
      have hup : Function.update
            (fun n => if h : n ≤ T then y ⟨n, Nat.lt_succ_of_le h⟩
              else v₀) i z i = z :=
        @Function.update_self _ _ _ _ _
          (fun n => if h : n ≤ T then y ⟨n, Nat.lt_succ_of_le h⟩
            else v₀)
      rw [hup]
      show z = (if h : i ≤ T then
        (Function.update y ⟨i, Nat.lt_succ_of_le htT'⟩ z)
          ⟨i, Nat.lt_succ_of_le h⟩ else v₀)
      rw [dif_pos hi]
      exact (@Function.update_self _ _ _ _ _ y).symm
    · have hneN : i ≠ t := hit
      rw [Function.update_of_ne hneN]
      show (if h : i ≤ T then y ⟨i, Nat.lt_succ_of_le h⟩ else v₀)
        = (if h : i ≤ T then
          (Function.update y ⟨t, Nat.lt_succ_of_le htT'⟩ z)
            ⟨i, Nat.lt_succ_of_le h⟩ else v₀)
      have hne : (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (T + 1))
          ≠ ⟨t, Nat.lt_succ_of_le htT'⟩ := by
        intro hcon
        exact hneN (Fin.mk.injEq .. ▸ hcon)
      rw [dif_pos hi, dif_pos hi]
      exact (Function.update_of_ne hne z y).symm
  have hact : rlp1Action s q τ m ρ T
        (Function.update
          (fun n => if h : n ≤ T then y ⟨n, Nat.lt_succ_of_le h⟩
            else v₀) t z)
      = rlp1Action s q τ m ρ T
          (fun n => if h : n ≤ T then
            (Function.update y ⟨t, Nat.lt_succ_of_le htT'⟩ z)
              ⟨n, Nat.lt_succ_of_le h⟩ else v₀) :=
    rlp1Action_congr_prefix s q τ m ρ T hpre
  rw [hact]
  exact hy _ (Finset.mem_univ _)

/-! ## §4. Seat-distance midpoint facts and TW-S3 -/

/-- The seat distance is symmetric. -/
theorem rlp1Seat_dist_comm (s : RLP1Seat V) (x y : V) :
    s.dist x y = s.dist y x :=
  SimpleGraph.dist_comm

/-- The seat distance satisfies the triangle inequality (the seat
graph is connected, part of the seat package). -/
theorem rlp1Seat_dist_triangle (s : RLP1Seat V) (x y z : V) :
    s.dist x z ≤ s.dist x y + s.dist y z :=
  s.connected.dist_triangle

/-- One step along a shortest path: from `a` at distance
`n ≥ 1` from `b` there is a graph neighbour at distance
`n − 1` from `b`. -/
theorem rlp1Seat_step (s : RLP1Seat V) {a b : V}
    (h : 1 ≤ s.dist a b) :
    ∃ a' : V, s.graph.Adj a a' ∧ s.dist a' b = s.dist a b - 1 := by
  obtain ⟨p, hp⟩ := s.connected.exists_walk_length_eq_dist a b
  cases p with
  | nil =>
    exfalso
    have hself : s.dist a a = 0 := SimpleGraph.dist_self
    omega
  | cons hadj p' =>
    rename_i a'
    refine ⟨a', hadj, ?_⟩
    have hle : s.dist a' b ≤ p'.length := SimpleGraph.dist_le p'
    have hlen : p'.length + 1 = s.dist a b := by
      have hlc := SimpleGraph.Walk.length_cons hadj p'
      rw [hp] at hlc
      exact hlc.symm
    have htri := rlp1Seat_dist_triangle s a a' b
    have h1 : s.dist a a' = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr hadj
    omega

/-- Every initial segment of a shortest path is realized: for
`k ≤ d(a, b)` there is a site `z` on a shortest `a`–`b` path at
distance `k` from `a`. -/
theorem rlp1Seat_exists_on_shortest (s : RLP1Seat V) (a b : V)
    {k : ℕ} (hk : k ≤ s.dist a b) :
    ∃ z : V, s.dist a z = k
      ∧ s.dist a z + s.dist z b = s.dist a b := by
  induction k generalizing a with
  | zero =>
    have hself : s.dist a a = 0 := SimpleGraph.dist_self
    exact ⟨a, hself, by rw [hself]; exact Nat.zero_add _⟩
  | succ k ih =>
    obtain ⟨a', hadj, hstep⟩ := rlp1Seat_step s (a := a) (b := b)
      (by omega)
    obtain ⟨z, hz1, hz2⟩ := ih (a := a') (by omega)
    have h1 : s.dist a a' = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr hadj
    have htri := rlp1Seat_dist_triangle s a a' z
    have htri' := rlp1Seat_dist_triangle s a' a z
    rw [rlp1Seat_dist_comm s a' a] at htri'
    have htrib := rlp1Seat_dist_triangle s a z b
    refine ⟨z, ?_, ?_⟩ <;> omega

/-- The midpoint value at the canonical split, by parity:
`(⌊n/2⌋)² + (⌈n/2⌉)² = ⌈n²/2⌉`. -/
theorem rlp1_midpoint_sq_value (n : ℕ) :
    (n / 2) ^ 2 + (n - n / 2) ^ 2 = (n ^ 2 + 1) / 2 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have e1 : n / 2 = k := by omega
    have e2 : n - n / 2 = k := by omega
    have e3 : n ^ 2 = 4 * k ^ 2 := by rw [hk]; ring
    rw [e2, e1, e3]; omega
  · have e1 : n / 2 = k := by omega
    have e2 : n - n / 2 = k + 1 := by omega
    have e3 : n ^ 2 = 4 * k ^ 2 + 4 * k + 1 := by rw [hk]; ring
    have e4 : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
    rw [e2, e1, e3, e4]; omega

/-- The midpoint value, lower bound (TW-S3, "moreover", first
half): for every `z`,
`⌈d(a,b)² / 2⌉ ≤ d(z,a)² + d(b,z)²`, where the ceiling of the
rational `d(a,b)² / 2` is the natural `(d(a,b)² + 1) / 2`.
*Proof (Gate 4 §1.2):* with `x = d(z,a)`, `y = d(z,b)`,
`n = d(a,b)`: the triangle inequality gives `x + y ≥ n`, hence
`x² + y² ≥ (x+y)²/2 ≥ n²/2`, and `x² + y²` is an integer. -/
theorem rlp1_midpoint_value_lower (s : RLP1Seat V) (a b z : V) :
    (s.dist a b ^ 2 + 1) / 2 ≤ s.dist z a ^ 2 + s.dist b z ^ 2 := by
  have htri : s.dist a b ≤ s.dist z a + s.dist b z := by
    have h := rlp1Seat_dist_triangle s a z b
    rwa [rlp1Seat_dist_comm s a z, rlp1Seat_dist_comm s z b] at h
  have key : (s.dist a b : ℤ) ^ 2
      ≤ 2 * ((s.dist z a : ℤ) ^ 2 + (s.dist b z : ℤ) ^ 2) := by
    have h1 : (s.dist a b : ℤ)
        ≤ (s.dist z a : ℤ) + s.dist b z := by exact_mod_cast htri
    have h2 : (0 : ℤ) ≤ ((s.dist z a : ℤ) - s.dist b z) ^ 2 :=
      sq_nonneg _
    have h3 : (0 : ℤ) ≤ ((s.dist z a : ℤ) + s.dist b z
          - s.dist a b)
        * ((s.dist z a : ℤ) + s.dist b z + s.dist a b) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith
  have keyN : s.dist a b ^ 2
      ≤ 2 * (s.dist z a ^ 2 + s.dist b z ^ 2) := by
    exact_mod_cast key
  omega

/-- The midpoint value is attained, at the canonical midpoint:
a site `z` on a shortest `a`–`b` path with `d(a,z) = ⌊d(a,b)/2⌋`
and `d(z,b) = ⌈d(a,b)/2⌉` (TW-S3, "moreover", second half). -/
theorem rlp1_exists_midpoint (s : RLP1Seat V) (a b : V) :
    ∃ z : V, s.dist a z = s.dist a b / 2
      ∧ s.dist z b = s.dist a b - s.dist a b / 2
      ∧ s.dist a z + s.dist z b = s.dist a b
      ∧ s.dist z a ^ 2 + s.dist b z ^ 2
        = (s.dist a b ^ 2 + 1) / 2 := by
  obtain ⟨z, hz1, hz2⟩ := rlp1Seat_exists_on_shortest s a b
    (k := s.dist a b / 2) (Nat.div_le_self _ _)
  refine ⟨z, hz1, by omega, hz2, ?_⟩
  have hca : s.dist z a = s.dist a b / 2 := by
    rw [rlp1Seat_dist_comm]; exact hz1
  have hcb : s.dist b z = s.dist a b - s.dist a b / 2 := by
    rw [rlp1Seat_dist_comm]; omega
  rw [hca, hcb]
  exact rlp1_midpoint_sq_value _

/-- The attainment arithmetic, isolated: if `n ≤ u + w` and
`u² + w² = ⌈n²/2⌉`, then `u + w = n` and `{u, w}` is the
canonical split `{⌊n/2⌋, ⌈n/2⌉}`. The key quantity is
`(u − w)² = 2(u² + w²) − (u + w)² ∈ {0, 1}`; the case
`(u + w)² = n² + 1` would force `(u − w)² = 0` and
`(u + w)² = n² + 1` with `n ≤ u + w`, which has no integer
solutions. -/
theorem rlp1_attains_midpoint_arith (u w n : ℕ) (htri : n ≤ u + w)
    (h : u ^ 2 + w ^ 2 = (n ^ 2 + 1) / 2) :
    u + w = n ∧ ((u = n / 2 ∧ w = n - n / 2)
      ∨ (u = n - n / 2 ∧ w = n / 2)) := by
  have hsqZ : ((u : ℤ) + w) ^ 2 ≤ 2 * ((u : ℤ) ^ 2 + (w : ℤ) ^ 2) := by
    nlinarith [sq_nonneg ((u : ℤ) - w)]
  have hsum2 : (n : ℤ) ^ 2 ≤ ((u : ℤ) + w) ^ 2 := by
    have hh := Nat.pow_le_pow_left htri 2
    have h' : ((n ^ 2 : ℕ) : ℤ) ≤ ((u + w) ^ 2 : ℕ) := by
      exact_mod_cast hh
    push_cast at h'
    convert h' using 2 <;> push_cast <;> ring
  have hdiffZ : ((u : ℤ) - w) ^ 2
      = 2 * ((u : ℤ) ^ 2 + (w : ℤ) ^ 2) - ((u : ℤ) + w) ^ 2 := by ring
  have h2 : 2 * (u ^ 2 + w ^ 2) = n ^ 2
      ∨ 2 * (u ^ 2 + w ^ 2) = n ^ 2 + 1 := by omega
  have fromSq : ((u : ℤ) + w) ^ 2 = (n : ℤ) ^ 2 → u + w = n := by
    intro hS
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hS with h1 | h1
    · exact_mod_cast h1
    · have hnn : (0 : ℤ) ≤ (n : ℤ) := by positivity
      have huw : (0 : ℤ) ≤ (u : ℤ) + w := by positivity
      have hSZ : (u : ℤ) + w = n := by linarith
      exact_mod_cast hSZ
  rcases h2 with h2A | h2B
  · have h2Z : 2 * ((u : ℤ) ^ 2 + (w : ℤ) ^ 2) = (n : ℤ) ^ 2 := by
      exact_mod_cast h2A
    have hd : ((u : ℤ) - w) ^ 2 = 0 := by
      nlinarith [sq_nonneg ((u : ℤ) - w)]
    have hS : ((u : ℤ) + w) ^ 2 = (n : ℤ) ^ 2 := by linarith
    have hsum := fromSq hS
    have huw : u = w := by
      have h0 := sq_eq_zero_iff.mp hd
      have h0' : (u : ℤ) = w := by linarith
      exact_mod_cast h0'
    exact ⟨hsum, Or.inl ⟨by omega, by omega⟩⟩
  · have h2Z : 2 * ((u : ℤ) ^ 2 + (w : ℤ) ^ 2)
        = (n : ℤ) ^ 2 + 1 := by exact_mod_cast h2B
    have hS : ((u : ℤ) + w) ^ 2 = (n : ℤ) ^ 2
        ∨ ((u : ℤ) + w) ^ 2 = (n : ℤ) ^ 2 + 1 := by omega
    rcases hS with hSA | hSB
    · have hsum := fromSq hSA
      have hd : ((u : ℤ) - w) ^ 2 = 1 := by linarith
      rcases sq_eq_one_iff.mp hd with h1 | h1
      · have h1Z : (u : ℤ) = (w : ℤ) + 1 := by linarith
        have h1N : u = w + 1 := by exact_mod_cast h1Z
        exact ⟨hsum, Or.inr ⟨by omega, by omega⟩⟩
      · have h1Z : (w : ℤ) = (u : ℤ) + 1 := by linarith
        have h1N : w = u + 1 := by exact_mod_cast h1Z
        exact ⟨hsum, Or.inl ⟨by omega, by omega⟩⟩
    · exfalso
      have hd : ((u : ℤ) - w) ^ 2 = 0 := by linarith
      have huw : (u : ℤ) = w := by
        have h0 := sq_eq_zero_iff.mp hd
        linarith
      have hSn : (n : ℤ) + 1 ≤ (u : ℤ) + w := by
        by_contra hc
        push_neg at hc
        have htriZ : (n : ℤ) ≤ (u : ℤ) + w := by
          exact_mod_cast htri
        have hSeq : (u : ℤ) + w = n := by omega
        rw [hSeq] at hSB
        have hcontra : (n : ℤ) ^ 2 < (n : ℤ) ^ 2 + 1 := lt_add_one _
        rw [← hSB] at hcontra
        exact lt_irrefl _ hcontra
      have hSsq : ((n : ℤ) + 1) ^ 2 ≤ ((u : ℤ) + w) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hSn 2
      have hn0 : (n : ℤ) = 0 := by nlinarith
      rw [hn0] at hSB
      norm_num at hSB
      have hS1 : (u : ℤ) + w = 1 := by
        have hge : (0 : ℤ) ≤ (u : ℤ) + w := by positivity
        nlinarith [sq_nonneg ((u : ℤ) + w - 1)]
      omega

/-- The attainment set, exactly (TW-S3, "moreover", the word
"exactly"): `z` attains the midpoint value iff `z` lies on a
shortest `a`–`b` path and its two distances are `⌊d(a,b)/2⌋` and
`⌈d(a,b)/2⌉`, **in either order**. For even `d(a,b)` the two
orders coincide; for odd `d(a,b)` both orders occur and both
attain — the registered text (Gate 4 §1.2) names only the first
order, and this statement records the full set rather than the
named half. -/
theorem rlp1_attains_midpoint_iff (s : RLP1Seat V) (a b z : V) :
    s.dist z a ^ 2 + s.dist b z ^ 2 = (s.dist a b ^ 2 + 1) / 2
      ↔ s.dist a z + s.dist z b = s.dist a b
        ∧ ((s.dist a z = s.dist a b / 2
              ∧ s.dist z b = s.dist a b - s.dist a b / 2)
            ∨ (s.dist a z = s.dist a b - s.dist a b / 2
              ∧ s.dist z b = s.dist a b / 2)) := by
  have hza : s.dist z a = s.dist a z := rlp1Seat_dist_comm s z a
  have hbz : s.dist b z = s.dist z b := rlp1Seat_dist_comm s b z
  rw [hza, hbz]
  constructor
  · intro h
    exact rlp1_attains_midpoint_arith _ _ _
      (rlp1Seat_dist_triangle s a z b) h
  · rintro ⟨hsum, hdisj⟩
    rcases hdisj with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · rw [h1, h2']
      exact rlp1_midpoint_sq_value _
    · rw [h1, h2', add_comm]
      exact rlp1_midpoint_sq_value _

/-- Φ of the zero background is zero (so `ρ ≡ 0` is a constant-Φ
background, for the free case below). -/
theorem rlp1Phi_zero (s : RLP1Seat V) (q : ℝ) (x : V) :
    rlp1Phi s q 0 x = 0 := by
  simp [rlp1Phi]

/-- **TW-S3 (the free case is a midpoint condition).** If
`Φ(ρ, ·)` is constant (in particular if `ρ ≡ 0`), stationarity
at an interior index `t` is equivalent to: `x_t` minimizes
`z ↦ d(z, a)² + d(b, z)²`, where `a = x_{t−1}`, `b = x_{t+1}`.
The value of that minimum and its attainment set are
`rlp1_midpoint_value_lower`, `rlp1_exists_midpoint`, and
`rlp1_attains_midpoint_iff`. This is the precise content of
"free motion" for the registered mechanics; per R-G2F2 nothing
directional is read into it. -/
theorem rlp1StationaryAt_free_iff (s : RLP1Seat V) (q τ m : ℝ)
    (hm : 0 < m) (hτ : 0 < τ) (ρ : V → ℝ)
    (hΦ : ∀ u v : V, rlp1Phi s q ρ u = rlp1Phi s q ρ v)
    (T : ℕ) (x : ℕ → V) {t : ℕ} (ht1 : 1 ≤ t) (htT : t < T) :
    rlp1StationaryAt s q τ m ρ T x t
      ↔ ∀ z : V, (s.dist (x t) (x (t - 1)) : ℝ) ^ 2
            + (s.dist (x (t + 1)) (x t) : ℝ) ^ 2
          ≤ (s.dist z (x (t - 1)) : ℝ) ^ 2
            + (s.dist (x (t + 1)) z : ℝ) ^ 2 := by
  have hpos : (0 : ℝ) < 2 * τ ^ 2 :=
    mul_pos (by norm_num) (pow_pos hτ 2)
  rw [rlp1StationaryAt_iff s q τ m hm ρ T x ht1 htT]
  constructor
  · intro h z
    have hz := h z
    unfold rlp1LocalExpr rlp1Iota at hz
    rw [hΦ z (x t), ← add_div, ← add_div] at hz
    exact (div_le_div_iff_of_pos_right hpos).mp (by linarith [hz])
  · intro h z
    have hz := h z
    have hdiv : ((s.dist (x t) (x (t - 1)) : ℝ) ^ 2
          + (s.dist (x (t + 1)) (x t) : ℝ) ^ 2) / (2 * τ ^ 2)
        ≤ ((s.dist z (x (t - 1)) : ℝ) ^ 2
          + (s.dist (x (t + 1)) z : ℝ) ^ 2) / (2 * τ ^ 2) :=
      (div_le_div_iff_of_pos_right hpos).mpr hz
    unfold rlp1LocalExpr rlp1Iota
    rw [hΦ z (x t), ← add_div, ← add_div]
    linarith [hdiv]

/-! ## §5. TW-S4 — balance form; TW-S5 — rest criterion -/

/-- **TW-S4 (balance form).** (ST) rearranged: `x_t` is
stationary at an interior index `t` iff for all `z`,
`Φ(ρ, z) − Φ(ρ, x_t) ≥ −(1/(2τ²)) · [ d(z,a)² + d(b,z)²
− d(x_t,a)² − d(b,x_t)² ]`, with `a = x_{t−1}`, `b = x_{t+1}`.
The coupling difference a move must "pay for" is bounded by the
inertial difference, with `τ` the exchange rate. *Proof:*
algebra on (ST) (TW-S1). -/
theorem rlp1StationaryAt_balance (s : RLP1Seat V) (q τ m : ℝ)
    (hm : 0 < m) (hτ : 0 < τ) (ρ : V → ℝ) (T : ℕ) (x : ℕ → V)
    {t : ℕ} (ht1 : 1 ≤ t) (htT : t < T) :
    rlp1StationaryAt s q τ m ρ T x t
      ↔ ∀ z : V, -(1 / (2 * τ ^ 2))
            * ((s.dist z (x (t - 1)) : ℝ) ^ 2
              + (s.dist (x (t + 1)) z : ℝ) ^ 2
              - (s.dist (x t) (x (t - 1)) : ℝ) ^ 2
              - (s.dist (x (t + 1)) (x t) : ℝ) ^ 2)
          ≤ rlp1Phi s q ρ z - rlp1Phi s q ρ (x t) := by
  have hτ0 : τ ≠ 0 := ne_of_gt hτ
  have hid : ∀ X Y : ℝ, X / (2 * τ ^ 2) + Y / (2 * τ ^ 2)
      = (1 / (2 * τ ^ 2)) * (X + Y) := by
    intro X Y
    rw [← add_div, one_div_mul_eq_div]
  have hneg : ∀ P Q : ℝ, -(1 / (2 * τ ^ 2)) * (Q - P)
      = (1 / (2 * τ ^ 2)) * P - (1 / (2 * τ ^ 2)) * Q := by
    intro P Q
    ring
  rw [rlp1StationaryAt_iff s q τ m hm ρ T x ht1 htT]
  constructor
  · intro h z
    have hz := h z
    unfold rlp1LocalExpr rlp1Iota at hz
    rw [hid, hid] at hz
    have e1 : (s.dist z (x (t - 1)) : ℝ) ^ 2
          + (s.dist (x (t + 1)) z : ℝ) ^ 2
          - (s.dist (x t) (x (t - 1)) : ℝ) ^ 2
          - (s.dist (x (t + 1)) (x t) : ℝ) ^ 2
        = ((s.dist z (x (t - 1)) : ℝ) ^ 2
            + (s.dist (x (t + 1)) z : ℝ) ^ 2)
          - ((s.dist (x t) (x (t - 1)) : ℝ) ^ 2
            + (s.dist (x (t + 1)) (x t) : ℝ) ^ 2) := by ring
    rw [e1, hneg]
    linarith [hz]
  · intro h z
    have hz := h z
    have e1 : (s.dist z (x (t - 1)) : ℝ) ^ 2
          + (s.dist (x (t + 1)) z : ℝ) ^ 2
          - (s.dist (x t) (x (t - 1)) : ℝ) ^ 2
          - (s.dist (x (t + 1)) (x t) : ℝ) ^ 2
        = ((s.dist z (x (t - 1)) : ℝ) ^ 2
            + (s.dist (x (t + 1)) z : ℝ) ^ 2)
          - ((s.dist (x t) (x (t - 1)) : ℝ) ^ 2
            + (s.dist (x (t + 1)) (x t) : ℝ) ^ 2) := by ring
    rw [e1, hneg] at hz
    unfold rlp1LocalExpr rlp1Iota
    rw [hid, hid]
    linarith [hz]

/-- **TW-S5 (rest criterion).** At any interior index `t`, the
constant path at `v₀` is stationary at `t` iff for all `z`,
`Φ(ρ, z) − Φ(ρ, v₀) ≥ −d(z, v₀)² / τ²`. *Proof (Gate 4 §1.2):*
at a constant path the local expression is
`m·[ d(z,v₀)²/τ² + Φ(ρ, z) ]`, since
`ι(z, v₀) + ι(v₀, z) = d(z,v₀)²/τ²`. -/
theorem rlp1StationaryAt_const_iff (s : RLP1Seat V) (q τ m : ℝ)
    (hm : 0 < m) (hτ : 0 < τ) (ρ : V → ℝ) (T : ℕ) (v₀ : V)
    {t : ℕ} (ht1 : 1 ≤ t) (htT : t < T) :
    rlp1StationaryAt s q τ m ρ T (fun _ => v₀) t
      ↔ ∀ z : V, -(s.dist z v₀ : ℝ) ^ 2 / τ ^ 2
          ≤ rlp1Phi s q ρ z - rlp1Phi s q ρ v₀ := by
  have hτ0 : τ ≠ 0 := ne_of_gt hτ
  have hloc : ∀ z : V, rlp1LocalExpr s q τ ρ v₀ v₀ z
      = (s.dist z v₀ : ℝ) ^ 2 / τ ^ 2 + rlp1Phi s q ρ z := by
    intro z
    unfold rlp1LocalExpr rlp1Iota
    rw [rlp1Seat_dist_comm s v₀ z]
    field_simp
    ring
  have hloc0 : rlp1LocalExpr s q τ ρ v₀ v₀ v₀
      = rlp1Phi s q ρ v₀ := by
    unfold rlp1LocalExpr rlp1Iota
    rw [show s.dist v₀ v₀ = 0 from SimpleGraph.dist_self]
    simp
  rw [rlp1StationaryAt_iff s q τ m hm ρ T (fun _ => v₀) ht1 htT]
  constructor
  · intro h z
    have hz : rlp1LocalExpr s q τ ρ v₀ v₀ v₀
        ≤ rlp1LocalExpr s q τ ρ v₀ v₀ z := h z
    rw [hloc0, hloc] at hz
    rw [neg_div]
    linarith [hz]
  · intro h z
    have hz := h z
    rw [neg_div] at hz
    have hz' : rlp1LocalExpr s q τ ρ v₀ v₀ v₀
        ≤ rlp1LocalExpr s q τ ρ v₀ v₀ z := by
      rw [hloc0, hloc]
      linarith [hz]
    exact hz'

/-- **TW-S5 (sufficient condition).** If `v₀` is a global
minimizer of `Φ(ρ, ·)`, the constant path at `v₀` rests
(stationary at every interior index): the `Φ`-deficit is
everywhere `≥ 0 ≥ −d(z, v₀)²/τ²`. Sufficient, not necessary
(Gate 4 §1.2): a site whose `Φ`-deficit is everywhere smaller
than the inertial penalty also rests, by
`rlp1StationaryAt_const_iff`. -/
theorem rlp1StationaryAt_const_of_phi_min (s : RLP1Seat V)
    (q τ m : ℝ) (hm : 0 < m) (hτ : 0 < τ) (ρ : V → ℝ) (T : ℕ)
    (v₀ : V) (hmin : ∀ z : V, rlp1Phi s q ρ v₀ ≤ rlp1Phi s q ρ z)
    {t : ℕ} (ht1 : 1 ≤ t) (htT : t < T) :
    rlp1StationaryAt s q τ m ρ T (fun _ => v₀) t := by
  rw [rlp1StationaryAt_const_iff s q τ m hm hτ ρ T v₀ ht1 htT]
  intro z
  have h1 : rlp1Phi s q ρ v₀ ≤ rlp1Phi s q ρ z := hmin z
  have h2 : (0 : ℝ) ≤ (s.dist z v₀ : ℝ) ^ 2 / τ ^ 2 :=
    div_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [neg_div]
  linarith [h1, h2]

/-- **TW-S5 (rest criterion, path level).** When an interior
index exists (`2 ≤ T`), the constant path at `v₀` is stationary
as a path iff the rest condition holds at every `z`. (Without
an interior index the path condition is vacuous; the registered
statement is the interior-index form
`rlp1StationaryAt_const_iff`, of which this is the path-level
reading.) -/
theorem rlp1Stationary_const_iff (s : RLP1Seat V) (q τ m : ℝ)
    (hm : 0 < m) (hτ : 0 < τ) (ρ : V → ℝ) (T : ℕ) (hT : 2 ≤ T)
    (v₀ : V) :
    rlp1Stationary s q τ m ρ T (fun _ => v₀)
      ↔ ∀ z : V, -(s.dist z v₀ : ℝ) ^ 2 / τ ^ 2
          ≤ rlp1Phi s q ρ z - rlp1Phi s q ρ v₀ := by
  constructor
  · intro h
    exact (rlp1StationaryAt_const_iff s q τ m hm hτ ρ T v₀
      (t := 1) le_rfl (by omega)).mp (h 1 le_rfl (by omega))
  · intro h t ht1 htT
    exact (rlp1StationaryAt_const_iff s q τ m hm hτ ρ T v₀
      ht1 htT).mpr h

/-! ## Axiom audit (headline theorems)

Expected: exactly the standard three (`propext`,
`Classical.choice`, `Quot.sound`) for every headline below. -/

#print axioms rlp1Action_update
#print axioms rlp1StationaryAt_iff
#print axioms rlp1Stationary_m_indep
#print axioms rlp1Stationary_exists
#print axioms rlp1_midpoint_value_lower
#print axioms rlp1_exists_midpoint
#print axioms rlp1_attains_midpoint_iff
#print axioms rlp1StationaryAt_free_iff
#print axioms rlp1StationaryAt_balance
#print axioms rlp1StationaryAt_const_iff
#print axioms rlp1Stationary_const_iff

end ThetLogos
