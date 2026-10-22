import Mathlib.Tactic

namespace ThetLogos
namespace DiscreteLangevin

/-!
# Discrete Langevin brick: Stokes–Einstein Rung 1 (T1 target, finite level)

Charter: `whitepaper/stokes-einstein-scoping-DRAFT-2026-10-18.md`, §5 Rung 1,
launched on Jeff's word 2026-10-22. Status of the direction: NO CLAIM beyond
the exact finite identities proved below.

THE MODEL. One particle, discrete time, the damped kicked walker

  `v ← a·v + F + ξ`,

in the smallest finite combinatorial model that carries it: at each step the
kick `ξ` is drawn from the two-point law `±σ` (mean `0`, second moment `σ²`,
exactly), and a path of length `n` is a function `p : Fin n → Bool` choosing
the kick signs, summed over with the uniform counting measure — the corpus's
house pattern for finite expectations (cf. the path sums of the finite walk
bricks). Every probabilistic hypothesis the moment theorems need — mean zero,
variance `σ²`, distinct kicks uncorrelated — is not assumed: in this finite
model it is *computed* from the path sums (Lemmas S0/S2 below are the whole
content of "independent mean-zero kicks of variance σ²" here).

Two processes are built.

* `vel a F σ v0 n p`: the walker started from the deterministic velocity
  `v0`. Its coordinates are listed in reverse chronological order
  (`p k` is the kick applied `k` steps before the present), which makes the
  head-peeling recurrence on paths *be* the Langevin update:
  `vel (n+1) (cons b q) = a * vel n q + F + σ * sgn b` (proved below).
  From its closed form: the mean after `n` steps and the exact variance
  `σ² · ∑_{j<n} (a²)^j`, with the variance recurrence
  `Var(n+1) = a² · Var(n) + σ²` and, for `a² ≠ 1`, the closed form
  `σ² · (1 − (a²)ⁿ) / (1 − a²)`.

* `velS a F σ w t p`: the stationary-start walker on the horizon space
  `Fin (N+1) → Bool`. Coordinate `0` carries the sign of the initial
  velocity `v₀ = m* + w · sgn`, coordinate `j+1` carries kick `j`. Its
  fluctuation is a finite mode expansion over the coordinates, and the
  path-sum orthogonality (S2) computes the covariance kernel exactly:
  for `s ≤ t ≤ N`, `E[(v_s − m*)(v_t − m*)] = a^(t−s) · V`, under the
  two hypotheses carried on the face: `w² = V` and the
  fluctuation–dissipation balance `σ² = (1 − a²) · V`.

HEADLINE IDENTITIES.

1. Stationary velocity variance: `V` with `a² · V + σ² = V`, i.e.
   `V = σ² / (1 − a²)` (`statVar_fixed`); in the stationary-start model
   `Var(v_t) = V` at every time `t` (`velS_var`).
2. Mobility: stationary mean velocity is `m* = F / (1 − a) = μ · F` with
   `μ := (1 − a)⁻¹` (`mstar_eq_mobility`, `velS_mean`,
   `velMean_stationary`).
3. Position variance (stationary regime, displacement over `N` steps):
   `E[(x_N − x_0 − N·m*)²] = N · σ²/(1−a)² − 2aV(1 − a^N)/(1−a)²`
   (`posVar_stationary`) — the growth is exactly linear with rate
   `σ²/(1−a)²` plus an explicit bounded correction; the per-step
   increment is `σ²/(1−a)² − 2V·a^(N+1)/(1−a)` (`posVar_increment`).
4. Einstein form: with the noise temperature *defined* by the
   fluctuation–dissipation balance, `Θ := σ² / (2(1−a))`, and the
   diffusivity pinned by the 1D convention (displacement variance grows
   as `2D` per step), `D := σ² / (2(1−a)²)`, the identity
   `D = μ · Θ` holds exactly (`einstein`), and `2 · D = σ²/(1−a)²` is
   the rate appearing in (3) (`two_mul_diffusivity`).

FENCES (charter §6, binding):

* K1: `Θ` is this model's noise temperature — a *defined ratio*
  `σ² / (2(1−a))`. It is not thermodynamic `k_B T`, and nothing here
  derives a thermodynamic temperature.
* K2: no ultrametric anything. The substrate is a finite path space.
* K3: `DiffusionDefect` is NOT imported and nothing here rests on it.
  The MSD-shaped law in (3) is derived from the Langevin update in
  this model, not cited from the walk brick.
* K4: no continuum statement: no Brownian motion, no diffusion
  equation, no Stokes drag `1/(6πηr)`. Discrete time, one particle,
  finite identities only.
-/

/-! ## Sign machinery on kick paths -/

/-- The sign of a Boolean kick: `+1` or `-1`, as a real number. -/
def sgnB (b : Bool) : ℝ := if b then 1 else -1

/-- The sign carried by coordinate `i` of a kick path `p`. -/
def sgn {M : ℕ} (p : Fin M → Bool) (i : Fin M) : ℝ := sgnB (p i)

theorem sgnB_self_mul (b : Bool) : sgnB b * sgnB b = 1 := by
  cases b <;> simp [sgnB]

theorem sum_sgnB : ∑ b : Bool, sgnB b = 0 := by
  rw [Fintype.sum_bool]
  simp [sgnB]

/-- The number of paths of length `M` is `2^M`. -/
theorem card_bool_paths (M : ℕ) : Fintype.card (Fin M → Bool) = 2 ^ M := by
  simp

/-- Summing over all paths of length `n + 1` splits into a sum over the
first (most recent) kick and a sum over all tails of length `n`. -/
theorem sum_bool_paths_succ {α : Type*} [AddCommMonoid α] {n : ℕ}
    (F : (Fin (n + 1) → Bool) → α) :
    (∑ p, F p) = ∑ b : Bool, ∑ q : Fin n → Bool, F (Fin.cons b q) := by
  have hbij : Function.Bijective
      (fun x : Bool × (Fin n → Bool) => (Fin.cons x.1 x.2 : Fin (n + 1) → Bool)) := by
    apply Function.bijective_iff_has_inverse.mpr
    refine ⟨fun p => (p 0, fun i => p (Fin.succ i)), ?_, ?_⟩
    · intro ⟨b, q⟩
      simp only [Fin.cons_zero, Fin.cons_succ]
    · intro p
      show Fin.cons (p 0) (Fin.tail p) = p
      exact Fin.cons_self_tail p
  have hprod : (∑ x : Bool × (Fin n → Bool), F (Fin.cons x.1 x.2))
      = ∑ b : Bool, ∑ q : Fin n → Bool, F (Fin.cons b q) :=
    Fintype.sum_prod_type _
  rw [← hprod]
  exact (Fintype.sum_bijective _ hbij (fun x => F (Fin.cons x.1 x.2)) F
    fun _ => rfl).symm

theorem sgn_cons_zero {n : ℕ} (b : Bool) (q : Fin n → Bool) :
    sgn (Fin.cons b q) 0 = sgnB b := by
  simp [sgn]

theorem sgn_cons_succ {n : ℕ} (b : Bool) (q : Fin n → Bool) (i : Fin n) :
    sgn (Fin.cons b q) (Fin.succ i) = sgn q i := by
  simp [sgn]

/-- **Lemma S0 (mean zero).** Summed over all paths, any single kick
coordinate cancels exactly. This is the finite content of
"the kicks have mean zero". -/
theorem sum_sgn : ∀ {M : ℕ} (i : Fin M), ∑ p : Fin M → Bool, sgn p i = 0 := by
  intro M
  induction M with
  | zero => intro i; exact Fin.elim0 i
  | succ M ih =>
      intro i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · rw [sum_bool_paths_succ]
        simp_rw [sgn_cons_zero, Finset.sum_const, Finset.card_univ,
          card_bool_paths, nsmul_eq_mul, ← Finset.mul_sum, sum_sgnB,
          mul_zero]
      · rw [sum_bool_paths_succ]
        simp_rw [sgn_cons_succ, ih i', Finset.sum_const_zero]

/-- **Lemma S2 (orthogonality).** Summed over all paths, two kick
coordinates are exactly orthogonal unless they coincide, in which case
the sum is the path count `2^M`. This is the finite content of
"distinct kicks are uncorrelated, each of variance `σ²`" (after the
`σ` scaling in the processes below). -/
theorem sum_sgn_mul_sgn : ∀ {M : ℕ} (i j : Fin M),
    ∑ p : Fin M → Bool, sgn p i * sgn p j
      = if i = j then (2 : ℝ) ^ M else 0 := by
  intro M
  induction M with
  | zero => intro i; exact Fin.elim0 i
  | succ M ih =>
      intro i j
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · -- i = j = 0: every summand is (sgn b)^2 = 1
        rw [sum_bool_paths_succ]
        simp_rw [sgn_cons_zero, sgnB_self_mul, Finset.sum_const,
          Finset.card_univ, card_bool_paths, Fintype.card_bool,
          nsmul_eq_mul]
        rw [if_true]
        push_cast
        rw [pow_succ]
        ring
      · -- i = 0, j = succ j': the head sign factors out and cancels
        rw [sum_bool_paths_succ]
        simp only [sgn_cons_zero, sgn_cons_succ]
        rw [← Finset.sum_mul_sum, sum_sgnB, zero_mul]
        exact (if_neg (Fin.succ_ne_zero j').symm).symm
      · -- i = succ i', j = 0: symmetric
        rw [sum_bool_paths_succ]
        have hcomm : ∀ (b : Bool) (q : Fin M → Bool),
            sgn (Fin.cons b q) (Fin.succ i') * sgn (Fin.cons b q) 0
              = sgnB b * sgn q i' := by
          intro b q
          rw [sgn_cons_zero, sgn_cons_succ, mul_comm]
        simp only [hcomm]
        rw [← Finset.sum_mul_sum, sum_sgnB, zero_mul]
        exact (if_neg (Fin.succ_ne_zero i')).symm
      · -- both succ: factor 2 out of the head sum, use the induction
        rw [sum_bool_paths_succ]
        simp_rw [sgn_cons_succ, ih i' j', Finset.sum_const,
          Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
        push_cast
        by_cases h : i' = j'
        · subst h
          rw [if_pos rfl, if_pos rfl, pow_succ]
          ring
        · have hne : Fin.succ i' ≠ Fin.succ j' := fun hh => h (Fin.succ_inj.mp hh)
          rw [if_neg h, if_neg hne]
          ring

/-! ## Expectation on path space and the mode-expansion master lemmas -/

/-- Expectation over the uniform measure on paths of length `M`:
the path sum divided by the path count `2^M`. -/
noncomputable def expct {M : ℕ} (f : (Fin M → Bool) → ℝ) : ℝ :=
  ((2 : ℝ) ^ M)⁻¹ * ∑ p, f p

/-- **Master lemma, mean form.** A constant plus a finite mode
expansion over kick coordinates has expectation exactly the constant:
every mode has mean zero (Lemma S0). -/
theorem expct_const_add_modexpand {M : ℕ} (r : ℝ) (c : Fin M → ℝ) :
    expct (fun p => r + ∑ i, c i * sgn p i) = r := by
  have h2 : (2 : ℝ) ^ M ≠ 0 := pow_ne_zero _ (by norm_num)
  unfold expct
  rw [Finset.sum_add_distrib]
  have hmodes : ∑ p : Fin M → Bool, (∑ i, c i * sgn p i) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    rw [← Finset.mul_sum, sum_sgn, mul_zero]
  have hconst : ∑ _p : Fin M → Bool, r = (2 : ℝ) ^ M * r := by
    rw [Finset.sum_const, Finset.card_univ, card_bool_paths, nsmul_eq_mul]
    push_cast
    ring
  rw [hmodes, hconst, add_zero, inv_mul_cancel_left₀ h2]

/-- **Master lemma, bilinear form.** Two finite mode expansions over
the same kick coordinates have expected product exactly the inner
product of their coefficient vectors: distinct modes are orthogonal
and each mode has unit second moment (Lemma S2). -/
theorem expct_modexpand_mul {M : ℕ} (c d : Fin M → ℝ) :
    expct (fun p => (∑ i, c i * sgn p i) * (∑ i, d i * sgn p i))
      = ∑ i, c i * d i := by
  have h2 : (2 : ℝ) ^ M ≠ 0 := pow_ne_zero _ (by norm_num)
  have pt : ∀ p : Fin M → Bool,
      (∑ i, c i * sgn p i) * (∑ j, d j * sgn p j)
        = ∑ i, ∑ j, (c i * d j) * (sgn p i * sgn p j) := by
    intro p
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  unfold expct
  simp_rw [pt]
  rw [Finset.sum_comm]
  have step1 : ∀ i : Fin M,
      (∑ p : Fin M → Bool, ∑ j, (c i * d j) * (sgn p i * sgn p j))
        = (c i * d i) * (2 : ℝ) ^ M := by
    intro i
    rw [Finset.sum_comm]
    have step2 : ∀ j : Fin M,
        (∑ p : Fin M → Bool, (c i * d j) * (sgn p i * sgn p j))
          = if i = j then (c i * d j) * (2 : ℝ) ^ M else 0 := by
      intro j
      rw [← Finset.mul_sum, sum_sgn_mul_sgn]
      by_cases h : i = j
      · subst h; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [Finset.sum_congr rfl (fun j _ => step2 j), Finset.sum_ite_eq]
    simp
  rw [Finset.sum_congr rfl (fun i _ => step1 i)]
  rw [← Finset.sum_mul]
  rw [mul_comm ((2 : ℝ) ^ M)⁻¹]
  rw [mul_assoc]
  rw [mul_inv_cancel₀ h2]
  rw [mul_one]

/-- **Master lemma, variance form** (the bilinear lemma at `d = c`). -/
theorem expct_modexpand_sq {M : ℕ} (c : Fin M → ℝ) :
    expct (fun p => (∑ i, c i * sgn p i) ^ 2) = ∑ i, (c i) ^ 2 := by
  have h := expct_modexpand_mul c c
  simp_rw [pow_two] at h ⊢
  rw [h]

/-! ## The plain-start walker -/

/-- The geometric-sum recurrence: `∑_{j<n+1} a^j = 1 + a · ∑_{j<n} a^j`. -/
theorem geom_succ (a : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), a ^ j)
      = 1 + a * (∑ j ∈ Finset.range n, a ^ j) := by
  have h1 : (∑ j ∈ Finset.range n, a ^ (j + 1))
      = a * (∑ j ∈ Finset.range n, a ^ j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => pow_succ' a j
  rw [Finset.sum_range_succ', h1, pow_zero]
  ring

/-- Mean velocity of the plain-start walker after `n` steps: the
deterministic part of the closed form. -/
def velMean (a F v0 : ℝ) (n : ℕ) : ℝ :=
  a ^ n * v0 + F * (∑ j ∈ Finset.range n, a ^ j)

/-- The plain-start Langevin walker: velocity after `n` steps on the
path space `Fin n → Bool`, in closed form. Coordinate `k` is the kick
applied `k` steps before the present (reverse chronological order), so
it has been damped `k` times and enters as `a^k · σ · sgn`. -/
def vel (a F σ v0 : ℝ) (n : ℕ) (p : Fin n → Bool) : ℝ :=
  velMean a F v0 n + ∑ k : Fin n, (a ^ k.val * σ) * sgn p k

/-- **The update rule, as a path recurrence.** Peeling the most recent
kick (the head of the path) gives exactly `v ← a·v + F + ξ`: the
closed form *is* the Langevin dynamics, not an ansatz fitted to it. -/
theorem vel_succ_cons (a F σ v0 : ℝ) (n : ℕ) (b : Bool) (q : Fin n → Bool) :
    vel a F σ v0 (n + 1) (Fin.cons b q)
      = a * vel a F σ v0 n q + F + σ * sgnB b := by
  have hmodes : (∑ k : Fin (n + 1), (a ^ k.val * σ) * sgn (Fin.cons b q) k)
      = σ * sgnB b + a * (∑ k : Fin n, (a ^ k.val * σ) * sgn q k) := by
    rw [Fin.sum_univ_succ]
    have hsucc : ∀ k : Fin n,
        (a ^ (Fin.succ k).val * σ) * sgn (Fin.cons b q) (Fin.succ k)
          = a * ((a ^ k.val * σ) * sgn q k) := by
      intro k
      rw [sgn_cons_succ]
      have hv : (Fin.succ k).val = k.val + 1 := rfl
      rw [hv, pow_succ]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hsucc k), ← Finset.mul_sum]
    have h0 : (a ^ (0 : Fin (n + 1)).val * σ) * sgn (Fin.cons b q) 0
        = σ * sgnB b := by
      rw [sgn_cons_zero]
      simp
    rw [h0]
  unfold vel velMean
  rw [hmodes, geom_succ]
  ring

/-- **Mean of the plain-start walker** (Target 2, transient form):
the expected velocity after `n` steps is exactly the closed-form
mean `a^n·v₀ + F·∑_{j<n} a^j`. -/
theorem expct_vel (a F σ v0 : ℝ) (n : ℕ) :
    expct (vel a F σ v0 n) = velMean a F v0 n := by
  show expct (fun p => velMean a F v0 n
    + ∑ k : Fin n, (a ^ k.val * σ) * sgn p k) = velMean a F v0 n
  exact expct_const_add_modexpand _ _

/-- **Mean recurrence**: `M(n+1) = a·M(n) + F`. -/
theorem velMean_succ (a F v0 : ℝ) (n : ℕ) :
    velMean a F v0 (n + 1) = a * velMean a F v0 n + F := by
  unfold velMean
  rw [geom_succ, pow_succ]
  ring

/-- Exact variance of the plain-start walker after `n` steps:
`σ² · ∑_{j<n} (a²)^j` (Target 1, transient form). -/
def velVar (a σ : ℝ) (n : ℕ) : ℝ :=
  σ ^ 2 * (∑ j ∈ Finset.range n, (a ^ 2) ^ j)

theorem pow_term (a σ : ℝ) (j : ℕ) :
    (a ^ j * σ) ^ 2 = σ ^ 2 * (a ^ 2) ^ j := by
  rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm j 2, mul_comm (σ ^ 2)]

/-- **Variance of the plain-start walker**: the expected squared
deviation from the mean is exactly `velVar`. -/
theorem expct_vel_sub_sq (a F σ v0 : ℝ) (n : ℕ) :
    expct (fun p => (vel a F σ v0 n p - velMean a F v0 n) ^ 2)
      = velVar a σ n := by
  have hsub : ∀ p : Fin n → Bool, vel a F σ v0 n p - velMean a F v0 n
      = ∑ k : Fin n, (a ^ k.val * σ) * sgn p k := by
    intro p
    unfold vel
    rw [add_sub_cancel_left]
  simp_rw [hsub]
  rw [expct_modexpand_sq]
  rw [Fin.sum_univ_eq_sum_range (fun j => (a ^ j * σ) ^ 2) n]
  unfold velVar
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => pow_term a σ j

/-- **Variance recurrence**: `Var(n+1) = a²·Var(n) + σ²`. The
stationary variance is its constant solution. -/
theorem velVar_succ (a σ : ℝ) (n : ℕ) :
    velVar a σ (n + 1) = a ^ 2 * velVar a σ n + σ ^ 2 := by
  unfold velVar
  rw [geom_succ (a ^ 2) n]
  ring

/-- **Variance, closed form** (for `a² ≠ 1`):
`Var(n) = σ² · (1 − (a²)ⁿ) / (1 − a²)`. At the fixed point this reads
`σ² / (1 − a²)` — the stationary variance of Target 1. -/
theorem velVar_eq_div (a σ : ℝ) (ha2 : a ^ 2 ≠ 1) (n : ℕ) :
    velVar a σ n = σ ^ 2 * (1 - (a ^ 2) ^ n) / (1 - a ^ 2) := by
  have h1 : (a ^ 2 : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr ha2
  have h2 : (1 : ℝ) - a ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm ha2)
  unfold velVar
  rw [geom_sum_eq ha2 n]
  field_simp
  ring

/-- The stationary variance `σ² / (1 − a²)`. -/
noncomputable def statVar (a σ : ℝ) : ℝ := σ ^ 2 / (1 - a ^ 2)

/-- **Target 1, algebraic form**: the stationary variance is the
constant solution of the variance recurrence,
`a² · V + σ² = V` with `V = σ² / (1 − a²)`. -/
theorem statVar_fixed (a σ : ℝ) (ha2 : a ^ 2 ≠ 1) :
    a ^ 2 * statVar a σ + σ ^ 2 = statVar a σ := by
  have h1 : (1 : ℝ) - a ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm ha2)
  unfold statVar
  field_simp
  ring

/-- The stationary mean velocity `F / (1 − a)`. -/
noncomputable def mstar (a F : ℝ) : ℝ := F / (1 - a)

/-- Mobility `μ := 1 / (1 − a)`. -/
noncomputable def mobility (a : ℝ) : ℝ := (1 - a)⁻¹

/-- The stationary mean is the constant solution of the mean
recurrence: `a·m* + F = m*`. -/
theorem mstar_fixed (a F : ℝ) (ha : a ≠ 1) :
    a * mstar a F + F = mstar a F := by
  have h1 : (1 : ℝ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  unfold mstar
  field_simp
  ring

/-- **Target 2, stationary form (definition level)**: the stationary
mean velocity is mobility times force, `m* = μ · F`. -/
theorem mstar_eq_mobility (a F : ℝ) : mstar a F = mobility a * F := by
  unfold mstar mobility
  rw [div_eq_mul_inv, mul_comm]

/-- **Target 2, stationary form (process level)**: started at the
stationary mean, the plain walker's expected velocity stays there
at every step. -/
theorem expct_vel_stationary (a F σ : ℝ) (ha : a ≠ 1) (n : ℕ) :
    expct (vel a F σ (mstar a F) n) = mstar a F := by
  rw [expct_vel]
  induction n with
  | zero => simp [velMean]
  | succ n ih =>
      rw [velMean_succ, ih]
      exact mstar_fixed a F ha

/-! ## The stationary-start walker -/

/-- Mode coefficient of the stationary-start walker's fluctuation at
time `t`, coordinate `c` of the horizon space `Fin (N+1) → Bool`:
coordinate `0` carries the initial fluctuation `a^t · w`; coordinate
`j+1` carries kick `j`, damped `a^(t−1−j)` once time has passed it,
and `0` before it occurs. -/
def modeCoeff {N : ℕ} (a σ w : ℝ) (t : ℕ) (c : Fin (N + 1)) : ℝ :=
  if c.val = 0 then a ^ t * w
  else if c.val ≤ t then a ^ (t - c.val) * σ
  else 0

theorem modeCoeff_zero {N : ℕ} (a σ w : ℝ) (t : ℕ) (c : Fin (N + 1))
    (hc : c.val = 0) : modeCoeff a σ w t c = a ^ t * w := by
  unfold modeCoeff
  rw [if_pos hc]

theorem modeCoeff_succ_of_le {N : ℕ} (a σ w : ℝ) (t : ℕ) (c : Fin (N + 1))
    (h0 : c.val ≠ 0) (hle : c.val ≤ t) :
    modeCoeff a σ w t c = a ^ (t - c.val) * σ := by
  unfold modeCoeff
  rw [if_neg h0, if_pos hle]

theorem modeCoeff_succ_of_gt {N : ℕ} (a σ w : ℝ) (t : ℕ) (c : Fin (N + 1))
    (h0 : c.val ≠ 0) (hgt : ¬ c.val ≤ t) : modeCoeff a σ w t c = 0 := by
  unfold modeCoeff
  rw [if_neg h0, if_neg hgt]

/-- The stationary-start Langevin walker: velocity at time `t` on the
horizon path space `Fin (N+1) → Bool`, started at
`v₀ = m* + w · sgn p 0` (the stationary mean plus a fluctuation of
size `w` carried by coordinate `0`) and kicked by coordinates
`1, 2, …`. Defined by its exact closed form: the stationary mean plus
a finite mode expansion over the coordinates. -/
noncomputable def velS {N : ℕ} (a F σ w : ℝ) (t : ℕ) (p : Fin (N + 1) → Bool) : ℝ :=
  mstar a F + ∑ c : Fin (N + 1), modeCoeff a σ w t c * sgn p c

/-- **The update rule for the stationary-start walker.** One more
step is exactly `v ← a·v + F + ξ`, with the fresh kick read off the
next coordinate. -/
theorem velS_succ {N : ℕ} (a F σ w : ℝ) (ha : a ≠ 1) {t : ℕ} (ht : t < N)
    (p : Fin (N + 1) → Bool) :
    velS a F σ w (t + 1) p
      = a * velS a F σ w t p + F
        + σ * sgn p ⟨t + 1, Nat.succ_lt_succ ht⟩ := by
  set c0 : Fin (N + 1) := ⟨t + 1, Nat.succ_lt_succ ht⟩ with hc0
  have hval0 : c0.val = t + 1 := rfl
  have hcoeff : ∀ c : Fin (N + 1), c ≠ c0 →
      modeCoeff a σ w (t + 1) c = a * modeCoeff a σ w t c := by
    intro c hc
    have hval : c.val ≠ t + 1 := fun h => hc (Fin.ext (by rw [h, hval0]))
    by_cases h0 : c.val = 0
    · rw [modeCoeff_zero _ _ _ _ _ h0, modeCoeff_zero _ _ _ _ _ h0, pow_succ']
      ring
    · by_cases hle : c.val ≤ t
      · have hle1 : c.val ≤ t + 1 := le_trans hle (Nat.le_succ t)
        have hexp : t + 1 - c.val = (t - c.val) + 1 := by omega
        rw [modeCoeff_succ_of_le _ _ _ _ _ h0 hle1,
          modeCoeff_succ_of_le _ _ _ _ _ h0 hle, hexp, pow_succ]
        ring
      · have hgt : ¬ c.val ≤ t + 1 := by
          have h1 : t < c.val := Nat.lt_of_not_ge hle
          intro hle1
          exact hval (by omega)
        rw [modeCoeff_succ_of_gt _ _ _ _ _ h0 hgt,
          modeCoeff_succ_of_gt _ _ _ _ _ h0 hle, mul_zero]
  have hT0 : modeCoeff a σ w t c0 = 0 := by
    apply modeCoeff_succ_of_gt
    · rw [hval0]; exact Nat.succ_ne_zero t
    · rw [hval0]; omega
  have hT1 : modeCoeff a σ w (t + 1) c0 = σ := by
    have h0 : c0.val ≠ 0 := by rw [hval0]; exact Nat.succ_ne_zero t
    have hle : c0.val ≤ t + 1 := by rw [hval0]
    rw [modeCoeff_succ_of_le _ _ _ _ _ h0 hle, hval0, tsub_self, pow_zero,
      one_mul]
  have hsum : ∀ u : ℕ, (∑ c : Fin (N + 1), modeCoeff a σ w u c * sgn p c)
      = modeCoeff a σ w u c0 * sgn p c0
        + ∑ c ∈ Finset.univ.erase c0, modeCoeff a σ w u c * sgn p c := by
    intro u
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ c0)).symm
  have herase : (∑ c ∈ Finset.univ.erase c0,
        modeCoeff a σ w (t + 1) c * sgn p c)
      = a * (∑ c ∈ Finset.univ.erase c0, modeCoeff a σ w t c * sgn p c) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    have hc0 : c ≠ c0 := (Finset.mem_erase.mp hc).1
    rw [hcoeff c hc0]
    ring
  unfold velS
  rw [hsum (t + 1), hsum t, hT0, hT1, herase]
  have hmf : a * mstar a F + F = mstar a F := mstar_fixed a F ha
  linarith [hmf]

/-- **Target 2, stationary form**: the stationary-start walker has
expected velocity exactly the stationary mean `m* = μ·F` at all
times. -/
theorem velS_mean {N : ℕ} (a F σ w : ℝ) (t : ℕ) :
    expct (velS (N := N) a F σ w t) = mstar a F := by
  show expct (fun p => mstar a F
    + ∑ c : Fin (N + 1), modeCoeff a σ w t c * sgn p c) = mstar a F
  exact expct_const_add_modexpand _ _

/-- **The mode-energy identity.** With `w² = V` and the
fluctuation–dissipation balance `σ² = (1 − a²)·V`, the squared mode
coefficients at time `s` total exactly `V`:
`a^(2s)·w² + σ²·∑_{j<s} (a²)^j = V`. This is the algebraic heart of
stationarity in this model. -/
theorem modeEnergy (a σ w V : ℝ) (hw : w ^ 2 = V)
    (hV : σ ^ 2 = (1 - a ^ 2) * V) (s : ℕ) :
    a ^ (2 * s) * w ^ 2 + σ ^ 2 * (∑ j ∈ Finset.range s, (a ^ 2) ^ j)
      = V := by
  have hgeom : (1 - a ^ 2) * (∑ j ∈ Finset.range s, (a ^ 2) ^ j)
      = 1 - a ^ (2 * s) := by
    have h := geom_sum_mul (a ^ 2) s
    rw [← pow_mul] at h
    have h2 : (1 - a ^ 2) * (∑ j ∈ Finset.range s, (a ^ 2) ^ j)
        = -((∑ j ∈ Finset.range s, (a ^ 2) ^ j) * (a ^ 2 - 1)) := by ring
    rw [h2, h]
    ring
  calc a ^ (2 * s) * w ^ 2 + σ ^ 2 * (∑ j ∈ Finset.range s, (a ^ 2) ^ j)
      = a ^ (2 * s) * V + ((1 - a ^ 2) * V)
          * (∑ j ∈ Finset.range s, (a ^ 2) ^ j) := by rw [hw, hV]
    _ = a ^ (2 * s) * V + V * ((1 - a ^ 2)
          * (∑ j ∈ Finset.range s, (a ^ 2) ^ j)) := by ring
    _ = a ^ (2 * s) * V + V * (1 - a ^ (2 * s)) := by rw [hgeom]
    _ = V := by ring

/-- **Covariance kernel, scalar form**: the inner product of the
mode-coefficient vectors at times `s ≤ t` is `a^(t−s) · V`. -/
theorem modeCoeff_inner {N : ℕ} (a σ w V : ℝ) (hw : w ^ 2 = V)
    (hV : σ ^ 2 = (1 - a ^ 2) * V) {s t : ℕ} (hst : s ≤ t) (htN : t ≤ N) :
    ∑ c : Fin (N + 1), modeCoeff a σ w s c * modeCoeff a σ w t c
      = a ^ (t - s) * V := by
  have hsN : s ≤ N := le_trans hst htN
  have hterm : ∀ j : Fin N,
      modeCoeff a σ w s (Fin.succ j) * modeCoeff a σ w t (Fin.succ j)
        = if j.val + 1 ≤ s
            then a ^ (t - s) * ((a ^ 2) ^ (s - 1 - j.val) * σ ^ 2)
            else 0 := by
    intro j
    have h0s : (Fin.succ j).val ≠ 0 := by
      show ¬ (j.val + 1 = 0)
      exact Nat.succ_ne_zero _
    by_cases hj : j.val + 1 ≤ s
    · have hjt : j.val + 1 ≤ t := le_trans hj hst
      rw [modeCoeff_succ_of_le _ _ _ _ _ h0s hj,
        modeCoeff_succ_of_le _ _ _ _ _ h0s hjt, if_pos hj, Fin.val_succ]
      have e1 : (a ^ (s - (j.val + 1)) * σ) * (a ^ (t - (j.val + 1)) * σ)
          = (a ^ (s - (j.val + 1)) * a ^ (t - (j.val + 1))) * σ ^ 2 := by
        ring
      have hexp : (s - (j.val + 1)) + (t - (j.val + 1))
          = (t - s) + 2 * (s - 1 - j.val) := by omega
      rw [e1, ← pow_add, hexp, pow_add, pow_mul]
      ring
    · have hjs : ¬ (Fin.succ j).val ≤ s := hj
      rw [modeCoeff_succ_of_gt _ _ _ _ _ h0s hjs, if_neg hj, zero_mul]
  rw [Fin.sum_univ_succ]
  rw [modeCoeff_zero _ _ _ _ _ (by rfl : (0 : Fin (N + 1)).val = 0),
    modeCoeff_zero _ _ _ _ _ (by rfl : (0 : Fin (N + 1)).val = 0)]
  have hhead : (a ^ s * w) * (a ^ t * w) = a ^ (t - s) * (a ^ (2 * s) * w ^ 2) := by
    have hpow : a ^ (s + t) = a ^ (t - s) * a ^ (2 * s) := by
      rw [show s + t = (t - s) + 2 * s by omega, pow_add]
    have e1 : (a ^ s * w) * (a ^ t * w) = a ^ (s + t) * w ^ 2 := by
      have e0 : (a ^ s * w) * (a ^ t * w) = (a ^ s * a ^ t) * (w * w) := by
        ring
      rw [e0, ← pow_add, ← pow_two]
    rw [e1, hpow]; ring
  rw [hhead]
  have htail : (∑ j : Fin N, modeCoeff a σ w s (Fin.succ j)
        * modeCoeff a σ w t (Fin.succ j))
      = a ^ (t - s) * (σ ^ 2 * ∑ j ∈ Finset.range s, (a ^ 2) ^ j) := by
    have hpt : ∀ j : Fin N, (if j.val + 1 ≤ s
          then a ^ (t - s) * ((a ^ 2) ^ (s - 1 - j.val) * σ ^ 2) else 0)
        = a ^ (t - s) * (if j.val + 1 ≤ s
            then (a ^ 2) ^ (s - 1 - j.val) * σ ^ 2 else 0) := by
      intro j
      by_cases hj : j.val + 1 ≤ s
      · rw [if_pos hj, if_pos hj]
      · rw [if_neg hj, if_neg hj, mul_zero]
    rw [Finset.sum_congr rfl (fun j _ => hterm j),
      Finset.sum_congr rfl (fun j _ => hpt j), ← Finset.mul_sum]
    rw [Fin.sum_univ_eq_sum_range
      (fun k => if k + 1 ≤ s then (a ^ 2) ^ (s - 1 - k) * σ ^ 2 else 0) N]
    have hsub : Finset.range s ⊆ Finset.range N :=
      Finset.range_subset.mpr
        (fun j hj => Finset.mem_range.mpr (lt_of_lt_of_le hj hsN))
    rw [← Finset.sum_subset
      (f := fun k => if k + 1 ≤ s then (a ^ 2) ^ (s - 1 - k) * σ ^ 2 else 0)
      hsub (by
      intro j _ hjS
      have hge : s ≤ j := by
        by_contra hlt
        push_neg at hlt
        exact hjS (Finset.mem_range.mpr hlt)
      have hj1 : ¬ j + 1 ≤ s := by omega
      exact if_neg hj1)]
    have hstrip : ∀ j ∈ Finset.range s,
        (if j + 1 ≤ s then (a ^ 2) ^ (s - 1 - j) * σ ^ 2 else 0)
          = (a ^ 2) ^ (s - 1 - j) * σ ^ 2 := by
      intro j hj
      have hj1 : j + 1 ≤ s := Finset.mem_range.mp hj
      rw [if_pos hj1]
    rw [Finset.sum_congr rfl hstrip, ← Finset.sum_mul,
      Finset.sum_range_reflect (fun k => (a ^ 2) ^ k) s]
    ring
  rw [htail, ← mul_add, modeEnergy a σ w V hw hV s]

/-- **Covariance kernel (Target 1 & 3 engine).** For `s ≤ t ≤ N`, the
stationary-start walker's velocity fluctuations at times `s` and `t`
have expected product exactly `a^(t−s) · V`, under the hypotheses on
the face: `w² = V` (the initial fluctuation has the stationary size)
and `σ² = (1 − a²)·V` (the fluctuation–dissipation balance). -/
theorem velS_cov {N : ℕ} (a F σ w V : ℝ) (hw : w ^ 2 = V)
    (hV : σ ^ 2 = (1 - a ^ 2) * V) {s t : ℕ} (hst : s ≤ t) (htN : t ≤ N) :
    expct (fun p => (velS (N := N) a F σ w s p - mstar a F)
      * (velS (N := N) a F σ w t p - mstar a F))
      = a ^ (t - s) * V := by
  have hfl : ∀ u : ℕ, ∀ p : Fin (N + 1) → Bool,
      velS a F σ w u p - mstar a F
        = ∑ c, modeCoeff a σ w u c * sgn p c := by
    intro u p
    unfold velS
    rw [add_sub_cancel_left]
  simp_rw [hfl]
  rw [expct_modexpand_mul]
  exact modeCoeff_inner a σ w V hw hV hst htN

/-- **Covariance kernel, symmetric form**: expected product of the
fluctuations at any two times `s, t ≤ N` is `a^|s−t| · V` (written
with `max`/`min` to stay in `ℕ`). -/
theorem velS_cov_abs {N : ℕ} (a F σ w V : ℝ) (hw : w ^ 2 = V)
    (hV : σ ^ 2 = (1 - a ^ 2) * V) {s t : ℕ} (hsN : s ≤ N) (htN : t ≤ N) :
    expct (fun p => (velS (N := N) a F σ w s p - mstar a F)
      * (velS (N := N) a F σ w t p - mstar a F))
      = a ^ (max s t - min s t) * V := by
  rcases le_total s t with h | h
  · rw [max_eq_right h, min_eq_left h]
    exact velS_cov a F σ w V hw hV h htN
  · rw [max_eq_left h, min_eq_right h]
    have hswap : (fun p => (velS (N := N) a F σ w s p - mstar a F)
        * (velS (N := N) a F σ w t p - mstar a F))
      = (fun p => (velS (N := N) a F σ w t p - mstar a F)
        * (velS (N := N) a F σ w s p - mstar a F)) := by
      funext p; ring
    rw [hswap]
    exact velS_cov a F σ w V hw hV h hsN

/-- **Target 1, stationary form**: in the stationary-start model the
velocity variance is exactly the stationary variance `V` at every
time — the process is stationary at the level of second moments, by
construction and computation, not by assumption. -/
theorem velS_var {N : ℕ} (a F σ w V : ℝ) (hw : w ^ 2 = V)
    (hV : σ ^ 2 = (1 - a ^ 2) * V) {t : ℕ} (htN : t ≤ N) :
    expct (fun p => (velS (N := N) a F σ w t p - mstar a F) ^ 2) = V := by
  have h := velS_cov a F σ w V hw hV (le_refl t) htN
  simpa only [pow_two, tsub_self, pow_zero, one_mul] using h

/-- **Target 1, instantiated**: with `V` taken to be `statVar a σ`
and `w` its square root (which exists when `a² < 1`), the
stationary-start walker's velocity variance is exactly
`σ² / (1 − a²)`. -/
theorem velS_var_stationary {N : ℕ} (a F σ : ℝ) (ha2 : a ^ 2 < 1)
    {t : ℕ} (htN : t ≤ N) :
    expct (fun p => (velS (N := N) a F σ (Real.sqrt (statVar a σ)) t p
      - mstar a F) ^ 2) = statVar a σ := by
  have h1 : (1 : ℝ) - a ^ 2 ≠ 0 := sub_ne_zero.mpr (ne_of_lt ha2).symm
  have hVnn : (0 : ℝ) ≤ statVar a σ := by
    show (0 : ℝ) ≤ σ ^ 2 / (1 - a ^ 2)
    exact div_nonneg (sq_nonneg σ) (by linarith)
  have hw : (Real.sqrt (statVar a σ)) ^ 2 = statVar a σ :=
    Real.sq_sqrt hVnn
  have hV : σ ^ 2 = (1 - a ^ 2) * statVar a σ := by
    show σ ^ 2 = (1 - a ^ 2) * (σ ^ 2 / (1 - a ^ 2))
    field_simp
  exact velS_var a F σ _ _ hw hV htN

/-! ## Position: the displacement and its exact growth -/

/-- The exact finite position-growth sum `∑_{j,k<n} a^|j−k|`
(written with `max`/`min` to stay in `ℕ`). -/
def posGrow (a : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, a ^ (max j k - min j k)

/-- Position-displacement coefficients: fluctuation of the position
after `n` steps along coordinate `c`. -/
def dispCoeff {N : ℕ} (a σ w : ℝ) (n : ℕ) (c : Fin (N + 1)) : ℝ :=
  ∑ k ∈ Finset.range n, modeCoeff a σ w (k + 1) c

/-- The position displacement after `n` steps (started at 0), as a
finite mode expansion. Its agreement with the telescoped velocity
fluctuations is `dispS_agree` below. -/
def dispS {N : ℕ} (a F σ w : ℝ) (n : ℕ) (p : Fin (N + 1) → Bool) : ℝ :=
  ∑ c : Fin (N + 1), dispCoeff a σ w n c * sgn p c

theorem dispS_agree (a F σ w : ℝ) (n : ℕ) (p : Fin (N + 1) → Bool) :
    dispS a F σ w n p
      = ∑ k ∈ Finset.range n, (velS a F σ w (k + 1) p - mstar a F) := by
  unfold dispS dispCoeff
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  unfold velS
  rw [add_sub_cancel_left]

/-- The displacement has mean zero at every `n`. -/
theorem expct_dispS {N : ℕ} (a F σ w : ℝ) (n : ℕ) :
    expct (dispS (N := N) a F σ w n) = 0 := by
  have hfun : dispS (N := N) a F σ w n
      = (fun p => ∑ c : Fin (N + 1), dispCoeff a σ w n c * sgn p c) := by
    funext p
    rfl
  rw [hfun]
  have h := expct_const_add_modexpand (0 : ℝ) (dispCoeff (N := N) a σ w n)
  simp only [zero_add] at h
  exact h

theorem dispCoeff_sq_sum (a σ w V : ℝ) (hw : w ^ 2 = V)
    (hV : σ ^ 2 = (1 - a ^ 2) * V) {N : ℕ} (n : ℕ) (hn : n ≤ N) :
    ∑ c : Fin (N + 1), (dispCoeff a σ w n c) ^ 2 = V * posGrow a n := by
  have hexp : ∀ j k : ℕ, max (j + 1) (k + 1) - min (j + 1) (k + 1)
      = max j k - min j k := by
    intro j k
    rcases le_total j k with h | h
    · rw [max_eq_right (Nat.succ_le_succ h), min_eq_left (Nat.succ_le_succ h),
        max_eq_right h, min_eq_left h]
      omega
    · rw [max_eq_left (Nat.succ_le_succ h), min_eq_right (Nat.succ_le_succ h),
        max_eq_left h, min_eq_right h]
      omega
  have hinner : ∀ j ∈ Finset.range n, ∀ k ∈ Finset.range n,
      (∑ c : Fin (N + 1),
        modeCoeff a σ w (j + 1) c * modeCoeff a σ w (k + 1) c)
        = a ^ (max j k - min j k) * V := by
    intro j hj k hk
    have hj1 : j + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    have hk1 : k + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
    rcases le_total j k with h | h
    · rw [max_eq_right h, min_eq_left h]
      have hmi := modeCoeff_inner a σ w V hw hV (Nat.succ_le_succ h)
        (le_trans hk1 hn)
      rwa [show (k + 1) - (j + 1) = k - j by omega] at hmi
    · rw [max_eq_left h, min_eq_right h]
      have hkk := modeCoeff_inner a σ w V hw hV (Nat.succ_le_succ h)
        (le_trans hj1 hn)
      rw [show (j + 1) - (k + 1) = j - k by omega] at hkk
      rw [show (∑ c : Fin (N + 1), modeCoeff a σ w (j + 1) c
            * modeCoeff a σ w (k + 1) c)
          = ∑ c : Fin (N + 1), modeCoeff a σ w (k + 1) c
            * modeCoeff a σ w (j + 1) c from
        Finset.sum_congr rfl (fun c _ => mul_comm _ _)]
      exact hkk
  unfold dispCoeff
  simp_rw [pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.range n)
    (f := fun c j => ∑ k ∈ Finset.range n,
      modeCoeff a σ w (j + 1) c * modeCoeff a σ w (k + 1) c)]
  rw [Finset.sum_congr rfl (fun j hj => Finset.sum_comm (s := Finset.univ)
    (t := Finset.range n)
    (f := fun c k => modeCoeff a σ w (j + 1) c * modeCoeff a σ w (k + 1) c))]
  rw [Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl
    (fun k hk => hinner j hj k hk))]
  unfold posGrow
  have hcomm : ∀ j k : ℕ, a ^ (max j k - min j k) * V
      = V * a ^ (max j k - min j k) :=
    fun j k => mul_comm _ _
  simp_rw [hcomm, ← Finset.mul_sum]

/-- **Target 3, finite form**: the expected squared displacement after
`n` steps is exactly `V · posGrow a n` — under the hypotheses on the
face (`w² = V`, `σ² = (1 − a²)·V`). Since the displacement has mean
zero (`expct_dispS`), this is the position variance. -/
theorem expct_dispS_sq (a F σ w V : ℝ) (hw : w ^ 2 = V)
    (hV : σ ^ 2 = (1 - a ^ 2) * V) {N : ℕ} (n : ℕ) (hn : n ≤ N) :
    expct (fun p => (dispS (N := N) a F σ w n p) ^ 2) = V * posGrow a n := by
  have hdeq : (fun p => (dispS (N := N) a F σ w n p) ^ 2)
      = (fun p => (∑ c : Fin (N + 1), dispCoeff a σ w n c * sgn p c) ^ 2) :=
    rfl
  rw [hdeq, expct_modexpand_sq]
  exact dispCoeff_sq_sum a σ w V hw hV n hn

/-- One-step growth of the position-growth sum. -/
theorem posGrow_succ (a : ℝ) (ha : a ≠ 1) (n : ℕ) :
    posGrow a (n + 1)
      = posGrow a n + 2 * (a * (1 - a ^ n) / (1 - a)) + 1 := by
  have h1a : (1 : ℝ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have hcross : ∑ j ∈ Finset.range n, a ^ (n - j)
      = a * (1 - a ^ n) / (1 - a) := by
    have hrefl : ∑ j ∈ Finset.range n, a ^ (n - j)
        = ∑ i ∈ Finset.range n, a ^ (i + 1) := by
      rw [← Finset.sum_range_reflect (fun i => a ^ (n - i)) n]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < n := Finset.mem_range.mp hi
      have he : n - (n - 1 - i) = i + 1 := by omega
      rw [he]
    have h1 : ∑ i ∈ Finset.range n, a ^ (i + 1)
        = a * ∑ i ∈ Finset.range n, a ^ i := by
      simp_rw [pow_succ]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hS : (1 - a) * (∑ i ∈ Finset.range n, a ^ i) = 1 - a ^ n := by
      have hgeom := geom_sum_mul a n
      have e : (1 - a) * (∑ i ∈ Finset.range n, a ^ i)
          = -((∑ i ∈ Finset.range n, a ^ i) * (a - 1)) := by ring
      rw [e, hgeom]
      ring
    have hdiv : (∑ i ∈ Finset.range n, a ^ i) = (1 - a ^ n) / (1 - a) := by
      rw [eq_div_iff h1a, mul_comm]
      exact hS
    rw [hrefl, h1, hdiv]
    field_simp
  have e1 : ∀ j ∈ Finset.range n, a ^ (max j n - min j n) = a ^ (n - j) := by
    intro j hj
    have hj' : j < n := Finset.mem_range.mp hj
    rw [max_eq_right (le_of_lt hj'), min_eq_left (le_of_lt hj')]
  have e2 : ∀ k ∈ Finset.range n, a ^ (max n k - min n k) = a ^ (n - k) := by
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    rw [max_eq_left (le_of_lt hk'), min_eq_right (le_of_lt hk')]
  have e3 : a ^ (max n n - min n n) = 1 := by
    rw [max_self, min_self, tsub_self, pow_zero]
  unfold posGrow
  rw [Finset.sum_range_succ]
  simp_rw [Finset.sum_range_succ]
  have step1 : (∑ j ∈ Finset.range n,
        ((∑ k ∈ Finset.range n, a ^ (max j k - min j k))
          + a ^ (max j n - min j n)))
      = (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, a ^ (max j k - min j k))
        + ∑ j ∈ Finset.range n, a ^ (n - j) := by
    rw [Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact e1 j hj
  have step2 : (∑ k ∈ Finset.range n, a ^ (max n k - min n k))
        + a ^ (max n n - min n n)
      = (∑ k ∈ Finset.range n, a ^ (n - k)) + 1 := by
    rw [Finset.sum_congr rfl (fun k hk => e2 k hk), e3]
  rw [step1, step2, hcross]
  generalize a * (1 - a ^ n) / (1 - a) = C
  ring

/-- Closed form of the position-growth sum, for `a ≠ 1`. -/
theorem posGrow_closed (a : ℝ) (ha : a ≠ 1) (n : ℕ) :
    posGrow a n
      = n * (1 + a) / (1 - a) - 2 * a * (1 - a ^ n) / (1 - a) ^ 2 := by
  have h1a : (1 : ℝ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have h1a2 : (1 - a) ^ 2 ≠ 0 := pow_ne_zero 2 h1a
  induction n with
  | zero =>
    unfold posGrow
    simp
  | succ n ih =>
    rw [posGrow_succ a ha n, ih, pow_succ]
    field_simp
    push_cast
    ring

/-- **Target 3, stationary form**: with `V = statVar a σ` the
position variance after `n` steps is exactly
`σ²/(1−a²) · posGrow a n`. -/
theorem posVar_stationary (a F σ : ℝ) (ha2 : a ^ 2 < 1) {N : ℕ} (n : ℕ)
    (hn : n ≤ N) :
    expct (fun p => (dispS (N := N) a F σ (Real.sqrt (statVar a σ)) n p) ^ 2)
      = statVar a σ * posGrow a n := by
  have h1 : (1 : ℝ) - a ^ 2 ≠ 0 := sub_ne_zero.mpr (ne_of_lt ha2).symm
  have hVnn : (0 : ℝ) ≤ statVar a σ := by
    show (0 : ℝ) ≤ σ ^ 2 / (1 - a ^ 2)
    exact div_nonneg (sq_nonneg σ) (by linarith)
  have hw : (Real.sqrt (statVar a σ)) ^ 2 = statVar a σ :=
    Real.sq_sqrt hVnn
  have hV : σ ^ 2 = (1 - a ^ 2) * statVar a σ := by
    show σ ^ 2 = (1 - a ^ 2) * (σ ^ 2 / (1 - a ^ 2))
    field_simp
  exact expct_dispS_sq a F σ _ _ hw hV n hn

/-- **Target 3, exact per-step increment**: the position variance grows
by exactly `V · ((1+a)/(1−a) − 2a^{n+1}/(1−a))` from step `n` to
`n+1` — the advertised rate `σ²/(1−a)²` plus a transient priced on
the face (see `posVar_rate`). -/
theorem posVar_increment (a F σ : ℝ) (ha2 : a ^ 2 < 1) (ha : a ≠ 1)
    {N : ℕ} (n : ℕ) (hn : n + 1 ≤ N) :
    expct (fun p => (dispS (N := N) a F σ (Real.sqrt (statVar a σ))
        (n + 1) p) ^ 2)
      - expct (fun p => (dispS (N := N) a F σ (Real.sqrt (statVar a σ))
        n p) ^ 2)
      = statVar a σ * ((1 + a) / (1 - a) - 2 * a ^ (n + 1) / (1 - a)) := by
  have h1a : (1 : ℝ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have h1a2 : (1 - a) ^ 2 ≠ 0 := pow_ne_zero 2 h1a
  rw [posVar_stationary a F σ ha2 (n + 1) hn,
    posVar_stationary a F σ ha2 n (le_trans (Nat.le_succ n) hn),
    posGrow_closed a ha (n + 1), posGrow_closed a ha n, pow_succ]
  field_simp
  push_cast
  ring

/-- Pure algebra: the increment's leading term is the advertised rate. -/
theorem rate_algebra (a σ : ℝ) (ha2 : a ^ 2 < 1) (ha : a ≠ 1) (n : ℕ) :
    statVar a σ * ((1 + a) / (1 - a) - 2 * a ^ (n + 1) / (1 - a))
      = σ ^ 2 / (1 - a) ^ 2
        - 2 * a ^ (n + 1) * statVar a σ / (1 - a) := by
  have h1a : (1 : ℝ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have h1a2 : (1 - a) ^ 2 ≠ 0 := pow_ne_zero 2 h1a
  have hpa : (1 : ℝ) + a ≠ 0 := by
    have hpos : (0 : ℝ) < 1 + a := by nlinarith [sq_nonneg (a + 1), ha2]
    exact ne_of_gt hpos
  have h2 : (1 : ℝ) - a ^ 2 ≠ 0 := sub_ne_zero.mpr (ne_of_lt ha2).symm
  unfold statVar
  field_simp
  ring

/-- **Target 3, pinned verdict form**: in the stationary regime the
per-step increment of the position variance is exactly
`σ²/(1−a)²` **minus** the transient `2a^{n+1}·V/(1−a)`, with
`V = σ²/(1−a²)`. The bare `σ²/(1−a)²` is the large-`n` (or
`a → 0`-kick) limit, not an exact finite identity — the transient is
the price of finiteness, stated on the face. -/
theorem posVar_rate (a F σ : ℝ) (ha2 : a ^ 2 < 1) (ha : a ≠ 1)
    {N : ℕ} (n : ℕ) (hn : n + 1 ≤ N) :
    expct (fun p => (dispS (N := N) a F σ (Real.sqrt (statVar a σ))
        (n + 1) p) ^ 2)
      - expct (fun p => (dispS (N := N) a F σ (Real.sqrt (statVar a σ))
        n p) ^ 2)
      = σ ^ 2 / (1 - a) ^ 2
        - 2 * a ^ (n + 1) * statVar a σ / (1 - a) := by
  rw [posVar_increment a F σ ha2 ha n hn, rate_algebra a σ ha2 ha n]

/-! ## Target 4: the Einstein form -/

/-- The **noise temperature** of the model: `Θ := σ² / (2(1 − a))`,
**defined** by the fluctuation–dissipation balance `σ² = (1 − a²)·V`
together with `V = μ·Θ` — an exact definition inside this finite
model. It is a model parameter, **not** thermodynamic `k_B T` (charter
kill K1); no temperature in kelvin is claimed anywhere. -/
noncomputable def noiseTemp (a σ : ℝ) : ℝ := σ ^ 2 / (2 * (1 - a))

/-- The diffusivity of the model, pinned by the one-dimensional
convention that position variance grows by `2D` per step: since the
growth rate's leading term is `σ²/(1−a)²` (`posVar_rate`),
`D := σ²/(2(1−a)²)`. -/
noncomputable def diffusivity (a σ : ℝ) : ℝ := σ ^ 2 / (2 * (1 - a) ^ 2)

/-- **Target 4 — the Einstein form.** `D = μ·Θ` as an exact finite
identity of real numbers, for `a ≠ 1`: the diffusivity (defined from
the measured growth rate) factors as mobility × noise temperature.
This is the discrete, finite, one-particle shadow of Einstein's
relation — nothing continuum, Brownian, or Stokes-drag is claimed
(charter kill K4). -/
theorem einstein (a σ : ℝ) (ha : a ≠ 1) :
    diffusivity a σ = mobility a * noiseTemp a σ := by
  have h1a : (1 : ℝ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have h1a2 : (1 - a) ^ 2 ≠ 0 := pow_ne_zero 2 h1a
  unfold diffusivity mobility noiseTemp
  field_simp

/-- The convention-check: `2D` is exactly the growth-rate constant
`σ²/(1−a)²` of `posVar_rate`. -/
theorem two_mul_diffusivity (a σ : ℝ) (ha : a ≠ 1) :
    2 * diffusivity a σ = σ ^ 2 / (1 - a) ^ 2 := by
  have h1a : (1 : ℝ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have h1a2 : (1 - a) ^ 2 ≠ 0 := pow_ne_zero 2 h1a
  unfold diffusivity
  field_simp

/-- **The targets tied together**: in the stationary regime the exact
per-step increment of the position variance is `2D` minus the
transient `2a^{n+1}·V/(1−a)` — Einstein's `2D` per step is the exact
leading term, with the finite-time correction on the face. -/
theorem posVar_rate_diffusivity (a F σ : ℝ) (ha2 : a ^ 2 < 1)
    (ha : a ≠ 1) {N : ℕ} (n : ℕ) (hn : n + 1 ≤ N) :
    expct (fun p => (dispS (N := N) a F σ (Real.sqrt (statVar a σ))
        (n + 1) p) ^ 2)
      - expct (fun p => (dispS (N := N) a F σ (Real.sqrt (statVar a σ))
        n p) ^ 2)
      = 2 * diffusivity a σ
        - 2 * a ^ (n + 1) * statVar a σ / (1 - a) := by
  rw [posVar_rate a F σ ha2 ha n hn, two_mul_diffusivity a σ ha]

end DiscreteLangevin
end ThetLogos
