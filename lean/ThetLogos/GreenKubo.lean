import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Normed
import ThetLogos.DiscreteLangevin

namespace ThetLogos
namespace GreenKubo

open DiscreteLangevin

/-!
# Green–Kubo brick: Stokes–Einstein Rung 2 (T1 target, finite + series level)

Charter: `whitepaper/stokes-einstein-scoping-DRAFT-2026-10-18.md`, §5 Rung 2:
"Green–Kubo, finite form. D as the summed velocity autocorrelation of the
Rung-1 process (autocovariance a^|k| · stationary variance), proved equal to
Rung 1's rate — the Kubo shape checked against the direct computation."

Rung 1: `ThetLogos.DiscreteLangevin` (dossier
`whitepaper/discrete-langevin-stokes-einstein-rung1-2026-10-22.md`), imported
and not modified. Status: STANDS WHOLE (T1), landed 2026-10-22
(parent-verified: in-tree build green, axiom check standard-only).
NO CLAIM beyond the finite and series identities proved below.

WHAT IS PROVED.

* T1 (lag autocovariance). `lagCov a σ k = a^k · V`, `V = statVar a σ`, is
  the lag form of the Rung-1 stationary covariance kernel: it equals the
  process covariance `E[(v₀ − m*)(v_k − m*)]` of the stationary-start
  walker (`lagCov_eq_velS_cov`, from `velS_cov_abs`).

* T2 (the Green–Kubo sum). The Kubo sum of the lag covariance,
  `V/2 + ∑_{k≥1} a^k · V` (the `1/2` is the trapezoidal weight of the
  zero-lag term, the discrete shadow of `∫₀^∞ C(t) dt`), equals Rung 1's
  diffusivity `D = σ²/(2(1−a)²)` exactly (`gkSum_eq_diffusivity`),
  via the summed geometric series `∑'_{k} a^k · V = V/(1−a)` at `|a| < 1`.

* T3 (finite-horizon consistency). The exact finite identity tying the
  position variance to the autocovariance: with `lagSum` the two-sided
  lag sum `Σ_{k=−(n−1)}^{n−1} (n − |k|) · a^|k|` (written as the diagonal
  term plus twice the positive-lag terms, using `C(−k) = C(k)`),
  `Var(x_n) = V · lagSum a n` at the level of the process
  (`posVar_eq_lagSum`, through Rung 1's `posVar_stationary` and
  `posGrow`), and `V · lagSum a n` is the lag sum in `lagCov` form
  (`statVar_mul_lagSum`, `posVar_lag_form`). The double-sum content is
  Rung 1's `posGrow` identity, proved there from the path-space mode
  expansion; here `posGrow = lagSum` is proved by matching the exact
  one-step recurrence both sides satisfy (`posGrow_succ` of Rung 1
  against `lagSum_succ` here) — algebra in `a, σ, n` on top of Rung 1's
  closed forms, stated plainly.

* T4 (partial sums). The finite partial Kubo sums have the closed form
  `gkPartial a σ N = V/2 + V · a(1 − a^N)/(1 − a)` (`gkPartial_closed`)
  and converge to `diffusivity a σ` as `N → ∞` (`gkPartial_tendsto`).

FENCES (charter §6, binding):

* K1: `noiseTemp` Θ of Rung 1 is a model ratio, `σ² / (2(1 − a))`,
  defined by the fluctuation–dissipation balance of the finite model.
  It is never thermodynamic `k_B T`, and nothing here derives a
  thermodynamic temperature. The Einstein form used is Rung 1's proved
  `D = μ · Θ` at the finite level.
* K3: nothing here rests on any other brick's displacement law. The
  only corpus import is Rung 1 (`DiscreteLangevin`), whose position
  variance is derived there from its own Langevin update.
* K4: no continuum statement. The only limits taken in this file are
  the `N → ∞` limit of finite partial sums and the sum of a convergent
  series whose terms are finite lag covariances. No limit process is
  named, and no continuum object is claimed.
-/

/-- `|a| < 1` from `a^2 < 1`, via the square root. -/
theorem abs_lt_one_of_sq_lt_one {a : ℝ} (ha2 : a ^ 2 < 1) : |a| < 1 := by
  have h := Real.sqrt_lt_sqrt (sq_nonneg a) ha2
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_one] at h

/-! ## T1: the lag autocovariance -/

/-- The **lag covariance** of the Rung-1 stationary process at lag `k`:
`C(k) = a^k · V` with `V = statVar a σ` the stationary variance. -/
noncomputable def lagCov (a σ : ℝ) (k : ℕ) : ℝ := a ^ k * statVar a σ

theorem lagCov_zero (a σ : ℝ) : lagCov a σ 0 = statVar a σ := by
  simp [lagCov]

/-- **T1 (lag autocovariance).** The lag covariance `C(k) = a^k · V` is
exactly the stationary-start process covariance at lag `k`:
`E[(v₀ − m*)(v_k − m*)] = C(k)`, instantiated from Rung 1's
`velS_cov_abs` with `w = sqrt V`, `V = statVar a σ` (which exists and
satisfies the fluctuation–dissipation balance when `a^2 < 1`). -/
theorem lagCov_eq_velS_cov {N : ℕ} (a F σ : ℝ) (ha2 : a ^ 2 < 1)
    (k : ℕ) (hk : k ≤ N) :
    expct (fun p => (velS (N := N) a F σ (Real.sqrt (statVar a σ)) 0 p
        - mstar a F)
      * (velS (N := N) a F σ (Real.sqrt (statVar a σ)) k p - mstar a F))
      = lagCov a σ k := by
  have hVnn : (0 : ℝ) ≤ statVar a σ := by
    show (0 : ℝ) ≤ σ ^ 2 / (1 - a ^ 2)
    exact div_nonneg (sq_nonneg σ) (by linarith)
  have hw : (Real.sqrt (statVar a σ)) ^ 2 = statVar a σ :=
    Real.sq_sqrt hVnn
  have hV : σ ^ 2 = (1 - a ^ 2) * statVar a σ := by
    show σ ^ 2 = (1 - a ^ 2) * (σ ^ 2 / (1 - a ^ 2))
    have h1 : (1 : ℝ) - a ^ 2 ≠ 0 := sub_ne_zero.mpr (ne_of_lt ha2).symm
    field_simp
  have h := velS_cov_abs a F σ (Real.sqrt (statVar a σ)) (statVar a σ)
    hw hV (Nat.zero_le N) hk
  rw [h]
  simp only [lagCov, max_eq_right (Nat.zero_le k),
    min_eq_left (Nat.zero_le k), tsub_zero]

/-! ## T2: the Green–Kubo sum -/

/-- The lag covariances are summable at `a^2 < 1`. -/
theorem summable_lagCov (a σ : ℝ) (ha2 : a ^ 2 < 1) :
    Summable (lagCov a σ) := by
  have ha_abs : |a| < 1 := abs_lt_one_of_sq_lt_one ha2
  have h : Summable fun k : ℕ => a ^ k * statVar a σ :=
    (summable_geometric_of_abs_lt_one ha_abs).mul_right _
  exact h

/-- The full lag sum: `∑'_k C(k) = V / (1 − a)` at `a^2 < 1`. -/
theorem tsum_lagCov (a σ : ℝ) (ha2 : a ^ 2 < 1) :
    ∑' k : ℕ, lagCov a σ k = statVar a σ / (1 - a) := by
  have ha_abs : |a| < 1 := abs_lt_one_of_sq_lt_one ha2
  calc ∑' k : ℕ, lagCov a σ k
      = ∑' k : ℕ, a ^ k * statVar a σ :=
        tsum_congr fun k => rfl
    _ = (1 - a)⁻¹ * statVar a σ :=
        ((hasSum_geometric_of_abs_lt_one ha_abs).mul_right _).tsum_eq
    _ = statVar a σ / (1 - a) := by rw [div_eq_mul_inv, mul_comm]

/-- The positive-lag tail of the lag sum:
`∑'_k a^(k+1) · V = aV · (1 − a)⁻¹` at `a^2 < 1`. -/
theorem tsum_lagCov_succ (a σ : ℝ) (ha2 : a ^ 2 < 1) :
    ∑' k : ℕ, a ^ (k + 1) * statVar a σ
      = (a * statVar a σ) * (1 - a)⁻¹ := by
  have ha_abs : |a| < 1 := abs_lt_one_of_sq_lt_one ha2
  have h := (hasSum_geometric_of_abs_lt_one ha_abs).mul_left
    (a * statVar a σ)
  rw [← h.tsum_eq]
  apply tsum_congr
  intro k
  rw [pow_succ]
  ring

/-- Pure algebra step of T2: `V/2 + aV/(1 − a) = D` at `a^2 < 1`,
with `V = σ²/(1 − a²)` and `D = σ²/(2(1 − a)²)`. -/
theorem gk_algebra (a σ : ℝ) (ha2 : a ^ 2 < 1) :
    statVar a σ / 2 + (a * statVar a σ) * (1 - a)⁻¹
      = diffusivity a σ := by
  have ha_abs : |a| < 1 := abs_lt_one_of_sq_lt_one ha2
  have h1a : (1 : ℝ) - a ≠ 0 :=
    sub_ne_zero.mpr (ne_of_lt (lt_of_abs_lt ha_abs)).symm
  have h1pa : (1 : ℝ) + a ≠ 0 :=
    ne_of_gt (by have h := (abs_lt.mp ha_abs).1; linarith)
  have hprod : ((1 : ℝ) - a) * (1 + a) ≠ 0 := mul_ne_zero h1a h1pa
  have hfact : (1 : ℝ) - a ^ 2 = (1 - a) * (1 + a) := by ring
  unfold statVar diffusivity
  rw [hfact]
  field_simp
  ring

/-- The **Green–Kubo sum** of the Rung-1 process: the zero-lag term at
trapezoidal weight `1/2` plus the summed positive-lag covariances. -/
noncomputable def gkSum (a σ : ℝ) : ℝ :=
  statVar a σ / 2 + ∑' k : ℕ, a ^ (k + 1) * statVar a σ

/-- **T2 (Green–Kubo sum = diffusivity) — the headline.** The summed
velocity autocorrelation of the Rung-1 stationary process, in Kubo
form, equals Rung 1's diffusivity `D = σ²/(2(1−a)²)` exactly:
`V/2 + ∑_{k≥1} a^k · V = D` at `a^2 < 1`. -/
theorem gkSum_eq_diffusivity (a σ : ℝ) (ha2 : a ^ 2 < 1) :
    gkSum a σ = diffusivity a σ := by
  unfold gkSum
  rw [tsum_lagCov_succ a σ ha2]
  exact gk_algebra a σ ha2

/-! ## T4: finite partial Kubo sums -/

/-- The finite partial Green–Kubo sum through lag `N`:
`V/2 + Σ_{k=1}^{N} a^k · V`. -/
noncomputable def gkPartial (a σ : ℝ) (N : ℕ) : ℝ :=
  statVar a σ / 2
    + ∑ k ∈ Finset.range N, a ^ (k + 1) * statVar a σ

/-- **T4, closed form**: the partial Kubo sum is
`V/2 + V · a(1 − a^N)/(1 − a)`. -/
theorem gkPartial_closed (a σ : ℝ) (ha : a ≠ 1) (N : ℕ) :
    gkPartial a σ N
      = statVar a σ / 2 + statVar a σ * (a * (1 - a ^ N) / (1 - a)) := by
  have hsum : (∑ k ∈ Finset.range N, a ^ (k + 1) * statVar a σ)
      = statVar a σ * (a * (1 - a ^ N) / (1 - a)) := by
    have h1 : (∑ k ∈ Finset.range N, a ^ (k + 1) * statVar a σ)
        = statVar a σ * (a * ∑ k ∈ Finset.range N, a ^ k) := by
      have hterm : ∀ k ∈ Finset.range N,
          a ^ (k + 1) * statVar a σ = statVar a σ * (a * a ^ k) := by
        intro k _
        rw [pow_succ]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
        ← Finset.mul_sum]
    have hS : (∑ k ∈ Finset.range N, a ^ k) = (1 - a ^ N) / (1 - a) := by
      rw [geom_sum_eq ha N]
      have hconv : (a ^ N - 1) / (a - 1) = (1 - a ^ N) / (1 - a) := by
        have h2 : (a ^ N - 1) / (a - 1)
            = (-(1 - a ^ N)) / (-(1 - a)) := by congr 1 <;> ring
        rw [h2, neg_div_neg_eq]
      exact hconv
    rw [h1, hS, mul_div_assoc]
  unfold gkPartial
  rw [hsum]

/-- **T4, convergence**: the partial Kubo sums tend to Rung 1's
diffusivity as `N → ∞`, at `a^2 < 1`. The only limit here is a limit
of finite partial sums (fence K4). -/
theorem gkPartial_tendsto (a σ : ℝ) (ha2 : a ^ 2 < 1) :
    Filter.Tendsto (gkPartial a σ) Filter.atTop
      (nhds (diffusivity a σ)) := by
  have ha_abs : |a| < 1 := abs_lt_one_of_sq_lt_one ha2
  have ha : a ≠ 1 := ne_of_lt (lt_of_abs_lt ha_abs)
  have hpow : Filter.Tendsto (fun N : ℕ => a ^ N) Filter.atTop
      (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one ha_abs
  have hlim : Filter.Tendsto
      (fun N : ℕ => statVar a σ / 2
        + statVar a σ * (a * (1 - a ^ N) / (1 - a)))
      Filter.atTop
      (nhds (statVar a σ / 2
        + statVar a σ * (a * (1 - 0) / (1 - a)))) := by
    apply Filter.Tendsto.const_add
    apply Filter.Tendsto.const_mul
    apply Filter.Tendsto.div_const
    apply Filter.Tendsto.const_mul
    exact Filter.Tendsto.const_sub 1 hpow
  have hfun : (fun N : ℕ => statVar a σ / 2
        + statVar a σ * (a * (1 - a ^ N) / (1 - a)))
      = gkPartial a σ :=
    funext fun N => (gkPartial_closed a σ ha N).symm
  rw [hfun] at hlim
  have hval : diffusivity a σ
      = statVar a σ / 2 + statVar a σ * (a * (1 - 0) / (1 - a)) := by
    have e : statVar a σ * (a * (1 - 0) / (1 - a))
        = (a * statVar a σ) * (1 - a)⁻¹ := by
      rw [sub_zero, mul_one, div_eq_mul_inv]
      ring
    rw [e]
    exact (gk_algebra a σ ha2).symm
  rw [hval]
  exact hlim

/-! ## T3: finite-horizon consistency -/

/-- The geometric sum over positive lags `1 ≤ k ≤ n`:
`Σ_{k=1}^{n} a^k = a(1 − a^n)/(1 − a)`. -/
theorem geom_Ico_one (a : ℝ) (ha : a ≠ 1) (n : ℕ) :
    ∑ k ∈ Finset.Ico 1 (n + 1), a ^ k = a * (1 - a ^ n) / (1 - a) := by
  have h1a : (1 : ℝ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have ha1 : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  have e1 : ∀ i : ℕ, a ^ (1 + i) = a * a ^ i := fun i => by
    rw [pow_add]
    simp
  rw [Finset.sum_congr rfl (fun i _ => e1 i), ← Finset.mul_sum,
    geom_sum_eq ha n]
  field_simp
  ring

/-- The **two-sided finite lag sum**
`Σ_{k=−(n−1)}^{n−1} (n − |k|) · a^|k|`, written with the diagonal term
plus twice the positive-lag terms (using `a^|−k| = a^|k|`):
`n + 2 · Σ_{k=1}^{n−1} (n − k) · a^k`. -/
def lagSum (a : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) + 2 * ∑ k ∈ Finset.Ico 1 n, ((n - k : ℕ) : ℝ) * a ^ k

/-- The lag sum satisfies the same one-step recurrence as Rung 1's
`posGrow` (`posGrow_succ`): the increment is
`2 · a(1 − a^n)/(1 − a) + 1`. -/
theorem lagSum_succ (a : ℝ) (ha : a ≠ 1) (n : ℕ) :
    lagSum a (n + 1)
      = lagSum a n + 2 * (a * (1 - a ^ n) / (1 - a)) + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lagSum]
  · have h1n : (1 : ℕ) ≤ n := hn
    have hsplit : (∑ k ∈ Finset.Ico 1 (n + 1),
          ((n + 1 - k : ℕ) : ℝ) * a ^ k)
        = (∑ k ∈ Finset.Ico 1 n, ((n - k : ℕ) : ℝ) * a ^ k)
          + (∑ k ∈ Finset.Ico 1 (n + 1), a ^ k) := by
      have hfn : ((n + 1 - n : ℕ) : ℝ) * a ^ n = a ^ n := by
        rw [show n + 1 - n = 1 by omega]
        simp
      have hA : (∑ k ∈ Finset.Ico 1 (n + 1),
            ((n + 1 - k : ℕ) : ℝ) * a ^ k)
          = (∑ k ∈ Finset.Ico 1 n, ((n + 1 - k : ℕ) : ℝ) * a ^ k)
            + a ^ n := by
        rw [Finset.sum_Ico_succ_top h1n
          (fun k => ((n + 1 - k : ℕ) : ℝ) * a ^ k), hfn]
      have hB : (∑ k ∈ Finset.Ico 1 (n + 1), a ^ k)
          = (∑ k ∈ Finset.Ico 1 n, a ^ k) + a ^ n :=
        Finset.sum_Ico_succ_top h1n (fun k => a ^ k)
      have hC : (∑ k ∈ Finset.Ico 1 n, ((n + 1 - k : ℕ) : ℝ) * a ^ k)
          = (∑ k ∈ Finset.Ico 1 n, ((n - k : ℕ) : ℝ) * a ^ k)
            + (∑ k ∈ Finset.Ico 1 n, a ^ k) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        have hk2 : k ≤ n := le_of_lt (Finset.mem_Ico.mp hk).2
        rw [show n + 1 - k = (n - k) + 1 by omega]
        push_cast
        ring
      rw [hA, hC, hB]
      ring
    unfold lagSum
    rw [hsplit, geom_Ico_one a ha n]
    push_cast
    ring

/-- **The finite lag identity**: Rung 1's position-growth sum is the
two-sided lag sum, `posGrow a n = lagSum a n`. Both sides start at
`0` and satisfy the identical exact recurrence (`posGrow_succ`,
`lagSum_succ`), so they agree at every `n`. -/
theorem posGrow_eq_lagSum (a : ℝ) (ha : a ≠ 1) (n : ℕ) :
    posGrow a n = lagSum a n := by
  induction n with
  | zero => simp [posGrow, lagSum]
  | succ n ih => rw [posGrow_succ a ha n, lagSum_succ a ha n, ih]

/-- The position variance in lag form, algebraic step:
`V · lagSum a n = n · C(0) + 2 · Σ_{k=1}^{n−1} (n − k) · C(k)`. -/
theorem statVar_mul_lagSum (a σ : ℝ) (n : ℕ) :
    statVar a σ * lagSum a n
      = n * lagCov a σ 0
        + 2 * ∑ k ∈ Finset.Ico 1 n, ((n - k : ℕ) : ℝ) * lagCov a σ k := by
  have hsum : (∑ k ∈ Finset.Ico 1 n, ((n - k : ℕ) : ℝ) * lagCov a σ k)
      = statVar a σ
        * ∑ k ∈ Finset.Ico 1 n, ((n - k : ℕ) : ℝ) * a ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold lagCov
    ring
  rw [hsum]
  unfold lagSum lagCov
  simp only [pow_zero, one_mul]
  ring

/-- **T3 (finite-horizon consistency).** The exact position variance
of the stationary-start process over `n` steps is the stationary
variance times the two-sided lag sum: `Var(x_n) = V · lagSum a n`.
This is Rung 1's `posVar_stationary` (itself computed there from the
path-space mode expansion as `V · posGrow a n`) composed with
`posGrow_eq_lagSum` — the autocovariance-sum form of the same exact
finite identity, not a new asymptotic. -/
theorem posVar_eq_lagSum (a F σ : ℝ) (ha2 : a ^ 2 < 1) (ha : a ≠ 1)
    {N : ℕ} (n : ℕ) (hn : n ≤ N) :
    expct (fun p => (dispS (N := N) a F σ (Real.sqrt (statVar a σ))
        n p) ^ 2)
      = statVar a σ * lagSum a n := by
  rw [posVar_stationary a F σ ha2 n hn, posGrow_eq_lagSum a ha n]

/-- **T3, lag-covariance form**: the position variance over `n` steps
is `n · C(0) + 2 · Σ_{k=1}^{n−1} (n − k) · C(k)` — the finite
Green–Kubo identity, i.e. `Σ_{k=−(n−1)}^{n−1} (n − |k|) · C(k)` with
`C(−k) = C(k)`. -/
theorem posVar_lag_form (a F σ : ℝ) (ha2 : a ^ 2 < 1) (ha : a ≠ 1)
    {N : ℕ} (n : ℕ) (hn : n ≤ N) :
    expct (fun p => (dispS (N := N) a F σ (Real.sqrt (statVar a σ))
        n p) ^ 2)
      = n * lagCov a σ 0
        + 2 * ∑ k ∈ Finset.Ico 1 n, ((n - k : ℕ) : ℝ) * lagCov a σ k := by
  rw [posVar_eq_lagSum a F σ ha2 ha n hn, statVar_mul_lagSum a σ n]

end GreenKubo
end ThetLogos
