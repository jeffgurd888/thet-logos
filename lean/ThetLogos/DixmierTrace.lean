import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace ThetLogos

open Filter Topology Finset

/-!
# ThetLogos.DixmierTrace — Round 2 intake: the Dixmier trace, pinned and tested at finite level

Dossier: `whitepaper/dixmier-trace-2026-10-18.md`. Priced **S–M** by the
parked-fleet gauntlet (`whitepaper/gauntlet-parked-fleet-2026-10-17.md`
§8): "Dixmier trace / noncommutative integration — stands as an intake,
**S–M**. … At finite level the Dixmier trace on the finite triple is a
finite, computable shadow (the noncommutative integral as a
residue/trace functional on the finite algebra) — a FIT-at-finite-level
verdict is there to be tested with real theorems; the continuum
Dixmier trace (singular traces on compacts, measurability) is the
predictable NO-FIT/window half, needing the analytic house Round 1
already fenced."

## Audit (grep-backed, pinned Mathlib v4.35.0-rc3)

- `grep -ri "dixmier" Mathlib/` — **zero hits**. No Dixmier trace, no
  singular traces on compact operators, no operator ideal `L^{1,∞}`,
  no measurability theory.
- `grep -ri "banach limit" Mathlib/`, `grep "banachLimit"` — **zero
  hits**. No Banach limit / generalized limit exists to instantiate.
- `grep -ri "dixmier\|banach" lean/ThetLogos/` — **zero hits**. The
  corpus had no Dixmier material at all before this module.
- What Mathlib DOES have, and this module uses: harmonic numbers with
  `tendsto_harmonic_sub_log_add_one` (Euler–Mascheroni), infinite sums
  (`Summable`, `sum_le_tsum`), `Real.tendsto_log_atTop`. An
  ultrafilter-limit construction (`Ultrafilter.lim`, for compact
  Hausdorff targets) exists but does not instantiate the pin below:
  `ℝ` is not compact, and no dilation-invariant state on `ℓ∞(ℕ)` is
  available.

## What this module is

§1 pins the two objects. A **profile** is a sequence `μ : ℕ → ℝ`,
read as the eigenvalue/singular-value profile of a positive compact
operator (the operator itself is continuum house — absent, above).
A **generalized limit** is pinned *as data* (`GenLimit`, tier T2):
a linear, positive functional on sequences which extends ordinary
limits. The **Dixmier trace** of `μ` relative to `ω` is the `ω`-value
of `μ`'s logarithmic means. Existence of any `GenLimit` is a
Hahn–Banach fact in the literature (T4); it is **not** proved here,
and no theorem below needs it — every theorem is universally
quantified over `ω`, as an intake pin should be.

§2–§6 are T1 theorems about the pinned objects: the logarithmic
mean's algebra (§2); vanishing for bounded-partial-sum, summable, and
eventually-zero profiles (§3); ω-independence (the measurability
criterion) and the Dixmier trace's algebra (§4); the finite-spectrum
evaluation — every finitely supported profile has trace zero under
every `ω` (§5); and the harmonic profile `n ↦ c/(n+1)`, whose
Dixmier trace is exactly `c` under every `ω` (§6).

## Fences (read before citing)

- NO Dixmier trace on any operator is constructed. There is no
  operator ideal, no compact-operator theory, no trace-class theory
  in this module; profiles are sequences, full stop.
- NO spectral-dimension claim for any object, finite or continuum.
- The finite-level verdict is a *theorem*, not an absence: every
  finitely supported profile — in particular the zero-padded
  eigenvalue list of any finite operator, e.g. of the finite
  triple's `buildDirac` (`SpectralActionFinite`) — has Dixmier
  trace **zero** under every generalized limit (§5). A nonzero
  finite Dixmier trace is impossible in principle, not merely
  unbuilt. At finite level the noncommutative-integral slot is
  occupied by the ordinary trace (the partial-sum limit), which is
  what the corpus's spectral action already uses (`Tr(D^{2k})`).
  This sharpens the gauntlet's predicted "finite computable
  shadow": the shadow is computable, and for the Dixmier trace
  proper it is zero (see the dossier, deviation note D1).
- The harmonic-profile theorem (§6) is a statement about the
  sequence `n ↦ c/(n+1)` — in the literature (T4) the eigenvalue
  profile of `|D|^{-d}` on a closed `d`-manifold — evaluated inside
  the pinned machinery. It is not a computation on any corpus
  operator, and no corpus operator is `|D|^{-d}` of anything.
-/

/-! ## §1. The pinned objects -/

/-- Partial sums of a profile: `σ_N = ∑_{n<N} μ n`. -/
def partialSum (μ : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, μ n

/-- Logarithmic mean of a profile at scale `N`:
`σ_N / log (N + 2)`. (The `+2` shift against the literature's
`log (1 + N)` is an indexing convention keeping the denominator
positive at every `N`; it changes no limit statement.) -/
noncomputable def logMean (μ : ℕ → ℝ) (N : ℕ) : ℝ :=
  partialSum μ N / Real.log ((N : ℝ) + 2)

/-- A **generalized limit**, pinned as data (T2): a linear, positive
functional on real sequences which agrees with the ordinary limit
on convergent sequences. This is the sequence-level content of a
Banach limit / Dixmier state `ω`. Dilation invariance — the extra
axiom the continuum theory imposes so that the induced functional
on operators is a trace — is *not* part of this pin: no statement
in this module needs it, and it is named here so its absence is a
recorded scoping decision, not an oversight. -/
structure GenLimit where
  /-- The functional itself. -/
  toFun : (ℕ → ℝ) → ℝ
  /-- Additivity. -/
  map_add' : ∀ x y : ℕ → ℝ, toFun (x + y) = toFun x + toFun y
  /-- Homogeneity. -/
  map_smul' : ∀ (c : ℝ) (x : ℕ → ℝ), toFun (c • x) = c * toFun x
  /-- Positivity. -/
  nonneg' : ∀ x : ℕ → ℝ, (∀ n, 0 ≤ x n) → 0 ≤ toFun x
  /-- It extends the ordinary limit. -/
  eq_of_tendsto' : ∀ (x : ℕ → ℝ) (a : ℝ), Tendsto x atTop (𝓝 a) → toFun x = a

/-- The **Dixmier trace** of a profile `μ` relative to a generalized
limit `ω`: the `ω`-value of `μ`'s logarithmic means. -/
noncomputable def dixmierTrace (ω : GenLimit) (μ : ℕ → ℝ) : ℝ :=
  ω.toFun (logMean μ)

/-- Auxiliary: the logarithmic denominator is positive at every scale. -/
theorem log_add_two_pos (N : ℕ) : 0 < Real.log ((N : ℝ) + 2) := by
  apply Real.log_pos
  have h : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  linarith

/-- Auxiliary: the logarithmic denominator never vanishes. -/
theorem log_add_two_ne_zero (N : ℕ) : Real.log ((N : ℝ) + 2) ≠ 0 :=
  ne_of_gt (log_add_two_pos N)

/-! ## §2. Algebra of the logarithmic mean (T1) -/

/-- The logarithmic mean is additive in the profile. -/
theorem logMean_add (μ ν : ℕ → ℝ) (N : ℕ) :
    logMean (μ + ν) N = logMean μ N + logMean ν N := by
  unfold logMean partialSum
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib]
  exact add_div _ _ _

/-- The logarithmic mean is homogeneous in the profile. -/
theorem logMean_smul (c : ℝ) (μ : ℕ → ℝ) (N : ℕ) :
    logMean (c • μ) N = c * logMean μ N := by
  unfold logMean partialSum
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, mul_div_assoc]

/-- Logarithmic means of a nonnegative profile are nonnegative. -/
theorem logMean_nonneg {μ : ℕ → ℝ} (hμ : ∀ n, 0 ≤ μ n) (N : ℕ) :
    0 ≤ logMean μ N :=
  div_nonneg (Finset.sum_nonneg (fun n _ => hμ n)) (le_of_lt (log_add_two_pos N))

/-- The logarithmic mean is monotone in the profile. -/
theorem logMean_mono {μ ν : ℕ → ℝ} (h : ∀ n, μ n ≤ ν n) (N : ℕ) :
    logMean μ N ≤ logMean ν N :=
  (div_le_div_iff_of_pos_right (log_add_two_pos N)).mpr
    (Finset.sum_le_sum (fun n _ => h n))

/-! ## §3. Vanishing theorems (T1)

The Dixmier trace is a *singular* trace: it vanishes on everything
whose partial sums do not grow logarithmically. Three increasingly
special forms: bounded partial sums, summable profiles, and
eventually-zero (finite) profiles. -/

/-- Bounded partial sums have logarithmic means tending to `0`. -/
theorem tendsto_logMean_of_bdd_partialSum {μ : ℕ → ℝ} {C : ℝ}
    (hC : ∀ N, ‖partialSum μ N‖ ≤ C) :
    Tendsto (logMean μ) atTop (𝓝 0) := by
  have hden : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have hC' : Tendsto (fun N : ℕ => C / Real.log ((N : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  refine squeeze_zero_norm' (Filter.Eventually.of_forall ?_) hC'
  intro N
  have hnorm : ‖Real.log ((N : ℝ) + 2)‖ = Real.log ((N : ℝ) + 2) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (log_add_two_pos N))]
  unfold logMean
  rw [norm_div, hnorm]
  exact (div_le_div_iff_of_pos_right (log_add_two_pos N)).mpr (hC N)

/-- A summable profile has logarithmic means tending to `0`:
its partial sums are bounded by `∑' ‖μ‖`. -/
theorem tendsto_logMean_of_summable {μ : ℕ → ℝ} (hμ : Summable μ) :
    Tendsto (logMean μ) atTop (𝓝 0) := by
  apply tendsto_logMean_of_bdd_partialSum (C := ∑' n, ‖μ n‖)
  intro N
  calc ‖partialSum μ N‖
      = ‖∑ n ∈ Finset.range N, μ n‖ := rfl
    _ ≤ ∑ n ∈ Finset.range N, ‖μ n‖ := norm_sum_le _ _
    _ ≤ ∑' n, ‖μ n‖ := by
        have hnorm : Summable (fun n => ‖μ n‖) := by
          simpa only [Real.norm_eq_abs] using (summable_abs_iff.mpr hμ)
        exact hnorm.sum_le_tsum _ (fun n _ => norm_nonneg _)

/-- Past its support, a finite profile's partial sums are constant. -/
theorem partialSum_eq_of_eventually_zero {μ : ℕ → ℝ} {N₀ : ℕ}
    (hμ : ∀ n ≥ N₀, μ n = 0) {N : ℕ} (hN : N₀ ≤ N) :
    partialSum μ N = partialSum μ N₀ := by
  unfold partialSum
  symm
  apply Finset.sum_subset (Finset.range_mono hN)
  intro n hn hn₀
  apply hμ
  simp only [Finset.mem_range] at hn hn₀
  omega

/-- An eventually-zero (finite) profile has logarithmic means
tending to `0`. -/
theorem tendsto_logMean_of_eventually_zero {μ : ℕ → ℝ} {N₀ : ℕ}
    (hμ : ∀ n ≥ N₀, μ n = 0) :
    Tendsto (logMean μ) atTop (𝓝 0) := by
  apply tendsto_logMean_of_bdd_partialSum (C := ∑ n ∈ Finset.range N₀, ‖μ n‖)
  intro N
  rcases le_total N₀ N with h | h
  · rw [partialSum_eq_of_eventually_zero hμ h]
    exact norm_sum_le _ _
  · calc ‖partialSum μ N‖
        ≤ ∑ n ∈ Finset.range N, ‖μ n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range N₀, ‖μ n‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
            (fun n _ _ => norm_nonneg _)

/-! ## §4. ω-independence and the Dixmier trace's algebra (T1)

The classical word is **measurability**: a profile whose logarithmic
means converge has the same Dixmier trace under *every* generalized
limit — the value does not depend on the choice of `ω`. That is the
entire content of measurability available at sequence level, and it
is a one-line consequence of the pin. -/

/-- **Measurability criterion.** If the logarithmic means of `μ`
converge to `a`, then `dixmierTrace ω μ = a` for every generalized
limit `ω`. -/
theorem dixmierTrace_of_tendsto_logMean {ω : GenLimit} {μ : ℕ → ℝ} {a : ℝ}
    (h : Tendsto (logMean μ) atTop (𝓝 a)) :
    dixmierTrace ω μ = a :=
  ω.eq_of_tendsto' _ _ h

/-- Every eventually-zero profile has Dixmier trace `0` under
every generalized limit. -/
theorem dixmierTrace_eq_zero_of_eventually_zero (ω : GenLimit) {μ : ℕ → ℝ}
    {N₀ : ℕ} (hμ : ∀ n ≥ N₀, μ n = 0) :
    dixmierTrace ω μ = 0 :=
  dixmierTrace_of_tendsto_logMean (tendsto_logMean_of_eventually_zero hμ)

/-- Every summable profile has Dixmier trace `0` under every
generalized limit. -/
theorem dixmierTrace_eq_zero_of_summable (ω : GenLimit) {μ : ℕ → ℝ}
    (hμ : Summable μ) :
    dixmierTrace ω μ = 0 :=
  dixmierTrace_of_tendsto_logMean (tendsto_logMean_of_summable hμ)

/-- The Dixmier trace is additive in the profile. -/
theorem dixmierTrace_add (ω : GenLimit) (μ ν : ℕ → ℝ) :
    dixmierTrace ω (μ + ν) = dixmierTrace ω μ + dixmierTrace ω ν := by
  have h : logMean (μ + ν) = logMean μ + logMean ν :=
    funext (logMean_add μ ν)
  unfold dixmierTrace
  rw [h]
  exact ω.map_add' _ _

/-- The Dixmier trace is homogeneous in the profile. -/
theorem dixmierTrace_smul (ω : GenLimit) (c : ℝ) (μ : ℕ → ℝ) :
    dixmierTrace ω (c • μ) = c * dixmierTrace ω μ := by
  have h : logMean (c • μ) = c • logMean μ :=
    funext (logMean_smul c μ)
  unfold dixmierTrace
  rw [h]
  exact ω.map_smul' c _

/-- The Dixmier trace of a nonnegative profile is nonnegative. -/
theorem dixmierTrace_nonneg (ω : GenLimit) {μ : ℕ → ℝ} (hμ : ∀ n, 0 ≤ μ n) :
    0 ≤ dixmierTrace ω μ :=
  ω.nonneg' _ (fun N => logMean_nonneg hμ N)

/-! ## §5. The finite-spectrum evaluation (T1)

A finite operator's eigenvalue/singular-value list, padded with
zeros, is an eventually-zero profile. Hence — as a theorem, under
every generalized limit — **the Dixmier trace of every finite
spectrum is zero**. This is the finite-level verdict of the intake:
the Dixmier trace proper is identically zero at finite level (it is
a singular trace; finite-rank operators are exactly its kernel),
and no nonzero "finite Dixmier trace" exists to be fitted. The
noncommutative-integral slot at finite level is the ordinary trace —
the partial-sum limit of §3's machinery with the logarithm removed —
which the corpus already owns (`SpectralActionFinite`). -/

/-- A finite list of reals, zero-padded to a profile: the eigenvalue
list of a finite operator, as a sequence. -/
def padProfile {n : ℕ} (v : Fin n → ℝ) : ℕ → ℝ :=
  fun k => if h : k < n then v ⟨k, h⟩ else 0

/-- The padded profile vanishes past the list's length. -/
theorem padProfile_apply_of_ge {n : ℕ} (v : Fin n → ℝ) {k : ℕ} (hk : n ≤ k) :
    padProfile v k = 0 := by
  have h : ¬ k < n := Nat.not_lt.mpr hk
  simp [padProfile, h]

/-- A padded finite profile has logarithmic means tending to `0`. -/
theorem tendsto_logMean_padProfile {n : ℕ} (v : Fin n → ℝ) :
    Tendsto (logMean (padProfile v)) atTop (𝓝 0) :=
  tendsto_logMean_of_eventually_zero (N₀ := n)
    (fun _k hk => padProfile_apply_of_ge v hk)

/-- **Finite evaluation.** Every finite spectrum — every list
`v : Fin n → ℝ`, e.g. an eigenvalue list of the finite triple's
Dirac operator — has Dixmier trace `0` under every generalized
limit. -/
theorem dixmierTrace_padProfile (ω : GenLimit) {n : ℕ} (v : Fin n → ℝ) :
    dixmierTrace ω (padProfile v) = 0 :=
  dixmierTrace_of_tendsto_logMean (tendsto_logMean_padProfile v)

/-! ## §6. The harmonic profile (T1)

The profile `n ↦ c/(n+1)`: partial sums are the harmonic numbers,
which grow exactly like `log`, so the logarithmic means converge
to `c` — the profile is measurable with value `c`, under every `ω`.
In the literature (T4) this is the eigenvalue profile of
`|D|^{-d}` on a closed `d`-dimensional manifold, and the statement
below is the sequence-level content of "the Dixmier trace reads
off the Wodzicki residue". No operator appears here. -/

/-- The harmonic profile with residue constant `c`. -/
noncomputable def harmProfile (c : ℝ) : ℕ → ℝ :=
  fun n => c / ((n : ℝ) + 1)

/-- Partial sums of the unit harmonic profile are the harmonic
numbers. -/
theorem partialSum_harmProfile_one (N : ℕ) :
    partialSum (harmProfile 1) N = (harmonic N : ℝ) := by
  unfold partialSum harmProfile harmonic
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  rw [one_div]

/-- The harmonic numerator estimate, shifted to this module's
denominator convention: `H_N − log (N + 2) → γ`. From Mathlib's
`Real.tendsto_harmonic_sub_log_add_one` plus
`log (N + 1) − log (N + 2) → 0`. -/
theorem tendsto_harmonic_sub_log_add_two :
    Tendsto (fun N : ℕ => (harmonic N : ℝ) - Real.log ((N : ℝ) + 2))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
  have hB : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) - Real.log ((N : ℝ) + 2))
      atTop (𝓝 0) := by
    have hratio : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / ((N : ℝ) + 2)) atTop (𝓝 1) := by
      have h1 : Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
      have heq : ∀ N : ℕ, ((N : ℝ) + 1) / ((N : ℝ) + 2) = 1 - 1 / ((N : ℝ) + 2) := by
        intro N
        have h2 : ((N : ℝ) + 2) ≠ 0 := by
          have h : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
          positivity
        field_simp
        ring
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub h1
      rw [sub_zero] at this
      exact this.congr (fun N => (heq N).symm)
    have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
    rw [Real.log_one] at hlog
    refine hlog.congr (fun N => ?_)
    simp only [Function.comp_apply]
    rw [Real.log_div]
    · have h : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      positivity
    · have h : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      positivity
  have h := Real.tendsto_harmonic_sub_log_add_one.add hB
  rw [add_zero] at h
  refine h.congr (fun N => ?_)
  ring

/-- The logarithmic means of the unit harmonic profile tend to `1`. -/
theorem tendsto_logMean_harmProfile_one :
    Tendsto (logMean (harmProfile 1)) atTop (𝓝 1) := by
  have hden : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have hfrac : Tendsto
      (fun N : ℕ => ((harmonic N : ℝ) - Real.log ((N : ℝ) + 2)) / Real.log ((N : ℝ) + 2))
      atTop (𝓝 0) :=
    tendsto_harmonic_sub_log_add_two.div_atTop hden
  have hEq : ∀ N : ℕ, logMean (harmProfile 1) N
      = ((harmonic N : ℝ) - Real.log ((N : ℝ) + 2)) / Real.log ((N : ℝ) + 2) + 1 := by
    intro N
    rw [logMean, partialSum_harmProfile_one]
    have hL := log_add_two_ne_zero N
    rw [sub_div, div_self hL]
    ring
  have h := hfrac.add (tendsto_const_nhds (x := (1 : ℝ)))
  rw [zero_add] at h
  exact h.congr (fun N => (hEq N).symm)

/-- The logarithmic means of the harmonic profile tend to `c`. -/
theorem tendsto_logMean_harmProfile (c : ℝ) :
    Tendsto (logMean (harmProfile c)) atTop (𝓝 c) := by
  have hsmul : harmProfile c = c • harmProfile 1 := by
    funext n
    simp only [harmProfile, Pi.smul_apply, smul_eq_mul]
    rw [mul_one_div]
  rw [hsmul]
  have h : Tendsto (fun N => c * logMean (harmProfile 1) N) atTop (𝓝 (c * 1)) :=
    tendsto_logMean_harmProfile_one.const_mul c
  rw [mul_one] at h
  exact h.congr (fun N => (logMean_smul c (harmProfile 1) N).symm)

/-- **Harmonic evaluation.** The harmonic profile has Dixmier trace
exactly `c`, under every generalized limit. -/
theorem dixmierTrace_harmProfile (ω : GenLimit) (c : ℝ) :
    dixmierTrace ω (harmProfile c) = c :=
  dixmierTrace_of_tendsto_logMean (tendsto_logMean_harmProfile c)
