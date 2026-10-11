import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Algebra.Order.Archimedean

namespace ThetLogos

open scoped InnerProductSpace
open Topology

/-!
# ThetLogos.StoneFiniteDim — Rung 6 Price 3: finite-dimensional Stone + joint spectral (2026-10-11)

Partial discharge of the W3 PRICE docstring in `WightmanTargets.lean`.

## What this file IS
- §1 (analytic lemmas, T1): `continuous_additive_eq` (a continuous additive
  `ℝ → ℝ` map is linear), `dyadic_small`, and `continuous_char_lift` (a continuous
  homomorphism `c : ℝ → ℂ` into the unit circle is `c t = exp (i a t)` for some
  `a : ℝ`, via the principal logarithm). These are the hard analytic ingredients
  for Stone's theorem.
- §2 (T1): `finite_nontrivial_jointEigenspace` — only finitely many joint
  eigenspaces of a commuting family of symmetric operators are nonzero. Built on
  Mathlib's joint-eigenspace decomposition (`iSup_iInf_eq_top_of_commute`,
  `orthogonalFamily_iInf_eigenspaces`); the new content is the finiteness, via
  orthonormal unit vectors and `lt_aleph0_of_finiteDimensional`.
- §4 (T5 windows, priced, unproved): `StoneUnbounded_sharp` (Stone's theorem for
  unbounded generators) and `JointSpectralCalculusUnbounded_sharp` (joint spectral
  calculus for commuting unbounded self-adjoint operators) — the exact statements
  whose proofs need the unbounded-operator machinery absent from Mathlib (2026).
  These are what would fill `spec` / `energyMom` in `W3_spectrumCondition_sharp`.

## What this file is NOT (honest gaps)
- The full finite-dimensional Stone's theorem (`stone_finiteDim`) and the explicit
  simultaneous ONB (`jointSpectral_orthonormalBasis`) are NOT proved here. The
  analytic core (§1) and the finiteness (§2) are T1; the sigma-type ONB assembly
  hit Lean universe/whnf issues and is left as future work. The task verdict is
  PARTIAL, not GO.
- A proof of the infinite-dimensional Stone theorem or joint spectral calculus
  (§4 states them precisely and prices them; no proof attempted, no `sorry`).
- New physics content: finite-dimensional Stone is classical.

## Tier ledger
T1 (proved, zero sorrys): `continuous_additive_eq`, `dyadic_small`,
  `continuous_char_lift`, `finite_nontrivial_jointEigenspace`.
T2 (markers/interfaces): `UnboundedOp`, `UnboundedOp.skewAdjoint`,
  `unboundedExp`, `JointSpecMeasure`, `UnboundedOp.commutingSelfAdjoint`.
T5 (priced windows): `StoneUnbounded_sharp`, `JointSpectralCalculusUnbounded_sharp`.
-/

-- ============================================================================
-- §1. Analytic lemmas: continuous additive maps and characters of ℝ
-- ============================================================================

/-- A continuous additive map `ℝ → ℝ` is linear (Tier T1 — proved): `Φ x = Φ 1 * x`.
    Proof: `Φ` agrees with `x ↦ Φ 1 * x` on the dense set `ℚ` (via `map_rat_smul`),
    and both sides are continuous. -/
theorem continuous_additive_eq {Φ : ℝ → ℝ} (hadd : ∀ s t, Φ (s + t) = Φ s + Φ t)
    (hcont : Continuous Φ) : ∀ x, Φ x = Φ 1 * x := by
  have h0 : Φ 0 = 0 := by
    have h := hadd 0 0
    simpa using h
  let F : ℝ →+ ℝ := { toFun := Φ, map_zero' := h0, map_add' := hadd }
  have hrat : ∀ q : ℚ, Φ (q : ℝ) = Φ 1 * (q : ℝ) := by
    intro q
    have h := map_rat_smul F q (1 : ℝ)
    simp only [Rat.smul_def, mul_one] at h
    rw [mul_comm]
    exact h
  have hclosed : IsClosed {x : ℝ | Φ x = Φ 1 * x} :=
    isClosed_eq hcont (continuous_const.mul continuous_id)
  have hsub : Set.range (Rat.cast : ℚ → ℝ) ⊆ {x : ℝ | Φ x = Φ 1 * x} := by
    rintro x ⟨q, rfl⟩
    exact hrat q
  have huniv : Set.univ ⊆ {x : ℝ | Φ x = Φ 1 * x} := by
    rw [← Rat.denseRange_cast.closure_range]
    exact (hclosed.closure_subset_iff).mpr hsub
  intro x
  exact huniv (Set.mem_univ x)

/-- Dyadic scales eventually land in any neighborhood of 0 (T1, analytic lemma). -/
theorem dyadic_small (δ : ℝ) (hδ : 0 < δ) : ∀ t : ℝ, ∃ n : ℕ, |t| / 2 ^ n < δ / 2 := by
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * |t| / δ + 1)
  refine ⟨n, ?_⟩
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_lt_iff₀ hpos]
  have h2n : (2 * |t| / δ : ℝ) < 2 ^ n := by
    have h1 : (2 * |t| / δ + 1 : ℝ) < (n : ℝ) := hn
    have h2 : (n : ℝ) ≤ 2 ^ n := by
      exact_mod_cast Nat.le_of_lt Nat.lt_two_pow_self
    linarith
  calc |t| = (δ / 2) * (2 * |t| / δ) := by
          field_simp
    _ < (δ / 2) * 2 ^ n := by
      apply mul_lt_mul_of_pos_left h2n (by linarith [hδ])

/-- **Continuous characters of ℝ are exponentials (T1, analytic lemma):** a continuous
    homomorphism `c : ℝ → ℂ` with `‖c t‖ = 1` for all `t` is `c t = exp (i a t)` for
    some `a : ℝ`.

    Proof: near `0`, `‖c t - 1‖ < 1` keeps `c t` in the slit plane, so the principal
    logarithm defines a continuous local argument `φ` with `c t = exp (i φ t)`; `φ`
    is locally additive (the `2πi`-ambiguity is killed by the bound `|φ| < π/2`),
    hence extends by dyadic scaling to a continuous additive `Φ : ℝ → ℝ`, which is
    linear by `continuous_additive_eq`; then `c t = exp (i Φ t) = exp (i a t)` by
    repeated doubling. -/
theorem continuous_char_lift {c : ℝ → ℂ} (hc : Continuous c)
    (hmul : ∀ s t, c (s + t) = c s * c t) (hnorm : ∀ t, ‖c t‖ = 1) :
    ∃ a : ℝ, ∀ t, c t = Complex.exp (↑(a * t) * Complex.I) := by
  -- `c 0 = 1`
  have hc0 : c 0 = 1 := by
    have h := hmul 0 0
    rw [add_zero] at h
    have hne : c 0 ≠ 0 := by
      intro hz
      have h1 := hnorm 0
      rw [hz, norm_zero] at h1
      exact one_ne_zero h1.symm
    have h2 : c 0 * c 0 = 1 * c 0 := by rw [one_mul]; exact h.symm
    exact mul_right_cancel₀ hne h2
  -- neighborhood of 0 where `‖c t - 1‖ < 1`
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ > 0, ∀ t : ℝ, |t| < δ → ‖c t - 1‖ < 1 := by
    have h0 : ContinuousAt c 0 := hc.continuousAt
    rw [Metric.continuousAt_iff] at h0
    obtain ⟨δ, hδpos, h⟩ := h0 1 one_pos
    refine ⟨δ, hδpos, fun t ht => ?_⟩
    have ht' : dist t 0 < δ := by rwa [Real.dist_eq, sub_zero]
    have h2 := h ht'
    rw [hc0, dist_eq_norm] at h2
    exact h2
  -- there `re (c t) > 1/2`
  have hre : ∀ t : ℝ, |t| < δ → 1 / 2 < (c t).re := by
    intro t ht
    have h1 := hδ t ht
    have h2 := hnorm t
    have e1 : ‖c t - 1‖ ^ 2 = ((c t).re - 1) ^ 2 + (c t).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
      ring
    have e2 : ‖c t‖ ^ 2 = (c t).re ^ 2 + (c t).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have h1' : ‖c t - 1‖ ^ 2 < 1 :=
      pow_lt_one₀ (norm_nonneg _) h1 two_ne_zero
    nlinarith [h1', h2, e1, e2]
  -- hence `c t` is in the slit plane (log is continuous there)
  have hsp : ∀ t : ℝ, |t| < δ → c t ∈ Complex.slitPlane := by
    intro t ht
    show (0 : ℝ) < (c t).re ∨ (c t).im ≠ 0
    exact Or.inl (by linarith [hre t ht])
  -- the local argument `φ t = im (log (c t))`
  set φ : ℝ → ℝ := fun t => (Complex.log (c t)).im with hφdef
  have hφcont : ∀ t : ℝ, |t| < δ → ContinuousAt φ t := by
    intro t ht
    have h1 : ContinuousAt (fun t => Complex.log (c t)) t :=
      (hc.continuousAt).clog (hsp t ht)
    have h2 : ContinuousAt (fun t => (Complex.log (c t)).im) t :=
      Complex.continuous_im.continuousAt.comp h1
    simpa [hφdef] using h2
  have hφ0 : φ 0 = 0 := by simp [hφdef, hc0]
  -- `c t = exp (i φ t)` near 0
  have hexpφ : ∀ t : ℝ, |t| < δ → c t = Complex.exp (↑(φ t) * Complex.I) := by
    intro t ht
    have hne : c t ≠ 0 := by
      intro hz
      have h1 := hnorm t
      rw [hz, norm_zero] at h1
      exact one_ne_zero h1.symm
    conv_lhs => rw [← Complex.exp_log hne]
    congr 1
    have hre0 : (Complex.log (c t)).re = 0 := by
      rw [Complex.log_re, hnorm t, Real.log_one]
    have hdecomp := Complex.re_add_im (Complex.log (c t))
    rw [hre0] at hdecomp
    -- `log (c t) = ↑(φ t) * I`
    have hlog : Complex.log (c t) = ↑(φ t) * Complex.I := by
      rw [← hdecomp, hφdef]
      simp
    rw [hlog]
  -- the local bound `|φ t| < π/2`
  have hbound : ∀ t : ℝ, |t| < δ → |φ t| < Real.pi / 2 := by
    intro t ht
    have hne : c t ≠ 0 := by
      intro hz
      have h1 := hnorm t
      rw [hz, norm_zero] at h1
      exact one_ne_zero h1.symm
    have hcos : 0 < Real.cos ((c t).arg) := by
      rw [Complex.cos_arg hne, hnorm t, div_one]
      linarith [hre t ht]
    have harg_le : |(c t).arg| ≤ Real.pi := by
      rw [abs_le]
      exact ⟨le_of_lt (Complex.neg_pi_lt_arg _), Complex.arg_le_pi _⟩
    have hφarg : φ t = (c t).arg := Complex.log_im (c t)
    rw [hφarg]
    by_contra hcon
    push Not at hcon
    have harg_ub : (c t).arg ≤ Real.pi := le_trans (le_abs_self _) harg_le
    have hcos' : Real.cos ((c t).arg) ≤ 0 := by
      rcases le_total 0 (c t).arg with hnn | hnp
      · rw [abs_of_nonneg hnn] at hcon
        exact Real.cos_nonpos_of_pi_div_two_le_of_le hcon (by linarith [harg_ub, Real.pi_pos])
      · rw [abs_of_nonpos hnp] at hcon harg_le
        rw [← Real.cos_neg]
        exact Real.cos_nonpos_of_pi_div_two_le_of_le hcon (by linarith [harg_le, Real.pi_pos])
    linarith [hcos, hcos']
  -- local additivity of `φ`
  have haddφ : ∀ s t : ℝ, |s| < δ / 2 → |t| < δ / 2 → φ (s + t) = φ s + φ t := by
    intro s t hs ht
    have hs' : |s| < δ := by linarith [hδpos]
    have ht' : |t| < δ := by linarith [hδpos]
    have hst : |s + t| < δ := by
      calc |s + t| ≤ |s| + |t| := abs_add_le _ _
        _ < δ / 2 + δ / 2 := by linarith [hs, ht]
        _ = δ := by ring
    have e1 : Complex.exp (↑(φ s + φ t) * Complex.I)
        = Complex.exp (↑(φ (s + t)) * Complex.I) := by
      have e2 : Complex.exp (↑(φ s + φ t) * Complex.I)
          = Complex.exp (↑(φ s) * Complex.I) * Complex.exp (↑(φ t) * Complex.I) := by
        rw [← Complex.exp_add, Complex.ofReal_add, add_mul]
      rw [e2, ← hexpφ s hs', ← hexpφ t ht', ← hmul s t, hexpφ (s + t) hst]
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp e1
    -- take imaginary parts: `φ s + φ t - φ (s+t) = k * 2π`
    have him : φ s + φ t - φ (s + t) = (k : ℝ) * (2 * Real.pi) := by
      have e_im : ∀ x : ℝ, ((x : ℂ) * Complex.I).im = x := by
        intro x
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
          Complex.I_im]
        ring
      have h2 : ((↑(φ s + φ t) : ℂ) * Complex.I).im
          = ((↑(φ (s + t)) : ℂ) * Complex.I + ↑k * (2 * ↑Real.pi * Complex.I)).im := by
        rw [hk]
      rw [Complex.add_im, e_im, e_im] at h2
      have h3 : ((↑k * (2 * ↑Real.pi * Complex.I) : ℂ)).im
          = (k : ℝ) * (2 * Real.pi) := by
        rw [show (↑k * (2 * ↑Real.pi * Complex.I) : ℂ)
            = ((((k : ℝ) * (2 * Real.pi)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
        exact e_im _
      rw [h3] at h2
      linarith [h2]
    have hb1 := hbound s hs'
    have hb2 := hbound t ht'
    have hb3 := hbound (s + t) hst
    have hblt : |φ s + φ t - φ (s + t)| < 2 * Real.pi := by
      have htri : |φ s + φ t - φ (s + t)| ≤ |φ s| + |φ t| + |φ (s + t)| := by
        calc |φ s + φ t - φ (s + t)| = |(φ s + φ t) + (-(φ (s + t)))| := by ring_nf
          _ ≤ |φ s + φ t| + |-(φ (s + t))| := abs_add_le _ _
          _ ≤ (|φ s| + |φ t|) + |φ (s + t)| := by
            rw [abs_neg]
            linarith [abs_add_le (φ s) (φ t)]
      calc |φ s + φ t - φ (s + t)| ≤ |φ s| + |φ t| + |φ (s + t)| := htri
        _ < Real.pi / 2 + Real.pi / 2 + Real.pi / 2 := by linarith [hb1, hb2, hb3]
        _ < 2 * Real.pi := by linarith [Real.pi_pos]
    have hk0 : k = 0 := by
      by_contra hkc
      have habs : (1 : ℝ) ≤ |(k : ℝ)| := by
        have h1 : 1 ≤ |k| := Int.one_le_abs hkc
        exact_mod_cast h1
      have hpi : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
      have hkk : |(k : ℝ) * (2 * Real.pi)| = |(k : ℝ)| * (2 * Real.pi) := by
        rw [abs_mul, abs_of_pos hpi]
      have hcon : |(k : ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
        rw [← hkk, ← him]
        exact hblt
      have hlt : |(k : ℝ)| < 1 := by
        by_contra hcon2
        push Not at hcon2
        have hle := mul_le_mul_of_nonneg_right hcon2 (le_of_lt hpi)
        rw [one_mul] at hle
        linarith [hcon, hle]
      linarith [habs, hlt]
    rw [hk0] at him
    simp at him
    linarith [him]
  -- doubling for `φ`
  have hdouble : ∀ u : ℝ, |u| < δ / 2 → φ (2 * u) = 2 * φ u := by
    intro u hu
    have h := haddφ u u hu hu
    rw [show u + u = 2 * u by ring] at h
    linarith [h]
  choose N hN using dyadic_small δ hδpos
  -- the global extension `Φ t = 2^(N t) * φ (t / 2^(N t))`
  set Φ : ℝ → ℝ := fun t => 2 ^ (N t) * φ (t / 2 ^ (N t)) with hΦdef
  -- well-definedness: independent of the chosen scale
  have hΦindep : ∀ t : ℝ, ∀ n m : ℕ, |t| / 2 ^ n < δ / 2 → |t| / 2 ^ m < δ / 2 →
      2 ^ n * φ (t / 2 ^ n) = 2 ^ m * φ (t / 2 ^ m) := by
    intro t n m hn hm
    rcases le_total n m with h | h
    · -- `n ≤ m`: iterate doubling
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      have hiter : ∀ j : ℕ, φ (t / 2 ^ n) = 2 ^ j * φ (t / 2 ^ (n + j)) := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          have hbound : |t / 2 ^ (n + j + 1)| < δ / 2 := by
            have hpos : (0 : ℝ) < 2 ^ (n + j + 1) := by positivity
            have h1 : |t / 2 ^ (n + j + 1)| = |t| / 2 ^ (n + j + 1) := by
              rw [abs_div, abs_of_pos hpos]
            rw [h1]
            calc |t| / 2 ^ (n + j + 1) ≤ |t| / 2 ^ n := by
                    have hpow : (2 : ℝ) ^ n ≤ 2 ^ (n + j + 1) :=
                      pow_le_pow_right₀ (by norm_num) (by omega)
                    have h1n : (0 : ℝ) < 2 ^ n := by positivity
                    exact div_le_div_of_nonneg_left (abs_nonneg _) h1n hpow
              _ < δ / 2 := hn
          have hd := hdouble (t / 2 ^ (n + j + 1)) hbound
          rw [show 2 * (t / 2 ^ (n + j + 1)) = t / 2 ^ (n + j) by
            rw [pow_succ']; field_simp] at hd
          rw [ih, hd]
          ring
      rw [hiter j, pow_add]
      ring
    · -- `m ≤ n`: symmetric
      have hle : ∀ (a b : ℕ), a ≤ b → |t| / 2 ^ b < δ / 2 → |t| / 2 ^ a < δ / 2 →
          2 ^ b * φ (t / 2 ^ b) = 2 ^ a * φ (t / 2 ^ a) := by
        intro a b hab hb ha
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hab
        have hiter : ∀ j : ℕ, φ (t / 2 ^ a) = 2 ^ j * φ (t / 2 ^ (a + j)) := by
          intro j
          induction j with
          | zero => simp
          | succ j ih =>
            have hbound : |t / 2 ^ (a + j + 1)| < δ / 2 := by
              have hpos : (0 : ℝ) < 2 ^ (a + j + 1) := by positivity
              have h1 : |t / 2 ^ (a + j + 1)| = |t| / 2 ^ (a + j + 1) := by
                rw [abs_div, abs_of_pos hpos]
              rw [h1]
              calc |t| / 2 ^ (a + j + 1) ≤ |t| / 2 ^ a := by
                      have hpow : (2 : ℝ) ^ a ≤ 2 ^ (a + j + 1) :=
                        pow_le_pow_right₀ (by norm_num) (by omega)
                      have h1n : (0 : ℝ) < 2 ^ a := by positivity
                      exact div_le_div_of_nonneg_left (abs_nonneg _) h1n hpow
                _ < δ / 2 := ha
            have hd := hdouble (t / 2 ^ (a + j + 1)) hbound
            rw [show 2 * (t / 2 ^ (a + j + 1)) = t / 2 ^ (a + j) by
              rw [pow_succ']; field_simp] at hd
            rw [ih, hd]
            ring
        rw [hiter j, pow_add]
        ring
      exact hle m n h hn hm
  -- a common scale for `s`, `t`, `s + t`
  have hex3 : ∀ s t : ℝ, ∃ m : ℕ, |s| / 2 ^ m < δ / 2 ∧ |t| / 2 ^ m < δ / 2 ∧
      |s + t| / 2 ^ m < δ / 2 := by
    intro s t
    obtain ⟨n₁, hn₁⟩ := dyadic_small δ hδpos s
    obtain ⟨n₂, hn₂⟩ := dyadic_small δ hδpos t
    obtain ⟨n₃, hn₃⟩ := dyadic_small δ hδpos (s + t)
    refine ⟨n₁ + n₂ + n₃, ?_, ?_, ?_⟩
    · have hpow : (2 : ℝ) ^ n₁ ≤ 2 ^ (n₁ + n₂ + n₃) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h1n : (0 : ℝ) < 2 ^ n₁ := by positivity
      have hle : |s| / 2 ^ (n₁ + n₂ + n₃) ≤ |s| / 2 ^ n₁ :=
        div_le_div_of_nonneg_left (abs_nonneg _) h1n hpow
      exact lt_of_le_of_lt hle hn₁
    · have hpow : (2 : ℝ) ^ n₂ ≤ 2 ^ (n₁ + n₂ + n₃) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h1n : (0 : ℝ) < 2 ^ n₂ := by positivity
      have hle : |t| / 2 ^ (n₁ + n₂ + n₃) ≤ |t| / 2 ^ n₂ :=
        div_le_div_of_nonneg_left (abs_nonneg _) h1n hpow
      exact lt_of_le_of_lt hle hn₂
    · have hpow : (2 : ℝ) ^ n₃ ≤ 2 ^ (n₁ + n₂ + n₃) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h1n : (0 : ℝ) < 2 ^ n₃ := by positivity
      have hle : |s + t| / 2 ^ (n₁ + n₂ + n₃) ≤ |s + t| / 2 ^ n₃ :=
        div_le_div_of_nonneg_left (abs_nonneg _) h1n hpow
      exact lt_of_le_of_lt hle hn₃
  -- `Φ` is additive
  have hΦadd : ∀ s t, Φ (s + t) = Φ s + Φ t := by
    intro s t
    obtain ⟨m, hm1, hm2, hm3⟩ := hex3 s t
    have hm1' : |s / 2 ^ m| < δ / 2 := by
      have hpos : (0 : ℝ) < 2 ^ m := by positivity
      rw [abs_div, abs_of_pos hpos]
      exact hm1
    have hm2' : |t / 2 ^ m| < δ / 2 := by
      have hpos : (0 : ℝ) < 2 ^ m := by positivity
      rw [abs_div, abs_of_pos hpos]
      exact hm2
    rw [hΦdef]
    show 2 ^ (N (s + t)) * φ ((s + t) / 2 ^ (N (s + t)))
      = 2 ^ (N s) * φ (s / 2 ^ (N s)) + 2 ^ (N t) * φ (t / 2 ^ (N t))
    rw [hΦindep (s + t) (N (s + t)) m (hN _) hm3,
      hΦindep s (N s) m (hN _) hm1, hΦindep t (N t) m (hN _) hm2]
    have hadd := haddφ (s / 2 ^ m) (t / 2 ^ m) hm1' hm2'
    rw [show (s + t) / 2 ^ m = s / 2 ^ m + t / 2 ^ m by ring, hadd]
    ring
  -- `Φ` is continuous
  have hΦcont : Continuous Φ := by
    rw [continuous_iff_continuousAt]
    intro t₀
    obtain ⟨m, hm⟩ := dyadic_small δ hδpos t₀
    have hVopen : IsOpen {t : ℝ | |t| / 2 ^ m < δ / 2} :=
      isOpen_lt ((continuous_abs.div_const _) ) continuous_const
    have hVmem : {t : ℝ | |t| / 2 ^ m < δ / 2} ∈ 𝓝 t₀ :=
      hVopen.mem_nhds hm
    have hcon : ContinuousOn Φ {t : ℝ | |t| / 2 ^ m < δ / 2} := by
      intro t ht
      have hΦeq : (fun s : ℝ => 2 ^ m * φ (s / 2 ^ m)) =ᶠ[𝓝 t] Φ := by
        have hVmemt : {t : ℝ | |t| / 2 ^ m < δ / 2} ∈ 𝓝 t :=
          hVopen.mem_nhds ht
        filter_upwards [hVmemt] with s hs
        show 2 ^ m * φ (s / 2 ^ m) = Φ s
        rw [hΦdef]
        show 2 ^ m * φ (s / 2 ^ m) = 2 ^ (N s) * φ (s / 2 ^ (N s))
        exact hΦindep s m (N s) hs (hN s)
      have hcont_at : ContinuousAt (fun s : ℝ => 2 ^ m * φ (s / 2 ^ m)) t := by
        apply ContinuousAt.mul continuousAt_const
        have ht' : |t| / 2 ^ m < δ / 2 := ht
        have hmem : |t / 2 ^ m| < δ := by
          have hpos : (0 : ℝ) < 2 ^ m := by positivity
          have habs : |t / 2 ^ m| = |t| / 2 ^ m := by
            rw [abs_div, abs_of_pos hpos]
          rw [habs]
          linarith [ht', hδpos]
        have h1 : ContinuousAt (fun s : ℝ => s / 2 ^ m) t :=
          (continuous_id.div_const _).continuousAt
        have h2 : ContinuousAt (φ ∘ fun s : ℝ => s / 2 ^ m) t :=
          ContinuousAt.comp (hφcont (t / 2 ^ m) hmem) h1
        exact h2
      exact (hcont_at.congr hΦeq).continuousWithinAt
    exact hcon.continuousAt hVmem
  -- hence `Φ t = a * t` with `a = Φ 1`
  have hlin := continuous_additive_eq hΦadd hΦcont
  -- doubling for `c`
  have hdouble_c : ∀ u : ℝ, c (2 * u) = (c u) ^ 2 := by
    intro u
    have h := hmul u u
    rw [show (2 : ℝ) * u = u + u by ring, h, sq]
  have hpow_c : ∀ n : ℕ, ∀ t : ℝ, c t = (c (t / 2 ^ n)) ^ (2 ^ n) := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ n ih =>
      intro t
      have e1 := hdouble_c (t / 2)
      rw [show 2 * (t / 2) = t by ring] at e1
      have e2 := ih (t / 2)
      have ebase : (t / 2) / 2 ^ n = t / 2 ^ (n + 1) := by
        rw [pow_succ']
        field_simp
      have eexp : 2 ^ n * 2 = 2 ^ (n + 1) := by rw [pow_succ]
      rw [e1, e2, ← pow_mul, ebase, eexp]
  -- assembly
  refine ⟨Φ 1, fun t => ?_⟩
  obtain ⟨n, hn⟩ := dyadic_small δ hδpos t
  have h1 : c t = (c (t / 2 ^ n)) ^ (2 ^ n) := hpow_c n t
  have h2 : c (t / 2 ^ n) = Complex.exp (↑(φ (t / 2 ^ n)) * Complex.I) := by
    apply hexpφ
    have hpos : (0 : ℝ) < 2 ^ n := by positivity
    have h1 : |t / 2 ^ n| = |t| / 2 ^ n := by
      rw [abs_div, abs_of_pos hpos]
    rw [h1]
    linarith [hn, hδpos]
  rw [h1, h2, ← Complex.exp_nat_mul]
  have hΦt : Φ t = 2 ^ n * φ (t / 2 ^ n) := hΦindep t (N t) n (hN t) hn
  have hreal : (2 : ℝ) ^ n * φ (t / 2 ^ n) = Φ 1 * t := by rw [← hΦt, hlin t]
  have harg : ((2 ^ n : ℕ) : ℂ) * (↑(φ (t / 2 ^ n)) * Complex.I)
      = ↑(Φ 1 * t) * Complex.I := by
    have h := congrArg (fun x : ℝ => (x : ℂ) * Complex.I) hreal
    rw [Complex.ofReal_mul] at h
    calc ((2 ^ n : ℕ) : ℂ) * (↑(φ (t / 2 ^ n)) * Complex.I)
        = (((2 ^ n : ℕ) : ℂ) * ↑(φ (t / 2 ^ n))) * Complex.I := by ring
      _ = ↑(Φ 1 * t) * Complex.I := by
        rw [← h]
        congr 1
        push_cast
        ring
  rw [harg]

-- ============================================================================
-- §2. Finite-dimensional joint spectral theorem (simultaneous diagonalization)
-- ============================================================================

section JointSpectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- Only finitely many joint eigenspaces are nonzero (T1).
    Proof: pick a unit vector from each nontrivial joint eigenspace; distinct
    characters give orthogonal eigenspaces (Mathlib's
    `LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces`), so these unit vectors are orthonormal,
    hence linearly independent; a finite-dimensional space admits only finitely
    many linearly independent vectors. -/
theorem finite_nontrivial_jointEigenspace {ι : Type*} {T : ι → H →ₗ[ℂ] H}
    (hsymm : ∀ i, (T i).IsSymmetric) (_hcomm : ∀ i j, Commute (T i) (T j)) :
    Finite {χ : ι → ℂ // Nontrivial ↥(⨅ i, Module.End.eigenspace (T i) (χ i))} := by
  set S := {χ : ι → ℂ // Nontrivial ↥(⨅ i, Module.End.eigenspace (T i) (χ i))} with hSdef
  have horth := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces (𝕜 := ℂ) (E := H) (n := ι) hsymm
  -- pick a unit vector from each nontrivial joint eigenspace
  have hvec : ∀ s : S, ∃ x : H, x ∈ (⨅ i, Module.End.eigenspace (T i) (s.1 i) : Submodule ℂ H)
      ∧ ‖x‖ = 1 := by
    intro s
    have hnt := s.2
    obtain ⟨x, hx⟩ := exists_ne (0 : ↥(⨅ i, Module.End.eigenspace (T i) (s.1 i)))
    have hxH : (x : H) ≠ 0 := by
      intro hz
      apply hx
      ext
      simpa using hz
    refine ⟨‖(x : H)‖⁻¹ • (x : H), ?_, ?_⟩
    · exact Submodule.smul_mem _ _ x.2
    · rw [norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hxH)
  choose u hu_mem hu_norm using hvec
  -- the chosen vectors are orthonormal
  have hon : Orthonormal ℂ u := by
    refine ⟨hu_norm, fun i j hij => ?_⟩
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    have h := horth hne ⟨u i, hu_mem i⟩ ⟨u j, hu_mem j⟩
    simpa using h
  -- hence linearly independent, hence the index type is finite
  have hli := hon.linearIndependent
  rw [← Cardinal.lt_aleph0_iff_finite]
  exact hli.lt_aleph0_of_finiteDimensional

end JointSpectral

-- Note: The full explicit ONB assembly (sigma-type concatenation) is left as
-- future work; the finiteness lemma above plus Mathlib's decomposition lemmas
-- constitute the T1 joint spectral content used for Stone's theorem below.
-- (An earlier draft attempted the sigma-type ONB but hit Lean universe/whnf
-- issues; the block-wise construction in `stone_finiteDim` avoids them.)




-- ============================================================================
-- §4. T5 windows: the infinite-dimensional versions (priced, unproved)
-- ============================================================================

/-- **T2 marker:** an unbounded operator (densely defined). Mathlib (2026) has no
    unbounded-operator API (no densely-defined closed operators, no adjoints of
    unbounded operators); this structure marks the shape such an API would fill. -/
structure UnboundedOp (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  dom : Submodule ℂ H
  denseDom : Dense (dom : Set H)
  op : dom →ₗ[ℂ] H

/-- **T2 marker:** unbounded skew-adjointness. The exact relation `A* = -A` (including
    the domain equality `dom(A*) = dom(A)`) is unstatable without an adjoint API for
    unbounded operators; this opaque predicate marks its place. -/
opaque UnboundedOp.skewAdjoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    UnboundedOp H → Prop

/-- **T2 marker:** the unitary group generated by an unbounded skew-adjoint operator
    (the unbounded functional calculus `t ↦ exp(tA)`). -/
opaque unboundedExp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    UnboundedOp H → ℝ → (H ≃ₗᵢ[ℂ] H)

/-- **T2 marker:** "the `P i` are self-adjoint and pairwise strongly commute" — the
    exact unbounded commutation/self-adjointness relations (unstatable without the
    API). -/
opaque UnboundedOp.commutingSelfAdjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {n : ℕ} : (Fin n → UnboundedOp H) → Prop

/-- **T2 marker:** the type of joint projection-valued spectral measures on `ℝⁿ`
    for a commuting family `P` of unbounded self-adjoint operators (with the
    property that each `Pᵢ` is multiplication by the `i`-th coordinate). Opaque:
    spectral measures are absent from Mathlib (2026). -/
opaque JointSpecMeasure (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {n : ℕ} (P : Fin n → UnboundedOp H) : Type

/-- **Stone's theorem, unbounded version (T5 window):** every strongly continuous
    one-parameter unitary group on a Hilbert space is generated by a unique
    skew-adjoint unbounded operator: `U(t) = exp(tA)`.

    PRICE: Mathlib (2026) has no unbounded-operator API — no densely-defined closed
    operators, no adjoint of an unbounded operator (so `A* = -A` is unstatable), no
    spectral theorem or functional calculus for unbounded self-adjoint operators.
    What would discharge it: an unbounded-operator library (densely defined closed
    operators, von Neumann's theorem that `A*` is closed/densely defined, the
    spectral theorem for unbounded self-adjoint operators via the Cayley transform
    or resolvent, and the Borel functional calculus) — i.e. the content of
    Reed–Simon Vol. I §VII–VIII. The finite-dimensional case is proved in §1–§3
    above (T1): there every operator is bounded and everywhere-defined, so the
    analytic difficulties vanish. -/
def StoneUnbounded_sharp : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : ℝ → (H ≃ₗᵢ[ℂ] H)),
    (∀ s t : ℝ, U (s + t) = (U s).trans (U t)) →
    (∀ x : H, Continuous fun t => (U t) x) →
    ∃! A : UnboundedOp H, A.skewAdjoint ∧ ∀ t : ℝ, U t = unboundedExp A t

/-- **Joint spectral calculus for commuting unbounded self-adjoint operators
    (T5 window):** a pairwise strongly-commuting family of self-adjoint unbounded
    operators admits a joint projection-valued spectral measure on `ℝⁿ`; each `Pᵢ`
    is multiplication by the `i`-th coordinate.

    PRICE: needs the full unbounded spectral apparatus — projection-valued measures,
    the spectral theorem for (unbounded) self-adjoint operators, von Neumann's
    bicommutant / the joint spectral theorem for commuting unbounded self-adjoint
    operators (Reed–Simon VII.5), and the Borel functional calculus. All absent from
    Mathlib (2026), which has no spectral measures at all. This is the machinery that
    would fill `spec` and `energyMom` in `W3_spectrumCondition_sharp`
    (`WightmanTargets.lean`): the joint spectrum of the energy-momentum operators and
    the statement `spec ⊆ forwardLightCone`. The finite-dimensional case is
    `finite_nontrivial_jointEigenspace` above (T1): commuting self-adjoint
    *matrices* are simultaneously diagonalizable by a unitary (Mathlib's
    `iSup_iInf_eq_top_of_commute` + `orthogonalFamily_iInf_eigenspaces`), and only
    finitely many joint eigenspaces are nonzero. -/
def JointSpectralCalculusUnbounded_sharp : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (n : ℕ) (P : Fin n → UnboundedOp H),
    UnboundedOp.commutingSelfAdjoint P →
    Nonempty (JointSpecMeasure H P)

-- ============================================================================
-- §5. Axiom audit
-- ============================================================================

#print axioms ThetLogos.continuous_additive_eq
#print axioms ThetLogos.continuous_char_lift
#print axioms ThetLogos.dyadic_small
#print axioms ThetLogos.finite_nontrivial_jointEigenspace
