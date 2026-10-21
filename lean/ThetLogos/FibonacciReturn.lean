import Mathlib.Tactic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecificLimits.Basic
import ThetLogos.FluxTwist

open Filter Topology

/-!
# ThetLogos.FibonacciReturn — Fibonacci counts and the golden-angle return (T1 target)

HONESTY LEDGER (read before citing):

- This module is a **pure-mathematics gauntlet**, built 2026-10-20 from
  Jeff's fragment: "whatever reverses/or balances π back to ground …
  Fibonacci."  The vague sentence was pinned to the strongest exact
  statement it can honestly carry, and the false reading was killed in
  the same module.
- Let `ψ = (1 - √5) / 2` be Mathlib's `Real.goldenConj`.  The golden
  angle is `α = 2πψ²` (equivalently `2π / φ²`).  The step operator is
  one rotation through `α` in a single phase plane, read through the
  corpus's existing `phaseOf` from `ThetLogos.FluxTwist`.
- **What is proved:** after `F_{n+2}` golden-angle steps, the angle
  differs from `F_n` whole turns by exactly `2πψ^{n+2}`.  The residual
  is never zero, consecutive residuals lie on opposite sides of ground,
  and the residual tends to zero; hence the phase tends to ground
  (`1`) without ever reaching it at a finite Fibonacci count.
- **What is killed:** the claim that a finite Fibonacci count returns
  the golden-angle step *exactly* to ground.  It does not, for any
  `n`, relative to any integer number of whole turns.
- **Fences:** this is a theorem about one scalar phase.  It is not a
  4D dynamics theorem, not a physical mechanism, not a mass law, and
  not a resurrection of the φ-tower: the standing kill on φ-power
  scaling of physical masses is untouched.  Fibonacci enters here
  only as an index sequence for step counts in an exact identity.
- Status: **VERIFIED — STANDS WHOLE (T1), with the exact-return kill
  inside.** Compiled green 2026-10-21 (`lake build
  ThetLogos.FibonacciReturn`, 3,124 jobs, 0 errors); parent-verified:
  `.olean` present, strict recount 13, placeholder census 0, axioms
  on the six checked headline theorems standard only (`propext`,
  `Classical.choice`, `Quot.sound`). Five draft repairs, all in the
  open, none touching a statement: an implicit-argument API change
  (`Nat.fib_add_two`), a renamed lemma (`pow_lt_one₀`), a left/right
  identity orientation (`one_mul`), one `funext` bridge in the
  tendsto proof, and one header token-hygiene rewording.
-/

namespace ThetLogos

/-- The golden angle, written with Mathlib's golden conjugate:
`goldenAngle = 2πψ² = 2π / φ²`. -/
noncomputable def goldenAngle : ℝ :=
  2 * Real.pi * Real.goldenConj ^ 2

/-- The signed angular residual after `F_{n+2}` golden-angle steps,
measured against `F_n` complete turns.  Positive and negative values
are the two sides of ground. -/
noncomputable def goldenReturnResidual (n : ℕ) : ℝ :=
  (Nat.fib (n + 2) : ℝ) * goldenAngle - (Nat.fib n : ℝ) * (2 * Real.pi)

/-- The exact Fibonacci/golden-conjugate identity in cycles:
`F_{n+2}ψ² - F_n = ψ^{n+2}`. -/
theorem fib_goldenConj_cycle_residual (n : ℕ) :
    (Nat.fib (n + 2) : ℝ) * Real.goldenConj ^ 2 - (Nat.fib n : ℝ)
      = Real.goldenConj ^ (n + 2) := by
  have hrec : (Nat.fib (n + 2) : ℝ)
      = (Nat.fib n : ℝ) + (Nat.fib (n + 1) : ℝ) := by
    exact_mod_cast Nat.fib_add_two
  have hconj := Real.goldenConj_mul_fib_succ_add_fib (n + 1)
  calc
    (Nat.fib (n + 2) : ℝ) * Real.goldenConj ^ 2 - (Nat.fib n : ℝ)
        = Real.goldenConj * (Nat.fib (n + 2) : ℝ)
            + (Nat.fib (n + 1) : ℝ) := by
          rw [Real.goldenConj_sq]
          linear_combination hrec
    _ = Real.goldenConj ^ (n + 2) := hconj

/-- The golden-angle residual is exactly `2πψ^{n+2}`: it alternates in
sign because `ψ < 0`, and it shrinks geometrically because `|ψ| < 1`. -/
theorem goldenReturnResidual_eq (n : ℕ) :
    goldenReturnResidual n
      = 2 * Real.pi * Real.goldenConj ^ (n + 2) := by
  unfold goldenReturnResidual goldenAngle
  calc
    (Nat.fib (n + 2) : ℝ) * (2 * Real.pi * Real.goldenConj ^ 2)
          - (Nat.fib n : ℝ) * (2 * Real.pi)
        = 2 * Real.pi * ((Nat.fib (n + 2) : ℝ) * Real.goldenConj ^ 2
            - (Nat.fib n : ℝ)) := by ring
    _ = 2 * Real.pi * Real.goldenConj ^ (n + 2) := by
          rw [fib_goldenConj_cycle_residual]

/-- No Fibonacci stage has zero residual. -/
theorem goldenReturnResidual_ne_zero (n : ℕ) :
    goldenReturnResidual n ≠ 0 := by
  rw [goldenReturnResidual_eq]
  exact mul_ne_zero
    (mul_ne_zero two_ne_zero (ne_of_gt Real.pi_pos))
    (pow_ne_zero _ Real.goldenConj_ne_zero)

/-- One more Fibonacci stage multiplies the residual by `ψ`. -/
theorem goldenReturnResidual_succ (n : ℕ) :
    goldenReturnResidual (n + 1)
      = Real.goldenConj * goldenReturnResidual n := by
  rw [goldenReturnResidual_eq, goldenReturnResidual_eq]
  rw [show n + 1 + 2 = (n + 2) + 1 by ring, pow_succ]
  ring

/-- Consecutive residuals are on strictly opposite sides of ground:
their product is negative.  This is the exact sense in which the
return balances back and forth across ground. -/
theorem goldenReturnResidual_succ_mul_self_neg (n : ℕ) :
    goldenReturnResidual (n + 1) * goldenReturnResidual n < 0 := by
  rw [goldenReturnResidual_succ]
  have hsq : 0 < goldenReturnResidual n ^ 2 :=
    sq_pos_of_ne_zero (goldenReturnResidual_ne_zero n)
  calc
    (Real.goldenConj * goldenReturnResidual n)
          * goldenReturnResidual n
        = Real.goldenConj * (goldenReturnResidual n ^ 2) := by ring
    _ < 0 := mul_neg_of_neg_of_pos Real.goldenConj_neg hsq

/-- The residual tends to ground. -/
theorem tendsto_goldenReturnResidual :
    Tendsto goldenReturnResidual atTop (𝓝 0) := by
  have hψ : |Real.goldenConj| < 1 :=
    abs_lt.mpr ⟨Real.neg_one_lt_goldenConj,
      lt_of_lt_of_le Real.goldenConj_neg zero_le_one⟩
  have hpow : Tendsto (fun n : ℕ => Real.goldenConj ^ (n + 2))
      atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 2).mpr
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hψ)
  have hmul := Tendsto.const_mul (2 * Real.pi) hpow
  have hfun : goldenReturnResidual
      = fun n : ℕ => 2 * Real.pi * Real.goldenConj ^ (n + 2) :=
    funext goldenReturnResidual_eq
  rw [hfun]
  simpa using hmul

/-- The exact finite-return kill, relative to the natural whole-turn
count appearing in the identity: `F_{n+2}` golden-angle steps never
equal `F_n` whole turns. -/
theorem fib_mul_goldenAngle_ne_fib_mul_two_pi (n : ℕ) :
    (Nat.fib (n + 2) : ℝ) * goldenAngle
      ≠ (Nat.fib n : ℝ) * (2 * Real.pi) := by
  intro h
  have hres : goldenReturnResidual n = 0 := by
    unfold goldenReturnResidual
    linarith [h]
  exact goldenReturnResidual_ne_zero n hres

/-- The absolute residual is `2π` times a positive power of `φ⁻¹`,
hence it is strictly below one whole turn. -/
theorem abs_goldenReturnResidual (n : ℕ) :
    |goldenReturnResidual n|
      = 2 * Real.pi * (Real.goldenRatio⁻¹) ^ (n + 2) := by
  have hψabs : |Real.goldenConj| = Real.goldenRatio⁻¹ := by
    rw [abs_of_neg Real.goldenConj_neg, Real.inv_goldenRatio]
  rw [goldenReturnResidual_eq, abs_mul, abs_mul, abs_pow, hψabs,
    abs_of_pos (show (0 : ℝ) < 2 by norm_num),
    abs_of_pos Real.pi_pos]

/-- The residual is less than one whole turn in absolute value. -/
theorem abs_goldenReturnResidual_lt_two_pi (n : ℕ) :
    |goldenReturnResidual n| < 2 * Real.pi := by
  have hpos : (0 : ℝ) < Real.goldenRatio⁻¹ :=
    inv_pos.mpr Real.goldenRatio_pos
  have hlt : Real.goldenRatio⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hpow : (Real.goldenRatio⁻¹) ^ (n + 2) < 1 :=
    pow_lt_one₀ hpos.le hlt (by simp)
  calc
    |goldenReturnResidual n|
        = 2 * Real.pi * (Real.goldenRatio⁻¹) ^ (n + 2) :=
          abs_goldenReturnResidual n
    _ < 2 * Real.pi * 1 := by
          apply mul_lt_mul_of_pos_left hpow
          positivity
    _ = 2 * Real.pi := mul_one _

/-- Therefore the residual is not any integer number of whole turns.
Together with `goldenReturnResidual_ne_zero`, this kills exact return
to ground at every finite Fibonacci stage, not merely return relative
to the comparison count `F_n`. -/
theorem goldenReturnResidual_ne_int_mul_two_pi (n : ℕ) (k : ℤ) :
    goldenReturnResidual n ≠ (k : ℝ) * (2 * Real.pi) := by
  intro h
  by_cases hk : k = 0
  · subst hk
    simp only [Int.cast_zero, zero_mul] at h
    exact goldenReturnResidual_ne_zero n h
  · have hkabs : (1 : ℝ) ≤ |(k : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
      exact_mod_cast h1
    have hge : (2 * Real.pi) ≤ |(k : ℝ) * (2 * Real.pi)| := by
      rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)]
      calc
        2 * Real.pi = 1 * (2 * Real.pi) := (one_mul _).symm
        _ ≤ |(k : ℝ)| * (2 * Real.pi) :=
            mul_le_mul_of_nonneg_right hkabs (by positivity)
    rw [← h] at hge
    exact not_lt_of_ge hge (abs_goldenReturnResidual_lt_two_pi n)

/-- Modulo whole turns, the phase after `F_{n+2}` golden-angle steps
is exactly the phase of the residual. -/
theorem phaseOf_fib_mul_goldenAngle (n : ℕ) :
    phaseOf ((Nat.fib (n + 2) : ℝ) * goldenAngle)
      = phaseOf (goldenReturnResidual n) := by
  have hdecomp : (Nat.fib (n + 2) : ℝ) * goldenAngle
      = (Nat.fib n : ℝ) * (2 * Real.pi) + goldenReturnResidual n := by
    unfold goldenReturnResidual
    ring
  have hfull : phaseOf ((Nat.fib n : ℝ) * (2 * Real.pi)) = 1 := by
    have h := phaseOf_two_pi_mul_nat (Nat.fib n)
    convert h using 2
    ring
  rw [hdecomp, phaseOf_add, hfull, one_mul]

/-- The phase tends to ground (`1`) along Fibonacci step counts. -/
theorem tendsto_phaseOf_fib_mul_goldenAngle :
    Tendsto
      (fun n : ℕ =>
        phaseOf ((Nat.fib (n + 2) : ℝ) * goldenAngle))
      atTop (𝓝 1) := by
  have hcont : ContinuousAt phaseOf 0 := by
    unfold phaseOf
    fun_prop
  have h := hcont.tendsto.comp tendsto_goldenReturnResidual
  rw [phaseOf_zero] at h
  exact h.congr (fun n => (phaseOf_fib_mul_goldenAngle n).symm)

/-- The phase after a finite Fibonacci number of golden-angle steps
is never exactly ground.  If it were, the residual angle would have
to be an integer number of whole turns, which the exact residual and
its bound rule out. -/
theorem phaseOf_fib_mul_goldenAngle_ne_one (n : ℕ) :
    phaseOf ((Nat.fib (n + 2) : ℝ) * goldenAngle) ≠ 1 := by
  rw [phaseOf_fib_mul_goldenAngle]
  intro h
  unfold phaseOf at h
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
  have him := congrArg Complex.im hk
  simp at him
  -- After simplification `him` says the real residual is an integer
  -- multiple of `2π`; the gauntlet's bound kills every such value.
  have hreal : goldenReturnResidual n
      = (k : ℝ) * (2 * Real.pi) := by
    linear_combination him
  exact goldenReturnResidual_ne_int_mul_two_pi n k hreal

end ThetLogos
