import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# ThetLogos.RepeatingSqrtPin — a viral graphic's arithmetic, pinned under a kernel proof (DRAFT)

STATUS: **DRAFT — UNVERDICTED** (lane thet-logos-og0,
branch sqrtpin, drafted 2026-11-11). Design record:
`STATUS-SQRTPIN.md` in the lane root.

## Source and audit (on the face)

Zero shared a social-media "competition problem"
graphic (2026-11-11): **√860.444444… = ?**, with
solutions costumed as Ramanujan and as Gauss, and
tapped: "A Lean pin of the problem."

The parent's audit, recorded before the build:

- **The arithmetic is CORRECT.** 860.444… = 860 + 4/9
  = 7744/9 = (88/3)², so the square root is 88/3.
- **The attribution is costume.** Neither Ramanujan
  nor Gauss authored this problem. The number was
  reverse-engineered from (88/3)² — the "problem" was
  built backward from its answer, which is why the
  repeating decimal lands on a perfect square of a
  rational.
- The graphic's narration ("subtract the second from
  the first") is direction-sloppy; the computation it
  narrates nevertheless lands on the right value.

The faces were borrowed. What this pin adds is the
one thing the graphic did not have: a proof, checked
by the Lean kernel, with the number DEFINED on the
face — 860.444… is not a picture here; it is
`860 + ∑' (n : ℕ), 4 / 10^(n+1)`, the digit-place sum,
and the theorems below are about that defined number.

## Fences

Pre-registered DIAL-INELIGIBLE; NO CLAIM; all dials
0/4. This is a piece of arithmetic with a machine
proof, pinned in the open. It is not a competition
result, not a recovered historical method, and it
makes no claim about how anyone — Ramanujan, Gauss,
or the graphic's anonymous author — solved anything.
-/

namespace ThetLogos

/-- **The repeating tail, proved:** the digit-place
sum `∑' (n : ℕ), 4 / 10^(n+1)` — that is, 0.444… — is
exactly `4 / 9`. The summand is `(2/5) * (1/10)^n`;
the geometric series does the rest. -/
theorem repeating_four_ninths :
    ∑' (n : ℕ), (4 : ℝ) / 10 ^ (n + 1) = 4 / 9 := by
  have hterm : ∀ n : ℕ, (4 : ℝ) / 10 ^ (n + 1)
      = (2 / 5) * (1 / 10) ^ n := by
    intro n
    rw [pow_succ, div_pow, one_pow]
    field_simp
    ring
  rw [tsum_congr hterm, tsum_mul_left,
    tsum_geometric_of_lt_one (show (0 : ℝ) ≤ 1 / 10 by norm_num)
      (show (1 / 10 : ℝ) < 1 by norm_num)]
  norm_num

/-- **The value under the radical:** 860 plus the
proved tail is `7744 / 9` — which is `(88/3)^2`, the
reverse-engineering the audit named, now a proved
rational identity. -/
theorem problem_value : (860 : ℝ) + 4 / 9 = 7744 / 9 := by
  norm_num

/-- **The problem as posed, answered under proof:**
with 860.444… DEFINED as 860 plus the digit-place
sum, its square root is exactly `88 / 3`. -/
theorem competition_sqrt :
    Real.sqrt ((860 : ℝ)
      + ∑' (n : ℕ), (4 : ℝ) / 10 ^ (n + 1)) = 88 / 3 := by
  rw [repeating_four_ninths, problem_value]
  have h : (88 / 3 : ℝ) ^ 2 = 7744 / 9 := by norm_num
  rw [← h]
  exact Real.sqrt_sq (by norm_num)

end ThetLogos
