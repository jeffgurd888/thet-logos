/-
# RiemannStatementPin — RH-0: the Riemann target, pinned to Mathlib's own

**Commissioned by Zero, 2026-11-21 00:09 EST ("fire").
Lane-grade pin. NO CLAIM. Pre-registered DIAL-INELIGIBLE; dials 0/4
under every outcome.**

Spec of record: ~/workspace/your_files/rh0-statement-pin-spec-2026-11-21.md
(rung RH-0 of millennium-ladders-ym-and-riemann-2026-11-21.md).

A statement pin earns NO progress. This pin does not prove, disprove,
or touch the Riemann Hypothesis. Its only job is to fix the corpus's
target as *provably the same proposition* as the prize's statement —
statement fidelity, at pin grade (the RH-2 discipline, applied at the
first rung).

STRIKE-CHECK (2026-11-21, against Mathlib): PARTIAL — the naive pin
is a DUPLICATE and dies. Mathlib already defines `RiemannHypothesis`
(`Mathlib/NumberTheory/LSeries/RiemannZeta.lean`): a pin that merely
re-states RH against Mathlib's ζ would duplicate it. This pin is the
re-shaped survivor: it names the nontrivial-zero predicate once, in
Mathlib's own exclusion shape; states the corpus target and PROVES it
is `RiemannHypothesis` (the keystone iff — a pure rearrangement, a
proof, not an assertion of sameness); states the critical-strip form
and proves the one direction that is cheap; and proves the zeros-set
form equivalent. The reverse strip direction is NOT in this pin: it
needs the functional equation and is RH-2/RH-3 bridge work.
`Mathlib.NumberTheory.LSeries.Nonvanishing` is deliberately NOT
imported — the hard direction's key lemma is out of scope, so the
brick cannot quietly grow into it.

HONEST SCOPE, on the face: Mathlib's `riemannZeta` is the analytic
continuation (Hurwitz/completed-ζ machinery), agreeing with the
Dirichlet series only for `re s > 1`. The pin states against
`riemannZeta` itself, so no series-vs-continuation bridge is needed
or implied. "Nontrivial" is not "in the strip" definitionally: strip
⇒ nontrivial is a computation (proved here); nontrivial ⇒ strip is a
theorem through the functional equation (flagged, not here).

STATUS: STATUS-RIEMANNSTATEMENT.md.
-/

import Mathlib.Tactic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros

namespace ThetLogos

/-- A nontrivial zero of the Riemann zeta function: `ζ(s) = 0`, `s` is not
one of the trivial zeros `-2, -4, -6, …`, and `s ≠ 1` (the pole). The
exclusion shape `¬∃ n : ℕ, s = -2 * (n + 1)` is copied exactly from
Mathlib's own `RiemannHypothesis` and matches the trivial-zero theorem
`riemannZeta_neg_two_mul_nat_add_one`. Copied, not prettified: the
keystone iff below must stay a pure rearrangement. -/
def IsNontrivialZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ (¬∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1

/-- The corpus's Riemann target: every nontrivial zeta zero has real
part `1 / 2`. This is a STATEMENT PIN — it asserts nothing about whether
any such zero exists or where zeros lie. -/
def RiemannHypothesisTarget : Prop :=
  ∀ s : ℂ, IsNontrivialZetaZero s → s.re = 1 / 2

/-- THE KEYSTONE. The corpus target is Mathlib's `RiemannHypothesis`
itself — proved, not asserted. The proof is a pure rearrangement of
`∀` and `∧` on both sides; if a future edit to either statement makes
this proof fail, the statements have drifted and the pin has done its
job by breaking. -/
theorem riemannHypothesisTarget_iff :
    RiemannHypothesisTarget ↔ RiemannHypothesis := by
  constructor
  · intro h s hs htriv hs1
    exact h s ⟨hs, htriv, hs1⟩
  · intro h s hs
    exact h s hs.1 hs.2.1 hs.2.2

/-- The critical-strip form of the target — the form usually quoted:
every zero of `ζ` in the open strip `0 < re s < 1` has `re s = 1 / 2`.
Stated separately from `RiemannHypothesisTarget` because the two are NOT
definitionally the same: see `criticalStripTarget_of_target` and the
spec's flagged reverse direction. -/
def CriticalStripTarget : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-- The cheap direction: the pinned target implies the strip form. A zero
in the open strip is automatically nontrivial — a trivial zero
`-2 * (n + 1)` has real part `-2 * (n + 1) ≤ -2 < 0`, and `re s < 1`
excludes the pole at `1`. The converse is NOT proved in this pin: it
needs the functional equation (zeros with `re s ≤ 0` are trivial), which
is bridge work for a later rung, and the pin does not state the iff. -/
theorem criticalStripTarget_of_target (h : RiemannHypothesisTarget) :
    CriticalStripTarget := by
  intro s hs hre0 hre1
  apply h s
  refine ⟨hs, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    have hre : s.re = -2 * ((n : ℝ) + 1) := by
      rw [hn]
      simp [Complex.mul_re, Complex.add_re, Complex.natCast_re]
    rw [hre] at hre0
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  · intro hs1
    rw [hs1] at hre1
    simp only [Complex.one_re] at hre1
    exact lt_irrefl 1 hre1

/-- The target restated over Mathlib's zeros set `riemannZetaZeros`:
every member of the set that is nontrivial has real part `1 / 2`.
Equivalent to the target by `mem_riemannZetaZeros` and rearrangement. -/
theorem riemannHypothesisTarget_iff_zerosSet :
    RiemannHypothesisTarget ↔
      ∀ s ∈ riemannZetaZeros, (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
        s.re = 1 / 2 := by
  constructor
  · intro h s hs htriv hs1
    exact h s ⟨(mem_riemannZetaZeros.mp hs), htriv, hs1⟩
  · intro h s hs
    exact h s (mem_riemannZetaZeros.mpr hs.1) hs.2.1 hs.2.2

end ThetLogos
