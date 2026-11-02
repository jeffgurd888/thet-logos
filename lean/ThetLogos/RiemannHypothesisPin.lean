import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

namespace ThetLogos

/-!
# ThetLogos.RiemannHypothesisPin — the Riemann board statement pin

Board charter: **NO CLAIM.** Parts of the Riemann Hypothesis closed
by this house: **0** — now, and after this pin lands (a statement
pin closes no part of RH). This module is a statement-grade object:
the house's first rung on the Riemann board, mirroring the other
Millennium boards' pins. It proves nothing about the Riemann
Hypothesis itself.

## The frozen statement

The statement pinned here is Mathlib's own definition, adopted
verbatim — not a house re-statement. In the pin (Mathlib
v4.35.0-rc3, `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:182-186`):

```lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
```

`RiemannBoardStatement` below is exactly that `Prop`, and
`riemannBoardStatement_iff` restates its unfolding with the pin's
literal text, proved by `Iff.rfl` — the pin's self-check.

The ξ function (`riemannXi`) is absent in-pin and is not needed
for this statement pin.

## K-RH-1 receipt (statement-grade non-vacuity)

`riemannBoardStatement_falsified_by_offline_zero` records that a
hypothetical zero at `s = 3/4 + 100 * Complex.I` would falsify the
pinned statement: its real part is `3/4 ≠ 1/2`, it is of no trivial
form `-2 * (n + 1)` (its imaginary part is `100`, while every
trivial seat is real), and it is `≠ 1`. So the pinned `Prop` is
falsified by exactly the counterexamples that would falsify RH —
it is neither vacuous nor true-by-junk on this exhibited seat.
This is a statement-grade receipt only; it asserts no zero exists
there (indeed the hypothesis `riemannZeta (3/4 + 100 * I) = 0` is
carried as a hypothesis, never discharged).

## Cited-API fence (pin facts, T4 — cited, NOT proved here)

Everything below is Mathlib's API at the pinned rev
(`lean/lake-manifest.json` rev
`516d31250e96c4e8e76888c3d8e2e43a9642b9ee`), cited from the RH-0
audit memo (`routeb-general-scratch/scoping-rh-0-2026-11-02.md` §2).
None of it is a house result, and none of it is proved in this
module; the fence is recorded in comments only.

- Pole at `s = 1` / junk value: the residue is
  `riemannZeta_residue_one : Tendsto (fun s ↦ (s - 1) * riemannZeta s)
  (𝓝[≠] 1) (𝓝 1)` — `RiemannZeta.lean:242`. The junk value at the
  pole is `riemannZeta_one : riemannZeta 1 = (γ - log (4 * π)) / 2`
  — `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:421`, and it is
  nonzero: `riemannZeta_one_ne_zero : riemannZeta 1 ≠ 0` —
  `ZetaAsymp.lean:444`. (Also `riemannZeta_zero : riemannZeta 0 =
  -1 / 2` — `RiemannZeta.lean:151`.)
- Trivial zeros, one-directional only (existence, no
  classification is claimed or cited):
  `riemannZeta_neg_two_mul_nat_add_one (n : ℕ) :
  riemannZeta (-2 * (n + 1)) = 0` — `RiemannZeta.lean:172-174`.
- Functional equations: `completedRiemannZeta₀_one_sub`
  (`Λ₀ (1 - s) = Λ₀ s`, unconditional) — `RiemannZeta.lean:100`;
  `completedRiemannZeta_one_sub` — `RiemannZeta.lean:106`;
  `riemannZeta_one_sub` (ζ form, under `∀ n : ℕ, s ≠ -n` and
  `s ≠ 1`) — `RiemannZeta.lean:178`. (`completedRiemannZeta` is
  defined at `RiemannZeta.lean:68`, `completedRiemannZeta₀` at
  `:64`.)
- Euler product for `re s > 1`:
  `riemannZeta_eulerProduct_hasProd (hs : 1 < s.re) :
  HasProd (fun p : Primes ↦ (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s)`
  — `Mathlib/NumberTheory/EulerProduct/DirichletLSeries.lean:91`
  (tprod form `:98`, partial products `:104`). Agreement with the
  Dirichlet series: `zeta_eq_tsum_one_div_nat_cpow` —
  `RiemannZeta.lean:207`.
- Nonvanishing for `re s ≥ 1`:
  `riemannZeta_ne_zero_of_one_le_re` —
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean:413`
  (strict form `riemannZeta_ne_zero_of_one_lt_re` —
  `Mathlib/NumberTheory/LSeries/Dirichlet.lean:328`).
- Zero set: `noncomputable def riemannZetaZeros : Set ℂ :=
  riemannZeta ⁻¹' {0}` —
  `Mathlib/NumberTheory/LSeries/ZetaZeros.lean:36`.

Honesty tiers in this file:
- **T1 (proved):** the unfold lemma (by `Iff.rfl`) and the K-RH-1
  receipt lemma below — both about the *statement*, not about ζ.
- **T4 (pin facts):** the cited-API fence above — Mathlib's
  theorems, cited by location, never re-proved or claimed here.
- **NO CLAIM:** the Riemann Hypothesis itself. Unproved here,
  unrefuted here, untouched here.
-/

/-- The Riemann board statement: Mathlib's `RiemannHypothesis`,
adopted verbatim as the frozen statement of this board.
NO CLAIM — this definition pins the statement; it proves nothing. -/
def RiemannBoardStatement : Prop :=
  RiemannHypothesis

/-- The pin's self-check: the board statement unfolds, definitionally,
to the pin's literal text (Mathlib
`NumberTheory/LSeries/RiemannZeta.lean:182-186`, re-read at build
time 2026-11-02 — the literal text matches the RH-0 audit's
paraphrase exactly, no deviation). Proved by `Iff.rfl`. -/
theorem riemannBoardStatement_iff :
    RiemannBoardStatement ↔
      ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1),
        s.re = 1 / 2 :=
  Iff.rfl

/-- K-RH-1 receipt (statement grade): a hypothetical zero at the
off-line seat `3/4 + 100 * Complex.I` would falsify the pinned
statement. The witness is not a trivial zero (its imaginary part
is `100`; every seat `-2 * (n + 1)` is real), it is not `1`, and
its real part `3/4` is not `1 / 2`. The zero itself is a carried
hypothesis — this lemma exhibits a falsifying seat, it does not
assert that any zero exists there. -/
theorem riemannBoardStatement_falsified_by_offline_zero :
    riemannZeta (3 / 4 + 100 * Complex.I) = 0 → ¬ RiemannBoardStatement := by
  intro hzero hRH
  have hnotriv : ¬∃ n : ℕ, (3 / 4 + 100 * Complex.I : ℂ) = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    have him := congrArg Complex.im hn
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.neg_im, Complex.natCast_im, Complex.one_im] at him
    norm_num at him
  have hneone : (3 / 4 + 100 * Complex.I : ℂ) ≠ 1 := by
    intro hn
    have him := congrArg Complex.im hn
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.one_im] at him
    norm_num at him
  have hre := hRH (3 / 4 + 100 * Complex.I) hzero hnotriv hneone
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.I_im] at hre
  norm_num at hre

end ThetLogos
