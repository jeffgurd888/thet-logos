/-
# RiemannDirichletTargetPin — RH-2 brick 2: the Dirichlet-side
target pin (statement pin, RH-0 method)

**Scope: ~/workspace/your_files/rh2-statement-fidelity-bridges-scope-2026-11-22.md
(§2(iv), §6). Ladder of record: Ladder 2, RH-2, in
~/workspace/your_files/millennium-ladders-ym-and-riemann-2026-11-21.md.
Obstruction map: ~/workspace/your_files/rh1-obstruction-map-2026-11-22.md.
Fired 2026-11-24 on the parent's word, L2 lane, per brick cadence
(RH2-1 banked the same morning at `8f36864`). T5. NO CLAIM.
Parts of the Riemann Hypothesis closed by this brick: 0. The
RH dial stays 0.**

WHAT THIS BRICK IS. RH-0 pinned the ζ-side target: the corpus's
statement IS Mathlib's `RiemannHypothesis`, proved as an iff
(`RiemannHypothesisPin.riemannBoardStatement_iff`). This brick
pins the Dirichlet-side target the same way: a house
`DirichletRiemannHypothesis`-shaped statement over
`DirichletCharacter.LFunction` zeros, with an iff against its
unfolded form as the pin's self-check. A statement pin closes
no part of any hypothesis; it fixes what the board's words
mean so later rungs cannot drift. Nothing in this module
states, assumes, or approaches the truth of the pinned
statement — it is neither proved, refuted, nor believed here.

THE ASYMMETRY, ON THE FACE. For ζ, Mathlib carries the
statement itself, and RH-0 adopted it verbatim (rule R1). For
Dirichlet L-functions the pin carries NO statement: at fire
time, a grep over the pinned Mathlib (v4.35.0-rc3) finds
`RiemannHypothesis` defined exactly once
(`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:185`), for ζ
alone. Adoption being impossible, the house pins the standard
GRH-for-Dirichlet shape itself — every zero of every Dirichlet
L-function in the open critical strip lies on the critical
line — by RH-0's method: a frozen `Prop`, an `Iff.rfl`
unfold, and statement-grade receipts. The `def` below is a
house definition of a STATEMENT, as RH-0's
`RiemannBoardStatement` was; it defines no function. The
functions named inside it are Mathlib's, adopted (R1).

THE POLE GUARD — THE BRICK'S NAMED KILL CRITERION, ANSWERED
AT DRAFTING. The scope's kill criterion for this brick: the
zeros statement must exclude `s = 1` for the principal
character exactly as `Nonvanishing.lean`'s hypotheses do
(`χ ≠ 1 ∨ s ≠ 1`); a draft that quantifies over the pole dies
at drafting, not at build. Read at fire time, the guard stands
in-pin verbatim: `DirichletCharacter.LFunction_ne_zero_of_re_eq_one`
(Nonvanishing.lean:387) and
`DirichletCharacter.LFunction_ne_zero_of_one_le_re` (:400)
both carry the hypothesis `(hχs : χ ≠ 1 ∨ s ≠ 1)`. The pinned
statement below carries that exact disjunction as its second
hypothesis, so for the principal character (`χ = 1`) the
statement can only be fed seats `s ≠ 1`, and for `s = 1` only
non-principal characters — the pole seat is outside the
statement's scope by construction, not by afterthought. The
receipt `dirichletRiemannHypothesis_pole_guard` banks the
load-bearing half as a theorem: at (`χ = 1`, `s = 1`) the
guard is false, so the pinned quantifier can never be applied
there. The kill criterion did NOT trigger: the draft never
quantified over the pole.

THE STRIP GUARDS. Mathlib's ζ statement excludes trivial
zeros by form (`¬∃ n : ℕ, s = -2 * (n + 1)`) because ζ's
trivial zeros have one shape. Dirichlet trivial zeros do not:
they sit at the non-positive integers of the character's own
parity, and the principal character mod `N > 1` carries
further zeros of its finite Euler factors on `re s = 0`. No
single form-guard generalizes, so this pin guards by domain
instead: a *nontrivial* zero of a Dirichlet L-function is by
definition a zero in the open critical strip, and the
hypotheses `0 < s.re` and `s.re < 1` are exactly that domain.
Every trivial zero is outside it by construction. This is a
statement-design decision, recorded here rather than hidden:
the pinned statement is the textbook GRH-for-Dirichlet shape.

THE RULES, ON THE FACE (scope R1–R3, binding on every RH-2
brick):
- **R1 — adopt, never redefine.** The L-function is Mathlib's
  `DirichletCharacter.LFunction` (DirichletContinuation.lean,
  under its own `variable {N : ℕ} [NeZero N]` context, carried
  identically below). No house L-function, ζ, or θ is defined
  here or anywhere on this board.
- **R2 — agreement before use.** The only house result this
  brick consumes is RH2-1's banked bridge
  (`dirichletLFunction_modOne_eq`: the mod-1 character's
  L-function IS `riemannZeta`, as functions), cited in the
  falsification receipt — never re-proved.
- **R3 — junk values are part of the object.** The mod-1
  bridge is a function equality, so it identifies the two
  functions at every `s`, the pole's junk value included; and
  the pole guard above is stated so that no junk value at
  `s = 1` can ever be fed to this statement as a "zero" of the
  principal character.

THE HECKE FENCE (scope §4, restated): the Hecke seat on this
board is EMPTY and stays empty. Nothing Hecke-side is
defined, named, stated, or touched in this module.

THE FOUR DECLARATIONS (scope §6 price: ~4 decls, ~3 strict;
statement pins are thin by nature and are counted thin):
1. `DirichletRiemannHypothesis` — the frozen statement (a
   `def`; the pin itself, not counted strict).
2. `dirichletRiemannHypothesis_iff` — the self-check: the
   statement unfolds, definitionally, to its literal text.
   Proved by `Iff.rfl`, exactly RH-0's method.
3. `dirichletRiemannHypothesis_pole_guard` — the kill
   criterion's receipt: the pole guard fails at the
   principal character's pole seat, so the statement can
   never be applied there.
4. `dirichletRiemannHypothesis_falsified_by_offline_zero` —
   the K-RH-1-style receipt, at RH-0's own seat: a
   hypothetical zero at `s = 3/4 + 100 * Complex.I` would
   falsify the pinned statement (its real part is `3/4`,
   inside the strip and off the line; it is `≠ 1`, so the
   pole guard passes by its right disjunct). The zero is a
   carried hypothesis, never discharged — via RH2-1's banked
   mod-1 bridge, the hypothesis is stated for `riemannZeta`
   itself, the same seat that falsifies RH-0's pin.
-/

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import ThetLogos.RiemannDirichletBridgePin

namespace ThetLogos

/-- **The Dirichlet-side target statement** (scope §2(iv)):
the Generalized Riemann Hypothesis for Dirichlet
L-functions, in the standard shape — for every modulus `N`,
every Dirichlet character `χ` mod `N`, and every `s` in the
open critical strip at which `LFunction χ` vanishes, `s`
lies on the critical line. The pole guard
`(χ ≠ 1 ∨ s ≠ 1)` is `Nonvanishing.lean`'s own hypothesis
shape (lines 387, 400, re-read at fire time): the principal
character's pole at `s = 1` is outside this statement's
scope by construction. NO CLAIM — this definition pins the
statement; it proves nothing. -/
def DirichletRiemannHypothesis : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    DirichletCharacter.LFunction χ s = 0 →
    (χ ≠ 1 ∨ s ≠ 1) →
    0 < s.re → s.re < 1 →
    s.re = 1 / 2

/-- **The pin's self-check**: the target statement unfolds,
definitionally, to its literal text — the same text the
module face audits against `Nonvanishing.lean`'s guard
shape. Proved by `Iff.rfl`, exactly RH-0's method
(`riemannBoardStatement_iff`). -/
theorem dirichletRiemannHypothesis_iff :
    DirichletRiemannHypothesis ↔
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
        DirichletCharacter.LFunction χ s = 0 →
        (χ ≠ 1 ∨ s ≠ 1) →
        0 < s.re → s.re < 1 →
        s.re = 1 / 2 :=
  Iff.rfl

/-- **The pole-guard receipt** (the brick's named kill
criterion, banked): at the principal character's pole seat
(`χ = 1`, `s = 1`) the pinned statement's pole guard is
FALSE — both disjuncts fail — so `DirichletRiemannHypothesis`
can never be applied at the pole, for any modulus. The
statement does not quantify over the pole; this theorem is
the receipt that it cannot be made to. -/
theorem dirichletRiemannHypothesis_pole_guard {N : ℕ} [NeZero N] :
    ¬ ((1 : DirichletCharacter ℂ N) ≠ 1 ∨ (1 : ℂ) ≠ 1) := by
  simp

/-- **The falsification receipt** (statement grade, mirroring
RH-0's K-RH-1 receipt at the same seat): a hypothetical zero
of `riemannZeta` at the off-line seat `3/4 + 100 * Complex.I`
would falsify the pinned Dirichlet-side statement — via
RH2-1's banked bridge (`dirichletLFunction_modOne_eq`,
cited, not re-proved) that seat is a zero of the mod-1
character's L-function; it is `≠ 1` (its imaginary part is
`100`), so the pole guard passes by its right disjunct; its
real part `3/4` is inside the strip and off the critical
line. So the pinned `Prop` is falsified by exactly the
counterexamples that would falsify GRH-for-Dirichlet — it is
neither vacuous nor true-by-junk on this exhibited seat. The
zero itself is a carried hypothesis, never discharged; this
lemma asserts no zero exists there. -/
theorem dirichletRiemannHypothesis_falsified_by_offline_zero :
    riemannZeta (3 / 4 + 100 * Complex.I) = 0 → ¬ DirichletRiemannHypothesis := by
  intro hζ hDRH
  have : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  have hzero : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)
      (3 / 4 + 100 * Complex.I) = 0 := by
    have h2 := dirichletLFunction_modOne_eq (χ := (1 : DirichletCharacter ℂ 1))
    rw [h2]
    exact hζ
  have hneone : (3 / 4 + 100 * Complex.I : ℂ) ≠ 1 := by
    intro hn
    have him := congrArg Complex.im hn
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.one_im] at him
    norm_num at him
  have h := hDRH 1 (1 : DirichletCharacter ℂ 1) (3 / 4 + 100 * Complex.I) hzero
    (Or.inr hneone)
    (by norm_num [Complex.add_re, Complex.mul_re, Complex.div_re,
      Complex.I_re, Complex.I_im])
    (by norm_num [Complex.add_re, Complex.mul_re, Complex.div_re,
      Complex.I_re, Complex.I_im])
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.I_im] at h
  norm_num at h

end ThetLogos
