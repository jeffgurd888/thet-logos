import ThetLogos.MeasuredClockCollapse

/-!
# ThetLogos.MeasuredClockQuestion2 — Q1′′: the clock question, re-posed

**Status: a posted question — definitions only, no theorems deciding
anything. NO CLAIM.**

## Why this entry exists: the collapse of Q1′ as posed

Q1′ — `measuredClockQuestion N ε` in `MeasuredClockSpectrum.lean` —
pairs an **absolute** tolerance `ε` with a target `c * clockObs m`
that scales with a **free** constant `c`. That mismatch is fatal,
and the receipt is landed at theorem grade in
`MeasuredClockCollapse.lean`: `measuredClockQuestion_trivial` shows
the posed question is true at every `N` at its pre-registered
tolerance (degenerate witness: zero spectrum, `c = 19 / 10^17`, so
the scaled target fits inside the tolerance on its own), and
`measuredClockQuestion_of_pos` shows it is true at every `N` for
**every** `ε > 0` by the same construction. Shrinking `c` shrinks
the target into the tolerance; the definition answers itself, and
the posed existential has no `N`-content at all.

Under the house relabeling rule the original entry is not edited:
`measuredClockQuestion` stands as posted, with its collapse receipt
beside it, and `blockedQ1` is untouched. The live question is this
**new** entry.

## The re-posing: eliminate the scale, per-line tolerances

`measuredClockQuestion2` below removes the disease rather than
patching its symptoms:

- **The scale `c` is eliminated.** Equivalently: `c` is fixed at
  `1`, or the scale is absorbed into the spectrum `lam`. A modular
  frequency difference must now meet the measured ratio itself, in
  observation units — no free factor remains that could shrink a
  line's target toward zero.
- **Each line carries its own entered tolerance.** Line `m` must
  land within `clockObsErr m`, the published standard uncertainty
  of that very ratio, instead of within one absolute `ε` shared by
  all lines.

In reduced form, with `x_k = β * lam k ^ 2`, a fit is a graph: the
seven lines as directed edges on `N` vertices, edge `m` carrying the
value `x_i - x_j ≈ clockObs m`. On each connected component the edge
values fix `x` up to translation, so the only obstructions are
cycles: around any cycle, the signed sum of the entered ratios must
vanish within the cycle's accumulated per-line tolerances. At
`N = 7` (seven edges, seven vertices) at least one independent cycle
is forced, so the question there is genuine — and finite: it turns
on the subset signed sums of the entered ratios, an exact rational
check. That decision is a separate brick; **nothing is decided in
this module.**

## Context at N = 9 and N = 8 (prose only)

The exact fits already landed — `measuredClockAnswer` (N = 9) and
`measuredClockAnswer8` (N = 8) — are witnesses at `c = 1` with fit
error exactly `0`, so morally they answer Q1′′ at their instances
for free: error `0` is within any per-line tolerance. The formal
conversion is **not** carried here: the exact-fit equalities are
local steps inside those theorems' proofs, not exported lemmas,
and the theorems conclude the Q1′ existential, from which no
witness can be extracted. Re-deriving the fits exceeds this brick's
definitions-only scope; the conversion belongs to the decision
brick (Brick D of the scoping memo).

## The fence

The clock table (`clockObs`, `clockObsErr`) is **Tier T4 INPUT** —
measured data from the CIPM compilation, not derived and not
proved. A verdict on `measuredClockQuestion2` at any `N` answers
the clock question only: it is a finite fit question about entered
ratios and differences of squares. **No physics claim. NO CLAIM.**
-/

namespace ThetLogos

/-- **Q1′′ — the measured clock question with the scale eliminated**
    — a definition (a posted question), **not** a theorem and **not**
    answered here.

    `measuredClockQuestion2 N` asks: does there exist a thermal
    triple — inverse temperature `β > 0` and a Dirac spectrum
    `lam : Fin N → ℝ` on an `N`-dimensional space — together with an
    assignment `f` of clock lines to pairs of levels, such that
    every *measured* ratio in `clockObs` is reproduced by a modular
    frequency difference `modularFreqDiff β lam i j =
    β (lam i ^ 2 - lam j ^ 2)` **in observation units** (no free
    scale) and **within that line's own entered uncertainty**
    `clockObsErr m`?

    Differences from Q1′ (`measuredClockQuestion`): the free scale
    `c` is gone (absorbed into the spectrum, equivalently fixed at
    `1`), and the single tolerance parameter `ε` is replaced by the
    per-line entered tolerances. Both changes are the repair for the
    collapse receipted in `MeasuredClockCollapse.lean`: with no
    scale to shrink and tolerances riding in the same units as the
    targets, the existential no longer answers itself. -/
noncomputable def measuredClockQuestion2 (N : ℕ) [NeZero N] : Prop :=
  ∃ (β : ℝ) (lam : Fin N → ℝ) (f : Fin 7 → Fin N × Fin N),
    0 < β ∧
      ∀ m : Fin 7,
        |modularFreqDiff β lam (f m).1 (f m).2 - (clockObs m : ℝ)|
          ≤ (clockObsErr m : ℝ)

/-- Definitional unfolding of `measuredClockQuestion2` — the posted
    existential, restated. No content beyond the definition. -/
lemma measuredClockQuestion2_iff (N : ℕ) [NeZero N] :
    measuredClockQuestion2 N ↔
      ∃ (β : ℝ) (lam : Fin N → ℝ) (f : Fin 7 → Fin N × Fin N),
        0 < β ∧
          ∀ m : Fin 7,
            |modularFreqDiff β lam (f m).1 (f m).2 - (clockObs m : ℝ)|
              ≤ (clockObsErr m : ℝ) :=
  Iff.rfl

end ThetLogos
