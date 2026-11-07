import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import ThetLogos.FiniteEntropy

namespace ThetLogos

/-!
# ThetLogos.FiniteOccupationEntropyPin — AB-7 PIN (interface; frozen names; 0 strict)

**Commission:** Jeff, tap 2026-11-07 09:53 EST, firing AB-7 as priced by the
Actions Bridge buildability scoping
(`~/workspace/your_files/actions-bridge-scoping-2026-11-07.md`, node 7).
**Price:** S — the content module `FiniteOccupationEntropy` at 8–14 strict.
**Status: PIN ONLY (this file). NO CLAIM. Dials 0/4. Dial-ineligible** — a
finite counting brick: it derives no measured number, no gravity object, no
continuum statement, and no prediction. It moves no dial.

## What this seat is

`N` two-level sites, occupation `k`; the microstate count is `Nat.choose N k`
and its logarithm is the occupation entropy. This seat counts configurations
of a *fixed occupation number*. It is a different variational problem from
the landed `FiniteEntropy` seat, which maximizes `entropyW` over *weight
functions*; the two are joined by the bridge form (4) below (the landed seat
evaluated at the uniform weight on the type of `k`-subsets), not duplicated.

Overlap audit (scoping, re-checked at lane start): NOT the finite-arrow
lane's FA-4b (`entropyW`/`relEntW` of a distribution under graph heat flow;
no occupation counting there), NOT the thermoelectric seat's `teTwoLevel`
(a two-*temperature* profile), NOT `ThermalProfileSeparation`'s sector
populations.

## The definition and the four frozen statement forms

This pin carries the definition and states the four forms as `Prop`s.
Names are FROZEN at this commit; the content module proves theorems whose
statements are these forms verbatim.

1. **Maximum at half occupation** — `occEntropyMaxAtHalfForm`.
2. **Forward difference, closed form** — `occEntropyStepForm`.
3. **Sign of the forward difference** — `occEntropyStepSignsForm`: bare sign
   facts about the log-ratio (positive below the middle step, negative past
   it, zero at it). The sign change is a fact about `Real.log` of a ratio of
   counting numbers; nothing else is stated.
4. **Bridge to the landed seat** — `occEntropyBridgeForm`: `occEntropy N k`
   is `entropyW` of the uniform weight `1 / card` on the type of `k`-subsets
   of `Fin N` (whose cardinality is `Nat.choose N k`).

## Kills armed at this pin (pre-registered, scoping §AB-7)

- **K-AB7-DUP** — if any in-flight lane (finite-arrow especially) lands
  occupation-count entropy first, this item dies as a duplicate.
- **K-AB7-FIAT** — if landing requires "temperature" inside a statement
  rather than the bare sign facts of form (3), the item dies. The words
  "temperature" / "negative temperature" appear in NO statement, definition,
  or theorem name in this package.
- **K-AB7-BOUND** — if the content brick grows past 14 strict, STOP and
  report for re-pricing; do not expand quietly.

## T5 READING (face comment only — no statement content)

T5: the sign flip of form (3) at the middle step is the finite counting
shadow of the population-inversion sign change graded in chat 2026-11-07
(the "negative temperature" neighbor of the map's node 7). This reading is
a gloss on the face of the pin; it is asserted by no definition and no
theorem in this package, and no proof obligation refers to it.
-/

/- REPAIR NOTE (parent-authorized 2026-11-07): as committed at 7d0e096 this
   pin never elaborated — the subtraction in frozen forms (2) and (3) was
   written with the display glyph U+2212, which the parser does not accept
   as a token (subtraction is ASCII `-`), and `occEntropy` lacked the
   `noncomputable` marking its `Real.log` body requires. The repair marks
   `occEntropy` `noncomputable` and replaces U+2212 with ASCII `-` on the
   code lines of forms (2)-(3) only (prose occurrences untouched). The
   propositions denoted are unchanged — the glyph lines never denoted
   anything at all. -/
/-- Occupation entropy of `N` two-level sites at occupation `k`: the
    logarithm of the microstate count, `log (choose N k)`. At `k > N` the
    count is `0` and the value is `log 0 = 0` by Mathlib's convention.
    Tier T1 (definition). -/
noncomputable def occEntropy (N k : ℕ) : ℝ :=
  Real.log (Nat.choose N k)

/-- **Frozen form (1) — maximum at half occupation:** for all `N k`,
    `occEntropy N k ≤ occEntropy N (N / 2)`. Tier T1 (statement pin). -/
def occEntropyMaxAtHalfForm : Prop :=
  ∀ N k : ℕ, occEntropy N k ≤ occEntropy N (N / 2)

/-- **Frozen form (2) — forward difference:** for `k < N`, the forward
    difference of `occEntropy N` at `k` is the logarithm of the ratio
    `(N − k) / (k + 1)` of counting numbers. Tier T1 (statement pin). -/
def occEntropyStepForm : Prop :=
  ∀ N k : ℕ, k < N →
    occEntropy N (k + 1) - occEntropy N k
      = Real.log ((N - k : ℝ) / (k + 1))

/-- **Frozen form (3) — sign of the forward difference:** below the middle
    step the difference is positive, past it negative, at it zero. Bare
    sign facts about the log-ratio of form (2); no other vocabulary.
    Tier T1 (statement pin). -/
def occEntropyStepSignsForm : Prop :=
  (∀ N k : ℕ, k < N → k + 1 < N - k →
    0 < occEntropy N (k + 1) - occEntropy N k) ∧
  (∀ N k : ℕ, k < N → N - k < k + 1 →
    occEntropy N (k + 1) - occEntropy N k < 0) ∧
  (∀ N k : ℕ, N - k = k + 1 →
    occEntropy N (k + 1) - occEntropy N k = 0)

/-- **Frozen form (4) — bridge to the landed `entropyW` seat:** for
    `k ≤ N`, `occEntropy N k` equals `entropyW` of the uniform weight
    `1 / card` on the type of `k`-subsets of `Fin N`. Tier T1
    (statement pin). -/
def occEntropyBridgeForm : Prop :=
  ∀ N k : ℕ, k ≤ N →
    occEntropy N k =
      entropyW (fun _ : ↥(Finset.powersetCard k
          (Finset.univ : Finset (Fin N))) =>
        1 / (Fintype.card ↥(Finset.powersetCard k
          (Finset.univ : Finset (Fin N))) : ℝ))

end ThetLogos
