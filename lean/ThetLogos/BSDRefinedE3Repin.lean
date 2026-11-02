import ThetLogos.BSDRefinedE3Pin
import Mathlib.GroupTheory.Torsion
import Mathlib.Tactic

namespace ThetLogos

/-!
# ThetLogos.BSDRefinedE3Repin — the refined BSD formula for `E3`, re-pinned

**NEW ENTRY under the relabeling rule**, on Jeff's decision
(2026-11-01 22:33 EST) on the K-BSD3-2c decision item. The old pin
`BSDRefinedE3Pin` / `BSDRefinedE3` stands **DEAD and UNEDITED** — its
`NagellLutzCriterionE3` is **FALSE** for `E3` (**K-BSD3-2c**, fired
2026-11-02) and `BSDRefinedE3` conditioned on it is vacuous; nothing
is edited back to life. This module is the new entry that replaces
it in the record; killed/vetoed claims return only as NEW entries
by proof, and the original stands.

**The corrected seam.** The corrected seam is the general
Nagell–Lutz form `(2y + a1*x + a3)^2 ∣ Δ`, which for `E3`
(`a1 = 0`, `a3 = 1`, `|Δ| = 161051 = 11^5`) is `(2*yi + 1)`; the
disjunct `2*yi + 1 = 0` is the 2-torsion case of the general
criterion. `NagellLutzCriterionE3R` below states exactly that form
and no other.

**The torsion card.** `|tors| = 5` enters **ONLY** as the named
hypothesis `E3TorsionCardSeam`, to be discharged by the sweep brick
conditional on `NagellLutzCriterionE3R`. It is **NOT** a T4 value
anywhere in this entry.

**Reused definitions.** `E3`, `E3RankZeroSeam`, `E3ShaFiniteSeam`,
`E3LValue`, `E3PeriodValue`, `E3TamagawaValue` are **REUSED** from
the dead pin's module unchanged (their content does not touch the
NL seam), as is `refinedRHS` from `ThetLogos.BSDRefinedAssembly`.

**Kills registered for this entry.**
- **K-BSD3-2R-a** (analytic-Sha identification beyond the B1
  licence).
- **K-BSD3-2R-b** (any NL form other than the corrected one,
  incl. resurrecting `yi^2 ∣ Δ`, or editing the old pin).
- **K-BSD3-2R-c** (armed on the SWEEP brick: if the corrected seam
  proves insufficient and a stronger form is needed, STOP and
  report).
- **K-BSD3-2R-d** (precision fence: the reused Props' bars are the
  bars; nothing quotes `L`/`Ω`/`sha` past them).

**What this file is NOT — the board fences, on the face.**
- **NO CLAIM; parts of Clay BSD closed: 0; dials 0/4** — before,
  during, and after this brick. The refined formula is not the
  official statement; this re-pin is a statement-grade instrument
  only. This brick proves nothing about the formula.

Honesty tiers in this file:
- **T5 (statement, unproved by design):** every def below — the
  corrected NL seam, the torsion-card seam, and the re-pin
  `BSDRefinedE3R`.
-/

/-! ## The corrected Nagell–Lutz seam -/

/-- **The corrected Nagell–Lutz seam for E3** (`NagellLutzCriterionE3R`,
the re-pin's instance), in the general Nagell–Lutz form only: every
torsion point of `E3(ℚ)` in affine coordinates has *integer* affine
coordinates whose `y`-coordinate satisfies `2*yi + 1 = 0` (the
2-torsion case) or `(2*yi + 1)^2 ∣ 161051` (here
`161051 = |Δ(E3)| = 11^5`; the general form is
`(2y + a1*x + a3)^2 ∣ Δ`, and for `E3`, `a1 = 0`, `a3 = 1`). A point
is torsion if some nonzero integer multiple of it is `0`. The
converse direction is *not* asserted. The Nagell–Lutz criterion
itself is not in Mathlib and is not proved here; it is carried as
this one labeled hypothesis, for the sweep brick to consume. Any
other form is **K-BSD3-2R-b**, a kill. -/
def NagellLutzCriterionE3R : Prop :=
  ∀ (x y : ℚ) (h : E3.toAffine.Nonsingular x y),
    (∃ n : ℤ, n ≠ 0 ∧
      n • (WeierstrassCurve.Affine.Point.some x y h :
        E3.toAffine.Point) = 0) →
    ∃ (xi yi : ℤ), x = (xi : ℚ) ∧ y = (yi : ℚ) ∧
      (2 * yi + 1 = 0 ∨ (2 * yi + 1) ^ 2 ∣ 161051)

/-! ## The torsion-card seam -/

/-- **E3's torsion-card seam.** `#E3(ℚ)_tors = 5`, carried **only**
as this named hypothesis `Prop`, in the same form as
`E1TorsionCardSeam` in `ThetLogos.BSDRefinedAssembly`. It is to be
discharged by the sweep brick conditional on
`NagellLutzCriterionE3R`; it is **not** a T4 value anywhere in this
entry. Stated as a `Prop`, proved nowhere. -/
def E3TorsionCardSeam : Prop :=
  Nat.card (AddCommGroup.torsion E3.toAffine.Point) = 5

/-! ## The re-pin -/

/-- **The E3 re-pin (statement only, brick BSD3-2R).** The same Prop
shape as the dead `BSDRefinedE3` and as `BSDRefinedE1`, for
`E3 : y² + y = x³ − x² − 10x − 20`, with E3's own labeled seams as
antecedents: the rank-0 seam (reused, **T4 recorded input**, Seam B4
labeled), the torsion-card seam (`E3TorsionCardSeam`, the new named
hypothesis of this entry — hence the literal `5` in `refinedRHS`),
the Sha seam (reused; Seam B1 licence, **K-BSD3-2R-a**), the in-pass
(c) L-value and period Props (reused), and the Tamagawa seam
instance (reused, `∏c_p = 5`). The refined right-hand side is taken
at `(Reg, tam, tors) = (1, 5, 5)`: the regulator is the literal `1`
(rank-0 empty-determinant convention). With the seams at their
recorded values `refinedRHS` reduces to `sha · Ω / 5`, and `sha` is
**derived by the later assembly's interval arithmetic, never
input** (the circularity fence). **No assembly theorem is stated or
proved in this brick.** -/
def BSDRefinedE3R : Prop :=
  ∀ (Lval ΩE3 : ℝ) (sha : ℕ) (tam : ℝ),
    E3RankZeroSeam → E3TorsionCardSeam → E3ShaFiniteSeam sha →
    E3LValue Lval → E3PeriodValue ΩE3 → E3TamagawaValue tam →
    |Lval - refinedRHS sha ΩE3 1 tam 5| ≤ 5e-3 ∧ sha = 1

end ThetLogos
