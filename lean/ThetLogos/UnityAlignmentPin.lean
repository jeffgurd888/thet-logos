/-
# UnityAlignmentPin — the rational frame arithmetic of the
Modular Thermal Equilibrium Calendar's unity alignment
(working label; final naming is Zero's)

**Design study. NO CLAIM. Dial-ineligible.**
Zero's line (commissioned 2026-11-17, "pin it"): the Unity
alignment memo, `unity-alignment-memo-2026-11-17.md`. This
module pins the memo's rational frame arithmetic — the
spans and residue bounds by which the calendar's
independent lunar ring returns against its solar–thermal
frame — and proves its elementary facts in the kernel. It
is a pin of a designed object's arithmetic, not a theorem
about the Moon, the Earth's orbit, or astronomy. NO CLAIM
on any dial; the calendar is a design study (T5) and this
pin changes no tier.

## The pinned constants

Two Register-2 astronomical inputs, pinned as design
values exactly as `ThermalCalendarPin` pins its
temperature table — entered as data, not derived:

    synodicMonth = 29.530589 days
    tropicalYear = 365.24219 days

## What is pinned

Residues are stated as inequalities only: the difference
of two spans, and the rational interval it lies in. Brick 1
pins the 19-year span (235 lunations against 19 tropical
years) and the LogicLock frame spans over 19 years with 4
and 5 leap residuals (`frameSpan`: 19 × 365 frame days —
364 counted days plus the one Boundary Day per year — plus
the leap days, which take no counted label by Zero's
ruling of 2026-11-14). Brick 2 pins the 8-year span
(99 lunations), the 334-year span (4131 lunations), the
module-versus-lunation comparison, and the lunations-per-
year bounds.
-/

import Mathlib.Tactic.NormNum

namespace ThetLogos

/-- The synodic month, in days: a Register-2 astronomical
input pinned as a design value (29.530589), exactly as
`ThermalCalendarPin` pins its temperature table. Entered
as data; not derived. -/
def synodicMonth : ℚ := 29530589 / 1000000

/-- The tropical year, in days: a Register-2 astronomical
input pinned as a design value (365.24219). Entered as
data; not derived. -/
def tropicalYear : ℚ := 36524219 / 100000

/-- The total span, in days, of `n` lunations at the
pinned synodic month. -/
def lunationSpan (n : ℕ) : ℚ := n * synodicMonth

/-- The LogicLock frame span, in days, over 19 years with
`leaps` leap residuals: 19 × 365 frame days (364 counted
days plus the one Boundary Day per year), plus the leap
days, which take no counted label. -/
def frameSpan (leaps : ℕ) : ℚ := 19 * 365 + leaps

/-- 235 lunations at the pinned synodic month span exactly
6939688415/1000000 days. -/
theorem lunationSpan_235 : lunationSpan 235 = 6939688415 / 1000000 := by
  norm_num [lunationSpan, synodicMonth]

/-- The 19-year residue bounds: the difference of 235
lunations over 19 tropical years lies in (0, 1/10). -/
theorem metonic_residue_bounds :
    0 < lunationSpan 235 - 19 * tropicalYear ∧
    lunationSpan 235 - 19 * tropicalYear < 1 / 10 := by
  refine ⟨by norm_num [lunationSpan, synodicMonth, tropicalYear],
    by norm_num [lunationSpan, synodicMonth, tropicalYear]⟩

/-- The 19-year frame span with 4 leap residuals is
exactly 6939 days. -/
theorem frameSpan_four : frameSpan 4 = 6939 := by
  norm_num [frameSpan]

/-- The 235-lunation span lies strictly between the
4-leap frame span and that span plus one day. -/
theorem frameSpan_four_bounds :
    frameSpan 4 < lunationSpan 235 ∧ lunationSpan 235 < frameSpan 4 + 1 := by
  refine ⟨by norm_num [frameSpan, lunationSpan, synodicMonth],
    by norm_num [frameSpan, lunationSpan, synodicMonth]⟩

/-- The 19-year frame span with 5 leap residuals is
exactly 6940 days. -/
theorem frameSpan_five : frameSpan 5 = 6940 := by
  norm_num [frameSpan]

/-- The 235-lunation span lies strictly between the
5-leap frame span minus one day and the 5-leap frame span
itself: the span is less than the frame span, and the
frame span is less than the lunation span plus one day. -/
theorem frameSpan_five_bounds :
    lunationSpan 235 < frameSpan 5 ∧ frameSpan 5 < lunationSpan 235 + 1 := by
  refine ⟨by norm_num [frameSpan, lunationSpan, synodicMonth],
    by norm_num [frameSpan, lunationSpan, synodicMonth]⟩

/-- The octaeteris residue: 99 lunations against 8 tropical years,
    as inequalities only. -/
theorem octaeteris_residue_bounds :
    1 < 99 * synodicMonth - 8 * tropicalYear ∧
    99 * synodicMonth - 8 * tropicalYear < 2 := by
  constructor <;> norm_num [synodicMonth, tropicalYear]

/-- The 334-year residue: 4131 lunations against 334 tropical years,
    bounded in absolute value, as an inequality only. -/
theorem cycle334_residue_abs_bound :
    |4131 * synodicMonth - 334 * tropicalYear| < 1 / 25 := by
  rw [abs_lt]
  constructor <;> norm_num [synodicMonth, tropicalYear]

/-- A 28-day module is shorter than one lunation: the pinned synodic
    month lies strictly between 28 and 30 days. -/
theorem synodicMonth_bounds :
    28 < synodicMonth ∧ synodicMonth < 30 := by
  constructor <;> norm_num [synodicMonth]

/-- Lunations per tropical year, as inequalities only: strictly
    between 12 and 13. -/
theorem lunations_per_year_bounds :
    12 < tropicalYear / synodicMonth ∧
    tropicalYear / synodicMonth < 13 := by
  have hpos : (0 : ℚ) < synodicMonth := by norm_num [synodicMonth]
  constructor
  · rw [lt_div_iff₀ hpos]; norm_num [synodicMonth, tropicalYear]
  · rw [div_lt_iff₀ hpos]; norm_num [synodicMonth, tropicalYear]

end ThetLogos
