/-
# ThermalMetricPin — the 0.0 Thermal Metric, carded

**Scope:
~/workspace/your_files/thermal-metric-pin-scope-2026-11-13.md
(flagged in the 2026-11-12 night log; opened by Zero
2026-11-13). NO CLAIM. Design-study metric, T5 on its
face. Dial-ineligible.**

THE CLAIM BEING CARDED (definitional): the 0.0
Thermal Metric exhibit's engine — one temperature
spine, `r = T / T̄` with `T̄ = 281.47 K` (the pinned
Schoolcraft mean), gold unity at `r = 1`, absolute
zero at the 0.0 foot. The pin cards the metric; it
does not prove physics.

FENCE (the scope's): `T̄` is an INPUT — the pinned
value, as the exhibit carries it — never a derived
constant (the K-SOLARTIME-UNIT discipline). Nothing
in this module derives 281.47 from anything.

STATUS: STATUS-METRIC.md.
-/

import Mathlib.Tactic

namespace ThetLogos

/-- **The pinned mean `T̄ = 281.47 K`** — an INPUT, as
the exhibit carries it (the pinned Schoolcraft mean),
stated as the exact rational `28147/100`. Not derived
from any table in this module or any other. -/
def Tbar : ℚ := 28147 / 100

/-- The thermal ratio: `r = T / T̄` — position on the
one temperature spine, in units of the pinned mean. -/
def r (T : ℚ) : ℚ := T / Tbar

/-- The pinned mean is positive (the spine's unit is a
genuine temperature). -/
theorem Tbar_pos : 0 < Tbar := by
  norm_num [Tbar]

/-- M-1: the unity marker is exact — at the pinned
mean, `r = 1` (gold unity). -/
theorem r_Tbar : r Tbar = 1 :=
  div_self (ne_of_gt Tbar_pos)

/-- M-2: the 0.0 foot is absolute zero — `r(0) = 0`. -/
theorem r_zero : r 0 = 0 :=
  zero_div _

/-- M-3: the spine preserves order strictly — `r` is
strictly monotone in `T`: order on the spine is order
on temperature. -/
theorem r_strictMono : StrictMono r := by
  intro a b hab
  rw [r, r, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul_of_pos_right hab (inv_pos.mpr Tbar_pos)

end ThetLogos
