/-
# SolarTimeRung — the solar-time rung (seat-general form)

**Zero's ruling (2026-11-13 03:02 EST):** the rung is
stated over **any place's positive temperature
table**, not the Schoolcraft table only — ST-1–ST-4
quantify over an arbitrary positive table
`τ : Fin 12 → ℚ`; the Schoolcraft pin
(`ThetLogos.ThermalCalendarPin`) stands as the named
instance. ST-4 (the discrete bridge corollary) ships
in the first brick.

**Grade: finite correspondence between two owned
objects. NO CLAIM. Dial-ineligible; dials 0/4.**
Scope of record:
~/workspace/your_files/solar-time-rung-scope-2026-11-13.md

## What is proved

Fix a positive table `τ` (kelvin means, one per
month) and a mean clock exchange rate `β̄ > 0`. The
segment exchange rates are defined BY RATIO ONLY:
`β_m = β̄ · (τ̄ / τ_m)`, τ̄ the table's mean — the
bridge's conversion (`gibbs_conversion`, T1 of
`ThetLogos.ThermalClock`: laboratory time
= β × thermal time) then gives segment thermal time
`Δs_m = (1/12) / β_m`, and this module proves:

- ST-1: the table's Θ-step IS the segment thermal
  time in mean-year units:
  `tableStep τ m = Δs_m / (1/β̄)`.
- ST-2: the identification accumulates over the
  year, and the accumulated table step closes at
  exactly 1 (the seat-general `cumTheta_end`).
- ST-3: orientation — Θ-rates stand as temperatures
  (ratio form), and a hotter month takes a strictly
  larger Θ-step (the general form of the pin's
  `winter_slow_step`). **Θ lives on the s side of
  the β conversion**; the inverted reading is
  pre-registered kill K-SOLARTIME-INVERT, already
  refuted in instance by `winter_slow_step`.
- ST-4: conversion contact — for every matrix `K`
  (no hypotheses; `gibbs_conversion` needs none),
  flowing at segment `m`'s exchange rate for exactly
  its segment thermal time is flowing for the
  month's laboratory step `1/12`. The discrete
  bridge corollary the bridge side did not carry.

The Schoolcraft instance is named:
`tableStep_eq_thetaStep` — at `τ = monthTempK` the
seat-general step is the pin's `thetaStep`.

Declaration count: 3 definitions + 6 theorems. (The
scope priced 2–3 definitions for the pin-table
form; the seat-general ruling needs the step as a
function of the table as well — `tableStep` is that
one extra definition, disclosed here.)

## The fence (kills on the face)

- K-SOLARTIME-INVERT — the inverted (t-side)
  reading. Armed; refuted in instance by the pin.
- K-SOLARTIME-FLOW — "the calendar is a modular
  flow / a Gibbs clock." The calendar side owns no
  K, no state, no algebra; ST-4 quantifies over an
  arbitrary K precisely because the correspondence
  is about the thermal-time PARAMETER, never a
  dynamics.
- K-SOLARTIME-CONT — the continuous/λ form (the
  scope's ST-5): NOT STATEABLE in this tree (the
  pin carries no λ and no T_eq function; the bridge
  carries no track). FRONTIER; not attempted here.
- K-SOLARTIME-UNIT — any form needing k_B, ħ,
  seconds, or any physical unit. β̄ is an abstract
  exchange rate; temperatures enter as ratios only.
- K-SOLARTIME-PHYS — any physical reading. The
  pin's own K-MTC-EQ / K-MTC-TIME travel with the
  rung: designed arithmetic meeting a finite matrix
  bridge, both already fenced NO CLAIM.

The bridge side needs nothing new: DERIV-1 landed
(`ThermalTimeBridgeDeriv`, d6f17cf) — the bridge is
complete at twelve clauses; this rung runs on the
conversion clause alone, per the scope.

Names `tableStep`, `betaTrack`, `segTime` and the
theorem labels are working labels (scope §9.4 —
naming is Zero's).

Build note (disclosed, 2026-11-13): attempt 1
failed on four elaboration errors, all mechanical —
the two ℝ-valued definitions needed `noncomputable`
(ℝ division); two `field_simp` closings finished
their goals outright, leaving a trailing `ring`
with no goals; and ST-2's closure bridge is stated
from the univ side, mirroring the pin's own
`cumTheta_twelve` bridge. No statement changed.
-/

import ThetLogos.ThermalCalendarPin
import ThetLogos.ThermalClock

namespace ThetLogos

/-- **The seat-general Θ-step** — month `m`'s share
of the year under an arbitrary positive table `τ`:
its kelvin mean over the table's total. At the
Schoolcraft table this is the pin's `thetaStep`
(`tableStep_eq_thetaStep` below). -/
def tableStep (τ : Fin 12 → ℚ) (m : Fin 12) : ℚ :=
  τ m / ∑ k, τ k

/-- **The segment exchange rate** at month `m`, by
ratio only: `β_m = β̄ · (τ̄ / τ_m)` with `τ̄` the
table's mean — a colder month carries the larger
exchange rate. `β̄` is the mean clock's abstract
exchange rate (the corpus's β dialect: no units). -/
noncomputable def betaTrack (τ : Fin 12 → ℚ) (βbar : ℝ) (m : Fin 12) : ℝ :=
  βbar * (((∑ k, τ k) / 12 / τ m : ℚ) : ℝ)

/-- **The segment thermal time** at month `m`: the
month's laboratory step `1/12` read through the
bridge's conversion at the segment's exchange rate,
`Δs_m = (1/12) / β_m`. -/
noncomputable def segTime (τ : Fin 12 → ℚ) (βbar : ℝ) (m : Fin 12) : ℝ :=
  (1 / 12) / betaTrack τ βbar m

/-- **The named instance:** at the Schoolcraft
table (`τ = monthTempK`) the seat-general step is
the pin's own `thetaStep`. -/
theorem tableStep_eq_thetaStep (m : Fin 12) :
    tableStep monthTempK m = thetaStep m := by
  unfold tableStep thetaStep thermalWeight meanK totalK
  rw [div_div, div_mul_cancel₀ _ (by norm_num : (12 : ℚ) ≠ 0)]

/-- **ST-1 — segment identification.** For every
positive table `τ`, every `β̄ > 0`, and every month
`m`: the Θ-step is the segment's bridge thermal
time measured in mean-year units
(`1 / β̄` is the mean clock's full-year thermal
time). -/
theorem st1_segment_identification {τ : Fin 12 → ℚ}
    (hτ : ∀ m, 0 < τ m) {βbar : ℝ} (hβ : 0 < βbar)
    (m : Fin 12) :
    (tableStep τ m : ℝ) = segTime τ βbar m / (1 / βbar) := by
  have hsum : (0 : ℚ) < ∑ k, τ k :=
    Finset.sum_pos (fun k _ => hτ k) Finset.univ_nonempty
  have ha : (τ m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (hτ m)
  have hS : (∑ k, (τ k : ℝ)) ≠ 0 := by
    rw [← Rat.cast_sum]
    exact_mod_cast ne_of_gt hsum
  have hb : βbar ≠ 0 := ne_of_gt hβ
  have e1 : (tableStep τ m : ℝ)
      = (τ m : ℝ) / (∑ k, (τ k : ℝ)) := by
    simp only [tableStep, Rat.cast_div, Rat.cast_sum]
  rw [e1]
  unfold segTime betaTrack
  push_cast
  field_simp

/-- **ST-2 — accumulation, with the year closure.**
The identification accumulates segment by segment
over any initial stretch of `n ≤ 12` months (both
sides indexed by the pin's own `% 12` convention),
and the accumulated table step over the full year
is exactly 1 — the seat-general `cumTheta_end`:
the track's year of thermal time is the mean
year's. -/
theorem st2_accumulation {τ : Fin 12 → ℚ}
    (hτ : ∀ m, 0 < τ m) {βbar : ℝ} (hβ : 0 < βbar)
    {n : ℕ} (hn : n ≤ 12) :
    (∑ m ∈ Finset.range n,
        (tableStep τ ⟨m % 12, Nat.mod_lt _ (by norm_num)⟩ : ℝ))
      = (∑ m ∈ Finset.range n,
          segTime τ βbar ⟨m % 12, Nat.mod_lt _ (by norm_num)⟩)
        / (1 / βbar)
    ∧ (∑ m ∈ Finset.range 12,
        (tableStep τ ⟨m % 12, Nat.mod_lt _ (by norm_num)⟩ : ℝ))
      = 1 := by
  have hsum : (0 : ℚ) < ∑ k, τ k :=
    Finset.sum_pos (fun k _ => hτ k) Finset.univ_nonempty
  have hS : (∑ k, (τ k : ℝ)) ≠ 0 := by
    rw [← Rat.cast_sum]
    exact_mod_cast ne_of_gt hsum
  constructor
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro m _
    exact st1_segment_identification hτ hβ _
  · have hbridge : ∀ m : Fin 12, (tableStep τ m : ℝ)
        = (fun i => (tableStep τ
            ⟨i % 12, Nat.mod_lt _ (by norm_num)⟩ : ℝ)) m.1 := by
      intro m
      have hfin : (⟨m.1 % 12, Nat.mod_lt _ (by norm_num)⟩ : Fin 12)
          = m := Fin.ext (Nat.mod_eq_of_lt m.2)
      show (tableStep τ m : ℝ)
        = (tableStep τ ⟨m.1 % 12, Nat.mod_lt _ (by norm_num)⟩ : ℝ)
      rw [hfin]
    have hsum : (∑ m : Fin 12, (tableStep τ m : ℝ))
        = ∑ i ∈ Finset.range 12,
          (tableStep τ ⟨i % 12, Nat.mod_lt _ (by norm_num)⟩ : ℝ) := by
      rw [← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl (fun m _ => hbridge m)
    rw [← hsum]
    have e1 : ∀ m : Fin 12, (tableStep τ m : ℝ)
        = (τ m : ℝ) / (∑ k, (τ k : ℝ)) := by
      intro m
      simp only [tableStep, Rat.cast_div, Rat.cast_sum]
    rw [Finset.sum_congr rfl (fun m _ => e1 m), ← Finset.sum_div]
    exact div_self hS

/-- **ST-3 (i) — the rate ratio.** At equal
laboratory steps, Θ-rates stand as temperatures:
the step ratio of two months is their kelvin
ratio, the table total cancelling. -/
theorem st3_rate_ratio {τ : Fin 12 → ℚ}
    (hτ : ∀ m, 0 < τ m) (m m' : Fin 12) :
    tableStep τ m / tableStep τ m' = τ m / τ m' := by
  have hsum : (0 : ℚ) < ∑ k, τ k :=
    Finset.sum_pos (fun k _ => hτ k) Finset.univ_nonempty
  have hS : (∑ k, τ k) ≠ 0 := ne_of_gt hsum
  have hm' : τ m' ≠ 0 := ne_of_gt (hτ m')
  unfold tableStep
  field_simp

/-- **ST-3 (ii) — orientation / monotonicity.** A
hotter month takes a strictly larger Θ-step: the
general form of the pin's `winter_slow_step`, and
the theorem form of the β-side pin — Θ accumulates
on the thermal-time (s) side of the conversion,
never the laboratory (t) side
(K-SOLARTIME-INVERT). -/
theorem st3_orientation {τ : Fin 12 → ℚ}
    (hτ : ∀ m, 0 < τ m) {m m' : Fin 12}
    (h : τ m < τ m') :
    tableStep τ m < tableStep τ m' := by
  have hsum : (0 : ℚ) < ∑ k, τ k :=
    Finset.sum_pos (fun k _ => hτ k) Finset.univ_nonempty
  show τ m / (∑ k, τ k) < τ m' / (∑ k, τ k)
  exact div_lt_div_of_pos_right h hsum

/-- **ST-4 — conversion contact (the discrete
bridge corollary).** For every matrix `K` — no
hypotheses, as `gibbs_conversion` needs none —
every month `m`, and every observable `B`: flowing
at the segment's exchange rate for exactly its
segment thermal time is flowing for the month's
laboratory step `1/12`. The calendar's
Θ-bookkeeping and the bridge's conversion agree
segment by segment. -/
theorem st4_conversion_contact {τ : Fin 12 → ℚ}
    (hτ : ∀ m, 0 < τ m) {βbar : ℝ} (hβ : 0 < βbar)
    (m : Fin 12) {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (B : Matrix (Fin N) (Fin N) ℂ) :
    modularFlow ((betaTrack τ βbar m : ℂ) • K)
        (segTime τ βbar m) B
      = modularFlow K (1 / 12) B := by
  have hsum : (0 : ℚ) < ∑ k, τ k :=
    Finset.sum_pos (fun k _ => hτ k) Finset.univ_nonempty
  have hpos : (0 : ℚ) < (∑ k, τ k) / 12 / τ m :=
    div_pos (div_pos hsum (by norm_num)) (hτ m)
  have hbt : betaTrack τ βbar m ≠ 0 := by
    unfold betaTrack
    apply mul_ne_zero (ne_of_gt hβ)
    have h2 : (0 : ℝ) < (((∑ k, τ k) / 12 / τ m : ℚ) : ℝ) := by
      exact_mod_cast hpos
    exact ne_of_gt h2
  have hprod : betaTrack τ βbar m * segTime τ βbar m
      = 1 / 12 := by
    unfold segTime
    field_simp
  rw [gibbs_conversion, hprod]

end ThetLogos
