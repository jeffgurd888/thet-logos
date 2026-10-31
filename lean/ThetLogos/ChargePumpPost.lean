import Mathlib.Tactic
import ThetLogos.ThermalZ4Ladder
import ThetLogos.ThermalZ4KMS
import ThetLogos.ThermalZ4ClockDefect
import ThetLogos.KMSBridge

namespace ThetLogos

/-!
# ThetLogos.ChargePumpPost — PUMP-0: the charge pump registration pin

**Status: REGISTRATION ONLY — definitions and stated `Prop`s, plus the
one proved face check below. NO CLAIM. No Millennium statement, no
ladder rung, no dial (dials stay 0/4).**

Commission: Jeff's "build all that we can," 2026-10-31. Governing
memo: `routeb-general-scratch/scoping-charge-pump-2026-10-31.md`
(§0 verdict, §1 the pin exact, §2 headline Props H1–H3, §4 the
PUMP-0 row, §5 kills K-PUMP-1..5, §6 rope). Working label: PUMP.
The item registered is Jeff's clarification of 2026-10-30 — a
spectral density matrix charge pump — in the repaired reading the
standing audits left standing: a pump is STATE + A NAMED DRIVEN
STEP OR CYCLE, transporting a chosen grading by redistribution,
with the cost accounted per cycle. Nothing stronger registers.

## The pin, as data (§1)

The seat is the corpus's owned 4-rung ladder, and nothing is
imported from any composite. The named state is the Gibbs state
of the ladder generator at inverse temperature `β`,
`ρ(β) := gibbsState z4Generator β`, identified numeral-for-numeral
with the ladder weights by the landed theorem `z4_gibbsState_eq`.
The named sectors are a CHOSEN site grading on the rung set — pin
data, not a derived object: `A = {0, 1}` and `B = {2, 3}` as
subsets of `Fin 4`, the low and high halves of the ladder. The
named drive is the Z4 clock turn `z4Shift`, applied by an
EXTERNAL protocol in four steps; the four-times-turned weights
return exactly to `z4Weight β`, since `k + 4 = k` in `Fin 4`.
The seat hypothesis `β > 0` is load-bearing and is never dropped
from any statement in this line (see H1).

## Honesty clause (§1, part of the pin, not a caveat beneath it)

NO owned charge operator exists at this seat. The corpus's charge
vocabulary lives on the Standard-Model side, and the composite's
charge grading is another line's unbuilt object. This pin's
sectors are rungs of a ladder and `popB` is population of a CHOSEN
rung label; the transported quantity is sector population of that
label. Its identification with electric charge is Jeff's T5
reading and is asserted nowhere in this line.

## Stationarity fence (K-PUMP-2)

The drive is external protocol data; it is never the state's own
dynamics. Under the state's own modular flow the state is fixed —
the landed theorem `gibbsWeight_stationary` of `KMSBridge` — so
no form of "the density matrix pumps itself" is statable at this
seat. The clock turns are APPLIED; β enters only through the
state's weights: it makes the weights uneven so there is
something to transport, and its sign sets the flux direction.
The clock does the transporting.

## K-PUMP-4 language discipline (binds this module's prose too)

The honest words are fixed: per-step flux, winding total one,
net zero, drive external, β sets the weights. Net transported
population per cycle is ZERO — H2(ii) states it and this face
repeats it: the state returns exactly after one cycle and the
net sector change over the cycle is exactly `0`. No sentence in
this line may sell the pump as producing net transfer from one
sector to the other per cycle, as driven by heat rather than by
the clock protocol, or may state the flux headline without its
`β > 0` hypothesis. The trace-defect total of the drive is also
exactly `0` (H2(iv)): the cost is paid in state distortion under
an external drive, accounted by the landed clock-defect factors
(`z4_clock_defect_factor`, cited, not re-proved), not in trace.
Conservation is a rail, never a result (K-PUMP-3): the weights
sum to `1` (`z4Weight_sum_eq_one`, landed) and the drive permutes
them, so total population is conserved by construction.

## Pre-registered kills, named on the face

- K-PUMP-1 (vacuity / commuting drive): if the pinned drive
  preserved the sector partition, per-step flux would be zero by
  construction. Guard, discharged at registration below: the
  drive's non-preservation is exhibited on this face
  (`chargePump_face_check`).
- K-PUMP-2 (autonomy): any form in which the density matrix's
  own dynamics does the pumping is dead on arrival
  (`gibbsWeight_stationary`; see the fence above).
- K-PUMP-3 (conservation as content, or violated): conservation
  is the rail that makes the transport redistribution; it may be
  cited as such and never reported as a result of this line.
- K-PUMP-4 (net-transport overclaim — reporting kill): see the
  language discipline above; it fires on the reporting, at the
  same volume as a win.
- K-PUMP-5 (field / continuum creep): no electromagnetic field
  object is defined, constructed, or implied anywhere in this
  line, and no continuum box, temperature field, or spatial
  transport appears.

## Rope (§6)

NO CLAIM; dials 0/4. The crossing total `1` of H2(iii) is one
unit of total probability mass winding a 4-ring — a dimensionless
normalization fact about a chosen ladder, not a derived measured
number. This pin is not a gravity object, not a continuum limit,
and not an externally confirmed prediction. Jeff's vacuum-box
chain remains T5 regardless of this line's outcome, and this
line's outcome may not be cited as movement on it, for the three
named reasons of memo §6: the sectors are chosen, not physical;
the mover is a clock, not heat; and there is no field object at
this seat. The cycle is not an energy source: it returns its
state exactly, its drive is external, and battery passivity
(`sliceBattery_extracted_nonpos`, cited by name) stands over the
line. This line is free-standing: it depends on the landed Z4
line and `KMSBridge` only, and neither feeds, duplicates, nor
gates the composite charge-grading line.
-/

/-! ## §1. The pin as data: sectors, label function, population -/

/-- The chosen high sector `B = {2, 3}` of the 4-rung ladder:
pin data, a chosen rung subset, not a derived object. -/
def chargePumpSectorB : Finset (Fin 4) := {2, 3}

/-- The chosen low sector `A = {0, 1}` of the 4-rung ladder:
pin data, the complement half of the chosen grading. -/
def chargePumpSectorA : Finset (Fin 4) := {0, 1}

/-- The sector label function `χB : Fin 4 → ℝ`: `χB k = 1` if
`k ∈ B`, else `0`. Population of this CHOSEN label is the only
quantity this line transports; see the honesty clause above. -/
def χB (k : Fin 4) : ℝ := if k ∈ chargePumpSectorB then 1 else 0

/-- The diagonal matrix form of the label function:
`QB := Matrix.diagonal χB`. A chosen-label diagonal, registered
as pin data; it is not an owned charge operator (honesty
clause). -/
def QB : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal χB

/-- Sector population of a weight function `w : Fin 4 → ℝ`:
`popB w := ∑ k ∈ B, w k` — the population of the chosen label
`B`, equivalently `∑ k, w k * χB k`. -/
def popB (w : Fin 4 → ℝ) : ℝ := ∑ k ∈ chargePumpSectorB, w k

/-! ## §1 (continued). The named state and the external drive -/

/-- The named state: the Gibbs state of the ladder generator at
inverse temperature `β`, `ρ(β) := gibbsState z4Generator β`,
identified with the ladder weights by the landed theorem
`z4_gibbsState_eq`. A state only: by itself, under its own flow,
it does nothing (`gibbsWeight_stationary`). -/
noncomputable def chargePumpState (β : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  gibbsState z4Generator β

/-- The drive as protocol data: the `j`-times clock-turned
weights, read in the landed pullback form — the turned weight at
rung `k` is `z4Weight β (k + j)`, with `j : Fin 4` and modular
addition on `Fin 4`. Four turns return the weights exactly,
since `k + 4 = k` in `Fin 4`. The turns are APPLIED by an
external protocol; this is not the state's own dynamics. -/
noncomputable def chargePumpTurnedWeight (β : ℝ) (j k : Fin 4) : ℝ :=
  z4Weight β (k + j)

/-- The per-step sector flux at step `j`: the change in `popB`
under the `(j+1)`-th clock turn applied to the `j`-times-turned
weights, `Δⱼ := popB (turned (j+1)) − popB (turned j)`. -/
noncomputable def chargePumpFlux (β : ℝ) (j : Fin 4) : ℝ :=
  popB (chargePumpTurnedWeight β (j + 1)) - popB (chargePumpTurnedWeight β j)

/-- The per-step energy exchange at step `j`:
`Δ⟨E⟩ⱼ := ∑ k, z4Energy k * (turned (j+1) weight at k − turned j
weight at k)`, the drive's energy ledger on the ladder's chosen
energies. -/
noncomputable def chargePumpEnergyExchange (β : ℝ) (j : Fin 4) : ℝ :=
  ∑ k : Fin 4, z4Energy k *
    (chargePumpTurnedWeight β (j + 1) k - chargePumpTurnedWeight β j k)

/-! ## §2. Headline Props H1–H3, stated verbatim in substance

Statements only — no theorem is attempted in this brick, and
nothing here asserts that any registered Prop holds, beyond the
single face check proved at the end of the module. -/

/-- **(H1) Per-step flux identity, with teeth (memo §2).** For
every `β`: the one-turn change in sector population is
`popB (z4ShiftedWeight β) − popB (z4Weight β)
  = z4Weight β 0 − z4Weight β 2
  = (1 − Real.exp (−β / 2)) / z4Partition β`.
For every `β` with `0 < β` — the hypothesis is ON the statement
and is never dropped (K-PUMP-4) — that flux is strictly
positive. At `β = 0` the flux is `0` (uniform weights). The
pump's direction is set by the sign of `β`. Target of PUMP-1. -/
def chargePumpH1 : Prop :=
  (∀ β : ℝ,
    popB (z4ShiftedWeight β) - popB (z4Weight β)
        = z4Weight β 0 - z4Weight β 2 ∧
    popB (z4ShiftedWeight β) - popB (z4Weight β)
        = (1 - Real.exp (-β / 2)) / z4Partition β) ∧
  (∀ β : ℝ, 0 < β →
    0 < popB (z4ShiftedWeight β) - popB (z4Weight β)) ∧
  (popB (z4ShiftedWeight 0) - popB (z4Weight 0) = 0)

/-- **(H2) Cycle accounting (memo §2) — the per-cycle
deliverable.** For the 4-step cycle at every `β` with `0 < β`:
(i) **state return:** the four-times clock-turned weights equal
`z4Weight β` exactly;
(ii) **net sector change zero:** `∑ j : Fin 4, Δⱼ = 0`, with
`Δ₀ = z4Weight β 0 − z4Weight β 2`,
`Δ₁ = z4Weight β 1 − z4Weight β 3`, and `Δⱼ₊₂ = −Δⱼ`;
(iii) **crossing total one:** for every fixed directed
rung-to-rung edge, read at rung `e`, the sum over the cycle of
the turned weight at `e` is exactly `1` — each rung's weight
crosses each directed edge exactly once per cycle, and the total
is `z4Weight_sum_eq_one`;
(iv) **defect paid:** at every step the turned weights still sum
to `1`, so the trace-defect total of the drive is exactly `0`,
and the per-step energy exchanges `Δ⟨E⟩ⱼ` have cycle total `0`;
the intermediate states carry the landed clock defect of
`z4_clock_defect_factor` (cited, not re-proved).
Together (i)+(ii)+(iii) say the pump moves the chosen label
AROUND, measurably, per step, while moving none NET —
redistribution, exactly as the standing re-audit required.
Target of PUMP-2. -/
def chargePumpH2 : Prop :=
  ∀ β : ℝ, 0 < β →
    ((fun k => z4Weight β
        (z4Shift (z4Shift (z4Shift (z4Shift k))))) = z4Weight β) ∧
    ((∑ j : Fin 4, chargePumpFlux β j = 0) ∧
      chargePumpFlux β 0 = z4Weight β 0 - z4Weight β 2 ∧
      chargePumpFlux β 1 = z4Weight β 1 - z4Weight β 3 ∧
      (∀ j : Fin 4, chargePumpFlux β (j + 2) = -chargePumpFlux β j)) ∧
    (∀ e : Fin 4, ∑ j : Fin 4, chargePumpTurnedWeight β j e = 1) ∧
    ((∀ j : Fin 4, ∑ k : Fin 4, chargePumpTurnedWeight β j k = 1) ∧
      (∑ j : Fin 4, chargePumpEnergyExchange β j = 0))

/-- **(H3) Who does the pumping — the drive characterization
(memo §2).** For any bijection `π : Fin 4 → Fin 4`:
`(∀ w : Fin 4 → ℝ, popB (w ∘ π) = popB w)
  ↔ (∀ k, k ∈ B ↔ π k ∈ B)`
— a drive transports no sector population for any state iff it
preserves the sector partition. And `z4Shift` does NOT preserve
it (the face check below: `χB (z4Shift 1) = χB 2 = 1 ≠ 0 = χB 1`),
which is exactly why the clock pumps and a sector-preserving
drive cannot. Registered corollary, citing the landed theorem
rather than re-proving it: under the state's own modular flow
the state is fixed (`gibbsWeight_stationary`), so transport is
a property of the drive's action on the partition, and the state
alone does nothing. Target of PUMP-3. -/
def chargePumpH3 : Prop :=
  ∀ π : Fin 4 → Fin 4, Function.Bijective π →
    ((∀ w : Fin 4 → ℝ, popB (w ∘ π) = popB w) ↔
      (∀ k : Fin 4, k ∈ chargePumpSectorB ↔ π k ∈ chargePumpSectorB))

/-! ## The face check (K-PUMP-1 guard, discharged at registration)

The one proved item in this brick: the pinned drive does not
preserve the sector partition, exhibited at rung `1` — the clock
turn sends rung `1` (label `0`) to rung `2` (label `1`). A
registration that could not exhibit a failing case for its own
transport Prop would stop here (K-PUMP-1). -/

/-- **Face check (K-PUMP-1 guard).** `χB (z4Shift 1) ≠ χB 1`:
the clock turn crosses the sector cut at rung `1`. A decidable
numeral fact at the seat — the shifted rung is the `Fin 4`
numeral `2`, in `B`; rung `1` is not. Tier T1. -/
theorem chargePump_face_check : χB (z4Shift 1) ≠ χB 1 := by
  norm_num [χB, chargePumpSectorB, z4Shift]

end ThetLogos
