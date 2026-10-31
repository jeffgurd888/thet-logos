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

/-! ## PUMP-1: the one-turn flux identity

The transported quantity throughout this section is the
POPULATION OF THE CHOSEN RUNG LABEL `B = {2, 3}` — `popB` of a
weight function — and nothing else: no charge operator is owned
or asserted at this seat (the registration's honesty clause).
One clock turn redistributes that population inside the closed
4-cycle: the turned population of `B` is read off rung by rung
below, and the one-turn flux at step `0` is exactly the rung-`0`
weight minus the rung-`2` weight. Net transported population
over the full cycle is zero (that accounting is the next
brick's registered content, not this one's); nothing here
asserts any one-way transfer. The hypothesis `β > 0` is carried
on every positivity statement and is never dropped: at `β = 0`
the flux vanishes, and no statement here asserts transport at
`β ≤ 0` beyond that proved vanishing. Conservation and
stationarity are rails, cited from the landed ladder and
`KMSBridge`, never results of this brick: the weights sum to
`1` (`z4Weight_sum_eq_one`), the drive permutes them, and the
state's own modular flow does nothing
(`gibbsWeight_stationary`) — the drive is the external
`z4Shift` protocol. No field object appears anywhere. NO
CLAIM; dials 0/4. -/

/-- The population of the chosen label `B = {2, 3}` of a weight
function is its rung-`2` weight plus its rung-`3` weight. -/
theorem chargePump_popB_eq (w : Fin 4 → ℝ) :
    popB w = w 2 + w 3 := by
  rw [popB, chargePumpSectorB]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

/-- The unturned population of the chosen label: the Gibbs
weights at rungs `2` and `3`. -/
theorem chargePump_popB_weight (β : ℝ) :
    popB (z4Weight β) = z4Weight β 2 + z4Weight β 3 :=
  chargePump_popB_eq _

/-- One clock turn moves the label population's support: the
turned weight at rung `2` is the rung-`3` weight, and at rung
`3` it is the rung-`0` weight (the wrap of the 4-cycle). -/
theorem chargePump_popB_shifted (β : ℝ) :
    popB (z4ShiftedWeight β) = z4Weight β 3 + z4Weight β 0 := by
  rw [chargePump_popB_eq]
  have h2 : z4ShiftedWeight β 2 = z4Weight β 3 := by
    have hidx : (2 : Fin 4) + 1 = 3 := by decide
    rw [z4ShiftedWeight, z4Shift, hidx]
  have h3 : z4ShiftedWeight β 3 = z4Weight β 0 := by
    have hidx : (3 : Fin 4) + 1 = 0 := by decide
    rw [z4ShiftedWeight, z4Shift, hidx]
  rw [h2, h3]

/-- The `j`-times-turned population of the chosen label, in the
registered turned-weight form: the weights at rungs `2 + j` and
`3 + j` (modular addition on `Fin 4`). -/
theorem chargePump_popB_turned (β : ℝ) (j : Fin 4) :
    popB (chargePumpTurnedWeight β j)
      = z4Weight β (2 + j) + z4Weight β (3 + j) := by
  rw [chargePump_popB_eq]
  rfl

/-- **The one-turn flux identity (H1, first face).** The
one-turn change in the chosen label's population is the
rung-`0` weight minus the rung-`2` weight: the turn carries
rung `3`'s population out of the label at the wrap and rung
`2`'s population into rung `3`, leaving exactly this
difference. A redistribution inside the closed 4-cycle. -/
theorem chargePump_flux_eq (β : ℝ) :
    popB (z4ShiftedWeight β) - popB (z4Weight β)
      = z4Weight β 0 - z4Weight β 2 := by
  rw [chargePump_popB_shifted, chargePump_popB_weight]
  ring

/-- **The general-step flux formula.** At every step `j`, the
per-step flux of the chosen label's population is the rung-`j`
weight minus the rung-`(j+2)` weight (indices mod `4` in the
registered turned-weight form): each step's gain at the wrap
is the weight two rungs ahead of the rung the label loses. -/
theorem chargePumpFlux_eq (β : ℝ) (j : Fin 4) :
    chargePumpFlux β j = z4Weight β j - z4Weight β (j + 2) := by
  have ha : ∀ j : Fin 4, 2 + (j + 1) = j + 3 := by
    intro j; fin_cases j <;> decide
  have hb : ∀ j : Fin 4, 3 + (j + 1) = j := by
    intro j; fin_cases j <;> decide
  have hc : ∀ j : Fin 4, 3 + j = j + 3 := by
    intro j; fin_cases j <;> decide
  have hd : ∀ j : Fin 4, 2 + j = j + 2 := by
    intro j; rw [add_comm]
  rw [chargePumpFlux, chargePump_popB_turned β (j + 1),
    chargePump_popB_turned β j, ha j, hb j, hc j, hd j]
  ring

/-- The step-`0` flux in the registered `chargePumpFlux` form:
`chargePumpFlux β 0 = z4Weight β 0 − z4Weight β 2`, the same
one-turn identity as `chargePump_flux_eq`. -/
theorem chargePumpFlux_zero_eq (β : ℝ) :
    chargePumpFlux β 0 = z4Weight β 0 - z4Weight β 2 := by
  have hidx : (0 : Fin 4) + 2 = 2 := by decide
  rw [chargePumpFlux_eq β 0, hidx]

/-- **The closed form (H1, second face).** Against the ladder's
landed normalization — energies `0, 1/4, 1/2, 3/4`, so rung `0`
carries numerator `1` and rung `2` carries numerator
`exp (−β/2)`, both over the same partition sum:
`z4Weight β 0 − z4Weight β 2
  = (1 − Real.exp (−β / 2)) / z4Partition β`. -/
theorem chargePump_weight_sub_closed (β : ℝ) :
    z4Weight β 0 - z4Weight β 2
      = (1 - Real.exp (-β / 2)) / z4Partition β := by
  have hE0 : z4Energy (0 : Fin 4) = 0 := by
    unfold z4Energy; simp
  have hE2 : z4Energy (2 : Fin 4) = 1 / 2 := by
    unfold z4Energy; norm_num
  have hexp : -β * z4Energy (2 : Fin 4) = -β / 2 := by
    rw [hE2]; ring
  unfold z4Weight
  rw [hE0, hexp]
  simp only [mul_zero, Real.exp_zero]
  rw [← sub_div]

/-- The step-`0` flux in closed form:
`chargePumpFlux β 0 = (1 − Real.exp (−β / 2)) / z4Partition β`
at every `β`. -/
theorem chargePumpFlux_closed (β : ℝ) :
    chargePumpFlux β 0
      = (1 - Real.exp (-β / 2)) / z4Partition β := by
  rw [chargePumpFlux_zero_eq, chargePump_weight_sub_closed]

/-- **Positivity exactly at `β > 0` (H1, teeth).** For every
`β` with `0 < β` — the hypothesis is on the statement and is
never dropped — the one-turn flux of the chosen label's
population is strictly positive: `exp (−β/2) < 1` exactly
because `β > 0`, and the partition sum is positive. -/
theorem chargePumpFlux_pos_of_pos {β : ℝ} (hβ : 0 < β) :
    0 < chargePumpFlux β 0 := by
  rw [chargePumpFlux_closed]
  apply div_pos _ (z4Partition_pos β)
  have hexp : Real.exp (-β / 2) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  linarith

/-- **The boundary clause (H1).** At `β = 0` the weights are
uniform and the one-turn flux of the chosen label's population
is exactly `0`. This vanishing is the only transport statement
made at the boundary; nothing is asserted at `β < 0` here
beyond what the iff below records. -/
theorem chargePumpFlux_zero_at_zero : chargePumpFlux 0 0 = 0 := by
  rw [chargePumpFlux_closed]
  simp

/-- **The iff form.** The one-turn flux of the chosen label's
population is strictly positive if and only if `β > 0`: at
`β ≤ 0` the closed form's numerator `1 − exp (−β/2)` is
nonpositive while the partition sum stays positive, so the
flux is nonpositive. The seat hypothesis `β > 0` is therefore
exact, not a convenience. -/
theorem chargePumpFlux_pos_iff (β : ℝ) :
    0 < chargePumpFlux β 0 ↔ 0 < β := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    rw [chargePumpFlux_closed] at h
    have hexp : (1 : ℝ) ≤ Real.exp (-β / 2) :=
      Real.one_le_exp_iff.mpr (by linarith)
    have hnonpos : (1 - Real.exp (-β / 2)) / z4Partition β ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith)
        (z4Partition_pos β).le
    linarith
  · exact chargePumpFlux_pos_of_pos

/-- **H1 discharged in full (PUMP-1 headline).** The registered
Prop `chargePumpH1` holds: the one-turn flux identity and its
closed form at every `β`, strict positivity of the chosen
label's population flux at every `β > 0` (hypothesis never
dropped), and the vanishing at `β = 0`. Tier T1. NO CLAIM;
dials 0/4. -/
theorem chargePumpH1_proved : chargePumpH1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro β
    exact ⟨chargePump_flux_eq β,
      by rw [chargePump_flux_eq β, chargePump_weight_sub_closed]⟩
  · intro β hβ
    rw [chargePump_flux_eq β]
    have h := chargePumpFlux_pos_of_pos hβ
    rwa [chargePumpFlux_zero_eq β] at h
  · rw [chargePump_flux_eq]
    have h := chargePumpFlux_zero_at_zero
    rwa [chargePumpFlux_zero_eq] at h

end ThetLogos
