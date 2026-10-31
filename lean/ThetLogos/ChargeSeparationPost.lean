import Mathlib.Tactic
import ThetLogos.ChargePumpPost

namespace ThetLogos

/-!
# ThetLogos.ChargeSeparationPost — SEP-0: the separation-operator registration

**Status: REGISTRATION ONLY — definitions and stated `Prop`s, plus the
proved face checks at the end of the module. NO CLAIM. No Millennium
statement, no ladder rung, no dial (dials stay 0/4).**

Commission: Jeff, 2026-10-31. Governing memo:
`routeb-general-scratch/scoping-separation-operator-2026-10-31.md`
(§0 the reduction, §1 the candidate ruling, §2 headline Props S1–S4,
§3 the seat ruling and honesty clause, §4 the SEP-0 row, §5 the
composite dependency, §6 kills K-SEP-1..4 with K-PUMP-4/5 carried
over). Working label: SEP. This module is a sibling extension of the
PUMP line: it CONSUMES PUMP-0's registered definitions (`χB`, `QB`,
`popB`, `chargePumpSectorB`) and does not redefine any of them.

## §0 — the reduction, stated before anything else

The line SURVIVED REDUCED at scoping. Jeff's coinage names the line —
"thermal density matrix charge separation operator" — and the honest
working label, which governs every statement below, is: **"a thermal
state's measured sector imbalance, and the driven step that changes
it."** No operator exists that does what the coinage literally says:
nothing acting on a thermal density matrix separates charge by its
own action. What registers here is the three-part reduced object of
memo §0: an imbalance observable (an instrument, §1(a)); the static
fact that the thermal state is already separated against the seat
grading, by an exact closed form (S1); and a drive in operator form —
the external clock — whose action changes the imbalance by exactly
`2 ×` the PUMP-1 flux per turn (S2).

## §3 — the honesty clause (part of the pin, not a caveat beneath it)

`Qsep` is READ, not applied: it separates nothing. It is diagonal in
the same basis as every state at this seat, it commutes with the
Gibbs state, and conjugating by it changes nothing. The clock does
every bit of the moving; `β` sets the state's imbalance and the
flux's size — `β` moves nothing by itself. The grading at this seat
is CHOSEN (PUMP-0 pin data: `B = {2, 3}` against `A = {0, 1}`), the
separated quantity is population of a chosen rung label, and NO
owned charge operator exists at this seat. The identification of
the rung label with electric charge is Jeff's T5 reading, asserted
nowhere in this line (K-SEP-3).

## Carried-over PUMP fences, still armed in this line

- K-PUMP-4: no net-per-cycle transfer claims, and no heat-as-mover
  language — the net imbalance change over the full clock cycle is
  exactly `0` (S4(iii)); the mover is the clock protocol, not heat.
- K-PUMP-5: no electromagnetic field object exists, is constructed,
  or is implied anywhere in this line.

## Pre-registered kills, named on the face (memo §6)

- K-SEP-1 (net-charge creation): any form claiming a separation
  operator here creates net charge or separates "from nothing" dies
  on sight. Total population is trace, preserved by construction;
  every change below is redistribution against the grading.
- K-SEP-2 (state-alone action): any form in which the thermal
  density matrix separates by itself — its own flow, functions of
  itself, an operator read off the state — is dead on arrival
  (`gibbsWeight_stationary`, landed, fixes the state under its own
  modular flow; S4(ii) is this kill stated as a target theorem).
- K-SEP-3 (label-vs-charge, reporting fence): see the honesty clause
  above; dropping the grading-relative fence, or the `β ≠ 0` /
  drive-externality hypotheses, from any headline fires this kill
  on the reporting.
- K-SEP-4 (vacuity): an "operator" whose separation vanishes on
  every state, or a headline true by definition-chasing alone, is
  bookkeeping. Guard, discharged at registration below in BOTH
  directions: a nonzero instance (S1's value at `β > 0` is a
  specific nonzero closed form, and the diagonal entries of `Qsep`
  are proved to be `(-1, -1, +1, +1)`), and genuine failing cases —
  at `β = 0` a clock turn changes the imbalance by exactly `0`
  (proved below), and a partition-preserving drive changes the
  imbalance by exactly `0` on every state (proved below for the
  within-sector swap).

## The composite form is DEFERRED, not duplicated (memo §5)

The composite-scale form of the ask — an operator against a DERIVED
charge grading on the composite — is Q7CR-3's registered venue,
gated on Q7CR-2. This line supplies Q7CR-3 nothing, consumes
nothing from it, and does not wait for it. Until Q7CR-3 lands a
grading there is nothing on the composite for a separation operator
to be relative to.

## Rope

NO CLAIM; dials 0/4, with reasons on the face: S1's closed form is
an exact property of a CHOSEN ladder's Gibbs weights (the energies
`k / 4` are chosen inputs) — not a derived measured number, not a
gravity object, not a continuum limit, not an externally confirmed
prediction. Jeff's vacuum-box chain remains T5 regardless of this
line's outcome. The drive is external and the cycle returns the
state exactly, so the line is not an energy source (battery
passivity, `sliceBattery_extracted_nonpos`, cited by name in the
PUMP line, stands over this line as well).
-/

/-! ## §1(a). The imbalance observable, over PUMP-0's registered data -/

/-- The sector-imbalance observable: `Qsep := Matrix.diagonal (fun k
=> 2 * χB k - 1)`, the diagonal operator with entries
`(-1, -1, +1, +1)` — sector `B` counts `+1`, sector `A` counts `-1`.
Defined over PUMP-0's registered `χB`; in PUMP-0 vocabulary it is
`2 • QB - 1` (proved below as `chargeSeparation_Qsep_eq`). An
instrument: it MEASURES separation, it causes none — see the
honesty clause on the module's face. -/
def Qsep : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal (fun k => 2 * χB k - 1)

/-- The diagonal expectation of `Qsep` on a diagonal state with
weights `w`: `⟨Qsep⟩_w := ∑ k, w k * (2 * χB k - 1)` — the
trace-form evaluation for diagonal states, per memo §1(a). For the
Gibbs state this is the density-matrix expectation in the honest
sense: by the landed `z4_gibbsState_eq`, `ρ(β)` is `Matrix.diagonal`
of the weights `z4Weight β`. -/
noncomputable def chargeSeparationExpectation (w : Fin 4 → ℝ) : ℝ :=
  ∑ k : Fin 4, w k * (2 * χB k - 1)

/-- The expectation-to-imbalance identity, STATED for diagonal
states (registered target; memo §1(a)): for weights summing to `1`,
`⟨Qsep⟩_w = popB w - popA w = 2 * popB w - 1` — the imbalance is
the difference of the sector populations against PUMP-0's chosen
grading, with `popB` consumed from PUMP-0 as registered. -/
def chargeSeparationExpectationIdentity : Prop :=
  ∀ w : Fin 4 → ℝ, (∑ k : Fin 4, w k = 1) →
    chargeSeparationExpectation w = 2 * popB w - 1

/-! ## §2. Headline Props S1–S4, stated verbatim in substance

Statements only — no theorem is attempted in this brick beyond the
face checks proved at the end, and nothing here asserts that any
registered Prop holds. -/

/-- **(S1) The static separation of the thermal state (memo §2 —
the line's headline).** For every `β`:
`⟨Qsep⟩_{ρ(β)} = (Real.exp (-β/2) - 1) / (Real.exp (-β/2) + 1)`
(the `exp` form is the registered one; the equivalent
`-Real.tanh (β/4)` form is a corollary for later bricks, not
load-bearing here). Teeth: the value is `0 ↔ β = 0`, and for
`β > 0` it is strictly negative — a specific nonzero closed form,
not a tautology (the K-SEP-4 nonzero-instance guard, stated).
Note what S1 says and does not say: the thermal state IS separated
(measured, exact, iff-gated) and NOTHING separated it — no operator
appears in S1. Target of SEP-1. -/
def chargeSeparationS1 : Prop :=
  (∀ β : ℝ, chargeSeparationExpectation (z4Weight β)
      = (Real.exp (-β / 2) - 1) / (Real.exp (-β / 2) + 1)) ∧
  (∀ β : ℝ, chargeSeparationExpectation (z4Weight β) = 0 ↔ β = 0) ∧
  (∀ β : ℝ, 0 < β → chargeSeparationExpectation (z4Weight β) < 0)

/-- **(S2) The driven step's action on the imbalance (memo §2).**
One clock turn changes the imbalance by exactly `2 ×` PUMP-1's H1
flux: for every `β`,
`⟨Qsep⟩_{shifted} - ⟨Qsep⟩ = 2 * (z4Weight β 0 - z4Weight β 2)`,
and — the consistency clause in the same statement, so a
convention mismatch between the SEP and PUMP lines cannot hide —
this equals `2 ×` PUMP-1's H1 closed form
`(1 - Real.exp (-β/2)) / z4Partition β`. The operator form of this
statement (conjugation by the `z4Shift` permutation unitary acting
as the landed shifted weights on diagonal states) is SEP-2's
brick, gated on PUMP-1; the expectation identity registered here
is the quantity that brick must match, factor of 2 included.
Target of SEP-2. -/
def chargeSeparationS2 : Prop :=
  (∀ β : ℝ,
    chargeSeparationExpectation (z4ShiftedWeight β)
        - chargeSeparationExpectation (z4Weight β)
      = 2 * (z4Weight β 0 - z4Weight β 2)) ∧
  (∀ β : ℝ,
    chargeSeparationExpectation (z4ShiftedWeight β)
        - chargeSeparationExpectation (z4Weight β)
      = 2 * ((1 - Real.exp (-β / 2)) / z4Partition β))

/-- **(S3) The separation iff (memo §2).** For a bijective drive
`π` of `Fin 4` against the Gibbs family: `π` changes `ρ(β)`'s
imbalance for SOME `β` iff `π` does not preserve the partition
`{0,1} | {2,3}` (PUMP-0's `chargePumpSectorB`, consumed as
registered). And for the clock specifically, for every `β`: the
turned imbalance differs from the imbalance iff `β ≠ 0`. Content:
separation by a drive occurs iff the drive fails to preserve the
grading's sectors AND the state is sector-uneven — the two factors
are independent and each is necessary; the failing cases (a
partition-preserving `π`; the clock at `β = 0`) are inside the
statement, per K-SEP-4 — a draft stating the clock clause without
`β ≠ 0` asserts a falsehood at `β = 0`. Target of SEP-3. -/
def chargeSeparationS3 : Prop :=
  (∀ π : Fin 4 → Fin 4, Function.Bijective π →
    ((∃ β : ℝ, chargeSeparationExpectation ((z4Weight β) ∘ π)
        ≠ chargeSeparationExpectation (z4Weight β))
      ↔ ¬ (∀ k : Fin 4, k ∈ chargePumpSectorB ↔ π k ∈ chargePumpSectorB))) ∧
  (∀ β : ℝ, chargeSeparationExpectation (z4ShiftedWeight β)
      ≠ chargeSeparationExpectation (z4Weight β) ↔ β ≠ 0)

/-- **(S4) The no-go corollaries (memo §2 — registered content at
the same rank as the positive headlines, not fine print).**
(i) Diagonal drives separate nothing: for any diagonal unitary
given by phases `d` (every `‖d k‖ = 1`), conjugation
of the named state `chargePumpState β` by `Matrix.diagonal d`
returns the state exactly. (ii) Under its own modular flow the
named state is fixed — the normalized form of the landed
`gibbsWeight_stationary` — so its imbalance is constant: the
state-alone separation operator does not exist at this seat
(K-SEP-2 as a theorem). (iii) Conservation and cycle return at
operator level: every bijective drive preserves total population
(`∑ k, (z4Weight β ∘ π) k = 1`); four clock turns return the
imbalance exactly; and the sum over the cycle of the per-turn
imbalance changes (read on PUMP-0's registered turned weights,
`chargePumpTurnedWeight`, consumed not redefined) is exactly `0`
— all separation at this seat is driven, temporary within the
cycle, and redistributive (K-SEP-1, K-PUMP-4). Target of SEP-3. -/
def chargeSeparationS4 : Prop :=
  (∀ (d : Fin 4 → ℂ) (β : ℝ), (∀ k : Fin 4, ‖d k‖ = 1) →
    Matrix.diagonal d * chargePumpState β
        * Matrix.conjTranspose (Matrix.diagonal d)
      = chargePumpState β) ∧
  (∀ (β s : ℝ),
    NormedSpace.exp ((Complex.I * (s : ℂ)) • z4Generator)
        * chargePumpState β
        * NormedSpace.exp ((-(Complex.I * (s : ℂ))) • z4Generator)
      = chargePumpState β) ∧
  ((∀ (π : Fin 4 → Fin 4), Function.Bijective π → ∀ β : ℝ,
      ∑ k : Fin 4, (z4Weight β ∘ π) k = 1) ∧
    (∀ β : ℝ, chargeSeparationExpectation
        (fun k => z4Weight β (z4Shift (z4Shift (z4Shift (z4Shift k)))))
      = chargeSeparationExpectation (z4Weight β)) ∧
    (∀ β : ℝ, ∑ j : Fin 4,
        (chargeSeparationExpectation (chargePumpTurnedWeight β (j + 1))
          - chargeSeparationExpectation (chargePumpTurnedWeight β j)) = 0))

/-! ## Face guards, discharged at registration (K-SEP-4)

Both directions exhibited on the face, as proved items: the seat's
separation is not vacuous (the observable's entries are the
specific numerals `(-1, -1, +1, +1)`, and `Qsep = 2 • QB - 1` over
PUMP-0's `QB`), and the drive clause has genuine failing cases —
at `β = 0` the clock changes the imbalance by exactly `0`, and the
partition-preserving within-sector swap below changes the
imbalance by exactly `0` on every state, the Gibbs family at
`β > 0` included (its corollary). -/

/-- The within-sector swap: the partition-preserving drive
exhibited for the failing-case guard. It swaps the two rungs
inside sector `A` and the two rungs inside sector `B`, so it
preserves PUMP-0's chosen partition by construction. -/
def chargeSeparationSectorSwap (k : Fin 4) : Fin 4 :=
  if k = 0 then 1 else if k = 1 then 0 else if k = 2 then 3 else 2

/-- `Qsep = 2 • QB - 1` as matrices, over PUMP-0's registered `QB`:
the registered matrix identity of memo §1(a), discharged here
rather than left as a target. Tier T1. -/
theorem chargeSeparation_Qsep_eq : Qsep = 2 • QB - 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    have hL : Qsep i i = 2 * χB i - 1 := Matrix.diagonal_apply_eq _ i
    have hQ : QB i i = χB i := Matrix.diagonal_apply_eq _ i
    rw [hL]
    simp only [Matrix.sub_apply, Matrix.smul_apply, hQ,
      Matrix.one_apply_eq]
    rw [nsmul_eq_mul]
    norm_num
  · have hL : Qsep i j = 0 := Matrix.diagonal_apply_ne _ h
    have hQ : QB i j = 0 := Matrix.diagonal_apply_ne _ h
    rw [hL]
    simp only [Matrix.sub_apply, Matrix.smul_apply, hQ,
      Matrix.one_apply_ne h]
    norm_num

/-- **Face check, nonzero direction (K-SEP-4 guard).** The
diagonal entries of `Qsep` are the specific numerals
`(-1, -1, +1, +1)`: sector `A` counts `-1`, sector `B` counts
`+1`, against PUMP-0's `χB`. Decidable numeral facts at the seat.
Tier T1. -/
theorem chargeSeparation_diagonal_entries :
    Qsep 0 0 = -1 ∧ Qsep 1 1 = -1 ∧ Qsep 2 2 = 1 ∧ Qsep 3 3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [Qsep, Matrix.diagonal_apply_eq, χB, chargePumpSectorB]

/-- **Face check, failing case at `β = 0` (K-SEP-4 guard).** At
`β = 0` the weights are uniform (`1/4` at every rung, by direct
computation from `z4Partition 0 = 4`), so a clock turn changes
the imbalance by exactly `0` — even the crossing drive separates
nothing on the sector-even state. Tier T1. -/
theorem chargeSeparation_face_check_beta_zero :
    chargeSeparationExpectation (z4ShiftedWeight 0)
      - chargeSeparationExpectation (z4Weight 0) = 0 := by
  have hw : ∀ k : Fin 4, z4Weight 0 k = 1 / 4 := by
    intro k
    have hp : z4Partition 0 = 4 := by
      simp [z4Partition, z4Energy]
    rw [z4Weight, hp]
    simp [z4Energy]
  have hs : ∀ k : Fin 4, z4ShiftedWeight 0 k = 1 / 4 := by
    intro k
    rw [z4ShiftedWeight, hw]
  have e1 : chargeSeparationExpectation (z4Weight 0) = 0 := by
    simp [chargeSeparationExpectation, Fin.sum_univ_four, hw, χB,
      chargePumpSectorB]
    norm_num
  have e2 : chargeSeparationExpectation (z4ShiftedWeight 0) = 0 := by
    simp [chargeSeparationExpectation, Fin.sum_univ_four, hs, χB,
      chargePumpSectorB]
    norm_num
  rw [e2, e1, sub_self]

/-- The within-sector swap preserves the sector label: `χB` read
at the swapped rung equals `χB` at the rung, for every rung.
Decidable numeral facts at the seat. Tier T1. -/
theorem chargeSeparation_sectorSwap_chiB :
    ∀ k : Fin 4, χB (chargeSeparationSectorSwap k) = χB k := by
  intro k
  fin_cases k <;> simp [chargeSeparationSectorSwap, χB, chargePumpSectorB]

/-- The within-sector swap changes no state's imbalance: for every
weight function `w`, the expectation of the swapped weights equals
the expectation of `w` — the swap only exchanges equal-labelled
rungs inside each sector. Tier T1. -/
theorem chargeSeparation_sectorSwap_expectation :
    ∀ w : Fin 4 → ℝ,
      chargeSeparationExpectation (w ∘ chargeSeparationSectorSwap)
        = chargeSeparationExpectation w := by
  intro w
  have e0 : chargeSeparationSectorSwap 0 = 1 := by
    simp [chargeSeparationSectorSwap]
  have e1 : chargeSeparationSectorSwap 1 = 0 := by
    simp [chargeSeparationSectorSwap]
  have e2 : chargeSeparationSectorSwap 2 = 3 := by
    simp [chargeSeparationSectorSwap]
  have e3 : chargeSeparationSectorSwap 3 = 2 := by
    simp [chargeSeparationSectorSwap]
  simp only [chargeSeparationExpectation, Fin.sum_univ_four,
    Function.comp_apply, e0, e1, e2, e3]
  have c0 : χB 0 = 0 := by simp [χB, chargePumpSectorB]
  have c1 : χB 1 = 0 := by simp [χB, chargePumpSectorB]
  have c2 : χB 2 = 1 := by simp [χB, chargePumpSectorB]
  have c3 : χB 3 = 1 := by simp [χB, chargePumpSectorB]
  rw [c0, c1, c2, c3]
  ring

/-- **Face check, failing case for a partition-preserving drive
(K-SEP-4 guard).** At every `β` — `β > 0` included — the
within-sector swap applied to the Gibbs weights changes the
imbalance by exactly `0`: a drive that preserves the grading's
sectors separates nothing, however uneven the state is. The
two-factor content of S3, exhibited at registration. Tier T1. -/
theorem chargeSeparation_face_check_partition_preserving :
    ∀ β : ℝ, chargeSeparationExpectation
        ((z4Weight β) ∘ chargeSeparationSectorSwap)
        - chargeSeparationExpectation (z4Weight β) = 0 := by
  intro β
  rw [chargeSeparation_sectorSwap_expectation, sub_self]

end ThetLogos
