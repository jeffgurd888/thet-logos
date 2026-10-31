# PUMP-3 landing — the drive characterization; the PUMP line's registered claims are complete

Filed: 2026-10-31. Brick: PUMP-3 (S–M priced) of the PUMP line.
Module: `ThetLogos.ChargePumpPost` extended (totals strict 29 / defs
12; delta +4 strict), append-only (128 insertions, 0 deletions), build
green, all four new theorems on exactly
[propext, Classical.choice, Quot.sound] (coordinator-verified:
`chargePumpH3_proved`, `chargePump_registered_claims_proved`,
`chargePump_popB_basis`, `chargePump_popB_basis_comp`).

**NO CLAIM** beyond the line's registered content is made by this
landing. Parts closed: 0 on every board. All four dials stand at **0/4**.
Card PUMP's verdict (FULL) landed at PUMP-2; this brick completes the
registered claim set and asserts no new outcome class. K-PUMP-4 fence
held throughout (population language; no operator, no field object).

## What landed

`chargePumpH3_proved : chargePumpH3` — the drive characterization,
proved natively in this module (ChargeSeparationPost imports this
module, so no SEP result is cited — no import cycle):

- (⇐) A partition-preserving bijection transports zero sector
  population for every weight vector (both B rungs land in B;
  injectivity fixes or swaps the pair; the population w 2 + w 3 is
  unchanged).
- (⇒) If every weight vector's population is transported unchanged,
  the drive preserves the partition: the basis weight concentrated at
  π k has its transported population detect exactly the membership of
  the preimage rung, forcing (k ∈ B) = (π k ∈ B) for every rung — both
  crossing directions by the same concentrated weight.

And the line's closing assembly:
`chargePump_registered_claims_proved : chargePumpH1 ∧ chargePumpH2 ∧
chargePumpH3` — a pure conjunction of the three landed `*_proved`
results. **The PUMP line is complete at its registered claims:** one
turn moves the label's population by (1 − exp(−β/2))/z4Partition β,
positive iff β > 0; the full cycle returns exactly, nets zero, crosses
one full unit gross, pays trace defect zero; and a bijective drive
transports nothing for all states iff it preserves the partition.

Coordinator's note: the builder's report used the phrase
"native_decide" for a Fin 4 index fact; the disk governs — the file
contains no such token (grep: 0 occurrences) and the axiom footprints
above are clean. The discrepancy is the report's wording, not the
module's content.

## Backers since last landing

The backer roll is unchanged since the previous landing. Backers are named
in `BACKERS.md` exactly as each wishes to be named, only after Jeff
confirms a gift arrived; amounts only with the giver's permission.

Census after this landing: 8,798 strict / 8,876 attribute-inclusive /
298 modules (parent-verified from disk; README badge and body updated and
grep-verified in the committed blob).
