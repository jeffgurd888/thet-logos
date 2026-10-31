# PUMP-1 landing — the one-turn flux, proved with its closed form

Filed: 2026-10-31. Brick: PUMP-1 (M priced) of the PUMP line (spectral
density matrix charge pump). Module: `ThetLogos.ChargePumpPost` extended
(totals strict 14 / defs 12; delta +13 strict), build green, headlines on
exactly [propext, Classical.choice, Quot.sound] (`chargePumpH1_proved`,
`chargePumpFlux_pos_iff`, `chargePumpFlux_eq`).

**NO CLAIM** is made by this landing. Parts closed: 0 on every board. All
four dials stand at **0/4**. Claims-registry note: Card PUMP's verdict
brick is PUMP-2; no outcome class exists yet.

**Reporting fence (K-PUMP-4), on this dossier as on the module:** the
transported quantity is the population of a chosen rung label (sector
B = rungs {2,3} of the owned four-rung ladder). There is no owned charge
operator at this seat and none is asserted. The one-turn flux below is a
redistribution inside a closed 4-cycle; the net population change over a
full cycle is zero (that accounting is PUMP-2's brick). Stationarity and
conservation facts are cited as rails, not results: the state's own
modular flow does nothing (`gibbsWeight_stationary`); the drive is the
external `z4Shift` protocol. No EM field object exists in this line.

## What landed (FULL, no seams)

- **The registered headline is discharged:** `chargePumpH1_proved :
  chargePumpH1`, assembling:
  - the flux identity — one turn moves the B-population by exactly
    `z4Weight β 0 − z4Weight β 2` (the turned population of the label is
    the weights at rungs 3 and 0, read rung by rung from the registered
    definitions);
  - the closed form — that difference is
    `(1 − Real.exp (−β/2)) / z4Partition β`, numeral-for-numeral against
    the landed ladder normalization (energies 0 and 1/2 at rungs 0 and
    2; no factor slip);
  - positivity exactly at positive temperature.
- **The iff is proved:** `chargePumpFlux_pos_iff : 0 < chargePumpFlux
  β 0 ↔ 0 < β` — the β > 0 hypothesis is carried, never dropped; at
  β = 0 the flux is exactly 0 (`chargePumpFlux_zero_at_zero`), and for
  β ≤ 0 the numerator is nonpositive against the positive partition.
- **The general-j formula landed** (the pack's optional item, not a
  seam): `chargePumpFlux β j = z4Weight β j − z4Weight β (j + 2)` for
  all j : Fin 4 — PUMP-2's full-cycle accounting consumes it directly.

Coordinator's fence check: the separation phrase occurs zero times in
the module (grep-verified at landing).

## Backers since last landing

The backer roll is unchanged since the previous landing. Backers are named
in `BACKERS.md` exactly as each wishes to be named, only after Jeff
confirms a gift arrived; amounts only with the giver's permission.

Census after this landing: 8,604 strict / 8,682 attribute-inclusive /
295 modules (parent-verified from disk; README badge and body updated and
grep-verified in the committed blob).
