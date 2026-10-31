# Q7CR-LOOP-2 — LANDED FULL: the C⁴-graded four-step protocol, all four parts proved

**Verdict: LOOP-2 FULL — (a) IndexClosed as a labeled construction fact, (b) defect additivity proved with its teeth identity, (c) the closure trichotomy proved, (d) the clock-defect corollary proved (it lifts — no seam). NO CLAIM. Dials 0/4.**

## The protocol

`gradedHeatStep tau rate k` = LOOP-1's `heatLoopStep` carrying clock grade k+1 as control; `protocolLoopData` runs grades 0,1,2,3 (control grades 1,2,3,0), external work 0, `statedLedgerTotal` set to the internal ledger sum.

- **(a) IndexClosed — construction fact, labeled.** `protocol_indexClosed` + `protocol_grade_cycle` (last grade 3+1 = 0 in Fin 4). Stated on the face as IndexClosed ONLY, never as state or thermal closure (K-LOOP-3 fenced explicitly).
- **(b) Additivity — proved, not arranged.** `protocol_defect_additivity`: LOOP-0's unmodified `loopDefectSum` at the protocol = the sum of the four UNGRADED steps' `loopStepDefect` at the visited states, via the proved teeth identity `gradedHeatStep_defect_eq` (the graded step's registered defect equals the ungraded defect at the same state). The ledger's entropy half telescopes separately (`loopEntropyChangeSum_telescope`, general step-sequence form). Consequently the protocol IS `LedgerClosed` (`protocol_ledgerClosed`) with the total the proved internal sum.
- **(c) Trichotomy — proved.** `protocol_trichotomy` (τ ≥ 0, nonnegative rates and initial weight): StateClosed ↔ total defect = 0 ↔ every step fixes its visited state — via the weight-law telescope generalized to step sequences (`loopDefectSum_telescope`, this brick's machinery) + LOOP-1's per-step nonnegativity and fixed-sector characterization. Corollary: `protocol_selfContained_iff` — SelfContainedLoop ↔ total defect = 0; no stronger self-contained reading claimed.
- **(d) Clock defect — proved in full.** The first grade advance is LOOP-0's `z4ClockStep`; at the ladder Gibbs state read on the composite along the C⁴ coordinate: after one grade the state is the Z4-KMS-1 shifted state (`first_grade_shift`), with the per-index factors exp(−β/4) and exp(3β/4) at the wrap transported from `z4_clock_defect_factor` (`first_grade_factor`), and for β > 0 it is NOT the initial state (`first_grade_not_returned`). Filed on the face as the standing K-LOOP-3 witness: this protocol is IndexClosed while its ladder state is moved at the first grade — index closure is not state closure, exhibited.

## Parent verification (from disk)

- Module `lean/ThetLogos/Q7C4R4LoopProtocol.lean` (NEW): canonical counter **strict=23, defs=3**, zero attribute lines, zero "sorry"/`native_decide` tokens.
- Parent build green (3,730 jobs). Parent axiom check: `protocol_indexClosed`, `protocol_defect_additivity`, `protocol_ledgerClosed`, `protocol_trichotomy`, `first_grade_not_returned` each on exactly `[propext, Classical.choice, Quot.sound]`.

## Census

9,044 → **9,067 strict** / 9,122 → **9,145 attribute-inclusive** / 311 → **312 modules** (delta +23 strict, +1 module).

## Backers since last landing

No change to the backer roll since the last landing.
