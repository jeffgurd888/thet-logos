# Q7CR-LOOP-0 — LANDED (registration): the three closure Props, separate, with StateClosed failable

**Verdict: registration landed as scoped. `LoopData` + `IndexClosed` / `StateClosed` / `LedgerClosed` as THREE SEPARATE definitions + `SelfContainedLoop`. No theorems attempted (registration brick, A0/T0 pattern). NO CLAIM. Dials 0/4.**

## The registered forms

- States: Q7CR-5's weight states (`compIndex → ℝ`); `IsGibbsInitial` registers `dynGibbs β` as the distinguished thermal family. A `LoopStep` carries its parameter (time / grade : Fin 4 / coupling), a stated state map, per-mode rate data for the defect term, and named defect/entropy factor fields over `LoopFactor` (q7 | c4 | r4). `LoopData` = step list + initial state + stated protocol endpoints (`initialParam`/`finalParam`) + `statedLedgerTotal` + the explicit `externalWork` field.
- `IndexClosed := finalParam = initialParam` — protocol only, no state mentioned. `StateClosed := loopFinalState L = L.initialState`, where `applyLoopSteps` is the literal recursive composition of the stated maps — NOT a return-map/projection, so StateClosed can genuinely FAIL for stated step-data (the K-LOOP-1 vacuity fence is printed on the face). `LedgerClosed := loopLedgerSum L = L.statedLedgerTotal`, the sum built over visited states from the `traceDefect` closed form per step plus T-ENT `entropyW` changes, every summand carried by its step's named factor fields. `SelfContainedLoop := StateClosed ∧ LedgerClosed ∧ externalWork = 0` — IndexClosed explicitly NOT a conjunct, per the memo.
- The Z₄ clock shift is registered on the face as the IndexClosed-only miniature (`z4ClockLoopData`, `Z4ClockMiniatureReading`), its defect cited from Z4-KMS-1 (`z4_clock_defect_factor`, `z4_clock_not_invariant`), not re-proved; its thermal content as a loop is stated as zero; no StateClosed/LedgerClosed/SelfContainedLoop statement is registered about it.
- Standing fences on the face: the three notions never conflated (K-LOOP-3); the strong reading (exact state closure + positive production + no ledger outlet) DEAD ON ARRIVAL per obstruction O1 — no brick attempts it; "forces" only in quotation as Jeff's; no β(x), no flow-generated arrow.

## Parent verification (from disk)

- Module `lean/ThetLogos/Q7C4R4LoopPost.lean` (NEW): canonical counter **strict=0, defs=16** (zero theorems by design), zero attribute lines, zero "sorry"/`native_decide` tokens. Parent build green (3,728 jobs). No axiom check (no theorems).

## Census

9,025 strict / 9,103 attribute-inclusive (both unchanged — registration defs only) / 309 → **310 modules**.

## Backers since last landing

No change to the backer roll since the last landing.
