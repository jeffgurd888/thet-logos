# BSD3-2R ASSEMBLY — LANDING (2026-11-02): the E3 line, complete

**Brick:** BSD3-2R assembly — the B1 assembly over the corrected
seam. **The BSD3-2R line is COMPLETE** (pin → sweep → assembly).
**Decision of record:** Jeff, 2026-11-01 22:33 EST — "1 re-pin."
**Module:** `ThetLogos/BSDRefinedE3Assembly.lean` (new; mirrors
`ThetLogos/BSDRefinedE1Assembly.lean` statement-for-statement with
E3's numbers: Tamagawa value 5 at the seam, torsion card 5 from
the sweep's discharge).
**Count:** strict 6 / defs 0.
**Build:** GREEN on build 1; parent re-build green.
**Axioms:** all six theorems exactly `propext`, `Classical.choice`,
`Quot.sound`.

## What is proved

Under the registered seams (rank zero; sha a positive natural; the
L-value within 1e-5 of 0.2538418609; the period Ω in
[1.2692092, 1.2692094]; the Tamagawa value 5):

- `refinedRHS_E3_tam_five` — with the regulator slot 1 and the
  torsion slot 5, the BSD right-hand side is `sha * Ω / 5`.
- `E3_sha_eq_one_of_tolerance` — tolerance forces sha = 1: any
  sha ≥ 2 gives RHS ≥ 2 · 1.2692092 / 5 = 0.50768368, above the
  L-value's ceiling 0.2538518609.
- `E3_tolerance_of_sha_eq_one` — sha = 1 gives
  Ω/5 ∈ [0.25384184, 0.25384188], within the 5e-3 tolerance of the
  L-value window.
- `E3_tolerance_iff_sha_eq_one` — the tolerance conjunct of the
  corrected pin statement holds **if and only if sha = 1**.
- `BSDRefinedE3R_assembly` — under the seams AND the corrected
  Nagell–Lutz criterion: the torsion card is discharged in-tree
  (via the sweep's `e3TorsionCard_of_nagellLutzR`) and the
  tolerance condition is equivalent to sha = 1.
- `BSDRefinedE3R_conclusion_of_tolerance` — if the pin statement's
  tolerance holds, its named conclusion sha = 1 follows.

**Shape fence (on the module's face, B2-6/E1 discipline):** the
bare pin statement `BSDRefinedE3R` is NOT asserted as a theorem —
as a ∀-proposition its first conjunct is false for sha ≥ 2. The
iff is the provable core, and it is proved. **K-BSD3-2R-a does not
fire**: the sha identification is exactly the licensed B1 content —
under the stated seams and the criterion hypothesis, the analytic
side pins sha = 1, and nothing beyond that licence is claimed
anywhere in this line.

## The line, whole

- **Pin** (`BSDRefinedE3Repin`, strict 0/defs 3): the corrected
  statement, new entry under the relabeling rule; the dead pin
  stands unedited with K-BSD3-2c on the record.
- **Sweep** (`BSDTorsionE3Sweep`, strict 18/defs 4): E3's torsion
  classified in-tree; |tors| = 5 derived from the corrected
  criterion; K-BSD3-2R-c did not fire.
- **Assembly** (this module, strict 6): the B1 iff over the
  corrected seam.

What the line establishes, at its exact tier: the BSD rank-0
refined statement for 11.a1 now exists in a CORRECTED form whose
Nagell–Lutz seam is true of the curve, whose torsion cardinality is
derived rather than imported, and whose Sha content is the proved
iff above — conditional, as the whole B1 architecture is, on the
named seams and the criterion hypothesis. It is bookkeeping-grade
verification of the statement's internal arithmetic, NOT a proof of
any case of the Birch–Swinnerton-Dyer conjecture.

**NO CLAIM. Parts of the Clay BSD statement closed by this line:
0. Dials 0/4.**

**Census after landing: 12,641 strict / 13,153 total / 445 counted
modules** (increment +6 strict / +0 defs / +1 module). Run totals
for the successor run (Orders 1 + 2): +49 strict / +20 defs /
+6 modules over the 12,592 / 13,087 / 439 close it inherited.
