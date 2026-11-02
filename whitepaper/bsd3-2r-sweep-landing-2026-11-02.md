# BSD3-2R SWEEP — LANDING (2026-11-02): E3's torsion, classified

**Brick:** BSD3-2R sweep — discharge of `E3TorsionCardSeam` from the
corrected criterion `NagellLutzCriterionE3R` (pin:
`ThetLogos/BSDRefinedE3Repin.lean`, dossier
`whitepaper/bsd3-2r-pin-landing-2026-11-02.md`; decision of record:
Jeff, 2026-11-01 22:33 EST — "1 re-pin").
**Module:** `ThetLogos/BSDTorsionE3Sweep.lean` (new).
**Count:** strict 18 / defs 4 (+1 instance, `E3.instIsElliptic`).
**Build:** GREEN at build 4; parent re-build green.
**Axioms:** every theorem in the module depends on exactly
`propext`, `Classical.choice`, `Quot.sound`.

## What is proved

For E3 = LMFDB 11.a1 (Δ = −11⁵; `E3_delta` by `norm_num`):

- **Enumeration** (`eq_of_sq_dvd_161051`, `e3_int_point_cases`): an
  integer `m` with `m² ∣ 161051` lies in `{±1, ±11, ±121}`; an
  integer point of E3 whose `y` satisfies the corrected
  Nagell–Lutz divisibility `(2y + 1)² ∣ 161051` has
  `y ∈ {−61, −6, −1, 0, 5, 60}` and its `x` in `−2..16` (bounds:
  the curve RHS is negative for `x ≤ −3` and exceeds every
  admissible `y² + y ≤ 3660` for `x ≥ 17`), and the point is one of
  exactly four: **(5, 5), (5, −6), (16, 60), (16, −61)**.
- **Group arithmetic** (frozen point defs `E3P55`, `E3P5m6`,
  `E3P1660`, `E3P16m61`; negation `E3_neg_P55 : -P55 = P5m6`,
  `E3_neg_P1660 : -P1660 = P16m61`): the ℤ-action computations
  `2•P55 = P16m61`, `2•P16m61 = P5m6`, `3•P55 = P1660`,
  `4•P55 = P5m6`, `5•P55 = 0` — (5, 5) has exact order 5, computed
  through Mathlib's affine addition formulas, every slope a ground
  rational.
- **Classification** (`E3_point_eq_of_torsion`): a rational point of
  E3 is torsion ⟺ it is `0`, `P55`, `P5m6`, `P1660`, or `P16m61`;
  with `e3_mem_torsion_iff` at the subgroup level.
- **The seam discharge** (`e3TorsionCard_of_nagellLutzR`):
  `NagellLutzCriterionE3R → E3TorsionCardSeam` — IF the corrected
  Nagell–Lutz criterion holds for E3, THEN
  `Nat.card (AddCommGroup.torsion E3.toAffine.Point) = 5`, the
  value 5 DERIVED from the in-tree enumeration and the order-5
  computation — not imported as data.

## K-BSD3-2R-c — DID NOT FIRE

The discharge consumed only `NagellLutzCriterionE3R` at its frozen
strength. No stronger form was needed; nothing was strengthened in
flight. What remains conditional is exactly what the pin's shape
says: the criterion itself is the hypothesis. (The criterion is the
classical Nagell–Lutz theorem specialized to E3; formalizing
Nagell–Lutz in general is not part of this line's registration —
the seam architecture is the predecessor board's B1 design, in
which the criterion enters as a named hypothesis at every curve.)

Pack slips (minor, none in a frozen statement): two Mathlib lemma
names carry the `Nat.` prefix differently than the pack's
line-cites (`Nat.dvd_prime_pow`, `Nat.pow_dvd_pow_iff_le_right`);
the enumeration closer runs `interval_cases xi <;> revert heq <;>
decide` over ℤ (the pack's `norm_num at heq` route errors in this
pin when `heq` closes first). All frozen statements elaborated
verbatim and were diff-checked.

**NO CLAIM. Parts of the Clay BSD statement closed by this landing:
0. Dials 0/4.**

**Census after landing: 12,635 strict / 13,147 total / 444 counted
modules** (increment +18 strict / +4 defs / +1 module).
