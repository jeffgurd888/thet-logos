# SEP-1 landing — the static imbalance, computed and proved

Filed: 2026-10-31. Brick: SEP-1 (M priced) of the SEP line (a thermal
state's measured sector imbalance, and the driven step that changes it —
the line's honest working label; Jeff's coinage names the line). Module:
`ThetLogos.ChargeSeparationPost` extended (totals strict 16 / defs 8;
delta +10 strict), build green, headlines on exactly
[propext, Classical.choice, Quot.sound] (`chargeSeparationS1_holds`,
`chargeSeparation_static_value`, `chargeSeparation_static_tanh`).

**NO CLAIM** is made by this landing. Parts closed: 0 on every board. All
four dials stand at **0/4**. Claims-registry note: Card SEP's verdict
brick is SEP-3; no outcome class exists yet. Fences carried: the
imbalance is a MEASURED expectation of the registered diagonal
observable `Qsep` on a thermal state; no charge operator is owned or
asserted beyond `Qsep` itself; no EM field object exists in this line;
the theorem is not a mechanism claim and borrows nothing from the
composite line (K-Q7CR-3 fired on a different object; no cross-claims in
either direction).

## What landed (FULL, no seams)

`chargeSeparationS1_holds : chargeSeparationS1` — SEP-0's registered
static target, discharged in full, the value COMPUTED from the landed
ladder weights (K-SEP-1: nothing re-entered), as named steps:

- `chargeSeparation_expectationIdentity_proved` — the registered
  identity ⟨Qsep⟩_w = 2·popB w − 1, proved;
- `chargeSeparation_partition_factor` — the partition factors:
  z4Partition β = (1 + exp(−β/4))·(1 + exp(−β/2));
- `chargeSeparation_popB_gibbs` — the population read:
  popB (z4Weight β) = exp(−β/2)/(1 + exp(−β/2)), the (1 + exp(−β/4))
  factor cancelling exactly;
- **`chargeSeparation_static_value`:**
  ⟨Qsep⟩_{ρ(β)} = (exp(−β/2) − 1)/(exp(−β/2) + 1);
- **`chargeSeparation_static_tanh`:** the same value = −tanh(β/4),
  bridged by exp algebra;
- **`chargeSeparation_static_eq_zero_iff`:** the value is 0 iff β = 0 —
  SEP-0's registration-time guard is now a corollary of the theorem;
- **`chargeSeparation_static_neg`:** strictly negative for β > 0.

## Backers since last landing

The backer roll is unchanged since the previous landing. Backers are named
in `BACKERS.md` exactly as each wishes to be named, only after Jeff
confirms a gift arrived; amounts only with the giver's permission.

Census after this landing: 8,614 strict / 8,692 attribute-inclusive /
295 modules (parent-verified from disk; README badge and body updated and
grep-verified in the committed blob).
