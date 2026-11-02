# DC-F1 — LANDING (2026-11-02): the ring and its helicity bookkeeping

**Line:** DUAL-CURRENT (working label; the public name is Jeff's to
coin). Charter: `~/workspace/your_files/dual-current-theory-charter-2026-11-01.md`.
**Decision of record:** Jeff, 2026-11-01 22:33 EST — "3 fire."
**Module:** `ThetLogos/DualCurrentRing.lean` (new).
**Count:** strict 6 / defs 3 (+1 private helper lemma, uncounted by
the house rule).
**Build:** GREEN on build 1; parent re-build green.
**Axioms:** all six theorems depend on exactly `propext`,
`Classical.choice`, `Quot.sound`.

> Named for Edward Leedskalnin (1887–1951), builder of Coral Castle,
> whose *Magnetic Current* (1945) posed the counter-streaming picture
> this theory makes checkable. Named for the question he asked, not
> for his answers — his answers keep their audited grades (see §6 of
> the charter).

## The model

Fields `j : ZMod n → ℚ` on the finite ring (`n ≥ 1`). Defs:
`dcEnergy j = ∑ i, (j i)^2`; `dcHelicity j = ∑ i, j i * (j (i+1) − j i)`
(the fully discrete D4 functional — no smoothness hypothesis, no
continuum object); `dcChurn jp jm = ∑ i, −(jp i * jm i)` (the
pointwise-opposition sum of the D2 channel split, which is
bookkeeping by declaration).

## Verdicts — all FULL

- `dcEnergy_nonneg` — energy is a sum of squares, `0 ≤ E`.
- `dcHelicity_eq_neg_half` — **the discrete helicity identity**:
  `H[j] = −(1/2) * ∑ i, (j (i+1) − j i)^2`, identically on every
  finite ring. (Pre-checked in exact rational arithmetic before the
  build: identity holds pointwise-in-sum for random fields, n = 2..5.)
- `dcHelicity_nonpos` — `H ≤ 0`: on the finite ring the helicity
  functional is a pure roughness cost; it never rewards variation.
- `dcHelicity_eq_zero_iff` — `H = 0 ↔ j` is constant: maximal
  smoothness is exactly the constant fields.
- `dcHelicity_abs_le` — `|H| ≤ 2 * E`: the roughness cost is bounded
  by the energy.
- `dcEnergy_add` — the net field's energy splits as channel energies
  minus twice the churn: `E[jp + jm] = E[jp] + E[jm] − 2 * churn`.

**K-DC-2 note (on the record):** `dcEnergy_add` is not a coupling
result and is not read as one. Churn ENTERS the net-energy identity
with a negative sign — pointwise opposition LOWERS net `∑ j²`. The
identity is bookkeeping about `∑ (jp + jm)²`; it seats no
interaction, no force, and no energy source (K-DC-3 stands).

## Fences carried on the module's face

K-DC-1 (no monopole reading — channels are bookkeeping), K-DC-2 (no
coupling claim), K-DC-3 (no energy surplus, ever), K-DC-4 (spin
currents / Berry connections / para-dia splits are T4 anchors in the
literature, never this line's results). **NO CLAIM. This line moves
no dial; dials 0/4.**

**Census after landing: 12,598 strict / 13,099 total / 441 counted
modules** (increment +6 strict / +3 defs / +1 module).
