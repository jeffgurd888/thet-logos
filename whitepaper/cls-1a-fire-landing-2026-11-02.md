# CLS-1a-FIRE LANDING DOSSIER — K-CLS-1a FIRED (base form) — 2026-11-02

**Item:** CLS-1a-FIRE (Lane 1) — BR1-029's priced follow-on:
fire K-CLS-1a by construction, via the conjugation route.

## VERDICT: K-CLS-1a FIRED (T1) — DialOneBase does NOT imply within-sign diagonality of the lift

**Artifact:** `lean/ThetLogos/DialOneConjugationCounterexample.lean`
— strict 66, defs 8 (M band, as priced). Verified by the
coordinator in the main tree (build green); seven checked
theorems, both headlines included, on exactly
`[propext, Classical.choice, Quot.sound]`.

**The witness:** `conjU` — the probe's rational orthogonal
(12-seat u-channel support; seat pairs 2↔28, 4↔26, 10↔20,
12↔18; diagonal 3/5, off-diagonal ±4/5), with unitarity
proved both sides. `piU a := conjU * pi1 a * conjUᵀ`.

**Transport, complete — no clause resisted, nothing
widened:** (a) `[conjU, gammaF] = 0` → clause 7; (b)
`piOp conjU = conjUᵀ` and the full intertwining transport
→ clauses 8, 9; (c) `[conjU, DF_oneGen Ynu Ye Yu Yd] = 0`
at **generic** Yukawa values, via the channel coefficient
form (no seated values) → clause 9; clauses 1–5 by sandwich
algebra; clause 6 by cancellation against `pi1_injective`;
clause 10 by determinant conjugation-invariance, π₁'s
(3,−1) verbatim. `dialOneBase_piU : DialOneBase piU`.

**The firing entry, as proved:** along (3,−1), the lifted
product's entry (2,28) is (12/25)·(e^{4ti} − e^{ti}); at
t = π/2 it equals **(12/25)(1 − i) ≠ 0**. Seats 2 and 28
are both γ = +1 with common weights 1 vs 4 (proved). The
second direction (−3,1) is covered by the same value at
−π/2.

**Headlines:** `k_cls_1a_fired` (the registered kill form)
and `not_forall_base_diagLift : ¬ ∀ π, DialOneBase π →
DiagLift π`. (`DiagLift` had no in-tree def; it is frozen
verbatim from the CLS-1a scoping §1.1 in-module, stated on
the face.)

**Consequences, at exact rank:**
- CLS-1's ExtractionLemma hypothesis material is now
  **known-sharp on its diagonality half**: within-sign
  diagonality is genuinely additional input, not a base
  consequence — proved by a base point that violates it.
  CLS-1's PARTIAL stands exactly as landed.
- **The correction rides with it:** the firing pair is
  (2,28), NOT the scoping's named candidate (8,9) — seats
  8, 9 are channel-separated and unreachable by conjugation
  (BR1-029). CLS-1a-X's cross-sign theorem is untouched.
- **Fences:** the strengthened form is NOT addressed —
  colProj does not commute with conjU, and piU's family
  status is claimed neither way. Grade W and the W′
  decision item are untouched. **Dial 1 = 0** — a
  counterexample to a forcing hope, not a derivation of
  anything measured.

**BRIDGE-1:** BR1-029 (the probe, registry entry appended
with this landing; memo committed alongside) — the probe's
exact-arithmetic witness is now a Lean theorem; probe and
proof agree on the entry value (12/25)(1 − i), the weights
(1 vs 4), and the transport conditions.

## Fences

NO CLAIM; all dials 0/4.

**Census after landing: 12,549 strict / 12,990 total / 433 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
