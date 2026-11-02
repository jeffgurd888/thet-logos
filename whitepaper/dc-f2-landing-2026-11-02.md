# DC-F2 — LANDING (2026-11-02): Leedskalnin configurations

**Line:** DUAL-CURRENT (working label). Charter:
`~/workspace/your_files/dual-current-theory-charter-2026-11-01.md`
(§2 D2, §3 F2, §5b).
**Decision of record:** Jeff, 2026-11-01 22:33 EST — "3 fire."
**Module:** `ThetLogos/DualCurrentLeedskalnin.lean` (new; imports the
landed `DualCurrentRing`, unmodified).
**Count:** strict 9 / defs 3.
**Build:** GREEN on build 2 (build 1 failed only on one rewrite in
`isLeedskalninConfig_iff`; fixed via component projections); parent
re-build green.
**Axioms:** headlines exactly `propext`, `Classical.choice`,
`Quot.sound`; structural theorems subsets thereof; no `sorryAx`.

> Named for Edward Leedskalnin (1887–1951), builder of Coral Castle,
> whose *Magnetic Current* (1945) posed the counter-streaming picture
> this theory makes checkable. Named for the question he asked, not
> for his answers — his answers keep their audited grades (see §6 of
> the charter).

## The seat

`IsLeedskalninConfig jp jm : Prop := ∀ i, jm i = -jp i` — the pure
counter-streaming state of charter §5b, named the **Leedskalnin
configuration**. `leedskalninConfig a = (a, -a)` is its canonical
parametrization.

## Verdicts — all FULL

- `leedskalninConfig_isLeedskalnin`, `leedskalninConfig_injective`,
  `isLeedskalninConfig_iff` — the configurations are exactly the
  pairs `(a, -a)`: the configuration space is parametrized by the
  single channel, with no extra freedom and no missing cases.
- `leedskalnin_net_eq_zero` — the net field of a Leedskalnin
  configuration is identically zero (D2 seated as a theorem).
- `leedskalnin_churn_eq_energy` — at a Leedskalnin configuration the
  churn EQUALS the channel energy: pointwise opposition is maximal
  relative to the channel. (Pre-checked exactly: churn(a, −a) =
  energy(a).)
- `dcProject` — the symmetrization `(jp, jm) ↦ ((jp − jm)/2,
  (jm − jp)/2)`: lands in the configurations
  (`dcProject_isLeedskalnin`), is idempotent
  (`dcProject_idempotent`), and its fixed points are EXACTLY the
  Leedskalnin configurations (`dcProject_eq_self_iff`).
  `dcProject_net_eq_zero` — the projection kills the net field.

**The F2(c) fence, on the record:** `dcProject_eq_self_iff` is the
finite content of Leedskalnin's "holding" picture and it is a
fixed-point statement about a DEFINITION. Nothing about energy
attaches to it: the projection is a relabeling of coordinates, not
a dynamics, and it stores, holds, and releases nothing. The
Perpetual Motion Holder stays where the audit put it — remanence
and the keeper effect. K-DC-3 stands; K-DC-1 stands (a configuration
of two bookkeeping channels is not a pair of monopole streams).

**NO CLAIM. This line moves no dial; dials 0/4.**

**Census after landing: 12,607 strict / 13,111 total / 442 counted
modules** (increment +9 strict / +3 defs / +1 module).
