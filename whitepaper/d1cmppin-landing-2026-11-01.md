# D1-CMP PIN LANDING DOSSIER — 2026-11-01

**Item:** D1-CMP (Dial-1 lane) — statement pin, per the
compensator scoping
(`dial1-compensator-scoping-2026-11-01.md`). The T1
confirmation entry for K-ESC-6's scoping-level firing. A NEW
ENTRY under the relabeling rule; D1-A, D1-A′, D1-C3 stand as
landed beside it.

**Status: PIN LANDED.** The pin asserts none of the three
confirmation facts; the confirmation module follows.

**Artifact:** `lean/ThetLogos/DialOneDoubleFlipPin.lean` —
strict 4, defs 4 (in the pack's band). Verified by the
coordinator in the main tree (build green, 3136 jobs);
headlines on exactly `[propext, Classical.choice, Quot.sound]`.

## What is pinned

`piDouble a := pi1 a + Matrix.single s8 s8 (star a.u1 − a.u1)
+ Matrix.single s9 s9 (a.u1 − star a.u1)` — π₁ with the ν_R
seat flipped and the e_R seat un-conjugated (π₁ already
conjugates e_R: `pi1_entry_eR`). Two face-noted vocabulary
facts: the tree had no `s9` (introduced following the `s8`
pattern), and non-proportionality is stated **directly** in
`DialOneForcing`'s conclusion shape at piDouble along its
unimodular direction (3, −1) — because the landed
`DialOneForcing` quantifies over the D1-A′ strengthened set
rather than taking π as an argument, so the pin's form is the
honest one (the pack's pre-named fallback).

The three confirmation Props, stated and NOT proved:
`C3PiDoubleCheck` (C3 piDouble — expected true, the +2αi and
−2αi contributions cancel), `BasePiDoubleCheck`
(DialOneBase piDouble — expected true at proof-shaped level;
the first-order transport over the (1↔9) Dirac pairing is the
bulk), `NonProportionalCheck` (no κ makes piDouble's lifted
eigenvalues match `exp(κ·t·(common matrix entry)·I)` at every
sector — its sector vector is (−3,−3,1,1,−6,0,4,−2), the
ν_R ↔ e_R swap of the table).

Kills on the face: **K-ESC-6** (fires at T1 when all three
land — base + C3 forcing FALSE in Lean, permanently);
**K-CMP-1** (the base transport fails at a named clause —
piDouble is then not a counterexample and the scoping firing
is overturned); **K-CMP-2** (the swap is proportional after
all); **K-CMP-3** (C3 piDouble fails at the gate). The
scoping's lesson is on the face: the base set's grip on
particle seats is per-Dirac-pair local.

**Dial 1: 0 — on every outcome.** This entry confirms a kill
or overturns one; it is not a forcing attempt. NO CLAIM.

**Census after landing: 11,390 strict / 11,638 total / 392 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
