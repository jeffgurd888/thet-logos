# PNP-1b LANDING DOSSIER — the P vs NP board statement — 2026-11-02

**Item:** PNP-1b (Millennium Lane 3) — the statement half
of PNP-1, against PNP-1a's frozen definitions.

## VERDICT: BOARD STATEMENT LANDED — both directions exhibited; the unfold is honestly not rfl

**Artifact:** `lean/ThetLogos/PvsNPStatement.lean` —
strict 3, defs 1. Verified by the coordinator in the main
tree (build green, first attempt); all three theorems on
exactly `[propext, Classical.choice, Quot.sound]`.
PNP-1a untouched.

`PvsNPBoardStatement : Prop := PeqNP` — adoption, the RH-1
pattern. The board↔PeqNP unfold is `Iff.rfl`.
**The two-directions theorem is NOT `Iff.rfl`** — set
equality does not unfold definitionally to the subset
conjunction — and the module says so on its face: it is
proved by the subset-antisymmetry step, inclusions read
off the equality. Both directions are thereby exhibited
separately, which was the point of the brick.

**The direction fence, as written on the face:**
- `P ⊆ NP` — the KNOWN inclusion, stated as T4 in the
  fence, **never as a house theorem** (textbook theory —
  the empty certificate; unproved in this corpus and not
  baked into anything).
- `NP ⊆ P` — the Clay question's direction (Cook: whether
  every NP language is in P; classical-open).
- `NPSubsetP` is fenced as exactly the one-way inclusion
  NP ⊆ P — a named weaker Prop: not the board statement,
  and the board statement is not it (`npSubsetP_iff_subset`
  landed as its definitional receipt).

**K-PNP-1 carried forward at its exact state:** Part A
PASS inherited (the defs are unchanged); Part B still
conditional on PNP-1c's D5 witness — the board statement
does not claim the K-test, and this dossier doesn't
either. PNP-1c is in flight.

## Fences

NO CLAIM; **parts of P vs NP closed: 0.** The board's
statement-grade rung: vocabulary (PNP-1a) + statement
(PNP-1b), mirroring RH-1 and NS-1a/b. Remaining on this
board: PNP-1c (the witness) and PNP-2 (the barrier map,
paper-grade by registration — formalizing a barrier
theorem is named UNPRICEABLE in the rotation scoping, and
a costume formalization is the failure the board's kill
discipline exists to catch).

**Census after landing: 12,562 strict / 13,044 total / 437 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
