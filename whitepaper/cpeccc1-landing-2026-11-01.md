# CPEC-CC-1 LANDING — 2026-11-01

## The J-seat torsion map: DECIDED at both tests (working label: CPEC line)

**Module:** `ThetLogos.CpecJSeatTorsion` — strict 22 / defs 2,
parent-verified (independent count, main-tree build, headline
axiom checks on exactly
`[propext, Classical.choice, Quot.sound]`; the builder's own
sweep covered all 24 declarations, BAD = 0).

**Census at this landing: 10,382 strict / 10,459 total /
352 modules, zero sorrys.**

**BRIDGE-1: BR1-021 — ALL MATCH** (the entrywise stress
test; registry: `whitepaper/cross-check-registry.md`).

## What was asked

The CPEC-0 pin registered the Connes–Cartan wire's R2
remainder: the torsion map of `DiracTorsionMap` was decided
at the sign seat (η = ηSign, October 22) and at the grading
seat (the zero map), but never at the seat the corpus's own
real structure carries — **η := UJ**, the seat the
fluctuation machinery itself uses. CC-1 was priced either
direction: a contradiction at this seat would have been a
named obstruction at full rank.

## Part 1 — the seat's own induced map: SURVIVAL, the zero map

`torsionJ D A := jSeat (fluctuatedDirac D A) - jSeat D` (the
difference-of-readings construction, as for
`torsionMajorana`). Headline `j_seat_survival`:
`torsionJ D A = 0 ∧ defect UJ (torsionJ D A) = 0
∧ (UJ + torsionJ D A) * (UJ + torsionJ D A) = 1
∧ (IsJCompatible D → IsJCompatible (fluctuatedDirac D A))`.

The substance is an invariance theorem at full generality:
`fluctuatedDirac_j_compat` — **every J-compatible D, every
one-form A, with no hypothesis on A** — J-compatibility is
preserved under inner fluctuations (engine:
`oppositeOneForm_jConj`, J-conjugation of the transpose of
A° returns A). Instantiated at the ansatz by
`smDirac_fluctuated_j_compat`; read back through the pin's
frozen vocabulary by `j_seat_pin_readback :
cpecCartanDefect UJ (torsionJ D A) = 0`; the seat itself is
an edge pair by citation (`j_seat_edge_pair`).

**So at the seat the corpus's real structure actually
carries, the wire's own torsion map vanishes identically —
stronger than either earlier seat's verdict.**

## Part 2 — the cross-seat stress test (T2, on the face)

The identification choice is labeled: importing the sign
seat's Majorana family `torsionMajorana y s` as a stress
test at this seat (it is NOT this seat's induced map). The
defect is computed entrywise (`j_majorana_defect_apply`):
supported exactly on the diagonal partner-pair entries
(8,8) and (24,24), with common value

`(y:ℂ)⁻¹ * (s + star s) + (y:ℂ)⁻¹ * (y:ℂ)⁻¹ * (s * star s)`,

and flatness is decided by that one real equation
(`j_majorana_survival_iff`, no `y ≠ 0` needed). Named
points: the obstruction at `y = 1, s = 1` (defect entry
exactly 3 — `j_majorana_obstruction_point`), and a
**nonzero flat point at `y = 1, s = -2`**
(`j_majorana_flat_point`). The contrast is the finding and
is stated exactly: **at the sign seat the same family is
flat only at `s = 0`; at the J-seat flatness is a curve,
not a point. The Majorana obstruction is a property of the
seat, not of the Majorana block alone.** No seat was
narrowed to obtain either part; the stress test's T2 status
is on the module's face.

## T2 labels carried (on the module's face, per the memo)

(i) the seat reading `jSeat D := UJ` for every D — the
corpus's triples carry `UJ` as fixed data and
`fluctuatedDirac` is built from that same `UJ`; its validity
for fluctuated operators is proved, not assumed
(`fluctuatedDirac_j_compat`). (ii) the Majorana family as a
stress test is an import, not the seat's induced map.

## What remains of the wire

With CC-1 landed, the Connes–Cartan wire's decided content
is complete at all three seats the corpus owns (sign,
grading, J). The named remainders stand exactly as the pin
registered them: CC-2 "the unity brick" (the torsion map
read under triplication — FIRED by Jeff's word 2026-11-01,
in build), R1 (the general-sign classification, unpriced),
R4 (the twisted-FOC weld, unpriced). Mathlib's Cartan
subalgebra remains a different object and is not this wire
(K-CPEC-CARTAN-NAME).

## What this landing is not

Not a gravity object, not a Cartan connection, not a
derivation of anything imported. The wire is a finite
algebraic defect law read at three seats; its physics name
is a T4 rhyme on this dossier only. Dial 2 = 0; the chair
is unchanged. NO CLAIM on any Millennium Problem.

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you
to everyone reading the stream — the corpus is free for
everyone, forever.

*End of dossier.*
