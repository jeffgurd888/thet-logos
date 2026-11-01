# SHELF-13 LANDING DOSSIER — 2026-11-01

**Item:** SHELF-13 (self-adjointness criteria), per the SHELF
rotation and the coordinator pack (`pack-shelf-13.md`).

**Status: PARTIAL at the pre-named seam** — the general
Kato–Rellich form (genuinely unbounded perturbation, relative
bound 0 < a < 1) is not proved; everything the pin supports
landed, including more than the pack expected at the unbounded
seat.

**Artifact:** `lean/ThetLogos/SelfAdjointCriteria.lean` —
strict 19, defs 1. Verified by the coordinator in the main tree
(build green, 3635 jobs); all 15 headlines on exactly
`[propext, Classical.choice, Quot.sound]`.

## Probe correction (on the record)

The pack expected the pin's unbounded-operator API to be absent.
It is PRESENT: `LinearPMap` graph adjoints with
`IsFormalAdjoint`, `adjoint_isFormalAdjoint`,
`isSelfAdjoint_def` et al. What the pin lacks is the resolvent
machinery for general self-adjoint `LinearPMap`s (resolvent
bounds / Neumann inversion) that the classical unbounded
Kato–Rellich proof runs on. "Rellich" and deficiency-index
vocabulary: zero occurrences in the pin — this brick is a fill,
not a strike.

## What landed

- **Bounded seat:** `katoRellich_bounded_seat` — self-adjoint plus
  bounded symmetric perturbation stays self-adjoint, with the
  relative-bound hypothesis a < 1 recorded in seat form (flagged
  on the face as unused at this seat, where boundedness makes it
  automatic).
- **Unbounded seat (headline):** `katoRellich_bounded_perturbation`
  — for a self-adjoint `LinearPMap` A and a bounded self-adjoint
  B, the sum on D(A) (`pmapAddBounded`) is self-adjoint in the
  graph dialect, at relative bound a = 0
  (`‖Bx‖ ≤ 0·‖Ax‖ + ‖B‖·‖x‖`), via the adjoint-domain pairing
  argument (`pmapAddBounded_adjoint_apply`, `pmapAddBounded_adjoint_le`).
- **Finite/everywhere-defined seats:** symmetric ⟹ self-adjoint
  by a pure graph argument; deficiency vanishing in finite form
  (`ker (T ∓ i) = ⊥` over ℂ; `range (T − i) = ⊤`).
- **Read-backs (two):** the bridge Laplacian's self-adjointness
  re-derived in the graph dialect through the finite-seat route;
  SHELF-2's Friedrichs operator plus any bounded self-adjoint
  perturbation is self-adjoint, through the unbounded-seat route.

## The seam, and the fenced neighbor

General Kato–Rellich (unbounded B, 0 < a < 1) NOT proved — the
missing pin input (resolvent estimates for self-adjoint
`LinearPMap`s) is named on the module's face. SHELF-2's Seam A
(domain equality `D(S) = D(t)`) was noted and NOT touched: this
brick's domain equalities are for the perturbed operator only and
neither use nor imply it; Seam A remains open exactly as SHELF-2
left it.

## Fences

NO CLAIM — no Millennium problem is claimed solved or advanced.
Dials 0/4.

**Census after landing: 10,906 strict / 11,013 total / 369 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
