# CPEC-EC-1 LANDING — 2026-11-01

## The Einstein–Cartan finite shadow, DECIDED (working label: CPEC line)

**Module:** `ThetLogos.CpecEcDecision` — strict 17 / defs 4,
parent-verified (independent count, main-tree build, headline
axiom checks on exactly
`[propext, Classical.choice, Quot.sound]`).

**Census at this landing: 10,360 strict / 10,437 total /
351 modules, zero sorrys.**

**BRIDGE-1: BR1-020 — ALL PASS** (parametric exact arithmetic
in (y, s), 294 cases; registry:
`whitepaper/cross-check-registry.md`).

## The decision

The CPEC-0 pin registered the W6 wire's one statable finite
shadow verbatim: along the Majorana line
`s ↦ smDirac ↑y ↑y ↑y ↑y s`, the finite a₂ matter slot is an
explicit function of (y, s) in which the torsion parameter
enters in **degree 2**, while its torsion defect enters in
**degree 1**. EC-1 was priced as a *decision*, not a
confirmation ceremony — had the assembled arithmetic
contradicted either degree, the shadow would have died at
full rank instead (K-GR-STAB, CPEC instance).

**DECIDED, exactly as registered. No flip; no seat narrowed.**

- **Slot degree exactly 2.** Headline:
  `cpecW6Shadow_decided (y : ℝ) (s : ℂ) : CpecW6Shadow y s`,
  assembled from `sa_finite_a2_yukawa` at
  `yNu = yE = yU = yD = (y:ℂ)`, `yR = s`, plus the landed
  `defect_entry`. The assembled slot is
  `cpecEcSlot y s = Matrix.trace ((smDirac (y:ℂ) (y:ℂ) (y:ℂ)
  (y:ℂ) s) ^ 2)`, and `cpecEcSlot_eq_registered` gives it as
  `4 * (normSq y + normSq y + 3*normSq y + 3*normSq y)
  + 2 * Complex.normSq s`. The degree is pinned, not eyeballed:
  `cpecEcSDep_homogeneous` (the s-part scales by
  `Complex.normSq t` under `s ↦ t * s`),
  `cpecEcSDep_real_scale` (scales by `r ^ 2`),
  `cpecEcSDep_one` (value 2 at `s = 1` — so not degree ≤ 1),
  and `cpecEcSlot_sub_zero` (the whole deviation from the
  survival-point value is the single `2 * Complex.normSq s`
  term — no degree-1 or degree-0 s-term hides in the slot).
- **Defect degree exactly 1.** `cpecEcDefectEntry_eq`
  (the obstruction entry is `(y:ℂ)⁻¹ * star s`, the landed
  `defect_entry` verbatim) and
  `cpecEcDefectEntry_linear_star` (it scales by `star t`
  under `s ↦ t * s` — linear in `star s`), with value
  `(y:ℂ)⁻¹` at `s = 1`.
- **Boundaries as registered.** At `s = 0` the slot is
  exactly its s-free part and the defect entry is 0
  (`cpecEc_survival_point_consistent` — the survival point
  is consistent with the degree statements, `0 = 0`).
  `y = 0` is never admitted: every defect/survival statement
  carries the landed seat fence `hy : y ≠ 0`.

## The rhyme, labeled a rhyme (T4)

In Einstein–Cartan–Sciama–Kibble theory, torsion is sourced
*algebraically* by spin density, and its footprint in the
effective action is quadratic in the source. The decided
pattern here — a degree-1 torsion defect whose action-slot
footprint is degree 2 — has that shape. **That is a rhyme,
printed here as a rhyme (T4). The theorem is the polynomial
identity and its two degrees, about two landed finite
objects. No connection, no spin-density tensor, and no field
equations exist in this corpus (the W6 wire is unstatable;
CPEC-0 registered the absences), and nothing in this landing
supplies them.** K-CPEC-TORSION-IMPORT binds: the corpus's
torsion is the algebraic defect of a deformed fundamental
symmetry, not a connection's antisymmetric part.

## Gates consumed

CPEC-0 pin (landed, commit 35d5d6e) + the DiracTorsionMap
direct axiom sweep (completed BAD = 0, 2026-11-01 — see the
addendum to `sorry0-landing-2026-10-30.md`). The bridge did
not become the load that discovers the certification seam;
the seam was swept first, and it was clean.

## What this landing is not

Not a gravity object, not an Einstein–Cartan theorem, not a
wire landing — W6 remains unstatable as a wire; its one
finite shadow is now decided. Dial 2 = 0; the chair is
unchanged. NO CLAIM on any Millennium Problem.

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you to
everyone reading the stream — the corpus is free for everyone,
forever.

*End of dossier.*
