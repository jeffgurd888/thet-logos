# Stage 2, Brick S2-5 — THE WELD — LANDED PARTIAL-by-named-class

Date: 2026-10-24. Module: `LatticeSliceWeld` (18 strict / 4 defs).
Parent-verified: targeted build exit 0, olean present, zero sorry,
`#print axioms sliceWeld_package` = [propext, Classical.choice,
Quot.sound] only. Census after landing: 5,140 strict / 5,189
attribute-inclusive / 172 modules.

## Verdict shape
PARTIAL exactly in kill K-S2-5's pre-registered class: the form-level
weld, discrepancy named. No kill fired at the descent step; nothing
silently shrunk.

## The structural finding
`sliceState` itself does NOT descend to the Π₁-quotient — the engine
norm is the transfer-form norm Re ⟪s a, T(s a)⟫, not the L² self-pairing.
What descends is the STEPPED state a ↦ transferOp (sliceState a): on the
radical, Π₂(a,a) = ‖T(s a)‖² (S2-2a's stepped reading) and
Π₂(a,a).re ≤ Π₁(a,a).re = 0 (S2-2b's domination), so its kernel contains
the radical. The descended weld map `sliceWeldMap` (Submodule.liftQ)
then delivers, at general (G, ρ), every real β, under exactly
SliceHPosOne (+ 0 < d where the landed bricks need it):

- Intertwining, exact: W(T̂x) = transferOp (W x) for all classes, plus
  the CLM form (`sliceWeldCLM`).
- Form identity: ⟪W x, W y⟫ = ⟪x, T̂ y⟫ — W is an isometry for the
  T̂-twisted form onto its image, and a contraction ‖W x‖ ≤ ‖x‖.
- Depth-one identity on classes: ⟪[a],[b]⟫ = ⟪s a, W[b]⟫
  = osForm (sliceObs a) (sliceObs b).
- Vacuum: W Ω = osVacuum.
- Hamiltonian clause (via S2-4's interface): sliceEnergyForm 1 x
  = ‖x‖² − ‖W x‖² — Q₁ IS the weld's norm defect — and
  ENNReal.ofReal (‖x‖² − ‖W x‖²) ≤ sliceHamForm x.

## The named discrepancy (K-S2-5)
‖[a]‖² = (⟪s a, W[a]⟫).re versus ‖s a‖² = (⟪s a, s a⟫).re — a proved
identity pair. A concrete numerical separation is NOT exhibited and is
not available at bare general (G, ρ) (it needs a seat with a nonconstant
observable — e.g. available at U(1), not claimed here). The PARTIAL
rests on the seat-independent identity pair, as the kill priced.

## Residue — the S2-4 operator brick (L), exact
(i) Completion of the engine space first; form identities persist by
continuity. (ii) Self-adjoint Ĥ ≥ 0 with ‖Ĥ^{1/2}x‖² = sliceHamForm x on
the completed domain. (iii) exp(−Ĥ) = T̂. The T̂^{1/2} polar-factor route
is noted as the L brick's own design question. Consumption interface
for the Stage 2 closing summary: sliceWeld_package + this dossier +
the S2-4 dossier's residue.

## Stage 2 state at this landing
S2-0 gate STANDS (as revised) · S2-1 PARTIAL-by-kill (𝔸⁺ dead at the
plane; P-0 verbatim on 𝔸_slice) · S2-2 COMPLETE · S2-3 STANDS IN FULL
(engine hypothesis-free at U(1)) · S2-4 form STANDS · S2-5 weld PARTIAL-
by-named-class. The only Stage 2 residue is the L operator brick.
NO CLAIM; Clay parts closed: 0; dials 0/4; 1b-B label untouched.
