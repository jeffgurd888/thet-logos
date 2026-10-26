# FG-2c-4 IDENTIFY — Landing Dossier

**Date:** 2026-10-26
**Module:** `ThetLogos/LatticeSliceIdentify.lean` (75 strict, 10 defs; 3,591 lines)
**Verdict: PARTIAL-A — with the split REVERSED from the pre-registration's guess.** The headline identification is proved in full; of the spectral correspondence's two clauses, the **Jensen clause is discharged** and the **gap clause** is the named open remainder. T1 at the seats stated. Stage 2 completeness at fixed volume only. NO CLAIM; dials 0/4; Items 3 (uniform estimates) and 4 (continuum) untouched.

## The headline (FULL)

`sliceYosidaS_one_eq`: at every seat (2 ≤ N, continuous ρ, even N, under the one carried hypothesis `SliceHPosOne`), the Yosida semigroup of the Friedrichs Hamiltonian, evaluated at t = 1, **is** the completed transfer operator restricted to the physical carrier:

S(1) = T̂_c as continuous linear maps on H′ = sliceFormClosure = (ker T̂_c)ᗮ.

The stepper and the river were kept separate in every text until this brick, per the commissioning ruling; this theorem is the identification itself, proved, and it is the only place the equality is asserted. The route ran through the shared functional calculus — the duality check in the proof's own shape: the resolvent was identified as a cfc restriction at every λ > 0 (Step A, via the Riesz specification and a defect bound), the Yosida approximants were identified as cfc restrictions of a clamped symbol (Step B), and the symbols converge uniformly on [0,1] with an explicit rate (Step C) — operator-norm convergence on the calculus side, strong convergence on the semigroup side, termwise agreement, uniqueness of limits.

## The Jensen clause (DISCHARGED)

`sliceJensen` (general seat) and `sliceBattery_jensen` (circle seat): for every unit vector u in the domain of Ĥ,

exp(−E u) ≤ ⟪u, T̂_c u⟫.re,

proved elementarily — no spectral measure. The moments a_j = ⟪y, Â_c^j y⟫.re satisfy a_{j+1} ≥ a_j·a₁ (positivity of ((1−μ) − a₁)((1−μ)^j − a₁^j) in the cfc pairing), hence a_j ≥ a₁^j; the logarithmic series for the form closes the case a₁ < 1, and a₁ = 1 is excluded by harmonic divergence against the finiteness of E u. The correspondence's vacuum-orthogonality hypothesis turned out **not to be needed**.

## The gap clause (OPEN — named remainder)

The clause ⟪x, T̂_c x⟫.re ≤ 1 − δ is **not** proved. The corpus's gap bound (`GapBoundU1`) controls the spectrum of the **pre-completion** transfer operator; no transport of that bound to the completed operator T̂_c's pairings exists in the record, and this brick does not supply one. The remainder is named: **the completion-transport problem** (pre-completion spectrum → completed pairings). It is a new entry in the gap queue, not a consequence claimed here.

**Battery consequence:** `SliceSpectralCorrespondence`'s Jensen conjunct is now a theorem; its gap conjunct is the sole open clause. The battery's "smallest stored quantum" statement (T4) continues to take the correspondence as a hypothesis, but any future discharge needs only the gap conjunct.

## Verification

Builder: targeted build exit 0 (3,692 jobs); axioms of `sliceYosidaS_one_eq`, `sliceJensen`, `sliceBattery_jensen` each exactly [propext, Classical.choice, Quot.sound]; grep-clean of placeholders and `native_decide`. Parent: recount on the shipped text (strict 75, defs 10, zero same-line attribute declarations), headline statements read on the face, main-tree targeted build green, axiom spot-check repeated. Header fences intact: placement label (Stage 2 completeness, fixed volume), NO CLAIM, dials 0/4.

## Census

Public census moves with this landing: strict 5,707 → **5,782**, attribute-inclusive 5,774 → **5,849**, counted modules 186 → **187**. Placeholder census unchanged at 6.

## Backers since last landing

The roll stands as it stood in the Solid Body dossier — no gifts recorded in this interval. Every gift, when it comes, is inscribed here by name as its giver wishes, or as "a gift of bench time" when they prefer no amount and no name. The record is the reciprocity: this landing exists in the open because the lab is free for everyone, forever.
