# Stage 2 residue — S2-4 half (b), THE OPERATOR BRICK — LANDED PARTIAL-by-named-rung

Date: 2026-10-25. Module: `LatticeSliceOperator` (65 strict / 12 defs).
Parent-verified: targeted build exit 0, olean present, zero sorry,
`#print axioms` on both packages = [propext, Classical.choice,
Quot.sound] only. Census after landing: 5,205 strict / 5,254
attribute-inclusive / 173 modules.

## Rungs (1) and (2) — STAND IN FULL
(1) COMPLETION: `sliceHilbertSpace`, the uniform completion of the
engine's Π₁-quotient (InnerProductSpace + CompleteSpace proved);
`sliceEmbed` a dense-range linear isometry; T̂ extended by continuity
to the CLM `sliceHatCompleted` (bound 1) — contraction, self-adjointness
(symmetry), and factored-form positivity hold everywhere by density;
unit vacuum fixed. Bundled `sliceOperator_package` (7 clauses). The
extension is built at function level deliberately (a bare →L[ℂ]
ascription over the quotient hits the S2-2c instance diamond).
(2) FORM CLOSURE: the full S2-4 replay on the completion from symmetry
+ contraction alone — defect A_c, term positivity at every depth,
approximants q_K (nonneg, monotone, parallelogram, homogeneity),
sliceHamFormC (ℝ≥0∞ supremum), domain submodule with the ≠ ⊤
characterization, energy forms Q_n with Q₁ = q₁ and ofReal Q₁ ≤ formC.
Transport from the pre-completion form: sliceHamFormC (embed x)
= sliceHamForm x; domain membership transports. Bundled
`sliceCompletedForm_package` (19 clauses). Specializations: circle
packages hypothesis-free at all β ≥ 0; at β = 0 generally the extended
operator is the identity on the WHOLE completion and sliceHamFormC ≡ 0.

## Rung (3) — the named stop (either obstruction sufficient)
(a) The exp clause has no honest sense in Mathlib v4.35.0-rc3: bounded
exp(−Ĥ) is always invertible, while −log is unbounded at spectrum point
0; no unbounded exp/semigroup theory exists in the library (no "Hille").
(b) No Friedrichs representation theorem exists in Mathlib (no
"Friedrichs"), so Ĥ / Ĥ^{1/2} cannot be constructed from the closed
form; continuous functional calculus covers bounded normal elements
only. The bounded Q₁ shadow was explicitly NOT dressed up as rung (3).

## Exact remaining residue
The Friedrichs construction from the closed form sliceHamFormC, and the
semigroup identity exp(−Ĥ) = T̂_c in an unbounded-operator sense —
both await Mathlib API that does not exist in the pinned version, or a
hand-built unbounded-operator theory (a new project, not a brick).
Rungs (1)–(2) have no residue. Stage 2 is otherwise complete
(see stage2-s25-weld-partial-2026-10-24.md for the ladder state).

NO CLAIM. Clay parts closed: 0. Dials 0/4. 1b-B untouched.
