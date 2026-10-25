# FG-2c-1 LANDED FULL — the resolvent family R_λ for all λ > 0

**Date:** 2026-10-25 · **Status: T1** (parent-verified: forced
rebuild exit 0 on the shipped text; 0 sorry; axioms exactly
[propext, Classical.choice, Quot.sound] on the package and all
checked clauses). **Module:** `lean/ThetLogos/LatticeSliceResolvent.lean`
— 63 strict, 17 defs.

## What stands

- **Transport:** the J_λ form (FG-2b's form + λ·inner product) is a
  full inner product on its domain for every λ > 0, with squared-norm
  dominations both ways (constants max(1,λ), max(1,λ⁻¹)) and a
  `UniformEquiv` to the J_1 domain — the gate's one new lemma.
- **Riesz at general λ:** `sliceResolventCLM : H' →L[ℂ] H'` with
  ‖R_λ‖ ≤ λ⁻¹ and the weak resolvent equation.
- **Domain independence, as set equality:**
  `sliceResolvent_range_eq : range R_λ = sliceHamOperatorDomain`
  for every λ > 0; operator form `Ĥ(R_λ f) = f − λ•R_λ f`;
  Ĥ + λ surjective.
- **λ = 1 consistency as equality:** `R_1 =
  sliceFriedrichsResolventLin` (FG-2b's operator, on all inputs).
- **Vacuum:** `R_λ Ω = λ⁻¹ • Ω`; pairing positivity; β = 0 gives
  R_λ = λ⁻¹·id; circle package hypothesis-free.

**Not in this brick (flagged by the builder, not rounded up):** the
gate's Hille–Yosida contraction bound ‖(λR_λ)^k‖ ≤ 1 — an S-sized
input folded into FG-2c-3's commission as its brick 0.
**Resolvent identity:** out of scope per the gate, not attempted.
**NO CLAIM; dials 0/4.**
