# FibonacciReturn — the golden angle balances π against home; it never brings it home

**Verdict: STANDS WHOLE (T1) — with the exact-return KILL proved in the
same module.** Compiled green 2026-10-21 (`lake build
ThetLogos.FibonacciReturn`, 3,124 jobs, 0 errors), parent-verified on
the exact shipped text: `.olean` present, strict recount 13,
placeholder census 0, axioms on the six checked headline theorems
standard only (`propext`, `Classical.choice`, `Quot.sound`).

Module: `lean/ThetLogos/FibonacciReturn.lean` — 13 strict
theorems/lemmas, 0 `@[simp]` declarations. Program totals move
**3,337 → 3,350 strict** (3,377 → 3,390 attribute-inclusive),
**118 → 119 counted modules**.

## Origin

Jeff's fragments (2026-10-20): "it seems like whatever reverses/or
balances π back to ground and so forth" + "Fibonacci" — then "build
and run the gauntlet." The pinned form: golden angle
α = 2πψ² = 2π/φ² (ψ = Mathlib's `Real.goldenConj`), step operator =
one rotation by α, step counts = Fibonacci numbers. Proved
symbolically (sympy, differences simplifying to literal 0) before the
Lean draft existed; the module is that mathematics, machine-checked.

## What is proved

- `fib_goldenConj_cycle_residual` — the cycle identity
  `F_{n+2}·ψ² − F_n = ψ^{n+2}`, exactly.
- `goldenReturnResidual_eq` — after `F_{n+2}` golden-angle steps, the
  signed residual from `F_n` whole turns is exactly
  **2πψ^{n+2}**.
- `goldenReturnResidual_ne_zero` — the residual is never 0.
- `goldenReturnResidual_succ` and
  `goldenReturnResidual_succ_mul_self_neg` — each stage's residual is
  ψ times the previous, and consecutive residuals multiply to a
  negative number: **the sign alternates at every stage** — the
  approach balances across ground, overshooting alternately.
- `tendsto_goldenReturnResidual` — the residual tends to 0. The
  balance closes in the limit.
- `abs_goldenReturnResidual`, `abs_goldenReturnResidual_lt_two_pi` —
  the absolute residual is `2π·φ^{-(n+2)}`, always less than one full
  turn.
- **THE KILL, in-module:** `fib_mul_goldenAngle_ne_fib_mul_two_pi` —
  `F_{n+2}` golden-angle steps never equal `F_n` whole turns, for any
  `n`; and `goldenReturnResidual_ne_int_mul_two_pi` — the residual is
  never an integer number of whole turns either. **Exact finite
  return is FALSE for every n.** Read as "Fibonacci brings π home,"
  the originating sentence is killed; read as "Fibonacci balances π
  against home," it is a theorem. Both readings are settled by the
  same file.
- Phase form (via `FluxTwist.phaseOf`): `phaseOf_fib_mul_goldenAngle`
  — the phase after `F_{n+2}` steps is the phase of the residual;
  `tendsto_phaseOf_fib_mul_goldenAngle` — it tends to 1;
  `phaseOf_fib_mul_goldenAngle_ne_one` — it is never 1.

## Verification record

- Drafted 2026-10-20 under an UNVERIFIED header; blocked behind the
  Ghys stage-2 build under the one-heavy-build rule; compiled
  2026-10-21 after Jeff's skip order freed the machine and the
  WindingRing landing completed. First build: 4 errors, all API-level;
  repaired; green at 3,124 jobs. Header flipped to VERIFIED only
  after the parent re-ran the targeted build on the exact shipped
  text (green, 3,124/3,124).
- Five repairs, in the open, none touching a statement:
  `Nat.fib_add_two` (argument implicit in pinned Mathlib),
  `pow_lt_one₀` (renamed lemma), `one_mul` (identity orientation),
  a `funext` bridge in the tendsto proof, and one header
  token-hygiene rewording by the drafting agent.
- Axiom audit (`#print axioms`): the residual identity, the residual
  formula, the tendsto, both exact-return kills, and the phase-form
  kill each depend on exactly
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.

## Fences (on the module's face)

- One scalar phase plane. Not a 4D dynamics theorem, not a physical
  mechanism, not a mass law.
- **Not a resurrection of the φ-tower:** the standing kill
  (2026-09-29) on φ-power scaling of physical masses is untouched.
  Fibonacci enters only as an index sequence for step counts in an
  exact identity.
- The symbolic (sympy) arctan-splitting bridge for π/4 noted during
  the gauntlet was NOT attempted in Lean and is not claimed here.
