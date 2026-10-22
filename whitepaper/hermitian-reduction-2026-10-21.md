# HermitianReduction — the general-Hermitian reduction (the shared remainder, discharged)

**Verdict: STANDS WHOLE (T1).** The named shared remainder of
three standing bricks — `ResonanceSpectrum`, `SpectralClock`,
`ThermalKernel`, each proved for a diagonal generator — is
discharged: for a general finite Hermitian generator `K` over `ℂ`,
the diagonal conclusions transport along Mathlib's spectral
decomposition `K = U * diagonal (eigenvalues) * star U`. Compiled
green 2026-10-21 (`lake build ThetLogos.HermitianReduction`,
3,583 jobs, 0 errors), parent-verified on the exact shipped text:
`.olean` present, strict recount 16, incompleteness census 0 on
comment-stripped source, axioms on the six checked headline
theorems standard only (`propext`, `Classical.choice`,
`Quot.sound`). Kill condition K1 (transport needs more than
conjugation of `exp`) did **not** trigger — the full transport
stands as drafted, no narrowing.

Module: `lean/ThetLogos/HermitianReduction.lean` — 16 strict
theorems/lemmas, 3 defs, 0 `@[simp]` declarations. Program totals
move **3,368 → 3,384 strict** (3,408 → 3,424
attribute-inclusive), **120 → 121 counted modules**.

## What is proved

- **Spectral form and spectrum.** `hermitian_spectral_form`
  unpacks `Matrix.IsHermitian.spectral_theorem` into plain matrix
  products; `hermitian_eigenvector` records each eigenvector-basis
  vector as an eigenvector with its eigenvalue;
  `hermitian_spectrum_real` records Mathlib's
  `spectrum_real_eq_range_eigenvalues` as the bridge: the eigenvalue
  function the transports speak about **is** `K`'s spectrum.
- **Conjugation calculus.** `exp_conj_star`:
  `exp (U * A * star U) = U * exp A * star U` (via
  `Matrix.exp_units_conj` at the explicit unit), plus the three
  associativity-collapse lemmas the transports compose with.
- **The kernel.** `heatKernelGen_eq_conj` — the brick's core:
  `exp (-tK) = U * diag (exp (-t * d i)) * star U` with
  `d = hK.eigenvalues`, via smul-through-conjugation and
  `Matrix.exp_diagonal`. `heatKernelGen_trace`: the trace schedule
  of `K` is the cast of `ThermalKernel`'s diagonal trace at the
  eigenvalue function. `hermitian_payoff_sum`: the summed payoff
  over positive modes is `∑ (eigenvalue)⁻¹`, `ThermalKernel`'s
  payoff stated at `K`'s spectrum. `heatKernelGen_add`: the
  semigroup law — proved directly (scalar split +
  `Matrix.exp_add_of_commute`), so it holds for **every** matrix;
  Hermiticity is not needed and the statement records none.
- **The clock, in the eigenbasis.** `genFlow` is the phase flow of
  `K`'s eigenvalue function conjugated by `U`;
  `genFlow_eigenbasis` pulls it back to `phaseFlow` exactly.
  `genFlow_stationary_iff` transports stationarity as an
  eigenbasis-entry statement. `genFlow_masterTick_apply` /
  `genFlow_masterTick_first`: at `masterTick (eigenvalues)` the
  widest eigenbasis coherence is negated, and at no earlier
  positive time — `SpectralClock`'s two theorems composed with the
  pullback identity.

## What does NOT transport (named remainders, on the header)

- **R1 — original-basis entries.** Flip, firstness, and
  stationarity hold for the entries of `star U * A * U` (the
  eigenbasis picture), not for entries of `A`. Nothing
  original-basis is claimed.
- **R2 — the jewel for non-diagonal ρ.** `e^{-K} = ρ` at `t = 1`
  transports only in diagonal form; `K = -ln ρ` for a non-diagonal
  state needs a matrix logarithm (functional calculus for `log`),
  untouched here. Only `exp` is transported.
- Not stated: the payoff integral of the full trace (zero modes
  pay at rate 1 forever, so it diverges — `ThermalKernel`'s
  filtered shape is inherited, and the reason is stated in the
  module); `ResonanceSpectrum` Part I (dephase/pinch fixed
  points) is basis-bound and not transported.

## Verification record and repairs (in the open)

Drafted and compiled 2026-10-21 (the draft's scoping discovery:
all three diagonal bricks are stated over eigenvalue *functions*,
never matrix exponentials — the brick is exactly the bridge).
Green at 3,583 jobs; header flipped only after the parent
re-ran the targeted build on the exact shipped text (3,583/3,583;
linter notes only). Repairs, none changing a statement's content:
(1) the exponential is spelled `NormedSpace.exp x` — this pin's
`NormedSpace.exp` takes no field argument, so the drafted
`NormedSpace.exp ℂ x` does not elaborate; the corpus's own
spelling (e.g. `FlowKernel`) is used, denotation unchanged, and
the repair touches the statement text of `exp_conj_star` and the
def `heatKernelGen` — flagged here as the one statement-adjacent
repair; (2) `hermitian_spectral_form` closes by the Mathlib term
after `Unitary.conjStarAlgAut_apply` (the drafted `rw [h]` hits a
motive error: the goal depends on `K` through
`hK.eigenvectorUnitary`; the residual cast gap closes by defeq);
(3) `hermitian_eigenvector` is the Mathlib term itself — in this
pin the lemma is already stated in cast form, so the drafted smul
rewrite is unnecessary; (4) one rewrite direction in the
per-entry `key` identity; (5) the finish of
`heatKernelGen_eq_conj` goes through an explicit function-level
identity (`Pi.coe_exp`) rather than the drafted `congr 1` descent
(the drafted form produced a non-type-correct entry goal);
(6) `heatKernelGen_add`'s proof route swapped (see above) — the
drafted transport proof cannot elaborate because the statement
never puts `hK` in scope; the statement is byte-identical, the
docstring was rewritten by the parent to describe the actual
proof, and the swap is recorded here and in the module. Three
cosmetic linter warnings remain, on record.

Axiom audit (`#print axioms`): `heatKernelGen_eq_conj`,
`heatKernelGen_trace`, `hermitian_payoff_sum`,
`genFlow_masterTick_apply`, `genFlow_masterTick_first`,
`hermitian_spectrum_real` — each exactly
`[propext, Classical.choice, Quot.sound]`. No `sorryAx`.

## Fences

Finite level only: finite index type, finite Hermitian matrix
over `ℂ`. No continuum generator, no unbounded operator, no
functional calculus beyond conjugation of `exp` and the diagonal
kernel. The tick is a property of `K`'s spectrum, not of
spacetime. The shared remainder named by ResonanceSpectrum,
SpectralClock, and ThermalKernel is discharged *for `exp`, the
trace, the payoff, stationarity, and the clock* — the two named
remainders R1/R2 above are what remains of it, and they are
remainders of statement shape, not of effort.
