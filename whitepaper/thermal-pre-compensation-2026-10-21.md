# ThermalPreCompensation — the thermal instance of the pre-compensation question

**Verdict: STANDS WHOLE (T1).** The named surviving remainder of
`PreCompensation` (28 T1, 2026-10-18) is discharged: Jeff's
pre-deformed-gears question for a thermal channel, where each
coherence is damped by a factor depending on the spectral gap —
thermalization acting through the clock's flow, not the constant
factor of a Schur family with one level. The density theorem
carries its kernel positive-semidefiniteness hypothesis **on its
face**, as chartered (a fence, pre-named K1 — not a hidden gap);
the corpus-supported cosine instance is unconditional; the
reachability criterion and the sharp obstruction are
unconditional. Compiled green 2026-10-21 (`lake build
ThetLogos.ThermalPreCompensation`, 3,368 jobs, 0 errors),
parent-verified on the exact shipped text: `.olean` present,
strict recount 24, incompleteness census 0 on comment-stripped
source, axioms on the six checked headline theorems standard only
(`propext`, `Classical.choice`, `Quot.sound`). K3 (narrowing the
iff) did not trigger.

Module: `lean/ThetLogos/ThermalPreCompensation.lean` — 24 strict
theorems/lemmas, 6 defs, 0 `@[simp]` declarations. Program totals
move **3,384 → 3,408 strict** (3,424 → 3,448
attribute-inclusive), **121 → 122 counted modules**.

## What is proved

- **The channel.** `thermDamp lam f A` scales the `(i, j)` entry
  by `f (lam i − lam j)`, with `f` carried by its properties
  (`f 0 = 1`, evenness, nowhere-vanishing, per theorem).
  Populations and zero-gap entries pass through exactly
  (`thermDamp_apply_diag`, `thermDamp_apply_of_lam_eq`); trace is
  preserved; Hermiticity is preserved (even `f`); the amplification
  `thermAmplify` (entrywise division by the factor) cancels the
  channel on both sides, and the pre-compensation candidate is
  unique (`eq_thermAmplify_of_thermDamp_eq`).
- **The corpus's own factor.** The two-kick flow average
  `½(phaseFlow s + phaseFlow (−s))` **is** `thermDamp` at the
  cosine factor `cos (s · gap)` (`thermDamp_cos_eq`), and it
  preserves density matrices **unconditionally**
  (`isDensityMatrix_thermDamp_cos` — an average of unitary
  conjugations). The scoping reason the channel is not *defined*
  this way: honest flow averages oscillate (zeros, negative
  values); a positive, nowhere-zero damping factor needs a
  Bochner/Fourier-positivity input the corpus does not carry.
- **Density, with its hypothesis on its face.**
  `isDensityMatrix_thermDamp`: if the gap kernel
  `(i, j) ↦ f (lam i − lam j)` is positive semidefinite, the
  channel preserves density matrices — via
  `thermDamp = gapKernel ⊙ A` (Hadamard product) and Mathlib's
  Schur product theorem. (`PreCompensation`'s positivity route —
  the affine split into density endpoints — does not exist for a
  gap-dependent factor; that is exactly why the hypothesis
  appears, and it is stated, not assumed silently.)
- **The reachability criterion, thermal form.**
  `thermPrecompensable_iff` and `thermPrecompensable_iff_pos`:
  a target is exactly pre-compensable iff the de-amplified
  candidate is a density matrix; Hermiticity and trace of the
  candidate are automatic — **positivity is the whole question**,
  as in `PreCompensation`. Every pre-image agrees with the target
  on zero-gap blocks (`thermDamp_preimage_apply_of_lam_eq`).
- **The exponential instance and the obstruction.**
  `expDamp β x = exp (−β|x|)` is even, positive, ≤ 1 (β ≥ 0), and
  the channels compose by adding temperatures' inverses
  (`thermDamp_expDamp_comp`: β₁ then β₂ is β₁ + β₂ — exponential
  instance only). The sharp obstruction
  (`not_thermPrecompensable_pairPlus_widest`): the maximally
  coherent pair across the **widest gap** is not
  pre-compensable at any β > 0 — the de-amplified candidate's
  quadratic form in the direction `eᵢ − eⱼ` is exactly
  `1 − exp (β · spectralWidth lam) < 0`, mirroring
  `PreCompensation`'s `1 − l⁻¹` computation. **The spectral width
  prices the tooth**: the wider the gap, the more expensive the
  pre-cut.

## Named remainders (on the module's header)

- **R1** — kernel positivity of the `expDamp` factor itself:
  classically true (Ornstein–Uhlenbeck covariance / Fourier), not
  proved here. The obstruction theorem deliberately does not
  need it.
- **R2** — continuous flow averages (sinc/Gaussian factors).
- **R3** — genuine Gibbs thermalization (Kraus/Lindblad maps,
  detailed balance) is not this Schur family; the shelf note in
  `PreCompensation`'s dossier stands as the pointer.
- **R4** — `ThermalKernel`'s jewel cited for language only;
  `HermitianReduction`'s R2 (matrix logarithm) untouched. At a
  general Hermitian `K`, the substitution `lam := hK.eigenvalues`
  is the whole transport (now available since
  `HermitianReduction` landed the same evening).

## Verification record and repairs (in the open)

Drafted and compiled 2026-10-21. Green at 3,368 jobs; header
flipped only after the parent re-ran the targeted build on the
exact shipped text (3,368/3,368; warnings only). Repairs, none
changing a statement: the bridge lemma
`posSemidef_of_isDensityMatrix` stands exactly as drafted (the
playbook's extra-hypothesis fallback was **not** used — its
self-conjugacy chain was repaired in the proof body); rewrite
orderings and pin-accurate lemma names (notably
`Matrix.diagonal_conjTranspose`; `Complex.exp_conj` direction);
`thermAmplify` marked `noncomputable` (marker only, body
identical — the same repair class as `NoCloning`'s `hadamard`);
`open scoped ComplexOrder` added — the ℂ-valued `PosSemidef`
statements cannot elaborate in this pin without the scoped order
instance Mathlib itself uses for them; no statement text altered
and the kernel hypothesis remains precisely as drafted,
undischarged and unhidden. Warnings on record (unused variables,
deprecated `if_neg`/`if_pos` names in the obstruction proof).

Axiom audit (`#print axioms`):
`thermPrecompensable_iff_pos`, `isDensityMatrix_thermDamp`,
`isDensityMatrix_thermDamp_cos`,
`not_thermPrecompensable_pairPlus_widest`,
`thermDamp_preimage_apply_of_lam_eq`, `thermDamp_expDamp_comp` —
each exactly `[propext, Classical.choice, Quot.sound]`. No
`sorryAx`.

## Fences

Finite level, finite index type, diagonal generator spectrum
`lam` (general Hermitian via `HermitianReduction`'s eigenvalue
substitution). A Schur multiplier family is not a thermalization
dynamics: no Lindblad generator, no detailed balance, no approach
to equilibrium is claimed. Fluctuations admit no exact pre-image
trick, here as in the gears: the criterion prices exact
pre-compensation of the systematic deformation only.
