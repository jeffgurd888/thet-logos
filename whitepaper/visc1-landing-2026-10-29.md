# VISC-1 LANDING — 2026-10-29

**Verdict: FULL.** Appended to `ThetLogos/ViscousLine.lean`
(VISC-1 adds strict 7 / defs 1; module totals strict 13 /
defs 1).

**NO CLAIM. Parts of any Millennium statement closed by this
landing: 0. Dials 0/4.**

## What landed — the generator theorem

`ternaryGenerator lam X := −(Λ X + X Λ)`, with
`Λ = Matrix.diagonal (lam cast to ℂ)`:

- **Spectrum on matrix units** (`ternaryGenerator_matrixUnit`):
  the generator's eigenvalue on the (i, j) matrix unit is
  exactly `−(λᵢ + λⱼ)`.
- **The generator theorem** (`hasDerivAt_ternaryStep_zero`,
  with `hasDerivAt_ternaryStep_zero_hermitian`): for every X,
  `HasDerivAt (fun t => ternaryStep lam t X)
  (ternaryGenerator lam Xᴴ) 0` — the step is
  `K_t * Xᴴ * K_t`, so its derivative at 0 is the generator
  applied to Xᴴ; for Hermitian X, the derivative is
  `ternaryGenerator lam X`. The form was a prediction the
  computation checked, not a definition it was forced into:
  entrywise, the step's (i, j) entry is
  `exp(−(λᵢ + λⱼ)·t) · (Xᴴ)ᵢⱼ`, whose scalar derivative is
  `−(λᵢ + λⱼ)·(Xᴴ)ᵢⱼ` — diagonal entries `−2·λᵢ·wᵢ`, as
  K-VISC-1 requires. **K-VISC-1 does not fire.**
- **Dissipativity at the diagonal seat**
  (`ternaryGenerator_dissipative_diag`): for `lam ≥ 0`, the
  trace form `Re tr (Xᴴ · ternaryGenerator lam X) ≤ 0` on
  diagonal states — stated in trace form because this pin
  has no `Inner ℂ` instance for plain matrices and the
  corpus lands no named HS-inner definition to consume;
  the trace form is the landed equivalent (entrywise it is
  `∑ i, w i · (−2·λᵢ·w i) ≤ 0`).

This theorem is the one brick the viscous line shares with
the parked TTK-2 (its generator theorem): built here, under
the viscous line only. TTK-2's other components
(`ternaryStepNorm`, level-set fixed points) remain unbuilt
and parked. No C₀-semigroup theory is cited — the pin owns
none; the derivative statement is entrywise HasDerivAt,
assembled by `hasDerivAt_pi`.

## Verification (parent, independent, from disk)

- Parent count of the whole module from disk: strict 13,
  defs 1. Census after this landing: **7,353 strict /
  7,431 attribute-inclusive / 251 counted modules** (from
  7,346 / 7,424 / 251 — an append, no new module).
- Main-tree build green (3,325 jobs). Parent axiom check
  on `hasDerivAt_ternaryStep_zero_hermitian`: exactly
  `[propext, Classical.choice, Quot.sound]`.
- Parent grep: placeholder tactic, `native_decide`, and
  the banned signature word occur 0 times in the module.

## Backers since last landing

No new backers recorded since the VISC-0 landing (earlier
today). The backers roll in `BACKERS.md` is unchanged.

## What this does not do

It gives the diagonal step its generator at the diagonal
seat. The general-Hermitian seat (VISC-2: transport through
`heatKernelGen`, superoperator multipliers
`exp(−t(λᵢ + λⱼ))` on the eigenbasis, dissipativity
transported) is the next brick, and it is where the master
kill K-VISC is live: a certified amplification instance
there would restrict the line's claims permanently to the
raw step.
