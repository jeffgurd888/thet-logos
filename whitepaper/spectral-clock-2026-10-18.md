# The Spectral Clock — Dossier

**Date:** 2026-10-18
**Module:** `lean/ThetLogos/SpectralClock.lean` — 14 T1 theorems + 3 definitions, zero sorrys, no new axioms
**Verdict: STANDS** (Theorem 1 and Theorem 2 both proved; no open clause)

## The commission

Jeff (2026-10-18): having established that every faithful state carries its own clock (`ThermalClock`: the modular flow of `K = −ln ρ`), he asked whether a "spectral destiny clock" can be made — a clock whose tick is read straight off a state's spectrum.

The premise attached to the question was "electron density is Equal to thermal time." That equality was audited **NO-GO** in the open before the build: electron density is a spatial field, thermal time is a flow parameter, and no such equality is defined anywhere in the corpus. It stays out of this brick — the module contains no electron-density content, and nothing in it depends on the premise. What was commissioned and built is the clock: the tick of a state's own modular flow, read off its spectrum.

## What was built

On the resonance brick's phase law (`ResonanceSpectrum.phaseFlow_apply`: under the flow of a diagonal generator, the `(i, j)` coherence is multiplied by `exp(−it(λᵢ − λⱼ))`) — imported and reused, no parallel flow defined:

**Definitions (T2):**
- `lamRange lam` — the finite range of an eigenvalue function `lam : ι → ℝ`.
- `spectralWidth lam` — the largest gap in the spectrum, `(max of the range) − (min of the range)`.
- `masterTick lam` — `π / spectralWidth lam`.

**Theorems (T1, all in `ThetLogos`):**
- `lamRange_nonempty`, `mem_lamRange` — the range is nonempty, and membership is being a value.
- `lam_le_rangeMax`, `rangeMin_le_lam` — every eigenvalue sits inside the range's ends.
- `exists_maximizer`, `exists_minimizer` — the ends are attained.
- `spectralWidth_eq` — the width is the gap between any maximal and any minimal level.
- `spectralWidth_nonneg` — the width is always ≥ 0.
- `spectralWidth_pos` — a nondegenerate spectrum (two levels differ) has strictly positive width.
- `masterTick_pos` — under positive width the master tick is a positive time.
- **`phaseFlow_masterTick_apply` (Theorem 1, extremal flip)** — at `t = masterTick`, for `i` maximal and `j` minimal, `phaseFlow lam t A i j = − A i j`: the widest coherence is negated, phase exactly `exp(−iπ) = −1`.
- **`phaseFlow_masterTick_first` (Theorem 2, firstness)** — for the same extremal pair, every `0 < t < masterTick`, and `A i j ≠ 0`: `phaseFlow lam t A i j ≠ − A i j`. The phase angle `t · width` lies in the open interval `(0, π)`, where cosine is strictly antitone and strictly above `cos π = −1`, so the phase cannot be `−1`. The master tick is the **first** positive flip time of the widest coherence — the tick is well-defined and minimal.
- **`spectralClock_masterTick` (packaged clock)** — a diagonal generator of positive width has extremal levels whose coherence flips exactly at `π / width` and at no earlier positive time.
- **`thermalClock_masterTick` (the modular instance)** — for a packaged `ThermalClock C` whose `K = −ln ρ` eigenvalue function `j ↦ −log (weights j)` has positive width, there are levels `i, j` at which `C.flow` negates the `(i, j)` entry exactly at the master tick and no earlier. This is the corpus's own modular flow, via `thermalClock_flow_eq_phaseFlow` / `diagFlow_eq_phaseFlow` — the state's own weights are the clock's levels, so no bridge was missing and none was faked.

**Verification:** `lake build ThetLogos.SpectralClock` green; strict count 14 theorems (line-initial `theorem|lemma` on comment-stripped source); sorry/admit grep on comment-stripped source clean; `#print axioms` on all four headline theorems (`phaseFlow_masterTick_apply`, `phaseFlow_masterTick_first`, `spectralClock_masterTick`, `thermalClock_masterTick`) returns exactly `[propext, Classical.choice, Quot.sound]`.

## Fences

- **Finite, diagonal-generator case.** The clock is read off an eigenvalue function on a finite index type. The general Hermitian-generator reduction (diagonalise, then read the clock in the eigenbasis) is the resonance brick's named remainder and is **not** attempted here.
- The tick is a property of a state/generator's spectrum. It is not a property of spacetime; no continuum clock is constructed.
- The time `t` is the modular-flow parameter. It converts to physical time only through `ThermalClock`'s `β` for Gibbs states; this module performs no such conversion.
- No electron-density content (the proposed equality was NO-GO and stays out).

## What remains open

- The general Hermitian-generator reduction (inherited remainder from the resonance brick — diagonalisation of a general Hermitian generator inside the corpus's flow machinery).
- Nothing else in this brick: firstness, the clause most at risk in the commission, is proved, not shelved.
