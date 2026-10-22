# Tesla Vortex Modular Dynamics — Rung 1: thermal separation — STANDS WHOLE (T1)

**Date:** 2026-10-22. **Commission:** Jeff, 2026-10-22 (idea dictated 14:53 EDT;
scope approved by widget tap + text, 14:55 EDT). **Charter:**
`whitepaper/tesla-vortex-modular-dynamics-scoping-2026-10-22.md` (audit of
Jeff's three-link chain before any build; fences K-TV1/K-TV2/K-TV3).
**Module:** `lean/ThetLogos/TeslaVortexSeparation.lean`.
**Declarations:** 18 strict theorems + 1 definition (`thermalSeparation`),
0 attribute-line declarations. **Program census after this landing: 3,561
strict / 3,601 attribute-inclusive, 128 counted modules.**

## What was built

The finite, provable core of link 1 of Jeff's chain: a thermal (Gibbs) state
over two sectors separates charge across them, exactly. With sector energies
`E : Fin 2 → ℝ`, input charge `q` (sector 0 carries `+q`, sector 1 carries
`−q`), and inverse temperature `β`, the separation is the Gibbs state's
normalized expectation of the charge observable.

## Verdicts — all five targets STAND (T1, 0 sorry, standard axioms only)

- **T1 — exact formula.** `S(β) = q·(e^{−βE₀} − e^{−βE₁}) / (e^{−βE₀} +
  e^{−βE₁})` — the partition normalization cancels; the ratio is independent
  of the Gibbs `logZ` convention (`thermalSeparation_eq_of_logZ`). Tanh form
  also proved: `S(β) = −q·tanh(β·(E₀ − E₁)/2)`.
- **T2 — zero iff equal.** For `β > 0`, `q ≠ 0`: `S(β) = 0 ⟺ E₀ = E₁`; plus
  the degenerate companions (equal energies vanish at all β; β = 0 vanishes
  for all energies).
- **T3 — monotonicity.** For a nonzero gap and `0 ≤ β₁ < β₂`:
  `|S(β₁)| < |S(β₂)|`, via `|S(β)| = |q|·(1 − e^{−β|gap|})/(1 + e^{−β|gap|})`.
- **T4 — bound and saturation, in full.** `|S(β)| < |q|` at every real β;
  `|S(β)| → |q|` as `β → ∞`; and both signed limits (`E₀ < E₁ ⇒ S → q`;
  `E₁ < E₀ ⇒ S → −q`). Nothing pinned partial.
- **T5 — flux hook.** Through the FluxClassification imports: a cross-sector
  entry of `D` at `β > 0` with a gap forces the modular flux of the
  separated Gibbs state's `K = diagModularK (gibbsWeightsE β E logZ)` to be
  nonzero (arbitrary `logZ`); the classification iff (flux = 0 ⟺ no `D`
  entries across distinct energy sectors); the one-sector collapse
  companion.

## Fences (on the module's face, standing)

- **K-TV1:** `q` and the energies are INPUTS. No charge values are derived;
  this is not the proton, neutron, or electron charge; no nucleus or atom
  is modeled. Thermodynamics here converts an energy gap into a population
  separation — it does not create the gap.
- **K-TV2:** Links 2–3 of Jeff's chain (separation creating the nuclear
  charge; electrons trapped in magnetic suspension) are NOT modeled. They
  stand as T5 picture with their standing NO-GOs where the record holds
  them (charge assignments: verdict 2026-10-22 10:10 EDT; charges as inputs:
  circularity ledger Row 2).
- **K-TV3:** "Tesla Vortex" is Jeff's coinage for his electric heat gauge
  vortex (pinned 2026-10-21) — not Tesla's devices, not 3-6-9 numerology.

## Verification

Built in scratch (`~/workspace/tvmd-scratch/`, md5 of the verified candidate
`78ae53278771d7c748e2815da6d01669`); final scratch compile exit 0, empty log.
Parent-verified: independent md5, comment-stripped hygiene scan (0 sorry /
admit / axioms), strict recount (18), `#print axioms` on all 18 theorems —
standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), no
`sorryAx`, no corpus axioms. In-tree build green (see repo commit).

## Status

Rung 1 STANDS WHOLE. Rung 2 is NOT commissioned. NO CLAIM beyond the finite
identities above; nothing here is a statement about real nuclei, atoms, or
physical charge.
