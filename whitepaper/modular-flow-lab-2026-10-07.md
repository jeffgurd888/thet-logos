# Modular Flow Laboratory — numerical track of the "play offense" program

**Date:** 2026-10-07 · **Tier: T4** (numerical exploration — nothing here is a theorem)
**Instrument:** `scripts/modular_flow_lab.py` · **Plots:** `whitepaper/figs/modular-flow-lab/`
**Status:** built, run, all checks green. Not pushed (parent's call).

## What was built

A hands-on instrument that evolves the modular flow on the finite spectral
triple and watches what moves. All playable parameters sit at the top of the
script (`MODE`, `S_MAX`, `N_S`, `BETA`, `PERTURB`, `RUN_WHATIF`): change them,
re-run, play.

Reused, not reinvented: `D_F` from `engine13_rsd.build_DF()`
(`DF_oneGen(Y_PHYS)·VEV`, 32×32 Hermitian), the represented-algebra basis and
Connes-distance machinery from `engine13_rsd`, the σ_s/KMS conventions from
`modular_flow.py`. Conventions match the Lean side exactly:

- `K = −ln ρ`, hermitized (modular Hamiltonian synthesized from the state)
- `φ = i[K, D]` (Lean `modularFlux K D`)
- `σ_s(A) = e^{isK} A e^{−isK}` (fixed-K modular flow)

## Sanity checks (all green)

| check | result |
|---|---|
| φ Hermitian | err = 0 (exact) |
| `eigenvalue_rigidity` ⟨v_j‖φ‖v_j⟩ = 0 | max 3.6e−14 |
| KMS (β=1) | err = 1.4e−13 |
| equilibrium/tracial → φ = 0 (`thermal_flux_vanishes`) | ‖φ‖_F = 0 exactly, three states |
| active mode → φ ≠ 0 (`exists_activeDriver`) | ‖φ‖_F = 1.6e3 |

## What the flow does (active mode, s ∈ [−2, 2])

**The spectrum stands still.** Max eigenvalue drift over the grid: 1.3e−12 —
machine precision. Flat lines are the *correct* result (unitary conjugation is
isospectral; `eigenvalue_rigidity` is T1). See `fig1_spectrum_rigidity.png`.

**Everything else moves.**
- Positive-energy eigenspace rotates up to **1.54 rad** (near π/2 — some
  directions fully rotate), quasi-periodic in s. `fig2_eigenspace_rotation.png`
- Commutator norms ‖[D_s, a_k]‖ vary by **~106–117** (operator norm units);
  notably they are *minimal at s = 0* — the flow drives the geometry away
  from its most commutative point. `fig3_commutator_norms.png`
- Mean finite Connes distance over probe pairs varies **0.0047 → 0.0102**;
  the spectral metric deforms. `fig4_connes_distance.png`

**New finding: the flow destroys the commutator kernel.** At s = 0 exactly,
`ker[D_s, ·]` is 1-dimensional and 20/36 probe pairs sit at infinite Connes
distance (disconnected components). For any s ≠ 0 down to ±0.001, the kernel
is 0-dimensional and all pairs are finitely connected. Mechanism (real, not
tolerance artifact): `ker[σ_s(D),·] ≠ 0 ⟺ σ_s(ker[D,·]) ∩ π(A_F) ≠ 0` — the
flow moves the kernel observable out of the represented algebra, and the
small-s commutator grows linearly, well above the 1e−8 kernel cutoff. In
words: the modular flow does not preserve the finite geometry's disconnected
structure; it mixes the algebra. Caveat: this is the Option-A represented
triple (2-dim represented algebra; M₃(ℂ) summand killed — documented artifact).

**What-if track (SPECULATIVE, beyond the Lean construction):** deforming
`D(t) = D + t·φ̂` along the flux direction itself. Eigenvalues *can* move
here — but the drift onset is **purely quadratic** (drift/t² flat at
2.52e−3 across the small-t window; log-log slope exactly 2, linear ruled
out). This is the numerical content of `eigenvalue_rigidity`: the flux
drives eigenbasis rotation at first order and eigenvalue drift only at
second order. `fig5_whatif_drift.png`, `fig5b_whatif_quadratic.png`

## Honest label

**T4 throughout.** The checks confirm the T1 theorems numerically; the flow
phenomena (kernel destruction, metric deformation, quadratic drift onset)
are *observations*, not theorems.

**BW-type signature vs. finite-size artifact:** we observe **no Lorentz-boost
signature and claim none.** The finite modular flow is a compact unitary
orbit — quasi-periodic rotation of eigenspaces, exactly the opposite of a
boost's hyperbolic non-compact action. The BW moral survives in miniature
(the flow moves the *representation* — eigenspaces, commutators, distances —
while the spectrum, the "Casimir-like" invariant, stands still), but a genuine
BW-type claim needs the Lorentzian/twisted extension of Rung 1, which does not
exist yet. Anyone reading boosts into these plots is seeing what they want
to see.

## Next play

- Prove the kernel-destruction mechanism in Lean
  (`ker[σ_s(D),·] ≠ 0 ⟺ σ_s(ker[D,·]) ∩ π(A_F) ≠ 0`) — looks formalizable.
- Feed a *driven* modular Hamiltonian into the what-if track only after the
  formal track (Stone's theorem / one-parameter group) says what a driven
  flow even means.
- The instrument is Jeff-playable now: `python3 scripts/modular_flow_lab.py`.
