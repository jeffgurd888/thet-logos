# Finite Thermal-Flow Probe — Scope

**Date:** 2026-09-30
**Status:** EXECUTED 2026-09-30 — **verdict: KILL** (finite version).
See `whitepaper/finite-thermal-flow-probe/results-2026-09-30.md`.
**Tier:** T4 (numerical). No theorem claimed; a Lean (T3) follow-up only if the signal is clean.
**Parent:** thet-logos spectral-action campaign (SA-1–SA-5 territory). No continuum objects.

## The question

Let ρ_β = e^(−βD_F²) / Tr(e^(−βD_F²)) be the Gibbs state on the finite triple
(A_F, H_F, D_F), H_F = ℂ³², A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ).
Let σ_t(a) = ρ_β^{it} a ρ_β^{−it} be its modular flow, K_β = −ln ρ_β = βD_F² + (ln Z)·1.

**Does σ_t act differently across the algebraic sectors ℂ / ℍ / M₃(ℂ)?**

A "yes, measurably" keeps the Tier-5 idea alive (one thermal substrate, sector-differentiated
spectral response). A "no, uniform up to scale" kills the finite version early — which is the
point of the probe.

## Footholds (already in hand)

- `modularFlux_selfAdjoint` (ModularTime.lean, T1): φ = i[K,D] is self-adjoint.
- `eigenvalue_rigidity` (ModularTime.lean, T1): ⟨v|φ|v⟩ = 0 on D-eigenvectors — first-order rigidity.
- SA-1: Tr(D_F²) and the fluctuated-trace decomposition (Lean, zero sorrys, T1).
- Python D_F builders exist (engine/spectral-diag work) — no Lean dependency for the numerics.

## Design

0. **Precompute:** eigenvalues of D_F² with physical Yukawa inputs. If D_F² is near-proportional
   to 1 on any sector, the flow is trivial there — record before interpreting anything.
2. **Build** ρ_β on a log-spaced β-grid with β^{−1} from ~1 GeV to ~10⁴ GeV
   (thermal scale vs. top-Yukawa scale ~173 GeV is the interesting crossing).
3. **Candidate observables** (fix one at implementation; report all tried):
   - (a) Per-sector modular speed: max over unit self-adjoint a in sector i of ‖[K_β, a]‖₂.
   - (b) Sector-projected generator norms: ‖P_i K_β‖₂ with P_i the block projection for
     each gauge sector's support in B(H_F).
   - (c) Chiral-sector response: restrict to H_L / H_R / conjugates; compare flow rates.
4. **Scan:** plot each observable vs. β^{−1}; look for sector *differentiation* (different
   curves), not just nonzero response.
5. **Controls:** repeat with D_F → 0 (expect uniform trivial flow) and with shuffled Yukawas
   (expect the differentiation pattern to track the Yukawa hierarchy if the signal is real).

## Kill / success criteria

- **KILL (finite version):** sector curves coincide up to an overall scale across the full β-grid,
  or the signal vanishes under the Yukawa-shuffle control. Verdict recorded, no Lean follow-up.
- **GO (to write-up):** robust sector differentiation that tracks physical input (Yukawa hierarchy),
  stable under controls. Then: whitepaper note (T4) + optional T3 formalization proposal.
- **Inconclusive** is an allowed outcome; report it as such.

## Confusions explicitly banned

1. **Gibbs K_β vs. synthesized K_mod.** ModularTime.lean's K = −ln ρ_synth is a *synthesized*
   modular Hamiltonian; this probe uses the *canonical* Gibbs K_β = βD_F² + ln Z. Different
   objects — compare them, never conflate them.
2. **No continuum fields.** n_e(x), Θ_T(x), ∇-forces: not in this probe. Those need SA-3's bridge,
   which is quarantined. Finite triple only.
3. **No per-sector λ.** Four tunable couplings = four inserted forces = the circularity flagged
   in the gauntlet. The probe measures response; it does not fit couplings.
4. **Coulomb is not the test.** Gauge kinetic terms are absent from the finite triple; demanding
   1/r² here repeats the gauntlet's hit #4.

## Deliverables (on GO for execution)

- `python/thet_logos/finite_thermal_flow.py` (+ tests), reusing existing D_F builders.
- Plots: per-sector observables vs. β^{−1}, with controls.
- Short whitepaper note with the verdict (GO / KILL / inconclusive), tier-labeled T4.

## Sequencing note

Numerics do not block on Lean SA-1's pending `tr_DF_fourth_yukawa`, but per "finish one before
moving on," execution starts only on Jeff's explicit GO — this file is the scope, not the start.
