# Scoping Draft — ACMD and the Stokes–Einstein Relation

**Date:** 2026-10-18 · **Status: NO CLAIM.** This charter scopes a proposed research direction. Nothing in it is a result. It exists so the direction can be worked — or killed — in the open, at its tiers.

## §1. Origin

Jeff asked what coefficient remains to be figured in the diffusion law z² = X² + y² + c·t. The answer given in session: c is the diffusivity — set to 1 by normalization in `DiffusionDefect`, and in physics computed, in the famous case, by Einstein's relation. An outside-drafted proposal then arrived ("ACMD: From Thet to Stokes–Einstein Diffusion"), asserting that ACMD proposes classical diffusion as a macroscopic limit of microscopic modular dynamics on an ultrametric substrate, with the objective of deriving D = k_BT·μ and recovering μ = 1/(6πηr). The proposal's own status line concedes it is "not yet a demonstrated ACMD derivation." It was audited against the ledger on 2026-10-18; this charter is the corrected, ratified form of the direction. The proposal text itself does not circulate as program text.

## §2. The classical target (T4, textbook)

- Einstein relation: **D = μ·k_BT** (mobility form; Einstein, 1905).
- Stokes mobility for a sphere at low Reynolds number: **μ = 1/(6πηr)**, hence D = k_BT/(6πηr).
- Einstein's diffusion law: mean-square displacement grows linearly, ⟨x²⟩ = 2dD·t in d dimensions.
- The physical road from microscopic dynamics to transport coefficients is fluctuation–dissipation / Green–Kubo: coefficients as time-integrals of equilibrium correlation functions. Any ACMD route walks that road or explains why it does not.

## §3. What the corpus owns toward it (T1)

- `DiffusionDefect` (2026-10-18): the finite walk law — expected squared displacement from (x, y) after t steps is exactly x² + y² + t, coefficient 1 pinned as the walk's chosen normalization. This proves the *shape* of Einstein's MSD law with an un-derived coefficient. It is not evidence for Stokes–Einstein (see kill K3).
- `ThermalKernel` (in build, 2026-10-18): mode-wise heat-kernel schedules of the modular generator; temperature enters through β as a parameter.
- Dissipative toe-holds: `DecoherenceToy` (the corpus's first partial trace; pinching), `PreCompensation` (dephasing family). Reversible modular flow alone does not dissipate; friction and noise require coarse-graining, which the corpus has only in toy form.

## §4. Corrections to the proposal (audit, 2026-10-18)

1. **Substrate.** "Ultrametric" has no address in this corpus: the discrete substrates of record are ℤ^d lattices and finite graphs. Worse, diffusion on ultrametric spaces is generically anomalous — the proposed substrate fights the stated target. Substrate of record for this charter: lattices and graphs. An ultrametric route would enter only as its own new claim carrying the burden of recovering *normal* diffusion.
2. **Temperature.** In the corpus's walls β is a parameter, not an output. The honest finite form of "temperature emerges" is: temperature *defined* by the noise–friction ratio at fluctuation–dissipation balance (Rung 1's Θ). Claiming thermodynamic k_BT at finite level is kill K1.
3. **The bridge.** The objective is restated in Green–Kubo terms: transport coefficients from correlation sums/integrals of the microscopic dynamics — not "operator-response dynamics," which names no object in the corpus.
4. **Ordering.** μ = 1/(6πηr) is continuum hydrodynamics (Stokes flow around a sphere). It is the last rung, not the next one.

## §5. Rungs, priced

- **Rung 1 (S–M) — the discrete Langevin brick.** A damped, kicked walker: v ← a·v + F + ξ, with ξ independent mean-zero kicks of variance σ², in a finite combinatorial model. Targets, all exact and finite: stationary velocity variance σ²/(1−a²); mean drift under constant force F gives mobility μ = 1/(1−a); position-variance growth rate σ²/(1−a)²; and the Einstein form **D = μ·Θ** with noise temperature Θ := σ²/(2(1−a)) — the relation as an exact finite identity, with temperature defined by the balance. Fences: discrete time, one particle, Θ is the model's temperature, not thermodynamic k_BT; no continuum statement.
- **Rung 2 (M–L) — Green–Kubo, finite form.** D as the summed velocity autocorrelation of the Rung-1 process (autocovariance a^|k| · stationary variance), proved equal to Rung 1's rate — the Kubo shape checked against the direct computation.
- **Rung 3 (L–XL) — continuum passage.** A scaling limit from the discrete processes toward Brownian motion / the diffusion equation. Research-scale analysis; parts likely blocked on the pinned Mathlib. Not scheduled.
- **Rung 4 (FRONTIER) — Stokes drag.** Deriving η, and with it 6πηr, from an underlying microscopic theory. Literature territory; no build priced.

## §6. Kills, pre-named

- **K1.** Any finite-level claim to have derived thermodynamic temperature (as opposed to a model ratio Θ) — dead on arrival.
- **K2.** Any ultrametric route asserted to yield normal diffusion without an explicit recovery mechanism — the substrate fights the target.
- **K3.** Any citation of `DiffusionDefect` as evidence toward Stokes–Einstein. It proves an MSD shape with a set coefficient; presenting it as a derivation of D is the ACME shape (conclusion assumed, not derived).
- **K4.** Any continuum claim earned by vocabulary — "hydrodynamic limit" as a phrase is not a limit proof.

## §7. Standing

Side charter, in the family of the Pitch 4 scoping draft: not part of the Yang–Mills ladder, no rung scheduled beyond Rung 1's price, and Rung 1 itself launches only on Jeff's word. The direction dies or climbs by its rungs, in the open.
