# Thet primitives — (θ, θ†)

**Tier T1 — Assumed Primitives.** Source: Gurd, *The Ontological Thet–LOGOS
Framework* (Revised Draft, Nexus Research, Sept 2026), §1.1.
See `../epistemic-ledger/LEDGER.md`.

## Postulates

**P1 (Pairing primitive).** There exists a primitive operator pair `(θ, θ†)`
where `θ†` is the adjoint (conjugate) of `θ`, acting on an abstract Hilbert
space H. No further algebraic relations are assumed at this level: `θ` is
the un-derived seed from which the ternary algebra is generated.
(Framework Def. 1.2.)

**P2 (Generation).** Finite products of `θ`, `θ†` under the ternary product
(see `../algebra/ternary-TRO.md`) generate the operator algebra used by all
higher layers. Binary multiplication appears only as a derived operation.

**P3 (Tripotent seed).** There exists a distinguished tripotent `N₀` with
`N₀³ = N₀` (in the ternary sense `N₀ N₀† N₀ = N₀`) that anchors the
linearization `L` of the tripotent layer. Its existence and normalization are
assumed; its consequences are derived. (Framework Table 1, Rung 5.)

## What is NOT assumed

- No Hilbert space inner product at this level (emerges at Rung 6).
- No commutativity, no spectral data.
- **Withdrawn:** any claim that `N₀` fixes spacetime dimension — see
  `../algebra/tripotent-N0.md` and Tier T5 in the ledger.

## Lean mirror

`lean/ThetLogos/Axioms.lean` — `ThetPair` structure, `N0` tripotent axiom,
`L` linearization definition. The postulates above appear as `axiom`
declarations, never as proved theorems.
