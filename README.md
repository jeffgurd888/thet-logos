# Thet-Logos

A research repository formalizing the **Ontological Thet–LOGOS Framework** —
operator-algebraic foundations, finite spectral-triple geometry, chromatic
architecture, Lean 4 formalization, Python computational engines, and a
five-tier epistemic ledger.

After: **Jeffrey Michael Gurd, Nexus Research** — *The Ontological Thet–LOGOS
Framework: Operator-Algebraic Foundations, Chromatic Flow Architecture, and
Finite Spectral-Triple Structure* (Revised Draft, Sept 2026).

## The 10-rung chromatic ladder (organizational device)

| Rung | Name | Color | Tier |
|---|---|---|---|
| 1 | Void (∅) | Black | T1 |
| 2 | Distinction ⟨a,b,c⟩ = ab†c | Cobalt | T2/T3 |
| 3 | Thet Primitive Θ = (θ, θ†) | Purple | T1 |
| 4 | LOGOS Engine K = −log ∆ | Crimson | T2/T3 |
| 5 | Tripotent Variety N₀³ = N₀ | Amber | T1/**T5 withdrawn** |
| 6 | 32-State Spectrum H_F = ℂ³² | Magenta | T2/T3 |
| 7 | Spectral Triple D_F | Cyan | T2/T3 |
| 8 | Order Conditions | Emerald | T3/T4 |
| 9 | Thet Engine (∆gap) | Indigo | T3 (simulation) |
| 10 | Epistemic Ledger | White | meta |

> The ladder is an organizational/mnemonic device, not a formalized
> Möbius-bundle construction. The Rung 5 claim that dim ker L = 4 fixes
> spacetime dimension is **withdrawn** as inconsistent on M₂(ℝ).

## Epistemic tiers (Framework §5)

| Tier | Category |
|---|---|
| T1 | Assumed Primitives — Void ∅, (θ,θ†), N₀³=N₀ |
| T2 | Defined Operations — TRO ⟨a,b,c⟩, K=−log ∆, D_F, π |
| T3 | Proved / Checked — order-zero identity (numerical); standard NCG facts |
| T4 | Emergent / Standard — vanishing cross-terms under order-one; Yukawa form |
| T5 | Open / Withdrawn — dim ker L=4 (withdrawn); unification; mass predictions; 3 generations; Möbius topology; complete Lean archive |

**Strict rule: Theorem ≠ Simulation ≠ Experiment ≠ Device.** A Lean `sorry`
is a T3 statement, never a proof. Numerical checks establish consistency of
the representation, not physical evidence.

## Layout

```
axioms/            thet primitives, TRO axioms, KO relations (T1/T2/T3)
algebra/           ternary TRO theory, tripotent N₀ + withdrawal notice
spectral/          32-state space, gauge algebra, Dirac + order-one,
                   spectral action, modular flow + mass gap
chromatic/         10-rung ladder (rungs.md), Thet Engine notes
lean/              Lean 4 + Mathlib project (ThetLogos.*)
python/            numerical engines (run: python3 python/run_all.py)
docs/              ontology index, B1–B8 bridge map, diagrams, reproducibility
epistemic-ledger/  TIERS.md + LEDGER.md (every claim tiered)
examples/          worked numerical examples
```

## Quick start

```bash
# Numerical engines (all pass)
cd python && pip install -r requirements.txt && python3 run_all.py

# Lean formalization
cd lean && lake update && lake exe cache get && lake build
```

See `docs/REPRODUCIBILITY.md` for seeds, tolerances, and measured results.
See `docs/AUDIT.md` for the release audit (what was built, tier per
component, gaps, next steps).

## License

MIT — see [LICENSE](LICENSE).
