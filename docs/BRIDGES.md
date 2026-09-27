# Bridge Map — B1–B8

From the Master Architectural Stack (`~/workspace/unity-theory/architectural-stack.md`),
mapped onto this repository's files. The chromatic rungs (§2 of the framework)
organize the same content; rung numbers are given where they align.

| Bridge | Mapping | Rung | Repository locations |
|---|---|---|---|
| B1 | (θ, θ†) ⟶ ker L | 1–5 | `axioms/thet-primitives.md`, `axioms/TRO-axioms.md`, `algebra/ternary-TRO.md`, `algebra/tripotent-N0.md` — with the T5 withdrawal of dim ker L = 4 |
| B2 | ker L ⊗ ℂ⁸ ⟶ H_F = ℂ³² | 6 | `spectral/hilbert-space-32.md`, `lean/ThetLogos/Scaffold32.lean` |
| B3 | A_F ⟶ End(ℂ³²); order-zero | 6, 8 | `spectral/gauge-algebra.md`, `lean/ThetLogos/FiniteSpectralTriple.lean`, `python/thet_logos/order_zero.py` |
| B4 | Order-one probe ⟶ D_F(Y_f, Y_R) | 7, 8 | `spectral/dirac-order-one.md`, `lean/ThetLogos/OrderOne.lean`, `python/thet_logos/order_one.py` |
| B5 | D_F ⟶ K^G; Z_F(β) | 4 | `spectral/modular-flow.md`, `lean/ThetLogos/ThermalKMS.lean`, `python/thet_logos/modular_flow.py` |
| B6 | L²(M) ⊗ ℂ³² ⟶ S_thermal; a₀,a₂,a₄ | 7 | `spectral/spectral-action.md` (finite-side inputs; continuum derivation T5) |
| B7 | Duality map T ∘ U(D_F*) = D_F* | — | Open (T5); no target in this pass |
| B8 | D_F* ⟶ observables via ∆ | 9 | `spectral/modular-flow.md`, `python/thet_logos/spectral_gap.py` — gap defined/computed; mass predictions T5 |

## Notes

- B1's original output (dim ker L = 4) is **withdrawn** per the revised
  framework; the bridge is documented with the withdrawal, not the claim.
- B7 (duality fixed point) has no formalization target in this pass and is
  logged T5 in the ledger.
- The chromatic ladder (Rungs 1–10) is the framework's organizational
  device for the same material; see `chromatic/rungs.md`.
