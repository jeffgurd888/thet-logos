# KO relations (KO-dimension 6)

**Tier T2 — Defined Operations** (the operators);
**Tier T3 — Proved/Checked** (the relations: Lean proofs + numerical checks).
Source: Gurd, *The Ontological Thet–LOGOS Framework* (Revised Draft, Nexus
Research, Sept 2026), §§2.1.6–2.1.8.

For the finite spectral triple `(A_F, H_F, D_F, J_F, γ_F)` of KO-dimension 6:

| Relation | Statement | Tier |
|---|---|---|
| Involution | `J_F² = 1` | T3 (checked) |
| Grading | `γ_F² = 1`, `γ_F* = γ_F` | T3 (checked) |
| Dirac | `D_F* = D_F`, `γ_F D_F + D_F γ_F = 0` | T3 (checked) |
| KO sign | `J_F γ_F = −γ_F J_F` | T3 (Lean statement; proof pending) |
| KO commutation | `J_F D_F = D_F J_F` | T3 (conditional on block symmetries) |

## Concrete realization (from the framework)

- Partner map `p(k) = k+16 (k<16)`, `k−16 (k≥16)`, `p² = 1`.
- `γ_F = diag(χ_k)`, `χ = (+,−,−,+)` across the four 8-blocks,
  `χ_{p(k)} = −χ_k`.
- `(J_F v)_k = v_{p(k)}` (anti-linear in the full theory; the Lean/Python
  models use the linear permutation matrix `U_J` with
  `(U_J)_{ij} = δ_{j, p(i)}` and verify `U_J² = 1`,
  `U_J · conj(γ_F) · U_J = −γ_F`).

## Lean mirror

`lean/ThetLogos/Scaffold32.lean` — `partner`, `gammaF`, `UJ_matrix`;
theorems `partner_involutive`, `gammaF_self_adjoint`,
`gammaF_involutive`, `UJ_mul_self` (proofs ported from unity-theory
`CGurd/Spectral.lean`); `UJ_gamma_anticomm` (T3, proof pending build).
