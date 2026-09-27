# Finite Dirac operator and the order-one condition

**Tier T2 — Defined Operations** (`D_F` as a definition);
**Tier T3 — Proved/Checked** (self-adjointness, γ-oddness; single-probe
numerics);
**Tier T4 — Emergent/Standard** (vanishing of C, E under order-one;
Yukawa form — standard one-generation NCG results, no new mass
predictions claimed);
**Tier T5 — Open** (full 576-pair machine check = "complete Lean archive").
Source: Gurd, *The Ontological Thet–LOGOS Framework* (Revised Draft, Nexus
Research, Sept 2026), §§2.1.7–2.1.8.

## D_F (T2)

`D_F ∈ End(ℂ³²)` is self-adjoint and γ_F-odd:

```
D_F* = D_F,     γ_F D_F + D_F γ_F = 0
```

In chiral block form (Framework eq. 2), with 8×8 blocks A, B, C, E:

```
        H_L   H_R   H_L^c  H_R^c
H_L   [  0     A      C      0   ]
H_R   [ A†     0      0      E†  ]
H_L^c [ C†     0      0      B   ]
H_R^c [  0     E      B†     0   ]
```

- `A`: inter-sector Yukawa-type block (H_L ↔ H_R).
- `B`: conjugate-sector block.
- `C`, `E`: cross-sector Majorana-type couplings, constrained by
  order-one (Rung 8).

Lean (`ThetLogos.FiniteSpectralTriple`): `buildDirac_self_adjoint` and
`buildDirac_gamma_odd` — proofs ported from unity-theory
`CGurd/Spectral.lean` (T3 after build).

KO relation: `J_F D_F = D_F J_F` holds **conditionally** on block
symmetries (`B = Ā`, `C`, `E` symmetric) — Lean: `buildDirac_J_compat`
(T3, proof pending).

## Order-one condition (T4 as mathematics; T5 as machine check)

```
[[D_F, π(a)], π°(b)] = 0    for all generators a, b  (576 pairs)
```

Under order-one, the cross-term blocks **C and E vanish (or take
restricted forms)**, isolating the fermion mass matrices
`Y_u, Y_d, Y_e, Y_ν` and a possible Majorana matrix `Y_R`.
Per the framework (§2.1.8, §6): *these are the standard one-generation
structures of the literature; no new mass predictions are claimed.*

- **T4 (Emergent/Standard):** the mathematical statement C, E → 0 under
  order-one and the resulting Yukawa block form.
- **T5 (Open):** the full 576-pair machine-checked verification
  ("complete Lean archive" — future work).
- **T3 (Checked):** the single-probe `[[D_F, P₊], P₋] = 0` is verified
  numerically in `examples/order_one_probe.py`: with `C, E ≠ 0` the probe
  commutator is non-zero; setting `C = E = 0` kills it. A probe result,
  not the 576-pair theorem.

## One-generation model (T2)

`DF_oneGen Yν Ye Yu Yd`: `A = diag(Yν, Ye, Yu, Yd, Yu, Yd, Yu, Yd)`,
`B = Ā`, `C = E = 0`. Used by the spectral-gap engine.
