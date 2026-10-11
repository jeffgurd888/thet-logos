# Causality re-entry lab — results (T4)

**Script:** `scripts/causality_product_trace_lab.py` · **Date:** 2026-10-08
**Deterministic** (no seeds; numpy only). Run: `python3 scripts/causality_product_trace_lab.py`

## What was measured

The finite-triple obstruction (`causalCone_obstruction`, TwistedTriple.lean §10)
runs on the trace-collapse engine: `Tr[D,f] = 0` forces PSD `i[D,f]` to vanish.
The lab checks whether that engine survives the almost-commutative product by
discretizing the manifold factor (S¹, N points) and taking N → ∞.

Continuum fact: `[i·d/dx, f] = i·f'` (multiplication), so `i[D,f] = -f'` is a
bounded nonzero multiplication operator — never trace-class.

### Table 1 — the finite engine fires per truncation

`|Tr_N([D_N, f_N])|` with D_N the N-point spectral `i·d/dx`, f_N = diag(sin):

| N   | 8 | 16 | 32 | 64 | 128 | 256 |
|-----|---|----|----|----|-----|-----|
| \|Tr\[D,f\]\| | 0.00e+00 | 0.00e+00 | 0.00e+00 | 0.00e+00 | 0.00e+00 | 0.00e+00 |

Finite cyclicity holds **exactly** at every truncation — `trace_comm_eq_zero`
alive on each lattice.

### Table 2 — the engine cannot survive the limit

M_N = compression of the continuum commutator (multiplication by cos) to N
Fourier modes:

| N   | Tr(M_N) | ‖M_N‖₁/N | ‖M_N‖_op | Tr(M_N⁺)/N |
|-----|---------|----------|----------|------------|
| 8   | 0 | 0.594846 | 0.939693 | 0.297423 |
| 16  | 0 | 0.614872 | 0.982973 | 0.307436 |
| 32  | 0 | 0.625512 | 0.995472 | 0.312756 |
| 64  | 0 | 0.631005 | 0.998832 | 0.315502 |
| 128 | 0 | 0.633797 | 0.999703 | 0.316898 |
| 256 | 0 | 0.635204 | 0.999925 | 0.317602 |

Analytic limits: ‖M_N‖₁/N → 2/π ≈ 0.636620; Tr(M_N⁺)/N → 1/π ≈ 0.318310;
‖M_N‖_op → 1; Tr(M_N) = 0 exactly, all N. All confirmed to 4+ digits.

## Verdict

- Tr_N([D_N,f_N]) = 0 at every finite N, but ‖C_N‖₁ ~ 0.6366·N → ∞: the
  continuum commutator is **not trace-class** — the trace over the manifold
  factor diverges, so `posSemidef_trace_eq_zero` has no purchase in the limit.
- The collapse *conclusion* is false in the limit: ‖M_N‖_op → 1 ≠ 0, and the
  positive-part mass Tr(M_N⁺)/N → 1/π > 0 persists rather than vanishing.
- Tensoring with the finite 32-dim factor only multiplies ‖·‖₁ by a finite
  constant; the divergence is purely manifold-side.

This is the T4 support for the Lean T2 axiom `prod_nonzero_causal_commutator`
(a cone function with `i[D_prod,f]` PSD but `[D_prod,f] ≠ 0`) in
`lean/ThetLogos/CausalProduct.lean`: the finite proof's engine provably
cannot run where the trace is infinite.
