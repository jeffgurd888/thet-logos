# Reproducibility Guide

## Python engines

```bash
cd python
pip install -r requirements.txt   # numpy>=1.26, scipy>=1.12
python3 run_all.py                # runs all 5 engines, prints PASS/FAIL
```

Verified environment: Python 3.12.3, numpy + scipy (system packages).

### Seeds and tolerances

| Engine | Seed | Key assertion |
|---|---|---|
| `tro` | 2026 | TRO associativity err < 1e-12; ker(L) dim < 4 |
| `order_zero` | 2026 | max \|[π(a),π°(b)]\| < 1e-10 (24×24 generators + 10 random pairs) |
| `order_one` | 2026 | probe detects C,E≠0 (> 1e-6); probe = 0 for C=E=0 (< 1e-10) |
| `spectral_gap` | 2026 | gap computed via `scipy.linalg.eigvalsh` |
| `modular_flow` | 2026 | group/stationarity err < 1e-10; KMS err < 1e-8 |

All randomness goes through `np.random.default_rng(2026)`; reruns are
bit-identical on the same platform/BLAS.

### Measured results (2026-09-21, this machine)

- TRO associativity max err: 7.653e-14 (20 trials, 3×4 complex matrices)
- Tripotent identity max err: 6.661e-16
- ker(L) dims over 30 random M₂(ℝ) tripotents: all 0 (withdrawal-consistent)
- Order-zero: 0.000e+00 exactly (structural) over 24×24 generators
- Single probe: 3.757e+00 with C,E≠0 → 0.000e+00 with C=E=0
- 576-pair census (one-gen D_F): 0.000e+00 exactly (structural, C=E=0)
- Gap demo: Δ tracks min Yukawa (0.100 → 0.100, …, 2.00 → 0.700)
- Modular flow: group 1.8e-14, stationarity 1.1e-15, KMS 5.1e-13

## Lean formalization

```bash
cd lean
lake update          # fetch mathlib4
lake exe cache get   # precompiled oleans (recommended)
lake build           # build ThetLogos
```

Toolchain: `leanprover/lean4:v4.35.0-rc2` (see `lean-toolchain`; Lake synced it
from v4.33.0 during `lake update` to match the resolved Mathlib revision).
Build status at release: see `docs/AUDIT.md` — honesty first: anything not
built is Tier T3 (statement), never claimed as machine-checked.

## Tier discipline for contributors

Every new claim needs a ledger entry (`epistemic-ledger/LEDGER.md`) with
one of the five tiers (T1–T5, `TIERS.md`). A Lean `sorry` is a T3
statement. Simulations are T3 at best. Theorem ≠ Simulation ≠ Experiment
≠ Device.
