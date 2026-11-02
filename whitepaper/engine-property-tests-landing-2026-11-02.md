# PROPERTY-BASED ENGINE TESTS LANDING — T2 NUMERICS — 2026-11-02

Jeff's order (2026-11-01 23:04 EST, "fire 1→4"), vector 3.

**TIER LABEL — READ FIRST.** Everything in this dossier is T2 numerics
about a Python simulator. **These tests harden the simulator and verify
NOTHING about the Lean theorems in this repository.** Theorem ≠
Simulation ≠ Experiment ≠ Device. Census unchanged (12,641 / 13,153 /
445, zero sorrys); no Lean file was touched; NO CLAIM; dials 0/4.

## What shipped

- **`python/tests/test_engine_property.py`** — a hypothesis-based
  property suite (8 properties, 25 examples each) over
  `engine_cycle.py` and `modular_flow.py`, under random Hermitian /
  positive-semidefinite perturbations at small dimension (n = 2..6):
  - Gibbs state is a valid density matrix (Hermitian, trace 1, PSD,
    returned spectrum = spectrum of H);
  - von Neumann entropy within [0, log n]; β = 0 gives the maximally
    mixed state with S = log n exactly;
  - mean energy within the spectral bounds;
  - KMS residual < 1e-6 in the conditioned regime (unit spectral norm);
  - Otto-cycle bookkeeping in the engine's own regime (uniform scaling
    H_h = r·H_c, β_h·r < β_c): first-law closure
    W_AB + W_CD + Q_h + Q_c = 0; Q_h > 0; W_net > 0; the exact
    uniform-scaling identity η = 1 − 1/r (asserted in energy units);
    η under the Carnot bound;
  - modular-flow: random states are valid density matrices;
    σ_{s+t} = σ_s ∘ σ_t; stationarity Tr(ρ σ_s(A)) = Tr(ρ A).
- **`python/tests/requirements-test.txt`** — test-only dependencies
  (pytest, hypothesis); runtime `requirements.txt` untouched.

## Run record

Environment: a throwaway venv (hypothesis is not installed in the
system environment and PEP 668 blocks a system install) with
numpy 2.5.4 / scipy 1.18.1 / hypothesis 6.170.14 / pytest (venv).
Note for reproducers: the system environment carries numpy 1.26.4 /
scipy 1.11.4; the suite was run under the venv pins above.

**Final state: the new suite passes 8/8 (fresh hypothesis database and
a fixed-seed rerun); the full `python/tests/` directory passes 43/43**
(35 pre-existing tests + the 8 new properties).

## Failures on the first run — reported at full rank

The first version of the suite FAILED 2 of 8 properties. Both failures
were diagnosed before any change; both were **test-side defects** (the
suite's tolerances/regimes, not the engine). No engine code was modified
— `engine_cycle.py`, `modular_flow.py`, `common.py` are byte-identical
to before this order.

1. **KMS residual 1.934e-06 vs the asserted absolute 1e-6** (n=5,
   β=3.0, unnormalized random PSD H). `kms_error` forms expm(±βH)
   explicitly, so its floating-point residual scales with term
   magnitudes and exp(β‖H‖) conditioning; 1.9e-06 is float noise at
   that scale, and the identity is exact in real arithmetic. Fix
   (test-side): normalize H to unit spectral norm — the conditioned
   regime the engine itself operates in — with the diagnosis recorded
   in the test's comment.
2. **Otto bookkeeping, two draws.** (a) η deviated from 1 − 1/r by
   3.24e-08 against a 1e-8 ratio tolerance: η is a ratio W/Q_h and
   amplifies energy rounding when Q_h is small. Fix (test-side):
   assert the identity in energy units, |W_net − (1−1/r)·Q_h| scaled
   by the energy scale. (b) Q_h came out **exactly 0.0** on a draw
   with spectrum {0, 10}: the hot/cold mean energies differ at the
   e^{−30}..e^{−40} level and cancel in floating point — the regime's
   strict positivity is real-arithmetic true but unrepresentable
   there. Fix (test-side): the nondegeneracy conditions are now
   hypothesis `assume(...)`s (reported as filtered, not silently
   skipped), with the float floor stated.

Had either diagnosis pointed at the engine, the order's rule was to
report the bug, not patch it. Neither did.
