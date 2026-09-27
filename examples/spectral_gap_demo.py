"""Worked example: spectral-gap demo (Tier T3 simulation).

Sweeps the neutrino Yukawa Y_nu in the one-generation D_F and tracks the
spectral gap Delta = min positive |eigenvalue|. Illustrates the Thet
Engine idea (Rung 9, Indigo): perturbing the gap.

SIMULATION only. Theorem != Simulation != Experiment != Device.
No physical mass prediction is claimed (Tier T5).
"""
import sys
sys.path.insert(0, "../python")
import numpy as np
import scipy.linalg as la
from thet_logos.common import DF_oneGen

print("=== Spectral-gap demo: Y_nu sweep ===")
print(f"  {'Y_nu':>8}  {'Delta':>10}  {'Tr D^2':>10}")
for Ynu in [0.1, 0.3, 0.5, 1.0, 2.0]:
    D = DF_oneGen(Ynu, 0.7, 1.1, 0.9)
    eigs = np.abs(la.eigvalsh(D))
    gap = float(np.min(eigs[eigs > 1e-10]))
    print(f"  {Ynu:8.2f}  {gap:10.6f}  {np.trace(D @ D).real:10.4f}")
print("\nDelta tracks the smallest Yukawa (here Y_nu).")
print("No mass prediction claimed -- Tier T5.")
