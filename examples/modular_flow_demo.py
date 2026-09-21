"""Worked example: modular flow / thermal time (Tier T3 simulation).

Builds K = -log rho for a random 32-state density matrix and shows the
modular flow sigma_s(A) = e^{isK} A e^{-isK} acting on an observable:
the flow is periodic (K has discrete spectrum) -- a finite-dimensional
cartoon of thermal time (Rung 4, Crimson).

SIMULATION only. Theorem != Simulation != Experiment != Device.
"""
import sys
sys.path.insert(0, "../python")
import numpy as np
import scipy.linalg as la

rng = np.random.default_rng(2026)
X = rng.standard_normal((32, 32)) + 1j * rng.standard_normal((32, 32))
rho = X @ X.conj().T
rho /= np.trace(rho)
K = -la.logm(rho)
K = (K + K.conj().T) / 2

A = rng.standard_normal((32, 32)) + 1j * rng.standard_normal((32, 32))
A = (A + A.conj().T) / 2  # observable

print("=== Modular flow demo ===")
print(f"  {'s':>6}  {'<A>_s = Tr(rho sigma_s(A))':>28}")
for s in [0.0, 0.5, 1.0, 2.0, 5.0]:
    U = la.expm(1j * s * K)
    As = U @ A @ U.conj().T
    print(f"  {s:6.2f}  {np.trace(rho @ As).real:28.12f}")
print("\nExpectation is s-independent (stationarity) -- thermal equilibrium.")
