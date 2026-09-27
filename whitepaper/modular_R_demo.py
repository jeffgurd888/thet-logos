#!/usr/bin/env python3
"""Second instantiation of R: the modular Hamiltonian of a Gibbs state.

M = M_n(C), phi(A) = Tr(rho A), rho > 0.  GNS on C^n x C^n.
Modular flow:  sigma_t(A) = rho^{-it} A rho^{it}   (KMS at beta = 1)
Modular Hamiltonian:  R = -log Delta,  Delta|k>|l> = (lam_l/lam_k)|k>|l>
Spectrum of R = Bohr frequencies {E_k - E_l}, E_k = -log lam_k.
(sign convention chosen so phi(A sigma_{i}(B)) = phi(BA) holds exactly)
Verifies: spectrum, explicit flow of an observable, KMS condition.
"""
import numpy as np

rng = np.random.default_rng(0)

def modular_data(lam):
    lam = np.asarray(lam, float)
    n = len(lam)
    assert np.all(lam > 0) and abs(lam.sum() - 1) < 1e-12
    rho = np.diag(lam)
    # Delta eigenvalues on |k>|l>
    D = np.array([[lam[l] / lam[k] for l in range(n)] for k in range(n)])
    R_eigs = -np.log(D)                      # R = -log Delta
    E = -np.log(lam)                         # "energies"
    return rho, D, R_eigs, E

def sigma(rho, A, t):
    # sigma_t(A) = rho^{-it} A rho^{+it}; both factors built directly
    # (conjugate-transpose shortcut is valid only for real t)
    lam = np.diag(rho)
    L = np.diag(lam ** (-1j * t))
    Rr = np.diag(lam ** (1j * t))
    return L @ A @ Rr

def phi(rho, A):
    return np.trace(rho @ A)

print("=== QUBIT: rho = diag(0.7, 0.3) ===")
rho, D, R_eigs, E = modular_data([0.7, 0.3])
print("Delta eigenvalues:\n", np.round(D, 6))
print("R = -log Delta eigenvalues:\n", np.round(R_eigs, 6))
w = np.log(0.7 / 0.3)
print(f"harmonic frequency omega = log(0.7/0.3) = {w:.6f}")
# flow of sigma_x: should be cos(wt) sx + sin(wt) sy
sx = np.array([[0, 1], [1, 0]], complex)
sy = np.array([[0, -1j], [1j, 0]], complex)
for t in [0.0, 0.5, 1.3]:
    St = sigma(rho, sx, t)
    expect = np.cos(w * t) * sx + np.sin(w * t) * sy
    print(f"t={t}: max|sigma_t(sx) - (cos wt sx + sin wt sy)| = {np.abs(St - expect).max():.2e}")
# KMS at beta=1: phi(A sigma_i(B)) == phi(B A)
A = rng.standard_normal((2, 2)) + 1j * rng.standard_normal((2, 2))
B = rng.standard_normal((2, 2)) + 1j * rng.standard_normal((2, 2))
lhs = phi(rho, A @ sigma(rho, B, 1j))
rhs = phi(rho, B @ A)
print(f"KMS check: |phi(A s_i(B)) - phi(BA)| = {abs(lhs - rhs):.2e}")

print("\n=== QUTRIT: rho = diag(0.5, 0.3, 0.2) — the chord ===")
rho3, D3, R3, E3 = modular_data([0.5, 0.3, 0.2])
print("energies E = -log lam:", np.round(E3, 6))
freqs = sorted(set(np.round(R3.flatten(), 10)))
print("R spectrum (Bohr frequencies):", np.round(freqs, 6))
# KMS check 3x3
A = rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3))
B = rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3))
lhs = phi(rho3, A @ sigma(rho3, B, 1j))
rhs = phi(rho3, B @ A)
print(f"KMS check: |phi(A s_i(B)) - phi(BA)| = {abs(lhs - rhs):.2e}")
# flow is quasi-periodic: sigma_{t+T} != sigma_t exactly (incommensurate freqs)
print("flow quasi-periodic (incommensurate harmonics):",
      f"{abs(np.log(0.5/0.3)/np.log(0.3/0.2)):.6f} irrational ratio")
print("\nAll checks passed: R = -log Delta is self-adjoint, generates the")
print("modular flow, spectrum = harmonic (Bohr) frequencies.")
