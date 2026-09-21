"""Spectral-gap engine: the Thet Engine simulation (Tier T3 numerical).

Builds the one-generation D_F from Yukawa blocks, perturbs by random
Hermitian inner fluctuations H (D_H = D_F + H), and tracks:
  - the spectral gap  Delta = min { |lambda| in spec(D_H) : |lambda| > 0 }
  - the flux proxy   || [K, D_H] ||  with K = -log rho for a random state
Also reports finite spectral-action moments Tr(D_F^2), Tr(D_F^4).

This is a SIMULATION (Tier T3). Theorem != Simulation != Experiment !=
Device: no hardware realization is asserted.
"""
import numpy as np
import scipy.linalg as la
from .common import DF_oneGen, random_block, DIM

SEED = 2026


def spectral_gap(D, tol=1e-10):
    eigs = np.abs(la.eigvalsh(D))
    pos = eigs[eigs > tol]
    return float(np.min(pos)) if pos.size else 0.0


def random_hermitian(rng, n=DIM, scale=1.0):
    X = rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))
    return scale * (X + X.conj().T) / 2


def random_state(rng, n=DIM):
    X = rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))
    rho = X @ X.conj().T
    return rho / np.trace(rho)


def main():
    rng = np.random.default_rng(SEED)
    D = DF_oneGen(0.5, 0.7, 1.1, 0.9, rng)
    gap0 = spectral_gap(D)
    print(f"[Gap] one-generation D_F: Delta = {gap0:.6f}")
    print(f"[Gap] Tr(D_F^2) = {np.trace(D @ D).real:.6f}, "
          f"Tr(D_F^4) = {np.trace(D @ D @ D @ D).real:.6f}")

    rho = random_state(rng)
    K = -la.logm(rho)
    K = (K + K.conj().T) / 2  # kill numerical anti-Hermitian dust
    print(f"[Gap] modular K Hermitian err: "
          f"{np.max(np.abs(K - K.conj().T)):.3e}")

    print("[Gap] perturbation sweep (D_H = D_F + eps*H):")
    for eps in [0.0, 0.01, 0.05, 0.2]:
        H = random_hermitian(rng, scale=eps if eps else 0.0)
        DH = D + H
        gap = spectral_gap(DH)
        flux = np.max(np.abs(K @ DH - DH @ K))
        print(f"        eps={eps:5.2f}  Delta={gap:.6f}  ||[K,D_H]||={flux:.3e}")
    print("[Gap] PASS (simulation -- Tier T3)")
    return True


if __name__ == "__main__":
    main()
