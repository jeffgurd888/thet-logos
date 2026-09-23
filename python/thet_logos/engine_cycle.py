"""Thet-engine graduation cycle (Tier T5 numerical exploration).

Runs a quantum Otto cycle whose working fluid is the ACTUAL one-generation
finite Dirac operator D_F from thet-logos (common.DF_oneGen):

  H(lam) = (lam * D_F)^2          spectral-action Hamiltonian (Tr D^2 term)
  rho_beta = exp(-beta H) / Z     KMS (Gibbs) thermal states, finite-dim exact

Cycle (Otto):
  A: Gibbs(H_c, beta_c) -- cold bath
  A->B: adiabatic stroke lam_c -> lam_h (uniform scaling: eigenbasis fixed,
        populations frozen exactly)
  B->C: hot isochore, thermalize to Gibbs(H_h, beta_h)
  C->D: adiabatic stroke lam_h -> lam_c
  D->A: cold isochore, thermalize to Gibbs(H_c, beta_c)

Checks: W_net > 0 (the cycle delivers work), eta < eta_Carnot,
and the KMS identity Tr(rho A sigma_{i beta}(B)) = Tr(rho B A) for both
baths (modular-flow layer, cf. modular_flow.py).

Theorem != Simulation != Experiment != Device: positive W_net here
graduates the thet engine from OPEN program to GO *engine design*
(T4 with numbers). No device exists.
"""
import numpy as np
import scipy.linalg as la
from .common import DF_oneGen, DIM

SEED = 2026


def gibbs_state(H, beta):
    w, V = la.eigh(H)
    p = np.exp(-beta * (w - w[0]))
    p /= p.sum()
    return (V * p) @ V.conj().T, w


def mean_energy(rho, H):
    return float(np.trace(rho @ H).real)


def kms_error(rho, H, beta, rng):
    """|Tr(rho A sigma_{i beta}(B)) - Tr(rho B A)|, K = beta H."""
    n = H.shape[0]
    A = rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))
    B = rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))
    F = la.expm(-beta * H)          # exp(i * (i beta) * K), K = beta H
    Fi = la.expm(beta * H)
    sig = F @ B @ Fi
    return abs(np.trace(rho @ A @ sig) - np.trace(rho @ B @ A))


def main():
    rng = np.random.default_rng(SEED)
    D = DF_oneGen(0.5, 0.7, 1.1, 0.9, rng)
    assert np.max(np.abs(D - D.conj().T)) < 1e-12, "D_F must be Hermitian"

    lam_c, lam_h = 1.0, np.sqrt(2.0)   # uniform gap scaling; r = 2
    H_c = (lam_c * D) @ (lam_c * D)
    H_h = (lam_h * D) @ (lam_h * D)

    beta_c, beta_h = 2.0, 1.0 / 3.0   # T_c = 0.5, T_h = 3.0
    T_c, T_h = 1 / beta_c, 1 / beta_h
    r = (lam_h / lam_c) ** 2
    assert r < T_h / T_c, "need r < T_h/T_c for eta < eta_Carnot"

    rho_c, _ = gibbs_state(H_c, beta_c)
    rho_h, _ = gibbs_state(H_h, beta_h)

    e_kms_c = kms_error(rho_c, H_c, beta_c, rng)
    e_kms_h = kms_error(rho_h, H_h, beta_h, rng)
    print(f"[Engine] KMS bath check err: cold {e_kms_c:.3e}, hot {e_kms_h:.3e}")
    assert e_kms_c < 1e-8 and e_kms_h < 1e-8

    E_A = mean_energy(rho_c, H_c)
    E_B = mean_energy(rho_c, H_h)   # adiabatic: same state, new Hamiltonian
    E_C = mean_energy(rho_h, H_h)
    E_D = mean_energy(rho_h, H_c)   # adiabatic: same state, new Hamiltonian

    Q_h = E_C - E_B
    Q_c = E_A - E_D
    W_net = Q_h + Q_c
    eta = W_net / Q_h
    eta_carnot = 1.0 - T_c / T_h

    print(f"[Engine] Otto cycle on D_F-derived H = D_F^2 (dim {DIM}):")
    print(f"         lam_c={lam_c}, lam_h={lam_h:.4f} (r={r:.2f}), "
          f"T_c={T_c}, T_h={T_h}")
    print(f"         W_net = {W_net:.6f}   (> 0 required)")
    print(f"         Q_h   = {Q_h:.6f}")
    print(f"         eta   = {eta:.6f}   (Carnot {eta_carnot:.6f})")
    assert W_net > 0, "graduation requires positive work"
    assert 0 < eta < eta_carnot, "must respect Carnot"
    print("[Engine] GRADUATION: positive-work cycle inside thet-logos parts.")
    print("[Engine] PASS -- engine design (T4 with numbers); no device asserted.")
    return True


if __name__ == "__main__":
    main()
