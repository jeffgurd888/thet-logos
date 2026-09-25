"""Dynamic density-matrix thermalization engine (Tier T4 numerical).

Engine #7. Lindblad evolution of the 32-state density matrix toward the
Gibbs (KMS) state on the one-generation finite triple:

    rho_dot = -i[H, rho]
              + sum_{m->n} g_{m->n} (L_{mn} rho L_{mn}^+ - 1/2 {L_{mn}^+ L_{mn}, rho})

  H(lam) = (lam * D_F)^2     working-fluid Hamiltonian, same modeling choice
                             as engine_cycle.py (Tr(D^2)-type term of the
                             spectral action; a modeling choice, not a
                             derived physical Hamiltonian)
  L_{mn} = |n><m|            jumps between energy eigenstates
  g_{m->n} = kappa / (1 + exp(beta (E_n - E_m)))

The rates satisfy g_{m->n} / g_{n->m} = exp(-beta (E_n - E_m)) (detailed
balance), so the Gibbs state rho_beta = exp(-beta H)/Z is the unique
stationary state of the dissipator.

Clock readout: K(t) = -log rho(t), the time-dependent modular Hamiltonian.
Far from equilibrium the clock is unsettled; as rho(t) -> rho_beta,
K(t) -> beta (H - F I) with F = -(1/beta) log Z. Note the stationarity
subtlety: rho_beta is invariant under its OWN modular flow (KMS states
are stationary) -- the dynamics here is the approach to equilibrium,
i.e. the clock settling, not the clock ticking itself.

Initial state: pure highest-energy eigenstate |E_max><E_max| -- zero
entropy, maximal energy, as far from thermal as a state can get.

Theorem != Simulation != Experiment != Device: numerical Lindblad
dynamics on 32x32 matrices only. No device exists.
"""
import numpy as np
import scipy.linalg as la
from .common import DF_oneGen, DIM

SEED = 2026
KAPPA = 1.0
BETA = 2.0
LAM = 1.0
T_FINAL = 20.0
DT = 0.01
N_SAMPLES = 41


def gibbs_state(H, beta):
    w, V = la.eigh(H)
    p = np.exp(-beta * (w - w[0]))
    p /= p.sum()
    return (V * p) @ V.conj().T, w, V


def lindblad_superop(H, beta, kappa):
    """Full Lindbladian as a (n^2 x n^2) superoperator in vec convention
    vec(A X B) = (B^T kron A) vec(X)."""
    w, V = la.eigh(H)
    n = H.shape[0]
    dE = w[None, :] - w[:, None]            # E_n - E_m
    gamma = kappa / (1.0 + np.exp(beta * dE))
    np.fill_diagonal(gamma, 0.0)
    I = np.eye(n)
    L = -1j * (np.kron(I, H) - np.kron(H.T, I))
    for m in range(n):
        Vm = V[:, m]
        for mm in range(n):
            if m == mm:
                continue
            g = gamma[m, mm]
            Lop = np.outer(V[:, mm], Vm.conj())      # |n><m|
            LdL = Lop.conj().T @ Lop
            L += g * (np.kron(Lop.conj(), Lop)
                      - 0.5 * np.kron(I, LdL)
                      - 0.5 * np.kron(LdL.T, I))
    return L, w, V, gamma


def rk4_step(psi, dt, L):
    k1 = L @ psi
    k2 = L @ (psi + 0.5 * dt * k1)
    k3 = L @ (psi + 0.5 * dt * k2)
    k4 = L @ (psi + dt * k3)
    return psi + dt / 6.0 * (k1 + 2.0 * k2 + 2.0 * k3 + k4)


def diagnostics(rho, rho_beta, H, beta, F):
    rho = 0.5 * (rho + rho.conj().T)          # kill RK4 drift
    rho /= np.trace(rho).real                 # kill trace drift
    s = la.eigvalsh(rho - rho_beta)
    trace_dist = 0.5 * float(np.sum(np.abs(s)))
    wr, Vr = la.eigh(rho)
    wr = np.clip(wr, 1e-300, None)
    S = float(-np.sum(wr * np.log(wr)))
    E = float(np.trace(rho @ H).real)
    K = (Vr * (-np.log(wr))) @ Vr.conj().T    # K(t) = -log rho(t)
    K_beta = beta * (H - F * np.eye(H.shape[0]))
    K_err = float(la.norm(K - K_beta, ord="fro"))
    purity = float(np.trace(rho @ rho).real)
    return {"trace_dist": trace_dist, "S": S, "E": E, "K_err": K_err,
            "purity": purity}


def main():
    rng = np.random.default_rng(SEED)
    D = DF_oneGen(0.5, 0.7, 1.1, 0.9, rng)
    assert np.max(np.abs(D - D.conj().T)) < 1e-12, "D_F must be Hermitian"
    H = (LAM * D) @ (LAM * D)

    rho_beta, w_beta, _ = gibbs_state(H, BETA)
    Z = float(np.sum(np.exp(-BETA * (w_beta - w_beta[0])))) * np.exp(-BETA * w_beta[0])
    F = -np.log(Z) / BETA
    S_beta = BETA * (float(np.trace(rho_beta @ H).real) - F)

    L, w, V, gamma = lindblad_superop(H, BETA, KAPPA)

    # Gibbs state must be stationary: L vec(rho_beta) ~ 0
    stat_err = float(la.norm(L @ rho_beta.reshape(-1)))
    print(f"[Thermalize] Gibbs stationarity |L rho_beta| = {stat_err:.3e}")
    assert stat_err < 1e-10, "Gibbs state must be stationary under L"

    # Initial state: pure top-energy eigenstate (far from equilibrium)
    psi0 = V[:, -1]
    rho = np.outer(psi0, psi0.conj())
    psi = rho.reshape(-1)

    steps = int(T_FINAL / DT)
    sample_every = steps // (N_SAMPLES - 1)
    traj = []
    d0 = diagnostics(rho, rho_beta, H, BETA, F)
    traj.append((0.0, d0))
    print(f"[Thermalize] t=0: S={d0['S']:.6f} (target {S_beta:.6f}), "
          f"trace_dist={d0['trace_dist']:.3e}, purity={d0['purity']:.6f}")
    for i in range(1, steps + 1):
        psi = rk4_step(psi, DT, L)
        if i % sample_every == 0:
            rho_i = psi.reshape(DIM, DIM)
            traj.append((i * DT, diagnostics(rho_i, rho_beta, H, BETA, F)))

    t_settle = next((t for t, d in traj if d["trace_dist"] < 1e-3), None)
    dN = traj[-1][1]
    print(f"[Thermalize] t={T_FINAL}: S={dN['S']:.6f} (target {S_beta:.6f}), "
          f"trace_dist={dN['trace_dist']:.3e}, K_err={dN['K_err']:.3e}, "
          f"purity={dN['purity']:.6f}")
    print(f"[Thermalize] clock-settling time (trace_dist < 1e-3): t = {t_settle}")

    # Contractivity: trace distance to the stationary state is non-increasing
    dists = [d["trace_dist"] for _, d in traj]
    assert all(b <= a + 1e-9 for a, b in zip(dists, dists[1:])), \
        "trace distance to Gibbs must be non-increasing (CPTP contractivity)"
    assert dN["trace_dist"] < 1e-6, "must thermalize"
    assert abs(dN["S"] - S_beta) < 1e-6, "entropy must reach Gibbs entropy"
    assert dN["K_err"] < 1e-4, "modular Hamiltonian K(t) must converge to beta(H - F)"
    assert dN["S"] > d0["S"], "entropy must rise from the pure initial state"
    print("[Thermalize] PASS: rho(t) -> rho_beta; K(t) -> beta(H - F). "
          "Clock settled. T4 numerical.")


if __name__ == "__main__":
    main()
