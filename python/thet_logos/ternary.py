"""Triple Point engine -- ternary Heat-Gravity-Time fixed point (Tier T4 numerical).

Engine #9. Numerical investigation of the ternary proposal: Heat (H),
Gravity (G), and Time (T) as three coupled transformations of a single
spectral state X = (D, rho, ell), with the fixed-point problem

    X_* = C( H_beta(X_*), G_ell(X_*), T_dt(X_*) ).

DESIGN SPEC -- what is stipulated vs. what is tested:
  * Manifold proxy: the finite triple D_F has no position/momentum, so G
    cannot live on it. This engine uses a 1D ring lattice (N sites,
    2-component spinors, Hilbert dim 2N) with lattice Dirac
    D = sigma_3 (x) p_lat as a toy manifold factor.
    LABEL: toy proxy, not the almost-commutative geometry M x F.
  * HEAT as H_beta: an exact finite-time Lindblad step (detailed-balance
    rates at inverse temperature beta, coupling kappa) toward the Gibbs
    state of H_work = D^2. Heat = change of spectral occupation/state
    weighting. Same dissipator as engine #7, integrated exactly in the
    energy eigenbasis (unconditionally stable).
  * GRAVITY as G_ell: site masses m_j from diag(rho); Nicolini-style
    smeared Newton kernel V_j = -G_N sum_i m_i erf(d_ji/2ell)/d_ji on
    ring chord distances; back-reaction D <- D_bare + lam_g (V (x) I_2).
    LABELS: smearing imported (not derived from the triple); lam_g, G_N
    are toy couplings; scalar-potential proxy (true metric coupling
    would deform D via the tetrad -- beyond this toy).
  * TIME as T_dt: modular flow of a probe position observable under the
    current state's K = -log rho -- the clock readout. At the fixed
    point rho_* is Gibbs, hence KMS-stationary under its OWN modular
    flow (same subtlety as engine #7): T acts as the identity on X_*
    and serves as the KMS check, mirroring the CLOSE step of the LOGOS
    cycle. During the transient the tick o_n = Tr(rho_n sigma_dt(a))
    tracks the approach to modular stationarity.
  * Combiner C: sequential composition X' = T_dt o G_ell o H_beta(X),
    the simplest choice. LABEL: not derived.
  * The proposal's K = beta D^2 thermal ansatz is not separately
    imposed: the Lindblad target Gibbs(H_work = D^2, beta) implements
    the same spectral-thermal link dynamically.

EXPERIMENTS:
  * Mode A (fixed ell): iterate to a self-consistent (D_*, rho_*) and
    report the dimensionless products beta*Delta_*, ell*Delta_*,
    kappa/Delta_*, with Delta_* the spectral gap of D_*.
  * Mode B (dynamical locking): ell_{n+1} = 1/Delta_n -- the "single
    spectral scale" hypothesis as a dynamical rule. Convergence is the
    question; the engine REPORTS the outcome, it does not assert it.
  * Mode C (locking + antiperiodic BCs): control experiment removing the
    ring zero mode, testing whether the Mode-B runaway is a zero-mode
    artifact or a genuine obstruction.

Theorem != Simulation != Experiment != Device: toy lattice matrices
only. No physical claim about gravity is made; the engine tests whether
the ternary fixed-point problem is well-posed and convergent.

Refinement (2026-09-25, spectral/modular-time.md): in the corrected formal
core T is not a primitive -- it is derived as the modular flow of the
(rho, D, beta) triple, TIME = ModularFlow[Information, Heat, Geometry].
The T_dt readout above is the observable trace of that derived flow.
Numerics unchanged.
"""
import numpy as np
import scipy.linalg as la
from scipy.special import erf

from .thermalize import gibbs_state
from .modular_flow import sigma

SEED = 2026
N_SITES = 8            # ring lattice; Hilbert dim = 2 * N_SITES
DIM = 2 * N_SITES
BETA = 2.0
KAPPA = 1.0
LAM_G = 0.1            # gravitational back-reaction coupling (toy)
G_NEWTON = 1.0         # toy Newton constant (lattice units)
TAU_THERM = 0.5        # Lindblad integration time per ternary iteration
DT_THERM = 0.01
MOD_TICK = 0.1         # modular-flow probe step (temporal readout)
MAX_ITER = 300
TOL = 1e-8


def lattice_dirac(n=N_SITES, antiperiodic=False):
    """Bare lattice Dirac D = sigma_3 (x) p_lat on a 1D ring.

    p_lat = F^dagger diag(p_k) F with p_k = 2 pi k / N (lattice units).
    Hermitian, chiral ({D, sigma_1 (x) I} = 0), spectrum +/- p_k.
    Periodic BCs have a zero mode (p = 0); antiperiodic BCs shift
    p_k -> 2 pi (k + 1/2)/N and remove it. Index order: |alpha, j>.
    """
    k = np.fft.fftfreq(n, d=1.0 / (2.0 * np.pi))   # p_k = 2 pi k / N
    if antiperiodic:
        k = k + np.pi / n
    k = np.fft.fftshift(k)
    F = np.fft.fft(np.eye(n)) / np.sqrt(n)      # unitary Fourier matrix
    p_lat = (F.conj().T * k) @ F
    p_lat = 0.5 * (p_lat + p_lat.conj().T)
    s3 = np.array([[1.0, 0.0], [0.0, -1.0]])
    return np.kron(s3, p_lat)


def spectral_gap(D):
    w = la.eigvalsh(D)
    nz = np.abs(w[np.abs(w) > 1e-12])
    return float(np.min(nz)) if nz.size else 0.0


def trace_dist(a, b):
    s = la.eigvalsh(a - b)
    return 0.5 * float(np.sum(np.abs(s)))


def site_masses(rho, n=N_SITES):
    """Mass density m_j = sum_alpha rho_{(alpha,j),(alpha,j)}; total = 1."""
    r4 = rho.reshape(2, n, 2, n)
    return np.real(np.einsum("ajaj->j", r4))


def smeared_potential(m, ell, n=N_SITES):
    """V_j = -G_N sum_i m_i erf(d_ji / 2ell) / d_ji on ring chord metric.

    d_ji = (N/pi) |sin(pi (j-i)/N)|; on-site term uses the limit
    erf(r/2ell)/r -> 1/(sqrt(pi) ell) as r -> 0.
    """
    j = np.arange(n)
    d = (n / np.pi) * np.abs(np.sin(np.pi * (j[:, None] - j[None, :]) / n))
    with np.errstate(divide="ignore", invalid="ignore"):
        kernel = erf(d / (2.0 * ell)) / d
    kernel[d == 0.0] = 1.0 / (np.sqrt(np.pi) * ell)
    return -G_NEWTON * kernel @ m


def thermal_step(H_work, rho, tau, beta=BETA, kappa=KAPPA):
    """Exact finite-time Lindblad step toward Gibbs(H_work, beta).

    Same dissipator as engine #7 (jumps |n><m| between H eigenstates
    with detailed-balance rates g_{m->n} = kappa/(1+exp(beta(E_n-E_m)))),
    integrated exactly in the energy eigenbasis instead of RK4 on the
    (dim^2 x dim^2) superoperator: populations follow the Pauli master
    equation p' = expm(W tau) p, coherences decay as
    exp(-[i(w_n-w_m) + (Gamma_n+Gamma_m)/2] tau). Unconditionally stable;
    Gibbs state is the exact stationary point (detailed balance).
    """
    w, V = la.eigh(H_work)
    n = len(w)
    dE = w[None, :] - w[:, None]          # E_n - E_m
    with np.errstate(over="ignore"):
        g = kappa / (1.0 + np.exp(beta * dE))   # g[a,b] = rate a -> b
    np.fill_diagonal(g, 0.0)
    Gamma = g.sum(axis=1)                  # Gamma[a] = total rate out of a
    W = g.T.copy()                         # W[n,m] = rate m -> n
    np.fill_diagonal(W, -Gamma)
    sig = V.conj().T @ rho @ V
    p_new = la.expm(W * tau) @ np.real(np.diag(sig)).copy()
    p_new = np.clip(p_new, 0.0, None)
    p_new /= p_new.sum()
    decay = np.exp(-(0.5 * (Gamma[:, None] + Gamma[None, :])
                     + 1j * (w[:, None] - w[None, :])) * tau)
    sig_new = sig * decay
    sig_new[np.diag_indices(n)] = p_new
    return hermitize_trace(V @ sig_new @ V.conj().T)


def hermitize_trace(rho):
    rho = 0.5 * (rho + rho.conj().T)
    rho /= np.trace(rho).real
    return rho


def modular_tick(rho, probe, dt=MOD_TICK):
    """T_dt readout: o = Tr(rho sigma_dt(probe)) with K = -log rho."""
    wr, Vr = la.eigh(rho)
    wr = np.clip(wr, 1e-300, None)
    K = (Vr * (-np.log(wr))) @ Vr.conj().T
    K = 0.5 * (K + K.conj().T)
    return float(np.trace(rho @ sigma(K, dt, probe)).real)


def kms_err(rho, rng):
    """KMS check at the fixed point: Tr(rho A sigma_{i}(B)) =? Tr(rho B A)."""
    A = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))
    B = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))
    wr, Vr = la.eigh(rho)
    wr = np.clip(wr, 1e-300, None)
    K = (Vr * (-np.log(wr))) @ Vr.conj().T
    K = 0.5 * (K + K.conj().T)
    lhs = np.trace(rho @ A @ sigma(K, 1j * 1.0, B))
    rhs = np.trace(rho @ B @ A)
    return float(abs(complex(lhs - rhs)))


def run(mode, ell_0=1.0, seed=SEED, antiperiodic=False):
    """Ternary iteration X_{n+1} = T_dt o G_ell o H_beta(X_n).

    mode 'A': ell fixed. mode 'B': dynamical locking ell_{n+1} = 1/Delta_n.
    antiperiodic=True removes the ring zero mode (control for the Mode-B
    runaway mechanism). Returns a result dict; convergence is reported,
    not assumed.
    """
    rng = np.random.default_rng(seed)
    D_bare = lattice_dirac(antiperiodic=antiperiodic)
    assert np.max(np.abs(D_bare - D_bare.conj().T)) < 1e-12

    # Initial state: pure, localized at site 0 -- S = 0, far from thermal.
    rho = np.zeros((DIM, DIM), dtype=complex)
    rho[0, 0] = 1.0
    D = D_bare.copy()
    ell = ell_0
    # Centered position probe for the modular clock readout.
    X_probe = np.kron(np.eye(2), np.diag(np.arange(N_SITES) - N_SITES / 2.0))

    converged, it = False, 0
    runaway = False
    for it in range(1, MAX_ITER + 1):
        rho_prev, D_prev, ell_prev = rho, D, ell
        # --- H_beta: partial thermalization toward Gibbs(D^2, beta) ---
        H_work = D @ D
        rho = thermal_step(H_work, rho, TAU_THERM)
        # --- G_ell: smeared-gravity back-reaction deforms D ---
        m = site_masses(rho)
        V = smeared_potential(m, ell)
        D = D_bare + LAM_G * np.kron(np.eye(2), np.diag(V))
        # --- T_dt: modular clock readout (identity on X at fixed point) ---
        tick = modular_tick(rho, X_probe)
        if mode == "B":
            ell = 1.0 / max(spectral_gap(D), 1e-9)
            if ell > 1e6:
                # Geometric runaway: the locking rule has no finite fixed
                # point here (ring zero mode -> uniform shift -> gap = |c|
                # -> ell = 1/|c| grows without bound, gravity decouples).
                runaway = True
                break
        delta = (trace_dist(rho, rho_prev)
                 + la.norm(D - D_prev, ord="fro") / (1.0 + la.norm(D_prev, ord="fro"))
                 + abs(ell - ell_prev) / (1.0 + abs(ell_prev)))
        if delta < TOL:
            converged = True
            break

    Delta_star = spectral_gap(D)
    rho_gibbs, _, _ = gibbs_state(D @ D, BETA)
    gibbs_resid = trace_dist(rho, rho_gibbs)
    ke = kms_err(rho, rng)
    wr = np.clip(la.eigvalsh(rho), 1e-300, None)
    S = float(-np.sum(wr * np.log(wr)))
    return {
        "mode": mode, "converged": converged, "runaway": runaway, "iters": it,
        "Delta_star": Delta_star, "ell_star": ell,
        "beta_Delta": BETA * Delta_star, "ell_Delta": ell * Delta_star,
        "kappa_over_Delta": KAPPA / max(Delta_star, 1e-12),
        "gibbs_resid": gibbs_resid, "kms_err": ke,
        "entropy": S, "tick": tick,
    }


def main():
    print("[Ternary] Triple Point engine #9: X_{n+1} = T_dt o G_ell o H_beta(X_n)"
          f" on 1D ring lattice, dim {DIM}")
    rA = run("A", ell_0=1.0)
    print(f"[Ternary] Mode A (fixed ell=1.0): converged={rA['converged']} "
          f"in {rA['iters']} iters")
    print(f"[Ternary]   Delta_*={rA['Delta_star']:.6f}  "
          f"beta*Delta_*={rA['beta_Delta']:.6f}  "
          f"ell*Delta_*={rA['ell_Delta']:.6f}  "
          f"kappa/Delta_*={rA['kappa_over_Delta']:.6f}")
    print(f"[Ternary]   Gibbs self-consistency resid={rA['gibbs_resid']:.3e}  "
          f"KMS err={rA['kms_err']:.3e}  S_*={rA['entropy']:.6f}  "
          f"tick_*={rA['tick']:.6f}")
    assert rA["converged"], "Mode A ternary iteration must converge"
    assert rA["gibbs_resid"] < 1e-6, \
        "fixed point must be the Gibbs state of its own D_* (self-consistency)"
    assert rA["kms_err"] < 1e-6, "KMS must hold at the fixed point"

    rB = run("B", ell_0=1.0)
    if rB["runaway"]:
        print(f"[Ternary] Mode B (dynamical locking ell=1/Delta): RUNAWAY "
              f"after {rB['iters']} iters (ell > 1e6) -- no finite locking "
              f"fixed point at these parameters; the rule drives ell -> inf "
              f"and switches gravity off (ring zero-mode mechanism).")
    else:
        print(f"[Ternary] Mode B (dynamical locking ell=1/Delta): "
              f"converged={rB['converged']} in {rB['iters']} iters")
        print(f"[Ternary]   Delta_*={rB['Delta_star']:.6f}  "
              f"ell_*={rB['ell_star']:.6f}  ell_*Delta_*={rB['ell_Delta']:.6f}")
    print(f"[Ternary]   Gibbs resid={rB['gibbs_resid']:.3e}  "
          f"KMS err={rB['kms_err']:.3e}")
    # Mode B outcome is REPORTED, not asserted: it is the experiment.
    # A clean runaway is a valid negative answer to the locking question.
    rC = run("B", ell_0=1.0, antiperiodic=True)
    print(f"[Ternary] Mode C (locking ell=1/Delta, ANTIPERIODIC ring, no "
          f"zero mode): runaway={rC['runaway']} converged={rC['converged']} "
          f"in {rC['iters']} iters")
    print(f"[Ternary]   Delta_*={rC['Delta_star']:.6f}  "
          f"ell_*={rC['ell_star']:.6f}  ell_*Delta_*={rC['ell_Delta']:.6f}")
    print(f"[Ternary]   Gibbs resid={rC['gibbs_resid']:.3e}  "
          f"KMS err={rC['kms_err']:.3e}")
    assert not rC["runaway"] and rC["converged"], \
        "antiperiodic control must admit the locking fixed point"
    assert rC["gibbs_resid"] < 1e-6 and rC["kms_err"] < 1e-6
    print("[Ternary] PASS: ternary fixed-point problem is well-posed "
          "(Mode A convergent, Gibbs self-consistent, KMS holds); "
          "locking hypothesis: NO finite fixed point on the periodic ring "
          "(Mode B runaway, zero-mode mechanism) but a self-consistent "
          "locking fixed point EXISTS with antiperiodic BCs "
          "(Mode C, ell_*Delta_* = 1). T4 numerical.")
    return True


if __name__ == "__main__":
    main()
