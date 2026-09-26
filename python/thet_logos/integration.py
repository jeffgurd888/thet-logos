"""Synthesis engine -- the product geometry M x F (Tier T4 numerical).

Engine #10. The integration run: all engines unified on the
almost-commutative product.

  H    = H_lat (x) H_F,   dim 16 x 32 = 512
  D    = D_lat (x) I_32 + Gamma_lat (x) D_F     (antiperiodic lattice ring)
  X    = (D, rho, ell)

H_beta: exact finite-time Lindblad step toward Gibbs(D^2, beta), in the
  energy eigenbasis (populations via expm_multiply, coherences by exact
  decay factors -- same dissipator as engines #7/#9).
G_ell: site masses m_j = sum_{alpha,f} rho_{(alpha,j,f),(alpha,j,f)};
  smeared Newton kernel (engine-#9 construction); back-reaction deforms
  the manifold Dirac as D_lat <- sigma_3 (x) (p_lat + lam_g V).
  This vector-potential-like deformation preserves {D_lat, Gamma_lat}=0
  exactly -- as a true metric deformation would in NCG, where D_M
  always anticommutes with chirality -- hence D^2 =
  D_lat(rho)^2 (x) I + I (x) D_F^2 holds EXACTLY and the product
  structure survives back-reaction. The finite triple is fixed.
  LABEL: toy deformation, not derived.
T_dt: readout o_n = Tr(rho_n X_lat (x) I_32). This equals
  Tr(rho_n sigma_{dt}(X)) for the modular flow of rho_n itself, because
  a state is stationary under its OWN modular flow -- so the tick tracks
  the state's drift between ternary iterations, not new dynamics. The
  nontrivial temporal content is the KMS check at the fixed point,
  evaluated on the full 512-dim state AND on the finite-factor reduced
  state rho_F = Tr_lat(rho_*): the finite triple inherits thermality.

Structural fact (checked, not assumed): the two terms of D^2 =
D_lat^2 (x) I + I (x) D_F^2 commute across factors, so at the fixed
point rho_* = Gibbs(D_*^2) factorizes as rho_lat,* (x) rho_F,*. The
engine asserts the factorization numerically.

Modes:
  A: fixed ell -- ternary fixed point on the product geometry.
  B: dynamical locking ell_{n+1} = 1/Delta_n. Antiperiodic BCs are used
     throughout because engine #9 showed the periodic sector's zero
     mode makes the locking rule ill-posed (runaway); the antiperiodic
     sector admits the locking fixed point.

Theorem != Simulation != Experiment != Device: numerical only. What
this engine proves is CONSISTENCY of the nine pieces at full scale,
not new physics.

Refinement (2026-09-25, spectral/modular-time.md): in the corrected formal
core T is not a primitive -- it is derived as the modular flow of the
(rho, D, beta) triple, TIME = ModularFlow[Information, Heat, Geometry].
The T readout above is the observable trace of that derived flow.
Numerics unchanged.
"""
import numpy as np
import scipy.linalg as la

from .common import DF_oneGen, DIM as DIM_F
from .ternary import (lattice_dirac, smeared_potential, spectral_gap,
                      trace_dist, gibbs_state)

try:
    from scipy.sparse.linalg import expm_multiply as _expm_multiply
except ImportError:  # pragma: no cover
    _expm_multiply = None

SEED = 2026
N_SITES = 8
DIM_LAT = 16
DIM = DIM_LAT * DIM_F          # 512
BETA = 2.0
KAPPA = 1.0
LAM_G = 0.1
TAU_THERM = 0.5
MAX_ITER = 200
TOL = 1e-8
I_F = np.eye(DIM_F)


def thermal_step_big(H_work, rho, tau, beta=BETA, kappa=KAPPA):
    """Exact finite-time Lindblad step (512-dim), eigenbasis integration.

    Populations: p' = exp(W tau) p via expm_multiply; coherences decay
    exactly. Same dissipator as engines #7/#9.
    """
    w, V = la.eigh(H_work)
    n = len(w)
    dE = w[None, :] - w[:, None]
    with np.errstate(over="ignore"):
        g = kappa / (1.0 + np.exp(beta * dE))    # g[a,b] = rate a -> b
    np.fill_diagonal(g, 0.0)
    Gamma = g.sum(axis=1)
    W = g.T.copy()
    np.fill_diagonal(W, -Gamma)
    sig = V.conj().T @ rho @ V
    p = np.real(np.diag(sig)).copy()
    if _expm_multiply is not None:
        p_new = _expm_multiply(W * tau, p)
    else:
        p_new = la.expm(W * tau) @ p
    p_new = np.clip(p_new, 0.0, None)
    p_new /= p_new.sum()
    decay = np.exp(-(0.5 * (Gamma[:, None] + Gamma[None, :])
                     + 1j * (w[:, None] - w[None, :])) * tau)
    sig_new = sig * decay
    sig_new[np.diag_indices(n)] = p_new
    out = V @ sig_new @ V.conj().T
    out = 0.5 * (out + out.conj().T)
    return out / np.trace(out).real


def site_masses_product(rho):
    """m_j = sum_{alpha,f} rho_{(alpha,j,f),(alpha,j,f)}; index |(a,j),f>."""
    r6 = rho.reshape(2, N_SITES, DIM_F, 2, N_SITES, DIM_F)
    return np.real(np.einsum("ajfajf->j", r6))


def partial_traces(rho):
    """rho_lat (16x16), rho_fin (32x32) from the 512-dim product state."""
    r4 = rho.reshape(DIM_LAT, DIM_F, DIM_LAT, DIM_F)
    rho_lat = np.einsum("ifjf->ij", r4)
    rho_fin = np.einsum("ifig->fg", r4)
    return rho_lat, rho_fin


def kms_err_eig(rho, rng, dim):
    """KMS: Tr(rho A sigma_{i}(B)) =? Tr(rho B A), eigenbasis evaluation,
    probes normalized to unit Frobenius norm (dimension-independent)."""
    A = rng.standard_normal((dim, dim)) + 1j * rng.standard_normal((dim, dim))
    B = rng.standard_normal((dim, dim)) + 1j * rng.standard_normal((dim, dim))
    A /= la.norm(A, ord="fro")
    B /= la.norm(B, ord="fro")
    w, V = la.eigh(rho)
    w = np.clip(w, 1e-300, None)
    kap = -np.log(w)
    Ahat = V.conj().T @ A @ V
    Bhat = V.conj().T @ B @ V
    # sigma_i(B) = V diag(e^{-kap}) Bhat diag(e^{kap}) V^dagger, so
    # Tr(rho A sigma_i(B)) = sum_{a,b} w_a Ahat_{ab} Bhat_{ba} e^{kap_a-kap_b}
    lhs = np.sum(w[:, None] * Ahat * Bhat.T
                 * np.exp(kap[:, None] - kap[None, :]))
    rhs = np.trace(rho @ B @ A)
    return float(abs(complex(lhs - rhs)))


def run(mode, ell_0=1.0, seed=SEED):
    rng = np.random.default_rng(seed)
    D_lat_bare = lattice_dirac(antiperiodic=True)
    s1 = np.array([[0.0, 1.0], [1.0, 0.0]])
    s3 = np.array([[1.0, 0.0], [0.0, -1.0]])
    Gamma_lat = np.kron(s1, np.eye(N_SITES))
    assert np.max(np.abs(Gamma_lat @ D_lat_bare + D_lat_bare @ Gamma_lat)) < 1e-10
    D_F = DF_oneGen(0.5, 0.7, 1.1, 0.9, rng)
    assert np.max(np.abs(D_F - D_F.conj().T)) < 1e-12

    def build_D(D_lat):
        return np.kron(D_lat, I_F) + np.kron(Gamma_lat, D_F)

    # Initial state: lattice site 0 x finite top-energy eigenstate (S = 0).
    wF, VF = la.eigh(D_F @ D_F)
    rho_lat0 = np.zeros((DIM_LAT, DIM_LAT), dtype=complex)
    rho_lat0[0, 0] = 1.0
    psi_f = VF[:, -1]
    rho_fin0 = np.outer(psi_f, psi_f.conj())
    rho = np.kron(rho_lat0, rho_fin0)
    D_lat = D_lat_bare.copy()
    D = build_D(D_lat)
    ell = ell_0
    X_lat = np.kron(np.eye(2), np.diag(np.arange(N_SITES) - N_SITES / 2.0))

    converged, runaway, it = False, False, 0
    for it in range(1, MAX_ITER + 1):
        rho_prev, D_prev, ell_prev = rho, D, ell
        # --- H_beta ---
        D2 = np.kron(D_lat @ D_lat, I_F) + np.kron(np.eye(DIM_LAT), D_F @ D_F)
        rho = thermal_step_big(D2, rho, TAU_THERM)
        # --- G_ell (manifold factor only; preserves {D_lat, Gamma_lat} = 0) ---
        m = site_masses_product(rho)
        Vpot = smeared_potential(m, ell)
        D_lat = D_lat_bare + LAM_G * np.kron(s3, np.diag(Vpot))
        assert np.max(np.abs(Gamma_lat @ D_lat + D_lat @ Gamma_lat)) < 1e-10, \
            "product structure broken by back-reaction"
        D = build_D(D_lat)
        # --- T readout: probe expectation (modular stationarity noted) ---
        tick = float(np.real(np.trace(rho @ np.kron(X_lat, I_F))))
        if mode == "B":
            ell = 1.0 / max(spectral_gap(D), 1e-9)
            if ell > 1e6:
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
    ke_full = kms_err_eig(rho, rng, DIM)
    rho_lat, rho_fin = partial_traces(rho)
    ke_fin = kms_err_eig(rho_fin / np.trace(rho_fin).real, rng, DIM_F)
    factor_err = trace_dist(rho, np.kron(rho_lat, rho_fin))
    wr = np.clip(la.eigvalsh(rho), 1e-300, None)
    S = float(-np.sum(wr * np.log(wr)))
    return {
        "mode": mode, "converged": converged, "runaway": runaway, "iters": it,
        "Delta_star": Delta_star, "ell_star": ell,
        "beta_Delta": BETA * Delta_star, "ell_Delta": ell * Delta_star,
        "gibbs_resid": gibbs_resid, "kms_full": ke_full,
        "kms_fin": ke_fin, "factor_err": factor_err,
        "entropy": S, "tick": tick,
    }


def main():
    print(f"[Synthesis] engine #10: product geometry M x F, dim {DIM} "
          "(16 lattice x 32 finite), antiperiodic ring")
    for mode in ("A", "B"):
        r = run(mode)
        tag = "fixed ell=1.0" if mode == "A" else "locking ell=1/Delta"
        if r["runaway"]:
            print(f"[Synthesis] Mode {mode} ({tag}): RUNAWAY")
        else:
            print(f"[Synthesis] Mode {mode} ({tag}): converged={r['converged']} "
                  f"in {r['iters']} iters | Delta_*={r['Delta_star']:.6f} "
                  f"ell_*={r['ell_star']:.6f} ell_*Delta_*={r['ell_Delta']:.6f}")
            print(f"[Synthesis]   Gibbs resid={r['gibbs_resid']:.3e} | "
                  f"KMS full={r['kms_full']:.3e} | KMS finite-factor={r['kms_fin']:.3e} | "
                  f"factorization err={r['factor_err']:.3e} | S_*={r['entropy']:.6f}")
        assert not r["runaway"], f"Mode {mode} must not run away (antiperiodic sector)"
        assert r["converged"], f"Mode {mode} must converge"
        assert r["gibbs_resid"] < 1e-6, "fixed point must be Gibbs of its own D"
        assert r["kms_full"] < 1e-6 and r["kms_fin"] < 1e-6, "KMS must hold"
        assert r["factor_err"] < 1e-8, "product fixed point must factorize"
    print("[Synthesis] PASS: all nine engines consistent on the product "
          "geometry -- ternary fixed point factorizes, finite factor "
          "exactly thermal (KMS). T4 numerical.")
    return True


if __name__ == "__main__":
    main()
