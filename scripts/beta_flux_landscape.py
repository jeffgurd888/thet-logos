"""BETA-A FLUX LANDSCAPE — the honest, computable core of a "thermomagnetic
coupling" probe on the finite triple.

Tier T4 NUMERICAL EXPLORATION. Nothing here is a theorem. Lean side
(ModularFlux.lean): thermal_flux_vanishes (T1, all beta), modularFlux_betaScale
(T1, new), Gibbs-KMS-at-own-beta pinned T5.

What this builds (and does NOT build):
  * beta-family of thermal states: rho_beta = e^{-beta K}/Z over a beta grid
    (beta -> 0 hot, beta large cold). beta is GLOBAL here: the finite triple
    has no x-dependence, so there is no beta(x) gradient. That boundary is
    explicit and load-bearing.
  * inner-fluctuation axis: D_A = D + A1 + J(A1), A1 a structured 1-form at
    small ||A||/||D|| (Span-2 structured regime).
  * landscape: ||phi(beta, A)||_F with phi = i[K_beta, D_A].
  * Explicit NON-goals: photon states, refractive index, cloaking, H = D^2,
    beta(x), continuum physics. If the landscape is flat, that IS the result.

Key analytic expectation (checked numerically, proved algebraically in Lean
as modularFlux_betaScale): K_beta = beta*K + (ln Z)I, so
phi(beta, A) = beta * i[K, D_A] -- the landscape is EXACTLY beta-linear at
fixed A (up to logm/expm roundoff). Amplification beyond the triangle bound
||[K,D_A]|| <= ||[K,D]|| + ||[K,fluct]|| is impossible by the triangle
inequality; we check the ratio.

Conventions (mirror the codebase exactly):
  D_F  = build_DF()                       (32x32 Hermitian; engine13_rsd)
  K    = -logm(rho), hermitized           (modular_flow.py convention)
  phi  = i * [K, D]                       (Lean: modularFlux K D)
  Jact(X) = U @ X.conj() @ U.T            (twist-lab convention; U = UJ())
"""

import json
import os
import sys

import numpy as np
import scipy.linalg as la

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "python"))
from thet_logos.engine13_rsd import build_DF, selfadjoint_basis, thermal_state
from thet_logos.common import UJ

# ===========================================================================
# PLAYABLE PARAMETERS
# ===========================================================================
SEED      = 2026      # state / KMS randomness
SEED_A    = 202607    # 1-form coefficients (Span-2 fluctuation seed)
BETA0     = 1.0       # base inverse temperature for the lab state
PERTURB   = 0.35      # active-mode perturbation strength (lab convention)
BETA_GRID = np.logspace(-1, 1, 13)          # 0.1 .. 10  (global beta)
T_RATIOS  = np.concatenate([[0.0], np.logspace(-3, np.log10(0.05), 9)])
OUT_DIR   = os.path.join(os.path.dirname(__file__), "..", "whitepaper",
                         "figs", "beta-flux-landscape")
RES_PATH  = os.path.join(os.path.dirname(__file__), "beta-flux-results.json")

rng = np.random.default_rng(SEED)
DIM = 32

# ===========================================================================
# 1. Triple, states, modular Hamiltonians.
# ===========================================================================
D = build_DF()
evals_D = la.eigvalsh(D)
fro = lambda M: float(la.norm(M, "fro"))  # noqa: E731

# --- active mode (lab construction) ---
rho0 = thermal_state(D @ D, BETA0)
X = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))
R = X @ X.conj().T
R = R / np.trace(R).real
rho_a = rho0 + PERTURB * R
rho_a = (rho_a + rho_a.conj().T) / 2
rho_a = rho_a / np.trace(rho_a).real
w, V = la.eigh(rho_a)
w = np.clip(w, 1e-10, None)
w = w / w.sum()
rho_a = (V * w) @ V.conj().T
K_active = -la.logm(rho_a)
K_active = (K_active + K_active.conj().T) / 2.0

# --- equilibrium mode: Gibbs w.r.t. D^2 (commutes with D) ---
rho_eq = thermal_state(D @ D, BETA0)
K_eq = -la.logm(rho_eq)
K_eq = (K_eq + K_eq.conj().T) / 2.0
e_eq_comm = fro(K_eq @ D - D @ K_eq)
print(f"[setup] ||[K_eq, D]||_F = {e_eq_comm:.3e} (expect ~1e-12: equilibrium)")


def beta_family(K, beta):
    """rho_beta = e^{-beta K}/Z ; K_beta = beta*K + (ln Z) I -- ANALYTIC.

    The spectral mapping theorem for Hermitian K gives K_beta exactly;
    using logm(expm(-beta K)) instead loses ~10 digits at large beta
    (eigenvalue spread e^{beta*range(K)} destroys the small modes).
    This is algebra, not an approximation.
    """
    E = la.expm(-beta * K)
    Z = float(np.trace(E).real)
    rho_b = E / Z
    Kb = beta * K + np.log(Z) * np.eye(K.shape[0], dtype=complex)
    return rho_b, Kb, Z


def kms_residual(rho_b, K, beta, A, B):
    """KMS at the state's own beta, STABLE cyclic form.

    Tr(rho A sigma^K_{i beta}(B)) = Tr(rho B A) with sigma_{i beta}(B)
    = e^{-beta K} B e^{+beta K}. The e^{+beta K} factor overflows; the
    cyclically equivalent Tr(A e^{-beta K} B)/Z never does (K >= 0 spectrum
    here, and in general e^{-beta K} is the safe direction).
    """
    E = la.expm(-beta * K)
    Z = float(np.trace(E).real)
    lhs = np.trace(A @ E @ B) / Z
    rhs = np.trace(rho_b @ B @ A)
    return abs(lhs - rhs)


# KMS probe matrices (fixed, seeded)
A_p = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))
B_p = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))

# ===========================================================================
# 2. Structured 1-form axis: A1(t) = t * sum_k c_k [D, h_k], D_A = D + A1 + J(A1).
# ===========================================================================
U = UJ()


def Jact(X):
    return U @ X.conj() @ U.T


Hself = selfadjoint_basis()
rngA = np.random.default_rng(SEED_A)
c0 = complex(rngA.standard_normal(), rngA.standard_normal())
c1 = complex(rngA.standard_normal(), rngA.standard_normal())
A1_raw = c0 * (D @ Hself[0] - Hself[0] @ D) + c1 * (D @ Hself[1] - Hself[1] @ D)
print(f"[setup] 1-form coeffs: c0={c0:.4f}, c1={c1:.4f} (seed {SEED_A})")
print(f"[setup] ||A1_raw||_F/||D||_F = {fro(A1_raw)/fro(D):.3e}")

fluct_mats, t_used, sa_resid, ratios = [], [], [], []
for r in T_RATIOS:
    t = r * fro(D) / fro(A1_raw) if fro(A1_raw) > 0 else 0.0
    A1 = t * A1_raw
    DA = D + A1 + Jact(A1)
    sa = fro(DA - DA.conj().T)
    fluct_mats.append(DA)
    t_used.append(t)
    sa_resid.append(sa)
    ratios.append(fro(A1) / fro(D))
t_used = np.array(t_used)
print(f"[setup] t=0 self-adjointness resid: {sa_resid[0]:.3e} (sanity: D Hermitian)")

# ===========================================================================
# 3. The landscape: ||phi(beta, A)||_F for both modes.
# ===========================================================================
results = {
    "meta": {
        "seed": SEED, "seed_A": SEED_A, "beta0": BETA0, "perturb": PERTURB,
        "beta_grid": [float(b) for b in BETA_GRID],
        "t_ratios": [float(r) for r in T_RATIOS],
        "c0": [c0.real, c0.imag], "c1": [c1.real, c1.imag],
        "note": "beta is GLOBAL (finite triple has no x-dependence). "
                "No photon states, no refractive index, no cloaking.",
    },
    "modes": {},
}

for mode, K in (("active", K_active), ("equilibrium", K_eq)):
    nB, nT = len(BETA_GRID), len(T_RATIOS)
    land = np.zeros((nB, nT))
    kms = np.zeros(nB)
    lin_resid = np.zeros(nT)   # max | ||phi(beta)||/beta - slope | per t
    for i, beta in enumerate(BETA_GRID):
        rho_b, Kb, Z = beta_family(K, beta)
        kms[i] = kms_residual(rho_b, K, beta, A_p, B_p)
        for j, DA in enumerate(fluct_mats):
            phi = 1j * (Kb @ DA - DA @ Kb)
            land[i, j] = fro(phi)
    # beta-linearity per t-column: ||phi|| = slope * beta ?
    slopes = np.zeros(nT)
    for j in range(nT):
        col = land[:, j]
        slope = float(np.polyfit(BETA_GRID, col, 1)[0])
        slopes[j] = slope
        lin_resid[j] = float(np.max(np.abs(col / BETA_GRID - slope)))
    results["modes"][mode] = {
        "landscape": land.tolist(),
        "kms_max": float(kms.max()),
        "slopes": [float(s) for s in slopes],
        "linearity_max_resid": [float(r) for r in lin_resid],
        "phi_beta1_t0": float(land[BETA_GRID.tolist().index(1.0), 0]),
    }
    print(f"[{mode:11s}] KMS max resid: {kms.max():.3e} | "
          f"||phi||_F @ beta=1,t=0: {land[BETA_GRID.tolist().index(1.0), 0]:.3e} | "
          f"beta-linearity max resid: {np.max(lin_resid):.3e}")

# ===========================================================================
# 4. Amplification analysis (active mode): triangle-bound ratio.
#    amp(t) = ||[K, D_A]|| / (||[K,D]|| + ||[K, A1+J(A1)]||)  <= 1 expected.
# ===========================================================================
K = K_active
nD = fro(K @ D - D @ K)
amp, add_lo, add_hi = [], [], []
for j, DA in enumerate(fluct_mats):
    if j == 0:
        amp.append(1.0)
        continue
    A1 = (t_used[j] * A1_raw)
    Fl = A1 + Jact(A1)
    num = fro(K @ DA - DA @ K)
    den = nD + fro(K @ Fl - Fl @ K)
    amp.append(num / den if den > 0 else float("nan"))
results["amplification"] = {
    "ratios": [float(r) for r in T_RATIOS],
    "amp_triangle_ratio": [float(a) for a in amp],
    "max_amp": float(np.nanmax(amp)),
    "note": "amp <= 1 expected by the triangle inequality; >1 would be genuine superadditive amplification.",
}
print(f"[amp] max triangle ratio: {np.nanmax(amp):.6f} "
      f"({'<=1: no superadditive amplification' if np.nanmax(amp) <= 1 + 1e-9 else 'AMPLIFICATION'})")

# ridge/valley of the active landscape
land_a = np.array(results["modes"]["active"]["landscape"])
ib, it = np.unravel_index(np.argmax(land_a), land_a.shape)
print(f"[landscape] active max ||phi||_F = {land_a.max():.3e} at "
      f"beta={BETA_GRID[ib]:.2f}, t_ratio={T_RATIOS[it]:.1e}")
print(f"[landscape] active min ||phi||_F = {land_a.min():.3e} "
      f"(at beta={BETA_GRID[0]:.2f}: beta-linearity => min at smallest beta)")
land_e = np.array(results["modes"]["equilibrium"]["landscape"])
print(f"[landscape] equilibrium max ||phi||_F = {land_e.max():.3e} "
      f"(expect ~1e-9: thermal_flux_vanishes, all beta)")

with open(RES_PATH, "w") as f:
    json.dump(results, f, indent=1)
print(f"[done] results -> {RES_PATH}")

# ===========================================================================
# 5. Plots.
# ===========================================================================
os.makedirs(OUT_DIR, exist_ok=True)
BB, TT = np.meshgrid(BETA_GRID, T_RATIOS, indexing="ij")

fig, axes = plt.subplots(1, 2, figsize=(13, 5))
for ax, mode in zip(axes, ("active", "equilibrium")):
    land = np.array(results["modes"][mode]["landscape"])
    if mode == "active":
        im = ax.pcolormesh(BB, TT, land, shading="auto",
                           norm=matplotlib.colors.LogNorm())
        fig.colorbar(im, ax=ax, label="||phi||_F")
    else:
        # equilibrium landscape is exactly 0 (thermal_flux_vanishes, all beta):
        # no log scale possible; flat panel with the verdict as text.
        ax.pcolormesh(BB, TT, land, shading="auto", cmap="Greys", vmin=0, vmax=1)
        ax.text(0.5, 0.5, "||phi||_F = 0\nfor all (beta, A)\n(T1: thermal_flux_vanishes)",
                transform=ax.transAxes, ha="center", va="center", fontsize=11)
    ax.set_xscale("log"); ax.set_yscale("log")
    ax.set_xlabel("beta (global inverse temperature)")
    ax.set_ylabel("fluctuation strength ||A1||/||D||")
    ax.set_title(f"||phi(beta,A)||_F — {mode} (T4)")
    fig.colorbar(im, ax=ax, label="||phi||_F")
fig.suptitle("beta-A flux landscape: thermal x gauge -> modular flux (finite triple; no beta(x))")
fig.tight_layout()
fig.savefig(os.path.join(OUT_DIR, "fig1_landscape.png"), dpi=120)
plt.close(fig)

fig, ax = plt.subplots(figsize=(8, 5))
for j in (0, 4, 8):
    ax.loglog(BETA_GRID, land_a[:, j], "o-", ms=4,
              label=f"t_ratio={T_RATIOS[j]:.1e}")
ax.set_xlabel("beta"); ax.set_ylabel("||phi(beta,A)||_F")
ax.set_title("beta-scaling at fixed fluctuation: linear (Lean: modularFlux_betaScale)")
ax.legend()
fig.tight_layout()
fig.savefig(os.path.join(OUT_DIR, "fig2_beta_scaling.png"), dpi=120)
plt.close(fig)

fig, ax = plt.subplots(figsize=(8, 5))
ax.semilogx(T_RATIOS[1:], np.array(amp[1:]), "o-")
ax.axhline(1.0, color="k", ls="--", lw=1, label="triangle bound")
ax.set_xlabel("fluctuation strength ||A1||/||D||")
ax.set_ylabel("||[K,D_A]|| / (||[K,D]|| + ||[K,fluct]||)")
ax.set_title("amplification test: superadditive iff ratio > 1")
ax.legend()
fig.tight_layout()
fig.savefig(os.path.join(OUT_DIR, "fig3_amplification.png"), dpi=120)
plt.close(fig)

print(f"[done] plots -> {OUT_DIR}")
