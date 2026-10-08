"""NON-GIBBS MAGNETOPHASE — the last well-posed hiding place for a non-zero
magnetophase flux.

Tier T4 NUMERICAL. The Gibbs magnetophase died by theorem
(magnetophaseFlux_vanishes, T1): K_A = beta*D_A^2 + cI commutes with D_A,
so phi_{beta,A} = 0 identically. This entry asks whether an ACTIVE
(non-equilibrium) mode with A-dependent generator rescues the flux.

Construction (mirrors modular_flow_lab.py active mode, with D -> D_A):
    rho0_A   = thermal_state(D_A @ D_A, BETA)      # Gibbs base at beta=1
    R        = X X^H / tr(X X^H), X ~ CN(0,1)     # seeded pump (SEED=2026,
                                                  # first draw: matches lab)
    rho_act  = normalize(rho0_A + PERTURB * R)     # driven state, projected
                                                  # back to full-rank positive
    K_A^act  = -logm(rho_act), hermitized         # NOT proportional to D_A^2
    phi_A^act = i [K_A^act, D_A]

At PERTURB = 0 the construction collapses to the Gibbs row (phi = 0:
consistency check). At A = 0, PERTURB = 0.35 it must reproduce the lab's
active flux ||phi||_F ~ 1.6e3 (sanity gate).

Conventions mirror magnetophase_lab.py exactly:
  D_F = build_DF();  Jact(X) = U @ X.conj() @ U.T, U = UJ()
  1-form: A1 = t * (c0 [D,h0] + c1 [D,h1]), seeds 2026 / 202607.
  beta GLOBAL = 1.0 (no beta(x)).
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
SEED      = 2026
SEED_A    = 202607
BETA      = 1.0
PERT_GRID = np.array([0.0, 0.1, 0.2, 0.35, 0.5, 0.75])  # drive strength
T_RATIOS  = np.concatenate([[0.0], np.logspace(-3, np.log10(0.05), 9)])
OUT_DIR   = os.path.join(os.path.dirname(__file__), "..", "whitepaper",
                         "figs", "non-gibbs-magnetophase")
RES_PATH  = os.path.join(os.path.dirname(__file__), "non-gibbs-magnetophase-results.json")
MD_PATH   = os.path.join(os.path.dirname(__file__), "non-gibbs-magnetophase-results.md")

DIM = 32
fro = lambda M: float(la.norm(M, "fro"))  # noqa: E731

# ===========================================================================
# 1. Triple, fluctuated Diracs (mirror magnetophase_lab.py).
# ===========================================================================
D = build_DF()
U = UJ()


def Jact(X):
    return U @ X.conj() @ U.T


Hself = selfadjoint_basis()
rngA = np.random.default_rng(SEED_A)
c0 = complex(rngA.standard_normal(), rngA.standard_normal())
c1 = complex(rngA.standard_normal(), rngA.standard_normal())
A1_raw = c0 * (D @ Hself[0] - Hself[0] @ D) + c1 * (D @ Hself[1] - Hself[1] @ D)

fluct_mats, t_used = [], []
for r in T_RATIOS:
    t = r * fro(D) / fro(A1_raw) if fro(A1_raw) > 0 else 0.0
    A1 = t * A1_raw
    DA = D + A1 + Jact(A1)
    DA = (DA + DA.conj().T) / 2.0
    fluct_mats.append(DA)
    t_used.append(t)
print(f"[setup] D_A hermiticity max resid: "
      f"{max(fro(DA - DA.conj().T) for DA in fluct_mats):.3e}")

# Seeded pump R — dedicated rng, FIRST draw is X (matches modular_flow_lab.py
# draw order: rng created, D built deterministically, then X drawn).
rng_act = np.random.default_rng(SEED)
X = rng_act.standard_normal((DIM, DIM)) + 1j * rng_act.standard_normal((DIM, DIM))
R = X @ X.conj().T
R = R / np.trace(R).real
print(f"[setup] pump R: tr=1 check {np.trace(R).real:.6f}, "
      f"||R||_F={fro(R):.4f}")


def active_state(DA, beta, perturb):
    """Driven non-Gibbs state on the fluctuated triple. Returns (rho, K_act)."""
    rho0 = thermal_state(DA @ DA, beta)
    rho = rho0 + perturb * R
    rho = (rho + rho.conj().T) / 2
    rho = rho / np.trace(rho).real
    w, V = la.eigh(rho)                       # project to full-rank positive
    w = np.clip(w, 1e-10, None)
    w = w / w.sum()
    rho = (V * w) @ V.conj().T
    K = -la.logm(rho)
    K = (K + K.conj().T) / 2.0                # hermitize (lab convention)
    return rho, K


def von_neumann_S(rho):
    w = np.clip(la.eigvalsh(rho), 1e-300, None)
    return float(-(w * np.log(w)).sum())


# Gibbs reference states/entropies (for the entropy-cost comparison)
gibbs_S = np.array([von_neumann_S(thermal_state(DA @ DA, BETA))
                    for DA in fluct_mats])

# ===========================================================================
# 2. Landscape over (drive, A): flux, entropy, entropy cost.
# ===========================================================================
nP, nT = len(PERT_GRID), len(T_RATIOS)
flux_land = np.zeros((nP, nT))     # ||phi_A^act||_F
S_land = np.zeros((nP, nT))        # S(omega_A^act)
cost_land = np.zeros((nP, nT))      # S_gibbs(A) - S_act  (entropy cost)
rot_land = np.zeros((nP, nT))      # flux-direction rotation vs A=0

phi_A0 = {}                        # reference fluxes at A=0 per drive
for i, p in enumerate(PERT_GRID):
    for j, DA in enumerate(fluct_mats):
        rho_act, K_act = active_state(DA, BETA, p)
        phi = 1j * (K_act @ DA - DA @ K_act)
        flux_land[i, j] = fro(phi)
        S_land[i, j] = von_neumann_S(rho_act)
        cost_land[i, j] = gibbs_S[j] - S_land[i, j]
    phi_A0[p] = 1j * (active_state(fluct_mats[0], BETA, p)[1] @ fluct_mats[0]
                      - fluct_mats[0] @ active_state(fluct_mats[0], BETA, p)[1])

# flux-direction rotation: normalized overlap with the A=0 flux at same drive
for i, p in enumerate(PERT_GRID):
    ref = phi_A0[p]
    rn = fro(ref)
    for j, DA in enumerate(fluct_mats):
        _, K_act = active_state(DA, BETA, p)
        phi = 1j * (K_act @ DA - DA @ K_act)
        if rn > 1e-12 and fro(phi) > 1e-12:
            rot_land[i, j] = float(abs(np.trace(ref.conj().T @ phi).real)
                                   / (rn * fro(phi)))
        else:
            rot_land[i, j] = float("nan")

# ===========================================================================
# 3. Gates and structure hunt.
# ===========================================================================
ip = list(PERT_GRID).index(0.35)
sanity = flux_land[ip, 0]
print(f"[gate ] A=0, drive=0.35: ||phi||_F = {sanity:.4e} "
      f"(lab active ~1.6e3 -> {'PASS' if 1e3 < sanity < 3e3 else 'CHECK'})")
gibbs_row = flux_land[0, :]
print(f"[gate ] drive=0 row max ||phi||_F = {gibbs_row.max():.3e} "
      f"(expect ~0: Gibbs collapse -> {'PASS' if gibbs_row.max() < 1e-6 else 'CHECK'})")
print(f"[gate ] drive=0 entropy cost max = {cost_land[0, :].max():.3e} "
      f"(expect ~0)")

# A-dependence beyond the ruled surface? Compare against the fixed-K ruled
# flux from the beta landscape: phi_ruled(A) = beta * i[K_lab, D_A].
rng_ruled = np.random.default_rng(SEED)
Xr = rng_ruled.standard_normal((DIM, DIM)) + 1j * rng_ruled.standard_normal((DIM, DIM))
Rr = Xr @ Xr.conj().T; Rr = Rr / np.trace(Rr).real
rho0_lab = thermal_state(D @ D, BETA)
rho_ruled = rho0_lab + 0.35 * Rr
rho_ruled = (rho_ruled + rho_ruled.conj().T) / 2
rho_ruled = rho_ruled / np.trace(rho_ruled).real
w, V = la.eigh(rho_ruled); w = np.clip(w, 1e-10, None); w = w / w.sum()
rho_ruled = (V * w) @ V.conj().T
K_ruled = -la.logm(rho_ruled); K_ruled = (K_ruled + K_ruled.conj().T) / 2.0
KB_ruled = BETA * K_ruled
ruled = np.array([fro(1j * (KB_ruled @ DA - DA @ KB_ruled))
                  for DA in fluct_mats])

print("[struct] A-dependence at drive=0.35: active vs ruled-surface shape")
act = flux_land[ip, :]
print(f"         ||phi_act(A)||/||phi_act(0)|| : "
      f"{np.array2string(act / act[0], precision=3, suppress_small=True)}")
print(f"         ||phi_ruled(A)||/||phi_ruled(0)||: "
      f"{np.array2string(ruled / ruled[0], precision=3, suppress_small=True)}")
print(f"[struct] flux-direction rotation vs A=0 at drive=0.35: "
      f"{np.array2string(rot_land[ip, :], precision=4, suppress_small=True)}")
print(f"[struct] landscape max ||phi||_F = {flux_land.max():.4e} "
      f"at (drive, t_ratio) = ({PERT_GRID[np.unravel_index(flux_land.argmax(), flux_land.shape)[0]]}, "
      f"{T_RATIOS[np.unravel_index(flux_land.argmax(), flux_land.shape)[1]]:.1e})")
print(f"[entr ] entropy cost at (0.35, A=0): {cost_land[ip, 0]:.6f} nats "
      f"(S_gibbs={gibbs_S[0]:.6f}, S_act={S_land[ip, 0]:.6f})")
print(f"[entr ] entropy cost range over grid: [{cost_land.min():.4f}, {cost_land.max():.4f}]")

results = {
    "meta": {
        "seed": SEED, "seed_A": SEED_A, "beta": BETA,
        "drive_grid": [float(p) for p in PERT_GRID],
        "t_ratios": [float(r) for r in T_RATIOS],
        "definition": "rho_A^act = proj_+( normalize( thermal_state(D_A^2,beta) "
                      "+ p*R) ); K_A^act = -logm(rho_A^act) hermitized; "
                      "phi_A^act = i[K_A^act, D_A]; R = XX^H/tr, X~CN(0,1) "
                      "seed 2026 first draw (matches modular_flow_lab.py). "
                      "beta GLOBAL = 1.",
    },
    "sanity_gate": {"A0_drive035_flux": float(sanity),
                    "pass": bool(1e3 < sanity < 3e3)},
    "gibbs_row_max": float(gibbs_row.max()),
    "landscape_max": float(flux_land.max()),
    "flux_landscape": flux_land.tolist(),
    "entropy_landscape": S_land.tolist(),
    "entropy_cost_landscape": cost_land.tolist(),
    "flux_rotation_vs_A0": rot_land.tolist(),
    "ruled_surface_ratio": (ruled / ruled[0]).tolist(),
    "active_ratio_drive035": (act / act[0]).tolist(),
}
with open(RES_PATH, "w") as f:
    json.dump(results, f, indent=1)
print(f"[done] results -> {RES_PATH}")

with open(MD_PATH, "w") as f:
    f.write("# Non-Gibbs magnetophase — numerical results (T4)\n\n")
    f.write(f"- sanity gate (A=0, drive=0.35): ||phi||_F = {sanity:.4e} "
            f"(lab ~1.6e3)\n")
    f.write(f"- drive=0 (Gibbs) row max: {gibbs_row.max():.3e}\n")
    f.write(f"- landscape max ||phi||_F: {flux_land.max():.4e}\n")
    f.write(f"- entropy cost at (0.35, A=0): {cost_land[ip, 0]:.6f} nats\n")
    f.write(f"- entropy cost range: [{cost_land.min():.4f}, {cost_land.max():.4f}]\n")
    f.write(f"- active A-ratio @0.35: {list(act / act[0])}\n")
    f.write(f"- ruled A-ratio: {list(ruled / ruled[0])}\n")
print(f"[done] notes -> {MD_PATH}")

# ===========================================================================
# 4. Plots.
# ===========================================================================
os.makedirs(OUT_DIR, exist_ok=True)
PP, TT = np.meshgrid(PERT_GRID, T_RATIOS, indexing="ij")

fig, ax = plt.subplots(figsize=(8, 6))
im = ax.pcolormesh(PP, TT, flux_land, shading="auto",
                   norm=matplotlib.colors.LogNorm())
fig.colorbar(im, ax=ax, label="||phi_A^act||_F")
ax.set_yscale("log")
ax.set_xlabel("drive strength p")
ax.set_ylabel("fluctuation strength ||A1||/||D||")
ax.set_title("non-Gibbs magnetophase flux landscape (T4)")
fig.tight_layout()
fig.savefig(os.path.join(OUT_DIR, "fig1_flux_landscape.png"), dpi=120)
plt.close(fig)

fig, ax = plt.subplots(figsize=(8, 5))
ax.plot(T_RATIOS[1:], act[1:] / act[0], "o-", ms=4, label="active (K_A^act)")
ax.plot(T_RATIOS[1:], ruled[1:] / ruled[0], "s-", ms=4, label="ruled (K fixed)")
ax.set_xscale("log")
ax.set_xlabel("fluctuation strength ||A1||/||D||")
ax.set_ylabel("||phi(A)|| / ||phi(0)|| at drive=0.35")
ax.set_title("A-dependence: active vs ruled surface (T4)")
ax.legend()
fig.tight_layout()
fig.savefig(os.path.join(OUT_DIR, "fig2_active_vs_ruled.png"), dpi=120)
plt.close(fig)

fig, ax = plt.subplots(figsize=(8, 5))
im = ax.pcolormesh(PP, TT, cost_land, shading="auto")
fig.colorbar(im, ax=ax, label="S_gibbs - S_act (nats)")
ax.set_yscale("log")
ax.set_xlabel("drive strength p")
ax.set_ylabel("fluctuation strength ||A1||/||D||")
ax.set_title("entropy cost of the active magnetophase (T4)")
fig.tight_layout()
fig.savefig(os.path.join(OUT_DIR, "fig3_entropy_cost.png"), dpi=120)
plt.close(fig)

print(f"[done] plots -> {OUT_DIR}")
