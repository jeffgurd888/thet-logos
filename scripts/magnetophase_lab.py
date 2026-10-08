"""THERMAL MAGNETOPHASE ENTROPY STATE — the thermal state built FROM the
magnetized Dirac.

Tier T4 NUMERICAL. Definition:
    rho_{beta,A} = e^{-beta K_A} / Tr(e^{-beta K_A}),
where K_A is the modular Hamiltonian of the EQUILIBRIUM Gibbs state w.r.t.
D_A^2, D_A = D + A1 + J(A1) the gauge-fluctuated triple (rho-real structured
1-forms so D_A is Hermitian / rho-self-adjoint).

The state knows about the magnetic background INTRINSICALLY (K depends on A),
not via an imposed beta(x) gradient (killed: no manifold, no beta(x)).

Analytic expectation (to verify):
  K_A = beta * D_A^2 + (ln Z) I   (spectral mapping, exact -- the trap fix)
  => [K_A, D_A] = 0  =>  phi_{beta,A} = i[K_A, D_A] = 0 IDENTICALLY.
  (This is thermal_flux_vanishes / thermal_flux_vanishes_allBeta (T1, Lean)
  applied to the fluctuated Dirac D_A. The flux part of "magnetophase" is a
  proved no-go; the ENTROPY S(rho_{beta,A}) = -Tr(rho ln rho) is where the
  magnetic imprint lives -- that is the new entry.)

Conventions mirror beta_flux_landscape.py exactly:
  D_F = build_DF();  Jact(X) = U @ X.conj() @ U.T, U = UJ()
  1-form: A1 = t * (c0 [D,h0] + c1 [D,h1]), same seeds 2026 / 202607.
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
BETA_GRID = np.logspace(-1, 1, 13)          # 0.1 .. 10 (global beta)
T_RATIOS  = np.concatenate([[0.0], np.logspace(-3, np.log10(0.05), 9)])
OUT_DIR   = os.path.join(os.path.dirname(__file__), "..", "whitepaper",
                         "figs", "thermal-magnetophase")
RES_PATH  = os.path.join(os.path.dirname(__file__), "magnetophase-results.json")
MD_PATH   = os.path.join(os.path.dirname(__file__), "magnetophase-results.md")

rng = np.random.default_rng(SEED)
DIM = 32
fro = lambda M: float(la.norm(M, "fro"))  # noqa: E731

# ===========================================================================
# 1. Triple, fluctuated Diracs (mirror beta_flux_landscape.py).
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
print(f"[setup] 1-form coeffs: c0={c0:.4f}, c1={c1:.4f} (seed {SEED_A})")

fluct_mats, t_used, sa_resid = [], [], []
for r in T_RATIOS:
    t = r * fro(D) / fro(A1_raw) if fro(A1_raw) > 0 else 0.0
    A1 = t * A1_raw
    DA = D + A1 + Jact(A1)
    DA = (DA + DA.conj().T) / 2.0          # Hermitian projection (defensive)
    fluct_mats.append(DA)
    t_used.append(t)
    sa_resid.append(fro(DA - DA.conj().T))
t_used = np.array(t_used)
print(f"[setup] D_A hermiticity max resid: {max(sa_resid):.3e}")
print(f"[setup] t=0 -> D_A == D: {fro(fluct_mats[0] - D):.3e}")

# KMS probe matrices (fixed, seeded)
A_p = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))
B_p = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))


# ===========================================================================
# 2. Magnetophase construction.
#    rho_{beta,A} = e^{-beta D_A^2}/Z ; K_A = beta*D_A^2 + (ln Z) I (analytic).
# ===========================================================================
def magnetophase(beta, DA):
    """Returns (rho, K_A, Z, S). All exact up to eigh roundoff."""
    H = DA @ DA                              # D_A^2, Hermitian, >= 0
    E, V = la.eigh(H)
    Eb = np.exp(-beta * E)
    Z = float(Eb.sum())
    w = Eb / Z                               # eigenvalues of rho
    rho = (V * w) @ V.conj().T
    KA = beta * H + np.log(Z) * np.eye(DIM)  # analytic modular Hamiltonian
    # von Neumann entropy, natural log (nats); clip for safety
    wc = np.clip(w, 1e-300, None)
    S = float(-(w * np.log(wc)).sum())
    return rho, KA, Z, S


def kms_residual_stable(rho, DA, beta, A, B):
    """KMS at the state's OWN beta, stable cyclic form.

    rho_{beta,A} = e^{-beta H}/Z with H = D_A^2 is KMS at inverse temperature
    beta w.r.t. the H-flow alpha_t(B) = e^{itH} B e^{-itH}:
        Tr(rho A alpha_{i beta}(B)) = Tr(rho B A).
    Cyclic move absorbs e^{+beta H}: lhs = Tr(A e^{-beta H} B)/Z.
    (The modular K_A-flow version would test KMS at 1, not beta -- the
    beta-landscape's convention tests the Gibbs state against its own beta
    w.r.t. the base Hamiltonian flow. Here the base Hamiltonian is D_A^2.)
    Eigen-decomposition of H (>= 0) keeps e^{-beta H} stable; never expm(K_A).
    """
    H = DA @ DA
    E, V = la.eigh(H)
    Eb = np.exp(-beta * E)
    Z = float(Eb.sum())
    AV = A @ V
    VB = V.conj().T @ B
    lhs = float(np.trace((AV * Eb) @ VB).real) / Z
    rhs = float(np.trace(rho @ B @ A).real)
    return abs(lhs - rhs)


# ===========================================================================
# 3. Landscapes: entropy S(beta, A), flux ||phi_{beta,A}||, KMS residuals.
# ===========================================================================
nB, nT = len(BETA_GRID), len(T_RATIOS)
S_land = np.zeros((nB, nT))
flux_land = np.zeros((nB, nT))
kms_land = np.zeros((nB, nT))
Z_land = np.zeros((nB, nT))

for i, beta in enumerate(BETA_GRID):
    for j, DA in enumerate(fluct_mats):
        rho, KA, Z, S = magnetophase(beta, DA)
        S_land[i, j] = S
        Z_land[i, j] = Z
        phi = 1j * (KA @ DA - DA @ KA)
        flux_land[i, j] = fro(phi)
        kms_land[i, j] = kms_residual_stable(rho, DA, beta, A_p, B_p)

print(f"[flux] max ||phi_{{beta,A}}||_F over grid: {flux_land.max():.3e} "
      f"(expect ~1e-12: proved no-go, [K_A, D_A] = 0)")
print(f"[kms ] max KMS residual over grid:       {kms_land.max():.3e}")
print(f"[entr] S(beta=1, A=0) = {S_land[BETA_GRID.tolist().index(1.0), 0]:.6f} nats")
print(f"[entr] S range over A at beta=1: "
      f"[{S_land[BETA_GRID.tolist().index(1.0), :].min():.6f}, "
      f"{S_land[BETA_GRID.tolist().index(1.0), :].max():.6f}]")
print(f"[entr] S range over A at beta=10: "
      f"[{S_land[-1, :].min():.6f}, {S_land[-1, :].max():.6f}]")

# --- magnetic imprint: dS/dA structure -------------------------------------
ib1 = BETA_GRID.tolist().index(1.0)
dS_dA = S_land[ib1, :] - S_land[ib1, 0]          # entropy shift vs unfluctuated
mono = bool(np.all(np.diff(S_land[ib1, :]) <= 1e-12) or
            np.all(np.diff(S_land[ib1, :]) >= -1e-12))
print(f"[entr] entropy shift monotone in A at beta=1: {mono}")
print(f"[entr] max |dS| over A at beta=1: {np.abs(dS_dA).max():.6f} nats "
      f"({100*np.abs(dS_dA).max()/S_land[ib1,0]:.2f}% of S(beta=1,A=0))")

# --- old-vs-new flux comparison --------------------------------------------
# Old: phi(beta,A) = beta * i[K_active, D_A] with K from the UNFLUCTUATED
# lab state (beta_flux_landscape.py). Rebuild K_active identically.
BETA0, PERTURB = 1.0, 0.35
rho0 = thermal_state(D @ D, BETA0)
X = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))
R = X @ X.conj().T
R = R / np.trace(R).real
rho_a = rho0 + PERTURB * R
rho_a = (rho_a + rho_a.conj().T) / 2
rho_a = rho_a / np.trace(rho_a).real
w, V = la.eigh(rho_a)
w = np.clip(w, 1e-10, None); w = w / w.sum()
rho_a = (V * w) @ V.conj().T
K_active = -la.logm(rho_a)
K_active = (K_active + K_active.conj().T) / 2.0

old_flux = np.zeros((nB, nT))
for i, beta in enumerate(BETA_GRID):
    Kb = beta * K_active          # K_beta = beta*K + (ln Z)I; cI drops from [,]
    for j, DA in enumerate(fluct_mats):
        old_flux[i, j] = fro(1j * (Kb @ DA - DA @ Kb))
print(f"[cmp ] old flux max: {old_flux.max():.3e} (ruled surface, beta-linear)")
print(f"[cmp ] new flux max: {flux_land.max():.3e} (magnetophase: identically zero)")

# --- A=0 reduction check: magnetophase at t=0 == equilibrium beta-family ---
DA0 = fluct_mats[0]
rho_m0, KA_m0, Z_m0, S_m0 = magnetophase(1.0, DA0)
rho_eq1 = thermal_state(D @ D, 1.0)
print(f"[red ] ||rho_(beta=1,A=0) - rho_eq(beta=1)||_1: "
      f"{float(la.norm(rho_m0 - rho_eq1, 1)):.3e} (expect ~0: exact reduction)")

results = {
    "meta": {
        "seed": SEED, "seed_A": SEED_A,
        "beta_grid": [float(b) for b in BETA_GRID],
        "t_ratios": [float(r) for r in T_RATIOS],
        "definition": "rho_{beta,A} = e^{-beta D_A^2}/Z; K_A = beta*D_A^2 + (ln Z)I; "
                      "phi_{beta,A} = i[K_A, D_A]; S = -Tr(rho ln rho). "
                      "beta GLOBAL (no beta(x)).",
    },
    "flux_max": float(flux_land.max()),
    "flux_verdict": "identically zero (proved no-go: [K_A, D_A]=0 since K_A = f(D_A))",
    "kms_max": float(kms_land.max()),
    "entropy": {
        "S_beta1_A0": float(S_land[ib1, 0]),
        "S_beta1_range": [float(S_land[ib1, :].min()), float(S_land[ib1, :].max())],
        "S_beta10_range": [float(S_land[-1, :].min()), float(S_land[-1, :].max())],
        "max_abs_dS_beta1": float(np.abs(dS_dA).max()),
        "monotone_in_A_beta1": mono,
        "landscape": S_land.tolist(),
    },
    "flux_comparison": {
        "old_flux_max": float(old_flux.max()),
        "new_flux_max": float(flux_land.max()),
        "verdict": "letting K depend on A kills the flux: equilibrium w.r.t. D_A^2 "
                   "is flux-free by construction (thermal_flux_vanishes, T1).",
    },
    "reduction_A0": float(la.norm(rho_m0 - rho_eq1, 1)),
}
with open(RES_PATH, "w") as f:
    json.dump(results, f, indent=1)
print(f"[done] results -> {RES_PATH}")

with open(MD_PATH, "w") as f:
    f.write("# Thermal magnetophase entropy state — numerical results (T4)\n\n")
    f.write(f"- flux max over (beta, A) grid: {flux_land.max():.3e} "
            f"(proved no-go: [K_A, D_A] = 0)\n")
    f.write(f"- KMS max residual: {kms_land.max():.3e}\n")
    f.write(f"- S(beta=1, A=0) = {S_land[ib1, 0]:.6f} nats\n")
    f.write(f"- S(beta=1) range over A: [{S_land[ib1, :].min():.6f}, "
            f"{S_land[ib1, :].max():.6f}]\n")
    f.write(f"- max |dS| over A at beta=1: {np.abs(dS_dA).max():.6f} nats\n")
    f.write(f"- monotone in A at beta=1: {mono}\n")
    f.write(f"- old flux max (K fixed): {old_flux.max():.3e}; "
            f"new flux max (K_A): {flux_land.max():.3e}\n")
    f.write(f"- A=0 reduction ||.||_1: {float(la.norm(rho_m0 - rho_eq1, 1)):.3e}\n")
print(f"[done] notes -> {MD_PATH}")

# ===========================================================================
# 4. Plots.
# ===========================================================================
os.makedirs(OUT_DIR, exist_ok=True)
BB, TT = np.meshgrid(BETA_GRID, T_RATIOS, indexing="ij")

fig, ax = plt.subplots(figsize=(8, 6))
im = ax.pcolormesh(BB, TT, S_land, shading="auto")
fig.colorbar(im, ax=ax, label="S (nats)")
ax.set_xscale("log"); ax.set_yscale("log")
ax.set_xlabel("beta (global)")
ax.set_ylabel("fluctuation strength ||A1||/||D||")
ax.set_title("magnetophase entropy S(rho_{beta,A}) (T4)")
fig.tight_layout()
fig.savefig(os.path.join(OUT_DIR, "fig1_entropy_landscape.png"), dpi=120)
plt.close(fig)

fig, ax = plt.subplots(figsize=(8, 5))
for j in (0, 4, 9):
    ax.semilogx(BETA_GRID, S_land[:, j], "o-", ms=4,
                label=f"t_ratio={T_RATIOS[j]:.1e}")
ax.set_xlabel("beta"); ax.set_ylabel("S (nats)")
ax.set_title("entropy vs beta at fixed fluctuation: magnetic imprint")
ax.legend()
fig.tight_layout()
fig.savefig(os.path.join(OUT_DIR, "fig2_entropy_beta.png"), dpi=120)
plt.close(fig)

fig, ax = plt.subplots(figsize=(8, 5))
ax.loglog(T_RATIOS[1:], np.abs(S_land[ib1, 1:] - S_land[ib1, 0]), "o-")
ax.set_xlabel("fluctuation strength ||A1||/||D||")
ax.set_ylabel("|S(beta=1,A) - S(beta=1,0)| (nats)")
ax.set_title("magnetic imprint on entropy at beta=1 (T4)")
fig.tight_layout()
fig.savefig(os.path.join(OUT_DIR, "fig3_entropy_imprint.png"), dpi=120)
plt.close(fig)

fig, axes = plt.subplots(1, 2, figsize=(13, 5))
im0 = axes[0].pcolormesh(BB, TT, old_flux, shading="auto",
                         norm=matplotlib.colors.LogNorm())
fig.colorbar(im0, ax=axes[0], label="||phi||_F")
axes[0].set_xscale("log"); axes[0].set_yscale("log")
axes[0].set_title("OLD: K fixed (ruled surface)")
axes[1].pcolormesh(BB, TT, flux_land, shading="auto", cmap="Greys",
                   vmin=0, vmax=1)
axes[1].set_xscale("log"); axes[1].set_yscale("log")
axes[1].text(0.5, 0.5, "||phi_{beta,A}||_F = 0\nfor all (beta, A)\n(T1: proved no-go)",
             transform=axes[1].transAxes, ha="center", va="center", fontsize=11)
axes[1].set_title("NEW: K_A from D_A (identically zero)")
for ax in axes:
    ax.set_xlabel("beta (global)")
    ax.set_ylabel("fluctuation strength")
fig.suptitle("flux comparison: fixed-K vs magnetophase K_A (T4)")
fig.tight_layout()
fig.savefig(os.path.join(OUT_DIR, "fig4_flux_comparison.png"), dpi=120)
plt.close(fig)

print(f"[done] plots -> {OUT_DIR}")
