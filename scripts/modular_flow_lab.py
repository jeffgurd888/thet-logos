"""MODULAR FLOW LABORATORY — numerical track of the "play offense" program.

Evolve the modular flow and watch what it does to the finite spectral triple.

Tier T4 NUMERICAL EXPLORATION. Nothing here is a theorem. The Lean side
(ModularTime.lean, ActiveFlux.lean) proves: modularFlux_selfAdjoint,
eigenvalue_rigidity (<v|phi|v> = 0 in D-eigenstates), thermal_flux_vanishes
(equilibrium -> no flow), exists_activeDriver (non-equilibrium -> driver).
This script CHECKS those numerically and then watches the flow move.

Conventions (mirror the codebase exactly):
  D_F  = DF_oneGen(Y_PHYS) * VEV          (32x32 Hermitian; engine13_rsd.build_DF)
  rho  = state (32x32, full-rank, trace 1)
  K    = -log(rho), hermitized            (synthesized modular Hamiltonian)
  phi  = i * [K, D]                       (Lean: modularFlux K D = i . (K*D - D*K))
  sigma_s(A) = e^{isK} A e^{-isK}         (modular_flow.py / engine13_rsd.sigma_flow)

Playable parameters are ALL at the top. Change them and re-run.

What the instrument shows (honest preview):
  * Fixed-K flow is EXACTLY isospectral: spec(sigma_s(D)) = spec(D).
    Flat spectrum lines are the CORRECT result (eigenvalue_rigidity, T1),
    not a null result.
  * What MOVES: eigenspaces rotate, [D_s, a] norms vary, Connes distances
    deform. The geometry flows while the spectrum stands still.
  * No Lorentz-boost signature is observed or claimed. The finite flow is a
    compact unitary orbit (periodic/quasi-periodic), not a boost. A BW-type
    claim would need the Lorentzian/twisted extension (Rung 1), which does
    not exist yet. The what-if track is labeled speculation.
"""

import os
import sys

import numpy as np
import scipy.linalg as la

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

# make thet_logos importable whether run from repo root or scripts/
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "python"))
from thet_logos.engine13_rsd import (
    build_DF, selfadjoint_basis, commutator_data, ket, connes_distance,
    thermal_state, opnorm,
)

# ===========================================================================
# PLAYABLE PARAMETERS — change these and re-run.
# ===========================================================================
SEED       = 2026    # rng seed (reproducibility)
DIM        = 32      # Hilbert space dimension (fixed by the triple)
S_MAX      = 2.0     # flow parameter range: s in [-S_MAX, S_MAX]
N_S        = 41      # flow grid resolution
MODE       = "active"  # "active" | "equilibrium" | "tracial"
BETA       = 1.0     # equilibrium: rho = exp(-BETA * D^2)/Z  ([K,D] = 0)
PERTURB    = 0.35    # active: rho ~ normalize(exp(-BETA D^2) + PERTURB*random)
RUN_WHATIF = True    # driven-K exploratory track (SPECULATIVE, beyond Lean)
V_STRENGTH = 0.6     # what-if driver strength: K(s) = K + s * V
N_CONNES   = 11      # Connes-distance samples along the flow (coarse grid)
OUT_DIR    = os.path.join(os.path.dirname(__file__), "..", "whitepaper",
                          "figs", "modular-flow-lab")

rng = np.random.default_rng(SEED)

# ===========================================================================
# 1. Build the triple, the state, K, and phi.
# ===========================================================================
D = build_DF()
evals_D, vecs_D = la.eigh(D)

if MODE == "tracial":
    rho = np.eye(DIM, dtype=complex) / DIM
elif MODE == "equilibrium":
    rho = thermal_state(D @ D, BETA)          # function of D^2 -> [K, D] = 0
elif MODE == "active":
    rho0 = thermal_state(D @ D, BETA)
    X = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))
    R = X @ X.conj().T
    R = R / np.trace(R).real
    rho = rho0 + PERTURB * R
    rho = (rho + rho.conj().T) / 2
    rho = rho / np.trace(rho).real
    # project back to full-rank positive (perturbation can break positivity)
    w, V = la.eigh(rho)
    w = np.clip(w, 1e-10, None)
    w = w / w.sum()
    rho = (V * w) @ V.conj().T
else:
    raise ValueError(f"unknown MODE {MODE}")

# K = -ln rho, hermitized (modular_flow.py convention)
K = -la.logm(rho)
K = (K + K.conj().T) / 2.0

# phi = i [K, D]  (Lean: modularFlux K D)
phi = 1j * (K @ D - D @ K)

print(f"=== Modular Flow Lab  (mode={MODE}, S_MAX={S_MAX}, N_S={N_S}) ===")

# ===========================================================================
# 2. Sanity checks (each prints its error).
# ===========================================================================
e_herm = float(np.max(np.abs(phi - phi.conj().T)))
print(f"[check] phi Hermitian err:              {e_herm:.3e}")

# eigenvalue_rigidity (T1): <v_j|phi|v_j> = 0 for D-eigenstates
rig = np.array([abs(vecs_D[:, j].conj() @ (phi @ vecs_D[:, j]))
                for j in range(DIM)])
print(f"[check] eigenvalue_rigidity max|<v|phi|v>|: {rig.max():.3e}")

# thermal_flux_vanishes analog: equilibrium/tracial -> phi ~= 0
phi_norm = float(la.norm(phi, "fro"))
print(f"[check] ||phi||_F = {phi_norm:.3e} "
      f"{'(expect ~0: equilibrium)' if MODE != 'active' else '(expect >0: active driver)'}")

# KMS spot check (modular_flow.py convention, beta = 1)
A = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))
B = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))
Fk = la.expm(1j * (1j * 1.0) * K)     # sigma_{i}(B): s = i
Fki = la.expm(-1j * (1j * 1.0) * K)
e_kms = abs(np.trace(rho @ A @ (Fk @ B @ Fki)) - np.trace(rho @ B @ A))
print(f"[check] KMS (beta=1) err:               {e_kms:.3e}")

# ===========================================================================
# 3. Fixed-K flow: D_s = sigma_s(D), s in grid.
# ===========================================================================
s_grid = np.linspace(-S_MAX, S_MAX, N_S)
evals_D0 = la.eigvalsh(D)

spec_drift = np.zeros(N_S)      # max_j |lam_j(s) - lam_j(0)|  (expect ~0)
sub_ang_max = np.zeros(N_S)     # largest principal angle of positive subspace
sub_ang_mean = np.zeros(N_S)
comm_norms = []                 # ||[D_s, a_k]|| for sample algebra elements
Hbasis = selfadjoint_basis()
a_idx = list(range(min(3, len(Hbasis))))
a_mats = [Hbasis[k] for k in a_idx]

pos0 = vecs_D[:, evals_D > 0]   # positive-energy subspace basis (gauge-fixed)

for i, s in enumerate(s_grid):
    F = la.expm(1j * s * K)
    Fi = la.expm(-1j * s * K)
    Ds = F @ D @ Fi
    ev = la.eigvalsh(Ds)
    spec_drift[i] = float(np.max(np.abs(ev - evals_D0)))
    # principal angles between positive subspaces: cosines = svd(V0^dagger Vs)
    _, vecs_s = la.eigh(Ds)
    poss = vecs_s[:, ev > 0]
    c = la.svdvals(pos0.conj().T @ poss)
    c = np.clip(c, -1.0, 1.0)
    ang = np.arccos(c)
    sub_ang_max[i] = float(ang.max())
    sub_ang_mean[i] = float(ang.mean())
    comm_norms.append([float(opnorm(Ds @ a - a @ Ds)) for a in a_mats])
comm_norms = np.array(comm_norms)

print(f"[flow] max spectrum drift over grid:   {spec_drift.max():.3e} (expect ~1e-12: isospectral)")
print(f"[flow] max subspace rotation (rad):   {sub_ang_max.max():.4f}")
print(f"[flow] commutator-norm variation:     "
      f"{[(comm_norms[:, k].max() - comm_norms[:, k].min()) for k in range(len(a_idx))]}")

# Connes distances along the flow (coarse grid). Fixed probe set; at each s,
# record the mean over finite-nonzero pairs (pairs that go kernel-separated
# are counted, not averaged). Shows the metric deforming under the flow.
probes = [ket(i) for i in range(8)] + [thermal_state(D @ D, 0.01)]
connes_idx = np.linspace(0, N_S - 1, N_CONNES, dtype=int)
connes_ss, connes_mean, connes_ninf = [], [], []
for i in connes_idx:
    s = s_grid[i]
    F = la.expm(1j * s * K)
    Ds = F @ D @ F.conj().T
    Ql, Kl = commutator_data(Ds, Hbasis)
    finite, ninf = [], 0
    for a in range(len(probes)):
        for b in range(a + 1, len(probes)):
            d, info = connes_distance(Ds, Hbasis, Ql, Kl, probes[a], probes[b], rng)
            if np.isinf(d):
                ninf += 1
            elif d > 1e-9:
                finite.append(d)
    connes_ss.append(s)
    connes_mean.append(float(np.mean(finite)) if finite else float("nan"))
    connes_ninf.append(ninf)
connes_ss = np.array(connes_ss); connes_mean = np.array(connes_mean)
print(f"[flow] Connes mean finite-nonzero distance: "
      f"{np.nanmin(connes_mean):.4f} .. {np.nanmax(connes_mean):.4f} "
      f"(varies => metric deforms); kernel-separated pairs per s: {connes_ninf}")

# ===========================================================================
# 4. What-if track (SPECULATIVE): deform D along the flux direction itself,
#    D(t) = D + t * phi_hat, phi_hat = phi / ||phi||_op.
#    This is NOT unitary conjugation, so eigenvalues CAN move — but the
#    proved eigenvalue_rigidity (<v|phi|v> = 0) predicts the drift is
#    SECOND-order in t (no linear term). We check exactly that.
#    Beyond the Lean construction; exploratory T4.
# ===========================================================================
whatif_drift = None
if RUN_WHATIF:
    phi_op = float(opnorm(phi))
    phi_hat = phi / phi_op
    t_max = 0.1 * float(opnorm(D)) / phi_op
    t_grid = np.linspace(-t_max, t_max, 81)
    whatif_evals = np.array([la.eigvalsh(D + t * phi_hat) for t in t_grid])
    whatif_drift = np.max(np.abs(whatif_evals - whatif_evals[40]), axis=1)
    # quadratic-onset check: drift(t)/t^2 should be ~constant for small t
    small = (np.abs(t_grid) > 0) & (np.abs(t_grid) < 0.3 * t_max)
    quad = whatif_drift[small] / t_grid[small] ** 2
    print(f"[whatif] SPECULATIVE flux-direction deformation D + t*phi_hat:")
    print(f"         max drift = {whatif_drift.max():.3e} at t_max={t_max:.3e}")
    print(f"         drift/t^2 in small-t window: min={quad.min():.3e} "
          f"max={quad.max():.3e} (flat => second-order onset, rigidity holds)")

# ===========================================================================
# 5. Plots.
# ===========================================================================
os.makedirs(OUT_DIR, exist_ok=True)

# need full eigenvalue trajectories for fig 1
eig_traj = np.zeros((N_S, DIM))
for i, s in enumerate(s_grid):
    F = la.expm(1j * s * K)
    eig_traj[i] = la.eigvalsh(F @ D @ F.conj().T)

fig, ax = plt.subplots(figsize=(8, 4.5))
for j in range(DIM):
    ax.plot(s_grid, eig_traj[:, j], lw=0.7, alpha=0.8)
ax.set_xlabel("flow parameter s")
ax.set_ylabel("eigenvalue of D_s = sigma_s(D)")
ax.set_title(f"spectrum under modular flow (mode={MODE}) — flat = rigidity (T1)")
fig.tight_layout()
fig.savefig(os.path.join(OUT_DIR, "fig1_spectrum_rigidity.png"), dpi=120)
plt.close(fig)

fig, ax = plt.subplots(figsize=(8, 4.5))
ax.semilogy(s_grid, np.maximum(spec_drift, 1e-16), label="max |lam(s)-lam(0)|")
ax.set_xlabel("flow parameter s")
ax.set_ylabel("max eigenvalue drift (log)")
ax.set_title("isospectrality check: drift at machine precision")
ax.legend()
fig.tight_layout()
fig.savefig(os.path.join(OUT_DIR, "fig1b_drift_log.png"), dpi=120)
plt.close(fig)

fig, ax = plt.subplots(figsize=(8, 4.5))
ax.plot(s_grid, sub_ang_max, label="max principal angle")
ax.plot(s_grid, sub_ang_mean, label="mean principal angle")
ax.set_xlabel("flow parameter s")
ax.set_ylabel("angle (rad)")
ax.set_title("positive-energy eigenspace rotation under the flow")
ax.legend()
fig.tight_layout()
fig.savefig(os.path.join(OUT_DIR, "fig2_eigenspace_rotation.png"), dpi=120)
plt.close(fig)

fig, ax = plt.subplots(figsize=(8, 4.5))
for k in range(len(a_idx)):
    ax.plot(s_grid, comm_norms[:, k], label=f"||[D_s, a_{a_idx[k]}]||")
ax.set_xlabel("flow parameter s")
ax.set_ylabel("operator norm")
ax.set_title("commutator norms deform along the flow (Connes metric moves)")
ax.legend()
fig.tight_layout()
fig.savefig(os.path.join(OUT_DIR, "fig3_commutator_norms.png"), dpi=120)
plt.close(fig)

fig, ax = plt.subplots(figsize=(8, 4.5))
ax.plot(connes_ss, connes_mean, "o-")
ax.set_xlabel("flow parameter s")
ax.set_ylabel("mean finite-nonzero Connes distance")
ax.set_title("spectral metric deforms under modular flow")
fig.tight_layout()
fig.savefig(os.path.join(OUT_DIR, "fig4_connes_distance.png"), dpi=120)
plt.close(fig)

if RUN_WHATIF:
    fig, ax = plt.subplots(figsize=(8, 4.5))
    for j in range(DIM):
        ax.plot(t_grid, whatif_evals[:, j], lw=0.7, alpha=0.8)
    ax.set_xlabel("deformation parameter t")
    ax.set_ylabel("eigenvalue of D + t*phi_hat")
    ax.set_title("WHAT-IF (speculative): flux-direction deformation — 2nd-order drift")
    fig.tight_layout()
    fig.savefig(os.path.join(OUT_DIR, "fig5_whatif_drift.png"), dpi=120)
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(8, 4.5))
    nz = t_grid != 0
    ax.loglog(np.abs(t_grid[nz]), np.maximum(whatif_drift[nz], 1e-18), "o-", ms=3)
    # reference slopes
    tt = np.abs(t_grid[nz])
    ax.loglog(tt, (tt / tt.max()) ** 2 * whatif_drift[nz].max(), "k--", lw=1,
              label="slope 2 (quadratic)")
    ax.loglog(tt, (tt / tt.max()) * whatif_drift[nz].max(), "r--", lw=1,
              label="slope 1 (linear, ruled out)")
    ax.set_xlabel("|t| (log)")
    ax.set_ylabel("max eigenvalue drift (log)")
    ax.set_title("drift onset: quadratic, not linear (rigidity holds)")
    ax.legend()
    fig.tight_layout()
    fig.savefig(os.path.join(OUT_DIR, "fig5b_whatif_quadratic.png"), dpi=120)
    plt.close(fig)

print(f"[done] plots in {OUT_DIR}")
