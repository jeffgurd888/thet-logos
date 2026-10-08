#!/usr/bin/env python3
"""TRACK 4 — beta <-> A involutive symmetry test (T4 numerical).

Jeff's adjoint-primitives thesis (heat and magnetism as the two physical
primitives in thet) predicts a possible involutive symmetry exchanging the
beta (thermal) and A (gauge/magnetic) axes of the measured landscapes.

Data (seeds recorded in JSONs):
  - scripts/beta-flux-results.json            : ||phi(beta,A)||_F, 13x10 (active mode)
  - scripts/magnetophase-results.json         : S(beta,A) entropy, 13x10
  - scripts/non-gibbs-magnetophase-results.json : active flux vs (drive, A) at beta=1, 6x10

Normalized coordinates: u = normalized log10(beta) in [0,1] (13 pts),
v = normalized A-strength t/t_max in [0,1] (10 pts).

Tests:
  T1 strict: interpolate landscape onto a common NxN (u,v) grid, compare
     G(u,v) vs G(v,u); R = ||G - G^T||_F / ||G||_F (raw, min-max
     normalized, and log-scale variants).
  T2 separability: SVD rank-1 energy fraction (structure diagnosis).
  T3 weak form (monotone reparametrization, onto increasing warps
     phi, psi : [0,1] -> [0,1]):
       Theorem (corner condition): if M(u,v) = L(phi(u),psi(v)) satisfies
       M(u,v) = M(v,u), then M(0,1) = M(1,0) gives L(0,1) = L(1,0),
       because onto increasing warps fix corners: phi(0)=psi(0)=0,
       phi(1)=psi(1)=1. So L(0,1) != L(1,0) rigorously kills the weak form.
       (Without onto-ness one may zoom into any flat patch and the
       question is vacuous; we use the standard meaning of
       "reparametrization of the axis".)
       Additional structural kills:
       - separable L(u,v)=f(u)g(v): weak symmetry <=> log-profiles match
         under a monotone warp; a strictly monotone profile can never match
         a non-monotone one (monotone o monotone = monotone).
       - entropy plateau: {S = ln4} contains a rectangle [u*,1]x[0,1],
         u*>0; a symmetric M would force S(0,1)=ln4.

Writes: scripts/beta-A-symmetry-results.json (numbers).
The .md writeup is produced alongside (see script tail).
"""
import json
import math
import numpy as np
from scipy.interpolate import RegularGridInterpolator
from scipy.stats import spearmanr

SCR = "/home/hatch/workspace/thet-logos/scripts/"
N = 65  # common square grid resolution

# ---------------------------------------------------------------- load
d_flux = json.load(open(SCR + "beta-flux-results.json"))
d_ent = json.load(open(SCR + "magnetophase-results.json"))
d_ng = json.load(open(SCR + "non-gibbs-magnetophase-results.json"))

beta = np.array(d_flux["meta"]["beta_grid"])          # 13, log-spaced 0.1..10
t = np.array(d_flux["meta"]["t_ratios"])              # 10, A-strength 0..0.05
assert np.allclose(beta, d_ent["meta"]["beta_grid"])
assert np.allclose(t, d_ent["meta"]["t_ratios"])

u = (np.log10(beta) - np.log10(beta[0])) / (np.log10(beta[-1]) - np.log10(beta[0]))
v = (t - t[0]) / (t[-1] - t[0])

F = np.array(d_flux["modes"]["active"]["landscape"])          # 13x10 ||phi||
Feq = np.array(d_flux["modes"]["equilibrium"]["landscape"])   # 13x10 zeros
S = np.array(d_ent["entropy"]["landscape"])                   # 13x10 entropy
Fng = np.array(d_ng["flux_landscape"])                        # 6x10, (drive, A), beta=1
drive = np.array(d_ng["meta"]["drive_grid"])

res = {"meta": {"script": "scripts/beta_A_symmetry_test.py",
                "seeds": {"flux": [2026, 202607]},
                "N_common_grid": N,
                "coords": "u = normalized log10(beta), v = normalized A-strength t/t_max"}}


def strict_swap(L, name):
    it = RegularGridInterpolator((u, v), L, method="linear",
                                 bounds_error=False, fill_value=None)
    g1 = np.linspace(0, 1, N)
    UU, VV = np.meshgrid(g1, g1, indexing="ij")
    G = it(np.stack([UU.ravel(), VV.ravel()], axis=-1)).reshape(N, N)
    out = {}
    out["R_raw"] = float(np.linalg.norm(G - G.T) / np.linalg.norm(G))
    Gm = (G - G.min()) / (G.max() - G.min())
    out["R_minmax"] = float(np.linalg.norm(Gm - Gm.T) / np.linalg.norm(Gm))
    if np.all(G > 0):
        Gl = np.log(G)
        out["R_log"] = float(np.linalg.norm(Gl - Gl.T) / np.linalg.norm(Gl))
    # corner values on the raw grid (no interpolation)
    out["corners"] = {"L00": float(L[0, 0]), "L01": float(L[0, -1]),
                      "L10": float(L[-1, 0]), "L11": float(L[-1, -1])}
    out["corner_01_vs_10_absdiff"] = float(abs(L[0, -1] - L[-1, 0]))
    out["corner_01_vs_10_reldiff"] = float(abs(L[0, -1] - L[-1, 0])
                                          / max(abs(L[0, -1]), abs(L[-1, 0])))
    res[name] = out
    return G


def svd_rank1(L, name):
    s = np.linalg.svd(L, compute_uv=False)
    frac = float(s[0] ** 2 / np.sum(s ** 2))
    res[name + "_svd_rank1_frac"] = frac
    res[name + "_svd_spectrum"] = [float(x) for x in s]
    return frac


def profile_stats(L, name, x_beta, x_A):
    """1-D marginal profiles: beta-column at A=0, A-row at beta=1 (index 6)."""
    pb = L[:, 0]
    pa = L[6, :]
    d = {}
    d["beta_profile_spearman"] = float(spearmanr(x_beta, pb).statistic)
    d["A_profile_spearman"] = float(spearmanr(x_A, pa).statistic)
    db, da = np.diff(pb), np.diff(pa)
    d["beta_profile_critpts"] = int(np.sum(db[:-1] * db[1:] < 0))
    d["A_profile_critpts"] = int(np.sum(da[:-1] * da[1:] < 0))
    d["beta_profile_monotone"] = bool(np.all(db > 0) or np.all(db < 0))
    d["A_profile_monotone"] = bool(np.all(da > 0) or np.all(da < 0))
    d["A_profile_argmin"] = int(np.argmin(pa))
    d["A_profile_min_over_endpoints"] = float(pa.min() / max(pa[0], pa[-1]))
    d["A_profile_maxrise_vs_min"] = float((pa.max() - pa.min()) / pa.min())
    d["A_profile_range_over_max"] = float((pa.max() - pa.min()) / pa.max())
    res[name + "_profiles"] = d
    return d


# ---------------------------------------------------------------- T1 strict
Gf = strict_swap(F, "flux_strict")
Gs = strict_swap(S, "entropy_strict")
res["flux_equilibrium_note"] = ("equilibrium ||phi|| landscape is identically "
                                "zero (13x10 zeros): trivially swap-symmetric, "
                                "content-free; not a symmetry of the thesis.")

# ---------------------------------------------------------------- T2 separability
svd_rank1(F, "flux")
svd_rank1(S, "entropy")
svd_rank1(S - math.log(4.0), "entropy_minus_ln4")

# beta-linearity check of F: F[i,j]/beta[i] independent of i
ratio = F / beta[:, None]
res["flux_beta_linearity_maxreldev"] = float(
    np.abs(ratio - ratio[6:7, :]).max() / np.abs(ratio).max())

# ---------------------------------------------------------------- T3 profiles
profile_stats(F, "flux", beta, t)
profile_stats(S, "entropy", beta, t)

# entropy plateau: rows beta>=6.812920690579611 (idx 11..12) == ln4 to 16 digits?
plateau = S[11:, :]
pdev = float(np.abs(plateau - math.log(4.0)).max())
res["entropy_plateau"] = {
    "rows": "beta_idx 11..12 (beta >= 6.8129)",
    "max_abs_dev_from_ln4": pdev,
    "numerically_exact_ln4": bool(pdev == 0.0),
    "u_star": float(u[11]),
    "note": "rows 9..10 within 1e-7/1e-11 of ln4 (exponential suppression "
            "tail); rows 11..12 equal ln4 to all 16 printed digits over the "
            "full A range: rectangular flat region [u*,1]x[0,1], u*>0.",
}
res["entropy_corners_for_weakform"] = {
    "S(beta_min=0.1, A_max=0.05)": float(S[0, -1]),
    "S(beta_max=10, A_min=0)": float(S[-1, 0]),
    "ln4": math.log(4.0),
}
res["flux_corners_for_weakform"] = {
    "F(beta_min=0.1, A_max=0.05)": float(F[0, -1]),
    "F(beta_max=10, A_min=0)": float(F[-1, 0]),
}

# ---------------------------------------------------------------- non-Gibbs corroboration (beta=1 fixed -> no swap test)
row = Fng[3, :]                      # drive = 0.35
ratio_ng = row / row[0]
d = np.diff(ratio_ng)
res["nongibbs_active_drive035"] = {
    "A_ratio": [float(x) for x in ratio_ng],
    "peak_ratio": float(ratio_ng.max()),
    "argmax": int(np.argmax(ratio_ng)),
    "A_profile_monotone": bool(np.all(d > 0) or np.all(d < 0)),
    "A_profile_critpts": int(np.sum(d[:-1] * d[1:] < 0)),
    "note": "beta fixed at 1: no beta axis, swap test N/A; used as independent "
            "check of the A-profile shape (non-monotone modulation vs "
            "monotone beta-scaling).",
}

json.dump(res, open(SCR + "beta-A-symmetry-results.json", "w"), indent=2)

# ---------------------------------------------------------------- console summary
for k in ["flux_strict", "entropy_strict"]:
    r = res[k]
    print(f"{k}: R_raw={r['R_raw']:.4f} R_minmax={r['R_minmax']:.4f} "
          f"R_log={r.get('R_log', float('nan')):.4f} "
          f"|L01-L10|_rel={r['corner_01_vs_10_reldiff']:.4f}")
print("rank1 frac: flux=%.6f entropy=%.6f entropy-ln4=%.6f" % (
    res["flux_svd_rank1_frac"], res["entropy_svd_rank1_frac"],
    res["entropy_minus_ln4_svd_rank1_frac"]))
print("flux beta-linearity max rel dev:", res["flux_beta_linearity_maxreldev"])
print("flux profiles:", json.dumps(res["flux_profiles"], indent=1))
print("entropy profiles:", json.dumps(res["entropy_profiles"], indent=1))
print("plateau:", json.dumps(res["entropy_plateau"]))
print("nongibbs:", json.dumps(res["nongibbs_active_drive035"]))
