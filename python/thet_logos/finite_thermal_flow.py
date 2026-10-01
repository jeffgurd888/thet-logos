"""Finite thermal-flow probe (Tier T4 numerical).

Question: does the modular flow of the Gibbs state
    rho_beta = exp(-beta D_F^2) / Tr(exp(-beta D_F^2))
on the finite triple (A_F, H_F, D_F) respond differently across the
gauge sectors C / H / M_3(C)?

Setup notes (read before citing):
  * D_F = DF_oneGen with physical-ish 3rd-generation Yukawas, scaled by
    the electroweak vev v = 246 GeV so eigenvalues are in GeV.
  * Sectors are the REPRESENTED gauge Lie algebras pi(A_F): anti-Hermitian
    generators via common.pi (Option-A embedding, mirrors Lean).
    KNOWN EMBEDDING ARTIFACT: pi(0,0,color) = 0 in this embedding (color
    appears only in q*color / u1*color products), so the su(3) sector is
    the zero algebra here. Its zero response is an artifact, not physics.
  * Observable: g_i = || ad_{D_F^2} restricted to sector i ||, i.e. the
    largest singular value of X -> [D_F^2, X] over an HS-orthonormal basis
    of the sector's (represented) Lie algebra. Since K_beta = beta*D_F^2
    + const exactly, the modular speed at inverse temperature beta is
    beta * g_i -- the beta-scan collapses to one number per sector.
  * Controls: democratic Yukawas (all equal -> D_F^2 proportional to
    identity -> everything must vanish) and Yukawa shuffles (the su(2)
    response must track the (nu,e) doublet mass splitting, proving the
    signal is mass-splitting kinematics, not sector structure).

Verdict logic (per scope): KILL the finite version if sector responses
coincide up to scale, or if the only differentiation is fully explained
by mass splitting within one multiplet (degenerate-mass control kills it).
"""
import json
import numpy as np
import scipy.linalg as la

from .common import DF_oneGen, pi, quat_units, UJ, DIM

VEV = 246.0  # GeV -- electroweak vev; puts D_F eigenvalues in GeV
Y_PHYS = {"Ynu": 0.0, "Ye": 0.010, "Yu": 0.93, "Yd": 0.024}
SEED = 2026


# ---------------- D_F^2 ----------------

def build_H(Y):
    """D_F^2 in GeV^2 for Yukawa dict Y."""
    D = DF_oneGen(Y["Ynu"], Y["Ye"], Y["Yu"], Y["Yd"]) * VEV
    assert np.max(np.abs(D - D.conj().T)) < 1e-9, "D_F must be Hermitian"
    return D @ D


# ---------------- represented gauge Lie algebras ----------------

def sector_bases():
    """Anti-Hermitian bases of the represented gauge Lie algebras.

    Returns dict name -> (list_of_matrices, artifact_flag).
    """
    z2 = np.zeros((2, 2), complex)
    z3 = np.zeros((3, 3), complex)
    qu = quat_units()  # 1, i, j, k as 2x2 (i, j, k anti-Hermitian)
    u1 = [pi((1j, z2, z3))]                      # u(1): u = i
    su2 = [pi((0j, qu[1], z3)),                  # i*sigma3-type
           pi((0j, qu[2], z3)),                  # j
           pi((0j, qu[3], z3))]                  # k
    su3 = []
    for p in range(3):
        for q_ in range(3):
            for s in (1.0, 1j):
                E = np.zeros((3, 3), complex)
                E[p, q_] = s
                su3.append(pi((0j, z2, E)))
    su3_max = max(np.max(np.abs(M)) for M in su3)
    return {
        "u1": (u1, False),
        "su2": (su2, False),
        "su3": (su3, True),  # artifact: embedding kills M_3(C)
        "_su3_max_entry": su3_max,
    }


def orthonormalize(mats):
    """Gram-Schmidt under <A,B> = Tr(A^dagger B); drops null vectors."""
    out = []
    for M in mats:
        W = M.copy()
        for Q in out:
            W = W - np.trace(Q.conj().T @ W) * Q
        n = np.sqrt(np.trace(W.conj().T @ W).real)
        if n > 1e-12:
            out.append(W / n)
    return out


def sector_response(H, basis):
    """g = || ad_H |_sector || = top singular value of X -> [H, X].

    Returns 0.0 for the empty/zero sector.
    """
    B = orthonormalize(basis)
    if not B:
        return 0.0
    cols = [(H @ X - X @ H).reshape(-1) for X in B]
    M = np.stack(cols, axis=1)
    s = la.svdvals(M)
    return float(s[0]) if len(s) else 0.0


def all_responses(H):
    secs = sector_bases()
    su3_max = secs.pop("_su3_max_entry")
    out = {}
    for name, (basis, artifact) in secs.items():
        out[name] = {"g_GeV2": sector_response(H, basis),
                     "artifact": artifact}
    out["_su3_max_entry"] = su3_max
    return out


# ---------------- Gibbs state + modular flow sanity ----------------

def gibbs_K(H, beta):
    """Exact K_beta = beta*(H - w0) + ln Z (avoids logm underflow)."""
    w = la.eigvalsh(H)
    w0 = w[0]
    p = np.exp(-beta * (w - w0))
    Z = p.sum()
    return beta * (H - w0 * np.eye(DIM)) + np.log(Z) * np.eye(DIM), w


def sigma(K, s, A):
    F = la.expm(1j * s * K)
    Fi = la.expm(-1j * s * K)
    return F @ A @ Fi


def sanity_gibbs(H, beta):
    """Group property, stationarity, KMS for the Gibbs modular flow."""
    rng = np.random.default_rng(SEED)
    K, w = gibbs_K(H, beta)
    p = np.exp(-beta * (w - w[0]))
    rho = (np.eye(DIM) * (p / p.sum()))
    # rebuild rho in eigenbasis properly
    _, V = la.eigh(H)
    rho = (V * (p / p.sum())) @ V.conj().T
    A = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))
    B = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))
    s, t = 0.7, -1.3
    e_group = np.max(np.abs(sigma(K, s + t, A) - sigma(K, s, sigma(K, t, A))))
    e_stat = abs(np.trace(rho @ sigma(K, s, A)) - np.trace(rho @ A))
    # KMS: the generator is K_beta = beta*H + const, so the modular KMS
    # parameter is 1 (not beta): Tr(rho A sigma_{i}(B)) = Tr(rho B A),
    # i.e. sigma_i(B) = e^{-K} B e^{K} = e^{-beta H} B e^{beta H}.
    lhs = np.trace(rho @ A @ sigma(K, 1j * 1.0, B))
    rhs = np.trace(rho @ B @ A)
    e_kms = abs(lhs - rhs)
    return {"group": float(e_group), "stationarity": float(e_stat),
            "kms": float(e_kms)}


def verify_linearity(H, beta):
    """Check [K_beta, X] == beta [H, X] with K from the eigenvalue route."""
    rng = np.random.default_rng(SEED)
    K, _ = gibbs_K(H, beta)
    X = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))
    lhs = K @ X - X @ K
    rhs = beta * (H @ X - X @ H)
    return float(np.max(np.abs(lhs - rhs)))


# ---------------- controls ----------------

def democratic_Y():
    return {"Ynu": 0.3, "Ye": 0.3, "Yu": 0.3, "Yd": 0.3}


def shuffled_Y(seed):
    rng = np.random.default_rng(seed)
    vals = [Y_PHYS["Ynu"], Y_PHYS["Ye"], Y_PHYS["Yu"], Y_PHYS["Yd"]]
    rng.shuffle(vals)
    return dict(zip(["Ynu", "Ye", "Yu", "Yd"], vals))


# ---------------- driver ----------------

def run(beta_grid=None):
    if beta_grid is None:
        beta_grid = 1.0 / np.logspace(0, 4, 9)  # T = 1 .. 1e4 GeV
    H = build_H(Y_PHYS)
    w = la.eigvalsh(H)
    res = {"Yukawas": Y_PHYS, "VEV_GeV": VEV,
           "DF2_eigenvalues_GeV2": [float(x) for x in w],
           "physical": all_responses(H)}
    # linearity demonstration: speed(beta) = beta * g
    g_su2 = res["physical"]["su2"]["g_GeV2"]
    lin = []
    for beta in beta_grid:
        lin.append({"T_GeV": float(1.0 / beta),
                    "speed_su2_GeV": float(beta * g_su2)})
    res["beta_linearity"] = lin
    res["linearity_check_maxerr"] = verify_linearity(H, beta_grid[len(beta_grid)//2])
    res["gibbs_sanity"] = sanity_gibbs(H, beta_grid[-1])
    # controls
    res["control_democratic"] = all_responses(build_H(democratic_Y()))
    shuffles = []
    for sd in (11, 22, 33):
        Y = shuffled_Y(sd)
        r = all_responses(build_H(Y))
        # predicted su2 response = |Ynu^2 - Ye^2| v^2 (analytic, orthonormal basis)
        pred = abs(Y["Ynu"]**2 - Y["Ye"]**2) * VEV**2
        shuffles.append({"seed": sd, "Y": Y,
                         "su2_g": r["su2"]["g_GeV2"],
                         "su2_predicted": float(pred)})
    res["control_shuffles"] = shuffles
    return res


def main():
    res = run()
    p = res["physical"]
    print("=== Finite thermal-flow probe (T4) ===")
    print(f"D_F^2 eigenvalue range: {res['DF2_eigenvalues_GeV2'][0]:.4g} .. "
          f"{res['DF2_eigenvalues_GeV2'][-1]:.4g} GeV^2")
    for name in ("u1", "su2", "su3"):
        d = p[name]
        flag = " [EMBEDDING ARTIFACT: pi kills M_3(C)]" if d["artifact"] else ""
        print(f"  sector {name:4s}: g = {d['g_GeV2']:.6g} GeV^2{flag}")
    print(f"[check] su(3) max generator entry: "
          f"{res['physical']['_su3_max_entry']:.2e} "
          f"(0 => artifact confirmed)")
    print(f"[check] [K_beta,X]=beta[H,X] max err: "
          f"{res['linearity_check_maxerr']:.2e}")
    s = res["gibbs_sanity"]
    print(f"[check] Gibbs flow sanity: group {s['group']:.2e}, "
          f"stationarity {s['stationarity']:.2e}, KMS {s['kms']:.2e}")
    dc = res["control_democratic"]
    print(f"[control] democratic Yukawas: u1 {dc['u1']['g_GeV2']:.2e}, "
          f"su2 {dc['su2']['g_GeV2']:.2e}, su3 {dc['su3']['g_GeV2']:.2e}")
    for sh in res["control_shuffles"]:
        print(f"[control] shuffle seed {sh['seed']}: su2 g={sh['su2_g']:.6g}, "
              f"predicted |Ynu^2-Ye^2|v^2={sh['su2_predicted']:.6g}")
    with open("/home/hatch/workspace/thet-logos/whitepaper/"
              "finite-thermal-flow-probe/results.json", "w") as f:
        json.dump(res, f, indent=1)
    print("[done] results -> whitepaper/finite-thermal-flow-probe/results.json")
    return res


if __name__ == "__main__":
    main()
