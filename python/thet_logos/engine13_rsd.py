"""Engine 13 — Relational Spectral Dynamics: Finite Spectral-to-Spacetime Emergence.

Tier T4 numerical probe. LOCAL. Commissioned 2026-10-01 (Jeff: GO).

Three deliverables, each ending in an explicit PASS/FAIL:
  E13-A  Connes spectral distance on the finite triple + stability under
         inner-fluctuation-type perturbations.
  E13-B  Heat-kernel spectral-dimension CONTROL (finite D_F => d_spec -> 0;
         never read as emergence).
  E13-C  Modular-flow inventory over admissible states (no clock-time
         identification anywhere).

QUARANTINE WALL (binding): this module does not attempt, claim, or smuggle
finite->continuum passage, d_spec->4, modular-parameter->clock-time,
Lorentzian GR recovery, or experimental prediction.

Conventions (mirror the codebase):
  D_F  = DF_oneGen(Y_PHYS) * VEV  (32x32 Hermitian; same Dirac as
         finite_thermal_flow.build_H, whose D_F^2 == D_F @ D_F)
  A_F  = C (+) H (+) M_3(C) via common.af_generators / common.pi (Option-A:
         represented on the first 16-sector, zero elsewhere)
  J    via common.UJ  (J M J^-1 = UJ @ M.conj() @ UJ.T)
"""

import numpy as np
import scipy.linalg as la
from scipy.optimize import minimize

from .common import DF_oneGen, af_generators, pi, random_af, UJ
from .finite_thermal_flow import Y_PHYS, VEV, orthonormalize

SEED = 2026
DIM = 32
KER_TOL_REL = 1e-8      # singular-value cutoff for ker[D, .]
KER_PROJ_TOL = 1e-6     # tolerance for "c has no kernel component"
ZERO_DIST_TOL = 1e-9    # below this, a distance counts as 0


# --------------------------------------------------------------------------
# shared ground
# --------------------------------------------------------------------------

def build_DF():
    """The finite Dirac: DF_oneGen with physical-ish Yukawas, scaled by VEV."""
    D = DF_oneGen(Y_PHYS["Ynu"], Y_PHYS["Ye"], Y_PHYS["Yu"], Y_PHYS["Yd"]) * VEV
    assert np.max(np.abs(D - D.conj().T)) < 1e-12, "D_F must be Hermitian"
    return D


def selfadjoint_basis():
    """Orthonormal real basis of the self-adjoint part of pi(A_F).

    Takes Hermitian parts of the 24 represented real generators and
    orthonormalizes under Tr(A^dagger B). Returns list of (32,32) Hermitian.
    """
    Hs = []
    for g in af_generators():
        P = pi(g)
        H = (P + P.conj().T) / 2.0
        if np.linalg.norm(H) > 1e-12:
            Hs.append(H)
    B = orthonormalize(Hs)
    for H in B:
        assert np.max(np.abs(H - H.conj().T)) < 1e-12
    return B


def opnorm(M):
    return float(la.svdvals(M)[0])


def commutator_data(D, Hbasis):
    """Real-linear map x -> [D, A(x)], A(x) = sum_k x_k H_k.

    Returns (Q, K): Q = (m, r) orthonormal basis of (ker)^perp in coefficient
    space; K = (m, nker) orthonormal basis of ker. The Connes constraint
    ||[D, A(x)]|| <= 1 is a norm exactly on span(Q).
    """
    m = len(Hbasis)
    cols = []
    for H in Hbasis:
        C = (D @ H - H @ D).reshape(-1)
        cols.append(np.concatenate([C.real, C.imag]))
    M = np.stack(cols, axis=1)  # (2*1024, m), real
    U, s, Vt = la.svd(M, full_matrices=False)
    keep = s >= KER_TOL_REL * s[0]
    Q = Vt[keep].T.copy()
    K = Vt[~keep].T.copy()
    return Q, K


def ket(i):
    v = np.zeros(DIM, complex)
    v[i] = 1.0
    return np.outer(v, v.conj())


def thermal_state(H, beta):
    evals = la.eigvalsh(H)
    w = np.exp(-beta * (evals - evals[0]))
    Z = np.sum(w)
    # rebuild in eigenbasis
    _, vecs = la.eigh(H)
    return (vecs * w) @ vecs.conj().T / Z


def random_state(rng):
    X = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))
    rho = X @ X.conj().T
    return rho / np.trace(rho).real


# --------------------------------------------------------------------------
# E13-A : Connes spectral distance
# --------------------------------------------------------------------------

def connes_distance(D, Hbasis, Q, K, rho1, rho2, rng, n_starts=7,
                    n_dir=800):
    """d_D(w1, w2) = sup{|(w1-w2)(a)| : ||[D,a]|| <= 1}.

    Returns (dist, info). dist = np.inf diagnoses a kernel-separated
    (disconnected) pair. Method: exact closed form when the commutator-kernel
    quotient is 1-dimensional (|cQ| / ||[D, A(e)]||); multi-start COBYLA on the
    kernel quotient with exact-boundary random-direction cross-check otherwise.
    """
    Delta = rho1 - rho2
    c = np.array([np.trace(Delta @ H).real for H in Hbasis])
    info = {}
    if K.shape[1] > 0:
        kcomp = float(np.linalg.norm(K.T @ c))
        info["kernel_component"] = kcomp
        if kcomp > KER_PROJ_TOL * max(1.0, float(np.linalg.norm(c))):
            return np.inf, info  # disconnected: sup is infinite
    cQ = Q.T @ c
    if float(np.linalg.norm(cQ)) < ZERO_DIST_TOL:
        return 0.0, info

    r = Q.shape[1]

    def Avec(y):
        x = Q @ y
        A = np.zeros((DIM, DIM), complex)
        for k, H in enumerate(Hbasis):
            A += x[k] * H
        return A

    def opnorm_comm(y):
        A = Avec(y)
        return opnorm(D @ A - A @ D)

    # r == 1 (the case for the Option-A represented triple): closed form.
    # Feasible set is the interval |y| <= 1/n0, n0 = ||[D, A(e1)]||, so
    # sup = |cQ| / n0 exactly. No optimizer needed; the random-direction
    # cross-check below then agrees by construction.
    if r == 1:
        n0 = opnorm_comm(np.ones(1))
        assert n0 > 1e-300, "quotient direction has zero commutator norm"
        d = float(abs(cQ[0]) / n0)
        info["closed_form"] = d
        info["xcheck_gap"] = 0.0
        return d, info

    def neg_obj(y):
        return float(-(cQ @ y))

    def feas(y):
        A = Avec(y)
        return 1.0 - opnorm(D @ A - A @ D)

    best = 0.0
    starts = [np.zeros(r)] + [0.5 * rng.standard_normal(r)
                              for _ in range(n_starts - 1)]
    for y0 in starts:
        res = minimize(neg_obj, y0, method="COBYLA",
                       constraints={"type": "ineq", "fun": feas},
                       options={"maxiter": 1500, "tol": 1e-9})
        if res.success and feas(res.x) >= -1e-7:
            best = max(best, -float(res.fun))
    info["cobyla"] = best

    # falsification cross-check: exact boundary values along random directions
    rb = 0.0
    for _ in range(n_dir):
        u = rng.standard_normal(r)
        u /= np.linalg.norm(u)
        A = Avec(u)
        nrm = opnorm(D @ A - A @ D)
        if nrm < 1e-300:
            continue
        rb = max(rb, float(cQ @ u) / nrm)
    info["random_dir"] = rb
    gap = rb - best
    info["xcheck_gap"] = gap
    # honest lower bound on the true sup: the max of both attacks
    return max(best, rb), info


def inner_fluctuation_perturbation(D, rng, eps=0.05, nterms=3):
    """Self-adjoint inner-fluctuation-type perturbation.

    delta = symmetrize( sum_k pi(x_k)[D, pi(y_k)] + J-conjugate ), scaled to
    ||delta|| <= eps * ||D||. One-form-flavored; documented as a perturbation
    of inner-fluctuation type, not the exact gauge fluctuation.
    """
    A = np.zeros((DIM, DIM), complex)
    for _ in range(nterms):
        x = pi(random_af(rng))
        y = pi(random_af(rng))
        A = A + x @ (D @ y - y @ D)
    U = UJ()
    JAJ = U @ A.conj() @ U.T
    pert = A + JAJ
    pert = (pert + pert.conj().T) / 2.0
    nrm = opnorm(pert)
    pert = pert * (eps * opnorm(D) / max(nrm, 1e-300))
    assert opnorm(pert) <= eps * opnorm(D) * (1 + 1e-9)
    return D + pert


def e13a(rng):
    lines = []
    D = build_DF()
    Hbasis = selfadjoint_basis()
    lines.append(f"[E13-A] D_F {D.shape}, ||D||={opnorm(D):.4g} GeV; "
                 f"self-adjoint represented-algebra basis dim m={len(Hbasis)} "
                 f"(Option-A embedding kills the M3(C) summand: documented "
                 f"artifact, cf. finite_thermal_flow sector_bases)")
    Q, K = commutator_data(D, Hbasis)
    lines.append(f"[E13-A] ker[D,.] real-dim = {K.shape[1]} "
                 f"(quotient dim r={Q.shape[1]}: the finite spectral geometry "
                 f"is {Q.shape[1]}-dimensional + disconnected components)")

    H = D @ D
    states = {}
    for i in range(8):
        states[f"pure{i}"] = ket(i)

    # Constructive same-kernel-class pair: the represented self-adjoint
    # algebra is 2-dim and both basis elements are diagonal, so scan the
    # active-sector diagonal for p,q with (O_v)_pp = (O_v)_qq (same kernel
    # class -> finite distance) but (O_q)_pp != (O_q)_qq (nonzero distance).
    # Without this, a generic sample lands only on 0/inf pairs.
    def A_of(x):
        A = np.zeros((DIM, DIM), complex)
        for k, Hh in enumerate(Hbasis):
            A += x[k] * Hh
        return A
    Ov = A_of(K[:, 0])
    Oq = A_of(Q[:, 0])
    dv = np.diag(Ov).real[:16]
    dq = np.diag(Oq).real[:16]
    pair = None
    for p in range(16):
        for q in range(p + 1, 16):
            if abs(dv[p] - dv[q]) < 1e-12 and abs(dq[p] - dq[q]) > 1e-9:
                pair = (p, q)
                break
        if pair:
            break
    assert pair is not None, "no same-class distinguishable pair exists"
    states["pureP"] = ket(pair[0])
    states["pureQ"] = ket(pair[1])
    lines.append(f"[E13-A] same-kernel-class pair: indices {pair} "
                 f"(dO_v={abs(dv[pair[0]]-dv[pair[1]]):.1e}, "
                 f"dO_q={abs(dq[pair[0]]-dq[pair[1]]):.3g})")
    states["pure_dead"] = ket(20)          # dead-sector probe -> expect inf
    states["thermal_b0.01"] = thermal_state(H, 0.01)
    states["thermal_b1.0"] = thermal_state(H, 1.0)
    ma = np.zeros((DIM, DIM), complex)
    ma[:16, :16] = np.eye(16) / 16.0
    states["mixed_active"] = ma
    states["random"] = random_state(rng)
    names = list(states.keys())
    n = len(names)

    dist = np.zeros((n, n))
    xgaps = []
    for i in range(n):
        for j in range(i + 1, n):
            d, info = connes_distance(D, Hbasis, Q, K, states[names[i]],
                                      states[names[j]], rng)
            dist[i, j] = dist[j, i] = d
            xgaps.append(info.get("xcheck_gap", 0.0))
    finite = dist[np.isfinite(dist) & (dist > ZERO_DIST_TOL)]
    ninf = int(np.sum(np.isinf(dist)) // 2)
    lines.append(f"[E13-A] pairs: {n*(n-1)//2}, finite-nonzero: "
                 f"{finite.size}, inf: {ninf}")
    assert ninf > 0, "expected at least one kernel-separated (inf) pair"
    assert finite.size > 0, "no finite nonzero distances: H20-critical"
    lines.append(f"[E13-A] finite distance range: "
                 f"{finite.min():.4g} .. {finite.max():.4g} GeV^-1")
    lines.append(f"[E13-A] optimizer x-check max gap (random-cobyla): "
                 f"{max(xgaps):.3g}")

    # triangle-inequality audit (optimizer sanity) over sampled triples
    worst = 0.0
    rng2 = np.random.default_rng(SEED + 1)
    idx = [i for i in range(n)]
    for _ in range(300):
        a, b, cc = rng2.choice(idx, 3, replace=False)
        dab, dbc, dac = dist[a, b], dist[b, cc], dist[a, cc]
        if np.isfinite(dab) and np.isfinite(dbc) and np.isfinite(dac):
            viol = dac - (dab + dbc)
            worst = max(worst, viol / (1.0 + dab + dbc))
    lines.append(f"[E13-A] triangle audit worst relative violation: "
                 f"{worst:.3g}")
    assert worst < 1e-3, "triangle violation: optimizer suspect"

    # stability under inner-fluctuation-type perturbation
    D2 = inner_fluctuation_perturbation(D, rng)
    Q2, K2 = commutator_data(D2, Hbasis)
    maxrel = 0.0
    flips = 0
    dmax = finite.max()
    for i in range(n):
        for j in range(i + 1, n):
            d, _ = connes_distance(D2, Hbasis, Q2, K2, states[names[i]],
                                   states[names[j]], rng)
            d0 = dist[i, j]
            if np.isinf(d0) != np.isinf(d):
                flips += 1
            elif np.isfinite(d0) and d0 > ZERO_DIST_TOL:
                maxrel = max(maxrel, abs(d - d0) / d0)
            elif np.isfinite(d0):
                maxrel = max(maxrel, abs(d - d0) / max(dmax, 1e-300))
    lines.append(f"[E13-A] fluctuation eps=0.05: finiteness flips={flips}, "
                 f"max relative distance change={maxrel:.3g}")
    ok = (flips == 0) and (maxrel < 1.0)
    verdict = "PASS" if ok else "FAIL"
    lines.append(f"[E13-A] {verdict}: nontrivial finite distances exist; "
                 f"stable under inner-fluctuation-type perturbation "
                 f"(flips={flips}, maxrel={maxrel:.3g} < 1.0)")
    return verdict, lines


# --------------------------------------------------------------------------
# E13-B : spectral-dimension control
# --------------------------------------------------------------------------

def e13b():
    lines = []
    D = build_DF()
    H = D @ D
    evals = la.eigvalsh(H)  # keep ALL eigenvalues incl. exact zeros:
    # K(t) -> (# zero modes) as t -> oo, so d_spec -> 0 in the IR.
    # (Filtering zeros made K underflow to 0 -- that was a bug, now fixed.)
    n_zero = int(np.sum(evals <= 1e-12))
    lines.append(f"[E13-B] D_F^2 eigenvalues: {len(evals)} total, {n_zero} "
                 f"exact-zero modes, nonzero range "
                 f"{evals[evals > 1e-12][0]:.4g}..{evals[-1]:.4g} GeV^2")
    ts = np.logspace(-8, 8, 600)
    K = np.array([np.sum(np.exp(-t * evals)) for t in ts])
    valid = K > 1e-290
    assert np.sum(valid) > 50, "heat trace underflowed everywhere: check units"
    lt, lK = np.log(ts[valid]), np.log(K[valid])
    dspec = -2.0 * np.gradient(lK, lt)
    lines.append(f"[E13-B] d_spec UV end (t={ts[valid][0]:.0e}): "
                 f"{dspec[0]:.4f}  |  IR end (t={ts[valid][-1]:.0e}): "
                 f"{dspec[-1]:.4f}")
    imax = int(np.argmax(dspec))
    lines.append(f"[E13-B] max transient: d_spec={dspec[imax]:.3f} at "
                 f"t={ts[valid][imax]:.2e} (log-derivative underflow "
                 f"artifact -- recorded, not interpreted)")
    ok_uv = dspec[0] < 0.5
    ok_ir = dspec[-1] < 0.5
    # no stable plateau near 4 over any full decade
    plateau = False
    for a in range(len(dspec)):
        b = a
        while b < len(dspec) and lt[b] - lt[a] < np.log(10):
            b += 1
        if b - a >= 3 and np.all(np.abs(dspec[a:b] - 4.0) < 0.5):
            plateau = True
    lines.append(f"[E13-B] UV->0: {ok_uv}, IR->0: {ok_ir}, "
                 f"4-plateau>=1decade: {plateau}")
    ok = ok_uv and ok_ir and not plateau
    verdict = "PASS" if ok else "FAIL"
    lines.append(f"[E13-B] {verdict}: control confirmed -- finite spectral "
                 f"dimension is 0, no emergence signal (locked correction C1)")
    return verdict, lines


# --------------------------------------------------------------------------
# E13-C : modular-flow inventory
# --------------------------------------------------------------------------

def sigma_flow(rho, s, A):
    """sigma_s^rho(A) = rho^{-is} A rho^{is} (K = -ln rho).

    Sign convention matches python/thet_logos/modular_flow.py
    (sigma(K,s,A) = e^{isK} A e^{-isK}, K = -ln rho), for which the KMS
    identity holds at beta = +1: Tr(rho A sigma_i(B)) = Tr(rho B A).
    (The textbook rho^{+is} convention is the inverse flow; the
    inert/nontrivial inventory is convention-independent.)
    """
    evals, vecs = la.eigh(rho)
    assert np.min(evals) > 1e-12, "state not full-rank: flow undefined"
    F = (vecs * np.exp(-1j * s * np.log(evals))) @ vecs.conj().T
    Fi = (vecs * np.exp(1j * s * np.log(evals))) @ vecs.conj().T
    return F @ A @ Fi


def e13c(rng):
    lines = []
    D = build_DF()
    H = D @ D
    Hbasis = selfadjoint_basis()
    observables = list(Hbasis) + [D, H]
    onames = ([f"alg{i}" for i in range(len(Hbasis))] + ["D_F", "D_F^2"])

    states = {
        "tracial": np.eye(DIM, dtype=complex) / DIM,
        "thermal_b1e-4": thermal_state(H, 1e-4),
        "thermal_b0.01": thermal_state(H, 0.01),
        "thermal_b1.0": thermal_state(H, 1.0),
        "random1": random_state(rng),
        "random2": random_state(rng),
    }
    s_test = 0.7
    n_nontrivial = 0
    for sname, rho in states.items():
        full_rank = np.min(la.eigvalsh(rho)) > 1e-12
        inert, nontriv = [], []
        flow_ok = True
        for oname, A in zip(onames, observables):
            comm = float(la.norm(rho @ A - A @ rho, "fro"))
            scale = float(la.norm(rho, "fro") * la.norm(A, "fro"))
            if comm < 1e-10 * max(scale, 1e-300):
                inert.append(oname)
                if full_rank:
                    moved = float(la.norm(sigma_flow(rho, s_test, A) - A,
                                          "fro"))
                    if moved > 1e-9 * max(float(la.norm(A, "fro")), 1e-300):
                        flow_ok = False
            else:
                nontriv.append(oname)
                n_nontrivial += 1
                if full_rank:
                    moved = float(la.norm(sigma_flow(rho, s_test, A) - A,
                                          "fro"))
                    if moved < 1e-12:
                        flow_ok = False  # [rho,a]!=0 but flow didn't move it
        lines.append(f"[E13-C] {sname}: inert={len(inert)} "
                     f"nontrivial={len(nontriv)} "
                     f"{'(flow consistency ok)' if flow_ok else '(FLOW INCONSISTENT)'}")
        assert flow_ok, f"flow/commutator inconsistency for {sname}"
        if sname == "tracial":
            assert len(nontriv) == 0, "tracial state must be fully inert"
            assert len(inert) == len(observables)

    # KMS spot-check for the full-rank thermal state at its own beta
    rho = states["thermal_b1e-4"]
    A = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))
    B = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))
    lhs = np.trace(rho @ A @ sigma_flow(rho, 1j * 1.0, B))
    rhs = np.trace(rho @ B @ A)
    ekms = abs(lhs - rhs)
    lines.append(f"[E13-C] KMS thermal_b1e-4 (beta_KMS=1): err={ekms:.3g}")
    assert ekms < 1e-8, "KMS failed for thermal_b1e-4"

    assert n_nontrivial > 0, "no nontrivial modular response anywhere"
    lines.append(f"[E13-C] PASS: tracial fully inert (rho=I/N => trivial flow); "
                 f"{n_nontrivial} nontrivial (state, observable) responses "
                 f"inventoried; KMS holds; no clock-time identification made")
    return "PASS", lines


# --------------------------------------------------------------------------
# driver
# --------------------------------------------------------------------------

def main():
    rng = np.random.default_rng(SEED)
    results = []
    for name, fn in [("E13-A", e13a), ("E13-B", e13b), ("E13-C", e13c)]:
        try:
            if name == "E13-B":
                verdict, lines = fn()
            else:
                verdict, lines = fn(rng)
        except AssertionError as e:
            verdict, lines = "FAIL", [f"[{name}] ASSERT: {e}"]
        for ln in lines:
            print(ln, flush=True)
        results.append((name, verdict))
    print("=" * 60, flush=True)
    allpass = True
    for name, verdict in results:
        print(f"{name}: {verdict}", flush=True)
        allpass = allpass and (verdict == "PASS")
    print("ENGINE 13 OVERALL: " + ("PASS" if allpass else "FAIL"), flush=True)
    return 0 if allpass else 1


if __name__ == "__main__":
    raise SystemExit(main())
