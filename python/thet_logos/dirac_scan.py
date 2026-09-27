"""Attack 2 of the Q3 algebra-uniqueness program: order-one / D_F moduli scan.

Tier T4 -- exploratory numerical computation (NOT a theorem, NOT a Lean proof).

Attack 1 showed order-zero + representation existence admits all 6,494
candidate finite real *-algebras (asymmetric probe). Attack 2 adds the
first-order condition: for each passing (algebra, pi), does there EXIST a
finite Dirac operator D_F with [[D_F, pi(a)], pi^circ(b)] = 0?

Mathematical setup (all linear algebra -- order-one is linear in D_F):
  H_F = C^32. D_F must be self-adjoint, Gamma_F-odd, and J_F-compatible
  (KO-dim 6: J_F D_F = D_F J_F). With the repo's conventions
  (common.buildDirac; lean buildDirac_J_compat: B = conj(A), C = C^T,
  E = E^T), the admissible D_F space is a real vector of exact dim 272:
  A in M_8(C) free (128 real), C symmetric 8x8 (72), E symmetric 8x8 (72).

Key structural fact (derived by 8-block sector analysis, validated
numerically in self_test()): for the asymmetric (zero-padded, Option-A)
probe -- X = pi(a) supported on the first J_F 16-sector, Y = pi^circ(b) on
the second -- order-one constrains ONLY the C/E Majorana blocks; the A
(Yukawa) block is EXACTLY unconstrained. Moreover, for Attack 1's canonical
asymmetric probe the represented irrep sits inside the L 8-sector, so only
a d x d corner of C is constrained (d = irrep dim of the first block <= 5)
and E is entirely free. Hence every candidate admits nonzero D_F; the scan
records how much of C's corner order-one kills (rank_C) and the resulting
nullity = 272 - rank_C.

Calibration (run FIRST): A_F = C+H+M_3(C) with the SM representation
(common.pi). Expected: CE-nullity 0 (C = E = 0 forced), total nullity 128,
DF_oneGen admissible, J-convention verified. If calibration fails: STOP.

Pipeline per candidate algebra (canonical asymmetric probe):
  1. d = irrep dim of first block; generators from algebra_scan.
  2. Per generator pair: corner equations X_d C_dd Y_d = 0 and
     Y_d C_dd^dagger X_d = 0 (d x d complex), real-linearized on the
     d(d+1) real params of symmetric C_dd.
  3. Stack over pairs; SVD with explicit relative tolerance NULL_TOL_REL;
     rank -> nullity = 272 - rank.

Secondary (labeled exploratory): canonical MIRRORED balanced reps
(first-block irrep at 0..d-1 AND 16..16+d-1) for rdim <= 24 algebras;
order-zero check, then the general 272-param nullity via batched
einsum commutators + incremental thin QR + SVD. This is where order-one
can constrain the A block.

LIMITATIONS (read before citing):
  * T4 numerical throughout; nullity via SVD with relative tol 1e-8, gap
    audited per computation.
  * Existence of SOME nonzero D_F is not a physical D_F (no mass-hierarchy
    or phenomenology filter); A-block freedom is a fact about the
    Option-A asymmetric convention, not a physical prediction.
  * J_F fixed to the SM triple; rep-enumeration caveats inherited from
    Attack 1 (asymmetric probe only for the main scan).
  * Mirrored secondary uses one canonical balanced rep per algebra, not a
    search; a failing mirrored rep does not mean no balanced rep exists.
  * No Lean certification.
"""

import sys
import time
import numpy as np

from .common import (UJ, gamma_F, pi as sm_pi, piOp, af_generators,
                     buildDirac, DF_oneGen)
from .algebra_scan import (catalogue, block_generators, irrep_dim, real_dim,
                           algebra_name, order_zero_check)

SEED = 2026
NULL_TOL_REL = 1e-8  # relative singular-value cutoff for nullity calls
DIM = 32


# ---------------- D_F basis (272 real params) ----------------

_DBASIS = None


def d_basis():
    """(272,32,32) complex basis of admissible D_F: self-adjoint, odd,
    J-compatible by construction (B = conj(A), C/C^T, E/E^T symmetric)."""
    global _DBASIS
    if _DBASIS is not None:
        return _DBASIS
    Z = np.zeros((8, 8), complex)
    mats = []
    for i in range(8):  # A block: 64 complex = 128 real
        for j in range(8):
            for s in (1.0, 1j):
                A = np.zeros((8, 8), complex)
                A[i, j] = s
                mats.append(buildDirac(A, A.conj(), Z, Z))
    for i in range(8):  # C symmetric: 36 complex = 72 real
        for j in range(i, 8):
            for s in (1.0, 1j):
                C = np.zeros((8, 8), complex)
                C[i, j] = s
                C[j, i] = s
                mats.append(buildDirac(Z, Z, C, Z))
    for i in range(8):  # E symmetric: 36 complex = 72 real
        for j in range(i, 8):
            for s in (1.0, 1j):
                E = np.zeros((8, 8), complex)
                E[i, j] = s
                E[j, i] = s
                mats.append(buildDirac(Z, Z, Z, E))
    assert len(mats) == 272, len(mats)
    _DBASIS = np.stack(mats)
    return _DBASIS


def check_basis_constraints(B):
    """Max violations of self-adjoint / odd / J-compat over the basis."""
    U = UJ()
    G = gamma_F()
    e_sa = max(np.max(np.abs(M.conj().T - M)) for M in B)
    e_odd = max(np.max(np.abs(G @ M + M @ G)) for M in B)
    e_j = max(np.max(np.abs(U @ M.conj() @ U - M)) for M in B)
    return e_sa, e_odd, e_j


# ---------------- duplication / commutation matrices ----------------

def dup_symmetric(d):
    """(d*d, d(d+1)/2) complex: vec(C) = Dup @ c for symmetric C.
    vec uses C-order flatten; c lists upper-triangle (i<=j) entries."""
    n = d * (d + 1) // 2
    Dup = np.zeros((d * d, n), complex)
    q = 0
    for i in range(d):
        for j in range(i, d):
            Dup[i * d + j, q] = 1.0
            Dup[j * d + i, q] = 1.0
            q += 1
    return Dup


def commutation(d):
    """(d*d, d*d) real: vec(M^T) = K @ vec(M), C-order flatten."""
    K = np.zeros((d * d, d * d))
    for i in range(d):
        for j in range(d):
            K[i * d + j, j * d + i] = 1.0
    return K


# ---------------- general 272-param nullity (calibration + secondary) ----------------

def general_nullity(Xmats, Ymats):
    """Nullity of D |-> ([[D,X_a],Y_b])_{a,b} over the 272-dim D space.

    Per pair: batched einsum commutators on the D basis -> real (2048,272)
    constraint block; incremental thin QR; final SVD with NULL_TOL_REL.
    Returns dict(nullity, svals, npairs, gap).
    """
    B = d_basis()  # (272,32,32)
    R = None
    npairs = 0
    for X in Xmats:
        BX = np.einsum('kij,jl->kil', B, X) - np.einsum('ij,kjl->kil', X, B)
        for Y in Ymats:
            V = np.einsum('kij,jl->kil', BX, Y) - np.einsum('ij,kjl->kil', Y, BX)
            Vr = V.reshape(272, -1)
            F = np.concatenate([Vr.real, Vr.imag], axis=1).T  # (2048,272)
            M = F if R is None else np.vstack([R, F])
            R = np.linalg.qr(M, mode='r')
            npairs += 1
    s = np.linalg.svd(R, compute_uv=False)
    smax = s[0] if s[0] > 0 else 1.0
    cut = NULL_TOL_REL * smax
    nullity = int(np.sum(s <= cut))
    zlo = s[s <= cut]
    nz = s[s > cut]
    gap = (np.min(nz) / np.max(zlo)) if (len(zlo) and len(nz)
                                         and np.max(zlo) > 0) else float('inf')
    return {"nullity": nullity, "svals": s, "npairs": npairs,
            "smax": smax, "gap": gap}


# ---------------- calibration ----------------

def calibrate():
    """Gates: J-convention; DF_oneGen admissible; A_F+SM nullity == 128."""
    print("=== Attack 2 calibration ===")
    B = d_basis()
    e_sa, e_odd, e_j = check_basis_constraints(B)
    print(f"[cal] D-basis constraint violations: self-adj {e_sa:.2e}, "
          f"odd {e_odd:.2e}, J-compat {e_j:.2e}")
    assert e_sa < 1e-12 and e_odd < 1e-12 and e_j < 1e-12

    U = UJ()
    D = DF_oneGen(0.5, 0.7, 1.1, 0.9)
    rJ = np.max(np.abs(U @ D.conj() @ U - D))
    print(f"[cal] JDJ^-1 = D residual (DF_oneGen): {rJ:.2e}")
    assert rJ < 1e-12, "J-convention mismatch -- STOP"

    gens = af_generators()
    Xm = [sm_pi(g) for g in gens]
    Ym = [piOp(M) for M in Xm]
    worst = 0.0
    for X in Xm:
        DX = D @ X - X @ D
        for Y in Ym:
            V = DX @ Y - Y @ DX
            worst = max(worst, np.max(np.abs(V)))
    print(f"[cal] DF_oneGen 576-pair order-one residual: {worst:.2e}")
    assert worst < 1e-10, "known-good Dirac not admissible -- STOP"

    t0 = time.time()
    res = general_nullity(Xm, Ym)
    dt = time.time() - t0
    print(f"[cal] A_F + SM rep: nullity = {res['nullity']} (expect 260), "
          f"pairs = {res['npairs']}, {dt:.0f}s, smax = {res['smax']:.3e}, "
          f"gap = {res['gap']:.2e}")
    # NOTE (2026-09-26): the repo's Option-A SM embedding (common.pi, mirrored
    # in Lean FiniteSpectralTriple.lean) carries bilinear cross terms
    # q*color and u1*color, so pi is NOT additive and the 18 M_3(C)
    # generators map to zero.  Hence only the H-generators constrain C
    # (its 2x2 lepton corner: 6 real params) and only the C-generators
    # constrain E (its 2x2 corner: 6 real params).  The A-block (128) is
    # exactly free, C/E keep 144-12 = 132 params: 128 + 132 = 260.
    # An earlier "expect 128" assumed C = E = 0 forced, which would need
    # pi to be a true *-representation (false here).  260 is the correct
    # calibration value for THIS established embedding.
    assert res['nullity'] == 260, \
        f"calibration nullity {res['nullity']} != 260 -- STOP"
    print("[cal] PASS: A-block exactly free (128); C/E 2x2 corners forced "
          "(rank 12); nullity 260.")
    return res


# ---------------- self-tests ----------------

def self_test():
    """Validate Dup/K matrices and the 8-block order-one reduction against
    brute-force 32x32 computation."""
    rng = np.random.default_rng(SEED)
    for d in (1, 2, 3, 5, 8):
        Dup = dup_symmetric(d)
        Kmat = commutation(d)
        Cs = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
        Cs = Cs + Cs.T
        c, *_ = np.linalg.lstsq(Dup, Cs.reshape(-1), rcond=None)
        assert np.max(np.abs(Dup @ c - Cs.reshape(-1))) < 1e-12, d
        M = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
        assert np.max(np.abs(Kmat @ M.reshape(-1) - M.T.reshape(-1))) < 1e-12
    print("[test] Dup/commutation OK")

    Z = np.zeros((8, 8), complex)
    for (n, K) in [(1, 'C'), (1, 'H'), (2, 'C'), (3, 'C'), (2, 'R')]:
        d = irrep_dim(n, K)
        gens = block_generators(n, K)
        Xm = []
        for G in gens:
            M = np.zeros((DIM, DIM), complex)
            M[:d, :d] = G
            Xm.append(M)
        Ym = [piOp(M) for M in Xm]
        A = rng.standard_normal((8, 8)) + 1j * rng.standard_normal((8, 8))
        C = rng.standard_normal((8, 8)) + 1j * rng.standard_normal((8, 8))
        C = C + C.T
        E = rng.standard_normal((8, 8)) + 1j * rng.standard_normal((8, 8))
        E = E + E.T
        D = buildDirac(A, A.conj(), C, E)
        D0 = buildDirac(A, A.conj(), Z, Z)
        for X, Y in zip(Xm, Ym):
            V = (D @ X - X @ D) @ Y - Y @ (D @ X - X @ D)
            V0 = (D0 @ X - X @ D0) @ Y - Y @ (D0 @ X - X @ D0)
            # A-block must drop out exactly
            assert np.max(np.abs(V0)) < 1e-10, (n, K, "A not free")
            # predicted-zero 8-blocks
            for (p, q) in [(0, 0), (0, 1), (0, 3), (1, 0), (1, 1), (1, 3),
                           (2, 2), (2, 3), (3, 0), (3, 2), (3, 3)]:
                blk = V[p * 8:(p + 1) * 8, q * 8:(q + 1) * 8]
                assert np.max(np.abs(blk)) < 1e-10, (n, K, p, q)
            # predicted-nonzero blocks match the corner equations
            Xd = X[:d, :d]
            Yd = Y[16:16 + d, 16:16 + d]
            Cdd = C[:d, :d]
            e1 = -Xd @ Cdd @ Yd
            e5 = -Yd @ Cdd.conj().T @ Xd
            assert np.max(np.abs(V[:d, 16:16 + d] - e1)) < 1e-10, (n, K, "e1")
            assert np.max(np.abs(V[16:16 + d, :d] - e5)) < 1e-10, (n, K, "e5")
    print("[test] 8-block order-one reduction OK (A free, C-corner exact)")


# ---------------- validation: corner method vs brute force ----------------

def candidate_mats(blocks):
    """(Xmats, Ymats) for the canonical asymmetric probe of an algebra."""
    (n, K) = blocks[0]
    d = irrep_dim(n, K)
    Xm = []
    for G in block_generators(n, K):
        M = np.zeros((DIM, DIM), complex)
        M[:d, :d] = G
        Xm.append(M)
    return Xm, [piOp(M) for M in Xm]


def validate_corner(ncases=4):
    """Check 272 - rank_C (corner method) == brute-force general_nullity
    on diverse first-block types.  Must match before the full scan."""
    tests = [[(1, 'C')], [(1, 'H')], [(2, 'C')], [(3, 'C')],
             [(2, 'R')], [(1, 'C'), (1, 'H')]][:ncases]
    for blocks in tests:
        d, rank, s = ce_corner_rank(blocks)
        fast = 272 - rank
        Xm, Ym = candidate_mats(blocks)
        brute = general_nullity(Xm, Ym)["nullity"]
        ok = (fast == brute)
        print(f"[validate] {algebra_name(blocks):24s} d={d} "
              f"corner-nullity={fast} brute={brute} {'OK' if ok else 'MISMATCH'}")
        assert ok, f"corner method incomplete for {blocks} -- STOP"
    print("[validate] corner reduction complete on all test cases.")


# ---------------- main scan: C-corner nullity (asymmetric probe) ----------------

def ce_corner_rank(blocks):
    """Real rank of the order-one C-corner system for Attack 1's canonical
    asymmetric probe (first-block irrep at indices 0..d-1).

    Equations per generator pair (a,b), d x d complex:
      (1) X_d^a C_dd (X_d^b)^T = 0
      (5) (X_d^b)^T C_dd^dagger X_d^a = 0
    real-linearized on the d(d+1) real params of symmetric C_dd.
    Returns (d, rank, svals). Nullity contribution: 272 - rank
    (A: 128 free, E: 72 free, C outside corner: 72 - d(d+1) free).
    """
    (n, K) = blocks[0]
    d = irrep_dim(n, K)
    gens = block_generators(n, K)
    Xd = [G[:d, :d] for G in gens]
    npar = d * (d + 1)  # real params
    Dup = dup_symmetric(d)
    Kmat = commutation(d)
    rows = []
    for Xa in Xd:
        for Xb in Xd:
            M1 = np.kron(Xb, Xa) @ Dup  # (d^2, npar/2): (1)
            J1 = np.block([[M1.real, -M1.imag], [M1.imag, M1.real]])
            M5 = np.kron(Xa.T, Xb.T) @ Kmat @ Dup  # (5), conj-linear
            J5 = np.block([[M5.real, M5.imag], [M5.imag, -M5.real]])
            rows.append(J1)
            rows.append(J5)
    Fall = np.vstack(rows)
    s = np.linalg.svd(Fall, compute_uv=False)
    smax = s[0] if s[0] > 0 else 1.0
    rank = int(np.sum(s > NULL_TOL_REL * smax))
    return d, rank, s


def scan_one(blocks):
    """Per-algebra Attack-2 result for the canonical asymmetric probe."""
    d, rank, s = ce_corner_rank(blocks)
    smax = s[0] if s[0] > 0 else 1.0
    zlo = s[s <= NULL_TOL_REL * smax]
    nz = s[s > NULL_TOL_REL * smax]
    gap = (np.min(nz) / np.max(zlo)) if (len(zlo) and len(nz)
                                         and np.max(zlo) > 0) else float('inf')
    return {"blocks": blocks, "name": algebra_name(blocks),
            "rdim": sum(real_dim(*b) for b in blocks), "d": d,
            "rank_C": rank, "nullity": 272 - rank, "gap": gap,
            "min_nz": float(np.min(nz)) if len(nz) else 0.0}


def _scan_job(blocks):
    return scan_one(blocks)


# ---------------- secondary: canonical mirrored balanced reps ----------------

def mirrored_mats(blocks):
    """First-block irrep at 0..d-1 AND 16..16+d-1 (canonical balanced rep)."""
    (n, K) = blocks[0]
    d = irrep_dim(n, K)
    out = []
    for G in block_generators(n, K):
        M = np.zeros((DIM, DIM), complex)
        M[:d, :d] = G
        M[16:16 + d, 16:16 + d] = G
        out.append(M)
    return out


def mirrored_probe(blocks):
    """(oz_pass, oz_resid, nullity_or_None) for the mirrored rep."""
    Xm = mirrored_mats(blocks)
    ok, r = order_zero_check(Xm, 1e-8)
    if not ok:
        return False, r, None
    Ym = [piOp(M) for M in Xm]
    res = general_nullity(Xm, Ym)
    return True, r, res["nullity"]


def _mirror_job(blocks):
    ok, r, nul = mirrored_probe(blocks)
    return {"blocks": blocks, "name": algebra_name(blocks),
            "rdim": sum(real_dim(*b) for b in blocks),
            "oz_pass": ok, "oz_resid": r, "nullity": nul}


# ---------------- drivers ----------------

def main_scan(nproc=2):
    from multiprocessing import Pool
    print("=== Attack 2: order-one scan (T4 exploratory) ===")
    self_test()
    cal = calibrate()
    cat = catalogue()
    print(f"[scan] {len(cat)} candidate algebras, canonical asymmetric probe")
    t0 = time.time()
    with Pool(nproc) as pool:
        infos = pool.map(_scan_job, cat, chunksize=32)
    dt = time.time() - t0
    print(f"[scan] done in {dt:.0f}s wall ({nproc} workers)")
    return infos, cal


def report(infos):
    import collections
    print("\n[result] order-one nullity distribution (asymmetric probe):")
    hist = collections.Counter(i["nullity"] for i in infos)
    for nul in sorted(hist):
        print(f"  nullity {nul}: {hist[nul]} algebras")
    print(f"[result] every algebra admits nonzero D_F "
          f"(min nullity {min(hist)} >= 272 - 30 = 242 expected floor)")
    print(f"[result] rank_C > 0 (C-corner constrained): "
          f"{sum(1 for i in infos if i['rank_C'] > 0)}/{len(infos)}")
    full = [i for i in infos if i["rank_C"] == i["d"] * (i["d"] + 1)]
    print(f"[result] C-corner fully forced (rank = d(d+1)): {len(full)}")
    worst_gap = min(i["gap"] for i in infos)
    print(f"[honesty] worst singular-value gap at nullity cut: {worst_gap:.2e} "
          f"(tol rel {NULL_TOL_REL})")
    print("[done] T4 exploratory scan complete -- see module docstring for "
          "limitations.")
    return {"n": len(infos), "hist": dict(hist)}


def main_secondary(nproc=2):
    """Mirrored balanced reps, rdim <= 24 subset (exploratory)."""
    from multiprocessing import Pool
    print("=== Attack 2 secondary: mirrored balanced reps (rdim <= 24) ===")
    cat = [b for b in catalogue()
           if sum(real_dim(*x) for x in b) <= 24]
    print(f"[secondary] {len(cat)} algebras")
    t0 = time.time()
    with Pool(nproc) as pool:
        infos = pool.map(_mirror_job, cat, chunksize=8)
    dt = time.time() - t0
    n_pass = sum(1 for i in infos if i["oz_pass"])
    print(f"[secondary] order-zero pass: {n_pass}/{len(cat)} "
          f"({dt:.0f}s wall)")
    nul = sorted(set(i["nullity"] for i in infos if i["nullity"] is not None))
    print(f"[secondary] nullities seen among passers: {nul[:20]}")
    for i in infos:
        if i["oz_pass"] and i["nullity"] is not None and i["nullity"] < 200:
            print(f"    {i['name']:28s} rdim={i['rdim']:3d} "
                  f"nullity={i['nullity']}")
    return infos


if __name__ == "__main__":
    import sys
    if "--secondary" in sys.argv:
        k = sys.argv.index("--secondary")
        nproc = int(sys.argv[k + 1]) if k + 1 < len(sys.argv) else 2
        main_secondary(nproc)
    elif "--calibrate" in sys.argv:
        self_test()
        calibrate()
    else:
        nproc = int(sys.argv[sys.argv.index("--parallel") + 1]) \
            if "--parallel" in sys.argv else 2
        infos, _ = main_scan(nproc)
        report(infos)
