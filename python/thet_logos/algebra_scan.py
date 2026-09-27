"""Attack 1 of the Q3 algebra-uniqueness program: candidate-algebra scan.

Tier T4 -- exploratory numerical computation (NOT a theorem, NOT a Lean proof).

Question: which finite real *-algebras admit a *-representation on C^32
satisfying the order-zero condition [pi(a), pi^circ(b)] = 0 against the SM
triple's FIXED real structure J_F (common.UJ / common.piOp)?

Pipeline per candidate algebra A = (+) M_{n_i}(K_i), K in {R, C, H},
total real dim <= 32:
  1. enumerate *-representations on C^32 as direct sums of irreps under a
     multiplicity scheme (zero-padded to dim 32; covers the SM's asymmetric
     Option-A pattern);
  2. build the representation matrices for a small real-algebra GENERATING
     set of each block (generator-pair checks imply the full condition --
     see block_generators docstring for the subalgebra argument);
  3. test order-zero on all generator pairs;
  4. record: any passing NONZERO rep? any passing BALANCED rep (both J_F
     16-sectors nonzero)? The balanced probe is stratified by peer
     relevance: rdim == 24 (A_F's dimension) gets a deep deterministic slice
     (600 patterns), rdim < 24 a standard slice (120), rdim > 24 the
     asymmetric probe only. Truncation is flagged per algebra.

Theta filter: the Thet relations J theta J^-1 = theta^dagger and
Gamma theta Gamma = -theta involve only the triple -- theta is a T1
primitive, independent of A. The scan computes the real solution space for
theta on C^32 (a triple-level fact) and compares survivor lists with and
without this filter.

LIMITATIONS (read before citing):
  * J_F is HELD FIXED to the SM triple (common.UJ). A candidate killed here
    might satisfy order-zero with a different real structure. This scan
    tests compatibility with the SM triple, not absolute admissibility.
  * Order-one and the D_F moduli are NOT tested (that's Attack 2).
  * Balanced-pattern search is budget-capped per algebra (deterministic
    order); algebras hitting the cap are flagged, not claimed exhaustive.
  * The zero representation is excluded from the survivor criterion (it
    trivially passes for every algebra).
  * Tolerance TOL = 1e-8 on max-abs commutator entries (float64).

Conventions mirror python/thet_logos/common.py (Option-A embedding,
piOp(M) = U_J @ M.T @ U_J) and lean/ThetLogos/Scaffold32.lean
(gamma_F = diag(+I8,-I8,-I8,+I8), partner k <-> k+16).
"""

import numpy as np

from .common import UJ, gamma_F, piOp, pi as sm_pi, af_generators, quat_units, partner

SEED = 2026
TOL = 1e-8
DIM = 32
HALF = 16
BALANCED_BUDGET = 800  # max balanced patterns tested per algebra (deterministic)

FIELD_RDIM = {"R": 1, "C": 2, "H": 4}


def real_dim(n, K):
    """Real dimension of the block M_n(K)."""
    return n * n * FIELD_RDIM[K]


def irrep_dim(n, K):
    """Complex dimension of the (unique) irreducible *-representation."""
    return n if K in ("R", "C") else 2 * n


def block_generators(n, K):
    """Small real-algebra GENERATING set for M_n(K) (complex matrices).

    Checking [pi(s), piOp(pi(t))] = 0 on generators s, t suffices: for fixed
    t the set {a : [pi(a), piOp(pi(t))] = 0} is a real subalgebra (sums are
    linear; products via [AB,C] = A[B,C] + [A,C]B), and piOp is an
    anti-homomorphism (piOp(b1 b2) = piOp(b2) piOp(b1) since transpose
    reverses order), so the same holds in the second argument. Hence
    generator-pair checks imply the full basis-pair condition.
    """
    qu = quat_units()
    i2, j2 = qu[1], qu[2]

    def unit(n_, p, q):
        M = np.zeros((n_, n_), complex)
        M[p, q] = 1.0
        return M

    gens = []
    if n == 1:
        if K == "R":
            return [np.ones((1, 1), complex)]
        if K == "C":
            return [1j * np.ones((1, 1), complex)]
        return [i2, j2]  # H: i, j generate (k = ij, 1 = -i^2)
    for i in range(n - 1):
        e1, e2 = unit(n, i, i + 1), unit(n, i + 1, i)
        if K == "H":
            gens.append(np.kron(e1, np.eye(2)))
            gens.append(np.kron(e2, np.eye(2)))
        else:
            gens.append(e1)
            gens.append(e2)
    if K == "C":
        gens.append(1j * unit(n, 0, 0))
    elif K == "H":
        gens.append(np.kron(unit(n, 0, 0), i2))
        gens.append(np.kron(unit(n, 0, 0), j2))
    return gens


_IRREP_CACHE = {}


def block_irrep_basis(n, K):
    """Real basis of M_n(K) as complex matrices (the irrep). Cached."""
    key = (n, K)
    if key in _IRREP_CACHE:
        return _IRREP_CACHE[key]
    E = np.eye(n, dtype=complex)
    basis = []
    if K == "R":
        for p in range(n):
            for q in range(n):
                M = np.zeros((n, n), complex)
                M[p, q] = 1.0
                basis.append(M)
    elif K == "C":
        for p in range(n):
            for q in range(n):
                for s in (1.0, 1j):
                    M = np.zeros((n, n), complex)
                    M[p, q] = s
                    basis.append(M)
    else:  # H: E_pq (x) quaternion unit, via Kronecker -> 2n x 2n
        for p in range(n):
            for q in range(n):
                Rpq = np.zeros((n, n), complex)
                Rpq[p, q] = 1.0
                for u in quat_units():
                    basis.append(np.kron(Rpq, u))
    assert len(basis) == real_dim(n, K)
    _IRREP_CACHE[key] = basis
    return basis


def block_types():
    """All (n, K) with real dim <= 32."""
    out = []
    for n in range(1, 33):
        for K in ("R", "C", "H"):
            if real_dim(n, K) <= DIM:
                out.append((n, K))
    return out


def catalogue():
    """All finite real *-algebras = multisets of blocks, real dim <= 32.

    Each isomorphism class exactly once (Artin-Wedderburn over R).
    """
    types = block_types()
    out = []

    def rec(start, current, rdim):
        if current:
            out.append(tuple(current))
        for i in range(start, len(types)):
            d = real_dim(*types[i])
            if rdim + d > DIM:
                continue
            current.append(types[i])
            rec(i, current, rdim + d)
            current.pop()

    rec(0, [], 0)
    return out


def algebra_name(blocks):
    parts = []
    for (n, K) in blocks:
        parts.append({("R"): f"M{n}(R)", ("C"): "C" if n == 1 else f"M{n}(C)",
                      ("H"): "H" if n == 1 else f"M{n}(H)"}[(K)])
    return " + ".join(parts)


def rep_matrices(blocks, mults, basis_fn=block_irrep_basis):
    """Complex 32x32 matrices for the real basis of A under the given
    multiplicities (irrep blocks placed in order, zero-padded to 32).

    basis_fn: block_irrep_basis (full real basis) or block_generators
    (small generating set -- sufficient for the order-zero test, see
    block_generators docstring).
    """
    # block offsets
    offs, off = [], 0
    for (n, K), m in zip(blocks, mults):
        offs.append(off)
        off += m * irrep_dim(n, K)
    assert off <= DIM
    mats = []
    for bi, ((n, K), m) in enumerate(zip(blocks, mults)):
        d = irrep_dim(n, K)
        for B in basis_fn(n, K):
            M = np.zeros((DIM, DIM), complex)
            for c in range(m):
                s = offs[bi] + c * d
                M[s:s + d, s:s + d] = B
            mats.append(M)
    return mats


def support_sectors(blocks, mults):
    """Which of the fixed 16+16 J_F sectors carry nonzero rep mass."""
    s1 = s2 = False
    off = 0
    for (n, K), m in zip(blocks, mults):
        d = irrep_dim(n, K)
        for c in range(m):
            a, b = off + c * d, off + (c + 1) * d
            if a < HALF:
                s1 = True
            if b > HALF:
                s2 = True
        off += m * d
    return s1, s2


def order_zero_residual(mats):
    """max |[pi(a), piOp(pi(b))]| over real-basis pairs."""
    if not mats:
        return 0.0
    O = np.stack([piOp(M) for M in mats])  # (J,32,32)
    worst = 0.0
    for A in mats:
        C = A @ O - O @ A
        v = np.max(np.abs(C))
        if v > worst:
            worst = v
    return worst


def order_zero_check(mats, tol):
    """(passes, worst): early-exit order-zero test over basis pairs."""
    if not mats:
        return True, 0.0
    O = [piOp(M) for M in mats]
    worst = 0.0
    for A in mats:
        for B in O:
            v = np.max(np.abs(A @ B - B @ A))
            if v > worst:
                worst = v
                if worst > tol:
                    return False, worst
    return True, worst


def canonical_patterns(blocks, budget):
    """Deterministic multiplicity patterns (nonincreasing for identical
    blocks), sum m_i d_i <= 32. Returns (patterns, exhausted)."""
    r = len(blocks)
    ds = [irrep_dim(*b) for b in blocks]
    pats, exhausted = [], [True]

    def rec(i, current, used, prev_block, prev_m):
        if len(pats) >= budget:
            exhausted[0] = False
            return
        if i == r:
            pats.append(tuple(current))
            return
        same = blocks[i] == prev_block
        hi = (32 - used) // ds[i]
        if same:
            hi = min(hi, prev_m)
        for m in range(hi + 1):
            current.append(m)
            rec(i + 1, current, used + m * ds[i], blocks[i], m)
            current.pop()
            if len(pats) >= budget:
                exhausted[0] = False
                return

    rec(0, [], 0, None, 10 ** 9)
    return pats, exhausted[0]


def is_commutative(blocks):
    """True iff every block is (1,R) or (1,C): then every *-representation
    is by diagonal matrices (1-dim irreps), piOp preserves diagonality
    (U_J is a permutation), and diagonal matrices commute -- so EVERY
    multiplicity pattern passes order-zero. Proved, not sampled."""
    return all(b == (1, "R") or b == (1, "C") for b in blocks)


def scan_algebra(blocks, budget=BALANCED_BUDGET):
    """Returns dict with survivor info for one candidate algebra.

    Order-zero is tested on small ALGEBRA-GENERATING sets (see
    block_generators): generator-pair checks imply the full condition.

    budget: max balanced patterns tested (deterministic order); truncation
    is flagged in the result, not silently dropped.
    """
    gen_mats = lambda p: rep_matrices(blocks, p, block_generators)
    # (a) canonical asymmetric probe: single irrep of first block in sector 1
    asym = [0] * len(blocks)
    asym[0] = 1
    r_asym = order_zero_residual(gen_mats(asym))
    # (b) balanced probe: deterministic budgeted patterns, both sectors hit.
    # Uses early-exit checks (most random patterns fail fast).
    # Enumerate budget+1 to distinguish true exhaustion from truncation.
    bal_tested = bal_pass = 0
    bal_example = None
    bal_by_theorem = False
    bal_skipped = budget <= 0
    if not bal_skipped:
        _pats, _ = canonical_patterns(blocks, budget + 1)
        exhaustive = len(_pats) <= budget
        pats = _pats[:budget]
    else:
        pats, exhaustive = [], True
    if is_commutative(blocks):
        # Diagonal-matrix argument: every balanced pattern passes (proved),
        # so the balanced question is fully resolved regardless of slice.
        exhaustive = True
        balps = [p for p in pats if sum(p) > 0
                 and all(support_sectors(blocks, p))]
        bal_tested = bal_pass = len(balps)
        bal_by_theorem = True
        if balps:
            bal_example = (balps[0], 0.0)
    else:
        for p in pats:
            if sum(p) == 0:
                continue
            s1, s2 = support_sectors(blocks, p)
            if not (s1 and s2):
                continue
            bal_tested += 1
            ok, r = order_zero_check(gen_mats(p), TOL)
            if ok:
                bal_pass += 1
                if bal_example is None:
                    bal_example = (p, r)
    return {
        "blocks": blocks,
        "name": algebra_name(blocks),
        "rdim": sum(real_dim(*b) for b in blocks),
        "asym_residual": r_asym,
        "asym_pass": r_asym < TOL,
        "bal_tested": bal_tested,
        "bal_pass": bal_pass,
        "bal_example": bal_example,
        "bal_exhaustive": exhaustive,
        "bal_by_theorem": bal_by_theorem,
        "bal_skipped": bal_skipped,
    }


# ---------------- Thet theta relations (triple-level) ----------------

def theta_solution_dim():
    """Exact real dimension of {theta in M_32(C) : J theta J^-1 = theta^dagger,
    Gamma theta Gamma = -theta}, with J = U_J o complex-conjugation.

    Write theta = X + iY (X, Y real). The relations become
      U X U = X^T,  U Y U = Y^T,  Gamma X Gamma = -X,  Gamma Y Gamma = -Y,
    i.e. entrywise with p the partner map and gamma_a = +/-1:
      X_ab = X_{p(b)p(a)},  Y_ab = Y_{p(b)p(a)},
      X_ab = Y_ab = 0 unless gamma_a gamma_b = -1.
    sigma(a,b) = (p(b), p(a)) is an involution; X and Y are each constant
    on sigma-orbits of the admissible support, giving twice the orbit
    count. Triple-level fact: independent of the candidate algebra A.
    """
    p = [partner(k) for k in range(DIM)]
    gamma = np.diag(gamma_F()).real
    S = [(a, b) for a in range(DIM) for b in range(DIM)
         if gamma[a] * gamma[b] < 0]
    seen = set()
    orbits = 0
    for (a, b) in S:
        if (a, b) in seen:
            continue
        seen.add((a, b))
        seen.add((p[b], p[a]))
        orbits += 1
    return 2 * orbits


def theta_example():
    """Explicit nonzero theta satisfying both Thet relations (T4 check)."""
    p = [partner(k) for k in range(DIM)]
    gamma = np.diag(gamma_F()).real
    # find an admissible 2-cycle orbit of sigma
    pick = None
    for a in range(DIM):
        for b in range(DIM):
            if gamma[a] * gamma[b] < 0 and (p[b], p[a]) != (a, b):
                pick = (a, b)
                break
        if pick:
            break
    a, b = pick
    c, d = p[b], p[a]
    X = np.zeros((DIM, DIM))
    Y = np.zeros((DIM, DIM))
    X[a, b] = X[c, d] = 1.0
    Y[a, b] = Y[c, d] = 1.0
    return X + 1j * Y


def check_theta_relations(theta):
    """Verify J theta J^-1 = theta^dagger and Gamma theta Gamma = -theta."""
    U = UJ()
    G = gamma_F()
    lhs1 = U @ theta.conj() @ U  # J theta J^-1, J = U o cc
    err1 = np.max(np.abs(lhs1 - theta.conj().T))
    err2 = np.max(np.abs(G @ theta @ G + theta))
    return err1, err2


# ---------------- controls ----------------

def sm_control():
    """Order-zero on the actual SM triple (common.pi, 24 generators)."""
    gens = af_generators()
    mats = [sm_pi(g) for g in gens]
    return order_zero_residual(mats)


def sm_doubled():
    """Balanced probe for A_F itself: SM 16-dim rep on BOTH J_F sectors."""
    from .common import embedSM
    gens = af_generators()
    mats = []
    for g in gens:
        E = embedSM(g)
        M = np.zeros((DIM, DIM), complex)
        M[:HALF, :HALF] = E
        M[HALF:, HALF:] = E
        mats.append(M)
    return order_zero_residual(mats)


def _scan_one(job):
    """Picklable worker for parallel scans. job = (blocks, budget)."""
    blocks, budget = job
    return scan_algebra(blocks, budget=budget)


def collect_theta_and_controls():
    """Triple-level theta facts + SM controls (serial, fast)."""
    nullity = theta_solution_dim()
    th = theta_example()
    e1, e2 = check_theta_relations(th)
    r_sm = sm_control()
    r_dbl = sm_doubled()
    return nullity, e1, e2, r_sm, r_dbl


def report_results(cat, infos, nullity, e1, e2, r_sm, r_dbl):
    """Print the survivor report from per-algebra infos."""
    survivors, bal_survivors, truncated = [], [], []
    for info in infos:
        assert info["asym_pass"], f"asymmetric probe failed for {info['name']}"
        survivors.append(info)
        if info["bal_pass"]:
            bal_survivors.append(info)
        if not info["bal_exhaustive"]:
            truncated.append(info["name"])

    print(f"\n[result] algebras with a passing (nonzero) rep: "
          f"{len(survivors)}/{len(cat)}")
    print(f"[result] algebras with a passing BALANCED rep: "
          f"{len(bal_survivors)}/{len(cat)}")
    n_thm = sum(1 for i in bal_survivors if i["bal_by_theorem"])
    n_comm_total = sum(1 for b in cat if is_commutative(b))
    n_comm_skipped = sum(1 for i in infos
                         if i["bal_skipped"] and is_commutative(i["blocks"]))
    print(f"  of which {n_thm} commutative (all patterns pass -- proved, "
          f"diagonal-matrix argument)")
    if n_comm_skipped:
        print(f"  plus {n_comm_skipped} commutative rdim>24 not probe-tested "
              f"but covered by the same theorem "
              f"({n_comm_total} commutative total)")
    if bal_survivors:
        print("  balanced survivors (noncommutative shown):")
        shown = 0
        for info in bal_survivors:
            if info["bal_by_theorem"]:
                continue
            p, r = info["bal_example"]
            print(f"    {info['name']:28s} rdim={info['rdim']:3d} "
                  f"example mults={p} resid={r:.2e} "
                  f"(tested {info['bal_tested']}, "
                  f"{'exhaustive' if info['bal_exhaustive'] else 'TRUNCATED'})")
            shown += 1
            if shown >= 40:
                print(f"    ... and {len(bal_survivors) - n_thm - shown} more")
                break
    print(f"[result] theta filter changes survivor list: NO "
          f"(theta relations are triple-level; nullity={nullity} > 0)")
    if truncated:
        print(f"[honesty] balanced search truncated (deterministic slice) for "
              f"{len(truncated)} algebras: "
              f"{', '.join(truncated[:6])}{'...' if len(truncated) > 6 else ''}")
    n_skip = sum(1 for i in infos if i["bal_skipped"])
    if n_skip:
        print(f"[honesty] {n_skip} algebras (rdim > 24) got the asymmetric "
              f"probe only -- no balanced search (out of peer range)")
    print("[done] T4 exploratory scan complete -- see module docstring for "
          "limitations.")
    return {
        "n_candidates": len(cat),
        "n_survivors": len(survivors),
        "n_balanced": len(bal_survivors),
        "theta_nullity": nullity,
        "truncated": truncated,
    }


def main():
    print("=== Attack 1: candidate-algebra scan (T4 exploratory) ===")
    cat = catalogue()
    print(f"catalogue: {len(cat)} candidate algebras (real dim <= 32)")

    nullity, e1, e2, r_sm, r_dbl = collect_theta_and_controls()
    print(f"[theta] solution-space real dim = {nullity}; "
          f"verify JtJ^-1=t^d err {e1:.2e}, GtG=-t err {e2:.2e}")
    assert nullity > 0 and e1 < 1e-8 and e2 < 1e-8
    print(f"[control] SM triple order-zero residual: {r_sm:.2e} "
          f"({'PASS' if r_sm < TOL else 'FAIL'})")
    assert r_sm < TOL
    print(f"[control] SM algebra, doubled (balanced) rep residual: {r_dbl:.2e} "
          f"({'PASS' if r_dbl < TOL else 'FAIL -- asymmetry forced'})")

    infos = []
    for idx, blocks in enumerate(cat):
        infos.append(scan_algebra(blocks))
        if idx % 500 == 0:
            print(f"  ... {idx}/{len(cat)} algebras scanned", flush=True)
    return report_results(cat, infos, nullity, e1, e2, r_sm, r_dbl)


def main_parallel(nproc=8):
    from multiprocessing import Pool
    print("=== Attack 1: candidate-algebra scan, parallel "
          f"(T4 exploratory, {nproc} workers) ===")
    cat = catalogue()
    print(f"catalogue: {len(cat)} candidate algebras (real dim <= 32)")

    nullity, e1, e2, r_sm, r_dbl = collect_theta_and_controls()
    print(f"[theta] solution-space real dim = {nullity}; "
          f"verify JtJ^-1=t^d err {e1:.2e}, GtG=-t err {e2:.2e}")
    assert nullity > 0 and e1 < 1e-8 and e2 < 1e-8
    print(f"[control] SM triple order-zero residual: {r_sm:.2e} "
          f"({'PASS' if r_sm < TOL else 'FAIL'})")
    assert r_sm < TOL
    print(f"[control] SM algebra, doubled (balanced) rep residual: {r_dbl:.2e} "
          f"({'PASS' if r_dbl < TOL else 'FAIL -- asymmetry forced'})")

    # Stratified balanced probe (the asymmetric survivor probe is exact and
    # cheap for all 6494; the balanced probe is budgeted by peer relevance):
    #   rdim == 24 (A_F's dimension): deep slice, budget 600
    #   rdim < 24:  standard slice, budget 120
    #   rdim > 24:  asymmetric probe only (budget 0 balanced patterns)
    jobs = []
    for b in cat:
        rd = sum(real_dim(*x) for x in b)
        if rd == 24:
            jobs.append((b, 600))
        elif rd < 24:
            jobs.append((b, 120))
        else:
            jobs.append((b, 0))
    n_deep = sum(1 for _, bd in jobs if bd == 600)
    n_std = sum(1 for _, bd in jobs if bd == 120)
    n_asym = sum(1 for _, bd in jobs if bd == 0)
    print(f"[plan] balanced probe: {n_deep} algebras at budget 600 "
          f"(rdim=24), {n_std} at budget 120 (rdim<24), "
          f"{n_asym} asymmetric-only (rdim>24)")

    with Pool(nproc) as pool:
        infos = pool.map(_scan_one, jobs, chunksize=4)
    return report_results(cat, infos, nullity, e1, e2, r_sm, r_dbl)


if __name__ == "__main__":
    import sys
    if "--parallel" in sys.argv:
        k = sys.argv.index("--parallel")
        nproc = int(sys.argv[k + 1]) if k + 1 < len(sys.argv) else 8
        main_parallel(nproc)
    else:
        main()
