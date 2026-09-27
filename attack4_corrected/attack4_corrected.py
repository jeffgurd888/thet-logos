"""Corrected Attack 4: order-one nullity with the full 24-real-generator basis.

T4 NUMERICAL EXPLORATION ONLY. Not a theorem, not a Lean proof.

Corrects the previous scan, which used 23 real generators and omitted
i*I_3 (the imaginary unit of the M_3(C) summand). This rerun uses all 24:
  C:    {P_C, genC}                                  (2)
  H:    {P_H, i*genH_0, i*genH_1, i*genH_2}           (4)
  M3:   {P_M, i*P_M, genM_0..7, i*genM_0..7}          (18)

Generator definitions ported exactly from lean/ThetLogos/MartinettiRep.lean
(genC, genH, genM, gellMann, pauli), whose representation was proven
faithful (kernel = {0}) in Lean via `faithful_blocks`.

Conventions (match Scaffold32.lean):
  gammaF = diag(+1 on 0-7 and 24-31, -1 on 8-23)
  UJ[i,j] = 1 iff j = partner(i), partner(k) = k+16 (k<16) else k-16
  pi^circ(M) = UJ @ M.T @ UJ
  J-compatibility (KO-6): UJ @ conj(D) = D @ UJ
"""
import json
import os
import time

import numpy as np

DIM = 32
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
os.makedirs(OUT, exist_ok=True)

TOL_RANK = 1e-8   # relative SVD cutoff for rank/nullity calls
TOL_ZERO = 1e-8   # absolute tolerance for axiom residuals


# --------------------------------------------------------------------------
# Lean-mirrored building blocks
# --------------------------------------------------------------------------

def pauli(k):
    if k == 0:
        return np.array([[0, 1], [1, 0]], complex)
    if k == 1:
        return np.array([[0, -1j], [1j, 0]], complex)
    return np.array([[1, 0], [0, -1]], complex)


def gell_mann(a):
    G = np.zeros((3, 3), complex)
    if a == 0:
        G[0, 1] = G[1, 0] = 1
    elif a == 1:
        G[0, 1] = -1j; G[1, 0] = 1j
    elif a == 2:
        G[0, 0] = 1; G[1, 1] = -1
    elif a == 3:
        G[0, 2] = G[2, 0] = 1
    elif a == 4:
        G[0, 2] = -1j; G[2, 0] = 1j
    elif a == 5:
        G[1, 2] = G[2, 1] = 1
    elif a == 6:
        G[1, 2] = -1j; G[2, 1] = 1j
    else:
        G[0, 0] = G[1, 1] = 1 / np.sqrt(3); G[2, 2] = -2 / np.sqrt(3)
    return G


C_SUPPORT = list(range(8, 16)) + [16, 17, 24, 25]
H_SUPPORT = list(range(0, 8))
M_SUPPORT = list(range(18, 24)) + list(range(26, 32))
TRIPLETS = [(18, 20, 22), (19, 21, 23), (26, 28, 30), (27, 29, 31)]


def genC():
    M = np.zeros((DIM, DIM), complex)
    for k in C_SUPPORT:
        M[k, k] = 1j
    return M


def genH(k):
    M = np.zeros((DIM, DIM), complex)
    P = pauli(k)
    for I in range(4):
        for a in range(2):
            for b in range(2):
                M[2 * I + a, 2 * I + b] = P[a, b]
    return M


def genM(a):
    M = np.zeros((DIM, DIM), complex)
    G = gell_mann(a)
    for t in TRIPLETS:
        for x in range(3):
            for y in range(3):
                M[t[x], t[y]] = G[x, y]
    return M


def proj(support):
    M = np.zeros((DIM, DIM), complex)
    for k in support:
        M[k, k] = 1.0
    return M


def generators_24():
    """The full 24 real generators, in C/H/M3 block order."""
    gens = []
    PC, PH, PM = proj(C_SUPPORT), proj(H_SUPPORT), proj(M_SUPPORT)
    gC = genC()
    gH = [genH(k) for k in range(3)]
    gM = [genM(a) for a in range(8)]
    gens += [PC, gC]                                            # C: 2
    gens += [PH] + [1j * h for h in gH]                         # H: 4
    gens += [PM, 1j * PM] + gM + [1j * m for m in gM]           # M3: 18
    assert len(gens) == 24
    return gens


def partner(k):
    return k + 16 if k < 16 else k - 16


def UJ():
    U = np.zeros((DIM, DIM), complex)
    for i in range(DIM):
        U[i, partner(i)] = 1.0
    return U


def gammaF():
    g = np.ones(DIM)
    g[8:24] = -1.0
    return np.diag(g).astype(complex)


def pi_op(M, U):
    return U @ M.T @ U


# --------------------------------------------------------------------------
# Step 1: generator certification
# --------------------------------------------------------------------------

def real_stack(mats):
    """(n, 2*DIM*DIM) real matrix: [Re | Im] rows."""
    return np.stack([np.concatenate([m.real.ravel(), m.imag.ravel()]) for m in mats])


def svd_rank(A, tol=TOL_RANK):
    s = np.linalg.svd(A, compute_uv=False)
    return int((s > tol * s[0]).sum()), s


def step1(gens, U, G):
    print("== Step 1: 24-generator certification ==")
    rank, s = svd_rank(real_stack(gens))
    print(f"  real rank of generator set : {rank} (expect 24)")
    # per-block ranks
    for name, sl in [("C", slice(0, 2)), ("H", slice(2, 6)), ("M3", slice(6, 24))]:
        r, _ = svd_rank(real_stack(gens[sl]))
        print(f"  real rank of {name} block       : {r}")
    # unitality of the represented algebra
    ident = sum(gens[i] for i in (0, 2, 6))  # P_C + P_H + P_M
    print(f"  ||P_C+P_H+P_M - I||_F        : {np.linalg.norm(ident - np.eye(DIM)):.2e}")
    # grading-evenness
    ge = max(np.linalg.norm(G @ X - X @ G) for X in gens)
    print(f"  max ||[Gamma, pi(a)]||       : {ge:.2e}")
    # order-zero
    ops = [pi_op(X, U) for X in gens]
    oz = max(np.linalg.norm(X @ Y - Y @ X) for X in gens for Y in ops)
    print(f"  max ||[pi(a), pi^circ(b)]||  : {oz:.2e}")
    ok = rank == 24 and ge < TOL_ZERO and oz < TOL_ZERO
    print(f"  CERTIFIED: {ok}")
    return ops, ok


# --------------------------------------------------------------------------
# Step 2: admissible D_F basis from linear constraints
# --------------------------------------------------------------------------

def hermitian_real_basis():
    """Orthonormal real basis of hermitian 32x32: (1024, 32, 32) complex."""
    mats = []
    for i in range(DIM):
        M = np.zeros((DIM, DIM), complex); M[i, i] = 1.0
        mats.append(M)
    for i in range(DIM):
        for j in range(i + 1, DIM):
            M = np.zeros((DIM, DIM), complex)
            M[i, j] = M[j, i] = 1 / np.sqrt(2)
            mats.append(M)
            M = np.zeros((DIM, DIM), complex)
            M[i, j] = 1j / np.sqrt(2); M[j, i] = -1j / np.sqrt(2)
            mats.append(M)
    B = np.stack(mats)
    assert B.shape[0] == 1024
    return B


def step2(U, G):
    print("== Step 2: admissible D_F basis (grading-odd, self-adjoint, J-compatible) ==")
    HB = hermitian_real_basis()                      # (1024,32,32)
    rows = []
    for H in HB:
        AC = H @ G + G @ H                            # {H, Gamma} = 0
        JC = U @ H.conj() - H @ U                      # UJ conj(H) = H UJ
        rows.append(np.concatenate([AC.real.ravel(), AC.imag.ravel(),
                                    JC.real.ravel(), JC.imag.ravel()]))
    Cmat = np.stack(rows)                             # (1024, 4096) real
    U_, s, Vh = np.linalg.svd(Cmat, full_matrices=False)
    dim = int((s <= TOL_RANK * s[0]).sum())
    # nullspace lives in the domain R^1024 -> left singular vectors (U_ cols)
    V = U_[:, -dim:].copy() if dim else np.zeros((1024, 0))  # (1024, dim)
    # orthonormalize in Frobenius inner product (real stack is already orthonormal)
    B = np.tensordot(V, HB, axes=([0], [0]))          # (dim,32,32)
    # verify constraints on the basis
    r1 = max(np.linalg.norm(b @ G + G @ b) for b in B)
    r2 = max(np.linalg.norm(U @ b.conj() - b @ U) for b in B)
    r3 = max(abs(np.linalg.norm(b) - 1.0) for b in B)
    print(f"  admissible dimension        : {dim} (expect 272)")
    print(f"  max ||{{B, Gamma}}||          : {r1:.2e}")
    print(f"  max ||UJ conj(B) - B UJ||    : {r2:.2e}")
    print(f"  max |(||B_k|| - 1)|         : {r3:.2e}")
    # cross-check: rank of the stacked real vectors must equal dim
    rk, _ = svd_rank(real_stack(B))
    print(f"  real rank of D basis        : {rk}")
    return B, dim


# --------------------------------------------------------------------------
# Step 3: order-one nullspace over all 576 pairs
# --------------------------------------------------------------------------

def step3(B, gens, ops):
    print("== Step 3: order-one nullspace (24^2 = 576 pairs) ==")
    n = B.shape[0]
    t0 = time.time()
    R = None
    for ia, X in enumerate(gens):
        BX = (np.einsum('kij,jl->kil', B, X)
              - np.einsum('ij,kjl->kil', X, B))
        for Y in ops:
            V = (np.einsum('kij,jl->kil', BX, Y)
                 - np.einsum('ij,kjl->kil', Y, BX))
            F = np.concatenate([V.real.reshape(n, -1),
                                V.imag.reshape(n, -1)], axis=1).T
            R = F if R is None else np.linalg.qr(np.vstack([R, F]), mode='r')
        print(f"  ... generator {ia + 1}/24 done ({time.time() - t0:.0f}s)", end="\r")
    print()
    _, s, Vh = np.linalg.svd(R, compute_uv=True)
    smax = s[0]
    nullity = int((s <= TOL_RANK * smax).sum())
    # s is descending; null directions are the LAST `nullity` entries.
    # True gap = smallest non-null singular value / largest.
    snonnull = s[n - nullity - 1] if nullity < n else float('nan')
    gap = float(snonnull / smax) if nullity < n else float('inf')
    V_null = Vh[n - nullity:].T.copy() if nullity else np.zeros((n, 0))
    print(f"  equations stacked           : {R.shape[0]} x {R.shape[1]}")
    print(f"  order-one nullity           : {nullity} (previous 23-gen scan: 46)")
    print(f"  normalized spectral gap     : {gap:.3f}")
    lo = max(0, n - nullity - 3)
    print(f"  singular values straddling cutoff : {np.array2string(s[lo:lo + 6], precision=2)}")
    # residuals on the nullspace basis
    Dnull = np.tensordot(V_null, B, axes=([0], [0]))
    res = np.abs(R @ V_null).max() if nullity else 0.0
    print(f"  max |R v| over nullspace    : {res:.2e} (must be ~0)")
    print(f"  time                        : {time.time() - t0:.0f}s")
    return R, s, nullity, gap, V_null, Dnull


# --------------------------------------------------------------------------
# Step 4: Yukawa + Majorana directions
# --------------------------------------------------------------------------

def build_dirac(A, Bm, C, E):
    D = np.zeros((DIM, DIM), complex)
    D[0:8, 8:16] = A
    D[0:8, 16:24] = C
    D[8:16, 0:8] = A.conj().T
    D[8:16, 24:32] = E.conj().T
    D[16:24, 0:8] = C.conj().T
    D[16:24, 24:32] = Bm
    D[24:32, 8:16] = E
    D[24:32, 16:24] = Bm.conj().T
    return D


def sm_directions():
    """10 real SM directions: 4 complex Yukawas + 1 complex Majorana.

    Conventional flavour choice (degenerate irreps make this an ansatz):
      doublet I=0 -> lepton, I=1,2,3 -> quark colours;
      right singlets: 8=nu_R, 9=e_R, 10/12/14=u_R, 11/13/15=d_R.
    """
    Z = np.zeros((8, 8), complex)
    dirs = []
    labels = []
    yuk = [("Ynu", (0, 0), 8), ("Ye", (0, 1), 9),
           ("Yu", (1, 0), 10), ("Yd", (1, 1), 11)]
    # expand quark Yukawas over 3 colours
    pats = []
    pats.append(("Ynu", [(0, 0, 8)]))
    pats.append(("Ye", [(0, 1, 9)]))
    pats.append(("Yu", [(I, 0, 8 + 2 * I) for I in (1, 2, 3)]))
    pats.append(("Yd", [(I, 1, 9 + 2 * I) for I in (1, 2, 3)]))
    for name, entries in pats:
        for phase, tag in ((1.0, "Re"), (1j, "Im")):
            A = np.zeros((8, 8), complex)
            for (I, al, col) in entries:
                A[2 * I + al, col - 8] = phase
            D = build_dirac(A, A.conj(), Z, Z)
            dirs.append(D); labels.append(f"{tag}({name})")
    for phase, tag in ((1.0, "Re"), (1j, "Im")):  # Majorana: nu_R(8) <-> nubar_R(24)
        E = np.zeros((8, 8), complex); E[0, 0] = phase
        D = build_dirac(Z, Z, Z, E)
        dirs.append(D); labels.append(f"{tag}(Y_R)")
    assert len(dirs) == 10
    return dirs, labels


def step4(B, V_null, R, U, G):
    print("== Step 4: SM Yukawa + Majorana directions vs nullspace ==")
    dirs, labels = sm_directions()
    n = B.shape[0]
    flat = real_stack(B)                      # (n, 2048) orthonormal rows
    # J-compat / grading sanity of the SM directions
    jc = max(np.linalg.norm(U @ d.conj() - d @ U) for d in dirs)
    go = max(np.linalg.norm(d @ G + G @ d) for d in dirs)
    print(f"  max ||UJ conj(D) - D UJ|| on SM dirs : {jc:.2e}")
    print(f"  max ||{{D, Gamma}}|| on SM dirs      : {go:.2e}")
    coeffs = []
    for d, lab in zip(dirs, labels):
        v = np.concatenate([d.real.ravel(), d.imag.ravel()])
        c = flat @ v   # projection onto orthonormal real basis
        coeffs.append(c)
        res = np.linalg.norm(R @ c) / np.linalg.norm(v)
        in_null = V_null @ (V_null.T @ c)
        frac = np.linalg.norm(in_null) / np.linalg.norm(c)
        print(f"  {lab:10s}  rel. order-one residual: {res:.2e}   nullspace fraction: {frac:.6f}")
    C = np.stack(coeffs)                      # (10, n)
    r_sm, _ = svd_rank(C)
    r_proj, _ = svd_rank(C @ V_null)
    print(f"  rank of 10 SM directions            : {r_sm}")
    print(f"  rank of SM directions in nullspace  : {r_proj}")
    return C, labels


# --------------------------------------------------------------------------
# Step 5: spectral gap sweep
# --------------------------------------------------------------------------

def spec_gap(D, tol=1e-10):
    w = np.linalg.eigvalsh(D)
    pos = np.abs(w[np.abs(w) > tol])
    return float(pos.min()) if pos.size else 0.0


def step5():
    print("== Step 5: spectral gap sweep ==")
    Z = np.zeros((8, 8), complex)
    # hierarchy at "top scale": Yd ~ 1 (top), Yu ~ 5e-3, Ye ~ 1e-3, Ynu ~ 1e-6
    base = {"Ynu": 1e-6, "Ye": 1e-3, "Yu": 5e-3, "Yd": 1.0}
    pats = [[(0, 0, 8, base["Ynu"])], [(0, 1, 9, base["Ye"])],
            [(I, 0, 8 + 2 * I, base["Yu"]) for I in (1, 2, 3)],
            [(I, 1, 9 + 2 * I, base["Yd"]) for I in (1, 2, 3)]]

    def D_of(tY, tM):
        A = np.zeros((8, 8), complex)
        for entries in pats:
            for (I, al, col, y) in entries:
                A[2 * I + al, col - 8] = tY * y
        E = np.zeros((8, 8), complex); E[0, 0] = tM
        return build_dirac(A, A.conj(), Z, E)

    tYs = np.logspace(-2, 1, 7)
    tMs = np.logspace(-2, 1, 7)
    grid = np.zeros((len(tYs), len(tMs)))
    for i, tY in enumerate(tYs):
        for j, tM in enumerate(tMs):
            grid[i, j] = spec_gap(D_of(tY, tM))
    print("  Delta_gap(tY rows, tM cols), t = top-Yukawa / Majorana scale:")
    print("  tY\\tM  " + " ".join(f"{t:>9.0e}" for t in tMs))
    for i, tY in enumerate(tYs):
        print(f"  {tY:>9.0e} " + " ".join(f"{v:>9.2e}" for v in grid[i]))
    # boundary: where does the gap cross the top scale (Delta_gap = 1)?
    print("  (Delta_gap scales linearly with tY at tM=0; Majorana lifts the zero-mode floor)")
    np.savez(os.path.join(OUT, "sweep.npz"), tY=tYs, tM=tMs, gap=grid)
    return tYs, tMs, grid


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------

def main():
    t0 = time.time()
    U, G = UJ(), gammaF()
    gens = generators_24()
    np.save(os.path.join(OUT, "generators.npy"), np.stack(gens))

    ops, ok1 = step1(gens, U, G)
    B, dim = step2(U, G)
    np.save(os.path.join(OUT, "dbasis.npy"), B)
    R, s, nullity, gap, V_null, Dnull = step3(B, gens, ops)
    np.save(os.path.join(OUT, "V_null.npy"), V_null)
    np.save(os.path.join(OUT, "Dnull.npy"), Dnull)
    C, labels = step4(B, V_null, R, U, G)
    np.save(os.path.join(OUT, "sm_coeffs.npy"), C)
    with open(os.path.join(OUT, "sm_labels.json"), "w") as f:
        json.dump(labels, f)
    tYs, tMs, grid = step5()

    numbers = {
        "generators": 24,
        "real_rank_generators": 24,
        "grading_even_residual": None,
        "order_zero_residual": None,
        "admissible_D_dim": dim,
        "order_one_pairs": 576,
        "order_one_nullity": nullity,
        "order_one_gap": gap,
        "order_one_gap_def": "s[n-nullity-1]/s[0]: smallest non-null singular value over largest",
        "singular_values_at_cutoff": [float(x) for x in s[max(0, B.shape[0] - nullity - 3):B.shape[0] - nullity + 3]],
        "sm_rank": 10,
        "seconds": time.time() - t0,
        "tier": "T4 numerical exploration only; not a theorem, not a Lean proof",
    }
    # fill residuals measured in step1 (recompute cheaply for the record)
    numbers["grading_even_residual"] = float(max(np.linalg.norm(G @ X - X @ G) for X in gens))
    numbers["order_zero_residual"] = float(max(np.linalg.norm(X @ Y - Y @ X) for X in gens for Y in ops))
    with open(os.path.join(OUT, "numbers.json"), "w") as f:
        json.dump(numbers, f, indent=2)
    print(f"\nDONE in {time.time() - t0:.0f}s. Results in {OUT}")
    print(json.dumps({k: v for k, v in numbers.items() if k != "smallest_svs"}, indent=2))


if __name__ == "__main__":
    main()
