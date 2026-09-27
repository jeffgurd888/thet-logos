"""Stage 2: basis-invariant characterization of the 36-dim complement.

T4 NUMERICAL EXPLORATION ONLY. Not a theorem, not a Lean proof.

Questions:
  Q1: Is C=0 on the full 46-dim nullspace (not just the complement)?
  Q2: Does the 36-dim space split into A-type / E-type (decoupled)?
  Q3: Which (p,q) entries of the A block / E block are allowed (basis-invariant support)?
  Q4: Order-one residual of the E36 basis (direct 576-pair check).
"""
import numpy as np
import os

DIM = 32
RES = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
TOL = 1e-8

def partner(k):
    return k + 16 if k < 16 else k - 16

def UJ():
    U = np.zeros((DIM, DIM), complex)
    for i in range(DIM):
        U[i, partner(i)] = 1.0
    return U

def gammaF():
    g = np.ones(DIM); g[8:24] = -1.0
    return np.diag(g).astype(complex)

def pauli(k):
    if k == 0: return np.array([[0, 1], [1, 0]], complex)
    if k == 1: return np.array([[0, -1j], [1j, 0]], complex)
    return np.array([[1, 0], [0, -1]], complex)

def gell_mann(a):
    G = np.zeros((3, 3), complex)
    if a == 0: G[0, 1] = G[1, 0] = 1
    elif a == 1: G[0, 1] = -1j; G[1, 0] = 1j
    elif a == 2: G[0, 0] = 1; G[1, 1] = -1
    elif a == 3: G[0, 2] = G[2, 0] = 1
    elif a == 4: G[0, 2] = -1j; G[2, 0] = 1j
    elif a == 5: G[1, 2] = G[2, 1] = 1
    elif a == 6: G[1, 2] = -1j; G[2, 1] = 1j
    else: G[0, 0] = G[1, 1] = 1/np.sqrt(3); G[2, 2] = -2/np.sqrt(3)
    return G

C_SUPPORT = list(range(8, 16)) + [16, 17, 24, 25]
H_SUPPORT = list(range(0, 8))
M_SUPPORT = list(range(18, 24)) + list(range(26, 32))
TRIPLETS = [(18, 20, 22), (19, 21, 23), (26, 28, 30), (27, 29, 31)]

def genC():
    M = np.zeros((DIM, DIM), complex)
    for k in C_SUPPORT: M[k, k] = 1j
    return M

def genH(k):
    M = np.zeros((DIM, DIM), complex); P = pauli(k)
    for I in range(4):
        for a in range(2):
            for b in range(2): M[2*I+a, 2*I+b] = P[a, b]
    return M

def genM(a):
    M = np.zeros((DIM, DIM), complex); G = gell_mann(a)
    for t in TRIPLETS:
        for x in range(3):
            for y in range(3): M[t[x], t[y]] = G[x, y]
    return M

def proj(support):
    M = np.zeros((DIM, DIM), complex)
    for k in support: M[k, k] = 1.0
    return M

def generators_24():
    PC, PH, PM = proj(C_SUPPORT), proj(H_SUPPORT), proj(M_SUPPORT)
    gH = [genH(k) for k in range(3)]; gM = [genM(a) for a in range(8)]
    return [PC, genC()] + [PH] + [1j*h for h in gH] + [PM, 1j*PM] + gM + [1j*m for m in gM]

def main():
    Dnull = np.load(os.path.join(RES, "Dnull.npy"))   # (46,32,32)
    E36 = np.load(os.path.join(RES, "E36.npy"))        # (36,32,32)
    SMo = np.load(os.path.join(RES, "SMo.npy"))        # (10,32,32)
    U, G = UJ(), gammaF()
    gens = generators_24()
    ops = [U @ X.T @ U for X in gens]

    A = lambda D: D[0:8, 8:16]
    C = lambda D: D[0:8, 16:24]
    E = lambda D: D[24:32, 8:16]
    B = lambda D: D[16:24, 24:32]

    # Q1: C-block over full 46
    c46 = np.array([np.linalg.norm(C(D)) for D in Dnull])
    print(f"Q1: max ||C|| over 46 nullspace dirs: {c46.max():.2e}")
    print(f"    max ||B - conj(A)|| over 46: {max(np.linalg.norm(B(D)-A(D).conj()) for D in Dnull):.2e}")

    # Q4: direct order-one residual for E36 basis (576 pairs each -> sample all, it's cheap)
    print("Q4: direct order-one check on E36 basis...")
    worst = 0.0
    for D in E36:
        for X in gens:
            DX = D @ X - X @ D
            for Y in ops:
                r = np.linalg.norm(DX @ Y - Y @ DX)
                if r > worst: worst = r
    print(f"    max ||[[D,X],Y]]|| over 36*576 pairs: {worst:.2e}")

    # Q2: split into A-type / E-type?
    # image dimensions of projections onto A-coords and E-coords
    XA = np.stack([np.concatenate([A(D).real.ravel(), A(D).imag.ravel()]) for D in E36])
    XE = np.stack([np.concatenate([E(D).real.ravel(), E(D).imag.ravel()]) for D in E36])
    sA = np.linalg.svd(XA, compute_uv=False); sE = np.linalg.svd(XE, compute_uv=False)
    rA = int((sA > TOL*sA[0]).sum()); rE = int((sE > TOL*sE[0]).sum())
    print(f"Q2: dim(im P_A) = {rA}, dim(im P_E) = {rE}, sum = {rA+rE} (36 => decoupled: {rA+rE==36})")
    # coupling check: is there (A,E) with A=0 but E!=0 and vice versa?
    # nullspace of XA within the 36 coeffs:
    UA, sA2, _ = np.linalg.svd(XA, full_matrices=False)
    nA0 = int((sA2 <= TOL*sA2[0]).sum())
    UE, sE2, _ = np.linalg.svd(XE, full_matrices=False)
    nE0 = int((sE2 <= TOL*sE2[0]).sum())
    print(f"    # directions with A=0 (E-pure): {nA0}, # with E=0 (A-pure): {nE0}")

    # Q3: basis-invariant allowed supports
    def allowed(part_fn, name):
        M = np.zeros((8, 8))
        for D in E36:
            M = np.maximum(M, np.abs(part_fn(D)))
        allow = M > 1e-10
        print(f"Q3: allowed entries in {name} block: {allow.sum()} of 64")
        return allow, M
    allowA, magA = allowed(A, "A")
    allowE, magE = allowed(E, "E")

    print("\nAllowed A-block entries (row=doublet 2I+alpha, col=singlet):")
    print("     " + " ".join(f"s{q}" for q in range(8)))
    for p in range(8):
        I, al = p // 2, p % 2
        row = " ".join(" X" if allowA[p, q] else " ." for q in range(8))
        tag = "SM " if (p, ) in [] else ""
        print(f"  I{I}a{al}: {row}")
    print("\nAllowed E-block entries (Majorana-like, row/col = singlet index):")
    print("     " + " ".join(f"s{q}" for q in range(8)))
    for p in range(8):
        row = " ".join(" X" if allowE[p, q] else " ." for q in range(8))
        print(f"  s{p}: {row}")

    np.save(os.path.join(RES, "allowA.npy"), allowA)
    np.save(os.path.join(RES, "allowE.npy"), allowE)
    np.save(os.path.join(RES, "magA.npy"), magA)
    np.save(os.path.join(RES, "magE.npy"), magE)
    print("\nDONE")

if __name__ == "__main__":
    main()
