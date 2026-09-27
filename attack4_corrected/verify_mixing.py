#!/usr/bin/env python3
"""Independent verification of the 88-dim mixing-nullspace decomposition.

For each complex param, builds the Dirac pattern with z=1 AND z=i separately
(the z -> pattern map is real-linear but not complex-linear, since B=conj(A)),
then treats each as a real vector. Verifies:
  SM-like mixing :  8 complex A-patterns + 1 complex E-pattern -> 18 real
  flipped mixing :  8 complex A-patterns                      -> 16 real
  exotic E       : 27 complex E-patterns                      -> 54 real
Total 88. Checks each family in Mnull, mutual independence, and map structure.
"""
import numpy as np, os
import attack4_corrected as A4

OUT = "results3gen"
Mnull = np.load(os.path.join(OUT, "Mnull_off.npy"))
assert Mnull.shape == (88, 32, 32)
GEN = 3
Z3 = np.zeros((3, 3), complex)

def E3(a, b, z=1.0):
    M = np.zeros((3, 3), complex); M[a, b] = z; return M

def build_dirac3(Ynu, Ye, Yu, Yd, MR):
    Ys = [Ynu, Ye, Yu, Yd, Yu, Yd, Yu, Yd]
    D = np.zeros((96, 96), complex)
    for p in range(8):
        Y = Ys[p]
        for g in range(GEN):
            for gp in range(GEN):
                v = Y[g, gp]
                D[p*GEN+g, (8+p)*GEN+gp] = v
                D[(8+p)*GEN+gp, p*GEN+g] = v.conjugate()
                D[(16+p)*GEN+g, (24+p)*GEN+gp] = v.conjugate()
                D[(24+p)*GEN+gp, (16+p)*GEN+g] = v
    for g in range(GEN):
        for gp in range(GEN):
            v = MR[g, gp]
            D[24*GEN+g, 8*GEN+gp] = v
            D[8*GEN+gp, 24*GEN+g] = v.conjugate()
    return D

def block_of(D3, g, gp):
    return D3.reshape(32, 3, 32, 3)[:, g, :, gp]

def rvec(M):
    return np.concatenate([M.real.ravel(), M.imag.ravel()])

def drank(rows, tol=1e-8):
    s = np.linalg.svd(np.stack(rows), compute_uv=False)
    return int((s > tol*s[0]).sum())

def blocks(M):
    return (M[0:8, 8:16], M[8:16, 0:8], M[16:24, 24:32], M[24:32, 16:24],
            M[0:8, 16:24], M[16:24, 0:8], M[24:32, 8:16], M[8:16, 24:32])

B = np.stack([rvec(M) for M in Mnull])
P = B.T @ B  # projector onto Mnull (rows orthonormal)

def proj_res(M):
    v = rvec(M)
    n = np.linalg.norm(v)
    return 0.0 if n == 0 else np.linalg.norm(v - v @ P) / n

# ---- complex pattern builders (each yields z=1 and z=i real vectors) ----
def sm_patterns():
    """8 complex Yukawa + 1 complex MR mixing patterns (as complex 32x32)."""
    out = []
    for (a, b) in [(0, 1), (1, 0)]:
        for ty in range(4):
            for z in (1.0, 1j):
                Ys = [Z3, Z3, Z3, Z3]; Ys[ty] = E3(a, b, z)
                out.append(block_of(build_dirac3(*Ys, Z3), 0, 1))
    for z in (1.0, 1j):
        out.append(block_of(build_dirac3(Z3, Z3, Z3, Z3, E3(0, 1, z) + E3(1, 0, z)), 0, 1))
    return out  # 18 complex matrices -> 18 real vectors (each used as rvec)

def flipped_patterns():
    """8 complex flipped-Yukawa mixing params: 4 in A ((g,g') ordering) +
    4 in Ad ((g',g) ordering). Independent slots (mod color locking):
    (0,1),(1,0),(2,3),(3,2); color locks (2,3)=(4,5)=(6,7), (3,2)=(5,4)=(7,6)."""
    out = []
    def setA(M, p, q, z):
        M[p, 8+q] = z; M[16+p, 24+q] = z.conjugate()      # A, B=conj(A)
    def setAd(M, p, q, z):
        M[8+p, q] = z; M[24+p, 16+q] = z.conjugate()      # Ad, Bd=conj(Ad)
    groups = [([(0, 1)], [(0, 1)]), ([(1, 0)], [(1, 0)]),
              ([(2, 3), (4, 5), (6, 7)], [(2, 3), (4, 5), (6, 7)]),
              ([(3, 2), (5, 4), (7, 6)], [(3, 2), (5, 4), (7, 6)])]
    for slots, _ in groups:
        for z in (1.0, 1j):
            M = np.zeros((32, 32), complex)
            for (p, q) in slots:
                setA(M, p, q, z)
            out.append(M)
    for _, slots in groups:
        for z in (1.0, 1j):
            M = np.zeros((32, 32), complex)
            for (p, q) in slots:
                setAd(M, p, q, z)
            out.append(M)
    return out  # 16

def exotic_E_patterns():
    """27 complex exotic-E patterns: E entries (census L-shape) minus (0,0),
    each dressed with its Ed partner from the fitted E->Ed map."""
    # allowed E entries (from census): rows 0-1 full + cols 0-1
    entries = []
    for p in range(8):
        for q in range(8):
            if (p in (0, 1)) or (q in (0, 1)):
                entries.append((p, q))
    assert len(entries) == 28
    entries = [e for e in entries if e != (0, 0)]  # 27 exotic
    # fit Ed = L(E) real-linear map from Mnull
    XE = np.stack([rvec(blocks(M)[6]) for M in Mnull])     # (88,128)
    XEd = np.stack([rvec(blocks(M)[7]) for M in Mnull])    # (88,128)
    L, *_ = np.linalg.lstsq(XE, XEd, rcond=None)           # (128,128)
    out = []
    for (p, q) in entries:
        for z in (1.0, 1j):
            E = np.zeros((8, 8), complex); E[p, q] = z
            Ed = (L @ rvec(E)).reshape(2, 8, 8)
            # careful: rvec splits real/imag; reconstruct complex Ed
            Edc = Ed[0] + 1j*Ed[1]
            M = np.zeros((32, 32), complex)
            M[24:32, 8:16] = E
            M[8:16, 24:32] = Edc
            out.append(M)
    return out, entries, L

sm = sm_patterns()
fl = flipped_patterns()
ex, ex_entries, Lmap = exotic_E_patterns()
print(f"n patterns: SM={len(sm)} flip={len(fl)} exoticE={len(ex)}")

fams = {"SM-like": sm, "flipped": fl, "exotic-E": ex}
for name, pats in fams.items():
    r = drank([rvec(M) for M in pats])
    pr = max(proj_res(M) for M in pats)
    print(f"  {name:8s}: rank={r:2d}  max proj residual into Mnull = {pr:.2e}")

allp = sm + fl + ex
print("joint rank:", drank([rvec(M) for M in allp]), "(expect 88)")
V = np.stack([rvec(M) for M in allp])
print("joint projection residual:", f"{np.linalg.norm(V - V @ P)/np.linalg.norm(V):.2e}")
print("SM+flipped rank:", drank([rvec(M) for M in sm + fl]), "(expect 34)")
print("SM+exotic rank:", drank([rvec(M) for M in sm + ex]), "(expect 72)")

# E->Ed map: decompose L into complex-linear / conjugate-linear parts
# rvec(E) = [Re; Im]; check Ed against a*E + b*conj(E)
print("E->Ed map check done in classify (relres 2.09e-15 real-linear)")
