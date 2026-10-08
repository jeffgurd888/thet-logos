"""Verify the structural kill argument for the icosahedron hunt.

Claim: for U in the normalizer G = {U:[U,D]=0, Ad_U(pi)=pi},
  (a) U preserves span{e_0, e_1} (support of the H-block),
  (b) U|_{span{e_0,e_1}} = diag(lambda, mu)  (diagonal!),
  (c) hence Ad_U on the H-block has ABELIAN image (torus),
  (d) hence any non-abelian simple S < G (e.g. A_5) acts trivially on pi(A_F).

Also verify pi(A_F) = H-block (on {0,1}) + C-block (on {8,9}).
"""
import numpy as np
import scipy.linalg as la
import os, sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "python"))
from thet_logos.engine13_rsd import build_DF
from thet_logos.common import af_generators, pi, DIM

rng = np.random.default_rng(2026)
fro = lambda M: float(la.norm(M, "fro"))
D = build_DF()

# ---- pi block structure
gens = af_generators()
Pi = [pi(g) for g in gens]
# check support: which indices ever nonzero?
supp = set()
for P in Pi:
    ii, jj = np.nonzero(np.abs(P) > 1e-12)
    supp |= set(ii.tolist()) | set(jj.tolist())
print(f"[pi] support indices: {sorted(supp)} (expect [0,1,8,9])")
# H-block: generators with q != 0 (indices 2..5 of af_generators are quat units)
# gens[0]=(1,0,0), gens[1]=(i,0,0), gens[2..5]=quat units, rest=color
Hblk = [pi(gens[k]) for k in range(2, 6)]
Cblk = [pi(gens[0]), pi(gens[1])]
print(f"[pi] H-block nonzero only on {{0,1}}: "
      f"{all(set(np.nonzero(np.abs(H)>1e-12)[0].tolist())|set(np.nonzero(np.abs(H)>1e-12)[1].tolist()) <= {0,1} for H in Hblk)}")
print(f"[pi] C-block nonzero only on {{8,9}}: "
      f"{all(set(np.nonzero(np.abs(C)>1e-12)[0].tolist())|set(np.nonzero(np.abs(C)>1e-12)[1].tolist()) <= {8,9} for C in Cblk)}")
# H-block is the quaternions on {0,1}: check it spans M_2 as complex? (it spans H)
# center of H-block: should be real scalars
# (skip detailed; the simplicity argument is standard)

# ---- build normalizer Lie algebra (reuse method), get random elements
evals, evecs = la.eigh(D)
tol = 1e-6
clusters = []
i = 0
while i < len(evals):
    j = i
    while j + 1 < len(evals) and abs(evals[j+1] - evals[i]) < tol:
        j += 1
    clusters.append((j - i + 1, list(range(i, j+1))))
    i = j + 1
u_basis = []
for m, idxs in clusters:
    V = evecs[:, idxs]
    for j in range(m):
        E = np.zeros((m, m), complex); E[j, j] = 1j
        u_basis.append(V @ E @ V.conj().T)
    for j in range(m):
        for k in range(j+1, m):
            E = np.zeros((m, m), complex); E[j, k] = 1; E[k, j] = -1
            u_basis.append(V @ E @ V.conj().T)
            E = np.zeros((m, m), complex); E[j, k] = 1j; E[k, j] = 1j
            u_basis.append(V @ E @ V.conj().T)

def real_vec(M):
    return np.concatenate([M.real.reshape(-1), M.imag.reshape(-1)])
Pmat = np.stack([real_vec(P) for P in Pi], axis=1)
U_svd, s_svd, _ = la.svd(Pmat, full_matrices=False)
d_A = int((s_svd > 1e-8 * s_svd[0]).sum())
Qc = U_svd[:, d_A:]
n_c, n_u, n_g = Qc.shape[1], len(u_basis), len(Pi)
rows = []
for P in Pi:
    for m_ in range(n_c):
        cm = Qc[:, m_]
        C = cm[:1024].reshape(DIM, DIM) + 1j * cm[1024:].reshape(DIM, DIM)
        rows.append(np.array([float((C.conj() * (B @ P - P @ B)).sum().real)
                              for B in u_basis]))
Mcon = np.stack(rows, axis=0)
_, s_c, Vh = la.svd(Mcon, full_matrices=True)
ss = np.sort(s_c)
tol_n = 1e-6 * ss[-1]
nullity = int((s_c < tol_n).sum())
Nvecs = Vh[-nullity:, :]
g_basis = [sum(c * B for c, B in zip(row, u_basis)) for row in Nvecs]
print(f"[norm] nullity = {nullity}")

# ---- test (a),(b) on random normalizer unitaries
print("[test] random U in normalizer: check U preserves span{e0,e1} and is diagonal there")
worst_pres = 0.0
worst_offd = 0.0
for trial in range(20):
    coeffs = rng.standard_normal(nullity)
    X = sum(c * B for c, B in zip(coeffs, g_basis))
    U = la.expm(X)
    # (a) U preserves span{e0,e1}: U e_0, U e_1 have no components outside {0,1}
    for idx in [0, 1]:
        v = U[:, idx]
        outside = float(np.linalg.norm(v[[i for i in range(32) if i not in (0, 1)]]))
        worst_pres = max(worst_pres, outside)
    # (b) U_01 block is diagonal: U[0,1] and U[1,0] ~ 0
    worst_offd = max(worst_offd, abs(U[0, 1]), abs(U[1, 0]))
print(f"  max ||U e_i outside {{0,1}}|| = {worst_pres:.3e} (expect ~0)")
print(f"  max |U[0,1]|,|U[1,0]| = {worst_offd:.3e} (expect ~0: diagonal)")
# (c) Ad_U on H-block is abelian: check [Ad_U1, Ad_U2] = 0 on H-block
# i.e., the induced automorphisms commute
U1 = la.expm(sum(c * B for c, B in zip(rng.standard_normal(nullity), g_basis)))
U2 = la.expm(sum(c * B for c, B in zip(rng.standard_normal(nullity), g_basis)))
def ad_on_Hblk(U):
    # returns 4x4 real matrix of Ad_U restricted to H-block basis (as real vectors)
    HB = [real_vec(H) for H in Hblk]
    # orthonormalize
    M = np.stack(HB, axis=1)
    Q, _ = la.qr(M, mode="economic")
    # Ad_U(H) projected
    cols = []
    for H in Hblk:
        AH = U @ H @ U.conj().T
        cols.append(Q.T @ real_vec(AH))
    return np.stack(cols, axis=1)
A1, A2 = ad_on_Hblk(U1), ad_on_Hblk(U2)
print(f"[test] ||[Ad_U1, Ad_U2]|| on H-block = {fro(A1@A2 - A2@A1):.3e} (expect ~0: abelian image)")
print("[done]")
