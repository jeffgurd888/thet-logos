"""AUTOMORPHISM HUNT — does Aut(A_F, H_F, D_F) contain I_h or 2I?

Tier T4 numerical. Well-posed question, no ontological claims.

G = {U in U(32) : [U, D_F] = 0, Ad_U(pi(A_F)) = pi(A_F)}
(the triple automorphisms: unitaries preserving D_F and the algebra rep).

Steps:
  1. D_F spectral structure (eigensectors, multiplicities).
  2. Commutant of D_F: complex dim = sum m^2; unitary commutant Lie algebra.
  3. Normalizer Lie algebra: X anti-Hermitian, [X,D_F]=0,
     [X, pi(g)] in span_R{pi} for all generators g.
  4. Icosahedral hunt on the resulting group.
"""
import numpy as np
import scipy.linalg as la
import os, sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "python"))
from thet_logos.engine13_rsd import build_DF
from thet_logos.common import af_generators, pi, gamma_F, UJ, DIM

SEED = 2026
rng = np.random.default_rng(SEED)
fro = lambda M: float(la.norm(M, "fro"))

D = build_DF()
print(f"[setup] ||D_F|| = {fro(D):.6g} GeV (expect ~228.78 for Yu block)")

# ---------------------------------------------------------------- 1. spectrum
evals, evecs = la.eigh(D)
# cluster
tol = 1e-6
clusters = []  # (value, multiplicity, indices)
i = 0
while i < len(evals):
    j = i
    while j + 1 < len(evals) and abs(evals[j + 1] - evals[i]) < tol:
        j += 1
    clusters.append((float(evals[i]), j - i + 1, list(range(i, j + 1))))
    i = j + 1
print("[1] D_F distinct eigenvalues (GeV) and multiplicities:")
tot = 0
for val, m, _ in clusters:
    print(f"    lambda = {val:+.6f}   mult = {m}")
    tot += m
print(f"    total dim = {tot}")
comm_cdim = sum(m * m for _, m, _ in clusters)
print(f"[1] commutant(D_F) complex-dim = sum m^2 = {comm_cdim}")
print(f"[1] unitary commutant real-dim = {comm_cdim} "
      f"(U({')xU('.join(str(m) for _, m, _ in clusters)}))")

# sector projectors
sectors = []
for val, m, idxs in clusters:
    P = (evecs[:, idxs] @ evecs[:, idxs].conj().T)
    sectors.append((val, m, P))

# ------------------------------------------------- 2. commutant Lie algebra
# anti-Hermitian basis block-diagonal across sectors
u_basis = []  # list of 32x32 anti-Hermitian, [B, D] = 0
for val, m, idxs in clusters:
    V = evecs[:, idxs]  # 32 x m
    # u(m) basis embedded: i*E_jj, (E_jk - E_kj), i*(E_jk + E_kj)
    for j in range(m):
        B = np.zeros((DIM, DIM), complex)
        E = np.zeros((m, m), complex); E[j, j] = 1j
        B = V @ E @ V.conj().T
        u_basis.append(B)
    for j in range(m):
        for k in range(j + 1, m):
            E = np.zeros((m, m), complex); E[j, k] = 1; E[k, j] = -1
            u_basis.append(V @ E @ V.conj().T)
            E = np.zeros((m, m), complex); E[j, k] = 1j; E[k, j] = 1j
            u_basis.append(V @ E @ V.conj().T)
n_u = len(u_basis)
print(f"[2] anti-Hermitian commutant basis: {n_u} (expect {comm_cdim})")
# verify [B, D] = 0
mx = max(fro(B @ D - D @ B) for B in u_basis)
print(f"[2] max ||[B_k, D_F]|| = {mx:.3e}")
# verify anti-Hermitian
mx2 = max(fro(B + B.conj().T) for B in u_basis)
print(f"[2] max ||B + B^H|| = {mx2:.3e}")

# ------------------------------------------------- 3. pi(A_F) real span
gens = af_generators()
Pi = [pi(g) for g in gens]
# real span via stacking [Re; Im]
def real_vec(M):
    return np.concatenate([M.real.reshape(-1), M.imag.reshape(-1)])
Pmat = np.stack([real_vec(P) for P in Pi], axis=1)  # (2048, 24)
U_svd, s_svd, _ = la.svd(Pmat, full_matrices=False)
d_A = int((s_svd > 1e-8 * s_svd[0]).sum())
print(f"[3] pi(A_F): {len(gens)} generators, real-span dim = {d_A}")
# orthonormal real basis for span{pi}
Qpi = U_svd[:, :d_A]
# complement basis
Qc = U_svd[:, d_A:]
print(f"[3] complement real-dim = {Qc.shape[1]}")

def in_span(M):
    v = real_vec(M)
    return float(la.norm(Qc.T @ v))

# sanity: each generator in span
print(f"[3] max generator complement-residual = "
      f"{max(in_span(P) for P in Pi):.3e}")

# ------------------------------------------------- 4. normalizer Lie algebra
# X = sum_k c_k B_k; require [X, pi(g_i)] in span_R(pi) for all i.
# Constraint rows: Re Tr(C_m^dagger [B_k, pi(g_i)]) = 0, C_m = complement basis
# vectorized as real vectors.
n_c = Qc.shape[1]
n_g = len(Pi)
# Build constraint matrix: rows = (m, i), cols = k
# [B_k, P_i] as real vector; take inner product with each complement dir.
rows = []
for i, P in enumerate(Pi):
    for m in range(n_c):
        # row_k = Re Tr( C_m^dagger [B_k, P] ), C_m unvectorized from Qc[:, m]
        cm = Qc[:, m]
        Cr = cm[:1024].reshape(DIM, DIM); Ci = cm[1024:].reshape(DIM, DIM)
        C = Cr + 1j * Ci
        row = np.array([float((C.conj() * (B @ P - P @ B)).sum().real)
                        for B in u_basis])
        rows.append(row)
Mcon = np.stack(rows, axis=0)
print(f"[4] constraint matrix: {Mcon.shape} "
      f"({n_g} gens x {n_c} complement dirs, {n_u} unknowns)")
s_c = la.svd(Mcon, compute_uv=False)
gap_idx = n_u - 1
ss = np.sort(s_c)
# nullity = # singular values below tol
tol_n = 1e-6 * (ss[-1] if len(ss) else 1.0)
nullity = int((s_c < tol_n).sum())
print(f"[4] singular values: max={ss[-1]:.3e}, "
      f"s[{nullity}]={ss[nullity] if nullity < len(ss) else float('nan'):.3e} "
      f"(tol={tol_n:.3e})")
print(f"[4] NORMALIZER Lie algebra real-dim n_G = {nullity}")
# nullspace basis
_, _, Vh = la.svd(Mcon, full_matrices=True)
null_basis_coeffs = Vh[nullity and -(nullity):] if nullity else np.zeros((0, n_u))
# careful: Vh rows are right singular vectors; nullspace = last `nullity` rows
if nullity:
    Nvecs = Vh[-nullity:, :]
    # build Lie algebra basis matrices
    g_basis = [sum(c * B for c, B in zip(row, u_basis)) for row in Nvecs]
    # verify constraints
    worst = 0.0
    for X in g_basis:
        for P in Pi:
            worst = max(worst, in_span(X @ P - P @ X) / max(fro(P), 1e-300))
    print(f"[4] verification: max relative [X,pi]-outside-span residual = {worst:.3e}")
    # verify [X, D] = 0 and anti-Hermitian
    print(f"[4] max ||[X,D]|| = {max(fro(X @ D - D @ X) for X in g_basis):.3e}, "
          f"max ||X+X^H|| = {max(fro(X + X.conj().T) for X in g_basis):.3e}")
    # structure: derived algebra? compute [g,g] dim to see abelian-ness
    comms = []
    for a in range(nullity):
        for b in range(a + 1, nullity):
            comms.append(g_basis[a] @ g_basis[b] - g_basis[b] @ g_basis[a])
    if comms:
        Cmat = np.stack([real_vec(C) for C in comms], axis=1)
        # project onto g_basis span
        Gmat = np.stack([real_vec(X) for X in g_basis], axis=1)
        Qg, _ = la.qr(Gmat, mode="economic")
        proj = Qg @ (Qg.T @ Cmat)
        resid = Cmat - proj
        rel = float(la.norm(resid) / max(float(la.norm(Cmat)), 1e-300))
        # dim of [g,g] within g
        scc = la.svd(proj, compute_uv=False)
        d_der = int((scc > 1e-8 * (scc[0] if len(scc) else 1)).sum())
        print(f"[4] [g,g] closure residual (relative) = {rel:.3e}; "
              f"dim[g,g] = {d_der} of {nullity} "
              f"({'abelian' if d_der == 0 else 'non-abelian'})")
else:
    g_basis = []
    print("[4] normalizer is trivial (only zero)")

# J and Gamma compatibility spot checks
Gamma = gamma_F(); Uj = UJ()
print(f"[x] ||[Gamma, D_F]|| = {fro(Gamma @ D - D @ Gamma):.3e} "
      f"(expect nonzero: anticommute)")
print(f"[x] ||{{Gamma, D_F}}|| = {fro(Gamma @ D + D @ Gamma):.3e} (expect ~0)")
# J as antilinear: check J D = D J via UJ conjugation on the matrix level
# J M J^-1 = UJ M* UJ^T; D real? check UJ D.conj() UJ.T vs D
JD = Uj @ D.conj() @ Uj.T
print(f"[x] ||J D J^-1 - D|| = {fro(JD - D):.3e} (0 => JD=DJ as operators)")

print("[done] part A complete")
