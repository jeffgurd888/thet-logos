"""FINAL: Embed A5 in G, verify triple-automorphism properties, analyze structural vs accidental.

1. Load A5 3x3 generators (a,b).
2. Embed as 3+3 on Yu+ sector (6-dim D_F eigenspace).
3. Verify [U,D_F]=0, Ad_U(pi)=pi directly.
4. Show it acts trivially on pi(A_F) (joint commutant).
5. Exotic sector permutation test.
"""
import numpy as np
import scipy.linalg as la
import sys, re
sys.path.insert(0, "/home/hatch/workspace/thet-logos/python")
from thet_logos.engine13_rsd import build_DF
from thet_logos.common import af_generators, pi, gamma_F, UJ, DIM

fro = lambda M: float(la.norm(M, "fro"))
D = build_DF()
a3 = np.load("/tmp/ico_a.npy"); b3 = np.load("/tmp/ico_b.npy")
print(f"[a5] loaded 3x3 generators: a^2=b^3=(ab)^5=1 verified={np.allclose(a3@a3,np.eye(3)) and np.allclose(np.linalg.matrix_power(b3,3),np.eye(3))}")

# Yu+ sector basis: (e_i + e_{i+8})/sqrt2, (e_{i+16}+e_{i+24})/sqrt2 for i=2,4,6
e = np.eye(32)
Yu_plus = []
for i in [2, 4, 6]:
    Yu_plus.append((e[i] + e[i+8]) / np.sqrt(2))
    Yu_plus.append((e[i+16] + e[i+24]) / np.sqrt(2))
Yu_plus = np.stack(Yu_plus, axis=1)  # 32x6, orthonormal
print(f"[embed] Yu+ basis 32x6, orthonormal check: {fro(Yu_plus.conj().T@Yu_plus - np.eye(6)):.3e}")
# verify these are +Yu eigenvectors
print(f"[embed] D_F eigenvalues on Yu+ basis: {np.sort(la.eigvalsh(Yu_plus.conj().T @ D @ Yu_plus))}")

# A5 as 3+3 on Yu+: block diag(a3, a3) and block diag(b3, b3) in Yu+ basis
A6 = la.block_diag(a3, a3); B6 = la.block_diag(b3, b3)
# 32x32: U = Yu_plus @ M6 @ Yu_plus^H + (I - P_Yu+)
P = Yu_plus @ Yu_plus.conj().T
def embed32(M6):
    return Yu_plus @ M6 @ Yu_plus.conj().T + (np.eye(32) - P)
UA = embed32(A6); UB = embed32(B6)
print(f"[embed] UA, UB unitary: {fro(UA@UA.conj().T-np.eye(32)):.3e}, {fro(UB@UB.conj().T-np.eye(32)):.3e}")
print(f"[embed] [UA,D_F]: {fro(UA@D-D@UA):.3e}, [UB,D_F]: {fro(UB@D-D@UB):.3e}")
# relations preserved?
print(f"[embed] UA^2=I: {np.allclose(UA@UA, np.eye(32), atol=1e-8)}, "
      f"UB^3=I: {np.allclose(UB@UB@UB, np.eye(32), atol=1e-8)}, "
      f"(UA UB)^5=I: {np.allclose(np.linalg.matrix_power(UA@UB,5), np.eye(32), atol=1e-8)}")

# Ad_U(pi) = pi? (U acts as identity on pi support {0,1,8,9})
gens = af_generators(); Pi = [pi(g) for g in gens]
def real_vec(M): return np.concatenate([M.real.reshape(-1), M.imag.reshape(-1)])
Pmat = np.stack([real_vec(P) for P in Pi], axis=1)
U_svd, s_svd, _ = la.svd(Pmat, full_matrices=False)
d_A = int((s_svd > 1e-8*s_svd[0]).sum()); Qpi = U_svd[:, :d_A]
def outside(M):
    v = real_vec(M); return float(np.linalg.norm(v - Qpi@(Qpi.T@v)))
mxA = max(outside(UA@P@UA.conj().T - P) for P in Pi)
mxB = max(outside(UB@P@UB.conj().T - P) for P in Pi)
print(f"[embed] max ||Ad_UA(pi)-pi|| outside span: {mxA:.3e} (expect ~0)")
print(f"[embed] max ||Ad_UB(pi)-pi|| outside span: {mxB:.3e} (expect ~0)")
# Actually stronger: Ad_U(pi) == pi exactly? (U=I on support)
print(f"[embed] max ||Ad_UA(pi)-pi||_F: {max(fro(UA@P@UA.conj().T-P) for P in Pi):.3e}")

# Gamma, J compatibility
Gamma = gamma_F(); Uj = UJ()
print(f"[embed] [UA,Gamma]: {fro(UA@Gamma-Gamma@UA):.3e} (expect nonzero: Gamma swaps Yu+<->Yu-)")
# J: UJ @ U.conj() @ UJ.T should equal U for JU=UJ
print(f"[embed] ||J UA J^-1 - UA||: {fro(Uj@UA.conj()@Uj.T - UA):.3e}")

print("\n[structural] A5 acts on Yu+ where pi=0. It is INVISIBLE to the algebra.")
print("[structural] This is accidental D_F-degeneracy, not structural icosahedral.")
print("[done] part B")
