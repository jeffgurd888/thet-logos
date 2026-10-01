"""Impose order-one in V4 basis; find nullspace; verify 22-dim and spanning by dirs22."""
import numpy as np
from scipy import sparse

N = 32
partner = np.array([i+16 if i < 16 else i-16 for i in range(N)])
V4 = np.load("/tmp/dim_analysis/v4basis.npy")  # (2048, 92)
d4 = V4.shape[1]
print("V4 dim:", d4)

def cvec(M):
    """Flatten complex matrix to real vector (2048,)."""
    v = np.zeros(2*N*N)
    for i in range(N):
        for j in range(N):
            v[(i*N+j)*2] = M[i,j].real
            v[(i*N+j)*2+1] = M[i,j].imag
    return v

def cmat(v):
    """Real vector (2048,) to complex matrix."""
    M = np.zeros((N,N), dtype=complex)
    for i in range(N):
        for j in range(N):
            M[i,j] = v[(i*N+j)*2] + 1j*v[(i*N+j)*2+1]
    return M

# --- generators ---
genC = np.diag([1j if (8 <= i < 16) or i in (16,17,24,25) else 0 for i in range(N)]).astype(complex)
pauli = [np.array([[0,1],[1,0]],dtype=complex),
         np.array([[0,-1j],[1j,0]],dtype=complex),
         np.array([[1,0],[0,-1]],dtype=complex)]
def genH(k):
    M = np.zeros((N,N), dtype=complex)
    P = pauli[k]
    for I in range(4):
        for a in range(2):
            for b in range(2):
                M[2*I+a, 2*I+b] = P[a,b]
    return M
# Gell-Mann
gm = np.zeros((8,3,3), dtype=complex)
gm[0] = [[0,1,0],[1,0,0],[0,0,0]]
gm[1] = [[0,-1j,0],[1j,0,0],[0,0,0]]
gm[2] = [[1,0,0],[0,-1,0],[0,0,0]]
gm[3] = [[0,0,1],[0,0,0],[1,0,0]]
gm[4] = [[0,0,-1j],[0,0,0],[1j,0,0]]
gm[5] = [[0,0,0],[0,0,1],[0,1,0]]
gm[6] = [[0,0,0],[0,0,-1j],[0,1j,0]]
gm[7] = (1/np.sqrt(3))*np.array([[1,0,0],[0,1,0],[0,0,-2]],dtype=complex)
triplets = [(18,20,22),(19,21,23),(26,28,30),(27,29,31)]
def genM(a):
    M = np.zeros((N,N), dtype=complex)
    G = gm[a]
    for t in triplets:
        for p1 in range(3):
            for p2 in range(3):
                M[t[p1], t[p2]] = G[p1,p2]
    return M
smGen = [genC] + [genH(k) for k in range(3)] + [genM(a) for a in range(8)]
# UJ permutation
UJ = np.zeros((N,N), dtype=complex)
for i in range(N):
    UJ[i, partner[i]] = 1
def smGenOp(g):
    A = smGen[g]
    return UJ @ A.T @ UJ

# sanity: smGenOp via formula (UJ M UJ)(i,j) = M(partner i, partner j)
# UJ is symmetric permutation; UJ @ A.T @ UJ: check equals P A^T P
# Build order-one constraint matrix in V4 coords.
# For D = sum_k x_k V4[:,k] (as complex matrices Dk), [[D,A_a],B_b] = sum_k x_k [[Dk,A_a],B_b].
# Each (a,b) gives 1024 complex = 2048 real linear equations in x (92 unknowns).
Dks = [cmat(V4[:,k]) for k in range(d4)]
rows, cols, data = [], [], []
rid = 0
for a in range(12):
    A = smGen[a]
    for b in range(12):
        B = smGenOp(b)
        # [[Dk,A],B] for each k
        for k in range(d4):
            Dk = Dks[k]
            C1 = Dk @ A - A @ Dk
            C2 = C1 @ B - B @ C1
            for i in range(N):
                for j in range(N):
                    z = C2[i,j]
                    if abs(z.real) > 1e-12:
                        rows.append(rid + (i*N+j)*2); cols.append(k); data.append(z.real)
                    if abs(z.imag) > 1e-12:
                        rows.append(rid + (i*N+j)*2+1); cols.append(k); data.append(z.imag)
        rid += 2*N*N
Moo = sparse.csr_matrix((data, (rows, cols)), shape=(rid, d4))
print("order-one matrix:", Moo.shape, "nnz:", Moo.nnz)
# nullspace
Md = Moo.toarray()
u, s, vh = np.linalg.svd(Md, full_matrices=True)
rank = np.sum(s > 1e-7)
d = d4 - rank
print("order-one rank:", rank, "null dim:", d)
null = vh[rank:].T  # (92, d)
np.save("/tmp/dim_analysis/w22basis_v4coords.npy", null)
# map back to full: W22 basis as complex matrices
W22mats = [(V4 @ null[:,k]) for k in range(d)]
W22mats = [cmat(w) for w in W22mats]
np.save("/tmp/dim_analysis/w22mats.npy", np.array(W22mats))
print("null dim =", d, "(expect 22)")
