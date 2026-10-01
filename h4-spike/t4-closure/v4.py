"""Compute real dimension of V4 and V4 cap order-one. Uses scipy sparse."""
import numpy as np
from scipy import sparse
from scipy.sparse.linalg import svds

N = 32
gamma = np.array([1]*8 + [-1]*8 + [-1]*8 + [1]*8)
S = set(list(range(18)) + [24, 25])
cf = np.array([1 if i in S else 0 for i in range(N)])
partner = np.array([i+16 if i < 16 else i-16 for i in range(N)])

def vidx(i, j, ri):
    return (i*N + j)*2 + ri

nvars = N*N*2  # 2048
rows, cols, data = [], [], []

def add_eq(terms, rhs=0.0):
    # terms: list of (var, coeff)
    r = len(rows) and (max(r[0] for r in [rows]) if False else 0)
    rid = add_eq.counter
    add_eq.counter += 1
    for (v, c) in terms:
        rows.append(rid); cols.append(v); data.append(c)
add_eq.counter = 0

E = set(i for i in range(N) if gamma[i]==1)
O = set(i for i in range(N) if gamma[i]==-1)
allowed = set()
ES = E & S; ET = E - S; OS = O & S; OT = O - S
for i in ES:
    for j in OS: allowed.add((i,j))
for i in ET:
    for j in OT: allowed.add((i,j))
for i in OS:
    for j in ES: allowed.add((i,j))
for i in OT:
    for j in ET: allowed.add((i,j))

# 1. grading+cf: D(i,j)=0 outside allowed
for i in range(N):
    for j in range(N):
        if (i,j) not in allowed:
            add_eq([(vidx(i,j,0), 1.0)])
            add_eq([(vidx(i,j,1), 1.0)])
# 2. SA: D(i,j) = conj(D(j,i))
for i in range(N):
    for j in range(N):
        add_eq([(vidx(i,j,0), 1.0), (vidx(j,i,0), -1.0)])
        add_eq([(vidx(i,j,1), 1.0), (vidx(j,i,1), 1.0)])
# 3. J: D(i,j) = D(partner j, partner i)
for i in range(N):
    for j in range(N):
        pi, pj = partner[i], partner[j]
        add_eq([(vidx(i,j,0), 1.0), (vidx(pj,pi,0), -1.0)])
        add_eq([(vidx(i,j,1), 1.0), (vidx(pj,pi,1), -1.0)])

M = sparse.csr_matrix((data, (rows, cols)), shape=(add_eq.counter, nvars))
print("V4 constraint matrix:", M.shape, "nnz:", M.nnz)

# Nullspace via dense SVD on the constraint matrix (2048 cols is fine)
Md = M.toarray()
u, s, vh = np.linalg.svd(Md, full_matrices=True)
tol = 1e-8
rank = np.sum(s > tol)
d4 = nvars - rank
print("rank:", rank, "dim V4:", d4)
null = vh[rank:].T  # (2048, d4) real basis for V4
np.save("/tmp/dim_analysis/v4basis.npy", null)
print("saved V4 basis")
