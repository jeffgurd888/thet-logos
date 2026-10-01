"""Nullspace via Gram matrix (92x92)."""
import numpy as np
from scipy import sparse
exec(open("/tmp/dim_analysis/orderone.py").read().split("# nullspace")[0].replace('print("order-one matrix:", Moo.shape, "nnz:", Moo.nnz)', ''))
print("order-one matrix:", Moo.shape, "nnz:", Moo.nnz)
G = (Moo.T @ Moo).toarray()  # 92x92
w, V = np.linalg.eigh(G)
print("smallest 30 eigenvalues:", np.sort(w)[:30])
rank = np.sum(w > 1e-6)
d = 92 - int(rank)
print("rank:", rank, "null dim:", d)
null = V[:, np.argsort(w)[:d]]  # (92, d)
np.save("/tmp/dim_analysis/w22basis_v4coords.npy", null)
W22mats = np.array([cmat(V4 @ null[:,k]) for k in range(d)])
np.save("/tmp/dim_analysis/w22mats.npy", W22mats)
print("null dim =", d, "(expect 22)")
# check the 22 explicit directions are in the nullspace (residual)
