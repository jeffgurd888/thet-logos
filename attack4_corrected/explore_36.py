"""Stage 1 exploration: project out the 10 SM directions from the 46-dim
order-one nullspace and characterize the remaining 36.

T4 NUMERICAL EXPLORATION ONLY. Not a theorem, not a Lean proof.
"""
import numpy as np
import os

DIM = 32
RES = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")

def frob(A, B):
    return np.vdot(A, B).real  # real inner product on complex matrices

def main():
    Dnull = np.load(os.path.join(RES, "Dnull.npy"))          # (46,32,32)
    dbasis = np.load(os.path.join(RES, "dbasis.npy"))        # (272,32,32)
    sm_coeffs = np.load(os.path.join(RES, "sm_coeffs.npy"))  # (10,272)
    gens = np.load(os.path.join(RES, "generators.npy"))      # (24,32,32)
    print("shapes:", Dnull.shape, dbasis.shape, sm_coeffs.shape, gens.shape)

    # reconstruct SM direction matrices
    SM = np.tensordot(sm_coeffs, dbasis, axes=([1], [0]))    # (10,32,32)
    # Gram matrix of SM dirs (should be ~identity if orthonormal)
    Gsm = np.array([[frob(a, b) for b in SM] for a in SM])
    print("SM Gram diag:", np.diag(Gsm))
    print("SM Gram offdiag max:", np.abs(Gsm - np.diag(np.diag(Gsm))).max())
    # orthonormalize SM dirs (Gram-Schmidt) to be safe
    Q = []
    for v in SM:
        w = v.copy()
        for q in Q:
            w = w - frob(w, q) * q
        n = np.sqrt(frob(w, w))
        Q.append(w / n)
    SMo = np.stack(Q)
    G2 = np.array([[frob(a, b) for b in SMo] for a in SMo])
    print("orthonormalized SM Gram offdiag max:", np.abs(G2 - np.eye(10)).max())

    # project each nullspace vector: residual after removing SM subspace
    Resid = []
    for D in Dnull:
        R = D.copy()
        for q in SMo:
            R = R - frob(R, q) * q
        Resid.append(R)
    Resid = np.stack(Resid)  # (46,32,32)
    # rank of residuals -> expect 36
    X = np.stack([np.concatenate([r.real.ravel(), r.imag.ravel()]) for r in Resid])
    s = np.linalg.svd(X, compute_uv=False)
    print("residual singular values (top 12):", np.array2string(s[:12], precision=3))
    print("residual singular values (last 12):", np.array2string(s[-12:], precision=3))
    rank36 = int((s > 1e-8 * s[0]).sum())
    print("rank of SM-orthogonal complement:", rank36, "(expect 36)")

    # orthonormal basis for the 36-dim complement
    U_, ss, Vh = np.linalg.svd(X, full_matrices=False)
    # orthonormal basis for the 36-dim complement:
    # E_j = sum_i Vh[j,i] * Resid[i]  (Vh rows orthonormal, Resid spans the 36-dim space)
    # E_j = sum_i U_[i,j] * Resid[i]: top-36 left singular vectors as coefficients
    E36 = np.tensordot(U_[:, :36].T, Resid, axes=([1], [0]))  # (36,46)x(46,32,32) -> (36,32,32)
    # check orthonormality
    Ge = np.array([[frob(a, b) for b in E36] for a in E36])
    print("E36 Gram offdiag max:", np.abs(Ge - np.eye(36)).max())

    np.save(os.path.join(RES, "E36.npy"), E36)
    np.save(os.path.join(RES, "SMo.npy"), SMo)

    # ---- per-direction features ----
    def block(D, rs, cs):
        return D[rs[0]:rs[1], cs[0]:cs[1]]
    S = [(0, 8), (8, 16), (16, 24), (24, 32)]
    print("\n== per-direction block norms (A=[0:8,8:16], C=[0:8,16:24], E=[24:32,8:16], B=[16:24,24:32]) ==")
    print("  j :  ||A||   ||C||   ||E||   ||B-conj(A)||  rank(A) rank(C) rank(E)")
    feats = []
    for j, D in enumerate(E36):
        A = block(D, S[0], S[1]); C = block(D, S[0], S[2])
        E = block(D, S[3], S[1]); B = block(D, S[2], S[3])
        nA, nC, nE = (np.linalg.norm(M) for M in (A, C, E))
        dBA = np.linalg.norm(B - A.conj())
        rA = int((np.linalg.svd(A, compute_uv=False) > 1e-8).sum())
        rC = int((np.linalg.svd(C, compute_uv=False) > 1e-8).sum())
        rE = int((np.linalg.svd(E, compute_uv=False) > 1e-8).sum())
        feats.append((nA, nC, nE, dBA, rA, rC, rE))
        print(f"  {j:2d}: {nA:.3f}  {nC:.3f}  {nE:.3f}   {dBA:.1e}      {rA}      {rC}      {rE}")
    np.save(os.path.join(RES, "E36_feats.npy"), np.array(feats))
    print("\nDONE")

if __name__ == "__main__":
    main()
