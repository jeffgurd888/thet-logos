"""Stage 3: fine structure of the 8 A-pure and 28 E-pure directions.

T4 NUMERICAL EXPLORATION ONLY. Not a theorem, not a Lean proof.

Q5: color-locking of flipped Yukawas (fixed ratios across the 3 colors)?
Q6: phase structure: is each allowed entry a full complex dim or a real line?
Q7: is E symmetric (E = E^T) on the E-pure space?
Q8: explicit representative matrices for each family.
"""
import numpy as np
import os

DIM = 32
RES = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")

def main():
    E36 = np.load(os.path.join(RES, "E36.npy"))        # (36,32,32)
    allowA = np.load(os.path.join(RES, "allowA.npy"))
    allowE = np.load(os.path.join(RES, "allowE.npy"))
    A = lambda D: D[0:8, 8:16]
    E = lambda D: D[24:32, 8:16]

    # separate A-pure (E==0) and E-pure (A==0) via nullspaces of the projections
    XA = np.stack([np.concatenate([A(D).real.ravel(), A(D).imag.ravel()]) for D in E36])  # (36,128)
    XE = np.stack([np.concatenate([E(D).real.ravel(), E(D).imag.ravel()]) for D in E36])  # (36,128)
    _, sXA, _ = np.linalg.svd(XA, full_matrices=False)
    _, sXE, _ = np.linalg.svd(XE, full_matrices=False)
    print(f"rank XA={int((sXA>1e-8*sXA[0]).sum())} (A-coords image), rank XE={int((sXE>1e-8*sXE[0]).sum())} (E-coords image)")
    # E-pure (A=0): ker(XA) in R^36. XA=U S Vh, XA:(36,128); ker from U columns past rank.
    Ua, sa, Vha = np.linalg.svd(XA, full_matrices=False)
    rXA = int((sa > 1e-8*sa[0]).sum())
    coef_Epure = Ua[:, rXA:]          # (36, 36-rXA): each column = coeffs with zero A-part
    # A-pure (E=0): ker(XE) in R^36
    Ue, se, Vhe = np.linalg.svd(XE, full_matrices=False)
    rXE = int((se > 1e-8*se[0]).sum())
    coef_Apure = Ue[:, rXE:]          # (36, 36-rXE)
    nNullA, nNullE = coef_Epure.shape[1], coef_Apure.shape[1]
    print(f"E-pure (A=0) dim: {nNullA}, A-pure (E=0) dim: {nNullE}")
    EE = np.tensordot(coef_Epure, E36, axes=([0], [0]))  # (28,36)x(36,32,32)
    EA = np.tensordot(coef_Apure, E36, axes=([0], [0]))  # (8,36)x(36,32,32)
    # orthonormalize each family
    def orth(Ms):
        X = np.stack([np.concatenate([m.real.ravel(), m.imag.ravel()]) for m in Ms])
        Uu, ssu, _ = np.linalg.svd(X, full_matrices=False)
        r = int((ssu > 1e-10*ssu[0]).sum())
        return np.tensordot(Uu[:, :r].T, Ms, axes=([1], [0])), r
    EA, rA = orth(EA); EE, rE = orth(EE)
    print(f"orthonormalized: A-pure rank {rA}, E-pure rank {rE}")
    # verify purity
    print(f"max ||E|| on A-pure: {max(np.linalg.norm(E(D)) for D in EA):.2e}, "
          f"max ||A|| on E-pure: {max(np.linalg.norm(A(D)) for D in EE):.2e}")

    # Q6: per-entry complex span dimension in A-pure space
    print("\nQ6: A-pure entries: (p,q) | real-dim of complex values | sample values")
    entriesA = [(p, q) for p in range(8) for q in range(8) if allowA[p, q]]
    for (p, q) in entriesA:
        vals = np.array([A(D)[p, q] for D in EA])  # 8 complex numbers
        M = np.stack([vals.real, vals.imag], axis=1)  # (8,2) real
        s = np.linalg.svd(M, compute_uv=False)
        rdim = int((s > 1e-8 * s[0]).sum()) if s[0] > 0 else 0
        # dominant phase
        v = vals[np.argmax(np.abs(vals))]
        print(f"  A[{p},{q}] (I{p//2}a{p%2}->s{q}): real-dim={rdim}, max-val={v:.3f} (|.|={abs(v):.3f}, phase={np.angle(v)/np.pi:.2f}pi)")

    # Q5: color locking — ratios of the 3 color entries within each flipped family
    print("\nQ5: color-locking check (ratios should be constant across the 8-dim space):")
    # up->down family: (I1a0->s3), (I2a0->s5), (I3a0->s7)
    fams = {
        "up->down (u_L->d_R)": [(2, 3), (4, 5), (6, 7)],
        "down->up (d_L->u_R)": [(3, 2), (5, 4), (7, 6)],
    }
    for name, ents in fams.items():
        print(f"  family {name}:")
        for D in EA:
            a = A(D)
            v = [a[p, q] for (p, q) in ents]
            if max(abs(x) for x in v) > 1e-12:
                print(f"    ({v[0]:.3f}, {v[1]:.3f}, {v[2]:.3f})  ratios v1/v0={v[1]/v[0]:.3f} v2/v0={v[2]/v[0]:.3f}")
                break
        # check constancy across all 8 basis vectors
        ratios = []
        for D in EA:
            a = A(D); v = [a[p, q] for (p, q) in ents]
            if abs(v[0]) > 1e-12:
                ratios.append((v[1]/v[0], v[2]/v[0]))
        if ratios:
            r1 = np.array([r[0] for r in ratios]); r2 = np.array([r[1] for r in ratios])
            print(f"    ratio1 = {r1.mean():.4f} +/- {r1.std():.2e}, ratio2 = {r2.mean():.4f} +/- {r2.std():.2e}")

    # Q7: E symmetry
    asym = max(np.linalg.norm(E(D) - E(D).T) for D in EE)
    print(f"\nQ7: max ||E - E^T|| over E-pure: {asym:.2e} (0 => symmetric Majorana)")
    # Q6 for E entries
    print("\nQ6: E-pure entries: real-dim of complex values (expect 2 = full complex):")
    entriesE = [(p, q) for p in range(8) for q in range(8) if allowE[p, q]]
    bad = []
    for (p, q) in entriesE:
        vals = np.array([E(D)[p, q] for D in EE])
        M = np.stack([vals.real, vals.imag], axis=1)
        s = np.linalg.svd(M, compute_uv=False)
        rdim = int((s > 1e-8 * s[0]).sum()) if s[0] > 0 else 0
        if rdim != 2: bad.append((p, q, rdim))
    print(f"  entries with real-dim != 2: {bad if bad else 'NONE — all full complex'}")

    # representative: build clean representatives
    # A-pure: 4 complex flipped Yukawas. Find basis aligned to entries.
    print("\n== Clean representatives ==")
    # For A-pure: use SVD per family to get canonical directions
    print("A-pure family representatives (A-block only, showing nonzero pattern):")
    XA = np.stack([np.concatenate([A(D).real.ravel(), A(D).imag.ravel()]) for D in EA])  # (8,128)
    # The 8 entries; group into 4 complex params. Just print the entry sets per basis vector's dominant entry.
    for j, D in enumerate(EA):
        a = A(D)
        dom = [(p, q, a[p, q]) for (p, q) in entriesA if abs(a[p, q]) > 1e-10]
        print(f"  dir{j}: " + ", ".join(f"A[{p},{q}]={v:.2f}" for p, q, v in dom))

    np.save(os.path.join(RES, "EA_pure.npy"), EA)
    np.save(os.path.join(RES, "EE_pure.npy"), EE)
    print("\nDONE")

if __name__ == "__main__":
    main()
