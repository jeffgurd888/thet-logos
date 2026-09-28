"""Stage 4: canonical full-46 structure + final verification numbers.

T4 NUMERICAL EXPLORATION ONLY. Not a theorem, not a Lean proof.
"""
import numpy as np
import os

DIM = 32
RES = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")

def main():
    Dnull = np.load(os.path.join(RES, "Dnull.npy"))    # (46,32,32)
    EE = np.load(os.path.join(RES, "EE_pure.npy"))     # (28,32,32) E-pure
    EA = np.load(os.path.join(RES, "EA_pure.npy"))     # (8,32,32) A-pure
    A = lambda D: D[0:8, 8:16]
    E = lambda D: D[24:32, 8:16]
    C = lambda D: D[0:8, 16:24]

    # canonical: image dims on full 46
    XA = np.stack([np.concatenate([A(D).real.ravel(), A(D).imag.ravel()]) for D in Dnull])
    XE = np.stack([np.concatenate([E(D).real.ravel(), E(D).imag.ravel()]) for D in Dnull])
    sA = np.linalg.svd(XA, compute_uv=False); sE = np.linalg.svd(XE, compute_uv=False)
    print(f"full-46: dim(im P_A)={int((sA>1e-8*sA[0]).sum())} (=16 expect: 8 complex), "
          f"dim(im P_E)={int((sE>1e-8*sE[0]).sum())} (=30 expect: 15 complex)")

    # quark-quark E entries on E-pure: forbidden?
    qq = max(np.abs(E(D)[p, q]) for D in EE for p in range(2, 8) for q in range(2, 8))
    print(f"max |E[p,q]| p,q in quark singlets (2..7) over E-pure: {qq:.2e} (forbidden if ~0)")
    # nuR-nuR slot on E-pure (should be 0: that's the SM slot)
    nn = max(np.abs(E(D)[0, 0]) for D in EE)
    print(f"max |E[0,0]| (nuR-nuR, SM slot) over E-pure: {nn:.2e}")
    # eR-eR present?
    ee = max(np.abs(E(D)[1, 1]) for D in EE)
    print(f"max |E[1,1]| (eR-eR Majorana) over E-pure: {ee:.2e} (>0 => present)")

    # A-block: straight vs flipped slot census on full 46
    supA = np.zeros((8, 8))
    for D in Dnull:
        supA = np.maximum(supA, np.abs(A(D)))
    print("A-block max-entry census (full 46), rows=I/A, cols=singlet:")
    for p in range(8):
        print(f"  I{p//2}a{p%2}: " + " ".join(f"{supA[p,q]:.2f}" for q in range(8)))

    # E-block census on full 46 (symmetric part)
    supE = np.zeros((8, 8))
    for D in Dnull:
        supE = np.maximum(supE, np.abs(E(D)))
    print("E-block max-entry census (full 46):")
    for p in range(8):
        print(f"  s{p}: " + " ".join(f"{supE[p,q]:.2f}" for q in range(8)))

    # C-block: identically zero?
    print(f"C-block max over full 46: {max(np.linalg.norm(C(D)) for D in Dnull):.2e}")
    print("DONE")

if __name__ == "__main__":
    main()
