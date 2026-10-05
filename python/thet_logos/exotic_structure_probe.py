"""Tier-4 probe: algebraic structure of the 12 exotic W22 directions.

Parses the explicit sparse-matrix definitions from CFKernelRetarget.lean,
then computes:
  1. Re/Im pair relationship (is Im determined by Re?)
  2. Commutator (Lie) closure dimension of the 12-dim span
  3. Anticommutator (Jordan) closure
  4. Index-support / block structure
Kill criterion: if the 12 directions sit in generic position with no
distinguished substructure, ladder item 7.1 (canonical decomposition)
is deprioritized.
"""
import re
import numpy as np

LEAN = "/home/hatch/workspace/thet-logos/lean/ThetLogos/CFKernelRetarget.lean"

NAMES = ["NuLeR", "ELNuR", "ULDR", "DLUR", "NuREbarR", "EREbarR"]

def parse_defs(path):
    src = open(path).read()
    mats = {}
    for name in NAMES:
        for part in ["Re", "Im"]:
            key = f"exotic{part}{name}"
            m = re.search(rf"def {key} : Matrix I32 I32 \u2102 := fun i j =>\n(.*?)(?=\n\n|\ndef |\n-- ===)",
                          src, re.S)
            assert m, key
            body = m.group(1)
            mat = np.zeros((32, 32), dtype=complex)
            # split into if/else-if branches: each "if <conds> then <val>"
            branches = re.findall(r"if (.*?) then (.*?)(?= else if | else 0)", body, re.S)
            # last branch ends with "else 0"
            for conds, val in branches:
                v = {"1": 1.0, "-1": -1.0, "Complex.I": 1j, "-Complex.I": -1j}[val.strip()]
                for a, b in re.findall(r"i = (\d+) \u2227 j = (\d+)", conds):
                    mat[int(a), int(b)] = v
            mats[key] = mat
    return mats

def main():
    mats = parse_defs(LEAN)
    E = [mats[f"exoticRe{n}"] for n in NAMES] + [mats[f"exoticIm{n}"] for n in NAMES]
    labels = [f"Re{n}" for n in NAMES] + [f"Im{n}" for n in NAMES]

    print("== 1. Re/Im pair structure ==")
    for n in NAMES:
        R, I = mats[f"exoticRe{n}"], mats[f"exoticIm{n}"]
        # support overlap
        sR = set(zip(*np.nonzero(R))); sI = set(zip(*np.nonzero(I)))
        print(f"{n}: |supp Re|={len(sR)} |supp Im|={len(sI)} same_support={sR==sI} "
              f"Im==i*skew? check: max|I - 1j*S| where S antisym part of sign pattern")
        # Is Im = i * A where A real antisymmetric on the support?
        A = I / 1j
        print(f"   I/i is real: {np.allclose(A.imag, 0)}, antisymmetric: {np.allclose(A.real + A.real.T, 0)}")

    print("\n== 2. Lie closure (commutators) ==")
    basis = [e.reshape(-1) for e in E]
    def span_dim(mats_list):
        M = np.stack([m.reshape(-1) for m in mats_list])
        return np.linalg.matrix_rank(M, tol=1e-8)
    cur = list(E)
    d0 = span_dim(cur)
    for step in range(6):
        new = []
        for a in range(len(cur)):
            for b in range(a + 1, len(cur)):
                C = cur[a] @ cur[b] - cur[b] @ cur[a]
                if np.linalg.norm(C) > 1e-10:
                    new.append(C)
        trial = cur + new
        d1 = span_dim(trial)
        print(f"  step {step}: dim {span_dim(cur)} -> {d1} (+{len(new)} commutators)")
        if d1 == span_dim(cur):
            break
        # extend basis with independent newcomers
        M = np.stack([m.reshape(-1) for m in cur])
        for C in new:
            v = C.reshape(-1)
            if np.linalg.matrix_rank(np.vstack([M, v]), tol=1e-8) > M.shape[0]:
                M = np.vstack([M, v]); cur.append(C)
    print(f"  Lie closure dim = {span_dim(cur)} (ambient u(32) has dim 1024 real)")

    print("\n== 3. Pairwise commutator norms (who talks to whom) ==")
    norms = np.zeros((12, 12))
    for a in range(12):
        for b in range(12):
            norms[a, b] = np.linalg.norm(E[a] @ E[b] - E[b] @ E[a])
    np.set_printoptions(precision=1, suppress=True, linewidth=200)
    print("   " + " ".join(f"{l:>8s}" for l in labels))
    for a, l in enumerate(labels):
        print(f"{l:>8s}" + " ".join(f"{norms[a,b]:>8.1f}" for b in range(12)))

    print("\n== 4. Block structure: support inside 16+16 split ==")
    for l, e in zip(labels, E):
        s = set(zip(*np.nonzero(e)))
        in00 = sum(1 for (a, b) in s if a < 16 and b < 16)
        in11 = sum(1 for (a, b) in s if a >= 16 and b >= 16)
        off = len(s) - in00 - in11
        print(f"  {l:>10s}: block00={in00} block11={in11} offdiag={off}")

if __name__ == "__main__":
    main()
