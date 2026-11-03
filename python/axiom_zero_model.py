#!/usr/bin/env python3
"""AXIOM TET — T2 companion: the first-primitives model, run numerically.

Implements the model of `grand-unified-axiom-zero-model-2026-11-03.md`
(a finite web, positive need weights, break energy
B_w(f) = sum_e w_e (f v - f u)^2, weighted graph Laplacian) and runs the
six tests the parent ran at scoping time, as assertions:

  1. C21: a random state breaks (B > 0); a constant state has B = 0;
     the Laplacian has exactly ONE zero mode.
  2. C21 with random positive per-edge need weights: still exactly
     one zero mode, and B_w(const) = 0. (The Need Guard, numerically:
     portions by need, unity intact.)
  3. A 5x5 grid: exactly one zero mode.
  4. Two disjoint C21s: exactly TWO zero modes — one per island.
     (The K-AZ-DISC fence: zero modes count components.)
  5. Two triangles joined by a bridge: bridge weight 1 -> one zero
     mode; bridge weight 0 -> two. (A zero-need edge silently
     disconnects the web.)
  6. Tolerance drift: a path whose adjacent differences are all
     < eps = 0.1 while its endpoints differ by 1.00 — approximate
     equality does NOT propagate. (Exactness is load-bearing.)

TIER NOTE (on the record): this is T2 — floating-point numerics.
It exercises the MODEL and the fences; it verifies NOTHING about
the Lean theorems in `lean/ThetLogos/AxiomTet.lean`, which stand
or fall by the kernel alone. NO CLAIM; dials 0/4.
"""

import numpy as np

TOL = 1e-8


def laplacian(n, edges, weights=None):
    L = np.zeros((n, n))
    for k, (u, v) in enumerate(edges):
        w = 1.0 if weights is None else weights[k]
        L[u, u] += w
        L[v, v] += w
        L[u, v] -= w
        L[v, u] -= w
    return L


def break_energy(f, edges, weights=None):
    return float(sum(
        (1.0 if weights is None else weights[k]) * (f[v] - f[u]) ** 2
        for k, (u, v) in enumerate(edges)))


def zero_modes(L):
    return int(np.sum(np.linalg.eigvalsh(L) < 1e-8))


def cycle_edges(n, offset=0):
    return [(offset + i, offset + (i + 1) % n) for i in range(n)]


def main():
    rng = np.random.default_rng(21)

    # 1. C21, flat weights.
    n = 21
    cyc = cycle_edges(n)
    f_rand = rng.normal(size=n)
    f_const = np.full(n, 3.25)
    b_rand = break_energy(f_rand, cyc)
    b_const = break_energy(f_const, cyc)
    zm = zero_modes(laplacian(n, cyc))
    print(f"[1] C21: B(random)={b_rand:.3f} (>0), B(const)={b_const:.1f}, "
          f"zero modes={zm}")
    assert b_rand > 0 and b_const == 0.0 and zm == 1

    # 2. C21, each edge its own positive need weight.
    w = rng.uniform(0.2, 5.0, size=len(cyc))
    zm_w = zero_modes(laplacian(n, cyc, w))
    b_w_const = break_energy(f_const, cyc, w)
    print(f"[2] C21 weighted (own needs): zero modes={zm_w}, "
          f"B_w(const)={b_w_const:.1f}")
    assert zm_w == 1 and b_w_const == 0.0

    # 3. 5x5 grid.
    m = 5
    gedges = []
    for r in range(m):
        for c in range(m):
            if r + 1 < m:
                gedges.append((r * m + c, (r + 1) * m + c))
            if c + 1 < m:
                gedges.append((r * m + c, r * m + c + 1))
    zm_g = zero_modes(laplacian(m * m, gedges))
    print(f"[3] Grid 5x5: zero modes={zm_g}")
    assert zm_g == 1

    # 4. Two disjoint C21s: one zero mode per island.
    two = cyc + cycle_edges(n, offset=n)
    zm_2 = zero_modes(laplacian(2 * n, two))
    print(f"[4] Two disjoint C21s: zero modes={zm_2} (one per island)")
    assert zm_2 == 2

    # 5. Bridge between two triangles: weight 1 vs weight 0.
    tri = [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (2, 3)]
    zm_b1 = zero_modes(laplacian(6, tri, [1, 1, 1, 1, 1, 1, 1.0]))
    zm_b0 = zero_modes(laplacian(6, tri, [1, 1, 1, 1, 1, 1, 0.0]))
    print(f"[5] Bridge weight 1: zero modes={zm_b1} | "
          f"bridge weight 0: zero modes={zm_b0}")
    assert zm_b1 == 1 and zm_b0 == 2

    # 6. Tolerance drift: approximate equality does not propagate.
    eps = 0.1
    vals = [i * (eps / 2) for i in range(21)]
    max_adj = max(abs(vals[i + 1] - vals[i]) for i in range(20))
    end_diff = vals[-1] - vals[0]
    print(f"[6] Tolerance path: max adjacent diff={max_adj:.3f} (< eps={eps}) "
          f"but endpoints differ by {end_diff:.2f}")
    assert max_adj < eps and end_diff == 1.00

    print("All six model tests pass at T2 (numerics only; the T1 "
          "statements are AxiomTet.lean's, graded by the kernel).")
    print("NO CLAIM; dials 0/4.")


if __name__ == "__main__":
    main()
