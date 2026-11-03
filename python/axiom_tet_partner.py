#!/usr/bin/env python3
"""T2 sanity check for the Partner Sector brick (AxiomTetPartner.lean).

TIER: T2 (numerical exploration). This script verifies NOTHING about
the theorems. It builds the weighted difference operator D = sqrt(W) d
for three finite webs (the cycle C21, a tree, a grid), forms the two
sector Hamiltonians H_v = D^T D and H_e = D D^T, and checks the
zero-mode counts and the index |V| - |E| against the component count.
It also reports whether the NONZERO spectra of the two sectors agree
numerically — the phenomenon whose proof (pin SP-5) is NOT in the
Lean module: the brick lands PARTIAL with K-SP-ISO fired and SP-5
named open, so this agreement is shown here as T2 evidence only.

Exit code 0 iff every count matches on every web.
"""
import numpy as np


def build_D(n, edges, w):
    """Weighted difference operator D = sqrt(W) d, shape (|E|, n).

    Orientation: each edge (u, v) is oriented u -> v; (df)(e) =
    f(v) - f(u). The Hamiltonians H_v = D^T D and H_e = D D^T and
    their spectra do not depend on this choice.
    """
    d = np.zeros((len(edges), n))
    for i, (u, v) in enumerate(edges):
        d[i, u] -= 1.0
        d[i, v] += 1.0
    return np.sqrt(w)[:, None] * d


def components(n, edges):
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for u, v in edges:
        ru, rv = find(u), find(v)
        if ru != rv:
            parent[ru] = rv
    return len({find(x) for x in range(n)})


def check(name, n, edges, seed):
    rng = np.random.default_rng(seed)
    w = rng.uniform(0.3, 2.7, size=len(edges))  # positive need weights
    D = build_D(n, edges, w)
    Hv = D.T @ D
    He = D @ D.T
    ev_v = np.linalg.eigvalsh(Hv)
    ev_e = np.linalg.eigvalsh(He)
    tol = 1e-8
    zv = int(np.sum(ev_v < tol))
    ze = int(np.sum(ev_e < tol))
    c = components(n, edges)
    idx = zv - ze
    ok_counts = (zv == c) and (ze == len(edges) - n + c) and (idx == n - len(edges))
    # T2-only observation (SP-5 is open at T1): nonzero spectra agree.
    nz_v = np.sort(ev_v[ev_v >= tol])
    nz_e = np.sort(ev_e[ev_e >= tol])
    spec_agree = len(nz_v) == len(nz_e) and (
        len(nz_v) == 0 or np.max(np.abs(nz_v - nz_e)) < 1e-8
    )
    print(f"[{name}] |V|={n} |E|={len(edges)} components={c}")
    print(f"  vertex zero modes = {zv} (expect {c})")
    print(f"  edge   zero modes = {ze} (expect {len(edges) - n + c})")
    print(f"  index zv - ze = {idx} (expect |V|-|E| = {n - len(edges)})")
    print(f"  nonzero spectra agree (T2 only; SP-5 open at T1): {spec_agree}")
    print(f"  counts ok: {ok_counts}")
    return ok_counts


def main():
    ok = True
    # C21: the cycle on 21 vertices.
    c21 = [(i, (i + 1) % 21) for i in range(21)]
    ok &= check("C21 cycle", 21, c21, seed=21)
    # A tree on 9 vertices (a path with two branches).
    tree = [(0, 1), (1, 2), (2, 3), (3, 4), (2, 5), (5, 6), (4, 7), (7, 8)]
    ok &= check("tree", 9, tree, seed=7)
    # A 4x4 grid (16 vertices, 24 edges).
    grid = []
    for r in range(4):
        for c in range(4):
            v = 4 * r + c
            if c < 3:
                grid.append((v, v + 1))
            if r < 3:
                grid.append((v, v + 4))
    ok &= check("4x4 grid", 16, grid, seed=4)
    # Two disjoint triangles + isolated vertex: 3 components.
    two = [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)]
    ok &= check("two triangles + isolated vertex", 7, two, seed=3)
    print("ALL OK" if ok else "MISMATCH")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
