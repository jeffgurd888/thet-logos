#!/usr/bin/env python3
"""
mirror21_orthogonal_heat.py — honest numerics companion (pin O5) to the
ORTHOGONAL PANTOREALITY Lean bricks
(ThetLogos/MirrorTwentyOneOrthogonal.lean,
 ThetLogos/MirrorTwentyOneOrthogonalSpectral.lean).

What this script does (T2 numerics; verifies NOTHING about the Lean
theorems — it illustrates the finite objects they describe):

  * Takes the arm spectrum of the C_21 cycle Laplacian from tonight's
    verified computation (analytic form 2 - 2 cos(2 pi k / 21),
    cross-checked against numpy's eigensolver exactly as in
    mirror21_heat.py) and forms the JOINT spectrum of
    L1 + L2 = L (x) I + I (x) L on the 21 x 21 grid as all pairwise
    SUMS lambda_i + lambda_j. For a Kronecker sum this is the exact
    spectrum, not an approximation.
  * DERIVES the zero-mode count of the joint operator from that
    spectrum (counted, not inserted): exactly 1 — the constants on
    the grid. This is the T2 shadow of the Lean pin O4/O4+.
  * Computes the degeneracy profile of the joint spectrum (the
    "product profile": sums of the arm profile [1 simple + 10
    doublets] with itself) and the joint gap
    (lambda_1 + 0 = 0.088854, the arm gap).
  * Computes the joint Laplacian heat trace
    K(t) = Tr exp(-t (L1 + L2)) = K_arm(t)^2 at a few times t.
    This is a Laplacian heat trace on the grid; it is NOT dressed
    up as a D^2 trace for any Dirac-type operator.

Tier note (on the record, per the scoping's pin O5): the zero-mode
count printed here is T2. Pin O4+ in the Lean brick is the T1
statement "kernel of L1 + L2 is exactly the constants"; this script
does not prove it and does not dress this count up as T1.

NO CLAIM — parts of any official Millennium statement closed: 0.
Dials: 0/4.
"""

import numpy as np

N = 21


def arm_spectrum() -> np.ndarray:
    """Spectrum of the C_21 cycle Laplacian, analytic form (verified
    against the matrix eigensolver in mirror21_heat.py)."""
    return np.sort(2.0 - 2.0 * np.cos(2.0 * np.pi * np.arange(N) / N))


def main() -> None:
    np.set_printoptions(precision=6, suppress=True, linewidth=110)

    lam = arm_spectrum()

    # --- Cross-check the arm spectrum against the explicit matrix ----
    L = 2.0 * np.eye(N)
    for i in range(N):
        L[i, (i + 1) % N] -= 1.0
        L[i, (i - 1) % N] -= 1.0
    arm_err = float(np.max(np.abs(np.linalg.eigvalsh(L) - lam)))

    # --- Joint spectrum: pairwise sums (Kronecker-sum spectrum) ------
    joint = np.sort((lam[:, None] + lam[None, :]).ravel())
    assert joint.size == N * N

    zero_tol = 1e-10
    zero_count = int(np.sum(joint < zero_tol))
    gap_joint = float(np.min(joint[joint >= zero_tol]))
    gap_arm = float(np.min(lam[lam >= zero_tol]))
    gap_exact = 4.0 * np.sin(np.pi / N) ** 2

    # Degeneracy profile of the joint spectrum: multiplicities of the
    # distinct eigenvalues, in increasing order.
    rounded = np.round(joint, 8)
    _, counts = np.unique(rounded, return_counts=True)
    joint_profile = [int(c) for c in counts]
    joint_profile_total = int(np.sum(counts))
    n_distinct = len(joint_profile)
    max_mult = max(joint_profile)

    # Smallest joint eigenvalues with multiplicities, for the record.
    head = []
    idx = 0
    vals = np.unique(rounded)
    for v in vals[:6]:
        head.append((float(v), int(np.sum(rounded == v))))

    # --- Joint heat trace K(t) = Tr exp(-t(L1+L2)) = K_arm(t)^2 ------
    t_vals = np.array([0.001, 0.01, 0.1, 0.5, 1.0, 5.0])
    K_joint = np.array([np.sum(np.exp(-t * joint)) for t in t_vals])
    K_arm = np.array([np.sum(np.exp(-t * lam)) for t in t_vals])
    K_factor_err = float(np.max(np.abs(K_joint - K_arm**2)))

    # --- Results block -------------------------------------------------
    print("=" * 72)
    print("ORTHOGONAL PANTOREALITY — joint spectrum of L1 + L2 on the")
    print("21 x 21 grid, honest numerics (T2, pin O5).")
    print("Companion to ThetLogos.MirrorTwentyOneOrthogonal{,Spectral}.lean (T1).")
    print("This script illustrates the finite objects; it proves nothing.")
    print("=" * 72)
    print(f"Arm spectrum vs matrix eigensolver: max abs err = {arm_err:.3e}")
    print(f"Joint spectrum size: {joint.size} = 21^2 (pairwise sums lambda_i + lambda_j)")
    print()
    print(f"Joint zero modes DERIVED from the spectrum (lambda < 1e-10): {zero_count}")
    print(f"  (exactly 1: the constant functions on the grid — counted, not inserted)")
    print(f"Joint spectral gap = {gap_joint:.6f}  (= arm gap {gap_arm:.6f}; "
          f"exact 4 sin^2(pi/21) = {gap_exact:.6f})")
    print(f"Joint degeneracy profile: {n_distinct} distinct eigenvalues, "
          f"multiplicities sum to {joint_profile_total}, max multiplicity {max_mult}")
    print(f"  smallest eigenvalues (value, multiplicity): {head}")
    print(f"  profile in full: {joint_profile}")
    print()
    print("Joint Laplacian heat trace K(t) = Tr exp(-t(L1+L2))   [NOT a D^2 trace]")
    for t, k in zip(t_vals, K_joint):
        print(f"  K({t:>6}) = {k:.6f}")
    print(f"Factorization check K_joint(t) = K_arm(t)^2: max abs err = {K_factor_err:.3e}")
    print()
    print("TIER NOTE (pin O5, on the record): the zero-mode count above is")
    print("T2 — derived from a floating-point spectrum. The T1 statement")
    print("'kernel of L1 + L2 is exactly the constants' is pin O4+ of the")
    print("Lean brick MirrorTwentyOneOrthogonalSpectral; this script")
    print("neither proves it nor upgrades this count to T1.")
    print("=" * 72)
    print("NO CLAIM; dials 0/4.")


if __name__ == "__main__":
    main()
