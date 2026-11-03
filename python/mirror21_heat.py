#!/usr/bin/env python3
"""
mirror21_heat.py — honest numerics companion to the MIRROR-21 Lean bricks
(ThetLogos/MirrorTwentyOne.lean, ThetLogos/MirrorTwentyOneAlgebra.lean).

What this script does (T2 numerics; verifies NOTHING about the Lean
theorems — it illustrates the finite object they describe):

  * Builds the cycle-graph Laplacian L of the 21-cycle C_21 on Z_21
    (L = 2I - shift - shift^{-1}), an operator that is mirror-symmetric
    BY CONSTRUCTION: the program verifies that L commutes with the
    permutation matrix of the mirror involution Theta : i -> -i (mod 21).
  * Computes the spectrum numerically. The zero-mode count is DERIVED
    from that spectrum (counted, not inserted): exactly 1 zero mode,
    the constants. The rest of the spectrum falls into 10 degenerate
    pairs lambda_k = lambda_{21-k} — the spectral shadow of the
    10 mirror pairs + 1 unique center proved in the Lean bricks.
  * Computes the LAPLACIAN heat trace K(t) = sum_k exp(-t * lambda_k)
    = Tr(exp(-tL)). This is a Laplacian heat trace; it is NOT dressed
    up as Tr(exp(-t D^2)) for any Dirac-type operator.
  * Extracts the small-t expansion from its exact POLYNOMIAL form
    K(t) = sum_j (-t)^j Tr(L^j) / j! : a_0 = Tr I = 21,
    linear coefficient -Tr L = -42, quadratic Tr(L^2)/2 = 63,
    and checks the truncated series against the direct trace.

  * Prints, on the record, why the dropped sketch's "effective
    spectral dimension" readout was an artifact (see bottom).

NO CLAIM — parts of any official Millennium statement closed: 0.
Dials: 0/4.
"""

import numpy as np

N = 21


def theta(i: int) -> int:
    """The mirror involution Theta : i -> -i (mod 21)."""
    return (-i) % N


def build_laplacian() -> np.ndarray:
    """Cycle-graph Laplacian of C_21: L = 2I - S - S^{-1}."""
    L = 2.0 * np.eye(N)
    for i in range(N):
        L[i, (i + 1) % N] -= 1.0
        L[i, (i - 1) % N] -= 1.0
    return L


def build_theta_permutation() -> np.ndarray:
    """Permutation matrix P of Theta: (P f)(i) = f(Theta i)."""
    P = np.zeros((N, N))
    for i in range(N):
        P[i, theta(i)] = 1.0
    return P


def main() -> None:
    np.set_printoptions(precision=6, suppress=True, linewidth=110)

    L = build_laplacian()
    P = build_theta_permutation()

    # --- Mirror symmetry, verified (not assumed): [P, L] = 0 ----------
    comm_residual = np.max(np.abs(P @ L - L @ P))
    p_involutive = np.max(np.abs(P @ P - np.eye(N)))

    # --- Spectrum, computed; zero-mode count DERIVED from it ----------
    eig = np.linalg.eigvalsh(L)
    zero_tol = 1e-10
    zero_count = int(np.sum(eig < zero_tol))
    gap = float(np.min(eig[eig >= zero_tol]))
    gap_exact = 4.0 * np.sin(np.pi / N) ** 2

    # Analytic spectrum of the cycle Laplacian: 2 - 2 cos(2 pi k / 21).
    analytic = np.sort(2.0 - 2.0 * np.cos(2.0 * np.pi * np.arange(N) / N))
    spectrum_err = float(np.max(np.abs(np.sort(eig) - analytic)))

    # Degeneracy structure: 1 simple eigenvalue (k = 0) + 10 doublets.
    rounded = np.round(eig, 8)
    _, counts = np.unique(rounded, return_counts=True)
    degeneracy_profile = sorted(int(c) for c in counts)

    # --- Laplacian heat trace K(t) = Tr exp(-tL) -----------------------
    t_vals = np.array([0.001, 0.01, 0.1, 0.5, 1.0, 5.0])
    K = np.array([np.sum(np.exp(-t * eig)) for t in t_vals])

    # --- Small-t expansion from the polynomial form --------------------
    tr_I = float(N)                       # Tr L^0 = a_0
    tr_L = float(np.trace(L))             # Tr L   = 42
    tr_L2 = float(np.trace(L @ L))        # Tr L^2 = 126
    tr_L3 = float(np.trace(L @ L @ L))    # Tr L^3 = 420
    a0 = tr_I
    a1 = -tr_L                            # coefficient of t^1
    a2 = tr_L2 / 2.0                      # coefficient of t^2
    a3 = -tr_L3 / 6.0                     # coefficient of t^3

    def series(t: float) -> float:
        return a0 + a1 * t + a2 * t**2 + a3 * t**3

    t_check = 0.01
    series_err = abs(series(t_check) - float(np.sum(np.exp(-t_check * eig))))

    # --- Results block --------------------------------------------------
    print("=" * 72)
    print("MIRROR-21 — cycle Laplacian C_21, honest numerics (T2)")
    print("Companion to ThetLogos.MirrorTwentyOne{,Algebra}.lean (T1).")
    print("This script illustrates the finite object; it proves nothing.")
    print("=" * 72)
    print(f"Theta permutation is an involution:   max |P^2 - I|   = {p_involutive:.3e}")
    print(f"L commutes with Theta (mirror symm.): max |PL - LP|   = {comm_residual:.3e}")
    print(f"Spectrum vs analytic 2-2cos(2 pi k/21): max abs err   = {spectrum_err:.3e}")
    print()
    print(f"Zero modes DERIVED from the spectrum (lambda < 1e-10): {zero_count}")
    print(f"  (exactly 1: the constant functions — counted, not inserted)")
    print(f"Degeneracy profile of the spectrum: {degeneracy_profile}")
    print(f"  (1 simple + 10 doublets: 10 mirror pairs + the unique center)")
    print(f"Spectral gap lambda_1 = {gap:.6f}   (exact 4 sin^2(pi/21) = {gap_exact:.6f})")
    print()
    print("Laplacian heat trace K(t) = Tr exp(-tL)   [NOT a D^2 trace]")
    for t, k in zip(t_vals, K):
        print(f"  K({t:>6}) = {k:.6f}")
    print()
    print("Small-t expansion from the polynomial form K(t) = sum_j (-t)^j Tr(L^j)/j!:")
    print(f"  a_0        = Tr I     = {a0:.1f}")
    print(f"  t^1 coeff  = -Tr L    = {a1:.1f}")
    print(f"  t^2 coeff  = Tr(L^2)/2 = {a2:.1f}   (Tr L^2 = {tr_L2:.1f})")
    print(f"  t^3 coeff  = -Tr(L^3)/6 = {a3:.1f}   (Tr L^3 = {tr_L3:.1f})")
    print(f"  Series vs direct K(0.01): abs err = {series_err:.3e}")
    print()
    print("ARTIFACT NOTE (on the record): the dropped sketch reported an")
    print("'effective spectral dimension' of 0.0622 from a log-log fit of")
    print("K(t) at small t. For ANY finite matrix, K(t) -> dim (here 21) as")
    print("t -> 0, so the log-log slope -> 0 and the 'dimension' -> 0 no")
    print("matter what the operator is: the readout measured finiteness,")
    print("not dimension. The (4 pi t)^(-d/2) Seeley-DeWitt prefactor it")
    print("imitated exists only for infinite-dimensional (continuum) heat")
    print("kernels. The honest small-t behavior of a finite heat trace is")
    print("the polynomial above: K(t) = 21 - 42 t + 63 t^2 - 70 t^3 + ...")
    print("=" * 72)
    print("NO CLAIM; dials 0/4.")


if __name__ == "__main__":
    main()
