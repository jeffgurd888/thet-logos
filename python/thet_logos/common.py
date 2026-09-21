"""Shared 32-state finite spectral triple constructions.

Mirrors lean/ThetLogos/Scaffold32.lean and FiniteSpectralTriple.lean:
partner map, grading gamma_F, real structure U_J, gauge algebra A_F =
C (+) H (+) M3(C) with the asymmetric Option-A representation pi,
opposite representation piOp, and the block Dirac operator buildDirac.
"""
import numpy as np

DIM = 32
HALF = 16


def partner(k: int) -> int:
    """Particle <-> antiparticle index swap: p(k) = k+16 (k<16), k-16 (k>=16)."""
    return k + 16 if k < 16 else k - 16


def gamma_F() -> np.ndarray:
    """Chiral grading diag(+I8, -I8, -I8, +I8)."""
    chi = np.ones(DIM)
    chi[8:24] = -1.0
    return np.diag(chi).astype(complex)


def UJ() -> np.ndarray:
    """Real-structure permutation matrix: (U_J)_{ij} = delta_{j, p(i)}."""
    U = np.zeros((DIM, DIM), dtype=complex)
    for i in range(DIM):
        U[i, partner(i)] = 1.0
    return U


# --- Gauge algebra A_F = C (+) H (+) M3(C) ---
# An element is a tuple (u1, q, color) with q 2x2, color 3x3 complex.

def quat_units():
    """1, i, j, k as 2x2 complex matrices."""
    one = np.eye(2, dtype=complex)
    i = np.array([[1j, 0], [0, -1j]])
    j = np.array([[0, 1], [-1, 0]])
    k = np.array([[0, 1j], [1j, 0]])
    return [one, i, j, k]


def af_generators():
    """24 real generators: 2 (C) + 4 (H) + 18 (M3(C))."""
    gens = []
    gens.append((1.0 + 0j, np.zeros((2, 2), complex), np.zeros((3, 3), complex)))
    gens.append((1j, np.zeros((2, 2), complex), np.zeros((3, 3), complex)))
    for q in quat_units():
        gens.append((0j, q, np.zeros((3, 3), complex)))
    for p in range(3):
        for q_ in range(3):
            E = np.zeros((3, 3), complex)
            E[p, q_] = 1.0
            gens.append((0j, np.zeros((2, 2), complex), E))
            gens.append((0j, np.zeros((2, 2), complex), 1j * E))
    assert len(gens) == 24
    return gens


def random_af(rng):
    """Random element of A_F."""
    u1 = rng.standard_normal() + 1j * rng.standard_normal()
    q = rng.standard_normal((2, 2)) + 1j * rng.standard_normal((2, 2))
    color = rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3))
    return (u1, q, color)


def embedSM(a) -> np.ndarray:
    """16x16 Option-A embedding of A_F (mirrors FiniteSpectralTriple.lean)."""
    u1, q, color = a
    M = np.zeros((16, 16), dtype=complex)
    # H_L x H_L (0-7)
    M[0:2, 0:2] = q
    for idx in range(2, 8):
        iso_i = (idx - 2) % 2
        col_i = (idx - 2) // 2
        for jdx in range(2, 8):
            iso_j = (jdx - 2) % 2
            col_j = (jdx - 2) // 2
            M[idx, jdx] = q[iso_i, iso_j] * color[col_i, col_j]
    # H_R x H_R (8-15)
    M[8, 8] = u1
    M[9, 9] = np.conj(u1)
    for idx in range(10, 16):
        iso_i = (idx - 10) % 2
        col_i = (idx - 10) // 2
        for jdx in range(10, 16):
            iso_j = (jdx - 10) % 2
            col_j = (jdx - 10) // 2
            if iso_i == iso_j:
                s = u1 if iso_i == 0 else np.conj(u1)
                M[idx, jdx] = s * color[col_i, col_j]
    return M


def pi(a) -> np.ndarray:
    """pi(a): 32x32, embedSM on top-left 16x16, zero elsewhere."""
    P = np.zeros((DIM, DIM), dtype=complex)
    P[:HALF, :HALF] = embedSM(a)
    return P


def piOp(M: np.ndarray) -> np.ndarray:
    """Opposite representation: piOp(M) = U_J @ M.T @ U_J (mirrors Lean)."""
    U = UJ()
    return U @ M.T @ U


def buildDirac(A, B, C, E) -> np.ndarray:
    """32x32 block Dirac operator (mirrors buildDirac in Lean).

    Blocks are 8x8: A (H_L->H_R), B (H_L^c->H_R^c),
    C (H_L->H_L^c), E (H_R->H_R^c) cross-sector Majorana-type.
    """
    D = np.zeros((DIM, DIM), dtype=complex)
    D[0:8, 8:16] = A
    D[0:8, 16:24] = C
    D[8:16, 0:8] = A.conj().T
    D[8:16, 24:32] = E.conj().T
    D[16:24, 0:8] = C.conj().T
    D[16:24, 24:32] = B
    D[24:32, 8:16] = E
    D[24:32, 16:24] = B.conj().T
    return D


def DF_oneGen(Ynu, Ye, Yu, Yd, rng=None) -> np.ndarray:
    """One-generation Dirac: A diagonal Yukawa, B = conj(A), C = E = 0."""
    A = np.diag([Ynu, Ye, Yu, Yd, Yu, Yd, Yu, Yd]).astype(complex)
    B = A.conj()
    Z = np.zeros((8, 8), dtype=complex)
    return buildDirac(A, B, Z, Z)


def random_block(rng, n=8):
    return rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))
