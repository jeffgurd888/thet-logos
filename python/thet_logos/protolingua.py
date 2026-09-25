"""THET Proto-Lingua Greek: pre-spatiotemporal operator alphabet (Tier T4 numerical).

Engine #8. Implements the Rung-4 proto-linguistic layer as runnable algebra.

  L0 = {top, bot, void, one, Theta, Phi, Omega}      (7-symbol alphabet)

Operator realizations. The symbol -> operator map is a STIPULATED SYNTAX
(a formal encoding), not a derivation of physics from philosophy:

  span{top, bot} ~= C^2,  e0 = |top> (presence), e1 = |bot> (absence)
  void -> 0   (zero operator: null-start -- no metric, no excitations,
               no background coordinates)
  one  -> I   (normalization baseline)

  Theta = Theta_dual (+) Theta_nil (+) M        (direct sum, three sectors)
    Theta_dual : Pauli-X on span{top,bot}; flips presence <-> absence.
    Theta_nil  : 6x6 shift T0 -> T1 -> ... -> T5 -> 0. Five transition
                 stages; nilpotency index 6 (N^6 = 0, N^5 != 0).
                 The spec's "order 5" is the stage count; the index is
                 reported honestly here.
    M          : Fibonacci matrix [[1,1],[1,0]] driving the chromatic
                 tower: ascent eigenvalue lambda_+ = phi, conjugate
                 descent lambda_- = -1/phi.

  Phi   -> phi = (1+sqrt(5))/2, checked as M's dominant eigenvalue.
  Omega -> identity on the sector space C^2 (+) C^6 (+) C^2 = C^10:
           closure = completeness of the sector decomposition.

LOGOS cycle (five modules), executed on the 32-state finite triple by
reusing Engine #7's Lindblad thermalizer and the modular-flow readout:

  REFLECT  : rho -> J rho J,  J = UJ o conj (real structure, antiunitary).
             Check: J^2 = +I and J D_F = D_F J (KO relations, numerical).
  FLOW     : Lindblad advance rho^R(0) -> rho^R(t) (modular-time proxy).
  GENERATE : K(t) = -log rho(t), the inner modular-Hamiltonian readout.
  COMPARE  : trace distance ||rho(t) - rho_beta||_1, predicted vs observed.
  CLOSE    : KMS boundary condition Tr(rho_beta A sigma_{i beta}(B))
             = Tr(rho_beta B A); the fixed point the cycle returns to.

Theorem != Simulation != Experiment != Device: small-matrix and 32x32
numerics only. No device exists. Nothing here establishes the
"pre-spatiotemporal" architectural claim -- that is Rung-4 placement
in the framework, not a numerical result.
"""
import numpy as np
import scipy.linalg as la

from .common import DF_oneGen, UJ, DIM
from . import thermalize
from .modular_flow import sigma

SEED = 2026
TOL = 1e-10

PHI = (1.0 + np.sqrt(5.0)) / 2.0


# ---------------------------------------------------------------- L0 alphabet
def theta_dual():
    """Pauli-X on span{top, bot}: flips presence <-> absence."""
    return np.array([[0, 1], [1, 0]], dtype=complex)


def theta_nil():
    """6x6 shift T0->T1->...->T5->0 (five transition stages)."""
    N = np.zeros((6, 6), dtype=complex)
    for i in range(5):
        N[i + 1, i] = 1.0
    return N


def fib_matrix():
    """M = [[1,1],[1,0]]: Fibonacci tower driver."""
    return np.array([[1, 1], [1, 0]], dtype=complex)


def fibonacci(n):
    """F_1 = F_2 = 1, exact integer Fibonacci."""
    a, b = 1, 1
    for _ in range(n - 1):
        a, b = b, a + b
    return a


# ------------------------------------------------------- LOGOS cycle helpers
def apply_J(rho):
    """REFLECT: rho -> J rho J with J = UJ o conj (antilinear)."""
    U = UJ()
    return U @ rho.conj() @ U.T


def kms_error(rho, K, beta, A, B):
    """|Tr(rho A sigma_{i beta}(B)) - Tr(rho B A)|."""
    lhs = np.trace(rho @ A @ sigma(K, 1j * beta, B))
    rhs = np.trace(rho @ B @ A)
    return abs(lhs - rhs)


# ------------------------------------------------------------------ main
def main():
    print("[ProtoLingua] === L0 alphabet: Theta sector decomposition ===")

    # --- Theta_dual: involution on span{top,bot}
    X = theta_dual()
    e_herm = float(np.max(np.abs(X - X.conj().T)))
    e_inv = float(np.max(np.abs(X @ X - np.eye(2))))
    top, bot = np.array([1, 0], complex), np.array([0, 1], complex)
    e_flip = float(np.max(np.abs(X @ top - bot)) + np.max(np.abs(X @ bot - top)))
    print(f"[ProtoLingua] Theta_dual Hermitian err: {e_herm:.3e}")
    print(f"[ProtoLingua] Theta_dual involution  err (X^2=I): {e_inv:.3e}")
    print(f"[ProtoLingua] Theta_dual flip err (top<->bot):    {e_flip:.3e}")
    assert e_herm < TOL and e_inv < TOL and e_flip < TOL

    # --- Theta_nil: 5 transition stages, nilpotency index 6
    N = theta_nil()
    n6 = float(la.norm(np.linalg.matrix_power(N, 6), ord="fro"))
    n5 = float(la.norm(np.linalg.matrix_power(N, 5), ord="fro"))
    print(f"[ProtoLingua] Theta_nil  ||N^6|| = {n6:.3e} (must vanish)")
    print(f"[ProtoLingua] Theta_nil  ||N^5|| = {n5:.6f} (must NOT vanish)")
    assert n6 < TOL and n5 > 1e-6

    # --- M: Fibonacci matrix, spectrum {phi, -1/phi}
    M = fib_matrix()
    ev = np.sort_complex(la.eigvals(M))
    e_phi = abs(ev[1] - PHI)
    e_phim = abs(ev[0] - (-1.0 / PHI))
    print(f"[ProtoLingua] M eigenvalues: {ev[0]:.6f}, {ev[1]:.6f}")
    print(f"[ProtoLingua]   |lambda_+ - phi| = {e_phi:.3e}, "
          f"|lambda_- + 1/phi| = {e_phim:.3e}")
    assert e_phi < TOL and e_phim < TOL

    # --- Fibonacci tower: M^n[0,0] = F_{n+1}, exact
    Mn = np.eye(2, dtype=complex)
    for n in range(1, 13):
        Mn = Mn @ M
        got = int(round(Mn[0, 0].real))
        want = fibonacci(n + 1)
        assert got == want, f"tower break at n={n}: {got} != {want}"
    print("[ProtoLingua] Fibonacci tower M^n[0,0] = F_{n+1} exact for n=1..12")

    # --- void / one / Omega: null-start, normalization, closure
    SECCAR = [(2, X, "dual"), (6, N, "nil"), (2, M, "fib")]
    dim10 = sum(d for d, _, _ in SECCAR)
    void = np.zeros((dim10, dim10), dtype=complex)
    one = np.eye(dim10, dtype=complex)
    x = np.arange(dim10, dtype=complex)
    assert np.max(np.abs(void @ x)) == 0.0 and np.max(np.abs(one @ x - x)) == 0.0
    # Omega = completeness: sector projectors sum to identity
    P = np.zeros((dim10, dim10), dtype=complex)
    k = 0
    for d, _, _ in SECCAR:
        P[k:k + d, k:k + d] = np.eye(d)
        k += d
    e_omega = float(np.max(np.abs(P - np.eye(dim10))))
    print(f"[ProtoLingua] void=0, one=I ok; Omega completeness err: {e_omega:.3e}")
    assert e_omega == 0.0
    print("[ProtoLingua] L0 alphabet checks PASS")

    print("[ProtoLingua] === LOGOS cycle on the 32-state triple ===")
    rng = np.random.default_rng(SEED)
    D = DF_oneGen(0.5, 0.7, 1.1, 0.9, rng)
    assert np.max(np.abs(D - D.conj().T)) < 1e-12, "D_F must be Hermitian"
    H = (thermalize.LAM * D) @ (thermalize.LAM * D)
    beta, kappa = thermalize.BETA, thermalize.KAPPA

    # REFLECT: real structure is an involutive symmetry of the triple
    U = UJ()
    e_J2 = float(np.max(np.abs(U @ U - np.eye(DIM))))
    e_JD = float(np.max(np.abs(U @ D.conj() - D @ U)))
    print(f"[ProtoLingua] REFLECT J^2=I err: {e_J2:.3e}")
    print(f"[ProtoLingua] REFLECT JD=DJ err: {e_JD:.3e}")
    assert e_J2 < TOL and e_JD < 1e-8

    rho_beta, w_beta, V = thermalize.gibbs_state(H, beta)
    # REFLECT fixes the thermal boundary state: J rho_beta J = rho_beta
    e_Jrho = float(la.norm(apply_J(rho_beta) - rho_beta, ord="fro"))
    print(f"[ProtoLingua] REFLECT ||J rho_beta J - rho_beta|| = {e_Jrho:.3e}")
    assert e_Jrho < 1e-10

    # FLOW: mirror the far-from-equilibrium state, then thermalize it
    L, w, Ve, gamma = thermalize.lindblad_superop(H, beta, kappa)
    psi0 = Ve[:, -1]
    rho0 = np.outer(psi0, psi0.conj())
    rhoR = apply_J(rho0)                       # REFLECT
    psi = rhoR.reshape(-1)                     # FLOW
    T_FLOW, DT = 8.0, 0.02
    for _ in range(int(T_FLOW / DT)):
        psi = thermalize.rk4_step(psi, DT, L)
    rho_t = psi.reshape(DIM, DIM)
    rho_t = 0.5 * (rho_t + rho_t.conj().T)
    rho_t /= np.trace(rho_t).real

    # GENERATE + COMPARE
    Z = float(np.sum(np.exp(-beta * (w_beta - w_beta[0])))) * np.exp(-beta * w_beta[0])
    F = -np.log(Z) / beta
    d = thermalize.diagnostics(rho_t, rho_beta, H, beta, F)
    print(f"[ProtoLingua] FLOW t={T_FLOW}: trace_dist={d['trace_dist']:.3e}, "
          f"S={d['S']:.6f}, K_err={d['K_err']:.3e}")
    assert d["trace_dist"] < 1e-2, "cycle did not approach the KMS boundary"

    # CLOSE: KMS boundary condition on the fixed point.
    # With K = -log rho the modular parameter is 1 (not beta): the KMS
    # theorem reads Tr(rho A sigma_i(B)) = Tr(rho B A); beta is already
    # inside K = beta*H + const. (Passing beta here is a real bug class --
    # modular_flow.py uses 1.0 for the same reason.)
    K_beta = -la.logm(rho_beta)
    K_beta = (K_beta + K_beta.conj().T) / 2
    A = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))
    B = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))
    e_kms = kms_error(rho_beta, K_beta, 1.0, A, B)
    print(f"[ProtoLingua] CLOSE KMS (modular parameter i) err: {e_kms:.3e}")
    assert e_kms < 1e-8

    print("[ProtoLingua] PASS -- Tier T4 (numerical engine design)")
    print("[ProtoLingua] Theorem != Simulation != Experiment != Device.")
    return True


if __name__ == "__main__":
    main()
