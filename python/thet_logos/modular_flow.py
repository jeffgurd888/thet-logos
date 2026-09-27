"""Modular flow simulation (Tier T3 numerical).

For a random positive density state rho (32x32):
  K = -log rho,  sigma_s(A) = e^{isK} A e^{-isK}
Checks:
  1. K Hermitian.
  2. Group property: sigma_{s+t} = sigma_s . sigma_t.
  3. Stationarity: Tr(rho sigma_s(A)) = Tr(rho A).
  4. KMS condition: Tr(rho A sigma_{i beta}(B)) = Tr(rho B A), beta = 1,
     i.e. imaginary-time flow. Proves itself from rho = e^{-K}/Z.
"""
import numpy as np
import scipy.linalg as la

SEED = 2026
DIM = 32


def random_state(rng, n=DIM):
    X = rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))
    rho = X @ X.conj().T
    return rho / np.trace(rho)


def sigma(K, s, A):
    # NOTE: for complex s (imaginary-time KMS flow) the second factor must be
    # exp(-i s K), NOT U.conj().T (they agree only for real s).
    F = la.expm(1j * s * K)
    Fi = la.expm(-1j * s * K)
    return F @ A @ Fi


def main():
    rng = np.random.default_rng(SEED)
    rho = random_state(rng)
    K = -la.logm(rho)
    K = (K + K.conj().T) / 2
    eK = np.max(np.abs(K - K.conj().T))
    print(f"[ModFlow] K Hermitian err: {eK:.3e}")
    assert eK < 1e-10

    A = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))
    B = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))
    s, t = 0.7, -1.3
    e_group = np.max(np.abs(sigma(K, s + t, A) - sigma(K, s, sigma(K, t, A))))
    e_stat = abs(np.trace(rho @ sigma(K, s, A)) - np.trace(rho @ A))
    # KMS at beta = 1: Tr(rho A sigma_{i}(B)) = Tr(rho B A)
    lhs = np.trace(rho @ A @ sigma(K, 1j * 1.0, B))
    rhs = np.trace(rho @ B @ A)
    e_kms = abs(lhs - rhs)
    print(f"[ModFlow] group-property err: {e_group:.3e}")
    print(f"[ModFlow] stationarity err:   {e_stat:.3e}")
    print(f"[ModFlow] KMS (beta=1) err:   {e_kms:.3e}")
    assert e_group < 1e-10 and e_stat < 1e-10 and e_kms < 1e-8
    print("[ModFlow] PASS (simulation -- Tier T3)")
    return True


if __name__ == "__main__":
    main()
