"""TRO identity checks + tripotent kernel census (Tier T3 / T5-withdrawal).

Checks:
 1. TRO associativity [[abc]de] = [ab[cde]] = [a[dcb]e] on random
    complex m x n matrices, [a b c] = a b* c.
 2. Tripotent identity e e* e = e for SVD-constructed tripotents.
 3. Kernel census for L(X) = X + N0 X N0 on M2(R): confirms dim ker L
    is NOT 4 in general -- consistent with the withdrawal of the
    dim ker L = 4 claim (Framework Sec. 2.1.5, Tier T5).
"""
import numpy as np

SEED = 2026


def ternary(a, b, c):
    return a @ b.conj().T @ c


def check_tro_identities(rng, trials=20, m=3, n=4):
    worst = 0.0
    for _ in range(trials):
        mats = [rng.standard_normal((m, n)) + 1j * rng.standard_normal((m, n))
                for _ in range(5)]
        a, b, c, d, e = mats
        lhs = ternary(ternary(a, b, c), d, e)
        mid = ternary(a, b, ternary(c, d, e))
        rhs = ternary(a, ternary(d, c, b), e)
        worst = max(worst, np.max(np.abs(lhs - mid)), np.max(np.abs(lhs - rhs)))
    return worst


def random_tripotent(rng):
    """Partial isometry from SVD with 0/1 singular values: e e* e = e."""
    U, _ = np.linalg.qr(rng.standard_normal((2, 2)))
    V, _ = np.linalg.qr(rng.standard_normal((2, 2)))
    S = np.diag([1.0, 0.0])  # rank-1 projector spectrum
    return (U @ S @ V.T)


def kernel_dim_L(N0):
    """Real dimension of ker(L), L(X) = X + N0 X N0 on M2(R) ~= R^4."""
    # Real-linear map as 4x4 real matrix on vec(X) (column stacking).
    Lmat = np.eye(4) + np.kron(N0, N0)
    s = np.linalg.svd(Lmat, compute_uv=False)
    return int(np.sum(s < 1e-10)), s


def main():
    rng = np.random.default_rng(SEED)
    err = check_tro_identities(rng)
    print(f"[TRO] associativity max error over 20 trials: {err:.3e}")
    assert err < 1e-12, "TRO associativity FAILED"

    worst_trip = 0.0
    dims = []
    for _ in range(30):
        e = random_tripotent(rng)
        worst_trip = max(worst_trip, np.max(np.abs(e @ e.T @ e - e)))
        d, _ = kernel_dim_L(e)
        dims.append(d)
    print(f"[TRO] tripotent identity max error: {worst_trip:.3e}")
    assert worst_trip < 1e-12, "tripotent identity FAILED"
    print(f"[TRO] ker(L) dims over 30 random tripotents in M2(R): "
          f"min={min(dims)}, max={max(dims)}, mean={np.mean(dims):.2f}")
    assert max(dims) < 4, "unexpected: dim ker L = 4 observed"
    print("[TRO] consistent with WITHDRAWAL of dim ker L = 4 (Tier T5)")
    print("[TRO] PASS")
    return True


if __name__ == "__main__":
    main()
