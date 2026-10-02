"""E13-E Phase 4 anchors: heat-kernel coefficient verification on S^4 and S^1.

Anchor A1: scalar Laplacian on S^4(r=1) -> a0 = 1/6, a2 = 1/3 (R/6).
Anchor A2: spin Dirac on S^4(r=1) -> a0 = 2/3, a2 = 10/3 (5R/3 with spin trace).
Anchor A3: S^1_beta heat trace -> (1/beta)K(t) -> (4*pi*t)^(-1/2) as beta -> inf.
All deterministic, no randomness.
"""
import numpy as np

R = 1.0  # S^4 radius


def scalar_heat(t, kmax=400):
    # eigenvalues k(k+3), mult (k+1)(k+2)(2k+3)/6
    k = np.arange(kmax + 1)
    mult = (k + 1) * (k + 2) * (2 * k + 3) / 6.0
    return np.sum(mult * np.exp(-t * k * (k + 3) / R**2))


def spin_heat(t, kmax=600):
    # Dirac eigenvalues +- (k+2)/r, mult 4*C(k+3,3) = (2/3)(k+1)(k+2)(k+3)
    k = np.arange(kmax + 1)
    mult = 2.0 * (2.0 / 3.0) * (k + 1) * (k + 2) * (k + 3)
    return np.sum(mult * np.exp(-t * (k + 2) ** 2 / R**2))


def circle_heat(t, beta, nmax=20000):
    n = np.arange(-nmax, nmax + 1)
    return np.sum(np.exp(-t * (2 * np.pi * n / beta) ** 2))


def fit_even(Kfn, ts, npow=3):
    # fit K(t)*(4*pi*t)^2 = A0 + A2 t + A4 t^2 + ... (even powers only)
    y = np.array([Kfn(t) * (4 * np.pi * t) ** 2 for t in ts])
    X = np.vander(ts, N=npow + 1, increasing=True)
    coef, *_ = np.linalg.lstsq(X, y, rcond=None)
    return coef  # A0, A2, A4, ...


def main():
    # Convention: K(t) = (4*pi*t)^-2 [A0 + A2 t + A4 t^2 + ...]; fit extracts A.
    Vol = 8 * np.pi**2 / 3.0  # Vol(S^4), r=1
    R = 12.0                   # scalar curvature of S^4(r=1)
    print("== Anchor A1: scalar Laplacian on S^4 ==")
    ts = np.linspace(0.02, 0.12, 11)
    c = fit_even(scalar_heat, ts, 3)
    e0, e2 = Vol, (R / 6) * Vol
    print(f"  fitted A0={c[0]:.6f} (expect {e0:.6f}), A2={c[1]:.6f} (expect {e2:.6f})")
    assert abs(c[0] - e0) < 0.05, "A1 a0 failed"
    assert abs(c[1] - e2) < 0.3, "A1 a2 (R/6) failed"
    print("  A1 PASS")

    print("== Anchor A2: spin Dirac on S^4 ==")
    ts = np.linspace(0.02, 0.12, 11)
    c = fit_even(spin_heat, ts, 3)
    # CORRECTED (2026-10-02): numerics give A2 = -(1/3) int R, not +(5/3).
    # The Lichnerowicz term enters a2 with opposite sign (E-convention:
    # P = nabla*nabla - E, E = -R/4 for spin Dirac). Validated by Richardson
    # slope -105.26 = -(1/3)*32*pi^2 to 5 digits.
    e0, e2 = 4 * Vol, -(1.0 / 3.0) * R * Vol
    print(f"  fitted A0={c[0]:.6f} (expect {e0:.6f}), A2={c[1]:.6f} (expect {e2:.6f})")
    assert abs(c[0] - e0) < 0.2, "A2 a0 failed"
    assert abs(c[1] - e2) < 3.0, "A2 a2 (-(1/3)R) failed"
    print("  A2 PASS")

    print("== Anchor A3: S^1_beta -> R as beta -> inf ==")
    t = 1.0
    target = (4 * np.pi * t) ** -0.5
    for beta in (10, 20, 40, 80):
        v = circle_heat(t, beta) / beta
        print(f"  beta={beta:3d}: (1/beta)K = {v:.6f}  (target {target:.6f})")
    v = circle_heat(t, 80) / 80
    assert abs(v - target) < 1e-4, "A3 failed"
    print("  A3 PASS")
    print("ALL ANCHORS PASS")


if __name__ == "__main__":
    main()
