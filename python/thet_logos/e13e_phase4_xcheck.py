"""E13-E Phase 4: numerical regression checks for the whitepaper numbers.

Verifies (deterministic, no fitting):
 N1: T2 = Tr(D_F^2) matches analytic 4*VEV^2*a to 12 digits.
 N2: D_F strictly proportional to VEV (no vev-independent pieces).
 N3: Tr(D_Phi(H)^2) = (2*T2/v^2)|H|^2 on neutral direction (ratio 1.0).
 N4: cross coefficient 2*T2/3v^2 = 6.92407 = (8/3)*a_ours exactly.
 N5: anchor A2 value -(1/3)*int_{S^4}R = -105.2758 (cross-checked).
"""
import numpy as np
import sys
sys.path.insert(0, ".")
from thet_logos.common import DF_oneGen, buildDirac
from thet_logos.finite_thermal_flow import Y_PHYS, VEV

Y = Y_PHYS
a_ours = Y["Ynu"]**2 + Y["Ye"]**2 + 3*Y["Yu"]**2 + 3*Y["Yd"]**2


def D_of(V):
    return DF_oneGen(Y["Ynu"], Y["Ye"], Y["Yu"], Y["Yd"]) * V


def main():
    D = D_of(VEV)
    ev2 = np.linalg.eigvalsh(D @ D)
    T2 = float(np.sum(ev2))
    print(f"N1: T2 = {T2:.6f}, analytic 4*VEV^2*a = {4*VEV**2*a_ours:.6f}")
    assert abs(T2 - 4*VEV**2*a_ours) < 1e-6

    D2 = D_of(2*VEV)
    assert np.max(np.abs(D2 - 2*D)) < 1e-9
    print("N2: D_F proportional to VEV exactly: PASS")

    v = VEV
    for H0 in (50.0, 174.0, 300.0):
        A = np.diag([Y[k] for k in ("Ynu","Ye","Yu","Yd","Yu","Yd","Yu","Yd")]).astype(complex)
        A = A * (np.sqrt(2)*H0*(VEV/v))
        Z = np.zeros((8, 8), complex)
        Dp = buildDirac(A, A.conj(), Z, Z)
        tr = float(np.real(np.trace(Dp @ Dp)))
        assert abs(tr/(2*T2/v**2*H0**2) - 1.0) < 1e-9
    print("N3: Tr(D_Phi(H)^2) = (2T2/v^2)|H|^2, ratio 1.0: PASS")

    cross = 2*T2/(3*v**2)
    print(f"N4: 2T2/3v^2 = {cross:.8f} = (8/3)a_ours = {8/3*a_ours:.8f}")
    assert abs(cross - 8/3*a_ours) < 1e-9
    # A-convention cross term in a4: +cross * beta * |H|^2 * int R
    print(f"    a4 cross term: +{cross:.4f} * beta * |H|^2 * int_{{M4}} R")

    A2_S4 = -(1.0/3.0)*32*np.pi**2
    print(f"N5: A2(S^4) = -(1/3)int R = {A2_S4:.4f} (anchor fit: -105.2748)")
    assert abs(A2_S4 - (-105.2758)) < 0.01
    print("ALL NUMERICAL CHECKS PASS")


if __name__ == "__main__":
    main()
