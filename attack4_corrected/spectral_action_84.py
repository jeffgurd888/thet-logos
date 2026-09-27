#!/usr/bin/env python3
"""Spectral action over the 84-direction selected Dirac space (T4 numerical).

Builds D_96 parameterized by the 84 physical parameters
(Ynu, Ye, Yu, Yd: 3x3 complex; MR: 3x3 complex symmetric), computes
Tr(1), Tr(D^2), Tr(D^4) by brute force AND via structural formulas, and
cross-checks. Inner fluctuations (gauge bosons) are SET TO ZERO: this is the
finite-triple trace contribution only (the unfluctuated background).

Structural formulas (derived in SPECTRAL_ACTION_84.md, verified here):
  Tr(D^2) = 4*(||Ynu||_F^2 + ||Ye||_F^2 + 3||Yu||_F^2 + 3||Yd||_F^2) + 2*||MR||_F^2
  Tr(D^4) = 4*[q(Ynu)+q(Ye)+3q(Yu)+3q(Yd)] - 2*q(Ynu)
            + ||Ynu'Ynu + MR'MR||_F^2 + ||conj(Ynu'Ynu) + MR MR'||_F^2
            + 4*||Ynu MR'||_F^2
  where q(Y) = ||Y Y'||_F^2 = Tr((Y'Y)^2), ' = adjoint.
  (Two corrections were needed during verification: the off-diagonal D^2
  slot blocks (0,24)/(8,16), and the slot-24 Yukawa part being conj(Ynu'Ynu).
  See SPECTRAL_ACTION_84.md "numerical artifacts".)

Checkpoints to disk after every parameter point (reap-safe).
"""
import json
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "results3gen")
os.makedirs(OUT, exist_ok=True)
CKPT = os.path.join(OUT, "spectral_action_ckpt.json")

D32, GEN, DIM = 32, 3, 96

# ---------------------------------------------------------------- D_3 ansatz (copied from attack4_3gen.py; self-contained)


def build_dirac3(Ynu, Ye, Yu, Yd, MR):
    Ys = [Ynu, Ye, Yu, Yd, Yu, Yd, Yu, Yd]
    D = np.zeros((DIM, DIM), complex)
    for p in range(8):
        Y = Ys[p]
        for g in range(GEN):
            for gp in range(GEN):
                v = Y[g, gp]
                D[p * GEN + g, (8 + p) * GEN + gp] = v
                D[(8 + p) * GEN + gp, p * GEN + g] = v.conjugate()
                D[(16 + p) * GEN + g, (24 + p) * GEN + gp] = v.conjugate()
                D[(24 + p) * GEN + gp, (16 + p) * GEN + g] = v
    for g in range(GEN):
        for gp in range(GEN):
            v = MR[g, gp]
            D[24 * GEN + g, 8 * GEN + gp] = v
            D[8 * GEN + gp, 24 * GEN + g] = v.conjugate()
    return D


# ---------------------------------------------------------------- structural formulas
def frob2(M):
    return float((np.abs(M) ** 2).sum())


def q4(Y):
    """q(Y) = ||Y Y'||_F^2 = Tr((Y'Y)^2)."""
    return float(np.trace((Y.conj().T @ Y) @ (Y.conj().T @ Y)).real)


def struct_trD2(Ynu, Ye, Yu, Yd, MR):
    n2 = lambda M: float((np.abs(M) ** 2).sum())
    return (4 * (n2(Ynu) + n2(Ye) + 3 * n2(Yu) + 3 * n2(Yd))
            + 2 * n2(MR))


def struct_trD4(Ynu, Ye, Yu, Yd, MR):
    # Diagonal slot blocks: 4*sum_p q(Y_p) - 2*q(Ynu) [slots 8,24 E-mixing]
    # (verified block-by-block to 1e-15: slot-24 Yukawa part is conj(Ynu'Ynu))
    base = 4 * (q4(Ynu) + q4(Ye) + 3 * q4(Yu) + 3 * q4(Yd)) - 2 * q4(Ynu)
    A = Ynu.conj().T @ Ynu + MR.conj().T @ MR            # slot-8 D^2 block
    B = (Ynu.conj().T @ Ynu).conj() + MR @ MR.conj().T  # slot-24 D^2 block
    # Off-diagonal D^2 slot blocks (0,24),(24,0),(8,16),(16,8),
    # each of Frobenius norm ||Ynu MR'||_F (MR symmetric => norms coincide)
    cross = 4 * float((np.abs(Ynu @ MR.conj().T) ** 2).sum())
    return base + float((np.abs(A) ** 2).sum()) + float((np.abs(B) ** 2).sum()) + cross


# ---------------------------------------------------------------- parameter points
rng = np.random.default_rng(20260927)


def randU3():
    Q, _ = np.linalg.qr(rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3)))
    return Q


def point_hierarchical():
    Yu = np.diag([1e-5, 1e-2, 1.0])
    Yd = np.diag([1e-4, 1e-2, 5e-2])
    Ye = np.diag([1e-6, 1e-3, 1e-2])
    Ynu = np.diag([1e-12, 1e-11, 1e-10])
    MR = np.diag([10.0, 30.0, 100.0])  # moderate seesaw (numerics; physical would be >>)
    return dict(Ynu=Ynu, Ye=Ye, Yu=Yu, Yd=Yd, MR=MR)


def point_random():
    R = lambda: rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3))
    A = R()
    return dict(Ynu=R(), Ye=R(), Yu=R(), Yd=R(), MR=A + A.T)


def point_mixed():
    # CKM-like: Yu, Yd rotated by random unitaries; MR = 50 I (symmetric)
    Yu = randU3() @ np.diag([1e-5, 1e-2, 1.0]) @ randU3().conj().T
    Yd = randU3() @ np.diag([1e-4, 1e-2, 5e-2]) @ randU3().conj().T
    Ye = np.diag([1e-6, 1e-3, 1e-2])
    Ynu = np.diag([1e-12, 1e-11, 1e-10])
    MR = 50.0 * np.eye(3)
    return dict(Ynu=Ynu, Ye=Ye, Yu=Yu, Yd=Yd, MR=MR)


POINTS = [
    ("hierarchical", point_hierarchical),
    ("random", point_random),
    ("mixed", point_mixed),
]


def save_ckpt(results):
    tmp = CKPT + ".tmp"
    with open(tmp, "w") as f:
        json.dump(results, f, indent=1)
    os.replace(tmp, CKPT)


def main():
    results = {}
    if os.path.exists(CKPT):
        with open(CKPT) as f:
            results = json.load(f)
        print(f"resumed: {len(results)} points already done")

    for name, fn in POINTS:
        if name in results:
            print(f"-- {name}: cached, skipping")
            continue
        P = fn()
        D = build_dirac3(**P)
        # basic checks
        r_sa = float(np.linalg.norm(D.conj().T - D))
        tr1 = DIM
        trD = float(np.trace(D).real)
        D2 = D @ D
        trD2_b = float(np.trace(D2).real)
        trD2_s = struct_trD2(**P)
        D4 = D2 @ D2
        trD4_b = float(np.trace(D4).real)
        trD4_s = struct_trD4(**P)
        trD3 = float(np.trace(D2 @ D).real)
        # CCM-style invariants (our normalization: Tr(D^2) = 4a + 2||MR||^2)
        n2 = lambda M: float((np.abs(M) ** 2).sum())
        a_ccm = n2(P["Ynu"]) + n2(P["Ye"]) + 3 * n2(P["Yu"]) + 3 * n2(P["Yd"])
        b_ccm = q4(P["Ynu"]) + q4(P["Ye"]) + 3 * q4(P["Yu"]) + 3 * q4(P["Yd"])
        rel2 = abs(trD2_b - trD2_s) / max(trD2_b, 1e-300)
        rel4 = abs(trD4_b - trD4_s) / max(trD4_b, 1e-300)
        results[name] = dict(
            tr1=tr1, trD=trD, trD3=trD3,
            trD2_brute=trD2_b, trD2_struct=trD2_s, relerr_D2=rel2,
            trD4_brute=trD4_b, trD4_struct=trD4_s, relerr_D4=rel4,
            selfadjoint_res=r_sa, a_ccm=a_ccm, b_ccm=b_ccm,
            MR_scale=float(np.abs(P["MR"]).max()),
        )
        print(f"-- {name}: Tr(D^2) brute={trD2_b:.6e} struct={trD2_s:.6e} relerr={rel2:.2e}")
        print(f"           Tr(D^4) brute={trD4_b:.6e} struct={trD4_s:.6e} relerr={rel4:.2e}")
        print(f"           Tr(D)={trD:.2e} Tr(D^3)={trD3:.2e} ||D*-D||={r_sa:.2e}")
        print(f"           a_ccm={a_ccm:.6e} b_ccm={b_ccm:.6e}")
        save_ckpt(results)

    print("checkpoint:", CKPT)


if __name__ == "__main__":
    main()
