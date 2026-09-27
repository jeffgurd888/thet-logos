"""Order-zero numerical check (Tier T3).

Verifies [pi(a), piOp(pi(b))] = 0 for the 24 AF generators and random
algebra elements, following the framework's illustrative fragment (Sec. 4).
Also verifies the KO sign U_J conj(gamma_F) U_J = -gamma_F and U_J^2 = 1.
"""
import numpy as np
from .common import (pi, piOp, af_generators, random_af, gamma_F, UJ, partner)

SEED = 2026
TOL = 1e-10


def check_order_zero():
    gens = af_generators()
    worst = 0.0
    for a in gens:
        pa = pi(a)
        for b in gens:
            comm = pa @ piOp(pi(b)) - piOp(pi(b)) @ pa
            worst = max(worst, np.max(np.abs(comm)))
    return worst


def check_ko_relations():
    U = UJ()
    g = gamma_F()
    err_J2 = np.max(np.abs(U @ U - np.eye(32)))
    err_sign = np.max(np.abs(U @ g.conj() @ U + g))
    # chi_{p(k)} = -chi_k
    chi = np.diag(g).real
    err_chi = max(abs(chi[partner(k)] + chi[k]) for k in range(32))
    return err_J2, err_sign, err_chi


def main():
    rng = np.random.default_rng(SEED)
    w = check_order_zero()
    print(f"[OrderZero] max |[pi(a), piOp(pi(b))]| over 24x24 generators: {w:.3e}")
    assert w < TOL, "order-zero FAILED on generators"
    wr = 0.0
    for _ in range(10):
        a, b = random_af(rng), random_af(rng)
        comm = pi(a) @ piOp(pi(b)) - piOp(pi(b)) @ pi(a)
        wr = max(wr, np.max(np.abs(comm)))
    print(f"[OrderZero] max commutator over 10 random pairs: {wr:.3e}")
    assert wr < TOL, "order-zero FAILED on random elements"
    eJ2, eS, eC = check_ko_relations()
    print(f"[OrderZero] U_J^2=1 err {eJ2:.3e}; U_J conj(gF) U_J=-gF err {eS:.3e}; "
          f"chi flip err {eC:.3e}")
    assert eJ2 < 1e-12 and eS < 1e-12 and eC < 1e-12
    print("[OrderZero] PASS")
    return True


if __name__ == "__main__":
    main()
