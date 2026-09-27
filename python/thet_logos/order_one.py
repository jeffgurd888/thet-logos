"""Order-one probes (Tier T3 numerical; full 576-pair = Tier T5 open).

1. Single-probe: [[D, P+], P-] with P+ / P- the particle/antiparticle
   projectors. Shows the probe commutator vanishes iff C = E = 0.
2. Full census attempt: [[D, pi(a)], piOp(pi(b))] over all 24x24 = 576
   generator pairs for the one-generation D_F (C = E = 0). Reports the
   max norm honestly -- this is numerical evidence, not a proof.
"""
import numpy as np
from .common import (pi, piOp, af_generators, buildDirac, DF_oneGen,
                     random_block, DIM, HALF)

SEED = 2026


def projectors():
    Pp = np.zeros((DIM, DIM), dtype=complex)
    Pm = np.zeros((DIM, DIM), dtype=complex)
    Pp[:HALF, :HALF] = np.eye(HALF)
    Pm[HALF:, HALF:] = np.eye(HALF)
    return Pp, Pm


def single_probe(D):
    Pp, Pm = projectors()
    inner = D @ Pp - Pp @ D
    return inner @ Pm - Pm @ inner


def order_one_comm(D, a, b):
    inner = D @ pi(a) - pi(a) @ D
    opb = piOp(pi(b))
    return inner @ opb - opb @ inner


def main():
    rng = np.random.default_rng(SEED)
    Pp, Pm = projectors()

    # --- single probe: C, E != 0 -> nonzero; C = E = 0 -> zero ---
    A = random_block(rng)
    B = A.conj()
    C = random_block(rng)
    E = random_block(rng)
    D_bad = buildDirac(A, B, C, E)
    n_bad = np.max(np.abs(single_probe(D_bad)))
    D_good = buildDirac(A, B, np.zeros((8, 8), complex), np.zeros((8, 8), complex))
    n_good = np.max(np.abs(single_probe(D_good)))
    print(f"[OrderOne] single-probe |[[D,P+],P-]| with C,E != 0 : {n_bad:.3e}")
    print(f"[OrderOne] single-probe |[[D,P+],P-]| with C=E=0     : {n_good:.3e}")
    assert n_bad > 1e-6, "probe should detect nonzero C, E"
    assert n_good < 1e-10, "probe should vanish for C = E = 0"

    # --- full 576-pair census on the one-generation model ---
    D = DF_oneGen(0.5, 0.7, 1.1, 0.9, rng)
    # sanity: D self-adjoint and gamma-odd
    from .common import gamma_F
    g = gamma_F()
    assert np.max(np.abs(D.conj().T - D)) < 1e-12
    assert np.max(np.abs(g @ D + D @ g)) < 1e-12
    gens = af_generators()
    worst = 0.0
    for a in gens:
        for b in gens:
            worst = max(worst, np.max(np.abs(order_one_comm(D, a, b))))
    print(f"[OrderOne] 576-pair census max |[[D,pi(a)],piOp(pi(b))]| : {worst:.3e}")
    print("[OrderOne] (numerical evidence only -- Tier T3, not a proof)")
    print("[OrderOne] PASS")
    return True


if __name__ == "__main__":
    main()
