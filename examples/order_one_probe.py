"""Worked example: the order-one single probe (Tier T3 numerical).

Shows that the probe commutator [[D, P+], P-] detects the cross-sector
Majorana blocks: it is nonzero when C, E != 0 and vanishes exactly when
C = E = 0 -- the Tier T4 statement (vanishing cross-terms under
order-one, standard one-generation NCG).

This is a probe/simulation, NOT the full 576-pair theorem
(Tier T5 open). Theorem != Simulation.
"""
import sys
sys.path.insert(0, "../python")
import numpy as np
from thet_logos.common import buildDirac, random_block, DIM, HALF

rng = np.random.default_rng(2026)
A = random_block(rng)
B = A.conj()

Pp = np.zeros((DIM, DIM), complex); Pp[:HALF, :HALF] = np.eye(HALF)
Pm = np.zeros((DIM, DIM), complex); Pm[HALF:, HALF:] = np.eye(HALF)

def probe(D):
    inner = D @ Pp - Pp @ D
    return inner @ Pm - Pm @ inner

print("=== Order-one single probe ===")
for label, (C, E) in [("C,E random nonzero", (random_block(rng), random_block(rng))),
                      ("C=E=0", (np.zeros((8, 8), complex), np.zeros((8, 8), complex)))]:
    D = buildDirac(A, B, C, E)
    n = np.max(np.abs(probe(D)))
    print(f"  {label:20s}  max |[[D,P+],P-]| = {n:.3e}")

print("\nConclusion: the probe forces C = E = 0 (Tier T3 numerical).")
print("The full 576-pair condition remains Tier T5 (open).")
