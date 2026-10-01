"""Pattern of killers for the 24 fundamental quark entries (HL x HR)."""
import numpy as np

N = 32
partner = np.array([i+16 if i < 16 else i-16 for i in range(N)])
# the 24: i in 2..7, j in 10..15, minus SM (i,i+8) and exotic
sm_ex = set()
for i in range(2,8): sm_ex.add((i,i+8))
sm_ex |= {(2,11),(4,13),(6,15),(3,10),(5,12),(7,14)}
fund = [(i,j) for i in range(2,8) for j in range(10,16) if (i,j) not in sm_ex]
print(len(fund), "fundamental entries")

lamC = np.array([1 if (8 <= i < 16) or i in (16,17,24,25) else 0 for i in range(N)], dtype=float)
lamH2 = np.array([1 if i < 8 and i % 2 == 0 else (-1 if i < 8 else 0) for i in range(N)], dtype=float)
lamM2 = np.zeros(N)
for t in [(18,20,22),(19,21,23),(26,28,30),(27,29,31)]: lamM2[t[0]] = 1; lamM2[t[1]] = -1
lamM7 = np.zeros(N)
for t in [(18,20,22),(19,21,23),(26,28,30),(27,29,31)]: lamM7[t[0]] = 1; lamM7[t[1]] = 1; lamM7[t[2]] = -2
diag_gens = {"C": lamC, "H2": lamH2, "M2": lamM2, "M7": lamM7}
diag_opps = {k: v[partner] for k, v in diag_gens.items()}
names = {"C":0, "H2":3, "M2":6, "M7":11}  # smGen indices

for (i,j) in fund:
    killers = []
    for a, lam in diag_gens.items():
        for b, mu in diag_opps.items():
            if lam[i] != lam[j] and mu[i] != mu[j]:
                killers.append(f"({a},{b}°)")
    print(f"({i},{j}): {killers}")
