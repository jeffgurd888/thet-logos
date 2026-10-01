"""All 16 diagonal-diagonal pairs (C,H2,M2,M7) x (C°,H2°,M2°,M7°)."""
import numpy as np

N = 32
gamma = np.array([1]*8 + [-1]*8 + [-1]*8 + [1]*8)
S = set(list(range(18)) + [24, 25])
partner = np.array([i+16 if i < 16 else i-16 for i in range(N)])
E = set(i for i in range(N) if gamma[i]==1); O = set(i for i in range(N) if gamma[i]==-1)
ES = E & S; ET = E - S; OS = O & S; OT = O - S
allowed = set()
for i in ES:
    for j in OS: allowed.add((i,j))
for i in ET:
    for j in OT: allowed.add((i,j))
for i in OS:
    for j in ES: allowed.add((i,j))
for i in OT:
    for j in ET: allowed.add((i,j))
def orbit(i, j):
    return {(i,j), (partner[j], partner[i]), (j,i), (partner[i], partner[j])}
surv = set((i,j) for (i,j) in allowed if all(p in allowed for p in orbit(i,j)))
sm = set()
for i in range(8):
    sm.add((i,i+8)); sm.add((i+8,i)); sm.add((i+16,i+24)); sm.add((i+24,i+16))
sm.add((8,24)); sm.add((24,8))
ex = set()
ex |= {(0,9),(9,0),(16,25),(25,16)}
ex |= {(1,8),(8,1),(17,24),(24,17)}
for (a,b) in [(2,11),(4,13),(6,15)]: ex |= {(a,b),(b,a),(a+16,b+16),(b+16,a+16)}
for (a,b) in [(3,10),(5,12),(7,14)]: ex |= {(a,b),(b,a),(a+16,b+16),(b+16,a+16)}
ex |= {(8,25),(25,8),(24,9),(9,24)}
ex |= {(9,25),(25,9)}
target = sm | ex
extra = set(surv - target)

# diagonal generator eigenvalues
lamC = np.array([1 if (8 <= i < 16) or i in (16,17,24,25) else 0 for i in range(N)], dtype=float)
# genH(2) = sigma3 on doublets (2I,2I+1): +1 on even, -1 on odd, for I=0..3 (indices 0-7)
lamH2 = np.array([1 if i < 8 and i % 2 == 0 else (-1 if i < 8 else 0) for i in range(N)], dtype=float)
lamM2 = np.zeros(N)
for t in [(18,20,22),(19,21,23),(26,28,30),(27,29,31)]:
    lamM2[t[0]] = 1; lamM2[t[1]] = -1
lamM7 = np.zeros(N)
for t in [(18,20,22),(19,21,23),(26,28,30),(27,29,31)]:
    lamM7[t[0]] = 1; lamM7[t[1]] = 1; lamM7[t[2]] = -2
diag_gens = {"C": lamC, "H2": lamH2, "M2": lamM2, "M7": lamM7}
# opposites: mu(i) = lam(partner(i))
diag_opps = {k: v[partner] for k, v in diag_gens.items()}

def kills(lam, mu):
    k = set()
    for (i,j) in surv:
        if lam[i] != lam[j] and mu[i] != mu[j]:
            k.add((i,j))
    return k & extra

# individual
for a, lam in diag_gens.items():
    for b, mu in diag_opps.items():
        k = kills(lam, mu)
        if k:
            print(f"({a},{b}°) kills {len(k)}")
# union
union = set()
for lam in diag_gens.values():
    for mu in diag_opps.values():
        union |= kills(lam, mu)
print("union kills:", len(union), "of", len(extra))
rem = extra - union
print("remaining:", len(rem))
if rem:
    print(sorted(rem))
