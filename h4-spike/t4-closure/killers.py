"""Find which order-one pairs give clean entrywise kills. Focus on diagonal generators."""
import numpy as np

N = 32
gamma = np.array([1]*8 + [-1]*8 + [-1]*8 + [1]*8)
S = set(list(range(18)) + [24, 25])
partner = np.array([i+16 if i < 16 else i-16 for i in range(N)])

# surviving 176 from 4 linear conditions (recompute)
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

# target support (72)
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
extra = sorted(surv - target)
print("|surv|:", len(surv), "|target|:", len(target), "|extra to kill|:", len(extra))

# Diagonal generators: genC, genM(2), genM(7). Compute their eigenvalue patterns.
lamC = np.array([1 if (8 <= i < 16) or i in (16,17,24,25) else 0 for i in range(N)])
muC = lamC[partner]
# genM(2) = lambda3 = diag(1,-1,0) on triplets T0=(18,20,22),T1=(19,21,23),T2=(26,28,30),T3=(27,29,31)
lamM2 = np.zeros(N)
for t in [(18,20,22),(19,21,23),(26,28,30),(27,29,31)]:
    lamM2[t[0]] = 1; lamM2[t[1]] = -1; lamM2[t[2]] = 0
muM2 = lamM2[partner]
# genM(7) = lambda8 = diag(1,1,-2)/sqrt3
lamM7 = np.zeros(N)
for t in [(18,20,22),(19,21,23),(26,28,30),(27,29,31)]:
    lamM7[t[0]] = 1; lamM7[t[1]] = 1; lamM7[t[2]] = -2
muM7 = lamM7[partner]

def kills(lam, mu):
    """Entries (i,j) in surv with (lam_i != lam_j and mu_i != mu_j) are killed."""
    k = []
    for (i,j) in surv:
        if lam[i] != lam[j] and mu[i] != mu[j]:
            k.append((i,j))
    return set(k)

kC = kills(lamC, muC)
kM2 = kills(lamM2, muM2)
kM7 = kills(lamM7, muM7)
print("(C,C°) kills:", len(kC & set(extra)), "of", len(extra))
print("(M2,M2°) kills:", len(kM2 & set(extra)))
print("(M7,M7°) kills:", len(kM7 & set(extra)))
union = (kC | kM2 | kM7) & set(extra)
print("union kills:", len(union))
remaining = set(extra) - union
print("remaining:", len(remaining))
if remaining:
    print(sorted(remaining)[:40])
