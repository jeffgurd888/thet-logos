"""Do 16 diagonal pairs + grading/cf kill ALL entries outside support72?"""
import numpy as np

N = 32
gamma = np.array([1]*8 + [-1]*8 + [-1]*8 + [1]*8)
S = set(list(range(18)) + [24, 25])
partner = np.array([i+16 if i < 16 else i-16 for i in range(N)])

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

# allowed by grading+cf
def in_allowed(i,j):
    return gamma[i] != gamma[j] and ((i in S) == (j in S))

lamC = np.array([1 if (8 <= i < 16) or i in (16,17,24,25) else 0 for i in range(N)], dtype=float)
lamH2 = np.array([1 if i < 8 and i % 2 == 0 else (-1 if i < 8 else 0) for i in range(N)], dtype=float)
lamM2 = np.zeros(N)
for t in [(18,20,22),(19,21,23),(26,28,30),(27,29,31)]: lamM2[t[0]] = 1; lamM2[t[1]] = -1
lamM7 = np.zeros(N)
for t in [(18,20,22),(19,21,23),(26,28,30),(27,29,31)]: lamM7[t[0]] = 1; lamM7[t[1]] = 1; lamM7[t[2]] = -2
diag_gens = [lamC, lamH2, lamM2, lamM7]
diag_opps = [v[partner] for v in diag_gens]

# For each (i,j) not in target, check if killed by grading/cf OR by some diagonal pair
unkilled = []
for i in range(N):
    for j in range(N):
        if (i,j) in target: continue
        if not in_allowed(i,j): continue  # killed by grading/cf
        killed = False
        for lam in diag_gens:
            for mu in diag_opps:
                if lam[i] != lam[j] and mu[i] != mu[j]:
                    killed = True; break
            if killed: break
        if not killed:
            unkilled.append((i,j))
print("unkilled by (grading/cf OR diagonal):", len(unkilled))
if unkilled:
    print(unkilled[:30])
else:
    print("SUCCESS: all non-support entries killed by linear + diagonal!")
