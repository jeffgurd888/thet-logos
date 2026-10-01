"""Full pattern of 104 entries; group by sector. Find killer pairs."""
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
extra = sorted(surv - target)
# group by (sector of i, sector of j)
def sector(i):
    if i < 8: return "HL"
    if i < 16: return "HR"
    if i < 24: return "HLc"
    return "HRc"
from collections import Counter
c = Counter((sector(i), sector(j)) for (i,j) in extra)
print("extra by sector:", dict(c))
print()
print("all extra:", extra)
