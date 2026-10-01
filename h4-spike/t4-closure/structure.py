"""Analyze W22 nullspace: support pattern, parametrization."""
import numpy as np

W22mats = np.load("/tmp/dim_analysis/w22mats.npy")  # (22, 32, 32) complex
d = W22mats.shape[0]
print("dim:", d)

# Which entries can be nonzero?
can_nz = np.zeros((32,32), dtype=bool)
for k in range(d):
    can_nz |= (np.abs(W22mats[k]) > 1e-8)
print("|support|:", can_nz.sum())

# SM support
sm = set()
for i in range(8):
    sm.add((i,i+8)); sm.add((i+8,i)); sm.add((i+16,i+24)); sm.add((i+24,i+16))
sm.add((8,24)); sm.add((24,8))
# exotic supports
ex = set()
ex |= {(0,9),(9,0),(16,25),(25,16)}
ex |= {(1,8),(8,1),(17,24),(24,17)}
for (a,b) in [(2,11),(4,13),(6,15)]:
    ex |= {(a,b),(b,a),(a+16,b+16),(b+16,a+16)}
for (a,b) in [(3,10),(5,12),(7,14)]:
    ex |= {(a,b),(b,a),(a+16,b+16),(b+16,a+16)}
ex |= {(8,25),(25,8),(24,9),(9,24)}
ex |= {(9,25),(25,9)}
print("|SM|:", len(sm), "|exotic|:", len(ex), "|union|:", len(sm|ex))
print("disjoint:", len(sm & ex) == 0)
nz_set = set(map(tuple, np.argwhere(can_nz)))
print("nullspace support == SM|exotic:", nz_set == (sm | ex))
print("nullspace support subset of SM|exotic:", nz_set <= (sm | ex))
print("SM|exotic subset of nullspace support:", (sm | ex) <= nz_set)
if nz_set != (sm | ex):
    print("extra:", sorted(nz_set - (sm|ex))[:20])
    print("missing:", sorted((sm|ex) - nz_set)[:20])
