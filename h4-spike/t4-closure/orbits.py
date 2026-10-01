"""SA/J orbits on support72. Do 11 pivots determine all via SA/J?"""
import numpy as np

N = 32
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
pivots = [(0,8),(1,9),(2,10),(3,11),(24,8),(0,9),(1,8),(2,11),(3,10),(8,25),(9,25)]

# SA/J orbit: (i,j) -> (j,i) [SA], (i,j) -> (partner[j], partner[i]) [J]
def orbit(i, j):
    seen = set(); stack = [(i,j)]
    while stack:
        (a,b) = stack.pop()
        if (a,b) in seen: continue
        seen.add((a,b))
        stack.append((b,a))
        stack.append((partner[b], partner[a]))
    return seen

# check all orbits stay in target and each orbit contains a pivot (or pivot-related)
orbits = []
seen = set()
for (i,j) in target:
    if (i,j) in seen: continue
    o = orbit(i,j)
    assert o <= target, f"orbit escapes: {o - target}"
    orbits.append(o)
    seen |= o
print("num SA/J orbits on support72:", len(orbits))
print("orbit sizes:", sorted([len(o) for o in orbits]))
# does each orbit contain a pivot?
pset = set(pivots)
for idx, o in enumerate(orbits):
    inter = o & pset
    # also check SA/J variants of pivots (conjugates)
    print(f"orbit {idx}: size {len(o)}, contains pivot: {len(inter)>0}, sample {sorted(o)[:4]}")
