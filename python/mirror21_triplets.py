#!/usr/bin/env python3
"""T2 companion for the TRIPLETS OF CORRELATIONS brick (MirrorTwentyOneTriplets).

TIER: T2 — a finite enumeration CHECKER. It recomputes the scoping ground truth
over Z_21^3 by brute force and asserts each number. It proves nothing; the T1
proofs live in lean/ThetLogos/MirrorTwentyOneTriplets.lean. Numbers checked:
  ordered resonant triples            441 = 21^2
  containing zero                     61  (60 doublet+center, + the origin)
  all-nonzero                         380
  all-distinct ordered                324
  all-distinct unordered sets         54
  within one gcd family (all-nonzero) 92
  mixing families   (all-nonzero)     288
NO CLAIM; dials 0/4.
"""
from math import gcd

N = 21
res = [(a, b, c) for a in range(N) for b in range(N) for c in range(N)
       if (a + b + c) % N == 0]
assert len(res) == 441, len(res)

with_zero = [t for t in res if 0 in t]
assert len(with_zero) == 61, len(with_zero)

nonzero = [t for t in res if 0 not in t]
assert len(nonzero) == 380, len(nonzero)

distinct = [t for t in nonzero if len(set(t)) == 3]
assert len(distinct) == 324, len(distinct)
assert len({frozenset(t) for t in distinct}) == 54

def fam(x):
    return gcd(x, N)

within = [t for t in nonzero if fam(t[0]) == fam(t[1]) == fam(t[2])]
mixing = [t for t in nonzero if not (fam(t[0]) == fam(t[1]) == fam(t[2]))]
assert len(within) == 92, len(within)
assert len(mixing) == 288, len(mixing)

# mirror organization: negation pairs + lone fixed (0,0,0)
resset = set(res)
seen, pairs = set(), 0
for t in res:
    if t in seen:
        continue
    m = tuple((-x) % N for x in t)
    assert m in resset
    if m == t:
        assert t == (0, 0, 0)
        seen.add(t)
    else:
        pairs += 1
        seen.add(t); seen.add(m)
assert pairs == 220, pairs

print("mirror21_triplets T2: 441 total / 61 with zero / 380 all-nonzero / "
      "324 distinct ordered / 54 unordered / 92 within-family / 288 mixing / "
      "220 mirror pairs + (0,0,0) — ALL CHECKS PASS")
