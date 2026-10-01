"""Constraint structure analysis for W22 dimension bound."""
import numpy as np

N = 32

# gammaF = diag(+1x8, -1x8, -1x8, +1x8)
gamma = np.array([1]*8 + [-1]*8 + [-1]*8 + [1]*8)

# cfMat support S = {0..17, 24, 25}
S = set(list(range(18)) + [24, 25])
cf = np.array([1 if i in S else 0 for i in range(N)])

# partner: i -> i+16 if i<16 else i-16
partner = np.array([i+16 if i < 16 else i-16 for i in range(N)])

# genC eigenvalues
lamC = np.array([1j if (8 <= i < 16) or i in (16,17,24,25) else 0 for i in range(N)], dtype=complex)
# smGenOp(genC) = UJ genC UJ eigenvalues: mu(i) = lamC(partner(i))
muC = lamC[partner]

print("lambda_C nonzero:", sorted(np.where(lamC != 0)[0]))
print("mu_C nonzero:", sorted(np.where(muC != 0)[0]))

# Allowed by grading + cf (the L set)
E = set([i for i in range(N) if gamma[i] == 1])
O = set([i for i in range(N) if gamma[i] == -1])
ES = E & S; ET = E - S; OS = O & S; OT = O - S
print("E&S:", sorted(ES), " E&T:", sorted(ET))
print("O&S:", sorted(OS), " O&T:", sorted(OT))
L = (ES | set())  # placeholder
allowed = set()
for i in ES:
    for j in OS: allowed.add((i,j))
for i in ET:
    for j in OT: allowed.add((i,j))
for i in OS:
    for j in ES: allowed.add((i,j))
for i in OT:
    for j in ET: allowed.add((i,j))
print("|allowed by grading+cf|:", len(allowed))

# J-orbit: D(i,j) = D(partner j, partner i); SA: D(i,j) = conj(D(j,i))
# D(i,j) forced zero if any of {(i,j),(partner j,partner i),(j,i),(partner i,partner j)} outside allowed
def orbit(i, j):
    return {(i,j), (partner[j], partner[i]), (j,i), (partner[i], partner[j])}

surv = [(i,j) for (i,j) in allowed if all(p in allowed for p in orbit(i,j))]
print("|surviving 4 linear conditions|:", len(surv))

# (C,C°) order-one: D(i,j)*(lam(j)-lam(i))*(mu(j)-mu(i)) = 0
L1 = set(np.where(lamC != 0)[0]); L0 = set(np.where(lamC == 0)[0])
M1 = set(np.where(muC != 0)[0]); M0 = set(np.where(muC == 0)[0])
def cc_ok(i, j):
    return ( (i in L1) == (j in L1) ) or ( (i in M1) == (j in M1) )
surv2 = [(i,j) for (i,j) in surv if cc_ok(i,j)]
print("|surviving + (C,C°)|:", len(surv2))
