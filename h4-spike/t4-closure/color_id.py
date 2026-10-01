"""Find (M_a, M_b°) pairs that identify color copies, e.g. D(4,12) = D(2,10)."""
import numpy as np

N = 32
# Build genM matrices
def build_genM():
    gm = []
    for a in range(8):
        M = np.zeros((N,N), dtype=complex)
        if a == 0: G = np.array([[0,1,0],[1,0,0],[0,0,0]], dtype=complex)
        elif a == 1: G = np.array([[0,-1j,0],[1j,0,0],[0,0,0]], dtype=complex)
        elif a == 2: G = np.array([[1,0,0],[0,-1,0],[0,0,0]], dtype=complex)
        elif a == 3: G = np.array([[0,0,1],[0,0,0],[1,0,0]], dtype=complex)
        elif a == 4: G = np.array([[0,0,-1j],[0,0,0],[1j,0,0]], dtype=complex)
        elif a == 5: G = np.array([[0,0,0],[0,0,1],[0,1,0]], dtype=complex)
        elif a == 6: G = np.array([[0,0,0],[0,0,-1j],[0,1j,0]], dtype=complex)
        elif a == 7: G = np.array([[1,0,0],[0,1,0],[0,0,-2]], dtype=complex)/np.sqrt(3)
        for t in [(18,20,22),(19,21,23),(26,28,30),(27,29,31)]:
            for ii in range(3):
                for jj in range(3):
                    M[t[ii],t[jj]] = G[ii,jj]
        gm.append(M)
    return gm

def build_UJ():
    UJ = np.zeros((N,N), dtype=complex)
    for i in range(N):
        j = i+16 if i < 16 else i-16
        UJ[j,i] = 1.0
    return UJ

gm = build_genM(); UJ = build_UJ()
smGenOp_M = [UJ @ M.T @ UJ for M in gm]  # M_b°

# We want: which (a,b) gives [[D,M_a],M_b°](i,j) = c1*D(4,12) + c2*D(2,10) + ... = 0
# that forces D(4,12) = D(2,10)?
# Let's look at the linear form at specific (i,j) positions.
# Actually simpler: the constraint must hold for ALL D in W22, so let's see
# which (a,b,i,j) gives a relation involving D(4,12) and D(2,10).

# For each (a,b), compute the constraint matrix C = [[., M_a], M_b°] as linear op on D.
# We want C(D)(i,j) to involve D(4,12) - D(2,10).
# Let's just check: for D in nullspace, D(4,12)-D(2,10) should be 0 (verify), 
# then find (a,b,i,j) where the equation is "simple".

# Actually, let me directly search for simple identification equations.
# For each (a,b), and each (i,j), express [[D,M_a],M_b°](i,j) as lin combo of D entries.
# Find ones that are proportional to (D(p,q) - D(r,s)) for color pairs.

# Simpler: brute force check which (a,b) pairs, when imposed, force color-univ.
# We know full order-one gives 22. Let's see which M-pairs are essential for color.

# Let's do: for each (a,b) in M x M°, compute its constraint matrix, 
# and see its effect on the color-copy entries.
print("Searching for color-identification pairs...")
# Focus on D(4,12) vs D(2,10). 
# The identification D(4,12)=D(2,10) means the vector v with v(4,12)=1, v(2,10)=-1 is in ker of constraints.
# Actually, we want a constraint that HAS to involve this difference.

# Let me just compute, for each (a,b), the nullspace of JUST that pair's constraints
# intersected with V4, and see the dimension / whether color-univ holds.
print("(this is exploratory)")
