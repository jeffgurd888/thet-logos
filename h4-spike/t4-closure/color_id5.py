"""Systematic search for D(4,12)=D(2,10) equation."""
import numpy as np

N = 32
def build_gens():
    # genC
    gC = np.zeros((N,N), dtype=complex)
    for i in list(range(8,16)) + [16,17,24,25]: gC[i,i] = 1j
    # genH(k)
    gH = []
    for k in range(3):
        H = np.zeros((N,N), dtype=complex)
        P = [np.array([[0,1],[1,0]]), np.array([[0,-1j],[1j,0]]), np.array([[1,0],[0,-1]])][k]
        for I in range(4):
            H[2*I:2*I+2, 2*I:2*I+2] = P
        gH.append(H)
    # genM(a)
    gM = []
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
                for jj in range(3): M[t[ii],t[jj]] = G[ii,jj]
        gM.append(M)
    return gC, gH, gM
def build_UJ():
    UJ = np.zeros((N,N), dtype=complex)
    for i in range(N):
        j = i+16 if i < 16 else i-16
        UJ[j,i] = 1.0
    return UJ

gC, gH, gM = build_gens(); UJ = build_UJ()
smGen = [gC] + gH + gM  # 12 gens: 0=C, 1-3=H, 4-11=M
smGenOp = [UJ @ A.T @ UJ for A in smGen]

def linform(A, B, i, j):
    d = {}
    for p in range(N):
        for q in range(N):
            c = A[p,q]*B[q,j]
            if abs(c) > 1e-12: d[(i,p)] = d.get((i,p),0) + c
    for p in range(N):
        for q in range(N):
            c = -A[i,p]*B[q,j]
            if abs(c) > 1e-12: d[(p,q)] = d.get((p,q),0) + c
    for p in range(N):
        for q in range(N):
            c = -B[i,p]*A[p,q]
            if abs(c) > 1e-12: d[(q,j)] = d.get((q,j),0) + c
    for p in range(N):
        for q in range(N):
            c = A[i,p]*B[p,q]
            if abs(c) > 1e-12: d[(q,j)] = d.get((q,j),0) + c
    return {k:v for k,v in d.items() if abs(v) > 1e-9}

# Search all (a,b,i,j) for forms proportional to D(4,12)-D(2,10)
# (allow linear combos, but look for simple ones)
target = {(4,12):1, (2,10):-1}
found = []
for a in range(12):
    for b in range(12):
        A = smGen[a]; B = smGenOp[b]
        for i in range(N):
            for j in range(N):
                f = linform(A,B,i,j)
                # check if f is supported on {(4,12),(2,10)} and proportional to target
                if set(f.keys()) <= {(4,12),(2,10)} and len(f) == 2:
                    v1 = f.get((4,12),0); v2 = f.get((2,10),0)
                    if abs(v1) > 1e-9 and abs(v2) > 1e-9 and abs(v1+v2) < 1e-9:
                        found.append((a,b,i,j,v1))
                        # print and break
if found:
    print("Found identifications:")
    for (a,b,i,j,v) in found[:10]:
        print(f"  (a={a},b={b}) at ({i},{j}): coeff {v}")
else:
    print("No simple D(4,12)-D(2,10) equation found.")
    print("Trying linear combinations...")
