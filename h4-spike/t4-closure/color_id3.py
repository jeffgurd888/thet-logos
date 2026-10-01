"""(C, M_0°) and (H, M_0°) for color identification."""
import numpy as np

N = 32
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
def build_genC():
    C = np.zeros((N,N), dtype=complex)
    for i in list(range(8,16)) + [16,17,24,25]:
        C[i,i] = 1j
    return C
gm = build_genM(); UJ = build_UJ(); gC = build_genC()
Mop = [UJ @ M.T @ UJ for M in gm]

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

# (C, M0°): A=genC, B=M0°
A = gC; B = Mop[0]
print("(C, M0°):")
for (i,j) in [(2,10),(4,12),(2,12),(4,10)]:
    f = linform(A,B,i,j)
    rel = {k:round(v.real,3)+round(v.imag,3)*1j for k,v in f.items() 
           if k[0] in range(2,8) and k[1] in range(10,16)}
    print(f"  at ({i},{j}): {rel}")
