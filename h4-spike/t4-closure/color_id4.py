"""(M0,M0°) on anti-quark block for color ID."""
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
gm = build_genM(); UJ = build_UJ()
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

# (M0, M0°) on anti-quark SM entries
A = gm[0]; B = Mop[0]
print("(M0, M0°) on anti-quark block:")
for (i,j) in [(18,26),(20,28),(18,28),(20,26)]:
    f = linform(A,B,i,j)
    rel = {k:(round(v.real,3),round(v.imag,3)) for k,v in f.items()
           if k[0] in range(18,24) and k[1] in range(26,32)}
    print(f"  at ({i},{j}): {rel}")
