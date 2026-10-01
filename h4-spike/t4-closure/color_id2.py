"""Find explicit (M_a,M_b°,i,j) giving D(4,12)=D(2,10)."""
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

# Build V4 basis (92-dim) as before, then for each (a,b,i,j), get the linear equation
# and see if it simplifies to a color identification on V4.
import sys
sys.path.insert(0, '/tmp/dim_analysis')
# Reuse V4 construction - quick version
gamma = np.array([1]*8 + [-1]*8 + [-1]*8 + [1]*8)
S = set(list(range(18)) + [24, 25])
partner = np.array([i+16 if i < 16 else i-16 for i in range(N)])
# Build V4 via nullspace (reuse from dim_proof)
# ... (skip full rebuild; instead directly test candidate equations)

# Candidate: (M0, M0°) at (2,10) or (4,12). Compute the linear form.
def comm(A,B): return A@B - B@A
def linform(A, B, i, j):
    """Return dict {(p,q): coeff} for [[D,A],B](i,j) as linear form in D."""
    # [[D,A],B](i,j) = sum_{p,q} c_{pq} D(p,q)
    # [[D,A],B] = DAB - ADB - BAD + ABD
    # (DAB)(i,j) = sum_{p,q} D(i,p) A(p,q) B(q,j)
    # etc. Let's compute coefficients.
    d = {}
    # DAB: D(i,p) A(p,q) B(q,j) -> D(i,p) coeff A(p,q)B(q,j)
    for p in range(N):
        for q in range(N):
            c = A[p,q]*B[q,j]
            if abs(c) > 1e-12:
                d[(i,p)] = d.get((i,p),0) + c
    # -ADB: -D(i,p) B? wait ADB = A D B. (ADB)(i,j) = sum A(i,p) D(p,q) B(q,j)
    for p in range(N):
        for q in range(N):
            c = -A[i,p]*B[q,j]
            if abs(c) > 1e-12:
                d[(p,q)] = d.get((p,q),0) + c
    # -BAD: -(BAD)(i,j) = -sum B(i,p) A(p,q) D(q,j)
    for p in range(N):
        for q in range(N):
            c = -B[i,p]*A[p,q]
            if abs(c) > 1e-12:
                d[(q,j)] = d.get((q,j),0) + c
    # +ABD: (ABD)(i,j) = sum A(i,p) B(p,q) D(q,j)
    for p in range(N):
        for q in range(N):
            c = A[i,p]*B[p,q]
            if abs(c) > 1e-12:
                d[(q,j)] = d.get((q,j),0) + c
    return {k:v for k,v in d.items() if abs(v) > 1e-9}

# Test (M0,M0°) at various (i,j), look for forms involving D(4,12), D(2,10)
A = gm[0]; B = Mop[0]
for (i,j) in [(2,10),(4,12),(2,12),(4,10)]:
    f = linform(A,B,i,j)
    # filter to entries in support72-ish (quark region)
    rel = {k:v for k,v in f.items() if k[0] in range(2,8) and k[1] in range(10,16)}
    print(f"(M0,M0°) at ({i},{j}): {len(f)} terms, quark-region: {rel}")
