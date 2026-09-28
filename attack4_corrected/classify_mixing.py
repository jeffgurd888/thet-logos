"""Step 4 (fixed): classify the 88 generation-mixing null directions per pair.

T4 NUMERICAL EXPLORATION ONLY. Not a theorem, not a Lean proof.

Fixes the tensordot shape bug in attack4_3gen.py Step 4:
    Mnull = np.tensordot(vecs.T, P_off, axes=([0],[0]))   # WRONG: (88,512)x(512,32,32) contracts 88 vs 512
    Mnull = np.tensordot(vecs, P_off, axes=([0],[0]))    # RIGHT: (512,88)x(512,32,32) -> (88,32,32)

Classifies the mixing nullspace the way DIRECTIONS_36.md did the 1-gen case:
block support, A/Ad/E/Ed slot census, SM-like subspace, selection counts.
"""
import json
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import attack4_corrected as A4

D32, GEN, DIM = 32, 3, 96
RES = os.path.join(HERE, "results")
OUT = os.path.join(HERE, "results3gen")
TOL = 1e-8
os.makedirs(OUT, exist_ok=True)

rng = np.random.default_rng(7)

# ---------------------------------------------------------------- setup (mirrors attack4_3gen.py)
gens24 = A4.generators_24()
U = A4.UJ()
Gam = A4.gammaF()
ops24 = [A4.pi_op(X, U) for X in gens24]
Bplus = np.load(os.path.join(RES, "dbasis.npy"))          # (272,32,32)
HB = A4.hermitian_real_basis()                            # (1024,32,32)
GO = np.stack([H for H in HB if np.linalg.norm(H @ Gam + Gam @ H) < 1e-12])
rows = []
for H in GO:
    C = U @ H.conj() + H @ U
    rows.append(np.concatenate([C.real.ravel(), C.imag.ravel()]))
Cmat = np.stack(rows).T
_, s_anti, Vh_anti = np.linalg.svd(Cmat, full_matrices=False)
n_anti = int((s_anti <= TOL * s_anti[0]).sum())
Bminus = np.tensordot(Vh_anti[-n_anti:].T, GO, axes=([0], [0]))
P_off = np.concatenate([Bplus, 1j * Bminus], axis=0)       # (512,32,32)
P = P_off.shape[0]
print(f"setup: P_off {P_off.shape}, n_anti={n_anti}", flush=True)

# real-orthonormality of P_off
G = np.stack([np.concatenate([M.real.ravel(), M.imag.ravel()]) for M in P_off])
gg = G @ G.T
print(f"  P_off real-orthonormality: max|G-I| = {np.abs(gg - np.eye(P)).max():.2e}", flush=True)


def build_dirac3(Ynu, Ye, Yu, Yd, MR):
    Ys = [Ynu, Ye, Yu, Yd, Yu, Yd, Yu, Yd]
    D = np.zeros((DIM, DIM), complex)
    for p in range(8):
        Y = Ys[p]
        for g in range(GEN):
            for gp in range(GEN):
                v = Y[g, gp]
                D[p * GEN + g, (8 + p) * GEN + gp] = v
                D[(8 + p) * GEN + gp, p * GEN + g] = v.conjugate()
                D[(16 + p) * GEN + g, (24 + p) * GEN + gp] = v.conjugate()
                D[(24 + p) * GEN + gp, (16 + p) * GEN + g] = v
    for g in range(GEN):
        for gp in range(GEN):
            v = MR[g, gp]
            D[24 * GEN + g, 8 * GEN + gp] = v
            D[8 * GEN + gp, 24 * GEN + g] = v.conjugate()
    return D


def block_of(D3, g, gp):
    return D3.reshape(32, 3, 32, 3)[:, g, :, gp]


# ---------------------------------------------------------------- N_off (cached, resumable)
Npath = os.path.join(OUT, "N_off.npy")
Ppath = os.path.join(OUT, "N_off_partial.npy")
if os.path.exists(Npath):
    print("loading cached N_off", flush=True)
    N_off = np.load(Npath)
else:
    start_ia = 0
    if os.path.exists(Ppath):
        part = np.load(Ppath, allow_pickle=True).item()
        N_off = part["N"]
        start_ia = part["next_ia"]
        print(f"resuming N_off from generator {start_ia + 1}/24", flush=True)
    else:
        print("computing N_off (takes a few minutes)...", flush=True)
        N_off = np.zeros((P, P))
    t0 = time.time()
    for ia in range(start_ia, len(gens24)):
        X = gens24[ia]
        BX = (np.einsum('kij,jl->kil', P_off, X)
              - np.einsum('ij,kjl->kil', X, P_off))
        for Y in ops24:
            V = (np.einsum('kij,jl->kil', BX, Y)
                 - np.einsum('ij,kjl->kil', Y, BX))
            F = np.concatenate([V.real.reshape(P, -1),
                                V.imag.reshape(P, -1)], axis=1).T
            N_off += F.T @ F
        np.save(Ppath, {"N": N_off, "next_ia": ia + 1})
        print(f"  gen {ia + 1}/24 ({time.time() - t0:.0f}s)", flush=True)
    np.save(Npath, N_off)
    if os.path.exists(Ppath):
        os.remove(Ppath)

w, V = np.linalg.eigh(N_off)
null_off = int((w <= TOL * w[-1]).sum())
gap = float(w[-null_off - 1] / w[-1]) if 0 < null_off < P else float('nan')
print(f"nullity per mixing pair: {null_off} (expect 88), gap={gap:.3f}", flush=True)
assert null_off == 88, "nullity changed!"

vecs = V[:, :null_off]                                    # (512, 88)
Mnull = np.tensordot(vecs, P_off, axes=([0], [0]))         # FIXED -> (88,32,32)
print(f"Mnull shape: {Mnull.shape} (expect (88,32,32))", flush=True)
np.save(os.path.join(OUT, "Mnull_off.npy"), Mnull)

# Mnull real-orthonormality
Gm = np.stack([np.concatenate([M.real.ravel(), M.imag.ravel()]) for M in Mnull])
print(f"Mnull real-orthonormality: max|G-I| = {np.abs(Gm @ Gm.T - np.eye(null_off)).max():.2e}", flush=True)

# ---------------------------------------------------------------- 1. direct order-one verification
print("== 1. direct order-one verification ==", flush=True)
maxr = 0.0
for X in gens24:
    DX = Mnull @ X - X @ Mnull
    for Y in ops24:
        DD = DX @ Y - Y @ DX
        maxr = max(maxr, np.abs(DD).max())
print(f"max ||[[M,X],Y^circ]]|| over 88 x 576 pairs: {maxr:.2e}", flush=True)

# ---------------------------------------------------------------- 2. block structure
print("== 2. block structure ==", flush=True)


def blocks(M):
    return (M[0:8, 8:16], M[8:16, 0:8],      # A, Ad
            M[16:24, 24:32], M[24:32, 16:24],  # B, Bd
            M[0:8, 16:24], M[16:24, 0:8],    # C, Cd
            M[24:32, 8:16], M[8:16, 24:32])  # E, Ed


r_odd = max(np.linalg.norm(M @ Gam + Gam @ M) for M in Mnull)
r_J = max(np.linalg.norm(U @ M.conj() - M @ U) for M in Mnull)
print(f"max ||{{M,Gamma}}|| = {r_odd:.2e}   max ||UJ conj(M)-M UJ|| = {r_J:.2e}", flush=True)

nC = max(np.linalg.norm(b[4]) for b in (blocks(M) for M in Mnull))
nCd = max(np.linalg.norm(b[5]) for b in (blocks(M) for M in Mnull))
print(f"max ||C|| = {nC:.2e}   max ||Cd|| = {nCd:.2e} (expect 0: order-one forces C=0)", flush=True)

# ---------------------------------------------------------------- 3. A/Ad slot census
print("== 3. A/Ad slot census ==", flush=True)
supA = np.zeros((8, 8))
supAd = np.zeros((8, 8))
for M in Mnull:
    A, Ad, *_ = blocks(M)
    supA = np.maximum(supA, np.abs(A))
    supAd = np.maximum(supAd, np.abs(Ad))
print("A-block max-entry census (rows=doublet, cols=singlet):")
for p in range(8):
    print("  I%da%d: " % (p // 2, p % 2) + " ".join(f"{supA[p, q]:.2f}" for q in range(8)))
print("Ad-block max-entry census:")
for p in range(8):
    print("  I%da%d: " % (p // 2, p % 2) + " ".join(f"{supAd[p, q]:.2f}" for q in range(8)))
nzA = [(p, q) for p in range(8) for q in range(8) if supA[p, q] > 1e-6]
nzAd = [(p, q) for p in range(8) for q in range(8) if supAd[p, q] > 1e-6]
print(f"nonzero A slots: {len(nzA)} (expect 16); nonzero Ad slots: {len(nzAd)} (expect 16)", flush=True)

# color universality on the A-sector across the whole nullspace
cu = max(max(np.abs(M[2, 8 + 2] - M[4, 8 + 4]),
             np.abs(M[2, 8 + 2] - M[6, 8 + 6])) for M in Mnull)
print(f"max |A[2,2]-A[4,4]|, |A[2,2]-A[6,6]| over nullspace: {cu:.2e} (color locking)", flush=True)

# ---------------------------------------------------------------- 4. E/Ed census, symmetry dropped?
print("== 4. E/Ed census ==", flush=True)
supE = np.zeros((8, 8))
supEd = np.zeros((8, 8))
for M in Mnull:
    *_, E, Ed = blocks(M)
    supE = np.maximum(supE, np.abs(E))
    supEd = np.maximum(supEd, np.abs(Ed))
print("E-block max-entry census:")
for p in range(8):
    print("  s%d: " % p + " ".join(f"{supE[p, q]:.2f}" for q in range(8)))
nzE = [(p, q) for p in range(8) for q in range(8) if supE[p, q] > 1e-6]
nzEd = [(p, q) for p in range(8) for q in range(8) if supEd[p, q] > 1e-6]
print(f"nonzero E entries: {len(nzE)} (expect 28); nonzero Ed entries: {len(nzEd)} (expect 28)", flush=True)
asym = max(np.linalg.norm(b[6] - b[6].T) for b in (blocks(M) for M in Mnull))
print(f"max ||E - E^T|| over nullspace: {asym:.2e} (>>0 => symmetry dropped)", flush=True)

# ---------------------------------------------------------------- 5. Yukawa vs Majorana sector decoupling + dims
print("== 5. sector decoupling ==", flush=True)


def rstack_sector(Ms, idx):
    return np.stack([np.concatenate([blocks(M)[i].real.ravel(),
                                     blocks(M)[i].imag.ravel()]) for i in idx for M in Ms])


XA = rstack_sector(Mnull, [0, 1])      # (176, 512): A, Ad
XE = rstack_sector(Mnull, [6, 7])      # (176, 1024): E, Ed
XB = rstack_sector(Mnull, [2, 3])      # B, Bd


def drank(X, tag):
    s = np.linalg.svd(X, compute_uv=False)
    r = int((s > 1e-8 * s[0]).sum())
    print(f"  rank({tag}) = {r}", flush=True)
    return r


rA = drank(XA, "A-sector(A,Ad)")
rE = drank(XE, "E-sector(E,Ed)")
rB = drank(XB, "B-sector(B,Bd)")
print(f"  rA + rE = {rA + rE} (expect 88 = decoupling)", flush=True)

# B-sector determination: least squares B,Bd as real-linear fn of (A,Ad)
YA = np.stack([np.concatenate([blocks(M)[0].real.ravel(), blocks(M)[0].imag.ravel(),
                               blocks(M)[1].real.ravel(), blocks(M)[1].imag.ravel()]) for M in Mnull])  # (88,2048)
YB = np.stack([np.concatenate([blocks(M)[2].real.ravel(), blocks(M)[2].imag.ravel(),
                               blocks(M)[3].real.ravel(), blocks(M)[3].imag.ravel()]) for M in Mnull])  # (88,2048)
coef, res, *_ = np.linalg.lstsq(YA, YB, rcond=None)
YB_fit = YA @ coef
rel = np.linalg.norm(YB - YB_fit) / np.linalg.norm(YB)
print(f"  B,Bd as real-linear fn of (A,Ad): rel residual = {rel:.2e} (0 => determined)", flush=True)
# candidate simple relations
c1 = max(np.linalg.norm(blocks(M)[2] - blocks(M)[0].conj()) for M in Mnull)
c2 = max(np.linalg.norm(blocks(M)[3] - blocks(M)[1].conj()) for M in Mnull)
print(f"  max||B - conj(A)|| = {c1:.2e};  max||Bd - conj(Ad)|| = {c2:.2e}", flush=True)

# ---------------------------------------------------------------- 6. SM-like mixing subspace (explicit, via build_dirac3)
print("== 6. SM-like mixing subspace ==", flush=True)
E01 = np.zeros((3, 3), complex); E01[0, 1] = 1.0
E10 = E01.T
Z3 = np.zeros((3, 3), complex)
cplx_pats = []
for mats in [(E01, Z3, Z3, Z3), (E10, Z3, Z3, Z3),
             (Z3, E01, Z3, Z3), (Z3, E10, Z3, Z3),
             (Z3, Z3, E01, Z3), (Z3, Z3, E10, Z3),
             (Z3, Z3, Z3, E01), (Z3, Z3, Z3, E10)]:
    D3 = build_dirac3(*mats, Z3)
    cplx_pats.append(block_of(D3, 0, 1))
D3 = build_dirac3(Z3, Z3, Z3, Z3, E01 + E10)
cplx_pats.append(block_of(D3, 0, 1))
print(f"  {len(cplx_pats)} complex SM-like mixing patterns (expect 9)", flush=True)
SMmix = []
for Mc in cplx_pats:
    SMmix.append(Mc.real)
    SMmix.append(Mc.imag)
SMmix = np.stack(SMmix)  # (18,32,32)
# null check
maxr_sm = 0.0
for X in gens24:
    DX = SMmix @ X - X @ SMmix
    for Y in ops24:
        maxr_sm = max(maxr_sm, np.abs(DX @ Y - Y @ DX).max())
print(f"  max ||[[S,X],Y^circ]]|| over 18 x 576: {maxr_sm:.2e}", flush=True)
# independence
s_sm = np.linalg.svd(np.stack([np.concatenate([M.real.ravel(), M.imag.ravel()]) for M in SMmix]),
                     compute_uv=False)
r_sm = int((s_sm > 1e-8 * s_sm[0]).sum())
print(f"  rank(SM-like mixing) = {r_sm} (expect 18)", flush=True)
# in-span check: projection onto Mnull
SMr = np.stack([np.concatenate([M.real.ravel(), M.imag.ravel()]) for M in SMmix])
proj = SMr @ Gm.T @ Gm
res_inspan = np.linalg.norm(SMr - proj) / np.linalg.norm(SMr)
print(f"  SM-like in span(Mnull): rel projection residual = {res_inspan:.2e}", flush=True)
# color universality of explicit SM mixing
D3u = build_dirac3(Z3, Z3, E01, Z3, Z3)
Mu = block_of(D3u, 0, 1)
print(f"  Yu color check: A[2,2]={Mu[2,10]:.3f} A[4,4]={Mu[4,12]:.3f} A[6,6]={Mu[6,14]:.3f}", flush=True)

# ---------------------------------------------------------------- 7. support-based decomposition + selection counts
print("== 7. support decomposition ==", flush=True)
SM_SLOTS = [(p, p) for p in range(8)]
FLIP_SLOTS = [(0, 1), (1, 0), (2, 3), (3, 2), (4, 5), (5, 4), (6, 7), (7, 6)]
E_SM = [(0, 0)]
E_EX = [(p, q) for p in range(8) for q in range(8)
        if supE[p, q] > 1e-6 and (p, q) != (0, 0)]


def support_rank(slots_A, slots_E, tag):
    rows = []
    for M in Mnull:
        A, Ad, _, _, _, _, E, Ed = blocks(M)
        v = []
        for (p, q) in slots_A:
            v += [A[p, q].real, A[p, q].imag, Ad[p, q].real, Ad[p, q].imag]
        for (p, q) in slots_E:
            v += [E[p, q].real, E[p, q].imag, Ed[p, q].real, Ed[p, q].imag]
        rows.append(v)
    X = np.stack(rows)
    s = np.linalg.svd(X, compute_uv=False)
    r = int((s > 1e-8 * s[0]).sum())
    print(f"  rank({tag}) = {r}", flush=True)
    return r


r_smA = support_rank(SM_SLOTS, [], "SM-A support")
r_flipA = support_rank(FLIP_SLOTS, [], "flipped-A support")
r_eSM = support_rank([], E_SM, "E-SM (nuR,nuR)")
r_eEx = support_rank([], E_EX, "E-exotic support")
print(f"  E-exotic entries: {len(E_EX)} (expect 27)", flush=True)
print(f"  sum = {r_smA + r_flipA + r_eSM + r_eEx} (expect 88)", flush=True)

# ---------------------------------------------------------------- 8. 96x96 physical direction check
print("== 8. physical 96x96 direction ==", flush=True)
M0 = Mnull[0]
D96 = np.zeros((96, 96), complex)
B0 = M0.reshape(32, 1, 32, 1)
D96r = D96.reshape(32, 3, 32, 3)
D96r[:, 0, :, 1] = M0
D96r[:, 1, :, 0] = M0.conj().T
r_sa96 = np.linalg.norm(D96.conj().T - D96)
U3 = np.kron(U, np.eye(3))
G3 = np.kron(Gam, np.eye(3))
r_J96 = np.linalg.norm(U3 @ D96.conj() - D96 @ U3)
r_od96 = np.linalg.norm(D96 @ G3 + G3 @ D96)
print(f"  pair-direction: ||D96*-D96||={r_sa96:.2e} ||UJ3 conj-UJ3||={r_J96:.2e} ||{{D96,G3}}||={r_od96:.2e}", flush=True)

# ---------------------------------------------------------------- numbers
numbers = {
    "tier": "T4 numerical exploration only; not a theorem, not a Lean proof",
    "bugfix": "tensordot axes ([0],[0]) on (vecs, P_off); was vecs.T",
    "nullity_per_mixing_pair": int(null_off),
    "nullity_gap": gap,
    "direct_orderone_max_residual_88x576": float(maxr),
    "max_grading_odd_residual": float(r_odd),
    "max_Jcompat_residual": float(r_J),
    "max_C_block": float(nC),
    "n_nonzero_A_slots": len(nzA),
    "n_nonzero_Ad_slots": len(nzAd),
    "A_color_universality_maxdev": float(cu),
    "n_nonzero_E_entries": len(nzE),
    "n_nonzero_Ed_entries": len(nzEd),
    "max_E_asymmetry": float(asym),
    "rank_A_sector": int(rA),
    "rank_E_sector": int(rE),
    "rank_B_sector": int(rB),
    "B_determined_by_AAd_relres": float(rel),
    "max_B_minus_conjA": float(c1),
    "max_Bd_minus_conjAd": float(c2),
    "sm_like_mixing_rank": int(r_sm),
    "sm_like_orderone_max": float(maxr_sm),
    "sm_like_in_span_relres": float(res_inspan),
    "rank_SM_A_support": int(r_smA),
    "rank_flip_A_support": int(r_flipA),
    "rank_E_SM_support": int(r_eSM),
    "rank_E_exotic_support": int(r_eEx),
    "n_E_exotic_entries": len(E_EX),
    "physical_96_SA": float(r_sa96),
    "physical_96_J": float(r_J96),
    "physical_96_odd": float(r_od96),
}
with open(os.path.join(OUT, "numbers_mixing.json"), "w") as f:
    json.dump(numbers, f, indent=2)
print("\nDONE. numbers_mixing.json written.", flush=True)
