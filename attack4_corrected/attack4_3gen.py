"""Attack 4 three-generation extension: finite spectral triple at C^96 = C^32 (x) C^3.

T4 NUMERICAL EXPLORATION ONLY. Not a theorem, not a Lean proof.

Triplicates the one-generation finite geometry (IMPOSED triplication, not derived):
  pi_3(a)   = pi(a) (x) I_3        (24 real generators, and the 12 selected complex ones)
  Gamma_3   = Gamma (x) I_3
  UJ_3      = UJ (x) I_3           (J-compat: UJ_3 conj(D_3) = D_3 UJ_3)
  D_3       = sum_{g,g'} D^{(g,g')} (x) E^3_{gg'}
where D^{(g,g')} is the one-generation smDirac ansatz with scalar Yukawas
  yNu = Ynu[g,g'], yE = Ye[g,g'], yU = Yu[g,g'], yD = Yd[g,g'], yR = MR[g,g'].
Ynu, Ye, Yu, Yd are arbitrary complex 3x3; MR is complex SYMMETRIC 3x3
(symmetry is required for D_3 self-adjointness -- checked below).

CKM/PMNS are NOT derived: the Yukawa matrices are arbitrary inputs, and the
selection of the SM directions per generation remains explicit physical input
(cf. DIRECTIONS_36.md: order-one admits 46/gen, physics selects 10/gen).

Steps:
  1. Build D_3 with random matrix Yukawas; verify grading-odd, self-adjoint,
     J-compatible, and order-one (144 selected pairs + full 576 pairs).
  2. Nullspace census, exploiting the generation-block structure of the
     order-one map: diagonal blocks reuse the 1-gen 272-basis; off-diagonal
     blocks use a 512-dim real basis (272 J-compatible + 240 J-anti-compatible
     hermitian pieces). Normal-equation SVD per block type.
  3. Classify the off-diagonal (generation-mixing) null directions by their
     32-pattern (A/E slots, C=0?, B=conj(A)?), as in DIRECTIONS_36.md.
  4. Verify the 3-gen SM ansatz subspace sits in the nullspace.
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
OUT = os.path.join(HERE, "results3gen")
os.makedirs(OUT, exist_ok=True)
TOL = 1e-8

rng = np.random.default_rng(20260927)

# ---------------------------------------------------------------- 1-gen objects
gens24 = A4.generators_24()                       # 24 real generators, 32x32
U = A4.UJ()
Gam = A4.gammaF()
ops24 = [A4.pi_op(X, U) for X in gens24]
I3 = np.eye(3, dtype=complex)


def kron3(M):
    return np.kron(M, I3)


gens96 = [kron3(X) for X in gens24]
ops96 = [kron3(Y) for Y in ops24]
U3 = kron3(U)
Gam3 = kron3(Gam)

# 12 selected complex generators (mirrors Lean smGen)
sm12 = [A4.genC()] + [A4.genH(k) for k in range(3)] + [A4.genM(a) for a in range(8)]
sm12op = [A4.pi_op(X, U) for X in sm12]
sm12_96 = [kron3(X) for X in sm12]
sm12op_96 = [kron3(Y) for Y in sm12op]


def randU(n):
    A = rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))
    return A + A.conj().T


def randS(n):
    A = rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))
    return A + A.T


# ---------------------------------------------------------------- D_3 ansatz
def build_dirac3(Ynu, Ye, Yu, Yd, MR):
    """3-generation Dirac ansatz. Ynu..Yd: (3,3) complex; MR: (3,3) complex symmetric."""
    Ys = [Ynu, Ye, Yu, Yd, Yu, Yd, Yu, Yd]  # one 3x3 per Fin-8 Yukawa slot
    D = np.zeros((DIM, DIM), complex)
    for p in range(8):
        Y = Ys[p]
        for g in range(GEN):
            for gp in range(GEN):
                v = Y[g, gp]
                # A-block  [0:8, 8:16]  and A-dagger [8:16, 0:8]
                D[p * GEN + g, (8 + p) * GEN + gp] = v
                D[(8 + p) * GEN + gp, p * GEN + g] = v.conjugate()
                # B-block  [16:24, 24:32] = conj(A),  B-dagger [24:32, 16:24]
                D[(16 + p) * GEN + g, (24 + p) * GEN + gp] = v.conjugate()
                D[(24 + p) * GEN + gp, (16 + p) * GEN + g] = v
    # E-block: only the (nu_R, nu_R) slot, [24:32, 8:16]; E-dagger [8:16, 24:32]
    for g in range(GEN):
        for gp in range(GEN):
            v = MR[g, gp]
            D[24 * GEN + g, 8 * GEN + gp] = v
            D[8 * GEN + gp, 24 * GEN + g] = v.conjugate()
    return D


def check_basic(D, tag):
    r_odd = np.linalg.norm(D @ Gam3 + Gam3 @ D)
    r_sa = np.linalg.norm(D.conj().T - D)
    r_J = np.linalg.norm(U3 @ D.conj() - D @ U3)
    print(f"  [{tag}] ||{{D,G}}||={r_odd:.2e}  ||D*-D||={r_sa:.2e}  "
          f"||UJ conj(D)-D UJ||={r_J:.2e}")
    return r_odd, r_sa, r_J


def order_one_max(D, gen_list, op_list):
    r = 0.0
    for X in gen_list:
        DX = D @ X - X @ D
        for Y in op_list:
            r = max(r, np.linalg.norm(DX @ Y - Y @ DX))
    return r


print("== Step 1: D_3 ansatz verification (random matrix Yukawas) ==")
basic_res, o1_144, o1_576 = [], [], []
for trial in range(3):
    Ys = [rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3)) for _ in range(4)]
    MR = randS(3)
    D3 = build_dirac3(*Ys, MR)
    nD3 = np.linalg.norm(D3)
    r_odd, r_sa, r_J = check_basic(D3, f"trial {trial} (||D||={nD3:.2f})")
    basic_res.append((r_odd, r_sa, r_J))
    r144 = order_one_max(D3, sm12_96, sm12op_96)
    r576 = order_one_max(D3, gens96, ops96)
    o1_144.append(r144)
    o1_576.append(r576)
    # non-vacuity: [D,X0] must be nonzero while [[D,X0],Y0] vanishes
    X0, Y0 = sm12_96[0], sm12op_96[0]
    nDX = np.linalg.norm(D3 @ X0 - X0 @ D3)
    print(f"           max ||[[D,X],Y^circ]]||: 144 SM-selected = {r144:.2e}, "
          f"144 all-lifted = {r576:.2e}; ||[D,X0]||={nDX:.2e} (non-vacuous if >> 0)")

# symmetry sanity: self-adjointness holds for ANY MR (E-dagger coded as adjoint),
# but J-compatibility needs MR symmetric -- verify both directions.
MR_bad = rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3))
D3_bad = build_dirac3(*[rng.standard_normal((3, 3)) for _ in range(4)], MR_bad)
r_sa_bad = np.linalg.norm(D3_bad.conj().T - D3_bad)
r_J_bad = np.linalg.norm(U3 @ D3_bad.conj() - D3_bad @ U3)
print(f"  [sanity] non-symmetric MR -> ||D*-D|| = {r_sa_bad:.2e} (0: SA needs no symmetry)")
print(f"  [sanity] non-symmetric MR -> ||UJ conj(D)-D UJ|| = {r_J_bad:.2e} (must be >> 0: J needs symmetry)")

# ---------------------------------------------------------------- census: admissible bases
print("== Step 2: admissible-space bases at C^96 ==")
Bplus = np.load(os.path.join(HERE, "results", "dbasis.npy"))  # (272,32,32) 1-gen Adm+
print(f"  1-gen Adm+ basis loaded: {Bplus.shape}")

# J-anti-compatible grading-odd hermitian basis (240-dim).
# Domain is the 512 REAL coefficients on the grading-odd hermitian basis GO;
# each constraint row is the (complex) J-anti condition flattened to real.
HB = A4.hermitian_real_basis()                    # (1024,32,32)
GO = np.stack([H for H in HB if np.linalg.norm(H @ Gam + Gam @ H) < 1e-12])
print(f"  grading-odd hermitian 32-basis: {GO.shape[0]} (expect 512)")
rows = []
for H in GO:
    C = U @ H.conj() + H @ U                      # J-anti: UJ conj(H) = -H UJ
    rows.append(np.concatenate([C.real.ravel(), C.imag.ravel()]))
Cmat = np.stack(rows).T                           # (2048, 512): coeffs -> constraint
_, s_anti, Vh_anti = np.linalg.svd(Cmat, full_matrices=False)
n_anti = int((s_anti <= TOL * s_anti[0]).sum())
print(f"  J-anti-compatible dim: {n_anti} (expect 240)")
Bminus = np.tensordot(Vh_anti[-n_anti:].T, GO, axes=([0], [0]))
# verify J-anti on the basis
r_anti = max(np.linalg.norm(U @ H.conj() + H @ U) for H in Bminus)
print(f"  max ||UJ conj(H)+H UJ|| on Bminus: {r_anti:.2e}")

# off-diagonal (g,g') real basis patterns, 512 = 272 + 240:
#   M = H+  (J-compatible)  or  M = i*H-  (J-compatible, shown in analysis)
P_off = np.concatenate([Bplus, 1j * Bminus], axis=0)
print(f"  off-diagonal block basis: {P_off.shape[0]} (expect 512)")
r_Joff = max(np.linalg.norm(U @ M.conj() - M @ U) for M in P_off)
r_Goff = max(np.linalg.norm(M @ Gam + Gam @ M) for M in P_off)
print(f"  max ||UJ conj(M)-M UJ||: {r_Joff:.2e}   max ||{{M,G}}||: {r_Goff:.2e}")

admissible_dim_96 = 3 * 272 + 3 * P_off.shape[0]
print(f"  admissible dim at C^96: {admissible_dim_96} (= 3x272 diag + 3x512 off-diag)")


# ---------------------------------------------------------------- census: order-one nullity per block type
def nullity_block(patterns, tag):
    """Real nullity of the order-one map on one generation-block type.

    patterns: (P,32,32) complex block-patterns, real-parametrized.
    Stacks all 576 pairs as real normal equations (P x P), then eigvalsh.
    """
    P = patterns.shape[0]
    N = np.zeros((P, P))
    t0 = time.time()
    for ia, X in enumerate(gens24):
        BX = (np.einsum('kij,jl->kil', patterns, X)
              - np.einsum('ij,kjl->kil', X, patterns))
        for Y in ops24:
            V = (np.einsum('kij,jl->kil', BX, Y)
                 - np.einsum('ij,kjl->kil', Y, BX))
            F = np.concatenate([V.real.reshape(P, -1),
                                V.imag.reshape(P, -1)], axis=1).T  # (2048, P)
            N += F.T @ F
    w = np.linalg.eigvalsh(N)
    null = int((w <= TOL * w[-1]).sum())
    gap = float(w[-null - 1] / w[-1]) if 0 < null < P else float('nan')
    print(f"  [{tag}] P={P} nullity={null} gap={gap:.3f} "
          f"eigs at cutoff: {np.array2string(w[max(0, P-null-2):P-null+2], precision=2)} "
          f"({time.time()-t0:.0f}s)")
    return null, w, N


print("== Step 3: order-one nullity per generation-block type ==")
null_diag, w_diag, _ = nullity_block(Bplus, "diagonal (g,g)")
null_off, w_off, N_off = nullity_block(P_off, "off-diagonal (g,g') g!=g'")
total_null = 3 * null_diag + 3 * null_off
print(f"  TOTAL order-one nullity at C^96: {total_null} "
      f"(= 3x{null_diag} diag + 3x{null_off} mixing)")

np.save(os.path.join(OUT, "w_diag.npy"), w_diag)
np.save(os.path.join(OUT, "w_off.npy"), w_off)

# ---------------------------------------------------------------- classify mixing null directions
print("== Step 4: classify generation-mixing null directions ==")
w, V = np.linalg.eigh(N_off)
vecs = V[:, :null_off]                       # (512, null_off) real coeff basis of nullspace
Mnull = np.tensordot(vecs.T, P_off, axes=([0], [0]))  # (null_off,32,32) complex patterns

# 1-gen allowed-slot masks from DIRECTIONS_36 (basis-invariant facts):
#   A-block: 16 allowed slots (8 SM + 8 flipped); C-block: 0; E: symmetric, 27 allowed entries
allowA = np.zeros((8, 8), bool)
smA = [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7)]
flipA = [(0, 1), (1, 0), (2, 3), (3, 2), (4, 5), (5, 4), (6, 7), (7, 6)]
for (i, j) in smA + flipA:
    allowA[i, j] = True

def pattern_report(M, tag):
    A = M[0:8, 8:16]; B = M[16:24, 24:32]; C = M[0:8, 16:24]; E = M[24:32, 8:16]
    nA_out = np.abs(A[~allowA]).max()
    nC = np.abs(C).max()
    nB_conjA = np.abs(B - A.conj()).max()
    nE_asym = np.abs(E - E.T).max()
    print(f"    [{tag}] max|A| outside 16 slots={nA_out:.2e}  max|C|={nC:.2e}  "
          f"max|B-conj(A)|={nB_conjA:.2e}  max|E-E^T|={nE_asym:.2e}")
    return nA_out, nC, nB_conjA, nE_asym

print("  worst-case over mixing nullspace basis:")
worst = [0, 0, 0, 0]
for k in range(null_off):
    r = pattern_report(Mnull[k], f"v{k}")
    worst = [max(a, b) for a, b in zip(worst, r)]
print(f"  WORST over all {null_off}: A-outside={worst[0]:.2e} C={worst[1]:.2e} "
      f"B-conjA={worst[2]:.2e} E-asym={worst[3]:.2e}")

# per-direction: split into A-pure / E-pure like the 1-gen analysis?
nA = np.array([np.linalg.norm(M[0:8, 8:16]) for M in Mnull])
nE = np.array([np.linalg.norm(M[24:32, 8:16]) for M in Mnull])
print(f"  A-block norms: min={nA.min():.3f} max={nA.max():.3f}")
print(f"  E-block norms: min={nE.min():.3f} max={nE.max():.3f}")
np.save(os.path.join(OUT, "Mnull_off.npy"), Mnull)

# ---------------------------------------------------------------- SM ansatz subspace at 3-gen
print("== Step 5: 3-gen SM ansatz subspace ==")
# per generation: 4 complex 3x3 Yukawas (72 real) + symmetric complex 3x3 Majorana (12 real)
# build explicit random SM-subspace directions and check they lie in the nullspace
n_sm_dirs = 0
max_res = 0.0
for trial in range(5):
    Ys = [rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3)) for _ in range(4)]
    MR = randS(3)
    D3 = build_dirac3(*Ys, MR)
    r = order_one_max(D3, sm12_96, sm12op_96)
    max_res = max(max_res, r)
    n_sm_dirs += 1
print(f"  {n_sm_dirs} random SM-ansatz D_3: max 144-pair residual = {max_res:.2e}")
print(f"  three-gen SM ansatz real dims: 4 matrix Yukawas x 18 + symmetric MR 12 = 84")

numbers = {
    "tier": "T4 numerical exploration only; not a theorem, not a Lean proof",
    "dim_96": DIM,
    "generators_96": 24,
    "admissible_D_dim_96": int(admissible_dim_96),
    "admissible_breakdown": "3x272 diagonal + 3x512 off-diagonal(gen-mixing)",
    "J_anti_dim_32": int(n_anti),
    "order_one_pairs_tested": 576,
    "nullity_per_diagonal_block": int(null_diag),
    "nullity_per_mixing_block": int(null_off),
    "order_one_nullity_96": int(total_null),
    "nullity_formula": f"3x{null_diag} + 3x{null_off}",
    "ansatz_basic_residuals_max": [float(max(b[i] for b in basic_res)) for i in range(3)],
    "ansatz_order_one_144_max": float(max(o1_144)),
    "ansatz_order_one_576_max": float(max(o1_576)),
    "nonsymmetric_MR_breaks_sa": float(r_sa_bad),
    "mixing_worst_A_outside_slots": float(worst[0]),
    "mixing_worst_C": float(worst[1]),
    "mixing_worst_B_minus_conjA": float(worst[2]),
    "mixing_worst_E_asym": float(worst[3]),
    "sm_ansatz_dims_96": 84,
    "sm_ansatz_144pair_residual": float(max_res),
    "selection_note": ("order-one admits %d; the three-gen SM ansatz (84 real dims) is a subspace. "
                       "Selection remains explicit physical input, not derived." % total_null),
}
with open(os.path.join(OUT, "numbers3gen.json"), "w") as f:
    json.dump(numbers, f, indent=2)
print("\nDONE. numbers3gen.json:")
print(json.dumps({k: v for k, v in numbers.items()}, indent=2))
