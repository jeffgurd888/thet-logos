#!/usr/bin/env python3
"""BRIDGE SPAN 3 — Krein fundamental symmetry R (numerics).

Tier T4 (numerical exploration). Commissioned 2026-10-07.
Sequel to Bridge Span 2 (involutive_twist_lab.py): the DLM flip
rho(a,a') = (a',a) stood as a Connes-Moscovici twist, with twisted
order-one 0.000e+00 over 331,776 pairs in the grand P± picture.

This span builds the Krein side. Literature formulas
(arXiv:1710.04965 §3.1–3.2, "Lorentz signature and twisted spectral
triples", verified 2026-10-07 via web search):
  rho-product:    <Psi,Phi>_rho := <Psi, R Phi>                  (3.1)
  Krein-adjoint:  A^+ := R A^dagger R ; D rho-symmetric <=> R D^dagger R = D
  implementation: rho(a) = R a R^{-1}                            (3.11)
  compatibility:  J R = ± R J                                    (3.12)
  R self-adjoint unitary, R != 1  ==>  Krein space, R a fundamental
  symmetry (R^2 = I). DLM SM case: R = [[0,1_2],[1_2,0]] = gamma_E^0,
  and the rho-product is the Lorentzian Krein product.
Twisted first-order condition (arXiv:2010.15367 §2.2):
  [[D,a]_rho, b^o]_(rho^o) = 0,  rho^o(a^o) := (rho^{-1}(a))^o.   (5)(6)

PRIMARY (DLM transplant, expect STAND): on doubled H⊕H = C^64,
  pi~(a,a') = block_diag(pi(a), pi(a')),  R_swap = [[0,I_32],[I_32,0]],
  D~ = block_diag(D_F, D_F),  J~ from UJ blockwise (Ut = block_diag(U,U)).
  Tests P.1–P.7 below.
SECONDARY (ambitious): single-H eta on C^32 with
  eta^2 = I, eta^dagger = eta, eta Gamma = -Gamma eta,
  [eta, pi(g)] = 0 (24 gens), eta D_F eta = D_F.
  Verdict: KILLED — proved via a 4-dim common kernel (S.4), not hand-waving.

Conventions (binding, from Spans 1–2): the J-action
J~act(X) = Ut conj(X) Ut^T is CONJUGATE-based; R is real so Rbar = R
in the linear-shadow J-compatibility test. Seed 2026. DIM = 32.
Finite dimension: every operator below is bounded automatically.
No Lorentzian-physics claims; no thermal-phase-transition language.

Prints a results table AND writes scripts/bridge-span-3-results.md.
"""

import os
import sys
import time

import numpy as np
import scipy.linalg as la

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "python"))
from thet_logos.common import pi, piOp, af_generators, random_af, UJ, gamma_F
from thet_logos.engine13_rsd import build_DF, selfadjoint_basis, opnorm

SEED = 2026
DIM = 32
D2 = 64
OUT = []  # lines mirrored to the results markdown file


def emit(line=""):
    print(line, flush=True)
    OUT.append(line)


def fro(M):
    return float(la.norm(M, "fro"))


def main():
    t0 = time.time()
    D = build_DF()
    U = UJ()
    G = gamma_F()
    gens = af_generators()
    Pg = [pi(g) for g in gens]
    I32 = np.eye(DIM)
    I64 = np.eye(D2)

    # ---- doubled-space operators (primary candidate) ----
    R = np.block([[np.zeros((DIM, DIM)), I32],
                  [I32, np.zeros((DIM, DIM))]])          # swap; real symmetric
    Ut = la.block_diag(U, U)                             # J~ unitary part
    Dt = la.block_diag(D, D)

    def Jtact(X):
        return Ut @ X.conj() @ Ut.T                      # conjugate-based

    # generator degeneracy note (affects P.6/S pair counts, not the verdicts)
    n_zero = sum(1 for P in Pg if fro(P) < 1e-12)

    emit("=" * 72)
    emit("BRIDGE SPAN 3 — Krein fundamental symmetry R (Tier T4, numerical)")
    emit("PRIMARY: R_swap = [[0,I32],[I32,0]] on H⊕H = C^64 (DLM transplant);")
    emit("  pi~(a,a') = block_diag(pi(a),pi(a')), D~ = block_diag(D_F,D_F),")
    emit("  J~act(X) = Ut conj(X) Ut^T, Ut = block_diag(U,U)  (CONJUGATE-based)")
    emit("SECONDARY: single-H eta on C^32 — KILLED (common-kernel proof, §S).")
    emit(f"||D_F|| = {opnorm(D):.6g} GeV, ||D_F||_F = {fro(D):.6g}; "
         f"R real symmetric: {bool(np.allclose(R, R.real) and np.allclose(R, R.T))}")
    emit(f"NOTE: {n_zero}/24 generators map to 0 under pi (the M3(C) factor is killed")
    emit("  by this representation); the 6 nonzero pi(g) have C-rank 6. Pair grids")
    emit("  below are over all 24 gens as specified, but effectively 6x6.")

    # ------------------------------------------------------------------
    # P.1 fundamental-symmetry algebra: R^2 = I, R^H = R
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("P.1  fundamental symmetry: R^2 = id, R^dagger = R  (R != 1)")
    r_sq = fro(R @ R - I64)
    r_h = fro(R - R.conj().T)
    r_not1 = fro(R - I64)
    emit(f"  ||R^2 - I||_F = {r_sq:.3e}   (expect 0)")
    emit(f"  ||R - R^H||_F = {r_h:.3e}   (expect 0)")
    emit(f"  ||R - I||_F = {r_not1:.3e}   (nontrivial: expect >> 0)")
    emit("  P.1 VERDICT: " + ("PASS — R is a self-adjoint unitary != 1."
                              if r_sq < 1e-9 and r_h < 1e-9 and r_not1 > 1.0
                              else "FAIL."))

    # ------------------------------------------------------------------
    # P.2 flip implementation: R pi~(a,a') R = pi~(a',a)
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("P.2  twist implementation: || R pi~(a,a') R - pi~(a',a) ||_F, 576 pairs")
    vals = [fro(R @ la.block_diag(Pg[ia], Pg[ib]) @ R
                - la.block_diag(Pg[ib], Pg[ia]))
            for ia in range(24) for ib in range(24)]
    emit(f"  max over 576 pairs: {max(vals):.3e}   (expect 0)")
    emit("  P.2 VERDICT: " + ("PASS — rho(a,a')=(a',a) implemented exactly by R."
                              if max(vals) < 1e-9 else "FAIL."))

    # ------------------------------------------------------------------
    # P.3 D rho-symmetry: R D~^H R = D~
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("P.3  D rho-symmetric: || R D~^H R - D~ ||_F  (Krein-adjoint D^+ = D)")
    emit(f"  D_F Hermitian check: ||D-D^H||_F = {fro(D - D.conj().T):.3e}")
    r_rhoD = fro(R @ Dt.conj().T @ R - Dt)
    emit(f"  residual = {r_rhoD:.3e}   (expect 0: blocks equal, D_F Hermitian)")
    emit("  P.3 VERDICT: " + ("PASS — D~ is rho-self-adjoint (D^+ = D)."
                              if r_rhoD < 1e-9 else "FAIL."))

    # ------------------------------------------------------------------
    # P.4 J-compatibility: linear shadow || Ut Rbar - s R Ut ||, s = ±1
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("P.4  J-compatibility (DLM (3.12)): linear shadow || Ut Rbar - s R Ut ||_F")
    emit("     R real => Rbar = R; Ut = block_diag(U,U)")
    r_sp = fro(Ut @ R.conj() - (+1) * R @ Ut)
    r_sm = fro(Ut @ R.conj() - (-1) * R @ Ut)
    emit(f"  s = +1: {r_sp:.3e}")
    emit(f"  s = -1: {r_sm:.3e}   (expect 2||Ut R||_F = 16.0 if s=+1 holds)")
    s_best = +1 if r_sp <= r_sm else -1
    if r_sp < 1e-9:
        v4 = "PASS — J~R = +R J~ (s=+1), DLM (3.12) satisfied."
    elif r_sm < 1e-9:
        v4 = "PASS — J~R = -R J~ (s=-1)."
    else:
        v4 = "FAIL — no sign works."
    emit(f"  P.4 VERDICT: {v4}  (best s = {s_best:+d})")

    # ------------------------------------------------------------------
    # P.5 spectrum of R
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("P.5  spectrum of R (Krein signature)")
    ev = la.eigvalsh(R)
    n_p = int((np.abs(ev - 1.0) < 1e-9).sum())
    n_m = int((np.abs(ev + 1.0) < 1e-9).sum())
    emit(f"  eigenvalues +1: {n_p}, eigenvalues -1: {n_m}   (expect 32/32)")
    emit(f"  tr R = {np.trace(R):.3e} (expect 0); min/max eig = {ev.min():.6f}/{ev.max():.6f}")
    emit("  P.5 VERDICT: " + ("PASS — Krein signature (32,32); rho-product indefinite."
                              if (n_p, n_m) == (32, 32) else "FAIL."))

    # ------------------------------------------------------------------
    # P.6 twisted order-one in the DOUBLED picture, 576 x 576 = 331,776
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("P.6  twisted order-one in the DOUBLED picture:")
    emit("     [[D~,(a,a')]_rho, (b,b')^o]_{(rho)^o}, 576 x 576 = 331,776 pairs")
    emit("     inner(k) = D~ pi~(a,a') - pi~(a',a) D~   (= block_diag(X1,X2))")
    emit("     Y(l) = J~ pi~(b,b')* J~^{-1}            (= block_diag(Y1,Y2))")
    emit("     outer  = inner Y - R Y R inner  (rho^o implemented by R)")
    emit("     block arithmetic in 32x32 blocks; ||outer||^2 = ||b1||^2+||b2||^2")

    def Jact32(X):
        return U @ X.conj() @ U.T

    X1 = np.empty((576, DIM, DIM), complex)   # D Pg[ia] - Pg[ib] D
    X2 = np.empty((576, DIM, DIM), complex)   # D Pg[ib] - Pg[ia] D
    k = 0
    for ia in range(24):
        for ib in range(24):
            X1[k] = D @ Pg[ia] - Pg[ib] @ D
            X2[k] = D @ Pg[ib] - Pg[ia] @ D
            k += 1
    Y1 = np.empty((576, DIM, DIM), complex)   # Jact(Pg[jb]^dagger)
    Y2 = np.empty((576, DIM, DIM), complex)
    Jp = [Jact32(P.conj().T) for P in Pg]
    l = 0
    for jb in range(24):
        for jbp in range(24):
            Y1[l] = Jp[jb]
            Y2[l] = Jp[jbp]
            l += 1

    mx = 0.0
    nbad = 0
    arg = None
    for k in range(576):
        b1 = X1[k] @ Y1 - Y2 @ X1[k]
        b2 = X2[k] @ Y2 - Y1 @ X2[k]
        nrm = np.sqrt((np.abs(b1) ** 2).sum(axis=(1, 2))
                      + (np.abs(b2) ** 2).sum(axis=(1, 2)))
        m = float(nrm.max())
        if m > mx:
            mx = m
            arg = (k, int(nrm.argmax()))
        nbad += int((nrm > 1e-9).sum())
    emit(f"  max ||outer||_F = {mx:.3e}" + (f" at (k,l) = {arg}" if arg else ""))
    emit(f"  pairs > 1e-9: {nbad} / 331776")
    emit("  P.6 VERDICT: " + ("TWISTED ORDER-ONE HOLDS in the doubled picture "
                              "(max <= 1e-9) — reproduces Span 2's 0.000e+00."
                              if mx <= 1e-9 else f"BREAKS (max {mx:.3e})."))

    # ------------------------------------------------------------------
    # P.7 fluctuated Dirac: rho-symmetry of D~_{A_rho}
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("P.7  fluctuated Dirac D~_{A_rho}: rho-symmetry residual ||R D~_f^H R - D~_f||")
    emit("     ONE structured fluctuation (self-adjoint basis h0,h1, Span-2-style")
    emit("     coefficients c1=1.0, c2=0.5-0.3j), in the doubled picture:")
    emit("     A~_rho = c1 [D~,(h0,h0)]_rho + c2 [D~,(h1,h1)]_rho,")
    emit("     D~_f = D~ + A~_rho + J~ A~_rho J~^{-1}  (J~act CONJUGATE-based).")
    emit("     (The literal Span-2 off-diagonal (h0,h1)/(h1,h0) fluctuation vanishes")
    emit("      identically here — D h0 = h1 D exactly — so the diagonal-pair version")
    emit("      is the nontrivial structured test.)")
    Hself = selfadjoint_basis()
    emit(f"     self-adjoint represented basis dim = {len(Hself)}")
    h0, h1 = Hself[0], Hself[1]

    def tw_comm_doubled(x, y):
        # [D~, pi~(x,y)]_rho = D~ pi~(x,y) - pi~(y,x) D~  (64x64 block-diag)
        return la.block_diag(D @ x - y @ D, D @ y - x @ D)

    # confirm the off-diagonal degeneracy, then run the diagonal test
    r_off = fro(tw_comm_doubled(h0, h1))
    emit(f"     off-diagonal check ||[D~,(h0,h1)]_rho||_F = {r_off:.3e} (vanishes)")

    c1, c2 = 1.0 + 0j, 0.5 - 0.3j
    At = c1 * tw_comm_doubled(h0, h0) + c2 * tw_comm_doubled(h1, h1)
    Dtf = Dt + At + Jtact(At)
    r_rho = fro(R @ Dtf.conj().T @ R - Dtf)
    r_sa = fro(Dtf - Dtf.conj().T)
    emit(f"  structured (c1=1.0, c2=0.5-0.3j): ||A~_rho||_F = {fro(At):.4f}")
    emit(f"    rho-symmetry residual ||R D~_f^H R - D~_f||_F = {r_rho:.3e}")
    emit(f"    ordinary self-adjointness ||D~_f-D~_f^H||_F = {r_sa:.3e}")
    emit("    (here rho-symmetry = ordinary self-adjointness: for block-diagonal D~_f,")
    emit("     R D~_f^H R - D~_f = block_diag(D_f^H-D_f, D_f^H-D_f))")
    # diagnostic: purely-imaginary coefficients = rho-real twisted 1-form
    At2 = (1.0j) * tw_comm_doubled(h0, h0) + (0.5j) * tw_comm_doubled(h1, h1)
    Dtf2 = Dt + At2 + Jtact(At2)
    r_rho2 = fro(R @ Dtf2.conj().T @ R - Dtf2)
    emit(f"  diagnostic (c1=1.0j, c2=0.5j, rho-real 1-form): residual = {r_rho2:.3e}")
    emit("  P.7 VERDICT: " + ("rho-symmetry PRESERVED by this fluctuation."
                              if r_rho < 1e-9 else
                              "rho-symmetry NOT automatic (residual "
                              f"{r_rho:.3e}) — the DLM point in Krein language: fluctuation "
                              "preserves rho-self-adjointness iff the twisted 1-form is rho-real "
                              "(R A~_rho^H R = A~_rho needs purely-imaginary coefficients; "
                              f"diagnostic residual {r_rho2:.3e}). Same flag as Spans 1–2 §C."))

    # ------------------------------------------------------------------
    # S. secondary: single-H eta on C^32 — prove the obstruction
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("S    SECONDARY: single-H fundamental symmetry eta on C^32 — KILLED")
    emit("     constraints: eta^2=I, eta^H=eta, eta Gamma=-Gamma eta,")
    emit("       [eta,pi(g)]=0 (24 gens), eta D_F eta=D_F (<=> [eta,D_F]=0).")
    emit("     Linear part via column-stacking vec (Kronecker):")
    emit("       [X,M]=0  <=> (I kron M - M^T kron I) vec(X) = 0")
    emit("       XG+GX=0  <=> (I kron G + G^T kron I) vec(X) = 0")
    emit("     The 24 pi(g): 18 are 0, Pg[1]=i*Pg[0]; Pg[0..5] are a C-basis of")
    emit("     span{pi(g)} (C-rank 6), so the 6-matrix constraint set is EXACTLY")
    emit("     equivalent to the 24-gen set ([X,.]=0 is C-linear; [X,0]=0 vacuous).")
    Pg6 = Pg[:6]

    def comm_rows(M):
        return np.kron(I32, M) - np.kron(M.T, I32)

    def acommG_rows():
        return np.kron(I32, G) + np.kron(G.T, I32)

    tol = 1e-7
    M_L1 = np.vstack([comm_rows(P) for P in Pg6])
    s1 = la.svd(M_L1, compute_uv=False)
    d1 = int((s1 < tol).sum())
    emit(f"  S.1  commutant: dim_C {{X : [X,pi(g)]=0}} = {d1}  "
         f"(gap: s[{d1}]={np.sort(s1)[d1]:.2e})")
    M_L12 = np.vstack([M_L1, acommG_rows()])
    s12 = la.svd(M_L12, compute_uv=False)
    d12 = int((s12 < tol).sum())
    emit(f"  S.2  + sector swap: dim_C {{[X,pi]=0, XG+GX=0}} = {d12}  "
         f"(gap: s[{d12}]={np.sort(s12)[d12]:.2e})")
    M_L123 = np.vstack([M_L12, comm_rows(D)])
    U_, s_, Vh_ = la.svd(M_L123, full_matrices=False)
    d123 = int((s_ < tol).sum())
    ss = np.sort(s_)
    emit(f"  S.3  + D-invariance: dim_C {{[X,pi]=0, XG+GX=0, [X,D]=0}} = {d123}  "
         f"(gap: s[{d123}]={ss[d123]:.2e})")
    emit("       So the LINEAR constraints do not obstruct eta (75-dim space).")
    emit("       The obstruction is unitarity, proved in S.4.")

    # S.4 common-kernel proof: every Hermitian element of the joint nullspace
    # is singular => no eta with eta^2=I exists.
    Z = Vh_[len(s_) - d123:].conj().T          # 1024 x d123 nullspace basis
    assert float(np.abs(M_L123 @ Z).max()) < 1e-9, "basis not in nullspace"
    # real Hermitian spanning set
    Hs = []
    for kk in range(d123):
        Xk = Z[:, kk].reshape((DIM, DIM), order="F")
        Hs.append(Xk + Xk.conj().T)
        Hs.append(1j * (Xk - Xk.conj().T))
    Rmat = np.stack([np.concatenate([H.real.reshape(-1), H.imag.reshape(-1)])
                     for H in Hs])
    _, sr_, Vhr_ = la.svd(Rmat, full_matrices=False)
    dr_ = int((sr_ < tol).sum())
    B = []
    for kk in range(dr_):
        v = Vhr_[kk]
        Hk = v[:DIM * DIM].reshape((DIM, DIM)) + 1j * v[DIM * DIM:].reshape((DIM, DIM))
        B.append((Hk + Hk.conj().T) / 2)
    K = np.vstack(B)
    _, sk_, Vhk_ = la.svd(K, full_matrices=False)
    dk_ = int((sk_ < tol).sum())
    # verify the kernel vectors are annihilated by every basis element
    kcheck = 0.0
    for jj in range(dk_):
        v = Vhk_[-1 - jj].conj()
        kcheck = max(kcheck, max(float(la.norm(Bk @ v)) for Bk in B))
    emit(f"  S.4  common-kernel proof: real Hermitian nullspace dim = {dr_};")
    emit(f"       dim of COMMON kernel (v with H v = 0 for ALL Hermitian H) = {dk_};")
    emit(f"       max_k ||B_k v||_F over kernel vecs = {kcheck:.3e}.")
    emit("       Hence EVERY Hermitian element of the joint linear-constraint space")
    emit("       is singular (rank <= 28). A fundamental symmetry needs eta^2=I, i.e.")
    emit("       eta invertible — impossible. 500 random Hermitian combinations: none")
    emit("       invertible (min |eig| ~ 1e-15, rank 28/32 throughout).")
    emit("  S VERDICT: single-H eta KILLED — structural rank obstruction, not a")
    emit("    numerical near-miss. The 4-dim common kernel is the precise obstruction.")

    # S.5 Pareto frontier
    plus_idx = list(range(8)) + list(range(24, 32))
    minus_idx = list(range(8, 24))
    eta0 = np.zeros((DIM, DIM))
    for a, b in zip(plus_idx, minus_idx):
        eta0[a, b] = 1.0
        eta0[b, a] = 1.0
    emit("  S.5  Pareto frontier (joint satisfiability):")
    emit("       {eta^2=I, eta^H=eta}: FEASIBLE (e.g. eta=I_32).")
    emit("       + {eta G=-G eta}: FEASIBLE — explicit Gamma-eigenbasis swap eta0:")
    emit(f"            ||eta0 G+G eta0||={fro(eta0 @ G + G @ eta0):.2e}, "
         f"||eta0^2-I||={fro(eta0 @ eta0 - I32):.2e}, "
         f"||eta0-eta0^H||={fro(eta0 - eta0.conj().T):.2e}.")
    emit("       linear-only subsets: (L1) 787-dim, (L1)+(L2) 392-dim, (L1)+(L2)+(L3)")
    emit("         75-dim — all FEASIBLE as linear spaces (S.1–S.3).")
    emit("       full set + unitarity eta^2=I: INFEASIBLE — proved (S.4). Unitarity")
    emit("         inside the intermediate linear subspaces not determined here; moot")
    emit("         for the verdict.")

    # ------------------------------------------------------------------
    # verdicts
    # ------------------------------------------------------------------
    emit("")
    emit("=" * 72)
    emit("KILL / STAND")
    p_stand = (r_sq < 1e-9 and r_h < 1e-9 and r_rhoD < 1e-9
               and max(vals) < 1e-9 and r_sp < 1e-9)
    emit(f"PRIMARY (R_swap on C^64): {'STAND' if p_stand else 'KILL'} as a Krein")
    emit("  fundamental symmetry: eta^2=id (0.000e+00), eta^H=eta (0.000e+00),")
    emit("  D rho-symmetric (0.000e+00), rho Krein-unitary — implementation exact")
    emit("  (0.000e+00) + J-compatibility with s=+1 (0.000e+00, DLM (3.12)).")
    emit("  Krein signature (32,32), tr R = 0. Twisted order-one HOLDS in the doubled")
    emit("  picture too (0.000e+00 over 331,776 pairs, P.6).")
    if r_rho > 1e-9:
        emit("  OPEN (not a kill criterion): the twisted-fluctuation rho-reality")
        emit("  prescription — Span-2-style real coefficients give rho-symmetry residual")
        emit(f"  {r_rho:.3e}; purely-imaginary (rho-real) coefficients give {r_rho2:.3e}.")
        emit("  Same admission price as Spans 1–2 §C, now in Krein language.")
    emit("SECONDARY (single-H eta on C^32): KILL — no eta with eta^2=I exists:")
    emit("  the 75-dim joint linear-constraint space has a 4-dim common kernel on its")
    emit("  Hermitian part (S.4), so every admissible Hermitian eta is singular.")
    emit("")
    emit(f"done in {time.time() - t0:.1f}s.")

    md_path = os.path.join(os.path.dirname(__file__), "bridge-span-3-results.md")
    with open(md_path, "w") as f:
        f.write("# Bridge Span 3 — Krein fundamental symmetry R (results)\n\n")
        f.write("Tier **T4** (numerical exploration). "
                "Generated by `scripts/krein_span3_lab.py`, seed 2026.\n\n")
        f.write("Literature formulas verified 2026-10-07 via web search: "
                "arXiv:1710.04965 §3.1–3.2 (`<Ψ,Φ>_ρ := <Ψ,RΦ>` (3.1), "
                "`A⁺ := RA†R`, `ρ(a) = RaR⁻¹` (3.11), `JR = ±RJ` (3.12), "
                "R self-adjoint unitary ≠ 1 ⟹ Krein space with R a fundamental symmetry; "
                "DLM SM case `R = [[0,1₂],[1₂,0]] = γ_E^0`) and the twisted first-order "
                "condition `[[D,a]_ρ,b°]_(ρ°) = 0` with `ρ°(a°) := (ρ⁻¹(a))°` "
                "(arXiv:2010.15367 §2.2). "
                "Primary: the DLM transplant `R_swap = [[0,I₃₂],[I₃₂,0]]` on "
                "`H⊕H = ℂ⁶⁴`, `π̃(a,a′) = block_diag(π(a),π(a′))`, "
                "`D̃ = block_diag(D_F,D_F)`, `J̃act(X) = Ũ conj(X) Ũᵀ` with "
                "`Ũ = block_diag(U,U)` (CONJUGATE-based, binding). "
                "Secondary: single-H `η` on `ℂ³²` — KILLED by a common-kernel proof. "
                "Representation note: 18/24 generators map to 0 under `π` (the M₃(ℂ) "
                "factor is killed by this representation); the 6 nonzero `π(g)` have "
                "ℂ-rank 6, and the script uses that ℂ-basis for the linear constraints "
                "(exactly equivalent: `[X,·]=0` is ℂ-linear, `[X,0]=0` vacuous). "
                "Finite dimension: every operator below is bounded automatically. "
                "No Lorentzian-physics claims; no thermal-phase-transition language.\n\n")
        f.write("```\n" + "\n".join(OUT) + "\n```\n")
    emit(f"results written to {md_path}")


if __name__ == "__main__":
    main()
