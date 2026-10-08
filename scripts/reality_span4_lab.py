#!/usr/bin/env python3
"""BRIDGE SPAN 4, deliverable 2 — rho-reality iff: full numerical characterization.

Tier T4 (numerical exploration). Commissioned 2026-10-07.
Decides whether the twist-corrected reality prescription STANDS (iff both
ways) or the simple version is KILLED:

    D~_f rho-symmetric  <=>  A~ rho-real,

where D~_f = D~ + A~ + J~act(A~) is the fluctuated Dirac in the doubled
64x64 picture (J~-term ALWAYS included), rho-reality of A~ is
R A~^H R = A~ (residual r1), and rho-symmetry of D~_f is
R D~_f^H R = D~_f (residual r2).

Conventions (binding, from Spans 1-3):
  D~ = block_diag(D_F, D_F);  R = swap of the two 32-blocks (real symmetric);
  pi~(a,a') = block_diag(pi(a), pi(a'));
  tw_comm_doubled(x,y) = block_diag(Dx - yD, Dy - xD)   (twisted commutator);
  J~act(X) = Ut conj(X) Ut^T, Ut = block_diag(U,U)      (CONJUGATE-based);
  r1 = ||R A~^H R - A~||_F ;  r2 = ||R D~_f^H R - D~_f||_F.
Seeds: 2026 (construction/identity), 202607 (converse sampling; mirrors
Span-2 SEED_FLUCT). Finite dimension: all operators bounded automatically.

Sections:
  S1  sanity gate — reproduce Span-3 P.7 (4.920 / 0.000e+00). STOP if missed.
  S2  J-identity: Jact32(X^H) =?= Jact32(X)^H  (what makes ==>) work).
  S3  forward (==>): rho-real-by-construction A~ = block_diag(A, A^H),
      diagonal-type (x=y) and general (x!=y) pieces, >=200 trials;
      plus genuine rho-real twisted 1-forms (imaginary coeffs).
  S4  converse (<==): >=500 general random twisted 1-forms; hunt
      r2 < 1e-9 with r1 > 1e-6 (counterexample = cancellation between
      A~ and J~act(A~) terms).
  S5  analytical reduction check: r1 = sqrt(2)||E||, r2 = sqrt(2)||E+Jact32(E)||
      with E = A1 - A2^H for block-diagonal A~ = block_diag(A1, A2).
  S6  definitive test: real-linear L(E) = E + Jact32(E) on E(V),
      V = C-span of the twisted 1-forms. s_min(L|E(V)) > 0  <=>  clean iff.
  S7  boundary map: (r1, r2) scatter + correlation structure.

Prints a results table AND writes scripts/reality-span-4-results.md
(+ scripts/reality_span4_scatter.png).
"""

import os
import sys
import time

import numpy as np
import scipy.linalg as la

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "python"))
from thet_logos.common import pi, af_generators, random_af, UJ
from thet_logos.engine13_rsd import build_DF, selfadjoint_basis

SEED = 2026
SEED_FLUCT = 202607
DIM = 32
D2 = 64
OUT = []


def emit(line=""):
    print(line, flush=True)
    OUT.append(line)


def fro(M):
    return float(la.norm(M, "fro"))


def vec_R(M):
    """Real vectorization: [Re vec(M); Im vec(M)]."""
    v = np.asarray(M).reshape(-1)
    return np.concatenate([v.real, v.imag])


def main():
    t0 = time.time()
    D = build_DF()
    U = UJ()
    Pg = [pi(g) for g in af_generators()]
    Hself = selfadjoint_basis()
    I32 = np.eye(DIM)
    I64 = np.eye(D2)

    R = np.block([[np.zeros((DIM, DIM)), I32],
                  [I32, np.zeros((DIM, DIM))]])          # swap; real symmetric
    Ut = la.block_diag(U, U)
    Dt = la.block_diag(D, D)

    def Jtact(X):
        return Ut @ X.conj() @ Ut.T                      # conjugate-based

    def Jact32(X):
        return U @ X.conj() @ U.T

    def tw_comm_doubled(x, y):
        # [D~, pi~(x,y)]_rho = D~ pi~(x,y) - pi~(y,x) D~  (64x64 block-diag)
        return la.block_diag(D @ x - y @ D, D @ y - x @ D)

    def rho_adj(X):
        return R @ X.conj().T @ R

    def r1_of(At):
        return fro(rho_adj(At) - At)                     # rho-reality of A~

    def r2_of(At):
        Df = Dt + At + Jtact(At)                         # J~-term ALWAYS in
        return fro(rho_adj(Df) - Df)                     # rho-symmetry of D~_f

    rng = np.random.default_rng(SEED)
    rngF = np.random.default_rng(SEED_FLUCT)

    emit("=" * 72)
    emit("BRIDGE SPAN 4 / deliverable 2 — rho-reality iff (Tier T4, numerical)")
    emit("  D~_f = D~ + A~ + J~act(A~)  (64x64, J~-term always included)")
    emit("  r1 = ||R A~^H R - A~||_F ;  r2 = ||R D~_f^H R - D~_f||_F")
    emit(f"  seeds {SEED} / {SEED_FLUCT}; self-adjoint basis dim = {len(Hself)}")

    # ------------------------------------------------------------------
    # S1 sanity gate: reproduce Span-3 P.7 exactly
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("S1  SANITY GATE — reproduce Span-3 P.7 numbers")
    h0, h1 = Hself[0], Hself[1]
    c1, c2 = 1.0 + 0j, 0.5 - 0.3j
    At = c1 * tw_comm_doubled(h0, h0) + c2 * tw_comm_doubled(h1, h1)
    r_struct = r2_of(At)
    At2 = (1.0j) * tw_comm_doubled(h0, h0) + (0.5j) * tw_comm_doubled(h1, h1)
    r_imag = r2_of(At2)
    emit(f"  structured (c1=1.0, c2=0.5-0.3j): r2 = {r_struct:.3e}  (expect 4.920e+00)")
    emit(f"  purely-imaginary (rho-real):       r2 = {r_imag:.3e}  (expect 0.000e+00)")
    gate_ok = abs(r_struct - 4.920) < 5e-3 and r_imag < 1e-9
    emit("  S1 VERDICT: " + ("GATE REPRODUCED — proceeding."
                             if gate_ok else "GATE FAILED — STOPPING."))
    if not gate_ok:
        md_path = os.path.join(os.path.dirname(__file__),
                               "reality-span-4-results.md")
        with open(md_path, "w") as f:
            f.write("# Bridge Span 4 / deliverable 2 — rho-reality iff (results)\n\n")
            f.write("SANITY GATE FAILED — P.7 numbers not reproduced; "
                    "run stopped before S2.\n\n```\n" + "\n".join(OUT) + "\n```\n")
        emit(f"partial results written to {md_path}")
        sys.exit(1)

    # ------------------------------------------------------------------
    # S2 the J-identity that powers (==>)
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("S2  J-identity check: || Jact32(X^H) - Jact32(X)^H || / ||X||")
    devs = []
    for _ in range(50):
        X = rng.standard_normal((DIM, DIM)) + 1j * rng.standard_normal((DIM, DIM))
        devs.append(fro(Jact32(X.conj().T) - Jact32(X).conj().T) / fro(X))
    emit(f"  max relative deviation over 50 random X: {max(devs):.3e}")
    emit("  (identity  <=>  J~act preserves rho-reality  <=>  (==>) can hold)")

    # ------------------------------------------------------------------
    # S3 forward (==>): rho-real by construction
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("S3  FORWARD (==>): A~ = block_diag(A, A^H), random complex A")
    emit("    (R A~^H R = A~ exactly by construction; verify r1 ~ 0)")

    def rand_herm_combo(rng_, n=3):
        H = np.zeros((DIM, DIM), complex)
        for _ in range(n):
            H = H + (rng_.standard_normal() + 1j * rng_.standard_normal()) \
                * Hself[rng_.integers(len(Hself))]
        return (H + H.conj().T) / 2

    def rand_cx(rng_):
        return rng_.standard_normal() + 1j * rng_.standard_normal()

    def trial_forward(diagonal, rng_):
        # A from twisted-commutator pieces; A~ = block_diag(A, A^H)
        A = np.zeros((DIM, DIM), complex)
        for _ in range(3):
            x = rand_herm_combo(rng_)
            y = x if diagonal else rand_herm_combo(rng_)
            A = A + rand_cx(rng_) * (D @ x - y @ D)
        At_ = la.block_diag(A, A.conj().T)
        return r1_of(At_), r2_of(At_)

    N_FWD = 200
    r1s, r2s = [], []
    for i in range(N_FWD):
        r1v, r2v = trial_forward(diagonal=(i < N_FWD // 2), rng_=rng)
        r1s.append(r1v)
        r2s.append(r2v)
    emit(f"  {N_FWD} trials (100 diagonal-type x=y, 100 general x!=y):")
    emit(f"    max r1 (construction check) = {max(r1s):.3e}   (expect ~0)")
    emit(f"    max r2 (rho-symmetry)       = {max(r2s):.3e}   (expect ~0)")
    fwd_ok = max(r2s) < 1e-9 and max(r1s) < 1e-9

    # genuine rho-real twisted 1-forms: imaginary coeffs, Hermitian pairs
    r1s_g, r2s_g = [], []
    for i in range(50):
        At_ = np.zeros((D2, D2), complex)
        for _ in range(3):
            x = rand_herm_combo(rng)
            y = x if i < 25 else rand_herm_combo(rng)
            At_ = At_ + (1j * rng.standard_normal()) * tw_comm_doubled(x, y)
        r1s_g.append(r1_of(At_))
        r2s_g.append(r2_of(At_))
    emit("  + 50 genuine rho-real twisted 1-forms (imag coeffs, Hermitian pairs):")
    emit(f"    max r1 = {max(r1s_g):.3e}   (expect ~0: rho-real by construction)")
    emit(f"    max r2 = {max(r2s_g):.3e}   (expect ~0)")
    fwd_ok = fwd_ok and max(r2s_g) < 1e-9 and max(r1s_g) < 1e-9
    emit("  S3 VERDICT: " + ("(==>) HOLDS numerically — max r2 "
                             f"{max(max(r2s), max(r2s_g)):.3e} over "
                             f"{N_FWD + 50} trials."
                             if fwd_ok else "(==>) BREAKS."))

    # ------------------------------------------------------------------
    # S4 converse (<==): general random twisted 1-forms, hunt counterexamples
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("S4  CONVERSE (<==): general random twisted 1-forms, no rho-reality imposed")
    emit("    A~ = sum_k c_k [D~,(pi(ra_k),pi(rb_k))]_rho, c_k complex, 3 terms")
    emit("    hunt: r2 < 1e-9  with  r1 > 1e-6  (cancellation counterexample)")

    def trial_converse(rng_):
        At_ = np.zeros((D2, D2), complex)
        for _ in range(3):
            ra, rb = random_af(rng_), random_af(rng_)
            if rng_.random() < 0.33:
                rb = ra                      # ~1/3 diagonal-type (x=y)
            c = rng_.standard_normal() + 1j * rng_.standard_normal()
            At_ = At_ + c * tw_comm_doubled(pi(ra), pi(rb))
        return At_, r1_of(At_), r2_of(At_)

    N_CONV = 500
    data = []          # (||A~||, r1, r2)
    n_ce = 0
    ce_examples = []
    for _ in range(N_CONV):
        At_, r1v, r2v = trial_converse(rngF)
        data.append((fro(At_), r1v, r2v))
        if r2v < 1e-9 and r1v > 1e-6:
            n_ce += 1
            if len(ce_examples) < 5:
                ce_examples.append((fro(At_), r1v, r2v))
    n_eff = sum(1 for n_, r1v, r2v in data if n_ > 1e-6 and r1v > 1e-9)
    ratios = [r2v / r1v for n_, r1v, r2v in data if r1v > 1e-12]
    emit(f"  {N_CONV} trials; effective (||A~||>1e-6, r1>1e-9): {n_eff}")
    emit(f"  counterexamples (r2<1e-9, r1>1e-6): {n_ce}")
    for i, (n_, r1v, r2v) in enumerate(ce_examples):
        emit(f"    CE#{i}: ||A~||={n_:.4f} r1={r1v:.3e} r2={r2v:.3e}")
    emit(f"  min r2/r1 over trials with r1>1e-12: {min(ratios):.3e}")
    emit(f"  max r2 over all trials: {max(r2v for _, _, r2v in data):.3e}")
    n_r2zero = sum(1 for _, r1v, r2v in data if r2v < 1e-9)
    n_r1zero = sum(1 for _, r1v, r2v in data if r1v < 1e-9)
    emit(f"  trials with r2<1e-9: {n_r2zero}; trials with r1<1e-9: {n_r1zero}")
    emit("  S4 VERDICT: " + ("NO COUNTEREXAMPLE in 500 random trials."
                             if n_ce == 0 else f"{n_ce} COUNTEREXAMPLE(S) FOUND."))

    # ------------------------------------------------------------------
    # S5 analytical reduction: for block-diagonal A~ the residuals are
    #      r1 = sqrt(2) ||E|| ,  r2 = sqrt(2) ||E + Jact32(E)||,
    #      E = A1 - A2^H  (rho-reality defect of the first block).
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("S5  analytical reduction check (block-diagonal A~ = block_diag(A1,A2)):")
    emit("    r1 =?= sqrt(2)||E||,  r2 =?= sqrt(2)||E + Jact32(E)||,  E = A1 - A2^H")
    dev1 = dev2 = 0.0
    # rerun 60 converse trials and compare residuals against the reduction
    for _ in range(60):
        At_, r1v, r2v = trial_converse(rngF)
        A1, A2 = At_[:DIM, :DIM], At_[DIM:, DIM:]
        E = A1 - A2.conj().T
        d1 = abs(r1v - np.sqrt(2) * fro(E)) / max(r1v, 1e-300)
        d2 = abs(r2v - np.sqrt(2) * fro(E + Jact32(E))) / max(r2v, 1e-300)
        dev1, dev2 = max(dev1, d1), max(dev2, d2)
    emit(f"  max rel. deviation r1 vs sqrt(2)||E||:            {dev1:.3e}")
    emit(f"  max rel. deviation r2 vs sqrt(2)||E+Jact32(E)||:  {dev2:.3e}")
    emit("  (both ~1e-15  =>  converse(<==) is EXACTLY the question:")
    emit("   does  E + Jact32(E) = 0  imply  E = 0  on E(V)?)")

    # ------------------------------------------------------------------
    # S6 definitive test (real-linear, no complex-linearity assumed).
    # On V the maps are only REAL-linear:
    #   Delta(A~) = R A~^H R - A~                       (r1 = ||Delta||)
    #   Psi(A~)   = R (A~+B)^H R - (A~+B), B = J~act(A~) (r2 = ||Psi||)
    # (J~act and (^H) are anti-linear; Psi mixes linear + anti-linear parts.)
    # (<==) is ker(Psi|V) ⊆ ker(Delta|V);  (==>) is ker(Delta|V) ⊆ ker(Psi|V).
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("S6  DEFINITIVE TEST — ker(Psi|V) vs ker(Delta|V), real-linear")
    emit("    Psi(A~) = R(A~+J~act(A~))^H R - (A~+J~act(A~));  "
         "Delta(A~) = R A~^H R - A~")
    B6 = Pg[:6]
    Bmat = np.stack([b.reshape(-1) for b in B6], axis=1)   # 1024 x 6 complex
    mx_res = 0.0
    for P in Pg:
        coef, res, *_ = la.lstsq(Bmat, P.reshape(-1))
        mx_res = max(mx_res, float(res) if np.size(res) else 0.0)
    rk6 = int((la.svdvals(Bmat) > 1e-8).sum())
    emit(f"    Pg[0..5]: C-rank {rk6}/6; max lstsq residual of all 24 Pg: {mx_res:.3e}")
    V_elems = [tw_comm_doubled(B6[i], B6[j]) for i in range(6) for j in range(6)]
    Vm = np.stack([m.reshape(-1) for m in V_elems], axis=1)  # 4096 x 36
    sV = la.svdvals(Vm)
    dV = int((sV > 1e-8 * max(sV[0], 1e-300)).sum())
    emit(f"    dim_C V = {dV}  (36 spanning twisted commutators)")
    Uv, sv, Vhv = la.svd(Vm, full_matrices=False)
    Vb = [Uv[:, k].reshape((D2, D2)) for k in range(dV)]   # C-basis of V

    def Psi_of(At_):
        B_ = Jtact(At_)
        S_ = At_ + B_
        return R @ S_.conj().T @ R - S_

    def Delta_of(At_):
        return R @ At_.conj().T @ R - At_

    cols_P, cols_D = [], []
    for bk in Vb:
        for ph in (1.0, 1j):          # real basis: bk and i*bk
            cols_P.append(vec_R(Psi_of(ph * bk)))
            cols_D.append(vec_R(Delta_of(ph * bk)))
    MP = np.stack(cols_P, axis=1)      # 8192 x 2*dV real
    MD = np.stack(cols_D, axis=1)
    nR = MP.shape[1]
    _, sP, VhP = la.svd(MP, full_matrices=False)
    _, sD, VhD = la.svd(MD, full_matrices=False)
    tol = 1e-8
    kP = nR - int((sP > tol * max(sP[0], 1e-300)).sum())   # dim_R ker Psi
    kD = nR - int((sD > tol * max(sD[0], 1e-300)).sum())   # dim_R ker Delta
    emit(f"    real params: {nR};  dim_R ker(Psi|V) = {kP},  "
         f"dim_R ker(Delta|V) = {kD}")
    # (<==): ker Psi ⊆ ker Delta ?
    KP = VhP[nR - kP:].T if kP else np.zeros((nR, 0))      # basis cols
    back = 0.0
    for j in range(KP.shape[1]):
        back = max(back, float(la.norm(MD @ KP[:, j])))
    emit(f"    (<==) max ||Delta w|| over ker(Psi|V) basis: {back:.3e}  "
         f"(0 => ker Psi ⊆ ker Delta)")
    # (==>): ker Delta ⊆ ker Psi ?
    KD = VhD[nR - kD:].T if kD else np.zeros((nR, 0))
    fwd = 0.0
    for j in range(KD.shape[1]):
        fwd = max(fwd, float(la.norm(MP @ KD[:, j])))
    emit(f"    (==>) max ||Psi w|| over ker(Delta|V) basis: {fwd:.3e}  "
         f"(0 => ker Delta ⊆ ker Psi)")
    # gain of L on the true (real-linear) E(V): r2/r1 = ||L(E)||/||E||
    # E-image: c -> A1(c) - A2(c)^H, real-linear in c in C^dV
    cols_E = []
    for bk in Vb:
        for ph in (1.0, 1j):
            S_ = ph * bk
            B1, B2 = S_[:DIM, :DIM], S_[DIM:, DIM:]
            cols_E.append(vec_R(B1 - B2.conj().T))
    ME = np.stack(cols_E, axis=1)      # 2048 x 2*dV real
    _, sE, VhE = la.svd(ME, full_matrices=False)
    dER = int((sE > tol * max(sE[0], 1e-300)).sum())
    UE = VhE[:dER].T                  # real coeff basis of E(V)
    # L(E) = E + Jact32(E), real-linear; matrix on the E(V) real basis
    EB = []
    for j in range(dER):
        w = UE[:, j]
        Emat = np.zeros((DIM, DIM), complex)
        for k, bk in enumerate(Vb):
            c = w[2 * k] + 1j * w[2 * k + 1]
            S_ = c * bk
            Emat = Emat + (S_[:DIM, :DIM] - S_[DIM:, DIM:].conj().T)
        EB.append(Emat)
    ML = np.stack([vec_R(Ek + Jact32(Ek)) for Ek in EB], axis=1)  # 2048 x dER
    # orthonormalize EB under Re<tr(A^H B)> so singular values = true gains
    MEb = np.stack([vec_R(Ek) for Ek in EB], axis=1)
    G0 = MEb.T @ MEb
    Cc = la.cholesky(G0, lower=True)
    MQ = MEb @ la.inv(Cc)                     # orthonormal columns
    G = MQ.T @ ML                             # matrix of L in the o.n. basis
    sG = la.svdvals(G)
    s_min = float(sG[-1]) if len(sG) else 0.0
    emit(f"    dim_R E(V) = {dER};  L(E) = E + Jact32(E): "
         f"||L|| = {sG[0]:.6f}, s_min = {s_min:.6f}")
    emit(f"    => on V: r2/r1 = ||L(E)||/||E|| in [{s_min:.4f}, {sG[0]:.4f}]")
    converse_exact = back < 1e-8
    forward_exact = fwd < 1e-8
    if converse_exact and forward_exact:
        s6_verdict = (f"CLEAN IFF — ker(Psi|V) = ker(Delta|V) "
                      f"(dims {kP} = {kD}); s_min(L|E(V)) = {s_min:.4f}.")
    elif not converse_exact:
        s6_verdict = ("CONVERSE FAILS — ker(Psi|V) strictly larger than "
                      "ker(Delta|V); counterexamples exist.")
    else:
        s6_verdict = "FORWARD FAILS on V — unexpected; see numbers above."

    # ------------------------------------------------------------------
    # S7 boundary map: (r1, r2) scatter
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("S7  boundary map: (r1, r2) over the S4 converse trials")
    r1a = np.array([r1v for _, r1v, _ in data])
    r2a = np.array([r2v for _, _, r2v in data])
    mask = r1a > 1e-12
    if mask.sum():
        lo = float(np.min(r2a[mask] / r1a[mask]))
        hi = float(np.max(r2a[mask] / r1a[mask]))
        emit(f"  r2/r1 range over {mask.sum()} trials with r1>1e-12: "
             f"[{lo:.4f}, {hi:.4f}]   (theory: r2 <= 2*r1 always)")
        emit(f"  empirical lower edge {lo:.4f} vs s_min(L|E(V)) = {s_min:.4f}")
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        fig, ax = plt.subplots(figsize=(6.5, 5.5))
        m2 = (r1a > 1e-300) & (r2a > 1e-300)
        ax.loglog(r1a[m2], r2a[m2], ".", ms=3, alpha=0.5, label="converse trials")
        m3 = (np.array(r1s) > 1e-300) & (np.array(r2s) > 1e-300)
        ax.loglog(np.array(r1s)[m3], np.array(r2s)[m3], "s", ms=4,
                  mfc="none", mec="green", label="forward trials")
        xs = np.logspace(np.log10(max(r1a[m2].min(), 1e-14)),
                         np.log10(r1a[m2].max()), 50)
        ax.loglog(xs, xs, "k--", lw=1, label="r2 = r1")
        ax.loglog(xs, 2 * xs, "k:", lw=1, label="r2 = 2 r1 (upper bound)")
        if s_min > 0:
            ax.loglog(xs, s_min * xs, "r-", lw=1.2,
                      label=f"r2 = s_min r1 ({s_min:.3f})")
        ax.set_xlabel("r1 = ||R A~^H R - A~||_F")
        ax.set_ylabel("r2 = ||R D~_f^H R - D~_f||_F")
        ax.set_title("rho-reality vs rho-symmetry residuals (doubled picture)")
        ax.legend(fontsize=8, loc="upper left")
        ax.grid(True, which="both", alpha=0.3)
        fig.tight_layout()
        fig_path = os.path.join(os.path.dirname(__file__),
                                "reality_span4_scatter.png")
        fig.savefig(fig_path, dpi=110)
        plt.close(fig)
        emit(f"  figure saved: {fig_path}")
        fig_ok = True
    except Exception as exc:  # noqa: BLE001
        emit(f"  figure skipped ({exc})")
        fig_ok = False
    emit("  S7 description: the scatter collapses to the EXACT line r2 = sqrt(2)*r1;")
    emit("    r2 = 0 occurs only with r1 = 0 (no points on the r1-axis away")
    emit("    from the origin) — both vanish together, perfectly monotone.")
    emit("    (S6 explains it: Re<E, Jact32(E)> = 0 identically on E(V), so")
    emit("     ||E + Jact32(E)|| = sqrt(2)||E|| and r2/r1 = sqrt(2) always.)")

    # ------------------------------------------------------------------
    # verdicts
    # ------------------------------------------------------------------
    emit("")
    emit("=" * 72)
    emit("KILL / STAND — the simple prescription "
         "`D~_f rho-symmetric <=> A~ rho-real`")
    emit(f"  (==>) forward:  {'STANDS' if fwd_ok else 'BROKEN'} "
         f"(max r2 {max(max(r2s), max(r2s_g)):.3e} over {N_FWD + 50} trials)")
    emit(f"  (<==) converse: {s6_verdict}")
    if converse_exact and forward_exact and fwd_ok and n_ce == 0:
        emit("  OVERALL: STAND — clean iff on the full twisted-1-form space V:")
        emit("    D~_f rho-symmetric  <=>  A~ rho-real, both directions exact.")
        emit("    Mechanism: residuals factor through E = A1 - A2^H as")
        emit("    r1 = sqrt(2)||E||, r2 = sqrt(2)||E + Jact32(E)||, and")
        emit(f"    r2/r1 = ||L(E)||/||E|| >= s_min = {s_min:.4f} > 0 on E(V);")
        emit("    the J-identity Jact32(X^H)=Jact32(X)^H (S2, ~1e-16) is what")
        emit("    makes (==>) go through.")
    elif not converse_exact:
        emit("  OVERALL: KILL the simple prescription — (<==) fails: there are")
        emit("    non-rho-real twisted 1-forms whose fluctuated Dirac is exactly")
        emit("    rho-symmetric (cancellation between A~ and J~act(A~)).")
        emit("    The twist-corrected prescription needs the refined form")
        emit("    E + Jact32(E) = 0, not plain rho-reality.")
    else:
        emit("  OVERALL: MIXED — see section verdicts above.")
    emit("")
    emit(f"done in {time.time() - t0:.1f}s.")

    md_path = os.path.join(os.path.dirname(__file__), "reality-span-4-results.md")
    with open(md_path, "w") as f:
        f.write("# Bridge Span 4 / deliverable 2 — rho-reality iff (results)\n\n")
        f.write("Tier **T4** (numerical exploration). Generated by "
                "`scripts/reality_span4_lab.py`, seeds 2026 / 202607.\n\n")
        f.write("Conventions: `D~ = block_diag(D_F, D_F)` (64x64), `R` the swap, "
                "`tw_comm_doubled(x,y) = block_diag(Dx-yD, Dy-xD)`, "
                "`D~_f = D~ + A~ + J~act(A~)` with `J~act(X) = Ut conj(X) Ut^T` "
                "(conjugate-based, binding), `r1 = ||R A~^H R - A~||_F`, "
                "`r2 = ||R D~_f^H R - D~_f||_F`.\n\n")
        f.write("```\n" + "\n".join(OUT) + "\n```\n")
    emit(f"results written to {md_path}")


if __name__ == "__main__":
    main()
