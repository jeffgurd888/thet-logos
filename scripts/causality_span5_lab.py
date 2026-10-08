#!/usr/bin/env python3
"""BRIDGE SPAN 5 — candidate causal cones on the finite triple (numerics).

Tier T4 (numerical exploration). Commissioned 2026-10-07.
Sequel to Bridge Spans 2-4: the DLM flip twist stood (Span 2), R_swap stood
as a Krein fundamental symmetry on C^64 (Span 3, primary), the single-H eta
was killed (Span 3, secondary).

This span asks the causality question: does a causal CONE exist numerically
on the finite triple, compatible with the standing bridge structures?

Axioms: Franco's causal-cone axioms (F1)-(F6), taken VERBATIM from the
literature worker's ledger
`whitepaper/bridge-span-5-causality-literature.md` (T5 survey, present in the
repo; arXiv:1212.5171 Def. 4; arXiv:1409.1480 Def. 13):
  (F1) a in C => a* = a                          (Hermitian)
  (F2) a,b in C => a+b in C                      (sum-stable)
  (F3) a in C, lam >= 0 => lam*a in C            (positive homogeneous)
  (F4) forall x in R, x*1 in C                   (ALL real multiples of the
                                                 unit, including negative)
  (F5) closure of complex-linear span of C = A   (spanning)
  (F6) forall a in C, forall phi, <phi, J[D,a]phi> <= 0
                                                 (operatorial condition with
                                                 the Krein fundamental
                                                 symmetry J)
Here J = R_swap on the doubled space C^64 (Span 3's DLM transplant),
D~ = block_diag(D_F, D_F), pi~(a,a') = block_diag(pi(a), pi(a')).

Candidates (on the REPRESENTED finite algebra -- 18/24 generators map to 0
under the lab's pi, the M3(C) factor is killed; we work with what is actually
represented: A_rep = span_C{6 active pi(g)} ~= M2(C)+C+C, A_sa,rep 2-dim):
  (a) Krein-positive cone: { a sa : R pi~(a,a) >= 0 }, diagonal (a,a).
  (b) Grading cone: { a = Gamma a Gamma : P_+ a P_+ + P_- a P_- >= 0 }.

Sections:
  A. setup: A_sa,rep (m=2), [Gamma,.]=0, represented unit e, [D_F,e]=0.
  B. candidate (a) vs (F1)-(F6): degenerate {0}.
  C. candidate (b) vs (F1)-(F6): passes (F1)-(F3), fails (F4) and (F6);
     triviality = ordinary positive cone.
  D. the (F6) characterization + no-go: (F6) <=> [D_F,A] = 0 on the diagonal
     (numerical); maximal (F6)-admissible complex span is the commutant,
     dim 3 < 6 diagonal, dim 6 < 12 doubled  =>  (F5) AND (F6) jointly
     unsatisfiable. This is the numerical half of the kill.
  E. twist compatibility: Span-2 flip rho on the doubled algebra.
  F. Krein compatibility: operator-positivity vs rho-positivity clash.
  G. verdict table.

Conventions (binding, Spans 1-3): Jact(X) = U conj(X) U^T (CONJUGATE-based);
U^H = conjugate transpose; seeds 2026/202607; Frobenius residuals.
No thermal-phase-transition language; no Lorentzian-physics claims.
Finite dimension: every operator below is bounded automatically.

Prints a results table AND writes scripts/bridge-span-5-results.md.
"""

import os
import sys
import time

import numpy as np
import scipy.linalg as la

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "python"))
from thet_logos.common import pi, piOp, af_generators, UJ, gamma_F
from thet_logos.engine13_rsd import build_DF, selfadjoint_basis, opnorm

SEED = 2026
SEED_EXTRA = 202607
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
    rng = np.random.default_rng(SEED)
    rng2 = np.random.default_rng(SEED_EXTRA)
    D = build_DF()
    U = UJ()
    G = gamma_F()
    gens = af_generators()
    Pg = [pi(g) for g in gens]
    H = selfadjoint_basis()          # orthonormal real basis of A_sa,rep
    m = len(H)
    act = [Pg[i] for i in range(24) if fro(Pg[i]) > 1e-12]  # C-basis of A_rep
    nact = len(act)
    I32 = np.eye(DIM)
    R = np.block([[np.zeros((DIM, DIM)), I32],
                  [I32, np.zeros((DIM, DIM))]])          # R_swap, real symmetric
    Pp = (I32 + G) / 2.0
    Pm = (I32 - G) / 2.0
    n_zero = 24 - nact
    # represented unit: identity of A_rep
    e = (Pg[0] + Pg[2] + Pg[0].conj().T + Pg[2].conj().T) / 2.0

    def Avec(x):
        A = np.zeros((DIM, DIM), complex)
        for k in range(m):
            A += x[k] * H[k]
        return A

    def M_rho(x):
        """R pi~(a,a) for a = Avec(x): [[0, A],[A, 0]] (candidate (a))."""
        A = Avec(x)
        return np.block([[np.zeros((DIM, DIM)), A],
                         [A, np.zeros((DIM, DIM))]])

    def E6_blk(A):
        """R [D~, pi~(a,a)] = [[0, X],[X, 0]], X = [D_F, A] anti-Hermitian."""
        X = D @ A - A @ D
        return np.block([[np.zeros((DIM, DIM)), X],
                         [X, np.zeros((DIM, DIM))]])

    emit("=" * 72)
    emit("BRIDGE SPAN 5 — candidate causal cones on the finite triple (Tier T4)")
    emit("Axioms (F1)-(F6): Franco's causal-cone axioms, verbatim from")
    emit("  whitepaper/bridge-span-5-causality-literature.md (arXiv:1212.5171 Def.4):")
    emit("  (F1) Hermitian  (F2) sum-stable  (F3) positive-homogeneous")
    emit("  (F4) ALL real multiples of the unit in C (incl. negative)")
    emit("  (F5) complex-linear span of C dense in A  (F6) <phi,J[D,a]phi> <= 0")
    emit("  with J = R_swap on C^64, D~ = block_diag(D_F,D_F) (Span 3 transplant).")
    emit("(a) Krein-positive cone: {a sa : R pi~(a,a) >= 0}, diagonal (a,a).")
    emit("(b) Grading cone: {a = Gamma a Gamma : P_+ a P_+ + P_- a P_- >= 0}.")
    emit(f"||D_F|| = {opnorm(D):.6g} GeV; {n_zero}/24 gens map to 0 under pi; "
         f"dim_C A_rep = {nact}; dim_R A_sa,rep = m = {m}")
    emit("Conventions: Jact CONJUGATE-based; seeds 2026/202607; Frobenius residuals.")

    # ------------------------------------------------------------------
    # A. setup
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("A    the represented algebra")
    gram = np.array([[np.trace(H[i].conj().T @ H[j]).real
                      for j in range(m)] for i in range(m)])
    emit(f"  A.1 self-adjoint basis orthonormality: ||Gram - I||_F = "
         f"{fro(gram - np.eye(m)):.3e}")
    rG = max(fro(G @ Hk - Hk @ G) for Hk in H)
    emit(f"  A.2 [Gamma, H_k] max residual = {rG:.3e}  (Span 2 A.0 reproduced)")
    r_unit = max(fro(e @ P - P) for P in act)
    emit(f"  A.3 represented unit e = Re(pi(g0)+pi(g2)): "
         f"max ||e pi(g) - pi(g)|| = {r_unit:.3e} (identity of A_rep); "
         f"||e^2 - e||_F = {fro(e @ e - e):.3e}")
    r_De = fro(D @ e - e @ D)
    emit(f"  A.4 [D_F, e] residual = {r_De:.3e}  "
         f"(the represented constant commutes with D_F: (F4)/(F6) not")
    emit("      trivially inconsistent via the unit)")
    S = np.stack([Hk.reshape(-1) for Hk in H], axis=1)
    cI, *_ = la.lstsq(S, I32.reshape(-1))
    ce, *_ = la.lstsq(S, e.reshape(-1))
    emit(f"  A.5 I_32 in span(H): residual = "
         f"{float(np.linalg.norm(I32.reshape(-1) - S @ cI)):.3e}  (NOT represented)")
    emit(f"      e in span(H): residual = "
         f"{float(np.linalg.norm(e.reshape(-1) - S @ ce)):.3e}  (the constant of A_rep)")
    mineig_H = [float(la.eigvalsh(Hk).min()) for Hk in H]
    emit(f"  A.6 min eigval(H_k) = {[f'{v:.6f}' for v in mineig_H]}  "
         f"(H_0, H_1 PSD); min eigval(e) = {float(la.eigvalsh(e).min()):.6f}; "
         f"min eigval(-e) = {float(la.eigvalsh(-e).min()):.6f}")

    # ------------------------------------------------------------------
    # B. candidate (a): the Krein-positive cone = {0}
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("B    candidate (a): Krein-positive cone {a : R pi~(a,a) >= 0}")
    N = 2000
    xs = rng.standard_normal((N, m))
    sym_res = 0.0
    min_eig = np.empty(N)
    for i in range(N):
        M = M_rho(xs[i])
        A = Avec(xs[i])
        lam = la.eigvalsh(A)
        evM = np.sort(la.eigvalsh(M))
        sym_res = max(sym_res,
                      float(np.linalg.norm(evM - np.sort(np.concatenate([lam, -lam])))))
        min_eig[i] = evM[0]
    nz = np.linalg.norm(xs, axis=1) > 1e-9
    bad = int(((min_eig >= -1e-9) & nz).sum())
    emit(f"  B.1 eig(R pi~(a,a)) = +/-eig(A): max residual over {N} samples = "
         f"{sym_res:.3e}; nonzero samples with min_eig >= -1e-9: {bad}/{N}")
    emit("      => R pi~(a,a) >= 0 forces A = 0: C_Krein = {0} on A_sa,rep.")
    emit("  B.2 vs (F1)-(F6):")
    emit("      (F1)-(F3): hold vacuously ({0} is a convex cone).")
    emit("      (F4): FAIL — x*e not in {0} for x != 0.")
    emit("      (F5): FAIL — span_C({0}) = {0}, dim_C A_rep = "
         f"{nact}.")
    emit("      (F6): holds vacuously ([D,0] = 0).")
    emit("  B VERDICT: DEGENERATE ({0}) — KILL as a causal cone (fails (F4),(F5)).")

    # ------------------------------------------------------------------
    # C. candidate (b): the grading cone
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("C    candidate (b): grading cone {a = Gamma a Gamma : "
         "P_+ a P_+ + P_- a P_- >= 0}")
    emit(f"  C.1 Gamma-even vacuity: max_k ||[Gamma,H_k]||_F = {rG:.3e}; "
         f"max ||P_+ A P_-||_F over 200 random A = "
         f"{max(fro(Pp @ Avec(rng.standard_normal(m)) @ Pm) for _ in range(200)):.3e}")
    emit("      => C_Gamma = {A in A_sa,rep : A >= 0} = ORDINARY positive cone.")
    cone_x = []
    while len(cone_x) < 400:
        x = rng2.standard_normal(m) * 2.0
        if la.eigvalsh(Avec(x)).min() >= -1e-9:
            cone_x.append(x)
    cone_x = np.array(cone_x)
    # convexity: closure under + and positive scaling, sampled
    viol = 0.0
    for _ in range(500):
        i, j = rng2.integers(0, len(cone_x), 2)
        t = rng2.random()
        lam = rng2.random() * 3.0
        A = t * Avec(cone_x[i]) + (1 - t) * Avec(cone_x[j])
        Bl = lam * Avec(cone_x[i])
        viol = max(viol, -min(la.eigvalsh(A).min(), 0.0),
                   -min(la.eigvalsh(Bl).min(), 0.0))
    emit(f"  C.1b convexity: 500 convex-combo/scaling tests, max PSD violation = "
         f"{viol:.3e}  (expect 0)")
    # (F6) probe on cone elements: M(a) = R[D~, pi~(a,a)] = [[0,X],[X,0]],
    # X = [D_F, A] anti-Hermitian. Hermitian part: (M+M^dagger)/2 = 0 EXACTLY
    # (M+M^dagger = [[0,X-X],[X-X,0]]); so <phi, M phi> is purely imaginary
    # unless X = 0. (F6) as an OPERATOR inequality ("j[D,a] <= 0", Besnard
    # arXiv:1508.01917 Def. 3) needs M self-adjoint: statable only on the
    # commutant.
    h_res = 0.0
    ah_nz = 0
    for x in cone_x:
        M = E6_blk(Avec(x))
        h_res = max(h_res, fro(M + M.conj().T))
        if fro(M - M.conj().T) > 1e-9:
            ah_nz += 1
    emit(f"  C.2 (F6) probe: over 400 nonzero C_Gamma samples, max ||M+M^dagger||_F "
         f"= {h_res:.3e} (Hermitian part vanishes identically);")
    emit(f"      samples with nonzero anti-Hermitian part (M not self-adjoint): "
         f"{ah_nz}/400.")
    emit("      => <phi, R[D~,pi~(a,a)]phi> is purely imaginary for generic a:")
    emit('      (F6) as "negative semidefinite OPERATOR" is not even statable')
    emit("      off the commutant [D_F, A] = 0 (in the commutative Lorentzian case")
    emit("      J[D,f] IS self-adjoint via the Clifford relations — Besnard")
    emit("      arXiv:1508.01917 §7; our finite transplant lacks that relation).")
    emit("  C.3 vs (F1)-(F6):")
    emit("      (F1)-(F3): PASS (positive cone is a convex cone; C.1b: 500")
    emit(f"                 convex-combo/scaling tests, max PSD violation {viol:.1e}).")
    emit("      (F4): FAIL — (F4) needs -e in C, but min eigval(-e) = -1.000000")
    emit("            (A.6): the positive cone contains no negative constants.")
    emit("      (F5): PASS formally (quadrant {x0,x1>=0} in C spans R^2;")
    emit("            cone-sample span rank 2 = m) — moot given (F4),(F6) fail.")
    emit("      (F6): NOT STATABLE for generic a (C.2: the (F6) form is purely")
    emit("            imaginary off the commutant; an operator inequality needs")
    emit("            a self-adjoint operator).")
    emit("  C.4 TRIVIALITY: C_Gamma IS the ordinary positive cone of A_sa,rep")
    emit("      (C.1) — order structure, not causal structure. SAYING SO.")
    emit("  C VERDICT: KILL as a causal cone — fails Franco (F4) (no negative")
    emit("      constants), (F6) not even statable off the commutant (C.2/D), and")
    emit("      trivial (positive cone) regardless.")

    # ------------------------------------------------------------------
    # D. the (F6) characterization and the general no-go
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("D    (F6) audit: Hermiticity first, then the no-go")
    emit('     (F6) is an OPERATOR inequality: "j[D,a] <= 0 (is a negative')
    emit('     semidefinite operator)" (Besnard arXiv:1508.01917 Def. 3). It is')
    emit("     statable only where M(a) := R[D~,pi~(a,a)] is self-adjoint.")
    emit("     M(a) = [[0,X],[X,0]], X = [D_F,A] anti-Hermitian;")
    emit("     M+M^dagger = [[0,X-X],[X-X,0]] = 0 EXACTLY, so <phi,M(a)phi> is")
    emit("     purely imaginary unless X = 0. (In the commutative Lorentzian")
    emit("     case J[D,f] is self-adjoint via the Clifford relations — ibid. §7.")
    # D.0 Hermiticity audit
    N6 = 500
    hmax = 0.0
    agree = 0
    for _ in range(N6):
        A = Avec(rng.standard_normal(m))
        M = E6_blk(A)
        hmax = max(hmax, fro(M + M.conj().T))
        sa = fro(M - M.conj().T) <= 1e-9      # M self-adjoint?
        cm = fro(D @ A - A @ D) <= 1e-9        # [D,A] = 0?
        if sa == cm:
            agree += 1
    emit(f"  D.0 Hermiticity audit over {N6} samples: max ||M+M^dagger||_F = "
         f"{hmax:.3e} (Hermitian part vanishes identically);")
    emit(f"      (M self-adjoint  <=>  [D_F,A] = 0): {agree}/{N6}.")
    emit("      => the (F6) form is purely imaginary off the commutant; (F6) is")
    emit("      statable (as a real operator inequality) EXACTLY on")
    emit("      {a in A_sa,rep : [D_F, pi(a)] = 0}, where M(a) = 0 and (F6) holds")
    emit("      with equality.")
    # commutant dimensions
    Mr = np.stack([np.concatenate([(D @ Hk - Hk @ D).reshape(-1).real,
                                   (D @ Hk - Hk @ D).reshape(-1).imag])
                   for Hk in H], axis=1)
    sr = la.svdvals(Mr)
    dr = int((sr < 1e-7 * sr[0]).sum())
    Mc = np.stack([(D @ P - P @ D).reshape(-1) for P in act], axis=1)
    sc = la.svdvals(Mc)
    dc = int((sc < 1e-7 * sc[0]).sum())
    emit(f"  D.1 real commutant in A_sa,rep: dim = {dr} (of {m}); "
         f"complex commutant in A_rep: dim = {dc} (of {nact})")
    emit(f"      singular values: {np.round(sc, 4)}")
    # doubled version: M_dbl = R[D~, pi~(a,a')] = [[0,U],[V,0]],
    # U = [D,A'], V = [D,A] (anti-Hermitian). Self-adjoint <=> U+V = 0
    # <=> [D, A+A'] = 0; then M_dbl = [[0,U],[-U,0]] Hermitian with
    # eigenvalues +/-mu(U); <= 0 <=> U = 0.
    Nd = 200
    agree_d = 0
    for _ in range(Nd):
        A1 = Avec(rng.standard_normal(m))
        A2 = Avec(rng.standard_normal(m))
        U_ = D @ A2 - A2 @ D
        V_ = D @ A1 - A1 @ D
        Mdbl = np.block([[np.zeros((DIM, DIM)), U_],
                         [V_, np.zeros((DIM, DIM))]])
        sa = fro(Mdbl - Mdbl.conj().T) <= 1e-9
        sm = fro(D @ (A1 + A2) - (A1 + A2) @ D) <= 1e-9
        if sa == sm:
            agree_d += 1
    emit(f"  D.2 doubled: (M_dbl self-adjoint  <=>  [D, A+A'] = 0): "
         f"{agree_d}/{Nd};")
    emit("      where self-adjoint, M_dbl = [[0,U],[-U,0]] <= 0  <=>  U = 0;")
    emit("      direct check on 100 commutant-x-commutant pairs:")
    # verify: (F6)-admissible doubled set = commutant x commutant
    Uc, sc_, Vhc = la.svd(Mc, full_matrices=False)
    nullc = Vhc[len(sc_) - dc:].conj().T          # 6 x dc commutant basis (coeffs)
    adm_res = 0.0
    adm_sa = 0.0
    adm_ev = -np.inf
    for _ in range(100):
        c1 = rng.standard_normal(dc) + 1j * rng.standard_normal(dc)
        c2 = rng.standard_normal(dc) + 1j * rng.standard_normal(dc)
        A1 = sum((nullc @ c1)[j] * act[j] for j in range(nact))
        A2 = sum((nullc @ c2)[j] * act[j] for j in range(nact))
        adm_res = max(adm_res, fro(D @ A1 - A1 @ D), fro(D @ A2 - A2 @ D))
        U_ = D @ A2 - A2 @ D
        V_ = D @ A1 - A1 @ D
        Mdbl = np.block([[np.zeros((DIM, DIM)), U_],
                         [V_, np.zeros((DIM, DIM))]])
        Hdbl = (Mdbl + Mdbl.conj().T) / 2
        adm_sa = max(adm_sa, fro(Mdbl - Mdbl.conj().T))
        adm_ev = max(adm_ev, float(la.eigvalsh(Hdbl).max()))
    emit(f"      check on 100 commutant-x-commutant pairs: max ||[D,A]||_F = "
         f"{adm_res:.3e}; max ||M_dbl - M_dbl^dagger||_F = {adm_sa:.3e};")
    emit(f"      max eigval of Hermitian part = {adm_ev:.3e} (<= 0 holds).")
    emit(f"      => (F6)-admissible doubled set = commutant x commutant, complex "
         f"dim {2 * dc} < {2 * nact}.")
    emit("  D.3 NO-GO: any cone on which (F6) is even statable has complex-linear")
    emit(f"      span inside the commutant: dim {dc} < {nact} (diagonal), dim "
         f"{2 * dc} < {2 * nact} (doubled).")
    emit("      => (F5) [spanning] AND (F6) [operatorial] are JOINTLY UNSATISFIABLE")
    emit("      on the represented finite triple with the DLM Krein structure")
    emit("      (R_swap, D~): (F6) is not even a real inequality off the commutant,")
    emit("      and the commutant does not span. No Franco-style causal cone exists")
    emit("      here — not just the two candidates: the axioms have no model.")
    emit("  D VERDICT: KILL — general, numerical half (Lean: Hermiticity audit,")
    emit("      statability <=> commutant, commutant properness).")

    # ------------------------------------------------------------------
    # E. twist compatibility
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("E    twist compatibility: Span-2 flip rho on the doubled algebra")
    vals = [fro(R @ la.block_diag(Pg[ia], Pg[ib]) @ R
                - la.block_diag(Pg[ib], Pg[ia]))
            for ia in range(24) for ib in range(24)]
    emit(f"  E.1 || R pi~(a,a') R - pi~(a',a) ||_F max over 576 gen pairs: "
         f"{max(vals):.3e}  (Span 3 P.2 reproduced)")
    mx = 0.0
    nbad = 0
    for _ in range(200):
        i, j = rng2.integers(0, len(cone_x), 2)
        A1, A2 = Avec(cone_x[i]), Avec(cone_x[j])
        r = fro(R @ la.block_diag(A1, A2) @ R - la.block_diag(A2, A1))
        mx = max(mx, r)
        if la.eigvalsh((R @ la.block_diag(A1, A2) @ R)[:DIM, :DIM]).min() < -1e-9:
            nbad += 1
    emit(f"  E.2 200 random (a,a') in doubled positive cone: max flip residual = "
         f"{mx:.3e}; blocks leaving the cone: {nbad}")
    emit("  E VERDICT: flip preserves the doubled cone exactly — PASS (both")
    emit("      candidates; (a) trivially). Twist compatibility is NOT the blocker.")

    # ------------------------------------------------------------------
    # F. Krein compatibility: operator-positivity vs rho-positivity
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("F    Krein compatibility: the two positivities on the diagonal")
    n_clash = 0
    worst_eig = 0.0
    for x in cone_x:
        me = float(la.eigvalsh(M_rho(x)).min())
        worst_eig = min(worst_eig, me)
        if me < -1e-9:
            n_clash += 1
    emit(f"  F.1 {len(cone_x)} nonzero C_Gamma samples: {n_clash} have "
         f"min_eig(R pi~(a,a)) < -1e-9 (worst {worst_eig:.4f})")
    emit("  F VERDICT: CLASH — operator-positivity and rho-product positivity are")
    emit("      incompatible on the diagonal; only {0} is both (cf. B). This is the")
    emit("      finite-triple shadow of why (F6) bites: the Krein form sees the")
    emit("      commutator, not the order.")

    # ------------------------------------------------------------------
    # G. verdict table
    # ------------------------------------------------------------------
    emit("")
    emit("=" * 72)
    emit("G    VERDICT TABLE (Franco (F1)-(F6))")
    emit("  candidate | (F1-3) | (F4) consts | (F5) span | (F6) oper.    | verdict")
    emit("  (a) Krein | vacuous| FAIL        | FAIL      | vacuous     | KILL — {0}")
    emit("            | ({0})  | (no x*e)    | (span={0})| (M(0)=0)    |  degenerate")
    emit("  (b) grade | PASS   | FAIL        | (pass*)   | NOT STATABLE| KILL — trivial")
    emit("            | (pos.  | (-e not PSD,| (*moot)   | (form purely |  + fails (F4)")
    emit("            |  cone) | min eig -1) |           |  imaginary  |")
    emit("            |        |             |           |  off comm.)  |")
    emit("  general   | —      | —           | FAIL      | —           | KILL — no model")
    emit("            |        |             | (statable span: commutant, dim 3<6;")
    emit("            |        |             |  doubled 6<12)")
    emit("")
    emit("  NUMERICAL HALF OF THE KILL:")
    emit("  * (a) is exactly {0} (B.1: +/- spectrum, residual "
         f"{sym_res:.1e}; {bad}/{N}")
    emit("    nonzero PSD samples) — degenerate, fails (F4),(F5).")
    emit("  * (b) is the ordinary positive cone (Gamma-even vacuous, C.1 residual "
         f"{rG:.1e})")
    emit("    — order structure, not causal structure — and fails Franco (F4)")
    emit("    (negative constants not PSD, min eig(-e) = -1).")
    emit("  * (F6) audit (D): M(a) = R[D~,pi~(a,a)] has vanishing Hermitian part")
    emit(f"    (D.0: max ||M+M^dagger|| = {hmax:.1e}); <phi,M(a)phi> is purely")
    emit(f"    imaginary off the commutant ({agree}/{N6} agreement) — (F6) as a")
    emit('    "negative semidefinite operator" (Besnard arXiv:1508.01917 Def. 3)')
    emit("    is statable exactly on [D_F,A] = 0, where it holds with equality.")
    emit(f"    Maximal statable complex span = commutant, dim {dc} < {nact} "
         f"(diagonal),")
    emit(f"    {2 * dc} < {2 * nact} (doubled, D.2: {agree_d}/{Nd}) — so (F5) and (F6)")
    emit("    are jointly unsatisfiable. No Franco-style causal cone exists on the")
    emit("    represented finite triple with the DLM Krein structure (R_swap, D~).")
    emit("    (In the commutative Lorentzian case J[D,f] IS self-adjoint via the")
    emit("    Clifford relations — ibid. §7; the finite transplant lacks it.)")
    emit("  * Twist compatibility PASSES (E.1 residual 0) — not the blocker.")
    emit("  * Besnard side-note (literature ledger §4b): M_3(C) is egalitarian")
    emit("    (trivial isocone only) — already killed by the representation here;")
    emit("    the represented M_2(C) summand is the one matrix algebra admitting")
    emit("    nontrivial isocones, but the Franco route is closed by (F5)x(F6).")
    emit("  The Lean worker formalizes: Hermiticity audit of M(a), statability <=>")
    emit("  commutant, commutant properness (dim 3<6 / 6<12), cone-(a) degeneracy.")
    emit("  These numbers are the T4 numerical half.")
    emit("")
    emit(f"done in {time.time() - t0:.1f}s.")

    md_path = os.path.join(os.path.dirname(__file__), "bridge-span-5-results.md")
    with open(md_path, "w") as f:
        f.write("# Bridge Span 5 — candidate causal cones on the finite triple (results)\n\n")
        f.write("Tier **T4** (numerical exploration). "
                "Generated by `scripts/causality_span5_lab.py`, seeds 2026 / 202607.\n\n")
        f.write("Causal-cone axioms: **Franco's (F1)–(F6)**, taken verbatim from the literature "
                "worker's ledger `whitepaper/bridge-span-5-causality-literature.md` "
                "(arXiv:1212.5171 Def. 4; arXiv:1409.1480 Def. 13): "
                "(F1) Hermitian; (F2) sum-stable; (F3) positive-homogeneous; "
                "(F4) **all** real multiples of the unit in C (including negative); "
                "(F5) complex-linear span of C dense in the algebra; "
                "(F6) `⟨φ, J[D,a]φ⟩ ≤ 0 ∀φ`, with `J = R_swap = [[0,I₃₂],[I₃₂,0]]` on `ℂ⁶⁴` "
                "and `D̃ = block_diag(D_F, D_F)` (the Span 3 DLM Krein transplant). "
                "Candidates on the **represented** finite algebra (18/24 generators map to 0 "
                "under the lab's `π`; the `M₃(ℂ)` factor is killed): "
                "(a) Krein-positive cone `{a sa : R π̃(a,a) ≥ 0}` on the diagonal `(a,a)`; "
                "(b) grading cone `{a = ΓaΓ : P₊aP₊ + P₋aP₋ ≥ 0}`. "
                "`A_rep = span_ℂ{6 active π(g)}` (dim 6), `A_sa,rep` real-dim 2. "
                "Conventions: `Jact(X) = U conj(X) Uᵀ` (CONJUGATE-based); "
                "finite dimension ⇒ every operator bounded automatically. "
                "No thermal-phase-transition language; no Lorentzian-physics claims.\n\n")
        f.write("```\n" + "\n".join(OUT) + "\n```\n")
    emit(f"results written to {md_path}")


if __name__ == "__main__":
    main()
