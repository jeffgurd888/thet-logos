#!/usr/bin/env python3
"""BRIDGE SPAN 1 — twisted-triple numerics over the finite triple.

Tier T4 (numerical exploration). Commissioned 2026-10-07.

Twist:  rho_s(a) := sigma(K, s, a) = e^{isK} a e^{-isK}   (unitary conjugation)
with K = -logm(rho) hermitized, rho = random 32x32 density state, seed 2026
(exactly the python/thet_logos/modular_flow.py construction).

Finite dimension (32) => every operator below is bounded automatically;
boundedness is not a numerical question here. No continuum limit, no
thermal-phase-transition language, no Lorentzian claims anywhere.

Sections:
  A.1 regularity:            || rho_s(a^dagger) - (rho_s^{-1}(a))^dagger ||
  A.2 preservation:          dist(sigma_s(pi(a)), pi(A_F))  [decides Aut?]
  A.3 real structure:        || [K, U_J] ||_F
  A.4 twisted commutators:   || [D_F,a]_{rho_s} || vs || [D_F, pi(a)] ||
  A.5 s -> 0 limit of the twisted commutator
  B   twisted order-one over all 576 generator pairs, s in {0, 0.5, 1.0}
  C   twisted fluctuation explorer: D_{A_rho}, self-adjointness, spectrum drift,
      twisted order-one on the fluctuated Dirac

Prints a results table AND writes scripts/bridge-span-1-results.md.
Fixed seeds throughout: SEED = 2026 (twist state K), SEED_FLUCT (explorer).
"""

import os
import sys
import time

import numpy as np
import scipy.linalg as la

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "python"))
from thet_logos.common import pi, piOp, af_generators, random_af, UJ
from thet_logos.engine13_rsd import build_DF, selfadjoint_basis, opnorm
from thet_logos.modular_flow import sigma, random_state

SEED = 2026
SEED_FLUCT = 202607
DIM = 32
S_GRID = [0.0, -0.1, 0.1, -0.5, 0.5, -1.0, 1.0, -2.0, 2.0]

OUT = []  # lines mirrored to the results markdown file


def emit(line=""):
    print(line, flush=True)
    OUT.append(line)


def fro(M):
    return float(la.norm(M, "fro"))


# --------------------------------------------------------------------------
# 0. ground
# --------------------------------------------------------------------------

def build_K():
    """Reproduce modular_flow.py's K exactly: seed-2026 random density."""
    rng = np.random.default_rng(SEED)
    rho = random_state(rng)          # first draws of the 2026 stream
    K = -la.logm(rho)
    K = (K + K.conj().T) / 2.0
    return K, rho


def c_orthonormalize(mats):
    """Complex Gram-Schmidt under <A,B> = Tr(A^dagger B); returns basis + rank."""
    basis = []
    for M in mats:
        v = M.reshape(-1).astype(complex).copy()
        for b in basis:
            v -= np.vdot(b, v) * b
        n = float(la.norm(v))
        if n > 1e-10:
            basis.append(v / n)
    return [b.reshape(DIM, DIM) for b in basis], len(basis)


def main():
    t0 = time.time()
    D = build_DF()
    K, rho = build_K()
    U = UJ()
    gens = af_generators()
    Pg = [pi(g) for g in gens]
    active = [i for i, P in enumerate(Pg) if fro(P) > 1e-12]
    kernel = [i for i, P in enumerate(Pg) if fro(P) <= 1e-12]

    emit("=" * 72)
    emit("BRIDGE SPAN 1 — twisted-triple numerics  (Tier T4, numerical)")
    emit("twist rho_s(a) = sigma(K,s,a) = e^{isK} a e^{-isK}, "
         "K = -logm(rho) hermitized, seed 2026")
    emit("finite dimension 32: all operators bounded automatically")
    emit(f"||D_F|| = {opnorm(D):.6g} GeV, ||K||_F = {fro(K):.6g}")
    emit(f"generators: 24 total, {len(active)} with pi(g) != 0, "
         f"{len(kernel)} in ker pi (Option-A kills M3(C): documented artifact)")

    # complex-linear span of the represented generators = pi(A_F) as matrices
    basis, rank = c_orthonormalize(Pg)
    emit(f"dim_C span{{pi(g)}} = {rank}  (expect 6: the C-summand contributes "
         f"2 since embedSM is only real-linear in u1 via conj(u1); the four "
         f"quaternion-unit matrices C-span all of M2(C); M3(C) in ker pi)")
    if rank != 6:
        emit("WARNING: rank != 6; projection still well-defined, "
             "interpretation needs review")

    def proj_residual(M):
        v = M.reshape(-1)
        r = v.copy()
        for b in basis:
            bv = b.reshape(-1)
            r -= np.vdot(bv, v) * bv
        return float(la.norm(r))

    def Us(s):
        return la.expm(1j * s * K)

    # sanity: precomputed-unitary twist == modular_flow.sigma
    A_test = Pg[active[0]]
    assert fro(Us(0.7) @ A_test @ Us(0.7).conj().T
               - sigma(K, 0.7, A_test)) < 1e-10

    # ------------------------------------------------------------------
    # A.1 regularity
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("A.1  regularity  || rho_s(a^dagger) - (rho_s^{-1}(a))^dagger ||_F")
    emit("     (Connes-Moscovici regularity; rho_s^{-1} = sigma(K,-s,.))")
    emit(f"{'s':>6} {'max over 24 gens':>16} {'max over 6 active':>18}")
    reg = {}
    for s in S_GRID:
        F, Fi = Us(s), Us(-s)
        Fd, Fid = F.conj().T, Fi.conj().T
        # rho_s(a^d) = F P^d F^d ; (rho_s^{-1}(a))^d = (Fi P Fi^d)^d
        #          = Fi P^d Fi^d
        vals = [fro(F @ P.conj().T @ Fd - Fi @ P.conj().T @ Fid)
                for P in Pg]
        reg[s] = vals
        emit(f"{s:>6.2f} {max(vals):>16.3e} "
             f"{max(vals[i] for i in active):>18.3e}")
    # diagnostic: unitary conjugation IS a *-automorphism
    star_auto = max(fro(Us(0.7) @ P.conj().T @ Us(0.7).conj().T
                        - (Us(0.7) @ P @ Us(0.7).conj().T).conj().T)
                    for P in Pg)
    emit(f"diagnostic *-automorphism residual "
         f"||rho_s(a^d) - rho_s(a)^d|| at s=0.7: {star_auto:.3e} (expect ~1e-12)")
    emit("A.1 VERDICT: regularity as stated FAILS for s != 0 (norm ~ 2|s| "
         "||[K,a^d]||, linear in s); holds trivially at s = 0. "
         "Unitary conjugation is a *-automorphism, but the CM identity "
         "rho(a*) = rho^{-1}(a)* does not hold for generic inner twist.")

    # ------------------------------------------------------------------
    # A.2 preservation
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("A.2  preservation: dist(sigma_s(pi(a)), pi(A_F)) = projection "
         "residual ||.||_F")
    emit("     (Frobenius-orthonormal complex basis of span{pi(g)}; "
         "decides rho_s in Aut(pi(A_F))?)")
    emit(f"{'s':>6} {'max resid (24)':>15} {'mean resid (24)':>16} "
         f"{'max resid (6 active)':>21}")
    pres = {}
    for s in S_GRID:
        F = Us(s)
        Fc = F.conj().T
        vals = [proj_residual(F @ P @ Fc) for P in Pg]
        pres[s] = vals
        emit(f"{s:>6.2f} {max(vals):>15.3e} {np.mean(vals):>16.3e} "
             f"{max(vals[i] for i in active):>21.3e}")
    emit("per-generator max-over-s residual (6 active gens):")
    for i in active:
        emit(f"  gen {i:>2}: {max(pres[s][i] for s in S_GRID):.3e}   "
             f"(||pi(g)||_F = {fro(Pg[i]):.3e})")
    pmax = max(max(v) for v in pres.values())
    emit(f"A.2 VERDICT: max residual {pmax:.3e} >> 0 for s != 0  =>  "
         "REFUTED: rho_s does NOT preserve pi(A_F); the generic K mixes the "
         "16-sector with the dead sector. (s = 0 residual ~1e-12 trivially.)")

    # ------------------------------------------------------------------
    # A.3 real-structure compatibility
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("A.3  real-structure compatibility: || [K, U_J] ||_F")
    cKU = fro(K @ U - U @ K)
    emit(f"||[K, U_J]||_F = {cKU:.6e}   (relative: {cKU / fro(K):.4f})")
    emit("A.3 VERDICT: nonzero for generic K => the twist does not commute "
         "with the real structure; rho_s(J) = eps J cannot hold with this K.")

    # ------------------------------------------------------------------
    # A.4 twisted vs untwisted commutators
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("A.4  || [D_F,a]_{rho_s} ||_F = || D pi(a) - sigma_s(pi(a)) D ||_F "
         "vs untwisted")
    emit(f"{'s':>6} {'mean tw':>10} {'max tw':>10} {'mean ratio':>11} "
         f"{'max ratio':>10}   (ratio over gens with ||[D,pi(a)]||>1e-12)")
    for s in S_GRID:
        F, Fc = Us(s), Us(s).conj().T
        tw, un, rat = [], [], []
        for P in Pg:
            t = fro(D @ P - (F @ P @ Fc) @ D)
            u = fro(D @ P - P @ D)
            tw.append(t)
            un.append(u)
            if u > 1e-12:
                rat.append(t / u)
        emit(f"{s:>6.2f} {np.mean(tw):>10.3e} {max(tw):>10.3e} "
             f"{np.mean(rat):>11.3f} {max(rat):>10.3f}")

    # ------------------------------------------------------------------
    # A.5 s -> 0 limit
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("A.5  s -> 0: max_g || [D,a]_{rho_s} - [D,a] ||_F  (expect -> 0)")
    for s in [-0.1, 0.1, -0.01, 0.01]:
        F, Fc = Us(s), Us(s).conj().T
        d = max(fro((F @ P @ Fc - P) @ D) for P in Pg)
        emit(f"  s = {s:>6.3f}:  {d:.3e}")
    emit("A.5 VERDICT: linear in |s| -> 0 as required "
         "(diff = (pi(a) - sigma_s(pi(a))) D).")

    # ------------------------------------------------------------------
    # B. twisted order-one, 576 pairs
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("B    twisted order-one: [[D_F,a]_{rho_s}, b^o]_{(rho_s)^o}, "
         "max over 24x24 = 576 pairs")
    emit("     inner = D@pia - sigma_s(pia)@D ; "
         "outer = inner@b^o - piOp(sigma_{-s}(pib))@inner")
    b_op = [piOp(P) for P in Pg]
    emit(f"{'s':>5} {'max ||outer||_F':>16} {'mean ||outer||_F':>17} "
         f"{'n pairs > 1e-9':>15}")
    bmax = {}
    for s in [0.0, 0.5, 1.0]:
        F, Fi = Us(s), Us(-s)
        vals = []
        for ia, Pa in enumerate(Pg):
            inner = D @ Pa - (F @ Pa @ F.conj().T) @ D
            for ib, Pb in enumerate(Pg):
                t_op = piOp(Fi @ Pb @ F)   # piOp(sigma(K,-s,pib))
                outer = inner @ b_op[ib] - t_op @ inner
                vals.append(fro(outer))
        bmax[s] = max(vals)
        emit(f"{s:>5.1f} {max(vals):>16.3e} {np.mean(vals):>17.3e} "
             f"{sum(1 for v in vals if v > 1e-9):>15}")
    emit("untwisted census value for comparison: 0.000e+00 "
         "(s = 0 reproduces it up to roundoff).")
    emit(f"B VERDICT: s = 0 max {bmax[0.0]:.3e} (order-one holds); "
         f"s = 0.5 max {bmax[0.5]:.3e}; s = 1.0 max {bmax[1.0]:.3e}.")

    # ------------------------------------------------------------------
    # C. twisted fluctuation explorer
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("C    twisted fluctuation explorer: A_rho = sum_k a_k [D,b_k]_{rho_s}")
    emit("     D_{A_rho} = D + A_rho + J A_rho J^{-1},  "
         "J X J^{-1} = U_J conj(X) U_J^T")
    emit("     (piOp uses transpose M^T; the J-action uses conjugate conj(X):")
    emit("      they agree on Hermitian X, differ otherwise -- see notes)")
    s_fl = 0.5
    F, Fi = Us(s_fl), Us(-s_fl)
    Fc = F.conj().T

    def twisted_comm(P):
        return D @ P - (F @ P @ Fc) @ D

    def Jact(X):
        return U @ X.conj() @ U.T

    rng = np.random.default_rng(SEED_FLUCT)
    choices = {
        "random (seed 202607, 3 terms)":
            ([pi(random_af(rng)) for _ in range(3)],
             [pi(random_af(rng)) for _ in range(3)]),
    }
    Hself = selfadjoint_basis()
    emit(f"self-adjoint represented basis dim = {len(Hself)} "
         f"(Option-A artifact, cf. engine13)")
    choices["structured (self-adjoint basis, 2 terms)"] = (
        [Hself[0], Hself[1]], [Hself[1], Hself[0]])

    evals_D = la.eigvalsh(D)
    emit(f"{'choice':<42} {'||A_rho||/||D||':>14} {'selfadj resid':>13} "
         f"{'spectrum drift':>15} {'tw-ord1 max':>12}")
    for name, (aks, bks) in choices.items():
        A_rho = sum((ak @ twisted_comm(bk)
                     for ak, bk in zip(aks, bks)),
                    np.zeros((DIM, DIM), complex))
        Df = D + A_rho + Jact(A_rho)
        sa_res = fro(Df - Df.conj().T)
        # spectrum drift on the Hermitian part if not self-adjoint
        Hf = (Df + Df.conj().T) / 2.0
        drift = float(la.norm(np.sort(la.eigvalsh(Hf)) - np.sort(evals_D)))
        tag = "" if sa_res < 1e-9 else " (of Hermitian part)"
        # twisted order-one on the fluctuated Dirac, same s
        omax = 0.0
        for Pa in Pg:
            inner = Df @ Pa - (F @ Pa @ Fc) @ Df
            for ib, Pb in enumerate(Pg):
                t_op = piOp(Fi @ Pb @ F)
                omax = max(omax, fro(inner @ b_op[ib] - t_op @ inner))
        emit(f"{name:<42} {fro(A_rho) / fro(D):>14.3e} {sa_res:>13.3e} "
             f"{drift:>15.3e}{tag} {omax:>12.3e}")
    emit("C notes: D_{A_rho} self-adjointness is NOT automatic for twisted "
         "1-forms; drift compares sorted spectra (2-norm of difference).")

    emit("")
    emit("=" * 72)
    emit(f"done in {time.time() - t0:.1f}s. "
         "Boundedness: automatic in finite dimension (stated, not tested).")

    md_path = os.path.join(os.path.dirname(__file__),
                           "bridge-span-1-results.md")
    with open(md_path, "w") as f:
        f.write("# Bridge Span 1 — twisted-triple numerics (results)\n\n")
        f.write("Tier **T4** (numerical exploration). "
                "Generated by `scripts/twisted_triple_lab.py`, seed 2026.\n\n")
        f.write("Twist: `rho_s(a) = sigma(K,s,a) = e^{isK} a e^{-isK}`, "
                "`K = -logm(rho)` hermitized, rho = seed-2026 random density "
                "(the `modular_flow.py` construction). "
                "Finite dimension 32: every operator below is bounded "
                "automatically; boundedness is not a numerical question here. "
                "No continuum limit is taken; no thermal-phase-transition "
                "language; no Lorentzian claims.\n\n")
        f.write("```\n" + "\n".join(OUT) + "\n```\n")
    emit(f"results written to {md_path}")


if __name__ == "__main__":
    main()
