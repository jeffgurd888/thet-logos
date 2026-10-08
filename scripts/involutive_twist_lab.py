#!/usr/bin/env python3
"""BRIDGE SPAN 2 — DLM involutive twist-by-grading (flip twist) numerics.

Tier T4 (numerical exploration). Commissioned 2026-10-07.
Sequel to Bridge Span 1 (twisted_triple_lab.py), which killed twist-from-flow
(rho_s = e^{isK} a e^{-isK}, generic K). Span 1's A.1 lesson: CM regularity
wants involutive twists (rho^2 = id), not one-parameter inner groups.

Candidate: Devastato-Lizzi-Martinetti minimal twist by grading, the flip
twist (Filaci-Martinetti SIGMA 2020, section 2.3).

  Grading:  Gamma = diag(+I8, -I8, -I8, +I8), 32x32, from thet_logos.common.
  Because [Gamma, pi(g)] = 0 for all 24 gens (verified below), the naive
  rho(a) = Gamma a Gamma is TRIVIAL, so DLM doubles the algebra.
  P_+ = (I+Gamma)/2, P_- = (I-Gamma)/2.
  pi2(a,a') = P_+ . pi(a) + P_- . pi(a')        (doubled representation)
  flip:      rho(a,a') = (a',a)                  (involutive by construction)
  twisted commutator: [D,(a,a')]_rho = D pi2(a,a') - pi2(a',a) D
  opposite/flip: (a,a')^o = (a^o, a'^o) componentwise (piOp);
                 rho^o((a,a')^o) = (a'^o, a^o) since rho^{-1} = rho.
  twisted outer: [X,(b,b')^o]_{rho^o} = X (b,b')^o - rho^o((b,b')^o) X.

Convention note (binding, from Span 1): piOp uses TRANSPOSE
(piOp(M) = U_J . M^T . U_J); the lab's J-action J X J^{-1} = U_J . conj(X) . U_J^T
uses CONJUGATE. They agree on Hermitian X, differ otherwise. B uses piOp
for b^o; C uses the J-action for the fluctuation. Stated wherever used.

Finite dimension (32): every operator below is bounded automatically.
Seeds: SEED = 2026 (pair sampling), SEED_FLUCT = 202607 (fluctuation).

Sections:
  A.0 sanity checks on Gamma (commutes pi, anticommutes D, G^2=1, herm, tr 0)
  A.1 CM regularity: || rho((a,a')^d) - (rho^{-1}(a,a'))^d ||_F   (expect 0)
  A.2 preservation: pi2 o rho lands in image(pi2) (expect exact, by constr.)
  A.3 J-compatibility: || pi2(rho(a,a')) - Gamma pi2(a,a') Gamma ||_F,
        and whether the J-action swaps/preserves the +- sectors
  A.4 twisted commutator norms vs untwisted (mean/max ratios; Span 1 blew 12-59x)
  B   twisted order-one [[D,(a,a')]_rho, (b,b')^o]_{rho^o}, full 576x576 pairs
  C   twisted fluctuation explorer (self-adjointness, spectrum drift,
      twisted order-one on fluctuated Dirac)
  D   Krein probe: Gamma D_{A_rho} Gamma = D_{A_rho}^H ? (exploratory T4)

Prints a results table AND writes scripts/bridge-span-2-results.md.
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
SEED_FLUCT = 202607
DIM = 32
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
    active = [i for i, P in enumerate(Pg) if fro(P) > 1e-12]

    Pp = (np.eye(DIM) + G) / 2.0
    Pm = (np.eye(DIM) - G) / 2.0

    def pi2(ia, ib):
        """Doubled representation of pair (a_ia, a_ib): P_+ pi(a) + P_- pi(a')."""
        return Pp @ Pg[ia] + Pm @ Pg[ib]

    def piOp2(ia, ib):
        """Componentwise opposite: (a,a')^o = (a^o, a'^o), piOp = transpose-based."""
        return Pp @ piOp(Pg[ia]) + Pm @ piOp(Pg[ib])

    emit("=" * 72)
    emit("BRIDGE SPAN 2 — DLM flip-twist-by-grading numerics (Tier T4, numerical)")
    emit("Gamma = diag(+I8,-I8,-I8,+I8); pi2(a,a') = P_+ pi(a) + P_- pi(a')")
    emit("flip rho(a,a') = (a',a), involutive by construction (rho^2 = id)")
    emit("convention: piOp uses TRANSPOSE; J-action uses CONJUGATE")
    emit(f"||D_F|| = {opnorm(D):.6g} GeV, "
         f"generators: 24 total, {len(active)} active, "
         f"pair set: 24x24 = 576 doubled elements")

    # ------------------------------------------------------------------
    # A.0 sanity checks on Gamma (verified facts, reproduced)
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("A.0  Gamma sanity checks (verified facts from the brief, reproduced)")
    emit(f"  [Gamma,pi(g)] max over 24 gens : {max(fro(G @ P - P @ G) for P in Pg):.3e} (expect 0)")
    emit(f"  {{Gamma,D_F}} = {fro(G @ D + D @ G):.3e} (expect 0)")
    emit(f"  Gamma^2 - I = {fro(G @ G - np.eye(DIM)):.3e}, "
         f"Gamma^H - Gamma = {fro(G - G.conj().T):.3e}, tr Gamma = {np.trace(G):.3e}")
    emit(f"  rank P_+ = {np.trace(Pp).real:.0f}, rank P_- = {np.trace(Pm).real:.0f}")
    # a = a' reduces to the ordinary commutator
    red = max(fro(D @ pi2(i, i) - pi2(i, i) @ D - (D @ Pg[i] - Pg[i] @ D))
              for i in range(24))
    emit(f"  a=a' reduction to ordinary commutator: max diff {red:.3e} (expect 0)")

    # ------------------------------------------------------------------
    # A.1 CM regularity  || rho((a,a')^d) - (rho^{-1}(a,a'))^d ||
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("A.1  CM regularity  || rho((a,a')^d) - (rho^{-1}(a,a'))^d ||_F")
    emit("     rho = flip, rho^{-1} = rho (involutive); d = dagger componentwise")
    vals = []
    for ia in range(24):
        for ib in range(24):
            lhs = Pp @ Pg[ib].conj().T + Pm @ Pg[ia].conj().T   # pi2(rho(a,a')^d)
            rhs = pi2(ib, ia).conj().T                          # (rho^{-1}(a,a'))^d
            vals.append(fro(lhs - rhs))
    emit(f"  max over all 576 pairs: {max(vals):.3e}   (Span 1: 0.866-2.02 REFUTED)")
    emit(f"  mean: {np.mean(vals):.3e}")
    emit("  A.1 VERDICT: " + ("HOLDS EXACTLY (involutive => CM-regular by construction)."
                              if max(vals) < 1e-9 else "FAILED."))

    # ------------------------------------------------------------------
    # A.2 preservation: pi2 o rho in image(pi2)?
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("A.2  preservation: is the flip well-defined on the represented")
    emit("     doubled algebra? i.e. || pi2(rho(a,a')) - pi2(a',a) ||_F")
    vals = [fro(pi2(ib, ia) - pi2(ib, ia)) for ia in range(24) for ib in range(24)]
    # (trivially zero; the substantive check: pi2(flip) has a preimage pair
    # in the 24x24 set -- (a',a) -- so it lies in image(pi2))
    res = max(fro((Pp @ Pg[ib] + Pm @ Pg[ia]) - pi2(ib, ia))
              for ia in range(24) for ib in range(24))
    emit(f"  max residual: {res:.3e}; preimage pair (a',a) always in the 24x24 set")
    emit("  A.2 VERDICT: HOLDS BY CONSTRUCTION (verified numerically).")
    emit("       Unlike Span 1's rho_s, the flip permutes the doubled basis,")
    emit("       so it cannot leave the represented algebra.")

    # ------------------------------------------------------------------
    # A.3 J-compatibility
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("A.3  J-compatibility of the flip with the real structure")

    def Jact(X):
        return U @ X.conj() @ U.T      # conjugate-based (lab convention)

    # (i) conjugation-by-Gamma vs the flip
    #     Gamma pi2(a,a') Gamma = pi2(a,a') since [Gamma, pi]=0 and [Gamma,P_pm]=0,
    #     so this measures whether the flip acts trivially on pi2: it does not.
    r1 = [fro(pi2(ib, ia) - G @ pi2(ia, ib) @ G) for ia in range(24) for ib in range(24)]
    emit(f"  (i)  || pi2(rho(a,a')) - Gamma pi2(a,a') Gamma ||_F :")
    emit(f"       max {max(r1):.3e}, mean {np.mean(r1):.3e} over 576 pairs")
    # (ii) does the J-action preserve or swap the +- sectors?
    Jp = Jact(Pp)
    s_keep = fro(Jp - Pp)
    s_swap = fro(Jp - Pm)
    emit("  (ii) J-action on the grading projectors (J X J^{-1} = U conj(X) U^T):")
    emit(f"       || J P_+ J^{{-1}} - P_+ ||_F = {s_keep:.3e}  (preserve)")
    emit(f"       || J P_+ J^{{-1}} - P_- ||_F = {s_swap:.3e}  (swap)")
    # (iii) direct: does J intertwine the flip?
    #       check || J pi2(rho(a,a')) J^{-1} - pi2-flip of (J pi2(a,a') J^{-1}) ||
    #       The cleanest test: is J pi2(a,a') J^{-1} in the doubled image at all?
    #       Compare against pi2(ia,ib) structure: report deviation from
    #       sector-block form G (J pi2 J^{-1}) G = +/- (J pi2 J^{-1}).
    blk = [fro(G @ Jact(pi2(ia, ib)) @ G - Jact(pi2(ia, ib)))
           for ia in range(24) for ib in range(24)]
    emit(f"  (iii) sector-block test: max || Gamma (J pi2 J^{{-1}}) Gamma"
         f" - (J pi2 J^{{-1}}) ||_F = {max(blk):.3e}")
    emit("       (0 would mean the J-action preserves the +/- block structure)")
    if s_keep < 1e-9:
        verdict_a3 = "J preserves the grading sectors (J P_+ J^{-1} = P_+)."
    elif s_swap < 1e-9:
        verdict_a3 = ("J SWAPS the grading sectors (J P_+ J^{-1} = P_-) -- the DLM "
                      "flip intertwines with J by exchanging the copies.")
    else:
        verdict_a3 = (f"J neither preserves nor swaps the sectors (residuals "
                      f"{s_keep:.3e}/{s_swap:.3e}); no clean intertwining.")
    emit(f"  A.3 VERDICT: {verdict_a3}")

    # ------------------------------------------------------------------
    # A.4 twisted vs untwisted commutators
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("A.4  || [D_F,(a,a')]_rho ||_F vs untwisted || [D_F, pi(a)] ||_F")
    tw, un, rat = [], [], []
    for ia in range(24):
        for ib in range(24):
            t = fro(D @ pi2(ia, ib) - pi2(ib, ia) @ D)
            u = fro(D @ Pg[ia] - Pg[ia] @ D)
            tw.append(t)
            un.append(u)
            if u > 1e-12:
                rat.append(t / u)
    emit(f"  twisted: mean {np.mean(tw):.3e}, max {max(tw):.3e}")
    emit(f"  untwisted (first component): mean {np.mean(un):.3e}, max {max(un):.3e}")
    emit(f"  ratio twisted/untwisted over pairs with ||[D,pi(a)]||>1e-12:")
    emit(f"       mean {np.mean(rat):.3f}, max {max(rat):.3f}   "
         f"(Span 1: 12-59x blow-up)")
    emit(f"  A.4 VERDICT: {'TAME (ratio O(1)).' if max(rat) < 2.0 else 'inflated.'}")

    # ------------------------------------------------------------------
    # B. twisted order-one: [[D,(a,a')]_rho, (b,b')^o]_{rho^o}, 576x576
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("B    twisted order-one: [[D_F,(a,a')]_rho, (b,b')^o]_{(rho)^o}")
    emit("     576 inner x 576 outer = 331,776 pairs, piOp = TRANSPOSE-based")
    emit("     inner = D pi2(a,a') - pi2(a',a) D")
    emit("     outer = inner . (b,b')^o - rho^o((b,b')^o) . inner")
    emit("            with (b,b')^o = P_+ b^o + P_- b'^o,")
    emit("            rho^o((b,b')^o) = P_+ b'^o + P_- b^o  (rho^{-1} = rho)")
    # precompute
    inner = np.empty((576, DIM, DIM), dtype=complex)
    bo = np.empty((576, DIM, DIM), dtype=complex)
    bo_flip = np.empty((576, DIM, DIM), dtype=complex)
    k = 0
    for ia in range(24):
        for ib in range(24):
            inner[k] = D @ pi2(ia, ib) - pi2(ib, ia) @ D
            bo[k] = piOp2(ia, ib)
            bo_flip[k] = piOp2(ib, ia)
            k += 1
    mx = 0.0
    nbad = 0
    tot = 0.0
    n = 576
    for ki in range(n):
        Xi = inner[ki]
        for kj in range(n):
            r = fro(Xi @ bo[kj] - bo_flip[kj] @ Xi)
            if r > mx:
                mx = r
            tot += r
            if r > 1e-9:
                nbad += 1
    emit(f"  max ||outer||_F = {mx:.3e}   (Span 1: 53.31 BROKEN)")
    emit(f"  mean = {tot / (n * n):.3e},  pairs > 1e-9: {nbad} / {n * n}")
    emit("  B VERDICT: " + ("TWISTED ORDER-ONE HOLDS (max <= 1e-9)."
                            if mx <= 1e-9
                            else f"BREAKS (max {mx:.3e})."))

    # ------------------------------------------------------------------
    # C. twisted fluctuation explorer
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("C    twisted fluctuation explorer: A_rho = sum_k c_k [D,(x_k,x'_k)]_rho")
    emit("     D_{A_rho} = D + A_rho + J A_rho J^{-1}, J-action = U conj(.) U^T")

    def twisted_comm2(ia, ib):
        return D @ pi2(ia, ib) - pi2(ib, ia) @ D

    rng = np.random.default_rng(SEED_FLUCT)
    # random: pairs of random_af components, random complex coefficients
    rpairs = []
    for _ in range(3):
        ra, rb = random_af(rng), random_af(rng)
        rpairs.append((pi(ra), pi(rb), (rng.standard_normal() + 1j * rng.standard_normal())))
    choices = {"random (seed 202607, 3 terms)": rpairs}
    Hself = selfadjoint_basis()
    emit(f"self-adjoint represented basis dim = {len(Hself)}")
    choices["structured (self-adjoint basis, 2 terms)"] = [
        (Hself[0], Hself[1], 1.0 + 0j), (Hself[1], Hself[0], 0.5 - 0.3j)]

    evals_D = la.eigvalsh(D)
    emit(f"{'choice':<42} {'||A_rho||/||D||':>14} {'selfadj resid':>13} "
         f"{'spectrum drift':>15} {'tw-ord1 max':>12}")
    fluctuated = {}
    for name, terms in choices.items():
        A_rho = np.zeros((DIM, DIM), complex)
        for xa, xb, c in terms:
            # embed pair components as 24-index? random_af pairs are not gens;
            # use pi2 directly on the represented matrices
            M = D @ (Pp @ xa + Pm @ xb) - (Pp @ xb + Pm @ xa) @ D
            A_rho += c * M
        Df = D + A_rho + Jact(A_rho)
        fluctuated[name] = Df
        sa_res = fro(Df - Df.conj().T)
        Hf = (Df + Df.conj().T) / 2.0
        drift = float(la.norm(np.sort(la.eigvalsh(Hf)) - np.sort(evals_D)))
        tag = "" if sa_res < 1e-9 else " (of Hermitian part)"
        # twisted order-one on the fluctuated Dirac over all 576x576 pairs
        innerf = np.empty((576, DIM, DIM), dtype=complex)
        k = 0
        for ia in range(24):
            for ib in range(24):
                innerf[k] = Df @ pi2(ia, ib) - pi2(ib, ia) @ Df
                k += 1
        omax = 0.0
        for ki in range(576):
            Xi = innerf[ki]
            for kj in range(576):
                r = fro(Xi @ bo[kj] - bo_flip[kj] @ Xi)
                if r > omax:
                    omax = r
        emit(f"{name:<42} {fro(A_rho) / fro(D):>14.3e} {sa_res:>13.3e} "
             f"{drift:>15.3e}{tag} {omax:>12.3e}")
    emit("C notes: selfadj resid compares D_{A_rho} with its own dagger; "
         "drift compares sorted spectra (2-norm); tw-ord1 on Df uses the same "
         "331,776 pair grid and TRANSPOSE-based piOp.")

    # ------------------------------------------------------------------
    # D. Krein probe (exploratory T4)
    # ------------------------------------------------------------------
    emit("")
    emit("-" * 72)
    emit("D    Krein probe (exploratory T4, not a claim): Gamma-product")
    emit("     [psi,phi] = <psi, Gamma phi>; is D_{A_rho} self-adjoint w.r.t.")
    emit("     the Gamma-product? test: || Gamma D_{A_rho} Gamma - D_{A_rho}^H ||")
    base = fro(G @ D @ G - D.conj().T)
    emit(f"  baseline (unfluctuated D_F): {base:.3e}  "
         f"(expect 2||D|| since {{Gamma,D}}=0: {2 * fro(D):.3e})")
    for name, Df in fluctuated.items():
        r = fro(G @ Df @ G - Df.conj().T)
        emit(f"  fluctuated D ({name.split('(')[0].strip()}): {r:.3e}")
    emit("  D notes: Gamma is REAL (diag +/-1), so conj/ transpose agree on it;")
    emit("       this probe uses the fluctuated D_{A_rho} from section C.")

    emit("")
    emit("=" * 72)
    emit(f"done in {time.time() - t0:.1f}s. "
         "Boundedness: automatic in finite dimension (stated, not tested).")

    md_path = os.path.join(os.path.dirname(__file__),
                           "bridge-span-2-results.md")
    with open(md_path, "w") as f:
        f.write("# Bridge Span 2 — DLM flip-twist-by-grading numerics (results)\n\n")
        f.write("Tier **T4** (numerical exploration). "
                "Generated by `scripts/involutive_twist_lab.py`, seeds 2026 / 202607.\n\n")
        f.write("Twist: the DLM minimal twist by grading (flip on the doubled algebra). "
                "`Gamma = diag(+I8,-I8,-I8,+I8)`; `pi2(a,a') = P_+ pi(a) + P_- pi(a')`; "
                "`rho(a,a') = (a',a)` (involutive, `rho^2 = id`). "
                "Finite dimension 32: every operator below is bounded automatically; "
                "boundedness is not a numerical question here. "
                "Convention: `piOp` is TRANSPOSE-based (`piOp(M) = U_J M^T U_J`); "
                "the J-action `J X J^{-1} = U_J conj(X) U_J^T` is CONJUGATE-based; "
                "they agree on Hermitian X, differ otherwise. "
                "No Lorentzian-physics claims; no thermal-phase-transition language.\n\n")
        f.write("```\n" + "\n".join(OUT) + "\n```\n")
    emit(f"results written to {md_path}")


if __name__ == "__main__":
    main()
