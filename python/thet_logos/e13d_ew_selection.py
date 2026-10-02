"""Phase 5 (reframed): electroweak sector mapping -- SELECTION theorem.

Tier T4 numerical probe. LOCAL -- not pushed. Parent: E13-D
(python/thet_logos/engine13d_components.py).

REFRAMING (law, from the audit): this is a SELECTION theorem, not a
discovery. The value 228.8 GeV = Yu x VEV is INHERITED FROM INPUT
(Y_PHYS in finite_thermal_flow.py, VEV = 246.0). What is tested here is
whether the Connes distance functional STRUCTURALLY locks onto the
heaviest-Yukawa block of D_F: d(C,H)^-1 = max(Y) x VEV across Yukawa
shuffles that move and rescale the maximum. Language implying the top
mass was predicted is FORBIDDEN (circular).

Experiment:
  P_EW  = explicit projector isolating the C(+)H probe sector; algebraic
          definition verified numerically.
  For each Yukawa configuration Y: rebuild D_F(Y), recompute d(C,H) with
  the E13-D solver, check 1/d == max(Y)*VEV (3% tolerance; solver gives
  rigorous lower bounds, so 1/d is an upper bracket -- tight per E13-D).
  Knockouts: max-only and max-removed D_F variants pin the mechanism to
  the heaviest block.
  FAIL = distance does not track max(Y)*VEV -> failed selection
  hypothesis, reported not rescued.

QUARANTINE WALL (binding): no spectral-action derivation (frozen per
ledger, SA-4), no finite->continuum, no d_spec->4, no clock-time, no
Lorentzian/GR, no experimental prediction. Component labels are
algebraic origins only.
"""

import numpy as np
import scipy.linalg as la

from .common import DF_oneGen, DIM
from .finite_thermal_flow import Y_PHYS, VEV
from . import engine13_rsd as e13
from . import engine13d_components as e13d

SEED = 20261305
TOL_TRACK = 0.03   # 1/d must match max(Y)*VEV within 3%
TOL_UNIFORM = 0.01  # across H samples

YUK_POSITIONS = ("Ynu", "Ye", "Yu", "Yd")


def build_DF_for_Y(Y):
    D = DF_oneGen(Y["Ynu"], Y["Ye"], Y["Yu"], Y["Yd"]) * VEV
    assert np.max(np.abs(D - D.conj().T)) < 1e-12, "D_F must be Hermitian"
    return D


def projector_checks():
    """P_EW: explicit projector isolating the C(+)H probe sector.

    Algebraic definition: z = (1, I_2, 0_3) in A_F is central; then
      pi_full(z) = Q_top (+) P_EW (+) Q_tail
    with Q_top supported on dims {0,1,8,9} (Option-A electroweak block),
    P_EW = diag(0_16, I_8, 0_8) on probe dims 16..23 (u1*I_4 (+) I_2(x)q),
    Q_tail = diag(0_30, I_2) (probe trailing u1 block, dims 30..31).
    Verified numerically below.
    """
    lines = []
    P_EW = np.zeros((DIM, DIM), complex)
    P_EW[16:24, 16:24] = np.eye(8)
    assert np.allclose(P_EW @ P_EW, P_EW), "not idempotent"
    assert np.allclose(P_EW, P_EW.conj().T), "not Hermitian"
    lines.append("[P5/P_EW] diag(0_16, I_8, 0_8): idempotent + Hermitian")

    z = (1.0 + 0j, np.eye(2, dtype=complex), np.zeros((3, 3), complex))
    Pz = e13d.pi_full(z)
    Q_top = np.zeros((DIM, DIM), complex)
    for i in (0, 1, 8, 9):
        Q_top[i, i] = 1.0
    Q_tail = np.zeros((DIM, DIM), complex)
    Q_tail[30, 30] = Q_tail[31, 31] = 1.0
    assert np.allclose(Pz, Q_top + P_EW + Q_tail), \
        "pi_full(z) != Q_top + P_EW + Q_tail"
    lines.append("[P5/P_EW] pi_full((1,I_2,0)) = Q_top + P_EW + Q_tail "
                 "verified (Q_top: dims {0,1,8,9}; Q_tail: dims {30,31})")
    # Ran(P_EW) = joint support of the C and H pure-state samples
    rng = np.random.default_rng(e13d.SEED)
    states = e13d.pure_state_sample(rng)
    for idx in [0] + list(range(1, 1 + e13d.N_H)):
        rho, lab = states[idx]
        supp = np.diag(rho).real > 0.5
        assert np.all(np.where(supp)[0] >= 16) and \
            np.all(np.where(supp)[0] < 24), \
            f"state {lab} not supported in Ran(P_EW)"
    lines.append(f"[P5/P_EW] C + {e13d.N_H} H pure states supported in "
                 f"Ran(P_EW) (dims 16..23)")
    lines.append("[P5/P_EW] PASS: projector constructed + algebraically "
                 "characterized")
    return "PASS", lines, P_EW


def setup_for_Y(Y, B, states):
    """Rebuild D_F(Y), commutator data, and E13-D solver globals."""
    D = build_DF_for_Y(Y)
    Q, K = e13.commutator_data(D, B)
    Lk = np.stack([D @ H - H @ D for H in B])
    e13d._D, e13d._B, e13d._Q, e13d._K = D, B, Q, K
    e13d._MATS = np.tensordot(Q, Lk, axes=([0], [0]))
    e13d._R = Q.shape[1]
    e13d._RHO = [rho for rho, _ in states]
    return D, Q, K


def ch_distances(h_idx, s0):
    """d(C, H[h]) for h in h_idx via the E13-D pair solver (serial)."""
    out = []
    for j in h_idx:
        i, j, d, d12, d21 = e13d._pair_worker((0, j, s0))
        assert np.isfinite(d) and d > 0, \
            f"C-H pair ({i},{j}) not finite-nonzero: {d}"
        out.append(d)
    return out


def main():
    out = []
    print("[P5] Phase 5 (reframed): electroweak SELECTION theorem", flush=True)
    print("[P5] quarantine: no spectral action (frozen SA-4), no continuum, "
          "no clock, no Lorentzian/GR, no predictions", flush=True)
    print("[P5] circularity firewall: 228.8 GeV = Yu x VEV is INPUT "
          "(Y_PHYS, VEV=246); only the SELECTION is tested", flush=True)

    v, lines, P_EW = projector_checks()
    for ln in lines:
        print(ln, flush=True)
        out.append(ln)

    # D-independent data: order-unit basis + pure-state sample
    B = e13d.selfadjoint_basis_full()
    rng = np.random.default_rng(e13d.SEED)
    states = e13d.pure_state_sample(rng)
    rho_c = states[0][0]
    h_idx = [1, 2, 7]
    print(f"[P5] order-unit basis dim m={len(B)}; H samples {h_idx}",
          flush=True)

    configs = [
        ("baseline Y_PHYS", dict(Y_PHYS)),
        ("democratic 0.3", {"Ynu": 0.3, "Ye": 0.3, "Yu": 0.3, "Yd": 0.3}),
        ("max@Ye", {"Ynu": 0.0, "Ye": 0.93, "Yu": 0.010, "Yd": 0.024}),
        ("max@Ynu", {"Ynu": 0.93, "Ye": 0.010, "Yu": 0.010, "Yd": 0.024}),
        ("max lowered 0.05", {"Ynu": 0.0, "Ye": 0.010, "Yu": 0.05,
                              "Yd": 0.024}),
        ("max@Yd 0.5", {"Ynu": 0.0, "Ye": 0.010, "Yu": 0.010, "Yd": 0.5}),
        ("KO max-only", {"Ynu": 0.0, "Ye": 0.0, "Yu": 0.93, "Yd": 0.0}),
        ("KO max-removed", {"Ynu": 0.0, "Ye": 0.010, "Yu": 0.0, "Yd": 0.024}),
    ]
    results = []
    failed = []
    for ci, (name, Y) in enumerate(configs):
        pred = max(Y[k] for k in YUK_POSITIONS) * VEV
        D, Q, K = setup_for_Y(Y, B, states)
        ds = ch_distances(h_idx, SEED + 1000 * ci)
        inv = [1.0 / d for d in ds]
        uni = (max(inv) - min(inv)) / np.mean(inv)
        rel = [abs(v - pred) / pred for v in inv]
        ok = all(r < TOL_TRACK for r in rel) and uni < TOL_UNIFORM
        tag = "PASS" if ok else "FAIL"
        if not ok:
            failed.append(name)
        line = (f"[P5/sel] {name:16s} maxY*VEV={pred:8.3f} GeV | "
                f"1/d(C,H)={[f'{v:.4f}' for v in inv]} GeV | "
                f"relerr={[f'{r:.2%}' for r in rel]} -> {tag}")
        print(line, flush=True)
        out.append(line)
        results.append((name, pred, inv, tag))

    # mechanism diagnostic on baseline: which Yukawa block binds?
    print("[P5/mech] binding-block diagnostic (baseline Y_PHYS):", flush=True)
    D, Q, K = setup_for_Y(dict(Y_PHYS), B, states)
    h_rho = states[h_idx[0]][0]
    Lk = np.stack([D @ H - H @ D for H in B])
    Mats = np.tensordot(Q, Lk, axes=([0], [0]))
    r = Q.shape[1]
    best, uu = e13d._one_direction(D, B, Q, K, Mats, r, rho_c, h_rho,
                                   seed=[SEED, 777])
    if uu is not None:
        Atilde = [sum(Q[j, k] * B[j] for j in range(len(B)))
                  for k in range(r)]
        Astar = sum(uu[k] * Atilde[k] for k in range(r))
        Cmat = D @ Astar - Astar @ D
        # the (24..32, 16..24) block carries the Yukawa couplings
        Blk = Cmat[24:32, 16:24]
        Yv = np.array([Y_PHYS[k] for k in YUK_POSITIONS])
        Y8 = np.array([Yv[0], Yv[1], Yv[2], Yv[3], Yv[2], Yv[3], Yv[2],
                       Yv[3]]) * VEV
        entries = []
        for a in range(8):
            for b in range(8):
                entries.append((abs(Blk[a, b]), a, b, Y8[a], Y8[b]))
        entries.sort(reverse=True)
        for mag, a, b, ya, yb in entries[:6]:
            line = (f"[P5/mech]   |[D,A*]| block entry ({a},{b}): "
                    f"{mag:.4f}  Yukawa(a)={ya:.2f} Yukawa(b)={yb:.2f} GeV")
            print(line, flush=True)
            out.append(line)
        # overlap of the binding block with the max-Yukawa positions
        maxpos = [p for p in range(8) if abs(Y8[p] - Y8.max()) < 1e-9]
        topwt = sum(m for m, a, b, ya, yb in entries[:8]
                    if a in maxpos or b in maxpos)
        totwt = sum(m for m, a, b, ya, yb in entries[:8])
        line = (f"[P5/mech] max-Yukawa positions {maxpos}: top-8 entry "
                f"weight fraction = {topwt / max(totwt, 1e-300):.3f}")
        print(line, flush=True)
        out.append(line)
    else:
        print("[P5/mech] no maximizing direction found; diagnostic skipped",
              flush=True)

    # forbidden-claim scan
    blob = "\n".join(out).lower()
    leaks = []
    for w in ["continuum", "lorentzian", "experimental prediction",
              "spectral action", "forced physical identity", "predicts the",
              "prediction of the top"]:
        if w in blob:
            for ln in out:
                ll = ln.lower()
                if w in ll and "quarantine" not in ll and "frozen" not in ll \
                        and "no " not in ll.split(w)[0][-20:]:
                    leaks.append((w, ln))
    if leaks:
        print("[P5] FORBIDDEN-CLAIM LEAK:", leaks, flush=True)
        return 1
    print("[P5] quarantine scan: clean", flush=True)

    print("=" * 60, flush=True)
    if failed:
        print(f"[P5] SELECTION-FAILED for: {failed}", flush=True)
        print("[P5] The selection hypothesis does NOT hold -- reported, "
              "not rescued.", flush=True)
        return 1
    print("[P5] SELECTION-CONFIRMED: 1/d(C,H) = max(Y)*VEV across all "
          f"{len(configs)} configurations (shuffles + knockouts)", flush=True)
    print("[P5] STATUS: selection theorem numerically witnessed (T4); "
          "value inherited from input, selection structural", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
