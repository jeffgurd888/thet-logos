#!/usr/bin/env python3
"""
Vacuum Portrait Exhibit — U(1) lattice gauge theory on a 6^4 torus.

Mirrors the corpus definitions (thet-logos, Pitch 4 Stage 0/1a):
  - Links: U(x,mu) = exp(i*theta(x,mu)), theta in [0, 2pi), x in (ZMod 6)^4,
    mu in Fin 4.                     [LatticeGauge.lean: Config = (Lambda x Fin 4) -> G]
  - Plaquette (ordered, counterclockwise from (x,mu)):
        U_p(x,mu,nu) = U(x,mu) * U(sigma_mu x, nu)
                       * (U(sigma_nu x, mu))^{-1} * (U(x,nu))^{-1}
                                     [LatticeGauge.lean, plaquette convention]
  - Wilson action (Circle fundamental rep, d = 1):
        S_beta = beta * sum_{x, mu<nu} (1 - Re U_p(x,mu,nu))
  - Gibbs measure: Z^{-1} * exp(-S_beta) against product Haar on links.
                                     [LatticeCorrelations.lean: gibbsMeasure]

Sampling: beta = 0 is EXACT product Haar (independent uniform phases).
beta > 0: heatbath (exact per-link von Mises conditional), checkerboard
by parity of sum of coordinates other than mu (links updated in a class
share no plaquette among their conditionals).

Reproduce:  python3 run_all.py     (fixed seeds; writes PNGs + results.json)
"""
import json
import time
import numpy as np

L = 6                       # torus extent per direction; sites = L^4 = 1296
ND = 4                      # directions
PLANES = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]  # mu < nu
SEED = 20261018             # fixed master seed (recorded in results.json)

THERM_SWEEPS = 300          # discarded per beta > 0
PROD_SWEEPS = 3000          # equilibrated configs recorded per beta (1/sweep)
BATCH = 100                 # batch-means block length (sweeps) for errors

BETAS_CURVE = [0.0, 0.25, 0.5, 0.6, 0.7, 0.85, 1.0, 1.15, 1.3, 1.5,
               1.75, 2.0, 2.5, 3.0]                       # 14 points in [0, 3]
BETAS_RENDER = [0.5, 1.0, 2.0]        # configs saved for slice portraits
BETAS_WILSON = [0.0, 1.0, 2.0]
WILSON_R = [1, 2, 3]

# ---------------------------------------------------------------- lattice ops

def shifted(T, mu, k):
    """Value at x + k*e_mu, for the direction-mu slice array T (site grid)."""
    return np.roll(T, -k, axis=mu)


def plaquette_phases(theta):
    """theta: (L,L,L,L,4) link phases. Returns (L,L,L,L,6) plaquette phases
    for the planes in PLANES, corpus ordered convention."""
    out = np.empty(theta.shape[:4] + (len(PLANES),))
    for pi, (mu, nu) in enumerate(PLANES):
        t_mu = theta[..., mu]
        t_nu = theta[..., nu]
        out[..., pi] = (t_mu + shifted(t_nu, mu, 1)
                        - shifted(t_mu, nu, 1) - t_nu)
    return out


def plaquette_cos_mean(theta):
    return float(np.cos(plaquette_phases(theta)).mean())


def _parity_masks():
    """For each direction mu, mask over the site grid of parity class of
    sum_{rho != mu} x_rho (mod 2). Links in one class never appear in each
    other's heatbath staple, so a class can be updated simultaneously."""
    grids = np.indices((L,) * ND)
    total = sum(grids)
    masks = {}
    for mu in range(ND):
        par = (total - grids[mu]) % 2
        masks[mu] = (par == 0, par == 1)
    return masks


MASKS = _parity_masks()


def _staple_z(theta, mu):
    """Complex staple sum z for links (x, mu): the conditional of theta(x,mu)
    is proportional to exp(beta * Re[exp(i*theta) * z]).
    Derived from the 2*(ND-1) plaquettes containing the link:
      phi(x,mu,nu)   = +theta + r+_nu,  r+ = T(x+mu,nu) - T(x+nu,mu) - T(x,nu)
      phi(x-nu,mu,nu)= -theta + r-_nu,  r- = T(x-nu,mu) + T(x+mu-nu,nu) - T(x-nu,nu)
    sum cos(phi) = Re[exp(i*theta)*(A + conj(B))], A=sum exp(i r+), B=sum exp(i r-).
    """
    A = np.zeros(theta.shape[:4], dtype=complex)
    B = np.zeros(theta.shape[:4], dtype=complex)
    t_mu = theta[..., mu]
    for nu in range(ND):
        if nu == mu:
            continue
        t_nu = theta[..., nu]
        rp = shifted(t_nu, mu, 1) - shifted(t_mu, nu, 1) - t_nu
        rm = (shifted(t_mu, nu, -1)
              + np.roll(shifted(t_nu, mu, 1), 1, axis=nu)
              - shifted(t_nu, nu, -1))
        A += np.exp(1j * rp)
        B += np.exp(1j * rm)
    return A + np.conj(B)


def heatbath_sweep(theta, beta, rng):
    for mu in range(ND):
        for cls in (0, 1):
            mask = MASKS[mu][cls]
            z = _staple_z(theta, mu)
            kappa = beta * np.abs(z)
            mean_dir = -np.angle(z)
            new = rng.vonmises(mean_dir[mask], kappa[mask])
            theta[..., mu][mask] = np.mod(new, 2 * np.pi)
    return theta


def wilson_loops(theta):
    """Mean Re W(R x R) over all sites and all 6 planes, for R in WILSON_R.
    Phase convention: counterclockwise loop, corpus path order."""
    res = {}
    for R in WILSON_R:
        acc = 0.0
        for (mu, nu) in PLANES:
            t_mu = theta[..., mu]
            t_nu = theta[..., nu]
            phase = np.zeros(theta.shape[:4])
            for i in range(R):
                phase += np.roll(t_mu, -i, axis=mu)                    # bottom
                phase -= np.roll(np.roll(t_mu, -i, axis=mu), -R, axis=nu)  # top
            for j in range(R):
                phase += np.roll(np.roll(t_nu, -R, axis=mu), -j, axis=nu)  # right
                phase -= np.roll(t_nu, -j, axis=nu)                     # left
            acc += np.cos(phase).mean()
        res[R] = acc / len(PLANES)
    return res


# ------------------------------------------------------- amendment fields
# Jeff's amendment: difference portraits. Same sampler, same lattice.

def slice_density(theta):
    """(0,1)-plane plaquette action density 1 - cos(phi_p) on the slice
    x2 = x3 = 0, as a (L, L) grid over (x0, x1)."""
    ph = plaquette_phases(theta)
    return 1.0 - np.cos(ph[:, :, 0, 0, 0])


LOOP_ORIGIN = (1, 1)   # (x0, x1) of the flux-tube loop corner, in the slice
LOOP_RT = (3, 3)       # R (dir 0) x T (dir 1)


def loop_reW(theta):
    """Re W of the single rectangular Wilson loop of the flux-tube panel:
    R=3 (dir 0) by T=3 (dir 1), corner at LOOP_ORIGIN, in the x2=x3=0 plane.
    Corpus path order (counterclockwise)."""
    a = theta[:, :, 0, 0, 0]   # dir-0 links over (x0, x1)
    b = theta[:, :, 0, 0, 1]   # dir-1 links over (x0, x1)
    x0, x1 = LOOP_ORIGIN
    R, T = LOOP_RT
    ph = 0.0
    for i in range(R):
        ph += a[(x0 + i) % L, x1]
        ph -= a[(x0 + i) % L, (x1 + T) % L]
    for j in range(T):
        ph += b[(x0 + R) % L, (x1 + j) % L]
        ph -= b[x0, (x1 + j) % L]
    return float(np.cos(ph))


# ---------------------------------------------------------------- statistics

def batch_sem(series, batch=BATCH):
    """Batch-means standard error of the mean for a (possibly correlated)
    time series."""
    x = np.asarray(series, dtype=float)
    n = (len(x) // batch) * batch
    if n == 0:
        return float(x.mean()), float('nan')
    blocks = x[:n].reshape(-1, batch).mean(axis=1)
    return float(x.mean()), float(blocks.std(ddof=1) / np.sqrt(len(blocks)))


# ---------------------------------------------------------------- main run

def run():
    t0 = time.time()
    results = {"seed": SEED, "L": L, "therm_sweeps": THERM_SWEEPS,
               "prod_configs_per_beta": PROD_SWEEPS, "plaquette": {},
               "wilson": {}, "saved_configs": {}}
    rng_master = np.random.default_rng(SEED)
    child_seeds = rng_master.integers(0, 2**63 - 1, size=64)
    seed_iter = iter(child_seeds.tolist())

    saved = {}       # beta -> theta config (for renders)
    plaq_series = {} # beta -> per-config plaquette means
    slice_sum = {}   # beta -> summed slice density grid (amendment panels)

    # ---- beta = 0: EXACT product Haar sampling (no MCMC)
    rng0 = np.random.default_rng(int(next(seed_iter)))
    series0 = []
    wilson_acc = {R: [] for R in WILSON_R}
    theta = None
    ss0 = np.zeros((L, L))
    for c in range(PROD_SWEEPS):
        theta = rng0.uniform(0.0, 2 * np.pi, size=(L,) * ND + (ND,))
        series0.append(plaquette_cos_mean(theta))
        ss0 += slice_density(theta)
        if c < 600:  # Wilson at beta=0 on 600 exact configs (plenty: SEM ~1e-3)
            w = wilson_loops(theta)
            for R in WILSON_R:
                wilson_acc[R].append(w[R])
    slice_sum[0.0] = ss0
    m0, e0 = batch_sem(series0)
    results["plaquette"]["0.0"] = {"mean": m0, "sem": e0}
    plaq_series[0.0] = series0
    results["wilson"]["0.0"] = {str(R): {"mean": float(np.mean(v)),
                                         "sem": float(np.std(v, ddof=1) / np.sqrt(len(v)))}
                                for R, v in wilson_acc.items()}
    results["wilson_n_configs"] = {str(b): (600 if b == 0.0 else PROD_SWEEPS)
                                   for b in BETAS_WILSON}
    saved[0.0] = theta.copy()
    print(f"[beta=0.00] exact Haar: <Re U_p> = {m0:+.5f} +- {e0:.5f} "
          f"(theory 0); Wilson R=1 {results['wilson']['0.0']['1']['mean']:+.5f}", flush=True)

    # ---- beta > 0: heatbath, ascending beta, continuation in beta
    for beta in BETAS_CURVE[1:]:
        rng = np.random.default_rng(int(next(seed_iter)))
        for _ in range(THERM_SWEEPS):
            theta = heatbath_sweep(theta, beta, rng)
        series = []
        wseries = {R: [] for R in WILSON_R}
        ss = np.zeros((L, L))
        flux_batches = []   # beta=2.0 only: per-batch (sumW, sumDW, sumD, n)
        bW, bDW, bD, bn = 0.0, np.zeros((L, L)), np.zeros((L, L)), 0
        for sweep in range(PROD_SWEEPS):
            theta = heatbath_sweep(theta, beta, rng)
            series.append(plaquette_cos_mean(theta))
            D = slice_density(theta)
            ss += D
            if beta == 2.0:
                W = loop_reW(theta)
                bW += W; bDW += D * W; bD += D; bn += 1
                if bn == BATCH:
                    flux_batches.append((bW, bDW.copy(), bD.copy(), bn))
                    bW, bDW, bD, bn = 0.0, np.zeros((L, L)), np.zeros((L, L)), 0
            if beta in BETAS_WILSON:
                w = wilson_loops(theta)
                for R in WILSON_R:
                    wseries[R].append(w[R])
        slice_sum[beta] = ss
        if beta == 2.0:
            results["flux_batches"] = [
                {"sumW": sW, "sumDW": sDW.tolist(), "sumD": sD.tolist(), "n": n}
                for (sW, sDW, sD, n) in flux_batches]
        m, e = batch_sem(series)
        results["plaquette"][f"{beta}"] = {"mean": m, "sem": e}
        plaq_series[beta] = series
        if beta in BETAS_WILSON:
            results["wilson"][f"{beta}"] = {
                str(R): {"mean": float(np.mean(v)),
                         "sem": float(np.std(v, ddof=1) / np.sqrt(len(v)))}
                for R, v in wseries.items()}
        if beta in BETAS_RENDER:
            saved[beta] = theta.copy()
        print(f"[beta={beta:4.2f}] heatbath: <Re U_p> = {m:+.5f} +- {e:.5f}", flush=True)

    # ---- amendment analysis: slice ensemble means + flux-tube reweighting
    slice_means = {b: s / PROD_SWEEPS for b, s in slice_sum.items()}
    fb = results.pop("flux_batches")
    nb = len(fb)
    sumW = sum(x["sumW"] for x in fb)
    sumDW = sum(np.array(x["sumDW"]) for x in fb)
    sumD = sum(np.array(x["sumD"]) for x in fb)
    ntot = sum(x["n"] for x in fb)
    diff_global = sumDW / sumW - sumD / ntot
    batch_diffs = np.array([np.array(x["sumDW"]) / x["sumW"]
                            - np.array(x["sumD"]) / x["n"] for x in fb])
    sem_grid = batch_diffs.std(axis=0, ddof=1) / np.sqrt(nb)
    batch_W = np.array([x["sumW"] / x["n"] for x in fb])
    W_mean = float(sumW / ntot)
    W_sem = float(batch_W.std(ddof=1) / np.sqrt(nb))
    peak = float(np.abs(diff_global).max())
    med_sem = float(np.median(sem_grid))
    ship = bool(peak > 3 * med_sem and abs(W_mean) > 5 * W_sem)
    results["flux_tube"] = {
        "loop": "R=3 (dir 0) x T=3 (dir 1), corner (1,1), x2=x3=0 plane, beta=2.0",
        "method": "reweighting: <D>_W - <D> = <D*ReW>/<ReW> - <D> on the beta=2.0 ensemble",
        "W_mean": W_mean, "W_sem": W_sem,
        "diff_peak_abs": peak, "diff_median_sem": med_sem,
        "diff_range": [float(diff_global.min()), float(diff_global.max())],
        "shipped": "reweighted flux tube" if ship else "FALLBACK single-config difference (reweighted signal/noise too low)",
        "n_configs": ntot, "n_batches": nb}
    print(f"[flux tube] <ReW(3x3)> = {W_mean:+.4f} +- {W_sem:.4f}; "
          f"diff peak {peak:.4f} vs median SEM {med_sem:.4f} -> "
          f"{results['flux_tube']['shipped']}", flush=True)
    np.savez_compressed(
        "fields.npz",
        **{f"slice_mean_{b}": slice_means[b] for b in slice_means},
        flux_diff=diff_global, flux_sem=sem_grid)

    results["runtime_sec"] = round(time.time() - t0, 1)
    np.savez_compressed("configs.npz",
                        **{f"beta_{b}": saved[b] for b in saved})
    with open("results.json", "w") as f:
        json.dump(results, f, indent=1)
    print(f"sampling done in {results['runtime_sec']}s; "
          f"configs saved for beta in {sorted(saved)}", flush=True)
    return results, saved


if __name__ == "__main__":
    run()
    import subprocess, sys
    subprocess.run([sys.executable, "render.py"], check=True)
