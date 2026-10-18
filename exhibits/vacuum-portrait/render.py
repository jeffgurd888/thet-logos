#!/usr/bin/env python3
"""Renders for the Vacuum Portrait Exhibit. Reads results.json,
configs.npz, fields.npz (all produced by run_all.py). Dark gallery style.
Slice convention: (0,1)-plane plaquette density at x2 = x3 = 0, displayed
with x0 horizontal, x1 vertical."""
import json
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle

L = 6
BG = "#0b0b10"
FG = "#e8e6df"
GOLD = "#d9b45b"
plt.rcParams.update({
    "figure.facecolor": BG, "axes.facecolor": BG, "savefig.facecolor": BG,
    "text.color": FG, "axes.edgecolor": "#555555", "axes.labelcolor": FG,
    "xtick.color": FG, "ytick.color": FG, "font.size": 10,
    "axes.titlesize": 11, "figure.titlesize": 13,
})


def slice_fields(theta):
    """(density, phase) (L,L) grids [x0, x1] of the (0,1)-plane plaquettes
    at x2 = x3 = 0, corpus ordered plaquette convention."""
    t0 = theta[:, :, 0, 0, 0]
    t1 = theta[:, :, 0, 0, 1]
    ph = (t0 + np.roll(t1, -1, axis=0) - np.roll(t0, -1, axis=1) - t1)
    return 1.0 - np.cos(ph), np.angle(np.exp(1j * ph))


def show(ax, grid, **kw):
    return ax.imshow(grid.T, origin="lower", interpolation="nearest", **kw)


def main():
    R = json.load(open("results.json"))
    C = np.load("configs.npz")
    F = np.load("fields.npz")
    P = R["plaquette"]
    NS = R["prod_configs_per_beta"]

    def pq(b):
        v = P[str(b)]
        return v["mean"], v["sem"]

    # ------------------------------------------------ 1. beta = 0 portrait
    dens, phase = slice_fields(C["beta_0.0"])
    m0, e0 = pq(0.0)
    fig, axes = plt.subplots(1, 2, figsize=(11.5, 5.2))
    im = show(axes[0], dens, cmap="inferno", vmin=0, vmax=2)
    axes[0].set_title("plaquette action density  1 − cos θ_p")
    fig.colorbar(im, ax=axes[0], shrink=0.9)
    im = show(axes[1], phase, cmap="hsv", vmin=-np.pi, vmax=np.pi)
    axes[1].set_title("plaquette phase  arg U_p  (cyclic)")
    cb = fig.colorbar(im, ax=axes[1], shrink=0.9, ticks=[-np.pi, 0, np.pi])
    cb.ax.set_yticklabels(["−π", "0", "π"])
    for ax in axes:
        ax.set_xlabel("x⁰"); ax.set_ylabel("x¹")
    fig.suptitle("The β = 0 vacuum — U(1) on a 6⁴ torus, slice x² = x³ = 0")
    fig.text(0.5, 0.012,
             f"β = 0: product Haar — EXACT sampling, no MCMC.  N = {NS} configs.   "
             f"⟨Re U_p⟩ = {m0:+.5f} ± {e0:.5f}   (theory: exactly 0)",
             ha="center", family="monospace", fontsize=9)
    fig.tight_layout(rect=[0, 0.09, 1, 0.94])
    fig.savefig("portrait_beta0.png", dpi=150); plt.close(fig)

    # ------------------------------------------------ 2. beta sweep slices
    fig, axes = plt.subplots(1, 3, figsize=(13.5, 4.8))
    for ax, b in zip(axes, [0.5, 1.0, 2.0]):
        d, _ = slice_fields(C[f"beta_{b}"])
        im = show(ax, d, cmap="inferno", vmin=0, vmax=2)
        m, e = pq(b)
        ax.set_title(f"β = {b}\n⟨Re U_p⟩ = {m:.4f} ± {e:.4f} (ensemble)")
        ax.set_xlabel("x⁰"); ax.set_ylabel("x¹")
    fig.suptitle("Ordering with coupling — same slice, same color scale "
                 "(single configurations)")
    fig.tight_layout(rect=[0, 0.02, 0.93, 0.92])
    cax = fig.add_axes([0.945, 0.16, 0.011, 0.68])
    fig.colorbar(im, cax=cax, label="1 − cos θ_p")
    fig.savefig("portrait_sweep.png", dpi=150); plt.close(fig)

    # ------------------------------------------------ 3. plaquette curve
    betas = sorted(float(b) for b in P)
    ms = [P[str(b)]["mean"] for b in betas]
    es = [P[str(b)]["sem"] for b in betas]
    fig, ax = plt.subplots(figsize=(8.6, 6.2))
    ax.errorbar(betas, ms, yerr=es, fmt="o-", color=GOLD, ecolor="#888888",
                capsize=3, markersize=5, linewidth=1.2)
    ax.axhline(0, color="#666666", linestyle="--", linewidth=0.9)
    ax.axvspan(0.95, 1.05, color="#33415e", alpha=0.55)
    ax.annotate("β = 0 exact value: 0", xy=(0.02, 0.012), fontsize=9)
    ax.annotate("literature crossover\nβ ≈ 1.0 (T4) —\nshown, not claimed",
                xy=(1.09, 0.18), fontsize=9, color="#aebadd")
    ax.set_xlabel("β"); ax.set_ylabel("⟨Re U_p⟩")
    ax.set_title("Mean plaquette vs β — U(1), 6⁴ torus\n"
                 f"heatbath, {NS} configs/β after {R['therm_sweeps']} "
                 "thermalization sweeps; batch-means errors")
    ax.set_xlim(-0.08, 3.08); ax.grid(alpha=0.18)
    fig.tight_layout()
    fig.savefig("plaquette_curve.png", dpi=150); plt.close(fig)

    # ------------------------------------------------ 4. Wilson loops
    W = R["wilson"]
    fig, ax = plt.subplots(figsize=(8.6, 6.2))
    for b, mk in [(0.0, "s"), (1.0, "o"), (2.0, "^")]:
        ys = [W[str(b)][str(r)]["mean"] for r in (1, 2, 3)]
        ye = [W[str(b)][str(r)]["sem"] for r in (1, 2, 3)]
        ax.errorbar([1, 2, 3], ys, yerr=ye, fmt=mk + "-", capsize=3,
                    label=f"β = {b}", markersize=6, linewidth=1.2)
    ax.axhline(0, color="#666666", linestyle="--", linewidth=0.9)
    lines = ["measured ⟨Re W(R×R)⟩ ± SEM:"]
    for b in (0.0, 1.0, 2.0):
        row = "  ".join(f"R={r}: {W[str(b)][str(r)]['mean']:+.4f} ± "
                        f"{W[str(b)][str(r)]['sem']:.4f}" for r in (1, 2, 3))
        lines.append(f"β = {b}:  {row}")
    lines.append("exact at β = 0: 0 for all R ≥ 1 (fundamental rep)")
    ax.text(0.015, -0.14, "\n".join(lines), transform=ax.transAxes,
            family="monospace", fontsize=8.2, va="top")
    ax.set_xlabel("R (loop is R × R)"); ax.set_ylabel("⟨Re W⟩")
    ax.set_xticks([1, 2, 3]); ax.legend(facecolor=BG, edgecolor="#555555")
    ax.set_title("Square Wilson loops — U(1), 6⁴ torus")
    ax.grid(alpha=0.18)
    fig.tight_layout()
    fig.savefig("wilson_loops.png", dpi=150); plt.close(fig)

    # --------------------------------------- 5. difference portrait (amend.)
    d_th = F["slice_mean_1.0"]
    d_vac = F["slice_mean_3.0"]
    diff = d_th - d_vac
    vmax = float(np.abs(diff).max())
    mt, et = pq(1.0); mv, ev = pq(3.0)
    fig, ax = plt.subplots(figsize=(7.6, 6.6))
    im = show(ax, diff, cmap="RdBu_r", vmin=-vmax, vmax=vmax)
    fig.colorbar(im, ax=ax, shrink=0.92,
                 label="Δ density  (thermal − vacuum reference)")
    ax.set_xlabel("x⁰"); ax.set_ylabel("x¹")
    ax.set_title("The difference portrait — state minus vacuum\n"
                 "⟨density⟩ at β = 1.0  −  ⟨density⟩ at β = 3.0, same slice")
    fig.text(0.5, 0.012,
             f"volume ensemble means: density(β=1.0) = {1-mt:.4f} · "
             f"density(β=3.0) = {1-mv:.4f}\n"
             f"⟨Re U_p⟩: β=1.0 {mt:.4f} ± {et:.4f} · β=3.0 {mv:.4f} ± {ev:.4f}\n"
             f"difference range on slice: [{diff.min():+.4f}, {diff.max():+.4f}]\n"
             "β = 3.0 = vacuum reference: the ordered end of the sweep, "
             "not T = 0 itself\n"
             "single portraits are dominated by vacuum fluctuation;\n"
             "the subtraction isolates the excitation content",
             ha="center", family="monospace", fontsize=8.4)
    fig.tight_layout(rect=[0, 0.13, 1, 0.96])
    fig.savefig("portrait_difference.png", dpi=150); plt.close(fig)

    # --------------------------------------- 6. flux tube / fallback (amend.)
    FT = R["flux_tube"]
    fig, ax = plt.subplots(figsize=(7.6, 6.6))
    if FT["shipped"] == "reweighted flux tube":
        grid = F["flux_diff"]
        vmax = float(np.abs(grid).max())
        im = show(ax, grid, cmap="RdBu_r", vmin=-vmax, vmax=vmax)
        fig.colorbar(im, ax=ax, shrink=0.92,
                     label="Δ density  (loop inserted − no loop)")
        ax.add_patch(Rectangle((0.5, 0.5), 3, 3, fill=False,
                               edgecolor=GOLD, linewidth=2.0))
        ax.set_title("The content portrait — flux tube between static charges\n"
                     "action density conditioned on a 3×3 Wilson loop, β = 2.0")
        note = (f"method: reweighting ⟨D·ReW⟩/⟨ReW⟩ − ⟨D⟩ on the β = 2.0 "
                f"ensemble ({FT['n_configs']} configs)\n"
                f"⟨Re W(3×3)⟩ = {FT['W_mean']:+.4f} ± {FT['W_sem']:.4f}   ·   "
                f"peak |Δ| = {FT['diff_peak_abs']:.4f} vs median SEM "
                f"{FT['diff_median_sem']:.4f} (noise floor)\n"
                "gold outline: the loop (enclosed plaquettes), schematic "
                "position — static charges sit at its ends")
    else:
        d1, _ = slice_fields(C["beta_1.0"])
        grid = d1 - d_vac
        vmax = float(np.abs(grid).max())
        im = show(ax, grid, cmap="RdBu_r", vmin=-vmax, vmax=vmax)
        fig.colorbar(im, ax=ax, shrink=0.92,
                     label="Δ density  (one thermal config − vacuum reference)")
        ax.set_title("Difference portrait, single configuration\n"
                     "one β = 1.0 configuration − β = 3.0 ensemble average")
        note = (f"FALLBACK shipped — reweighted flux tube was noise: peak "
                f"|Δ| {FT['diff_peak_abs']:.4f} vs median SEM "
                f"{FT['diff_median_sem']:.4f}, ⟨Re W(3×3)⟩ = "
                f"{FT['W_mean']:+.4f} ± {FT['W_sem']:.4f} at β = 2.0.\n"
                "a null result is a result: no flux tube is claimed. "
                "See EXHIBIT.md.")
    ax.set_xlabel("x⁰"); ax.set_ylabel("x¹")
    fig.text(0.5, 0.015, note, ha="center", family="monospace", fontsize=8.4)
    fig.tight_layout(rect=[0, 0.09, 1, 0.96])
    fig.savefig("portrait_flux_tube.png", dpi=150); plt.close(fig)

    print("renders written: portrait_beta0.png portrait_sweep.png "
          "plaquette_curve.png wilson_loops.png portrait_difference.png "
          "portrait_flux_tube.png")


if __name__ == "__main__":
    main()
