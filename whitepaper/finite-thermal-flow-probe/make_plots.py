"""Plots for the finite thermal-flow probe results (T4)."""
import json
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

RDIR = "/home/hatch/workspace/thet-logos/whitepaper/finite-thermal-flow-probe/"
with open(RDIR + "results.json") as f:
    res = json.load(f)

# 1. per-sector response, physical Yukawas
p = res["physical"]
names = ["u(1)", "su(2)", "su(3)"]
vals = [p["u1"]["g_GeV2"], p["su2"]["g_GeV2"], p["su3"]["g_GeV2"]]
fig, ax = plt.subplots(figsize=(6, 4))
bars = ax.bar(names, vals, color=["#888888", "#2a7fbf", "#bbbbbb"])
bars[2].set_hatch("///")
ax.set_ylabel("g = || ad_{D_F^2} |_sector ||  [GeV^2]")
ax.set_title("Finite Gibbs-flow response per represented gauge sector")
ax.text(1, vals[1] * 1.05, f"{vals[1]:.4g} = |Ye^2-Ynu^2| v^2",
        ha="center", fontsize=9)
ax.text(2, max(vals[1] * 0.03, 1e-9), "embedding artifact:\npi kills M_3(C)",
        ha="center", fontsize=8, style="italic")
ax.set_yscale("log")
ax.set_ylim(1e-2, vals[1] * 20)
fig.tight_layout()
fig.savefig(RDIR + "sector_response.png", dpi=110)
plt.close(fig)

# 2. linearity: modular speed vs temperature (log-log, slope 1)
lin = res["beta_linearity"]
T = np.array([d["T_GeV"] for d in lin])
sp = np.array([d["speed_su2_GeV"] for d in lin])
fig, ax = plt.subplots(figsize=(6, 4))
ax.loglog(T, sp, "o-", label="measured speed = beta * g_su2")
ax.loglog(T, sp[0] * (T[0] / T), "k--", label="slope -1 reference")
ax.set_xlabel("T = 1/beta  [GeV]")
ax.set_ylabel("su(2) modular speed [GeV]")
ax.set_title("Modular speed is exactly linear in beta (ratios T-independent)")
ax.legend(fontsize=9)
fig.tight_layout()
fig.savefig(RDIR + "beta_linearity.png", dpi=110)
plt.close(fig)

# 3. shuffle control: measured vs predicted su(2) response
sh = res["control_shuffles"]
meas = [s["su2_g"] for s in sh] + [p["su2"]["g_GeV2"]]
pred = [s["su2_predicted"] for s in sh] + \
    [abs(res["Yukawas"]["Ynu"]**2 - res["Yukawas"]["Ye"]**2)
     * res["VEV_GeV"]**2]
labels = [f"shuffle {s['seed']}" for s in sh] + ["physical"]
fig, ax = plt.subplots(figsize=(6, 4))
ax.loglog(pred, meas, "o", ms=8)
lo = min(min(pred), min(meas)) * 0.5
hi = max(max(pred), max(meas)) * 2
ax.loglog([lo, hi], [lo, hi], "k--", label="measured = predicted")
for x, y, lb in zip(pred, meas, labels):
    ax.text(x * 1.15, y, lb, fontsize=8)
ax.set_xlabel("predicted |Ynu^2 - Ye^2| v^2  [GeV^2]")
ax.set_ylabel("measured su(2) g  [GeV^2]")
ax.set_title("Shuffle control: response tracks doublet mass splitting exactly")
ax.legend(fontsize=9)
fig.tight_layout()
fig.savefig(RDIR + "shuffle_control.png", dpi=110)
plt.close(fig)
print("plots written")
