"""TikTok: 'Luci's Light' — the verified luciferase reaction as digital chemistry.

Real data only:
  Reaction: D-luciferin + ATP + O2 -> oxyluciferin + AMP + PPi + CO2 + light
  Luciferin: C11H8N2O3S2 (26 atoms) | ATP: C10H16N5O13P3 (37 atoms) | O2: 2 atoms
  Photon: 560 nm (yellow-green), E = hc/lambda = 3.55e-19 J = 2.21 eV (T4 verified)
  Catalyst: luciferase + Mg2+ (labeled, not simulated)
NO kinetics invented. No Dirac-operator chemistry (that path killed as category error).
"""
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
from matplotlib.patches import Circle

W, H, DPI = 720, 1280, 100
FPS, DUR = 30, 16.0
NFRAMES = int(FPS * DUR)
rng = np.random.default_rng(42)

# atom colors (CPK-ish): C dark gray, H white, N blue, O red, S yellow, P orange
ACOL = {"C": "#555555", "H": "#eeeeee", "N": "#3b6fe0", "O": "#e03131",
        "S": "#f2c200", "P": "#ff8c1a", "Mg": "#7CFC00"}
ARAD = {"C": 0.030, "H": 0.020, "N": 0.030, "O": 0.030, "S": 0.036, "P": 0.038, "Mg": 0.026}

def mol_atoms(formula):
    atoms = []
    for el, n in formula:
        atoms.extend([el] * n)
    return atoms

LUCIFERIN = [("C", 11), ("H", 8), ("N", 2), ("O", 3), ("S", 2)]
ATP = [("C", 10), ("H", 16), ("N", 5), ("O", 13), ("P", 3)]

def blob_positions(atoms, cx, cy, spread, seed):
    r = np.random.default_rng(seed)
    n = len(atoms)
    pos = []
    for i in range(n):
        a = 2 * np.pi * i / max(n, 1) + r.uniform(-0.3, 0.3)
        rad = spread * (0.55 + 0.45 * r.random())
        pos.append((cx + rad * np.cos(a), cy + rad * np.sin(a) * 0.5625))
    return pos

luc_atoms = mol_atoms(LUCIFERIN)
atp_atoms = mol_atoms(ATP)
luc_pos0 = blob_positions(luc_atoms, 0.28, 0.55, 0.20, 1)
atp_pos0 = blob_positions(atp_atoms, 0.72, 0.55, 0.22, 2)
o2_pos0 = [(0.48, 0.78), (0.54, 0.78)]

fig = plt.figure(figsize=(W / DPI, H / DPI), dpi=DPI, facecolor="black")

def ease(t):
    t = min(1.0, max(0.0, t))
    return t * t * (3 - 2 * t)

def draw_mol(ax, atoms, pos, alpha, scale=1.0):
    for (el, (x, y)) in zip(atoms, pos):
        c = Circle((x, y), ARAD[el] * scale, color=ACOL[el], alpha=alpha, zorder=3)
        ax.add_patch(c)

def draw(t):
    fig.clear()
    ax = fig.add_axes([0, 0, 1, 1], facecolor="black")
    ax.set_xlim(0, 1); ax.set_ylim(0, 1); ax.axis("off")
    sx, sy = rng.random(100), rng.random(100)
    ax.scatter(sx, sy, s=2, c="white", alpha=0.2)

    if t < 3.0:
        a = min(1.0, t / 1.0)
        ax.text(0.5, 0.58, "a firefly makes light", ha="center", fontsize=40,
                color="white", weight="bold", alpha=a)
        ax.text(0.5, 0.50, "without heat", ha="center", fontsize=40,
                color="#adff2f", weight="bold", alpha=a)
        ax.text(0.5, 0.40, "this is the chemistry", ha="center", fontsize=24,
                color="#aaaaaa", alpha=a)
    elif t < 8.0:
        # molecules assemble
        lt = ease((t - 3.0) / 2.0)
        a = min(1.0, (t - 3.0) / 0.8)
        ax.text(0.5, 0.93, "luciferin  +  ATP  +  oxygen", ha="center", fontsize=26,
                color="white", weight="bold", alpha=a)
        ax.text(0.5, 0.885, "C11H8N2O3S2   C10H16N5O13P3   O2", ha="center", fontsize=16,
                color="#aaaaaa", alpha=a)
        # drift together
        cx = 0.5
        lp = [(x + (cx - 0.28) * lt * 0.55, y) for (x, y) in luc_pos0]
        ap = [(x - (0.72 - cx) * lt * 0.55, y) for (x, y) in atp_pos0]
        op = [(x + (cx - x) * lt * 0.6, y - (y - 0.55) * lt * 0.6) for (x, y) in o2_pos0]
        draw_mol(ax, luc_atoms, lp, a)
        draw_mol(ax, atp_atoms, ap, a)
        draw_mol(ax, ["O", "O"], op, a)
        ax.text(0.5, 0.12, "luciferase + Mg2+  (the catalyst)", ha="center", fontsize=20,
                color="#7CFC00", alpha=a)
    elif t < 11.0:
        # FLASH
        ft = (t - 8.0) / 3.0
        flash = np.exp(-3.0 * ft) if ft < 1 else 0
        bg = 0.12 * flash
        ax.set_facecolor((bg, bg * 1.2, bg * 0.4))
        ax.text(0.5, 0.60, "LIGHT", ha="center", fontsize=72, color="#eaffea",
                weight="bold", alpha=min(1.0, flash * 3))
        # photon wave at 560nm color
        if ft > 0.15:
            wt = (ft - 0.15) / 0.85
            x0 = 0.5 - wt * 0.9
            xs = np.linspace(max(0.02, x0), 0.98, 300)
            ys = 0.30 + 0.035 * np.sin((xs - x0) * 90) * np.exp(-((xs - x0) * 6) ** 2)
            ax.plot(xs, ys, color="#adff2f", lw=3, alpha=0.9)
            ax.text(0.5, 0.20, "one photon  •  560 nm", ha="center", fontsize=26,
                    color="#adff2f", weight="bold", alpha=min(1.0, wt * 2))
    else:
        # the numbers
        a = min(1.0, (t - 11.0) / 0.8)
        ax.text(0.5, 0.66, "E = hc / λ", ha="center", fontsize=44, color="white",
                weight="bold", alpha=a)
        ax.text(0.5, 0.56, "3.55 × 10⁻¹⁹ J", ha="center", fontsize=40, color="#adff2f",
                weight="bold", alpha=a)
        ax.text(0.5, 0.49, "≈ 2.21 eV", ha="center", fontsize=34, color="#adff2f", alpha=a)
        ax.text(0.5, 0.38, "computed, not guessed", ha="center", fontsize=22,
                color="#aaaaaa", alpha=a)
        if t > 13.5:
            a2 = min(1.0, (t - 13.5) / 0.8)
            ax.text(0.5, 0.24, "real chemistry.", ha="center", fontsize=26,
                    color="white", alpha=a2)
            ax.text(0.5, 0.185, "real light.", ha="center", fontsize=26,
                    color="white", weight="bold", alpha=a2)

ani = FuncAnimation(fig, draw, frames=np.linspace(0, DUR, NFRAMES), interval=1000 / FPS)
out = "/home/hatch/workspace/goals/thet-logos-continued-development-and-release/files/tiktok-daily/tiktok-2026-10-05-luci-light.mp4"
ani.save(out, writer="ffmpeg", fps=FPS, dpi=DPI,
         extra_args=["-pix_fmt", "yuv420p", "-crf", "20"])
print("wrote", out)
