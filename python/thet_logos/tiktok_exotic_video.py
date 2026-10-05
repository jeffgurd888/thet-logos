"""TikTok video built from the REAL exotic matrices (not stock AI visuals).

4 phases, 9:16 vertical (720x1280):
  1. Hook: "12 hidden directions in the math of reality"
  2. The 12 actual exotic matrices as glowing heatmaps (parsed from Lean source)
  3. Commutator graph: nodes split into 8 + 2 + 2 sectors (real computed structure)
  4. "8 + 2 + 2 — the 12 is becoming architecture" + question card
"""
import re
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
from matplotlib.patches import Ellipse
import sys
sys.path.insert(0, "/home/hatch/workspace/thet-logos/python/thet_logos")
from exotic_structure_probe import parse_defs, LEAN

NAMES = ["NuLeR", "ELNuR", "ULDR", "DLUR", "NuREbarR", "EREbarR"]
LABELS = [f"Re{n}" for n in NAMES] + [f"Im{n}" for n in NAMES]
# sector assignment from the probe: A=8 (idx 0,1,4,5,6,7,10,11), B1=ULDR pair (2,8), B2=DLUR pair (3,9)
SECTOR = [0, 0, 1, 2, 0, 0, 0, 0, 1, 2, 0, 0]
SECTOR_COLORS = ["#4da6ff", "#ffcc33", "#ff5566"]  # blue, gold, red
SECTOR_NAMES = ["8", "2", "2"]

W, H, DPI = 720, 1280, 100
FPS = 30
DUR = 15.0
NFRAMES = int(FPS * DUR)

mats = parse_defs(LEAN)
E = [mats[f"exoticRe{n}"] for n in NAMES] + [mats[f"exoticIm{n}"] for n in NAMES]
# commutator adjacency
adj = np.zeros((12, 12))
for a in range(12):
    for b in range(12):
        if a != b and np.linalg.norm(E[a] @ E[b] - E[b] @ E[a]) > 1e-8:
            adj[a, b] = 1

# node layout: ring for sector A, pairs pulled to sides (axes coords; y scaled by W/H for circular appearance)
AR = W / H  # 0.5625
rng = np.random.default_rng(7)
posA = []
A_idx = [i for i in range(12) if SECTOR[i] == 0]
for k, i in enumerate(A_idx):
    th = 2 * np.pi * k / len(A_idx)
    posA.append((0.5 + 0.27 * np.cos(th), 0.50 + 0.27 * AR * np.sin(th)))
pos = {}
for k, i in enumerate(A_idx):
    pos[i] = posA[k]
B1 = [i for i in range(12) if SECTOR[i] == 1]
B2 = [i for i in range(12) if SECTOR[i] == 2]
pos[B1[0]] = (0.13, 0.56); pos[B1[1]] = (0.13, 0.44)
pos[B2[0]] = (0.87, 0.56); pos[B2[1]] = (0.87, 0.44)
# start: all clustered center, end: separated
start_pos = {i: (0.5 + 0.05 * rng.standard_normal(), 0.52 + 0.05 * rng.standard_normal()) for i in range(12)}

fig = plt.figure(figsize=(W / DPI, H / DPI), dpi=DPI, facecolor="black")

def ease(t):
    return t * t * (3 - 2 * t)

def draw(t):
    fig.clear()
    # starfield background
    ax_bg = fig.add_axes([0, 0, 1, 1], facecolor="black")
    ax_bg.set_xlim(0, 1); ax_bg.set_ylim(0, 1); ax_bg.axis("off")
    sx, sy = rng.random(120), rng.random(120)
    ax_bg.scatter(sx, sy, s=2, c="white", alpha=0.25)

    if t < 2.5:
        # PHASE 1: hook
        a = min(1.0, t / 1.0)
        ax_bg.text(0.5, 0.55, "12 hidden directions", ha="center", va="center",
                   fontsize=44, color="white", weight="bold", alpha=a)
        ax_bg.text(0.5, 0.47, "in the math of reality", ha="center", va="center",
                   fontsize=34, color="#4da6ff", alpha=a)
    elif t < 7.5:
        # PHASE 2: the 12 real matrices
        a = min(1.0, (t - 2.5) / 0.8)
        ax_bg.text(0.5, 0.93, "a computer proved", ha="center", fontsize=30,
                   color="white", weight="bold", alpha=a)
        ax_bg.text(0.5, 0.885, "every single step", ha="center", fontsize=30,
                   color="#4da6ff", weight="bold", alpha=a)
        for k in range(12):
            r, c = divmod(k, 3)
            ax = fig.add_axes([0.06 + c * 0.30, 0.62 - r * 0.175, 0.26, 0.15], facecolor="black")
            ax.imshow(np.abs(E[k]), cmap="hot", interpolation="nearest", alpha=a)
            ax.set_xticks([]); ax.set_yticks([])
            for sp in ax.spines.values():
                sp.set_color("#333333")
            ax.set_title(LABELS[k], color="#aaaaaa", fontsize=11, pad=2)
    elif t < 11.5:
        # PHASE 3: graph splits into 8+2+2
        lt = ease(min(1.0, max(0.0, (t - 7.5) / 2.5)))
        a = min(1.0, (t - 7.5) / 0.6)
        ax_bg.text(0.5, 0.93, "tonight they split apart", ha="center", fontsize=30,
                   color="white", weight="bold", alpha=a)
        cur = {i: (start_pos[i][0] + (pos[i][0] - start_pos[i][0]) * lt,
                   start_pos[i][1] + (pos[i][1] - start_pos[i][1]) * lt) for i in range(12)}
        for a_i in range(12):
            for b_i in range(a_i + 1, 12):
                if adj[a_i, b_i]:
                    ax_bg.plot([cur[a_i][0], cur[b_i][0]], [cur[a_i][1], cur[b_i][1]],
                               color="#444444", lw=1, alpha=0.7 * a)
        for i in range(12):
            x, y = cur[i]
            node = Ellipse((x, y), 0.085, 0.085 * AR, color=SECTOR_COLORS[SECTOR[i]],
                           alpha=a, zorder=3)
            ax_bg.add_patch(node)
            ax_bg.text(x, y, LABELS[i], ha="center", va="center", fontsize=6.5,
                       color="black", weight="bold", alpha=a, zorder=4)
        # sector labels
        ax_bg.text(0.5, 0.78, "8", ha="center", fontsize=40, color="#4da6ff", weight="bold", alpha=a * lt)
        ax_bg.text(0.13, 0.66, "2", ha="center", fontsize=40, color="#ffcc33", weight="bold", alpha=a * lt)
        ax_bg.text(0.87, 0.66, "2", ha="center", fontsize=40, color="#ff5566", weight="bold", alpha=a * lt)
    else:
        # PHASE 4: payoff + question
        a = min(1.0, (t - 11.5) / 0.8)
        ax_bg.text(0.5, 0.62, "8 + 2 + 2", ha="center", va="center",
                   fontsize=72, color="white", weight="bold", alpha=a)
        ax_bg.text(0.5, 0.52, "the 12 is becoming", ha="center", fontsize=32, color="#4da6ff", alpha=a)
        ax_bg.text(0.5, 0.465, "architecture", ha="center", fontsize=32, color="#4da6ff",
                   weight="bold", alpha=a)
        if t > 13.0:
            a2 = min(1.0, (t - 13.0) / 0.8)
            ax_bg.text(0.5, 0.30, "what do you think", ha="center", fontsize=28,
                       color="white", alpha=a2)
            ax_bg.text(0.5, 0.25, "the 2 + 2 are?", ha="center", fontsize=28,
                       color="white", weight="bold", alpha=a2)

ani = FuncAnimation(fig, draw, frames=np.linspace(0, DUR, NFRAMES), interval=1000 / FPS)
out = "/home/hatch/workspace/goals/thet-logos-continued-development-and-release/files/tiktok-daily/tiktok-2026-10-05-exotic-split-real.mp4"
ani.save(out, writer="ffmpeg", fps=FPS, dpi=DPI,
         extra_args=["-pix_fmt", "yuv420p", "-crf", "20"])
print("wrote", out)
