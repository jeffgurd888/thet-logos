# Exhibit — The Walker

**Exhibit (interactive numerical demonstration, not a theorem).**

A two-dimensional simple random walker, and the crowd he belongs to:

- **Main panel:** one walker steps randomly on a lattice from a starting
  point (x, y) you can set, leaving a fading trail. Live counters show
  the step count t, his position, and his squared distance r² — x in red,
  y in blue, r² in green (the house color law).
- **Ensemble panel:** 200 walkers run in parallel, and their average
  squared distance is plotted live against the exact line x² + y² + t.

The theorem the exhibit demonstrates is machine-checked in Lean 4
(`lean/DiffusionDefect.lean`, 12 theorems, zero sorry): for this walk,
the expected squared displacement after t steps is EXACTLY x² + y² + t.
The simulation agreeing with the line is the demonstration; the proof
is in the repository. Fences, as printed on the exhibit itself:
t = step count; the coefficient 1 is the walk's chosen diffusivity;
the + is the chosen Euclidean signature.

To play: download `index.html`, open it in any browser. Single
self-contained file, no dependencies, no network calls — it runs
entirely on your machine. Free forever under the repository's MIT
license — Nexus Research, thet-logos / ACMD program.
