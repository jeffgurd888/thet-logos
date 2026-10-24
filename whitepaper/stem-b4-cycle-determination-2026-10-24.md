# STEM Bridge B4-General — The Determination Theorem STANDS; the Bridge Stands WHOLE at Its Finite Seat

**Date:** 2026-10-24 · **Charter:** `whitepaper/stem-bridge-scoping-2026-10-24.md`; remainder named by `whitepaper/stem-b4prime-flux-2026-10-24.md`. **Verdict: STANDS (T1) — the STEM bridge ladder (B1, B2, B3, B4′, B4, B5) is complete.** Parent-verified 2026-10-24: targeted build exit 0 on the shipped text, strict recount 22, zero `sorry`/`admit`, headline axioms standard only.

**NO CLAIM.** Finite bookkeeping only — not Maxwell, no continuum seat; the killed pastes stay killed (no EM-torsion identity, no "strong = EM", magnetophase-as-flux stays killed at T1). Parts of any official Clay statement closed: **0**.

## The module — `BridgeMagneticCycle` (22 strict / 3 defs)

- **Stage 1 — the tree seat, as explicit datum (the plan-of-record fallback, fenced on the module's face).** A spanning tree enters as data: root / parent / depth with the step law `depth (par v) + 1 = depth v` off the root; §1 proves it behaves as a tree (`iterate_par_eq_root`: every vertex reaches the root in exactly `depth v` parent steps). Why a datum and not a construction: the corpus's vocabulary carries the connection θ on *all ordered pairs* — there is no edge set and no `SimpleGraph` in the bridge vocabulary, so "the graph" is the complete pair set, whose spanning trees are exactly parent data. Mathlib was checked as tasked: `SimpleGraph.IsTree`/`IsAcyclic` exist, but **there is no cycle-space API anywhere in Mathlib**, and welding SimpleGraph adjacency to θ would be a second bridge. The datum is a hypothesis because this vocabulary cannot state "graph" to construct it from — recorded here and on the module's face, not hidden.
- **Stage 2 — global gauge fixing STANDS.** `normalConn θ = gaugeConn (treeHol θ) θ` is trivial on every tree edge (`normalConn_trivial_on_tree`) — gauge-fix any connection to tree-trivial form, no side conditions beyond the datum and θ's antisymmetry law.
- **Stage 3 — determination STANDS AT FULL STRENGTH.** `determination`: two connections are gauge-equivalent **if and only if** all their fundamental-cycle holonomies agree — a full ⇔, not injective-only, no connectedness restriction; the backward direction is witnessed explicitly by the gauge `(treeHol θ₂)⁻¹ * treeHol θ₁`. Bonus: `normalConn_unique` — the normal form is the *unique* tree-trivial representative of its gauge class.
- **Stage 4 — readings STAND.** `cycleHol_readings` in B4′'s exact package shape: agreement of cycle holonomies ⇔ agreement of face holonomies ∧ spectrum ∧ heat trace, the hypothesis traded up to holonomy equality via `determination`. Weld `cycleHol_one`: at θ ≡ 1 every cycle holonomy is 1.

## Bridge state

**The STEM bridge stands WHOLE at its finite seat.** B4′'s PARTIAL is discharged by name: what the face-restricted brick could not say — that the holonomy data determines the gauge class, and with it the spectrum and heat readings — is now a theorem, relative to a given tree datum in the corpus's all-pairs vocabulary. One honest boundary remains on the record: turning "every finite graph carries such a tree datum" into a construction inside this vocabulary (or welding `SimpleGraph`) is a separate, unbuilt bridge — a vocabulary fact, not a gap in the determination itself.

## Census

4,662 → **4,684 strict** · 4,711 → **4,733 attribute-inclusive** · 158 → **159 counted modules**. Seven-sorry qualification unchanged.
