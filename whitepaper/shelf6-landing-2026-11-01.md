# SHELF-6 LANDING DOSSIER — 2026-11-01

**Item:** SHELF-6 (semigroup duality: resolvent positivity), per
the ratified SHELF memo and the coordinator pack (`pack-shelf-6.md`).

**Status: FULL at the named finite C(K) seat; PARTIAL at the
pre-named general ordered-Banach-lattice seam** (the pin lacks the
API, named exactly below). Both halves were registered in advance;
the verdict is the registered shape.

**Artifact:** `lean/ThetLogos/SemigroupDuality.lean` — strict 54,
defs 10 (above the pack's 25–40 estimate; disclosed). Verified by
the coordinator in the main tree (build green, 8979 jobs); all
four headlines on exactly `[propext, Classical.choice, Quot.sound]`.

## What landed (finite C(K) seat)

Seat: `E = K → ℝ`, `[Fintype K] [DecidableEq K] [Nonempty K]`,
pointwise positivity, Pi (sup) norm; bounded generators
`A : (K → ℝ) →L[ℝ] (K → ℝ)`; the semigroup is SHELF-1a's
`expSemigroup` (cited, never forked).

- `sgPos_iff_resPosLarge` — positivity duality: the semigroup is
  positive ⟺ the resolvent is positive at all large parameters
  (via the Metzler/quasi-positivity bridge).
- `sgContr_iff_dissBound` — contraction duality: the semigroup is
  contractive ⟺ SHELF-1b's `DissBound` holds at the seat
  (Yosida–Neumann route).
- `sgPosContr_iff_resPosDiss` — the combined iff.
- SHELF-5 read-backs: `pf_posOp`, `pf_posOp_exp`, `pf_stationary`
  (the Perron vector is stationary for the shifted semigroup).
  Pack correction on the record: SHELF-5's landed module is
  `PerronFrobenius.lean` (headline `perronFrobenius`), not the
  pack's guessed filename; its names are cited exactly.

## The PARTIAL seam — missing API named exactly

The general ordered-Banach-lattice form was NOT landed. The pin
(Mathlib v4.35.0-rc3) does not carry it: (1) no Banach-lattice /
closed-cone positive-operator package — only
`NormedLatticeAddCommGroup` and `HasSolidNorm` exist, and no
positive-operator or positive-semigroup API at all; (2) no
Post–Widder exponential formula and no Laplace resolvent formula
(the latter is also SHELF-1a's named remainder) — the classical
basis-free routes; (3) no resolvent-positivity lemma of any kind
in the pin (grep: zero hits).

## Fences

NO CLAIM — no Millennium problem is claimed solved or advanced.
Dials 0/4.

**Census after landing: 10,838 strict / 10,941 total / 365 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
