# MAX-1 LANDING — 2026-11-01

## The weld + the atom: FULL (working label: MAX line)

**Module:** `ThetLogos.MaxwellQuadWeld` — strict 15 / defs 0,
parent-verified (independent count, main-tree build,
headline axiom checks on exactly
`[propext, Classical.choice, Quot.sound]`).

**Census at this landing: 10,397 strict / 10,474 total /
353 modules, zero sorrys.**

MAX-1 is the first build brick of the MAX line (the finite
Maxwell quadratic operator on the layer lattice's link
angles; scoping: `scoping-maxwell-finite-2026-10-31.md`;
pin: MAX-0, `MaxwellQuadPost.lean`). It discharges the two
contents the rest of the line stands on.

## The weld — the additive shadow IS the holonomy's shadow

`plaqHol_circle_exp_weld`:
`PlaqHol P (fun ℓ => Circle.exp (θ ℓ))
= Circle.exp (plaqAngle P θ)`
for every plaquette datum P and every link-angle field θ.
The additive plaquette angle `plaqAngle` (the pin's
definition) is hereby *proved* — not asserted — to be the
logarithm-side shadow of the corpus's landed multiplicative
plaquette holonomy `PlaqHol` at the Circle seat. Every
downstream reading of `plaqAngle` as the holonomy's additive
form (MAX-2's assembly; the REM line's defect field, which
cites `plaqAngle` by the pin) now rests on a theorem.

**Name resolution, on the record:** the scoping memo and
the build pack named the Circle exponential
`expMapCircle`; that name exists nowhere in this corpus or
its Mathlib pin (grep-verified). The landed vocabulary is
`Circle.exp` (Mathlib `Analysis/Complex/Circle.lean`, with
`Circle.exp_add` / `Circle.exp_neg`; already used in-corpus
at `LatticeGramSeries.lean:675`), and the weld is stated
and proved with it. The MAX-0 pin registered no weld Prop
(headlines M1–M5 only), so no registered statement was
altered — the pack's form governs, with the one name
resolved to its real home.

## The atom (M4) — spectrum exactly {4, 0, 0, 0}, as registered

`maxwellM4_proved : maxwellM4` discharges the pin's
registered atom statement in full: the single-plaquette
operator on its four edge values is rank one
(`maxwellAtomOp x = plaqPattern x • atomVec`,
`atomVec = (1, 1, -1, -1)` in (B, R, T, L) order);
eigenvalue 4 with named eigenvector `atomVec`
(`maxwellAtomOp_atomVec`, via `plaqPattern atomVec = 4`);
eigenvalue 0 (witness `(1, 0, 1, 0)`); **no other
eigenvalue** (`maxwellAtomOp_eigenvalue_eq`); kernel
exactly `{x | x 0 + x 1 = x 2 + x 3}` of finrank 3
(`maxwellAtomOp_eq_zero_iff`, `maxwellAtomOp_finrank_ker`);
Rayleigh form `∑ i, x i * (maxwellAtomOp x) i
= (plaqPattern x)^2` (`maxwellAtomOp_rayleigh`).

**K-MAX-3 did not fire** — the computed spectrum is the
registered one. **K-MAX-1 re-checked at the landing:** the
atom as built is the pin's own component formula on
`Fin 4 → ℝ`; it is not definitionally the transfer
operator, the plaquette block/factor, `magLin`, or the
vertex `lapLin` renamed (none has this type or formula),
and its form does not collapse to `osForm`.

## What this landing is not

A single plaquette's operator and a logarithm identity —
finite algebra at spacing 1. Not a dispersion relation
(that is MAX-3's finite spectrum, labeled finite there),
not a photon (OP-1's photon is a different, disjoint
finite object — the massless direction of the Higgs mass
form), not a continuum statement of any kind. "Lorentzian"
and "bridge" remain unspent (K-MAX-2). Dial 2 = 0; NO
CLAIM; dials 0/4.

Next on the line: MAX-2 (assembly at general N — M1/M2/M3
plus the Wilson tie), which hard-gates GEO-2, PROP-1, and
REM-2; then MAX-3 (the cube spectrum and the finite gap
`4·sin²(π/N)`), the claims registry's last verdict brick.

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you
to everyone reading the stream — the corpus is free for
everyone, forever.

*End of dossier.*
