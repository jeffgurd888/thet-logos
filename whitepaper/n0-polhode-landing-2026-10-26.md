# N0 — The Momentum-Sphere Affine Forms (Nonlinear Program Prerequisite)

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/SolidBodyPolhode.lean` (strict 48, defs 12, zero
`sorry`, zero `native_decide`; main-tree build green, 3,229 jobs,
parent-verified on the shipped text). Scoped in
routeb-general-scratch/nonlinear-rigid-scoping-2026-10-26.
**Parts of the Clay Yang–Mills statement closed by this landing:
0.** Classical mechanics, abstract body only.*

## A correction to the scoping memo — reported first

The memo's §0 registers "M₃² affine *increasing* in u". **That is
false under the memo's own conventions**, and this landing proves
the true version. On the momentum sphere, both M₁² and M₃² are
affine functions of u = M₂², and both are *decreasing*: their
slopes sum to −1 necessarily, since M₁² + u + M₃² = Λ. Numeric
witness: I = (1,2,3), Λ = 10, E = 3 — as u goes 0 → 1, M₃² goes
6 → 5.25. The proved forms are `m1SqOfU` / `m3SqOfU` in factored
slope•(root − u) form, with `m3SqOfU_strictAnti` registering the
decreasing direction. **Downstream bricks (portrait, period) must
consume decreasing/decreasing; the memo's §0 wording is superseded
by this dossier and must not be propagated.**

## What landed

The affine parametrizations of the first-integral pair on the
momentum sphere: `m1SqOfU`, `m3SqOfU`, their roots, the band bounds
on u, the three energy levels Λ/(2I_k), and **`sep_saddle`** — the
separatrix characterization: at E_sep = Λ/(2I₂), both M₁² and M₃²
vanish together at u = Λ (the saddles). This is the shared
prerequisite the scoping priced for both nonlinear remainders —
the polhode portrait and the separatrix period — now in hand.

Axiom sets on the headlines: exactly
`[propext, Classical.choice, Quot.sound]`.

## Census effect

Strict 5,956 → **6,004**; attribute-inclusive 6,034 → **6,082**;
modules 202 → **203**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
