# Solid Body Foundation — Landing Dossier

**Date:** 2026-10-26 (built 2026-10-25/26)
**Modules:** `ThetLogos/SolidBody.lean` (18 strict, 16 defs, +6 same-line `@[simp]` evaluation lemmas), `ThetLogos/SolidBodyOcean.lean` (5 strict, 2 defs, 1 structure)
**Verdict: FULL — both bricks, the stretch included.** T1-from-hypotheses over T4 physics inputs. NO CLAIM on any physical body or on the real Earth.

## What landed

**Brick 1 — the rigid body.** A `SolidBody` is three positive principal moments. On it: angular momentum, rotational energy, |L|², and the Euler right-hand side with the cyclic convention ω̇ᵢ = ((Iⱼ−Iₖ)/Iᵢ)·ωⱼ·ωₖ fixed in the header. The two algebraic contraction identities vanish identically; energy and body-frame |L|² are conserved along any differentiable ω satisfying the Euler equations (T1 from the Euler hypothesis — the hypothesis is named, not hidden; space-frame L is explicitly NOT claimed — that needs Poinsot theory Mathlib does not carry). The linearized intermediate-axis instability is proved: for I1 < I2 < I3 and spin Ω > 0 about the middle axis, the growth rate γ = Ω·√(((I3−I2)(I2−I1))/(I1·I3)) is positive and the mode x(t) = sinh(γt), z(t) = (γ/a)·cosh(γt) satisfies the linearized system and is unbounded (`intermediate_linear_unstable`). The stretch — a stable-axis (max-axis) bounded sin/cos mode with |x(t)| ≤ 1 — landed in the same brick as the contrast case.

**Brick 2 — the ocean amendment (Jeff's commission: "rigid body with oceans of lunar tidal locked water").** An `OceanBody` adds a locked ocean with moment Ioc > 0, coupling κ > 0, tidal lag δ, and lunar rate. The tidal torque is a DEFINITION in the MacDonald lag form τ := −κ·sin(2δ), labeled T4 input in its docstring, not derived. Proved: the torque's sign on 0 < δ < π/4 (`tidalTorque_neg`); total angular momentum conservation from the two channel hypotheses (spin loses what orbit gains, exactly); the secular corollary in full — Lspin is affine in t with slope τ, strictly antitone when the torque is negative (`Lspin_affine`, `Lspin_strictAnti`); and the chain-rule lemma that the locked channel's angular momentum Ioc·nMoon carries no independent time dependence (`locked_phase_rate`). The day-lengthening / lunar-recession calibration numbers (+2.3 ms/century, 3.8 cm/yr) appear in comments as T4 reference values only.

## Fences printed on the modules' faces

Euler's equations, the torque law, κ, δ are T4 physics inputs; the theorems are T1 consequences of stated hypotheses. Only the ocean's **locked** (tidal) component is modeled — the free currents and Coriolis flows are a different channel (the melt-loop exhibit's motion term), and in this model the lock never slips, which is exactly why the braking is secular. Brick 1 is the fixed-moments **foundation** — the variable-intermediate-axis theorem Jeff named on 2026-10-25 stands above it, still unbuilt, as Curiosity Ledger item 9's remaining content.

## Verification

Bench (isolated tree): brick 1 build exit 0, brick 2 build exit 0, oleans present. Axiom checks: every headline theorem in both modules depends on exactly [propext, Classical.choice, Quot.sound]. Zero `sorry` (grep), `native_decide` never used. Parent recount on the shipped text confirmed strict 18 + 5. Main-tree targeted build: see the landing commit.

## Census

Public census moves with this landing: strict 5,684 → **5,707**, attribute-inclusive 5,745 → **5,774**, counted modules 183 → **185**. Placeholder census unchanged at 6.

## Backers since last landing

The roll stands as it stood in the KMS dossier — no gifts recorded in this interval. Every gift, when it comes, is inscribed here by name as its giver wishes, or as "a gift of bench time" when they prefer no amount and no name. The record is the reciprocity: this landing exists in the open because the lab is free for everyone, forever.
