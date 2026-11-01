# TTK-2 LANDING DOSSIER — 2026-11-01

**Item:** TTK-2 (Ternary Thermal Kernel line, brick 2) —
unparked by Jeff naming it (2026-11-01 17:12 EST); built per
its registered scoping (2026-10-27 memo §3 Brick 2).

## VERDICT: FULL — the fixed-point characterization holds in both directions; the generator lands beyond the pre-named PARTIAL

**Artifact:** `lean/ThetLogos/TernaryThermalNormalized.lean` —
strict 15, defs 2 (in the 12–20 estimate). Verified by the
coordinator in the main tree (build green, 3585 jobs); all
fifteen theorems on exactly
`[propext, Classical.choice, Quot.sound]`.

**The normalized step (T2):** `ternaryStepNorm lam t X :=
(trace (ternaryStep lam t X))⁻¹ • ternaryStep lam t X`, with
the supporting bank: on diagonal states the normalized
weights are `Z⁻¹ · exp(−2t·lam i) · w i` with
`Z = ∑ exp(−2t·lam j) · w j > 0` at states (no junk case
enters), normalized trace exactly 1, states map to states.

**Fixed-point characterization (the brick's core, T1):**
for `t > 0` and a diagonal state `w`,

```
ternaryStepNorm lam t (diagState w) = diagState w
  ↔ ∃ L, ∀ i, w i = 0 ∨ lam i = L
```

— a diagonal state is fixed iff its support lies inside a
single lam-level. Both directions proved; no counterexample
in either direction; no K-TTK kill fires.

**Generator theorem — landed MORE than the pre-named
PARTIAL, with one honest correction at full rank:** the
step conjugates its middle argument, so the derivative at
general X is at `Xᴴ`, not X:

- general: `HasDerivAt (fun t => ternaryStep lam t X)
  (-(Λ * Xᴴ + Xᴴ * Λ)) 0` for ALL X;
- the pack's literal form `-(Λ X + X Λ)` lands exactly where
  it is true — the Hermitian seat and the charged diagonal
  seat (`diagState w`), with the closed form
  `-(Λ ρ + ρ Λ) = diagState (fun i => -2 * lam i * w i)`.

The literal-X general statement is FALSE as stated for
non-Hermitian X; reported, not forced.

**KMS-failure quantification (T1):** one conjunction
theorem — for a thermal clock C, t > 0, and lam taking two
distinct values: the KMS identity for the clock state under
the modular diagFlow holds (unconditionally, TTK-1's landed
theorem) AND the normalized ternary step moves the clock
state. At the clock (full support), normalized-step fixed
iff lam is constant — the failure is exactly "one level vs.
two." The memo's fence stands: nothing here rehabilitates
any "the ternary step is the modular flow" claim — TTK-1's
kill of that identification stands, now quantified.

## Fences

Finite, diagonal-seat, corpus-internal dynamics; "dynamics"
means exactly these maps. Jeff's T5 glosses stay prose. NO
CLAIM; dials 0/4.

**Census after landing: 11,659 strict / 11,959 total / 397 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
