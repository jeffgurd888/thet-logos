# GATE-B3′ LANDING DOSSIER — 2026-11-02

**Item:** GATE-B3′ (SHELF-7b-disc chain, GATE-B) — the disc
spectral mapping EQUALITY, `Shelf7bDiscInterior`.

## VERDICT: PARTIAL at the pack's pre-named seam — the equality is assembled under one named hypothesis; one ingredient landed FULL; the constant case is unconditional

**Artifact:** `lean/ThetLogos/HfcDiscSpectralMapping.lean`
— strict 10, defs 1. Verified by the coordinator in the
main tree (build green, 2984 jobs); all 8 headlines on
exactly `[propext, Classical.choice, Quot.sound]`. The
unconditional `shelf7bDiscInterior_proved` is NOT claimed.

**Landed FULL — ingredient 1:** `hfcDisc_mul_of_summable`,
the general sharp-scale multiplicativity of the disc
calculus under Cauchy products of coefficient sequences
(GATE-B2′ had only the discFactor special case). This is a
permanent tool for the whole shelf line.

**The seam, exactly:** `shelf7bDiscInterior_proved_of_factorisation`
assembles the equality from B2′ (forward inclusion) and the
reverse inclusion proved under the single named hypothesis

```
DiscFactorisationHyp a f R := ∀ R₀ (interior), ∀ mu ∉ f '' spectrum ℂ a,
  ∃ (lam : List ℂ) (hc : ℕ → ℂ), (∀ l ∈ lam, l ∉ spectrum ℂ a) ∧
    Summable (fun n => ‖hc n • a ^ n‖) ∧ IsUnit (hfcDisc a hc) ∧
    hfcDisc a (discCoeff f R₀) − mu • 1
      = (lam.map fun l => a − l • 1).prod * hfcDisc a hc
```

— the joint output of the route's ingredients 2+3. The
assembly from a factorisation is fully proved (including
`isUnit_a_sub_smul_one_of_notMem_spectrum` and the
noncommutative List.prod unit lemma). What remains open,
named on the module's face: **discharging the hypothesis in
general** — ingredient 2 (a zero-free holomorphic factor's
calculus value is a unit, via the reciprocal series) and
ingredient 3 (finiteness and factorisation of the zeros of
f − mu in a closed subdisc).

**Bonus, hypothesis-free:** the equality for **constant
functions** is proved unconditionally
(`shelf7bDiscInterior_const`, via `discCoeff_const` and
`discFactorisationHyp_const`).

**K-GELFAND-SUBALGEBRA respected** — no character/Gelfand
route was used or attempted. The REFUTED frozen forms were
never consumed.

**Successor:** discharging `DiscFactorisationHyp` (working
label GATE-B4) goes to scoping in flow — ingredients 2 and 3
priced separately, kills registered there. The 7b-disc
chain's state: B1a/B1b/B1d FULL, B1c killed-and-corrected,
B2′ FULL, B3′ PARTIAL at this named hypothesis.

## Fences

NO CLAIM; all dials 0/4. 7b-in-full remains pin-blocked;
the disc chain runs under its own name.

**Census after landing: 12,227 strict / 12,612 total / 418 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
