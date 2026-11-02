# B4-REPAIR LANDING DOSSIER — 2026-11-02

**Item:** B4-REPAIR (SHELF-7b-disc chain, GATE-B) — the
repair entry for the hypothesis GATE-B3′ left named, after
the GATE-B4 scoping found the frozen form false as stated
(K-B4-LITERAL). The B4 scoping memo rides into `whitepaper/`
with this landing (`scoping-gate-b4-2026-11-02.md`).

## VERDICT: FULL — refutation in-tree, corrected form frozen, adapter complete; no seam

**Artifact:** `lean/ThetLogos/HfcDiscFactorisationRepair.lean`
— strict 3, defs 1. Verified by the coordinator in the
main tree (build green, 2985 jobs); all headlines on
exactly `[propext, Classical.choice, Quot.sound]`. The
landed B3′ module is untouched.

**(1) The refutation, now a theorem:**
`discFactorisationHyp_not : ¬ DiscFactorisationHyp (0 : A)
f 2` for GATE-B1's boundary witness f (1 on the unit
circle, 0 elsewhere), at R₀ = 1, μ = 1. LHS = 0 (via
`hfcDisc_at_zero` and the landed boundary coefficient
`discCoeff f 1 0 = 1`); the hypothesised RHS is a unit
(B3′'s own `isUnit_list_prod` and
`isUnit_a_sub_smul_one_of_notMem_spectrum` times the
hypothesised unit) — contradiction with `IsUnit.ne_zero`.
Helper: spectral values of 0 have norm ≤ 0, so
`f '' spectrum ℂ 0 = {0}` and 1 ∉ it. **K-B4-LITERAL's
in-tree receipt.**

**(2) The corrected form, new entry:**
`DiscFactorisationHyp'` — the frozen body behind exactly
the antecedents `Shelf7bDiscInterior` supplies:
`DiscHolomorphic f R → (spectralRadius ℂ a).toReal < R →
DiscFactorisationHyp a f R`. Every later GATE-B brick
targets the primed form; the frozen form is never consumed
downstream.

**(3) The adapter, FULL:**
`shelf7bDiscInterior_proved_of_factorisation'` — the
interior equality from the primed hypothesis, by applying
it under the interior's own antecedents and feeding B3′'s
landed assembly. So B3′'s PARTIAL is now, precisely:
equality ⇐ `DiscFactorisationHyp'`, a hypothesis about
holomorphic f only — satisfiable in principle and the
target of the priced discharge campaign (B4-FIN ∥ B4-PROD
→ B4-TAIL → B4-UNIT → B4-ASM, per the scoping's firing
order).

## Fences

NO CLAIM; all dials 0/4. 7b-in-full remains pin-blocked;
the disc chain runs under its own name.

**Census after landing: 12,255 strict / 12,661 total / 422 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
