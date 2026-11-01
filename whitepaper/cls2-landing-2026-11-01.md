# CLS-2 LANDING DOSSIER — 2026-11-01

**Item:** CLS-2 (Dial-1 classification lane) — the toggle-orbit
structure of the strengthened set.

## VERDICT: PARTIAL at one named point — the uniform triple swap's Base clause; K-CLS-2 does NOT fire, and is now armed at exactly that point

**Artifact:** `lean/ThetLogos/DialOneSwapOrbit.lean` — strict
51, defs 5 (above the 20–40 estimate — the allSwap analysis
below; reported as counted). Verified by the coordinator in
the main tree (build green, 3142 jobs); all headlines on
exactly `[propext, Classical.choice, Quot.sound]`.

**Landed FULL:** `orbitRep b` = pi1 plus the landed
single-corrections of the toggles whose bit is set (bit 0 =
piDouble; bits 1–3 = piSwap 0, 1, 2), with read-backs
(`orbitRep_zero`, `orbitRep_bit0 = piDouble`,
`orbitRep_bitSwap c = piSwap c`); **injectivity**
(`orbitRep_injective` — the 16 orbit points are pairwise
distinct; K-CLS-2's relation arm does not fire); **C3 holds
at every orbit point** (`c3_orbitRep`); and the membership
decision at **15 of 16 points**:

```
strengthened_orbitRep_iff_of_ne_allSwap :
  b ≠ allSwapBits → (DialOneStrengthenedFam (orbitRep b) ↔ b = 0)
```

— bit 0 set ⇒ F_eR fails (trace −2αi, localized: only
piDouble's correction touches seats {9, 25}); mixed swap
patterns ⇒ `DialOneBase` fails at order-zero (the entry
reads φ_c vs φ_c′, which differ exactly on mixed pairs,
generalized to any distinct colour pair).

**The open point — `allSwapBits` (all three colours toggled,
bit 0 unset).** Both exclusion mechanisms provably fail
there (`allSwap_exclusion_mechanisms_fail` is proved): F_eR
holds, C3 and the whole clean γ-family hold
(`gammaFamily_allSwap`), and the order-zero entry cannot
distinguish a uniform toggle (φ_c vs φ_c′ agree when every
colour is flipped). Membership is reduced exactly:
**`strengthened_allSwap_iff_base`** — the uniform triple
swap is in the strengthened set iff it satisfies
`DialOneBase`, and that clause is **the one remaining open
seat** (named PARTIAL seam: `DialOneBase (orbitRep
allSwapBits)` — analysis suggests the base clauses are
colour-uniformity-compatible, but it is NOT proved; the
point is quoted neither in nor out).

**K-CLS-2 status: NOT fired, armed at one point.** If the
Base clause holds at allSwap, K-CLS-2 fires — a non-identity
orbit point inside the strengthened set — and the toggle
exclusion gains exactly one exception, the uniform triple
swap (whose weights still differ from the table's at every
colour's u_R seat, so Grade W is untouched either way). If
it fails, the exclusion is complete over the orbit. The
deciding brick is CLS-2b (prove or kill the Base clause at
allSwap; both outcomes land at full rank). The pre-registered
group-law seam ((ℤ/2)⁴ composition) also stands open, named
`groupLaw_partial_seam`.

## Fences

NO CLAIM; **Dial 1: 0.** Classification state after this
landing: Grade T is decided at 15/16 orbit points with the
16th reduced to one clause; Grade W open; Grade R unposed.

**Census after landing: 11,869 strict / 12,219 total / 402 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
