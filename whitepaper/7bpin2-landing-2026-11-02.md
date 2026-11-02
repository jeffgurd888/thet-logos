# 7B-PIN-2 LANDING DOSSIER — 2026-11-02

**Item:** 7B-PIN-2 (SHELF-7b-disc repair) — interior
re-freeze of B2/B3 + the in-tree decision on the frozen
forms.

## VERDICT: FULL — the live chain is re-frozen against interior presentations, and the frozen B2/B3 are REFUTED in-tree (not merely clouded)

**Artifact:** `lean/ThetLogos/Shelf7bPin2.lean` — strict 8,
defs 2 (in the 6–14 band). Verified by the coordinator in
the main tree (build green, 2982 jobs); the decision
headlines on exactly `[propext, Classical.choice,
Quot.sound]`. The frozen Props in `Shelf7bPin.lean` stand
untouched beside their verdicts (relabeling rule).

**Part 1 — the live forms:** `Shelf7bB2ForwardInterior` and
`Shelf7bDiscInterior` — B2/B3 quantified over an interior
presenting radius R₀ with `(spectralRadius ℂ a).toReal <
R₀ < R`, where GATE-B1's B1a (coefficient independence) and
corrected B1c (scalar values = f) make the chain sound.
GATE-B2′ (12–25) and GATE-B3′ (25–45, B3's PARTIAL seam as
registered) are priced against them on the face.

**Part 2 — the decision, in-tree:** for GATE-B1's witness f
(0 on the open unit ball, 1 on the circle),

```
shelf7bB2Forward_not : ¬ Shelf7bB2Forward (0 : A) f 1
shelf7bDisc_not      : ¬ Shelf7bDisc (0 : A) f 1
```

The chain: f is DiscHolomorphic at R = 1 (it vanishes on the
open ball); `spectralRadius ℂ 0 = 0 < 1`; 0 ∈ spectrum(0);
landed `discCoeff f 1 0 = 1`; the new `hfcDisc_at_zero`
(`hfcDisc 0 c = c 0 • 1` — higher terms vanish by
`zero_pow`) gives `hfcDisc 0 (discCoeff f 1) = 1`; and
`spectrum.zero_notMem` contradicts `f 0 = 0` lying in that
spectrum. The Disc refutation is the contraposition through
`shelf7bDisc_imp_forward`. So the boundary-presentation
defect is decided at all three frozen statements — B1c,
B2Forward, Disc: **all three are false as frozen, each
refuted in the tree**, and the interior chain is the only
live form of 7b-disc's back half.

## Fences

7b-disc only; NOT 7b-in-full. NO CLAIM; dials 0/4.

**Census after landing: 12,116 strict / 12,486 total / 413 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
