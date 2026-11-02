# CLS-3a LANDING DOSSIER — 2026-11-02

**Item:** CLS-3a (Dial-1 classification lane) — the lepton
chapter of Grade T.

## VERDICT: FULL — the lepton toggle group has exactly one strengthened-set point; the chapter closes at the C3/family level, no Base analysis

**Artifact:** `lean/ThetLogos/DialOneLeptonChapter.lean` —
strict 18, defs 1 (in the 10–20 band). Verified by the
coordinator in the main tree (build green, 3141 jobs); all
audited headlines on exactly
`[propext, Classical.choice, Quot.sound]`.

**The missing object, defined:** `piEFlip a := pi1 a +
Matrix.single s9 s9 (a.u1 − star a.u1)` — pi1 plus ONLY
piDouble's e_R single (verbatim from the D1-CMP pin), with
read-backs (its step is the s9 single; seat values at s8/s9;
the group read-back `piDouble a = piFlip a + (piEFlip a −
pi1 a)`; distinctness from pi1, piFlip, piDouble, witnessed).

**Two independent exclusions, both exact:** piEFlip fails
**C3** — `Tr (γ_F · piEFlip (u1Gen α β)) = −2αi`, witness
(1, 0) — and independently fails **F_eR** —
`Tr (γ_F · eRProj · piEFlip (u1Gen α β)) = −2αi` (its single
lives exactly on the F_eR seats {9, 25}; pi1's sub-sums
vanish by ℤ-shadow decide). Either alone excludes it from
the strengthened set.

**Chapter headline:**

```
lepton_toggle_membership :
  ∀ π ∈ ({pi1, piFlip, piEFlip, piDouble} : Finset _),
    DialOneStrengthenedFam π ↔ π = pi1
```

assembled from landed parts only (piFlip out by C3, landed
in the D1-C3 checks; piDouble out by F_eR, landed in the FAM
checks; piEFlip out by both, this brick; pi1 in, landed).
The lepton (ℤ/2)² chapter of Grade T is CLOSED. The module
records on its face that no Base analysis was used or needed
(the lepton points' Base status is decided only for
piDouble, landed IN base in the D1-CMP checks).

## Fences

NO CLAIM; **Dial 1: 0.** Grade T state: the lepton chapter
closed; the quark orbit decided at 15/16 points with the
uniform triple swap's Base clause the one open seat
(CLS-2b, in flight). Grade W open; Grade R unposed.

**Census after landing: 11,930 strict / 12,286 total / 406 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
