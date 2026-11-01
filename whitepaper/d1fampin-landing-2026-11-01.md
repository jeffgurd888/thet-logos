# D1-CMP-FAM PIN LANDING DOSSIER — 2026-11-01

**Item:** D1-CMP-FAM (Dial-1 lane) — statement pin, per the
compensator scoping §2.3/§4 Rank 2. A NEW ENTRY under the
relabeling rule; D1-A, D1-A′, D1-C3, D1-CMP stand as landed
beside it.

**Status: PIN LANDED.** The pin asserts none of its
pre-checks; the checks gauntlet follows. No forcing is
attempted at this set, ever, in this entry.

**Artifact:** `lean/ThetLogos/DialOneGammaFamilyPin.lean` —
strict 8, defs 12 (top of the pack's band). Verified by the
coordinator in the main tree (build green, 3137 jobs);
headlines on exactly `[propext, Classical.choice, Quot.sound]`.

## What is pinned

One definition pattern — diagonal seat projections
(`seatProj`, partner-closed 0/1 indicators; no table values
named): `lepProj` (pairs {0,1,8,9}), `colProj c` (pairs
{2+2c, 3+2c, 10+2c, 11+2c} per colour), `eRProj` ({9}). The
four clean-tier functionals in C3's pattern (γ_F composed
with a projection, π at the first power): `C3lep`, `C3col c`,
`FeR`; the family `GammaFamily` and the strengthened set
`DialOneStrengthenedFam := DialOneBase ∧ C3 ∧ GammaFamily`.

**F_eR's flag is on the face:** a two-seat tie in raw weights
holding for π₁ at exactly one pair — that accident its entire
motivation, the clean tier's weakest member, and
**load-bearing** against the lepton swap (without it the
toggle kernel is 16, not 8). The family is reported with and
without it.

Pre-checks registered for the checks module: π₁ holds every
clause (expected (0,0) each — new computations); piDouble
fails the family by F_eR alone (C3lep and the colour clauses
hold for it — the compensation is internal to the lepton
sector); the three per-colour quark swaps' family vanishing,
base membership, and non-proportionality. Kills on the face:
**K-CMP-F1** (a quark swap in base + family with non-table
weights ⇒ forcing at base + clean family FALSE,
permanently), **K-CMP-F2** (π₁ fails a clause ⇒ mis-posed,
dies at full rank), **K-CMP-F3** (piDouble passes the whole
family ⇒ the F_eR arithmetic was wrong). The outcome fence
stands: swaps failing base yields exactly a toggle-level
exclusion — not a forcing theorem.

**Dial 1: 0. NO CLAIM.**

**Census after landing: 11,561 strict / 11,852 total / 395 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
