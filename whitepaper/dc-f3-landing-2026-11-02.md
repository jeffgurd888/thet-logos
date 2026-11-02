# DC-F3 — LANDING (2026-11-02): mixing — what is conserved, what is not

**Line:** DUAL-CURRENT (working label). Charter:
`~/workspace/your_files/dual-current-theory-charter-2026-11-01.md`
(§3 F3). **The finite core F1–F3 is now complete.**
**Decision of record:** Jeff, 2026-11-01 22:33 EST — "3 fire."
**Module:** `ThetLogos/DualCurrentMixing.lean` (new; imports the
landed `DualCurrentRing` and `DualCurrentLeedskalnin`, unmodified).
**Count:** strict 10 / defs 4 (+1 private helper, uncounted).
**Build:** GREEN on build 2 (build 1 failed on one rewrite inside
`dcHelicity_smul`; proof body only, statement untouched); parent
re-build green.
**Axioms:** all ten theorems exactly `propext`, `Classical.choice`,
`Quot.sound`; no `sorryAx`.

> Named for Edward Leedskalnin (1887–1951), builder of Coral Castle,
> whose *Magnetic Current* (1945) posed the counter-streaming picture
> this theory makes checkable. Named for the question he asked, not
> for his answers — his answers keep their audited grades (see §6 of
> the charter).

## The question

The mixing move `dcMix t jp jm` interpolates the two channels
(`jp' = (1−t) jp + t jm`, `jm' = t jp + (1−t) jm`) — the discrete
analogue of cross-stream diffusion. Which functionals survive it?

## Verdicts

**CONSERVED — proved in general (every ring, every t):**

- `dcMix_net` — the net field is preserved pointwise. Hence
  (`dcMix_dcEnergy_net`, `dcMix_dcHelicity_net`) the net energy and
  the net helicity are conserved under mixing: conservation lives
  at the level of the SUM of the channels, nowhere else.
- `dcHelicity_add` — helicity of a sum splits as
  `H[jp + jm] = H[jp] + H[jm] + X[jp, jm]` with the cross-helicity
  `X = dcCrossHelicity` an explicit symmetric bilinear term: the
  failure of channel-wise additivity is exactly measured, not
  hidden.
- `dcHelicity_smul` — `H[c • j] = c^2 * H[j]`.

**NOT CONSERVED — the naive channel-wise hope is KILLED at T1.**
Witness pair at n = 2, t = 1/2: `dcExA = (1, 0)`, `dcExB = (0, 1)`
(each theorem states both values; the pair of values is the kill):

- channel energy of the first mixed channel: **1/4 ≠ 1**
  (`dcMix_channelEnergy_counterexample`);
- its channel helicity: **−1/4 ≠ −1**
  (`dcMix_channelHelicity_counterexample`);
- total channel energy: **1/2 ≠ 1**
  (`dcMix_totalChannelEnergy_counterexample`);
- churn: **−1/2 ≠ 0** (`dcMix_churn_counterexample`) — mixing
  CREATES pointwise opposition out of two non-opposing channels;
- cross-helicity: **0 ≠ 2** (`dcMix_crossHelicity_counterexample`).

So the charter's F3 as naively hoped — conservation channel by
channel — is **false**, and the in-tree counterexamples are the
verdict. What survives is sharper: conservation is a property of
the net field alone, and mixing manufactures churn. Both halves are
theorems; neither half is a dial event, an energy statement, or a
coupling (K-DC-2 / K-DC-3 stand; K-DC-4: none of this touches the
T4 anchors).

**NO CLAIM. This line moves no dial; dials 0/4.**

## Line status

**DUAL-CURRENT finite core COMPLETE as chartered**: F1 (ring +
helicity bookkeeping, incl. the identity H = −½Σ(Δj)²), F2
(Leedskalnin configurations + projection fixed points), F3 (mixing:
net conservation proved, channel-wise conservation killed). Any
successor (F4 candidates named in the charter — open chains,
reflection positivity, continuum reading) is a NEW registration,
not part of this firing.

**Census after landing: 12,617 strict / 13,125 total / 443 counted
modules** (increment +10 strict / +4 defs / +1 module).
