# GR-PROP-2 LANDING DOSSIER — 2026-11-01

**Item:** GR-PROP-2 (wave-mode identification at the MAX-3 gate: the
modes of `maxwellOpCE` identified as PROP-1's wave modes, the
longitudinal sector stationary), per the ratified GR-PROP pin and the
coordinator pack (`pack-prop-2.md`). Gate ruling on the record:
PROP-2 fired on MAX-3's LANDED clauses 1, 2, 3, 5 — the mode
identification is M5's spectrum named; MAX-3 clause 4 (the gap as a
bound) is NOT a PROP-2 input and was not consumed, implied, or
assumed anywhere.

**Status: PARTIAL at the named completeness seam, stated exactly.**
The existence, frequency, preservation, and
longitudinal-stationarity directions are discharged. The "exactly"
direction — every mode of `maxwellOpCE N` is one of the named
Fourier modes — is NOT discharged and NOT asserted: the landed
MAX-3 clauses provide no completeness/dimension count over the
full constructed family (cross-momentum independence plus a
link-space dimension count), which an exhaustion theorem would
need. The seam is stated verbatim on the module's face.

**Artifact:** `lean/ThetLogos/WaveModeIdentification.lean` — strict
20, defs 4. Verified by the coordinator in the main tree (build
green, 3687 jobs); all 11 printed headlines on exactly
`[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.

## What landed

Generic transport (covers every real mode MAX-3 names, including
the clause-2 witnesses): `maxwellOpCE_modeVecC` (real eigenmodes
complexify to eigenmodes of `maxwellOpCE` at the cast eigenvalue,
via PROP-1's `maxwellOpC_ofReal_apply`); `modeFreq_modeVecC`
(ModeFreq transport); `modeVecC_phase` (the wave family acts by the
evolution phase at the mode's frequency).

Fourier modes at the named frequency (frequency supplied/named,
never existentially quantified): `cosModeC`/`sinModeC` are
eigenmodes of `maxwellOpCE` at `(maxwellTransverseEig N k : ℂ)` for
spatial momenta (zero time component), under the constructible
side conditions (2 ≤ N, gauge-transversality
`∑ ν, A ν * modeSin K ν = 0`); ModeFreq instance theorems;
preservation under `linkWaveFamily` (PROP-1's
`modeFreq_linkWaveFamily`); the phase law; and
`exists_modeFreqC_transverse` — occurrence only, from MAX-3
clause 1, explicitly not completeness.

Longitudinal sector (finite arithmetic only): `gaugeModeC` is an
eigenmode at 0 (`gaugeModeC_eigen_zero`, transport of MAX-2's
`maxwellOp_gaugeAngle`); ModeFreq at 0; and
`gaugeModeC_stationary` — the family's stationary sector, proved as
the phase action at frequency 0 (`evolPhase 0 t = 1`), stated on
the face as eigenvalue arithmetic, never as physics.

## Fences

NO CLAIM — no Millennium problem is claimed solved or advanced; no
part of any official statement is claimed. No `PoseObjBFreqShadow`
instance is asserted anywhere (that decision is PROP-3's, gated on
this brick and carrying a mandatory BRIDGE-1 check). No
gravity/propagation-as-physics language; the frequency is the
spectral datum of `maxwellOpCE` as PROP-0 registered it. Dials 0/4;
Dial 2 (Jeff's chair) unmoved — the PROP line's vocabulary now
receives a frequency-shadow candidate at PROP-3; receivable is not
seated.

**Census after landing: 10,711 strict / 10,792 total / 361 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
