# GR-PROP-0 — LANDED FULL: the propagation registration pin (the wave family cited, the perturbation frozen as an operator, both shadow predicates verbatim)

**Verdict: GR-PROP-0 FULL. The GR-PROP line's interface is frozen as its own verified commit — the third and last pin of the gravity vocabulary map. The wave family is registered as what it honestly is (the corpus's landed unitary group, cited — no new evolution theory), the mode/frequency vocabulary is defined over the named seat operator, the line's perturbation is frozen as a concrete operator definition in owned vocabulary, and both PoseObjB shadow predicates (freq half, path half) are registered verbatim with their ceilings. PROGRAM CEILING, on this dossier's face: vocabulary — it seats NO gravity object; Dial 2 = 0 under every outcome. NO CLAIM. Dials 0/4.**

## What the pin registers (`WaveFamilyPost.lean`, new module; working label — Jeff names)

- **`waveFamily hT t := evolOp hT t`** — a citation-registration of `SchrodingerDynamics`' landed one-parameter unitary group, with read-backs `waveFamily_add` (citing `evolOp_add`), `waveFamily_isometry` (citing `evolOp_isometry`), `waveFamily_zero`, `waveFamily_unitary_apply`. On the face: **K-GR-SMUG instance (ii)** — a "wave family" that is `maxwellOp` renamed, landing without the `evolOp` weld and its proved group law, is the static-form smuggle, void on sight.
- **`ModeFreq S v ω : Prop := v ≠ 0 ∧ S v = ω • v`** — an eigenpair of the named seat operator, `ω` registered as the mode's frequency. Intended instantiation on the face: the complexified `maxwellOp N` (the weld is GR-PROP-1, gated on MAX-2) and MAX-3's Fourier modes at named momentum `k`, frequency the M5 eigenvalue `4·Σ sin²(πkᵢ/N)`, longitudinal modes at 0. **K-GR-SMUG instance (iii)** on the face: a frequency taken from any operator other than the named spatial seat operator fires the kill.
- **`FreqShift S S' v ω ω' : ℝ := ω' − ω`**, and **the perturbation, frozen as a definition**: `onePlaqDefectOp N P₀ := maxwellOp N + plaqRankOneOp P₀`, where `plaqRankOneOp P₀ θ ℓ = plaqSign P₀ ℓ * plaqAngle P₀ θ` — in form vocabulary, the `maxwellQuad` form plus the plaquette-angle rank-one term `(plaqAngle P₀ θ)²` at the named plaquette `P₀`, entirely in `MaxwellQuadPost`'s owned vocabulary. PROP-3's perturbation is this operator; it cannot drift.
- **The freq-shadow predicate, verbatim:** `PoseObjBFreqShadow N P₀ v ω ω' statedShift : Prop` := `ModeFreq (maxwellOp N) v ω ∧ ModeFreq (onePlaqDefectOp N P₀) v ω' ∧ statedShift = FreqShift (maxwellOp N) (onePlaqDefectOp N P₀) v ω ω'` — mode, perturbation, seat, and stated shift (sign included) are supplied parameters, the shift compared by equation, never existentially quantified (the GEO-0 constant discipline; K-GR-VAC struck in advance on the face). Ceiling on the face: a finite operator's eigenvalue arithmetic — not bending, not redshift.
- **The path-shadow predicate, verbatim:** `PoseObjBPathShadow N Dp x y statedLength : Prop := statedLength = Dp x y ∧ geoDist N x y ≤ statedLength` — a supplied perturbed distance function and a supplied stated length, registered under its graph-only ceiling (the word "bending" appears only inside that fence). It is the optional GR-PROP-4's predicate — registered here because the pin freezes the line's words; PROP-4 remains unfired.
- **Modular flow excluded on the face (G2):** `diagFlow` fixes its own Gibbs state exactly and is not a candidate propagator/separator for any predicate in this line. The complexification weld seam (real `maxwellOp` vs complex `evolOp`; spectrum unchanged; a real-rotation variant a fenced alternate, not priced) is named in advance for PROP-1. Kills on the face: K-GR-VAC, K-GR-SMUG (ii)+(iii), K-GR-LAUNDER, K-GR-STAB, K-GR-BUY, K-PROP-STATIC. Noun audit: all hits inside fences/ceiling sentences.

## Parent verification (from disk)

- Canonical counter: **strict=12, defs=7** (inside the S estimate 8–14); zero attribute-prefixed declarations, zero "sorry"/`native_decide` tokens; no landed file edited.
- Parent module build green, independently reproduced (3,674-job closure).
- Parent axiom check: `waveFamily_add`, `waveFamily_isometry`, `poseObjBFreqShadow_unfold` on exactly `[propext, Classical.choice, Quot.sound]` (builder's sweep: all 12 read-backs on subsets of the standard three — one on no axioms — reported as such).

## Census

10,056 → **10,068 strict** / 10,133 → **10,145 attribute-inclusive** / 339 → **340 modules** (delta +12 strict, +1 module). README badge and body both updated at this landing and verified against the committed README.

## Backers since last landing

No change to the backer roll since the last landing.
