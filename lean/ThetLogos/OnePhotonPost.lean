import ThetLogos.SMHiggsBreaking

/-!
# ThetLogos.OnePhotonPost — the one-photon question-post

**Status: definitions only. NO CLAIM.**

Jeff Gurd coined **"the one photon theory"** on 2026-10-26; the
phrase is his, and stays his regardless of any verdict below. His
own filed line prices the phrase exactly: it is *the room's door,
not its furniture*. This module is that door: it posts the question
the phrase can honestly become, records what died at the door, and
points at the room where the live part was answered
(`ThetLogos.PhotonUniqueMassless`).

The posted question — Jeff's "what is the 'one'?", sharpened to the
one reading that is theorem-shaped (reading R3′ of the 2026-10-27
scoping):

> Within the finite assembly, the photon is the **unique**
> massless gauge direction: exactly one line in the gauge sector
> stays massless after breaking, and it is the photon line.

**What died at this door — the Wheeler reading (R1), KILLED.**
The one-electron universe (Wheeler to Feynman, spring 1940; T4)
reads every electron as one worldline zigzagging through time,
antiparticles its return legs. The photon version breaks at three
distinct points, each fatal to a different reading of "one":

- **(O1) Own antiparticle.** The zigzag's whole payload is the
  forward/backward pairing; a photon is its own antiparticle, so
  a return leg is indistinguishable from an outgoing photon and
  the pairing collapses into tautology.
- **(O2) Null path.** A photon's path is null: no timelike
  worldline, no proper time, nothing to zigzag with.
- **(O3) Number not conserved.** Photons are created and destroyed
  freely; there is no conserved photon number for a single "one"
  to keep the books on.

**The other readings, tiered.** (R2) *One field seen everywhere* —
one electromagnetic field, photons its excitations — is true and
standard (T4 background); as a bare statement it has no house
content, and acquires any only relativized to the assembly, which
is R3′. (R3) *Light as the single seen-through medium* is Jeff's
doctrine (T5); it stays doctrine, anchors to R3′ under the
Interpretive Conservation Principle, and is not a build item.

**Fence.** This is a **photon** question. Nothing posted here is a
gravity object, and Dial 2 is unaffected by this line in either
direction. The couplings and the VEV in the question are the
assembly's T2 inputs; the statement is classical and
assembly-internal.

This module contains definitions only: no theorem, no proof
obligation discharged, and no placeholder.
-/

namespace ThetLogos

/-- The readings of "the one" distinguished at the door.

Organizational labels only (the `Q7DFTPost` convention): they name
the readings so the tiering in the header is inspectable; they
carry no mathematical content. -/
inductive OnePhotonReading where
  | wheelerParticle
  | oneField
  | seenThroughMedium
  | assemblyUniqueMassless
deriving DecidableEq, Repr

/-- **The photon line** (definition; the assembled sector's unique
massless direction, as a predicate on field values).

A field tuple `(W1, W2, W3, B)` lies on the photon line when the
charged fields vanish and the neutral pair is proportional to
`(g′, g)` — the combination `higgs_photon_direction_massless`
proved massless. -/
def onPhotonLine (g g' W1 W2 W3 B : ℝ) : Prop :=
  W1 = 0 ∧ W2 = 0 ∧ ∃ t : ℝ, W3 = t * g' ∧ B = t * g

/-- **The one-photon question, sharpened form R3′** (definition; a
posted question, not a theorem — its answer is built in
`ThetLogos.PhotonUniqueMassless`, under exactly these hypotheses).

For every choice of the assembly's inputs with `v ≠ 0` and
`g ≠ 0`, the Higgs mass form `higgsMassQuad` vanishes exactly on
the photon line: the photon is the unique massless gauge
direction of the finite assembly. The `g ≠ 0` hypothesis is the
one the source's algebra demands — at `g = 0` the charged
directions are massless too, since the SU(2) coupling is off. -/
def onePhotonQuestion : Prop :=
  ∀ (g g' v W1 W2 W3 B : ℝ), v ≠ 0 → g ≠ 0 →
    (higgsMassQuad g g' v W1 W2 W3 B = 0 ↔
      onPhotonLine g g' W1 W2 W3 B)

end ThetLogos
