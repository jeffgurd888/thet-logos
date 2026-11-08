import Mathlib.Tactic
import ThetLogos.SubsetMarginalsPin

namespace ThetLogos

/-!
# ThetLogos.ConditionalEntropyPin — PIN (interface; frozen names; 0 strict)

**Commission:** brick **H-2 (conditional entropy and chain rules
at subset level)** of the priced obstruction package in the
holographic-shadow scoping
(`~/workspace/your_files/holographic-shadow-scoping-2026-11-07.md`,
§4), fired by Jeff's direct word **"build and run h-2"**
(2026-11-08), ahead of its original queue position on that
scoping's menu. **Price: band M** (the scoping's price for H-2).
This pin is the interface brick: definitions + statement pins
only, frozen names, **0 strict**. The content module
`ThetLogos.ConditionalEntropy` proves the frozen forms.
**Status: PIN ONLY (this file). NO CLAIM. Dials 0/4.**

## What this seat is

The scoping's verdict on Jeff's fragment "I think 4D entropy is
3d gravity" was **(C) NOT STATEABLE**, for one named reason: the
corpus had no subset-level entropy theory. Brick H-1
(`SubsetMarginalsPin` / `SubsetMarginals`, names frozen there and
consumed here unchanged) seated the first half of the repair: the
subset marginal `margWeightSet` and the region entropy
`regionEntropy`. H-2 is the second brick: **conditional entropy
at subset level and its chain rules** — the entropy of a region
given a second subset, the chain rule
`regionEntropy w (s ∪ t) = regionEntropy w t + condEntropy w s t`,
and monotonicity of region entropy under marginalization
(scoping §4). It builds on H-1's frozen names and on its working
identity `sum_margWeightSet_mul_log`, the refibering identity the
H-1 pin's face names as the one H-2's chain rules consume.

## The fences (on the face)

- **Vocabulary, not the claim.** This brick is subset-entropy
  VOCABULARY, exactly as H-1 was. Landing it does **not** make
  the holographic fragment stateable, states no area-shaped
  bound, and does not approach a gravity object (Dial 2 = 0).
  One further brick stands between this vocabulary and even the
  *formability* of an area-shaped statement: **H-3** (a locality
  seat: an adjacency graph on `κ` and a Markov-type hypothesis).
  **The choice of locality hypothesis in H-3 is Jeff's design
  decision — not this brick's, and not any lane's.** The bound
  itself is unpriced (scoping §4).
- **Dial-neutral, dial-ineligible.** H-2 is honest
  information-theory bookkeeping in its own right (scoping §4);
  it moves no dial and is evidence for no claim.
- **K-HOL-PROXY — ARMED, NOT FIRED** (scoping §5). No statement
  in this package renames a cardinality "4D", a boundary count
  "area", or a counting bound "gravity". This brick names no
  boundary and no adjacency: `s` and `t` are any `Finset κ`,
  distinguished by nothing.
- **K-HOL-INFLATE — ARMED, NOT FIRED** (scoping §5). No landed
  text presents a counting bound as holography or as a gravity
  object. `condEntropy`'s theorems are finite Shannon bookkeeping
  over subset marginals — nothing more is claimed for them.
- **K-HOL-DUP — ARMED, prospective** (scoping §5). It fires on
  any "boundary control" exhibit that merely restates
  `SiteEntropyMap`'s product-weight additivity in holographic
  dress. This brick is not that shape: conditional entropy over
  arbitrary weights is genuinely absent vocabulary (the scoping
  names "no conditional entropy" in its deciding reason), stated
  with no product hypothesis and no boundary language anywhere
  in it.

## Form refinements, logged on the face (not silent deviations)

- The scoping phrases the conditioning set as a region's
  "complement's boundary layer". No boundary-layer object exists
  until H-3 seats an adjacency and a locality hypothesis, and
  H-3 is Jeff's open decision. `condEntropy` is therefore seated
  for an **arbitrary second subset** `t`; the boundary-layer
  reading is the intended special case, available the day H-3
  exists. This widens nothing: two-subset conditional entropy is
  the general vocabulary of which the boundary-layer case is an
  instance.
- The scoping's chain rule is stated there for a region and its
  (disjoint) layer. At this level of generality **no
  disjointness hypothesis is needed**: the chain identity is the
  definition of `condEntropy` read backwards, and
  nonnegativity is monotonicity at `t ⊆ s ∪ t`. The frozen forms
  are therefore stated without a disjointness side condition —
  strictly stronger than the scoping's phrasing, with the
  disjoint region/layer case as the intended application.
- Forms (2) and (3) are two faces of one fact — marginalizing
  cannot increase entropy — mirroring H-1's singleton recovery
  appearing in two forms (marginal level, entropy level). Both
  are frozen, as the scoping names both the conditional
  entropy's chain rules and monotonicity under marginalization.
- Deliberately **not** frozen: subset subadditivity
  (`regionEntropy w (s ∪ t) ≤ regionEntropy w s +
  regionEntropy w t`). It is not in the scoping's H-2 text, and
  the pin does not grow past its charter.

## The definition and the three frozen statement forms

This pin carries the brick's definition and states the three
forms as `Prop`s. Names are FROZEN at this commit; the content
module proves theorems whose statements are these forms
verbatim.

1. **The chain rule** — `CondEntropyChainForm`: the union's
   entropy is the conditioning region's entropy plus the
   conditional entropy.
2. **Nonnegativity** — `CondEntropyNonnegForm`: for a
   probability weight, conditional entropy is nonnegative.
3. **Monotonicity under marginalization** — `RegionEntropyMonoForm`:
   for a probability weight, enlarging the region cannot
   decrease its entropy.
-/

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*}
  [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

/-- The conditional entropy of the region `s` given the region
`t`: the entropy gap of the union over `t`. The subset-level
conditional entropy of the scoping's brick H-2, seated for an
arbitrary second subset `t` (see the refinement note on the
face: the boundary-layer reading awaits H-3). Tier T1
(definition). -/
noncomputable def condEntropy (w : (∀ i, X i) → ℝ)
    (s t : Finset κ) : ℝ :=
  regionEntropy w (s ∪ t) - regionEntropy w t

/-- **Frozen form (1) — the chain rule.** The entropy of the
union is the entropy of the conditioning region plus the
conditional entropy: the scoping's chain rule
`entropy(region ∪ layer) = entropy(layer) + conditional`, at
general subset level. Tier T1 (statement pin). -/
def CondEntropyChainForm : Prop :=
  ∀ (w : (∀ i, X i) → ℝ) (s t : Finset κ),
    regionEntropy w (s ∪ t)
      = regionEntropy w t + condEntropy w s t

/-- **Frozen form (2) — nonnegativity.** For a probability
weight, the conditional entropy of any region given any other
is nonnegative. Tier T1 (statement pin). -/
def CondEntropyNonnegForm : Prop :=
  ∀ (w : (∀ i, X i) → ℝ), IsProbWeight w →
    ∀ (s t : Finset κ), 0 ≤ condEntropy w s t

/-- **Frozen form (3) — monotonicity under marginalization.**
For a probability weight, a subregion's entropy is at most the
larger region's: marginalizing a region down to a subregion
cannot increase entropy. Tier T1 (statement pin). -/
def RegionEntropyMonoForm : Prop :=
  ∀ (w : (∀ i, X i) → ℝ), IsProbWeight w →
    ∀ (s t : Finset κ), s ⊆ t →
      regionEntropy w s ≤ regionEntropy w t

end ThetLogos
