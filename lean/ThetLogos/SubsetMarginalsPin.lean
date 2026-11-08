import Mathlib.Tactic
import ThetLogos.SiteEntropyMap

namespace ThetLogos

/-!
# ThetLogos.SubsetMarginalsPin — PIN (interface; frozen names; 0 strict)

**Commission:** brick **H-1 (subset marginals)** of the priced
obstruction package in the holographic-shadow scoping
(`~/workspace/your_files/holographic-shadow-scoping-2026-11-07.md`,
§4), enrolled by Jeff's **"build all you can"** (2026-11-07) on that
scoping's menu. **Price: band S–M** (the scoping's price for H-1).
This pin is the interface brick: definitions + statement pins only,
frozen names, **0 strict**. The content module
`ThetLogos.SubsetMarginals` proves the frozen forms.
**Status: PIN ONLY (this file). NO CLAIM. Dials 0/4.**

## What this seat is

The scoping's verdict on Jeff's fragment "I think 4D entropy is 3d
gravity" was **(C) NOT STATEABLE**, for one named reason: the corpus
had no subset-level entropy theory. Its marginals existed only for
**single sites** (`SiteEntropyMap.margWeight w i`, one `i` at a
time); there was no subset-marginal weight, no entropy of a region.
H-1 is the first brick of the priced repair: `margWeight`
generalized from a site `i` to a subset `s : Finset κ` — the
marginal weight on the subtype configuration space
`(∀ i : s, X i)` — its `IsProbWeight` theory, and a region entropy
`regionEntropy w s := entropyW (margWeightSet w s)`, with the
single-site map recovered as the singleton case. Routine
generalization of landed machinery; the honest price is in the
dependent-type bookkeeping over subtype configuration spaces
(scoping §4).

## The fences (on the face)

- **Vocabulary, not the claim.** This brick is subset-entropy
  VOCABULARY. Landing it does not make the holographic fragment
  stateable, does not state any area-shaped bound, and does not
  approach a gravity object (Dial 2 = 0). Two further bricks stand
  between this vocabulary and even the *formability* of an
  area-shaped statement: **H-2** (conditional entropy and chain
  rules at subset level — it builds on the names frozen here) and
  **H-3** (a locality seat: an adjacency graph and a Markov-type
  hypothesis). **The choice of locality hypothesis in H-3 is
  Jeff's design decision — not this brick's, and not any lane's.**
  The bound itself is unpriced (scoping §4).
- **Dial-neutral, dial-ineligible.** H-1 is honest
  information-theory bookkeeping in its own right (scoping §4);
  it moves no dial and is evidence for no claim.
- **K-HOL-PROXY — ARMED, NOT FIRED** (scoping §5). No statement
  in this package renames a cardinality "4D", a boundary count
  "area", or a counting bound "gravity". This brick names no
  boundary and no adjacency: a subset `s` here is any `Finset κ`,
  distinguished by nothing.
- **K-HOL-INFLATE — ARMED, NOT FIRED** (scoping §5). No landed
  text presents a counting bound as holography or as a gravity
  object. `regionEntropy`'s bounds are the whole-region counting
  bounds consumed from `FiniteEntropy` — volume-shaped, like
  every bound in the parent seat.
- **K-HOL-DUP — ARMED, prospective** (scoping §5). It fires on
  any "boundary control" exhibit that merely restates
  `SiteEntropyMap`'s product-weight additivity in holographic
  dress. This brick is not that shape: the subset marginal is
  genuinely absent vocabulary (the scoping's deciding reason),
  stated for arbitrary weights, with no product hypothesis and
  no boundary language anywhere in it.

## Form refinements, logged on the face (not silent deviations)

- The marginal is defined by the restriction-equality filter —
  configurations whose restriction to `s` equals the given
  subtype configuration — mirroring `margWeight`'s fiber form, so
  the fibering proofs of the parent seat transport at their
  landed shape.
- The scoping's "single-site map recovered as the singleton
  case" is rendered in two forms: the pointwise identity
  (`MargWeightSetSingletonForm` — the subset marginal at `{i}`
  is the single-site marginal read at the subtype configuration's
  unique coordinate) and its entropy consequence
  (`RegionEntropySingletonForm` — `regionEntropy w {i} =
  siteEntropy w i`, via `FiniteEntropy`'s landed relabeling
  invariance `entropyW_comp_equiv`).
- The content module additionally lands
  `sum_margWeightSet_mul_log`, the subset analog of the parent
  seat's §1 refibering lemma `sum_margWeight_mul_log`: the
  working identity H-2's chain rules will consume. It is a
  supporting lemma of the marginal machinery, not a fifth form.

## The definitions and the four frozen statement forms

This pin carries the brick's definitions and states the four
forms as `Prop`s. Names are FROZEN at this commit; the content
module proves theorems whose statements are these forms
verbatim.

1. **The `IsProbWeight` theory** — `MargWeightSetProbForm`:
   the subset marginal of a probability weight is a probability
   weight, at every subset.
2. **The region entropy's basic bounds** —
   `RegionEntropyBoundsForm`: for a probability weight, the
   region entropy is nonnegative and at most
   `log (card (∀ i : s, X i))` — `FiniteEntropy`'s two bounds
   consumed at the marginal, exactly as `SiteEntropyMap` §2
   consumes them for `siteEntropy`.
3. **Singleton recovery, marginal form** —
   `MargWeightSetSingletonForm` (see the refinement note).
4. **Singleton recovery, entropy form** —
   `RegionEntropySingletonForm` (see the refinement note).
-/

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*}
  [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

/-- The marginal weight of `w` on the subset `s`: the total
weight of all configurations whose restriction to `s` equals
`z`, where `z` ranges over the subtype configuration space
`(∀ i : s, X i)`. The generalization of `margWeight` (the
singleton case) from a site to a subset — scoping §4, brick
H-1. Tier T1 (definition). -/
def margWeightSet (w : (∀ i, X i) → ℝ) (s : Finset κ) :
    (∀ i : s, X i) → ℝ :=
  fun z => ∑ y ∈ Finset.univ.filter
    (fun y => (fun i : s => y i) = z), w y

/-- The entropy of the region `s` under `w`: the entropy of
the subset marginal, with `entropyW` consumed from
`FiniteEntropy` at its exact landed shape. Tier T1
(definition). -/
noncomputable def regionEntropy (w : (∀ i, X i) → ℝ)
    (s : Finset κ) : ℝ :=
  entropyW (margWeightSet w s)

/-- **Frozen form (1) — the `IsProbWeight` theory.** The
subset marginal of a probability weight is a probability
weight, at every subset `s`. Tier T1 (statement pin). -/
def MargWeightSetProbForm : Prop :=
  ∀ (w : (∀ i, X i) → ℝ) (s : Finset κ),
    IsProbWeight w → IsProbWeight (margWeightSet w s)

/-- **Frozen form (2) — the region entropy's basic bounds.**
For a probability weight, the entropy of any region is
nonnegative and at most the log of the region's configuration
count — `FiniteEntropy`'s bounds consumed at the subset
marginal. Tier T1 (statement pin). -/
def RegionEntropyBoundsForm : Prop :=
  ∀ (w : (∀ i, X i) → ℝ) (s : Finset κ), IsProbWeight w →
    0 ≤ regionEntropy w s ∧
      regionEntropy w s
        ≤ Real.log (Fintype.card (∀ i : s, X i) : ℝ)

/-- **Frozen form (3) — singleton recovery, marginal form.**
The subset marginal at the singleton `{i}` is the single-site
marginal, read at the subtype configuration's unique
coordinate `z ⟨i, _⟩`. Tier T1 (statement pin). -/
def MargWeightSetSingletonForm : Prop :=
  ∀ (w : (∀ i, X i) → ℝ) (i : κ)
    (z : ∀ j : ({i} : Finset κ), X j),
    margWeightSet w {i} z
      = margWeight w i (z ⟨i, Finset.mem_singleton_self i⟩)

/-- **Frozen form (4) — singleton recovery, entropy form.**
The entropy of the singleton region `{i}` is the site entropy
at `i`: the single-site map is the singleton case of the
region map. Tier T1 (statement pin). -/
def RegionEntropySingletonForm : Prop :=
  ∀ (w : (∀ i, X i) → ℝ) (i : κ),
    regionEntropy w {i} = siteEntropy w i

end ThetLogos
