# Pitch 4, Stage 1b-A — the reflection structure pack + Wilson action split

**Date:** 2026-10-17. **Module:** `lean/ThetLogos/LatticeReflection.lean`
(1,335 lines; imports `ThetLogos.LatticeCorrelations`).
**Tier:** T1 at the finite-lattice level, throughout.
**Status: STANDS WHOLE** — all four scoped items landed at general
`(G, ρ)`, general even extent `N`, and (for the measure items) every
real `β`. None of the three pre-named PARTIAL shapes (α: Haar-level
measure compatibility only; β: through-sites only; γ: fixed stratum
enumerated, not characterized) was triggered.
**Pitch-level shape after this landing:** Stage 1b-A stands; Stage 1b
as a whole stands at **PARTIAL-δ only once 1b-B lands** (gauntlet
ruling: PARTIAL-δ = A + B, "reflection positivity stands"). 1b-B
(positivity proper), 1b-C (OS space), and 1b-D (transfer matrix)
remain priced and unbuilt.
**Parts of the official Clay Yang–Mills statement closed by this
module: 0.**

Governing spec: the Stage 1b decomposition in §1 of
`whitepaper/gauntlet-parked-fleet-2026-10-17.md`, over §6.2 of
`whitepaper/pitch-4-continuum-scoping-DRAFT-2026-10-17.md`, under §8's
five mandatory clauses, all carried verbatim in the module header.

## 1. Scoped vs landed, per item

**Item 1 — the setup, pinned as the first act. STANDS.**
All reflection content is built on Stage 0's concrete torus
`Fin 4 → ZMod N` with reflected direction `0` (the `torusShift N`
presentation of Stage 0), at general even `N`. The theorems carry
exactly the hypotheses they use: `Even N` for the reflection
arithmetic, class transport, and both measure-invariance headlines;
extent `2` is excluded as degenerate in the header (at `N = 2` both
time-link layers are fixed and the ± classes contain no temporal
plaquette; the minimal nondegenerate even extent is `4`). The
generality of Stages 0/1a in `(G, ρ)` is retained throughout; what is
*not* retained is Stage 0's abstract-`Λ` generality for the
reflection itself — provably impossible, per the gauntlet's
obstruction (the abstract presentation carries no reflection), and
the reason this campaign exists as a separate structure pack.

**Item 2 — the reflection and its fixed link stratum,
CHARACTERIZED. STANDS.**
The reflection is the scoping §6.2 **between-sites** reflection: on
sites, `reflSite x = Function.update x 0 (-1 - x 0)` (time
coordinate `k ↦ -1 - k`, spatial coordinates fixed). It is an
involution (`reflSite_involutive`), satisfies the shift calculus
`θ σ₀ θ = σ₀⁻¹`, `θ σᵢ = σᵢ θ` for `i ≠ 0`, and has **no fixed
sites** at even `N` (`reflSite_ne_self`: `2k = -1` has no solution
in `ZMod N` for `N` even). On links,
`reflLink (x, μ) = (θx, μ)` for `μ ≠ 0` and
`reflLink (x, 0) = ((σ₀)⁻¹ (θx), 0)` — a time link is named by its
base site, so its reflected base is shifted back. On configurations,
`(θU)(x, 0) = (U (reflLink (x, 0)))⁻¹` (time links are inverted,
as a reflected link is traversed backwards) and
`(θU)(x, μ) = U (reflLink (x, μ))` for `μ ≠ 0`; `reflConfig` is an
involution. The fixed link stratum is **characterized, not
enumerated** — the headline

> `reflLink_eq_self_iff`: `reflLink (x, μ) = (x, μ)` iff
> `μ = 0` and `(x 0).val ∈ {N/2 - 1, N - 1}`

is an if-and-only-if: the fixed links are exactly the time links
based in the two layers adjacent to the two reflection planes
(the plane between slices `N/2 - 1`/`N/2` and the plane between
`N - 1`/`0`). This matches the gauntlet's between-sites count
(2 fixed time-link layers at even `N`); the through-sites
alternative, which would fix two whole slices of spatial links,
was not used. PARTIAL shape (γ) is therefore not triggered.

**Item 3 — measure compatibility, at the Gibbs level for every β.
STANDS.**
Route: the configuration reflection factors as
`θ = invConfig ∘ permConfig`, where `permConfig` is the coordinate
permutation by `reflLinkEquiv` (Mathlib's `piCongrLeft`) and
`invConfig` inverts the time-link coordinates. Each factor
preserves Stage 0's product-Haar measure, giving the strong form

> `configMeasure_map_reflConfig`:
> `Measure.map reflConfig (configMeasure μG) = configMeasure μG`.

For the Gibbs measure, the density is invariant because the action
is (Item 4's corollary), the partition function is a scalar, and
the base measure is invariant, giving

> `gibbsMeasure_map_reflConfig`:
> `Measure.map reflConfig (gibbsMeasure (torusShift N) μG ρ β)`
> `= gibbsMeasure (torusShift N) μG ρ β`, for **every real β**.

PARTIAL shape (α) (compatibility only at the β = 0 / Haar level) is
therefore not triggered: compatibility holds for the Gibbs measure
itself, at every coupling.

**Item 4 — the Wilson action split. STANDS.**
Plaquette indices `p = (x, μ, ν)` with `μ < ν` (the action's index
set, `plaqIndex`) are classified by `plaqTimeHi p`, the highest
time slice the plaquette occupies (`(x 0).val + 1` if `μ = 0`,
else `(x 0).val`): **positive** if `plaqTimeHi < N/2`, **negative**
if `(x 0).val ≥ N/2` and `plaqTimeHi < N`, **crossing** otherwise.
Spatial plaquettes are never crossing; a temporal plaquette is
crossing iff it is based at time `N/2 - 1` or `N - 1` — precisely
the plaquettes standing on the fixed link layers of Item 2. The
split is proved as an equality of real numbers for every
configuration:

> `wilsonAction_split`: `S = S₊ + S₋ + S₀`,

and the three pieces transport under reflection as

> `wilsonActionPlus_reflConfig`: `S₊ (θU) = S₋ (U)`;
> `wilsonActionMinus_reflConfig`: `S₋ (θU) = S₊ (U)`;
> `wilsonActionZero_reflConfig`: `S₀ (θU) = S₀ (U)`.

The crossing piece is invariant **term by term**: the reflected
index map `refPlaq` fixes every crossing index pointwise
(`refPlaq_eq_of_isZeroPlaq` — at the two crossing layers
`θx = σ₀x` exactly cancels the reflected base shift). Corollary:
`wilsonAction_reflConfig`, `S (θU) = S (U)` for every `U`.

The engine under the transports is the plaquette transport
headline

> `plaquetteDensity_reflConfig`: the plaquette density at the
> reflected base site of `θU` equals the density at `x` of `U`,

proved from the factor-level identities: spatial plaquettes
transport exactly; temporal plaquettes transport as a
conjugate-of-inverse,
`plaquette (θU) ((σ₀)⁻¹ θx) 0 ν = (U (x,0))⁻¹ (plaquette U x 0 ν)⁻¹ U (x,0)`,
whose density is unchanged because the trace absorbs conjugation
and inversion (`trace_repMatrix_conj`, `repMatrix_inv`, and the
star-trace identity, all Stage 0 / in-module).

## 2. What the split says, in plain terms

Split the Wilson action's plaquettes by where they sit in the time
direction. `S₊` is the sum over plaquettes lying entirely in the
first half of the time circle (slices `0 … N/2 - 1`); `S₋` is the
sum over plaquettes lying entirely in the second half
(`N/2 … N - 1`); `S₀` is the sum over the plaquettes that straddle
one of the two reflection planes — exactly the temporal plaquettes
based at slice `N/2 - 1` (crossing the mid-plane) or slice `N - 1`
(crossing the seam). Reflection swaps the two halves, so `S₊` and
`S₋` are mirror images of each other (`S₊ ∘ θ = S₋`), and it fixes
each crossing plaquette individually, so `S₀` is unchanged plaquette
by plaquette. This `S₊ / S₋ / S₀` decomposition with these three
transport identities is the exact combinatorial input that the
reflection-positivity argument of Stage 1b-B consumes (the cross
terms between the halves are what positivity is made of). This
module proves the structure only: **no positivity statement is
proved or claimed here.**

## 3. Verification record

- Targeted build `lake build ThetLogos.LatticeReflection`
  (Lean/Mathlib pinned v4.35.0-rc3): **green, 3,392 jobs**;
  `.lake/build/lib/lean/ThetLogos/LatticeReflection.olean`
  confirmed present after the build (1,515,960 bytes).
- **67 theorem/lemma declarations** in the module (column-0 grep
  convention), plus 16 definitions/abbrevs. Program total:
  2,216 + 67 = **2,283**.
- **Zero `sorry` / `admit`** in the module (the only grep hit is
  the word "sorrys" in the header's honesty ledger).
- **Axiom audit** (`#print axioms`, scratch file, `lake env lean`):
  `reflLink_eq_self_iff`, `configMeasure_map_reflConfig`,
  `plaquetteDensity_reflConfig`, `wilsonAction_split`,
  `wilsonActionPlus_reflConfig`, `wilsonAction_reflConfig`, and
  `gibbsMeasure_map_reflConfig` each depend on exactly
  `[propext, Classical.choice, Quot.sound]` — the standard three,
  no others.
- The module is **not** in the root import list (house pattern for
  new modules; disclosed here and in the header). It is verified by
  the targeted build above.

## 4. Accommodations and disclosures

- **`[MeasurableInv G]`** is an added section-level instance
  hypothesis in the measure sections (needed for measurability of
  coordinate inversion and Mathlib's `measurePreserving_inv`).
  Stage 0/1a's concrete instances (Circle, unitary groups) satisfy
  it; the hypothesis is stated, not hidden, in the Stage 0/1a
  section-hypothesis style.
- The class predicates `IsPosPlaq` / `IsNegPlaq` / `IsZeroPlaq`
  are `abbrev`s (reducible definitions), deliberately: filter
  decidability then synthesizes the canonical instances and the
  three classes share one trichotomy with no instance mismatch.
- `refPlaqSite_zero_val` (the reflected temporal base value) needs
  `2 ≤ N` — at `N = 1` its intermediate `a ≠ 0` step is false
  (`ZMod 1` is trivial); every consumer runs under `Even N`, which
  supplies `2 ≤ N`.
- No `set_option` accommodations are used anywhere in the module.
- No positivity, no OS/Hilbert space, no transfer matrix, no
  continuum or limit statement: Stages 1b-B/C/D are untouched.

## 5. Priced remainders (unchanged from the gauntlet)

- **1b-B — positivity proper (L):** the sesquilinear OS form
  argument on top of this pack: `⟨θF · F⟩_β ≥ 0` for positive-time
  observables. With A landed, A + B = PARTIAL-δ ("reflection
  positivity stands").
- **1b-C — the OS space (M):** quotient/completion of the
  positive-time observable algebra by the OS form, via the
  time-slice L² route (the quotient/completion route at L was
  declined by the gauntlet).
- **1b-D — transfer matrix + lattice gap (M):** the OS-space
  transfer operator, self-adjointness, and the gap at stated
  `(a, L, β)`.
