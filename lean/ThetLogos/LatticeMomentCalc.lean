import ThetLogos.LatticeTwirl

/-
# Linkwise moment calculus at β = 0 (Pitch 4, Stage 1c-0, gap-queue Q13, brick Q13-2)

HONESTY LEDGER — read this before citing anything from this file.

## 0. What this file is

Tier: **T1 at the finite-lattice level** — machine-checked theorems
about one fixed finite lattice, in the Stage 0 / Stage 1a / Stage 1c-0
setting of `ThetLogos.LatticeGauge`, `ThetLogos.LatticeCorrelations`
and `ThetLogos.LatticeAnalyticity`, whose devices are consumed
unchanged, and of `ThetLogos.LatticeTwirl` (bricks Q13-0/Q13-1),
whose J-twirl apparatus is consumed unchanged.

This module is **brick Q13-2** of the re-priced Stage 1c-0 clause-(ii)
programme (`whitepaper/stage1c0-q13-reprice-2026-10-24.md` §3). Its
charter: express β = 0 expectations of finite products of plaquette
matrix entries as products of one-link J moments — the singleton rule
(a link read by exactly one entry factor contributes a `haarTwirl1`
entry), the pair rule (a link read by exactly two entry factors
contributes a `haarTwirl` entry, whichever word the factors come
from), the empty rule (a link read by no factor contributes `1`) —
and derive the **centered** contractions of charter eq. (7) in the
same J data, means included: the mean subtraction is *not* dropped,
so reducible `ρ` with a trivial subrepresentation is handled exactly
(the one-factor twirls in the means need not vanish). The charter's
Q13-2 PARTIAL trigger — uncentered moments landing without the mean
subtraction in the same J data — therefore does **not** fire.

Orientation patterns are matrix functions: a direct factor reads
`M`, a conjugated factor reads `orientConj M`, a literal inverse
factor reads the dual with the transpose wiring of
`mat_inv_eq_dual_transpose` (`linkEntryInv_eq`). All four
orientations of `repMatrix ρ` from `LatticeTwirl` §7 are admissible
(§5 below).

One honesty note on hypotheses: the moment identities of §2–§4 hold
for **arbitrary** matrix functions `M : G → Matrix (Fin d) (Fin d) ℂ`
with no continuity or unitarity hypothesis at all — both sides are
Bochner integrals against the product measure, and the product-rule
identity `integral_fintype_prod_eq_prod` is unconditional. The
representation bundle (multiplicativity / unit / inverse-star /
entry continuity) enters only where it mathematically must: the
inverse-entry dictionary of §1 and the corpus discharge of §5.

## 0.1 Scope fences (binding on this module)

**(i) Multiplicity fence.** Every product formula here is consumed
through per-link fiber integrals; the fiber evaluations are proved
for fibers of cardinality `0`, `1` and `2` only. Words in which one
configuration link occurs more than twice across the two signed
plaquette words need higher Haar moment tensors; that stronger
reading is excluded from Q13's price (charter §5) and is **not**
built here.

**(ii) No contraction brick.** The two-plaquette tensor-network
contraction (charter eq. (8), brick Q13-3) and the assembly into
`κ_p` (brick Q13-4) are **not** in this module. What is proved here
is the linkwise calculus those bricks consume: expectations of
entry products, evaluated link by link in J data, with the exact
interface recorded in the brick's verdict memo.

**(iii) Finite-volume clause.** Every statement is at fixed finite
`Λ`. No limit — in volume, in spacing, in anything — is taken or
asserted.

**(iv) Clay clause.** Parts of the official Clay Yang–Mills
statement closed by this module: **0**. **NO CLAIM.** Stage 1c-0
clause (ii) remains PARTIAL until Q13-3 and Q13-4 land and are
parent-verified.

This module is NOT in the root import list of the library (the
corpus pattern for recent exhibits); it is verified by a targeted
build.

- Status: brick Q13-2 — built 2026-10-24 under the gap queue;
  verdict STANDS (charter generality); parent-verified
  2026-10-24 (targeted build exit 0, strict recount, axiom
  check). Dossier:
  `whitepaper/stage1c0-q13-brick2-2026-10-24.md`.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal Topology

section Setup

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ)
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-! ## §1. Link-entry observables

A single matrix-entry factor, read off one configuration link. All
orientation variants (direct, conjugate, dual, conjugate-dual) are
instances: an orientation is a matrix function `M : G → Matrix
(Fin d) (Fin d) ℂ`, and a conjugated entry factor is `linkEntry`
of `orientConj M`. -/

/-- The link-entry observable: the `(a, b)` entry of `M` evaluated
at the configuration's value on link `ℓ`. -/
noncomputable def linkEntry (M : G → Matrix (Fin d) (Fin d) ℂ)
    (ℓ : Link Λ) (a b : Fin d) : Config Λ G → ℂ :=
  fun U => M (U ℓ) a b

/-- The inverse link-entry observable: the `(a, b)` entry of the
inverse matrix at link `ℓ`. By the Q13-1 dictionary this is the
dual representation read with transposed indices. -/
noncomputable def linkEntryInv (M : G → Matrix (Fin d) (Fin d) ℂ)
    (ℓ : Link Λ) (a b : Fin d) : Config Λ G → ℂ :=
  fun U => (M (U ℓ))⁻¹ a b

/-- **Inverse-entry dictionary.** A literal inverse entry factor is
the dual orientation read with its two indices transposed
(charter §1.2, via `mat_inv_eq_dual_transpose`). This is the only
place the representation bundle is needed in §1–§4. -/
theorem linkEntryInv_eq (M : G → Matrix (Fin d) (Fin d) ℂ)
    (hmul : ∀ g h : G, M (g * h) = M g * M h) (hone : M 1 = 1)
    (hinv : ∀ g : G, M g⁻¹ = star (M g)) (ℓ : Link Λ) (a b : Fin d) :
    linkEntryInv M ℓ a b = linkEntry (orientDual M) ℓ b a := by
  funext U
  show (M (U ℓ))⁻¹ a b = orientDual M (U ℓ) b a
  rw [mat_inv_eq_dual_transpose M hmul hone hinv (U ℓ)]
  exact Matrix.transpose_apply _ _ _

/-- A link-entry observable depends only on its own link. This is
the push of the Stage 1a factorization from whole observables down
to matrix-entry observables (the charter's Q13-2 kill condition —
it does not fire). -/
theorem linkEntry_dependsOnlyOn (M : G → Matrix (Fin d) (Fin d) ℂ)
    (ℓ : Link Λ) (a b : Fin d) :
    DependsOnlyOn (linkEntry M ℓ a b) {ℓ} :=
  ⟨fun v => M (v ⟨ℓ, Finset.mem_singleton_self ℓ⟩) a b, fun U => rfl⟩

/-! ## §2. The named link-occurrence patterns

The three patterns of charter §1.3, as standalone theorems in the
corpus's currency (`gibbsExpect` at `β = 0`): singleton, pair at a
shared link, pair at distinct links. -/

/-- A single-link factor over the product measure: the integral of
a product concentrated on one link is the integral over that
link's Haar measure. -/
theorem integral_single_link_factor (φ : G → ℂ) (ℓ : Link Λ) :
    ∫ U, (∏ ℓ' : Link Λ, if ℓ' = ℓ then φ (U ℓ') else 1)
        ∂(configMeasure μG)
      = ∫ g, φ g ∂μG := by
  have h1 : ∫ U, (∏ ℓ' : Link Λ, if ℓ' = ℓ then φ (U ℓ') else 1)
        ∂(configMeasure μG)
      = ∏ ℓ' : Link Λ, ∫ g, (if ℓ' = ℓ then φ g else 1) ∂μG := by
    show ∫ U : Link Λ → G, (∏ ℓ' : Link Λ, if ℓ' = ℓ then φ (U ℓ') else 1)
        ∂(Measure.pi fun _ : Link Λ => μG)
      = ∏ ℓ' : Link Λ, ∫ g, (if ℓ' = ℓ then φ g else 1) ∂μG
    exact integral_fintype_prod_eq_prod (fun ℓ' g => if ℓ' = ℓ then φ g else 1)
  rw [h1]
  rw [Finset.prod_eq_single_of_mem ℓ (Finset.mem_univ ℓ)
    (fun ℓ' _ hne => by simp [hne])]
  congr 1
  funext g
  exact if_pos rfl

/-- **Singleton rule.** The β = 0 expectation of one link-entry
factor is the one-factor twirl entry `𝒥(M)`. -/
theorem gibbsExpect_zero_linkEntry (M : G → Matrix (Fin d) (Fin d) ℂ)
    (ℓ : Link Λ) (a b : Fin d) :
    gibbsExpect σ μG ρ 0 (linkEntry M ℓ a b) = haarTwirl1 μG M a b := by
  have hpt : ∀ U : Config Λ G, linkEntry M ℓ a b U
      = ∏ ℓ' : Link Λ, if ℓ' = ℓ then M (U ℓ') a b else 1 := by
    intro U
    show M (U ℓ) a b = ∏ ℓ' : Link Λ, if ℓ' = ℓ then M (U ℓ') a b else 1
    rw [Finset.prod_eq_single_of_mem ℓ (Finset.mem_univ ℓ)
      (fun ℓ' _ hne => if_neg hne)]
    exact (if_pos rfl).symm
  rw [gibbsExpect_zero, haarTwirl1_apply,
    integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact integral_single_link_factor μG (fun g => M g a b) ℓ

/-- **Pair rule (shared link).** The β = 0 expectation of two
link-entry factors reading the *same* link is the pair-twirl entry
`𝒥(M, N)`. The two factors may come from either plaquette word, in
either orientation — the rule sees only the link's factor pair. -/
theorem gibbsExpect_zero_linkEntry_mul_self
    (M N : G → Matrix (Fin d) (Fin d) ℂ) (ℓ : Link Λ)
    (a b c e : Fin d) :
    gibbsExpect σ μG ρ 0
        (fun U => linkEntry M ℓ a b U * linkEntry N ℓ c e U)
      = haarTwirl μG M N (a, c) (b, e) := by
  have hpt : ∀ U : Config Λ G, linkEntry M ℓ a b U * linkEntry N ℓ c e U
      = ∏ ℓ' : Link Λ, if ℓ' = ℓ then M (U ℓ') a b * N (U ℓ') c e else 1 := by
    intro U
    show M (U ℓ) a b * N (U ℓ) c e
      = ∏ ℓ' : Link Λ, if ℓ' = ℓ then M (U ℓ') a b * N (U ℓ') c e else 1
    rw [Finset.prod_eq_single_of_mem ℓ (Finset.mem_univ ℓ)
      (fun ℓ' _ hne => if_neg hne)]
    exact (if_pos rfl).symm
  rw [gibbsExpect_zero, haarTwirl_apply,
    integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact integral_single_link_factor μG (fun g => M g a b * N g c e) ℓ

/-- **Pair rule (distinct links).** Two link-entry factors reading
*different* links factorize at β = 0 into their singleton twirls —
the Stage 1a disjoint factorization, pushed down to entries via
`linkEntry_dependsOnlyOn`. -/
theorem gibbsExpect_zero_linkEntry_mul_ne
    (M N : G → Matrix (Fin d) (Fin d) ℂ) {ℓ ℓ' : Link Λ} (hℓ : ℓ ≠ ℓ')
    (a b c e : Fin d) :
    gibbsExpect σ μG ρ 0
        (fun U => linkEntry M ℓ a b U * linkEntry N ℓ' c e U)
      = haarTwirl1 μG M a b * haarTwirl1 μG N c e := by
  rw [gibbsExpect_zero_mul_of_disjoint σ μG ρ _ _ {ℓ} {ℓ'}
    (Finset.disjoint_singleton.mpr hℓ)
    (linkEntry_dependsOnlyOn M ℓ a b) (linkEntry_dependsOnlyOn N ℓ' c e),
    gibbsExpect_zero_linkEntry, gibbsExpect_zero_linkEntry]

/-! ## §3. The linkwise product rule

The master computation: a finite product of link-entry factors
(slots), regrouped by the link each slot reads. The right-hand
side is a product over links of **fiber integrals**; §3's second
half evaluates a fiber integral by its cardinality: `0 ↦ 1`,
`1 ↦ 𝒥(M)` entry, `2 ↦ 𝒥(M, N)` entry. -/

/-- Regrouping a product of link-entry factors by link. -/
theorem prod_linkEntry_eq {ι : Type*} [Fintype ι]
    (sl : ι → Link Λ) (M : ι → G → Matrix (Fin d) (Fin d) ℂ)
    (a b : ι → Fin d) (U : Config Λ G) :
    (∏ i, linkEntry (M i) (sl i) (a i) (b i) U)
      = ∏ ℓ : Link Λ, ∏ i ∈ Finset.univ.filter (fun i => sl i = ℓ),
          M i (U ℓ) (a i) (b i) := by
  have h := Finset.prod_fiberwise_of_maps_to
    (s := (Finset.univ : Finset ι)) (t := (Finset.univ : Finset (Link Λ)))
    (g := sl) (fun i _ => Finset.mem_univ _)
    (fun i => M i (U (sl i)) (a i) (b i))
  show (∏ i, M i (U (sl i)) (a i) (b i))
      = ∏ ℓ : Link Λ, ∏ i ∈ Finset.univ.filter (fun i => sl i = ℓ),
          M i (U ℓ) (a i) (b i)
  rw [← h]
  refine Finset.prod_congr rfl fun ℓ _ => Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_filter] at hi
  rw [hi.2]

/-- **The linkwise product rule.** The β = 0 expectation of a
finite product of link-entry factors is the product over links of
the fiber integrals. No multiplicity hypothesis is needed at this
level; the fiber evaluations below are where cardinality `≤ 2`
enters. -/
theorem gibbsExpect_zero_prod_linkEntry {ι : Type*} [Fintype ι]
    (sl : ι → Link Λ) (M : ι → G → Matrix (Fin d) (Fin d) ℂ)
    (a b : ι → Fin d) :
    gibbsExpect σ μG ρ 0 (fun U => ∏ i, linkEntry (M i) (sl i) (a i) (b i) U)
      = ∏ ℓ : Link Λ, ∫ g, ∏ i ∈ Finset.univ.filter (fun i => sl i = ℓ),
          M i g (a i) (b i) ∂μG := by
  rw [gibbsExpect_zero]
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (fun U => prod_linkEntry_eq sl M a b U))]
  show ∫ U : Link Λ → G,
      (∏ ℓ : Link Λ, ∏ i ∈ Finset.univ.filter (fun i => sl i = ℓ),
        M i (U ℓ) (a i) (b i)) ∂(Measure.pi fun _ : Link Λ => μG)
    = ∏ ℓ : Link Λ, ∫ g, ∏ i ∈ Finset.univ.filter (fun i => sl i = ℓ),
        M i g (a i) (b i) ∂μG
  exact integral_fintype_prod_eq_prod
    (fun ℓ g => ∏ i ∈ Finset.univ.filter (fun i => sl i = ℓ), M i g (a i) (b i))

/-- Fiber evaluation, empty fiber: the local moment is `1`. -/
theorem integral_fiberProd_empty {ι : Type*}
    (M : ι → G → Matrix (Fin d) (Fin d) ℂ) (a b : ι → Fin d) :
    ∫ g, ∏ i ∈ (∅ : Finset ι), M i g (a i) (b i) ∂μG = 1 := by
  simp [integral_const]

/-- Fiber evaluation, singleton fiber: the local moment is the
one-factor twirl entry. -/
theorem integral_fiberProd_singleton {ι : Type*}
    (M : ι → G → Matrix (Fin d) (Fin d) ℂ) (a b : ι → Fin d) (i₀ : ι) :
    ∫ g, ∏ i ∈ {i₀}, M i g (a i) (b i) ∂μG
      = haarTwirl1 μG (M i₀) (a i₀) (b i₀) := by
  have h : (∫ g, ∏ i ∈ {i₀}, M i g (a i) (b i) ∂μG)
      = ∫ g, M i₀ g (a i₀) (b i₀) ∂μG := by
    apply integral_congr_ae
    filter_upwards with g
    rw [Finset.prod_singleton]
  rw [h]
  exact (haarTwirl1_apply μG (M i₀) (a i₀) (b i₀)).symm

/-- Fiber evaluation, two-element fiber: the local moment is the
pair-twirl entry. -/
theorem integral_fiberProd_pair {ι : Type*} [DecidableEq ι]
    (M : ι → G → Matrix (Fin d) (Fin d) ℂ) (a b : ι → Fin d)
    {i₀ j₀ : ι} (h : i₀ ≠ j₀) :
    ∫ g, ∏ i ∈ {i₀, j₀}, M i g (a i) (b i) ∂μG
      = haarTwirl μG (M i₀) (M j₀) (a i₀, a j₀) (b i₀, b j₀) := by
  have hh : (∫ g, ∏ i ∈ {i₀, j₀}, M i g (a i) (b i) ∂μG)
      = ∫ g, M i₀ g (a i₀) (b i₀) * M j₀ g (a j₀) (b j₀) ∂μG := by
    apply integral_congr_ae
    filter_upwards with g
    rw [Finset.prod_pair h]
  rw [hh]
  exact (haarTwirl_apply μG (M i₀) (M j₀) (a i₀, a j₀) (b i₀, b j₀)).symm

/-! ## §4. Two families and the centered contraction

The two-word form of the product rule, the combined fiber
evaluations for the mixed patterns, and the centered contraction
of charter eq. (7) with both means expressed in the same J data. -/

/-- **Two-family product rule.** The β = 0 expectation of a
product of two entry-factor families is the product over links of
the combined fiber integrals (first family's fiber factor times
the second family's). -/
theorem gibbsExpect_zero_prod_linkEntry_mul {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB]
    (slA : ιA → Link Λ) (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ)
    (aA bA : ιA → Fin d)
    (slB : ιB → Link Λ) (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ)
    (aB bB : ιB → Fin d) :
    gibbsExpect σ μG ρ 0
        (fun U => (∏ i, linkEntry (MA i) (slA i) (aA i) (bA i) U)
          * (∏ j, linkEntry (MB j) (slB j) (aB j) (bB j) U))
      = ∏ ℓ : Link Λ, ∫ g,
          (∏ i ∈ Finset.univ.filter (fun i => slA i = ℓ), MA i g (aA i) (bA i))
            * (∏ j ∈ Finset.univ.filter (fun j => slB j = ℓ),
                MB j g (aB j) (bB j)) ∂μG := by
  rw [gibbsExpect_zero]
  have hpt : ∀ U : Config Λ G,
      (∏ i, linkEntry (MA i) (slA i) (aA i) (bA i) U)
          * (∏ j, linkEntry (MB j) (slB j) (aB j) (bB j) U)
        = ∏ ℓ : Link Λ,
            (∏ i ∈ Finset.univ.filter (fun i => slA i = ℓ), MA i (U ℓ) (aA i) (bA i))
              * (∏ j ∈ Finset.univ.filter (fun j => slB j = ℓ),
                  MB j (U ℓ) (aB j) (bB j)) := by
    intro U
    rw [prod_linkEntry_eq slA MA aA bA U, prod_linkEntry_eq slB MB aB bB U]
    exact (Finset.prod_mul_distrib
      (f := fun ℓ => ∏ i ∈ Finset.univ.filter (fun i => slA i = ℓ),
        MA i (U ℓ) (aA i) (bA i))
      (g := fun ℓ => ∏ j ∈ Finset.univ.filter (fun j => slB j = ℓ),
        MB j (U ℓ) (aB j) (bB j))).symm
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  show ∫ U : Link Λ → G, (∏ ℓ : Link Λ,
      (∏ i ∈ Finset.univ.filter (fun i => slA i = ℓ), MA i (U ℓ) (aA i) (bA i))
        * (∏ j ∈ Finset.univ.filter (fun j => slB j = ℓ),
            MB j (U ℓ) (aB j) (bB j))) ∂(Measure.pi fun _ : Link Λ => μG)
    = ∏ ℓ : Link Λ, ∫ g,
        (∏ i ∈ Finset.univ.filter (fun i => slA i = ℓ), MA i g (aA i) (bA i))
          * (∏ j ∈ Finset.univ.filter (fun j => slB j = ℓ),
              MB j g (aB j) (bB j)) ∂μG
  exact integral_fintype_prod_eq_prod
    (fun ℓ g => (∏ i ∈ Finset.univ.filter (fun i => slA i = ℓ), MA i g (aA i) (bA i))
      * (∏ j ∈ Finset.univ.filter (fun j => slB j = ℓ), MB j g (aB j) (bB j)))

/-- Combined fiber evaluation, shared link (one factor from each
family): the local moment is the pair-twirl entry mixing the two
families' orientations. -/
theorem integral_fiberProd_mul_singleton_singleton {ιA ιB : Type*}
    (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d)
    (i₀ : ιA) (j₀ : ιB) :
    ∫ g, (∏ i ∈ {i₀}, MA i g (aA i) (bA i))
        * (∏ j ∈ {j₀}, MB j g (aB j) (bB j)) ∂μG
      = haarTwirl μG (MA i₀) (MB j₀) (aA i₀, aB j₀) (bA i₀, bB j₀) := by
  have hh : (∫ g, (∏ i ∈ {i₀}, MA i g (aA i) (bA i))
        * (∏ j ∈ {j₀}, MB j g (aB j) (bB j)) ∂μG)
      = ∫ g, MA i₀ g (aA i₀) (bA i₀) * MB j₀ g (aB j₀) (bB j₀) ∂μG := by
    apply integral_congr_ae
    filter_upwards with g
    rw [Finset.prod_singleton, Finset.prod_singleton]
  rw [hh]
  exact (haarTwirl_apply μG (MA i₀) (MB j₀) (aA i₀, aB j₀) (bA i₀, bB j₀)).symm

/-- Combined fiber evaluation, second family absent at the link:
the combined fiber integral is the first family's fiber integral
(then §3's evaluations apply). -/
theorem integral_fiberProd_mul_empty_right {ιA ιB : Type*}
    (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d)
    (sA : Finset ιA) :
    ∫ g, (∏ i ∈ sA, MA i g (aA i) (bA i))
        * (∏ j ∈ (∅ : Finset ιB), MB j g (aB j) (bB j)) ∂μG
      = ∫ g, ∏ i ∈ sA, MA i g (aA i) (bA i) ∂μG := by
  simp

/-- Combined fiber evaluation, first family absent at the link:
the combined fiber integral is the second family's fiber
integral (then §3's evaluations apply). -/
theorem integral_fiberProd_mul_empty_left {ιA ιB : Type*}
    (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d)
    (sB : Finset ιB) :
    ∫ g, (∏ i ∈ (∅ : Finset ιA), MA i g (aA i) (bA i))
        * (∏ j ∈ sB, MB j g (aB j) (bB j)) ∂μG
      = ∫ g, ∏ j ∈ sB, MB j g (aB j) (bB j) ∂μG := by
  simp

/-- **The centered contraction in J data (charter eq. (7), linkwise
form).** The covariance of two entry-factor products at β = 0 is
the combined linkwise product *minus* the product of the two
one-family linkwise products — the means are the same fiber
integrals, evaluated by the same §3 rules, so nothing about the
centering is dropped: for reducible `ρ` the one-factor twirls in
the means carry the trivial-subrepresentation contributions. -/
theorem covZero_prod_linkEntry {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (slA : ιA → Link Λ) (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ)
    (aA bA : ιA → Fin d)
    (slB : ιB → Link Λ) (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ)
    (aB bB : ιB → Fin d) :
    covZero σ μG ρ (fun U => ∏ i, linkEntry (MA i) (slA i) (aA i) (bA i) U)
        (fun U => ∏ j, linkEntry (MB j) (slB j) (aB j) (bB j) U)
      = (∏ ℓ : Link Λ, ∫ g,
            (∏ i ∈ Finset.univ.filter (fun i => slA i = ℓ), MA i g (aA i) (bA i))
              * (∏ j ∈ Finset.univ.filter (fun j => slB j = ℓ),
                  MB j g (aB j) (bB j)) ∂μG)
        - (∏ ℓ : Link Λ, ∫ g,
              ∏ i ∈ Finset.univ.filter (fun i => slA i = ℓ),
                MA i g (aA i) (bA i) ∂μG)
          * (∏ ℓ : Link Λ, ∫ g,
              ∏ j ∈ Finset.univ.filter (fun j => slB j = ℓ),
                MB j g (aB j) (bB j) ∂μG) := by
  show gibbsExpect σ μG ρ 0
        (fun U => (∏ i, linkEntry (MA i) (slA i) (aA i) (bA i) U)
          * (∏ j, linkEntry (MB j) (slB j) (aB j) (bB j) U))
      - gibbsExpect σ μG ρ 0 (fun U => ∏ i, linkEntry (MA i) (slA i) (aA i) (bA i) U)
        * gibbsExpect σ μG ρ 0
            (fun U => ∏ j, linkEntry (MB j) (slB j) (aB j) (bB j) U)
      = _
  rw [gibbsExpect_zero_prod_linkEntry_mul, gibbsExpect_zero_prod_linkEntry,
    gibbsExpect_zero_prod_linkEntry]

/-- **C3 guard, linkwise seat.** If every entry factor of the
second family is identically `1` — the trivial-representation
pattern, where the second word's observable is constant — the
centered contraction vanishes. (Matches the landed
`covZero_const_right` guard shape of Q13-0/Q13-1.) -/
theorem covZero_prod_linkEntry_eq_zero_of_entries_one {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB]
    (slA : ιA → Link Λ) (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ)
    (aA bA : ιA → Fin d)
    (slB : ιB → Link Λ) (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ)
    (aB bB : ιB → Fin d)
    (hB : ∀ (j : ιB) (g : G), MB j g (aB j) (bB j) = 1) :
    covZero σ μG ρ (fun U => ∏ i, linkEntry (MA i) (slA i) (aA i) (bA i) U)
        (fun U => ∏ j, linkEntry (MB j) (slB j) (aB j) (bB j) U) = 0 := by
  have hobs : (fun U => ∏ j, linkEntry (MB j) (slB j) (aB j) (bB j) U)
      = (fun _ => (1 : ℂ)) := by
    funext U
    simp [linkEntry, hB]
  rw [hobs]
  exact covZero_const_right σ μG ρ _ 1

/-! ## §5. Corpus discharge: orientations of `repMatrix ρ`

The abstract calculus of §1–§4 at the corpus's own representation.
The singleton/pair rules need no hypotheses; the inverse-entry
dictionary consumes the Q13-1 bundle satisfaction lemmas. -/

/-- The inverse-entry dictionary at any orientation of `repMatrix
ρ`: the orientation's own bundle (Q13-1's `IsOrientationMat`
satisfaction) is exactly what the dictionary consumes. -/
theorem linkEntryInv_eq_of_isOrientationMat
    {N : G → Matrix (Fin d) (Fin d) ℂ}
    (hN : IsOrientationMat (repMatrix ρ) N) (ℓ : Link Λ) (a b : Fin d) :
    linkEntryInv N ℓ a b = linkEntry (orientDual N) ℓ b a :=
  linkEntryInv_eq N hN.1 hN.2.1 hN.2.2.1 ℓ a b

/-- The inverse-entry dictionary at `repMatrix ρ` itself: an
inverse entry factor is the corpus dual orientation `repMatDual ρ`
read with transposed indices. -/
theorem repMatrix_linkEntryInv
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (ℓ : Link Λ) (a b : Fin d) :
    linkEntryInv (repMatrix ρ) ℓ a b = linkEntry (repMatDual ρ) ℓ b a :=
  linkEntryInv_eq_of_isOrientationMat ρ
    (repMatrix_isOrientationMat ρ hρcont) ℓ a b

/-- Singleton rule at the conjugate orientation: the β = 0 mean of
a conjugated entry factor is the one-factor twirl of `repMatConj
ρ` — the conjugate sector's contribution to the means of charter
eq. (7). -/
theorem gibbsExpect_zero_linkEntry_repMatConj (ℓ : Link Λ) (a b : Fin d) :
    gibbsExpect σ μG ρ 0 (linkEntry (repMatConj ρ) ℓ a b)
      = haarTwirl1 μG (repMatConj ρ) a b :=
  gibbsExpect_zero_linkEntry σ μG ρ (repMatConj ρ) ℓ a b

/-- Pair rule at a shared link, direct × conjugate: the β = 0
expectation of a direct entry factor times a conjugated entry
factor on the same link is the `𝒥(ρ, ρ̄)` pair-twirl entry — the
`End(V)`-sector pairing of charter §1.2. -/
theorem gibbsExpect_zero_linkEntry_mul_repMatConj (ℓ : Link Λ)
    (a b c e : Fin d) :
    gibbsExpect σ μG ρ 0
        (fun U => linkEntry (repMatrix ρ) ℓ a b U
          * linkEntry (repMatConj ρ) ℓ c e U)
      = haarTwirl μG (repMatrix ρ) (repMatConj ρ) (a, c) (b, e) :=
  gibbsExpect_zero_linkEntry_mul_self σ μG ρ (repMatrix ρ) (repMatConj ρ)
    ℓ a b c e

end Setup

end ThetLogos
