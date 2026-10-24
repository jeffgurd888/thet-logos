import ThetLogos.LatticeMomentCalc

/-
# Two-plaquette tensor-network contraction (Pitch 4, Stage 1c-0, gap-queue Q13, brick Q13-3)

HONESTY LEDGER — read this before citing anything from this file.

## 0. What this file is

Tier: **T1 at the finite-lattice level** — machine-checked theorems
about one fixed finite lattice, in the Stage 0 / Stage 1a / Stage 1c-0
setting of `ThetLogos.LatticeGauge`, `ThetLogos.LatticeCorrelations`
and `ThetLogos.LatticeAnalyticity`, consuming `ThetLogos.LatticeTwirl`
(bricks Q13-0/Q13-1: the J-twirl apparatus) and
`ThetLogos.LatticeMomentCalc` (brick Q13-2: the linkwise moment
calculus) unchanged.

This module is **brick Q13-3** of the re-priced Stage 1c-0
clause-(ii) programme (`whitepaper/stage1c0-q13-reprice-2026-10-24.md`
§3). Its charter: define the contraction `Contr` that Q13-0
deliberately left undefined, and prove the contraction identities
(charter eqs. (7)–(8)): for two plaquette words `p, q`, each
expectation `𝔼₀[W_p W_q^s]` (`s = ±`, `W_q^+ = W_q`,
`W_q^- = conj W_q`) is the finite contraction of the J data along the
shared-link pattern of `(p, q)`, and the centered combination is the
per-plaquette covariance summand of charter eq. (6),

`Cov₀(W_p, D_q) = -(1/2d) (𝔈⁺_{p,q} + 𝔈⁻_{p,q})`,
`𝔈^s_{p,q} = Contr^s_{p,q}(𝒥) - Contr^s_{p,∅}(𝒥) Contr^s_{∅,q}(𝒥)`,

with the covariance centering carried through in the same J data —
the means are one-word contractions, not dropped terms, so reducible
`ρ` with a trivial subrepresentation is handled exactly.

## 0.1 What `Contr` is — and what it is not

`wordContr` (§1) is a product **over links** of one-link Haar
integrals of entry products against `μG`: the fiber-integral form of
the J-moment data. It is *not* the covariance integral over
configuration space renamed — the identification of a β = 0
expectation with `wordContr` is a theorem (the Stage 1a
factorization, via Q13-2), not a definition; this is the distinction
the charter's Q13-0 kill (b) turns on. §2 then *evaluates* every
one-link factor: a link whose combined fiber (factors from both
words together) has cardinality `0`, `1` or `2` contributes exactly
`1`, a one-factor twirl entry `𝒥(M)`, or a pair-twirl entry
`𝒥(M, N)`, with the orientations `ρ, ρ̄, ρ^∨, ρ̄^∨` and the
inverse-factor transpose wiring of Q13-1/Q13-2 (§4 of this module
fixes the plaquette slot data: direct steps read `ρ`, inverse steps
read `ρ^∨` with transposed indices, conjugated words read `ρ̄` /
`ρ̄^∨`).

## 0.2 Scope fences (binding on this module)

**(i) Multiplicity fence — the named PARTIAL class.** A link can be
read twice by one plaquette word: the `μ`-links of `p = (x, μ, ν)`
collide iff `σ ν x = x`, the `ν`-links iff `σ μ x = x` (for
`μ < ν`). If such a doubled link is *also* read by the other word,
the combined fiber has cardinality `3` or `4` and the link factor is
a higher Haar moment tensor, **not** a pair twirl; pair intertwiners
alone do not evaluate it (charter §5, excluded stronger reading 2).
For exactly this geometric class — *a plaquette base site fixed by
the transverse shift, with the doubled link shared with the other
word* — the **evaluated** form of (8) is not asserted: brick Q13-3
lands **PARTIAL** there by name. The contraction identity itself,
`𝔼₀[W_p W_q^s] = Contr^s_{p,q}` with `Contr` in fiber-integral form,
and the centered identity (6)–(7), hold for **every** `(p, q)` with
no restriction. Under the generic hypothesis that no shift fixes
either base site, every fiber has cardinality `≤ 1` per word and
the classification of §2 applies to every link (§5).

**(ii) No assembly.** Substituting the per-`(p, q)` identity into
the landed link-sharing sum (charter eq. (1)) to obtain `κ_p` in
the form (9), and discharging the mandatory checks **C1** (circle
specialization recovering `κ_p = -1/2` termwise) and **C2**
(termwise agreement with `covZero_plaquetteLoop_eq_sum`), is brick
Q13-4, **not** built here. §4's headline is stated in exactly the
per-`q` shape the landed sum consumes, so both checks are statable
against it; the C3 guards (cyclic-rotation invariance of the final
contraction; `κ_p = 0` at the trivial representation) are likewise
Q13-4 acceptance items, with the slot-level C3 seat already landed
in Q13-2 (`covZero_prod_linkEntry_eq_zero_of_entries_one`).

**(iii) Excluded readings stay excluded.** No canonical
Schur/Clebsch–Gordan expansion of the J projectors for arbitrary
reducible `ρ` (charter §5, excluded reading 1) is built or implied.

**(iv) Finite-volume clause.** Every statement is at fixed finite
`Λ`. No limit — in volume, in spacing, in anything — is taken or
asserted.

**(v) Clay clause.** Parts of the official Clay Yang–Mills
statement closed by this module: **0**. **NO CLAIM.** Stage 1c-0
clause (ii) remains PARTIAL until Q13-4 lands and is
parent-verified.

This module is NOT in the root import list of the library (the
corpus pattern for recent exhibits); it is verified by a targeted
build.

- Status: brick Q13-3 — built 2026-10-24 under the gap queue;
  verdict PARTIAL (the evaluated contraction lands at the generic
  seat and under the stated pattern hypothesis; the doubled-link
  class of fence (i) is the named residue); parent-verified
  2026-10-24 (targeted build exit 0, strict recount, axiom
  check). Dossier:
  `whitepaper/stage1c0-q13-brick3-partial-2026-10-24.md`.
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

/-! ## §1. The contraction: definitions and the expectation identities

A **slot family** is a finite set of entry factors: slots `i : ι`,
each reading the link `sl i` through the matrix function `M i` at
indices `(a i, b i)`. Q13-2 evaluated expectations of slot-family
products link by link; here the linkwise values are named as the
contraction itself. -/

/-- The **one-link contraction factor**: the combined fiber integral
of two slot families at one link — the first family's fiber factor
times the second family's, integrated against the one-link Haar
measure. For combined fiber cardinality `≤ 2` this is exactly a
J-twirl entry (§2); in general it is the J-moment datum of that
link. -/
noncomputable def linkContr {ιA ιB : Type*} (μG : Measure G)
    (sA : Finset ιA) (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (sB : Finset ιB) (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d) :
    ℂ :=
  ∫ g, (∏ i ∈ sA, MA i g (aA i) (bA i)) * (∏ j ∈ sB, MB j g (aB j) (bB j)) ∂μG

/-- The **contraction of two slot families** (the slot-level form of
charter `Contr^s_{p,q}(𝒥)`): the product over all links of the
one-link contraction factors, each family's slots grouped by the
link they read. -/
noncomputable def wordContr {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (μG : Measure G)
    (slA : ιA → Link Λ) (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (slB : ιB → Link Λ) (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d) :
    ℂ :=
  ∏ ℓ : Link Λ, linkContr μG (Finset.univ.filter (fun i => slA i = ℓ)) MA aA bA
    (Finset.univ.filter (fun j => slB j = ℓ)) MB aB bB

/-- The **one-word contraction** (the empty-word contraction
`Contr_{p,∅}(𝒥)` of charter (9) at slot level): the product over
links of the family's fiber integrals — the J data of the mean
`𝔼₀[∏ entries]`. -/
noncomputable def wordMean {ι : Type*} [Fintype ι] (μG : Measure G)
    (sl : ι → Link Λ) (M : ι → G → Matrix (Fin d) (Fin d) ℂ) (a b : ι → Fin d) : ℂ :=
  ∏ ℓ : Link Λ, ∫ g, ∏ i ∈ Finset.univ.filter (fun i => sl i = ℓ),
      M i g (a i) (b i) ∂μG

/-- The one-word contraction is the β = 0 expectation of the slot
product (Q13-2's linkwise product rule, named). -/
theorem gibbsExpect_zero_slots {ι : Type*} [Fintype ι]
    (sl : ι → Link Λ) (M : ι → G → Matrix (Fin d) (Fin d) ℂ) (a b : ι → Fin d) :
    gibbsExpect σ μG ρ 0 (fun U => ∏ i, linkEntry (M i) (sl i) (a i) (b i) U)
      = wordMean μG sl M a b :=
  gibbsExpect_zero_prod_linkEntry σ μG ρ sl M a b

/-- **Charter (8) at slot level.** The β = 0 expectation of a product
of two slot-family observables is their contraction. -/
theorem gibbsExpect_zero_slots_mul {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (slA : ιA → Link Λ) (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (slB : ιB → Link Λ) (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d) :
    gibbsExpect σ μG ρ 0
        (fun U => (∏ i, linkEntry (MA i) (slA i) (aA i) (bA i) U)
          * (∏ j, linkEntry (MB j) (slB j) (aB j) (bB j) U))
      = wordContr μG slA MA aA bA slB MB aB bB :=
  gibbsExpect_zero_prod_linkEntry_mul σ μG ρ slA MA aA bA slB MB aB bB

/-- **Charter (7) at slot level.** The centered contraction: the
covariance of two slot-family products is the two-word contraction
minus the product of the one-word contractions — the centering is
in the same J data (Q13-2's centered headline, named). -/
theorem covZero_slots {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (slA : ιA → Link Λ) (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (slB : ιB → Link Λ) (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d) :
    covZero σ μG ρ (fun U => ∏ i, linkEntry (MA i) (slA i) (aA i) (bA i) U)
        (fun U => ∏ j, linkEntry (MB j) (slB j) (aB j) (bB j) U)
      = wordContr μG slA MA aA bA slB MB aB bB
        - wordMean μG slA MA aA bA * wordMean μG slB MB aB bB :=
  covZero_prod_linkEntry σ μG ρ slA MA aA bA slB MB aB bB

/-! ## §2. Evaluation of the one-link factors

The six patterns of combined fiber cardinality `≤ 2`: the factor is
`1`, a one-factor twirl entry, or a pair-twirl entry. Each lemma is
one of Q13-2's fiber evaluations, named at the contraction. -/

/-- Pattern `(0,0)`: a link read by neither family contributes `1`. -/
theorem linkContr_empty_empty {ιA ιB : Type*}
    (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d) :
    linkContr μG (∅ : Finset ιA) MA aA bA (∅ : Finset ιB) MB aB bB = 1 := by
  show (∫ g, (∏ i ∈ (∅ : Finset ιA), MA i g (aA i) (bA i))
      * (∏ j ∈ (∅ : Finset ιB), MB j g (aB j) (bB j)) ∂μG) = 1
  rw [integral_fiberProd_mul_empty_right]
  exact integral_fiberProd_empty μG MA aA bA

/-- Second family absent at the link (any first fiber): the factor
is the first family's fiber integral. -/
theorem linkContr_empty_right {ιA ιB : Type*}
    (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d)
    (sA : Finset ιA) :
    linkContr μG sA MA aA bA (∅ : Finset ιB) MB aB bB
      = ∫ g, ∏ i ∈ sA, MA i g (aA i) (bA i) ∂μG := by
  show (∫ g, (∏ i ∈ sA, MA i g (aA i) (bA i))
      * (∏ j ∈ (∅ : Finset ιB), MB j g (aB j) (bB j)) ∂μG) = _
  exact integral_fiberProd_mul_empty_right μG MA aA bA MB aB bB sA

/-- First family absent at the link (any second fiber): the factor
is the second family's fiber integral. -/
theorem linkContr_empty_left {ιA ιB : Type*}
    (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d)
    (sB : Finset ιB) :
    linkContr μG (∅ : Finset ιA) MA aA bA sB MB aB bB
      = ∫ g, ∏ j ∈ sB, MB j g (aB j) (bB j) ∂μG := by
  show (∫ g, (∏ i ∈ (∅ : Finset ιA), MA i g (aA i) (bA i))
      * (∏ j ∈ sB, MB j g (aB j) (bB j)) ∂μG) = _
  exact integral_fiberProd_mul_empty_left μG MA aA bA MB aB bB sB

/-- Pattern `(1,0)`: one factor of the first family only — the
one-factor twirl entry `𝒥(M)`. -/
theorem linkContr_singleton_empty {ιA ιB : Type*}
    (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d) (i₀ : ιA) :
    linkContr μG {i₀} MA aA bA (∅ : Finset ιB) MB aB bB
      = haarTwirl1 μG (MA i₀) (aA i₀) (bA i₀) := by
  show (∫ g, (∏ i ∈ {i₀}, MA i g (aA i) (bA i))
      * (∏ j ∈ (∅ : Finset ιB), MB j g (aB j) (bB j)) ∂μG) = _
  rw [integral_fiberProd_mul_empty_right]
  exact integral_fiberProd_singleton μG MA aA bA i₀

/-- Pattern `(0,1)`: one factor of the second family only — the
one-factor twirl entry `𝒥(N)`. -/
theorem linkContr_empty_singleton {ιA ιB : Type*}
    (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d) (j₀ : ιB) :
    linkContr μG (∅ : Finset ιA) MA aA bA {j₀} MB aB bB
      = haarTwirl1 μG (MB j₀) (aB j₀) (bB j₀) := by
  show (∫ g, (∏ i ∈ (∅ : Finset ιA), MA i g (aA i) (bA i))
      * (∏ j ∈ {j₀}, MB j g (aB j) (bB j)) ∂μG) = _
  rw [integral_fiberProd_mul_empty_left]
  exact integral_fiberProd_singleton μG MB aB bB j₀

/-- Pattern `(1,1)` — **the shared link**: one factor from each
family — the pair-twirl entry `𝒥(M, N)` mixing the two words'
orientations at that link. This is the only pattern in which the
two plaquette words actually interact. -/
theorem linkContr_singleton_singleton {ιA ιB : Type*}
    (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d)
    (i₀ : ιA) (j₀ : ιB) :
    linkContr μG {i₀} MA aA bA {j₀} MB aB bB
      = haarTwirl μG (MA i₀) (MB j₀) (aA i₀, aB j₀) (bA i₀, bB j₀) := by
  show (∫ g, (∏ i ∈ {i₀}, MA i g (aA i) (bA i))
      * (∏ j ∈ {j₀}, MB j g (aB j) (bB j)) ∂μG) = _
  exact integral_fiberProd_mul_singleton_singleton μG MA aA bA MB aB bB i₀ j₀

/-- Pattern `(2,0)`: both factors from the first family (one word
reads the link twice) — the pair-twirl entry `𝒥(M, M')` within that
word's orientations. -/
theorem linkContr_pair_empty {ιA ιB : Type*} [DecidableEq ιA]
    (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d)
    {i₀ i₁ : ιA} (h : i₀ ≠ i₁) :
    linkContr μG {i₀, i₁} MA aA bA (∅ : Finset ιB) MB aB bB
      = haarTwirl μG (MA i₀) (MA i₁) (aA i₀, aA i₁) (bA i₀, bA i₁) := by
  show (∫ g, (∏ i ∈ {i₀, i₁}, MA i g (aA i) (bA i))
      * (∏ j ∈ (∅ : Finset ιB), MB j g (aB j) (bB j)) ∂μG) = _
  rw [integral_fiberProd_mul_empty_right]
  exact integral_fiberProd_pair μG MA aA bA h

/-- Pattern `(0,2)`: both factors from the second family — the
pair-twirl entry `𝒥(N, N')`. -/
theorem linkContr_empty_pair {ιA ιB : Type*} [DecidableEq ιB]
    (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d)
    {j₀ j₁ : ιB} (h : j₀ ≠ j₁) :
    linkContr μG (∅ : Finset ιA) MA aA bA {j₀, j₁} MB aB bB
      = haarTwirl μG (MB j₀) (MB j₁) (aB j₀, aB j₁) (bB j₀, bB j₁) := by
  show (∫ g, (∏ i ∈ (∅ : Finset ιA), MA i g (aA i) (bA i))
      * (∏ j ∈ {j₀, j₁}, MB j g (aB j) (bB j)) ∂μG) = _
  rw [integral_fiberProd_mul_empty_left]
  exact integral_fiberProd_pair μG MB aB bB h

/-- **Classification of one-link factors.** If both fibers have
cardinality `≤ 2` and their cardinalities sum to `≤ 2`, the link
factor is one of the six evaluated J values, with the fiber shapes
and slot witnesses recorded. The excluded patterns `(2,1)`, `(1,2)`,
`(2,2)` are exactly the ones the cardinality hypotheses rule out —
there the factor is a higher Haar moment (header fence (i)). -/
theorem linkContr_classify {ιA ιB : Type*} [DecidableEq ιA] [DecidableEq ιB]
    (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d)
    (sA : Finset ιA) (sB : Finset ιB)
    (hcA : sA.card ≤ 2) (hcB : sB.card ≤ 2) (hcs : sA.card + sB.card ≤ 2) :
    (sA = ∅ ∧ sB = ∅ ∧ linkContr μG sA MA aA bA sB MB aB bB = 1)
    ∨ (∃ i, sA = {i} ∧ sB = ∅
        ∧ linkContr μG sA MA aA bA sB MB aB bB
          = haarTwirl1 μG (MA i) (aA i) (bA i))
    ∨ (∃ j, sA = ∅ ∧ sB = {j}
        ∧ linkContr μG sA MA aA bA sB MB aB bB
          = haarTwirl1 μG (MB j) (aB j) (bB j))
    ∨ (∃ i i', i ≠ i' ∧ sA = {i, i'} ∧ sB = ∅
        ∧ linkContr μG sA MA aA bA sB MB aB bB
          = haarTwirl μG (MA i) (MA i') (aA i, aA i') (bA i, bA i'))
    ∨ (∃ i j, sA = {i} ∧ sB = {j}
        ∧ linkContr μG sA MA aA bA sB MB aB bB
          = haarTwirl μG (MA i) (MB j) (aA i, aB j) (bA i, bB j))
    ∨ (∃ j j', j ≠ j' ∧ sA = ∅ ∧ sB = {j, j'}
        ∧ linkContr μG sA MA aA bA sB MB aB bB
          = haarTwirl μG (MB j) (MB j') (aB j, aB j') (bB j, bB j')) := by
  have hA : sA.card = 0 ∨ sA.card = 1 ∨ sA.card = 2 := by omega
  have hB : sB.card = 0 ∨ sB.card = 1 ∨ sB.card = 2 := by omega
  rcases hA with hA | hA | hA <;> rcases hB with hB | hB | hB
  · -- (0,0)
    left
    have hsA : sA = ∅ := Finset.card_eq_zero.mp hA
    have hsB : sB = ∅ := Finset.card_eq_zero.mp hB
    exact ⟨hsA, hsB, by rw [hsA, hsB]; exact linkContr_empty_empty μG MA aA bA MB aB bB⟩
  · -- (0,1)
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hB
    have hsA : sA = ∅ := Finset.card_eq_zero.mp hA
    refine Or.inr (Or.inr (Or.inl ⟨j, hsA, hj, ?_⟩))
    rw [hsA, hj]
    exact linkContr_empty_singleton μG MA aA bA MB aB bB j
  · -- (0,2)
    obtain ⟨j, j', hjne, hj⟩ := Finset.card_eq_two.mp hB
    have hsA : sA = ∅ := Finset.card_eq_zero.mp hA
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j, j', hjne, hsA, hj, ?_⟩))))
    rw [hsA, hj]
    exact linkContr_empty_pair μG MA aA bA MB aB bB hjne
  · -- (1,0)
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hA
    have hsB : sB = ∅ := Finset.card_eq_zero.mp hB
    refine Or.inr (Or.inl ⟨i, hi, hsB, ?_⟩)
    rw [hi, hsB]
    exact linkContr_singleton_empty μG MA aA bA MB aB bB i
  · -- (1,1)
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hA
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hB
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, j, hi, hj, ?_⟩))))
    rw [hi, hj]
    exact linkContr_singleton_singleton μG MA aA bA MB aB bB i j
  · -- (1,2): excluded by the sum hypothesis
    omega
  · -- (2,0)
    obtain ⟨i, i', hine, hi⟩ := Finset.card_eq_two.mp hA
    have hsB : sB = ∅ := Finset.card_eq_zero.mp hB
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨i, i', hine, hi, hsB, ?_⟩)))
    rw [hi, hsB]
    exact linkContr_pair_empty μG MA aA bA MB aB bB hine
  · -- (2,1): excluded by the sum hypothesis
    omega
  · -- (2,2): excluded by the sum hypothesis
    omega

/-- **Disjoint supports split the contraction.** If at every link
at most one of the two families is present, the two-word
contraction is the product of the one-word contractions — the two
words do not interact link by link. -/
theorem wordContr_eq_wordMean_mul_of_disjoint {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB]
    (slA : ιA → Link Λ) (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (slB : ιB → Link Λ) (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d)
    (hdisj : ∀ ℓ : Link Λ,
      (Finset.univ.filter (fun i => slA i = ℓ)) = ∅
        ∨ (Finset.univ.filter (fun j => slB j = ℓ)) = ∅) :
    wordContr μG slA MA aA bA slB MB aB bB
      = wordMean μG slA MA aA bA * wordMean μG slB MB aB bB := by
  show (∏ ℓ : Link Λ, linkContr μG (Finset.univ.filter (fun i => slA i = ℓ)) MA aA bA
        (Finset.univ.filter (fun j => slB j = ℓ)) MB aB bB)
      = (∏ ℓ : Link Λ, ∫ g, ∏ i ∈ Finset.univ.filter (fun i => slA i = ℓ),
            MA i g (aA i) (bA i) ∂μG)
        * (∏ ℓ : Link Λ, ∫ g, ∏ j ∈ Finset.univ.filter (fun j => slB j = ℓ),
            MB j g (aB j) (bB j) ∂μG)
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  rcases hdisj ℓ with hA | hB
  · rw [hA, linkContr_empty_left]
    rw [integral_fiberProd_empty μG MA aA bA, one_mul]
  · rw [hB, linkContr_empty_right]
    rw [integral_fiberProd_empty μG MB aB bB, mul_one]

/-- **Non-interaction at slot level.** Two slot families with
disjoint link supports have zero covariance at β = 0 — through the
contraction language: the contraction splits, and the centered
combination cancels. This is the mechanism behind the landed
link-sharing reduction; §5 applies it to non-sharing plaquettes. -/
theorem covZero_slots_eq_zero_of_disjoint {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB]
    (slA : ιA → Link Λ) (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (slB : ιB → Link Λ) (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d)
    (hdisj : ∀ ℓ : Link Λ,
      (Finset.univ.filter (fun i => slA i = ℓ)) = ∅
        ∨ (Finset.univ.filter (fun j => slB j = ℓ)) = ∅) :
    covZero σ μG ρ (fun U => ∏ i, linkEntry (MA i) (slA i) (aA i) (bA i) U)
        (fun U => ∏ j, linkEntry (MB j) (slB j) (aB j) (bB j) U) = 0 := by
  rw [covZero_slots, wordContr_eq_wordMean_mul_of_disjoint μG slA MA aA bA slB MB aB bB hdisj,
    sub_self]

/-! ## §3. Analytic helpers

Moving between the trace expansions of §4 and the slot calculus of
§1–§2 needs: measurability and integrability of entry observables
(entries of orientation matrix functions are continuous in the link
variable and bounded by `1`), and finite-sum / additivity rules for
the β = 0 expectation. -/

/-- A measurable observable bounded by `1` is integrable against
the configuration probability measure. -/
theorem integrable_of_measurable_bound_one {F : Config Λ G → ℂ}
    (hF : Measurable F) (hB : ∀ U, ‖F U‖ ≤ 1) :
    Integrable F (configMeasure μG) :=
  MeasureTheory.Integrable.of_bound hF.aestronglyMeasurable 1
    (Filter.Eventually.of_forall hB)

/-- A measurable bounded observable is integrable against the
configuration probability measure. -/
theorem integrable_of_measurable_bound {F : Config Λ G → ℂ}
    (hF : Measurable F) (C : ℝ) (hB : ∀ U, ‖F U‖ ≤ C) :
    Integrable F (configMeasure μG) :=
  MeasureTheory.Integrable.of_bound hF.aestronglyMeasurable C
    (Filter.Eventually.of_forall hB)

/-- Measurability of a link-entry observable with continuous
entries: a coordinate projection composed with the entry function. -/
theorem measurable_linkEntry {M : G → Matrix (Fin d) (Fin d) ℂ}
    (hM : ∀ a c, Continuous fun g => M g a c) (ℓ : Link Λ) (a b : Fin d) :
    Measurable (linkEntry M ℓ a b) :=
  (hM a b).measurable.comp (measurable_pi_apply ℓ)

/-- Measurability of a slot-family product observable. -/
theorem measurable_prod_linkEntry {ι : Type*} [Fintype ι]
    (sl : ι → Link Λ) (M : ι → G → Matrix (Fin d) (Fin d) ℂ) (a b : ι → Fin d)
    (hM : ∀ i x y, Continuous fun g => M i g x y) :
    Measurable (fun U => ∏ i, linkEntry (M i) (sl i) (a i) (b i) U) :=
  Finset.measurable_prod _ fun i _ => measurable_linkEntry (hM i) (sl i) (a i) (b i)

/-- A slot-family product observable with entries bounded by `1`
is bounded by `1`. -/
theorem bound_prod_linkEntry {ι : Type*} [Fintype ι]
    (sl : ι → Link Λ) (M : ι → G → Matrix (Fin d) (Fin d) ℂ) (a b : ι → Fin d)
    (hM : ∀ i g x y, ‖M i g x y‖ ≤ 1) (U : Config Λ G) :
    ‖∏ i, linkEntry (M i) (sl i) (a i) (b i) U‖ ≤ 1 := by
  refine le_trans (norm_prod_le _ _) ?_
  rw [show (1 : ℝ) = ∏ _i : ι, (1 : ℝ) from Finset.prod_const_one.symm]
  gcongr with i
  exact hM i (U (sl i)) (a i) (b i)

/-- Integrability of a slot-family product observable. -/
theorem integrable_prod_linkEntry {ι : Type*} [Fintype ι]
    (sl : ι → Link Λ) (M : ι → G → Matrix (Fin d) (Fin d) ℂ) (a b : ι → Fin d)
    (hcont : ∀ i x y, Continuous fun g => M i g x y)
    (hbound : ∀ i g x y, ‖M i g x y‖ ≤ 1) :
    Integrable (fun U => ∏ i, linkEntry (M i) (sl i) (a i) (b i) U)
      (configMeasure μG) :=
  integrable_of_measurable_bound_one μG
    (measurable_prod_linkEntry sl M a b hcont)
    (bound_prod_linkEntry sl M a b hbound)

/-- Finite sums pass through the β = 0 expectation. -/
theorem gibbsExpect_zero_finset_sum {ι : Type*} (s : Finset ι)
    (F : ι → Config Λ G → ℂ) (hF : ∀ i ∈ s, Integrable (F i) (configMeasure μG)) :
    gibbsExpect σ μG ρ 0 (fun U => ∑ i ∈ s, F i U)
      = ∑ i ∈ s, gibbsExpect σ μG ρ 0 (F i) := by
  calc gibbsExpect σ μG ρ 0 (fun U => ∑ i ∈ s, F i U)
      = ∫ U, (∑ i ∈ s, F i U) ∂(configMeasure μG) := gibbsExpect_zero σ μG ρ _
    _ = ∑ i ∈ s, ∫ U, F i U ∂(configMeasure μG) := integral_finsetSum s hF
    _ = ∑ i ∈ s, gibbsExpect σ μG ρ 0 (F i) :=
        Finset.sum_congr rfl fun i _ => (gibbsExpect_zero σ μG ρ (F i)).symm

/-- Additivity of the β = 0 expectation for integrable
observables. -/
theorem gibbsExpect_zero_add {F H : Config Λ G → ℂ}
    (hF : Integrable F (configMeasure μG)) (hH : Integrable H (configMeasure μG)) :
    gibbsExpect σ μG ρ 0 (fun U => F U + H U)
      = gibbsExpect σ μG ρ 0 F + gibbsExpect σ μG ρ 0 H := by
  calc gibbsExpect σ μG ρ 0 (fun U => F U + H U)
      = ∫ U, (F U + H U) ∂(configMeasure μG) := gibbsExpect_zero σ μG ρ _
    _ = (∫ U, F U ∂(configMeasure μG)) + ∫ U, H U ∂(configMeasure μG) :=
        integral_add hF hH
    _ = gibbsExpect σ μG ρ 0 F + gibbsExpect σ μG ρ 0 H := by
        rw [gibbsExpect_zero σ μG ρ F, gibbsExpect_zero σ μG ρ H]

/-- Subtractivity of the β = 0 expectation for integrable
observables. -/
theorem gibbsExpect_zero_sub {F H : Config Λ G → ℂ}
    (hF : Integrable F (configMeasure μG)) (hH : Integrable H (configMeasure μG)) :
    gibbsExpect σ μG ρ 0 (fun U => F U - H U)
      = gibbsExpect σ μG ρ 0 F - gibbsExpect σ μG ρ 0 H := by
  calc gibbsExpect σ μG ρ 0 (fun U => F U - H U)
      = ∫ U, (F U - H U) ∂(configMeasure μG) := gibbsExpect_zero σ μG ρ _
    _ = (∫ U, F U ∂(configMeasure μG)) - ∫ U, H U ∂(configMeasure μG) :=
        integral_sub hF hH
    _ = gibbsExpect σ μG ρ 0 F - gibbsExpect σ μG ρ 0 H := by
        rw [gibbsExpect_zero σ μG ρ F, gibbsExpect_zero σ μG ρ H]

/-- The β = 0 expectation of a constant observable is the
constant. -/
theorem gibbsExpect_zero_const (c : ℂ) :
    gibbsExpect σ μG ρ 0 (fun _ => c) = c := by
  rw [gibbsExpect_zero σ μG ρ]
  simp

/-- Division by a constant passes through the β = 0 expectation. -/
theorem gibbsExpect_zero_div_const {F : Config Λ G → ℂ} (c : ℂ) :
    gibbsExpect σ μG ρ 0 (fun U => F U / c) = gibbsExpect σ μG ρ 0 F / c := by
  have hfun : (fun U => F U / c) = fun U => c⁻¹ * F U :=
    funext fun U => div_eq_inv_mul _ _
  rw [hfun, div_eq_inv_mul, gibbsExpect_zero σ μG ρ (fun U => c⁻¹ * F U),
    integral_const_mul, gibbsExpect_zero σ μG ρ F]

/-! ## §4. Plaquette slot data and the trace expansions

The plaquette word `plaquetteSteps μ ν` has four steps; read in the
trace's cyclic order, its matrix factors are

`ρ(U(x,μ))`, `ρ(U(σ μ x, ν))`, `ρ((U(σ ν x, μ))⁻¹)`,
`ρ((U(x,ν))⁻¹)`.

The two inverse factors are read through the dual orientation with
transposed indices (Q13-2's `repMatrix_linkEntryInv` dictionary):
`ρ(g⁻¹) a b = ρ^∨(g) b a`. Hence the slot data below: links in step
order, matrix functions `ρ, ρ, ρ^∨, ρ^∨`, and the row/column wiring
`(0,1), (1,2), (3,2), (0,3)` — the dual steps swap their row and
column positions in the cyclic trace. -/

/-- The links read by the plaquette word at `x` in directions
`μ ν`, in step order. As a set this is `plaquetteLinks`
(`plaquetteLinks_eq`). -/
def plaqSlotLink (x : Λ) (μ ν : Fin 4) : Fin 4 → Link Λ :=
  ![(x, μ), (σ μ x, ν), (σ ν x, μ), (x, ν)]

/-- The plaquette word's step matrix functions: forward steps read
`ρ`, backward (inverse) steps read the dual orientation `ρ^∨`. -/
def plaqSlotMat : Fin 4 → (G → Matrix (Fin d) (Fin d) ℂ) :=
  ![repMatrix ρ, repMatrix ρ, repMatDual ρ, repMatDual ρ]

/-- The conjugate plaquette word's step matrix functions: forward
steps read `ρ̄`, backward steps read `ρ̄^∨`. -/
def plaqSlotMatConj : Fin 4 → (G → Matrix (Fin d) (Fin d) ℂ) :=
  ![repMatConj ρ, repMatConj ρ, repMatConjDual ρ, repMatConjDual ρ]

/-- Row wiring of the plaquette trace: step `k`'s factor carries
row index `i (plaqRow k)` for an index assignment `i`. -/
def plaqRow : Fin 4 → Fin 4 := ![0, 1, 3, 0]

/-- Column wiring of the plaquette trace: step `k`'s factor carries
column index `i (plaqCol k)`. The dual steps `2, 3` have their
row/column positions swapped against the naive cyclic order — the
transpose wiring of the inverse factors. -/
def plaqCol : Fin 4 → Fin 4 := ![1, 2, 2, 3]

/-- Every step matrix function of the plaquette word is an
orientation of `repMatrix ρ` (Q13-1's bundle satisfaction). -/
theorem plaqSlotMat_isOrientationMat
    (hρcont : Continuous fun g : G => repMatrix ρ g) (k : Fin 4) :
    IsOrientationMat (repMatrix ρ) (plaqSlotMat ρ k) := by
  fin_cases k <;> simp only [plaqSlotMat, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact repMatrix_isOrientationMat ρ hρcont
  · exact repMatrix_isOrientationMat ρ hρcont
  · exact repMatDual_isOrientationMat ρ hρcont
  · exact repMatDual_isOrientationMat ρ hρcont

/-- Every step matrix function of the conjugate plaquette word is
an orientation of `repMatrix ρ`. -/
theorem plaqSlotMatConj_isOrientationMat
    (hρcont : Continuous fun g : G => repMatrix ρ g) (k : Fin 4) :
    IsOrientationMat (repMatrix ρ) (plaqSlotMatConj ρ k) := by
  fin_cases k <;> simp only [plaqSlotMatConj, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact repMatConj_isOrientationMat ρ hρcont
  · exact repMatConj_isOrientationMat ρ hρcont
  · exact repMatConjDual_isOrientationMat ρ hρcont
  · exact repMatConjDual_isOrientationMat ρ hρcont

/-- Entry continuity of the plaquette word's step matrices. -/
theorem plaqSlotMat_cont (hρcont : Continuous fun g : G => repMatrix ρ g)
    (k : Fin 4) (x y : Fin d) :
    Continuous fun g => plaqSlotMat ρ k g x y :=
  (plaqSlotMat_isOrientationMat ρ hρcont k).2.2.2 x y

/-- Entry bound of the plaquette word's step matrices. -/
theorem plaqSlotMat_bound (hρcont : Continuous fun g : G => repMatrix ρ g)
    (k : Fin 4) (g : G) (x y : Fin d) :
    ‖plaqSlotMat ρ k g x y‖ ≤ 1 :=
  matFn_abs_entry _ (plaqSlotMat_isOrientationMat ρ hρcont k).1
    (plaqSlotMat_isOrientationMat ρ hρcont k).2.1
    (plaqSlotMat_isOrientationMat ρ hρcont k).2.2.1 g x y

/-- Entry continuity of the conjugate word's step matrices. -/
theorem plaqSlotMatConj_cont (hρcont : Continuous fun g : G => repMatrix ρ g)
    (k : Fin 4) (x y : Fin d) :
    Continuous fun g => plaqSlotMatConj ρ k g x y :=
  (plaqSlotMatConj_isOrientationMat ρ hρcont k).2.2.2 x y

/-- Entry bound of the conjugate word's step matrices. -/
theorem plaqSlotMatConj_bound (hρcont : Continuous fun g : G => repMatrix ρ g)
    (k : Fin 4) (g : G) (x y : Fin d) :
    ‖plaqSlotMatConj ρ k g x y‖ ≤ 1 :=
  matFn_abs_entry _ (plaqSlotMatConj_isOrientationMat ρ hρcont k).1
    (plaqSlotMatConj_isOrientationMat ρ hρcont k).2.1
    (plaqSlotMatConj_isOrientationMat ρ hρcont k).2.2.1 g x y

/-- Index assignments `Fin 4 → Fin d` as tuples. -/
def assignEquiv : (Fin d × Fin d × Fin d × Fin d) ≃ (Fin 4 → Fin d) :=
  ⟨fun t => ![t.1, t.2.1, t.2.2.1, t.2.2.2],
   fun i => (i 0, i 1, i 2, i 3),
   fun t => by simp,
   fun i => by funext k; fin_cases k <;> simp⟩

/-- **Trace of a fourfold product, expanded.** The trace of
`((A₀ A₁) A₂) A₃` is the sum over index assignments of the cyclic
entry product — the tensor-network expansion of one word. -/
theorem trace_mul_four (A0 A1 A2 A3 : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace ((A0 * A1) * A2 * A3)
      = ∑ i : Fin 4 → Fin d, A0 (i 0) (i 1) * A1 (i 1) (i 2)
          * A2 (i 2) (i 3) * A3 (i 3) (i 0) := by
  have hsum : (∑ i : Fin 4 → Fin d, A0 (i 0) (i 1) * A1 (i 1) (i 2)
        * A2 (i 2) (i 3) * A3 (i 3) (i 0))
      = ∑ a : Fin d, ∑ b : Fin d, ∑ c : Fin d, ∑ e : Fin d,
          A0 a b * A1 b c * A2 c e * A3 e a := by
    rw [← Equiv.sum_comp assignEquiv]
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
    simp [assignEquiv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three]
  rw [hsum]
  have hassoc : (A0 * A1) * A2 * A3 = A0 * (A1 * (A2 * A3)) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
  rw [hassoc]
  unfold Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i0 _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
  ring

/-- **The plaquette Wilson loop as a slot-family sum.** With
commuting shifts, the plaquette loop is the sum over index
assignments of the product of its four link-entry factors, with
the slot data of §4 (Q13-3's consumption form of the trace). -/
theorem wilsonLoop_plaquette_eq_sum
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (U : Config Λ G) (x : Λ) (μ ν : Fin 4) :
    wilsonLoop σ ρ U x (plaquetteSteps μ ν)
      = ∑ i : Fin 4 → Fin d, ∏ k : Fin 4,
          linkEntry (plaqSlotMat ρ k) (plaqSlotLink σ x μ ν k)
            (i (plaqRow k)) (i (plaqCol k)) U := by
  have h1 : wilsonLoop σ ρ U x (plaquetteSteps μ ν)
      = Matrix.trace ((repMatrix ρ (U (x, μ)) * repMatrix ρ (U (σ μ x, ν)))
          * repMatrix ρ ((U (σ ν x, μ))⁻¹) * repMatrix ρ ((U (x, ν))⁻¹)) := by
    unfold wilsonLoop
    rw [loopProd_plaquetteSteps σ hσ U x μ ν]
    unfold plaquette
    simp only [repMatrix_mul]
  rw [h1, trace_mul_four]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_four]
  simp only [plaqSlotMat, plaqSlotLink, plaqRow, plaqCol, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, linkEntry, repMatDual, orientDual_apply]

/-- The conjugate word's slot matrices are the conjugates of the
direct word's, step by step. -/
theorem plaqSlotMatConj_eq (k : Fin 4) :
    plaqSlotMatConj ρ k = orientConj (plaqSlotMat ρ k) := by
  fin_cases k <;> simp [plaqSlotMat, plaqSlotMatConj, repMatConj, repMatDual,
    repMatConjDual, orientConjDual]

/-- **The conjugate plaquette loop as a slot-family sum.** The
conjugate of the plaquette loop is the slot sum of the conjugate
word (entrywise conjugation, same links, same wiring). -/
theorem star_wilsonLoop_plaquette_eq_sum
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (U : Config Λ G) (x : Λ) (μ ν : Fin 4) :
    star (wilsonLoop σ ρ U x (plaquetteSteps μ ν))
      = ∑ i : Fin 4 → Fin d, ∏ k : Fin 4,
          linkEntry (plaqSlotMatConj ρ k) (plaqSlotLink σ x μ ν k)
            (i (plaqRow k)) (i (plaqCol k)) U := by
  rw [wilsonLoop_plaquette_eq_sum σ ρ hσ U x μ ν, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [plaqSlotMatConj_eq]
  rfl

/-! ## §5. The plaquette contractions and the per-plaquette identity

The charter's `Contr^s_{p,q}(𝒥)`: the sum over the two words' index
assignments of their slot contractions. The means
`Contr^s_{p,∅}(𝒥) = 𝔼₀[W_p]` and `Contr^s_{∅,q}(𝒥) = 𝔼₀[W_q^s]`
are the one-word contractions. -/

/-- The contraction `Contr⁺_{p,q}(𝒥)` of charter (8): the sum over
the two plaquette words' index assignments of their slot
contractions, `q` read directly. -/
noncomputable def plaqContrPlus (x : Λ) (μ ν : Fin 4) (y : Λ) (α β : Fin 4) : ℂ :=
  ∑ i : Fin 4 → Fin d, ∑ j : Fin 4 → Fin d,
    wordContr μG (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
      (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
      (plaqSlotLink σ y α β) (plaqSlotMat ρ)
      (fun k => j (plaqRow k)) (fun k => j (plaqCol k))

/-- The contraction `Contr⁻_{p,q}(𝒥)` of charter (8): `q` read
through the conjugate word. -/
noncomputable def plaqContrMinus (x : Λ) (μ ν : Fin 4) (y : Λ) (α β : Fin 4) : ℂ :=
  ∑ i : Fin 4 → Fin d, ∑ j : Fin 4 → Fin d,
    wordContr μG (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
      (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
      (plaqSlotLink σ y α β) (plaqSlotMatConj ρ)
      (fun k => j (plaqRow k)) (fun k => j (plaqCol k))

/-- The one-word contraction `Contr_{p,∅}(𝒥)`: the J data of the
mean `𝔼₀[W_p]`. -/
noncomputable def plaqMean (x : Λ) (μ ν : Fin 4) : ℂ :=
  ∑ i : Fin 4 → Fin d, wordMean μG (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
    (fun k => i (plaqRow k)) (fun k => i (plaqCol k))

/-- The one-word contraction of the conjugate word: the J data of
the mean `𝔼₀[conj W_p]`. -/
noncomputable def plaqMeanConj (x : Λ) (μ ν : Fin 4) : ℂ :=
  ∑ i : Fin 4 → Fin d, wordMean μG (plaqSlotLink σ x μ ν) (plaqSlotMatConj ρ)
    (fun k => i (plaqRow k)) (fun k => i (plaqCol k))

/-- The mean of a plaquette loop is its one-word contraction. -/
theorem gibbsExpect_zero_wilsonLoop_plaquette_mean
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x)) (x : Λ) (μ ν : Fin 4) :
    gibbsExpect σ μG ρ 0 (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν))
      = plaqMean σ μG ρ x μ ν := by
  have hfun : (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν))
      = fun U => ∑ i : Fin 4 → Fin d, ∏ k : Fin 4,
          linkEntry (plaqSlotMat ρ k) (plaqSlotLink σ x μ ν k)
            (i (plaqRow k)) (i (plaqCol k)) U :=
    funext fun U => wilsonLoop_plaquette_eq_sum σ ρ hσ U x μ ν
  rw [hfun, gibbsExpect_zero_finset_sum σ μG ρ Finset.univ _
    (fun i _ => integrable_prod_linkEntry (μG := μG)
      (plaqSlotLink σ x μ ν) (plaqSlotMat ρ) (fun k => i (plaqRow k))
      (fun k => i (plaqCol k))
      (fun k x' y' => plaqSlotMat_cont ρ hρcont k x' y')
      (fun k g x' y' => plaqSlotMat_bound ρ hρcont k g x' y'))]
  exact Finset.sum_congr rfl fun i _ =>
    gibbsExpect_zero_slots σ μG ρ (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
      (fun k => i (plaqRow k)) (fun k => i (plaqCol k))

/-- The mean of the conjugate plaquette loop is the conjugate
word's one-word contraction. -/
theorem gibbsExpect_zero_star_wilsonLoop_plaquette
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x)) (x : Λ) (μ ν : Fin 4) :
    gibbsExpect σ μG ρ 0 (fun U => star (wilsonLoop σ ρ U x (plaquetteSteps μ ν)))
      = plaqMeanConj σ μG ρ x μ ν := by
  have hfun : (fun U => star (wilsonLoop σ ρ U x (plaquetteSteps μ ν)))
      = fun U => ∑ i : Fin 4 → Fin d, ∏ k : Fin 4,
          linkEntry (plaqSlotMatConj ρ k) (plaqSlotLink σ x μ ν k)
            (i (plaqRow k)) (i (plaqCol k)) U :=
    funext fun U => star_wilsonLoop_plaquette_eq_sum σ ρ hσ U x μ ν
  rw [hfun, gibbsExpect_zero_finset_sum σ μG ρ Finset.univ _
    (fun i _ => integrable_prod_linkEntry (μG := μG)
      (plaqSlotLink σ x μ ν) (plaqSlotMatConj ρ) (fun k => i (plaqRow k))
      (fun k => i (plaqCol k))
      (fun k x' y' => plaqSlotMatConj_cont ρ hρcont k x' y')
      (fun k g x' y' => plaqSlotMatConj_bound ρ hρcont k g x' y'))]
  exact Finset.sum_congr rfl fun i _ =>
    gibbsExpect_zero_slots σ μG ρ (plaqSlotLink σ x μ ν) (plaqSlotMatConj ρ)
      (fun k => i (plaqRow k)) (fun k => i (plaqCol k))

/-- **Charter (8), direct sign.** `𝔼₀[W_p W_q] = Contr⁺_{p,q}(𝒥)`,
for arbitrary plaquettes `p = (x, μ, ν)`, `q = (y, α, β)` — no
sharing or non-degeneracy hypothesis. -/
theorem gibbsExpect_zero_wilsonLoop_mul_plaquette
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (x : Λ) (μ ν : Fin 4) (y : Λ) (α β : Fin 4) :
    gibbsExpect σ μG ρ 0 (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν)
        * wilsonLoop σ ρ U y (plaquetteSteps α β))
      = plaqContrPlus σ μG ρ x μ ν y α β := by
  have hInt : ∀ (i j : Fin 4 → Fin d), Integrable
      (fun U => (∏ k : Fin 4, linkEntry (plaqSlotMat ρ k) (plaqSlotLink σ x μ ν k)
            (i (plaqRow k)) (i (plaqCol k)) U)
        * (∏ k : Fin 4, linkEntry (plaqSlotMat ρ k) (plaqSlotLink σ y α β k)
            (j (plaqRow k)) (j (plaqCol k)) U)) (configMeasure μG) := by
    intro i j
    refine integrable_of_measurable_bound_one μG
      ((measurable_prod_linkEntry (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
          (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
          (fun k x' y' => plaqSlotMat_cont ρ hρcont k x' y')).mul
        (measurable_prod_linkEntry (plaqSlotLink σ y α β) (plaqSlotMat ρ)
          (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
          (fun k x' y' => plaqSlotMat_cont ρ hρcont k x' y'))) ?_
    intro U
    rw [norm_mul]
    exact mul_le_one₀
      (bound_prod_linkEntry (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
        (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
        (fun k g x' y' => plaqSlotMat_bound ρ hρcont k g x' y') U)
      (norm_nonneg _)
      (bound_prod_linkEntry (plaqSlotLink σ y α β) (plaqSlotMat ρ)
        (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
        (fun k g x' y' => plaqSlotMat_bound ρ hρcont k g x' y') U)
  have hfun : (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν)
        * wilsonLoop σ ρ U y (plaquetteSteps α β))
      = fun U => ∑ i : Fin 4 → Fin d, ∑ j : Fin 4 → Fin d,
          (∏ k : Fin 4, linkEntry (plaqSlotMat ρ k) (plaqSlotLink σ x μ ν k)
            (i (plaqRow k)) (i (plaqCol k)) U)
            * (∏ k : Fin 4, linkEntry (plaqSlotMat ρ k) (plaqSlotLink σ y α β k)
              (j (plaqRow k)) (j (plaqCol k)) U) := by
    funext U
    rw [wilsonLoop_plaquette_eq_sum σ ρ hσ U x μ ν,
      wilsonLoop_plaquette_eq_sum σ ρ hσ U y α β]
    rw [Finset.sum_mul_sum]
  have hIntS : ∀ i ∈ (Finset.univ : Finset (Fin 4 → Fin d)), Integrable
      (fun U => ∑ j : Fin 4 → Fin d,
        (∏ k : Fin 4, linkEntry (plaqSlotMat ρ k) (plaqSlotLink σ x μ ν k)
          (i (plaqRow k)) (i (plaqCol k)) U)
          * (∏ k : Fin 4, linkEntry (plaqSlotMat ρ k) (plaqSlotLink σ y α β k)
            (j (plaqRow k)) (j (plaqCol k)) U)) (configMeasure μG) :=
    fun i _ => integrable_finsetSum Finset.univ (fun j _ => hInt i j)
  rw [hfun, gibbsExpect_zero_finset_sum σ μG ρ Finset.univ _ hIntS]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gibbsExpect_zero_finset_sum σ μG ρ Finset.univ _ (fun j _ => hInt i j)]
  exact Finset.sum_congr rfl fun j _ =>
    gibbsExpect_zero_slots_mul σ μG ρ _ _ _ _ _ _ _ _

/-- **Charter (8), conjugate sign.** `𝔼₀[W_p · conj W_q] =
Contr⁻_{p,q}(𝒥)`, for arbitrary plaquettes — no sharing or
non-degeneracy hypothesis. -/
theorem gibbsExpect_zero_wilsonLoop_mul_star_plaquette
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (x : Λ) (μ ν : Fin 4) (y : Λ) (α β : Fin 4) :
    gibbsExpect σ μG ρ 0 (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν)
        * star (wilsonLoop σ ρ U y (plaquetteSteps α β)))
      = plaqContrMinus σ μG ρ x μ ν y α β := by
  have hInt : ∀ (i j : Fin 4 → Fin d), Integrable
      (fun U => (∏ k : Fin 4, linkEntry (plaqSlotMat ρ k) (plaqSlotLink σ x μ ν k)
            (i (plaqRow k)) (i (plaqCol k)) U)
        * (∏ k : Fin 4, linkEntry (plaqSlotMatConj ρ k) (plaqSlotLink σ y α β k)
            (j (plaqRow k)) (j (plaqCol k)) U)) (configMeasure μG) := by
    intro i j
    refine integrable_of_measurable_bound_one μG
      ((measurable_prod_linkEntry (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
          (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
          (fun k x' y' => plaqSlotMat_cont ρ hρcont k x' y')).mul
        (measurable_prod_linkEntry (plaqSlotLink σ y α β) (plaqSlotMatConj ρ)
          (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
          (fun k x' y' => plaqSlotMatConj_cont ρ hρcont k x' y'))) ?_
    intro U
    rw [norm_mul]
    exact mul_le_one₀
      (bound_prod_linkEntry (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
        (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
        (fun k g x' y' => plaqSlotMat_bound ρ hρcont k g x' y') U)
      (norm_nonneg _)
      (bound_prod_linkEntry (plaqSlotLink σ y α β) (plaqSlotMatConj ρ)
        (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
        (fun k g x' y' => plaqSlotMatConj_bound ρ hρcont k g x' y') U)
  have hfun : (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν)
        * star (wilsonLoop σ ρ U y (plaquetteSteps α β)))
      = fun U => ∑ i : Fin 4 → Fin d, ∑ j : Fin 4 → Fin d,
          (∏ k : Fin 4, linkEntry (plaqSlotMat ρ k) (plaqSlotLink σ x μ ν k)
            (i (plaqRow k)) (i (plaqCol k)) U)
            * (∏ k : Fin 4, linkEntry (plaqSlotMatConj ρ k) (plaqSlotLink σ y α β k)
              (j (plaqRow k)) (j (plaqCol k)) U) := by
    funext U
    rw [wilsonLoop_plaquette_eq_sum σ ρ hσ U x μ ν,
      star_wilsonLoop_plaquette_eq_sum σ ρ hσ U y α β]
    rw [Finset.sum_mul_sum]
  have hIntS : ∀ i ∈ (Finset.univ : Finset (Fin 4 → Fin d)), Integrable
      (fun U => ∑ j : Fin 4 → Fin d,
        (∏ k : Fin 4, linkEntry (plaqSlotMat ρ k) (plaqSlotLink σ x μ ν k)
          (i (plaqRow k)) (i (plaqCol k)) U)
          * (∏ k : Fin 4, linkEntry (plaqSlotMatConj ρ k) (plaqSlotLink σ y α β k)
            (j (plaqRow k)) (j (plaqCol k)) U)) (configMeasure μG) :=
    fun i _ => integrable_finsetSum Finset.univ (fun j _ => hInt i j)
  rw [hfun, gibbsExpect_zero_finset_sum σ μG ρ Finset.univ _ hIntS]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gibbsExpect_zero_finset_sum σ μG ρ Finset.univ _ (fun j _ => hInt i j)]
  exact Finset.sum_congr rfl fun j _ =>
    gibbsExpect_zero_slots_mul σ μG ρ _ _ _ _ _ _ _ _

/-- Integrability of a plaquette loop observable. -/
theorem integrable_wilsonLoop_plaquette
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (x : Λ) (μ ν : Fin 4) :
    Integrable (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν))
      (configMeasure μG) :=
  integrable_of_measurable_bound μG
    (measurable_wilsonLoop σ ρ hρcont x _) (d : ℝ)
    (fun U => norm_wilsonLoop_le σ ρ hd U x _)

/-- Integrability of a conjugate plaquette loop observable. -/
theorem integrable_star_wilsonLoop_plaquette
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (x : Λ) (μ ν : Fin 4) :
    Integrable (fun U => star (wilsonLoop σ ρ U x (plaquetteSteps μ ν)))
      (configMeasure μG) :=
  integrable_of_measurable_bound μG
    (continuous_star.measurable.comp (measurable_wilsonLoop σ ρ hρcont x _)) (d : ℝ)
    (fun U => by rw [norm_star]; exact norm_wilsonLoop_le σ ρ hd U x _)

/-- Integrability of a product of two plaquette loop
observables. -/
theorem integrable_wilsonLoop_mul_plaquette
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (x : Λ) (μ ν : Fin 4) (y : Λ) (α β : Fin 4) :
    Integrable (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν)
        * wilsonLoop σ ρ U y (plaquetteSteps α β)) (configMeasure μG) :=
  integrable_of_measurable_bound μG
    ((measurable_wilsonLoop σ ρ hρcont x _).mul
      (measurable_wilsonLoop σ ρ hρcont y _)) ((d : ℝ) * d)
    (fun U => by
      rw [norm_mul]
      exact mul_le_mul (norm_wilsonLoop_le σ ρ hd U x _)
        (norm_wilsonLoop_le σ ρ hd U y _) (norm_nonneg _) (Nat.cast_nonneg d))

/-- Integrability of a plaquette loop times a conjugate plaquette
loop. -/
theorem integrable_wilsonLoop_mul_star_plaquette
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (x : Λ) (μ ν : Fin 4) (y : Λ) (α β : Fin 4) :
    Integrable (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν)
        * star (wilsonLoop σ ρ U y (plaquetteSteps α β))) (configMeasure μG) :=
  integrable_of_measurable_bound μG
    ((measurable_wilsonLoop σ ρ hρcont x _).mul
      (continuous_star.measurable.comp (measurable_wilsonLoop σ ρ hρcont y _)))
    ((d : ℝ) * d)
    (fun U => by
      rw [norm_mul, norm_star]
      exact mul_le_mul (norm_wilsonLoop_le σ ρ hd U x _)
        (norm_wilsonLoop_le σ ρ hd U y _) (norm_nonneg _) (Nat.cast_nonneg d))

/-- **The plaquette density in loop form.** The complexified
plaquette density is `1 - (W_q + conj W_q) / (2d)`: the
direct/conjugate split of charter (6), at the level of
observables. -/
theorem plaquetteDensityC_eq (hd : 0 < d)
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (y : Λ) (α β : Fin 4) :
    (fun U => (plaquetteDensity σ ρ U y α β : ℂ))
      = fun U => 1 - (wilsonLoop σ ρ U y (plaquetteSteps α β)
          + star (wilsonLoop σ ρ U y (plaquetteSteps α β))) / (2 * (d : ℂ)) := by
  funext U
  have htr : Matrix.trace (repMatrix ρ (plaquette σ U y α β))
      = wilsonLoop σ ρ U y (plaquetteSteps α β) := by
    unfold wilsonLoop
    rw [loopProd_plaquetteSteps σ hσ U y α β]
  have hre : ∀ z : ℂ, (z.re : ℂ) = (z + star z) / 2 := by
    intro z
    apply Complex.ext
    · simp [Complex.div_re, Complex.add_re]
    · simp [Complex.div_im, Complex.add_im]
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold plaquetteDensity
  rw [htr]
  push_cast
  rw [hre]
  field_simp

/-- **The per-plaquette contraction identity (charter (6)+(7)+(8)).**
For arbitrary plaquettes `p = (x, μ, ν)` and `q = (y, α, β)`,

`Cov₀(W_p, D_q) = -(1/2d) ((Contr⁺_{p,q} - 𝔼₀[W_p] 𝔼₀[W_q])
                            + (Contr⁻_{p,q} - 𝔼₀[W_p] 𝔼₀[conj W_q]))`,

with every mean a one-word contraction in the same J data. This is
the per-`q` summand identity that brick Q13-4 substitutes into the
landed link-sharing sum (charter (1)) to obtain `κ_p` in the form
(9); the left-hand side has exactly the shape of the summand of
`covZero_plaquetteLoop_eq_sum`. No sharing, orientation or
non-degeneracy hypothesis is needed: the identity holds for every
pair `(p, q)`, sharing or not. -/
theorem covZero_plaquette_density_eq_contr
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (x : Λ) (μ ν : Fin 4) (y : Λ) (α β : Fin 4) :
    covZero σ μG ρ (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν))
        (fun U => (plaquetteDensity σ ρ U y α β : ℂ))
      = -((1 : ℂ) / (2 * (d : ℂ))) *
          ((plaqContrPlus σ μG ρ x μ ν y α β
              - plaqMean σ μG ρ x μ ν * plaqMean σ μG ρ y α β)
            + (plaqContrMinus σ μG ρ x μ ν y α β
              - plaqMean σ μG ρ x μ ν * plaqMeanConj σ μG ρ y α β)) := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hWp := integrable_wilsonLoop_plaquette σ μG ρ hρcont hd x μ ν
  have hWq := integrable_wilsonLoop_plaquette σ μG ρ hρcont hd y α β
  have hWqstar := integrable_star_wilsonLoop_plaquette σ μG ρ hρcont hd y α β
  have hWpmul := integrable_wilsonLoop_mul_plaquette σ μG ρ hρcont hd x μ ν y α β
  have hWpmulstar := integrable_wilsonLoop_mul_star_plaquette σ μG ρ hρcont hd
    x μ ν y α β
  have hsum : Integrable (fun U => wilsonLoop σ ρ U y (plaquetteSteps α β)
      + star (wilsonLoop σ ρ U y (plaquetteSteps α β))) (configMeasure μG) :=
    hWq.add hWqstar
  have hsumP : Integrable (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν)
        * wilsonLoop σ ρ U y (plaquetteSteps α β)
      + wilsonLoop σ ρ U x (plaquetteSteps μ ν)
        * star (wilsonLoop σ ρ U y (plaquetteSteps α β))) (configMeasure μG) :=
    hWpmul.add hWpmulstar
  have eD : gibbsExpect σ μG ρ 0 (fun U => (plaquetteDensity σ ρ U y α β : ℂ))
      = 1 - (plaqMean σ μG ρ y α β + plaqMeanConj σ μG ρ y α β) / (2 * (d : ℂ)) := by
    rw [plaquetteDensityC_eq σ ρ hd hσ y α β,
      gibbsExpect_zero_sub σ μG ρ (integrable_const (1 : ℂ))
        (hsum.div_const (2 * (d : ℂ))),
      gibbsExpect_zero_const, gibbsExpect_zero_div_const,
      gibbsExpect_zero_add σ μG ρ hWq hWqstar,
      gibbsExpect_zero_wilsonLoop_plaquette_mean σ μG ρ hρcont hσ y α β,
      gibbsExpect_zero_star_wilsonLoop_plaquette σ μG ρ hρcont hσ y α β]
  have hpoint : (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν)
        * (plaquetteDensity σ ρ U y α β : ℂ))
      = fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν)
          - (wilsonLoop σ ρ U x (plaquetteSteps μ ν)
              * wilsonLoop σ ρ U y (plaquetteSteps α β)
            + wilsonLoop σ ρ U x (plaquetteSteps μ ν)
              * star (wilsonLoop σ ρ U y (plaquetteSteps α β))) / (2 * (d : ℂ)) := by
    funext U
    have hDU : (plaquetteDensity σ ρ U y α β : ℂ)
        = 1 - (wilsonLoop σ ρ U y (plaquetteSteps α β)
            + star (wilsonLoop σ ρ U y (plaquetteSteps α β))) / (2 * (d : ℂ)) :=
      congrFun (plaquetteDensityC_eq σ ρ hd hσ y α β) U
    rw [hDU]
    ring
  have eWD : gibbsExpect σ μG ρ 0 (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν)
        * (plaquetteDensity σ ρ U y α β : ℂ))
      = plaqMean σ μG ρ x μ ν
        - (plaqContrPlus σ μG ρ x μ ν y α β + plaqContrMinus σ μG ρ x μ ν y α β)
          / (2 * (d : ℂ)) := by
    rw [hpoint, gibbsExpect_zero_sub σ μG ρ hWp (hsumP.div_const (2 * (d : ℂ))),
      gibbsExpect_zero_div_const,
      gibbsExpect_zero_add σ μG ρ hWpmul hWpmulstar,
      gibbsExpect_zero_wilsonLoop_plaquette_mean σ μG ρ hρcont hσ x μ ν,
      gibbsExpect_zero_wilsonLoop_mul_plaquette σ μG ρ hρcont hσ x μ ν y α β,
      gibbsExpect_zero_wilsonLoop_mul_star_plaquette σ μG ρ hρcont hσ x μ ν y α β]
  show gibbsExpect σ μG ρ 0 (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν)
        * (plaquetteDensity σ ρ U y α β : ℂ))
      - gibbsExpect σ μG ρ 0 (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν))
        * gibbsExpect σ μG ρ 0 (fun U => (plaquetteDensity σ ρ U y α β : ℂ)) = _
  rw [eWD, eD, gibbsExpect_zero_wilsonLoop_plaquette_mean σ μG ρ hρcont hσ x μ ν]
  field_simp
  ring

/-- A step link of a plaquette word lies in the plaquette's link
set. -/
theorem plaqSlotLink_mem_plaquetteLinks
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (x : Λ) (μ ν : Fin 4) (k : Fin 4) :
    plaqSlotLink σ x μ ν k ∈ plaquetteLinks σ x μ ν := by
  rw [plaquetteLinks_eq σ hσ x μ ν]
  fin_cases k <;> simp [plaqSlotLink, Matrix.tail_cons]

/-- **Non-sharing plaquettes do not interact.** If `q`'s link set
is disjoint from `p`'s, then `Cov₀(W_p, D_q) = 0` — proved through
the contraction: at every link at most one word is present, the
contraction splits into the product of the means, and both
centered brackets of the headline identity vanish. (The landed
link-sharing sum (1) does not need these terms; the contraction
language covers them anyway, as the charter requires.) -/
theorem covZero_plaquette_density_eq_zero_of_disjoint
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (x : Λ) (μ ν : Fin 4) (y : Λ) (α β : Fin 4)
    (hdisj : Disjoint (plaquetteLinks σ x μ ν) (plaquetteLinks σ y α β)) :
    covZero σ μG ρ (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν))
        (fun U => (plaquetteDensity σ ρ U y α β : ℂ)) = 0 := by
  have hsplit : ∀ (MB : Fin 4 → (G → Matrix (Fin d) (Fin d) ℂ)) (i j : Fin 4 → Fin d),
      wordContr μG (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
          (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
          (plaqSlotLink σ y α β) MB (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
        = wordMean μG (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
            (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
          * wordMean μG (plaqSlotLink σ y α β) MB
            (fun k => j (plaqRow k)) (fun k => j (plaqCol k)) := by
    intro MB i j
    apply wordContr_eq_wordMean_mul_of_disjoint
    intro ℓ
    by_cases hA : (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)) = ∅
    · exact Or.inl hA
    · right
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k' hk'
      rw [Finset.mem_filter] at hk'
      obtain ⟨k, hk⟩ : (Finset.univ.filter
          (fun k => plaqSlotLink σ x μ ν k = ℓ)).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hA
      rw [Finset.mem_filter] at hk
      have hℓp : ℓ ∈ plaquetteLinks σ x μ ν :=
        hk.2 ▸ plaqSlotLink_mem_plaquetteLinks σ hσ x μ ν k
      have hℓq : ℓ ∈ plaquetteLinks σ y α β :=
        hk'.2 ▸ plaqSlotLink_mem_plaquetteLinks σ hσ y α β k'
      exact (Finset.disjoint_left.mp hdisj hℓp) hℓq
  have hplus : plaqContrPlus σ μG ρ x μ ν y α β
      = plaqMean σ μG ρ x μ ν * plaqMean σ μG ρ y α β := by
    unfold plaqContrPlus plaqMean
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      hsplit (plaqSlotMat ρ) i j
  have hminus : plaqContrMinus σ μG ρ x μ ν y α β
      = plaqMean σ μG ρ x μ ν * plaqMeanConj σ μG ρ y α β := by
    unfold plaqContrMinus plaqMean plaqMeanConj
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      hsplit (plaqSlotMatConj ρ) i j
  rw [covZero_plaquette_density_eq_contr σ μG ρ hρcont hd hσ x μ ν y α β,
    hplus, hminus]
  simp

/-! ## §6. Fiber geometry of plaquette words: the multiplicity fence

A plaquette word reads each link at most twice (its two `μ`-steps
and its two `ν`-steps have different directions, so a fiber is
contained in one direction's step pair), and at most once when no
shift fixes its base site. These are the facts that delimit the
evaluated form of (8) (header fence (i)). -/

/-- The direction of a plaquette word's steps: steps `0, 2` have
direction `μ`, steps `1, 3` have direction `ν`. -/
theorem plaqSlotLink_snd (x : Λ) (μ ν : Fin 4) (k : Fin 4) :
    (plaqSlotLink σ x μ ν k).2 = μ ∨ (plaqSlotLink σ x μ ν k).2 = ν := by
  fin_cases k <;> simp [plaqSlotLink, Matrix.tail_cons]

/-- A plaquette word (with `μ < ν`) reads every link at most
twice. -/
theorem plaqSlotLink_fiber_card_le_two (x : Λ) (μ ν : Fin 4) (hμν : μ < ν)
    (ℓ : Link Λ) :
    (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)).card ≤ 2 := by
  by_cases hμ : ℓ.2 = μ
  · have hsub : Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)
        ⊆ {0, 2} := by
      intro k hk
      rw [Finset.mem_filter] at hk
      have hk2 : (plaqSlotLink σ x μ ν k).2 = μ := by
        rw [hk.2]; exact hμ
      fin_cases k <;> simp [plaqSlotLink, Matrix.tail_cons, ne_of_gt hμν] at hk2 ⊢
    refine le_trans (Finset.card_le_card hsub) ?_
    simp
  · by_cases hν : ℓ.2 = ν
    · have hsub : Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)
          ⊆ {1, 3} := by
        intro k hk
        rw [Finset.mem_filter] at hk
        have hk2 : (plaqSlotLink σ x μ ν k).2 = ν := by
          rw [hk.2]; exact hν
        fin_cases k <;> simp [plaqSlotLink, Matrix.tail_cons, ne_of_lt hμν] at hk2 ⊢
      refine le_trans (Finset.card_le_card hsub) ?_
      simp
    · have hempty : Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)
          = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro k hk
        rw [Finset.mem_filter] at hk
        rcases plaqSlotLink_snd σ x μ ν k with h | h
        · exact hμ (hk.2 ▸ h)
        · exact hν (hk.2 ▸ h)
      rw [hempty]
      simp

/-- A plaquette word whose base site is fixed by neither shift
reads every link at most once. -/
theorem plaqSlotLink_fiber_card_le_one (x : Λ) (μ ν : Fin 4) (hμν : μ < ν)
    (hνx : σ ν x ≠ x) (hμx : σ μ x ≠ x) (ℓ : Link Λ) :
    (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro k₁ hk₁ k₂ hk₂
  rw [Finset.mem_filter] at hk₁ hk₂
  have heq : plaqSlotLink σ x μ ν k₁ = plaqSlotLink σ x μ ν k₂ :=
    hk₁.2.trans hk₂.2.symm
  have hμν' : μ ≠ ν := ne_of_lt hμν
  have hνμ' : ν ≠ μ := ne_of_gt hμν
  fin_cases k₁ <;> fin_cases k₂ <;> simp_all [plaqSlotLink, Matrix.tail_cons]
  all_goals
    have h12 := hk₁.trans hk₂.symm
    rw [Prod.mk.injEq] at h12
    rcases h12 with ⟨h1, h2⟩
    first
      | exact absurd h2 hμν'
      | exact absurd h2 hνμ'
      | exact absurd h1.symm hμx
      | exact absurd h1 hμx
      | exact absurd h1.symm hνx
      | exact absurd h1 hνx

/-- **Classification of plaquette link factors.** Under the
pattern hypothesis `hgood` — no link's combined fiber (both words
together) has cardinality `> 2` — every one-link factor of both
`Contr⁺_{p,q}` and `Contr⁻_{p,q}` is one of the six evaluated J
values of §2, link by link, for every index assignment. The
hypothesis `hgood` fails exactly on the named PARTIAL class of
header fence (i): a doubled link (base site fixed by the
transverse shift) shared with the other word. -/
theorem plaqLinkContr_classify (x : Λ) (μ ν : Fin 4) (hμν : μ < ν)
    (y : Λ) (α β : Fin 4) (hαβ : α < β)
    (hgood : ∀ ℓ : Link Λ,
      (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)).card
        + (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ)).card ≤ 2)
    (MB : Fin 4 → (G → Matrix (Fin d) (Fin d) ℂ)) (i j : Fin 4 → Fin d) (ℓ : Link Λ) :
    (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)) = ∅
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ)) = ∅
        ∧ linkContr μG (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ))
            (plaqSlotMat ρ) (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
            (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ))
            MB (fun k => j (plaqRow k)) (fun k => j (plaqCol k)) = 1
    ∨ (∃ k₀, (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)) = {k₀}
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ)) = ∅
        ∧ linkContr μG (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ))
            (plaqSlotMat ρ) (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
            (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ))
            MB (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
          = haarTwirl1 μG (plaqSlotMat ρ k₀) (i (plaqRow k₀)) (i (plaqCol k₀)))
    ∨ (∃ k₀, (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)) = ∅
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ)) = {k₀}
        ∧ linkContr μG (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ))
            (plaqSlotMat ρ) (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
            (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ))
            MB (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
          = haarTwirl1 μG (MB k₀) (j (plaqRow k₀)) (j (plaqCol k₀)))
    ∨ (∃ k₀ k₁, k₀ ≠ k₁
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)) = {k₀, k₁}
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ)) = ∅
        ∧ linkContr μG (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ))
            (plaqSlotMat ρ) (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
            (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ))
            MB (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
          = haarTwirl μG (plaqSlotMat ρ k₀) (plaqSlotMat ρ k₁)
              (i (plaqRow k₀), i (plaqRow k₁)) (i (plaqCol k₀), i (plaqCol k₁)))
    ∨ (∃ k₀ k₁, (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)) = {k₀}
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ)) = {k₁}
        ∧ linkContr μG (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ))
            (plaqSlotMat ρ) (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
            (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ))
            MB (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
          = haarTwirl μG (plaqSlotMat ρ k₀) (MB k₁)
              (i (plaqRow k₀), j (plaqRow k₁)) (i (plaqCol k₀), j (plaqCol k₁)))
    ∨ (∃ k₀ k₁, k₀ ≠ k₁
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)) = ∅
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ)) = {k₀, k₁}
        ∧ linkContr μG (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ))
            (plaqSlotMat ρ) (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
            (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ))
            MB (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
          = haarTwirl μG (MB k₀) (MB k₁)
              (j (plaqRow k₀), j (plaqRow k₁)) (j (plaqCol k₀), j (plaqCol k₁))) :=
  linkContr_classify μG (plaqSlotMat ρ) (fun k => i (plaqRow k))
    (fun k => i (plaqCol k)) MB (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
    _ _ (plaqSlotLink_fiber_card_le_two σ x μ ν hμν ℓ)
    (plaqSlotLink_fiber_card_le_two σ y α β hαβ ℓ) (hgood ℓ)

/-- **The generic seat is fully evaluated.** If no shift fixes
either plaquette's base site, the pattern hypothesis `hgood`
holds: every fiber has cardinality `≤ 1` per word, so the
classification `plaqLinkContr_classify` applies to every link,
every index assignment, and both signs (`MB := plaqSlotMat ρ` for
`Contr⁺`, `MB := plaqSlotMatConj ρ` for `Contr⁻`). -/
theorem plaqLinkContr_classify_of_not_fixed (x : Λ) (μ ν : Fin 4) (hμν : μ < ν)
    (hνx : σ ν x ≠ x) (hμx : σ μ x ≠ x)
    (y : Λ) (α β : Fin 4) (hαβ : α < β)
    (hβy : σ β y ≠ y) (hαy : σ α y ≠ y)
    (MB : Fin 4 → (G → Matrix (Fin d) (Fin d) ℂ)) (i j : Fin 4 → Fin d)
    (ℓ : Link Λ) :
    (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)) = ∅
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ)) = ∅
        ∧ linkContr μG (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ))
            (plaqSlotMat ρ) (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
            (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ))
            MB (fun k => j (plaqRow k)) (fun k => j (plaqCol k)) = 1
    ∨ (∃ k₀, (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)) = {k₀}
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ)) = ∅
        ∧ linkContr μG (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ))
            (plaqSlotMat ρ) (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
            (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ))
            MB (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
          = haarTwirl1 μG (plaqSlotMat ρ k₀) (i (plaqRow k₀)) (i (plaqCol k₀)))
    ∨ (∃ k₀, (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)) = ∅
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ)) = {k₀}
        ∧ linkContr μG (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ))
            (plaqSlotMat ρ) (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
            (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ))
            MB (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
          = haarTwirl1 μG (MB k₀) (j (plaqRow k₀)) (j (plaqCol k₀)))
    ∨ (∃ k₀ k₁, k₀ ≠ k₁
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)) = {k₀, k₁}
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ)) = ∅
        ∧ linkContr μG (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ))
            (plaqSlotMat ρ) (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
            (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ))
            MB (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
          = haarTwirl μG (plaqSlotMat ρ k₀) (plaqSlotMat ρ k₁)
              (i (plaqRow k₀), i (plaqRow k₁)) (i (plaqCol k₀), i (plaqCol k₁)))
    ∨ (∃ k₀ k₁, (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)) = {k₀}
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ)) = {k₁}
        ∧ linkContr μG (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ))
            (plaqSlotMat ρ) (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
            (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ))
            MB (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
          = haarTwirl μG (plaqSlotMat ρ k₀) (MB k₁)
              (i (plaqRow k₀), j (plaqRow k₁)) (i (plaqCol k₀), j (plaqCol k₁)))
    ∨ (∃ k₀ k₁, k₀ ≠ k₁
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)) = ∅
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ)) = {k₀, k₁}
        ∧ linkContr μG (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ))
            (plaqSlotMat ρ) (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
            (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ))
            MB (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
          = haarTwirl μG (MB k₀) (MB k₁)
              (j (plaqRow k₀), j (plaqRow k₁)) (j (plaqCol k₀), j (plaqCol k₁))) :=
  plaqLinkContr_classify σ μG ρ x μ ν hμν y α β hαβ
    (fun ℓ => add_le_add
      (plaqSlotLink_fiber_card_le_one σ x μ ν hμν hνx hμx ℓ)
      (plaqSlotLink_fiber_card_le_one σ y α β hαβ hβy hαy ℓ)) MB i j ℓ

end Setup

end ThetLogos
