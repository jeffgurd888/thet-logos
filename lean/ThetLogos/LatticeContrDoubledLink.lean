import ThetLogos.LatticeContr

/-
# The doubled-link evaluation at general geometry (gap-queue Q13, the residue brick)

HONESTY LEDGER — read this before citing anything from this file.

## 0. What this file is

Tier: **T1 at the finite-lattice level** — machine-checked theorems
about one fixed finite lattice, in the same setting as
`ThetLogos.LatticeContr` (brick Q13-3), which this module imports
unchanged and extends.

Q13 closed **STANDS-with-one-named-PARTIAL** (2026-10-24): the sole
residue was Q13-3's — the *evaluated* twirl-entry form of the
one-link contraction factor `linkContr` is asserted there only for
combined fiber cardinality `≤ 2` (`linkContr_classify`, under
`sA.card + sB.card ≤ 2`; the plaquette lift `plaqLinkContr_classify`
under the pattern hypothesis `hgood`). The excluded patterns are
exactly `(2,1)`, `(1,2)`, `(2,2)` — combined fiber cardinality `3`
or `4` — and they occur geometrically exactly on the named class of
Q13-3's header fence (i): a plaquette base site fixed by the
transverse shift (`σ ν x = x` doubles the `μ`-links; `σ μ x = x`
doubles the `ν`-links), whose doubled link is also read by the
other word. There the link factor is a higher Haar moment, not a
pair twirl.

## 1. What this module proves

The three excluded patterns are evaluated as entries of the next
two J-moment tensors, defined here in the family's own entry form:

- `haarTwirl3 μG M N P` — the triple twirl, a matrix on
  `Fin d × Fin d × Fin d` with entries
  `∫ g, M g · * N g · * P g · ∂μG`;
- `haarTwirl4 μG M N P Q` — the quadruple twirl, likewise.

Evaluations: `linkContr_pair_singleton` (pattern `(2,1)`),
`linkContr_singleton_pair` (pattern `(1,2)`),
`linkContr_pair_pair` (pattern `(2,2)`). Capstones:
`linkContr_classify_general` — the one-link classification with the
cardinality-sum hypothesis of `linkContr_classify` **dropped**;
and `plaqLinkContr_classify_general` — the plaquette classification
with the pattern hypothesis `hgood` of `plaqLinkContr_classify`
**dropped**: for every pair of plaquettes (`μ < ν`, `α < β`), with
no fixed-base hypothesis, every one-link factor of both contraction
signs is one of the nine evaluated J values. This is the
doubled-link evaluation at general geometry: the residue is
discharged, and Q13's PARTIAL is closed.

## 2. Scope fences (binding on this module)

**(i) Evaluation, not intertwiner theory.** The triple and
quadruple twirls are defined and used in entry form only, exactly
as far as the evaluations require. No Schur / Clebsch–Gordan
expansion of the higher J tensors is built or implied (the Q13
charter's excluded reading 1 stays excluded), and no invariance
theory of `haarTwirl3` / `haarTwirl4` beyond their entries is
asserted.

**(ii) Multiplicity fence unchanged.** No word reads a link more
than twice per word (`plaqSlotLink_fiber_card_le_two` is a theorem
of Q13-3), so patterns beyond `(2,2)` do not occur for plaquette
words and are not treated.

**(iii) Finite-volume clause.** Every statement is at fixed finite
`Λ`. No limit — in volume, in spacing, in anything — is taken or
asserted.

**(iv) Clay clause.** Parts of the official Clay Yang–Mills
statement closed by this module: **0**. **NO CLAIM.**

This module is NOT in the root import list of the library (the
corpus pattern for recent exhibits); it is verified by a targeted
build.
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

/-! ## §1. The higher J-moment tensors, entry form

The one-factor twirl `𝒥(M)` and the pair twirl `𝒥(M, N)` of
`LatticeTwirl` are the first two moment tensors of the J data. The
doubled-link patterns `(2,1)`, `(1,2)`, `(2,2)` are entries of the
next two, defined here at the contraction's seat (all matrix
functions on `Fin d`), in the same entry form. -/

/-- The **triple Haar twirl** `𝒥(M, N, P)`, entry form:
`𝒥(M,N,P) (a₁,a₂,a₃) (b₁,b₂,b₃) = ∫ g, M g a₁ b₁ * N g a₂ b₂ *
P g a₃ b₃ ∂μG`. No matrix-valued integral is used; the operator is
its entry matrix. -/
noncomputable def haarTwirl3 (M N P : G → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ :=
  Matrix.of fun p q => ∫ g, M g p.1 q.1 * N g p.2.1 q.2.1 * P g p.2.2 q.2.2 ∂μG

theorem haarTwirl3_apply (M N P : G → Matrix (Fin d) (Fin d) ℂ)
    (p q : Fin d × Fin d × Fin d) :
    haarTwirl3 μG M N P p q
      = ∫ g, M g p.1 q.1 * N g p.2.1 q.2.1 * P g p.2.2 q.2.2 ∂μG := rfl

/-- The **quadruple Haar twirl** `𝒥(M, N, P, Q)`, entry form:
`𝒥(M,N,P,Q) (a₁,a₂,a₃,a₄) (b₁,b₂,b₃,b₄) = ∫ g, M g a₁ b₁ *
N g a₂ b₂ * P g a₃ b₃ * Q g a₄ b₄ ∂μG`. -/
noncomputable def haarTwirl4 (M N P Q : G → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d × Fin d) ℂ :=
  Matrix.of fun p q => ∫ g, M g p.1 q.1 * N g p.2.1 q.2.1 * P g p.2.2.1 q.2.2.1
    * Q g p.2.2.2 q.2.2.2 ∂μG

theorem haarTwirl4_apply (M N P Q : G → Matrix (Fin d) (Fin d) ℂ)
    (p q : Fin d × Fin d × Fin d × Fin d) :
    haarTwirl4 μG M N P Q p q
      = ∫ g, M g p.1 q.1 * N g p.2.1 q.2.1 * P g p.2.2.1 q.2.2.1
        * Q g p.2.2.2 q.2.2.2 ∂μG := rfl

/-! ## §2. Evaluation of the doubled-link patterns

The three patterns `linkContr_classify` excludes: combined fiber
cardinality `3` or `4`. Each is a higher-twirl entry, by the same
fiber-product computation as the six patterns of `LatticeContr`
§2, carried one moment higher. -/

/-- Pattern `(2,1)` — **the doubled link read once by the other
word**: both factors of the first family (one word reads the link
twice — the doubled link of a transverse-shift-fixed base) and one
factor of the second family. The factor is the triple-twirl entry
`𝒥(M, M', N)`. -/
theorem linkContr_pair_singleton {ιA ιB : Type*} [DecidableEq ιA]
    (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d)
    {i₀ i₁ : ιA} (h : i₀ ≠ i₁) (j₀ : ιB) :
    linkContr μG {i₀, i₁} MA aA bA {j₀} MB aB bB
      = haarTwirl3 μG (MA i₀) (MA i₁) (MB j₀)
          (aA i₀, aA i₁, aB j₀) (bA i₀, bA i₁, bB j₀) := by
  show (∫ g, (∏ i ∈ {i₀, i₁}, MA i g (aA i) (bA i))
      * (∏ j ∈ {j₀}, MB j g (aB j) (bB j)) ∂μG) = _
  rw [haarTwirl3_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show (∏ i ∈ {i₀, i₁}, MA i g (aA i) (bA i)) * (∏ j ∈ {j₀}, MB j g (aB j) (bB j))
      = MA i₀ g (aA i₀) (bA i₀) * MA i₁ g (aA i₁) (bA i₁) * MB j₀ g (aB j₀) (bB j₀)
  rw [Finset.prod_pair h, Finset.prod_singleton]

/-- Pattern `(1,2)`: one factor of the first family and both
factors of the second family (the other word's doubled link, read
once by the first). The factor is the triple-twirl entry
`𝒥(M, N, N')`. -/
theorem linkContr_singleton_pair {ιA ιB : Type*} [DecidableEq ιB]
    (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d)
    (i₀ : ιA) {j₀ j₁ : ιB} (h : j₀ ≠ j₁) :
    linkContr μG {i₀} MA aA bA {j₀, j₁} MB aB bB
      = haarTwirl3 μG (MA i₀) (MB j₀) (MB j₁)
          (aA i₀, aB j₀, aB j₁) (bA i₀, bB j₀, bB j₁) := by
  show (∫ g, (∏ i ∈ {i₀}, MA i g (aA i) (bA i))
      * (∏ j ∈ {j₀, j₁}, MB j g (aB j) (bB j)) ∂μG) = _
  rw [haarTwirl3_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show (∏ i ∈ {i₀}, MA i g (aA i) (bA i)) * (∏ j ∈ {j₀, j₁}, MB j g (aB j) (bB j))
      = MA i₀ g (aA i₀) (bA i₀) * MB j₀ g (aB j₀) (bB j₀) * MB j₁ g (aB j₁) (bB j₁)
  rw [Finset.prod_singleton, Finset.prod_pair h, mul_assoc]

/-- Pattern `(2,2)` — **both words double the shared link**: two
factors from each family, combined fiber cardinality `4`. The
factor is the quadruple-twirl entry `𝒥(M, M', N, N')`. -/
theorem linkContr_pair_pair {ιA ιB : Type*} [DecidableEq ιA] [DecidableEq ιB]
    (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d)
    {i₀ i₁ : ιA} (hA : i₀ ≠ i₁) {j₀ j₁ : ιB} (hB : j₀ ≠ j₁) :
    linkContr μG {i₀, i₁} MA aA bA {j₀, j₁} MB aB bB
      = haarTwirl4 μG (MA i₀) (MA i₁) (MB j₀) (MB j₁)
          (aA i₀, aA i₁, aB j₀, aB j₁) (bA i₀, bA i₁, bB j₀, bB j₁) := by
  show (∫ g, (∏ i ∈ {i₀, i₁}, MA i g (aA i) (bA i))
      * (∏ j ∈ {j₀, j₁}, MB j g (aB j) (bB j)) ∂μG) = _
  rw [haarTwirl4_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show (∏ i ∈ {i₀, i₁}, MA i g (aA i) (bA i)) * (∏ j ∈ {j₀, j₁}, MB j g (aB j) (bB j))
      = MA i₀ g (aA i₀) (bA i₀) * MA i₁ g (aA i₁) (bA i₁)
        * MB j₀ g (aB j₀) (bB j₀) * MB j₁ g (aB j₁) (bB j₁)
  rw [Finset.prod_pair hA, Finset.prod_pair hB]
  ring

/-! ## §3. The one-link classification at general cardinality

`linkContr_classify` of `LatticeContr`, with the cardinality-sum
hypothesis dropped: each fiber may independently have cardinality
`≤ 2`, and all nine patterns are evaluated — the six of Q13-3 plus
the three doubled-link patterns of §2. -/

/-- **Classification of one-link factors, general form.** If both
fibers have cardinality `≤ 2` — with **no** hypothesis on their
sum — the link factor is one of the nine evaluated J values, with
the fiber shapes and slot witnesses recorded. The last three
values are the higher Haar moments of the doubled-link patterns
`(2,1)`, `(1,2)`, `(2,2)`: this is `linkContr_classify` with its
excluded class discharged. -/
theorem linkContr_classify_general {ιA ιB : Type*} [DecidableEq ιA] [DecidableEq ιB]
    (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ) (aA bA : ιA → Fin d)
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d)
    (sA : Finset ιA) (sB : Finset ιB)
    (hcA : sA.card ≤ 2) (hcB : sB.card ≤ 2) :
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
          = haarTwirl μG (MB j) (MB j') (aB j, aB j') (bB j, bB j'))
    ∨ (∃ i i' j, i ≠ i' ∧ sA = {i, i'} ∧ sB = {j}
        ∧ linkContr μG sA MA aA bA sB MB aB bB
          = haarTwirl3 μG (MA i) (MA i') (MB j)
              (aA i, aA i', aB j) (bA i, bA i', bB j))
    ∨ (∃ i j j', j ≠ j' ∧ sA = {i} ∧ sB = {j, j'}
        ∧ linkContr μG sA MA aA bA sB MB aB bB
          = haarTwirl3 μG (MA i) (MB j) (MB j')
              (aA i, aB j, aB j') (bA i, bB j, bB j'))
    ∨ (∃ i i' j j', i ≠ i' ∧ j ≠ j' ∧ sA = {i, i'} ∧ sB = {j, j'}
        ∧ linkContr μG sA MA aA bA sB MB aB bB
          = haarTwirl4 μG (MA i) (MA i') (MB j) (MB j')
              (aA i, aA i', aB j, aB j') (bA i, bA i', bB j, bB j')) := by
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
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, j', hjne, hsA, hj, ?_⟩)))))
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
  · -- (1,2)
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hA
    obtain ⟨j, j', hjne, hj⟩ := Finset.card_eq_two.mp hB
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨i, j, j', hjne, hi, hj, ?_⟩)))))))
    rw [hi, hj]
    exact linkContr_singleton_pair μG MA aA bA MB aB bB i hjne
  · -- (2,0)
    obtain ⟨i, i', hine, hi⟩ := Finset.card_eq_two.mp hA
    have hsB : sB = ∅ := Finset.card_eq_zero.mp hB
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨i, i', hine, hi, hsB, ?_⟩)))
    rw [hi, hsB]
    exact linkContr_pair_empty μG MA aA bA MB aB bB hine
  · -- (2,1)
    obtain ⟨i, i', hine, hi⟩ := Finset.card_eq_two.mp hA
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hB
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨i, i', j, hine, hi, hj, ?_⟩))))))
    rw [hi, hj]
    exact linkContr_pair_singleton μG MA aA bA MB aB bB hine j
  · -- (2,2)
    obtain ⟨i, i', hine, hi⟩ := Finset.card_eq_two.mp hA
    obtain ⟨j, j', hjne, hj⟩ := Finset.card_eq_two.mp hB
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨i, i', j, j', hine, hjne, hi, hj, ?_⟩)))))))
    rw [hi, hj]
    exact linkContr_pair_pair μG MA aA bA MB aB bB hine hjne

/-! ## §4. The plaquette classification at general geometry

`plaqLinkContr_classify` of `LatticeContr` needed the pattern
hypothesis `hgood` — no link's combined fiber has cardinality
`> 2` — which fails exactly on the doubled-link class. With the
nine-pattern classification of §3, each word's fiber bound
(`plaqSlotLink_fiber_card_le_two`, a theorem) is all that is
needed: the classification now holds for **every** pair of
plaquettes, transverse-shift-fixed bases included. -/

/-- **Classification of plaquette link factors at general
geometry.** For every two plaquettes (`μ < ν`, `α < β`) — with
**no** hypothesis on the shifts fixing the base sites and no
pattern hypothesis — every one-link factor of the two-word
contraction is one of the nine evaluated J values of §3, link by
link, for every index assignment. Both signs are covered by the
choice of `MB` (`plaqSlotMat ρ` for `Contr⁺`, `plaqSlotMatConj ρ`
for `Contr⁻`). The last three values are the doubled-link
evaluations: a link doubled by one word and read by the other —
the named PARTIAL class of Q13-3 — is a triple- or quadruple-twirl
entry. -/
theorem plaqLinkContr_classify_general (x : Λ) (μ ν : Fin 4) (hμν : μ < ν)
    (y : Λ) (α β : Fin 4) (hαβ : α < β)
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
              (j (plaqRow k₀), j (plaqRow k₁)) (j (plaqCol k₀), j (plaqCol k₁)))
    ∨ (∃ k₀ k₁ k₂, k₀ ≠ k₁
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)) = {k₀, k₁}
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ)) = {k₂}
        ∧ linkContr μG (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ))
            (plaqSlotMat ρ) (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
            (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ))
            MB (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
          = haarTwirl3 μG (plaqSlotMat ρ k₀) (plaqSlotMat ρ k₁) (MB k₂)
              (i (plaqRow k₀), i (plaqRow k₁), j (plaqRow k₂))
              (i (plaqCol k₀), i (plaqCol k₁), j (plaqCol k₂)))
    ∨ (∃ k₀ k₁ k₂, k₁ ≠ k₂
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)) = {k₀}
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ)) = {k₁, k₂}
        ∧ linkContr μG (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ))
            (plaqSlotMat ρ) (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
            (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ))
            MB (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
          = haarTwirl3 μG (plaqSlotMat ρ k₀) (MB k₁) (MB k₂)
              (i (plaqRow k₀), j (plaqRow k₁), j (plaqRow k₂))
              (i (plaqCol k₀), j (plaqCol k₁), j (plaqCol k₂)))
    ∨ (∃ k₀ k₁ k₂ k₃, k₀ ≠ k₁ ∧ k₂ ≠ k₃
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ)) = {k₀, k₁}
        ∧ (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ)) = {k₂, k₃}
        ∧ linkContr μG (Finset.univ.filter (fun k => plaqSlotLink σ x μ ν k = ℓ))
            (plaqSlotMat ρ) (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
            (Finset.univ.filter (fun k => plaqSlotLink σ y α β k = ℓ))
            MB (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
          = haarTwirl4 μG (plaqSlotMat ρ k₀) (plaqSlotMat ρ k₁) (MB k₂) (MB k₃)
              (i (plaqRow k₀), i (plaqRow k₁), j (plaqRow k₂), j (plaqRow k₃))
              (i (plaqCol k₀), i (plaqCol k₁), j (plaqCol k₂), j (plaqCol k₃))) :=
  linkContr_classify_general μG (plaqSlotMat ρ) (fun k => i (plaqRow k))
    (fun k => i (plaqCol k)) MB (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
    _ _ (plaqSlotLink_fiber_card_le_two σ x μ ν hμν ℓ)
    (plaqSlotLink_fiber_card_le_two σ y α β hαβ ℓ)

end Setup

end ThetLogos
