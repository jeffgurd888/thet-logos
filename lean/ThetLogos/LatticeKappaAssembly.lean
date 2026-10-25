import ThetLogos.LatticeContr

/-!
# The assembled κ_p: assembly and consistency discharge (Q13-4)

**NO CLAIM.** Parts of any official Clay statement closed: **0**.
Stage 1b-B label unchanged (U(1) T1 at all β ≥ 0; general (G, ρ)
OPEN). This module is the assembly brick Q13-4 of gap queue Q13
(Stage 1c-0 clause (ii)), per the re-price charter
`whitepaper/stage1c0-q13-reprice-2026-10-24.md`. It proves no new
analysis: it substitutes Q13-3's centered contraction headline
into the landed link-sharing sum (charter (1)) to obtain the
closed form (9) of κ_p at general (G, ρ), and then discharges the
charter's three frozen consistency checks against the assembled
formula:

- **C2 (assembly / termwise agreement).** `kappa_eq_sum_contr` and
  its factored form `kappa_eq_contr`: κ_p is the sum over the
  link-sharing plaquettes of the per-plaquette contraction
  brackets `kappaContrTerm`, i.e. charter (9) with every summand
  in J-twirl contraction data. Pure substitution of
  `covZero_plaquette_density_eq_contr` (Q13-3) into
  `covZero_plaquetteLoop_eq_sum` (Stage 1c-0). The derivative
  form is recovered as the negative of (9) only through the
  landed `deriv_plaquetteLoop_eq`
  (`deriv_plaquetteLoop_eq_contr`); no new sign convention.
- **C3 (guards).** (§2) The assembled contraction is unchanged
  by cyclic rotation of either plaquette word — in fact by any
  permutation of either word's step slots (`wordContr_reindex_left`
  / `wordContr_reindex_right`, instantiated at the cyclic
  rotation `rot4`) — and by simultaneous relabeling of all
  contracted indices by a permutation of `Fin d`
  (`plaqContrPlus_relabel`, `plaqContrMinus_relabel`). (§3) At
  the entries-one seat — every `repMatrix ρ` entry equal to `1`,
  the pattern of the trivial one-dimensional representation —
  κ_p vanishes: the contraction evaluations are all `1`
  (`wordContr_eq_one_of_entries_one`,
  `wordMean_eq_one_of_entries_one`), the centered brackets cancel
  (`covZero_plaquette_density_eq_zero_of_entries_one`), and hence
  `kappa_eq_zero_of_entries_one`; Q13-2's entries-one seat
  `covZero_prod_linkEntry_eq_zero_of_entries_one` is also consumed
  directly at the plaquette slot families.
- **C1 (circle/fundamental specialization).** (§4) At
  `G = Circle`, `ρ = circleRep`, `Λ = Fin 4 → ZMod N`,
  `σ = torusShift N` (`N ≥ 2`), the J data collapses: the slot
  fiber products are the landed per-link character factors
  (`fiberProd_circle`, `fiberProdConj_circle`), the one-factor
  twirls kill every mean (`plaqMean_circle_eq_zero`,
  `plaqMeanConj_circle_eq_zero`), the direct contraction vanishes
  (`plaqContrPlus_circle_eq_zero`) and the conjugate contraction
  is the diagonal indicator (`plaqContrMinus_circle`). The
  per-plaquette discharge
  `covZero_circle_plaquette_density_contr` recovers
  `Cov₀(W_p, D_q) = -1/2` for `q = p` and `0` otherwise, in exact
  agreement with the landed `covZero_circle_plaquette_density`,
  and the assembled total `assembled_kappa_circle` /
  `kappa_circle_plaquette_contr` recovers `κ_p = -1/2`, in exact
  agreement with `kappa_circle_plaquette`. At this seat no shift
  fixes a site (`torusShift_ne_self`), so the doubled-link
  PARTIAL class of Q13-3 (header fence (i) there) does not arise:
  every fiber has cardinality `≤ 1` per word, and at `d = 1` the
  fiber integrals are the scalar character integrals above.

Header fence: the Q13-3 PARTIAL is inherited, not discharged
here — the *evaluated* twirl-entry form of the contraction at
general (G, ρ) remains unasserted on the doubled-link class
named in `LatticeContr` (a plaquette base site fixed by the
transverse shift whose doubled link is also read by the other
word). The assembly (C2), the guards (C3) and the circle
discharge (C1) are unconditional within their stated seats:
C2/C3(a) at general (G, ρ), C3(b) at the entries-one seat,
C1 at the circle/fundamental seat, where the PARTIAL class is
empty.

- Status: brick Q13-4 — built 2026-10-24 under the gap queue;
  verdict STANDS (C1/C2/C3 all pass; Q13 closes
  STANDS-with-one-named-PARTIAL, the Q13-3 doubled-link
  evaluation residue); parent-verified 2026-10-24 (targeted
  build exit 0, strict recount, axiom check). Dossier:
  `whitepaper/stage1c0-q13-closes-2026-10-24.md`.
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

/-! ## §1. C2 — the assembly (charter (9))

The per-plaquette contraction bracket, then the substitution of
Q13-3's centered headline into the landed clause-(ii) sum. -/

/-- The **per-plaquette contraction bracket** of charter (9): the
summand the assembled formula assigns to a plaquette
`q = (y, α, β)`, in J-twirl contraction data — the centered direct
bracket plus the centered conjugate bracket, with the `-(1/2d)`
density factor. It is, definitionally, the right-hand side of
Q13-3's `covZero_plaquette_density_eq_contr` at `q`. -/
noncomputable def kappaContrTerm (x : Λ) (μ ν : Fin 4)
    (q : Λ × Fin 4 × Fin 4) : ℂ :=
  -((1 : ℂ) / (2 * (d : ℂ))) *
    ((plaqContrPlus σ μG ρ x μ ν q.1 q.2.1 q.2.2
        - plaqMean σ μG ρ x μ ν * plaqMean σ μG ρ q.1 q.2.1 q.2.2)
      + (plaqContrMinus σ μG ρ x μ ν q.1 q.2.1 q.2.2
        - plaqMean σ μG ρ x μ ν * plaqMeanConj σ μG ρ q.1 q.2.1 q.2.2))

/-- **C2, sum form.** κ_p is the link-sharing sum of the
contraction brackets: substitute the per-plaquette identity
`covZero_plaquette_density_eq_contr` into the landed
`covZero_plaquetteLoop_eq_sum`. Pure substitution — this is the
termwise agreement of the J formula with the landed summands of
(1), for every `q ∈ sharingPlaquettes`, at general (G, ρ),
reducible ρ included (the centering means are the one-factor
twirl contractions, not set to zero). -/
theorem kappa_eq_sum_contr
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (x : Λ) (μ ν : Fin 4) :
    covZero σ μG ρ (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν))
        (fun U => (actionDensity σ ρ U : ℂ))
      = ∑ q ∈ sharingPlaquettes σ (plaquetteLinks σ x μ ν),
          kappaContrTerm σ μG ρ x μ ν q := by
  rw [covZero_plaquetteLoop_eq_sum σ μG ρ hρcont hd hσ x μ ν]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [covZero_plaquette_density_eq_contr σ μG ρ hρcont hd hσ x μ ν
    q.1 q.2.1 q.2.2]
  rfl

/-- **C2, charter (9) form.** κ_p as the factored contraction
expression: the `-(1/2d)` density factor outside the link-sharing
sum of centered direct-plus-conjugate contraction brackets, all
in J data (`plaqContrPlus` / `plaqContrMinus` are the
`Contr^±_{p,q}(𝒥)` of charter (8); `plaqMean` / `plaqMeanConj`
the one-word contractions `Contr_{p,∅}(𝒥)`, `Contr^±_{∅,q}(𝒥)`). -/
theorem kappa_eq_contr
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (x : Λ) (μ ν : Fin 4) :
    covZero σ μG ρ (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν))
        (fun U => (actionDensity σ ρ U : ℂ))
      = -((1 : ℂ) / (2 * (d : ℂ))) *
          ∑ q ∈ sharingPlaquettes σ (plaquetteLinks σ x μ ν),
            ((plaqContrPlus σ μG ρ x μ ν q.1 q.2.1 q.2.2
                - plaqMean σ μG ρ x μ ν * plaqMean σ μG ρ q.1 q.2.1 q.2.2)
              + (plaqContrMinus σ μG ρ x μ ν q.1 q.2.1 q.2.2
                - plaqMean σ μG ρ x μ ν
                  * plaqMeanConj σ μG ρ q.1 q.2.1 q.2.2)) := by
  rw [kappa_eq_sum_contr σ μG ρ hρcont hd hσ x μ ν, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rfl

/-- **The derivative form of (9)**, recovered only through the
landed derivative theorem `deriv_plaquetteLoop_eq`: the
first-order response of the plaquette expectation is the negative
of the assembled contraction sum. No new sign convention is
introduced. -/
theorem deriv_plaquetteLoop_eq_contr
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (x : Λ) (μ ν : Fin 4) :
    deriv (fun β : ℝ => gibbsExpect σ μG ρ β
        (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν))) 0
      = -∑ q ∈ sharingPlaquettes σ (plaquetteLinks σ x μ ν),
          kappaContrTerm σ μG ρ x μ ν q := by
  rw [deriv_plaquetteLoop_eq σ μG ρ hρcont hd hσ x μ ν]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [covZero_plaquette_density_eq_contr σ μG ρ hρcont hd hσ x μ ν
    q.1 q.2.1 q.2.2]
  rfl

/-! ## §2. C3(a) — rotation and relabeling guards

The contraction of a slot family depends on its slots only
through the fiber products over links; reindexing the slots of
either family by a bijection therefore leaves `wordContr`
unchanged. Instantiated at plaquettes: the assembled contraction
is unchanged by rotating either word's steps (any step
permutation, in particular the cyclic rotation `rot4`), and by
simultaneous relabeling of all contracted indices. -/

/-- One-link factor under reindexing of the first family: the
factor of the reindexed family at a finset of new slots is the
factor of the original family at the image finset. -/
theorem linkContr_map_equiv_left {ιA ιA' ιB : Type*} [DecidableEq ιA]
    (e : ιA' ≃ ιA)
    (sA : Finset ιA') (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ)
    (aA bA : ιA → Fin d) (sB : Finset ιB)
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d) :
    linkContr μG sA (MA ∘ e) (aA ∘ e) (bA ∘ e) sB MB aB bB
      = linkContr μG (sA.map e.toEmbedding) MA aA bA sB MB aB bB := by
  show (∫ g, (∏ i ∈ sA, (MA ∘ e) i g ((aA ∘ e) i) ((bA ∘ e) i))
      * (∏ j ∈ sB, MB j g (aB j) (bB j)) ∂μG)
    = ∫ g, (∏ i ∈ sA.map e.toEmbedding, MA i g (aA i) (bA i))
      * (∏ j ∈ sB, MB j g (aB j) (bB j)) ∂μG
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show (∏ i ∈ sA, (MA ∘ e) i g ((aA ∘ e) i) ((bA ∘ e) i))
      * (∏ j ∈ sB, MB j g (aB j) (bB j))
    = (∏ i ∈ sA.map e.toEmbedding, MA i g (aA i) (bA i))
      * (∏ j ∈ sB, MB j g (aB j) (bB j))
  rw [Finset.prod_map]
  rfl

/-- One-link factor under reindexing of the second family. -/
theorem linkContr_map_equiv_right {ιA ιB ιB' : Type*} [DecidableEq ιB]
    (e : ιB' ≃ ιB)
    (sA : Finset ιA) (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ)
    (aA bA : ιA → Fin d) (sB : Finset ιB')
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d) :
    linkContr μG sA MA aA bA sB (MB ∘ e) (aB ∘ e) (bB ∘ e)
      = linkContr μG sA MA aA bA (sB.map e.toEmbedding) MB aB bB := by
  show (∫ g, (∏ i ∈ sA, MA i g (aA i) (bA i))
      * (∏ j ∈ sB, (MB ∘ e) j g ((aB ∘ e) j) ((bB ∘ e) j)) ∂μG)
    = ∫ g, (∏ i ∈ sA, MA i g (aA i) (bA i))
      * (∏ j ∈ sB.map e.toEmbedding, MB j g (aB j) (bB j)) ∂μG
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show (∏ i ∈ sA, MA i g (aA i) (bA i))
      * (∏ j ∈ sB, (MB ∘ e) j g ((aB ∘ e) j) ((bB ∘ e) j))
    = (∏ i ∈ sA, MA i g (aA i) (bA i))
      * (∏ j ∈ sB.map e.toEmbedding, MB j g (aB j) (bB j))
  rw [Finset.prod_map]
  rfl

/-- **Slot reindexing invariance, first family.** Reindexing the
slots of the first family by a bijection — links, matrix
functions and both index functions composed with it — leaves the
two-word contraction unchanged. -/
theorem wordContr_reindex_left {ιA ιA' ιB : Type*} [Fintype ιA] [Fintype ιA']
    [Fintype ιB] [DecidableEq ιA] (e : ιA' ≃ ιA)
    (slA : ιA → Link Λ) (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ)
    (aA bA : ιA → Fin d) (slB : ιB → Link Λ)
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d) :
    wordContr μG (slA ∘ e) (MA ∘ e) (aA ∘ e) (bA ∘ e) slB MB aB bB
      = wordContr μG slA MA aA bA slB MB aB bB := by
  show (∏ ℓ : Link Λ, linkContr μG
        (Finset.univ.filter (fun i => (slA ∘ e) i = ℓ)) (MA ∘ e) (aA ∘ e)
        (bA ∘ e) (Finset.univ.filter (fun j => slB j = ℓ)) MB aB bB)
    = ∏ ℓ : Link Λ, linkContr μG
        (Finset.univ.filter (fun i => slA i = ℓ)) MA aA bA
        (Finset.univ.filter (fun j => slB j = ℓ)) MB aB bB
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  have hfil : (Finset.univ.filter (fun i => (slA ∘ e) i = ℓ)).map e.toEmbedding
      = Finset.univ.filter (fun i => slA i = ℓ) := by
    ext j
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hj
      exact ⟨e.symm j, by simpa using hj, by simp⟩
  rw [linkContr_map_equiv_left μG e _ MA aA bA _ MB aB bB, hfil]

/-- **Slot reindexing invariance, second family.** -/
theorem wordContr_reindex_right {ιA ιB ιB' : Type*} [Fintype ιA]
    [Fintype ιB] [Fintype ιB'] [DecidableEq ιB] (e : ιB' ≃ ιB)
    (slA : ιA → Link Λ) (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ)
    (aA bA : ιA → Fin d) (slB : ιB → Link Λ)
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d) :
    wordContr μG slA MA aA bA (slB ∘ e) (MB ∘ e) (aB ∘ e) (bB ∘ e)
      = wordContr μG slA MA aA bA slB MB aB bB := by
  show (∏ ℓ : Link Λ, linkContr μG
        (Finset.univ.filter (fun i => slA i = ℓ)) MA aA bA
        (Finset.univ.filter (fun j => (slB ∘ e) j = ℓ)) (MB ∘ e) (aB ∘ e)
        (bB ∘ e))
    = ∏ ℓ : Link Λ, linkContr μG
        (Finset.univ.filter (fun i => slA i = ℓ)) MA aA bA
        (Finset.univ.filter (fun j => slB j = ℓ)) MB aB bB
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  have hfil : (Finset.univ.filter (fun j => (slB ∘ e) j = ℓ)).map e.toEmbedding
      = Finset.univ.filter (fun j => slB j = ℓ) := by
    ext j
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hj
      exact ⟨e.symm j, by simpa using hj, by simp⟩
  rw [linkContr_map_equiv_right μG e _ MA aA bA _ MB aB bB, hfil]

/-- **Rotation invariance of `Contr⁺`, first word.** For any
permutation `e` of the four steps — in particular the cyclic
rotation — the assembled direct contraction equals its expansion
along the rotated first word (rotated links, matrix functions and
trace wiring). -/
theorem plaqContrPlus_rotate_left (e : Fin 4 ≃ Fin 4) (x : Λ) (μ ν : Fin 4)
    (y : Λ) (α β : Fin 4) :
    plaqContrPlus σ μG ρ x μ ν y α β
      = ∑ i : Fin 4 → Fin d, ∑ j : Fin 4 → Fin d,
          wordContr μG (plaqSlotLink σ x μ ν ∘ e) (plaqSlotMat ρ ∘ e)
            (fun k => i (plaqRow (e k))) (fun k => i (plaqCol (e k)))
            (plaqSlotLink σ y α β) (plaqSlotMat ρ)
            (fun k => j (plaqRow k)) (fun k => j (plaqCol k)) := by
  unfold plaqContrPlus
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact (wordContr_reindex_left μG e (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
    (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
    (plaqSlotLink σ y α β) (plaqSlotMat ρ)
    (fun k => j (plaqRow k)) (fun k => j (plaqCol k))).symm

/-- **Rotation invariance of `Contr⁺`, second word.** -/
theorem plaqContrPlus_rotate_right (e : Fin 4 ≃ Fin 4) (x : Λ) (μ ν : Fin 4)
    (y : Λ) (α β : Fin 4) :
    plaqContrPlus σ μG ρ x μ ν y α β
      = ∑ i : Fin 4 → Fin d, ∑ j : Fin 4 → Fin d,
          wordContr μG (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
            (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
            (plaqSlotLink σ y α β ∘ e) (plaqSlotMat ρ ∘ e)
            (fun k => j (plaqRow (e k))) (fun k => j (plaqCol (e k))) := by
  unfold plaqContrPlus
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact (wordContr_reindex_right μG e (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
    (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
    (plaqSlotLink σ y α β) (plaqSlotMat ρ)
    (fun k => j (plaqRow k)) (fun k => j (plaqCol k))).symm

/-- **Rotation invariance of `Contr⁻`, first word.** -/
theorem plaqContrMinus_rotate_left (e : Fin 4 ≃ Fin 4) (x : Λ) (μ ν : Fin 4)
    (y : Λ) (α β : Fin 4) :
    plaqContrMinus σ μG ρ x μ ν y α β
      = ∑ i : Fin 4 → Fin d, ∑ j : Fin 4 → Fin d,
          wordContr μG (plaqSlotLink σ x μ ν ∘ e) (plaqSlotMat ρ ∘ e)
            (fun k => i (plaqRow (e k))) (fun k => i (plaqCol (e k)))
            (plaqSlotLink σ y α β) (plaqSlotMatConj ρ)
            (fun k => j (plaqRow k)) (fun k => j (plaqCol k)) := by
  unfold plaqContrMinus
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact (wordContr_reindex_left μG e (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
    (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
    (plaqSlotLink σ y α β) (plaqSlotMatConj ρ)
    (fun k => j (plaqRow k)) (fun k => j (plaqCol k))).symm

/-- **Rotation invariance of `Contr⁻`, second word.** -/
theorem plaqContrMinus_rotate_right (e : Fin 4 ≃ Fin 4) (x : Λ) (μ ν : Fin 4)
    (y : Λ) (α β : Fin 4) :
    plaqContrMinus σ μG ρ x μ ν y α β
      = ∑ i : Fin 4 → Fin d, ∑ j : Fin 4 → Fin d,
          wordContr μG (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
            (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
            (plaqSlotLink σ y α β ∘ e) (plaqSlotMatConj ρ ∘ e)
            (fun k => j (plaqRow (e k))) (fun k => j (plaqCol (e k))) := by
  unfold plaqContrMinus
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact (wordContr_reindex_right μG e (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
    (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
    (plaqSlotLink σ y α β) (plaqSlotMatConj ρ)
    (fun k => j (plaqRow k)) (fun k => j (plaqCol k))).symm

/-- The **cyclic rotation** of the four plaquette steps,
`0 ↦ 1 ↦ 2 ↦ 3 ↦ 0`. -/
def rot4 : Fin 4 ≃ Fin 4 :=
  ⟨fun k => ![1, 2, 3, 0] k, fun k => ![3, 0, 1, 2] k,
   fun k => by fin_cases k <;> decide, fun k => by fin_cases k <;> decide⟩

/-- **C3(a) headline: cyclic-rotation invariance.** The assembled
contractions are unchanged when either plaquette word is read
from the rotated step list — the trace word is cyclic, at the
level of the final contraction. -/
theorem plaqContrPlus_rotation (x : Λ) (μ ν : Fin 4) (y : Λ) (α β : Fin 4) :
    plaqContrPlus σ μG ρ x μ ν y α β
      = ∑ i : Fin 4 → Fin d, ∑ j : Fin 4 → Fin d,
          wordContr μG (plaqSlotLink σ x μ ν ∘ rot4) (plaqSlotMat ρ ∘ rot4)
            (fun k => i (plaqRow (rot4 k))) (fun k => i (plaqCol (rot4 k)))
            (plaqSlotLink σ y α β) (plaqSlotMat ρ)
            (fun k => j (plaqRow k)) (fun k => j (plaqCol k)) :=
  plaqContrPlus_rotate_left σ μG ρ rot4 x μ ν y α β

/-- **Reindexing a contraction sum by post-composition.** The
double index-assignment sum of a two-word contraction is
unchanged when both assignments are post-composed with a fixed
permutation `π` of the matrix indices: post-composition is a
bijection of the assignment type, applied once per sum. -/
theorem sum_wordContr_comp {M N : Fin 4 → (G → Matrix (Fin d) (Fin d) ℂ)}
    (slA slB : Fin 4 → Link Λ) (π : Fin d ≃ Fin d) :
    (∑ i : Fin 4 → Fin d, ∑ j : Fin 4 → Fin d,
        wordContr μG slA M (fun k => (π ∘ i) (plaqRow k))
          (fun k => (π ∘ i) (plaqCol k))
          slB N (fun k => (π ∘ j) (plaqRow k)) (fun k => (π ∘ j) (plaqCol k)))
      = ∑ i : Fin 4 → Fin d, ∑ j : Fin 4 → Fin d,
          wordContr μG slA M (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
            slB N (fun k => j (plaqRow k)) (fun k => j (plaqCol k)) := by
  let e : (Fin 4 → Fin d) ≃ (Fin 4 → Fin d) :=
    ⟨fun a => π ∘ a, fun a => π.symm ∘ a,
     fun a => by funext k; simp, fun a => by funext k; simp⟩
  have hsum : ∀ Φ : (Fin 4 → Fin d) → ℂ, (∑ i, Φ (e i)) = ∑ i, Φ i :=
    fun Φ => Equiv.sum_comp e Φ
  calc (∑ i : Fin 4 → Fin d, ∑ j : Fin 4 → Fin d,
        wordContr μG slA M (fun k => (π ∘ i) (plaqRow k))
          (fun k => (π ∘ i) (plaqCol k))
          slB N (fun k => (π ∘ j) (plaqRow k)) (fun k => (π ∘ j) (plaqCol k)))
      = ∑ i : Fin 4 → Fin d, ∑ j : Fin 4 → Fin d,
          wordContr μG slA M (fun k => (π ∘ i) (plaqRow k))
            (fun k => (π ∘ i) (plaqCol k))
            slB N (fun k => j (plaqRow k)) (fun k => j (plaqCol k)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact hsum (fun j => wordContr μG slA M (fun k => (π ∘ i) (plaqRow k))
          (fun k => (π ∘ i) (plaqCol k)) slB N (fun k => j (plaqRow k))
          (fun k => j (plaqCol k)))
    _ = ∑ i : Fin 4 → Fin d, ∑ j : Fin 4 → Fin d,
          wordContr μG slA M (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
            slB N (fun k => j (plaqRow k)) (fun k => j (plaqCol k)) :=
        hsum (fun i => ∑ j : Fin 4 → Fin d,
          wordContr μG slA M (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
            slB N (fun k => j (plaqRow k)) (fun k => j (plaqCol k)))

/-- **Index-relabeling invariance of `Contr⁺`.** Simultaneously
relabeling every contracted index of both words by a permutation
`π` of `Fin d` leaves the assembled contraction unchanged: the
assembly sums over all index assignments, and relabeling is a
reindexing of that sum. -/
theorem plaqContrPlus_relabel (π : Fin d ≃ Fin d) (x : Λ) (μ ν : Fin 4)
    (y : Λ) (α β : Fin 4) :
    plaqContrPlus σ μG ρ x μ ν y α β
      = ∑ i : Fin 4 → Fin d, ∑ j : Fin 4 → Fin d,
          wordContr μG (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
            (fun k => π (i (plaqRow k))) (fun k => π (i (plaqCol k)))
            (plaqSlotLink σ y α β) (plaqSlotMat ρ)
            (fun k => π (j (plaqRow k))) (fun k => π (j (plaqCol k))) := by
  unfold plaqContrPlus
  refine (sum_wordContr_comp μG (plaqSlotLink σ x μ ν)
    (plaqSlotLink σ y α β) π).symm.trans ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rfl

/-- **Index-relabeling invariance of `Contr⁻`.** -/
theorem plaqContrMinus_relabel (π : Fin d ≃ Fin d) (x : Λ) (μ ν : Fin 4)
    (y : Λ) (α β : Fin 4) :
    plaqContrMinus σ μG ρ x μ ν y α β
      = ∑ i : Fin 4 → Fin d, ∑ j : Fin 4 → Fin d,
          wordContr μG (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
            (fun k => π (i (plaqRow k))) (fun k => π (i (plaqCol k)))
            (plaqSlotLink σ y α β) (plaqSlotMatConj ρ)
            (fun k => π (j (plaqRow k))) (fun k => π (j (plaqCol k))) := by
  unfold plaqContrMinus
  refine (sum_wordContr_comp μG (plaqSlotLink σ x μ ν)
    (plaqSlotLink σ y α β) π).symm.trans ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rfl

/-! ## §3. C3(b) — the trivial-representation guard

At the entries-one seat — every entry of `repMatrix ρ` equal to
`1`, the pattern of the trivial one-dimensional representation
(there `W_p = 1` and `D_q = 0`) — every slot entry of both words
is `1`, every fiber integral is `1`, every contraction and mean
is `1`, the centered brackets cancel, and κ_p vanishes. This
catches a missing covariance subtraction or an incorrect `2d`
denominator in the assembly. -/

/-- At the entries-one seat, a constant-`1` integrand integrates
to `1` (the measure is a probability measure). -/
theorem integral_eq_one_of_forall_eq_one {f : G → ℂ} (hf : ∀ g, f g = 1) :
    ∫ g, f g ∂μG = 1 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall hf)]
  simp

/-- Slot entries at the entries-one seat, direct word: forward
steps by hypothesis; dual steps because a dual entry is an entry
of `ρ g⁻¹` with transposed indices. -/
theorem plaqSlotMat_apply_eq_one_of_entries_one
    (hent : ∀ (g : G) (a b : Fin d), repMatrix ρ g a b = 1)
    (k : Fin 4) (g : G) (a b : Fin d) :
    plaqSlotMat ρ k g a b = 1 := by
  fin_cases k <;>
    simp only [plaqSlotMat, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      repMatDual, orientDual_apply]
  · exact hent g a b
  · exact hent g a b
  · exact hent g⁻¹ b a
  · exact hent g⁻¹ b a

/-- Slot entries at the entries-one seat, conjugate word:
the conjugate word's step matrices are the conjugates of the
direct word's (Q13-3's `plaqSlotMatConj_eq`), and `star 1 = 1`. -/
theorem plaqSlotMatConj_apply_eq_one_of_entries_one
    (hent : ∀ (g : G) (a b : Fin d), repMatrix ρ g a b = 1)
    (k : Fin 4) (g : G) (a b : Fin d) :
    plaqSlotMatConj ρ k g a b = 1 := by
  rw [plaqSlotMatConj_eq, orientConj_apply,
    plaqSlotMat_apply_eq_one_of_entries_one ρ hent k g a b]
  simp

/-- One-link factor at the entries-one seat: the integrand is
the constant `1`. -/
theorem linkContr_eq_one_of_entries_one {ιA ιB : Type*}
    (sA : Finset ιA) (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ)
    (aA bA : ιA → Fin d) (sB : Finset ιB)
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d)
    (hA : ∀ (i : ιA) (g : G), MA i g (aA i) (bA i) = 1)
    (hB : ∀ (j : ιB) (g : G), MB j g (aB j) (bB j) = 1) :
    linkContr μG sA MA aA bA sB MB aB bB = 1 := by
  show (∫ g, (∏ i ∈ sA, MA i g (aA i) (bA i))
    * (∏ j ∈ sB, MB j g (aB j) (bB j)) ∂μG) = 1
  refine integral_eq_one_of_forall_eq_one μG fun g => ?_
  rw [Finset.prod_eq_one (fun i _ => hA i g),
    Finset.prod_eq_one (fun j _ => hB j g), mul_one]

/-- Two-word contraction at the entries-one seat: every link
factor is `1`. -/
theorem wordContr_eq_one_of_entries_one {ιA ιB : Type*} [Fintype ιA]
    [Fintype ιB]
    (slA : ιA → Link Λ) (MA : ιA → G → Matrix (Fin d) (Fin d) ℂ)
    (aA bA : ιA → Fin d) (slB : ιB → Link Λ)
    (MB : ιB → G → Matrix (Fin d) (Fin d) ℂ) (aB bB : ιB → Fin d)
    (hA : ∀ (i : ιA) (g : G), MA i g (aA i) (bA i) = 1)
    (hB : ∀ (j : ιB) (g : G), MB j g (aB j) (bB j) = 1) :
    wordContr μG slA MA aA bA slB MB aB bB = 1 := by
  show (∏ ℓ : Link Λ, linkContr μG
    (Finset.univ.filter (fun i => slA i = ℓ)) MA aA bA
    (Finset.univ.filter (fun j => slB j = ℓ)) MB aB bB) = 1
  exact Finset.prod_eq_one fun ℓ _ =>
    linkContr_eq_one_of_entries_one μG _ MA aA bA _ MB aB bB hA hB

/-- One-word contraction at the entries-one seat. -/
theorem wordMean_eq_one_of_entries_one {ι : Type*} [Fintype ι]
    (sl : ι → Link Λ) (M : ι → G → Matrix (Fin d) (Fin d) ℂ)
    (a b : ι → Fin d)
    (h : ∀ (i : ι) (g : G), M i g (a i) (b i) = 1) :
    wordMean μG sl M a b = 1 := by
  show (∏ ℓ : Link Λ, ∫ g, ∏ i ∈ Finset.univ.filter (fun i => sl i = ℓ),
    M i g (a i) (b i) ∂μG) = 1
  refine Finset.prod_eq_one fun ℓ _ => ?_
  refine integral_eq_one_of_forall_eq_one μG fun g => ?_
  exact Finset.prod_eq_one fun i _ => h i g

/-- **C3(b), per-plaquette form.** At the entries-one seat the
contraction equals the product of the means in both signs
(`Contr^±_{p,q} = 𝔼₀[W_p] 𝔼₀[W_q^±]`, both sides being the same
count of `1`s), so the centered brackets of the headline vanish
and `Cov₀(W_p, D_q) = 0`. -/
theorem covZero_plaquette_density_eq_zero_of_entries_one
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (hent : ∀ (g : G) (a b : Fin d), repMatrix ρ g a b = 1)
    (x : Λ) (μ ν : Fin 4) (y : Λ) (α β : Fin 4) :
    covZero σ μG ρ (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν))
        (fun U => (plaquetteDensity σ ρ U y α β : ℂ)) = 0 := by
  have hplus : plaqContrPlus σ μG ρ x μ ν y α β
      = plaqMean σ μG ρ x μ ν * plaqMean σ μG ρ y α β := by
    unfold plaqContrPlus plaqMean
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h1 : wordContr μG (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
        (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
        (plaqSlotLink σ y α β) (plaqSlotMat ρ)
        (fun k => j (plaqRow k)) (fun k => j (plaqCol k)) = 1 :=
      wordContr_eq_one_of_entries_one μG _ _ _ _ _ _ _ _
        (fun k g => plaqSlotMat_apply_eq_one_of_entries_one ρ hent k g _ _)
        (fun k g => plaqSlotMat_apply_eq_one_of_entries_one ρ hent k g _ _)
    have h2 : wordMean μG (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
        (fun k => i (plaqRow k)) (fun k => i (plaqCol k)) = 1 :=
      wordMean_eq_one_of_entries_one μG _ _ _ _
        (fun k g => plaqSlotMat_apply_eq_one_of_entries_one ρ hent k g _ _)
    have h3 : wordMean μG (plaqSlotLink σ y α β) (plaqSlotMat ρ)
        (fun k => j (plaqRow k)) (fun k => j (plaqCol k)) = 1 :=
      wordMean_eq_one_of_entries_one μG _ _ _ _
        (fun k g => plaqSlotMat_apply_eq_one_of_entries_one ρ hent k g _ _)
    rw [h1, h2, h3, mul_one]
  have hminus : plaqContrMinus σ μG ρ x μ ν y α β
      = plaqMean σ μG ρ x μ ν * plaqMeanConj σ μG ρ y α β := by
    unfold plaqContrMinus plaqMean plaqMeanConj
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h1 : wordContr μG (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
        (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
        (plaqSlotLink σ y α β) (plaqSlotMatConj ρ)
        (fun k => j (plaqRow k)) (fun k => j (plaqCol k)) = 1 :=
      wordContr_eq_one_of_entries_one μG _ _ _ _ _ _ _ _
        (fun k g => plaqSlotMat_apply_eq_one_of_entries_one ρ hent k g _ _)
        (fun k g => plaqSlotMatConj_apply_eq_one_of_entries_one ρ hent k g _ _)
    have h2 : wordMean μG (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
        (fun k => i (plaqRow k)) (fun k => i (plaqCol k)) = 1 :=
      wordMean_eq_one_of_entries_one μG _ _ _ _
        (fun k g => plaqSlotMat_apply_eq_one_of_entries_one ρ hent k g _ _)
    have h3 : wordMean μG (plaqSlotLink σ y α β) (plaqSlotMatConj ρ)
        (fun k => j (plaqRow k)) (fun k => j (plaqCol k)) = 1 :=
      wordMean_eq_one_of_entries_one μG _ _ _ _
        (fun k g => plaqSlotMatConj_apply_eq_one_of_entries_one ρ hent k g _ _)
    rw [h1, h2, h3, mul_one]
  rw [covZero_plaquette_density_eq_contr σ μG ρ hρcont hd hσ x μ ν y α β,
    hplus, hminus]
  simp

/-- **C3(b) headline.** At the entries-one seat — the trivial
one-dimensional representation's pattern — the assembled
κ_p vanishes: every per-plaquette bracket of (9) is zero, hence
so is the sum, i.e. `κ_p` itself by C2. -/
theorem kappa_eq_zero_of_entries_one
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (hent : ∀ (g : G) (a b : Fin d), repMatrix ρ g a b = 1)
    (x : Λ) (μ ν : Fin 4) :
    covZero σ μG ρ (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν))
        (fun U => (actionDensity σ ρ U : ℂ)) = 0 := by
  rw [covZero_plaquetteLoop_eq_sum σ μG ρ hρcont hd hσ x μ ν]
  exact Finset.sum_eq_zero fun q _ =>
    covZero_plaquette_density_eq_zero_of_entries_one σ μG ρ hρcont hd hσ
      hent x μ ν q.1 q.2.1 q.2.2

/-- **Q13-2's entries-one seat, consumed at the plaquette slot
families (direct second word).** If every entry of the second
word is `1`, its slot product is the constant observable `1` and
the centered slot contraction vanishes — the linkwise form of
the guard, applied to the two plaquette words at any index
assignments. -/
theorem covZero_plaquette_slots_eq_zero_of_entries_one
    (hent : ∀ (g : G) (a b : Fin d), repMatrix ρ g a b = 1)
    (x : Λ) (μ ν : Fin 4) (y : Λ) (α β : Fin 4) (i j : Fin 4 → Fin d) :
    covZero σ μG ρ
        (fun U => ∏ k, linkEntry (plaqSlotMat ρ k) (plaqSlotLink σ x μ ν k)
          (i (plaqRow k)) (i (plaqCol k)) U)
        (fun U => ∏ k, linkEntry (plaqSlotMat ρ k) (plaqSlotLink σ y α β k)
          (j (plaqRow k)) (j (plaqCol k)) U) = 0 :=
  covZero_prod_linkEntry_eq_zero_of_entries_one σ μG ρ
    (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
    (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
    (plaqSlotLink σ y α β) (plaqSlotMat ρ)
    (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
    (fun k g => plaqSlotMat_apply_eq_one_of_entries_one ρ hent k g _ _)

/-- **Q13-2's entries-one seat, consumed at the plaquette slot
families (conjugate second word).** -/
theorem covZero_plaquette_slots_conj_eq_zero_of_entries_one
    (hent : ∀ (g : G) (a b : Fin d), repMatrix ρ g a b = 1)
    (x : Λ) (μ ν : Fin 4) (y : Λ) (α β : Fin 4) (i j : Fin 4 → Fin d) :
    covZero σ μG ρ
        (fun U => ∏ k, linkEntry (plaqSlotMat ρ k) (plaqSlotLink σ x μ ν k)
          (i (plaqRow k)) (i (plaqCol k)) U)
        (fun U => ∏ k, linkEntry (plaqSlotMatConj ρ k)
          (plaqSlotLink σ y α β k) (j (plaqRow k)) (j (plaqCol k)) U) = 0 :=
  covZero_prod_linkEntry_eq_zero_of_entries_one σ μG ρ
    (plaqSlotLink σ x μ ν) (plaqSlotMat ρ)
    (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
    (plaqSlotLink σ y α β) (plaqSlotMatConj ρ)
    (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
    (fun k g => plaqSlotMatConj_apply_eq_one_of_entries_one ρ hent k g _ _)

/-! ## §4. C1 — the circle/fundamental specialization

At `G = Circle`, `ρ = circleRep` (so `d = 1`), `Λ = Fin 4 → ZMod N`,
`σ = torusShift N`, `μG = haarProb Circle`, `N ≥ 2`, `μ < ν`: the
J data collapses onto the landed per-link character factors. No
shift fixes a site at this seat (`torusShift_ne_self`), so every
plaquette fiber has cardinality `≤ 1` per word and the doubled-link
PARTIAL class of Q13-3 does not arise; at `d = 1` the remaining
fiber integrals are the scalar character integrals of Stage 1c-0. -/

section Circle

variable {N : ℕ} [NeZero N]

/-- A plaquette character factor is always the coercion of a
circle element: `(z : ℂ)`, `((z : ℂ))⁻¹` or `1` according to the
link. -/
theorem phiFactor_eq_coe (x : Fin 4 → ZMod N) (μ ν : Fin 4)
    (ℓ : Link (Fin 4 → ZMod N)) (z : Circle) :
    ∃ w : Circle, phiFactor (torusShift N) x μ ν ℓ z = (w : ℂ) := by
  unfold phiFactor
  by_cases h1 : ℓ = (x, μ)
  · exact ⟨z, by rw [if_pos h1]⟩
  by_cases h2 : ℓ = ((torusShift N μ) x, ν)
  · exact ⟨z, by rw [if_neg h1, if_pos h2]⟩
  by_cases h3 : ℓ = ((torusShift N ν) x, μ)
  · refine ⟨z⁻¹, ?_⟩
    rw [if_neg h1, if_neg h2, if_pos h3, Circle.coe_inv]
  by_cases h4 : ℓ = (x, ν)
  · refine ⟨z⁻¹, ?_⟩
    rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4, Circle.coe_inv]
  · exact ⟨1, by rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4,
      Circle.coe_one]⟩

/-- The four slot links of a plaquette word at the torus seat. -/
theorem plaqSlotLink_circle (x : Fin 4 → ZMod N) (μ ν : Fin 4) :
    plaqSlotLink (torusShift N) x μ ν 0 = (x, μ)
      ∧ plaqSlotLink (torusShift N) x μ ν 1 = ((torusShift N μ) x, ν)
      ∧ plaqSlotLink (torusShift N) x μ ν 2 = ((torusShift N ν) x, μ)
      ∧ plaqSlotLink (torusShift N) x μ ν 3 = (x, ν) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [plaqSlotLink]

/-- Every slot of a plaquette word reads one of its four links. -/
theorem plaqSlotLink_circle_cases (x : Fin 4 → ZMod N) (μ ν : Fin 4)
    (k : Fin 4) :
    plaqSlotLink (torusShift N) x μ ν k = (x, μ)
      ∨ plaqSlotLink (torusShift N) x μ ν k = ((torusShift N μ) x, ν)
      ∨ plaqSlotLink (torusShift N) x μ ν k = ((torusShift N ν) x, μ)
      ∨ plaqSlotLink (torusShift N) x μ ν k = (x, ν) := by
  fin_cases k
  · exact Or.inl (by simp [plaqSlotLink])
  · exact Or.inr (Or.inl (by simp [plaqSlotLink]))
  · exact Or.inr (Or.inr (Or.inl (by simp [plaqSlotLink])))
  · exact Or.inr (Or.inr (Or.inr (by simp [plaqSlotLink])))

/-- At the torus seat a plaquette word's fiber over any of its
own links is a singleton: no shift fixes the base site, so the
fiber cardinality is `≤ 1` (Q13-3's fence), and the slot itself
witnesses membership. The doubled-link class is empty here. -/
theorem fiber_circle_eq_singleton (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ < ν) (k₀ : Fin 4) :
    Finset.univ.filter (fun k => plaqSlotLink (torusShift N) x μ ν k
        = plaqSlotLink (torusShift N) x μ ν k₀) = {k₀} := by
  have hmem : k₀ ∈ Finset.univ.filter
      (fun k => plaqSlotLink (torusShift N) x μ ν k
        = plaqSlotLink (torusShift N) x μ ν k₀) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hcard : (Finset.univ.filter
      (fun k => plaqSlotLink (torusShift N) x μ ν k
        = plaqSlotLink (torusShift N) x μ ν k₀)).card ≤ 1 :=
    plaqSlotLink_fiber_card_le_one (torusShift N) x μ ν hμν
      (torusShift_ne_self N hN ν x) (torusShift_ne_self N hN μ x) _
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp
    (le_antisymm hcard (Finset.card_pos.mpr ⟨k₀, hmem⟩))
  have hak : k₀ = a := by
    have hmem' := hmem
    rw [ha] at hmem'
    exact Finset.mem_singleton.mp hmem'
  rw [ha, hak]

/-- Slot entries of the circle word: forward steps read the
character, dual steps its inverse. -/
theorem plaqSlotMat_circle_entry (z : Circle) (k : Fin 4) (a b : Fin 1) :
    plaqSlotMat circleRep k z a b
      = if k = 0 ∨ k = 1 then (z : ℂ) else ((z : ℂ))⁻¹ := by
  fin_cases k
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, ↓reduceIte]
    show repMatrix circleRep z a b = (z : ℂ)
    rw [show repMatrix circleRep z = Matrix.of (fun _ _ => (z : ℂ)) from rfl]
    rfl
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, ↓reduceIte]
    show repMatrix circleRep z a b = (z : ℂ)
    rw [show repMatrix circleRep z = Matrix.of (fun _ _ => (z : ℂ)) from rfl]
    rfl
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, ↓reduceIte]
    show repMatDual circleRep z a b = ((z : ℂ))⁻¹
    rw [show repMatDual circleRep = orientDual (repMatrix circleRep) from rfl,
      orientDual_apply,
      show repMatrix circleRep z⁻¹
        = Matrix.of (fun _ _ => ((z⁻¹ : Circle) : ℂ)) from rfl]
    exact Circle.coe_inv z
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, ↓reduceIte]
    show repMatDual circleRep z a b = ((z : ℂ))⁻¹
    rw [show repMatDual circleRep = orientDual (repMatrix circleRep) from rfl,
      orientDual_apply,
      show repMatrix circleRep z⁻¹
        = Matrix.of (fun _ _ => ((z⁻¹ : Circle) : ℂ)) from rfl]
    exact Circle.coe_inv z

/-- **The bridge at `d = 1`.** The fiber product of a plaquette
word's slot entries over one link is the landed per-link
character factor `phiFactor` of that link. This is where the
Q13 slot wiring (dual steps = transposed inverse entries) meets
the Stage 1c-0 circle computation: a transpose or orientation
error in the wiring would surface here as the wrong character. -/
theorem fiberProd_circle (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ < ν) (ℓ : Link (Fin 4 → ZMod N)) (z : Circle)
    (i : Fin 4 → Fin 1) :
    (∏ k ∈ Finset.univ.filter (fun k => plaqSlotLink (torusShift N) x μ ν k = ℓ),
      plaqSlotMat circleRep k z (i (plaqRow k)) (i (plaqCol k)))
      = phiFactor (torusShift N) x μ ν ℓ z := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ :=
    plaquette_four_links_distinct hN x (ne_of_lt hμν)
  obtain ⟨hplaq0, hplaq1, hplaq2, hplaq3⟩ := plaqSlotLink_circle x μ ν
  by_cases h0 : ℓ = (x, μ)
  · have hfil : Finset.univ.filter
        (fun k => plaqSlotLink (torusShift N) x μ ν k = ℓ) = {0} := by
      rw [h0, ← hplaq0]
      exact fiber_circle_eq_singleton hN x hμν 0
    rw [hfil, Finset.prod_singleton, h0, phiFactor_fst]
    have h := plaqSlotMat_circle_entry z 0 (i (plaqRow 0)) (i (plaqCol 0))
    rw [if_pos (Or.inl rfl)] at h
    exact h
  by_cases h1 : ℓ = ((torusShift N μ) x, ν)
  · have hfil : Finset.univ.filter
        (fun k => plaqSlotLink (torusShift N) x μ ν k = ℓ) = {1} := by
      rw [h1, ← hplaq1]
      exact fiber_circle_eq_singleton hN x hμν 1
    rw [hfil, Finset.prod_singleton, h1,
      phiFactor_snd (torusShift N) x μ ν z (Ne.symm d1)]
    have h := plaqSlotMat_circle_entry z 1 (i (plaqRow 1)) (i (plaqCol 1))
    rw [if_pos (Or.inr rfl)] at h
    exact h
  by_cases h2 : ℓ = ((torusShift N ν) x, μ)
  · have hfil : Finset.univ.filter
        (fun k => plaqSlotLink (torusShift N) x μ ν k = ℓ) = {2} := by
      rw [h2, ← hplaq2]
      exact fiber_circle_eq_singleton hN x hμν 2
    rw [hfil, Finset.prod_singleton, h2,
      phiFactor_thd (torusShift N) x μ ν z (Ne.symm d2) (Ne.symm d4)]
    have h := plaqSlotMat_circle_entry z 2 (i (plaqRow 2)) (i (plaqCol 2))
    rw [if_neg (by decide)] at h
    exact h
  by_cases h3 : ℓ = (x, ν)
  · have hfil : Finset.univ.filter
        (fun k => plaqSlotLink (torusShift N) x μ ν k = ℓ) = {3} := by
      rw [h3, ← hplaq3]
      exact fiber_circle_eq_singleton hN x hμν 3
    rw [hfil, Finset.prod_singleton, h3,
      phiFactor_fth (torusShift N) x μ ν z
        (fun h => (ne_of_lt hμν) (Prod.ext_iff.mp h).2.symm) (Ne.symm d5)
        (Ne.symm d6)]
    have h := plaqSlotMat_circle_entry z 3 (i (plaqRow 3)) (i (plaqCol 3))
    rw [if_neg (by decide)] at h
    exact h
  · have hfil : Finset.univ.filter
        (fun k => plaqSlotLink (torusShift N) x μ ν k = ℓ) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      rw [Finset.mem_filter] at hk
      rcases plaqSlotLink_circle_cases x μ ν k with h | h | h | h
      · rw [h] at hk
        exact h0 hk.2.symm
      · rw [h] at hk
        exact h1 hk.2.symm
      · rw [h] at hk
        exact h2 hk.2.symm
      · rw [h] at hk
        exact h3 hk.2.symm
    rw [hfil, Finset.prod_empty]
    unfold phiFactor
    rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3]

/-- **The bridge at `d = 1`, conjugate word.** The fiber product
of the conjugate word's slot entries is the conjugate character
factor: the conjugate slot matrices are the conjugates of the
direct ones step by step (Q13-3's `plaqSlotMatConj_eq`). -/
theorem fiberProdConj_circle (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ < ν) (ℓ : Link (Fin 4 → ZMod N)) (z : Circle)
    (j : Fin 4 → Fin 1) :
    (∏ k ∈ Finset.univ.filter (fun k => plaqSlotLink (torusShift N) x μ ν k = ℓ),
      plaqSlotMatConj circleRep k z (j (plaqRow k)) (j (plaqCol k)))
      = starRingEnd ℂ (phiFactor (torusShift N) x μ ν ℓ z) := by
  rw [← fiberProd_circle hN x hμν ℓ z j, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [plaqSlotMatConj_eq, orientConj_apply, starRingEnd_apply]

/-- **The means vanish at the circle seat.** The one-word
contraction of a plaquette word is a product of character
integrals; the `(x, μ)` factor is `∫ (z : ℂ) = 0` (the
one-factor twirl of the fundamental representation vanishes).
In J language: `plaqMean` collapses through
`circleRep_haarTwirl1_eq_zero`'s content. -/
theorem plaqMean_circle_eq_zero (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ < ν) :
    plaqMean (torusShift N) (haarProb Circle) circleRep x μ ν = 0 := by
  unfold plaqMean
  refine Finset.sum_eq_zero fun i _ => ?_
  show (∏ ℓ : Link (Fin 4 → ZMod N), ∫ g, ∏ k ∈ Finset.univ.filter
      (fun k => plaqSlotLink (torusShift N) x μ ν k = ℓ),
      plaqSlotMat circleRep k g (i (plaqRow k)) (i (plaqCol k))
      ∂(haarProb Circle)) = 0
  refine Finset.prod_eq_zero (Finset.mem_univ (x, μ)) ?_
  rw [integral_congr_ae (Filter.Eventually.of_forall fun g =>
    fiberProd_circle hN x hμν (x, μ) g i),
    integral_congr_ae (Filter.Eventually.of_forall fun g =>
    phiFactor_fst (torusShift N) x μ ν g)]
  exact integral_circle_coe

/-- **The conjugate mean vanishes at the circle seat.** -/
theorem plaqMeanConj_circle_eq_zero (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ < ν) :
    plaqMeanConj (torusShift N) (haarProb Circle) circleRep x μ ν = 0 := by
  unfold plaqMeanConj
  refine Finset.sum_eq_zero fun i _ => ?_
  show (∏ ℓ : Link (Fin 4 → ZMod N), ∫ g, ∏ k ∈ Finset.univ.filter
      (fun k => plaqSlotLink (torusShift N) x μ ν k = ℓ),
      plaqSlotMatConj circleRep k g (i (plaqRow k)) (i (plaqCol k))
      ∂(haarProb Circle)) = 0
  refine Finset.prod_eq_zero (Finset.mem_univ (x, μ)) ?_
  rw [integral_congr_ae (Filter.Eventually.of_forall fun g =>
    fiberProdConj_circle hN x hμν (x, μ) g i),
    integral_congr_ae (Filter.Eventually.of_forall fun g =>
      congrArg (starRingEnd ℂ) (phiFactor_fst (torusShift N) x μ ν g)),
    integral_congr_ae (Filter.Eventually.of_forall fun g =>
      conj_circle_coe g)]
  exact integral_circle_coe_inv

/-- **The two-word contraction at the circle seat, direct
sign**: a product over links of the one-link character moments
`∫ phiFactor_p · phiFactor_q` — the J data at `d = 1`, for every
index assignment (the value does not depend on the assignments,
all indices being in `Fin 1`). -/
theorem wordContr_circle_plus (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ < ν) (y : Fin 4 → ZMod N)
    {α β : Fin 4} (hαβ : α < β) (i j : Fin 4 → Fin 1) :
    wordContr (haarProb Circle) (plaqSlotLink (torusShift N) x μ ν)
        (plaqSlotMat circleRep)
        (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
        (plaqSlotLink (torusShift N) y α β) (plaqSlotMat circleRep)
        (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
      = ∏ ℓ : Link (Fin 4 → ZMod N), ∫ z : Circle,
          phiFactor (torusShift N) x μ ν ℓ z
            * phiFactor (torusShift N) y α β ℓ z
          ∂(haarProb Circle) := by
  show (∏ ℓ : Link (Fin 4 → ZMod N), linkContr (haarProb Circle)
      (Finset.univ.filter (fun k => plaqSlotLink (torusShift N) x μ ν k = ℓ))
      (plaqSlotMat circleRep) (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
      (Finset.univ.filter (fun k => plaqSlotLink (torusShift N) y α β k = ℓ))
      (plaqSlotMat circleRep) (fun k => j (plaqRow k))
      (fun k => j (plaqCol k))) = _
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  show (∫ g, (∏ k ∈ Finset.univ.filter
        (fun k => plaqSlotLink (torusShift N) x μ ν k = ℓ),
        plaqSlotMat circleRep k g (i (plaqRow k)) (i (plaqCol k)))
      * (∏ k ∈ Finset.univ.filter
        (fun k => plaqSlotLink (torusShift N) y α β k = ℓ),
        plaqSlotMat circleRep k g (j (plaqRow k)) (j (plaqCol k)))
      ∂(haarProb Circle)) = _
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show (∏ k ∈ Finset.univ.filter (fun k => plaqSlotLink (torusShift N) x μ ν k = ℓ),
        plaqSlotMat circleRep k g (i (plaqRow k)) (i (plaqCol k)))
      * (∏ k ∈ Finset.univ.filter
        (fun k => plaqSlotLink (torusShift N) y α β k = ℓ),
        plaqSlotMat circleRep k g (j (plaqRow k)) (j (plaqCol k)))
    = phiFactor (torusShift N) x μ ν ℓ g
      * phiFactor (torusShift N) y α β ℓ g
  rw [fiberProd_circle hN x hμν ℓ g i, fiberProd_circle hN y hαβ ℓ g j]

/-- **The two-word contraction at the circle seat, conjugate
sign**: a product over links of `∫ phiFactor_p · conj phiFactor_q`. -/
theorem wordContr_circle_minus (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ < ν) (y : Fin 4 → ZMod N)
    {α β : Fin 4} (hαβ : α < β) (i j : Fin 4 → Fin 1) :
    wordContr (haarProb Circle) (plaqSlotLink (torusShift N) x μ ν)
        (plaqSlotMat circleRep)
        (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
        (plaqSlotLink (torusShift N) y α β) (plaqSlotMatConj circleRep)
        (fun k => j (plaqRow k)) (fun k => j (plaqCol k))
      = ∏ ℓ : Link (Fin 4 → ZMod N), ∫ z : Circle,
          phiFactor (torusShift N) x μ ν ℓ z
            * starRingEnd ℂ (phiFactor (torusShift N) y α β ℓ z)
          ∂(haarProb Circle) := by
  show (∏ ℓ : Link (Fin 4 → ZMod N), linkContr (haarProb Circle)
      (Finset.univ.filter (fun k => plaqSlotLink (torusShift N) x μ ν k = ℓ))
      (plaqSlotMat circleRep) (fun k => i (plaqRow k)) (fun k => i (plaqCol k))
      (Finset.univ.filter (fun k => plaqSlotLink (torusShift N) y α β k = ℓ))
      (plaqSlotMatConj circleRep) (fun k => j (plaqRow k))
      (fun k => j (plaqCol k))) = _
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  show (∫ g, (∏ k ∈ Finset.univ.filter
        (fun k => plaqSlotLink (torusShift N) x μ ν k = ℓ),
        plaqSlotMat circleRep k g (i (plaqRow k)) (i (plaqCol k)))
      * (∏ k ∈ Finset.univ.filter
        (fun k => plaqSlotLink (torusShift N) y α β k = ℓ),
        plaqSlotMatConj circleRep k g (j (plaqRow k)) (j (plaqCol k)))
      ∂(haarProb Circle)) = _
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show (∏ k ∈ Finset.univ.filter (fun k => plaqSlotLink (torusShift N) x μ ν k = ℓ),
        plaqSlotMat circleRep k g (i (plaqRow k)) (i (plaqCol k)))
      * (∏ k ∈ Finset.univ.filter
        (fun k => plaqSlotLink (torusShift N) y α β k = ℓ),
        plaqSlotMatConj circleRep k g (j (plaqRow k)) (j (plaqCol k)))
    = phiFactor (torusShift N) x μ ν ℓ g
      * starRingEnd ℂ (phiFactor (torusShift N) y α β ℓ g)
  rw [fiberProd_circle hN x hμν ℓ g i, fiberProdConj_circle hN y hαβ ℓ g j]

/-- `Contr⁺` at the circle seat, as the product of one-link
character moments (the index sums collapse: `Fin 4 → Fin 1` has
one element). -/
theorem plaqContrPlus_circle_eq_prod (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ < ν) (y : Fin 4 → ZMod N)
    {α β : Fin 4} (hαβ : α < β) :
    plaqContrPlus (torusShift N) (haarProb Circle) circleRep x μ ν y α β
      = ∏ ℓ : Link (Fin 4 → ZMod N), ∫ z : Circle,
          phiFactor (torusShift N) x μ ν ℓ z
            * phiFactor (torusShift N) y α β ℓ z
          ∂(haarProb Circle) := by
  unfold plaqContrPlus
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    wordContr_circle_plus hN x hμν y hαβ i j).trans ?_
  simp [Finset.sum_const, Fintype.card_fun]

/-- `Contr⁻` at the circle seat, as the product of one-link
character moments. -/
theorem plaqContrMinus_circle_eq_prod (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ < ν) (y : Fin 4 → ZMod N)
    {α β : Fin 4} (hαβ : α < β) :
    plaqContrMinus (torusShift N) (haarProb Circle) circleRep x μ ν y α β
      = ∏ ℓ : Link (Fin 4 → ZMod N), ∫ z : Circle,
          phiFactor (torusShift N) x μ ν ℓ z
            * starRingEnd ℂ (phiFactor (torusShift N) y α β ℓ z)
          ∂(haarProb Circle) := by
  unfold plaqContrMinus
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    wordContr_circle_minus hN x hμν y hαβ i j).trans ?_
  simp [Finset.sum_const, Fintype.card_fun]

/-- **`Contr⁺` vanishes at the circle seat, for every `q`** (the
charge-two contraction: `𝔼₀[W_p W_q] = 0`, recovered from the
product of one-link moments via the landed
`integral_wilsonLoop_mul_eq_zero`). -/
theorem plaqContrPlus_circle_eq_zero (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ < ν) (y : Fin 4 → ZMod N)
    {α β : Fin 4} (hαβ : α < β) :
    plaqContrPlus (torusShift N) (haarProb Circle) circleRep x μ ν y α β
      = 0 := by
  rw [plaqContrPlus_circle_eq_prod hN x hμν y hαβ,
    ← integral_wilsonLoop_mul hN x (ne_of_lt hμν) y (ne_of_lt hαβ)]
  exact integral_wilsonLoop_mul_eq_zero hN x hμν y hαβ

/-- **`Contr⁻` at the circle seat is the diagonal indicator.**
For `q = p` every one-link factor is
`∫ phiFactor · conj phiFactor = ∫ 1 = 1` (a character times its
conjugate), so the product is `1`; for `q ≠ p` the product is the
landed vanishing conjugate moment
`integral_wilsonLoop_mul_conj_eq_zero`. -/
theorem plaqContrMinus_circle (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ < ν) (y : Fin 4 → ZMod N)
    {α β : Fin 4} (hαβ : α < β) :
    plaqContrMinus (torusShift N) (haarProb Circle) circleRep x μ ν y α β
      = if (y, α, β) = (x, μ, ν) then 1 else 0 := by
  by_cases hqp : (y, α, β) = (x, μ, ν)
  · rw [if_pos hqp, plaqContrMinus_circle_eq_prod hN x hμν y hαβ]
    obtain ⟨hy, hα, hβ⟩ : y = x ∧ α = μ ∧ β = ν := by
      simpa only [Prod.mk.injEq] using hqp
    rw [hy, hα, hβ]
    refine Finset.prod_eq_one fun ℓ _ => ?_
    have hpt : ∀ z : Circle, phiFactor (torusShift N) x μ ν ℓ z
        * starRingEnd ℂ (phiFactor (torusShift N) x μ ν ℓ z) = 1 := by
      intro z
      obtain ⟨w, hw⟩ := phiFactor_eq_coe x μ ν ℓ z
      rw [hw]
      exact circle_coe_mul_conj w
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    simp
  · rw [if_neg hqp, plaqContrMinus_circle_eq_prod hN x hμν y hαβ,
      ← integral_wilsonLoop_mul_conj hN x (ne_of_lt hμν) y (ne_of_lt hαβ)]
    exact integral_wilsonLoop_mul_conj_eq_zero hN x hμν y hαβ hqp

/-- **C1, per-plaquette discharge.** The contraction formula of
Q13-3, evaluated at the circle/fundamental seat, recovers
`Cov₀(W_p, D_q) = -1/2` for `q = p` and `0` otherwise — termwise,
in exact agreement with the landed
`covZero_circle_plaquette_density` (whose proof is the
independent Stage 1c-0 character computation). The assembly's
J normalization, dual/transpose wiring, covariance centering
and `2d` denominator all pass through this evaluation: the
direct contraction and both means vanish, the conjugate
contraction is the diagonal indicator, and
`-(1/2)·(0 + 1) = -1/2`. -/
theorem covZero_circle_plaquette_density_contr (hN : 2 ≤ N)
    (x : Fin 4 → ZMod N) {μ ν : Fin 4} (hμν : μ < ν)
    (y : Fin 4 → ZMod N) {α β : Fin 4} (hαβ : α < β) :
    covZero (torusShift N) (haarProb Circle) circleRep
        (fun U => wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν))
        (fun U => (plaquetteDensity (torusShift N) circleRep U y α β : ℂ))
      = if (y, α, β) = (x, μ, ν) then (-1 / 2 : ℂ) else 0 := by
  rw [covZero_plaquette_density_eq_contr (torusShift N) (haarProb Circle)
      circleRep circleRep_continuous (by norm_num) (torusShift_comm N)
      x μ ν y α β,
    plaqContrPlus_circle_eq_zero hN x hμν y hαβ,
    plaqContrMinus_circle hN x hμν y hαβ,
    plaqMean_circle_eq_zero hN x hμν, plaqMean_circle_eq_zero hN y hαβ,
    plaqMeanConj_circle_eq_zero hN y hαβ]
  split_ifs <;> norm_num

/-- The assembled per-plaquette bracket (charter (9)'s summand)
at the circle seat: `-1/2` on the diagonal, `0` off it. -/
theorem kappaContrTerm_circle (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ < ν) (y : Fin 4 → ZMod N)
    {α β : Fin 4} (hαβ : α < β) :
    kappaContrTerm (torusShift N) (haarProb Circle) circleRep x μ ν (y, α, β)
      = if (y, α, β) = (x, μ, ν) then (-1 / 2 : ℂ) else 0 := by
  have h := covZero_circle_plaquette_density_contr hN x hμν y hαβ
  rw [covZero_plaquette_density_eq_contr (torusShift N) (haarProb Circle)
    circleRep circleRep_continuous (by norm_num) (torusShift_comm N)
    x μ ν y α β] at h
  exact h

/-- **C1, total discharge.** The assembled formula (9),
evaluated at the circle/fundamental seat, totals `-1/2`: in the
link-sharing sum only the diagonal bracket survives. -/
theorem assembled_kappa_circle (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ < ν) :
    ∑ q ∈ sharingPlaquettes (torusShift N)
        (plaquetteLinks (torusShift N) x μ ν),
        kappaContrTerm (torusShift N) (haarProb Circle) circleRep x μ ν q
      = -1 / 2 := by
  have hmem : (x, μ, ν) ∈ sharingPlaquettes (torusShift N)
      (plaquetteLinks (torusShift N) x μ ν) := by
    rw [sharingPlaquettes, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hμν, ?_⟩
    refine ⟨(x, μ), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩ <;>
      · rw [plaquetteLinks_eq (torusShift N) (torusShift_comm N)]
        exact Finset.mem_insert_self _ _
  have h₀ : ∀ q ∈ sharingPlaquettes (torusShift N)
        (plaquetteLinks (torusShift N) x μ ν), q ≠ (x, μ, ν) →
      kappaContrTerm (torusShift N) (haarProb Circle) circleRep x μ ν q
        = 0 := by
    intro q hq hqne
    rw [sharingPlaquettes, Finset.mem_filter] at hq
    obtain ⟨y, α, β⟩ := q
    have hαβ : α < β := hq.2.1
    rw [kappaContrTerm_circle hN x hμν y hαβ, if_neg hqne]
  rw [Finset.sum_eq_single (x, μ, ν) h₀ (fun h => (h hmem).elim),
    kappaContrTerm_circle hN x hμν x hμν, if_pos rfl]

/-- **C1 headline.** κ_p at the circle/fundamental seat, computed
through the assembled contraction formula (C2's (9) with the
brackets evaluated termwise), is `-1/2` — in exact agreement
with the landed `kappa_circle_plaquette`. -/
theorem kappa_circle_plaquette_contr (hN : 2 ≤ N) (x : Fin 4 → ZMod N)
    {μ ν : Fin 4} (hμν : μ < ν) :
    covZero (torusShift N) (haarProb Circle) circleRep
        (fun U => wilsonLoop (torusShift N) circleRep U x (plaquetteSteps μ ν))
        (fun U => (actionDensity (torusShift N) circleRep U : ℂ))
      = -1 / 2 := by
  rw [kappa_eq_sum_contr (torusShift N) (haarProb Circle) circleRep
    circleRep_continuous (by norm_num) (torusShift_comm N) x μ ν]
  exact assembled_kappa_circle hN x hμν

end Circle

end Setup

end ThetLogos
