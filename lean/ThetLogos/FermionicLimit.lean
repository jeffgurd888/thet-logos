import ThetLogos.FermionicFock
import ThetLogos.FockLimit

/-!
# ThetLogos.FermionicLimit — Pitch 2, Campaign A: the fermionic tower,
limit space, and Fock embeddings (Tasks 0, 1, 2 — fermionic half)

Scoping: `whitepaper/pitch-2-infinite-mode-scoping-DRAFT-2026-10-16.md`
§3 Tasks 0–2 and §3.9 (sequencing: fermions first). Route B (concrete
`lp` target over the limit configuration set `Finset ℕ`); no abstract
`Module.DirectLimit` anywhere.

## Contents (all T1)

**Task 0 — the tower at the index level.**
- `fermConfigEmb (h : d ≤ e) : Finset (Fin d) ↪ Finset (Fin e)`, by
  `Finset.map (Fin.castLEEmb h)`; `fermConfigEmbLim d : Finset (Fin d) ↪
  Finset ℕ` by `Finset.map Fin.valEmbedding`.
- Coherence in full (not just successive steps):
  `fermConfigEmb_trans`, and the cocycle `fermConfigEmbLim_comp` against
  the limit embedding.
- Limit factorization `fermConfig_factor`: every `S : Finset ℕ` is the
  image of a configuration at some finite level (via `Finset.attachFin`).
- Cardinality is preserved at every step (`Finset.card_map`).

**Task 1 — the limit space.**
- `FermionicFockLim := lp (fun _ : Finset ℕ => ℂ) 2`; basis `fockBasisLim`
  via `lp.single`; orthonormality from `lp.inner_single_left`; vacuum
  `fockVacLim`; finite-particle domain `fermDomLim` as the span of the basis
  range — proved DENSE in `FermionicFockLim` (`fermDomLim_topologicalClosure`,
  from the shared `lp` density lemma in `FockLimit`); sectors
  `fermSectorLim n` by `Finset.card`.

**Task 2 — the Fock embeddings.**
- The finite-level basis is repackaged as a `HilbertBasis`
  (`fermHilbertBasis`, via `EuclideanSpace.basisFun` +
  `OrthonormalBasis.toHilbertBasis`).
- `fockEmbLim d : FermionicFock d →ₗᵢ[ℂ] FermionicFockLim` and the
  finite-to-finite `fockEmb (h : d ≤ e)`, both assembled by the
  `onbEmb` machine of `FockLimit` (Mathlib has no `lp`-reindexing).
- Basis action, vacuum compatibility, domain compatibility
  (finite-particle → finite-particle), sector preservation, and the
  cocycle `(fockEmbLim e) ∘ (fockEmb h) = fockEmbLim d` — all PROVED
  (the full form, not the embeddings-into-the-limit-only partial).

## Honesty ledger

- Tier: T1, free theory, finite-particle domains. Zero sorries, no new
  axioms.
- This module builds the tower and the limit space ONLY. There is NO
  Γ-identification in the limit, NO `dΓ` in the limit, and NO gap
  statement (those are Campaign B). The density of `fermDomLim` is proved
  here as groundwork; the union characterization of the domains is
  Campaign B.
- Explicitly NOT claimed: interaction, the continuum limit, the
  Yang–Mills mass gap.
-/

namespace ThetLogos

open scoped InnerProductSpace

-- ============================================================================
-- Task 0 — the tower at the index level (fermions)
-- ============================================================================

/-- **Task 0 (fermions):** the mode-inclusion of occupation subsets,
`Finset (Fin d) ↪ Finset (Fin e)` along `d ≤ e`, by `Finset.map` of
`Fin.castLEEmb`. -/
def fermConfigEmb {d e : ℕ} (h : d ≤ e) : Finset (Fin d) ↪ Finset (Fin e) :=
  ⟨fun S => S.map (Fin.castLEEmb h), Finset.map_injective _⟩

/-- **Task 0 (fermions):** the inclusion of finite-level occupation
subsets into the limit index set `Finset ℕ`, by `Finset.map` of
`Fin.valEmbedding`. -/
def fermConfigEmbLim (d : ℕ) : Finset (Fin d) ↪ Finset ℕ :=
  ⟨fun S => S.map Fin.valEmbedding, Finset.map_injective _⟩

@[simp] theorem fermConfigEmb_apply {d e : ℕ} (h : d ≤ e) (S : Finset (Fin d)) :
    fermConfigEmb h S = S.map (Fin.castLEEmb h) := rfl

@[simp] theorem fermConfigEmbLim_apply (d : ℕ) (S : Finset (Fin d)) :
    fermConfigEmbLim d S = S.map Fin.valEmbedding := rfl

theorem fermConfigEmb_empty {d e : ℕ} (h : d ≤ e) :
    fermConfigEmb h (∅ : Finset (Fin d)) = ∅ := by
  rw [fermConfigEmb_apply, Finset.map_empty]

theorem fermConfigEmbLim_empty (d : ℕ) :
    fermConfigEmbLim d (∅ : Finset (Fin d)) = ∅ := by
  rw [fermConfigEmbLim_apply, Finset.map_empty]

/-- **Task 0 coherence, general form (T1):** the tower maps compose.
`fermConfigEmb h₂ ∘ fermConfigEmb h₁ = fermConfigEmb (h₁.trans h₂)`,
proved for all `d ≤ e ≤ f` at once (stronger than the successive-step
chain named as the acceptable partial in the scoping). -/
theorem fermConfigEmb_trans {d e f : ℕ} (h₁ : d ≤ e) (h₂ : e ≤ f) (S : Finset (Fin d)) :
    fermConfigEmb h₂ (fermConfigEmb h₁ S) = fermConfigEmb (h₁.trans h₂) S := by
  have hcast : (Fin.castLEEmb h₁).trans (Fin.castLEEmb h₂)
      = Fin.castLEEmb (h₁.trans h₂) := rfl
  show (S.map (Fin.castLEEmb h₁)).map (Fin.castLEEmb h₂)
    = S.map (Fin.castLEEmb (h₁.trans h₂))
  rw [Finset.map_map, hcast]

/-- **Task 0 cocycle against the limit (T1):** embedding a level-`d`
configuration first to level `e` and then into the limit is the same as
embedding it into the limit directly. -/
theorem fermConfigEmbLim_comp {d e : ℕ} (h : d ≤ e) (S : Finset (Fin d)) :
    fermConfigEmbLim e (fermConfigEmb h S) = fermConfigEmbLim d S := by
  have hcast : (Fin.castLEEmb h).trans Fin.valEmbedding = Fin.valEmbedding := rfl
  show (S.map (Fin.castLEEmb h)).map Fin.valEmbedding = S.map Fin.valEmbedding
  rw [Finset.map_map, hcast]

/-- Cardinality (= fermionic particle number) is preserved by the tower
maps. -/
theorem fermConfigEmb_card {d e : ℕ} (h : d ≤ e) (S : Finset (Fin d)) :
    (fermConfigEmb h S).card = S.card := by
  rw [fermConfigEmb_apply, Finset.card_map]

/-- Cardinality is preserved by the limit embedding. -/
theorem fermConfigEmbLim_card (d : ℕ) (S : Finset (Fin d)) :
    (fermConfigEmbLim d S).card = S.card := by
  rw [fermConfigEmbLim_apply, Finset.card_map]

/-- **Task 0 limit factorization (T1):** every limit configuration
`S : Finset ℕ` factors through some finite level: there is a `d` and a
`S₀ : Finset (Fin d)` with `fermConfigEmbLim d S₀ = S`. -/
theorem fermConfig_factor (S : Finset ℕ) :
    ∃ d, ∃ S₀ : Finset (Fin d), fermConfigEmbLim d S₀ = S := by
  refine ⟨S.sup id + 1, S.attachFin (fun m hm => ?_), ?_⟩
  · exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hm)
  · ext n
    simp only [fermConfigEmbLim_apply, Finset.mem_map, Finset.mem_attachFin]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hn
      exact ⟨⟨n, Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)⟩, hn, rfl⟩

-- ============================================================================
-- Task 1 — the limit space, its basis, vacuum, domain, and sectors (fermions)
-- ============================================================================

/-- **Task 1 (fermions):** the infinite-mode fermionic Fock space,
`ℓ²` over all finite occupation subsets of `ℕ`. -/
noncomputable abbrev FermionicFockLim := lp (fun _ : Finset ℕ => ℂ) 2

/-- The limit occupation basis vector at `S : Finset ℕ`. -/
noncomputable def fockBasisLim (S : Finset ℕ) : FermionicFockLim := lp.single 2 S 1

/-- The limit basis is orthonormal (from `lp.inner_single_left`). -/
theorem fockBasisLim_inner (S T : Finset ℕ) :
    ⟪fockBasisLim S, fockBasisLim T⟫_ℂ = if S = T then (1 : ℂ) else 0 := by
  unfold fockBasisLim
  rw [lp.inner_single_left, lp.single_apply]
  by_cases h : S = T <;> simp [h, RCLike.inner_apply]

theorem fockBasisLim_orthonormal : Orthonormal ℂ fockBasisLim := by
  rw [orthonormal_iff_ite]
  exact fockBasisLim_inner

/-- The limit vacuum `|0⟩ = e ∅`. -/
noncomputable def fockVacLim : FermionicFockLim := fockBasisLim ∅

/-- **Task 1 (fermions):** the finite-particle domain in the limit — the
span of the limit basis. -/
noncomputable def fermDomLim : Submodule ℂ FermionicFockLim :=
  Submodule.span ℂ (Set.range fockBasisLim)

/-- The finite-particle domain is dense in the limit space (proved here
as groundwork from the shared `lp` density lemma; the union
characterization of the tower's domains is Campaign B). -/
theorem fermDomLim_topologicalClosure : (fermDomLim).topologicalClosure = ⊤ :=
  lp_single_span_topologicalClosure (Finset ℕ)

/-- **Task 1 (fermions):** the `n`-particle sector in the limit — span of
the basis vectors whose occupation set has cardinality `n`. -/
noncomputable def fermSectorLim (n : ℕ) : Submodule ℂ FermionicFockLim :=
  Submodule.span ℂ (fockBasisLim '' {S : Finset ℕ | S.card = n})

theorem fockBasisLim_mem_sector {S : Finset ℕ} {n : ℕ} (hS : S.card = n) :
    fockBasisLim S ∈ fermSectorLim n :=
  Submodule.subset_span ⟨S, hS, rfl⟩

-- ============================================================================
-- Task 2 — the Fock embeddings (fermions)
-- ============================================================================

/-- The finite-level fermionic basis is orthonormal. -/
theorem fockBasis_orthonormal (d : ℕ) : Orthonormal ℂ (fockBasis d) := by
  rw [orthonormal_iff_ite]
  exact fockBasis_inner d

/-- The finite-level basis repackaged as a `HilbertBasis` (via
`EuclideanSpace.basisFun` and `OrthonormalBasis.toHilbertBasis`), the
input the `onbEmb` machine consumes. -/
noncomputable def fermHilbertBasis (d : ℕ) :
    HilbertBasis (Finset (Fin d)) ℂ (FermionicFock d) :=
  (EuclideanSpace.basisFun (Finset (Fin d)) ℂ).toHilbertBasis

theorem fermHilbertBasis_coe (d : ℕ) : ⇑(fermHilbertBasis d) = fockBasis d := by
  funext S
  simp only [fermHilbertBasis, OrthonormalBasis.coe_toHilbertBasis,
    EuclideanSpace.basisFun_apply, fockBasis]

/-- The finite-level basis spans the whole (finite-dimensional) space. -/
theorem fermHilbertBasis_span (d : ℕ) :
    Submodule.span ℂ (Set.range ⇑(fermHilbertBasis d)) = ⊤ := by
  have hdense := (fermHilbertBasis d).dense_span
  have hclosed : IsClosed
      ((Submodule.span ℂ (Set.range ⇑(fermHilbertBasis d)) : Submodule ℂ (FermionicFock d))
        : Set (FermionicFock d)) :=
    Submodule.closed_of_finiteDimensional _
  rw [eq_top_iff]
  calc ⊤ = (Submodule.span ℂ (Set.range ⇑(fermHilbertBasis d))).topologicalClosure :=
        hdense.symm
    _ ≤ Submodule.span ℂ (Set.range ⇑(fermHilbertBasis d)) :=
        Submodule.topologicalClosure_minimal _ le_rfl hclosed

/-- The finite sector, restated as a span over an image set (the shape
the embedding machine consumes). -/
theorem sector_eq_image (d n : ℕ) :
    sector d n = Submodule.span ℂ (fockBasis d '' {S : Finset (Fin d) | S.card = n}) := by
  have hset : {x : FermionicFock d | ∃ S : Finset (Fin d), S.card = n ∧ x = fockBasis d S}
      = fockBasis d '' {S : Finset (Fin d) | S.card = n} := by
    ext x
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact ⟨S, hS, rfl⟩
    · rintro ⟨S, hS, rfl⟩
      exact ⟨S, hS, rfl⟩
  show Submodule.span ℂ
      {x : FermionicFock d | ∃ S : Finset (Fin d), S.card = n ∧ x = fockBasis d S} = _
  rw [hset]

/-- The target family of `fockEmbLim d` is orthonormal (an orthonormal
family composed with an embedding stays orthonormal). -/
theorem fockBasisLim_comp_orthonormal (d : ℕ) :
    Orthonormal ℂ (fockBasisLim ∘ ⇑(fermConfigEmbLim d)) :=
  fockBasisLim_orthonormal.comp _ (fermConfigEmbLim d).injective

/-- **Task 2 (fermions): the embedding into the limit.**
`fockEmbLim d : FermionicFock d →ₗᵢ[ℂ] FermionicFockLim`, assembled by the
`onbEmb` machine: it is the unique linear isometry sending each
finite-level basis vector to the limit basis vector at the embedded
configuration. -/
noncomputable def fockEmbLim (d : ℕ) : FermionicFock d →ₗᵢ[ℂ] FermionicFockLim :=
  onbEmb (fermHilbertBasis d) (fockBasisLim ∘ ⇑(fermConfigEmbLim d))
    (fockBasisLim_comp_orthonormal d)

/-- **Task 2 basis action (T1):** `fockEmbLim d (e S) = eLim (embLim S)`. -/
theorem fockEmbLim_basis (d : ℕ) (S : Finset (Fin d)) :
    fockEmbLim d (fockBasis d S) = fockBasisLim (fermConfigEmbLim d S) := by
  have h := onbEmb_apply (fermHilbertBasis d) (fockBasisLim ∘ ⇑(fermConfigEmbLim d))
    (fockBasisLim_comp_orthonormal d) S
  rw [fermHilbertBasis_coe] at h
  exact h

/-- **Task 2 vacuum compatibility (T1):** the embedding sends the
finite-level vacuum to the limit vacuum. -/
theorem fockEmbLim_vacuum (d : ℕ) : fockEmbLim d (fockVac d) = fockVacLim := by
  show fockEmbLim d (fockBasis d ∅) = fockBasisLim ∅
  rw [fockEmbLim_basis, fermConfigEmbLim_empty]

/-- **Task 2 domain compatibility (T1):** every finite-level vector —
the finite-level space is the span of its basis, so this is the whole
finite-particle domain — lands in the limit's finite-particle domain
`fermDomLim`. -/
theorem fockEmbLim_mem_domLim (d : ℕ) (x : FermionicFock d) : fockEmbLim d x ∈ fermDomLim := by
  show onbEmb (fermHilbertBasis d) (fockBasisLim ∘ ⇑(fermConfigEmbLim d))
    (fockBasisLim_comp_orthonormal d) x ∈ fermDomLim
  refine onbEmb_mem _ _ _ (s := Set.univ) (t := fermDomLim) ?_ ?_
  · intro S _
    show fockBasisLim (fermConfigEmbLim d S) ∈ fermDomLim
    exact Submodule.subset_span ⟨fermConfigEmbLim d S, rfl⟩
  · rw [Set.image_univ, fermHilbertBasis_span]
    exact Submodule.mem_top

/-- **Task 2 sector preservation (T1):** the `n`-particle sector at
level `d` maps into the `n`-particle sector of the limit. -/
theorem fockEmbLim_sector (d n : ℕ) (x : FermionicFock d) (hx : x ∈ sector d n) :
    fockEmbLim d x ∈ fermSectorLim n := by
  rw [sector_eq_image] at hx
  show onbEmb (fermHilbertBasis d) (fockBasisLim ∘ ⇑(fermConfigEmbLim d))
    (fockBasisLim_comp_orthonormal d) x ∈ fermSectorLim n
  refine onbEmb_mem _ _ _ (s := {S : Finset (Fin d) | S.card = n}) (t := fermSectorLim n) ?_ ?_
  · intro S hS
    show fockBasisLim (fermConfigEmbLim d S) ∈ fermSectorLim n
    exact fockBasisLim_mem_sector (by rw [fermConfigEmbLim_card]; exact hS)
  · rwa [fermHilbertBasis_coe]

/-- The target family of the finite-to-finite embedding is orthonormal. -/
theorem fockBasis_comp_orthonormal {d e : ℕ} (h : d ≤ e) :
    Orthonormal ℂ (fockBasis e ∘ ⇑(fermConfigEmb h)) :=
  (fockBasis_orthonormal e).comp _ (fermConfigEmb h).injective

/-- **Task 2 (fermions): the finite-to-finite embedding.**
`fockEmb (h : d ≤ e) : FermionicFock d →ₗᵢ[ℂ] FermionicFock e`, by the
same `onbEmb` machine. -/
noncomputable def fockEmb {d e : ℕ} (h : d ≤ e) :
    FermionicFock d →ₗᵢ[ℂ] FermionicFock e :=
  onbEmb (fermHilbertBasis d) (fockBasis e ∘ ⇑(fermConfigEmb h))
    (fockBasis_comp_orthonormal h)

/-- **Task 2 basis action, finite-to-finite (T1).** -/
theorem fockEmb_basis {d e : ℕ} (h : d ≤ e) (S : Finset (Fin d)) :
    fockEmb h (fockBasis d S) = fockBasis e (fermConfigEmb h S) := by
  have h' := onbEmb_apply (fermHilbertBasis d) (fockBasis e ∘ ⇑(fermConfigEmb h))
    (fockBasis_comp_orthonormal h) S
  rw [fermHilbertBasis_coe] at h'
  exact h'

/-- **Task 2 vacuum compatibility, finite-to-finite (T1).** -/
theorem fockEmb_vacuum {d e : ℕ} (h : d ≤ e) : fockEmb h (fockVac d) = fockVac e := by
  show fockEmb h (fockBasis d ∅) = fockBasis e ∅
  rw [fockEmb_basis, fermConfigEmb_empty]

/-- **Task 2 cocycle (T1):** embedding level `d` into level `e` and then
into the limit equals embedding level `d` into the limit directly.
Proved by `ContinuousLinearMap.ext_on`: the two composites are
continuous, agree on every basis vector (basis actions + the index
cocycle `fermConfigEmbLim_comp`), and the basis spans a dense set. -/
theorem fockEmb_cocycle {d e : ℕ} (h : d ≤ e) :
    (fockEmbLim e).comp (fockEmb h) = fockEmbLim d := by
  have hEq : ((fockEmbLim e).comp (fockEmb h)).toContinuousLinearMap
      = (fockEmbLim d).toContinuousLinearMap := by
    refine ContinuousLinearMap.ext_on (s := Set.range ⇑(fermHilbertBasis d)) ?_ ?_
    · rw [fermHilbertBasis_span]
      exact dense_univ
    · intro y hy
      obtain ⟨S, rfl⟩ := hy
      simp only [LinearIsometry.coe_toContinuousLinearMap]
      rw [fermHilbertBasis_coe]
      show (fockEmbLim e) ((fockEmb h) (fockBasis d S)) = (fockEmbLim d) (fockBasis d S)
      rw [fockEmb_basis, fockEmbLim_basis, fockEmbLim_basis, fermConfigEmbLim_comp]
  apply LinearIsometry.ext
  intro x
  simpa [LinearIsometry.coe_toContinuousLinearMap] using
    DFunLike.congr_fun hEq x

end ThetLogos
