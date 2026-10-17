import ThetLogos.BosonicAssembly
import ThetLogos.FockLimit

/-!
# ThetLogos.BosonicLimit — Pitch 2, Campaign A: the bosonic tower,
limit space, and Fock embeddings (Tasks 0, 1, 2 — bosonic half)

Scoping: `whitepaper/pitch-2-infinite-mode-scoping-DRAFT-2026-10-16.md`
§3 Tasks 0–2 and §3.9 (sequencing: bosons immediately after fermions —
see `FermionicLimit`). Route B (concrete `lp` target over the limit
configuration set `ConfigLim := ℕ →₀ ℕ`); no abstract
`Module.DirectLimit` anywhere.

## Contents (all T1)

**Task 0 — the tower at the index level.**
- `configEmb (h : d ≤ e) : Config d ↪ Config e`, by
  `Finsupp.embDomain (Fin.castLEEmb h)`; `configEmbLim d : Config d ↪
  ConfigLim` by `Finsupp.embDomain Fin.valEmbedding`. (One technical
  helper is proved first: `Finsupp.embDomain` composition,
  `embDomain_trans` — Mathlib has the simp-normal forms of `embDomain`
  but no composition lemma.)
- Coherence in full (not just successive steps): `configEmb_trans`,
  and the cocycle `configEmbLim_comp` against the limit embedding.
- Limit factorization `config_factor`: every `c : ℕ →₀ ℕ` factors
  through some finite level (restriction built with
  `Finsupp.onFinset` over `Finset.attachFin` of the support).

**Task 1 — the limit space.**
- `BosonicFockLim := lp (fun _ : ConfigLim => ℂ) 2`; basis `boseELim`
  via `lp.single`; orthonormality from `lp.inner_single_left`; vacuum
  `boseVacLim`; finite-particle domain `DomLim` as the span of the
  basis range — proved DENSE in `BosonicFockLim`
  (`DomLim_topologicalClosure`, shared `lp` density lemma); sectors
  `sectorSubLim n` by `totLim` (the `Finsupp.sum` total occupation).

**Task 2 — the Fock embeddings.**
- The finite-level basis is repackaged as a `HilbertBasis`
  (`boseHilbertBasis`, via `HilbertBasis.mk` + the density of `Dom d`,
  itself the shared `lp` density lemma: `Dom_topologicalClosure`).
- `fockEmbBosLim d : BosonicFock d →ₗᵢ[ℂ] BosonicFockLim` and the
  finite-to-finite `fockEmbBos (h : d ≤ e)`, both assembled by the
  `onbEmb` machine of `FockLimit` (Mathlib has no `lp`-reindexing).
- Basis action, vacuum compatibility, domain compatibility
  (`Dom d → DomLim`), sector preservation (via `totLim`-preservation
  `totLim_configEmbLim` / `tot_configEmb`), and the cocycle
  `(fockEmbBosLim e) ∘ (fockEmbBos h) = fockEmbBosLim d` — all PROVED
  (the full form, not the embeddings-into-the-limit-only partial).

## Honesty ledger

- Tier: T1, free theory, finite-particle domains. Zero sorries, no new
  axioms.
- This module builds the tower and the limit space ONLY. There is NO
  Γ-identification in the limit, NO `dΓ` in the limit, and NO gap
  statement (those are Campaign B). The density of `DomLim` is proved
  here as groundwork; the union characterization of the domains is
  Campaign B.
- Explicitly NOT claimed: interaction, the continuum limit, the
  Yang–Mills mass gap.
-/

namespace ThetLogos

open scoped InnerProductSpace

/-- **Task 1 (bosons), index set:** the limit configuration set
`ℕ →₀ ℕ` — finitely supported occupation functions on all modes. -/
abbrev ConfigLim := Finsupp ℕ ℕ

-- ============================================================================
-- Task 0 — the tower at the index level (bosons)
-- ============================================================================

/-- Technical helper: `Finsupp.embDomain` evaluated at a point in the
range of the embedding. -/
theorem embDomain_apply_of_eq {α β M : Type*} [Zero M] {e : α ↪ β} (v : α →₀ M)
    {a : α} {b : β} (ha : e a = b) : Finsupp.embDomain e v b = v a := by
  rw [Finsupp.embDomain_apply, dite_eq_left ⟨a, ha⟩]
  congr 1
  exact e.injective ((Classical.choose_spec (⟨a, ha⟩ : ∃ a, e a = b)).trans ha.symm)

/-- Technical helper: `Finsupp.embDomain` composes along embeddings
(Mathlib has no such lemma). -/
theorem embDomain_trans {α β γ M : Type*} [Zero M] (e₁ : α ↪ β) (e₂ : β ↪ γ)
    (v : α →₀ M) :
    Finsupp.embDomain e₂ (Finsupp.embDomain e₁ v)
      = Finsupp.embDomain (e₁.trans e₂) v := by
  ext b
  by_cases hb : ∃ a, (e₁.trans e₂) a = b
  · obtain ⟨a, ha⟩ := hb
    rw [embDomain_apply_of_eq _ ha,
      embDomain_apply_of_eq _ (show e₂ (e₁ a) = b from ha)]
    exact embDomain_apply_of_eq _ rfl
  · conv_rhs => rw [Finsupp.embDomain_apply, dite_eq_right hb]
    conv_lhs => rw [Finsupp.embDomain_apply]
    by_cases hb₂ : ∃ a₂, e₂ a₂ = b
    · rw [dite_eq_left hb₂]
      refine Finsupp.embDomain_of_notMem_range e₁ v _ ?_
      intro hmem
      obtain ⟨a₁, ha₁⟩ := hmem
      exact hb ⟨a₁, by
        rw [Function.Embedding.trans_apply, ha₁, Classical.choose_spec hb₂]⟩
    · rw [dite_eq_right hb₂]

/-- **Task 0 (bosons):** the mode-inclusion of occupation
configurations, `Config d ↪ Config e` along `d ≤ e`, by
`Finsupp.embDomain (Fin.castLEEmb h)`. -/
noncomputable def configEmb {d e : ℕ} (h : d ≤ e) : Config d ↪ Config e :=
  ⟨Finsupp.embDomain (Fin.castLEEmb h), Finsupp.embDomain_injective _⟩

/-- **Task 0 (bosons):** the inclusion of finite-level configurations
into the limit index set `ConfigLim`, by `Finsupp.embDomain
Fin.valEmbedding`. -/
noncomputable def configEmbLim (d : ℕ) : Config d ↪ ConfigLim :=
  ⟨Finsupp.embDomain Fin.valEmbedding, Finsupp.embDomain_injective _⟩

@[simp] theorem configEmb_apply {d e : ℕ} (h : d ≤ e) (c : Config d) :
    configEmb h c = Finsupp.embDomain (Fin.castLEEmb h) c := rfl

@[simp] theorem configEmbLim_apply (d : ℕ) (c : Config d) :
    configEmbLim d c = Finsupp.embDomain Fin.valEmbedding c := rfl

theorem configEmb_zero {d e : ℕ} (h : d ≤ e) :
    configEmb h (0 : Config d) = 0 := by
  simp only [configEmb_apply, Finsupp.embDomain_zero]

theorem configEmbLim_zero (d : ℕ) :
    configEmbLim d (0 : Config d) = 0 := by
  simp only [configEmbLim_apply, Finsupp.embDomain_zero]

/-- The tower map reads off the original occupation at embedded modes:
`(configEmb h c) (castLE h i) = c i`. -/
theorem configEmb_apply_castLE {d e : ℕ} (h : d ≤ e) (c : Config d) (i : Fin d) :
    configEmb h c (Fin.castLE h i) = c i := by
  show Finsupp.embDomain (Fin.castLEEmb h) c (Fin.castLE h i) = c i
  exact embDomain_apply_of_eq _ rfl

/-- **Task 0 coherence, general form (T1):** the tower maps compose,
for all `d ≤ e ≤ f` at once (stronger than the successive-step chain
named as the acceptable partial in the scoping). -/
theorem configEmb_trans {d e f : ℕ} (h₁ : d ≤ e) (h₂ : e ≤ f) (c : Config d) :
    configEmb h₂ (configEmb h₁ c) = configEmb (h₁.trans h₂) c := by
  show Finsupp.embDomain (Fin.castLEEmb h₂) (Finsupp.embDomain (Fin.castLEEmb h₁) c)
    = Finsupp.embDomain (Fin.castLEEmb (h₁.trans h₂)) c
  rw [embDomain_trans,
    show (Fin.castLEEmb h₁).trans (Fin.castLEEmb h₂)
      = Fin.castLEEmb (h₁.trans h₂) from rfl]

/-- **Task 0 cocycle against the limit (T1):** embedding a level-`d`
configuration first to level `e` and then into the limit is the same as
embedding it into the limit directly. -/
theorem configEmbLim_comp {d e : ℕ} (h : d ≤ e) (c : Config d) :
    configEmbLim e (configEmb h c) = configEmbLim d c := by
  show Finsupp.embDomain Fin.valEmbedding (Finsupp.embDomain (Fin.castLEEmb h) c)
    = Finsupp.embDomain Fin.valEmbedding c
  rw [embDomain_trans,
    show (Fin.castLEEmb h).trans Fin.valEmbedding = Fin.valEmbedding from rfl]

/-- **Task 0 limit factorization (T1):** every limit configuration
`c : ℕ →₀ ℕ` factors through some finite level: there is a `d` and a
`c₀ : Config d` with `configEmbLim d c₀ = c`. The restriction is built
with `Finsupp.onFinset` over `Finset.attachFin` of the support; the
level `c.support.sup id + 1` is a strict bound for the support. -/
theorem config_factor (c : ConfigLim) :
    ∃ d, ∃ c₀ : Config d, configEmbLim d c₀ = c := by
  classical
  refine ⟨c.support.sup id + 1,
    Finsupp.onFinset (c.support.attachFin (fun m hm => ?_)) (fun i => c i.val)
      (fun i hi => ?_), ?_⟩
  · exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hm)
  · rw [Finset.mem_attachFin]
    exact Finsupp.mem_support_iff.mpr hi
  · ext j
    show (Finsupp.embDomain Fin.valEmbedding _) j = c j
    by_cases hj : j < c.support.sup id + 1
    · rw [embDomain_apply_of_eq _ (show Fin.valEmbedding ⟨j, hj⟩ = j from rfl),
        Finsupp.onFinset_apply]
    · have hle : j ≤ c.support.sup id → False := fun hle =>
        hj (Nat.lt_succ_of_le hle)
      have hcj : c j = 0 := by
        by_contra hne
        exact hle (Finset.le_sup (f := id) (Finsupp.mem_support_iff.mpr hne))
      rw [hcj]
      rw [Finsupp.embDomain_apply]
      by_cases hjj : ∃ a : Fin (c.support.sup id + 1), Fin.valEmbedding a = j
      · rw [dite_eq_left hjj]
        have hval : (Classical.choose hjj).val = j := Classical.choose_spec hjj
        rw [Finsupp.onFinset_apply, hval, hcj]
      · rw [dite_eq_right hjj]

-- ============================================================================
-- Task 1 — the limit space, its basis, vacuum, domain, and sectors (bosons)
-- ============================================================================

/-- **Task 1 (bosons):** the infinite-mode bosonic Fock space, `ℓ²` over
all finitely supported occupation configurations on `ℕ`. -/
noncomputable abbrev BosonicFockLim := lp (fun _ : ConfigLim => ℂ) 2

/-- The limit occupation basis vector at `c : ConfigLim`. -/
noncomputable def boseELim (c : ConfigLim) : BosonicFockLim := lp.single 2 c 1

/-- The limit basis is orthonormal (from `lp.inner_single_left`). -/
theorem boseELim_inner (c c' : ConfigLim) :
    ⟪boseELim c, boseELim c'⟫_ℂ = if c = c' then (1 : ℂ) else 0 := by
  unfold boseELim
  rw [lp.inner_single_left, lp.single_apply]
  by_cases h : c = c' <;> simp [h, RCLike.inner_apply]

theorem boseELim_orthonormal : Orthonormal ℂ boseELim := by
  rw [orthonormal_iff_ite]
  exact boseELim_inner

/-- The limit vacuum `|0⟩ = e 0`. -/
noncomputable def boseVacLim : BosonicFockLim := boseELim 0

/-- **Task 1 (bosons):** the finite-particle domain in the limit — the
span of the limit basis. -/
noncomputable def DomLim : Submodule ℂ BosonicFockLim :=
  Submodule.span ℂ (Set.range boseELim)

/-- The finite-particle domain is dense in the limit space (proved here
as groundwork from the shared `lp` density lemma; the union
characterization of the tower's domains is Campaign B). -/
theorem DomLim_topologicalClosure : (DomLim).topologicalClosure = ⊤ :=
  lp_single_span_topologicalClosure ConfigLim

/-- Total occupation count of a limit configuration (`Finsupp.sum`). -/
def totLim (c : ConfigLim) : ℕ := c.sum (fun _ n => n)

/-- **Task 1 (bosons):** the `n`-particle sector in the limit — span of
the basis vectors whose total occupation count is `n`. -/
noncomputable def sectorSubLim (n : ℕ) : Submodule ℂ BosonicFockLim :=
  Submodule.span ℂ (boseELim '' {c : ConfigLim | totLim c = n})

theorem boseELim_mem_sector {c : ConfigLim} {n : ℕ} (hc : totLim c = n) :
    boseELim c ∈ sectorSubLim n :=
  Submodule.subset_span ⟨c, hc, rfl⟩

/-- The finite-particle domain at finite level is dense (the density
input for `boseHilbertBasis`; the shared `lp` density lemma applied to
`Dom d`). -/
theorem Dom_topologicalClosure (d : ℕ) : (Dom d).topologicalClosure = ⊤ :=
  lp_single_span_topologicalClosure (Config d)

-- ============================================================================
-- Task 2 — the Fock embeddings (bosons)
-- ============================================================================

/-- The finite-level bosonic basis repackaged as a `HilbertBasis` (via
`HilbertBasis.mk` and the density of `Dom d`), the input the `onbEmb`
machine consumes. -/
noncomputable def boseHilbertBasis (d : ℕ) : HilbertBasis (Config d) ℂ (BosonicFock d) :=
  HilbertBasis.mk (boseE_orthonormal d) (top_le_iff.mpr (Dom_topologicalClosure d))

theorem boseHilbertBasis_coe (d : ℕ) : ⇑(boseHilbertBasis d) = boseE d :=
  HilbertBasis.coe_mk _ _

/-- Total occupation is preserved by `embDomain` over any embedding of
mode sets (the arithmetic core of sector preservation). -/
theorem embDomain_sum_tot {d : ℕ} {β : Type*} (e : Fin d ↪ β) (c : Config d) :
    (Finsupp.embDomain e c).sum (fun _ n => n) = c.sum (fun _ n => n) := by
  classical
  show (∑ b ∈ (Finsupp.embDomain e c).support, (Finsupp.embDomain e c) b)
    = ∑ a ∈ c.support, c a
  rw [Finsupp.support_embDomain, Finset.sum_map]
  simp only [Finsupp.embDomain_apply_self]

/-- The finite total occupation, as a `Finsupp.sum`. -/
theorem tot_eq_sum (c : Config d) : tot c = c.sum (fun _ n => n) := by
  show (∑ i, c i) = c.sum (fun _ n => n)
  rw [Finsupp.sum_fintype _ _ (fun i => rfl)]

/-- **Sector preservation, index level (limit):** `totLim (configEmbLim d c) = tot c`. -/
theorem totLim_configEmbLim (d : ℕ) (c : Config d) :
    totLim (configEmbLim d c) = tot c := by
  show (Finsupp.embDomain Fin.valEmbedding c).sum (fun _ n => n) = tot c
  rw [tot_eq_sum, embDomain_sum_tot]

/-- **Sector preservation, index level (finite-to-finite):**
`tot (configEmb h c) = tot c`. -/
theorem tot_configEmb {d e : ℕ} (h : d ≤ e) (c : Config d) :
    tot (configEmb h c) = tot c := by
  rw [tot_eq_sum, tot_eq_sum, configEmb_apply, embDomain_sum_tot]

/-- The target family of `fockEmbBosLim d` is orthonormal. -/
theorem boseELim_comp_orthonormal (d : ℕ) :
    Orthonormal ℂ (boseELim ∘ ⇑(configEmbLim d)) :=
  boseELim_orthonormal.comp _ (configEmbLim d).injective

/-- **Task 2 (bosons): the embedding into the limit.**
`fockEmbBosLim d : BosonicFock d →ₗᵢ[ℂ] BosonicFockLim`, assembled by
the `onbEmb` machine: it is the unique linear isometry sending each
finite-level basis vector to the limit basis vector at the embedded
configuration. -/
noncomputable def fockEmbBosLim (d : ℕ) : BosonicFock d →ₗᵢ[ℂ] BosonicFockLim :=
  onbEmb (boseHilbertBasis d) (boseELim ∘ ⇑(configEmbLim d))
    (boseELim_comp_orthonormal d)

/-- **Task 2 basis action (T1):** `fockEmbBosLim d (e c) = eLim (embLim c)`. -/
theorem fockEmbBosLim_basis (d : ℕ) (c : Config d) :
    fockEmbBosLim d (boseE d c) = boseELim (configEmbLim d c) := by
  have h := onbEmb_apply (boseHilbertBasis d) (boseELim ∘ ⇑(configEmbLim d))
    (boseELim_comp_orthonormal d) c
  rw [boseHilbertBasis_coe] at h
  exact h

/-- **Task 2 vacuum compatibility (T1):** the embedding sends the
finite-level vacuum `e 0` to the limit vacuum. -/
theorem fockEmbBosLim_vacuum (d : ℕ) :
    fockEmbBosLim d (boseE d 0) = boseVacLim := by
  show fockEmbBosLim d (boseE d 0) = boseELim 0
  rw [fockEmbBosLim_basis, configEmbLim_zero]

/-- **Task 2 domain compatibility (T1):** the finite-particle domain
`Dom d` maps into the limit's finite-particle domain `DomLim`. -/
theorem fockEmbBosLim_dom (d : ℕ) (x : BosonicFock d) (hx : x ∈ Dom d) :
    fockEmbBosLim d x ∈ DomLim := by
  show onbEmb (boseHilbertBasis d) (boseELim ∘ ⇑(configEmbLim d))
    (boseELim_comp_orthonormal d) x ∈ DomLim
  refine onbEmb_mem _ _ _ (s := Set.univ) (t := DomLim) ?_ ?_
  · intro c _
    show boseELim (configEmbLim d c) ∈ DomLim
    exact Submodule.subset_span ⟨configEmbLim d c, rfl⟩
  · rw [Set.image_univ, boseHilbertBasis_coe]
    exact hx

/-- **Task 2 sector preservation (T1):** the `n`-particle sector at
level `d` maps into the `n`-particle sector of the limit. -/
theorem fockEmbBosLim_sector (d n : ℕ) (x : BosonicFock d) (hx : x ∈ sectorSub d n) :
    fockEmbBosLim d x ∈ sectorSubLim n := by
  show onbEmb (boseHilbertBasis d) (boseELim ∘ ⇑(configEmbLim d))
    (boseELim_comp_orthonormal d) x ∈ sectorSubLim n
  refine onbEmb_mem _ _ _ (s := {c : Config d | tot c = n}) (t := sectorSubLim n) ?_ ?_
  · intro c hc
    show boseELim (configEmbLim d c) ∈ sectorSubLim n
    exact boseELim_mem_sector (by rw [totLim_configEmbLim]; exact hc)
  · rwa [boseHilbertBasis_coe]

/-- The target family of the finite-to-finite embedding is orthonormal. -/
theorem boseE_comp_orthonormal {d e : ℕ} (h : d ≤ e) :
    Orthonormal ℂ (boseE e ∘ ⇑(configEmb h)) :=
  (boseE_orthonormal e).comp _ (configEmb h).injective

/-- **Task 2 (bosons): the finite-to-finite embedding.**
`fockEmbBos (h : d ≤ e) : BosonicFock d →ₗᵢ[ℂ] BosonicFock e`, by the
same `onbEmb` machine. -/
noncomputable def fockEmbBos {d e : ℕ} (h : d ≤ e) :
    BosonicFock d →ₗᵢ[ℂ] BosonicFock e :=
  onbEmb (boseHilbertBasis d) (boseE e ∘ ⇑(configEmb h))
    (boseE_comp_orthonormal h)

/-- **Task 2 basis action, finite-to-finite (T1).** -/
theorem fockEmbBos_basis {d e : ℕ} (h : d ≤ e) (c : Config d) :
    fockEmbBos h (boseE d c) = boseE e (configEmb h c) := by
  have h' := onbEmb_apply (boseHilbertBasis d) (boseE e ∘ ⇑(configEmb h))
    (boseE_comp_orthonormal h) c
  rw [boseHilbertBasis_coe] at h'
  exact h'

/-- **Task 2 vacuum compatibility, finite-to-finite (T1).** -/
theorem fockEmbBos_vacuum {d e : ℕ} (h : d ≤ e) :
    fockEmbBos h (boseE d 0) = boseE e 0 := by
  rw [fockEmbBos_basis, configEmb_zero]

/-- **Task 2 cocycle (T1):** embedding level `d` into level `e` and
then into the limit equals embedding level `d` into the limit
directly. Proved by `ContinuousLinearMap.ext_on`: the two composites
are continuous, agree on every basis vector (basis actions + the index
cocycle `configEmbLim_comp`), and the basis spans the dense domain
`Dom d`. -/
theorem fockEmbBos_cocycle {d e : ℕ} (h : d ≤ e) :
    (fockEmbBosLim e).comp (fockEmbBos h) = fockEmbBosLim d := by
  have hspan : Submodule.span ℂ (Set.range ⇑(boseHilbertBasis d)) = Dom d := by
    unfold Dom
    rw [boseHilbertBasis_coe]
  have hEq : ((fockEmbBosLim e).comp (fockEmbBos h)).toContinuousLinearMap
      = (fockEmbBosLim d).toContinuousLinearMap := by
    refine ContinuousLinearMap.ext_on (s := Set.range ⇑(boseHilbertBasis d)) ?_ ?_
    · rw [hspan]
      intro x
      rw [← Submodule.topologicalClosure_coe, Dom_topologicalClosure]
      exact Submodule.mem_top
    · intro y hy
      obtain ⟨c, rfl⟩ := hy
      simp only [LinearIsometry.coe_toContinuousLinearMap]
      rw [boseHilbertBasis_coe]
      show (fockEmbBosLim e) ((fockEmbBos h) (boseE d c))
        = (fockEmbBosLim d) (boseE d c)
      rw [fockEmbBos_basis, fockEmbBosLim_basis, fockEmbBosLim_basis, configEmbLim_comp]
  apply LinearIsometry.ext
  intro x
  simpa [LinearIsometry.coe_toContinuousLinearMap] using
    DFunLike.congr_fun hEq x

end ThetLogos
