/-
# Bosonic essential self-adjointness, β: the domain argument

2026-10-17. Tier T1 throughout (zero `sorry`/`admit`; headline axioms are the
standard three — see the `#print axioms` lines at the end of this file).

## What this file proves

`BosonicESA d lam W g` for **every** mode count `d`, **every** frequency tuple
`lam`, **every** quartic tensor `W` and **every** real coupling `g` — with no
parameter hypotheses at all:

    (hamPMap d lam W g).closure = (hamPMap d lam W g)†

This is Pitch 3's last open clause (the bosonic essential self-adjointness left
priced by Campaign 2, and reduced by ESA-α to the single inclusion
`(hamPMap)† ≤ (hamPMap).closure`). It is a **finite-mode** statement: the
configuration space is the finite-particle domain `Dom d` over finitely many
modes. Nothing here is a continuum or infinite-mode claim.

## The route (ESA-α §c, steps β1–β3)

The interaction `hamIntBos` is the balanced quartic `a†a†aa`; it preserves each
particle-number sector `domSector d n` *exactly*
(`hamIntBos_mem_domSector`, Δn = 0). The proof therefore never compares
operators across sectors and never touches von Neumann's double-adjoint
identity:

* **β1** (`coefB_adjoint_sector`): if two Fock vectors `y, z` are linked by
  the pairing identity `⟪z, e_c⟫ = ⟪y, H e_c⟫` at every basis vector, then the
  `c₀`-th Fourier coefficient of `z` equals the `c₀`-th coordinate of
  `H` applied to the *single-sector* truncation of `y` at `tot c₀`. Only
  exact sector preservation and symmetry of `H` on the finite-particle domain
  are used — no sectorwise-adjoint API, no relative-bound argument.
* **β2** (`hamIntBos_truncVec`, `truncVec_tendsto`): consequently `H` maps
  the occupation-cutoff truncation of `y` to the truncation of `z`, while
  the truncations converge to `y` and (applied to the adjoint value) to `z`
  by the basis expansion of the ℓ² space. There is no graph-norm tail
  estimate to make: exact sector preservation turns the tail into the tail
  of a convergent basis expansion.
* **β3** (`adjoint_le_closure`): an adjoint graph pair `(y, z)` is therefore
  a limit of graph pairs of `hamPMap`, i.e. lies in the closure of the
  graph, i.e. in the graph of the closure. ESA-α's equivalence
  `bosonicESA_iff_adjoint_le_closure` closes the headline
  (`bosonicESA_proved`).

Inputs consumed, all already theorems of the corpus: `hamIntBos_isSymmetric`,
`hamIntBos_mem_domSector`, `boseRepr_apply_eq_zero_of_tot_ne`, `dom_expand`,
`boseRepr_basis`, `dom_dense`, and ESA-α's `hamPMap_isClosable` and
`bosonicESA_iff_adjoint_le_closure`.
-/

import ThetLogos.BosonicESA

namespace ThetLogos

open scoped LinearPMap InnerProductSpace Topology
open Filter

/-- Basis vector of the finite-particle domain at a configuration: the
domain element whose underlying Fock vector is `boseE d c`. -/
noncomputable def basisVec (d : ℕ) (c : Config d) : Dom d :=
  ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩

/-- Fourier coefficient of a Fock vector at a configuration:
`coefB d y c = ⟪e_c, y⟫`. -/
noncomputable def coefB (d : ℕ) (y : BosonicFock d) (c : Config d) : ℂ :=
  ⟪boseE d c, y⟫_ℂ

/-- The coefficient is the plain `ℓ²` coordinate of the vector:
`⟪e_c, y⟫ = y c`. -/
theorem coefB_eq_apply (d : ℕ) (y : BosonicFock d) (c : Config d) :
    coefB d y c = y c := by
  show ⟪boseE d c, y⟫_ℂ = y c
  rw [boseE, lp.inner_single_left]
  simp [RCLike.inner_apply]

/-- Coefficients of a finite-particle vector are its `boseRepr`
coordinates. -/
theorem coefB_repr (d : ℕ) (x : Dom d) (c : Config d) :
    coefB d (x : BosonicFock d) c = (boseRepr d x) c := by
  have e0 : ((x : Dom d) : BosonicFock d)
      = ((∑ γ ∈ (boseRepr d x).support, ((boseRepr d x) γ) •
          ⟨boseE d γ, Submodule.subset_span (Set.mem_range_self γ)⟩ : Dom d) :
          BosonicFock d) :=
    congrArg (fun v : Dom d => ((v : BosonicFock d))) (dom_expand d x)
  have e1 : ((x : Dom d) : BosonicFock d)
      = ∑ γ ∈ (boseRepr d x).support, ((boseRepr d x) γ) • boseE d γ := by
    rw [e0, Submodule.coe_sum]
    exact Finset.sum_congr rfl (fun γ _ => Submodule.coe_smul _ _)
  show ⟪boseE d c, (x : BosonicFock d)⟫_ℂ = (boseRepr d x) c
  rw [e1, inner_sum]
  simp_rw [inner_smul_right, boseE_inner, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  by_cases hc : c ∈ (boseRepr d x).support
  · simp only [hc, ite_true]
  · simp only [hc, ite_false, Finsupp.notMem_support_iff.mp hc]

/-- The expansion of a domain vector in the Fock space, as a finite sum over
the support of its coordinates. -/
theorem dom_coe_expand (d : ℕ) (x : Dom d) :
    ((x : Dom d) : BosonicFock d)
      = ∑ γ ∈ (boseRepr d x).support, ((boseRepr d x) γ) • boseE d γ := by
  have e0 : ((x : Dom d) : BosonicFock d)
      = ((∑ γ ∈ (boseRepr d x).support, ((boseRepr d x) γ) •
          ⟨boseE d γ, Submodule.subset_span (Set.mem_range_self γ)⟩ : Dom d) :
          BosonicFock d) :=
    congrArg (fun v : Dom d => ((v : BosonicFock d))) (dom_expand d x)
  rw [e0, Submodule.coe_sum]
  exact Finset.sum_congr rfl (fun γ _ => Submodule.coe_smul _ _)

/-- Basis expansion of an arbitrary Fock vector along the occupation
basis. -/
theorem hasSum_coefB (d : ℕ) (y : BosonicFock d) :
    HasSum (fun c => coefB d y c • boseE d c) y := by
  have h := lp.hasSum_single (E := fun _ : Config d => ℂ) ENNReal.ofNat_ne_top y
  have e : ∀ c : Config d, coefB d y c • boseE d c
      = lp.single (E := fun _ : Config d => ℂ) 2 c (y c) := by
    intro c
    rw [coefB_eq_apply]
    show (y c) • lp.single 2 c (1 : ℂ) = lp.single (E := fun _ : Config d => ℂ) 2 c (y c)
    rw [← lp.single_smul, smul_eq_mul, mul_one]
  exact h.congr_fun (fun c => e c)

/-- The finset of configurations of total occupation at most `N`. -/
noncomputable def totLeFinset (d : ℕ) (N : ℕ) : Finset (Config d) :=
  (Finset.range (N + 1)).biUnion (sectorFinset d)

theorem mem_totLeFinset {d : ℕ} {N : ℕ} {c : Config d} :
    c ∈ totLeFinset d N ↔ tot c ≤ N := by
  simp only [totLeFinset, Finset.mem_biUnion, Finset.mem_range, mem_sectorFinset]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact Nat.lt_succ_iff.mp hn
  · intro h
    exact ⟨tot c, Nat.lt_succ_iff.mpr h, rfl⟩

/-- The cutoff finsets are cofinal: every finset of configurations is
eventually contained in one of them. -/
theorem tendsto_totLeFinset (d : ℕ) : Tendsto (totLeFinset d) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro s
  refine ⟨s.sup tot, fun N hN c hc => ?_⟩
  rw [mem_totLeFinset]
  exact (Finset.le_sup hc).trans hN

/-- Sector truncation of an arbitrary Fock vector, as a domain vector: the
sector-`n` part of `y`, placed in the finite-particle domain. -/
noncomputable def truncSector (d : ℕ) (y : BosonicFock d) (n : ℕ) : Dom d :=
  ∑ c ∈ sectorFinset d n, coefB d y c • basisVec d c

/-- Truncation of an arbitrary Fock vector to total occupation `≤ N`, as a
domain vector. -/
noncomputable def truncVec (d : ℕ) (y : BosonicFock d) (N : ℕ) : Dom d :=
  ∑ c ∈ totLeFinset d N, coefB d y c • basisVec d c

theorem basisVec_mem_domSector (d : ℕ) (c : Config d) :
    basisVec d c ∈ domSector d (tot c) :=
  Submodule.subset_span ⟨c, rfl, rfl⟩

theorem boseRepr_basisVec (d : ℕ) (c : Config d) :
    boseRepr d (basisVec d c) = Finsupp.single c 1 :=
  boseRepr_basis d c

/-- Linearity of `boseRepr` on basis sums, evaluated at a configuration:
coordinates of a linearly mapped basis sum. -/
theorem repr_linear_sum (d : ℕ) (F : Dom d →ₗ[ℂ] Dom d) (s : Finset (Config d))
    (w : Config d → ℂ) (c₀ : Config d) :
    (boseRepr d (F (∑ c ∈ s, w c • basisVec d c))) c₀
      = ∑ c ∈ s, w c * (boseRepr d (F (basisVec d c))) c₀ := by
  rw [map_sum, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]

/-- Coordinates of a basis sum: the coordinate at `c₀` picks out the
coefficient of `c₀` if `c₀` is in the index finset, and vanishes
otherwise. -/
theorem repr_basis_sum_apply (d : ℕ) (s : Finset (Config d)) (w : Config d → ℂ)
    (c₀ : Config d) :
    (boseRepr d (∑ c ∈ s, w c • basisVec d c)) c₀
      = if c₀ ∈ s then w c₀ else 0 := by
  rw [map_sum, Finsupp.finsetSum_apply]
  simp_rw [map_smul, boseRepr_basisVec, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']

/-- The Fock-space coercion of a truncation is the partial basis sum. -/
theorem coe_truncVec (d : ℕ) (y : BosonicFock d) (N : ℕ) :
    ((truncVec d y N : Dom d) : BosonicFock d)
      = ∑ c ∈ totLeFinset d N, coefB d y c • boseE d c := by
  rw [truncVec, Submodule.coe_sum]
  exact Finset.sum_congr rfl (fun γ _ => Submodule.coe_smul _ _)

/-- Partial basis sums of a Fock vector over a finset of configurations. -/
noncomputable def partialSum (d : ℕ) (y : BosonicFock d) (s : Finset (Config d)) :
    BosonicFock d :=
  ∑ c ∈ s, coefB d y c • boseE d c

/-- **β2 (convergence half).** The occupation-cutoff truncations of any
Fock vector converge to the vector. -/
theorem truncVec_tendsto (d : ℕ) (y : BosonicFock d) :
    Tendsto (fun N => ((truncVec d y N : Dom d) : BosonicFock d)) atTop (𝓝 y) := by
  have key0 : Tendsto (partialSum d y) atTop (𝓝 y) := hasSum_coefB d y
  have key : Tendsto (fun N => partialSum d y (totLeFinset d N)) atTop (𝓝 y) :=
    key0.comp (tendsto_totLeFinset d)
  refine key.congr (fun N => ?_)
  show partialSum d y (totLeFinset d N) = ((truncVec d y N : Dom d) : BosonicFock d)
  rw [partialSum]
  exact (coe_truncVec d y N).symm

/-- **β1.** The sector coefficient identity.

If two Fock vectors `y, z` are linked by the pairing identity
`⟪z, e_c⟫ = ⟪y, H e_c⟫` at every basis vector `e_c`, then the `c₀`-th
Fourier coefficient of `z` is the `c₀`-th coordinate of `H` applied to the
truncation of `y` to the single sector `tot c₀`:

    coefB z c₀ = (H (truncSector y (tot c₀)))_{c₀}.

Only exact sector preservation (`hamIntBos_mem_domSector`) and symmetry of
`H` on the finite-particle domain (`hamIntBos_isSymmetric`) enter. -/
theorem coefB_adjoint_sector (d : ℕ) (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) (y z : BosonicFock d)
    (hyz : ∀ c : Config d, ⟪z, (basisVec d c : BosonicFock d)⟫_ℂ
      = ⟪y, ((hamIntBos d lam W g (basisVec d c) : Dom d) : BosonicFock d)⟫_ℂ)
    (c₀ : Config d) :
    coefB d z c₀
      = (boseRepr d (hamIntBos d lam W g (truncSector d y (tot c₀)))) c₀ := by
  set n := tot c₀ with hn
  have step2 : coefB d z c₀
      = starRingEnd ℂ ⟪y,
          ((hamIntBos d lam W g (basisVec d c₀) : Dom d) : BosonicFock d)⟫_ℂ := by
    show ⟪boseE d c₀, z⟫_ℂ = _
    rw [← inner_conj_symm]
    show starRingEnd ℂ ⟪z, (basisVec d c₀ : BosonicFock d)⟫_ℂ = _
    rw [hyz c₀]
  have hHmem : hamIntBos d lam W g (basisVec d c₀) ∈ domSector d n :=
    hamIntBos_mem_domSector d lam W g (basisVec d c₀) (hn ▸ basisVec_mem_domSector d c₀)
  have hvan : ∀ γ : Config d, tot γ ≠ n →
      (boseRepr d (hamIntBos d lam W g (basisVec d c₀))) γ = 0 :=
    fun γ hγ => boseRepr_apply_eq_zero_of_tot_ne d hHmem hγ
  have step3 : ⟪y, ((hamIntBos d lam W g (basisVec d c₀) : Dom d) : BosonicFock d)⟫_ℂ
      = ∑ γ ∈ sectorFinset d n,
          ((boseRepr d (hamIntBos d lam W g (basisVec d c₀))) γ)
            * starRingEnd ℂ (coefB d y γ) := by
    rw [dom_coe_expand, inner_sum]
    have hterm : ∀ γ : Config d,
        ⟪y, ((boseRepr d (hamIntBos d lam W g (basisVec d c₀))) γ)
            • boseE d γ⟫_ℂ
          = ((boseRepr d (hamIntBos d lam W g (basisVec d c₀))) γ)
            * starRingEnd ℂ (coefB d y γ) := by
      intro γ
      rw [inner_smul_right, ← inner_conj_symm]
      rfl
    rw [Finset.sum_congr rfl (fun γ _ => hterm γ)]
    have hz1 : ∀ γ ∈ (boseRepr d (hamIntBos d lam W g (basisVec d c₀))).support
          ∪ sectorFinset d n,
        γ ∉ (boseRepr d (hamIntBos d lam W g (basisVec d c₀))).support →
          ((boseRepr d (hamIntBos d lam W g (basisVec d c₀))) γ)
            * starRingEnd ℂ (coefB d y γ) = 0 := by
      intro γ _ hγ
      rw [Finsupp.notMem_support_iff.mp hγ, zero_mul]
    have hz2 : ∀ γ ∈ (boseRepr d (hamIntBos d lam W g (basisVec d c₀))).support
          ∪ sectorFinset d n,
        γ ∉ sectorFinset d n →
          ((boseRepr d (hamIntBos d lam W g (basisVec d c₀))) γ)
            * starRingEnd ℂ (coefB d y γ) = 0 := by
      intro γ _ hγ
      rw [hvan γ (fun h => hγ ((mem_sectorFinset d).mpr h)), zero_mul]
    rw [Finset.sum_subset Finset.subset_union_left hz1,
      ← Finset.sum_subset Finset.subset_union_right hz2]
  have hswap : ∀ γ : Config d,
      (boseRepr d (hamIntBos d lam W g (basisVec d γ))) c₀
        = starRingEnd ℂ ((boseRepr d (hamIntBos d lam W g (basisVec d c₀))) γ) := by
    intro γ
    have hsym := hamIntBos_isSymmetric d lam W g (basisVec d γ) (basisVec d c₀)
    calc (boseRepr d (hamIntBos d lam W g (basisVec d γ))) c₀
        = ⟪boseE d c₀,
            ((hamIntBos d lam W g (basisVec d γ) : Dom d) : BosonicFock d)⟫_ℂ :=
          (coefB_repr d (hamIntBos d lam W g (basisVec d γ)) c₀).symm
      _ = starRingEnd ℂ ⟪((hamIntBos d lam W g (basisVec d γ) : Dom d) : BosonicFock d),
            boseE d c₀⟫_ℂ := by rw [inner_conj_symm]
      _ = starRingEnd ℂ ⟪((hamIntBos d lam W g (basisVec d γ) : Dom d) : BosonicFock d),
            ((basisVec d c₀ : Dom d) : BosonicFock d)⟫_ℂ := rfl
      _ = starRingEnd ℂ ⟪(basisVec d γ : BosonicFock d),
            ((hamIntBos d lam W g (basisVec d c₀) : Dom d) : BosonicFock d)⟫_ℂ := by
          rw [hsym]
      _ = starRingEnd ℂ (coefB d
            ((hamIntBos d lam W g (basisVec d c₀) : Dom d) : BosonicFock d) γ) := rfl
      _ = starRingEnd ℂ ((boseRepr d (hamIntBos d lam W g (basisVec d c₀))) γ) := by
          rw [coefB_repr]
  have step4 : (boseRepr d (hamIntBos d lam W g (truncSector d y n))) c₀
      = ∑ γ ∈ sectorFinset d n, (coefB d y γ)
          * starRingEnd ℂ ((boseRepr d (hamIntBos d lam W g (basisVec d c₀))) γ) := by
    rw [truncSector, repr_linear_sum]
    exact Finset.sum_congr rfl (fun γ _ => by rw [hswap γ])
  rw [step2, step3, step4]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  rw [map_mul, starRingEnd_self_apply, mul_comm]

/-- **β1 + β2 (operator half).** For any pair `y, z` linked by the pairing
identity at basis vectors, the Hamiltonian maps the occupation-cutoff
truncation of `y` exactly onto the truncation of `z`:

    H (truncVec y N) = truncVec z N.

In particular this holds for `y` in the adjoint domain and
`z = (hamPMap)† y` — the pairing identity at basis vectors is the formal
adjoint relation. Sectorwise this is β1; the coordinate at `c₀` with
`tot c₀ > N` vanishes on both sides by exact sector preservation. -/
theorem hamIntBos_truncVec (d : ℕ) (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) (y z : BosonicFock d)
    (hyz : ∀ c : Config d, ⟪z, (basisVec d c : BosonicFock d)⟫_ℂ
      = ⟪y, ((hamIntBos d lam W g (basisVec d c) : Dom d) : BosonicFock d)⟫_ℂ)
    (N : ℕ) :
    hamIntBos d lam W g (truncVec d y N) = truncVec d z N := by
  apply (boseRepr d).injective
  apply Finsupp.ext
  intro c₀
  have hL : (boseRepr d (hamIntBos d lam W g (truncVec d y N))) c₀
      = ∑ c ∈ totLeFinset d N, coefB d y c
          * (boseRepr d (hamIntBos d lam W g (basisVec d c))) c₀ := by
    rw [truncVec, repr_linear_sum]
  have hR : (boseRepr d (truncVec d z N)) c₀
      = if c₀ ∈ totLeFinset d N then coefB d z c₀ else 0 := by
    rw [truncVec, repr_basis_sum_apply]
  rw [hL, hR]
  by_cases hN : tot c₀ ≤ N
  · simp only [mem_totLeFinset.mpr hN, ite_true]
    have hsub : sectorFinset d (tot c₀) ⊆ totLeFinset d N := by
      intro γ hγ
      rw [mem_totLeFinset, (mem_sectorFinset d).mp hγ]
      exact hN
    have hvan : ∀ γ ∈ totLeFinset d N, γ ∉ sectorFinset d (tot c₀) →
        coefB d y γ * (boseRepr d (hamIntBos d lam W g (basisVec d γ))) c₀ = 0 := by
      intro γ _ hγ
      have hγ' : tot γ ≠ tot c₀ := fun h => hγ ((mem_sectorFinset d).mpr h)
      have hmem : hamIntBos d lam W g (basisVec d γ) ∈ domSector d (tot γ) :=
        hamIntBos_mem_domSector d lam W g (basisVec d γ) (basisVec_mem_domSector d γ)
      rw [boseRepr_apply_eq_zero_of_tot_ne d hmem (Ne.symm hγ'), mul_zero]
    rw [← Finset.sum_subset hsub hvan]
    have hE := coefB_adjoint_sector d lam W g y z hyz c₀
    rw [hE, truncSector, repr_linear_sum]
  · have hnc : ¬ c₀ ∈ totLeFinset d N := fun h => hN (mem_totLeFinset.mp h)
    simp only [hnc, ite_false]
    refine Finset.sum_eq_zero (fun γ hγ => ?_)
    have hγN : tot γ ≤ N := mem_totLeFinset.mp hγ
    have hne : tot c₀ ≠ tot γ := fun h => hN (h ▸ hγN)
    have hmem : hamIntBos d lam W g (basisVec d γ) ∈ domSector d (tot γ) :=
      hamIntBos_mem_domSector d lam W g (basisVec d γ) (basisVec_mem_domSector d γ)
    rw [boseRepr_apply_eq_zero_of_tot_ne d hmem hne, mul_zero]

/-- **β3.** The adjoint of `hamPMap` is contained in its closure:
every adjoint graph pair is a limit of `hamPMap` graph pairs — namely of
the pairs `(truncVec y N, truncVec z N)`, which lie in the graph by
`hamIntBos_truncVec`, and converge by `truncVec_tendsto`. -/
theorem adjoint_le_closure (d : ℕ) (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) :
    (hamPMap d lam W g)† ≤ (hamPMap d lam W g).closure := by
  apply LinearPMap.le_of_le_graph
  intro p hp
  rw [LinearPMap.mem_graph_iff] at hp
  obtain ⟨a, ha1, ha2⟩ := hp
  have hyz : ∀ c : Config d,
      ⟪(hamPMap d lam W g)† a, (basisVec d c : BosonicFock d)⟫_ℂ
        = ⟪(a : BosonicFock d),
            ((hamIntBos d lam W g (basisVec d c) : Dom d) : BosonicFock d)⟫_ℂ :=
    fun c => LinearPMap.adjoint_isFormalAdjoint (T := hamPMap d lam W g)
      (dom_dense d) a (basisVec d c)
  rw [← (hamPMap_isClosable d lam W g).graph_closure_eq_closure_graph]
  have hpmem : p ∈ closure ((hamPMap d lam W g).graph : Set (BosonicFock d × BosonicFock d)) := by
    rw [mem_closure_iff_seq_limit]
    refine ⟨fun N => (((truncVec d (a : BosonicFock d) N : Dom d) : BosonicFock d),
        ((truncVec d ((hamPMap d lam W g)† a) N : Dom d) : BosonicFock d)), ?_, ?_⟩
    · intro N
      dsimp only
      rw [SetLike.mem_coe, LinearPMap.mem_graph_iff]
      refine ⟨⟨((truncVec d (a : BosonicFock d) N : Dom d) : BosonicFock d),
        (truncVec d (a : BosonicFock d) N).2⟩, rfl, ?_⟩
      show (hamPMap d lam W g) ⟨((truncVec d (a : BosonicFock d) N : Dom d) : BosonicFock d),
          (truncVec d (a : BosonicFock d) N).2⟩
        = ((truncVec d ((hamPMap d lam W g)† a) N : Dom d) : BosonicFock d)
      rw [show (hamPMap d lam W g) ⟨((truncVec d (a : BosonicFock d) N : Dom d) : BosonicFock d),
            (truncVec d (a : BosonicFock d) N).2⟩
          = ((hamIntBos d lam W g (truncVec d (a : BosonicFock d) N) : Dom d) :
              BosonicFock d) from rfl,
        hamIntBos_truncVec d lam W g (a : BosonicFock d) ((hamPMap d lam W g)† a) hyz N]
    · have hp_eq : p = ((a : BosonicFock d), (hamPMap d lam W g)† a) :=
        Prod.ext ha1.symm ha2.symm
      rw [hp_eq]
      exact (truncVec_tendsto d (a : BosonicFock d)).prodMk_nhds
        (truncVec_tendsto d ((hamPMap d lam W g)† a))
  rwa [← Submodule.topologicalClosure_coe, SetLike.mem_coe] at hpmem

/-- **ESA-β headline.** Bosonic essential self-adjointness, for all
parameters and with no hypotheses: the closure of the finite-particle
bosonic Hamiltonian equals its adjoint. This discharges Pitch 3's last open
clause. Finite modes only — not a continuum statement. -/
theorem bosonicESA_proved (d : ℕ) (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) :
    BosonicESA d lam W g :=
  (bosonicESA_iff_adjoint_le_closure d lam W g).mpr (adjoint_le_closure d lam W g)

#print axioms coefB_adjoint_sector
#print axioms hamIntBos_truncVec
#print axioms adjoint_le_closure
#print axioms bosonicESA_proved

end ThetLogos
