import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Spectrum
import ThetLogos.BosonicSecondQuant
import ThetLogos.FockLimit

namespace ThetLogos

open scoped InnerProductSpace

/-!
# ThetLogos.BosonicInteraction — Pitch 3, Campaign 2: bosonic interaction

**Mandatory honesty clause (Pitch 3 scoping §6).** *Interacting Hamiltonian at
finite modes: H = H₀ + gV with V a Wick polynomial in the corpus's
creation/annihilation operators. The gap statements are in the eigenvalue
sense of Rungs 9–10 (bosons: on the finite-particle domain). This is matter
self-interaction only — no gauge field, no continuum, no Poincaré — and is
not the interacting Yang–Mills mass gap; the spectral statement for the
bosonic operator is its sectorwise form, and uniform gap persistence for
general bosonic coupling is false in general and is not claimed.*

This module builds Campaign 2 of the Pitch 3 scoping
(`whitepaper/pitch-3-interaction-scoping-DRAFT-2026-10-16.md`, Tasks
B1–B3), the bosonic companion of Campaign 1 (`FermionicInteraction.lean`,
not imported — the two Fock parents cannot share an environment):

- **B1 (§1).** The bosonic quartic monomial calculus on `Dom d`: monomial
  action on the configuration basis with its √-coefficient formula
  (`monoC_single`), particle-number bookkeeping (`monoCoef_ne_zero_tot`,
  injectivity of the configuration map on the support), and the
  number-relative bound `‖monoCoef‖ ≤ (n+2)²` on the `n`-particle sector.
  The general quartic `wickQuarticBos W`, its coefficient and column-sum
  bounds (`intBoundBos W · (n+2)²`), and the symmetrized interaction
  `intOpBos W`, symmetric on `Dom d` for every coupling tensor `W`.
- **B2 (§2).** The interacting Hamiltonian `hamIntBos = H₀ + g • intOpBos W`:
  symmetric on `Dom d`, preserving every particle sector. The
  self-adjointness content is stated in exactly the senses proved:
  (i) sectorwise — every sector `domSector d n` is finite-dimensional and
  the restriction of `hamIntBos` to it is symmetric, hence diagonalizable
  by the finite-dimensional spectral theorem (`hamIntBosSector_spectral`);
  (ii) as a partial linear map — `hamPMap` is densely defined and a formal
  adjoint of itself, i.e. `hamPMap ≤ hamPMap†`. Essential self-adjointness
  of the closure is **not** claimed in this module — it was discharged
  separately in `BosonicESA.lean` and `BosonicESABeta.lean`, building on
  `LinearPMap.closure`: the closure operation for partial linear maps
  DOES exist in the pinned Mathlib. (An earlier form of this header
  asserted that Mathlib has no closure operation for partial linear
  maps and no essential-self-adjointness criterion — that premise is
  stale; corrected 2026-10-18. The discharge route is the closure
  route, not a Mathlib Kato–Rellich or analytic-vector criterion, and
  the closure's domain remains an ℓ²-growth condition across
  infinitely many sectors.)
- **B3 (§§3–4).** (i) The diagonal density exhibit `densityIntBos`:
  explicit eigenvalues on the configuration basis, an exact gap theorem
  (uniform, all sectors), and the **not-a-dΓ certificate**
  `densityIntBos_not_dgamma` (the bosonic mirror of Campaign 1's).
  (iii) The proved refusal: with an attractive density coupling the
  eigenvalues are unbounded below (`densHamEigBos_unbounded_below`) —
  the reason no uniform persistence is claimed. (ii) Windowed persistence
  for the general quartic (`hamIntBos_gap_persistence_windowed`): inside
  any fixed `n`-particle sector, the free gap persists under an explicit
  small-coupling threshold depending on the window, by the
  maximal-coordinate transport of §4.

Everything is in the eigenvalue sense of Rungs 9–10: eigenvalue statements
are about eigenvectors in `Dom d` (equivalently, coordinates through
`boseRepr`), never about an abstract unbounded spectrum. Bosons only;
operators are unbounded on the full Fock space and live on the dense
finite-particle domain `Dom d`, the corpus's standing honest formulation.
-/

variable (d : ℕ)

-- ============================================================================
-- §0. Sector and diagonal-operator toolkit
-- ============================================================================

/-- Removing one particle at an occupied mode lowers the total count by one. -/
theorem tot_sub_single (c : Config d) (i : Fin d) (h : c i ≠ 0) :
    tot (c - Finsupp.single i (1 : ℕ)) = tot c - 1 := by
  have h1 : tot c = tot (c - Finsupp.single i (1 : ℕ)) + 1 := by
    conv_lhs => rw [← config_sub_single_add_single d c i h]
    exact tot_add_single _ _
  omega

/-- Removing one particle at an empty mode changes nothing. -/
theorem config_sub_single_eq_self (c : Config d) (i : Fin d) (h : c i = 0) :
    c - Finsupp.single i (1 : ℕ) = c := by
  ext j
  rw [Finsupp.tsub_apply, Finsupp.single_apply]
  by_cases hj : i = j
  · rw [if_pos hj]
    subst hj
    rw [h]
  · rw [if_neg hj, Nat.sub_zero]

/-- Removing one particle never raises the total count. -/
theorem tot_sub_single_le (c : Config d) (i : Fin d) :
    tot (c - Finsupp.single i (1 : ℕ)) ≤ tot c := by
  by_cases h : c i = 0
  · rw [config_sub_single_eq_self d c i h]
  · rw [tot_sub_single d c i h]
    exact Nat.sub_le _ _

/-- A mode's occupation is at most the total count. -/
theorem config_le_tot (c : Config d) (i : Fin d) : c i ≤ tot c :=
  Finset.single_le_sum (fun j _ => Nat.zero_le (c j)) (Finset.mem_univ i)

/-- The set of configurations of a fixed total count is finite: such a
configuration is determined by its values, each `< n + 1`. -/
theorem finite_setOf_tot_eq (n : ℕ) : Set.Finite {c : Config d | tot c = n} := by
  have hinj : Function.Injective
      (fun c : {c : Config d // tot c = n} =>
        (fun i => ⟨c.1 i, Nat.lt_succ_iff.mpr
          ((config_le_tot d c.1 i).trans (le_of_eq c.2))⟩ : Fin d → Fin (n + 1))) := by
    intro c₁ c₂ h
    apply Subtype.ext
    ext i
    have h2 := congrFun h i
    simpa using h2
  haveI : Finite {c : Config d // tot c = n} := Finite.of_injective _ hinj
  exact Set.finite_coe_iff.mpr this

/-- The configurations of total count `n`, as a finset. -/
noncomputable def sectorFinset (n : ℕ) : Finset (Config d) :=
  (finite_setOf_tot_eq d n).toFinset

theorem mem_sectorFinset {n : ℕ} {c : Config d} :
    c ∈ sectorFinset d n ↔ tot c = n :=
  Set.Finite.mem_toFinset _

/-- Coordinates of a vector in the `n`-particle sector vanish at every
configuration of a different total count. -/
theorem boseRepr_apply_eq_zero_of_tot_ne {n : ℕ} {x : Dom d}
    (hx : x ∈ domSector d n) {c : Config d} (hc : tot c ≠ n) :
    (boseRepr d x) c = 0 := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨γ, hγ, rfl⟩ := hz
      rw [boseRepr_basis, Finsupp.single_apply]
      split_ifs with h
      · exfalso
        subst h
        exact hc hγ
      · rfl
  | zero => simp
  | add u v _ _ hu hv => rw [map_add, Finsupp.add_apply, hu, hv, add_zero]
  | smul a u _ hu => rw [map_smul, Finsupp.smul_apply, hu, smul_eq_mul, mul_zero]

/-- Coordinate formula for an operator diagonal in the configuration basis. -/
theorem diagOpBos_coord {T : Module.End ℂ (Dom d)} {r : Config d → ℝ}
    (hT : ∀ c, T ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = (r c : ℂ) • ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩)
    (x : Dom d) (c : Config d) :
    (boseRepr d (T x)) c = (r c : ℂ) * (boseRepr d x) c := by
  have e1 : boseEquiv d (boseRepr d x)
      = ∑ γ ∈ (boseRepr d x).support, ((boseRepr d x) γ) •
          ⟨boseE d γ, Submodule.subset_span (Set.mem_range_self γ)⟩ := by
    have h := dom_expand d (boseEquiv d (boseRepr d x))
    rwa [show boseRepr d (boseEquiv d (boseRepr d x)) = boseRepr d x from
      LinearEquiv.symm_apply_apply (boseEquiv d) _] at h
  have hx : T x = ∑ γ ∈ (boseRepr d x).support,
      (((boseRepr d x) γ * (r γ : ℂ)) •
        ⟨boseE d γ, Submodule.subset_span (Set.mem_range_self γ)⟩) := by
    have hxe : x = boseEquiv d (boseRepr d x) :=
      (LinearEquiv.apply_symm_apply (boseEquiv d) x).symm
    conv_lhs => rw [hxe, e1]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [map_smul, hT γ, smul_smul]
  rw [hx, map_sum, Finsupp.finsetSum_apply]
  simp_rw [map_smul, boseRepr_basis, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul]
  by_cases hc : c ∈ (boseRepr d x).support
  · rw [Finset.sum_eq_single c (fun γ _ hγc => ?_) (fun h => absurd hc h)]
    · rw [if_pos rfl]
      ring
    · rw [if_neg hγc, mul_zero]
  · have hψc : (boseRepr d x) c = 0 := Finsupp.notMem_support_iff.mp hc
    rw [hψc, mul_zero]
    refine Finset.sum_eq_zero (fun γ hγ => ?_)
    by_cases hγc : γ = c
    · subst hγc
      exact absurd hγ hc
    · rw [if_neg hγc, mul_zero]

/-- A basis-diagonal operator with real eigenvalues is symmetric on `Dom d`. -/
theorem diagOpBos_isSymmetric {T : Module.End ℂ (Dom d)} {r : Config d → ℝ}
    (hT : ∀ c, T ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = (r c : ℂ) • ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩)
    (x y : Dom d) :
    ⟪((T x : Dom d) : BosonicFock d), (y : BosonicFock d)⟫_ℂ
      = ⟪(x : BosonicFock d), ((T y : Dom d) : BosonicFock d)⟫_ℂ := by
  refine Dom_induction₂ (P := fun x y =>
    ⟪((T x : Dom d) : BosonicFock d), (y : BosonicFock d)⟫_ℂ
      = ⟪(x : BosonicFock d), ((T y : Dom d) : BosonicFock d)⟫_ℂ) d
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ x y
  · intro c c'
    rw [hT c, hT c', Submodule.coe_smul, Submodule.coe_smul, inner_smul_left,
      inner_smul_right, boseE_inner]
    by_cases h : c = c'
    · subst h
      rw [if_pos rfl]
      simp [Complex.conj_ofReal]
    · rw [if_neg h]
      simp
  · intro x x' y hx hx'
    simp only [map_add, Submodule.coe_add, inner_add_left, hx, hx']
  · intro y
    simp [map_zero]
  · intro a x y hx
    simp only [map_smul, Submodule.coe_smul, inner_smul_left, hx]
  · intro x y y' hy hy'
    simp only [map_add, Submodule.coe_add, inner_add_right, hy, hy']
  · intro x
    simp [map_zero]
  · intro a x y hx
    simp only [map_smul, Submodule.coe_smul, inner_smul_right, hx]

/-- Eigenvalue extraction for a diagonal operator on `Dom d`
(Rungs 9–10 dialect, bosonic form). -/
theorem diagOpBos_eigenvalue {T : Module.End ℂ (Dom d)} {r : Config d → ℝ}
    (hT : ∀ c, T ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = (r c : ℂ) • ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩)
    {ψ : Dom d} (hψ : ψ ≠ 0) {μ : ℂ} (hμ : T ψ = μ • ψ) :
    ∃ c, μ = (r c : ℂ) := by
  obtain ⟨c, hc⟩ : ∃ c, (boseRepr d ψ) c ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : boseRepr d ψ = 0 := by
      ext c
      rw [Finsupp.zero_apply]
      exact h c
    have e : boseEquiv d (boseRepr d ψ) = ψ :=
      LinearEquiv.apply_symm_apply (boseEquiv d) ψ
    rw [hz, map_zero] at e
    exact hψ e.symm
  refine ⟨c, ?_⟩
  have hcoord := diagOpBos_coord d hT ψ c
  have hcoord2 : (boseRepr d (T ψ)) c = μ * (boseRepr d ψ) c := by
    rw [hμ, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact (mul_right_cancel₀ hc (hcoord.symm.trans hcoord2)).symm

-- ============================================================================
-- §1. B1: the bosonic quartic monomial calculus on `Dom d`
-- ============================================================================

/-- The configuration reached from `γ` by one quartic monomial
`a†ᵢ a†ⱼ aₖ aₗ` (annihilations act first: `l`, then `k`). -/
noncomputable def monoPhi (i j k l : Fin d) (γ : Config d) : Config d :=
  ((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ)) + Finsupp.single j (1 : ℕ)
    + Finsupp.single i (1 : ℕ)

/-- The √-coefficient of one quartic monomial `a†ᵢ a†ⱼ aₖ aₗ` on the
configuration basis: `√(γ l)` for the first annihilation (zero if the mode
is empty, killing the term), `√((γ - eₗ) k)` for the second, and
`√(· j + 1)`, `√(· i + 1)` for the creations. -/
noncomputable def monoCoef (i j k l : Fin d) (γ : Config d) : ℂ :=
  ((if γ l = 0 then 0 else sqrtNat (γ l))
    * (if (γ - Finsupp.single l (1 : ℕ)) k = 0 then 0
        else sqrtNat ((γ - Finsupp.single l (1 : ℕ)) k))
    * sqrtNat (((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ)) j
        + 1))
    * sqrtNat ((((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ))
        + Finsupp.single j (1 : ℕ)) i + 1)

/-- One quartic monomial at the coefficient level. -/
noncomputable def monoC (i j k l : Fin d) :
    (Config d →₀ ℂ) →ₗ[ℂ] (Config d →₀ ℂ) :=
  (adagC d i) ∘ₗ ((adagC d j) ∘ₗ ((annC d k) ∘ₗ (annC d l)))

/-- **Monomial action on the configuration basis (B1 core).** -/
theorem monoC_single (i j k l : Fin d) (γ : Config d) (a : ℂ) :
    monoC d i j k l (Finsupp.single γ a)
      = (a * monoCoef d i j k l γ) • Finsupp.single (monoPhi d i j k l γ) 1 := by
  by_cases h1 : γ l = 0
  · have hz : annC d l (Finsupp.single γ a) = 0 := by
      rw [annC_single, if_pos h1]
    simp only [monoC, monoCoef, monoPhi, LinearMap.comp_apply, hz, map_zero,
      if_pos h1, zero_mul, mul_zero, zero_smul]
  · by_cases h2 : (γ - Finsupp.single l (1 : ℕ)) k = 0
    · have hz : (annC d k ∘ₗ annC d l) (Finsupp.single γ a) = 0 := by
        rw [LinearMap.comp_apply, annC_single, if_neg h1, single_smul_one,
          annC_single, if_pos h2]
      simp only [monoC, monoCoef, monoPhi, LinearMap.comp_apply, hz, map_zero,
        if_neg h1, if_pos h2, mul_zero, zero_mul, zero_smul]
    · have e1 : annC d l (Finsupp.single γ a)
          = (a * sqrtNat (γ l)) • Finsupp.single (γ - Finsupp.single l (1 : ℕ)) 1 := by
        rw [annC_single, if_neg h1]
      have e2 : (annC d k) ((a * sqrtNat (γ l))
            • Finsupp.single (γ - Finsupp.single l (1 : ℕ)) 1)
          = ((a * sqrtNat (γ l)) * sqrtNat ((γ - Finsupp.single l (1 : ℕ)) k))
            • Finsupp.single ((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ))
              1 := by
        rw [single_smul_one, annC_single, if_neg h2]
      have e3 : (adagC d j) (((a * sqrtNat (γ l))
              * sqrtNat ((γ - Finsupp.single l (1 : ℕ)) k))
            • Finsupp.single ((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ))
              1)
          = (((a * sqrtNat (γ l)) * sqrtNat ((γ - Finsupp.single l (1 : ℕ)) k))
              * sqrtNat (((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ)) j
                  + 1))
            • Finsupp.single (((γ - Finsupp.single l (1 : ℕ))
                - Finsupp.single k (1 : ℕ)) + Finsupp.single j (1 : ℕ)) 1 := by
        rw [single_smul_one, adagC_single]
      have e4 : (adagC d i) ((((a * sqrtNat (γ l))
                * sqrtNat ((γ - Finsupp.single l (1 : ℕ)) k))
              * sqrtNat (((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ)) j
                  + 1))
            • Finsupp.single (((γ - Finsupp.single l (1 : ℕ))
                - Finsupp.single k (1 : ℕ)) + Finsupp.single j (1 : ℕ)) 1)
          = ((((a * sqrtNat (γ l)) * sqrtNat ((γ - Finsupp.single l (1 : ℕ)) k))
              * sqrtNat (((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ)) j
                  + 1))
              * sqrtNat ((((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ))
                  + Finsupp.single j (1 : ℕ)) i + 1))
            • Finsupp.single ((((γ - Finsupp.single l (1 : ℕ))
                - Finsupp.single k (1 : ℕ)) + Finsupp.single j (1 : ℕ))
                + Finsupp.single i (1 : ℕ)) 1 := by
        rw [single_smul_one, adagC_single]
      simp only [monoC, LinearMap.comp_apply, e1, e2, e3, e4, monoCoef,
        monoPhi, if_neg h1, if_neg h2]
      congr 1
      ring

/-- A monomial with nonzero coefficient preserves the total count: it
annihilates two particles and creates two. -/
theorem monoCoef_ne_zero_tot {i j k l : Fin d} {γ : Config d}
    (h : monoCoef d i j k l γ ≠ 0) : tot (monoPhi d i j k l γ) = tot γ := by
  have hl : γ l ≠ 0 := by
    by_contra hzero
    exact h (by simp only [monoCoef, if_pos hzero, zero_mul])
  have hk : (γ - Finsupp.single l (1 : ℕ)) k ≠ 0 := by
    by_contra hzero
    exact h (by simp only [monoCoef, if_pos hzero, mul_zero, zero_mul])
  have s1 : tot (γ - Finsupp.single l (1 : ℕ)) = tot γ - 1 :=
    tot_sub_single d γ l hl
  have s2 : tot ((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ))
      = tot (γ - Finsupp.single l (1 : ℕ)) - 1 :=
    tot_sub_single d _ k hk
  have s3 : tot (((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ))
        + Finsupp.single j (1 : ℕ))
      = tot ((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ)) + 1 :=
    tot_add_single _ _
  have s4 : tot (monoPhi d i j k l γ)
      = tot (((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ))
          + Finsupp.single j (1 : ℕ)) + 1 :=
    tot_add_single _ _
  have hγ2 : 2 ≤ tot γ := by
    have h1 : 1 ≤ γ l := Nat.pos_of_ne_zero hl
    have h2 : γ l ≤ tot γ := config_le_tot d γ l
    have h3 : 1 ≤ (γ - Finsupp.single l (1 : ℕ)) k := Nat.pos_of_ne_zero hk
    have h4 : (γ - Finsupp.single l (1 : ℕ)) k
        ≤ tot (γ - Finsupp.single l (1 : ℕ)) := config_le_tot d _ k
    omega
  rw [s4, s3, s2, s1]
  omega

/-- The configuration map of a monomial is invertible on the support of its
coefficient: from `monoPhi γ` one recovers `γ` by removing the created
particles and restoring the annihilated ones. -/
theorem monoPhi_sub_add {i j k l : Fin d} {γ : Config d}
    (h : monoCoef d i j k l γ ≠ 0) :
    ((monoPhi d i j k l γ - Finsupp.single i (1 : ℕ)) - Finsupp.single j (1 : ℕ))
      + Finsupp.single k (1 : ℕ) + Finsupp.single l (1 : ℕ) = γ := by
  have hl : γ l ≠ 0 := by
    by_contra hzero
    apply h
    simp only [monoCoef, if_pos hzero, zero_mul, mul_zero]
  have hk : (γ - Finsupp.single l (1 : ℕ)) k ≠ 0 := by
    by_contra hzero
    apply h
    simp only [monoCoef, if_pos hzero, mul_zero, zero_mul]
  have step1 : monoPhi d i j k l γ - Finsupp.single i (1 : ℕ)
      = ((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ)) + Finsupp.single j (1 : ℕ) :=
    config_add_single_sub_single d _ i
  have step2 : (((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ))
        + Finsupp.single j (1 : ℕ)) - Finsupp.single j (1 : ℕ)
      = (γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ) :=
    config_add_single_sub_single d _ j
  have step3 : ((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ))
        + Finsupp.single k (1 : ℕ) = γ - Finsupp.single l (1 : ℕ) :=
    config_sub_single_add_single d _ k hk
  have step4 : (γ - Finsupp.single l (1 : ℕ)) + Finsupp.single l (1 : ℕ) = γ :=
    config_sub_single_add_single d γ l hl
  calc ((monoPhi d i j k l γ - Finsupp.single i (1 : ℕ)) - Finsupp.single j (1 : ℕ))
        + Finsupp.single k (1 : ℕ) + Finsupp.single l (1 : ℕ)
      = ((((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ)))
          + Finsupp.single k (1 : ℕ)) + Finsupp.single l (1 : ℕ) := by
        rw [step1, step2]
    _ = (γ - Finsupp.single l (1 : ℕ)) + Finsupp.single l (1 : ℕ) := by rw [step3]
    _ = γ := step4

/-- Injectivity of the monomial configuration map on the coefficient
support — the combinatorial heart of the column bound. -/
theorem monoPhi_inj_on_support {i j k l : Fin d} {γ γ' : Config d}
    (hγ : monoCoef d i j k l γ ≠ 0) (hγ' : monoCoef d i j k l γ' ≠ 0)
    (h : monoPhi d i j k l γ = monoPhi d i j k l γ') : γ = γ' := by
  have eγ := monoPhi_sub_add d hγ
  have eγ' := monoPhi_sub_add d hγ'
  rw [← eγ, ← eγ', h]

/-- The norm of a `sqrtNat`, as a real square root. -/
theorem norm_sqrtNat (m : ℕ) : ‖sqrtNat m‖ = Real.sqrt (m : ℝ) := by
  rw [sqrtNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

/-- **Number-relative bound for a monomial coefficient (B1).** On the
`n`-particle sector the √-coefficient is at most `(n + 2)²`: two
annihilation factors contribute `√n` each, two creation factors `√(n+2)`
each. This is the bosonic substitute for Campaign 1's norm bound `‖a‖ ≤ 1`
— the bosonic `a`, `a†` are unbounded, and every bound in this campaign is
relative to the sector. -/
theorem monoCoef_norm_le {i j k l : Fin d} {γ : Config d} {n : ℕ}
    (hγ : tot γ = n) : ‖monoCoef d i j k l γ‖ ≤ ((n : ℝ) + 2) ^ 2 := by
  have hsqrt : ∀ m : ℕ, (m : ℝ) ≤ (n : ℝ) + 2 →
      ‖sqrtNat m‖ ≤ Real.sqrt ((n : ℝ) + 2) := by
    intro m hm
    rw [norm_sqrtNat]
    exact Real.sqrt_le_sqrt hm
  have hf1 : ‖(if γ l = 0 then (0 : ℂ) else sqrtNat (γ l))‖
      ≤ Real.sqrt ((n : ℝ) + 2) := by
    by_cases h : γ l = 0
    · rw [if_pos h, norm_zero]
      exact Real.sqrt_nonneg _
    · rw [if_neg h]
      exact hsqrt _ (by
        have := config_le_tot d γ l
        rw [hγ] at this
        have h2 : (γ l : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
        linarith)
  have hf2 : ‖(if (γ - Finsupp.single l (1 : ℕ)) k = 0 then (0 : ℂ)
        else sqrtNat ((γ - Finsupp.single l (1 : ℕ)) k))‖
      ≤ Real.sqrt ((n : ℝ) + 2) := by
    by_cases h : (γ - Finsupp.single l (1 : ℕ)) k = 0
    · rw [if_pos h, norm_zero]
      exact Real.sqrt_nonneg _
    · rw [if_neg h]
      refine hsqrt _ (by
        have h1 : (γ - Finsupp.single l (1 : ℕ)) k ≤ tot (γ - Finsupp.single l (1 : ℕ)) :=
          config_le_tot d _ k
        have h2 : tot (γ - Finsupp.single l (1 : ℕ)) ≤ tot γ := tot_sub_single_le d γ l
        rw [hγ] at h2
        have h3 : ((γ - Finsupp.single l (1 : ℕ)) k : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast h1.trans h2
        linarith)
  have hf3 : ‖sqrtNat (((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ)) j + 1)‖
      ≤ Real.sqrt ((n : ℝ) + 2) := by
    refine hsqrt _ (by
      have h1 : ((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ)) j
          ≤ tot ((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ)) :=
        config_le_tot d _ j
      have h2 : tot ((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ)) ≤ tot γ :=
        (tot_sub_single_le d _ k).trans (tot_sub_single_le d γ l)
      rw [hγ] at h2
      have hN : ((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ)) j + 1
          ≤ n + 2 := by omega
      exact_mod_cast hN)
  have hf4 : ‖sqrtNat ((((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ))
        + Finsupp.single j (1 : ℕ)) i + 1)‖ ≤ Real.sqrt ((n : ℝ) + 2) := by
    refine hsqrt _ (by
      have h1 : (((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ))
            + Finsupp.single j (1 : ℕ)) i
          ≤ tot (((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ))
            + Finsupp.single j (1 : ℕ)) := config_le_tot d _ i
      have h2 : tot (((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ))
            + Finsupp.single j (1 : ℕ))
          = tot ((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ)) + 1 :=
        tot_add_single _ _
      have h3 : tot ((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ)) ≤ tot γ :=
        (tot_sub_single_le d _ k).trans (tot_sub_single_le d γ l)
      rw [hγ] at h3
      have hN : (((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ))
            + Finsupp.single j (1 : ℕ)) i + 1 ≤ n + 2 := by omega
      exact_mod_cast hN)
  have hS : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) + 2) := Real.sqrt_nonneg _
  have step1 : ‖(if γ l = 0 then (0 : ℂ) else sqrtNat (γ l))‖
        * ‖(if (γ - Finsupp.single l (1 : ℕ)) k = 0 then (0 : ℂ)
            else sqrtNat ((γ - Finsupp.single l (1 : ℕ)) k))‖
      ≤ Real.sqrt ((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 2) :=
    mul_le_mul hf1 hf2 (norm_nonneg _) hS
  have step2 : ‖(if γ l = 0 then (0 : ℂ) else sqrtNat (γ l))‖
        * ‖(if (γ - Finsupp.single l (1 : ℕ)) k = 0 then (0 : ℂ)
            else sqrtNat ((γ - Finsupp.single l (1 : ℕ)) k))‖
        * ‖sqrtNat (((γ - Finsupp.single l (1 : ℕ)) - Finsupp.single k (1 : ℕ)) j + 1)‖
      ≤ (Real.sqrt ((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 2))
        * Real.sqrt ((n : ℝ) + 2) :=
    mul_le_mul step1 hf3 (norm_nonneg _) (mul_nonneg hS hS)
  have stepA : ‖((if γ l = 0 then (0 : ℂ) else sqrtNat (γ l))
        * (if (γ - Finsupp.single l (1 : ℕ)) k = 0 then (0 : ℂ)
            else sqrtNat ((γ - Finsupp.single l (1 : ℕ)) k)))‖
      ≤ Real.sqrt ((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 2) :=
    (norm_mul_le _ _).trans step1
  have stepB : ‖(((if γ l = 0 then (0 : ℂ) else sqrtNat (γ l))
        * (if (γ - Finsupp.single l (1 : ℕ)) k = 0 then (0 : ℂ)
            else sqrtNat ((γ - Finsupp.single l (1 : ℕ)) k)))
        * sqrtNat (((γ - Finsupp.single l (1 : ℕ))
            - Finsupp.single k (1 : ℕ)) j + 1))‖
      ≤ (Real.sqrt ((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 2))
        * Real.sqrt ((n : ℝ) + 2) :=
    (norm_mul_le _ _).trans
      (mul_le_mul stepA hf3 (norm_nonneg _) (mul_nonneg hS hS))
  have step3 : ‖monoCoef d i j k l γ‖
      ≤ ((Real.sqrt ((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 2))
          * Real.sqrt ((n : ℝ) + 2)) * Real.sqrt ((n : ℝ) + 2) := by
    rw [monoCoef]
    exact (norm_mul_le _ _).trans
      (mul_le_mul stepB hf4 (norm_nonneg _)
        (mul_nonneg (mul_nonneg hS hS) hS))
  refine step3.trans ?_
  have hsq : (Real.sqrt ((n : ℝ) + 2)) ^ 2 = (n : ℝ) + 2 :=
    Real.sq_sqrt (by positivity)
  have h5 : ((Real.sqrt ((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 2))
          * Real.sqrt ((n : ℝ) + 2)) * Real.sqrt ((n : ℝ) + 2)
      = ((Real.sqrt ((n : ℝ) + 2)) ^ 2) ^ 2 := by ring
  rw [h5, hsq]

/-- One quartic monomial as an operator on the finite-particle domain. -/
noncomputable def wickMonoBos (i j k l : Fin d) : Module.End ℂ (Dom d) :=
  (adagBos d i) ∘ₗ ((adagBos d j) ∘ₗ ((annBos d k) ∘ₗ (annBos d l)))

/-- The domain monomial is the coefficient monomial, transported. -/
theorem repr_wickMonoBos (i j k l : Fin d) (x : Dom d) :
    boseRepr d (wickMonoBos d i j k l x) = monoC d i j k l (boseRepr d x) := by
  simp only [wickMonoBos, monoC, LinearMap.comp_apply, adag_transport,
    ann_transport]

/-- **Sector preservation for a monomial (B1).** A quartic monomial maps
the `n`-particle sector to itself: it is a scalar multiple of the basis
vector at `monoPhi γ`, which has the same total count whenever the scalar
is nonzero, and is zero otherwise. -/
theorem wickMonoBos_mem_domSector (i j k l : Fin d) {n : ℕ} (x : Dom d)
    (hx : x ∈ domSector d n) : wickMonoBos d i j k l x ∈ domSector d n := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨γ, hγ, rfl⟩ := hz
      have hform : wickMonoBos d i j k l
            ⟨boseE d γ, Submodule.subset_span (Set.mem_range_self γ)⟩
          = monoCoef d i j k l γ •
            ⟨boseE d (monoPhi d i j k l γ),
              Submodule.subset_span (Set.mem_range_self _)⟩ := by
        apply (boseRepr d).injective
        rw [repr_wickMonoBos, boseRepr_basis, monoC_single, map_smul,
          boseRepr_basis, one_mul]
      rw [hform]
      by_cases hcoef : monoCoef d i j k l γ = 0
      · rw [hcoef, zero_smul]
        exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _
          (Submodule.subset_span
            ⟨monoPhi d i j k l γ, (monoCoef_ne_zero_tot d hcoef).trans hγ, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | smul a u _ hu => rw [map_smul]; exact Submodule.smul_mem _ _ hu

/-- The total coupling mass of a tensor: the sum of the entry norms.
The bosonic sector bounds are proportional to it. -/
noncomputable def couplingMassBos (W : Fin d → Fin d → Fin d → Fin d → ℂ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, ‖W i j k l‖

/-- The interaction bound constant: twice the coupling mass (the quartic
plus its adjoint copy). -/
noncomputable def intBoundBos (W : Fin d → Fin d → Fin d → Fin d → ℂ) : ℝ :=
  2 * couplingMassBos d W

/-- The general bosonic quartic at the coefficient level. -/
noncomputable def quarticC (W : Fin d → Fin d → Fin d → Fin d → ℂ) :
    (Config d →₀ ℂ) →ₗ[ℂ] (Config d →₀ ℂ) :=
  ∑ i, ∑ j, ∑ k, ∑ l, (W i j k l) • monoC d i j k l

/-- The general bosonic quartic on the domain: a finite sum of quartic
monomials with coupling tensor `W`. -/
noncomputable def wickQuarticBos (W : Fin d → Fin d → Fin d → Fin d → ℂ) :
    Module.End ℂ (Dom d) :=
  ∑ i, ∑ j, ∑ k, ∑ l, (W i j k l) • wickMonoBos d i j k l

/-- The domain quartic is the coefficient quartic, transported. -/
theorem repr_wickQuarticBos (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    (x : Dom d) :
    boseRepr d (wickQuarticBos d W x) = quarticC d W (boseRepr d x) := by
  simp only [wickQuarticBos, quarticC, LinearMap.sum_apply, map_sum, map_smul,
    LinearMap.smul_apply, repr_wickMonoBos]

/-- The quartic preserves every particle sector. -/
theorem wickQuarticBos_mem_domSector (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    {n : ℕ} (x : Dom d) (hx : x ∈ domSector d n) :
    wickQuarticBos d W x ∈ domSector d n := by
  have step : ∀ (s : Finset (Fin d)) (f : Fin d → Module.End ℂ (Dom d)),
      (∀ i ∈ s, f i x ∈ domSector d n) →
      (∑ i ∈ s, f i) x ∈ domSector d n := by
    intro s f hf
    rw [LinearMap.sum_apply]
    exact Submodule.sum_mem _ (fun i hi => hf i hi)
  unfold wickQuarticBos
  refine step Finset.univ _ (fun i _ => ?_)
  refine step Finset.univ _ (fun j _ => ?_)
  refine step Finset.univ _ (fun k _ => ?_)
  refine step Finset.univ _ (fun l _ => ?_)
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _
    (wickMonoBos_mem_domSector d i j k l x hx)

/-- **Coefficient bound for the quartic (B1).** Every matrix coefficient of
the quartic out of the `n`-particle sector is at most the coupling mass
times `(n + 2)²`. -/
theorem quarticC_coeff_bound (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    {n : ℕ} {γ : Config d} (hγ : tot γ = n) (c : Config d) :
    ‖(quarticC d W (Finsupp.single γ 1)) c‖
      ≤ couplingMassBos d W * ((n : ℝ) + 2) ^ 2 := by
  have hterm : ∀ i j k l : Fin d,
      ‖(W i j k l) * ((monoC d i j k l (Finsupp.single γ 1)) c)‖
        ≤ ‖W i j k l‖ * ((n : ℝ) + 2) ^ 2 := by
    intro i j k l
    by_cases hc : monoPhi d i j k l γ = c
    · have e : (monoC d i j k l (Finsupp.single γ 1)) c
          = monoCoef d i j k l γ := by
        rw [monoC_single, Finsupp.smul_apply, hc, Finsupp.single_apply,
          if_pos rfl, smul_eq_mul, mul_one, one_mul]
      rw [e, norm_mul]
      exact mul_le_mul_of_nonneg_left (monoCoef_norm_le d hγ) (norm_nonneg _)
    · have e : (monoC d i j k l (Finsupp.single γ 1)) c = 0 := by
        rw [monoC_single, Finsupp.smul_apply, Finsupp.single_apply,
          if_neg hc, smul_eq_mul, mul_zero]
      rw [e, mul_zero, norm_zero]
      exact mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hexpand : (quarticC d W (Finsupp.single γ 1)) c
      = ∑ i, ∑ j, ∑ k, ∑ l,
        (W i j k l) * ((monoC d i j k l (Finsupp.single γ 1)) c) := by
    rw [quarticC, LinearMap.sum_apply, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [LinearMap.sum_apply, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [LinearMap.sum_apply, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [LinearMap.sum_apply, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [hexpand]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum (fun i _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum (fun j _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun k _ => (norm_sum_le _ _).trans
        (Finset.sum_le_sum (fun l _ => hterm i j k l)))))))).trans ?_
  rw [couplingMassBos, Finset.sum_mul]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun k _ => ?_)
  exact le_of_eq (Finset.sum_mul ..).symm

/-- **Column bound for the quartic (B1).** Summing the coefficient norms
down one output column over the whole input sector still costs only the
coupling mass times `(n + 2)²`: for fixed output `c`, at most one input
configuration in the sector contributes to each monomial (injectivity of
`monoPhi` on the coefficient support). -/
theorem quarticC_col_sum_le (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    (n : ℕ) (c : Config d) :
    ∑ γ ∈ sectorFinset d n, ‖(quarticC d W (Finsupp.single γ 1)) c‖
      ≤ couplingMassBos d W * ((n : ℝ) + 2) ^ 2 := by
  have hexpand : ∀ γ : Config d, (quarticC d W (Finsupp.single γ 1)) c
      = ∑ i, ∑ j, ∑ k, ∑ l,
        (W i j k l) * ((monoC d i j k l (Finsupp.single γ 1)) c) := by
    intro γ
    rw [quarticC, LinearMap.sum_apply, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [LinearMap.sum_apply, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [LinearMap.sum_apply, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [LinearMap.sum_apply, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul]
  have hval : ∀ (i j k l : Fin d) (γ : Config d),
      ‖(W i j k l) * ((monoC d i j k l (Finsupp.single γ 1)) c)‖
        = ‖W i j k l‖ *
          (if monoPhi d i j k l γ = c then ‖monoCoef d i j k l γ‖ else 0) := by
    intro i j k l γ
    by_cases hc : monoPhi d i j k l γ = c
    · have e : (monoC d i j k l (Finsupp.single γ 1)) c
          = monoCoef d i j k l γ := by
        rw [monoC_single, Finsupp.smul_apply, hc, Finsupp.single_apply,
          if_pos rfl, smul_eq_mul, mul_one, one_mul]
      rw [if_pos hc, e, norm_mul]
    · have e : (monoC d i j k l (Finsupp.single γ 1)) c = 0 := by
        rw [monoC_single, Finsupp.smul_apply, Finsupp.single_apply,
          if_neg hc, smul_eq_mul, mul_zero]
      rw [if_neg hc, e, mul_zero, norm_zero, mul_zero]
  have hmono : ∀ i j k l : Fin d,
      ∑ γ ∈ sectorFinset d n,
        ‖(W i j k l) * ((monoC d i j k l (Finsupp.single γ 1)) c)‖
        ≤ ‖W i j k l‖ * ((n : ℝ) + 2) ^ 2 := by
    intro i j k l
    rw [Finset.sum_congr rfl (fun γ _ => hval i j k l γ), ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    by_cases hex : ∃ γ₀ ∈ sectorFinset d n,
        monoPhi d i j k l γ₀ = c ∧ monoCoef d i j k l γ₀ ≠ 0
    · obtain ⟨γ₀, hγ₀, hφ, hcoef⟩ := hex
      have htot : tot γ₀ = n := (finite_setOf_tot_eq d n).mem_toFinset.mp hγ₀
      refine le_trans (le_of_eq (Finset.sum_eq_single γ₀
        (fun γ hγS hγγ₀ => ?_) (fun hγ₀S => absurd hγ₀ hγ₀S))) ?_
      · by_cases h1 : monoPhi d i j k l γ = c
        · by_cases h2 : monoCoef d i j k l γ = 0
          · rw [if_pos h1, h2, norm_zero]
          · exact absurd
              (monoPhi_inj_on_support d h2 hcoef (h1.trans hφ.symm)) hγγ₀
        · rw [if_neg h1]
      · rw [if_pos hφ]
        exact monoCoef_norm_le d htot
    · refine le_trans (le_of_eq (Finset.sum_eq_zero (fun γ hγS => ?_))) ?_
      · by_cases h1 : monoPhi d i j k l γ = c
        · by_cases h2 : monoCoef d i j k l γ = 0
          · rw [if_pos h1, h2, norm_zero]
          · exact absurd ⟨γ, hγS, h1, h2⟩ hex
        · rw [if_neg h1]
      · exact sq_nonneg _
  have hswap : ∀ (F : Fin d → Fin d → Fin d → Fin d → Config d → ℝ),
      (∑ γ ∈ sectorFinset d n, ∑ i, ∑ j, ∑ k, ∑ l, F i j k l γ)
        = ∑ i, ∑ j, ∑ k, ∑ l, ∑ γ ∈ sectorFinset d n, F i j k l γ := by
    intro F
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact Finset.sum_comm
  have hpt : ∀ γ ∈ sectorFinset d n,
      ‖(quarticC d W (Finsupp.single γ 1)) c‖
        ≤ ∑ i, ∑ j, ∑ k, ∑ l,
            ‖(W i j k l) * ((monoC d i j k l (Finsupp.single γ 1)) c)‖ := by
    intro γ _
    rw [hexpand γ]
    exact (norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun i _ => (norm_sum_le _ _).trans
        (Finset.sum_le_sum (fun j _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum (fun k _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum (fun l _ => le_refl _))))))))
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [hswap (fun i j k l γ =>
    ‖(W i j k l) * ((monoC d i j k l (Finsupp.single γ 1)) c)‖)]
  refine (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
    (fun j _ => Finset.sum_le_sum (fun k _ => Finset.sum_le_sum
      (fun l _ => hmono i j k l))))).trans ?_
  rw [couplingMassBos, Finset.sum_mul]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun k _ => ?_)
  exact le_of_eq (Finset.sum_mul ..).symm

/-- Reversal of a quadruple sum over `Fin d` (the index flip
`(i, j, k, l) ↦ (l, k, j, i)`), by the product-type equiv — the same
argument as Campaign 1's `sum_quadruple_rev`, restated here since the
fermionic module cannot be imported. -/
theorem sum_quadruple_rev_bos {β : Type*} [AddCommMonoid β]
    (F : Fin d → Fin d → Fin d → Fin d → β) :
    (∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d, F i j k l)
      = ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d, F l k j i := by
  have key : ∀ G : Fin d → Fin d → Fin d → Fin d → β,
      (∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d, G i j k l)
        = ∑ t : ((Fin d × Fin d) × Fin d) × Fin d,
          G t.1.1.1 t.1.1.2 t.1.2 t.2 := by
    intro G
    exact (Fintype.sum_prod_type
      (fun p : Fin d × Fin d => ∑ k : Fin d, ∑ l : Fin d, G p.1 p.2 k l)).symm.trans
      ((Fintype.sum_prod_type
        (fun q : (Fin d × Fin d) × Fin d => ∑ l : Fin d, G q.1.1 q.1.2 q.2 l)).symm.trans
        (Fintype.sum_prod_type
          (fun t : ((Fin d × Fin d) × Fin d) × Fin d =>
            G t.1.1.1 t.1.1.2 t.1.2 t.2)).symm)
  let rev : ((Fin d × Fin d) × Fin d) × Fin d ≃ ((Fin d × Fin d) × Fin d) × Fin d :=
    { toFun := fun t => (((t.2, t.1.2), t.1.1.2), t.1.1.1)
      invFun := fun t => (((t.2, t.1.2), t.1.1.2), t.1.1.1)
      left_inv := fun ⟨⟨⟨a, b⟩, c⟩, e⟩ => rfl
      right_inv := fun ⟨⟨⟨a, b⟩, c⟩, e⟩ => rfl }
  exact (key F).trans ((Equiv.sum_comp rev
    (fun t => F t.1.1.1 t.1.1.2 t.1.2 t.2)).symm.trans
    (key (fun i j k l => F l k j i)).symm)

/-- The adjoint coupling tensor: `W` with indices reversed and entries
conjugated, as in Campaign 1. -/
noncomputable def adjCouplBos (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    (i j k l : Fin d) : ℂ :=
  (starRingEnd ℂ) (W l k j i)

/-- Conjugating the adjoint coupling twice returns the coupling. -/
theorem adjCouplBos_adjCouplBos (W : Fin d → Fin d → Fin d → Fin d → ℂ) :
    adjCouplBos d (adjCouplBos d W) = W := by
  funext i j k l
  simp [adjCouplBos]

/-- The adjoint flip preserves the coupling mass (index reversal is a
bijection of the quadruple sum). -/
theorem couplingMassBos_adjCouplBos (W : Fin d → Fin d → Fin d → Fin d → ℂ) :
    couplingMassBos d (adjCouplBos d W) = couplingMassBos d W := by
  have h2 : ∀ i j k l : Fin d, ‖adjCouplBos d W i j k l‖ = ‖W l k j i‖ := by
    intro i j k l
    rw [adjCouplBos, RCLike.norm_conj]
  calc couplingMassBos d (adjCouplBos d W)
      = ∑ i, ∑ j, ∑ k, ∑ l, ‖W l k j i‖ := by
        unfold couplingMassBos
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
          (fun j _ => Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl
            (fun l _ => h2 i j k l))))
    _ = couplingMassBos d W := by
        rw [couplingMassBos]
        exact (sum_quadruple_rev_bos d (fun i j k l => ‖W i j k l‖)).symm

/-- The symmetrized interaction at the coefficient level. -/
noncomputable def intOpC (W : Fin d → Fin d → Fin d → Fin d → ℂ) :
    (Config d →₀ ℂ) →ₗ[ℂ] (Config d →₀ ℂ) :=
  quarticC d W + quarticC d (adjCouplBos d W)

/-- The symmetrized bosonic interaction on the domain (B1 headline):
`V + V*` at the Wick level, symmetric for every coupling tensor `W`. -/
noncomputable def intOpBos (W : Fin d → Fin d → Fin d → Fin d → ℂ) :
    Module.End ℂ (Dom d) :=
  wickQuarticBos d W + wickQuarticBos d (adjCouplBos d W)

/-- The domain interaction is the coefficient interaction, transported. -/
theorem repr_intOpBos (W : Fin d → Fin d → Fin d → Fin d → ℂ) (x : Dom d) :
    boseRepr d (intOpBos d W x) = intOpC d W (boseRepr d x) := by
  simp only [intOpBos, intOpC, LinearMap.add_apply, map_add,
    repr_wickQuarticBos]

/-- Coefficient bound for the symmetrized interaction. -/
theorem intOpC_coeff_bound (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    {n : ℕ} {γ : Config d} (hγ : tot γ = n) (c : Config d) :
    ‖(intOpC d W (Finsupp.single γ 1)) c‖
      ≤ intBoundBos d W * ((n : ℝ) + 2) ^ 2 := by
  have e : (intOpC d W (Finsupp.single γ 1)) c
      = (quarticC d W (Finsupp.single γ 1)) c
        + (quarticC d (adjCouplBos d W) (Finsupp.single γ 1)) c := by
    rw [intOpC, LinearMap.add_apply, Finsupp.add_apply]
  rw [e, intBoundBos]
  refine (norm_add_le _ _).trans ?_
  have h1 := quarticC_coeff_bound d W hγ c
  have h2 := quarticC_coeff_bound d (adjCouplBos d W) hγ c
  rw [couplingMassBos_adjCouplBos] at h2
  have hX : 0 ≤ ((n : ℝ) + 2) ^ 2 := sq_nonneg _
  linarith [mul_le_mul_of_nonneg_right (le_refl (couplingMassBos d W)) hX]

/-- Column bound for the symmetrized interaction. -/
theorem intOpC_col_sum_le (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    (n : ℕ) (c : Config d) :
    ∑ γ ∈ sectorFinset d n, ‖(intOpC d W (Finsupp.single γ 1)) c‖
      ≤ intBoundBos d W * ((n : ℝ) + 2) ^ 2 := by
  have e : ∀ γ : Config d, (intOpC d W (Finsupp.single γ 1)) c
      = (quarticC d W (Finsupp.single γ 1)) c
        + (quarticC d (adjCouplBos d W) (Finsupp.single γ 1)) c := by
    intro γ
    rw [intOpC, LinearMap.add_apply, Finsupp.add_apply]
  have h1 := quarticC_col_sum_le d W n c
  have h2 := quarticC_col_sum_le d (adjCouplBos d W) n c
  rw [couplingMassBos_adjCouplBos] at h2
  have hmid : ∀ γ ∈ sectorFinset d n,
      ‖(intOpC d W (Finsupp.single γ 1)) c‖
        ≤ ‖(quarticC d W (Finsupp.single γ 1)) c‖
          + ‖(quarticC d (adjCouplBos d W) (Finsupp.single γ 1)) c‖ := by
    intro γ _
    rw [e γ]
    exact norm_add_le _ _
  refine (Finset.sum_le_sum hmid).trans ?_
  rw [Finset.sum_add_distrib]
  refine (add_le_add h1 h2).trans ?_
  rw [intBoundBos]
  ring_nf
  exact le_refl _

/-- The interaction preserves every particle sector. -/
theorem intOpBos_mem_domSector (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    {n : ℕ} (x : Dom d) (hx : x ∈ domSector d n) :
    intOpBos d W x ∈ domSector d n := by
  rw [intOpBos, LinearMap.add_apply]
  exact Submodule.add_mem _ (wickQuarticBos_mem_domSector d W x hx)
    (wickQuarticBos_mem_domSector d (adjCouplBos d W) x hx)

/-- The adjoint relation for one monomial on the domain: the adjoint of
`a†ᵢ a†ⱼ aₖ aₗ` is `a†ₗ a†ₖ aⱼ aᵢ`, from the corpus's `a`/`a†` adjoint
relations applied four times. -/
theorem wickMonoBos_inner_adjoint (i j k l : Fin d) (x y : Dom d) :
    ⟪((wickMonoBos d i j k l x : Dom d) : BosonicFock d),
        (y : BosonicFock d)⟫_ℂ
      = ⟪(x : BosonicFock d),
          ((wickMonoBos d l k j i y : Dom d) : BosonicFock d)⟫_ℂ := by
  simp only [wickMonoBos, LinearMap.comp_apply]
  rw [adjoint_relation_adag, adjoint_relation_adag, adjoint_relation,
    adjoint_relation]

/-- The adjoint relation for the quartic: the adjoint of `wickQuarticBos W`
is `wickQuarticBos (adjCouplBos W)`. -/
theorem wickQuarticBos_inner_adjoint (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    (x y : Dom d) :
    ⟪((wickQuarticBos d W x : Dom d) : BosonicFock d),
        (y : BosonicFock d)⟫_ℂ
      = ⟪(x : BosonicFock d),
          ((wickQuarticBos d (adjCouplBos d W) y : Dom d) :
            BosonicFock d)⟫_ℂ := by
  have hterm : ∀ i j k l : Fin d,
      ⟪((((W i j k l) • wickMonoBos d i j k l) x : Dom d) : BosonicFock d),
          (y : BosonicFock d)⟫_ℂ
        = ⟪(x : BosonicFock d),
            ((((adjCouplBos d W) l k j i • wickMonoBos d l k j i) y :
              Dom d) : BosonicFock d)⟫_ℂ := by
    intro i j k l
    rw [LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul,
      Submodule.coe_smul, inner_smul_left, inner_smul_right,
      wickMonoBos_inner_adjoint]
    rfl
  calc ⟪((wickQuarticBos d W x : Dom d) : BosonicFock d),
          (y : BosonicFock d)⟫_ℂ
      = ∑ i, ∑ j, ∑ k, ∑ l,
          ⟪((((W i j k l) • wickMonoBos d i j k l) x : Dom d) :
            BosonicFock d), (y : BosonicFock d)⟫_ℂ := by
        rw [wickQuarticBos, LinearMap.sum_apply, Submodule.coe_sum,
          sum_inner]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [LinearMap.sum_apply, Submodule.coe_sum, sum_inner]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [LinearMap.sum_apply, Submodule.coe_sum, sum_inner]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [LinearMap.sum_apply, Submodule.coe_sum, sum_inner]
    _ = ∑ i, ∑ j, ∑ k, ∑ l,
          ⟪(x : BosonicFock d),
            ((((adjCouplBos d W) l k j i • wickMonoBos d l k j i) y :
              Dom d) : BosonicFock d)⟫_ℂ :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
          (fun j _ => Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl
            (fun l _ => hterm i j k l))))
    _ = ⟪(x : BosonicFock d),
          ((wickQuarticBos d (adjCouplBos d W) y : Dom d) :
            BosonicFock d)⟫_ℂ := by
        rw [← sum_quadruple_rev_bos d (fun i j k l =>
          ⟪(x : BosonicFock d),
            ((((adjCouplBos d W) i j k l • wickMonoBos d i j k l) y :
              Dom d) : BosonicFock d)⟫_ℂ)]
        rw [wickQuarticBos, LinearMap.sum_apply, Submodule.coe_sum,
          inner_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [LinearMap.sum_apply, Submodule.coe_sum, inner_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [LinearMap.sum_apply, Submodule.coe_sum, inner_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [LinearMap.sum_apply, Submodule.coe_sum, inner_sum]

/-- **The bosonic interaction is symmetric on `Dom d` for every coupling
tensor `W` (B1 headline).** -/
theorem intOpBos_isSymmetric (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    (x y : Dom d) :
    ⟪((intOpBos d W x : Dom d) : BosonicFock d), (y : BosonicFock d)⟫_ℂ
      = ⟪(x : BosonicFock d), ((intOpBos d W y : Dom d) :
          BosonicFock d)⟫_ℂ := by
  have e1 : ∀ z : Dom d, ((intOpBos d W z : Dom d) : BosonicFock d)
      = ((wickQuarticBos d W z : Dom d) : BosonicFock d)
        + ((wickQuarticBos d (adjCouplBos d W) z : Dom d) : BosonicFock d) := by
    intro z
    rw [intOpBos, LinearMap.add_apply, Submodule.coe_add]
  rw [e1 x, e1 y, inner_add_left, inner_add_right,
    wickQuarticBos_inner_adjoint, wickQuarticBos_inner_adjoint,
    adjCouplBos_adjCouplBos, add_comm]

-- ============================================================================
-- §2. B2: the interacting Hamiltonian and its self-adjointness content
-- ============================================================================

/-- The interacting bosonic Hamiltonian on the finite-particle domain:
free part `dΓ(diag λ)` plus `g • V` for the symmetrized quartic `V`. -/
noncomputable def hamIntBos (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) :
    Module.End ℂ (Dom d) :=
  freeHamiltonianBos d lam + (g : ℂ) • intOpBos d W

/-- At zero coupling the interacting Hamiltonian is the free Hamiltonian. -/
theorem hamIntBos_zero (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) :
    hamIntBos d lam W 0 = freeHamiltonianBos d lam := by
  simp [hamIntBos]

/-- **The interacting Hamiltonian is symmetric on `Dom d` (B2, symmetry).** -/
theorem hamIntBos_isSymmetric (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) (x y : Dom d) :
    ⟪((hamIntBos d lam W g x : Dom d) : BosonicFock d),
        (y : BosonicFock d)⟫_ℂ
      = ⟪(x : BosonicFock d), ((hamIntBos d lam W g y : Dom d) :
          BosonicFock d)⟫_ℂ := by
  have e1 : ∀ z : Dom d, ((hamIntBos d lam W g z : Dom d) : BosonicFock d)
      = ((freeHamiltonianBos d lam z : Dom d) : BosonicFock d)
        + ((g : ℂ) • ((intOpBos d W z : Dom d) : BosonicFock d)) := by
    intro z
    rw [hamIntBos, LinearMap.add_apply, LinearMap.smul_apply,
      Submodule.coe_add, Submodule.coe_smul]
  rw [e1 x, e1 y, inner_add_left, inner_add_right,
    freeHamiltonianBos_selfadjoint, inner_smul_left, inner_smul_right,
    intOpBos_isSymmetric, Complex.conj_ofReal]

/-- The interacting Hamiltonian preserves every particle sector. -/
theorem hamIntBos_mem_domSector (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) {n : ℕ} (x : Dom d)
    (hx : x ∈ domSector d n) : hamIntBos d lam W g x ∈ domSector d n := by
  rw [hamIntBos, LinearMap.add_apply, LinearMap.smul_apply]
  exact Submodule.add_mem _
    (dgammaBos_mem_domSector d (onePartDiagBos d lam) n x hx)
    (Submodule.smul_mem _ _ (intOpBos_mem_domSector d W x hx))

/-- Every particle sector is finite-dimensional: it is the span of the
finitely many configurations of that total count. -/
theorem domSector_finiteDimensional (n : ℕ) :
    FiniteDimensional ℂ (domSector d n) := by
  have hset : {x : Dom d | ∃ c : Config d, tot c = n ∧
        x = ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩}
      = (fun c : {c : Config d // tot c = n} =>
          (⟨boseE d c.1, Submodule.subset_span
            (Set.mem_range_self c.1)⟩ : Dom d)) '' Set.univ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_univ, true_and]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
    · rintro ⟨⟨c, hc⟩, rfl⟩
      exact ⟨c, hc, rfl⟩
  have hfin : Set.Finite
      (Set.range fun c : {c : Config d // tot c = n} =>
        (⟨boseE d c.1, Submodule.subset_span
          (Set.mem_range_self c.1)⟩ : Dom d)) := by
    haveI : Finite {c : Config d // tot c = n} :=
      Finite.of_injective
        (fun c : {c : Config d // tot c = n} =>
          (fun i => ⟨c.1 i, Nat.lt_succ_iff.mpr
            ((config_le_tot d c.1 i).trans (le_of_eq c.2))⟩ :
            Fin d → Fin (n + 1)))
        (by
          intro c₁ c₂ h
          apply Subtype.ext
          ext i
          have h2 := congrFun h i
          simpa using h2)
    exact Set.finite_range _
  show FiniteDimensional ℂ (Submodule.span ℂ
    {x : Dom d | ∃ c : Config d, tot c = n ∧
      x = ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩})
  rw [hset]
  exact FiniteDimensional.span_of_finite ℂ (by rwa [Set.image_univ])

/-- The restriction of the interacting Hamiltonian to one particle
sector: a finite-dimensional endomorphism. -/
noncomputable def hamIntBosSector (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) (n : ℕ) :
    (domSector d n) →ₗ[ℂ] (domSector d n) :=
  (hamIntBos d lam W g).restrict
    (fun x hx => hamIntBos_mem_domSector d lam W g x hx)

/-- The sector restriction is symmetric. -/
theorem hamIntBosSector_isSymmetric (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) (n : ℕ) :
    @LinearMap.IsSymmetric ℂ (↥(domSector d n)) _ _ _
      (hamIntBosSector d lam W g n) := by
  intro x y
  exact hamIntBos_isSymmetric d lam W g x y

set_option maxHeartbeats 1600000 in
/-- **Sectorwise spectral theorem for the interacting Hamiltonian (B2
headline).** On every particle sector, `hamIntBos` has an orthonormal
basis of eigenvectors with real eigenvalues — the finite-dimensional
spectral theorem applied sector by sector. This, with the symmetry on
`Dom d` and the partial-map statement below, is the self-adjointness
content available in current Mathlib; see the module header for the
precise scope (no closure/essential-self-adjointness claim). -/
theorem hamIntBosSector_spectral (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) (n : ℕ) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ (domSector d n))) ℂ
          (domSector d n))
      (μ : Fin (Module.finrank ℂ (domSector d n)) → ℝ),
      ∀ i, hamIntBosSector d lam W g n (b i) = (μ i : ℂ) • (b i) := by
  haveI := domSector_finiteDimensional d n
  have hsym := hamIntBosSector_isSymmetric d lam W g n
  refine ⟨@LinearMap.IsSymmetric.eigenvectorBasis ℂ _ (↥(domSector d n)) _ _
      (hamIntBosSector d lam W g n) _ _ hsym rfl,
    @LinearMap.IsSymmetric.eigenvalues ℂ _ (↥(domSector d n)) _ _
      (hamIntBosSector d lam W g n) _ _ hsym rfl, fun i => ?_⟩
  exact @LinearMap.IsSymmetric.apply_eigenvectorBasis ℂ _ (↥(domSector d n)) _
    _ (hamIntBosSector d lam W g n) _ _ hsym rfl i

/-- The finite-particle domain is dense in the bosonic Fock space. -/
theorem dom_topologicalClosure :
    (Dom d).topologicalClosure = ⊤ := by
  have h := lp_single_span_topologicalClosure (Config d)
  exact h

/-- The finite-particle domain is dense (set form). -/
theorem dom_dense : Dense ((Dom d : Set (BosonicFock d))) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr (dom_topologicalClosure d)

/-- The interacting Hamiltonian as a partially defined linear map on the
whole Fock space, with domain the finite-particle domain. -/
noncomputable def hamPMap (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) :
    BosonicFock d →ₗ.[ℂ] BosonicFock d where
  domain := Dom d
  toFun := (Dom d).subtype ∘ₗ hamIntBos d lam W g

/-- **The Hamiltonian partial map is a formal adjoint of itself (B2).** -/
theorem hamPMap_isFormalAdjoint (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) :
    (hamPMap d lam W g).IsFormalAdjoint (hamPMap d lam W g) := by
  intro x y
  exact hamIntBos_isSymmetric d lam W g x y

/-- Consequently `hamPMap ≤ hamPMap†` in the partial-map order: the
operator is contained in its adjoint — the maximal self-adjointness
statement the `LinearPMap` API expresses without a closure operation. -/
theorem hamPMap_le_adjoint (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) :
    hamPMap d lam W g ≤ LinearPMap.adjoint (hamPMap d lam W g) :=
  (hamPMap_isFormalAdjoint d lam W g).le_adjoint (dom_dense d)

-- ============================================================================
-- §3. B3(i): the diagonal density exhibit, its exact gap, the not-a-dΓ
-- certificate, and (iii) the proved refusal of uniform persistence
-- ============================================================================

/-- The number operator of one mode, as a domain endomorphism. -/
noncomputable def numModeBos (i : Fin d) : Module.End ℂ (Dom d) :=
  (adagBos d i) ∘ₗ (annBos d i)

theorem numModeBos_basis (i : Fin d) (c : Config d) :
    numModeBos d i ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = (c i : ℂ) • ⟨boseE d c, Submodule.subset_span
          (Set.mem_range_self c)⟩ :=
  numberOp_mode_dom d i c

/-- The eigenvalue function of the density exhibit: the pairwise density
coupling evaluated on a configuration. -/
noncomputable def densEigBos (U : Fin d → Fin d → ℝ) (c : Config d) : ℝ :=
  ∑ i, ∑ j, if i < j then U i j * (c i : ℝ) * (c j : ℝ) else 0

/-- **The density-type interaction (B3 exhibit).** A quartic interaction
diagonal in the configuration basis: a sum over mode pairs of `U i j`
times the product of the two number operators. -/
noncomputable def densityIntBos (U : Fin d → Fin d → ℝ) :
    Module.End ℂ (Dom d) :=
  ∑ i, ∑ j, (if i < j then (U i j : ℂ) else 0) •
    ((numModeBos d i) ∘ₗ (numModeBos d j))

/-- The density interaction is diagonal in the configuration basis, with
explicit eigenvalues. -/
theorem densityIntBos_basis (U : Fin d → Fin d → ℝ) (c : Config d) :
    densityIntBos d U ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = (densEigBos d U c : ℂ) • ⟨boseE d c,
          Submodule.subset_span (Set.mem_range_self c)⟩ := by
  have hterm : ∀ i j : Fin d,
      ((numModeBos d i) ∘ₗ (numModeBos d j))
          ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
        = ((c j : ℂ) * (c i : ℂ)) • ⟨boseE d c,
            Submodule.subset_span (Set.mem_range_self c)⟩ := by
    intro i j
    rw [LinearMap.comp_apply, numModeBos_basis, map_smul, numModeBos_basis,
      smul_smul]
  have step1 : densityIntBos d U
        ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = (∑ i, ∑ j, ((if i < j then (U i j : ℂ) else 0)
          * ((c j : ℂ) * (c i : ℂ)))) • ⟨boseE d c,
            Submodule.subset_span (Set.mem_range_self c)⟩ := by
    simp only [densityIntBos, LinearMap.sum_apply, LinearMap.smul_apply,
      hterm, smul_smul, ← Finset.sum_smul]
  have step2 : (∑ i, ∑ j, ((if i < j then (U i j : ℂ) else 0)
        * ((c j : ℂ) * (c i : ℂ)))) = (densEigBos d U c : ℂ) := by
    rw [densEigBos]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases h : i < j
    · rw [if_pos h, if_pos h]
      push_cast
      ring
    · rw [if_neg h, if_neg h]
      simp
  rw [step1, step2]

/-- The density interaction is a genuine quartic Wick polynomial: it
equals the normal-ordered quartic with creation/annihilation operators
in the order `a†ᵢ aᵢ a†ⱼ aⱼ`. -/
theorem densityIntBos_eq_quartic (U : Fin d → Fin d → ℝ) :
    densityIntBos d U
      = ∑ i, ∑ j, (if i < j then (U i j : ℂ) else 0) •
          ((adagBos d i) ∘ₗ ((annBos d i) ∘ₗ ((adagBos d j) ∘ₗ (annBos d j)))) := by
  unfold densityIntBos numModeBos
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [LinearMap.comp_assoc]

/-- The density interaction is symmetric on `Dom d`. -/
theorem densityIntBos_isSymmetric (U : Fin d → Fin d → ℝ) (x y : Dom d) :
    ⟪((densityIntBos d U x : Dom d) : BosonicFock d), (y : BosonicFock d)⟫_ℂ
      = ⟪(x : BosonicFock d), ((densityIntBos d U y : Dom d) :
          BosonicFock d)⟫_ℂ :=
  diagOpBos_isSymmetric d (densityIntBos_basis d U) x y

/-- The free eigenvalue of a configuration. -/
noncomputable def freeEigBos (lam : Fin d → ℝ) (c : Config d) : ℝ :=
  ∑ i, lam i * (c i : ℝ)

/-- The eigenvalue of the diagonal interacting Hamiltonian on a
configuration: free part plus coupling times density part. -/
noncomputable def densHamEigBos (lam : Fin d → ℝ) (U : Fin d → Fin d → ℝ)
    (g : ℝ) (c : Config d) : ℝ :=
  freeEigBos d lam c + g * densEigBos d U c

/-- The diagonal interacting Hamiltonian: free Hamiltonian plus the
density interaction. Diagonal in the configuration basis, hence the one
bosonic interacting Hamiltonian whose gap is exact and uniform. -/
noncomputable def hamiltonianDensBos (lam : Fin d → ℝ)
    (U : Fin d → Fin d → ℝ) (g : ℝ) : Module.End ℂ (Dom d) :=
  freeHamiltonianBos d lam + (g : ℂ) • densityIntBos d U

theorem hamiltonianDensBos_basis (lam : Fin d → ℝ) (U : Fin d → Fin d → ℝ)
    (g : ℝ) (c : Config d) :
    hamiltonianDensBos d lam U g
        ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = (densHamEigBos d lam U g c : ℂ) • ⟨boseE d c,
          Submodule.subset_span (Set.mem_range_self c)⟩ := by
  have hfree : freeHamiltonianBos d lam
        ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = (freeEigBos d lam c : ℂ) • ⟨boseE d c,
          Submodule.subset_span (Set.mem_range_self c)⟩ :=
    freeHamiltonianBos_basis d lam c
  rw [hamiltonianDensBos, LinearMap.add_apply, hfree, LinearMap.smul_apply,
    densityIntBos_basis, smul_smul, ← add_smul]
  congr 1
  rw [densHamEigBos]
  push_cast
  ring

/-- The density Hamiltonian is symmetric on `Dom d`. -/
theorem hamiltonianDensBos_isSymmetric (lam : Fin d → ℝ)
    (U : Fin d → Fin d → ℝ) (g : ℝ) (x y : Dom d) :
    ⟪((hamiltonianDensBos d lam U g x : Dom d) : BosonicFock d),
        (y : BosonicFock d)⟫_ℂ
      = ⟪(x : BosonicFock d), ((hamiltonianDensBos d lam U g y : Dom d) :
          BosonicFock d)⟫_ℂ :=
  diagOpBos_isSymmetric d (hamiltonianDensBos_basis d lam U g) x y

/-- At zero coupling the density Hamiltonian is the free Hamiltonian. -/
theorem hamiltonianDensBos_zero (lam : Fin d → ℝ) (U : Fin d → Fin d → ℝ) :
    hamiltonianDensBos d lam U 0 = freeHamiltonianBos d lam := by
  simp [hamiltonianDensBos]

/-- With nonnegative density coupling and nonnegative coupling constant,
the density eigenvalue is nonnegative term by term. -/
theorem densEigBos_nonneg {U : Fin d → Fin d → ℝ}
    (hU : ∀ i j, 0 ≤ U i j) (c : Config d) : 0 ≤ densEigBos d U c := by
  rw [densEigBos]
  refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ?_))
  by_cases h : i < j
  · rw [if_pos h]
    exact mul_nonneg (mul_nonneg (hU i j) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  · rw [if_neg h]

/-- Under nonnegative coupling the interaction only raises eigenvalues. -/
theorem densHamEigBos_ge_freeEigBos {lam : Fin d → ℝ}
    {U : Fin d → Fin d → ℝ} (hg : 0 ≤ g) (hU : ∀ i j, 0 ≤ U i j)
    (c : Config d) :
    freeEigBos d lam c ≤ densHamEigBos d lam U g c := by
  rw [densHamEigBos]
  have := densEigBos_nonneg d hU c
  linarith [mul_nonneg hg this]

/-- With nonnegative one-particle energies the free eigenvalue of every
configuration is nonnegative. -/
theorem freeEigBos_nonneg {lam : Fin d → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (c : Config d) : 0 ≤ freeEigBos d lam c := by
  rw [freeEigBos]
  exact Finset.sum_nonneg (fun i _ =>
    mul_nonneg (hlam i) (Nat.cast_nonneg _))

/-- **Eigenvalue form of the density Hamiltonian (B3(i), weak dichotomy).**
On the finite-particle domain, every eigenvalue of the density
Hamiltonian is a `densHamEigBos` value at some configuration, is `≥ 0`,
and dominates a free eigenvalue that is `0` or `≥ Δ`. -/
theorem hamiltonianDensBos_eigenvalue_form (lam : Fin d → ℝ)
    (U : Fin d → Fin d → ℝ) (g : ℝ) (Δ : ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hgap : ∀ i, lam i = 0 ∨ Δ ≤ lam i)
    (hg : 0 ≤ g) (hU : ∀ i j, 0 ≤ U i j)
    {ψ : Dom d} (hψ : ψ ≠ 0) {μ : ℂ}
    (hμ : hamiltonianDensBos d lam U g ψ = μ • ψ) :
    ∃ c, μ = (densHamEigBos d lam U g c : ℂ)
      ∧ 0 ≤ densHamEigBos d lam U g c
      ∧ (freeEigBos d lam c = 0 ∨ Δ ≤ freeEigBos d lam c) := by
  obtain ⟨c, hc⟩ := diagOpBos_eigenvalue d
    (hamiltonianDensBos_basis d lam U g) hψ hμ
  refine ⟨c, hc, ?_, free_gap_dichotomy_bos d lam Δ hlam hgap c⟩
  rw [densHamEigBos]
  exact add_nonneg (freeEigBos_nonneg d hlam c)
    (mul_nonneg hg (densEigBos_nonneg d hU c))

/-- **Exact gap for the density Hamiltonian (B3(i) headline).** Under the
strong dichotomy hypothesis (every one-particle energy is `≥ Δ > 0`:
no zero modes), nonnegative coupling and nonnegative density matrix,
every eigenvalue of the density Hamiltonian on the finite-particle
domain is either exactly `0` (the vacuum configuration) or `≥ Δ` —
an exact, uniform gap, the bosonic mirror of Campaign 1's exhibit
theorem. The hypothesis cannot be relaxed to the weak dichotomy:
two distinct zero modes `a < b` with `U a b > 0` give the eigenvalue
`g • U a b ∈ (0, Δ)` at the configuration with one particle in each —
recorded here, as in Campaign 1, as the reason the strong hypothesis
is stated. -/
theorem hamiltonianDensBos_gap_exact (lam : Fin d → ℝ)
    (U : Fin d → Fin d → ℝ) (g : ℝ) (Δ : ℝ) (hΔ : 0 < Δ)
    (hlam : ∀ i, Δ ≤ lam i) (hg : 0 ≤ g) (hU : ∀ i j, 0 ≤ U i j)
    {ψ : Dom d} (hψ : ψ ≠ 0) {μ : ℂ}
    (hμ : hamiltonianDensBos d lam U g ψ = μ • ψ) :
    ∃ c, μ = (densHamEigBos d lam U g c : ℂ)
      ∧ (densHamEigBos d lam U g c = 0 ∨ Δ ≤ densHamEigBos d lam U g c) := by
  obtain ⟨c, hc⟩ := diagOpBos_eigenvalue d
    (hamiltonianDensBos_basis d lam U g) hψ hμ
  refine ⟨c, hc, ?_⟩
  by_cases hc0 : c = 0
  · left
    subst hc0
    rw [densHamEigBos, freeEigBos, densEigBos]
    simp
  · right
    obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hc0 (Finsupp.ext h)
    have hterm : lam i * (c i : ℝ) ≤ freeEigBos d lam c := by
      rw [freeEigBos]
      refine Finset.single_le_sum (f := fun j => lam j * (c j : ℝ))
        (s := Finset.univ) (fun j _ => ?_) (Finset.mem_univ i)
      exact mul_nonneg (le_trans (le_of_lt hΔ) (hlam j)) (Nat.cast_nonneg _)
    have hci : (1 : ℝ) ≤ (c i : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hi
    have hge : freeEigBos d lam c ≤ densHamEigBos d lam U g c :=
      densHamEigBos_ge_freeEigBos d hg hU c
    have hstep : Δ * (1 : ℝ) ≤ lam i * (c i : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_left hci (le_of_lt hΔ))
        (mul_le_mul_of_nonneg_right (hlam i) (Nat.cast_nonneg _))
    refine le_trans ?_ (le_trans hterm hge)
    calc Δ = Δ * 1 := (mul_one Δ).symm
      _ ≤ lam i * (c i : ℝ) := hstep

/-- The diagonal coefficient of a one-particle lift `dΓ(M)` on a basis
vector: only the diagonal entries of `M` contribute, weighted by the
occupations. The computational heart of the not-a-dΓ certificate. -/
theorem dgammaC_diag_coeff (M : Matrix (Fin d) (Fin d) ℂ) (γ : Config d)
    (a : ℂ) :
    (dgammaC d M (Finsupp.single γ a)) γ
      = a * ∑ i, M i i * (γ i : ℂ) := by
  have hterm : ∀ i j : Fin d,
      (((adagC d i) ∘ₗ (annC d j)) (Finsupp.single γ a)) γ
        = if i = j then a * (γ i : ℂ) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      by_cases hγ : γ i = 0
      · rw [if_pos rfl]
        simp only [LinearMap.comp_apply, annC_single, if_pos hγ, map_zero,
          Finsupp.zero_apply]
        rw [hγ]
        simp
      · have e1 : annC d i (Finsupp.single γ a)
            = (a * sqrtNat (γ i)) • Finsupp.single (γ - Finsupp.single i 1) 1 := by
          rw [annC_single, if_neg hγ]
        have e2 : adagC d i ((a * sqrtNat (γ i)) •
              Finsupp.single (γ - Finsupp.single i 1) 1)
            = (a * ((γ i : ℂ))) • Finsupp.single γ 1 := by
          rw [single_smul_one, adagC_single,
            config_sub_single_add_single d γ i hγ,
            config_sub_single_apply_self γ i hγ, mul_assoc, sqrtNat_mul_self]
        rw [LinearMap.comp_apply, e1, e2, Finsupp.smul_apply,
          Finsupp.single_apply, if_pos rfl, smul_eq_mul, mul_one, if_pos rfl]
    · by_cases hγ : γ j = 0
      · have hz : annC d j (Finsupp.single γ a) = 0 := by
          rw [annC_single, if_pos hγ]
        rw [LinearMap.comp_apply, hz, map_zero, Finsupp.zero_apply, if_neg hij]
      · have e1 : annC d j (Finsupp.single γ a)
            = (a * sqrtNat (γ j)) • Finsupp.single (γ - Finsupp.single j 1) 1 := by
          rw [annC_single, if_neg hγ]
        have hne : (γ - Finsupp.single j 1) + Finsupp.single i 1 ≠ γ := by
          intro hcon
          have hval := congrFun (congrArg DFunLike.coe hcon) i
          rw [Finsupp.add_apply, Finsupp.single_apply, if_pos rfl,
            config_sub_single_apply_ne γ j i (Ne.symm hij)] at hval
          exact Nat.succ_ne_self (γ i) hval
        rw [LinearMap.comp_apply, e1]
        simp only [single_smul_one, adagC_single, Finsupp.smul_apply,
          Finsupp.single_apply, if_neg hne, smul_eq_mul, mul_zero]
        exact (if_neg hij).symm
  have hexpand : (dgammaC d M (Finsupp.single γ a)) γ
      = ∑ i, ∑ j, M i j * (((adagC d i) ∘ₗ (annC d j))
          (Finsupp.single γ a)) γ := by
    rw [dgammaC, LinearMap.sum_apply, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [LinearMap.sum_apply, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [hexpand]
  have hdiag : ∀ i : Fin d, (∑ j, M i j * (((adagC d i) ∘ₗ (annC d j))
        (Finsupp.single γ a)) γ) = M i i * (a * (γ i : ℂ)) := by
    intro i
    rw [Finset.sum_eq_single i (fun j _ hj => ?_)
      (fun h => absurd (Finset.mem_univ i) h)]
    · rw [hterm i i, if_pos rfl]
    · rw [hterm i j, if_neg (Ne.symm hj), mul_zero]
  rw [Finset.sum_congr rfl (fun i _ => hdiag i), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- Evaluation of the density eigenvalue at the one-particle
configurations: it vanishes (a single particle has no pair). -/
theorem densEigBos_single (U : Fin d → Fin d → ℝ) (a : Fin d) :
    densEigBos d U (Finsupp.single a 1) = 0 := by
  have hc : ∀ k : Fin d, ((Finsupp.single a 1 : Config d) k : ℝ)
      = if k = a then 1 else 0 := by
    intro k
    by_cases hk : k = a
    · subst k
      simp
    · rw [Finsupp.single_apply]
      simp only [if_neg hk, if_neg (Ne.symm hk), Nat.cast_zero]
  rw [densEigBos]
  refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
  rw [hc i, hc j]
  by_cases hij : i < j
  · rw [if_pos hij]
    by_cases hi : i = a
    · rw [if_pos hi]
      have hja : ¬ j = a := by
        rintro rfl
        rw [hi] at hij
        exact lt_irrefl _ hij
      rw [if_neg hja]
      simp
    · rw [if_neg hi]
      simp
  · rw [if_neg hij]

/-- Evaluation of the density eigenvalue at the two-particle
configuration `{a, b}` with `a < b`: exactly `U a b`. -/
theorem densEigBos_pair (U : Fin d → Fin d → ℝ) {a b : Fin d} (hab : a < b) :
    densEigBos d U (Finsupp.single a 1 + Finsupp.single b 1) = U a b := by
  have hne : a ≠ b := ne_of_lt hab
  have hca : ((Finsupp.single a 1 + Finsupp.single b 1 : Config d) a : ℝ)
      = 1 := by
    rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    simp [hne.symm]
  have hcb : ((Finsupp.single a 1 + Finsupp.single b 1 : Config d) b : ℝ)
      = 1 := by
    rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    simp [hne]
  have hcz : ∀ k : Fin d, k ≠ a → k ≠ b →
      ((Finsupp.single a 1 + Finsupp.single b 1 : Config d) k : ℝ) = 0 := by
    intro k hka hkb
    rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    simp [Ne.symm hka, Ne.symm hkb]
  have hterm : ∀ i j : Fin d,
      (if i < j then U i j
          * ((Finsupp.single a 1 + Finsupp.single b 1 : Config d) i : ℝ)
          * ((Finsupp.single a 1 + Finsupp.single b 1 : Config d) j : ℝ)
        else 0)
        = if (i = a ∧ j = b) then U a b else 0 := by
    intro i j
    by_cases hcase : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hcase
      rw [if_pos hab, hca, hcb, if_pos ⟨rfl, rfl⟩]
      simp
    · rw [if_neg hcase]
      by_cases hij : i < j
      · rw [if_pos hij]
        by_cases hi : i = a
        · subst i
          have hjb : j ≠ b := fun h => hcase ⟨rfl, h⟩
          have hja : j ≠ a := by
            intro h
            subst j
            exact lt_irrefl _ hij
          rw [hcz j hja hjb]
          simp
        · by_cases hib : i = b
          · subst i
            have hja : j ≠ a := by
              intro h
              subst j
              exact (not_lt.mpr (le_of_lt hab)) hij
            have hjb : j ≠ b := by
              intro h
              subst j
              exact lt_irrefl _ hij
            rw [hcz j hja hjb]
            simp
          · rw [hcz i hi hib]
            simp
      · rw [if_neg hij]
  rw [densEigBos]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
    (fun j _ => hterm i j))]
  refine (Finset.sum_eq_single a ?_ (fun h => absurd (Finset.mem_univ a) h)).trans ?_
  · intro i _ hi
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [if_neg (fun h => hi h.1)]
  · refine (Finset.sum_eq_single b ?_ (fun h => absurd (Finset.mem_univ b) h)).trans ?_
    · intro j _ hj
      rw [if_neg (fun h => hj h.2)]
    · rw [if_pos ⟨rfl, rfl⟩]

/-- The diagonal `dΓ` coefficient at the one-particle configurations:
exactly the corresponding diagonal entry of `M`. -/
theorem diagCoeff_single (M : Matrix (Fin d) (Fin d) ℂ) (a : Fin d) :
    ∑ i, M i i * ((Finsupp.single a 1 : Config d) i : ℂ) = M a a := by
  rw [Finset.sum_eq_single a (fun i _ hi => ?_) (fun h => absurd
    (Finset.mem_univ a) h)]
  · rw [Finsupp.single_apply]
    simp
  · rw [Finsupp.single_apply]
    simp [Ne.symm hi]

/-- The diagonal `dΓ` coefficient at the two-particle configuration:
the sum of the two diagonal entries (additivity — the property the
density interaction provably lacks). -/
theorem diagCoeff_pair (M : Matrix (Fin d) (Fin d) ℂ) {a b : Fin d}
    (hab : a ≠ b) :
    ∑ i, M i i * (((Finsupp.single a 1 + Finsupp.single b 1 :
      Config d) i) : ℂ) = M a a + M b b := by
  have hsub : ({a, b} : Finset (Fin d)) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_subset hsub (fun i _ hi => ?_)]
  · rw [Finset.sum_pair hab]
    congr 1
    · rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
      simp [hab.symm]
    · rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
      simp [hab]
  · rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    push_neg at hi
    rw [if_neg (fun h : a = i => hi.1 h.symm), if_neg (fun h : b = i => hi.2 h.symm)]
    simp

/-- **The density interaction is not a one-particle lift (B3
certificate).** If some pair coupling `U a b` (`a < b`) is nonzero, the
density interaction differs from `dΓ(M)` for every one-particle operator
`M`: a `dΓ` is additive over configurations (its diagonal coefficient
at `{a, b}` is the sum of those at `{a}` and `{b}`, both of which vanish
for the density eigenvalue), while the density eigenvalue at `{a, b}`
is `U a b ≠ 0`. The bosonic mirror of Campaign 1's
`densityInt_not_dgamma`. -/
theorem densityIntBos_not_dgamma (U : Fin d → Fin d → ℝ) {a b : Fin d}
    (hab : a < b) (hU : U a b ≠ 0) (M : Matrix (Fin d) (Fin d) ℂ) :
    densityIntBos d U ≠ dgammaBos d M := by
  intro hcon
  have key : ∀ c : Config d, (densEigBos d U c : ℂ)
      = ∑ i, M i i * (c i : ℂ) := by
    intro c
    have h1 : (boseRepr d (densityIntBos d U
          ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩)) c
        = (densEigBos d U c : ℂ) := by
      rw [densityIntBos_basis, map_smul, boseRepr_basis, Finsupp.smul_apply,
        Finsupp.single_apply, if_pos rfl, smul_eq_mul, mul_one]
    have h2 : (boseRepr d (dgammaBos d M
          ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩)) c
        = ∑ i, M i i * (c i : ℂ) := by
      rw [repr_dgammaBos, boseRepr_basis, dgammaC_diag_coeff, one_mul]
    rw [hcon] at h1
    exact h1.symm.trans h2
  have e1 := key (Finsupp.single a 1)
  have e2 := key (Finsupp.single b 1)
  have e3 := key (Finsupp.single a 1 + Finsupp.single b 1)
  rw [densEigBos_single] at e1 e2
  rw [densEigBos_pair d U hab] at e3
  rw [diagCoeff_single] at e1 e2
  rw [diagCoeff_pair d M (ne_of_lt hab)] at e3
  have hbb : M b b = 0 := by
    have := e2
    simp at this
    exact this.symm
  have haa : M a a = 0 := by
    have := e1
    simp at this
    exact this.symm
  rw [haa, hbb, add_zero] at e3
  have : (U a b : ℂ) = 0 := e3
  exact hU (Complex.ofReal_eq_zero.mp this)

/-- The free eigenvalue at the two-mode configuration with `n`
particles in each of two distinct modes: `(λ a + λ b) • n`. -/
theorem freeEigBos_pair (lam : Fin d → ℝ) {a b : Fin d} (hab : a ≠ b)
    (n : ℕ) :
    freeEigBos d lam (Finsupp.single a n + Finsupp.single b n)
      = (lam a + lam b) * (n : ℝ) := by
  have hsub : ({a, b} : Finset (Fin d)) ⊆ Finset.univ := Finset.subset_univ _
  have hval : ∀ k : Fin d,
      ((Finsupp.single a n + Finsupp.single b n : Config d) k : ℝ)
        = (if k = a then (n : ℝ) else 0) + (if k = b then (n : ℝ) else 0) := by
    intro k
    rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
      Nat.cast_add]
    congr 1
    · by_cases hka : k = a
      · rw [if_pos hka, if_pos hka.symm]
      · rw [if_neg hka, if_neg (fun h : a = k => hka h.symm), Nat.cast_zero]
    · by_cases hkb : k = b
      · rw [if_pos hkb, if_pos hkb.symm]
      · rw [if_neg hkb, if_neg (fun h : b = k => hkb h.symm), Nat.cast_zero]
  rw [freeEigBos, ← Finset.sum_subset hsub (fun i _ hi => ?_)]
  · rw [Finset.sum_pair hab, hval a, hval b, if_pos rfl, if_neg hab,
      if_neg hab.symm, if_pos rfl]
    ring
  · rw [hval i]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    push_neg at hi
    rw [if_neg hi.1, if_neg hi.2]
    simp

/-- The density eigenvalue of the attractive single-pair coupling
(`-1` at one pair `a < b`, zero elsewhere): exactly minus the product
of the two occupations — the quadratic term that defeats every linear
free gap at large occupation. -/
theorem densEigBos_neg_pair (c : Config d) {a b : Fin d} (hab : a < b) :
    densEigBos d (fun i j => if i = a ∧ j = b then (-1 : ℝ) else 0) c
      = -((c a : ℝ) * (c b : ℝ)) := by
  have hterm : ∀ i j : Fin d,
      (if i < j then (if i = a ∧ j = b then (-1 : ℝ) else 0)
          * (c i : ℝ) * (c j : ℝ) else 0)
        = if (i = a ∧ j = b) then -((c a : ℝ) * (c b : ℝ)) else 0 := by
    intro i j
    by_cases hcase : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hcase
      rw [if_pos hab, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩]
      ring
    · by_cases hij : i < j
      · rw [if_pos hij, if_neg hcase]
        simp [hcase]
      · rw [if_neg hij, if_neg hcase]
  rw [densEigBos]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
    (fun j _ => hterm i j))]
  refine (Finset.sum_eq_single a ?_ (fun h => absurd (Finset.mem_univ a) h)).trans ?_
  · intro i _ hi
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [if_neg (fun h => hi h.1)]
  · refine (Finset.sum_eq_single b ?_ (fun h => absurd (Finset.mem_univ b) h)).trans ?_
    · intro j _ hj
      rw [if_neg (fun h => hj h.2)]
    · rw [if_pos ⟨rfl, rfl⟩]

/-- **The proved refusal of uniform bosonic gap persistence (B3(iii)).**
For the density Hamiltonian with an attractive pair coupling (`g = 1`,
`U a b = -1` at one pair `a < b`), the eigenvalues are unbounded below:
at the configuration with `n` particles in each of the two modes the
eigenvalue is `(λ a + λ b) • n - n²`, which dives below every bound.
Hence no uniform persistence theorem for general bosonic quartic
interactions exists to be proved — the windowed form of §4 is the
strongest true statement, exactly as scoped. -/
theorem densHamEigBos_unbounded_below (lam : Fin d → ℝ) {a b : Fin d}
    (hab : a < b) (B : ℝ) :
    ∃ c : Config d, densHamEigBos d lam
      (fun i j => if i = a ∧ j = b then (-1 : ℝ) else 0) 1 c < B := by
  obtain ⟨n, hn⟩ := exists_nat_gt (|lam a + lam b| + |B| + 1)
  refine ⟨Finsupp.single a n + Finsupp.single b n, ?_⟩
  have hfree := freeEigBos_pair d lam (ne_of_lt hab) n
  have heig := densEigBos_neg_pair d
    (Finsupp.single a n + Finsupp.single b n) hab
  have hca : ((Finsupp.single a n + Finsupp.single b n : Config d) a : ℝ)
      = (n : ℝ) := by
    rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    simp [(ne_of_lt hab).symm]
  have hcb : ((Finsupp.single a n + Finsupp.single b n : Config d) b : ℝ)
      = (n : ℝ) := by
    rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    simp [ne_of_lt hab]
  rw [densHamEigBos, hfree, heig, hca, hcb]
  have hnpos : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hprod : (0 : ℝ)
      ≤ ((n : ℝ) - (|lam a + lam b| + |B| + 1)) * (n : ℝ) :=
    mul_nonneg (by linarith [hn]) hnpos
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have h1 := abs_nonneg (lam a + lam b)
    have h2 := abs_nonneg B
    linarith [hn]
  have hKn : (lam a + lam b) * (n : ℝ) ≤ |lam a + lam b| * (n : ℝ) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hnpos
  have hBn : |B| * (1 : ℝ) ≤ |B| * (n : ℝ) :=
    mul_le_mul_of_nonneg_left hn1 (abs_nonneg _)
  have hB : B ≤ |B| := le_abs_self _
  have hstep1 : (lam a + lam b) * (n : ℝ) - (n : ℝ) * (n : ℝ)
      ≤ |lam a + lam b| * (n : ℝ) - (n : ℝ) * (n : ℝ) :=
    sub_le_sub_right hKn _
  have hstep2 : (|lam a + lam b| + |B| + 1) * (n : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
    have h := hprod
    ring_nf at h ⊢
    linarith [h]
  have hstep3 : (|B| + 1) * (n : ℝ) ≤ (n : ℝ) * (n : ℝ)
      - |lam a + lam b| * (n : ℝ) := by
    have h := hstep2
    ring_nf at h ⊢
    linarith [h]
  have hstep4 : |B| + 1 ≤ (n : ℝ) * (n : ℝ)
      - |lam a + lam b| * (n : ℝ) - (lam a + lam b) * (n : ℝ)
      + (lam a + lam b) * (n : ℝ) := by
    have h1 := hstep3
    have h2 : |B| + 1 ≤ (|B| + 1) * (n : ℝ) := by
      have hBn' : |B| * (1 : ℝ) ≤ |B| * (n : ℝ) := hBn
      have hn1' : (1 : ℝ) ≤ (n : ℝ) := hn1
      nlinarith [hBn', hn1', abs_nonneg B]
    linarith [h1, h2]
  have hgoal : (lam a + lam b) * (n : ℝ) + 1 * -((n : ℝ) * (n : ℝ)) < B := by
    have h6 : |B| + 1 ≤ (n : ℝ) * (n : ℝ) - (lam a + lam b) * (n : ℝ) := by
      linarith [hstep4]
    have h7 : (lam a + lam b) * (n : ℝ) - (n : ℝ) * (n : ℝ)
        ≤ -(|B| + 1) := by
      have h := neg_le_neg h6
      rwa [neg_sub] at h
    have h8 : -(|B| + 1) < B := by
      have h9 : -|B| ≤ B := neg_abs_le B
      linarith [h9]
    have h9 : (lam a + lam b) * (n : ℝ) + 1 * -((n : ℝ) * (n : ℝ))
        = (lam a + lam b) * (n : ℝ) - (n : ℝ) * (n : ℝ) := by ring
    rw [h9]
    exact lt_of_le_of_lt h7 h8
  exact hgoal

-- ============================================================================
-- §4. B3(ii): windowed gap persistence for the general quartic interaction
-- ============================================================================

/-- A finitely supported coefficient function is the sum of its
single-configuration pieces over any finset covering its support. -/
theorem finsupp_eq_sum_single (f : Config d →₀ ℂ) (S : Finset (Config d))
    (hS : ∀ γ, f γ ≠ 0 → γ ∈ S) :
    f = ∑ γ ∈ S, (f γ) • Finsupp.single γ 1 := by
  ext δ
  rw [Finsupp.finsetSum_apply]
  by_cases hδ : δ ∈ S
  · rw [Finset.sum_eq_single δ (fun γ _ hγδ => ?_) (fun h => absurd hδ h)]
    · rw [Finsupp.smul_apply, Finsupp.single_apply, if_pos rfl, smul_eq_mul,
        mul_one]
    · rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg hγδ, smul_eq_mul,
        mul_zero]
  · have hz : f δ = 0 := by
      by_contra h
      exact hδ (hS δ h)
    rw [hz]
    refine (Finset.sum_eq_zero (fun γ _ => ?_)).symm
    by_cases hγδ : γ = δ
    · subst hγδ
      rw [hz]
      simp
    · rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg hγδ, smul_eq_mul,
        mul_zero]

/-- **Coordinate bound at a maximal configuration.** On the
`n`-particle sector, the interaction's coordinate at any configuration
is bounded by the interaction bound times the largest coordinate of the
vector: the maximal-coordinate (Gershgorin-type) step of the windowed
persistence proof, with the column-sum bound `intOpC_col_sum_le` doing
the work. -/
theorem intOpC_coord_le (W : Fin d → Fin d → Fin d → Fin d → ℂ)
    (n : ℕ) (f : Config d →₀ ℂ) (hf : ∀ γ, f γ ≠ 0 → tot γ = n)
    (c₀ γ₀ : Config d) (hγ₀ : tot γ₀ = n)
    (hmax : ∀ γ, tot γ = n → ‖f γ‖ ≤ ‖f γ₀‖) :
    ‖(intOpC d W f) c₀‖ ≤ intBoundBos d W * ((n : ℝ) + 2) ^ 2 * ‖f γ₀‖ := by
  have hexp : f = ∑ γ ∈ sectorFinset d n, (f γ) • Finsupp.single γ 1 :=
    finsupp_eq_sum_single d f (sectorFinset d n)
      (fun γ hγ => (finite_setOf_tot_eq d n).mem_toFinset.mpr (hf γ hγ))
  have hcoord : (intOpC d W f) c₀
      = ∑ γ ∈ sectorFinset d n,
        (f γ) * (intOpC d W (Finsupp.single γ 1)) c₀ := by
    conv_lhs => rw [hexp]
    rw [map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [hcoord]
  have hpt : ∀ γ ∈ sectorFinset d n,
      ‖f γ * (intOpC d W (Finsupp.single γ 1)) c₀‖
        ≤ ‖f γ₀‖ * ‖(intOpC d W (Finsupp.single γ 1)) c₀‖ := by
    intro γ hγ
    have hγn : tot γ = n := (finite_setOf_tot_eq d n).mem_toFinset.mp hγ
    refine (norm_mul_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hmax γ hγn) (norm_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum hpt).trans ?_
  calc (∑ γ ∈ sectorFinset d n,
        ‖f γ₀‖ * ‖(intOpC d W (Finsupp.single γ 1)) c₀‖)
      = ‖f γ₀‖ * (∑ γ ∈ sectorFinset d n,
          ‖(intOpC d W (Finsupp.single γ 1)) c₀‖) := by
          rw [Finset.mul_sum]
    _ = (∑ γ ∈ sectorFinset d n,
          ‖(intOpC d W (Finsupp.single γ 1)) c₀‖) * ‖f γ₀‖ := mul_comm _ _
    _ ≤ (intBoundBos d W * ((n : ℝ) + 2) ^ 2) * ‖f γ₀‖ :=
        mul_le_mul_of_nonneg_right (intOpC_col_sum_le d W n c₀)
          (norm_nonneg _)
    _ = intBoundBos d W * ((n : ℝ) + 2) ^ 2 * ‖f γ₀‖ := by ring

/-- The coordinate identity for the full interacting Hamiltonian:
free eigenvalue times coordinate, plus coupling times interaction
coordinate. -/
theorem hamIntBos_coord (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) (ψ : Dom d)
    (c : Config d) :
    (boseRepr d (hamIntBos d lam W g ψ)) c
      = ((freeEigBos d lam c : ℝ) : ℂ) * (boseRepr d ψ) c
        + (g : ℂ) * (intOpC d W (boseRepr d ψ)) c := by
  have e1 : boseRepr d (hamIntBos d lam W g ψ)
      = boseRepr d (freeHamiltonianBos d lam ψ)
        + (g : ℂ) • intOpC d W (boseRepr d ψ) := by
    rw [hamIntBos, LinearMap.add_apply, LinearMap.smul_apply, map_add,
      map_smul, repr_intOpBos]
  rw [e1, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    freeHamiltonianBos_coord]
  rfl

/-- Eigenvalues of the interacting Hamiltonian are real (from symmetry
on the domain). -/
theorem hamIntBos_eigenvalue_real (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) {ψ : Dom d}
    (hψ : ψ ≠ 0) {μ : ℂ} (hμ : hamIntBos d lam W g ψ = μ • ψ) :
    μ.im = 0 := by
  have hψ' : ((ψ : Dom d) : BosonicFock d) ≠ 0 :=
    fun h => hψ (Subtype.ext h)
  have hs : ⟪((ψ : Dom d) : BosonicFock d),
      ((ψ : Dom d) : BosonicFock d)⟫_ℂ ≠ 0 :=
    inner_self_ne_zero.mpr hψ'
  have hcoe : ∀ (r : ℂ) (z : Dom d),
      ((r • z : Dom d) : BosonicFock d) = r • ((z : Dom d) : BosonicFock d) :=
    fun r z => rfl
  have hsymm := hamIntBos_isSymmetric d lam W g ψ ψ
  rw [hμ, hcoe, inner_smul_left, inner_smul_right] at hsymm
  have hconj : (starRingEnd ℂ) μ = μ := by
    by_contra hne
    have hz : ((starRingEnd ℂ) μ - μ)
        * ⟪((ψ : Dom d) : BosonicFock d),
            ((ψ : Dom d) : BosonicFock d)⟫_ℂ = 0 := by
      rw [sub_mul, hsymm, sub_self]
    rcases mul_eq_zero.mp hz with h | h
    · exact hne (sub_eq_zero.mp h)
    · exact hs h
  rw [starRingEnd_apply, Complex.star_def] at hconj
  have h2 := congrArg Complex.im hconj
  rw [Complex.conj_im] at h2
  linarith

/-- **Eigenvalue transport into a sector window.** Every eigenvalue of
the interacting Hamiltonian with eigenvector in the `n`-particle sector
lies within `‖g‖ • intBoundBos W • (n+2)²` of the free eigenvalue of some
sector configuration where the eigenvector's coordinate is maximal.
The window `n` is explicit and unavoidable: the bound grows with the
sector, and §3(iii) shows no uniform version exists. -/
theorem hamIntBos_eigenvalue_transport_sector (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ)
    {n : ℕ} {ψ : Dom d} (hψsec : ψ ∈ domSector d n) (hψ : ψ ≠ 0) {μ : ℂ}
    (hμ : hamIntBos d lam W g ψ = μ • ψ) :
    ∃ c₀ : Config d, tot c₀ = n ∧ (boseRepr d ψ) c₀ ≠ 0 ∧
      ‖μ - ((freeEigBos d lam c₀ : ℝ) : ℂ)‖
        ≤ ‖(g : ℂ)‖ * (intBoundBos d W * ((n : ℝ) + 2) ^ 2) := by
  obtain ⟨c₀, hc₀n, hc₀ne, hc₀max⟩ : ∃ c₀, tot c₀ = n
      ∧ (boseRepr d ψ) c₀ ≠ 0
      ∧ ∀ γ, tot γ = n → ‖(boseRepr d ψ) γ‖ ≤ ‖(boseRepr d ψ) c₀‖ := by
    have hne : ∃ γ, tot γ = n ∧ (boseRepr d ψ) γ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hψ
      have hzero : boseRepr d ψ = 0 := by
        refine Finsupp.ext (fun γ => ?_)
        rw [Finsupp.zero_apply]
        by_cases hγ : tot γ = n
        · exact hcon γ hγ
        · exact boseRepr_apply_eq_zero_of_tot_ne d hψsec hγ
      exact (boseRepr d).injective (by rw [hzero, map_zero])
    obtain ⟨γ₀, hγ₀n, hγ₀ne⟩ := hne
    obtain ⟨c₀, hc₀mem, hc₀max⟩ := Finset.exists_max_image (sectorFinset d n)
      (fun γ => ‖(boseRepr d ψ) γ‖)
      ⟨γ₀, (finite_setOf_tot_eq d n).mem_toFinset.mpr hγ₀n⟩
    refine ⟨c₀, (finite_setOf_tot_eq d n).mem_toFinset.mp hc₀mem, ?_,
      fun γ hγ => hc₀max γ ((finite_setOf_tot_eq d n).mem_toFinset.mpr hγ)⟩
    have hle := hc₀max γ₀ ((finite_setOf_tot_eq d n).mem_toFinset.mpr hγ₀n)
    intro hzero
    rw [hzero, norm_zero] at hle
    exact hγ₀ne (norm_eq_zero.mp (le_antisymm hle (norm_nonneg _)))
  refine ⟨c₀, hc₀n, hc₀ne, ?_⟩
  have hcoordψ : (boseRepr d (hamIntBos d lam W g ψ)) c₀
      = μ * (boseRepr d ψ) c₀ := by
    rw [hμ, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hcoord := hamIntBos_coord d lam W g ψ c₀
  rw [hcoordψ] at hcoord
  have hdiff : (μ - ((freeEigBos d lam c₀ : ℝ) : ℂ)) * (boseRepr d ψ) c₀
      = (g : ℂ) * (intOpC d W (boseRepr d ψ)) c₀ := by
    linear_combination hcoord
  have hbound := intOpC_coord_le d W n (boseRepr d ψ)
    (fun γ hγ => by
      by_contra htot
      exact hγ (boseRepr_apply_eq_zero_of_tot_ne d hψsec htot)) c₀ c₀ hc₀n
    hc₀max
  have hnormeq : ‖(μ - ((freeEigBos d lam c₀ : ℝ) : ℂ))‖
        * ‖(boseRepr d ψ) c₀‖
      = ‖(g : ℂ) * (intOpC d W (boseRepr d ψ)) c₀‖ := by
    rw [← hdiff, norm_mul]
  have hle : ‖(μ - ((freeEigBos d lam c₀ : ℝ) : ℂ))‖
        * ‖(boseRepr d ψ) c₀‖
      ≤ (‖(g : ℂ)‖ * (intBoundBos d W * ((n : ℝ) + 2) ^ 2))
        * ‖(boseRepr d ψ) c₀‖ := by
    have h2 : ‖(g : ℂ)‖ * ‖(intOpC d W (boseRepr d ψ)) c₀‖
        ≤ ‖(g : ℂ)‖ * (intBoundBos d W * ((n : ℝ) + 2) ^ 2
            * ‖(boseRepr d ψ) c₀‖) :=
      mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    have h3 : ‖(g : ℂ)‖ * (intBoundBos d W * ((n : ℝ) + 2) ^ 2
          * ‖(boseRepr d ψ) c₀‖)
        = (‖(g : ℂ)‖ * (intBoundBos d W * ((n : ℝ) + 2) ^ 2))
          * ‖(boseRepr d ψ) c₀‖ := by ring
    rw [hnormeq, norm_mul]
    exact h3 ▸ h2
  have hpos : 0 < ‖(boseRepr d ψ) c₀‖ := norm_pos_iff.mpr hc₀ne
  exact le_of_mul_le_mul_right hle hpos

/-- **Windowed gap persistence for the general bosonic quartic
interaction (B3(ii) headline).** Fix a particle window `n`. If the
free one-particle energies are nonnegative and dichotomous (`0` or
`≥ Δ`) and the coupling is small at the scale of the window
(`2‖g‖ • intBoundBos W • (n+2)² ≤ Δ/4`), then every eigenvalue of the
interacting Hamiltonian with eigenvector in the `n`-particle sector is
either within the interaction bound of `0` or at least `Δ/2`: the free
gap persists *inside the window*. The window is in the statement
because it must be: for fixed nonzero coupling the threshold fails at
large `n`, and §3(iii) proves eigenvalues dive to `-∞` across sectors,
so no uniform-in-`n` persistence is available — or true. -/
theorem hamIntBos_gap_persistence_windowed (lam : Fin d → ℝ)
    (W : Fin d → Fin d → Fin d → Fin d → ℂ) (g : ℝ) (Δ : ℝ)
    (hΔ : 0 < Δ) (hlam : ∀ i, 0 ≤ lam i)
    (hgap : ∀ i, lam i = 0 ∨ Δ ≤ lam i) {n : ℕ}
    (hsmall : 2 * (‖(g : ℂ)‖ * (intBoundBos d W * ((n : ℝ) + 2) ^ 2)) ≤ Δ / 4)
    {ψ : Dom d} (hψsec : ψ ∈ domSector d n) (hψ : ψ ≠ 0) {μ : ℂ}
    (hμ : hamIntBos d lam W g ψ = μ • ψ) :
    μ.re ≤ ‖(g : ℂ)‖ * (intBoundBos d W * ((n : ℝ) + 2) ^ 2)
      ∨ Δ / 2 ≤ μ.re := by
  obtain ⟨c₀, -, -, htr⟩ := hamIntBos_eigenvalue_transport_sector d lam W g
    hψsec hψ hμ
  set ρ := ‖(g : ℂ)‖ * (intBoundBos d W * ((n : ℝ) + 2) ^ 2) with hρ
  have hμr : μ.im = 0 := hamIntBos_eigenvalue_real d lam W g hψ hμ
  have hfree : freeEigBos d lam c₀ = 0 ∨ Δ ≤ freeEigBos d lam c₀ :=
    free_gap_dichotomy_bos d lam Δ hlam hgap c₀
  have hre : |μ.re - freeEigBos d lam c₀| ≤ ρ := by
    have h := Complex.abs_re_le_norm (μ - ((freeEigBos d lam c₀ : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at h
    exact h.trans htr
  have hρle : ρ ≤ Δ / 8 := by linarith [hsmall]
  rcases hfree with he | hΔe
  · left
    rw [he] at hre
    exact le_trans (le_abs_self _) (by simpa using hre)
  · right
    have habs := abs_le.mp hre
    linarith

-- ============================================================================
-- §5. Axiom audit
-- ============================================================================

#print axioms hamIntBos_gap_persistence_windowed
#print axioms intOpBos_isSymmetric
#print axioms densityIntBos_not_dgamma
#print axioms hamIntBosSector_spectral
#print axioms hamiltonianDensBos_gap_exact
#print axioms hamPMap_le_adjoint
