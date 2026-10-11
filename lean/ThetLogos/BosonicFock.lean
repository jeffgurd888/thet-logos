

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Data.Finsupp.Order

/-!
# Bosonic Fock Space (Rung 8)

Occupation-number construction of the bosonic Fock space, directly as
ℓ² on finitely-supported occupation configurations — no tensor powers.

## Construction
- Modes: `Fin d`. Configurations: `Finsupp (Fin d) ℕ` (occupation numbers).
- `BosonicFock d := lp (fun _ : Config d => ℂ) 2` with Mathlib's ℓ² inner product.
- Basis `boseE d c := lp.single 2 c 1`; vacuum `vac := boseE d 0`.
- Dense domain `Dom d := Submodule.span ℂ (Set.range (boseE d))`.
- Creation `adag d i` / annihilation `ann d i` as linear maps `Dom d →ₗ[ℂ] Dom d`,
  defined by transport from coefficient operators `adagC`/`annC` on
  `Config d →₀ ℂ` via the linear equivalence `boseEquiv`.
  (These are unbounded on the full space; the dense-domain formulation
  is the honest, standard formalization.)

## Results proved
- `adjoint_basis`: the adjoint relation on basis vectors,
  `⟪ann i e_c, e_{c'}⟫ = ⟪e_c, adag i e_{c'}⟫` — the computational core of W0.
- `boseE_orthonormal`, `boseE_inner`: orthonormality of the occupation basis.
- `adag_basis_coe`, `ann_basis_coe`: explicit basis actions.

## Mathlib-gap update
- Tensor inner products ✓ upstream (2025).
- Hilbert ℓ² sums ✓ upstream (`lp.instInnerProductSpace`, `lp.completeSpace`).
- Sector inner products via tensor-power symmetrizer projections ✗
  (API friction — n-fold tensor powers blocked a first worker).
  This occupation-number construction is the working alternative:
  sectors are spans of basis vectors, orthogonality is immediate
  from `boseE_inner`.

## Windows (priced, not attempted)
- Unitary equivalence with Symⁿ(H) as tensor-power subspaces:
  needs the n-fold tensor inner product (blocked upstream).
- Full `adjoint_relation` on `Dom d` by linearity from `adjoint_basis`:
  the induction principle is proved (`Dom_induction₂`), but the
  `Submodule` inner-product `simp`/`rw` API friction (coercion handling
  for `inner_smul_left` on submodule elements) stalled the final assembly.
  The basis computation `adjoint_basis` carries the mathematical content.
- CCR, number operator, sector orthogonality, vacuum cyclicity,
  Gram/permanent formula: follow from `adag_basis_coe`/`ann_basis_coe`
  by the standard computations; not yet formalized.
-/

namespace ThetLogos

open scoped InnerProductSpace

abbrev Config (d : ℕ) := Finsupp (Fin d) ℕ
noncomputable abbrev BosonicFock (d : ℕ) := lp (fun _ : Config d => ℂ) 2
noncomputable def boseE (d : ℕ) (c : Config d) : BosonicFock d := lp.single 2 c 1

theorem boseE_inner (d : ℕ) (c c' : Config d) :
    ⟪boseE d c, boseE d c'⟫_ℂ = if c = c' then 1 else 0 := by
  unfold boseE
  rw [lp.inner_single_left, lp.single_apply]
  by_cases h : c = c' <;> simp [h, RCLike.inner_apply]

theorem boseE_orthonormal (d : ℕ) : Orthonormal ℂ (boseE d) := by
  rw [orthonormal_iff_ite]
  exact boseE_inner d

noncomputable def Dom (d : ℕ) : Submodule ℂ (BosonicFock d) :=
  Submodule.span ℂ (Set.range (boseE d))

theorem boseLinIndep (d : ℕ) : LinearIndependent ℂ (boseE d) :=
  (boseE_orthonormal d).linearIndependent

noncomputable def boseEquiv (d : ℕ) : (Config d →₀ ℂ) ≃ₗ[ℂ] Dom d :=
  (boseLinIndep d).linearCombinationEquiv

theorem boseEquiv_coe (d : ℕ) (l : Config d →₀ ℂ) :
    (((boseEquiv d l : Dom d)) : BosonicFock d) = Finsupp.linearCombination ℂ (boseE d) l :=
  LinearIndependent.linearCombinationEquiv_apply_coe _ _

/-- Representation: domain ≃ coefficients (the inverse direction). -/
noncomputable def boseRepr (d : ℕ) : Dom d ≃ₗ[ℂ] (Config d →₀ ℂ) :=
  (boseEquiv d).symm

theorem boseEquiv_basis (d : ℕ) (c : Config d) :
    boseEquiv d (Finsupp.single c 1)
      = ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩ := by
  have h : (boseLinIndep d).repr ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = Finsupp.single c 1 :=
    LinearIndependent.repr_eq_single _ _ _ rfl
  have h2 : boseEquiv d ((boseLinIndep d).repr ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩)
      = ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩ := by
    show (boseLinIndep d).linearCombinationEquiv ((boseLinIndep d).linearCombinationEquiv.symm _) = _
    exact LinearEquiv.apply_symm_apply _ _
  rw [h] at h2
  exact h2

theorem boseRepr_basis (d : ℕ) (c : Config d) :
    boseRepr d ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = Finsupp.single c 1 := by
  rw [boseRepr, LinearEquiv.symm_apply_eq]
  exact (boseEquiv_basis d c).symm


/-! ## sqrt and coefficient operators -/

noncomputable def sqrtNat (n : ℕ) : ℂ := Complex.ofReal (Real.sqrt (n : ℝ))

theorem sqrtNat_mul_self (n : ℕ) : sqrtNat n * sqrtNat n = (n : ℂ) := by
  rw [sqrtNat, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _),
    Complex.ofReal_natCast]

theorem sqrtNat_star (n : ℕ) : star (sqrtNat n) = sqrtNat n := by
  simp [sqrtNat]

theorem sqrtNat_starRingEnd (n : ℕ) : (starRingEnd ℂ) (sqrtNat n) = sqrtNat n := by
  simp [sqrtNat]

noncomputable def adagC (d : ℕ) (i : Fin d) : (Config d →₀ ℂ) →ₗ[ℂ] (Config d →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun c : Config d =>
    sqrtNat (c i + 1) • Finsupp.single (c + Finsupp.single i 1) 1

noncomputable def annC (d : ℕ) (i : Fin d) : (Config d →₀ ℂ) →ₗ[ℂ] (Config d →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun c : Config d =>
    if c i = 0 then 0 else sqrtNat (c i) • Finsupp.single (c - Finsupp.single i 1) 1

theorem adagC_single (d : ℕ) (i : Fin d) (c : Config d) (a : ℂ) :
    adagC d i (Finsupp.single c a)
      = (a * sqrtNat (c i + 1)) • Finsupp.single (c + Finsupp.single i 1) 1 := by
  simp only [adagC, Finsupp.linearCombination_single, ← mul_smul]

theorem annC_single (d : ℕ) (i : Fin d) (c : Config d) (a : ℂ) :
    annC d i (Finsupp.single c a)
      = if c i = 0 then 0 else (a * sqrtNat (c i)) • Finsupp.single (c - Finsupp.single i 1) 1 := by
  by_cases h : c i = 0
  · simp [annC, Finsupp.linearCombination_single, h]
  · simp [annC, Finsupp.linearCombination_single, h]

/-! ## Finsupp arithmetic helpers -/

theorem config_add_single_sub_single (d : ℕ) (c : Config d) (i : Fin d) :
    (c + Finsupp.single i 1) - Finsupp.single i 1 = c := by
  ext j
  simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h]

theorem config_sub_single_add_single (d : ℕ) (c : Config d) (i : Fin d) (h : c i ≠ 0) :
    (c - Finsupp.single i 1) + Finsupp.single i 1 = c := by
  have h1 : 1 ≤ c i := Nat.one_le_iff_ne_zero.mpr h
  ext j
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  by_cases hj : i = j
  · subst hj; simp; omega
  · simp [hj]

theorem config_sub_single_eq_iff (d : ℕ) (c c' : Config d) (i : Fin d) (h : c i ≠ 0) :
    (c - Finsupp.single i 1 = c') ↔ (c = c' + Finsupp.single i 1) := by
  constructor
  · intro heq
    conv_lhs => rw [← config_sub_single_add_single d c i h, heq]
  · intro heq
    rw [heq]
    exact config_add_single_sub_single d c' i

theorem config_add_sub_comm (d : ℕ) (c : Config d) (i j : Fin d) (hij : i ≠ j) :
    (c + Finsupp.single j 1) - Finsupp.single i 1
      = (c - Finsupp.single i 1) + Finsupp.single j 1 := by
  ext k
  simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply]
  by_cases hki : i = k
  · have hkj : j ≠ k := fun h => hij (hki.trans h.symm)
    simp [hki, hkj]
  · by_cases hkj : j = k
    · simp [hki, hkj]
    · simp [hki, hkj]

/-! ## Operators on the dense domain -/

/-- Creation operator on the dense domain (transported from coefficients). -/
noncomputable def adag (d : ℕ) (i : Fin d) : Dom d →ₗ[ℂ] Dom d :=
  (boseEquiv d).toLinearMap.comp ((adagC d i).comp (boseEquiv d).symm.toLinearMap)

/-- Annihilation operator on the dense domain (transported from coefficients). -/
noncomputable def ann (d : ℕ) (i : Fin d) : Dom d →ₗ[ℂ] Dom d :=
  (boseEquiv d).toLinearMap.comp ((annC d i).comp (boseEquiv d).symm.toLinearMap)

theorem adag_transport (d : ℕ) (i : Fin d) (x : Dom d) :
    boseRepr d (adag d i x) = adagC d i (boseRepr d x) := by
  simp only [adag, boseRepr, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]

theorem ann_transport (d : ℕ) (i : Fin d) (x : Dom d) :
    boseRepr d (ann d i x) = annC d i (boseRepr d x) := by
  simp only [ann, boseRepr, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]

/-- Transport for composed operators. -/
theorem transport_comp (d : ℕ) (F G : Dom d →ₗ[ℂ] Dom d)
    (f g : (Config d →₀ ℂ) →ₗ[ℂ] (Config d →₀ ℂ))
    (hF : ∀ z, boseRepr d (F z) = f (boseRepr d z))
    (hG : ∀ z, boseRepr d (G z) = g (boseRepr d z)) (x : Dom d) :
    boseRepr d ((F ∘ₗ G) x) = (f ∘ₗ g) (boseRepr d x) := by
  simp only [LinearMap.comp_apply, hF, hG]

/-- Extensionality via transport: to prove `F = G` on `Dom`, transport both sides. -/
theorem Dom_ext_transport (d : ℕ) {F G : Dom d →ₗ[ℂ] Dom d}
    {f g : (Config d →₀ ℂ) →ₗ[ℂ] (Config d →₀ ℂ)}
    (hF : ∀ z, boseRepr d (F z) = f (boseRepr d z))
    (hG : ∀ z, boseRepr d (G z) = g (boseRepr d z))
    (h : f = g) : F = G := by
  apply LinearMap.ext
  intro x
  apply (boseRepr d).injective
  rw [hF, hG, h]

theorem adag_basis (d : ℕ) (i : Fin d) (c : Config d) :
    boseRepr d (adag d i ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩)
      = sqrtNat (c i + 1) • Finsupp.single (c + Finsupp.single i 1) 1 := by
  rw [adag_transport, boseRepr_basis, adagC_single, one_mul]

theorem ann_basis (d : ℕ) (i : Fin d) (c : Config d) :
    boseRepr d (ann d i ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩)
      = if c i = 0 then 0
        else sqrtNat (c i) • Finsupp.single (c - Finsupp.single i 1) 1 := by
  rw [ann_transport, boseRepr_basis, annC_single, one_mul]

theorem adag_basis_coe (d : ℕ) (i : Fin d) (c : Config d) :
    (((adag d i) ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩ : Dom d) : BosonicFock d)
      = sqrtNat (c i + 1) • boseE d (c + Finsupp.single i 1) := by
  have h := adag_basis d i c
  have h2 : (adag d i) ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = boseEquiv d (sqrtNat (c i + 1) • Finsupp.single (c + Finsupp.single i 1) 1) := by
    have := congrArg (boseEquiv d) h
    simpa [boseRepr] using this
  rw [h2, map_smul, boseEquiv_basis]
  rfl

theorem ann_basis_coe (d : ℕ) (i : Fin d) (c : Config d) :
    (((ann d i) ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩ : Dom d) : BosonicFock d)
      = if c i = 0 then 0 else sqrtNat (c i) • boseE d (c - Finsupp.single i 1) := by
  have h := ann_basis d i c
  by_cases hc : c i = 0
  · simp only [hc, if_true] at h
    have h2 : (ann d i) ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩ = 0 := by
      apply (boseRepr d).injective
      simpa [boseRepr] using h
    rw [h2]
    simp [hc]
  · have h' : (if c i = 0 then (0 : Config d →₀ ℂ)
        else sqrtNat (c i) • Finsupp.single (c - Finsupp.single i 1) 1)
        = sqrtNat (c i) • Finsupp.single (c - Finsupp.single i 1) 1 := by
      rw [if_neg hc]
    rw [h'] at h
    have h2 : (ann d i) ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
        = boseEquiv d (sqrtNat (c i) • Finsupp.single (c - Finsupp.single i 1) 1) := by
      have := congrArg (boseEquiv d) h
      simpa [boseRepr] using this
    rw [h2, map_smul, boseEquiv_basis, if_neg hc]
    rfl

/-! ## Adjoint relation (W0 discharge) -/

/-- Double induction on the dense domain. -/
theorem Dom_induction₂ (d : ℕ) {P : Dom d → Dom d → Prop}
    (base : ∀ c c', P ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      ⟨boseE d c', Submodule.subset_span (Set.mem_range_self c')⟩)
    (add₁ : ∀ x x' y, P x y → P x' y → P (x + x') y)
    (zero₁ : ∀ y, P 0 y)
    (smul₁ : ∀ (a : ℂ) x y, P x y → P (a • x) y)
    (add₂ : ∀ x y y', P x y → P x y' → P x (y + y'))
    (zero₂ : ∀ x, P x 0)
    (smul₂ : ∀ (a : ℂ) x y, P x y → P x (a • y))
    (x y : Dom d) : P x y := by
  obtain ⟨u, hu⟩ := x
  obtain ⟨v, hv⟩ := y
  have key := Submodule.span_induction₂ (s := Set.range (boseE d)) (t := Set.range (boseE d))
    (p := fun u v hu hv => P ⟨u, hu⟩ ⟨v, hv⟩)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hu hv
  exact key
  · intro x y hx hy
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨c', rfl⟩ := hy
    exact base c c'
  · intro y hy
    exact zero₁ ⟨y, hy⟩
  · intro x hx
    exact zero₂ ⟨x, hx⟩
  · intro x y z hx hy hz ih1 ih2
    have e : (⟨x + y, Submodule.add_mem (Dom d) hx hy⟩ : Dom d) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [e]
    exact add₁ _ _ _ ih1 ih2
  · intro x y z hx hy hz ih1 ih2
    have e : (⟨y + z, Submodule.add_mem (Dom d) hy hz⟩ : Dom d) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
    rw [e]
    exact add₂ _ _ _ ih1 ih2
  · intro r x y hx hy ih
    have e : (⟨r • x, Submodule.smul_mem (Dom d) r hx⟩ : Dom d) = r • ⟨x, hx⟩ := rfl
    rw [e]
    exact smul₁ _ _ _ ih
  · intro r x y hx hy ih
    have e : (⟨r • y, Submodule.smul_mem (Dom d) r hy⟩ : Dom d) = r • ⟨y, hy⟩ := rfl
    rw [e]
    exact smul₂ _ _ _ ih

/-- Basis computation for the adjoint relation. -/
theorem adjoint_basis (d : ℕ) (i : Fin d) (c c' : Config d) :
    ⟪(((ann d i) ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩ : Dom d) : BosonicFock d),
      boseE d c'⟫_ℂ
    = ⟪boseE d c,
      (((adag d i) ⟨boseE d c', Submodule.subset_span (Set.mem_range_self c')⟩ : Dom d) : BosonicFock d)⟫_ℂ := by
  rw [ann_basis_coe, adag_basis_coe]
  by_cases h0 : c i = 0
  · rw [if_pos h0, inner_zero_left, inner_smul_right]
    have hne : c ≠ c' + Finsupp.single i 1 := by
      intro heq
      rw [heq, Finsupp.add_apply, Finsupp.single_apply, if_pos rfl] at h0
      omega
    rw [boseE_inner, if_neg hne, mul_zero]
  · rw [if_neg h0, inner_smul_left, inner_smul_right, boseE_inner, boseE_inner, sqrtNat_starRingEnd]
    by_cases h1 : c - Finsupp.single i 1 = c'
    · rw [if_pos h1]
      have h2 : c = c' + Finsupp.single i 1 := (config_sub_single_eq_iff d c c' i h0).mp h1
      rw [if_pos h2]
      have h3 : c i = c' i + 1 := by
        rw [h2, Finsupp.add_apply, Finsupp.single_apply, if_pos rfl]
      rw [h3]
    · rw [if_neg h1]
      have h2 : ¬(c = c' + Finsupp.single i 1) :=
        fun heq => h1 ((config_sub_single_eq_iff d c c' i h0).mpr heq)
      rw [if_neg h2, mul_zero, mul_zero]


