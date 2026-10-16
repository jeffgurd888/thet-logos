import ThetLogos.BosonicFock

/-!
# Bosonic Assembly (Rung 8B)

Closes the bosonic PARTIAL of Rung 8. Starting point:
`ThetLogos.BosonicFock` (25 T1s): occupation basis `boseE`, dense domain
`Dom d`, creation/annihilation `adag`/`ann` as linear maps on `Dom d`,
basis actions, basis-level adjoint relation `adjoint_basis`, and the
double induction principle `Dom_induction₂`.

## What this module proves
- `adjoint_relation` — the full inner-product adjoint identity between
  `ann i` and `adag i` on all of `Dom d`, assembled from `adjoint_basis`
  by `Dom_induction₂` (the Rung 8 priced gap).
- CCR on `Dom d` (mixed commutator, ann/ann and adag/adag commutativity),
  transported from coefficient-space identities on `Config d →₀ ℂ`.
- `numberOp` — the number operator `∑ i, adag i ∘ₗ ann i` on `Dom d`,
  with basis eigenvalue the total occupation count, vacuum eigenvalue 0.
- Vacuum annihilation and sector orthogonality for distinct total
  occupation counts.

## Honesty labels
Finite mode set `Fin d`; operators are unbounded on the full Fock space
and are formalized on the dense finite-particle domain `Dom d`, the
standard honest formulation. This is the *free* bosonic theory. It is
not an interacting theory, not Yang–Mills, and not a Millennium claim.
Bosonic Γ(U) and the infinite-mode limit remain priced, unattempted here.
-/

namespace ThetLogos

open scoped InnerProductSpace

/-! ## 1. The full adjoint relation on `Dom d` -/

/-- **Rung 8B, target 1 (T1):** the full adjoint relation on the dense
domain. For all `x y : Dom d`,
`⟪ann i x, y⟫ = ⟪x, adag i y⟫` (inner products taken in `BosonicFock d`
via the coercion). Assembled from `adjoint_basis` by `Dom_induction₂`. -/
theorem adjoint_relation (d : ℕ) (i : Fin d) (x y : Dom d) :
    ⟪(((ann d i x) : Dom d) : BosonicFock d), (y : BosonicFock d)⟫_ℂ
      = ⟪(x : BosonicFock d), (((adag d i y) : Dom d) : BosonicFock d)⟫_ℂ := by
  refine Dom_induction₂ (P := fun x y =>
    ⟪(((ann d i x) : Dom d) : BosonicFock d), (y : BosonicFock d)⟫_ℂ
      = ⟪(x : BosonicFock d), (((adag d i y) : Dom d) : BosonicFock d)⟫_ℂ) d
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ x y
  · -- base: basis vectors — this is `adjoint_basis`
    intro c c'
    exact adjoint_basis d i c c'
  · -- additivity in the first argument
    intro x x' y hx hx'
    simp only [map_add, Submodule.coe_add, inner_add_left, hx, hx']
  · -- zero in the first argument
    intro y
    simp [map_zero]
  · -- scalar multiplication in the first argument
    intro a x y hx
    simp only [map_smul, Submodule.coe_smul, inner_smul_left, hx]
  · -- additivity in the second argument
    intro x y y' hy hy'
    simp only [map_add, Submodule.coe_add, inner_add_right, hy, hy']
  · -- zero in the second argument
    intro x
    simp [map_zero]
  · -- scalar multiplication in the second argument
    intro a x y hx
    simp only [map_smul, Submodule.coe_smul, inner_smul_right, hx]

/-- **T1:** the companion adjoint relation, with creation on the left:
`⟪adag i x, y⟫ = ⟪x, ann i y⟫` on `Dom d`. Follows from
`adjoint_relation` by conjugate symmetry of the inner product. -/
theorem adjoint_relation_adag (d : ℕ) (i : Fin d) (x y : Dom d) :
    ⟪(((adag d i x) : Dom d) : BosonicFock d), (y : BosonicFock d)⟫_ℂ
      = ⟪(x : BosonicFock d), (((ann d i y) : Dom d) : BosonicFock d)⟫_ℂ := by
  rw [← inner_conj_symm, ← adjoint_relation d i y x, inner_conj_symm]

/-! ## 2. CCR — coefficient-space identities -/

/-- A scalar multiple of the unit single is the single of the scalar. -/
theorem single_smul_one (c : Config d) (a : ℂ) :
    a • Finsupp.single c (1 : ℂ) = Finsupp.single c a := by
  ext k
  simp only [Finsupp.smul_apply, Finsupp.single_apply]
  by_cases h : c = k <;> simp [h, smul_eq_mul]

/-- Evaluating an added single at a different index. -/
theorem config_add_single_apply_ne (c : Config d) (i j : Fin d) (hij : j ≠ i) :
    (c + Finsupp.single j (1 : ℕ)) i = c i := by
  simp [Finsupp.add_apply, Finsupp.single_apply, hij]

/-- Evaluating an added single at its own index. -/
theorem config_add_single_apply_self (c : Config d) (i : Fin d) :
    (c + Finsupp.single i (1 : ℕ)) i = c i + 1 := by
  simp [Finsupp.add_apply, Finsupp.single_apply]

/-- Evaluating a subtracted single at a different index. -/
theorem config_sub_single_apply_ne (c : Config d) (i j : Fin d) (hij : i ≠ j) :
    (c - Finsupp.single i (1 : ℕ)) j = c j := by
  simp [Finsupp.tsub_apply, Finsupp.single_apply, hij]

/-- Evaluating a subtracted single at its own index, then adding one back. -/
theorem config_sub_single_apply_self (c : Config d) (i : Fin d) (h : c i ≠ 0) :
    (c - Finsupp.single i (1 : ℕ)) i + 1 = c i := by
  have h1 : 1 ≤ c i := Nat.one_le_iff_ne_zero.mpr h
  have h2 : (c - Finsupp.single i (1 : ℕ)) i = c i - 1 := by simp
  rw [h2]
  omega

/-- Subtracting singles at two indices commutes. -/
theorem config_sub_sub_comm (c : Config d) (i j : Fin d) :
    (c - Finsupp.single i (1 : ℕ)) - Finsupp.single j (1 : ℕ)
      = (c - Finsupp.single j (1 : ℕ)) - Finsupp.single i (1 : ℕ) := by
  ext k
  simp only [Finsupp.tsub_apply, Finsupp.single_apply]
  by_cases hi : i = k <;> by_cases hj : j = k <;> simp [hi, hj] <;> omega

/-- Adding singles at two indices commutes (as a total configuration). -/
theorem config_add_add_comm (c : Config d) (i j : Fin d) :
    (c + Finsupp.single i (1 : ℕ)) + Finsupp.single j (1 : ℕ)
      = (c + Finsupp.single j (1 : ℕ)) + Finsupp.single i (1 : ℕ) := by
  rw [add_assoc, add_comm (Finsupp.single i (1 : ℕ)) (Finsupp.single j (1 : ℕ)), ← add_assoc]

/-- **Coefficient CCR, mixed (T1):** on `Config d →₀ ℂ`,
`annC i ∘ adagC j - adagC j ∘ annC i = δ i j • id`. Checked on singles
via `Finsupp.lhom_ext`; the scalar content is `sqrtNat_mul_self`. -/
theorem ccr_coeff_mixed (d : ℕ) (i j : Fin d) :
    (annC d i) ∘ₗ (adagC d j) - (adagC d j) ∘ₗ (annC d i)
      = if i = j then (1 : Module.End ℂ (Config d →₀ ℂ)) else 0 := by
  apply Finsupp.lhom_ext
  intro c a
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, Module.End.one_apply]
    have term1 : annC d i (adagC d i (Finsupp.single c a))
        = (a * ((c i + 1 : ℕ) : ℂ)) • Finsupp.single c 1 := by
      rw [adagC_single, map_smul, annC_single, config_add_single_apply_self,
        if_neg (by omega : ¬ (c i + 1 = 0)), one_mul, smul_smul,
        config_add_single_sub_single, mul_assoc, sqrtNat_mul_self]
    have term2 : adagC d i (annC d i (Finsupp.single c a))
        = (a * (c i : ℂ)) • Finsupp.single c 1 := by
      by_cases hci : c i = 0
      · rw [annC_single, if_pos hci, map_zero, hci]
        simp
      · rw [annC_single, if_neg hci, map_smul, adagC_single,
          config_sub_single_apply_self _ _ hci, one_mul, smul_smul,
          mul_assoc, sqrtNat_mul_self, config_sub_single_add_single _ _ _ hci]
    rw [term1, term2, ← sub_smul]
    have hsc : a * ((c i + 1 : ℕ) : ℂ) - a * (c i : ℂ) = a := by push_cast; ring
    rw [hsc, single_smul_one]
  · rw [if_neg hij]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply]
    by_cases hci : c i = 0
    · have term1 : annC d i (adagC d j (Finsupp.single c a)) = 0 := by
        rw [adagC_single, map_smul, annC_single,
          config_add_single_apply_ne _ _ _ (Ne.symm hij), if_pos hci, smul_zero]
      have term2 : adagC d j (annC d i (Finsupp.single c a)) = 0 := by
        rw [annC_single, if_pos hci, map_zero]
      rw [term1, term2, sub_self]
    · have term1 : annC d i (adagC d j (Finsupp.single c a))
          = (a * sqrtNat (c j + 1) * sqrtNat (c i))
            • Finsupp.single ((c + Finsupp.single j 1) - Finsupp.single i 1) 1 := by
        rw [adagC_single, map_smul, annC_single,
          config_add_single_apply_ne _ _ _ (Ne.symm hij), if_neg hci, one_mul, smul_smul]
      have term2 : adagC d j (annC d i (Finsupp.single c a))
          = (a * sqrtNat (c i) * sqrtNat (c j + 1))
            • Finsupp.single ((c - Finsupp.single i 1) + Finsupp.single j 1) 1 := by
        rw [annC_single, if_neg hci, map_smul, adagC_single,
          config_sub_single_apply_ne _ _ _ hij, one_mul, smul_smul]
      rw [term1, term2, config_add_sub_comm _ _ _ _ hij,
        show a * sqrtNat (c j + 1) * sqrtNat (c i)
          = a * sqrtNat (c i) * sqrtNat (c j + 1) from by ring, sub_self]

/-- **Coefficient CCR, ann/ann (T1):** annihilation operators commute on
`Config d →₀ ℂ`. -/
theorem ccr_coeff_ann_ann (d : ℕ) (i j : Fin d) :
    (annC d i) ∘ₗ (annC d j) = (annC d j) ∘ₗ (annC d i) := by
  by_cases hij : i = j
  · subst hij; rfl
  apply Finsupp.lhom_ext
  intro c a
  simp only [LinearMap.comp_apply]
  by_cases hcj : c j = 0
  · rw [annC_single, if_pos hcj, map_zero]
    by_cases hci : c i = 0
    · rw [annC_single, if_pos hci, map_zero]
    · rw [annC_single, if_neg hci, map_smul, annC_single,
        config_sub_single_apply_ne _ _ _ hij, if_pos hcj, smul_zero]
  · by_cases hci : c i = 0
    · rw [annC_single, if_neg hcj, map_smul, annC_single,
        config_sub_single_apply_ne _ _ _ (Ne.symm hij), if_pos hci, smul_zero,
        annC_single, if_pos hci, map_zero]
    · rw [annC_single, if_neg hcj, map_smul, annC_single,
        config_sub_single_apply_ne _ _ _ (Ne.symm hij), if_neg hci, one_mul, smul_smul,
        annC_single, if_neg hci, map_smul, annC_single,
        config_sub_single_apply_ne _ _ _ hij, if_neg hcj, one_mul, smul_smul,
        config_sub_sub_comm,
        show (a * sqrtNat (c j)) * sqrtNat (c i)
          = (a * sqrtNat (c i)) * sqrtNat (c j) from by ring]

/-- **Coefficient CCR, adag/adag (T1):** creation operators commute on
`Config d →₀ ℂ`. -/
theorem ccr_coeff_adag_adag (d : ℕ) (i j : Fin d) :
    (adagC d i) ∘ₗ (adagC d j) = (adagC d j) ∘ₗ (adagC d i) := by
  by_cases hij : i = j
  · subst hij; rfl
  apply Finsupp.lhom_ext
  intro c a
  simp only [LinearMap.comp_apply]
  rw [adagC_single, map_smul, adagC_single, config_add_single_apply_ne _ _ _ (Ne.symm hij),
    one_mul, smul_smul,
    adagC_single, map_smul, adagC_single, config_add_single_apply_ne _ _ _ hij,
    one_mul, smul_smul, config_add_add_comm,
    show (a * sqrtNat (c j + 1)) * sqrtNat (c i + 1)
      = (a * sqrtNat (c i + 1)) * sqrtNat (c j + 1) from by ring]

/-! ## 3. CCR on `Dom d` (transported from coefficient space) -/

/-- Transport of a composite `ann ∘ adag` through `boseRepr`. -/
theorem repr_ann_adag (d : ℕ) (i j : Fin d) (x : Dom d) :
    boseRepr d (((ann d i) ∘ₗ (adag d j)) x)
      = ((annC d i) ∘ₗ (adagC d j)) (boseRepr d x) := by
  simp only [LinearMap.comp_apply, ann_transport, adag_transport]

/-- Transport of a composite `adag ∘ ann` through `boseRepr`. -/
theorem repr_adag_ann (d : ℕ) (i j : Fin d) (x : Dom d) :
    boseRepr d (((adag d i) ∘ₗ (ann d j)) x)
      = ((adagC d i) ∘ₗ (annC d j)) (boseRepr d x) := by
  simp only [LinearMap.comp_apply, adag_transport, ann_transport]

/-- Transport of a composite `ann ∘ ann` through `boseRepr`. -/
theorem repr_ann_ann (d : ℕ) (i j : Fin d) (x : Dom d) :
    boseRepr d (((ann d i) ∘ₗ (ann d j)) x)
      = ((annC d i) ∘ₗ (annC d j)) (boseRepr d x) := by
  simp only [LinearMap.comp_apply, ann_transport]

/-- Transport of a composite `adag ∘ adag` through `boseRepr`. -/
theorem repr_adag_adag (d : ℕ) (i j : Fin d) (x : Dom d) :
    boseRepr d (((adag d i) ∘ₗ (adag d j)) x)
      = ((adagC d i) ∘ₗ (adagC d j)) (boseRepr d x) := by
  simp only [LinearMap.comp_apply, adag_transport]

/-- **CCR on `Dom d`, mixed (T1):**
`ann i ∘ₗ adag j - adag j ∘ₗ ann i = δ i j • id` as linear maps on the
dense domain. -/
theorem ccr_mixed (d : ℕ) (i j : Fin d) :
    (ann d i) ∘ₗ (adag d j) - (adag d j) ∘ₗ (ann d i)
      = if i = j then (1 : Module.End ℂ (Dom d)) else 0 := by
  refine Dom_ext_transport d ?_ ?_ (ccr_coeff_mixed d i j)
  · intro z
    simp only [LinearMap.sub_apply, map_sub, repr_ann_adag, repr_adag_ann]
  · intro z
    by_cases hij : i = j
    · subst hij
      simp only [if_true, Module.End.one_apply]
    · simp only [if_neg hij, LinearMap.zero_apply, map_zero]

/-- **CCR on `Dom d`, ann/ann (T1):** annihilation operators commute. -/
theorem ccr_ann_ann (d : ℕ) (i j : Fin d) :
    (ann d i) ∘ₗ (ann d j) = (ann d j) ∘ₗ (ann d i) := by
  refine Dom_ext_transport d ?_ ?_ (ccr_coeff_ann_ann d i j)
  · intro z
    simp only [LinearMap.comp_apply, ann_transport]
  · intro z
    simp only [LinearMap.comp_apply, ann_transport]

/-- **CCR on `Dom d`, adag/adag (T1):** creation operators commute. -/
theorem ccr_adag_adag (d : ℕ) (i j : Fin d) :
    (adag d i) ∘ₗ (adag d j) = (adag d j) ∘ₗ (adag d i) := by
  refine Dom_ext_transport d ?_ ?_ (ccr_coeff_adag_adag d i j)
  · intro z
    simp only [LinearMap.comp_apply, adag_transport]
  · intro z
    simp only [LinearMap.comp_apply, adag_transport]

/-- **CCR, pointwise mixed form (T1):** for every `x : Dom d`,
`ann i (adag j x) = adag j (ann i x) + (if i = j then x else 0)`. -/
theorem ccr_mixed_apply (d : ℕ) (i j : Fin d) (x : Dom d) :
    ann d i (adag d j x)
      = adag d j (ann d i x) + (if i = j then x else 0) := by
  have h := LinearMap.congr_fun (ccr_mixed d i j) x
  by_cases hij : i = j
  · subst hij
    simp only [if_pos rfl, LinearMap.sub_apply, LinearMap.comp_apply,
      Module.End.one_apply] at h
    rw [if_pos rfl]
    exact (eq_add_of_sub_eq h).trans (add_comm _ _)
  · simp only [if_neg hij, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.zero_apply] at h
    rw [if_neg hij, add_zero]
    exact sub_eq_zero.mp h

/-! ## 4. Number operator -/

/-- The number operator on the dense domain: `N = ∑ i, adag i ∘ₗ ann i`. -/
noncomputable def numberOp (d : ℕ) : Dom d →ₗ[ℂ] Dom d :=
  ∑ i, (adag d i) ∘ₗ (ann d i)

/-- One mode's contribution to `numberOp` on a basis vector, in
coefficient form: mode `i` contributes the scalar `c i`. -/
theorem repr_numberOp_mode (d : ℕ) (i : Fin d) (c : Config d) :
    boseRepr d (((adag d i) ∘ₗ (ann d i))
      ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩)
      = (c i : ℂ) • Finsupp.single c 1 := by
  rw [LinearMap.comp_apply, adag_transport, ann_basis]
  by_cases hci : c i = 0
  · rw [if_pos hci, map_zero]
    simp [hci]
  · rw [if_neg hci, map_smul, adagC_single, config_sub_single_apply_self _ _ hci,
      one_mul, smul_smul, sqrtNat_mul_self, config_sub_single_add_single _ _ _ hci]

/-- **Number operator eigenvalue (T1):** `numberOp` acts on the basis
vector `e_c` as multiplication by the total occupation count
`∑ i, c i`. -/
theorem numberOp_basis (d : ℕ) (c : Config d) :
    numberOp d ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = (∑ i, (c i : ℂ)) • ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩ := by
  apply (boseRepr d).injective
  rw [map_smul, boseRepr_basis]
  simp only [numberOp, LinearMap.sum_apply, map_sum, repr_numberOp_mode,
    Finset.sum_smul]

/-! ## 5. Vacuum and sectors -/

/-- The vacuum as an element of the dense domain. -/
noncomputable def vacDom (d : ℕ) : Dom d :=
  ⟨boseE d 0, Submodule.subset_span (Set.mem_range_self (0 : Config d))⟩

/-- **Vacuum annihilation (T1):** `ann i` kills the vacuum. -/
theorem ann_vacuum (d : ℕ) (i : Fin d) : ann d i (vacDom d) = 0 := by
  apply (boseRepr d).injective
  rw [map_zero]
  show boseRepr d (ann d i ⟨boseE d 0, Submodule.subset_span
    (Set.mem_range_self (0 : Config d))⟩) = 0
  rw [ann_basis]
  simp

/-- **Vacuum eigenvalue (T1):** the number operator kills the vacuum
(eigenvalue `0 = ∑ i, (0 : Config d) i`). -/
theorem numberOp_vacuum (d : ℕ) : numberOp d (vacDom d) = 0 := by
  show numberOp d ⟨boseE d 0, Submodule.subset_span
    (Set.mem_range_self (0 : Config d))⟩ = 0
  rw [numberOp_basis]
  simp

/-- Total occupation count of a configuration. -/
def tot (c : Config d) : ℕ := ∑ i, c i

/-- The `n`-particle sector: span (in `BosonicFock d`) of the basis
vectors whose total occupation count is `n`. -/
noncomputable def sectorSub (d : ℕ) (n : ℕ) : Submodule ℂ (BosonicFock d) :=
  Submodule.span ℂ (boseE d '' {c | tot c = n})

/-- **Sector orthogonality (T1):** sectors of distinct total occupation
counts are orthogonal. Immediate from `boseE_inner`: distinct totals
force distinct configurations. -/
theorem sector_orthogonal (d : ℕ) {n n' : ℕ} (h : n ≠ n')
    (x y : BosonicFock d) (hx : x ∈ sectorSub d n) (hy : y ∈ sectorSub d n') :
    ⟪x, y⟫_ℂ = 0 := by
  refine Submodule.span_induction₂ (s := boseE d '' {c | tot c = n})
    (t := boseE d '' {c | tot c = n'}) (p := fun u v _ _ => ⟪u, v⟫_ℂ = 0)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro u v ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    have hcc : c ≠ c' := by
      intro heq
      subst heq
      exact h (hc.symm.trans hc')
    rw [boseE_inner, if_neg hcc]
  · intro v _
    exact inner_zero_left v
  · intro u _
    exact inner_zero_right u
  · intro u u' v _ _ _ hu hu'
    rw [inner_add_left, hu, hu', add_zero]
  · intro u v v' _ _ _ hv hv'
    rw [inner_add_right, hv, hv', add_zero]
  · intro r u v _ _ hu
    rw [inner_smul_left, hu, mul_zero]
  · intro r u v _ _ hv
    rw [inner_smul_right, hv, mul_zero]

/-! ## 6. Vacuum cyclicity (stretch) -/

/-- `sqrtNat` is nonzero at a positive occupation number. -/
theorem sqrtNat_ne_zero {n : ℕ} (hn : n ≠ 0) : sqrtNat n ≠ 0 := by
  rw [sqrtNat, Ne, Complex.ofReal_eq_zero, Real.sqrt_eq_zero (Nat.cast_nonneg n),
    Nat.cast_eq_zero]
  exact hn

/-- The number operator's one-mode eigenvalue computation, at the level
of `Dom d` (not just coefficients): `adag i` raises the configuration
`c` to `c + δi` with scalar `sqrtNat (c i + 1)`. -/
theorem adag_basis_dom (d : ℕ) (i : Fin d) (c : Config d) :
    adag d i ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = sqrtNat (c i + 1) • ⟨boseE d (c + Finsupp.single i 1),
          Submodule.subset_span (Set.mem_range_self _)⟩ := by
  apply (boseRepr d).injective
  rw [map_smul, adag_transport, boseRepr_basis, boseRepr_basis, adagC_single, one_mul]

/-- Applying a list of creation operators to the vacuum, in list order. -/
noncomputable def applyList (d : ℕ) : List (Fin d) → Dom d
  | [] => vacDom d
  | i :: l => adag d i (applyList d l)

/-- The cyclic submodule: the span of everything reachable from the
vacuum by finitely many creation operators. -/
noncomputable def cycSub (d : ℕ) : Submodule ℂ (Dom d) :=
  Submodule.span ℂ (Set.range (applyList d))

/-- The cyclic submodule is closed under every creation operator. -/
theorem adag_mem_cycSub (d : ℕ) (i : Fin d) {y : Dom d} (hy : y ∈ cycSub d) :
    adag d i y ∈ cycSub d := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, rfl⟩ := hz
      show adag d i (applyList d l) ∈ Submodule.span ℂ (Set.range (applyList d))
      exact Submodule.subset_span ⟨i :: l, rfl⟩
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add u v _ _ hu hv =>
      rw [map_add]
      exact add_mem hu hv
  | smul r u _ hu =>
      rw [map_smul]
      exact Submodule.smul_mem _ _ hu

/-- Adding one particle at mode `i` raises the total count by one. -/
theorem tot_add_single (c : Config d) (i : Fin d) :
    tot (c + Finsupp.single i (1 : ℕ)) = tot c + 1 := by
  have hsum : ∑ j, (Finsupp.single i (1 : ℕ)) j = 1 := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Finsupp.single_apply, show i ≠ j from fun hh => hji hh.symm]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  simp only [tot, Finsupp.add_apply, Finset.sum_add_distrib, hsum]

/-- Every basis vector lies in the cyclic submodule, by strong induction
on the total occupation count: peel one particle off with `ann`-inverse
reasoning — `e_c` is a nonzero scalar multiple of `adag i e_{c - δi}`. -/
theorem basis_mem_cycSub (d : ℕ) :
    ∀ (n : ℕ) (c : Config d), tot c = n →
      ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩ ∈ cycSub d := by
  intro n
  induction n with
  | zero =>
      intro c hc
      have hc0 : c = 0 := by
        have h2 := (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => Nat.zero_le (c i))).mp hc
        ext i
        rw [h2 i (Finset.mem_univ i)]
        rfl
      subst hc0
      show vacDom d ∈ Submodule.span ℂ (Set.range (applyList d))
      exact Submodule.subset_span ⟨[], rfl⟩
  | succ n ih =>
      intro c hc
      by_cases hall : ∀ i, c i = 0
      · have hc0 : c = 0 := by
          ext i
          rw [hall i]
          rfl
        subst hc0
        simp [tot] at hc
      · push_neg at hall
        obtain ⟨i, hi⟩ := hall
        have htot : tot c = tot (c - Finsupp.single i 1) + 1 := by
          conv_lhs => rw [← config_sub_single_add_single d c i hi]
          exact tot_add_single _ _
        have htot' : tot (c - Finsupp.single i 1) = n := by omega
        have had : adag d i ⟨boseE d (c - Finsupp.single i 1),
            Submodule.subset_span (Set.mem_range_self (c - Finsupp.single i 1))⟩
            ∈ cycSub d :=
          adag_mem_cycSub d i (ih _ htot')
        have hmul : adag d i ⟨boseE d (c - Finsupp.single i 1),
              Submodule.subset_span (Set.mem_range_self (c - Finsupp.single i 1))⟩
            = sqrtNat (c i) • ⟨boseE d c,
                Submodule.subset_span (Set.mem_range_self c)⟩ := by
          have h1 := adag_basis_dom d i (c - Finsupp.single i 1)
          rw [config_sub_single_apply_self _ _ hi,
            config_sub_single_add_single _ _ _ hi] at h1
          exact h1
        rw [hmul] at had
        have hne : sqrtNat (c i) ≠ 0 := sqrtNat_ne_zero hi
        have hinv : (⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩ : Dom d)
            = (sqrtNat (c i))⁻¹ • (sqrtNat (c i) • ⟨boseE d c,
                Submodule.subset_span (Set.mem_range_self c)⟩) := by
          rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
        rw [hinv]
        exact Submodule.smul_mem _ _ had

/-- **Vacuum cyclicity (T1, stretch):** the cyclic submodule generated
from the vacuum by the creation operators is all of `Dom d`. -/
theorem cycSub_eq_top (d : ℕ) : cycSub d = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have key : ∀ l : Config d →₀ ℂ, boseEquiv d l ∈ cycSub d := by
    intro l
    induction l using Finsupp.induction with
    | zero =>
        rw [map_zero]
        exact Submodule.zero_mem _
    | single_add a b f _ _ ihf =>
        rw [map_add]
        refine add_mem ?_ ihf
        have hb : boseEquiv d (Finsupp.single a b)
            = b • ⟨boseE d a, Submodule.subset_span (Set.mem_range_self a)⟩ := by
          rw [← single_smul_one a b, map_smul, boseEquiv_basis]
        rw [hb]
        exact Submodule.smul_mem _ _ (basis_mem_cycSub d (tot a) a rfl)
  have hx : boseEquiv d (boseRepr d x) = x :=
    LinearEquiv.apply_symm_apply (boseEquiv d) x
  rw [← hx]
  exact key _

end ThetLogos
