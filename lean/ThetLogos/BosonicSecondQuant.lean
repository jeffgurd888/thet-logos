import ThetLogos.BosonicAssembly

/-!
# Bosonic Second Quantization (Rung 10) — the dΓ lift and the free gap

Starting point: Rung 8 (`ThetLogos.BosonicFock`) and Rung 8B
(`ThetLogos.BosonicAssembly`): occupation basis `boseE`, dense domain
`Dom d`, creation/annihilation `adag`/`ann` on `Dom d`, the full adjoint
relation, CCR, and `numberOp = ∑ i, adag i ∘ₗ ann i` with basis
eigenvalue the total occupation count.

This module mirrors Rung 9's fermionic `SecondQuantDGamma`:

## Task 1 — the bosonic dΓ lift
`dgammaBos M = ∑ i j, M i j • (adag i ∘ₗ ann j)` on `Dom d`, with
- `dgammaBos_adjoint` — `⟪dΓ(M) x, y⟫ = ⟪x, dΓ(Mᴴ) y⟫` on `Dom d`;
- `dgammaBos_one` — `dΓ(1) = numberOp`;
- `dgammaBos_vacuum` — `dΓ(M)` annihilates the vacuum;
- `dgammaBos_basis_diag` — `dΓ(diag λ) e_c = (∑ i, λ i · c i) • e_c`;
- sector preservation: `dgammaBos` preserves every `domSector d n`,
  and `domSector` coerces into the Fock-space sector `sectorSub d n`.

## Task 2 — the bosonic free Hamiltonian gap, DERIVED
For `H = dΓ(diag λ)` with real `λ i ≥ 0`:
- `freeHamiltonianBos_basis` — basis eigenvalue `∑ i, λ i · c i`;
- `freeHamiltonianBos_vacuum` — vacuum eigenvalue `0`;
- `freeHamiltonianBos_selfadjoint` — `H` self-adjoint (Dom inner form);
- `free_gap_dichotomy_bos` — every basis eigenvalue is `0` or `≥ Δ`
  whenever each `λ i = 0 ∨ Δ ≤ λ i`;
- `freeHamiltonianBos_eigenvalue_gap` — every operator eigenvalue of
  `H` on `Dom d` is `0` or `≥ Δ`;
- `freeHamiltonianBos_expectation` / `_nonneg` — the expectation
  formula and `H ≥ 0`.

**Honesty labels.** Finite mode set `Fin d`; operators live on the
dense finite-particle domain `Dom d`. This is the **free** bosonic
theory at **finite modes**. The gap above is *derived* for the free
Hamiltonian — it is **not** the interacting Yang–Mills mass gap, and
nothing here is a Millennium claim. Bosonic Γ(U) is the companion file
`ThetLogos.BosonicGamma`; the infinite-mode limit and the continuum
remain priced, unattempted.
-/

namespace ThetLogos

open scoped InnerProductSpace
open scoped Matrix

/-! ## 1. Basis actions at the level of `Dom d` -/

/-- The annihilation operator's action on a basis vector, at the level
of `Dom d` (companion to `adag_basis_dom` from Rung 8B). -/
theorem ann_basis_dom (d : ℕ) (i : Fin d) (c : Config d) :
    ann d i ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = if c i = 0 then 0
        else sqrtNat (c i) • ⟨boseE d (c - Finsupp.single i 1),
          Submodule.subset_span (Set.mem_range_self _)⟩ := by
  by_cases hc : c i = 0
  · rw [if_pos hc]
    apply (boseRepr d).injective
    simp [ann_transport, boseRepr_basis, annC_single, hc]
  · rw [if_neg hc]
    apply (boseRepr d).injective
    rw [map_smul, ann_transport, boseRepr_basis, boseRepr_basis, annC_single,
      if_neg hc, one_mul]

/-- One mode's number contribution at the level of `Dom d`:
`(adag i ∘ₗ ann i) e_c = (c i) • e_c`. -/
theorem numberOp_mode_dom (d : ℕ) (i : Fin d) (c : Config d) :
    ((adag d i) ∘ₗ (ann d i)) ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = (c i : ℂ) • ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩ := by
  apply (boseRepr d).injective
  rw [map_smul, boseRepr_basis]
  exact repr_numberOp_mode d i c

/-! ## 2. Task 1 — the bosonic dΓ lift -/

/-- **Rung 10, Task 1.** The bosonic dΓ lift of a one-particle matrix
`M`: `dΓ(M) = ∑ i j, M i j • (adag i ∘ₗ ann j)` on the dense domain
`Dom d`. -/
noncomputable def dgammaBos (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) :
    Module.End ℂ (Dom d) :=
  ∑ i : Fin d, ∑ j : Fin d, (M i j) • ((adag d i) ∘ₗ (ann d j))

/-- `dΓ(M)` annihilates the vacuum (T1). -/
theorem dgammaBos_vacuum (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) :
    dgammaBos d M (vacDom d) = 0 := by
  unfold dgammaBos
  rw [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  rw [LinearMap.smul_apply, LinearMap.comp_apply, ann_vacuum, map_zero, smul_zero]

/-- **The adjoint of `dΓ(M)` is `dΓ(Mᴴ)` (T1, inner-product form on
`Dom d`).** Mirrors the fermionic `dgamma_adjoint`, with the Rung 8B
adjoint relations in place of the finite-dimensional adjoints. -/
theorem dgammaBos_adjoint (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) (x y : Dom d) :
    ⟪(((dgammaBos d M x) : Dom d) : BosonicFock d), (y : BosonicFock d)⟫_ℂ
      = ⟪(x : BosonicFock d), (((dgammaBos d Mᴴ y) : Dom d) : BosonicFock d)⟫_ℂ := by
  have term : ∀ i j : Fin d,
      ⟪((((M i j) • ((adag d i) ∘ₗ (ann d j))) x : Dom d) : BosonicFock d),
          (y : BosonicFock d)⟫_ℂ
        = ⟪(x : BosonicFock d),
            ((((Mᴴ j i) • ((adag d j) ∘ₗ (ann d i))) y : Dom d) : BosonicFock d)⟫_ℂ := by
    intro i j
    rw [LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul,
      Submodule.coe_smul, inner_smul_left, inner_smul_right,
      LinearMap.comp_apply, LinearMap.comp_apply, adjoint_relation_adag,
      adjoint_relation, Matrix.conjTranspose_apply, starRingEnd_apply]
  simp only [dgammaBos, LinearMap.sum_apply, Submodule.coe_sum, inner_sum, sum_inner]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => term j i))

/-- **The number operator is `dΓ(1)` (T1).** -/
theorem dgammaBos_one (d : ℕ) :
    dgammaBos d (1 : Matrix (Fin d) (Fin d) ℂ) = numberOp d := by
  unfold dgammaBos numberOp
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine (Finset.sum_eq_single i (fun j _ hji => ?_)
    (fun hi => absurd (Finset.mem_univ i) hi)).trans ?_
  · rw [Matrix.one_apply_ne' hji, zero_smul]
  · rw [Matrix.one_apply_eq, one_smul]

/-- **Diagonal action of `dΓ` (T1):**
`dΓ(diag λ) e_c = (∑ i, λ i * (c i)) • e_c` — on the `n`-particle
sector, `dΓ` of a diagonal one-particle operator is the occupation-
weighted sum of its eigenvalues. -/
theorem dgammaBos_basis_diag (d : ℕ) (lam : Fin d → ℂ) (c : Config d) :
    dgammaBos d (Matrix.diagonal lam)
        ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = (∑ i, lam i * (c i : ℂ)) •
          ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩ := by
  have step : ∀ i : Fin d,
      ((∑ j : Fin d, ((Matrix.diagonal lam) i j) • ((adag d i) ∘ₗ (ann d j)))
          ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩)
        = lam i • (((adag d i) ∘ₗ (ann d i))
            ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩) := by
    intro i
    rw [LinearMap.sum_apply]
    refine (Finset.sum_eq_single i (fun j _ hji => ?_)
      (fun hi => absurd (Finset.mem_univ i) hi)).trans ?_
    · rw [LinearMap.smul_apply, Matrix.diagonal_apply_ne' _ hji, zero_smul]
    · rw [LinearMap.smul_apply, Matrix.diagonal_apply_eq]
  calc dgammaBos d (Matrix.diagonal lam)
          ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = ∑ i : Fin d, lam i • (((adag d i) ∘ₗ (ann d i))
          ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩) := by
        unfold dgammaBos
        rw [LinearMap.sum_apply]
        exact Finset.sum_congr rfl (fun i _ => step i)
    _ = ∑ i : Fin d, lam i • ((c i : ℂ) •
          ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩) :=
        Finset.sum_congr rfl (fun i _ => by rw [numberOp_mode_dom])
    _ = ∑ i : Fin d, (lam i * (c i : ℂ)) •
          ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩ :=
        Finset.sum_congr rfl (fun i _ => by rw [smul_smul])
    _ = (∑ i, lam i * (c i : ℂ)) •
          ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩ :=
        Finset.sum_smul.symm

/-! ## 3. Sector preservation -/

/-- The `n`-particle sector inside the dense domain: the span in
`Dom d` of the basis vectors of total occupation count `n`. -/
noncomputable def domSector (d : ℕ) (n : ℕ) : Submodule ℂ (Dom d) :=
  Submodule.span ℂ {x : Dom d | ∃ c : Config d, tot c = n ∧
    x = ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩}

/-- A dΓ monomial, at the level of `Dom d`: `adag i ∘ₗ ann j` sends
`e_c` to a scalar multiple of `e_{c - δj + δi}` (or to `0`). -/
theorem dgammaBos_term_dom (d : ℕ) (i j : Fin d) (c : Config d) :
    ((adag d i) ∘ₗ (ann d j)) ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = if c j = 0 then 0
        else (sqrtNat (c j) * sqrtNat ((c - Finsupp.single j 1 : Config d) i + 1)) •
          ⟨boseE d (c - Finsupp.single j 1 + Finsupp.single i 1),
            Submodule.subset_span (Set.mem_range_self _)⟩ := by
  rw [LinearMap.comp_apply, ann_basis_dom]
  by_cases hc : c j = 0
  · rw [if_pos hc, if_pos hc, map_zero]
  · rw [if_neg hc, if_neg hc, map_smul, adag_basis_dom, smul_smul]

/-- Every dΓ monomial term (with its matrix coefficient) maps a basis
vector into its own sector. -/
theorem dgammaBos_term_mem_domSector (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ)
    (i j : Fin d) (c : Config d) :
    (M i j) • (((adag d i) ∘ₗ (ann d j))
        ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩)
      ∈ domSector d (tot c) := by
  rw [dgammaBos_term_dom]
  by_cases hc : c j = 0
  · rw [if_pos hc, smul_zero]
    exact Submodule.zero_mem _
  · have h1 : tot (c - Finsupp.single j 1 + Finsupp.single i 1)
        = tot (c - Finsupp.single j 1) + 1 := tot_add_single _ _
    have h2 : tot c = tot (c - Finsupp.single j 1) + 1 := by
      conv_lhs => rw [← config_sub_single_add_single d c j hc]
      exact tot_add_single _ _
    rw [if_neg hc, smul_smul]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨c - Finsupp.single j 1 + Finsupp.single i 1, by omega, rfl⟩

/-- **`dΓ(M)` preserves every n-particle sector in `Dom d` (T1).** -/
theorem dgammaBos_mem_domSector (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) (n : ℕ)
    (x : Dom d) (hx : x ∈ domSector d n) :
    dgammaBos d M x ∈ domSector d n := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨c, hc, rfl⟩ := hz
      rw [← hc]
      unfold dgammaBos
      rw [LinearMap.sum_apply]
      apply Submodule.sum_mem
      intro i _
      rw [LinearMap.sum_apply]
      apply Submodule.sum_mem
      intro j _
      rw [LinearMap.smul_apply]
      exact dgammaBos_term_mem_domSector d M i j c
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add u v _ _ hu hv =>
      rw [map_add]
      exact add_mem hu hv
  | smul a u _ hu =>
      rw [map_smul]
      exact Submodule.smul_mem _ _ hu

/-- The domain sector coerces into the Fock-space sector of Rung 8B:
`x ∈ domSector d n → (x : BosonicFock d) ∈ sectorSub d n` (T1). -/
theorem domSector_coe (d : ℕ) (n : ℕ) (x : Dom d) (hx : x ∈ domSector d n) :
    ((x : Dom d) : BosonicFock d) ∈ sectorSub d n := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨c, hc, rfl⟩ := hz
      show boseE d c ∈ sectorSub d n
      apply Submodule.subset_span
      exact ⟨c, hc, rfl⟩
  | zero =>
      exact Submodule.zero_mem _
  | add u v _ _ hu hv =>
      rw [Submodule.coe_add]
      exact add_mem hu hv
  | smul a u _ hu =>
      rw [Submodule.coe_smul]
      exact Submodule.smul_mem _ _ hu

/-! ## 4. Task 2 — the bosonic free Hamiltonian gap

Everything in this section is the **free** bosonic theory at **finite
modes** (`Fin d`), on the dense domain `Dom d`. The gap is *derived*
for `H = dΓ(diag λ)` — it is not the interacting Yang–Mills gap. -/

/-- The coefficient-space dΓ lift (on `Config d →₀ ℂ`), the transport
of `dgammaBos` along `boseRepr`. -/
noncomputable def dgammaC (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) :
    (Config d →₀ ℂ) →ₗ[ℂ] (Config d →₀ ℂ) :=
  ∑ i : Fin d, ∑ j : Fin d, (M i j) • ((adagC d i) ∘ₗ (annC d j))

/-- `dgammaBos` transported to coefficient space is `dgammaC` (T1). -/
theorem repr_dgammaBos (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) (x : Dom d) :
    boseRepr d (dgammaBos d M x) = dgammaC d M (boseRepr d x) := by
  simp only [dgammaBos, dgammaC, LinearMap.sum_apply, map_sum, map_smul,
    LinearMap.smul_apply, repr_adag_ann]

/-- One coefficient-space number mode:
`(adagC i ∘ₗ annC i) (single c a) = (a * (c i)) • single c 1` (T1). -/
theorem dgammaC_number_mode (d : ℕ) (i : Fin d) (c : Config d) (a : ℂ) :
    ((adagC d i) ∘ₗ (annC d i)) (Finsupp.single c a)
      = (a * (c i : ℂ)) • Finsupp.single c 1 := by
  have h1 : ((adagC d i) ∘ₗ (annC d i)) (Finsupp.single c 1)
      = (c i : ℂ) • Finsupp.single c 1 := by
    have h := repr_numberOp_mode d i c
    rw [repr_adag_ann, boseRepr_basis] at h
    exact h
  calc ((adagC d i) ∘ₗ (annC d i)) (Finsupp.single c a)
      = ((adagC d i) ∘ₗ (annC d i)) (a • Finsupp.single c 1) := by
        rw [← single_smul_one]
    _ = a • ((adagC d i) ∘ₗ (annC d i)) (Finsupp.single c 1) := map_smul _ _ _
    _ = a • ((c i : ℂ) • Finsupp.single c 1) := by rw [h1]
    _ = (a * (c i : ℂ)) • Finsupp.single c 1 := smul_smul a _ _

/-- The coefficient-space diagonal action on a single basis
coefficient (T1). -/
theorem dgammaC_diag_single (d : ℕ) (lam : Fin d → ℂ) (c : Config d) (a : ℂ) :
    dgammaC d (Matrix.diagonal lam) (Finsupp.single c a)
      = (a * (∑ i, lam i * (c i : ℂ))) • Finsupp.single c 1 := by
  have step : ∀ i : Fin d,
      ((∑ j : Fin d, ((Matrix.diagonal lam) i j) • ((adagC d i) ∘ₗ (annC d j)))
          (Finsupp.single c a))
        = lam i • ((adagC d i) ∘ₗ (annC d i)) (Finsupp.single c a) := by
    intro i
    rw [LinearMap.sum_apply]
    refine (Finset.sum_eq_single i (fun j _ hji => ?_)
      (fun hi => absurd (Finset.mem_univ i) hi)).trans ?_
    · rw [LinearMap.smul_apply, Matrix.diagonal_apply_ne' _ hji, zero_smul]
    · rw [LinearMap.smul_apply, Matrix.diagonal_apply_eq]
  calc dgammaC d (Matrix.diagonal lam) (Finsupp.single c a)
      = ∑ i : Fin d, lam i • ((adagC d i) ∘ₗ (annC d i)) (Finsupp.single c a) := by
        unfold dgammaC
        rw [LinearMap.sum_apply]
        exact Finset.sum_congr rfl (fun i _ => step i)
    _ = ∑ i : Fin d, lam i • ((a * (c i : ℂ)) • Finsupp.single c 1) :=
        Finset.sum_congr rfl (fun i _ => by rw [dgammaC_number_mode])
    _ = ∑ i : Fin d, (lam i * (a * (c i : ℂ))) • Finsupp.single c 1 :=
        Finset.sum_congr rfl (fun i _ => by rw [smul_smul])
    _ = (∑ i, lam i * (a * (c i : ℂ))) • Finsupp.single c 1 := Finset.sum_smul.symm
    _ = (a * (∑ i, lam i * (c i : ℂ))) • Finsupp.single c 1 := by
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)

/-- **The coefficient formula for `dΓ(diag λ)` (T1):** extracting the
`c`-th coefficient multiplies by the eigenvalue `∑ i, λ i * (c i)`. -/
theorem dgammaC_diag_apply (d : ℕ) (lam : Fin d → ℂ) (l : Config d →₀ ℂ)
    (c : Config d) :
    (dgammaC d (Matrix.diagonal lam) l) c = (∑ i, lam i * (c i : ℂ)) * l c := by
  induction l using Finsupp.induction with
  | zero => simp
  | single_add γ v f _ _ ih =>
      rw [map_add, Finsupp.add_apply, Finsupp.add_apply, ih, dgammaC_diag_single,
        Finsupp.smul_apply, Finsupp.single_apply, Finsupp.single_apply, smul_eq_mul]
      by_cases hγ : γ = c
      · rw [if_pos hγ, if_pos hγ]
        subst hγ
        ring
      · rw [if_neg hγ, if_neg hγ]
        ring

/-- The diagonal one-particle operator with real eigenvalues. -/
noncomputable def onePartDiagBos (d : ℕ) (lam : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun i => (lam i : ℂ))

/-- The free bosonic Hamiltonian `H = dΓ(diag λ)` on `Dom d` — free
theory, finite modes. -/
noncomputable def freeHamiltonianBos (d : ℕ) (lam : Fin d → ℝ) :
    Module.End ℂ (Dom d) :=
  dgammaBos d (onePartDiagBos d lam)

/-- **Free-Hamiltonian basis action (T1, free theory, finite modes):**
`H e_c = ((∑ i, λ i · (c i) : ℝ) : ℂ) • e_c`. -/
theorem freeHamiltonianBos_basis (d : ℕ) (lam : Fin d → ℝ) (c : Config d) :
    freeHamiltonianBos d lam ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = ((∑ i, lam i * (c i : ℝ) : ℝ) : ℂ) •
          ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩ := by
  show dgammaBos d (Matrix.diagonal (fun i => (lam i : ℂ))) _ = _
  rw [dgammaBos_basis_diag]
  congr 1
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun i _ => by push_cast; ring)

/-- **Free-Hamiltonian coordinate identity (T1, free theory, finite
modes):** the `c`-th coefficient of `H x`, extracted through
`boseRepr`, is the eigenvalue `∑ i, λ i · (c i)` times that of `x`. -/
theorem freeHamiltonianBos_coord (d : ℕ) (lam : Fin d → ℝ) (x : Dom d)
    (c : Config d) :
    (boseRepr d (freeHamiltonianBos d lam x)) c
      = ((∑ i, lam i * (c i : ℝ) : ℝ) : ℂ) * (boseRepr d x) c := by
  have h1 : (boseRepr d (freeHamiltonianBos d lam x)) c
      = (∑ i, (lam i : ℂ) * (c i : ℂ)) * (boseRepr d x) c := by
    show (boseRepr d (dgammaBos d (Matrix.diagonal (fun i => (lam i : ℂ))) x)) c = _
    rw [repr_dgammaBos]
    exact dgammaC_diag_apply d (fun i => (lam i : ℂ)) (boseRepr d x) c
  rw [h1]
  congr 1
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun i _ => by push_cast; ring)

/-- The vacuum eigenvalue of the free Hamiltonian is `0` (T1, free
theory, finite modes). -/
theorem freeHamiltonianBos_vacuum (d : ℕ) (lam : Fin d → ℝ) :
    freeHamiltonianBos d lam (vacDom d) = 0 :=
  dgammaBos_vacuum d _

/-- The diagonal one-particle operator with real eigenvalues is
self-adjoint as a matrix (T1). -/
theorem onePartDiagBos_conjTranspose (d : ℕ) (lam : Fin d → ℝ) :
    (onePartDiagBos d lam)ᴴ = onePartDiagBos d lam := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [onePartDiagBos, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq,
      Complex.conj_ofReal]
  · have h' : j ≠ i := Ne.symm h
    simp only [onePartDiagBos, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply_ne' _ h, Matrix.diagonal_apply_ne' _ h', star_zero]

/-- **The free Hamiltonian is self-adjoint (T1, free theory, finite
modes; inner-product form on `Dom d`).** -/
theorem freeHamiltonianBos_selfadjoint (d : ℕ) (lam : Fin d → ℝ) (x y : Dom d) :
    ⟪(((freeHamiltonianBos d lam x) : Dom d) : BosonicFock d),
        (y : BosonicFock d)⟫_ℂ
      = ⟪(x : BosonicFock d),
          (((freeHamiltonianBos d lam y) : Dom d) : BosonicFock d)⟫_ℂ := by
  show ⟪(((dgammaBos d (onePartDiagBos d lam) x) : Dom d) : BosonicFock d),
        (y : BosonicFock d)⟫_ℂ
      = ⟪(x : BosonicFock d),
          (((dgammaBos d (onePartDiagBos d lam) y) : Dom d) : BosonicFock d)⟫_ℂ
  rw [dgammaBos_adjoint, onePartDiagBos_conjTranspose]

/-- **The free-theory dichotomy (T1, free theory, finite modes):**
every basis eigenvalue `∑ i, λ i · (c i)` of the free Hamiltonian is
`0` or `≥ Δ`, whenever each `λ i = 0 ∨ Δ ≤ λ i`. -/
theorem free_gap_dichotomy_bos (d : ℕ) (lam : Fin d → ℝ) (Δ : ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hgap : ∀ i, lam i = 0 ∨ Δ ≤ lam i) (c : Config d) :
    (∑ i, lam i * (c i : ℝ)) = 0 ∨ Δ ≤ ∑ i, lam i * (c i : ℝ) := by
  by_cases h : ∀ i, lam i * (c i : ℝ) = 0
  · exact Or.inl (Finset.sum_eq_zero (fun i _ => h i))
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    have hli : lam i ≠ 0 := fun hl => hi (by rw [hl, zero_mul])
    have hci : (1 : ℝ) ≤ (c i : ℝ) := by
      have hne : c i ≠ 0 := fun hc => hi (by rw [hc, Nat.cast_zero, mul_zero])
      have h1 : 1 ≤ c i := Nat.one_le_iff_ne_zero.mpr hne
      exact_mod_cast h1
    rcases hgap i with h0 | hge
    · exact absurd h0 hli
    · refine Or.inr (le_trans ?_ (Finset.single_le_sum
          (fun j _ => mul_nonneg (hlam j) (Nat.cast_nonneg _)) (Finset.mem_univ i)))
      calc Δ ≤ lam i := hge
        _ = lam i * 1 := (mul_one _).symm
        _ ≤ lam i * (c i : ℝ) := mul_le_mul_of_nonneg_left hci (hlam i)

/-- **The bosonic free Hamiltonian gap, DERIVED (T1 — free theory,
finite modes; NOT the interacting Yang–Mills gap).** Every eigenvalue
`μ` of `H = dΓ(diag λ)` on a nonzero vector of `Dom d` is realized by
a basis configuration, and is `0` or `≥ Δ` whenever each
`λ i = 0 ∨ Δ ≤ λ i`. -/
theorem freeHamiltonianBos_eigenvalue_gap (d : ℕ) (lam : Fin d → ℝ) (Δ : ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hgap : ∀ i, lam i = 0 ∨ Δ ≤ lam i)
    (ψ : Dom d) (hψ : ψ ≠ 0) (μ : ℂ)
    (hμ : freeHamiltonianBos d lam ψ = μ • ψ) :
    ∃ c : Config d, μ = ((∑ i, lam i * (c i : ℝ) : ℝ) : ℂ)
      ∧ ((∑ i, lam i * (c i : ℝ)) = 0 ∨ Δ ≤ ∑ i, lam i * (c i : ℝ)) := by
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
  refine ⟨c, ?_, free_gap_dichotomy_bos d lam Δ hlam hgap c⟩
  have hcoord := freeHamiltonianBos_coord d lam ψ c
  have hcoord2 : (boseRepr d (freeHamiltonianBos d lam ψ)) c
      = μ * (boseRepr d ψ) c := by
    rw [hμ, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact (mul_right_cancel₀ hc (hcoord.symm.trans hcoord2)).symm

/-- Every element of `Dom d` is the finite sum of its basis components
(T1). -/
theorem dom_expand (d : ℕ) (x : Dom d) :
    x = ∑ c ∈ (boseRepr d x).support, ((boseRepr d x) c) •
      ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩ := by
  apply (boseRepr d).injective
  rw [map_sum]
  simp_rw [map_smul, boseRepr_basis]
  conv_lhs => rw [← Finsupp.sum_single (boseRepr d x)]
  unfold Finsupp.sum
  exact Finset.sum_congr rfl (fun c _ => (single_smul_one c ((boseRepr d x) c)).symm)

/-- Auxiliary expectation computation over a general coefficient
vector `l` (T1, free theory, finite modes). -/
theorem freeHamiltonianBos_expectation_aux (d : ℕ) (lam : Fin d → ℝ)
    (l : Config d →₀ ℂ) :
    ⟪(((boseEquiv d l) : Dom d) : BosonicFock d),
        (((freeHamiltonianBos d lam (boseEquiv d l)) : Dom d) : BosonicFock d)⟫_ℂ
      = ((∑ c ∈ l.support, Complex.normSq (l c) *
          (∑ i, lam i * (c i : ℝ)) : ℝ) : ℂ) := by
  have e1 : boseEquiv d l
      = ∑ c ∈ l.support, (l c) •
          ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩ := by
    have h := dom_expand d (boseEquiv d l)
    rwa [show boseRepr d (boseEquiv d l) = l from
      LinearEquiv.symm_apply_apply (boseEquiv d) l] at h
  have e2 : freeHamiltonianBos d lam (boseEquiv d l)
      = ∑ c ∈ l.support, ((l c) * ((∑ i, lam i * (c i : ℝ) : ℝ) : ℂ)) •
          ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩ := by
    rw [e1, map_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [map_smul, freeHamiltonianBos_basis, smul_smul]
  rw [e2, e1]
  simp only [Submodule.coe_sum, Submodule.coe_smul, inner_sum, sum_inner,
    inner_smul_left, inner_smul_right, boseE_inner]
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_eq_single c
    (fun c' _ hcc' => by simp [hcc'])
    (fun hcc => absurd hc hcc)]
  rw [Complex.ofReal_mul, ← Complex.mul_conj, if_pos rfl]
  ring

/-- **Free-Hamiltonian expectation formula (T1, free theory, finite
modes):** `⟪x, H x⟫ = ∑_c ‖x_c‖² · (eigenvalue of c)`, a nonnegative
real combination when `λ ≥ 0`. -/
theorem freeHamiltonianBos_expectation (d : ℕ) (lam : Fin d → ℝ) (x : Dom d) :
    ⟪(x : BosonicFock d),
        (((freeHamiltonianBos d lam x) : Dom d) : BosonicFock d)⟫_ℂ
      = ((∑ c ∈ (boseRepr d x).support, Complex.normSq ((boseRepr d x) c) *
          (∑ i, lam i * (c i : ℝ)) : ℝ) : ℂ) := by
  have h := freeHamiltonianBos_expectation_aux d lam (boseRepr d x)
  have e : boseEquiv d (boseRepr d x) = x :=
    LinearEquiv.apply_symm_apply (boseEquiv d) x
  rwa [e] at h

/-- **The free Hamiltonian is positive (T1, free theory, finite
modes):** the real part of every expectation is `≥ 0` whenever
`λ i ≥ 0` — the expectation is a sum of nonnegative terms. -/
theorem freeHamiltonianBos_expectation_nonneg (d : ℕ) (lam : Fin d → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (x : Dom d) :
    0 ≤ (⟪(x : BosonicFock d),
        (((freeHamiltonianBos d lam x) : Dom d) : BosonicFock d)⟫_ℂ).re := by
  rw [freeHamiltonianBos_expectation, Complex.ofReal_re]
  apply Finset.sum_nonneg
  intro c _
  apply mul_nonneg (Complex.normSq_nonneg _)
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hlam i) (Nat.cast_nonneg _)

end ThetLogos
