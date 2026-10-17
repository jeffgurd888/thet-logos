import ThetLogos.FermionicLimit
import ThetLogos.SecondQuantGamma
import ThetLogos.SecondQuantDGamma

/-!
# Pitch 2, Campaign B (fermionic side): Γ of the padded inclusion, the union
# characterization, diagonal dΓ in the limit, and the free gap in the limit

Campaign A (`FockLimit`, `FermionicLimit`, `BosonicLimit`) built the limit
Fock spaces at countably many modes, the finite-level embeddings, and the
density of the limit finite-particle domains.  This module proves the
Campaign B tasks on the fermionic side:

* **Task 3a.**  The level embedding `fockEmb h` *is* second quantization of
  the padded inclusion: it equals `gammaFermRect (padMatrixFerm h)`, the
  rectangular Γ-operator (minor determinants, Rung 9's Γ API widened to
  rectangular matrices) of the matrix that pads `Fin d` into `Fin e` by
  `Fin.castLE h`.
* **Task 4a.**  The union characterization: `fermDomLim` is the supremum,
  over all levels `d`, of the ranges of the limit embeddings `fockEmbLim d`.
  (Density itself was Campaign A: `fermDomLim_topologicalClosure`.)
* **Task 5.**  Diagonal `dΓ` in the limit: for an eigenvalue function
  `a : ℕ → ℂ`, `dGammaLimFerm a` acts on the limit domain `fermDomLim` by
  multiplying the `S`-coefficient by `∑ j ∈ S, a j`.  Its restriction along
  `fockEmbLim d` agrees with the finite `dgamma d (diagA d a)`, and the
  number operator is the case `a ≡ 1`.
* **Task 6.**  The free gap survives: for `ω : ℕ → ℝ` with `1 ≤ ω i`, the
  limit free Hamiltonian `freeHamiltonianLimFerm ω` has vacuum eigenvalue
  `0`, every basis eigenvalue is `0` or `≥ Δ` (any `0 < Δ ≤ ω`), and every
  nonzero eigenvector on the domain has eigenvalue `0` or `≥ Δ`;
  orthogonality to the vacuum forces `≥ Δ`.

## Ledger (honesty labels)

* **T1 throughout**: every statement below is machine-checked, no `sorry`.
* **Free theory only.**  `dGammaLimFerm` is a *diagonal* second quantization;
  second quantization of a general one-particle operator in the limit, and
  any interaction, are not in this pitch.
* **Countably many modes** after this campaign (Campaign A removed the
  "finite modes" scope word); there is **no continuum** here and **no
  Poincaré action**.
* **Not the Yang–Mills gap.**  Mandatory clause, carried verbatim from the
  Pitch 2 scoping §6: the gap proved here is the gap in the
  eigenvalue-on-finite-particle-domain sense of Rungs 9–10; the spectral
  statement is priced, unattempted.
* Task 3b (full rectangular functoriality) and Task 7 (spectral form) are
  pre-agreed cuts of the scoping and are not attempted.
-/

namespace ThetLogos

open scoped InnerProductSpace

/-! ## Task 3a (fermions): the rectangular Γ API and the padded inclusion -/

/-- Rectangular minor determinant: the minor of a rectangular matrix
`M : Matrix (Fin e) (Fin d) ℂ` between a source configuration `S` and a
target configuration `T`.  For square `M` this is `minorDet` verbatim. -/
noncomputable def minorDetRect {d e : ℕ} (M : Matrix (Fin e) (Fin d) ℂ)
    (S : Finset (Fin d)) (T : Finset (Fin e)) : ℂ :=
  if h : S.card = T.card then
    Matrix.det (fun a b : Fin T.card => M (T.orderEmbOfFin rfl a) (S.orderEmbOfFin h b))
  else 0

/-- The rectangular minor determinant restricts to Rung 9's `minorDet` on
square matrices. -/
theorem minorDetRect_eq_minorDet {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ)
    (S T : Finset (Fin d)) : minorDetRect M S T = minorDet d M S T := rfl

/-- Rectangular Γ on the coordinate (`Pi`) model: the widened form of
Rung 9's `gammaPi`. -/
noncomputable def gammaPiRect {d e : ℕ} (M : Matrix (Fin e) (Fin d) ℂ) :
    (Π _S : Finset (Fin d), ℂ) →ₗ[ℂ] (Π _T : Finset (Fin e), ℂ) where
  toFun x T := ∑ S, minorDetRect M S T * x S
  map_add' x y := by
    funext T
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun S _ => mul_add _ _ _
  map_smul' c x := by
    funext T
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    ring

/-- Rectangular Γ on Fock space, by conjugation with the coordinate
equivalences — the widened form of Rung 9's `gamma`, written as an explicit
composition. -/
noncomputable def gammaFermRect {d e : ℕ} (M : Matrix (Fin e) (Fin d) ℂ) :
    FermionicFock d →ₗ[ℂ] FermionicFock e :=
  (fockEquiv e).toLinearMap ∘ₗ (gammaPiRect M ∘ₗ (fockEquiv d).symm.toLinearMap)

@[simp]
theorem gammaFermRect_apply {d e : ℕ} (M : Matrix (Fin e) (Fin d) ℂ)
    (x : FermionicFock d) (T : Finset (Fin e)) :
    (gammaFermRect M x).ofLp T = ∑ S, minorDetRect M S T * x.ofLp S := rfl

/-- The padded-inclusion matrix: `Fin d` sits inside `Fin e` via
`Fin.castLE h`, padded by zero columns/rows outside the image. -/
noncomputable def padMatrixFerm {d e : ℕ} (h : d ≤ e) : Matrix (Fin e) (Fin d) ℂ :=
  fun i j => if (i : ℕ) = (j : ℕ) then 1 else 0

/-- The order-embedding of the embedded configuration `fermConfigEmb h S`
is `Fin.castLE h` applied to the order-embedding of `S`. -/
theorem fermConfigEmb_orderEmbOfFin {d e : ℕ} (h : d ≤ e) (S : Finset (Fin d))
    (T : Finset (Fin e)) (hT : T = fermConfigEmb h S) (hcard : S.card = T.card)
    (a : Fin T.card) :
    T.orderEmbOfFin rfl a = Fin.castLE h (S.orderEmbOfFin hcard a) := by
  subst hT
  have hunique : (fun a => Fin.castLE h (S.orderEmbOfFin hcard a))
      = (fermConfigEmb h S).orderEmbOfFin rfl := by
    apply Finset.orderEmbOfFin_unique rfl
    · intro a
      show Fin.castLE h (S.orderEmbOfFin hcard a)
          ∈ Finset.map (Fin.castLEEmb h) S
      exact Finset.mem_map.mpr ⟨S.orderEmbOfFin hcard a,
        Finset.orderEmbOfFin_mem _ _ _, rfl⟩
    · exact (Fin.strictMono_castLE h).comp (S.orderEmbOfFin hcard).strictMono
  exact (congrFun hunique a).symm

/-- The padded-inclusion minor: `1` exactly on the embedded configuration,
`0` elsewhere.  This is the finite computation that makes the level
embedding a Γ-operator. -/
theorem minorDetRect_pad {d e : ℕ} (h : d ≤ e) (S : Finset (Fin d))
    (T : Finset (Fin e)) :
    minorDetRect (padMatrixFerm h) S T = if T = fermConfigEmb h S then 1 else 0 := by
  by_cases hT : T = fermConfigEmb h S
  · rw [if_pos hT]
    have hcard : S.card = T.card := by rw [hT, fermConfigEmb_card]
    rw [minorDetRect, dif_pos hcard]
    have hmat : (fun a b : Fin T.card =>
        padMatrixFerm h (T.orderEmbOfFin rfl a) (S.orderEmbOfFin hcard b))
        = (1 : Matrix (Fin T.card) (Fin T.card) ℂ) := by
      funext a b
      have hval : ((T.orderEmbOfFin rfl a : Fin e) : ℕ)
          = ((S.orderEmbOfFin hcard b : Fin d) : ℕ) ↔ a = b := by
        rw [fermConfigEmb_orderEmbOfFin h S T hT hcard a]
        constructor
        · intro hv
          have hinj := (S.orderEmbOfFin hcard).injective
          apply hinj
          exact Fin.ext hv
        · intro hab
          subst hab
          rfl
      show (if ((T.orderEmbOfFin rfl a : Fin e) : ℕ)
          = ((S.orderEmbOfFin hcard b : Fin d) : ℕ) then (1 : ℂ) else 0)
          = (1 : Matrix (Fin T.card) (Fin T.card) ℂ) a b
      by_cases hab : a = b
      · subst hab
        rw [if_pos (hval.mpr rfl), Matrix.one_apply_eq]
      · rw [if_neg (fun hv => hab (hval.mp hv)), Matrix.one_apply_ne hab]
    rw [hmat, Matrix.det_one]
  · rw [if_neg hT]
    by_cases hcard : S.card = T.card
    · rw [minorDetRect, dif_pos hcard]
      -- Some column is zero: some value of `S` is attained by no value of
      -- `T` — otherwise the two value sets agree, and `T = fermConfigEmb h S`.
      obtain ⟨b, hb⟩ : ∃ b : Fin T.card, ∀ a : Fin T.card,
          ((T.orderEmbOfFin rfl a : Fin e) : ℕ)
            ≠ ((S.orderEmbOfFin hcard b : Fin d) : ℕ) := by
        by_contra hcon
        push_neg at hcon
        apply hT
        have hcardST : (S.image Fin.val).card = (T.image Fin.val).card := by
          rw [Finset.card_image_of_injective _ Fin.val_injective,
            Finset.card_image_of_injective _ Fin.val_injective, hcard]
        have hsub : (S.image Fin.val) ⊆ (T.image Fin.val) := by
          intro x hx
          obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
          obtain ⟨b, hb⟩ : ∃ b : Fin T.card, S.orderEmbOfFin hcard b = s := by
            have hs' : (s : Fin d) ∈ Set.range (S.orderEmbOfFin hcard) := by
              rw [Finset.range_orderEmbOfFin]; exact Finset.mem_coe.mpr hs
            obtain ⟨b, hb⟩ := hs'
            exact ⟨b, hb⟩
          obtain ⟨a, ha⟩ := hcon b
          exact Finset.mem_image.mpr ⟨T.orderEmbOfFin rfl a,
            Finset.orderEmbOfFin_mem _ _ _, ha.trans (congrArg Fin.val hb)⟩
        have himg : S.image Fin.val = T.image Fin.val :=
          Finset.eq_of_subset_of_card_le hsub (le_of_eq hcardST.symm)
        apply Finset.ext
        intro t
        constructor
        · intro ht
          have hvt : (t : ℕ) ∈ S.image Fin.val := by
            have hmem : (t : ℕ) ∈ T.image Fin.val :=
              Finset.mem_image.mpr ⟨t, ht, rfl⟩
            rwa [← himg] at hmem
          obtain ⟨s, hs, hsv⟩ := Finset.mem_image.mp hvt
          rw [fermConfigEmb_apply]
          refine Finset.mem_map.mpr ⟨s, hs, ?_⟩
          apply Fin.ext
          exact hsv
        · intro ht
          rw [fermConfigEmb_apply] at ht
          obtain ⟨s, hs, hsu⟩ := Finset.mem_map.mp ht
          have hvs : (s : ℕ) ∈ T.image Fin.val := by
            have hmem : (s : ℕ) ∈ S.image Fin.val :=
              Finset.mem_image.mpr ⟨s, hs, rfl⟩
            rwa [himg] at hmem
          obtain ⟨t', ht', htv⟩ := Finset.mem_image.mp hvs
          have hut : Fin.castLEEmb h s = t' := Fin.ext htv.symm
          rw [← hsu, hut]
          exact ht'
      exact Matrix.det_eq_zero_of_column_eq_zero b (fun a => by
        show (if ((T.orderEmbOfFin rfl a : Fin e) : ℕ)
            = ((S.orderEmbOfFin hcard b : Fin d) : ℕ) then (1 : ℂ) else 0) = 0
        exact if_neg (hb a))
    · rw [minorDetRect, dif_neg hcard]

/-- The rectangular Γ of the padded inclusion sends basis vector to basis
vector exactly as the level embedding does. -/
theorem gammaFermRect_pad_basis {d e : ℕ} (h : d ≤ e) (S : Finset (Fin d)) :
    gammaFermRect (padMatrixFerm h) (fockBasis d S)
      = fockBasis e (fermConfigEmb h S) := by
  apply PiLp.ext
  intro T
  simp only [gammaFermRect_apply, fockBasis_ofLp]
  rw [Finset.sum_eq_single S]
  · rw [minorDetRect_pad]
    simp
  · intro S' _ hS'
    rw [if_neg hS', mul_zero]
  · intro hS
    exact absurd (Finset.mem_univ S) hS

/-- **Task 3a (fermions), operator form.**  The level embedding *is* second
quantization of the padded inclusion: `fockEmb h` equals the rectangular
Γ-operator of `padMatrixFerm h`. -/
theorem gammaFermRect_pad {d e : ℕ} (h : d ≤ e) :
    gammaFermRect (padMatrixFerm h) = (fockEmb h).toLinearMap := by
  have key : ∀ x : FermionicFock d,
      gammaFermRect (padMatrixFerm h) x = fockEmb h x := by
    intro x
    have hx : x ∈ Submodule.span ℂ (Set.range (fockBasis d)) := by
      rw [← fermHilbertBasis_coe, fermHilbertBasis_span]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨S, rfl⟩ := hy
        exact (gammaFermRect_pad_basis h S).trans (fockEmb_basis h S).symm
    | zero => rw [map_zero, map_zero]
    | add y z _ _ ihy ihz => rw [map_add, map_add, ihy, ihz]
    | smul a y _ ihy => rw [map_smul, map_smul, ihy]
  exact LinearMap.ext key

/-! ## Task 4a (fermions): the union characterization -/

/-- **Task 4a (fermions).**  The limit finite-particle domain is exactly
the union (supremum) over all finite levels of the embedded finite
spaces: every limit configuration factors through a finite level
(`fermConfig_factor`), and each embedded level lands in the domain
(`fockEmbLim_mem_domLim`). -/
theorem fermDomLim_eq_iSup_range :
    fermDomLim = ⨆ d : ℕ, LinearMap.range (fockEmbLim d).toLinearMap := by
  apply le_antisymm
  · rw [fermDomLim, Submodule.span_le]
    rintro _ ⟨S, rfl⟩
    obtain ⟨d, S₀, hS₀⟩ := fermConfig_factor S
    apply Submodule.mem_iSup_of_mem d
    rw [← hS₀, ← fockEmbLim_basis]
    exact LinearMap.mem_range_self _ _
  · apply iSup_le
    intro d
    intro x hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy]
    exact fockEmbLim_mem_domLim d y

/-- Density of the union, restated: the closure of the supremum of the
embedded finite levels is everything (Campaign A proved this for
`fermDomLim` itself). -/
theorem ferm_iSup_range_topologicalClosure :
    (⨆ d : ℕ, LinearMap.range (fockEmbLim d).toLinearMap).topologicalClosure
      = ⊤ := by
  rw [← fermDomLim_eq_iSup_range]
  exact fermDomLim_topologicalClosure

/-! ## Task 5 (fermions): diagonal dΓ in the limit -/

/-- Linear independence of the limit basis family (from orthonormality). -/
theorem fockBasisLim_linIndep : LinearIndependent ℂ fockBasisLim :=
  fockBasisLim_orthonormal.linearIndependent

/-- The coordinate equivalence between finitely supported coefficient
functions on limit configurations and the limit domain — the limit form of
the finite `fockEquiv`-style basis equivalence. -/
noncomputable def fermEquivLim : (Finset ℕ →₀ ℂ) ≃ₗ[ℂ] fermDomLim :=
  fockBasisLim_linIndep.linearCombinationEquiv

/-- The coefficient (representation) equivalence, inverse of
`fermEquivLim`. -/
noncomputable def fermReprLim : fermDomLim ≃ₗ[ℂ] (Finset ℕ →₀ ℂ) :=
  fermEquivLim.symm

theorem fermEquivLim_basis (S : Finset ℕ) :
    fermEquivLim (Finsupp.single S 1)
      = ⟨fockBasisLim S, Submodule.subset_span ⟨S, rfl⟩⟩ := by
  have h : fockBasisLim_linIndep.repr ⟨fockBasisLim S, Submodule.subset_span ⟨S, rfl⟩⟩
      = Finsupp.single S 1 :=
    LinearIndependent.repr_eq_single _ _ _ rfl
  have h2 : fermEquivLim (fockBasisLim_linIndep.repr
        ⟨fockBasisLim S, Submodule.subset_span ⟨S, rfl⟩⟩)
      = ⟨fockBasisLim S, Submodule.subset_span ⟨S, rfl⟩⟩ := by
    show fockBasisLim_linIndep.linearCombinationEquiv
        (fockBasisLim_linIndep.linearCombinationEquiv.symm _) = _
    exact LinearEquiv.apply_symm_apply _ _
  rw [h] at h2
  exact h2

theorem fermReprLim_basis (S : Finset ℕ) :
    fermReprLim ⟨fockBasisLim S, Submodule.subset_span ⟨S, rfl⟩⟩
      = Finsupp.single S 1 := by
  rw [fermReprLim, LinearEquiv.symm_apply_eq]
  exact (fermEquivLim_basis S).symm

/-- The eigenvalue of a diagonal one-particle operator with eigenvalue
function `a` on the configuration `S`: the `a`-weighted total
`∑ j ∈ S, a j`. -/
def fermEigLim (a : ℕ → ℂ) (S : Finset ℕ) : ℂ := ∑ j ∈ S, a j

/-- The diagonal action on coefficient functions: multiply the
`S`-coefficient by the eigenvalue `fermEigLim a S`. -/
noncomputable def diagFinsuppFerm (a : ℕ → ℂ) :
    (Finset ℕ →₀ ℂ) →ₗ[ℂ] (Finset ℕ →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun S => fermEigLim a S • Finsupp.single S 1)

theorem diagFinsuppFerm_apply (a : ℕ → ℂ) (f : Finset ℕ →₀ ℂ) (T : Finset ℕ) :
    (diagFinsuppFerm a f) T = fermEigLim a T * f T := by
  rw [diagFinsuppFerm, Finsupp.linearCombination_apply, Finsupp.sum_apply]
  show (∑ S ∈ f.support, (f S • (fermEigLim a S • Finsupp.single S 1)) T)
      = fermEigLim a T * f T
  rw [Finset.sum_eq_single T]
  · rw [Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.single_apply, if_pos rfl,
      smul_eq_mul, smul_eq_mul, mul_one]
    exact mul_comm _ _
  · intro S _ hST
    rw [Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.single_apply, if_neg hST]
    simp
  · intro hT
    have hfT : f T = 0 := Finsupp.notMem_support_iff.mp hT
    rw [hfT]
    simp [Finsupp.smul_apply]

/-- **Diagonal dΓ in the limit (fermions).**  For an eigenvalue function
`a : ℕ → ℂ`, `dGammaLimFerm a` is the diagonal second quantization on the
limit domain: it multiplies the `S`-shaped coefficient by `∑ j ∈ S, a j`.
Only the diagonal family is in this pitch; dΓ of a general one-particle
operator in the limit is not attempted. -/
noncomputable def dGammaLimFerm (a : ℕ → ℂ) : fermDomLim →ₗ[ℂ] fermDomLim :=
  fermEquivLim.toLinearMap ∘ₗ (diagFinsuppFerm a ∘ₗ fermReprLim.toLinearMap)

/-- Basis vectors are eigenvectors of the limit diagonal dΓ, with the
expected eigenvalue. -/
theorem dGammaLimFerm_basis (a : ℕ → ℂ) (S : Finset ℕ) :
    dGammaLimFerm a ⟨fockBasisLim S, Submodule.subset_span ⟨S, rfl⟩⟩
      = fermEigLim a S • ⟨fockBasisLim S, Submodule.subset_span ⟨S, rfl⟩⟩ := by
  have hdiag : diagFinsuppFerm a (Finsupp.single S 1)
      = fermEigLim a S • Finsupp.single S 1 := by
    ext T
    rw [diagFinsuppFerm_apply, Finsupp.smul_apply, Finsupp.single_apply]
    by_cases hST : S = T <;> simp [hST, smul_eq_mul]
  show fermEquivLim (diagFinsuppFerm a
      (fermReprLim ⟨fockBasisLim S, Submodule.subset_span ⟨S, rfl⟩⟩)) = _
  rw [fermReprLim_basis, hdiag, map_smul, fermEquivLim_basis]

/-- The coefficient formula for the limit diagonal dΓ. -/
theorem dGammaLimFerm_coord (a : ℕ → ℂ) (x : fermDomLim) (S : Finset ℕ) :
    (fermReprLim (dGammaLimFerm a x)) S = fermEigLim a S * (fermReprLim x) S := by
  have h : fermReprLim (dGammaLimFerm a x)
      = diagFinsuppFerm a (fermReprLim x) := by
    show fermEquivLim.symm (fermEquivLim (diagFinsuppFerm a (fermReprLim x)))
      = diagFinsuppFerm a (fermReprLim x)
    exact LinearEquiv.symm_apply_apply _ _
  rw [h, diagFinsuppFerm_apply]

/-- Expansion of a domain vector in the limit basis (finite sum over the
support of its coefficient function). -/
theorem fermDomLim_expand (x : fermDomLim) :
    x = ∑ S ∈ (fermReprLim x).support, (fermReprLim x) S
      • (⟨fockBasisLim S, Submodule.subset_span ⟨S, rfl⟩⟩ : fermDomLim) := by
  apply fermReprLim.injective
  rw [map_sum]
  simp_rw [map_smul, fermReprLim_basis]
  conv_lhs => rw [← Finsupp.sum_single (fermReprLim x)]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The inner product with a basis vector reads off the (conjugated)
coefficient: the vacuum-orthogonality content used in Task 6. -/
theorem fermInner_basis (x : fermDomLim) (S : Finset ℕ) :
    ⟪x, (⟨fockBasisLim S, Submodule.subset_span ⟨S, rfl⟩⟩ : fermDomLim)⟫_ℂ
      = starRingEnd ℂ ((fermReprLim x) S) := by
  calc ⟪x, (⟨fockBasisLim S, Submodule.subset_span ⟨S, rfl⟩⟩ : fermDomLim)⟫_ℂ
      = ∑ T ∈ (fermReprLim x).support, starRingEnd ℂ ((fermReprLim x) T)
          * ⟪(⟨fockBasisLim T, Submodule.subset_span ⟨T, rfl⟩⟩ : fermDomLim),
              (⟨fockBasisLim S, Submodule.subset_span ⟨S, rfl⟩⟩ : fermDomLim)⟫_ℂ := by
        conv_lhs => rw [fermDomLim_expand x]
        rw [sum_inner]
        refine Finset.sum_congr rfl (fun T _ => ?_)
        exact inner_smul_left
          (⟨fockBasisLim T, Submodule.subset_span ⟨T, rfl⟩⟩ : fermDomLim)
          (⟨fockBasisLim S, Submodule.subset_span ⟨S, rfl⟩⟩ : fermDomLim)
          ((fermReprLim x) T)
    _ = starRingEnd ℂ ((fermReprLim x) S)
          * ⟪(⟨fockBasisLim S, Submodule.subset_span ⟨S, rfl⟩⟩ : fermDomLim),
              (⟨fockBasisLim S, Submodule.subset_span ⟨S, rfl⟩⟩ : fermDomLim)⟫_ℂ := by
        refine Finset.sum_eq_single S (fun T _ hTS => ?_) (fun hS => ?_)
        · simp [fockBasisLim_inner, hTS]
        · rw [Finsupp.notMem_support_iff.mp hS]
          simp
    _ = starRingEnd ℂ ((fermReprLim x) S) := by
        have hnorm : ‖fockBasisLim S‖ = 1 := fockBasisLim_orthonormal.1 S
        simp [hnorm]

/-- Coefficient expansion of the inner product over any finset covering
the support of the first vector's coefficients. -/
theorem fermInner_expand_of_subset (u v : fermDomLim) (U : Finset (Finset ℕ))
    (hU : (fermReprLim u).support ⊆ U) :
    ⟪u, v⟫_ℂ = ∑ T ∈ U, starRingEnd ℂ ((fermReprLim u) T)
      * (fermReprLim v) T := by
  have hbase : ⟪u, v⟫_ℂ = ∑ T ∈ (fermReprLim u).support,
      starRingEnd ℂ ((fermReprLim u) T) * (fermReprLim v) T := by
    conv_lhs => rw [fermDomLim_expand u]
    rw [sum_inner]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    have hTS : ⟪(⟨fockBasisLim T, Submodule.subset_span ⟨T, rfl⟩⟩
          : fermDomLim), v⟫_ℂ
        = (starRingEnd ℂ) (⟪v, (⟨fockBasisLim T,
            Submodule.subset_span ⟨T, rfl⟩⟩ : fermDomLim)⟫_ℂ) :=
      (RCLike.conj_conj _).symm.trans (congrArg (starRingEnd ℂ)
        (inner_conj_symm v
          (⟨fockBasisLim T, Submodule.subset_span ⟨T, rfl⟩⟩ : fermDomLim)))
    calc ⟪(fermReprLim u) T • (⟨fockBasisLim T,
              Submodule.subset_span ⟨T, rfl⟩⟩ : fermDomLim), v⟫_ℂ
        = (starRingEnd ℂ) ((fermReprLim u) T)
            * ⟪(⟨fockBasisLim T, Submodule.subset_span ⟨T, rfl⟩⟩
                : fermDomLim), v⟫_ℂ :=
          inner_smul_left
            (⟨fockBasisLim T, Submodule.subset_span ⟨T, rfl⟩⟩ : fermDomLim) v
            ((fermReprLim u) T)
      _ = (starRingEnd ℂ) ((fermReprLim u) T) * (fermReprLim v) T := by
          congr 1
          exact hTS.trans ((congrArg (starRingEnd ℂ)
            (fermInner_basis v T)).trans (RCLike.conj_conj _))
  rw [hbase]
  exact Finset.sum_subset hU (fun T _ hT => by
    rw [Finsupp.notMem_support_iff.mp hT]
    simp)

/-- The finite-level diagonal matrix of the eigenvalue function `a` at
level `d`: mode `j` carries eigenvalue `a j`. -/
noncomputable def diagA (d : ℕ) (a : ℕ → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun j : Fin d => a (j : ℕ))

/-- The level-`d` domain map: the limit embedding, viewed as landing in
the limit domain (legitimate for fermions: every finite vector is a
finite-particle vector). -/
noncomputable def fermDomMap (d : ℕ) : FermionicFock d →ₗ[ℂ] fermDomLim :=
  (fockEmbLim d).toLinearMap.codRestrict fermDomLim
    (fun x => fockEmbLim_mem_domLim d x)

theorem fermDomMap_apply (d : ℕ) (x : FermionicFock d) :
    ((fermDomMap d x : fermDomLim) : FermionicFockLim) = fockEmbLim d x := rfl

theorem fermDomMap_basis (d : ℕ) (S : Finset (Fin d)) :
    fermDomMap d (fockBasis d S)
      = ⟨fockBasisLim (fermConfigEmbLim d S),
          Submodule.subset_span ⟨fermConfigEmbLim d S, rfl⟩⟩ := by
  apply Subtype.ext
  show fockEmbLim d (fockBasis d S) = fockBasisLim (fermConfigEmbLim d S)
  exact fockEmbLim_basis d S

/-- The eigenvalue transports along the embedding: the `a`-weighted total
of the embedded configuration is the `a`-weighted total at the finite
level. -/
theorem fermEigLim_configEmbLim (a : ℕ → ℂ) (d : ℕ) (S : Finset (Fin d)) :
    fermEigLim a (fermConfigEmbLim d S) = ∑ j ∈ S, a (j : ℕ) := by
  rw [fermEigLim, fermConfigEmbLim_apply, Finset.sum_map]
  exact Finset.sum_congr rfl (fun j _ => rfl)

/-- **Task 5 compatibility (fermions).**  The limit diagonal dΓ restricts
along the level-`d` embedding to the finite diagonal dΓ: the diagram
commutes on the nose. -/
theorem dGammaLimFerm_compat (a : ℕ → ℂ) (d : ℕ) :
    (dGammaLimFerm a) ∘ₗ (fermDomMap d)
      = (fermDomMap d) ∘ₗ (dgamma d (diagA d a)) := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span ℂ (Set.range (fockBasis d)) := by
    rw [← fermHilbertBasis_coe, fermHilbertBasis_span]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨S, rfl⟩ := hy
      calc (dGammaLimFerm a ∘ₗ fermDomMap d) (fockBasis d S)
          = dGammaLimFerm a ⟨fockBasisLim (fermConfigEmbLim d S),
              Submodule.subset_span ⟨fermConfigEmbLim d S, rfl⟩⟩ := by
            rw [LinearMap.comp_apply, fermDomMap_basis]
        _ = fermEigLim a (fermConfigEmbLim d S)
              • ⟨fockBasisLim (fermConfigEmbLim d S),
                  Submodule.subset_span ⟨fermConfigEmbLim d S, rfl⟩⟩ :=
            dGammaLimFerm_basis a _
        _ = (∑ j ∈ S, a (j : ℕ)) • fermDomMap d (fockBasis d S) := by
            rw [fermEigLim_configEmbLim, fermDomMap_basis]
        _ = fermDomMap d ((∑ j ∈ S, a (j : ℕ)) • fockBasis d S) := by
            rw [map_smul]
        _ = (fermDomMap d ∘ₗ dgamma d (diagA d a)) (fockBasis d S) := by
            rw [LinearMap.comp_apply]
            congr 1
            exact (dgamma_basis_diag d (fun j : Fin d => a (j : ℕ)) S).symm
  | zero =>
      show dGammaLimFerm a (fermDomMap d 0)
          = fermDomMap d (dgamma d (diagA d a) 0)
      simp only [map_zero]
  | add y z _ _ ihy ihz =>
      have ihy' : dGammaLimFerm a (fermDomMap d y)
          = fermDomMap d (dgamma d (diagA d a) y) := ihy
      have ihz' : dGammaLimFerm a (fermDomMap d z)
          = fermDomMap d (dgamma d (diagA d a) z) := ihz
      show dGammaLimFerm a (fermDomMap d (y + z))
          = fermDomMap d (dgamma d (diagA d a) (y + z))
      simp only [map_add, ihy', ihz']
  | smul c y _ ihy =>
      have ihy' : dGammaLimFerm a (fermDomMap d y)
          = fermDomMap d (dgamma d (diagA d a) y) := ihy
      show dGammaLimFerm a (fermDomMap d (c • y))
          = fermDomMap d (dgamma d (diagA d a) (c • y))
      simp only [map_smul, ihy']

/-- **The number operator in the limit (fermions)**: the `a ≡ 1` case of
the limit diagonal dΓ. -/
noncomputable def numberOpLimFerm : fermDomLim →ₗ[ℂ] fermDomLim :=
  dGammaLimFerm (fun _ => 1)

theorem numberOpLimFerm_basis (S : Finset ℕ) :
    numberOpLimFerm ⟨fockBasisLim S, Submodule.subset_span ⟨S, rfl⟩⟩
      = (S.card : ℂ) • ⟨fockBasisLim S, Submodule.subset_span ⟨S, rfl⟩⟩ := by
  rw [numberOpLimFerm, dGammaLimFerm_basis]
  congr 1
  simp [fermEigLim, Finset.sum_const, nsmul_eq_mul]

/-- The limit number operator restricts to the finite number operator at
every level (via `dgamma_one`). -/
theorem numberOpLimFerm_compat (d : ℕ) :
    numberOpLimFerm ∘ₗ (fermDomMap d) = (fermDomMap d) ∘ₗ (numberOp d) := by
  have h1 : diagA d (fun _ => (1 : ℂ)) = 1 := by
    rw [diagA, Matrix.diagonal_one]
  calc numberOpLimFerm ∘ₗ (fermDomMap d)
      = (dGammaLimFerm (fun _ => 1)) ∘ₗ (fermDomMap d) := rfl
    _ = (fermDomMap d) ∘ₗ (dgamma d (diagA d (fun _ => (1 : ℂ)))) :=
        dGammaLimFerm_compat (fun _ => 1) d
    _ = (fermDomMap d) ∘ₗ (numberOp d) := by rw [h1, dgamma_one]

/-- The vacuum is annihilated by every limit diagonal dΓ. -/
theorem dGammaLimFerm_vacuum (a : ℕ → ℂ) :
    dGammaLimFerm a ⟨fockVacLim, Submodule.subset_span ⟨∅, rfl⟩⟩ = 0 := by
  show dGammaLimFerm a ⟨fockBasisLim ∅, Submodule.subset_span ⟨∅, rfl⟩⟩ = 0
  rw [dGammaLimFerm_basis]
  simp [fermEigLim]

/-! ## Task 6 (fermions): the free gap in the limit -/

/-- The real eigenvalue of the limit free Hamiltonian on a
configuration. -/
def fermEigReal (ω : ℕ → ℝ) (S : Finset ℕ) : ℝ := ∑ j ∈ S, ω j

/-- **The limit free Hamiltonian (fermions)**: diagonal dΓ of the
single-mode energies `ω`. -/
noncomputable def freeHamiltonianLimFerm (ω : ℕ → ℝ) :
    fermDomLim →ₗ[ℂ] fermDomLim :=
  dGammaLimFerm (fun i => (ω i : ℂ))

theorem freeHamiltonianLimFerm_basis (ω : ℕ → ℝ) (S : Finset ℕ) :
    freeHamiltonianLimFerm ω ⟨fockBasisLim S, Submodule.subset_span ⟨S, rfl⟩⟩
      = ((fermEigReal ω S : ℝ) : ℂ)
        • ⟨fockBasisLim S, Submodule.subset_span ⟨S, rfl⟩⟩ := by
  rw [freeHamiltonianLimFerm, dGammaLimFerm_basis]
  congr 1
  rw [fermEigLim, fermEigReal, Complex.ofReal_sum]

/-- Vacuum eigenvalue `0` for the limit free Hamiltonian. -/
theorem freeHamiltonianLimFerm_vacuum (ω : ℕ → ℝ) :
    freeHamiltonianLimFerm ω ⟨fockVacLim, Submodule.subset_span ⟨∅, rfl⟩⟩
      = 0 :=
  dGammaLimFerm_vacuum (fun i => (ω i : ℂ))

/-- The gap dichotomy on basis vectors, Δ-general: every basis eigenvalue
is `0` or `≥ Δ`. -/
theorem free_gap_dichotomy_lim_ferm (ω : ℕ → ℝ) (Δ : ℝ) (hΔ : 0 < Δ)
    (hω : ∀ i, Δ ≤ ω i) (S : Finset ℕ) :
    fermEigReal ω S = 0 ∨ Δ ≤ fermEigReal ω S := by
  by_cases hS : S = ∅
  · refine Or.inl ?_
    rw [hS]
    simp [fermEigReal]
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    refine Or.inr (le_trans (hω j) ?_)
    refine Finset.single_le_sum (fun i _ => (hΔ.le).trans (hω i)) hj

/-- The gap dichotomy at the tasked normalization `Δ = 1`. -/
theorem free_gap_dichotomy_lim_ferm_one (ω : ℕ → ℝ) (hω : ∀ i, 1 ≤ ω i)
    (S : Finset ℕ) :
    fermEigReal ω S = 0 ∨ 1 ≤ fermEigReal ω S :=
  free_gap_dichotomy_lim_ferm ω 1 one_pos hω S

/-- The coordinate formula for the limit free Hamiltonian. -/
theorem freeHamiltonianLimFerm_coord (ω : ℕ → ℝ) (x : fermDomLim)
    (S : Finset ℕ) :
    (fermReprLim (freeHamiltonianLimFerm ω x)) S
      = ((fermEigReal ω S : ℝ) : ℂ) * (fermReprLim x) S := by
  rw [freeHamiltonianLimFerm, dGammaLimFerm_coord]
  congr 1
  rw [fermEigLim, fermEigReal, Complex.ofReal_sum]

/-- Eigenvalue extraction in the limit, Δ-general: a nonzero eigenvector
on the domain has eigenvalue `((fermEigReal ω S : ℝ) : ℂ)` for some
configuration `S`, and that real eigenvalue is `0` or `≥ Δ`.  This is the
eigenvalue-on-finite-particle-domain gap of Rungs 9–10, at countably many
modes. -/
theorem freeHamiltonianLimFerm_eigenvalue_gap (ω : ℕ → ℝ) (Δ : ℝ)
    (hΔ : 0 < Δ) (hω : ∀ i, Δ ≤ ω i) (ψ : fermDomLim) (hψ : ψ ≠ 0) (μ : ℂ)
    (hμ : freeHamiltonianLimFerm ω ψ = μ • ψ) :
    ∃ S : Finset ℕ, μ = ((fermEigReal ω S : ℝ) : ℂ)
      ∧ (fermEigReal ω S = 0 ∨ Δ ≤ fermEigReal ω S)
      ∧ (fermReprLim ψ) S ≠ 0 := by
  obtain ⟨S, hS⟩ : ∃ S, (fermReprLim ψ) S ≠ 0 := by
    by_contra h
    push_neg at h
    apply hψ
    have hz : fermReprLim ψ = 0 := by
      ext T
      exact h T
    have hψ0 : ψ = fermEquivLim (fermReprLim ψ) :=
      (LinearEquiv.apply_symm_apply fermEquivLim ψ).symm
    rw [hz, map_zero] at hψ0
    exact hψ0
  refine ⟨S, ?_, free_gap_dichotomy_lim_ferm ω Δ hΔ hω S, hS⟩
  have hcoord := freeHamiltonianLimFerm_coord ω ψ S
  have hcoord2 : (fermReprLim (freeHamiltonianLimFerm ω ψ)) S
      = μ * (fermReprLim ψ) S := by
    rw [hμ, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact (mul_right_cancel₀ hS (hcoord.symm.trans hcoord2)).symm

/-- **The limit free gap (fermions), orthogonality form, `Δ = 1`.**  A
nonzero eigenvector on the domain that is orthogonal to the vacuum has
eigenvalue `≥ 1`.  Gap in the eigenvalue-on-finite-particle-domain sense
of Rungs 9–10; the spectral statement is priced, unattempted. -/
theorem freeHamiltonianLimFerm_gap_of_orth (ω : ℕ → ℝ) (hω : ∀ i, 1 ≤ ω i)
    (ψ : fermDomLim) (hψ : ψ ≠ 0) (μ : ℝ)
    (hμ : freeHamiltonianLimFerm ω ψ = (μ : ℂ) • ψ)
    (horth : ⟪ψ, (⟨fockVacLim,
      Submodule.subset_span ⟨∅, rfl⟩⟩ : fermDomLim)⟫_ℂ = 0) :
    1 ≤ μ := by
  obtain ⟨S, hμS, hdich, hSne⟩ :=
    freeHamiltonianLimFerm_eigenvalue_gap ω 1 one_pos hω ψ hψ (μ : ℂ) hμ
  have hμR : μ = fermEigReal ω S := by
    have hre := congrArg Complex.re hμS
    simpa using hre
  rcases hdich with h0 | h1
  · exfalso
    have hSempty : S = ∅ := by
      by_contra hne
      obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hpos : 0 < fermEigReal ω S :=
        lt_of_lt_of_le (by positivity : (0:ℝ) < 1)
          (le_trans (hω j) (Finset.single_le_sum
            (fun i _ => (zero_le_one).trans (hω i)) hj))
      rw [h0] at hpos
      exact lt_irrefl 0 hpos
    have hcoef : (fermReprLim ψ) ∅ ≠ 0 := hSempty ▸ hSne
    have horth' : ⟪ψ, (⟨fockBasisLim ∅,
        Submodule.subset_span ⟨∅, rfl⟩⟩ : fermDomLim)⟫_ℂ = 0 := horth
    rw [fermInner_basis] at horth'
    have hz : (fermReprLim ψ) ∅ = 0 := by
      apply (starRingEnd ℂ).injective
      rw [horth', map_zero]
    exact hcoef hz
  · rw [hμR]
    exact h1

/-- Self-adjointness of the limit free Hamiltonian on the domain
(expectation-form symmetry, as in the finite theory). -/
theorem freeHamiltonianLimFerm_selfadjoint (ω : ℕ → ℝ) (x y : fermDomLim) :
    ⟪freeHamiltonianLimFerm ω x, y⟫_ℂ
      = ⟪x, freeHamiltonianLimFerm ω y⟫_ℂ := by
  classical
  set U := (fermReprLim x).support ∪ (fermReprLim y).support
    ∪ (fermReprLim (freeHamiltonianLimFerm ω x)).support
    ∪ (fermReprLim (freeHamiltonianLimFerm ω y)).support with hU
  have hsub1 : (fermReprLim (freeHamiltonianLimFerm ω x)).support ⊆ U := by
    intro T hT
    simp only [hU, Finset.mem_union]
    exact Or.inl (Or.inr hT)
  have hsub2 : (fermReprLim x).support ⊆ U := by
    intro T hT
    simp only [hU, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl hT))
  rw [fermInner_expand_of_subset _ _ U hsub1,
    fermInner_expand_of_subset _ _ U hsub2]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  have hconj : ∀ r : ℝ, (starRingEnd ℂ) ((r : ℂ)) = (r : ℂ) :=
    fun r => RCLike.conj_ofReal r
  rw [freeHamiltonianLimFerm_coord, freeHamiltonianLimFerm_coord, map_mul,
    hconj]
  ring

end ThetLogos
