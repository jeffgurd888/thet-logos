import ThetLogos.BosonicLimit
import ThetLogos.BosonicGamma
import ThetLogos.BosonicGammaFunctor
import ThetLogos.BosonicSecondQuant

/-!
# Pitch 2, Campaign B (bosonic side): Γ of the padded inclusion, the union
# characterization, diagonal dΓ in the limit, and the free gap in the limit

Campaign A (`FockLimit`, `FermionicLimit`, `BosonicLimit`) built the limit
Fock spaces at countably many modes, the finite-level embeddings, and the
density of the limit finite-particle domains.  This module proves the
Campaign B tasks on the bosonic side:

* **Task 3a.**  The level embedding `fockEmbBos h` *is* second
  quantization of the padded inclusion: it equals `gammaBosRect
  (padMatrixBos h)`, the rectangular Γ-operator (permanent kernels, Rung
  10's Γ API widened to rectangular matrices) of the matrix that pads
  `Fin d` into `Fin e` by `Fin.castLE h`, as an operator `Dom d →ₗ Dom e`.
* **Task 4a.**  The union characterization: `DomLim` is the supremum,
  over all levels `d`, of the images of the finite domains under the
  limit embeddings `fockEmbBosLim d`.  (Density itself was Campaign A:
  `DomLim_topologicalClosure`.)
* **Task 5.**  Diagonal `dΓ` in the limit: for an eigenvalue function
  `a : ℕ → ℂ`, `dGammaLimBos a` acts on the limit domain `DomLim` by
  multiplying the `c`-coefficient by `c.sum (fun i n => a i * n)`.  Its
  restriction along `fockEmbBosLim d` agrees with the finite
  `dgammaBos d (diagABos d a)`, and the number operator is the case
  `a ≡ 1`.
* **Task 6.**  The free gap survives: for `ω : ℕ → ℝ` with `1 ≤ ω i`, the
  limit free Hamiltonian `freeHamiltonianLimBos ω` has vacuum eigenvalue
  `0`, every basis eigenvalue is `0` or `≥ Δ` (any `0 < Δ ≤ ω`), and
  every nonzero eigenvector on the domain has eigenvalue `0` or `≥ Δ`;
  orthogonality to the vacuum forces `≥ Δ`.

## Ledger (honesty labels)

* **T1 throughout**: every statement below is machine-checked, no `sorry`.
* **Free theory only.**  `dGammaLimBos` is a *diagonal* second
  quantization; second quantization of a general one-particle operator in
  the limit, and any interaction, are not in this pitch.
* **Countably many modes** after this campaign (Campaign A removed the
  "finite modes" scope word); there is **no continuum** here and **no
  Poincaré action**.
* **Not the Yang–Mills gap.**  Mandatory clause, carried verbatim from
  the Pitch 2 scoping §6: the gap proved here is the gap in the
  eigenvalue-on-finite-particle-domain sense of Rungs 9–10; the spectral
  statement is priced, unattempted.
* Task 3b (full rectangular functoriality) and Task 7 (spectral form)
  are pre-agreed cuts of the scoping and are not attempted.
-/

namespace ThetLogos

open scoped InnerProductSpace

/-! ## Shared transport lemma -/

/-- Sum transport along an embedding of index sets: summing a
`g`-weighted finsupp sum over an embedded finsupp equals summing over the
original with the index pushed forward. -/
theorem embDomain_sum_transport {α β M N : Type*} [Zero M] [AddCommMonoid N]
    (e : α ↪ β) (l : α →₀ M) (g : β → M → N) :
    (Finsupp.embDomain e l).sum g = l.sum (fun a m => g (e a) m) := by
  show (∑ b ∈ (Finsupp.embDomain e l).support, g b ((Finsupp.embDomain e l) b))
      = ∑ a ∈ l.support, g (e a) (l a)
  rw [Finsupp.support_embDomain, Finset.sum_map]
  exact Finset.sum_congr rfl (fun a _ => by rw [Finsupp.embDomain_apply_self])

/-! ## Task 3a (bosons): the rectangular Γ API and the padded inclusion -/

/-- Rectangular permanent minor: the permanent of a rectangular matrix
`M : Matrix (Fin e) (Fin d) ℂ` between a source configuration `c` and a
target configuration `c'`.  For square `M` this is `perMinor` verbatim. -/
noncomputable def perMinorRect {d e : ℕ} (M : Matrix (Fin e) (Fin d) ℂ)
    (c' : Config e) (c : Config d) : ℂ :=
  if h : tot c' = tot c then
    Matrix.permanent (fun a b : Fin (tot c) =>
      M (configEnum e c' (finCongr h.symm a)) (configEnum d c b))
  else 0

/-- The rectangular permanent minor restricts to Rung 10's `perMinor` on
square matrices. -/
theorem perMinorRect_eq_perMinor {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ)
    (c' c : Config d) : perMinorRect M c' c = perMinor d M c' c := rfl

/-- The padded-inclusion matrix: `Fin d` sits inside `Fin e` via
`Fin.castLE h`, padded by zeros outside the image. -/
noncomputable def padMatrixBos {d e : ℕ} (h : d ≤ e) : Matrix (Fin e) (Fin d) ℂ :=
  fun i j => if (i : ℕ) = (j : ℕ) then 1 else 0

/-- The fiber count of the padded position map `Fin.castLE h ∘ configEnum`
is exactly the embedded configuration. -/
theorem fiberCount_castLE_configEnum {d e : ℕ} (h : d ≤ e) (c : Config d)
    (i : Fin e) :
    fiberCount (fun b : Fin (tot c) => Fin.castLE h (configEnum d c b)) i
      = configEmb h c i := by
  classical
  by_cases hi : (i : ℕ) < d
  · set j : Fin d := ⟨(i : ℕ), hi⟩ with hj
    have hji : Fin.castLE h j = i := Fin.ext rfl
    have hfilter : (Finset.univ.filter (fun b => Fin.castLE h (configEnum d c b) = i))
        = Finset.univ.filter (fun b => configEnum d c b = j) := by
      apply Finset.filter_congr
      intro b _
      constructor
      · intro hb
        have hinj := (Fin.castLEOrderEmb h).injective
        apply hinj
        show Fin.castLE h (configEnum d c b) = Fin.castLE h j
        rw [hb, hji]
      · intro hb
        rw [hb, hji]
    have hfc : fiberCount (configEnum d c) j = c j := configEnum_fiber_card d c j
    have hce : configEmb h c i = c j := by
      rw [configEmb_apply]
      exact embDomain_apply_of_eq c (Fin.ext rfl)
    show (Finset.univ.filter (fun b => Fin.castLE h (configEnum d c b) = i)).card
        = configEmb h c i
    rw [hfilter, hce]
    exact hfc
  · have hempty : (Finset.univ.filter (fun b => Fin.castLE h (configEnum d c b) = i))
        = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro b _ hb
      have hv : ((configEnum d c b : Fin d) : ℕ) = (i : ℕ) := congrArg Fin.val hb
      have hlt : (configEnum d c b : ℕ) < d := (configEnum d c b).isLt
      omega
    have hnotmem : i ∉ (configEmb h c).support := by
      rw [configEmb_apply, Finsupp.support_embDomain]
      intro hm
      obtain ⟨j, _, hjm⟩ := Finset.mem_map.mp hm
      have hv : (j : ℕ) = (i : ℕ) := congrArg Fin.val hjm
      have hlt : (j : ℕ) < d := j.isLt
      omega
    show (Finset.univ.filter (fun b => Fin.castLE h (configEnum d c b) = i)).card
        = configEmb h c i
    rw [hempty, Finset.card_empty]
    exact (Finsupp.notMem_support_iff.mp hnotmem).symm

/-- Factorial products are invariant under a configuration embedding, for
any weight `F` with `F 0 = 1` (instantiated at `ℕ`, `ℝ`, `ℂ`). -/
theorem prod_factorial_configEmb {d e : ℕ} (h : d ≤ e) (c : Config d)
    {R : Type*} [CommSemiring R] (F : ℕ → R) (hF : F 0 = 1) :
    ∏ i : Fin e, F (configEmb h c i) = ∏ j : Fin d, F (c j) := by
  have step1 : ∏ i : Fin e, F (configEmb h c i)
      = (configEmb h c).prod (fun _ n => F n) :=
    (Finsupp.prod_fintype _ _ (fun _ => hF)).symm
  have step2 : (configEmb h c).prod (fun _ n => F n)
      = c.prod (fun _ n => F n) := by
    show (∏ x ∈ (configEmb h c).support, F ((configEmb h c) x))
        = ∏ x ∈ c.support, F (c x)
    rw [configEmb_apply, Finsupp.support_embDomain, Finset.prod_map]
    exact Finset.prod_congr rfl (fun j _ => by rw [Finsupp.embDomain_apply_self])
  have step3 : c.prod (fun _ n => F n) = ∏ j : Fin d, F (c j) :=
    Finsupp.prod_fintype _ _ (fun _ => hF)
  rw [step1, step2, step3]

/-- The padded-inclusion permanent minor: on the embedded configuration
it is the total multiplicity factorial; elsewhere it vanishes. -/
theorem perMinorRect_pad {d e : ℕ} (h : d ≤ e) (c' : Config e) (c : Config d) :
    perMinorRect (padMatrixBos h) c' c
      = if c' = configEmb h c then ((∏ j, Nat.factorial (c j) : ℕ) : ℂ)
        else 0 := by
  by_cases htot : tot c' = tot c
  · rw [perMinorRect, dif_pos htot]
    have hmat : (fun a b : Fin (tot c) => padMatrixBos h
          (configEnum e c' (finCongr htot.symm a)) (configEnum d c b))
        = (fun a b => if configEnum e c' (finCongr htot.symm a)
            = Fin.castLE h (configEnum d c b) then (1 : ℂ) else 0) := by
      funext a b
      show (if ((configEnum e c' (finCongr htot.symm a) : Fin e) : ℕ)
            = ((configEnum d c b : Fin d) : ℕ) then (1 : ℂ) else 0)
          = (if configEnum e c' (finCongr htot.symm a)
              = Fin.castLE h (configEnum d c b) then (1 : ℂ) else 0)
      by_cases hEq : configEnum e c' (finCongr htot.symm a)
          = Fin.castLE h (configEnum d c b)
      · have hval : ((configEnum e c' (finCongr htot.symm a) : Fin e) : ℕ)
            = ((configEnum d c b : Fin d) : ℕ) := congrArg Fin.val hEq
        rw [if_pos hval, if_pos hEq]
      · have hval : ¬ ((configEnum e c' (finCongr htot.symm a) : Fin e) : ℕ)
            = ((configEnum d c b : Fin d) : ℕ) := by
          intro hv
          exact hEq (Fin.ext hv)
        rw [if_neg hval, if_neg hEq]
    rw [hmat, permanent_indicator (w := fun _ => (1 : ℂ))]
    by_cases hEq : c' = configEmb h c
    · rw [if_pos hEq]
      have hcond : (∀ i, fiberCount (fun a : Fin (tot c) =>
            configEnum e c' (finCongr htot.symm a)) i
          = fiberCount (fun b : Fin (tot c) =>
            Fin.castLE h (configEnum d c b)) i) := by
        intro i
        rw [fiberCount_configEnum_finCongr e htot.symm i,
          fiberCount_castLE_configEnum h c i, hEq]
      rw [if_pos hcond, Finset.prod_const_one, mul_one]
      have hfib : (∀ i : Fin e, fiberCount (fun a : Fin (tot c) =>
            configEnum e c' (finCongr htot.symm a)) i = c' i) :=
        fun i => fiberCount_configEnum_finCongr e htot.symm i
      calc ((∏ i, Nat.factorial (fiberCount (fun a : Fin (tot c) =>
                configEnum e c' (finCongr htot.symm a)) i) : ℕ) : ℂ)
          = ∏ i, ((Nat.factorial (c' i) : ℕ) : ℂ) := by
            rw [Nat.cast_prod]
            exact Finset.prod_congr rfl (fun i _ => by rw [hfib i])
        _ = ((∏ j, Nat.factorial (c j) : ℕ) : ℂ) := by
            rw [hEq, Nat.cast_prod]
            exact prod_factorial_configEmb h c
              (fun n => ((Nat.factorial n : ℕ) : ℂ)) (by simp)
    · rw [if_neg hEq]
      rw [if_neg]
      intro hall
      apply hEq
      ext i
      have h1 : fiberCount (fun a : Fin (tot c) =>
            configEnum e c' (finCongr htot.symm a)) i = c' i :=
        fiberCount_configEnum_finCongr e htot.symm i
      have h2 : fiberCount (fun b : Fin (tot c) =>
            Fin.castLE h (configEnum d c b)) i = configEmb h c i :=
        fiberCount_castLE_configEnum h c i
      rw [← h1, ← h2]
      exact hall i
  · rw [perMinorRect, dif_neg htot,
      if_neg (fun hEq => htot (by rw [hEq, tot_configEmb]))]

/-- The rectangular Γ kernel: permanent minor over the normalization
factors — Rung 10's `gammaKernel` widened to rectangular matrices (the
source configuration's factor is at level `d`, the target's at `e`). -/
noncomputable def gammaKernelRect {d e : ℕ} (M : Matrix (Fin e) (Fin d) ℂ)
    (c' : Config e) (c : Config d) : ℂ :=
  perMinorRect M c' c / ((normFactor d c * normFactor e c' : ℝ) : ℂ)

/-- The rectangular kernel is nonzero only at matching total particle
number. -/
theorem gammaKernelRect_ne_zero {d e : ℕ} (M : Matrix (Fin e) (Fin d) ℂ)
    {c' : Config e} {c : Config d} (h : gammaKernelRect M c' c ≠ 0) :
    tot c' = tot c := by
  by_contra ht
  apply h
  rw [gammaKernelRect, perMinorRect, dif_neg ht, zero_div]

/-- The rectangular kernel packaged as a finitely supported function of
the target configuration. -/
noncomputable def gammaKernelFinsuppRect {d e : ℕ} (M : Matrix (Fin e) (Fin d) ℂ)
    (c : Config d) : Config e →₀ ℂ :=
  Finsupp.ofSupportFinite (fun c' => gammaKernelRect M c' c)
    (Set.Finite.subset (configsOfTot e (tot c)).finite_toSet fun c' hc' =>
      (mem_configsOfTot e (tot c) c').mpr (gammaKernelRect_ne_zero M hc'))

theorem gammaKernelFinsuppRect_apply {d e : ℕ} (M : Matrix (Fin e) (Fin d) ℂ)
    (c : Config d) (c' : Config e) :
    (gammaKernelFinsuppRect M c) c' = gammaKernelRect M c' c := by
  unfold gammaKernelFinsuppRect
  exact congrFun Finsupp.ofSupportFinite_coe c'

/-- The rectangular kernel of the padded inclusion is the indicator of
the embedded configuration. -/
theorem gammaKernelRect_pad {d e : ℕ} (h : d ≤ e) (c' : Config e) (c : Config d) :
    gammaKernelRect (padMatrixBos h) c' c
      = if c' = configEmb h c then 1 else 0 := by
  by_cases hEq : c' = configEmb h c
  · rw [if_pos hEq, gammaKernelRect, perMinorRect_pad, if_pos hEq]
    have hnorm : normFactor e (configEmb h c) = normFactor d c := by
      rw [normFactor, normFactor,
        prod_factorial_configEmb h c (fun n => (Nat.factorial n : ℝ)) (by simp)]
    rw [hEq, hnorm]
    have hsq : normFactor d c * normFactor d c
        = ∏ j, (Nat.factorial (c j) : ℝ) := by
      rw [normFactor, Real.mul_self_sqrt (by positivity)]
    have hnum : ((∏ j, Nat.factorial (c j) : ℕ) : ℂ)
        = ((normFactor d c * normFactor d c : ℝ) : ℂ) := by
      rw [hsq]
      norm_cast
    rw [hnum]
    refine div_self ?_
    have hpos : (0 : ℝ) < normFactor d c * normFactor d c := by
      rw [normFactor]
      positivity
    exact_mod_cast (ne_of_gt hpos)
  · rw [if_neg hEq, gammaKernelRect, perMinorRect_pad, if_neg hEq, zero_div]

/-- The rectangular coefficient operator: the widened form of Rung 10's
`gammaC`. -/
noncomputable def gammaCRect {d e : ℕ} (M : Matrix (Fin e) (Fin d) ℂ) :
    (Config d →₀ ℂ) →ₗ[ℂ] (Config e →₀ ℂ) :=
  Finsupp.linearCombination ℂ (gammaKernelFinsuppRect M)

/-- Rectangular Γ on bosonic Fock space, by conjugation with the
coordinate equivalences — the widened form of Rung 10's `gammaBos`. -/
noncomputable def gammaBosRect {d e : ℕ} (M : Matrix (Fin e) (Fin d) ℂ) :
    Dom d →ₗ[ℂ] Dom e :=
  (boseEquiv e).toLinearMap ∘ₗ (gammaCRect M ∘ₗ (boseRepr d).toLinearMap)

theorem gammaBosRect_apply {d e : ℕ} (M : Matrix (Fin e) (Fin d) ℂ) (x : Dom d) :
    gammaBosRect M x = boseEquiv e (gammaCRect M (boseRepr d x)) := rfl

theorem gammaBosRect_apply_basis {d e : ℕ} (M : Matrix (Fin e) (Fin d) ℂ)
    (c : Config d) :
    gammaBosRect M ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = boseEquiv e (gammaKernelFinsuppRect M c) := by
  rw [gammaBosRect_apply, boseRepr_basis, gammaCRect,
    Finsupp.linearCombination_single, one_smul]

/-- The padded kernel, as a finitely supported function, is the unit
single at the embedded configuration. -/
theorem gammaKernelFinsuppRect_pad {d e : ℕ} (h : d ≤ e) (c : Config d) :
    gammaKernelFinsuppRect (padMatrixBos h) c
      = Finsupp.single (configEmb h c) 1 := by
  ext c'
  rw [gammaKernelFinsuppRect_apply, gammaKernelRect_pad, Finsupp.single_apply]
  by_cases hcc : c' = configEmb h c
  · subst hcc
    simp
  · rw [if_neg hcc, if_neg (Ne.symm hcc)]

/-- The level embedding preserves the finite-particle domains. -/
theorem fockEmbBos_dom {d e : ℕ} (h : d ≤ e) (x : BosonicFock d)
    (hx : x ∈ Dom d) : fockEmbBos h x ∈ Dom e := by
  show onbEmb (boseHilbertBasis d) (boseE e ∘ ⇑(configEmb h))
      (boseE_comp_orthonormal h) x ∈ Dom e
  refine onbEmb_mem _ _ _ (s := Set.univ) (t := Dom e) ?_ ?_
  · intro c _
    exact Submodule.subset_span ⟨configEmb h c, rfl⟩
  · rw [Set.image_univ, boseHilbertBasis_coe]
    exact hx

/-- The level embedding as a map of finite-particle domains. -/
noncomputable def fockEmbBosDom {d e : ℕ} (h : d ≤ e) : Dom d →ₗ[ℂ] Dom e :=
  ((fockEmbBos h).toLinearMap.domRestrict (Dom d)).codRestrict (Dom e)
    (fun x => fockEmbBos_dom h x x.2)

theorem fockEmbBosDom_apply {d e : ℕ} (h : d ≤ e) (x : Dom d) :
    ((fockEmbBosDom h x : Dom e) : BosonicFock e)
      = fockEmbBos h (x : BosonicFock d) := rfl

/-- Coefficient transport at finite levels: the coefficients of the
embedded vector are the embedded coefficients. -/
theorem boseEquiv_embDomain {d e : ℕ} (h : d ≤ e) (l : Config d →₀ ℂ) :
    boseEquiv e (Finsupp.embDomain (configEmb h) l)
      = fockEmbBosDom h (boseEquiv d l) := by
  apply Subtype.ext
  show ((boseEquiv e (Finsupp.embDomain (configEmb h) l) : Dom e) : BosonicFock e)
      = fockEmbBos h ((boseEquiv d l : Dom d) : BosonicFock d)
  rw [boseEquiv_coe, boseEquiv_coe, Finsupp.linearCombination_apply,
    Finsupp.linearCombination_apply, embDomain_sum_transport]
  show (∑ c ∈ l.support, l c • boseE e (configEmb h c))
      = fockEmbBos h (∑ c ∈ l.support, l c • boseE d c)
  rw [show fockEmbBos h (∑ c ∈ l.support, l c • boseE d c)
      = (fockEmbBos h).toLinearMap (∑ c ∈ l.support, l c • boseE d c) from rfl,
    map_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  show l c • boseE e (configEmb h c)
      = (fockEmbBos h).toLinearMap (l c • boseE d c)
  rw [map_smul]
  show l c • boseE e (configEmb h c) = l c • fockEmbBos h (boseE d c)
  rw [fockEmbBos_basis]

/-- Coefficient computation of the padded rectangular Γ: it is exactly
coefficient transport along the configuration embedding. -/
theorem gammaCRect_pad_apply {d e : ℕ} (h : d ≤ e) (l : Config d →₀ ℂ)
    (c' : Config e) :
    (gammaCRect (padMatrixBos h) l) c'
      = (Finsupp.embDomain (configEmb h) l) c' := by
  rw [gammaCRect, Finsupp.linearCombination_apply, Finsupp.sum_apply]
  by_cases hex : ∃ c₀, configEmb h c₀ = c'
  · obtain ⟨c₀, hc₀⟩ := hex
    have hR : (Finsupp.embDomain (configEmb h) l) c' = l c₀ := by
      have hex' : ∃ a, (configEmb h) a = c' := ⟨c₀, hc₀⟩
      rw [Finsupp.embDomain_apply, dif_pos hex']
      have hchoose : (configEmb h) (Classical.choose hex') = c' :=
        Classical.choose_spec hex'
      have hinj : Classical.choose hex' = c₀ :=
        (configEmb h).injective (hchoose.trans hc₀.symm)
      exact congrArg l hinj
    rw [hR]
    show (∑ c ∈ l.support, (l c • gammaKernelFinsuppRect (padMatrixBos h) c) c')
        = l c₀
    rw [Finset.sum_eq_single c₀]
    · rw [Finsupp.smul_apply, gammaKernelFinsuppRect_apply, gammaKernelRect_pad,
        if_pos hc₀.symm, smul_eq_mul, mul_one]
    · intro c _ hc
      rw [Finsupp.smul_apply, gammaKernelFinsuppRect_apply, gammaKernelRect_pad,
        if_neg (fun hce => hc ((configEmb h).injective
          (hce.symm.trans hc₀.symm))), smul_eq_mul, mul_zero]
    · intro hns
      simp [Finsupp.smul_apply, Finsupp.notMem_support_iff.mp hns]
  · rw [Finsupp.embDomain_apply, dif_neg hex]
    show (∑ c ∈ l.support, (l c • gammaKernelFinsuppRect (padMatrixBos h) c) c')
        = 0
    apply Finset.sum_eq_zero
    intro c _
    rw [Finsupp.smul_apply, gammaKernelFinsuppRect_apply, gammaKernelRect_pad,
      if_neg (fun hce => hex ⟨c, hce.symm⟩), smul_eq_mul, mul_zero]

/-- **Task 3a (bosons), operator form.**  The level embedding *is* second
quantization of the padded inclusion: as a map of finite-particle
domains, `fockEmbBosDom h` equals the rectangular Γ-operator of
`padMatrixBos h`. -/
theorem gammaBosRect_pad {d e : ℕ} (h : d ≤ e) :
    gammaBosRect (padMatrixBos h) = fockEmbBosDom h := by
  have htrans : ∀ x : Dom d, boseRepr e (fockEmbBosDom h x)
      = Finsupp.embDomain (configEmb h) (boseRepr d x) := by
    intro x
    apply (boseEquiv e).injective
    show (boseEquiv e) ((boseEquiv e).symm (fockEmbBosDom h x))
        = (boseEquiv e) (Finsupp.embDomain (configEmb h) (boseRepr d x))
    rw [LinearEquiv.apply_symm_apply]
    show fockEmbBosDom h x
        = boseEquiv e (Finsupp.embDomain (configEmb h) (boseRepr d x))
    rw [boseEquiv_embDomain]
    show fockEmbBosDom h x
        = fockEmbBosDom h ((boseEquiv d) ((boseEquiv d).symm x))
    rw [LinearEquiv.apply_symm_apply]
  have hgam : ∀ x : Dom d, boseRepr e (gammaBosRect (padMatrixBos h) x)
      = gammaCRect (padMatrixBos h) (boseRepr d x) := by
    intro x
    show (boseEquiv e).symm (boseEquiv e
        (gammaCRect (padMatrixBos h) (boseRepr d x))) = _
    exact LinearEquiv.symm_apply_apply _ _
  apply LinearMap.ext
  intro x
  apply (boseRepr e).injective
  rw [hgam, htrans]
  ext c'
  exact gammaCRect_pad_apply h (boseRepr d x) c'

/-- Basis form of Task 3a (bosons): the padded Γ sends basis vector to
basis vector exactly as the level embedding does. -/
theorem gammaBosRect_pad_basis {d e : ℕ} (h : d ≤ e) (c : Config d) :
    gammaBosRect (padMatrixBos h)
        ⟨boseE d c, Submodule.subset_span (Set.mem_range_self c)⟩
      = ⟨boseE e (configEmb h c),
          Submodule.subset_span (Set.mem_range_self _)⟩ := by
  rw [gammaBosRect_apply_basis, gammaKernelFinsuppRect_pad, boseEquiv_basis]

/-! ## Task 4a (bosons): the union characterization -/

/-- **Task 4a (bosons).**  The limit finite-particle domain is exactly
the union (supremum) over all finite levels of the embedded finite
domains: every limit configuration factors through a finite level
(`config_factor`), and each embedded finite domain lands in the limit
domain (`fockEmbBosLim_dom`).  Note the finite *domains* `Dom d` appear
on the right, not the full finite Fock spaces — the bosonic asymmetry
recorded in the scoping. -/
theorem DomLim_eq_iSup_map :
    DomLim = ⨆ d : ℕ, (Dom d).map (fockEmbBosLim d).toLinearMap := by
  apply le_antisymm
  · rw [DomLim, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    obtain ⟨d, c₀, hc₀⟩ := config_factor c
    apply Submodule.mem_iSup_of_mem d
    rw [← hc₀, ← fockEmbBosLim_basis]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨c₀, rfl⟩)
  · apply iSup_le
    intro d
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    exact fockEmbBosLim_dom d x hx

/-- Density of the union, restated: the closure of the supremum of the
embedded finite domains is everything (Campaign A proved this for
`DomLim` itself). -/
theorem bos_iSup_map_topologicalClosure :
    (⨆ d : ℕ, (Dom d).map (fockEmbBosLim d).toLinearMap).topologicalClosure
      = ⊤ := by
  rw [← DomLim_eq_iSup_map]
  exact DomLim_topologicalClosure

/-! ## Task 5 (bosons): diagonal dΓ in the limit -/

/-- Linear independence of the limit basis family (from orthonormality). -/
theorem boseELim_linIndep : LinearIndependent ℂ boseELim :=
  boseELim_orthonormal.linearIndependent

/-- The coordinate equivalence between finitely supported coefficient
functions on limit configurations and the limit domain — the limit form
of the finite `boseEquiv`-style basis equivalence. -/
noncomputable def bosEquivLim : (ConfigLim →₀ ℂ) ≃ₗ[ℂ] DomLim :=
  boseELim_linIndep.linearCombinationEquiv

/-- The coefficient (representation) equivalence, inverse of
`bosEquivLim`. -/
noncomputable def bosReprLim : DomLim ≃ₗ[ℂ] (ConfigLim →₀ ℂ) :=
  bosEquivLim.symm

theorem bosEquivLim_basis (c : ConfigLim) :
    bosEquivLim (Finsupp.single c 1)
      = ⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩ := by
  have h : boseELim_linIndep.repr ⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩
      = Finsupp.single c 1 :=
    LinearIndependent.repr_eq_single _ _ _ rfl
  have h2 : bosEquivLim (boseELim_linIndep.repr
        ⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩)
      = ⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩ := by
    show boseELim_linIndep.linearCombinationEquiv
        (boseELim_linIndep.linearCombinationEquiv.symm _) = _
    exact LinearEquiv.apply_symm_apply _ _
  rw [h] at h2
  exact h2

theorem bosReprLim_basis (c : ConfigLim) :
    bosReprLim ⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩
      = Finsupp.single c 1 := by
  rw [bosReprLim, LinearEquiv.symm_apply_eq]
  exact (bosEquivLim_basis c).symm

theorem bosEquivLim_coe (l : ConfigLim →₀ ℂ) :
    ((bosEquivLim l : DomLim) : BosonicFockLim)
      = Finsupp.linearCombination ℂ boseELim l := rfl

/-- The eigenvalue of a diagonal one-particle operator with eigenvalue
function `a` on the configuration `c`: the `a`-weighted total
`c.sum (fun i n => a i * n)`. -/
def bosEigLim (a : ℕ → ℂ) (c : ConfigLim) : ℂ :=
  c.sum (fun i n => a i * (n : ℂ))

/-- The diagonal action on coefficient functions: multiply the
`c`-coefficient by the eigenvalue `bosEigLim a c`. -/
noncomputable def diagFinsuppBos (a : ℕ → ℂ) :
    (ConfigLim →₀ ℂ) →ₗ[ℂ] (ConfigLim →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun c => bosEigLim a c • Finsupp.single c 1)

theorem diagFinsuppBos_apply (a : ℕ → ℂ) (f : ConfigLim →₀ ℂ)
    (c' : ConfigLim) :
    (diagFinsuppBos a f) c' = bosEigLim a c' * f c' := by
  rw [diagFinsuppBos, Finsupp.linearCombination_apply, Finsupp.sum_apply]
  show (∑ c ∈ f.support, (f c • (bosEigLim a c • Finsupp.single c 1)) c')
      = bosEigLim a c' * f c'
  rw [Finset.sum_eq_single c']
  · rw [Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.single_apply, if_pos rfl,
      smul_eq_mul, smul_eq_mul, mul_one]
    exact mul_comm _ _
  · intro c _ hc
    rw [Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.single_apply, if_neg hc]
    simp
  · intro hc'
    have hf : f c' = 0 := Finsupp.notMem_support_iff.mp hc'
    rw [hf]
    simp [Finsupp.smul_apply]

/-- **Diagonal dΓ in the limit (bosons).**  For an eigenvalue function
`a : ℕ → ℂ`, `dGammaLimBos a` is the diagonal second quantization on the
limit domain: it multiplies the `c`-coefficient by
`c.sum (fun i n => a i * n)`.  Only the diagonal family is in this pitch;
dΓ of a general one-particle operator in the limit is not attempted. -/
noncomputable def dGammaLimBos (a : ℕ → ℂ) : DomLim →ₗ[ℂ] DomLim :=
  bosEquivLim.toLinearMap ∘ₗ (diagFinsuppBos a ∘ₗ bosReprLim.toLinearMap)

/-- Basis vectors are eigenvectors of the limit diagonal dΓ, with the
expected eigenvalue. -/
theorem dGammaLimBos_basis (a : ℕ → ℂ) (c : ConfigLim) :
    dGammaLimBos a ⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩
      = bosEigLim a c • ⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩ := by
  have hdiag : diagFinsuppBos a (Finsupp.single c 1)
      = bosEigLim a c • Finsupp.single c 1 := by
    ext c'
    rw [diagFinsuppBos_apply, Finsupp.smul_apply, Finsupp.single_apply]
    by_cases h : c = c' <;> simp [h, smul_eq_mul]
  show bosEquivLim (diagFinsuppBos a
      (bosReprLim ⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩)) = _
  rw [bosReprLim_basis, hdiag, map_smul, bosEquivLim_basis]

/-- The coefficient formula for the limit diagonal dΓ. -/
theorem dGammaLimBos_coord (a : ℕ → ℂ) (x : DomLim) (c : ConfigLim) :
    (bosReprLim (dGammaLimBos a x)) c = bosEigLim a c * (bosReprLim x) c := by
  have h : bosReprLim (dGammaLimBos a x)
      = diagFinsuppBos a (bosReprLim x) := by
    show bosEquivLim.symm (bosEquivLim (diagFinsuppBos a (bosReprLim x)))
      = diagFinsuppBos a (bosReprLim x)
    exact LinearEquiv.symm_apply_apply _ _
  rw [h, diagFinsuppBos_apply]

/-- Expansion of a domain vector in the limit basis (finite sum over the
support of its coefficient function). -/
theorem bosDomLim_expand (x : DomLim) :
    x = ∑ c ∈ (bosReprLim x).support, (bosReprLim x) c
      • (⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩ : DomLim) := by
  apply bosReprLim.injective
  rw [map_sum]
  simp_rw [map_smul, bosReprLim_basis]
  conv_lhs => rw [← Finsupp.sum_single (bosReprLim x)]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The inner product with a basis vector reads off the (conjugated)
coefficient: the vacuum-orthogonality content used in Task 6. -/
theorem bosInner_basis (x : DomLim) (c : ConfigLim) :
    ⟪x, (⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩ : DomLim)⟫_ℂ
      = starRingEnd ℂ ((bosReprLim x) c) := by
  calc ⟪x, (⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩ : DomLim)⟫_ℂ
      = ∑ c' ∈ (bosReprLim x).support, starRingEnd ℂ ((bosReprLim x) c')
          * ⟪(⟨boseELim c', Submodule.subset_span ⟨c', rfl⟩⟩ : DomLim),
              (⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩ : DomLim)⟫_ℂ := by
        conv_lhs => rw [bosDomLim_expand x]
        rw [sum_inner]
        refine Finset.sum_congr rfl (fun c' _ => ?_)
        exact inner_smul_left
          (⟨boseELim c', Submodule.subset_span ⟨c', rfl⟩⟩ : DomLim)
          (⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩ : DomLim)
          ((bosReprLim x) c')
    _ = starRingEnd ℂ ((bosReprLim x) c)
          * ⟪(⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩ : DomLim),
              (⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩ : DomLim)⟫_ℂ := by
        refine Finset.sum_eq_single c (fun c' _ hc' => ?_) (fun hc => ?_)
        · simp [boseELim_inner, hc']
        · rw [Finsupp.notMem_support_iff.mp hc]
          simp
    _ = starRingEnd ℂ ((bosReprLim x) c) := by
        have hnorm : ‖boseELim c‖ = 1 := boseELim_orthonormal.1 c
        simp [hnorm]

/-- Coefficient expansion of the inner product over any finset covering
the support of the first vector's coefficients. -/
theorem bosInner_expand_of_subset (u v : DomLim) (U : Finset ConfigLim)
    (hU : (bosReprLim u).support ⊆ U) :
    ⟪u, v⟫_ℂ = ∑ c ∈ U, starRingEnd ℂ ((bosReprLim u) c)
      * (bosReprLim v) c := by
  have hbase : ⟪u, v⟫_ℂ = ∑ c ∈ (bosReprLim u).support,
      starRingEnd ℂ ((bosReprLim u) c) * (bosReprLim v) c := by
    conv_lhs => rw [bosDomLim_expand u]
    rw [sum_inner]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    have hTS : ⟪(⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩
          : DomLim), v⟫_ℂ
        = (starRingEnd ℂ) (⟪v, (⟨boseELim c,
            Submodule.subset_span ⟨c, rfl⟩⟩ : DomLim)⟫_ℂ) :=
      (RCLike.conj_conj _).symm.trans (congrArg (starRingEnd ℂ)
        (inner_conj_symm v
          (⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩ : DomLim)))
    calc ⟪(bosReprLim u) c • (⟨boseELim c,
              Submodule.subset_span ⟨c, rfl⟩⟩ : DomLim), v⟫_ℂ
        = (starRingEnd ℂ) ((bosReprLim u) c)
            * ⟪(⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩
                : DomLim), v⟫_ℂ :=
          inner_smul_left
            (⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩ : DomLim) v
            ((bosReprLim u) c)
      _ = (starRingEnd ℂ) ((bosReprLim u) c) * (bosReprLim v) c := by
          congr 1
          exact hTS.trans ((congrArg (starRingEnd ℂ)
            (bosInner_basis v c)).trans (RCLike.conj_conj _))
  rw [hbase]
  exact Finset.sum_subset hU (fun c _ hc => by
    rw [Finsupp.notMem_support_iff.mp hc]
    simp)

/-- The finite-level diagonal matrix of the eigenvalue function `a` at
level `d`: mode `j` carries eigenvalue `a j`. -/
noncomputable def diagABos (d : ℕ) (a : ℕ → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun j : Fin d => a (j : ℕ))

/-- The level-`d` domain map: the limit embedding, viewed as a map of
finite-particle domains. -/
noncomputable def bosDomMap (d : ℕ) : Dom d →ₗ[ℂ] DomLim :=
  ((fockEmbBosLim d).toLinearMap.domRestrict (Dom d)).codRestrict DomLim
    (fun x => fockEmbBosLim_dom d x x.2)

theorem bosDomMap_apply (d : ℕ) (x : Dom d) :
    ((bosDomMap d x : DomLim) : BosonicFockLim)
      = fockEmbBosLim d (x : BosonicFock d) := rfl

/-- Coefficient transport to the limit: the coefficients of the embedded
domain vector are the embedded coefficients. -/
theorem bosEquivLim_embDomain (d : ℕ) (l : Config d →₀ ℂ) :
    bosEquivLim (Finsupp.embDomain (configEmbLim d) l)
      = bosDomMap d (boseEquiv d l) := by
  apply Subtype.ext
  show ((bosEquivLim (Finsupp.embDomain (configEmbLim d) l) : DomLim)
      : BosonicFockLim)
    = fockEmbBosLim d ((boseEquiv d l : Dom d) : BosonicFock d)
  rw [bosEquivLim_coe, boseEquiv_coe, Finsupp.linearCombination_apply,
    Finsupp.linearCombination_apply, embDomain_sum_transport]
  show (∑ c ∈ l.support, l c • boseELim (configEmbLim d c))
      = fockEmbBosLim d (∑ c ∈ l.support, l c • boseE d c)
  rw [show fockEmbBosLim d (∑ c ∈ l.support, l c • boseE d c)
      = (fockEmbBosLim d).toLinearMap (∑ c ∈ l.support, l c • boseE d c)
      from rfl, map_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  show l c • boseELim (configEmbLim d c)
      = (fockEmbBosLim d).toLinearMap (l c • boseE d c)
  rw [map_smul]
  show l c • boseELim (configEmbLim d c) = l c • fockEmbBosLim d (boseE d c)
  rw [fockEmbBosLim_basis]

/-- The coefficients of the embedded domain vector are the embedded
coefficients. -/
theorem bosReprLim_bosDomMap (d : ℕ) (x : Dom d) :
    bosReprLim (bosDomMap d x)
      = Finsupp.embDomain (configEmbLim d) (boseRepr d x) := by
  apply (bosEquivLim).injective
  show bosEquivLim ((bosEquivLim).symm (bosDomMap d x))
      = bosEquivLim (Finsupp.embDomain (configEmbLim d) (boseRepr d x))
  rw [LinearEquiv.apply_symm_apply]
  show bosDomMap d x
      = bosEquivLim (Finsupp.embDomain (configEmbLim d) (boseRepr d x))
  rw [bosEquivLim_embDomain]
  show bosDomMap d x
      = bosDomMap d ((boseEquiv d) ((boseEquiv d).symm x))
  rw [LinearEquiv.apply_symm_apply]

/-- The eigenvalue transports along the embedding: the `a`-weighted total
of the embedded configuration is the finite-level `a`-weighted sum. -/
theorem bosEigLim_configEmbLim (a : ℕ → ℂ) (d : ℕ) (c : Config d) :
    bosEigLim a (configEmbLim d c)
      = ∑ j : Fin d, a (j : ℕ) * ((c j : ℕ) : ℂ) := by
  rw [bosEigLim, configEmbLim_apply, embDomain_sum_transport]
  exact Finsupp.sum_fintype _ _ (fun j => by simp)

/-- The diagonal action commutes with coefficient transport, pointwise:
at the embedded configuration the eigenvalue is the finite one
(`bosEigLim_configEmbLim` against `dgammaC_diag_apply`); off the range
both sides vanish. -/
theorem diagFinsuppBos_embDomain_apply (a : ℕ → ℂ) (d : ℕ)
    (l : Config d →₀ ℂ) (c' : ConfigLim) :
    (diagFinsuppBos a (Finsupp.embDomain (configEmbLim d) l)) c'
      = (Finsupp.embDomain (configEmbLim d)
          (dgammaC d (diagABos d a) l)) c' := by
  rw [diagFinsuppBos_apply]
  by_cases hex : ∃ c₀, configEmbLim d c₀ = c'
  · obtain ⟨c₀, hc₀⟩ := hex
    have hR : ∀ f : Config d →₀ ℂ,
        (Finsupp.embDomain (configEmbLim d) f) c' = f c₀ := by
      intro f
      have hex' : ∃ a_1, (configEmbLim d) a_1 = c' := ⟨c₀, hc₀⟩
      rw [Finsupp.embDomain_apply, dif_pos hex']
      have hchoose : (configEmbLim d) (Classical.choose hex') = c' :=
        Classical.choose_spec hex'
      have hinj : Classical.choose hex' = c₀ :=
        (configEmbLim d).injective (hchoose.trans hc₀.symm)
      exact congrArg f hinj
    rw [hR l, hR (dgammaC d (diagABos d a) l), diagABos,
      dgammaC_diag_apply, ← hc₀, bosEigLim_configEmbLim]
  · have hz : ∀ f : Config d →₀ ℂ,
        (Finsupp.embDomain (configEmbLim d) f) c' = 0 := by
      intro f
      rw [Finsupp.embDomain_apply, dif_neg hex]
    rw [hz, hz, mul_zero]

/-- **Task 5 compatibility (bosons).**  The limit diagonal dΓ restricts
along the level-`d` embedding to the finite diagonal dΓ: the diagram
commutes on the nose. -/
theorem dGammaLimBos_compat (a : ℕ → ℂ) (d : ℕ) :
    (dGammaLimBos a) ∘ₗ (bosDomMap d)
      = (bosDomMap d) ∘ₗ (dgammaBos d (diagABos d a)) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  apply bosReprLim.injective
  have e1 : bosReprLim (dGammaLimBos a (bosDomMap d x))
      = diagFinsuppBos a (bosReprLim (bosDomMap d x)) := by
    show bosEquivLim.symm (bosEquivLim
        (diagFinsuppBos a (bosReprLim (bosDomMap d x))))
      = diagFinsuppBos a (bosReprLim (bosDomMap d x))
    exact LinearEquiv.symm_apply_apply _ _
  have e2 : bosReprLim (bosDomMap d (dgammaBos d (diagABos d a) x))
      = Finsupp.embDomain (configEmbLim d)
          (dgammaC d (diagABos d a) (boseRepr d x)) := by
    rw [bosReprLim_bosDomMap, repr_dgammaBos]
  rw [e1, e2, bosReprLim_bosDomMap]
  ext c'
  exact diagFinsuppBos_embDomain_apply a d (boseRepr d x) c'

/-- The eigenvalue of the number operator: the total particle number. -/
theorem bosEigLim_one (c : ConfigLim) :
    bosEigLim (fun _ => (1 : ℂ)) c = ((totLim c : ℕ) : ℂ) := by
  rw [bosEigLim, totLim]
  show (∑ i ∈ c.support, (1 : ℂ) * ((c i : ℕ) : ℂ))
      = ((∑ i ∈ c.support, c i : ℕ) : ℂ)
  rw [Nat.cast_sum]
  exact Finset.sum_congr rfl (fun i _ => one_mul _)

/-- **The number operator in the limit (bosons)**: the `a ≡ 1` case of
the limit diagonal dΓ. -/
noncomputable def numberOpLimBos : DomLim →ₗ[ℂ] DomLim :=
  dGammaLimBos (fun _ => 1)

theorem numberOpLimBos_basis (c : ConfigLim) :
    numberOpLimBos ⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩
      = ((totLim c : ℕ) : ℂ)
        • ⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩ := by
  rw [numberOpLimBos, dGammaLimBos_basis]
  congr 1
  exact bosEigLim_one c

/-- The limit number operator restricts to the finite number operator at
every level (via `dgammaBos_one`). -/
theorem numberOpLimBos_compat (d : ℕ) :
    numberOpLimBos ∘ₗ (bosDomMap d) = (bosDomMap d) ∘ₗ (numberOp d) := by
  have h1 : diagABos d (fun _ => (1 : ℂ)) = 1 := by
    rw [diagABos, Matrix.diagonal_one]
  calc numberOpLimBos ∘ₗ (bosDomMap d)
      = (dGammaLimBos (fun _ => 1)) ∘ₗ (bosDomMap d) := rfl
    _ = (bosDomMap d) ∘ₗ (dgammaBos d (diagABos d (fun _ => (1 : ℂ)))) :=
        dGammaLimBos_compat (fun _ => 1) d
    _ = (bosDomMap d) ∘ₗ (numberOp d) := by rw [h1, dgammaBos_one]

/-- The vacuum is annihilated by every limit diagonal dΓ. -/
theorem dGammaLimBos_vacuum (a : ℕ → ℂ) :
    dGammaLimBos a ⟨boseVacLim, Submodule.subset_span ⟨0, rfl⟩⟩ = 0 := by
  show dGammaLimBos a ⟨boseELim 0, Submodule.subset_span ⟨0, rfl⟩⟩ = 0
  rw [dGammaLimBos_basis]
  simp [bosEigLim]

/-! ## Task 6 (bosons): the free gap in the limit -/

/-- The real eigenvalue of the limit free Hamiltonian on a
configuration: the `ω`-weighted total particle count. -/
def bosEigReal (ω : ℕ → ℝ) (c : ConfigLim) : ℝ :=
  c.sum (fun i n => ω i * (n : ℝ))

/-- Real-cast coherence of the limit eigenvalues. -/
theorem bosEigLim_ofReal (ω : ℕ → ℝ) (c : ConfigLim) :
    bosEigLim (fun i => (ω i : ℂ)) c = ((bosEigReal ω c : ℝ) : ℂ) := by
  show (∑ i ∈ c.support, ((ω i : ℂ)) * ((c i : ℕ) : ℂ))
      = ((∑ i ∈ c.support, ω i * ((c i : ℕ) : ℝ) : ℝ) : ℂ)
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun i _ => by norm_cast)

/-- **The limit free Hamiltonian (bosons)**: diagonal dΓ of the
single-mode energies `ω`. -/
noncomputable def freeHamiltonianLimBos (ω : ℕ → ℝ) :
    DomLim →ₗ[ℂ] DomLim :=
  dGammaLimBos (fun i => (ω i : ℂ))

theorem freeHamiltonianLimBos_basis (ω : ℕ → ℝ) (c : ConfigLim) :
    freeHamiltonianLimBos ω ⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩
      = ((bosEigReal ω c : ℝ) : ℂ)
        • ⟨boseELim c, Submodule.subset_span ⟨c, rfl⟩⟩ := by
  rw [freeHamiltonianLimBos, dGammaLimBos_basis]
  congr 1
  exact bosEigLim_ofReal ω c

/-- Vacuum eigenvalue `0` for the limit free Hamiltonian. -/
theorem freeHamiltonianLimBos_vacuum (ω : ℕ → ℝ) :
    freeHamiltonianLimBos ω ⟨boseVacLim, Submodule.subset_span ⟨0, rfl⟩⟩
      = 0 :=
  dGammaLimBos_vacuum (fun i => (ω i : ℂ))

/-- The gap dichotomy on basis vectors, Δ-general: every basis
eigenvalue is `0` or `≥ Δ`. -/
theorem free_gap_dichotomy_lim_bos (ω : ℕ → ℝ) (Δ : ℝ) (hΔ : 0 < Δ)
    (hω : ∀ i, Δ ≤ ω i) (c : ConfigLim) :
    bosEigReal ω c = 0 ∨ Δ ≤ bosEigReal ω c := by
  by_cases hc : c = 0
  · refine Or.inl ?_
    rw [hc]
    simp [bosEigReal]
  · obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra h
      apply hc
      ext j
      by_contra hj
      exact h ⟨j, hj⟩
    have hterm : ω i * ((c i : ℕ) : ℝ) ≤ bosEigReal ω c := by
      show ω i * ((c i : ℕ) : ℝ) ≤ ∑ j ∈ c.support, ω j * ((c j : ℕ) : ℝ)
      exact Finset.single_le_sum
        (fun j _ => mul_nonneg (hΔ.le.trans (hω j)) (Nat.cast_nonneg _))
        (Finsupp.mem_support_iff.mpr hi)
    have hci : (1 : ℝ) ≤ ((c i : ℕ) : ℝ) :=
      Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hi)
    refine Or.inr (le_trans (le_trans (hω i)
      (le_mul_of_one_le_right (hΔ.le.trans (hω i)) hci)) hterm)

/-- The gap dichotomy at the tasked normalization `Δ = 1`. -/
theorem free_gap_dichotomy_lim_bos_one (ω : ℕ → ℝ) (hω : ∀ i, 1 ≤ ω i)
    (c : ConfigLim) :
    bosEigReal ω c = 0 ∨ 1 ≤ bosEigReal ω c :=
  free_gap_dichotomy_lim_bos ω 1 one_pos hω c

/-- The coordinate formula for the limit free Hamiltonian. -/
theorem freeHamiltonianLimBos_coord (ω : ℕ → ℝ) (x : DomLim)
    (c : ConfigLim) :
    (bosReprLim (freeHamiltonianLimBos ω x)) c
      = ((bosEigReal ω c : ℝ) : ℂ) * (bosReprLim x) c := by
  rw [freeHamiltonianLimBos, dGammaLimBos_coord]
  congr 1
  exact bosEigLim_ofReal ω c

/-- Eigenvalue extraction in the limit, Δ-general: a nonzero
eigenvector on the domain has eigenvalue `((bosEigReal ω c : ℝ) : ℂ)`
for some configuration `c`, and that real eigenvalue is `0` or `≥ Δ`.
This is the eigenvalue-on-finite-particle-domain gap of Rungs 9–10, at
countably many modes. -/
theorem freeHamiltonianLimBos_eigenvalue_gap (ω : ℕ → ℝ) (Δ : ℝ)
    (hΔ : 0 < Δ) (hω : ∀ i, Δ ≤ ω i) (ψ : DomLim) (hψ : ψ ≠ 0) (μ : ℂ)
    (hμ : freeHamiltonianLimBos ω ψ = μ • ψ) :
    ∃ c : ConfigLim, μ = ((bosEigReal ω c : ℝ) : ℂ)
      ∧ (bosEigReal ω c = 0 ∨ Δ ≤ bosEigReal ω c)
      ∧ (bosReprLim ψ) c ≠ 0 := by
  obtain ⟨c, hc⟩ : ∃ c, (bosReprLim ψ) c ≠ 0 := by
    by_contra h
    apply hψ
    have hz : bosReprLim ψ = 0 := by
      ext T
      by_contra hT
      exact h ⟨T, hT⟩
    have hψ0 : ψ = bosEquivLim (bosReprLim ψ) :=
      (LinearEquiv.apply_symm_apply bosEquivLim ψ).symm
    rw [hz, map_zero] at hψ0
    exact hψ0
  refine ⟨c, ?_, free_gap_dichotomy_lim_bos ω Δ hΔ hω c, hc⟩
  have hcoord := freeHamiltonianLimBos_coord ω ψ c
  have hcoord2 : (bosReprLim (freeHamiltonianLimBos ω ψ)) c
      = μ * (bosReprLim ψ) c := by
    rw [hμ, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact (mul_right_cancel₀ hc (hcoord.symm.trans hcoord2)).symm

/-- **The limit free gap (bosons), orthogonality form, `Δ = 1`.**  A
nonzero eigenvector on the domain that is orthogonal to the vacuum has
eigenvalue `≥ 1`.  Gap in the eigenvalue-on-finite-particle-domain
sense of Rungs 9–10; the spectral statement is priced, unattempted. -/
theorem freeHamiltonianLimBos_gap_of_orth (ω : ℕ → ℝ) (hω : ∀ i, 1 ≤ ω i)
    (ψ : DomLim) (hψ : ψ ≠ 0) (μ : ℝ)
    (hμ : freeHamiltonianLimBos ω ψ = (μ : ℂ) • ψ)
    (horth : ⟪ψ, (⟨boseVacLim,
      Submodule.subset_span ⟨0, rfl⟩⟩ : DomLim)⟫_ℂ = 0) :
    1 ≤ μ := by
  obtain ⟨c, hμS, hdich, hcne⟩ :=
    freeHamiltonianLimBos_eigenvalue_gap ω 1 one_pos hω ψ hψ (μ : ℂ) hμ
  have hμR : μ = bosEigReal ω c := by
    have hre := congrArg Complex.re hμS
    simpa using hre
  rcases hdich with h0 | h1
  · exfalso
    have hc0 : c = 0 := by
      by_contra hc
      obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
        by_contra h
        apply hc
        ext j
        by_contra hj
        exact h ⟨j, hj⟩
      have hterm : ω i * ((c i : ℕ) : ℝ) ≤ bosEigReal ω c := by
        show ω i * ((c i : ℕ) : ℝ) ≤ ∑ j ∈ c.support, ω j * ((c j : ℕ) : ℝ)
        exact Finset.single_le_sum
          (fun j _ => mul_nonneg (zero_le_one.trans (hω j)) (Nat.cast_nonneg _))
          (Finsupp.mem_support_iff.mpr hi)
      have hci : (1 : ℝ) ≤ ((c i : ℕ) : ℝ) :=
        Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hi)
      have hge : (1 : ℝ) ≤ bosEigReal ω c :=
        le_trans (le_trans (hω i)
          (le_mul_of_one_le_right (zero_le_one.trans (hω i)) hci)) hterm
      rw [h0] at hge
      exact (by norm_num : ¬ (1 : ℝ) ≤ 0) hge
    have hcoef : (bosReprLim ψ) 0 ≠ 0 := hc0 ▸ hcne
    have horth' : ⟪ψ, (⟨boseELim 0,
        Submodule.subset_span ⟨0, rfl⟩⟩ : DomLim)⟫_ℂ = 0 := horth
    rw [bosInner_basis] at horth'
    have hz : (bosReprLim ψ) 0 = 0 := by
      apply (starRingEnd ℂ).injective
      rw [horth', map_zero]
    exact hcoef hz
  · rw [hμR]
    exact h1

/-- Self-adjointness of the limit free Hamiltonian on the domain
(expectation-form symmetry, as in the finite theory). -/
theorem freeHamiltonianLimBos_selfadjoint (ω : ℕ → ℝ) (x y : DomLim) :
    ⟪freeHamiltonianLimBos ω x, y⟫_ℂ
      = ⟪x, freeHamiltonianLimBos ω y⟫_ℂ := by
  classical
  set U := (bosReprLim x).support ∪ (bosReprLim y).support
    ∪ (bosReprLim (freeHamiltonianLimBos ω x)).support
    ∪ (bosReprLim (freeHamiltonianLimBos ω y)).support with hU
  have hsub1 : (bosReprLim (freeHamiltonianLimBos ω x)).support ⊆ U := by
    intro c hc
    simp only [hU, Finset.mem_union]
    exact Or.inl (Or.inr hc)
  have hsub2 : (bosReprLim x).support ⊆ U := by
    intro c hc
    simp only [hU, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl hc))
  rw [bosInner_expand_of_subset _ _ U hsub1,
    bosInner_expand_of_subset _ _ U hsub2]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have hconj : ∀ r : ℝ, (starRingEnd ℂ) ((r : ℂ)) = (r : ℂ) :=
    fun r => RCLike.conj_ofReal r
  rw [freeHamiltonianLimBos_coord, freeHamiltonianLimBos_coord, map_mul,
    hconj]
  ring

end ThetLogos
