import ThetLogos.StoneFiniteDim
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace ThetLogos

open scoped InnerProductSpace Function

/-!
# ThetLogos.StoneFiniteDim2 — Rung 7 Prong 3: Stone/ONB, induction strategy (2026-10-11)

Discharges the honest gaps left in `StoneFiniteDim.lean` (Rung 6, PARTIAL verdict):
the full finite-dimensional Stone's theorem (`stone_finiteDim`) and the explicit
joint spectral orthonormal basis (`jointSpectral_orthonormalBasis`).

## Strategy (why this avoids the timeouts)
The Rung-6 attempt assembled the ONB by concatenating orthonormal bases over
*all* nontrivial joint eigenspaces at once, indexed by the sigma type
`Σ χ, Fin (dim χ)` — and hit Lean universe/whnf timeouts in elaboration.
This file uses genuinely different proof strategies with no sigma types anywhere:

- **Joint ONB (`jointONB_aux`)**: induction on `Module.finrank ℂ H`.  At each step,
  Mathlib's joint-eigenspace decomposition (`iSup_iInf_eq_top_of_commute`) supplies
  *one* nontrivial joint eigenspace; take a unit joint eigenvector `v`, restrict the
  family to `(span {v})ᗮ`, recurse.  The basis is assembled with `Fin.cons`
  (`Fin (n+1)`), never a sigma type.
- **Stone (`stone_finiteDim`)**: split each unitary `U t` into self-adjoint real
  and imaginary parts — a commuting family indexed by `ℝ ⊕ ℝ` — diagonalize it with
  the joint ONB, and read off a continuous character `ℝ → ℂ` on each basis vector.
  `continuous_char_lift` (Rung 6, T1) identifies each character as
  `t ↦ exp (i * a * t)`; the frequencies reassemble into the skew-adjoint generator.

## Tier ledger
T1 (proved, zero sorrys): `jointONB_aux`, `jointSpectral_orthonormalBasis`,
  `stone_finiteDim`.
T2 (interface): `IsSkewAdjoint` (definition for the Stone generator).
-/

-- ============================================================================
-- §A. Joint spectral ONB by induction on finrank (no sigma types)
-- ============================================================================

/-- **Simultaneous diagonalization, by induction on `finrank` (T1).**

    A commuting family of symmetric operators on a finite-dimensional inner
    product space admits an orthonormal basis of joint eigenvectors, indexed by
    `Fin (finrank)`, with eigenvalues `μ`.  The induction peels off one joint
    eigenvector at a time (from Mathlib's joint-eigenspace decomposition) and
    recurses on the orthogonal complement — no sigma-type concatenation. -/
theorem jointONB_aux : ∀ (n : ℕ) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H], Module.finrank ℂ H = n →
    ∀ {ι : Type*} (T : ι → H →ₗ[ℂ] H),
    (∀ i, (T i).IsSymmetric) → (∀ i j, Commute (T i) (T j)) →
    ∃ (b : Fin n → H) (μ : Fin n → ι → ℂ),
      Orthonormal ℂ b ∧ ∀ i k, T i (b k) = μ k i • b k := by
  intro n
  induction n with
  | zero =>
      intro H _ _ _ _ ι T _ _
      exact ⟨fun k => k.elim0, fun k => k.elim0,
        ⟨fun k => k.elim0, fun i j _ => i.elim0⟩, fun i k => k.elim0⟩
  | succ n IH =>
      intro H _ _ _ hfin ι T hsymm hcomm
      have hdec := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute (𝕜 := ℂ) (E := H)
        hsymm (fun i j _ => hcomm i j)
      -- some joint eigenspace is nontrivial
      obtain ⟨χ, hχnt⟩ : ∃ χ : ι → ℂ,
          Nontrivial ↥(⨅ i, Module.End.eigenspace (T i) (χ i)) := by
        by_contra hcon
        have hss : ∀ χ : ι → ℂ,
            Subsingleton ↥(⨅ i, Module.End.eigenspace (T i) (χ i)) := by
          intro χ
          rw [← not_nontrivial_iff_subsingleton]
          exact fun hnt => hcon ⟨χ, hnt⟩
        have hbot : ∀ χ : ι → ℂ, (⨅ i, Module.End.eigenspace (T i) (χ i)) = ⊥ := by
          intro χ
          rw [eq_bot_iff]
          intro x hx
          rw [Submodule.mem_bot ℂ]
          have h0 : (⟨x, hx⟩ : ↥(⨅ i, Module.End.eigenspace (T i) (χ i))) = 0 :=
            @Subsingleton.elim _ (hss χ) _ _
          exact congrArg Subtype.val h0
        have hsup : (⨆ χ : ι → ℂ, ⨅ i, Module.End.eigenspace (T i) (χ i)) = ⊥ := by
          simp only [hbot]
          exact iSup_bot
        rw [hsup] at hdec
        have hall : ∀ x : H, x = 0 := by
          intro x
          have hx : x ∈ (⊥ : Submodule ℂ H) := by
            rw [hdec]; exact Submodule.mem_top
          exact (Submodule.mem_bot ℂ).mp hx
        haveI : Subsingleton H := ⟨fun a b => by rw [hall a, hall b]⟩
        have h0 : Module.finrank ℂ H = 0 := Module.finrank_zero_of_subsingleton
        omega
      -- a unit joint eigenvector
      obtain ⟨x, hx⟩ := exists_ne (0 : ↥(⨅ i, Module.End.eigenspace (T i) (χ i)))
      have hxH : (x : H) ≠ 0 := by
        intro hz
        apply hx
        ext
        simpa using hz
      set v : H := ‖(x : H)‖⁻¹ • (x : H) with hvdef
      have hv_norm : ‖v‖ = 1 := by
        rw [hvdef, norm_smul, norm_inv, norm_norm]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hxH)
      have hv_ne : v ≠ 0 := by
        intro hz; rw [hz, norm_zero] at hv_norm; exact zero_ne_one hv_norm
      have hv_mem : v ∈ ⨅ i, Module.End.eigenspace (T i) (χ i) := by
        rw [hvdef]; exact Submodule.smul_mem _ _ x.2
      have hmem : ∀ i, T i v = χ i • v := fun i =>
        Module.End.mem_eigenspace_iff.mp (((Submodule.mem_iInf _).mp hv_mem) i)
      -- restrict to the orthogonal complement of `v`
      set Kv : Submodule ℂ H := ℂ ∙ v with hKvdef
      set W : Submodule ℂ H := Kvᗮ with hWdef
      have hvK : v ∈ Kv := by
        rw [hKvdef]; exact Submodule.mem_span_of_mem (Set.mem_singleton v)
      have hKfin : Module.finrank ℂ ↥Kv = 1 := finrank_span_singleton hv_ne
      have hWfin : Module.finrank ℂ ↥W = n := by
        have hsum := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℂ) (E := H) Kv
        rw [hKfin, hfin] at hsum
        have hWW : Module.finrank ℂ ↥W = Module.finrank ℂ ↥Kvᗮ := by rw [hWdef]
        omega
      -- `W` is invariant under each `T i`
      have hinv : ∀ i : ι, ∀ x : ↥W, T i (x : H) ∈ W := by
        intro i x
        have hxW : (x : H) ∈ Kvᗮ := x.2
        show T i (x : H) ∈ Kvᗮ
        apply (Submodule.mem_orthogonal Kv _).mpr
        intro w hw
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
        have h1 : ⟪v, T i (x : H)⟫_ℂ = 0 := by
          have h2 : ⟪v, T i (x : H)⟫_ℂ = ⟪T i v, (x : H)⟫_ℂ := ((hsymm i) v x).symm
          rw [h2, hmem i, inner_smul_left]
          have h3 : ⟪v, (x : H)⟫_ℂ = 0 :=
            ((Submodule.mem_orthogonal Kv (x : H)).mp hxW) v hvK
          rw [h3, mul_zero]
        rw [inner_smul_left, h1, mul_zero]
      -- the restricted family on `W`
      set S : ι → (↥W →ₗ[ℂ] ↥W) :=
        fun i => LinearMap.codRestrict W (T i ∘ₗ W.subtype) (fun x => hinv i x) with hSdef
      have hScoe : ∀ (i : ι) (x : ↥W), ((S i x : ↥W) : H) = T i (x : H) := fun i x => rfl
      have hsymmS : ∀ i, (S i).IsSymmetric := by
        intro i x y
        have e1 : ⟪S i x, y⟫_ℂ = ⟪T i (x : H), (y : H)⟫_ℂ := by
          rw [Submodule.coe_inner W, hScoe i x]
        have e2 : ⟪x, S i y⟫_ℂ = ⟪(x : H), T i (y : H)⟫_ℂ := by
          rw [Submodule.coe_inner W, hScoe i y]
        rw [e1, e2]
        exact hsymm i _ _
      have hcommS : ∀ i j, Commute (S i) (S j) := by
        intro i j
        have h := (hcomm i j).eq
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        show ((S i (S j x) : ↥W) : H) = ((S j (S i x) : ↥W) : H)
        rw [hScoe, hScoe, hScoe, hScoe]
        have h2 := LinearMap.congr_fun h (x : H)
        rw [Module.End.mul_apply, Module.End.mul_apply] at h2
        exact h2
      -- recurse
      obtain ⟨b, μ, hon, hdiag⟩ := IH (H := ↥W) hWfin S hsymmS hcommS
      -- assemble: `v` followed by the basis of `W`
      refine ⟨Fin.cons (α := fun _ => H) v (fun k => ((b k : ↥W) : H)),
        fun k i => Fin.cases (χ i) (fun j => μ j i) k, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro k
          cases k using Fin.cases with
          | zero => rw [Fin.cons_zero]; exact hv_norm
          | succ j =>
            rw [Fin.cons_succ]
            show ‖(((b j : ↥W)) : H)‖ = 1
            rw [show ‖(((b j : ↥W)) : H)‖ = ‖b j‖ from rfl]
            exact hon.1 j
        · intro k l hkl
          cases k using Fin.cases with
          | zero =>
            cases l using Fin.cases with
            | zero => exact absurd rfl hkl
            | succ j =>
              rw [Fin.cons_zero, Fin.cons_succ]
              exact ((Submodule.mem_orthogonal Kv _).mp
                (by show ((b j : ↥W) : H) ∈ Kvᗮ; exact (b j).2)) v hvK
          | succ i =>
            cases l using Fin.cases with
            | zero =>
              rw [Fin.cons_succ, Fin.cons_zero]
              have h1 : ⟪v, (((b i : ↥W)) : H)⟫_ℂ = 0 :=
                ((Submodule.mem_orthogonal Kv _).mp
                  (by show (((b i : ↥W)) : H) ∈ Kvᗮ; exact (b i).2)) v hvK
              rw [← inner_conj_symm, h1, map_zero]
            | succ j =>
              rw [Fin.cons_succ, Fin.cons_succ]
              have hij : i ≠ j := fun h => hkl (congrArg Fin.succ h)
              rw [← Submodule.coe_inner W]
              exact hon.2 hij
      · intro i k
        obtain rfl | ⟨j, rfl⟩ := k.eq_zero_or_eq_succ
        · rw [Fin.cons_zero]
          show T i v = χ i • v
          exact hmem i
        · rw [Fin.cons_succ]
          show T i (((b j : ↥W)) : H) = μ j i • (((b j : ↥W)) : H)
          have h2 := hdiag i j
          have h3 : T i (((b j : ↥W)) : H) = (((μ j i • b j : ↥W)) : H) := by
            have h4 := congrArg Subtype.val h2
            simpa [hScoe] using h4
          rw [h3, Submodule.coe_smul]

/-- **Joint spectral orthonormal basis (T1).** A commuting family of symmetric
    operators on a finite-dimensional inner product space is simultaneously
    diagonalized by an orthonormal basis indexed by `Fin (finrank)`, with
    eigenvalues `μ k i`.  Proved via `jointONB_aux` (induction on `finrank`),
    avoiding the sigma-type ONB assembly that hit Lean universe/whnf timeouts. -/
theorem jointSpectral_orthonormalBasis {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] {ι : Type*} {T : ι → H →ₗ[ℂ] H}
    (hsymm : ∀ i, (T i).IsSymmetric) (hcomm : ∀ i j, Commute (T i) (T j)) :
    ∃ (b : Fin (Module.finrank ℂ H) → H) (μ : Fin (Module.finrank ℂ H) → ι → ℂ),
      Orthonormal ℂ b ∧ ∀ i k, T i (b k) = μ k i • b k :=
  jointONB_aux (Module.finrank ℂ H) rfl T hsymm hcomm

-- ============================================================================
-- §B. Finite-dimensional Stone's theorem (diagonal form)
-- ============================================================================

/-- Skew-adjointness of a linear map: `⟪A x, y⟫ = -⟪x, A y⟫` (T2 interface for
    the Stone generator). -/
def IsSkewAdjoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ[ℂ] H) : Prop :=
  ∀ x y, ⟪A x, y⟫_ℂ = -⟪x, A y⟫_ℂ

/-- **Finite-dimensional Stone's theorem (T1, diagonal form).**

    A strongly continuous one-parameter unitary group `U` on a finite-dimensional
    Hilbert space is simultaneously diagonalized by an orthonormal basis: there
    is a skew-adjoint generator `A` with `A (b k) = (a k) * i • b k` and
    `(U t) (b k) = exp (i * a k * t) • b k`.

    Proof strategy (avoids the timeout paths): split each `U t` into self-adjoint
    real and imaginary parts — a commuting family indexed by `ℝ ⊕ ℝ` —
    diagonalize it with `jointSpectral_orthonormalBasis`, and read off a continuous
    character `ℝ → ℂ` on each basis vector.  `continuous_char_lift` (Rung 6, T1)
    identifies each character as `t ↦ exp (i * a * t)`; the frequencies reassemble
    into the skew-adjoint generator `A`. -/
theorem stone_finiteDim {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (U : ℝ → (H ≃ₗᵢ[ℂ] H))
    (hmul : ∀ s t, U (s + t) = (U s).trans (U t))
    (hcont : ∀ x : H, Continuous fun t => (U t) x) :
    ∃ (A : H →ₗ[ℂ] H), IsSkewAdjoint A ∧
      ∃ (a : Fin (Module.finrank ℂ H) → ℝ) (b : Fin (Module.finrank ℂ H) → H),
        Orthonormal ℂ b ∧
        (∀ k, A (b k) = (↑(a k) * Complex.I) • (b k)) ∧
        (∀ k t, (U t) (b k) = Complex.exp (↑(a k * t) * Complex.I) • (b k)) := by
  -- the group as linear maps
  set T : ℝ → H →ₗ[ℂ] H := fun t => (U t).toLinearEquiv.toLinearMap with hTdef
  have hTapp : ∀ (t : ℝ) (x : H), T t x = (U t) x := fun t x => rfl
  have hTcomm : ∀ s t, Commute (T s) (T t) := by
    intro s t
    have h1 : ∀ x, (U (s + t)) x = (U t) ((U s) x) := fun x => by
      rw [hmul s t, LinearIsometryEquiv.trans_apply]
    have h2 : ∀ x, (U (s + t)) x = (U s) ((U t) x) := fun x => by
      rw [add_comm s t, hmul t s, LinearIsometryEquiv.trans_apply]
    have key : ∀ x, T s (T t x) = T t (T s x) := by
      intro x
      calc T s (T t x) = (U s) ((U t) x) := rfl
        _ = (U (s + t)) x := (h2 x).symm
        _ = (U t) ((U s) x) := h1 x
        _ = T t (T s x) := rfl
    have hmul_eq : T s * T t = T t * T s := LinearMap.ext key
    exact hmul_eq
  have hU0 : U 0 = LinearIsometryEquiv.refl ℂ H := by
    ext x
    have h := hmul 0 0
    have h1 : ((U 0).trans (U 0)) x = (U 0) x := by rw [← h]; simp
    rw [LinearIsometryEquiv.trans_apply] at h1
    have h2 := (U 0).injective h1
    simpa using h2
  have hUsymm : ∀ t, U (-t) = (U t).symm := by
    intro t
    have h := hmul t (-t)
    rw [add_neg_cancel, hU0] at h
    -- h : refl ℂ H = (U t).trans (U (-t))
    have h1 : ∀ x, (U (-t)) ((U t) x) = x := by
      intro x
      have hx : ((U t).trans (U (-t))) x = x := by rw [← h]; rfl
      rw [LinearIsometryEquiv.trans_apply] at hx
      exact hx
    ext x
    calc (U (-t)) x = (U (-t)) ((U t) ((U t).symm x)) := by
            rw [LinearIsometryEquiv.apply_symm_apply]
      _ = (U t).symm x := h1 _
  -- adjoint of `T t` is `T (-t)`
  have hTadj : ∀ t, LinearMap.adjoint (T t) = T (-t) := by
    intro t
    apply LinearMap.ext
    intro y
    apply ext_inner_left ℂ
    intro z
    calc ⟪z, LinearMap.adjoint (T t) y⟫_ℂ = ⟪T t z, y⟫_ℂ :=
          LinearMap.adjoint_inner_right _ _ _
      _ = ⟪z, T (-t) y⟫_ℂ := by
          rw [hTapp, hTapp, hUsymm t]
          have h3 := (U t).inner_map_map z ((U t).symm y)
          rw [LinearIsometryEquiv.apply_symm_apply] at h3
          exact h3
  have hadj : ∀ (s : ℝ) (x y : H), ⟪T s x, y⟫_ℂ = ⟪x, T (-s) y⟫_ℂ := by
    intro s x y
    calc ⟪T s x, y⟫_ℂ = ⟪x, LinearMap.adjoint (T s) y⟫_ℂ :=
          (LinearMap.adjoint_inner_right _ _ _).symm
      _ = ⟪x, T (-s) y⟫_ℂ := by rw [hTadj s]
  -- real and imaginary parts: a commuting family of symmetric operators
  set F : ℝ ⊕ ℝ → H →ₗ[ℂ] H := fun p => match p with
    | Sum.inl t => (1/2 : ℂ) • (T t + T (-t))
    | Sum.inr t => (1/(2*Complex.I) : ℂ) • (T t - T (-t)) with hFdef
  have hFinl : ∀ t, F (Sum.inl t) = (1/2 : ℂ) • (T t + T (-t)) := fun t => rfl
  have hFinr : ∀ t, F (Sum.inr t) = (1/(2*Complex.I) : ℂ) • (T t - T (-t)) := fun t => rfl
  have hInvI : (1/(2*Complex.I) : ℂ) = -Complex.I/2 := by
    have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have hne : (2*Complex.I:ℂ) ≠ 0 := by simp
    rw [div_eq_iff hne]
    calc (1:ℂ) = -(Complex.I * Complex.I) := by rw [hII]; ring
      _ = (-Complex.I/2) * (2*Complex.I) := by ring
  have hFsymm : ∀ p : ℝ ⊕ ℝ, (F p).IsSymmetric := by
    intro p x y
    cases p with
    | inl t =>
        rw [hFinl]
        show ⟪((1/2:ℂ) • (T t + T (-t))) x, y⟫_ℂ = ⟪x, ((1/2:ℂ) • (T t + T (-t))) y⟫_ℂ
        rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.add_apply,
          inner_smul_left, inner_add_left, inner_smul_right, inner_add_right,
          hadj t x y, hadj (-t) x y, neg_neg]
        have hc : (starRingEnd ℂ) (1/2 : ℂ) = 1/2 := by
          have h : ((1/2 : ℝ):ℂ) = (1/2 : ℂ) := by norm_num
          rw [← h, Complex.conj_ofReal]
        rw [hc]; ring
    | inr t =>
        rw [hFinr]
        show ⟪((1/(2*Complex.I):ℂ) • (T t - T (-t))) x, y⟫_ℂ
          = ⟪x, ((1/(2*Complex.I):ℂ) • (T t - T (-t))) y⟫_ℂ
        rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.sub_apply,
          inner_smul_left, inner_sub_left, inner_smul_right, inner_sub_right,
          hadj t x y, hadj (-t) x y, neg_neg]
        have hc : (starRingEnd ℂ) (1/(2*Complex.I) : ℂ) = -(1/(2*Complex.I) : ℂ) := by
          have e1 : (-Complex.I/2 : ℂ) = ((-1/2 : ℝ):ℂ) * Complex.I := by
            push_cast; ring
          have e2 : (Complex.I/2 : ℂ) = ((1/2 : ℝ):ℂ) * Complex.I := by
            push_cast; ring
          have e3 : (starRingEnd ℂ) (-Complex.I/2 : ℂ) = Complex.I/2 := by
            rw [e1, e2, map_mul, Complex.conj_ofReal, Complex.conj_I]
            push_cast; ring
          rw [hInvI, e3]
          ring
        rw [hc]; ring
  have hFcomm : ∀ p q : ℝ ⊕ ℝ, Commute (F p) (F q) := by
    intro p q
    cases p with
    | inl s =>
      cases q with
      | inl t =>
          rw [hFinl, hFinl]
          have hXY : Commute (T s + T (-s)) (T t + T (-t)) :=
            ((hTcomm s t).add_right (hTcomm s (-t))).add_left
              ((hTcomm (-s) t).add_right (hTcomm (-s) (-t)))
          exact (hXY.smul_left (1/2 : ℂ)).smul_right (1/2 : ℂ)
      | inr t =>
          rw [hFinl, hFinr]
          have hXY : Commute (T s + T (-s)) (T t - T (-t)) := by
            rw [sub_eq_add_neg]
            exact ((hTcomm s t).add_right (hTcomm s (-t)).neg_right).add_left
              ((hTcomm (-s) t).add_right (hTcomm (-s) (-t)).neg_right)
          exact (hXY.smul_left (1/2 : ℂ)).smul_right (1/(2*Complex.I) : ℂ)
    | inr s =>
      cases q with
      | inl t =>
          rw [hFinr, hFinl]
          have hXY : Commute (T s - T (-s)) (T t + T (-t)) := by
            rw [sub_eq_add_neg]
            exact ((hTcomm s t).add_right (hTcomm s (-t))).add_left
              (((hTcomm (-s) t).add_right (hTcomm (-s) (-t))).neg_left)
          exact (hXY.smul_left (1/(2*Complex.I) : ℂ)).smul_right (1/2 : ℂ)
      | inr t =>
          rw [hFinr, hFinr]
          have hXY : Commute (T s - T (-s)) (T t - T (-t)) := by
            rw [sub_eq_add_neg, sub_eq_add_neg]
            exact (((hTcomm s t).add_right (hTcomm s (-t)).neg_right).add_left
              (((hTcomm (-s) t).add_right (hTcomm (-s) (-t)).neg_right).neg_left))
          exact (hXY.smul_left (1/(2*Complex.I) : ℂ)).smul_right (1/(2*Complex.I) : ℂ)
  -- diagonalize the real/imaginary family
  obtain ⟨b, μ, hon, hdiag⟩ := jointSpectral_orthonormalBasis hFsymm hFcomm
  -- `T t` reassembled from its real and imaginary parts
  have hTdecomp : ∀ t : ℝ, T t = F (Sum.inl t) + Complex.I • F (Sum.inr t) := by
    intro t
    apply LinearMap.ext
    intro x
    rw [hFinl, hFinr]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply]
    have hImul : Complex.I * (1/(2*Complex.I) : ℂ) = 1/2 := by
      rw [hInvI]
      have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
      linear_combination (-1/2 : ℂ) * hII
    have e1 : Complex.I • ((1/(2*Complex.I):ℂ) • (T t x - T (-t) x))
        = (1/2:ℂ) • (T t x - T (-t) x) := by
      rw [← mul_smul, hImul]
    rw [e1]
    have key : (1/2:ℂ) • (T t x + T (-t) x) + (1/2:ℂ) • (T t x - T (-t) x) = T t x := by
      rw [smul_add, smul_sub]
      have e3 : (1/2:ℂ) • T t x + (1/2:ℂ) • T t x = T t x := by
        rw [← add_smul]; norm_num
      have key2 : (1/2:ℂ) • T t x + (1/2:ℂ) • T (-t) x
          + ((1/2:ℂ) • T t x - (1/2:ℂ) • T (-t) x)
          = (1/2:ℂ) • T t x + (1/2:ℂ) • T t x := by abel
      rw [key2, e3]
    exact key.symm
  -- on each basis vector, `U t` acts by a character
  have hchar_eq : ∀ (k : Fin (Module.finrank ℂ H)) (t : ℝ),
      (U t) (b k) = (μ k (Sum.inl t) + Complex.I * μ k (Sum.inr t)) • (b k) := by
    intro k t
    have e1 : ((1/2:ℂ) • (T t + T (-t))) (b k) = μ k (Sum.inl t) • b k := by
      have h := hdiag (Sum.inl t) k
      rwa [hFinl] at h
    have e2 : ((1/(2*Complex.I):ℂ) • (T t - T (-t))) (b k)
        = μ k (Sum.inr t) • b k := by
      have h := hdiag (Sum.inr t) k
      rwa [hFinr] at h
    have hTT : T t (b k) = ((1/2:ℂ) • (T t + T (-t))) (b k)
        + Complex.I • (((1/(2*Complex.I):ℂ) • (T t - T (-t))) (b k)) := by
      have hdecomp := hTdecomp t
      have hx := congrArg (fun f : H →ₗ[ℂ] H => f (b k)) hdecomp
      simp only [LinearMap.add_apply, LinearMap.smul_apply, hFinl, hFinr] at hx
      exact hx
    calc (U t) (b k) = T t (b k) := (hTapp t (b k)).symm
      _ = ((1/2:ℂ) • (T t + T (-t))) (b k)
          + Complex.I • (((1/(2*Complex.I):ℂ) • (T t - T (-t))) (b k)) := hTT
      _ = μ k (Sum.inl t) • b k + Complex.I • (μ k (Sum.inr t) • b k) := by rw [e1, e2]
      _ = (μ k (Sum.inl t) + Complex.I * μ k (Sum.inr t)) • b k := by
          rw [← mul_smul, ← add_smul]
  have hmul_c : ∀ (k : Fin (Module.finrank ℂ H)) (s t : ℝ),
      (μ k (Sum.inl (s+t)) + Complex.I * μ k (Sum.inr (s+t)))
      = (μ k (Sum.inl s) + Complex.I * μ k (Sum.inr s))
        * (μ k (Sum.inl t) + Complex.I * μ k (Sum.inr t)) := by
    intro k s t
    have e1 := hchar_eq k (s + t)
    have e2 := hchar_eq k s
    have e3 := hchar_eq k t
    have hU : (U (s + t)) (b k) = (U t) ((U s) (b k)) := by
      rw [hmul s t, LinearIsometryEquiv.trans_apply]
    rw [e1, e2, map_smul, e3, ← mul_smul] at hU
    have hbk0 : b k ≠ 0 := hon.ne_zero k
    have hinj := smul_left_injective ℂ hbk0
    exact hinj hU
  have hnorm_c : ∀ (k : Fin (Module.finrank ℂ H)) (t : ℝ),
      ‖μ k (Sum.inl t) + Complex.I * μ k (Sum.inr t)‖ = 1 := by
    intro k t
    have e := hchar_eq k t
    have h1 : ‖(U t) (b k)‖ = 1 := by
      rw [LinearIsometryEquiv.norm_map]; exact hon.1 k
    rw [e, norm_smul, hon.1 k, mul_one] at h1
    exact h1
  have hcont_c : ∀ k : Fin (Module.finrank ℂ H),
      Continuous fun t => (μ k (Sum.inl t) + Complex.I * μ k (Sum.inr t) : ℂ) := by
    intro k
    have e : (fun t => (μ k (Sum.inl t) + Complex.I * μ k (Sum.inr t) : ℂ))
        = fun t => ⟪b k, (U t) (b k)⟫_ℂ := by
      funext t
      rw [hchar_eq k t, inner_smul_right]
      have hbb : ⟪b k, b k⟫_ℂ = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hon.1 k]; norm_num
      rw [hbb, mul_one]
    rw [e]
    exact continuous_const.inner (hcont (b k))
  -- each character is `t ↦ exp (i * a * t)`
  obtain ⟨a, ha⟩ : ∃ a : Fin (Module.finrank ℂ H) → ℝ, ∀ k t,
      (μ k (Sum.inl t) + Complex.I * μ k (Sum.inr t))
        = Complex.exp (↑(a k * t) * Complex.I) := by
    choose a ha using fun k => continuous_char_lift (hcont_c k) (hmul_c k) (hnorm_c k)
    exact ⟨a, ha⟩
  -- the generator, diagonal in the same basis
  -- (use the finrank directly to avoid `set` interfering with the obtained `b`)
  let bs : Module.Basis (Fin (Module.finrank ℂ H)) ℂ H :=
    basisOfLinearIndependentOfCardEqFinrank' b hon.linearIndependent (Fintype.card_fin _)
  have hbk : ∀ k : Fin (Module.finrank ℂ H), bs k = b k := fun k =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' b hon.linearIndependent (Fintype.card_fin _)) k
  set A : H →ₗ[ℂ] H := (bs.constr ℂ) (fun k => (↑(a k) * Complex.I) • (b k)) with hAdef
  have hA_apply : ∀ k : Fin (Module.finrank ℂ H), A (b k) = (↑(a k) * Complex.I) • (b k) := by
    intro k
    have hbk' : b k = bs k := (hbk k).symm
    calc A (b k) = A (bs k) := by rw [hbk']
      _ = (↑(a k) * Complex.I) • (b k) := by
          rw [hAdef]
          exact Module.Basis.constr_basis bs ℂ (fun k => (↑(a k) * Complex.I) • (b k)) k
  -- `A` is skew-adjoint: check on matrix elements, then expand
  have hmat : ∀ k l : Fin (Module.finrank ℂ H), ⟪A (b k), b l⟫_ℂ = -⟪b k, A (b l)⟫_ℂ := by
    intro k l
    rw [hA_apply k, hA_apply l, inner_smul_left, inner_smul_right]
    have hck : (starRingEnd ℂ) (↑(a k) * Complex.I) = -(↑(a k) * Complex.I) := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
    rw [hck]
    by_cases hkl : k = l
    · subst hkl; ring
    · rw [hon.2 hkl, mul_zero, mul_zero, neg_zero]
  have hexp : ∀ z : H, ∑ k : Fin (Module.finrank ℂ H), (bs.repr z) k • (b k) = z := by
    intro z
    have h := bs.sum_repr z
    simpa [hbk] using h
  have key : ∀ x y : H, ⟪A x, y⟫_ℂ = ∑ k : Fin (Module.finrank ℂ H), ∑ l : Fin (Module.finrank ℂ H),
      (starRingEnd ℂ) ((bs.repr x) k) * (bs.repr y) l * ⟪A (b k), b l⟫_ℂ := by
    intro x y
    conv_lhs => rw [← hexp x, ← hexp y, map_sum]
    simp_rw [map_smul, sum_inner, inner_smul_left, inner_sum, inner_smul_right,
      Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    ring
  have key2 : ∀ x y : H, ⟪x, A y⟫_ℂ = ∑ k : Fin (Module.finrank ℂ H), ∑ l : Fin (Module.finrank ℂ H),
      (starRingEnd ℂ) ((bs.repr x) k) * (bs.repr y) l * ⟪b k, A (b l)⟫_ℂ := by
    intro x y
    conv_lhs => rw [← hexp x, ← hexp y, map_sum]
    simp_rw [map_smul, sum_inner, inner_smul_left, inner_sum, inner_smul_right,
      Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    ring
  have hskew : IsSkewAdjoint A := by
    intro x y
    have e1 := key x y
    have e2 := key2 x y
    calc ⟪A x, y⟫_ℂ
        = ∑ k : Fin (Module.finrank ℂ H), ∑ l : Fin (Module.finrank ℂ H),
            (starRingEnd ℂ) ((bs.repr x) k) * (bs.repr y) l * ⟪A (b k), b l⟫_ℂ := e1
      _ = ∑ k : Fin (Module.finrank ℂ H), ∑ l : Fin (Module.finrank ℂ H),
            -((starRingEnd ℂ) ((bs.repr x) k) * (bs.repr y) l * ⟪b k, A (b l)⟫_ℂ) := by
          apply Finset.sum_congr rfl; intro k _
          apply Finset.sum_congr rfl; intro l _
          rw [hmat k l]; ring
      _ = -∑ k : Fin (Module.finrank ℂ H), ∑ l : Fin (Module.finrank ℂ H),
            (starRingEnd ℂ) ((bs.repr x) k) * (bs.repr y) l * ⟪b k, A (b l)⟫_ℂ := by
          simp only [← Finset.sum_neg_distrib]
      _ = -⟪x, A y⟫_ℂ := by rw [e2]
  refine ⟨A, hskew, a, b, hon, hA_apply, fun k t => ?_⟩
  rw [hchar_eq k t, ha k t]

-- ============================================================================
-- §C. Axiom audit
-- ============================================================================

#print axioms ThetLogos.jointONB_aux
#print axioms ThetLogos.jointSpectral_orthonormalBasis
#print axioms ThetLogos.stone_finiteDim
