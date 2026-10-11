import ThetLogos.OneModeFermion
import ThetLogos.WightmanTargets

namespace ThetLogos

open scoped InnerProductSpace

/-!
# ThetLogos.Rung5W5 — axiom W5 (vacuum cyclicity) for the one-mode Majorana field (Rung 5)

**Honest label.** Two T1 results — a proved framing correction in the antipode tradition
("proved not-this"):

**PART A — W5 as framed is FALSE (`w5_framed_false`).**
`W5_vacuumCyclic_sharp` asks for `Dense (Set.range polyApply)` — density of the
*monomial* range (individual field-polynomials applied to the vacuum), not its linear
span. For the Majorana field this is false: every monomial is a scalar multiple of
`vac1` or of `e1Fock` (one field application swaps `vac1 ↔ e1Fock` up to a scalar, by
`majorana1_vac` / `majorana1_e1`), so the range sits inside the union of two complex
lines. The vector `vac1 + e1Fock` is at distance ≥ 1 from every range element
(Cauchy–Schwarz against the orthogonal probe), hence not in the closure. Monomial
density fails — even for a genuine free-fermion field.

**PART B — the corrected span-version is TRUE (`w5_span_true`).**
What the physics literature means by "the polynomials are dense" is that the *linear
span* of the monomials is dense. Here `vac1` (the empty monomial) and `e1Fock`
(the monomial `[1]`) are both in the range, and they span all of `Fock1`, so the span
is `⊤` — hence dense.

This is a framing correction, not a physics failure.
-/

/-!
## Helpers: the monomial recursion on coerced values
-/

/-- One field-application step, on coerced values (T1 helper). Definitional:
    `polyApply (f :: fs) = liftTop (fieldMajorana f) (polyApply fs)`, the `⊤`-coercion
    is the identity, and `fieldMajorana f = f • majorana1`. -/
theorem polyApply_cons_val (f : ℂ) (fs : List ℂ) :
    (polyApply Fock1 vac1 ⟨ℂ⟩ ⊤ (fun c => liftTop (fieldMajorana c)) Submodule.mem_top (f :: fs) : Fock1)
      = f • majorana1 ((polyApply Fock1 vac1 ⟨ℂ⟩ ⊤ (fun c => liftTop (fieldMajorana c)) Submodule.mem_top fs : ↥(⊤ : Submodule ℂ Fock1)) : Fock1) :=
  rfl

/-- Every monomial is a scalar multiple of `vac1` or of `e1Fock` (T1).
    The Majorana field swaps `vac1 ↔ e1Fock` up to the test-function scalar, so
    longer products never leave the two lines. -/
theorem w5_range_char : ∀ l : List ℂ, ∃ c : ℂ,
    (polyApply Fock1 vac1 ⟨ℂ⟩ ⊤ (fun c => liftTop (fieldMajorana c)) Submodule.mem_top l : Fock1)
      = c • vac1
    ∨ (polyApply Fock1 vac1 ⟨ℂ⟩ ⊤ (fun c => liftTop (fieldMajorana c)) Submodule.mem_top l : Fock1)
      = c • e1Fock := by
  intro l
  induction l with
  | nil =>
    refine ⟨1, Or.inl ?_⟩
    have h : (polyApply Fock1 vac1 ⟨ℂ⟩ ⊤ (fun c => liftTop (fieldMajorana c)) Submodule.mem_top [] : Fock1)
        = vac1 := rfl
    rw [h, one_smul]
  | cons f fs ih =>
    obtain ⟨c, hc | hc⟩ := ih
    · exact ⟨f * c, Or.inr (by rw [polyApply_cons_val, hc, map_smul, majorana1_vac, ← mul_smul])⟩
    · exact ⟨f * c, Or.inl (by rw [polyApply_cons_val, hc, map_smul, majorana1_e1, ← mul_smul])⟩

/-!
## Distance lower bounds: `vac1 + e1Fock` stays away from both lines
-/

/-- `⟪e1Fock, e1Fock⟫ = 1` (T1 helper). -/
theorem e1Fock_self_inner : ⟪e1Fock, e1Fock⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_e1Fock]
  norm_num

/-- `⟪vac1, vac1⟫ = 1` (T1 helper). -/
theorem vac1_self_inner : ⟪vac1, vac1⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_vac1]
  norm_num

/-- `⟪e1Fock, vac1⟫ = 0` (T1 helper). -/
theorem e1Fock_vac1_orth : ⟪e1Fock, vac1⟫_ℂ = 0 := by
  have h := inner_conj_symm (𝕜 := ℂ) vac1 e1Fock
  rw [vac1_e1_orth] at h
  exact star_eq_zero.mp h

/-- `vac1 + e1Fock` is at distance ≥ 1 from `span{vac1}` (T1).
    Probe with `e1Fock`: `⟪(c • vac1) - (vac1 + e1Fock), e1Fock⟫ = -1`, then
    Cauchy–Schwarz. -/
theorem dist_span_vac1_ge (c : ℂ) :
    1 ≤ dist (c • vac1) (vac1 + e1Fock) := by
  have hinner : ⟪(c • vac1) - (vac1 + e1Fock), e1Fock⟫_ℂ = -1 := by
    rw [inner_sub_left, inner_add_left, inner_smul_left, vac1_e1_orth, e1Fock_self_inner]
    simp
  calc (1 : ℝ) = ‖(-1 : ℂ)‖ := by rw [norm_neg, norm_one]
    _ = ‖⟪(c • vac1) - (vac1 + e1Fock), e1Fock⟫_ℂ‖ := by rw [hinner]
    _ ≤ ‖(c • vac1) - (vac1 + e1Fock)‖ * ‖e1Fock‖ := norm_inner_le_norm _ _
    _ = ‖(c • vac1) - (vac1 + e1Fock)‖ := by rw [norm_e1Fock, mul_one]
    _ = dist (c • vac1) (vac1 + e1Fock) := (dist_eq_norm _ _).symm

/-- `vac1 + e1Fock` is at distance ≥ 1 from `span{e1Fock}` (T1).
    Probe with `vac1`: `⟪(c • e1Fock) - (vac1 + e1Fock), vac1⟫ = -1`, then
    Cauchy–Schwarz. -/
theorem dist_span_e1Fock_ge (c : ℂ) :
    1 ≤ dist (c • e1Fock) (vac1 + e1Fock) := by
  have hinner : ⟪(c • e1Fock) - (vac1 + e1Fock), vac1⟫_ℂ = -1 := by
    rw [inner_sub_left, inner_add_left, inner_smul_left, e1Fock_vac1_orth, vac1_self_inner]
    simp
  calc (1 : ℝ) = ‖(-1 : ℂ)‖ := by rw [norm_neg, norm_one]
    _ = ‖⟪(c • e1Fock) - (vac1 + e1Fock), vac1⟫_ℂ‖ := by rw [hinner]
    _ ≤ ‖(c • e1Fock) - (vac1 + e1Fock)‖ * ‖vac1‖ := norm_inner_le_norm _ _
    _ = ‖(c • e1Fock) - (vac1 + e1Fock)‖ := by rw [norm_vac1, mul_one]
    _ = dist (c • e1Fock) (vac1 + e1Fock) := (dist_eq_norm _ _).symm

/-!
## PART A — the framed target is FALSE
-/

/-- **W5 as framed is FALSE (T1 refutation).** With `ε = 1/2`, no monomial is within
    `ε` of `vac1 + e1Fock` (every monomial lies on one of the two lines, both at
    distance ≥ 1), so `vac1 + e1Fock ∉ closure (range …)` and the range is not dense. -/
theorem w5_framed_false :
    ¬ W5_vacuumCyclic_sharp Fock1 vac1 ⟨ℂ⟩ (⊤ : Submodule ℂ Fock1)
      (fun c => liftTop (fieldMajorana c)) (Submodule.mem_top) := by
  intro hDense
  have hxmem : vac1 + e1Fock ∈ closure (Set.range fun l : List ℂ =>
      (polyApply Fock1 vac1 ⟨ℂ⟩ ⊤ (fun c => liftTop (fieldMajorana c)) Submodule.mem_top l : Fock1)) :=
    hDense _
  rw [Metric.mem_closure_iff] at hxmem
  obtain ⟨y, hy, hlt⟩ := hxmem (1 / 2) (by norm_num)
  rw [dist_comm] at hlt
  obtain ⟨l, hl⟩ := hy
  have hl' : (polyApply Fock1 vac1 ⟨ℂ⟩ ⊤ (fun c => liftTop (fieldMajorana c)) Submodule.mem_top l : Fock1)
      = y := hl
  obtain ⟨c, hc | hc⟩ := w5_range_char l
  · rw [← hl', hc] at hlt
    linarith [dist_span_vac1_ge c]
  · rw [← hl', hc] at hlt
    linarith [dist_span_e1Fock_ge c]

/-!
## PART B — the corrected span-version is TRUE
-/

/-- Every `x : Fock1` is `(x₀) • vac1 + (x₁) • e1Fock` (T1). -/
theorem fock1_decomp (x : Fock1) : x = (x.ofLp 0) • vac1 + (x.ofLp 1) • e1Fock := by
  apply Fock1_ext
  intro k
  have h : ((x.ofLp 0) • vac1 + (x.ofLp 1) • e1Fock).ofLp k
      = (x.ofLp 0) * (vac1.ofLp k) + (x.ofLp 1) * (e1Fock.ofLp k) := by
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [h]
  fin_cases k <;> simp [vac1_ofLp, e1Fock_ofLp]

/-- `vac1` is the empty monomial (T1). -/
theorem w5_vac1_mem :
    vac1 ∈ Submodule.span ℂ (Set.range fun l : List ℂ =>
      (polyApply Fock1 vac1 ⟨ℂ⟩ ⊤ (fun c => liftTop (fieldMajorana c)) Submodule.mem_top l : Fock1)) := by
  apply Submodule.subset_span
  exact ⟨[], rfl⟩

/-- `e1Fock` is the monomial `[1]`: `ψ(1)` sends `vac1 ↦ e1Fock` (T1). -/
theorem w5_e1Fock_mem :
    e1Fock ∈ Submodule.span ℂ (Set.range fun l : List ℂ =>
      (polyApply Fock1 vac1 ⟨ℂ⟩ ⊤ (fun c => liftTop (fieldMajorana c)) Submodule.mem_top l : Fock1)) := by
  apply Submodule.subset_span
  refine ⟨[1], ?_⟩
  show (polyApply Fock1 vac1 ⟨ℂ⟩ ⊤ (fun c => liftTop (fieldMajorana c)) Submodule.mem_top [1] : Fock1)
    = e1Fock
  have h1 := polyApply_cons_val 1 []
  rw [h1]
  have h2 : ((polyApply Fock1 vac1 ⟨ℂ⟩ ⊤ (fun c => liftTop (fieldMajorana c)) Submodule.mem_top [] :
      ↥(⊤ : Submodule ℂ Fock1)) : Fock1) = vac1 := rfl
  rw [h2, one_smul, majorana1_vac]

/-- **The corrected W5 is TRUE (T1).** The linear span of the field-monomials applied
    to the vacuum is dense in `Fock1`: `vac1` and `e1Fock` are both monomials and they
    span the whole space, so the span is `⊤`. This is what the physics literature means
    by vacuum cyclicity. -/
theorem w5_span_true :
    Dense (↑(Submodule.span ℂ (Set.range fun l : List ℂ =>
      (polyApply Fock1 vac1 ⟨ℂ⟩ ⊤ (fun c => liftTop (fieldMajorana c)) Submodule.mem_top l : Fock1))) :
      Set Fock1) := by
  have hspan : Submodule.span ℂ (Set.range fun l : List ℂ =>
      (polyApply Fock1 vac1 ⟨ℂ⟩ ⊤ (fun c => liftTop (fieldMajorana c)) Submodule.mem_top l : Fock1))
      = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    rw [fock1_decomp x]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ w5_vac1_mem) (Submodule.smul_mem _ _ w5_e1Fock_mem)
  rw [hspan, Submodule.top_coe]
  exact dense_univ

#print axioms w5_framed_false
#print axioms w5_span_true

end ThetLogos
