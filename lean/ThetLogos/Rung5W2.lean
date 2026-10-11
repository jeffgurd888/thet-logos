import ThetLogos.OneModeFermion
import ThetLogos.WightmanTargets

namespace ThetLogos

/-!
# ThetLogos.Rung5W2 — W2 (ℤ₂ fermion-parity covariance) for the one-mode Majorana fermion

**Honest label (T1 proved; scope priced).** This file proves the *sharp* W2
target `W2_poincareCovariant_sharp` for the one-mode Majorana field, with the
`PoincareMarker` instantiated by the finite group `Multiplicative (ZMod 2)`:
the representation sends the nontrivial element to fermion parity
`P = diag(1,-1)`, and the geometric action on test functions is negation.
This is **ℤ₂ fermion-parity covariance, NOT Poincaré covariance.** Genuine
Poincaré covariance — the unitary representation of the restricted Poincaré
group on physical Fock space via second quantization, plus the Schwartz
action on test functions — remains priced infrastructure (see the PRICE note
on `W2_poincareCovariant_sharp` in `WightmanTargets.lean`).

What IS proved here (T1, zero sorrys): with `H = Fock1`, `T = ℂ`, `D = ⊤`,
- `rep : ℤ₂ → (Fock1 ≃ₗᵢ[ℂ] Fock1)` is a homomorphism with `rep 1 = refl`;
- `act : ℤ₂ → ℂ → ℂ` satisfies `act (g₁ * g₂) f = act g₁ (act g₂ f)`;
- the covariance equation `φ(act g f) (rep g ψ) = rep g (φ f ψ)` holds on `D`;
  the nontrivial case is parity anticommuting with the Majorana field
  (`parityOp_anticomm_majorana`).
-/

/-- Fermion parity as a linear equivalence, from the involutive `parityOp`. -/
noncomputable def parityEquiv : Fock1 ≃ₗ[ℂ] Fock1 :=
  { parityOp with
    invFun := ⇑parityOp
    left_inv := fun x => by simpa using LinearMap.congr_fun parityOp_involutive x
    right_inv := fun x => by simpa using LinearMap.congr_fun parityOp_involutive x }

/-- Fermion parity as a linear isometry equivalence (norms preserved by
    `parityOp_norm`). -/
noncomputable def parityLIE : Fock1 ≃ₗᵢ[ℂ] Fock1 :=
  { parityEquiv with norm_map' := parityOp_norm }

theorem parityLIE_apply (x : Fock1) : parityLIE x = parityOp x := rfl

/-- `parityLIE` is an involution. -/
theorem parityLIE_sq :
    parityLIE.trans parityLIE = LinearIsometryEquiv.refl ℂ Fock1 := by
  apply LinearIsometryEquiv.ext
  intro x
  rw [LinearIsometryEquiv.trans_apply, parityLIE_apply, parityLIE_apply]
  have h := LinearMap.congr_fun parityOp_involutive x
  simpa using h

/-- The ℤ₂ marker standing in for the Poincaré group (honest label: this is
    finite-group covariance; genuine Poincaré action is priced). -/
abbrev Poin : PoincareMarker := ⟨Multiplicative (ZMod 2)⟩

/-- Case analysis on `Multiplicative (ZMod 2)`. -/
theorem zmod2_cases (g : Multiplicative (ZMod 2)) :
    g = 1 ∨ g = Multiplicative.ofAdd 1 := by
  have hall : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hall g.toAdd with h | h
  · left
    have hg : g = Multiplicative.ofAdd 0 := by rw [← h, ofAdd_toAdd]
    rwa [ofAdd_zero] at hg
  · right
    rw [← h, ofAdd_toAdd]

theorem one_ne_ofAdd_one :
    (1 : Multiplicative (ZMod 2)) ≠ Multiplicative.ofAdd 1 := by
  decide

/-- The representation: identity on `0`, fermion parity on `1`. -/
noncomputable def repW2 : Multiplicative (ZMod 2) → (Fock1 ≃ₗᵢ[ℂ] Fock1) :=
  fun g => if g = Multiplicative.ofAdd 1 then parityLIE
    else LinearIsometryEquiv.refl ℂ Fock1

theorem repW2_one : repW2 1 = LinearIsometryEquiv.refl ℂ Fock1 := by
  simp [repW2, one_ne_ofAdd_one]

theorem repW2_ofAdd_one : repW2 (Multiplicative.ofAdd 1) = parityLIE := by
  simp [repW2]

theorem ofAdd_one_mul_self :
    (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by
  rw [← ofAdd_add]
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [h11, ofAdd_zero]

/-- `repW2` is a homomorphism (checked on the four pairs of `ZMod 2`). -/
theorem repW2_hom (g₁ g₂ : Multiplicative (ZMod 2)) :
    repW2 (g₁ * g₂) = (repW2 g₁).trans (repW2 g₂) := by
  rcases zmod2_cases g₁ with rfl | rfl <;> rcases zmod2_cases g₂ with rfl | rfl
  · rw [mul_one, repW2_one, LinearIsometryEquiv.trans_refl]
  · rw [one_mul, repW2_one, repW2_ofAdd_one, LinearIsometryEquiv.refl_trans]
  · rw [mul_one, repW2_ofAdd_one, repW2_one, LinearIsometryEquiv.trans_refl]
  · rw [ofAdd_one_mul_self, repW2_one, repW2_ofAdd_one, parityLIE_sq]

/-- The geometric action on test functions: identity on `0`, negation on `1`. -/
def actW2 : Multiplicative (ZMod 2) → ℂ → ℂ :=
  fun g c => if g = Multiplicative.ofAdd 1 then -c else c

theorem actW2_one (f : ℂ) : actW2 1 f = f := by
  simp [actW2, one_ne_ofAdd_one]

theorem actW2_ofAdd_one (f : ℂ) : actW2 (Multiplicative.ofAdd 1) f = -f := by
  simp [actW2]

/-- `actW2` is an action (checked on the four pairs of `ZMod 2`). -/
theorem actW2_hom (g₁ g₂ : Multiplicative (ZMod 2)) (f : ℂ) :
    actW2 (g₁ * g₂) f = actW2 g₁ (actW2 g₂ f) := by
  rcases zmod2_cases g₁ with rfl | rfl <;> rcases zmod2_cases g₂ with rfl | rfl
  · rw [mul_one, actW2_one, actW2_one]
  · rw [one_mul, actW2_ofAdd_one, actW2_one]
  · rw [mul_one, actW2_one]
  · rw [ofAdd_one_mul_self, actW2_one, actW2_ofAdd_one, actW2_ofAdd_one, neg_neg]

/-- Parity anticommutes with the Majorana field up to the test-function sign:
    `ψ(-f)(P x) = P(ψ(f) x)` (T1). -/
theorem parity_anticomm_field (f : ℂ) (x : Fock1) :
    (fieldMajorana (-f)) (parityOp x) = parityOp (fieldMajorana f x) := by
  have hanti : parityOp (majorana1 x) = -(majorana1 (parityOp x)) := by
    have h := LinearMap.congr_fun parityOp_anticomm_majorana x
    simpa using h
  simp only [fieldMajorana, LinearMap.smul_apply, LinearMap.neg_apply, map_smul, hanti,
    smul_neg, neg_smul]

/-- **W2 for the one-mode Majorana fermion (T1).** ℤ₂ fermion-parity covariance
    of the sharp Wightman target. Honest scope: the `PoincareMarker` is the
    finite group `Multiplicative (ZMod 2)`, not the Poincaré group. -/
theorem w2_parity : W2_poincareCovariant_sharp Fock1 ⟨ℂ⟩ (⊤ : Submodule ℂ Fock1)
    Poin repW2 actW2 (fun c => liftTop (fieldMajorana c))
    (fun _g _ψ => Submodule.mem_top) := by
  refine ⟨repW2_hom, repW2_one, actW2_hom, ?_⟩
  intro g f ψ
  rcases zmod2_cases g with rfl | rfl
  · -- `g = 1`: both sides are the field applied to `ψ`.
    rw [repW2_one, actW2_one]
    apply Subtype.ext
    rfl
  · -- `g` nontrivial: parity anticommutes with the Majorana field.
    rw [repW2_ofAdd_one, actW2_ofAdd_one]
    apply Subtype.ext
    show (fieldMajorana (-f)) (parityOp ↑ψ) = parityOp ((fieldMajorana f) ↑ψ)
    exact parity_anticomm_field f ↑ψ

#print axioms w2_parity

end ThetLogos
