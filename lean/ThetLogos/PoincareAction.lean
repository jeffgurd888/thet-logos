import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
import ThetLogos.WightmanAxioms

namespace ThetLogos

/-!
# ThetLogos.PoincareAction — the Poincaré group and its geometric action on test functions

Source: Rung 6, Price 4 (2026-10-11) — genuine Poincaré covariance, the deep item.
Rung 5 proved W2 only for ℤ₂ fermion parity (`Rung5W2.lean`); this file builds the
*geometric half* of genuine Poincaré covariance as T1 and prices the
representation-theoretic half as exact T5 windows.

**What IS proved here (T1, zero sorrys):**
- `LorentzGroup` — the Lorentz group O(1,3) as Minkowski-form-preserving linear
  equivalences, with a `Group` instance. Mathlib (2026) was checked first
  (2026-10-11): `Matrix.orthogonalGroup` is the *compact* form (transpose =
  inverse), not the Lorentz group, and `SemidirectProduct` is multiplicative-only
  (would need `Multiplicative` wrappers plus `MulAut` conversion friction), so
  both are defined directly — definitionally transparent, no wrappers.
- `PoincareGroup` — spacetime translations ⋊ Lorentz group, with the explicit
  semidirect multiplication `(a₁,Λ₁)·(a₂,Λ₂) = (a₁ + Λ₁a₂, Λ₁Λ₂)`, and a `Group`
  instance.
- `poincareAct_one`, `poincareAct_mul` — the geometric action
  `f_{(a,Λ)}(x) = f(Λ⁻¹(x − a))` on `Minkowski → ℂ` is a genuine group action
  (identity acts trivially, composition law holds), packaged as a
  `MulAction PoincareGroup (Minkowski → ℂ)` instance.
- `poincareActLin` — the action is ℂ-linear in the test function (the interface
  point: it descends to any ℂ-submodule of test functions).
- `lorentz_preserves_massShell_eq` — Lorentz maps preserve the mass-shell
  *equation* `⟪p,p⟫ = m²` (the `p⁰ > 0` half needs the restricted pin — priced).

**What is PRICED (T5 windows, exact statements, unproved by design):**
- `OneParticleRep_window` — the one-particle Poincaré representation on the mass
  shell, `U₁(a,Λ)ψ(p) = e^{ia·p}ψ(Λ⁻¹p)`;
- `SecondQuantization_window` — second quantization `Γ(U₁)` lifting it to Fock
  space (the unitary implementation);
- the *restricted* (proper orthochronous) pin — `det = 1` plus time-orientation
  preservation as a subgroup condition (composing orientations is the nontrivial
  step; the full O(1,3) defined here does not preserve `p⁰ > 0`).

Interface note: everything is stated over `Minkowski → ℂ`, not blocked on the
parallel Schwartz-space effort. When `𝒮(ℝ⁴)` lands as a ℂ-submodule, the same
formula restricts — closure of Schwartz functions under the affine pullback
`x ↦ Λ⁻¹(x − a)` is part of the Schwartz-theory price, not proved here.
-/

/-!
## The Lorentz group O(1,3)
-/

/-- The Lorentz group O(1,3): linear automorphisms of Minkowski space preserving
    the Minkowski form `⟪Λx, Λy⟫ = ⟪x, y⟫`. -/
structure LorentzGroup where
  toLin : Minkowski ≃ₗ[ℝ] Minkowski
  preserves : ∀ x y : Minkowski, minkowskiInner (toLin x) (toLin y) = minkowskiInner x y

@[ext]
theorem LorentzGroup.ext {a b : LorentzGroup} (h : a.toLin = b.toLin) : a = b := by
  obtain ⟨ta, ha⟩ := a
  obtain ⟨tb, hb⟩ := b
  have h' : ta = tb := h
  subst h'
  rfl

/-- Multiplication is composition: `(a * b) x = a (b x)`, i.e. apply `b`
    first. With `LinearEquiv.trans_apply : (e₁.trans e₂) x = e₂ (e₁ x)` this is
    `b.toLin.trans a.toLin`. -/
instance : Mul LorentzGroup where
  mul a b := ⟨b.toLin.trans a.toLin, fun x y => by
    simp only [LinearEquiv.trans_apply]
    exact (a.preserves _ _).trans (b.preserves _ _)⟩

instance : One LorentzGroup :=
  ⟨⟨LinearEquiv.refl ℝ Minkowski, fun _ _ => rfl⟩⟩

instance : Inv LorentzGroup where
  inv a := ⟨a.toLin.symm, fun x y => by
    have h := a.preserves (a.toLin.symm x) (a.toLin.symm y)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    exact h.symm⟩

@[simp] theorem LorentzGroup.mul_toLin (a b : LorentzGroup) :
    (a * b).toLin = b.toLin.trans a.toLin := rfl

@[simp] theorem LorentzGroup.one_toLin :
    (1 : LorentzGroup).toLin = LinearEquiv.refl ℝ Minkowski := rfl

@[simp] theorem LorentzGroup.inv_toLin (a : LorentzGroup) :
    a⁻¹.toLin = a.toLin.symm := rfl

/-- **T1:** the Lorentz multiplication is associative. -/
theorem lorentz_mul_assoc (a b c : LorentzGroup) :
    (a * b) * c = a * (b * c) := by
  refine LorentzGroup.ext ?_
  simp only [LorentzGroup.mul_toLin]
  exact (LinearEquiv.trans_assoc c.toLin b.toLin a.toLin).symm

/-- **T1:** the identity Lorentz transformation acts trivially. -/
theorem lorentz_one_mul (a : LorentzGroup) : 1 * a = a := by
  refine LorentzGroup.ext ?_
  simp only [LorentzGroup.mul_toLin, LorentzGroup.one_toLin]
  exact LinearEquiv.trans_refl a.toLin

/-- **T1:** inverse Lorentz transformations cancel on the left. -/
theorem lorentz_inv_mul_cancel (a : LorentzGroup) : a⁻¹ * a = 1 := by
  refine LorentzGroup.ext ?_
  simp only [LorentzGroup.mul_toLin, LorentzGroup.inv_toLin, LorentzGroup.one_toLin]
  exact LinearEquiv.self_trans_symm a.toLin

/-- **T1:** the Lorentz group is a group. -/
instance : Group LorentzGroup :=
  Group.ofLeftAxioms lorentz_mul_assoc lorentz_one_mul lorentz_inv_mul_cancel

/-!
## The Poincaré group (translations ⋊ Lorentz)
-/

/-- The Poincaré group: spacetime translations semidirect the Lorentz group,
    with `(a₁,Λ₁)·(a₂,Λ₂) = (a₁ + Λ₁a₂, Λ₁Λ₂)`. -/
structure PoincareGroup where
  trans : Minkowski
  lor : LorentzGroup

@[ext]
theorem PoincareGroup.ext {a b : PoincareGroup}
    (ht : a.trans = b.trans) (hl : a.lor = b.lor) : a = b := by
  obtain ⟨ta, la⟩ := a
  obtain ⟨tb, lb⟩ := b
  have ht' : ta = tb := ht
  have hl' : la = lb := hl
  subst ht'
  subst hl'
  rfl

instance : Mul PoincareGroup where
  mul g₁ g₂ := ⟨g₁.trans + g₁.lor.toLin g₂.trans, g₁.lor * g₂.lor⟩

instance : One PoincareGroup := ⟨⟨0, 1⟩⟩

instance : Inv PoincareGroup where
  inv g := ⟨-g.lor.toLin.symm g.trans, g.lor⁻¹⟩

@[simp] theorem PoincareGroup.mul_trans (g₁ g₂ : PoincareGroup) :
    (g₁ * g₂).trans = g₁.trans + g₁.lor.toLin g₂.trans := rfl

@[simp] theorem PoincareGroup.mul_lor (g₁ g₂ : PoincareGroup) :
    (g₁ * g₂).lor = g₁.lor * g₂.lor := rfl

@[simp] theorem PoincareGroup.one_trans : (1 : PoincareGroup).trans = 0 := rfl

@[simp] theorem PoincareGroup.one_lor : (1 : PoincareGroup).lor = 1 := rfl

@[simp] theorem PoincareGroup.inv_trans (g : PoincareGroup) :
    g⁻¹.trans = -g.lor.toLin.symm g.trans := rfl

@[simp] theorem PoincareGroup.inv_lor (g : PoincareGroup) :
    g⁻¹.lor = g.lor⁻¹ := rfl

/-- **T1:** the Poincaré multiplication is associative. -/
theorem poincare_mul_assoc (a b c : PoincareGroup) :
    (a * b) * c = a * (b * c) := by
  refine PoincareGroup.ext ?_ ?_
  · simp only [PoincareGroup.mul_trans, PoincareGroup.mul_lor, LorentzGroup.mul_toLin,
      LinearEquiv.trans_apply, map_add]
    exact add_assoc _ _ _
  · simp only [PoincareGroup.mul_lor]
    exact lorentz_mul_assoc _ _ _

/-- **T1:** the identity Poincaré transformation acts trivially. -/
theorem poincare_one_mul (a : PoincareGroup) : 1 * a = a := by
  refine PoincareGroup.ext ?_ ?_
  · simp only [PoincareGroup.mul_trans, PoincareGroup.one_trans, PoincareGroup.one_lor,
      LorentzGroup.one_toLin, LinearEquiv.refl_apply, zero_add]
  · simp only [PoincareGroup.mul_lor, PoincareGroup.one_lor, lorentz_one_mul]

/-- **T1:** inverse Poincaré transformations cancel on the left. -/
theorem poincare_inv_mul_cancel (a : PoincareGroup) : a⁻¹ * a = 1 := by
  refine PoincareGroup.ext ?_ ?_
  · simp only [PoincareGroup.mul_trans, PoincareGroup.inv_trans, PoincareGroup.inv_lor,
      PoincareGroup.one_trans, LorentzGroup.inv_toLin]
    exact neg_add_cancel _
  · simp only [PoincareGroup.mul_lor, PoincareGroup.inv_lor, PoincareGroup.one_lor,
      lorentz_inv_mul_cancel]

/-- **T1:** the Poincaré group is a group. -/
instance : Group PoincareGroup :=
  Group.ofLeftAxioms poincare_mul_assoc poincare_one_mul poincare_inv_mul_cancel

/-!
## The geometric action on test functions (T1)
-/

/-- The geometric action of the Poincaré group on test functions:
    `f_{(a,Λ)}(x) = f(Λ⁻¹(x − a))`. Stated over `Minkowski → ℂ` (interface note
    in the file header: not blocked on the Schwartz-space effort). -/
def poincareAct (g : PoincareGroup) (f : Minkowski → ℂ) : Minkowski → ℂ :=
  fun x => f (g.lor.toLin.symm (x - g.trans))

/-- **T1:** the identity acts trivially on test functions. -/
theorem poincareAct_one (f : Minkowski → ℂ) : poincareAct 1 f = f := by
  funext x
  show f ((1 : PoincareGroup).lor.toLin.symm (x - (1 : PoincareGroup).trans)) = f x
  rw [PoincareGroup.one_trans, PoincareGroup.one_lor, LorentzGroup.one_toLin, sub_zero]
  have h : (LinearEquiv.refl ℝ Minkowski).symm x = x := by simp
  rw [h]

/-- **T1:** the composition law — `f_{(g₁g₂)} = (f_{g₂})_{g₁}`. This is the
    genuine group-action law for the geometric half of W2. -/
theorem poincareAct_mul (g₁ g₂ : PoincareGroup) (f : Minkowski → ℂ) :
    poincareAct (g₁ * g₂) f = poincareAct g₁ (poincareAct g₂ f) := by
  funext x
  show f ((g₁ * g₂).lor.toLin.symm (x - (g₁ * g₂).trans))
      = f (g₂.lor.toLin.symm (g₁.lor.toLin.symm (x - g₁.trans) - g₂.trans))
  rw [PoincareGroup.mul_trans, PoincareGroup.mul_lor, LorentzGroup.mul_toLin,
    LinearEquiv.trans_symm, LinearEquiv.trans_apply]
  have h : g₁.lor.toLin.symm (x - (g₁.trans + g₁.lor.toLin g₂.trans))
      = g₁.lor.toLin.symm (x - g₁.trans) - g₂.trans := by
    have h1 : x - (g₁.trans + g₁.lor.toLin g₂.trans)
        = (x - g₁.trans) - g₁.lor.toLin g₂.trans := (sub_sub _ _ _).symm
    rw [h1, map_sub, LinearEquiv.symm_apply_apply]
  rw [h]

/-- **T1:** the geometric action packaged as a genuine group action. -/
instance : SMul PoincareGroup (Minkowski → ℂ) := ⟨poincareAct⟩

instance : MulAction PoincareGroup (Minkowski → ℂ) where
  one_smul f := poincareAct_one f
  mul_smul g₁ g₂ f := poincareAct_mul g₁ g₂ f

/-- **T1 (interface point):** the geometric action is ℂ-linear in the test
    function, so it descends to any ℂ-submodule of `Minkowski → ℂ`. -/
def poincareActLin (g : PoincareGroup) : (Minkowski → ℂ) →ₗ[ℂ] (Minkowski → ℂ) where
  toFun := poincareAct g
  map_add' f₁ f₂ := by funext x; rfl
  map_smul' c f := by funext x; rfl

/-!
## The mass shell (T1 set; measure priced)
-/

/-- The positive mass shell `{p : ⟪p,p⟫ = m², p⁰ > 0}` — exactly statable as a
    set (T1). The Lorentz-invariant *measure* on it is the priced part. -/
def massShell (m : ℝ) : Set Minkowski :=
  {p | minkowskiInner p p = m ^ 2 ∧ 0 < p 0}

/-- **T1:** Lorentz maps preserve the mass-shell *equation* `⟪p,p⟫ = m²`.
    The `p⁰ > 0` half is NOT preserved by all of O(1,3) (e.g. time reversal) —
    it needs the restricted (proper orthochronous) pin, priced in
    `OneParticleRep_window`. -/
theorem lorentz_preserves_massShell_eq (Λ : LorentzGroup) (p : Minkowski) (m : ℝ)
    (h : minkowskiInner p p = m ^ 2) :
    minkowskiInner (Λ.toLin p) (Λ.toLin p) = m ^ 2 := by
  rw [Λ.preserves p p]
  exact h

/-!
## T5 windows: the representation-theoretic half (exact statements, unproved by design)
-/

/-- **T2 marker:** the bosonic/fermionic Fock space *with* its inner product and
    completion — the W0 gap. `FreeField.lean` builds the algebraic Fock space;
    the Hilbert completion is the missing piece. -/
structure FockMarker where
  carrier : Type

/-- **T5 window:** the one-particle Poincaré representation on the mass shell.

    Exact statement. Let `h = L²(Hₘ⁺, dμ)` be the one-particle Hilbert space
    over the positive mass shell `Hₘ⁺ = {p : ⟪p,p⟫ = m², p⁰ > 0}` with the
    Lorentz-invariant measure `dμ = d³p / (2E_p)`. Then
    `U₁(a,Λ) ψ (p) = e^{i a·p} ψ (Λ⁻¹ p)` is a strongly continuous unitary
    representation of the restricted Poincaré group. As a Prop: `U1` is a
    homomorphism into unitaries, and the displayed momentum-space formula holds
    for the marked wavefunction-evaluation and plane-wave maps, with the marked
    shell action `shellAct`.

    PRICE: (i) the invariant measure `dμ` on the hyperboloid — needs the coarea
    formula / disintegration for the level set `{p² = m²}`, absent from Mathlib
    2026; (ii) unitarity of `U₁` — needs `Λ`-invariance of `dμ` from (i);
    (iii) strong continuity — needs dominated convergence on the shell;
    (iv) the *restricted* (proper orthochronous) hypothesis — the `p⁰ > 0` half
    of the shell is not preserved by all of O(1,3), so the formula as stated
    needs the restricted pin (det = 1 + time-orientation as a subgroup
    condition; composing orientations is the nontrivial step).
    What would discharge it: measure theory on submanifolds + the standard free
    one-particle construction (established mathematics — Wigner 1939; only the
    formalization is blocked). -/
def OneParticleRep_window (m : ℝ)
    (h : Type*) [NormedAddCommGroup h] [InnerProductSpace ℂ h] [CompleteSpace h]
    (U1 : PoincareGroup → (h ≃ₗᵢ[ℂ] h))
    (wavefn : h → massShell m → ℂ)
    (planeWave : Minkowski → massShell m → ℂ)
    (shellAct : PoincareGroup → massShell m → massShell m) : Prop :=
  (∀ g₁ g₂ : PoincareGroup, U1 (g₁ * g₂) = (U1 g₁).trans (U1 g₂)) ∧
  (U1 1 = LinearIsometryEquiv.refl ℂ h) ∧
  ∀ (g : PoincareGroup) (ψ : h) (p : massShell m),
    wavefn (U1 g ψ) p = planeWave g.trans p * wavefn ψ (shellAct g p)

/-- **T5 window:** second quantization — the unitary implementation on Fock space.

    Exact statement. Given the one-particle unitary representation `U1` of the
    (restricted) Poincaré group on `h`, second quantization produces a unitary
    representation `Γ(U1)` on the bosonic/fermionic Fock space `Γ(h)` by
    `Γ(U1)(ψ₁ ⊗ ⋯ ⊗ ψₙ) = U1ψ₁ ⊗ ⋯ ⊗ U1ψₙ` (and `Γ(U1)Ω = Ω`) — a homomorphism
    into unitaries fixing the vacuum. As a Prop: the homomorphism law, the
    identity law, and vacuum invariance, with the Fock space marked.

    PRICE: (i) the Fock space *with* its inner product and completion — the W0
    gap (no Fock inner product in Mathlib 2026; `FreeField.lean` builds the
    algebraic Fock space only); (ii) unitarity of `Γ(U1)` — needs the inner
    product from (i). The tensor-factor formula is the exact shape; the analytic
    content (completion, unitarity) is the gap. (`_U1` names the one-particle
    input being lifted; the formula determining `GammaU` from it,
    `Γ(U1)(ψ₁⊗⋯⊗ψₙ) = U1ψ₁⊗⋯⊗U1ψₙ`, is part of the priced construction.)
    What would discharge it: the Fock inner product + completion + the standard
    second-quantization construction (established mathematics; formalization-
    blocked only). -/
def SecondQuantization_window
    (h : Type*) [NormedAddCommGroup h] [InnerProductSpace ℂ h] [CompleteSpace h]
    (Fock : FockMarker)
    [NormedAddCommGroup Fock.carrier] [InnerProductSpace ℂ Fock.carrier]
    [CompleteSpace Fock.carrier]
    (_U1 : PoincareGroup → (h ≃ₗᵢ[ℂ] h))
    (GammaU : PoincareGroup → (Fock.carrier ≃ₗᵢ[ℂ] Fock.carrier))
    (vac : Fock.carrier) : Prop :=
  (∀ g₁ g₂ : PoincareGroup, GammaU (g₁ * g₂) = (GammaU g₁).trans (GammaU g₂)) ∧
  (GammaU 1 = LinearIsometryEquiv.refl ℂ Fock.carrier) ∧
  ∀ g : PoincareGroup, GammaU g vac = vac

end ThetLogos
