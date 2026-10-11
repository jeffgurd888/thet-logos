import Mathlib.Tactic
import ThetLogos.InnerFluctuations

namespace ThetLogos

/-!
# ThetLogos.ClassicalYangMills — THEORIES INTAKE Candidate 2: classical Yang-Mills

Tier header.
- **Scope:** CLASSICAL Yang-Mills gauge theory only: connections (inner
  fluctuations), the curvature 2-form, gauge transformations, and the
  Yang-Mills action `Tr(F²)`. The QUANTUM mass gap is QUARANTINED T5
  (`ThetLogos.MassGapDossier`) — this file proves nothing about it, claims
  nothing about it, and does not touch it.
- **T1 (proved, zero sorrys):** the gauge group action on operators
  (group laws, self-adjointness preservation, trace-invariance of
  `Tr(Xᵏ)`); the represented curvature 2-form `F = Σᵢ[D,aᵢ][D,bᵢ] + A²`
  from 1-form data, with EXACT gauge covariance
  (`repCurvature_gauge_covariant`); gauge invariance of the Yang-Mills
  action `Tr(F²)`; the commutator Jacobi identity (the algebraic core of
  Bianchi).
- **T2 (definitions):** `IsUnitaryMat`, `gaugeAct`, `repCurvature`,
  `ymAction`, `IsFieldStrength`.
- **Priced windows (not claimed):** the junk-ideal quotient (the curvature
  here is the represented 2-form BEFORE junk is quotiented); the continuum
  action `∫_M Tr(F∧⋆F)` (needs the manifold factor constructed, currently
  T2-axiomatized in `ProductTriple`); the full Bianchi identity `DF = 0`
  (needs the differential calculus on 2-forms).
- **6-dim caveat (carried everywhere the gauge algebra is discussed):**
  the represented finite gauge algebra is 6-dimensional real — Option-A
  kills the `M₃(ℂ)` summand in the representation (`InnerFluctuations`
  header). Nothing here claims the full SM gauge group
  `SU(3)×SU(2)×U(1)`; the gauge group below is the unitary group of the
  represented finite algebra.

## Fit-test mapping (classical YM → formalized objects)

- Gauge potential `A` ↔ algebraic 1-form `IsAlgebraicOneForm`
  (`InnerFluctuations.lean`, T1). On the almost-commutative product the
  fluctuations split (`prod_commutator_decomp`, `ProductTriple.lean`, T1)
  into manifold 1-forms `[D_M,f]⊗a` — the genuine spacetime gauge fields —
  and finite 1-forms `Γ_M f⊗[D_F,a]` (scalars).
- Field strength `F = dA + A²` ↔ `repCurvature` (T2 def, T1 covariance):
  the represented 2-form `Σᵢ[D,aᵢ][D,bᵢ] + A²` built from 1-form data.
  The junk-ideal quotient is NOT performed (priced).
- Gauge transformation `A ↦ u[D,u*] + uAu*`, `F ↦ uFu*` ↔ `gaugeAct`
  (T2 def, T1 group action) and `repCurvature_gauge_covariant` (T1).
- Yang-Mills action `∫Tr(F∧⋆F)` ↔ `ymAction F = Tr(F*F)` (T2 structured
  target; the integral over `M` is priced) with T1 gauge invariance.
- Bianchi `DF = 0` ↔ the commutator Jacobi identity (T1, the algebraic
  core); the full identity needs the differential calculus (priced).
-/

/-! ## §1. Classical gauge data = inner fluctuations (mapping, by reference)

The classical gauge potential is already formalized: an algebraic 1-form
`A = ∑ᵢ π(aᵢ)[D_F, π(bᵢ)]` (`IsAlgebraicOneForm`, `InnerFluctuations.lean`)
with fluctuated Dirac `D_A = D_F + A + JAJ⁻¹` (`fluctuatedDirac`). The T1
facts this intake rests on:
- `inner_fluctuation_preserves_order_one`: fluctuations preserve order-one;
- `fluctuatedDirac_self_adjoint`: `D_A` is self-adjoint when `D_F, A` are;
- `inner_fluctuation_majorana_subspace`: the Majorana E-block entry is
  unfluctuated.
On the product (`ProductTriple.lean`, T1 `prod_commutator_decomp`) the
fluctuations split into manifold gauge fields and finite scalars — the
manifold factor is what promotes constant gauge parameters to
spacetime-dependent gauge fields. The 6-dim caveat applies: the
represented finite gauge algebra is 6-dimensional real.
-/

/-! ## §2. The gauge group action (T1) -/

/-- A unitary matrix: `u†u = 1` and `uu† = 1`. (Both are stated; for finite
    matrices either implies the other.) Tier T2. -/
def IsUnitaryMat (u : Matrix I32 I32 ℂ) : Prop :=
  u.conjTranspose * u = 1 ∧ u * u.conjTranspose = 1

/-- The gauge action: conjugation `X ↦ uXu†`. Tier T2. -/
def gaugeAct (u X : Matrix I32 I32 ℂ) : Matrix I32 I32 ℂ :=
  u * X * u.conjTranspose

/-- The gauge action is multiplicative (Tier T1 — proved). -/
theorem gaugeAct_mul (u X Y : Matrix I32 I32 ℂ) (h : u.conjTranspose * u = 1) :
    gaugeAct u (X * Y) = gaugeAct u X * gaugeAct u Y := by
  unfold gaugeAct
  calc u * (X * Y) * u.conjTranspose
      = u * X * Y * u.conjTranspose := by simp only [Matrix.mul_assoc]
    _ = u * X * (u.conjTranspose * u) * Y * u.conjTranspose := by
        rw [h]; simp only [Matrix.mul_one]
    _ = (u * X * u.conjTranspose) * (u * Y * u.conjTranspose) := by
        simp only [Matrix.mul_assoc]

/-- The gauge action composes (Tier T1 — proved): `(uv)·X = u·(v·X)`. -/
theorem gaugeAct_comp (u v X : Matrix I32 I32 ℂ) :
    gaugeAct (u * v) X = gaugeAct u (gaugeAct v X) := by
  unfold gaugeAct
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- The identity acts trivially (Tier T1 — proved). -/
theorem gaugeAct_one (X : Matrix I32 I32 ℂ) : gaugeAct 1 X = X := by
  unfold gaugeAct
  simp

/-- The adjoint inverts the action (Tier T1 — proved). -/
theorem gaugeAct_inv (u X : Matrix I32 I32 ℂ) (hu : IsUnitaryMat u) :
    gaugeAct u (gaugeAct u.conjTranspose X) = X := by
  obtain ⟨h1, h2⟩ := hu
  unfold gaugeAct
  rw [Matrix.conjTranspose_conjTranspose]
  calc u * (u.conjTranspose * X * u) * u.conjTranspose
      = (u * u.conjTranspose) * X * (u * u.conjTranspose) := by
        simp only [Matrix.mul_assoc]
    _ = X := by rw [h2]; simp

/-- The gauge action preserves self-adjointness (Tier T1 — proved). -/
theorem gaugeAct_selfAdjoint (u X : Matrix I32 I32 ℂ)
    (hX : IsSelfAdjoint X) : IsSelfAdjoint (gaugeAct u X) := by
  have hX' : X.conjTranspose = X := hX
  show (u * X * u.conjTranspose).conjTranspose = u * X * u.conjTranspose
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hX', Matrix.mul_assoc]

/-- The gauge action preserves powers (Tier T1 — proved). -/
theorem gaugeAct_pow (u X : Matrix I32 I32 ℂ) (hu : IsUnitaryMat u) (k : ℕ) :
    (gaugeAct u X) ^ k = gaugeAct u (X ^ k) := by
  induction k with
  | zero =>
    simp only [pow_zero]
    unfold gaugeAct
    rw [Matrix.mul_one, hu.2]
  | succ k ih =>
    rw [pow_succ, pow_succ, ih, gaugeAct_mul _ _ _ hu.1]

/-- The gauge action preserves the trace (Tier T1 — proved). -/
theorem gaugeAct_trace (u X : Matrix I32 I32 ℂ) (h : u.conjTranspose * u = 1) :
    Matrix.trace (gaugeAct u X) = Matrix.trace X := by
  unfold gaugeAct
  rw [Matrix.trace_mul_comm (u * X) u.conjTranspose, ← Matrix.mul_assoc, h,
    Matrix.one_mul]

/-- Gauge invariance of the heat-trace invariants (Tier T1 — proved):
    `Tr((uXu†)ᵏ) = Tr(Xᵏ)`. These are the finite shadows from which the
    spectral action — and hence the Yang-Mills term — is built. -/
theorem gaugeAct_trace_pow (u X : Matrix I32 I32 ℂ) (hu : IsUnitaryMat u) (k : ℕ) :
    Matrix.trace ((gaugeAct u X) ^ k) = Matrix.trace (X ^ k) := by
  rw [gaugeAct_pow _ _ hu, gaugeAct_trace _ _ hu.1]

/-! ## §3. The represented curvature 2-form (T2 def, T1 covariance) -/

/-- The gauge action distributes over subtraction (Tier T1 — proved). -/
theorem gaugeAct_sub (u X Y : Matrix I32 I32 ℂ) :
    gaugeAct u (X - Y) = gaugeAct u X - gaugeAct u Y := by
  unfold gaugeAct
  rw [Matrix.mul_sub, Matrix.sub_mul]

/-- The gauge action distributes over addition (Tier T1 — proved). -/
theorem gaugeAct_add (u X Y : Matrix I32 I32 ℂ) :
    gaugeAct u (X + Y) = gaugeAct u X + gaugeAct u Y := by
  unfold gaugeAct
  rw [Matrix.mul_add, Matrix.add_mul]

/-- The gauge action commutes with finite sums (Tier T1 — proved). -/
theorem gaugeAct_sum (u : Matrix I32 I32 ℂ) (k : ℕ)
    (f : Fin k → Matrix I32 I32 ℂ) :
    gaugeAct u (∑ i, f i) = ∑ i, gaugeAct u (f i) := by
  unfold gaugeAct
  rw [Finset.mul_sum, Finset.sum_mul]

/-- The gauge action preserves commutators (Tier T1 — proved). -/
theorem gaugeAct_commutator (u X Y : Matrix I32 I32 ℂ)
    (h : u.conjTranspose * u = 1) :
    gaugeAct u (X * Y - Y * X)
      = gaugeAct u X * gaugeAct u Y - gaugeAct u Y * gaugeAct u X := by
  rw [gaugeAct_sub, gaugeAct_mul _ _ _ h, gaugeAct_mul _ _ _ h]

/-- Represented curvature 2-form from 1-form data (Tier T2 — definition):
    `F = ∑ᵢ[D,aᵢ][D,bᵢ] + A²` where `A = ∑ᵢ aᵢ[D,bᵢ]`.
    This is the represented 2-form BEFORE the junk-ideal quotient
    (priced window — see header). -/
def repCurvature (D : Matrix I32 I32 ℂ) (k : ℕ)
    (a b : Fin k → Matrix I32 I32 ℂ) : Matrix I32 I32 ℂ :=
  (∑ i : Fin k, (D * a i - a i * D) * (D * b i - b i * D)) +
    (∑ i : Fin k, a i * (D * b i - b i * D)) ^ 2

/-- Exact gauge covariance of the represented curvature (Tier T1 — proved):
    simultaneous unitary conjugation of the data `(D, aᵢ, bᵢ)` conjugates `F`.
    This is the algebraic core of `F ↦ uFu*`. The inhomogeneous `u[D,u*]`
    piece of the full fluctuation transformation law is priced (see header). -/
theorem repCurvature_gauge_covariant (u D : Matrix I32 I32 ℂ)
    (hu : IsUnitaryMat u) (k : ℕ) (a b : Fin k → Matrix I32 I32 ℂ) :
    repCurvature (gaugeAct u D) k (fun i => gaugeAct u (a i))
        (fun i => gaugeAct u (b i))
      = gaugeAct u (repCurvature D k a b) := by
  have h1 := hu.1
  have term1 : ∀ i : Fin k,
      (gaugeAct u D * gaugeAct u (a i) - gaugeAct u (a i) * gaugeAct u D) *
      (gaugeAct u D * gaugeAct u (b i) - gaugeAct u (b i) * gaugeAct u D)
      = gaugeAct u ((D * a i - a i * D) * (D * b i - b i * D)) := by
    intro i
    rw [← gaugeAct_commutator _ _ _ h1, ← gaugeAct_commutator _ _ _ h1,
      ← gaugeAct_mul _ _ _ h1]
  have term2 : ∀ i : Fin k,
      gaugeAct u (a i) *
      (gaugeAct u D * gaugeAct u (b i) - gaugeAct u (b i) * gaugeAct u D)
      = gaugeAct u (a i * (D * b i - b i * D)) := by
    intro i
    rw [← gaugeAct_commutator _ _ _ h1, ← gaugeAct_mul _ _ _ h1]
  unfold repCurvature
  have s1 : (∑ i : Fin k, (gaugeAct u D * gaugeAct u (a i)
      - gaugeAct u (a i) * gaugeAct u D) *
      (gaugeAct u D * gaugeAct u (b i) - gaugeAct u (b i) * gaugeAct u D))
      = gaugeAct u (∑ i : Fin k, (D * a i - a i * D) * (D * b i - b i * D)) :=
    calc (∑ i : Fin k, (gaugeAct u D * gaugeAct u (a i)
          - gaugeAct u (a i) * gaugeAct u D) *
          (gaugeAct u D * gaugeAct u (b i) - gaugeAct u (b i) * gaugeAct u D))
        = ∑ i : Fin k, gaugeAct u ((D * a i - a i * D) * (D * b i - b i * D)) :=
          Finset.sum_congr rfl (fun i _ => term1 i)
      _ = gaugeAct u (∑ i : Fin k, (D * a i - a i * D) * (D * b i - b i * D)) :=
          (gaugeAct_sum u k _).symm
  have s2 : (∑ i : Fin k, gaugeAct u (a i) *
      (gaugeAct u D * gaugeAct u (b i) - gaugeAct u (b i) * gaugeAct u D))
      = gaugeAct u (∑ i : Fin k, a i * (D * b i - b i * D)) :=
    calc (∑ i : Fin k, gaugeAct u (a i) *
          (gaugeAct u D * gaugeAct u (b i) - gaugeAct u (b i) * gaugeAct u D))
        = ∑ i : Fin k, gaugeAct u (a i * (D * b i - b i * D)) :=
          Finset.sum_congr rfl (fun i _ => term2 i)
      _ = gaugeAct u (∑ i : Fin k, a i * (D * b i - b i * D)) :=
          (gaugeAct_sum u k _).symm
  rw [s1, s2, gaugeAct_pow _ _ hu, ← gaugeAct_add]

/-! ## §4. The Yang-Mills action (T2 target, T1 gauge invariance) -/

/-- The Yang-Mills action `S_YM[F] = Tr(F†F)` (Tier T2 — structured target).
    The continuum integral `∫_M Tr(F∧⋆F)` is priced (needs the manifold
    factor); this is its finite represented shadow. -/
def ymAction (F : Matrix I32 I32 ℂ) : ℂ :=
  Matrix.trace (F.conjTranspose * F)

/-- A field strength is self-adjoint (Tier T2 — definition). -/
def IsFieldStrength (F : Matrix I32 I32 ℂ) : Prop := IsSelfAdjoint F

/-- The gauge action commutes with adjoints (Tier T1 — proved). -/
theorem gaugeAct_conjTranspose (u X : Matrix I32 I32 ℂ) :
    (gaugeAct u X).conjTranspose = gaugeAct u (X.conjTranspose) := by
  unfold gaugeAct
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

/-- Gauge invariance of the Yang-Mills action (Tier T1 — proved):
    `S_YM[uFu†] = S_YM[F]`. -/
theorem ymAction_gauge_invariant (u F : Matrix I32 I32 ℂ)
    (hu : IsUnitaryMat u) :
    ymAction (gaugeAct u F) = ymAction F := by
  obtain ⟨h1, _⟩ := hu
  have key : (gaugeAct u F).conjTranspose * (gaugeAct u F)
      = gaugeAct u (F.conjTranspose * F) := by
    rw [gaugeAct_conjTranspose, ← gaugeAct_mul _ _ _ h1]
  unfold ymAction
  rw [key]
  exact gaugeAct_trace u _ h1

/-! ## §5. Bianchi core: the commutator Jacobi identity (T1) -/

/-- The commutator Jacobi identity (Tier T1 — proved): the algebraic core of
    the Bianchi identity `DF = 0`. The full Bianchi needs the differential
    calculus on 2-forms (priced window — see header). -/
theorem commutator_jacobi (X Y Z : Matrix I32 I32 ℂ) :
    (X * (Y * Z - Z * Y) - (Y * Z - Z * Y) * X)
    + (Y * (Z * X - X * Z) - (Z * X - X * Z) * Y)
    + (Z * (X * Y - Y * X) - (X * Y - Y * X) * Z) = 0 := by
  simp only [Matrix.mul_sub, Matrix.sub_mul]
  noncomm_ring

end ThetLogos
