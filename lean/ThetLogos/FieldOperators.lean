import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import ThetLogos.FreeField

namespace ThetLogos

/-!
# ThetLogos.FieldOperators — smeared field operators, creation part

Source: Rung 4 Track 3 (2026-10-11), Jeff's "Build the house and use the gaps
as windows."

**What this file IS.** The fermionic core of `FreeField.lean` pushed one step
toward genuine field operators: creators smeared with test functions.
The test-function space is a T2 marker (`TestFunctionMarker` — Mathlib 2026
has no Schwartz space), and the smearing map `smear : 𝕋 →ₗ[ℂ] V` is T2-marker
data (in a real construction: the Dirac solution operator / positive-frequency
projector). Everything proved below is T1 *conditional on the marker*:
linearity of the smeared creators in the test function, the smeared CAR
(creator half), smeared Pauli exclusion, vanishing smeared one-point
functions, and smeared vacuum cyclicity under a surjective smearing map.
The bosonic mirror is included for symmetry.

**What this file is NOT.** The full smeared field `ψ(f) = a†(f) + a(f)`.
The annihilation half needs adjoints, hence the Fock inner product, which
Mathlib does not have — that is priced as a window (`fermionicFieldCAR_window`,
`bosonicFieldCCR_window`), not a sorry.

Honesty tiers in this file:
- **T1 (proved):** `createFerm_add`, `createFerm_smul` (linearity of the
  unsmeared creators — new), `createFermSmeared_add`, `createFermSmeared_smul`,
  `createFermSmeared_anticommute`, `createFermSmeared_sq`,
  `createFermSmeared_onePoint`, `smearedFermion_cyclic_of_surjective`
  (fermionic); `create_add`, `create_smul`, `createSmeared_add`,
  `createSmeared_smul`, `createSmeared_commute`,
  `smearedBoson_cyclic_of_surjective` (bosonic).
- **T2 (labeled markers):** `TestFunctionMarker`, the smearing map `smear`.
- **T5 (priced windows, exact statements, unproved by design):**
  `fermionicFieldCAR_window`, `bosonicFieldCCR_window`.
-/

/-- **T2 marker:** the test-function space. Mathlib (2026) has no Schwartz
    space `𝒮(ℝ⁴)`; this labels the placeholder. In a real construction the
    carrier would be `𝒮(ℝ⁴, ℂ⁴)` (Dirac spinor test functions) with pointwise
    vector-space operations. -/
structure TestFunctionMarker where
  carrier : Type

variable (V : Type*) [AddCommGroup V] [Module ℂ V]
variable (T : TestFunctionMarker) [AddCommGroup T.carrier] [Module ℂ T.carrier]
/- **T2-marker data:** the one-particle smearing map. In a real construction
   this is the Dirac solution operator (positive/negative-frequency
   projection); here it is an abstract linear map the T1 results are
   conditional on. -/
variable (smear : T.carrier →ₗ[ℂ] V)

/-!
## Fermionic smeared creators

`a†(f) = a†(smear f)`: the creation part of the smeared Dirac field.
-/

/-- The unsmeared fermionic creator is additive in the one-particle vector
    (T1). -/
theorem createFerm_add (v w : V) :
    createFerm V (v + w) = createFerm V v + createFerm V w := by
  ext x
  simp only [createFerm, LinearMap.mulLeft_apply, LinearMap.add_apply, map_add,
    add_mul]

/-- The unsmeared fermionic creator is homogeneous in the one-particle vector
    (T1). -/
theorem createFerm_smul (c : ℂ) (v : V) :
    createFerm V (c • v) = c • createFerm V v := by
  ext x
  simp only [createFerm, LinearMap.mulLeft_apply, LinearMap.smul_apply, map_smul,
    smul_mul_assoc]

/-- Smeared fermionic creation operator: `a†(f)` is left multiplication by
    `ι (smear f)`. This is the creation half of the smeared Dirac field
    `ψ(f) = a†(f) + a(f)`; the annihilation half is the priced window below. -/
def createFermSmeared (f : T.carrier) : fermionicFock V →ₗ[ℂ] fermionicFock V :=
  createFerm V (smear f)

/-- Smeared creators are additive in the test function (T1): the field is
    linear in `f` at the creation-operator level. -/
theorem createFermSmeared_add (f g : T.carrier) :
    createFermSmeared V T smear (f + g)
      = createFermSmeared V T smear f + createFermSmeared V T smear g := by
  simp only [createFermSmeared, map_add, createFerm_add]

/-- Smeared creators are homogeneous in the test function (T1). -/
theorem createFermSmeared_smul (c : ℂ) (f : T.carrier) :
    createFermSmeared V T smear (c • f)
      = c • createFermSmeared V T smear f := by
  simp only [createFermSmeared, map_smul, createFerm_smul]

/-- Smeared CAR, creator half: `{a†(f), a†(g)} = 0` (T1). Follows directly
    from the unsmeared `createFerm_anticommute`. -/
theorem createFermSmeared_anticommute (f g : T.carrier) :
    (createFermSmeared V T smear f).comp (createFermSmeared V T smear g)
      = -((createFermSmeared V T smear g).comp (createFermSmeared V T smear f)) :=
  createFerm_anticommute V (smear f) (smear g)

/-- Smeared Pauli exclusion: `a†(f)² = 0` (T1). No test function creates two
    fermions in the same smeared one-particle state. -/
theorem createFermSmeared_sq (f : T.carrier) :
    (createFermSmeared V T smear f).comp (createFermSmeared V T smear f) = 0 :=
  pauli_exclusion V (smear f)

/-- The smeared one-point function vanishes (T1): the algebraic vacuum
    functional kills every smeared creator. -/
theorem createFermSmeared_onePoint (f : T.carrier) :
    fermionExp V (ExteriorAlgebra.ι (R := ℂ) (M := V) (smear f)) = 0 :=
  fermion_onePoint_vanishes V (smear f)

/-- Smeared vacuum cyclicity (T1): a *surjective* smearing map loses no
    creators — the algebra generated by the smeared creators is the whole
    fermionic Fock algebra. Smearing does not shrink the field algebra. -/
theorem smearedFermion_cyclic_of_surjective (hsurj : Function.Surjective smear) :
    Algebra.adjoin ℂ
        (Set.range (fun f : T.carrier => ExteriorAlgebra.ι (R := ℂ) (M := V) (smear f)))
      = ⊤ := by
  have hset : Set.range (fun f : T.carrier => ExteriorAlgebra.ι (R := ℂ) (M := V) (smear f))
      = Set.range (ExteriorAlgebra.ι (R := ℂ) (M := V)) := by
    ext y
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨smear f, rfl⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨f, rfl⟩ := hsurj v
      exact ⟨f, rfl⟩
  rw [hset]
  exact fermion_vacuum_cyclic V

/-!
## Bosonic smeared creators (mirror)

The same construction on the symmetric-algebra side, for symmetry with the
fermionic line above.
-/

/-- The unsmeared bosonic creator is additive in the one-particle vector
    (T1). -/
theorem create_add (v w : V) :
    create V (v + w) = create V v + create V w := by
  ext x
  simp only [create, LinearMap.mulLeft_apply, LinearMap.add_apply, map_add,
    add_mul]

/-- The unsmeared bosonic creator is homogeneous in the one-particle vector
    (T1). -/
theorem create_smul (c : ℂ) (v : V) :
    create V (c • v) = c • create V v := by
  ext x
  simp only [create, LinearMap.mulLeft_apply, LinearMap.smul_apply, map_smul,
    smul_mul_assoc]

/-- Smeared bosonic creation operator: the creation half of the smeared
    scalar field `φ(f) = a†(f) + a(f)`. -/
def createSmeared (f : T.carrier) : bosonicFock V →ₗ[ℂ] bosonicFock V :=
  create V (smear f)

/-- Smeared bosonic creators are additive in the test function (T1). -/
theorem createSmeared_add (f g : T.carrier) :
    createSmeared V T smear (f + g)
      = createSmeared V T smear f + createSmeared V T smear g := by
  simp only [createSmeared, map_add, create_add]

/-- Smeared bosonic creators are homogeneous in the test function (T1). -/
theorem createSmeared_smul (c : ℂ) (f : T.carrier) :
    createSmeared V T smear (c • f) = c • createSmeared V T smear f := by
  simp only [createSmeared, map_smul, create_smul]

/-- Smeared CCR, creator half: `[a†(f), a†(g)] = 0` (T1). -/
theorem createSmeared_commute (f g : T.carrier) :
    (createSmeared V T smear f).comp (createSmeared V T smear g)
      = (createSmeared V T smear g).comp (createSmeared V T smear f) :=
  create_commute V (smear f) (smear g)

/-- Smeared bosonic cyclicity (T1): a surjective smearing map loses no
    bosonic creators either. -/
theorem smearedBoson_cyclic_of_surjective (hsurj : Function.Surjective smear) :
    Algebra.adjoin ℂ
        (Set.range (fun f : T.carrier => SymmetricAlgebra.ι ℂ V (smear f)))
      = ⊤ := by
  have hset : Set.range (fun f : T.carrier => SymmetricAlgebra.ι ℂ V (smear f))
      = Set.range (SymmetricAlgebra.ι ℂ V) := by
    ext y
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨smear f, rfl⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨f, rfl⟩ := hsurj v
      exact ⟨f, rfl⟩
  rw [hset]
  exact vacuum_cyclic V

/-!
## Priced windows: the full smeared fields

The statements below are exact — they pin what the full smeared field
*is* — but unproved by design: each needs the annihilation operators, i.e.
adjoints of the creators, i.e. the Fock inner product, which Mathlib (2026)
does not have. These are windows with clean frames, not sorrys.
-/

/-- **Priced window (T5):** the full smeared fermionic field
    `ψ(f) = a†(f) + a(f)` with the CAR `{ψ(f), ψ(g)} = pairing f g · 1`.

    PRICE — two infrastructure gaps, both absent from Mathlib (2026):
    (i) the annihilation operator `a(f)` is the adjoint of `a†(f)`, so it
    needs the Fock inner product (the `fockInnerProduct` gap logged in
    `FreeField.lean`); (ii) the Dirac pairing on test functions needs the
    solution operator of the Dirac equation (positive/negative-frequency
    projectors), i.e. Schwartz distribution theory.
    What would discharge it: Fock inner product + tempered distributions +
    the free Dirac operator. Note the creator-half CAR `{a†(f), a†(g)} = 0`
    is already T1 above (`createFermSmeared_anticommute`) — this window is
    exactly the missing mixed half. -/
def fermionicFieldCAR_window (pairing : T.carrier → T.carrier → ℂ) : Prop :=
  ∃ annihil : T.carrier → (fermionicFock V →ₗ[ℂ] fermionicFock V),
  ∃ fieldOp : T.carrier → (fermionicFock V →ₗ[ℂ] fermionicFock V),
    (∀ f : T.carrier, fieldOp f = createFermSmeared V T smear f + annihil f) ∧
    ∀ f g : T.carrier,
      (fieldOp f).comp (fieldOp g) + (fieldOp g).comp (fieldOp f)
        = pairing f g • LinearMap.id

/-- **Priced window (T5):** the full smeared bosonic field
    `φ(f) = a†(f) + a(f)` with the CCR `[φ(f), φ(g)] = iΔ(f,g) · 1`,
    where `pjordan` marks the smeared Pauli–Jordan pairing.

    PRICE — same two gaps as the fermionic window: (i) annihilation needs
    the Fock inner product; (ii) the Pauli–Jordan distribution `Δ` needs
    Schwartz theory plus Bessel-function analysis (both absent from
    Mathlib 2026). The creator-half commutator `[a†(f), a†(g)] = 0` is
    already T1 above (`createSmeared_commute`). -/
def bosonicFieldCCR_window (pjordan : T.carrier → T.carrier → ℂ) : Prop :=
  ∃ annihil : T.carrier → (bosonicFock V →ₗ[ℂ] bosonicFock V),
  ∃ fieldOp : T.carrier → (bosonicFock V →ₗ[ℂ] bosonicFock V),
    (∀ f : T.carrier, fieldOp f = createSmeared V T smear f + annihil f) ∧
    ∀ f g : T.carrier,
      (fieldOp f).comp (fieldOp g) - (fieldOp g).comp (fieldOp f)
        = pjordan f g • LinearMap.id

#print axioms createFerm_add
#print axioms createFerm_smul
#print axioms createFermSmeared_add
#print axioms createFermSmeared_smul
#print axioms createFermSmeared_anticommute
#print axioms createFermSmeared_sq
#print axioms createFermSmeared_onePoint
#print axioms smearedFermion_cyclic_of_surjective
#print axioms create_add
#print axioms create_smul
#print axioms createSmeared_add
#print axioms createSmeared_smul
#print axioms createSmeared_commute
#print axioms smearedBoson_cyclic_of_surjective

end ThetLogos
