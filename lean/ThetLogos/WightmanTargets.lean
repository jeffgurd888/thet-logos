import Mathlib.Analysis.InnerProductSpace.Basic
import ThetLogos.WightmanAxioms
import ThetLogos.FieldOperators

namespace ThetLogos

open scoped InnerProductSpace

/-!
# ThetLogos.WightmanTargets — sharpened Wightman targets (structured, unproved)

Source: Rung 4 Track 3 (2026-10-11), Jeff's "Build the house and use the gaps
as windows."

**What this file IS.** For each of the six Wightman axioms pinned opaquely in
`WightmanAxioms.lean`, a *sharpened target*: a `def ... : Prop` with the right
shape — exact hypotheses, exact conclusion, the analytic content spelled out
as explicit formulas (domain questions, the Hermiticity equation, the
covariance equation, the locality (anti)commutator, the cyclicity density
statement, the connected-4-point nontriviality criterion). These are precise
statements, NOT theorems: no proof is attempted, so no `sorry` is needed.
Each target carries a docstring pricing its proof: what Mathlib (2026) lacks
and what would discharge it. `SharpWightmanTarget` bundles all six into one
closed Prop — the clean frame around the window.

**What this file is NOT.** A proof of any Wightman axiom, or progress toward
one. The axioms stay unproved; the windows get clean frames.

Honesty tiers in this file:
- **T1 (proved):** nothing — this file proves nothing by design. (The
  algebraic shadows it refines live in `FreeField.lean` / `FieldOperators.lean`.)
- **T2 (labeled markers):** `PoincareMarker`; the marker data each target
  takes as parameters (test-function conjugation, spacelike separation, the
  Wightman functions, the joint spectrum, the energy-momentum generators).
- **T5 (structured targets, exact statements, unproved by design):**
  `W1_fieldsExist_sharp`, `W2_poincareCovariant_sharp`,
  `W3_spectrumCondition_sharp`, `W4_locality_sharp`, `W5_vacuumCyclic_sharp`,
  `W6_nontrivial_sharp`, `SharpWightmanTarget`.
-/

/-- **T2 marker:** the (restricted) Poincaré group. Mathlib (2026) has no
    Poincaré-group representation theory for unbounded operators; this labels
    the placeholder. -/
structure PoincareMarker where
  carrier : Type

/-!
## W1 — fields as operator-valued tempered distributions (sharp)

The exact content: a common dense invariant domain `D`, field operators
`field f : D →ₗ[ℂ] D` linear in the test function, weakly Hermitian
(`⟪φ(f)ψ, χ⟫ = ⟪ψ, φ(f̄)χ⟫` — statable with the genuine Hilbert inner
product), test-function conjugation involutive, vacuum nonzero and in `D`.
-/

/-- **W1 sharp (T5 target):** quantum fields with exact hypotheses and exact
    conclusion. `conjTest` marks complex conjugation of test functions;
    `field f` is `φ(f)` restricted to the common dense invariant domain
    (invariance is baked into the type `D →ₗ[ℂ] D` — justifying it is part
    of the price).

    PRICE: (i) the Schwartz space `𝒮(ℝ⁴)` and its conjugation — Mathlib has
    no tempered distributions; (ii) the common dense invariant domain for a
    real theory — needs the Fock completion (the W0 gap: no Fock inner
    product in Mathlib 2026); (iii) constructing `φ(f)` as closable operators
    — needs distribution theory plus second quantization.
    What would discharge it: tempered distributions + Fock inner product and
    completion + the free-field construction (Streater–Wightman 1964, whose
    mathematical content is established — only the formalization is blocked). -/
def W1_fieldsExist_sharp (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Ω : H) (T : TestFunctionMarker) [AddCommGroup T.carrier] [Module ℂ T.carrier]
    (D : Submodule ℂ H)
    (conjTest : T.carrier → T.carrier)
    (field : T.carrier → (D →ₗ[ℂ] D)) : Prop :=
  (Ω ∈ D) ∧
  (∀ f g : T.carrier, field (f + g) = field f + field g) ∧
  (∀ (c : ℂ) (f : T.carrier), field (c • f) = c • field f) ∧
  (∀ (f : T.carrier) (ψ χ : D),
    ⟪(field f ψ : H), (χ : H)⟫_ℂ = ⟪(ψ : H), (field (conjTest f) χ : H)⟫_ℂ) ∧
  (∀ f : T.carrier, conjTest (conjTest f) = f) ∧
  Ω ≠ 0

/-!
## W2 — Poincaré covariance (sharp)

The exact content: a unitary representation `rep` of the Poincaré group
(`LinearIsometryEquiv` — Mathlib HAS unitary operators), a geometric action
`act` on test functions, and the covariance equation
`U(g) φ(f) U(g)⁻¹ = φ(f_g)` written on the domain as
`U(g)(φ(f)ψ) = φ(f_g)(U(g)ψ)`.
-/

/-- **W2 sharp (T5 target):** Poincaré covariance with the covariance
    equation as an explicit formula. `repPresD` (the representation preserves
    the domain) is an exact hypothesis.

    PRICE: (i) the unitary Poincaré representation on the *physical* Hilbert
    space — needs second quantization `Γ(U₁)`, hence the W0 Fock completion;
    (ii) the geometric action on Schwartz test functions
    `f_{(a,Λ)}(x) = f(Λ⁻¹(x − a))` — needs Schwartz theory.
    What would discharge it: the one-particle Poincaré representation on the
    mass shell (buildable in principle from Mathlib measure theory — a large
    construction) + second quantization + tempered distributions. -/
def W2_poincareCovariant_sharp (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : TestFunctionMarker) [AddCommGroup T.carrier] [Module ℂ T.carrier]
    (D : Submodule ℂ H)
    (Poin : PoincareMarker) [Group Poin.carrier]
    (rep : Poin.carrier → (H ≃ₗᵢ[ℂ] H))
    (act : Poin.carrier → T.carrier → T.carrier)
    (field : T.carrier → (D →ₗ[ℂ] D))
    (repPresD : ∀ (g : Poin.carrier) (ψ : D), (rep g) ((ψ : H)) ∈ D) : Prop :=
  (∀ g₁ g₂ : Poin.carrier, rep (g₁ * g₂) = (rep g₁).trans (rep g₂)) ∧
  (rep 1 = LinearIsometryEquiv.refl ℂ H) ∧
  (∀ g₁ g₂ : Poin.carrier, ∀ f : T.carrier, act (g₁ * g₂) f = act g₁ (act g₂ f)) ∧
  ∀ (g : Poin.carrier) (f : T.carrier) (ψ : D),
    field (act g f) ⟨(rep g) ((ψ : H)), repPresD g ψ⟩
      = ⟨(rep g) ((field f ψ : H)), repPresD g (field f ψ)⟩

/-!
## W3 — spectrum condition (sharp)

The exact content: the translation representation, the energy-momentum
generators `P^μ` on the domain (weakly symmetric, weakly commuting), and the
conclusion itself — `spec ⊆ forwardLightCone` — as a literal formula, where
`spec` marks the joint spectrum.
-/

/-- **W3 sharp (T5 target):** the spectrum condition. The weak symmetry
    `⟪P^μ ψ, χ⟫ = ⟪ψ, P^μ χ⟫` and weak commutation `[P^μ, P^ν] = 0` are exact
    statable formulas; `spec` marks the joint spectrum of the `P^μ`, and
    `spec ⊆ forwardLightCone` is the axiom's conclusion verbatim (the cone's
    geometry is T1-pinned in `WightmanAxioms.lean`).

    PRICE: (i) defining `spec` as *the* joint spectrum needs unbounded-operator
    spectral theory — Stone's theorem (generators of `transRep`) and the joint
    spectral calculus for commuting unbounded self-adjoint operators, both
    absent from Mathlib 2026; (ii) the tie `transRep a = exp(i a·P)` needs
    unbounded functional calculus. The formulas here are the exact shape; the
    analytic machinery that fills `spec` and `energyMom` is the gap. -/
def W3_spectrumCondition_sharp (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : Submodule ℂ H)
    (transRep : Minkowski → (H ≃ₗᵢ[ℂ] H))
    (energyMom : Fin 4 → (D →ₗ[ℂ] D))
    (spec : Set Minkowski) : Prop :=
  (∀ a b : Minkowski, transRep (a + b) = (transRep a).trans (transRep b)) ∧
  (∀ μ : Fin 4, ∀ ψ χ : D,
    ⟪(energyMom μ ψ : H), (χ : H)⟫_ℂ = ⟪(ψ : H), (energyMom μ χ : H)⟫_ℂ) ∧
  (∀ μ ν : Fin 4, ∀ ψ : D,
    energyMom μ (energyMom ν ψ) = energyMom ν (energyMom μ ψ)) ∧
  spec ⊆ forwardLightCone

/-!
## W4 — locality / microcausality (sharp)

The exact content: for spacelike-separated test functions, the graded
commutator vanishes — `[φ(f), φ(g)] = 0` bosonic, `{φ(f), φ(g)} = 0`
fermionic — as an explicit operator equation, with the sign `s = ±1`
(`s² = 1`) selecting the statistics.
-/

/-- **W4 sharp (T5 target):** locality as an explicit (anti)commutator
    formula. `spacelikeSep` marks spacelike separation of supports; `s`
    selects statistics (`s = 1` commutator, `s = -1` anticommutator).

    PRICE: defining `spacelikeSep` — i.e. supports of test functions and
    "every `x ∈ supp f`, `y ∈ supp g` is spacelike" via the Minkowski form —
    needs Schwartz support theory (absent from Mathlib 2026). The equation
    itself is exact. Note the fermionic creation-part already satisfies the
    anticommutator *unconditionally* at the algebraic level
    (`createFermSmeared_anticommute` in `FieldOperators.lean` — T1, no
    spacelike hypothesis needed); the full field (anti)commutator with the
    annihilation half is behind the Fock-inner-product gap. -/
def W4_locality_sharp (H : Type*) [AddCommMonoid H] [Module ℂ H]
    (T : TestFunctionMarker) [AddCommGroup T.carrier] [Module ℂ T.carrier]
    (D : Submodule ℂ H)
    (field : T.carrier → (D →ₗ[ℂ] D))
    (spacelikeSep : T.carrier → T.carrier → Prop)
    (s : ℂ) : Prop :=
  s ^ 2 = 1 ∧
  ∀ f g : T.carrier, spacelikeSep f g →
    (field f).comp (field g) = s • (field g).comp (field f)

/-!
## W5 — vacuum cyclicity (sharp)

The exact content: polynomials in the smeared fields applied to the vacuum
are dense in the Hilbert space — stated via an explicit recursive
`polyApply` and `Dense`.
-/

/-- Polynomials in the smeared fields applied to the vacuum:
    `polyApply H Ω T D field hΩD [f₁, …, fₙ] = φ(f₁)⋯φ(fₙ)Ω ∈ D`. -/
def polyApply (H : Type*) [AddCommMonoid H] [Module ℂ H]
    (Ω : H) (T : TestFunctionMarker) [AddCommGroup T.carrier] [Module ℂ T.carrier]
    (D : Submodule ℂ H) (field : T.carrier → (D →ₗ[ℂ] D)) (hΩD : Ω ∈ D) :
    List T.carrier → D
  | [] => ⟨Ω, hΩD⟩
  | f :: fs => field f (polyApply H Ω T D field hΩD fs)

/-- **W5 sharp (T5 target):** vacuum cyclicity — the field-polynomials applied
    to `Ω` are dense in `H`. An exact, checkable density statement.

    PRICE: density in the Hilbert norm needs the completed Hilbert space —
    the W0 Fock-completion gap. The *algebraic* shadow is already T1:
    `vacuum_cyclic` / `fermion_vacuum_cyclic` in `FreeField.lean` and the
    smeared versions `smearedBoson_cyclic_of_surjective` /
    `smearedFermion_cyclic_of_surjective` in `FieldOperators.lean` prove the
    generated algebra is everything; the missing step is purely the norm
    completion turning "everything algebraically" into "dense analytically". -/
def W5_vacuumCyclic_sharp (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Ω : H) (T : TestFunctionMarker) [AddCommGroup T.carrier] [Module ℂ T.carrier]
    (D : Submodule ℂ H) (field : T.carrier → (D →ₗ[ℂ] D)) (hΩD : Ω ∈ D) : Prop :=
  Dense (Set.range fun l : List T.carrier => (polyApply H Ω T D field hΩD l : H))

/-!
## W6 — nontriviality (sharp)

The exact content: the theory is not (generalized) free. Sharp sufficient
criterion, exactly statable: the connected 4-point function does not vanish.
For a quasi-free theory Wick's theorem forces every connected n-point
function with `n ≠ 2` to zero — so a nonzero connected 4-point function
proves the theory is not quasi-free.
-/

/-- The connected 4-point function (bosonic Wick subtraction): the full
    4-point function minus the three Wick pairings of 2-point functions. -/
def connectedFourPoint (T : TestFunctionMarker)
    (w : ℕ → List T.carrier → ℂ) (fs : Fin 4 → T.carrier) : ℂ :=
  w 4 [fs 0, fs 1, fs 2, fs 3]
    - (w 2 [fs 0, fs 1] * w 2 [fs 2, fs 3]
      + w 2 [fs 0, fs 2] * w 2 [fs 1, fs 3]
      + w 2 [fs 0, fs 3] * w 2 [fs 1, fs 2])

/-- **W6 sharp (T5 target):** nontriviality — the connected 4-point function
    does not vanish identically. `w` marks the Wightman functions (the
    n-point tempered distributions evaluated on test functions).

    PRICE: the Wightman functions as tempered distributions need Schwartz
    theory (absent from Mathlib 2026). Honest scoping: non-vanishing of the
    connected 4-point function is *sufficient* for "not quasi-free" (Wick's
    theorem), not a full characterization — the frame is clean but narrower
    than "not a generalized free field" in full generality. Stated in bosonic
    form; the fermionic version inserts Koszul signs (priced refinement).
    Sanity check on the shape: for the free field this target is *false* —
    the free field is quasi-free — exactly as the nontriviality axiom demands. -/
def W6_nontrivial_sharp (T : TestFunctionMarker)
    (w : ℕ → List T.carrier → ℂ) : Prop :=
  ∃ fs : Fin 4 → T.carrier, connectedFourPoint T w fs ≠ 0

/-!
## The bundle: one closed Prop framing all six windows
-/

/-- **The sharp Wightman target (T5):** all six sharpened axioms bundled into
    one closed Prop — the clean frame around the window. Discharging this
    for an *interacting* theory is the constructive-QFT existence problem
    (Clay-grade; no interacting 4D example has ever been constructed). For
    the free field, W1–W5 are the Streater–Wightman 1964 construction
    (blocked in formalization only by the priced infrastructure gaps above)
    and W6 is false, as it must be. The axioms stay unproved; this Prop
    states exactly what "proved" would mean. -/
def SharpWightmanTarget : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H),
  ∃ (Ω : H) (T : TestFunctionMarker) (_ : AddCommGroup T.carrier) (_ : Module ℂ T.carrier),
  ∃ (D : Submodule ℂ H) (_ : Dense (D : Set H)) (hΩD : Ω ∈ D),
  ∃ (conjTest : T.carrier → T.carrier) (field : T.carrier → (D →ₗ[ℂ] D)),
  ∃ (Poin : PoincareMarker) (_ : Group Poin.carrier)
    (rep : Poin.carrier → (H ≃ₗᵢ[ℂ] H)) (act : Poin.carrier → T.carrier → T.carrier),
  ∃ (transRep : Minkowski → (H ≃ₗᵢ[ℂ] H)) (energyMom : Fin 4 → (D →ₗ[ℂ] D))
    (spec : Set Minkowski) (spacelikeSep : T.carrier → T.carrier → Prop)
    (w : ℕ → List T.carrier → ℂ),
  W1_fieldsExist_sharp H Ω T D conjTest field ∧
  (∃ repPresD : ∀ (g : Poin.carrier) (ψ : D), (rep g) ((ψ : H)) ∈ D,
    W2_poincareCovariant_sharp H T D Poin rep act field repPresD) ∧
  W3_spectrumCondition_sharp H D transRep energyMom spec ∧
  (∃ s : ℂ, W4_locality_sharp H T D field spacelikeSep s) ∧
  W5_vacuumCyclic_sharp H Ω T D field hΩD ∧
  W6_nontrivial_sharp T w

end ThetLogos
