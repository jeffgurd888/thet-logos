/-
# WP2 character route, Module B, brick B1b2 — the finite
# irreducible character family

Second half of brick B1b (re-cut as B1b1 + B1b2, disclosed
in B1b1's header and in the lane STATUS).  B1b1 realized
each minimal constituent by a unitary matrix model; here
the characters of all irreducible unitary models are shown
to form a **finite** family `irredCharSet`: transported
through the matrix model (`unitaryRepOf`), Mathlib's
character orthonormality for finite groups
(`Representation.char_orthonormal`) becomes orthonormality
of the `charFn`s in the counting pairing
`∑ g, χ g * star (χ' g)` — `= Fintype.card G` on the
diagonal, `0` off it — and a family of functions pairwise
orthogonal with nonzero self-pairing is linearly
independent in the finite-dimensional space `G → ℂ`,
hence finite.

**Fences.**  FACT-freeness (scope §3, F1–F3): nothing here
routes through `StratumColumnFactorization`.  This brick
proves no positivity and closes nothing: `DeltaGramGap` is
proved at no seat, no β, no `d`; `LayerKernelPos` at general
finite `(G, ρ)`, β > 0, remains OPEN.

NO CLAIM; dials 0/4.  Dial 2 = 0 under every outcome of
this line: M-U3 is a positivity joint, not a gravity object.
-/

import ThetLogos.LayerKernelUnitaryModel
import Mathlib.RepresentationTheory.Character

open Finset
open scoped Matrix

namespace ThetLogos

section IrredFamily

variable {G : Type*} [Group G] [Fintype G]

/-- A unitary model, viewed as a Mathlib representation on
the coordinate space `Fin d → ℂ` (matrices acting by
`Matrix.toLin'`). -/
def unitaryRepOf {d : ℕ} (σ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) :
    Representation ℂ G (Fin d → ℂ) where
  toFun g := Matrix.toLin' (repMatrix σ g)
  map_one' := by
    show Matrix.toLin' ((σ 1).1) = 1
    rw [map_one]
    exact Matrix.toLin'_one
  map_mul' := by
    intro g h
    show Matrix.toLin' (repMatrix σ (g * h))
      = Matrix.toLin' (repMatrix σ g) * Matrix.toLin' (repMatrix σ h)
    rw [repMatrix_mul, Matrix.toLin'_mul, Module.End.mul_eq_comp]

/-- The Mathlib character of the transported model is the
corpus character. -/
theorem unitaryRepOf_character {d : ℕ}
    (σ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) :
    (unitaryRepOf σ).character = charFn σ := by
  funext g
  show LinearMap.trace ℂ _ (Matrix.toLin' (repMatrix σ g))
    = Matrix.trace (repMatrix σ g)
  exact Matrix.trace_toLin'_eq _

/-- The irreducibility bridge: owned irreducibility (no
nontrivial invariant submodule of the coordinate space) is
Mathlib irreducibility of the transported representation.
The hypothesis `0 < d` is essential: at `d = 0` the owned
notion holds vacuously on the zero space, while the
Mathlib notion requires a nontrivial subrepresentation
lattice. -/
theorem unitaryRepOf_isIrreducible {d : ℕ} (hd : 0 < d)
    {σ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)}
    (hσ : RepIrreducible σ) :
    Representation.IsIrreducible (unitaryRepOf σ) := by
  haveI : Nontrivial
      (Subrepresentation (unitaryRepOf σ)) := by
    refine ⟨⊥, ⊤, ?_⟩
    intro hcon
    have h2 := congrArg Subrepresentation.toSubmodule hcon
    have htop : Pi.single ⟨0, hd⟩ (1 : ℂ)
        ∈ (⊤ : Subrepresentation
          (unitaryRepOf σ)).toSubmodule := Submodule.mem_top
    rw [← h2] at htop
    have h4 : (Pi.single (⟨0, hd⟩ : Fin d) (1 : ℂ) : Fin d → ℂ)
        = 0 := htop
    have h5 := congrFun h4 ⟨0, hd⟩
    simp at h5
  refine IsSimpleOrder.of_forall_eq_top (fun W hW => ?_)
  have hcase := hσ W.toSubmodule (fun h v hv =>
    W.apply_mem_toSubmodule h hv)
  cases hcase with
  | inl hbot =>
    exact absurd (Subrepresentation.toSubmodule_injective hbot) hW
  | inr htop =>
    exact Subrepresentation.toSubmodule_injective htop

/-- The character at the inverse is the conjugate character
(for unitary models, inversion is conjugate transposition).
(The corpus's `charFn_inv` states this with `starRingEnd`
under a topological package; this is the finite counting
form with `star`.) -/
theorem charFn_inv_star {d : ℕ}
    (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) (g : G) :
    charFn ρ g⁻¹ = star (charFn ρ g) := by
  show Matrix.trace (repMatrix ρ g⁻¹)
    = star (Matrix.trace (repMatrix ρ g))
  show (∑ x, repMatrix ρ g⁻¹ x x)
    = star (∑ x, repMatrix ρ g x x)
  rw [star_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [GramWordTensor.repMatrix_inv_entry,
    GramWordTensor.repMatrix_conjRep, GramWordTensor.conjMat_apply]

open scoped Classical in
/-- **Counting-pairing orthonormality of irreducible
characters**, transported from
`Representation.char_orthonormal`: the pairing of two
irreducible `charFn`s is `1` (after the `(card G)⁻¹`
normalization) exactly when the transported models are
equivalent. -/
theorem charFn_pairing_eq {d e : ℕ}
    {σ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)}
    {τ : G →* ↥(Matrix.unitaryGroup (Fin e) ℂ)}
    (hσ : RepIrreducible σ) (hτ : RepIrreducible τ)
    (hd : 0 < d) (he : 0 < e) :
    (Nat.card G : ℂ)⁻¹ * ∑ g, charFn σ g * star (charFn τ g)
      = if Nonempty (Representation.Equiv (unitaryRepOf τ)
          (unitaryRepOf σ)) then 1 else 0 := by
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    have hpos : 0 < Nat.card G := Nat.card_pos
    exact_mod_cast hpos.ne'
  haveI : Invertible (Nat.card G : ℂ) :=
    { invOf := (Nat.card G : ℂ)⁻¹,
      invOf_mul_self := inv_mul_cancel₀ hcard,
      mul_invOf_self := mul_inv_cancel₀ hcard }
  haveI : Representation.IsIrreducible (unitaryRepOf σ) :=
    unitaryRepOf_isIrreducible hd hσ
  haveI : Representation.IsIrreducible (unitaryRepOf τ) :=
    unitaryRepOf_isIrreducible he hτ
  have h := Representation.char_orthonormal
    (unitaryRepOf σ) (unitaryRepOf τ)
  rw [unitaryRepOf_character, unitaryRepOf_character] at h
  have hsum : (∑ g, charFn σ g * charFn τ g⁻¹)
      = ∑ g, charFn σ g * star (charFn τ g) :=
    Finset.sum_congr rfl fun g _ => by rw [charFn_inv_star]
  rwa [hsum] at h

/-- Self-pairing of an irreducible character is `card G`. -/
theorem charFn_pairing_self {d : ℕ}
    {σ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)}
    (hσ : RepIrreducible σ) (hd : 0 < d) :
    ∑ g, charFn σ g * star (charFn σ g) = (Nat.card G : ℂ) := by
  have h := charFn_pairing_eq hσ hσ hd hd
  rw [if_pos ⟨Representation.Equiv.refl (unitaryRepOf σ)⟩] at h
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    have hpos : 0 < Nat.card G := Nat.card_pos
    exact_mod_cast hpos.ne'
  have h2 := congrArg (fun z : ℂ => (Nat.card G : ℂ) * z) h
  simp only [← mul_assoc, mul_inv_cancel₀ hcard, one_mul, mul_one] at h2
  exact h2

/-- Distinct irreducible characters are orthogonal in the
counting pairing. -/
theorem charFn_pairing_of_ne {d e : ℕ}
    {σ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)}
    {τ : G →* ↥(Matrix.unitaryGroup (Fin e) ℂ)}
    (hσ : RepIrreducible σ) (hτ : RepIrreducible τ)
    (hd : 0 < d) (he : 0 < e) (hne : charFn σ ≠ charFn τ) :
    ∑ g, charFn σ g * star (charFn τ g) = 0 := by
  have h := charFn_pairing_eq hσ hτ hd he
  have hne' : ¬ Nonempty (Representation.Equiv
      (unitaryRepOf τ) (unitaryRepOf σ)) := by
    rintro ⟨φ⟩
    apply hne
    have hχ := Representation.char_iso φ
    rw [unitaryRepOf_character, unitaryRepOf_character] at hχ
    exact hχ.symm
  rw [if_neg hne'] at h
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    have hpos : 0 < Nat.card G := Nat.card_pos
    exact_mod_cast hpos.ne'
  cases mul_eq_zero.mp h with
  | inl h1 => exact absurd (inv_eq_zero.mp h1) hcard
  | inr h2 => exact h2

/-- **The irreducible character family**: all `charFn σ`
for irreducible unitary models `σ`, of every dimension.
(The zero function belongs to it, as the character of the
zero-dimensional model, whose owned irreducibility is
vacuous; it is harmless in every consumer, contributing
`0` to any expansion.) -/
def irredCharSet : Set (G → ℂ) :=
  {χ | ∃ (d : ℕ) (σ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)),
    RepIrreducible σ ∧ charFn σ = χ}

/-- **The irreducible character family is finite**: its
nonzero members are pairwise orthogonal with self-pairing
`card G ≠ 0`, hence linearly independent in the
finite-dimensional space `G → ℂ`. -/
theorem irredCharSet_finite : (irredCharSet (G := G)).Finite := by
  classical
  -- the nonzero part is linearly independent
  have hli : LinearIndependent ℂ
      (fun χ : ↥(irredCharSet (G := G) \ {0}) => χ.1) := by
    rw [linearIndependent_iff']
    intro s c hc χ0 hχ0
    -- choose a model for each member of the finset
    have hwit : ∀ χ : ↥(irredCharSet (G := G) \ {0}),
        ∃ (d : ℕ) (σ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)),
          RepIrreducible σ ∧ charFn σ = χ.1 ∧ 0 < d := by
      intro χ
      obtain ⟨d, σ, hσ, hχσ⟩ := χ.2.1
      refine ⟨d, σ, hσ, hχσ, ?_⟩
      by_contra hd
      have hd0 : d = 0 := by omega
      subst hd0
      have h0 : charFn σ = 0 := by
        funext g
        show Matrix.trace (repMatrix σ g) = 0
        show (∑ x : Fin 0, repMatrix σ g x x) = 0
        simp
      have : χ.1 = 0 := by rw [← hχσ, h0]
      exact χ.2.2 (Set.mem_singleton_iff.mpr this)
    choose d σ hσ hχσ hd using hwit
    -- pair the vanishing combination with `χ0`'s character
    have hpair : ∀ χ : ↥(irredCharSet (G := G) \ {0}),
        (∑ g, χ.1 g * star (χ0.1 g))
          = if χ = χ0 then (Nat.card G : ℂ) else 0 := by
      intro χ
      by_cases hχ : χ = χ0
      · rw [if_pos hχ]
        subst hχ
        have := charFn_pairing_self (σ := σ χ) (hσ χ) (hd χ)
        rwa [hχσ] at this
      · rw [if_neg hχ]
        have hne : charFn (σ χ) ≠ charFn (σ χ0) := by
          rw [hχσ χ, hχσ χ0]
          exact fun hh => hχ (Subtype.ext hh)
        have := charFn_pairing_of_ne (hσ χ) (hσ χ0) (hd χ) (hd χ0) hne
        rwa [hχσ χ, hχσ χ0] at this
    -- apply the pairing functional to the combination
    have hL : (∑ g, (∑ χ ∈ s, c χ • χ.1) g * star (χ0.1 g))
        = ∑ χ ∈ s, c χ * (if χ = χ0 then (Nat.card G : ℂ) else 0) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun χ _ => ?_
      have hterm : (∑ g, (c χ * χ.1 g) * star (χ0.1 g))
          = c χ * ∑ g, χ.1 g * star (χ0.1 g) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun g _ => mul_assoc _ _ _
      rw [hterm, hpair χ]
    rw [hc] at hL
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hL
    rw [Finset.sum_eq_single χ0 (fun χ _ hχ => by
      rw [if_neg hχ, mul_zero]) (fun hχ0s => absurd hχ0 hχ0s)] at hL
    rw [if_pos rfl] at hL
    have hcard : (Nat.card G : ℂ) ≠ 0 := by
      have hpos : 0 < Nat.card G := Nat.card_pos
      exact_mod_cast hpos.ne'
    exact (mul_eq_zero.mp hL.symm).resolve_right hcard
  have hfin : Finite ↥(irredCharSet (G := G) \ {0}) := hli.finite
  have : (irredCharSet (G := G) \ {0}).Finite := Set.finite_coe_iff.mpr hfin
  have hunion : irredCharSet (G := G) ⊆ (irredCharSet (G := G) \ {0}) ∪ {0} := by
    intro χ hχ
    by_cases h0 : χ = 0
    · exact Or.inr (Set.mem_singleton_iff.mpr h0)
    · exact Or.inl ⟨hχ, h0⟩
  exact Set.Finite.subset
    (this.union (Set.finite_singleton 0)) hunion

end IrredFamily

end ThetLogos
