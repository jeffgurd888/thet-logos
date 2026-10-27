import ThetLogos.LatticeTwirl
import ThetLogos.PlaneCrossingBeta2
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-
# PW-1: entry orthogonality of the corpus representation

The `ρ ⊗ ρ̄` projector, evaluated. Brick PW-1 of the projector
scoping (`whitepaper` companion: `scoping-pw-projector-2026-10-27.md`
§2). The projector object itself is already owned — `haarTwirl` of
`LatticeTwirl` is the coefficient-product integral, proved there to be
the projection onto `pairInvariantSubmodule`. What was missing, and
what this module supplies, is the **evaluation**: an irreducibility
notion for the owned `ρ`, and the entry-level orthogonality relation

  `∫ g, repMatrix ρ g i j * star (repMatrix ρ g k l) ∂μG
      = if i = k ∧ j = l then (d : ℂ)⁻¹ else 0`,

together with the character-norm identity `∫ χ * star χ = 1`.
(Conjugation is spelled `star` throughout: on `ℂ` in this pin that is
the conjugation operation, and it is the spelling the owned
`orientConj` kit produces.)

HONESTY LEDGER — read this before citing anything from this file.

**(i) NO CLAIM; dials 0/4.** Parts of the official Clay Yang–Mills
statement closed by this module: **0**. This is finite-volume /
compact-group representation algebra: a general topological group
`G`, a normalized Haar probability `μG`, a unitary representation
`ρ : G →* unitaryGroup (Fin d) ℂ` with continuity carried as a
hypothesis. No limit is taken or asserted.

**(ii) Scope flag (pre-registered K-PW-1b).** Every orthogonality
statement here is proved for **irreducible** `ρ` only. The
reducible-`ρ` form (an isotypic decomposition of the twirl) is not
proved and not claimed. If a consumer — in particular the sign of
the β⁴ coefficient via the layer kernel — is ever stated at
reducible `ρ`, its statement must carry irreducibility of `ρ` as a
hypothesis; this module does not paper over that.

**(iii) Seat checks first (pre-registered K-PW-1).** Before the
general proof was attempted, the headline formula was checked by
exact arithmetic at the two probed seats, (S₃, std) and (C₃, faithful
χ), with normalized counting measure: at both seats irreducibility
holds and the integral equals `δ/d` on every index tuple, and the
character norm is exactly `1`. The general proof below is therefore
a proof of a formula already known to hold at the seats; had a seat
disagreed, this file would instead be a defect report on the twirl
kit.

**(iv) Method.** The evaluation does not go through the twirl's
range: it goes through the conjugation twirl `twirlEndo` (owned,
`LatticeTwirl` §6). The twirl of any endomorphism `X` commutes with
every `repMatrix ρ h`; by the hand-rolled Schur lemma of §1 such an
`X`-twirl is a scalar, and its trace — computed directly — fixes the
scalar as `(d : ℂ)⁻¹ * trace X`. The headline is the entry of that
identity at a matrix unit. The trace identity for the pair twirl
itself (`haarTwirl_trace`, owned) is recovered as a corollary via
the character norm.

This module is NOT in the root import list of the library (the
corpus pattern for recent exhibits); it is verified by a targeted
build.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix

section Setup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (μG : Measure G) [IsProbabilityMeasure μG] [Measure.IsMulLeftInvariant μG]
  [Measure.IsMulRightInvariant μG] [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-! ## §1. Irreducibility in owned vocabulary, and Schur's lemma -/

/-- **Irreducibility of the corpus representation**, in owned
vocabulary: no submodule of `Fin d → ℂ` other than `⊥` and `⊤` is
invariant under every `repMatrix ρ h` acting by matrix–vector
multiplication. (This is the owned-vocabulary counterpart of the
standard notion; no foreign representation vocabulary is used.) -/
def RepIrreducible : Prop :=
  ∀ W : Submodule ℂ (Fin d → ℂ),
    (∀ h : G, ∀ v ∈ W, repMatrix ρ h *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤

/-- The `lam`-eigenspace of a matrix, as a plain submodule of the
function space, in owned vocabulary: the vectors `v` with
`A *ᵥ v = lam • v`. -/
def matrixEigenspace (A : Matrix (Fin d) (Fin d) ℂ) (lam : ℂ) :
    Submodule ℂ (Fin d → ℂ) where
  carrier := {v | A *ᵥ v = lam • v}
  add_mem' := by
    intro x y hx hy
    show A *ᵥ (x + y) = lam • (x + y)
    rw [Matrix.mulVec_add, hx, hy, smul_add]
  zero_mem' := by
    show A *ᵥ (0 : Fin d → ℂ) = lam • (0 : Fin d → ℂ)
    rw [Matrix.mulVec_zero, smul_zero]
  smul_mem' := by
    intro c x hx
    show A *ᵥ (c • x) = lam • (c • x)
    rw [Matrix.mulVec_smul, hx, smul_comm]

theorem mem_matrixEigenspace (A : Matrix (Fin d) (Fin d) ℂ) (lam : ℂ)
    (v : Fin d → ℂ) :
    v ∈ matrixEigenspace A lam ↔ A *ᵥ v = lam • v := Iff.rfl

/-- **Schur's lemma, hand-rolled in owned vocabulary.** If `ρ` is
irreducible and `0 < d`, every matrix commuting with all
`repMatrix ρ h` is a scalar multiple of the identity. The eigenvalue
step is `Module.End.exists_eigenvalue` (in-pin, over the
algebraically closed field `ℂ`), transferred once into the owned
`matrixEigenspace`; an eigenspace of a commuting matrix is an
invariant submodule, and irreducibility forces a nonzero such
submodule to be everything. -/
theorem commutant_eq_smul_of_repIrreducible (hd : 0 < d) (hρirr : RepIrreducible ρ)
    (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ h : G, repMatrix ρ h * A = A * repMatrix ρ h) :
    ∃ c : ℂ, A = c • 1 := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue (Matrix.toLin' A)
  obtain ⟨v, hv, hv0⟩ : ∃ v ∈ matrixEigenspace A lam, v ≠ 0 := by
    have hne : Module.End.eigenspace (Matrix.toLin' A) lam ≠ ⊥ := hlam
    rw [Submodule.ne_bot_iff] at hne
    obtain ⟨w, hw, hw0⟩ := hne
    have hweq : A *ᵥ w = lam • w := by
      have h2 := (Module.End.mem_eigenspace_iff).1 hw
      rwa [Matrix.toLin'_apply] at h2
    exact ⟨w, hweq, hw0⟩
  have hSne : matrixEigenspace A lam ≠ ⊥ :=
    (Submodule.ne_bot_iff (matrixEigenspace A lam)).2 ⟨v, hv, hv0⟩
  have hSinv : ∀ h : G, ∀ w ∈ matrixEigenspace A lam,
      repMatrix ρ h *ᵥ w ∈ matrixEigenspace A lam := by
    intro h w hw
    have hw' : A *ᵥ w = lam • w := hw
    show A *ᵥ (repMatrix ρ h *ᵥ w) = lam • (repMatrix ρ h *ᵥ w)
    calc A *ᵥ (repMatrix ρ h *ᵥ w)
        = (A * repMatrix ρ h) *ᵥ w := Matrix.mulVec_mulVec w A (repMatrix ρ h)
      _ = (repMatrix ρ h * A) *ᵥ w := by rw [← hA h]
      _ = repMatrix ρ h *ᵥ (A *ᵥ w) := (Matrix.mulVec_mulVec w (repMatrix ρ h) A).symm
      _ = repMatrix ρ h *ᵥ (lam • w) := by rw [hw']
      _ = lam • (repMatrix ρ h *ᵥ w) := Matrix.mulVec_smul _ _ _
  rcases hρirr _ hSinv with h | h
  · exact absurd h hSne
  · refine ⟨lam, ?_⟩
    ext i j
    have hvec : A *ᵥ Pi.single j 1 = lam • Pi.single j 1 := by
      have hmem : Pi.single j (1 : ℂ) ∈ matrixEigenspace A lam := by
        rw [h]; exact Submodule.mem_top
      exact hmem
    have hentry := congrFun hvec i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at hentry
    rw [hentry]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]

/-- Every one-dimensional representation is irreducible: a submodule
of `Fin 1 → ℂ` is `⊥` or `⊤` for dimension reasons alone. This is the
irreducibility half of the (C₃, χ) seat inside owned vocabulary. -/
theorem repIrreducible_of_dim_eq_one (hd : d = 1) : RepIrreducible ρ := by
  subst hd
  intro W _hW
  by_cases h0 : W = ⊥
  · exact Or.inl h0
  · right
    obtain ⟨v, hv, hv0⟩ : ∃ v ∈ W, v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact h0 ((Submodule.eq_bot_iff W).2 fun x hx => hcon x hx)
    have hkey : ∀ x : Fin 1, x = 0 := fun x => Fin.eq_zero x
    have hv0' : v 0 ≠ 0 := by
      by_contra hc
      apply hv0
      funext x
      rw [hkey x, hc]
      rfl
    apply eq_top_iff.2
    intro w _
    have hw : w = (w 0 * (v 0)⁻¹) • v := by
      funext x
      rw [hkey x, Pi.smul_apply, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hv0', mul_one]
    rw [hw]
    exact W.smul_mem _ hv

/-! ## §2. The matrix unit -/

/-- The matrix unit: entry `1` at `(j, l)`, `0` elsewhere. -/
def matUnit (j l : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun c e => if c = j ∧ e = l then 1 else 0

theorem matUnit_apply (j l c e : Fin d) :
    matUnit j l c e = if c = j ∧ e = l then (1 : ℂ) else 0 := rfl

theorem matUnit_trace (j l : Fin d) :
    Matrix.trace (matUnit j l) = if j = l then (1 : ℂ) else 0 := by
  have hsum : Matrix.trace (matUnit j l)
      = ∑ a : Fin d, (if a = j ∧ a = l then (1 : ℂ) else 0) := by
    show (∑ a : Fin d, matUnit j l a a) = _
    exact Finset.sum_congr rfl fun a _ => matUnit_apply j l a a
  rw [hsum]
  by_cases h : j = l
  · subst h
    refine (Finset.sum_eq_single j ?_ ?_).trans ?_
    · intro a _ haj
      simp [haj]
    · simp
    · simp
  · refine (Finset.sum_eq_zero ?_).trans ?_
    · intro a _
      by_cases ha : a = j
      · subst ha; simp [h]
      · simp [ha]
    · simp [h]

/-! ## §3. The conjugation twirl: scalar evaluation

`twirlEndo μG (repMatrix ρ) X = ∫ g, repMatrix ρ g * X * star
(repMatrix ρ g)` is owned (`LatticeTwirl` §6). It is an intertwiner
of `ρ` with itself; by §1 it is a scalar when `ρ` is irreducible,
and the trace fixes the scalar. -/

/-- Entry expansion of the conjugation integrand:
`(repMatrix ρ g * X * star (repMatrix ρ g)) a b
  = ∑ c, ∑ e, repMatrix ρ g a c * X c e * star (repMatrix ρ g b e)`. -/
theorem twirlEndo_entry (X : Matrix (Fin d) (Fin d) ℂ) (g : G) (a b : Fin d) :
    (repMatrix ρ g * X * star (repMatrix ρ g)) a b
      = ∑ c, ∑ e, repMatrix ρ g a c * X c e * star (repMatrix ρ g b e) := by
  rw [Matrix.mul_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_apply, Matrix.star_apply, Finset.sum_mul]

/-- The entries of the conjugation integrand are integrable against
the probability measure `μG`. -/
theorem twirlEndo_entry_integrable (hρcont : Continuous fun g : G => repMatrix ρ g)
    (X : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    Integrable (fun g => (repMatrix ρ g * X * star (repMatrix ρ g)) a b) μG := by
  obtain ⟨hMmul, hMone, hMinv, hMcont⟩ := repMatrix_isOrientationMat ρ hρcont
  obtain ⟨hNmul, hNone, hNinv, hNcont⟩ := repMatConj_isOrientationMat ρ hρcont
  have hsum : Integrable (fun g => ∑ c, ∑ e,
      repMatrix ρ g a c * X c e * star (repMatrix ρ g b e)) μG := by
    refine MeasureTheory.integrable_finsetSum Finset.univ fun c _ =>
      MeasureTheory.integrable_finsetSum Finset.univ fun e _ => ?_
    have hInt : Integrable (fun g => repMatrix ρ g a c * repMatConj ρ g b e) μG :=
      matFn_integrable_entry_mul μG _ _ hMmul hMone hMinv hMcont
        hNmul hNone hNinv hNcont a c b e
    refine (hInt.mul_const (X c e)).congr (Filter.Eventually.of_forall fun g => ?_)
    show repMatrix ρ g a c * repMatConj ρ g b e * X c e
        = repMatrix ρ g a c * X c e * star (repMatrix ρ g b e)
    rw [show repMatConj ρ g b e = star (repMatrix ρ g b e) from orientConj_apply _ _ _ _]
    ring
  exact hsum.congr (Filter.Eventually.of_forall fun g => (twirlEndo_entry ρ X g a b).symm)

/-- **The conjugation twirl is an intertwiner**: it commutes with
every `repMatrix ρ h`. (Haar invariance, spent once on the left and
once through the unitary relation `star (repMatrix ρ h) * repMatrix
ρ h = 1`.) -/
theorem twirlEndo_repMatrix_comm (hρcont : Continuous fun g : G => repMatrix ρ g)
    (X : Matrix (Fin d) (Fin d) ℂ) (h : G) :
    repMatrix ρ h * twirlEndo μG (repMatrix ρ) X
      = twirlEndo μG (repMatrix ρ) X * repMatrix ρ h := by
  have hstar : star (repMatrix ρ h) * repMatrix ρ h = 1 :=
    (Matrix.mem_unitaryGroup_iff').1 (repMatrix_mem ρ h)
  have key : ∀ g : G, repMatrix ρ (h * g) * X * star (repMatrix ρ (h * g)) * repMatrix ρ h
      = repMatrix ρ (h * g) * X * star (repMatrix ρ g) := by
    intro g
    have hform : repMatrix ρ (h * g) * X * star (repMatrix ρ (h * g)) * repMatrix ρ h
        = (repMatrix ρ (h * g) * X * star (repMatrix ρ g))
            * (star (repMatrix ρ h) * repMatrix ρ h) := by
      rw [repMatrix_mul, star_mul]
      noncomm_ring
    rw [hform, hstar, mul_one]
  ext a b
  calc (repMatrix ρ h * twirlEndo μG (repMatrix ρ) X) a b
      = ∫ g, (repMatrix ρ (h * g) * X * star (repMatrix ρ g)) a b ∂μG := by
        rw [Matrix.mul_apply]
        calc ∑ c, repMatrix ρ h a c * twirlEndo μG (repMatrix ρ) X c b
            = ∑ c, ∫ g, repMatrix ρ h a c
                * (repMatrix ρ g * X * star (repMatrix ρ g)) c b ∂μG :=
              Finset.sum_congr rfl fun c _ => by
                rw [twirlEndo_apply, ← integral_const_mul]
          _ = ∫ g, ∑ c, repMatrix ρ h a c
                * (repMatrix ρ g * X * star (repMatrix ρ g)) c b ∂μG := by
              rw [integral_finsetSum]
              exact fun c _ => (twirlEndo_entry_integrable μG ρ hρcont X c b).const_mul _
          _ = ∫ g, (repMatrix ρ (h * g) * X * star (repMatrix ρ g)) a b ∂μG :=
              integral_congr_ae (Filter.Eventually.of_forall fun g => by
                show (∑ c, repMatrix ρ h a c
                    * (repMatrix ρ g * X * star (repMatrix ρ g)) c b)
                  = (repMatrix ρ (h * g) * X * star (repMatrix ρ g)) a b
                rw [← Matrix.mul_apply, ← mul_assoc, ← mul_assoc, ← repMatrix_mul])
    _ = ∫ g, (repMatrix ρ (h * g) * X * star (repMatrix ρ (h * g)) * repMatrix ρ h) a b
          ∂μG :=
        integral_congr_ae (Filter.Eventually.of_forall fun g => by
          show (repMatrix ρ (h * g) * X * star (repMatrix ρ g)) a b
              = (repMatrix ρ (h * g) * X * star (repMatrix ρ (h * g)) * repMatrix ρ h) a b
          rw [key g])
    _ = ∫ g, (repMatrix ρ g * X * star (repMatrix ρ g) * repMatrix ρ h) a b ∂μG :=
        integral_mul_left_eq_self
          (fun u => (repMatrix ρ u * X * star (repMatrix ρ u) * repMatrix ρ h) a b) h
    _ = (twirlEndo μG (repMatrix ρ) X * repMatrix ρ h) a b := by
        rw [Matrix.mul_apply]
        calc (∫ g, (repMatrix ρ g * X * star (repMatrix ρ g) * repMatrix ρ h) a b ∂μG)
            = ∫ g, ∑ c, (repMatrix ρ g * X * star (repMatrix ρ g)) a c
                * repMatrix ρ h c b ∂μG :=
              integral_congr_ae (Filter.Eventually.of_forall fun g => by
                show (repMatrix ρ g * X * star (repMatrix ρ g) * repMatrix ρ h) a b
                    = ∑ c, (repMatrix ρ g * X * star (repMatrix ρ g)) a c
                        * repMatrix ρ h c b
                rw [Matrix.mul_apply])
          _ = ∑ c, ∫ g, (repMatrix ρ g * X * star (repMatrix ρ g)) a c
                * repMatrix ρ h c b ∂μG := by
              rw [integral_finsetSum]
              exact fun c _ => (twirlEndo_entry_integrable μG ρ hρcont X a c).mul_const _
          _ = ∑ c, twirlEndo μG (repMatrix ρ) X a c * repMatrix ρ h c b :=
              Finset.sum_congr rfl fun c _ => by
                rw [twirlEndo_apply, ← integral_mul_const]

/-- **The conjugation twirl preserves trace**: by cyclicity of trace
and `star (repMatrix ρ g) * repMatrix ρ g = 1`, the integrand's trace
is constantly `trace X`, and `μG` is a probability measure. -/
theorem twirlEndo_repMatrix_trace (hρcont : Continuous fun g : G => repMatrix ρ g)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (twirlEndo μG (repMatrix ρ) X) = Matrix.trace X := by
  have hpt : ∀ g : G, Matrix.trace (repMatrix ρ g * X * star (repMatrix ρ g))
      = Matrix.trace X := by
    intro g
    have hstar : star (repMatrix ρ g) * repMatrix ρ g = 1 :=
      (Matrix.mem_unitaryGroup_iff').1 (repMatrix_mem ρ g)
    calc Matrix.trace (repMatrix ρ g * X * star (repMatrix ρ g))
        = Matrix.trace (star (repMatrix ρ g) * (repMatrix ρ g * X)) := by
          rw [Matrix.trace_mul_comm]
      _ = Matrix.trace X := by rw [← mul_assoc, hstar, one_mul]
  calc Matrix.trace (twirlEndo μG (repMatrix ρ) X)
      = ∑ a, ∫ g, (repMatrix ρ g * X * star (repMatrix ρ g)) a a ∂μG := by
        show (∑ a, twirlEndo μG (repMatrix ρ) X a a) = _
        exact Finset.sum_congr rfl fun a _ => twirlEndo_apply μG (repMatrix ρ) X a a
    _ = ∫ g, ∑ a, (repMatrix ρ g * X * star (repMatrix ρ g)) a a ∂μG := by
        rw [integral_finsetSum]
        exact fun a _ => twirlEndo_entry_integrable μG ρ hρcont X a a
    _ = ∫ _g : G, Matrix.trace X ∂μG :=
        integral_congr_ae (Filter.Eventually.of_forall fun g => by
          show Matrix.trace (repMatrix ρ g * X * star (repMatrix ρ g)) = Matrix.trace X
          exact hpt g)
    _ = Matrix.trace X := by simp

/-- **Evaluation of the conjugation twirl at irreducible `ρ`**: the
twirl of `X` is the scalar `(d : ℂ)⁻¹ * trace X` times the identity.
Schur (§1) supplies the scalar; the trace identity above fixes it. -/
theorem twirlEndo_repMatrix_eq (hd : 0 < d) (hρirr : RepIrreducible ρ)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (X : Matrix (Fin d) (Fin d) ℂ) :
    twirlEndo μG (repMatrix ρ) X = ((d : ℂ)⁻¹ * Matrix.trace X) • 1 := by
  obtain ⟨c, hc⟩ := commutant_eq_smul_of_repIrreducible ρ hd hρirr
    (twirlEndo μG (repMatrix ρ) X) (fun h => twirlEndo_repMatrix_comm μG ρ hρcont X h)
  have htr : Matrix.trace (twirlEndo μG (repMatrix ρ) X) = Matrix.trace X :=
    twirlEndo_repMatrix_trace μG ρ hρcont X
  rw [hc, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at htr
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hcval : c = (d : ℂ)⁻¹ * Matrix.trace X := by
    rw [← htr]
    field_simp
  rw [hcval] at hc
  exact hc

/-- Entry form of the conjugation twirl's evaluation. -/
theorem twirlEndo_repMatrix_apply (hd : 0 < d) (hρirr : RepIrreducible ρ)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (X : Matrix (Fin d) (Fin d) ℂ)
    (a b : Fin d) :
    twirlEndo μG (repMatrix ρ) X a b
      = (d : ℂ)⁻¹ * Matrix.trace X * (if a = b then (1 : ℂ) else 0) := by
  rw [twirlEndo_repMatrix_eq μG ρ hd hρirr hρcont X]
  by_cases hab : a = b <;> simp [hab, Matrix.smul_apply, smul_eq_mul]

/-- The conjugation integrand at a matrix unit collapses to a single
coefficient product — the entry-level bridge from the twirl to the
orthogonality integral. -/
theorem twirlEndo_matUnit_entry (g : G) (i j k l : Fin d) :
    (repMatrix ρ g * matUnit j l * star (repMatrix ρ g)) i k
      = repMatrix ρ g i j * star (repMatrix ρ g k l) := by
  rw [twirlEndo_entry]
  refine (Finset.sum_eq_single j ?_ ?_).trans ?_
  · intro c _ hcj
    refine Finset.sum_eq_zero fun e _ => ?_
    simp [matUnit_apply, hcj]
  · simp
  · refine (Finset.sum_eq_single l ?_ ?_).trans ?_
    · intro e _ hel
      simp [matUnit_apply, hel]
    · simp
    · simp [matUnit_apply]

/-! ## §4. The headline: entry orthogonality

The entry of §3's evaluation at the matrix unit `matUnit j l` is
the orthogonality relation. The case `d = 0` is vacuous (there are
no indices). -/

/-- **PW-1 headline — entry orthogonality of the corpus
representation.** For continuous irreducible `ρ` and normalized
Haar `μG`,
`∫ g, repMatrix ρ g i j * star (repMatrix ρ g k l) ∂μG
  = if i = k ∧ j = l then (d : ℂ)⁻¹ else 0`.
This is the evaluation of the owned `haarTwirl` projector at
`(repMatrix ρ, orientConj (repMatrix ρ))`; see
`haarTwirl_repMatrix_orientConj_apply` below. -/
theorem integral_repMatrix_mul_star_repMatrix
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hρirr : RepIrreducible ρ)
    (i j k l : Fin d) :
    ∫ g, repMatrix ρ g i j * star (repMatrix ρ g k l) ∂μG
      = if i = k ∧ j = l then (d : ℂ)⁻¹ else 0 := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    obtain ⟨i, hi⟩ := i
    exact absurd hi (Nat.not_lt_zero _)
  · have hE : twirlEndo μG (repMatrix ρ) (matUnit j l) i k
        = (((d : ℂ)⁻¹ * Matrix.trace (matUnit j l)) • (1 : Matrix (Fin d) (Fin d) ℂ)) i k := by
      rw [twirlEndo_repMatrix_eq μG ρ hd hρirr hρcont (matUnit j l)]
    rw [matUnit_trace] at hE
    have hint : twirlEndo μG (repMatrix ρ) (matUnit j l) i k
        = ∫ g, repMatrix ρ g i j * star (repMatrix ρ g k l) ∂μG := by
      rw [twirlEndo_apply]
      exact integral_congr_ae (Filter.Eventually.of_forall fun g =>
        twirlEndo_matUnit_entry ρ g i j k l)
    rw [hint] at hE
    rw [hE]
    by_cases h1 : i = k <;> by_cases h2 : j = l <;>
      simp [h1, h2, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]

/-- The conjugate-swapped form of entry orthogonality:
`∫ g, star (repMatrix ρ g i j) * repMatrix ρ g k l ∂μG
  = if i = k ∧ j = l then (d : ℂ)⁻¹ else 0`.
(Not a formal conjugate of the headline — conjugation produces
`repMatrix ρ g j i * star (repMatrix ρ g l k)` instead. The swap is
the inversion substitution `g ↦ g⁻¹`, spent through
`repMatrix_inv`.) -/
theorem integral_star_repMatrix_mul_repMatrix
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hρirr : RepIrreducible ρ)
    (i j k l : Fin d) :
    ∫ g, star (repMatrix ρ g i j) * repMatrix ρ g k l ∂μG
      = if i = k ∧ j = l then (d : ℂ)⁻¹ else 0 := by
  have hsub : (∫ g, star (repMatrix ρ g i j) * repMatrix ρ g k l ∂μG)
      = ∫ g, star (repMatrix ρ g⁻¹ i j) * repMatrix ρ g⁻¹ k l ∂μG :=
    (integral_inv_eq_self (fun u => star (repMatrix ρ u i j) * repMatrix ρ u k l) μG).symm
  have hpt : ∀ g : G, star (repMatrix ρ g⁻¹ i j) * repMatrix ρ g⁻¹ k l
      = repMatrix ρ g j i * star (repMatrix ρ g l k) := by
    intro g
    rw [repMatrix_inv, Matrix.star_apply, Matrix.star_apply, star_star]
  calc ∫ g, star (repMatrix ρ g i j) * repMatrix ρ g k l ∂μG
      = ∫ g, star (repMatrix ρ g⁻¹ i j) * repMatrix ρ g⁻¹ k l ∂μG := hsub
    _ = ∫ g, repMatrix ρ g j i * star (repMatrix ρ g l k) ∂μG :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = if j = l ∧ i = k then (d : ℂ)⁻¹ else 0 :=
        integral_repMatrix_mul_star_repMatrix μG ρ hρcont hρirr j i l k
    _ = if i = k ∧ j = l then (d : ℂ)⁻¹ else 0 := by
        by_cases h1 : i = k ∧ j = l
        · have h2 : j = l ∧ i = k := ⟨h1.2, h1.1⟩
          rw [if_pos h2, if_pos h1]
        · have h2 : ¬ (j = l ∧ i = k) := fun hh => h1 ⟨hh.2, hh.1⟩
          rw [if_neg h2, if_neg h1]

/-- **Character norm at irreducible `ρ`**: `∫ g, charFn ρ g * star
(charFn ρ g) ∂μG = 1`. Proved by expanding the character as a trace
and applying the headline entry-by-entry. (The hypothesis `0 < d`
is essential: at `d = 0` the character vanishes identically.) -/
theorem integral_charFn_mul_star_charFn (hd : 0 < d)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hρirr : RepIrreducible ρ) :
    ∫ g, charFn ρ g * star (charFn ρ g) ∂μG = 1 := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  obtain ⟨hMmul, hMone, hMinv, hMcont⟩ := repMatrix_isOrientationMat ρ hρcont
  obtain ⟨hNmul, hNone, hNinv, hNcont⟩ := repMatConj_isOrientationMat ρ hρcont
  have hInt : ∀ i k : Fin d,
      Integrable (fun g => repMatrix ρ g i i * star (repMatrix ρ g k k)) μG := by
    intro i k
    have hh := matFn_integrable_entry_mul μG _ _ hMmul hMone hMinv hMcont
      hNmul hNone hNinv hNcont i i k k
    refine hh.congr (Filter.Eventually.of_forall fun g => ?_)
    show repMatrix ρ g i i * repMatConj ρ g k k
        = repMatrix ρ g i i * star (repMatrix ρ g k k)
    rw [show repMatConj ρ g k k = star (repMatrix ρ g k k) from orientConj_apply _ _ _ _]
  have hprod : ∀ g : G, charFn ρ g * star (charFn ρ g)
      = ∑ i, ∑ k, repMatrix ρ g i i * star (repMatrix ρ g k k) := by
    intro g
    show Matrix.trace (repMatrix ρ g) * star (Matrix.trace (repMatrix ρ g)) = _
    rw [show Matrix.trace (repMatrix ρ g) = ∑ i, repMatrix ρ g i i from rfl,
      star_sum, Finset.sum_mul_sum]
  calc ∫ g, charFn ρ g * star (charFn ρ g) ∂μG
      = ∫ g, ∑ i, ∑ k, repMatrix ρ g i i * star (repMatrix ρ g k k) ∂μG :=
        integral_congr_ae (Filter.Eventually.of_forall hprod)
    _ = ∑ i, ∑ k, ∫ g, repMatrix ρ g i i * star (repMatrix ρ g k k) ∂μG := by
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_finsetSum]
          exact fun k _ => hInt i k
        · intro i _
          exact MeasureTheory.integrable_finsetSum _ fun k _ => hInt i k
    _ = ∑ i, ∑ k, (if i = k ∧ i = k then (d : ℂ)⁻¹ else 0) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
          integral_repMatrix_mul_star_repMatrix μG ρ hρcont hρirr i i k k
    _ = ∑ _i : Fin d, (d : ℂ)⁻¹ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine (Finset.sum_eq_single i ?_ ?_).trans ?_
        · intro k _ hk
          have hne : ¬ (i = k) := fun hh => hk hh.symm
          simp [hne]
        · simp
        · simp
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_inv_cancel₀ hd0]

/-- **The owned twirl, evaluated**: the entries of the pair twirl at
`(repMatrix ρ, orientConj (repMatrix ρ))` are
`haarTwirl μG (repMatrix ρ) (orientConj (repMatrix ρ)) (a, b) (c, e)
  = if a = b ∧ c = e then (d : ℂ)⁻¹ else 0` —
the projector onto the scalar line, in coordinates. -/
theorem haarTwirl_repMatrix_orientConj_apply
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hρirr : RepIrreducible ρ)
    (a b c e : Fin d) :
    haarTwirl μG (repMatrix ρ) (orientConj (repMatrix ρ)) (a, b) (c, e)
      = if a = b ∧ c = e then (d : ℂ)⁻¹ else 0 := by
  rw [haarTwirl_apply]
  have hcongr : (∫ g, repMatrix ρ g a c * orientConj (repMatrix ρ) g b e ∂μG)
      = ∫ g, repMatrix ρ g a c * star (repMatrix ρ g b e) ∂μG :=
    integral_congr_ae (Filter.Eventually.of_forall fun g => by
      show repMatrix ρ g a c * orientConj (repMatrix ρ) g b e
          = repMatrix ρ g a c * star (repMatrix ρ g b e)
      rw [orientConj_apply])
  rw [hcongr]
  exact integral_repMatrix_mul_star_repMatrix μG ρ hρcont hρirr a c b e

/-- The trace of the evaluated twirl is `1` — recovered from the
owned `haarTwirl_trace` identity and the character norm, closing
the loop with the route the scoping memo priced. -/
theorem haarTwirl_repMatrix_orientConj_trace (hd : 0 < d)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hρirr : RepIrreducible ρ) :
    Matrix.trace (haarTwirl μG (repMatrix ρ) (orientConj (repMatrix ρ))) = 1 := by
  obtain ⟨hMmul, hMone, hMinv, hMcont⟩ := repMatrix_isOrientationMat ρ hρcont
  obtain ⟨hNmul, hNone, hNinv, hNcont⟩ := repMatConj_isOrientationMat ρ hρcont
  have h1 : ∀ g : G, Matrix.trace (repMatConj ρ g)
      = star (Matrix.trace (repMatrix ρ g)) := by
    intro g
    show Matrix.trace (orientConj (repMatrix ρ) g)
        = star (Matrix.trace (repMatrix ρ g))
    show (∑ a, orientConj (repMatrix ρ) g a a) = star (∑ a, repMatrix ρ g a a)
    rw [star_sum]
    exact Finset.sum_congr rfl fun a _ => orientConj_apply _ _ _ _
  have htr : ∀ g : G, Matrix.trace (repMatrix ρ g) * Matrix.trace (repMatConj ρ g)
      = charFn ρ g * star (charFn ρ g) := by
    intro g
    show Matrix.trace (repMatrix ρ g) * Matrix.trace (repMatConj ρ g)
        = Matrix.trace (repMatrix ρ g) * star (Matrix.trace (repMatrix ρ g))
    rw [h1 g]
  calc Matrix.trace (haarTwirl μG (repMatrix ρ) (orientConj (repMatrix ρ)))
      = ∫ g, Matrix.trace (repMatrix ρ g) * Matrix.trace (repMatConj ρ g) ∂μG :=
        haarTwirl_trace μG _ _ hMmul hMone hMinv hMcont hNmul hNone hNinv hNcont
    _ = ∫ g, charFn ρ g * star (charFn ρ g) ∂μG :=
        integral_congr_ae (Filter.Eventually.of_forall htr)
    _ = 1 := integral_charFn_mul_star_charFn μG ρ hd hρcont hρirr

/-! ## §5. The invariant submodule is the scalar line

The projector-side form of the same evaluation: for irreducible
`ρ`, the invariant submodule of the pair action
`ρ ⊗ ρ̄` is exactly the span of the diagonal vector `δ`. -/

/-- The diagonal vector `δ(a, b) = if a = b then 1 else 0` on the
pair index — the vector form of the identity matrix. -/
def deltaVec : (Fin d × Fin d) → ℂ := fun p => if p.1 = p.2 then 1 else 0

theorem deltaVec_apply (p : Fin d × Fin d) :
    deltaVec p = if p.1 = p.2 then (1 : ℂ) else 0 := rfl

/-- The diagonal vector is invariant under the pair action: summing
the pair action against `δ` collapses to
`repMatrix ρ h * star (repMatrix ρ h) = 1`. -/
theorem deltaVec_mem_pairInvariantSubmodule :
    deltaVec ∈ pairInvariantSubmodule (repMatrix ρ) (orientConj (repMatrix ρ)) := by
  rw [mem_pairInvariantSubmodule]
  intro h
  funext ⟨a, b⟩
  have hstar : repMatrix ρ h * star (repMatrix ρ h) = 1 :=
    (Matrix.mem_unitaryGroup_iff).1 (repMatrix_mem ρ h)
  calc (pairMat (repMatrix ρ h) (orientConj (repMatrix ρ) h) *ᵥ deltaVec) (a, b)
      = ∑ c, repMatrix ρ h a c * star (repMatrix ρ h b c) := by
        rw [pairMat_mulVec_apply, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun c _ => ?_
        refine (Finset.sum_eq_single c ?_ ?_).trans ?_
        · intro e _ hec
          have hne : ¬ (c = e) := fun hh => hec hh.symm
          simp [orientConj_apply, deltaVec_apply, hne]
        · simp
        · simp [orientConj_apply, deltaVec_apply]
    _ = (repMatrix ρ h * star (repMatrix ρ h)) a b := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun c _ => by rw [Matrix.star_apply]
    _ = deltaVec (a, b) := by
        rw [hstar]
        simp [deltaVec_apply, Matrix.one_apply]

/-- The bridge from pair-invariance to commutation: if `w` is
invariant under the pair action, the matrix it spells out commutes
with every `repMatrix ρ h`. -/
theorem commutes_of_mem_pairInvariantSubmodule {w : (Fin d × Fin d) → ℂ}
    (hw : w ∈ pairInvariantSubmodule (repMatrix ρ) (orientConj (repMatrix ρ))) (h : G) :
    repMatrix ρ h * Matrix.of (fun a b => w (a, b))
      = Matrix.of (fun a b => w (a, b)) * repMatrix ρ h := by
  have hstar : star (repMatrix ρ h) * repMatrix ρ h = 1 :=
    (Matrix.mem_unitaryGroup_iff').1 (repMatrix_mem ρ h)
  have hinv : repMatrix ρ h * Matrix.of (fun a b => w (a, b)) * star (repMatrix ρ h)
      = Matrix.of (fun a b => w (a, b)) := by
    ext a b
    have hentry := congrFun ((mem_pairInvariantSubmodule _ _ _).1 hw h) (a, b)
    rw [pairMat_mulVec_apply, Fintype.sum_prod_type] at hentry
    simp only [orientConj_apply] at hentry
    show (repMatrix ρ h * Matrix.of (fun a b => w (a, b)) * star (repMatrix ρ h)) a b
        = w (a, b)
    rw [twirlEndo_entry]
    refine (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_).trans hentry
    show repMatrix ρ h a c * Matrix.of (fun a b => w (a, b)) c e
          * star (repMatrix ρ h b e)
        = repMatrix ρ h a c * star (repMatrix ρ h b e) * w (c, e)
    rw [Matrix.of_apply]
    ring
  have hcalc : (repMatrix ρ h * Matrix.of (fun a b => w (a, b)) * star (repMatrix ρ h))
        * repMatrix ρ h
      = repMatrix ρ h * Matrix.of (fun a b => w (a, b)) := by
    have hform : (repMatrix ρ h * Matrix.of (fun a b => w (a, b)) * star (repMatrix ρ h))
          * repMatrix ρ h
        = (repMatrix ρ h * Matrix.of (fun a b => w (a, b)))
            * (star (repMatrix ρ h) * repMatrix ρ h) := by
      noncomm_ring
    rw [hform, hstar, mul_one]
  rw [hinv] at hcalc
  exact hcalc.symm

/-- **The invariant submodule of `ρ ⊗ ρ̄` is the scalar line**: for
irreducible `ρ`, `pairInvariantSubmodule (repMatrix ρ) (orientConj
(repMatrix ρ))` is exactly the span of `δ`. (At `d = 0` both sides
are `⊥`, since every vector vanishes.) -/
theorem pairInvariantSubmodule_repMatrix_orientConj_eq_span_deltaVec
    (hρirr : RepIrreducible ρ) :
    pairInvariantSubmodule (repMatrix ρ) (orientConj (repMatrix ρ))
      = Submodule.span ℂ {deltaVec} := by
  apply le_antisymm
  · intro w hw
    by_cases hd : d = 0
    · subst hd
      have hw0 : w = 0 := by
        funext ⟨a, b⟩
        obtain ⟨a, ha⟩ := a
        exact absurd ha (Nat.not_lt_zero _)
      rw [hw0]
      exact Submodule.zero_mem _
    · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
      obtain ⟨c, hc⟩ := commutant_eq_smul_of_repIrreducible ρ hdpos hρirr
        (Matrix.of fun a b => w (a, b)) (commutes_of_mem_pairInvariantSubmodule ρ hw)
      rw [Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      funext ⟨a, b⟩
      show (c • deltaVec) (a, b) = w (a, b)
      have h1 : w (a, b) = Matrix.of (fun a b => w (a, b)) a b := rfl
      rw [h1, hc]
      by_cases hab : a = b <;>
        simp [hab, deltaVec_apply, Matrix.smul_apply, Matrix.one_apply, Pi.smul_apply,
          smul_eq_mul]
  · exact Submodule.span_le.2 (Set.singleton_subset_iff.2
      (deltaVec_mem_pairInvariantSubmodule ρ))

/-- The evaluated twirl fixes `δ` — as it must, since `δ` spans its
range at irreducible `ρ`. -/
theorem haarTwirl_repMatrix_orientConj_mulVec_deltaVec
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    haarTwirl μG (repMatrix ρ) (orientConj (repMatrix ρ)) *ᵥ deltaVec = deltaVec := by
  obtain ⟨hMmul, hMone, hMinv, hMcont⟩ := repMatrix_isOrientationMat ρ hρcont
  obtain ⟨hNmul, hNone, hNinv, hNcont⟩ := repMatConj_isOrientationMat ρ hρcont
  exact haarTwirl_mulVec_of_mem μG _ _ hMmul hMone hMinv hMcont hNmul hNone hNinv hNcont
    (deltaVec_mem_pairInvariantSubmodule ρ)

/-! ## §6. Vanishing means at irreducible `ρ` of dimension `≥ 2`

An irreducible representation of dimension `≥ 2` has no nonzero
fixed vector (a fixed vector would span an invariant line, forcing
dimension `1`), so its one-factor twirl — the matrix of entry
means — vanishes, and in particular the character has mean zero.
(For `d = 1` this is false in general: the trivial character has
mean `1`. The mean `e1` of the corpus's moment vocabulary is the
real part of this integral.) -/

/-- The fixed submodule of an irreducible `ρ` with `2 ≤ d` is `⊥`. -/
theorem fixedSubmodule_repMatrix_eq_bot (hρirr : RepIrreducible ρ) (hd : 2 ≤ d) :
    fixedSubmodule (repMatrix ρ) = ⊥ := by
  by_contra hne
  obtain ⟨v, hv, hv0⟩ : ∃ v ∈ fixedSubmodule (repMatrix ρ), v ≠ 0 :=
    (Submodule.ne_bot_iff _).1 hne
  have hspaninv : ∀ h : G, ∀ w ∈ Submodule.span ℂ {v},
      repMatrix ρ h *ᵥ w ∈ Submodule.span ℂ {v} := by
    intro h w hw
    rw [Submodule.mem_span_singleton] at hw ⊢
    obtain ⟨c, rfl⟩ := hw
    refine ⟨c, ?_⟩
    rw [Matrix.mulVec_smul]
    congr 1
    exact ((mem_fixedSubmodule _ _).1 hv h).symm
  rcases hρirr (Submodule.span ℂ {v}) hspaninv with h1 | h1
  · have hvspan : v ∈ Submodule.span ℂ {v} := Submodule.mem_span_singleton_self v
    rw [h1] at hvspan
    exact hv0 (by simpa using hvspan)
  · have hfr1 : Module.finrank ℂ (Submodule.span ℂ {v}) = 1 := finrank_span_singleton hv0
    have hfr2 : Module.finrank ℂ (Submodule.span ℂ {v}) = Module.finrank ℂ (Fin d → ℂ) :=
      (LinearEquiv.ofTop _ h1).finrank_eq
    rw [Module.finrank_pi, Fintype.card_fin] at hfr2
    omega

/-- The one-factor twirl of an irreducible `ρ` with `2 ≤ d`
vanishes: every matrix coefficient has mean zero. -/
theorem haarTwirl1_repMatrix_eq_zero (hρirr : RepIrreducible ρ) (hd : 2 ≤ d)
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    haarTwirl1 μG (repMatrix ρ) = 0 := by
  obtain ⟨hMmul, hMone, hMinv, hMcont⟩ := repMatrix_isOrientationMat ρ hρcont
  ext a c
  have hmem : haarTwirl1 μG (repMatrix ρ) *ᵥ Pi.single c 1
      ∈ fixedSubmodule (repMatrix ρ) :=
    haarTwirl1_mulVec_mem μG _ hMmul hMone hMinv hMcont _
  have h0 : haarTwirl1 μG (repMatrix ρ) *ᵥ Pi.single c 1 = 0 := by
    rw [fixedSubmodule_repMatrix_eq_bot ρ hρirr hd] at hmem
    simpa using hmem
  have h1 := congrFun h0 a
  rwa [Matrix.mulVec_single_one] at h1

/-- Entry form of the vanishing one-factor twirl. -/
theorem integral_repMatrix_entry_eq_zero (hρirr : RepIrreducible ρ) (hd : 2 ≤ d)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (i j : Fin d) :
    ∫ g, repMatrix ρ g i j ∂μG = 0 := by
  have h0 : haarTwirl1 μG (repMatrix ρ) i j = 0 := by
    rw [haarTwirl1_repMatrix_eq_zero μG ρ hρirr hd hρcont]
    rfl
  rwa [haarTwirl1_apply] at h0

/-- The character of an irreducible `ρ` with `2 ≤ d` has mean
zero. -/
theorem integral_charFn_eq_zero (hρirr : RepIrreducible ρ) (hd : 2 ≤ d)
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    ∫ g, charFn ρ g ∂μG = 0 := by
  obtain ⟨hMmul, hMone, hMinv, hMcont⟩ := repMatrix_isOrientationMat ρ hρcont
  calc ∫ g, charFn ρ g ∂μG
      = ∫ g, ∑ i, repMatrix ρ g i i ∂μG :=
        integral_congr_ae (Filter.Eventually.of_forall fun g => by
          show Matrix.trace (repMatrix ρ g) = ∑ i, repMatrix ρ g i i
          rfl)
    _ = ∑ i, ∫ g, repMatrix ρ g i i ∂μG := by
        rw [integral_finsetSum]
        exact fun i _ => matFn_integrable_entry μG _ hMmul hMone hMinv hMcont i i
    _ = ∑ i, haarTwirl1 μG (repMatrix ρ) i i :=
        Finset.sum_congr rfl fun i _ => (haarTwirl1_apply μG (repMatrix ρ) i i).symm
    _ = 0 := by
        rw [haarTwirl1_repMatrix_eq_zero μG ρ hρirr hd hρcont]
        simp

end Setup

end ThetLogos
