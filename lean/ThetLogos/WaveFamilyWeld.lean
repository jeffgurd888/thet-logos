import Mathlib.Tactic
import ThetLogos.WaveFamilyPost
import ThetLogos.MaxwellQuadAssembly

namespace ThetLogos

open scoped InnerProductSpace
open Finset

/-!
# ThetLogos.WaveFamilyWeld - GR-PROP-1: the wave weld

**Working label only.** The module name `WaveFamilyWeld`
and the line name GR-PROP are working labels; Jeff names.

**Status: GR-PROP-1 landing brick. NO CLAIM. Dial 2 = 0
under every outcome of this line, including total
success. No gravity object is defined, constructed, or
asserted to exist.**

Governing texts: the GR-PROP-0 pin `WaveFamilyPost.lean`
(its registered names govern: `waveFamily` by citation of
`SchrodingerDynamics.evolOp`, `ModeFreq`, `FreqShift`,
`onePlaqDefectOp`, `PoseObjBFreqShadow`), MAX-2
`MaxwellQuadAssembly.lean` (`maxwellM1_proved` - the form
identity + positivity for `maxwellOp N`, consumed below),
and the scoping memo
`routeb-general-scratch/scoping-gravity-vocabulary-2026-10-31.md`
sections 5-6.

## What is built here, in the memo's registered form

1. **Complexification.** `maxwellOp N` is a real operator
   on the real link space `linkAngle N`; `evolOp` is
   complex. `maxwellOpC N` below is its complexification
   on the complexified link space `LayerLink N -> ℂ`,
   built by the same plaquette formula with the real
   coefficients cast to `ℂ` (`maxwellOpC_ofReal` proves it
   extends the real operator exactly). Its transport
   `maxwellOpCE N` to `EuclideanSpace ℂ (LayerLink N)` is
   symmetric (`maxwellOpCE_isSymmetric`), proved by the
   polarized plaquette identity - the complex form of
   MAX-2's polarization output (`sum_mul_plaqSign`,
   `maxwellOp_form`, `maxwellOp_form_symm` in
   `MaxwellQuadAssembly`), with the real quadratic-form
   identity consumed directly from `maxwellM1_proved`
   (`maxwellOpC_quad_ofReal`).
2. **The family on link space.** `linkWaveFamily N` is
   the pin's `waveFamily` instantiated at the
   complexified link space, with group law and isometry
   BY CITATION of the landed `evolOp_add` /
   `evolOp_isometry` through the pin's own read-backs
   `waveFamily_add` / `waveFamily_isometry`. No new
   evolution theory is built.
3. **Eigenspace preservation.** The family preserves
   each eigenspace of the complexified operator, and
   preserves the pin's `ModeFreq` registration of a mode
   (modes stay modes, at the same frequency), by citation
   of `evolOp_map_eigenspace_le` /
   `evolOp_apply_mem_eigenspace` /
   `evolOp_apply_commute`. The modes here are ABSTRACT:
   the Fourier identification of the modes is GR-PROP-2's,
   gated on MAX-3, and is NOT built or asserted here.

## Fences (binding, from the pin and the memo)

- This brick asserts NO instance of the pin's
  `PoseObjBFreqShadow` predicate, for any mode,
  plaquette, seat, or stated shift. It builds the family
  that predicate's decision (GR-PROP-3) will consume.
- Frequencies and shifts are named/supplied, never
  existentially smuggled (K-GR-VAC).
- The deliverable is evolution vocabulary over a finite
  operator - bookkeeping about the instrument. No
  propagation-in-spacetime, bending, redshift, or gravity
  sentence may be drawn from it (K-GR-SMUG / K-GR-LAUNDER).
  The modular flow stays excluded by name (G2, on the
  pin's face): nothing here cites it.
- Ceiling on the face: Dial 2 unmoved by anything in
  this brick; NO CLAIM.
-/

section Complexification

variable {N : ℕ} [NeZero N]

/-- **Complex plaquette angle.** The complex form of the
pin's `plaqAngle`: for `P : PlaqDatum N` and a complex
link potential `ψ`,
`ψ (plaqEdgeB P) + ψ (plaqEdgeR P) - ψ (plaqEdgeT P)
  - ψ (plaqEdgeL P)`, in the corpus's (B, R, T, L) edge
order. -/
def plaqAngleC (P : PlaqDatum N) (ψ : LayerLink N → ℂ) :
    ℂ :=
  ψ (plaqEdgeB P) + ψ (plaqEdgeR P)
    - ψ (plaqEdgeT P) - ψ (plaqEdgeL P)

/-- **Read-back.** The complex plaquette angle unfolds
exactly as registered. -/
theorem plaqAngleC_apply (P : PlaqDatum N)
    (ψ : LayerLink N → ℂ) :
    plaqAngleC P ψ
      = ψ (plaqEdgeB P) + ψ (plaqEdgeR P)
        - ψ (plaqEdgeT P) - ψ (plaqEdgeL P) :=
  rfl

/-- **The complex plaquette sign pattern**: the pin's
real `plaqSign P ℓ` read in `ℂ` - `+1` on the (B, R)
edges, `-1` on the (T, L) edges, `0` elsewhere. Defined
AS the cast of the real sign pattern, so the
complexification spends the real operator's own
coefficients, no others, by construction. -/
noncomputable def plaqSignC (P : PlaqDatum N)
    (ℓ : LayerLink N) : ℂ :=
  (plaqSign P ℓ : ℂ)

/-- **The complex sign pattern is the real one, cast.**
`plaqSignC P ℓ = (plaqSign P ℓ : ℂ)` - by definition. -/
theorem plaqSignC_eq_cast (P : PlaqDatum N)
    (ℓ : LayerLink N) :
    plaqSignC P ℓ = (plaqSign P ℓ : ℂ) :=
  rfl

open Classical in
/-- A real indicator, cast to `ℂ`, is the complex
indicator. -/
theorem ofReal_indicator (ℓ e : LayerLink N) :
    ((if ℓ = e then (1 : ℝ) else 0 : ℝ) : ℂ)
      = (if ℓ = e then (1 : ℂ) else 0) := by
  split_ifs <;> simp

open Classical in
/-- **Expansion of the complex sign pattern** into
complex indicators: `+1` on the (B, R) edges, `-1` on
the (T, L) edges, `0` elsewhere - the cast of the pin's
`plaqSign` expansion. -/
theorem plaqSignC_expand (P : PlaqDatum N)
    (ℓ : LayerLink N) :
    plaqSignC P ℓ
      = (if ℓ = plaqEdgeB P then (1 : ℂ) else 0)
        + (if ℓ = plaqEdgeR P then (1 : ℂ) else 0)
        - (if ℓ = plaqEdgeT P then (1 : ℂ) else 0)
        - (if ℓ = plaqEdgeL P then (1 : ℂ) else 0) := by
  simp only [plaqSignC, plaqSign, Complex.ofReal_add,
    Complex.ofReal_sub, ofReal_indicator]

/-- **Conjugation fixes the sign pattern** (it is a real
coefficient read in `ℂ`). -/
theorem conj_plaqSignC (P : PlaqDatum N)
    (ℓ : LayerLink N) :
    (starRingEnd ℂ) (plaqSignC P ℓ) = plaqSignC P ℓ := by
  simp only [plaqSignC, Complex.conj_ofReal]

/-- **The complex plaquette angle of a real angle is the
real plaquette angle, cast** - the angle-level statement
that the complexification extends the real seat. -/
theorem plaqAngleC_ofReal (P : PlaqDatum N)
    (θ : linkAngle N) :
    plaqAngleC P (fun ℓ => (θ ℓ : ℂ))
      = (plaqAngle P θ : ℂ) := by
  simp only [plaqAngleC, plaqAngle, Complex.ofReal_add,
    Complex.ofReal_sub]

open Classical in
/-- The link sum of a complex potential against one
indicator: `sum l, ψ l * (if l = e then 1 else 0) = ψ e`
(the complex form of MAX-2's `sum_mul_indicator`). -/
theorem sum_mul_indicatorC (ψ : LayerLink N → ℂ)
    (e : LayerLink N) :
    (∑ ℓ, ψ ℓ * (if ℓ = e then (1 : ℂ) else 0)) = ψ e := by
  rw [Finset.sum_eq_single e]
  · simp
  · intro ℓ _ hℓ
    simp [hℓ]
  · simp

open Classical in
/-- **Polarization identity at one plaquette, complex
form** (the complex form of MAX-2's `sum_mul_plaqSign`):
the link sum of `ψ` against the plaquette sign pattern
is the complex plaquette angle itself,
`sum l, ψ l * plaqSignC P l = plaqAngleC P ψ`. -/
theorem sum_mul_plaqSignC (P : PlaqDatum N)
    (ψ : LayerLink N → ℂ) :
    (∑ ℓ, ψ ℓ * plaqSignC P ℓ) = plaqAngleC P ψ := by
  calc (∑ ℓ, ψ ℓ * plaqSignC P ℓ)
      = ∑ ℓ, (ψ ℓ * (if ℓ = plaqEdgeB P then (1 : ℂ) else 0)
          + ψ ℓ * (if ℓ = plaqEdgeR P then (1 : ℂ) else 0)
          - ψ ℓ * (if ℓ = plaqEdgeT P then (1 : ℂ) else 0)
          - ψ ℓ * (if ℓ = plaqEdgeL P then (1 : ℂ) else 0)) := by
        apply Finset.sum_congr rfl
        intro ℓ _
        rw [plaqSignC_expand]
        ring
    _ = (∑ ℓ, ψ ℓ * (if ℓ = plaqEdgeB P then (1 : ℂ) else 0))
        + (∑ ℓ, ψ ℓ * (if ℓ = plaqEdgeR P then (1 : ℂ) else 0))
        - (∑ ℓ, ψ ℓ * (if ℓ = plaqEdgeT P then (1 : ℂ) else 0))
        - (∑ ℓ, ψ ℓ * (if ℓ = plaqEdgeL P then (1 : ℂ) else 0)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          Finset.sum_add_distrib]
    _ = plaqAngleC P ψ := by
        rw [sum_mul_indicatorC, sum_mul_indicatorC,
          sum_mul_indicatorC, sum_mul_indicatorC]
        rfl

/-- **The sign pattern on the left**: the complex
plaquette angle is also the link sum with the sign
pattern on the left,
`plaqAngleC P ψ = sum l, plaqSignC P l * ψ l`. -/
theorem plaqAngleC_eq_sum (P : PlaqDatum N)
    (ψ : LayerLink N → ℂ) :
    plaqAngleC P ψ = ∑ ℓ, plaqSignC P ℓ * ψ ℓ := by
  rw [← sum_mul_plaqSignC]
  apply Finset.sum_congr rfl
  intro ℓ _
  ring

/-- **Conjugate polarization at one plaquette**: the
link sum of the conjugate potential against the sign
pattern is the conjugate plaquette angle,
`sum l, conj (ψ l) * plaqSignC P l
  = conj (plaqAngleC P ψ)`. -/
theorem sum_conj_mul_plaqSignC (P : PlaqDatum N)
    (ψ : LayerLink N → ℂ) :
    (∑ ℓ, (starRingEnd ℂ) (ψ ℓ) * plaqSignC P ℓ)
      = (starRingEnd ℂ) (plaqAngleC P ψ) := by
  have h := sum_mul_plaqSignC P (fun ℓ => (starRingEnd ℂ) (ψ ℓ))
  rw [h]
  simp only [plaqAngleC, map_add, map_sub]

/-- **THE COMPLEXIFICATION of `maxwellOp N`.** The
complex linear operator on the complexified link space
`LayerLink N -> ℂ` given by the pin's own component
formula with its real coefficients cast to `ℂ`:
`(maxwellOpC N ψ) ℓ = sum P in allPlaqData N,
  plaqSignC P ℓ * plaqAngleC P ψ`. Same enumeration, same
sign pattern, same plaquette angle - complexified. -/
noncomputable def maxwellOpC (N : ℕ) [NeZero N] :
    (LayerLink N → ℂ) →ₗ[ℂ] (LayerLink N → ℂ) where
  toFun ψ ℓ :=
    ∑ P ∈ allPlaqData N, plaqSignC P ℓ * plaqAngleC P ψ
  map_add' ψ η := by
    funext ℓ
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro P _
    simp only [plaqAngleC, Pi.add_apply]
    ring
  map_smul' c ψ := by
    funext ℓ
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro P _
    simp only [plaqAngleC, Pi.smul_apply, smul_eq_mul]
    ring

/-- **Component formula of the complexification** (the
pin's registered polarization formula, complexified,
read pointwise). -/
theorem maxwellOpC_apply (ψ : LayerLink N → ℂ)
    (ℓ : LayerLink N) :
    (maxwellOpC N ψ) ℓ
      = ∑ P ∈ allPlaqData N, plaqSignC P ℓ * plaqAngleC P ψ :=
  rfl

/-- **The complexification extends the real operator,
componentwise**: at a real angle read in `ℂ`, the
complexified operator's component is the real operator's
component, cast. -/
theorem maxwellOpC_ofReal_apply (θ : linkAngle N)
    (ℓ : LayerLink N) :
    (maxwellOpC N (fun m => (θ m : ℂ))) ℓ
      = ((maxwellOp N θ) ℓ : ℂ) := by
  rw [maxwellOpC_apply,
    show (maxwellOp N θ) ℓ
        = ∑ P ∈ allPlaqData N, plaqSign P ℓ * plaqAngle P θ
      from rfl,
    Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro P _
  rw [plaqSignC_eq_cast, plaqAngleC_ofReal,
    Complex.ofReal_mul]

/-- **The complexification extends the real operator**:
at a real angle read in `ℂ`, the complexified operator
is the real operator, cast componentwise. -/
theorem maxwellOpC_ofReal (θ : linkAngle N) :
    maxwellOpC N (fun m => (θ m : ℂ))
      = fun ℓ => ((maxwellOp N θ) ℓ : ℂ) := by
  funext ℓ
  exact maxwellOpC_ofReal_apply θ ℓ

/-- **The quadratic form of the complexification at a
real angle is MAX-2's form, cast**: the pairing of a real
angle against its complexified image is
`(maxwellQuad N θ : ℂ)` - proved by transporting the
pairing to the real pairing and consuming MAX-2's
`maxwellM1_proved` (its form-identity component)
directly. -/
theorem maxwellOpC_quad_ofReal (θ : linkAngle N) :
    (∑ ℓ, (starRingEnd ℂ) ((θ ℓ : ℂ))
        * (maxwellOpC N (fun m => (θ m : ℂ))) ℓ)
      = (maxwellQuad N θ : ℂ) := by
  have hterm : ∀ ℓ : LayerLink N,
      (starRingEnd ℂ) ((θ ℓ : ℂ))
          * (maxwellOpC N (fun m => (θ m : ℂ))) ℓ
        = ((θ ℓ * (maxwellOp N θ) ℓ : ℝ) : ℂ) := by
    intro ℓ
    rw [maxwellOpC_ofReal_apply, Complex.conj_ofReal,
      Complex.ofReal_mul]
  rw [Finset.sum_congr rfl (fun ℓ _ => hterm ℓ),
    ← Complex.ofReal_sum, (maxwellM1_proved (N := N)).1 θ]

end Complexification

section EuclideanTransport

variable {N : ℕ} [NeZero N]

/-- The canonical identification of the Euclidean space
of complex link potentials with plain complex potentials
(the `BridgeMagnetic.euclEquivC` pattern, at the link
seat). -/
def linkEquivC (N : ℕ) [NeZero N] :
    EuclideanSpace ℂ (LayerLink N) ≃ₗ[ℂ] (LayerLink N → ℂ) :=
  WithLp.linearEquiv 2 ℂ (LayerLink N → ℂ)

/-- **Component form of the canonical identification**:
reading a Euclidean link potential through `linkEquivC`
changes nothing at a link. -/
theorem linkEquivC_apply (X : EuclideanSpace ℂ (LayerLink N))
    (ℓ : LayerLink N) :
    linkEquivC N X ℓ = X ℓ :=
  rfl

/-- **The complexified Maxwell operator on the Euclidean
link space**: `maxwellOpC N` transported by `linkEquivC`.
This is the operator in the form the pin's `waveFamily`
registration consumes - a linear map on a
finite-dimensional complex inner product space. -/
noncomputable def maxwellOpCE (N : ℕ) [NeZero N] :
    EuclideanSpace ℂ (LayerLink N)
      →ₗ[ℂ] EuclideanSpace ℂ (LayerLink N) :=
  (linkEquivC N).symm.conj (maxwellOpC N)

/-- **Transport identity**: `linkEquivC` after
`maxwellOpCE` recovers `maxwellOpC` on plain potentials. -/
theorem equiv_maxwellOpCE (X : EuclideanSpace ℂ (LayerLink N)) :
    linkEquivC N (maxwellOpCE N X)
      = maxwellOpC N (linkEquivC N X) :=
  rfl

/-- **Component form of the transport identity.** -/
theorem maxwellOpCE_apply (X : EuclideanSpace ℂ (LayerLink N))
    (ℓ : LayerLink N) :
    (maxwellOpCE N X) ℓ = maxwellOpC N (linkEquivC N X) ℓ :=
  rfl

/-- The Euclidean inner product over `ℂ` at the link
seat, in coordinates (the `BridgeMagnetic`
`euclid_inner_applyC` pattern). -/
theorem euclid_inner_link (X Y : EuclideanSpace ℂ (LayerLink N)) :
    ⟪X, Y⟫_ℂ = ∑ ℓ, (starRingEnd ℂ) (X ℓ) * Y ℓ := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [RCLike.inner_apply]
  exact mul_comm _ _

/-- **The polarized plaquette identity, right form**:
the pairing of `X` against the complexified operator
applied to `Y` is the plaquette sum of conjugate
plaquette angles,
`⟪X, maxwellOpCE N Y⟫
  = sum P in allPlaqData N,
      conj (plaqAngleC P (linkEquivC X))
        * plaqAngleC P (linkEquivC Y)`.
This is the complex polarization of MAX-2's
`maxwellOp_form`: the proof swaps the two finite sums
and spends `sum_conj_mul_plaqSignC` at each plaquette. -/
theorem inner_maxwellOpCE (X Y : EuclideanSpace ℂ (LayerLink N)) :
    ⟪X, maxwellOpCE N Y⟫_ℂ
      = ∑ P ∈ allPlaqData N,
          (starRingEnd ℂ) (plaqAngleC P (linkEquivC N X))
            * plaqAngleC P (linkEquivC N Y) := by
  rw [euclid_inner_link]
  calc (∑ ℓ, (starRingEnd ℂ) (X ℓ) * (maxwellOpCE N Y) ℓ)
      = ∑ ℓ, ∑ P ∈ allPlaqData N,
          (starRingEnd ℂ) (X ℓ)
            * (plaqSignC P ℓ * plaqAngleC P (linkEquivC N Y)) := by
        apply Finset.sum_congr rfl
        intro ℓ _
        rw [maxwellOpCE_apply, maxwellOpC_apply, Finset.mul_sum]
    _ = ∑ P ∈ allPlaqData N, ∑ ℓ,
          (starRingEnd ℂ) (X ℓ)
            * (plaqSignC P ℓ * plaqAngleC P (linkEquivC N Y)) :=
        Finset.sum_comm
    _ = ∑ P ∈ allPlaqData N,
          (starRingEnd ℂ) (plaqAngleC P (linkEquivC N X))
            * plaqAngleC P (linkEquivC N Y) := by
        apply Finset.sum_congr rfl
        intro P _
        rw [← sum_conj_mul_plaqSignC P (linkEquivC N X),
          Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ℓ _
        rw [linkEquivC_apply]
        ring

/-- **The polarized plaquette identity, left form**: the
pairing of the complexified operator applied to `X`
against `Y` is the same plaquette sum as the right form,
`⟪maxwellOpCE N X, Y⟫
  = sum P in allPlaqData N,
      conj (plaqAngleC P (linkEquivC X))
        * plaqAngleC P (linkEquivC Y)`.
The proof conjugates the component formula (the sign
pattern is real, `conj_plaqSignC`) and spends
`plaqAngleC_eq_sum` at each plaquette. -/
theorem maxwellOpCE_inner (X Y : EuclideanSpace ℂ (LayerLink N)) :
    ⟪maxwellOpCE N X, Y⟫_ℂ
      = ∑ P ∈ allPlaqData N,
          (starRingEnd ℂ) (plaqAngleC P (linkEquivC N X))
            * plaqAngleC P (linkEquivC N Y) := by
  rw [euclid_inner_link]
  calc (∑ ℓ, (starRingEnd ℂ) ((maxwellOpCE N X) ℓ) * Y ℓ)
      = ∑ ℓ, ∑ P ∈ allPlaqData N,
          (plaqSignC P ℓ
            * (starRingEnd ℂ) (plaqAngleC P (linkEquivC N X)))
            * Y ℓ := by
        apply Finset.sum_congr rfl
        intro ℓ _
        have h1 : (starRingEnd ℂ) ((maxwellOpCE N X) ℓ)
            = ∑ P ∈ allPlaqData N, plaqSignC P ℓ
                * (starRingEnd ℂ)
                    (plaqAngleC P (linkEquivC N X)) := by
          calc (starRingEnd ℂ) ((maxwellOpCE N X) ℓ)
              = (starRingEnd ℂ)
                  (∑ P ∈ allPlaqData N, plaqSignC P ℓ
                    * plaqAngleC P (linkEquivC N X)) := by
                rw [maxwellOpCE_apply, maxwellOpC_apply]
            _ = ∑ P ∈ allPlaqData N,
                  (starRingEnd ℂ) (plaqSignC P ℓ
                    * plaqAngleC P (linkEquivC N X)) :=
                map_sum _ _ _
            _ = ∑ P ∈ allPlaqData N, plaqSignC P ℓ
                  * (starRingEnd ℂ)
                      (plaqAngleC P (linkEquivC N X)) :=
                Finset.sum_congr rfl (fun P _ => by
                  rw [map_mul, conj_plaqSignC])
        rw [h1, Finset.sum_mul]
    _ = ∑ P ∈ allPlaqData N, ∑ ℓ,
          (plaqSignC P ℓ
            * (starRingEnd ℂ) (plaqAngleC P (linkEquivC N X)))
            * Y ℓ :=
        Finset.sum_comm
    _ = ∑ P ∈ allPlaqData N,
          (starRingEnd ℂ) (plaqAngleC P (linkEquivC N X))
            * plaqAngleC P (linkEquivC N Y) := by
        apply Finset.sum_congr rfl
        intro P _
        rw [plaqAngleC_eq_sum P (linkEquivC N Y),
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ℓ _
        rw [linkEquivC_apply]
        ring

/-- **HEADLINE - the complexified Maxwell operator is
symmetric.** `maxwellOpCE N` is a symmetric
(self-adjoint) operator on the complexified link space,
in exactly the form the pin's `waveFamily` registration
consumes (a `LinearMap.IsSymmetric` witness for
`evolOp`). The proof is the two polarized plaquette
identities above: both pairings are the same plaquette
sum - the complex form of MAX-2's polarization output
(`maxwellOp_form` / `maxwellOp_form_symm`), whose real
form identity is consumed directly in
`maxwellOpC_quad_ofReal` from `maxwellM1_proved`. -/
theorem maxwellOpCE_isSymmetric (N : ℕ) [NeZero N] :
    (maxwellOpCE N).IsSymmetric := by
  intro X Y
  rw [maxwellOpCE_inner, inner_maxwellOpCE]

end EuclideanTransport

section WaveFamilyOnLinks

variable {N : ℕ} [NeZero N]

/-- **THE WAVE FAMILY ON LINK SPACE (the weld).** The
pin's registered `waveFamily`, instantiated at the
complexified link space with generator the complexified
Maxwell operator `maxwellOpCE N` and its symmetry
witness `maxwellOpCE_isSymmetric`. By the pin's
registration this IS the landed `evolOp` of
`SchrodingerDynamics` at that generator - cited, not
rebuilt. -/
noncomputable def linkWaveFamily (N : ℕ) [NeZero N] (t : ℝ) :
    EuclideanSpace ℂ (LayerLink N)
      →ₗ[ℂ] EuclideanSpace ℂ (LayerLink N) :=
  waveFamily (maxwellOpCE_isSymmetric N) t

/-- **Read-back.** The link wave family is exactly the
cited landed `evolOp` at the complexified operator,
unfolded through the pin's registration. -/
theorem linkWaveFamily_unfold (t : ℝ) :
    linkWaveFamily N t
      = evolOp (maxwellOpCE_isSymmetric N) t :=
  rfl

/-- **Group law BY CITATION.** The link wave family
satisfies the one-parameter group law, by the pin's
`waveFamily_add`, itself the landed `evolOp_add`
(`SchrodingerDynamics`). Cited, not re-proved. -/
theorem linkWaveFamily_add (s t : ℝ) :
    linkWaveFamily N (s + t)
      = (linkWaveFamily N s).comp (linkWaveFamily N t) :=
  waveFamily_add _ s t

/-- **Isometry BY CITATION.** The link wave family
preserves norms, by the pin's `waveFamily_isometry`,
itself the landed `evolOp_isometry`
(`SchrodingerDynamics`). Cited, not re-proved. -/
theorem linkWaveFamily_isometry (t : ℝ)
    (X : EuclideanSpace ℂ (LayerLink N)) :
    ‖linkWaveFamily N t X‖ = ‖X‖ :=
  waveFamily_isometry _ t X

/-- **Value at time zero BY CITATION.** The link wave
family at time `0` is the identity, by the pin's
`waveFamily_zero`, itself the landed `evolOp_zero`.
Cited, not re-proved. -/
theorem linkWaveFamily_zero :
    linkWaveFamily N 0 = LinearMap.id :=
  waveFamily_zero _

/-- **Unitary packaging BY CITATION.** The landed
unitary packaging `evolUnitary` at the complexified
operator applies as the link wave family, by the pin's
`waveFamily_unitary_apply`. Cited, not re-proved. -/
theorem linkWaveFamily_unitary_apply (t : ℝ)
    (X : EuclideanSpace ℂ (LayerLink N)) :
    evolUnitary (maxwellOpCE_isSymmetric N) t X
      = linkWaveFamily N t X :=
  waveFamily_unitary_apply _ t X

end WaveFamilyOnLinks

section EigenspacePreservation

variable {N : ℕ} [NeZero N]

/-- **Eigenspace preservation.** The link wave family
preserves each eigenspace of the complexified operator:
for every complex eigenvalue `μ`, the image of the
`μ`-eigenspace of `maxwellOpCE N` under
`linkWaveFamily N t` stays inside that eigenspace. By
citation of the landed `evolOp_map_eigenspace_le`
(`SchrodingerDynamics`), through the pin's registration.
The modes are abstract here - no Fourier identification
is made (that is GR-PROP-2's, gated on MAX-3). -/
theorem linkWaveFamily_map_eigenspace_le (t : ℝ) (μ : ℂ) :
    (Module.End.eigenspace (maxwellOpCE N) μ).map
        (linkWaveFamily N t)
      ≤ Module.End.eigenspace (maxwellOpCE N) μ :=
  evolOp_map_eigenspace_le _ t μ

/-- **Phase action on an eigenspace.** On a vector in
the `μ`-eigenspace of the complexified operator, the
link wave family acts by the eigenphase `evolPhase μ.re
t`, by citation of the landed
`evolOp_apply_mem_eigenspace` (`SchrodingerDynamics`),
through the pin's registration. -/
theorem linkWaveFamily_apply_mem_eigenspace (t : ℝ)
    {ψ : EuclideanSpace ℂ (LayerLink N)} {μ : ℂ}
    (hψ : ψ ∈ Module.End.eigenspace (maxwellOpCE N) μ) :
    linkWaveFamily N t ψ = evolPhase μ.re t • ψ :=
  evolOp_apply_mem_eigenspace _ t hψ

/-- **The family commutes with its generator**, by
citation of the landed `evolOp_apply_commute`
(`SchrodingerDynamics`), through the pin's
registration. -/
theorem linkWaveFamily_apply_commute (t : ℝ)
    (X : EuclideanSpace ℂ (LayerLink N)) :
    linkWaveFamily N t (maxwellOpCE N X)
      = maxwellOpCE N (linkWaveFamily N t X) :=
  evolOp_apply_commute _ t X

/-- **Modes stay modes (in the pin's `ModeFreq`
vocabulary).** If `v` is a mode of the complexified
operator at frequency `ω` - `ModeFreq (maxwellOpCE N) v
ω`, the pin's registered eigenpair statement - then the
evolved vector `linkWaveFamily N t v` is again a mode
of the same operator at the SAME frequency `ω`. The
nonvanishing half is the cited isometry; the eigenpair
half is the cited commutation with the generator. No
frequency is shifted, named, or asserted to exist by
this statement: `v` and `ω` are supplied. -/
theorem modeFreq_linkWaveFamily (t : ℝ)
    {v : EuclideanSpace ℂ (LayerLink N)} {ω : ℂ}
    (hv : ModeFreq (maxwellOpCE N) v ω) :
    ModeFreq (maxwellOpCE N) (linkWaveFamily N t v) ω := by
  refine ⟨?_, ?_⟩
  · intro h0
    have hnorm := linkWaveFamily_isometry (N := N) t v
    rw [h0, norm_zero] at hnorm
    exact hv.1 (norm_eq_zero.mp hnorm.symm)
  · rw [← linkWaveFamily_apply_commute, hv.2, map_smul]

/-- **Phase action on a mode at a real frequency.** If
`v` is a mode of the complexified operator at the real
frequency `ω` (cast to `ℂ`), the link wave family acts
on it by the eigenphase at `ω`:
`linkWaveFamily N t v = evolPhase ω t • v`. By citation
of `linkWaveFamily_apply_mem_eigenspace`. The
frequency is supplied, not asserted to occur. -/
theorem linkWaveFamily_apply_of_modeFreq (t : ℝ)
    {v : EuclideanSpace ℂ (LayerLink N)} {ω : ℝ}
    (hv : ModeFreq (maxwellOpCE N) v ((ω : ℂ))) :
    linkWaveFamily N t v = evolPhase ω t • v := by
  have hmem : v ∈ Module.End.eigenspace (maxwellOpCE N) ((ω : ℂ)) :=
    Module.End.mem_eigenspace_iff.mpr hv.2
  have h := linkWaveFamily_apply_mem_eigenspace (N := N) t hmem
  rwa [Complex.ofReal_re] at h

end EigenspacePreservation

/-! ## Axiom audit

Headlines checked on exactly
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms maxwellOpCE_isSymmetric
#print axioms maxwellOpC_quad_ofReal
#print axioms linkWaveFamily_add
#print axioms linkWaveFamily_isometry
#print axioms linkWaveFamily_map_eigenspace_le
#print axioms modeFreq_linkWaveFamily
#print axioms linkWaveFamily_apply_of_modeFreq

end ThetLogos
