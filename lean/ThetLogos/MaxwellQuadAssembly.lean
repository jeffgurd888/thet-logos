import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import ThetLogos.MaxwellQuadWeld

namespace ThetLogos

open Finset

/-!
# ThetLogos.MaxwellQuadAssembly - MAX-2: assembly at general N

**Status: MAX-2 landing brick. NO CLAIM. No Millennium
statement, no ladder rung, no dial (dials stay 0/4).**
Governing texts: the MAX-0 pin `MaxwellQuadPost.lean` (its
registered names and its registered (M1)/(M2)/(M3) forms
govern - this brick discharges exactly what the pin states,
under exactly its hypotheses) and MAX-1
`MaxwellQuadWeld.lean` (the weld
`plaqHol_circle_exp_weld` and the atom `maxwellM4_proved`),
under the scoping memo
`scoping-maxwell-finite-2026-10-31.md` sections 3-5.

Contents, in order:

1. The operator in the pin's registered form: the component
formula `maxwellOp_apply` (the pin defines `maxwellOp N` by
polarization of `maxwellQuad N`), the bilinear form identity
`maxwellOp_form`, its diagonal `maxwellOp_form_self`, and
its symmetry `maxwellOp_form_symm` (the coordinate form of
self-adjointness).
2. **(M1)** `maxwellM1_proved`: form identity and positivity,
exactly the pin's `maxwellM1 N`.
3. **(M2)** `maxwellM2_proved`: kernel = flat link angles,
exactly the pin's registered iff `maxwellM2 N`.
4. **(M3)** `maxwellM3_proved`: every pure-gauge angle has
vanishing plaquette angle at every plaquette datum
(additive telescoping around the four corners), exactly the
pin's `maxwellM3 N`; hence `maxwellOp_gaugeAngle` puts every
gauge mode in the kernel of the operator.
5. The Wilson tie at one plaquette, as two-sided cosine
bounds only (never an equality of actions):
`wilson_cos_bounds` and its plaquette form
`wilson_tie_plaqAngle`: for `|phi| <= 1`,
`(1/4) * phi^2 <= 1 - Real.cos phi` and
`1 - Real.cos phi <= (1/2) * phi^2` - the quadratic term of
the Wilson weight's per-plaquette term `1 - cos phi`, with
the overall scalar beta/2 stripped, matching `maxwellQuad`'s
per-plaquette term `(plaqAngle P theta)^2`.

## Fences (memo section 5, K-MAX-2)

Finite in every statement: every result here is about the
chosen finite operator on the finite link-angle space at
spacing 1; not a derived measured number, not a gravity
object, not a statement about any limit. FENCE SENTENCE:
the words "Lorentzian" and "bridge" are not earned terms in
this line and appear in this module only inside this fence
sentence. Disjoint from OP-1's photon (the massless
Higgs-sector direction) - no trading between the two senses.

## K-MAX-1 re-check (on the face)

`maxwellOp` is the pin's own polarization definition on the
link-angle space `LayerLink N -> R`: its component formula
sums `plaqSign P l * plaqAngle P theta` over the registered
plaquette enumeration. It is not definitionally the transfer
operator (which acts on functions on link configurations),
the plaquette block/factor (scalar kernels on the group),
`magLin` (vertex potentials in a background connection), or
the vertex `lapLin`, and its form `maxwellQuad` is not
`osForm`; the types and the component formula differ from
each of those, and the form identity proved below is proved
for this definition, not transported from any of them.
-/

section OperatorForm

variable {N : ℕ} [NeZero N]

/-- **Component formula of the operator** (the pin's
registered polarization definition, read pointwise):
`(maxwellOp N theta) l = sum P in allPlaqData N,
plaqSign P l * plaqAngle P theta`. -/
theorem maxwellOp_apply (θ : linkAngle N) (ℓ : LayerLink N) :
    (maxwellOp N θ) ℓ
      = ∑ P ∈ allPlaqData N, plaqSign P ℓ * plaqAngle P θ :=
  rfl

open Classical in
/-- The link sum of an angle against one indicator:
`sum l, theta l * (if l = e then 1 else 0) = theta e`. -/
theorem sum_mul_indicator (θ : linkAngle N) (e : LayerLink N) :
    (∑ ℓ, θ ℓ * (if ℓ = e then (1 : ℝ) else 0)) = θ e := by
  rw [Finset.sum_eq_single e]
  · simp
  · intro ℓ _ hℓ
    simp [hℓ]
  · simp

open Classical in
/-- **Polarization identity at one plaquette**: the link sum
of `theta` against the plaquette sign pattern is the
plaquette angle itself,
`sum l, theta l * plaqSign P l = plaqAngle P theta`
(counted with multiplicity, as `plaqSign` registers). -/
theorem sum_mul_plaqSign (P : PlaqDatum N) (θ : linkAngle N) :
    (∑ ℓ, θ ℓ * plaqSign P ℓ) = plaqAngle P θ := by
  calc (∑ ℓ, θ ℓ * plaqSign P ℓ)
      = ∑ ℓ, (θ ℓ * (if ℓ = plaqEdgeB P then (1 : ℝ) else 0)
          + θ ℓ * (if ℓ = plaqEdgeR P then (1 : ℝ) else 0)
          - θ ℓ * (if ℓ = plaqEdgeT P then (1 : ℝ) else 0)
          - θ ℓ * (if ℓ = plaqEdgeL P then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro ℓ _
        simp only [plaqSign]
        ring
    _ = (∑ ℓ, θ ℓ * (if ℓ = plaqEdgeB P then (1 : ℝ) else 0))
        + (∑ ℓ, θ ℓ * (if ℓ = plaqEdgeR P then (1 : ℝ) else 0))
        - (∑ ℓ, θ ℓ * (if ℓ = plaqEdgeT P then (1 : ℝ) else 0))
        - (∑ ℓ, θ ℓ * (if ℓ = plaqEdgeL P then (1 : ℝ) else 0)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          Finset.sum_add_distrib]
    _ = plaqAngle P θ := by
        rw [sum_mul_indicator, sum_mul_indicator,
          sum_mul_indicator, sum_mul_indicator]
        rfl

/-- **The bilinear form of the operator**: for all angles
`theta, eta`,
`sum l, theta l * (maxwellOp N eta) l
  = sum P in allPlaqData N, plaqAngle P theta * plaqAngle P eta`.
This is the polarization of `maxwellQuad N`. -/
theorem maxwellOp_form (θ η : linkAngle N) :
    (∑ ℓ, θ ℓ * (maxwellOp N η) ℓ)
      = ∑ P ∈ allPlaqData N, plaqAngle P θ * plaqAngle P η := by
  calc (∑ ℓ, θ ℓ * (maxwellOp N η) ℓ)
      = ∑ ℓ, ∑ P ∈ allPlaqData N,
          θ ℓ * (plaqSign P ℓ * plaqAngle P η) := by
        apply Finset.sum_congr rfl
        intro ℓ _
        rw [maxwellOp_apply, Finset.mul_sum]
    _ = ∑ P ∈ allPlaqData N, ∑ ℓ,
          θ ℓ * (plaqSign P ℓ * plaqAngle P η) :=
        Finset.sum_comm
    _ = ∑ P ∈ allPlaqData N, ∑ ℓ,
          (θ ℓ * plaqSign P ℓ) * plaqAngle P η := by
        apply Finset.sum_congr rfl
        intro P _
        apply Finset.sum_congr rfl
        intro ℓ _
        ring
    _ = ∑ P ∈ allPlaqData N,
          (∑ ℓ, θ ℓ * plaqSign P ℓ) * plaqAngle P η := by
        apply Finset.sum_congr rfl
        intro P _
        rw [Finset.sum_mul]
    _ = ∑ P ∈ allPlaqData N, plaqAngle P θ * plaqAngle P η := by
        apply Finset.sum_congr rfl
        intro P _
        rw [sum_mul_plaqSign]

/-- **Symmetry of the operator's form** (the coordinate form
of self-adjointness):
`sum l, theta l * (maxwellOp N eta) l
  = sum l, eta l * (maxwellOp N theta) l`. -/
theorem maxwellOp_form_symm (θ η : linkAngle N) :
    (∑ ℓ, θ ℓ * (maxwellOp N η) ℓ)
      = ∑ ℓ, η ℓ * (maxwellOp N θ) ℓ := by
  rw [maxwellOp_form, maxwellOp_form]
  apply Finset.sum_congr rfl
  intro P _
  ring

/-- The quadratic form is nonnegative: it is a sum of
squares over the registered plaquette enumeration. -/
theorem maxwellQuad_nonneg (θ : linkAngle N) :
    0 ≤ maxwellQuad N θ := by
  unfold maxwellQuad
  exact Finset.sum_nonneg (fun P _ => sq_nonneg _)

/-- **The diagonal of the operator's form is the quadratic
form**: `sum l, theta l * (maxwellOp N theta) l
= maxwellQuad N theta`. -/
theorem maxwellOp_form_self (θ : linkAngle N) :
    (∑ ℓ, θ ℓ * (maxwellOp N θ) ℓ) = maxwellQuad N θ := by
  rw [maxwellOp_form]
  unfold maxwellQuad
  apply Finset.sum_congr rfl
  intro P _
  rw [sq]

end OperatorForm

section M1

variable {N : ℕ} [NeZero N]

/-- **(M1) Form identity + positivity, discharged exactly
as registered in the MAX-0 pin (`maxwellM1 N`)**: the form
of `maxwellOp N` is `maxwellQuad N` in the coordinate form
of the inner product, and that form is nonnegative. -/
theorem maxwellM1_proved : maxwellM1 N :=
  ⟨fun θ => maxwellOp_form_self θ,
    fun θ => (maxwellOp_form_self θ) ▸ maxwellQuad_nonneg θ⟩

end M1

section M2

variable {N : ℕ} [NeZero N]

/-- **(M2) Kernel = flat link angles, discharged exactly as
registered in the MAX-0 pin (`maxwellM2 N`)**: the
registered iff holds for the pin's enumeration
`allPlaqData N` as registered - the forward direction reads
flatness off the vanishing of the form (a sum of squares),
the backward direction is termwise in the component
formula. No enumeration was repaired. -/
theorem maxwellM2_proved : maxwellM2 N := by
  intro θ
  constructor
  · intro hθ P hP
    have hform : (∑ ℓ, θ ℓ * (maxwellOp N θ) ℓ) = 0 := by
      rw [hθ]
      simp
    have hquad : maxwellQuad N θ = 0 :=
      (maxwellOp_form_self θ) ▸ hform
    have hterm : (plaqAngle P θ) ^ 2 = 0 := by
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun Q _ => sq_nonneg (plaqAngle Q θ))).mp
        (show (∑ Q ∈ allPlaqData N, (plaqAngle Q θ) ^ 2) = 0
          from hquad)
      exact h0 P hP
    by_contra hc
    exact (pow_ne_zero 2 hc) hterm
  · intro hθ
    funext ℓ
    rw [maxwellOp_apply]
    simp only [Pi.zero_apply]
    exact Finset.sum_eq_zero (fun P hP => by
      rw [hθ P hP, mul_zero])

end M2

section M3

variable {N : ℕ} [NeZero N]

/-- Tail of the bottom edge: the base corner `c00`. -/
theorem linkTail_plaqEdgeB (P : PlaqDatum N) :
    linkTail (plaqEdgeB P) = plaqCorner00 P := rfl

/-- Tail of the right edge: the corner `c10`. -/
theorem linkTail_plaqEdgeR (P : PlaqDatum N) :
    linkTail (plaqEdgeR P) = plaqCorner10 P := rfl

/-- Tail of the top edge: the corner `c01`. -/
theorem linkTail_plaqEdgeT (P : PlaqDatum N) :
    linkTail (plaqEdgeT P) = plaqCorner01 P := rfl

/-- Tail of the left edge: the base corner `c00`. -/
theorem linkTail_plaqEdgeL (P : PlaqDatum N) :
    linkTail (plaqEdgeL P) = plaqCorner00 P := rfl

/-- Head of the bottom edge: the corner `c10`. -/
theorem linkHead_plaqEdgeB (P : PlaqDatum N) :
    linkHead (plaqEdgeB P) = plaqCorner10 P := rfl

/-- Head of the right edge: the corner `c11`. -/
theorem linkHead_plaqEdgeR (P : PlaqDatum N) :
    linkHead (plaqEdgeR P) = plaqCorner11 P := by
  show layerShift P.nu P.hnu (plaqCorner10 P) = plaqCorner11 P
  exact (plaqCorner11_eq_shift10 P).symm

/-- Head of the top edge: the corner `c11`. -/
theorem linkHead_plaqEdgeT (P : PlaqDatum N) :
    linkHead (plaqEdgeT P) = plaqCorner11 P := rfl

/-- Head of the left edge: the corner `c01`. -/
theorem linkHead_plaqEdgeL (P : PlaqDatum N) :
    linkHead (plaqEdgeL P) = plaqCorner01 P := rfl

/-- The pure-gauge angle on the bottom edge:
`phi c10 - phi c00`. -/
theorem gaugeAngle_plaqEdgeB (φ : LayerSite N → ℝ)
    (P : PlaqDatum N) :
    gaugeAngle φ (plaqEdgeB P)
      = φ (plaqCorner10 P) - φ (plaqCorner00 P) := by
  show φ (linkHead (plaqEdgeB P)) - φ (linkTail (plaqEdgeB P))
    = _
  rw [linkHead_plaqEdgeB, linkTail_plaqEdgeB]

/-- The pure-gauge angle on the right edge:
`phi c11 - phi c10`. -/
theorem gaugeAngle_plaqEdgeR (φ : LayerSite N → ℝ)
    (P : PlaqDatum N) :
    gaugeAngle φ (plaqEdgeR P)
      = φ (plaqCorner11 P) - φ (plaqCorner10 P) := by
  show φ (linkHead (plaqEdgeR P)) - φ (linkTail (plaqEdgeR P))
    = _
  rw [linkHead_plaqEdgeR, linkTail_plaqEdgeR]

/-- The pure-gauge angle on the top edge:
`phi c11 - phi c01`. -/
theorem gaugeAngle_plaqEdgeT (φ : LayerSite N → ℝ)
    (P : PlaqDatum N) :
    gaugeAngle φ (plaqEdgeT P)
      = φ (plaqCorner11 P) - φ (plaqCorner01 P) := by
  show φ (linkHead (plaqEdgeT P)) - φ (linkTail (plaqEdgeT P))
    = _
  rw [linkHead_plaqEdgeT, linkTail_plaqEdgeT]

/-- The pure-gauge angle on the left edge:
`phi c01 - phi c00`. -/
theorem gaugeAngle_plaqEdgeL (φ : LayerSite N → ℝ)
    (P : PlaqDatum N) :
    gaugeAngle φ (plaqEdgeL P)
      = φ (plaqCorner01 P) - φ (plaqCorner00 P) := by
  show φ (linkHead (plaqEdgeL P)) - φ (linkTail (plaqEdgeL P))
    = _
  rw [linkHead_plaqEdgeL, linkTail_plaqEdgeL]

/-- **(M3) Gauge modes are in the kernel, discharged
exactly as registered in the MAX-0 pin (`maxwellM3 N`)**:
for every site potential `phi` and every plaquette datum
`P`, the plaquette angle of the pure-gauge angle vanishes,
by additive telescoping around the four corners:
`(phi c10 - phi c00) + (phi c11 - phi c10)
  - (phi c11 - phi c01) - (phi c01 - phi c00) = 0`. -/
theorem maxwellM3_proved : maxwellM3 N := by
  intro φ P
  unfold plaqAngle
  rw [gaugeAngle_plaqEdgeB, gaugeAngle_plaqEdgeR,
    gaugeAngle_plaqEdgeT, gaugeAngle_plaqEdgeL]
  ring

/-- **Gauge modes lie in the kernel of the operator**
(the operator form of (M3), through (M2)):
`maxwellOp N (gaugeAngle phi) = 0` for every site
potential `phi`. -/
theorem maxwellOp_gaugeAngle (φ : LayerSite N → ℝ) :
    maxwellOp N (gaugeAngle φ) = 0 :=
  ((maxwellM2_proved (N := N)) (gaugeAngle φ)).mpr
    (fun P _ => maxwellM3_proved φ P)

end M3

section WilsonTie

/-- The half-angle identity behind the Wilson tie:
`1 - Real.cos phi = 2 * (Real.sin (phi / 2))^2`. -/
theorem one_sub_cos_eq (φ : ℝ) :
    1 - Real.cos φ = 2 * (Real.sin (φ / 2)) ^ 2 := by
  have h2 : Real.cos φ = 2 * (Real.cos (φ / 2)) ^ 2 - 1 := by
    have h := Real.cos_two_mul (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring] at h
    exact h
  have hsc := Real.sin_sq_add_cos_sq (φ / 2)
  linarith

/-- Lower bound on `|sin t|` on `|t| <= 1/2`, from
Mathlib's `Real.sin_ge_sub_cube`:
`(23/24) * |t| <= |Real.sin t|`. -/
theorem abs_sin_ge_of_abs_le_half {t : ℝ} (ht : |t| ≤ 1 / 2) :
    (23 / 24) * |t| ≤ |Real.sin t| := by
  have ht' := abs_le.mp ht
  have key : ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 →
      (23 / 24) * s ≤ Real.sin s := by
    intro s hs hs2
    have hcube : s - s ^ 3 / 6 ≤ Real.sin s :=
      Real.sin_ge_sub_cube hs
    have hs2' : s ^ 2 ≤ 1 / 4 := by nlinarith
    have h3 : s ^ 3 ≤ s / 4 := by
      have h := mul_le_mul_of_nonneg_left hs2' hs
      calc s ^ 3 = s * s ^ 2 := by ring
        _ ≤ s * (1 / 4) := h
        _ = s / 4 := by ring
    linarith
  have hpi : (1 : ℝ) ≤ Real.pi := by
    have h := Real.one_le_pi_div_two
    have hp := Real.pi_pos
    linarith
  have hsinabs : |Real.sin t| = Real.sin |t| := by
    have hodd : ∀ s : ℝ, |Real.sin (-s)| = |Real.sin s| := by
      intro s
      rw [Real.sin_neg, abs_neg]
    rcases lt_or_ge t 0 with ht0 | ht0
    · have hsin : 0 ≤ Real.sin (-t) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
          (by linarith)
      rw [abs_of_neg ht0, ← hodd t]
      exact abs_of_nonneg hsin
    · have hsin : 0 ≤ Real.sin t :=
        Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith)
      rw [abs_of_nonneg ht0]
      exact abs_of_nonneg hsin
  rw [hsinabs]
  exact key |t| (abs_nonneg t) ht

/-- **The Wilson tie at one plaquette, upper and lower
bound together** (never an equality of actions): for
`|phi| <= 1`,
`(1/4) * phi^2 <= 1 - Real.cos phi` and
`1 - Real.cos phi <= (1/2) * phi^2`. The cosine estimates
are Mathlib's (`Real.sin_sq_le_sq`,
`Real.sin_ge_sub_cube`, read through the half-angle
identity `one_sub_cos_eq`). -/
theorem wilson_cos_bounds {φ : ℝ} (hφ : |φ| ≤ 1) :
    (1 / 4) * φ ^ 2 ≤ 1 - Real.cos φ
      ∧ 1 - Real.cos φ ≤ (1 / 2) * φ ^ 2 := by
  rw [one_sub_cos_eq]
  have hup : (Real.sin (φ / 2)) ^ 2 ≤ (φ / 2) ^ 2 :=
    Real.sin_sq_le_sq
  have hhalf : |φ / 2| ≤ 1 / 2 := by
    rw [abs_div, abs_two]
    linarith [hφ]
  have hlo := abs_sin_ge_of_abs_le_half hhalf
  have habs : |φ / 2| ^ 2 = φ ^ 2 / 4 := by
    rw [sq_abs]
    ring
  have hlo2 : ((23 / 24) * |φ / 2|) ^ 2
      ≤ (Real.sin (φ / 2)) ^ 2 := by
    rw [← sq_abs (Real.sin (φ / 2))]
    exact pow_le_pow_left₀ (by positivity) hlo 2
  constructor
  · nlinarith [sq_nonneg φ, hlo2, habs]
  · nlinarith [sq_nonneg φ, hup]

/-- **The Wilson tie in plaquette form**: at any plaquette
datum `P` and any angle `theta` whose plaquette angle
satisfies `|plaqAngle P theta| <= 1`, the Wilson weight's
per-plaquette term `1 - Real.cos (plaqAngle P theta)` is
trapped between `(1/4)` and `(1/2)` of the quadratic form's
per-plaquette term `(plaqAngle P theta)^2` - the tie
between `maxwellQuad` and the Wilson action, with the
overall scalar beta/2 stripped, as two-sided bounds only. -/
theorem wilson_tie_plaqAngle {N : ℕ} [NeZero N]
    (P : PlaqDatum N) (θ : linkAngle N)
    (hθ : |plaqAngle P θ| ≤ 1) :
    (1 / 4) * (plaqAngle P θ) ^ 2
        ≤ 1 - Real.cos (plaqAngle P θ)
      ∧ 1 - Real.cos (plaqAngle P θ)
        ≤ (1 / 2) * (plaqAngle P θ) ^ 2 :=
  wilson_cos_bounds hθ

end WilsonTie

end ThetLogos
