/-
# ThetLogos.PlaqBlockReductions — Brick A2-2b: reductions and
 symmetries of the plaquette block (Route B)

**Fences, up front.** NO CLAIM. Parts of the Clay Yang–Mills
statement closed by this module: **0**. Dials **0/4**, unmoved.
Route B scope on the face: a landed A2-2 buys the one-plaquette
mechanism + leading square only — this brick is **NOT**
`𝒜 ⪰ 0`, **NOT** clause (a), and the block is not a factor of
`layerKernel`. Header of `PlaquetteTelescoping` (A2-2a, the
registration; the pack's name `PlaqBlockRegistration` is that
module) and of `PlaquetteFactorPD` (A2-1; the pack's
`PlaquetteFactorPosDef`) govern the objects consumed here:
`PlaqBlock`, `PlaqKernel` Ψ, `plaquetteFactor_posDef_classFn`
and its series form (consumed by A2-2c, not here), and the
landed trace family `trace_repMatrix_conj` /
`trace_repMatrix_inv`. The literal quotient form R1 is
CERTIFIED DEAD (probe BR1-005) and is not touched. Probe
routing consumed as background only: (T) exact, (P) PASS with
the coefficient law `c_π = (ĉ_π / dim π)⁴`; the `k ↔ −k`
pairing caveat at non-self-dual labels is strategy-bearing
for A2-2c and is noted here, not consumed.

## What lands in this brick

1. **Full-stratum vs corner-integral form of `PlaqBlock`**
   (`plaqBlockStratum_eq_plaqBlock`): the block as an integral
   over the full stratum `LayerSite N → G` equals the
   corner-integral form of A2-2a, via the owned real
   pi-measure transport `integral_comp_emb_real`
   (`PlaneCrossingBeta2`, the real copy of the corpus's
   `integral_comp_emb` / `integral_pi_restrict` pattern),
   along the corner embedding `cornerEmb` (injective at
   `Even N`, `4 ≤ N`, by A2-2a's corner distinctness).
2. **Cyclic-rotation invariance of column words under trace**
   (`wordDensity_rotate4` and its column-word corollaries):
   rotating a column word `a · u′ · b⁻¹ · u⁻¹` does not change
   `wordDensity`, hence does not change its factor.
3. **Ψ's elementary symmetries** from `CornerWeight`'s (here:
   `PlaqKernel`'s) own integral representation, by Haar
   change of variables on the four corners: conjugation of
   the `u`-data (`plaqBlock_conj_u`, corners left-translated),
   conjugation of the `u′`-data (`plaqBlock_conj_u'`, corners
   right-translated), exchange of the two arguments
   (`plaqBlock_swap`, corners inverted — the inverted word's
   density is the swapped word's density by inversion +
   rotation), and the `β = 0` normalization.
4. **Separate class invariance of Ψ: CLOSED at this level**
   (`plaqKernel_class_left`, `plaqKernel_class_right`,
   bundled as `plaqKernel_separately_classFn`). The section
   configurations intertwine with the two conjugation actions
   of item 3 on the nose, so both conjuncts of the registered
   (P)(ii) close by change of variables alone.

## DEFERRED TO A2-2d (stop rule; not a kill, not assumed)

- **Both-arguments inversion** `Ψ x⁻¹ y⁻¹ = Ψ x y`: no
  per-factor density identity exists at the change-of-
  variables level — inverting and rotating the bottom word
  of `Ψ x⁻¹ y⁻¹` produces a word differing from the bottom
  word of `Ψ x y` in its first letter, so no corner
  substitution proves it factorwise. Obstruction named:
  the identity, if true, is integrated (character /
  coefficient-law level), not factorwise. DEFERRED TO A2-2d.
- **Corner permutation / plaquette rotation of the corners
  alone** (without simultaneously rotating the edge data):
  not a symmetry of the integrand — the four factors pair
  corners to fixed edges. A rotated-plaquette statement
  needs a rotated datum and is not attempted here.
  DEFERRED TO A2-2d (datum-rotation form).
- Nothing else in this brick is deferred: items 1–4 above
  land in full, including separate class invariance.
-/

import ThetLogos.PlaquetteTelescoping
import ThetLogos.PlaneCrossingBeta2

namespace ThetLogos

open Finset MeasureTheory

section WordRotation

variable {G : Type*} [Group G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- **Rotation of a two-letter word**: `wordDensity` of
`x * y` equals `wordDensity` of `y * x` — the word `x * y`
is the conjugate of `y * x` by `x`, and `wordDensity` is a
class function (`wordDensity_conj_invariant`, via the landed
`trace_repMatrix_conj`). -/
theorem wordDensity_mul_rotate (x y : G) :
    wordDensity ρ (x * y) = wordDensity ρ (y * x) := by
  have h := wordDensity_conj_invariant ρ (y * x) x
  have heq : x * (y * x) * x⁻¹ = x * y := by group
  rw [heq] at h
  exact h

/-- **Inversion of a word**: `wordDensity` of `w⁻¹` equals
`wordDensity` of `w`, via the landed `trace_repMatrix_inv`
(the real part of a represented trace is inversion-stable). -/
theorem wordDensity_inv (w : G) :
    wordDensity ρ w⁻¹ = wordDensity ρ w := by
  unfold wordDensity
  rw [trace_repMatrix_inv]

/-- **Cyclic rotation of a four-letter word**:
`wordDensity (w * x * y * z) = wordDensity (x * y * z * w)`. -/
theorem wordDensity_rotate4 (w x y z : G) :
    wordDensity ρ (w * x * y * z) = wordDensity ρ (x * y * z * w) := by
  have e1 : w * x * y * z = w * (x * y * z) := by group
  have e2 : x * y * z * w = (x * y * z) * w := by group
  rw [e1, e2]
  exact wordDensity_mul_rotate ρ w (x * y * z)

/-- The plaquette factor of a word, `exp (−(β · wordDensity w))`:
`columnKernel` is this factor at its column word. -/
noncomputable def wordFactor (β : ℝ) (w : G) : ℝ :=
  Real.exp (-(β * wordDensity ρ w))

theorem columnKernel_eq_wordFactor (β : ℝ) (a b u u' : G) :
    columnKernel ρ β a b u u' = wordFactor ρ β (a * u' * b⁻¹ * u⁻¹) :=
  rfl

/-- The word factor is a class function of its word. -/
theorem wordFactor_conj (β : ℝ) (g w : G) :
    wordFactor ρ β (g * w * g⁻¹) = wordFactor ρ β w := by
  unfold wordFactor
  rw [wordDensity_conj_invariant]

/-- The word factor is inversion-stable in its word. -/
theorem wordFactor_inv (β : ℝ) (w : G) :
    wordFactor ρ β w⁻¹ = wordFactor ρ β w := by
  unfold wordFactor
  rw [wordDensity_inv]

/-- The word factor is invariant under cyclic rotation of
its (four-letter) word. -/
theorem wordFactor_rotate4 (β : ℝ) (w x y z : G) :
    wordFactor ρ β (w * x * y * z) = wordFactor ρ β (x * y * z * w) := by
  unfold wordFactor
  rw [wordDensity_rotate4]

/-- **Column-word rotation 1**: the first cyclic rotation of
the column word `a * u' * b⁻¹ * u⁻¹` has the same density. -/
theorem wordDensity_column_rotate1 (a b u u' : G) :
    wordDensity ρ (a * u' * b⁻¹ * u⁻¹)
      = wordDensity ρ (u' * b⁻¹ * u⁻¹ * a) :=
  wordDensity_rotate4 ρ a u' b⁻¹ u⁻¹

/-- **Column-word rotation 2**. -/
theorem wordDensity_column_rotate2 (a b u u' : G) :
    wordDensity ρ (a * u' * b⁻¹ * u⁻¹)
      = wordDensity ρ (b⁻¹ * u⁻¹ * a * u') := by
  rw [wordDensity_column_rotate1]
  exact wordDensity_rotate4 ρ u' b⁻¹ u⁻¹ a

/-- **Column-word rotation 3**. -/
theorem wordDensity_column_rotate3 (a b u u' : G) :
    wordDensity ρ (a * u' * b⁻¹ * u⁻¹)
      = wordDensity ρ (u⁻¹ * a * u' * b⁻¹) := by
  rw [wordDensity_column_rotate2]
  exact wordDensity_rotate4 ρ b⁻¹ u⁻¹ a u'

/-- **Column-factor rotation**: the exponential factor of a
column word is unchanged by any of its cyclic rotations
(the form A2-2c's corner contractions consume). -/
theorem wordFactor_column_rotations (β : ℝ) (a b u u' : G) :
    wordFactor ρ β (a * u' * b⁻¹ * u⁻¹)
      = wordFactor ρ β (u' * b⁻¹ * u⁻¹ * a)
    ∧ wordFactor ρ β (a * u' * b⁻¹ * u⁻¹)
      = wordFactor ρ β (b⁻¹ * u⁻¹ * a * u')
    ∧ wordFactor ρ β (a * u' * b⁻¹ * u⁻¹)
      = wordFactor ρ β (u⁻¹ * a * u' * b⁻¹) := by
  exact ⟨wordFactor_rotate4 ρ β a u' b⁻¹ u⁻¹,
    (wordFactor_rotate4 ρ β a u' b⁻¹ u⁻¹).trans
      (wordFactor_rotate4 ρ β u' b⁻¹ u⁻¹ a),
    (wordFactor_rotate4 ρ β a u' b⁻¹ u⁻¹).trans
      ((wordFactor_rotate4 ρ β u' b⁻¹ u⁻¹ a).trans
        (wordFactor_rotate4 ρ β b⁻¹ u⁻¹ a u'))⟩

/-- **The inverted column word, swapped**: at inverted corner
values, the column factor with exchanged boundary data equals
the original column factor. The inverted word
`(a⁻¹ * u' * b * u⁻¹)` has inverse `u * b⁻¹ * u'⁻¹ * a`, whose
third cyclic rotation is the swapped word
`a * u * b⁻¹ * u'⁻¹`; density sees neither inversion nor
rotation. This is the factor identity behind `plaqBlock_swap`. -/
theorem columnKernel_inv_swap (β : ℝ) (a b u u' : G) :
    columnKernel ρ β a⁻¹ b⁻¹ u u' = columnKernel ρ β a b u' u := by
  rw [columnKernel_eq_wordFactor, columnKernel_eq_wordFactor]
  have hinv : (a⁻¹ * u' * (b⁻¹)⁻¹ * u⁻¹)⁻¹ = u * b⁻¹ * u'⁻¹ * a := by
    group
  calc wordFactor ρ β (a⁻¹ * u' * (b⁻¹)⁻¹ * u⁻¹)
      = wordFactor ρ β ((a⁻¹ * u' * (b⁻¹)⁻¹ * u⁻¹)⁻¹) :=
        (wordFactor_inv ρ β _).symm
    _ = wordFactor ρ β (u * b⁻¹ * u'⁻¹ * a) := by rw [hinv]
    _ = wordFactor ρ β (b⁻¹ * u'⁻¹ * a * u) :=
        wordFactor_rotate4 ρ β u b⁻¹ u'⁻¹ a
    _ = wordFactor ρ β (u'⁻¹ * a * u * b⁻¹) :=
        wordFactor_rotate4 ρ β b⁻¹ u'⁻¹ a u
    _ = wordFactor ρ β (a * u * b⁻¹ * u'⁻¹) :=
        wordFactor_rotate4 ρ β u'⁻¹ a u b⁻¹

/-- **Corner left-translation = conjugation of the `u`-edge**:
left-translating both corner values of a column by `g` while
conjugating its `u`-edge by `g` leaves the column factor
unchanged — the translated word is the conjugate of the
original word. -/
theorem columnKernel_leftMul_conj (β : ℝ) (g a b u u' : G) :
    columnKernel ρ β (g * a) (g * b) (g * u * g⁻¹) u'
      = columnKernel ρ β a b u u' := by
  rw [columnKernel_eq_wordFactor, columnKernel_eq_wordFactor]
  have e : (g * a) * u' * (g * b)⁻¹ * (g * u * g⁻¹)⁻¹
      = g * (a * u' * b⁻¹ * u⁻¹) * g⁻¹ := by group
  rw [e]
  exact wordFactor_conj ρ β g _

/-- **Corner right-translation = conjugation of the `u'`-edge**:
right-translating both corner values of a column by `h` while
conjugating its `u'`-edge by `h⁻¹` leaves the column factor
unchanged — the translated word is the original word on the
nose (the translations cancel inside the word). -/
theorem columnKernel_rightMul_conj (β : ℝ) (h a b u u' : G) :
    columnKernel ρ β (a * h) (b * h) u (h⁻¹ * u' * h)
      = columnKernel ρ β a b u u' := by
  rw [columnKernel_eq_wordFactor, columnKernel_eq_wordFactor]
  have e : (a * h) * (h⁻¹ * u' * h) * (b * h)⁻¹ * u⁻¹
      = a * u' * b⁻¹ * u⁻¹ := by group
  rw [e]

end WordRotation

section CornerSubstitutions

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- Per-coordinate inversion of the four corners, as a
measurable equivalence of `Fin 4 → G`. -/
def cornerInvEquiv : (Fin 4 → G) ≃ᵐ (Fin 4 → G) where
  toFun a := fun i => (a i)⁻¹
  invFun a := fun i => (a i)⁻¹
  left_inv a := by funext i; simp
  right_inv a := by funext i; simp
  measurable_toFun := by
    rw [measurable_pi_iff]
    intro i
    exact (measurable_pi_apply i).inv
  measurable_invFun := by
    rw [measurable_pi_iff]
    intro i
    exact (measurable_pi_apply i).inv

/-- Per-coordinate left translation of the four corners by
`g`, as a measurable equivalence. -/
def cornerLeftMulEquiv (g : G) : (Fin 4 → G) ≃ᵐ (Fin 4 → G) where
  toFun a := fun i => g * a i
  invFun a := fun i => g⁻¹ * a i
  left_inv a := by funext i; simp
  right_inv a := by funext i; simp
  measurable_toFun := by
    rw [measurable_pi_iff]
    intro i
    exact measurable_const.mul (measurable_pi_apply i)
  measurable_invFun := by
    rw [measurable_pi_iff]
    intro i
    exact measurable_const.mul (measurable_pi_apply i)

/-- Per-coordinate right translation of the four corners by
`h`, as a measurable equivalence. -/
def cornerRightMulEquiv (h : G) : (Fin 4 → G) ≃ᵐ (Fin 4 → G) where
  toFun a := fun i => a i * h
  invFun a := fun i => a i * h⁻¹
  left_inv a := by funext i; simp [mul_assoc]
  right_inv a := by funext i; simp [mul_assoc]
  measurable_toFun := by
    rw [measurable_pi_iff]
    intro i
    exact (measurable_pi_apply i).mul measurable_const
  measurable_invFun := by
    rw [measurable_pi_iff]
    intro i
    exact (measurable_pi_apply i).mul measurable_const

theorem cornerInvEquiv_apply (a : Fin 4 → G) (i : Fin 4) :
    cornerInvEquiv a i = (a i)⁻¹ := rfl

theorem measurePreserving_cornerInvEquiv :
    MeasurePreserving cornerInvEquiv
      (Measure.pi fun _ : Fin 4 => μG)
      (Measure.pi fun _ : Fin 4 => μG) := by
  refine measurePreserving_pi
    (f := fun (_ : Fin 4) (v : G) => v⁻¹)
    (fun _ : Fin 4 => μG) (fun _ : Fin 4 => μG) fun _ => ?_
  exact Measure.measurePreserving_inv μG

theorem cornerLeftMulEquiv_apply (g : G) (a : Fin 4 → G) (i : Fin 4) :
    cornerLeftMulEquiv g a i = g * a i := rfl

theorem measurePreserving_cornerLeftMulEquiv (g : G) :
    MeasurePreserving (cornerLeftMulEquiv g)
      (Measure.pi fun _ : Fin 4 => μG)
      (Measure.pi fun _ : Fin 4 => μG) := by
  refine measurePreserving_pi
    (f := fun (_ : Fin 4) (v : G) => g * v)
    (fun _ : Fin 4 => μG) (fun _ : Fin 4 => μG) fun _ => ?_
  exact measurePreserving_mul_left μG g

theorem cornerRightMulEquiv_apply (h : G) (a : Fin 4 → G) (i : Fin 4) :
    cornerRightMulEquiv h a i = a i * h := rfl

theorem measurePreserving_cornerRightMulEquiv (h : G) :
    MeasurePreserving (cornerRightMulEquiv h)
      (Measure.pi fun _ : Fin 4 => μG)
      (Measure.pi fun _ : Fin 4 => μG) := by
  refine measurePreserving_pi
    (f := fun (_ : Fin 4) (v : G) => v * h)
    (fun _ : Fin 4 => μG) (fun _ : Fin 4 => μG) fun _ => ?_
  exact measurePreserving_mul_right μG h

/-- Corner-integral substitution: inversion of all corners. -/
theorem cornerIntegral_inv (F : (Fin 4 → G) → ℝ) :
    (∫ a : Fin 4 → G, F (cornerInvEquiv a)
      ∂(Measure.pi fun _ : Fin 4 => μG))
      = ∫ a : Fin 4 → G, F a ∂(Measure.pi fun _ : Fin 4 => μG) :=
  (measurePreserving_cornerInvEquiv μG).integral_comp
    cornerInvEquiv.measurableEmbedding F

/-- Corner-integral substitution: left translation of all
corners by `g`. -/
theorem cornerIntegral_leftMul (g : G) (F : (Fin 4 → G) → ℝ) :
    (∫ a : Fin 4 → G, F (cornerLeftMulEquiv g a)
      ∂(Measure.pi fun _ : Fin 4 => μG))
      = ∫ a : Fin 4 → G, F a ∂(Measure.pi fun _ : Fin 4 => μG) :=
  (measurePreserving_cornerLeftMulEquiv μG g).integral_comp
    (cornerLeftMulEquiv g).measurableEmbedding F

/-- Corner-integral substitution: right translation of all
corners by `h`. -/
theorem cornerIntegral_rightMul (h : G) (F : (Fin 4 → G) → ℝ) :
    (∫ a : Fin 4 → G, F (cornerRightMulEquiv h a)
      ∂(Measure.pi fun _ : Fin 4 => μG))
      = ∫ a : Fin 4 → G, F a ∂(Measure.pi fun _ : Fin 4 => μG) :=
  (measurePreserving_cornerRightMulEquiv μG h).integral_comp
    (cornerRightMulEquiv h).measurableEmbedding F

/-- **The block integrand**: the fourfold product of column
factors at corner values `a`, in `PlaqBlock`'s order
(bottom, right, top, left). -/
noncomputable def plaqIntegrand (P : PlaqDatum N) (β : ℝ)
    (u u' : LayerLink N → G) (a : Fin 4 → G) : ℝ :=
  columnKernel ρ β (a 0) (a 1) (u (plaqEdgeB P)) (u' (plaqEdgeB P)) *
  columnKernel ρ β (a 1) (a 3) (u (plaqEdgeR P)) (u' (plaqEdgeR P)) *
  columnKernel ρ β (a 2) (a 3) (u (plaqEdgeT P)) (u' (plaqEdgeT P)) *
  columnKernel ρ β (a 0) (a 2) (u (plaqEdgeL P)) (u' (plaqEdgeL P))

theorem plaqBlock_eq_integral (P : PlaqDatum N) (β : ℝ)
    (u u' : LayerLink N → G) :
    PlaqBlock μG ρ P β u u'
      = ∫ a : Fin 4 → G, plaqIntegrand ρ P β u u' a
          ∂(Measure.pi fun _ : Fin 4 => μG) :=
  rfl

/-- Pointwise: the integrand at left-translated corners, with
the `u`-data conjugated, is the original integrand. -/
theorem plaqIntegrand_leftMul_conj (P : PlaqDatum N) (β : ℝ)
    (g : G) (u u' : LayerLink N → G) (a : Fin 4 → G) :
    plaqIntegrand ρ P β (fun ℓ => g * u ℓ * g⁻¹) u'
        (cornerLeftMulEquiv g a)
      = plaqIntegrand ρ P β u u' a := by
  unfold plaqIntegrand
  rw [cornerLeftMulEquiv_apply, cornerLeftMulEquiv_apply,
    cornerLeftMulEquiv_apply, cornerLeftMulEquiv_apply,
    columnKernel_leftMul_conj, columnKernel_leftMul_conj,
    columnKernel_leftMul_conj, columnKernel_leftMul_conj]

/-- **Block symmetry — conjugation of the `u`-data**:
conjugating every edge value of `u` by `g` (and leaving `u'`)
does not change the block. Haar change of variables: left
translation of all four corners. -/
theorem plaqBlock_conj_u (P : PlaqDatum N) (β : ℝ) (g : G)
    (u u' : LayerLink N → G) :
    PlaqBlock μG ρ P β (fun ℓ => g * u ℓ * g⁻¹) u'
      = PlaqBlock μG ρ P β u u' := by
  rw [plaqBlock_eq_integral, plaqBlock_eq_integral,
    ← cornerIntegral_leftMul μG g
      (plaqIntegrand ρ P β (fun ℓ => g * u ℓ * g⁻¹) u')]
  apply integral_congr_ae
  exact ae_of_all _ fun a => plaqIntegrand_leftMul_conj ρ P β g u u' a

/-- Pointwise: the integrand at right-translated corners,
with the `u'`-data conjugated by `h⁻¹`, is the original
integrand. -/
theorem plaqIntegrand_rightMul_conj (P : PlaqDatum N) (β : ℝ)
    (h : G) (u u' : LayerLink N → G) (a : Fin 4 → G) :
    plaqIntegrand ρ P β u (fun ℓ => h⁻¹ * u' ℓ * h)
        (cornerRightMulEquiv h a)
      = plaqIntegrand ρ P β u u' a := by
  unfold plaqIntegrand
  rw [cornerRightMulEquiv_apply, cornerRightMulEquiv_apply,
    cornerRightMulEquiv_apply, cornerRightMulEquiv_apply,
    columnKernel_rightMul_conj, columnKernel_rightMul_conj,
    columnKernel_rightMul_conj, columnKernel_rightMul_conj]

/-- **Block symmetry — conjugation of the `u'`-data**:
conjugating every edge value of `u'` by `g` (and leaving `u`)
does not change the block. Haar change of variables: right
translation of all four corners by `g⁻¹`. -/
theorem plaqBlock_conj_u' (P : PlaqDatum N) (β : ℝ) (g : G)
    (u u' : LayerLink N → G) :
    PlaqBlock μG ρ P β u (fun ℓ => g * u' ℓ * g⁻¹)
      = PlaqBlock μG ρ P β u u' := by
  have hform : (fun ℓ => g * u' ℓ * g⁻¹)
      = (fun ℓ => (g⁻¹)⁻¹ * u' ℓ * g⁻¹) := by
    funext ℓ
    simp
  rw [plaqBlock_eq_integral, plaqBlock_eq_integral, hform,
    ← cornerIntegral_rightMul μG g⁻¹
      (plaqIntegrand ρ P β u (fun ℓ => (g⁻¹)⁻¹ * u' ℓ * g⁻¹))]
  apply integral_congr_ae
  exact ae_of_all _ fun a =>
    plaqIntegrand_rightMul_conj ρ P β g⁻¹ u u' a

/-- Pointwise: the integrand at inverted corners, with the
two boundary data exchanged, is the original integrand
(factorwise `columnKernel_inv_swap`). -/
theorem plaqIntegrand_inv_swap (P : PlaqDatum N) (β : ℝ)
    (u u' : LayerLink N → G) (a : Fin 4 → G) :
    plaqIntegrand ρ P β u' u (cornerInvEquiv a)
      = plaqIntegrand ρ P β u u' a := by
  unfold plaqIntegrand
  rw [cornerInvEquiv_apply, cornerInvEquiv_apply,
    cornerInvEquiv_apply, cornerInvEquiv_apply,
    columnKernel_inv_swap, columnKernel_inv_swap,
    columnKernel_inv_swap, columnKernel_inv_swap]

/-- **Block symmetry — exchange of the two arguments**:
`PlaqBlock u u' = PlaqBlock u' u`. Haar change of variables:
inversion of all four corners. -/
theorem plaqBlock_swap (P : PlaqDatum N) (β : ℝ)
    (u u' : LayerLink N → G) :
    PlaqBlock μG ρ P β u u' = PlaqBlock μG ρ P β u' u := by
  rw [plaqBlock_eq_integral, plaqBlock_eq_integral,
    ← cornerIntegral_inv μG (plaqIntegrand ρ P β u' u)]
  apply integral_congr_ae
  exact ae_of_all _ fun a => (plaqIntegrand_inv_swap ρ P β u u' a).symm

/-- **Normalization at `β = 0`**: every column factor is `1`,
so the block is the total mass `1` of the corner probability
measure. -/
theorem plaqBlock_zero (P : PlaqDatum N) (u u' : LayerLink N → G) :
    PlaqBlock μG ρ P 0 u u' = 1 := by
  rw [plaqBlock_eq_integral]
  have h1 : ∀ a : Fin 4 → G, plaqIntegrand ρ P 0 u u' a = 1 := by
    intro a
    unfold plaqIntegrand columnKernel wordDensity
    simp
  rw [integral_congr_ae (ae_of_all _ fun a => h1 a)]
  simp [integral_const, Measure.real]

end CornerSubstitutions

section StratumForm

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **The corner embedding**: the four corners of the
plaquette `P`, as an embedding candidate `Fin 4 → LayerSite N`
in the block's order `(c₀₀, c₁₀, c₀₁, c₁₁)`. -/
def cornerEmb (P : PlaqDatum N) : Fin 4 → LayerSite N :=
  ![plaqCorner00 P, plaqCorner10 P, plaqCorner01 P, plaqCorner11 P]

theorem cornerEmb_zero (P : PlaqDatum N) :
    cornerEmb P 0 = plaqCorner00 P := by
  simp [cornerEmb]

theorem cornerEmb_one (P : PlaqDatum N) :
    cornerEmb P 1 = plaqCorner10 P := by
  simp [cornerEmb]

theorem cornerEmb_two (P : PlaqDatum N) :
    cornerEmb P 2 = plaqCorner01 P := by
  simp [cornerEmb]

theorem cornerEmb_three (P : PlaqDatum N) :
    cornerEmb P 3 = plaqCorner11 P := by
  simp [cornerEmb]

/-- **The corner embedding is injective** at `Even N`,
`4 ≤ N`: the four corners are pairwise distinct, by A2-2a's
corner distinctness lemmas. -/
theorem cornerEmb_injective (hN : Even N) (h4N : 4 ≤ N)
    (P : PlaqDatum N) : Function.Injective (cornerEmb P) := by
  have hcases : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    intro i
    fin_cases i <;> simp
  intro i j hij
  rcases hcases i with rfl | rfl | rfl | rfl <;>
    rcases hcases j with rfl | rfl | rfl | rfl <;>
    simp only [cornerEmb_zero, cornerEmb_one, cornerEmb_two,
      cornerEmb_three] at hij <;>
    first
      | rfl
      | exact absurd hij (plaqCorner10_ne_00 hN h4N P)
      | exact absurd hij.symm (plaqCorner10_ne_00 hN h4N P)
      | exact absurd hij (plaqCorner01_ne_00 hN h4N P)
      | exact absurd hij.symm (plaqCorner01_ne_00 hN h4N P)
      | exact absurd hij (plaqCorner11_ne_00 hN h4N P)
      | exact absurd hij.symm (plaqCorner11_ne_00 hN h4N P)
      | exact absurd hij (plaqCorner10_ne_01 hN h4N P)
      | exact absurd hij.symm (plaqCorner10_ne_01 hN h4N P)
      | exact absurd hij (plaqCorner11_ne_10 hN h4N P)
      | exact absurd hij.symm (plaqCorner11_ne_10 hN h4N P)
      | exact absurd hij (plaqCorner11_ne_01 hN h4N P)
      | exact absurd hij.symm (plaqCorner11_ne_01 hN h4N P)

/-- **The full-stratum form of the block**: the same fourfold
product, integrated over the full corner stratum
`α : LayerSite N → G` (the integrand reads only the four
corner coordinates `α ∘ cornerEmb P`). -/
noncomputable def PlaqBlockStratum (P : PlaqDatum N) (β : ℝ)
    (u u' : LayerLink N → G) : ℝ :=
  ∫ α : LayerSite N → G, plaqIntegrand ρ P β u u' (α ∘ cornerEmb P)
    ∂(Measure.pi fun _ : LayerSite N => μG)

/-- **Full-stratum vs corner-integral form of `PlaqBlock`**
(deliverable 1): the full-stratum integral equals the
corner-integral form registered in A2-2a. The re-basing is
the owned real pi-measure transport `integral_comp_emb_real`
(the `integral_comp_emb` / `integral_pi_restrict` pattern)
along the injective corner embedding. -/
theorem plaqBlockStratum_eq_plaqBlock (hN : Even N) (h4N : 4 ≤ N)
    (P : PlaqDatum N) (β : ℝ) (u u' : LayerLink N → G) :
    PlaqBlockStratum μG ρ P β u u' = PlaqBlock μG ρ P β u u' := by
  unfold PlaqBlockStratum
  rw [plaqBlock_eq_integral]
  exact integral_comp_emb_real μG (cornerEmb P)
    (cornerEmb_injective hN h4N P) (plaqIntegrand ρ P β u u')

/-- The symmetric reading: `PlaqBlock` equals its full-stratum
form. -/
theorem plaqBlock_eq_plaqBlockStratum (hN : Even N) (h4N : 4 ≤ N)
    (P : PlaqDatum N) (β : ℝ) (u u' : LayerLink N → G) :
    PlaqBlock μG ρ P β u u' = PlaqBlockStratum μG ρ P β u u' :=
  (plaqBlockStratum_eq_plaqBlock μG ρ hN h4N P β u u').symm

end StratumForm

section KernelClassInvariance

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- The section intertwines with conjugation: the section at
a conjugate is the pointwise conjugate of the section
(at the bottom edge both read the conjugate; off it, both
read `g * 1 * g⁻¹ = 1`). -/
theorem plaqSection_map_conj (P : PlaqDatum N) (g x : G) :
    plaqSection P (g * x * g⁻¹)
      = fun ℓ => g * plaqSection P x ℓ * g⁻¹ := by
  funext ℓ
  by_cases hℓ : ℓ = plaqEdgeB P <;> simp [plaqSection, hℓ]

/-- **Separate class invariance of Ψ, first argument**
(deliverable 4 — CLOSED): `Ψ (g * x * g⁻¹) y = Ψ x y`, by the
block's `u`-conjugation symmetry (corner left translation). -/
theorem plaqKernel_class_left (P : PlaqDatum N) (β : ℝ)
    (g x y : G) :
    PlaqKernel μG ρ P β (g * x * g⁻¹) y = PlaqKernel μG ρ P β x y := by
  unfold PlaqKernel
  rw [plaqSection_map_conj]
  exact plaqBlock_conj_u μG ρ P β g (plaqSection P x) (plaqSection P y)

/-- **Separate class invariance of Ψ, second argument**
(deliverable 4 — CLOSED): `Ψ x (g * y * g⁻¹) = Ψ x y`, by the
block's `u'`-conjugation symmetry (corner right translation
by `g⁻¹`). -/
theorem plaqKernel_class_right (P : PlaqDatum N) (β : ℝ)
    (g x y : G) :
    PlaqKernel μG ρ P β x (g * y * g⁻¹) = PlaqKernel μG ρ P β x y := by
  unfold PlaqKernel
  rw [plaqSection_map_conj]
  exact plaqBlock_conj_u' μG ρ P β g (plaqSection P x) (plaqSection P y)

/-- **Separate class invariance of Ψ, bundled** in exactly the
shape of the two class conjuncts of the registered
proposition (P) (`PlaqKernelPos` in `PlaquetteTelescoping`):
both close at the change-of-variables level, so neither is
deferred to A2-2d. (The PSD conjunct of (P) is not touched
here; it is A2-2d/e's.) -/
theorem plaqKernel_separately_classFn (P : PlaqDatum N) (β : ℝ) :
    (∀ g x y : G, PlaqKernel μG ρ P β (g * x * g⁻¹) y
      = PlaqKernel μG ρ P β x y)
    ∧ (∀ g x y : G, PlaqKernel μG ρ P β x (g * y * g⁻¹)
      = PlaqKernel μG ρ P β x y) :=
  ⟨fun g x y => plaqKernel_class_left μG ρ P β g x y,
   fun g x y => plaqKernel_class_right μG ρ P β g x y⟩

/-- **Ψ is symmetric**: `Ψ x y = Ψ y x`, from the block's
exchange symmetry (corner inversion). -/
theorem plaqKernel_swap (P : PlaqDatum N) (β : ℝ) (x y : G) :
    PlaqKernel μG ρ P β x y = PlaqKernel μG ρ P β y x := by
  unfold PlaqKernel
  exact plaqBlock_swap μG ρ P β (plaqSection P x) (plaqSection P y)

/-- **Ψ at `β = 0`** is identically `1`. -/
theorem plaqKernel_zero (P : PlaqDatum N) (x y : G) :
    PlaqKernel μG ρ P 0 x y = 1 := by
  unfold PlaqKernel
  exact plaqBlock_zero μG ρ P (plaqSection P x) (plaqSection P y)

end KernelClassInvariance

end ThetLogos
