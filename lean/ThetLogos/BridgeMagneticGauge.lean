import Mathlib.Tactic
import Mathlib.Analysis.Complex.Circle
import ThetLogos.BridgeMagnetic

open scoped InnerProductSpace

/-!
# BridgeMagneticGauge — STEM bridge brick B2: gauge covariance

*STEM = Spectral–Thermal ElectroMagnetic (Jeff's name, 2026-10-24).*

**NO CLAIM.** This module is brick **B2** of the STEM bridge scoped in
`whitepaper/stem-bridge-scoping-2026-10-24.md`. It proves the
charter's statement **S3**: the magnetic graph Laplacian of brick B1
(`BridgeMagnetic`) is gauge-covariant. For a vertex gauge
transformation `g : V → Circle`, the conjugated connection is
`θ^g i j = g i * θ i j * (g j)⁻¹` and the diagonal unitary is
`(U_g F) i = g i • F i`; the headline is the operator identity
`magLin w θ^g = U_g ∘ₗ magLin w θ ∘ₗ U_g*` on `EuclideanSpace ℂ V`,
where `U_g*` is carried as the diagonal operator of the inverse
phases and proved to be the adjoint (two-sided inverse + the
adjoint's defining inner-product identity). Corollaries at the level
the corpus carries: the phased Dirichlet energy is gauge-invariant,
and `μ` is an eigenvalue of `L_{w,θ^g}` iff it is one of `L_{w,θ}`.
(The heat-trace half of S3's "hence" belongs to brick B3, whose
object does not exist yet; it is not asserted here.)

**Fences (charter §5, on the face).** This is finite graph
bookkeeping: a U(1) connection on a finite graph and an operator on
a finite-dimensional space. It is **not** Maxwell theory (continuum
Maxwell has NO SEAT in this corpus), not a force-unification claim,
not a torsion claim, and not a modular-flux claim — the killed
EM-torsion paste, the killed "strong nuclear = electromagnetic"
identification, and the killed magnetophase flux
(`ModularFlux.magnetophaseFlux_vanishes`) stay killed. Parts of any
official Clay statement closed by this module: **0**.

Conventions follow B1: `θ a b` is the phase of transport from `b`
to `a`, the connection hypothesis is `θ j i = (θ i j)⁻¹`, and
operators on `EuclideanSpace ℂ V` are packaged by conjugation with
`euclEquivC`, exactly as `magLin` is. The convention for `θ^g` is
forced by the charter's `U_g`: the intertwining
`L_{θ^g} ∘ U_g = U_g ∘ L_θ` holds termwise iff
`θ^g i j * g j = g i * θ i j` (proved as `gaugeConn_mul`).

- Status: **VERIFIED — STANDS WHOLE (T1), landed 2026-10-24.**
  The headline `magLin_gauge` and the corollaries
  `magEnergy_gauge`, `magLin_gauge_hasEigenvalue` are
  machine-checked (parent-verified rebuild, 3,321 jobs;
  axioms standard, no `sorryAx`). Dossier:
  `whitepaper/stem-bridge-b2-gauge-covariance-2026-10-24.md`.
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. The gauge action on connections

A gauge transformation `g : V → Circle` acts on a connection by
conjugation at the endpoints. Circle is abelian, so the action
preserves the connection antisymmetry `θ j i = (θ i j)⁻¹` — B1's
theorems therefore apply verbatim to the transformed connection. -/

/-- **The conjugated connection** `θ^g`: transport along `(i, j)`
first picks up the gauge phase at the head `i`, crosses with `θ`,
and drops the gauge phase at the tail `j`. In B1's convention
(`θ a b` = phase of transport from `b` to `a`) this is the unique
form for which `L_{θ^g} ∘ U_g = U_g ∘ L_θ` — see `gaugeConn_mul`. -/
noncomputable def gaugeConn (g : V → Circle) (θ : V → V → Circle)
    (i j : V) : Circle :=
  g i * θ i j * (g j)⁻¹

theorem gaugeConn_apply (g : V → Circle) (θ : V → V → Circle)
    (i j : V) :
    gaugeConn g θ i j = g i * θ i j * (g j)⁻¹ := rfl

/-- The coercion of the conjugated connection to `ℂ`, factor by
factor. -/
theorem gaugeConn_coe (g : V → Circle) (θ : V → V → Circle)
    (i j : V) :
    ((gaugeConn g θ i j : Circle) : ℂ)
      = (g i : ℂ) * (θ i j : ℂ) * ((g j : ℂ))⁻¹ := by
  simp only [gaugeConn_apply, Circle.coe_mul, Circle.coe_inv]

/-- **The key identity** (in `Circle`): the conjugated phase,
followed by the gauge phase at the tail, is the gauge phase at the
head followed by the original phase. This is what makes the
intertwining close termwise. -/
theorem gaugeConn_mul (g : V → Circle) (θ : V → V → Circle)
    (i j : V) :
    gaugeConn g θ i j * g j = g i * θ i j := by
  show g i * θ i j * (g j)⁻¹ * g j = g i * θ i j
  rw [mul_assoc (g i * θ i j) ((g j)⁻¹) (g j), inv_mul_cancel,
    mul_one]

/-- The key identity read in `ℂ`. -/
theorem gaugeConn_coe_mul (g : V → Circle) (θ : V → V → Circle)
    (i j : V) :
    ((gaugeConn g θ i j : Circle) : ℂ) * (g j : ℂ)
      = (g i : ℂ) * (θ i j : ℂ) := by
  rw [← Circle.coe_mul, gaugeConn_mul, Circle.coe_mul]

/-- **The gauge action preserves connection antisymmetry** (S3's
admission ticket): if `θ j i = (θ i j)⁻¹` for all `i j`, so does
`θ^g`. Hence B1's self-adjointness and energy identity apply to
`L_{w,θ^g}` unchanged. -/
theorem gaugeConn_antisymm (g : V → Circle) (θ : V → V → Circle)
    (hθ : ∀ i j, θ j i = (θ i j)⁻¹) :
    ∀ i j, gaugeConn g θ j i = (gaugeConn g θ i j)⁻¹ := by
  intro i j
  calc gaugeConn g θ j i
      = g j * (θ i j)⁻¹ * (g i)⁻¹ := by
        rw [gaugeConn_apply, hθ i j]
    _ = (g i * θ i j * (g j)⁻¹)⁻¹ := by
        rw [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc]
    _ = (gaugeConn g θ i j)⁻¹ := by
        rw [gaugeConn_apply]

/-- The trivial gauge transformation acts trivially. -/
theorem gaugeConn_one (θ : V → V → Circle) :
    gaugeConn 1 θ = θ := by
  funext i j
  simp [gaugeConn_apply]

/-- A coerced Circle phase is nonzero in `ℂ` (it has norm `1`). -/
theorem circle_coe_ne_zero (z : Circle) : (z : ℂ) ≠ 0 := by
  intro h
  have hn := Circle.norm_coe z
  rw [h, norm_zero] at hn
  exact one_ne_zero hn.symm

/-- Conjugation of a coerced phase is the coerced inverse phase:
`conj z = z⁻¹` on the circle, in the `starRingEnd` form B1 uses. -/
theorem star_circle_coe (z : Circle) :
    (starRingEnd ℂ) (z : ℂ) = ((z⁻¹ : Circle) : ℂ) :=
  (Circle.coe_inv_eq_conj z).symm

/-! ## §2. The diagonal unitary `U_g`

Packaged exactly as B1 packages `magLin`: a linear map on plain
potentials, transported to `EuclideanSpace ℂ V` by conjugation with
`euclEquivC`. The adjoint `U_g*` is the diagonal operator of the
inverse phases; §2 proves it is the adjoint in both senses the
corpus needs: it is a two-sided inverse of `U_g`, and it satisfies
the adjoint's defining inner-product identity. -/

/-- The diagonal gauge map on plain complex potentials:
`(U_g F) i = g i • F i`. -/
def gaugeDiag (g : V → Circle) : (V → ℂ) →ₗ[ℂ] (V → ℂ) where
  toFun := fun F i => (g i : ℂ) * F i
  map_add' := by
    intro F G
    funext i
    simp [mul_add]
  map_smul' := by
    intro c F
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem gaugeDiag_apply (g : V → Circle) (F : V → ℂ) (i : V) :
    gaugeDiag g F i = (g i : ℂ) * F i := rfl

/-- Component form of the canonical identification: reading a
Euclidean potential through `euclEquivC` changes nothing at a
vertex. -/
theorem euclEquivC_apply (F : EuclideanSpace ℂ V) (i : V) :
    euclEquivC F i = F i := rfl

/-- **The diagonal unitary** `U_g` on `EuclideanSpace ℂ V`:
`gaugeDiag g` transported by `euclEquivC`, the `magLin` pattern. -/
def gaugeOp (g : V → Circle) :
    EuclideanSpace ℂ V →ₗ[ℂ] EuclideanSpace ℂ V :=
  euclEquivC.symm.conj (gaugeDiag g)

/-- Transport identity: `euclEquivC` after `gaugeOp` recovers
`gaugeDiag` on plain potentials. -/
theorem equiv_gaugeOp (g : V → Circle) (F : EuclideanSpace ℂ V) :
    euclEquivC (gaugeOp g F) = gaugeDiag g (euclEquivC F) := rfl

/-- Component form of the diagonal unitary: `(U_g F) i = g i • F i`,
the charter's defining formula. -/
theorem gaugeOp_apply (g : V → Circle) (F : EuclideanSpace ℂ V)
    (i : V) :
    (gaugeOp g F) i = (g i : ℂ) * F i := rfl

/-- The inverse phases undo the gauge phases, applied pointwise:
`U_g (U_g⁻¹ F) = F`. -/
theorem gaugeOp_gaugeOpInv_apply (g : V → Circle)
    (F : EuclideanSpace ℂ V) :
    gaugeOp g (gaugeOp (fun i => (g i)⁻¹) F) = F := by
  ext i
  simp only [gaugeOp_apply]
  rw [← mul_assoc, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one,
    one_mul]

/-- The gauge phases undo the inverse phases, applied pointwise:
`U_g⁻¹ (U_g F) = F`. -/
theorem gaugeOpInv_gaugeOp_apply (g : V → Circle)
    (F : EuclideanSpace ℂ V) :
    gaugeOp (fun i => (g i)⁻¹) (gaugeOp g F) = F := by
  ext i
  simp only [gaugeOp_apply]
  rw [← mul_assoc, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one,
    one_mul]

/-- `U_g*` is a two-sided inverse of `U_g`, operator form:
`U_g ∘ₗ U_g* = 1`. -/
theorem gaugeOp_comp_gaugeOpInv (g : V → Circle) :
    gaugeOp g ∘ₗ gaugeOp (fun i => (g i)⁻¹) = 1 := by
  apply LinearMap.ext
  intro F
  rw [LinearMap.comp_apply]
  exact gaugeOp_gaugeOpInv_apply g F

/-- `U_g*` is a two-sided inverse of `U_g`, operator form:
`U_g* ∘ₗ U_g = 1`. -/
theorem gaugeOpInv_comp_gaugeOp (g : V → Circle) :
    gaugeOp (fun i => (g i)⁻¹) ∘ₗ gaugeOp g = 1 := by
  apply LinearMap.ext
  intro F
  rw [LinearMap.comp_apply]
  exact gaugeOpInv_gaugeOp_apply g F

/-- **`U_g*` is the adjoint of `U_g`**: it satisfies the adjoint's
defining identity `⟪U_g X, Y⟫ = ⟪X, U_g* Y⟫` for all `X Y` (the
adjoint on a Hilbert space is unique, so this characterizes it). -/
theorem gaugeOp_adjoint (g : V → Circle)
    (X Y : EuclideanSpace ℂ V) :
    ⟪gaugeOp g X, Y⟫_ℂ
      = ⟪X, gaugeOp (fun i => (g i)⁻¹) Y⟫_ℂ := by
  rw [euclid_inner_applyC, euclid_inner_applyC]
  apply Finset.sum_congr rfl
  intro i _
  simp only [gaugeOp_apply, map_mul, star_circle_coe]
  ring

/-! ## §3. S3 — the conjugation identity

The intertwining is pure algebra: no symmetry of `w` and no
antisymmetry of `θ` is spent. At vertex `i`, the transformed
operator's sum is the gauge phase `g i` times the original sum at
the inverse-transformed potential; the two gauge phases at `i`
cancel and `gaugeConn_coe_mul` identifies the phase at each edge. -/

/-- **The intertwining, component form.** At every vertex, the
magnetic Laplacian of the conjugated connection agrees with the
gauge conjugate of the original magnetic Laplacian. -/
theorem magLin_gauge_apply (w : V → V → ℝ) (g : V → Circle)
    (θ : V → V → Circle) (F : EuclideanSpace ℂ V) (i : V) :
    (magLin w (gaugeConn g θ) F) i
      = (gaugeOp g (magLin w θ (gaugeOp (fun i => (g i)⁻¹) F))) i := by
  simp only [gaugeOp_apply, magLin_apply, magLap_apply,
    equiv_gaugeOp, gaugeDiag_apply, euclEquivC_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Circle.coe_inv, gaugeConn_coe]
  field_simp [circle_coe_ne_zero (g i), circle_coe_ne_zero (g j)]

/-- **Gauge covariance (S3).** The magnetic Laplacian of the
conjugated connection is the diagonal-unitary conjugate of the
original magnetic Laplacian:
`L_{w,θ^g} = U_g ∘ₗ L_{w,θ} ∘ₗ U_g*`, with `U_g*` the
inverse-phase diagonal operator of §2 (proved there to be the
adjoint and a two-sided inverse of `U_g`). -/
theorem magLin_gauge (w : V → V → ℝ) (g : V → Circle)
    (θ : V → V → Circle) :
    magLin w (gaugeConn g θ)
      = gaugeOp g ∘ₗ magLin w θ ∘ₗ gaugeOp (fun i => (g i)⁻¹) := by
  apply LinearMap.ext
  intro F
  apply PiLp.ext
  intro i
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  exact magLin_gauge_apply w g θ F i

/-! ## §4. Corollaries at the level the corpus carries

The spectrum of `L_{w,θ}` depends only on the gauge class of `θ`:
stated here as eigenvalue transport (an eigenvalue of one side is
an eigenvalue of the other, with the eigenvector carried by `U_g`)
plus invariance of the phased Dirichlet energy — the quadratic form
whose spectrum S3 speaks of. The heat-trace consequence of S3
waits for brick B3's heat object and is not asserted. -/

/-- B1's self-adjointness, transported along the gauge action for
free: `L_{w,θ^g}` is symmetric whenever `L_{w,θ}`'s hypotheses
hold, because `θ^g` still satisfies the antisymmetry hypothesis
(`gaugeConn_antisymm`). -/
theorem magLin_gaugeConn_isSymmetric (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (g : V → Circle)
    (θ : V → V → Circle) (hθ : ∀ i j, θ j i = (θ i j)⁻¹) :
    (magLin w (gaugeConn g θ)).IsSymmetric :=
  magLin_isSymmetric w hw _ (gaugeConn_antisymm g θ hθ)

/-- **The phased Dirichlet energy is gauge-invariant**: gauging the
connection and the potential together does not change the energy.
Termwise, the twisted difference at `(i, j)` is `g i` times the
original twisted difference (`gaugeConn_coe_mul`), and a phase has
`normSq` one. -/
theorem magEnergy_gauge (w : V → V → ℝ) (g : V → Circle)
    (θ : V → V → Circle) (F : V → ℂ) :
    magEnergy w (gaugeConn g θ) (fun i => (g i : ℂ) * F i)
      = magEnergy w θ F := by
  unfold magEnergy
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  have hnorm : Complex.normSq (g i : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Circle.norm_coe]
    norm_num
  have hfactor : (g i : ℂ) * F i
        - ((gaugeConn g θ i j : Circle) : ℂ) * ((g j : ℂ) * F j)
      = (g i : ℂ) * (F i - (θ i j : ℂ) * F j) := by
    rw [← mul_assoc, gaugeConn_coe_mul]
    ring
  rw [hfactor, Complex.normSq_mul, hnorm, one_mul]

/-- **The spectrum is gauge-invariant** (corpus form): `μ` is an
eigenvalue of `L_{w,θ^g}` iff it is an eigenvalue of `L_{w,θ}`.
Eigenvectors are transported by the diagonal unitary and back by
its inverse, via `magLin_gauge`. -/
theorem magLin_gauge_hasEigenvalue (w : V → V → ℝ) (g : V → Circle)
    (θ : V → V → Circle) (μ : ℂ) :
    Module.End.HasEigenvalue (magLin w (gaugeConn g θ)) μ
      ↔ Module.End.HasEigenvalue (magLin w θ) μ := by
  have hcomp : ∀ x : EuclideanSpace ℂ V,
      magLin w (gaugeConn g θ) x
        = gaugeOp g (magLin w θ (gaugeOp (fun i => (g i)⁻¹) x)) := by
    intro x
    rw [magLin_gauge]
    simp only [LinearMap.comp_apply]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    have hmem : magLin w (gaugeConn g θ) v = μ • v :=
      Module.End.HasEigenvector.apply_eq_smul hv
    have hne : gaugeOp (fun i => (g i)⁻¹) v ≠ 0 := by
      intro hz
      apply (Module.End.hasEigenvector_iff.mp hv).2
      have hcan := gaugeOp_gaugeOpInv_apply g v
      rw [hz, map_zero] at hcan
      exact hcan.symm
    have hmem' : magLin w θ (gaugeOp (fun i => (g i)⁻¹) v)
        = μ • gaugeOp (fun i => (g i)⁻¹) v := by
      calc magLin w θ (gaugeOp (fun i => (g i)⁻¹) v)
          = gaugeOp (fun i => (g i)⁻¹)
              (magLin w (gaugeConn g θ) v) := by
            rw [hcomp v, gaugeOpInv_gaugeOp_apply]
        _ = gaugeOp (fun i => (g i)⁻¹) (μ • v) := by rw [hmem]
        _ = μ • gaugeOp (fun i => (g i)⁻¹) v := map_smul _ _ _
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr hmem', hne⟩)
  · intro h
    obtain ⟨u, hu⟩ := h.exists_hasEigenvector
    have hmem : magLin w θ u = μ • u :=
      Module.End.HasEigenvector.apply_eq_smul hu
    have hne : gaugeOp g u ≠ 0 := by
      intro hz
      apply (Module.End.hasEigenvector_iff.mp hu).2
      have hcan := gaugeOpInv_gaugeOp_apply g u
      rw [hz, map_zero] at hcan
      exact hcan.symm
    have hmem' : magLin w (gaugeConn g θ) (gaugeOp g u)
        = μ • gaugeOp g u := by
      calc magLin w (gaugeConn g θ) (gaugeOp g u)
          = gaugeOp g (magLin w θ
              (gaugeOp (fun i => (g i)⁻¹) (gaugeOp g u))) := hcomp _
        _ = gaugeOp g (magLin w θ u) := by
            rw [gaugeOpInv_gaugeOp_apply]
        _ = gaugeOp g (μ • u) := by rw [hmem]
        _ = μ • gaugeOp g u := map_smul _ _ _
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr hmem', hne⟩)

end ThetLogos
