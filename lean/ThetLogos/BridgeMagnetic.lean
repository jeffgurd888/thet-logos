import Mathlib.Tactic
import Mathlib.Analysis.Complex.Circle
import ThetLogos.BridgeCompletion

open scoped InnerProductSpace

/-!
# BridgeMagnetic — STEM bridge brick B1: the magnetic graph Laplacian

*STEM = Spectral–Thermal ElectroMagnetic (Jeff's name, 2026-10-24).*

**NO CLAIM.** This module is brick **B1** of the STEM bridge scoped in
`whitepaper/stem-bridge-scoping-2026-10-24.md`. It builds the joining
object of that charter's Seat 1: the **magnetic graph Laplacian**
`L_{w,θ}` on the Bridge exhibit's own graph — the exhibit's real
conductances `w` unchanged, a U(1) connection `θ` (Circle-valued, with
the reverse edge carrying the inverse phase) seated in the Ohm factor,
and complex potentials. It proves the charter's statement **S1**:
self-adjointness of the operator on `EuclideanSpace ℂ V`, the phased
energy identity, and positivity for nonnegative conductances. It also
proves the *definitional* zero-field weld: at `θ ≡ 1`, `magLap` is the
complex form of the exhibit's `laplacianOp` (the full weld S5, with
eigenvalues and heat content, is brick B5 and is not asserted here).

**Fences (charter §5, on the face).** This is finite graph bookkeeping:
a U(1) connection on a finite graph and an operator on a finite
dimensional space. It is **not** Maxwell theory (continuum Maxwell has
NO SEAT in this corpus), not a force-unification claim, not a torsion
claim, and not a modular-flux claim — the killed EM-torsion paste, the
killed "strong nuclear = electromagnetic" identification, and the
killed magnetophase flux (`ModularFlux.magnetophaseFlux_vanishes`)
stay killed. Parts of any official Clay statement closed by this
module: **0**.

Conventions follow the exhibit (`BridgeLaplacian`): the drop of a
potential along `(i, j)` is read at the head, `dropVec F i j = F j - F i`;
here the covariant drop transports `F i` to `j` before comparing.
`θ a b` is the phase of transport from `b` to `a`, so the antisymmetry
hypothesis reads `θ j i = (θ i j)⁻¹`.

- Status: **VERIFIED — STANDS WHOLE (T1), landed 2026-10-24.**
  The charter's S1 is machine-checked: the magnetic Laplacian
  `magLap w θ`, the factorization `magLap_eq_diverge_ohm_drop`,
  S1a `magLin_isSymmetric`, S1b `magBilin_identity` /
  `magLin_energy_identity`, positivity (`magEnergy_nonneg`,
  `magLin_energy_nonneg`), and the definitional zero-field weld
  `magLap_one` (parent-verified rebuild, 3,320 jobs; 24 strict;
  axioms standard, no `sorryAx`). Dossier:
  `whitepaper/stem-bridge-b1-magnetic-laplacian-2026-10-24.md`.
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. The connection in the bridge: phased drop, Ohm, divergence

The exhibit's three maps (`dropVec` / `ohm` / `diverge`) ported to `ℂ`,
with the connection seated in the drop (equivalently, after the
factorization theorem of §2, in the Ohm factor of the composite). -/

/-- The covariant drop of a complex potential `F` along the edge
`(i, j)`: the value at `j` minus the value at `i` parallel-transported
to `j` along the connection. At `θ ≡ 1` this is the exhibit's
`dropVec` read over `ℂ`. -/
def magDrop (θ : V → V → Circle) (F : V → ℂ) (i j : V) : ℂ :=
  F j - (θ j i : ℂ) * F i

/-- Ohm's law over `ℂ`: multiply an edge function by the (real,
cast) conductance. -/
def ohmC (w : V → V → ℝ) (X : V → V → ℂ) (i j : V) : ℂ :=
  (w i j : ℂ) * X i j

/-- The Ohm flow of a potential under the connection: conductance
times covariant drop. -/
def magFlow (w : V → V → ℝ) (θ : V → V → Circle) (F : V → ℂ) :
    V → V → ℂ :=
  ohmC w (magDrop θ F)

/-- The divergence (return crossing `dᵀ`) over `ℂ`: sum an edge
function back to the nodes, gathering the transposed entries. -/
def divergeC (X : V → V → ℂ) (i : V) : ℂ := ∑ j, X j i

/-- **The magnetic graph Laplacian** (the STEM bridge's joining
operator): `(magLap w θ F) i = ∑ j, w i j • (F i − θ i j • F j)` —
the exhibit's `laplacianOp` with the drop at each edge twisted by the
connection. -/
def magLap (w : V → V → ℝ) (θ : V → V → Circle) (F : V → ℂ) (i : V) :
    ℂ :=
  ∑ j, (w i j : ℂ) * (F i - (θ i j : ℂ) * F j)

theorem magDrop_apply (θ : V → V → Circle) (F : V → ℂ) (i j : V) :
    magDrop θ F i j = F j - (θ j i : ℂ) * F i := rfl

theorem ohmC_apply (w : V → V → ℝ) (X : V → V → ℂ) (i j : V) :
    ohmC w X i j = (w i j : ℂ) * X i j := rfl

theorem magFlow_apply (w : V → V → ℝ) (θ : V → V → Circle)
    (F : V → ℂ) (i j : V) :
    magFlow w θ F i j = (w i j : ℂ) * (F j - (θ j i : ℂ) * F i) := rfl

theorem divergeC_apply (X : V → V → ℂ) (i : V) :
    divergeC X i = ∑ j, X j i := rfl

theorem magLap_apply (w : V → V → ℝ) (θ : V → V → Circle)
    (F : V → ℂ) (i : V) :
    magLap w θ F i = ∑ j, (w i j : ℂ) * (F i - (θ i j : ℂ) * F j) :=
  rfl

/-! ## §2. The factorization `L_{w,θ} = dᵀ σ d`, and the zero-field weld

As in the exhibit, the factorization spends the symmetry of `w` (the
divergence gathers transposed entries); the connection's
antisymmetry is *not* needed here — it is spent in §4, on the energy. -/

/-- **The bridge factorization, phased.** The magnetic Laplacian is
the composite of the three separately defined maps: covariant drop
(`d`), Ohm factor (`σ`), divergence (`dᵀ`). -/
theorem magLap_eq_diverge_ohm_drop (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (θ : V → V → Circle) (F : V → ℂ) :
    magLap w θ F = divergeC (ohmC w (magDrop θ F)) := by
  funext i
  simp only [magLap_apply, divergeC_apply, ohmC_apply, magDrop_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (w j i : ℂ) = (w i j : ℂ) by exact_mod_cast (hw j i)]

/-- The factorization with the magnetic Ohm flow named:
`L_{w,θ} F = dᵀ (flow of F)`. -/
theorem magLap_eq_diverge_flow (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (θ : V → V → Circle) (F : V → ℂ) :
    magLap w θ F = divergeC (magFlow w θ F) :=
  magLap_eq_diverge_ohm_drop w hw θ F

/-- The complex form of the exhibit's plain Laplacian:
`(laplacianOpC w F) i = ∑ j, w i j • (F i − F j)` over `ℂ`. -/
def laplacianOpC (w : V → V → ℝ) (F : V → ℂ) (i : V) : ℂ :=
  ∑ j, (w i j : ℂ) * (F i - F j)

/-- **Definitional zero-field weld.** At the trivial connection,
`magLap` is definitionally the complex plain Laplacian. (The full
weld S5 — eigenvalues `lapEig`, heat content `heatOp` — is brick B5;
this is the definition check pulled forward, per charter §6/B5's
admission rule A2.) -/
theorem magLap_one (w : V → V → ℝ) (F : V → ℂ) :
    magLap w 1 F = laplacianOpC w F := by
  funext i
  simp only [magLap_apply, laplacianOpC, Pi.one_apply, Circle.coe_one,
    one_mul]

/-- The complex plain Laplacian of a real potential is the cast of
the exhibit's `laplacianOp`: the weld to the landed exhibit,
verbatim. -/
theorem laplacianOpC_ofReal (w : V → V → ℝ) (f : V → ℝ) (i : V) :
    laplacianOpC w (fun j => (f j : ℂ)) i
      = ((laplacianOp w f i : ℝ) : ℂ) := by
  simp only [laplacianOpC, laplacianOp_apply, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

/-! ## §3. The operator on `EuclideanSpace ℂ V`

Packaged exactly as the exhibit packages `laplacianOp`: a linear map
on plain potentials, transported to the Euclidean space by
conjugation with the canonical identification. -/

/-- Linearity of `magLap` in the potential (additivity). -/
theorem magLap_add (w : V → V → ℝ) (θ : V → V → Circle)
    (F G : V → ℂ) :
    magLap w θ (F + G) = magLap w θ F + magLap w θ G := by
  funext i
  simp only [magLap_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Linearity of `magLap` in the potential (scaling). -/
theorem magLap_smul (w : V → V → ℝ) (θ : V → V → Circle) (c : ℂ)
    (F : V → ℂ) :
    magLap w θ (c • F) = c • magLap w θ F := by
  funext i
  simp only [magLap_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- `magLap w θ` as a linear map on plain complex potentials. -/
def magLapFun (w : V → V → ℝ) (θ : V → V → Circle) :
    (V → ℂ) →ₗ[ℂ] (V → ℂ) where
  toFun := magLap w θ
  map_add' := magLap_add w θ
  map_smul' := magLap_smul w θ

/-- The canonical identification of the Euclidean space of complex
potentials with plain potentials (the `BridgeCompletion.euclEquiv`
pattern, over `ℂ`). -/
def euclEquivC : EuclideanSpace ℂ V ≃ₗ[ℂ] (V → ℂ) :=
  WithLp.linearEquiv 2 ℂ (V → ℂ)

/-- **The magnetic Laplacian as an operator** on
`EuclideanSpace ℂ V`: `magLap w θ` transported by `euclEquivC`. -/
def magLin (w : V → V → ℝ) (θ : V → V → Circle) :
    EuclideanSpace ℂ V →ₗ[ℂ] EuclideanSpace ℂ V :=
  euclEquivC.symm.conj (magLapFun w θ)

/-- Transport identity: `euclEquivC` after `magLin` recovers
`magLap` on plain potentials. -/
theorem equiv_magLin (w : V → V → ℝ) (θ : V → V → Circle)
    (F : EuclideanSpace ℂ V) :
    euclEquivC (magLin w θ F) = magLap w θ (euclEquivC F) := rfl

/-- Component form of the transport identity. -/
theorem magLin_apply (w : V → V → ℝ) (θ : V → V → Circle)
    (F : EuclideanSpace ℂ V) (i : V) :
    (magLin w θ F) i = magLap w θ (euclEquivC F) i := rfl

/-- The Euclidean inner product over `ℂ`, in coordinates. -/
theorem euclid_inner_applyC (X Y : EuclideanSpace ℂ V) :
    ⟪X, Y⟫_ℂ = ∑ i, (starRingEnd ℂ) (X i) * Y i := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [RCLike.inner_apply]
  exact mul_comm _ _

/-- The (sesquilinear) energy pairing of the magnetic Laplacian on
plain potentials: `magBilin w θ F G = ⟪G, magLap w θ F⟫` in
coordinates. -/
def magBilin (w : V → V → ℝ) (θ : V → V → Circle) (F G : V → ℂ) :
    ℂ :=
  ∑ i, (starRingEnd ℂ) (G i) * magLap w θ F i

/-- The operator pairing is the bilinear form: for Euclidean
potentials `X Y`, `⟪X, magLin w θ Y⟫ = magBilin w θ (eucl Y) (eucl X)`. -/
theorem inner_magLin_apply (w : V → V → ℝ) (θ : V → V → Circle)
    (X Y : EuclideanSpace ℂ V) :
    ⟪X, magLin w θ Y⟫_ℂ
      = magBilin w θ (euclEquivC Y) (euclEquivC X) := by
  rw [euclid_inner_applyC]
  rfl

/-! ## §4. S1 — the polarized identity and self-adjointness

The ℂ form of the exhibit's symmetrization (`bilin_identity`): the
pairing expands once, and the swapped copy of the sum is the *same*
sum — the antisymmetry of the connection, in the form
`conj (θ i j) = θ j i`, is what identifies the cross terms. -/

/-- Conjugation of a connection phase is the reverse phase: for a
Circle-valued connection with `θ j i = (θ i j)⁻¹`,
`conj (θ i j) = θ j i` in `ℂ`. -/
theorem starRingEnd_circle_coe (θ : V → V → Circle)
    (hθ : ∀ i j, θ j i = (θ i j)⁻¹) (i j : V) :
    (starRingEnd ℂ) ((θ i j : ℂ)) = ((θ j i : Circle) : ℂ) := by
  have h := (Circle.coe_inv_eq_conj (θ i j)).symm.trans
    (Circle.coe_inv (θ i j))
  rw [hθ i j, Circle.coe_inv]
  exact h

/-- A connection phase times its reverse is `1` in `ℂ`:
`θ j i • θ i j = 1` — the unitarity the energy identity spends on
its diagonal cross terms. -/
theorem circle_coe_mul_rev (θ : V → V → Circle)
    (hθ : ∀ i j, θ j i = (θ i j)⁻¹) (i j : V) :
    ((θ j i : Circle) : ℂ) * ((θ i j : Circle) : ℂ) = 1 := by
  rw [← Circle.coe_mul, hθ i j, inv_mul_cancel, Circle.coe_one]

/-- **The phased polarized identity (S1, form).** Twice the pairing
`⟪G, L_{w,θ} F⟫` is the conductance-weighted sum of the phased drop
products `conj (G i − θ i j • G j) • (F i − θ i j • F j)` — the
exhibit's `bilin_identity` with phases. The symmetrization is the
content: the cross terms are identified by swapping the sum and
spending `w`'s symmetry and `conj (θ i j) = θ j i`. -/
theorem magBilin_identity (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (θ : V → V → Circle)
    (hθ : ∀ i j, θ j i = (θ i j)⁻¹) (F G : V → ℂ) :
    2 * magBilin w θ F G
      = ∑ i, ∑ j, (w i j : ℂ)
          * ((starRingEnd ℂ) (G i - (θ i j : ℂ) * G j)
            * (F i - (θ i j : ℂ) * F j)) := by
  have hA : magBilin w θ F G
      = ∑ i, ∑ j, (w i j : ℂ)
          * ((starRingEnd ℂ) (G i) * (F i - (θ i j : ℂ) * F j)) := by
    simp only [magBilin, magLap_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hS : (∑ i, ∑ j, (w i j : ℂ)
        * ((starRingEnd ℂ) (G i - (θ i j : ℂ) * G j)
          * (F i - (θ i j : ℂ) * F j)))
      = (∑ i, ∑ j, (w i j : ℂ)
          * ((starRingEnd ℂ) (G i) * (F i - (θ i j : ℂ) * F j)))
        + ∑ i, ∑ j, (w i j : ℂ)
          * ((starRingEnd ℂ) (G j) * (F j - (θ j i : ℂ) * F i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [map_sub, map_mul, starRingEnd_circle_coe θ hθ]
    linear_combination
      (↑(w i j) * (starRingEnd ℂ) (G j) * F j) * circle_coe_mul_rev θ hθ i j
  have hB : (∑ i, ∑ j, (w i j : ℂ)
        * ((starRingEnd ℂ) (G j) * (F j - (θ j i : ℂ) * F i)))
      = ∑ i, ∑ j, (w i j : ℂ)
          * ((starRingEnd ℂ) (G i) * (F i - (θ i j : ℂ) * F j)) := by
    calc (∑ i, ∑ j, (w i j : ℂ)
          * ((starRingEnd ℂ) (G j) * (F j - (θ j i : ℂ) * F i)))
        = ∑ i, ∑ j, (w j i : ℂ)
          * ((starRingEnd ℂ) (G i) * (F i - (θ i j : ℂ) * F j)) :=
          Finset.sum_comm
      _ = ∑ i, ∑ j, (w i j : ℂ)
          * ((starRingEnd ℂ) (G i) * (F i - (θ i j : ℂ) * F j)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [show (w j i : ℂ) = (w i j : ℂ) by
            exact_mod_cast (hw j i)]
  rw [hS, hB, ← hA]
  ring

/-- The pairing is Hermitian-symmetric: conjugating the pairing
swaps the two potentials. -/
theorem magBilin_conj (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (θ : V → V → Circle)
    (hθ : ∀ i j, θ j i = (θ i j)⁻¹) (F G : V → ℂ) :
    (starRingEnd ℂ) (magBilin w θ F G) = magBilin w θ G F := by
  have h1 := magBilin_identity w hw θ hθ F G
  have h2 := magBilin_identity w hw θ hθ G F
  have key : (starRingEnd ℂ) (2 * magBilin w θ F G)
      = 2 * magBilin w θ G F := by
    rw [h1, h2]
    simp only [map_sum, map_mul, map_sub, starRingEnd_self_apply,
      starRingEnd_circle_coe θ hθ]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [map_mul, Complex.conj_ofReal]
    ring
  have h2ne : (2 : ℂ) ≠ 0 := two_ne_zero
  have key' : (2 : ℂ) * (starRingEnd ℂ) (magBilin w θ F G)
      = (2 : ℂ) * magBilin w θ G F := by
    have e : (2 : ℂ) * (starRingEnd ℂ) (magBilin w θ F G)
        = (starRingEnd ℂ) (2 * magBilin w θ F G) := by
      rw [map_mul, map_ofNat]
    rw [e]
    exact key
  exact mul_left_cancel₀ h2ne key'

/-- **Self-adjointness (S1).** For symmetric conductances and an
antisymmetric connection, the magnetic Laplacian is a symmetric
(self-adjoint) operator on `EuclideanSpace ℂ V`. The hypotheses are
the exhibit's own (`w` symmetric) plus the connection's
antisymmetry — both hold at `θ ≡ 1`, so nothing here excludes the
zero-field case. -/
theorem magLin_isSymmetric (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (θ : V → V → Circle)
    (hθ : ∀ i j, θ j i = (θ i j)⁻¹) :
    (magLin w θ).IsSymmetric := by
  intro X Y
  calc ⟪(magLin w θ) X, Y⟫_ℂ
      = (starRingEnd ℂ) ⟪Y, (magLin w θ) X⟫_ℂ := by
        rw [inner_conj_symm]
    _ = (starRingEnd ℂ) (magBilin w θ (euclEquivC X) (euclEquivC Y)) := by
        rw [inner_magLin_apply]
    _ = magBilin w θ (euclEquivC Y) (euclEquivC X) :=
        magBilin_conj w hw θ hθ _ _
    _ = ⟪X, (magLin w θ) Y⟫_ℂ := (inner_magLin_apply w θ X Y).symm

/-! ## §5. S1 — the phased energy identity and positivity

The diagonal of the polarized identity: the quadratic form of
`L_{w,θ}` is the phased Dirichlet energy — half the
conductance-weighted sum of the squared covariant drops. -/

/-- **The phased Dirichlet energy** of a complex potential:
`∑ i j, w i j • |F i − θ i j • F j|²`, with `|·|²` read as
`Complex.normSq`. The exhibit's energy with phases. -/
def magEnergy (w : V → V → ℝ) (θ : V → V → Circle) (F : V → ℂ) :
    ℝ :=
  ∑ i, ∑ j, w i j * Complex.normSq (F i - (θ i j : ℂ) * F j)

/-- The phased energy is nonnegative for nonnegative conductances
(no symmetry needed — the sum is termwise nonnegative). -/
theorem magEnergy_nonneg (w : V → V → ℝ)
    (hw0 : ∀ i j, 0 ≤ w i j) (θ : V → V → Circle) (F : V → ℂ) :
    0 ≤ magEnergy w θ F := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (hw0 i j) (Complex.normSq_nonneg _)

/-- The diagonal of the polarized identity, as a real quantity:
the pairing of `F` against `L_{w,θ} F` is `1/2` of the phased
energy, cast to `ℂ`. -/
theorem magBilin_self (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (θ : V → V → Circle)
    (hθ : ∀ i j, θ j i = (θ i j)⁻¹) (F : V → ℂ) :
    magBilin w θ F F
      = (((1 / 2 : ℝ) * magEnergy w θ F : ℝ) : ℂ) := by
  have h := magBilin_identity w hw θ hθ F F
  have hT : (∑ i, ∑ j, (w i j : ℂ)
        * ((starRingEnd ℂ) (F i - (θ i j : ℂ) * F j)
          * (F i - (θ i j : ℂ) * F j)))
      = ((magEnergy w θ F : ℝ) : ℂ) := by
    rw [magEnergy, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Complex.ofReal_mul]
    congr 1
    rw [mul_comm]
    exact Complex.mul_conj _
  have h2 : (2 : ℂ) * magBilin w θ F F
      = ((magEnergy w θ F : ℝ) : ℂ) := h.trans hT
  have hE : (((1 / 2 : ℝ) * magEnergy w θ F : ℝ) : ℂ)
      = (2 : ℂ)⁻¹ * ((magEnergy w θ F : ℝ) : ℂ) := by
    push_cast
    norm_num
  rw [hE, ← h2, inv_mul_cancel_left₀ two_ne_zero]

/-- **The phased energy identity (S1).** On `EuclideanSpace ℂ V`,
`⟪F, L_{w,θ} F⟫ = (1/2) • (phased energy of F)` — the diagonal of
`magBilin_identity`, transported to the operator. In particular the
quadratic form is real. -/
theorem magLin_energy_identity (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (θ : V → V → Circle)
    (hθ : ∀ i j, θ j i = (θ i j)⁻¹) (F : EuclideanSpace ℂ V) :
    ⟪F, magLin w θ F⟫_ℂ
      = (((1 / 2 : ℝ) * magEnergy w θ (euclEquivC F) : ℝ) : ℂ) := by
  rw [inner_magLin_apply, magBilin_self w hw θ hθ]

/-- **Positivity (S1).** For nonnegative symmetric conductances, the
quadratic form of `L_{w,θ}` is nonnegative — read in `ℂ` via the
energy identity, which exhibits it as a nonnegative real. -/
theorem magLin_energy_nonneg (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (θ : V → V → Circle) (hθ : ∀ i j, θ j i = (θ i j)⁻¹)
    (F : EuclideanSpace ℂ V) :
    0 ≤ (⟪F, magLin w θ F⟫_ℂ).re := by
  rw [magLin_energy_identity w hw θ hθ F, Complex.ofReal_re]
  exact mul_nonneg (by norm_num) (magEnergy_nonneg w hw0 θ _)

end ThetLogos
