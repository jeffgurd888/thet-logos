import Mathlib.Tactic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Matrix.PosDef
import ThetLogos.HermitianReduction
import ThetLogos.BridgeMagneticGauge

open scoped InnerProductSpace
open scoped ComplexOrder
open Matrix

/-!
# BridgeMagneticHeat — STEM bridge brick B3: the heat object

*STEM = Spectral–Thermal ElectroMagnetic (Jeff's name, 2026-10-24).*

Brick B3 of the STEM bridge charter
(`whitepaper/stem-bridge-scoping-2026-10-24.md`, statement S2):
the heat object of B1's magnetic Laplacian `L_{w,θ}`. The corpus's
general Hermitian heat engine already exists —
`HermitianReduction.heatKernelGen`, the matrix exponential
`exp (-tK)` of a Hermitian matrix `K`, with its semigroup law
(`heatKernelGen_add`), its spectral form (`heatKernelGen_eq_conj`)
and its trace identity (`heatKernelGen_trace`, the eigenvalue-sum
datum form of `ThermalKernel.heatKernel_trace`). This brick feeds
the engine B1's operator: `magMat w θ` is the matrix of `magLin w θ`
in the canonical basis (proved: its `mulVec` action is `magLap`),
Hermitian under B1's own hypotheses (`magMat_isHermitian`), and

    magHeat w θ t = heatKernelGen (magMat w θ) t = exp (-t • L_{w,θ})

at matrix level — the engine's packaging, followed exactly. On top
of it: the semigroup law, the initial condition, the trace
identity against the datum form, the zero-field sanity (the
matrix's action at `θ ≡ 1` is the exhibit's `laplacianOpC`; the
full weld to `BridgeCompletion.heatOp` is brick B5 and is not
asserted), and B2's deferred corollary: the heat trace depends
only on the gauge class of `θ` (`magHeatTrace_gauge`), through the
matrix gauge conjugation `magMat_gauge` and the engine's
exponential conjugation law `exp_conj_star`. Charter S2's last
clause also lands: `magMat` is positive semidefinite (its
quadratic form is S1's phased energy), so its eigenvalues — the
`λ_k` of the trace identity — are nonnegative
(`magMat_eigenvalues_nonneg`), and for `t ≥ 0` the heat kernel
contracts at the quadratic-form level (`magHeat_contraction`):
in eigenbasis coordinates every mode is damped by
`exp (-t λᵢ) ∈ (0, 1]`.

**NO CLAIM.** Parts of any official (Clay) statement closed: 0.
This is finite graph bookkeeping — a heat semigroup of a finite
matrix. It is **not** Maxwell theory (continuum Maxwell has NO
SEAT in this corpus), not a force-unification claim, not a
torsion claim, and not a modular-flux claim: the bridge's thermal
object is a heat semigroup / heat trace, never a modular flux
(`ModularFlux.magnetophaseFlux_vanishes` stays a kill at T1).

- Status: **VERIFIED — STANDS WHOLE (T1), landed 2026-10-24.**
  The headlines `magHeatTrace_eq`, `magHeatTrace_gauge` and
  `magHeat_contraction` are machine-checked (parent-verified
  rebuild, 3,592 jobs; axioms standard, no `sorryAx`).
  LEVEL MARK, kept: `magHeat_contraction` is contraction at the
  quadratic-form level only — the operator-norm form is not
  asserted in this module. Dossier:
  `whitepaper/stem-bridge-b3-heat-object-2026-10-24.md`.
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. The matrix of the magnetic Laplacian

`magLin w θ` lives on `EuclideanSpace ℂ V`; the heat engine eats
matrices. `magMat w θ` is its matrix in the canonical basis: row
`i` carries the full conductance row-sum on the diagonal and the
phased hopping `-w i j • θ i j` off it — read off `magLap_apply`
term by term. -/

/-- **The matrix of `L_{w,θ}`** in the canonical basis:
`(magMat w θ) i j = (row sum of `w` at `i`, if `j = i`) − w i j •
θ i j`. Tier T2 (definition). -/
def magMat (w : V → V → ℝ) (θ : V → V → Circle) : Matrix V V ℂ :=
  fun i j => (if j = i then ∑ k, (w i k : ℂ) else 0)
    - (w i j : ℂ) * (θ i j : ℂ)

theorem magMat_apply (w : V → V → ℝ) (θ : V → V → Circle) (i j : V) :
    magMat w θ i j = (if j = i then ∑ k, (w i k : ℂ) else 0)
      - (w i j : ℂ) * (θ i j : ℂ) := rfl

/-- **The matrix acts as the operator**: `magMat w θ` multiplies a
potential vector exactly as `magLap w θ` acts on it. This is the
tie between the engine's input and B1's operator — `magMat` is
not *a* matrix resembling `L_{w,θ}`; it is `L_{w,θ}` in
coordinates. -/
theorem magMat_mulVec (w : V → V → ℝ) (θ : V → V → Circle)
    (F : V → ℂ) :
    magMat w θ *ᵥ F = magLap w θ F := by
  funext i
  have hterm : ∀ j : V,
      magMat w θ i j * F j
        = (if j = i then (∑ k, (w i k : ℂ)) * F i else 0)
          - (w i j : ℂ) * ((θ i j : ℂ) * F j) := by
    intro j
    by_cases h : j = i
    · subst h
      simp only [magMat_apply, ite_true, sub_mul, mul_assoc]
    · simp only [magMat_apply, h, ite_false, zero_mul, sub_mul,
        mul_assoc]
  calc (magMat w θ *ᵥ F) i
      = (∑ k, (w i k : ℂ)) * F i
          - ∑ j, (w i j : ℂ) * ((θ i j : ℂ) * F j) := by
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_congr rfl (fun j _ => hterm j),
          Finset.sum_sub_distrib, Finset.sum_ite_eq',
          if_pos (Finset.mem_univ i)]
    _ = magLap w θ F i := by
        rw [magLap_apply, Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [mul_sub]

/-- The matrix tie, operator form: `Matrix.toLin'` of `magMat` is
B1's linear map on plain potentials. -/
theorem magMat_toLin' (w : V → V → ℝ) (θ : V → V → Circle) :
    Matrix.toLin' (magMat w θ) = magLapFun w θ := by
  refine LinearMap.ext fun F => ?_
  rw [Matrix.toLin'_apply]
  exact magMat_mulVec w θ F

/-- **The matrix is Hermitian** under B1's hypotheses (symmetric
conductances, antisymmetric connection) — proved entrywise: the
conjugate of the `(j, i)` entry is the `(i, j)` entry, the
diagonal being a real row-sum and the off-diagonal phases
conjugating to their inverses, which antisymmetry trades back.
Consistent with, and independent of, `magLin_isSymmetric`. -/
theorem magMat_isHermitian (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (θ : V → V → Circle)
    (hθ : ∀ i j, θ j i = (θ i j)⁻¹) :
    (magMat w θ).IsHermitian := by
  have hconj : ∀ x y : V, star ((θ x y : ℂ))
      = (((θ x y)⁻¹ : Circle) : ℂ) := by
    intro x y
    rw [RCLike.star_def, ← Circle.coe_inv_eq_conj]
  show Matrix.conjTranspose (magMat w θ) = magMat w θ
  ext i j
  rw [Matrix.conjTranspose_apply, magMat_apply, magMat_apply]
  by_cases h : i = j
  · subst h
    have hdiag : star ((θ i i : ℂ)) = (θ i i : ℂ) := by
      rw [hconj i i]
      exact congrArg (fun z : Circle => ((z : ℂ))) (hθ i i).symm
    simp only [ite_true, star_sub, star_mul,
      star_sum, Complex.star_def, Complex.conj_ofReal, hdiag]
    rw [mul_comm ((θ i i : ℂ)) ((w i i : ℝ) : ℂ)]
  · have hne : j ≠ i := fun hh => h hh.symm
    have hoff : star ((θ j i : ℂ)) = (θ i j : ℂ) := by
      rw [hconj j i]
      have hinv : (θ j i)⁻¹ = θ i j := by rw [hθ i j, inv_inv]
      exact congrArg (fun z : Circle => ((z : ℂ))) hinv
    simp only [if_neg h, if_neg hne]
    rw [star_sub, star_mul]
    simp only [Complex.star_def, Complex.conj_ofReal, hoff, hw j i,
      map_zero]
    rw [mul_comm ((θ i j : ℂ)) ((w i j : ℝ) : ℂ)]

/-! ## §2. The heat object

The engine's packaging is a matrix exponential; the brick follows
the engine. `magHeat w θ t` is `exp (-t • L_{w,θ})` as a matrix;
its action on a potential is `Matrix.mulVec`. -/

/-- **The magnetic heat kernel** (charter S2's heat object):
`e^{-t L_{w,θ}}`, the corpus heat engine `heatKernelGen` fed with
the matrix of B1's magnetic Laplacian. Tier T2 (definition) —
the theorems about it are the brick. -/
noncomputable def magHeat (w : V → V → ℝ) (θ : V → V → Circle)
    (t : ℝ) : Matrix V V ℂ :=
  heatKernelGen (magMat w θ) t

/-- **The semigroup law** (S2): the magnetic heat kernel composes,
`e^{-(t+s)L} = e^{-tL} * e^{-sL}`. The engine's law
`heatKernelGen_add`, which needs no Hermiticity — recorded
hypothesis-free, as the engine states it. -/
theorem magHeat_add (w : V → V → ℝ) (θ : V → V → Circle)
    (t s : ℝ) :
    magHeat w θ (t + s) = magHeat w θ t * magHeat w θ s :=
  heatKernelGen_add t s

/-- **The initial condition**: at `t = 0` the heat kernel is the
identity matrix — no heat has flowed. -/
theorem magHeat_zero (w : V → V → ℝ) (θ : V → V → Circle) :
    magHeat w θ 0 = 1 := by
  simp [magHeat, heatKernelGen]

/-! ## §3. The heat trace, against its datum form

The charter's question for the trace was datum-or-forged: is
`Tr e^{-tL}` the trace of the constructed object, equal to the
eigenvalue schedule sum the corpus's datum (`ThermalKernel`)
carries — or only a stated definition? Answer, proved below: the
trace is `Matrix.trace` of the constructed kernel, and the
engine's `heatKernelGen_trace` proves it equal to the datum form
at the eigenvalues of `magMat w θ` — which, by §1's tie, are the
eigenvalues of `L_{w,θ}`. Nothing is defined into place. -/

/-- **The magnetic heat trace**: the trace of the constructed
heat kernel. A definition — but §3's theorem is not: it proves
this trace equal to the eigenvalue datum form. -/
noncomputable def magHeatTrace (w : V → V → ℝ) (θ : V → V → Circle)
    (t : ℝ) : ℂ :=
  Matrix.trace (magHeat w θ t)

/-- **The trace identity** (S2): the magnetic heat trace is the
cast of the eigenvalue schedule sum,
`Tr e^{-t L_{w,θ}} = ↑(∑ k, exp (-t • λ_k))`,
with `λ = (magMat w θ)`'s eigenvalues — the datum form of
`ThermalKernel.heatKernel_trace`, transported by the engine's
`heatKernelGen_trace`. Datum, not forged. -/
theorem magHeatTrace_eq (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (θ : V → V → Circle)
    (hθ : ∀ i j, θ j i = (θ i j)⁻¹) (t : ℝ) :
    magHeatTrace w θ t
      = ((∑ i, Real.exp
          (-t * (magMat_isHermitian w hw θ hθ).eigenvalues i) : ℝ)
        : ℂ) := by
  unfold magHeatTrace magHeat
  rw [heatKernelGen_trace (magMat_isHermitian w hw θ hθ) t,
    heatKernel_trace]

/-! ## §4. Zero-field sanity (the cheap half of B5)

At `θ ≡ 1` the heat object is the engine's kernel of the
zero-field operator's matrix, whose action is the exhibit's
`laplacianOpC` verbatim. The identification of this kernel with
`BridgeCompletion.heatOp`'s eigenbasis form is the full weld —
brick B5, not asserted here. -/

/-- At the trivial connection, the matrix's action is the
exhibit's complex plain Laplacian. -/
theorem magMat_one_mulVec (w : V → V → ℝ) (F : V → ℂ) :
    magMat w 1 *ᵥ F = laplacianOpC w F :=
  (magMat_mulVec w 1 F).trans (magLap_one w F)

/-- At the trivial connection, the magnetic heat kernel is the
heat engine's kernel of the zero-field matrix. (The kernel is
*defined* from that matrix at every `θ`; the content here is
§1's weld `magMat_one_mulVec` — the matrix being heated at
`θ ≡ 1` is the exhibit's operator.) -/
theorem magHeat_one (w : V → V → ℝ) (t : ℝ) :
    magHeat w 1 t = heatKernelGen (magMat w 1) t := rfl

/-! ## §5. The gauge corollary B2 deferred

B2 proved the operator conjugation `magLin_gauge` and carried the
spectrum consequence at eigenvalue level; the heat-trace half
was deferred to this brick, on the grounds that once the heat
object exists as a form consuming the operator, the trace
consequence is a corollary. It is: the matrix of the gauged
operator is the diagonal-unitary conjugate of the matrix
(`magMat_gauge`, pure algebra, hypothesis-free like
`magLin_gauge` itself), the exponential conjugates by the
engine's `exp_conj_star`, and the trace cycles. -/

/-- **The matrix gauge unitary**: the diagonal matrix of the
gauge phases — the matrix form of B2's `gaugeOp`. -/
def gaugeMat (g : V → Circle) : Matrix V V ℂ :=
  Matrix.diagonal (fun i => (g i : ℂ))

theorem gaugeMat_star (g : V → Circle) :
    star (gaugeMat g)
      = Matrix.diagonal (fun i => ((g i : ℂ))⁻¹) := by
  ext i j
  rw [Matrix.star_apply]
  by_cases h : i = j
  · subst h
    simp only [gaugeMat, Matrix.diagonal_apply_eq]
    rw [← Circle.coe_inv]
    exact star_circle_coe (g i)
  · have hji : ¬ j = i := fun hh => h hh.symm
    simp only [gaugeMat, Matrix.diagonal_apply, h, hji, ite_false,
      star_zero]

/-- The matrix gauge unitary is unitary, left identity:
`star U * U = 1`. -/
theorem gaugeMat_star_mul_self (g : V → Circle) :
    star (gaugeMat g) * gaugeMat g = 1 := by
  rw [gaugeMat_star, gaugeMat, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  exact inv_mul_cancel₀ (circle_coe_ne_zero (g i))

/-- The matrix gauge unitary is unitary, right identity:
`U * star U = 1`. -/
theorem gaugeMat_mul_star_self (g : V → Circle) :
    gaugeMat g * star (gaugeMat g) = 1 := by
  rw [gaugeMat_star, gaugeMat, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (circle_coe_ne_zero (g i))

/-- **The matrix gauge conjugation**: the matrix of the gauged
magnetic Laplacian is the diagonal-unitary conjugate of the
matrix, `magMat w θ^g = U • magMat w θ • U*` — the matrix shadow
of B2's `magLin_gauge`, and like it pure algebra: no symmetry of
`w`, no antisymmetry of `θ` is spent. Entrywise, the head phase
`g i` and the tail phase `(g j)⁻¹` are exactly the factors
`gaugeConn_coe` puts on the gauged hopping, and on the diagonal
they cancel. -/
theorem magMat_gauge (w : V → V → ℝ) (g : V → Circle)
    (θ : V → V → Circle) :
    magMat w (gaugeConn g θ)
      = gaugeMat g * magMat w θ * star (gaugeMat g) := by
  ext i j
  by_cases h : j = i
  · subst h
    have hg : (g j : ℂ) ≠ 0 := circle_coe_ne_zero (g j)
    simp only [gaugeMat, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Pi.star_apply, magMat_apply,
      gaugeConn_coe, ite_true, Complex.star_def,
      ← Circle.coe_inv_eq_conj, Circle.coe_inv]
    field_simp
  · have hg : (g j : ℂ) ≠ 0 := circle_coe_ne_zero (g j)
    simp only [gaugeMat, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Pi.star_apply, magMat_apply,
      gaugeConn_coe, if_neg h, Complex.star_def,
      ← Circle.coe_inv_eq_conj, Circle.coe_inv]
    field_simp
    ring

/-- **The heat kernel conjugates**: the heat kernel of the gauged
connection is the unitary conjugate of the heat kernel — the
operator-level form of B2's deferred corollary, through the
engine's exponential conjugation law `exp_conj_star`. -/
theorem magHeat_gauge (w : V → V → ℝ) (g : V → Circle)
    (θ : V → V → Circle) (t : ℝ) :
    magHeat w (gaugeConn g θ) t
      = gaugeMat g * magHeat w θ t * star (gaugeMat g) := by
  have hsmul : (-(t : ℂ)) • (gaugeMat g * magMat w θ * star (gaugeMat g))
      = gaugeMat g * ((-(t : ℂ)) • magMat w θ) * star (gaugeMat g) := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul]
  unfold magHeat heatKernelGen
  rw [magMat_gauge, hsmul,
    exp_conj_star _ _ (gaugeMat_star_mul_self g)
      (gaugeMat_mul_star_self g)]

/-- **B2's deferred corollary, landed**: the magnetic heat trace
depends only on the gauge class of `θ` —
`Tr e^{-t L_{w,θ^g}} = Tr e^{-t L_{w,θ}}` for every gauge
transformation `g` and every time `t`. The trace of S3's "hence"
sentence, at the level B2 named: a corollary of the heat object's
conjugation, proved by cycling the trace. -/
theorem magHeatTrace_gauge (w : V → V → ℝ) (g : V → Circle)
    (θ : V → V → Circle) (t : ℝ) :
    magHeatTrace w (gaugeConn g θ) t = magHeatTrace w θ t := by
  unfold magHeatTrace
  rw [magHeat_gauge, Matrix.trace_mul_cycle, gaugeMat_star_mul_self,
    Matrix.one_mul]

/-! ## §6. Spectral positivity (S1's energy, read spectrally)

Charter S2's contraction clause rests on `λ_k(θ) ≥ 0` "by S1".
S1 proved the quadratic form of `L_{w,θ}` is the phased energy;
read through §1's matrix tie, that says `magMat w θ` is positive
semidefinite — and a PSD matrix's eigenvalues are nonnegative.
These are the `λ_k` of §3's trace identity. -/

/-- The quadratic form of the matrix is the phased energy: for
every potential `x`, `star x ⬝ᵥ (magMat w θ *ᵥ x)` is the cast
of `(1/2) • magEnergy w θ x`. B1's energy identity
(`magLin_energy_identity`), read in coordinates through
`magMat_mulVec` and `magBilin`. -/
theorem magMat_dotProduct (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (θ : V → V → Circle)
    (hθ : ∀ i j, θ j i = (θ i j)⁻¹) (x : V → ℂ) :
    star x ⬝ᵥ (magMat w θ *ᵥ x)
      = (((1 / 2 : ℝ) * magEnergy w θ x : ℝ) : ℂ) := by
  calc star x ⬝ᵥ (magMat w θ *ᵥ x)
      = magBilin w θ x x := by
        rw [magMat_mulVec]
        rfl
    _ = ⟪euclEquivC.symm x, magLin w θ (euclEquivC.symm x)⟫_ℂ := by
        rw [inner_magLin_apply, LinearEquiv.apply_symm_apply]
    _ = (((1 / 2 : ℝ) * magEnergy w θ x : ℝ) : ℂ) := by
        rw [magLin_energy_identity w hw θ hθ,
          LinearEquiv.apply_symm_apply]

/-- **`magMat w θ` is positive semidefinite** for nonnegative
symmetric conductances and an antisymmetric connection: its
quadratic form is the phased energy, a nonnegative real. -/
theorem magMat_posSemidef (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (θ : V → V → Circle) (hθ : ∀ i j, θ j i = (θ i j)⁻¹) :
    (magMat w θ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨magMat_isHermitian w hw θ hθ, fun x => ?_⟩
  rw [magMat_dotProduct w hw θ hθ x]
  exact RCLike.ofReal_nonneg.mpr
    (mul_nonneg (by norm_num) (magEnergy_nonneg w hw0 θ x))

/-- **The spectrum is nonnegative** (S2's `λ_k(θ) ≥ 0`): every
eigenvalue of `magMat w θ` — every `λ_k` in §3's trace
identity — is a nonnegative real. -/
theorem magMat_eigenvalues_nonneg (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (θ : V → V → Circle) (hθ : ∀ i j, θ j i = (θ i j)⁻¹) (i : V) :
    0 ≤ (magMat_isHermitian w hw θ hθ).eigenvalues i :=
  Matrix.PosSemidef.eigenvalues_nonneg
    (magMat_posSemidef w hw hw0 θ hθ) i

/-! ## §7. Contraction (S2's last clause)

For `t ≥ 0` the heat semigroup contracts: its quadratic form is
squeezed between `0` and the identity's. The proof is the
spectral form of §6 read in the eigenbasis: in the coordinates
`y = U* x` of `magMat`'s eigenvector unitary, the heated form is
`∑ i, exp (-t λᵢ) ‖yᵢ‖²` — every mode damped by a factor in
`(0, 1]`, since `λᵢ ≥ 0` (§6) and `t ≥ 0` — while the unheated
form is `∑ i, ‖yᵢ‖²`. Stated at the quadratic-form level, which
is the level the corpus's engine carries; the operator-norm
form is the same mathematics one Cauchy–Schwarz away and is not
separately asserted. -/

/-- The eigenvector unitary's adjunction for the dot product:
moving `U` across `⬝ᵥ` costs a `star` on the other side. -/
theorem eigenvectorUnitary_star_dotProduct (K : Matrix V V ℂ)
    (hK : K.IsHermitian) (x z : V → ℂ) :
    star x ⬝ᵥ ((hK.eigenvectorUnitary : Matrix V V ℂ) *ᵥ z)
      = star ((star (hK.eigenvectorUnitary : Matrix V V ℂ)) *ᵥ x)
        ⬝ᵥ z := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]

/-- The unheated quadratic form, in eigenbasis coordinates:
`star x ⬝ᵥ x = ∑ i, ‖yᵢ‖²` for `y = U* x` — the unitary change
of coordinates preserves the total. -/
theorem heatKernelGen_quadraticForm_norm (K : Matrix V V ℂ)
    (hK : K.IsHermitian) (x : V → ℂ) :
    star x ⬝ᵥ x
      = ((∑ i, ‖((star (hK.eigenvectorUnitary : Matrix V V ℂ))
          *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := by
  calc star x ⬝ᵥ x
      = star ((star (hK.eigenvectorUnitary : Matrix V V ℂ)) *ᵥ x)
          ⬝ᵥ ((star (hK.eigenvectorUnitary : Matrix V V ℂ)) *ᵥ x) := by
        rw [← eigenvectorUnitary_star_dotProduct K hK x,
          Matrix.mulVec_mulVec, ← Unitary.coe_star,
          Unitary.coe_mul_star_self, Matrix.one_mulVec]
    _ = ((∑ i, ‖((star (hK.eigenvectorUnitary : Matrix V V ℂ))
          *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := by
        simp only [dotProduct, Pi.star_apply]
        rw [Complex.ofReal_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]

/-- The heated quadratic form, in eigenbasis coordinates:
`star x ⬝ᵥ (e^{-tK} *ᵥ x) = ∑ i, exp (-t λᵢ) ‖yᵢ‖²` — the
trace identity's computation one vector at a time (the trace is
this sum over the standard basis, by §3's route). -/
theorem heatKernelGen_quadraticForm_eq (K : Matrix V V ℂ)
    (hK : K.IsHermitian) (t : ℝ) (x : V → ℂ) :
    star x ⬝ᵥ (heatKernelGen K t *ᵥ x)
      = ((∑ i, Real.exp (-t * hK.eigenvalues i)
          * ‖((star (hK.eigenvectorUnitary : Matrix V V ℂ))
            *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := by
  calc star x ⬝ᵥ (heatKernelGen K t *ᵥ x)
      = star ((star (hK.eigenvectorUnitary : Matrix V V ℂ)) *ᵥ x)
          ⬝ᵥ (hermitianDiagKernel hK.eigenvalues t
            *ᵥ ((star (hK.eigenvectorUnitary : Matrix V V ℂ))
              *ᵥ x)) := by
        rw [heatKernelGen_eq_conj hK t, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec,
          eigenvectorUnitary_star_dotProduct K hK x]
    _ = ((∑ i, Real.exp (-t * hK.eigenvalues i)
          * ‖((star (hK.eigenvectorUnitary : Matrix V V ℂ))
            *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := by
        have hD : hermitianDiagKernel hK.eigenvalues t
              *ᵥ ((star (hK.eigenvectorUnitary : Matrix V V ℂ)) *ᵥ x)
            = fun i => ((Real.exp (-t * hK.eigenvalues i) : ℝ) : ℂ)
              * ((star (hK.eigenvectorUnitary : Matrix V V ℂ))
                *ᵥ x) i := by
          funext i
          exact Matrix.mulVec_diagonal _ _ i
        rw [hD]
        simp only [dotProduct, Pi.star_apply]
        rw [Complex.ofReal_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Complex.ofReal_mul]
        have hconj : star (((star (hK.eigenvectorUnitary
              : Matrix V V ℂ)) *ᵥ x) i)
            * (((star (hK.eigenvectorUnitary : Matrix V V ℂ))
              *ᵥ x) i)
            = ((‖((star (hK.eigenvectorUnitary : Matrix V V ℂ))
              *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.star_def, Complex.ofReal_pow]
          exact Complex.conj_mul' _
        rw [← hconj]
        ring

/-- **Contraction** (S2, at the quadratic-form level): for
`t ≥ 0`, nonnegative symmetric conductances and an
antisymmetric connection, the magnetic heat kernel's quadratic
form is nonnegative and dominated by the identity's:
`0 ≤ ⟪x, e^{-tL} x⟫ ∧ ⟪x, e^{-tL} x⟫ ≤ ⟪x, x⟫`, read through
the real parts (both forms are real, by §6's identity and its
heated analogue). Every mode is damped by `exp (-t λᵢ) ∈ (0, 1]`
and none is amplified or sign-flipped. -/
theorem magHeat_contraction (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (θ : V → V → Circle) (hθ : ∀ i j, θ j i = (θ i j)⁻¹)
    (ht : 0 ≤ t) (x : V → ℂ) :
    0 ≤ (star x ⬝ᵥ (magHeat w θ t *ᵥ x)).re ∧
      (star x ⬝ᵥ (magHeat w θ t *ᵥ x)).re
        ≤ (star x ⬝ᵥ x).re := by
  unfold magHeat
  rw [heatKernelGen_quadraticForm_eq (magMat w θ)
      (magMat_isHermitian w hw θ hθ) t x,
    heatKernelGen_quadraticForm_norm (magMat w θ)
      (magMat_isHermitian w hw θ hθ) x]
  simp only [Complex.ofReal_re]
  constructor
  · apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (Real.exp_nonneg _) (by positivity)
  · apply Finset.sum_le_sum
    intro i _
    have hdi : 0 ≤ (magMat_isHermitian w hw θ hθ).eigenvalues i :=
      magMat_eigenvalues_nonneg w hw hw0 θ hθ i
    have hexp : Real.exp
        (-t * (magMat_isHermitian w hw θ hθ).eigenvalues i) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      rw [neg_mul]
      exact neg_nonpos.mpr (mul_nonneg ht hdi)
    exact mul_le_of_le_one_left (by positivity) hexp

end ThetLogos
