/-
# PartnerThermal — TAB-1: the Partner thermal seat

**TAB-1 of the thermal-acoustic bridge line
(~/workspace/your_files/thermal-acoustic-bridge-scope-2026-11-11.md
§5). NO CLAIM. Dial-ineligible. NO physics claim.**

TAB-0 (`ThermalAcousticPin`) recorded the bridge: the
temperature–frequency correspondence STANDS at the
diagonal seat under its owned statements. TAB-2
(`ResonanceTransport`) carried the frequency law to
general Hermitian generators. TAB-1 is the remaining
seat: the AxiomTet Partner Hamiltonians
(`AxiomTetPartner.vertexHam` / `edgeHam`, with SP-5's
spectral correspondence in `AxiomTetPartnerIso`) read
thermally.

What "read thermally" means here, exactly:

1. **The Gibbs form at a general seat** — `gibbsForm`,
   the FlowKernel pin's right side named, at an
   arbitrary finite index type (§1), with its
   Hermiticity, positivity and trace facts.
2. **The KMS property of the Gibbs form** (§2): for a
   Hermitian generator `H` over a nonempty index,
   `IsKMSFlow (gibbsForm H β) H β` — the Gibbs ⟹ KMS
   direction of the finite correspondence, in
   `FlowKernel`'s own vocabulary (§§2–3). (This is also AQFT-1's
   brick C; it is proved once, here, and cited there.
   The bare pin `FlowKernel.kms_iff_gibbs` is FALSE —
   refuted in `FlowKernelKMS` (K-AQFT1-FORM); the
   correspondence holds at Hermitian generators, which
   is the form proved here.)
3. **The Partner seats** (§4): the vertex and edge
   Hamiltonians complexified, their Gibbs forms, and
   their Hermiticity — the vertex/edge matrices are
   `Dᴴ * D` / `D * Dᴴ` forms, Hermitian by construction.
4. **The thermal reading of SP-5** (§5): the resonance
   (gap) sets of the two Partner Gibbs generators agree
   wherever SP-5's spectral correspondence reaches —
   stated as the conditional identity the correspondence
   supports, with the zero-sector hypothesis named.

Nothing here is a claim about heat, sound, or any
physical system; "thermal" names the Gibbs/KMS
vocabulary of the corpus, nothing more. **K-TAB-DIAL
stands. K-TAB-SEAT is the armed kill for this module:
if a Partner seat cannot carry the Gibbs form in the
corpus's own vocabulary, the failure is reported, not
papered over.**

Build note (disclosed, 2026-11-13): brick 1's first
build exposed three latent defects in the draft's
star computations, all repaired without touching
any statement — the scalar star on ℂ is bridged by
`Complex.star_def` (not a `starRingEnd` rewrite,
whose pattern the elaborated term does not carry);
the factored spectral form closes by unfolding
`hermitianDiagKernel` before the diagonal rewrite
(the kernel def is semireducible, so the rewrite's
closing rfl cannot see through it); and the Gibbs
scalar's star-fixedness is proved through the
positive-real cast (`RCLike.ofReal_inv`), the
draft's bare `simp` having unfolded the trace sum
instead of closing.

Build note (brick 5, 2026-11-13): the §5 route is
polynomial, not spectral-theorem-first. SP-5's charpoly
identity is transported along `Complex.ofReal`
(`Matrix.charpoly_map`; the draft's bare-`ofReal` /
`⇑ofRealHom` mismatch is bridged by a definitional
`rfl` step), nonzero roots are read off by evaluation
at the root, and eigenvalue membership is bridged by
`spectrum_eq_image_range` and
`mem_spectrum_iff_isRoot_charpoly`. The gap-set
identity itself is conditional on the zero-sector
hypothesis — both seats carry the zero mode — named
in `resonanceSpectrum_partnerSeats_eq`.

STATUS: STATUS-TAB1.md.
-/

import Mathlib
import ThetLogos.FlowKernel
import ThetLogos.KMSBridge
import ThetLogos.HermitianReduction
import ThetLogos.ResonanceSpectrum
import ThetLogos.ResonanceTransport
import ThetLogos.AxiomTetPartner
import ThetLogos.AxiomTetPartnerIso

namespace ThetLogos

open Matrix
-- Brick-3 environment repair (disclosed, 2026-11-13):
-- `Matrix.PosSemidef` over `ℂ` needs `ℂ`'s partial
-- order, which this Mathlib pin keeps as the scoped
-- instance `Complex.partialOrder`
-- (`Mathlib/Analysis/Complex/Order.lean`), available
-- only under `open scoped ComplexOrder`. No statement
-- is changed by this line; §§1–2 do not use the order.
open scoped ComplexOrder

variable {m : Type*} [Fintype m] [DecidableEq m]

/-! ## §1 — the Gibbs form at a general seat -/

/-- The Gibbs form at generator `H` and inverse
temperature `β`: `(Tr exp(-βH))⁻¹ • exp(-βH)` — the
`FlowKernel` pin's right side, named. (Also the
definition `FlowKernelKMS` cites; there is one
`gibbsForm` in the tree and it lives here.) -/
noncomputable def gibbsForm (H : Matrix m m ℂ) (β : ℝ) :
    Matrix m m ℂ :=
  (trace (NormedSpace.exp ((-(β:ℂ)) • H)))⁻¹
    • NormedSpace.exp ((-(β:ℂ)) • H)

/-- The Gibbs exponential of a Hermitian generator is
Hermitian: `star (exp A) = exp (star A)`
(`NormedSpace.star_exp`), and the Gibbs exponent
`-(β:ℂ) • H` is star-fixed when `H` is Hermitian (the
scalar is a negated real cast, star-fixed). -/
theorem gibbsExp_isHermitian {H : Matrix m m ℂ}
    (hH : H.IsHermitian) (β : ℝ) :
    (NormedSpace.exp ((-(β:ℂ)) • H)).IsHermitian := by
  have hstarH : star H = H := by
    rw [Matrix.star_eq_conjTranspose]; exact hH
  have hE : star ((-(β:ℂ)) • H) = (-(β:ℂ)) • H := by
    rw [star_smul, hstarH]
    congr 1
    rw [star_neg, Complex.star_def,
      Complex.conj_ofReal]
  show (NormedSpace.exp ((-(β:ℂ)) • H))ᴴ
    = NormedSpace.exp ((-(β:ℂ)) • H)
  rw [← Matrix.star_eq_conjTranspose, NormedSpace.star_exp,
    hE]

/-- The Gibbs exponential in spectral form: the
unitary conjugate of the diagonal heat kernel
(`HermitianReduction.hermitianDiagKernel`) — TAB-2's
`exp_smul_conj_diag` with the eigenvalue exponentials
read as real exponentials. Factored once; the trace
computation (§1) and the positivity transport (§2b)
both consume this form. -/
theorem gibbsExp_eq_conj_diagK {H : Matrix m m ℂ}
    (hH : H.IsHermitian) (β : ℝ) :
    NormedSpace.exp ((-(β:ℂ)) • H)
      = (hH.eigenvectorUnitary : Matrix m m ℂ)
        * hermitianDiagKernel hH.eigenvalues β
        * star (hH.eigenvectorUnitary : Matrix m m ℂ) := by
  have hdiag : (fun i => Complex.exp
        ((-(β:ℂ)) * (hH.eigenvalues i : ℂ)))
      = (fun i => ((Real.exp ((-β) * hH.eigenvalues i)
          : ℝ) : ℂ)) := by
    funext i
    have harg : (-(β:ℂ)) * (hH.eigenvalues i : ℂ)
        = (((-β) * hH.eigenvalues i : ℝ) : ℂ) := by
      push_cast; ring
    rw [harg]
    exact (Complex.ofReal_exp _).symm
  rw [exp_smul_conj_diag hH (-(β:ℂ))]
  unfold hermitianDiagKernel
  rw [hdiag]

/-- The trace of the Gibbs exponential is the cast of
a positive-real sum of exponentials of the eigenvalues
— the factored spectral form
(`gibbsExp_eq_conj_diagK`) plus
`HermitianReduction.trace_conj_diagKernel`. (The
statement's `-(β * λ)` and the kernel's `(-β) * λ`
are identified by `neg_mul` at the last step.) -/
theorem gibbsTraceExp_eq {H : Matrix m m ℂ}
    (hH : H.IsHermitian) (β : ℝ) :
    trace (NormedSpace.exp ((-(β:ℂ)) • H))
      = ((∑ i, Real.exp (-(β * hH.eigenvalues i)) : ℝ) : ℂ) := by
  rw [gibbsExp_eq_conj_diagK hH β,
    trace_conj_diagKernel _ (Unitary.coe_star_mul_self _) _ _]
  simp only [neg_mul]

/-- The eigenvalue sum in `gibbsTraceExp_eq` is a
positive real (a nonempty sum of positive terms). -/
theorem gibbsTraceExp_pos {H : Matrix m m ℂ}
    (hH : H.IsHermitian) (β : ℝ) [Nonempty m] :
    0 < ∑ i, Real.exp (-(β * hH.eigenvalues i)) :=
  Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

/-- The Gibbs form of a Hermitian generator is
Hermitian: its scalar `(Tr exp(-βH))⁻¹` is the inverse
of a positive real cast (`gibbsTraceExp_eq`,
`gibbsTraceExp_pos`), hence star-fixed, and the
exponential is Hermitian by `gibbsExp_isHermitian`. -/
theorem gibbsForm_isHermitian {H : Matrix m m ℂ}
    (hH : H.IsHermitian) (β : ℝ) [Nonempty m] :
    (gibbsForm H β).IsHermitian := by
  have htr := gibbsTraceExp_eq hH β
  have hscalar : star
      ((trace (NormedSpace.exp ((-(β:ℂ)) • H)))⁻¹)
      = (trace (NormedSpace.exp ((-(β:ℂ)) • H)))⁻¹ := by
    rw [htr, star_inv₀, Complex.star_def,
      Complex.conj_ofReal]
  rw [gibbsForm, Matrix.IsHermitian,
    Matrix.conjTranspose_smul, hscalar,
    (gibbsExp_isHermitian hH β).eq]

/-- The Gibbs form has trace one (the normalization
is the definition, plus the trace's nonvanishing from
`gibbsTraceExp_pos`). -/
theorem gibbsForm_trace {H : Matrix m m ℂ}
    (hH : H.IsHermitian) (β : ℝ) [Nonempty m] :
    trace (gibbsForm H β) = 1 := by
  have htr := gibbsTraceExp_eq hH β
  have hpos := gibbsTraceExp_pos hH β
  have hne : ((∑ i, Real.exp (-(β * hH.eigenvalues i)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  rw [gibbsForm, Matrix.trace_smul, smul_eq_mul, htr,
    inv_mul_cancel₀ hne]

/-! ## §2 — the Gibbs form is KMS (the flowAction API
and the weight computation)

The API lemmas are `FlowKernel`-general; they live
here because TAB-1's KMS lemma consumes them first,
and `FlowKernelKMS` (AQFT-1) cites them. -/

/-- Scalar multiples of the generator commute with the
generator (index-general form of
`KMSBridge.commute_smul_K`). -/
theorem flowAction_commute_smul (H : Matrix m m ℂ) (z : ℂ) :
    Commute (z • H) H :=
  Commute.smul_left (Commute.refl H) z

/-- The exponentials of commuting scalar multiples
multiply by adding parameters. -/
theorem flowAction_exp_smul_add (H : Matrix m m ℂ) (z w : ℂ) :
    NormedSpace.exp ((z + w) • H)
      = NormedSpace.exp (z • H) * NormedSpace.exp (w • H) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _
    ((flowAction_commute_smul H z).smul_right w)

/-- Exponentials of scalar multiples of one generator
commute with each other. -/
theorem flowAction_exp_smul_commute (H : Matrix m m ℂ) (z w : ℂ) :
    Commute (NormedSpace.exp (z • H)) (NormedSpace.exp (w • H)) := by
  have h := flowAction_exp_smul_add H z w
  have h' := flowAction_exp_smul_add H w z
  rw [add_comm w z] at h'
  exact h.symm.trans h'

/-- The flow at parameter zero is the identity action. -/
theorem flowAction_zero (H : Matrix m m ℂ) (B : Matrix m m ℂ) :
    flowAction H 0 B = B := by
  unfold flowAction
  simp

/-- **The group law at complex parameters:**
`flowAction H (z + w) = flowAction H z ∘ flowAction H w`.
`FlowKernel` lands the real group law
(`flow_group_law`); this is the complex-parameter form
the KMS condition consumes (its parameter is
`t + β·I`). -/
theorem flowAction_add (H : Matrix m m ℂ) (z w : ℂ) (B : Matrix m m ℂ) :
    flowAction H (z + w) B = flowAction H z (flowAction H w B) := by
  classical
  unfold flowAction
  have hcomm1 : Commute ((Complex.I * z) • H) ((Complex.I * w) • H) := by
    apply Commute.smul_right
    apply Commute.smul_left
    exact Commute.refl H
  have hcomm2 : Commute ((-Complex.I * z) • H) ((-Complex.I * w) • H) := by
    apply Commute.smul_right
    apply Commute.smul_left
    exact Commute.refl H
  have e1 : NormedSpace.exp ((Complex.I * (z + w)) • H)
      = NormedSpace.exp ((Complex.I * z) • H)
        * NormedSpace.exp ((Complex.I * w) • H) := by
    rw [mul_add, add_smul]
    exact Matrix.exp_add_of_commute _ _ hcomm1
  have e2 : NormedSpace.exp ((-Complex.I * (z + w)) • H)
      = NormedSpace.exp ((-Complex.I * w) • H)
        * NormedSpace.exp ((-Complex.I * z) • H) := by
    have hs : -Complex.I * (z + w)
        = -Complex.I * w + -Complex.I * z := by ring
    rw [hs]
    exact flowAction_exp_smul_add H _ _
  rw [e1, e2]
  simp only [Matrix.mul_assoc]

/-- The flow is an algebra action:
`flowAction H z (A * B) = flowAction H z A * flowAction H z B`
(the sandwich's middle factors cancel by the exp group
law at inverse parameters). -/
theorem flowAction_mul (H : Matrix m m ℂ) (z : ℂ)
    (A B : Matrix m m ℂ) :
    flowAction H z (A * B) = flowAction H z A * flowAction H z B := by
  classical
  unfold flowAction
  have hcancel : NormedSpace.exp ((-Complex.I * z) • H)
      * NormedSpace.exp ((Complex.I * z) • H) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _
      (Commute.smul_right (Commute.smul_left (Commute.refl H) _) _)]
    simp
  have key : (NormedSpace.exp ((Complex.I * z) • H) * (A * B)
        * NormedSpace.exp ((-Complex.I * z) • H))
      = (NormedSpace.exp ((Complex.I * z) • H) * A
        * NormedSpace.exp ((-Complex.I * z) • H))
        * (NormedSpace.exp ((Complex.I * z) • H) * B
        * NormedSpace.exp ((-Complex.I * z) • H)) := by
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc
      (NormedSpace.exp ((Complex.I * z) • H) * A)
      (NormedSpace.exp ((-Complex.I * z) • H))
      (NormedSpace.exp ((Complex.I * z) • H)), hcancel,
      Matrix.mul_one]
  exact key

/-- **Imaginary time:** at the purely imaginary
parameter `z = (β:ℂ) * I`, the flow is the Gibbs
sandwich `exp(-βH) * B * exp(βH)` — note the
orientation: `I * (β·I) = -β`, so the LEFT factor is
the Gibbs exponential itself. This is the identity the
KMS weight computation consumes: with
`G = c • exp(-βH)`, the right factor `exp(βH)` meets
`exp(-βH)` under the trace and cancels it. -/
theorem flowAction_I_mul (H : Matrix m m ℂ) (β : ℝ) (B : Matrix m m ℂ) :
    flowAction H ((β:ℂ) * Complex.I) B
      = NormedSpace.exp ((-(β:ℂ)) • H) * B
        * NormedSpace.exp ((β:ℂ) • H) := by
  unfold flowAction
  congr 1
  · congr 2
    rw [show Complex.I * ((β:ℂ) * Complex.I) = (-(β:ℂ)) by
      rw [mul_comm Complex.I, mul_assoc]
      simp]
  · congr 2
    rw [show -Complex.I * ((β:ℂ) * Complex.I) = (β:ℂ) by
      rw [mul_comm (-Complex.I), mul_assoc]
      simp]

/-! ## §2b — positivity and the density property -/

/-- The Gibbs exponential is positive semidefinite:
spectrally it is `U * D * Uᴴ` with `D` the diagonal of
positive real exponentials (`Matrix.PosSemidef.diagonal`
+ the conjugation closure
`Matrix.PosSemidef.mul_mul_conjTranspose_same`). -/
theorem gibbsExp_posSemidef {H : Matrix m m ℂ}
    (hH : H.IsHermitian) (β : ℝ) :
    (NormedSpace.exp ((-(β:ℂ)) • H)).PosSemidef := by
  have hD : (hermitianDiagKernel hH.eigenvalues β).PosSemidef := by
    unfold hermitianDiagKernel
    apply Matrix.PosSemidef.diagonal
    rw [Pi.le_def]
    intro i
    simp only [Pi.zero_apply]
    exact RCLike.ofReal_nonneg.mpr (Real.exp_nonneg _)
  have h := hD.mul_mul_conjTranspose_same
    (hH.eigenvectorUnitary : Matrix m m ℂ)
  rw [gibbsExp_eq_conj_diagK hH β]
  rwa [Matrix.star_eq_conjTranspose]

/-- The Gibbs form is positive semidefinite (a
positive-real scalar multiple of `gibbsExp_posSemidef`). -/
theorem gibbsForm_posSemidef {H : Matrix m m ℂ}
    (hH : H.IsHermitian) (β : ℝ) [Nonempty m] :
    (gibbsForm H β).PosSemidef := by
  have hpos : 0 < ∑ i, Real.exp (-(β * hH.eigenvalues i)) :=
    gibbsTraceExp_pos hH β
  have hsm : ∀ (r : ℝ) (M : Matrix m m ℂ), ((r : ℂ)) • M = r • M := by
    intro r M
    ext i j
    simp [Matrix.smul_apply, smul_eq_mul]
  rw [gibbsForm, gibbsTraceExp_eq hH β, ← Complex.ofReal_inv, hsm]
  exact (gibbsExp_posSemidef hH β).smul (inv_nonneg.mpr hpos.le)

/-- **The Gibbs form is a density matrix** at any
Hermitian generator over a nonempty index: Hermitian
(`gibbsForm_isHermitian`), positive
(`gibbsForm_posSemidef`, read through
`Matrix.PosSemidef.dotProduct_mulVec_nonneg`), trace
one (`gibbsForm_trace`). -/
theorem gibbsForm_isDensityMatrix {H : Matrix m m ℂ}
    (hH : H.IsHermitian) (β : ℝ) [Nonempty m] :
    IsDensityMatrix (gibbsForm H β) := by
  refine ⟨gibbsForm_isHermitian hH β, ?_, gibbsForm_trace hH β⟩
  intro x
  have h := (gibbsForm_posSemidef hH β).dotProduct_mulVec_nonneg x
  exact (RCLike.nonneg_iff.mp h).1

/-! ## §3 — the KMS property of the Gibbs form -/

/-- The two Gibbs exponentials at inverse parameters
cancel: `exp(βH) * exp(-βH) = 1`. -/
theorem gibbsExp_mul_gibbsExp_neg {H : Matrix m m ℂ} (β : ℝ) :
    NormedSpace.exp ((β:ℂ) • H)
      * NormedSpace.exp ((-(β:ℂ)) • H) = 1 := by
  rw [← flowAction_exp_smul_add]
  simp

/-- **The KMS weight identity at imaginary time:**
inserting the imaginary-time flow against the Gibbs
form collapses, under the trace, to the swapped
product — the right factor `exp(βH)` cycles to the
front, meets the Gibbs form's own `exp(-βH)`, and
cancels it (`gibbsExp_mul_gibbsExp_neg`). -/
theorem gibbs_weight (H : Matrix m m ℂ) (β : ℝ)
    (A B : Matrix m m ℂ) :
    trace (gibbsForm H β * A
        * flowAction H ((β:ℂ) * Complex.I) B)
      = trace (gibbsForm H β * B * A) := by
  rw [flowAction_I_mul]
  have hEG : NormedSpace.exp ((β:ℂ) • H) * gibbsForm H β
      = (trace (NormedSpace.exp ((-(β:ℂ)) • H)))⁻¹
        • (1 : Matrix m m ℂ) := by
    rw [gibbsForm, Matrix.mul_smul, gibbsExp_mul_gibbsExp_neg]
  have step1 : trace (gibbsForm H β * A
        * (NormedSpace.exp ((-(β:ℂ)) • H) * B
          * NormedSpace.exp ((β:ℂ) • H)))
      = trace (NormedSpace.exp ((β:ℂ) • H)
          * (gibbsForm H β * A
            * (NormedSpace.exp ((-(β:ℂ)) • H) * B))) := by
    rw [show gibbsForm H β * A
          * (NormedSpace.exp ((-(β:ℂ)) • H) * B
            * NormedSpace.exp ((β:ℂ) • H))
        = (gibbsForm H β * A
            * (NormedSpace.exp ((-(β:ℂ)) • H) * B))
          * NormedSpace.exp ((β:ℂ) • H) from by
          simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
  rw [step1,
    show NormedSpace.exp ((β:ℂ) • H)
        * (gibbsForm H β * A
          * (NormedSpace.exp ((-(β:ℂ)) • H) * B))
      = (NormedSpace.exp ((β:ℂ) • H) * gibbsForm H β) * A
        * (NormedSpace.exp ((-(β:ℂ)) • H) * B) from by
        simp only [Matrix.mul_assoc],
    hEG]
  simp only [smul_mul_assoc, Matrix.one_mul,
    gibbsForm, Matrix.trace_smul, smul_eq_mul]
  rw [Matrix.trace_mul_comm]

/-- **Gibbs ⟹ KMS at Hermitian generators** — the
(⇐) direction of the finite KMS ⇔ Gibbs
correspondence, in `FlowKernel`'s vocabulary: for `H`
Hermitian over a nonempty index, the Gibbs form is a
KMS state for its own generator at its own `β`. The
proof splits the KMS parameter `t + β·I` the other
way (`β·I` outside), applies `gibbs_weight` to the
inner imaginary-time flow, and reads the result as the
right side. (The bare pin `FlowKernel.kms_iff_gibbs`
quantifies over non-Hermitian `H` too and is FALSE —
`FlowKernelKMS`, K-AQFT1-FORM; the correspondence
holds exactly here, at Hermitian generators, which is
where this lemma and AQFT-1's brick D meet.) -/
theorem gibbsForm_isKMSFlow {H : Matrix m m ℂ}
    (hH : H.IsHermitian) (β : ℝ) [Nonempty m] :
    IsKMSFlow (gibbsForm H β) H β := by
  refine ⟨gibbsForm_isDensityMatrix hH β, hH, ?_⟩
  intro A B t
  have hsplit : flowAction H ((t:ℂ) + (β:ℂ) * Complex.I) B
      = flowAction H ((β:ℂ) * Complex.I)
          (flowAction H (t:ℂ) B) := by
    rw [show (t:ℂ) + (β:ℂ) * Complex.I
        = (β:ℂ) * Complex.I + (t:ℂ) by ring,
      flowAction_add]
  rw [hsplit, gibbs_weight]

/-! ## §4 — the Partner seats

The AxiomTet Partner Hamiltonians complexified: the
matrices of `H_v = Dᵀ ∘ D` and `H_e = D ∘ Dᵀ` over `ℂ`
(the operators themselves are the real linear maps of
`AxiomTetPartner`; their matrices are
`LinearMap.toMatrix'`, as in `AxiomTetPartnerIso`).
Both are Hermitian — over `ℝ` each is a `DᵀD` / `DDᵀ`
form, symmetric by `toMatrix'_wAdjDiff_eq_transpose` —
so the whole Gibbs/KMS machine of §§1–3 seats on them. -/

section PartnerSeats

-- The Partner files' own device for the edge seat's
-- decidability (AxiomTetPartner, AxiomTetPartnerIso),
-- confined to this section.
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [LinearOrder V]
  (G : SimpleGraph V) (w : Sym2 V → ℝ)

/-- The vertex Hamiltonian complexified: the matrix of
`H_v = Dᵀ ∘ D` over `ℂ`. -/
noncomputable def vertexHamC : Matrix V V ℂ :=
  (LinearMap.toMatrix' (vertexHam G w)).map Complex.ofReal

/-- The edge Hamiltonian complexified: the matrix of
`H_e = D ∘ Dᵀ` over `ℂ`. -/
noncomputable def edgeHamC : Matrix ↥G.edgeSet ↥G.edgeSet ℂ :=
  (LinearMap.toMatrix' (edgeHam G w)).map Complex.ofReal

/-- The complexified vertex Hamiltonian is Hermitian:
its real matrix is symmetric (`M_v = M_Dᵀ * M_D` by
`toMatrix'_vertexHam` and
`toMatrix'_wAdjDiff_eq_transpose`), and complexification
preserves the symmetry entrywise. -/
theorem vertexHamC_isHermitian : (vertexHamC G w).IsHermitian := by
  have hsymm : (LinearMap.toMatrix' (vertexHam G w)).transpose
      = LinearMap.toMatrix' (vertexHam G w) := by
    rw [toMatrix'_vertexHam, toMatrix'_wAdjDiff_eq_transpose,
      Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.IsHermitian, vertexHamC]
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply,
    Complex.star_def, Complex.conj_ofReal]
  have h := congrFun (congrFun hsymm i) j
  rw [Matrix.transpose_apply] at h
  exact_mod_cast h

/-- The complexified edge Hamiltonian is Hermitian:
its real matrix is symmetric (`M_e = M_D * M_Dᵀ`). -/
theorem edgeHamC_isHermitian : (edgeHamC G w).IsHermitian := by
  have hsymm : (LinearMap.toMatrix' (edgeHam G w)).transpose
      = LinearMap.toMatrix' (edgeHam G w) := by
    rw [toMatrix'_edgeHam, toMatrix'_wAdjDiff_eq_transpose,
      Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.IsHermitian, edgeHamC]
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply,
    Complex.star_def, Complex.conj_ofReal]
  have h := congrFun (congrFun hsymm i) j
  rw [Matrix.transpose_apply] at h
  exact_mod_cast h

/-- The Gibbs form at the vertex seat is a density
matrix (§2b transported). -/
theorem vertexHamC_gibbs_isDensity (β : ℝ) [Nonempty V] :
    IsDensityMatrix (gibbsForm (vertexHamC G w) β) :=
  gibbsForm_isDensityMatrix (vertexHamC_isHermitian G w) β

/-- The Gibbs form at the edge seat is a density
matrix, where the edge seat is inhabited (§2b
transported). -/
theorem edgeHamC_gibbs_isDensity (β : ℝ) [Nonempty ↥G.edgeSet] :
    IsDensityMatrix (gibbsForm (edgeHamC G w) β) :=
  gibbsForm_isDensityMatrix (edgeHamC_isHermitian G w) β

/-- **KMS at the vertex seat:** the vertex Gibbs form
is a KMS state for its own generator — §3's
`gibbsForm_isKMSFlow` transported to the Partner seat,
honestly a specialization, no new computation. -/
theorem vertexHamC_gibbs_isKMS (β : ℝ) [Nonempty V] :
    IsKMSFlow (gibbsForm (vertexHamC G w) β) (vertexHamC G w) β :=
  gibbsForm_isKMSFlow (vertexHamC_isHermitian G w) β

/-- **KMS at the edge seat:** the edge Gibbs form is a
KMS state for its own generator, where the edge seat
is inhabited — §3 transported, as at the vertex. -/
theorem edgeHamC_gibbs_isKMS (β : ℝ) [Nonempty ↥G.edgeSet] :
    IsKMSFlow (gibbsForm (edgeHamC G w) β) (edgeHamC G w) β :=
  gibbsForm_isKMSFlow (edgeHamC_isHermitian G w) β

end PartnerSeats

/-! ## §5 — the thermal reading of SP-5

The resonance (gap) sets of the two Partner Gibbs
generators agree wherever SP-5's spectral
correspondence reaches. The route is the polynomial
one: SP-5's characteristic-polynomial identity is
transported to the complexified seats; a nonzero real
is an eigenvalue at one seat iff it is one at the
other (the `X ^ card` prefactors vanish only at `0`);
so the two eigenvalue ranges differ at most in the
zero sector, and under the zero-sector hypothesis —
both seats carry the zero mode — the ranges, and
with them the resonance gap sets, agree outright. -/

section SP5Thermal

open Polynomial

-- The Partner files' own device for the edge seat's
-- decidability, as in §4, confined to this section.
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [LinearOrder V]
  (G : SimpleGraph V) (w : Sym2 V → ℝ)

/-- The characteristic polynomial of the complexified
vertex Hamiltonian is the complexification of the
real one. -/
theorem vertexHamC_charpoly :
    (vertexHamC G w).charpoly
      = ((vertexHam G w).charpoly).map Complex.ofRealHom := by
  have hmap : (LinearMap.toMatrix' (vertexHam G w)).map Complex.ofReal
      = (LinearMap.toMatrix' (vertexHam G w)).map ⇑Complex.ofRealHom := rfl
  rw [vertexHamC, hmap, Matrix.charpoly_map, ← charpoly_vertexHam]

/-- The characteristic polynomial of the complexified
edge Hamiltonian is the complexification of the
real one. -/
theorem edgeHamC_charpoly :
    (edgeHamC G w).charpoly
      = ((edgeHam G w).charpoly).map Complex.ofRealHom := by
  have hmap : (LinearMap.toMatrix' (edgeHam G w)).map Complex.ofReal
      = (LinearMap.toMatrix' (edgeHam G w)).map ⇑Complex.ofRealHom := rfl
  rw [edgeHamC, hmap, Matrix.charpoly_map, ← charpoly_edgeHam]

/-- **SP-5 at the complexified seats:** the polynomial
identity of `AxiomTetPartnerIso.sp5_charpoly_identity`,
transported along `Complex.ofReal`. -/
theorem sp5_charpoly_identity_C :
    X ^ Fintype.card ↥G.edgeSet * (vertexHamC G w).charpoly
      = X ^ Fintype.card V * (edgeHamC G w).charpoly := by
  have h := congrArg (Polynomial.map Complex.ofRealHom)
    (sp5_charpoly_identity G w)
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X] at h
  rw [vertexHamC_charpoly, edgeHamC_charpoly]
  exact h

/-- A nonzero complex number is a root of one seat's
characteristic polynomial iff it is a root of the
other's: in SP-5's identity the prefactors
`X ^ card` vanish only at `0`. -/
theorem isRoot_vertexHamC_charpoly_iff {μ : ℂ} (hμ : μ ≠ 0) :
    (vertexHamC G w).charpoly.IsRoot μ
      ↔ (edgeHamC G w).charpoly.IsRoot μ := by
  have hev : μ ^ Fintype.card ↥G.edgeSet
        * (vertexHamC G w).charpoly.eval μ
      = μ ^ Fintype.card V * (edgeHamC G w).charpoly.eval μ := by
    have h := congrArg (fun p : ℂ[X] => p.eval μ)
      (sp5_charpoly_identity_C G w)
    simpa [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
      using h
  rw [Polynomial.IsRoot, Polynomial.IsRoot]
  constructor
  · intro h0
    rw [h0, mul_zero] at hev
    exact (mul_eq_zero.mp hev.symm).resolve_left (pow_ne_zero _ hμ)
  · intro h0
    rw [h0, mul_zero] at hev
    exact (mul_eq_zero.mp hev).resolve_left (pow_ne_zero _ hμ)

/-- For a Hermitian matrix, a real number is in the
range of its eigenvalue function iff its
complexification is a root of the characteristic
polynomial (spectrum = eigenvalue range; spectrum =
charpoly roots). -/
theorem isHermitian_mem_range_eigenvalues_iff {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (r : ℝ) :
    r ∈ Set.range hA.eigenvalues ↔ A.charpoly.IsRoot (r : ℂ) := by
  rw [← Matrix.mem_spectrum_iff_isRoot_charpoly, hA.spectrum_eq_image_range]
  constructor
  · rintro ⟨s, -, rfl⟩
    exact ⟨hA.eigenvalues s, ⟨s, rfl⟩, rfl⟩
  · rintro ⟨-, ⟨s, rfl⟩, hs⟩
    have h2 : ((hA.eigenvalues s : ℂ)) = (r : ℂ) := hs
    exact ⟨s, by exact_mod_cast h2⟩

/-- A nonzero real eigenvalue of the vertex seat is
an eigenvalue of the edge seat and conversely —
SP-5's correspondence, read through the spectral
theorem. -/
theorem mem_range_eigenvalues_vertexHamC_iff {r : ℝ} (hr : r ≠ 0) :
    r ∈ Set.range (vertexHamC_isHermitian G w).eigenvalues
      ↔ r ∈ Set.range (edgeHamC_isHermitian G w).eigenvalues := by
  rw [isHermitian_mem_range_eigenvalues_iff,
    isHermitian_mem_range_eigenvalues_iff]
  exact isRoot_vertexHamC_charpoly_iff G w (by exact_mod_cast hr)

/-- **The thermal reading of SP-5 (the gap-set
identity), in the conditional form the correspondence
supports.** Under the zero-sector hypothesis — both
seats carry the zero mode — the resonance gap sets
of the two Partner Gibbs generators agree: the two
eigenvalue ranges coincide (the nonzero parts by
SP-5, the zero parts by hypothesis), and a gap set
sees only the range. -/
theorem resonanceSpectrum_partnerSeats_eq
    (hzero : (0 : ℝ) ∈ Set.range (vertexHamC_isHermitian G w).eigenvalues
      ∧ (0 : ℝ) ∈ Set.range (edgeHamC_isHermitian G w).eigenvalues) :
    resonanceSpectrum (vertexHamC_isHermitian G w).eigenvalues
      = resonanceSpectrum (edgeHamC_isHermitian G w).eigenvalues := by
  have hrange : Set.range (vertexHamC_isHermitian G w).eigenvalues
      = Set.range (edgeHamC_isHermitian G w).eigenvalues := by
    ext r
    by_cases hr : r = 0
    · subst hr
      exact ⟨fun _ => hzero.2, fun _ => hzero.1⟩
    · exact mem_range_eigenvalues_vertexHamC_iff G w hr
  unfold resonanceSpectrum
  ext x
  constructor
  · rintro ⟨⟨i, j⟩, rfl⟩
    obtain ⟨i', hi'⟩ :
        (vertexHamC_isHermitian G w).eigenvalues i
          ∈ Set.range (edgeHamC_isHermitian G w).eigenvalues := by
      rw [← hrange]; exact ⟨i, rfl⟩
    obtain ⟨j', hj'⟩ :
        (vertexHamC_isHermitian G w).eigenvalues j
          ∈ Set.range (edgeHamC_isHermitian G w).eigenvalues := by
      rw [← hrange]; exact ⟨j, rfl⟩
    exact ⟨(i', j'), by simp only [hi', hj']⟩
  · rintro ⟨⟨i, j⟩, rfl⟩
    obtain ⟨i', hi'⟩ :
        (edgeHamC_isHermitian G w).eigenvalues i
          ∈ Set.range (vertexHamC_isHermitian G w).eigenvalues := by
      rw [hrange]; exact ⟨i, rfl⟩
    obtain ⟨j', hj'⟩ :
        (edgeHamC_isHermitian G w).eigenvalues j
          ∈ Set.range (vertexHamC_isHermitian G w).eigenvalues := by
      rw [hrange]; exact ⟨j, rfl⟩
    exact ⟨(i', j'), by simp only [hi', hj']⟩

end SP5Thermal

end ThetLogos
