import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.Analysis.Matrix.Order
import ThetLogos.PreCompensation
import ThetLogos.ResonanceSpectrum
import ThetLogos.SpectralClock
import ThetLogos.ThermalClock

open Matrix Finset
open scoped ComplexOrder

namespace ThetLogos

/-!
# ThetLogos.ThermalPreCompensation — the thermal instance of pre-compensation (T1 target)

HONESTY LEDGER (read before citing):

- Status: **VERIFIED — STANDS WHOLE (T1), compiled green
  2026-10-21** (`lake build ThetLogos.ThermalPreCompensation`,
  3,368 jobs, 0 errors), parent-verified on the exact shipped
  text (`.olean` present, strict recount 24, incompleteness
  census 0 on comment-stripped source, axioms on the six checked
  headline theorems standard only: `propext`, `Classical.choice`,
  `Quot.sound`). K3 (narrowing the reachability iff) did NOT
  trigger — the iff stands as stated; the density theorem carries
  its kernel positive-semidefiniteness hypothesis on its face, as
  chartered (K1, a fence, not a gap). Repairs in the open, no
  statement changed: proof-body rewrite-order and lemma-name
  fixes (notably `Matrix.diagonal_conjTranspose`, the pin's name);
  `thermAmplify` marked `noncomputable` (marker only, body
  identical); `open scoped ComplexOrder` added (the ℂ-valued
  `PosSemidef` statements cannot elaborate in this pin without
  the scoped order instance Mathlib itself uses). Full repair
  log: dossier `whitepaper/thermal-pre-compensation-2026-10-21.md`.
- What this brick is: the named surviving remainder of
  `PreCompensation` (28 T1, landed 2026-10-18). That brick treats
  Jeff's pre-deformed-gears question for a CONSTANT-factor Schur
  family, `dephase l A = l • A + (1 − l) • pinch A`, and its
  dossier names the thermal instance as the one that did NOT fall
  out: pre-distort a state so that a thermal deformation lands it
  on target, where the deformation "acts through the clock's
  flow, not a Schur family". This brick builds the thermal
  channel AS a Schur family — but one INDEXED BY THE SPECTRUM of
  the clock's generator: the coherence `(i, j)` is damped by a
  factor `f (lam i − lam j)` depending on the GAP of the
  generator's eigenvalue function `lam`. Gap-zero coherences are
  untouched (factor `f 0 = 1`), wider gaps are damped harder. At
  a packaged `ThermalClock C` the intended reading is
  `lam = clockLam C`, `j ↦ −log (C.weights j)` — the eigenvalues
  of `K = −ln ρ`, the same function `SpectralClock` reads the
  master tick off. At a general Hermitian generator (post
  `HermitianReduction`) take `lam := hK.eigenvalues`; every
  statement here is at abstract `lam`, so that substitution is
  the whole transport, and no further transport is claimed.
- The factor is taken axiomatically-by-properties, NOT from a
  flow average, and the header owes the reason: the corpus's own
  flow (`ResonanceSpectrum.phaseFlow`, `ThermalClock.diagFlow`)
  has PHASE factors `exp(−it·gap)` of modulus 1; its honest
  time-averages give oscillatory factors (cosine / sinc type)
  which take negative values and have zeros — damping factors
  in the thermal sense (positive, at most 1, nowhere zero if
  de-amplification is to make sense) do not fall out of the
  corpus's flow without a positivity input the corpus does not
  currently carry (a Bochner / Fourier-positivity theorem).
  What the corpus DOES support is included as a theorem, not
  used as the definition: the two-kick flow average
  `½(phaseFlow s + phaseFlow (−s))` is exactly `thermDamp` at
  the factor `cos (s · ·)` (`thermDamp_cos_eq`,
  `isDensityMatrix_thermDamp_cos`) — the flow's own shadow in
  this family, with positivity discharged there. The headline
  damping factor is the exponential `expDamp β x = exp(−β|x|)`,
  instantiated where a concrete obstruction needs numbers.
- CENTRE OF GRAVITY — positivity is conditional, on the face.
  `PreCompensation`'s positivity route does NOT transport: it
  wrote the channel as an affine combination of two
  density-preserving maps (identity and pinch). A gap-Schur
  multiplier has no such decomposition. Its positivity is the
  Schur product theorem (Mathlib's `Matrix.PosSemidef.hadamard`)
  and therefore needs the KERNEL `(i, j) ↦ f (lam i − lam j)`
  to be positive semidefinite. That hypothesis is stated
  explicitly as a condition on `(lam, f)` in
  `isDensityMatrix_thermDamp` — it is the price of the channel,
  printed on the label, never assumed silently (kill condition
  K1: this is a fence, not a failure). Two instances discharge
  it in this file: the constant factor `f ≡ 1` (the identity
  channel; kernel `1`, positivity is `PreCompensation`'s
  systematic case in degenerate form — not separately stated)
  and the cosine two-kick factor above. The reachability theory
  (§3) and the obstruction (§4) do NOT use positivity of the
  channel at all: they are entrywise algebra plus the
  candidate's own positivity clause, exactly as in
  `PreCompensation`.
- What is proved (targets): the thermal Schur channel and its
  entry law; diagonal and zero-gap entries fixed; trace and
  Hermiticity (the latter needs `f` even); the de-amplification
  candidate and the two-sided cancellation; the reachability
  iff in `PreCompensation`'s exact shape (candidate unique,
  Hermiticity and trace automatic, positivity the whole
  question); the degenerate-block law (zero-gap entries pass
  through unchanged, and every pre-image agrees with the target
  there — no amplification is possible or needed on a
  degenerate block); the exponential factor's semigroup law in
  `β`; and the sharp obstruction: the maximally coherent pair
  state across the WIDEST gap is not pre-compensable at any
  `β > 0`, its candidate's negative direction priced at exactly
  `exp (β · spectralWidth lam) = 1 / f (width)` — the widest
  tooth is the most expensive to pre-cut, and the price is the
  spectral width `SpectralClock` already owns.
- Named remainders (not proved, not hidden):
  R1. Kernel positivity of the exponential factor
  `exp (−β|·|)`. Classically true (it is the covariance kernel
  of an Ornstein–Uhlenbeck process; equivalently a Fourier
  transform of a positive density), but no proof exists in this
  corpus or is attempted here. The obstruction theorem is
  deliberately stated so as not to need it: it obstructs
  pre-compensation whether or not the exponential-damped map
  is everywhere a channel.
  R2. Continuous flow time-averages (sinc-type factors from
  averaging `phaseFlow` over an interval, Gaussian factors
  from Gaussian averaging). Only the two-kick average is
  discharged; the averaged-factor family and its kernel
  positivity are open.
  R3. Genuine Gibbs thermalization (a Kraus / Lindblad channel
  satisfying detailed balance, relaxation to `gibbsState`) is
  NOT this Schur family. This brick is the gap-indexed Schur
  shadow of thermal damping, per the commission; the shelf
  note in `PreCompensation`'s dossier — thermalization acts
  through the clock's flow — stands as the pointer to that
  larger, unbuilt object.
  R4. The `e^{−K} = ρ` jewel and the payoff vocabulary of
  `ThermalKernel` are cited for language only; nothing here
  re-proves or extends them, and `HermitianReduction`'s
  remainder R2 (matrix logarithm for non-diagonal `ρ`) is
  untouched.
- Fences. Finite level only: finite index type, matrices over
  `ℂ`, a real eigenvalue function `lam : ι → ℝ` and a real
  factor `f : ℝ → ℝ`. Factor hypotheses are carried explicitly
  (`f 0 = 1`, evenness, nowhere-vanishing) and each theorem
  states the ones it uses. `thermAmplify` at a factor with
  zeros is still a well-defined matrix but is NOT claimed to
  invert anything there — the cancellation and reachability
  theorems carry `∀ x, f x ≠ 0` on their faces. No continuum,
  no dynamics, no Yang–Mills or Millennium content.
- Pre-named kill conditions. K1: if positivity of the channel
  needs the kernel positive-semidefiniteness hypothesis, the
  brick stands WITH the hypothesis stated on its face (a fence,
  as above — expected, and already the design). K2: any
  placeholder proof, and this file does not count. K3: if the
  reachability iff does not transport to gap-dependent factors,
  the brick narrows to the channel + obstruction and names the
  iff a remainder. (Scoping showed the iff's proof in
  `PreCompensation` is pure inversion algebra, which transports
  entrywise; K3 is the compile-time narrowing rule if that
  judgement fails.)
-/

-- ============================================================================
-- §0. The clock's eigenvalue function
-- ============================================================================

/-- **The clock's eigenvalue function** (Tier T2, definition): for
a packaged thermal clock `C`, the eigenvalues of its generator
`K = −ln ρ` are `j ↦ −log (weights j)` — the same function
`SpectralClock.thermalClock_masterTick` reads the master tick
off. The thermal channel of a clock is `thermDamp` at this
`lam`. Stated as a definition so the instance has a name; all
theorems below are at abstract `lam`. -/
noncomputable def clockLam {N : ℕ} (C : ThermalClock N) : Fin N → ℝ :=
  fun j => -Real.log (C.weights j)

-- ============================================================================
-- §1. The thermal Schur channel: entry algebra
-- ============================================================================

section Channel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The gap kernel** (Tier T2, definition): the matrix of
damping factors, `(i, j) ↦ ((f (lam i − lam j) : ℂ))`. The
channel below is its Hadamard (entrywise) product with the
input — which is exactly why its positivity is the Schur
product theorem's business (§2). -/
def gapKernel (lam : ι → ℝ) (f : ℝ → ℝ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => ((f (lam i - lam j) : ℂ))

/-- **The thermal Schur channel** (Tier T2, definition): the
coherence `(i, j)` of `A` is damped by the factor
`f (lam i − lam j)` of its spectral gap. Diagonal entries have
gap `0`; with `f 0 = 1` they are populations and do not move.
This replaces `PreCompensation`'s constant level `l` by a
gap-dependent factor — the thermal deformation, indexed by the
generator's spectrum. -/
def thermDamp (lam : ι → ℝ) (f : ℝ → ℝ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => ((f (lam i - lam j) : ℂ)) * A i j

/-- **The de-amplified candidate** (Tier T2, definition): entry
`(i, j)` divided by its damping factor — the unique possible
pre-image of the reachability theorem (§3), the thermal form
of `PreCompensation`'s `dephase l⁻¹` candidate. Where a factor
vanishes this is still a matrix (junk entries at the zeros);
it inverts the channel only under `∀ x, f x ≠ 0`. -/
noncomputable def thermAmplify (lam : ι → ℝ) (f : ℝ → ℝ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => (((f (lam i - lam j) : ℂ)))⁻¹ * A i j

/-- The entry law of the thermal channel (Tier T1 target). -/
theorem thermDamp_apply (lam : ι → ℝ) (f : ℝ → ℝ) (A : Matrix ι ι ℂ)
    (i j : ι) :
    thermDamp lam f A i j = ((f (lam i - lam j) : ℂ)) * A i j :=
  rfl

/-- The entry law of the de-amplified candidate (Tier T1
target). -/
theorem thermAmplify_apply (lam : ι → ℝ) (f : ℝ → ℝ) (A : Matrix ι ι ℂ)
    (i j : ι) :
    thermAmplify lam f A i j = (((f (lam i - lam j) : ℂ)))⁻¹ * A i j :=
  rfl

/-- The channel is the Hadamard product with its kernel
(Tier T1 target): `thermDamp lam f A = gapKernel lam f ⊙ A`.
This is the bridge the Schur product theorem walks across in
§2. -/
theorem thermDamp_eq_hadamard (lam : ι → ℝ) (f : ℝ → ℝ) (A : Matrix ι ι ℂ) :
    thermDamp lam f A = gapKernel lam f ⊙ A := by
  ext i j
  rw [Matrix.hadamard_apply]
  rfl

/-- Populations are invariant under the thermal channel
(Tier T1 target): the diagonal of `thermDamp lam f A` is the
diagonal of `A`, because the diagonal gap is `0` and `f 0 = 1`.
The thermal form of `dephase_diag`. -/
theorem thermDamp_apply_diag (lam : ι → ℝ) (f : ℝ → ℝ) (hf0 : f 0 = 1)
    (A : Matrix ι ι ℂ) (i : ι) :
    thermDamp lam f A i i = A i i := by
  rw [thermDamp_apply, sub_self, hf0]
  simp

/-- **Zero-gap entries pass through unchanged** (Tier T1
target): any coherence inside a degenerate block (`lam i =
lam j`) is a fixed entry of the channel, at every factor with
`f 0 = 1`. The degenerate-block law, channel side — the
thermal form of the pinch's diagonal invariance, one level
up: whole blocks, not just the diagonal, are invisible to a
gap-indexed deformation. -/
theorem thermDamp_apply_of_lam_eq (lam : ι → ℝ) (f : ℝ → ℝ) (hf0 : f 0 = 1)
    (A : Matrix ι ι ℂ) {i j : ι} (h : lam i = lam j) :
    thermDamp lam f A i j = A i j := by
  have hgap : lam i - lam j = 0 := by rw [h, sub_self]
  rw [thermDamp_apply, hgap, hf0]
  simp

/-- The thermal channel preserves the trace (Tier T1 target),
at every factor with `f 0 = 1`: the trace reads only the
diagonal, and the diagonal does not move. -/
theorem trace_thermDamp (lam : ι → ℝ) (f : ℝ → ℝ) (hf0 : f 0 = 1)
    (A : Matrix ι ι ℂ) :
    Matrix.trace (thermDamp lam f A) = Matrix.trace A := by
  show (∑ i, thermDamp lam f A i i) = ∑ i, A i i
  exact Finset.sum_congr rfl fun i _ => thermDamp_apply_diag lam f hf0 A i

/-- The thermal channel preserves Hermiticity (Tier T1 target)
when the factor is even, `f (−x) = f x`: the `(j, i)` factor
is the `(i, j)` factor because the reversed gap is the
negated gap, and the factor is real, so no conjugation lands
on it. The thermal form of `isHermitian_dephase`. -/
theorem isHermitian_thermDamp (lam : ι → ℝ) (f : ℝ → ℝ)
    (hfeven : ∀ x : ℝ, f (-x) = f x) {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) :
    (thermDamp lam f A).IsHermitian := by
  have hstar : ∀ r : ℝ, star ((r : ℂ)) = (r : ℂ) := by
    intro r
    rw [← starRingEnd_apply]
    exact Complex.conj_ofReal r
  show (thermDamp lam f A)ᴴ = thermDamp lam f A
  ext i j
  have hAij : star (A j i) = A i j := by
    have h1 : Aᴴ j i = A j i := by rw [hA.eq]
    rw [Matrix.conjTranspose_apply] at h1
    rw [← h1, star_star]
  rw [Matrix.conjTranspose_apply, thermDamp_apply, thermDamp_apply,
    star_mul, hstar, hAij]
  have hfac : ((f (lam j - lam i) : ℂ)) = ((f (lam i - lam j) : ℂ)) := by
    have hgap : lam j - lam i = -(lam i - lam j) := by ring
    rw [hgap, hfeven]
  rw [hfac]
  exact mul_comm _ _

/-- De-amplification cancels the thermal channel (left
inverse), for a nowhere-zero factor (Tier T1 target): the
candidate of §3 really is a pre-image when it is a state. -/
theorem thermDamp_amplify_cancel (lam : ι → ℝ) (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, f x ≠ 0) (A : Matrix ι ι ℂ) :
    thermDamp lam f (thermAmplify lam f A) = A := by
  ext i j
  rw [thermDamp_apply, thermAmplify_apply, ← mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (hf _)), one_mul]

/-- The thermal channel cancels de-amplification (right
inverse), for a nowhere-zero factor (Tier T1 target). -/
theorem thermAmplify_thermDamp_cancel (lam : ι → ℝ) (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, f x ≠ 0) (A : Matrix ι ι ℂ) :
    thermAmplify lam f (thermDamp lam f A) = A := by
  ext i j
  rw [thermAmplify_apply, thermDamp_apply, ← mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (hf _)), one_mul]

/-- **The candidate is the unique possible pre-image**
(Tier T1 target): any matrix the channel lands on `ρ` is the
de-amplified candidate. Uniqueness is what makes the
reachability question of §3 a question about ONE matrix. -/
theorem eq_thermAmplify_of_thermDamp_eq (lam : ι → ℝ) (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, f x ≠ 0) {σ ρ : Matrix ι ι ℂ}
    (h : thermDamp lam f σ = ρ) :
    σ = thermAmplify lam f ρ := by
  conv_lhs => rw [← thermAmplify_thermDamp_cancel lam f hf σ]
  rw [h]

end Channel

-- ============================================================================
-- §2. Density preservation: the Schur route, and the flow's own instance
-- ============================================================================

section Density

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Bridge (Tier T1 target): a corpus density matrix is a
Mathlib positive-semidefinite matrix. The Hermitian clause is
shared; the positivity clause is the same quadratic form,
read through `RCLike.nonneg_iff` — the quadratic form of a
Hermitian matrix is real, so its imaginary part vanishes (it
is its own conjugate: conjugate the form and use `ρᴴ = ρ`). -/
theorem posSemidef_of_isDensityMatrix {ρ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) : ρ.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hρ.1, fun x => ?_⟩
  have him : ((star x) ⬝ᵥ (ρ *ᵥ x)).im = 0 := by
    have hself : star ((star x) ⬝ᵥ (ρ *ᵥ x)) = (star x) ⬝ᵥ (ρ *ᵥ x) := by
      rw [← Matrix.star_dotProduct, Matrix.star_mulVec, hρ.1.eq,
        ← dotProduct_mulVec]
    have h2 := congrArg Complex.im hself
    rw [Complex.star_def, Complex.conj_im] at h2
    linarith
  exact RCLike.nonneg_iff.mpr ⟨hρ.2.1 x, him⟩

/-- **The channel property, with its price on the label**
(Tier T1 target): if the gap kernel of `(lam, f)` is positive
semidefinite, `f 0 = 1`, and `f` is even, then the thermal
channel maps density matrices to density matrices. The kernel
hypothesis is the whole content beyond `PreCompensation`:
positivity of a Schur multiplier IS the positivity of its
kernel, by Mathlib's Schur product theorem
(`Matrix.PosSemidef.hadamard`) — stated here as a hypothesis
on `(lam, f)`, per kill condition K1, never assumed silently.
Hermiticity comes from the product theorem, the trace from
the fixed diagonal. -/
theorem isDensityMatrix_thermDamp (lam : ι → ℝ) (f : ℝ → ℝ)
    (hf0 : f 0 = 1) (hfeven : ∀ x : ℝ, f (-x) = f x)
    (hK : (gapKernel lam f).PosSemidef)
    {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (thermDamp lam f ρ) := by
  have hps : (gapKernel lam f ⊙ ρ).PosSemidef :=
    hK.hadamard (posSemidef_of_isDensityMatrix hρ)
  rw [thermDamp_eq_hadamard]
  refine ⟨hps.isHermitian, fun x => hps.re_dotProduct_nonneg x, ?_⟩
  show (∑ i, (gapKernel lam f ⊙ ρ) i i) = 1
  have hdiag : ∀ i, (gapKernel lam f ⊙ ρ) i i = ρ i i := by
    intro i
    show ((f (lam i - lam i) : ℂ)) * ρ i i = ρ i i
    rw [sub_self, hf0]
    simp
  rw [Finset.sum_congr rfl (fun i _ => hdiag i)]
  exact hρ.2.2

/-- **The flow's own instance** (Tier T1 target): the two-kick
time average of the clock's phase flow IS a thermal channel —
the factor `cos (s · gap)`. Entry by entry this is
`phaseFlow_apply` at times `s` and `−s` plus Euler's identity:
the phases `exp(∓is·gap)` average to the real factor
`cos (s · gap)`. This is the corpus-supported sense in which
the thermal deformation "acts through the clock's flow": the
flow's symmetric two-point average lands in this family. -/
theorem thermDamp_cos_eq (lam : ι → ℝ) (s : ℝ) (A : Matrix ι ι ℂ) :
    thermDamp lam (fun x => Real.cos (s * x)) A
      = ((1 / 2 : ℝ) : ℂ) • (phaseFlow lam s A + phaseFlow lam (-s) A) := by
  have hcos : ∀ θ : ℝ, ((Real.cos θ : ℂ))
      = (Complex.exp ((θ : ℂ) * Complex.I)
        + Complex.exp (-((θ : ℂ) * Complex.I))) / 2 := by
    intro θ
    rw [Complex.ofReal_cos, Complex.cos]
    congr 1
    congr 1
    rw [neg_mul]
  ext i j
  simp only [thermDamp_apply, Matrix.smul_apply, Matrix.add_apply,
    phaseFlow_apply, smul_eq_mul]
  have hgap : ((s * (lam i - lam j) : ℝ) : ℂ)
      = (s : ℂ) * ((lam i : ℂ) - (lam j : ℂ)) := by push_cast; ring
  have e1 : -(Complex.I * (s : ℂ) * ((lam i : ℂ) - (lam j : ℂ)))
      = -(((s * (lam i - lam j) : ℝ) : ℂ) * Complex.I) := by
    rw [hgap]; ring
  have e2 : -(Complex.I * ((-s : ℝ) : ℂ) * ((lam i : ℂ) - (lam j : ℂ)))
      = ((s * (lam i - lam j) : ℝ) : ℂ) * Complex.I := by
    rw [hgap]; push_cast; ring
  rw [hcos, e1, e2]
  push_cast
  ring

/-- **The two-kick instance is a channel, unconditionally**
(Tier T1 target): `thermDamp` at the cosine factor maps
density matrices to density matrices, with NO kernel
hypothesis — positivity is discharged by the flow itself.
Each `phaseFlow lam t` is conjugation of `ρ` by the diagonal
unitary of its phases, hence density-preserving by
`PreCompensation.isDensityMatrix_conj`; the channel is the
average of the two kicks, a convex combination of two
density-preserving maps — the same affine route
`isDensityMatrix_dephase` walks, one floor up. Note the
cosine factor has zeros and negative values: it is a channel
that is NOT de-amplifiable, and §3 does not apply to it. The
two facts are compatible, and both are on the label. -/
theorem isDensityMatrix_thermDamp_cos (lam : ι → ℝ) (s : ℝ)
    {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (thermDamp lam (fun x => Real.cos (s * x)) ρ) := by
  have hpf : ∀ t : ℝ, IsDensityMatrix (phaseFlow lam t ρ) := by
    intro t
    set D : Matrix ι ι ℂ :=
      diagonal (fun j => Complex.exp (-(Complex.I * (t : ℂ) * (lam j : ℂ))))
      with hD
    have hstarD : star D
        = diagonal (fun j => Complex.exp (Complex.I * (t : ℂ) * (lam j : ℂ))) := by
      rw [hD, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
      congr 1
      funext j
      show star (Complex.exp (-(Complex.I * (t : ℂ) * (lam j : ℂ))))
          = Complex.exp (Complex.I * (t : ℂ) * (lam j : ℂ))
      rw [← starRingEnd_apply, ← Complex.exp_conj]
      congr 1
      have hI : (starRingEnd ℂ) Complex.I = -Complex.I := Complex.conj_I
      have hRe : ∀ r : ℝ, (starRingEnd ℂ) (r : ℂ) = (r : ℂ) :=
        fun r => Complex.conj_ofReal r
      rw [map_neg, map_mul, map_mul, hI, hRe, hRe]
      ring
    have hUD : star D * D = 1 := by
      rw [hstarD, hD, Matrix.diagonal_mul_diagonal]
      have hfun : (fun j => Complex.exp (Complex.I * (t : ℂ) * (lam j : ℂ))
            * Complex.exp (-(Complex.I * (t : ℂ) * (lam j : ℂ))))
          = fun _ => (1 : ℂ) := by
        funext j
        rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      rw [hfun, Matrix.diagonal_one]
    have key := isDensityMatrix_conj hUD hρ
    have hform : phaseFlow lam t ρ = D * ρ * star D := by
      unfold phaseFlow
      rw [← hstarD, ← hD]
    rwa [hform]
  rw [thermDamp_cos_eq]
  have h1 := hpf s
  have h2 := hpf (-s)
  have hstar : star (((1 / 2 : ℝ) : ℂ)) = ((1 / 2 : ℝ) : ℂ) := by
    rw [← starRingEnd_apply]
    exact Complex.conj_ofReal _
  refine ⟨?_, ?_, ?_⟩
  · show (((1 / 2 : ℝ) : ℂ) • (phaseFlow lam s ρ + phaseFlow lam (-s) ρ))ᴴ
      = ((1 / 2 : ℝ) : ℂ) • (phaseFlow lam s ρ + phaseFlow lam (-s) ρ)
    have hAe1 : (phaseFlow lam s ρ)ᴴ = phaseFlow lam s ρ := h1.1
    have hAe2 : (phaseFlow lam (-s) ρ)ᴴ = phaseFlow lam (-s) ρ := h2.1
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, hAe1, hAe2, hstar]
  · intro x
    have hre : ∀ (c : ℝ) (z : ℂ), (((c : ℂ)) * z).re = c * z.re := by
      intro c z
      simp [Complex.mul_re]
    have hQ : (star x) ⬝ᵥ ((((1 / 2 : ℝ) : ℂ)
          • (phaseFlow lam s ρ + phaseFlow lam (-s) ρ)) *ᵥ x)
        = ((1 / 2 : ℝ) : ℂ)
          * (((star x) ⬝ᵥ (phaseFlow lam s ρ *ᵥ x))
            + ((star x) ⬝ᵥ (phaseFlow lam (-s) ρ *ᵥ x))) := by
      rw [Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul,
        dotProduct_add]
      simp only [smul_eq_mul]
    rw [hQ, hre, Complex.add_re]
    exact mul_nonneg (by norm_num) (add_nonneg (h1.2.1 x) (h2.2.1 x))
  · rw [Matrix.trace_smul, Matrix.trace_add, h1.2.2, h2.2.2]
    norm_num

end Density

-- ============================================================================
-- §3. Reachability: exactly which targets can be pre-compensated
-- ============================================================================

section Reachability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A target state `ρ` is **exactly pre-compensable** under
the thermal channel `thermDamp lam f` if some density matrix
`σ` is mapped onto it. The thermal form of
`PreCompensation.PreCompensable`. -/
def ThermPreCompensable (lam : ι → ℝ) (f : ℝ → ℝ) (ρ : Matrix ι ι ℂ) :
    Prop :=
  ∃ σ : Matrix ι ι ℂ, IsDensityMatrix σ ∧ thermDamp lam f σ = ρ

/-- **The reachability theorem, thermal form** (Tier T1
target): for a nowhere-zero factor, a density matrix `ρ` is
exactly pre-compensable under `thermDamp lam f` iff the
de-amplified candidate `thermAmplify lam f ρ` is itself a
density matrix. The candidate is the unique possible
pre-image (`eq_thermAmplify_of_thermDamp_eq`); reachability
is exactly "de-amplification stays inside the state space".
The proof is `precompensable_iff`'s inversion algebra,
transported entrywise — no positivity of the channel is used
or needed. -/
theorem thermPrecompensable_iff (lam : ι → ℝ) (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, f x ≠ 0) {ρ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) :
    ThermPreCompensable lam f ρ
      ↔ IsDensityMatrix (thermAmplify lam f ρ) := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rw [thermAmplify_thermDamp_cancel lam f hf]
    exact hσ
  · intro h
    exact ⟨thermAmplify lam f ρ, h, thermDamp_amplify_cancel lam f hf ρ⟩

/-- The candidate at the amplified factor (Tier T1 target):
`thermAmplify lam f` IS `thermDamp` at the reciprocal factor,
entrywise — division by a real cast is the cast of the
division. This is what lets the automatic clauses below reuse
§1 at the factor `fun x => (f x)⁻¹`. -/
theorem thermAmplify_eq_thermDamp_inv (lam : ι → ℝ) (f : ℝ → ℝ)
    (A : Matrix ι ι ℂ) :
    thermAmplify lam f A = thermDamp lam (fun x => (f x)⁻¹) A := by
  ext i j
  rw [thermAmplify_apply, thermDamp_apply, Complex.ofReal_inv]

/-- Of the candidate's three density conditions, two are
automatic (Tier T1 target): Hermiticity (the reciprocal of an
even factor is even) and trace (the diagonal factor is
`(f 0)⁻¹ = 1`). The reachability question is exactly the
positivity clause — `isDensityMatrix_dephase_iff_pos`,
transported. -/
theorem isDensityMatrix_thermAmplify_iff_pos (lam : ι → ℝ) (f : ℝ → ℝ)
    (hf0 : f 0 = 1) (hfeven : ∀ x : ℝ, f (-x) = f x)
    {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (thermAmplify lam f ρ)
      ↔ ∀ x : ι → ℂ,
          0 ≤ ((star x) ⬝ᵥ ((thermAmplify lam f ρ) *ᵥ x)).re :=
  ⟨fun h => h.2.1,
   fun h => by
     rw [thermAmplify_eq_thermDamp_inv] at h ⊢
     refine ⟨?_, h, ?_⟩
     · exact isHermitian_thermDamp lam (fun x => (f x)⁻¹)
         (fun x => by rw [hfeven x]) hρ.1
     · rw [trace_thermDamp lam (fun x => (f x)⁻¹) (by rw [hf0, inv_one])]
       exact hρ.2.2⟩

/-- **The reachability theorem, positivity form** (Tier T1
target): `ρ` is exactly pre-compensable under the thermal
channel iff the de-amplified candidate's quadratic form is
everywhere nonnegative. Positivity is the whole question —
the thermal form of `precompensable_iff_pos`, and the form
the obstruction of §4 is proved in. -/
theorem thermPrecompensable_iff_pos (lam : ι → ℝ) (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, f x ≠ 0) (hf0 : f 0 = 1)
    (hfeven : ∀ x : ℝ, f (-x) = f x)
    {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) :
    ThermPreCompensable lam f ρ
      ↔ ∀ x : ι → ℂ,
          0 ≤ ((star x) ⬝ᵥ ((thermAmplify lam f ρ) *ᵥ x)).re :=
  (thermPrecompensable_iff lam f hf hρ).trans
    (isDensityMatrix_thermAmplify_iff_pos lam f hf0 hfeven hρ)

/-- **The degenerate-block law, pre-image side** (Tier T1
target): every pre-image agrees with its target on every
zero-gap entry. A deformation that cannot see a block cannot
require the preparation to distort it: on a degenerate block
there is no amplification, possible or needed — the
candidate's entries there are the target's own
(entries of `thermAmplify` at gap `0` carry the factor
`(f 0)⁻¹ = 1`). -/
theorem thermDamp_preimage_apply_of_lam_eq (lam : ι → ℝ) (f : ℝ → ℝ)
    (hf0 : f 0 = 1) {σ ρ : Matrix ι ι ℂ}
    (h : thermDamp lam f σ = ρ) {i j : ι} (hij : lam i = lam j) :
    σ i j = ρ i j := by
  have h1 : ρ i j = thermDamp lam f σ i j := by rw [h]
  rw [h1, thermDamp_apply_of_lam_eq lam f hf0 σ hij]

end Reachability

-- ============================================================================
-- §4. The exponential factor and the widest-gap obstruction
-- ============================================================================

section ExpFactor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The exponential damping factor** (Tier T2, definition):
`expDamp β x = exp (−β|x|)` — the headline thermal factor.
Gap `0` is untouched, the factor is even, positive, and at
most `1` for `β ≥ 0`: the wider the gap, the harder the
damping, priced in units of the inverse temperature `β`. Its
kernel positivity is remainder R1 (see the header); the
obstruction below is stated so as not to need it. -/
noncomputable def expDamp (β : ℝ) : ℝ → ℝ :=
  fun x => Real.exp (-β * |x|)

/-- The exponential factor is even (Tier T1 target): it reads
the gap through `|·|`. -/
theorem expDamp_even (β : ℝ) : ∀ x : ℝ, expDamp β (-x) = expDamp β x := by
  intro x
  simp only [expDamp, abs_neg]

/-- The exponential factor is everywhere positive (Tier T1
target) — in particular nowhere zero, so de-amplification
makes sense at every gap and §3 applies. -/
theorem expDamp_pos (β : ℝ) (x : ℝ) : 0 < expDamp β x :=
  Real.exp_pos _

/-- The exponential factor damps, never amplifies (Tier T1
target): for `β ≥ 0`, `expDamp β x ≤ 1`, with equality at
gap `0`. -/
theorem expDamp_le_one {β : ℝ} (hβ : 0 ≤ β) (x : ℝ) :
    expDamp β x ≤ 1 := by
  have hle : -β * |x| ≤ 0 := by
    have h1 : 0 ≤ β * |x| := mul_nonneg hβ (abs_nonneg x)
    linarith
  calc expDamp β x = Real.exp (-β * |x|) := rfl
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hle
    _ = 1 := Real.exp_zero

/-- **The composition law of the exponential instance**
(Tier T1 target): thermal channels at inverse temperatures
`β₁` and `β₂` compose to the channel at `β₁ + β₂` — the
factors multiply along the SAME gap, `exp(−β₁|g|) ·
exp(−β₂|g|) = exp(−(β₁+β₂)|g|)`. Stated for the exponential
instance only: a general factor family has no such law (its
composition multiplies the factors pointwise, which closes
in the family only for exponentials). The thermal form of
`dephase_comp`. -/
theorem thermDamp_expDamp_comp (lam : ι → ℝ) (β₁ β₂ : ℝ)
    (A : Matrix ι ι ℂ) :
    thermDamp lam (expDamp β₁) (thermDamp lam (expDamp β₂) A)
      = thermDamp lam (expDamp (β₁ + β₂)) A := by
  ext i j
  rw [thermDamp_apply, thermDamp_apply, thermDamp_apply]
  have hfac : ((expDamp β₁ (lam i - lam j) : ℂ))
        * ((expDamp β₂ (lam i - lam j) : ℂ))
      = ((expDamp (β₁ + β₂) (lam i - lam j) : ℂ)) := by
    rw [← Complex.ofReal_mul]
    simp only [expDamp]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, hfac]

end ExpFactor

section Obstruction

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **The sharp thermal obstruction** (Tier T1 target): the
maximally coherent pair state (`PreCompensation.pairPlus`)
across the WIDEST gap — `i` a maximal level, `j` a minimal
level, `spectralWidth lam > 0` — is NOT exactly
pre-compensable under the exponential thermal channel at any
`β > 0`. Its de-amplified candidate, tested against
`eᵢ − eⱼ`, has quadratic form exactly
`1 − exp (β · spectralWidth lam) < 0`: the negative direction
is priced at `1 / f (width) = exp (β · width)`. The widest
coherence is the most expensive tooth to pre-cut, and its
price is the spectral width — compare
`not_precompensable_pairPlus`, where the constant factor
prices the same state at `1 − l⁻¹` uniformly across gaps. -/
theorem not_thermPrecompensable_pairPlus_widest (lam : ι → ℝ)
    {β : ℝ} (hβ : 0 < β) {i j : ι}
    (hi : ∀ k, lam k ≤ lam i) (hj : ∀ k, lam j ≤ lam k)
    (hW : 0 < spectralWidth lam) :
    ¬ ThermPreCompensable lam (expDamp β) (pairPlus i j) := by
  intro hpre
  have hij : i ≠ j := by
    intro h
    subst h
    rw [spectralWidth_eq lam hi hj] at hW
    simp at hW
  have hDM : IsDensityMatrix (pairPlus i j) := isDensityMatrix_pairPlus hij
  have hf : ∀ x : ℝ, expDamp β x ≠ 0 :=
    fun x => ne_of_gt (expDamp_pos β x)
  have hf0 : expDamp β 0 = 1 := by
    simp [expDamp]
  have hpos := (thermPrecompensable_iff_pos lam (expDamp β) hf hf0
    (expDamp_even β) hDM).mp hpre (basisVec i - basisVec j)
  set D : Matrix ι ι ℂ := thermAmplify lam (expDamp β) (pairPlus i j) with hD
  have hfac : ∀ x : ℝ, ((expDamp β x : ℂ))⁻¹
      = ((Real.exp (β * |x|) : ℂ)) := by
    intro x
    rw [← Complex.ofReal_inv]
    congr 1
    simp only [expDamp]
    rw [show -β * |x| = -(β * |x|) by ring, Real.exp_neg, inv_inv]
  have hDii : D i i = 1 / 2 := by
    rw [hD, thermAmplify_apply, hfac]
    have hgap : lam i - lam i = 0 := sub_self _
    rw [hgap]
    simp only [abs_zero, mul_zero, Real.exp_zero, Complex.ofReal_one]
    rw [pairPlus_apply]
    calc ((1 : ℂ)) * (pairVec i j i * star (pairVec i j i))
        = pairVec i j i * star (pairVec i j i) := by simp
      _ = 1 / 2 := pairVec_mul_star i j (Or.inl rfl) (Or.inl rfl)
  have hDjj : D j j = 1 / 2 := by
    rw [hD, thermAmplify_apply, hfac]
    have hgap : lam j - lam j = 0 := sub_self _
    rw [hgap]
    simp only [abs_zero, mul_zero, Real.exp_zero, Complex.ofReal_one]
    rw [pairPlus_apply]
    calc ((1 : ℂ)) * (pairVec i j j * star (pairVec i j j))
        = pairVec i j j * star (pairVec i j j) := by simp
      _ = 1 / 2 := pairVec_mul_star i j (Or.inr rfl) (Or.inr rfl)
  have hgapW : lam i - lam j = spectralWidth lam :=
    (spectralWidth_eq lam hi hj).symm
  have hDij : D i j = ((Real.exp (β * spectralWidth lam) : ℂ)) * (1 / 2) := by
    rw [hD, thermAmplify_apply, hfac, hgapW, abs_of_pos hW, pairPlus_apply]
    congr 1
    exact pairVec_mul_star i j (Or.inl rfl) (Or.inr rfl)
  have hDji : D j i = ((Real.exp (β * spectralWidth lam) : ℂ)) * (1 / 2) := by
    have hgapW' : lam j - lam i = -(spectralWidth lam) := by
      rw [← hgapW]; ring
    rw [hD, thermAmplify_apply, hfac, hgapW', abs_neg, abs_of_pos hW,
      pairPlus_apply]
    congr 1
    exact pairVec_mul_star i j (Or.inr rfl) (Or.inl rfl)
  have hQ : (star (basisVec i - basisVec j)) ⬝ᵥ (D *ᵥ (basisVec i - basisVec j))
      = ((1 - Real.exp (β * spectralWidth lam) : ℝ) : ℂ) := by
    have hsum : ∀ a ∉ ({i, j} : Finset ι),
        (star (basisVec i - basisVec j)) a * (D *ᵥ (basisVec i - basisVec j)) a
          = 0 := by
      intro a ha
      have hai : a ≠ i := fun h => ha (by simp [h])
      have haj : a ≠ j := fun h => ha (by simp [h])
      have hx : (basisVec i - basisVec j) a = 0 := by
        show (if a = i then (1 : ℂ) else 0) - (if a = j then (1 : ℂ) else 0) = 0
        rw [if_neg hai, if_neg haj, sub_zero]
      rw [Pi.star_apply, hx, star_zero, zero_mul]
    have hfi : (star (basisVec i - basisVec j)) i
        * (D *ᵥ (basisVec i - basisVec j)) i
        = 1 / 2 - ((Real.exp (β * spectralWidth lam) : ℂ)) * (1 / 2) := by
      have hx1 : (basisVec i - basisVec j) i = 1 := by
        show (if i = i then (1 : ℂ) else 0) - (if i = j then (1 : ℂ) else 0) = 1
        rw [if_pos rfl, if_neg hij, sub_zero]
      have hmv1 : (D *ᵥ (basisVec i - basisVec j)) i = D i i - D i j := by
        rw [Matrix.mulVec_sub, Pi.sub_apply, mulVec_basisVec, mulVec_basisVec]
      rw [Pi.star_apply, hx1, star_one, one_mul, hmv1, hDii, hDij]
    have hfj : (star (basisVec i - basisVec j)) j
        * (D *ᵥ (basisVec i - basisVec j)) j
        = 1 / 2 - ((Real.exp (β * spectralWidth lam) : ℂ)) * (1 / 2) := by
      have hx2 : (basisVec i - basisVec j) j = -1 := by
        show (if j = i then (1 : ℂ) else 0) - (if j = j then (1 : ℂ) else 0) = -1
        rw [if_neg (Ne.symm hij), if_pos rfl, zero_sub]
      have hmv2 : (D *ᵥ (basisVec i - basisVec j)) j = D j i - D j j := by
        rw [Matrix.mulVec_sub, Pi.sub_apply, mulVec_basisVec, mulVec_basisVec]
      rw [Pi.star_apply, hx2, hmv2, hDji, hDjj]
      simp only [star_neg, star_one]
      ring
    show (∑ a, (star (basisVec i - basisVec j)) a
        * (D *ᵥ (basisVec i - basisVec j)) a)
        = ((1 - Real.exp (β * spectralWidth lam) : ℝ) : ℂ)
    rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset ι))
      (fun a _ ha => hsum a ha), Finset.sum_pair hij, hfi, hfj]
    push_cast
    ring
  rw [hQ, Complex.ofReal_re] at hpos
  have hgt : (1 : ℝ) < Real.exp (β * spectralWidth lam) := by
    rw [Real.one_lt_exp_iff]
    exact mul_pos hβ hW
  linarith

end Obstruction

end ThetLogos
