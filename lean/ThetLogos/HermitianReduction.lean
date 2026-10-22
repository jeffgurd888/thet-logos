import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import ThetLogos.ThermalKernel
import ThetLogos.SpectralClock

open Matrix Finset MeasureTheory

namespace ThetLogos

/-!
# ThetLogos.HermitianReduction — the general-Hermitian reduction (T1 target)

HONESTY LEDGER (read before citing):

- Status: **VERIFIED — STANDS WHOLE (T1), compiled green
  2026-10-21** (`lake build ThetLogos.HermitianReduction`, 3,583
  jobs, 0 errors), parent-verified on the exact shipped text
  (`.olean` present, strict recount 16, incompleteness census 0 on
  comment-stripped source, axioms on the six checked headline
  theorems standard only: `propext`, `Classical.choice`,
  `Quot.sound`). Kill condition K1 did NOT trigger: the full
  transport stands as drafted, no narrowing. Repairs in the open,
  no statement's content changed: the exponential is spelled
  `NormedSpace.exp x` (this pin takes no field argument; the
  drafted `NormedSpace.exp ℂ x` does not elaborate — the corpus's
  own spelling, e.g. in `FlowKernel`); `hermitian_eigenvector`
  closes by the Mathlib term itself (already cast-form in this
  pin); and `heatKernelGen_add` is proved directly (scalar split
  + `Matrix.exp_add_of_commute`) rather than by the drafted
  diagonal route — its statement never mentions Hermiticity, so
  the semigroup law in fact holds for every matrix, and its
  docstring now says so. Full repair log: dossier
  `whitepaper/hermitian-reduction-2026-10-21.md`.
- What this brick is: the named shared remainder of three standing
  bricks — `ResonanceSpectrum`, `SpectralClock`, `ThermalKernel` —
  each proved for a DIAGONAL generator (an eigenvalue function
  `lam : ι → ℝ`). Here the generator is a general finite Hermitian
  matrix `K` over `ℂ`, and the diagonal conclusions are TRANSPORTED
  along the spectral decomposition. The transport machinery is
  Mathlib's spectral theorem for Hermitian matrices
  (`Matrix.IsHermitian.spectral_theorem`, pinned Mathlib
  v4.35.0-rc3): `K = U * diagonal (eigenvalues) * star U` with `U`
  the eigenvector unitary. Nothing new is diagonalised by hand;
  the work is the conjugation calculus and the honest bookkeeping
  of what the transport does and does not carry.
- What transports (targets): (a) the spectrum of `K` is the range
  of its eigenvalue function (Mathlib's own
  `spectrum_real_eq_range_eigenvalues`, recorded here); every
  eigenvalue value is attained at an explicit eigenvector, the
  corresponding column of `U`. (b) The matrix exponential
  conjugates: `exp (U * A * star U) = U * exp A * star U`, hence
  the heat kernel of `K` is the conjugate of the diagonal
  schedule kernel, `exp (-tK) = U * diag (exp (-t * d i)) * star U`.
  (c) The TRACE schedule and the semigroup law transport verbatim,
  and the payoff statements hold for `K`'s eigenvalue function
  exactly as `ThermalKernel` states them for a diagonal `lam`.
  (d) The clock transports IN THE EIGENBASIS: with the flow of `K`
  defined as conjugation of `phaseFlow` by `U`, the widest
  eigenbasis coherence is negated at the master tick
  `π / spectralWidth (eigenvalues)` and at no earlier positive
  time, and stationarity transports as a statement about
  eigenbasis entries.
- Named remainders (what does NOT transport — K3):
  R1. Entry-level statements in the ORIGINAL basis. The flip,
  firstness, and stationarity conclusions are about the entries
  of `star U * A * U` (the eigenbasis picture of `A`), not about
  the entries of `A` itself. No original-basis entry statement
  is claimed or implied.
  R2. The jewel in non-diagonal form. `ThermalKernel`'s
  `e^{-K} = ρ` at `t = 1` is stated for a diagonal state. For a
  non-diagonal density matrix, `K = -ln ρ` needs a matrix
  logarithm (functional calculus for `log`), which this brick
  does NOT touch: only `exp` is transported, by conjugation.
- Fences. Finite level only: finite index type, finite Hermitian
  matrix over `ℂ`. No continuum generator, no unbounded operator,
  no functional calculus beyond conjugation of `exp` and the
  diagonal kernel. The tick is a property of `K`'s spectrum, not
  of spacetime. Nothing here touches Yang–Mills or any
  Millennium statement.
- Pre-named kill conditions. K1: if the transport needs a
  functional calculus beyond conjugation of `exp` in this pin,
  the brick narrows to what transports (trace + width) and says
  so. (Scoping found `Matrix.exp_units_conj`, `Matrix.exp_conj`,
  and `Matrix.exp_diagonal` in the pin, so the full route is
  drafted; K1 is the compile-time narrowing rule.) K2: any
  placeholder proof, and this file does not count. K3: any
  diagonal statement whose shape does not transport is named a
  remainder in this header (done: R1, R2), never silently dropped.
-/

-- ============================================================================
-- §0. Setup and the spectral form
-- ============================================================================

section Setup

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Matrix ι ι ℂ} (hK : K.IsHermitian)

/-- **The spectral form of a Hermitian generator** (Tier T1 target):
`K = U * diagonal (eigenvalues) * star U`, where `U` is Mathlib's
eigenvector unitary. Unpacking of
`Matrix.IsHermitian.spectral_theorem` (which states the form via
`conjStarAlgAut`) into plain matrix products. -/
theorem hermitian_spectral_form :
    K = (hK.eigenvectorUnitary : Matrix ι ι ℂ)
        * Matrix.diagonal (fun i => ((hK.eigenvalues i : ℂ)))
        * star (hK.eigenvectorUnitary : Matrix ι ι ℂ) := by
  have h := hK.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  exact h

/-- **Eigenvectors of a Hermitian generator** (Tier T1 target): the
`i`-th eigenvector basis vector is an eigenvector of `K` with
eigenvalue `hK.eigenvalues i` (real, cast to `ℂ`). The vector is
the `i`-th column of the eigenvector unitary
(`Matrix.IsHermitian.eigenvectorUnitary_apply`). Transport of
Mathlib's `Matrix.IsHermitian.mulVec_eigenvectorBasis`, with the
real scalar action rewritten as the cast complex one. -/
theorem hermitian_eigenvector (i : ι) :
    K *ᵥ ⇑(hK.eigenvectorBasis i)
      = ((hK.eigenvalues i : ℂ)) • ⇑(hK.eigenvectorBasis i) :=
  hK.mulVec_eigenvectorBasis i

/-- **The spectrum of `K` is its eigenvalue function** (Tier T1
target): the `ℝ`-spectrum of a Hermitian matrix is exactly the
range of its eigenvalue function — every eigenvalue is attained
and there are no others. This is Mathlib's
`Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`, recorded
here as the bridge the rest of the brick stands on: the width,
tick, and payoff statements below are about `hK.eigenvalues`,
and by this theorem that function IS the spectrum of `K`. -/
theorem hermitian_spectrum_real :
    spectrum ℝ K = Set.range hK.eigenvalues :=
  hK.spectrum_real_eq_range_eigenvalues

end Setup

-- ============================================================================
-- §1. The conjugation calculus
-- ============================================================================

section Conjugation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Exponential conjugation** (Tier T1 target): for a matrix `U`
whose conjugate transpose is its two-sided inverse, the matrix
exponential conjugates:
`exp (U * A * star U) = U * exp A * star U`. Proved through
Mathlib's `Matrix.exp_units_conj` at the explicit unit
`⟨U, star U, hU', hU⟩`, whose coercion and inverse coercion are
`U` and `star U` by construction. -/
theorem exp_conj_star (U A : Matrix ι ι ℂ) (hU : star U * U = 1)
    (hU' : U * star U = 1) :
    NormedSpace.exp (U * A * star U)
      = U * NormedSpace.exp A * star U :=
  Matrix.exp_units_conj (⟨U, star U, hU', hU⟩ : (Matrix ι ι ℂ)ˣ) A

/-- Conjugate of a product of conjugates (Tier T1 target): the
middle unitary pair cancels. Pure associativity plus `hU`. -/
theorem conj_mul_conj (U X Y : Matrix ι ι ℂ) (hU : star U * U = 1) :
    (U * X * star U) * (U * Y * star U) = U * (X * Y) * star U := by
  have h : (U * X * star U) * (U * Y * star U)
      = U * (X * (star U * U) * Y) * star U := by
    simp only [Matrix.mul_assoc]
  rw [h, hU, Matrix.mul_one]

/-- Collapsing a conjugation round trip, left form (Tier T1
target): `star U * (U * X * star U) * U = X`. -/
theorem star_conj_collapse (U X : Matrix ι ι ℂ) (hU : star U * U = 1) :
    star U * (U * X * star U) * U = X := by
  have h : star U * (U * X * star U) * U
      = (star U * U) * X * (star U * U) := by
    simp only [Matrix.mul_assoc]
  rw [h, hU, Matrix.one_mul, Matrix.mul_one]

/-- Collapsing a conjugation round trip, right form (Tier T1
target): `U * (star U * X * U) * star U = X`. Needs both unitary
identities. -/
theorem conj_star_collapse (U X : Matrix ι ι ℂ) (hU : star U * U = 1)
    (hU' : U * star U = 1) :
    U * (star U * X * U) * star U = X := by
  have h : U * (star U * X * U) * star U
      = (U * star U) * X * (U * star U) := by
    simp only [Matrix.mul_assoc]
  rw [h, hU', Matrix.one_mul, Matrix.mul_one]

end Conjugation

-- ============================================================================
-- §2. The heat kernel of a general Hermitian generator
-- ============================================================================

section HeatKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Matrix ι ι ℂ} (hK : K.IsHermitian)

/-- The complex diagonal schedule kernel of an eigenvalue function
`d`: the diagonal matrix whose `i`-th entry is the cast of the
`i`-th mode's real schedule `exp (-t * d i)`. This is
`ThermalKernel.heatKernel` read over `ℂ`. Tier T2 (definition). -/
noncomputable def hermitianDiagKernel (d : ι → ℝ) (t : ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => ((Real.exp (-t * d i) : ℝ) : ℂ))

/-- **The heat kernel of a general Hermitian generator** (Tier T2,
definition): `exp (-tK)`, the matrix exponential of the scaled
generator. No Hermiticity is needed for the definition; the
theorems use it. -/
noncomputable def heatKernelGen (K : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  NormedSpace.exp ((-(t : ℂ)) • K)

/-- **The transported kernel** (Tier T1 target): the heat kernel of
a Hermitian generator is the conjugate of its diagonal schedule
kernel,
`exp (-tK) = U * diag (exp (-t * d i)) * star U`
with `d = hK.eigenvalues`. The functional calculus of `K` at
`exp (-t * ·)` is the diagonal calculus conjugated — this is the
reduction the three diagonal bricks named as their remainder. -/
theorem heatKernelGen_eq_conj (t : ℝ) :
    heatKernelGen K t
      = (hK.eigenvectorUnitary : Matrix ι ι ℂ)
        * hermitianDiagKernel hK.eigenvalues t
        * star (hK.eigenvectorUnitary : Matrix ι ι ℂ) := by
  have hsmul : (-(t : ℂ)) • K
      = (hK.eigenvectorUnitary : Matrix ι ι ℂ)
        * ((-(t : ℂ)) • Matrix.diagonal (fun i => ((hK.eigenvalues i : ℂ))))
        * star (hK.eigenvectorUnitary : Matrix ι ι ℂ) := by
    conv_lhs => rw [hermitian_spectral_form hK]
    rw [mul_smul_comm, smul_mul_assoc]
  have hdiag : (-(t : ℂ)) • Matrix.diagonal (fun i => ((hK.eigenvalues i : ℂ)))
      = Matrix.diagonal (fun i => (-(t : ℂ)) * ((hK.eigenvalues i : ℂ))) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
    · simp [Matrix.diagonal_apply, h, Matrix.smul_apply, smul_eq_mul]
  have key : ∀ z : ℝ,
      NormedSpace.exp ((-(t : ℂ)) * ((z : ℂ)))
        = ((Real.exp (-t * z) : ℝ) : ℂ) := by
    intro z
    have harg : (-(t : ℂ)) * ((z : ℂ)) = ((-t * z : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, Complex.ofReal_exp]
    exact congrFun Complex.exp_eq_exp_ℂ.symm _
  unfold heatKernelGen
  rw [hsmul, exp_conj_star _ _ (Unitary.coe_star_mul_self _)
    (Unitary.coe_mul_star_self _), hdiag, Matrix.exp_diagonal]
  have hfun : NormedSpace.exp (fun i => (-(t : ℂ)) * ((hK.eigenvalues i : ℂ)))
      = (fun i => ((Real.exp (-t * hK.eigenvalues i) : ℝ) : ℂ)) := by
    funext i
    rw [Pi.coe_exp]
    exact key _
  unfold hermitianDiagKernel
  rw [hfun]

/-- **Trace transport, abstract form** (Tier T1 target): for any
`U` with `star U * U = 1`, the trace of the conjugated diagonal
schedule kernel is the cast of the diagonal trace sum. Only the
left unitary identity is needed: the trace cycles the right
factor to the front. -/
theorem trace_conj_diagKernel (U : Matrix ι ι ℂ) (hU : star U * U = 1)
    (d : ι → ℝ) (t : ℝ) :
    Matrix.trace (U * hermitianDiagKernel d t * star U)
      = ((∑ i, Real.exp (-t * d i) : ℝ) : ℂ) := by
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  unfold hermitianDiagKernel
  rw [Matrix.trace_diagonal]
  exact (RCLike.ofReal_sum Finset.univ _).symm

/-- **The trace schedule transports** (Tier T1 target): the trace
of the heat kernel of a general Hermitian `K` is the cast of the
diagonal kernel's trace at `K`'s eigenvalue function:
`trace (exp (-tK)) = ((trace (heatKernel (eigenvalues) t) : ℝ) : ℂ)`,
and hence, by `ThermalKernel.heatKernel_trace`, the sum of the
mode schedules of `K`'s spectrum. -/
theorem heatKernelGen_trace (t : ℝ) :
    Matrix.trace (heatKernelGen K t)
      = ((Matrix.trace (heatKernel hK.eigenvalues t) : ℝ) : ℂ) := by
  rw [heatKernelGen_eq_conj hK t,
    trace_conj_diagKernel _ (Unitary.coe_star_mul_self _) _ _,
    heatKernel_trace]

/-- **The semigroup law** (Tier T1 — proved): the heat kernel
composes, `exp (-(t + s)K) = exp (-tK) * exp (-sK)`. Proved
directly — split the scalar, the two multiples of `K` commute,
`Matrix.exp_add_of_commute` — so Hermiticity is not needed and
the statement is recorded without it: the law holds for every
matrix. (The drafted proof transported via the diagonal
schedules and `conj_mul_conj`; that route could not elaborate,
because this statement never puts `hK` in scope. The direct
proof is stronger and shorter; the swap is recorded here and
in the dossier, in the open.) -/
theorem heatKernelGen_add (t s : ℝ) :
    heatKernelGen K (t + s) = heatKernelGen K t * heatKernelGen K s := by
  have hsplit : (-(((t + s : ℝ)) : ℂ)) • K
      = (-(t : ℂ)) • K + (-(s : ℂ)) • K := by
    rw [← add_smul]
    congr 1
    push_cast
    ring
  have hcomm : Commute ((-(t : ℂ)) • K) ((-(s : ℂ)) • K) :=
    ((Commute.refl K).smul_left (-(t : ℂ))).smul_right (-(s : ℂ))
  unfold heatKernelGen
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm]

/-- **The payoff transports** (Tier T1 target): the summed payoff
of a general Hermitian generator's positive modes is the sum of
their reciprocals — `ThermalKernel.integral_sum_exp_neg_mul_Ioi`
stated at `K`'s eigenvalue function. No new analysis: the
transport content is that the diagonal payoff theorem applies
verbatim to the spectrum of `K` (by `hermitian_spectrum_real`,
that function IS `K`'s spectrum). The full trace's payoff
integral is NOT stated: zero modes pay at rate `1` forever, so
it diverges — exactly the reason `ThermalKernel`'s payoff is
filtered to positive modes, a shape the transport inherits. -/
theorem hermitian_payoff_sum :
    ∫ t : ℝ in Set.Ioi 0,
        ∑ i ∈ Finset.univ.filter (fun i => 0 < hK.eigenvalues i),
          Real.exp (-t * hK.eigenvalues i)
      = ∑ i ∈ Finset.univ.filter (fun i => 0 < hK.eigenvalues i),
          (hK.eigenvalues i)⁻¹ :=
  integral_sum_exp_neg_mul_Ioi _

end HeatKernel

-- ============================================================================
-- §3. The clock of a general Hermitian generator (eigenbasis form)
-- ============================================================================

section Clock

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {K : Matrix ι ι ℂ} (hK : K.IsHermitian)

/-- **The flow of a general Hermitian generator** (Tier T2,
definition): conjugation of the diagonal phase flow by the
eigenvector unitary — pull `A` into the eigenbasis, run
`phaseFlow` at `K`'s eigenvalue function, push back. This is the
flow the diagonal clock's theorems transport to. -/
noncomputable def genFlow (hK : K.IsHermitian) (t : ℝ) (A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  (hK.eigenvectorUnitary : Matrix ι ι ℂ)
    * phaseFlow hK.eigenvalues t
      (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * A
        * (hK.eigenvectorUnitary : Matrix ι ι ℂ))
    * star (hK.eigenvectorUnitary : Matrix ι ι ℂ)

/-- **The eigenbasis picture of the flow** (Tier T1 target):
pulling the transported flow back into the eigenbasis recovers
the diagonal phase flow exactly. Every clock statement below is
this identity composed with a `SpectralClock` theorem. -/
theorem genFlow_eigenbasis (t : ℝ) (A : Matrix ι ι ℂ) :
    star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * genFlow hK t A
        * (hK.eigenvectorUnitary : Matrix ι ι ℂ)
      = phaseFlow hK.eigenvalues t
          (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * A
            * (hK.eigenvectorUnitary : Matrix ι ι ℂ)) :=
  star_conj_collapse _ _ (Unitary.coe_star_mul_self _)

/-- **Stationarity transports** (Tier T1 target): a matrix is
fixed by the flow of `K` at all times iff every eigenbasis entry
between distinct eigenvalues of `K` vanishes — the eigenbasis
form of `ResonanceSpectrum.phaseFlow_stationary_iff`. Per
remainder R1, this is a statement about the eigenbasis entries
of `A`, not its original-basis entries. -/
theorem genFlow_stationary_iff (A : Matrix ι ι ℂ) :
    (∀ t : ℝ, genFlow hK t A = A)
      ↔ ∀ i j, hK.eigenvalues i ≠ hK.eigenvalues j →
          (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * A
            * (hK.eigenvectorUnitary : Matrix ι ι ℂ)) i j = 0 := by
  constructor
  · intro h i j hij
    have hB : ∀ t : ℝ, phaseFlow hK.eigenvalues t
        (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * A
          * (hK.eigenvectorUnitary : Matrix ι ι ℂ))
        = star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * A
          * (hK.eigenvectorUnitary : Matrix ι ι ℂ) := by
      intro t
      rw [← genFlow_eigenbasis hK t A, h t]
    exact (phaseFlow_stationary_iff hK.eigenvalues _).mp hB i j hij
  · intro h t
    have hB : ∀ t : ℝ, phaseFlow hK.eigenvalues t
        (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * A
          * (hK.eigenvectorUnitary : Matrix ι ι ℂ))
        = star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * A
          * (hK.eigenvectorUnitary : Matrix ι ι ℂ) :=
      (phaseFlow_stationary_iff hK.eigenvalues _).mpr h
    calc genFlow hK t A
        = (hK.eigenvectorUnitary : Matrix ι ι ℂ)
            * (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * A
              * (hK.eigenvectorUnitary : Matrix ι ι ℂ))
            * star (hK.eigenvectorUnitary : Matrix ι ι ℂ) := by
          unfold genFlow
          rw [hB t]
      _ = A := conj_star_collapse _ _
          (Unitary.coe_star_mul_self _) (Unitary.coe_mul_star_self _)

/-- **The master tick transports — the extremal flip** (Tier T1
target): at the master tick `π / spectralWidth (eigenvalues)` of
a general Hermitian generator, the widest eigenbasis coherence
is negated: for `i` a maximal and `j` a minimal eigenvalue
index, the `(i, j)` entry of the eigenbasis picture of
`genFlow` at the tick is minus the `(i, j)` entry of the
eigenbasis picture of `A`. The width and the tick are read off
`K`'s eigenvalue function, which by `hermitian_spectrum_real`
is `K`'s spectrum — the same numbers the diagonal clock reads.
Per remainder R1, the negated entry is an eigenbasis entry. -/
theorem genFlow_masterTick_apply (hW : 0 < spectralWidth hK.eigenvalues)
    (A : Matrix ι ι ℂ) {i j : ι}
    (hi : ∀ k, hK.eigenvalues k ≤ hK.eigenvalues i)
    (hj : ∀ k, hK.eigenvalues j ≤ hK.eigenvalues k) :
    (star (hK.eigenvectorUnitary : Matrix ι ι ℂ)
        * genFlow hK (masterTick hK.eigenvalues) A
        * (hK.eigenvectorUnitary : Matrix ι ι ℂ)) i j
      = - (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * A
          * (hK.eigenvectorUnitary : Matrix ι ι ℂ)) i j := by
  rw [genFlow_eigenbasis]
  exact phaseFlow_masterTick_apply _ hW _ hi hj

/-- **The master tick transports — firstness** (Tier T1 target):
the master tick of a general Hermitian generator is the FIRST
positive flip time of its widest eigenbasis coherence: at any
`0 < t < π / spectralWidth (eigenvalues)`, no nonzero widest
eigenbasis coherence is negated. Eigenbasis form of
`SpectralClock.phaseFlow_masterTick_first`; per remainder R1,
no original-basis firstness is claimed. -/
theorem genFlow_masterTick_first (hW : 0 < spectralWidth hK.eigenvalues)
    (A : Matrix ι ι ℂ) {i j : ι}
    (hi : ∀ k, hK.eigenvalues k ≤ hK.eigenvalues i)
    (hj : ∀ k, hK.eigenvalues j ≤ hK.eigenvalues k)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < masterTick hK.eigenvalues)
    (hA : (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * A
      * (hK.eigenvectorUnitary : Matrix ι ι ℂ)) i j ≠ 0) :
    (star (hK.eigenvectorUnitary : Matrix ι ι ℂ)
        * genFlow hK t A * (hK.eigenvectorUnitary : Matrix ι ι ℂ)) i j
      ≠ - (star (hK.eigenvectorUnitary : Matrix ι ι ℂ) * A
          * (hK.eigenvectorUnitary : Matrix ι ι ℂ)) i j := by
  rw [genFlow_eigenbasis]
  exact phaseFlow_masterTick_first _ hW _ hi hj ht0 ht1 hA

end Clock

end ThetLogos
