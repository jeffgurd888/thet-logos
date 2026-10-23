import Mathlib.Tactic
import ThetLogos.TeslaVortexMultiSector
import ThetLogos.GibbsSpan
import ThetLogos.NullStart

namespace ThetLogos.ModularVariance

/-!
# ThetLogos.ModularVariance — the distance-from-the-void dial

STATUS: STANDS WHOLE (T1) — landed 2026-10-23 by parent review:
targeted in-tree build green on the shipped text, strict recount,
placeholder census, `#print axioms` standard-only on the headline
declarations. All four charter targets stand, T4 included, with one
precision on the face (the modular dial is faithful at `β ≠ 0`;
`β = 0` collapses it — proved, not hidden). Commissioned by Jeff
2026-10-22 23:10 EDT ("build this the right way — no q-toy hacks,
no clamping, and no circular Lean axioms"). Charter:
`whitepaper/modular-variance-scoping-2026-10-22.md`; dossier:
`whitepaper/modular-variance-2026-10-23.md`. Salvaged from
two dropped packages audited the same evening (verdicts HOLD): both
stubs *assumed* the non-negativity of the variance (as a class field
in one, as a structure field in the other). This brick derives it.

## NO CLAIM

NO CLAIM beyond the finite identities proved below. In particular
NO CLAIM on any Millennium statement, and no claim about any
continuum or von Neumann-algebra modular theory (fence K-MV1).

## The statement, at the tier it can carry

For a finite Gibbs state — sectors `ι` (finite, nonempty), INPUT
energies `E : ι → ℝ`, inverse temperature `β` — the corpus's modular
Hamiltonian is, by GibbsSpan's proved form, the diagonal matrix
`K = diagModularK (gibbsWeightsE β E logZ)` with diagonal entries
`β • Eᵢ + logZ` (`GibbsSpan.gibbsK_apply_diag`), where here
`logZ = log (partition sum)`. The **modular variance** is the
variance of those eigenvalues under the Gibbs state itself:

    `Var_β(K) = β² • Var_β(E)`,

the variance of the modular Hamiltonian is `β²` times the variance
of the energy — an exact finite identity (Target T1). The energy
variance is nonnegative by derivation, not by assumption: it is a
sum of squares weighted by strictly positive Gibbs weights
(Target T2). And the dial is faithful (Target T3): the variance
reads zero exactly at the degenerate state — all energies equal —
which is NullStart's silent state (`silent_iff_varModular_eq_zero`
welds the dial to the silence directly), and reads strictly
positive exactly when a gap exists. Variance is the
distance-from-the-void dial of the finite box. Target T4 (stretch)
is the fluctuation–response identity `d⟨E⟩/dβ = −Var_β(E)`.

## Route

Eigenvalue-level, as the charter permits: the variance is computed
from GibbsSpan's proved diagonal form of `K`. The weld to
GibbsSpan's matrix is `modEigen_eq_gibbsK_diag` (the eigenvalues
used here ARE the diagonal entries of the corpus's `K`). No new
matrix-variance machinery is introduced.

## Fences (on the face, per the charter)

- **K-MV1.** Finite Gibbs states only. "Modular Hamiltonian" is the
  corpus's finite `diagModularK` in GibbsSpan's proved form — NOT
  the Tomita–Takesaki modular operator of a von Neumann algebra.
- **K-MV2.** No heat-kernel coefficients anywhere: no `a₀`/`a₂`, no
  specific heat "extracted" from them. The finite heat-capacity
  analog, if named at all, is `β² • Var_β(E)` itself — defined
  here, not extracted (it is `varModular`).
- **K-MV3.** No q-deformation, no non-Hermitian operators, no
  clamping: every quantity is computed from a genuine state
  (strictly positive Gibbs weights, `gibbsProb_pos`), and the
  variance's non-negativity is a theorem (`gibbsVar_nonneg`), not
  a rounding instruction.
- **The `β = 0` precision.** T1–T3 for the ENERGY dial hold at
  every real `β` (Gibbs weights are positive at every `β`). For
  the MODULAR dial, `β = 0` collapses `K` to the scalar
  `logZ • 1`, so `Var₀(K) = 0` identically (`varModular_zero_beta`)
  and carries no information about `E`; the faithfulness
  statements for `Var(K)` therefore carry the hypothesis `β ≠ 0`
  on their face. This is T1's own content at `β = 0`, stated, not
  hidden.

## Tier map

- T2 (definitions): `partSum`, `gibbsProb`, `gibbsExpect`,
  `gibbsVar`, `meanEnergy`, `varEnergy`, `modEigen`, `varModular`.
- T1 (targets): every theorem below; T1 = `varModular_eq`,
  T2 = `gibbsVar_nonneg` and its corollaries, T3 = the zero/positivity
  iffs and the NullStart silence weld, T4 = `hasDerivAt_meanEnergy`.

## Contents

- §0: the finite Gibbs state as a probability distribution, its
  expectation functional, and the variance definitions.
- §1: state lemmas — positivity and normalization of the weights,
  linearity of the expectation, ratio forms.
- §2: variance algebra — the second-moment form, affine covariance,
  TARGET T1, and the GibbsSpan eigenvalue weld.
- §3: TARGET T2 — non-negativity, derived.
- §4: TARGET T3 — the dial reads the void (zero/positivity iffs,
  the NullStart silence weld).
- §5: TARGET T4 (stretch) — fluctuation response.
-/

variable {ι : Type*} [Fintype ι] [Nonempty ι]

-- ============================================================================
-- §0. The finite Gibbs state, expectation, and variance (definitions)
-- ============================================================================

/-- **Partition sum** (Tier T2 — definition): `Z(E, β) = Σᵢ e^{−βEᵢ}`,
the normalizer of the finite Gibbs state at INPUT energies
`E : ι → ℝ` and inverse temperature `β`. This is the denominator of
`TeslaVortexMultiSector.sepN`. -/
noncomputable def partSum (E : ι → ℝ) (β : ℝ) : ℝ :=
  ∑ i, Real.exp (-(β * E i))

/-- **Gibbs probability** (Tier T2 — definition): the probability
of sector `i` in the finite Gibbs state,
`pᵢ = e^{−βEᵢ} / Z(E, β)`. Strictly positive at every `β`
(`gibbsProb_pos`) and normalized (`sum_gibbsProb`): a genuine
state, per fence K-MV3. -/
noncomputable def gibbsProb (E : ι → ℝ) (β : ℝ) (i : ι) : ℝ :=
  Real.exp (-(β * E i)) / partSum E β

/-- **Gibbs expectation** (Tier T2 — definition): the expectation
of an observable `X : ι → ℝ` under the finite Gibbs state,
`⟨X⟩_β = Σᵢ pᵢ Xᵢ`. -/
noncomputable def gibbsExpect (E : ι → ℝ) (β : ℝ) (X : ι → ℝ) : ℝ :=
  ∑ i, gibbsProb E β i * X i

/-- **Gibbs variance** (Tier T2 — definition): the variance of an
observable `X` under the finite Gibbs state, in the sum-of-squares
form `⟨(X − ⟨X⟩)²⟩_β` — the form from which non-negativity is
DERIVED in §3 (Target T2), never assumed. -/
noncomputable def gibbsVar (E : ι → ℝ) (β : ℝ) (X : ι → ℝ) : ℝ :=
  gibbsExpect E β (fun i => (X i - gibbsExpect E β X) ^ 2)

/-- **Mean energy** (Tier T2 — definition): `⟨E⟩_β`, the Gibbs
expectation of the energy observable. -/
noncomputable def meanEnergy (E : ι → ℝ) (β : ℝ) : ℝ :=
  gibbsExpect E β E

/-- **Energy variance** (Tier T2 — definition): `Var_β(E)`, the
Gibbs variance of the energy observable — the energy-side reading
of the distance-from-the-void dial. -/
noncomputable def varEnergy (E : ι → ℝ) (β : ℝ) : ℝ :=
  gibbsVar E β E

/-- **Modular eigenvalue** (Tier T2 — definition): the `i`-th
eigenvalue of the Gibbs state's modular Hamiltonian in GibbsSpan's
proved form: `β • Eᵢ + log Z(E, β)`. That these are literally the
diagonal entries of the corpus's `diagModularK` is
`modEigen_eq_gibbsK_diag` (§2). -/
noncomputable def modEigen (E : ι → ℝ) (β : ℝ) (i : ι) : ℝ :=
  β * E i + Real.log (partSum E β)

/-- **Modular variance** (Tier T2 — definition): `Var_β(K)`, the
Gibbs variance of the modular eigenvalues — the dial itself. By
Target T1 it equals `β² • Var_β(E)`; by fence K-MV2 it is also the
only heat-capacity analog this brick names. -/
noncomputable def varModular (E : ι → ℝ) (β : ℝ) : ℝ :=
  gibbsVar E β (modEigen E β)

-- ============================================================================
-- §1. State lemmas: positivity, normalization, linearity, ratio forms
-- ============================================================================

/-- The partition sum is positive at every real `β` (Tier T1 —
proved): a sum of positive exponentials over a nonempty index —
the landed denominator lemma of `TeslaVortexMultiSector`, read off
for `partSum`. -/
theorem partSum_pos (E : ι → ℝ) (β : ℝ) : 0 < partSum E β :=
  ThetLogos.TeslaVortexMultiSector.sepN_denominator_pos E β

/-- The partition sum is nonzero at every `β` (Tier T1 — proved). -/
theorem partSum_ne_zero (E : ι → ℝ) (β : ℝ) : partSum E β ≠ 0 :=
  ne_of_gt (partSum_pos E β)

/-- Every Gibbs probability is strictly positive, at every sector
and every `β` (Tier T1 — proved): the weights are exponentials over
a positive normalizer. This positivity is the engine of both the
derived non-negativity (§3) and the dial's faithfulness (§4). -/
theorem gibbsProb_pos (E : ι → ℝ) (β : ℝ) (i : ι) : 0 < gibbsProb E β i :=
  div_pos (Real.exp_pos _) (partSum_pos E β)

/-- The Gibbs probabilities are normalized (Tier T1 — proved):
`Σᵢ pᵢ = 1` — the Gibbs state is a genuine probability
distribution (fence K-MV3). -/
theorem sum_gibbsProb (E : ι → ℝ) (β : ℝ) : ∑ i, gibbsProb E β i = 1 := by
  show (∑ i, Real.exp (-(β * E i)) / partSum E β) = 1
  rw [← Finset.sum_div]
  show partSum E β / partSum E β = 1
  exact div_self (partSum_ne_zero E β)

/-- Expectation of a constant is the constant (Tier T1 — proved). -/
theorem gibbsExpect_const (E : ι → ℝ) (β : ℝ) (c : ℝ) :
    gibbsExpect E β (fun _ => c) = c := by
  show (∑ i, gibbsProb E β i * c) = c
  rw [← Finset.sum_mul, sum_gibbsProb, one_mul]

omit [Nonempty ι] in
/-- Expectation commutes with constant multiples (Tier T1 —
proved): `⟨a • X⟩_β = a • ⟨X⟩_β`. -/
theorem gibbsExpect_const_mul (E : ι → ℝ) (β : ℝ) (X : ι → ℝ) (a : ℝ) :
    gibbsExpect E β (fun i => a * X i) = a * gibbsExpect E β X := by
  show (∑ i, gibbsProb E β i * (a * X i)) = a * ∑ i, gibbsProb E β i * X i
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- Expectation is affine (Tier T1 — proved):
`⟨a • X + b⟩_β = a • ⟨X⟩_β + b` for constant `b` — the linearity
the variance algebra of §2 runs on. -/
theorem gibbsExpect_affine (E : ι → ℝ) (β : ℝ) (X : ι → ℝ) (a b : ℝ) :
    gibbsExpect E β (fun i => a * X i + b)
      = a * gibbsExpect E β X + b := by
  have hterm : ∀ i, gibbsProb E β i * (a * X i + b)
      = a * (gibbsProb E β i * X i) + b * gibbsProb E β i :=
    fun i => by ring
  show (∑ i, gibbsProb E β i * (a * X i + b))
      = a * (∑ i, gibbsProb E β i * X i) + b
  calc (∑ i, gibbsProb E β i * (a * X i + b))
      = ∑ i, (a * (gibbsProb E β i * X i) + b * gibbsProb E β i) :=
        Finset.sum_congr rfl (fun i _ => hterm i)
    _ = a * (∑ i, gibbsProb E β i * X i) + b * (∑ i, gibbsProb E β i) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = a * (∑ i, gibbsProb E β i * X i) + b := by
        rw [sum_gibbsProb, mul_one]

/-- The mean of the modular eigenvalues (Tier T1 — proved):
`⟨K⟩_β = β • ⟨E⟩_β + log Z` — the scalar `log Z` passes through
the expectation untouched, the first sign that it cannot move the
variance. -/
theorem gibbsExpect_modEigen (E : ι → ℝ) (β : ℝ) :
    gibbsExpect E β (modEigen E β)
      = β * meanEnergy E β + Real.log (partSum E β) :=
  gibbsExpect_affine E β E β (Real.log (partSum E β))

omit [Nonempty ι] in
/-- Ratio form of the expectation (Tier T1 — proved):
`⟨X⟩_β = (Σᵢ Xᵢ e^{−βEᵢ}) / Z(E, β)` — the unnormalized numerator
over the partition sum; the form Target T4 differentiates. -/
theorem gibbsExpect_eq_ratio (E : ι → ℝ) (β : ℝ) (X : ι → ℝ) :
    gibbsExpect E β X
      = (∑ i, X i * Real.exp (-(β * E i))) / partSum E β := by
  have hterm : ∀ i, gibbsProb E β i * X i
      = (X i * Real.exp (-(β * E i))) / partSum E β := by
    intro i
    show (Real.exp (-(β * E i)) / partSum E β) * X i = _
    ring
  show (∑ i, gibbsProb E β i * X i) = _
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_div]

omit [Nonempty ι] in
/-- Ratio form of the mean energy (Tier T1 — proved):
`⟨E⟩_β = (Σᵢ Eᵢ e^{−βEᵢ}) / Z(E, β)`. -/
theorem meanEnergy_eq_ratio (E : ι → ℝ) (β : ℝ) :
    meanEnergy E β
      = (∑ i, E i * Real.exp (-(β * E i))) / partSum E β :=
  gibbsExpect_eq_ratio E β E

-- ============================================================================
-- §2. Variance algebra and TARGET T1
-- ============================================================================

/-- The second-moment form of the variance (Tier T1 — proved):
`Var_β(X) = ⟨X²⟩_β − ⟨X⟩_β²`, by expanding the square in the
sum-of-squares definition and using normalization. The
sum-of-squares form is the definition (it is what §3 derives
non-negativity from); this is its computational face. -/
theorem gibbsVar_eq (E : ι → ℝ) (β : ℝ) (X : ι → ℝ) :
    gibbsVar E β X
      = gibbsExpect E β (fun i => (X i) ^ 2) - (gibbsExpect E β X) ^ 2 := by
  set m := gibbsExpect E β X with hm
  have hterm : ∀ i, gibbsProb E β i * (X i - m) ^ 2
      = gibbsProb E β i * (X i) ^ 2 - (2 * m) * (gibbsProb E β i * X i)
        + (m ^ 2) * gibbsProb E β i :=
    fun i => by ring
  show (∑ i, gibbsProb E β i * (X i - m) ^ 2)
      = (∑ i, gibbsProb E β i * (X i) ^ 2) - m ^ 2
  calc (∑ i, gibbsProb E β i * (X i - m) ^ 2)
      = ∑ i, (gibbsProb E β i * (X i) ^ 2 - (2 * m) * (gibbsProb E β i * X i)
          + (m ^ 2) * gibbsProb E β i) :=
        Finset.sum_congr rfl (fun i _ => hterm i)
    _ = (∑ i, gibbsProb E β i * (X i) ^ 2)
          - (2 * m) * (∑ i, gibbsProb E β i * X i) + (m ^ 2) * 1 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, sum_gibbsProb]
    _ = (∑ i, gibbsProb E β i * (X i) ^ 2) - m ^ 2 := by
        have hS1 : (∑ i, gibbsProb E β i * X i) = m := rfl
        rw [hS1]
        ring

/-- Affine covariance of the variance (Tier T1 — proved):
`Var_β(a • X + b) = a² • Var_β(X)` — a constant shift moves no
variance, and a scaling moves it by the square. Proved from the
definition: the mean shifts by the same affine map
(`gibbsExpect_affine`), so the deviations scale by `a` exactly. -/
theorem gibbsVar_affine (E : ι → ℝ) (β : ℝ) (X : ι → ℝ) (a b : ℝ) :
    gibbsVar E β (fun i => a * X i + b) = a ^ 2 * gibbsVar E β X := by
  have hfun : (fun i => ((a * X i + b)
        - gibbsExpect E β (fun i => a * X i + b)) ^ 2)
      = (fun i => a ^ 2 * (X i - gibbsExpect E β X) ^ 2) := by
    funext i
    rw [gibbsExpect_affine]
    ring
  show gibbsExpect E β (fun i => ((a * X i + b)
      - gibbsExpect E β (fun i => a * X i + b)) ^ 2)
    = a ^ 2 * gibbsExpect E β (fun i => (X i - gibbsExpect E β X) ^ 2)
  rw [hfun, gibbsExpect_const_mul]

/-- **TARGET T1 — the identity** (Tier T1 — proved):
`Var_β(K) = β² • Var_β(E)`. The modular eigenvalues are the affine
image `β • E + log Z` of the energies (`modEigen`), and affine
covariance (`gibbsVar_affine`) discharges the scalar `log Z`
exactly: a constant shifts no variance. This is the finite,
corpus-native content of "the modular variance is `β²` times the
energy variance" — with `K` in GibbsSpan's proved form, fenced by
K-MV1 to the finite `diagModularK`. -/
theorem varModular_eq (E : ι → ℝ) (β : ℝ) :
    varModular E β = β ^ 2 * varEnergy E β :=
  gibbsVar_affine E β E β (Real.log (partSum E β))

/-- **The GibbsSpan weld** (Tier T1 — proved): the modular
eigenvalues of this brick ARE the diagonal entries of the corpus's
modular Hamiltonian matrix: for the Gibbs weights of `GibbsSpan`
at `logZ = log Z(E, β)`,
`(diagModularK (gibbsWeightsE β E (log Z)) i i).re = β • Eᵢ + log Z`.
The eigenvalue-level route of T1 is thereby tied to the matrix
`K` itself, via `GibbsSpan.gibbsK_apply_diag` unmodified. -/
theorem modEigen_eq_gibbsK_diag {N : ℕ} [Nonempty (Fin N)]
    (E : Fin N → ℝ) (β : ℝ) (i : Fin N) :
    (diagModularK (ThetLogos.GibbsSpan.gibbsWeightsE β E
        (Real.log (partSum E β))) i i).re
      = modEigen E β i := by
  rw [ThetLogos.GibbsSpan.gibbsK_apply_diag]
  exact Complex.ofReal_re _

-- ============================================================================
-- §3. TARGET T2 — non-negativity, derived
-- ============================================================================

/-- **TARGET T2 — non-negativity, DERIVED** (Tier T1 — proved):
`0 ≤ Var_β(X)` for every observable `X`, at every `β`. The proof
is the derivation the two audited stubs assumed away: the variance
is DEFINED as the sum-of-squares form, each summand is a strictly
positive Gibbs weight (`gibbsProb_pos`) times a square
(`sq_nonneg`), and a sum of nonnegative terms is nonnegative.
Nothing about non-negativity is postulated anywhere in this
module — no class field, no structure field, no axiom. -/
theorem gibbsVar_nonneg (E : ι → ℝ) (β : ℝ) (X : ι → ℝ) :
    0 ≤ gibbsVar E β X := by
  show 0 ≤ ∑ i, gibbsProb E β i * (X i - gibbsExpect E β X) ^ 2
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (le_of_lt (gibbsProb_pos E β i)) (sq_nonneg _)

/-- The energy variance is nonnegative (Tier T1 — proved),
by `gibbsVar_nonneg`. -/
theorem varEnergy_nonneg (E : ι → ℝ) (β : ℝ) : 0 ≤ varEnergy E β :=
  gibbsVar_nonneg E β E

/-- The modular variance is nonnegative (Tier T1 — proved),
by `gibbsVar_nonneg` applied to the modular eigenvalues. -/
theorem varModular_nonneg (E : ι → ℝ) (β : ℝ) : 0 ≤ varModular E β :=
  gibbsVar_nonneg E β (modEigen E β)

-- ============================================================================
-- §4. TARGET T3 — the dial reads the void
-- ============================================================================

/-- Variance zero means the observable is constant (Tier T1 —
proved): `Var_β(X) = 0 ⟺ ∀ i, X i = ⟨X⟩_β`. Forward: a sum of
nonnegative terms (`gibbsProb_pos` times squares) vanishes only
termwise, and every Gibbs weight is strictly positive, so every
deviation vanishes. This is the general fact the dial's
faithfulness is read off from. -/
theorem gibbsVar_eq_zero_iff (E : ι → ℝ) (β : ℝ) (X : ι → ℝ) :
    gibbsVar E β X = 0 ↔ ∀ i, X i = gibbsExpect E β X := by
  constructor
  · intro h i
    have hnonneg : ∀ j ∈ Finset.univ,
        0 ≤ gibbsProb E β j * (X j - gibbsExpect E β X) ^ 2 :=
      fun j _ => mul_nonneg (le_of_lt (gibbsProb_pos E β j)) (sq_nonneg _)
    have hsum : (∑ j, gibbsProb E β j * (X j - gibbsExpect E β X) ^ 2) = 0 := h
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum i
      (Finset.mem_univ i)
    rcases mul_eq_zero.mp hterm with hp | hsq
    · exact absurd hp (ne_of_gt (gibbsProb_pos E β i))
    · have hdev : X i - gibbsExpect E β X = 0 :=
        (pow_eq_zero_iff (two_ne_zero)).mp hsq
      exact sub_eq_zero.mp hdev
  · intro h
    show (∑ i, gibbsProb E β i * (X i - gibbsExpect E β X) ^ 2) = 0
    apply Finset.sum_eq_zero
    intro i _
    rw [h i, sub_self]
    simp

/-- At constant energies the mean energy is that constant
(Tier T1 — proved). -/
theorem meanEnergy_eq_of_forall_eq (E : ι → ℝ) (β : ℝ) (c : ℝ)
    (h : ∀ i, E i = c) : meanEnergy E β = c := by
  show (∑ i, gibbsProb E β i * E i) = c
  calc (∑ i, gibbsProb E β i * E i)
      = ∑ i, gibbsProb E β i * c :=
        Finset.sum_congr rfl (fun i _ => by rw [h i])
    _ = (∑ i, gibbsProb E β i) * c := by rw [Finset.sum_mul]
    _ = c := by rw [sum_gibbsProb, one_mul]

/-- **TARGET T3 — the energy dial reads the void** (Tier T1 —
proved): at every real `β`,
`Var_β(E) = 0 ⟺ ∀ i j, E i = E j` — the energy variance vanishes
exactly at the degenerate state, all sectors at one level:
NullStart's void, characterized at the level of energies. -/
theorem varEnergy_eq_zero_iff (E : ι → ℝ) (β : ℝ) :
    varEnergy E β = 0 ↔ ∀ i j, E i = E j := by
  constructor
  · intro h i j
    have hi := (gibbsVar_eq_zero_iff E β E).mp h i
    have hj := (gibbsVar_eq_zero_iff E β E).mp h j
    rw [hi, hj]
  · intro h
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have hmean : meanEnergy E β = E i₀ :=
      meanEnergy_eq_of_forall_eq E β (E i₀) (fun i => h i i₀)
    apply (gibbsVar_eq_zero_iff E β E).mpr
    intro i
    have hmean' : gibbsExpect E β E = E i₀ := hmean
    rw [hmean']
    exact h i i₀

/-- **TARGET T3 — the modular dial reads the void** (Tier T1 —
proved): at `β ≠ 0`,
`Var_β(K) = 0 ⟺ ∀ i j, E i = E j` — the modular variance vanishes
exactly at the degenerate state. The hypothesis `β ≠ 0` is on the
face: at `β = 0` the modular Hamiltonian is the scalar `logZ • 1`
and `Var₀(K) = 0` for every `E` (see `varModular_zero_beta`), so
no faithful reading exists there; at every `β ≠ 0` the `β²`
factor of T1 is a nonzero scalar and the dial is exact. -/
theorem varModular_eq_zero_iff (E : ι → ℝ) {β : ℝ} (hβ : β ≠ 0) :
    varModular E β = 0 ↔ ∀ i j, E i = E j := by
  rw [varModular_eq, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (pow_ne_zero 2 hβ)
    · exact (varEnergy_eq_zero_iff E β).mp h
  · intro h
    right
    exact (varEnergy_eq_zero_iff E β).mpr h

/-- At `β = 0` the modular variance is identically zero
(Tier T1 — proved): `K` is the scalar `logZ • 1`, the dial is
collapsed, and no information about `E` can be read from it —
the stated reason the faithfulness theorems carry `β ≠ 0`. -/
theorem varModular_zero_beta (E : ι → ℝ) : varModular E 0 = 0 := by
  rw [varModular_eq]
  simp

/-- The energy dial is strictly positive exactly at a gap
(Tier T1 — proved): `0 < Var_β(E) ⟺ ∃ i j, E i ≠ E j`, at every
`β` — non-negativity (§3) plus the zero characterization above. -/
theorem varEnergy_pos_iff (E : ι → ℝ) (β : ℝ) :
    0 < varEnergy E β ↔ ∃ i j, E i ≠ E j := by
  constructor
  · intro h
    by_contra hc
    have hall : ∀ i j, E i = E j := by
      intro i j
      by_contra hne
      exact hc ⟨i, j, hne⟩
    exact h.ne' ((varEnergy_eq_zero_iff E β).mpr hall)
  · rintro ⟨i, j, hij⟩
    apply lt_of_le_of_ne (varEnergy_nonneg E β)
    intro hv
    exact hij ((varEnergy_eq_zero_iff E β).mp hv.symm i j)

/-- The modular dial is strictly positive exactly at a gap
(Tier T1 — proved): at `β ≠ 0`,
`0 < Var_β(K) ⟺ ∃ i j, E i ≠ E j`. -/
theorem varModular_pos_iff (E : ι → ℝ) {β : ℝ} (hβ : β ≠ 0) :
    0 < varModular E β ↔ ∃ i j, E i ≠ E j := by
  have hβ2 : (0 : ℝ) < β ^ 2 :=
    lt_of_le_of_ne (sq_nonneg β) (pow_ne_zero 2 hβ).symm
  rw [varModular_eq, mul_pos_iff_of_pos_left hβ2]
  exact varEnergy_pos_iff E β

/-- Helper for the silence weld (Tier T1 — proved): if the Gibbs
probabilities are a constant function, the flux at
`diagModularK` of those probabilities vanishes for every `D` —
NullStart's silence at constant weights, applied. -/
theorem flux_zero_of_gibbsProb_eq_const {N : ℕ} (E : Fin N → ℝ) (β : ℝ)
    (c : ℝ) (h : gibbsProb E β = fun _ => c)
    (D : Matrix (Fin N) (Fin N) ℂ) :
    modularFlux (diagModularK (gibbsProb E β)) D = 0 := by
  rw [h]
  exact ThetLogos.NullStart.flux_zero_of_diagModularK_const c D

/-- Helper for the silence weld (Tier T1 — proved): at constant
energies the Gibbs probabilities are constant — every sector
carries the same exponential. -/
theorem gibbsProb_eq_const_of_forall_eq {N : ℕ} (E : Fin N → ℝ) (β : ℝ)
    (c : ℝ) (h : ∀ i, E i = c) :
    gibbsProb E β = fun _ => Real.exp (-(β * c)) / partSum E β := by
  funext i
  show Real.exp (-(β * E i)) / partSum E β = _
  rw [h i]

/-- **TARGET T3, the NullStart weld** (Tier T1 — proved): at every
real `β`, the modular variance of the Gibbs state vanishes iff
the state's modular Hamiltonian is flux-silent against every
probe:

    `Var_β(K) = 0 ⟺ ∀ D, modularFlux (diagModularK (gibbsProb E β)) D = 0`.

The dial reads NullStart's silence exactly. Forward: silence
forces the (strictly positive) probabilities to be constant
(NullStart's `silent_iff_weights_const_of_pos`), hence — at
`β ≠ 0` — the energies are constant and the energy variance
vanishes; at `β = 0` the modular variance is zero outright.
Backward: variance zero makes the probabilities constant (at
`β ≠ 0` via the energy characterization; at `β = 0` because every
weight is `e⁰ = 1`), and constant weights are silent by
NullStart's scalar route. Both directions are corpus theorems
composed; no new mechanism is introduced. -/
theorem silent_iff_varModular_eq_zero {N : ℕ} [Nonempty (Fin N)]
    (E : Fin N → ℝ) (β : ℝ) :
    (∀ D : Matrix (Fin N) (Fin N) ℂ,
        modularFlux (diagModularK (gibbsProb E β)) D = 0)
      ↔ varModular E β = 0 := by
  constructor
  · intro hsil
    have hprob : ∀ i j, gibbsProb E β i = gibbsProb E β j :=
      (ThetLogos.NullStart.silent_iff_weights_const_of_pos (gibbsProb E β)
        (fun j => gibbsProb_pos E β j)).mp hsil
    by_cases hβ : β = 0
    · rw [hβ]
      exact varModular_zero_beta E
    · have hE : ∀ i j, E i = E j := by
        intro i j
        have h1 : Real.exp (-(β * E i)) = Real.exp (-(β * E j)) := by
          have h2 : Real.exp (-(β * E i)) / partSum E β
              = Real.exp (-(β * E j)) / partSum E β := hprob i j
          have hZ : partSum E β ≠ 0 := partSum_ne_zero E β
          have h3 := (div_eq_div_iff hZ hZ).mp h2
          rcases (mul_eq_mul_right_iff).mp h3 with h | h
          · exact h
          · exact absurd h hZ
        have harg : -(β * E i) = -(β * E j) := Real.exp_strictMono.injective h1
        have h2 : β * E i = β * E j := neg_inj.mp harg
        exact mul_left_cancel₀ hβ h2
      exact (varModular_eq_zero_iff E hβ).mpr hE
  · intro hvar D
    obtain ⟨i₀⟩ := ‹Nonempty (Fin N)›
    by_cases hβ : β = 0
    · have hconst : gibbsProb E β = fun _ => (1 : ℝ) / partSum E β := by
        funext i
        show Real.exp (-(β * E i)) / partSum E β = _
        rw [hβ]
        simp
      exact flux_zero_of_gibbsProb_eq_const E β _ hconst D
    · have hE : ∀ i j, E i = E j := (varModular_eq_zero_iff E hβ).mp hvar
      have hconst : gibbsProb E β
          = fun _ => Real.exp (-(β * E i₀)) / partSum E β :=
        gibbsProb_eq_const_of_forall_eq E β (E i₀) (fun i => hE i i₀)
      exact flux_zero_of_gibbsProb_eq_const E β _ hconst D

-- ============================================================================
-- §5. TARGET T4 (stretch) — fluctuation response
-- ============================================================================

/-- Term derivative for T4 (Tier T1 — proved): the derivative of
`β' ↦ e^{−β'c}` is `−c • e^{−βc}` — the chain rule through
`Real.hasDerivAt_exp` and the affine inner function, with the
value massaged to the displayed form. -/
theorem hasDerivAt_exp_neg_mul (c β : ℝ) :
    HasDerivAt (fun β' => Real.exp (-(β' * c)))
      (-(c * Real.exp (-(β * c)))) β := by
  have hlin : HasDerivAt (fun β' : ℝ => -(β' * c)) (-c) β := by
    have h1 : HasDerivAt (fun β' : ℝ => β' * c) c β := by
      simpa using (hasDerivAt_id β).mul_const c
    exact h1.neg
  have h := (Real.hasDerivAt_exp (-(β * c))).comp β hlin
  have hderiv : Real.exp (-(β * c)) * (-c) = -(c * Real.exp (-(β * c))) := by
    ring
  rw [hderiv] at h
  exact h

omit [Nonempty ι] in
/-- Derivative of the partition sum (Tier T1 — proved):
`Z'(β) = −Σᵢ Eᵢ e^{−βEᵢ}` — termwise differentiation of the
finite sum (`HasDerivAt.fun_sum`). -/
theorem hasDerivAt_partSum (E : ι → ℝ) (β : ℝ) :
    HasDerivAt (partSum E)
      (-(∑ i, E i * Real.exp (-(β * E i)))) β := by
  show HasDerivAt (fun β' => ∑ i, Real.exp (-(β' * E i))) _ β
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => hasDerivAt_exp_neg_mul (E i) β)
  have hval : (∑ i, -(E i * Real.exp (-(β * E i))))
      = -(∑ i, E i * Real.exp (-(β * E i))) :=
    Finset.sum_neg_distrib ..
  rw [hval] at h
  exact h

omit [Nonempty ι] in
/-- Derivative of the unnormalized mean-energy numerator
(Tier T1 — proved): `N'(β) = −Σᵢ (Eᵢ)² e^{−βEᵢ}` where
`N(β) = Σᵢ Eᵢ e^{−βEᵢ}` — termwise differentiation, each term a
constant multiple of an exponential. -/
theorem hasDerivAt_weighted_sum (E : ι → ℝ) (β : ℝ) :
    HasDerivAt (fun β' => ∑ i, E i * Real.exp (-(β' * E i)))
      (-(∑ i, (E i) ^ 2 * Real.exp (-(β * E i)))) β := by
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (hasDerivAt_exp_neg_mul (E i) β).const_mul (E i))
  have hval : (∑ i, E i * -(E i * Real.exp (-(β * E i))))
      = -(∑ i, (E i) ^ 2 * Real.exp (-(β * E i))) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hval] at h
  exact h

/-- **TARGET T4 — fluctuation response** (Tier T1 — proved;
pre-registered stretch, landed whole): the mean energy's
`β`-derivative is minus the energy variance,

    `d/dβ ⟨E⟩_β = −Var_β(E)`,

at every `β`. Proof: differentiate the ratio form
(`meanEnergy_eq_ratio`) by the quotient rule — `Z' = −N` and
`N' = −M` (§5 lemmas), so the derivative is
`(N² − M • Z) / Z²`, and the second-moment form of the variance
(`gibbsVar_eq`, §2) reads `Var = M/Z − (N/Z)²`, the same number
negated. The finite fluctuation–response identity: the dial of
§4 is exactly the thermal response of the mean energy. -/
theorem hasDerivAt_meanEnergy (E : ι → ℝ) (β : ℝ) :
    HasDerivAt (fun β => meanEnergy E β) (-(varEnergy E β)) β := by
  have hvar : varEnergy E β
      = (∑ i, (E i) ^ 2 * Real.exp (-(β * E i))) / partSum E β
        - ((∑ i, E i * Real.exp (-(β * E i))) / partSum E β) ^ 2 := by
    calc varEnergy E β
        = gibbsExpect E β (fun i => (E i) ^ 2) - (gibbsExpect E β E) ^ 2 :=
          gibbsVar_eq E β E
      _ = (∑ i, (E i) ^ 2 * Real.exp (-(β * E i))) / partSum E β
            - ((∑ i, E i * Real.exp (-(β * E i))) / partSum E β) ^ 2 := by
          rw [gibbsExpect_eq_ratio, gibbsExpect_eq_ratio]
  have hfun : (fun β => meanEnergy E β)
      = (fun y => (∑ i, E i * Real.exp (-(y * E i))) / partSum E y) :=
    funext fun y => meanEnergy_eq_ratio E y
  have hderiv : ((-∑ i, (E i) ^ 2 * Real.exp (-(β * E i))) * partSum E β
        - (∑ i, E i * Real.exp (-(β * E i)))
          * (-∑ i, E i * Real.exp (-(β * E i)))) / partSum E β ^ 2
      = -(varEnergy E β) := by
    have hZ : partSum E β ≠ 0 := partSum_ne_zero E β
    rw [hvar]
    field_simp
    rw [show (∑ x, E x ^ 2 * Real.exp (-(E x * β)))
        = (∑ x, E x ^ 2 * Real.exp (-(β * E x))) from
      Finset.sum_congr rfl (fun x _ => by rw [mul_comm (E x) β])]
    ring
  rw [hfun]
  have hdiv := (hasDerivAt_weighted_sum E β).div (hasDerivAt_partSum E β)
    (partSum_ne_zero E β)
  exact hderiv ▸ hdiv

-- Axiom check (headlines): expect exactly
-- [propext, Classical.choice, Quot.sound] on every line.
#print axioms varModular_eq
#print axioms modEigen_eq_gibbsK_diag
#print axioms gibbsVar_nonneg
#print axioms varEnergy_nonneg
#print axioms varModular_nonneg
#print axioms gibbsVar_eq_zero_iff
#print axioms varEnergy_eq_zero_iff
#print axioms varModular_eq_zero_iff
#print axioms varEnergy_pos_iff
#print axioms varModular_pos_iff
#print axioms silent_iff_varModular_eq_zero
#print axioms hasDerivAt_meanEnergy

end ThetLogos.ModularVariance
