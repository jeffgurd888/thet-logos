import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import ThetLogos.BridgeLaplacian

open scoped InnerProductSpace

/-!
# ThetLogos.BridgeCompletion — spectral completion of the bridge exhibit (T1)

The priced follow-ons to `BridgeLaplacian.lean`, built per the
re-pricing of `whitepaper/gauntlet-parked-fleet-2026-10-17.md` §7.
`BridgeLaplacian.lean` is NOT modified; everything here is a new
module *about* its objects.

HONESTY LEDGER (read before citing):

- Everything is **T1 finite weighted-graph algebra**, in exactly the
  setting of `BridgeLaplacian.lean`: a finite vertex type `V`, a
  symmetric real weight function `w : V → V → ℝ` with nonnegativity a
  hypothesis where needed. Zero sorrys, no new axioms (headline
  theorems checked against the standard three: `propext`,
  `Classical.choice`, `Quot.sound` — see the dossier).
- **Attainment (priced S) STANDS.** For `|V| ≥ 2` (two distinct
  vertices), the Fiedler infimum of `BridgeLaplacian` is *attained*:
  `exists_fiedler_minimizer` produces an admissible potential —
  mean-zero, unit-norm — whose energy *equals* `fiedler w`. The
  admissible set is a closed subset of the unit sphere of a
  finite-dimensional space, hence compact; the energy is a
  polynomial, hence continuous; this is
  `IsCompact.exists_forall_le`. And `laplacianOp_fiedler_minimizer`
  identifies the minimizer as an **eigenvector of `laplacianOp` for
  the attained value**: the Lagrange condition in finite dimensions
  (first variation against orthogonal mean-zero perturbations
  vanishes, the constants absorb the mean-constraint multiplier, and
  the total-current law kills it).
- **λ₂-identification (part of the priced decay package, M) STANDS.**
  `fiedler_le_of_eigenvector`: every mean-zero eigenvector of
  `laplacianOp` has eigenvalue `≥ fiedler w`; combined with
  attainment, `fiedler w` *is* the smallest eigenvalue of `L` on the
  mean-zero subspace — an eigenvalue, attained, and a floor for the
  others. (No connectivity hypothesis is made or needed; if the
  graph is disconnected in the support of `w`, `fiedler w = 0` and
  the statements remain true verbatim.)
- **Exponential decay (priced M) STANDS.** The flow is defined
  eigenbasis-wise, a direct port of `SchrodingerDynamics`' `evolOp`
  pattern with real decaying exponentials in place of phases:
  `heatOp hL t` multiplies the `k`-th eigenbasis coefficient by
  `exp (−λₖ t)`, where the eigenbasis is Mathlib's spectral basis of
  the symmetric operator `lapLin w` on `EuclideanSpace ℝ V`.
  `heatFlow_hasDerivAt` is the derivative theorem `Ḟ = −L F`
  (`HasDerivAt` in the Euclidean norm), `heatFlow_zero` is the
  initial condition, and `heatFlow_decay` is the decay estimate at
  the Fiedler rate, for `t ≥ 0`:

      `‖F(t) − mean‖ ≤ exp (−(fiedler w) · t) · ‖F₀ − mean‖`,

  where `mean` is the constant potential at the mean of `F₀`. The
  estimate is a Parseval computation against the eigenbasis; the one
  non-formal input is the termwise alternative — a mode either has
  eigenvalue `≥ fiedler w` (so it decays at least at the Fiedler
  rate) or it is a zero mode invisible to every mean-zero potential.
- **Faraday storey (priced S–M, optional) LANDED, §9.** A face
  structure on the Bridge's own graph (faces as ordered vertex
  quadruples, an `ℝ`-valued flux per face), the discrete Stokes
  identity for potentials (circulation of potential drops around a
  face boundary vanishes — the graph's `d² = 0`), and the
  EMF = −dΦ/dt definition-theorem pair. Header-fenced: this is
  graph-Faraday bookkeeping, not Maxwell theory; no coupled
  induced-field dynamics is built.
- NOT CLAIMED: no continuum limit, no infinite graph, no Maxwell
  theory, no Yang–Mills content. The decay is for the finite
  semigroup on the finite-dimensional space of potentials, exactly
  as scoped. The three readings of `BridgeLaplacian` (resistor
  network / graph heat / DeGroot consensus) remain an equation
  identity, not a claim about the world.
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. Energy and bilinear form; linearity of `laplacianOp`

`BridgeLaplacian` works with the unfolded sums; here the quadratic
form and its polarization get names, and the linearity of
`laplacianOp` in the potential — used by every variation argument
below — is proved. -/

/-- The energy of a potential: the quadratic form of `laplacianOp`,
`∑ i, F i * (L F) i` (the diagonal sum of `BridgeLaplacian`). -/
def energy (w : V → V → ℝ) (F : V → ℝ) : ℝ :=
  ∑ i, F i * laplacianOp w F i

/-- The polarized bilinear form `∑ i, G i * (L F) i`. -/
def bilin (w : V → V → ℝ) (F G : V → ℝ) : ℝ :=
  ∑ i, G i * laplacianOp w F i

theorem energy_def (w : V → V → ℝ) (F : V → ℝ) :
    energy w F = ∑ i, F i * laplacianOp w F i := rfl

theorem bilin_def (w : V → V → ℝ) (F G : V → ℝ) :
    bilin w F G = ∑ i, G i * laplacianOp w F i := rfl

theorem bilin_self (w : V → V → ℝ) (F : V → ℝ) : bilin w F F = energy w F := rfl

/-- Linearity of `laplacianOp` in the potential: additivity. -/
theorem laplacianOp_add (w : V → V → ℝ) (F G : V → ℝ) :
    laplacianOp w (F + G) = laplacianOp w F + laplacianOp w G := by
  funext i
  simp only [laplacianOp_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Linearity of `laplacianOp` in the potential: scaling. -/
theorem laplacianOp_smul (w : V → V → ℝ) (c : ℝ) (F : V → ℝ) :
    laplacianOp w (c • F) = c • laplacianOp w F := by
  funext i
  simp only [laplacianOp_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Linearity of `laplacianOp` in the potential: subtraction. -/
theorem laplacianOp_sub (w : V → V → ℝ) (F G : V → ℝ) :
    laplacianOp w (F - G) = laplacianOp w F - laplacianOp w G := by
  funext i
  simp only [laplacianOp_apply, Pi.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The energy is quadratic: `energy (c • F) = c² • energy F`. -/
theorem energy_smul (w : V → V → ℝ) (c : ℝ) (F : V → ℝ) :
    energy w (c • F) = c ^ 2 * energy w F := by
  rw [energy_def, laplacianOp_smul]
  have h : ∀ i : V, (c • F) i * (c • laplacianOp w F) i
      = c ^ 2 * (F i * laplacianOp w F i) := by
    intro i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun i _ => h i), ← Finset.mul_sum, energy_def]

/-- The one-step variation of the energy: along `F + t • G` the
energy is a quadratic polynomial in `t` whose linear coefficient is
twice the bilinear form. This is the computation the Lagrange
argument feeds on. -/
theorem energy_add_smul (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (F G : V → ℝ) (t : ℝ) :
    energy w (F + t • G)
      = energy w F + 2 * t * bilin w F G + t ^ 2 * energy w G := by
  rw [energy_def, bilin_def, laplacianOp_add, laplacianOp_smul]
  have hexp : ∀ i : V, (F + t • G) i * (laplacianOp w F + t • laplacianOp w G) i
      = F i * laplacianOp w F i
        + t * (G i * laplacianOp w F i + F i * laplacianOp w G i)
        + t ^ 2 * (G i * laplacianOp w G i) := by
    intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hexp i),
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib, laplacianOp_symm_form w hw G F,
    show energy w F = ∑ i, F i * laplacianOp w F i from rfl,
    show energy w G = ∑ i, G i * laplacianOp w G i from rfl]
  ring

/-- The energy of an eigenvector is the eigenvalue times the squared
norm — the computation behind both the λ₂ floor and the
nonnegativity of eigenvalues. -/
theorem energy_of_eigenvector (w : V → V → ℝ) (G : V → ℝ) (μ : ℝ)
    (hG : ∀ i, laplacianOp w G i = μ * G i) :
    energy w G = μ * ∑ i, G i ^ 2 := by
  rw [energy_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hG i]
  ring

/-- A nonzero potential has positive squared norm. -/
theorem sum_sq_pos_of_fun_ne_zero {G : V → ℝ} (hGne : G ≠ 0) :
    (0:ℝ) < ∑ i, G i ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, G i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hGne (funext h)
  exact Finset.sum_pos' (fun j _ => sq_nonneg (G j))
    ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

/-! ## §2. Attainment of the Fiedler infimum

The admissible potentials form a closed, bounded — hence compact —
subset of the finite-dimensional space `V → ℝ`; the energy is
continuous; so the infimum defining `fiedler w` is attained whenever
the admissible set is inhabited, which `BridgeLaplacian` discharges
for two distinct vertices. -/

/-- The admissible potentials: mean-zero and unit-norm. This is the
indexing set of `BridgeLaplacian.fiedlerSet`, named once here. -/
def fiedlerAdmissible : Set (V → ℝ) :=
  {F | (∑ i, F i = 0) ∧ (∑ i, F i ^ 2 = 1)}

/-- The energy is continuous in the potential (it is a polynomial in
the coordinates). -/
theorem continuous_energy (w : V → V → ℝ) : Continuous (energy w) := by
  show Continuous fun F : V → ℝ => ∑ i, F i * laplacianOp w F i
  apply continuous_finset_sum
  intro i _
  apply Continuous.mul (continuous_apply i)
  have hfun : (fun F : V → ℝ => laplacianOp w F i)
      = (fun F : V → ℝ => ∑ j, w i j * (F i - F j)) := by
    funext F
    exact laplacianOp_apply w F i
  rw [hfun]
  apply continuous_finset_sum
  intro j _
  exact continuous_const.mul ((continuous_apply i).sub (continuous_apply j))

/-- The admissible set is closed: it is cut out by the two
continuous conditions `∑ F = 0` and `∑ F² = 1`. -/
theorem isClosed_fiedlerAdmissible : IsClosed (fiedlerAdmissible (V := V)) := by
  have h1 : IsClosed {F : V → ℝ | ∑ i, F i = 0} :=
    isClosed_eq (continuous_finset_sum _ fun i _ => continuous_apply i)
      continuous_const
  have h2 : IsClosed {F : V → ℝ | ∑ i, F i ^ 2 = 1} :=
    isClosed_eq (continuous_finset_sum _ fun i _ =>
      (continuous_pow 2).comp (continuous_apply i)) continuous_const
  have hset : fiedlerAdmissible (V := V)
      = {F : V → ℝ | ∑ i, F i = 0} ∩ {F : V → ℝ | ∑ i, F i ^ 2 = 1} := rfl
  rw [hset]
  exact h1.inter h2

/-- The admissible set is bounded: every admissible potential has
all coordinates in `[−1, 1]`. -/
theorem isBounded_fiedlerAdmissible :
    Bornology.IsBounded (fiedlerAdmissible (V := V)) := by
  apply Bornology.IsBounded.subset Metric.isBounded_closedBall
  intro F hF
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
  intro i
  have hsq : F i ^ 2 ≤ ∑ j, F j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (F j)) (Finset.mem_univ i)
  rw [hF.2] at hsq
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_one]
  exact Real.sqrt_le_sqrt hsq

/-- The admissible set is compact (finite-dimensional: closed and
bounded). -/
theorem isCompact_fiedlerAdmissible : IsCompact (fiedlerAdmissible (V := V)) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_fiedlerAdmissible
    isBounded_fiedlerAdmissible

/-- The admissible set is inhabited whenever two distinct vertices
exist — extracted from `BridgeLaplacian`'s inhabitedness of the
admissible *energies*. -/
theorem fiedlerAdmissible_nonempty (w : V → V → ℝ) {a b : V} (hab : a ≠ b) :
    (fiedlerAdmissible (V := V)).Nonempty := by
  obtain ⟨x, hx⟩ := fiedlerSet_nonempty_of_exists_ne w hab
  obtain ⟨F, hF0, hF1, -⟩ := hx
  exact ⟨F, hF0, hF1⟩

/-- **Attainment (T1).** For two distinct vertices, the Fiedler
infimum is attained: some admissible potential has energy exactly
`fiedler w`, and it minimizes the energy over the admissible set. -/
theorem exists_fiedler_minimizer (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) {a b : V} (hab : a ≠ b) :
    ∃ F : V → ℝ, F ∈ fiedlerAdmissible ∧ energy w F = fiedler w
      ∧ ∀ H ∈ fiedlerAdmissible, energy w F ≤ energy w H := by
  obtain ⟨F, hFmem, hFmin⟩ := isCompact_fiedlerAdmissible.exists_isMinOn
    (fiedlerAdmissible_nonempty w hab) (continuous_energy w).continuousOn
  refine ⟨F, hFmem, ?_, fun H hH => isMinOn_iff.mp hFmin H hH⟩
  apply le_antisymm
  · rw [fiedler_def]
    apply le_csInf (fiedlerSet_nonempty_of_exists_ne w hab)
    rintro x ⟨G, hG0, hG1, rfl⟩
    exact isMinOn_iff.mp hFmin G ⟨hG0, hG1⟩
  · exact fiedler_le_energy w hw hw0 F hFmem.1 hFmem.2

/-! ## §3. The Lagrange identification

The minimizer of §2 is an eigenvector. First the first-variation
lemma: at a minimizer, the bilinear form vanishes against every
mean-zero perturbation orthogonal to the minimizer — proved by
feeding the normalized perturbation line `F + t • G` to the
variational bound and reading off that the linear coefficient of
the resulting quadratic inequality cannot be nonzero. -/

/-- First variation at a minimizer: `bilin w F G = 0` for every
mean-zero `G` orthogonal to the minimizer `F`. -/
theorem bilin_eq_zero_of_minimizer (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (F G : V → ℝ) (hF : F ∈ fiedlerAdmissible)
    (hmin : ∀ H ∈ fiedlerAdmissible, energy w F ≤ energy w H)
    (hG0 : ∑ i, G i = 0) (hGF : ∑ i, G i * F i = 0) :
    bilin w F G = 0 := by
  have key : ∀ t : ℝ, 0 ≤ 2 * t * bilin w F G
      + t ^ 2 * (energy w G - energy w F * ∑ i, G i ^ 2) := by
    intro t
    have hq0 : (0:ℝ) ≤ ∑ i, G i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hpos : (0:ℝ) < 1 + t ^ 2 * ∑ i, G i ^ 2 :=
      lt_of_lt_of_le zero_lt_one
        (le_add_of_nonneg_right (mul_nonneg (sq_nonneg t) hq0))
    set s : ℝ := Real.sqrt (1 + t ^ 2 * ∑ i, G i ^ 2) with hs
    have hs2 : s ^ 2 = 1 + t ^ 2 * ∑ i, G i ^ 2 := Real.sq_sqrt hpos.le
    have hsne : s ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    have hmem : (s⁻¹ • (F + t • G)) ∈ fiedlerAdmissible := by
      constructor
      · have h1 : ∀ i : V, (s⁻¹ • (F + t • G)) i = s⁻¹ * (F i + t * G i) := by
          intro i
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.mul_sum,
          Finset.sum_add_distrib, ← Finset.mul_sum, hF.1, hG0]
        simp
      · have hnorm : (∑ i, (s⁻¹ • (F + t • G)) i ^ 2)
            = s⁻¹ ^ 2 * (1 + t ^ 2 * ∑ i, G i ^ 2) := by
          have h1 : ∀ i : V, (s⁻¹ • (F + t • G)) i ^ 2
              = s⁻¹ ^ 2 * ((F i + t * G i) ^ 2) := by
            intro i
            simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            ring
          rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.mul_sum]
          congr 1
          have hexp : ∀ i : V, (F i + t * G i) ^ 2
              = F i ^ 2 + 2 * t * (F i * G i) + t ^ 2 * (G i ^ 2) :=
            fun i => by ring
          rw [Finset.sum_congr rfl (fun i _ => hexp i),
            Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
          have hFG : (∑ i, F i * G i) = 0 := by
            have hcomm : (∑ i, F i * G i) = ∑ i, G i * F i :=
              Finset.sum_congr rfl fun i _ => mul_comm _ _
            rw [hcomm, hGF]
          rw [hF.2, hFG]
          ring
        rw [hnorm, ← hs2, ← mul_pow, inv_mul_cancel₀ hsne, one_pow]
    have hle := hmin _ hmem
    rw [energy_smul, energy_add_smul w hw] at hle
    have h3 : s ^ 2 * (s⁻¹ ^ 2 * (energy w F + 2 * t * bilin w F G
        + t ^ 2 * energy w G))
        = energy w F + 2 * t * bilin w F G + t ^ 2 * energy w G := by
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hsne, one_pow, one_mul]
    have h4 := mul_le_mul_of_nonneg_left hle (sq_nonneg s)
    rw [h3] at h4
    have h5 : energy w F * (1 + t ^ 2 * ∑ i, G i ^ 2) = s ^ 2 * energy w F := by
      rw [← hs2]
      ring
    have hmul : energy w F * (1 + t ^ 2 * ∑ i, G i ^ 2)
        ≤ energy w F + 2 * t * bilin w F G + t ^ 2 * energy w G := h5 ▸ h4
    have e1 : energy w F * (1 + t ^ 2 * ∑ i, G i ^ 2)
        = energy w F + t ^ 2 * (energy w F * ∑ i, G i ^ 2) := by ring
    have e2 : t ^ 2 * (energy w G - energy w F * ∑ i, G i ^ 2)
        = t ^ 2 * energy w G - t ^ 2 * (energy w F * ∑ i, G i ^ 2) := by ring
    rw [e1] at hmul
    rw [e2]
    linarith
  by_contra hB
  set C : ℝ := energy w G - energy w F * ∑ i, G i ^ 2 with hC
  set u : ℝ := |C| + 1 with hu
  have hu0 : (0:ℝ) < u := by
    have h1 : (0:ℝ) ≤ |C| := abs_nonneg C
    rw [hu]
    linarith
  have hune : u ≠ 0 := ne_of_gt hu0
  have h0 := key (-(bilin w F G) / u)
  have hB2 : (0:ℝ) < (bilin w F G) ^ 2 := sq_pos_of_ne_zero hB
  have h1 : (0:ℝ) ≤ -2 * (bilin w F G) ^ 2 * u + (bilin w F G) ^ 2 * C := by
    have h2 := mul_nonneg h0 (sq_nonneg u)
    have h3 : (2 * (-(bilin w F G) / u) * bilin w F G
        + (-(bilin w F G) / u) ^ 2 * C) * u ^ 2
        = -2 * (bilin w F G) ^ 2 * u + (bilin w F G) ^ 2 * C := by
      field_simp
    rwa [h3] at h2
  rw [hu] at h1
  have h4 : (bilin w F G) ^ 2 * C ≤ (bilin w F G) ^ 2 * |C| :=
    mul_le_mul_of_nonneg_left (le_abs_self C) hB2.le
  have h5 : (0:ℝ) ≤ (bilin w F G) ^ 2 * |C| := mul_nonneg hB2.le (abs_nonneg C)
  linarith

/-- A summation helper: the `i`-th delta picks out the `i`-th value. -/
theorem sum_ite_mul (X : V → ℝ) (i : V) :
    (∑ k, (if k = i then (1:ℝ) else 0) * X k) = X i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- A summation helper: the `i`-th delta sums to one. -/
theorem sum_ite_one (i : V) : (∑ k, (if k = i then (1:ℝ) else 0)) = 1 := by
  rw [Finset.sum_ite_eq']
  simp

/-- **The minimizer is an eigenvector (T1).** The attained Fiedler
minimizer satisfies `laplacianOp w F = (fiedler w) • F` pointwise:
the value `fiedler w` is an eigenvalue of `L`, with an admissible
eigenvector. The proof pairs the first-variation lemma against
every mean-zero `G` (subtracting the `F`-component first), reads off
that `L F − (fiedler w) • F` is constant, and kills the constant by
summing (the total current vanishes, the mean of `F` vanishes, and
`|V| ≥ 2`). -/
theorem laplacianOp_fiedler_minimizer (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    {a b : V} (hab : a ≠ b) :
    ∃ F : V → ℝ, F ∈ fiedlerAdmissible
      ∧ ∀ i, laplacianOp w F i = fiedler w * F i := by
  obtain ⟨F, hFmem, hFE, hmin⟩ := exists_fiedler_minimizer w hw hw0 hab
  refine ⟨F, hFmem, ?_⟩
  have key : ∀ G : V → ℝ, (∑ i, G i = 0) →
      ∑ i, G i * laplacianOp w F i = fiedler w * ∑ i, G i * F i := by
    intro G hG0
    set s : ℝ := ∑ i, G i * F i with hs
    have hB := bilin_eq_zero_of_minimizer w hw F (G - s • F) hFmem hmin
      (by
        have h1 : ∀ i : V, (G - s • F) i = G i - s * F i := fun i => by
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_sub_distrib,
          ← Finset.mul_sum, hG0, hFmem.1]
        simp)
      (by
        have h1 : ∀ i : V, (G - s • F) i * F i
            = G i * F i - s * (F i * F i) := fun i => by
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        have hsq : (∑ i, F i * F i) = 1 := by
          simp_rw [← pow_two]
          exact hFmem.2
        rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_sub_distrib,
          ← Finset.mul_sum, hsq, ← hs]
        simp)
    rw [bilin_def] at hB
    have hsum : (∑ i, (G - s • F) i * laplacianOp w F i)
        = (∑ i, G i * laplacianOp w F i) - s * energy w F := by
      have hexp : ∀ i : V, (G - s • F) i * laplacianOp w F i
          = G i * laplacianOp w F i - s * (F i * laplacianOp w F i) :=
        fun i => by
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
      rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_sub_distrib,
        ← Finset.mul_sum, energy_def]
    rw [hsum, hFE] at hB
    linarith
  have hconst : ∀ i j : V, laplacianOp w F i - fiedler w * F i
      = laplacianOp w F j - fiedler w * F j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · set G : V → ℝ := (fun k => if k = i then (1:ℝ) else 0)
        - (fun k => if k = j then (1:ℝ) else 0) with hG
      have hGeq : ∀ k : V, G k
          = (if k = i then (1:ℝ) else 0) - (if k = j then (1:ℝ) else 0) := by
        intro k
        simp only [hG, Pi.sub_apply]
      have hGsum : ∑ k, G k = 0 := by
        rw [Finset.sum_congr rfl (fun k _ => hGeq k), Finset.sum_sub_distrib,
          sum_ite_one, sum_ite_one, sub_self]
      have hδ : ∀ (X : V → ℝ), (∑ k, G k * X k) = X i - X j := by
        intro X
        have e1 : ∀ k : V, G k * X k
            = (if k = i then (1:ℝ) else 0) * X k
              - (if k = j then (1:ℝ) else 0) * X k := by
          intro k
          rw [hGeq k]
          ring
        rw [Finset.sum_congr rfl (fun k _ => e1 k), Finset.sum_sub_distrib,
          sum_ite_mul, sum_ite_mul]
      have hGkey := key G hGsum
      rw [hδ, hδ] at hGkey
      have hdist : fiedler w * (F i - F j)
          = fiedler w * F i - fiedler w * F j := by ring
      rw [hdist] at hGkey
      linarith
  have hHa : ∀ i : V, laplacianOp w F i = fiedler w * F i
      + (laplacianOp w F a - fiedler w * F a) := by
    intro i
    have h := hconst i a
    linarith
  have hsum : ∑ i, laplacianOp w F i = 0 := sum_laplacianOp_eq_zero w hw F
  have hsum2 : (∑ i, laplacianOp w F i)
      = fiedler w * (∑ i, F i)
        + (Fintype.card V : ℝ) * (laplacianOp w F a - fiedler w * F a) := by
    calc (∑ i, laplacianOp w F i)
        = ∑ i, (fiedler w * F i
            + (laplacianOp w F a - fiedler w * F a)) :=
          Finset.sum_congr rfl fun i _ => hHa i
      _ = fiedler w * (∑ i, F i)
            + (Fintype.card V : ℝ)
              * (laplacianOp w F a - fiedler w * F a) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            nsmul_eq_mul, Finset.card_univ]
  rw [hFmem.1] at hsum2
  have hcard : (2:ℝ) ≤ (Fintype.card V : ℝ) := by
    have h2 : ({a, b} : Finset V).card = 2 := Finset.card_pair hab
    have hle : ({a, b} : Finset V).card ≤ Fintype.card V := by
      have h := Finset.card_le_card (Finset.subset_univ ({a, b} : Finset V))
      rwa [Finset.card_univ] at h
    rw [h2] at hle
    exact_mod_cast hle
  have hcardne : (Fintype.card V : ℝ) ≠ 0 := by
    have hpos : (0:ℝ) < (Fintype.card V : ℝ) := by linarith
    exact ne_of_gt hpos
  have hν : laplacianOp w F a - fiedler w * F a = 0 := by
    have hzero : (Fintype.card V : ℝ)
        * (laplacianOp w F a - fiedler w * F a) = 0 := by
      have h := hsum
      rw [hsum2] at h
      simpa using h
    exact (mul_eq_zero.mp hzero).resolve_left hcardne
  intro i
  rw [hHa i, hν, add_zero]

/-! ## §4. The λ₂-identification

`fiedler w` is the smallest eigenvalue of `L` on the mean-zero
subspace: attained (§3) and a floor for every mean-zero eigenvalue
(here). Eigenvalues of `L` are nonnegative in general. -/

/-- **The λ₂ floor (T1).** Every mean-zero eigenvector of
`laplacianOp` has eigenvalue at least `fiedler w`. -/
theorem fiedler_le_of_eigenvector (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (G : V → ℝ) (μ : ℝ)
    (hG0 : ∑ i, G i = 0) (hGne : G ≠ 0)
    (hG : ∀ i, laplacianOp w G i = μ * G i) :
    fiedler w ≤ μ := by
  have hq : (0:ℝ) < ∑ i, G i ^ 2 := sum_sq_pos_of_fun_ne_zero hGne
  set c : ℝ := (Real.sqrt (∑ i, G i ^ 2))⁻¹ with hc
  have hc2 : c ^ 2 = (∑ i, G i ^ 2)⁻¹ := by
    rw [hc, inv_pow, Real.sq_sqrt hq.le]
  have h1 : (∑ i, (c • G) i) = 0 := by
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hG0, mul_zero]
  have h2 : (∑ i, (c • G) i ^ 2) = 1 := by
    have hterm : ∀ i : V, (c • G) i ^ 2 = c ^ 2 * (G i ^ 2) := fun i => by
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum, hc2,
      inv_mul_cancel₀ hq.ne']
  have h3 : fiedler w ≤ energy w (c • G) :=
    fiedler_le_energy w hw hw0 (c • G) h1 h2
  rw [energy_smul, energy_of_eigenvector w G μ hG, hc2] at h3
  have hqne : (∑ i, G i ^ 2) ≠ 0 := hq.ne'
  calc fiedler w ≤ (∑ i, G i ^ 2)⁻¹ * (μ * ∑ i, G i ^ 2) := h3
    _ = μ := by
        rw [mul_comm μ (∑ i, G i ^ 2), ← mul_assoc, inv_mul_cancel₀ hqne,
          one_mul]

/-- Eigenvalues of `laplacianOp` (nonneg symmetric weights) are
nonnegative — the energy of an eigenvector is `μ` times a positive
squared norm. -/
theorem eigenvalue_nonneg_of_eigenvector (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (G : V → ℝ) (μ : ℝ)
    (hGne : G ≠ 0) (hG : ∀ i, laplacianOp w G i = μ * G i) :
    0 ≤ μ := by
  have hq : (0:ℝ) < ∑ i, G i ^ 2 := sum_sq_pos_of_fun_ne_zero hGne
  have hE := energy_of_eigenvector w G μ hG
  have hnn : 0 ≤ energy w G := energy_nonneg w hw hw0 G
  rw [hE] at hnn
  exact nonneg_of_mul_nonneg_left hnn hq

/-! ## §5. `laplacianOp` as a symmetric operator

The decay theorem of §7 is built from Mathlib's spectral basis of a
symmetric operator, so `laplacianOp w` is packaged as a linear map
on the Euclidean space `EuclideanSpace ℝ V` (potentials with the L²
inner product `∑ Fᵢ Gᵢ`), by conjugation with the canonical
identification `euclEquiv` of Euclidean potentials with plain
potentials — the corpus's `FermionicFock` pattern. -/

/-- `laplacianOp w` as a linear map on plain potentials. -/
def lapLinFun (w : V → V → ℝ) : (V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun := laplacianOp w
  map_add' := laplacianOp_add w
  map_smul' := laplacianOp_smul w

/-- The canonical identification of the Euclidean space of
potentials with plain potentials. -/
def euclEquiv : EuclideanSpace ℝ V ≃ₗ[ℝ] (V → ℝ) :=
  WithLp.linearEquiv 2 ℝ (V → ℝ)

/-- `laplacianOp w` transported to the Euclidean space of
potentials. -/
def lapLin (w : V → V → ℝ) : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V :=
  euclEquiv.symm.conj (lapLinFun w)

/-- Transport identity: `euclEquiv` after `lapLin` recovers
`laplacianOp` on plain potentials. -/
theorem equiv_lapLin (w : V → V → ℝ) (F : EuclideanSpace ℝ V) :
    euclEquiv (lapLin w F) = laplacianOp w (euclEquiv F) := rfl

/-- Component form of the transport identity. -/
theorem lapLin_apply (w : V → V → ℝ) (F : EuclideanSpace ℝ V) (i : V) :
    (lapLin w F) i = laplacianOp w (euclEquiv F) i := rfl

/-- The Euclidean inner product in coordinates. -/
theorem euclid_inner_apply (X Y : EuclideanSpace ℝ V) :
    ⟪X, Y⟫_ℝ = ∑ i, X i * Y i := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  exact mul_comm _ _

/-- **Symmetry (T1).** `lapLin w` is a symmetric operator for
symmetric weights — the transport of `laplacianOp_symm_form`. -/
theorem lapLin_isSymmetric (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i) :
    (lapLin w).IsSymmetric := by
  intro F G
  have key : ∀ X Y : EuclideanSpace ℝ V,
      ⟪lapLin w X, Y⟫_ℝ
        = ∑ i, (euclEquiv Y) i * laplacianOp w (euclEquiv X) i := by
    intro X Y
    rw [euclid_inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (lapLin w X) i = laplacianOp w (euclEquiv X) i from rfl]
    exact mul_comm _ _
  rw [key, show ⟪F, lapLin w G⟫_ℝ = ⟪lapLin w G, F⟫_ℝ from real_inner_comm _ _,
    key]
  exact laplacianOp_symm_form w hw _ _

/-! ## §6. Means and constant vectors

The decay estimate measures distance to the constant potential at
the mean. This section packages the mean, the constant vectors, and
their two governing facts: `L` kills constants, and subtracting the
mean lands in the mean-zero subspace. -/

/-- The mean of a potential. -/
noncomputable def finMean (F : V → ℝ) : ℝ := (∑ i, F i) / (Fintype.card V : ℝ)

/-- The constant potential at the mean of `F`. -/
noncomputable def meanVec (F : V → ℝ) : V → ℝ := fun _ => finMean F

/-- Two distinct vertices force `(card V : ℝ) ≥ 2`, in particular
the mean is well-defined. -/
theorem card_ge_two {a b : V} (hab : a ≠ b) : (2:ℝ) ≤ (Fintype.card V : ℝ) := by
  have h2 : ({a, b} : Finset V).card = 2 := Finset.card_pair hab
  have hle : ({a, b} : Finset V).card ≤ Fintype.card V := by
    have h := Finset.card_le_card (Finset.subset_univ ({a, b} : Finset V))
    rwa [Finset.card_univ] at h
  rw [h2] at hle
  exact_mod_cast hle

/-- Subtracting the mean lands in the mean-zero subspace. -/
theorem sum_sub_meanVec (F : V → ℝ) (hcard : (Fintype.card V : ℝ) ≠ 0) :
    ∑ i, (F - meanVec F) i = 0 := by
  have hterm : ∀ i : V, (F - meanVec F) i = F i - finMean F := fun i => rfl
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  simp only [finMean]
  rw [mul_div_cancel₀ _ hcard, sub_self]

/-- The constant Euclidean vector at height `c`. -/
def constEucl (c : ℝ) : EuclideanSpace ℝ V :=
  euclEquiv.symm (fun _ : V => c)

theorem equiv_constEucl (c : ℝ) :
    euclEquiv (constEucl c) = (fun _ : V => c) := rfl

theorem constEucl_apply (c : ℝ) (i : V) : (constEucl c) i = c :=
  congrFun (equiv_constEucl c) i

/-- `L` kills constant vectors (the transport of
`laplacianOp_const`). -/
theorem lapLin_constEucl (w : V → V → ℝ) (c : ℝ) :
    lapLin w (constEucl c) = 0 := by
  apply euclEquiv.injective
  rw [map_zero, equiv_lapLin, equiv_constEucl, laplacianOp_const]

/-- The Euclidean mean vector: the constant vector at the mean of
the potential. -/
noncomputable def euclidMean (F : EuclideanSpace ℝ V) : EuclideanSpace ℝ V :=
  constEucl (finMean (euclEquiv F))

theorem equiv_euclidMean (F : EuclideanSpace ℝ V) :
    euclEquiv (euclidMean F) = meanVec (euclEquiv F) :=
  equiv_constEucl (finMean (euclEquiv F))

theorem euclidMean_apply (F : EuclideanSpace ℝ V) (i : V) :
    (euclidMean F) i = finMean (euclEquiv F) :=
  constEucl_apply (finMean (euclEquiv F)) i

/-- `L` kills the Euclidean mean vector. -/
theorem lapLin_euclidMean (w : V → V → ℝ) (F : EuclideanSpace ℝ V) :
    lapLin w (euclidMean F) = 0 :=
  lapLin_constEucl w (finMean (euclEquiv F))

/-- Pairing with the Euclidean mean vector factors through the sum
of the other potential's components. -/
theorem inner_euclidMean (F Y : EuclideanSpace ℝ V) :
    ⟪euclidMean F, Y⟫_ℝ = finMean (euclEquiv F) * ∑ i, Y i := by
  have hterm : ∀ i : V, (euclidMean F) i * Y i
      = finMean (euclEquiv F) * Y i := fun i => by rw [euclidMean_apply]
  rw [euclid_inner_apply, Finset.sum_congr rfl (fun i _ => hterm i),
    ← Finset.mul_sum]

/-- Pairing a vector against a constant vector factors through the
sum of its components. -/
theorem inner_constEucl (X : EuclideanSpace ℝ V) (c : ℝ) :
    ⟪X, constEucl c⟫_ℝ = (∑ i, X i) * c := by
  rw [euclid_inner_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [constEucl_apply]

/-- Pairing a constant vector against a vector factors through the
sum of the vector's components (left-slot form). -/
theorem inner_constEucl_left (Y : EuclideanSpace ℝ V) (c : ℝ) :
    ⟪constEucl c, Y⟫_ℝ = c * ∑ i, Y i := by
  have hterm : ∀ i : V, (constEucl c) i * Y i = c * Y i :=
    fun i => by rw [constEucl_apply]
  rw [euclid_inner_apply, Finset.sum_congr rfl (fun i _ => hterm i),
    ← Finset.mul_sum]

/-! ## §7. The heat flow and exponential decay

The flow is defined eigenbasis-wise, a direct port of
`SchrodingerDynamics`' `evolOp` pattern with the real decaying
exponentials `exp (−λt)` in place of phases: `heatOp hsymm t`
multiplies the `k`-th eigenbasis coefficient by
`exp (−(lapEig k) · t)`. The derivative theorem identifies the flow
as the solution of `Ḟ = −L F`, and the decay estimate is a Parseval
computation in which every mode either decays at least at the
Fiedler rate or is invisible to the mean-zero initial data. -/

/-- The eigenbasis of `lapLin w` from Mathlib's spectral theorem. -/
noncomputable def lapBasis (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric) :
    OrthonormalBasis (Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) ℝ
      (EuclideanSpace ℝ V) :=
  hsymm.eigenvectorBasis rfl

/-- The eigenvalues of `lapLin w`. -/
noncomputable def lapEig (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) : ℝ :=
  hsymm.eigenvalues rfl k

/-- `euclEquiv` does not change components. -/
theorem euclEquiv_apply (F : EuclideanSpace ℝ V) (i : V) :
    (euclEquiv F) i = F i := rfl

theorem lapBasis_apply_eig (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) :
    lapLin w ((lapBasis w hsymm) k)
      = lapEig w hsymm k • (lapBasis w hsymm) k :=
  hsymm.apply_eigenvectorBasis rfl k

/-- The eigenbasis equation read on plain potentials, pointwise. -/
theorem lapEig_eq_of_basis (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) :
    ∀ i, laplacianOp w (euclEquiv ((lapBasis w hsymm) k)) i
      = lapEig w hsymm k * (euclEquiv ((lapBasis w hsymm) k)) i := by
  intro i
  have h := congrArg euclEquiv (lapBasis_apply_eig w hsymm k)
  rw [equiv_lapLin, map_smul] at h
  have h3 := congrFun h i
  simpa only [Pi.smul_apply, smul_eq_mul] using h3

theorem lapBasis_ne_zero (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) :
    (lapBasis w hsymm) k ≠ 0 := by
  have hn : ‖(lapBasis w hsymm) k‖ = 1 :=
    (lapBasis w hsymm).orthonormal.1 k
  intro h
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

/-- An eigenbasis vector with nonzero eigenvalue is mean-zero as a
potential: it is orthogonal to the constants, and `L` kills the
constants. -/
theorem sum_euclEquiv_lapBasis_eq_zero (w : V → V → ℝ)
    (hsymm : (lapLin w).IsSymmetric)
    (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V)))
    (hk : lapEig w hsymm k ≠ 0) :
    ∑ i, (euclEquiv ((lapBasis w hsymm) k)) i = 0 := by
  have step1 : ⟪constEucl 1, lapLin w ((lapBasis w hsymm) k)⟫_ℝ = 0 := by
    have h := hsymm (constEucl 1) ((lapBasis w hsymm) k)
    rw [lapLin_constEucl, inner_zero_left] at h
    exact h.symm
  have step2 : ⟪constEucl (1:ℝ), lapLin w ((lapBasis w hsymm) k)⟫_ℝ
      = lapEig w hsymm k * ∑ i, ((lapBasis w hsymm) k) i := by
    have hterm : ∀ i : V, (constEucl (1:ℝ)) i
        * (lapEig w hsymm k • (lapBasis w hsymm) k) i
        = lapEig w hsymm k * ((lapBasis w hsymm) k) i := fun i => by
      rw [constEucl_apply, PiLp.smul_apply, smul_eq_mul, one_mul]
    rw [lapBasis_apply_eig, euclid_inner_apply,
      Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]
  rw [step2] at step1
  have hsum : ∑ i, ((lapBasis w hsymm) k) i = 0 :=
    (mul_eq_zero.mp step1).resolve_left hk
  rw [Finset.sum_congr rfl (fun i _ => euclEquiv_apply ((lapBasis w hsymm) k) i)]
  exact hsum

/-- Every eigenbasis eigenvalue with a nonzero value is at least
the Fiedler value: the λ₂-identification read on the spectral
basis. -/
theorem fiedler_le_lapEig (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) (hsymm : (lapLin w).IsSymmetric)
    (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V)))
    (hk : lapEig w hsymm k ≠ 0) :
    fiedler w ≤ lapEig w hsymm k :=
  fiedler_le_of_eigenvector w hw hw0 _ _
    (sum_euclEquiv_lapBasis_eq_zero w hsymm k hk)
    (fun h => lapBasis_ne_zero w hsymm k
      (euclEquiv.injective (by rw [h, map_zero])))
    (lapEig_eq_of_basis w hsymm k)

/-- The Fiedler value is nonnegative (for two distinct vertices):
it is the infimum of a nonempty set of energies. -/
theorem fiedler_nonneg_of (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) {a b : V} (hab : a ≠ b) :
    0 ≤ fiedler w := by
  rw [fiedler_def]
  apply le_csInf (fiedlerSet_nonempty_of_exists_ne w hab)
  rintro x ⟨G, hG0, hG1, rfl⟩
  exact energy_nonneg w hw hw0 G

/-- The zero-mode kill: if a zero-eigenvalue eigenbasis mode pairs
nontrivially with the mean-removed vector `x − euclidMean x`, then
the Fiedler value is zero. (The mode's own mean-removal is a
mean-zero zero-mode, so `fiedler ≤ 0`; the content is that when
`fiedler w > 0` — e.g. a connected graph — every zero mode is
constant, hence invisible to mean-removed data.) -/
theorem fiedler_eq_zero_of_inner_ne_zero (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric) {a b : V} (hab : a ≠ b)
    (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V)))
    (hk : lapEig w hsymm k = 0) (x : EuclideanSpace ℝ V)
    (hc : ⟪(lapBasis w hsymm) k, x - euclidMean x⟫_ℝ ≠ 0) :
    fiedler w = 0 := by
  have hcard0 : (Fintype.card V : ℝ) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) (card_ge_two hab))
  have hysum : ∑ i, (x - euclidMean x) i = 0 := by
    rw [Finset.sum_congr rfl
      (fun i _ => (euclEquiv_apply (x - euclidMean x) i).symm),
      map_sub, equiv_euclidMean]
    exact sum_sub_meanVec _ hcard0
  have hv0sum : ∑ i, (euclEquiv
      ((lapBasis w hsymm) k - euclidMean ((lapBasis w hsymm) k))) i = 0 := by
    rw [map_sub, equiv_euclidMean]
    exact sum_sub_meanVec _ hcard0
  have hinner : ⟪x - euclidMean x,
      (lapBasis w hsymm) k - euclidMean ((lapBasis w hsymm) k)⟫_ℝ
      = ⟪(lapBasis w hsymm) k, x - euclidMean x⟫_ℝ := by
    have h1 : ⟪x - euclidMean x, euclidMean ((lapBasis w hsymm) k)⟫_ℝ
        = 0 := by
      rw [show ⟪x - euclidMean x, euclidMean ((lapBasis w hsymm) k)⟫_ℝ
          = ⟪euclidMean ((lapBasis w hsymm) k), x - euclidMean x⟫_ℝ from
          real_inner_comm _ _, inner_euclidMean, hysum, mul_zero]
    rw [inner_sub_right, h1, sub_zero]
    exact real_inner_comm _ _
  have hv0 : (lapBasis w hsymm) k - euclidMean ((lapBasis w hsymm) k)
      ≠ 0 := by
    intro hv0
    apply hc
    rw [← hinner, hv0, inner_zero_right]
  have hv0eig : ∀ i, laplacianOp w (euclEquiv
      ((lapBasis w hsymm) k - euclidMean ((lapBasis w hsymm) k))) i
      = 0 * (euclEquiv
        ((lapBasis w hsymm) k - euclidMean ((lapBasis w hsymm) k))) i := by
    have hL : lapLin w ((lapBasis w hsymm) k
        - euclidMean ((lapBasis w hsymm) k)) = 0 := by
      have h1 : lapLin w ((lapBasis w hsymm) k) = 0 := by
        rw [lapBasis_apply_eig w hsymm k, hk, zero_smul]
      rw [map_sub, h1, lapLin_euclidMean, sub_zero]
    intro i
    have h2 : euclEquiv (lapLin w ((lapBasis w hsymm) k
        - euclidMean ((lapBasis w hsymm) k)))
        = laplacianOp w (euclEquiv ((lapBasis w hsymm) k
          - euclidMean ((lapBasis w hsymm) k))) := equiv_lapLin w _
    rw [hL, map_zero] at h2
    have h3 := congrFun h2.symm i
    simpa using h3
  have hle : fiedler w ≤ 0 :=
    fiedler_le_of_eigenvector w hw hw0 _ 0 hv0sum
      (fun h => hv0 (euclEquiv.injective (by rw [h, map_zero]))) hv0eig
  exact le_antisymm hle (fiedler_nonneg_of w hw hw0 hab)

/-! ## §8. The heat operator, its ODE, and its decay

`heatOp hsymm t` is the eigenbasis-wise operator multiplying the
`k`-th eigenbasis coefficient by `Real.exp (−(lapEig k) · t)` — the
real decaying-exponential twin of `SchrodingerDynamics.evolOp`.
Below: its solution formula, the derivative theorem `Ḟ = −L F`,
the initial condition, and the decay estimate at the Fiedler rate. -/

/-- The heat operator: eigenbasis-wise multiplication by
`exp (−λ t)`. -/
noncomputable def heatOp (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (t : ℝ) : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V :=
  (lapBasis w hsymm).toBasis.constr ℝ
    fun k => Real.exp (-(lapEig w hsymm k) * t) • (lapBasis w hsymm) k

theorem heatOp_apply_basis (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (t : ℝ) (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) :
    heatOp w hsymm t ((lapBasis w hsymm) k)
      = Real.exp (-(lapEig w hsymm k) * t) • (lapBasis w hsymm) k :=
  Module.Basis.constr_basis _ _ _ _

theorem heatOp_apply (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (t : ℝ) (x : EuclideanSpace ℝ V) :
    heatOp w hsymm t x = ∑ k, (Real.exp (-(lapEig w hsymm k) * t)
      * (lapBasis w hsymm).repr x k) • (lapBasis w hsymm) k := by
  have step : heatOp w hsymm t x
      = heatOp w hsymm t (∑ k, (lapBasis w hsymm).repr x k
        • (lapBasis w hsymm) k) :=
    congrArg _ ((lapBasis w hsymm).sum_repr x).symm
  rw [step, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul, heatOp_apply_basis, smul_smul]
  congr 1
  ring

/-- The solution formula: the evolved potential's eigenbasis
coefficients are the initial coefficients multiplied by the
decaying exponentials. -/
theorem heatOp_solution_formula (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (t : ℝ) (x : EuclideanSpace ℝ V) :
    heatOp w hsymm t x = ∑ k, (Real.exp (-(lapEig w hsymm k) * t)
      * ⟪(lapBasis w hsymm) k, x⟫_ℝ) • (lapBasis w hsymm) k := by
  rw [heatOp_apply]
  exact Finset.sum_congr rfl fun k _ => by
    rw [(lapBasis w hsymm).repr_apply_apply]

theorem heatOp_repr (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (t : ℝ) (x : EuclideanSpace ℝ V)
    (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) :
    (lapBasis w hsymm).repr (heatOp w hsymm t x) k
      = Real.exp (-(lapEig w hsymm k) * t) * (lapBasis w hsymm).repr x k := by
  rw [(lapBasis w hsymm).repr_apply_apply, heatOp_solution_formula, inner_sum]
  rw [Finset.sum_eq_single k]
  · rw [inner_smul_right,
      orthonormal_iff_ite.mp (lapBasis w hsymm).orthonormal k k,
      if_pos rfl, mul_one]
    rw [(lapBasis w hsymm).repr_apply_apply]
  · intro j _ hjk
    rw [inner_smul_right,
      orthonormal_iff_ite.mp (lapBasis w hsymm).orthonormal k j,
      if_neg hjk.symm, mul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem heatOp_inner_basis (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (t : ℝ) (x : EuclideanSpace ℝ V)
    (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) :
    ⟪(lapBasis w hsymm) k, heatOp w hsymm t x⟫_ℝ
      = Real.exp (-(lapEig w hsymm k) * t) * ⟪(lapBasis w hsymm) k, x⟫_ℝ := by
  rw [← (lapBasis w hsymm).repr_apply_apply, heatOp_repr,
    (lapBasis w hsymm).repr_apply_apply]

/-- The initial condition: `heatOp` at `t = 0` is the identity. -/
theorem heatOp_zero (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (x : EuclideanSpace ℝ V) : heatOp w hsymm 0 x = x := by
  rw [heatOp_solution_formula]
  simp only [neg_mul, mul_zero, Real.exp_zero, one_mul]
  exact (lapBasis w hsymm).sum_repr' x

/-- `heatOp` fixes every vector annihilated by `L`: the
zero-eigenvalue modes carry the factor `exp 0 = 1`, and the
nonzero modes pair to zero against the kernel vector. -/
theorem heatOp_eq_of_lapLin_eq_zero (w : V → V → ℝ)
    (hsymm : (lapLin w).IsSymmetric) (t : ℝ) (z : EuclideanSpace ℝ V)
    (hz : lapLin w z = 0) : heatOp w hsymm t z = z := by
  rw [heatOp_solution_formula]
  have hterm : ∀ k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V)),
      (Real.exp (-(lapEig w hsymm k) * t) * ⟪(lapBasis w hsymm) k, z⟫_ℝ)
        • (lapBasis w hsymm) k
        = ⟪(lapBasis w hsymm) k, z⟫_ℝ • (lapBasis w hsymm) k := by
    intro k
    by_cases hk : lapEig w hsymm k = 0
    · rw [hk, neg_zero, zero_mul, Real.exp_zero, one_mul]
    · have h1 : lapEig w hsymm k * ⟪(lapBasis w hsymm) k, z⟫_ℝ = 0 := by
        have h2 : ⟪lapLin w ((lapBasis w hsymm) k), z⟫_ℝ
            = ⟪(lapBasis w hsymm) k, lapLin w z⟫_ℝ := hsymm _ _
        rw [lapBasis_apply_eig, hz, inner_zero_right] at h2
        rwa [inner_smul_left, starRingEnd_apply, star_trivial] at h2
      have h3 : ⟪(lapBasis w hsymm) k, z⟫_ℝ = 0 :=
        (mul_eq_zero.mp h1).resolve_left hk
      rw [h3, mul_zero, zero_smul]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  exact (lapBasis w hsymm).sum_repr' z

/-- `heatOp` fixes the Euclidean mean vector. -/
theorem heatOp_euclidMean (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (t : ℝ) (x : EuclideanSpace ℝ V) :
    heatOp w hsymm t (euclidMean x) = euclidMean x :=
  heatOp_eq_of_lapLin_eq_zero w hsymm t _ (lapLin_euclidMean w x)

/-- **The heat equation (T1).** The curve `s ↦ heatOp s x`
differentiates to `−(lapLin w (heatOp t x))` at every `t`: it solves
the bridge heat equation `Ḟ = −L F`. -/
theorem heatFlow_hasDerivAt (w : V → V → ℝ) (hsymm : (lapLin w).IsSymmetric)
    (x : EuclideanSpace ℝ V) (t : ℝ) :
    HasDerivAt (fun s => heatOp w hsymm s x)
      (-(lapLin w (heatOp w hsymm t x))) t := by
  have hfun : (fun s => heatOp w hsymm s x)
      = ∑ k, (fun s => (Real.exp (-(lapEig w hsymm k) * s)
          * ⟪(lapBasis w hsymm) k, x⟫_ℝ) • (lapBasis w hsymm) k) := by
    funext s
    rw [Finset.sum_apply]
    exact heatOp_solution_formula w hsymm s x
  rw [hfun]
  have hterm : ∀ k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V)),
      HasDerivAt (fun s => (Real.exp (-(lapEig w hsymm k) * s)
          * ⟪(lapBasis w hsymm) k, x⟫_ℝ) • (lapBasis w hsymm) k)
        ((-(lapEig w hsymm k) * (Real.exp (-(lapEig w hsymm k) * t)
          * ⟪(lapBasis w hsymm) k, x⟫_ℝ)) • (lapBasis w hsymm) k) t := by
    intro k
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-(lapEig w hsymm k) * s))
        (Real.exp (-(lapEig w hsymm k) * t) * (-(lapEig w hsymm k))) t := by
      have harg : HasDerivAt (fun s : ℝ => -(lapEig w hsymm k) * s)
          (-(lapEig w hsymm k)) t := by
        simpa using (hasDerivAt_id t).const_mul (-(lapEig w hsymm k))
      exact harg.exp
    have h2 := h1.mul (hasDerivAt_const t (⟪(lapBasis w hsymm) k, x⟫_ℝ))
    have h3 := h2.smul_const ((lapBasis w hsymm) k)
    convert h3 using 1
    congr 1
    ring
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun k _ => hterm k)
  convert hsum using 1
  rw [heatOp_solution_formula, map_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul, lapBasis_apply_eig, smul_smul, ← neg_smul]
  congr 1
  ring

/-- **Exponential decay at the Fiedler rate (T1).** For `t ≥ 0`,
the heat flow decays to the mean at the rate the spectral gap
sets:

    `‖F(t) − mean‖ ≤ exp (−(fiedler w) · t) · ‖F₀ − mean‖`.

Every eigenbasis mode either has eigenvalue at least
`fiedler w` (so it decays at least at the Fiedler rate) or is a
zero mode; in the latter case it is invisible to the mean-removed
data unless `fiedler w = 0`, in which case the rate factor is `1`.
Finite graph only; no continuum claim. -/
theorem heatFlow_decay (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i)
    (hw0 : ∀ i j, 0 ≤ w i j) {a b : V} (hab : a ≠ b)
    (hsymm : (lapLin w).IsSymmetric) (x : EuclideanSpace ℝ V) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖heatOp w hsymm t x - euclidMean x‖
      ≤ Real.exp (-(fiedler w) * t) * ‖x - euclidMean x‖ := by
  have hcard0 : (Fintype.card V : ℝ) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) (card_ge_two hab))
  set y := x - euclidMean x with hy
  have hflow : heatOp w hsymm t x - euclidMean x = heatOp w hsymm t y := by
    have h1 : heatOp w hsymm t y
        = heatOp w hsymm t x - heatOp w hsymm t (euclidMean x) := by
      rw [hy, map_sub]
    rw [heatOp_euclidMean] at h1
    exact h1.symm
  rw [hflow]
  have hnorm1 : ‖heatOp w hsymm t y‖ ^ 2
      = ∑ k, (Real.exp (-(lapEig w hsymm k) * t)
          * ⟪(lapBasis w hsymm) k, y⟫_ℝ) ^ 2 := by
    rw [← (lapBasis w hsymm).sum_sq_norm_inner_right (heatOp w hsymm t y)]
    apply Finset.sum_congr rfl
    intro k _
    rw [heatOp_inner_basis, Real.norm_eq_abs, sq_abs]
  have hnorm2 : ‖y‖ ^ 2
      = ∑ k, ⟪(lapBasis w hsymm) k, y⟫_ℝ ^ 2 := by
    rw [← (lapBasis w hsymm).sum_sq_norm_inner_right y]
    apply Finset.sum_congr rfl
    intro k _
    rw [Real.norm_eq_abs, sq_abs]
  have hterm : ∀ k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V)),
      (Real.exp (-(lapEig w hsymm k) * t) * ⟪(lapBasis w hsymm) k, y⟫_ℝ) ^ 2
        ≤ (Real.exp (-(fiedler w) * t)) ^ 2 * ⟪(lapBasis w hsymm) k, y⟫_ℝ ^ 2 := by
    intro k
    by_cases hc : ⟪(lapBasis w hsymm) k, y⟫_ℝ = 0
    · rw [hc]
      simp
    · by_cases hk : lapEig w hsymm k = 0
      · have hf0 : fiedler w = 0 :=
          fiedler_eq_zero_of_inner_ne_zero w hw hw0 hsymm hab k hk x hc
        rw [hk, hf0]
        simp
      · have hle : fiedler w ≤ lapEig w hsymm k :=
          fiedler_le_lapEig w hw hw0 hsymm k hk
        have hexp : Real.exp (-(lapEig w hsymm k) * t)
            ≤ Real.exp (-(fiedler w) * t) := by
          apply Real.exp_le_exp.mpr
          have hmul : (fiedler w) * t ≤ (lapEig w hsymm k) * t :=
            mul_le_mul_of_nonneg_right hle ht
          linarith
        have hnn1 : (0:ℝ) ≤ Real.exp (-(lapEig w hsymm k) * t) :=
          Real.exp_nonneg _
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnn1 hexp 2)
          (sq_nonneg _)
  have hsum : ‖heatOp w hsymm t y‖ ^ 2
      ≤ (Real.exp (-(fiedler w) * t)) ^ 2 * ‖y‖ ^ 2 := by
    rw [hnorm1, hnorm2, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hterm k
  rw [← mul_pow] at hsum
  have hnnL : (0:ℝ) ≤ ‖heatOp w hsymm t y‖ := norm_nonneg _
  have hnnR : (0:ℝ) ≤ Real.exp (-(fiedler w) * t) * ‖y‖ :=
    mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)
  exact (sq_le_sq₀ hnnL hnnR).mp hsum

/-! ## §9. The Faraday storey (graph-Faraday, definitions + two
identities)

`BridgeLaplacian` has no faces, so Faraday needs a face structure
on the Bridge's own graph — it cannot be borrowed from
`LatticeGauge`, whose plaquettes are group-valued holonomies on a
cubical torus (multiplicative, generally nonabelian), while the
Bridge's circulation is additive telescoping of real drops. The
datum here: faces indexed by a type `F`, each face an ordered
quadruple of vertices (its boundary loop), and an `ℝ`-valued flux
per face. The proved content is exactly the discrete Stokes
identity for potentials (the circulation of potential drops around
any face boundary vanishes — the graph's `d² = 0`) and the
EMF = −dΦ/dt definition-theorem pair. This is graph-Faraday
bookkeeping on the finite graph, NOT Maxwell theory. -/

/-- A face of the bridge graph: an ordered quadruple of vertices,
its boundary loop `a → b → c → d → a`. -/
structure GraphFace (V : Type*) where
  /-- First boundary vertex. -/
  a : V
  /-- Second boundary vertex. -/
  b : V
  /-- Third boundary vertex. -/
  c : V
  /-- Fourth boundary vertex. -/
  d : V

/-- The circulation of a potential around a face boundary: the sum
of potential drops along the boundary loop. -/
def circulation {F : Type*} (bd : F → GraphFace V) (f : F) (Φ : V → ℝ) : ℝ :=
  dropVec Φ (bd f).a (bd f).b + dropVec Φ (bd f).b (bd f).c
    + dropVec Φ (bd f).c (bd f).d + dropVec Φ (bd f).d (bd f).a

/-- The circulation of an edge field around a face boundary. -/
def edgeCirculation {F : Type*} (bd : F → GraphFace V) (f : F)
    (E : V → V → ℝ) : ℝ :=
  E (bd f).a (bd f).b + E (bd f).b (bd f).c
    + E (bd f).c (bd f).d + E (bd f).d (bd f).a

/-- The flux of an edge field through a face is its boundary
circulation — the graph's discrete Stokes definition. -/
def faceFluxOf {F : Type*} (bd : F → GraphFace V) (E : V → V → ℝ)
    (f : F) : ℝ :=
  edgeCirculation bd f E

theorem circulation_eq_edgeCirculation {F : Type*} (bd : F → GraphFace V)
    (f : F) (Φ : V → ℝ) :
    circulation bd f Φ = edgeCirculation bd f (fun i j => Φ j - Φ i) := rfl

/-- **Discrete Stokes for potentials (T1).** The flux of a
potential field through any face is zero: potential drops telescope
around the closed boundary loop. -/
theorem faceFluxOf_dropVec {F : Type*} (bd : F → GraphFace V) (f : F)
    (Φ : V → ℝ) : faceFluxOf bd (fun i j => Φ j - Φ i) f = 0 := by
  simp only [faceFluxOf, edgeCirculation]
  ring

/-- **Circulation of a potential vanishes (T1).** -/
theorem circulation_eq_zero {F : Type*} (bd : F → GraphFace V) (f : F)
    (Φ : V → ℝ) : circulation bd f Φ = 0 := by
  simp only [circulation, dropVec]
  ring

/-- The induced EMF around a face: minus the time derivative of
the face's flux. -/
noncomputable def inducedEMF {F : Type*} (flux : ℝ → F → ℝ) (f : F)
    (t : ℝ) : ℝ :=
  -deriv (fun s => flux s f) t

/-- **Faraday's law, graph form (T1 as a derivative
computation).** If the flux curve has derivative `flux' f` at `t`,
the induced EMF at `t` is `-flux' f`. -/
theorem inducedEMF_of_hasDerivAt {F : Type*} (flux : ℝ → F → ℝ)
    (flux' : F → ℝ) (t : ℝ)
    (h : ∀ f, HasDerivAt (fun s => flux s f) (flux' f) t) (f : F) :
    inducedEMF flux f t = -flux' f := by
  rw [inducedEMF, (h f).deriv]

/-- The Faraday package for one face: potentials induce no
circulation, and the EMF is minus the flux's time derivative. -/
theorem faraday_package {F : Type*} (bd : F → GraphFace V) (Φ : V → ℝ)
    (flux : ℝ → F → ℝ) (flux' : F → ℝ) (t : ℝ)
    (h : ∀ f, HasDerivAt (fun s => flux s f) (flux' f) t) (f : F) :
    circulation bd f Φ = 0 ∧ inducedEMF flux f t = -flux' f :=
  ⟨circulation_eq_zero bd f Φ, inducedEMF_of_hasDerivAt flux flux' t h f⟩

end ThetLogos

