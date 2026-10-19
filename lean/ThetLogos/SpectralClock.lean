import Mathlib.Tactic
import ThetLogos.ResonanceSpectrum

open Matrix Finset

namespace ThetLogos

/-!
# The spectral density clock: the master tick of a state's own spectrum (T1, finite level)

Origin (Jeff, 2026-10-18): having been told that every faithful state
carries its own clock (`ThermalClock`: the flow of `K = −ln ρ`), Jeff
asked whether a "spectral destiny clock" can be made — a clock whose
tick is read straight off the spectrum. The electron-density premise
attached to the question ("electron density is equal to thermal
time") was audited NO-GO in the open and stays out: a density is a
spatial field, thermal time is a flow parameter, and no such equality
is defined or used anywhere in this module.

What IS built here, on the resonance brick's phase law
(`ResonanceSpectrum.phaseFlow_apply`): for a diagonal generator with
eigenvalue function `lam`, the **spectral width** is the largest gap,
`max lam − min lam`, and the **master tick** is `π / width`. The
widest coherence — the entry between a maximal and a minimal level —
rotates at exactly the width frequency, so at the master tick its
phase is `exp(−iπ) = −1`: the entry is negated (Theorem 1, the
extremal flip). And the master tick is the FIRST positive time at
which this happens: at any earlier positive time the phase has angle
in the open interval `(0, π)`, where cosine is strictly greater than
`−1`, so the phase is not `−1` (Theorem 2, firstness). Packaged for a
packaged `ThermalClock` (the corollary `thermalClock_masterTick`),
the diagonal modular clock of a state with nondegenerate `K`-spectrum
has master tick `π / width`, attained first by its widest coherence.

**Fences.** Finite level, finite index types, DIAGONAL generator:
the clock is read off an eigenvalue function `lam : ι → ℝ`. The
general Hermitian-generator reduction (diagonalise, then read the
clock in the eigenbasis) is the resonance brick's named remainder
and is NOT attempted here. The tick is a property of a state /
generator's spectrum — it is not a property of spacetime, and no
continuum clock is constructed. The time `t` throughout is the
modular-flow parameter; it converts to physical time only through
`ThermalClock`'s `β` for Gibbs states, and nothing here performs
that conversion. No electron-density content appears: that proposed
equality was NO-GO and stays out.
-/

-- ============================================================================
-- The spectral width and the master tick
-- ============================================================================

section SpectralWidth

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The finite range of an eigenvalue function, as a finset of reals.
Tier T2 (definition). -/
noncomputable def lamRange (lam : ι → ℝ) : Finset ℝ :=
  Finset.univ.image lam

/-- The range of an eigenvalue function on a nonempty index type is
nonempty (Tier T1 — proved). -/
theorem lamRange_nonempty (lam : ι → ℝ) : (lamRange lam).Nonempty := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  exact ⟨lam i₀, Finset.mem_image.mpr ⟨i₀, Finset.mem_univ i₀, rfl⟩⟩

/-- A real number is in the range of `lam` iff it is a value of `lam`
(Tier T1 — proved). -/
theorem mem_lamRange {lam : ι → ℝ} {x : ℝ} :
    x ∈ lamRange lam ↔ ∃ i, lam i = x := by
  constructor
  · intro h
    obtain ⟨i, -, hi⟩ := (Finset.mem_image).mp h
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩

/-- **The spectral width** of a diagonal generator: the largest gap
in its spectrum, `max lam − min lam`. This is the diameter of the
resonance spectrum's generating set — the frequency of the widest
coherence. Tier T2 (definition). -/
noncomputable def spectralWidth (lam : ι → ℝ) : ℝ :=
  (lamRange lam).max' (lamRange_nonempty lam)
    - (lamRange lam).min' (lamRange_nonempty lam)

/-- Every eigenvalue is at most the top of the range
(Tier T1 — proved). -/
theorem lam_le_rangeMax (lam : ι → ℝ) (i : ι) :
    lam i ≤ (lamRange lam).max' (lamRange_nonempty lam) :=
  Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- The bottom of the range is at most every eigenvalue
(Tier T1 — proved). -/
theorem rangeMin_le_lam (lam : ι → ℝ) (i : ι) :
    (lamRange lam).min' (lamRange_nonempty lam) ≤ lam i :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- A maximal level exists: some index attains the top of the
spectrum (Tier T1 — proved). -/
theorem exists_maximizer (lam : ι → ℝ) : ∃ i, ∀ k, lam k ≤ lam i := by
  have hmem := Finset.max'_mem (lamRange lam) (lamRange_nonempty lam)
  obtain ⟨i, -, hi⟩ := (Finset.mem_image).mp hmem
  exact ⟨i, fun k => hi ▸ lam_le_rangeMax lam k⟩

/-- A minimal level exists: some index attains the bottom of the
spectrum (Tier T1 — proved). -/
theorem exists_minimizer (lam : ι → ℝ) : ∃ j, ∀ k, lam j ≤ lam k := by
  have hmem := Finset.min'_mem (lamRange lam) (lamRange_nonempty lam)
  obtain ⟨j, -, hj⟩ := (Finset.mem_image).mp hmem
  exact ⟨j, fun k => hj ▸ rangeMin_le_lam lam k⟩

/-- The spectral width is the gap between any maximal and any minimal
level (Tier T1 — proved). -/
theorem spectralWidth_eq (lam : ι → ℝ) {i j : ι}
    (hi : ∀ k, lam k ≤ lam i) (hj : ∀ k, lam j ≤ lam k) :
    spectralWidth lam = lam i - lam j := by
  have hmax : (lamRange lam).max' (lamRange_nonempty lam) = lam i := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      obtain ⟨k, -, hk⟩ := (Finset.mem_image).mp hy
      exact hk ▸ hi k
    · exact lam_le_rangeMax lam i
  have hmin : (lamRange lam).min' (lamRange_nonempty lam) = lam j := by
    apply le_antisymm
    · exact rangeMin_le_lam lam j
    · apply Finset.le_min'
      intro y hy
      obtain ⟨k, -, hk⟩ := (Finset.mem_image).mp hy
      exact hk ▸ hj k
  unfold spectralWidth
  rw [hmax, hmin]

/-- The spectral width is always nonnegative (Tier T1 — proved):
some eigenvalue sits between the bottom and the top of the range. -/
theorem spectralWidth_nonneg (lam : ι → ℝ) : 0 ≤ spectralWidth lam := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  unfold spectralWidth
  have h1 := rangeMin_le_lam lam i₀
  have h2 := lam_le_rangeMax lam i₀
  linarith

/-- **Nondegeneracy makes the width positive** (Tier T1 — proved):
if two levels differ, the spectral width is strictly positive, so
the master tick below is a genuine positive time. -/
theorem spectralWidth_pos (lam : ι → ℝ)
    (h : ∃ i j, lam i ≠ lam j) : 0 < spectralWidth lam := by
  obtain ⟨i, j, hij⟩ := h
  have hwidth : ∀ a b : ι,
      lam a - lam b ≤ spectralWidth lam := by
    intro a b
    unfold spectralWidth
    have h1 := lam_le_rangeMax lam a
    have h2 := rangeMin_le_lam lam b
    linarith
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have := hwidth j i
    linarith
  · have := hwidth i j
    linarith

/-- **The master tick** of a diagonal generator: `π` divided by the
spectral width. The candidate first-flip time of the widest
coherence; the theorems below show it is attained, and attained
first. Tier T2 (definition). -/
noncomputable def masterTick (lam : ι → ℝ) : ℝ :=
  Real.pi / spectralWidth lam

/-- Under a positive width the master tick is a positive time
(Tier T1 — proved). -/
theorem masterTick_pos (lam : ι → ℝ) (hW : 0 < spectralWidth lam) :
    0 < masterTick lam :=
  div_pos Real.pi_pos hW

end SpectralWidth

-- ============================================================================
-- The clock: extremal flip at the master tick, and firstness
-- ============================================================================

section Clock

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **Theorem 1 — the extremal flip (Tier T1 — proved).** At the
master tick, the widest coherence of the phase flow is negated: for
`i` a maximal level and `j` a minimal level, the `(i, j)` entry at
`t = π / width` is exactly minus its initial value. The phase is
`exp(−i · (π/width) · width) = exp(−iπ) = −1`. -/
theorem phaseFlow_masterTick_apply (lam : ι → ℝ)
    (hW : 0 < spectralWidth lam) (A : Matrix ι ι ℂ) {i j : ι}
    (hi : ∀ k, lam k ≤ lam i) (hj : ∀ k, lam j ≤ lam k) :
    phaseFlow lam (masterTick lam) A i j = - A i j := by
  have hgap : lam i - lam j = spectralWidth lam :=
    (spectralWidth_eq lam hi hj).symm
  have hWc : ((lam i : ℂ) - (lam j : ℂ)) = ((spectralWidth lam : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sub, hgap]
  rw [phaseFlow_apply, hWc, mul_assoc]
  have hmul : (masterTick lam : ℂ) * ((spectralWidth lam : ℝ) : ℂ)
      = (Real.pi : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    exact div_mul_cancel₀ Real.pi (ne_of_gt hW)
  rw [hmul, mul_comm Complex.I (Real.pi : ℂ), Complex.exp_neg,
    Complex.exp_pi_mul_I]
  simp

/-- **Theorem 2 — firstness of the master tick (Tier T1 — proved).**
The master tick is the FIRST positive flip time of the widest
coherence: at any `0 < t < π / width`, the phase angle `t · width`
lies in the open interval `(0, π)`, where cosine is strictly
antitone and still above `cos π = −1`; hence the phase is not `−1`,
and no nonzero widest coherence is negated before the master tick.
The clock's tick is therefore well-defined and minimal. -/
theorem phaseFlow_masterTick_first (lam : ι → ℝ)
    (hW : 0 < spectralWidth lam) (A : Matrix ι ι ℂ) {i j : ι}
    (hi : ∀ k, lam k ≤ lam i) (hj : ∀ k, lam j ≤ lam k)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < masterTick lam) (hA : A i j ≠ 0) :
    phaseFlow lam t A i j ≠ - A i j := by
  intro hcon
  have hgap : lam i - lam j = spectralWidth lam :=
    (spectralWidth_eq lam hi hj).symm
  have hWc : ((lam i : ℂ) - (lam j : ℂ)) = ((spectralWidth lam : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sub, hgap]
  rw [phaseFlow_apply, hWc] at hcon
  -- Cancel the nonzero entry: the phase itself must be `−1`.
  have hexp : Complex.exp (-(Complex.I * (t : ℂ)
        * ((spectralWidth lam : ℝ) : ℂ))) = -1 := by
    rw [← neg_one_mul (A i j)] at hcon
    exact mul_right_cancel₀ hA hcon
  -- The phase angle `θ = t · width` lies in `(0, π)`.
  have hθ0 : 0 < t * spectralWidth lam := mul_pos ht0 hW
  have hθπ : t * spectralWidth lam < Real.pi := by
    have hmul := mul_lt_mul_of_pos_right ht1 hW
    unfold masterTick at hmul
    rwa [div_mul_cancel₀ Real.pi (ne_of_gt hW)] at hmul
  -- Rewrite the phase as `exp((−θ) * I)` and read off its real part.
  have hexp2 : Complex.exp (((-(t * spectralWidth lam) : ℝ) : ℂ)
      * Complex.I) = -1 := by
    rw [← hexp]
    congr 1
    push_cast
    ring
  have hre := congrArg Complex.re hexp2
  rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg] at hre
  simp only [Complex.neg_re, Complex.one_re] at hre
  -- But cosine is strictly antitone on `[0, π]`, so `cos θ > −1`.
  have hanti := Real.strictAntiOn_cos
    (Set.mem_Icc.mpr ⟨le_of_lt hθ0, le_of_lt hθπ⟩)
    (Set.mem_Icc.mpr ⟨Real.pi_pos.le, le_refl Real.pi⟩) hθπ
  rw [Real.cos_pi] at hanti
  linarith

/-- **The spectral clock, packaged (Tier T1 — proved).** A diagonal
generator with positive spectral width has a well-defined clock:
there is a widest coherence (between a maximal and a minimal level),
it is negated exactly at the master tick `π / width`, and at no
earlier positive time. The tick is read off the spectrum alone. -/
theorem spectralClock_masterTick (lam : ι → ℝ)
    (hW : 0 < spectralWidth lam) (A : Matrix ι ι ℂ) :
    ∃ i j : ι, (∀ k, lam k ≤ lam i) ∧ (∀ k, lam j ≤ lam k) ∧
      phaseFlow lam (masterTick lam) A i j = - A i j ∧
      ∀ t : ℝ, 0 < t → t < masterTick lam → A i j ≠ 0 →
        phaseFlow lam t A i j ≠ - A i j := by
  obtain ⟨i, hi⟩ := exists_maximizer lam
  obtain ⟨j, hj⟩ := exists_minimizer lam
  exact ⟨i, j, hi, hj, phaseFlow_masterTick_apply lam hW A hi hj,
    fun t ht0 ht1 hA => phaseFlow_masterTick_first lam hW A hi hj ht0 ht1 hA⟩

end Clock

-- ============================================================================
-- The modular instance: the clock of a packaged thermal clock
-- ============================================================================

section ThermalInstance

/-- **The clock reading for a thermal clock (Tier T1 — proved).**
The diagonal modular clock of a packaged thermal clock `C` — the
flow of its generator `K = −ln ρ`, via
`thermalClock_flow_eq_phaseFlow` — whose `K`-spectrum has positive
width has master tick `π / width` of the eigenvalue function
`j ↦ −log (weights j)`, and the tick is attained first by the
clock's widest coherence: there are levels `i, j` (maximal and
minimal for `K`) at which the flow negates the `(i, j)` entry
exactly at the master tick and at no earlier positive time.
Stated for the generator's spectrum; the `ρ`-instance is this
statement itself, through `diagFlow_eq_phaseFlow` — the state's
own weights are the clock's levels. -/
theorem thermalClock_masterTick {N : ℕ} [Nonempty (Fin N)]
    (C : ThermalClock N)
    (hW : 0 < spectralWidth (fun j => -Real.log (C.weights j)))
    (a : Matrix (Fin N) (Fin N) ℂ) :
    ∃ i j : Fin N,
      C.flow (masterTick (fun j => -Real.log (C.weights j))) a i j
        = - a i j ∧
      ∀ t : ℝ, 0 < t →
        t < masterTick (fun j => -Real.log (C.weights j)) →
        a i j ≠ 0 → C.flow t a i j ≠ - a i j := by
  obtain ⟨i, hi⟩ := exists_maximizer (fun j => -Real.log (C.weights j))
  obtain ⟨j, hj⟩ := exists_minimizer (fun j => -Real.log (C.weights j))
  refine ⟨i, j, ?_, ?_⟩
  · rw [thermalClock_flow_eq_phaseFlow]
    exact phaseFlow_masterTick_apply _ hW a hi hj
  · intro t ht0 ht1 hA hcon
    rw [thermalClock_flow_eq_phaseFlow] at hcon
    exact phaseFlow_masterTick_first _ hW a hi hj ht0 ht1 hA hcon

end ThermalInstance

end ThetLogos
