import Mathlib.Tactic
import ThetLogos.FluxClassification
import ThetLogos.TeslaVortexMultiSector

open ThetLogos.FluxClassification ThetLogos.TeslaVortexMultiSector

namespace ThetLogos.NullStart

/-!
# ThetLogos.NullStart — building from the void: the degenerate state

STATUS: STANDS WHOLE (T1) — landed 2026-10-22 under Jeff's
commission ("let build from the void", 2026-10-22 21:43 EDT; bench
ruling: bump the Ghys filler, build now). Parent-verified on the
shipped text: targeted in-tree build green, strict recount,
placeholder census, #print axioms standard-only on all 13
declarations. Charter:
`whitepaper/null-start-scoping-2026-10-22.md`; dossier:
`whitepaper/null-start-2026-10-22.md`.

## What this brick proves

The void of a finite Gibbs box is the **degenerate state**: all
sector energies (equivalently, for the built modular Hamiltonian
`diagModularK`, all log-weights) equal. No gap, no distinguished
sector — the null start of the box. Three facts about it, all in the
landed modules' own vocabulary (`modularFlux`, `diagModularK` from
`ModularTime`; `modularFlux_diagonal_apply`,
`classification_diagModularK` from `FluxClassification`; `sepN` from
`TeslaVortexMultiSector`):

1. **T1 — Silence.** At constant weights the built modular
   Hamiltonian is a scalar matrix,
   `diagModularK (fun _ => c) = (-log c) • 1`
   (`diagModularK_const`), and a scalar commutes with everything, so
   the modular flux vanishes for EVERY Dirac operator `D`, with no
   hypothesis on `D`:
   `modularFlux (diagModularK (fun _ => c)) D = 0`
   (`flux_zero_of_diagModularK_const`). The engine is the general
   fact `modularFlux_smul_one`: flux at any scalar `K = s • 1` is
   zero. This reproves FluxClassification's one-sector collapse
   (`flux_diagModularK_eq_zero_of_const`) by the scalar route the
   charter names — the statement is the same, the mechanism (K is
   literally a scalar matrix) is this brick's content.

2. **T2 — Uniqueness.** The void is the ONLY fully silent state.
   If `modularFlux (diagModularK w) D = 0` for every `D`, then all
   log-weights agree (`log_eq_of_silent`, proved from the entry
   computation `modularFlux_diagonal_apply` with a single-entry
   witness `D`), `diagModularK w` is a scalar matrix
   (`diagModularK_eq_smul_one_of_silent`), and at strictly positive
   weights silence is exactly constancy of the weights
   (`silent_iff_weights_const_of_pos`). Headline form:
   `silent_iff_log_const`. Route note: T2 closed via the entry
   computation (a center-of-the-algebra argument in one-entry form),
   NOT via the sector-classification route — the classification is
   used only for the easy (backward) direction of the iff.
   Anything carrying a gap speaks to some probe.

3. **T3 — β-blindness.** At degenerate energies the multi-sector
   separation is the flat charge average at EVERY real `β`
   (`sepN_eq_average_of_forall_eq`, `sepN_eq_average_const`):
   Rung 2 (`TeslaVortexMultiSector.sepN_zero_beta`) proved `β = 0`;
   this is all `β`. Equivalently the separation does not move with
   `β` at all (`sepN_eq_of_forall_eq`): the void has no temperature.
   Contrapositive companion (`not_exists_const_of_sepN_ne_average`):
   a separation observed off the flat average at any `β` certifies
   that the energies are not all equal.

## Honest fences

- **K-V1.** The "void" here is the degenerate Gibbs state of a
  finite box. It is NOT the QFT vacuum, NOT creation ex nihilo, NOT
  a cosmological initial condition. The commissioning null-start
  ordering (shape before heat, Jeff 2026-10-22) is T5 motivation
  recorded on the charter — never a theorem statement.
- **K-V2.** No gravity object. "Shape" in this brick means the
  sector structure of a finite state, not spacetime geometry. This
  brick earns nothing toward any gravity claim and makes none.
- At bare `diagModularK` (arbitrary real weights, no positivity),
  silence characterizes the LOG-weights: `Real.log` identifies
  `w` and `-w` and sends `0` to `0`, exactly as recorded on
  FluxClassification's face. Weight-level constancy is claimed
  only under strict positivity (`silent_iff_weights_const_of_pos`).

## Status line

NO CLAIM beyond the finite identities proved below.

## Contents

- §1 (Target T1): scalar flux vanishing, the degenerate `K` as a
  scalar matrix, silence at the built `K`.
- §2 (Target T2): silence forces equal log-weights; the silent `K`
  is scalar; the iff headlines.
- §3 (Target T3): β-blindness of the separation at degenerate
  energies, and its contrapositive companion.
-/

-- ============================================================================
-- §1. Silence (Target T1)
-- ============================================================================

section Flux

variable {N : ℕ}

/-- **TARGET T1, engine** (Tier T1 target): the modular flux at a
scalar matrix `K = s • 1` vanishes for EVERY `D` — a scalar commutes
with every matrix, and flux vanishing is commutation
(`FluxClassification.modularFlux_eq_zero_iff_commute`). No
hypothesis on `D`, none on `s`. -/
theorem modularFlux_smul_one (s : ℂ) (D : Matrix (Fin N) (Fin N) ℂ) :
    modularFlux (s • (1 : Matrix (Fin N) (Fin N) ℂ)) D = 0 := by
  have hcomm : (s • (1 : Matrix (Fin N) (Fin N) ℂ)) * D = D * (s • 1) := by
    rw [smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one]
  exact (modularFlux_eq_zero_iff_commute _ _).mpr hcomm

/-- **TARGET T1, the degenerate `K` is scalar** (Tier T1 target):
at constant weights the corpus's built modular Hamiltonian is
literally a scalar matrix:
`diagModularK (fun _ => c) = (-log c) • 1`, the scalar being the
common eigenvalue `-log c`. -/
theorem diagModularK_const (c : ℝ) :
    diagModularK (fun _ : Fin N => c)
      = ((-Real.log c : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  have hdiag : diagModularK (fun _ : Fin N => c)
      = Matrix.diagonal (fun _ : Fin N => ((-Real.log c : ℝ) : ℂ)) := rfl
  rw [hdiag]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.diagonal_apply_eq]
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

/-- **TARGET T1, silence from scalar form** (Tier T1 target): if the
built modular Hamiltonian is a scalar matrix, the flux at it
vanishes for every `D`. -/
theorem flux_eq_zero_of_diagModularK_eq_smul_one {w : Fin N → ℝ} {s : ℂ}
    (hK : diagModularK w = s • (1 : Matrix (Fin N) (Fin N) ℂ))
    (D : Matrix (Fin N) (Fin N) ℂ) :
    modularFlux (diagModularK w) D = 0 := by
  rw [hK]
  exact modularFlux_smul_one s D

/-- **TARGET T1 — SILENCE** (Tier T1 target): at the degenerate
state (constant weights), the modular flux at the built
`K = diagModularK` vanishes for EVERY Dirac operator `D`, no
hypothesis on `D`: the void answers every probe with nothing.
Same statement as FluxClassification's
`flux_diagModularK_eq_zero_of_const`, proved here by the scalar
route: constant weights make `K` a scalar matrix
(`diagModularK_const`), and scalars are flux-silent against
everything (`modularFlux_smul_one`). -/
theorem flux_zero_of_diagModularK_const (c : ℝ)
    (D : Matrix (Fin N) (Fin N) ℂ) :
    modularFlux (diagModularK (fun _ : Fin N => c)) D = 0 :=
  flux_eq_zero_of_diagModularK_eq_smul_one (diagModularK_const c) D

-- ============================================================================
-- §2. Uniqueness (Target T2)
-- ============================================================================

/-- **Scalar form of a constant diagonal** (Tier T1 target): a
diagonal matrix whose entries all agree is a scalar matrix. The
empty-index case is vacuous (any two matrices over an empty index
type agree entrywise because there are no entries). -/
theorem diagonal_eq_smul_one_of_forall_eq (k : Fin N → ℂ)
    (hk : ∀ i j, k i = k j) :
    ∃ s : ℂ, Matrix.diagonal k = s • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  by_cases hNe : Nonempty (Fin N)
  · obtain ⟨i₀⟩ := hNe
    refine ⟨k i₀, ?_⟩
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply,
        Matrix.one_apply_eq, smul_eq_mul, mul_one, hk i i₀]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  · exact ⟨0, by ext i j; exact (hNe ⟨i⟩).elim⟩

/-- **TARGET T2, core** (Tier T1 target): if the flux at
`K = diagModularK w` vanishes for EVERY `D`, then all log-weights
agree. Proof: the entry computation
(`FluxClassification.modularFlux_diagonal_apply`) at a single-entry
witness `D` (one entry `1` at `(i, j)`, zero elsewhere) gives
`I * ((-log (w i)) - (-log (w j))) = 0`, and `I ≠ 0`. This is the
center-of-the-matrix-algebra argument in one-entry form. -/
theorem log_eq_of_silent (w : Fin N → ℝ)
    (h : ∀ D : Matrix (Fin N) (Fin N) ℂ, modularFlux (diagModularK w) D = 0) :
    ∀ i j, Real.log (w i) = Real.log (w j) := by
  intro i j
  by_contra hne
  -- The single-entry witness at `(i, j)`.
  set D : Matrix (Fin N) (Fin N) ℂ :=
    fun a b => if a = i ∧ b = j then (1 : ℂ) else 0 with hDdef
  have hentry : (modularFlux (Matrix.diagonal
      (fun j => ((-Real.log (w j) : ℝ) : ℂ))) D) i j = 0 := by
    have h0 := h D
    exact congrFun (congrFun h0 i) j
  rw [modularFlux_diagonal_apply] at hentry
  have hDij : D i j = 1 := by simp [hDdef]
  rw [hDij, mul_one] at hentry
  have hk : ((-Real.log (w i) : ℝ) : ℂ) = ((-Real.log (w j) : ℝ) : ℂ) := by
    rcases mul_eq_zero.mp hentry with hI | hsub
    · exact absurd hI Complex.I_ne_zero
    · exact sub_eq_zero.mp hsub
  have hreal : (-Real.log (w i) : ℝ) = (-Real.log (w j) : ℝ) := by
    exact_mod_cast hk
  exact hne (neg_inj.mp hreal)

/-- **TARGET T2, scalar form** (Tier T1 target): a fully silent
built modular Hamiltonian is a scalar matrix — silence for every
probe forces `diagModularK w = s • 1`. -/
theorem diagModularK_eq_smul_one_of_silent (w : Fin N → ℝ)
    (h : ∀ D : Matrix (Fin N) (Fin N) ℂ, modularFlux (diagModularK w) D = 0) :
    ∃ s : ℂ, diagModularK w = s • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  have hlog := log_eq_of_silent w h
  obtain ⟨s, hs⟩ := diagonal_eq_smul_one_of_forall_eq
    (fun j => ((-Real.log (w j) : ℝ) : ℂ))
    (fun i j => by rw [hlog i j])
  refine ⟨s, ?_⟩
  show Matrix.diagonal (fun j => ((-Real.log (w j) : ℝ) : ℂ))
    = s • (1 : Matrix (Fin N) (Fin N) ℂ)
  exact hs

/-- **TARGET T2 — UNIQUENESS, headline iff** (Tier T1 target): the
built modular Hamiltonian `diagModularK w` is flux-silent against
every probe iff all its log-weights agree:
`(∀ D, modularFlux (diagModularK w) D = 0) ↔
  ∀ i j, Real.log (w i) = Real.log (w j)`.
The void (all sectors at one level) is the only fully silent
state; anything with a log-weight gap speaks to the single-entry
probe at the gap. Backward direction: the landed classification
(`FluxClassification.classification_diagModularK`) — distinct
log-weight sectors do not exist when all log-weights agree. -/
theorem silent_iff_log_const (w : Fin N → ℝ) :
    (∀ D : Matrix (Fin N) (Fin N) ℂ, modularFlux (diagModularK w) D = 0)
      ↔ ∀ i j, Real.log (w i) = Real.log (w j) := by
  constructor
  · exact log_eq_of_silent w
  · intro hlog D
    rw [classification_diagModularK]
    intro i j hij
    exact (hij (hlog i j)).elim

/-- **TARGET T2 at positive weights** (Tier T1 target): for
strictly positive weights, `Real.log` is injective, so full silence
at `diagModularK w` is exactly constancy of the weights themselves:
`(∀ D, modularFlux (diagModularK w) D = 0) ↔ ∀ i j, w i = w j`.
At bare weights without positivity only the log form
(`silent_iff_log_const`) is claimed — see the header fence. -/
theorem silent_iff_weights_const_of_pos (w : Fin N → ℝ)
    (hw : ∀ j, 0 < w j) :
    (∀ D : Matrix (Fin N) (Fin N) ℂ, modularFlux (diagModularK w) D = 0)
      ↔ ∀ i j, w i = w j := by
  rw [silent_iff_log_const]
  constructor
  · intro hlog i j
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr (hw i))
      (Set.mem_Ioi.mpr (hw j)) (hlog i j)
  · intro hconst i j
    rw [hconst i j]

end Flux

-- ============================================================================
-- §3. β-blindness (Target T3)
-- ============================================================================

section Separation

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **TARGET T3 — β-BLINDNESS** (Tier T1 target): at degenerate
energies (`E` constant), the multi-sector separation is the flat
charge average at EVERY real `β`:

    `sepN q E β = (Σᵢ qᵢ) / (card ι)` for all `β`.

Rung 2 proved the `β = 0` case (`sepN_zero_beta`); at degenerate
energies every Gibbs weight equals the common factor
`e^{−βc}`, which cancels between numerator and denominator at
every `β` — the void has no temperature. The energies are an
INPUT (fence K-TV1 of the rung stands); no charge value is
derived. -/
theorem sepN_eq_average_of_forall_eq (q E : ι → ℝ) (c : ℝ)
    (hE : ∀ i, E i = c) (β : ℝ) :
    sepN q E β = (∑ i, q i) / (Fintype.card ι : ℝ) := by
  have hw : ∀ i, Real.exp (-(β * E i)) = Real.exp (-(β * c)) :=
    fun i => by rw [hE i]
  have ht : Real.exp (-(β * c)) ≠ 0 := Real.exp_ne_zero _
  have hnum : (∑ i, q i * Real.exp (-(β * E i)))
      = (∑ i, q i) * Real.exp (-(β * c)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by rw [hw i])
  have hden : (∑ i, Real.exp (-(β * E i)))
      = (Fintype.card ι : ℝ) * Real.exp (-(β * c)) := by
    have e : (∑ i, Real.exp (-(β * E i)))
        = ∑ _i : ι, Real.exp (-(β * c)) :=
      Finset.sum_congr rfl (fun i _ => hw i)
    rw [e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold sepN
  rw [hnum, hden]
  exact mul_div_mul_right _ _ ht

/-- **TARGET T3, constant-energy form** (Tier T1 target): with the
energy assignment literally constant, `sepN q (fun _ => c) β` is
the flat charge average at every `β`. -/
theorem sepN_eq_average_const (q : ι → ℝ) (c β : ℝ) :
    sepN q (fun _ => c) β = (∑ i, q i) / (Fintype.card ι : ℝ) :=
  sepN_eq_average_of_forall_eq q (fun _ => c) c (fun _ => rfl) β

/-- **TARGET T3, β-independence form** (Tier T1 target): at
degenerate energies the separation does not depend on `β` at all:
`sepN q E β₁ = sepN q E β₂` for any two inverse temperatures. -/
theorem sepN_eq_of_forall_eq (q E : ι → ℝ) (c : ℝ) (hE : ∀ i, E i = c)
    (β₁ β₂ : ℝ) :
    sepN q E β₁ = sepN q E β₂ := by
  rw [sepN_eq_average_of_forall_eq q E c hE β₁,
    sepN_eq_average_of_forall_eq q E c hE β₂]

/-- **TARGET T3, contrapositive companion** (Tier T1 target): if
the separation at some `β` is off the flat charge average, the
energies are not all equal — a measured departure from flatness
certifies a gap somewhere. This is `sepN_eq_average_of_forall_eq`
contraposed; no converse is claimed (a particular charge
assignment can sit on the average at a particular `β` even with
gaps present). -/
theorem not_exists_const_of_sepN_ne_average (q E : ι → ℝ) (β : ℝ)
    (h : sepN q E β ≠ (∑ i, q i) / (Fintype.card ι : ℝ)) :
    ¬ ∃ c, ∀ i, E i = c := by
  rintro ⟨c, hc⟩
  exact h (sepN_eq_average_of_forall_eq q E c hc β)

end Separation

-- Axiom check (all declarations): expect exactly
-- [propext, Classical.choice, Quot.sound] on every line.
#print axioms modularFlux_smul_one
#print axioms diagModularK_const
#print axioms flux_eq_zero_of_diagModularK_eq_smul_one
#print axioms flux_zero_of_diagModularK_const
#print axioms diagonal_eq_smul_one_of_forall_eq
#print axioms log_eq_of_silent
#print axioms diagModularK_eq_smul_one_of_silent
#print axioms silent_iff_log_const
#print axioms silent_iff_weights_const_of_pos
#print axioms sepN_eq_average_of_forall_eq
#print axioms sepN_eq_average_const
#print axioms sepN_eq_of_forall_eq
#print axioms not_exists_const_of_sepN_ne_average

end ThetLogos.NullStart
