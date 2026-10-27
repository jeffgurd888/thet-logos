import ThetLogos.BlockingProjection
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic

/-!
# ThetLogos.BlockingProjectionNonab — RG-2c: the plaquette-matched
projection at a NONABELIAN small seat (S4)

HONESTY LEDGER (read before citing):

- **What this module proves.** RG-2a (`BlockingProjection`) proved
  that plaquette matching is **vacuous** at the RG-1 seat: the coarse
  plaquette there is a commutator in an *abelian* group, hence
  trivial, the coarse mean plaquette density is identically `0`, and
  no `β′` matches any `β > 0`. This module rebuilds the **same
  geometry** — fine `Fin 2` with swap shifts, coarse `Fin 1` with
  identity shifts, the same `flowBlocking` scheme — over a
  **nonabelian** group, the dihedral group `D₄` of order `8`, with
  its two-dimensional unitary representation (rotations by `90°`).
  At this seat the one-site coarse plaquette
  `V_μ V_ν V_μ⁻¹ V_ν⁻¹` is a genuine commutator, the coarse mean
  plaquette density is a genuine `β′`-dependent quantity, and the
  projection of RG-2 scoping §4 (S4) exists:

  * **Existence + uniqueness.** For every `β ≥ 0` there is a unique
    `β′` with `PlaquetteMatched flowσ flowσ' μS ρ₄ flowBlocking β β'`.
  * **Monotonicity.** The matched `β′(β)` is strictly increasing.
  * **The anchor, in its exact analogue.** The matched value at
    `β = 0` is `β′(0) < 0` — *not* `0`. At this seat
    `¬ PlaquetteMatched … 0 0` (the fine side at `0` has mean
    density `1`, the coarse side at `0` has `3/4`), even though
    `BlockedGibbsIsCoarseGibbs … 0 0` holds by the general Stage-2
    theorem. The projection therefore provably departs from the
    measure truth already at the anchor at this seat: matching one
    observable is not matching the measure (RG-2 scoping §0 hygiene,
    in sharp form).

- **Standing kill (RG-2 scoping §0, quoted).** "Any presentation of
  a projected `β′(β)` as an RG *flow* — in prose, dossier, or post —
  without a theorem equating the blocked measure with a coarse
  measure, is killed on sight." This module defines **no flow, no
  curve, no β-function, no iteration, and no fixed point of any
  dynamical system.** A projection is a statistic of a *pair* of
  measures. RG-1 is precisely the theorem that the measure equality
  the flow reading would need fails at the abelian seat for `β > 0`;
  nothing here touches that question at this seat either.

- **The mechanism (S4).** On both sides the Gibbs family is an
  exponential family in its own mean plaquette density
  (`wilsonAction = β · (n_p · meanPlaqDensity)`), so both
  expectations are values of one finite "tilt mean"
  `F_a(t) = (Σᵢ e^{−t aᵢ} aᵢ)/(Σᵢ e^{−t aᵢ})` — the coarse side at
  `t = 6β′`, the fine side at `t = 12β`. `F_a` is continuous,
  strictly antitone wherever `a` is nonconstant (a symmetrized-sum
  variance identity — no derivatives are taken), with limits the
  essential minimum and maximum of `a`. The coarse observable
  ranges over `[0, 5/3]` (minimum `0` at the trivial configuration,
  a witness at `5/3`), the fine expectation over `β ≥ 0` stays in
  `(0, 1]`, strictly inside the coarse range — existence by the
  intermediate value theorem, uniqueness by strict antitonicity.

- **Seat disclosures.** The group is `DihedralGroup 4` (order `8`),
  chosen because its faithful two-dimensional unitary
  representation has entries in `{0, ±1}` (rotations by `90°`): no
  irrational entries occur anywhere, and every commutator lands in
  `{1, r 2}` with `ρ(r 2) = −I`, so a noncommuting link pair has
  plaquette density exactly `2`. The coarse lattice has **one**
  site, as at the RG-1 seat: the coarseness is the point of the
  seat and is disclosed exactly as RG-1 disclosed its own. The
  blocked side of the matching is, by the design resolution
  recorded in `BlockingProjection`, the fine ensemble's mean
  plaquette density.

- *(finite-lattice discipline)* Everything is a finite lattice at
  fixed spacing and volume. No continuum statement, no uniformity
  in volume, no iteration.

- *(standing charter)* "Parts of the official Clay Yang–Mills
  statement closed by this module: 0." Dials: 0/4. NO CLAIM.
-/

namespace ThetLogos

open MeasureTheory Finset Filter
open scoped Matrix ENNReal NNReal Topology

/-! ## §1. The seat group, its topology, and its uniform measure

`DihedralGroup 4` carries no canonical topology or measurable-space
structure in Mathlib, so the seat installs the discrete ones,
mirroring the RG-1 seat (`LatticeBlockingFlow` §0). -/

instance : TopologicalSpace (DihedralGroup 4) := ⊥

instance : MeasurableSpace (DihedralGroup 4) := ⊤

instance : DiscreteTopology (DihedralGroup 4) := ⟨rfl⟩

instance : BorelSpace (DihedralGroup 4) :=
  ⟨borel_eq_top_of_discrete.symm⟩

/-- The uniform probability measure on the seat group: one eighth
of the counting measure. -/
noncomputable abbrev nbμG : Measure (DihedralGroup 4) :=
  (8 : ℝ≥0∞)⁻¹ • Measure.count

instance : IsProbabilityMeasure nbμG := ⟨by
  rw [Measure.smul_apply, smul_eq_mul, Measure.count_univ]
  simp only [ENat.card_eq_coe_natCard, Nat.card_eq_fintype_card,
    DihedralGroup.card]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

instance : Measure.IsInvInvariant nbμG where
  inv_eq_self := by
    show Measure.map Inv.inv ((8 : ℝ≥0∞)⁻¹ • Measure.count)
      = (8 : ℝ≥0∞)⁻¹ • Measure.count
    rw [Measure.map_smul _ measurable_inv.aemeasurable,
      Measure.map_inv_eq_self]

theorem nbμG_singleton (g : DihedralGroup 4) :
    nbμG {g} = (8 : ℝ≥0∞)⁻¹ := by
  simp [Measure.smul_apply]

/-! ## §2. The two-dimensional representation of `D₄`

The faithful two-dimensional unitary representation of the
dihedral group: rotations by `90°` and a reflection, with all
entries in `{0, ±1}` — no irrational numbers occur, which is what
makes every trace in this module exactly computable. -/

section NbRep

/-- Rotation by `90°`. -/
def nbRot : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

/-- The reflection `diag(1, -1)`. -/
def nbRefl : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem nbRot_sq : nbRot ^ 2 = -1 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nbRot, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem nbRot_pow_four : nbRot ^ 4 = 1 := by
  have h : nbRot ^ 4 = (nbRot ^ 2) ^ 2 := by rw [← pow_mul]
  rw [h, nbRot_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem nbRot_mem : nbRot ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nbRot, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] <;>
    norm_num

theorem nbRefl_mem : nbRefl ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nbRefl, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] <;>
    norm_num

/-- The rotation matrix indexed by `ZMod 4`: `nbRotZ i = nbRot ^ i.val`. -/
def nbRotZ (i : ZMod 4) : Matrix (Fin 2) (Fin 2) ℂ := nbRot ^ i.val

theorem nbRotZ_zero : nbRotZ 0 = 1 := by
  simp [nbRotZ]

theorem nbRot_pow_mod (k : ℕ) : nbRot ^ (k % 4) = nbRot ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k 4, pow_add, pow_mul, nbRot_pow_four,
    one_pow, mul_one]

theorem nbRotZ_add (i j : ZMod 4) :
    nbRotZ (i + j) = nbRotZ i * nbRotZ j := by
  unfold nbRotZ
  rw [ZMod.val_add, nbRot_pow_mod, pow_add]

theorem nbRotZ_mem (i : ZMod 4) :
    nbRotZ i ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  pow_mem nbRot_mem _

theorem nbRefl_mul_self : nbRefl * nbRefl = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nbRefl, Matrix.mul_apply, Fin.sum_univ_two]

/-- The reflection conjugates rotations to their inverses:
`refl * rot^m = rot^(4-m) * refl` for `m ≤ 4`. -/
theorem nbRefl_mul_rot_pow (m : ℕ) (hm : m ≤ 4) :
    nbRefl * nbRot ^ m = nbRot ^ (4 - m) * nbRefl := by
  interval_cases m <;>
    simp only [pow_zero, pow_one, nbRot_sq, pow_succ] <;>
    (try rw [nbRot_pow_four]) <;>
    (try (ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [nbRot, nbRefl, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num))

theorem nbRefl_mul_rotZ (i : ZMod 4) :
    nbRefl * nbRotZ i = nbRotZ (-i) * nbRefl := by
  have hval : (-i).val = (4 - i.val) % 4 := ZMod.neg_val' i
  unfold nbRotZ
  rw [hval, nbRot_pow_mod]
  exact nbRefl_mul_rot_pow i.val (by
    have := ZMod.val_lt i
    omega)

/-- The representation matrices: rotations act as rotations,
reflections as a rotation times the fixed reflection. -/
def nbRepMat : DihedralGroup 4 → Matrix (Fin 2) (Fin 2) ℂ
  | .r i => nbRotZ i
  | .sr i => nbRotZ (-i) * nbRefl

theorem nbRepMat_mem (g : DihedralGroup 4) :
    nbRepMat g ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  cases g with
  | r i => exact nbRotZ_mem i
  | sr i => exact mul_mem (nbRotZ_mem _) nbRefl_mem

/-- The two-dimensional unitary representation of `D₄`. -/
def nbRep : DihedralGroup 4 →* ↥(Matrix.unitaryGroup (Fin 2) ℂ) where
  toFun g := ⟨nbRepMat g, nbRepMat_mem g⟩
  map_one' := by
    apply Subtype.ext
    show nbRepMat 1 = 1
    rw [DihedralGroup.one_def]
    exact nbRotZ_zero
  map_mul' := by
    intro g h
    apply Subtype.ext
    show nbRepMat (g * h) = nbRepMat g * nbRepMat h
    cases g with
    | r i =>
      cases h with
      | r j =>
        rw [DihedralGroup.r_mul_r]
        exact nbRotZ_add i j
      | sr j =>
        rw [DihedralGroup.r_mul_sr]
        show nbRotZ (-(j - i)) * nbRefl
          = nbRotZ i * (nbRotZ (-j) * nbRefl)
        rw [show -(j - i) = i + -j by ring, nbRotZ_add, Matrix.mul_assoc]
    | sr i =>
      cases h with
      | r j =>
        rw [DihedralGroup.sr_mul_r]
        show nbRotZ (-(i + j)) * nbRefl
          = (nbRotZ (-i) * nbRefl) * nbRotZ j
        rw [show -(i + j) = -i + -j by ring, nbRotZ_add,
          Matrix.mul_assoc (nbRotZ (-i)) nbRefl (nbRotZ j),
          nbRefl_mul_rotZ j, ← Matrix.mul_assoc]
      | sr j =>
        rw [DihedralGroup.sr_mul_sr]
        show nbRotZ (j - i)
          = (nbRotZ (-i) * nbRefl) * (nbRotZ (-j) * nbRefl)
        rw [show j - i = -i + j by ring, nbRotZ_add,
          Matrix.mul_assoc (nbRotZ (-i)) nbRefl (nbRotZ (-j) * nbRefl),
          ← Matrix.mul_assoc nbRefl (nbRotZ (-j)) nbRefl,
          nbRefl_mul_rotZ (-j)]
        simp [Matrix.mul_assoc, nbRefl_mul_self]

theorem repMatrix_nbRep (g : DihedralGroup 4) :
    repMatrix nbRep g = nbRepMat g := rfl

theorem nbRep_continuous :
    Continuous fun g => repMatrix nbRep g :=
  continuous_of_discreteTopology

/-- The quarter-turn acts as `nbRot` itself. -/
theorem nbRepMat_r_one : nbRepMat (DihedralGroup.r 1) = nbRot := by
  have h1 : (1 : ZMod 4).val = 1 := by decide
  show nbRotZ 1 = nbRot
  rw [nbRotZ, h1, pow_one]

/-- The half-turn `r 2` maps to `-I`: its trace is `-2`. -/
theorem nb_trace_r2 :
    (Matrix.trace (nbRepMat (DihedralGroup.r 2))).re = -2 := by
  have h2 : (2 : ZMod 4).val = 2 := by decide
  show (Matrix.trace (nbRotZ 2)).re = -2
  rw [nbRotZ, h2, nbRot_sq]
  simp [Matrix.trace_neg, Matrix.trace_one]

/-- The identity has trace `2` (the representation dimension). -/
theorem nb_trace_one :
    (Matrix.trace (nbRepMat 1)).re = 2 := by
  rw [DihedralGroup.one_def]
  show (Matrix.trace (nbRotZ 0)).re = 2
  rw [nbRotZ_zero]
  simp [Matrix.trace_one]

end NbRep

/-! ## §3. The coarse observable is non-degenerate

The one-site coarse plaquette is the genuine commutator of the two
link values. In `D₄` every commutator is `1` or `r 2`, and
`ρ(r 2) = -I` — so every coarse plaquette density is exactly `0` or
exactly `2`, and both values occur. -/

section NbCoarse

/-- The coarse mean plaquette density at the nonabelian seat. -/
noncomputable abbrev nbCoarse (V : Config (Fin 1) (DihedralGroup 4)) : ℝ :=
  meanPlaqDensity flowσ' nbRep V

theorem two_mul_zmod4 (x : ZMod 4) :
    (2 : ZMod 4) * x = 0 ∨ (2 : ZMod 4) * x = 2 := by
  revert x
  decide

/-- Every commutator in `D₄` is `1` or the half-turn `r 2`. -/
theorem nb_comm_cases (a b : DihedralGroup 4) :
    a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = DihedralGroup.r 2 := by
  cases a with
  | r i =>
    cases b with
    | r j =>
      left
      simp only [DihedralGroup.r_mul_r, DihedralGroup.inv_r]
      rw [show i + j + -i + -j = (0 : ZMod 4) by ring]
      exact DihedralGroup.one_def.symm
    | sr j =>
      simp only [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr, DihedralGroup.inv_r, DihedralGroup.inv_sr]
      rw [show j - (j - i + -i) = 2 * i by ring]
      rcases two_mul_zmod4 i with h | h <;> rw [h]
      · exact Or.inl DihedralGroup.one_def.symm
      · exact Or.inr rfl
  | sr i =>
    cases b with
    | r j =>
      simp only [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr,
        DihedralGroup.r_mul_r, DihedralGroup.inv_r, DihedralGroup.inv_sr]
      rw [show i - (i + j) + -j = -(2 * j) by ring,
        show -(2 * j) = 2 * (-j) by ring]
      rcases two_mul_zmod4 (-j) with h | h <;> rw [h]
      · exact Or.inl DihedralGroup.one_def.symm
      · exact Or.inr rfl
    | sr j =>
      simp only [DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr,
        DihedralGroup.inv_sr]
      rw [show j - (i - (j - i)) = 2 * (j - i) by ring]
      rcases two_mul_zmod4 (j - i) with h | h <;> rw [h]
      · exact Or.inl DihedralGroup.one_def.symm
      · exact Or.inr rfl

/-- At the coarse seat every plaquette is a commutator of the two
link values at the site. -/
theorem nb_plaquette_coarse (V : Config (Fin 1) (DihedralGroup 4))
    (x : Fin 1) (μ ν : Fin 4) :
    plaquette flowσ' V x μ ν
      = V (x, μ) * V (x, ν) * (V (x, μ))⁻¹ * (V (x, ν))⁻¹ := by
  unfold plaquette
  simp only [flowσ'_apply]

theorem nb_density_eq_zero_of (V : Config (Fin 1) (DihedralGroup 4))
    (x : Fin 1) (μ ν : Fin 4)
    (h : V (x, μ) * V (x, ν) * (V (x, μ))⁻¹ * (V (x, ν))⁻¹ = 1) :
    plaquetteDensity flowσ' nbRep V x μ ν = 0 := by
  unfold plaquetteDensity
  rw [nb_plaquette_coarse, h, repMatrix_nbRep, nb_trace_one]
  norm_num

theorem nb_density_eq_two_of (V : Config (Fin 1) (DihedralGroup 4))
    (x : Fin 1) (μ ν : Fin 4)
    (h : V (x, μ) * V (x, ν) * (V (x, μ))⁻¹ * (V (x, ν))⁻¹
      = DihedralGroup.r 2) :
    plaquetteDensity flowσ' nbRep V x μ ν = 2 := by
  unfold plaquetteDensity
  rw [nb_plaquette_coarse, h, repMatrix_nbRep, nb_trace_r2]
  norm_num

/-- Every coarse plaquette density at this seat is `0` or `2`. -/
theorem nb_coarse_density_cases (V : Config (Fin 1) (DihedralGroup 4))
    (x : Fin 1) (μ ν : Fin 4) :
    plaquetteDensity flowσ' nbRep V x μ ν = 0
      ∨ plaquetteDensity flowσ' nbRep V x μ ν = 2 := by
  rcases nb_comm_cases (V (x, μ)) (V (x, ν)) with h | h
  · exact Or.inl (nb_density_eq_zero_of V x μ ν h)
  · exact Or.inr (nb_density_eq_two_of V x μ ν h)

theorem nbCoarse_nonneg (V : Config (Fin 1) (DihedralGroup 4)) :
    0 ≤ nbCoarse V := by
  unfold nbCoarse meanPlaqDensity
  apply div_nonneg _ (by positivity)
  refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun μ _ =>
    Finset.sum_nonneg fun ν _ => ?_
  exact (plaquetteDensity_mem_Icc flowσ' nbRep (by norm_num) V x μ ν).1

theorem nbCoarse_trivial : nbCoarse (fun _ => 1) = 0 := by
  have hd : ∀ (x : Fin 1) (μ ν : Fin 4),
      plaquetteDensity flowσ' nbRep (fun _ => (1 : DihedralGroup 4)) x μ ν
        = 0 := by
    intro x μ ν
    unfold plaquetteDensity
    rw [plaquette_one, repMatrix_nbRep, nb_trace_one]
    norm_num
  unfold nbCoarse meanPlaqDensity
  rw [Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero
    (fun μ _ => Finset.sum_eq_zero (fun ν _ => hd x μ ν)))]
  simp

theorem nbIoi0 : Finset.Ioi (0 : Fin 4) = {1, 2, 3} := by decide
theorem nbIoi1 : Finset.Ioi (1 : Fin 4) = {2, 3} := by decide
theorem nbIoi2 : Finset.Ioi (2 : Fin 4) = {3} := by decide
theorem nbIoi3 : Finset.Ioi (3 : Fin 4) = ∅ := by decide

theorem nb_sum_Ioi0 (f : Fin 4 → ℝ) :
    ∑ ν ∈ Finset.Ioi (0 : Fin 4), f ν = f 1 + f 2 + f 3 := by
  rw [nbIoi0, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, add_assoc]

theorem nb_sum_Ioi1 (f : Fin 4 → ℝ) :
    ∑ ν ∈ Finset.Ioi (1 : Fin 4), f ν = f 2 + f 3 := by
  rw [nbIoi1, Finset.sum_insert (by decide), Finset.sum_singleton]

theorem nb_sum_Ioi2 (f : Fin 4 → ℝ) :
    ∑ ν ∈ Finset.Ioi (2 : Fin 4), f ν = f 3 := by
  rw [nbIoi2, Finset.sum_singleton]

theorem nb_sum_Ioi3 (f : Fin 4 → ℝ) :
    ∑ ν ∈ Finset.Ioi (3 : Fin 4), f ν = 0 := by
  rw [nbIoi3, Finset.sum_empty]

/-- First witness: links `r 1` and `sr 0` in directions `0, 1`
(their commutator is `r 2`), all other links trivial. -/
def nbVW : Config (Fin 1) (DihedralGroup 4) :=
  Function.update
    (Function.update (fun _ => (1 : DihedralGroup 4)) (0, 0)
      (DihedralGroup.r 1))
    (0, 1) (DihedralGroup.sr 0)

theorem nbCoarse_nbVW : nbCoarse nbVW = 1 / 3 := by
  have d01 : plaquetteDensity flowσ' nbRep nbVW 0 0 1 = 2 :=
    nb_density_eq_two_of nbVW 0 0 1 (by decide)
  have d02 : plaquetteDensity flowσ' nbRep nbVW 0 0 2 = 0 :=
    nb_density_eq_zero_of nbVW 0 0 2 (by decide)
  have d03 : plaquetteDensity flowσ' nbRep nbVW 0 0 3 = 0 :=
    nb_density_eq_zero_of nbVW 0 0 3 (by decide)
  have d12 : plaquetteDensity flowσ' nbRep nbVW 0 1 2 = 0 :=
    nb_density_eq_zero_of nbVW 0 1 2 (by decide)
  have d13 : plaquetteDensity flowσ' nbRep nbVW 0 1 3 = 0 :=
    nb_density_eq_zero_of nbVW 0 1 3 (by decide)
  have d23 : plaquetteDensity flowσ' nbRep nbVW 0 2 3 = 0 :=
    nb_density_eq_zero_of nbVW 0 2 3 (by decide)
  unfold nbCoarse meanPlaqDensity
  rw [Fin.sum_univ_one, Fin.sum_univ_four, nb_sum_Ioi0, nb_sum_Ioi1,
    nb_sum_Ioi2, nb_sum_Ioi3, d01, d02, d03, d12, d13, d23]
  norm_num [Fintype.card_fin]

/-- Second witness: five of the six link pairs do not commute, so
the coarse density reaches `5/3` — the coarse range reaches
strictly above `1`, which is what the fine side at `β = 0` needs
matched. -/
def nbVM : Config (Fin 1) (DihedralGroup 4) :=
  Function.update
    (Function.update
      (Function.update
        (Function.update (fun _ => (1 : DihedralGroup 4)) (0, 0)
          (DihedralGroup.r 1))
        (0, 1) (DihedralGroup.sr 0))
      (0, 2) (DihedralGroup.r 3))
    (0, 3) (DihedralGroup.sr 1)

theorem nbCoarse_nbVM : nbCoarse nbVM = 5 / 3 := by
  have d01 : plaquetteDensity flowσ' nbRep nbVM 0 0 1 = 2 :=
    nb_density_eq_two_of nbVM 0 0 1 (by decide)
  have d02 : plaquetteDensity flowσ' nbRep nbVM 0 0 2 = 0 :=
    nb_density_eq_zero_of nbVM 0 0 2 (by decide)
  have d03 : plaquetteDensity flowσ' nbRep nbVM 0 0 3 = 2 :=
    nb_density_eq_two_of nbVM 0 0 3 (by decide)
  have d12 : plaquetteDensity flowσ' nbRep nbVM 0 1 2 = 2 :=
    nb_density_eq_two_of nbVM 0 1 2 (by decide)
  have d13 : plaquetteDensity flowσ' nbRep nbVM 0 1 3 = 2 :=
    nb_density_eq_two_of nbVM 0 1 3 (by decide)
  have d23 : plaquetteDensity flowσ' nbRep nbVM 0 2 3 = 2 :=
    nb_density_eq_two_of nbVM 0 2 3 (by decide)
  unfold nbCoarse meanPlaqDensity
  rw [Fin.sum_univ_one, Fin.sum_univ_four, nb_sum_Ioi0, nb_sum_Ioi1,
    nb_sum_Ioi2, nb_sum_Ioi3, d01, d02, d03, d12, d13, d23]
  norm_num [Fintype.card_fin]

end NbCoarse

/-! ## §4. The fine observable: nonnegative, vanishing at the
trivial configuration, and positive somewhere -/

section NbFine

/-- The fine mean plaquette density at the nonabelian seat. -/
noncomputable abbrev nbFine (U : Config (Fin 2) (DihedralGroup 4)) : ℝ :=
  meanPlaqDensity flowσ nbRep U

theorem nbFine_nonneg (U : Config (Fin 2) (DihedralGroup 4)) :
    0 ≤ nbFine U := by
  unfold nbFine meanPlaqDensity
  apply div_nonneg _ (by positivity)
  refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun μ _ =>
    Finset.sum_nonneg fun ν _ => ?_
  exact (plaquetteDensity_mem_Icc flowσ nbRep (by norm_num) U x μ ν).1

theorem nbFine_trivial : nbFine (fun _ => 1) = 0 := by
  have hd : ∀ (x : Fin 2) (μ ν : Fin 4),
      plaquetteDensity flowσ nbRep (fun _ => (1 : DihedralGroup 4)) x μ ν
        = 0 := by
    intro x μ ν
    unfold plaquetteDensity
    rw [plaquette_one, repMatrix_nbRep, nb_trace_one]
    norm_num
  unfold nbFine meanPlaqDensity
  rw [Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero
    (fun μ _ => Finset.sum_eq_zero (fun ν _ => hd x μ ν)))]
  simp

/-- Fine witness: a single quarter-turn link at `(0, 0)`. The
plaquette at `(0, 0, 1)` is that link itself (every other link in
the plaquette is trivial), with trace `0`, hence density `1`. -/
def nbUW : Config (Fin 2) (DihedralGroup 4) :=
  Function.update (fun _ => (1 : DihedralGroup 4)) (0, 0)
    (DihedralGroup.r 1)

theorem nbFine_density_witness :
    plaquetteDensity flowσ nbRep nbUW 0 0 1 = 1 := by
  have e1 : nbUW (0, 0) = DihedralGroup.r 1 := by decide
  have e2 : nbUW (1, 1) = 1 := by decide
  have e3 : nbUW (1, 0) = 1 := by decide
  have e4 : nbUW (0, 1) = 1 := by decide
  unfold plaquetteDensity plaquette
  simp only [flowσ_apply_zero]
  rw [e1, e2, e3, e4]
  norm_num [repMatrix_nbRep, nbRepMat_r_one, Matrix.trace_fin_two, nbRot]

theorem nbFine_witness_lower : (1 : ℝ) / 12 ≤ nbFine nbUW := by
  have hden : ∀ (x : Fin 2) (μ ν : Fin 4),
      0 ≤ plaquetteDensity flowσ nbRep nbUW x μ ν :=
    fun x μ ν =>
      (plaquetteDensity_mem_Icc flowσ nbRep (by norm_num) nbUW x μ ν).1
  have hstep1 : plaquetteDensity flowσ nbRep nbUW 0 0 1
      ≤ ∑ ν ∈ Finset.Ioi (0 : Fin 4),
        plaquetteDensity flowσ nbRep nbUW 0 0 ν :=
    Finset.single_le_sum (fun ν _ => hden 0 0 ν) (by decide)
  have hstep2 : (∑ ν ∈ Finset.Ioi (0 : Fin 4),
        plaquetteDensity flowσ nbRep nbUW 0 0 ν)
      ≤ ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ,
        plaquetteDensity flowσ nbRep nbUW 0 μ ν :=
    Finset.single_le_sum
      (fun μ _ => Finset.sum_nonneg (fun ν _ => hden 0 μ ν))
      (Finset.mem_univ 0)
  have hstep3 : (∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ,
        plaquetteDensity flowσ nbRep nbUW 0 μ ν)
      ≤ ∑ x : Fin 2, ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ,
        plaquetteDensity flowσ nbRep nbUW x μ ν :=
    Finset.single_le_sum
      (f := fun x => ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ,
        plaquetteDensity flowσ nbRep nbUW x μ ν)
      (fun x _ => Finset.sum_nonneg
        (fun μ _ => Finset.sum_nonneg (fun ν _ => hden x μ ν)))
      (Finset.mem_univ 0)
  have hS : (1 : ℝ) ≤ ∑ x : Fin 2, ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ,
      plaquetteDensity flowσ nbRep nbUW x μ ν :=
    nbFine_density_witness ▸ hstep1.trans (hstep2.trans hstep3)
  have hcard : ((Fintype.card (Fin 2) : ℕ) : ℝ) = 2 := by
    norm_num [Fintype.card_fin]
  unfold nbFine meanPlaqDensity
  rw [hcard, le_div_iff₀ (by norm_num : (0 : ℝ) < 2 * 6)]
  have he : (1 : ℝ) / 12 * (2 * 6) = 1 := by norm_num
  rw [he]
  exact hS

end NbFine

/-! ## §5. The coarse total over all configurations

Summing the coarse density over all `8⁴ = 4096` configurations:
each plaquette-density sum factors through the two links it uses
(`64` free choices for the other two links), and the pair-density
total over `D₄ × D₄` is `48` (exactly `24` of the `64` pairs do not
commute, each contributing `2`). Each of the six pairs therefore
contributes `64 · 48 = 3072`, and the mean over the six pairs gives
`∑_V A_c(V) = 3072` — whence `A_c` averages to `3072 / 4096 = 3/4`
under the uniform measure. -/

section NbTotal

/-- The plaquette density of a link pair, as a function of the two
link values alone. -/
noncomputable def nbPairDens (a b : DihedralGroup 4) : ℝ :=
  1 - (Matrix.trace (nbRepMat (a * b * a⁻¹ * b⁻¹))).re / 2

theorem nb_density_eq_pairDens (V : Config (Fin 1) (DihedralGroup 4))
    (x : Fin 1) (μ ν : Fin 4) :
    plaquetteDensity flowσ' nbRep V x μ ν
      = nbPairDens (V (x, μ)) (V (x, ν)) := by
  unfold plaquetteDensity nbPairDens
  rw [nb_plaquette_coarse, repMatrix_nbRep]
  norm_num

theorem nbPairDens_eq_zero_of {a b : DihedralGroup 4}
    (h : a * b * a⁻¹ * b⁻¹ = 1) : nbPairDens a b = 0 := by
  unfold nbPairDens
  rw [h, nb_trace_one]
  norm_num

theorem nbPairDens_eq_two_of {a b : DihedralGroup 4}
    (h : a * b * a⁻¹ * b⁻¹ = DihedralGroup.r 2) :
    nbPairDens a b = 2 := by
  unfold nbPairDens
  rw [h, nb_trace_r2]
  norm_num

/-- Exactly `24` of the `64` link pairs have commutator `r 2`, each
contributing density `2`: the pair-density total is `48`. -/
theorem nbPairDens_sum : ∑ a, ∑ b, nbPairDens a b = 48 := by
  have hcount : (Finset.univ.filter
      (fun p : DihedralGroup 4 × DihedralGroup 4 =>
        p.1 * p.2 * p.1⁻¹ * p.2⁻¹ = DihedralGroup.r 2)).card = 24 := by
    decide
  have hval : ∀ p : DihedralGroup 4 × DihedralGroup 4,
      nbPairDens p.1 p.2
        = if p.1 * p.2 * p.1⁻¹ * p.2⁻¹ = DihedralGroup.r 2
          then 2 else 0 := by
    intro p
    rcases nb_comm_cases p.1 p.2 with h | h
    · have hne : ¬ (p.1 * p.2 * p.1⁻¹ * p.2⁻¹
          = DihedralGroup.r 2) := by
        rw [h]
        decide
      rw [nbPairDens_eq_zero_of h, if_neg hne]
    · rw [nbPairDens_eq_two_of h, if_pos h]
  have hprod : ∑ p : DihedralGroup 4 × DihedralGroup 4,
        nbPairDens p.1 p.2 = ∑ a, ∑ b, nbPairDens a b :=
    Fintype.sum_prod_type (fun p => nbPairDens p.1 p.2)
  rw [← hprod,
    Finset.sum_congr rfl (fun p _ => hval p), ← Finset.sum_filter,
    Finset.sum_const, hcount]
  norm_num [nsmul_eq_mul]

/-- Configurations with two pinned link values are the same as
configurations of the remaining two links. -/
def nbFiberEquiv (ℓ₁ ℓ₂ : Fin 1 × Fin 4) (hℓ : ℓ₁ ≠ ℓ₂)
    (a b : DihedralGroup 4) :
    {V : Config (Fin 1) (DihedralGroup 4) // V ℓ₁ = a ∧ V ℓ₂ = b}
      ≃ ({ℓ : Fin 1 × Fin 4 // ℓ ≠ ℓ₁ ∧ ℓ ≠ ℓ₂} →
          DihedralGroup 4) where
  toFun V ℓ := V.1 ℓ.1
  invFun W := ⟨fun ℓ => if h : ℓ = ℓ₁ then a
      else if h' : ℓ = ℓ₂ then b else W ⟨ℓ, h, h'⟩, by
    refine ⟨?_, ?_⟩
    · show (if h : ℓ₁ = ℓ₁ then a
        else if h' : ℓ₁ = ℓ₂ then b else W ⟨ℓ₁, h, h'⟩) = a
      rw [dif_pos rfl]
    · show (if h : ℓ₂ = ℓ₁ then a
        else if h' : ℓ₂ = ℓ₂ then b else W ⟨ℓ₂, h, h'⟩) = b
      rw [dif_neg (fun hh : ℓ₂ = ℓ₁ => hℓ hh.symm), dif_pos rfl]⟩
  left_inv V := by
    apply Subtype.ext
    funext ℓ
    by_cases h1 : ℓ = ℓ₁
    · show (if h : ℓ = ℓ₁ then a
        else if h' : ℓ = ℓ₂ then b else V.1 ℓ) = V.1 ℓ
      rw [dif_pos h1, h1]
      exact V.2.1.symm
    · by_cases h2 : ℓ = ℓ₂
      · show (if h : ℓ = ℓ₁ then a
          else if h' : ℓ = ℓ₂ then b else V.1 ℓ) = V.1 ℓ
        rw [dif_neg h1, dif_pos h2, h2]
        exact V.2.2.symm
      · show (if h : ℓ = ℓ₁ then a
          else if h' : ℓ = ℓ₂ then b else V.1 ℓ) = V.1 ℓ
        rw [dif_neg h1, dif_neg h2]
  right_inv W := by
    funext ℓ
    obtain ⟨h1, h2⟩ := ℓ.2
    show (if h : ℓ.1 = ℓ₁ then a
      else if h' : ℓ.1 = ℓ₂ then b else W ⟨ℓ.1, h, h'⟩) = W ℓ
    rw [dif_neg h1, dif_neg h2]

theorem nb_fiber_card (ℓ₁ ℓ₂ : Fin 1 × Fin 4) (hℓ : ℓ₁ ≠ ℓ₂)
    (a b : DihedralGroup 4) :
    (Finset.univ.filter
      (fun V : Config (Fin 1) (DihedralGroup 4) =>
        V ℓ₁ = a ∧ V ℓ₂ = b)).card = 64 := by
  have hsub : Fintype.card {ℓ : Fin 1 × Fin 4 // ℓ ≠ ℓ₁ ∧ ℓ ≠ ℓ₂}
      = 2 := by
    rw [Fintype.card_subtype]
    have hset : Finset.univ.filter (fun ℓ : Fin 1 × Fin 4 =>
          ℓ ≠ ℓ₁ ∧ ℓ ≠ ℓ₂) = Finset.univ \ {ℓ₁, ℓ₂} := by
      ext ℓ
      simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_sdiff,
        Finset.mem_insert, Finset.mem_singleton, not_or, true_and]
    rw [hset, Finset.card_sdiff, Finset.inter_univ, Finset.card_pair hℓ,
      Finset.card_univ]
    simp [Fintype.card_prod]
  rw [← Fintype.card_subtype,
    Fintype.card_congr (nbFiberEquiv ℓ₁ ℓ₂ hℓ a b), Fintype.card_pi,
    Finset.prod_const, Finset.card_univ, hsub]
  norm_num [DihedralGroup.card]

/-- Summing a two-link observable over all configurations factors:
`64` choices for the remaining two links times the pair total. -/
theorem nb_sum_factor (ℓ₁ ℓ₂ : Fin 1 × Fin 4) (hℓ : ℓ₁ ≠ ℓ₂)
    (F : DihedralGroup 4 → DihedralGroup 4 → ℝ) :
    ∑ V : Config (Fin 1) (DihedralGroup 4), F (V ℓ₁) (V ℓ₂)
      = 64 * ∑ a, ∑ b, F a b := by
  have key : ∑ y : DihedralGroup 4 × DihedralGroup 4,
        ∑ V ∈ (Finset.univ : Finset (Config (Fin 1) (DihedralGroup 4))).filter
            (fun V : Config (Fin 1) (DihedralGroup 4) =>
              (V ℓ₁, V ℓ₂) = y),
          F (V ℓ₁) (V ℓ₂)
      = ∑ V : Config (Fin 1) (DihedralGroup 4), F (V ℓ₁) (V ℓ₂) :=
    Finset.sum_fiberwise_of_maps_to
      (g := fun V : Config (Fin 1) (DihedralGroup 4) => (V ℓ₁, V ℓ₂))
      (fun V _ => Finset.mem_univ _)
      (fun V : Config (Fin 1) (DihedralGroup 4) => F (V ℓ₁) (V ℓ₂))
  have hprod : ∑ y : DihedralGroup 4 × DihedralGroup 4,
        ∑ V ∈ (Finset.univ : Finset (Config (Fin 1) (DihedralGroup 4))).filter
            (fun V : Config (Fin 1) (DihedralGroup 4) =>
              (V ℓ₁, V ℓ₂) = y),
          F (V ℓ₁) (V ℓ₂)
      = ∑ a, ∑ b, ∑ V ∈ (Finset.univ :
            Finset (Config (Fin 1) (DihedralGroup 4))).filter
          (fun V : Config (Fin 1) (DihedralGroup 4) =>
            (V ℓ₁, V ℓ₂) = (a, b)), F (V ℓ₁) (V ℓ₂) :=
    Fintype.sum_prod_type _
  rw [← key, hprod, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hfilter : Finset.univ.filter
        (fun V : Config (Fin 1) (DihedralGroup 4) =>
          (V ℓ₁, V ℓ₂) = (a, b))
      = Finset.univ.filter (fun V => V ℓ₁ = a ∧ V ℓ₂ = b) := by
    ext V
    simp [Prod.ext_iff]
  rw [hfilter, Finset.sum_eq_card_nsmul (b := F a b)
    (fun V hV => by
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hV).2
      rw [h1, h2]), nb_fiber_card ℓ₁ ℓ₂ hℓ]
  norm_num [nsmul_eq_mul]

/-- Each of the six plaquette positions contributes `64 · 48`. -/
theorem nb_pair_sum (μ ν : Fin 4) (hμν : μ ≠ ν) :
    ∑ V : Config (Fin 1) (DihedralGroup 4),
        plaquetteDensity flowσ' nbRep V 0 μ ν = 3072 := by
  have hℓ : ((0 : Fin 1), μ) ≠ (0, ν) :=
    fun hh => hμν (Prod.ext_iff.mp hh).2
  calc ∑ V : Config (Fin 1) (DihedralGroup 4),
        plaquetteDensity flowσ' nbRep V 0 μ ν
      = ∑ V : Config (Fin 1) (DihedralGroup 4),
          nbPairDens (V (0, μ)) (V (0, ν)) :=
        Finset.sum_congr rfl (fun V _ => nb_density_eq_pairDens V 0 μ ν)
    _ = 64 * ∑ a, ∑ b, nbPairDens a b :=
        nb_sum_factor (0, μ) (0, ν) hℓ _
    _ = 3072 := by rw [nbPairDens_sum]; norm_num

/-- The coarse density summed over all `4096` configurations. -/
theorem nb_sum_coarse_total :
    ∑ V : Config (Fin 1) (DihedralGroup 4), nbCoarse V = 3072 := by
  have key : ∀ V : Config (Fin 1) (DihedralGroup 4), nbCoarse V
      = (1 / 6) * ∑ μ, ∑ ν ∈ Finset.Ioi μ,
        plaquetteDensity flowσ' nbRep V 0 μ ν := by
    intro V
    unfold nbCoarse meanPlaqDensity
    rw [Fin.sum_univ_one,
      show ((Fintype.card (Fin 1) : ℕ) : ℝ) = 1 by
        norm_num [Fintype.card_fin], one_mul,
      div_eq_iff (by norm_num : (6 : ℝ) ≠ 0)]
    ring
  calc ∑ V : Config (Fin 1) (DihedralGroup 4), nbCoarse V
      = ∑ V : Config (Fin 1) (DihedralGroup 4), (1 / 6) *
          (plaquetteDensity flowσ' nbRep V 0 0 1
            + plaquetteDensity flowσ' nbRep V 0 0 2
            + plaquetteDensity flowσ' nbRep V 0 0 3
            + (plaquetteDensity flowσ' nbRep V 0 1 2
              + plaquetteDensity flowσ' nbRep V 0 1 3)
            + plaquetteDensity flowσ' nbRep V 0 2 3 + 0) := by
        refine Finset.sum_congr rfl fun V _ => ?_
        rw [key V, Fin.sum_univ_four, nb_sum_Ioi0, nb_sum_Ioi1,
          nb_sum_Ioi2, nb_sum_Ioi3]
    _ = (1 / 6) * (3072 + 3072 + 3072 + (3072 + 3072) + 3072 + 0) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_const_zero,
          nb_pair_sum 0 1 (by decide), nb_pair_sum 0 2 (by decide),
          nb_pair_sum 0 3 (by decide), nb_pair_sum 1 2 (by decide),
          nb_pair_sum 1 3 (by decide), nb_pair_sum 2 3 (by decide)]
    _ = 3072 := by norm_num

end NbTotal

/-! ## §6. The tilt-mean kit

For a finitely valued observable `a`, the Gibbs expectation in the
exponential family with weights `e^{−t·a}` is the **tilt mean**
`F_a(t) = (Σᵢ e^{−t aᵢ} aᵢ) / (Σᵢ e^{−t aᵢ})`. This section proves,
for nonconstant `a`: `F_a` is continuous, strictly antitone (by a
symmetrized-sum variance identity — no derivatives), strictly
between the essential minimum and maximum, with limits the minimum
at `t → +∞` and the maximum at `t → −∞`. Hence every value strictly
between min and max is attained exactly once. -/

section TiltKit

/-- The numerator of the tilt mean. -/
noncomputable def tiltNum {ι : Type*} [Fintype ι] (a : ι → ℝ) (t : ℝ) :
    ℝ :=
  ∑ i, Real.exp (-(t * a i)) * a i

/-- The denominator of the tilt mean. -/
noncomputable def tiltDen {ι : Type*} [Fintype ι] (a : ι → ℝ) (t : ℝ) :
    ℝ :=
  ∑ i, Real.exp (-(t * a i))

/-- The tilt mean `F_a(t)`. -/
noncomputable def tiltMean {ι : Type*} [Fintype ι] (a : ι → ℝ) (t : ℝ) :
    ℝ :=
  tiltNum a t / tiltDen a t

theorem tiltDen_pos {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ)
    (t : ℝ) : 0 < tiltDen a t := by
  unfold tiltDen
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

theorem tiltNum_sub {ι : Type*} [Fintype ι] (a : ι → ℝ) (c t : ℝ) :
    (∑ i, Real.exp (-(t * a i)) * (a i - c))
      = tiltNum a t - c * tiltDen a t := by
  unfold tiltNum tiltDen
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Shifting the observable by a constant shifts the tilt mean by
the same constant (the weights pick up a common factor). -/
theorem tiltMean_shift {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (c t : ℝ) :
    tiltMean (fun i => a i - c) t = tiltMean a t - c := by
  have hfac : ∀ i : ι, Real.exp (-(t * (a i - c)))
      = Real.exp (t * c) * Real.exp (-(t * a i)) := by
    intro i
    rw [← Real.exp_add]
    congr 1
    ring
  have hnum : tiltNum (fun i => a i - c) t
      = Real.exp (t * c) * (tiltNum a t - c * tiltDen a t) := by
    unfold tiltNum
    calc (∑ i, Real.exp (-(t * (a i - c))) * (a i - c))
        = ∑ i, Real.exp (t * c) * (Real.exp (-(t * a i)) * (a i - c)) :=
          Finset.sum_congr rfl fun i _ => by rw [hfac i]; ring
      _ = Real.exp (t * c) * ∑ i, Real.exp (-(t * a i)) * (a i - c) := by
          rw [Finset.mul_sum]
      _ = Real.exp (t * c) * (tiltNum a t - c * tiltDen a t) := by
          rw [tiltNum_sub]
  have hden : tiltDen (fun i => a i - c) t
      = Real.exp (t * c) * tiltDen a t := by
    unfold tiltDen
    calc (∑ i, Real.exp (-(t * (a i - c))))
        = ∑ i, Real.exp (t * c) * Real.exp (-(t * a i)) :=
          Finset.sum_congr rfl fun i _ => hfac i
      _ = Real.exp (t * c) * ∑ i, Real.exp (-(t * a i)) := by
          rw [Finset.mul_sum]
  unfold tiltMean
  rw [hnum, hden, mul_div_mul_left _ _ (Real.exp_ne_zero _), sub_div,
    mul_div_cancel_right₀ _ (tiltDen_pos a t).ne']

/-- Reflecting the observable reflects the tilt mean, with the tilt
parameter negated. -/
theorem tiltMean_neg {ι : Type*} [Fintype ι] (a : ι → ℝ) (t : ℝ) :
    tiltMean (fun i => -a i) t = - tiltMean a (-t) := by
  have harg : ∀ i : ι, -(t * -a i) = -((-t) * a i) := fun i => by ring
  have e1 : (∑ i, Real.exp (-(t * -a i)) * -a i)
      = - ∑ i, Real.exp (-((-t) * a i)) * a i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [harg i]; ring
  have e2 : (∑ i, Real.exp (-(t * -a i)))
      = ∑ i, Real.exp (-((-t) * a i)) :=
    Finset.sum_congr rfl fun i _ => by rw [harg i]
  unfold tiltMean tiltNum tiltDen
  rw [e1, e2, neg_div]

theorem tiltDen_continuous {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    Continuous (tiltDen a) := by
  unfold tiltDen
  apply continuous_finset_sum
  intro i _
  exact Real.continuous_exp.comp
    ((continuous_id.mul continuous_const).neg)

theorem tiltNum_continuous {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    Continuous (tiltNum a) := by
  unfold tiltNum
  apply continuous_finset_sum
  intro i _
  exact (Real.continuous_exp.comp
    ((continuous_id.mul continuous_const).neg)).mul continuous_const

theorem tiltMean_continuous {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) : Continuous (tiltMean a) := by
  unfold tiltMean
  exact (tiltNum_continuous a).div (tiltDen_continuous a)
    (fun t => (tiltDen_pos a t).ne')

/-- Strict antitonicity of the tilt mean for a nonconstant
observable: the numerator difference is a symmetrized variance
sum, nonnegative termwise and positive at one pair. -/
theorem tiltMean_strictAnti {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (hna : ¬ ∀ i j : ι, a i = a j) :
    StrictAnti (tiltMean a) := by
  obtain ⟨p, q, hpq⟩ : ∃ p q, a p ≠ a q := by
    by_contra hcon
    push_neg at hcon
    exact hna hcon
  intro s t hst
  haveI : Nonempty ι := ⟨p⟩
  have hfac : ∀ i j : ι, Real.exp (-(s * a i + t * a j))
        - Real.exp (-(t * a i + s * a j))
      = Real.exp (-(s * (a i + a j))) *
          (Real.exp (-((t - s) * a j))
            - Real.exp (-((t - s) * a i))) := by
    intro i j
    have e1 : -(s * (a i + a j)) + -((t - s) * a j)
        = -(s * a i + t * a j) := by ring
    have e2 : -(s * (a i + a j)) + -((t - s) * a i)
        = -(t * a i + s * a j) := by ring
    rw [mul_sub, ← Real.exp_add, ← Real.exp_add, e1, e2]
  have hterm : ∀ i j : ι, 0 ≤ (a i - a j) *
      (Real.exp (-(s * a i + t * a j))
        - Real.exp (-(t * a i + s * a j))) := by
    intro i j
    rcases le_total (a i) (a j) with hij | hij
    · have h1 : a i - a j ≤ 0 := sub_nonpos.mpr hij
      have h2 : Real.exp (-((t - s) * a j))
          - Real.exp (-((t - s) * a i)) ≤ 0 := by
        apply sub_nonpos.mpr
        apply Real.exp_le_exp.mpr
        have hts : 0 ≤ t - s := sub_nonneg.mpr hst.le
        have hmul := mul_le_mul_of_nonneg_left hij hts
        linarith
      have hE : 0 ≤ Real.exp (-(s * (a i + a j))) := (Real.exp_pos _).le
      have h3 : 0 ≤ (a i - a j) *
          (Real.exp (-((t - s) * a j))
            - Real.exp (-((t - s) * a i))) :=
        mul_nonneg_of_nonpos_of_nonpos h1 h2
      rw [hfac i j]
      calc (a i - a j) * (Real.exp (-(s * (a i + a j))) *
            (Real.exp (-((t - s) * a j))
              - Real.exp (-((t - s) * a i))))
          = Real.exp (-(s * (a i + a j))) * ((a i - a j) *
              (Real.exp (-((t - s) * a j))
                - Real.exp (-((t - s) * a i)))) := by ring
        _ ≥ 0 := mul_nonneg hE h3
    · have h1 : 0 ≤ a i - a j := sub_nonneg.mpr hij
      have h2 : 0 ≤ Real.exp (-((t - s) * a j))
          - Real.exp (-((t - s) * a i)) := by
        apply sub_nonneg.mpr
        apply Real.exp_le_exp.mpr
        have hts : 0 ≤ t - s := sub_nonneg.mpr hst.le
        have hmul := mul_le_mul_of_nonneg_left hij hts
        linarith
      have hE : 0 ≤ Real.exp (-(s * (a i + a j))) := (Real.exp_pos _).le
      have h3 : 0 ≤ (a i - a j) *
          (Real.exp (-((t - s) * a j))
            - Real.exp (-((t - s) * a i))) := mul_nonneg h1 h2
      rw [hfac i j]
      calc (a i - a j) * (Real.exp (-(s * (a i + a j))) *
            (Real.exp (-((t - s) * a j))
              - Real.exp (-((t - s) * a i))))
          = Real.exp (-(s * (a i + a j))) * ((a i - a j) *
              (Real.exp (-((t - s) * a j))
                - Real.exp (-((t - s) * a i)))) := by ring
        _ ≥ 0 := mul_nonneg hE h3
  have hsign : ∀ i j : ι, a i ≠ a j → 0 < (a i - a j) *
      (Real.exp (-(s * a i + t * a j))
        - Real.exp (-(t * a i + s * a j))) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have h1 : a i - a j < 0 := sub_neg.mpr hlt
      have h2 : Real.exp (-((t - s) * a j))
          - Real.exp (-((t - s) * a i)) < 0 := by
        apply sub_neg.mpr
        apply Real.exp_lt_exp.mpr
        have hts : 0 < t - s := sub_pos.mpr hst
        have hmul := mul_lt_mul_of_pos_left hlt hts
        linarith
      have hE : 0 < Real.exp (-(s * (a i + a j))) := Real.exp_pos _
      rw [hfac i j]
      calc (a i - a j) * (Real.exp (-(s * (a i + a j))) *
            (Real.exp (-((t - s) * a j))
              - Real.exp (-((t - s) * a i))))
          = Real.exp (-(s * (a i + a j))) * ((a i - a j) *
              (Real.exp (-((t - s) * a j))
                - Real.exp (-((t - s) * a i)))) := by ring
        _ > 0 := mul_pos hE (mul_pos_of_neg_of_neg h1 h2)
    · have h1 : 0 < a i - a j := sub_pos.mpr hgt
      have h2 : 0 < Real.exp (-((t - s) * a j))
          - Real.exp (-((t - s) * a i)) := by
        apply sub_pos.mpr
        apply Real.exp_lt_exp.mpr
        have hts : 0 < t - s := sub_pos.mpr hst
        have hmul := mul_lt_mul_of_pos_left hgt hts
        linarith
      have hE : 0 < Real.exp (-(s * (a i + a j))) := Real.exp_pos _
      rw [hfac i j]
      calc (a i - a j) * (Real.exp (-(s * (a i + a j))) *
            (Real.exp (-((t - s) * a j))
              - Real.exp (-((t - s) * a i))))
          = Real.exp (-(s * (a i + a j))) * ((a i - a j) *
              (Real.exp (-((t - s) * a j))
                - Real.exp (-((t - s) * a i)))) := by ring
        _ > 0 := mul_pos hE (mul_pos h1 h2)
  have hsym : ∀ F : ι → ι → ℝ, ∑ i, ∑ j, F i j
      = (1 / 2) * (∑ i, ∑ j, F i j + ∑ i, ∑ j, F j i) := by
    intro F
    have hswap : ∑ i, ∑ j, F j i = ∑ i, ∑ j, F i j :=
      Finset.sum_comm
    rw [hswap]
    ring
  have hmain : tiltNum a s * tiltDen a t - tiltNum a t * tiltDen a s
      = (1 / 2) * ∑ i, ∑ j, (a i - a j) *
          (Real.exp (-(s * a i + t * a j))
            - Real.exp (-(t * a i + s * a j))) := by
    have e1 : tiltNum a s * tiltDen a t - tiltNum a t * tiltDen a s
        = ∑ i, ∑ j, (a i * Real.exp (-(s * a i + t * a j))
            - a i * Real.exp (-(t * a i + s * a j))) := by
      unfold tiltNum tiltDen
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have m1 : Real.exp (-(s * a i)) * a i * Real.exp (-(t * a j))
          = a i * Real.exp (-(s * a i + t * a j)) := by
        rw [mul_comm (Real.exp (-(s * a i))) (a i), mul_assoc,
          ← Real.exp_add]
        congr 1
        ring
      have m2 : Real.exp (-(t * a i)) * a i * Real.exp (-(s * a j))
          = a i * Real.exp (-(t * a i + s * a j)) := by
        rw [mul_comm (Real.exp (-(t * a i))) (a i), mul_assoc,
          ← Real.exp_add]
        congr 1
        ring
      rw [m1, m2]
    rw [e1, hsym (fun i j => a i * Real.exp (-(s * a i + t * a j))
      - a i * Real.exp (-(t * a i + s * a j)))]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsum : 0 < ∑ i, ∑ j, (a i - a j) *
      (Real.exp (-(s * a i + t * a j))
        - Real.exp (-(t * a i + s * a j))) :=
    Finset.sum_pos' (fun i _ =>
      Finset.sum_nonneg (fun j _ => hterm i j))
      ⟨p, Finset.mem_univ p, Finset.sum_pos' (fun j _ => hterm p j)
        ⟨q, Finset.mem_univ q, hsign p q hpq⟩⟩
  have hpos : 0 < tiltNum a s * tiltDen a t - tiltNum a t * tiltDen a s := by
    rw [hmain]
    exact mul_pos (by norm_num) hsum
  have hDs := tiltDen_pos a s
  have hDt := tiltDen_pos a t
  unfold tiltMean
  rw [div_lt_div_iff₀ hDt hDs]
  linarith

/-- The tilt mean strictly exceeds any lower bound that is not
itself attained everywhere. -/
theorem tiltMean_gt {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ)
    (c : ℝ) (t : ℝ) (h0 : ∀ i, 0 ≤ a i - c) (h1 : ∃ i, 0 < a i - c) :
    c < tiltMean a t := by
  have hD := tiltDen_pos a t
  have hN : 0 < ∑ i, Real.exp (-(t * a i)) * (a i - c) :=
    Finset.sum_pos' (fun i _ => mul_nonneg (Real.exp_pos _).le (h0 i))
      (h1.imp fun i hi => ⟨Finset.mem_univ i, mul_pos (Real.exp_pos _) hi⟩)
  have hFc : tiltMean a t - c
      = (∑ i, Real.exp (-(t * a i)) * (a i - c)) / tiltDen a t := by
    have h2 : tiltMean a t - c
        = (tiltNum a t - c * tiltDen a t) / tiltDen a t := by
      unfold tiltMean
      rw [sub_div, mul_div_cancel_right₀ _ hD.ne']
    rw [h2, tiltNum_sub]
  have hdiv := div_pos hN hD
  linarith

/-- The tilt mean strictly falls short of any upper bound that is
not itself attained everywhere. -/
theorem tiltMean_lt {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ)
    (c : ℝ) (t : ℝ) (h0 : ∀ i, a i - c ≤ 0) (h1 : ∃ i, a i - c < 0) :
    tiltMean a t < c := by
  have hD := tiltDen_pos a t
  have hN : ∑ i, Real.exp (-(t * a i)) * (a i - c) < 0 :=
    Finset.sum_neg' (fun i _ => mul_nonpos_of_nonneg_of_nonpos
      (Real.exp_pos _).le (h0 i))
      (h1.imp fun i hi => ⟨Finset.mem_univ i,
        mul_neg_of_pos_of_neg (Real.exp_pos _) hi⟩)
  have hFc : tiltMean a t - c
      = (∑ i, Real.exp (-(t * a i)) * (a i - c)) / tiltDen a t := by
    have h2 : tiltMean a t - c
        = (tiltNum a t - c * tiltDen a t) / tiltDen a t := by
      unfold tiltMean
      rw [sub_div, mul_div_cancel_right₀ _ hD.ne']
    rw [h2, tiltNum_sub]
  have hdiv := div_neg_of_neg_of_pos hN hD
  linarith

/-- As `t → +∞`, the tilt mean converges to the minimum of the
observable (squeeze: it is nonnegative after shifting, and at most
the numerator, whose every term vanishes). -/
theorem tiltMean_tendsto_min {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (i₀ : ι) (hmin : ∀ i, a i₀ ≤ a i) :
    Tendsto (tiltMean a) atTop (nhds (a i₀)) := by
  have hb0 : ∀ i, 0 ≤ a i - a i₀ := fun i => sub_nonneg.mpr (hmin i)
  have hnum : Tendsto (fun t => ∑ i, Real.exp (-(t * (a i - a i₀)))
      * (a i - a i₀)) atTop (nhds 0) := by
    have hterm : ∀ i : ι, Tendsto
        (fun t => Real.exp (-(t * (a i - a i₀))) * (a i - a i₀))
        atTop (nhds 0) := by
      intro i
      rcases eq_or_lt_of_le (hb0 i) with h0 | hpos
      · have hfun : (fun t => Real.exp (-(t * (a i - a i₀)))
            * (a i - a i₀)) = fun _ => 0 := by
          funext t
          rw [← h0]
          simp
        rw [hfun]
        exact tendsto_const_nhds
      · have htop : Tendsto (fun t : ℝ => t * (a i - a i₀)) atTop atTop :=
          tendsto_id.atTop_mul_const hpos
        have hexp : Tendsto (fun t => Real.exp (-(t * (a i - a i₀))))
            atTop (nhds 0) :=
          Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp htop)
        simpa using hexp.mul_const (a i - a i₀)
    have hsum := tendsto_finset_sum Finset.univ (fun i _ => hterm i)
    simpa using hsum
  have hD1 : ∀ t : ℝ, 1 ≤ ∑ i, Real.exp (-(t * (a i - a i₀))) := by
    intro t
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun i => Real.exp (-(t * (a i - a i₀))))
      (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ i₀)
    have e : Real.exp (-(t * (a i₀ - a i₀))) = 1 := by simp
    rwa [e] at h
  have hDen : ∀ t : ℝ, tiltDen (fun i => a i - a i₀) t
      = ∑ i, Real.exp (-(t * (a i - a i₀))) := fun t => rfl
  have hF0 : ∀ t : ℝ, 0 ≤ tiltMean (fun i => a i - a i₀) t := by
    intro t
    unfold tiltMean tiltNum
    rw [hDen t]
    apply div_nonneg _ (le_trans zero_le_one (hD1 t))
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (Real.exp_pos _).le (hb0 i)
  have hFle : ∀ t : ℝ, tiltMean (fun i => a i - a i₀) t
      ≤ ∑ i, Real.exp (-(t * (a i - a i₀))) * (a i - a i₀) := by
    intro t
    unfold tiltMean tiltNum
    rw [hDen t, div_le_iff₀ (lt_of_lt_of_le zero_lt_one (hD1 t))]
    exact le_mul_of_one_le_right
      (Finset.sum_nonneg fun i _ =>
        mul_nonneg (Real.exp_pos _).le (hb0 i)) (hD1 t)
  have hlim_b : Tendsto (tiltMean (fun i => a i - a i₀)) atTop
      (nhds 0) :=
    squeeze_zero hF0 hFle hnum
  have hid : ∀ t : ℝ, tiltMean a t
      = tiltMean (fun i => a i - a i₀) t + a i₀ := by
    intro t
    rw [tiltMean_shift a (a i₀) t]
    exact (sub_add_cancel _ _).symm
  have hadd := hlim_b.add_const (a i₀)
  rw [zero_add] at hadd
  exact hadd.congr (fun t => (hid t).symm)

/-- As `t → -∞`, the tilt mean converges to the maximum of the
observable (by reflection to the `+∞` statement). -/
theorem tiltMean_tendsto_max {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (i₁ : ι) (hmax : ∀ i, a i ≤ a i₁) :
    Tendsto (tiltMean a) atBot (nhds (a i₁)) := by
  have hlim : Tendsto (tiltMean (fun i => a i₁ - a i)) atTop
      (nhds 0) := by
    have h := tiltMean_tendsto_min (fun i => a i₁ - a i) i₁
      (fun i => by
        show a i₁ - a i₁ ≤ a i₁ - a i
        rw [sub_self]
        exact sub_nonneg.mpr (hmax i))
    simpa using h
  have hid : ∀ t : ℝ, tiltMean a t
      = a i₁ - tiltMean (fun i => a i₁ - a i) (-t) := by
    intro t
    have h1 : (fun i => a i₁ - a i) = (fun i => -(a i - a i₁)) := by
      funext i
      ring
    rw [h1, tiltMean_neg, neg_neg, tiltMean_shift]
    ring
  have hcomp : Tendsto (fun t => tiltMean (fun i => a i₁ - a i) (-t))
      atBot (nhds 0) := hlim.comp tendsto_neg_atBot_atTop
  have hsub : Tendsto
      (fun t => a i₁ - tiltMean (fun i => a i₁ - a i) (-t))
      atBot (nhds (a i₁ - 0)) := tendsto_const_nhds.sub hcomp
  rw [sub_zero] at hsub
  exact hsub.congr (fun t => (hid t).symm)

/-- Every value strictly between the attained minimum and an
attained upper bound is hit by the tilt mean (continuity plus the
two limits, via the intermediate value theorem). -/
theorem tiltMean_surj_on {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (i₀ i₁ : ι) (hmin : ∀ i, a i₀ ≤ a i)
    (hmax : ∀ i, a i ≤ a i₁) {y : ℝ} (hy0 : a i₀ < y) (hy1 : y < a i₁) :
    ∃ t, tiltMean a t = y := by
  have hcont : Continuous (tiltMean a) := tiltMean_continuous a
  have hlimTop := tiltMean_tendsto_min a i₀ hmin
  have hlimBot := tiltMean_tendsto_max a i₁ hmax
  obtain ⟨T₂, hT₂0, hT₂⟩ : ∃ t, 0 ≤ t ∧ tiltMean a t < y := by
    have hev := hlimTop.eventually (Iio_mem_nhds hy0)
    obtain ⟨t, ht1, ht2⟩ := (hev.and (eventually_ge_atTop (0 : ℝ))).exists
    exact ⟨t, ht2, ht1⟩
  obtain ⟨T₁, hT₁0, hT₁⟩ : ∃ t, t ≤ 0 ∧ y < tiltMean a t := by
    have hev := hlimBot.eventually (Ioi_mem_nhds hy1)
    obtain ⟨t, ht1, ht2⟩ := (hev.and (eventually_le_atBot (0 : ℝ))).exists
    exact ⟨t, ht2, ht1⟩
  have hmem : y ∈ Set.Icc (tiltMean a T₂) (tiltMean a T₁) :=
    ⟨hT₂.le, hT₁.le⟩
  obtain ⟨t, -, ht⟩ := (intermediate_value_Icc' (le_trans hT₁0 hT₂0)
    hcont.continuousOn) hmem
  exact ⟨t, ht⟩

end TiltKit

/-! ## §7. Bridges: Gibbs expectations are tilt means

On both sides the Wilson action is the coupling times the number
of plaquettes times the mean plaquette density, so each Gibbs
expectation is the tilt mean of its own density observable: the
coarse side at tilt `6β′`, the fine side at tilt `12β`. The
constant configuration mass cancels in the ratio. -/

section NbBridge

theorem nb_configMeasure_singleton {Λ : Type*} [Fintype Λ]
    (V : Config Λ (DihedralGroup 4)) :
    (configMeasure nbμG) {V} = ∏ ℓ : Link Λ, nbμG {V ℓ} := by
  have h : ({V} : Set (Config Λ (DihedralGroup 4)))
      = Set.univ.pi (fun ℓ : Link Λ => {V ℓ}) := by
    ext W
    simp [Set.mem_pi, funext_iff]
  rw [configMeasure, h, Measure.pi_pi]

/-- Every coarse configuration has mass `1/4096`. -/
theorem nb_configMeasure_singleton_coarse
    (V : Config (Fin 1) (DihedralGroup 4)) :
    (configMeasure nbμG) {V} = (4096 : ℝ≥0∞)⁻¹ := by
  rw [nb_configMeasure_singleton]
  simp only [nbμG_singleton, Finset.prod_const, Finset.card_univ]
  show ((8 : ℝ≥0∞)⁻¹) ^ (Fintype.card (Fin 1 × Fin 4)) = (4096 : ℝ≥0∞)⁻¹
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [← ENNReal.inv_pow]
  norm_num

/-- Every fine configuration has mass `(1/8)⁸`. -/
theorem nb_configMeasure_singleton_fine
    (U : Config (Fin 2) (DihedralGroup 4)) :
    (configMeasure nbμG) {U} = (8 : ℝ≥0∞)⁻¹ ^ 8 := by
  rw [nb_configMeasure_singleton]
  simp only [nbμG_singleton, Finset.prod_const, Finset.card_univ]
  show ((8 : ℝ≥0∞)⁻¹) ^ (Fintype.card (Fin 2 × Fin 4)) = (8 : ℝ≥0∞)⁻¹ ^ 8
  simp [Fintype.card_prod]

/-- On these finite discrete configuration spaces every real
observable is integrable against the product measure. -/
theorem nb_integrable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (F : Config Λ (DihedralGroup 4) → ℝ) :
    Integrable F (configMeasure nbμG) :=
  Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable
    (∑ U, ‖F U‖)
    (ae_of_all _ fun U =>
      Finset.single_le_sum (fun U' _ => norm_nonneg _) (Finset.mem_univ U))

/-- The Wilson action is the coupling times the plaquette count
times the mean plaquette density. -/
theorem nb_wilson_eq {Λ : Type*} [Fintype Λ]
    (σ : Fin 4 → Equiv.Perm Λ)
    (hΛ : 0 < Fintype.card Λ) (β : ℝ) (U : Config Λ (DihedralGroup 4)) :
    wilsonAction σ nbRep β U
      = β * ((Fintype.card Λ : ℝ) * 6 * meanPlaqDensity σ nbRep U) := by
  have h1 : (0 : ℝ) < (Fintype.card Λ : ℝ) := by exact_mod_cast hΛ
  have hc : ((Fintype.card Λ : ℝ) * 6) ≠ 0 :=
    mul_ne_zero h1.ne' (by norm_num)
  unfold wilsonAction meanPlaqDensity
  field_simp

/-- The generic bridge: if the Wilson action is `β · (n · F)` and
every configuration has the same mass `c`, the Gibbs expectation
of `F` is the tilt mean of `F` at tilt `β · n`. -/
theorem gibbsExpectR_eq_tiltMean {Λ : Type*} [Fintype Λ]
    [DecidableEq Λ] (σ : Fin 4 → Equiv.Perm Λ)
    (F : Config Λ (DihedralGroup 4) → ℝ) (n : ℝ) (c : ℝ≥0∞) (β : ℝ)
    (hW : ∀ U, wilsonAction σ nbRep β U = β * (n * F U))
    (hc : ∀ U : Config Λ (DihedralGroup 4), (configMeasure nbμG) {U} = c)
    (hc0 : c.toReal ≠ 0) :
    gibbsExpectR σ nbμG nbRep β F = tiltMean F (β * n) := by
  have hcR : ∀ U : Config Λ (DihedralGroup 4),
      (configMeasure nbμG).real {U} = c.toReal := by
    intro U
    show ((configMeasure nbμG) {U}).toReal = c.toReal
    rw [hc U]
  have hnum : (∫ U, Real.exp (- wilsonAction σ nbRep β U) * F U
        ∂(configMeasure nbμG))
      = c.toReal * tiltNum F (β * n) := by
    rw [integral_fintype (nb_integrable
      (fun U => Real.exp (- wilsonAction σ nbRep β U) * F U))]
    unfold tiltNum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun U _ => ?_
    rw [hcR U, hW U]
    simp only [smul_eq_mul]
    ring_nf
  have hden : gibbsPartition σ nbμG nbRep β
      = c.toReal * tiltDen F (β * n) := by
    unfold gibbsPartition
    rw [integral_fintype (nb_integrable
      (fun U => Real.exp (- wilsonAction σ nbRep β U)))]
    unfold tiltDen
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun U _ => ?_
    rw [hcR U, hW U]
    simp only [smul_eq_mul]
    ring_nf
  unfold tiltMean
  rw [gibbsExpectR_eq_ratio σ nbμG nbRep nbRep_continuous (by norm_num)
    β F, hnum, hden, mul_div_mul_left _ _ hc0]

/-- The coarse Gibbs expectation is the coarse tilt mean at `6β′`. -/
theorem nb_coarse_bridge (β' : ℝ) :
    gibbsExpectR flowσ' nbμG nbRep β' nbCoarse
      = tiltMean nbCoarse (6 * β') := by
  have hW : ∀ V, wilsonAction flowσ' nbRep β' V
      = β' * (6 * nbCoarse V) := by
    intro V
    have h2 := nb_wilson_eq flowσ' (by norm_num) β' V
    have h3 : ((Fintype.card (Fin 1) : ℝ)) = 1 := by
      norm_num [Fintype.card_fin]
    rw [h3] at h2
    calc wilsonAction flowσ' nbRep β' V
        = β' * (1 * 6 * meanPlaqDensity flowσ' nbRep V) := h2
      _ = β' * (6 * nbCoarse V) := by
          congr 1
          show (1 : ℝ) * 6 * meanPlaqDensity flowσ' nbRep V
            = 6 * meanPlaqDensity flowσ' nbRep V
          ring
  have h := gibbsExpectR_eq_tiltMean flowσ' nbCoarse 6
    (4096 : ℝ≥0∞)⁻¹ β' hW (fun V => nb_configMeasure_singleton_coarse V)
    (ENNReal.toReal_pos (by simp) (by simp)).ne'
  rwa [show β' * (6 : ℝ) = 6 * β' by ring] at h

/-- The fine Gibbs expectation is the fine tilt mean at `12β`. -/
theorem nb_fine_bridge (β : ℝ) :
    gibbsExpectR flowσ nbμG nbRep β nbFine
      = tiltMean nbFine (12 * β) := by
  have hW : ∀ U, wilsonAction flowσ nbRep β U
      = β * (12 * nbFine U) := by
    intro U
    have h2 := nb_wilson_eq flowσ (by norm_num) β U
    have h3 : ((Fintype.card (Fin 2) : ℝ)) = 2 := by
      norm_num [Fintype.card_fin]
    rw [h3] at h2
    calc wilsonAction flowσ nbRep β U
        = β * (2 * 6 * meanPlaqDensity flowσ nbRep U) := h2
      _ = β * (12 * nbFine U) := by
          congr 1
          show (2 : ℝ) * 6 * meanPlaqDensity flowσ nbRep U
            = 12 * meanPlaqDensity flowσ nbRep U
          ring
  have h := gibbsExpectR_eq_tiltMean flowσ nbFine 12
    ((8 : ℝ≥0∞)⁻¹ ^ 8) β hW (fun U => nb_configMeasure_singleton_fine U)
    (ENNReal.toReal_pos (by simp) (by simp)).ne'
  rwa [show β * (12 : ℝ) = 12 * β by ring] at h

/-- The Haar intertwiner of the two-dimensional representation has
trace zero: invariance under the quarter-turn forces both diagonal
entries to vanish (`rot · P = P` gives `P 0 0 = -P 1 0 = -P 0 0`). -/
theorem nb_haar_trace :
    (Matrix.trace (haarIntertwiner nbμG nbRep)).re = 0 := by
  set P := haarIntertwiner nbμG nbRep with hP
  have key : nbRot * P = P := by
    have h := repMatrix_mul_haarIntertwiner nbμG nbRep nbRep_continuous
      (DihedralGroup.r 1)
    rwa [repMatrix_nbRep, nbRepMat_r_one] at h
  have vanish : ∀ z : ℂ, -z = z → z = 0 := by
    intro z hz
    have h3 : (2 : ℂ) * z = 0 := by
      calc (2 : ℂ) * z = z + z := by ring
        _ = z + -z := by rw [hz]
        _ = 0 := add_neg_cancel _
    exact (mul_eq_zero.mp h3).resolve_left (by norm_num)
  have e10 : P 1 0 = P 0 0 := by
    have h := congrFun (congrFun key 1) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, nbRot] at h
    have h2 : P 0 0 = P 1 0 := by simpa using h
    exact h2.symm
  have e00 : P 0 0 = 0 := by
    have h := congrFun (congrFun key 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, nbRot] at h
    rw [e10] at h
    have h2 : -P 0 0 = P 0 0 := by simpa using h
    exact vanish _ h2
  have e11 : P 1 1 = 0 := by
    have h := congrFun (congrFun key 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, nbRot] at h
    have h' := congrFun (congrFun key 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, nbRot] at h'
    have h1 : -P 1 1 = P 0 1 := by simpa using h
    have h2 : P 0 1 = P 1 1 := by simpa using h'
    rw [h2] at h1
    exact vanish _ h1
  rw [Matrix.trace_fin_two, e00, e11]
  simp

/-- The fine mean density at `β = 0` is exactly `1` (the β = 0
formula of `BlockingProjection` plus the vanishing intertwiner
trace). -/
theorem nb_fine_expect_zero :
    gibbsExpectR flowσ nbμG nbRep 0 nbFine = 1 := by
  have h := gibbsExpectR_zero_meanPlaqDensity flowσ nbμG nbRep
    nbRep_continuous (by norm_num [Fintype.card_fin])
    (fun x μ ν _ => by
      rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) x with rfl | rfl
      · exact ⟨by rw [flowσ_apply_zero]; decide,
          by rw [flowσ_apply_zero]; decide⟩
      · exact ⟨by rw [flowσ_apply_one]; decide,
          by rw [flowσ_apply_one]; decide⟩)
  rw [nb_haar_trace] at h
  norm_num at h
  exact h

/-- The coarse mean density at `β′ = 0` is the plain average of the
coarse density over all configurations: `3072 / 4096 = 3/4`. -/
theorem nb_coarse_expect_zero :
    gibbsExpectR flowσ' nbμG nbRep 0 nbCoarse = 3 / 4 := by
  rw [nb_coarse_bridge, mul_zero]
  unfold tiltMean tiltNum tiltDen
  rw [Finset.sum_congr rfl (g := fun V => nbCoarse V)
    (fun V _ => by simp), nb_sum_coarse_total]
  simp only [zero_mul, neg_zero, Real.exp_zero, Finset.sum_const,
    Finset.card_univ]
  rw [show Fintype.card (Config (Fin 1) (DihedralGroup 4)) = 4096 by
    norm_num [Fintype.card_pi, Finset.prod_const, Fintype.card_prod,
      DihedralGroup.card, Fintype.card_fin]]
  norm_num [nsmul_eq_mul]

end NbBridge

/-! ## §8. S4 at the nonabelian seat

Existence, uniqueness, and strict monotonicity of the
plaquette-matched projection, and the anchor in its exact
analogue: the value matched to `β = 0` is **negative**, the pair
`(0, 0)` does not match, and yet the blocked measure at `(0, 0)`
*is* the coarse Gibbs measure — the projection departs from the
measure truth already at the anchor. -/

section NbS4

theorem nbCoarse_nonconst :
    ¬ ∀ V W : Config (Fin 1) (DihedralGroup 4),
      nbCoarse V = nbCoarse W := by
  intro h
  have h1 := h (fun _ => 1) nbVW
  rw [nbCoarse_trivial, nbCoarse_nbVW] at h1
  norm_num at h1

theorem nbFine_nonconst :
    ¬ ∀ U U' : Config (Fin 2) (DihedralGroup 4),
      nbFine U = nbFine U' := by
  intro h
  have h1 := h (fun _ => 1) nbUW
  rw [nbFine_trivial] at h1
  have h2 := nbFine_witness_lower
  linarith

theorem nb_coarse_tilt_zero : tiltMean nbCoarse 0 = 3 / 4 := by
  have h := nb_coarse_bridge 0
  rw [mul_zero, nb_coarse_expect_zero] at h
  exact h.symm

theorem nb_fine_tilt_zero : tiltMean nbFine 0 = 1 := by
  have h := nb_fine_bridge 0
  rw [mul_zero, nb_fine_expect_zero] at h
  exact h.symm

/-- Matching at this seat, restated through the bridges. -/
theorem nb_plaquetteMatched_iff (β β' : ℝ) :
    PlaquetteMatched flowσ flowσ' nbμG nbRep flowBlocking β β'
      ↔ tiltMean nbCoarse (6 * β')
        = gibbsExpectR flowσ nbμG nbRep β nbFine := by
  show (gibbsExpectR flowσ nbμG nbRep β nbFine
      = gibbsExpectR flowσ' nbμG nbRep β' nbCoarse) ↔ _
  rw [nb_coarse_bridge]
  exact eq_comm

/-- For `β ≥ 0` the fine mean density lies in `(0, 1]`. -/
theorem nb_fine_range {β : ℝ} (hβ : 0 ≤ β) :
    gibbsExpectR flowσ nbμG nbRep β nbFine ∈ Set.Ioc 0 1 := by
  rw [nb_fine_bridge]
  constructor
  · apply tiltMean_gt nbFine 0 (12 * β)
    · intro U
      simpa using nbFine_nonneg U
    · refine ⟨nbUW, ?_⟩
      simpa using (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 12)
        nbFine_witness_lower)
  · rcases eq_or_lt_of_le hβ with h0 | hpos
    · subst h0
      rw [mul_zero, nb_fine_tilt_zero]
    · have hlt : tiltMean nbFine (12 * β) < tiltMean nbFine 0 :=
        tiltMean_strictAnti nbFine nbFine_nonconst
          (mul_pos (by norm_num) hpos)
      rw [nb_fine_tilt_zero] at hlt
      exact hlt.le

/-- **S4 at the nonabelian seat: existence and uniqueness of the
plaquette-matched projection.** For every `β ≥ 0` there is a
unique `β′` whose coarse Gibbs mean plaquette density equals the
fine (blocked-side) mean plaquette density at `β`. -/
theorem nb_matched_exists_unique {β : ℝ} (hβ : 0 ≤ β) :
    ∃! β' : ℝ, PlaquetteMatched flowσ flowσ' nbμG nbRep
      flowBlocking β β' := by
  obtain ⟨hf0, hf1⟩ := nb_fine_range hβ
  obtain ⟨Vmax, -, hVmax⟩ := Finset.exists_max_image Finset.univ
    nbCoarse ⟨(fun _ => 1), Finset.mem_univ _⟩
  have hVmax' : ∀ V, nbCoarse V ≤ nbCoarse Vmax :=
    fun V => hVmax V (Finset.mem_univ V)
  have hmax53 : (5 : ℝ) / 3 ≤ nbCoarse Vmax :=
    le_trans (le_of_eq nbCoarse_nbVM.symm) (hVmax' nbVM)
  set y := gibbsExpectR flowσ nbμG nbRep β nbFine with hy
  obtain ⟨t, ht⟩ := tiltMean_surj_on nbCoarse (fun _ => 1) Vmax
    (fun V => by rw [nbCoarse_trivial]; exact nbCoarse_nonneg V)
    hVmax'
    (by rw [nbCoarse_trivial]; exact hf0)
    (by linarith)
  refine ⟨t / 6, ?_, ?_⟩
  · show PlaquetteMatched flowσ flowσ' nbμG nbRep flowBlocking β
      (t / 6)
    rw [nb_plaquetteMatched_iff,
      show (6 : ℝ) * (t / 6) = t by field_simp]
    exact ht
  · intro β'' hβ''
    rw [nb_plaquetteMatched_iff] at hβ''
    have hinj := (tiltMean_strictAnti nbCoarse
      nbCoarse_nonconst).injective (hβ''.trans ht.symm)
    have hfin : β'' = t / 6 := by
      rw [← hinj]
      field_simp
    exact hfin

/-- **S4 monotonicity.** The matched value is strictly increasing
in `β`: matched pairs at `β₁ < β₂` satisfy `β₁′ < β₂′`. -/
theorem nb_matched_strict_mono {β₁ β₂ β₁' β₂' : ℝ}
    (h2 : β₁ < β₂)
    (hm1 : PlaquetteMatched flowσ flowσ' nbμG nbRep flowBlocking
      β₁ β₁')
    (hm2 : PlaquetteMatched flowσ flowσ' nbμG nbRep flowBlocking
      β₂ β₂') :
    β₁' < β₂' := by
  rw [nb_plaquetteMatched_iff, nb_fine_bridge] at hm1 hm2
  by_contra hcon
  push_neg at hcon
  have hle : tiltMean nbCoarse (6 * β₁')
      ≤ tiltMean nbCoarse (6 * β₂') := by
    rcases eq_or_lt_of_le hcon with he | hl
    · rw [he]
    · exact (tiltMean_strictAnti nbCoarse nbCoarse_nonconst
        (by linarith : 6 * β₂' < 6 * β₁')).le
  have hflt : tiltMean nbFine (12 * β₂) < tiltMean nbFine (12 * β₁) :=
    tiltMean_strictAnti nbFine nbFine_nonconst (by linarith)
  linarith

/-- The anchor, negative: the pair `(0, 0)` does **not** match at
this seat — the fine side at `0` is `1`, the coarse side at `0`
is `3/4`. -/
theorem nb_not_matched_zero_zero :
    ¬ PlaquetteMatched flowσ flowσ' nbμG nbRep flowBlocking 0 0 := by
  rw [nb_plaquetteMatched_iff, nb_fine_expect_zero, mul_zero,
    nb_coarse_tilt_zero]
  norm_num

/-- Every value matched to `β = 0` at this seat is negative. -/
theorem nb_anchor_neg {β' : ℝ}
    (hβ' : PlaquetteMatched flowσ flowσ' nbμG nbRep flowBlocking
      0 β') :
    β' < 0 := by
  rw [nb_plaquetteMatched_iff, nb_fine_expect_zero] at hβ'
  by_contra hcon
  push_neg at hcon
  rcases eq_or_lt_of_le hcon with he | hpos
  · rw [← he, mul_zero, nb_coarse_tilt_zero] at hβ'
    norm_num at hβ'
  · have hlt : tiltMean nbCoarse (6 * β') < tiltMean nbCoarse 0 :=
      tiltMean_strictAnti nbCoarse nbCoarse_nonconst
        (mul_pos (by norm_num) hpos)
    rw [nb_coarse_tilt_zero] at hlt
    linarith

/-- The hygiene contrast at the anchor: at `(0, 0)` the blocked
measure **is** the coarse Gibbs measure (the general Stage-2
theorem at zero coupling), even though the plaquette projection
does not match there. Matching one observable is not matching
the measure. -/
theorem nb_anchor_blocked :
    BlockedGibbsIsCoarseGibbs flowσ flowσ' nbμG nbRep flowBlocking
      0 0 :=
  blockedGibbsIsCoarseGibbs_zero flowσ flowσ' nbμG nbRep flowBlocking

end NbS4

end ThetLogos
