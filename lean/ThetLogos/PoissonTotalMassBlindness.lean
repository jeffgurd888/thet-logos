import Mathlib.Tactic
import ThetLogos.ThermalChargePoisson

/-!
# ThetLogos.PoissonTotalMassBlindness — SHADOW-TEST-1: the total-mass-blindness decision (T1)

HONESTY LEDGER (read before citing):

- **Working label only.** SHADOW-TEST-1 and this module name are
  working labels from the shadow scoping dossier
  (`~/workspace/your_files/dial2-shadow-scoping-2026-11-04.md`, §4);
  Jeff names.
- **What this is.** A **fence theorem about the shadow**, in the
  dependence-tracking dialect of GR-POSE-1 (`GravityPoseDecision`).
  The gravity-object audit (2026-11-04) found, and T2
  (`ThermalChargePoisson`) landed, that on a closed finite seat the
  Poisson inversion sees only a **mean-subtracted mass contrast**:
  a potential exists iff `∑ i, g i = 0`, and the field `dropVec f`
  is unique although `f` is unique only up to constants. This
  module promotes that contour (CT-1 of the shadow scoping) from
  dossier prose to a **class theorem**: *every* quantity factoring
  through T2's output — the canonical field `poissonField`, the
  canonical Ohm flow `poissonFlow`, or equivalently the
  mean-subtracted source `meanSub g` itself — is **invariant under
  constant shifts of the source** `g ↦ g + c`. No such quantity can
  detect total mass; a fortiori none can carry the isolated-mass
  signature (SH-7 + SH-9 at Newtonian scope) that a gravitational
  reading would need.
- **Pre-registered dispositions (shadow scoping §4, honored).**
  This brick is **Dial-INELIGIBLE**: Dial 2 stays 0 under every
  outcome, including this one. It seats no gravity object, defines
  no response law, and names nothing gravitational. Its
  consequences are exactly: **route SR-4 (Poisson
  post-processing — anything built from T2's output alone) is
  closed at T1**, and **route SR-5's ceiling is kernel-fenced**
  (the thermal-source composite, whatever source it feeds T2, is
  still seen by T2 only as a contrast). It also pays T2 a dividend:
  this is the precise statement of what T2's output contains.
- **The class, pinned honestly.** A "quantity factoring through
  T2's output" is formalized in the only two dialects the landed
  API supports: (i) `F (poissonField w … g)` / `F (poissonFlow w …
  g)` for an *arbitrary* function `F` of the field/flow data — the
  canonical field is well-defined because T2 proves `dropVec`
  (hence `flowVec`) is the same for every potential; (ii)
  `F (meanSub g)` for an arbitrary `F` of the mean-subtracted
  source, which determines the field by T2 existence +
  uniqueness. The potential `φ` itself is *not* in the class: it
  is not unique, so a bare function of a chosen `φ` is not a
  quantity of the seat at all. No wider class is claimed — a
  construction that also reads the graph, the weights, or the
  unprojected source does not factor through T2's output, and the
  scoping names that leak precisely: it would be
  source-dependent geometry, i.e. SR-6's pin, not a member of
  this class. The invariance for the registered class LANDS
  (below), so no leak exists inside it.
- **The sharpest single corollary.** A *uniform* source — pure
  total mass, zero contrast — produces **no field at all**
  (`poissonField_const`): `poissonField w … (fun _ => c) = 0`.
- Everything here is T1 finite linear algebra on the
  `BridgeLaplacian` seat, consuming T2 at its landed shapes. Zero
  sorrys, no `native_decide`, headline axioms exactly the standard
  three (`propext`, `Classical.choice`, `Quot.sound`).
- SEP FENCES, STANDING. No operator separates charge by its own
  action; no charge operator and no electromagnetic field object
  is claimed at this seat; β appears nowhere. Determination, not
  self-organization. Finite graph statics only. **NO CLAIM;
  dials 0/4. Dial 2 = 0.**
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. The mean and the mean-subtraction projection -/

/-- The **mean** of a source: its total divided by the number of
sites. (On the empty seat this is `0 / 0 = 0` by the field
convention; every statement below is proved for all finite `V`,
the empty case being discharged inside the proofs.) -/
noncomputable def meanVal (g : V → ℝ) : ℝ :=
  (∑ i, g i) / (Fintype.card V : ℝ)

/-- The **mean-subtracted source** `ρ − ρ̄`: `g` minus its own
constant mean. This is the projection onto T2's compatibility
class — by T2's existence and uniqueness, the exact data T2's
output is a function of. -/
noncomputable def meanSub (g : V → ℝ) : V → ℝ := fun i => g i - meanVal g

omit [DecidableEq V] in
/-- The mean of a constant function is that constant (on a
nonempty seat, expressed as `card ≠ 0`). -/
theorem meanVal_const (c : ℝ) (hcard : (Fintype.card V : ℝ) ≠ 0) :
    meanVal (fun _ : V => c) = c := by
  have hsum : (∑ _i : V, c) = (Fintype.card V : ℝ) * c := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [meanVal, hsum, div_eq_iff hcard]
  ring

omit [DecidableEq V] in
/-- The mean shifts with a constant shift of the source. -/
theorem meanVal_add_const (g : V → ℝ) (c : ℝ)
    (hcard : (Fintype.card V : ℝ) ≠ 0) :
    meanVal (fun i => g i + c) = meanVal g + c := by
  have hsum : (∑ i, (g i + c))
      = (∑ i, g i) + (Fintype.card V : ℝ) * c := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  have hdiv : ((Fintype.card V : ℝ) * c) / (Fintype.card V : ℝ) = c :=
    (div_eq_iff hcard).mpr (by ring)
  simp only [meanVal, hsum, add_div, hdiv]

omit [DecidableEq V] in
/-- **The projection lands in the compatibility class.** The
mean-subtracted source always has total zero — it is always a
legitimate T2 input. -/
theorem sum_meanSub_eq_zero (g : V → ℝ) : ∑ i, meanSub g i = 0 := by
  rcases isEmpty_or_nonempty V with hE | hNE
  · have := hE
    simp [Finset.univ_eq_empty]
  · have := hNE
    have hcard : (Fintype.card V : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := V)).ne'
    have hsum : ∑ i, meanSub g i
        = (∑ i, g i) - (Fintype.card V : ℝ) * meanVal g := by
      simp only [meanSub, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    rw [hsum, meanVal]
    have hmul : (Fintype.card V : ℝ) * ((∑ i, g i) / (Fintype.card V : ℝ))
        = ∑ i, g i := by
      field_simp
    rw [hmul, sub_self]

omit [DecidableEq V] in
/-- The projection fixes the sources already in its range: a
mean-zero source is its own mean-subtraction. -/
theorem meanSub_of_sum_eq_zero (g : V → ℝ) (hg : ∑ i, g i = 0) :
    meanSub g = g := by
  funext i
  simp only [meanSub, meanVal, hg, zero_div, sub_zero]

omit [DecidableEq V] in
/-- **The invariance of the projection.** A constant shift of the
source is exactly a change of total mass at fixed contrast — and
the projection does not see it: `meanSub (g + c) = meanSub g`.
This one line is the engine of every blindness statement below. -/
theorem meanSub_add_const (g : V → ℝ) (c : ℝ) :
    meanSub (fun i => g i + c) = meanSub g := by
  rcases isEmpty_or_nonempty V with hE | hNE
  · funext i
    exact (hE.false i).elim
  · have := hNE
    have hcard : (Fintype.card V : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := V)).ne'
    funext i
    simp only [meanSub, meanVal_add_const g c hcard]
    ring

omit [DecidableEq V] in
/-- A constant source — pure total mass, zero contrast — projects
to zero. -/
theorem meanSub_const [Nonempty V] (c : ℝ) :
    meanSub (fun _ : V => c) = 0 := by
  have hcard : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := V)).ne'
  funext i
  simp only [meanSub, meanVal_const c hcard, Pi.zero_apply, sub_self]

omit [DecidableEq V] in
/-- The projection is idempotent: projecting a projection changes
nothing. -/
theorem meanSub_meanSub (g : V → ℝ) : meanSub (meanSub g) = meanSub g :=
  meanSub_of_sum_eq_zero (meanSub g) (sum_meanSub_eq_zero g)

omit [DecidableEq V] in
/-- **Characterization of the fibers.** Two sources have the same
mean-subtraction iff they differ by a constant — i.e. iff they
have the same contrast and possibly different totals. The fibers
of the projection are exactly the total-mass directions. -/
theorem meanSub_eq_iff (g g' : V → ℝ) :
    meanSub g = meanSub g' ↔
      ∃ c : ℝ, g' = fun i => g i + c := by
  constructor
  · intro h
    refine ⟨meanVal g' - meanVal g, funext fun i => ?_⟩
    have hi := congrFun h i
    simp only [meanSub] at hi
    show g' i = g i + (meanVal g' - meanVal g)
    linarith
  · rintro ⟨c, rfl⟩
    exact (meanSub_add_const g c).symm

/-! ## §2. T2's canonical output: the field and flow of a source -/

/-- **A canonical potential for a source**: a chosen potential for
its mean-subtraction, by T2 existence (`meanSub g` is always
mean-zero, §1). The choice is immaterial for everything below:
T2's uniqueness makes the induced field and flow independent of
it (§3). -/
noncomputable def poissonPotential (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (g : V → ℝ) : V → ℝ :=
  Classical.choose
    (exists_potential_of_sum_eq_zero w hw hw0 hpos (meanSub g)
      (sum_meanSub_eq_zero g))

/-- The canonical potential solves the Poisson problem for the
mean-subtracted source. -/
theorem laplacianOp_poissonPotential (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (g : V → ℝ) :
    laplacianOp w (poissonPotential w hw hw0 hpos g) = meanSub g :=
  Classical.choose_spec
    (exists_potential_of_sum_eq_zero w hw hw0 hpos (meanSub g)
      (sum_meanSub_eq_zero g))

/-- **The canonical field of a source**: the edge drop `dφ` of a
potential for its mean-subtraction. Well-defined as *the* field
of `g` because T2 proves every potential for the same source has
the same drop. -/
noncomputable def poissonField (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (g : V → ℝ) : V → V → ℝ :=
  dropVec (poissonPotential w hw hw0 hpos g)

/-- **The canonical Ohm flow of a source**: the current field of a
potential for its mean-subtraction; likewise well-defined by T2. -/
noncomputable def poissonFlow (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (g : V → ℝ) : V → V → ℝ :=
  flowVec w (poissonPotential w hw hw0 hpos g)

/-! ## §3. Dependence: the output factors through the projection -/

/-- **The field depends only on the mean-subtracted source.** Two
sources with the same contrast have the same field — the field is
a function of `meanSub g`, not of `g`. -/
theorem poissonField_eq_of_meanSub_eq (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (g g' : V → ℝ)
    (h : meanSub g = meanSub g') :
    poissonField w hw hw0 hpos g = poissonField w hw hw0 hpos g' := by
  unfold poissonField
  apply dropVec_eq_of_laplacianOp_eq w hw hw0 hpos
  rw [laplacianOp_poissonPotential, laplacianOp_poissonPotential]
  exact h.symm

/-- **The flow depends only on the mean-subtracted source.** -/
theorem poissonFlow_eq_of_meanSub_eq (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (g g' : V → ℝ)
    (h : meanSub g = meanSub g') :
    poissonFlow w hw hw0 hpos g = poissonFlow w hw hw0 hpos g' := by
  unfold poissonFlow
  apply flowVec_eq_of_laplacianOp_eq w hw hw0 hpos
  rw [laplacianOp_poissonPotential, laplacianOp_poissonPotential]
  exact h.symm

/-- **The field is blind to constant source shifts.** Adding a
constant `c` to the source — changing the total mass at fixed
contrast — does not change the field. -/
theorem poissonField_add_const (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (g : V → ℝ) (c : ℝ) :
    poissonField w hw hw0 hpos (fun i => g i + c)
      = poissonField w hw hw0 hpos g :=
  poissonField_eq_of_meanSub_eq w hw hw0 hpos _ _ (meanSub_add_const g c)

/-! ## §4. The decision: no quantity of the class detects total mass -/

/-- **Class theorem, field dialect (SHADOW-TEST-1).** For an
*arbitrary* quantity `F` of the field data, `F` of the field of
`g + c` equals `F` of the field of `g`, for every source `g` and
every shift `c`. Every construction factoring through T2's field
output is invariant under constant source shifts. -/
theorem fieldFactor_add_const {α : Type*} (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j)
    (F : (V → V → ℝ) → α) (g : V → ℝ) (c : ℝ) :
    F (poissonField w hw hw0 hpos (fun i => g i + c))
      = F (poissonField w hw hw0 hpos g) := by
  rw [poissonField_add_const]

/-- **Class theorem, flow dialect.** The same invariance for an
arbitrary quantity of the Ohm-flow data. -/
theorem flowFactor_add_const {α : Type*} (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j)
    (F : (V → V → ℝ) → α) (g : V → ℝ) (c : ℝ) :
    F (poissonFlow w hw hw0 hpos (fun i => g i + c))
      = F (poissonFlow w hw hw0 hpos g) := by
  rw [poissonFlow_eq_of_meanSub_eq w hw hw0 hpos _ _ (meanSub_add_const g c)]

omit [DecidableEq V] in
/-- **Class theorem, projection dialect.** The same invariance for
an arbitrary quantity of the mean-subtracted source — the
equivalent form of the class, since the field is a function of
the projection (§3). -/
theorem meanSubFactor_add_const {α : Type*} (F : (V → ℝ) → α)
    (g : V → ℝ) (c : ℝ) :
    F (meanSub (fun i => g i + c)) = F (meanSub g) := by
  rw [meanSub_add_const]

/-- **A uniform source produces no field.** Pure total mass with
zero contrast is invisible to the seat in the strongest sense:
its canonical field is identically zero. -/
theorem poissonField_const [Nonempty V] (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (c : ℝ) :
    poissonField w hw hw0 hpos (fun _ : V => c) = 0 := by
  have hL : laplacianOp w (poissonPotential w hw hw0 hpos (fun _ : V => c))
      = 0 := by
    rw [laplacianOp_poissonPotential, meanSub_const]
  have h0 : laplacianOp w (0 : V → ℝ) = 0 := by
    funext i
    simp [laplacianOp]
  have hdrop := (dropVec_eq_of_laplacianOp_eq w hw hw0 hpos
    (poissonPotential w hw hw0 hpos (fun _ : V => c)) 0
    (by rw [hL, h0])).symm
  unfold poissonField
  rw [hdrop]
  funext i j
  simp [dropVec_apply]

/-- **The decision, field dialect.** There is no quantity of the
field data, no source, and no nonzero constant shift at which the
quantity responds to the shift: *detecting total mass* — the
response an isolated-mass signature (SH-7 + SH-9) would require —
is impossible inside the class. **SR-4 is closed at T1; SR-5's
ceiling is fenced.** Pre-registered Dial-ineligible: Dial 2 = 0. -/
theorem not_exists_fieldFactor_detects_totalMass (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) :
    ¬ ∃ (F : (V → V → ℝ) → ℝ) (g : V → ℝ) (c : ℝ), c ≠ 0 ∧
      F (poissonField w hw hw0 hpos (fun i => g i + c))
        ≠ F (poissonField w hw hw0 hpos g) := by
  rintro ⟨F, g, c, -, hne⟩
  exact hne (fieldFactor_add_const w hw hw0 hpos F g c)

omit [DecidableEq V] in
/-- **The decision, projection dialect.** The same impossibility
stated at the projection: no quantity of the mean-subtracted
source responds to a constant shift of the source. -/
theorem not_exists_meanSubFactor_detects_totalMass :
    ¬ ∃ (F : (V → ℝ) → ℝ) (g : V → ℝ) (c : ℝ), c ≠ 0 ∧
      F (meanSub (fun i => g i + c)) ≠ F (meanSub g) := by
  rintro ⟨F, g, c, -, hne⟩
  exact hne (meanSubFactor_add_const F g c)

end ThetLogos
