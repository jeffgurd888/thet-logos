import Mathlib.Tactic
import ThetLogos.PoissonTotalMassBlindness

/-!
# ThetLogos.GreenOperator — the well-posed inverse of the seat Laplacian (T1)

HONESTY LEDGER (read before citing):

- **Working label only.** "Green operator" and this module name are
  working labels from the scoping note
  (`~/workspace/your_files/green-operator-scoping-2026-11-04.md`);
  Jeff names.
- **What this is.** T2 (`ThermalChargePoisson`) landed the discrete
  Poisson problem on the `BridgeLaplacian` seat in its honest,
  ill-posed form: a potential for `g` exists iff `∑ i, g i = 0`, and
  is then unique only up to an additive constant — T2's canonical
  potential (`poissonPotential`, SHADOW-TEST-1) still carries
  whatever constant `Classical.choose` handed back. This module
  forms the **well-posed object**: the inverse of the Laplacian
  restricted to the mean-zero subspace `LinearMap.ker chargeSum`,
  packaged as a linear equivalence (`lapEquiv`), and the induced
  operator on all sources (`greenOp`), where the source is first
  projected by `meanSub` and the potential is required to be
  mean-zero itself. Existence (headline 1), the zero-mean gauge
  (headline 3), and uniqueness on the subspace (headline 2) are
  theorems, so "well-posed" here is a proved word: `greenOp … g`
  is the *unique* mean-zero potential for `meanSub g`
  (`eq_greenOp_of`).
- **The fence, on the face (scoping §0, verbatim in spirit).** This
  object is **the shared inversion made well-posed** — nothing
  more. The corpus's one Laplacian inversion serves the heat,
  entropy, charge, and potential readings alike; packaging its
  inverse does not promote any one reading. **K-SR-4 stands over
  it:** SHADOW-TEST-1 proved the inversion factors through the
  mean-subtracted source and is therefore **blind to total mass** —
  and `greenOp` inherits this exactly, stated here at the operator
  itself (`greenOp_const`, `greenOp_meanSub`, and the kernel
  characterization `greenOp_eq_zero_iff`: the sources `greenOp`
  kills are precisely the constants, the pure-total-mass
  direction). **Pre-registered Dial-INELIGIBLE:** this brick moves
  no dial under any outcome; it states no response law — nothing
  falls, nothing is attracted, no geometry responds. It is a
  bookkeeping / well-posedness brick, the same family and ceiling
  as SR-5 (`ThermalSourceComposite`). **NO CLAIM; dials 0/4.**
- **Hypotheses on the face, never hidden.** Everything sits at
  T2's standing generality: a finite vertex type `V`, a symmetric
  weight function `w` (`hw`), nonnegative (`hw0`), with every
  off-diagonal weight strictly positive (`hpos`) — `hpos` *is* the
  connectedness of the weighted graph at this seat (a zero-weight
  edge severs the seat and manufactures a second zero mode; the
  bare kernel claim without it is false, cf. the DuctGap record).
  The brick is stated at `[Nonempty V]` throughout: the empty
  seat's inverse is the zero map by inspection, and T2's own
  injectivity (`lapRestrict_injective`) already carries the same
  hypothesis. No headline drops `hw0` or `hpos`.
- **What is new and what is packaging, honestly.** Every hard fact
  is landed: existence (T2 §5), injectivity of the restriction
  (T2 §4 — the fact kernel ∩ mean-zero = {0}), the `meanSub`
  projection API (SHADOW-TEST-1 §1). The genuinely new proof work
  is small: the linearity of `meanSub` (§1, not previously landed),
  that `L` does not see the mean-subtraction of its argument
  (§1), and the packaging itself. A Green's-function kernel
  `G i j`, positivity, and norm bounds are NOT in this brick.
- Everything is T1 finite linear algebra on the `BridgeLaplacian`
  seat. Zero sorrys, no `native_decide`, headline axioms exactly
  the standard three (`propext`, `Classical.choice`, `Quot.sound`).
  Finite statics only. **NO CLAIM; dials 0/4.**
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. Support: the linearity of `meanSub` (new), and `L` ignores
the mean-subtraction of its argument -/

omit [DecidableEq V] in
/-- The mean-subtraction projection is additive. (Not previously
landed: SHADOW-TEST-1's §1 API has shift-invariance and
idempotence, but not linearity.) -/
theorem meanSub_add (g h : V → ℝ) : meanSub (g + h) = meanSub g + meanSub h := by
  have hmean : meanVal (g + h) = meanVal g + meanVal h := by
    simp only [meanVal, Pi.add_apply, Finset.sum_add_distrib, add_div]
  funext i
  simp only [meanSub, hmean, Pi.add_apply]
  ring

omit [DecidableEq V] in
/-- The mean-subtraction projection is homogeneous. -/
theorem meanSub_smul (c : ℝ) (g : V → ℝ) : meanSub (c • g) = c • meanSub g := by
  have hmean : meanVal (c • g) = c * meanVal g := by
    simp only [meanVal, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      mul_div_assoc]
  funext i
  simp only [meanSub, hmean, Pi.smul_apply, smul_eq_mul]
  ring

/-- `L` does not see the mean-subtraction of its argument:
subtracting the mean subtracts a constant, and constants are in
the kernel of `L` (`laplacianOp_const`). -/
theorem laplacianOp_meanSub (w : V → V → ℝ) (F : V → ℝ) :
    laplacianOp w (meanSub F) = laplacianOp w F := by
  have hfun : meanSub F = F - (fun _ => meanVal F) := by
    funext i
    simp only [meanSub, Pi.sub_apply]
  rw [hfun, laplacianOp_sub, laplacianOp_const, sub_zero]

section GreenOp

variable [Nonempty V]

/-! ## §2. The restriction as a linear equivalence -/

/-- **The well-posed core.** The Laplacian restricted to the
mean-zero subspace is a **linear equivalence** of that subspace:
T2 §4's injectivity (`lapRestrict_injective`) plus
finite-dimensionality gives surjectivity by the exact idiom
T2 §5 already used, and `LinearEquiv.ofBijective` packages the
pair as an invertible map. This is the nested space of the
scoping note: the mean-zero subspace inside the seat's function
space, on which the ill-posed problem becomes well-posed. -/
noncomputable def lapEquiv (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) :
    (LinearMap.ker (chargeSum : (V → ℝ) →ₗ[ℝ] ℝ)) ≃ₗ[ℝ]
      (LinearMap.ker (chargeSum : (V → ℝ) →ₗ[ℝ] ℝ)) :=
  LinearEquiv.ofBijective (lapRestrict w hw)
    ⟨lapRestrict_injective w hw hw0 hpos,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
        (lapRestrict_injective w hw hw0 hpos)⟩

/-- The equivalence applies as the Laplacian (coercion form of
T2's `lapRestrict_coe`). -/
theorem lapEquiv_apply (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (F : LinearMap.ker chargeSum) :
    (lapEquiv w hw hw0 hpos F : V → ℝ) = laplacianOp w (F : V → ℝ) := by
  show (lapRestrict w hw F : V → ℝ) = laplacianOp w (F : V → ℝ)
  exact lapRestrict_coe w hw F

/-- The inverse equivalence undoes the Laplacian on the subspace:
the Laplacian of the inverse image of a mean-zero element is the
element itself. -/
theorem lapEquiv_symm_apply (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (G : LinearMap.ker chargeSum) :
    laplacianOp w ((lapEquiv w hw hw0 hpos).symm G : V → ℝ) = (G : V → ℝ) := by
  have h := congrArg Subtype.val
    (LinearEquiv.apply_symm_apply (lapEquiv w hw hw0 hpos) G)
  rwa [lapEquiv_apply] at h

/-! ## §3. The Green operator on all sources -/

/-- **The Green operator.** The gauged inverse of the seat
Laplacian, on an arbitrary source `g`: project the source by
`meanSub` (landing in T2's compatibility class), invert the
restriction by `lapEquiv.symm`, and read the result back as a
plain function — which is therefore mean-zero by construction.
This is the well-posed form of T2's problem: where
`poissonPotential` returns *a* potential, carrying an arbitrary
constant, `greenOp` returns *the* potential in the zero-mean
gauge. -/
noncomputable def greenOp (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (g : V → ℝ) : V → ℝ :=
  ((lapEquiv w hw hw0 hpos).symm
    ⟨meanSub g, by
      rw [mem_ker_chargeSum_iff]; exact sum_meanSub_eq_zero g⟩ : V → ℝ)

/-- **Headline 1 — the right-inverse law, in projected form.**
`L (greenOp g) = meanSub g`: the Green operator solves the
Poisson problem for the mean-subtracted source. The unprojected
form `= g` is false whenever `∑ g ≠ 0` (T2's compatibility
obstruction) and is not stated. -/
theorem laplacianOp_greenOp (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (g : V → ℝ) :
    laplacianOp w (greenOp w hw hw0 hpos g) = meanSub g :=
  lapEquiv_symm_apply w hw hw0 hpos _

/-- **Headline 3 — the gauge.** The Green potential is itself
mean-zero: `greenOp`'s value *is* an element of the mean-zero
subspace. Existence (headline 1) + this gauge + uniqueness on the
subspace (headline 2) are the three clauses of well-posedness. -/
theorem sum_greenOp (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (g : V → ℝ) :
    ∑ i, greenOp w hw hw0 hpos g i = 0 := by
  have h2 : greenOp w hw hw0 hpos g ∈ LinearMap.ker chargeSum :=
    ((lapEquiv w hw hw0 hpos).symm
      ⟨meanSub g, by
        rw [mem_ker_chargeSum_iff]; exact sum_meanSub_eq_zero g⟩).2
  rwa [mem_ker_chargeSum_iff] at h2

/-- **The uniqueness characterization.** A mean-zero function
whose Laplacian is the projected source *is* the Green
potential: `greenOp … g` is the unique mean-zero potential for
`meanSub g`. (Uniqueness is injectivity of the restriction —
T2 §4 — read through the equivalence.) -/
theorem eq_greenOp_of (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (g u : V → ℝ)
    (hu : ∑ i, u i = 0) (hLu : laplacianOp w u = meanSub g) :
    u = greenOp w hw hw0 hpos g := by
  have hmem : u ∈ LinearMap.ker chargeSum := by
    rw [mem_ker_chargeSum_iff]; exact hu
  have hGmem : meanSub g ∈ LinearMap.ker chargeSum := by
    rw [mem_ker_chargeSum_iff]; exact sum_meanSub_eq_zero g
  have hEq : lapEquiv w hw hw0 hpos ⟨u, hmem⟩ = ⟨meanSub g, hGmem⟩ := by
    apply Subtype.ext
    rw [lapEquiv_apply]
    exact hLu
  have hU : (⟨u, hmem⟩ : LinearMap.ker chargeSum)
      = (lapEquiv w hw hw0 hpos).symm ⟨meanSub g, hGmem⟩ := by
    rw [← hEq]
    exact (LinearEquiv.symm_apply_apply _ _).symm
  exact congrArg Subtype.val hU

/-- **Headline 2 — the left-inverse law on the subspace.** For a
mean-zero `f`, inverting its Laplacian returns `f` itself: on the
mean-zero subspace, `greenOp ∘ L = id`. -/
theorem greenOp_laplacianOp (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (f : V → ℝ)
    (hf : ∑ i, f i = 0) :
    greenOp w hw hw0 hpos (laplacianOp w f) = f :=
  (eq_greenOp_of w hw hw0 hpos (laplacianOp w f) f hf
    (meanSub_of_sum_eq_zero (laplacianOp w f)
      (sum_laplacianOp_eq_zero w hw f)).symm).symm

/-- The left-inverse law off the subspace: for arbitrary `f`,
inverting its Laplacian returns the mean-subtraction of `f` —
the gauge discards exactly the constant part. -/
theorem greenOp_laplacianOp_meanSub (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (f : V → ℝ) :
    greenOp w hw hw0 hpos (laplacianOp w f) = meanSub f := by
  apply (eq_greenOp_of w hw hw0 hpos (laplacianOp w f) (meanSub f)
    (sum_meanSub_eq_zero f) _).symm
  rw [laplacianOp_meanSub, meanSub_of_sum_eq_zero _
    (sum_laplacianOp_eq_zero w hw f)]

/-! ## §4. Linearity, the ceiling at the operator, and agreement
with the landed canonical potential -/

/-- **Headline 4a.** `greenOp` is additive in the source. (Via the
uniqueness characterization: the sum of the two Green potentials
is mean-zero and has the right Laplacian, using §1's
`meanSub_add` — the one genuinely new proof ingredient.) -/
theorem greenOp_add (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (g h : V → ℝ) :
    greenOp w hw hw0 hpos (g + h)
      = greenOp w hw hw0 hpos g + greenOp w hw hw0 hpos h := by
  apply (eq_greenOp_of w hw hw0 hpos (g + h)
    (greenOp w hw hw0 hpos g + greenOp w hw hw0 hpos h) _ _).symm
  · simp only [Pi.add_apply, Finset.sum_add_distrib, sum_greenOp, add_zero]
  · rw [laplacianOp_add, laplacianOp_greenOp, laplacianOp_greenOp,
      ← meanSub_add]

/-- **Headline 4b.** `greenOp` is homogeneous in the source. -/
theorem greenOp_smul (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (c : ℝ) (g : V → ℝ) :
    greenOp w hw hw0 hpos (c • g) = c • greenOp w hw hw0 hpos g := by
  apply (eq_greenOp_of w hw hw0 hpos (c • g)
    (c • greenOp w hw hw0 hpos g) _ _).symm
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, sum_greenOp,
      mul_zero]
  · rw [laplacianOp_smul, laplacianOp_greenOp, ← meanSub_smul]

/-- **Headline 5 — K-SR-4 at the operator itself.** A constant
source — pure total mass, zero contrast — inverts to the zero
potential: the Green operator does not respond to the total-mass
direction at all. -/
theorem greenOp_const (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (c : ℝ) :
    greenOp w hw hw0 hpos (fun _ => c) = 0 := by
  apply (eq_greenOp_of w hw hw0 hpos (fun _ => c) 0 _ _).symm
  · simp
  · have hL0 : laplacianOp w (0 : V → ℝ) = 0 := laplacianOp_const w 0
    rw [hL0, meanSub_const]

/-- **Headline 6.** The operator factors through the projection,
as a theorem about the operator: pre-projecting the source
changes nothing. -/
theorem greenOp_meanSub (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (g : V → ℝ) :
    greenOp w hw hw0 hpos (meanSub g) = greenOp w hw hw0 hpos g := by
  apply (eq_greenOp_of w hw hw0 hpos (meanSub g)
    (greenOp w hw hw0 hpos g) _ _).symm
  · exact sum_greenOp w hw hw0 hpos g
  · rw [laplacianOp_greenOp, meanSub_meanSub]

/-- **Headline 8 — the blindness ceiling as an iff.** The sources
the Green operator kills are exactly the constants: its kernel
is precisely the total-mass direction (a constant shift of the
source), nothing else. Forward: if `greenOp g = 0` then
`meanSub g = L (greenOp g) = 0`, so `g` is its own mean,
constant. Backward: headline 5. -/
theorem greenOp_eq_zero_iff (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (g : V → ℝ) :
    greenOp w hw hw0 hpos g = 0 ↔ ∃ c : ℝ, g = fun _ => c := by
  constructor
  · intro h
    have hmean : meanSub g = 0 := by
      have hL := laplacianOp_greenOp w hw hw0 hpos g
      rw [h] at hL
      have hL0 : laplacianOp w (0 : V → ℝ) = 0 := laplacianOp_const w 0
      rw [hL0] at hL
      exact hL.symm
    refine ⟨meanVal g, funext fun i => ?_⟩
    have hi := congrFun hmean i
    simp only [meanSub, Pi.zero_apply] at hi
    show g i = meanVal g
    linarith
  · rintro ⟨c, rfl⟩
    exact greenOp_const w hw hw0 hpos c

/-- **Headline 9 — agreement with the landed API.** The Green
potential is exactly SHADOW-TEST-1's canonical potential with its
gauge fixed by mean-subtraction: `greenOp … g = meanSub
(poissonPotential … g)`. Mean-subtracting a potential does not
change its Laplacian (§1), and it forces the gauge — so the two
constructions agree, and downstream consumers (SR-5's composite
among them) can rewrite between them. -/
theorem greenOp_eq_meanSub_poissonPotential (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (g : V → ℝ) :
    greenOp w hw hw0 hpos g
      = meanSub (poissonPotential w hw hw0 hpos g) := by
  apply (eq_greenOp_of w hw hw0 hpos g
    (meanSub (poissonPotential w hw hw0 hpos g)) _ _).symm
  · exact sum_meanSub_eq_zero _
  · rw [laplacianOp_meanSub, laplacianOp_poissonPotential]

/-- **Self-adjointness (the scoping's optional stretch, landed).**
The Green operator is symmetric in the seat's bilinear form, on
mean-zero arguments: `∑ i, f i * (greenOp g) i = ∑ i, (greenOp f) i
* g i`. Both sides reduce through `laplacianOp_symm_form` once the
inverse laws are spent. -/
theorem sum_mul_greenOp_comm (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (f g : V → ℝ)
    (hf : ∑ i, f i = 0) (hg : ∑ i, g i = 0) :
    (∑ i, f i * greenOp w hw hw0 hpos g i)
      = ∑ i, greenOp w hw hw0 hpos f i * g i := by
  have hLf : laplacianOp w (greenOp w hw hw0 hpos f) = f := by
    rw [laplacianOp_greenOp, meanSub_of_sum_eq_zero f hf]
  have hLg : laplacianOp w (greenOp w hw hw0 hpos g) = g := by
    rw [laplacianOp_greenOp, meanSub_of_sum_eq_zero g hg]
  calc (∑ i, f i * greenOp w hw hw0 hpos g i)
      = ∑ i, greenOp w hw hw0 hpos g i
          * laplacianOp w (greenOp w hw hw0 hpos f) i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hLf]
        ring
    _ = ∑ i, greenOp w hw hw0 hpos f i
          * laplacianOp w (greenOp w hw hw0 hpos g) i :=
        laplacianOp_symm_form w hw (greenOp w hw hw0 hpos f)
          (greenOp w hw hw0 hpos g)
    _ = ∑ i, greenOp w hw hw0 hpos f i * g i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hLg]

end GreenOp

end ThetLogos
