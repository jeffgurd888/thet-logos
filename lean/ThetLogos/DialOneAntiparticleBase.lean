import Mathlib.Tactic
import ThetLogos.DialOneAntiparticleChapter
import ThetLogos.DialOneShapeBIdentification
import ThetLogos.DialOneSwapOrbitBase

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneGammaTraceChecks
open ThetLogos.DialOneGammaFamilyPin
open ThetLogos.DialOneGammaFamilyChecks
open ThetLogos.DialOneClassificationPin
open ThetLogos.DialOneSwapOrbit
open ThetLogos.DialOneSwapOrbitBase
open ThetLogos.DialOneShapeBIdentification
open ThetLogos.DialOneAntiparticleChapter

/-!
# CLS-3c-A — the `piAnti` cell, decided by colour-twist transport

Governing texts: the CLS-3c-A scoping
(`routeb-general-scratch/scoping-cls-3c-a-2026-11-02.md`,
read in full) and its pack
(`routeb-general-scratch/pack-cls-3c-a.md`). CLS-3c
(`DialOneAntiparticleChapter`) landed `piAnti`'s
definition and named its base status OPEN. This module
decides that cell — by the scoping's **τ-transport
route** (not the fallback clause-by-clause entry
transport): `piAnti` is *literally* π₁ precomposed with
entrywise colour conjugation,

  `piAnti = pi1 ∘ colourTwist`,

`colourTwist` is an `AF`-algebra automorphism flipping
only the β-sign of the two generator families
(`u1Gen` / `u1ParamGen`), and every clause of
`DialOneBase`, of the strengthened family, and the
weight relation is transported from π₁'s landed proofs
by substitution at the twisted argument. Clause 10's
witness flips `(3, −1) ↦ (3, 1)`, exactly as scoped.

## Verdicts (all T1 here)

* `DialOneBase piAnti` — the base holds.
* `DialOneStrengthenedFam piAnti` — the full
  strengthened family holds (`C3 piAnti` was already
  landed in CLS-3c; `C3lep` / `C3col` / `FeR` are
  transported here).
* `weightAt piAnti commonWeightVector` — `piAnti`
  carries exactly the table's common weights, and
  hence `WeightQuestionW` is answered YES by `piAnti`
  (`weightQuestionW_piAnti`), at exactly the scoping's
  grade: a second *model* of the strengthened set
  carrying the common weights, not a forcing result.

## Fences, on the face

* **CLS-3c's toggle-fenced uniqueness is NOT
  contradicted**: its boundary theorem fences
  uniqueness to toggles / named directions, and
  `piAnti` is not a toggle — it is not π₁ (landed,
  `piAnti_ne_pi1`) and it is no toggle-orbit point
  (`piAnti_not_orbit` here). A successful landing is
  the FINDING (an off-orbit strengthened point
  carrying the common weights), not a kill of anything
  landed.
* **CLS-2b's orbit classification is untouched**:
  `piAnti` is not an orbit point, and the
  classification is cited, never re-read.
* **K-CLS-3c-A does not fire**: no landed negation of
  any of the three headlines exists; the scoping's
  transport claim stands.

**NO CLAIM; Dial 1 = 0; all dials 0/4. Classification
data only: parts of any official statement closed by
this module: 0.**
-/

namespace ThetLogos.DialOneAntiparticleBase

/-! ## The colour twist -/

/-- **The colour twist** `τ` (the scoping's one new
definition; working label — practical naming only):
entrywise conjugation of the M₃ (colour) summand
alone; the ℂ and ℍ summands are untouched. -/
def colourTwist (a : AF) : AF :=
  ⟨a.u1, a.q, a.color.map (starRingEnd ℂ)⟩

/-- Entries of the twist: entrywise `star` on colour. -/
theorem colourTwist_color_apply (a : AF) (k l : Fin 3) :
    (colourTwist a).color k l = star (a.color k l) :=
  rfl

/-- **τ is multiplicative** for `afMul`: `star` over a
finite sum of products, with ℂ-entry commutativity
absorbing the `star_mul` order flip. -/
theorem colourTwist_afMul (a b : AF) :
    colourTwist (afMul a b)
      = afMul (colourTwist a) (colourTwist b) := by
  refine (ThetLogos.PreOptionARepresentation.ext_iff).mpr ⟨rfl, rfl, ?_⟩
  ext k l
  show star ((a.color * b.color) k l)
    = ((a.color.map (starRingEnd ℂ))
      * (b.color.map (starRingEnd ℂ))) k l
  rw [Matrix.mul_apply, Matrix.mul_apply, star_sum]
  apply Finset.sum_congr rfl
  intro x _
  show star (a.color k x * b.color x l)
    = star (a.color k x) * star (b.color x l)
  rw [star_mul]; exact mul_comm _ _

/-- **τ is additive** for `afAdd`, entrywise. -/
theorem colourTwist_afAdd (a b : AF) :
    colourTwist (afAdd a b)
      = afAdd (colourTwist a) (colourTwist b) := by
  refine (ThetLogos.PreOptionARepresentation.ext_iff).mpr ⟨rfl, rfl, ?_⟩
  ext k l
  show star ((a.color + b.color) k l)
    = ((a.color.map (starRingEnd ℂ))
      + (b.color.map (starRingEnd ℂ))) k l
  simp [Matrix.add_apply, star_add]

/-- **τ commutes with `afStar`**: at a colour entry both
sides collapse to the naked entry `a.color l k` — the
two stars (from `conjTranspose` and from the twist)
cancel; this is CLS-3c-A scoping §1 clause 3's
collapse, at the algebra level. -/
theorem colourTwist_afStar (a : AF) :
    colourTwist (afStar a) = afStar (colourTwist a) := by
  refine (ThetLogos.PreOptionARepresentation.ext_iff).mpr ⟨rfl, rfl, ?_⟩
  ext k l
  show star (a.color.conjTranspose k l)
    = ((a.color.map (starRingEnd ℂ)).conjTranspose) k l
  simp [Matrix.conjTranspose_apply, Matrix.map_apply]

/-- **τ fixes the unit** (`star 1 = 1`, `star 0 = 0`
entrywise on the colour identity). -/
theorem colourTwist_afOne : colourTwist afOne = afOne := by
  refine (ThetLogos.PreOptionARepresentation.ext_iff).mpr ⟨rfl, rfl, ?_⟩
  ext k l
  show star ((1 : Matrix (Fin 3) (Fin 3) ℂ) k l)
    = (1 : Matrix (Fin 3) (Fin 3) ℂ) k l
  by_cases h : k = l <;> simp [Matrix.one_apply, h]

/-- **τ fixes zero**, entrywise. -/
theorem colourTwist_afZero : colourTwist afZero = afZero := by
  refine (ThetLogos.PreOptionARepresentation.ext_iff).mpr ⟨rfl, rfl, ?_⟩
  ext k l
  show star ((0 : Matrix (Fin 3) (Fin 3) ℂ) k l)
    = (0 : Matrix (Fin 3) (Fin 3) ℂ) k l
  simp

/-- **τ is involutive** (`star_star` entrywise), hence
an `AF`-algebra automorphism with the laws above. -/
theorem colourTwist_involutive : Function.Involutive colourTwist := by
  intro a
  refine (ThetLogos.PreOptionARepresentation.ext_iff).mpr ⟨rfl, rfl, ?_⟩
  ext k l
  show star (star (a.color k l)) = a.color k l
  exact star_star _

/-- **τ is bijective**, by involutivity. -/
theorem colourTwist_bijective : Function.Bijective colourTwist :=
  colourTwist_involutive.bijective

/-- **τ flips only β in `u1Gen`**: the colour seat
`(β·I) • 1` maps to `((−β)·I) • 1`; the ℂ seat and the
zero ℍ seat are τ-fixed. -/
theorem colourTwist_u1Gen (α β : ℤ) :
    colourTwist (u1Gen α β) = u1Gen α (-β) := by
  refine (ThetLogos.PreOptionARepresentation.ext_iff).mpr ⟨rfl, rfl, ?_⟩
  ext k l
  by_cases h : k = l <;>
    simp [colourTwist, u1Gen, Matrix.map_apply, Matrix.smul_apply, h]

/-- **τ flips only β in `u1ParamGen`**: the colour seat
`exp (β·t·I) • 1` maps to `exp (−β·t·I) • 1` (the
landed `star_exp_int` pattern); the ℂ seat is τ-fixed. -/
theorem colourTwist_u1ParamGen (α β : ℤ) (t : ℝ) :
    colourTwist (u1ParamGen α β t) = u1ParamGen α (-β) t := by
  refine (ThetLogos.PreOptionARepresentation.ext_iff).mpr ⟨rfl, rfl, ?_⟩
  ext k l
  by_cases h : k = l
  · subst h
    simp only [colourTwist, u1ParamGen, Matrix.map_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one]
    have hstar : (starRingEnd ℂ)
        (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I)))
        = Complex.exp (-((β : ℂ) * ((t : ℂ) * Complex.I))) := by
      rw [starRingEnd_apply, star_exp_int]
    rw [hstar]
    congr 1
    push_cast
    ring
  · simp [colourTwist, u1ParamGen, Matrix.map_apply, Matrix.smul_apply,
      Matrix.one_apply_ne h]

/-! ## The one entry proof -/

/-- **`piAnti = pi1 ∘ colourTwist`, exactly** — the one
genuine entry proof of the brick: in the two changed
branches (slots 18–23 and 26–31) `pi1 (colourTwist a)`
carries `star (star (a.color k l)) = a.color k l`;
every other branch reads only `a.u1`, `a.q`, or
`star a.u1`, all τ-fixed. Proved by 32×32 entry
exhaustion over the two definitions, `star_star`
closing the antiquark branches inside `simp`. -/
theorem piAnti_eq_pi1_colourTwist :
    ∀ a, piAnti a = pi1 (colourTwist a) := by
  intro a
  ext i j
  obtain ⟨v, hv⟩ := i
  obtain ⟨w, hw⟩ := j
  interval_cases v <;> interval_cases w <;>
    simp [piAnti, pi1, colourTwist, Matrix.map_apply]

/-! ## Transport: the base -/

/-- **HEADLINE 1 — `DialOneBase piAnti`**, transported
clause by clause from the landed
`DialOneGammaTraceChecks.dialOneBase_pi1`: clauses 1–5
by the τ-laws, clause 6 by injectivity of π₁ composed
with bijective τ, clauses 7–9 by literal substitution
at `(τ a, τ b)` (`piOp` and `DF_oneGen` untouched),
clause 10 with the flipped witness `(3, 1)`. -/
theorem dialOneBase_piAnti : DialOneBase piAnti := by
  have h := ThetLogos.DialOneGammaTraceChecks.dialOneBase_pi1
  have e := piAnti_eq_pi1_colourTwist
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    calc piAnti (afMul a b)
        = pi1 (afMul (colourTwist a) (colourTwist b)) := by
          rw [e, colourTwist_afMul]
      _ = pi1 (colourTwist a) * pi1 (colourTwist b) := h.1 _ _
      _ = piAnti a * piAnti b := by rw [← e, ← e]
  · intro a b
    calc piAnti (afAdd a b)
        = pi1 (afAdd (colourTwist a) (colourTwist b)) := by
          rw [e, colourTwist_afAdd]
      _ = pi1 (colourTwist a) + pi1 (colourTwist b) := h.2.1 _ _
      _ = piAnti a + piAnti b := by rw [← e, ← e]
  · intro a
    calc piAnti (afStar a)
        = pi1 (afStar (colourTwist a)) := by
          rw [e, colourTwist_afStar]
      _ = (pi1 (colourTwist a))ᴴ := h.2.2.1 _
      _ = (piAnti a)ᴴ := by rw [← e]
  · calc piAnti afOne = pi1 (colourTwist afOne) := e _
      _ = pi1 afOne := by rw [colourTwist_afOne]
      _ = 1 := h.2.2.2.1
  · calc piAnti afZero = pi1 (colourTwist afZero) := e _
      _ = pi1 afZero := by rw [colourTwist_afZero]
      _ = 0 := h.2.2.2.2.1
  · have hfun : piAnti = pi1 ∘ colourTwist := funext e
    rw [hfun]
    exact h.2.2.2.2.2.1.comp colourTwist_bijective.injective
  · intro a
    rw [e]
    exact h.2.2.2.2.2.2.1 _
  · intro a b
    rw [e, e]
    exact h.2.2.2.2.2.2.2.1 _ _
  · intro Ynu Ye Yu Yd a b i j
    rw [e, e]
    exact h.2.2.2.2.2.2.2.2.1 Ynu Ye Yu Yd _ _ i j
  · refine ⟨3, 1, by norm_num, fun t => ?_⟩
    calc (piAnti (u1ParamGen 3 1 t)).det
        = (pi1 (u1ParamGen 3 (-1) t)).det := by
          rw [e, colourTwist_u1ParamGen]
      _ = 1 := by
          rw [pi1_det_gen]
          norm_num

/-! ## Transport: the γ-trace family -/

/-- **`C3lep piAnti`**, transported: the clause at
`(α, β)` for `piAnti` is π₁'s clause at `(α, −β)`,
since `piAnti (u1Gen α β) = pi1 (u1Gen α (−β))`. -/
theorem c3lep_piAnti : C3lep piAnti := by
  intro α β
  have e' : piAnti (u1Gen α β) = pi1 (u1Gen α (-β)) := by
    rw [piAnti_eq_pi1_colourTwist, colourTwist_u1Gen]
  rw [e']
  exact c3lep_pi1 α (-β)

/-- **`C3col c piAnti`** for every colour `c`,
transported the same way. -/
theorem c3col_piAnti (c : Fin 3) : C3col c piAnti := by
  intro α β
  have e' : piAnti (u1Gen α β) = pi1 (u1Gen α (-β)) := by
    rw [piAnti_eq_pi1_colourTwist, colourTwist_u1Gen]
  rw [e']
  exact c3col_pi1 c α (-β)

/-- **`FeR piAnti`**, transported the same way. -/
theorem feR_piAnti : FeR piAnti := by
  intro α β
  have e' : piAnti (u1Gen α β) = pi1 (u1Gen α (-β)) := by
    rw [piAnti_eq_pi1_colourTwist, colourTwist_u1Gen]
  rw [e']
  exact feR_pi1 α (-β)

/-- **The clean-tier γ-trace family for `piAnti`**:
`GammaFamily piAnti`, assembled from the three
transports. -/
theorem gammaFamily_piAnti : GammaFamily piAnti :=
  ⟨c3lep_piAnti, c3col_piAnti, feR_piAnti⟩

/-- **HEADLINE 2 — `DialOneStrengthenedFam piAnti`**:
base (Headline 1) ∧ `C3 piAnti` (landed in CLS-3c,
`DialOneAntiparticleChapter.c3_piAnti`) ∧ the family
(transported above). -/
theorem strengthenedFam_piAnti : DialOneStrengthenedFam piAnti :=
  ⟨dialOneBase_piAnti,
   ThetLogos.DialOneAntiparticleChapter.c3_piAnti,
   gammaFamily_piAnti⟩

/-! ## Transport: the weights -/

/-- **HEADLINE 3 — `weightAt piAnti
commonWeightVector`**, transported from the landed
`DialOneShapeBIdentification.weightAt_pi1_common`:
`piAnti` carries the common weights along the flipped
direction `(α, −β)` of π₁'s direction — for π₁'s
`(3, −1)` this is the frozen `(3, 1)`. The `gcd` is
unchanged (`natAbs` of a negation), and the lifted
eigenvalue at every seat is π₁'s, since
`piAnti (u1ParamGen α (−β) t)
= pi1 (u1ParamGen α β t)` as matrices. -/
theorem weightAt_piAnti_common :
    weightAt piAnti commonWeightVector := by
  obtain ⟨α, β, hgcd, hdet, hlift⟩ :=
    ThetLogos.DialOneShapeBIdentification.weightAt_pi1_common
  refine ⟨α, -β, ?_, ?_, ?_⟩
  · rwa [Int.natAbs_neg]
  · intro t
    have e' : piAnti (u1ParamGen α (-β) t)
        = pi1 (u1ParamGen α β t) := by
      rw [piAnti_eq_pi1_colourTwist, colourTwist_u1ParamGen, neg_neg]
    rw [e']
    exact hdet t
  · intro t s
    have e' : piAnti (u1ParamGen α (-β) t)
        = pi1 (u1ParamGen α β t) := by
      rw [piAnti_eq_pi1_colourTwist, colourTwist_u1ParamGen, neg_neg]
    rw [e']
    exact hlift t s

/-- **Grade W, answered YES by `piAnti`**:
`WeightQuestionW` holds via
`⟨piAnti, strengthenedFam_piAnti, piAnti_ne_pi1,
weightAt_piAnti_common⟩` — a representation in the
strengthened set other than π₁ carrying exactly the
common weights, at exactly the scoping's grade (a
second model, not a forcing statement). -/
theorem weightQuestionW_piAnti : WeightQuestionW :=
  ⟨piAnti, strengthenedFam_piAnti,
   ThetLogos.DialOneAntiparticleChapter.piAnti_ne_pi1,
   weightAt_piAnti_common⟩

/-- **`piAnti` is off the toggle orbit**: it is no
`orbitRep b`. By CLS-2b's landed classification
(`orbit_classification_complete`, cited untouched),
a strengthened orbit point is the identity toggle
(π₁ — excluded by landed `piAnti_ne_pi1`) or the
uniform triple swap (excluded because it does not
carry the common weights, landed
`allSwap_not_weightAt_common`, while `piAnti` does). -/
theorem piAnti_not_orbit :
    ∀ b : Fin 4 → Bool, piAnti ≠ orbitRep b := by
  intro b h
  have hstr : DialOneStrengthenedFam (orbitRep b) :=
    h ▸ strengthenedFam_piAnti
  have hclass :=
    (ThetLogos.DialOneSwapOrbitBase.orbit_classification_complete b).mp
      hstr
  rcases hclass with hb | hb
  · subst hb
    exact ThetLogos.DialOneAntiparticleChapter.piAnti_ne_pi1
      (h.trans ThetLogos.DialOneSwapOrbit.orbitRep_zero)
  · subst hb
    exact ThetLogos.DialOneSwapOrbitBase.allSwap_not_weightAt_common
      (h ▸ weightAt_piAnti_common)

/-! ## The chapter headline -/

/-- **CLS-3c-A, assembled**: the `piAnti` cell is
decided by colour-twist transport — `piAnti = pi1 ∘
colourTwist`, the base holds, the full strengthened
family holds, the common weights are carried, Grade W
is answered YES by `piAnti`, and `piAnti` lies off the
toggle orbit. **CLS-3c's toggle-fenced uniqueness is
not contradicted** (`piAnti` is not a toggle: neither
π₁ nor an orbit point) and **CLS-2b's orbit
classification is untouched**. K-CLS-3c-A does not
fire. -/
theorem antiparticle_base_chapter :
    piAnti = pi1 ∘ colourTwist
      ∧ DialOneBase piAnti
      ∧ DialOneStrengthenedFam piAnti
      ∧ weightAt piAnti commonWeightVector
      ∧ WeightQuestionW
      ∧ ∀ b : Fin 4 → Bool, piAnti ≠ orbitRep b :=
  ⟨funext piAnti_eq_pi1_colourTwist, dialOneBase_piAnti,
   strengthenedFam_piAnti, weightAt_piAnti_common,
   weightQuestionW_piAnti, piAnti_not_orbit⟩

-- Axiom audit for the three headlines (expected:
-- [propext, Classical.choice, Quot.sound] throughout).
#print axioms dialOneBase_piAnti
#print axioms strengthenedFam_piAnti
#print axioms weightAt_piAnti_common

end ThetLogos.DialOneAntiparticleBase
