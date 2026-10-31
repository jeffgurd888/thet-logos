import ThetLogos.GravityPosePost

namespace ThetLogos

/-!
# ThetLogos.GravityPoseDecision - GR-POSE-1: the decision brick

**Working label only.** The module name `GravityPoseDecision`
and the line name GR-POSE are working labels; Jeff names.

**Status: DECISION - the pin's registered pose `PoseKill` is
proved here, against the frozen pair of
`ThetLogos.GravityPosePost` (`PoseKillClassC`, `PoseKillGravC`),
with no definition renamed, narrowed, or extended. NO CLAIM
beyond the decision itself. No gravity object is defined,
constructed, or asserted to exist. Dials 0/4.**

Governing pack: `routeb-general-scratch/pack-gr-pose-1.md`,
governing memo: `routeb-general-scratch/scoping-gravity-pose-2026-10-31.md`
(section 2 pose P-kill, section 5 GR-POSE-1 spec, section 6
kills).

## Section-0 fence (on the face)

This brick seats NO object; Dial 2 = 0 under every outcome,
including this one. The honest FULL sentence for the headline
below (K-GR-LAUNDER fence) is: "the corpus's gravity
coefficient is imported, not derived" - a theorem ABOUT THE
CORPUS, completing SA-FLIP-1's prose fence. It is not a
statement that the corpus understands or proves anything
about gravity itself, and it uses no seating or warming
language (K-GR-BUY).

Ceiling fence for fenced vocabulary: the words metric,
geodesic, curvature, Einstein, stress-energy, propagation,
spacetime, and the expression 1/r are FRONTIER vocabulary in
this line, owned by nothing in the corpus. In this module
each of them appears only inside this fence. Any other use
is a fence breach.

## The decision, in one paragraph

Membership in the frozen class C is exactly R-independence
(the pin's read-back `poseKillClassC_iff`): a member's value
does not change when only the R-slot value changes. The
frozen predicate `PoseKillGravC` demands, at some finite
square `X`, an affine R-response at the landed slope
`a2GravCoeff`, and `a2_grav_coeff_ne_zero` says that slope is
not zero. Evaluating the demanded response at `R = 1` against
R-independence at the same square forces the slope to be
zero - a contradiction. The decision therefore lands FULL,
with no split at the class boundary: the argument uses only
the two frozen definitions and the two landed facts named
above, and it narrows neither the class nor the predicate
(K-GR-STAB: no silent repair was needed or made).

## What is proved here

1. `rIndependent_response_slope_eq_zero` - the general
   dependence lemma: an R-independent functional whose value
   at a square responds affinely with slope `c` has `c = 0`.
2. `poseKill_response_slope_eq_zero` - the same at the
   landed slope `a2GravCoeff`, from the frozen pair alone.
3. `poseKillGravC_not_satisfiable` - no functional at all
   satisfies the frozen predicate (its class conjunct is
   already enough to contradict its response conjunct).
4. `poseKill_decision` - the headline: the pin's `PoseKill`,
   discharged in its registered shape.
5. `gilkeyA2_response_witness` and `gilkeyA2_not_mem_classC` -
   the landed functional `gilkeyA2` does carry the response
   shape (the pin's read-back), and exactly therefore it is
   not a member of the frozen class C: its R-half is not a
   functional of the finite data alone.
-/

/-! ## The dependence lemma -/

/-- **General dependence lemma.** If a functional `F` is
R-independent at a square `X` (its value at `X` does not
change when only the R-slot value changes) and at that same
square it responds to the R-slot affinely with slope `c`,
then `c = 0`. Proof: the response at `R = 1` says
`F 1 X = c + F 0 X`, while R-independence says
`F 1 X = F 0 X`; cancelling the common term gives `c = 0`.
No hypothesis on `F` beyond the two displayed properties is
used. -/
theorem rIndependent_response_slope_eq_zero
    (F : ℂ → Matrix I32 I32 ℂ → ℂ) (X : Matrix I32 I32 ℂ)
    (c : ℂ)
    (hindep : ∀ R₁ R₂ : ℂ, F R₁ X = F R₂ X)
    (hresp : ∀ R : ℂ, F R X = c * R + F 0 X) :
    c = 0 := by
  have h1 : F 1 X = c * 1 + F 0 X := hresp 1
  have hconst : F 1 X = F 0 X := hindep 1 0
  rw [hconst] at h1
  have h2 : c * 1 + F 0 X = F 0 X := h1.symm
  rw [mul_one] at h2
  have h3 : c = c + F 0 X - F 0 X := by ring
  rw [h2, sub_self] at h3
  exact h3

/-- **The dependence lemma at the frozen pair.** If `F`
lies in the frozen class `PoseKillClassC` and at some
finite square `X` it carries the affine R-response at the
landed slope `a2GravCoeff` demanded by `PoseKillGravC`,
then `a2GravCoeff = 0`. This is the whole contradiction of
the decision, isolated before it is closed against
`a2_grav_coeff_ne_zero`. -/
theorem poseKill_response_slope_eq_zero
    (F : ℂ → Matrix I32 I32 ℂ → ℂ) (X : Matrix I32 I32 ℂ)
    (hC : PoseKillClassC F)
    (hresp : ∀ R : ℂ, F R X = a2GravCoeff * R + F 0 X) :
    a2GravCoeff = 0 := by
  have hindep : ∀ (R₁ R₂ : ℂ) (Y : Matrix I32 I32 ℂ),
      F R₁ Y = F R₂ Y :=
    (poseKillClassC_iff F).mp hC
  exact rIndependent_response_slope_eq_zero F X a2GravCoeff
    (fun R₁ R₂ => hindep R₁ R₂ X) hresp

/-! ## The decision -/

/-- **No functional satisfies the frozen predicate.** The
predicate `PoseKillGravC` carries class membership as its
first conjunct and the affine response at slope
`a2GravCoeff` as its second; the lemma above turns those
two conjuncts into `a2GravCoeff = 0`, and the landed
`a2_grav_coeff_ne_zero` closes the contradiction. Stated
without the extra class hypothesis of `PoseKill` because
the predicate supplies it itself. -/
theorem poseKillGravC_not_satisfiable
    (F : ℂ → Matrix I32 I32 ℂ → ℂ) :
    ¬ PoseKillGravC F := by
  rintro ⟨hC, X, hresp⟩
  exact a2_grav_coeff_ne_zero
    (poseKill_response_slope_eq_zero F X hC hresp)

/-- **HEADLINE - GR-POSE-1, the decision, FULL.**
The pin's registered pose `PoseKill`, discharged in exactly
its registered shape (read back by the pin's
`poseKill_unfold`): for every functional `F`, membership in
the frozen class C excludes the frozen predicate GRAV_C.
In the pack's honest sentence: the corpus's gravity
coefficient is imported, not derived - the R-half of the
separated a2 coefficient enters through the stated Gilkey
form of `SpectralActionA2`, not from any functional of the
finite spectral data alone. A theorem about the corpus's
own expressive limits for this named class; it seats no
object and Dial 2 = 0. -/
theorem poseKill_decision : PoseKill := by
  intro F _hC hGrav
  exact poseKillGravC_not_satisfiable F hGrav

/-- **Read-back of the headline against the pin.** The
headline above is the pin's `PoseKill` itself, unfolded by
the pin's own `poseKill_unfold`: the closure chain from the
proved decision to the registered statement is the
identity, stated here so the match of shapes is checked by
the kernel rather than asserted in prose. -/
theorem poseKill_decision_unfolded :
    ∀ F : ℂ → Matrix I32 I32 ℂ → ℂ,
      PoseKillClassC F → ¬ PoseKillGravC F :=
  poseKill_unfold.mp poseKill_decision

/-! ## The landed functional, on the other side of the fence -/

/-- **The response shape does occur - outside the class.**
The landed functional `gilkeyA2` satisfies the response
conjunct of the frozen predicate at every finite square, in
particular at the zero square: this is the pin's
`gilkeyA2_response_readback` restated as a witness. The
response shape is therefore not vacuous; what the decision
excludes is its occurrence inside the frozen class. -/
theorem gilkeyA2_response_witness :
    ∃ X : Matrix I32 I32 ℂ,
      ∀ R : ℂ, gilkeyA2 R X = a2GravCoeff * R + gilkeyA2 0 X :=
  ⟨0, fun R => gilkeyA2_response_readback R 0⟩

/-- **`gilkeyA2` is not a member of the frozen class.** If
it were, the decision's lemma would force its R-slope to
vanish; the slope is `a2GravCoeff`, landed nonzero. So the
one landed functional carrying the R-response does not
factor through the finite data alone - its R-dependence is
exactly the part the finite factor cannot supply. -/
theorem gilkeyA2_not_mem_classC :
    ¬ PoseKillClassC gilkeyA2 := by
  intro hC
  obtain ⟨X, hresp⟩ := gilkeyA2_response_witness
  exact a2_grav_coeff_ne_zero
    (poseKill_response_slope_eq_zero gilkeyA2 X hC hresp)

/-- **Two-value form of the same exclusion.** For a member
of the frozen class, the values at any two R-slot values
agree at every square (the pin's read-back), while the
landed `gilkeyA2` values at `R = 0` and `R = 1` differ at
every square by exactly the nonzero slope - the finite
statement a later brick can cite without unfolding the
decision. -/
theorem gilkeyA2_values_differ (X : Matrix I32 I32 ℂ) :
    gilkeyA2 1 X - gilkeyA2 0 X = a2GravCoeff := by
  have h := gilkeyA2_response_readback 1 X
  rw [h]
  ring

end ThetLogos
