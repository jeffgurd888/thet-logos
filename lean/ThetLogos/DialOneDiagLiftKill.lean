import Mathlib.Tactic
import ThetLogos.DialOneExtraction
import ThetLogos.DialOneCrossSign
import ThetLogos.DialOneConjugationCounterexample

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneExtraction
open ThetLogos.DialOneCrossSign
open ThetLogos.DialOneShapeBIdentification
open ThetLogos.DialOneClassificationPin
open ThetLogos.DialOneConjugationCounterexample

namespace ThetLogos.DialOneDiagLiftKill

/-!
# ThetLogos.DialOneDiagLiftKill — K-CLS-DIAG FIRED:
the CLS-A1 brick's prove-target was already refuted

**Commission:** CLS Line A, front brick only (CLS-A1,
`DiagLift` — within-sign diagonality), commissioned by
Zero 2026-11-17 ("Fire both C and the DiagLift brick")
against the CLS classification scope of the same day.
**Verdict of this brick: THE KILL. There is nothing to
prove — the statement is FALSE, and was already refuted
at T1 in-tree before the scope was written.** This
module is the kill certificate in the scope's own
statement shapes; every load-bearing fact is landed
material, cited, not re-derived.

## The kill, at full rank

**K-CLS-DIAG FIRES** (pre-registered in the CLS scope
§8: "if within-sign diagonality (`DiagLift`) fails at
any exhibited base π, `ExtractionLemma` as pinned dies
in its current form"). It had in fact already fired,
under its registered name **K-CLS-1a**, in
`DialOneConjugationCounterexample` (main tree,
committed; disk sha256 = blob sha256 at 11c8a39):

* `k_cls_1a_fired` — there is a `π` (`piU`) with
  `DialOneBase π` such that for EVERY primitive
  determinant-one direction there exist `t` and seats
  `s ≠ s'` of the SAME γ-sign with
  `liftedProd π α β t s s' ≠ 0`.
* `not_forall_base_diagLift` —
  `¬ ∀ π, DialOneBase π → DiagLift π`, witnessed by
  `piU` at the seat pair `(2, 28)`: both seats carry
  γ-sign `+1` (`gamma_two_twenty_eight`), and along
  `(3, -1)` at `t = π/2` the lifted entry is
  `(12/25)(1 - i) ≠ 0`
  (`liftedProd_piU_entry_pi_div_two`,
  `liftedProd_piU_entry_ne_zero`); the second primitive
  direction `(-3, 1)` is the same computation at `-t`
  (`liftedProd_piU_entry_neg_dir`), and `(3, -1)`,
  `(-3, 1)` are the ONLY primitive det-1 directions
  (`det_one_pi1`, `dir_of_det_shape_4312`).

This module adds the two consequences in the scope's
shapes:

* `not_forall_base_extractionLemma` — the CLS-1
  A-shape `∀ π, DialOneBase π → ExtractionLemma π`
  is REFUTED at T1: `ExtractionLemma` is `DiagLift`
  plus the regularity conjunct
  (`extractionLemma_implies_diagLift` is the
  projection), so the universal base implication dies
  with `DiagLift`. CLS-1's prove-direction is closed,
  negatively.
* `within_sign_diagonality_refuted` — CLS-A1's own
  statement (within-sign diagonality of `liftedProd`
  for every base π, at every primitive det-1 direction)
  is FALSE, at the same witness.

## Correction to the commissioning scope, at full rank

The CLS classification scope (2026-11-17) priced
CLS-A1 as OPEN prove-work (M–L) and described
within-sign diagonality as "untouched", with K-CLS-1a
"armed at the seat pair `(8, 9)`". That status was
stale when written: `DialOneConjugationCounterexample`
and `DialOneRegularPin` — neither in the scope's
source list — already carried the firing, and the
counterexample's own face fences that `(8, 9)` "is NOT
the firing pair and cannot be" (channel separation);
the firing pair is `(2, 28)`. The scope's §1 corrected
three stale premises of ITS brief; this is a fourth,
against the scope itself, recorded at the same volume.
(The scope's Line A total, L+, and its §6 account —
classification buys M-U2 nothing directly — are
unaffected in direction: the diagonality half of
CLS-1 is now decided, negatively, which is more than
the scope knew, not less.)

## Fences (on the face)

* **Base form only.** The STRENGTHENED form is NOT
  addressed: `piU`'s strengthened-family status is
  claimed NEITHER way (inherited from the
  counterexample's face: the colour projectors do not
  commute with `conjU`, so C3-type clauses are not
  inherited). Nothing here decides `ExtractionLemma`
  over `DialOneStrengthenedFam` or over
  `DialOneRegular`.
* **`ExtractionLemma` survives as hypothesis
  material.** π₁ satisfies it (`extractionLemma_pi1`,
  landed), `extraction_modulo` stands, and
  `DialOneRegular` (base ∧ the lemma) remains a
  coherent, inhabited re-pose. What dies is only the
  claim that the BASE implies it.
* **CLS-A2 is not commissioned and is not started.**
  The regularity half is untouched by this brick; with
  the diagonality half decided negatively at the base,
  A2's premise (a common front brick A1) is gone in
  the prove-direction — any re-pose is a new entry,
  under the relabeling rule, on a fresh ruling.
* Cross-sign diagonality (CLS-1a-X, T1) is untouched;
  the decided pair (`PiAntiOrbitQReal`,
  `PreservationQReal`, both refuted at T1) and M-U1's
  closure are fences, not material.

**NO CLAIM. Dial 1 = 0; all dials 0/4.** Parts of
official statements closed by this module: 0.
-/

/-- **`ExtractionLemma` is `DiagLift` plus regularity.**
The projection: drop the differentiability conjunct
from the pinned lemma (`DialOneExtraction` §6) and
what remains is exactly `DiagLift`
(`DialOneConjugationCounterexample`, frozen verbatim
from the CLS-1a scoping §1.1 — same gcd form, same
determinant conjunct, same diagonality conjunct). -/
theorem extractionLemma_implies_diagLift
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    ExtractionLemma π → DiagLift π := by
  rintro ⟨α, β, hgcd, hdet, hdiag, -⟩
  exact ⟨α, β, hgcd, hdet, hdiag⟩

/-- **The witness's determinant along `(3, -1)` is 1.**
`piU` and `pi1` have the same determinant on the whole
algebra (`piU_det`, landed), and `pi1`'s determinant
along the primitive direction `(3, -1)` is 1 by the
landed `pi1_det_gen` — the same computation
`extractionLemma_pi1` performs. -/
theorem piU_det_one_3_neg1 (t : ℝ) :
    (piU (u1ParamGen 3 (-1) t)).det = 1 := by
  rw [piU_det]
  have h0 : (-4 * (3 : ℤ) + -12 * (-1) : ℤ) = 0 := rfl
  rw [pi1_det_gen, h0]
  simp

/-- **`piU` admits no `DiagLift` direction.** The
sharp form of the landed `not_forall_base_diagLift`,
with the witness named: any candidate direction for
`piU` has determinant one only if it is `(3, -1)` or
`(-3, 1)` (`det_one_pi1`, `dir_of_det_shape_4312`),
and at both, the within-sign seat pair `(2, 28)`
(both γ-sign `+1`) carries the nonzero lifted entry
`(12/25)(1 - i)` at `t = ±π/2`. -/
theorem not_diagLift_piU : ¬ DiagLift piU := by
  intro h
  obtain ⟨α, β, hgcd, hdet, hdiag⟩ := h
  have hdet1 : ∀ t, (pi1 (u1ParamGen α β t)).det = 1 := by
    intro t
    rw [← piU_det]
    exact hdet t
  have hlin := det_one_pi1 hdet1
  have hne : (⟨2, by norm_num⟩ : Fin 32)
      ≠ ⟨28, by norm_num⟩ := by decide
  rcases dir_of_det_shape_4312 hgcd hlin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h0 := hdiag (Real.pi / 2) ⟨2, by norm_num⟩
      ⟨28, by norm_num⟩ hne
    rw [liftedProd_piU_entry_pi_div_two] at h0
    have hcontra : ((12 / 25 : ℝ) : ℂ) * (1 - Complex.I) ≠ 0 :=
      mul_ne_zero (by norm_num) (by
        intro hh
        have him := congrArg Complex.im hh
        simp at him)
    exact hcontra h0
  · have h0 := hdiag (-(Real.pi / 2)) ⟨2, by norm_num⟩
      ⟨28, by norm_num⟩ hne
    rw [liftedProd_piU_entry_neg_dir] at h0
    have hcontra : ((12 / 25 : ℝ) : ℂ) * (1 - Complex.I) ≠ 0 :=
      mul_ne_zero (by norm_num) (by
        intro hh
        have him := congrArg Complex.im hh
        simp at him)
    exact hcontra h0

/-- **HEADLINE — K-CLS-DIAG FIRED: the CLS-1 A-shape
is refuted.** `∀ π, DialOneBase π → ExtractionLemma π`
is FALSE at T1. The base does not imply the extraction
lemma: the diagonality conjunct already fails at the
exhibited base point `piU`, so no proof of the
A-shape exists and CLS-1's prove-direction is closed,
negatively. (The lemma itself, as a hypothesis —
`DialOneRegular` — is untouched; see the header
fences.) -/
theorem not_forall_base_extractionLemma :
    ¬ ∀ π, DialOneBase π → ExtractionLemma π := by
  intro h
  exact not_diagLift_piU
    (extractionLemma_implies_diagLift piU
      (h piU dialOneBase_piU))

/-- **CLS-A1's own statement, refuted.** Within-sign
diagonality of `liftedProd` for every base `π`, at
every primitive determinant-one direction — the front
brick as scoped — is FALSE: at `piU`, direction
`(3, -1)`, `t = π/2`, the same-sign pair `(2, 28)`
carries `(12/25)(1 - i) ≠ 0`. Together with CLS-1a-X
(cross-sign diagonality, T1), this decides the
diagonality content of `ExtractionLemma` completely
at the base: the cross-sign half is a theorem, the
within-sign half is a counterexample. -/
theorem within_sign_diagonality_refuted :
    ¬ ∀ π, DialOneBase π →
      ∀ α β : ℤ, Nat.gcd α.natAbs β.natAbs = 1 →
        (∀ t, (π (u1ParamGen α β t)).det = 1) →
        ∀ t (s s' : Fin 32), s ≠ s' →
          gammaF s s = gammaF s' s' →
          liftedProd π α β t s s' = 0 := by
  intro h
  have h0 := h piU dialOneBase_piU 3 (-1) (by decide)
    piU_det_one_3_neg1 (Real.pi / 2) ⟨2, by norm_num⟩
    ⟨28, by norm_num⟩ (by decide)
    (by rw [gamma_two_twenty_eight.1,
      gamma_two_twenty_eight.2])
  exact liftedProd_piU_entry_ne_zero h0

end ThetLogos.DialOneDiagLiftKill
