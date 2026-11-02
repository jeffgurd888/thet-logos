import Mathlib.Tactic
import ThetLogos.DialOneGammaFamilyChecks

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneDoubleFlipPin
open ThetLogos.DialOneGammaTraceChecks
open ThetLogos.DialOneGammaFamilyPin
open ThetLogos.DialOneGammaFamilyChecks
open ThetLogos.DialOneDoubleFlipChecks

/-!
# CLS-3a — the lepton chapter of Grade T (Dial-1 classification lane)

The lepton toggle group is `(ℤ/2)²`: the ν_R flip and the e_R
flip independently — `{pi1, piFlip, piEFlip, piDouble}`.
Three of its four points were already decided in landed
modules: `pi1` lies in `DialOneStrengthenedFam` (landed,
`DialOneGammaFamilyChecks.strengthened_pi1`); `piFlip` is
excluded by `C3` alone (landed, D1-C3:
`trace_gammaF_piFlip_u1Gen` gives trace `2α·i`);
`piDouble` is excluded by `FeR` alone (landed, D1-CMP-FAM:
`trace_feR_piDouble` gives `−2α·i` at the e_R seats). The
missing object is the e_R flip alone, `piEFlip` — π₁ plus
ONLY piDouble's e_R single at `s9`, verbatim from the
D1-CMP pin.

## Verdicts (all T1, machine-checked below)

* **`piEFlip` fails `C3`**: `Tr (γ_F · piEFlip (u1Gen α β))
  = −2α·i` exactly (`trace_gammaF_piEFlip_u1Gen`) — the s9
  single's γ-weighted contribution, with no seat-8 term to
  cancel it. Hence `¬ C3 piEFlip` and
  `¬ DialOneStrengthenedFam piEFlip` (C3 is a conjunct).
* **`piEFlip` fails `FeR` independently**: the e_R
  projection is exactly seats `{9, 25}` and piEFlip's
  single lives there: `Tr (γ_F · eRProj · piEFlip
  (u1Gen α β)) = −2α·i` (`trace_feR_piEFlip`), witness
  `(1, 0)` — the same value as piDouble's FeR trace,
  because piDouble's s8 single vanishes against `eRProj`
  (landed). A second, independent exclusion.
* **The chapter headline** (`lepton_toggle_membership`):
  over the four-element lepton toggle set,
  `DialOneStrengthenedFam π ↔ π = pi1`, assembled from
  landed parts only plus this brick's piEFlip exclusions.

## Fence — no Base analysis

**The chapter closes at the C3/family level. NO Base
analysis is done anywhere in this module**: the lepton
points' Base status is decided only for piDouble (landed
IN base, `DialOneDoubleFlipChecks.dialOneBase_piDouble`),
and the chapter's exclusions never needed it — piFlip,
piEFlip, and piDouble are each excluded by a γ-trace
clause of the strengthened family alone.

**NO CLAIM; Dial 1 = 0; all dials 0/4. Classification
data only: parts of any official statement closed by
this module: 0.**
-/

namespace ThetLogos.DialOneLeptonChapter

/-! ## The e_R flip alone -/

/-- **The e_R flip alone**: π₁ plus ONLY piDouble's e_R
single — the seat-9 un-conjugation `a.u1 − star a.u1` at
`s9`, verbatim from the D1-CMP pin's `piDouble` (π₁
already conjugates e_R, so the flip there is
un-conjugation). Seat 9 acts by `a.u1`, every other entry
is π₁'s. The fourth point of the lepton toggle group
`(ℤ/2)²`. -/
def piEFlip (a : AF) : Matrix (Fin 32) (Fin 32) ℂ :=
  pi1 a + Matrix.single s9 s9 (a.u1 - star a.u1)

/-- Read-back: `piEFlip` is visibly π₁ plus the s9 single
alone. -/
theorem piEFlip_unfold (a : AF) :
    piEFlip a
      = pi1 a + Matrix.single s9 s9 (a.u1 - star a.u1) :=
  rfl

/-- Read-back: the step from π₁ to `piEFlip` is exactly
the s9 single. -/
theorem piEFlip_sub_pi1 (a : AF) :
    piEFlip a - pi1 a
      = Matrix.single s9 s9 (a.u1 - star a.u1) := by
  show pi1 a + Matrix.single s9 s9 (a.u1 - star a.u1) - pi1 a
    = Matrix.single s9 s9 (a.u1 - star a.u1)
  rw [add_sub_cancel_left]

/-- **The group read-back**: `piDouble` is `piFlip` plus
the e_R step `(piEFlip − pi1)` — the two flips are
independent and their singles are disjoint, so the
`(ℤ/2)²` toggle group closes: `piDouble = piFlip +
(piEFlip − pi1)`. -/
theorem piDouble_eq_piFlip_add_piEFlip_sub (a : AF) :
    piDouble a
      = ThetLogos.HyperchargeForcing.piFlip a
        + (piEFlip a - pi1 a) := by
  rw [piEFlip_sub_pi1]
  exact piDouble_eq_piFlip_add a

/-! ## Seat read-backs and distinctness -/

/-- At seat 9, `piEFlip` acts by `a.u1` (π₁'s `star a.u1`
plus the un-conjugation single). -/
theorem piEFlip_s9 (a : AF) : piEFlip a s9 s9 = a.u1 := by
  have hpi : pi1 a s9 s9 = star a.u1 := pi1_entry_eR a
  show (pi1 a + Matrix.single s9 s9 (a.u1 - star a.u1)) s9 s9
    = a.u1
  rw [Matrix.add_apply, Matrix.single_apply_same, hpi]
  ring

/-- At seat 8, `piEFlip` is π₁: it acts by `a.u1` (the s9
single does not touch seat 8). -/
theorem piEFlip_s8 (a : AF) : piEFlip a s8 s8 = a.u1 := by
  have hpi : pi1 a s8 s8 = a.u1 := pi1_entry_nuR a
  show (pi1 a + Matrix.single s9 s9 (a.u1 - star a.u1)) s8 s8
    = a.u1
  rw [Matrix.add_apply, Matrix.single_apply,
    if_neg (by decide : ¬ (s9 = s8 ∧ s9 = s8)), add_zero, hpi]

/-- At seat 8, `piFlip` acts by `star a.u1` (its defining
flip). -/
theorem piFlip_s8 (a : AF) :
    ThetLogos.HyperchargeForcing.piFlip a s8 s8
      = star a.u1 := by
  rw [piFlip_apply, if_pos ⟨rfl, rfl⟩]

/-- At seat 8, `piDouble` acts by `star a.u1` (it carries
piFlip's seat-8 flip; the s9 single does not touch
seat 8). -/
theorem piDouble_s8 (a : AF) :
    piDouble a s8 s8 = star a.u1 := by
  rw [piDouble_eq_piFlip_add]
  show (ThetLogos.HyperchargeForcing.piFlip a
      + Matrix.single s9 s9 (a.u1 - star a.u1)) s8 s8
    = star a.u1
  rw [Matrix.add_apply, Matrix.single_apply,
    if_neg (by decide : ¬ (s9 = s8 ∧ s9 = s8)), add_zero,
    piFlip_s8]

/-- Distinctness: `piEFlip ≠ pi1`, witnessed at seat 9 at
`u1Gen 1 0` (`a.u1 = i` vs π₁'s `star i = −i`). -/
theorem piEFlip_ne_pi1 : piEFlip ≠ pi1 := by
  intro h
  have hentry := congrArg
    (fun M : Matrix (Fin 32) (Fin 32) ℂ => M s9 s9)
    (congrFun h (u1Gen 1 0))
  rw [piEFlip_s9, pi1_entry_eR] at hentry
  have hu1 : (u1Gen 1 0).u1
      = ((1 : ℤ) : ℂ) * Complex.I := rfl
  rw [hu1, hstar] at hentry
  norm_num [Complex.ext_iff] at hentry

/-- Distinctness: `piEFlip ≠ piFlip`, witnessed at seat 8
at `u1Gen 1 0` (`a.u1 = i` vs piFlip's `star i = −i`). -/
theorem piEFlip_ne_piFlip :
    piEFlip ≠ ThetLogos.HyperchargeForcing.piFlip := by
  intro h
  have hentry := congrArg
    (fun M : Matrix (Fin 32) (Fin 32) ℂ => M s8 s8)
    (congrFun h (u1Gen 1 0))
  rw [piEFlip_s8, piFlip_s8] at hentry
  have hu1 : (u1Gen 1 0).u1
      = ((1 : ℤ) : ℂ) * Complex.I := rfl
  rw [hu1, hstar] at hentry
  norm_num [Complex.ext_iff] at hentry

/-- Distinctness: `piEFlip ≠ piDouble`, witnessed at
seat 8 at `u1Gen 1 0` (`a.u1 = i` vs piDouble's
`star i = −i`). -/
theorem piEFlip_ne_piDouble : piEFlip ≠ piDouble := by
  intro h
  have hentry := congrArg
    (fun M : Matrix (Fin 32) (Fin 32) ℂ => M s8 s8)
    (congrFun h (u1Gen 1 0))
  rw [piEFlip_s8, piDouble_s8] at hentry
  have hu1 : (u1Gen 1 0).u1
      = ((1 : ℤ) : ℂ) * Complex.I := rfl
  rw [hu1, hstar] at hentry
  norm_num [Complex.ext_iff] at hentry

/-! ## piEFlip fails C3 -/

/-- The γ-weighted trace of the seat-9 single:
`gammaF s9 s9 = -1` picks out exactly the `single` entry
(the s9 analogue of the landed `trace_gammaF_single_s8`). -/
theorem trace_gammaF_single_s9 (c : ℂ) :
    Matrix.trace (gammaF * Matrix.single s9 s9 c) = -c := by
  rw [trace_gammaF_mul]
  have h9 : gammaF s9 s9 = -1 := gammaF_s9
  rw [Finset.sum_eq_single s9]
  · rw [h9]
    simp
  · intro i _ hi
    have hne : ¬ (s9 = i ∧ s9 = i) := fun h => hi h.1.symm
    have hsingle : Matrix.single s9 s9 c i i = 0 := by
      simp only [Matrix.single_apply, hne, ite_false]
    rw [hsingle, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- **The γ-weighted trace of `piEFlip` at the generator
is exactly `−2α·i`**: π₁'s landed trace `0` plus the s9
single's contribution `(−1)·(α·i − star (α·i)) = −2α·i` —
the e_R half of piDouble's landed cancellation, standing
alone. -/
theorem trace_gammaF_piEFlip_u1Gen (α β : ℤ) :
    Matrix.trace (gammaF * piEFlip (u1Gen α β))
      = -2 * (α : ℂ) * Complex.I := by
  have hu1 : (u1Gen α β).u1 = (α : ℂ) * Complex.I := rfl
  have hs : star (u1Gen α β).u1 = -((α : ℂ) * Complex.I) := by
    rw [hu1]
    simp
  rw [piEFlip_unfold, mul_add, Matrix.trace_add,
    trace_gammaF_pi1_u1Gen, trace_gammaF_single_s9, hs, hu1]
  ring

/-- **`¬ C3 piEFlip`**, witnessed at `(α, β) = (1, 0)`,
where the trace is `−2·i ≠ 0`. -/
theorem not_c3_piEFlip : ¬ C3 piEFlip := by
  intro h
  have h10 := h 1 0
  rw [trace_gammaF_piEFlip_u1Gen] at h10
  norm_num [Complex.ext_iff] at h10

/-- **First exclusion**: `piEFlip` lies outside the
strengthened family, by `C3` alone (C3 is a conjunct of
`DialOneStrengthenedFam`). No Base analysis. -/
theorem not_strengthened_piEFlip :
    ¬ DialOneStrengthenedFam piEFlip :=
  fun h => not_c3_piEFlip h.2.1

/-! ## piEFlip fails FeR independently -/

/-- **The e_R γ-trace of `piEFlip` at the generator is
exactly `−2α·i`**: π₁'s FeR sub-sums are `(0, 0)` (landed
ℤ shadows), and the s9 single — living exactly on the
FeR seats `{9, 25}` — contributes
`gammaF s9 s9 · eRProj s9 s9 · (α·i − star (α·i))
= (−1)·1·(2α·i)`. The same value as piDouble's landed
FeR trace: piDouble's s8 single vanishes against
`eRProj` (landed). -/
theorem trace_feR_piEFlip (α β : ℤ) :
    Matrix.trace (gammaF * eRProj * piEFlip (u1Gen α β))
      = -2 * (α : ℂ) * Complex.I := by
  have hdec : piEFlip (u1Gen α β)
      = pi1 (u1Gen α β)
        + Matrix.single s9 s9
          ((α : ℂ) * Complex.I
            - star ((α : ℂ) * Complex.I)) := rfl
  rw [hdec, Matrix.mul_add, Matrix.trace_add,
    trace_gammaF_proj_pi1 eRProj eRInd eRProj_diag_mul
      eRProj_diag,
    trace_gammaF_proj_single]
  have hA : (∑ i : Fin 32,
      gammaVal i.val * eRInd i.val * pi1AVal i.val) = 0 := by
    decide
  have hB : (∑ i : Fin 32,
      gammaVal i.val * eRInd i.val * pi1BVal i.val) = 0 := by
    decide
  have p9 : eRProj s9 s9 = 1 := by
    have h := eRProj_diag s9
    simpa [eRInd] using h
  rw [hA, hB]
  simp only [Int.cast_zero, zero_mul, add_zero]
  rw [gammaF_s9, p9, hstar α]
  ring

/-- **`¬ FeR piEFlip`**, witnessed at `(α, β) = (1, 0)`,
where the trace is `−2·i ≠ 0`. -/
theorem not_feR_piEFlip : ¬ FeR piEFlip := by
  intro h
  have h10 := h 1 0
  rw [trace_feR_piEFlip] at h10
  norm_num [Complex.ext_iff] at h10

/-- **Second, independent exclusion**: `piEFlip` lies
outside the strengthened family, by `FeR` alone (FeR is
a conjunct of the family, hence of
`DialOneStrengthenedFam`). No Base analysis. -/
theorem not_strengthened_piEFlip_feR :
    ¬ DialOneStrengthenedFam piEFlip :=
  fun h => not_feR_piEFlip h.2.2.2.2

/-! ## The chapter headline -/

open Classical in
/-- **The lepton chapter of Grade T**: over the
four-element lepton toggle set `{pi1, piFlip, piEFlip,
piDouble}` — the `(ℤ/2)²` of the ν_R and e_R flips —
membership in the strengthened family
(`DialOneStrengthenedFam`: base ∧ C3 ∧ clean family)
holds exactly at π₁. Assembled from landed parts only:
pi1 in (`strengthened_pi1`, landed); piFlip out by C3
(`not_strengthened_piFlip`, landed); piDouble out by
FeR (`not_strengthened_piDouble`, landed); piEFlip out
by C3 and independently by FeR (this brick). **The
chapter closes at the C3/family level — no Base
analysis anywhere.** -/
theorem lepton_toggle_membership :
    ∀ π ∈ ({pi1, ThetLogos.HyperchargeForcing.piFlip, piEFlip,
        piDouble} : Finset (AF → Matrix (Fin 32) (Fin 32) ℂ)),
      DialOneStrengthenedFam π ↔ π = pi1 := by
  intro π hπ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hπ
  rcases hπ with rfl | rfl | rfl | rfl
  · exact ⟨fun _ => rfl, fun _ => strengthened_pi1⟩
  · exact ⟨fun h => (not_strengthened_piFlip h).elim,
      fun h => by rw [h]; exact strengthened_pi1⟩
  · exact ⟨fun h => (not_strengthened_piEFlip h).elim,
      fun h => by rw [h]; exact strengthened_pi1⟩
  · exact ⟨fun h => (not_strengthened_piDouble h).elim,
      fun h => by rw [h]; exact strengthened_pi1⟩

-- Axiom audit for the headline verdicts (expected:
-- [propext, Classical.choice, Quot.sound] throughout).
#print axioms trace_gammaF_piEFlip_u1Gen
#print axioms trace_feR_piEFlip
#print axioms not_strengthened_piEFlip
#print axioms not_strengthened_piEFlip_feR
#print axioms piDouble_eq_piFlip_add_piEFlip_sub
#print axioms lepton_toggle_membership

end ThetLogos.DialOneLeptonChapter
