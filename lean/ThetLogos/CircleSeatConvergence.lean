/-
# MQ3-5: pointwise convergence at the circle seat

Rung 5 of the M-Q3 continuum ladder
(`~/workspace/your_files/m-q3-scope-2026-11-08.md` §1 + §4):
clause (4)'s discharge at the circle seat
`(haarProb Circle, circleRep)` along MQ3-4's exhibited
trajectory `trajFloorU1` (`βt N = 1/(N+1)^4`).

**What is proved.** `CorrelationsConvergePointwise
(haarProb Circle) circleRep trajFloorU1 limitSystemMQ35`
— the pin's convergence clause **verbatim**, for every `k`
and every insertion family, for the explicitly exhibited
limit system `limitSystemMQ35` below.

**Faced tension (from MQ3-4).** The floored trajectory runs
to `β = 0` — the degenerate end. The exhibited `S` is
therefore the β = 0 (free / product-Haar) system, computed
exactly: an insertion family is keyed by its ℤ-walk
occurrences `(pos, offset, μ, sign)` (§1), and `S k c = 1`
iff every key's net sign exponent is `0`, else `0`. This is
not an `S` chosen for convenience: §2 proves the finite
correlations' β = 0 values equal `S k c` for all large `N`
(monomial factorization over links + stabilization of the
link-equality pattern), and §3 proves
`‖⟨F_N⟩_{βt N} − ⟨F_N⟩₀‖ → 0` by a near/far weight
comparison (the plaquettes sharing a link with the
observable's support are bounded in number, independently
of `N`, by the landed perimeter count; the far weight is
exactly independent of the observable). §4 assembles.

**K-MQ3-CONV: does NOT fire** — the finite correlations
converge pointwise along `trajFloorU1`, to the exhibited
`S`.

**VERDICT (2026-11-09): LANDED FULL — 57 strict.**
Full-file `lake env lean` check green; targeted
`lake build ThetLogos.CircleSeatConvergence` green;
`#print axioms correlationsConvergePointwise_trajFloorU1`
= `[propext, Classical.choice, Quot.sound]`; zero sorries.
The design is frozen in `STATUS-MQ35.md` §1.

**NO CLAIM** — parts of any Clay statement closed by this
module: 0. Dials: 0/4; Dial 3 = 0 (no dial moves before
MQ3-6).
-/

import ThetLogos.TrajectoryFloorU1
import ThetLogos.LatticeGramSeries

/-! **Import-clash note (faced, 2026-11-08).** This module
does NOT import `ThetLogos.LatticeAnalyticity`: that module
and `ThetLogos.LatticeVacuumSimple` (in MQ3-4's chain via
`LatticeHdenSeat`) both declare `ThetLogos.actionBound`
(with different signatures), so Analyticity and the MQ3-4
chain cannot be co-imported into one environment
(compiler-verified: "environment already contains
'ThetLogos.actionBound' from ThetLogos.LatticeVacuumSimple").
The five elementary Analyticity devices this rung needs
(the circle Wilson-loop coercion, the action-density sum
form, plaquette-density dependence/measurability, and the
perimeter count of sharing plaquettes) are reproved under
local names in §2.0 below, from `LatticeGauge` /
`LatticeCorrelations` directly. -/

namespace ThetLogos

open MeasureTheory Finset

section CircleSeatConvergence

/-! ## §1. The ℤ-walk, the finite-N walk, and the exhibited `S` -/

/-- The site a step starting at the ℤ-offset `o` ends at:
the ℤ-lift of `stepSite`. -/
def zSiteStep (o : Fin 4 → ℤ) : Step → Fin 4 → ℤ
  | Step.fwd μ => o + Pi.single μ 1
  | Step.bwd μ => o - Pi.single μ 1

/-- The link a step starting at the ℤ-offset `o` reads,
and its sign: `fwd μ` reads `(o, μ)` with sign `+1`;
`bwd μ` reads `(o − e_μ, μ)` with sign `−1` (mirroring
`stepFactor` / `loopLinks`: a backward step reads the link
`((σ μ).symm s, μ)` with the inverse factor). -/
def zOcc (o : Fin 4 → ℤ) : Step → (Fin 4 → ℤ) × Fin 4 × ℤ
  | Step.fwd μ => (o, μ, 1)
  | Step.bwd μ => (o - Pi.single μ 1, μ, -1)

/-- The occurrence list of a step list walked on `ℤ^4`
from the offset `o`: one `((offset, μ), sign)` triple per
step, in order. -/
def walkOccZ (o : Fin 4 → ℤ) : List Step → List ((Fin 4 → ℤ) × Fin 4 × ℤ)
  | [] => []
  | st :: t => zOcc o st :: walkOccZ (zSiteStep o st) t

theorem walkOccZ_length (o : Fin 4 → ℤ) (steps : List Step) :
    (walkOccZ o steps).length = steps.length := by
  induction steps generalizing o with
  | nil => rfl
  | cons st t ih => simp [walkOccZ, ih]

/-- The occurrence list of a step list walked on the
level-`N` torus from the site `s`: one `((site, μ), sign)`
triple per step, in order, with the same sign convention
as `walkOccZ`. -/
def walkOccN (N : ℕ) (s : Fin 4 → ZMod N) :
    List Step → List ((Fin 4 → ZMod N) × Fin 4 × ℤ)
  | [] => []
  | st :: t =>
    (match st with
     | Step.fwd μ => (s, μ, 1)
     | Step.bwd μ => ((torusShift N μ).symm s, μ, -1)) ::
      walkOccN N (stepSite (torusShift N) s st) t

theorem walkOccN_length (N : ℕ) (s : Fin 4 → ZMod N) (steps : List Step) :
    (walkOccN N s steps).length = steps.length := by
  induction steps generalizing s with
  | nil => rfl
  | cons st t ih => simp [walkOccN, ih]

/-- An occurrence index of a family `c`: an insertion
together with a step position within it. -/
abbrev OccIdx (k : ℕ) (c : Fin k → LoopInsertion) :=
  Σ i : Fin k, Fin (c i).steps.length

/-- The ℤ-occurrence at an occurrence index. -/
def occZ {k : ℕ} (c : Fin k → LoopInsertion) (idx : OccIdx k c) :
    (Fin 4 → ℤ) × Fin 4 × ℤ :=
  (walkOccZ 0 (c idx.1).steps).get
    (Fin.cast (walkOccZ_length 0 (c idx.1).steps).symm idx.2)

/-- The limit key of an occurrence: the insertion's
rational position, the ℤ-offset, and the direction. -/
def occKey {k : ℕ} (c : Fin k → LoopInsertion) (idx : OccIdx k c) :
    (Fin 4 → ℚ) × (Fin 4 → ℤ) × Fin 4 :=
  ((c idx.1).pos, (occZ c idx).1, (occZ c idx).2.1)

/-- The sign of an occurrence. -/
def occSign {k : ℕ} (c : Fin k → LoopInsertion) (idx : OccIdx k c) :
    ℤ :=
  (occZ c idx).2.2

/-- The key exponent of a limit key: the sum of the signs
of all occurrences carrying that key. -/
def keyExp {k : ℕ} (c : Fin k → LoopInsertion)
    (K : (Fin 4 → ℚ) × (Fin 4 → ℤ) × Fin 4) : ℤ :=
  ∑ idx ∈ Finset.univ.filter (fun idx => occKey c idx = K), occSign c idx

/-- **The exhibited limit system (MQ3-5).** The β = 0
(free / product-Haar) correlation values, in owned
vocabulary: `1` if every limit key's net sign exponent
vanishes, else `0`. -/
def limitSystemMQ35 : LimitCorrelationSystem :=
  fun k c => if (∀ idx, keyExp c (occKey c idx) = 0) then 1 else 0

/-! ## §2. The finite-N walk reads the ℤ-walk

The occurrence at step position `n` of the level-`N` walk
from `rescaledSite N pos` has the same sign and direction
as the ℤ-walk occurrence at the same position, and its site
is `rescaledSite N pos + (ℤ-offset cast to `ZMod N`)`. -/

/-- Casting a ℤ single-step vector to `ZMod N` gives the
`ZMod N` single-step vector, coordinatewise. -/
theorem cast_single_zmod (N : ℕ) (μ ν : Fin 4) :
    (((Pi.single μ (1 : ℤ) : Fin 4 → ℤ) ν : ℤ) : ZMod N)
      = (Pi.single μ (1 : ZMod N) : Fin 4 → ZMod N) ν := by
  by_cases h : ν = μ <;> simp [Pi.single_apply, h]

/-- The backward torus shift subtracts the single-step
vector: `((torusShift N μ).symm s) ν = s ν − e_μ ν`. -/
theorem torusShift_symm_apply (N : ℕ) (μ : Fin 4)
    (s : Fin 4 → ZMod N) (ν : Fin 4) :
    (torusShift N μ).symm s ν = s ν - (Pi.single μ (1 : ZMod N) : Fin 4 → ZMod N) ν := by
  have h2 : torusShift N μ (s - (Pi.single μ (1 : ZMod N) : Fin 4 → ZMod N))
      = s := by
    funext κ
    rw [torusShift_apply]
    simp only [Pi.add_apply, Pi.sub_apply]
    exact add_sub_cancel _ _
  have h : (torusShift N μ).symm s
      = s - (Pi.single μ (1 : ZMod N) : Fin 4 → ZMod N) := by
    rw [Equiv.symm_apply_eq]
    exact h2.symm
  rw [h]
  rfl

/-- **Walk correspondence.** If the starting site `s`
reads `base + (o cast)` coordinatewise, then at every step
position `n` the level-`N` occurrence and the ℤ occurrence
agree in sign and direction, and the level-`N` site reads
`base + (ℤ-offset cast)` coordinatewise. -/
theorem walkOccN_get (N : ℕ) (base : Fin 4 → ZMod N) :
    ∀ (o : Fin 4 → ℤ) (s : Fin 4 → ZMod N),
      (∀ ν, s ν = base ν + (o ν : ZMod N)) →
      ∀ (steps : List Step) (n : ℕ) (hn : n < steps.length),
        ((walkOccN N s steps).get ⟨n, by
            rw [walkOccN_length]; exact hn⟩).2.2
          = ((walkOccZ o steps).get ⟨n, by
            rw [walkOccZ_length]; exact hn⟩).2.2
        ∧ ((walkOccN N s steps).get ⟨n, by
            rw [walkOccN_length]; exact hn⟩).2.1
          = ((walkOccZ o steps).get ⟨n, by
            rw [walkOccZ_length]; exact hn⟩).2.1
        ∧ ∀ ν, ((walkOccN N s steps).get ⟨n, by
            rw [walkOccN_length]; exact hn⟩).1 ν
          = base ν + (((walkOccZ o steps).get ⟨n, by
            rw [walkOccZ_length]; exact hn⟩).1 ν : ZMod N) := by
  intro o s hs steps
  induction steps generalizing o s with
  | nil => intro n hn; exact absurd hn (by simp)
  | cons st t ih =>
    intro n hn
    cases st with
    | fwd μ =>
      have hs' : ∀ ν, stepSite (torusShift N) s (Step.fwd μ) ν
          = base ν + ((zSiteStep o (Step.fwd μ)) ν : ZMod N) := by
        intro ν
        show (torusShift N μ s) ν = base ν + ((o + (Pi.single μ (1 : ℤ) : Fin 4 → ℤ)) ν : ZMod N)
        rw [torusShift_apply]
        simp only [Pi.add_apply]
        rw [hs ν, Int.cast_add, cast_single_zmod]
        ring
      cases n with
      | zero =>
        refine ⟨rfl, rfl, fun ν => hs ν⟩
      | succ m =>
        have hm : m < t.length := Nat.lt_of_succ_lt_succ hn
        have h := ih (zSiteStep o (Step.fwd μ))
          (stepSite (torusShift N) s (Step.fwd μ)) hs' m hm
        simpa [walkOccN, walkOccZ, List.get_cons_succ] using h
    | bwd μ =>
      have hs' : ∀ ν, stepSite (torusShift N) s (Step.bwd μ) ν
          = base ν + ((zSiteStep o (Step.bwd μ)) ν : ZMod N) := by
        intro ν
        show (torusShift N μ).symm s ν
          = base ν + ((o - (Pi.single μ (1 : ℤ) : Fin 4 → ℤ)) ν : ZMod N)
        rw [torusShift_symm_apply, hs ν]
        simp only [Pi.sub_apply]
        rw [Int.cast_sub, cast_single_zmod]
        ring
      cases n with
      | zero =>
        refine ⟨rfl, rfl, fun ν => ?_⟩
        show (torusShift N μ).symm s ν
          = base ν + (((zOcc o (Step.bwd μ)).1) ν : ZMod N)
        rw [torusShift_symm_apply, hs ν]
        show base ν + (o ν : ZMod N)
            - (Pi.single μ (1 : ZMod N) : Fin 4 → ZMod N) ν
          = base ν + (((o - (Pi.single μ (1 : ℤ) : Fin 4 → ℤ)) ν : ℤ) : ZMod N)
        simp only [Pi.sub_apply]
        rw [Int.cast_sub, cast_single_zmod]
        ring
      | succ m =>
        have hm : m < t.length := Nat.lt_of_succ_lt_succ hn
        have h := ih (zSiteStep o (Step.bwd μ))
          (stepSite (torusShift N) s (Step.bwd μ)) hs' m hm
        simpa [walkOccN, walkOccZ, List.get_cons_succ] using h

/-- The finite-N occurrence at an occurrence index. -/
def occN {k : ℕ} (c : Fin k → LoopInsertion) (N : ℕ) (idx : OccIdx k c) :
    (Fin 4 → ZMod N) × Fin 4 × ℤ :=
  (walkOccN N (rescaledSite N (c idx.1).pos) (c idx.1).steps).get
    (Fin.cast (walkOccN_length N _ (c idx.1).steps).symm idx.2)

/-- The link read by a finite-N occurrence. -/
def occLinkN {k : ℕ} (c : Fin k → LoopInsertion) (N : ℕ)
    (idx : OccIdx k c) : Link (Fin 4 → ZMod N) :=
  ((occN c N idx).1, (occN c N idx).2.1)

/-- **Occurrence correspondence at the seat.** The finite-N
occurrence at `idx` has the ℤ-occurrence's sign and
direction, and its site is the rescaled site plus the
ℤ-offset cast to `ZMod N`. -/
theorem occN_eq {k : ℕ} (c : Fin k → LoopInsertion) (N : ℕ)
    (idx : OccIdx k c) :
    (occN c N idx).2.2 = occSign c idx
    ∧ (occN c N idx).2.1 = (occZ c idx).2.1
    ∧ ∀ ν, (occN c N idx).1 ν
        = rescaledSite N (c idx.1).pos ν + ((occZ c idx).1 ν : ZMod N) := by
  have h := walkOccN_get N (rescaledSite N (c idx.1).pos) 0
    (rescaledSite N (c idx.1).pos)
    (fun ν => by simp) (c idx.1).steps idx.2.1 idx.2.2
  exact h

/-! ## §2.0. Local devices (the Analyticity five, reproved)

Per the import-clash note at the head of this module, the
elementary devices of `LatticeAnalyticity` used below are
reproved here under local names, from `LatticeGauge` /
`LatticeCorrelations` directly. -/

/-- A circle Wilson loop is the coercion of its loop
product (local form of `wilsonLoop_circleRep`). -/
theorem wilsonLoop_circleRep_MQ35 (N : ℕ) [NeZero N]
    (U : Config (Fin 4 → ZMod N) Circle) (s : Fin 4 → ZMod N)
    (steps : List Step) :
    wilsonLoop (torusShift N) circleRep U s steps
      = ((loopProd (torusShift N) U s steps : Circle) : ℂ) := by
  have h : ∀ g : Circle, Matrix.trace (repMatrix circleRep g) = (g : ℂ) := by
    intro g
    have hr : repMatrix circleRep g = Matrix.of (fun _ _ => (g : ℂ)) := rfl
    rw [hr, Matrix.trace]
    simp [Matrix.diag, Fin.sum_univ_one, Matrix.of_apply]
  unfold wilsonLoop
  exact h _

/-- The action density at the circle seat, as a plaquette
sum (local form of `actionDensity`). -/
noncomputable def actDen (N : ℕ) [NeZero N] (U : Config (Fin 4 → ZMod N) Circle) : ℝ :=
  ∑ x : Fin 4 → ZMod N, ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ,
    plaquetteDensity (torusShift N) circleRep U x μ ν

theorem wilsonAction_eq_actDen (N : ℕ) [NeZero N] (β : ℝ)
    (U : Config (Fin 4 → ZMod N) Circle) :
    wilsonAction (torusShift N) circleRep β U = β * actDen N U :=
  rfl

theorem measurable_actDen (N : ℕ) [NeZero N] :
    Measurable (actDen N) := by
  have h : actDen N = fun U => wilsonAction (torusShift N) circleRep 1 U := by
    funext U
    rw [wilsonAction_eq_actDen]
    ring
  rw [h]
  exact measurable_wilsonAction (torusShift N) circleRep
    circleRep_continuous 1

/-- The action density as a sum over unordered plaquette
triples (local form of `actionDensity_eq_sum_triples`). -/
theorem actDen_eq_sum_triples (N : ℕ) [NeZero N]
    (U : Config (Fin 4 → ZMod N) Circle) :
    actDen N U
      = ∑ q ∈ Finset.univ.filter
          (fun q : (Fin 4 → ZMod N) × Fin 4 × Fin 4 => q.2.1 < q.2.2),
          plaquetteDensity (torusShift N) circleRep U q.1 q.2.1 q.2.2 := by
  have hIoi : ∀ μ : Fin 4, Finset.Ioi μ
      = Finset.univ.filter (fun ν : Fin 4 => μ < ν) := fun μ => by
    ext ν
    simp [Finset.mem_Ioi]
  unfold actDen
  simp only [hIoi, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Fintype.sum_prod_type]

/-- The link support of a plaquette (local form of
`plaquetteLinks`). -/
def plaqLinks (N : ℕ) (x : Fin 4 → ZMod N) (μ ν : Fin 4) :
    Finset (Link (Fin 4 → ZMod N)) :=
  loopLinks (torusShift N) x (plaquetteSteps μ ν)

theorem plaqLinks_eq (N : ℕ) (x : Fin 4 → ZMod N) (μ ν : Fin 4) :
    plaqLinks N x μ ν
      = {(x, μ), ((torusShift N μ) x, ν), ((torusShift N ν) x, μ), (x, ν)} := by
  have h1 : (torusShift N μ).symm ((torusShift N ν) ((torusShift N μ) x))
      = (torusShift N ν) x := by
    rw [← torusShift_comm N μ ν x]
    exact Equiv.symm_apply_apply (torusShift N μ) ((torusShift N ν) x)
  simp [plaqLinks, loopLinks, plaquetteSteps, h1]

/-- A plaquette density, as a complex observable, depends
only on the plaquette's links (local form of
`plaquetteDensity_dependsOnlyOn`, at `d = 1`). -/
theorem plaquetteDensity_dependsOnlyOn_MQ35 (N : ℕ) [NeZero N]
    (y : Fin 4 → ZMod N) (κ₁ κ₂ : Fin 4) :
    DependsOnlyOn
      (fun U => (plaquetteDensity (torusShift N) circleRep U y κ₁ κ₂ : ℂ))
      (plaqLinks N y κ₁ κ₂) := by
  obtain ⟨fW, hfW⟩ := wilsonLoop_dependsOnlyOn (torusShift N) circleRep
    y (plaquetteSteps κ₁ κ₂)
  refine ⟨fun w => (1 : ℂ) - ((fW w).re : ℂ), fun U => ?_⟩
  have hU : wilsonLoop (torusShift N) circleRep U y (plaquetteSteps κ₁ κ₂)
      = fW (fun ℓ : ↥(loopLinks (torusShift N) y (plaquetteSteps κ₁ κ₂))
          => U ℓ.1) := hfW U
  calc (plaquetteDensity (torusShift N) circleRep U y κ₁ κ₂ : ℂ)
      = (1 : ℂ) - ((wilsonLoop (torusShift N) circleRep U y
          (plaquetteSteps κ₁ κ₂)).re : ℂ) := by
        unfold plaquetteDensity wilsonLoop
        rw [loopProd_plaquetteSteps (torusShift N) (torusShift_comm N)]
        push_cast
        ring
    _ = (1 : ℂ) - ((fW (fun ℓ : ↥(loopLinks (torusShift N) y
          (plaquetteSteps κ₁ κ₂)) => U ℓ.1)).re : ℂ) := by rw [hU]

/-- Plaquette densities are measurable complex observables
(local form of `measurable_plaquetteDensityC`, at `d = 1`). -/
theorem measurable_plaquetteDensityC_MQ35 (N : ℕ) [NeZero N]
    (y : Fin 4 → ZMod N) (κ₁ κ₂ : Fin 4) :
    Measurable (fun U => (plaquetteDensity (torusShift N) circleRep
      U y κ₁ κ₂ : ℂ)) := by
  have hfun : (fun U => (plaquetteDensity (torusShift N) circleRep
        U y κ₁ κ₂ : ℂ))
      = fun U => (1 : ℂ) - ((wilsonLoop (torusShift N) circleRep U y
          (plaquetteSteps κ₁ κ₂)).re : ℂ) := by
    funext U
    unfold plaquetteDensity wilsonLoop
    rw [loopProd_plaquetteSteps (torusShift N) (torusShift_comm N)]
    push_cast
    ring
  rw [hfun]
  exact measurable_const.sub
    (Complex.continuous_ofReal.measurable.comp
      (measurable_wilsonLoop_re (torusShift N) circleRep
        circleRep_continuous y (plaquetteSteps κ₁ κ₂)))

/-- Real plaquette densities are measurable. -/
theorem measurable_plaquetteDensity_MQ35 (N : ℕ) [NeZero N]
    (y : Fin 4 → ZMod N) (κ₁ κ₂ : Fin 4) :
    Measurable (fun U => plaquetteDensity (torusShift N) circleRep
      U y κ₁ κ₂) := by
  have heq : (fun U => plaquetteDensity (torusShift N) circleRep U y κ₁ κ₂)
      = fun U => ((plaquetteDensity (torusShift N) circleRep U y κ₁ κ₂
          : ℂ)).re :=
    funext fun U => (Complex.ofReal_re _).symm
  rw [heq]
  exact Complex.measurable_re.comp
    (measurable_plaquetteDensityC_MQ35 N y κ₁ κ₂)

/-- The plaquettes sharing at least one link with the
support `s` (local form of `sharingPlaquettes`). -/
def sharingMQ (N : ℕ) [NeZero N] (s : Finset (Link (Fin 4 → ZMod N))) :
    Finset ((Fin 4 → ZMod N) × Fin 4 × Fin 4) :=
  Finset.univ.filter (fun q : (Fin 4 → ZMod N) × Fin 4 × Fin 4 =>
    q.2.1 < q.2.2 ∧ (plaqLinks N q.1 q.2.1 q.2.2 ∩ s).Nonempty)

/-- Directions other than a given one: exactly three. -/
theorem card_filter_ne_MQ35 (a : Fin 4) :
    (Finset.univ.filter (fun b : Fin 4 => b ≠ a)).card = 3 := by
  have h : Finset.univ.filter (fun b : Fin 4 => b ≠ a)
      = Finset.univ \ {a} := by
    ext b
    simp
  rw [h, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
    Fintype.card_fin, Finset.card_singleton]

/-- The candidate plaquettes through a link: the four
slots, each with a free second direction (local form of
`candSet`). -/
def candSetMQ (N : ℕ) (ℓ : Link (Fin 4 → ZMod N)) :
    Finset ((Fin 4 → ZMod N) × Fin 4 × Fin 4) :=
  (Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
      (fun a => (ℓ.1, ℓ.2, a))
  ∪ (Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
      (fun a => ((torusShift N a).symm ℓ.1, a, ℓ.2))
  ∪ (Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
      (fun a => ((torusShift N a).symm ℓ.1, ℓ.2, a))
  ∪ (Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
      (fun a => (ℓ.1, a, ℓ.2))

/-- At most twelve plaquettes pass through a given link. -/
theorem card_candSetMQ_le (N : ℕ) (ℓ : Link (Fin 4 → ZMod N)) :
    (candSetMQ N ℓ).card ≤ 12 := by
  have hI : ∀ f : Fin 4 → (Fin 4 → ZMod N) × Fin 4 × Fin 4,
      ((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image f).card ≤ 3 :=
    fun f => (Finset.card_image_le).trans (le_of_eq (card_filter_ne_MQ35 ℓ.2))
  unfold candSetMQ
  calc ((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => (ℓ.1, ℓ.2, a))
        ∪ (Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => ((torusShift N a).symm ℓ.1, a, ℓ.2))
        ∪ (Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => ((torusShift N a).symm ℓ.1, ℓ.2, a))
        ∪ (Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => (ℓ.1, a, ℓ.2))).card
      ≤ (((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => (ℓ.1, ℓ.2, a))
        ∪ (Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => ((torusShift N a).symm ℓ.1, a, ℓ.2))
        ∪ (Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => ((torusShift N a).symm ℓ.1, ℓ.2, a))).card)
        + ((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => (ℓ.1, a, ℓ.2))).card := Finset.card_union_le _ _
    _ ≤ (((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => (ℓ.1, ℓ.2, a))
        ∪ (Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => ((torusShift N a).symm ℓ.1, a, ℓ.2))).card
        + ((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => ((torusShift N a).symm ℓ.1, ℓ.2, a))).card)
        + ((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => (ℓ.1, a, ℓ.2))).card :=
          add_le_add (Finset.card_union_le _ _) (le_refl _)
    _ ≤ (((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => (ℓ.1, ℓ.2, a))).card
        + ((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => ((torusShift N a).symm ℓ.1, a, ℓ.2))).card
        + ((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => ((torusShift N a).symm ℓ.1, ℓ.2, a))).card)
        + ((Finset.univ.filter (fun a : Fin 4 => a ≠ ℓ.2)).image
          (fun a => (ℓ.1, a, ℓ.2))).card :=
          add_le_add (add_le_add (Finset.card_union_le _ _) (le_refl _))
            (le_refl _)
    _ ≤ ((3 + 3) + 3) + 3 :=
          add_le_add (add_le_add (add_le_add (hI _) (hI _)) (hI _)) (hI _)
    _ = 12 := rfl

/-- Every plaquette through a link is among the
candidates. -/
theorem mem_candSetMQ_of_mem_plaqLinks (N : ℕ) [NeZero N]
    {y : Fin 4 → ZMod N} {κ ν : Fin 4} (hκν : κ ≠ ν)
    {ℓ : Link (Fin 4 → ZMod N)}
    (hℓ : ℓ ∈ plaqLinks N y κ ν) :
    (y, κ, ν) ∈ candSetMQ N ℓ := by
  rw [plaqLinks_eq N y κ ν] at hℓ
  have hA : ∀ a : Fin 4, a ≠ ℓ.2 → (ℓ.1, ℓ.2, a) ∈ candSetMQ N ℓ :=
    fun a ha => Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩)))
  have hB : ∀ a : Fin 4, a ≠ ℓ.2 → ((torusShift N a).symm ℓ.1, a, ℓ.2)
      ∈ candSetMQ N ℓ :=
    fun a ha => Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩)))
  have hC : ∀ a : Fin 4, a ≠ ℓ.2 → ((torusShift N a).symm ℓ.1, ℓ.2, a)
      ∈ candSetMQ N ℓ :=
    fun a ha => Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩))
  have hD : ∀ a : Fin 4, a ≠ ℓ.2 → (ℓ.1, a, ℓ.2) ∈ candSetMQ N ℓ :=
    fun a ha => Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩)
  rcases Finset.mem_insert.mp hℓ with h | hℓ
  · subst h
    exact hA ν (fun hh => hκν hh.symm)
  rcases Finset.mem_insert.mp hℓ with h | hℓ
  · subst h
    have hmem := hB κ hκν
    rw [Equiv.symm_apply_apply] at hmem
    exact hmem
  rcases Finset.mem_insert.mp hℓ with h | hℓ
  · subst h
    have hmem := hC ν (fun hh => hκν hh.symm)
    rw [Equiv.symm_apply_apply] at hmem
    exact hmem
  · have h : ℓ = (y, ν) := Finset.mem_singleton.mp hℓ
    subst h
    exact hD κ hκν

/-- **Perimeter counting (local form):** the plaquettes
sharing a link with a support `s` number at most `12·|s|`. -/
theorem card_sharingMQ_le (N : ℕ) [NeZero N]
    (s : Finset (Link (Fin 4 → ZMod N))) :
    (sharingMQ N s).card ≤ 12 * s.card := by
  refine le_trans (Finset.card_le_card ?_)
    (le_trans ((Finset.card_biUnion_le (s := s) (t := candSetMQ N))) ?_)
  · intro q hq
    simp only [sharingMQ, Finset.mem_filter, Finset.mem_univ, true_and]
      at hq
    obtain ⟨ℓ, hℓ⟩ := hq.2
    rw [Finset.mem_inter] at hℓ
    exact Finset.mem_biUnion.mpr ⟨ℓ, hℓ.2,
      mem_candSetMQ_of_mem_plaqLinks N (ne_of_lt hq.1) hℓ.1⟩
  · refine le_trans (Finset.sum_le_sum fun ℓ _ => card_candSetMQ_le N ℓ) ?_
    rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-! ## §2.1. The finite correlation is an occurrence monomial

At the circle seat a Wilson loop is the product, over the
walk's occurrences, of the link variables raised to their
signs. -/

/-- The loop product is the occurrence product (in
`Circle`). -/
theorem loopProd_eq_prod_occN (N : ℕ) [NeZero N]
    (U : Config (Fin 4 → ZMod N) Circle) (s : Fin 4 → ZMod N)
    (steps : List Step) :
    loopProd (torusShift N) U s steps
      = ((walkOccN N s steps).map
          fun occ => (U (occ.1, occ.2.1)) ^ occ.2.2).prod := by
  induction steps generalizing s with
  | nil => simp [walkOccN]
  | cons st t ih =>
    rw [loopProd_cons, ih]
    cases st with
    | fwd μ => simp [walkOccN, stepFactor]
    | bwd μ => simp [walkOccN, stepFactor]

/-- A circle Wilson loop is the occurrence product (in
`ℂ`). -/
theorem wilsonLoop_eq_prod_occN (N : ℕ) [NeZero N]
    (U : Config (Fin 4 → ZMod N) Circle) (s : Fin 4 → ZMod N)
    (steps : List Step) :
    wilsonLoop (torusShift N) circleRep U s steps
      = ((walkOccN N s steps).map
          fun occ => ((U (occ.1, occ.2.1) : ℂ)) ^ occ.2.2).prod := by
  induction steps generalizing s with
  | nil => simp [wilsonLoop_circleRep_MQ35, walkOccN]
  | cons st t ih =>
    have hsplit : wilsonLoop (torusShift N) circleRep U s (st :: t)
        = ((stepFactor (torusShift N) U s st : Circle) : ℂ)
          * wilsonLoop (torusShift N) circleRep U
              (stepSite (torusShift N) s st) t := by
      rw [wilsonLoop_circleRep_MQ35, loopProd_cons, Circle.coe_mul,
        ← wilsonLoop_circleRep_MQ35]
    rw [hsplit, ih]
    cases st with
    | fwd μ => simp [walkOccN, stepFactor]
    | bwd μ => simp [walkOccN, stepFactor, Circle.coe_inv, zpow_neg_one]

/-- A list product is the product over the list's index
type. -/
theorem list_prod_eq_prod_fin {α : Type*} (L : List α) (f : α → ℂ) :
    (L.map f).prod
      = ∏ n : Fin L.length, f (L.get n) := by
  rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]
  refine Finset.prod_congr rfl (fun n _ => ?_)
  congr 1

/-- **The family observable of the pin's finite
correlation**, named: the product of the insertions'
Wilson loops at their rescaled sites. -/
noncomputable def famObs {k : ℕ} (c : Fin k → LoopInsertion) (N : ℕ)
    [NeZero N] (U : Config (Fin 4 → ZMod N) Circle) : ℂ :=
  ∏ i : Fin k, wilsonLoop (torusShift N) circleRep U
    (rescaledSite N (c i).pos) (c i).steps

/-- The pin's finite correlation is the Gibbs expectation
of `famObs` (definitional). -/
theorem finiteCorrelation_eq_gibbsExpect_famObs {k : ℕ}
    (c : Fin k → LoopInsertion) (N : ℕ) [NeZero N] :
    finiteCorrelation (haarProb Circle) circleRep trajFloorU1 N k c
      = gibbsExpect (torusShift N) (haarProb Circle) circleRep
          (trajFloorU1 N) (fun U => famObs c N U) :=
  rfl

/-- A list product, reindexed to any equal length. -/
theorem list_prod_eq_prod_fin_cast {α : Type*} (L : List α) (m : ℕ)
    (h : L.length = m) (f : α → ℂ) :
    (L.map f).prod
      = ∏ n : Fin m, f (L.get (Fin.cast h.symm n)) := by
  subst h
  exact list_prod_eq_prod_fin L f

/-- **The family observable is the occurrence monomial:**
the product over all occurrence indices of the link
variables raised to their signs. -/
theorem famObs_eq_prod_occ {k : ℕ} (c : Fin k → LoopInsertion)
    (N : ℕ) [NeZero N] (U : Config (Fin 4 → ZMod N) Circle) :
    famObs c N U
      = ∏ idx : OccIdx k c, ((U (occLinkN c N idx) : ℂ)) ^ occSign c idx := by
  have hsig : ∏ idx : OccIdx k c, ((U (occLinkN c N idx) : ℂ)) ^ occSign c idx
      = ∏ i : Fin k, ∏ n : Fin (c i).steps.length,
          ((U (occLinkN c N ⟨i, n⟩) : ℂ)) ^ occSign c ⟨i, n⟩ :=
    Fintype.prod_sigma (fun idx => ((U (occLinkN c N idx) : ℂ)) ^ occSign c idx)
  rw [hsig]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [wilsonLoop_eq_prod_occN,
    list_prod_eq_prod_fin_cast _ _ (walkOccN_length N _ (c i).steps)]
  refine Finset.prod_congr rfl (fun n _ => ?_)
  rw [← (occN_eq c N ⟨i, n⟩).1]
  rfl

/-! ## §2.2. The β = 0 closed form

The product-Haar expectation of the occurrence monomial
factorizes over links; each link contributes its character
integral `∫ z^e = δ_{e0}`. -/

/-- Powers over a finset sum, on the circle. -/
theorem zpow_sum_circle {α : Type*} (s : Finset α) (f : α → ℤ)
    (z : Circle) :
    ∏ i ∈ s, z ^ f i = z ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

/-- The link exponent at level `N`: the sum of the signs
of all occurrences reading the link `ℓ`. -/
def linkExp {k : ℕ} (c : Fin k → LoopInsertion) (N : ℕ) [NeZero N]
    (ℓ : Link (Fin 4 → ZMod N)) : ℤ :=
  ∑ idx ∈ Finset.univ.filter (fun idx => occLinkN c N idx = ℓ),
    occSign c idx

/-- **β = 0 closed form.** The product-Haar expectation of
the family observable is the product over links of the
character selectors: `1` iff every link exponent vanishes,
else `0`. -/
theorem gibbsExpect_zero_famObs {k : ℕ} (c : Fin k → LoopInsertion)
    (N : ℕ) [NeZero N] :
    gibbsExpect (torusShift N) (haarProb Circle) circleRep 0
        (fun U => famObs c N U)
      = ∏ ℓ : Link (Fin 4 → ZMod N),
          (if linkExp c N ℓ = 0 then (1 : ℂ) else 0) := by
  have hF : ∀ U : Config (Fin 4 → ZMod N) Circle,
      famObs c N U = ∏ ℓ : Link (Fin 4 → ZMod N),
        ((U ℓ : ℂ)) ^ linkExp c N ℓ := by
    intro U
    rw [famObs_eq_prod_occ,
      ← Finset.prod_fiberwise_of_maps_to (s := Finset.univ)
        (t := Finset.univ) (g := occLinkN c N)
        (fun idx _ => Finset.mem_univ _)
        (fun idx => ((U (occLinkN c N idx) : ℂ)) ^ occSign c idx)]
    refine Finset.prod_congr rfl (fun ℓ _ => ?_)
    have hcirc : ∏ idx ∈ Finset.univ.filter
          (fun idx => occLinkN c N idx = ℓ),
          ((U (occLinkN c N idx) : ℂ)) ^ occSign c idx
        = ((∏ idx ∈ Finset.univ.filter
            (fun idx => occLinkN c N idx = ℓ),
            (U ℓ) ^ occSign c idx : Circle) : ℂ) := by
      rw [coe_prod_circle]
      refine Finset.prod_congr rfl (fun idx hidx => ?_)
      rw [Finset.mem_filter] at hidx
      rw [coe_zpow_circle, hidx.2]
    rw [hcirc]
    show ((∏ idx ∈ Finset.univ.filter (fun idx => occLinkN c N idx = ℓ),
        (U ℓ) ^ occSign c idx : Circle) : ℂ)
      = ((U ℓ : ℂ)) ^ linkExp c N ℓ
    rw [zpow_sum_circle, coe_zpow_circle]
    rfl
  rw [gibbsExpect_zero, integral_congr_ae (ae_of_all _ hF)]
  show (∫ U : Config (Fin 4 → ZMod N) Circle,
      ∏ ℓ : Link (Fin 4 → ZMod N), ((U ℓ : ℂ)) ^ linkExp c N ℓ
      ∂(Measure.pi fun _ : Link (Fin 4 → ZMod N) => haarProb Circle))
    = ∏ ℓ : Link (Fin 4 → ZMod N),
        (if linkExp c N ℓ = 0 then (1 : ℂ) else 0)
  rw [MeasureTheory.integral_fintype_prod_eq_prod
    (fun ℓ (z : Circle) => ((z : ℂ)) ^ linkExp c N ℓ)]
  refine Finset.prod_congr rfl (fun ℓ _ => ?_)
  rw [integral_congr_ae
    (ae_of_all _ (fun w => (coe_zpow_circle w (linkExp c N ℓ)).symm)),
    integral_circle_zpow_haarProb]

/-! ## §2.3. Stabilization of the link-equality pattern

Two occurrences share a finite-`N` link iff they share a
limit key, for all large `N`. The coordinate content: for
rational positions `x, y ∈ [0, 1)` and integer offsets
`p, q`, the congruence `⌊Nx⌋ + p ≡ ⌊Ny⌋ + q (mod N)` holds
for all large `N` iff `x = y ∧ p = q` — when `x ≠ y` the
floor difference tracks `N(x−y)` with `|x−y| ∈ (0, 1)`, so
no multiple of `N` can meet it once
`N > (1 + |p − q|) / min(|x−y|, 1 − |x−y|)`. -/

open Filter in
/-- **Coordinate stabilization.** -/
theorem coord_eventually {x y : ℚ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) (p q : ℤ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ((⌊(N : ℚ) * x⌋₊ : ℤ) + p) ≡ ((⌊(N : ℚ) * y⌋₊ : ℤ) + q)
        [ZMOD N] ↔ (x = y ∧ p = q) := by
  by_cases hxy : x = y
  · subst hxy
    refine Filter.eventually_atTop.2 ⟨(p - q).natAbs + 1, fun N hN => ?_⟩
    constructor
    · intro hcong
      rw [Int.modEq_iff_dvd] at hcong
      have hD : ((⌊(N : ℚ) * x⌋₊ : ℤ) + q) - ((⌊(N : ℚ) * x⌋₊ : ℤ) + p)
          = q - p := by ring
      rw [hD] at hcong
      refine ⟨rfl, ?_⟩
      by_contra hne
      have hq : q ≠ p := fun h => hne h.symm
      have hle : N ≤ (q - p).natAbs := by
        have h1 : (N : ℤ).natAbs ∣ (q - p).natAbs :=
          Int.natAbs_dvd_natAbs.2 hcong
        rw [Int.natAbs_natCast] at h1
        exact Nat.le_of_dvd (Int.natAbs_pos.2 (sub_ne_zero.2 hq)) h1
      have heq : (q - p).natAbs = (p - q).natAbs := by
        rw [← Int.natAbs_neg]
        congr 1
        ring
      omega
    · intro h
      rw [h.2]
  · -- The case `x ≠ y`: the congruence fails for all large `N`.
    have hx0' : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
    have hx1' : (x : ℝ) < 1 := by exact_mod_cast hx1
    have hy0' : (0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy0
    have hy1' : (y : ℝ) < 1 := by exact_mod_cast hy1
    set δ : ℝ := (x : ℝ) - (y : ℝ) with hδdef
    have hδ0 : δ ≠ 0 := by
      rw [hδdef, sub_ne_zero]
      exact_mod_cast hxy
    have hδ1 : |δ| < 1 := by
      rw [hδdef, abs_lt]
      constructor <;> linarith
    have hδpos : 0 < |δ| := abs_pos.2 hδ0
    set C : ℝ := 1 + |(p : ℝ) - (q : ℝ)| with hCdef
    have hCpos : 0 < C := by positivity
    have hminpos : 0 < min |δ| (1 - |δ|) :=
      lt_min hδpos (by linarith)
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (C / min |δ| (1 - |δ|))
    refine Filter.eventually_atTop.2 ⟨N₀, fun N hN => ?_⟩
    have hNr : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < (N : ℝ) :=
      lt_of_lt_of_le (lt_trans (div_pos hCpos hminpos) hN₀) hNr
    have hCmin : C < (N₀ : ℝ) * min |δ| (1 - |δ|) := by
      have h := (div_lt_iff₀ hminpos).1 hN₀
      linarith
    refine iff_of_false ?_ (fun h => hxy h.1)
    intro hcong
    rw [Int.modEq_iff_dvd] at hcong
    obtain ⟨m, hm⟩ := hcong
    have hfx1 : (⌊(N : ℚ) * x⌋₊ : ℝ) ≤ (N : ℝ) * (x : ℝ) := by
      have h := Nat.floor_le (show (0 : ℚ) ≤ (N : ℚ) * x by positivity)
      exact_mod_cast h
    have hfx2 : (N : ℝ) * (x : ℝ) < (⌊(N : ℚ) * x⌋₊ : ℝ) + 1 := by
      have h := Nat.lt_floor_add_one ((N : ℚ) * x)
      exact_mod_cast h
    have hfy1 : (⌊(N : ℚ) * y⌋₊ : ℝ) ≤ (N : ℝ) * (y : ℝ) := by
      have h := Nat.floor_le (show (0 : ℚ) ≤ (N : ℚ) * y by positivity)
      exact_mod_cast h
    have hfy2 : (N : ℝ) * (y : ℝ) < (⌊(N : ℚ) * y⌋₊ : ℝ) + 1 := by
      have h := Nat.lt_floor_add_one ((N : ℚ) * y)
      exact_mod_cast h
    have hmR : (⌊(N : ℚ) * y⌋₊ : ℝ) + (q : ℝ)
        - ((⌊(N : ℚ) * x⌋₊ : ℝ) + (p : ℝ)) = (N : ℝ) * (m : ℝ) := by
      have h2 : ((⌊(N : ℚ) * y⌋₊ : ℤ) + q)
          - ((⌊(N : ℚ) * x⌋₊ : ℤ) + p) = (N : ℤ) * m := hm
      have h3 := congrArg (fun z : ℤ => (z : ℝ)) h2
      push_cast at h3
      exact h3
    have hbound : (N : ℝ) * |((m : ℝ)) + δ| ≤ C := by
      have h1 : |((⌊(N : ℚ) * y⌋₊ : ℝ) - (N : ℝ) * (y : ℝ))
          - ((⌊(N : ℚ) * x⌋₊ : ℝ) - (N : ℝ) * (x : ℝ))| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      have h2 : |(⌊(N : ℚ) * y⌋₊ : ℝ) + (q : ℝ)
          - ((⌊(N : ℚ) * x⌋₊ : ℝ) + (p : ℝ)) + (N : ℝ) * δ| ≤ C := by
        have hexp : (⌊(N : ℚ) * y⌋₊ : ℝ) + (q : ℝ)
            - ((⌊(N : ℚ) * x⌋₊ : ℝ) + (p : ℝ)) + (N : ℝ) * δ
          = ((⌊(N : ℚ) * y⌋₊ : ℝ) - (N : ℝ) * (y : ℝ))
            - ((⌊(N : ℚ) * x⌋₊ : ℝ) - (N : ℝ) * (x : ℝ))
            + ((q : ℝ) - (p : ℝ)) := by
          rw [hδdef]
          ring
        rw [hexp, hCdef]
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_sub_comm (q : ℝ) (p : ℝ)]
        linarith [abs_nonneg ((q : ℝ) - (p : ℝ))]
      have h3 : (N : ℝ) * ((m : ℝ) + δ)
          = (⌊(N : ℚ) * y⌋₊ : ℝ) + (q : ℝ)
            - ((⌊(N : ℚ) * x⌋₊ : ℝ) + (p : ℝ)) + (N : ℝ) * δ := by
        rw [hmR]
        ring
      rw [← h3, abs_mul, abs_of_pos hNpos] at h2
      exact h2
    have hge : min |δ| (1 - |δ|) ≤ |((m : ℝ)) + δ| := by
      rcases (by omega : m = 0 ∨ 1 ≤ m ∨ m ≤ -1) with hm0 | hm1 | hm2
      · rw [hm0]
        simp only [Int.cast_zero, zero_add]
        exact min_le_left _ _
      · have hmR' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
        have hpos : (0 : ℝ) < (m : ℝ) + δ := by
          have h := neg_abs_le δ
          linarith
        rw [abs_of_pos hpos]
        refine le_trans (min_le_right _ _) ?_
        have h := neg_abs_le δ
        linarith
      · have hmR' : (m : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast hm2
        have hneg : (m : ℝ) + δ < 0 := by
          have h := le_abs_self δ
          linarith
        rw [abs_of_neg hneg]
        refine le_trans (min_le_right _ _) ?_
        have h := le_abs_self δ
        linarith
    have hle2 : (N : ℝ) * min |δ| (1 - |δ|) ≤ C :=
      le_trans (mul_le_mul_of_nonneg_left hge (le_of_lt hNpos)) hbound
    have hle3 : (N₀ : ℝ) * min |δ| (1 - |δ|) ≤ C :=
      le_trans (mul_le_mul_of_nonneg_right hNr (le_of_lt hminpos)) hle2
    linarith

/-- The site of an occurrence, in cast form: the floor of
the rescaled position plus the ℤ-offset, as one integer
cast to `ZMod N`. -/
theorem occN_site_cast {k : ℕ} (c : Fin k → LoopInsertion) (N : ℕ)
    (idx : OccIdx k c) (ν : Fin 4) :
    (occN c N idx).1 ν
      = (((⌊(N : ℚ) * (c idx.1).pos ν⌋₊ : ℤ) + (occZ c idx).1 ν : ℤ)
          : ZMod N) := by
  rw [(occN_eq c N idx).2.2 ν]
  unfold rescaledSite
  push_cast
  ring

/-- **Pair stabilization.** For each pair of occurrences,
sharing a finite-`N` link is eventually equivalent to
sharing a limit key. -/
theorem occLinkN_eventually {k : ℕ} (c : Fin k → LoopInsertion)
    (a b : OccIdx k c) :
    ∀ᶠ N : ℕ in Filter.atTop,
      occLinkN c N a = occLinkN c N b ↔ occKey c a = occKey c b := by
  have hcoord : ∀ᶠ N : ℕ in Filter.atTop, ∀ ν : Fin 4,
      ((⌊(N : ℚ) * (c a.1).pos ν⌋₊ : ℤ) + (occZ c a).1 ν)
        ≡ ((⌊(N : ℚ) * (c b.1).pos ν⌋₊ : ℤ) + (occZ c b).1 ν)
        [ZMOD N]
        ↔ ((c a.1).pos ν = (c b.1).pos ν
            ∧ (occZ c a).1 ν = (occZ c b).1 ν) := by
    rw [Filter.eventually_all]
    intro ν
    exact coord_eventually ((c a.1).pos_nonneg ν) ((c a.1).pos_lt_one ν)
      ((c b.1).pos_nonneg ν) ((c b.1).pos_lt_one ν) _ _
  filter_upwards [hcoord] with N hN
  have hcong : ∀ ν : Fin 4, occLinkN c N a = occLinkN c N b →
      ((⌊(N : ℚ) * (c a.1).pos ν⌋₊ : ℤ) + (occZ c a).1 ν)
        ≡ ((⌊(N : ℚ) * (c b.1).pos ν⌋₊ : ℤ) + (occZ c b).1 ν)
        [ZMOD N] := by
    intro ν hlink
    have hsites : (occN c N a).1 = (occN c N b).1 := by
      have h := congrArg Prod.fst hlink
      exact h
    have hν := congrFun hsites ν
    rw [occN_site_cast, occN_site_cast] at hν
    exact (ZMod.intCast_eq_intCast_iff _ _ _).1 hν
  constructor
  · intro hlink
    have hμ : (occZ c a).2.1 = (occZ c b).2.1 := by
      have h1 : (occN c N a).2.1 = (occN c N b).2.1 := by
        have h := congrArg Prod.snd hlink
        exact h
      rwa [(occN_eq c N a).2.1, (occN_eq c N b).2.1] at h1
    have hpos : (c a.1).pos = (c b.1).pos :=
      funext fun ν => ((hN ν).1 (hcong ν hlink)).1
    have hoff : (occZ c a).1 = (occZ c b).1 :=
      funext fun ν => ((hN ν).1 (hcong ν hlink)).2
    exact Prod.ext hpos (Prod.ext hoff hμ)
  · intro hkey
    have hpos : (c a.1).pos = (c b.1).pos := congrArg Prod.fst hkey
    have hoff : (occZ c a).1 = (occZ c b).1 :=
      congrArg (fun K => K.2.1) hkey
    have hμ : (occZ c a).2.1 = (occZ c b).2.1 :=
      congrArg (fun K => K.2.2) hkey
    rw [Prod.ext_iff]
    constructor
    · funext ν
      show (occN c N a).1 ν = (occN c N b).1 ν
      rw [(occN_eq c N a).2.2 ν, (occN_eq c N b).2.2 ν, hpos, hoff]
    · show (occN c N a).2.1 = (occN c N b).2.1
      rwa [(occN_eq c N a).2.1, (occN_eq c N b).2.1]

/-- **Stabilization, uniform over pairs.** Past some
threshold, two occurrences share a finite-`N` link iff
they share a limit key. -/
theorem exists_stab {k : ℕ} (c : Fin k → LoopInsertion) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ a b : OccIdx k c,
      occLinkN c N a = occLinkN c N b ↔ occKey c a = occKey c b := by
  have h1 : ∀ᶠ N : ℕ in Filter.atTop,
      ∀ p : OccIdx k c × OccIdx k c,
        occLinkN c N p.1 = occLinkN c N p.2
          ↔ occKey c p.1 = occKey c p.2 := by
    rw [Filter.eventually_all]
    intro p
    exact occLinkN_eventually c p.1 p.2
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 h1
  exact ⟨N₀, fun N hN a b => hN₀ N hN (a, b)⟩

/-- **Fiber transfer.** When two indexings of a fintype
induce the same equality relation, their fiber sign-sums
vanish together. -/
theorem all_fiber_zero_iff {ι L K : Type*} [Fintype ι]
    [DecidableEq L] [DecidableEq K]
    (link : ι → L) (key : ι → K) (sgn : ι → ℤ)
    (h : ∀ a b, link a = link b ↔ key a = key b) :
    (∀ ℓ, ∑ idx ∈ Finset.univ.filter (fun idx => link idx = ℓ),
        sgn idx = 0)
      ↔ (∀ K₀, ∑ idx ∈ Finset.univ.filter (fun idx => key idx = K₀),
          sgn idx = 0) := by
  constructor
  · intro hl K₀
    by_cases hK : ∃ a, key a = K₀
    · obtain ⟨a, ha⟩ := hK
      have hfil : Finset.univ.filter (fun idx => key idx = K₀)
          = Finset.univ.filter (fun idx => link idx = link a) := by
        refine Finset.filter_congr (fun idx _ => ?_)
        rw [← ha]
        exact (h idx a).symm
      rw [hfil]
      exact hl _
    · have hempty : Finset.univ.filter (fun idx => key idx = K₀)
          = ∅ := by
        rw [Finset.filter_false_of_mem]
        intro idx _
        exact fun hki => hK ⟨idx, hki⟩
      rw [hempty]
      simp
  · intro hk ℓ
    by_cases hℓ : ∃ a, link a = ℓ
    · obtain ⟨a, ha⟩ := hℓ
      have hfil : Finset.univ.filter (fun idx => link idx = ℓ)
          = Finset.univ.filter (fun idx => key idx = key a) := by
        refine Finset.filter_congr (fun idx _ => ?_)
        rw [← ha]
        exact h idx a
      rw [hfil]
      exact hk _
    · have hempty : Finset.univ.filter (fun idx => link idx = ℓ)
          = ∅ := by
        rw [Finset.filter_false_of_mem]
        intro idx _
        exact fun hli => hℓ ⟨idx, hli⟩
      rw [hempty]
      simp

/-- **The β = 0 values stabilize to the exhibited `S`.**
For all large `N`, the product-Haar expectation of the
family observable equals `limitSystemMQ35 k c`. -/
theorem gibbsExpect_zero_famObs_eq_limitSystem {k : ℕ}
    (c : Fin k → LoopInsertion) :
    ∃ N₀ : ℕ, ∀ N : ℕ, ∀ [NeZero N], N₀ ≤ N →
      gibbsExpect (torusShift N) (haarProb Circle) circleRep 0
          (fun U => famObs c N U)
        = limitSystemMQ35 k c := by
  obtain ⟨N₀, hN₀⟩ := exists_stab c
  refine ⟨N₀, fun N _ hN => ?_⟩
  rw [gibbsExpect_zero_famObs]
  have hfib : (∀ ℓ, linkExp c N ℓ = 0) ↔ (∀ K₀, keyExp c K₀ = 0) :=
    all_fiber_zero_iff (occLinkN c N) (occKey c) (occSign c)
      (fun a b => hN₀ N hN a b)
  have hidx : (∀ K₀, keyExp c K₀ = 0)
      ↔ (∀ idx, keyExp c (occKey c idx) = 0) := by
    constructor
    · intro h idx
      exact h _
    · intro h K₀
      by_cases hK : ∃ idx, occKey c idx = K₀
      · obtain ⟨idx, hidx⟩ := hK
        rw [← hidx]
        exact h idx
      · have hempty : Finset.univ.filter
              (fun idx => occKey c idx = K₀) = ∅ := by
          rw [Finset.filter_false_of_mem]
          intro idx _
          exact fun hki => hK ⟨idx, hki⟩
        unfold keyExp
        rw [hempty]
        simp
  show (∏ ℓ : Link (Fin 4 → ZMod N),
      (if linkExp c N ℓ = 0 then (1 : ℂ) else 0))
    = limitSystemMQ35 k c
  unfold limitSystemMQ35
  by_cases hall : ∀ ℓ, linkExp c N ℓ = 0
  · rw [if_pos (hidx.1 (hfib.1 hall))]
    refine Finset.prod_eq_one (fun ℓ _ => ?_)
    rw [if_pos (hall ℓ)]
  · rw [if_neg (fun hcon => hall (hfib.2 (hidx.2 hcon)))]
    obtain ⟨ℓ, hℓ⟩ := not_forall.1 hall
    exact Finset.prod_eq_zero (Finset.mem_univ ℓ) (by rw [if_neg hℓ])

/-! ## §3. The near/far comparison (5b)

The analytic step: on a probability space, if two positive
weights differ by a factor `r ∈ [exp (−η), 1]` pointwise,
their expectations of a `‖F‖ ≤ 1` observable differ by at
most `2(1 − exp (−η)) exp (η)`. The proof recenters at the
far expectation: `∫ W·(F − E) = 0`, and replacing `r` by
its `W`-mean `t ∈ [exp (−η), 1]` costs `|r − t| ≤ 1 − exp (−η)`
against `‖F − E‖ ≤ 2`. -/

/-- Bounded measurable observables are integrable on a
probability space (complex form). -/
theorem integrable_of_bounded_prob {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Ω → ℂ} (hF : Measurable F) (B : ℝ) (hB : ∀ U, ‖F U‖ ≤ B) :
    Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable B (ae_of_all _ hB)

/-- Bounded measurable observables are integrable on a
probability space (real form). -/
theorem integrable_of_bounded_prob_real {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Ω → ℝ} (hF : Measurable F) (B : ℝ) (hB : ∀ U, |F U| ≤ B) :
    Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable B
    (ae_of_all _ fun U => by rw [Real.norm_eq_abs]; exact hB U)

/-- **Weight comparison.** With `D = ∫ W`, `D' = ∫ W·r`,
`E = (∫ W·F)/D`, `E' = (∫ W·r·F)/D'` (integrals against a
probability measure, `W` real with `0 ≤ W ≤ 1`, `D > 0`,
`r ∈ [exp (−η), 1]` pointwise, `‖F‖ ≤ 1`):
`‖E' − E‖ ≤ 2(1 − exp (−η))·exp (η)`. -/
theorem weight_compare {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℂ) (hF : Measurable F) (hFB : ∀ U, ‖F U‖ ≤ 1)
    (W : Ω → ℝ) (hW : Measurable W) (hWnn : ∀ U, 0 ≤ W U)
    (hWle : ∀ U, W U ≤ 1)
    (hDpos : 0 < ∫ U, W U ∂μ)
    (r : Ω → ℝ) (hr : Measurable r) {η : ℝ}
    (hrb : ∀ U, Real.exp (-η) ≤ r U ∧ r U ≤ 1) :
    ‖(∫ U, (W U : ℂ) * (r U : ℂ) * F U ∂μ)
        / ((∫ U, W U * r U ∂μ : ℝ) : ℂ)
      - (∫ U, (W U : ℂ) * F U ∂μ)
        / ((∫ U, W U ∂μ : ℝ) : ℂ)‖
      ≤ 2 * (1 - Real.exp (-η)) * Real.exp η := by
  classical
  obtain ⟨U₀, hU₀⟩ : ∃ U, 0 < W U := by
    by_contra h
    push_neg at h
    have h0 : ∀ U, W U = 0 := fun U => le_antisymm (h U) (hWnn U)
    have h4 : ∫ U, W U ∂μ = ∫ U, (0 : ℝ) ∂μ :=
      integral_congr_ae (ae_of_all _ fun U => h0 U)
    simp at h4
    rw [h4] at hDpos
    exact (lt_irrefl _ hDpos).elim
  have hexpη : Real.exp (-η) ≤ 1 := le_trans (hrb U₀).1 (hrb U₀).2
  have hη : 0 ≤ η := by
    have h := (Real.exp_le_one_iff).1 hexpη
    linarith
  have h1m : (0 : ℝ) ≤ 1 - Real.exp (-η) := by linarith
  set D : ℝ := ∫ U, W U ∂μ with hDdef
  set D' : ℝ := ∫ U, W U * r U ∂μ with hD'def
  set E : ℂ := (∫ U, (W U : ℂ) * F U ∂μ) / (D : ℂ) with hEdef
  have hW1 : ∀ U, ‖(W U : ℂ)‖ ≤ 1 := fun U => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hWnn U)]
    exact hWle U
  have hr1 : ∀ U, ‖(r U : ℂ)‖ ≤ 1 := fun U => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.2 ⟨by linarith [Real.exp_nonneg (-η), (hrb U).1], (hrb U).2⟩
  have hWint : Integrable W μ :=
    integrable_of_bounded_prob_real μ hW 1
      (fun U => abs_le.2 ⟨by linarith [hWnn U], hWle U⟩)
  have hWrint : Integrable (fun U => W U * r U) μ := by
    refine integrable_of_bounded_prob_real μ (hW.mul hr) 1 (fun U => ?_)
    rw [abs_mul, abs_of_nonneg (hWnn U)]
    refine le_trans (mul_le_mul_of_nonneg_left (abs_le.2
      ⟨by linarith [Real.exp_nonneg (-η), (hrb U).1], (hrb U).2⟩)
      (hWnn U)) ?_
    simpa using hWle U
  have hIntC : ∀ (s : Ω → ℝ) (g : Ω → ℂ) (B : ℝ),
      Measurable s → (∀ U, ‖(s U : ℂ)‖ ≤ 1) → Measurable g
      → (∀ U, ‖g U‖ ≤ B) →
      Integrable (fun U => (W U : ℂ) * (s U : ℂ) * g U) μ := by
    intro s g B hs hs1 hg hgB
    refine integrable_of_bounded_prob μ
      (((Complex.measurable_ofReal.comp hW).mul
        (Complex.measurable_ofReal.comp hs)).mul hg) B (fun U => ?_)
    rw [norm_mul, norm_mul]
    refine le_trans (mul_le_mul
      (mul_le_mul (hW1 U) (hs1 U) (by positivity) (by norm_num))
      (hgB U) (norm_nonneg _) (by norm_num)) ?_
    simp
  have hWFint : Integrable (fun U => (W U : ℂ) * F U) μ := by
    have h := hIntC (fun _ => (1 : ℝ)) F 1 measurable_const
      (fun U => by simp) hF hFB
    exact h.congr (ae_of_all _ fun U => by simp)
  have hWrFint : Integrable (fun U => (W U : ℂ) * (r U : ℂ) * F U) μ :=
    hIntC r F 1 hr hr1 hF hFB
  have hWrCint : Integrable (fun U => (W U : ℂ) * (r U : ℂ)) μ := by
    have h := hIntC r (fun _ => (1 : ℂ)) 1 hr hr1 measurable_const
      (fun U => by simp)
    exact h.congr (ae_of_all _ fun U => by simp)
  have hD'ge : Real.exp (-η) * D ≤ D' := by
    have h := integral_mono_ae (hWint.const_mul (Real.exp (-η))) hWrint
      (ae_of_all _ fun U => by
        show Real.exp (-η) * W U ≤ W U * r U
        rw [mul_comm (Real.exp (-η)) (W U)]
        exact mul_le_mul_of_nonneg_left (hrb U).1 (hWnn U))
    rwa [integral_const_mul] at h
  have hD'le : D' ≤ D := by
    refine integral_mono_ae hWrint hWint (ae_of_all _ fun U => ?_)
    calc W U * r U ≤ W U * 1 :=
          mul_le_mul_of_nonneg_left (hrb U).2 (hWnn U)
      _ = W U := mul_one _
  have hD'pos : 0 < D' :=
    lt_of_lt_of_le (mul_pos (Real.exp_pos _) hDpos) hD'ge
  set t : ℝ := D' / D with htdef
  have ht1 : Real.exp (-η) ≤ t := by
    rw [htdef, le_div_iff₀ hDpos]
    exact hD'ge
  have ht2 : t ≤ 1 := by
    rw [htdef, div_le_one hDpos]
    exact hD'le
  have hEle : ‖E‖ ≤ 1 := by
    rw [hEdef, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hDpos, div_le_one hDpos]
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine integral_mono_ae hWFint.norm hWint (ae_of_all _ fun U => ?_)
    show ‖(W U : ℂ) * F U‖ ≤ W U
    rw [norm_mul,
      show ‖(W U : ℂ)‖ = W U by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hWnn U)]]
    refine le_trans (mul_le_mul_of_nonneg_left (hFB U) (hWnn U)) ?_
    rw [mul_one]
  have hWEint : Integrable (fun U => (W U : ℂ) * E) μ :=
    integrable_of_bounded_prob μ
      ((Complex.measurable_ofReal.comp hW).mul measurable_const) 1
      (fun U => by
        rw [norm_mul]
        exact le_trans (mul_le_mul (hW1 U) hEle (norm_nonneg _)
          zero_le_one) (by simp))
  have hcenter : ∫ U, (W U : ℂ) * (F U - E) ∂μ = 0 := by
    have hsplit : ∫ U, (W U : ℂ) * (F U - E) ∂μ
        = (∫ U, (W U : ℂ) * F U ∂μ) - (∫ U, (W U : ℂ) * E ∂μ) := by
      rw [← integral_sub hWFint hWEint]
      refine integral_congr_ae (ae_of_all _ fun U => ?_)
      show (W U : ℂ) * (F U - E) = (W U : ℂ) * F U - (W U : ℂ) * E
      rw [mul_sub]
    rw [hsplit, integral_mul_const, integral_complex_ofReal, ← hDdef,
      hEdef]
    have hDne : (D : ℂ) ≠ 0 := by exact_mod_cast hDpos.ne'
    field_simp
    ring
  have hG2 : ∀ U, ‖F U - E‖ ≤ 2 :=
    fun U => le_trans (norm_sub_le _ _) (by linarith [hFB U, hEle])
  have hrt1 : ∀ U, ‖((r U - t : ℝ) : ℂ)‖ ≤ 1 := fun U => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.2 ⟨by linarith [ht2, (hrb U).1, Real.exp_nonneg (-η)],
      by linarith [(hrb U).2, ht1, Real.exp_nonneg (-η)]⟩
  have hrtmeas : Measurable (fun U => r U - t) := hr.sub measurable_const
  have hdefect : (∫ U, (W U : ℂ) * (r U : ℂ) * F U ∂μ) - E * (D' : ℂ)
      = ∫ U, (W U : ℂ) * ((r U - t : ℝ) : ℂ) * (F U - E) ∂μ := by
    have e2 : ∫ U, (W U : ℂ) * (t : ℂ) * (F U - E) ∂μ = 0 := by
      have hcong : (fun U => (W U : ℂ) * (t : ℂ) * (F U - E))
          = (fun U => (t : ℂ) * ((W U : ℂ) * (F U - E))) := by
        funext U
        ring
      rw [hcong, integral_const_mul, hcenter, mul_zero]
    have e3 : ∫ U, (W U : ℂ) * (r U : ℂ) * (F U - E) ∂μ
        = (∫ U, (W U : ℂ) * (r U : ℂ) * F U ∂μ) - E * (D' : ℂ) := by
      have hsplit : ∫ U, (W U : ℂ) * (r U : ℂ) * (F U - E) ∂μ
          = (∫ U, (W U : ℂ) * (r U : ℂ) * F U ∂μ)
            - (∫ U, E * ((W U : ℂ) * (r U : ℂ)) ∂μ) := by
        rw [← integral_sub hWrFint (hWrCint.const_mul E)]
        refine integral_congr_ae (ae_of_all _ fun U => ?_)
        ring
      rw [hsplit, integral_const_mul]
      congr 1
      have hcast : (fun U => (W U : ℂ) * (r U : ℂ))
          = (fun U => ((W U * r U : ℝ) : ℂ)) := by
        funext U
        push_cast
        ring
      rw [hcast, integral_complex_ofReal]
    have e1 : ∫ U, (W U : ℂ) * ((r U - t : ℝ) : ℂ) * (F U - E) ∂μ
        = (∫ U, (W U : ℂ) * (r U : ℂ) * (F U - E) ∂μ)
          - (∫ U, (W U : ℂ) * (t : ℂ) * (F U - E) ∂μ) := by
      rw [← integral_sub
        (hIntC r (fun U => F U - E) 2 hr hr1 (hF.sub measurable_const) hG2)
        (hIntC (fun _ => t) (fun U => F U - E) 2 measurable_const
          (fun U => by
            rw [Complex.norm_real, Real.norm_eq_abs]
            exact abs_le.2 ⟨by linarith [ht1, Real.exp_nonneg (-η)], ht2⟩)
          (hF.sub measurable_const) hG2)]
      refine integral_congr_ae (ae_of_all _ fun U => ?_)
      push_cast
      ring
    calc (∫ U, (W U : ℂ) * (r U : ℂ) * F U ∂μ) - E * (D' : ℂ)
        = ∫ U, (W U : ℂ) * (r U : ℂ) * (F U - E) ∂μ := e3.symm
      _ = ∫ U, (W U : ℂ) * ((r U - t : ℝ) : ℂ) * (F U - E) ∂μ := by
          rw [e1, e2, sub_zero]
  have hnum : ‖(∫ U, (W U : ℂ) * (r U : ℂ) * F U ∂μ) - E * (D' : ℂ)‖
      ≤ (1 - Real.exp (-η)) * (2 * D) := by
    have hpoint : ∀ U, ‖(W U : ℂ) * ((r U - t : ℝ) : ℂ) * (F U - E)‖
        ≤ (1 - Real.exp (-η)) * (2 * W U) := by
      intro U
      have hrt : ‖((r U - t : ℝ) : ℂ)‖ ≤ 1 - Real.exp (-η) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
        constructor
        · linarith [(hrb U).1, ht2]
        · linarith [(hrb U).2, ht1]
      have hWeq : ‖(W U : ℂ)‖ = W U := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hWnn U)]
      rw [norm_mul, norm_mul, hWeq]
      refine le_trans (mul_le_mul
        (mul_le_mul le_rfl hrt (norm_nonneg _) (hWnn U)) (hG2 U)
        (norm_nonneg _) (mul_nonneg (hWnn U) h1m)) (le_of_eq ?_)
      ring
    rw [hdefect]
    refine le_trans (norm_integral_le_integral_norm _)
      (le_trans (integral_mono_ae
        (hIntC (fun U => r U - t) (fun U => F U - E) 2 hrtmeas hrt1
          (hF.sub measurable_const) hG2).norm
        ((hWint.const_mul ((1 - Real.exp (-η)) * 2)).congr
          (ae_of_all _ fun U => by ring))
        (ae_of_all _ hpoint)) ?_)
    refine le_of_eq ?_
    have hfun : (fun U => (1 - Real.exp (-η)) * (2 * W U))
        = (fun U => ((1 - Real.exp (-η)) * 2) * W U) :=
      funext fun U => by ring
    rw [hfun, integral_const_mul, ← hDdef]
    ring
  have hfin : (∫ U, (W U : ℂ) * (r U : ℂ) * F U ∂μ) / (D' : ℂ) - E
      = ((∫ U, (W U : ℂ) * (r U : ℂ) * F U ∂μ) - E * (D' : ℂ))
        / (D' : ℂ) := by
    have hD'ne : (D' : ℂ) ≠ 0 := by exact_mod_cast hD'pos.ne'
    field_simp
  rw [hfin, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hD'pos]
  calc ‖(∫ U, (W U : ℂ) * (r U : ℂ) * F U ∂μ) - E * (D' : ℂ)‖ / D'
      ≤ ((1 - Real.exp (-η)) * (2 * D)) / (Real.exp (-η) * D) := by
        gcongr
    _ = 2 * (1 - Real.exp (-η)) * Real.exp η := by
        have hD0 : (D : ℝ) ≠ 0 := hDpos.ne'
        have he : Real.exp η ≠ 0 := (Real.exp_pos _).ne'
        rw [div_eq_iff (mul_ne_zero (by
          rw [Real.exp_neg]; exact inv_ne_zero he) hD0), Real.exp_neg]
        field_simp

/-! ### §3B. Specialization: near/far at the circle seat

The far weight (plaquettes sharing no link with the
insertion support) is exactly independent of the observable;
the near weight differs from `1` by `exp (−η)` with
`η = β · 2 · #near`. -/

section NearFar

variable {k : ℕ} (c : Fin k → LoopInsertion) (N : ℕ) [NeZero N]

/-- Links touched by the insertion family at level `N`. -/
def sN : Finset (Link (Fin 4 → ZMod N)) :=
  Finset.univ.image (occLinkN c N)

/-- Plaquette triples sharing a link with the support. -/
def nearQ : Finset ((Fin 4 → ZMod N) × Fin 4 × Fin 4) :=
  sharingMQ N (sN c N)

/-- All plaquette triples. -/
def univ33 : Finset ((Fin 4 → ZMod N) × Fin 4 × Fin 4) :=
  Finset.univ.filter (fun q => q.2.1 < q.2.2)

/-- The far action: plaquettes disjoint from the support. -/
noncomputable def afar (U : Config (Fin 4 → ZMod N) Circle) : ℝ :=
  ∑ q ∈ univ33 N \ nearQ c N,
    plaquetteDensity (torusShift N) circleRep U q.1 q.2.1 q.2.2

/-- The near action: plaquettes touching the support. -/
noncomputable def anear (U : Config (Fin 4 → ZMod N) Circle) : ℝ :=
  ∑ q ∈ nearQ c N,
    plaquetteDensity (torusShift N) circleRep U q.1 q.2.1 q.2.2

theorem card_sN_le : (sN c N).card ≤ ∑ i : Fin k, (c i).steps.length := by
  have h1 : (sN c N).card ≤ Fintype.card (OccIdx k c) := by
    show (Finset.univ.image (occLinkN c N)).card ≤ Fintype.card (OccIdx k c)
    rw [← Finset.card_univ]
    exact Finset.card_image_le
  have h2 : Fintype.card (OccIdx k c)
      = ∑ i : Fin k, (c i).steps.length := by
    show Fintype.card (Σ i : Fin k, Fin (c i).steps.length) = _
    rw [Fintype.card_sigma]
    exact Finset.sum_congr rfl (fun i _ => Fintype.card_fin _)
  exact h1.trans h2.le

theorem card_nearQ_le :
    (nearQ c N).card ≤ 12 * (∑ i : Fin k, (c i).steps.length) :=
  le_trans (card_sharingMQ_le N (sN c N))
    (Nat.mul_le_mul_left 12 (card_sN_le c N))

theorem nearQ_subset : nearQ c N ⊆ univ33 N := by
  intro q hq
  simp only [nearQ, sharingMQ, Finset.mem_filter, Finset.mem_univ,
    true_and] at hq
  simp only [univ33, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hq.1

theorem actDen_split (U : Config (Fin 4 → ZMod N) Circle) :
    actDen N U = anear c N U + afar c N U := by
  have h := actDen_eq_sum_triples N U
  rw [show (Finset.univ.filter
        (fun q : (Fin 4 → ZMod N) × Fin 4 × Fin 4 => q.2.1 < q.2.2))
      = univ33 N from rfl] at h
  rw [h, ← Finset.sum_sdiff (nearQ_subset c N), add_comm]
  rfl

theorem afar_nonneg (U : Config (Fin 4 → ZMod N) Circle) :
    0 ≤ afar c N U :=
  Finset.sum_nonneg (fun q _ =>
    (plaquetteDensity_mem_Icc (torusShift N) circleRep (by norm_num)
      U q.1 q.2.1 q.2.2).1)

theorem anear_nonneg (U : Config (Fin 4 → ZMod N) Circle) :
    0 ≤ anear c N U :=
  Finset.sum_nonneg (fun q _ =>
    (plaquetteDensity_mem_Icc (torusShift N) circleRep (by norm_num)
      U q.1 q.2.1 q.2.2).1)

theorem afar_le (U : Config (Fin 4 → ZMod N) Circle) :
    afar c N U ≤ ((univ33 N \ nearQ c N).card : ℝ) * 2 := by
  refine le_trans (Finset.sum_le_card_nsmul _ _ 2 (fun q _ =>
    (plaquetteDensity_mem_Icc (torusShift N) circleRep (by norm_num)
      U q.1 q.2.1 q.2.2).2)) ?_
  rw [nsmul_eq_mul]

theorem anear_le (U : Config (Fin 4 → ZMod N) Circle) :
    anear c N U ≤ ((nearQ c N).card : ℝ) * 2 := by
  refine le_trans (Finset.sum_le_card_nsmul _ _ 2 (fun q _ =>
    (plaquetteDensity_mem_Icc (torusShift N) circleRep (by norm_num)
      U q.1 q.2.1 q.2.2).2)) ?_
  rw [nsmul_eq_mul]

/-- Finite sums of plaquette densities are measurable
(induction on the index set). -/
theorem measurable_density_sum (s : Finset ((Fin 4 → ZMod N) × Fin 4 × Fin 4)) :
    Measurable (fun U => ∑ q ∈ s,
      plaquetteDensity (torusShift N) circleRep U q.1 q.2.1 q.2.2) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (measurable_const : Measurable (fun _ : Config (Fin 4 → ZMod N) Circle => (0 : ℝ)))
  | @insert a s ha ih =>
    have hfun : (fun U => ∑ q ∈ insert a s,
          plaquetteDensity (torusShift N) circleRep U q.1 q.2.1 q.2.2)
        = (fun U => plaquetteDensity (torusShift N) circleRep U
            a.1 a.2.1 a.2.2
          + ∑ q ∈ s, plaquetteDensity (torusShift N) circleRep U
              q.1 q.2.1 q.2.2) := by
      funext U
      exact Finset.sum_insert ha
    rw [hfun]
    exact (measurable_plaquetteDensity_MQ35 N a.1 a.2.1 a.2.2).add ih

theorem measurable_afar : Measurable (afar c N) :=
  measurable_density_sum N _

theorem measurable_anear : Measurable (anear c N) :=
  measurable_density_sum N _

theorem famObs_norm_le (U : Config (Fin 4 → ZMod N) Circle) :
    ‖famObs c N U‖ ≤ 1 := by
  show ‖∏ i : Fin k, wilsonLoop (torusShift N) circleRep U
      (rescaledSite N (c i).pos) (c i).steps‖ ≤ 1
  refine le_trans (norm_prod_le Finset.univ _) ?_
  refine Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
  refine le_trans (norm_wilsonLoop_le (torusShift N) circleRep
    (by norm_num) U _ _) ?_
  norm_num

/-- Measurability of finite products of Wilson loops
(induction on the index set). -/
theorem measurable_wilson_prod (s : Finset (Fin k)) :
    Measurable (fun U => ∏ i ∈ s, wilsonLoop (torusShift N) circleRep U
      (rescaledSite N (c i).pos) (c i).steps) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simpa using (measurable_const :
      Measurable (fun _ : Config (Fin 4 → ZMod N) Circle => (1 : ℂ)))
  | @insert a s ha ih =>
    have hfun : (fun U => ∏ i ∈ insert a s, wilsonLoop (torusShift N)
          circleRep U (rescaledSite N (c i).pos) (c i).steps)
        = (fun U => wilsonLoop (torusShift N) circleRep U
            (rescaledSite N (c a).pos) (c a).steps
          * ∏ i ∈ s, wilsonLoop (torusShift N) circleRep U
              (rescaledSite N (c i).pos) (c i).steps) := by
      funext U
      exact Finset.prod_insert ha
    rw [hfun]
    exact (measurable_wilsonLoop (torusShift N) circleRep
      circleRep_continuous _ _).mul ih

theorem measurable_famObs : Measurable (famObs c N) :=
  measurable_wilson_prod c N Finset.univ

theorem linkExp_eq_zero_of_not_mem {ℓ : Link (Fin 4 → ZMod N)}
    (hℓ : ℓ ∉ sN c N) : linkExp c N ℓ = 0 := by
  unfold linkExp
  rw [Finset.filter_false_of_mem, Finset.sum_empty]
  intro idx _
  intro hcon
  exact hℓ (Finset.mem_image.2 ⟨idx, Finset.mem_univ idx, hcon⟩)

theorem famObs_eq_prod_linkExp (U : Config (Fin 4 → ZMod N) Circle) :
    famObs c N U = ∏ ℓ : Link (Fin 4 → ZMod N),
      ((U ℓ : ℂ)) ^ linkExp c N ℓ := by
  rw [famObs_eq_prod_occ,
    ← Finset.prod_fiberwise_of_maps_to (s := Finset.univ)
      (t := Finset.univ) (g := occLinkN c N)
      (fun idx _ => Finset.mem_univ _)
      (fun idx => ((U (occLinkN c N idx) : ℂ)) ^ occSign c idx)]
  refine Finset.prod_congr rfl (fun ℓ _ => ?_)
  have hcirc : ∏ idx ∈ Finset.univ.filter
        (fun idx => occLinkN c N idx = ℓ),
        ((U (occLinkN c N idx) : ℂ)) ^ occSign c idx
      = ((∏ idx ∈ Finset.univ.filter
          (fun idx => occLinkN c N idx = ℓ),
          (U ℓ) ^ occSign c idx : Circle) : ℂ) := by
    rw [coe_prod_circle]
    refine Finset.prod_congr rfl (fun idx hidx => ?_)
    rw [Finset.mem_filter] at hidx
    rw [coe_zpow_circle, hidx.2]
  rw [hcirc]
  show ((∏ idx ∈ Finset.univ.filter (fun idx => occLinkN c N idx = ℓ),
      (U ℓ) ^ occSign c idx : Circle) : ℂ)
    = ((U ℓ : ℂ)) ^ linkExp c N ℓ
  rw [zpow_sum_circle, coe_zpow_circle]
  rfl

/-- The factor of the observable through its support. -/
noncomputable def gF (v : ↥(sN c N) → Circle) : ℂ :=
  ∏ ℓ : ↥(sN c N), ((v ℓ : ℂ)) ^ linkExp c N ℓ.1

theorem famObs_factor (U : Config (Fin 4 → ZMod N) Circle) :
    famObs c N U = gF c N (fun ℓ : ↥(sN c N) => U ℓ.1) := by
  rw [famObs_eq_prod_linkExp]
  have h1 : ∏ ℓ : Link (Fin 4 → ZMod N), ((U ℓ : ℂ)) ^ linkExp c N ℓ
      = ∏ ℓ ∈ sN c N, ((U ℓ : ℂ)) ^ linkExp c N ℓ := by
    refine (Finset.prod_subset (Finset.subset_univ _) (fun ℓ _ hℓ => ?_)).symm
    rw [linkExp_eq_zero_of_not_mem c N hℓ, zpow_zero]
  rw [h1]
  show (∏ ℓ ∈ sN c N, ((U ℓ : ℂ)) ^ linkExp c N ℓ)
    = ∏ ℓ ∈ (sN c N).attach, ((U ℓ.1 : ℂ)) ^ linkExp c N ℓ.1
  exact (Finset.prod_attach _ _).symm

/-- Each far plaquette density factors through the complement
of the insertion support (as a complex observable). -/
theorem far_density_factors : ∀ q ∈ univ33 N \ nearQ c N,
    ∃ g : (↥(sN c N)ᶜ → Circle) → ℂ,
      ∀ U : Config (Fin 4 → ZMod N) Circle,
        (plaquetteDensity (torusShift N) circleRep U q.1 q.2.1 q.2.2 : ℂ)
          = g (fun ℓ : ↥(sN c N)ᶜ => U ℓ.1) := by
  intro q hq
  have hlt : q.2.1 < q.2.2 := by
    have h1 : q ∈ univ33 N := (Finset.mem_sdiff.1 hq).1
    simp only [univ33, Finset.mem_filter, Finset.mem_univ, true_and] at h1
    exact h1
  have hsub : ∀ i ∈ plaqLinks N q.1 q.2.1 q.2.2, i ∈ (sN c N)ᶜ := by
    intro i hi
    rw [Finset.mem_compl]
    intro hiS
    have hne : (plaqLinks N q.1 q.2.1 q.2.2 ∩ sN c N).Nonempty :=
      ⟨i, Finset.mem_inter.2 ⟨hi, hiS⟩⟩
    have hqnear : q ∈ nearQ c N := by
      show q ∈ sharingMQ N (sN c N)
      rw [sharingMQ, Finset.mem_filter]
      exact ⟨Finset.mem_univ q, hlt, hne⟩
    exact (Finset.mem_sdiff.1 hq).2 hqnear
  obtain ⟨f, hf⟩ := plaquetteDensity_dependsOnlyOn_MQ35 N q.1 q.2.1 q.2.2
  exact ⟨fun w => f (fun ℓ : ↥(plaqLinks N q.1 q.2.1 q.2.2) =>
    w ⟨ℓ.1, hsub ℓ ℓ.2⟩), fun U => hf U⟩

/-- The far weight as a complex observable. -/
noncomputable def farWeight (β : ℝ) (U : Config (Fin 4 → ZMod N) Circle) :
    ℂ :=
  ((Real.exp (-(β * afar c N U)) : ℝ) : ℂ)

/-- **Far factorization.** The far weight is exactly
independent of the observable under the product measure. -/
theorem far_split (β : ℝ) :
    ∫ U, famObs c N U * farWeight c N β U
        ∂(configMeasure (haarProb Circle))
      = (∫ U, famObs c N U ∂(configMeasure (haarProb Circle)))
        * (∫ U, farWeight c N β U
            ∂(configMeasure (haarProb Circle))) := by
  classical
  choose gq hgq using far_density_factors c N
  have hsum : ∀ U : Config (Fin 4 → ZMod N) Circle,
      afar c N U = ∑ q : ↥(univ33 N \ nearQ c N),
        (gq q.1 q.2 (fun ℓ : ↥(sN c N)ᶜ => U ℓ.1)).re := by
    intro U
    unfold afar
    rw [← Finset.sum_attach (univ33 N \ nearQ c N)
      (fun q => plaquetteDensity (torusShift N) circleRep U q.1 q.2.1 q.2.2),
      Finset.univ_eq_attach]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    have h := congrArg Complex.re (hgq q.1 q.2 U)
    rw [Complex.ofReal_re] at h
    exact h
  have hfac : ∀ U : Config (Fin 4 → ZMod N) Circle,
      farWeight c N β U
        = ((Real.exp (-(β * ∑ q : ↥(univ33 N \ nearQ c N),
            (gq q.1 q.2 (fun ℓ : ↥(sN c N)ᶜ => U ℓ.1)).re)) : ℝ) : ℂ) := by
    intro U
    unfold farWeight
    rw [hsum U]
  rw [← gibbsExpect_zero (torusShift N) (haarProb Circle) circleRep
      (fun U => famObs c N U * farWeight c N β U),
    ← gibbsExpect_zero (torusShift N) (haarProb Circle) circleRep
      (fun U => famObs c N U),
    ← gibbsExpect_zero (torusShift N) (haarProb Circle) circleRep
      (fun U => farWeight c N β U)]
  exact (gibbsExpect_zero_mul_of_compl_dependsOnlyOn (torusShift N)
    (haarProb Circle) circleRep (fun U => famObs c N U)
    (fun U => farWeight c N β U) (sN c N) (gF c N)
    (fun w => ((Real.exp (-(β * ∑ q : ↥(univ33 N \ nearQ c N),
      (gq q.1 q.2 w).re)) : ℝ) : ℂ))
    (fun U => famObs_factor c N U) hfac)

/-- The far partition integral is positive: the far action is
bounded by twice the number of far plaquettes. -/
theorem farWeight_integral_pos (β : ℝ) (hβ : 0 ≤ β) :
    0 < ∫ U, Real.exp (-(β * afar c N U))
      ∂(configMeasure (haarProb Circle)) := by
  have hInt : Integrable (fun U => Real.exp (-(β * afar c N U)))
      (configMeasure (haarProb Circle)) := by
    refine Integrable.of_bound
      ((Real.measurable_exp.comp
        ((measurable_afar c N).const_mul β).neg).aestronglyMeasurable) 1
      (ae_of_all _ fun U => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact (Real.exp_le_one_iff).2
      (neg_nonpos.2 (mul_nonneg hβ (afar_nonneg c N U)))
  have hle : ∫ U, Real.exp (-(β * (((univ33 N \ nearQ c N).card : ℝ) * 2)))
        ∂(configMeasure (haarProb Circle))
      ≤ ∫ U, Real.exp (-(β * afar c N U))
        ∂(configMeasure (haarProb Circle)) :=
    integral_mono_ae (integrable_const _) hInt (ae_of_all _ fun U =>
      Real.exp_le_exp.2
        (neg_le_neg (mul_le_mul_of_nonneg_left (afar_le c N U) hβ)))
  refine lt_of_lt_of_le ?_ hle
  rw [integral_const,
    show (configMeasure (haarProb Circle)).real Set.univ = 1 by
      rw [measureReal_def, measure_univ, ENNReal.toReal_one], one_smul]
  exact Real.exp_pos _

/-- **Near/far bound.** Along any `β ≥ 0`, the Gibbs
expectation of the family observable differs from its
`β = 0` value by at most `2(1 − exp(−η))·exp(η)` with
`η = β · 2 · #near`. -/
theorem near_far_bound (β : ℝ) (hβ : 0 ≤ β) :
    ‖gibbsExpect (torusShift N) (haarProb Circle) circleRep β
        (fun U => famObs c N U)
      - gibbsExpect (torusShift N) (haarProb Circle) circleRep 0
        (fun U => famObs c N U)‖
    ≤ 2 * (1 - Real.exp (-(β * (2 * ((nearQ c N).card : ℝ)))))
        * Real.exp (β * (2 * ((nearQ c N).card : ℝ))) := by
  classical
  have hWmeas : Measurable (fun U => Real.exp (-(β * afar c N U))) :=
    Real.measurable_exp.comp ((measurable_afar c N).const_mul β).neg
  have hrmeas : Measurable (fun U => Real.exp (-(β * anear c N U))) :=
    Real.measurable_exp.comp ((measurable_anear c N).const_mul β).neg
  have hWle : ∀ U, Real.exp (-(β * afar c N U)) ≤ 1 := fun U =>
    (Real.exp_le_one_iff).2
      (neg_nonpos.2 (mul_nonneg hβ (afar_nonneg c N U)))
  have hrb : ∀ U, Real.exp (-(β * (2 * ((nearQ c N).card : ℝ))))
      ≤ Real.exp (-(β * anear c N U))
      ∧ Real.exp (-(β * anear c N U)) ≤ 1 := by
    intro U
    refine ⟨Real.exp_le_exp.2 (neg_le_neg ?_),
      (Real.exp_le_one_iff).2
        (neg_nonpos.2 (mul_nonneg hβ (anear_nonneg c N U)))⟩
    refine mul_le_mul_of_nonneg_left ?_ hβ
    calc anear c N U ≤ ((nearQ c N).card : ℝ) * 2 := anear_le c N U
      _ = 2 * ((nearQ c N).card : ℝ) := by ring
  have hsplit_exp : ∀ U : Config (Fin 4 → ZMod N) Circle,
      Real.exp (-(β * actDen N U))
        = Real.exp (-(β * afar c N U)) * Real.exp (-(β * anear c N U)) := by
    intro U
    rw [actDen_split c N U,
      show -(β * (anear c N U + afar c N U))
        = -(β * afar c N U) + -(β * anear c N U) by ring, Real.exp_add]
  have hI2 : gibbsExpect (torusShift N) (haarProb Circle) circleRep β
        (fun U => famObs c N U)
      = (∫ U, ((Real.exp (-(β * afar c N U)) : ℝ) : ℂ)
          * ((Real.exp (-(β * anear c N U)) : ℝ) : ℂ) * famObs c N U
          ∂(configMeasure (haarProb Circle)))
        / ((∫ U, Real.exp (-(β * afar c N U))
            * Real.exp (-(β * anear c N U))
            ∂(configMeasure (haarProb Circle)) : ℝ) : ℂ) := by
    unfold gibbsExpect
    congr 1
    · refine integral_congr_ae (ae_of_all _ fun U => ?_)
      dsimp only
      rw [wilsonAction_eq_actDen, hsplit_exp U]
      push_cast
      ring
    · congr 1
      refine integral_congr_ae (ae_of_all _ fun U => ?_)
      dsimp only
      rw [wilsonAction_eq_actDen, hsplit_exp U]
  have hI1 : (∫ U, ((Real.exp (-(β * afar c N U)) : ℝ) : ℂ)
        * famObs c N U ∂(configMeasure (haarProb Circle)))
      / ((∫ U, Real.exp (-(β * afar c N U))
          ∂(configMeasure (haarProb Circle)) : ℝ) : ℂ)
      = gibbsExpect (torusShift N) (haarProb Circle) circleRep 0
          (fun U => famObs c N U) := by
    rw [gibbsExpect_zero]
    have hnum : ∫ U, ((Real.exp (-(β * afar c N U)) : ℝ) : ℂ)
          * famObs c N U ∂(configMeasure (haarProb Circle))
        = (∫ U, famObs c N U ∂(configMeasure (haarProb Circle)))
          * ((∫ U, Real.exp (-(β * afar c N U))
              ∂(configMeasure (haarProb Circle)) : ℝ) : ℂ) := by
      have h1 : ∫ U, ((Real.exp (-(β * afar c N U)) : ℝ) : ℂ)
            * famObs c N U ∂(configMeasure (haarProb Circle))
          = ∫ U, famObs c N U * farWeight c N β U
              ∂(configMeasure (haarProb Circle)) :=
        integral_congr_ae (ae_of_all _ fun U => mul_comm _ _)
      rw [h1, far_split c N β]
      congr 1
      have h2 : ∫ U, farWeight c N β U
            ∂(configMeasure (haarProb Circle))
          = ((∫ U, Real.exp (-(β * afar c N U))
              ∂(configMeasure (haarProb Circle)) : ℝ) : ℂ) := by
        have hcong : ∫ U, farWeight c N β U
              ∂(configMeasure (haarProb Circle))
            = ∫ U, ((Real.exp (-(β * afar c N U)) : ℝ) : ℂ)
                ∂(configMeasure (haarProb Circle)) :=
          integral_congr_ae (ae_of_all _ fun U => rfl)
        rw [hcong]
        exact integral_complex_ofReal
      rw [h2]
    rw [hnum]
    exact mul_div_cancel_right₀ _
      (by exact_mod_cast (farWeight_integral_pos c N β hβ).ne')
  have key := weight_compare (configMeasure (haarProb Circle))
    (famObs c N) (measurable_famObs c N) (famObs_norm_le c N)
    (fun U => Real.exp (-(β * afar c N U))) hWmeas
    (fun U => Real.exp_nonneg _) hWle (farWeight_integral_pos c N β hβ)
    (fun U => Real.exp (-(β * anear c N U))) hrmeas hrb
  rw [hI2, ← hI1]
  exact key

end NearFar

/-! ## §4. Assembly (5c)

Along `trajFloorU1`, `η_N = βt N · 2 · #near ≤ βt N · 24 ·
(total insertion length) ≤ 24·L/(N+1) → 0`; past the
stabilization threshold the `β = 0` value is the exhibited
limit system on the nose, and for `η ≤ 1/2` the comparison
bound is at most `4η`. -/

/-- **MQ3-5 headline.** The finite correlations converge
pointwise along `trajFloorU1` to the exhibited limit system
`limitSystemMQ35` — the `β = 0` (free/product-Haar) system:
a family has correlation `1` iff every limit link exponent
vanishes, else `0`. -/
theorem correlationsConvergePointwise_trajFloorU1 :
    CorrelationsConvergePointwise (haarProb Circle) circleRep
      trajFloorU1 limitSystemMQ35 := by
  intro k c ε hε
  classical
  set Ltot : ℕ := ∑ i : Fin k, (c i).steps.length with hLtot
  obtain ⟨N₁, hN₁⟩ := gibbsExpect_zero_famObs_eq_limitSystem c
  obtain ⟨N₂, hN₂⟩ : ∃ n : ℕ, 96 * (Ltot : ℝ) / ε < (n : ℝ) :=
    exists_nat_gt _
  obtain ⟨N₃, hN₃⟩ : ∃ n : ℕ, 48 * (Ltot : ℝ) < (n : ℝ) :=
    exists_nat_gt _
  refine ⟨max N₁ (max N₂ N₃), ?_⟩
  intro N instN hN hEven h2N
  have hN₁' : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN₂' : N₂ ≤ N :=
    le_trans (le_max_of_le_right (le_max_left _ _)) hN
  have hN₃' : N₃ ≤ N :=
    le_trans (le_max_of_le_right (le_max_right _ _)) hN
  have hN2r : 96 * (Ltot : ℝ) / ε < (N : ℝ) :=
    lt_of_lt_of_le hN₂ (by exact_mod_cast hN₂')
  have hN3r : 48 * (Ltot : ℝ) < (N : ℝ) :=
    lt_of_lt_of_le hN₃ (by exact_mod_cast hN₃')
  have hLnn : (0 : ℝ) ≤ (Ltot : ℝ) := by positivity
  set η : ℝ := trajFloorU1 N * (2 * ((nearQ c N).card : ℝ)) with hηdef
  have hcard : (2 : ℝ) * ((nearQ c N).card : ℝ) ≤ 24 * (Ltot : ℝ) := by
    have h' : ((nearQ c N).card : ℝ) ≤ 12 * (Ltot : ℝ) := by
      exact_mod_cast card_nearQ_le c N
    linarith
  have htraj : trajFloorU1 N ≤ 1 / ((N : ℝ) + 1) := by
    unfold trajFloorU1
    refine one_div_le_one_div_of_le (by positivity) ?_
    calc ((N : ℝ) + 1) = ((N : ℝ) + 1) ^ 1 := (pow_one _).symm
      _ ≤ ((N : ℝ) + 1) ^ 4 := by
        refine pow_le_pow_right₀ ?_ (by norm_num)
        have h : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast N.zero_le
        linarith
  have hηle : η ≤ 24 * (Ltot : ℝ) / ((N : ℝ) + 1) := by
    rw [hηdef]
    calc trajFloorU1 N * (2 * ((nearQ c N).card : ℝ))
        ≤ (1 / ((N : ℝ) + 1)) * (24 * (Ltot : ℝ)) :=
          mul_le_mul htraj hcard (by positivity) (by positivity)
      _ = 24 * (Ltot : ℝ) / ((N : ℝ) + 1) := by ring
  have hηhalf : η ≤ 1 / 2 := by
    refine le_trans hηle ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hN3r, hLnn]
  have hηε : η < ε / 4 := by
    refine lt_of_le_of_lt hηle ?_
    rw [div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
    have h96 : 96 * (Ltot : ℝ) < (N : ℝ) * ε := by
      rwa [div_lt_iff₀ hε] at hN2r
    nlinarith [h96, hε, hLnn]
  have hηnn : 0 ≤ η :=
    mul_nonneg (trajFloorU1_pos N).le (by positivity)
  have hmain : ‖finiteCorrelation (haarProb Circle) circleRep
        trajFloorU1 N k c - limitSystemMQ35 k c‖
      ≤ 2 * (1 - Real.exp (-η)) * Real.exp η := by
    rw [finiteCorrelation_eq_gibbsExpect_famObs, ← hN₁ N hN₁']
    exact near_far_bound c N (trajFloorU1 N) (trajFloorU1_pos N).le
  refine lt_of_le_of_lt hmain ?_
  have h1 : 1 - Real.exp (-η) ≤ η := by
    have h := Real.add_one_le_exp (-η)
    linarith
  have h2 : Real.exp η ≤ 2 := by
    have h3 : (1 : ℝ) - η ≤ Real.exp (-η) := by
      have h := Real.add_one_le_exp (-η)
      linarith
    have h4 : Real.exp η = (Real.exp (-η))⁻¹ := by
      rw [Real.exp_neg, inv_inv]
    rw [h4]
    refine le_trans (inv_anti₀
      (by linarith [hηhalf] : (0 : ℝ) < 1 - η) h3) ?_
    have h5 : ((1 : ℝ) - η)⁻¹ ≤ ((1 / 2 : ℝ))⁻¹ :=
      inv_anti₀ (by norm_num) (by linarith [hηhalf])
    refine le_trans h5 (by norm_num)
  calc 2 * (1 - Real.exp (-η)) * Real.exp η
      ≤ (2 * η) * 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2
          (Real.exp_nonneg η) (by linarith [hηnn])
    _ = 4 * η := by ring
    _ < ε := by linarith [hηε]

end CircleSeatConvergence

end ThetLogos
