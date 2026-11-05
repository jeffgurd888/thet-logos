import ThetLogos.LayerCubeRemainderPost

namespace ThetLogos

open Finset

/-!
# ThetLogos.LayerCubeRemainderSeat - REM-1: the closure-remainder
teeth and the naive-closure kill (working label)

**Status: two decided seat results at the frozen seat. NO CLAIM.
No Millennium statement, no ladder rung, no dial. Dial 2 = 0,
Dial 3 = 0. Finite seat values testify about the finite seat
only (K-GR-LAUNDER).**

Governing pack: `routeb-general-scratch/pack-rem-1.md`. The pin
REM-0 (`LayerCubeRemainderPost.lean`) has landed; its names
(`plaqDefectField`, `wrapHolonomy`, `wrapHolonomy1/2/3`,
`RemNaiveClosure`, `RemClosure`) are consumed here, never renamed
or extended (K-REM-FORK). The MAX pin's `plaqAngle` and
`gaugeAngle` are cited, never redefined. REM-CYCLE is not touched
by this brick (K-REM-MERGE).

**Seat (frozen):** Even `N`, `N = 4` - the smallest seat where the
landed edge-distinctness lemmas of `PlaquetteTelescoping.lean`
(`plaqEdgeR_ne_B`, `plaqEdgeL_ne_B`, `plaqEdgeT_ne_B`, at Even `N`,
`4 <= N`) hold.

## The two decisions

1. **The excitation value.** For the named plaquette datum
   `remSeatPlaq` at `N = 4` (base the zero site, directions
   `mu = 1`, `nu = 2`) and the single-plaquette excitation
   `singlePlaqExcitation P t` (value `t` on the bottom edge
   `plaqEdgeB P`, `0` on every other link), the plaquette angle
   is exactly `t`: `plaqAngle remSeatPlaq
   (singlePlaqExcitation remSeatPlaq t) = t`, for general
   `t : R`. The other three edges are distinct from the bottom
   edge by the landed distinctness lemmas, so their terms
   vanish. (BRIDGE-1: an exact Python recomputation of this
   seat arithmetic accompanies this brick in the scratch
   record, prefix `rem1-`.)

2. **The naive closure is KILLED at theorem grade
   (K-GR-STAB finding).** The constant direction field
   `constDirField` (value `1` on every link of spatial
   direction `1`, `0` on every other link) is flat at every
   plaquette - in any plaquette its direction's two edges
   contribute `+1` and `-1`, or none - yet it is not a
   gradient: its wrap holonomy in its own direction is
   `4 != 0`, while every gradient's wrap holonomy is `0` by
   the finite cyclic telescoping lemma `wrapHolonomy_gaugeAngle`,
   proved once in the general form REM-2 consumes (any `N`,
   any spatial direction, any base site, any potential).
   Hence `RemNaiveClosure 4` is false:
   `remNaiveClosure_four_not`.

   **Scoping-grade remark (on the face, not a theorem):** the
   counterexample is uniform in `N >= 2` - the same constant
   direction field is flat at every plaquette at any `N`, and
   its wrap sum in its own direction is `N != 0`. The
   theorem-grade kill above is at the frozen seat `N = 4`;
   this uniformity sentence is scoping-grade and is not
   smuggled as a theorem. The seat is not narrowed to hide
   the kill: the death of the naive closure is the finding
   (flatness does not imply pure gauge on this base - the
   base carries a global remainder no plaquette can see).

Landing sentence (the dossier's): "On the finite base, balance
can fail locally with an exact value at a named plaquette, and
flatness does not imply pure gauge - the base carries a global
remainder no plaquette can see."
-/

section RemSeatData

/-- The zero layer site at `N = 4`: the site whose coordinates
are all `0` (its time coordinate is `0`, as a layer site
requires). -/
def remSeatSite0 : LayerSite 4 :=
  ⟨0, by simp⟩

/-- **The named seat plaquette datum `P0`** at `N = 4`: base the
zero site, directions `mu = 1`, `nu = 2`. -/
def remSeatPlaq : PlaqDatum 4 :=
  ⟨remSeatSite0, 1, 2, by decide, by decide, by decide⟩

end RemSeatData

section RemExcitation

open Classical in
/-- **The single-plaquette excitation**: the link angle that is
`t` on the bottom edge `plaqEdgeB P` of the plaquette datum `P`
and `0` on every other link. (Link equality is not decidable
in the corpus, so the definition is under classical
decidability, as with the MAX pin's `allPlaqData`.) -/
noncomputable def singlePlaqExcitation {N : ℕ} [NeZero N] (P : PlaqDatum N)
    (t : ℝ) : linkAngle N :=
  fun ℓ => if ℓ = plaqEdgeB P then t else 0

/-- The excitation's value on the bottom edge is `t`. -/
theorem singlePlaqExcitation_apply_B {N : ℕ} [NeZero N]
    (P : PlaqDatum N) (t : ℝ) :
    singlePlaqExcitation P t (plaqEdgeB P) = t := by
  classical
  simp [singlePlaqExcitation]

/-- The excitation vanishes on every link other than the bottom
edge. -/
theorem singlePlaqExcitation_apply_of_ne {N : ℕ} [NeZero N]
    (P : PlaqDatum N) (t : ℝ) {ℓ : LayerLink N}
    (hℓ : ℓ ≠ plaqEdgeB P) :
    singlePlaqExcitation P t ℓ = 0 := by
  classical
  simp [singlePlaqExcitation, hℓ]

/-- **The excitation value, general plaquette form.** At Even
`N` with `4 <= N`, the single-plaquette excitation at any
plaquette datum `P` has plaquette angle exactly `t` at `P`:
the bottom edge contributes `t` and the other three edges are
distinct from it (the landed distinctness lemmas
`plaqEdgeR_ne_B`, `plaqEdgeT_ne_B`, `plaqEdgeL_ne_B`), so their
terms vanish. -/
theorem plaqAngle_singlePlaqExcitation {N : ℕ} [NeZero N]
    (hN : Even N) (h4N : 4 ≤ N) (P : PlaqDatum N) (t : ℝ) :
    plaqAngle P (singlePlaqExcitation P t) = t := by
  rw [plaqAngle, singlePlaqExcitation_apply_B,
    singlePlaqExcitation_apply_of_ne P t (plaqEdgeR_ne_B P),
    singlePlaqExcitation_apply_of_ne P t
      (plaqEdgeT_ne_B hN h4N P),
    singlePlaqExcitation_apply_of_ne P t (plaqEdgeL_ne_B P)]
  ring

/-- **Decision 1 at the frozen seat.** The single-plaquette
excitation at the named datum `remSeatPlaq` (`N = 4`) has
plaquette angle exactly `t`: balance can fail locally with an
exact value at a named plaquette. -/
theorem remSeat_excitation_angle (t : ℝ) :
    plaqAngle remSeatPlaq (singlePlaqExcitation remSeatPlaq t)
      = t :=
  plaqAngle_singlePlaqExcitation ⟨2, rfl⟩ (by norm_num) _ t

/-- Seat corollary: for `t != 0` the excitation's plaquette
angle at `remSeatPlaq` is nonzero - the defect field
`plaqDefectField` of the REM-0 pin attains the exact nonzero
value `t` there. -/
theorem remSeat_excitation_nonzero {t : ℝ} (ht : t ≠ 0) :
    plaqDefectField (singlePlaqExcitation remSeatPlaq t)
        remSeatPlaq ≠ 0 := by
  rw [plaqDefectField_apply, remSeat_excitation_angle]
  exact ht

end RemExcitation

section RemConstDirField

/-- **The constant direction field**: the link angle that is
`1` on every link whose spatial direction is `1` and `0` on
every other link. This is the counterexample field of the
naive-closure kill. -/
def constDirField {N : ℕ} [NeZero N] : linkAngle N :=
  fun ℓ => if ℓ.1.2 = 1 then (1 : ℝ) else 0

/-- The constant direction field on the bottom edge of a
plaquette reads the direction indicator of `P.mu`. -/
theorem constDirField_plaqEdgeB {N : ℕ} [NeZero N]
    (P : PlaqDatum N) :
    constDirField (plaqEdgeB P) = if P.mu = 1 then (1 : ℝ) else 0 :=
  rfl

/-- The constant direction field on the right edge of a
plaquette reads the direction indicator of `P.nu`. -/
theorem constDirField_plaqEdgeR {N : ℕ} [NeZero N]
    (P : PlaqDatum N) :
    constDirField (plaqEdgeR P) = if P.nu = 1 then (1 : ℝ) else 0 :=
  rfl

/-- The constant direction field on the top edge of a
plaquette reads the direction indicator of `P.mu`. -/
theorem constDirField_plaqEdgeT {N : ℕ} [NeZero N]
    (P : PlaqDatum N) :
    constDirField (plaqEdgeT P) = if P.mu = 1 then (1 : ℝ) else 0 :=
  rfl

/-- The constant direction field on the left edge of a
plaquette reads the direction indicator of `P.nu`. -/
theorem constDirField_plaqEdgeL {N : ℕ} [NeZero N]
    (P : PlaqDatum N) :
    constDirField (plaqEdgeL P) = if P.nu = 1 then (1 : ℝ) else 0 :=
  rfl

/-- **Flatness of the constant direction field**, at any
plaquette datum of any layer: the direction-`1` edges of a
plaquette are its bottom and top edges (direction `P.mu`,
contributing `+` and `-`) and its right and left edges
(direction `P.nu`, contributing `+` and `-`); if the direction
is absent all four terms are `0`. In every case the plaquette
angle is `0`. -/
theorem plaqAngle_constDirField {N : ℕ} [NeZero N]
    (P : PlaqDatum N) :
    plaqAngle P (constDirField (N := N)) = 0 := by
  rw [plaqAngle, constDirField_plaqEdgeB, constDirField_plaqEdgeR,
    constDirField_plaqEdgeT, constDirField_plaqEdgeL]
  ring

/-- **Flatness at the frozen seat**, in the enumeration form
the naive closure quantifies over: the constant direction
field at `N = 4` is flat at every `P` in `allPlaqData 4`. -/
theorem constDirField_flat_four :
    ∀ P ∈ allPlaqData 4,
      plaqAngle P (constDirField (N := 4)) = 0 :=
  fun P _ => plaqAngle_constDirField P

/-- **The constant direction field's wrap holonomy in its own
direction is `4` at `N = 4`**, at every base site: each of the
four links of the direction-`1` coordinate cycle carries the
value `1`. -/
theorem wrapHolonomy1_constDirField (c : LayerSite 4) :
    wrapHolonomy1 (constDirField (N := 4)) c = 4 := by
  have hterm : ∀ k ∈ Finset.range 4,
      (constDirField (N := 4))
          (layerLinkOf ((layerShift (1 : Fin 4) (by decide))^[k] c)
            (1 : Fin 4) (by decide)) = (1 : ℝ) := by
    intro k _
    rfl
  rw [wrapHolonomy1_apply, wrapHolonomy_apply,
    Finset.sum_congr rfl hterm]
  simp

end RemConstDirField

section RemTelescoping

/-- Coordinate formula for iterated layer shifts: after `k`
shifts in direction `nu`, the `j`-th coordinate of a site is
its original `j`-th coordinate plus `k` (in `ZMod N`) if
`j = nu`, and is unchanged otherwise. -/
theorem layerShift_iterate_apply {N : ℕ} [NeZero N]
    (ν : Fin 4) (hν : ν ≠ 0) (c : LayerSite N) :
    ∀ k : ℕ, ∀ j : Fin 4,
      ((layerShift ν hν)^[k] c).1 j
        = c.1 j + (if j = ν then (k : ZMod N) else 0) := by
  intro k
  induction k with
  | zero => intro j; simp
  | succ k ih =>
    intro j
    rw [Function.iterate_succ_apply']
    show (torusShift N ν (((layerShift ν hν)^[k] c).1)) j = _
    rw [torusShift_apply, Pi.add_apply, ih j]
    by_cases hj : j = ν
    · subst hj
      rw [Pi.single_eq_same]
      simp only [ite_true]
      push_cast
      ring
    · rw [Pi.single_eq_of_ne hj]
      simp only [hj, ite_false]
      simp

/-- **The coordinate cycle closes**: `N` successive layer
shifts in a spatial direction return every layer site to
itself, because the shifted coordinate has advanced by
`(N : ZMod N) = 0`. -/
theorem layerShift_iterate_N {N : ℕ} [NeZero N]
    (ν : Fin 4) (hν : ν ≠ 0) (c : LayerSite N) :
    (layerShift ν hν)^[N] c = c := by
  apply Subtype.ext
  funext j
  rw [layerShift_iterate_apply ν hν c N j]
  simp

/-- The tail of the layer link over a site is the site. -/
theorem linkTail_layerLinkOf_seat {N : ℕ} [NeZero N]
    (s : LayerSite N) (ν : Fin 4) (hν : ν ≠ 0) :
    linkTail (layerLinkOf s ν hν) = s :=
  rfl

/-- The head of the layer link over a site is the site shifted
in the link's direction. -/
theorem linkHead_layerLinkOf_seat {N : ℕ} [NeZero N]
    (s : LayerSite N) (ν : Fin 4) (hν : ν ≠ 0) :
    linkHead (layerLinkOf s ν hν) = layerShift ν hν s :=
  rfl

/-- A gradient's value on the `k`-th link of a coordinate
cycle is the difference of the potential at successive sites
of the cycle: the `(k+1)`-th site minus the `k`-th. -/
theorem gaugeAngle_wrap_link {N : ℕ} [NeZero N]
    (φ : LayerSite N → ℝ) (ν : Fin 4) (hν : ν ≠ 0)
    (c : LayerSite N) (k : ℕ) :
    gaugeAngle φ (layerLinkOf ((layerShift ν hν)^[k] c) ν hν)
      = φ ((layerShift ν hν)^[k + 1] c)
        - φ ((layerShift ν hν)^[k] c) := by
  show φ (linkHead (layerLinkOf ((layerShift ν hν)^[k] c) ν hν))
      - φ (linkTail (layerLinkOf ((layerShift ν hν)^[k] c) ν hν))
    = _
  rw [linkHead_layerLinkOf_seat, linkTail_layerLinkOf_seat,
    Function.iterate_succ_apply']

/-- **Telescoping of successive potential differences** along
a coordinate cycle, by induction on the number of steps: the
sum of `phi` differences between successive sites of the cycle
is the last site's value minus the first. -/
theorem sum_range_gaugeAngle_telescope {N : ℕ} [NeZero N]
    (φ : LayerSite N → ℝ) (ν : Fin 4) (hν : ν ≠ 0)
    (c : LayerSite N) :
    ∀ n : ℕ, ∑ k ∈ Finset.range n,
        (φ ((layerShift ν hν)^[k + 1] c)
          - φ ((layerShift ν hν)^[k] c))
      = φ ((layerShift ν hν)^[n] c) - φ c := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- **The finite cyclic telescoping lemma** (the general form
REM-2 consumes): for every layer size `N`, every site
potential `phi`, every spatial direction `nu` and every base
site `c`, the wrap holonomy of the gradient `gaugeAngle phi`
around the coordinate cycle through `c` in direction `nu` is
`0` - the sum over the cycle is the telescoping sum of
successive potential differences
(`sum_range_gaugeAngle_telescope`), and the cycle closes
after `N` steps (`layerShift_iterate_N`), so the sum is
`phi c - phi c = 0`. -/
theorem wrapHolonomy_gaugeAngle {N : ℕ} [NeZero N]
    (φ : LayerSite N → ℝ) (ν : Fin 4) (hν : ν ≠ 0)
    (c : LayerSite N) :
    wrapHolonomy (gaugeAngle φ) ν hν c = 0 := by
  have hterm : ∀ k ∈ Finset.range N,
      gaugeAngle φ (layerLinkOf ((layerShift ν hν)^[k] c) ν hν)
        = φ ((layerShift ν hν)^[k + 1] c)
          - φ ((layerShift ν hν)^[k] c) :=
    fun k _ => gaugeAngle_wrap_link φ ν hν c k
  rw [wrapHolonomy_apply, Finset.sum_congr rfl hterm,
    sum_range_gaugeAngle_telescope, layerShift_iterate_N,
    sub_self]

end RemTelescoping

section RemNaiveKill

/-- **Decision 2: `RemNaiveClosure` is KILLED at theorem grade
at the frozen seat `N = 4` (K-GR-STAB finding).** The constant
direction field `constDirField` is flat at every plaquette of
`allPlaqData 4` (`constDirField_flat_four`), so the naive
closure would make it a gradient `gaugeAngle phi`; but its
wrap holonomy in direction `1` is `4`
(`wrapHolonomy1_constDirField`) while every gradient's wrap
holonomy is `0` (`wrapHolonomy_gaugeAngle`) - contradiction.
Flatness does not imply pure gauge on this base. -/
theorem remNaiveClosure_four_not : ¬ RemNaiveClosure 4 := by
  rw [remNaiveClosure_iff]
  intro h
  obtain ⟨φ, hφ⟩ := h (constDirField (N := 4))
    constDirField_flat_four
  have h1 : wrapHolonomy1 (constDirField (N := 4)) remSeatSite0
      = 4 :=
    wrapHolonomy1_constDirField remSeatSite0
  have h2 : wrapHolonomy1 (gaugeAngle φ) remSeatSite0 = 0 := by
    rw [wrapHolonomy1_apply]
    exact wrapHolonomy_gaugeAngle φ 1 (by decide) remSeatSite0
  rw [hφ] at h1
  rw [h2] at h1
  norm_num at h1

end RemNaiveKill

end ThetLogos
