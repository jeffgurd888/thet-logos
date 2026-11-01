import ThetLogos.LayerCubeRemainderSeat
import ThetLogos.MaxwellQuadAssembly
import ThetLogos.LayerCubeDistance

namespace ThetLogos

open Finset

/-!
# ThetLogos.LayerCubeRemainderClosure - REM-2: the corrected
closure characterization at general even N (working label)

**Status: REM-2 landing brick. NO CLAIM. No Millennium
statement, no ladder rung, no dial. Dial 2 = 0, Dial 3 = 0.
Finite seat values testify about the finite seat only.**

Governing pack: `routeb-general-scratch/pack-rem-2.md`. The
pin REM-0 (`LayerCubeRemainderPost.lean`) has landed; its
registered Prop `RemClosure` is discharged here in its exact
registered form, never restated or forked (K-REM-FORK). REM-1
(`LayerCubeRemainderSeat.lean`) supplies the telescoping lemma
`wrapHolonomy_gaugeAngle` in reusable form, and MAX-2
(`MaxwellQuadAssembly.lean`) supplies M3, `maxwellM3_proved`:
gauge modes are flat. REM-CONFIG only; the cycle side is not
touched (K-REM-MERGE). The naive closure stays dead (REM-1's
kill stands).

## The statement discharged

`remClosure_proved`: at general even `N`, `RemClosure N` -
for every link configuration `theta`, flatness at every
plaquette datum together with vanishing of all three wrap
holonomies at every base site holds if and only if
`theta = gaugeAngle phi` for some site potential `phi`.

## Proof route (forward direction)

The potential is built by path integration from the root
site: `remPotential theta c` sums `theta` along the
coordinate path that first walks direction `1` for
`(c.1 1).val` steps, then direction `2` for `(c.1 2).val`
steps, then direction `3` for `(c.1 3).val` steps
(`stepSum` is the sum along one straight run). The
plaquette relation (`flat_swap`) says the two orders of a
unit square carry the same total; summed along a run it
gives the run-shift identity `stepSum_shift_base`, and
iterated, `stepSum_iterate_base`. Those identities move the
later runs when an earlier coordinate is stepped, and the
telescoped totals leave exactly the link's own value. When
the stepped coordinate wraps (its value is `N - 1`), the
same identities reduce the difference to a partial wrap sum,
and the vanishing wrap holonomy at the wrapped site closes
it. The backward direction is M3 (flatness of gradients)
plus REM-1's telescoping (wrap holonomies of gradients
vanish).
-/

section Infrastructure

variable {N : ℕ} [NeZero N]

/-- The root site: all coordinates `0`. -/
def remRoot (N : ℕ) [NeZero N] : LayerSite N :=
  ⟨0, by simp⟩

/-- The root site's underlying function is `0`. -/
theorem remRoot_coe : (remRoot N).1 = 0 :=
  rfl

/-- Layer shifts in two directions commute. -/
theorem layerShift_comm_gen {μ ν : Fin 4} (hμ : μ ≠ 0)
    (hν : ν ≠ 0) (c : LayerSite N) :
    layerShift μ hμ (layerShift ν hν c)
      = layerShift ν hν (layerShift μ hμ c) := by
  apply Subtype.ext
  show torusShift N μ (torusShift N ν c.1)
    = torusShift N ν (torusShift N μ c.1)
  exact torusShift_comm N μ ν c.1

/-- Iterates of one layer shift commute past a single shift
in another direction. -/
theorem layerShift_iterate_commute {μ ν : Fin 4} (hμ : μ ≠ 0)
    (hν : ν ≠ 0) (c : LayerSite N) :
    ∀ k : ℕ, (layerShift μ hμ)^[k] (layerShift ν hν c)
      = layerShift ν hν ((layerShift μ hμ)^[k] c) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have step1 : (layerShift μ hμ)^[k + 1] (layerShift ν hν c)
        = layerShift μ hμ ((layerShift μ hμ)^[k]
            (layerShift ν hν c)) :=
      Function.iterate_succ_apply' _ _ _
    have step2 : layerShift μ hμ ((layerShift μ hμ)^[k] c)
        = (layerShift μ hμ)^[k + 1] c :=
      (Function.iterate_succ_apply' _ _ _).symm
    rw [step1, ih, layerShift_comm_gen hμ hν, step2]

/-- Iterates of two layer shifts commute. -/
theorem layerShift_iterate_iterate_commute {μ ν : Fin 4}
    (hμ : μ ≠ 0) (hν : ν ≠ 0) (c : LayerSite N) :
    ∀ m n : ℕ, (layerShift μ hμ)^[m] ((layerShift ν hν)^[n] c)
      = (layerShift ν hν)^[n] ((layerShift μ hμ)^[m] c) := by
  intro m
  induction m with
  | zero => intro n; rfl
  | succ m ih =>
    intro n
    have step1 : (layerShift μ hμ)^[m + 1] ((layerShift ν hν)^[n] c)
        = layerShift μ hμ ((layerShift μ hμ)^[m]
            ((layerShift ν hν)^[n] c)) :=
      Function.iterate_succ_apply' _ _ _
    have step2 : layerShift μ hμ ((layerShift μ hμ)^[m] c)
        = (layerShift μ hμ)^[m + 1] c :=
      (Function.iterate_succ_apply' _ _ _).symm
    rw [step1, ih n,
      (layerShift_iterate_commute hν hμ
        ((layerShift μ hμ)^[m] c) n).symm,
      step2]

/-- **The run sum**: the sum of `theta` along the straight
run of `n` links in direction `nu` starting at the site `s`:
`sum over k < n of theta` at the link over the `k`-th
iterate of `s`. This is the wrap holonomy's summand shape:
at `n = N` it is the wrap holonomy itself. -/
def stepSum {N : ℕ} [NeZero N] (θ : linkAngle N)
    (ν : Fin 4) (hν : ν ≠ 0) (s : LayerSite N) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    θ (layerLinkOf ((layerShift ν hν)^[k] s) ν hν)

/-- Read-back: the run sum is its defining sum. -/
theorem stepSum_apply {N : ℕ} [NeZero N] (θ : linkAngle N)
    (ν : Fin 4) (hν : ν ≠ 0) (s : LayerSite N) (n : ℕ) :
    stepSum θ ν hν s n
      = ∑ k ∈ Finset.range n,
          θ (layerLinkOf ((layerShift ν hν)^[k] s) ν hν) :=
  rfl

/-- The run sum at length `N` is the wrap holonomy. -/
theorem stepSum_eq_wrapHolonomy {N : ℕ} [NeZero N]
    (θ : linkAngle N) (ν : Fin 4) (hν : ν ≠ 0)
    (s : LayerSite N) :
    stepSum θ ν hν s N = wrapHolonomy θ ν hν s :=
  rfl

/-- The run sum of length `0` is `0`. -/
theorem stepSum_zero {N : ℕ} [NeZero N] (θ : linkAngle N)
    (ν : Fin 4) (hν : ν ≠ 0) (s : LayerSite N) :
    stepSum θ ν hν s 0 = 0 := by
  simp [stepSum]

/-- The run sum of length `n + 1` is the run sum of length
`n` plus the last link's value. -/
theorem stepSum_succ {N : ℕ} [NeZero N] (θ : linkAngle N)
    (ν : Fin 4) (hν : ν ≠ 0) (s : LayerSite N) (n : ℕ) :
    stepSum θ ν hν s (n + 1)
      = stepSum θ ν hν s n
        + θ (layerLinkOf ((layerShift ν hν)^[n] s) ν hν) := by
  rw [stepSum_apply, Finset.sum_range_succ]
  rfl

end Infrastructure

section Potential

variable {N : ℕ} [NeZero N]

/-- **The path-integrated potential**: `remPotential theta c`
is the sum of `theta` along the coordinate path from the
root site to `c` that walks direction `1` first (for
`(c.1 1).val` steps), then direction `2` (for `(c.1 2).val`
steps from the end of the first run), then direction `3`
(for `(c.1 3).val` steps from the end of the second run). -/
def remPotential (θ : linkAngle N) (c : LayerSite N) : ℝ :=
  stepSum θ 1 (by decide) (remRoot N) (c.1 1).val
    + stepSum θ 2 (by decide)
        ((layerShift 1 (by decide))^[(c.1 1).val] (remRoot N))
        (c.1 2).val
    + stepSum θ 3 (by decide)
        ((layerShift 2 (by decide))^[(c.1 2).val]
          ((layerShift 1 (by decide))^[(c.1 1).val] (remRoot N)))
        (c.1 3).val

/-- Read-back: the potential is its defining three-run sum. -/
theorem remPotential_apply (θ : linkAngle N) (c : LayerSite N) :
    remPotential θ c =
      stepSum θ 1 (by decide) (remRoot N) (c.1 1).val
        + stepSum θ 2 (by decide)
            ((layerShift 1 (by decide))^[(c.1 1).val] (remRoot N))
            (c.1 2).val
        + stepSum θ 3 (by decide)
            ((layerShift 2 (by decide))^[(c.1 2).val]
              ((layerShift 1 (by decide))^[(c.1 1).val]
                (remRoot N)))
            (c.1 3).val :=
  rfl

/-- **Site representation**: every site is reached from the
root by its three coordinate runs, in the potential's order:
first `(c.1 1).val` steps in direction `1`, then
`(c.1 2).val` steps in direction `2`, then `(c.1 3).val`
steps in direction `3`. -/
theorem site_eq_runs (c : LayerSite N) :
    c = (layerShift 3 (by decide))^[(c.1 3).val]
          ((layerShift 2 (by decide))^[(c.1 2).val]
            ((layerShift 1 (by decide))^[(c.1 1).val]
              (remRoot N))) := by
  apply Subtype.ext
  funext j
  fin_cases j
  · -- coordinate 0: no spatial shift moves it, and `c.1 0 = 0`
    rw [layerShift_iterate_apply, layerShift_iterate_apply,
      layerShift_iterate_apply]
    simp [layerSite_zero c, remRoot_coe]
  · -- coordinate 1: only the first run moves it, by its value
    rw [layerShift_iterate_apply, layerShift_iterate_apply,
      layerShift_iterate_apply]
    simp [remRoot_coe]
  · -- coordinate 2: only the second run moves it
    rw [layerShift_iterate_apply, layerShift_iterate_apply,
      layerShift_iterate_apply]
    simp [remRoot_coe]
  · -- coordinate 3: only the third run moves it
    rw [layerShift_iterate_apply, layerShift_iterate_apply,
      layerShift_iterate_apply]
    simp [remRoot_coe]

/-- The value of the stepped site's own coordinate. -/
theorem val_shift_self (ν : Fin 4) (hν : ν ≠ 0)
    (c : LayerSite N) :
    ((layerShift ν hν c).1 ν).val
      = if (c.1 ν).val + 1 < N then (c.1 ν).val + 1 else 0 := by
  rw [plaqShift_apply_self, add_comm (1 : ZMod N)]
  exact zmod_val_add_one (c.1 ν)

/-- The value of the stepped site's other coordinates is
unchanged. -/
theorem val_shift_of_ne {μ ν : Fin 4} (h : ν ≠ μ) (hμ : μ ≠ 0)
    (c : LayerSite N) :
    ((layerShift μ hμ c).1 ν).val = (c.1 ν).val := by
  rw [plaqShift_apply_of_ne h hμ]

end Potential

section FlatSwap

variable {N : ℕ} [NeZero N] {θ : linkAngle N}

/-- **The plaquette relation in run form**: under flatness,
the two orders of a unit square carry the same total:
`theta` at the `mu` link over `s` plus `theta` at the `nu`
link over the `mu`-shift of `s` equals `theta` at the `mu`
link over the `nu`-shift of `s` plus `theta` at the `nu`
link over `s`. This is `plaqAngle` at the datum
`(s; mu, nu)` read through the edge definitions. -/
theorem flat_swap (hflat : ∀ P : PlaqDatum N, plaqAngle P θ = 0)
    (s : LayerSite N) {μ ν : Fin 4} (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hne : μ ≠ ν) :
    θ (layerLinkOf s μ hμ)
        + θ (layerLinkOf (layerShift μ hμ s) ν hν)
      = θ (layerLinkOf (layerShift ν hν s) μ hμ)
        + θ (layerLinkOf s ν hν) := by
  have h := hflat ⟨s, μ, ν, hμ, hν, hne⟩
  rw [plaqAngle] at h
  have eB : plaqEdgeB ⟨s, μ, ν, hμ, hν, hne⟩
      = layerLinkOf s μ hμ := rfl
  have eR : plaqEdgeR ⟨s, μ, ν, hμ, hν, hne⟩
      = layerLinkOf (layerShift μ hμ s) ν hν := rfl
  have eT : plaqEdgeT ⟨s, μ, ν, hμ, hν, hne⟩
      = layerLinkOf (layerShift ν hν s) μ hμ := rfl
  have eL : plaqEdgeL ⟨s, μ, ν, hμ, hν, hne⟩
      = layerLinkOf s ν hν := rfl
  rw [eB, eR, eT, eL] at h
  linarith

/-- **The run-shift identity**: shifting a run's base site
by one step in a transverse direction `mu` changes the
`nu`-run sum by exactly the difference of the `mu` values
at the run's two ends. Induction on the run length, one
plaquette relation (`flat_swap`) per step. -/
theorem stepSum_shift_base
    (hflat : ∀ P : PlaqDatum N, plaqAngle P θ = 0)
    {μ ν : Fin 4} (hμ : μ ≠ 0) (hν : ν ≠ 0) (hne : μ ≠ ν)
    (s : LayerSite N) :
    ∀ n : ℕ, stepSum θ ν hν (layerShift μ hμ s) n
      = stepSum θ ν hν s n
        + (θ (layerLinkOf ((layerShift ν hν)^[n] s) μ hμ)
          - θ (layerLinkOf s μ hμ)) := by
  intro n
  induction n with
  | zero =>
    simp [stepSum_zero]
  | succ n ih =>
    have hcomm : ∀ k : ℕ, (layerShift ν hν)^[k] (layerShift μ hμ s)
        = layerShift μ hμ ((layerShift ν hν)^[k] s) :=
      fun k => layerShift_iterate_commute hν hμ s k
    have hsum : stepSum θ ν hν (layerShift μ hμ s) (n + 1)
        = stepSum θ ν hν (layerShift μ hμ s) n
          + θ (layerLinkOf
              (layerShift μ hμ ((layerShift ν hν)^[n] s)) ν hν) := by
      rw [stepSum_succ, hcomm n]
    have hplaq := flat_swap hflat ((layerShift ν hν)^[n] s)
      hμ hν hne
    rw [hsum, ih, stepSum_succ]
    have hsucc : (layerShift ν hν)^[n + 1] s
        = layerShift ν hν ((layerShift ν hν)^[n] s) :=
      Function.iterate_succ_apply' _ _ _
    rw [hsucc]
    linarith

/-- **The iterated run-shift identity**: shifting a run's
base site by `m` steps in a transverse direction `mu`
changes the `nu`-run sum by the sum, over the `m` steps, of
the end differences of `stepSum_shift_base`. -/
theorem stepSum_iterate_base
    (hflat : ∀ P : PlaqDatum N, plaqAngle P θ = 0)
    {μ ν : Fin 4} (hμ : μ ≠ 0) (hν : ν ≠ 0) (hne : μ ≠ ν)
    (s : LayerSite N) (n : ℕ) :
    ∀ m : ℕ, stepSum θ ν hν ((layerShift μ hμ)^[m] s) n
      = stepSum θ ν hν s n
        + ∑ i ∈ Finset.range m,
            (θ (layerLinkOf
                ((layerShift ν hν)^[n] ((layerShift μ hμ)^[i] s))
                μ hμ)
              - θ (layerLinkOf ((layerShift μ hμ)^[i] s) μ hμ)) := by
  intro m
  induction m with
  | zero => simp [stepSum]
  | succ m ih =>
    have h1 : (layerShift μ hμ)^[m + 1] s
        = layerShift μ hμ ((layerShift μ hμ)^[m] s) :=
      Function.iterate_succ_apply' _ _ _
    rw [h1, stepSum_shift_base hflat hμ hν hne _ n, ih,
      Finset.sum_range_succ]
    ring

/-- **Partial wrap extraction**: if the run sum of length
`N` at `s` vanishes and `N = m + 1` and the `m`-th iterate
of `s` is `c`, then the run sum of length `m` at `s` is
minus the value at `c`. -/
theorem stepSum_eq_neg_of_wrap {ν : Fin 4} (hν : ν ≠ 0)
    {s c : LayerSite N} {m : ℕ} (hN : N = m + 1)
    (hwrap : stepSum θ ν hν s N = 0)
    (hlast : (layerShift ν hν)^[m] s = c) :
    stepSum θ ν hν s m = - θ (layerLinkOf c ν hν) := by
  have h := stepSum_succ θ ν hν s m
  rw [← hN] at h
  rw [hwrap, hlast] at h
  linarith

end FlatSwap

section Increment

variable {N : ℕ} [NeZero N] {θ : linkAngle N}

/-- A nonzero direction of `Fin 4` is `1`, `2`, or `3`. -/
theorem fin4_ne_zero_cases (ν : Fin 4) (hν : ν ≠ 0) :
    ν = 1 ∨ ν = 2 ∨ ν = 3 := by
  fin_cases ν
  · exact absurd rfl hν
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- **Direction-1 increment**: stepping a site in direction
`1` changes the potential by exactly the link's value.
Non-wrap case: the first run gains one link, and the
second and third runs shift by one step in direction `1`
(`stepSum_shift_base` twice); the telescoped differences
cancel against the gained link except at the target site.
Wrap case: the first run empties, the second and third
runs fall back to the root column (`stepSum_iterate_base`
twice), and the difference reduces to a partial wrap sum,
closed by the vanishing wrap holonomy at the wrapped site. -/
theorem potential_incr1
    (hflat : ∀ P : PlaqDatum N, plaqAngle P θ = 0)
    (hwrap : ∀ c : LayerSite N, wrapHolonomy1 θ c = 0 ∧
      wrapHolonomy2 θ c = 0 ∧ wrapHolonomy3 θ c = 0)
    (c : LayerSite N) :
    remPotential θ (layerShift 1 (by decide) c)
      = remPotential θ c + θ (layerLinkOf c 1 (by decide)) := by
  have hval_lt : (c.1 1).val < N := ZMod.val_lt _
  by_cases hcase : (c.1 1).val + 1 < N
  · have hval1 : ((layerShift 1 (by decide) c).1 1).val
        = (c.1 1).val + 1 := by
      have h := val_shift_self (1 : Fin 4) (by decide) c
      rw [if_pos hcase] at h
      exact h
    have hval2 : ((layerShift 1 (by decide) c).1 2).val
        = (c.1 2).val :=
      val_shift_of_ne (show (2 : Fin 4) ≠ 1 by decide)
        (show (1 : Fin 4) ≠ 0 by decide) c
    have hval3 : ((layerShift 1 (by decide) c).1 3).val
        = (c.1 3).val :=
      val_shift_of_ne (show (3 : Fin 4) ≠ 1 by decide)
        (show (1 : Fin 4) ≠ 0 by decide) c
    rw [remPotential_apply, remPotential_apply, hval1, hval2, hval3]
    have hS1succ : (layerShift 1 (by decide))^[(c.1 1).val + 1]
          (remRoot N)
        = layerShift 1 (by decide)
            ((layerShift 1 (by decide))^[(c.1 1).val] (remRoot N)) :=
      Function.iterate_succ_apply' _ _ _
    rw [hS1succ]
    have hbase3 : (layerShift 2 (by decide))^[(c.1 2).val]
          (layerShift 1 (by decide)
            ((layerShift 1 (by decide))^[(c.1 1).val] (remRoot N)))
        = layerShift 1 (by decide)
            ((layerShift 2 (by decide))^[(c.1 2).val]
              ((layerShift 1 (by decide))^[(c.1 1).val]
                (remRoot N))) :=
      layerShift_iterate_commute (by decide) (by decide) _ _
    rw [hbase3]
    have hS1 := stepSum_succ θ 1 (by decide) (remRoot N)
      (c.1 1).val
    have hB2 := stepSum_shift_base (μ := 1) (ν := 2) hflat
      (by decide) (by decide) (by decide)
      ((layerShift 1 (by decide))^[(c.1 1).val] (remRoot N))
      (c.1 2).val
    have hB3 := stepSum_shift_base (μ := 1) (ν := 3) hflat
      (by decide) (by decide) (by decide)
      ((layerShift 2 (by decide))^[(c.1 2).val]
        ((layerShift 1 (by decide))^[(c.1 1).val] (remRoot N)))
      (c.1 3).val
    rw [← site_eq_runs c] at hB3
    rw [hS1, hB2, hB3]
    ring
  · have hN1 : (c.1 1).val + 1 = N := by omega
    have hval1 : ((layerShift 1 (by decide) c).1 1).val = 0 := by
      have h := val_shift_self (1 : Fin 4) (by decide) c
      rw [if_neg hcase] at h
      exact h
    have hval2 : ((layerShift 1 (by decide) c).1 2).val
        = (c.1 2).val :=
      val_shift_of_ne (show (2 : Fin 4) ≠ 1 by decide)
        (show (1 : Fin 4) ≠ 0 by decide) c
    have hval3 : ((layerShift 1 (by decide) c).1 3).val
        = (c.1 3).val :=
      val_shift_of_ne (show (3 : Fin 4) ≠ 1 by decide)
        (show (1 : Fin 4) ≠ 0 by decide) c
    rw [remPotential_apply, remPotential_apply, hval1, hval2, hval3]
    rw [stepSum_zero, Function.iterate_zero_apply]
    have hbase : (layerShift 2 (by decide))^[(c.1 2).val]
          ((layerShift 1 (by decide))^[(c.1 1).val] (remRoot N))
        = (layerShift 1 (by decide))^[(c.1 1).val]
            ((layerShift 2 (by decide))^[(c.1 2).val] (remRoot N)) :=
      layerShift_iterate_iterate_commute (by decide) (by decide) _ _ _
    rw [hbase]
    have hC2 := stepSum_iterate_base (μ := 1) (ν := 2) hflat
      (by decide) (by decide) (by decide) (remRoot N)
      (c.1 2).val (c.1 1).val
    have hC3 := stepSum_iterate_base (μ := 1) (ν := 3) hflat
      (by decide) (by decide) (by decide)
      ((layerShift 2 (by decide))^[(c.1 2).val] (remRoot N))
      (c.1 3).val (c.1 1).val
    have hsumSub2 : (∑ i ∈ Finset.range (c.1 1).val,
          (θ (layerLinkOf ((layerShift 2 (by decide))^[(c.1 2).val]
              ((layerShift 1 (by decide))^[i] (remRoot N)))
              1 (by decide))
            - θ (layerLinkOf ((layerShift 1 (by decide))^[i]
                (remRoot N)) 1 (by decide))))
        = (∑ i ∈ Finset.range (c.1 1).val,
            θ (layerLinkOf ((layerShift 2 (by decide))^[(c.1 2).val]
                ((layerShift 1 (by decide))^[i] (remRoot N)))
                1 (by decide)))
          - (∑ i ∈ Finset.range (c.1 1).val,
            θ (layerLinkOf ((layerShift 1 (by decide))^[i]
                (remRoot N)) 1 (by decide))) :=
      by rw [Finset.sum_sub_distrib]
    have hsumSub3 : (∑ i ∈ Finset.range (c.1 1).val,
          (θ (layerLinkOf ((layerShift 3 (by decide))^[(c.1 3).val]
              ((layerShift 1 (by decide))^[i]
                ((layerShift 2 (by decide))^[(c.1 2).val]
                  (remRoot N)))) 1 (by decide))
            - θ (layerLinkOf ((layerShift 1 (by decide))^[i]
                ((layerShift 2 (by decide))^[(c.1 2).val]
                  (remRoot N))) 1 (by decide))))
        = (∑ i ∈ Finset.range (c.1 1).val,
            θ (layerLinkOf ((layerShift 3 (by decide))^[(c.1 3).val]
                ((layerShift 1 (by decide))^[i]
                  ((layerShift 2 (by decide))^[(c.1 2).val]
                    (remRoot N)))) 1 (by decide)))
          - (∑ i ∈ Finset.range (c.1 1).val,
            θ (layerLinkOf ((layerShift 1 (by decide))^[i]
                ((layerShift 2 (by decide))^[(c.1 2).val]
                  (remRoot N))) 1 (by decide))) :=
      by rw [Finset.sum_sub_distrib]
    have hZeq : (∑ i ∈ Finset.range (c.1 1).val,
          θ (layerLinkOf ((layerShift 3 (by decide))^[(c.1 3).val]
              ((layerShift 1 (by decide))^[i]
                ((layerShift 2 (by decide))^[(c.1 2).val]
                  (remRoot N)))) 1 (by decide)))
        = ∑ i ∈ Finset.range (c.1 1).val,
            θ (layerLinkOf ((layerShift 3 (by decide))^[(c.1 3).val]
                ((layerShift 2 (by decide))^[(c.1 2).val]
                  ((layerShift 1 (by decide))^[i] (remRoot N))))
                1 (by decide)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [layerShift_iterate_iterate_commute (μ := 1) (ν := 2)
        (by decide) (by decide) (remRoot N) i (c.1 2).val]
    have hXeq : (∑ i ∈ Finset.range (c.1 1).val,
          θ (layerLinkOf ((layerShift 1 (by decide))^[i]
              ((layerShift 2 (by decide))^[(c.1 2).val]
                (remRoot N))) 1 (by decide)))
        = ∑ i ∈ Finset.range (c.1 1).val,
            θ (layerLinkOf ((layerShift 2 (by decide))^[(c.1 2).val]
                ((layerShift 1 (by decide))^[i] (remRoot N)))
                1 (by decide)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [layerShift_iterate_iterate_commute (μ := 1) (ν := 2)
        (by decide) (by decide) (remRoot N) i (c.1 2).val]
    have hcrepr : layerShift 1 (by decide) c
        = (layerShift 3 (by decide))^[(c.1 3).val]
            ((layerShift 2 (by decide))^[(c.1 2).val] (remRoot N)) := by
      have h := site_eq_runs (layerShift 1 (by decide) c)
      rw [hval1, hval2, hval3, Function.iterate_zero_apply] at h
      exact h
    have hTi : ∀ i : ℕ, (layerShift 1 (by decide))^[i]
          (layerShift 1 (by decide) c)
        = (layerShift 3 (by decide))^[(c.1 3).val]
            ((layerShift 2 (by decide))^[(c.1 2).val]
              ((layerShift 1 (by decide))^[i] (remRoot N))) := by
      intro i
      rw [hcrepr,
        layerShift_iterate_iterate_commute (by decide) (by decide)
          _ _ _]
      congr 1
      exact layerShift_iterate_iterate_commute (by decide)
        (by decide) _ _ _
    have hsumZ : (∑ i ∈ Finset.range (c.1 1).val,
          θ (layerLinkOf ((layerShift 3 (by decide))^[(c.1 3).val]
              ((layerShift 2 (by decide))^[(c.1 2).val]
                ((layerShift 1 (by decide))^[i] (remRoot N))))
                1 (by decide)))
        = stepSum θ 1 (by decide) (layerShift 1 (by decide) c)
            (c.1 1).val := by
      rw [stepSum_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [hTi i]
    have hwrapStep : stepSum θ 1 (by decide)
          (layerShift 1 (by decide) c) N = 0 := by
      have h := (hwrap (layerShift 1 (by decide) c)).1
      rw [wrapHolonomy1_apply] at h
      rw [stepSum_eq_wrapHolonomy]
      exact h
    have hlast : (layerShift 1 (by decide))^[(c.1 1).val]
          (layerShift 1 (by decide) c) = c := by
      have h1 : (layerShift 1 (by decide))^[(c.1 1).val]
            (layerShift 1 (by decide) c)
          = (layerShift 1 (by decide))^[(c.1 1).val + 1] c :=
        (Function.iterate_succ_apply _ _ _).symm
      have h2 : (layerShift 1 (by decide))^[(c.1 1).val + 1] c
          = (layerShift 1 (by decide))^[N] c := by
        rw [hN1]
      rw [h1, h2]
      exact layerShift_iterate_N _ (by decide) _
    have hpartial := stepSum_eq_neg_of_wrap (ν := 1) (by decide)
      (hN := hN1.symm) (hwrap := hwrapStep) (hlast := hlast)
    have hS1sum : stepSum θ 1 (by decide) (remRoot N) (c.1 1).val
        = ∑ i ∈ Finset.range (c.1 1).val,
            θ (layerLinkOf ((layerShift 1 (by decide))^[i]
                (remRoot N)) 1 (by decide)) :=
      stepSum_apply _ _ _ _ _
    rw [hC2, hC3, hsumSub2, hsumSub3, hZeq, hXeq, hS1sum, hsumZ,
      hpartial]
    ring

/-- **Direction-2 increment**: stepping in direction `2`
leaves the first run alone, gains one link in the second
run, and shifts the third run by one step in direction `2`
(`stepSum_shift_base`); in the wrap case the second run
empties and the third run falls back
(`stepSum_iterate_base`), closed by the direction-2 wrap
holonomy at the wrapped site. -/
theorem potential_incr2
    (hflat : ∀ P : PlaqDatum N, plaqAngle P θ = 0)
    (hwrap : ∀ c : LayerSite N, wrapHolonomy1 θ c = 0 ∧
      wrapHolonomy2 θ c = 0 ∧ wrapHolonomy3 θ c = 0)
    (c : LayerSite N) :
    remPotential θ (layerShift 2 (by decide) c)
      = remPotential θ c + θ (layerLinkOf c 2 (by decide)) := by
  have hval_lt : (c.1 2).val < N := ZMod.val_lt _
  by_cases hcase : (c.1 2).val + 1 < N
  · have hval1 : ((layerShift 2 (by decide) c).1 1).val
        = (c.1 1).val :=
      val_shift_of_ne (show (1 : Fin 4) ≠ 2 by decide)
        (show (2 : Fin 4) ≠ 0 by decide) c
    have hval2 : ((layerShift 2 (by decide) c).1 2).val
        = (c.1 2).val + 1 := by
      have h := val_shift_self (2 : Fin 4) (by decide) c
      rw [if_pos hcase] at h
      exact h
    have hval3 : ((layerShift 2 (by decide) c).1 3).val
        = (c.1 3).val :=
      val_shift_of_ne (show (3 : Fin 4) ≠ 2 by decide)
        (show (2 : Fin 4) ≠ 0 by decide) c
    rw [remPotential_apply, remPotential_apply, hval1, hval2, hval3]
    have hbase3 : (layerShift 2 (by decide))^[(c.1 2).val + 1]
          ((layerShift 1 (by decide))^[(c.1 1).val] (remRoot N))
        = layerShift 2 (by decide)
            ((layerShift 2 (by decide))^[(c.1 2).val]
              ((layerShift 1 (by decide))^[(c.1 1).val]
                (remRoot N))) :=
      Function.iterate_succ_apply' _ _ _
    rw [hbase3]
    have hS2 := stepSum_succ θ 2 (by decide)
      ((layerShift 1 (by decide))^[(c.1 1).val] (remRoot N))
      (c.1 2).val
    have hB3 := stepSum_shift_base (μ := 2) (ν := 3) hflat
      (by decide) (by decide) (by decide)
      ((layerShift 2 (by decide))^[(c.1 2).val]
        ((layerShift 1 (by decide))^[(c.1 1).val] (remRoot N)))
      (c.1 3).val
    rw [← site_eq_runs c] at hB3
    rw [hS2, hB3]
    ring
  · have hN1 : (c.1 2).val + 1 = N := by omega
    have hval1 : ((layerShift 2 (by decide) c).1 1).val
        = (c.1 1).val :=
      val_shift_of_ne (show (1 : Fin 4) ≠ 2 by decide)
        (show (2 : Fin 4) ≠ 0 by decide) c
    have hval2 : ((layerShift 2 (by decide) c).1 2).val = 0 := by
      have h := val_shift_self (2 : Fin 4) (by decide) c
      rw [if_neg hcase] at h
      exact h
    have hval3 : ((layerShift 2 (by decide) c).1 3).val
        = (c.1 3).val :=
      val_shift_of_ne (show (3 : Fin 4) ≠ 2 by decide)
        (show (2 : Fin 4) ≠ 0 by decide) c
    rw [remPotential_apply, remPotential_apply, hval1, hval2, hval3]
    rw [stepSum_zero, Function.iterate_zero_apply]
    have hC3 := stepSum_iterate_base (μ := 2) (ν := 3) hflat
      (by decide) (by decide) (by decide)
      ((layerShift 1 (by decide))^[(c.1 1).val] (remRoot N))
      (c.1 3).val (c.1 2).val
    have hsumSub : (∑ j ∈ Finset.range (c.1 2).val,
          (θ (layerLinkOf ((layerShift 3 (by decide))^[(c.1 3).val]
              ((layerShift 2 (by decide))^[j]
                ((layerShift 1 (by decide))^[(c.1 1).val]
                  (remRoot N)))) 2 (by decide))
            - θ (layerLinkOf ((layerShift 2 (by decide))^[j]
                ((layerShift 1 (by decide))^[(c.1 1).val]
                  (remRoot N))) 2 (by decide))))
        = (∑ j ∈ Finset.range (c.1 2).val,
            θ (layerLinkOf ((layerShift 3 (by decide))^[(c.1 3).val]
                ((layerShift 2 (by decide))^[j]
                  ((layerShift 1 (by decide))^[(c.1 1).val]
                    (remRoot N)))) 2 (by decide)))
          - (∑ j ∈ Finset.range (c.1 2).val,
            θ (layerLinkOf ((layerShift 2 (by decide))^[j]
                ((layerShift 1 (by decide))^[(c.1 1).val]
                  (remRoot N))) 2 (by decide))) :=
      by rw [Finset.sum_sub_distrib]
    have hcrepr : layerShift 2 (by decide) c
        = (layerShift 3 (by decide))^[(c.1 3).val]
            ((layerShift 1 (by decide))^[(c.1 1).val] (remRoot N)) := by
      have h := site_eq_runs (layerShift 2 (by decide) c)
      rw [hval1, hval2, hval3, Function.iterate_zero_apply] at h
      exact h
    have hsumZ : (∑ j ∈ Finset.range (c.1 2).val,
          θ (layerLinkOf ((layerShift 3 (by decide))^[(c.1 3).val]
              ((layerShift 2 (by decide))^[j]
                ((layerShift 1 (by decide))^[(c.1 1).val]
                  (remRoot N)))) 2 (by decide)))
        = stepSum θ 2 (by decide) (layerShift 2 (by decide) c)
            (c.1 2).val := by
      rw [stepSum_apply]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      rw [hcrepr,
        layerShift_iterate_iterate_commute (μ := 2) (ν := 3)
          (by decide) (by decide)
          ((layerShift 1 (by decide))^[(c.1 1).val] (remRoot N))
          j (c.1 3).val]
    have hwrapStep : stepSum θ 2 (by decide)
          (layerShift 2 (by decide) c) N = 0 := by
      have h := (hwrap (layerShift 2 (by decide) c)).2.1
      rw [wrapHolonomy2_apply] at h
      rw [stepSum_eq_wrapHolonomy]
      exact h
    have hlast : (layerShift 2 (by decide))^[(c.1 2).val]
          (layerShift 2 (by decide) c) = c := by
      have h1 : (layerShift 2 (by decide))^[(c.1 2).val]
            (layerShift 2 (by decide) c)
          = (layerShift 2 (by decide))^[(c.1 2).val + 1] c :=
        (Function.iterate_succ_apply _ _ _).symm
      have h2 : (layerShift 2 (by decide))^[(c.1 2).val + 1] c
          = (layerShift 2 (by decide))^[N] c := by
        rw [hN1]
      rw [h1, h2]
      exact layerShift_iterate_N _ (by decide) _
    have hpartial := stepSum_eq_neg_of_wrap (ν := 2) (by decide)
      (hN := hN1.symm) (hwrap := hwrapStep) (hlast := hlast)
    have hS2sum : stepSum θ 2 (by decide)
          ((layerShift 1 (by decide))^[(c.1 1).val] (remRoot N))
          (c.1 2).val
        = ∑ j ∈ Finset.range (c.1 2).val,
            θ (layerLinkOf ((layerShift 2 (by decide))^[j]
                ((layerShift 1 (by decide))^[(c.1 1).val]
                  (remRoot N))) 2 (by decide)) :=
      stepSum_apply _ _ _ _ _
    rw [hC3, hsumSub, hS2sum, hsumZ, hpartial]
    ring

/-- **Direction-3 increment**: stepping in direction `3`
leaves the first two runs alone and gains one link in the
third run; in the wrap case the third run empties, closed
by the direction-3 wrap holonomy at the wrapped site. -/
theorem potential_incr3
    (hflat : ∀ P : PlaqDatum N, plaqAngle P θ = 0)
    (hwrap : ∀ c : LayerSite N, wrapHolonomy1 θ c = 0 ∧
      wrapHolonomy2 θ c = 0 ∧ wrapHolonomy3 θ c = 0)
    (c : LayerSite N) :
    remPotential θ (layerShift 3 (by decide) c)
      = remPotential θ c + θ (layerLinkOf c 3 (by decide)) := by
  have hval_lt : (c.1 3).val < N := ZMod.val_lt _
  by_cases hcase : (c.1 3).val + 1 < N
  · have hval1 : ((layerShift 3 (by decide) c).1 1).val
        = (c.1 1).val :=
      val_shift_of_ne (show (1 : Fin 4) ≠ 3 by decide)
        (show (3 : Fin 4) ≠ 0 by decide) c
    have hval2 : ((layerShift 3 (by decide) c).1 2).val
        = (c.1 2).val :=
      val_shift_of_ne (show (2 : Fin 4) ≠ 3 by decide)
        (show (3 : Fin 4) ≠ 0 by decide) c
    have hval3 : ((layerShift 3 (by decide) c).1 3).val
        = (c.1 3).val + 1 := by
      have h := val_shift_self (3 : Fin 4) (by decide) c
      rw [if_pos hcase] at h
      exact h
    rw [remPotential_apply, remPotential_apply, hval1, hval2, hval3]
    have hS3 := stepSum_succ θ 3 (by decide)
      ((layerShift 2 (by decide))^[(c.1 2).val]
        ((layerShift 1 (by decide))^[(c.1 1).val] (remRoot N)))
      (c.1 3).val
    rw [← site_eq_runs c] at hS3
    rw [hS3]
    ring
  · have hN1 : (c.1 3).val + 1 = N := by omega
    have hval1 : ((layerShift 3 (by decide) c).1 1).val
        = (c.1 1).val :=
      val_shift_of_ne (show (1 : Fin 4) ≠ 3 by decide)
        (show (3 : Fin 4) ≠ 0 by decide) c
    have hval2 : ((layerShift 3 (by decide) c).1 2).val
        = (c.1 2).val :=
      val_shift_of_ne (show (2 : Fin 4) ≠ 3 by decide)
        (show (3 : Fin 4) ≠ 0 by decide) c
    have hval3 : ((layerShift 3 (by decide) c).1 3).val = 0 := by
      have h := val_shift_self (3 : Fin 4) (by decide) c
      rw [if_neg hcase] at h
      exact h
    rw [remPotential_apply, remPotential_apply, hval1, hval2, hval3]
    rw [stepSum_zero]
    have hbase : (layerShift 2 (by decide))^[(c.1 2).val]
          ((layerShift 1 (by decide))^[(c.1 1).val] (remRoot N))
        = layerShift 3 (by decide) c := by
      have h := site_eq_runs (layerShift 3 (by decide) c)
      rw [hval1, hval2, hval3, Function.iterate_zero_apply] at h
      exact h.symm
    have hwrapStep : stepSum θ 3 (by decide)
          (layerShift 3 (by decide) c) N = 0 := by
      have h := (hwrap (layerShift 3 (by decide) c)).2.2
      rw [wrapHolonomy3_apply] at h
      rw [stepSum_eq_wrapHolonomy]
      exact h
    have hlast : (layerShift 3 (by decide))^[(c.1 3).val]
          (layerShift 3 (by decide) c) = c := by
      have h1 : (layerShift 3 (by decide))^[(c.1 3).val]
            (layerShift 3 (by decide) c)
          = (layerShift 3 (by decide))^[(c.1 3).val + 1] c :=
        (Function.iterate_succ_apply _ _ _).symm
      have h2 : (layerShift 3 (by decide))^[(c.1 3).val + 1] c
          = (layerShift 3 (by decide))^[N] c := by
        rw [hN1]
      rw [h1, h2]
      exact layerShift_iterate_N _ (by decide) _
    have hpartial := stepSum_eq_neg_of_wrap (ν := 3) (by decide)
      (hN := hN1.symm) (hwrap := hwrapStep) (hlast := hlast)
    rw [hbase, hpartial]
    ring

/-- **The potential increment in any spatial direction**:
the three direction lemmas, dispatched by the direction's
value. -/
theorem potential_increment
    (hflat : ∀ P : PlaqDatum N, plaqAngle P θ = 0)
    (hwrap : ∀ c : LayerSite N, wrapHolonomy1 θ c = 0 ∧
      wrapHolonomy2 θ c = 0 ∧ wrapHolonomy3 θ c = 0)
    (c : LayerSite N) (ν : Fin 4) (hν : ν ≠ 0) :
    remPotential θ (layerShift ν hν c)
      = remPotential θ c + θ (layerLinkOf c ν hν) := by
  rcases fin4_ne_zero_cases ν hν with rfl | rfl | rfl
  · exact potential_incr1 hflat hwrap c
  · exact potential_incr2 hflat hwrap c
  · exact potential_incr3 hflat hwrap c

end Increment

section Main

variable {N : ℕ} [NeZero N]

/-- A link is the layer link over its tail in its own
direction. -/
theorem link_eq_layerLinkOf (ℓ : LayerLink N) :
    ℓ = layerLinkOf (linkTail ℓ) ℓ.1.2 ℓ.2.2 := by
  apply Subtype.ext
  rfl

/-- **REM-2, discharged in the pin's exact registered form**:
at general even `N`, `RemClosure N` - a link configuration
is flat at every plaquette datum and has vanishing wrap
holonomies in all three directions at every base site if
and only if it is a site-potential gradient. The forward
direction is the path-integrated potential
`remPotential`; the backward direction is M3
(`maxwellM3_proved`) plus REM-1's telescoping
(`wrapHolonomy_gaugeAngle`). -/
theorem remClosure_proved (hN : Even N) : RemClosure N := by
  rw [remClosure_iff]
  intro θ
  constructor
  · intro hθ
    obtain ⟨hflat, hwrap⟩ := hθ
    refine ⟨remPotential θ, ?_⟩
    funext ℓ
    have hℓ := link_eq_layerLinkOf ℓ
    have hhead : linkHead ℓ
        = layerShift ℓ.1.2 ℓ.2.2 (linkTail ℓ) := rfl
    show θ ℓ = remPotential θ (linkHead ℓ)
      - remPotential θ (linkTail ℓ)
    conv_lhs => rw [hℓ]
    rw [hhead, potential_increment hflat hwrap (linkTail ℓ)
      ℓ.1.2 ℓ.2.2]
    ring
  · intro hθ
    obtain ⟨φ, hφ⟩ := hθ
    rw [hφ]
    refine ⟨fun P => maxwellM3_proved φ P, fun c => ⟨?_, ?_, ?_⟩⟩
    · rw [wrapHolonomy1_apply]
      exact wrapHolonomy_gaugeAngle φ 1 (by decide) c
    · rw [wrapHolonomy2_apply]
      exact wrapHolonomy_gaugeAngle φ 2 (by decide) c
    · rw [wrapHolonomy3_apply]
      exact wrapHolonomy_gaugeAngle φ 3 (by decide) c

end Main

end ThetLogos
