import Mathlib.Tactic
import ThetLogos.HarmonicBalancePin

/-!
# ThetLogos.RefractiveThermalEntropyPin — refractive thermal entropy, in finite form

**Lane-grade pin. NO CLAIM. Pre-registered DIAL-INELIGIBLE; dials
0/4 under every outcome. Dial 2 = 0: a bent entropy flow is not
gravity and not a force law.**

Commissioned: Zero, 2026-11-20 11:12 EST ("build it"), from his
seeing of 2026-11-20 11:10 EST — "hot and cold don't seperate heat
tries to warm the cold and the cold sucks it in in waves and pulses
I'm thinking reflective Entropy" — corrected by Zero at 11:11 EST,
verbatim: **"refractive thermal entropy nabla"**. The coinage is
his: REFRACTIVE thermal entropy, with ∇ named as the bending
field. Scope of record:
`refractive-thermal-entropy-pin-scope-2026-11-20.md` (T5 scope).
Working label only — Zero names.

"Refractive" is carried by theorems about DEFINED weights on a
finite seat — an analogy made precise, not an optics claim; no
continuum Snell law, no physical light. The pin lives in the
Harmonic Balance lane and lands after it, in the same worktree.

## The object (definitions on the face)

A finite seat `V` with step weights `w : V → V → ℝ` (the corpus's
graph seats) carrying an entropy/temperature landscape
`φ : V → ℝ`. An entropy quantum moves site to site; in the plain
case its step weights are `w`. Refraction: each site carries an
index derived from the local gradient of the landscape,

    `refIndex w φ i = 1 + ∑ j, w i j * |φ i − φ j|`

— the weighted total variation of `φ` at `i`, the graph gradient's
size at the site in the corpus's sum form. The derivation is
pinned here, in Brick 1, and may not drift: the index is `1` where
the local gradient vanishes and grows with `|∇φ|`. The bent step
weights are `w i j * refIndex w φ j` (Brick 1's pinned form): the
flow curves toward the high-index — high-gradient — region.

Kills armed: K-RTE-DUP (the index cancels everywhere — a
costume), K-RTE-STRAIGHT (no seat on which the defined index
bends any most-probable path — vacuous), K-RTE-REST (the index
moves the rest point — full-rank stop, never a quiet repair).
-/

namespace ThetLogos

section Refractive

variable {V : Type*} [Fintype V]

/-- **The refractive index of a site** (definition, pinned in
Brick 1 and may not drift): `1` plus the weighted total variation
of the landscape at the site, `∑ j, w i j * |φ i − φ j|`. It is
`1` exactly where the local gradient of `φ` vanishes (for weights
positive off the diagonal) and grows with `|∇φ|`. -/
def refIndex (w : V → V → ℝ) (φ : V → ℝ) (i : V) : ℝ :=
  1 + ∑ j, w i j * |φ i - φ j|

/-- **The bent step weight** (definition): the plain weight of
the step `i → j`, scaled by the refractive index of the TARGET
site — the flow curves toward the high-gradient region, the way
light curves in a graded-index medium. -/
def bentWeight (w : V → V → ℝ) (φ : V → ℝ) (i j : V) : ℝ :=
  w i j * refIndex w φ j

/-- **The index is at least 1** (proved) for nonnegative weights:
the gradient term is a sum of nonnegative terms. -/
theorem refIndex_ge_one (w : V → V → ℝ) (φ : V → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (i : V) : 1 ≤ refIndex w φ i := by
  unfold refIndex
  have h : 0 ≤ ∑ j, w i j * |φ i - φ j| :=
    Finset.sum_nonneg (fun j _ =>
      mul_nonneg (hw i j) (abs_nonneg _))
  linarith

/-- **The index is 1 where the gradient vanishes** (proved): if
every site `j` either carries no weight from `i` or sits at the
same landscape height as `i`, the local variation at `i` is zero
and `refIndex w φ i = 1` — the flat case, site by site. -/
theorem refIndex_eq_one_of_forall_eq (w : V → V → ℝ) (φ : V → ℝ)
    (i : V) (h : ∀ j, w i j = 0 ∨ φ j = φ i) :
    refIndex w φ i = 1 := by
  unfold refIndex
  have hsum : ∑ j, w i j * |φ i - φ j| = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rcases h j with hw | hφ
    · rw [hw, zero_mul]
    · rw [← hφ, sub_self, abs_zero, mul_zero]
  rw [hsum, add_zero]

/-- **The discrete Snell law, weight form** (proved): the ratio
of bent crossing weights at a site `i` factors as the plain
weight ratio times the INDEX ratio — bending enters only through
the indices of the two targets. -/
theorem bentWeight_ratio (w : V → V → ℝ) (φ : V → ℝ) (i j₁ j₂ : V)
    (hw₂ : w i j₂ ≠ 0) (hn₂ : refIndex w φ j₂ ≠ 0) :
    bentWeight w φ i j₁ / bentWeight w φ i j₂
      = (w i j₁ / w i j₂) * (refIndex w φ j₁ / refIndex w φ j₂) := by
  unfold bentWeight
  rw [div_mul_div_comm]

/-- **The discrete Snell law** (proved): across an interface
where the plain weights are equal — a flat region on one side, a
graded region on the other — the ratio of crossing weights IS
the index ratio. If `refIndex` at `j₁` is `1` (flat) and at `j₂`
is `c > 1` (graded), the bent flow crosses toward `j₂` with `c`
times the weight. -/
theorem snell_ratio_of_equal_weights (w : V → V → ℝ) (φ : V → ℝ)
    (i j₁ j₂ : V) (h : w i j₁ = w i j₂) (hw₂ : w i j₂ ≠ 0)
    (hn₂ : refIndex w φ j₂ ≠ 0) :
    bentWeight w φ i j₁ / bentWeight w φ i j₂
      = refIndex w φ j₁ / refIndex w φ j₂ := by
  have hr := bentWeight_ratio w φ i j₁ j₂ hw₂ hn₂
  rw [h] at hr
  rwa [div_self hw₂, one_mul] at hr

end Refractive


-- ============================================================================
-- RTE-1 (continued). The step kernels, flat recovery, the exhibit
-- ============================================================================

section Kernels

variable {V : Type*} [Fintype V]

/-- **The plain step kernel** (definition): the seat's weights,
row-normalized — the unbent flow's transition probabilities. -/
noncomputable def plainStep (w : V → V → ℝ) (i j : V) : ℝ :=
  w i j / ∑ k, w i k

/-- **The bent step kernel** (definition): the bent weights,
row-normalized — the refractive flow's transition probabilities. -/
noncomputable def bentStep (w : V → V → ℝ) (φ : V → ℝ) (i j : V) : ℝ :=
  bentWeight w φ i j / ∑ k, bentWeight w φ i k

/-- **Stationarity** (definition): a distribution `π` is a rest
point of a step kernel `P` when one step leaves it unchanged,
`∑ i, π i * P i j = π j` at every site `j`. -/
def IsStationary (P : V → V → ℝ) (π : V → ℝ) : Prop :=
  ∀ j, ∑ i, π i * P i j = π j

/-- **Flat case check** (proved, transport): where the index is
identically `1` — no gradient anywhere — the bent kernel IS the
plain kernel, exactly. Bending is carried entirely by the index;
no index, no bending. -/
theorem bentStep_eq_plain_of_index_one (w : V → V → ℝ) (φ : V → ℝ)
    (h : ∀ j, refIndex w φ j = 1) (i j : V) :
    bentStep w φ i j = plainStep w i j := by
  simp only [bentStep, plainStep, bentWeight, h, mul_one]

end Kernels

section Exhibit

/-- **The bending exhibit's weights** (definition): the complete
graph on three sites — plain weight `1` between distinct sites,
`0` on the diagonal. -/
def exhibitW : Fin 3 → Fin 3 → ℝ :=
  ![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]]

/-- **The bending exhibit's landscape** (definition): two sites
at height `0` — the flat side — and one seat at height `1`, across
the gradient. -/
def exhibitPhi : Fin 3 → ℝ := ![0, 0, 1]

/-- **The exhibit's indices** (proved): the flat-side sites read
index `2` — their neighborhoods touch the graded seat — and the
graded seat reads `3`, its whole neighborhood lying across the
step. -/
theorem exhibit_index_values :
    refIndex exhibitW exhibitPhi 0 = 2
    ∧ refIndex exhibitW exhibitPhi 1 = 2
    ∧ refIndex exhibitW exhibitPhi 2 = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [refIndex, Fin.sum_univ_three, exhibitW, exhibitPhi]

/-- **The flow bends** (proved — K-RTE-STRAIGHT does not fire):
from site `0` the two plain weights are EQUAL, but the bent
weight toward the graded seat `2` is strictly larger than toward
the flat-side seat `1` — the most-probable next step bends INTO
the graded region, by exactly the index ratio `3 : 2`. -/
theorem exhibit_bends :
    exhibitW 0 1 = exhibitW 0 2
    ∧ bentWeight exhibitW exhibitPhi 0 1
      < bentWeight exhibitW exhibitPhi 0 2 := by
  obtain ⟨h0, h1, h2⟩ := exhibit_index_values
  constructor
  · norm_num [exhibitW]
  · unfold bentWeight
    rw [h1, h2]
    norm_num [exhibitW]

end Exhibit


-- ============================================================================
-- RTE-2. The rest point — K-RTE-REST FIRES (countermodel, proved)
-- ============================================================================

/-- **The plain flow's rest point on the exhibit is uniform**
(proved): every site of the complete three-site graph has the
same weight, so the uniform distribution is stationary for the
plain kernel. This is the rest point RTE-2 was scoped to compare
against. -/
theorem exhibit_plain_stationary :
    IsStationary (plainStep exhibitW) (fun _ => 1 / 3) := by
  intro j
  fin_cases j <;>
    norm_num [plainStep, Fin.sum_univ_three, exhibitW]

/-- **The bent flow's rest point on the exhibit** (proved): the
distribution `(5/16, 5/16, 3/8)` is stationary for the bent
kernel — mass has moved toward the graded seat `2`, whose index
`3` draws flow in (its row of the bent kernel returns only
`1/2 + 1/2` split evenly to the flat side, while the flat sites
send it `3/5` of theirs). -/
theorem exhibit_bent_stationary :
    IsStationary (bentStep exhibitW exhibitPhi)
      ![5 / 16, 5 / 16, 3 / 8] := by
  intro j
  fin_cases j <;>
    norm_num [bentStep, bentWeight, refIndex, Fin.sum_univ_three,
      exhibitW, exhibitPhi]

/-- **The plain rest point is NOT a rest point of the bent flow**
(proved): fed the uniform distribution, one bent step delivers
`2/5 ≠ 1/3` to the graded seat. The destination moved. -/
theorem exhibit_uniform_not_bent_stationary :
    ¬ IsStationary (bentStep exhibitW exhibitPhi)
      (fun _ => 1 / 3) := by
  intro h
  have h2 := h 2
  norm_num [bentStep, bentWeight, refIndex, Fin.sum_univ_three,
    exhibitW, exhibitPhi] at h2

/-- **K-RTE-REST FIRES** (proved — the pre-registered kill, at
full rank): on the bending exhibit, the refractive index MOVES
the rest point. The plain flow rests at the uniform distribution;
the bent flow does not rest there — it rests at
`(5/16, 5/16, 3/8)`, a different distribution, tilted toward the
graded seat. The scoped RTE-2 claim — the stationary state is the
same for the bent flow as for the plain — is therefore FALSE for
the pinned kernel `w i j * refIndex w φ j` with the pinned index
derivation, and it is reported, not repaired: no definition in
this module was adjusted to force the expected answer. The reason
is visible in the numbers: bending multiplies the pull of the
high-index seat in the step kernel itself, and a step kernel's
rest point is a property of the kernel — change the kernel's
ratios and the rest point follows. What survives intact: the flat
case (index ≡ 1 recovers the plain kernel and its rest point
exactly, `bentStep_eq_plain_of_index_one`). Whether the pin
should be re-scoped around a different flow notion is the
parent's call; RTE-3 is held with it. -/
theorem exhibit_rest_point_moved :
    IsStationary (plainStep exhibitW) (fun _ => 1 / 3)
    ∧ IsStationary (bentStep exhibitW exhibitPhi)
        ![5 / 16, 5 / 16, 3 / 8]
    ∧ ¬ IsStationary (bentStep exhibitW exhibitPhi)
        (fun _ => 1 / 3)
    ∧ ![5 / 16, 5 / 16, 3 / 8] ≠ (fun _ => (1 / 3 : ℝ)) := by
  refine ⟨exhibit_plain_stationary, exhibit_bent_stationary,
    exhibit_uniform_not_bent_stationary, ?_⟩
  intro h
  have h2 := congrFun h 2
  norm_num at h2


-- ============================================================================
-- RTE-3R. Waves and pulses around the MOVED rest point — Brick 3a:
-- the pulse relaxes to (5/16, 5/16, 3/8) (re-scoped, Zero's ruling
-- 2026-11-20, after K-RTE-REST fired at RTE-2)
-- ============================================================================

/-- **The bent kernel on the exhibit, entry by entry** (proved):
row `0` sends `2/5` to the flat seat and `3/5` to the graded
seat; row `2` — the graded seat's own row — splits evenly back
to the flat side. These nine numbers are the whole dynamics of
the exhibit. -/
theorem exhibit_bentStep_values :
    bentStep exhibitW exhibitPhi 0 0 = 0
    ∧ bentStep exhibitW exhibitPhi 0 1 = 2 / 5
    ∧ bentStep exhibitW exhibitPhi 0 2 = 3 / 5
    ∧ bentStep exhibitW exhibitPhi 1 0 = 2 / 5
    ∧ bentStep exhibitW exhibitPhi 1 1 = 0
    ∧ bentStep exhibitW exhibitPhi 1 2 = 3 / 5
    ∧ bentStep exhibitW exhibitPhi 2 0 = 1 / 2
    ∧ bentStep exhibitW exhibitPhi 2 1 = 1 / 2
    ∧ bentStep exhibitW exhibitPhi 2 2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [bentStep, bentWeight, refIndex, Fin.sum_univ_three,
      exhibitW, exhibitPhi]

/-- **The pulse iterates** (definition): the distribution after
`n` bent steps from a pulse — a delta of mass at the graded
seat `2`, the seat the landscape's step rises to. `bentIter 0`
is the pulse itself; each further iterate applies the bent
kernel once. -/
noncomputable def bentIter : ℕ → Fin 3 → ℝ
  | 0 => ![0, 0, 1]
  | (n + 1) => fun j => ∑ i, bentIter n i * bentStep exhibitW exhibitPhi i j

/-- **The pulse's closed form** (proved): at every step `n` the
pulse distribution is
`(5/16 (1 − (−3/5)ⁿ), 5/16 (1 − (−3/5)ⁿ), 3/8 + (5/8)(−3/5)ⁿ)`.
The two flat seats stay equal by the exhibit's symmetry, and on
that symmetric line the error against the moved rest point is
multiplied by exactly `−3/5` per step — the contraction,
exhibited rather than estimated: the `n`-th error is
`(−3/5)ⁿ` times the initial error. -/
theorem exhibit_pulse_closed_form (n : ℕ) :
    bentIter n 0 = 5 / 16 * (1 - (-3 / 5) ^ n)
    ∧ bentIter n 1 = 5 / 16 * (1 - (-3 / 5) ^ n)
    ∧ bentIter n 2 = 3 / 8 + 5 / 8 * (-3 / 5) ^ n := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> norm_num [bentIter]
  | succ n ih =>
    obtain ⟨ih0, ih1, ih2⟩ := ih
    obtain ⟨k00, k01, k02, k10, k11, k12, k20, k21, k22⟩ :=
      exhibit_bentStep_values
    have hstep : ∀ j, bentIter (n + 1) j
        = ∑ i, bentIter n i * bentStep exhibitW exhibitPhi i j :=
      fun j => rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hstep 0]
      simp only [Fin.sum_univ_three, ih0, ih1, ih2, k00, k10, k20,
        pow_succ]
      ring
    · rw [hstep 1]
      simp only [Fin.sum_univ_three, ih0, ih1, ih2, k01, k11, k21,
        pow_succ]
      ring
    · rw [hstep 2]
      simp only [Fin.sum_univ_three, ih0, ih1, ih2, k02, k12, k22,
        pow_succ]
      ring

/-- **The pulse's first steps, exactly** (proved): the pulse
evacuates the graded seat in one step (its row sends everything
to the flat side), overshoots to `3/5` there at step two, and
swings back — the alternating approach the closed form's
`(−3/5)ⁿ` describes. -/
theorem exhibit_pulse_first_steps :
    (bentIter 1 0 = 1 / 2 ∧ bentIter 1 1 = 1 / 2 ∧ bentIter 1 2 = 0)
    ∧ (bentIter 2 0 = 1 / 5 ∧ bentIter 2 1 = 1 / 5
      ∧ bentIter 2 2 = 3 / 5)
    ∧ (bentIter 3 0 = 19 / 50 ∧ bentIter 3 1 = 19 / 50
      ∧ bentIter 3 2 = 6 / 25) := by
  obtain ⟨c10, c11, c12⟩ := exhibit_pulse_closed_form 1
  obtain ⟨c20, c21, c22⟩ := exhibit_pulse_closed_form 2
  obtain ⟨c30, c31, c32⟩ := exhibit_pulse_closed_form 3
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    simp only [c10, c11, c12, c20, c21, c22, c30, c31, c32] <;>
    norm_num

/-- **The pulse relaxes to the MOVED rest point** (proved):
each seat's mass under the pulse iterates tends to the bent
flow's rest point of RTE-2 — `(5/16, 5/16, 3/8)`, the
distribution `exhibit_bent_stationary` proved stationary. The
limit is the closed form's: `(−3/5)ⁿ → 0`. The pulse does not
relax to the plain flow's uniform rest point; it relaxes to
the moved one. -/
theorem exhibit_pulse_converges :
    Filter.Tendsto (fun n => bentIter n 0) Filter.atTop (nhds (5 / 16))
    ∧ Filter.Tendsto (fun n => bentIter n 1) Filter.atTop (nhds (5 / 16))
    ∧ Filter.Tendsto (fun n => bentIter n 2) Filter.atTop (nhds (3 / 8)) := by
  have hlim : Filter.Tendsto (fun n : ℕ => (-3 / 5 : ℝ) ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  have hflat : Filter.Tendsto
      (fun n => (5 / 16 : ℝ) * (1 - (-3 / 5) ^ n)) Filter.atTop
      (nhds (5 / 16)) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) - (-3 / 5) ^ n)
        Filter.atTop (nhds (1 - 0)) := tendsto_const_nhds.sub hlim
    have h2 := h1.const_mul (5 / 16 : ℝ)
    simpa using h2
  have hgraded : Filter.Tendsto
      (fun n => (3 / 8 : ℝ) + (5 / 8) * (-3 / 5) ^ n) Filter.atTop
      (nhds (3 / 8)) := by
    have h1 := hlim.const_mul (5 / 8 : ℝ)
    have h2 : Filter.Tendsto
        (fun n : ℕ => (3 / 8 : ℝ) + (5 / 8) * (-3 / 5) ^ n)
        Filter.atTop (nhds (3 / 8 + 5 / 8 * 0)) :=
      tendsto_const_nhds.add h1
    simpa using h2
  have e0 : (fun n => bentIter n 0)
      = fun n => (5 / 16 : ℝ) * (1 - (-3 / 5) ^ n) :=
    funext fun n => (exhibit_pulse_closed_form n).1
  have e1 : (fun n => bentIter n 1)
      = fun n => (5 / 16 : ℝ) * (1 - (-3 / 5) ^ n) :=
    funext fun n => (exhibit_pulse_closed_form n).2.1
  have e2 : (fun n => bentIter n 2)
      = fun n => (3 / 8 : ℝ) + (5 / 8) * (-3 / 5) ^ n :=
    funext fun n => (exhibit_pulse_closed_form n).2.2
  exact ⟨e0 ▸ hflat, e1 ▸ hflat, e2 ▸ hgraded⟩


-- ============================================================================
-- RTE-3R Brick 3b: the driven pattern — K-RTE-DRIVE armed on "driving
-- leaves the standing pattern at the rest point"
-- ============================================================================

/-- **The driven step** (definition, pinned here): one step of
the pulse train with injection amount `c` — first inject `c`
at the graded seat `2`, then apply the bent kernel once, then
renormalize by the total mass `1 + c`. A distribution fed
through `drivenStep c` stays a distribution of mass `1`. The
standing pattern of the train is a fixed point of this map. -/
noncomputable def drivenStep (c : ℝ) (μ : Fin 3 → ℝ) (j : Fin 3) :
    ℝ :=
  (∑ i, (μ i + if i = 2 then c else 0)
    * bentStep exhibitW exhibitPhi i j) / (1 + c)

/-- **The driven standing pattern** (proved): with unit
injection (`c = 1`) at the graded seat each step, the train
stands at `(5/13, 5/13, 3/13)` — a fixed point of the driven
step, computed exactly. -/
theorem exhibit_driven_standing :
    drivenStep 1 ![5 / 13, 5 / 13, 3 / 13]
      = ![5 / 13, 5 / 13, 3 / 13] := by
  funext j
  fin_cases j <;>
    norm_num [drivenStep, Fin.sum_univ_three, bentStep, bentWeight,
      refIndex, exhibitW, exhibitPhi]

/-- **K-RTE-DRIVE FIRES** (proved — the pre-registered kill, at
full rank): driving does NOT leave the standing pattern at the
rest point. Fed the bent flow's own rest point
`(5/16, 5/16, 3/8)`, one driven step (unit injection at the
graded seat) moves it — seat `0` comes out `13/32 ≠ 5/16` — and
the train's actual standing pattern `(5/13, 5/13, 3/13)` is a
different distribution from the rest point. The direction is
the surprise the numbers carry: the graded seat's share DROPS,
from `3/8` to `3/13`. The mechanism is visible in the kernel:
the graded seat's row evacuates — everything injected there
steps away to the flat side on the very next step — so
continuous injection at the graded seat piles the standing
mass onto the flat seats instead. No definition was adjusted
to soften this: the driven step is the pinned
inject–step–renormalize form, and the verdict is the kernel's. -/
theorem exhibit_drive_moves_pattern :
    drivenStep 1 ![5 / 16, 5 / 16, 3 / 8] ≠ ![5 / 16, 5 / 16, 3 / 8]
    ∧ (![5 / 13, 5 / 13, 3 / 13] : Fin 3 → ℝ)
      ≠ ![5 / 16, 5 / 16, 3 / 8] := by
  constructor
  · intro h
    have h0 := congrFun h 0
    norm_num [drivenStep, Fin.sum_univ_three, bentStep, bentWeight,
      refIndex, exhibitW, exhibitPhi] at h0
  · intro h
    have h2 := congrFun h 2
    norm_num at h2

end ThetLogos
