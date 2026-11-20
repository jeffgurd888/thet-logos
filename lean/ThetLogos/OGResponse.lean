import Mathlib.Tactic
import ThetLogos.OGResponsePin

namespace ThetLogos

/-!
# ThetLogos.OGResponse — OG-RL-1a, the action calculus + EL form

**Commission:** the C-4 line of `og-response-law-scope-2026-11-17.md`
(§3, OG-RL-1), under Zero's four design rulings of 2026-11-17
09:41–09:47 EST, frozen in `OGResponsePin` (OG-RL-0). This brick is
the first half of OG-RL-1: the variation calculus of the frozen
action and the EL characterization. The scaling engine and the
non-vacuity witness are OG-RL-1b, a separate banked build (the
small-brick cap split the scoped brick, whose declaration count
grew past ~10 in drafting; the content assignment is the scope's,
unchanged).

## Face declarations

- **NO CLAIM. PRE-REGISTERED DIAL-INELIGIBLE.** Dial 2 = 0 before
  this brick, 0 after it, 0 under every outcome of the line. The
  law proved here is a law of the EXTENDED datum
  (`OGResponseDatum`), never of OG-as-pinned (K-OG-RL-SCOPE).
- Everything below is about the pin's frozen forms: the action is
  `ogAction` exactly as frozen (no retuning — D2-0), the kernel is
  `seatKinetic` (the seat's own `w`; Ruling 4), the potential is
  the grounded inversion (Ruling 3; K-OG-RL-SHADOW stands armed
  over any closed-channel rerouting — there is none here).
- The EL form is VARIATIONAL: stationarity is exactly the
  site-balance minimality at interior sites. On a general graph
  this is path-optimality, not an acceleration vector (D2-4's
  predeclared residual risk).

## Contents (5 declarations)

- `ogPotential_update` — a single-site variation moves the
  potential sum by exactly the site difference.
- `ogKinetic_update` — a single-site interior variation moves the
  kinetic sum by exactly the two touching steps' difference.
- `ogAction_eq` — the frozen action, unfolded (its definitional
  form, for rewriting).
- `ogAction_update` — the action's variation is the site-balance
  difference: `A(x with k ↦ y) = A x + (balance y − balance (x k))`.
- `og_el_form` — **the EL form**: `OGResponseELForm D B n x`,
  the pin's frozen target, proved as an iff in both directions.
-/

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- **Variation of the potential sum.** Replacing the path's site
at `k` by `y` changes the potential sum by exactly the difference
at that site: every other site is untouched. -/
theorem ogPotential_update (D : OGResponseDatum V) (B : OGBody V)
    (n : ℕ) (x : Fin (n + 1) → V) (k : Fin (n + 1)) (y : V) :
    (∑ j : Fin (n + 1), B.m * ogPotential D ((Function.update x k y) j)) =
      (∑ j : Fin (n + 1), B.m * ogPotential D (x j)) +
        (B.m * ogPotential D y - B.m * ogPotential D (x k)) := by
  have hE : (∑ j ∈ Finset.univ.erase k,
        B.m * ogPotential D ((Function.update x k y) j)) =
      (∑ j ∈ Finset.univ.erase k, B.m * ogPotential D (x j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ k), hE,
    Function.update_self]
  ring

/-- **Variation of the kinetic sum.** Replacing the path's site at
an INTERIOR `k` by `y` changes the kinetic sum by exactly the two
steps touching `k`: the step in (from the predecessor site) and
the step out (to the successor site). Every other step is
untouched. This is the discrete variation computation on which
the EL form rests. -/
theorem ogKinetic_update (D : OGResponseDatum V) (B : OGBody V)
    (n : ℕ) (x : Fin (n + 1) → V) (k : Fin (n + 1))
    (hk : 0 < k.val ∧ k.val < n) (y : V) :
    (∑ j : Fin n, B.m * seatKinetic D.w
        ((Function.update x k y) j.castSucc)
        ((Function.update x k y) j.succ)) =
      (∑ j : Fin n, B.m * seatKinetic D.w (x j.castSucc) (x j.succ)) +
        (B.m * (seatKinetic D.w (x ⟨k.val - 1, by omega⟩) y +
            seatKinetic D.w y (x ⟨k.val + 1, by omega⟩)) -
          B.m * (seatKinetic D.w (x ⟨k.val - 1, by omega⟩) (x k) +
            seatKinetic D.w (x k) (x ⟨k.val + 1, by omega⟩))) := by
  -- The two step-indices touching `k`: `j₁` (step into `k`) and
  -- `j₂` (step out of `k`).
  set j₁ : Fin n := ⟨k.val - 1, by omega⟩ with hj₁
  set j₂ : Fin n := ⟨k.val, by omega⟩ with hj₂
  have hj₁₂ : j₁ ≠ j₂ := by
    intro h
    have := congrArg Fin.val h
    simp [hj₁, hj₂] at this
    omega
  have hj₁v : j₁.val = k.val - 1 := by rw [hj₁]
  have hj₂v : j₂.val = k.val := by rw [hj₂]
  -- Index facts in `Fin (n+1)`.
  have h₁s : j₁.succ = k := by
    apply Fin.ext
    simp [Fin.val_succ, hj₁]
    omega
  have h₂c : j₂.castSucc = k :=
    Fin.ext (by simp only [Fin.val_castSucc]; exact hj₂v)
  have h₁c : j₁.castSucc = ⟨k.val - 1, by omega⟩ := by
    apply Fin.ext
    simp [hj₁]
  have h₂s : j₂.succ = ⟨k.val + 1, by omega⟩ :=
    Fin.ext (by show j₂.val + 1 = k.val + 1; omega)
  have h₁cne : j₁.castSucc ≠ k := by
    intro h
    have := congrArg Fin.val h
    simp [h₁c] at this
    omega
  have h₂sne : j₂.succ ≠ k := by
    intro h
    have := congrArg Fin.val h
    simp [h₂s] at this
  -- Split any path's kinetic sum into the untouched part and the
  -- two touching steps.
  have hsplit : ∀ z : Fin (n + 1) → V,
      (∑ j : Fin n, B.m * seatKinetic D.w (z j.castSucc) (z j.succ)) =
        (∑ j ∈ Finset.univ \ {j₁, j₂},
          B.m * seatKinetic D.w (z j.castSucc) (z j.succ)) +
          (B.m * seatKinetic D.w (z j₁.castSucc) (z j₁.succ) +
            B.m * seatKinetic D.w (z j₂.castSucc) (z j₂.succ)) := by
    intro z
    rw [← Finset.sum_sdiff (Finset.subset_univ {j₁, j₂}),
      Finset.sum_pair hj₁₂]
  rw [hsplit (Function.update x k y), hsplit x]
  have hrest : (∑ j ∈ Finset.univ \ {j₁, j₂},
        B.m * seatKinetic D.w
          ((Function.update x k y) j.castSucc)
          ((Function.update x k y) j.succ)) =
      (∑ j ∈ Finset.univ \ {j₁, j₂},
        B.m * seatKinetic D.w (x j.castSucc) (x j.succ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj₁' : j ≠ j₁ := by
      have h := (Finset.mem_sdiff.mp hj).2
      simp only [Finset.mem_insert, Finset.mem_singleton,
        not_or] at h
      exact h.1
    have hj₂' : j ≠ j₂ := by
      have h := (Finset.mem_sdiff.mp hj).2
      simp only [Finset.mem_insert, Finset.mem_singleton,
        not_or] at h
      exact h.2
    have hc : j.castSucc ≠ k := by
      intro h
      apply hj₂'
      apply Fin.ext
      have := congrArg Fin.val h
      simpa using this
    have hs : j.succ ≠ k := by
      intro h
      apply hj₁'
      apply Fin.ext
      have := congrArg Fin.val h
      simp [Fin.val_succ] at this
      omega
    rw [Function.update_of_ne hc, Function.update_of_ne hs]
  rw [hrest, Function.update_of_ne h₁cne,
    Function.update_of_ne h₂sne, h₁s, h₂c, h₁c, h₂s,
    Function.update_self]
  ring

/-- **The frozen action, unfolded.** `ogAction` is by definition
the kinetic sum minus the potential sum; this is its
definitional form, stated for rewriting. -/
theorem ogAction_eq (D : OGResponseDatum V) (B : OGBody V) (n : ℕ)
    (x : Fin (n + 1) → V) :
    ogAction D B n x =
      (∑ j : Fin n, B.m * seatKinetic D.w (x j.castSucc) (x j.succ)) -
        (∑ j : Fin (n + 1), B.m * ogPotential D (x j)) :=
  rfl

/-- **The action's variation is the site-balance difference.**
For an interior `k` and any site `y`:
`A (x with k ↦ y) = A x + (balance y − balance (x k))`, where
`balance` is the pin's `ogSiteBalance`. The entire content of
the EL form is this identity plus the definition of
stationarity. -/
theorem ogAction_update (D : OGResponseDatum V) (B : OGBody V)
    (n : ℕ) (x : Fin (n + 1) → V) (k : Fin (n + 1))
    (hk : 0 < k.val ∧ k.val < n) (y : V) :
    ogAction D B n (Function.update x k y) = ogAction D B n x +
      (ogSiteBalance D B n x k hk y -
        ogSiteBalance D B n x k hk (x k)) := by
  have hbal : ∀ z : V, ogSiteBalance D B n x k hk z =
      B.m * (seatKinetic D.w (x ⟨k.val - 1, by omega⟩) z +
          seatKinetic D.w z (x ⟨k.val + 1, by omega⟩)) -
        B.m * ogPotential D z :=
    fun z => rfl
  rw [ogAction_eq, ogAction_eq, ogKinetic_update D B n x k hk y,
    ogPotential_update D B n x k y, hbal y, hbal (x k)]
  ring

/-- **THE EL FORM (OG-RL-1's headline; the pin's frozen target
`OGResponseELForm`).** A path is stationary if and only if at
every interior site, the site balance is minimal at the path's
own site: no single-site move lowers the balance further.
Derived in
both directions from `ogAction_update` and the definition of
stationarity — the response (the stationary path set) is an
output of the action, not an input. Variational form only:
path-optimality on a general graph, not an acceleration vector
(D2-4, predeclared). -/
theorem og_el_form (D : OGResponseDatum V) (B : OGBody V) (n : ℕ)
    (x : Fin (n + 1) → V) :
    OGResponseELForm D B n x := by
  constructor
  · intro h k hk y
    have hst := h k hk.1 hk.2 y
    rw [ogAction_update D B n x k hk y] at hst
    linarith
  · intro h k hk₁ hk₂ y
    rw [ogAction_update D B n x k ⟨hk₁, hk₂⟩ y]
    have hb := h k ⟨hk₁, hk₂⟩ y
    linarith

/-! ## OG-RL-1b — the scaling engine + the Fin 2 witness seat

Appended as the second banked brick of OG-RL-1 (the small-brick
split recorded in this module's header; design frozen in
`STATUS-OGRL.md`). Contents (7 declarations):

- `ogAction_scaling` — scaling the body's mass by `t > 0`
  scales the action by `t`: the mass is one scalar factor on
  both sums of the frozen action.
- `ogStationary_scaling` — stationarity is invariant under
  positive mass scaling. This is the engine of OG-RL-2's
  universality theorem.
- `ogWitnessWeight` — the two-site seat: weight `1` across the
  two sites, `0` on the diagonal.
- `ogWitnessDatum` — the witness datum on `Fin 2`: the witness
  weight, `θ = 0`, source `ρ` = the point mass at site `1`,
  ground `b = 0`, complete positivity off the diagonal.
- `ogWitnessPotential_zero` — the witness potential vanishes
  at the ground — the landed `groundedPotential_at_ground`
  itself, read at the witness datum.
- `ogWitnessPotential_one` — the witness potential at the
  source site is exactly `1`, computed from the landed Poisson
  equation (`laplacianOp_groundedPotential` at site `1`): the
  value is forced by `laplacianOp`'s conventions and the
  grounded inversion — no sign is chosen (K-OG-RL-SIGN).
- `ogWitness_not_stationary` — **non-vacuity**: the path
  `![0, 1, 0]` is NOT stationary at the witness seat — varying
  its interior site to the ground lowers the action `1 → 0`.
  Stationarity bites at a named seat: K-OG-RL-VAC's every-path
  direction is answered here (the existence direction is
  OG-RL-3's shadow form). -/

/-- **The action scales with the mass.** Replacing the body
`B` by the body of mass `t * B.m` (for `t > 0`) multiplies the
action by `t`, at every path: the frozen action carries the
mass as a single scalar factor on both of its sums. -/
theorem ogAction_scaling (D : OGResponseDatum V) (B : OGBody V)
    {t : ℝ} (ht : 0 < t) (n : ℕ) (x : Fin (n + 1) → V) :
    ogAction D ⟨t * B.m, mul_pos ht B.hm⟩ n x =
      t * ogAction D B n x := by
  rw [ogAction_eq, ogAction_eq]
  show (∑ j : Fin n, (t * B.m) * seatKinetic D.w (x j.castSucc)
        (x j.succ)) -
      (∑ j : Fin (n + 1), (t * B.m) * ogPotential D (x j)) =
    t * ((∑ j : Fin n, B.m * seatKinetic D.w (x j.castSucc)
        (x j.succ)) -
      (∑ j : Fin (n + 1), B.m * ogPotential D (x j)))
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

/-- **Stationarity is invariant under positive mass scaling.**
A path is stationary for the body of mass `t * B.m` (`t > 0`)
if and only if it is stationary for `B`: the common positive
factor cancels from every variational inequality. Proved from
`ogAction_scaling` alone — the cancellation is a theorem
about the frozen action, never a hypothesis (K-OG-RL-UNIV). -/
theorem ogStationary_scaling (D : OGResponseDatum V)
    (B : OGBody V) {t : ℝ} (ht : 0 < t) (n : ℕ)
    (x : Fin (n + 1) → V) :
    ogStationary D ⟨t * B.m, mul_pos ht B.hm⟩ n x ↔
      ogStationary D B n x := by
  constructor
  · intro h k hk1 hk2 y
    have h' := h k hk1 hk2 y
    rw [ogAction_scaling D B ht, ogAction_scaling D B ht] at h'
    exact le_of_mul_le_mul_left h' ht
  · intro h k hk1 hk2 y
    have h' := h k hk1 hk2 y
    rw [ogAction_scaling D B ht, ogAction_scaling D B ht]
    exact mul_le_mul_of_nonneg_left h' ht.le

/-- **The witness seat's weights.** Two sites; weight `1`
across, `0` on the diagonal — complete positivity off the
diagonal, as the grounded inversion requires. -/
def ogWitnessWeight : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then 0 else 1

/-- **The witness datum** on `Fin 2`: the witness weight,
`θ = 0`, source `ρ` the point mass at site `1`, ground
`b = 0`. The smallest seat at which the grounded channel, the
EL form, and stationarity can be checked with content. -/
def ogWitnessDatum : OGResponseDatum (Fin 2) where
  w := ogWitnessWeight
  w_nonneg := by
    intro i j
    by_cases h : i = j <;> simp [ogWitnessWeight, h]
  w_symm := by
    intro i j
    by_cases h : i = j
    · subst h
      simp [ogWitnessWeight]
    · have h' : j ≠ i := Ne.symm h
      simp [ogWitnessWeight, h, h']
  θ := 0
  ρ := fun i => if i = 1 then 1 else 0
  b := 0
  w_pos := by
    intro i j hij
    simp [ogWitnessWeight, hij]

/-- **The witness potential vanishes at the ground.** This is
the landed `groundedPotential_at_ground`, read at the witness
datum (whose ground is site `0`). -/
theorem ogWitnessPotential_zero :
    ogPotential ogWitnessDatum 0 = 0 :=
  groundedPotential_at_ground ogWitnessDatum.w
    ogWitnessDatum.w_symm ogWitnessDatum.w_nonneg
    ogWitnessDatum.w_pos ogWitnessDatum.b ogWitnessDatum.ρ

/-- **The witness potential at the source site is exactly
`1`.** Computed from the landed Poisson equation at site `1`:
`laplacianOp w φ 1 = w 1 0 · (φ 1 − φ 0) + w 1 1 · (φ 1 − φ 1)
= φ 1`, and the equation sets this equal to `ρ 1 = 1`. The
value is forced by `laplacianOp`'s landed conventions and the
grounded inversion — no sign is chosen anywhere
(K-OG-RL-SIGN). -/
theorem ogWitnessPotential_one :
    ogPotential ogWitnessDatum 1 = 1 := by
  have hw10 : ogWitnessDatum.w 1 0 = 1 := by
    show (if (1 : Fin 2) = 0 then (0 : ℝ) else 1) = 1
    exact if_neg (by decide)
  have hw11 : ogWitnessDatum.w 1 1 = 0 := by
    show (if (1 : Fin 2) = 1 then (0 : ℝ) else 1) = 0
    exact if_pos rfl
  have hρ1 : ogWitnessDatum.ρ 1 = 1 := by
    show (if (1 : Fin 2) = 1 then (1 : ℝ) else 0) = 1
    exact if_pos rfl
  have hlap : laplacianOp ogWitnessDatum.w
      (ogPotential ogWitnessDatum) 1 = ogWitnessDatum.ρ 1 :=
    laplacianOp_groundedPotential ogWitnessDatum.w
      ogWitnessDatum.w_symm ogWitnessDatum.w_nonneg
      ogWitnessDatum.w_pos ogWitnessDatum.b ogWitnessDatum.ρ
      (by decide)
  simp only [laplacianOp, Fin.sum_univ_two] at hlap
  rw [hw10, hw11, ogWitnessPotential_zero, hρ1] at hlap
  linarith

/-- **Non-vacuity at the witness seat.** The path
`![0, 1, 0]` — ground, source site, ground — is NOT
stationary for the unit body: varying its interior site to
the ground lowers the action from `1` to `0`. So
stationarity is not vacuous in the every-path direction at a
named seat (K-OG-RL-VAC answered in that direction; the
existence direction is OG-RL-3's shadow form). -/
theorem ogWitness_not_stationary :
    ¬ ogStationary ogWitnessDatum ⟨1, one_pos⟩ 2 ![0, 1, 0] := by
  intro h
  have hvar := h 1 (by decide) (by decide) 0
  have hw00 : ogWitnessDatum.w 0 0 = 0 := by
    show (if (0 : Fin 2) = 0 then (0 : ℝ) else 1) = 0
    exact if_pos rfl
  have hw01 : ogWitnessDatum.w 0 1 = 1 := by
    show (if (0 : Fin 2) = 1 then (0 : ℝ) else 1) = 1
    exact if_neg (by decide)
  have hw10 : ogWitnessDatum.w 1 0 = 1 := by
    show (if (1 : Fin 2) = 0 then (0 : ℝ) else 1) = 1
    exact if_neg (by decide)
  have hw11 : ogWitnessDatum.w 1 1 = 0 := by
    show (if (1 : Fin 2) = 1 then (0 : ℝ) else 1) = 0
    exact if_pos rfl
  have hA1 : ogAction ogWitnessDatum ⟨1, one_pos⟩ 2 ![0, 1, 0]
      = 1 := by
    rw [ogAction_eq, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [seatKinetic, hw00, hw01, hw10, hw11,
      ogWitnessPotential_zero, ogWitnessPotential_one]
  have hA2 : ogAction ogWitnessDatum ⟨1, one_pos⟩ 2
      (Function.update ![0, 1, 0] 1 0) = 0 := by
    rw [ogAction_eq, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [seatKinetic, hw00, hw01, hw10, hw11,
      ogWitnessPotential_zero, ogWitnessPotential_one,
      Function.update]
  rw [hA1, hA2] at hvar
  norm_num at hvar

/-! ## OG-RL-2 — universality + the second-channel countermodel

Appended as the third banked brick (design frozen in
`STATUS-OGRL.md`; the pin's charged definitions were re-read
verbatim before drafting). Contents (8 declarations):

- `ogStationary_mass_congr` — stationarity sees only the
  mass: two bodies of equal mass have the same stationary
  paths, since `ogAction`'s only body-dependence is `B.m`.
- `og_universality` — **the universality theorem**: the pin's
  frozen `OGResponseUniversalityForm`. Any two bodies have the
  same stationary paths. Proved from `ogStationary_scaling`
  with `t := B₂.m / B₁.m`: the mass factor cancels. This is a
  THEOREM about the frozen action — it enters as no
  hypothesis, field condition, or definition (K-OG-RL-UNIV).
- `ogWitnessDatum_w` — the witness datum's weights, evaluated:
  the projection is the witness weight function.
- `ogWitnessChargePotential_zero` / `ogWitnessChargePotential_one`
  — the second channel's potential at the witness seat, for
  `σ = ρ`: it is the grounded potential of the same source, so
  its values are the witness potential's values, `0` and `1`.
- `ogChargedAction_witness_path` — the charged action of the
  path `![0, 1, 0]` at the witness seat is `1 − q`: the
  uncharged action `1`, minus the charge coupling `q · 1`.
- `ogChargedAction_witness_update` — the charged action of
  the interior variation `![0, 0, 0]` is `0` at every charge:
  the varied path sits at the ground throughout, where both
  potentials vanish.
- `og_countermodel` — **the countermodel**: the pin's frozen
  `OGResponseCountermodelForm` at the witness seat. The path
  `![0, 1, 0]` under the unit body is charged-stationary at
  charge `1` (its only lowering variation is exactly paid by
  the coupling: `0 ≥ 1 − 1`) and NOT charged-stationary at
  charge `0` (`0 ≥ 1` fails). Same datum, same body, same
  mass, same path — the response moves with the second
  channel's coupling, so mass-independence is content with a
  failure mode, not a vacuity (D2-6, CT-8 answered;
  K-OG-RL-SECOND does not fire). -/

/-- **Stationarity sees only the mass.** Two bodies of equal
mass have exactly the same stationary paths: by
`ogAction_eq`, the action's only body-dependence is the
scalar factor `B.m`, and stationarity is built from the
action alone. (This is also the route around the dependent
proof field: a body is never rewritten inside its own
positivity proof — the mass is compared at the level of the
action, where it is a plain real factor.) -/
theorem ogStationary_mass_congr (D : OGResponseDatum V)
    (B B' : OGBody V) (hm : B.m = B'.m) (n : ℕ)
    (x : Fin (n + 1) → V) :
    ogStationary D B n x ↔ ogStationary D B' n x := by
  simp only [ogStationary, ogAction_eq, hm]

/-- **THE UNIVERSALITY THEOREM (OG-RL-2's headline; the pin's
frozen target `OGResponseUniversalityForm`).** The stationary
path set is independent of the body's mass: for any two
bodies — which, an `OGBody` carrying nothing but its mass,
differ only in mass — stationarity under one is stationarity
under the other. The proof is the scaling engine at
`t = B₂.m / B₁.m > 0`, transported across the mass identity
`B₂.m / B₁.m * B₁.m = B₂.m` by `ogStationary_mass_congr`. -/
theorem og_universality (D : OGResponseDatum V) (n : ℕ)
    (x : Fin (n + 1) → V) : OGResponseUniversalityForm D n x := by
  intro B₁ B₂
  have ht : 0 < B₂.m / B₁.m := div_pos B₂.hm B₁.hm
  have hmass : B₂.m / B₁.m * B₁.m = B₂.m :=
    div_mul_cancel₀ B₂.m (ne_of_gt B₁.hm)
  have h := ogStationary_scaling D B₁ ht n x
  have hcong := ogStationary_mass_congr D
    ⟨B₂.m / B₁.m * B₁.m, mul_pos ht B₁.hm⟩ B₂ hmass n x
  exact h.symm.trans hcong

/-- **The witness datum's weights, evaluated.** The datum's
weight projection is the witness weight function itself. -/
theorem ogWitnessDatum_w : ∀ i j : Fin 2,
    ogWitnessDatum.w i j = if i = j then 0 else 1 :=
  fun i j => rfl

/-- **The second channel's potential at the ground** (witness
seat, `σ = ρ`): the charge potential of the datum's own
source is the datum's potential, which vanishes at the
ground. -/
theorem ogWitnessChargePotential_zero :
    ogChargePotential ogWitnessDatum ogWitnessDatum.ρ 0 = 0 :=
  ogWitnessPotential_zero

/-- **The second channel's potential at the source site**
(witness seat, `σ = ρ`): exactly `1`, as for the first
channel. -/
theorem ogWitnessChargePotential_one :
    ogChargePotential ogWitnessDatum ogWitnessDatum.ρ 1 = 1 :=
  ogWitnessPotential_one

/-- **The charged action of the witness path.** At the
witness seat, for the unit body and `σ = ρ`, the path
`![0, 1, 0]` has charged action `1 − q`: the uncharged
action `1` (OG-RL-1b) minus the coupling `q` times the
charge-potential sum `ψ(0) + ψ(1) + ψ(0) = 1`. -/
theorem ogChargedAction_witness_path (q : ℝ) :
    ogChargedAction ogWitnessDatum ⟨1, one_pos⟩ q
      ogWitnessDatum.ρ 2 ![0, 1, 0] = 1 - q := by
  simp only [ogChargedAction]
  rw [ogAction_eq, Fin.sum_univ_two, Fin.sum_univ_three,
    Fin.sum_univ_three]
  norm_num [seatKinetic, ogWitnessDatum_w,
    ogWitnessPotential_zero, ogWitnessPotential_one,
    ogWitnessChargePotential_zero, ogWitnessChargePotential_one]

/-- **The charged action of the varied witness path.** The
interior variation of `![0, 1, 0]` to the ground —
`![0, 0, 0]` — has charged action `0` at EVERY charge: it
sits at the ground throughout, where the kinetic term, the
potential, and the charge potential all vanish. -/
theorem ogChargedAction_witness_update (q : ℝ) :
    ogChargedAction ogWitnessDatum ⟨1, one_pos⟩ q
      ogWitnessDatum.ρ 2 (Function.update ![0, 1, 0] 1 0)
      = 0 := by
  simp only [ogChargedAction]
  rw [ogAction_eq, Fin.sum_univ_two, Fin.sum_univ_three,
    Fin.sum_univ_three]
  norm_num [seatKinetic, ogWitnessDatum_w,
    ogWitnessPotential_zero, ogWitnessPotential_one,
    ogWitnessChargePotential_zero, ogWitnessChargePotential_one,
    Function.update]

/-- **THE COUNTERMODEL (OG-RL-2's second headline; the pin's
frozen target `OGResponseCountermodelForm`).** At the
witness seat, with `σ = ρ`, the unit body, and the path
`![0, 1, 0]`: the path is charged-stationary under charge
`1` and not under charge `0`. Everything else is held fixed
— same datum, same body, same mass, same path — and the
response still moves with the second channel's coupling.
Universality for mass alone is therefore a theorem with a
failure mode (D2-6); K-OG-RL-SECOND does not fire. -/
theorem og_countermodel :
    OGResponseCountermodelForm ogWitnessDatum
      ogWitnessDatum.ρ 2 := by
  refine ⟨⟨1, one_pos⟩, 1, 0, ![0, 1, 0], one_ne_zero, ?_, ?_⟩
  · intro k hk1 hk2 y
    have hk : k = 1 := by
      have hv : k.val = 1 := by omega
      exact Fin.ext hv
    subst hk
    have hy : y = 0 ∨ y = 1 := by
      have h2 : y.val = 0 ∨ y.val = 1 := by
        have hlt := y.isLt
        omega
      rcases h2 with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases hy with rfl | rfl
    · rw [ogChargedAction_witness_update,
        ogChargedAction_witness_path]
      norm_num
    · have hUpd : ogChargedAction ogWitnessDatum ⟨1, one_pos⟩
          1 ogWitnessDatum.ρ 2
          (Function.update ![0, 1, 0] 1 1) = 0 := by
        simp only [ogChargedAction]
        rw [ogAction_eq, Fin.sum_univ_two, Fin.sum_univ_three,
          Fin.sum_univ_three]
        norm_num [seatKinetic, ogWitnessDatum_w,
          ogWitnessPotential_zero, ogWitnessPotential_one,
          ogWitnessChargePotential_zero,
          ogWitnessChargePotential_one, Function.update]
      rw [hUpd, ogChargedAction_witness_path]
      norm_num
  · intro h
    have hvar := h 1 (by decide) (by decide) 0
    rw [ogChargedAction_witness_update,
      ogChargedAction_witness_path] at hvar
    norm_num at hvar

/-! ## OG-RL-3a — the shadow seat + the datum-level assembly

The first of the two banked bricks of OG-RL-3 (the
small-brick split, as for OG-RL-1a/1b; design frozen in the
scope §3 and `STATUS-OGRL.md`). Contents (8 declarations):

- `ogShadowWeight` — the completed path-graph weights on
  `Fin 3`: adjacent sites carry weight `1`, the distance-2
  pair carries `1/2`, the diagonal `0`. COMPLETED, because
  the grounded inversion requires complete positivity
  (`w_pos`): a literal path graph (weight `0` at distance 2)
  is not a seat the channel can run on — the completion is
  the landed hypothesis's own demand, recorded here.
- `ogShadowDatum` — the shadow datum: the completed
  weights, `θ = 0`, source `ρ` the point mass at the far
  site `2`, ground `b = 0`.
- `ogShadowDatum_w` — the datum's weights, evaluated.
- `ogShadowPotential_ground` / `ogShadowPotential_mid` /
  `ogShadowPotential_source` — the grounded potential of
  the point source, COMPUTED: `φ = (0, 1/2, 1)`. The values
  are forced by the two landed Poisson equations at the
  ungrounded sites — at site `1`: `2φ₁ − φ₂ = ρ(1) = 0`;
  at site `2`: `(3/2)φ₂ − φ₁ = ρ(2) = 1` — solved, not
  chosen (K-OG-RL-SIGN).
- `og_exists_stationary` — the finite-minimum engine: over
  any extended datum, any body, any step count, a
  stationary path EXISTS — a global minimizer of the
  action over the finite path space is single-site
  stationary by minimality alone.
- `og_shadow_form` — **the datum-level assembly**: the
  pin's frozen `OGResponseShadowForm`, proved for EVERY
  extended datum. The law has instances over the datum
  itself, not only over bare functions; K-OG-RL-VAC's
  no-instances direction is answered at full generality.
  (The form's source hypotheses are the physical regime's;
  the existence half needs none of them — the minimum
  argument is unconditional, and the brick says so rather
  than pretend otherwise.) -/

/-- **The completed path-graph weights** on `Fin 3`:
weight `1` between adjacent sites, `1/2` between the two
ends (the distance-2 pair), `0` on the diagonal. -/
noncomputable def ogShadowWeight : Fin 3 → Fin 3 → ℝ :=
  fun i j => if i = j then 0
    else if i.val + j.val = 1 ∨ i.val + j.val = 3 then 1
    else 1 / 2

/-- **The shadow datum** on `Fin 3`: the completed
path-graph weights, `θ = 0`, source `ρ` the point mass at
the far site `2`, ground `b = 0`. -/
noncomputable def ogShadowDatum : OGResponseDatum (Fin 3) where
  w := ogShadowWeight
  w_nonneg := by
    intro i j
    by_cases h1 : i = j <;>
      by_cases h2 : i.val + j.val = 1 ∨ i.val + j.val = 3 <;>
      simp [ogShadowWeight, h1, h2]
  w_symm := by
    intro i j
    by_cases h : i = j
    · subst h
      simp [ogShadowWeight]
    · have h' : j ≠ i := Ne.symm h
      have hsum : (i.val + j.val = 1 ∨ i.val + j.val = 3) ↔
          (j.val + i.val = 1 ∨ j.val + i.val = 3) := by
        rw [add_comm i.val j.val]
      simp [ogShadowWeight, h, h', hsum]
  θ := 0
  ρ := fun i => if i = 2 then 1 else 0
  b := 0
  w_pos := by
    intro i j hij
    by_cases h2 : i.val + j.val = 1 ∨ i.val + j.val = 3 <;>
      simp [ogShadowWeight, hij, h2]

/-- **The shadow datum's weights, evaluated.** The datum's
weight projection is the completed path-graph weight
function itself. -/
theorem ogShadowDatum_w : ∀ i j : Fin 3,
    ogShadowDatum.w i j = if i = j then 0
      else if i.val + j.val = 1 ∨ i.val + j.val = 3 then 1
      else 1 / 2 :=
  fun i j => rfl

/-- **The shadow potential at the ground**: `0` — the
landed `groundedPotential_at_ground` at the shadow datum. -/
theorem ogShadowPotential_ground :
    ogPotential ogShadowDatum 0 = 0 :=
  groundedPotential_at_ground ogShadowDatum.w
    ogShadowDatum.w_symm ogShadowDatum.w_nonneg
    ogShadowDatum.w_pos ogShadowDatum.b ogShadowDatum.ρ

/-- **The shadow potential at the middle site**: exactly
`1/2`. Computed from the landed Poisson equations at the
two ungrounded sites (see the section header): the system
`2φ₁ − φ₂ = 0`, `(3/2)φ₂ − φ₁ = 1` forces `φ₁ = 1/2`
(and `φ₂ = 1`). -/
theorem ogShadowPotential_mid :
    ogPotential ogShadowDatum 1 = 1 / 2 := by
  have hρ1 : ogShadowDatum.ρ 1 = 0 := by
    show (if (1 : Fin 3) = 2 then (1 : ℝ) else 0) = 0
    exact if_neg (by decide)
  have hρ2 : ogShadowDatum.ρ 2 = 1 := by
    show (if (2 : Fin 3) = 2 then (1 : ℝ) else 0) = 1
    exact if_pos rfl
  have hlap1 : laplacianOp ogShadowDatum.w
      (ogPotential ogShadowDatum) 1 = ogShadowDatum.ρ 1 :=
    laplacianOp_groundedPotential ogShadowDatum.w
      ogShadowDatum.w_symm ogShadowDatum.w_nonneg
      ogShadowDatum.w_pos ogShadowDatum.b ogShadowDatum.ρ
      (by decide)
  have hlap2 : laplacianOp ogShadowDatum.w
      (ogPotential ogShadowDatum) 2 = ogShadowDatum.ρ 2 :=
    laplacianOp_groundedPotential ogShadowDatum.w
      ogShadowDatum.w_symm ogShadowDatum.w_nonneg
      ogShadowDatum.w_pos ogShadowDatum.b ogShadowDatum.ρ
      (by decide)
  simp only [laplacianOp, Fin.sum_univ_three] at hlap1 hlap2
  rw [hρ1] at hlap1
  rw [hρ2] at hlap2
  norm_num [ogShadowDatum_w, ogShadowPotential_ground]
    at hlap1 hlap2
  linarith

/-- **The shadow potential at the source site**: exactly
`1` — the full point mass, read at its own site through the
grounded inversion. Same computation as
`ogShadowPotential_mid`: the system `2φ₁ − φ₂ = 0`,
`(3/2)φ₂ − φ₁ = 1` forces `φ₂ = 1`. -/
theorem ogShadowPotential_source :
    ogPotential ogShadowDatum 2 = 1 := by
  have hρ1 : ogShadowDatum.ρ 1 = 0 := by
    show (if (1 : Fin 3) = 2 then (1 : ℝ) else 0) = 0
    exact if_neg (by decide)
  have hρ2 : ogShadowDatum.ρ 2 = 1 := by
    show (if (2 : Fin 3) = 2 then (1 : ℝ) else 0) = 1
    exact if_pos rfl
  have hlap1 : laplacianOp ogShadowDatum.w
      (ogPotential ogShadowDatum) 1 = ogShadowDatum.ρ 1 :=
    laplacianOp_groundedPotential ogShadowDatum.w
      ogShadowDatum.w_symm ogShadowDatum.w_nonneg
      ogShadowDatum.w_pos ogShadowDatum.b ogShadowDatum.ρ
      (by decide)
  have hlap2 : laplacianOp ogShadowDatum.w
      (ogPotential ogShadowDatum) 2 = ogShadowDatum.ρ 2 :=
    laplacianOp_groundedPotential ogShadowDatum.w
      ogShadowDatum.w_symm ogShadowDatum.w_nonneg
      ogShadowDatum.w_pos ogShadowDatum.b ogShadowDatum.ρ
      (by decide)
  simp only [laplacianOp, Fin.sum_univ_three] at hlap1 hlap2
  rw [hρ1] at hlap1
  rw [hρ2] at hlap2
  norm_num [ogShadowDatum_w, ogShadowPotential_ground]
    at hlap1 hlap2
  linarith

/-- **Stationary paths exist — the finite-minimum
engine.** Over ANY extended datum, for any body and any
step count, some path is stationary: the path space
`Fin (n + 1) → V` is finite and nonempty, so the action
attains its minimum, and a global minimizer is
single-site stationary by minimality alone — every
single-site variation is another path, hence has no
smaller action. No hypothesis on the source is used. -/
theorem og_exists_stationary (D : OGResponseDatum V)
    (B : OGBody V) (n : ℕ) :
    ∃ x : Fin (n + 1) → V, ogStationary D B n x := by
  obtain ⟨x₀, -, hx₀⟩ := Finset.exists_min_image
    Finset.univ (ogAction D B n) Finset.univ_nonempty
  refine ⟨x₀, fun k _ _ y => hx₀ _ (Finset.mem_univ _)⟩

/-- **THE SHADOW FORM (OG-RL-3's assembly; the pin's
frozen target `OGResponseShadowForm`).** For every
extended datum: under a nonnegative source with some
positive mass off the ground, every body at every step
count has a stationary path. The law is stated and
proved over `OGResponseDatum` itself. The existence is
`og_exists_stationary` — it needs neither source
hypothesis, and the brick records that plainly: what the
hypotheses buy is the physical regime (and the computed
exhibit of OG-RL-3b), not the existence. -/
theorem og_shadow_form (D : OGResponseDatum V) :
    OGResponseShadowForm D :=
  fun _ _ B n => og_exists_stationary D B n

/-! ## OG-RL-3b — the EL attraction + the failure countermodel

The second banked brick of OG-RL-3. Contents (5 declarations):

- `ogShadow_step_stationary` — at the shadow seat, the
  path `![0, 2, 0]` (ground, source site, ground) is
  stationary for EVERY body: its action is `0`; the
  interior variations give `0` (to the ground) and
  `3m/2` (to the middle site) — no variation lowers it.
- `ogShadow_el_attraction` — **the EL attraction
  content**, in variational form: by `og_el_form`, the
  site balance at the stationary path's own middle site
  — the source site — is minimal among ALL sites. The
  step from the ground goes to the far source site rather
  than the adjacent middle site (whose variation costs
  `3m/2 > 0`): the potential term pays for the longer
  step. The direction is derived from `laplacianOp`'s
  conventions via the computed potential
  `φ = (0, 1/2, 1)` — no sign is chosen (K-OG-RL-SIGN).
- `ogShadowNegDatum` — the failure seat: the shadow
  datum with source positivity REMOVED — `ρ` the
  NEGATIVE point mass at site `2`.
- `ogShadowNegPotential_source` — its potential at the
  source site is `−1`: the same landed equations with
  the flipped source, `2φ₁ − φ₂ = 0`,
  `(3/2)φ₂ − φ₁ = −1`.
- `ogShadowNeg_not_stationary` — **the failure
  countermodel**: at the negative seat the step path
  `![0, 2, 0]` is NOT stationary — its action is `2`,
  and varying the middle site to the ground lowers it
  to `0`. The shadow's attraction conclusion fails
  exactly where its load-bearing hypothesis (source
  positivity) is removed (scope Gate 5c). The shadow
  FORM is not contradicted: its antecedents fail at
  this seat too — the exhibit's conclusion and the
  hypothesis fall together, which is the point. -/

/-- **The step path is stationary at the shadow seat.**
For every body, `![0, 2, 0]` — ground, source, ground —
is stationary: action `0`, and the only interior
variations give `0` (ground) and `3m/2` (middle site). -/
theorem ogShadow_step_stationary (B : OGBody (Fin 3)) :
    ogStationary ogShadowDatum B 2 ![0, 2, 0] := by
  intro k hk1 hk2 y
  have hk : k = 1 := by
    have hv : k.val = 1 := by omega
    exact Fin.ext hv
  subst hk
  have hpath : ogAction ogShadowDatum B 2 ![0, 2, 0] = 0 := by
    rw [ogAction_eq, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [seatKinetic, ogShadowDatum_w,
      ogShadowPotential_ground, ogShadowPotential_mid,
      ogShadowPotential_source]
    ring
  have hup0 : ogAction ogShadowDatum B 2
      (Function.update ![0, 2, 0] 1 0) = 0 := by
    rw [ogAction_eq, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [seatKinetic, ogShadowDatum_w,
      ogShadowPotential_ground, ogShadowPotential_mid,
      ogShadowPotential_source, Function.update]
  have hup1 : ogAction ogShadowDatum B 2
      (Function.update ![0, 2, 0] 1 1) = 3 * B.m / 2 := by
    rw [ogAction_eq, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [seatKinetic, ogShadowDatum_w,
      ogShadowPotential_ground, ogShadowPotential_mid,
      ogShadowPotential_source, Function.update]
    ring
  have hup2 : ogAction ogShadowDatum B 2
      (Function.update ![0, 2, 0] 1 2) = 0 := by
    rw [ogAction_eq, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [seatKinetic, ogShadowDatum_w,
      ogShadowPotential_ground, ogShadowPotential_mid,
      ogShadowPotential_source, Function.update]
    ring
  have hy : y = 0 ∨ y = 1 ∨ y = 2 := by
    have hlt := y.isLt
    have hv : y.val = 0 ∨ y.val = 1 ∨ y.val = 2 := by omega
    rcases hv with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  rcases hy with rfl | rfl | rfl
  · rw [hup0, hpath]
  · rw [hup1, hpath]
    linarith [B.hm]
  · rw [hup2, hpath]

/-- **THE EL ATTRACTION (OG-RL-3's variational sign
content).** At the shadow seat, the site balance of the
stationary step path `![0, 2, 0]`, at its own middle
site — the source site `2` — does not exceed the balance
at any other site: by the EL form (`og_el_form`), the
path's step sits at the balance's minimum, and that
minimum is attained at the source side, not at the
adjacent middle site (whose action cost is `3m/2`,
strictly positive, by `ogShadow_step_stationary`'s
computation). Derived from the grounded inversion and
`laplacianOp`'s conventions through the computed
potential — no sign is chosen anywhere (K-OG-RL-SIGN).
Variational form only: this is path-optimality, not an
acceleration vector (D2-4, predeclared). -/
theorem ogShadow_el_attraction (B : OGBody (Fin 3))
    (y : Fin 3) :
    ogSiteBalance ogShadowDatum B 2 ![0, 2, 0] 1
        (by decide) (![0, 2, 0] 1) ≤
      ogSiteBalance ogShadowDatum B 2 ![0, 2, 0] 1
        (by decide) y :=
  (og_el_form ogShadowDatum B 2 ![0, 2, 0]).mp
    (ogShadow_step_stationary B) 1 (by decide) y

/-- **The failure seat**: the shadow datum with source
positivity removed — the NEGATIVE point mass at site
`2`. Same completed weights, same ground; only the
source's sign is flipped. -/
noncomputable def ogShadowNegDatum :
    OGResponseDatum (Fin 3) where
  w := ogShadowWeight
  w_nonneg := by
    intro i j
    by_cases h1 : i = j <;>
      by_cases h2 : i.val + j.val = 1 ∨ i.val + j.val = 3 <;>
      simp [ogShadowWeight, h1, h2]
  w_symm := by
    intro i j
    by_cases h : i = j
    · subst h
      simp [ogShadowWeight]
    · have h' : j ≠ i := Ne.symm h
      have hsum : (i.val + j.val = 1 ∨ i.val + j.val = 3) ↔
          (j.val + i.val = 1 ∨ j.val + i.val = 3) := by
        rw [add_comm i.val j.val]
      simp [ogShadowWeight, h, h', hsum]
  θ := 0
  ρ := fun i => if i = 2 then -1 else 0
  b := 0
  w_pos := by
    intro i j hij
    by_cases h2 : i.val + j.val = 1 ∨ i.val + j.val = 3 <;>
      simp [ogShadowWeight, hij, h2]

/-- **The failure seat's potential at the source site**:
exactly `−1` — the shadow seat's computation with the
source flipped: `2φ₁ − φ₂ = 0` and `(3/2)φ₂ − φ₁ = −1`
force `φ = (0, −1/2, −1)`. -/
theorem ogShadowNegPotential_source :
    ogPotential ogShadowNegDatum 2 = -1 := by
  have hw : ∀ i j : Fin 3, ogShadowNegDatum.w i j =
      if i = j then 0
        else if i.val + j.val = 1 ∨ i.val + j.val = 3 then 1
        else 1 / 2 :=
    fun i j => rfl
  have hφ0 : ogPotential ogShadowNegDatum 0 = 0 :=
    groundedPotential_at_ground ogShadowNegDatum.w
      ogShadowNegDatum.w_symm ogShadowNegDatum.w_nonneg
      ogShadowNegDatum.w_pos ogShadowNegDatum.b
      ogShadowNegDatum.ρ
  have hρ1 : ogShadowNegDatum.ρ 1 = 0 := by
    show (if (1 : Fin 3) = 2 then (-1 : ℝ) else 0) = 0
    exact if_neg (by decide)
  have hρ2 : ogShadowNegDatum.ρ 2 = -1 := by
    show (if (2 : Fin 3) = 2 then (-1 : ℝ) else 0) = -1
    exact if_pos rfl
  have hlap1 : laplacianOp ogShadowNegDatum.w
      (ogPotential ogShadowNegDatum) 1 =
        ogShadowNegDatum.ρ 1 :=
    laplacianOp_groundedPotential ogShadowNegDatum.w
      ogShadowNegDatum.w_symm ogShadowNegDatum.w_nonneg
      ogShadowNegDatum.w_pos ogShadowNegDatum.b
      ogShadowNegDatum.ρ (by decide)
  have hlap2 : laplacianOp ogShadowNegDatum.w
      (ogPotential ogShadowNegDatum) 2 =
        ogShadowNegDatum.ρ 2 :=
    laplacianOp_groundedPotential ogShadowNegDatum.w
      ogShadowNegDatum.w_symm ogShadowNegDatum.w_nonneg
      ogShadowNegDatum.w_pos ogShadowNegDatum.b
      ogShadowNegDatum.ρ (by decide)
  simp only [laplacianOp, Fin.sum_univ_three] at hlap1 hlap2
  rw [hρ1] at hlap1
  rw [hρ2] at hlap2
  norm_num [hw, hφ0] at hlap1 hlap2
  linarith

/-- **THE FAILURE COUNTERMODEL (OG-RL-3's second
headline).** At the negative seat — source positivity
removed — the step path `![0, 2, 0]` is NOT stationary
for the unit body: its action is `2` (the flipped
potential now CHARGES the path for visiting the source
site), and varying the middle site to the ground lowers
the action to `0`. The attraction conclusion of the
shadow exhibit fails exactly where its load-bearing
hypothesis fails (scope Gate 5c; D2-6's third failure
mode). -/
theorem ogShadowNeg_not_stationary :
    ¬ ogStationary ogShadowNegDatum ⟨1, one_pos⟩ 2
      ![0, 2, 0] := by
  intro h
  have hvar := h 1 (by decide) (by decide) 0
  have hw : ∀ i j : Fin 3, ogShadowNegDatum.w i j =
      if i = j then 0
        else if i.val + j.val = 1 ∨ i.val + j.val = 3 then 1
        else 1 / 2 :=
    fun i j => rfl
  have hφ0 : ogPotential ogShadowNegDatum 0 = 0 :=
    groundedPotential_at_ground ogShadowNegDatum.w
      ogShadowNegDatum.w_symm ogShadowNegDatum.w_nonneg
      ogShadowNegDatum.w_pos ogShadowNegDatum.b
      ogShadowNegDatum.ρ
  have hA1 : ogAction ogShadowNegDatum ⟨1, one_pos⟩ 2
      ![0, 2, 0] = 2 := by
    rw [ogAction_eq, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [seatKinetic, hw, hφ0,
      ogShadowNegPotential_source]
  have hA2 : ogAction ogShadowNegDatum ⟨1, one_pos⟩ 2
      (Function.update ![0, 2, 0] 1 0) = 0 := by
    rw [ogAction_eq, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [seatKinetic, hw, hφ0, Function.update]
  rw [hA1, hA2] at hvar
  norm_num at hvar

end ThetLogos
