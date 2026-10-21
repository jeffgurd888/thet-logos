import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.ModEq

/-!
# ThetLogos.WindingRing — winding numbers on a finite phase ring (T1 target)

HONESTY LEDGER (read before citing):

- Status: **VERIFIED — STANDS WHOLE (T1).** Compiled green 2026-10-21
  (`lake build ThetLogos.WindingRing`, 3,117 jobs, 0 errors, 0 warnings);
  parent-verified: `.olean` present, strict recount 14, placeholder
  census 0, axioms on the five checked headline theorems standard
  only (`propext`, `Classical.choice`, `Quot.sound`). One draft proof
  was repaired in the open (`winding_neg`: a codomain-pinning failure
  of `Finset.sum_neg_distrib` under bare `exact`, replaced by an
  `eq_neg_of_add_eq_zero_left` argument) — proof body only; no
  statement, name, or fence changed.
- Commissioned by Jeff 2026-10-21, out of the sitting on strings,
  knots, light-as-wiggling-heat, and heat-separating-charge. The
  audit of that weave named three missing pieces — a single stage,
  the exchange rates, and the SLIP (the event that lets a conserved
  quantity change). This brick builds the smallest honest piece of
  that country: winding as integer bookkeeping on a finite ring,
  and the slip as the one event that changes it.
- The stage is a finite ring of `N` edges. A configuration is a step
  pattern `a : Fin N → ℤ`: integer phase steps, in ticks. `M : ℕ`
  is the number of ticks per full turn. When the total step count is
  divisible by `M`, the winding number is the exact quotient
  `(∑ i, a i) / M` in `ℤ`. Integer bookkeeping only: no real angles,
  no circle API, no analysis anywhere in this file.
- What is proved (targets): the zero pattern winds `0`; winding adds
  over compound patterns and negates over reversed ones; a slip —
  one edge gaining exactly one full turn of ticks — raises the
  winding by exactly `1` while changing NO visible phase (the
  slipped pattern agrees with the original modulo `M` at every
  edge: same local picture, different global sector — the headline
  of the brick); winding `0` does not imply the trivial pattern
  (the `(1, -1)` pattern on two edges is the counterexample); at
  lift level, the step sum over one period telescopes to
  `u(N) - u(0)`, and re-gauging a lift by an `N`-periodic integer
  function changes neither the period difference nor the winding —
  the winding is a property of the sector, not of the gauge.
- **Fences.** This is finite integer bookkeeping on a lift. It is
  NOT an Abrikosov vortex: no manifold, no order-parameter field,
  no broken phase, no core energy, no flux quantisation in physical
  units. It carries no knots: a ring has no crossings, and winding
  here is one integer, not a knot invariant. The word "flow" in
  this file means re-gauging invariance only — there is no
  time-evolution equation. Nothing here touches Yang–Mills, the
  continuum, or any Millennium statement.
- Kinship: `ThetLogos.FluxTwist` proved that a ring's spectrum is
  `2π`-periodic in the flux through it — a full turn of flux is
  invisible to the ring's eigenphases. The slip of this file is the
  discrete shadow of that fact, stated without spectra: add one
  full turn at one edge and every visible phase stands still; only
  the winding sector moves, by exactly one.
- Pre-named kill conditions. K1: if stating the winding needs
  real-angle or circle machinery, the design dies (the whole point
  is that `ℤ` suffices). K2: if the invariance needs a hidden
  step-size bound, it dies. K3: any placeholder proof, and this
  file does not count.
-/

namespace ThetLogos

variable {N : ℕ}

/- Section 1: patterns on the ring. -/

/-- The winding number of a step pattern: the total step count
divided by the ticks per turn, as exact integer division. The
theorems below only draw conclusions under the divisibility
hypotheses that make this quotient exact. -/
def winding (a : Fin N → ℤ) (M : ℕ) : ℤ :=
  (∑ i, a i) / ((M : ℤ))

/-- One slip at edge `i`: the pattern `a` with exactly one full turn
of ticks (`M` ticks) added at the single edge `i`. The slip is the
brick's one event: the only way the winding ever changes. -/
def slip (a : Fin N → ℤ) (i : Fin N) (M : ℕ) : Fin N → ℤ :=
  a + Pi.single i ((M : ℤ))

/-- If the period sum of `a` is exactly `M * q`, the winding of `a`
is `q`. This is the one place integer division is discharged, via
the divisibility carried in the hypothesis. -/
lemma winding_eq_of_sum_eq_mul {M : ℕ} {a : Fin N → ℤ} {q : ℤ}
    (hM0 : ((M : ℤ)) ≠ 0) (h : ∑ i, a i = (M : ℤ) * q) :
    winding a M = q := by
  unfold winding
  rw [h]
  exact Int.mul_ediv_cancel_left q hM0

/-- The zero pattern winds zero times. -/
theorem winding_zero (M : ℕ) : winding (0 : Fin N → ℤ) M = 0 := by
  simp [winding]

/-- Compound is addition: the winding of a compound pattern is the
sum of the windings, provided each part is itself divisible. -/
theorem winding_add {M : ℕ} {a b : Fin N → ℤ} (hM : 0 < M)
    (ha : ((M : ℤ)) ∣ ∑ i, a i) (hb : ((M : ℤ)) ∣ ∑ i, b i) :
    winding (a + b) M = winding a M + winding b M := by
  have hM0 : ((M : ℤ)) ≠ 0 := by exact_mod_cast hM.ne'
  obtain ⟨qa, hqa⟩ := ha
  obtain ⟨qb, hqb⟩ := hb
  have hsum : ∑ i, (a + b) i = (M : ℤ) * (qa + qb) := by
    have hsplit : ∑ i, (a + b) i = (∑ i, a i) + (∑ i, b i) := by
      simp only [Pi.add_apply]
      exact Finset.sum_add_distrib
    rw [hsplit, hqa, hqb]
    ring
  rw [winding_eq_of_sum_eq_mul hM0 hsum, winding_eq_of_sum_eq_mul hM0 hqa,
    winding_eq_of_sum_eq_mul hM0 hqb]

/-- Reversing every step negates the winding. -/
theorem winding_neg {M : ℕ} {a : Fin N → ℤ} (hM : 0 < M)
    (ha : ((M : ℤ)) ∣ ∑ i, a i) :
    winding (-a) M = -winding a M := by
  have hM0 : ((M : ℤ)) ≠ 0 := by exact_mod_cast hM.ne'
  obtain ⟨q, hq⟩ := ha
  have hsum : ∑ i, (-a) i = (M : ℤ) * (-q) := by
    have hneg : ∑ i, (-a) i = -∑ i, a i := by
      apply eq_neg_of_add_eq_zero_left
      rw [← Finset.sum_add_distrib]
      simp [Pi.neg_apply]
    rw [hneg, hq]
    ring
  rw [winding_eq_of_sum_eq_mul hM0 hsum, winding_eq_of_sum_eq_mul hM0 hq]

/-- A slip changes only its own edge, by exactly `M` ticks; every
other edge is untouched. -/
lemma slip_apply (a : Fin N → ℤ) (i : Fin N) (M : ℕ) (j : Fin N) :
    slip a i M j = a j + (if j = i then ((M : ℤ)) else 0) := by
  by_cases h : j = i
  · subst h
    simp [slip, Pi.single_eq_same]
  · simp [slip, h]

/-- The period sum of a slipped pattern is the old period sum plus
exactly one full turn of ticks. -/
lemma sum_slip (a : Fin N → ℤ) (i : Fin N) (M : ℕ) :
    ∑ j, slip a i M j = (∑ j, a j) + ((M : ℤ)) := by
  calc ∑ j, slip a i M j
      = ∑ j, (a j + (if j = i then ((M : ℤ)) else 0)) :=
        Finset.sum_congr rfl fun j _ => slip_apply a i M j
    _ = (∑ j, a j) + ∑ j, (if j = i then ((M : ℤ)) else 0) :=
        Finset.sum_add_distrib
    _ = (∑ j, a j) + ((M : ℤ)) := by
        congr 1
        simp [Finset.sum_ite_eq']

/-- The slip event: one slip raises the winding by exactly one. -/
theorem winding_slip {M : ℕ} {a : Fin N → ℤ} (hM : 0 < M)
    (ha : ((M : ℤ)) ∣ ∑ i, a i) (i : Fin N) :
    winding (slip a i M) M = winding a M + 1 := by
  have hM0 : ((M : ℤ)) ≠ 0 := by exact_mod_cast hM.ne'
  obtain ⟨q, hq⟩ := ha
  have hsum : ∑ j, slip a i M j = (M : ℤ) * (q + 1) := by
    rw [sum_slip, hq]
    ring
  rw [winding_eq_of_sum_eq_mul hM0 hsum, winding_eq_of_sum_eq_mul hM0 hq]

/-- Two slips at the same edge raise the winding by exactly two:
the event composes additively, like the winding itself. -/
theorem winding_slip_twice {M : ℕ} {a : Fin N → ℤ} (hM : 0 < M)
    (ha : ((M : ℤ)) ∣ ∑ i, a i) (i : Fin N) :
    winding (slip (slip a i M) i M) M = winding a M + 2 := by
  have ha' : ((M : ℤ)) ∣ ∑ j, slip a i M j := by
    rw [sum_slip]
    exact dvd_add ha (dvd_refl _)
  rw [winding_slip hM ha' i, winding_slip hM ha i]
  ring

/-- Slip invisibility — the headline. After a slip, the pattern
agrees with the original modulo `M` at EVERY edge: every visible
phase is unchanged. Only the winding sector moved. -/
theorem slip_modEq (a : Fin N → ℤ) (i : Fin N) (M : ℕ) (j : Fin N) :
    slip a i M j ≡ a j [ZMOD ((M : ℤ))] := by
  rw [Int.modEq_iff_dvd, slip_apply]
  split_ifs
  · exact ⟨-1, by ring⟩
  · exact ⟨0, by ring⟩

/-- The counterexample pattern on two edges: one step forward, one
step back. -/
def counterPattern : Fin 2 → ℤ := ![1, -1]

/-- Winding zero does NOT mean trivial: the `(1, -1)` pattern on a
two-edge ring with two ticks per turn has winding `0`, yet it is
not the zero pattern. The winding sees the sector, not the shape. -/
theorem counterexample : winding counterPattern 2 = 0 ∧ counterPattern ≠ 0 := by
  refine ⟨?_, ?_⟩
  · simp [winding, counterPattern, Fin.sum_univ_two]
  · intro h
    have h0 := congrFun h 0
    simp [counterPattern] at h0

/- Section 2: lifts and the flow (re-gauging invariance). -/

/-- Telescope: the steps of a lift `u : ℤ → ℤ` over one period add
up to the net change of the lift across the period. -/
theorem lift_steps_telescope (u : ℤ → ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range n, (u ((k : ℤ) + 1) - u (k : ℤ)) = u (n : ℤ) - u 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Bridge: the period sum of the lift's step pattern on the ring
(the `Fin N` sum) equals the lift's net change across the period —
the ring reads the lift. -/
theorem lift_period_sum (u : ℤ → ℤ) (N : ℕ) :
    ∑ i : Fin N, (u (((i : ℕ) : ℤ) + 1) - u ((i : ℕ) : ℤ)) = u (N : ℤ) - u 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => u ((k : ℤ) + 1) - u (k : ℤ)) N]
  exact lift_steps_telescope u N

/-- Flow invariance at lift level: re-gauging a lift by an
`N`-periodic integer function `p` (periodic as integers: `p` takes
the same value at `k + N` as at `k`, for every integer `k`) does
not change the lift's net change across one period. -/
theorem regauge_period_eq (u p : ℤ → ℤ) (N : ℕ)
    (hp : ∀ k : ℤ, p (k + ((N : ℤ))) = p k) :
    (u + p) ((N : ℤ)) - (u + p) 0 = u ((N : ℤ)) - u 0 := by
  have hN : p ((N : ℤ)) = p 0 := by
    have h0 := hp 0
    simpa using h0
  simp only [Pi.add_apply]
  rw [hN]
  ring

/-- Flow invariance of the winding itself: the step patterns of a
lift and of a periodically re-gauged lift have the same winding —
no divisibility hypothesis is even needed, because the period sums
are literally equal. The winding is a property of the sector, not
of the gauge. -/
theorem winding_regauge (u p : ℤ → ℤ) (N M : ℕ)
    (hp : ∀ k : ℤ, p (k + ((N : ℤ))) = p k) :
    winding (fun i : Fin N => (u + p) (((i : ℕ) : ℤ) + 1) - (u + p) ((i : ℕ) : ℤ)) M
      = winding (fun i : Fin N => u (((i : ℕ) : ℤ) + 1) - u ((i : ℕ) : ℤ)) M := by
  have h1 := lift_period_sum (u + p) N
  have h2 := lift_period_sum u N
  have h3 := regauge_period_eq u p N hp
  unfold winding
  simp only [h1, h2, h3]

end ThetLogos
