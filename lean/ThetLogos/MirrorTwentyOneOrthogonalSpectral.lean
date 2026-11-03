/-
# ORTHOGONAL PANTOREALITY — the grid operators and the joint zero mode

Brick: ORTHOGONAL PANTOREALITY, spectral module (Jeff's fire
word, 2026-11-02 21:45 EST; scoping:
`your_files/pantogram-construction-and-build-scoping-2026-11-02.md`,
Part 2). Foundation: `MirrorTwentyOneOrthogonal` (the two arm
pullbacks `Θ̂₁`, `Θ̂₂` on grid functions `Fin 21 × Fin 21 → ℝ`,
their exact commutation O1, and the jointly fixed equivalence
O2: 121 = 11² forced).

The scoping's dependency note: the Mirror-21 SPECTRAL brick was
NOT fired, so pin O3 carries the mirror–operator weld itself,
in the pointwise operator form used here: operators are
functions on functions, `(Lf)(i) = 2f(i) − f(i+1) − f(i−1)` over
`Z_21` indices (the cycle Laplacian of tonight's T2 run,
`python/mirror21_heat.py`). No matrix form is used, and
Spectral's single-ring kernel pin (its P4) is NOT built here.

**What this module proves — and all it proves (pins O3, O4, O4+):**
- O3 (arm derivatives don't leak): the coordinate Laplacians
  commute, `L₁ (L₂ f) = L₂ (L₁ f)`, and each `Lᵢ` commutes with
  both arm pullbacks — the weld, on both arms.
- O4: every constant grid function is a zero mode of `L₁ + L₂`
  (`lapSum_const`).
- O4+ (the stretch, kill-armed K-O4+): the kernel of `L₁ + L₂`
  is EXACTLY the constants (`lapSum_eq_zero_iff`), proved via
  the grid energy identity
  `∑ f · (L₁+L₂) f = ∑ (Δ₁ f)² + ∑ (Δ₂ f)²`
  (`lap₁_energy`, `lap₂_energy`, `lapSum_energy`).

Tier note: the joint zero-mode count is also derived at T2 by
`python/mirror21_orthogonal_heat.py` (pin O5: count = 1 from the
floating-point spectrum). O4+ is the T1 statement; the two
agree on the record, and neither is dressed as the other.

Finite, elementary, kernel-checked. No continuum operator, no
Dirac operator, no `D²` is asserted anywhere here.

**NO CLAIM** — parts of any official Millennium statement
closed by this module: 0. Dials: 0/4.
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Pi
import ThetLogos.MirrorTwentyOneOrthogonal

namespace ThetLogos

/-- `GridIndex` is a plain-`def` alias, so typeclass search does
not see through it to `Fin 21 × Fin 21`'s `Fintype` instance;
supply the instance explicitly so finite sums over the grid
elaborate. -/
instance : Fintype GridIndex := by
  show Fintype (Fin 21 × Fin 21)
  infer_instance

/-- The successor on the 21-cycle, `i ↦ i + 1 (mod 21)`. -/
def succ (i : ManifoldIndex) : ManifoldIndex :=
  ⟨(i.val + 1) % 21, Nat.mod_lt _ (by decide)⟩

/-- The predecessor on the 21-cycle, `i ↦ i − 1 (mod 21)`,
in closed form `i ↦ i + 20 (mod 21)`. -/
def pred (i : ManifoldIndex) : ManifoldIndex :=
  ⟨(i.val + 20) % 21, Nat.mod_lt _ (by decide)⟩

/-- The value of the successor, by definition. -/
theorem succ_val (i : ManifoldIndex) :
    (succ i).val = (i.val + 1) % 21 := rfl

/-- The value of the predecessor, by definition. -/
theorem pred_val (i : ManifoldIndex) :
    (pred i).val = (i.val + 20) % 21 := rfl

/-- Predecessor after successor is the identity. -/
theorem pred_succ (i : ManifoldIndex) : pred (succ i) = i := by
  apply Fin.ext
  show ((i.val + 1) % 21 + 20) % 21 = i.val
  have hi := i.isLt
  omega

/-- Successor after predecessor is the identity. -/
theorem succ_pred (i : ManifoldIndex) : succ (pred i) = i := by
  apply Fin.ext
  show ((i.val + 20) % 21 + 1) % 21 = i.val
  have hi := i.isLt
  omega

/-- The successor as a permutation of the 21 points. -/
def succEquiv : ManifoldIndex ≃ ManifoldIndex where
  toFun := succ
  invFun := pred
  left_inv := pred_succ
  right_inv := succ_pred

/-- The successor in the first grid coordinate, as a permutation
of the grid. -/
def succEquiv₁ : GridIndex ≃ GridIndex :=
  Equiv.prodCongr succEquiv (Equiv.refl ManifoldIndex)

/-- The successor in the second grid coordinate, as a permutation
of the grid. -/
def succEquiv₂ : GridIndex ≃ GridIndex :=
  Equiv.prodCongr (Equiv.refl ManifoldIndex) succEquiv

/-- The mirror conjugates the successor to the predecessor:
`Θ (i+1) = Θ i − 1`. On the cycle, mirroring reverses the
direction of travel — the arithmetic heart of the weld. -/
theorem involution_succ (i : ManifoldIndex) :
    involution (succ i) = pred (involution i) := by
  apply Fin.ext
  show (21 - (i.val + 1) % 21) % 21 = ((21 - i.val) % 21 + 20) % 21
  have hi := i.isLt
  omega

/-- The mirror conjugates the predecessor to the successor:
`Θ (i−1) = Θ i + 1`. -/
theorem involution_pred (i : ManifoldIndex) :
    involution (pred i) = succ (involution i) := by
  apply Fin.ext
  show (21 - (i.val + 20) % 21) % 21 = ((21 - i.val) % 21 + 1) % 21
  have hi := i.isLt
  omega

/-- The C_21 cycle Laplacian along the first coordinate,
pointwise form: `(L₁ f)(a, b) = 2f(a,b) − f(a+1, b) − f(a−1, b)`. -/
def lap₁ (f : GridIndex → ℝ) : GridIndex → ℝ :=
  fun p => 2 * f p - f (succ p.1, p.2) - f (pred p.1, p.2)

/-- The C_21 cycle Laplacian along the second coordinate,
pointwise form: `(L₂ f)(a, b) = 2f(a,b) − f(a, b+1) − f(a, b−1)`. -/
def lap₂ (f : GridIndex → ℝ) : GridIndex → ℝ :=
  fun p => 2 * f p - f (p.1, succ p.2) - f (p.1, pred p.2)

/-- The joint operator `L₁ + L₂` on grid functions. -/
def lapSum (f : GridIndex → ℝ) : GridIndex → ℝ :=
  lap₁ f + lap₂ f

/-- **O3, weld, first arm / own mirror:** `L₁` commutes with
`Θ̂₁`. Mirroring the coordinate reverses travel along it, and
the Laplacian is symmetric under that reversal. -/
theorem lap₁_thetaHat₁ (f : GridIndex → ℝ) :
    thetaHat₁ (lap₁ f) = lap₁ (thetaHat₁ f) := by
  funext ⟨a, b⟩
  show 2 * f (involution a, b) - f (succ (involution a), b)
        - f (pred (involution a), b)
      = 2 * f (involution a, b) - f (involution (succ a), b)
        - f (involution (pred a), b)
  rw [involution_succ, involution_pred]
  ring

/-- **O3, weld, second arm / own mirror:** `L₂` commutes
with `Θ̂₂`. -/
theorem lap₂_thetaHat₂ (f : GridIndex → ℝ) :
    thetaHat₂ (lap₂ f) = lap₂ (thetaHat₂ f) := by
  funext ⟨a, b⟩
  show 2 * f (a, involution b) - f (a, succ (involution b))
        - f (a, pred (involution b))
      = 2 * f (a, involution b) - f (a, involution (succ b))
        - f (a, involution (pred b))
  rw [involution_succ, involution_pred]
  ring

/-- **O3, cross weld:** `L₂` commutes with the OTHER arm's
mirror `Θ̂₁` — the second coordinate's derivative does not see
the first coordinate's mirror at all. -/
theorem lap₂_thetaHat₁ (f : GridIndex → ℝ) :
    thetaHat₁ (lap₂ f) = lap₂ (thetaHat₁ f) := rfl

/-- **O3, cross weld:** `L₁` commutes with the OTHER arm's
mirror `Θ̂₂`. -/
theorem lap₁_thetaHat₂ (f : GridIndex → ℝ) :
    thetaHat₂ (lap₁ f) = lap₁ (thetaHat₂ f) := rfl

/-- **O3, the arms' derivatives don't leak into each other:**
`L₁` and `L₂` commute as operators, `L₁ (L₂ f) = L₂ (L₁ f)`.
Both sides expand to the same nine-term expression on the
3 × 3 stencil. -/
theorem lap₁_lap₂_comm (f : GridIndex → ℝ) :
    lap₁ (lap₂ f) = lap₂ (lap₁ f) := by
  funext ⟨a, b⟩
  show 2 * (2 * f (a, b) - f (a, succ b) - f (a, pred b))
        - (2 * f (succ a, b) - f (succ a, succ b) - f (succ a, pred b))
        - (2 * f (pred a, b) - f (pred a, succ b) - f (pred a, pred b))
      = 2 * (2 * f (a, b) - f (succ a, b) - f (pred a, b))
        - (2 * f (a, succ b) - f (succ a, succ b) - f (pred a, succ b))
        - (2 * f (a, pred b) - f (succ a, pred b) - f (pred a, pred b))
  ring

/-- **O4 — the joint zero mode exists (cheap direction):**
every constant grid function is a zero mode of `L₁ + L₂`. -/
theorem lapSum_const (c : ℝ) : lapSum (fun _ => c) = 0 := by
  funext ⟨a, b⟩
  show (2 * c - c - c) + (2 * c - c - c) = 0
  ring

/-- Energy identity, first arm:
`∑ f · L₁ f = ∑ (f(a+1, b) − f(a, b))²`. The reindexing step
uses the coordinate successor permutation: the predecessor
cross-term equals the successor cross-term, and the squared
successor term reindexes to the squared self term. -/
theorem lap₁_energy (f : GridIndex → ℝ) :
    ∑ p : GridIndex, f p * (lap₁ f) p
      = ∑ p : GridIndex, (f (succ p.1, p.2) - f p) ^ 2 := by
  have hexp : ∀ p : GridIndex, (lap₁ f) p
      = 2 * f p - f (succ p.1, p.2) - f (pred p.1, p.2) := fun p => rfl
  have hC : (∑ p : GridIndex, (f (succ p.1, p.2)) ^ 2) = ∑ p : GridIndex, (f p) ^ 2 :=
    Equiv.sum_comp succEquiv₁ (fun p : GridIndex => (f p) ^ 2)
  have hA : (∑ p : GridIndex, f p * f (pred p.1, p.2))
      = ∑ p : GridIndex, f (succ p.1, p.2) * f p := by
    rw [← Equiv.sum_comp succEquiv₁
      (fun p : GridIndex => f p * f (pred p.1, p.2))]
    apply Finset.sum_congr rfl
    intro p _
    obtain ⟨a, b⟩ := p
    show f (succ a, b) * f (pred (succ a), b)
        = f (succ a, b) * f (a, b)
    rw [pred_succ]
  have hX : (∑ p : GridIndex, f (succ p.1, p.2) * f p)
      = ∑ p : GridIndex, f p * f (succ p.1, p.2) :=
    Finset.sum_congr rfl (fun p _ => mul_comm _ _)
  have step1 : (∑ p : GridIndex, f p * (lap₁ f) p)
      = ∑ p : GridIndex, (2 * (f p) ^ 2 - f p * f (succ p.1, p.2)
          - f p * f (pred p.1, p.2)) := by
    apply Finset.sum_congr rfl
    intro p _
    rw [hexp p]; ring
  have step2 : (∑ p : GridIndex, (f (succ p.1, p.2) - f p) ^ 2)
      = ∑ p : GridIndex, ((f (succ p.1, p.2)) ^ 2
          - 2 * (f (succ p.1, p.2) * f p) + (f p) ^ 2) := by
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [step1, step2]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hC, hA, hX]
  ring

/-- Energy identity, second arm:
`∑ f · L₂ f = ∑ (f(a, b+1) − f(a, b))²`. -/
theorem lap₂_energy (f : GridIndex → ℝ) :
    ∑ p : GridIndex, f p * (lap₂ f) p
      = ∑ p : GridIndex, (f (p.1, succ p.2) - f p) ^ 2 := by
  have hexp : ∀ p : GridIndex, (lap₂ f) p
      = 2 * f p - f (p.1, succ p.2) - f (p.1, pred p.2) := fun p => rfl
  have hC : (∑ p : GridIndex, (f (p.1, succ p.2)) ^ 2) = ∑ p : GridIndex, (f p) ^ 2 :=
    Equiv.sum_comp succEquiv₂ (fun p : GridIndex => (f p) ^ 2)
  have hA : (∑ p : GridIndex, f p * f (p.1, pred p.2))
      = ∑ p : GridIndex, f (p.1, succ p.2) * f p := by
    rw [← Equiv.sum_comp succEquiv₂
      (fun p : GridIndex => f p * f (p.1, pred p.2))]
    apply Finset.sum_congr rfl
    intro p _
    obtain ⟨a, b⟩ := p
    show f (a, succ b) * f (a, pred (succ b))
        = f (a, succ b) * f (a, b)
    rw [pred_succ]
  have hX : (∑ p : GridIndex, f (p.1, succ p.2) * f p)
      = ∑ p : GridIndex, f p * f (p.1, succ p.2) :=
    Finset.sum_congr rfl (fun p _ => mul_comm _ _)
  have step1 : (∑ p : GridIndex, f p * (lap₂ f) p)
      = ∑ p : GridIndex, (2 * (f p) ^ 2 - f p * f (p.1, succ p.2)
          - f p * f (p.1, pred p.2)) := by
    apply Finset.sum_congr rfl
    intro p _
    rw [hexp p]; ring
  have step2 : (∑ p : GridIndex, (f (p.1, succ p.2) - f p) ^ 2)
      = ∑ p : GridIndex, ((f (p.1, succ p.2)) ^ 2
          - 2 * (f (p.1, succ p.2) * f p) + (f p) ^ 2) := by
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [step1, step2]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hC, hA, hX]
  ring

/-- The grid energy identity for the joint operator:
`∑ f · (L₁ + L₂) f = ∑ (Δ₁ f)² + ∑ (Δ₂ f)²`, the sum of the
squared steps in the two coordinate directions. -/
theorem lapSum_energy (f : GridIndex → ℝ) :
    ∑ p : GridIndex, f p * (lapSum f) p
      = (∑ p : GridIndex, (f (succ p.1, p.2) - f p) ^ 2)
        + ∑ p : GridIndex, (f (p.1, succ p.2) - f p) ^ 2 := by
  have hpoint : ∀ p : GridIndex, f p * (lapSum f) p
      = f p * (lap₁ f) p + f p * (lap₂ f) p := by
    intro p
    show f p * ((lap₁ f) p + (lap₂ f) p)
        = f p * (lap₁ f) p + f p * (lap₂ f) p
    ring
  rw [Finset.sum_congr rfl (fun p _ => hpoint p),
    Finset.sum_add_distrib, lap₁_energy, lap₂_energy]

/-- The `n`-step successor shift on the 21-cycle,
`x ↦ x + n (mod 21)`. Stated as a named function so that
rewrite patterns never have to match raw anonymous-constructor
index terms. -/
def shift (x : ManifoldIndex) (n : ℕ) : ManifoldIndex :=
  ⟨(x.val + n) % 21, Nat.mod_lt _ (by decide)⟩

/-- The zero shift is the identity. -/
theorem shift_zero (x : ManifoldIndex) : shift x 0 = x := by
  apply Fin.ext
  show (x.val + 0) % 21 = x.val
  have hx := x.isLt
  omega

/-- Shifting by `n + 1` is shifting by `n` and then stepping
once: the cycle arithmetic `(x + (n+1)) mod 21 =
((x + n) mod 21 + 1) mod 21`. -/
theorem shift_succ (x : ManifoldIndex) (n : ℕ) :
    shift x (n + 1) = succ (shift x n) := by
  apply Fin.ext
  show (x.val + (n + 1)) % 21 = ((x.val + n) % 21 + 1) % 21
  omega

/-- Shifting a point by the complementary count `21 − x`
returns it to the center: the cycle closes,
`x + (21 − x) ≡ 0 (mod 21)`. -/
theorem shift_full (x : ManifoldIndex) :
    shift x ((21 - x.val) % 21) = TethCenter := by
  apply Fin.ext
  show (x.val + (21 - x.val) % 21) % 21 = 0
  have hx := x.isLt
  omega

/-- Iteration along the first coordinate: if `f` is unchanged
by every first-coordinate successor step, it is unchanged by
the `n`-step successor shift, for every `n`. -/
theorem apply_succ_iterate_fst (f : GridIndex → ℝ)
    (h₁ : ∀ a b, f (succ a, b) = f (a, b)) :
    ∀ (n : ℕ) (x : ManifoldIndex) (b : ManifoldIndex),
      f (shift x n, b) = f (x, b) := by
  intro n
  induction n with
  | zero =>
    intro x b
    rw [shift_zero]
  | succ n ih =>
    intro x b
    rw [shift_succ, h₁]
    exact ih x b

/-- Iteration along the second coordinate. -/
theorem apply_succ_iterate_snd (f : GridIndex → ℝ)
    (h₂ : ∀ a b, f (a, succ b) = f (a, b)) :
    ∀ (n : ℕ) (x : ManifoldIndex) (b : ManifoldIndex),
      f (x, shift b n) = f (x, b) := by
  intro n
  induction n with
  | zero =>
    intro x b
    rw [shift_zero]
  | succ n ih =>
    intro x b
    rw [shift_succ, h₂]
    exact ih x b

/-- Constancy from vanishing steps: a grid function unchanged
by every successor step in both coordinates is constant.
Each coordinate is walked back to the center `0` by the
complementary number of successor steps (the cycle closes:
`a + (21 − a) ≡ 0 (mod 21)`). -/
theorem eq_const_of_succ_eq (f : GridIndex → ℝ)
    (h₁ : ∀ a b, f (succ a, b) = f (a, b))
    (h₂ : ∀ a b, f (a, succ b) = f (a, b)) :
    ∃ c, f = fun _ => c := by
  refine ⟨f (TethCenter, TethCenter), ?_⟩
  funext ⟨a, b⟩
  have step1 : f (TethCenter, b) = f (a, b) := by
    have h := apply_succ_iterate_fst f h₁ ((21 - a.val) % 21) a b
    have h2 : shift a ((21 - a.val) % 21) = TethCenter :=
      shift_full a
    rwa [h2] at h
  have step2 : f (TethCenter, TethCenter) = f (TethCenter, b) := by
    have h := apply_succ_iterate_snd f h₂ ((21 - b.val) % 21)
      TethCenter b
    have h2 : shift b ((21 - b.val) % 21) = TethCenter :=
      shift_full b
    rwa [h2] at h
  show f (a, b) = f (TethCenter, TethCenter)
  rw [← step1, ← step2]

/-- **O4+ — the joint zero mode is unique (T1):** the kernel
of `L₁ + L₂` is exactly the constant functions. If
`(L₁ + L₂) f = 0`, the grid energy identity forces every
successor step of `f` in both coordinates to vanish, and a
function with no steps anywhere on the grid is constant.
(Pre-registered kill K-O4+ armed against the grid energy
identity's seam bookkeeping; it did not fire. The cheap
direction — constants are zero modes — is `lapSum_const`,
pin O4.) -/
theorem lapSum_eq_zero_iff (f : GridIndex → ℝ) :
    lapSum f = 0 ↔ ∃ c, f = fun _ => c := by
  constructor
  · intro h
    have hsum : ∑ p : GridIndex, f p * (lapSum f) p = 0 := by simp [h]
    rw [lapSum_energy] at hsum
    have hnn1 : 0 ≤ ∑ p : GridIndex, (f (succ p.1, p.2) - f p) ^ 2 :=
      Finset.sum_nonneg (fun p _ => sq_nonneg _)
    have hnn2 : 0 ≤ ∑ p : GridIndex, (f (p.1, succ p.2) - f p) ^ 2 :=
      Finset.sum_nonneg (fun p _ => sq_nonneg _)
    obtain ⟨hS1, hS2⟩ :=
      (add_eq_zero_iff_of_nonneg hnn1 hnn2).mp hsum
    have hdiff1 : ∀ a b, f (succ a, b) = f (a, b) := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun p _ => sq_nonneg (f (succ p.1, p.2) - f p))).mp hS1
      intro a b
      have h0 : (f (succ a, b) - f (a, b)) ^ 2 = 0 :=
        hz (a, b) (Finset.mem_univ _)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp h0)
    have hdiff2 : ∀ a b, f (a, succ b) = f (a, b) := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun p _ => sq_nonneg (f (p.1, succ p.2) - f p))).mp hS2
      intro a b
      have h0 : (f (a, succ b) - f (a, b)) ^ 2 = 0 :=
        hz (a, b) (Finset.mem_univ _)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp h0)
    exact eq_const_of_succ_eq f hdiff1 hdiff2
  · rintro ⟨c, rfl⟩
    exact lapSum_const c

end ThetLogos
