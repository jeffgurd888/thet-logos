import Mathlib.Tactic

namespace ThetLogos

/-!
# Diffusion defect: `z² = X² + y² + t` for a finite random walk (T1, finite level)

Origin (Jeff, 2026-10-18): his notation `X² + t + y² + t = z² + t`,
whose net form (one `t` cancels) is `z² = X² + y² + t` — time as the
Pythagorean defect: exactly how much the squared diagonal overshoots
the flat right-triangle closure `X² + y²`. The gauntlet's price for
taking it seriously was: a coefficient for `t`, and an independent
clock. This module pays both, in the smallest honest model.

The model is the simple symmetric random walk on `ℤ²`: at each of
`n` steps the walker moves one unit in one of the four coordinate
directions. Summing the squared distance from the start over all
`4^n` paths (uniform counting measure), the cross terms cancel
exactly (Lemma A/B) and the second moment is exactly `4^n · n`
(Lemma C). Hence the headline theorem: for every start `(x, y)`,

`∑_{p} ‖(x, y) + disp p‖² = 4^n · (x² + y² + n)`,

and in expectation over the uniform path measure,

`E ‖(x, y) + disp p‖² = x² + y² + n`.

This is Jeff's equation with `t := n`: the step count is the
independent clock, and `z²` is read as the expected squared distance.

FENCES, stated plainly:

* This is a finite combinatorial model. `t` is a step count, not
  clock time; it becomes clock time only when a physical clock and
  a physical diffusivity are supplied from outside the model.
* The coefficient `1` in front of `t` is the walk's normalization —
  unit steps, four directions equally likely. It is the diffusivity
  of *this* model: chosen, not derived.
* The `+` sign on `t` is this model's Euclidean signature: chosen,
  not derived. In this house, signature is input data
  (cf. `EdgeSignature.signature_not_determined`).
* The theorem is about the expected squared displacement of this
  walk. No continuum limit is taken or claimed; there is no
  spacetime claim and no Navier–Stokes claim.
-/

/-- The four unit steps of the walk on `ℤ²`, indexed by `Fin 4`:
east, west, north, south. -/
def stepVec (s : Fin 4) : ℤ × ℤ :=
  match s.1 with
  | 0 => (1, 0)
  | 1 => (-1, 0)
  | 2 => (0, 1)
  | _ => (0, -1)

/-- Squared Euclidean norm of a lattice vector, in `ℤ`. -/
def normSq (v : ℤ × ℤ) : ℤ := v.1 ^ 2 + v.2 ^ 2

/-- Displacement of a path: the sum of its step vectors. A path of
length `n` is a function `p : Fin n → Fin 4` choosing a step at each
time. -/
def disp {n : ℕ} (p : Fin n → Fin 4) : ℤ × ℤ := ∑ i, stepVec (p i)

/-- Expansion of the squared norm of a sum: the Pythagorean part plus
twice the inner product plus the second squared norm. -/
theorem normSq_add (u v : ℤ × ℤ) :
    normSq (u + v) = normSq u + 2 * (u.1 * v.1 + u.2 * v.2) + normSq v := by
  obtain ⟨a, b⟩ := u
  obtain ⟨c, d⟩ := v
  show (a + c) ^ 2 + (b + d) ^ 2 = (a ^ 2 + b ^ 2) + 2 * (a * c + b * d) + (c ^ 2 + d ^ 2)
  ring

/-- Every step has squared length `1`. -/
theorem normSq_stepVec (s : Fin 4) : normSq (stepVec s) = 1 := by
  fin_cases s <;> decide

/-- **Lemma A, mean part.** The four step vectors cancel exactly. -/
theorem sum_stepVec : ∑ s : Fin 4, stepVec s = 0 := by
  rw [Fin.sum_univ_four]
  decide

/-- **Lemma A, energy part.** Each step has squared length `1`, so the
four steps carry total squared length `4`. -/
theorem sum_normSq_stepVec : ∑ s : Fin 4, normSq (stepVec s) = 4 := by
  rw [Fin.sum_univ_four]
  decide

/-- The first components of the step vectors cancel. -/
theorem sum_stepVec_fst : ∑ s : Fin 4, (stepVec s).1 = 0 := by
  rw [← Prod.fst_sum, sum_stepVec]
  rfl

/-- The second components of the step vectors cancel. -/
theorem sum_stepVec_snd : ∑ s : Fin 4, (stepVec s).2 = 0 := by
  rw [← Prod.snd_sum, sum_stepVec]
  rfl

/-- The displacement of a path splits into its first step plus the
displacement of its tail. -/
theorem disp_cons {n : ℕ} (s : Fin 4) (q : Fin n → Fin 4) :
    disp (Fin.cons s q) = stepVec s + disp q := by
  unfold disp
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- Summing over all paths of length `n + 1` splits into a sum over
the first step and a sum over all tails of length `n`. -/
theorem sum_paths_succ {M : Type*} [AddCommMonoid M] {n : ℕ}
    (F : (Fin (n + 1) → Fin 4) → M) :
    (∑ p, F p) = ∑ s : Fin 4, ∑ q : Fin n → Fin 4, F (Fin.cons s q) := by
  have hbij : Function.Bijective
      (fun x : Fin 4 × (Fin n → Fin 4) => (Fin.cons x.1 x.2 : Fin (n + 1) → Fin 4)) := by
    apply Function.bijective_iff_has_inverse.mpr
    refine ⟨fun p => (p 0, fun i => p (Fin.succ i)), ?_, ?_⟩
    · intro ⟨s, q⟩
      simp only [Fin.cons_zero, Fin.cons_succ]
    · intro p
      show Fin.cons (p 0) (Fin.tail p) = p
      exact Fin.cons_self_tail p
  have hprod : (∑ x : Fin 4 × (Fin n → Fin 4), F (Fin.cons x.1 x.2))
      = ∑ s : Fin 4, ∑ q : Fin n → Fin 4, F (Fin.cons s q) :=
    Fintype.sum_prod_type _
  rw [← hprod]
  exact (Fintype.sum_bijective _ hbij (fun x => F (Fin.cons x.1 x.2)) F
    fun _ => rfl).symm

/-- **Lemma B (mean).** Summed over all paths of any length, the total
displacement is zero: the walk has no drift. The recurrence is
`D (n+1) = 4 • D n`: the first step averages out by Lemma A and each
tail contributes the previous total once per choice of first step. -/
theorem sum_disp (n : ℕ) : ∑ p : Fin n → Fin 4, disp p = 0 := by
  induction n with
  | zero =>
      apply Finset.sum_eq_zero
      intro p _
      simp [disp]
  | succ n ih =>
      have hcard : Fintype.card (Fin n → Fin 4) = 4 ^ n := by simp
      have h1 : ∀ s : Fin 4, (∑ q : Fin n → Fin 4, stepVec s)
          = (4 ^ n : ℕ) • stepVec s := by
        intro s
        rw [Finset.sum_const, Finset.card_univ, hcard]
      rw [sum_paths_succ]
      simp_rw [disp_cons, Finset.sum_add_distrib, h1, ih]
      rw [← Finset.smul_sum, sum_stepVec, smul_zero, Finset.sum_const_zero,
        add_zero]

/-- **Lemma C (second moment).** Summed over all paths of length `n`,
the squared displacement totals `4^n · n`. The recurrence is
`Q (n+1) = 4 · Q n + 4^(n+1)`: tails contribute the previous total
once per first step, each first step contributes its unit squared
length once per tail, and the cross terms vanish by Lemma A. -/
theorem sum_normSq_disp (n : ℕ) :
    ∑ p : Fin n → Fin 4, normSq (disp p) = (4 : ℤ) ^ n * (n : ℤ) := by
  induction n with
  | zero =>
      simp only [Nat.cast_zero, mul_zero]
      apply Finset.sum_eq_zero
      intro p _
      have hd : disp p = 0 := by simp [disp]
      rw [hd]
      rfl
  | succ n ih =>
      have hcard : Fintype.card (Fin n → Fin 4) = 4 ^ n := by simp
      have hA : ∑ s : Fin 4, ∑ q : Fin n → Fin 4, normSq (stepVec s)
          = (4 : ℤ) ^ (n + 1) := by
        simp_rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul,
          ← Finset.mul_sum, sum_normSq_stepVec]
        push_cast
        exact (pow_succ (4 : ℤ) n).symm
      have hB : ∑ s : Fin 4, ∑ q : Fin n → Fin 4,
          (2 : ℤ) * ((stepVec s).1 * (disp q).1 + (stepVec s).2 * (disp q).2)
          = 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_eq_zero
        intro q _
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul,
          ← Finset.sum_mul, sum_stepVec_fst, sum_stepVec_snd]
        simp
      have hC : ∑ s : Fin 4, ∑ q : Fin n → Fin 4, normSq (disp q)
          = 4 * ((4 : ℤ) ^ n * (n : ℤ)) := by
        simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ih,
          nsmul_eq_mul]
        norm_num
      rw [sum_paths_succ]
      simp_rw [disp_cons, normSq_add, Finset.sum_add_distrib]
      rw [hA, hB, hC]
      simp only [pow_succ, Nat.cast_succ]
      ring

/-- **Headline theorem.** For every start `(x, y)` and every length
`n`, the squared distance from the start, summed over all `4^n`
paths, is `4^n · (x² + y² + n)`: the start's own squared distance,
plus exactly one unit per step. This is Jeff's
`z² = X² + y² + t` with `t := n`, in counting form — the cross terms
vanish by Lemma B and the accumulated second moment is Lemma C. -/
theorem sum_normSq_add_disp (x y : ℤ) (n : ℕ) :
    ∑ p : Fin n → Fin 4, normSq ((x, y) + disp p)
      = (4 : ℤ) ^ n * (x ^ 2 + y ^ 2 + (n : ℤ)) := by
  have hexp : ∀ p : Fin n → Fin 4, normSq ((x, y) + disp p)
      = normSq (x, y) + 2 * (x * (disp p).1 + y * (disp p).2)
        + normSq (disp p) := by
    intro p
    exact normSq_add (x, y) (disp p)
  have hnorm : normSq (x, y) = x ^ 2 + y ^ 2 := rfl
  have h1 : ∑ p : Fin n → Fin 4, normSq (x, y)
      = (4 : ℤ) ^ n * normSq (x, y) := by
    have hcard : Fintype.card (Fin n → Fin 4) = 4 ^ n := by simp
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat]
  have h2 : ∑ p : Fin n → Fin 4,
      (2 : ℤ) * (x * (disp p).1 + y * (disp p).2) = 0 := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Prod.fst_sum, ← Prod.snd_sum, sum_disp]
    simp
  simp_rw [hexp, Finset.sum_add_distrib]
  rw [h1, h2, sum_normSq_disp, hnorm]
  ring

/-- **Expectation form.** Dividing by the number of paths: under the
uniform measure on paths of length `n`, the expected squared
distance from the start `(x, y)` is exactly `x² + y² + n`. This is
Jeff's equation `z² = X² + y² + t` with `t := n` the step count (the
independent clock) and `z²` read as the expected squared distance. -/
theorem expected_normSq (x y : ℤ) (n : ℕ) :
    ((4 : ℚ) ^ n)⁻¹ * ∑ p : Fin n → Fin 4, (normSq ((x, y) + disp p) : ℚ)
      = (x : ℚ) ^ 2 + (y : ℚ) ^ 2 + (n : ℚ) := by
  have h4 : (4 : ℚ) ^ n ≠ 0 := by positivity
  rw [← Int.cast_sum, sum_normSq_add_disp]
  push_cast
  exact inv_mul_cancel_left₀ h4 _

end ThetLogos
