import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.NumberTheory.Real.Irrational

open Polynomial

namespace ThetLogos.GenericSeparationCriterionPin

/-!
# ThetLogos.GenericSeparationCriterionPin — the generic arithmetic
separation criterion (lane grade, 2026-11-20)

**Charter: T5, NO CLAIM, dial-ineligible pre-registered, dials 0/4.**
Scope of record:
`your_files/mrb-generic-criterion-pin-scope-2026-11-19.md`, on the
audit `your_files/mrb-arithmetic-separation-criterion-audit-2026-11-19.md`
(verdict HOLD).

## What this pin is

A formalization of the *generic* irrationality criterion behind the
MRB arithmetic separation criterion: if a real number `α` admits
integer polynomials `P` of degree `≤ A * m`, with no rational root
and with `0 < |P(α)| < exp (-c * m ^ 2)`, for arbitrarily large `m`,
then `α` is irrational. The argument is the classical
clearing-denominators one: at a rational `a / b` the value
`b ^ (deg P) * P(a / b)` is a nonzero integer, hence `≥ 1` in
absolute value, contradicting the assumed bound once
`c * m > A * log b`.

The MRB constant `C_MRB` is named in this header as motivation
only. **No statement in this module mentions MRB or any specific
constant** (K-MRB-COSTUME): every statement quantifies over a
generic real `α`. This pin proves nothing about `C_MRB`; its
irrationality remains open, and the hypothesis family of the
criterion is *assumed*, never constructed, for any `α`.

## Strike-check disclosure (Brick 0, recorded in STATUS-MRB.md)

Mathlib carries the multiplicative clearing identity in general
form (`Polynomial.scaleRoots_eval_mul`,
`Polynomial.scaleRoots_eval₂_mul`): `eval (s * r) (scaleRoots p s)
= s ^ natDegree p * eval r p`. It does **not** carry the criterion
itself, nor the `ℤ[X]`/`ℚ` integrality specialization proved in
Brick 1 below, nor the resulting lower bound
`|P(q)| ≥ q.den ^ (-natDegree P)`: the rational root theorem
(`Mathlib.RingTheory.Polynomial.RationalRoot`) concludes
divisibility only under the hypothesis that the value *is* zero,
which is exactly the case this criterion must exclude. The
Liouville files treat rational approximations `|x - m / n|`, a
different hypothesis shape. Brick 1 is therefore the pin's delta:
the specialization plus the bound, proved here directly in sum
form.

## Vacuity assessment (K-MRB-VACUOUS, recorded in STATUS-MRB.md)

The hypothesis family is not vacuous by construction: the degree
bound is an upper bound only and forces nothing to vanish;
`0 < |P(α)|` excludes `P = 0` by itself; "no rational root" is
compatible with super-small values (irreducible quadratics
evaluated near a real root are the standard example, and the
family is satisfiable, e.g. for `α` the square root of a Liouville
number, via `q X ^ 2 - p` at its convergents). The criterion is a
conditional; whether the family exists for any *particular* `α`
is the hard open content, assumed here and constructed nowhere.
-/

/-- **Brick 1 (the delta) — clearing denominators.** For an integer
polynomial `P` and a rational `q`, the scaled value
`q.den ^ (natDegree P) * P(q)` is an integer. This is the integrality
specialization of the clearing identity; Mathlib carries the
identity in general form (`scaleRoots_eval_mul`) but not this
statement. -/
theorem clearing_exists_int (P : ℤ[X]) (q : ℚ) :
    ∃ z : ℤ, (z : ℚ) = (q.den : ℚ) ^ P.natDegree * aeval q P := by
  classical
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1),
    P.coeff i * q.num ^ i * (q.den : ℤ) ^ (P.natDegree - i), ?_⟩
  have hden : (q.den : ℚ) ≠ 0 := by
    have hpos : 0 < q.den := Nat.pos_of_ne_zero q.den_ne_zero
    exact_mod_cast hpos.ne'
  have hsum : ((∑ i ∈ Finset.range (P.natDegree + 1),
        P.coeff i * q.num ^ i * (q.den : ℤ) ^ (P.natDegree - i) : ℤ) : ℚ)
      = ∑ i ∈ Finset.range (P.natDegree + 1),
        (P.coeff i : ℚ) * (q.num : ℚ) ^ i * (q.den : ℚ) ^ (P.natDegree - i) := by
    push_cast
    rfl
  rw [hsum]
  have haeval : aeval q P
      = ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i : ℚ) * q ^ i := by
    rw [aeval_def, eval₂_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp [algebraMap_int_eq]
  rw [haeval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hq : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
  have hpow : (q.den : ℚ) ^ P.natDegree
      = (q.den : ℚ) ^ i * (q.den : ℚ) ^ (P.natDegree - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi']
  have hdeni : (q.den : ℚ) ^ i ≠ 0 := pow_ne_zero i hden
  have hqi : q ^ i = (q.num : ℚ) ^ i / (q.den : ℚ) ^ i := by
    conv_lhs => rw [hq]
    rw [div_pow]
  have hterm : (q.den : ℚ) ^ P.natDegree * ((P.coeff i : ℚ) * q ^ i)
      = (P.coeff i : ℚ) * (q.num : ℚ) ^ i * (q.den : ℚ) ^ (P.natDegree - i) := by
    rw [hqi, hpow]
    field_simp
  exact hterm.symm

/-- **Brick 1 — the cleared value is at least 1 in absolute value**
whenever `P(q) ≠ 0`: a nonzero integer has absolute value `≥ 1`. -/
theorem one_le_abs_clearing (P : ℤ[X]) (q : ℚ) (h : aeval q P ≠ 0) :
    1 ≤ |(q.den : ℚ) ^ P.natDegree * aeval q P| := by
  obtain ⟨z, hz⟩ := clearing_exists_int P q
  have hden : (q.den : ℚ) ^ P.natDegree ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Nat.pos_of_ne_zero q.den_ne_zero).ne')
  have hz0 : z ≠ 0 := by
    intro hzz
    apply h
    have hprod : (q.den : ℚ) ^ P.natDegree * aeval q P = 0 := by
      rw [← hz, hzz]
      simp
    exact (mul_eq_zero.mp hprod).resolve_left hden
  rw [← hz]
  have h1 : (1 : ℤ) ≤ |z| := Int.one_le_abs hz0
  calc (1 : ℚ) = ((1 : ℤ) : ℚ) := by norm_num
    _ ≤ ((|z| : ℤ) : ℚ) := by exact_mod_cast h1
    _ = |(z : ℚ)| := by rw [Int.cast_abs]

/-- **Brick 1 — cast bridge.** Evaluating an integer polynomial at
a rational, in `ℚ` or in `ℝ`, is the same value cast. -/
theorem aeval_rat_cast_real (P : ℤ[X]) (q : ℚ) :
    aeval ((q : ℝ)) P = ((aeval q P : ℚ) : ℝ) := by
  have h1 : aeval ((q : ℝ)) P
      = ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i : ℝ) * (q : ℝ) ^ i := by
    rw [aeval_def, eval₂_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp [algebraMap_int_eq]
  have h2 : aeval q P
      = ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i : ℚ) * q ^ i := by
    rw [aeval_def, eval₂_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp [algebraMap_int_eq]
  rw [h1, h2]
  push_cast
  rfl

/-- **Brick 1 — the bound in the real face**, the exact form the
headline criterion (Brick 2) spends: at a rational point where `P`
does not vanish, `q.den ^ (natDegree P) * |P(q)| ≥ 1` over `ℝ`. -/
theorem one_le_den_pow_mul_abs_aeval_real (P : ℤ[X]) (q : ℚ)
    (h : aeval ((q : ℝ)) P ≠ 0) :
    (1 : ℝ) ≤ (q.den : ℝ) ^ P.natDegree * |aeval ((q : ℝ)) P| := by
  have hq0 : aeval q P ≠ 0 := by
    intro hh
    apply h
    rw [aeval_rat_cast_real, hh]
    simp
  have hle := one_le_abs_clearing P q hq0
  have hcast : ((|(q.den : ℚ) ^ P.natDegree * aeval q P| : ℚ) : ℝ)
      = (q.den : ℝ) ^ P.natDegree * |aeval ((q : ℝ)) P| := by
    have hdenpos : (0 : ℝ) < (q.den : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero q.den_ne_zero
    rw [Rat.cast_abs, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
      aeval_rat_cast_real, abs_mul, abs_of_pos (pow_pos hdenpos _)]
  have h1 : (1 : ℝ) ≤ ((|(q.den : ℚ) ^ P.natDegree * aeval q P| : ℚ) : ℝ) := by
    exact_mod_cast hle
  rwa [hcast] at h1

/-- **Brick 2 — the size contradiction at a rational point.** If
`P` does not vanish at `q`, has degree `≤ A * m`, and satisfies
`|P(q)| < exp (-c * m ^ 2)` with `A * log (q.den) ≤ c * m`, then
Brick 1's lower bound `1 ≤ q.den ^ (deg P) * |P(q)|` collides with
`q.den ^ (A * m) * exp (-c * m ^ 2) ≤ 1`. -/
theorem bound_contradiction {A m : ℕ} {c : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (q : ℚ) (P : ℤ[X]) (hdeg : P.natDegree ≤ A * m)
    (hroot : aeval ((q : ℝ)) P ≠ 0)
    (hsmall : |aeval ((q : ℝ)) P| < Real.exp (-c * (m : ℝ) ^ 2))
    (hmc : (A : ℝ) * Real.log (q.den : ℝ) ≤ c * (m : ℝ)) : False := by
  have hdenpos : (0 : ℝ) < (q.den : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero q.den_ne_zero
  have hden1 : (1 : ℝ) ≤ (q.den : ℝ) := by
    have h1n : 1 ≤ q.den := Nat.pos_of_ne_zero q.den_ne_zero
    exact_mod_cast h1n
  have h1 := one_le_den_pow_mul_abs_aeval_real P q hroot
  have hpow : (q.den : ℝ) ^ P.natDegree ≤ (q.den : ℝ) ^ (A * m) :=
    pow_le_pow_right₀ hden1 hdeg
  have h2 : (1 : ℝ) ≤ (q.den : ℝ) ^ (A * m) * |aeval ((q : ℝ)) P| :=
    le_trans h1 (mul_le_mul_of_nonneg_right hpow (abs_nonneg _))
  have h3 : (q.den : ℝ) ^ (A * m) * |aeval ((q : ℝ)) P|
      < (q.den : ℝ) ^ (A * m) * Real.exp (-c * (m : ℝ) ^ 2) :=
    mul_lt_mul_of_pos_left hsmall (pow_pos hdenpos _)
  have h4 : (q.den : ℝ) ^ (A * m) * Real.exp (-c * (m : ℝ) ^ 2) ≤ 1 := by
    have hden_eq : (q.den : ℝ) ^ (A * m)
        = Real.exp (((A * m : ℕ) : ℝ) * Real.log (q.den : ℝ)) := by
      rw [Real.exp_nat_mul, Real.exp_log hdenpos]
    have hmul : ((A * m : ℕ) : ℝ) * Real.log (q.den : ℝ) ≤ c * (m : ℝ) ^ 2 := by
      have hstep := mul_le_mul_of_nonneg_right hmc (Nat.cast_nonneg m)
      calc ((A * m : ℕ) : ℝ) * Real.log (q.den : ℝ)
          = ((A : ℝ) * Real.log (q.den : ℝ)) * (m : ℝ) := by push_cast; ring
        _ ≤ (c * (m : ℝ)) * (m : ℝ) := hstep
        _ = c * (m : ℝ) ^ 2 := by ring
    rw [hden_eq, ← Real.exp_add, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    linarith [hmul]
  exact (not_lt_of_ge h4) (h2.trans_lt h3)

/-- **Brick 2 — the headline criterion.** Let `α` be a real number
and `A : ℕ`, `c : ℝ` with `0 < c`. Suppose that for every bound `M`
there exist `m ≥ M` and an integer polynomial `P` with
`natDegree P ≤ A * m`, with no rational root, and with
`0 < |P(α)| < exp (-c * m ^ 2)`. Then `α` is irrational.

This is the generic criterion of the scope: it uses no property of
any specific constant. The hypothesis family is assumed, not
constructed; in particular nothing here is asserted about the MRB
constant, whose name appears in this module's header as motivation
only (K-MRB-COSTUME). -/
theorem irrational_of_superapprox {α : ℝ} {A : ℕ} {c : ℝ} (hc : 0 < c)
    (h : ∀ M : ℕ, ∃ m : ℕ, ∃ P : ℤ[X], M ≤ m ∧ P.natDegree ≤ A * m
      ∧ (∀ q : ℚ, aeval ((q : ℝ)) P ≠ 0)
      ∧ 0 < |aeval α P| ∧ |aeval α P| < Real.exp (-c * (m : ℝ) ^ 2)) :
    Irrational α := by
  intro hα
  obtain ⟨q, hq⟩ := hα
  obtain ⟨N, hN⟩ := exists_nat_gt ((A : ℝ) * Real.log (q.den : ℝ) / c)
  obtain ⟨m, P, hmM, hdeg, hroot, _hpos, hsmall⟩ := h (N + 1)
  subst hq
  have hm1 : 1 ≤ m := le_trans (Nat.le_add_left 1 N) hmM
  have hmA : (A : ℝ) * Real.log (q.den : ℝ) ≤ c * (m : ℝ) := by
    have hmR : ((N + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmM
    have hN' : (A : ℝ) * Real.log (q.den : ℝ) < c * ((N + 1 : ℕ) : ℝ) := by
      rw [div_lt_iff₀ hc] at hN
      have hNcast : ((N : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_succ N
      nlinarith [hN, hc, hNcast]
    exact le_trans hN'.le (mul_le_mul_of_nonneg_left hmR hc.le)
  exact bound_contradiction hc hm1 q P hdeg (hroot q) hsmall hmA

/-- **Brick 3 — the irreducible wrapper, rational face.** An
irreducible polynomial over `ℚ` of degree `≥ 2` has no rational
root: a root `q` would exhibit the degree-1 factor `X - C q`, and
irreducibility forces that factor or its cofactor to be a unit,
both impossible at these degrees. This is hypothesis (1) of the
original criterion, discharged against the operative
no-rational-root hypothesis the proof actually spends. -/
theorem no_rat_root_of_irreducible (P : ℚ[X]) (hirr : Irreducible P)
    (hdeg : 2 ≤ P.natDegree) (q : ℚ) : ¬ P.IsRoot q := by
  intro hroot
  obtain ⟨Q, hQ⟩ := dvd_iff_isRoot.mpr hroot
  rcases hirr.isUnit_or_isUnit hQ with hu | hu
  · -- The factor `X - C q` would be a unit, but its degree is 1.
    have hdeg1 : (X - C q).degree = 0 := isUnit_iff_degree_eq_zero.mp hu
    simp [degree_X_sub_C] at hdeg1
  · -- The cofactor `Q` would be a unit, forcing `natDegree P = 1`.
    have hdegQ : Q.degree = 0 := isUnit_iff_degree_eq_zero.mp hu
    have hdegP : P.degree = 1 := by
      rw [hQ, degree_mul, degree_X_sub_C, hdegQ, add_zero]
    have hnat : P.natDegree = 1 := natDegree_eq_of_degree_eq_some hdegP
    omega

/-- **Brick 3 — the irreducible wrapper, the criterion's face.**
If the image of `P : ℤ[X]` in `ℚ[X]` is irreducible of degree
`≥ 2`, then `P` has no rational root in exactly the sense Brick 2
spends: its real evaluation at every rational point is nonzero. -/
theorem no_rat_root_real_of_irreducible_map (P : ℤ[X])
    (hirr : Irreducible (P.map (Int.castRingHom ℚ)))
    (hdeg : 2 ≤ (P.map (Int.castRingHom ℚ)).natDegree) (q : ℚ) :
    aeval ((q : ℝ)) P ≠ 0 := by
  intro h0
  have hq0 : aeval q P = 0 := by
    rw [aeval_rat_cast_real] at h0
    exact_mod_cast h0
  have hroot : (P.map (Int.castRingHom ℚ)).IsRoot q := by
    have h1 : (P.map (Int.castRingHom ℚ)).eval q = aeval q P := by
      rw [eval_map, aeval_def, algebraMap_int_eq]
    rw [IsRoot.def, h1]
    exact hq0
  exact no_rat_root_of_irreducible _ hirr hdeg q hroot

end ThetLogos.GenericSeparationCriterionPin
