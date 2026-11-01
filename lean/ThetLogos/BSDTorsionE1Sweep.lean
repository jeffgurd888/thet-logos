import ThetLogos.BSDRefinedAssembly
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.GroupTheory.Torsion
import Mathlib.Tactic

namespace ThetLogos

/-!
# ThetLogos.BSDTorsionE1Sweep — the E1 torsion sweep, modulo the shared seam

Source: BSD rung 3, brick **BSD3-1** (module 1), mirroring B2-1's E2
discharge in `ThetLogos.BSDRefinedPin`. B2-6 stated the E1 sibling's
torsion seam `E1TorsionCardSeam` (`#E1(ℚ)_tors = 4`) and proved
nothing about it. This module discharges it *conditional on* the one
shared Nagell–Lutz seam, instantiated for E1 in exactly the E2 seam's
form (`NagellLutzCriterionE1` below): sanctioned strength only, no
stronger form adopted anywhere (the inherited kill **K-BSD3-1b** —
if a stronger form were needed, this brick would stop and report;
it was not needed, and the kill does not fire).

**The sweep finds points here** (unlike E2, where it excluded all):
the criterion gives integer coordinates on `y² = x³ − x` with
`y = 0` or `y² ∣ 64` (here `64 = Δ(E1)`). The `y = 0` case factors
`x³ − x = x(x−1)(x+1)`, giving `x ∈ {0, 1, −1}` — the three affine
2-torsion points `(0,0)`, `(1,0)`, `(−1,0)`. The `y² ∣ 64`,
`y ≠ 0` case closes by enumeration: positivity forces
`0 ≤ x ≤ 4` (for `x ≤ −1`, `x³ − x ≤ 0 < y²`; for `x ≥ 5`,
`x³ − x ≥ 120 > 64 ≥ y²`), and the finitely many remaining
`(x, y)` pairs are checked by integer arithmetic — none satisfies
the curve equation. Each affine point found has `y = 0`, hence is
its own negative, hence has order dividing `2`; together with `O`
the torsion subgroup is exactly `{O, (0,0), (1,0), (−1,0)}`,
`ℤ/2 × ℤ/2`, of cardinality `4`. The enumeration is closed, not
sampled: every case is discharged in-tree.

**Charter fence, on the face.** BSD is a NO CLAIM board. This
module is a conditional discharge of a statement-grade seam for one
regression curve; it closes **0** parts of the Clay BSD statement.
The Nagell–Lutz criterion itself is not in Mathlib and is not
proved here; it is carried as the labeled hypothesis
`NagellLutzCriterionE1`, exactly as B2-1 carried
`NagellLutzCriterionE2`.

Honesty tiers in this file:
- **T1 (proved):** `E1.Δ = 64`, the candidate enumeration, the
  order-2 facts, the classification of torsion points, and the
  cardinality theorem — the last three conditional on the seam.
- **T5 (statement, unproved by design):** `NagellLutzCriterionE1`.

Status: NO CLAIM on BSD. Parts of the official statement closed: 0.
-/

/-! ## The discriminant and the elliptic instance -/

/-- The discriminant of `y² = x³ − x` is `64`. -/
theorem E1_delta : E1.Δ = 64 := by
  norm_num [E1, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : E1.IsElliptic :=
  ⟨by rw [E1_delta]; exact isUnit_iff_ne_zero.mpr (by norm_num)⟩

/-! ## The shared seam, instantiated for E1 -/

/-- **The Nagell–Lutz seam for E1** (`nagellLutz_seam`, E1
instance), in the sanctioned strength only — the *same form* as
B2-1's `NagellLutzCriterionE2`: every torsion point of `E1(ℚ)` in
affine coordinates has *integer* affine coordinates whose
`y`-coordinate satisfies `y = 0` or `y² ∣ 64` (here `64 = Δ(E1)`;
the E2 form carries `1728 = |Δ(E2)|`). A point is torsion if some
nonzero integer multiple of it is `0`. The converse direction is
*not* asserted, and no stronger form is sanctioned by this brick
(K-BSD3-1b: the stronger form would be a new named seam for the
parent's ruling, never adopted silently — it is not needed here).
The Nagell–Lutz criterion itself is not in Mathlib and is not
proved here; it is carried as this one labeled hypothesis. -/
def NagellLutzCriterionE1 : Prop :=
  ∀ (x y : ℚ) (h : E1.toAffine.Nonsingular x y),
    (∃ n : ℤ, n ≠ 0 ∧
      n • (WeierstrassCurve.Affine.Point.some x y h :
        E1.toAffine.Point) = 0) →
    ∃ (xi yi : ℤ), x = (xi : ℚ) ∧ y = (yi : ℚ) ∧
      (yi = 0 ∨ yi ^ 2 ∣ 64)

/-! ## The candidate enumeration over `ℤ` -/

/-- The candidate enumeration: an integer whose square divides
`64` is one of `0, ±1, ±2, ±4, ±8`. From `y ^ 2 ∣ 64` one gets
`y ^ 2 ≤ 64`, hence `-8 ≤ y ≤ 8`; the finitely many remaining
cases are checked by integer arithmetic (the true divisors
survive, the rest contradict the divisibility hypothesis). -/
theorem eq_of_sq_dvd_64 (y : ℤ) (h : y ^ 2 ∣ 64) :
    y = 0 ∨ y = 1 ∨ y = -1 ∨ y = 2 ∨ y = -2 ∨ y = 4 ∨ y = -4 ∨
    y = 8 ∨ y = -8 := by
  have hle : y ^ 2 ≤ 64 := Int.le_of_dvd (by norm_num) h
  have hhi : y ≤ 8 := by
    by_contra hcon
    have h9 : (9 : ℤ) ≤ y := by omega
    have hsq : (81 : ℤ) ≤ y ^ 2 := by
      calc (81 : ℤ) = 9 ^ 2 := by norm_num
        _ ≤ y ^ 2 := pow_le_pow_left₀ (by norm_num) h9 2
    omega
  have hlo : -8 ≤ y := by
    by_contra hcon
    have h9 : (9 : ℤ) ≤ -y := by omega
    have hsq : (81 : ℤ) ≤ y ^ 2 := by
      calc (81 : ℤ) = 9 ^ 2 := by norm_num
        _ ≤ (-y) ^ 2 := pow_le_pow_left₀ (by norm_num) h9 2
        _ = y ^ 2 := by ring
    omega
  interval_cases y <;> norm_num at h <;> norm_num

/-- **The sweep's arithmetic core, closed.** An integer point of
`y² = x³ − x` whose ordinate is `0` or squares-dividing `64` is
one of `(0, 0)`, `(1, 0)`, `(−1, 0)`. The `y = 0` case factors
`x³ − x = x(x−1)(x+1)`. In the `y ≠ 0` case, `1 ≤ y² ≤ 64` and
the equation force `0 ≤ x ≤ 4` (for `x ≤ −1` the right side is
`x(x²−1) ≤ 0`; for `x ≥ 5` it is at least `5 · 24 = 120 > 64`),
and the remaining finitely many `(x, y)` pairs — `x ∈ {0,…,4}`,
`−8 ≤ y ≤ 8` — are checked one by one: none satisfies the
equation with `y ≠ 0`. The enumeration closes; it is not a
sample. -/
theorem e1_int_point_cases {xi yi : ℤ} (heq : yi ^ 2 = xi ^ 3 - xi)
    (hy : yi = 0 ∨ yi ^ 2 ∣ 64) :
    (xi = 0 ∧ yi = 0) ∨ (xi = 1 ∧ yi = 0) ∨ (xi = -1 ∧ yi = 0) := by
  have hzero : yi = 0 → (xi = 0 ∧ yi = 0) ∨ (xi = 1 ∧ yi = 0) ∨
      (xi = -1 ∧ yi = 0) := by
    intro h0
    subst h0
    have h3 : xi ^ 3 = xi := by
      have htmp := heq
      norm_num at htmp
      linarith
    have hf : xi * (xi - 1) * (xi + 1) = 0 := by
      have hring : xi * (xi - 1) * (xi + 1) = xi ^ 3 - xi := by ring
      rw [hring]; linarith
    rcases mul_eq_zero.mp hf with h | h
    · rcases mul_eq_zero.mp h with h1 | h1
      · exact Or.inl ⟨h1, rfl⟩
      · exact Or.inr (Or.inl ⟨by omega, rfl⟩)
    · exact Or.inr (Or.inr ⟨by omega, rfl⟩)
  rcases hy with h0 | hdvd
  · exact hzero h0
  · by_cases hy0 : yi = 0
    · exact hzero hy0
    · exfalso
      have hle : yi ^ 2 ≤ 64 := Int.le_of_dvd (by norm_num) hdvd
      have hpos : 0 < yi ^ 2 := sq_pos_of_ne_zero hy0
      have hfact : xi ^ 3 - xi = xi * (xi ^ 2 - 1) := by ring
      have hxi0 : 0 ≤ xi := by
        by_contra hcon
        have hle1 : xi ≤ -1 := by omega
        have hsq1 : (1 : ℤ) ≤ xi ^ 2 := by nlinarith [sq_nonneg (xi + 1)]
        have hnp : xi * (xi ^ 2 - 1) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by omega) (by linarith)
        omega
      have hxi4 : xi ≤ 4 := by
        by_contra hcon
        have hge5 : (5 : ℤ) ≤ xi := by omega
        have hsq25 : (25 : ℤ) ≤ xi ^ 2 := by
          calc (25 : ℤ) = 5 ^ 2 := by norm_num
            _ ≤ xi ^ 2 := pow_le_pow_left₀ (by norm_num) hge5 2
        have hbig : (120 : ℤ) ≤ xi * (xi ^ 2 - 1) := by
          calc (120 : ℤ) = 5 * 24 := by norm_num
            _ ≤ xi * (xi ^ 2 - 1) :=
              mul_le_mul hge5 (by linarith) (by norm_num) (by omega)
        omega
      have hyhi : yi ≤ 8 := by
        by_contra hcon
        have h9 : (9 : ℤ) ≤ yi := by omega
        have hsq : (81 : ℤ) ≤ yi ^ 2 := by
          calc (81 : ℤ) = 9 ^ 2 := by norm_num
            _ ≤ yi ^ 2 := pow_le_pow_left₀ (by norm_num) h9 2
        omega
      have hylo : -8 ≤ yi := by
        by_contra hcon
        have h9 : (9 : ℤ) ≤ -yi := by omega
        have hsq : (81 : ℤ) ≤ yi ^ 2 := by
          calc (81 : ℤ) = 9 ^ 2 := by norm_num
            _ ≤ (-yi) ^ 2 := pow_le_pow_left₀ (by norm_num) h9 2
            _ = yi ^ 2 := by ring
        omega
      interval_cases xi <;> interval_cases yi <;> norm_num at heq <;>
        norm_num at hy0

/-! ## The three affine 2-torsion points -/

/-- The point `(0, 0)` on `E1`. -/
def E1P00 : E1.toAffine.Point :=
  WeierstrassCurve.Affine.Point.some 0 0 (by
    apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]; norm_num [E1])

/-- The point `(1, 0)` on `E1`. -/
def E1P10 : E1.toAffine.Point :=
  WeierstrassCurve.Affine.Point.some 1 0 (by
    apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]; norm_num [E1])

/-- The point `(−1, 0)` on `E1`. -/
def E1Pm10 : E1.toAffine.Point :=
  WeierstrassCurve.Affine.Point.some (-1) 0 (by
    apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]; norm_num [E1])

/-- A point of `E1` with `y = 0` is its own negative: the negation
formula sends `y` to `−y − a₁x − a₃`, and for `E1` both `a₁` and
`a₃` vanish. -/
theorem E1_neg_some_zero (x : ℚ) (h : E1.toAffine.Nonsingular x 0) :
    -WeierstrassCurve.Affine.Point.some x 0 h =
      WeierstrassCurve.Affine.Point.some x 0 h := by
  rw [WeierstrassCurve.Affine.Point.neg_some]
  congr 1
  simp [WeierstrassCurve.Affine.negY, E1]

/-- A point of `E1` with `y = 0` has order dividing `2`: it is
its own negative, so `2 • P = P + (−P) = 0`. -/
theorem E1_two_nsmul_some_zero (x : ℚ)
    (h : E1.toAffine.Nonsingular x 0) :
    (2 : ℕ) • WeierstrassCurve.Affine.Point.some x 0 h = 0 := by
  have hneg : -WeierstrassCurve.Affine.Point.some x 0 h =
      WeierstrassCurve.Affine.Point.some x 0 h := E1_neg_some_zero x h
  calc (2 : ℕ) • WeierstrassCurve.Affine.Point.some x 0 h
      = WeierstrassCurve.Affine.Point.some x 0 h +
        WeierstrassCurve.Affine.Point.some x 0 h := two_nsmul _
    _ = WeierstrassCurve.Affine.Point.some x 0 h +
        -WeierstrassCurve.Affine.Point.some x 0 h := by rw [hneg]
    _ = 0 := add_neg_cancel _

/-- Every affine `y = 0` point of `E1` — in particular each of
`(0,0)`, `(1,0)`, `(−1,0)` — lies in the torsion subgroup. -/
theorem E1_some_zero_mem_torsion (x : ℚ)
    (h : E1.toAffine.Nonsingular x 0) :
    WeierstrassCurve.Affine.Point.some x 0 h ∈
      AddCommGroup.torsion E1.toAffine.Point :=
  (AddCommGroup.mem_torsion _).mpr
    (isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      ⟨2, by norm_num, E1_two_nsmul_some_zero x h⟩)

/-! ## The classification and the card -/

/-- **The sweep's conclusion at the level of points**, conditional
on the shared seam: under `NagellLutzCriterionE1` (sanctioned
strength only), every torsion point of `E1(ℚ)` — torsion in the
criterion's own form, `∃ n : ℤ, n ≠ 0 ∧ n • P = 0` — is one of
`O`, `(0,0)`, `(1,0)`, `(−1,0)`. The affine case is decided by
`e1_int_point_cases`: the criterion gives integer coordinates on
`y² = x³ − x` with `yi = 0` or `yi² ∣ 64`, and the closed
enumeration leaves exactly the three affine points. -/
theorem E1_point_eq_of_torsion (hNL : NagellLutzCriterionE1)
    (P : E1.toAffine.Point) (htors : ∃ n : ℤ, n ≠ 0 ∧ n • P = 0) :
    P = 0 ∨ P = E1P00 ∨ P = E1P10 ∨ P = E1Pm10 := by
  cases P with
  | zero => exact Or.inl rfl
  | some x y h =>
    obtain ⟨xi, yi, hx, hy, hy0⟩ := hNL x y h htors
    have heq : y ^ 2 = x ^ 3 - x := by
      have heq0 := h.1
      rw [WeierstrassCurve.Affine.equation_iff] at heq0
      simp only [E1] at heq0
      linarith [heq0]
    rw [hx, hy] at heq
    have hZ : yi ^ 2 = xi ^ 3 - xi := by exact_mod_cast heq
    subst hx
    subst hy
    rcases e1_int_point_cases hZ hy0 with ⟨hxi, hyi⟩ | ⟨hxi, hyi⟩ |
      ⟨hxi, hyi⟩
    · subst hxi; subst hyi
      exact Or.inr (Or.inl (by simp [E1P00]))
    · subst hxi; subst hyi
      exact Or.inr (Or.inr (Or.inl (by simp [E1P10])))
    · subst hxi; subst hyi
      exact Or.inr (Or.inr (Or.inr (by simp [E1Pm10])))

/-- The torsion membership characterization, conditional on the
shared seam: `P ∈ E1(ℚ)_tors` iff `P` is one of `O`, `(0,0)`,
`(1,0)`, `(−1,0)`. The forward direction is the sweep
(`E1_point_eq_of_torsion`, with Mathlib's natural-multiple form
of finite order converted to the criterion's integer-multiple
form, as in B2-1); the backward direction is the order-2 fact
`E1_some_zero_mem_torsion` at the three affine points, and
`0 ∈ tors` since the torsion subgroup is a subgroup. -/
theorem e1_mem_torsion_iff (hNL : NagellLutzCriterionE1)
    (P : E1.toAffine.Point) :
    P ∈ AddCommGroup.torsion E1.toAffine.Point ↔
      P = 0 ∨ P = E1P00 ∨ P = E1P10 ∨ P = E1Pm10 := by
  constructor
  · intro hP
    rw [AddCommGroup.mem_torsion, isOfFinAddOrder_iff_nsmul_eq_zero] at hP
    obtain ⟨n, hn, hns⟩ := hP
    apply E1_point_eq_of_torsion hNL P
    refine ⟨(n : ℤ), by exact_mod_cast hn.ne', ?_⟩
    simpa using hns
  · rintro (rfl | rfl | rfl | rfl)
    · exact AddSubgroup.zero_mem _
    · exact E1_some_zero_mem_torsion 0 _
    · exact E1_some_zero_mem_torsion 1 _
    · exact E1_some_zero_mem_torsion (-1) _

/-- **BSD3-1's module-1 headline: B2-6's `E1TorsionCardSeam`,
discharged conditional on the one shared seam**
`NagellLutzCriterionE1`, in the sanctioned strength only
(K-BSD3-1b does not fire). The torsion subgroup of `E1(ℚ)` is
exactly `{O, (0,0), (1,0), (−1,0)}` — `ℤ/2 × ℤ/2`, the three
affine points having distinct `x`-coordinates, so the displayed
four-element finset has card `4` — hence `#tors = 4`. This is
the `#tors = 4` the E1 sibling pin consumes; it is conditional
on the seam, and it closes zero parts of the official BSD
statement. -/
theorem e1TorsionCard_of_nagellLutz (hNL : NagellLutzCriterionE1) :
    E1TorsionCardSeam := by
  have hiff : ∀ P : E1.toAffine.Point,
      P ∈ AddCommGroup.torsion E1.toAffine.Point ↔
        P ∈ ({0, E1P00, E1P10, E1Pm10} : Finset E1.toAffine.Point) := by
    intro P
    constructor
    · intro hP
      rcases (e1_mem_torsion_iff hNL P).mp hP with rfl | rfl | rfl |
        rfl <;> simp
    · intro hP
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_singleton] at hP
      exact (e1_mem_torsion_iff hNL P).mpr hP
  have hpropeq : (fun P : E1.toAffine.Point =>
        P ∈ AddCommGroup.torsion E1.toAffine.Point) =
      (fun P : E1.toAffine.Point =>
        P ∈ ({0, E1P00, E1P10, E1Pm10} : Finset E1.toAffine.Point)) :=
    funext fun P => propext (hiff P)
  have hcardS : ({0, E1P00, E1P10, E1Pm10} :
      Finset E1.toAffine.Point).card = 4 := by
    have d0a : (0 : E1.toAffine.Point) ≠ E1P00 :=
      fun h => (WeierstrassCurve.Affine.Point.some_ne_zero
        (W' := E1.toAffine) (x := 0) (y := 0) _) h.symm
    have d0b : (0 : E1.toAffine.Point) ≠ E1P10 :=
      fun h => (WeierstrassCurve.Affine.Point.some_ne_zero
        (W' := E1.toAffine) (x := 1) (y := 0) _) h.symm
    have d0c : (0 : E1.toAffine.Point) ≠ E1Pm10 :=
      fun h => (WeierstrassCurve.Affine.Point.some_ne_zero
        (W' := E1.toAffine) (x := -1) (y := 0) _) h.symm
    have dab : E1P00 ≠ E1P10 := by simp [E1P00, E1P10]
    have dac : E1P00 ≠ E1Pm10 := by simp [E1P00, E1Pm10]
    have dbc : E1P10 ≠ E1Pm10 := by
      intro h
      simp [E1P10, E1Pm10] at h
      norm_num at h
    have m1 : (0 : E1.toAffine.Point) ∉
        ({E1P00, E1P10, E1Pm10} : Finset E1.toAffine.Point) := by
      simp [Finset.mem_insert, Finset.mem_singleton, d0a, d0b, d0c]
    have m2 : E1P00 ∉
        ({E1P10, E1Pm10} : Finset E1.toAffine.Point) := by
      simp [Finset.mem_insert, Finset.mem_singleton, dab, dac]
    have m3 : E1P10 ∉ ({E1Pm10} : Finset E1.toAffine.Point) := by
      simp [Finset.mem_singleton, dbc]
    rw [Finset.card_insert_of_notMem m1, Finset.card_insert_of_notMem m2,
      Finset.card_insert_of_notMem m3, Finset.card_singleton]
  show Nat.card (AddCommGroup.torsion E1.toAffine.Point) = 4
  calc Nat.card (AddCommGroup.torsion E1.toAffine.Point)
      = Nat.card ↥({0, E1P00, E1P10, E1Pm10} :
          Finset E1.toAffine.Point) :=
        Nat.card_congr (Equiv.subtypeEquivProp hpropeq)
    _ = ({0, E1P00, E1P10, E1Pm10} : Finset E1.toAffine.Point).card :=
        Nat.card_eq_finsetCard _
    _ = 4 := hcardS

/-! ## Axiom checks (headline results) -/

#print axioms E1_delta
#print axioms eq_of_sq_dvd_64
#print axioms e1_int_point_cases
#print axioms E1_neg_some_zero
#print axioms E1_two_nsmul_some_zero
#print axioms E1_some_zero_mem_torsion
#print axioms E1_point_eq_of_torsion
#print axioms e1_mem_torsion_iff
#print axioms e1TorsionCard_of_nagellLutz

end ThetLogos
