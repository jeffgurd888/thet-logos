import Mathlib.Tactic
import Mathlib.Analysis.Real.Pi.Irrational
import ThetLogos.DialOneSwapOrbit

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneDoubleFlipPin
open ThetLogos.DialOneGammaTraceChecks
open ThetLogos.DialOneGammaFamilyPin
open ThetLogos.DialOneGammaFamilyChecks
open ThetLogos.DialOneClassificationPin
open ThetLogos.DialOneSwapOrbit

/-!
# CLS-2b — the Base clause at the uniform triple swap

NO CLAIM; Dial 1 = 0. CLS-2 (landed, `DialOneSwapOrbit`)
reduced membership of the all-swap orbit point
`orbitRep allSwapBits` in `DialOneStrengthenedFam` exactly
to `DialOneBase (orbitRep allSwapBits)`
(`strengthened_allSwap_iff_base`), with C3 and the clean
γ-family already landed there. This module decides that
base clause, clause by clause through the landed
`DialOneBase` definition.

The mechanism is the colour-uniformity of the triple swap:
the corrections act at the six quark-R seats
{uSeat c, dSeat c} and their partners, identically across
the three colours, with the u/d coefficient depending only
on the isospin seat (not the colour). The single-colour
swaps fail order-zero precisely through a set/unset colour
pair; at the uniform point no such pair exists, and the
cross-colour entries of `rho1` (colour matrices at fixed
isospin) are matched on both sides because the correction
coefficient is colour-blind. Where a clause is transported
from π₁, the transport is proved, not asserted by analogy
with piDouble (whose (1↔9) transport does not cover quark
seats).
-/

namespace ThetLogos.DialOneSwapOrbitBase

/-! ## §0. The all-swap representative as π₁ + corrections -/

/-- The total swap correction: the three colours'
`orbitCorrS` corrections. -/
def swapCorr (a : AF) : Matrix (Fin 32) (Fin 32) ℂ :=
  orbitCorrS 0 a + orbitCorrS 1 a + orbitCorrS 2 a

/-- The all-swap representative is π₁ plus the total swap
correction (bit 0 unset, bits 1–3 set). -/
theorem allSwap_eq (a : AF) :
    orbitRep allSwapBits a = pi1 a + swapCorr a := by
  simp only [orbitRep, allSwapBits, swapCorr]
  norm_num [add_assoc]

/-- The opposite-side correction: `piOp` of the total swap
correction, as a sum of diagonal singles at the partner
seats with the same coefficients. -/
def swapCorrOp (b : AF) : Matrix (Fin 32) (Fin 32) ℂ :=
  Matrix.single (partner (uSeat 0)) (partner (uSeat 0)) (star b.u1 - b.u1)
    + Matrix.single (partner (dSeat 0)) (partner (dSeat 0)) (b.u1 - star b.u1)
    + Matrix.single (partner (uSeat 1)) (partner (uSeat 1)) (star b.u1 - b.u1)
    + Matrix.single (partner (dSeat 1)) (partner (dSeat 1)) (b.u1 - star b.u1)
    + Matrix.single (partner (uSeat 2)) (partner (uSeat 2)) (star b.u1 - b.u1)
    + Matrix.single (partner (dSeat 2)) (partner (dSeat 2)) (b.u1 - star b.u1)

/-- `piOp ∘ (orbitRep allSwapBits)` is `rho1` plus the
opposite-side correction. -/
theorem rhoAllSwap_eq (b : AF) :
    piOp (orbitRep allSwapBits b) = ThetLogos.Track1RouteB.rho1 b + swapCorrOp b := by
  rw [allSwap_eq, piOp_add]
  have h1 : piOp (pi1 b) = ThetLogos.Track1RouteB.rho1 b := rfl
  rw [h1]
  congr 1
  rw [swapCorr, swapCorrOp, piOp_add, piOp_add,
    orbitCorrS, orbitCorrS, orbitCorrS,
    piOp_add, piOp_add, piOp_add,
    piOp_single, piOp_single, piOp_single, piOp_single,
    piOp_single, piOp_single]
  abel

/-! ## §1. Entry lemmas for the corrections -/

/-- The dSeat diagonal of one colour's correction. -/
theorem orbitCorrS_dSeat_diag (c : Fin 3) (a : AF) :
    orbitCorrS c a (dSeat c) (dSeat c) = a.u1 - star a.u1 := by
  have hu : ¬ (uSeat c = dSeat c ∧ uSeat c = dSeat c) :=
    fun h => uSeat_ne_dSeat c h.1
  rw [orbitCorrS, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply, if_neg hu, if_pos ⟨rfl, rfl⟩, zero_add]

/-- Another colour's correction vanishes at the dSeat
diagonal. -/
theorem orbitCorrS_dSeat_of_ne (c c' : Fin 3) (h : c' ≠ c) (a : AF) :
    orbitCorrS c' a (dSeat c) (dSeat c) = 0 := by
  have hu : ¬ (uSeat c' = dSeat c ∧ uSeat c' = dSeat c) := by
    intro hh; have hv := congrArg Fin.val hh.1
    simp only [uSeat, dSeat] at hv; have hc := c'.isLt; have hc2 := c.isLt
    omega
  have hd : ¬ (dSeat c' = dSeat c ∧ dSeat c' = dSeat c) := by
    intro hh; apply h
    have hv := congrArg Fin.val hh.1
    simp only [dSeat] at hv
    exact Fin.ext (by omega)
  rw [orbitCorrS, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply, if_neg hu, if_neg hd, add_zero]

/-- One colour's correction at the uSeat diagonal, as an
if on the colour. -/
theorem orbitCorrS_uSeat_diag_if (c c' : Fin 3) (a : AF) :
    orbitCorrS c' a (uSeat c) (uSeat c)
      = if c' = c then star a.u1 - a.u1 else 0 := by
  by_cases h : c' = c
  · subst h; rw [if_pos rfl, orbitCorrS_uSeat_diag]
  · rw [if_neg h, orbitCorrS_uSeat_of_ne c c' h]

/-- One colour's correction at the dSeat diagonal, as an
if on the colour. -/
theorem orbitCorrS_dSeat_diag_if (c c' : Fin 3) (a : AF) :
    orbitCorrS c' a (dSeat c) (dSeat c)
      = if c' = c then a.u1 - star a.u1 else 0 := by
  by_cases h : c' = c
  · subst h; rw [if_pos rfl, orbitCorrS_dSeat_diag]
  · rw [if_neg h, orbitCorrS_dSeat_of_ne c c' h]

/-- The total correction at a uSeat diagonal: the swapped
value's difference `star a.u1 - a.u1`, colour-uniform. -/
theorem swapCorr_uSeat_diag (c : Fin 3) (a : AF) :
    swapCorr a (uSeat c) (uSeat c) = star a.u1 - a.u1 := by
  rw [swapCorr, Matrix.add_apply, Matrix.add_apply,
    orbitCorrS_uSeat_diag_if, orbitCorrS_uSeat_diag_if,
    orbitCorrS_uSeat_diag_if]
  fin_cases c <;> simp <;> ring

/-- The total correction at a dSeat diagonal. -/
theorem swapCorr_dSeat_diag (c : Fin 3) (a : AF) :
    swapCorr a (dSeat c) (dSeat c) = a.u1 - star a.u1 := by
  rw [swapCorr, Matrix.add_apply, Matrix.add_apply,
    orbitCorrS_dSeat_diag_if, orbitCorrS_dSeat_diag_if,
    orbitCorrS_dSeat_diag_if]
  fin_cases c <;> simp <;> ring

/-- One colour's correction vanishes off its two diagonal
seats. -/
theorem orbitCorrS_apply_of_ne (c : Fin 3) (a : AF) {i j : Fin 32}
    (h : ¬ ((i = uSeat c ∧ j = uSeat c) ∨ (i = dSeat c ∧ j = dSeat c))) :
    orbitCorrS c a i j = 0 := by
  have hu : ¬ (uSeat c = i ∧ uSeat c = j) :=
    fun hh => h (Or.inl ⟨hh.1.symm, hh.2.symm⟩)
  have hd : ¬ (dSeat c = i ∧ dSeat c = j) :=
    fun hh => h (Or.inr ⟨hh.1.symm, hh.2.symm⟩)
  rw [orbitCorrS, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply, if_neg hu, if_neg hd, add_zero]

/-- The total correction vanishes off the six diagonal
quark-R seats: if `i` is not a quark-R seat of any colour,
the whole row vanishes; if `j` is not, the column does. -/
theorem swapCorr_apply_of_row_notin (a : AF) {i j : Fin 32}
    (h : ∀ c : Fin 3, i ≠ uSeat c ∧ i ≠ dSeat c) :
    swapCorr a i j = 0 := by
  rw [swapCorr]
  have h0 : orbitCorrS 0 a i j = 0 :=
    orbitCorrS_apply_of_ne 0 a (by
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact (h 0).1 h1
      · exact (h 0).2 h1)
  have h1 : orbitCorrS 1 a i j = 0 :=
    orbitCorrS_apply_of_ne 1 a (by
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact (h 1).1 h1
      · exact (h 1).2 h1)
  have h2 : orbitCorrS 2 a i j = 0 :=
    orbitCorrS_apply_of_ne 2 a (by
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact (h 2).1 h1
      · exact (h 2).2 h1)
  rw [Matrix.add_apply, Matrix.add_apply, h0, h1, h2, add_zero, add_zero]

theorem swapCorr_apply_of_col_notin (a : AF) {i j : Fin 32}
    (h : ∀ c : Fin 3, j ≠ uSeat c ∧ j ≠ dSeat c) :
    swapCorr a i j = 0 := by
  rw [swapCorr]
  have h0 : orbitCorrS 0 a i j = 0 :=
    orbitCorrS_apply_of_ne 0 a (by
      rintro (⟨-, h2⟩ | ⟨-, h2⟩)
      · exact (h 0).1 h2
      · exact (h 0).2 h2)
  have h1 : orbitCorrS 1 a i j = 0 :=
    orbitCorrS_apply_of_ne 1 a (by
      rintro (⟨-, h2⟩ | ⟨-, h2⟩)
      · exact (h 1).1 h2
      · exact (h 1).2 h2)
  have h2 : orbitCorrS 2 a i j = 0 :=
    orbitCorrS_apply_of_ne 2 a (by
      rintro (⟨-, h2⟩ | ⟨-, h2⟩)
      · exact (h 2).1 h2
      · exact (h 2).2 h2)
  rw [Matrix.add_apply, Matrix.add_apply, h0, h1, h2, add_zero, add_zero]

/-- Away from the six diagonal quark-R seats, the all-swap
representative agrees with π₁ entrywise. -/
theorem allSwap_apply_of_not_diag (a : AF) {i j : Fin 32}
    (h : ¬ ∃ c : Fin 3, (i = uSeat c ∧ j = uSeat c)
      ∨ (i = dSeat c ∧ j = dSeat c)) :
    orbitRep allSwapBits a i j = pi1 a i j := by
  rw [allSwap_eq, Matrix.add_apply]
  have hz : swapCorr a i j = 0 := by
    rw [swapCorr, Matrix.add_apply, Matrix.add_apply,
      orbitCorrS_apply_of_ne 0 a (fun hh => h ⟨0, hh⟩),
      orbitCorrS_apply_of_ne 1 a (fun hh => h ⟨1, hh⟩),
      orbitCorrS_apply_of_ne 2 a (fun hh => h ⟨2, hh⟩),
      add_zero, add_zero]
  rw [hz, add_zero]

/-! ## §2. π₁ at the dSeats, and single-product lemmas -/

/-- π₁'s dSeat diagonal is `star a.u1`. -/
theorem pi1_dSeat_diag (c : Fin 3) (a : AF) :
    pi1 a (dSeat c) (dSeat c) = star a.u1 := by
  have hseat : dSeat c
      = ⟨10 + 2 * c.val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩ :=
    Fin.ext (by simp [dSeat]; omega)
  rw [hseat]
  have h := pi1_entry_quarkR a c c ⟨1, by omega⟩ ⟨1, by omega⟩
  simpa using h

/-- π₁'s row at a dSeat is concentrated on the diagonal. -/
theorem pi1_row_dSeat (c : Fin 3) (a : AF) (j : Fin 32) :
    pi1 a (dSeat c) j = if j = dSeat c then star a.u1 else 0 := by
  fin_cases c <;> obtain ⟨v, hv⟩ := j <;> interval_cases v <;>
    simp [pi1, dSeat]

/-- π₁'s column at a dSeat is concentrated on the diagonal. -/
theorem pi1_col_dSeat (c : Fin 3) (a : AF) (k : Fin 32) :
    pi1 a k (dSeat c) = if k = dSeat c then star a.u1 else 0 := by
  fin_cases c <;> obtain ⟨v, hv⟩ := k <;> interval_cases v <;>
    simp [pi1, dSeat]

/-- A diagonal single times a matrix whose row at the seat
is concentrated: only the diagonal value survives. -/
theorem single_mul_of_row (M : Matrix (Fin 32) (Fin 32) ℂ) (s : Fin 32)
    (c v : ℂ) (hrow : ∀ j, M s j = if j = s then v else 0) :
    Matrix.single s s c * M = Matrix.single s s (c * v) := by
  ext i' j'
  rw [single_mul_apply, Matrix.single_apply, hrow]
  by_cases hi : s = i'
  · rw [if_pos hi]
    by_cases hj : j' = s
    · rw [if_pos hj, if_pos ⟨hi, hj.symm⟩]
    · rw [if_neg hj, if_neg (fun h : s = i' ∧ s = j' => hj h.2.symm),
        mul_zero]
  · rw [if_neg hi, if_neg (fun h : s = i' ∧ s = j' => hi h.1)]

/-- A matrix whose column at the seat is concentrated,
times a diagonal single. -/
theorem mul_single_of_col (M : Matrix (Fin 32) (Fin 32) ℂ) (s : Fin 32)
    (c v : ℂ) (hcol : ∀ k, M k s = if k = s then v else 0) :
    M * Matrix.single s s c = Matrix.single s s (v * c) := by
  ext i' j'
  rw [mul_single_apply, Matrix.single_apply, hcol]
  by_cases hj : s = j'
  · rw [if_pos hj]
    by_cases hi : i' = s
    · rw [if_pos hi, if_pos ⟨hi.symm, hj⟩]
    · rw [if_neg hi, if_neg (fun h : s = i' ∧ s = j' => hi h.1.symm),
        zero_mul]
  · rw [if_neg hj, if_neg (fun h : s = i' ∧ s = j' => hj h.2)]

/-- π₁ times one colour's correction: two diagonal singles
with coefficients multiplied by π₁'s seat values. -/
theorem pi1_mul_orbitCorrS (x y : AF) (c : Fin 3) :
    pi1 x * orbitCorrS c y
      = Matrix.single (uSeat c) (uSeat c) (x.u1 * (star y.u1 - y.u1))
        + Matrix.single (dSeat c) (dSeat c)
            (star x.u1 * (y.u1 - star y.u1)) := by
  rw [orbitCorrS, mul_add,
    mul_single_of_col _ _ _ _ (pi1_col_uSeat c x),
    mul_single_of_col _ _ _ _ (pi1_col_dSeat c x)]

/-- One colour's correction times π₁. -/
theorem orbitCorrS_mul_pi1 (x y : AF) (c : Fin 3) :
    orbitCorrS c x * pi1 y
      = Matrix.single (uSeat c) (uSeat c) ((star x.u1 - x.u1) * y.u1)
        + Matrix.single (dSeat c) (dSeat c)
            ((x.u1 - star x.u1) * star y.u1) := by
  rw [orbitCorrS, add_mul,
    single_mul_of_row _ _ _ _ (pi1_row_uSeat c y),
    single_mul_of_row _ _ _ _ (pi1_row_dSeat c y)]

/-- One colour's correction times itself (same colour):
the two diagonal singles multiply seatwise. -/
theorem orbitCorrS_mul_orbitCorrS_same (x y : AF) (c : Fin 3) :
    orbitCorrS c x * orbitCorrS c y
      = Matrix.single (uSeat c) (uSeat c)
          ((star x.u1 - x.u1) * (star y.u1 - y.u1))
        + Matrix.single (dSeat c) (dSeat c)
            ((x.u1 - star x.u1) * (y.u1 - star y.u1)) := by
  rw [orbitCorrS, orbitCorrS, add_mul, mul_add, mul_add,
    single_mul_single, single_mul_single, single_mul_single,
    single_mul_single,
    if_pos rfl, if_pos rfl,
    if_neg (dSeat_ne_uSeat c), if_neg (uSeat_ne_dSeat c),
    add_zero, zero_add]

/-- Distinct colours' corrections annihilate each other:
every seat of one colour differs from every seat of the
other (isospin parity separates uSeats from dSeats, and
the seat maps are colour-injective). -/
theorem orbitCorrS_mul_orbitCorrS_ne (x y : AF) {c c' : Fin 3}
    (h : c' ≠ c) :
    orbitCorrS c x * orbitCorrS c' y = 0 := by
  have huu : uSeat c ≠ uSeat c' := by
    intro hh; apply h; apply Fin.ext
    have hv := congrArg Fin.val hh
    simp only [uSeat] at hv; omega
  have hdd : dSeat c ≠ dSeat c' := by
    intro hh; apply h; apply Fin.ext
    have hv := congrArg Fin.val hh
    simp only [dSeat] at hv; omega
  have hud : uSeat c ≠ dSeat c' := by
    intro hh; have hv := congrArg Fin.val hh
    simp only [uSeat, dSeat] at hv; have hc := c.isLt; have hc' := c'.isLt
    omega
  have hdu : dSeat c ≠ uSeat c' := by
    intro hh; have hv := congrArg Fin.val hh
    simp only [uSeat, dSeat] at hv; have hc := c.isLt; have hc' := c'.isLt
    omega
  rw [orbitCorrS, orbitCorrS, add_mul, mul_add, mul_add,
    single_mul_single, single_mul_single, single_mul_single,
    single_mul_single,
    if_neg huu, if_neg hud, if_neg hdu, if_neg hdd,
    add_zero, add_zero]

/-! ## §3. The hom clauses, transported from π₁ -/

/-- **Per-colour multiplicativity identity**: one colour's
correction of a product is the sum of the three cross
terms. The coefficient identities are the uSeat identity
`x(ȳ−y) + (x̄−x)y + (x̄−x)(ȳ−y) = x̄ȳ − xy` and its dSeat
mirror — colour-uniform, isospin-only. -/
theorem orbitCorrS_afMul_key (a b : AF) (c : Fin 3) :
    orbitCorrS c (afMul a b)
      = pi1 a * orbitCorrS c b + orbitCorrS c a * pi1 b
        + orbitCorrS c a * orbitCorrS c b := by
  rw [pi1_mul_orbitCorrS, orbitCorrS_mul_pi1,
    orbitCorrS_mul_orbitCorrS_same]
  ext i j
  simp only [orbitCorrS, Matrix.add_apply, Matrix.single_apply]
  split_ifs with hu hd
  · exfalso
    exact uSeat_ne_dSeat c (hu.1.trans hd.1.symm)
  · simp only [add_zero]
    rw [afMul_u1, star_mul]
    ring
  · simp only [add_zero, zero_add]
    rw [afMul_u1, star_mul]
    ring
  · simp

/-- **Clause `afMul` for the all-swap representative**,
transported from `pi1_afMul` through the per-colour key
identities; distinct colours' corrections annihilate. -/
theorem allSwap_afMul (a b : AF) :
    orbitRep allSwapBits (afMul a b)
      = orbitRep allSwapBits a * orbitRep allSwapBits b := by
  rw [allSwap_eq, allSwap_eq, allSwap_eq]
  simp only [swapCorr, add_mul, mul_add]
  rw [pi1_afMul,
    orbitCorrS_mul_orbitCorrS_ne a b (c := 0) (c' := 1) (by decide),
    orbitCorrS_mul_orbitCorrS_ne a b (c := 0) (c' := 2) (by decide),
    orbitCorrS_mul_orbitCorrS_ne a b (c := 1) (c' := 0) (by decide),
    orbitCorrS_mul_orbitCorrS_ne a b (c := 1) (c' := 2) (by decide),
    orbitCorrS_mul_orbitCorrS_ne a b (c := 2) (c' := 0) (by decide),
    orbitCorrS_mul_orbitCorrS_ne a b (c := 2) (c' := 1) (by decide),
    orbitCorrS_afMul_key a b 0, orbitCorrS_afMul_key a b 1,
    orbitCorrS_afMul_key a b 2]
  abel

/-- One colour's correction is additive. -/
theorem orbitCorrS_afAdd (a b : AF) (c : Fin 3) :
    orbitCorrS c (afAdd a b) = orbitCorrS c a + orbitCorrS c b := by
  ext i j
  simp only [orbitCorrS, Matrix.add_apply, Matrix.single_apply,
    afAdd_u1, star_add]
  split_ifs <;> ring

/-- **Clause `afAdd` for the all-swap representative.** -/
theorem allSwap_afAdd (a b : AF) :
    orbitRep allSwapBits (afAdd a b)
      = orbitRep allSwapBits a + orbitRep allSwapBits b := by
  rw [allSwap_eq, allSwap_eq, allSwap_eq, pi1_afAdd]
  simp only [swapCorr, orbitCorrS_afAdd]
  abel

/-- A diagonal single's conjugate transpose. -/
theorem single_conjTranspose_diag (s : Fin 32) (c : ℂ) :
    (Matrix.single s s c)ᴴ = Matrix.single s s (star c) := by
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.single_apply,
    Matrix.single_apply]
  by_cases h : s = j ∧ s = i
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
  · rw [if_neg h, if_neg (fun hh : s = i ∧ s = j => h ⟨hh.2, hh.1⟩),
      star_zero]

/-- One colour's correction respects the star. -/
theorem orbitCorrS_afStar (a : AF) (c : Fin 3) :
    orbitCorrS c (afStar a) = (orbitCorrS c a)ᴴ := by
  have hu : star (afStar a).u1 - (afStar a).u1
      = star (star a.u1 - a.u1) := by
    rw [afStar_u1, star_sub, star_star]
  have hd : (afStar a).u1 - star (afStar a).u1
      = star (a.u1 - star a.u1) := by
    rw [afStar_u1, star_sub, star_star]
  rw [orbitCorrS, orbitCorrS, Matrix.conjTranspose_add,
    single_conjTranspose_diag, single_conjTranspose_diag, hu, hd]

/-- **Clause `afStar` for the all-swap representative.** -/
theorem allSwap_afStar (a : AF) :
    orbitRep allSwapBits (afStar a)
      = (orbitRep allSwapBits a)ᴴ := by
  rw [allSwap_eq, allSwap_eq, pi1_afStar, Matrix.conjTranspose_add]
  simp only [swapCorr, orbitCorrS_afStar, Matrix.conjTranspose_add]

/-- One colour's correction vanishes at `afOne`. -/
theorem orbitCorrS_one (c : Fin 3) : orbitCorrS c afOne = 0 := by
  ext i j
  simp [orbitCorrS, Matrix.single_apply, afOne_u1]

/-- One colour's correction vanishes at `afZero`. -/
theorem orbitCorrS_zero (c : Fin 3) : orbitCorrS c afZero = 0 := by
  ext i j
  simp [orbitCorrS, Matrix.single_apply, afZero_u1]

/-- **Clause `afOne` for the all-swap representative.** -/
theorem allSwap_one : orbitRep allSwapBits afOne = 1 := by
  rw [allSwap_eq, pi1_one]
  simp [swapCorr, orbitCorrS_one]

/-- **Clause `afZero` for the all-swap representative.** -/
theorem allSwap_zero : orbitRep allSwapBits afZero = 0 := by
  rw [allSwap_eq, pi1_zero]
  simp [swapCorr, orbitCorrS_zero]

/-! ## §4. Injectivity, grading, determinant -/

/-- If a seat's value is outside the quark-R range, no
diag-seat alternative applies at that seat. -/
theorem not_diag_of_val {i j : Fin 32} (hi : ¬ (10 ≤ i.val ∧ i.val < 16)) :
    ¬ ∃ c : Fin 3, (i = uSeat c ∧ j = uSeat c)
      ∨ (i = dSeat c ∧ j = dSeat c) := by
  rintro ⟨c, hc | hc⟩
  · exact hi ⟨by rw [hc.1]; simp only [uSeat]; omega,
      by rw [hc.1]; have hc3 := c.isLt; simp only [uSeat]; omega⟩
  · exact hi ⟨by rw [hc.1]; simp only [dSeat]; omega,
      by rw [hc.1]; have hc3 := c.isLt; simp only [dSeat]; omega⟩

/-- **Clause injectivity for the all-swap representative**:
the u1 component is read at seat 8 (untouched), the ℍ
component at the lepton-L seats (untouched), and the
colour component at the quark-Lc seats (untouched), exactly
as for π₁; transported through `allSwap_apply_of_not_diag`. -/
theorem allSwap_injective :
    Function.Injective (orbitRep allSwapBits) := by
  intro a b h
  obtain ⟨ua, qa, ma⟩ := a
  obtain ⟨ub, qb, mb⟩ := b
  have happly : ∀ (x : AF) (i j : Fin 32),
      ¬ (10 ≤ i.val ∧ i.val < 16) →
      orbitRep allSwapBits x i j = pi1 x i j := by
    intro x i j hi
    exact allSwap_apply_of_not_diag x (not_diag_of_val hi)
  have hu1 : ua = ub := by
    have h8 := congrFun (congrFun h ⟨8, by omega⟩) ⟨8, by omega⟩
    rw [happly _ _ _ (by decide), happly _ _ _ (by decide),
      pi1_entry_nuR, pi1_entry_nuR] at h8
    exact h8
  have hq : qa = qb := by
    ext s t
    have hst := congrFun (congrFun h ⟨s.val, by omega⟩)
      ⟨t.val, by omega⟩
    have hval : ¬ (10 ≤ (⟨s.val, by omega⟩ : Fin 32).val
        ∧ (⟨s.val, by omega⟩ : Fin 32).val < 16) := by
      have hs := s.isLt
      show ¬ (10 ≤ s.val ∧ s.val < 16)
      omega
    rw [happly _ _ _ hval, happly _ _ _ hval,
      pi1_entry_leptonL, pi1_entry_leptonL] at hst
    exact hst
  have hcolor : ma = mb := by
    ext k l
    have hkl := congrFun (congrFun h
      ⟨18 + 2 * k.val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩)
      ⟨18 + 2 * l.val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩
    have hval : ¬ (10 ≤ (⟨18 + 2 * k.val
          + (⟨0, by omega⟩ : Fin 2).val, by omega⟩ : Fin 32).val
        ∧ (⟨18 + 2 * k.val + (⟨0, by omega⟩ : Fin 2).val,
          by omega⟩ : Fin 32).val < 16) := by
      have hk := k.isLt
      show ¬ (10 ≤ 18 + 2 * k.val ∧ 18 + 2 * k.val < 16)
      omega
    rw [happly _ _ _ hval, happly _ _ _ hval,
      pi1_entry_quarkLc _ _ _ ⟨0, by omega⟩ ⟨0, by omega⟩,
      pi1_entry_quarkLc _ _ _ ⟨0, by omega⟩ ⟨0, by omega⟩] at hkl
    rw [if_pos rfl, if_pos rfl] at hkl
    have h2 := congrArg star hkl
    simpa using h2
  simp [hu1, hq, hcolor]

/-- A diagonal single commutes with the diagonal grading. -/
theorem gammaF_single_comm (s : Fin 32) (c : ℂ) :
    gammaF * Matrix.single s s c = Matrix.single s s c * gammaF := by
  ext i j
  rw [gammaF_mul_apply, mul_gammaF_apply, Matrix.single_apply]
  by_cases h : s = i ∧ s = j
  · obtain ⟨rfl, rfl⟩ : i = s ∧ j = s := ⟨h.1.symm, h.2.symm⟩
    rw [if_pos ⟨rfl, rfl⟩]
    exact mul_comm _ _
  · rw [if_neg h, mul_zero, zero_mul]

/-- One colour's correction is grading-even. -/
theorem orbitCorrS_grading (a : AF) (c : Fin 3) :
    gammaF * orbitCorrS c a = orbitCorrS c a * gammaF := by
  rw [orbitCorrS, mul_add, add_mul, gammaF_single_comm,
    gammaF_single_comm]

/-- The total correction is grading-even. -/
theorem swapCorr_grading (a : AF) :
    gammaF * swapCorr a = swapCorr a * gammaF := by
  simp only [swapCorr, mul_add, add_mul, orbitCorrS_grading]

/-- **Clause grading for the all-swap representative.** -/
theorem allSwap_grading (a : AF) :
    gammaF * orbitRep allSwapBits a
      = orbitRep allSwapBits a * gammaF := by
  rw [allSwap_eq, mul_add, add_mul, pi1_grading_even,
    swapCorr_grading]

/-- The seat-swap permutation of the six quark-R seats:
uSeat ↔ dSeat within each colour. -/
def swapPerm : Equiv.Perm (Fin 32) :=
  Equiv.swap (uSeat 0) (dSeat 0) * Equiv.swap (uSeat 1) (dSeat 1)
    * Equiv.swap (uSeat 2) (dSeat 2)

theorem swapPerm_uSeat (c : Fin 3) : swapPerm (uSeat c) = dSeat c := by
  fin_cases c <;> simp [swapPerm, Equiv.Perm.mul_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne] <;>
    decide

theorem swapPerm_dSeat (c : Fin 3) : swapPerm (dSeat c) = uSeat c := by
  fin_cases c <;> simp [swapPerm, Equiv.Perm.mul_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne] <;>
    decide

theorem swapPerm_of_ne {i : Fin 32}
    (h : ∀ c : Fin 3, i ≠ uSeat c ∧ i ≠ dSeat c) :
    swapPerm i = i := by
  simp [swapPerm, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne, (h 0).1, (h 0).2, (h 1).1, (h 1).2,
    (h 2).1, (h 2).2]

theorem swapPerm_involutive (i : Fin 32) :
    swapPerm (swapPerm i) = i := by
  by_cases hi : ∃ c : Fin 3, i = uSeat c ∨ i = dSeat c
  · obtain ⟨c, rfl | rfl⟩ := hi
    · rw [swapPerm_uSeat, swapPerm_dSeat]
    · rw [swapPerm_dSeat, swapPerm_uSeat]
  · push_neg at hi
    rw [swapPerm_of_ne hi, swapPerm_of_ne hi]

/-- π₁'s diagonal value at a uSeat is `lam`. -/
theorem pi1Diag_uSeat (lam μ : ℂ) (c : Fin 3) :
    pi1Diag lam μ (uSeat c) = lam := by
  have h := pi1DiagVal_quarkR lam μ c (0 : Fin 2)
  have hval : (uSeat c).val
      = 10 + 2 * c.val + (0 : Fin 2).val := by
    have hv1 : (uSeat c).val = 10 + 2 * c.val := rfl
    have hv2 : (0 : Fin 2).val = 0 := rfl
    rw [hv1, hv2]
    omega
  show pi1DiagVal lam μ (uSeat c).val = lam
  rw [hval]
  simpa using h

/-- π₁'s diagonal value at a dSeat is `star lam`. -/
theorem pi1Diag_dSeat (lam μ : ℂ) (c : Fin 3) :
    pi1Diag lam μ (dSeat c) = star lam := by
  have h := pi1DiagVal_quarkR lam μ c (1 : Fin 2)
  have hval : (dSeat c).val
      = 10 + 2 * c.val + (1 : Fin 2).val := by
    have hv1 : (dSeat c).val = 11 + 2 * c.val := rfl
    have hv2 : (1 : Fin 2).val = 1 := rfl
    rw [hv1, hv2]
    omega
  show pi1DiagVal lam μ (dSeat c).val = star lam
  rw [hval]
  simpa using h

/-- **The all-swap representative at the generator is the
π₁ diagonal read through the seat swap**: at every colour
the u_R weight is swapped against the u_L-type partner
value — the diagonal entries at uSeat/dSeat are exchanged,
all other seats fixed. -/
theorem allSwap_eq_diagonal (α β : ℤ) (t : ℝ) :
    orbitRep allSwapBits (u1ParamGen α β t)
      = Matrix.diagonal (fun i =>
          pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
            (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I)))
            (swapPerm i)) := by
  set lam : ℂ := Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)) with hlam
  set μ : ℂ := Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I)) with hμ
  have hU : u1ParamGen α β t = ⟨lam, 1, μ • (1 : Matrix I3 I3 ℂ)⟩ := rfl
  rw [hU, allSwap_eq]
  apply eq_diagonal_of_entry
  intro i j
  have hpi : pi1 ⟨lam, 1, μ • (1 : Matrix I3 I3 ℂ)⟩
      = Matrix.diagonal (pi1Diag lam μ) := pi1_eq_diagonal lam μ
  by_cases hij : i = j
  · subst hij
    rw [Matrix.add_apply, hpi, Matrix.diagonal_apply_eq, if_pos rfl]
    by_cases hu : ∃ c : Fin 3, i = uSeat c
    · obtain ⟨c, rfl⟩ := hu
      rw [swapCorr_uSeat_diag, pi1Diag_uSeat, swapPerm_uSeat,
        pi1Diag_dSeat]
      show lam + (star lam - lam) = star lam
      ring
    · by_cases hd : ∃ c : Fin 3, i = dSeat c
      · obtain ⟨c, rfl⟩ := hd
        rw [swapCorr_dSeat_diag, pi1Diag_dSeat, swapPerm_dSeat,
          pi1Diag_uSeat]
        show star lam + (lam - star lam) = lam
        ring
      · have hz : swapCorr ⟨lam, 1, μ • (1 : Matrix I3 I3 ℂ)⟩ i i = 0 := by
          apply swapCorr_apply_of_row_notin
          intro c
          constructor
          · intro hh; apply hu; exact ⟨c, hh⟩
          · intro hh; apply hd; exact ⟨c, hh⟩
        have hfix : swapPerm i = i := by
          apply swapPerm_of_ne
          intro c
          constructor
          · intro hh; apply hu; exact ⟨c, hh⟩
          · intro hh; apply hd; exact ⟨c, hh⟩
        rw [hz, hfix, add_zero]
  · rw [Matrix.add_apply, hpi, Matrix.diagonal_apply_ne _ hij,
    if_neg hij, zero_add]
    have hz : swapCorr ⟨lam, 1, μ • (1 : Matrix I3 I3 ℂ)⟩ i j = 0 := by
      rw [swapCorr, Matrix.add_apply, Matrix.add_apply,
        orbitCorrS_apply_of_ne 0 _ (fun hh => hij (hh.elim
          (fun hh2 => hh2.1.trans hh2.2.symm)
          (fun hh2 => hh2.1.trans hh2.2.symm))),
        orbitCorrS_apply_of_ne 1 _ (fun hh => hij (hh.elim
          (fun hh2 => hh2.1.trans hh2.2.symm)
          (fun hh2 => hh2.1.trans hh2.2.symm))),
        orbitCorrS_apply_of_ne 2 _ (fun hh => hij (hh.elim
          (fun hh2 => hh2.1.trans hh2.2.symm)
          (fun hh2 => hh2.1.trans hh2.2.symm))),
        add_zero, add_zero]
    rw [hz]

/-- **The all-swap determinant at the generator is π₁'s
exactly**: the seat swap permutes the diagonal factors. -/
theorem allSwap_det_gen (α β : ℤ) (t : ℝ) :
    (orbitRep allSwapBits (u1ParamGen α β t)).det
      = (pi1 (u1ParamGen α β t)).det := by
  have hU : u1ParamGen α β t
      = ⟨Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)), 1,
        Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))
          • (1 : Matrix I3 I3 ℂ)⟩ := rfl
  rw [allSwap_eq_diagonal, Matrix.det_diagonal, hU, pi1_eq_diagonal,
    Matrix.det_diagonal]
  exact Fintype.prod_equiv swapPerm
    (fun i => pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
      (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) (swapPerm i))
    (pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
      (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))))
    (fun _ => rfl)

/-! ## §5. Order-zero: entry and product lemmas -/

/-- The opposite-side correction is `piOp` of the total
swap correction (the two descriptions agree, by cancelling
`rho1` in `rhoAllSwap_eq`). -/
theorem swapCorrOp_eq (b : AF) :
    swapCorrOp b = piOp (swapCorr b) := by
  have h2 : ThetLogos.Track1RouteB.rho1 b + swapCorrOp b
      = ThetLogos.Track1RouteB.rho1 b + piOp (swapCorr b) := by
    rw [← rhoAllSwap_eq, allSwap_eq, piOp_add]
    rfl
  exact add_left_cancel h2

/-- The total correction vanishes at `(k, j)` whenever
`k ≠ j` (it is diagonal). -/
theorem swapCorr_apply_of_ne {a : AF} {k j : Fin 32} (h : k ≠ j) :
    swapCorr a k j = 0 := by
  rw [swapCorr, Matrix.add_apply, Matrix.add_apply,
    orbitCorrS_apply_of_ne 0 a (fun hh => h (hh.elim
      (fun h2 => h2.1.trans h2.2.symm) (fun h2 => h2.1.trans h2.2.symm))),
    orbitCorrS_apply_of_ne 1 a (fun hh => h (hh.elim
      (fun h2 => h2.1.trans h2.2.symm) (fun h2 => h2.1.trans h2.2.symm))),
    orbitCorrS_apply_of_ne 2 a (fun hh => h (hh.elim
      (fun h2 => h2.1.trans h2.2.symm) (fun h2 => h2.1.trans h2.2.symm))),
    add_zero, add_zero]

/-- The opposite correction vanishes at `(k, j)` whenever
`k ≠ j`. -/
theorem swapCorrOp_apply_of_ne {b : AF} {k j : Fin 32} (h : k ≠ j) :
    swapCorrOp b k j = 0 := by
  rw [swapCorrOp_eq, piOp_apply]
  apply swapCorr_apply_of_ne
  intro hh
  apply h
  have h2 := congrArg partner hh
  rw [partner_involutive, partner_involutive] at h2
  exact h2.symm

/-- Product entry: a matrix times a diagonal correction
picks out the correction's diagonal at the column. -/
theorem mul_swapCorr_entry (M : Matrix (Fin 32) (Fin 32) ℂ) (a : AF)
    (i j : Fin 32) :
    (M * swapCorr a) i j = M i j * swapCorr a j j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · intro k _ hk
    rw [swapCorr_apply_of_ne hk, mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ j) hcon

theorem swapCorr_mul_entry (M : Matrix (Fin 32) (Fin 32) ℂ) (a : AF)
    (i j : Fin 32) :
    (swapCorr a * M) i j = swapCorr a i i * M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rw [swapCorr_apply_of_ne (Ne.symm hk), zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ i) hcon

theorem mul_swapCorrOp_entry (M : Matrix (Fin 32) (Fin 32) ℂ) (b : AF)
    (i j : Fin 32) :
    (M * swapCorrOp b) i j = M i j * swapCorrOp b j j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · intro k _ hk
    rw [swapCorrOp_apply_of_ne hk, mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ j) hcon

theorem swapCorrOp_mul_entry (M : Matrix (Fin 32) (Fin 32) ℂ) (b : AF)
    (i j : Fin 32) :
    (swapCorrOp b * M) i j = swapCorrOp b i i * M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rw [swapCorrOp_apply_of_ne (Ne.symm hk), zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ i) hcon

/-- The total correction's diagonal outside the quark-R
range vanishes. -/
theorem swapCorr_diag_of_notin (a : AF) {z : Fin 32}
    (hz : ¬ (10 ≤ z.val ∧ z.val < 16)) : swapCorr a z z = 0 := by
  apply swapCorr_apply_of_row_notin
  intro c
  refine ⟨fun hh => ?_, fun hh => ?_⟩
  · have hv := congrArg Fin.val hh
    simp only [uSeat] at hv
    omega
  · have hv := congrArg Fin.val hh
    simp only [dSeat] at hv
    omega

/-- The opposite correction's diagonal outside the
quark-Rc range vanishes. -/
theorem swapCorrOp_diag_of_notin (b : AF) {z : Fin 32}
    (hz : ¬ (26 ≤ z.val ∧ z.val < 32)) : swapCorrOp b z z = 0 := by
  rw [swapCorrOp_eq, piOp_apply]
  apply swapCorr_apply_of_row_notin
  intro c
  refine ⟨fun hh => ?_, fun hh => ?_⟩
  · have hv := congrArg Fin.val hh
    rw [partner_val_eq] at hv
    simp only [uSeat] at hv
    split_ifs at hv <;> omega
  · have hv := congrArg Fin.val hh
    rw [partner_val_eq] at hv
    simp only [dSeat] at hv
    split_ifs at hv <;> omega

/-- The total correction's diagonal in the quark-R range:
the coefficient depends only on the seat parity
(isospin), not the colour — the colour-uniformity at the
heart of this brick. -/
theorem swapCorr_diag_R (a : AF) {i : Fin 32}
    (hi : 10 ≤ i.val ∧ i.val < 16) :
    swapCorr a i i
      = if i.val % 2 = 0 then star a.u1 - a.u1 else a.u1 - star a.u1 := by
  by_cases hpar : i.val % 2 = 0
  · rw [if_pos hpar]
    have hseat : i = uSeat ⟨(i.val - 10) / 2, by omega⟩ :=
      Fin.ext (by simp only [uSeat]; omega)
    rw [hseat, swapCorr_uSeat_diag]
  · rw [if_neg hpar]
    have hseat : i = dSeat ⟨(i.val - 10) / 2, by omega⟩ :=
      Fin.ext (by simp only [dSeat]; omega)
    rw [hseat, swapCorr_dSeat_diag]

/-- The opposite correction's diagonal in the quark-Rc
range: same parity-only coefficient. -/
theorem swapCorrOp_diag_Rc (b : AF) {i : Fin 32}
    (hi : 26 ≤ i.val ∧ i.val < 32) :
    swapCorrOp b i i
      = if i.val % 2 = 0 then star b.u1 - b.u1 else b.u1 - star b.u1 := by
  rw [swapCorrOp_eq, piOp_apply]
  have hpar : (partner i).val % 2 = i.val % 2 := by
    rw [partner_val_eq]
    split_ifs <;> omega
  have hrange : 10 ≤ (partner i).val ∧ (partner i).val < 16 := by
    rw [partner_val_eq]
    split_ifs <;> omega
  rw [swapCorr_diag_R b hrange, hpar]

/-- Seat decomposition in the quark-R range. -/
theorem R_seat_decomp {i : Fin 32} (hi : 10 ≤ i.val ∧ i.val < 16) :
    ∃ (c : Fin 3) (s : Fin 2),
      i = ⟨10 + 2 * c.val + s.val, by omega⟩ := by
  refine ⟨⟨(i.val - 10) / 2, by omega⟩, ⟨(i.val - 10) % 2, by omega⟩,
    Fin.ext ?_⟩
  show i.val = 10 + 2 * ((i.val - 10) / 2) + (i.val - 10) % 2
  omega

/-- Seat decomposition in the quark-Rc range. -/
theorem Rc_seat_decomp {i : Fin 32} (hi : 26 ≤ i.val ∧ i.val < 32) :
    ∃ (c : Fin 3) (s : Fin 2),
      i = ⟨26 + 2 * c.val + s.val, by omega⟩ := by
  refine ⟨⟨(i.val - 26) / 2, by omega⟩, ⟨(i.val - 26) % 2, by omega⟩,
    Fin.ext ?_⟩
  show i.val = 26 + 2 * ((i.val - 26) / 2) + (i.val - 26) % 2
  omega

/-- The partner of a quark-R seat in decomposition form. -/
theorem partner_R_seat (c : Fin 3) (s : Fin 2) :
    partner ⟨10 + 2 * c.val + s.val, by omega⟩
      = ⟨26 + 2 * c.val + s.val, by omega⟩ := by
  apply Fin.ext
  have hc := c.isLt
  have hs := s.isLt
  show (partner ⟨10 + 2 * c.val + s.val, by omega⟩).val
    = 26 + 2 * c.val + s.val
  have hval : (⟨10 + 2 * c.val + s.val, by omega⟩ : Fin 32).val
      = 10 + 2 * c.val + s.val := rfl
  rw [partner_val_eq, hval]
  split_ifs <;> omega

/-- `rho1` entries vanish across sectors. -/
theorem rho1_cross_sector (b : AF) {i j : Fin 32}
    (h : i.val / 8 ≠ j.val / 8) :
    ThetLogos.Track1RouteB.rho1 b i j = 0 :=
  rho1_entry_eq_zero_of_not_sameBlock b (not_sameBlock_of_ne_sector h)

/-- `rho1` on the quark-R block: the colour matrix at
fixed isospin, transposed through the partner seats —
the same formula as on the quark-L block. -/
theorem rho1_R_block (b : AF) {i j : Fin 32}
    (hi : 10 ≤ i.val ∧ i.val < 16) (hj : 10 ≤ j.val ∧ j.val < 16) :
    ThetLogos.Track1RouteB.rho1 b i j
      = if i.val % 2 = j.val % 2
        then star (b.color ⟨(j.val - 10) / 2, by omega⟩
          ⟨(i.val - 10) / 2, by omega⟩) else 0 := by
  obtain ⟨cj, sj, hjseat⟩ := R_seat_decomp hj
  obtain ⟨ci, si, hiseat⟩ := R_seat_decomp hi
  have hparj : (j.val - 10) / 2 = cj.val ∧ (j.val - 10) % 2 = sj.val := by
    have hv : j.val = 10 + 2 * cj.val + sj.val := by
      have h2 := congrArg Fin.val hjseat
      simpa using h2
    have hc := cj.isLt
    have hs := sj.isLt
    constructor <;> omega
  have hpari : (i.val - 10) / 2 = ci.val ∧ (i.val - 10) % 2 = si.val := by
    have hv : i.val = 10 + 2 * ci.val + si.val := by
      have h2 := congrArg Fin.val hiseat
      simpa using h2
    have hc := ci.isLt
    have hs := si.isLt
    constructor <;> omega
  have h1 : ThetLogos.Track1RouteB.rho1 b i j
      = ThetLogos.Track1RouteB.rho1 b
          ⟨10 + 2 * ci.val + si.val, by omega⟩
          ⟨10 + 2 * cj.val + sj.val, by omega⟩ := by
    rw [hiseat, hjseat]
  rw [h1, rho1_entry, partner_R_seat, partner_R_seat,
    pi1_entry_quarkRc]
  have hcj : (⟨(j.val - 10) / 2, by omega⟩ : Fin 3) = cj :=
    Fin.ext hparj.1
  have hci : (⟨(i.val - 10) / 2, by omega⟩ : Fin 3) = ci :=
    Fin.ext hpari.1
  rw [hcj, hci]
  by_cases hps : sj = si
  · have hpsv : sj.val = si.val := congrArg Fin.val hps
    have hpar : i.val % 2 = j.val % 2 := by
      have h1 : i.val % 2 = si.val := by omega
      have h2 : j.val % 2 = sj.val := by omega
      omega
    rw [if_pos hps, if_pos hpar]
  · have hpar : ¬ (i.val % 2 = j.val % 2) := by
      intro hh
      apply hps
      apply Fin.ext
      have h1 : i.val % 2 = si.val := by omega
      have h2 : j.val % 2 = sj.val := by omega
      omega
    rw [if_neg hps, if_neg hpar]

/-- π₁ on the quark-Rc block: the colour matrix at fixed
isospin. -/
theorem pi1_Rc_block (a : AF) {i j : Fin 32}
    (hi : 26 ≤ i.val ∧ i.val < 32) (hj : 26 ≤ j.val ∧ j.val < 32) :
    pi1 a i j
      = if i.val % 2 = j.val % 2
        then star (a.color ⟨(i.val - 26) / 2, by omega⟩
          ⟨(j.val - 26) / 2, by omega⟩) else 0 := by
  obtain ⟨cj, sj, hjseat⟩ := Rc_seat_decomp hj
  obtain ⟨ci, si, hiseat⟩ := Rc_seat_decomp hi
  have hparj : (j.val - 26) / 2 = cj.val ∧ (j.val - 26) % 2 = sj.val := by
    have hv : j.val = 26 + 2 * cj.val + sj.val := by
      have h2 := congrArg Fin.val hjseat
      simpa using h2
    have hc := cj.isLt
    have hs := sj.isLt
    constructor <;> omega
  have hpari : (i.val - 26) / 2 = ci.val ∧ (i.val - 26) % 2 = si.val := by
    have hv : i.val = 26 + 2 * ci.val + si.val := by
      have h2 := congrArg Fin.val hiseat
      simpa using h2
    have hc := ci.isLt
    have hs := si.isLt
    constructor <;> omega
  have h1 : pi1 a i j
      = pi1 a ⟨26 + 2 * ci.val + si.val, by omega⟩
          ⟨26 + 2 * cj.val + sj.val, by omega⟩ := by
    rw [hiseat, hjseat]
  rw [h1, pi1_entry_quarkRc]
  have hcj : (⟨(j.val - 26) / 2, by omega⟩ : Fin 3) = cj :=
    Fin.ext hparj.1
  have hci : (⟨(i.val - 26) / 2, by omega⟩ : Fin 3) = ci :=
    Fin.ext hpari.1
  rw [hcj, hci]
  by_cases hps : si = sj
  · have hpsv : si.val = sj.val := congrArg Fin.val hps
    have hpar : i.val % 2 = j.val % 2 := by
      have h1 : i.val % 2 = si.val := by omega
      have h2 : j.val % 2 = sj.val := by omega
      omega
    rw [if_pos hps, if_pos hpar]
  · have hpar : ¬ (i.val % 2 = j.val % 2) := by
      intro hh
      apply hps
      apply Fin.ext
      have h1 : i.val % 2 = si.val := by omega
      have h2 : j.val % 2 = sj.val := by omega
      omega
    rw [if_neg hps, if_neg hpar]

/-- `rho1` with quark-R row and column outside the
quark-R range vanishes: the partner column sits in the
quark-Rc block, whose support is the partner range. -/
theorem rho1_R_row_vanish (b : AF) (c : Fin 3) (s : Fin 2)
    {j : Fin 32} (hj : ¬ (10 ≤ j.val ∧ j.val < 16)) :
    ThetLogos.Track1RouteB.rho1 b
        ⟨10 + 2 * c.val + s.val, by omega⟩ j = 0 := by
  rw [rho1_entry, partner_R_seat]
  by_cases hj8 : j = ⟨8, by omega⟩
  · subst hj8
    have hp : partner ⟨8, by omega⟩ = ⟨24, by omega⟩ := by
      apply Fin.ext
      show (partner ⟨8, by omega⟩).val = 24
      rw [partner_val_eq]
      norm_num
    rw [hp]
    apply pi1_vanish_nuRc
    simp only [Finset.mem_singleton]
    intro hh
    have hv := congrArg Fin.val hh
    have hc := c.isLt
    have hs := s.isLt
    dsimp only at hv
    omega
  · by_cases hj9 : j = ⟨9, by omega⟩
    · subst hj9
      have hp : partner ⟨9, by omega⟩ = ⟨25, by omega⟩ := by
        apply Fin.ext
        show (partner ⟨9, by omega⟩).val = 25
        rw [partner_val_eq]
        norm_num
      rw [hp]
      apply pi1_vanish_eRc
      simp only [Finset.mem_singleton]
      intro hh
      have hv := congrArg Fin.val hh
      have hc := c.isLt
      have hs := s.isLt
      dsimp only at hv
      omega
    · apply pi1_entry_cross_sector
      have hjv8 : j.val ≠ 8 := fun hh => hj8 (Fin.ext hh)
      have hjv9 : j.val ≠ 9 := fun hh => hj9 (Fin.ext hh)
      have hc := c.isLt
      have hs := s.isLt
      show (partner j).val / 8
        ≠ (⟨26 + 2 * c.val + s.val, by omega⟩ : Fin 32).val / 8
      have hv26 : (⟨26 + 2 * c.val + s.val, by omega⟩ : Fin 32).val
          = 26 + 2 * c.val + s.val := rfl
      rw [hv26]
      have hvp : (partner j).val
          = if j.val < 16 then j.val + 16 else j.val - 16 :=
        partner_val_eq j
      rw [hvp]
      split_ifs <;> omega

/-- `rho1` with column a quark-R seat and row outside the
quark-R range vanishes. -/
theorem rho1_R_col_vanish (b : AF) (c : Fin 3) (s : Fin 2)
    {i : Fin 32} (hi : ¬ (10 ≤ i.val ∧ i.val < 16)) :
    ThetLogos.Track1RouteB.rho1 b i
        ⟨10 + 2 * c.val + s.val, by omega⟩ = 0 := by
  rw [rho1_entry, partner_R_seat]
  apply pi1_vanish_quarkRc
  intro hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h
  all_goals
    have hv := congrArg Fin.val h
    rw [partner_val_eq] at hv
    dsimp only at hv
    split_ifs at hv <;> omega

/-! ## §5b. Order-zero assembly -/

/-- The two corrections annihilate each other (disjoint
supports). -/
theorem swapCorr_mul_swapCorrOp (a b : AF) :
    swapCorr a * swapCorrOp b = 0 := by
  ext i j
  rw [Matrix.zero_apply, mul_swapCorrOp_entry]
  by_cases hj : 26 ≤ j.val ∧ j.val < 32
  · by_cases hij : i = j
    · subst hij
      rw [swapCorr_diag_of_notin a (by omega), zero_mul]
    · rw [swapCorr_apply_of_ne hij, zero_mul]
  · rw [swapCorrOp_diag_of_notin b hj, mul_zero]

/-- The two corrections annihilate each other, mirrored. -/
theorem swapCorrOp_mul_swapCorr (a b : AF) :
    swapCorrOp b * swapCorr a = 0 := by
  ext i j
  rw [Matrix.zero_apply, swapCorrOp_mul_entry]
  by_cases hi : 26 ≤ i.val ∧ i.val < 32
  · by_cases hij : i = j
    · subst hij
      rw [swapCorr_diag_of_notin a (by omega), mul_zero]
    · rw [swapCorr_apply_of_ne hij, mul_zero]
  · rw [swapCorrOp_diag_of_notin b hi, zero_mul]

/-- The cross identity at the heart of order-zero for the
uniform swap: on the quark-R block the correction's
parity-only diagonal commutes past `rho1`'s colour matrix
(the colour sum collapses because the coefficients are
colour-blind and `rho1`'s colour entries at fixed isospin
agree on both sides); on the quark-Rc block the mirrored
statement; every mixed or off-block entry vanishes. -/
theorem cross_oz (a b : AF) (i j : Fin 32) :
    (pi1 a * swapCorrOp b) i j + (swapCorr a * ThetLogos.Track1RouteB.rho1 b) i j
      = (swapCorrOp b * pi1 a) i j
        + (ThetLogos.Track1RouteB.rho1 b * swapCorr a) i j := by
  rw [mul_swapCorrOp_entry, swapCorr_mul_entry, swapCorrOp_mul_entry,
    mul_swapCorr_entry]
  by_cases hiS : 10 ≤ i.val ∧ i.val < 16
  · by_cases hjS : 10 ≤ j.val ∧ j.val < 16
    · -- (S, S): the colour-sum collapse
      rw [swapCorrOp_diag_of_notin b (by omega),
        swapCorrOp_diag_of_notin b (by omega), mul_zero, zero_mul,
        zero_add, zero_add, swapCorr_diag_R a hiS,
        swapCorr_diag_R a hjS, rho1_R_block b hiS hjS]
      by_cases hpar : i.val % 2 = j.val % 2
      · have hi0 : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
        rw [if_pos hpar]
        rcases hi0 with h0 | h1
        · have hj0 : j.val % 2 = 0 := by omega
          rw [if_pos h0, if_pos hj0]
          exact mul_comm _ _
        · have hj1 : ¬ j.val % 2 = 0 := by omega
          have hi1 : ¬ i.val % 2 = 0 := by omega
          rw [if_neg hi1, if_neg hj1]
          exact mul_comm _ _
      · rw [if_neg hpar, mul_zero, zero_mul]
    · by_cases hjS' : 26 ≤ j.val ∧ j.val < 32
      · -- (S, S'): everything vanishes cross-sector
        have hpi : pi1 a i j = 0 := pi1_entry_cross_sector a (by omega)
        rw [hpi, rho1_cross_sector b (by omega)]
        simp only [zero_mul, mul_zero, add_zero]
      · -- (S, outside): rho1 row vanishes
        have hrho : ThetLogos.Track1RouteB.rho1 b i j = 0 := by
          obtain ⟨c, s, hseat⟩ := R_seat_decomp hiS
          rw [hseat]
          exact rho1_R_row_vanish b c s hjS
        rw [hrho, swapCorrOp_diag_of_notin b hjS',
          swapCorrOp_diag_of_notin b (by omega),
          swapCorr_diag_of_notin a hjS]
        simp only [zero_mul, mul_zero, add_zero]
  · by_cases hiS' : 26 ≤ i.val ∧ i.val < 32
    · by_cases hjS' : 26 ≤ j.val ∧ j.val < 32
      · -- (S', S'): the mirrored collapse
        rw [swapCorr_diag_of_notin a (by omega),
          swapCorr_diag_of_notin a (by omega), zero_mul, mul_zero,
          add_zero, add_zero, pi1_Rc_block a hiS' hjS',
          swapCorrOp_diag_Rc b hiS', swapCorrOp_diag_Rc b hjS']
        by_cases hpar : i.val % 2 = j.val % 2
        · have hi0 : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
          rw [if_pos hpar]
          rcases hi0 with h0 | h1
          · have hj0 : j.val % 2 = 0 := by omega
            rw [if_pos h0, if_pos hj0]
            exact mul_comm _ _
          · have hj1 : ¬ j.val % 2 = 0 := by omega
            have hi1 : ¬ i.val % 2 = 0 := by omega
            rw [if_neg hi1, if_neg hj1]
            exact mul_comm _ _
        · rw [if_neg hpar, mul_zero, zero_mul]
      · by_cases hjS : 10 ≤ j.val ∧ j.val < 16
        · -- (S', S): everything vanishes cross-sector
          have hpi : pi1 a i j = 0 := pi1_entry_cross_sector a (by omega)
          rw [hpi, rho1_cross_sector b (by omega),
            swapCorr_diag_of_notin a (by omega),
            swapCorrOp_diag_of_notin b (by omega)]
          simp only [zero_mul, mul_zero, add_zero]
        · -- (S', outside): pi1 row vanishes on quark-Rc
          have hpi : pi1 a i j = 0 := by
            obtain ⟨c, s, hseat⟩ := Rc_seat_decomp hiS'
            rw [hseat]
            apply pi1_vanish_quarkRc
            intro hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h | h | h | h | h | h
            all_goals
              have hv := congrArg Fin.val h
              have hc := c.isLt
              have hs := s.isLt
              dsimp only at hv
              omega
          rw [hpi, swapCorr_diag_of_notin a (by omega),
            swapCorr_diag_of_notin a hjS]
          simp only [zero_mul, mul_zero, add_zero]
    · by_cases hjS : 10 ≤ j.val ∧ j.val < 16
      · -- (outside, S): rho1 column vanishes
        have hrho : ThetLogos.Track1RouteB.rho1 b i j = 0 := by
          obtain ⟨c, s, hseat⟩ := R_seat_decomp hjS
          rw [hseat]
          exact rho1_R_col_vanish b c s hiS
        rw [hrho, swapCorrOp_diag_of_notin b (by omega),
          swapCorrOp_diag_of_notin b (by omega),
          swapCorr_diag_of_notin a hiS]
        simp only [zero_mul, mul_zero, add_zero]
      · by_cases hjS' : 26 ≤ j.val ∧ j.val < 32
        · -- (outside, S'): pi1 column vanishes on quark-Rc
          have hpi : pi1 a i j = 0 := by
            obtain ⟨c, s, hseat⟩ := Rc_seat_decomp hjS'
            rw [hseat]
            apply pi1_vanish_col_quarkRc
            intro hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h | h | h | h | h | h
            all_goals
              have hv := congrArg Fin.val h
              have hc := c.isLt
              have hs := s.isLt
              dsimp only at hv
              omega
          rw [hpi, swapCorr_diag_of_notin a hiS,
            swapCorrOp_diag_of_notin b hiS',
            swapCorr_diag_of_notin a (by omega)]
          simp only [zero_mul, mul_zero, add_zero]
        · -- (outside, outside): all diagonal factors vanish
          rw [swapCorrOp_diag_of_notin b hjS',
            swapCorr_diag_of_notin a hiS,
            swapCorrOp_diag_of_notin b hiS',
            swapCorr_diag_of_notin a hjS]
          simp only [zero_mul, mul_zero, add_zero]

/-- Order-zero for the uniform swap. -/
theorem allSwap_order_zero (a b : AF) :
    orbitRep allSwapBits a * piOp (orbitRep allSwapBits b)
      = piOp (orbitRep allSwapBits b) * orbitRep allSwapBits a := by
  have hcross : pi1 a * swapCorrOp b
        + swapCorr a * ThetLogos.Track1RouteB.rho1 b
      = swapCorrOp b * pi1 a
        + ThetLogos.Track1RouteB.rho1 b * swapCorr a :=
    Matrix.ext fun i j => cross_oz a b i j
  calc orbitRep allSwapBits a * piOp (orbitRep allSwapBits b)
      = (pi1 a + swapCorr a)
          * (ThetLogos.Track1RouteB.rho1 b + swapCorrOp b) := by
        rw [rhoAllSwap_eq, allSwap_eq]
    _ = pi1 a * ThetLogos.Track1RouteB.rho1 b + pi1 a * swapCorrOp b
          + (swapCorr a * ThetLogos.Track1RouteB.rho1 b
            + swapCorr a * swapCorrOp b) := by
        rw [add_mul, mul_add, mul_add]
    _ = ThetLogos.Track1RouteB.rho1 b * pi1 a + pi1 a * swapCorrOp b
          + (swapCorr a * ThetLogos.Track1RouteB.rho1 b + 0) := by
        rw [pi1_order_zero, swapCorr_mul_swapCorrOp]
    _ = ThetLogos.Track1RouteB.rho1 b * pi1 a
          + (pi1 a * swapCorrOp b
            + swapCorr a * ThetLogos.Track1RouteB.rho1 b) := by
        rw [add_zero, add_assoc]
    _ = ThetLogos.Track1RouteB.rho1 b * pi1 a
          + (swapCorrOp b * pi1 a
            + ThetLogos.Track1RouteB.rho1 b * swapCorr a) := by
        rw [hcross]
    _ = ThetLogos.Track1RouteB.rho1 b * pi1 a
          + (ThetLogos.Track1RouteB.rho1 b * swapCorr a
            + swapCorrOp b * pi1 a) := by
        rw [add_comm (swapCorrOp b * pi1 a)
          (ThetLogos.Track1RouteB.rho1 b * swapCorr a)]
    _ = (ThetLogos.Track1RouteB.rho1 b * pi1 a
          + ThetLogos.Track1RouteB.rho1 b * swapCorr a)
          + swapCorrOp b * pi1 a := by
        rw [← add_assoc]
    _ = (ThetLogos.Track1RouteB.rho1 b + swapCorrOp b)
          * (pi1 a + swapCorr a) := by
        rw [add_mul, mul_add, mul_add, swapCorrOp_mul_swapCorr,
          add_zero]
    _ = piOp (orbitRep allSwapBits b) * orbitRep allSwapBits a := by
        rw [rhoAllSwap_eq, allSwap_eq]

/-! ## §6. First-order: entry infrastructure -/

/-- `Dval` is invariant under the matched slot (it depends
only on the value mod 8, and `md` shifts by 8). -/
theorem Dval_md (Ynu Ye Yu Yd : ℝ) (i : Fin 32) :
    Dval Ynu Ye Yu Yd (md i) = Dval Ynu Ye Yu Yd i := by
  rw [Dval_eq, Dval_eq]
  congr 1
  apply Fin.ext
  show (md i).val % 8 = i.val % 8
  rw [md_val]
  split_ifs <;> omega

/-- Product entry: `DF` times an arbitrary matrix. -/
theorem DF_mul_entry (Ynu Ye Yu Yd : ℝ)
    (M : Matrix (Fin 32) (Fin 32) ℂ) (i j : Fin 32) :
    (DF_oneGen Ynu Ye Yu Yd * M) i j
      = Dval Ynu Ye Yu Yd i * M (md i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (md i)]
  · rw [DF_oneGen_entry, if_pos rfl]
  · intro k _ hk
    rw [DF_oneGen_entry, if_neg hk, zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ (md i)) hcon

/-- Product entry: an arbitrary matrix times `DF`. -/
theorem mul_DF_entry (Ynu Ye Yu Yd : ℝ)
    (M : Matrix (Fin 32) (Fin 32) ℂ) (i j : Fin 32) :
    (M * DF_oneGen Ynu Ye Yu Yd) i j
      = M i (md j) * Dval Ynu Ye Yu Yd (md j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (md j)]
  · rw [DF_oneGen_entry, md_involutive, if_pos rfl]
  · intro k _ hk
    rw [DF_oneGen_entry, if_neg, mul_zero]
    intro hjk
    apply hk
    have hkj : md j = k := by
      rw [show md j = md (md k) from congrArg md hjk]
      exact md_involutive k
    exact hkj.symm
  · intro hcon
    exact absurd (Finset.mem_univ (md j)) hcon

/-- Entry of the correction commutator
`E = [DF, swapCorr a]`. -/
theorem E_entry (Ynu Ye Yu Yd : ℝ) (a : AF) (i j : Fin 32) :
    (DF_oneGen Ynu Ye Yu Yd * swapCorr a
        - swapCorr a * DF_oneGen Ynu Ye Yu Yd) i j
      = Dval Ynu Ye Yu Yd i * swapCorr a (md i) j
        - swapCorr a i (md j) * Dval Ynu Ye Yu Yd (md j) := by
  rw [Matrix.sub_apply, DF_mul_entry, mul_DF_entry]

/-- `E` vanishes off the matched pairs. -/
theorem E_apply_of_ne_md (Ynu Ye Yu Yd : ℝ) (a : AF) {i j : Fin 32}
    (h : j ≠ md i) :
    (DF_oneGen Ynu Ye Yu Yd * swapCorr a
        - swapCorr a * DF_oneGen Ynu Ye Yu Yd) i j = 0 := by
  have hne : i ≠ md j := by
    intro hh
    apply h
    have h2 : md i = md (md j) := congrArg md hh
    rw [md_involutive] at h2
    exact h2.symm
  rw [E_entry, swapCorr_apply_of_ne (Ne.symm h),
    swapCorr_apply_of_ne hne, mul_zero, zero_mul, sub_zero]

/-- `E` on a matched pair: only the two diagonal values of
the correction enter. -/
theorem E_pair (Ynu Ye Yu Yd : ℝ) (a : AF) (x : Fin 32) :
    (DF_oneGen Ynu Ye Yu Yd * swapCorr a
        - swapCorr a * DF_oneGen Ynu Ye Yu Yd) x (md x)
      = Dval Ynu Ye Yu Yd x
        * (swapCorr a (md x) (md x) - swapCorr a x x) := by
  rw [E_entry, md_involutive]
  ring

/-- `E` on a matched pair outside the quark band vanishes. -/
theorem E_pair_zero (Ynu Ye Yu Yd : ℝ) (a : AF) {x : Fin 32}
    (hx : ¬ (2 ≤ x.val ∧ x.val < 8) ∧ ¬ (10 ≤ x.val ∧ x.val < 16)) :
    (DF_oneGen Ynu Ye Yu Yd * swapCorr a
        - swapCorr a * DF_oneGen Ynu Ye Yu Yd) x (md x) = 0 := by
  have h2 : ¬ (10 ≤ (md x).val ∧ (md x).val < 16) := by
    rw [md_val]
    split_ifs <;> omega
  rw [E_pair, swapCorr_diag_of_notin a hx.2,
    swapCorr_diag_of_notin a h2, sub_self, mul_zero]

/-- Seat decomposition in the left-quark range. -/
theorem Lq_seat_decomp {i : Fin 32} (hi : 2 ≤ i.val ∧ i.val < 8) :
    ∃ (c : Fin 3) (s : Fin 2),
      i = ⟨2 + 2 * c.val + s.val, by omega⟩ := by
  refine ⟨⟨(i.val - 2) / 2, by omega⟩, ⟨(i.val - 2) % 2, by omega⟩,
    Fin.ext ?_⟩
  show i.val = 2 + 2 * ((i.val - 2) / 2) + (i.val - 2) % 2
  omega

/-- The matched slot on a left-quark seat. -/
theorem md_Lq_seat (c : Fin 3) (s : Fin 2) :
    md ⟨2 + 2 * c.val + s.val, by omega⟩
      = ⟨10 + 2 * c.val + s.val, by omega⟩ := by
  apply Fin.ext
  have hc := c.isLt
  have hs := s.isLt
  have hv : (⟨2 + 2 * c.val + s.val, by omega⟩ : Fin 32).val
      = 2 + 2 * c.val + s.val := rfl
  show (md ⟨2 + 2 * c.val + s.val, by omega⟩).val
    = 10 + 2 * c.val + s.val
  rw [md_val_L _ (by omega)]
  omega

/-- The matched slot on a quark-R seat. -/
theorem md_R_seat (c : Fin 3) (s : Fin 2) :
    md ⟨10 + 2 * c.val + s.val, by omega⟩
      = ⟨2 + 2 * c.val + s.val, by omega⟩ := by
  apply Fin.ext
  have hc := c.isLt
  have hs := s.isLt
  have hv : (⟨10 + 2 * c.val + s.val, by omega⟩ : Fin 32).val
      = 10 + 2 * c.val + s.val := rfl
  show (md ⟨10 + 2 * c.val + s.val, by omega⟩).val
    = 2 + 2 * c.val + s.val
  rw [md_val_R _ ⟨by omega, by omega⟩]
  omega

/-- The partner of a left-quark seat. -/
theorem partner_Lq_seat (c : Fin 3) (s : Fin 2) :
    partner ⟨2 + 2 * c.val + s.val, by omega⟩
      = ⟨18 + 2 * c.val + s.val, by omega⟩ := by
  apply Fin.ext
  have hc := c.isLt
  have hs := s.isLt
  have hv : (⟨2 + 2 * c.val + s.val, by omega⟩ : Fin 32).val
      = 2 + 2 * c.val + s.val := rfl
  show (partner ⟨2 + 2 * c.val + s.val, by omega⟩).val
    = 18 + 2 * c.val + s.val
  rw [partner_val_eq]
  split_ifs <;> omega

/-! ## §6b. First-order: `rho1` Lq block, vanishings -/

/-- `rho1` on the left-quark block: the colour matrix at
fixed isospin (colour indices crossed, as `rho1` is the
opposite representation). -/
theorem rho1_Lq_block (b : AF) {i j : Fin 32}
    (hi : 2 ≤ i.val ∧ i.val < 8) (hj : 2 ≤ j.val ∧ j.val < 8) :
    ThetLogos.Track1RouteB.rho1 b i j
      = if i.val % 2 = j.val % 2
        then star (b.color ⟨(j.val - 2) / 2, by omega⟩
          ⟨(i.val - 2) / 2, by omega⟩) else 0 := by
  obtain ⟨cj, sj, hjseat⟩ := Lq_seat_decomp hj
  obtain ⟨ci, si, hiseat⟩ := Lq_seat_decomp hi
  have hparj : (j.val - 2) / 2 = cj.val ∧ (j.val - 2) % 2 = sj.val := by
    have hv : j.val = 2 + 2 * cj.val + sj.val := by
      have h2 := congrArg Fin.val hjseat
      simpa using h2
    have hc := cj.isLt
    have hs := sj.isLt
    constructor <;> omega
  have hpari : (i.val - 2) / 2 = ci.val ∧ (i.val - 2) % 2 = si.val := by
    have hv : i.val = 2 + 2 * ci.val + si.val := by
      have h2 := congrArg Fin.val hiseat
      simpa using h2
    have hc := ci.isLt
    have hs := si.isLt
    constructor <;> omega
  have h1 : ThetLogos.Track1RouteB.rho1 b i j
      = ThetLogos.Track1RouteB.rho1 b
          ⟨2 + 2 * ci.val + si.val, by omega⟩
          ⟨2 + 2 * cj.val + sj.val, by omega⟩ := by
    rw [hiseat, hjseat]
  rw [h1, rho1_entry, partner_Lq_seat, partner_Lq_seat,
    pi1_entry_quarkLc]
  have hcj : (⟨(j.val - 2) / 2, by omega⟩ : Fin 3) = cj :=
    Fin.ext hparj.1
  have hci : (⟨(i.val - 2) / 2, by omega⟩ : Fin 3) = ci :=
    Fin.ext hpari.1
  rw [hcj, hci]
  by_cases hps : sj = si
  · have hpsv : sj.val = si.val := congrArg Fin.val hps
    have hpar : i.val % 2 = j.val % 2 := by
      have h1 : i.val % 2 = si.val := by omega
      have h2 : j.val % 2 = sj.val := by omega
      omega
    rw [if_pos hps, if_pos hpar]
  · have hpar : ¬ (i.val % 2 = j.val % 2) := by
      intro hh
      apply hps
      apply Fin.ext
      have h1 : i.val % 2 = si.val := by omega
      have h2 : j.val % 2 = sj.val := by omega
      omega
    rw [if_neg hps, if_neg hpar]

/-- `rho1` with quark-R row and column outside the quark-R
range vanishes (range form of the landed seat lemma). -/
theorem rho1_vanish_row_R_col_out (b : AF) {x y : Fin 32}
    (hx : 10 ≤ x.val ∧ x.val < 16)
    (hy : ¬ (10 ≤ y.val ∧ y.val < 16)) :
    ThetLogos.Track1RouteB.rho1 b x y = 0 := by
  obtain ⟨c, s, hseat⟩ := R_seat_decomp hx
  rw [hseat]
  exact rho1_R_row_vanish b c s hy

/-- `rho1` with quark-R column and row outside the quark-R
range vanishes (range form). -/
theorem rho1_vanish_col_R_row_out (b : AF) {x y : Fin 32}
    (hy : 10 ≤ y.val ∧ y.val < 16)
    (hx : ¬ (10 ≤ x.val ∧ x.val < 16)) :
    ThetLogos.Track1RouteB.rho1 b x y = 0 := by
  obtain ⟨c, s, hseat⟩ := R_seat_decomp hy
  rw [hseat]
  exact rho1_R_col_vanish b c s hx

/-- `rho1` with left-quark row and column outside the
left-quark range vanishes. -/
theorem rho1_vanish_row_Lq_col_out (b : AF) {x y : Fin 32}
    (hx : 2 ≤ x.val ∧ x.val < 8)
    (hy : ¬ (2 ≤ y.val ∧ y.val < 8)) :
    ThetLogos.Track1RouteB.rho1 b x y = 0 := by
  obtain ⟨c, s, hseat⟩ := Lq_seat_decomp hx
  rw [hseat, rho1_entry, partner_Lq_seat]
  apply pi1_vanish_col_quarkLc
  intro hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h
  all_goals
    have hv := congrArg Fin.val h
    rw [partner_val_eq] at hv
    dsimp only at hv
    split_ifs at hv <;> omega

/-- `rho1` with left-quark column and row outside the
left-quark range vanishes. -/
theorem rho1_vanish_col_Lq_row_out (b : AF) {x y : Fin 32}
    (hy : 2 ≤ y.val ∧ y.val < 8)
    (hx : ¬ (2 ≤ x.val ∧ x.val < 8)) :
    ThetLogos.Track1RouteB.rho1 b x y = 0 := by
  obtain ⟨c, s, hseat⟩ := Lq_seat_decomp hy
  rw [hseat, rho1_entry, partner_Lq_seat]
  apply pi1_vanish_quarkLc
  intro hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h
  all_goals
    have hv := congrArg Fin.val h
    rw [partner_val_eq] at hv
    dsimp only at hv
    split_ifs at hv <;> omega

/-- `E` vanishes at any entry whose column is a quark-Rc
seat: both correction factors sit in the particle half. -/
theorem E_apply_of_col_Rc (Ynu Ye Yu Yd : ℝ) (a : AF) {x t : Fin 32}
    (ht : 26 ≤ t.val ∧ t.val < 32) :
    (DF_oneGen Ynu Ye Yu Yd * swapCorr a
        - swapCorr a * DF_oneGen Ynu Ye Yu Yd) x t = 0 := by
  rw [E_entry]
  have h1 : swapCorr a (md x) t = 0 := by
    by_cases h : md x = t
    · rw [← h]
      apply swapCorr_diag_of_notin
      have hv : (md x).val = t.val := congrArg Fin.val h
      omega
    · exact swapCorr_apply_of_ne h
  have h2 : swapCorr a x (md t) = 0 := by
    by_cases h : x = md t
    · rw [← h]
      apply swapCorr_diag_of_notin
      have hv : (md t).val = t.val - 8 := md_val_Rc t (by omega)
      omega
    · exact swapCorr_apply_of_ne h
  rw [h1, h2, mul_zero, zero_mul, sub_zero]

/-- `E` vanishes at any entry whose row is a quark-Rc
seat. -/
theorem E_apply_of_row_Rc (Ynu Ye Yu Yd : ℝ) (a : AF) {x t : Fin 32}
    (hx : 26 ≤ x.val ∧ x.val < 32) :
    (DF_oneGen Ynu Ye Yu Yd * swapCorr a
        - swapCorr a * DF_oneGen Ynu Ye Yu Yd) x t = 0 := by
  rw [E_entry]
  have h1 : swapCorr a (md x) t = 0 := by
    by_cases h : md x = t
    · rw [← h]
      apply swapCorr_diag_of_notin
      have hv : (md x).val = x.val - 8 := md_val_Rc x (by omega)
      omega
    · exact swapCorr_apply_of_ne h
  have h2 : swapCorr a x (md t) = 0 := by
    by_cases h : x = md t
    · rw [← h]
      apply swapCorr_diag_of_notin
      omega
    · exact swapCorr_apply_of_ne h
  rw [h1, h2, mul_zero, zero_mul, sub_zero]

/-- The `pi1` commutator vanishes at any entry whose
column is a quark-Rc seat (landed particle/anti and
anti/anti vanishings). -/
theorem comm_apply_of_col_Rc (Ynu Ye Yu Yd : ℝ) (a : AF) {x t : Fin 32}
    (ht : 26 ≤ t.val ∧ t.val < 32) :
    (DF_oneGen Ynu Ye Yu Yd * pi1 a
        - pi1 a * DF_oneGen Ynu Ye Yu Yd) x t = 0 := by
  by_cases hx : x.val < 16
  · exact comm_particle_anti Ynu Ye Yu Yd a hx (by omega)
  · exact comm_anti_anti Ynu Ye Yu Yd a (by omega) (by omega)

/-- The `pi1` commutator vanishes at any entry whose row
is a quark-Rc seat. -/
theorem comm_apply_of_row_Rc (Ynu Ye Yu Yd : ℝ) (a : AF) {x t : Fin 32}
    (hx : 26 ≤ x.val ∧ x.val < 32) :
    (DF_oneGen Ynu Ye Yu Yd * pi1 a
        - pi1 a * DF_oneGen Ynu Ye Yu Yd) x t = 0 := by
  by_cases ht : t.val < 16
  · exact comm_anti_particle Ynu Ye Yu Yd a (by omega) ht
  · exact comm_anti_anti Ynu Ye Yu Yd a (by omega) (by omega)

/-! ## §6c. First-order: brackets and assembly -/

/-- Product entry: `E` times `rho1` collapses to the
matched term. -/
theorem E_mul_rho1_entry (Ynu Ye Yu Yd : ℝ) (a b : AF) (i j : Fin 32) :
    ((DF_oneGen Ynu Ye Yu Yd * swapCorr a
        - swapCorr a * DF_oneGen Ynu Ye Yu Yd)
      * ThetLogos.Track1RouteB.rho1 b) i j
      = (DF_oneGen Ynu Ye Yu Yd * swapCorr a
          - swapCorr a * DF_oneGen Ynu Ye Yu Yd) i (md i)
        * ThetLogos.Track1RouteB.rho1 b (md i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (md i)]
  · intro k _ hk
    rw [E_apply_of_ne_md Ynu Ye Yu Yd a hk, zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ (md i)) hcon

/-- Product entry: `rho1` times `E` collapses to the
matched term. -/
theorem rho1_mul_E_entry (Ynu Ye Yu Yd : ℝ) (a b : AF) (i j : Fin 32) :
    (ThetLogos.Track1RouteB.rho1 b
      * (DF_oneGen Ynu Ye Yu Yd * swapCorr a
        - swapCorr a * DF_oneGen Ynu Ye Yu Yd)) i j
      = ThetLogos.Track1RouteB.rho1 b i (md j)
        * (DF_oneGen Ynu Ye Yu Yd * swapCorr a
          - swapCorr a * DF_oneGen Ynu Ye Yu Yd) (md j) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (md j)]
  · intro k _ hk
    have hne : j ≠ md k := by
      intro hh
      apply hk
      have h2 : md j = md (md k) := congrArg md hh
      rw [md_involutive] at h2
      exact h2.symm
    rw [E_apply_of_ne_md Ynu Ye Yu Yd a hne, mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ (md j)) hcon

/-- Bracket `[C1, rho1] = 0` entrywise: the landed
`pi1_first_order`. -/
theorem bracket_C1_rho1 (Ynu Ye Yu Yd : ℝ) (a b : AF) (i j : Fin 32) :
    ((DF_oneGen Ynu Ye Yu Yd * pi1 a
        - pi1 a * DF_oneGen Ynu Ye Yu Yd)
      * ThetLogos.Track1RouteB.rho1 b) i j
      = (ThetLogos.Track1RouteB.rho1 b
        * (DF_oneGen Ynu Ye Yu Yd * pi1 a
          - pi1 a * DF_oneGen Ynu Ye Yu Yd)) i j := by
  have h := pi1_first_order Ynu Ye Yu Yd a b i j
  rwa [Matrix.sub_apply, sub_eq_zero] at h

/-- Bracket `[C1, S'] = 0`, left entry: the commutator
vanishes on quark-Rc columns. -/
theorem bracket_C1_S' (Ynu Ye Yu Yd : ℝ) (a b : AF) (i j : Fin 32) :
    ((DF_oneGen Ynu Ye Yu Yd * pi1 a
        - pi1 a * DF_oneGen Ynu Ye Yu Yd) * swapCorrOp b) i j = 0 := by
  rw [mul_swapCorrOp_entry]
  by_cases hj : 26 ≤ j.val ∧ j.val < 32
  · rw [comm_apply_of_col_Rc Ynu Ye Yu Yd a hj, zero_mul]
  · rw [swapCorrOp_diag_of_notin b hj, mul_zero]

/-- Bracket `[C1, S'] = 0`, right entry. -/
theorem bracket_S'_C1 (Ynu Ye Yu Yd : ℝ) (a b : AF) (i j : Fin 32) :
    (swapCorrOp b * (DF_oneGen Ynu Ye Yu Yd * pi1 a
        - pi1 a * DF_oneGen Ynu Ye Yu Yd)) i j = 0 := by
  rw [swapCorrOp_mul_entry]
  by_cases hi : 26 ≤ i.val ∧ i.val < 32
  · rw [comm_apply_of_row_Rc Ynu Ye Yu Yd a hi, mul_zero]
  · rw [swapCorrOp_diag_of_notin b hi, zero_mul]

/-- Bracket `[E, S'] = 0`, left entry: `E` vanishes on
quark-Rc columns. -/
theorem bracket_E_S' (Ynu Ye Yu Yd : ℝ) (a b : AF) (i j : Fin 32) :
    ((DF_oneGen Ynu Ye Yu Yd * swapCorr a
        - swapCorr a * DF_oneGen Ynu Ye Yu Yd) * swapCorrOp b) i j
      = 0 := by
  rw [mul_swapCorrOp_entry]
  by_cases hj : 26 ≤ j.val ∧ j.val < 32
  · rw [E_apply_of_col_Rc Ynu Ye Yu Yd a hj, zero_mul]
  · rw [swapCorrOp_diag_of_notin b hj, mul_zero]

/-- Bracket `[E, S'] = 0`, right entry. -/
theorem bracket_S'_E (Ynu Ye Yu Yd : ℝ) (a b : AF) (i j : Fin 32) :
    (swapCorrOp b * (DF_oneGen Ynu Ye Yu Yd * swapCorr a
        - swapCorr a * DF_oneGen Ynu Ye Yu Yd)) i j = 0 := by
  rw [swapCorrOp_mul_entry]
  by_cases hi : 26 ≤ i.val ∧ i.val < 32
  · rw [E_apply_of_row_Rc Ynu Ye Yu Yd a hi, mul_zero]
  · rw [swapCorrOp_diag_of_notin b hi, zero_mul]

/-- Bracket `[E, rho1] = 0` entrywise. Off the quark band
everything vanishes by support; on the two mixed
(left-quark, quark-R) rectangles the identity is the
colour-sum collapse: `rho1`'s colour entries at fixed
isospin agree on the two sides, and the scalar
coefficients — the Yukawa weight and the correction's
diagonal, both colour-blind and isospin-only — match. -/
theorem bracket_E_rho1 (Ynu Ye Yu Yd : ℝ) (a b : AF) (i j : Fin 32) :
    ((DF_oneGen Ynu Ye Yu Yd * swapCorr a
        - swapCorr a * DF_oneGen Ynu Ye Yu Yd)
      * ThetLogos.Track1RouteB.rho1 b) i j
      = (ThetLogos.Track1RouteB.rho1 b
        * (DF_oneGen Ynu Ye Yu Yd * swapCorr a
          - swapCorr a * DF_oneGen Ynu Ye Yu Yd)) i j := by
  rw [E_mul_rho1_entry, rho1_mul_E_entry]
  by_cases hiLq : 2 ≤ i.val ∧ i.val < 8
  · by_cases hjS : 10 ≤ j.val ∧ j.val < 16
    · -- Collapse on (Lq, R)
      obtain ⟨ci, si, hiseat⟩ := Lq_seat_decomp hiLq
      obtain ⟨cj, sj, hjseat⟩ := R_seat_decomp hjS
      have hmdi : md i = ⟨10 + 2 * ci.val + si.val, by omega⟩ := by
        rw [hiseat]; exact md_Lq_seat ci si
      have hmdj : md j = ⟨2 + 2 * cj.val + sj.val, by omega⟩ := by
        rw [hjseat]; exact md_R_seat cj sj
      have hiv : i.val = 2 + 2 * ci.val + si.val := by
        have h := congrArg Fin.val hiseat; simpa using h
      have hjv : j.val = 10 + 2 * cj.val + sj.val := by
        have h := congrArg Fin.val hjseat; simpa using h
      have hmdv_i : (md i).val = 10 + 2 * ci.val + si.val := by
        have h := congrArg Fin.val hmdi; simpa using h
      have hmdv_j : (md j).val = 2 + 2 * cj.val + sj.val := by
        have h := congrArg Fin.val hmdj; simpa using h
      have hc_i := ci.isLt
      have hs_i := si.isLt
      have hc_j := cj.isLt
      have hs_j := sj.isLt
      have hE1 : (DF_oneGen Ynu Ye Yu Yd * swapCorr a
            - swapCorr a * DF_oneGen Ynu Ye Yu Yd) i (md i)
          = Dval Ynu Ye Yu Yd i * swapCorr a (md i) (md i) := by
        have hSi : swapCorr a i i = 0 :=
          swapCorr_diag_of_notin a (by omega)
        rw [E_pair, hSi, sub_zero]
      have hE2 : (DF_oneGen Ynu Ye Yu Yd * swapCorr a
            - swapCorr a * DF_oneGen Ynu Ye Yu Yd) (md j) j
          = Dval Ynu Ye Yu Yd j * swapCorr a j j := by
        have h := E_pair Ynu Ye Yu Yd a (md j)
        have hS : swapCorr a (md j) (md j) = 0 :=
          swapCorr_diag_of_notin a (by omega)
        rw [md_involutive, Dval_md, hS, sub_zero] at h
        exact h
      have hR1 : ThetLogos.Track1RouteB.rho1 b (md i) j
          = if si = sj then star (b.color cj ci) else 0 := by
        have h := rho1_R_block (i := md i) (j := j) b (by omega) hjS
        have hp1 : (md i).val % 2 = si.val := by omega
        have hp2 : j.val % 2 = sj.val := by omega
        have hidx1 : (⟨(j.val - 10) / 2, by omega⟩ : Fin 3) = cj :=
          Fin.ext (by show (j.val - 10) / 2 = cj.val; omega)
        have hidx2 : (⟨((md i).val - 10) / 2, by omega⟩ : Fin 3)
            = ci := Fin.ext (by
              show ((md i).val - 10) / 2 = ci.val; omega)
        rw [hp1, hp2, hidx1, hidx2] at h
        by_cases hst : si = sj
        · rw [if_pos (congrArg Fin.val hst)] at h
          rwa [if_pos hst]
        · rw [if_neg (fun hh => hst (Fin.ext hh))] at h
          rwa [if_neg hst]
      have hR2 : ThetLogos.Track1RouteB.rho1 b i (md j)
          = if si = sj then star (b.color cj ci) else 0 := by
        have h := rho1_Lq_block (i := i) (j := md j) b hiLq (by omega)
        have hp1 : i.val % 2 = si.val := by omega
        have hp2 : (md j).val % 2 = sj.val := by omega
        have hidx1 : (⟨((md j).val - 2) / 2, by omega⟩ : Fin 3)
            = cj := Fin.ext (by
              show ((md j).val - 2) / 2 = cj.val; omega)
        have hidx2 : (⟨(i.val - 2) / 2, by omega⟩ : Fin 3) = ci :=
          Fin.ext (by show (i.val - 2) / 2 = ci.val; omega)
        rw [hp1, hp2, hidx1, hidx2] at h
        by_cases hst : si = sj
        · rw [if_pos (congrArg Fin.val hst)] at h
          rwa [if_pos hst]
        · rw [if_neg (fun hh => hst (Fin.ext hh))] at h
          rwa [if_neg hst]
      have hD1 : Dval Ynu Ye Yu Yd i
          = if si = 0 then (Yu : ℂ) else (Yd : ℂ) := by
        rw [hiseat]; exact Dval_quarkL Ynu Ye Yu Yd ci si
      have hD2 : Dval Ynu Ye Yu Yd j
          = if sj = 0 then (Yu : ℂ) else (Yd : ℂ) := by
        rw [hjseat]; exact Dval_quarkR Ynu Ye Yu Yd cj sj
      have hS1 : swapCorr a (md i) (md i)
          = if si = 0 then star a.u1 - a.u1
            else a.u1 - star a.u1 := by
        have h := swapCorr_diag_R (i := md i) a (by omega)
        have hp : (md i).val % 2 = si.val := by omega
        rw [hp] at h
        by_cases hsi : si = 0
        · rw [if_pos (by
            have hv := congrArg Fin.val hsi; simpa using hv)] at h
          rwa [if_pos hsi]
        · rw [if_neg (show ¬ (si.val = 0) from fun hh => hsi (Fin.ext hh))] at h
          rwa [if_neg hsi]
      have hS2 : swapCorr a j j
          = if sj = 0 then star a.u1 - a.u1
            else a.u1 - star a.u1 := by
        have h := swapCorr_diag_R a hjS
        have hp : j.val % 2 = sj.val := by omega
        rw [hp] at h
        by_cases hsj : sj = 0
        · rw [if_pos (by
            have hv := congrArg Fin.val hsj; simpa using hv)] at h
          rwa [if_pos hsj]
        · rw [if_neg (show ¬ (sj.val = 0) from fun hh => hsj (Fin.ext hh))] at h
          rwa [if_neg hsj]
      rw [hE1, hE2, hR1, hR2, hD1, hD2, hS1, hS2]
      by_cases hst : si = sj
      · by_cases hsi : si = 0
        · have hsj : sj = 0 := by rw [← hst]; exact hsi
          rw [if_pos hst, if_pos hsi, if_pos hsi, if_pos hsj, if_pos hsj]
          exact mul_comm _ _
        · have hsj : ¬ sj = 0 := fun h => hsi (by rw [hst]; exact h)
          rw [if_pos hst, if_neg hsi, if_neg hsi, if_neg hsj, if_neg hsj]
          exact mul_comm _ _
      · rw [if_neg hst, mul_zero, zero_mul]
    · by_cases hjLq : 2 ≤ j.val ∧ j.val < 8
      · have h1 : ThetLogos.Track1RouteB.rho1 b (md i) j = 0 := by
          apply rho1_vanish_col_Lq_row_out b hjLq
          have hv : (md i).val = i.val + 8 := md_val_L i (by omega)
          omega
        have h2 : ThetLogos.Track1RouteB.rho1 b i (md j) = 0 := by
          apply rho1_vanish_col_R_row_out b _ (by omega)
          have hv : (md j).val = j.val + 8 := md_val_L j (by omega)
          omega
        rw [h1, mul_zero, h2, zero_mul]
      · have h1 : ThetLogos.Track1RouteB.rho1 b (md i) j = 0 := by
          apply rho1_vanish_row_R_col_out b _ hjS
          have hv : (md i).val = i.val + 8 := md_val_L i (by omega)
          omega
        have hE : (DF_oneGen Ynu Ye Yu Yd * swapCorr a
              - swapCorr a * DF_oneGen Ynu Ye Yu Yd) (md j) j = 0 := by
          have h1' : ¬ (2 ≤ (md j).val ∧ (md j).val < 8) := by
            rw [md_val]; split_ifs <;> omega
          have h2' : ¬ (10 ≤ (md j).val ∧ (md j).val < 16) := by
            rw [md_val]; split_ifs <;> omega
          have h := E_pair_zero Ynu Ye Yu Yd a (x := md j) ⟨h1', h2'⟩
          rwa [md_involutive] at h
        rw [h1, mul_zero, hE, mul_zero]
  · by_cases hiS : 10 ≤ i.val ∧ i.val < 16
    · by_cases hjLq : 2 ≤ j.val ∧ j.val < 8
      · -- Collapse on (R, Lq), mirrored
        obtain ⟨ci, si, hiseat⟩ := R_seat_decomp hiS
        obtain ⟨cj, sj, hjseat⟩ := Lq_seat_decomp hjLq
        have hmdi : md i = ⟨2 + 2 * ci.val + si.val, by omega⟩ := by
          rw [hiseat]; exact md_R_seat ci si
        have hmdj : md j = ⟨10 + 2 * cj.val + sj.val, by omega⟩ := by
          rw [hjseat]; exact md_Lq_seat cj sj
        have hiv : i.val = 10 + 2 * ci.val + si.val := by
          have h := congrArg Fin.val hiseat; simpa using h
        have hjv : j.val = 2 + 2 * cj.val + sj.val := by
          have h := congrArg Fin.val hjseat; simpa using h
        have hmdv_i : (md i).val = 2 + 2 * ci.val + si.val := by
          have h := congrArg Fin.val hmdi; simpa using h
        have hmdv_j : (md j).val = 10 + 2 * cj.val + sj.val := by
          have h := congrArg Fin.val hmdj; simpa using h
        have hc_i := ci.isLt
        have hs_i := si.isLt
        have hc_j := cj.isLt
        have hs_j := sj.isLt
        have hE1 : (DF_oneGen Ynu Ye Yu Yd * swapCorr a
              - swapCorr a * DF_oneGen Ynu Ye Yu Yd) i (md i)
            = Dval Ynu Ye Yu Yd i * (0 - swapCorr a i i) := by
          have hS : swapCorr a (md i) (md i) = 0 :=
            swapCorr_diag_of_notin a (by omega)
          rw [E_pair, hS]
        have hE2 : (DF_oneGen Ynu Ye Yu Yd * swapCorr a
              - swapCorr a * DF_oneGen Ynu Ye Yu Yd) (md j) j
            = Dval Ynu Ye Yu Yd j
              * (0 - swapCorr a (md j) (md j)) := by
          have h := E_pair Ynu Ye Yu Yd a (md j)
          have hS : swapCorr a j j = 0 :=
            swapCorr_diag_of_notin a (by omega)
          rw [md_involutive, Dval_md, hS] at h
          exact h
        have hR1 : ThetLogos.Track1RouteB.rho1 b (md i) j
            = if si = sj then star (b.color cj ci) else 0 := by
          have h := rho1_Lq_block (i := md i) (j := j) b (by omega) hjLq
          have hp1 : (md i).val % 2 = si.val := by omega
          have hp2 : j.val % 2 = sj.val := by omega
          have hidx1 : (⟨(j.val - 2) / 2, by omega⟩ : Fin 3) = cj :=
            Fin.ext (by show (j.val - 2) / 2 = cj.val; omega)
          have hidx2 : (⟨((md i).val - 2) / 2, by omega⟩ : Fin 3)
              = ci := Fin.ext (by
                show ((md i).val - 2) / 2 = ci.val; omega)
          rw [hp1, hp2, hidx1, hidx2] at h
          by_cases hst : si = sj
          · rw [if_pos (congrArg Fin.val hst)] at h
            rwa [if_pos hst]
          · rw [if_neg (fun hh => hst (Fin.ext hh))] at h
            rwa [if_neg hst]
        have hR2 : ThetLogos.Track1RouteB.rho1 b i (md j)
            = if si = sj then star (b.color cj ci) else 0 := by
          have h := rho1_R_block (i := i) (j := md j) b hiS (by omega)
          have hp1 : i.val % 2 = si.val := by omega
          have hp2 : (md j).val % 2 = sj.val := by omega
          have hidx1 : (⟨((md j).val - 10) / 2, by omega⟩ : Fin 3)
              = cj := Fin.ext (by
                show ((md j).val - 10) / 2 = cj.val; omega)
          have hidx2 : (⟨(i.val - 10) / 2, by omega⟩ : Fin 3) = ci :=
            Fin.ext (by show (i.val - 10) / 2 = ci.val; omega)
          rw [hp1, hp2, hidx1, hidx2] at h
          by_cases hst : si = sj
          · rw [if_pos (congrArg Fin.val hst)] at h
            rwa [if_pos hst]
          · rw [if_neg (fun hh => hst (Fin.ext hh))] at h
            rwa [if_neg hst]
        have hD1 : Dval Ynu Ye Yu Yd i
            = if si = 0 then (Yu : ℂ) else (Yd : ℂ) := by
          rw [hiseat]; exact Dval_quarkR Ynu Ye Yu Yd ci si
        have hD2 : Dval Ynu Ye Yu Yd j
            = if sj = 0 then (Yu : ℂ) else (Yd : ℂ) := by
          rw [hjseat]; exact Dval_quarkL Ynu Ye Yu Yd cj sj
        have hS1 : swapCorr a i i
            = if si = 0 then star a.u1 - a.u1
              else a.u1 - star a.u1 := by
          have h := swapCorr_diag_R a hiS
          have hp : i.val % 2 = si.val := by omega
          rw [hp] at h
          by_cases hsi : si = 0
          · rw [if_pos (by
              have hv := congrArg Fin.val hsi; simpa using hv)] at h
            rwa [if_pos hsi]
          · rw [if_neg (show ¬ (si.val = 0) from fun hh => hsi (Fin.ext hh))] at h
            rwa [if_neg hsi]
        have hS2 : swapCorr a (md j) (md j)
            = if sj = 0 then star a.u1 - a.u1
              else a.u1 - star a.u1 := by
          have h := swapCorr_diag_R (i := md j) a (by omega)
          have hp : (md j).val % 2 = sj.val := by omega
          rw [hp] at h
          by_cases hsj : sj = 0
          · rw [if_pos (by
              have hv := congrArg Fin.val hsj; simpa using hv)] at h
            rwa [if_pos hsj]
          · rw [if_neg (show ¬ (sj.val = 0) from fun hh => hsj (Fin.ext hh))] at h
            rwa [if_neg hsj]
        rw [hE1, hE2, hR1, hR2, hD1, hD2, hS1, hS2]
        by_cases hst : si = sj
        · by_cases hsi : si = 0
          · have hsj : sj = 0 := by rw [← hst]; exact hsi
            rw [if_pos hst, if_pos hsi, if_pos hsi, if_pos hsj, if_pos hsj]
            exact mul_comm _ _
          · have hsj : ¬ sj = 0 := fun h => hsi (by rw [hst]; exact h)
            rw [if_pos hst, if_neg hsi, if_neg hsi, if_neg hsj, if_neg hsj]
            exact mul_comm _ _
        · rw [if_neg hst, mul_zero, zero_mul]
      · by_cases hjS : 10 ≤ j.val ∧ j.val < 16
        · have h1 : ThetLogos.Track1RouteB.rho1 b (md i) j = 0 := by
            apply rho1_vanish_col_R_row_out b hjS
            have hv : (md i).val = i.val - 8 :=
              md_val_R i ⟨by omega, by omega⟩
            omega
          have h2 : ThetLogos.Track1RouteB.rho1 b i (md j) = 0 := by
            apply rho1_vanish_col_Lq_row_out b _ (by omega)
            have hv : (md j).val = j.val - 8 :=
              md_val_R j ⟨by omega, by omega⟩
            omega
          rw [h1, mul_zero, h2, zero_mul]
        · have h1 : ThetLogos.Track1RouteB.rho1 b (md i) j = 0 := by
            apply rho1_vanish_row_Lq_col_out b _ hjLq
            have hv : (md i).val = i.val - 8 :=
              md_val_R i ⟨by omega, by omega⟩
            omega
          have hE : (DF_oneGen Ynu Ye Yu Yd * swapCorr a
                - swapCorr a * DF_oneGen Ynu Ye Yu Yd) (md j) j
              = 0 := by
            have h1' : ¬ (2 ≤ (md j).val ∧ (md j).val < 8) := by
              rw [md_val]; split_ifs <;> omega
            have h2' : ¬ (10 ≤ (md j).val ∧ (md j).val < 16) := by
              rw [md_val]; split_ifs <;> omega
            have h := E_pair_zero Ynu Ye Yu Yd a (x := md j) ⟨h1', h2'⟩
            rwa [md_involutive] at h
          rw [h1, mul_zero, hE, mul_zero]
    · have hE0 : (DF_oneGen Ynu Ye Yu Yd * swapCorr a
          - swapCorr a * DF_oneGen Ynu Ye Yu Yd) i (md i) = 0 :=
        E_pair_zero Ynu Ye Yu Yd a ⟨hiLq, hiS⟩
      by_cases hjLq : 2 ≤ j.val ∧ j.val < 8
      · have h2 : ThetLogos.Track1RouteB.rho1 b i (md j) = 0 := by
          apply rho1_vanish_col_R_row_out b _ hiS
          have hv : (md j).val = j.val + 8 := md_val_L j (by omega)
          omega
        rw [hE0, zero_mul, h2, zero_mul]
      · by_cases hjS : 10 ≤ j.val ∧ j.val < 16
        · have h2 : ThetLogos.Track1RouteB.rho1 b i (md j) = 0 := by
            apply rho1_vanish_col_Lq_row_out b _ hiLq
            have hv : (md j).val = j.val - 8 :=
              md_val_R j ⟨by omega, by omega⟩
            omega
          rw [hE0, zero_mul, h2, zero_mul]
        · have hE : (DF_oneGen Ynu Ye Yu Yd * swapCorr a
                - swapCorr a * DF_oneGen Ynu Ye Yu Yd) (md j) j
              = 0 := by
            have h1' : ¬ (2 ≤ (md j).val ∧ (md j).val < 8) := by
              rw [md_val]; split_ifs <;> omega
            have h2' : ¬ (10 ≤ (md j).val ∧ (md j).val < 16) := by
              rw [md_val]; split_ifs <;> omega
            have h := E_pair_zero Ynu Ye Yu Yd a (x := md j) ⟨h1', h2'⟩
            rwa [md_involutive] at h
          rw [hE0, zero_mul, hE, mul_zero]

/-- First-order for the uniform swap: the total commutator
splits as `C1 + E` against `rho1 + S'`, and all four
brackets vanish (the `pi1` one by the landed
`pi1_first_order`). -/
theorem allSwap_first_order (Ynu Ye Yu Yd : ℝ) (a b : AF)
    (i j : Fin 32) :
    ((DF_oneGen Ynu Ye Yu Yd * orbitRep allSwapBits a
        - orbitRep allSwapBits a * DF_oneGen Ynu Ye Yu Yd)
      * piOp (orbitRep allSwapBits b)
      - piOp (orbitRep allSwapBits b)
        * (DF_oneGen Ynu Ye Yu Yd * orbitRep allSwapBits a
          - orbitRep allSwapBits a * DF_oneGen Ynu Ye Yu Yd)) i j
      = 0 := by
  have hC : DF_oneGen Ynu Ye Yu Yd * orbitRep allSwapBits a
        - orbitRep allSwapBits a * DF_oneGen Ynu Ye Yu Yd
      = (DF_oneGen Ynu Ye Yu Yd * pi1 a
          - pi1 a * DF_oneGen Ynu Ye Yu Yd)
        + (DF_oneGen Ynu Ye Yu Yd * swapCorr a
          - swapCorr a * DF_oneGen Ynu Ye Yu Yd) := by
    rw [allSwap_eq]
    noncomm_ring
  rw [hC, rhoAllSwap_eq]
  simp only [add_mul, mul_add, Matrix.sub_apply, Matrix.add_apply]
  rw [bracket_C1_S' Ynu Ye Yu Yd a b i j,
    bracket_E_S' Ynu Ye Yu Yd a b i j,
    bracket_S'_C1 Ynu Ye Yu Yd a b i j,
    bracket_S'_E Ynu Ye Yu Yd a b i j,
    bracket_C1_rho1 Ynu Ye Yu Yd a b i j,
    bracket_E_rho1 Ynu Ye Yu Yd a b i j]
  simp only [add_zero, zero_add, sub_self]

/-! ## §7. Assembly: the base holds, K-CLS-2 fires -/

/-- **The uniform triple swap satisfies `DialOneBase`** —
the decision of this brick: outcome (a), the base HOLDS at
the all-swap point, clause by clause (§§3–6). -/
theorem base_allSwap : DialOneBase (orbitRep allSwapBits) :=
  ⟨allSwap_afMul,
   allSwap_afAdd,
   allSwap_afStar,
   allSwap_one,
   allSwap_zero,
   allSwap_injective,
   allSwap_grading,
   fun a b => allSwap_order_zero a b,
   fun Ynu Ye Yu Yd a b i j => allSwap_first_order Ynu Ye Yu Yd a b i j,
   ⟨3, -1, by norm_num, fun t => by
     rw [allSwap_det_gen, pi1_det_gen]
     norm_num⟩⟩

/-- **K-CLS-2 FIRES**: the all-swap point is a member of
the strengthened family — the toggle orbit has a second
strengthened point besides `pi1` itself. -/
theorem allSwap_mem_strengthened :
    DialOneStrengthenedFam (orbitRep allSwapBits) :=
  strengthened_allSwap_iff_base.mpr base_allSwap

/-- The orbit has a strengthened point other than the
identity toggle. -/
theorem orbit_two_points :
    ∃ b : Fin 4 → Bool, b ≠ (fun _ => false)
      ∧ DialOneStrengthenedFam (orbitRep b) :=
  ⟨allSwapBits, by decide, allSwap_mem_strengthened⟩

/-- **The completed toggle-orbit classification**: a
toggle point is in the strengthened family iff it is the
identity toggle or the uniform triple swap. -/
theorem orbit_classification_complete (b : Fin 4 → Bool) :
    DialOneStrengthenedFam (orbitRep b)
      ↔ b = (fun _ => false) ∨ b = allSwapBits := by
  by_cases hb : b = allSwapBits
  · subst hb
    constructor
    · intro _
      exact Or.inr rfl
    · intro _
      exact allSwap_mem_strengthened
  · rw [strengthened_orbitRep_iff_of_ne_allSwap hb]
    constructor
    · intro h
      exact Or.inl h
    · intro h
      rcases h with h | h
      · exact h
      · exact absurd h hb

/-! ## §8. Weight read-back: the new point's weights differ -/

/-- The diagonal value of `pi1`'s shadow at the literal
quark-Rc seat `26`: `star μ`. -/
theorem pi1Diag_Rc26 (lam μ : ℂ) :
    pi1Diag lam μ ⟨26, by omega⟩ = star μ := by
  show pi1DiagVal lam μ 26 = star μ
  unfold pi1DiagVal
  rw [if_neg (by norm_num), if_neg (by norm_num),
    if_neg (by norm_num), if_neg (by norm_num),
    if_neg (by norm_num), if_neg (by norm_num),
    if_neg (by norm_num)]

/-- The partner of the first up seat is the literal `26`. -/
theorem partner_uSeat_zero :
    partner (uSeat (0 : Fin 3)) = ⟨26, by omega⟩ := by
  have h := partner_uSeat (0 : Fin 3)
  simpa using h

/-- The swap permutation fixes the literal seat `26`. -/
theorem swapPerm_26 : swapPerm ⟨26, by omega⟩ = ⟨26, by omega⟩ :=
  swapPerm_of_ne (fun c => ⟨fun h => by
    have hv := congrArg Fin.val h
    have h0 : (⟨26, by omega⟩ : Fin 32).val = 26 := rfl
    have h1 : (uSeat c).val = 10 + 2 * c.val := rfl
    have hc := c.isLt
    omega, fun h => by
    have hv := congrArg Fin.val h
    have h0 : (⟨26, by omega⟩ : Fin 32).val = 26 := rfl
    have h1 : (dSeat c).val = 11 + 2 * c.val := rfl
    have hc := c.isLt
    omega⟩)

/-- Diagonal lifted entry: a diagonal matrix times its
opposite picks out the two matched diagonal values. -/
theorem diagonal_lifted_entry (w : Fin 32 → ℂ) (s : Fin 32) :
    (Matrix.diagonal w * piOp (Matrix.diagonal w)) s s
      = w s * w (partner s) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · rw [Matrix.diagonal_apply_eq, piOp_apply,
      Matrix.diagonal_apply_eq]
  · intro k _ hk
    rw [Matrix.diagonal_apply_ne w (Ne.symm hk), zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ s) hcon

/-- **The all-swap lifted entry at the first up seat**:
the swap moves the seat to its down partner, so the
lifted character is `exp (-(α + β) t I)` — against `pi1`'s
`exp ((α - β) t I)`. -/
theorem allSwap_lifted_uSeat (α β : ℤ) (t : ℝ) :
    (orbitRep allSwapBits (u1ParamGen α β t)
      * piOp (orbitRep allSwapBits (u1ParamGen α β t)))
        (uSeat (0 : Fin 3)) (uSeat (0 : Fin 3))
      = Complex.exp (((-(α + β) : ℤ) : ℂ) * (t : ℂ)
          * Complex.I) := by
  rw [allSwap_eq_diagonal, diagonal_lifted_entry]
  show pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
        (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I)))
        (swapPerm (uSeat (0 : Fin 3)))
      * pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
        (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I)))
        (swapPerm (partner (uSeat (0 : Fin 3)))) = _
  rw [swapPerm_uSeat, pi1Diag_dSeat, partner_uSeat_zero, swapPerm_26,
    pi1Diag_Rc26, star_exp_int, star_exp_int, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The common weight vector at the first up seat is `4`
(the `pi1` lifted weight there). -/
theorem commonWeightVector_uSeat_zero :
    commonWeightVector (uSeat (0 : Fin 3)) = 4 := by decide

/-- Imaginary parts of an integral character relation:
if `x * I = n * (2π * I)` in `ℂ` with `x n : ℤ`, then
`x = n * 2π` in `ℝ`. -/
theorem im_int_mul_I (x n : ℤ)
    (h : ((x : ℂ)) * Complex.I
      = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) :
    (x : ℝ) = (n : ℝ) * (2 * Real.pi) := by
  have h2 : (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
      = (n : ℂ) * (((2 * Real.pi : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h2] at h
  have hIm := congrArg Complex.im h
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.intCast_re, Complex.intCast_im,
    Complex.ofReal_re, Complex.ofReal_im] at hIm
  linarith [hIm]

/-- Character rigidity: a pure integral character agreeing
with the weight-`4` character at every `t` has weight `4`
(otherwise `π` would be rational). -/
theorem exp_char_rigidity {w : ℤ} (hw : w ≠ 4)
    (h : ∀ t : ℝ, Complex.exp ((w : ℂ) * (t : ℂ) * Complex.I)
      = Complex.exp ((4 : ℂ) * (t : ℂ) * Complex.I)) : False := by
  have h1 := h 1
  simp only [Complex.ofReal_one, mul_one] at h1
  have h2 : Complex.exp (((w - 4 : ℤ) : ℂ) * Complex.I) = 1 := by
    have hsub : Complex.exp ((w : ℂ) * Complex.I
        - (4 : ℂ) * Complex.I) = 1 := by
      rw [Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
    have h4 : (((w - 4 : ℤ) : ℂ)) * Complex.I
        = (w : ℂ) * Complex.I - (4 : ℂ) * Complex.I := by
      push_cast
      ring
    rwa [← h4] at hsub
  obtain ⟨n, hn⟩ := (Complex.exp_eq_one_iff).mp h2
  have him : ((w - 4 : ℤ) : ℝ) = (n : ℝ) * (2 * Real.pi) :=
    im_int_mul_I (w - 4) n hn
  by_cases hn0 : n = 0
  · rw [hn0] at him
    simp at him
    have h5 : w = 4 := by
      exact_mod_cast (show (w : ℝ) = (4 : ℝ) by linarith [him])
    exact hw h5
  · apply irrational_pi.ne_rational (w - 4) (2 * n)
    rw [eq_div_iff (by simp [hn0] : ((2 * n : ℤ) : ℝ) ≠ 0)]
    push_cast
    push_cast at him
    linarith [him]

/-- **Weight read-back**: the all-swap point does NOT
carry the common weight vector. Its strengthened-set
membership (§7) therefore does not realize
`commonWeightVector` at a second point: at the first up
seat its lifted character along any primitive unimodular
det-1 direction is `exp (-(α + β) t I)` with
`(α, β) = ±(3, -1)` forced by the determinant, i.e.
exponent `∓2`, never the common value `4`. Grade W
(`WeightQuestionW`) is untouched: this is one point's
read-back, not the question's resolution. -/
theorem allSwap_not_weightAt_common :
    ¬ weightAt (orbitRep allSwapBits) commonWeightVector := by
  rintro ⟨α, β, hgcd, hdet, hlift⟩
  have hdet2 : Complex.exp (((-4 * α + -12 * β : ℤ) : ℂ)
      * Complex.I) = 1 := by
    have h := hdet 1
    rw [allSwap_det_gen, pi1_det_gen] at h
    simpa only [Complex.ofReal_one, one_mul] using h
  obtain ⟨n, hn⟩ := (Complex.exp_eq_one_iff).mp hdet2
  have him : ((-4 * α + -12 * β : ℤ) : ℝ)
      = (n : ℝ) * (2 * Real.pi) :=
    im_int_mul_I (-4 * α + -12 * β) n hn
  have hαβ : α = -3 * β := by
    by_cases hn0 : n = 0
    · rw [hn0] at him
      simp at him
      have h5 : -4 * α + -12 * β = 0 := by
        have hR : ((-4 * α + -12 * β : ℤ) : ℝ) = 0 := by
          push_cast
          linarith [him]
        exact_mod_cast hR
      omega
    · exfalso
      apply irrational_pi.ne_rational (-4 * α + -12 * β) (2 * n)
      rw [eq_div_iff (by simp [hn0] : ((2 * n : ℤ) : ℝ) ≠ 0)]
      push_cast
      push_cast at him
      linarith [him]
  have hβ : β = 1 ∨ β = -1 := by
    have h1 : β.natAbs = 1 := by
      have hα : α.natAbs = 3 * β.natAbs := by
        rw [hαβ]
        simp [Int.natAbs_mul]
      have hdvd : β.natAbs ∣ 1 := by
        rw [← hgcd, hα]
        exact dvd_gcd (dvd_mul_left _ _) dvd_rfl
      exact Nat.dvd_one.mp hdvd
    exact Int.isUnit_iff.mp (Int.isUnit_iff_natAbs_eq.mpr h1)
  have hentry : ∀ t : ℝ,
      Complex.exp (((-(α + β) : ℤ) : ℂ) * (t : ℂ) * Complex.I)
        = Complex.exp (((4 : ℤ) : ℂ) * (t : ℂ) * Complex.I) := by
    intro t
    have h := hlift t (uSeat (0 : Fin 3))
    rwa [commonWeightVector_uSeat_zero, allSwap_lifted_uSeat α β t]
      at h
  rcases hβ with hβ1 | hβ1
  · have hα : α = -3 := by omega
    apply exp_char_rigidity (w := 2) (by norm_num)
    intro t
    have h := hentry t
    rwa [show ((-(α + β) : ℤ) : ℂ) = ((2 : ℤ) : ℂ) by
      rw [hα, hβ1]; norm_num] at h
  · have hα : α = 3 := by omega
    apply exp_char_rigidity (w := -2) (by norm_num)
    intro t
    have h := hentry t
    rwa [show ((-(α + β) : ℤ) : ℂ) = ((-2 : ℤ) : ℂ) by
      rw [hα, hβ1]; norm_num] at h

#print axioms base_allSwap
#print axioms allSwap_mem_strengthened
#print axioms orbit_classification_complete
#print axioms allSwap_not_weightAt_common

end ThetLogos.DialOneSwapOrbitBase
