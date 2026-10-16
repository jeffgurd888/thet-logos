import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic
import ThetLogos.TritGrading

open scoped Matrix

/-!
# ThetLogos.SexagesimalClock — the base-60 clock: `ZMod 60` arithmetic and clock gradings (T1)

HONESTY LEDGER (read before citing):

- Everything in this file is **T1 background algebra**: the two-place and
  three-place sexagesimal digit theorems for natural numbers, the
  divisibility facts that make `60` the least common multiple of `1,…,6`,
  the canonical reduction maps out of `ZMod 60`, the Chinese remainder
  decomposition `ZMod 60 ≃+* ZMod 3 × ZMod 4 × ZMod 5`, submodule-valued
  `ZMod 60`-gradings of matrix algebras with their commutator / adjoint /
  reflection consequences, the block-offset instance, and the pushforward
  of such a grading along the mod-3 reduction to a `ZMod 3` grading (and,
  transported along `Trit.addEquivZMod3`, to a `TritGrading`).
- It is **not** physics, **not** mass-gap content, **not** a bridge to the
  rest of ACMD. No claim is made or proved connecting the gradings here to
  the ternary TRO, to modular (Tomita) flow, or to any physical system.
  "Modular" in the ACMD corpus means Tomita modular theory; the modular
  arithmetic of this file is a different word that happens to rhyme.
- The grading reduction lands in the *existing* `TritGrading` structure
  of `ThetLogos.TritGrading`. That is a statement about grading
  bookkeeping only: the trit clock sits inside the sexagesimal clock as
  its mod-3 shadow. It is not a physical identification.
- Provenance: Jeff's napkin chain of 2026-10-16 — the sidereal year has
  366 rotations, a circle graduated in 366 would count rotations instead
  of sunrises, and the inherited graduation of the actual circle is
  Babylonian base 60, "base 60 primitive". This file is the machine-checked
  arithmetic of that primitive: what base 60 is, why 60 is the lcm of
  `1,…,6`, and what a clock grading on `ZMod 60` does and does not do.
- Zero sorrys, no new axioms.
-/

namespace ThetLogos

/-! ## §1. Sexagesimal digits

A natural number below `60²` has a unique two-place base-60 expansion;
below `60³`, a unique three-place one. The places are read high-to-low,
as on a clock: `n = 60 * a + b` is hours and minutes. -/

/-- The two sexagesimal digits of `n`, high place first: `(n / 60, n % 60)`. -/
def sexagesimalPair (n : ℕ) : ℕ × ℕ := (n / 60, n % 60)

/-- The digits of `n < 3600` are genuine digits: both are `< 60`. -/
theorem sexagesimalPair_lt {n : ℕ} (hn : n < 3600) :
    (sexagesimalPair n).1 < 60 ∧ (sexagesimalPair n).2 < 60 := by
  constructor
  · exact Nat.div_lt_of_lt_mul (by omega : n < 60 * 60)
  · exact Nat.mod_lt _ (by norm_num)

/-- Two-place sexagesimal expansion: existence. -/
theorem sexagesimal_two_place (n : ℕ) (hn : n < 3600) :
    ∃ a b : ℕ, a < 60 ∧ b < 60 ∧ n = 60 * a + b := by
  refine ⟨n / 60, n % 60, (sexagesimalPair_lt hn).1, (sexagesimalPair_lt hn).2, ?_⟩
  have h := Nat.div_add_mod n 60
  omega

/-- Two-place sexagesimal expansion: uniqueness. -/
theorem sexagesimal_two_place_unique {n a b a' b' : ℕ}
    (_ha : a < 60) (_hb : b < 60) (_ha' : a' < 60) (_hb' : b' < 60)
    (h : n = 60 * a + b) (h' : n = 60 * a' + b') : a = a' ∧ b = b' := by
  omega

/-- The digits produced by `sexagesimalPair` are the two-place expansion. -/
theorem sexagesimalPair_spec {n : ℕ} (hn : n < 3600) :
    n = 60 * (sexagesimalPair n).1 + (sexagesimalPair n).2 ∧
      (sexagesimalPair n).1 < 60 ∧ (sexagesimalPair n).2 < 60 := by
  obtain ⟨a, b, ha, hb, h⟩ := sexagesimal_two_place n hn
  obtain ⟨h1, h2⟩ := sexagesimal_two_place_unique ha hb (sexagesimalPair_lt hn).1
    (sexagesimalPair_lt hn).2 h (by
      have hdm := Nat.div_add_mod n 60
      simp only [sexagesimalPair]
      omega)
  exact ⟨by omega, sexagesimalPair_lt hn⟩

/-- Three-place sexagesimal expansion: existence. Built from the two-place
expansion applied to `n` and then to its high part `n / 60`. -/
theorem sexagesimal_three_place (n : ℕ) (hn : n < 216000) :
    ∃ a b c : ℕ, a < 60 ∧ b < 60 ∧ c < 60 ∧ n = 3600 * a + 60 * b + c := by
  have hdiv : n / 60 < 3600 := Nat.div_lt_of_lt_mul (by omega : n < 60 * 3600)
  obtain ⟨a, b, ha, hb, hm⟩ := sexagesimal_two_place (n / 60) hdiv
  refine ⟨a, b, n % 60, ha, hb, Nat.mod_lt _ (by norm_num), ?_⟩
  have hdm := Nat.div_add_mod n 60
  omega

/-- Three-place sexagesimal expansion: uniqueness. -/
theorem sexagesimal_three_place_unique {n a b c a' b' c' : ℕ}
    (_ha : a < 60) (_hb : b < 60) (_hc : c < 60)
    (_ha' : a' < 60) (_hb' : b' < 60) (_hc' : c' < 60)
    (h : n = 3600 * a + 60 * b + c) (h' : n = 3600 * a' + 60 * b' + c') :
    a = a' ∧ b = b' ∧ c = c' := by
  omega

/-! ## §2. The divisibility core: why 60 is the lcm primitive

`60` is the least common multiple of `1, 2, 3, 4, 5, 6` — the smallest
positive integer every one of them divides. That is the arithmetic content
of "base 60 primitive": inside base 60, halves, thirds, quarters, fifths
and sixths are all whole. -/

/-- Every one of `1, 2, 3, 4, 5, 6` divides `60`. -/
theorem dvd_sixty : ∀ k ∈ ({1, 2, 3, 4, 5, 6} : Finset ℕ), k ∣ 60 := by
  decide

/-- The iterated lcm of `1, 2, 3, 4, 5, 6` is `60`. -/
theorem lcm_one_through_six :
    Nat.lcm (Nat.lcm (Nat.lcm (Nat.lcm (Nat.lcm 1 2) 3) 4) 5) 6 = 60 := by
  decide

/-- The coprimality facts the Chinese remainder decomposition consumes:
`60 = 3 * 20` with `gcd(3, 20) = 1`, then `20 = 4 * 5` with `gcd(4, 5) = 1`. -/
theorem coprime_three_twenty : Nat.Coprime 3 20 := by decide

theorem coprime_four_five : Nat.Coprime 4 5 := by decide

/-! ## §3. Sub-clock reductions

A divisor `d ∣ 60` of the big clock carries a canonical ring homomorphism
`ZMod 60 →+* ZMod d`: read the hour hand on the smaller dial. The mod-3
reduction is the headline: it is the trit clock inside the sexagesimal
clock. -/

/-- The mod-3 reduction of the sexagesimal clock: the trit shadow. -/
def toTritClock : ZMod 60 →+* ZMod 3 := ZMod.castHom (by decide : 3 ∣ 60) (ZMod 3)

/-- The mod-12 reduction (the hour dial inside the sexagesimal clock). -/
def toTwelveClock : ZMod 60 →+* ZMod 12 := ZMod.castHom (by decide : 12 ∣ 60) (ZMod 12)

/-- The mod-5 reduction. -/
def toFiveClock : ZMod 60 →+* ZMod 5 := ZMod.castHom (by decide : 5 ∣ 60) (ZMod 5)

/-- The mod-20 reduction. -/
def toTwentyClock : ZMod 60 →+* ZMod 20 := ZMod.castHom (by decide : 20 ∣ 60) (ZMod 20)

/-- The mod-4 reduction. -/
def toFourClock : ZMod 60 →+* ZMod 4 := ZMod.castHom (by decide : 4 ∣ 60) (ZMod 4)

/-- The reductions are compatible: reducing mod 12 and then mod 3 is
reducing mod 3. -/
theorem toTritClock_eq_comp :
    (ZMod.castHom (by decide : 3 ∣ 12) (ZMod 3)).comp toTwelveClock = toTritClock := by
  simp only [toTwelveClock, toTritClock]
  exact ZMod.castHom_comp _ _

/-- The trit reduction of a cast natural is the cast natural: numerals are
read mod 3, as they should be. -/
theorem toTritClock_natCast (m : ℕ) : toTritClock (m : ZMod 60) = (m : ZMod 3) :=
  map_natCast _ _

/-- The trit reduction of `x` is the cast of its representative. -/
theorem toTritClock_val (x : ZMod 60) : toTritClock x = (x.val : ZMod 3) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  exact map_natCast _ _

/-- The trit reduction on the first clock numerals, one full turn of the
trit dial: `0 1 2 0 1 2`. -/
theorem toTritClock_zero : toTritClock (0 : ZMod 60) = 0 := map_zero _

theorem toTritClock_one : toTritClock (1 : ZMod 60) = 1 := map_one _

theorem toTritClock_two : toTritClock (2 : ZMod 60) = 2 := by
  have h : (2 : ZMod 60) = ((2 : ℕ) : ZMod 60) := by norm_num
  rw [h, toTritClock_natCast]
  decide

theorem toTritClock_three : toTritClock (3 : ZMod 60) = 0 := by
  have h : (3 : ZMod 60) = ((3 : ℕ) : ZMod 60) := by norm_num
  rw [h, toTritClock_natCast]
  decide

theorem toTritClock_four : toTritClock (4 : ZMod 60) = 1 := by
  have h : (4 : ZMod 60) = ((4 : ℕ) : ZMod 60) := by norm_num
  rw [h, toTritClock_natCast]
  decide

theorem toTritClock_five : toTritClock (5 : ZMod 60) = 2 := by
  have h : (5 : ZMod 60) = ((5 : ℕ) : ZMod 60) := by norm_num
  rw [h, toTritClock_natCast]
  decide

/-! ## §4. The Chinese remainder decomposition

`60 = 3 * 20` and `20 = 4 * 5`, both splits coprime, so the sexagesimal
clock is the product of its three prime-power dials, with the trit dial
first. -/

/-- The Chinese remainder equivalence of the sexagesimal clock, with the
trit factor `ZMod 3` explicit as the first component. -/
def crtEquiv : ZMod 60 ≃+* ZMod 3 × ZMod 4 × ZMod 5 :=
  (ZMod.chineseRemainder coprime_three_twenty).trans
    (RingEquiv.prodCongr (RingEquiv.refl (ZMod 3)) (ZMod.chineseRemainder coprime_four_five))

/-- The first component of the CRT equivalence is the trit reduction:
projecting the decomposition onto the `ZMod 3` factor is `toTritClock`. -/
theorem crtEquiv_fst (x : ZMod 60) : (crtEquiv x).1 = toTritClock x := by
  have h1 : (crtEquiv x).1 = (x.val : ZMod 3) := by
    have hfst : (crtEquiv x).1
        = (RingHom.fst (ZMod 3) (ZMod 4 × ZMod 5)) (crtEquiv x) := rfl
    rw [hfst]
    conv_lhs => rw [← ZMod.natCast_zmod_val x]
    rw [map_natCast, map_natCast]
  rw [h1, toTritClock_val]

/-- The CRT equivalence at zero and one, as a sanity check on the dials. -/
theorem crtEquiv_zero : crtEquiv (0 : ZMod 60) = 0 := map_zero _

theorem crtEquiv_one : crtEquiv (1 : ZMod 60) = 1 := map_one _

/-! ## §5. Clock gradings

The `ZMod 60` analogue of `TritGrading`: each homogeneous component is a
`Submodule` (so zero, additive, and scalar closure come for free) and the
multiplication rule is the only axiom. The commutator and adjoint-action
consequences follow exactly as in the trit case. -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A `ZMod 60`-grading ("clock grading") of the matrix algebra
`Matrix ι ι ℂ`: a `ℂ`-submodule of homogeneous matrices for each clock
position, with multiplication respecting addition on the dial. -/
structure ClockGrading (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The homogeneous component at clock position `i`. -/
  component : ZMod 60 → Submodule ℂ (Matrix ι ι ℂ)
  /-- Multiplication of homogeneous elements lands at the summed position. -/
  mul_mem : ∀ (i j : ZMod 60) {A B : Matrix ι ι ℂ},
    A ∈ component i → B ∈ component j → A * B ∈ component (i + j)

namespace ClockGrading

/-- Subtraction closure within a component (inherited from the submodule). -/
theorem sub_mem (G : ClockGrading n) {i : ZMod 60} {A B : Matrix n n ℂ}
    (hA : A ∈ G.component i) (hB : B ∈ G.component i) : A - B ∈ G.component i :=
  (G.component i).sub_mem hA hB

/-- The commutator of homogeneous elements is homogeneous at the summed
clock position. -/
theorem commutator_mem (G : ClockGrading n) {i j : ZMod 60} {A B : Matrix n n ℂ}
    (hA : A ∈ G.component i) (hB : B ∈ G.component j) :
    commutator A B ∈ G.component (i + j) := by
  have hAB : A * B ∈ G.component (i + j) := G.mul_mem i j hA hB
  have hBA : B * A ∈ G.component (i + j) := by
    have h := G.mul_mem j i hB hA
    rwa [add_comm j i] at h
  exact (G.component _).sub_mem hAB hBA

/-- The adjoint action of a position-`0` element preserves every
component: the clock analogue of `TritGrading.ad_mem`, with the additive
identity `0` of the dial playing the role of the trit `zero`. -/
theorem ad_mem (G : ClockGrading n) {j : ZMod 60} {A X : Matrix n n ℂ}
    (hA : A ∈ G.component 0) (hX : X ∈ G.component j) :
    ad A X ∈ G.component j := by
  have hAX : A * X ∈ G.component j := by
    have h := G.mul_mem 0 j hA hX
    rwa [zero_add] at h
  have hXA : X * A ∈ G.component j := by
    have h := G.mul_mem j 0 hX hA
    rwa [add_zero] at h
  exact (G.component _).sub_mem hAX hXA

/-- Reflection of the dial: reading the clock backwards (`i ↦ -i`) turns
a clock grading into a clock grading. This is the symmetry of the dial
that the trit substrate carries as `Trit.negate`. -/
def neg (G : ClockGrading n) : ClockGrading n where
  component := fun i => G.component (-i)
  mul_mem := by
    intro i j A B hA hB
    have h := G.mul_mem (-i) (-j) hA hB
    rwa [neg_add]

/-- The reflected grading at position `i` is the original at `-i`, by
definition. -/
theorem neg_component (G : ClockGrading n) (i : ZMod 60) :
    G.neg.component i = G.component (-i) :=
  rfl

/-- Reflecting twice returns the original grading, componentwise. -/
theorem neg_neg_component (G : ClockGrading n) (i : ZMod 60) :
    G.neg.neg.component i = G.component i := by
  simp only [neg_component, neg_neg]

end ClockGrading

/-! ## §6. The block-offset instance

Matrices indexed by `ZMod 60 × n`: the component at position `g` is the
submodule of block matrices supported where the column block equals the
row block shifted by `g` — a literal 60-block clock face. This is the
`TritGrading.blockGrading` construction read on the big dial, and shows
the grading axioms are inhabited. -/

/-- The position-`g` block component: matrices over `ZMod 60 × n`
vanishing outside the block diagonal offset by `g`. -/
def blockComponentClock (g : ZMod 60) :
    Submodule ℂ (Matrix (ZMod 60 × n) (ZMod 60 × n) ℂ) where
  carrier := {M | ∀ (i j : ZMod 60) (r k : n), j ≠ i + g → M (i, r) (j, k) = 0}
  zero_mem' := by
    intro i j r k _
    simp
  add_mem' := by
    intro A B hA hB i j r k hij
    simp only [Matrix.add_apply, hA i j r k hij, hB i j r k hij, add_zero]
  smul_mem' := by
    intro c A hA i j r k hij
    simp only [Matrix.smul_apply, hA i j r k hij, smul_eq_mul, mul_zero]

omit [Fintype n] [DecidableEq n] in
theorem mem_blockComponentClock {g : ZMod 60} {M : Matrix (ZMod 60 × n) (ZMod 60 × n) ℂ} :
    M ∈ blockComponentClock g ↔
      ∀ (i j : ZMod 60) (r k : n), j ≠ i + g → M (i, r) (j, k) = 0 :=
  Iff.rfl

/-- The block-offset components assemble into a `ClockGrading`. -/
def blockClockGrading : ClockGrading (ZMod 60 × n) where
  component := blockComponentClock
  mul_mem := by
    intro g₁ g₂ A B hA hB
    rw [mem_blockComponentClock] at hA hB ⊢
    intro i j r k hij
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    rintro ⟨m, p⟩ -
    by_cases hm : m = i + g₁
    · have hmj : j ≠ m + g₂ := by
        have hsum : m + g₂ = i + (g₁ + g₂) := by
          rw [hm]
          exact add_assoc i g₁ g₂
        rw [hsum]
        exact hij
      rw [hB m j p k hmj, mul_zero]
    · rw [hA i m r p hm, zero_mul]

/-! ## §7. Reduction of gradings: the trit clock inside the sexagesimal clock

Push a `ClockGrading` forward along `toTritClock`: the `ZMod 3` component
at `k` is the sum (supremum) of the `ZMod 60` components over the fiber
`toTritClock i = k` — twenty clock positions over each trit position.
Multiplication closes because `toTritClock` is a ring homomorphism.
Transporting along `Trit.addEquivZMod3` lands in the existing
`TritGrading` structure. -/

namespace ClockGrading

/-- The pushed-forward family on `ZMod 3`: at `k`, the supremum of the
clock components over the fiber of `toTritClock` above `k`. -/
def pushforward (G : ClockGrading n) (k : ZMod 3) : Submodule ℂ (Matrix n n ℂ) :=
  ⨆ i, ⨆ _ : toTritClock i = k, G.component i

/-- A clock component at position `i` sits inside the pushed-forward
component at its trit shadow `toTritClock i`. -/
theorem component_le_pushforward (G : ClockGrading n) (i : ZMod 60) :
    G.component i ≤ G.pushforward (toTritClock i) :=
  le_iSup_of_le i (le_iSup_of_le rfl le_rfl)

/-- Multiplication closes in the pushed-forward family: the `ZMod 3`
shadow of the clock grading is a grading. The proof is nested inductions
over the fiber suprema — over the position index and over the fiber
proof for the first factor, then over the fibers for the second. -/
theorem pushforward_mul_mem (G : ClockGrading n) {p q : ZMod 3} {A B : Matrix n n ℂ}
    (hA : A ∈ G.pushforward p) (hB : B ∈ G.pushforward q) :
    A * B ∈ G.pushforward (p + q) := by
  -- Induct on the membership of `A`, with the claim quantified over the
  -- second factor so the induction hypotheses are strong enough.
  refine Submodule.iSup_induction _ hA
    (motive := fun A => ∀ (q : ZMod 3) (B : Matrix n n ℂ),
      B ∈ G.pushforward q → A * B ∈ G.pushforward (p + q)) ?_ ?_ ?_ q B hB
  · -- `A` lies over a single clock position `a`: induct on the fiber proof.
    intro a A hA'
    refine Submodule.iSup_induction _ hA'
      (motive := fun A => ∀ (q : ZMod 3) (B : Matrix n n ℂ),
        B ∈ G.pushforward q → A * B ∈ G.pushforward (p + q)) ?_ ?_ ?_
    · -- `A` is homogeneous at position `a` with `toTritClock a = p`:
      -- induct on the membership of `B`.
      intro ha A hAcomp q B hB
      refine Submodule.iSup_induction _ hB
        (motive := fun B => A * B ∈ G.pushforward (p + q)) ?_ ?_ ?_
      · intro b B hB'
        refine Submodule.iSup_induction _ hB'
          (motive := fun B => A * B ∈ G.pushforward (p + q)) ?_ ?_ ?_
        · -- Both factors homogeneous: multiply on the big dial and land
          -- in the fiber over `p + q`.
          intro hb B hBcomp
          have hmul : A * B ∈ G.component (a + b) := G.mul_mem a b hAcomp hBcomp
          have hfib : toTritClock (a + b) = p + q := by rw [map_add, ha, hb]
          have hle := G.component_le_pushforward (a + b)
          rw [hfib] at hle
          exact hle hmul
        · rw [mul_zero]; exact Submodule.zero_mem _
        · intro B₁ B₂ ih₁ ih₂
          rw [mul_add]; exact Submodule.add_mem _ ih₁ ih₂
      · rw [mul_zero]; exact Submodule.zero_mem _
      · intro B₁ B₂ ih₁ ih₂
        rw [mul_add]; exact Submodule.add_mem _ ih₁ ih₂
    · intro q B _
      rw [zero_mul]; exact Submodule.zero_mem _
    · intro A₁ A₂ ih₁ ih₂ q B hB
      rw [add_mul]; exact Submodule.add_mem _ (ih₁ q B hB) (ih₂ q B hB)
  · intro q B _
    rw [zero_mul]; exact Submodule.zero_mem _
  · intro A₁ A₂ ih₁ ih₂ q B hB
    rw [add_mul]; exact Submodule.add_mem _ (ih₁ q B hB) (ih₂ q B hB)

/-- The reduction of a clock grading to a genuine `TritGrading`: the
component at trit `t` is the pushed-forward component at its `ZMod 3`
reading `Trit.toZMod3 t`, and multiplication closes via
`Trit.toZMod3_add`. This is the precise content of "the trit clock sits
inside the sexagesimal clock". -/
def reduceToTrit (G : ClockGrading n) : TritGrading n where
  component := fun t => G.pushforward (Trit.toZMod3 t)
  mul_mem := by
    intro t₁ t₂ A B hA hB
    have h := G.pushforward_mul_mem hA hB
    rw [← Trit.toZMod3_add] at h
    exact h

/-- The reduced grading of the block clock is defined at every trit; in
particular its `zero` component is a submodule, as `TritGrading`
requires — a definitional sanity check that the reduction is inhabited. -/
theorem reduceToTrit_blockClockGrading_zero :
    (blockClockGrading (n := n)).reduceToTrit.component Trit.zero
      = (blockClockGrading (n := n)).pushforward 0 :=
  rfl

end ClockGrading

end ThetLogos
