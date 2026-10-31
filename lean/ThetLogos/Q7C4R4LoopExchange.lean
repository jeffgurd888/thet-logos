import Mathlib.Tactic
import ThetLogos.Q7C4R4LoopProtocol
import ThetLogos.Q7C4R4EnergySplit

namespace ThetLogos

/-!
# ThetLogos.Q7C4R4LoopExchange - the factor-exchange loop
(Q7CR-LOOP-3, the LOOP line's final brick)

**Status: T1 theorem brick. NO CLAIM. Dials 0/4. No measured
number is claimed by this line.**

Governing documents: the scoping memo
`scoping-q7cr-missing-pieces-thermal-loops-2026-10-30.md`
section 2 and the section 4 LOOP-3 row, and the brick pack
`pack-loop-3.md`. Built over LOOP-0's landed registration
(`ThetLogos.Q7C4R4LoopPost`: `LoopData`, `LoopStep`,
`loopStepDefect`, `loopStepEntropyChange`, `loopDefectSum`,
`loopEntropyChangeSum`, `loopLedgerSum`, the three closure
Props, `LoopFactor`), LOOP-2's entropy telescope
(`ThetLogos.Q7C4R4LoopProtocol`), T-ENT
(`ThetLogos.FiniteEntropy`: `entropyW` and its permutation
invariance), Q7CR-2's spectrum (`eigComp`, `compIndex`,
`s7c`, `s4c`, `s_R` in `ThetLogos.Q7C4R4Spectrum`), and
T-Q7-2's composite-energy form (the weight form of
`compEnergy`: sum over composite indices of weight times
`eigComp`). No landed file is edited.

## Verdicts, one per registered part

- **(a) Energy conservation BY FORM - PROVED in general.**
  An exchange step is a permutation `pi` of `compIndex` with
  `eigComp (pi x) = eigComp x` for all `x`, acting on weight
  states by relabeling (`permWeight`). Section 1 proves
  `weightEnergy (permWeight pi w) = weightEnergy w` from the
  stated invariance alone, for any such `pi` and any `w`
  (`weightEnergy_perm`). Section 2 builds the factor-pair
  steps used here as products of factor permutations and
  proves their spectrum preservation from the factor
  eigenvalue functions.
- **(b) Entropy bookkeeping - PROVED for this sequence's
  states, in factor-sum form.** The visited states are
  product-form states (Section 3). For product probability
  weights, `entropyW` of the product is the sum of the
  factor entropies (`entropyW_prod_three`, from the
  two-factor additivity `entropyW_prod_two`), the factor
  marginals of a product state are its factors
  (`q7Marg_prod`, `c4Marg_prod`, `r4Marg_prod`), and hence
  the total entropy change across the exchange sequence is
  the sum of the three factor marginal entropy changes
  (`exchange_entropy_bookkeeping`). The production clause,
  stated exactly: this brick's steps are PURE RELABELING
  steps, not defect-carrying steps - each step's defect term
  and entropy-change term are exactly `0` (Section 1), so
  the total production of the landed sequence is `0`, which
  is `>= 0` in equality form. The memo's conditional clause
  for defect-carrying exchange steps is NOT instantiated
  here and is not claimed: no defect-carrying exchange step
  is used. (b) does not die; it lands in the relabeling
  form, labeled as such.
- **(c) Closure - PROVED, under a NEW name.** The stated
  exchange sequence (`exchangeData`, Section 4) is two
  factor-pair steps on the Q7 x C4 joint package: the first
  swaps a Q7 site pair and a C4 site pair (both pairs carry
  equal factor eigenvalues, so both steps are
  spectrum-preserving by Section 2), the second swaps the
  Q7 pair back and touches nothing else. The Q7 factor
  marginal therefore returns EXACTLY to its initial value,
  the composite data is `LedgerClosed` with stated total
  `0` and every ledger term carried on the `c4` / `r4`
  factor fields of its step (no ledger term is carried by
  `q7`), the external work term is `0`, and the content on
  the non-working factors is NONTRIVIAL: when the initial
  C4 weight distinguishes the swapped C4 sites, the final
  C4 marginal differs from the initial one
  (`exchange_c4Marg_ne`), the full composite state does NOT
  return (`exchange_not_stateClosed`), and a fully concrete
  basis-weight instance is exhibited
  (`exchange_concrete_factorSelfContained`).

## Naming distinction (binding, stated on the face)

LOOP-0's `SelfContainedLoop` requires FULL composite
`StateClosed`: the whole state on `compIndex` returns. The
closure proved here is weaker and different: only the
working factor (Q7) returns, while the C4 marginal is
provably moved. It is therefore registered under the NEW
name `FactorSelfContainedLoop` (Section 4): Q7-marginal
state closure, AND `LedgerClosed`, AND external work `0`.
LOOP-0's name is never spent on this statement, and the
concrete instance below proves the distinction is real for
this very data: `FactorSelfContainedLoop` holds and
`StateClosed` fails. Per K-LOOP-3, no index closure is
sold as state closure anywhere in this module: the protocol
parameters of `exchangeData` start and end equal as stated
data, and no theorem here calls that a finding.

## Line-closing summary - the three readings, as landed

- Autonomous reading (LOOP-1): a self-contained autonomous
  thermal loop is trivial-or-nonexistent - exact return
  forces every visited state into the fixed sector.
- Protocol reading (LOOP-2): `IndexClosed` plus a ledger;
  the controls return, the state is in general moved, and
  state closure is equivalent to total defect `0`.
- Factor-exchange reading (LOOP-3, this brick): the
  surviving meaning of "self-contained thermal loop" -
  energy conserved by form, entropy accounted factor by
  factor, the working factor returning exactly, the cost
  and the movement carried on the other factors' ledgers,
  zero external work. In the form landed here the steps
  are pure relabelings, so the carried production is `0`
  and the nontrivial content is the moved C4 marginal.

Fences: NO CLAIM; dials 0/4; no measured number is claimed
by this line; the bounded-commutator vacuity caveat of the
gauntlet memo applies where the composite's operators are
mentioned.
-/

/-! ## Section 1. Permutation exchange steps in general:
energy conserved by form, defect and entropy change zero -/

/-- **The weight-form composite energy**: the expectation of
the composite eigenvalue function `eigComp` (Q7CR-2) under
a weight state - the weight form of T-Q7-2's `compEnergy`.
Tier T2 (definition). -/
noncomputable def weightEnergy (w : compIndex → ℝ) : ℝ :=
  ∑ x, w x * eigComp x

/-- **Relabeling action of a permutation** on weight states.
Tier T2 (definition). -/
def permWeight (pi : Equiv.Perm compIndex) (w : compIndex → ℝ) :
    compIndex → ℝ :=
  fun x => w (pi x)

/-- **(a) ENERGY CONSERVATION BY FORM (Tier T1), in general.**
For any permutation `pi` of `compIndex` preserving the
composite eigenvalue function (`eigComp (pi x) = eigComp x`
for all `x`) and any weight state `w`, the relabeled state's
weight energy equals the original's. The proof is the
reindexing `Equiv.sum_comp` after rewriting each eigenvalue
by the stated invariance - conservation is proved from the
property, not computed on an example. -/
theorem weightEnergy_perm (pi : Equiv.Perm compIndex)
    (hpi : ∀ x, eigComp (pi x) = eigComp x) (w : compIndex → ℝ) :
    weightEnergy (permWeight pi w) = weightEnergy w := by
  unfold weightEnergy permWeight
  have hterm : ∀ x, w (pi x) * eigComp x
      = w (pi x) * eigComp (pi x) := by
    intro x
    rw [hpi x]
  rw [Finset.sum_congr rfl (fun x _ => hterm x)]
  exact Equiv.sum_comp pi (fun x => w x * eigComp x)

/-- **An exchange step as loop data**: the relabeling step of
a permutation `pi`, with zero time, zero rate data, and both
ledger terms carried by the named factor `f`. The zero time
is what makes its registered defect term vanish; the factor
field is where its (zero) ledger terms are carried. Tier T2
(definition). -/
def permLoopStep (pi : Equiv.Perm compIndex) (f : LoopFactor) :
    LoopStep where
  param := { time := 0, grade := 0, coupling := 0 }
  applyState := permWeight pi
  rate := fun _ => 0
  defectFactor := f
  entropyFactor := f

/-- **A permutation step's defect term is zero** (Tier T1):
its time is `0`, so every summand of `loopStepDefect`
carries the factor `1 - exp 0 = 0`. -/
theorem permLoopStep_defect_zero (pi : Equiv.Perm compIndex)
    (f : LoopFactor) (w : compIndex → ℝ) :
    loopStepDefect (permLoopStep pi f) w = 0 := by
  unfold loopStepDefect permLoopStep
  simp

/-- **A permutation step's entropy-change term is zero**
(Tier T1): T-ENT's permutation invariance of `entropyW`
(`entropyW_comp_perm`), applied to the relabeled state. -/
theorem permLoopStep_entropyChange_zero
    (pi : Equiv.Perm compIndex) (f : LoopFactor)
    (w : compIndex → ℝ) :
    loopStepEntropyChange (permLoopStep pi f) w = 0 := by
  unfold loopStepEntropyChange permLoopStep permWeight
  rw [entropyW_comp_perm w pi, sub_self]

/-- **Ledger sums over a list of permutation steps vanish**
(Tier T1): if every step of a list is a permutation step
(`permLoopStep` of some permutation and factor), then both
the defect sum and the entropy-change sum over the list,
at any initial state, are `0`. This is the ledger content
of the pure-relabeling form: production `0`, in equality
form, carried step by step on each step's named factor. -/
theorem permSteps_ledger_zero :
    ∀ (L : List LoopStep),
      (∀ s ∈ L, ∃ (pi : Equiv.Perm compIndex) (f : LoopFactor),
        s = permLoopStep pi f)
      → ∀ w, loopDefectSum L w = 0
        ∧ loopEntropyChangeSum L w = 0 := by
  intro L
  induction L with
  | nil =>
    intro _ w
    exact ⟨rfl, rfl⟩
  | cons s rest ih =>
    intro h w
    obtain ⟨pi, f, rfl⟩ := h s List.mem_cons_self
    have hrest : ∀ s' ∈ rest, ∃ (pi : Equiv.Perm compIndex)
        (f : LoopFactor), s' = permLoopStep pi f :=
      fun s' hs' => h s' (List.mem_cons_of_mem (permLoopStep pi f) hs')
    obtain ⟨hd, he⟩ := ih hrest ((permLoopStep pi f).applyState w)
    show loopStepDefect (permLoopStep pi f) w
        + loopDefectSum rest ((permLoopStep pi f).applyState w) = 0
      ∧ loopStepEntropyChange (permLoopStep pi f) w
        + loopEntropyChangeSum rest
          ((permLoopStep pi f).applyState w) = 0
    simp only [permLoopStep_defect_zero, permLoopStep_entropyChange_zero,
      hd, he, add_zero]
    exact ⟨trivial, trivial⟩

/-! ## Section 2. Factor-pair permutations and their
spectrum preservation -/

/-- **A factor permutation**: the product of permutations of
the three factor index sets, as a permutation of
`compIndex = ((Fin 7 x Fin 2) x (Fin 4 x Fin 2)) x Fin 4`.
Tier T2 (definition). -/
def factorPerm (p7 : Equiv.Perm (Fin 7 × Fin 2))
    (p4 : Equiv.Perm (Fin 4 × Fin 2)) (pR : Equiv.Perm (Fin 4)) :
    Equiv.Perm compIndex :=
  Equiv.prodCongr (Equiv.prodCongr p7 p4) pR

/-- **Spectrum preservation for factor permutations**
(Tier T1): if each factor permutation preserves its factor
eigenvalue function (`s7c`, `s4c`, `s_R`), the factor
permutation preserves the composite eigenvalue function
`eigComp`, whose value is the sum of the three factor
values. -/
theorem eigComp_factorPerm (p7 : Equiv.Perm (Fin 7 × Fin 2))
    (p4 : Equiv.Perm (Fin 4 × Fin 2)) (pR : Equiv.Perm (Fin 4))
    (h7 : ∀ a, s₇c (p7 a) = s₇c a)
    (h4 : ∀ c, s₄c (p4 c) = s₄c c)
    (hR : ∀ r, s_R (pR r) = s_R r) (t : compIndex) :
    eigComp (factorPerm p7 p4 pR t) = eigComp t := by
  show s₇c (p7 t.1.1) + s₄c (p4 t.1.2) + s_R (pR t.2)
    = s₇c t.1.1 + s₄c t.1.2 + s_R t.2
  rw [h7, h4, hR]

/-- **The Q7 site-pair swap**, as a permutation of the
realified Q7 index: swap sites `0` and `1` of `Fin 7`,
fixing the realification coordinate. Sites `0` and `1`
carry the squared diagonal entries `a7 0 ^ 2 = 9` and
`a7 1 ^ 2 = 9`. Tier T2 (definition). -/
def swapQ7A : Equiv.Perm (Fin 7 × Fin 2) :=
  Equiv.prodCongr (Equiv.swap 0 1) (Equiv.refl (Fin 2))

/-- **The C4 site-pair swap**, as a permutation of the
realified C4 index: swap sites `0` and `3` of `Fin 4`,
fixing the realification coordinate. Sites `0` and `3`
carry the squared centered ladder entries
`d4 0 ^ 2 = 9 / 64` and `d4 3 ^ 2 = 9 / 64`. Tier T2
(definition). -/
def swapC4B : Equiv.Perm (Fin 4 × Fin 2) :=
  Equiv.prodCongr (Equiv.swap 0 3) (Equiv.refl (Fin 2))

/-- The Q7 swap is involutive, pointwise. Tier T1. -/
theorem swapQ7A_involutive (a : Fin 7 × Fin 2) :
    swapQ7A (swapQ7A a) = a := by
  obtain ⟨k, b⟩ := a
  show ((Equiv.swap (0 : Fin 7) 1) ((Equiv.swap 0 1) k), b) = (k, b)
  rw [Equiv.swap_apply_self]

/-- **The Q7 swap preserves the Q7 factor eigenvalues**
(Tier T1): at the swapped sites the values are both `9`;
at every other site the swap fixes the index. -/
theorem s7c_swapQ7A (a : Fin 7 × Fin 2) :
    s₇c (swapQ7A a) = s₇c a := by
  obtain ⟨k, b⟩ := a
  rw [s₇c_apply, s₇c_apply]
  show a₇ ((Equiv.swap (0 : Fin 7) 1) k) ^ 2 = a₇ k ^ 2
  by_cases h0 : k = 0
  · rw [h0]
    simp [a₇]
  · by_cases h1 : k = 1
    · rw [h1]
      simp [a₇]
    · rw [Equiv.swap_apply_of_ne_of_ne h0 h1]

/-- **The C4 swap preserves the C4 factor eigenvalues**
(Tier T1): at the swapped sites the values are both
`9 / 64`; at every other site the swap fixes the index. -/
theorem s4c_swapC4B (c : Fin 4 × Fin 2) :
    s₄c (swapC4B c) = s₄c c := by
  obtain ⟨k, b⟩ := c
  rw [s₄c_apply, s₄c_apply]
  show d₄ ((Equiv.swap (0 : Fin 4) 3) k) ^ 2 = d₄ k ^ 2
  by_cases h0 : k = 0
  · rw [h0]
    norm_num [d₄, z4Energy]
  · by_cases h3 : k = 3
    · rw [h3]
      norm_num [d₄, z4Energy]
    · rw [Equiv.swap_apply_of_ne_of_ne h0 h3]


/-! ## Section 3. Factor marginals, product states, and the
entropy factor-sum identity -/

/-- **The Q7 factor marginal** of a composite weight state:
sum over the C4 and R4 coordinates. Tier T2 (definition). -/
noncomputable def q7Marg (w : compIndex → ℝ) :
    (Fin 7 × Fin 2) → ℝ :=
  fun a => ∑ c, ∑ r, w ((a, c), r)

/-- **The C4 factor marginal**: sum over the Q7 and R4
coordinates. Tier T2 (definition). -/
noncomputable def c4Marg (w : compIndex → ℝ) :
    (Fin 4 × Fin 2) → ℝ :=
  fun c => ∑ a, ∑ r, w ((a, c), r)

/-- **The R4 factor marginal**: sum over the Q7 and C4
coordinates. Tier T2 (definition). -/
noncomputable def r4Marg (w : compIndex → ℝ) : Fin 4 → ℝ :=
  fun r => ∑ a, ∑ c, w ((a, c), r)

/-- **A product-form composite weight state** from factor
weights `u`, `v`, `z`. Tier T2 (definition). -/
def prodWeight (u : (Fin 7 × Fin 2) → ℝ)
    (v : (Fin 4 × Fin 2) → ℝ) (z : Fin 4 → ℝ) :
    compIndex → ℝ :=
  fun t => u t.1.1 * v t.1.2 * z t.2

/-- **Q7 marginal of a product state** (Tier T1): when the
other two factors have total weight `1` each, the Q7
marginal is exactly the Q7 factor weight. -/
theorem q7Marg_prod (u : (Fin 7 × Fin 2) → ℝ)
    (v : (Fin 4 × Fin 2) → ℝ) (z : Fin 4 → ℝ)
    (hv : ∑ c, v c = 1) (hz : ∑ r, z r = 1) :
    q7Marg (prodWeight u v z) = u := by
  funext a
  show (∑ c, ∑ r, u a * v c * z r) = u a
  have h1 : ∀ c, (∑ r, u a * v c * z r) = u a * v c := by
    intro c
    have hrw : (∑ r, u a * v c * z r)
        = (u a * v c) * ∑ r, z r := by
      rw [Finset.mul_sum]
    rw [hrw, hz, mul_one]
  rw [Finset.sum_congr rfl (fun c _ => h1 c), ← Finset.mul_sum, hv,
    mul_one]

/-- **C4 marginal of a product state** (Tier T1). -/
theorem c4Marg_prod (u : (Fin 7 × Fin 2) → ℝ)
    (v : (Fin 4 × Fin 2) → ℝ) (z : Fin 4 → ℝ)
    (hu : ∑ a, u a = 1) (hz : ∑ r, z r = 1) :
    c4Marg (prodWeight u v z) = v := by
  funext c
  show (∑ a, ∑ r, u a * v c * z r) = v c
  have h1 : ∀ a, (∑ r, u a * v c * z r) = u a * v c := by
    intro a
    have hrw : (∑ r, u a * v c * z r)
        = (u a * v c) * ∑ r, z r := by
      rw [Finset.mul_sum]
    rw [hrw, hz, mul_one]
  rw [Finset.sum_congr rfl (fun a _ => h1 a), ← Finset.sum_mul, hu,
    one_mul]

/-- **R4 marginal of a product state** (Tier T1). -/
theorem r4Marg_prod (u : (Fin 7 × Fin 2) → ℝ)
    (v : (Fin 4 × Fin 2) → ℝ) (z : Fin 4 → ℝ)
    (hu : ∑ a, u a = 1) (hv : ∑ c, v c = 1) :
    r4Marg (prodWeight u v z) = z := by
  funext r
  show (∑ a, ∑ c, u a * v c * z r) = z r
  have h1 : ∀ a, (∑ c, u a * v c * z r) = u a * z r := by
    intro a
    have hrw : (∑ c, u a * v c * z r)
        = (u a * z r) * ∑ c, v c := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    rw [hrw, hv, mul_one]
  rw [Finset.sum_congr rfl (fun a _ => h1 a), ← Finset.sum_mul, hu,
    one_mul]

/-- **A product of two probability weights** is a
probability weight. Tier T1. -/
theorem isProbWeight_prod_two {α β : Type*} [Fintype α]
    [Fintype β] {u : α → ℝ} {v : β → ℝ}
    (hu : IsProbWeight u) (hv : IsProbWeight v) :
    IsProbWeight (fun p : α × β => u p.1 * v p.2) := by
  constructor
  · intro p
    exact mul_nonneg (hu.1 p.1) (hv.1 p.2)
  · rw [sum_prod_mul, hu.2, hv.2, mul_one]

/-- **A permuted probability weight** is a probability
weight. Tier T1. -/
theorem isProbWeight_comp_perm {α : Type*} [Fintype α]
    {w : α → ℝ} (hw : IsProbWeight w) (e : Equiv.Perm α) :
    IsProbWeight (fun j => w (e j)) := by
  constructor
  · intro j
    exact hw.1 (e j)
  · exact (Equiv.sum_comp e w).trans hw.2

/-- The pointwise log-product identity behind entropy
additivity (Tier T1): at every pair, the product weight's
entropy summand splits into the two weighted factor
summands - in all cases, including zero weights, where
Mathlib's `Real.log 0 = 0` makes both sides vanish. -/
theorem mul_log_prod_split {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x * y) * Real.log (x * y)
      = y * (x * Real.log x) + x * (y * Real.log y) := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · simp
  · rcases eq_or_lt_of_le hy with rfl | hypos
    · simp
    · rw [Real.log_mul hxpos.ne' hypos.ne']
      ring

/-- **Two-factor entropy additivity (Tier T1)**: for
probability weights on finite types, the entropy of the
product weight is the sum of the factor entropies - the
T-ENT additivity this brick's factor bookkeeping rests
on. -/
theorem entropyW_prod_two {α β : Type*} [Fintype α]
    [Fintype β] {u : α → ℝ} {v : β → ℝ}
    (hu : IsProbWeight u) (hv : IsProbWeight v) :
    entropyW (fun p : α × β => u p.1 * v p.2)
      = entropyW u + entropyW v := by
  have hterm : ∀ p : α × β,
      (u p.1 * v p.2) * Real.log (u p.1 * v p.2)
        = v p.2 * (u p.1 * Real.log (u p.1))
          + u p.1 * (v p.2 * Real.log (v p.2)) :=
    fun p => mul_log_prod_split (hu.1 p.1) (hv.1 p.2)
  have hs1 : ∑ p : α × β, v p.2 * (u p.1 * Real.log (u p.1))
      = ∑ a, u a * Real.log (u a) := by
    calc ∑ p : α × β, v p.2 * (u p.1 * Real.log (u p.1))
        = ∑ p : α × β, (fun a => u a * Real.log (u a)) p.1
            * (fun b => v b) p.2 := by
          apply Finset.sum_congr rfl
          intro p _
          show v p.2 * (u p.1 * Real.log (u p.1))
            = u p.1 * Real.log (u p.1) * v p.2
          ring
      _ = (∑ a, u a * Real.log (u a)) * ∑ b, v b :=
          sum_prod_mul (fun a => u a * Real.log (u a)) (fun b => v b)
      _ = ∑ a, u a * Real.log (u a) := by rw [hv.2, mul_one]
  have hs2 : ∑ p : α × β, u p.1 * (v p.2 * Real.log (v p.2))
      = ∑ b, v b * Real.log (v b) := by
    calc ∑ p : α × β, u p.1 * (v p.2 * Real.log (v p.2))
        = ∑ p : α × β, (fun a => u a) p.1
            * (fun b => v b * Real.log (v b)) p.2 := rfl
      _ = (∑ a, u a) * ∑ b, v b * Real.log (v b) :=
          sum_prod_mul (fun a => u a) (fun b => v b * Real.log (v b))
      _ = ∑ b, v b * Real.log (v b) := by rw [hu.2, one_mul]
  have hsum : ∑ p : α × β,
        (u p.1 * v p.2) * Real.log (u p.1 * v p.2)
      = (∑ a, u a * Real.log (u a))
        + ∑ b, v b * Real.log (v b) := by
    rw [Finset.sum_congr rfl (fun p _ => hterm p),
      Finset.sum_add_distrib, hs1, hs2]
  unfold entropyW
  rw [hsum]
  ring

/-- **Three-factor entropy additivity (Tier T1)**: for
probability factor weights, the entropy of the composite
product weight is the sum of the three factor entropies.
Route: two-factor additivity at the pair factor, then at
the composite. -/
theorem entropyW_prod_three (u : (Fin 7 × Fin 2) → ℝ)
    (v : (Fin 4 × Fin 2) → ℝ) (z : Fin 4 → ℝ)
    (hu : IsProbWeight u) (hv : IsProbWeight v)
    (hz : IsProbWeight z) :
    entropyW (prodWeight u v z)
      = entropyW u + entropyW v + entropyW z := by
  have hprod : prodWeight u v z
      = (fun t : ((Fin 7 × Fin 2) × (Fin 4 × Fin 2)) × Fin 4 =>
          (fun p : (Fin 7 × Fin 2) × (Fin 4 × Fin 2) =>
            u p.1 * v p.2) t.1 * z t.2) := rfl
  rw [hprod, entropyW_prod_two (isProbWeight_prod_two hu hv) hz,
    entropyW_prod_two hu hv]


/-! ## Section 4. The stated exchange sequence and its
closure under the new name -/

/-- **The first exchange permutation**: swap the Q7 site
pair and the C4 site pair, fix R4. It acts on the Q7 x C4
joint factor package. Tier T2 (definition). -/
def exchangePi1 : Equiv.Perm compIndex :=
  factorPerm swapQ7A swapC4B (Equiv.refl (Fin 4))

/-- **The second exchange permutation**: swap the Q7 site
pair back, fix C4 and R4. Tier T2 (definition). -/
def exchangePi2 : Equiv.Perm compIndex :=
  factorPerm swapQ7A (Equiv.refl (Fin 4 × Fin 2))
    (Equiv.refl (Fin 4))

/-- **Both exchange permutations are spectrum-preserving**
(Tier T1), by `eigComp_factorPerm` and the factor swap
lemmas - hence (a) applies to both steps by
`weightEnergy_perm`. -/
theorem eigComp_exchangePi :
    (∀ x, eigComp (exchangePi1 x) = eigComp x)
      ∧ (∀ x, eigComp (exchangePi2 x) = eigComp x) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · exact eigComp_factorPerm swapQ7A swapC4B (Equiv.refl (Fin 4))
      s7c_swapQ7A s4c_swapC4B (fun r => rfl) x
  · exact eigComp_factorPerm swapQ7A (Equiv.refl (Fin 4 × Fin 2))
      (Equiv.refl (Fin 4)) s7c_swapQ7A (fun c => rfl) (fun r => rfl) x

/-- **The stated exchange sequence as loop data**: two
permutation steps - the first carried on the `c4` factor
field, the second on the `r4` factor field (every ledger
term of this data is carried by a C4/R4 field, none by
`q7`) - initial state the product weight `prodWeight u v z`,
protocol parameters stated identical at start and end,
stated ledger total `0`, external work `0`. Tier T2
(definition). -/
noncomputable def exchangeData (u : (Fin 7 × Fin 2) → ℝ)
    (v : (Fin 4 × Fin 2) → ℝ) (z : Fin 4 → ℝ) : LoopData where
  steps := [permLoopStep exchangePi1 LoopFactor.c4,
    permLoopStep exchangePi2 LoopFactor.r4]
  initialState := prodWeight u v z
  initialParam := { time := 0, grade := 0, coupling := 0 }
  finalParam := { time := 0, grade := 0, coupling := 0 }
  statedLedgerTotal := 0
  externalWork := 0

/-- Every step of the exchange data is a permutation step.
Tier T1. -/
theorem exchange_steps_perm (u : (Fin 7 × Fin 2) → ℝ)
    (v : (Fin 4 × Fin 2) → ℝ) (z : Fin 4 → ℝ) :
    ∀ s ∈ (exchangeData u v z).steps,
      ∃ (pi : Equiv.Perm compIndex) (f : LoopFactor),
        s = permLoopStep pi f := by
  intro s hs
  simp only [exchangeData, List.mem_cons, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl | rfl
  · exact ⟨exchangePi1, LoopFactor.c4, rfl⟩
  · exact ⟨exchangePi2, LoopFactor.r4, rfl⟩

/-- **LedgerClosed of the exchange data** (Tier T1): both
ledger sums vanish by `permSteps_ledger_zero`, and the
stated total is `0`. The ledger terms are the steps' own,
carried on their `c4` / `r4` fields. -/
theorem exchange_ledgerClosed (u : (Fin 7 × Fin 2) → ℝ)
    (v : (Fin 4 × Fin 2) → ℝ) (z : Fin 4 → ℝ) :
    LedgerClosed (exchangeData u v z) := by
  obtain ⟨hd, he⟩ := permSteps_ledger_zero
    (exchangeData u v z).steps (exchange_steps_perm u v z)
    (exchangeData u v z).initialState
  show loopLedgerSum (exchangeData u v z)
    = (exchangeData u v z).statedLedgerTotal
  unfold loopLedgerSum
  rw [hd, he, add_zero]
  rfl

/-- **(a) at the exchange sequence** (Tier T1): the final
state's weight energy equals the initial state's, by two
applications of `weightEnergy_perm`. -/
theorem exchange_energy_conserved (u : (Fin 7 × Fin 2) → ℝ)
    (v : (Fin 4 × Fin 2) → ℝ) (z : Fin 4 → ℝ) :
    weightEnergy (loopFinalState (exchangeData u v z))
      = weightEnergy (prodWeight u v z) := by
  have hfin : loopFinalState (exchangeData u v z)
      = permWeight exchangePi2
        (permWeight exchangePi1 (prodWeight u v z)) := rfl
  rw [hfin, weightEnergy_perm exchangePi2 eigComp_exchangePi.2,
    weightEnergy_perm exchangePi1 eigComp_exchangePi.1]

/-- **The state after the first exchange step** (Tier T1):
the product weight with its Q7 and C4 factors relabeled by
the respective swaps. -/
theorem exchange_firstState_eq (u : (Fin 7 × Fin 2) → ℝ)
    (v : (Fin 4 × Fin 2) → ℝ) (z : Fin 4 → ℝ) :
    (permLoopStep exchangePi1 LoopFactor.c4).applyState
        (prodWeight u v z)
      = prodWeight (fun a => u (swapQ7A a))
          (fun c => v (swapC4B c)) z := by
  funext t
  show u (swapQ7A t.1.1) * v (swapC4B t.1.2) * z t.2
    = u (swapQ7A t.1.1) * v (swapC4B t.1.2) * z t.2
  rfl

/-- **The final state of the exchange sequence** (Tier T1):
the product weight with Q7 factor restored exactly (the
swap applied twice), C4 factor relabeled by its swap, R4
factor untouched. -/
theorem exchange_finalState_eq (u : (Fin 7 × Fin 2) → ℝ)
    (v : (Fin 4 × Fin 2) → ℝ) (z : Fin 4 → ℝ) :
    loopFinalState (exchangeData u v z)
      = prodWeight u (fun c => v (swapC4B c)) z := by
  have hfin : loopFinalState (exchangeData u v z)
      = permWeight exchangePi2
        (permWeight exchangePi1 (prodWeight u v z)) := rfl
  rw [hfin]
  funext t
  show (prodWeight u v z) (exchangePi1 (exchangePi2 t))
    = u t.1.1 * v (swapC4B t.1.2) * z t.2
  have hcoord : exchangePi1 (exchangePi2 t)
      = ((t.1.1, swapC4B t.1.2), t.2) := by
    show ((swapQ7A (swapQ7A t.1.1), swapC4B t.1.2), t.2)
      = ((t.1.1, swapC4B t.1.2), t.2)
    rw [swapQ7A_involutive]
  rw [hcoord]
  rfl

/-- **FactorSelfContainedLoop (NEW NAME, this module)**:
working-factor state closure AND ledger closure AND zero
external work - that is,
`q7Marg (loopFinalState L) = q7Marg L.initialState`,
`LedgerClosed L`, and `L.externalWork = 0`.

**Distinction from LOOP-0's `SelfContainedLoop`**: that
name requires FULL composite `StateClosed`
(`loopFinalState L = L.initialState` on all of
`compIndex`). This name requires the return of the Q7
factor marginal only; the other factors may - and in the
instance below provably do - move. The two names are not
interchangeable, and this module never uses LOOP-0's name
for the factor statement. Tier T2 (definition). -/
def FactorSelfContainedLoop (L : LoopData) : Prop :=
  q7Marg (loopFinalState L) = q7Marg L.initialState
    ∧ LedgerClosed L ∧ L.externalWork = 0

/-- **The Q7 marginal returns exactly** (Tier T1): final
and initial Q7 marginals both equal the Q7 factor weight
`u`, by the final-state formula and `q7Marg_prod` (the
permuted C4 weight still sums to `1`). -/
theorem exchange_q7Marg_returns (u : (Fin 7 × Fin 2) → ℝ)
    (v : (Fin 4 × Fin 2) → ℝ) (z : Fin 4 → ℝ)
    (hv : ∑ c, v c = 1) (hz : ∑ r, z r = 1) :
    q7Marg (loopFinalState (exchangeData u v z))
      = q7Marg (prodWeight u v z) := by
  have hvswap : ∑ c, v (swapC4B c) = 1 :=
    (Equiv.sum_comp swapC4B v).trans hv
  rw [exchange_finalState_eq, q7Marg_prod u _ z hvswap hz,
    q7Marg_prod u v z hv hz]

/-- **The final C4 marginal** (Tier T1): the initial C4
factor weight relabeled by the C4 swap. -/
theorem exchange_c4Marg_final (u : (Fin 7 × Fin 2) → ℝ)
    (v : (Fin 4 × Fin 2) → ℝ) (z : Fin 4 → ℝ)
    (hu : ∑ a, u a = 1) (hz : ∑ r, z r = 1) :
    c4Marg (loopFinalState (exchangeData u v z))
      = fun c => v (swapC4B c) := by
  rw [exchange_finalState_eq]
  exact c4Marg_prod u (fun c => v (swapC4B c)) z hu hz

/-- **NONTRIVIALITY on the non-working factor** (Tier T1):
when the initial C4 weight distinguishes the swapped C4
sites (`v (3, 0) ≠ v (0, 0)` at site-pair `(0, 3)`), the
final C4 marginal DIFFERS from the initial C4 marginal.
A sequence moving nothing would be vacuity; this one
provably moves the C4 marginal. -/
theorem exchange_c4Marg_ne (u : (Fin 7 × Fin 2) → ℝ)
    (v : (Fin 4 × Fin 2) → ℝ) (z : Fin 4 → ℝ)
    (hu : ∑ a, u a = 1) (hz : ∑ r, z r = 1)
    (hne : v ((3 : Fin 4), (0 : Fin 2))
      ≠ v ((0 : Fin 4), (0 : Fin 2))) :
    c4Marg (loopFinalState (exchangeData u v z))
      ≠ c4Marg (prodWeight u v z) := by
  intro h
  have hfin := exchange_c4Marg_final u v z hu hz
  have hini : c4Marg (prodWeight u v z) = v :=
    c4Marg_prod u v z hu hz
  rw [hfin, hini] at h
  have hval := congrFun h ((0 : Fin 4), (0 : Fin 2))
  have hswap : swapC4B ((0 : Fin 4), (0 : Fin 2))
      = ((3 : Fin 4), (0 : Fin 2)) := rfl
  rw [hswap] at hval
  exact hne hval

/-- **The exchange sequence is NOT fully state-closed**
(Tier T1), under the same nontriviality hypothesis: full
composite `StateClosed` would force the C4 marginals to
agree, and they do not. This is the proved distinction
between `FactorSelfContainedLoop` and LOOP-0's
`SelfContainedLoop` at this data. -/
theorem exchange_not_stateClosed (u : (Fin 7 × Fin 2) → ℝ)
    (v : (Fin 4 × Fin 2) → ℝ) (z : Fin 4 → ℝ)
    (hu : ∑ a, u a = 1) (hz : ∑ r, z r = 1)
    (hne : v ((3 : Fin 4), (0 : Fin 2))
      ≠ v ((0 : Fin 4), (0 : Fin 2))) :
    ¬ StateClosed (exchangeData u v z) := by
  intro h
  apply exchange_c4Marg_ne u v z hu hz hne
  have hmarg : c4Marg (loopFinalState (exchangeData u v z))
      = c4Marg (exchangeData u v z).initialState :=
    congrArg c4Marg h
  exact hmarg

/-- **(c) THE CLOSURE THEOREM (Tier T1)**: the exchange
data is `FactorSelfContainedLoop` - the Q7 marginal
returns exactly, the ledger closes with its terms carried
on the `c4` / `r4` fields, and the external work term is
`0`. This is the factor-exchange reading, under its own
name; LOOP-0's `SelfContainedLoop` is not claimed. -/
theorem exchange_factorSelfContained
    (u : (Fin 7 × Fin 2) → ℝ) (v : (Fin 4 × Fin 2) → ℝ)
    (z : Fin 4 → ℝ) (hv : ∑ c, v c = 1) (hz : ∑ r, z r = 1) :
    FactorSelfContainedLoop (exchangeData u v z) := by
  refine ⟨?_, exchange_ledgerClosed u v z, rfl⟩
  show q7Marg (loopFinalState (exchangeData u v z))
    = q7Marg (exchangeData u v z).initialState
  exact exchange_q7Marg_returns u v z hv hz


/-! ## Section 5. Entropy bookkeeping for the sequence and
the concrete instance -/

/-- **Entropy additivity at the visited states** (Tier
T1): the initial, intermediate (after the first step), and
final states of the exchange sequence are product-form,
and at each of them the composite entropy is the sum of
the three factor entropies, by `entropyW_prod_three`.
The permuted factor entropies equal the original ones by
T-ENT invariance, recorded in the intermediate line. -/
theorem exchange_entropy_additivity_visited
    (u : (Fin 7 × Fin 2) → ℝ) (v : (Fin 4 × Fin 2) → ℝ)
    (z : Fin 4 → ℝ) (hu : IsProbWeight u) (hv : IsProbWeight v)
    (hz : IsProbWeight z) :
    entropyW (prodWeight u v z)
        = entropyW u + entropyW v + entropyW z
      ∧ entropyW ((permLoopStep exchangePi1 LoopFactor.c4).applyState
          (prodWeight u v z))
        = entropyW u + entropyW v + entropyW z
      ∧ entropyW (loopFinalState (exchangeData u v z))
        = entropyW u + entropyW v + entropyW z := by
  have hperm7 : IsProbWeight (fun a => u (swapQ7A a)) :=
    isProbWeight_comp_perm hu swapQ7A
  have hperm4 : IsProbWeight (fun c => v (swapC4B c)) :=
    isProbWeight_comp_perm hv swapC4B
  have e7 : entropyW (fun a => u (swapQ7A a)) = entropyW u :=
    entropyW_comp_perm u swapQ7A
  have e4 : entropyW (fun c => v (swapC4B c)) = entropyW v :=
    entropyW_comp_perm v swapC4B
  refine ⟨entropyW_prod_three u v z hu hv hz, ?_, ?_⟩
  · rw [exchange_firstState_eq,
      entropyW_prod_three _ _ _ hperm7 hperm4 hz, e7, e4]
  · rw [exchange_finalState_eq,
      entropyW_prod_three u _ z hu hperm4 hz, e4]

/-- **(b) THE FACTOR-SUM ENTROPY IDENTITY for the exchange
sequence** (Tier T1): the sum of the three factor marginal
entropy changes (Q7, C4, R4) equals the total composite
entropy change across the sequence - and both sides are
`0`, because the visited states are product-form
(additivity), the marginals of product states are their
factors, and the only moved factor's entropy is unchanged
by relabeling. This is the factor-sum bookkeeping in the
pure-relabeling form: total production `0`, stated in
equality form, not a defect-carrying production claim. -/
theorem exchange_entropy_bookkeeping
    (u : (Fin 7 × Fin 2) → ℝ) (v : (Fin 4 × Fin 2) → ℝ)
    (z : Fin 4 → ℝ) (hu : IsProbWeight u) (hv : IsProbWeight v)
    (hz : IsProbWeight z) :
    (entropyW (q7Marg (loopFinalState (exchangeData u v z)))
        - entropyW (q7Marg (prodWeight u v z)))
      + ((entropyW (c4Marg (loopFinalState (exchangeData u v z)))
          - entropyW (c4Marg (prodWeight u v z)))
        + (entropyW (r4Marg (loopFinalState (exchangeData u v z)))
          - entropyW (r4Marg (prodWeight u v z))))
      = entropyW (loopFinalState (exchangeData u v z))
        - entropyW (prodWeight u v z)
    ∧ entropyW (loopFinalState (exchangeData u v z))
        - entropyW (prodWeight u v z) = 0 := by
  have hvswap : ∑ c, v (swapC4B c) = 1 :=
    (Equiv.sum_comp swapC4B v).trans hv.2
  have hperm4 : IsProbWeight (fun c => v (swapC4B c)) :=
    isProbWeight_comp_perm hv swapC4B
  have e4 : entropyW (fun c => v (swapC4B c)) = entropyW v :=
    entropyW_comp_perm v swapC4B
  have qmF : q7Marg (loopFinalState (exchangeData u v z)) = u := by
    rw [exchange_finalState_eq]
    exact q7Marg_prod u _ z hvswap hz.2
  have qmI : q7Marg (prodWeight u v z) = u :=
    q7Marg_prod u v z hv.2 hz.2
  have cmF : c4Marg (loopFinalState (exchangeData u v z))
      = fun c => v (swapC4B c) :=
    exchange_c4Marg_final u v z hu.2 hz.2
  have cmI : c4Marg (prodWeight u v z) = v :=
    c4Marg_prod u v z hu.2 hz.2
  have rmF : r4Marg (loopFinalState (exchangeData u v z)) = z := by
    rw [exchange_finalState_eq]
    exact r4Marg_prod u _ z hu.2 hvswap
  have rmI : r4Marg (prodWeight u v z) = z :=
    r4Marg_prod u v z hu.2 hv.2
  have hF : entropyW (loopFinalState (exchangeData u v z))
      = entropyW u + entropyW v + entropyW z := by
    rw [exchange_finalState_eq,
      entropyW_prod_three u _ z hu hperm4 hz, e4]
  have hI : entropyW (prodWeight u v z)
      = entropyW u + entropyW v + entropyW z :=
    entropyW_prod_three u v z hu hv hz
  constructor
  · rw [qmF, qmI, cmF, cmI, rmF, rmI, e4, hF, hI]
    ring
  · rw [hF, hI, sub_self]

/-- **The concrete instance** (Tier T1): at the basis
factor weights concentrated at the Q7 site `(0, 0)`, the
C4 site `(0, 0)`, and the R4 site `0`, the exchange data
is `FactorSelfContainedLoop`, its C4 marginal is
nontrivially moved, and it is NOT `StateClosed` - the
naming distinction and the non-vacuity are both exhibited
on one fully concrete instance, with no hypotheses left
open. -/
theorem exchange_concrete_factorSelfContained :
    FactorSelfContainedLoop
        (exchangeData
          (fun a => if a = ((0 : Fin 7), (0 : Fin 2)) then 1 else 0)
          (fun c => if c = ((0 : Fin 4), (0 : Fin 2)) then 1 else 0)
          (fun r => if r = (0 : Fin 4) then 1 else 0))
      ∧ c4Marg (loopFinalState
          (exchangeData
            (fun a => if a = ((0 : Fin 7), (0 : Fin 2)) then 1 else 0)
            (fun c => if c = ((0 : Fin 4), (0 : Fin 2)) then 1 else 0)
            (fun r => if r = (0 : Fin 4) then 1 else 0)))
        ≠ c4Marg (prodWeight
            (fun a => if a = ((0 : Fin 7), (0 : Fin 2)) then 1 else 0)
            (fun c => if c = ((0 : Fin 4), (0 : Fin 2)) then 1 else 0)
            (fun r => if r = (0 : Fin 4) then 1 else 0))
      ∧ ¬ StateClosed
          (exchangeData
            (fun a => if a = ((0 : Fin 7), (0 : Fin 2)) then 1 else 0)
            (fun c => if c = ((0 : Fin 4), (0 : Fin 2)) then 1 else 0)
            (fun r => if r = (0 : Fin 4) then 1 else 0)) := by
  have hne : (fun c => if c = ((0 : Fin 4), (0 : Fin 2))
        then (1 : ℝ) else 0) ((3 : Fin 4), (0 : Fin 2))
      ≠ (fun c => if c = ((0 : Fin 4), (0 : Fin 2))
        then (1 : ℝ) else 0) ((0 : Fin 4), (0 : Fin 2)) := by
    simp
  refine ⟨exchange_factorSelfContained _ _ _ (by simp) (by simp),
    exchange_c4Marg_ne _ _ _ (by simp) (by simp) hne,
    exchange_not_stateClosed _ _ _ (by simp) (by simp) hne⟩

#print axioms weightEnergy_perm
#print axioms permSteps_ledger_zero
#print axioms eigComp_exchangePi
#print axioms exchange_ledgerClosed
#print axioms exchange_energy_conserved
#print axioms exchange_finalState_eq
#print axioms exchange_q7Marg_returns
#print axioms exchange_c4Marg_ne
#print axioms exchange_not_stateClosed
#print axioms exchange_factorSelfContained
#print axioms entropyW_prod_three
#print axioms exchange_entropy_additivity_visited
#print axioms exchange_entropy_bookkeeping
#print axioms exchange_concrete_factorSelfContained

end ThetLogos
