import Mathlib.Tactic
import ThetLogos.RefractiveThermalEntropyPin

/-!
# ThetLogos.ThermalExpansionPin — nabla chaos of thermal expansion, in finite form

**Lane-grade pin. NO CLAIM. Pre-registered DIAL-INELIGIBLE; dials
0/4 under every outcome. Dial 2 = 0 under every outcome: expansion
here is growth of total mass under unnormalized bent weights on a
finite seat — not thermal expansion of a material, not a continuum
statement, not gravity. QTST — Zero's filed candidate name for a
continuum string completion — is NOT worn by this pin.**

Commissioned from Zero's fragment, filed verbatim 2026-11-21
04:02 EST: "nabla chaos of thermal expansion" — a fragment, never
completed by him, and not completed here. Queued by Zero
2026-11-21 04:03 EST ("Queue its scope behind RNE too"). Scope of
record: `nabla-chaos-thermal-expansion-scope-2026-11-21.md`
(T5 scope). Working label only — Zero names.

## The naming correction (the header does not wear the word as a result)

**K-NCTE-CHAOS — FIRED AT SCOPING.** This pin does not exhibit
chaos, and no finite or linear seat in-tree can. Two structural
reasons: (1) the count seat is a deterministic map on a FINITE
state space — every orbit is eventually periodic, so sensitive
dependence is impossible there, at any landscape, forever;
(2) the distribution seat iterates a LINEAR map (the bent kernel)
or an AFFINE map (the driven step) — eigenmodes decay, persist
periodically, or grow geometrically; no sensitive dependence, no
positive Lyapunov exponent, no aperiodic bounded orbit, in any
dimension. True chaos is a nonlinear continuum notion; no
nonlinear continuum dynamics object exists in-tree. Chaos stays
FRONTIER — flagged, never priced, and no brick of this pin is a
down payment on it. Zero's word "chaos" names the seeing in this
header and appears in NO statement below.

What the finite machinery honestly states, and what this pin
proves, is the residue at the boundary the fragment points at:

1. **Expansion** — the unnormalized bent weights genuinely grow
   total mass, at a seat-dependent rate: DIFFERENTIAL expansion
   (the RTE exhibit's flat seats expand by exactly 5 per step,
   its graded seat by exactly 4; the pulse's total mass runs
   1, 4, 20, 88, … with Perron factor exactly `1 + √13` — the
   unnormalized reading only).
2. **Non-settling** — at the contraction boundary (`Fin 2`, where
   row-normalization erases the refractive index entirely) the
   bent flow is exactly the swap: error multiplier exactly `−1`,
   period-2 forever, around a stationary rest point that no
   non-uniform start ever approaches.

## Audit verdicts carried on the face (fired at scoping, not build results)

- **K-NCTE-DRIVE — FIRED AT SCOPING.** The driven-train candidate
  dies as stated: RTE-3b's `drivenStep c` is affine in the
  distribution with linear part `bentStep / (1 + c)`, spectral
  radius `< 1` for every `c > 0`, so for every positive drive a
  unique standing pattern exists and every start approaches it
  (RTE proved the `c = 1` case: `exhibit_driven_standing`,
  standing at `(5/13, 5/13, 3/13)`). The only route past the
  affine verdict is a TIME-VARYING drive — the "thermal entropy
  shock timing" seeing's territory (filed 2026-11-20, flagged not
  fired), NOT this pin's. The joint is named here, not merged:
  no brick below depends on it, and no definition anticipates it.
- **No `|multiplier| > 1` mode exists on any normalized kernel**:
  `bentStep` is row-normalized by construction, and a
  row-stochastic kernel has spectral radius exactly `1`. On the
  distribution seat the only non-contraction available is the
  boundary — a nontrivial mode with multiplier exactly `−1`.
  Brick 1 exhibits it.
- **RTE's exhibit kernel contracts in EVERY mode** — the
  symmetric error mode at exactly `−3/5` (RTE-3a, cited) and the
  antisymmetric mode at exactly `−2/5` (Brick 3 below). No
  landscape change to that exhibit produces non-contraction;
  the boundary case lives on `Fin 2` or nowhere in this
  machinery.

## Ownership (K-NCTE-DUP fence)

Cited, never re-proved: RTE-3a's `exhibit_pulse_closed_form` and
its `−3/5` multiplier, RTE-3b's `exhibit_driven_standing`, RTE-2's
`exhibit_bent_stationary` (the moved rest point
`(5/16, 5/16, 3/8)`), `exhibit_bentStep_values`,
`exhibit_index_values`. RTE's `bentIter` is the exhibit instance
of this pin's `kernelIter` — the normalized kernel
`bentStep exhibitW exhibitPhi` iterated from the same pulse
`![0, 0, 1]` — cited here, not re-defined. HB-3's
`undamped_full_step_oscillates` is the COUNT seat's period-2;
Brick 1 states what is new over it: the distribution seat, the
index-erasure, and the `−1` error identity.

Definitions pinned before any verdict is computed; no definition
is repaired to force or soften an answer (the RTE-2 rule).
-/

namespace ThetLogos

/-- **The general kernel iterate** (definition): the distribution
after `n` steps of a step kernel `P` from the start `μ`, in the
row convention of RTE's pulse iterates:
`kernelIter P μ 0 = μ` and
`(kernelIter P μ (n + 1)) j = ∑ i, kernelIter P μ n i * P i j`.
RTE's `bentIter` is its exhibit instance — cited in the header,
not re-defined. -/
def kernelIter {V : Type*} [Fintype V] (P : V → V → ℝ) (μ : V → ℝ) :
    ℕ → V → ℝ
  | 0 => μ
  | (n + 1) => fun j => ∑ i, kernelIter P μ n i * P i j

/-- **The raw (unnormalized) pulse iterate** (definition): the
same pulse as RTE-3a — a delta of mass at the graded seat `2` —
iterated under the UNNORMALIZED bent weights
`bentWeight exhibitW exhibitPhi`. One pulse, two readings:
normalized it settles (RTE-3a); raw, it expands (Brick 2). -/
def rawIter : ℕ → Fin 3 → ℝ :=
  kernelIter (bentWeight exhibitW exhibitPhi) ![0, 0, 1]

/-- **The per-seat expansion factor** (definition): the row sum
of the unnormalized bent weights at seat `i` — the total mass one
unit seated at `i` becomes after one raw step; exactly the factor
that the row-normalization in `bentStep` divides away. -/
def expansionFactor {V : Type*} [Fintype V] (w : V → V → ℝ)
    (φ : V → ℝ) (i : V) : ℝ :=
  ∑ j, bentWeight w φ i j


-- ============================================================================
-- Brick 1 — the non-settling boundary, Fin 2: the index cannot act,
-- the bent kernel is the swap, the error multiplier is exactly −1
-- ============================================================================

/-- **K-NCTE-BEND2 FIRES** (proved — the pre-registered kill): on
`Fin 2`, row-normalization ERASES the refractive index for every
landscape. With positive off-diagonal weights and no self-weights
— each row of `bentWeight` has a single nonzero entry, its
off-diagonal — every row's bent weight divided by its own row sum
is `0` on the diagonal and `1` off it: the bent kernel IS the swap
kernel `!![0, 1; 1, 0]`, whatever `φ` says. Bending needs at
least three seats; on two, there is nothing to bend. The
zero-diagonal hypotheses are the scope audit's "single nonzero
entry" condition stated exactly (its brick text lists the
off-diagonal hypotheses; its audit prose asserts each row has a
single nonzero entry — on `Fin 2` that is `w 0 0 = 0` and
`w 1 1 = 0`; without them the claim is false: `w ≡ 1`, `φ ≡ 0`
gives `bentStep w φ 0 0 = 1 / 2`). -/
theorem bentStep_fin_two_swap (w : Fin 2 → Fin 2 → ℝ)
    (φ : Fin 2 → ℝ) (hw01 : 0 < w 0 1) (hw10 : 0 < w 1 0)
    (hd0 : w 0 0 = 0) (hd1 : w 1 1 = 0) :
    ∀ i j, bentStep w φ i j = !![0, 1; 1, 0] i j := by
  have hw : ∀ i j, 0 ≤ w i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hd0, hd1, le_of_lt hw01, le_of_lt hw10]
  have hr0 : refIndex w φ 0 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le one_pos (refIndex_ge_one w φ hw 0))
  have hr1 : refIndex w φ 1 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le one_pos (refIndex_ge_one w φ hw 1))
  have e00 : bentStep w φ 0 0 = 0 := by
    simp only [bentStep, Fin.sum_univ_two, bentWeight, hd0, hd1,
      zero_mul, zero_add, add_zero, zero_div]
  have e01 : bentStep w φ 0 1 = 1 := by
    simp only [bentStep, Fin.sum_univ_two, bentWeight, hd0, hd1,
      zero_mul, zero_add, add_zero]
    rw [div_self (mul_ne_zero (ne_of_gt hw01) hr1)]
  have e10 : bentStep w φ 1 0 = 1 := by
    simp only [bentStep, Fin.sum_univ_two, bentWeight, hd0, hd1,
      zero_mul, zero_add, add_zero]
    rw [div_self (mul_ne_zero (ne_of_gt hw10) hr0)]
  have e11 : bentStep w φ 1 1 = 0 := by
    simp only [bentStep, Fin.sum_univ_two, bentWeight, hd0, hd1,
      zero_mul, zero_add, add_zero, zero_div]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [e00, e01, e10, e11, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]

/-- **The swap flow's period-2 closed form** (proved): from any
start `μ`, the swap kernel's iterates are exactly `μ` at even
steps and the seat-swap `![μ 1, μ 0]` at odd steps — perpetual
oscillation, exhibited as a closed form, not estimated. -/
theorem swapIter_closed_form (w : Fin 2 → Fin 2 → ℝ)
    (φ : Fin 2 → ℝ) (hw01 : 0 < w 0 1) (hw10 : 0 < w 1 0)
    (hd0 : w 0 0 = 0) (hd1 : w 1 1 = 0) (μ : Fin 2 → ℝ) (n : ℕ) :
    kernelIter (bentStep w φ) μ (2 * n) = μ
    ∧ kernelIter (bentStep w φ) μ (2 * n + 1) = ![μ 1, μ 0] := by
  have hswap := bentStep_fin_two_swap w φ hw01 hw10 hd0 hd1
  have hstep : ∀ ν : Fin 2 → ℝ,
      kernelIter (bentStep w φ) ν 1 = ![ν 1, ν 0] := by
    intro ν
    have hunfold : ∀ j, kernelIter (bentStep w φ) ν 1 j
        = ∑ i, ν i * bentStep w φ i j := fun j => rfl
    funext j
    rw [hunfold j]
    fin_cases j <;>
      simp [Fin.sum_univ_two, hswap, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  induction n with
  | zero => exact ⟨rfl, hstep μ⟩
  | succ n ih =>
    obtain ⟨ihe, iho⟩ := ih
    have hev : kernelIter (bentStep w φ) μ (2 * (n + 1)) = μ := by
      have h1 : kernelIter (bentStep w φ) μ (2 * (n + 1))
          = kernelIter (bentStep w φ)
              (kernelIter (bentStep w φ) μ (2 * n + 1)) 1 := rfl
      rw [h1, iho, hstep]
      funext i
      fin_cases i <;>
        simp [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
    refine ⟨hev, ?_⟩
    have h1 : kernelIter (bentStep w φ) μ (2 * (n + 1) + 1)
        = kernelIter (bentStep w φ)
            (kernelIter (bentStep w φ) μ (2 * (n + 1))) 1 := rfl
    rw [h1, hev, hstep]

/-- **The error identity** (proved): at every step `n`, the swap
flow's error is exactly `(−1)ⁿ` times the initial error — the
multiplier is exactly `−1`; the contraction is gone, exhibited as
an identity, not estimated. -/
theorem swap_error_multiplier (w : Fin 2 → Fin 2 → ℝ)
    (φ : Fin 2 → ℝ) (hw01 : 0 < w 0 1) (hw10 : 0 < w 1 0)
    (hd0 : w 0 0 = 0) (hd1 : w 1 1 = 0) (μ : Fin 2 → ℝ) (n : ℕ) :
    kernelIter (bentStep w φ) μ n 0 - kernelIter (bentStep w φ) μ n 1
      = (-1) ^ n * (μ 0 - μ 1) := by
  have hswap := bentStep_fin_two_swap w φ hw01 hw10 hd0 hd1
  have h0 : ∀ m : ℕ, kernelIter (bentStep w φ) μ (m + 1) 0
      = kernelIter (bentStep w φ) μ m 1 := by
    intro m
    have hunfold : kernelIter (bentStep w φ) μ (m + 1) 0
        = ∑ i, kernelIter (bentStep w φ) μ m i
            * bentStep w φ i 0 := rfl
    rw [hunfold, Fin.sum_univ_two]
    simp [hswap, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
  have h1 : ∀ m : ℕ, kernelIter (bentStep w φ) μ (m + 1) 1
      = kernelIter (bentStep w φ) μ m 0 := by
    intro m
    have hunfold : kernelIter (bentStep w φ) μ (m + 1) 1
        = ∑ i, kernelIter (bentStep w φ) μ m i
            * bentStep w φ i 1 := rfl
    rw [hunfold, Fin.sum_univ_two]
    simp [hswap, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
  induction n with
  | zero => simp only [kernelIter, pow_zero, one_mul]
  | succ n ih =>
    rw [h0, h1, pow_succ]
    have hih : kernelIter (bentStep w φ) μ n 1
        - kernelIter (bentStep w φ) μ n 0
        = -((-1) ^ n * (μ 0 - μ 1)) := by linarith [ih]
    rw [hih]; ring

/-- **K-NCTE-SETTLE FIRES** (proved — the pre-registered kill):
the swap flow's rest point EXISTS, is stationary, and its shape
is unique — every stationary distribution is symmetric, so with
mass `1` it is the uniform distribution — and it is approached by
NO non-uniform start: a non-uniform start's iterates fail to
converge to anything at all, since the even iterates are
constantly `μ` and the odd iterates constantly its swap.
Existence of a rest point is not settling — RNE's lesson, here at
full strength. (HB-3's `undamped_full_step_oscillates` is the
COUNT seat's period-2; what is new here is the distribution seat,
the index-erasure that forces the swap, and the `−1` error
identity above.) -/
theorem swap_not_settling (w : Fin 2 → Fin 2 → ℝ)
    (φ : Fin 2 → ℝ) (hw01 : 0 < w 0 1) (hw10 : 0 < w 1 0)
    (hd0 : w 0 0 = 0) (hd1 : w 1 1 = 0) :
    IsStationary (bentStep w φ) (fun _ => 1 / 2)
    ∧ (∀ π : Fin 2 → ℝ, IsStationary (bentStep w φ) π → π 0 = π 1)
    ∧ (∀ (μ : Fin 2 → ℝ), μ 0 ≠ μ 1 → ∀ π : Fin 2 → ℝ,
        ¬ Filter.Tendsto (fun n => kernelIter (bentStep w φ) μ n)
            Filter.atTop (nhds π)) := by
  have hswap := bentStep_fin_two_swap w φ hw01 hw10 hd0 hd1
  refine ⟨?_, ?_, ?_⟩
  · intro j
    fin_cases j <;>
      simp [IsStationary, Fin.sum_univ_two, hswap, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        <;> ring
  · intro π hπ
    have h := hπ 0
    simp [IsStationary, Fin.sum_univ_two, hswap, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      at h
    linarith
  · intro μ hμ π hT
    have hEvenT : Filter.Tendsto (fun n : ℕ => 2 * n)
        Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_atTop.mpr
        (fun b => ⟨b, fun n hn => by omega⟩)
    have hOddT : Filter.Tendsto (fun n : ℕ => 2 * n + 1)
        Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_atTop.mpr
        (fun b => ⟨b, fun n hn => by omega⟩)
    have hE := hT.comp hEvenT
    have hO := hT.comp hOddT
    simp only [Function.comp_def] at hE hO
    have hE' : Filter.Tendsto (fun _ : ℕ => μ) Filter.atTop
        (nhds π) := by
      have he : (fun n => kernelIter (bentStep w φ) μ (2 * n))
          = fun _ => μ :=
        funext fun n =>
          (swapIter_closed_form w φ hw01 hw10 hd0 hd1 μ n).1
      rwa [he] at hE
    have hO' : Filter.Tendsto (fun _ : ℕ => ![μ 1, μ 0])
        Filter.atTop (nhds π) := by
      have ho : (fun n => kernelIter (bentStep w φ) μ (2 * n + 1))
          = fun _ => ![μ 1, μ 0] :=
        funext fun n =>
          (swapIter_closed_form w φ hw01 hw10 hd0 hd1 μ n).2
      rwa [ho] at hO
    have hπμ : π = μ := tendsto_nhds_unique hE' tendsto_const_nhds
    have hπs : π = ![μ 1, μ 0] :=
      tendsto_nhds_unique hO' tendsto_const_nhds
    have hcontra : μ 0 = μ 1 := by
      have h : μ = ![μ 1, μ 0] := hπμ.symm.trans hπs
      have h0 := congrFun h 0
      simpa using h0
    exact hμ hcontra

-- ============================================================================
-- Brick 2 — differential expansion on the RTE exhibit: factors 5, 5, 4,
-- the symmetric line, the (1 + √13) closed form, the mass ratio
-- ============================================================================

/-- **The exhibit's bent weights, entry by entry** (proved): the
flat seats' rows carry bent weights `(0, 2, 3)` and `(2, 0, 3)`;
the graded seat's row is `(2, 2, 0)`. The row sums — `5, 5, 4` —
are the expansion factors of the next theorem. -/
theorem exhibit_bentWeight_values :
    ∀ i j, bentWeight exhibitW exhibitPhi i j
      = ![![0, 2, 3], ![2, 0, 3], ![2, 2, 0]] i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bentWeight, refIndex, Fin.sum_univ_three, exhibitW,
      exhibitPhi, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]

/-- **K-NCTE-GROWTH fires in its fence form** (proved — the
pre-registered naming fence): the RTE exhibit's expansion factors
are exactly `![5, 5, 4]` — each flat seat's unit mass becomes `5`
after one raw step, the graded seat's becomes `4`: the expansion
is DIFFERENTIAL, seats pulling apart at different rates, the
finite form of the fragment's irregular gradient. Expansion is a
property of the UNNORMALIZED weights; the normalized `bentStep`
conserves total mass exactly, and any text calling RTE's flow
itself expansive is false. This pin's expansion theorems are
stated about `rawIter` and `expansionFactor` only. -/
theorem exhibit_expansion_factors :
    expansionFactor exhibitW exhibitPhi = ![5, 5, 4] := by
  funext i
  fin_cases i <;>
    norm_num [expansionFactor, bentWeight, refIndex,
      Fin.sum_univ_three, exhibitW, exhibitPhi, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

/-- **The raw pulse stays on the symmetric line** (proved): at
every step the two flat seats of the raw iterate agree — the same
exhibit symmetry RTE-3a used, in the unnormalized reading. -/
theorem exhibit_rawIter_symmetric (n : ℕ) :
    rawIter n 0 = rawIter n 1 := by
  have hstep : ∀ (m : ℕ) (j : Fin 3), rawIter (m + 1) j
      = ∑ i, rawIter m i * bentWeight exhibitW exhibitPhi i j :=
    fun m j => rfl
  induction n with
  | zero =>
    have hr0 : rawIter 0 = ![0, 0, 1] := rfl
    rw [hr0]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
  | succ n ih =>
    rw [hstep n 0, hstep n 1, Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [exhibit_bentWeight_values, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rw [ih]; ring

/-- **The raw pulse's closed form** (proved): at every step `n`,
`√13 * rawIter n 0 = (1 + √13)ⁿ − (1 − √13)ⁿ` and
`2√13 * rawIter n 2
  = (√13 − 1)(1 + √13)ⁿ + (√13 + 1)(1 − √13)ⁿ`
— the two modes of the symmetric sector map `((2, 2), (6, 0))`
(`a' = 2a + 2b`, `b' = 6a`), whose characteristic roots are
`1 ± √13`. First values: `rawIter n 0` runs `0, 2, 4, 32, …` and
`rawIter n 2` runs `1, 0, 12, 24, …`. The `√13` factors are
carried on the left so that no division by an irrational appears
in the statement. -/
theorem exhibit_rawIter_closed_form (n : ℕ) :
    Real.sqrt 13 * rawIter n 0
      = (1 + Real.sqrt 13) ^ n - (1 - Real.sqrt 13) ^ n
    ∧ 2 * Real.sqrt 13 * rawIter n 2
      = (Real.sqrt 13 - 1) * (1 + Real.sqrt 13) ^ n
        + (Real.sqrt 13 + 1) * (1 - Real.sqrt 13) ^ n := by
  have hs : Real.sqrt 13 * Real.sqrt 13 = 13 :=
    Real.mul_self_sqrt (by norm_num)
  have hstep : ∀ (m : ℕ) (j : Fin 3), rawIter (m + 1) j
      = ∑ i, rawIter m i * bentWeight exhibitW exhibitPhi i j :=
    fun m j => rfl
  have hrec0 : ∀ m : ℕ, rawIter (m + 1) 0
      = 2 * rawIter m 0 + 2 * rawIter m 2 := by
    intro m
    rw [hstep m 0, Fin.sum_univ_three]
    simp only [exhibit_bentWeight_values, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rw [← exhibit_rawIter_symmetric m]; ring
  have hrec2 : ∀ m : ℕ, rawIter (m + 1) 2
      = 6 * rawIter m 0 := by
    intro m
    rw [hstep m 2, Fin.sum_univ_three]
    simp only [exhibit_bentWeight_values, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rw [← exhibit_rawIter_symmetric m]; ring
  have hrec0' : ∀ m : ℕ, rawIter (m + 2) 0
      = 2 * rawIter (m + 1) 0 + 12 * rawIter m 0 := by
    intro m
    have h1 : rawIter (m + 2) 0 = 2 * rawIter (m + 1) 0
        + 2 * rawIter (m + 1) 2 := hrec0 (m + 1)
    rw [h1, hrec2 m]; ring
  have hrec2' : ∀ m : ℕ, rawIter (m + 2) 2
      = 2 * rawIter (m + 1) 2 + 12 * rawIter m 2 := by
    intro m
    have h1 : rawIter (m + 2) 2 = 6 * rawIter (m + 1) 0 :=
      hrec2 (m + 1)
    rw [h1, hrec0 m, hrec2 m]; ring
  have hroot : ∀ r : ℝ, r * r = 2 * r + 12 →
      ∀ m : ℕ, r ^ (m + 2) = 2 * r ^ (m + 1) + 12 * r ^ m := by
    intro r hr m
    have h : r ^ (m + 2) = r ^ m * (r * r) := by
      rw [pow_add, pow_two]
    rw [h, hr]; ring
  have hr1 : (1 + Real.sqrt 13) * (1 + Real.sqrt 13)
      = 2 * (1 + Real.sqrt 13) + 12 := by
    have h : (1 + Real.sqrt 13) * (1 + Real.sqrt 13)
        = 1 + 2 * Real.sqrt 13 + Real.sqrt 13 * Real.sqrt 13 := by
      ring
    rw [h, hs]; ring
  have hr2 : (1 - Real.sqrt 13) * (1 - Real.sqrt 13)
      = 2 * (1 - Real.sqrt 13) + 12 := by
    have h : (1 - Real.sqrt 13) * (1 - Real.sqrt 13)
        = 1 - 2 * Real.sqrt 13 + Real.sqrt 13 * Real.sqrt 13 := by
      ring
    rw [h, hs]; ring
  have hr0 : rawIter 0 = ![0, 0, 1] := rfl
  have key : ∀ n : ℕ,
      (Real.sqrt 13 * rawIter n 0
        = (1 + Real.sqrt 13) ^ n - (1 - Real.sqrt 13) ^ n
      ∧ 2 * Real.sqrt 13 * rawIter n 2
        = (Real.sqrt 13 - 1) * (1 + Real.sqrt 13) ^ n
          + (Real.sqrt 13 + 1) * (1 - Real.sqrt 13) ^ n)
      ∧ (Real.sqrt 13 * rawIter (n + 1) 0
        = (1 + Real.sqrt 13) ^ (n + 1) - (1 - Real.sqrt 13) ^ (n + 1)
      ∧ 2 * Real.sqrt 13 * rawIter (n + 1) 2
        = (Real.sqrt 13 - 1) * (1 + Real.sqrt 13) ^ (n + 1)
          + (Real.sqrt 13 + 1) * (1 - Real.sqrt 13) ^ (n + 1)) := by
    intro n
    induction n with
    | zero =>
      have e0 : rawIter 0 0 = 0 := by
        rw [hr0]; norm_num [Matrix.cons_val_zero]
      have e2 : rawIter 0 2 = 1 := by
        rw [hr0]
        norm_num [Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.head_cons]
      have e1 : rawIter (0 + 1) 0 = 2 := by
        rw [hrec0 0, e0, e2]; norm_num
      have e3 : rawIter (0 + 1) 2 = 0 := by
        rw [hrec2 0, e0]; norm_num
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · rw [e0]; simp only [pow_zero, mul_zero, sub_self]
      · rw [e2]; simp only [pow_zero, mul_one]; ring
      · show Real.sqrt 13 * rawIter (0 + 1) 0
            = (1 + Real.sqrt 13) ^ 1 - (1 - Real.sqrt 13) ^ 1
        rw [e1]; simp only [pow_one]; ring
      · show 2 * Real.sqrt 13 * rawIter (0 + 1) 2
            = (Real.sqrt 13 - 1) * (1 + Real.sqrt 13) ^ 1
              + (Real.sqrt 13 + 1) * (1 - Real.sqrt 13) ^ 1
        rw [e3]; simp only [pow_one]; ring
    | succ n ih =>
      obtain ⟨⟨ihn0, ihn2⟩, ⟨ihn10, ihn12⟩⟩ := ih
      refine ⟨⟨ihn10, ihn12⟩, ⟨?_, ?_⟩⟩
      · show Real.sqrt 13 * rawIter (n + 2) 0
            = (1 + Real.sqrt 13) ^ (n + 2)
              - (1 - Real.sqrt 13) ^ (n + 2)
        have e1 : Real.sqrt 13 * rawIter (n + 2) 0
            = 2 * (Real.sqrt 13 * rawIter (n + 1) 0)
              + 12 * (Real.sqrt 13 * rawIter n 0) := by
          rw [hrec0' n]; ring
        rw [e1, ihn0, ihn10, hroot _ hr1, hroot _ hr2]; ring
      · show 2 * Real.sqrt 13 * rawIter (n + 2) 2
            = (Real.sqrt 13 - 1) * (1 + Real.sqrt 13) ^ (n + 2)
              + (Real.sqrt 13 + 1) * (1 - Real.sqrt 13) ^ (n + 2)
        have e2 : 2 * Real.sqrt 13 * rawIter (n + 2) 2
            = 2 * (2 * Real.sqrt 13 * rawIter (n + 1) 2)
              + 12 * (2 * Real.sqrt 13 * rawIter n 2) := by
          rw [hrec2' n]; ring
        rw [e2, ihn2, ihn12, hroot _ hr1, hroot _ hr2]; ring
  exact (key n).1

/-- **The raw pulse's total mass and its growth ratio** (proved):
the total mass of `rawIter n` is `2 * rawIter n 0 + rawIter n 2`
— the sequence `1, 4, 20, 88, …` — and the step ratio of the mass
tends to the Perron root `1 + √13`: the differential expansion's
growth factor, stated in the unnormalized reading only
(K-NCTE-GROWTH's fence applies to the whole theorem). -/
theorem exhibit_raw_mass_growth :
    (∀ n : ℕ, ∑ j, rawIter n j = 2 * rawIter n 0 + rawIter n 2)
    ∧ Filter.Tendsto
        (fun n => (∑ j, rawIter (n + 1) j) / (∑ j, rawIter n j))
        Filter.atTop (nhds (1 + Real.sqrt 13)) := by
  have hstep : ∀ (m : ℕ) (j : Fin 3), rawIter (m + 1) j
      = ∑ i, rawIter m i * bentWeight exhibitW exhibitPhi i j :=
    fun m j => rfl
  have hrec0 : ∀ m : ℕ, rawIter (m + 1) 0
      = 2 * rawIter m 0 + 2 * rawIter m 2 := by
    intro m
    rw [hstep m 0, Fin.sum_univ_three]
    simp only [exhibit_bentWeight_values, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rw [← exhibit_rawIter_symmetric m]; ring
  have hrec2 : ∀ m : ℕ, rawIter (m + 1) 2
      = 6 * rawIter m 0 := by
    intro m
    rw [hstep m 2, Fin.sum_univ_three]
    simp only [exhibit_bentWeight_values, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rw [← exhibit_rawIter_symmetric m]; ring
  have hmass : ∀ n : ℕ, ∑ j, rawIter n j
      = 2 * rawIter n 0 + rawIter n 2 := by
    intro n
    rw [Fin.sum_univ_three, ← exhibit_rawIter_symmetric n]; ring
  have hr0 : rawIter 0 = ![0, 0, 1] := rfl
  have hnonneg : ∀ n : ℕ, 0 ≤ rawIter n 0 ∧ 0 ≤ rawIter n 2
      ∧ 1 ≤ rawIter n 0 + rawIter n 2 := by
    intro n
    induction n with
    | zero =>
      have e0 : rawIter 0 0 = 0 := by
        rw [hr0]; norm_num [Matrix.cons_val_zero]
      have e2 : rawIter 0 2 = 1 := by
        rw [hr0]
        norm_num [Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.head_cons]
      rw [e0, e2]; norm_num
    | succ n ih =>
      obtain ⟨ih0, ih2, ihs⟩ := ih
      rw [hrec0 n, hrec2 n]
      refine ⟨by linarith, by linarith, by linarith⟩
  have hpos : ∀ n : ℕ, 0 < ∑ j, rawIter n j := by
    intro n
    rw [hmass n]
    obtain ⟨h0, h2, hs⟩ := hnonneg n
    linarith
  have hM : ∀ n : ℕ, 2 * Real.sqrt 13 * (∑ j, rawIter n j)
      = (3 + Real.sqrt 13) * (1 + Real.sqrt 13) ^ n
        + (Real.sqrt 13 - 3) * (1 - Real.sqrt 13) ^ n := by
    intro n
    rw [hmass n]
    obtain ⟨h1, h2⟩ := exhibit_rawIter_closed_form n
    have e : 2 * Real.sqrt 13 * (2 * rawIter n 0 + rawIter n 2)
        = 2 * (2 * (Real.sqrt 13 * rawIter n 0))
          + (2 * Real.sqrt 13 * rawIter n 2) := by ring
    rw [e, h1, h2]; ring
  have hspos : (0:ℝ) < Real.sqrt 13 := Real.sqrt_pos.mpr (by norm_num)
  have h3 : (3:ℝ) < Real.sqrt 13 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hne : (1:ℝ) + Real.sqrt 13 ≠ 0 := ne_of_gt (by linarith)
  have hE : ∀ n : ℕ,
      (3 + Real.sqrt 13) * (1 + Real.sqrt 13) ^ n
        + (Real.sqrt 13 - 3) * (1 - Real.sqrt 13) ^ n
      = (1 + Real.sqrt 13) ^ n
        * ((3 + Real.sqrt 13)
          + (Real.sqrt 13 - 3)
            * ((1 - Real.sqrt 13) / (1 + Real.sqrt 13)) ^ n) := by
    intro n
    have hrq : (1 + Real.sqrt 13)
        * ((1 - Real.sqrt 13) / (1 + Real.sqrt 13))
        = 1 - Real.sqrt 13 := by
      rw [mul_comm, div_mul_cancel₀ _ hne]
    have h2 : (1 - Real.sqrt 13) ^ n
        = (1 + Real.sqrt 13) ^ n
          * ((1 - Real.sqrt 13) / (1 + Real.sqrt 13)) ^ n := by
      rw [← mul_pow, hrq]
    rw [h2]; ring
  have hEpos : ∀ n : ℕ, 0 < (3 + Real.sqrt 13) * (1 + Real.sqrt 13) ^ n
        + (Real.sqrt 13 - 3) * (1 - Real.sqrt 13) ^ n := by
    intro n
    rw [← hM n]
    exact mul_pos (by linarith) (hpos n)
  have hDpos : ∀ n : ℕ, 0 < (3 + Real.sqrt 13)
      + (Real.sqrt 13 - 3)
        * ((1 - Real.sqrt 13) / (1 + Real.sqrt 13)) ^ n := by
    intro n
    have h1 : (0:ℝ) < (1 + Real.sqrt 13) ^ n :=
      pow_pos (by linarith) n
    have h2 := hEpos n
    rw [hE n] at h2
    exact (mul_pos_iff_of_pos_left h1).mp h2
  have hq : |(1 - Real.sqrt 13) / (1 + Real.sqrt 13)| < 1 := by
    have hp : (0:ℝ) < 1 + Real.sqrt 13 := by linarith
    rw [abs_div, abs_of_pos hp]
    have hn : |(1:ℝ) - Real.sqrt 13| = Real.sqrt 13 - 1 := by
      rw [abs_of_neg (by linarith)]; ring
    rw [hn, div_lt_one hp]; linarith
  have hqlim : Filter.Tendsto
      (fun n => ((1 - Real.sqrt 13) / (1 + Real.sqrt 13)) ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq
  have hD : Filter.Tendsto
      (fun n => (3 + Real.sqrt 13)
        + (Real.sqrt 13 - 3)
          * ((1 - Real.sqrt 13) / (1 + Real.sqrt 13)) ^ n)
      Filter.atTop (nhds (3 + Real.sqrt 13)) := by
    have h1 := hqlim.const_mul (Real.sqrt 13 - 3)
    have h2 : Filter.Tendsto
        (fun n => (3 + Real.sqrt 13)
          + (Real.sqrt 13 - 3)
            * ((1 - Real.sqrt 13) / (1 + Real.sqrt 13)) ^ n)
        Filter.atTop
        (nhds (3 + Real.sqrt 13 + (Real.sqrt 13 - 3) * 0)) :=
      tendsto_const_nhds.add h1
    simpa using h2
  have hD1 : Filter.Tendsto
      (fun n => (3 + Real.sqrt 13)
        + (Real.sqrt 13 - 3)
          * ((1 - Real.sqrt 13) / (1 + Real.sqrt 13)) ^ (n + 1))
      Filter.atTop (nhds (3 + Real.sqrt 13)) := by
    have h := hD.comp (Filter.tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def] using h
  have hne3 : (3:ℝ) + Real.sqrt 13 ≠ 0 := ne_of_gt (by linarith)
  have hlim : Filter.Tendsto
      ((fun n => (1 + Real.sqrt 13)
          * ((3 + Real.sqrt 13)
            + (Real.sqrt 13 - 3)
              * ((1 - Real.sqrt 13) / (1 + Real.sqrt 13)) ^ (n + 1)))
        / (fun n => (3 + Real.sqrt 13)
            + (Real.sqrt 13 - 3)
              * ((1 - Real.sqrt 13) / (1 + Real.sqrt 13)) ^ n))
      Filter.atTop (nhds (1 + Real.sqrt 13)) := by
    have h := (hD1.const_mul (1 + Real.sqrt 13)).div hD hne3
    have htarget : (1 + Real.sqrt 13) * (3 + Real.sqrt 13)
        / (3 + Real.sqrt 13) = 1 + Real.sqrt 13 := by
      rw [eq_comm, eq_div_iff_mul_eq hne3]
    simpa only [htarget] using h
  refine ⟨hmass, ?_⟩
  apply Filter.Tendsto.congr' _ hlim
  apply Filter.Eventually.of_forall
  intro n
  show (1 + Real.sqrt 13)
      * ((3 + Real.sqrt 13) + (Real.sqrt 13 - 3)
          * ((1 - Real.sqrt 13) / (1 + Real.sqrt 13)) ^ (n + 1))
      / ((3 + Real.sqrt 13) + (Real.sqrt 13 - 3)
          * ((1 - Real.sqrt 13) / (1 + Real.sqrt 13)) ^ n)
    = (∑ j, rawIter (n + 1) j) / (∑ j, rawIter n j)
  have hs2 : (2:ℝ) * Real.sqrt 13 ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt hspos)
  have hME : ∀ k : ℕ, (∑ j, rawIter k j)
      = ((3 + Real.sqrt 13) * (1 + Real.sqrt 13) ^ k
        + (Real.sqrt 13 - 3) * (1 - Real.sqrt 13) ^ k)
        / (2 * Real.sqrt 13) := by
    intro k
    rw [eq_div_iff_mul_eq hs2, mul_comm]; exact hM k
  rw [hME (n + 1), hME n, hE (n + 1), hE n]
  have hr1n : (1 + Real.sqrt 13) ^ n ≠ 0 :=
    ne_of_gt (pow_pos (by linarith) n)
  have hDn : (3 + Real.sqrt 13)
      + (Real.sqrt 13 - 3)
        * ((1 - Real.sqrt 13) / (1 + Real.sqrt 13)) ^ n ≠ 0 :=
    ne_of_gt (hDpos n)
  have hDn' : (1 + Real.sqrt 13) ^ n
      * ((3 + Real.sqrt 13)
        + (Real.sqrt 13 - 3)
          * ((1 - Real.sqrt 13) / (1 + Real.sqrt 13)) ^ n)
      / (2 * Real.sqrt 13) ≠ 0 :=
    div_ne_zero (mul_ne_zero hr1n hDn) hs2
  field_simp [hr1n, hDn, hDn', hs2]
  rw [pow_succ]
  ring

-- ============================================================================
-- Brick 3 — the exhibit's full mode picture, and the boundary stated once
-- ============================================================================

/-- **The exhibit kernel's antisymmetric mode contracts at
exactly `−2/5`** (proved): the bent kernel sends the
antisymmetric error shape `(a, −a, 0)` to `−2/5` of itself, seat
by seat. Together with RTE-3a's symmetric multiplier `−3/5`
(cited, never re-proved), EVERY error mode of the exhibit kernel
contracts — the exhibit carries no non-contracting mode, which
is why Brick 1's boundary case had to live on `Fin 2`. -/
theorem exhibit_bentStep_antisymmetric_mode (a : ℝ) (j : Fin 3) :
    ∑ i, ![a, -a, 0] i * bentStep exhibitW exhibitPhi i j
      = ![(-2 / 5) * a, (2 / 5) * a, 0] j := by
  obtain ⟨k00, k01, k02, k10, k11, k12, k20, k21, k22⟩ :=
    exhibit_bentStep_values
  fin_cases j <;>
    simp [Fin.sum_univ_three, k00, k01, k02, k10, k11, k12, k20,
      k21, k22, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] <;> ring

/-- **Every start's iterates converge to the moved rest point**
(proved — assembled from the two modes and RTE's stationary
point, all cited or proved above): a distribution `μ` on the
exhibit decomposes as its mass times the moved rest point
`(5/16, 5/16, 3/8)`, plus a symmetric error (multiplier `−3/5`
per step) plus an antisymmetric error (multiplier `−2/5` per
step); both errors die geometrically, so the iterates tend to
the rest point itself. The closed form is proved by induction;
the symmetric mode's one-step action is computed from
`exhibit_bentStep_values` (cited), the antisymmetric one from
the mode theorem above, and stationarity is RTE-2's
`exhibit_bent_stationary` (cited). -/
theorem exhibit_kernelIter_converges (μ : Fin 3 → ℝ)
    (hμ : ∑ i, μ i = 1) :
    Filter.Tendsto
      (fun n => kernelIter (bentStep exhibitW exhibitPhi) μ n)
      Filter.atTop (nhds ![5 / 16, 5 / 16, 3 / 8]) := by
  set m := μ 0 + μ 1 + μ 2 with hm_def
  set s := (μ 0 + μ 1) / 2 - (μ 0 + μ 1 + μ 2) * (5 / 16) with hs_def
  set t := (μ 0 - μ 1) / 2 with ht_def
  have hm1 : m = 1 := by
    rw [hm_def, ← Fin.sum_univ_three]; exact hμ
  have hP0 : ∀ j : Fin 3,
      ∑ i, ![5 / 16, 5 / 16, 3 / 8] i
          * bentStep exhibitW exhibitPhi i j
        = ![5 / 16, 5 / 16, 3 / 8] j :=
    fun j => exhibit_bent_stationary j
  have hPs : ∀ j : Fin 3,
      ∑ i, ![1, 1, -2] i * bentStep exhibitW exhibitPhi i j
        = (-3 / 5) * ![1, 1, -2] j := by
    intro j
    obtain ⟨k00, k01, k02, k10, k11, k12, k20, k21, k22⟩ :=
      exhibit_bentStep_values
    fin_cases j <;>
      simp [Fin.sum_univ_three, k00, k01, k02, k10, k11, k12, k20,
        k21, k22, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons] <;> ring
  have hPa : ∀ j : Fin 3,
      ∑ i, ![1, -1, 0] i * bentStep exhibitW exhibitPhi i j
        = (-2 / 5) * ![1, -1, 0] j := by
    intro j
    have h := exhibit_bentStep_antisymmetric_mode 1 j
    rw [h]
    fin_cases j <;>
      simp [Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons] <;> ring
  have hdec : ∀ j : Fin 3, μ j
      = m * ![5 / 16, 5 / 16, 3 / 8] j + s * ![1, 1, -2] j
        + t * ![1, -1, 0] j := by
    intro j
    fin_cases j <;>
      simp [hm_def, hs_def, ht_def, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] <;> ring
  have hcf : ∀ (n : ℕ) (j : Fin 3),
      kernelIter (bentStep exhibitW exhibitPhi) μ n j
        = m * ![5 / 16, 5 / 16, 3 / 8] j
          + (-3 / 5) ^ n * (s * ![1, 1, -2] j)
          + (-2 / 5) ^ n * (t * ![1, -1, 0] j) := by
    intro n
    induction n with
    | zero =>
      intro j
      have h0 : kernelIter (bentStep exhibitW exhibitPhi) μ 0 j
          = μ j := rfl
      rw [h0, hdec j]
      simp
    | succ n ih =>
      intro j
      have hstep : kernelIter (bentStep exhibitW exhibitPhi) μ
            (n + 1) j
          = ∑ i, kernelIter (bentStep exhibitW exhibitPhi) μ n i
              * bentStep exhibitW exhibitPhi i j := rfl
      rw [hstep]
      have hsum : (∑ i, kernelIter (bentStep exhibitW exhibitPhi)
              μ n i * bentStep exhibitW exhibitPhi i j)
          = ∑ i, (m * ![5 / 16, 5 / 16, 3 / 8] i
              + (-3 / 5) ^ n * (s * ![1, 1, -2] i)
              + (-2 / 5) ^ n * (t * ![1, -1, 0] i))
              * bentStep exhibitW exhibitPhi i j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [ih i]
      rw [hsum]
      simp only [add_mul, Finset.sum_add_distrib, mul_assoc,
        ← Finset.mul_sum]
      rw [hP0 j, hPs j, hPa j, pow_succ, pow_succ]
      ring
  apply tendsto_pi_nhds.mpr
  intro j
  show Filter.Tendsto
    (fun n => kernelIter (bentStep exhibitW exhibitPhi) μ n j)
    Filter.atTop (nhds (![5 / 16, 5 / 16, 3 / 8] j))
  have hlim0 : Filter.Tendsto (fun n => (-3 / 5 : ℝ) ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  have hlim1 : Filter.Tendsto (fun n => (-2 / 5 : ℝ) ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  have h2 : Filter.Tendsto
      (fun n => m * ![5 / 16, 5 / 16, 3 / 8] j
        + (-3 / 5) ^ n * (s * ![1, 1, -2] j)
        + (-2 / 5) ^ n * (t * ![1, -1, 0] j))
      Filter.atTop
      (nhds (m * ![5 / 16, 5 / 16, 3 / 8] j + 0 + 0)) := by
    apply Filter.Tendsto.add
    apply Filter.Tendsto.add
    · exact tendsto_const_nhds
    · simpa using hlim0.mul tendsto_const_nhds
    · simpa using hlim1.mul tendsto_const_nhds
  have hlim : m * ![5 / 16, 5 / 16, 3 / 8] j + 0 + 0
      = ![5 / 16, 5 / 16, 3 / 8] j := by simp [hm1]
  rw [hlim] at h2
  have h3 : (fun n => kernelIter (bentStep exhibitW exhibitPhi) μ n j)
      = (fun n => m * ![5 / 16, 5 / 16, 3 / 8] j
        + (-3 / 5) ^ n * (s * ![1, 1, -2] j)
        + (-2 / 5) ^ n * (t * ![1, -1, 0] j)) :=
    funext fun n => hcf n j
  rwa [h3]

/-- **The boundary, stated once** (proved — the conjunction of
the proved exhibits): on the seats in-tree, non-contraction of a
bent flow occurs exactly at the degenerate two-seat seat where
the index cannot act (Brick 1: the kernel is the swap), and on
the three-seat exhibit every error mode contracts — the
antisymmetric mode at `−2/5` (above) and the symmetric mode at
`−3/5` (RTE-3a's closed form, cited). This is the conjunction of
the exhibits, NOT a general spectral theorem: the general claim
is mathematics this pin cites in prose, not a statement it
proves. -/
theorem fin_two_only_boundary :
    (∀ (w : Fin 2 → Fin 2 → ℝ) (φ : Fin 2 → ℝ),
      0 < w 0 1 → 0 < w 1 0 → w 0 0 = 0 → w 1 1 = 0 →
      ∀ i j, bentStep w φ i j = !![0, 1; 1, 0] i j)
    ∧ (∀ (a : ℝ) (j : Fin 3),
        ∑ i, ![a, -a, 0] i * bentStep exhibitW exhibitPhi i j
          = ![(-2 / 5) * a, (2 / 5) * a, 0] j)
    ∧ (∀ n : ℕ, bentIter n 0 = 5 / 16 * (1 - (-3 / 5) ^ n)
        ∧ bentIter n 1 = 5 / 16 * (1 - (-3 / 5) ^ n)
        ∧ bentIter n 2 = 3 / 8 + 5 / 8 * (-3 / 5) ^ n) :=
  ⟨fun w φ h1 h2 h3 h4 => bentStep_fin_two_swap w φ h1 h2 h3 h4,
   fun a j => exhibit_bentStep_antisymmetric_mode a j,
   fun n => exhibit_pulse_closed_form n⟩

end ThetLogos
