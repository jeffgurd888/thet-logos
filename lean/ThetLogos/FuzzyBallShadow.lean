import Mathlib.Tactic
import Mathlib.Analysis.Complex.Exponential

/-!
# FuzzyBallShadow — the fuzzy-ball gauntlet, formalized

*The gravitational atomic spectral bridge, finite seat (Jeff's name,
2026-10-25).*

This module formalizes the Fuzzy Ball Gauntlet
(`whitepaper/fuzzy-ball-gauntlet-2026-10-25.md`) under its
formalization charter
(`whitepaper/fuzzy-ball-formalization-charter-2026-10-25.md`). The
gauntlet was an exact-arithmetic computation on a declared finite
model; this module is its exhibit → T1 promotion: the same claims
C1–C5, as theorems, with the same rational data. No new physics is
asserted.

**The model (declared, exactly as in the gauntlet).** A *fuzzy
shell* of radius `r` and cutoff `L` carries the angular spectrum of
the round sphere truncated at `l = L`: `(2l+1)` copies of the
eigenvalue `l(l+1)/r²`. The *fuzzy ball* is the sediment stack of
five shells at radii `k/5`, `k = 1..5` — angular spectra only,
**no radial kinetic term**, no inter-shell coupling. The *heat
shadow* of a removed multiset `R` at time `t` is
`Σ_{λ ∈ R} exp (-t λ)`: the amount by which the break lowers the
ball's heat trace `Tr (exp (-t Δ))`, recorded in eigenvalue space.

**The breaks.** Five declared mode removals from the ball:
the lune `A` (per `l`, the `l` modes `m ≥ 1` of the outer shell),
its mirror `B` (the `m ≤ -1` half), the decapitation `C` (the
outer shell entire), the interior crack `D` (shell `k = 3`
entire), and the same-count control `E` (36 modes of the outer
shell taken as whole top-`l` blocks). A and B have **the same
definition** (§1.3 of the charter): the spectrum is all the
thermal record carries, the geometric distinction between the two
lunes is not representable in the removed multiset, and that
non-representability is the content of C2, not a shortcut.

**Clauses.** C1: every nonempty shadow is strictly positive (at
every `t`, no sign hypothesis — the exponential does it). C2: the
mirror lune casts the identical shadow. C3: A and E remove the
same number of modes with different first moments, and their
shadow *functions* differ (witnessed at `t = 1/100` through the
one analytic lemma L2, `exp (-x) ≤ 1 - x + x²/2`). C4:
decapitation's shadow strictly exceeds the crack's at **every**
`t > 0` (the formal version strengthens the gauntlet's tail
statement; the termwise domination `λ ↦ (25/9)λ` is exact). C5:
the lune break preserves the spectral gap `2`.

## Fences

- This formalizes **the gauntlet's declared finite model only.**
  Float figures from the gauntlet (Θ values, grid minima, shadow
  maxima) appear nowhere in the statements; only rational data
  (multisets, cards, moments, gaps) and real-analytic
  inequalities are formalized.
- **Zero gravity content.** "Quantum gravity shadow" is Jeff's
  name for a heat-trace difference; the corpus holds zero gravity
  objects before this brick and zero after it. **Dial #2
  unmoved.**
- **NO CLAIM.** Parts of any official (Clay) statement closed: 0.
- Placement: exhibit formalization, **NOT frontier progress.**

NO CLAIM. Dials 0/4.
-/

namespace ThetLogos

/-! ## §1. The objects (charter §1.2, verbatim in shape) -/

/-- The angular spectrum of one fuzzy shell of radius `r`, modes
`l = 0..L`: `(2l+1)` copies of `l(l+1)/r^2`. -/
def shellSpectrum (r : ℚ) (L : ℕ) : Multiset ℚ :=
  (Multiset.range (L + 1)).bind fun l =>
    Multiset.replicate (2 * l + 1) ((l * (l + 1) : ℚ) / r ^ 2)

/-- The fuzzy ball: shells `k = 1..K` at radii `r_k = k/K`, joined. -/
def ballSpectrum (K L : ℕ) : Multiset ℚ :=
  (Multiset.range K).bind fun k =>
    shellSpectrum (((k + 1 : ℕ) : ℚ) / (K : ℚ)) L

/-- The heat shadow of a removed multiset `R` at time `t`:
`Σ_{λ ∈ R} exp (-t λ)`. The coercion `ℚ → ℝ` is applied
elementwise, here and nowhere else. -/
noncomputable def shadow (R : Multiset ℚ) (t : ℝ) : ℝ :=
  (R.map fun x : ℚ => Real.exp (-t * (x : ℝ))).sum

/-- Zeroth/first/second spectral moments of a removed multiset. -/
def modeCount (R : Multiset ℚ) : ℕ := R.card
def firstMoment (R : Multiset ℚ) : ℚ := R.sum
def secondMoment (R : Multiset ℚ) : ℚ := (R.map fun x : ℚ => x ^ 2).sum

/-- Gap, in statement form: `g` is the spectral gap of `s` if `g`
occurs in `s` and no positive element of `s` is smaller. -/
def IsSpectralGap (s : Multiset ℚ) (g : ℚ) : Prop :=
  g ∈ s ∧ ∀ x ∈ s, 0 < x → g ≤ x

/-! ## §1.3. The breaks (charter §1.3, exact multiset operations) -/

/-- Lune removal at cutoff `L`, from a shell at `r = 1`: per `l`,
`l` copies of `l(l+1)` (the `m ≥ 1` half; `l = 0` removes none). -/
def removedLune (L : ℕ) : Multiset ℚ :=
  (Multiset.range (L + 1)).bind fun l =>
    Multiset.replicate l ((l * (l + 1) : ℚ))

def removedA : Multiset ℚ := removedLune 8   -- lune, m > 0
def removedB : Multiset ℚ := removedLune 8   -- mirror lune, m < 0
def removedC : Multiset ℚ := shellSpectrum 1 8        -- decapitation
def removedD : Multiset ℚ := shellSpectrum (3 / 5) 8  -- interior crack, shell k = 3
def removedE : Multiset ℚ :=                          -- same-count control
  Multiset.replicate 4 42 + Multiset.replicate 15 56 + Multiset.replicate 17 72

/-- The lune's kept half of the outer shell: per `l`, the `l + 1`
copies with `m ≤ 0`. Used in the sub-multiset decompositions. -/
def keptLune (L : ℕ) : Multiset ℚ :=
  (Multiset.range (L + 1)).bind fun l =>
    Multiset.replicate (l + 1) ((l * (l + 1) : ℚ))

/-! ## §1.3′′. Evaluation and membership helpers.

The charter prescribed kernel `decide` for the §1.4
cross-checks. On this toolchain `decide` does not reduce these
rational-multiset computations (the kernel evaluator stalls
inside `Rat` arithmetic on cast numerals — "failed to reduce"
at every site — and `native_decide` is fenced off by the axiom
rule). The cross-checks are therefore discharged by structural
evaluation instead: bind-over-range bridges turn each card and
moment into a `Finset.range` sum, and `norm_num` evaluates the
resulting rational arithmetic. The statements — and every
figure — are the charter's, unchanged. -/

/-- Card of a bind over `Multiset.range`, as a `Finset.range`
sum. -/
theorem card_bind_range (f : ℕ → Multiset ℚ) (n : ℕ) :
    ((Multiset.range n).bind f).card = ∑ l ∈ Finset.range n, (f l).card := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Multiset.range_succ, Multiset.cons_bind, Multiset.card_add, ih,
        Finset.sum_range_succ]
      exact add_comm _ _

/-- Sum of a bind over `Multiset.range`, as a `Finset.range`
sum. -/
theorem sum_bind_range (f : ℕ → Multiset ℚ) (n : ℕ) :
    ((Multiset.range n).bind f).sum = ∑ l ∈ Finset.range n, (f l).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Multiset.range_succ, Multiset.cons_bind, Multiset.sum_add, ih,
        Finset.sum_range_succ]
      exact add_comm _ _

theorem shellSpectrum_card (r : ℚ) (L : ℕ) :
    (shellSpectrum r L).card = ∑ l ∈ Finset.range (L + 1), (2 * l + 1) := by
  unfold shellSpectrum
  rw [card_bind_range]
  apply Finset.sum_congr rfl
  intro l _
  exact Multiset.card_replicate _ _

theorem shellSpectrum_sum (r : ℚ) (L : ℕ) :
    (shellSpectrum r L).sum =
      ∑ l ∈ Finset.range (L + 1), (2 * l + 1) • ((l * (l + 1) : ℚ) / r ^ 2) := by
  unfold shellSpectrum
  rw [sum_bind_range]
  apply Finset.sum_congr rfl
  intro l _
  exact Multiset.sum_replicate _ _

theorem mem_removedLune {x : ℚ} {L : ℕ} :
    x ∈ removedLune L ↔ ∃ l : ℕ, l ≤ L ∧ l ≠ 0 ∧ x = (l * (l + 1) : ℚ) := by
  rw [removedLune, Multiset.mem_bind]
  constructor
  · rintro ⟨l, hl, hx⟩
    rw [Multiset.mem_range] at hl
    rw [Multiset.mem_replicate] at hx
    exact ⟨l, by omega, hx.1, hx.2⟩
  · rintro ⟨l, hl, hne, rfl⟩
    exact ⟨l, Multiset.mem_range.mpr (by omega),
      Multiset.mem_replicate.mpr ⟨hne, rfl⟩⟩

theorem mem_shellSpectrum {x : ℚ} {r : ℚ} {L : ℕ} :
    x ∈ shellSpectrum r L ↔
      ∃ l : ℕ, l ≤ L ∧ x = (l * (l + 1) : ℚ) / r ^ 2 := by
  rw [shellSpectrum, Multiset.mem_bind]
  constructor
  · rintro ⟨l, hl, hx⟩
    rw [Multiset.mem_range] at hl
    rw [Multiset.mem_replicate] at hx
    exact ⟨l, by omega, hx.2⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, Multiset.mem_range.mpr (by omega),
      Multiset.mem_replicate.mpr ⟨by omega, rfl⟩⟩

theorem mem_keptLune {x : ℚ} {L : ℕ} :
    x ∈ keptLune L ↔ ∃ l : ℕ, l ≤ L ∧ x = (l * (l + 1) : ℚ) := by
  rw [keptLune, Multiset.mem_bind]
  constructor
  · rintro ⟨l, hl, hx⟩
    rw [Multiset.mem_range] at hl
    rw [Multiset.mem_replicate] at hx
    exact ⟨l, by omega, hx.2⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, Multiset.mem_range.mpr (by omega),
      Multiset.mem_replicate.mpr ⟨by omega, rfl⟩⟩

theorem mem_ballSpectrum {x : ℚ} {K L : ℕ} :
    x ∈ ballSpectrum K L ↔ ∃ k : ℕ, k < K ∧ ∃ l : ℕ, l ≤ L ∧
      x = (l * (l + 1) : ℚ) / (((k + 1 : ℕ) : ℚ) / (K : ℚ)) ^ 2 := by
  rw [ballSpectrum, Multiset.mem_bind]
  constructor
  · rintro ⟨k, hk, hx⟩
    rw [Multiset.mem_range] at hk
    rw [mem_shellSpectrum] at hx
    obtain ⟨l, hl, hxl⟩ := hx
    exact ⟨k, hk, l, hl, hxl⟩
  · rintro ⟨k, hk, l, hl, rfl⟩
    exact ⟨k, Multiset.mem_range.mpr hk,
      mem_shellSpectrum.mpr ⟨l, hl, rfl⟩⟩

/-! ## §1.4. Rational cross-checks (charter §1.4; figures
against `results.json`; a disagreement here is a charter
KILL, not a patch) -/

theorem modeCount_ball : modeCount (ballSpectrum 5 8) = 405 := by
  unfold modeCount ballSpectrum
  rw [card_bind_range]
  norm_num [Finset.sum_range_succ, shellSpectrum_card]

theorem modeCount_removedA : modeCount removedA = 36 := by
  unfold modeCount removedA removedLune
  rw [card_bind_range]
  norm_num [Finset.sum_range_succ, Multiset.card_replicate]

theorem modeCount_removedB : modeCount removedB = 36 := modeCount_removedA

theorem modeCount_removedC : modeCount removedC = 81 := by
  unfold modeCount removedC
  rw [shellSpectrum_card]
  norm_num [Finset.sum_range_succ]

theorem modeCount_removedD : modeCount removedD = 81 := by
  unfold modeCount removedD
  rw [shellSpectrum_card]
  norm_num [Finset.sum_range_succ]

theorem modeCount_removedE : modeCount removedE = 36 := by
  unfold modeCount removedE
  norm_num [Multiset.card_add, Multiset.card_replicate]

theorem firstMoment_removedA : firstMoment removedA = 1500 := by
  unfold firstMoment removedA removedLune
  rw [sum_bind_range]
  norm_num [Finset.sum_range_succ, Multiset.sum_replicate, nsmul_eq_mul]

theorem firstMoment_removedB : firstMoment removedB = 1500 :=
  firstMoment_removedA

theorem firstMoment_removedC : firstMoment removedC = 3240 := by
  unfold firstMoment removedC
  rw [shellSpectrum_sum]
  norm_num [Finset.sum_range_succ, nsmul_eq_mul]

theorem firstMoment_removedD : firstMoment removedD = 9000 := by
  unfold firstMoment removedD
  rw [shellSpectrum_sum]
  norm_num [Finset.sum_range_succ, nsmul_eq_mul]

theorem firstMoment_removedE : firstMoment removedE = 2232 := by
  unfold firstMoment removedE
  norm_num [Multiset.sum_add, Multiset.sum_replicate, nsmul_eq_mul]

theorem secondMoment_removedA : secondMoment removedA = 80616 := by
  unfold secondMoment removedA removedLune
  rw [Multiset.map_bind, sum_bind_range]
  norm_num [Finset.sum_range_succ, Multiset.map_replicate, Multiset.sum_replicate,
    nsmul_eq_mul]

theorem secondMoment_removedE : secondMoment removedE = 142224 := by
  unfold secondMoment removedE
  norm_num [Multiset.map_add, Multiset.map_replicate, Multiset.sum_add,
    Multiset.sum_replicate, nsmul_eq_mul]

/-- Every removed eigenvalue of A, C, E is nonnegative (consumed
by C3's termwise bounds and C4's domination). -/
theorem removedA_nonneg : ∀ x ∈ removedA, 0 ≤ x := by
  intro x hx
  have hx' : x ∈ removedLune 8 := hx
  rw [mem_removedLune] at hx'
  obtain ⟨l, -, -, rfl⟩ := hx'
  positivity

theorem removedC_nonneg : ∀ x ∈ removedC, 0 ≤ x := by
  intro x hx
  have hx' : x ∈ shellSpectrum 1 8 := hx
  rw [mem_shellSpectrum] at hx'
  obtain ⟨l, -, rfl⟩ := hx'
  positivity

theorem removedE_nonneg : ∀ x ∈ removedE, 0 ≤ x := by
  intro x hx
  have hx' : x ∈ Multiset.replicate 4 42 + Multiset.replicate 15 56 +
      Multiset.replicate 17 72 := hx
  rw [Multiset.mem_add, Multiset.mem_add] at hx'
  rcases hx' with (h | h) | h <;>
    rw [Multiset.mem_replicate] at h <;> obtain ⟨-, rfl⟩ := h <;> norm_num


/-! ## §1.3′. Sub-multiset decompositions (the removed multisets
sit inside the ball, in the shells the gauntlet says they do) -/

theorem ballSpectrum_five :
    ballSpectrum 5 8 = shellSpectrum 1 8 + shellSpectrum (4 / 5) 8 +
      shellSpectrum (3 / 5) 8 + shellSpectrum (2 / 5) 8 +
      shellSpectrum (1 / 5) 8 := by
  simp only [ballSpectrum, Multiset.range_succ, Multiset.bind_zero]
  norm_num
  ac_rfl

/-- The outer shell splits into the lune's removed and kept
halves: per `l`, `replicate (2l+1) a = replicate l a +
replicate (l+1) a`. -/
theorem shellSpectrum_one_split :
    shellSpectrum 1 8 = removedA + keptLune 8 := by
  have hval : ∀ l : ℕ, (l * (l + 1) : ℚ) / (1 : ℚ) ^ 2 = (l * (l + 1) : ℚ) := by
    intro l; simp
  have hcount : ∀ l : ℕ, (2 : ℕ) * l + 1 = l + (l + 1) := fun l => by omega
  simp only [shellSpectrum, removedA, removedLune, keptLune, hval, hcount,
    Multiset.replicate_add, Multiset.bind_add]

theorem shellSpectrum_one_split_E :
    shellSpectrum 1 8 = removedE +
      (Multiset.replicate 1 0 + Multiset.replicate 3 2 + Multiset.replicate 5 6 +
        Multiset.replicate 7 12 + Multiset.replicate 9 20 + Multiset.replicate 11 30 +
        Multiset.replicate 9 42) := by
  have hval : ∀ l : ℕ, (l * (l + 1) : ℚ) / (1 : ℚ) ^ 2 = (l * (l + 1) : ℚ) := fun l => by
    simp
  simp only [shellSpectrum, hval, Multiset.range_succ, Multiset.cons_bind,
    Multiset.bind_zero, Multiset.range_zero, removedE]
  norm_num only [Nat.cast_ofNat]
  rw [show (13 : ℕ) = 4 + 9 from rfl, Multiset.replicate_add]
  ac_rfl

/-- The ball, with the decapitation shell split off as the last
summand. -/
theorem ball_eq_rest4_add_C :
    ballSpectrum 5 8 =
      (shellSpectrum (4 / 5) 8 + shellSpectrum (3 / 5) 8 + shellSpectrum (2 / 5) 8 +
        shellSpectrum (1 / 5) 8) + removedC := by
  rw [ballSpectrum_five]; unfold removedC; ac_rfl

/-- The ball, with the lune split off as the last summand. -/
theorem ball_eq_rest4kept_add_A :
    ballSpectrum 5 8 =
      (shellSpectrum (4 / 5) 8 + shellSpectrum (3 / 5) 8 + shellSpectrum (2 / 5) 8 +
        shellSpectrum (1 / 5) 8 + keptLune 8) + removedA := by
  rw [ballSpectrum_five, shellSpectrum_one_split]; ac_rfl

theorem removedA_le_ball : removedA ≤ ballSpectrum 5 8 := by
  rw [ball_eq_rest4kept_add_A]; exact Multiset.le_add_left _ _

theorem removedB_le_ball : removedB ≤ ballSpectrum 5 8 := removedA_le_ball

theorem removedC_le_ball : removedC ≤ ballSpectrum 5 8 := by
  rw [ball_eq_rest4_add_C]; exact Multiset.le_add_left _ _

theorem removedD_le_ball : removedD ≤ ballSpectrum 5 8 := by
  have h : ballSpectrum 5 8 =
      (shellSpectrum 1 8 + shellSpectrum (4 / 5) 8 + shellSpectrum (2 / 5) 8 +
        shellSpectrum (1 / 5) 8) + removedD := by
    rw [ballSpectrum_five]; unfold removedD; ac_rfl
  rw [h]; exact Multiset.le_add_left _ _

theorem removedE_le_ball : removedE ≤ ballSpectrum 5 8 := by
  have h : ballSpectrum 5 8 =
      (shellSpectrum (4 / 5) 8 + shellSpectrum (3 / 5) 8 + shellSpectrum (2 / 5) 8 +
        shellSpectrum (1 / 5) 8 +
        (Multiset.replicate 1 0 + Multiset.replicate 3 2 + Multiset.replicate 5 6 +
          Multiset.replicate 7 12 + Multiset.replicate 9 20 + Multiset.replicate 11 30 +
          Multiset.replicate 9 42)) + removedE := by
    rw [ballSpectrum_five, shellSpectrum_one_split_E]; ac_rfl
  rw [h]; exact Multiset.le_add_left _ _

/-- Removing the decapitation leaves exactly the four inner
shells. -/
theorem ball_sub_C : ballSpectrum 5 8 - removedC =
    shellSpectrum (4 / 5) 8 + shellSpectrum (3 / 5) 8 + shellSpectrum (2 / 5) 8 +
      shellSpectrum (1 / 5) 8 := by
  have key : ballSpectrum 5 8 - removedC + removedC =
      (shellSpectrum (4 / 5) 8 + shellSpectrum (3 / 5) 8 + shellSpectrum (2 / 5) 8 +
        shellSpectrum (1 / 5) 8) + removedC := by
    rw [Multiset.add_sub_cancel removedC_le_ball, ball_eq_rest4_add_C]
  exact Multiset.add_left_inj.mp key

/-- Removing the lune leaves the four inner shells plus the
kept half of the outer shell. -/
theorem ball_sub_A : ballSpectrum 5 8 - removedA =
    (shellSpectrum (4 / 5) 8 + shellSpectrum (3 / 5) 8 + shellSpectrum (2 / 5) 8 +
      shellSpectrum (1 / 5) 8 + keptLune 8) := by
  have key : ballSpectrum 5 8 - removedA + removedA =
      (shellSpectrum (4 / 5) 8 + shellSpectrum (3 / 5) 8 + shellSpectrum (2 / 5) 8 +
        shellSpectrum (1 / 5) 8 + keptLune 8) + removedA := by
    rw [Multiset.add_sub_cancel removedA_le_ball, ball_eq_rest4kept_add_A]
  exact Multiset.add_left_inj.mp key

/-! ## C1 — every shadow is strictly positive (charter §2, C1).
No hypothesis on `t`, none on the signs in `R`: the exponential
does all of it. Stronger than the gauntlet, as chartered. -/

theorem shadow_pos {R : Multiset ℚ} (hR : R ≠ 0) (t : ℝ) :
    0 < shadow R t := by
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hR
  have hmem : Real.exp (-t * (a : ℝ)) ∈
      R.map (fun x : ℚ => Real.exp (-t * (x : ℝ))) :=
    Multiset.mem_map_of_mem _ ha
  have hnn : ∀ y ∈ R.map (fun x : ℚ => Real.exp (-t * (x : ℝ))), 0 ≤ y := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp hy
    exact (Real.exp_pos _).le
  exact (Real.exp_pos _).trans_le (Multiset.single_le_sum hnn _ hmem)

/-- The formal form of "the shadow is the heat-trace difference":
for `R ≤ S`, the broken spectrum's shadow plus the removed
shadow is the unbroken shadow. -/
theorem shadow_sub_add_shadow {R S : Multiset ℚ} (h : R ≤ S) (t : ℝ) :
    shadow (S - R) t + shadow R t = shadow S t := by
  unfold shadow
  rw [← Multiset.sum_add, ← Multiset.map_add, Multiset.sub_add_cancel h]

/-! ## C2 — the mirror casts the same shadow (charter §2, C2).
The identity is `rfl` by construction: the removed multiset is
counts only, and counts are all the thermal record carries. -/

theorem removedA_eq_removedB : removedA = removedB := rfl

theorem shadow_A_eq_shadow_B (t : ℝ) : shadow removedA t = shadow removedB t := by
  rw [removedA_eq_removedB]

/-! ## C3 — same count, different shadow (charter §2, C3).
Level (i) is pure rational arithmetic. Level (ii) goes through
the two one-variable bounds L1/L2, summed termwise. -/

/-- **L1**: `1 - x ≤ exp (-x)` for `x ≥ 0`. -/
theorem exp_neg_ge (x : ℝ) (hx : 0 ≤ x) : 1 - x ≤ Real.exp (-x) := by
  have h := Real.add_one_le_exp (-x)
  linarith

/-- **L2** (the brick's one analytic lemma): `exp (-x) ≤
1 - x + x²/2` for `x ≥ 0`. Proved by reciprocation from
`Real.quadratic_le_exp_of_nonneg`: with `P = 1 + x + x²/2` and
`Q = 1 - x + x²/2`, one has `P * Q = 1 + x⁴/4 ≥ 1` and `Q > 0`,
so `exp (-x) = (exp x)⁻¹ ≤ P⁻¹ ≤ Q`. No restriction `x ≤ 1`. -/
theorem exp_neg_le (x : ℝ) (hx : 0 ≤ x) : Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  set P : ℝ := 1 + x + x ^ 2 / 2 with hPdef
  set Q : ℝ := 1 - x + x ^ 2 / 2 with hQdef
  have hQpos : 0 < Q := by nlinarith [sq_nonneg (x - 1)]
  have hPpos : 0 < P := by nlinarith [sq_nonneg x, hx]
  have hPQ : P * Q = 1 + x ^ 4 / 4 := by rw [hPdef, hQdef]; ring
  have hExp : P ≤ Real.exp x := Real.quadratic_le_exp_of_nonneg hx
  have h1 : Real.exp (-x) ≤ P⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hPpos hExp
  have h2 : P⁻¹ ≤ Q := by
    have h3 : (1 : ℝ) ≤ Q * P := by
      have h4 : (0 : ℝ) ≤ x ^ 4 := by positivity
      rw [mul_comm Q P, hPQ]; linarith
    have h5 : P⁻¹ * (1 : ℝ) ≤ P⁻¹ * (Q * P) :=
      mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr hPpos.le)
    have h6 : P⁻¹ * (Q * P) = Q := by
      rw [mul_comm Q P, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hPpos), one_mul]
    rwa [mul_one, h6] at h5
  exact h1.trans h2

/-- Termwise lower bound, summed over a multiset of nonnegative
rationals: `card - t·(first moment) ≤ shadow`. -/
theorem shadow_ge {R : Multiset ℚ} (hR : ∀ x ∈ R, 0 ≤ x) (t : ℝ) (ht : 0 ≤ t) :
    (R.card : ℝ) - t * (R.sum : ℝ) ≤ shadow R t := by
  revert hR
  induction R using Multiset.induction with
  | empty => intro _; simp [shadow]
  | cons a s ih =>
      intro hR
      have ha : (0 : ℚ) ≤ a := hR a (by simp)
      have ih' : (s.card : ℝ) - t * (s.sum : ℝ) ≤
          (s.map fun x : ℚ => Real.exp (-t * (x : ℝ))).sum :=
        ih (fun x hx => hR x (Multiset.mem_cons_of_mem hx))
      have hL1 : (1 : ℝ) - t * (a : ℝ) ≤ Real.exp (-t * (a : ℝ)) := by
        have h := exp_neg_ge (t * (a : ℝ)) (mul_nonneg ht (by exact_mod_cast ha))
        rwa [← neg_mul] at h
      simp only [shadow, Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
        Multiset.sum_cons]
      push_cast
      push_cast at ih'
      rw [mul_add]
      linarith [ih', hL1]

/-- Termwise upper bound, summed: `shadow ≤ card - t·(first
moment) + (t²/2)·(second moment)`. -/
theorem shadow_le {R : Multiset ℚ} (hR : ∀ x ∈ R, 0 ≤ x) (t : ℝ) (ht : 0 ≤ t) :
    shadow R t ≤ (R.card : ℝ) - t * (R.sum : ℝ) +
      (t ^ 2 / 2) * ((R.map fun x : ℚ => x ^ 2).sum : ℝ) := by
  revert hR
  induction R using Multiset.induction with
  | empty => intro _; simp [shadow]
  | cons a s ih =>
      intro hR
      have ha : (0 : ℚ) ≤ a := hR a (by simp)
      have ih' : (s.map fun x : ℚ => Real.exp (-t * (x : ℝ))).sum ≤
          (s.card : ℝ) - t * (s.sum : ℝ) +
            (t ^ 2 / 2) * ((s.map fun x : ℚ => x ^ 2).sum : ℝ) :=
        ih (fun x hx => hR x (Multiset.mem_cons_of_mem hx))
      have hL2 : Real.exp (-t * (a : ℝ)) ≤
          (1 : ℝ) - t * (a : ℝ) + (t * (a : ℝ)) ^ 2 / 2 := by
        have h := exp_neg_le (t * (a : ℝ)) (mul_nonneg ht (by exact_mod_cast ha))
        rwa [← neg_mul] at h
      simp only [shadow, Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
        Multiset.sum_cons]
      push_cast
      push_cast at ih'
      rw [mul_add, mul_add]
      have hsq : (t * (a : ℝ)) ^ 2 / 2 = (t ^ 2 / 2) * (a : ℝ) ^ 2 := by ring
      linarith [ih', hL2, hsq]

theorem C3_moments :
    modeCount removedA = modeCount removedE ∧
    firstMoment removedA ≠ firstMoment removedE := by
  constructor
  · rw [modeCount_removedA, modeCount_removedE]
  · rw [firstMoment_removedA, firstMoment_removedE]; norm_num

/-- Level (ii): the shadow *functions* differ, witnessed at
`t₀ = 1/100`, where the bounds give
`shadow A t₀ ≥ 21 > 20.7912 ≥ shadow E t₀`. -/
theorem C3_shadow_ne : shadow removedA ≠ shadow removedE := by
  intro hEq
  have hcA : (removedA.card : ℝ) = 36 := by
    have h : removedA.card = 36 := modeCount_removedA
    exact_mod_cast h
  have hsA : (removedA.sum : ℝ) = 1500 := by
    have h : removedA.sum = 1500 := firstMoment_removedA
    exact_mod_cast h
  have hcE : (removedE.card : ℝ) = 36 := by
    have h : removedE.card = 36 := modeCount_removedE
    exact_mod_cast h
  have hsE : (removedE.sum : ℝ) = 2232 := by
    have h : removedE.sum = 2232 := firstMoment_removedE
    exact_mod_cast h
  have hqE : ((removedE.map fun x : ℚ => x ^ 2).sum : ℝ) = 142224 := by
    have h : (removedE.map fun x : ℚ => x ^ 2).sum = 142224 := secondMoment_removedE
    exact_mod_cast h
  have hA := shadow_ge removedA_nonneg (1 / 100 : ℝ) (by norm_num)
  have hE := shadow_le removedE_nonneg (1 / 100 : ℝ) (by norm_num)
  rw [hcA, hsA] at hA
  rw [hcE, hsE, hqE] at hE
  have hval := congrFun hEq (1 / 100 : ℝ)
  norm_num at hA hE
  linarith

/-! ## C4 — decapitation's shadow strictly exceeds the crack's,
at every `t > 0` (charter §2, C4; the formal version strengthens
the gauntlet's tail statement, via exact termwise domination). -/

/-- The scaling identity: the crack's spectrum is the
decapitation's pattern blue-shifted by `1/r₃² = 25/9`, with
identical multiplicities. -/
theorem removedD_eq_map : removedD = removedC.map (· * (25 / 9 : ℚ)) := by
  simp only [removedD, removedC, shellSpectrum, Multiset.map_bind,
    Multiset.map_replicate]
  congr 1
  funext l
  congr 1
  have h1 : ((3 : ℚ) / 5) ^ 2 = 9 / 25 := by norm_num
  rw [h1]
  field_simp

theorem C4_shadow_lt (t : ℝ) (ht : 0 < t) :
    shadow removedD t < shadow removedC t := by
  have h2mem : (2 : ℚ) ∈ removedC := by
    have h : (2 : ℚ) ∈ shellSpectrum 1 8 :=
      mem_shellSpectrum.mpr ⟨1, by norm_num, by norm_num⟩
    exact h
  rw [removedD_eq_map]
  unfold shadow
  rw [Multiset.map_map]
  apply Multiset.sum_lt_sum
  · intro x hx
    have hx0 : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast removedC_nonneg x hx
    have hcast : ((x * (25 / 9 : ℚ) : ℚ) : ℝ) = (x : ℝ) * (25 / 9 : ℝ) := by
      push_cast; ring
    simp only [Function.comp_apply]
    rw [hcast]
    apply Real.exp_le_exp.mpr
    have hge : (x : ℝ) ≤ (x : ℝ) * (25 / 9 : ℝ) := by
      have h := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 25 / 9 by norm_num) hx0
      rwa [mul_one] at h
    have hmul := mul_le_mul_of_nonneg_left hge ht.le
    linarith [hmul]
  · refine ⟨2, h2mem, ?_⟩
    have hcast : ((2 * (25 / 9 : ℚ) : ℚ) : ℝ) = (50 / 9 : ℝ) := by norm_num
    simp only [Function.comp_apply]
    rw [hcast]
    apply Real.exp_lt_exp.mpr
    have h2r : ((2 : ℚ) : ℝ) = 2 := by norm_num
    rw [h2r]
    nlinarith [ht]

/-! ## C5 — the lune break preserves the gap (charter §2, C5),
plus the ball's gap and the one gap-moving break as
cross-checks. -/

theorem gap_ball : IsSpectralGap (ballSpectrum 5 8) 2 := by
  unfold IsSpectralGap
  constructor
  · rw [mem_ballSpectrum]
    exact ⟨4, by norm_num, 1, by norm_num, by norm_num⟩
  · intro x hx hxpos
    rw [mem_ballSpectrum] at hx
    obtain ⟨k, hk, l, -, rfl⟩ := hx
    simp only [Nat.cast_ofNat]
    have hl1 : 1 ≤ l := by
      by_contra hcon
      push_neg at hcon
      have hl0 : l = 0 := by omega
      subst hl0
      norm_num at hxpos
    have hv : (2 : ℚ) ≤ (l * (l + 1) : ℚ) := by
      have h2 : (2 : ℕ) ≤ l * (l + 1) := by
        calc (2 : ℕ) = 1 * 2 := by norm_num
        _ ≤ l * (l + 1) := Nat.mul_le_mul hl1 (by omega)
      exact_mod_cast h2
    have hr1 : ((k + 1 : ℕ) : ℚ) / 5 ≤ 1 := by
      rw [div_le_one (by norm_num : (0 : ℚ) < 5)]
      exact_mod_cast (by omega : k + 1 ≤ 5)
    have hr : (((k + 1 : ℕ) : ℚ) / 5) ^ 2 ≤ 1 := by
      have hnn : (0 : ℚ) ≤ ((k + 1 : ℕ) : ℚ) / 5 := by positivity
      nlinarith [hr1, hnn,
        mul_nonneg hnn (show (0 : ℚ) ≤ 1 - ((k + 1 : ℕ) : ℚ) / 5 by linarith)]
    rw [le_div_iff₀ (by positivity : (0 : ℚ) < (((k + 1 : ℕ) : ℚ) / 5) ^ 2)]
    have h3 := mul_le_mul_of_nonneg_left hr (show (0 : ℚ) ≤ 2 by norm_num)
    linarith [h3, hv]

theorem gap_ball_minus_C :
    IsSpectralGap (ballSpectrum 5 8 - removedC) (25 / 8) := by
  unfold IsSpectralGap
  rw [ball_sub_C]
  constructor
  · have hmem : (25 / 8 : ℚ) ∈ shellSpectrum (4 / 5) 8 :=
      mem_shellSpectrum.mpr ⟨1, by norm_num, by norm_num⟩
    rw [Multiset.mem_add, Multiset.mem_add, Multiset.mem_add]
    exact Or.inl (Or.inl (Or.inl hmem))
  · intro x hx hxpos
    rw [Multiset.mem_add, Multiset.mem_add, Multiset.mem_add] at hx
    have hl1_of {r : ℚ} {l : ℕ} (hxpos' : 0 < (l * (l + 1) : ℚ) / r ^ 2)
        (hr : r ≠ 0) : 1 ≤ l := by
      by_contra hcon
      push_neg at hcon
      have hl0 : l = 0 := by omega
      subst hl0
      simp [hr] at hxpos'
    have hv_of {l : ℕ} (hl1 : 1 ≤ l) : (2 : ℚ) ≤ (l * (l + 1) : ℚ) := by
      have h2 : (2 : ℕ) ≤ l * (l + 1) := by
        calc (2 : ℕ) = 1 * 2 := by norm_num
        _ ≤ l * (l + 1) := Nat.mul_le_mul hl1 (by omega)
      exact_mod_cast h2
    rcases hx with ((h | h) | h) | h
    · rw [mem_shellSpectrum] at h
      obtain ⟨l, -, rfl⟩ := h
      have hl1 := hl1_of hxpos (by norm_num)
      rw [le_div_iff₀ (by norm_num : (0 : ℚ) < (4 / 5 : ℚ) ^ 2)]
      nlinarith [hv_of hl1]
    · rw [mem_shellSpectrum] at h
      obtain ⟨l, -, rfl⟩ := h
      have hl1 := hl1_of hxpos (by norm_num)
      rw [le_div_iff₀ (by norm_num : (0 : ℚ) < (3 / 5 : ℚ) ^ 2)]
      nlinarith [hv_of hl1]
    · rw [mem_shellSpectrum] at h
      obtain ⟨l, -, rfl⟩ := h
      have hl1 := hl1_of hxpos (by norm_num)
      rw [le_div_iff₀ (by norm_num : (0 : ℚ) < (2 / 5 : ℚ) ^ 2)]
      nlinarith [hv_of hl1]
    · rw [mem_shellSpectrum] at h
      obtain ⟨l, -, rfl⟩ := h
      have hl1 := hl1_of hxpos (by norm_num)
      rw [le_div_iff₀ (by norm_num : (0 : ℚ) < (1 / 5 : ℚ) ^ 2)]
      nlinarith [hv_of hl1]

theorem gap_ball_minus_A :
    IsSpectralGap (ballSpectrum 5 8 - removedA) 2 := by
  unfold IsSpectralGap
  rw [ball_sub_A]
  have hrest4_le : (shellSpectrum (4 / 5) 8 + shellSpectrum (3 / 5) 8 +
      shellSpectrum (2 / 5) 8 + shellSpectrum (1 / 5) 8) ≤ ballSpectrum 5 8 :=
    Multiset.le_iff_exists_add.mpr ⟨removedC, ball_eq_rest4_add_C⟩
  have hkept_le : keptLune 8 ≤ ballSpectrum 5 8 := by
    apply le_trans _ (Multiset.le_iff_exists_add.mpr
      ⟨shellSpectrum (4 / 5) 8 + shellSpectrum (3 / 5) 8 + shellSpectrum (2 / 5) 8 +
        shellSpectrum (1 / 5) 8, by rw [ballSpectrum_five]; ac_rfl⟩ :
        shellSpectrum 1 8 ≤ ballSpectrum 5 8)
    exact Multiset.le_iff_exists_add.mpr
      ⟨removedA, by rw [shellSpectrum_one_split, add_comm]⟩
  constructor
  · have hmem : (2 : ℚ) ∈ keptLune 8 :=
      mem_keptLune.mpr ⟨1, by norm_num, by norm_num⟩
    rw [Multiset.mem_add]
    exact Or.inr hmem
  · intro x hx hxpos
    rw [Multiset.mem_add] at hx
    have hxball : x ∈ ballSpectrum 5 8 := by
      rcases hx with h | h
      · exact Multiset.mem_of_le hrest4_le h
      · exact Multiset.mem_of_le hkept_le h
    exact gap_ball.2 x hxball hxpos

theorem C5_gap :
    IsSpectralGap (ballSpectrum 5 8) 2 ∧
    IsSpectralGap (ballSpectrum 5 8 - removedA) 2 :=
  ⟨gap_ball, gap_ball_minus_A⟩

/-! ## The package (charter §2 headline): C1–C5 conjoined. -/

theorem fuzzyBall_package :
    (∀ (R : Multiset ℚ), R ≠ 0 → ∀ t : ℝ, 0 < shadow R t) ∧
    (∀ t : ℝ, shadow removedA t = shadow removedB t) ∧
    (modeCount removedA = modeCount removedE ∧
      firstMoment removedA ≠ firstMoment removedE) ∧
    (shadow removedA ≠ shadow removedE) ∧
    (∀ t : ℝ, 0 < t → shadow removedD t < shadow removedC t) ∧
    (IsSpectralGap (ballSpectrum 5 8) 2 ∧
      IsSpectralGap (ballSpectrum 5 8 - removedA) 2) :=
  ⟨fun _ hR t => shadow_pos hR t, shadow_A_eq_shadow_B, C3_moments,
    C3_shadow_ne, fun t ht => C4_shadow_lt t ht, C5_gap⟩

end ThetLogos
