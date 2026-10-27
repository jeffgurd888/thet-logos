import ThetLogos.MeasuredClockQuestion2
import ThetLogos.MeasuredClockAnswer8
import Mathlib.Data.Fin.VecNotation
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# ThetLogos.MeasuredClockDecision7 — Q1′′ decided at N = 7: NO FIT (Tier T1, about T4 input)

**Status: the re-posed clock question `measuredClockQuestion2`,
decided for the single instance N = 7 — negatively. NO CLAIM beyond
that instance.**

## The question and the verdict

`measuredClockQuestion2 7` asks for a thermal triple — `β > 0` and a
spectrum `lam : Fin 7 → ℝ` — together with an assignment `f` of the
seven measured clock lines to pairs of levels, such that every line's
modular frequency difference `β (lam i ^ 2 - lam j ^ 2)` reproduces the
entered ratio `clockObs m` **in observation units** (no free scale)
within that line's own entered uncertainty `clockObsErr m`. The data
are Tier T4 INPUT (the CIPM compilation entered in
`MeasuredClockSpectrum.lean`); this module decides a finite fit
question about that table and nothing else. **The answer at N = 7 is
no** (`measuredClockNoFit7` below). The question at N ≤ 6 is not
asked and not decided here; `blockedQ1` is untouched. The c = 1 exact
fits are re-derived as Q1′′ instances at N = 8 and N = 9 at the end
of the module, from the same witnesses as the landed Q1′ answers.

## The argument, in outline

Put `x k = β * lam k ^ 2` and `d m = x (f m).1 - x (f m).2`. A fit
makes `|d m - clockObs m| ≤ clockObsErr m` for all seven lines, hence
`d m > 0`: each line is a directed edge between two distinct levels,
strictly decreasing in `x`. The seven unordered pairs
`{(f m).1, (f m).2}` are all distinct: an aligned repetition would
force two entered ratios within their combined uncertainties of each
other, and a swapped repetition would force their sum below the same
budget — both excluded by the entered table (Brick 1). So the pairs
are seven distinct edges of a simple graph on seven vertices. Some
connected component then has at least as many edges as vertices;
inside it, a spanning tree leaves one extra edge over, and the tree
path between that edge's endpoints closes a trail (Brick 4). Around
any closed trail the signed sum of the `d m` telescopes to zero, so
the signs read off the trail give a signed sum of entered ratios
bounded by the accumulated tolerances — under `10 ^ -11` in total.
But the finite check (Brick 2) shows every nonzero sign pattern on
the seven entered ratios has absolute signed sum above `10 ^ -11`:
patterns using line 6 fail by the size of `clockObs 6` itself, and
patterns on lines 0–5 fail by an exact integer enumeration (the
closest, `-obs 1 - obs 3 + obs 4 + obs 5`, misses by about
`2.34 × 10 ^ -2` against a budget of about `5 × 10 ^ -16` — thirteen
orders of magnitude). Contradiction; no fit exists.
-/

namespace ThetLogos

/-! ## Brick 1 — data numerics

Facts about the entered table, checked entry by entry in ℚ. The
kernel is never asked to evaluate rational arithmetic directly
(it stalls on `Rat` goals in this pin); every check goes through
`norm_num` on the unfolded table. -/

/-- Every entered uncertainty is nonnegative. -/
lemma clockObsErr_nonneg : ∀ m : Fin 7, 0 ≤ clockObsErr m := by
  intro m
  fin_cases m <;> norm_num [clockObsErr]

/-- Every entered uncertainty is strictly below its own ratio — the
    data-level reason no line can be a self-loop. -/
lemma clockObs_err_lt : ∀ m : Fin 7, clockObsErr m < clockObs m := by
  intro m
  fin_cases m <;> norm_num [clockObs, clockObsErr]

/-- Every entered ratio is positive. -/
lemma clockObs_pos : ∀ m : Fin 7, 0 < clockObs m :=
  fun m => lt_of_le_of_lt (clockObsErr_nonneg m) (clockObs_err_lt m)

/-- Pair separation: distinct entered ratios are separated by more
    than their combined uncertainties — the data-level reason no two
    lines can occupy the same ordered pair of levels. -/
lemma clockObs_pair_sep : ∀ m m' : Fin 7, m ≠ m' →
    clockObsErr m + clockObsErr m' < |clockObs m - clockObs m'| := by
  intro m m' h
  fin_cases m <;> fin_cases m' <;> simp_all <;> norm_num [clockObs, clockObsErr]

/-- Pair sums: any two entered ratios sum to more than their combined
    uncertainties — the data-level reason no two lines can occupy the
    same unordered pair of levels in opposite orientations. -/
lemma clockObs_pair_add : ∀ m m' : Fin 7,
    clockObsErr m + clockObsErr m' < clockObs m + clockObs m' := by
  intro m m'
  fin_cases m <;> fin_cases m' <;> norm_num [clockObs, clockObsErr]

/-- Line 6 dwarfs the six small lines together, by a margin of more
    than 46681 — the data-level reason line 6 can sit on no cycle. -/
lemma clockObs_six_gap :
    (∑ m : Fin 6, clockObs (Fin.castSucc m)) + 46681 < clockObs 6 := by
  rw [Fin.sum_univ_six]
  norm_num [clockObs, Fin.castSucc]

/-- The total of all seven entered uncertainties is below `10 ^ -11`
    (the Sr/Cs bar dominates it). This is the single tolerance budget
    every cycle in the decision argument must fit inside. -/
lemma clockObsErr_sum_lt : ∑ m : Fin 7, (clockObsErr m : ℝ) < 1 / 10 ^ 11 := by
  have hq : ∑ m : Fin 7, clockObsErr m < (1 : ℚ) / 10 ^ 11 := by
    rw [Fin.sum_univ_seven]
    norm_num [clockObsErr]
  have hcast : ((∑ m : Fin 7, clockObsErr m : ℚ) : ℝ)
      = ∑ m : Fin 7, (clockObsErr m : ℝ) := by
    push_cast
    ring
  calc ∑ m : Fin 7, (clockObsErr m : ℝ)
      = ((∑ m : Fin 7, clockObsErr m : ℚ) : ℝ) := hcast.symm
    _ < ((1 : ℚ) / 10 ^ 11 : ℝ) := by exact_mod_cast hq
    _ = 1 / 10 ^ 11 := by norm_num

/-! ## Brick 2 — the finite check

Every nonzero sign pattern on the seven entered ratios has absolute
signed sum above `10 ^ -11`. Patterns using line 6 are excluded by
size (`clockObs_six_gap`); patterns on lines 0–5 reduce, over the
common denominator `10 ^ 18`, to an integer statement about the
numerators, discharged by kernel computation over the `3 ^ 6 = 729`
sign vectors (`sign_check_int`). The bound the computation verifies,
`10 ^ 16`, is far cruder than the true minimum `23428808635383031`
(Brick C's enumeration) — crudeness is free, since the tolerance
budget is `10 ^ -11 = 10 ^ 7 / 10 ^ 18`. -/

/-- The numerators of `clockObs 0` … `clockObs 5` over the common
    denominator `10 ^ 18`. -/
def clockNum : Fin 6 → ℤ :=
  ![1207507039343337845, 2611701431781463019, 2162887127516663705,
    1495991618544900552, 1603714045975103000, 2480550195715877540]

/- The integer finite check: every nonconstant sign vector on the
   six small numerators has absolute signed sum above `10 ^ 16`.
   Discharged by kernel computation over all `3 ^ 6` sign vectors. -/
set_option maxRecDepth 100000 in
theorem sign_check_int : ∀ s : Fin 6 → Fin 3, s ≠ (fun _ => 1) →
    (10 ^ 16 : ℤ) < |∑ m, ((s m).val - 1) * clockNum m| := by
  decide

/-- `clockObs` on lines 0–5 is `clockNum` over `10 ^ 18`. -/
lemma clockObs_eq_num : ∀ m : Fin 6,
    clockObs (Fin.castSucc m) = (clockNum m : ℚ) / 10 ^ 18 := by
  intro m
  fin_cases m <;> norm_num [clockObs, clockNum, Fin.castSucc]

/-- **The finite check.** Every nonzero sign pattern `σ` on the seven
    entered ratios satisfies `|∑ σ * clockObs| > 10 ^ -11`. -/
theorem sign_check : ∀ σ : Fin 7 → ℤ,
    (∀ m, σ m = -1 ∨ σ m = 0 ∨ σ m = 1) → (∃ m, σ m ≠ 0) →
    (1 / 10 ^ 11 : ℚ) < |∑ m, σ m * clockObs m| := by
  intro σ hσ hne
  have hσ1 : ∀ m, |σ m| ≤ 1 := by
    intro m
    rcases hσ m with h | h | h <;> simp [h]
  -- Split the sum over `Fin 7` into lines 0–5 and line 6.
  have hsplit : ∑ m : Fin 7, σ m * clockObs m
      = (∑ m : Fin 6, σ (Fin.castSucc m) * clockObs (Fin.castSucc m))
        + σ 6 * clockObs 6 := by
    have hlast : Fin.last 6 = (6 : Fin 7) := by
      ext
      rfl
    rw [Fin.sum_univ_castSucc, hlast]
  by_cases h6 : σ 6 = 0
  · -- Patterns on lines 0–5 only: the integer check decides.
    rw [hsplit, h6]
    simp only [Int.cast_zero, zero_mul, add_zero]
    -- The small sum, in integer form over the common denominator.
    have hS5 : (∑ m : Fin 6, σ (Fin.castSucc m) * clockObs (Fin.castSucc m))
        = ((∑ m : Fin 6, σ (Fin.castSucc m) * clockNum m : ℤ) : ℚ)
          / 10 ^ 18 := by
      have h1 : ∀ m : Fin 6, σ (Fin.castSucc m) * clockObs (Fin.castSucc m)
          = ((σ (Fin.castSucc m) * clockNum m : ℤ) : ℚ) / 10 ^ 18 := by
        intro m
        rw [clockObs_eq_num]
        push_cast
        ring
      calc (∑ m : Fin 6, σ (Fin.castSucc m) * clockObs (Fin.castSucc m))
          = ∑ m : Fin 6, ((σ (Fin.castSucc m) * clockNum m : ℤ) : ℚ)
              / 10 ^ 18 :=
            Finset.sum_congr rfl (fun m _ => h1 m)
        _ = ((∑ m : Fin 6, ((σ (Fin.castSucc m) * clockNum m : ℤ) : ℚ))
              / 10 ^ 18) := by
            rw [Finset.sum_div]
        _ = ((∑ m : Fin 6, σ (Fin.castSucc m) * clockNum m : ℤ) : ℚ)
              / 10 ^ 18 := by
            rw [Int.cast_sum]
    rw [hS5, abs_div]
    -- Transport σ to a sign vector `s : Fin 6 → Fin 3`.
    set s : Fin 6 → Fin 3 := fun m =>
      ⟨(σ (Fin.castSucc m) + 1).toNat, by
        have h1 := hσ (Fin.castSucc m)
        rcases h1 with h | h | h <;> simp [h]⟩ with hs
    have hsval : ∀ m : Fin 6, ((s m).val : ℤ) - 1 = σ (Fin.castSucc m) := by
      intro m
      have h1 := hσ (Fin.castSucc m)
      rcases h1 with h | h | h <;> simp [hs, h]
    have hsne : s ≠ (fun _ => 1) := by
      intro hcon
      obtain ⟨m, hm⟩ := hne
      apply hm
      by_cases hm6 : m = 6
      · rw [hm6]; exact h6
      · obtain ⟨k, hk⟩ : ∃ k : Fin 6, m = Fin.castSucc k :=
          ⟨⟨m.val, by
            have h := m.isLt
            omega⟩, by
            ext
            simp⟩
        rw [hk]
        have h2 := hsval k
        have h3 : s k = 1 := congrFun hcon k
        rw [h3] at h2
        simp at h2
        exact h2.symm
    have hint := sign_check_int s hsne
    have hsum_eq : (∑ m : Fin 6, σ (Fin.castSucc m) * clockNum m)
        = ∑ m : Fin 6, (((s m).val : ℤ) - 1) * clockNum m := by
      apply Finset.sum_congr rfl
      intro m _
      rw [hsval m]
    rw [hsum_eq]
    have hgt : (10 ^ 16 : ℚ)
        < |((∑ m : Fin 6, (((s m).val : ℤ) - 1) * clockNum m : ℤ) : ℚ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast hint
    have hnorm : |(10 ^ 18 : ℚ)| = 10 ^ 18 := abs_of_pos (by norm_num)
    rw [hnorm]
    calc (1 : ℚ) / 10 ^ 11
        < (10 ^ 16 : ℚ) / 10 ^ 18 := by norm_num
      _ ≤ |((∑ m : Fin 6, (((s m).val : ℤ) - 1) * clockNum m : ℤ) : ℚ)|
            / 10 ^ 18 :=
          div_le_div_of_nonneg_right (le_of_lt hgt) (by norm_num)
  · -- Patterns using line 6: line 6 dwarfs everything else.
    have h6v : σ 6 = -1 ∨ σ 6 = 1 := by
      rcases hσ 6 with h | h | h
      · exact Or.inl h
      · exact absurd h h6
      · exact Or.inr h
    rw [hsplit]
    have hS5abs : |(∑ m : Fin 6, σ (Fin.castSucc m) * clockObs (Fin.castSucc m))|
        ≤ ∑ m : Fin 6, clockObs (Fin.castSucc m) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
      intro m _
      have h1 : |(σ (Fin.castSucc m) : ℚ)| ≤ 1 := by
        have := hσ1 (Fin.castSucc m)
        exact_mod_cast this
      calc |σ (Fin.castSucc m) * clockObs (Fin.castSucc m)|
          = |(σ (Fin.castSucc m) : ℚ)| * |clockObs (Fin.castSucc m)| :=
            abs_mul _ _
        _ ≤ 1 * |clockObs (Fin.castSucc m)| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = clockObs (Fin.castSucc m) := by
            rw [one_mul, abs_of_nonneg (le_of_lt (clockObs_pos _))]
    have h6abs : |σ 6 * clockObs 6| = clockObs 6 := by
      rcases h6v with h | h <;> simp [h, abs_of_nonneg (le_of_lt (clockObs_pos 6))]
    have htri : |σ 6 * clockObs 6|
        ≤ |(∑ m : Fin 6, σ (Fin.castSucc m) * clockObs (Fin.castSucc m))
            + σ 6 * clockObs 6|
          + |(∑ m : Fin 6, σ (Fin.castSucc m) * clockObs (Fin.castSucc m))| := by
      have h : |σ 6 * clockObs 6|
          = |((∑ m : Fin 6, σ (Fin.castSucc m) * clockObs (Fin.castSucc m))
              + σ 6 * clockObs 6)
            + (-(∑ m : Fin 6, σ (Fin.castSucc m) * clockObs (Fin.castSucc m)))| := by
        congr 1
        ring
      rw [h]
      exact (abs_add_le _ _).trans (add_le_add_right (le_of_eq (abs_neg _)) _)
    have hfin : (46681 : ℚ)
        < |(∑ m : Fin 6, σ (Fin.castSucc m) * clockObs (Fin.castSucc m))
            + σ 6 * clockObs 6| := by
      have h := le_trans htri (add_le_add_right hS5abs _)
      rw [h6abs] at h
      linarith [clockObs_six_gap]
    exact lt_trans (by norm_num) hfin

/-! ## General helpers: transferring walks along adjacency-preserving maps

The cycle production in Brick 4 moves a walk from a spanning tree to
its component graph (same vertices, more edges) and then to the
ambient graph (subtype vertices to plain vertices). Mathlib's
`Walk.map` covers the second move for embeddings; the bespoke
recursion here covers both uniformly and keeps the edge list
transparent: transferred edges are the pointwise image of the
original edges. -/

/-- Every unordered pair has representatives. -/
lemma sym2_rep {α : Type*} (e : Sym2 α) : ∃ a b, s(a, b) = e :=
  Sym2.inductionOn e (fun a b => ⟨a, b, rfl⟩)

/-- `Sym2.map` of an injective function is injective. -/
lemma sym2_map_injective {α β : Type*} {g : α → β} (hg : Function.Injective g) :
    Function.Injective (Sym2.map g) := by
  intro e₁ e₂ h
  obtain ⟨a, b, hab⟩ := sym2_rep e₁
  obtain ⟨c, d, hcd⟩ := sym2_rep e₂
  rw [← hab, ← hcd, Sym2.map_mk, Sym2.map_mk] at h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← hab, ← hcd, hg h1, hg h2]
  · rw [← hab, ← hcd, hg h1, hg h2, Sym2.eq_swap]

/-- Transfer a walk along a vertex map that preserves adjacency. -/
def walkTransfer {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}
    (φ : V → W) (hφ : ∀ ⦃a b : V⦄, G.Adj a b → G'.Adj (φ a) (φ b)) :
    ∀ {u v : V}, G.Walk u v → G'.Walk (φ u) (φ v)
  | _, _, .nil => .nil
  | _, _, .cons h p => .cons (hφ h) (walkTransfer φ hφ p)

/-- The edges of a transferred walk are the pointwise image of the
    original edges. -/
lemma walkTransfer_edges {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}
    (φ : V → W) (hφ : ∀ ⦃a b : V⦄, G.Adj a b → G'.Adj (φ a) (φ b))
    {u v : V} (p : G.Walk u v) :
    (walkTransfer φ hφ p).edges = p.edges.map (Sym2.map φ) := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [walkTransfer, ih]

/-- A trail transfers to a trail when the vertex map is injective
    on edges. -/
lemma walkTransfer_isTrail {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}
    (φ : V → W) (hφ : ∀ ⦃a b : V⦄, G.Adj a b → G'.Adj (φ a) (φ b))
    (hφinj : Function.Injective (Sym2.map φ))
    {u v : V} {p : G.Walk u v} (hp : p.IsTrail) :
    (walkTransfer φ hφ p).IsTrail := by
  rw [SimpleGraph.Walk.isTrail_def] at hp ⊢
  rw [walkTransfer_edges]
  exact hp.map_on (fun a _ b _ h => hφinj h)

/-! ## Brick 3 — the fit, unpacked

Throughout this section, a putative fit is fixed: `β > 0`, a spectrum
`lam`, and an assignment `f` meeting every line within its entered
tolerance. The realized differences are positive, and the seven line
pairs are pairwise distinct as unordered pairs. -/

/-- Sum bookkeeping for one signed step: overwriting one vanishing
    coefficient of a sign pattern changes the weighted sum by exactly
    the new signed term. -/
lemma sum_sign_cons {σ : Fin 7 → ℤ} {m₀ : Fin 7} (h0 : σ m₀ = 0)
    (s₀ : ℤ) (g : Fin 7 → ℝ) :
    ∑ m, ((Function.update σ m₀ s₀ m : ℤ) : ℝ) * g m
      = ∑ m, (σ m : ℝ) * g m + (s₀ : ℝ) * g m₀ := by
  have key1 := Finset.add_sum_erase (Finset.univ : Finset (Fin 7))
    (fun m => ((Function.update σ m₀ s₀ m : ℤ) : ℝ) * g m)
    (Finset.mem_univ m₀)
  have key2 := Finset.add_sum_erase (Finset.univ : Finset (Fin 7))
    (fun m => (σ m : ℝ) * g m) (Finset.mem_univ m₀)
  have hdiff : ∑ m ∈ (Finset.univ : Finset (Fin 7)).erase m₀,
        ((Function.update σ m₀ s₀ m : ℤ) : ℝ) * g m
      = ∑ m ∈ (Finset.univ : Finset (Fin 7)).erase m₀,
        (σ m : ℝ) * g m := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_erase] at hm
    rw [Function.update_of_ne hm.1]
  have hterm : ((Function.update σ m₀ s₀ m₀ : ℤ) : ℝ) * g m₀
      = (s₀ : ℝ) * g m₀ := by
    rw [Function.update_self]
  have hterm0 : (σ m₀ : ℝ) * g m₀ = 0 := by
    rw [h0]
    simp
  linarith

section FitContext

variable (β : ℝ) (lam : Fin 7 → ℝ) (f : Fin 7 → Fin 7 × Fin 7)
variable (hfit : ∀ m : Fin 7,
  |modularFreqDiff β lam (f m).1 (f m).2 - (clockObs m : ℝ)|
    ≤ (clockObsErr m : ℝ))

include hfit

/-- The scaled level squares `x k = β * lam k ^ 2`. -/
noncomputable def xfit : Fin 7 → ℝ := fun k => β * lam k ^ 2

/-- The realized difference of line `m`. -/
noncomputable def dfit (m : Fin 7) : ℝ := xfit β lam (f m).1 - xfit β lam (f m).2

/- The realized difference is the modular frequency difference. -/
omit hfit in
lemma dfit_eq (m : Fin 7) :
    dfit β lam f m = modularFreqDiff β lam (f m).1 (f m).2 := by
  simp only [dfit, xfit, modularFreqDiff]
  ring

/-- Each realized difference meets its entered ratio within its
    entered uncertainty. -/
lemma dfit_approx (m : Fin 7) :
    |dfit β lam f m - (clockObs m : ℝ)| ≤ (clockObsErr m : ℝ) := by
  rw [dfit_eq]
  exact hfit m

/-- Each realized difference is strictly positive. -/
lemma dfit_pos (m : Fin 7) : 0 < dfit β lam f m := by
  have h1 := abs_le.mp (dfit_approx β lam f hfit m)
  have h2 : (clockObsErr m : ℝ) < (clockObs m : ℝ) := by
    exact_mod_cast clockObs_err_lt m
  have h3 : (0 : ℝ) ≤ (clockObsErr m : ℝ) := by
    exact_mod_cast clockObsErr_nonneg m
  linarith

/-- The unordered pair of levels assigned to line `m`. -/
def pairFit (m : Fin 7) : Sym2 (Fin 7) := s((f m).1, (f m).2)

/-- No line pair is a diagonal pair: the two levels differ. -/
lemma pairFit_ne_diag (m : Fin 7) (a : Fin 7) : pairFit f m ≠ s(a, a) := by
  intro hcon
  have hpos := dfit_pos β lam f hfit m
  rw [pairFit, Sym2.eq_iff] at hcon
  have hne : (f m).1 ≠ (f m).2 := by
    intro h
    rw [dfit, h] at hpos
    simp at hpos
  rcases hcon with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact hne (h1.trans h2.symm)

/-- **The seven line pairs are pairwise distinct.** An aligned
    repetition is killed by pair separation (`clockObs_pair_sep`);
    a swapped repetition by pair sums (`clockObs_pair_add`). -/
lemma pairFit_injective : Function.Injective (pairFit f) := by
  intro m m' h
  by_contra hne
  simp only [pairFit, Sym2.eq_iff] at h
  have h1 := dfit_approx β lam f hfit m
  have h2 := dfit_approx β lam f hfit m'
  have hb1 := abs_le.mp h1
  have hb2 := abs_le.mp h2
  rcases h with ⟨h1f, h2f⟩ | ⟨h1f, h2f⟩
  · -- Aligned: the realized differences agree.
    have hd : dfit β lam f m = dfit β lam f m' := by
      simp only [dfit, h1f, h2f]
    have hsep : (clockObsErr m : ℝ) + (clockObsErr m' : ℝ)
        < |(clockObs m : ℝ) - (clockObs m' : ℝ)| := by
      have hq := clockObs_pair_sep m m' hne
      have hcast : ((|clockObs m - clockObs m'| : ℚ) : ℝ)
          = |(clockObs m : ℝ) - (clockObs m' : ℝ)| := by
        push_cast
        ring
      rw [← hcast]
      exact_mod_cast hq
    have hle : |(clockObs m : ℝ) - (clockObs m' : ℝ)|
        ≤ (clockObsErr m : ℝ) + (clockObsErr m' : ℝ) := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  · -- Swapped: the realized differences are negatives of each other.
    have hd : dfit β lam f m' = -(dfit β lam f m) := by
      simp only [dfit, h1f, h2f]
      ring
    have hadd : (clockObsErr m : ℝ) + (clockObsErr m' : ℝ)
        < (clockObs m : ℝ) + (clockObs m' : ℝ) := by
      have hq := clockObs_pair_add m m'
      exact_mod_cast hq
    have hle : (clockObs m : ℝ) + (clockObs m' : ℝ)
        ≤ (clockObsErr m : ℝ) + (clockObsErr m' : ℝ) := by
      linarith
    linarith

/-- The graph of line pairs: seven edges on the seven levels. -/
def graphFit : SimpleGraph (Fin 7) :=
  SimpleGraph.fromEdgeSet (Set.range (pairFit f))

/-- The edge set of the line-pair graph is exactly the seven pairs. -/
lemma graphFit_edgeSet : (graphFit f).edgeSet = Set.range (pairFit f) := by
  unfold graphFit
  rw [SimpleGraph.edgeSet_fromEdgeSet, sdiff_eq_self_iff_disjoint,
    Set.disjoint_left]
  rintro e hdiag ⟨m, rfl⟩
  rw [Sym2.mem_diagSet] at hdiag
  have h12 : (f m).1 = (f m).2 := Sym2.mk_isDiag_iff.mp hdiag
  have hpos := dfit_pos β lam f hfit m
  rw [dfit, h12] at hpos
  simp at hpos

/-- Adjacency in the line-pair graph is carrying a line. -/
lemma graphFit_adj {a b : Fin 7} :
    (graphFit f).Adj a b ↔ ∃ m, pairFit f m = s(a, b) := by
  unfold graphFit
  rw [SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨m, hm⟩, -⟩
    exact ⟨m, hm⟩
  · rintro ⟨m, hm⟩
    refine ⟨⟨m, hm⟩, ?_⟩
    intro hab
    subst hab
    exact pairFit_ne_diag β lam f hfit m a hm

/-- The line-pair graph's edge set is finite, with the canonical
    instance used throughout this module. -/
noncomputable instance : Fintype (graphFit f).edgeSet :=
  (Set.finite_univ.subset (Set.subset_univ _)).fintype

/-- The line-pair graph has exactly seven edges. -/
lemma graphFit_edgeFinset_card : (graphFit f).edgeFinset.card = 7 := by
  have h1 : (graphFit f).edgeFinset = Finset.univ.image (pairFit f) := by
    ext e
    constructor
    · intro he
      have h2 : e ∈ (graphFit f).edgeSet := SimpleGraph.mem_edgeFinset.mp he
      rw [graphFit_edgeSet β lam f hfit] at h2
      obtain ⟨m, hm⟩ := h2
      exact Finset.mem_image.mpr ⟨m, Finset.mem_univ m, hm⟩
    · intro he
      obtain ⟨m, -, hm⟩ := Finset.mem_image.mp he
      apply SimpleGraph.mem_edgeFinset.mpr
      rw [graphFit_edgeSet β lam f hfit]
      exact ⟨m, hm⟩
  rw [h1, Finset.card_image_of_injective _ (pairFit_injective β lam f hfit),
    Finset.card_univ, Fintype.card_fin]

/-- The line carried by an edge of the line-pair graph, chosen once
    and for all; on edges outside the graph it defaults to line 0. -/
noncomputable def lineOf (e : Sym2 (Fin 7)) : Fin 7 :=
  if h : e ∈ Set.range (pairFit f) then h.choose else 0

/-- The chosen line really is carried by the edge. -/
lemma lineOf_spec {e : Sym2 (Fin 7)} (he : e ∈ Set.range (pairFit f)) :
    pairFit f (lineOf f e) = e := by
  unfold lineOf
  rw [dite_eq_left he]
  exact he.choose_spec

/-- **Telescope around a trail.** Along any trail in the line-pair
    graph, the endpoint potentials differ by a signed sum of the
    line differences: each traversed edge contributes its line
    exactly once, with sign `+1` if the trail crosses the line in
    its entered direction and `-1` otherwise. -/
lemma trail_telescope {a b : Fin 7} (p : (graphFit f).Walk a b) :
    p.IsTrail →
      ∃ σ : Fin 7 → ℤ,
        (∀ m, σ m = -1 ∨ σ m = 0 ∨ σ m = 1) ∧
        (∀ m, σ m ≠ 0 ↔ m ∈ (p.edges.map (lineOf f)).toFinset) ∧
        xfit β lam b - xfit β lam a
          = ∑ m, (σ m : ℝ) * dfit β lam f m := by
  induction p with
  | nil =>
    intro _
    refine ⟨0, ?_, ?_, ?_⟩
    · intro m
      exact Or.inr (Or.inl rfl)
    · intro m
      simp
    · simp
  | cons h p ih =>
    rename_i u v w
    intro hp
    obtain ⟨hp', hnotmem⟩ := (SimpleGraph.Walk.isTrail_cons h p).mp hp
    obtain ⟨σ, hval, hsupp, hid⟩ := ih hp'
    have hedg : s(u, v) ∈ (SimpleGraph.Walk.cons h p).edges := by
      rw [SimpleGraph.Walk.edges_cons]
      exact List.mem_cons_self
    have heSet : s(u, v) ∈ (graphFit f).edgeSet :=
      (SimpleGraph.Walk.cons h p).edges_subset_edgeSet hedg
    have hrange : s(u, v) ∈ Set.range (pairFit f) := by
      rwa [graphFit_edgeSet β lam f hfit] at heSet
    set m₀ := lineOf f s(u, v) with hm₀
    have hpf : pairFit f m₀ = s(u, v) := lineOf_spec β lam f hfit hrange
    have hpf2 : s((f m₀).1, (f m₀).2) = s(u, v) := hpf
    have hσ0 : σ m₀ = 0 := by
      by_contra hne0
      have hmem := (hsupp m₀).mp hne0
      rw [List.mem_toFinset, List.mem_map] at hmem
      obtain ⟨e', he', hline⟩ := hmem
      have he'Set : e' ∈ (graphFit f).edgeSet := p.edges_subset_edgeSet he'
      have hrange' : e' ∈ Set.range (pairFit f) := by
        rwa [graphFit_edgeSet β lam f hfit] at he'Set
      have hpe' : pairFit f (lineOf f e') = e' :=
        lineOf_spec β lam f hfit hrange'
      have he'eq : e' = s(u, v) := by
        rw [← hpe', hline]
        exact hpf
      exact hnotmem (he'eq ▸ he')
    have finish : ∀ s₀ : ℤ, (s₀ = -1 ∨ s₀ = 1) →
        (s₀ : ℝ) * dfit β lam f m₀ = xfit β lam v - xfit β lam u →
        ∃ σ' : Fin 7 → ℤ,
          (∀ m, σ' m = -1 ∨ σ' m = 0 ∨ σ' m = 1) ∧
          (∀ m, σ' m ≠ 0 ↔
            m ∈ ((SimpleGraph.Walk.cons h p).edges.map (lineOf f)).toFinset) ∧
          xfit β lam w - xfit β lam u
            = ∑ m, (σ' m : ℝ) * dfit β lam f m := by
      intro s₀ hs₀ hkey
      refine ⟨Function.update σ m₀ s₀, ?_, ?_, ?_⟩
      · intro m
        by_cases hm : m = m₀
        · subst hm
          rw [Function.update_self]
          rcases hs₀ with h | h
          · rw [h]
            exact Or.inl rfl
          · rw [h]
            exact Or.inr (Or.inr rfl)
        · rw [Function.update_of_ne hm]
          exact hval m
      · intro m
        by_cases hm : m = m₀
        · subst hm
          constructor
          · intro _
            rw [List.mem_toFinset, SimpleGraph.Walk.edges_cons,
              List.map_cons]
            exact List.mem_cons_self
          · intro _
            rw [Function.update_self]
            rcases hs₀ with h | h <;> rw [h] <;> norm_num
        · constructor
          · intro hne'
            rw [Function.update_of_ne hm] at hne'
            have hmem := (hsupp m).mp hne'
            rw [List.mem_toFinset] at hmem
            rw [List.mem_toFinset, SimpleGraph.Walk.edges_cons,
              List.map_cons, List.mem_cons]
            exact Or.inr hmem
          · intro hmem
            rw [List.mem_toFinset, SimpleGraph.Walk.edges_cons,
              List.map_cons, List.mem_cons] at hmem
            rcases hmem with h | h
            · exact absurd h hm
            · have hne' : σ m ≠ 0 :=
                (hsupp m).mpr (List.mem_toFinset.mpr h)
              rwa [Function.update_of_ne hm]
      · rw [sum_sign_cons hσ0 s₀ (dfit β lam f), ← hid, hkey]
        ring
    rcases Sym2.eq_iff.mp hpf2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · apply finish (-1) (Or.inl rfl)
      have hdfit : dfit β lam f m₀
          = xfit β lam u - xfit β lam v := by
        show xfit β lam (f m₀).1 - xfit β lam (f m₀).2 = _
        rw [h1, h2]
      rw [hdfit]
      ring
    · apply finish 1 (Or.inr rfl)
      have hdfit : dfit β lam f m₀
          = xfit β lam v - xfit β lam u := by
        show xfit β lam (f m₀).1 - xfit β lam (f m₀).2 = _
        rw [h1, h2]
      rw [hdfit]
      ring

end FitContext

/-! ## Brick 4 — components, counting, and the closed trail

General graph facts, stated for any simple graph on `Fin 7` with
seven edges. The vertex sets of the connected components partition
the seven vertices; the edge sets of the components partition the
seven edges; so some component has at least as many edges as
vertices. A spanning tree of that component has one fewer edge than
vertices, leaving an extra edge over; the tree path between its
endpoints, closed by the edge itself, is a closed trail. -/

/-- The edges of a graph whose two endpoints lie in a fixed
    component. -/
def edgeComp (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj]
    [Fintype G.edgeSet]
    (C : G.ConnectedComponent) : Finset (Sym2 (Fin 7)) :=
  G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ C.supp)

/-- Membership in a component's edge set. -/
lemma edgeComp_mem {G : SimpleGraph (Fin 7)} [DecidableRel G.Adj]
    [Fintype G.edgeSet]
    {C : G.ConnectedComponent} {e : Sym2 (Fin 7)} :
    e ∈ edgeComp G C ↔ e ∈ G.edgeFinset ∧ ∀ v ∈ e, v ∈ C.supp :=
  Finset.mem_filter

/-- The components' vertex counts sum to 7. -/
lemma sum_supp_card (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj] :
    ∑ C : G.ConnectedComponent, C.supp.toFinset.card = 7 := by
  have hunion : (Finset.univ : Finset G.ConnectedComponent).biUnion
        (fun C => C.supp.toFinset) = Finset.univ := by
    have hset : (((Finset.univ : Finset G.ConnectedComponent).biUnion
          (fun C => C.supp.toFinset)) : Set (Fin 7)) = Set.univ := by
      rw [Finset.coe_biUnion]
      simp only [Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
        Set.coe_toFinset]
      exact SimpleGraph.iUnion_connectedComponentSupp G
    exact Finset.coe_injective (by rwa [Finset.coe_univ])
  have hcard := Finset.card_biUnion
    (s := (Finset.univ : Finset G.ConnectedComponent))
    (t := fun C : G.ConnectedComponent => C.supp.toFinset)
    (fun x _ y _ hxy => Set.disjoint_toFinset.mpr
      (SimpleGraph.pairwise_disjoint_supp_connectedComponent G hxy))
  rw [hunion, Finset.card_univ, Fintype.card_fin] at hcard
  exact hcard.symm

/-- The components' edge counts sum to the graph's edge count. -/
lemma sum_edgeComp_card (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj]
    [Fintype G.edgeSet] :
    ∑ C : G.ConnectedComponent, (edgeComp G C).card
      = G.edgeFinset.card := by
  have hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset G.ConnectedComponent)) (edgeComp G) := by
    intro C _ C' _ hne
    apply Finset.disjoint_left.mpr
    rintro e heC heC'
    rw [edgeComp_mem] at heC heC'
    obtain ⟨a, b, hab⟩ := sym2_rep e
    have ha : a ∈ e := by
      rw [← hab]
      exact Sym2.mem_mk_left a b
    have h1 : a ∈ C.supp := heC.2 a ha
    have h2 : a ∈ C'.supp := heC'.2 a ha
    exact hne (SimpleGraph.ConnectedComponent.eq_of_common_vertex h1 h2)
  have hunion : (Finset.univ : Finset G.ConnectedComponent).biUnion
        (edgeComp G) = G.edgeFinset := by
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, edgeComp_mem]
    constructor
    · rintro ⟨C, he, -⟩
      exact he
    · intro he
      obtain ⟨a, b, hab⟩ := sym2_rep e
      have hadj : G.Adj a b := by
        have h1 : s(a, b) ∈ G.edgeSet := by
          rw [hab]
          exact SimpleGraph.mem_edgeFinset.mp he
        exact (SimpleGraph.mem_edgeSet _).mp h1
      refine ⟨G.connectedComponentMk a, he, ?_⟩
      intro v hv
      rw [← hab, Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
      · exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
          (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            hadj).symm
  have hcard := Finset.card_biUnion
    (s := (Finset.univ : Finset G.ConnectedComponent))
    (t := edgeComp G) hdisj
  exact hcard.symm.trans (congrArg Finset.card hunion)

/-- A component's edge count is the edge count of its induced
    graph. -/
lemma edgeComp_card_eq (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj]
    [Fintype G.edgeSet]
    (C : G.ConnectedComponent) [Fintype C.toSimpleGraph.edgeSet] :
    (edgeComp G C).card = (C.toSimpleGraph).edgeFinset.card := by
  refine (Finset.card_bij (fun e' _ => Sym2.map Subtype.val e') ?_ ?_ ?_).symm
  · -- The map lands in the component's edge set.
    intro e' he'
    obtain ⟨a, b, hab⟩ := sym2_rep e'
    have hadj : G.Adj a.val b.val := by
      have h1 : s(a, b) ∈ C.toSimpleGraph.edgeSet := by
        rw [hab]
        exact SimpleGraph.mem_edgeFinset.mp he'
      rw [SimpleGraph.mem_edgeSet] at h1
      exact (SimpleGraph.ConnectedComponent.toSimpleGraph_adj C
        a.property b.property).mp h1
    rw [← hab, Sym2.map_mk, edgeComp_mem]
    refine ⟨SimpleGraph.mem_edgeFinset.mpr
      (SimpleGraph.mem_edgeSet _ |>.mpr hadj), ?_⟩
    intro v hv
    rw [Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact a.property
    · exact b.property
  · -- The map is injective.
    intro e₁ _ e₂ _ h
    exact sym2_map_injective Subtype.val_injective h
  · -- The map is surjective onto the component's edge set.
    intro e he
    rw [edgeComp_mem] at he
    obtain ⟨a, b, hab⟩ := sym2_rep e
    have hadj : G.Adj a b := by
      have h1 : s(a, b) ∈ G.edgeSet := by
        rw [hab]
        exact SimpleGraph.mem_edgeFinset.mp he.1
      exact (SimpleGraph.mem_edgeSet _).mp h1
    have ha : a ∈ C.supp :=
      he.2 a (by rw [← hab]; exact Sym2.mem_mk_left a b)
    have hb : b ∈ C.supp :=
      he.2 b (by rw [← hab]; exact Sym2.mem_mk_right a b)
    refine ⟨s(⟨a, ha⟩, ⟨b, hb⟩), ?_, ?_⟩
    · refine SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet _).mpr ?_)
      exact (SimpleGraph.ConnectedComponent.toSimpleGraph_adj C ha hb).mpr
        hadj
    · rw [Sym2.map_mk]
      exact hab

/-- Some component has at least as many edges as vertices. -/
lemma exists_component_ge (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj]
    [Fintype G.edgeSet]
    (hG : G.edgeFinset.card = 7) :
    ∃ C : G.ConnectedComponent, C.supp.toFinset.card
      ≤ (edgeComp G C).card := by
  by_contra h
  push Not at h
  have hsum1 := sum_supp_card G
  have hsum2 := sum_edgeComp_card G
  have hle : ∑ C : G.ConnectedComponent, ((edgeComp G C).card + 1)
      ≤ ∑ C : G.ConnectedComponent, C.supp.toFinset.card :=
    Finset.sum_le_sum (fun C _ => h C)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ] at hle
  simp only [smul_eq_mul, mul_one] at hle
  have hcard : (0 : ℕ) < Fintype.card G.ConnectedComponent :=
    Fintype.card_pos_iff.mpr ⟨G.connectedComponentMk 0⟩
  omega

/-- A component with at least as many edges as vertices carries a
    closed trail: a spanning tree leaves an extra edge over, and the
    tree path between that edge's endpoints closes through it. -/
lemma closed_trail_of_component (G : SimpleGraph (Fin 7))
    [DecidableRel G.Adj] [Fintype G.edgeSet] (C : G.ConnectedComponent)
    [Fintype C.toSimpleGraph.edgeSet]
    (hC : C.supp.toFinset.card ≤ (edgeComp G C).card) :
    ∃ (v : Fin 7) (p : G.Walk v v), p.IsTrail ∧ p.edges ≠ [] := by
  have hEH : (C.toSimpleGraph).edgeFinset.card = (edgeComp G C).card :=
    (edgeComp_card_eq G C).symm
  classical
  have hV : Fintype.card ↥C = C.supp.toFinset.card := by
    rw [← Nat.card_eq_fintype_card, Set.toFinset_card,
      ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.refl _)
  obtain ⟨T, hTH, hT⟩ :=
    (SimpleGraph.ConnectedComponent.connected_toSimpleGraph C).exists_isTree_le
  have hET : T.edgeFinset.card + 1 = Fintype.card ↥C := hT.card_edgeFinset
  have hlt : T.edgeFinset.card < (C.toSimpleGraph).edgeFinset.card := by
    omega
  obtain ⟨e₀, he₀H, he₀T⟩ : ∃ e ∈ (C.toSimpleGraph).edgeFinset,
      e ∉ T.edgeFinset := by
    by_contra hcon
    push Not at hcon
    exact absurd (Finset.card_le_card hcon) (not_le_of_gt hlt)
  obtain ⟨a, b, hab⟩ := sym2_rep e₀
  have hadjH : C.toSimpleGraph.Adj a b := by
    have h1 : e₀ ∈ (C.toSimpleGraph).edgeSet :=
      SimpleGraph.mem_edgeFinset.mp he₀H
    rw [← hab] at h1
    exact (SimpleGraph.mem_edgeSet _).mp h1
  obtain ⟨pT, hpT, -⟩ := hT.existsUnique_path a b
  -- Transfer the tree path into the component graph and close it.
  set pH := walkTransfer id (fun {a b} (h : T.Adj a b) => hTH h) pT with hpH
  have hpH_trail : pH.IsTrail :=
    walkTransfer_isTrail id (fun {a b} (h : T.Adj a b) => hTH h)
      (sym2_map_injective Function.injective_id) hpT.isTrail
  set q : C.toSimpleGraph.Walk b a :=
    SimpleGraph.Walk.cons hadjH.symm SimpleGraph.Walk.nil with hq
  have hq_trail : q.IsTrail := by
    rw [hq, SimpleGraph.Walk.isTrail_cons]
    exact ⟨SimpleGraph.Walk.IsTrail.nil, by simp⟩
  have hq_edges : q.edges = [s(b, a)] := by simp [hq]
  have hdisj : pH.edges.Disjoint q.edges := by
    rw [hq_edges, List.disjoint_left]
    intro e he1 he2
    rw [List.mem_singleton] at he2
    subst he2
    have hmem : s(b, a) ∈ pH.edges := he1
    have hmemT : s(b, a) ∈ T.edgeFinset := by
      have h1 : s(b, a) ∈ pH.edges := hmem
      rw [hpH, walkTransfer_edges] at h1
      have h2 : ∃ e' ∈ pT.edges, Sym2.map id e' = s(b, a) := by
        rwa [List.mem_map] at h1
      obtain ⟨e', he', hmap⟩ := h2
      have h3 : e' = s(b, a) := by
        have hid : Sym2.map id e' = e' :=
          Sym2.inductionOn e' (fun x y => rfl)
        rw [hid] at hmap
        exact hmap
      exact SimpleGraph.mem_edgeFinset.mpr (h3 ▸ pT.edges_subset_edgeSet he')
    rw [Sym2.eq_swap] at hmemT
    exact he₀T (hab ▸ hmemT)
  have hclosed : (pH.append q).IsTrail :=
    (SimpleGraph.Walk.isTrail_append _ _).mpr ⟨hpH_trail, hq_trail, hdisj⟩
  -- Transfer the closed trail into the ambient graph.
  refine ⟨a.val, walkTransfer Subtype.val
    (fun {a b} (h : C.toSimpleGraph.Adj a b) =>
      (SimpleGraph.ConnectedComponent.toSimpleGraph_adj C a.property
        b.property).mp h) (pH.append q), ?_, ?_⟩
  · exact walkTransfer_isTrail Subtype.val _
      (sym2_map_injective Subtype.val_injective) hclosed
  · intro hcon
    have hmem : Sym2.map Subtype.val s(b, a)
        ∈ (walkTransfer Subtype.val
          (fun {a b} (h : C.toSimpleGraph.Adj a b) =>
            (SimpleGraph.ConnectedComponent.toSimpleGraph_adj C a.property
              b.property).mp h) (pH.append q)).edges := by
      rw [walkTransfer_edges]
      apply List.mem_map_of_mem
      rw [SimpleGraph.Walk.edges_append, hq_edges]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    rw [hcon] at hmem
    simp at hmem

/-- **A graph on `Fin 7` with seven edges carries a closed trail.** -/
lemma exists_closed_trail (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj]
    [Fintype G.edgeSet]
    (hG : G.edgeFinset.card = 7) :
    ∃ (v : Fin 7) (p : G.Walk v v), p.IsTrail ∧ p.edges ≠ [] := by
  obtain ⟨C, hC⟩ := exists_component_ge G hG
  letI : Fintype C.toSimpleGraph.edgeSet :=
    (Set.finite_univ.subset (Set.subset_univ _)).fintype
  exact closed_trail_of_component G C hC

/-- **The decision at N = 7: Q1′′ has no fit.**

    Suppose a fit existed. Its line-pair graph has seven edges on
    seven vertices, so it carries a closed trail (`exists_closed_trail`).
    Telescoping the potentials around the trail
    (`trail_telescope`) writes `0` as a signed sum
    `∑ σ * dfit` of the realized differences, with `σ` a nonzero
    sign pattern. Each realized difference lies within its entered
    uncertainty of the measured ratio (`dfit_approx`), so the same
    signed sum of the *measured* ratios is at most the total entered
    uncertainty `∑ clockObsErr < 10⁻¹¹` (`clockObsErr_sum_lt`). But
    the finite check (`sign_check`, the exact rational enumeration
    of Brick C discharged inside Lean) says every nonzero sign
    pattern satisfies `|∑ σ * clockObs| > 10⁻¹¹`. Contradiction.
    This decides the clock question at `N = 7` only: the table is
    T4 input, and nothing here touches `N ≤ 6` or any physics.
    NO CLAIM. -/
theorem measuredClockNoFit7 : ¬ measuredClockQuestion2 7 := by
  rintro ⟨β, lam, f, -, hfit⟩
  classical
  obtain ⟨v, p, htrail, hne⟩ := exists_closed_trail (graphFit f)
    (graphFit_edgeFinset_card β lam f hfit)
  obtain ⟨σ, hval, hsupp, hid⟩ := trail_telescope β lam f hfit p htrail
  have hsum0 : ∑ m, (σ m : ℝ) * dfit β lam f m = 0 := by
    rw [← hid, sub_self]
  have hσ : ∃ m, σ m ≠ 0 := by
    obtain ⟨e, he⟩ : ∃ e, e ∈ p.edges := by
      by_contra hcon
      push Not at hcon
      exact hne (List.eq_nil_iff_forall_not_mem.mpr hcon)
    exact ⟨lineOf f e, (hsupp _).mpr
      (List.mem_toFinset.mpr (List.mem_map_of_mem he))⟩
  have hsc := sign_check σ hval hσ
  have hscR : (1 / 10 ^ 11 : ℝ) < |∑ m, (σ m : ℝ) * (clockObs m : ℝ)| := by
    have hcast : ((|∑ m, σ m * clockObs m| : ℚ) : ℝ)
        = |∑ m, (σ m : ℝ) * (clockObs m : ℝ)| := by
      push_cast
      rfl
    calc (1 / 10 ^ 11 : ℝ) = ((1 / 10 ^ 11 : ℚ) : ℝ) := by norm_num
      _ < ((|∑ m, σ m * clockObs m| : ℚ) : ℝ) := by exact_mod_cast hsc
      _ = |∑ m, (σ m : ℝ) * (clockObs m : ℝ)| := hcast
  have hbound : |∑ m, (σ m : ℝ) * (clockObs m : ℝ)|
      ≤ ∑ m, (clockObsErr m : ℝ) := by
    have h1 : ∑ m, (σ m : ℝ) * (clockObs m : ℝ)
        = -∑ m, (σ m : ℝ) * (dfit β lam f m - (clockObs m : ℝ)) := by
      have hsplit : ∀ m : Fin 7, (σ m : ℝ) * (clockObs m : ℝ)
          = (σ m : ℝ) * dfit β lam f m
            - (σ m : ℝ) * (dfit β lam f m - (clockObs m : ℝ)) := by
        intro m
        ring
      rw [Finset.sum_congr rfl (fun m _ => hsplit m),
        Finset.sum_sub_distrib, hsum0, zero_sub]
    rw [h1, abs_neg]
    calc |∑ m, (σ m : ℝ) * (dfit β lam f m - (clockObs m : ℝ))|
        ≤ ∑ m, |(σ m : ℝ) * (dfit β lam f m - (clockObs m : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m, (clockObsErr m : ℝ) := by
          apply Finset.sum_le_sum
          intro m _
          have hσ1 : |(σ m : ℝ)| ≤ 1 := by
            rcases hval m with h | h | h <;> simp [h]
          calc |(σ m : ℝ) * (dfit β lam f m - (clockObs m : ℝ))|
              = |(σ m : ℝ)| * |dfit β lam f m - (clockObs m : ℝ)| :=
                abs_mul _ _
            _ ≤ 1 * (clockObsErr m : ℝ) :=
                mul_le_mul hσ1 (dfit_approx β lam f hfit m)
                  (abs_nonneg _) (by norm_num)
            _ = (clockObsErr m : ℝ) := one_mul _
  have hlt := clockObsErr_sum_lt
  linarith

/-! ## Brick 6 — the c = 1 witnesses at N = 8 and N = 9, re-derived

The exact fits of `MeasuredClockAnswer` and `MeasuredClockAnswer8`
meet every line exactly (residual `0`), so they answer Q1′′ at
their instances: residual `0` is within every entered per-line
tolerance. The witnesses are rebuilt here from the exported square
identities; nothing is extracted from the Q1′ theorems. -/

/-- **Q1′′ answered at N = 8**: the zero-anchored exact fit
    (`β = 1`, `lam = clockFitLam8`, `f = clockFitF8`) reproduces
    every entered ratio exactly, hence within its entered
    uncertainty. -/
theorem measuredClockAnswer2_8 : measuredClockQuestion2 8 := by
  refine ⟨1, clockFitLam8, clockFitF8, one_pos, ?_⟩
  intro m
  have h1 : (clockFitLam8 (clockFitF8 m).1) ^ 2 = (clockObs m : ℝ) := by
    have hnn : (0 : ℝ) ≤ clockFitSq8 (clockFitF8 m).1 := by
      rw [clockFitSq8_fst m]
      have h := clockObs_nonneg m
      have h' : (0 : ℝ) ≤ (clockObs m : ℝ) := by exact_mod_cast h
      linarith
    calc (clockFitLam8 (clockFitF8 m).1) ^ 2
        = clockFitSq8 (clockFitF8 m).1 := Real.sq_sqrt hnn
      _ = (clockObs m : ℝ) := clockFitSq8_fst m
  have h2 : (clockFitLam8 (clockFitF8 m).2) ^ 2 = 0 := by
    have hnn : (0 : ℝ) ≤ clockFitSq8 (clockFitF8 m).2 := by
      rw [clockFitSq8_snd m]
    calc (clockFitLam8 (clockFitF8 m).2) ^ 2
        = clockFitSq8 (clockFitF8 m).2 := Real.sq_sqrt hnn
      _ = 0 := clockFitSq8_snd m
  have hdiff : modularFreqDiff 1 clockFitLam8 (clockFitF8 m).1
        (clockFitF8 m).2 = (clockObs m : ℝ) := by
    rw [modularFreqDiff, h1, h2]
    ring
  rw [hdiff, sub_self, abs_zero]
  exact_mod_cast clockObsErr_nonneg m

/-- **Q1′′ answered at N = 9**: the shared-base exact fit
    (`β = 1`, `lam = clockFitLam`, `f = clockFitF`) reproduces
    every entered ratio exactly, hence within its entered
    uncertainty. -/
theorem measuredClockAnswer2_9 : measuredClockQuestion2 9 := by
  refine ⟨1, clockFitLam, clockFitF, one_pos, ?_⟩
  intro m
  have h1 : (clockFitLam (clockFitF m).1) ^ 2
      = 1 + (clockObs m : ℝ) := by
    have hnn : (0 : ℝ) ≤ clockFitSq (clockFitF m).1 := by
      rw [clockFitSq_fst m]
      have h := clockObs_nonneg m
      have h' : (0 : ℝ) ≤ (clockObs m : ℝ) := by exact_mod_cast h
      linarith
    calc (clockFitLam (clockFitF m).1) ^ 2
        = clockFitSq (clockFitF m).1 := Real.sq_sqrt hnn
      _ = 1 + (clockObs m : ℝ) := clockFitSq_fst m
  have h2 : (clockFitLam (clockFitF m).2) ^ 2 = 1 := by
    have hnn : (0 : ℝ) ≤ clockFitSq (clockFitF m).2 := by
      rw [clockFitSq_snd m]
      norm_num
    calc (clockFitLam (clockFitF m).2) ^ 2
        = clockFitSq (clockFitF m).2 := Real.sq_sqrt hnn
      _ = 1 := clockFitSq_snd m
  have hdiff : modularFreqDiff 1 clockFitLam (clockFitF m).1
        (clockFitF m).2 = (clockObs m : ℝ) := by
    rw [modularFreqDiff, h1, h2]
    ring
  rw [hdiff, sub_self, abs_zero]
  exact_mod_cast clockObsErr_nonneg m

end ThetLogos
