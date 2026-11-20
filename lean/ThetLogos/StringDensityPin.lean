/-
# StringDensityPin — the density of states of the thermal string seat

**Scope: ~/workspace/your_files/thermal-string-density-of-states-scope-2026-11-17.md
(Zero's "scope the pin" 2026-11-17, following the string-theory
comparison the same evening; build commissioned by his word
"build it", 2026-11-17). Working label only — final naming is Zero's.
NO CLAIM. Dial-ineligible.**

THE CONTENT: StringSeatPin's finite bendable chain has configurations
`c : Fin n → Fin (k+1)` and energy `bendEnergy c`, the total bend
content. The tree's `bendCost` is the 0/1 indicator — `0` on the
straight state, `1` on every bent state — verified from the definition
at DOS-0, so `bendEnergy` COUNTS bent links. This pin computes the
seat's DENSITY OF STATES: the number of configurations at energy level
`m` is exactly `Nat.choose n m * k^m` — choose which `m` links bend;
each bent link carries `k` non-straight states. Brick 2 adds the
log-concavity of the level counts, the hottest level, and the
no-Hagedorn bound as a theorem.

CITATION (DOS-2, cite-only — NOT re-proved here): the partition closed
form `partSum β = (1 + k * Real.exp (−β))^n` is already proved at lane
grade on branch `stringresponse` (StringResponsePin: `siteSum_eq` —
the single-site sum is exactly `1 + k·e^{−β}` — and
`partSum_bendEnergy_eq` — the partition sum is the `n`-th power of the
single-site sum), riding the INTEG-EVERYTHING T7 queue. It is cited,
never re-proved or double-counted in this module.

FIDELITY FENCES (non-negotiable, on the pin's face):
- NO HAGEDORN AT FINITE `n`. For fixed `n` the partition sum is a
  polynomial in `e^{−β}` — finite at every `β`, no divergence, no
  limiting temperature. K-STRING-HAGEDORN ARMED: any claim that this
  seat exhibits a Hagedorn transition is void. The Hagedorn rhyme
  lives only in the large-`n` growth of these level counts —
  Register-2-style analysis, citable prose, never a Lean claim from
  this pin.
- K-DOS-COUNT ARMED: the level count stands or falls with `bendCost`
  being the 0/1 indicator (verified at DOS-0 from the definition). If
  that ever changes upstream, this pin's closed form is void, not
  quietly re-based.
- K-DOS-COSTUME ARMED: no "temperature", "entropy", or "Hagedorn"
  word attaches to any definition in this pin that is not literally a
  count or a ratio of counts proved in this module.
- K-STRING-PHYS and K-STRING-KNOT remain armed from the parent seat:
  a finite toy; it does NOT model a physical string's mechanics; the
  pin's "knot" is bend content, not topological knot type.

STATUS: STATUS-STRINGDENSITY.md (worktree root).
-/

import Mathlib.Tactic
import ThetLogos.StringSeatPin
import ThetLogos.ModularVariance

namespace ThetLogos.StringDensityPin

open ThetLogos.StringSeatPin

variable {k : ℕ}

/-! ## §1 — the level set and its count (DOS-1) -/

/-- **Level set**: the configurations of the `n`-link chain whose bend
energy is exactly `m` — the seat's states at energy level `m`. -/
noncomputable def levelSet (n m : ℕ) : Finset (Fin n → Fin (k + 1)) :=
  Finset.univ.filter fun c => bendEnergy c = (m : ℝ)

/-- **Level count**: the density of states of the seat at level `m` —
the number of configurations whose bend energy is exactly `m`. -/
noncomputable def levelCount (n m : ℕ) : ℕ := (levelSet (k := k) n m).card

/-- **Fiber over a head value**: for a chain of `n + 1` links at level
`m + 1` whose head link carries the state `s`, the tails whose bend
energy makes up the rest of the level once the head link's bend cost
is paid. -/
noncomputable def fiberSet (n m : ℕ) (s : Fin (k + 1)) : Finset (Fin n → Fin (k + 1)) :=
  Finset.univ.filter (fun t => bendEnergy t = ((m + 1 : ℕ) : ℝ) - bendCost s)

/-- Splitting a configuration into its head link and its tail adds the
head link's bend cost to the tail's bend energy. -/
theorem bendEnergy_cons {n : ℕ} (s : Fin (k + 1)) (t : Fin n → Fin (k + 1)) :
    bendEnergy (Fin.cons s t) = bendCost s + bendEnergy t := by
  simp only [bendEnergy, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- **Recurrence**: a chain of `n + 1` links at level `m + 1` either
keeps its head link straight and puts all `m + 1` bends in the tail, or
bends its head link (`k` choices) and puts the remaining `m` bends in
the tail. -/
theorem levelCount_succ_succ (n m : ℕ) :
    levelCount (k := k) (n + 1) (m + 1) = levelCount (k := k) n (m + 1)
      + k * levelCount (k := k) n m := by
  classical
  have hfiber : ∀ s : Fin (k + 1), (fiberSet n m s).card
      = if s = 0 then levelCount (k := k) n (m + 1) else levelCount (k := k) n m := by
    intro s
    unfold levelCount
    by_cases hs : s = 0
    · have hcost : bendCost s = 0 := (bendCost_eq_zero_iff s).mpr hs
      have hval : ((m + 1 : ℕ) : ℝ) - bendCost s = ((m + 1 : ℕ) : ℝ) := by
        rw [hcost, sub_zero]
      have hfin : fiberSet n m s = levelSet n (m + 1) := by
        unfold fiberSet levelSet
        apply Finset.filter_congr
        intro t _
        rw [hval]
      rw [if_pos hs, hfin]
    · have hcost : bendCost s = 1 := by
        unfold bendCost
        rw [if_neg hs]
      have hval : ((m + 1 : ℕ) : ℝ) - bendCost s = (m : ℝ) := by
        rw [hcost]
        push_cast
        ring
      have hfin : fiberSet n m s = levelSet n m := by
        unfold fiberSet levelSet
        apply Finset.filter_congr
        intro t _
        rw [hval]
      rw [if_neg hs, hfin]
  have hsplit : levelCount (k := k) (n + 1) (m + 1)
      = ∑ s : Fin (k + 1), (fiberSet n m s).card := by
    unfold levelCount
    rw [← Finset.card_sigma]
    apply Finset.card_bij
      (fun c _ => (⟨c 0, Fin.tail c⟩ : Σ _ : Fin (k + 1), Fin n → Fin (k + 1)))
    · intro c hc
      simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and, fiberSet,
        Finset.mem_filter, true_and]
      have hdec : bendEnergy c
          = bendCost (c 0) + bendEnergy (Fin.tail c) := by
        conv_lhs => rw [← Fin.cons_self_tail c]
        exact bendEnergy_cons _ _
      rw [hc] at hdec
      linarith
    · intro c₁ _ c₂ _ h
      have hcons : Fin.cons (c₁ 0) (Fin.tail c₁)
          = Fin.cons (c₂ 0) (Fin.tail c₂) := by
        have h1 : c₁ 0 = c₂ 0 := congrArg Sigma.fst h
        have h2 : Fin.tail c₁ = Fin.tail c₂ := congrArg Sigma.snd h
        rw [h1, h2]
      rwa [Fin.cons_self_tail, Fin.cons_self_tail] at hcons
    · intro p hp
      obtain ⟨s, t⟩ := p
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and, fiberSet,
        Finset.mem_filter, true_and] at hp
      refine ⟨Fin.cons s t, ?_, ?_⟩
      · simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [bendEnergy_cons]
        linarith [hp]
      · simp only [Fin.cons_zero, Fin.tail_cons]
  rw [hsplit]
  trans ∑ s : Fin (k + 1),
    (if s = 0 then levelCount (k := k) n (m + 1) else levelCount (k := k) n m)
  · exact Finset.sum_congr rfl (fun s _ => hfiber s)
  rw [← Finset.add_sum_erase Finset.univ _
    (Finset.mem_univ (0 : Fin (k + 1))), if_pos rfl]
  congr 1
  rw [Finset.sum_congr rfl
      (fun s hs => if_neg (Finset.ne_of_mem_erase hs)),
    Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin (k + 1))),
    Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel, smul_eq_mul]

/-- **DOS-1 — the level count.** The density of states of the thermal
string seat: exactly `Nat.choose n m * k^m` configurations of the
`n`-link chain have bend energy `m` — choose which `m` links bend;
each bent link carries `k` non-straight states. -/
theorem levelCount_eq (n m : ℕ) : levelCount (k := k) n m = n.choose m * k ^ m := by
  induction n generalizing m with
  | zero =>
    have hE : ∀ c : Fin 0 → Fin (k + 1), bendEnergy c = 0 :=
      fun c => Finset.sum_eq_zero (fun i _ => i.elim0)
    cases m with
    | zero =>
      have hset : levelSet (k := k) 0 0 = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro c
        simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and,
          Nat.cast_zero]
        exact hE c
      rw [levelCount, hset, Finset.card_univ]
      simp [Fintype.card_fun]
    | succ m =>
      have hne : ∀ c : Fin 0 → Fin (k + 1),
          bendEnergy c ≠ ((m + 1 : ℕ) : ℝ) := by
        intro c
        rw [hE c]
        exact ne_of_lt (by exact_mod_cast Nat.succ_pos m)
      rw [levelCount, levelSet,
        Finset.filter_false_of_mem (fun c _ => hne c)]
      simp [Nat.choose_eq_zero_of_lt (Nat.succ_pos m)]
  | succ n ih =>
    cases m with
    | zero =>
      have hset : levelSet (k := k) (n + 1) 0 = {straightConfig} := by
        ext c
        simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton, Nat.cast_zero]
        exact bendEnergy_eq_zero_iff c
      simp [levelCount, hset]
    | succ m =>
      rw [levelCount_succ_succ, ih (m + 1), ih m, Nat.choose_succ_succ']
      ring

/-- Above the top level there are no states: a chain of `n` links
cannot bend more than `n` times. -/
theorem levelCount_eq_zero_of_lt {n m : ℕ} (h : n < m) :
    levelCount (k := k) n m = 0 := by
  rw [levelCount_eq, Nat.choose_eq_zero_of_lt h, Nat.zero_mul]

/-- **Ratio identity**: successive level counts obey
`g (m+1) · (m+1) = g m · k · (n − m)` — the discrete crossing law from
which the hottest level is read off. From the closed form (DOS-1) and
`Nat.choose_succ_right_eq`. -/
theorem levelCount_ratio_mul (n m : ℕ) :
    levelCount (k := k) n (m + 1) * (m + 1) = levelCount (k := k) n m * (k * (n - m)) := by
  rw [levelCount_eq, levelCount_eq, pow_succ]
  have hc := Nat.choose_succ_right_eq n m
  calc (n.choose (m + 1) * (k ^ m * k)) * (m + 1)
      = (n.choose (m + 1) * (m + 1)) * (k ^ m * k) := by ring
    _ = (n.choose m * (n - m)) * (k ^ m * k) := by rw [hc]
    _ = (n.choose m * k ^ m) * (k * (n - m)) := by ring

/-- **DOS-3 — log-concavity of the level counts**: for `1 ≤ m` and
`m + 1 ≤ n`, `g (m−1) · g (m+1) ≤ (g m)^2`. Proved from the ratio
identity alone: the factor `g (m−1) · k · (n − m)` sits below
`g m · (m + 1)`, and the common factor `(m + 1)` cancels. -/
theorem levelCount_logConcave {n m : ℕ} (hm : 1 ≤ m) (hmn : m + 1 ≤ n) :
    levelCount (k := k) n (m - 1) * levelCount (k := k) n (m + 1)
      ≤ (levelCount (k := k) n m) ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hA := levelCount_ratio_mul (k := k) n (j + 1)
  have hB := levelCount_ratio_mul (k := k) n j
  have key : levelCount (k := k) n j * (k * (n - (j + 1)))
      ≤ levelCount (k := k) n (j + 1) * (j + 1 + 1) := by
    calc levelCount n j * (k * (n - (j + 1)))
        ≤ levelCount n j * (k * (n - j)) := by
          exact Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (by omega))
      _ = levelCount n (j + 1) * (j + 1) := hB.symm
      _ ≤ levelCount n (j + 1) * (j + 1 + 1) :=
          Nat.mul_le_mul le_rfl (by omega)
  have hmain : (levelCount (k := k) n j * levelCount (k := k) n (j + 1 + 1)) * (j + 1 + 1)
      ≤ (levelCount (k := k) n (j + 1)) ^ 2 * (j + 1 + 1) := by
    have e1 : (levelCount (k := k) n j * levelCount (k := k) n (j + 1 + 1)) * (j + 1 + 1)
        = levelCount (k := k) n (j + 1)
          * (levelCount (k := k) n j * (k * (n - (j + 1)))) := by
      rw [mul_assoc, hA]; ring
    have e2 : (levelCount (k := k) n (j + 1)) ^ 2 * (j + 1 + 1)
        = levelCount (k := k) n (j + 1)
          * (levelCount (k := k) n (j + 1) * (j + 1 + 1)) := by
      rw [pow_two]; ring
    rw [e1, e2]
    exact Nat.mul_le_mul le_rfl key
  exact Nat.le_of_mul_le_mul_right hmain (by omega)

/-- **DOS-4 — the hottest level**: the level count attains its maximum
at some level `m ≤ n`, and at that level the counts have stopped
rising in both directions — the crossing characterization: nothing
above the peak exceeds it, and the level just below the peak does not
exceed it either. Together with `levelCount_ratio_mul` this locates
the peak where `k · (n − m)` crosses `m + 1`. -/
theorem levelCount_exists_max (n : ℕ) :
    ∃ m ≤ n, (∀ j ≤ n, levelCount (k := k) n j ≤ levelCount (k := k) n m)
      ∧ (m + 1 ≤ n → levelCount (k := k) n (m + 1) ≤ levelCount (k := k) n m)
      ∧ (1 ≤ m → levelCount (k := k) n (m - 1) ≤ levelCount (k := k) n m) := by
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.range (n + 1))
    (levelCount (k := k) n) ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
  have hmn : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
  refine ⟨m, hmn, fun j hj => hmax j (Finset.mem_range.mpr (by omega)),
    fun h => hmax (m + 1) (Finset.mem_range.mpr (by omega)),
    fun _ => hmax (m - 1) (Finset.mem_range.mpr (by omega))⟩

/-- **The no-Hagedorn bound, as a theorem** (the fence on this pin's
face): for `β ≥ 0` the partition sum of the finite chain is at most
`(k + 1)^n` — every Boltzmann weight is at most `1` because the bend
energy is nonnegative, and there are `(k + 1)^n` configurations. A
finite sum of bounded weights: no divergence, no limiting
temperature, at any finite `n`. Proved directly, independent of the
cited closed form. -/
theorem partSum_bendEnergy_le (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    ModularVariance.partSum (fun c : Fin n → Fin (k + 1) => bendEnergy c) β
      ≤ ((k : ℝ) + 1) ^ n := by
  have hterm : ∀ c : Fin n → Fin (k + 1),
      Real.exp (-(β * bendEnergy c)) ≤ 1 := by
    intro c
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg hβ (bendEnergy_nonneg c))
  calc ModularVariance.partSum (fun c : Fin n → Fin (k + 1) => bendEnergy c) β
      = ∑ c : Fin n → Fin (k + 1), Real.exp (-(β * bendEnergy c)) := rfl
    _ ≤ ∑ _c : Fin n → Fin (k + 1), (1 : ℝ) :=
        Finset.sum_le_sum (fun c _ => hterm c)
    _ = ((k : ℝ) + 1) ^ n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, mul_one]
        push_cast
        ring
