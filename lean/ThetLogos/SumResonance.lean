import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Sum resonance: coincidence counts for sums of finite rational spectra (RES-0)

Registration brick of the resonance line, per the scoping memo of
2026-10-30 (`routeb-general-scratch/scoping-resonance-2026-10-30.md`,
§2's Props and §6's pre-registered kills govern this module's language).

**Registered framing (the memo's, verbatim in substance).** Two systems
share a resonance iff they share a nonzero gap — the abstract
combinatorial statement of §2 (a2), nothing physical. "Harmonic",
"sympathetic", and "octave" in this line name ONLY the pinned
spectral-coincidence mathematics of §2: no acoustics, no physical-world
claim, no measured number derived or fitted, Dial 1 untouched.

**Naming fence.** The corpus already owns the word "resonance":
`ThetLogos.ResonanceSpectrum` defines a single system's resonance
spectrum as its GAP SET. That meaning stands and is not reused here.
This module's objects live BETWEEN spectra, in sums; the two notions
meet in exactly one place, and it is a theorem (RES-1's (a2)), not a pun.

**This brick (RES-0) is registration-grade only:** the definitions of
§2 in their exact forms, the named API (card of the sum index,
`diffCount` symmetry, `diffCount` at 0 as a sum of squared
multiplicities, the multiset↔family bridges), and small read-backs.
RES-1's shared-gap core — the collision inner-product identity (a1)
and the sharp criterion (a2) — is NOT proved here; it is the headline
brick, separately fired. K-RES-1 (the framing kill) is noted on the
face: raw coincidence counts at any seat are bookkeeping; the theorems
of this line are the criterion and the identity, not the counts.

NO CLAIM beyond the abstract finite-ℚ statements proved below.
-/

namespace ThetLogos

open Finset

variable {m n l : ℕ}

/-- The sum family of two finite rational tone families: the tones of
the Kronecker-sum spectrum, indexed by pairs. Memo §2, exact form. -/
def sumFam (a : Fin m → ℚ) (b : Fin n → ℚ) : Fin m × Fin n → ℚ :=
  fun p => a p.1 + b p.2

/-- The sum spectrum as a multiset: `Finset.univ.val.map` of `sumFam`.
Memo §2, exact form. -/
def sumSpec (a : Fin m → ℚ) (b : Fin n → ℚ) : Multiset ℚ :=
  Finset.univ.val.map (sumFam a b)

/-- The ternary sum family. Memo §2, exact form. -/
def sumFam3 (a : Fin m → ℚ) (b : Fin n → ℚ) (c : Fin l → ℚ) :
    Fin m × Fin n × Fin l → ℚ :=
  fun p => a p.1 + b p.2.1 + c p.2.2

/-- The ternary sum spectrum as a multiset. -/
def sumSpec3 (a : Fin m → ℚ) (b : Fin n → ℚ) (c : Fin l → ℚ) : Multiset ℚ :=
  Finset.univ.val.map (sumFam3 a b c)

/-- The multiplicity of tone `x` in the family `a`: the memo's `multA`
(and `multB`, the same function applied to the other factor). -/
def multA (a : Fin m → ℚ) (x : ℚ) : ℕ :=
  (Finset.univ.filter (fun i => a i = x)).card

/-- The difference-count function of `a`: the number of ordered pairs
with `a p.1 - a p.2 = d`. This is the multiplicity function of the
multiset form of `ResonanceSpectrum`'s gap set; the gap set itself is
its support. Memo §2, exact form. -/
def diffCount (a : Fin m → ℚ) (d : ℚ) : ℕ :=
  (Finset.univ.filter (fun p : Fin m × Fin m => a p.1 - a p.2 = d)).card

/-- The finite difference set (gap set) of `a`: the support of
`diffCount a`. Named in memo §2 (a1). -/
def diffRange (a : Fin m → ℚ) : Finset ℚ :=
  Finset.univ.image (fun p : Fin m × Fin m => a p.1 - a p.2)

/-- The difference multiset of `a`: the multiset form of the gap set,
whose multiplicity function is `diffCount a`. -/
def diffSpec (a : Fin m → ℚ) : Multiset ℚ :=
  Finset.univ.val.map (fun p : Fin m × Fin m => a p.1 - a p.2)

/-- Ordered collision pairs of the sum (diagonal included; the diagonal
contributes exactly `m * n`). Memo §2, exact form. -/
def collCount (a : Fin m → ℚ) (b : Fin n → ℚ) : ℕ :=
  (Finset.univ.filter (fun p : (Fin m × Fin n) × (Fin m × Fin n) =>
    sumFam a b p.1 = sumFam a b p.2)).card

/-- Ordered collision pairs of the ternary sum (diagonal included). -/
def collCount3 (a : Fin m → ℚ) (b : Fin n → ℚ) (c : Fin l → ℚ) : ℕ :=
  (Finset.univ.filter (fun p : (Fin m × Fin n × Fin l) × (Fin m × Fin n × Fin l) =>
    sumFam3 a b c p.1 = sumFam3 a b c p.2)).card

/-- Total degeneracy of the sum beyond distinctness:
`m * n` minus the number of distinct sum values. Memo §2, exact form. -/
def excess (a : Fin m → ℚ) (b : Fin n → ℚ) : ℕ :=
  m * n - (sumSpec a b).dedup.card

/-- The ZERO-FENCED scaled resonance count: pairs `(i, j)` with
`(q : ℚ) * a i = p * b j` and `a i ≠ 0`. The zero tone is excluded by
construction — `0` is resonant with `0` at every ratio simultaneously,
so an unfenced count counts the vacuum (memo §2 (b2); the fence is
load-bearing). Memo §2, exact form. -/
def resCount (p q : ℕ) (a : Fin m → ℚ) (b : Fin n → ℚ) : ℕ :=
  (Finset.univ.filter (fun ij : Fin m × Fin n =>
    (q : ℚ) * a ij.1 = (p : ℚ) * b ij.2 ∧ a ij.1 ≠ 0)).card

/-- Octave equivalence of rational tones: `y` is a power-of-two
multiple of `x`. Memo §2, exact form. -/
def OctEq (x y : ℚ) : Prop :=
  ∃ k : ℤ, y = (2 : ℚ) ^ k * x

/-- The octave invariant of a rational tone: its odd part,
`x / 2 ^ (padicValRat 2 x)`. For nonzero `x`, `octInv x` has 2-adic
valuation 0. Memo §2, exact form. -/
def octInv (x : ℚ) : ℚ :=
  x / (2 : ℚ) ^ (padicValRat 2 x)

/-- A finite octave chain in `S`: the tones `x, 2x, …, 2^k x` all lie
in `S`. By memo §2 (c2), finite spectra carry only finite chains —
no finite nonzero spectrum is doubling-invariant. Memo §2, exact form. -/
def OctChain (S : Finset ℚ) (x : ℚ) (k : ℕ) : Prop :=
  ∀ i ≤ k, (2 : ℚ) ^ i * x ∈ S

-- ============================================================================
-- API
-- ============================================================================

/-- Bridge: `sumSpec` is the multiset form of `sumFam`, by definition. -/
theorem sumSpec_eq_map (a : Fin m → ℚ) (b : Fin n → ℚ) :
    sumSpec a b = Finset.univ.val.map (sumFam a b) :=
  rfl

/-- Card of the sum index: the sum spectrum has exactly `m * n` tones,
counted with multiplicity. -/
theorem card_sumSpec (a : Fin m → ℚ) (b : Fin n → ℚ) :
    (sumSpec a b).card = m * n := by
  simp [sumSpec, Fintype.card_prod]

/-- Card of the ternary sum index: `m * n * l` tones with multiplicity. -/
theorem card_sumSpec3 (a : Fin m → ℚ) (b : Fin n → ℚ) (c : Fin l → ℚ) :
    (sumSpec3 a b c).card = m * n * l := by
  simp [sumSpec3, Fintype.card_prod, mul_assoc]

/-- Membership bridge, multiset↔family: a value lies in the sum
spectrum iff it is a sum of a pair of tones. -/
theorem mem_sumSpec {a : Fin m → ℚ} {b : Fin n → ℚ} {v : ℚ} :
    v ∈ sumSpec a b ↔ ∃ p, sumFam a b p = v := by
  simp [sumSpec, Multiset.mem_map]

/-- Count bridge, multiset↔family: the multiplicity of a value in the
sum spectrum is the number of tone pairs summing to it. -/
theorem count_sumSpec (a : Fin m → ℚ) (b : Fin n → ℚ) (v : ℚ) :
    (sumSpec a b).count v =
      (Finset.univ.filter (fun p => sumFam a b p = v)).card := by
  have hf : Finset.univ.filter (fun p => v = sumFam a b p)
      = Finset.univ.filter (fun p => sumFam a b p = v) :=
    Finset.filter_congr (fun p _ => eq_comm)
  rw [sumSpec_eq_map, Multiset.count_map, ← Finset.filter_val, hf]
  rfl

/-- Multiplicity bridge: the family multiplicity `multA a x` is the
multiset count of `x` in the tone multiset of `a`. -/
theorem multA_eq_count (a : Fin m → ℚ) (x : ℚ) :
    multA a x = (Finset.univ.val.map a).count x := by
  have hf : Finset.univ.filter (fun i => x = a i)
      = Finset.univ.filter (fun i => a i = x) :=
    Finset.filter_congr (fun i _ => eq_comm)
  rw [Multiset.count_map, ← Finset.filter_val, hf]
  rfl

/-- Difference bridge: `diffCount a d` is the multiset count of `d`
in the difference multiset `diffSpec a` — `diffCount` is the
multiplicity function of the gap multiset, as registered. -/
theorem diffCount_eq_count (a : Fin m → ℚ) (d : ℚ) :
    diffCount a d = (diffSpec a).count d := by
  have hf : Finset.univ.filter (fun p : Fin m × Fin m => d = a p.1 - a p.2)
      = Finset.univ.filter (fun p : Fin m × Fin m => a p.1 - a p.2 = d) :=
    Finset.filter_congr (fun p _ => eq_comm)
  rw [diffSpec, Multiset.count_map, ← Finset.filter_val, hf]
  rfl

/-- The difference set is the finset form of the difference multiset:
`diffRange a = (diffSpec a).toFinset`, i.e. the support of
`diffCount a`. -/
theorem diffRange_eq_toFinset (a : Fin m → ℚ) :
    diffRange a = (diffSpec a).toFinset := by
  ext x
  simp [diffRange, diffSpec, Multiset.mem_toFinset, Finset.mem_image]

/-- `diffCount` symmetry: `r(−d) = r(d)`, by swapping the pair. -/
theorem diffCount_neg (a : Fin m → ℚ) (d : ℚ) :
    diffCount a (-d) = diffCount a d := by
  unfold diffCount
  apply Finset.card_bij (fun p _ => (p.2, p.1))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    linarith
  · intro p₁ _ p₂ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 h.1
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨(p.2, p.1), by linarith, rfl⟩

/-- `diffCount` at `0` is the sum of squared multiplicities:
`diffCount a 0 = ∑ x ∈ range a, (multA a x)^2`, by fibering the
equal-tone pairs over their common value. -/
theorem diffCount_zero (a : Fin m → ℚ) :
    diffCount a 0 = ∑ x ∈ Finset.univ.image a, (multA a x) ^ 2 := by
  have hset : Finset.univ.filter (fun p : Fin m × Fin m => a p.1 - a p.2 = 0)
      = Finset.univ.filter (fun p : Fin m × Fin m => a p.1 = a p.2) := by
    apply Finset.filter_congr
    intro p _
    rw [sub_eq_zero]
  rw [diffCount, hset]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : Fin m × Fin m => a p.1)
    (t := Finset.univ.image a) ?_]
  · apply Finset.sum_congr rfl
    intro x _
    have hfiber : (Finset.univ.filter (fun p : Fin m × Fin m => a p.1 = a p.2)).filter
          (fun p => a p.1 = x)
        = (Finset.univ.filter (fun i => a i = x)) ×ˢ
          (Finset.univ.filter (fun j => a j = x)) := by
      ext ⟨i, j⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1.symm.trans h2⟩
      · rintro ⟨h2, h3⟩
        exact ⟨h2.trans h3.symm, h2⟩
    rw [hfiber, Finset.card_product, pow_two]
    rfl
  · intro p _
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem a (Finset.mem_univ p.1))

/-- The diagonal contributes exactly `m * n` collision pairs, so
`m * n ≤ collCount a b` — collisions beyond the diagonal are the
content (a2) measures. -/
theorem collCount_diag_le (a : Fin m → ℚ) (b : Fin n → ℚ) :
    m * n ≤ collCount a b := by
  have hinj : Function.Injective (fun p : Fin m × Fin n => (p, p)) := by
    intro p₁ p₂ h
    simpa using congrArg Prod.fst h
  have hcard : (Finset.univ.image (fun p : Fin m × Fin n => (p, p))).card = m * n := by
    rw [Finset.card_image_of_injective _ hinj]
    simp [Fintype.card_prod]
  have hsub : Finset.univ.image (fun p : Fin m × Fin n => (p, p)) ⊆
      Finset.univ.filter (fun p : (Fin m × Fin n) × (Fin m × Fin n) =>
        sumFam a b p.1 = sumFam a b p.2) := by
    intro q hq
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hq
    obtain ⟨p, rfl⟩ := hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  unfold collCount
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- Excess bookkeeping: excess plus the number of distinct sum values
is exactly `m * n`. -/
theorem excess_add_dedup_card (a : Fin m → ℚ) (b : Fin n → ℚ) :
    excess a b + (sumSpec a b).dedup.card = m * n := by
  unfold excess
  apply Nat.sub_add_cancel
  calc (sumSpec a b).dedup.card ≤ (sumSpec a b).card :=
        Multiset.card_le_card (Multiset.dedup_le _)
    _ = m * n := card_sumSpec a b

/-- The zero fence at work: an all-zero family resonates with nothing,
at any ratio — the vacuum is not counted. -/
theorem resCount_zero_family (p q : ℕ) (b : Fin n → ℚ) :
    resCount p q (fun _ : Fin m => (0 : ℚ)) b = 0 := by
  unfold resCount
  rw [Finset.filter_false_of_mem (fun ij _ h => h.2 rfl)]
  exact Finset.card_empty

/-- Doubling is an octave step: `OctEq x (2 * x)`, with `k = 1`. -/
theorem octEq_two_mul (x : ℚ) : OctEq x (2 * x) :=
  ⟨1, by simp⟩

-- ============================================================================
-- Read-backs: each definition unfolded once against a small named example
-- ============================================================================

/-- Named example family: tones `0, 1`. -/
def exA : Fin 2 → ℚ := ![0, 1]

/-- Named example family: tones `1, 2`. -/
def exB : Fin 2 → ℚ := ![1, 2]

/-- Read-back, `sumFam`: `exA 1 + exB 0 = 1 + 1 = 2`. -/
theorem rb_sumFam : sumFam exA exB (1, 0) = 2 := by
  norm_num [sumFam, exA, exB]

/-- Read-back, `sumFam3`: `exA 1 + exB 0 + exA 1 = 1 + 1 + 1 = 3`. -/
theorem rb_sumFam3 : sumFam3 exA exB exA (1, 0, 1) = 3 := by
  norm_num [sumFam3, exA, exB]

/-- Read-back, `sumSpec`: the sum spectrum of the examples has
`2 * 2 = 4` tones with multiplicity. -/
theorem rb_sumSpec_card : (sumSpec exA exB).card = 4 := by
  rw [card_sumSpec exA exB]

/-- Read-back, `multA`: tone `0` occurs once in `exA`. -/
theorem rb_multA_zero : multA exA 0 = 1 := by
  simp only [multA, Finset.card_filter, Fin.sum_univ_two]
  norm_num [exA]

/-- Read-back, `multA`: tone `1` occurs once in `exA`. -/
theorem rb_multA_one : multA exA 1 = 1 := by
  simp only [multA, Finset.card_filter, Fin.sum_univ_two]
  norm_num [exA]

/-- Read-back, `diffRange`: the gaps `1, -1, 0` all occur for `exA`. -/
theorem rb_diffRange_mem :
    (1 : ℚ) ∈ diffRange exA ∧ (-1 : ℚ) ∈ diffRange exA ∧ (0 : ℚ) ∈ diffRange exA := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [diffRange, Finset.mem_image, Finset.mem_univ, true_and]
  · exact ⟨(1, 0), by norm_num [exA]⟩
  · exact ⟨(0, 1), by norm_num [exA]⟩
  · exact ⟨(0, 0), by norm_num [exA]⟩

/-- Read-back, `diffCount`: for `exA = {0, 1}`, the zero difference
occurs twice (the two diagonal pairs). -/
theorem rb_diffCount_zero : diffCount exA 0 = 2 := by
  simp only [diffCount, Finset.card_filter, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num [exA]

/-- Read-back, `diffCount`: the difference `1` occurs once for `exA`. -/
theorem rb_diffCount_one : diffCount exA 1 = 1 := by
  simp only [diffCount, Finset.card_filter, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num [exA]

/-- Read-back, `resCount`: at the octave ratio `(p, q) = (2, 1)`,
`exB = {1, 2}` against `exA = {0, 1}` has exactly one fenced
resonance — the pair `(1, 1)`, where `1 * exB 1 = 2 * exA 1`. -/
theorem rb_resCount : resCount 2 1 exB exA = 1 := by
  simp only [resCount, Finset.card_filter, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num [exA, exB]

/-- Read-back, `OctEq`: `12` is two octaves above `3` (`k = 2`). -/
theorem rb_octEq : OctEq 3 12 :=
  ⟨2, by norm_num⟩

/-- Read-back, `octInv`: the odd part of `1` is `1`. -/
theorem rb_octInv_one : octInv 1 = 1 := by
  simp [octInv, padicValRat.one]

/-- Read-back, `octInv`: the odd part of `2` is `1` — `2` lies in the
octave class of `1`. -/
theorem rb_octInv_two : octInv 2 = 1 := by
  have h : padicValRat 2 (2 : ℚ) = 1 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num]
    exact padicValRat.self (by norm_num)
  rw [octInv, h]
  norm_num

/-- Read-back, `OctChain`: `{1, 2, 4}` carries the octave chain
`1, 2, 4` of length `2` above `1`. -/
theorem rb_octChain : OctChain ({1, 2, 4} : Finset ℚ) 1 2 := by
  intro i hi
  interval_cases i <;> norm_num

end ThetLogos

#print axioms ThetLogos.diffCount_neg
#print axioms ThetLogos.diffCount_zero
#print axioms ThetLogos.count_sumSpec
#print axioms ThetLogos.multA_eq_count
#print axioms ThetLogos.diffCount_eq_count
#print axioms ThetLogos.collCount_diag_le
#print axioms ThetLogos.excess_add_dedup_card
#print axioms ThetLogos.rb_resCount
