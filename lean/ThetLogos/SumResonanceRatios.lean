import Mathlib.Tactic
import ThetLogos.SumResonance
import ThetLogos.SumResonanceCore
import ThetLogos.SumResonanceForcing

/-!
# Sum resonance: ratios and octaves (RES-3)

Fourth brick of the resonance line, per the coordinator pack
`routeb-general-scratch/pack-res-3.md` and the ratified scoping memo
`routeb-general-scratch/scoping-resonance-2026-10-30.md` (§2(b),
§2(c), and §3's (b)/(c) verdicts). RES-0's vocabulary
(`ThetLogos.SumResonance`: `resCount` zero-fenced, `OctEq`, `octInv`,
`OctChain`, `multA`), RES-1's core (`ThetLogos.SumResonanceCore`),
and RES-2's scaling family (`scaleFam`, `ThetLogos.SumResonanceForcing`)
are cited, never forked.

**Content (memo §2(b)–(c), statements registered in substance).**
- (b1) Unison is the overlap inner product of the multiplicity
  functions, and the general ratio count is the unison count after
  scaling one side by `p / q` — one theorem for all ratios. The
  ratio form is stated for `q ≠ 0` (a ratio `p / q` presupposes it).
- (b2) The zero-fence lemma: the unfenced count is the fenced count
  plus exactly `multA a 0 * multA b 0`, at any ratio with `p ≠ 0`
  (`0` is resonant with `0` at every such ratio, and the zero tones
  contribute exactly that product and nothing else). The degenerate
  case `p = 0` genuinely differs — there every `b`-tone pairs with
  a zero `a`-tone — and is proved separately at full rank
  (`resCountAll_zero_left`); the fence identity is not asserted
  there, because it is false there.
- (b3) Geometric-family closed forms: the octave ladder
  `g i = 2 ^ i` has `resCount 2 1 g g = k` and `resCount 3 2 g g = 0`
  (the fifth would need odd part `3` inside a power of `2`).
- (c1) The octave-class invariant: for positive rationals,
  `OctEq x y ↔ octInv x = octInv y` (odd parts agree; powers of `2`
  are exactly the class of `1`).
- (c2) No finite octave closure (kill-grade): a doubling-invariant
  finite finset of rationals not containing `0` is empty; and an
  octave chain's top tone is bounded by the finset's maximum.
- (c3) The two extremal class censuses: the geometric family lies in
  ONE octave class; the arithmetic family `{1, …, L}` meets exactly
  the odd numbers `≤ L` as classes — `(L + 1) / 2` of them.

**K-RES-1 (pre-registered framing kill), noted on the face:** raw
resonance counts at any seat are bookkeeping; the theorems of this
line are the identities, the fence, the invariant, and the
impossibility, never the raw counts.

**(c2) carries its kill-grade framing (memo §2(c2), verbatim in
substance):** a finite nonzero spectrum is NEVER doubling-invariant:
the doubling orbit of any tone is infinite. Hence "octave structure"
in any finite spectrum means finite `OctChain`s only, and the maximal
chain length in `S` is bounded by the spectrum's own range. Any future
claim of an "octave-complete" finite spectrum dies against (c2) on
sight.

NO CLAIM beyond the abstract finite-ℚ statements proved below.
"Harmonic / sympathetic / octave" name only the pinned mathematics
of the memo's §2: no acoustics, no physical-world claim, no measured
number derived or fitted. Dial 1 untouched; dials 0/4.
-/

namespace ThetLogos

open Finset

variable {m n : ℕ}

/-- The UNFENCED scaled resonance count: pairs `(i, j)` with
`(q : ℚ) * a i = p * b j`, with no exclusion of the zero tone.
Memo §2 (b2): RES-0 defined only the fenced `resCount`; the
unfenced variant is defined here so the fence can be priced. -/
def resCountAll (p q : ℕ) (a : Fin m → ℚ) (b : Fin n → ℚ) : ℕ :=
  (Finset.univ.filter (fun ij : Fin m × Fin n =>
    (q : ℚ) * a ij.1 = (p : ℚ) * b ij.2)).card

/-- The geometric family (the octave ladder itself):
`g : Fin (k + 1) → ℚ`, `g i = 2 ^ i`. Memo §2 (b3). -/
def geomFam (k : ℕ) : Fin (k + 1) → ℚ :=
  fun i => (2 : ℚ) ^ i.val

/-- The arithmetic family `{1, …, L}` as a finset of rationals.
Memo §2 (c3). -/
def arithSet (L : ℕ) : Finset ℚ :=
  (Finset.Icc 1 L).image (fun t : ℕ => (t : ℚ))

-- ============================================================================
-- (b1), unfenced form: unison is the overlap inner product
-- ============================================================================

/-- **(b1), unfenced unison.** The unfenced unison count is exactly
the overlap inner product of the two multiplicity functions, summed
over the first family's tones (the summand vanishes off the first
family's range, by `multA`'s definition). The fenced form
`resCount_one_one` below is this theorem plus the fence (b2). -/
theorem resCountAll_one_one (a : Fin m → ℚ) (b : Fin n → ℚ) :
    resCountAll 1 1 a b
      = ∑ x ∈ Finset.univ.image a, multA a x * multA b x := by
  have hs : Finset.univ.filter (fun ij : Fin m × Fin n =>
        ((1 : ℕ) : ℚ) * a ij.1 = ((1 : ℕ) : ℚ) * b ij.2)
      = Finset.univ.filter (fun ij : Fin m × Fin n => a ij.1 = b ij.2) :=
    Finset.filter_congr (fun ij _ => by simp)
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter (fun ij : Fin m × Fin n => a ij.1 = b ij.2))
    (t := Finset.univ.image a)
    (f := fun ij : Fin m × Fin n => a ij.1) (by
      intro ij _
      exact Finset.mem_image_of_mem a (Finset.mem_univ ij.1))
  unfold resCountAll
  rw [hs, h]
  apply Finset.sum_congr rfl
  intro x _
  have hfiber : (Finset.univ.filter (fun ij : Fin m × Fin n => a ij.1 = b ij.2)).filter
        (fun ij => a ij.1 = x)
      = (Finset.univ.filter (fun i => a i = x)) ×ˢ
        (Finset.univ.filter (fun j => b j = x)) := by
    rw [Finset.filter_filter]
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1.symm.trans h2⟩
    · rintro ⟨h2, h3⟩
      exact ⟨h2.trans h3.symm, h2⟩
  rw [hfiber, Finset.card_product]
  rfl

-- ============================================================================
-- (b2) The zero-fence lemma
-- ============================================================================

/-- **(b2) The zero-fence lemma** (memo §2 (b2)): at any ratio with
`p ≠ 0`, the unfenced count is the fenced count plus exactly
`multA a 0 * multA b 0` — `0` is resonant with `0` at every such
ratio, and the zero tones contribute exactly that product and
nothing else. Any dossier reporting an unfenced resonance count at
a seat with zero tones has counted the vacuum and called it music;
the fence is in RES-0's definition so it cannot be forgotten. -/
theorem resCountAll_eq_add (p q : ℕ) (hp : p ≠ 0) (a : Fin m → ℚ) (b : Fin n → ℚ) :
    resCountAll p q a b
      = resCount p q a b + multA a 0 * multA b 0 := by
  have hpQ : ((p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hp
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun ij : Fin m × Fin n =>
      (q : ℚ) * a ij.1 = (p : ℚ) * b ij.2))
    (p := fun ij : Fin m × Fin n => a ij.1 ≠ 0)
  have hF : (Finset.univ.filter (fun ij : Fin m × Fin n =>
        (q : ℚ) * a ij.1 = (p : ℚ) * b ij.2)).filter
        (fun ij => a ij.1 ≠ 0)
      = Finset.univ.filter (fun ij : Fin m × Fin n =>
        (q : ℚ) * a ij.1 = (p : ℚ) * b ij.2 ∧ a ij.1 ≠ 0) := by
    rw [Finset.filter_filter]
  have hZ : (Finset.univ.filter (fun ij : Fin m × Fin n =>
        (q : ℚ) * a ij.1 = (p : ℚ) * b ij.2)).filter
        (fun ij => ¬ a ij.1 ≠ 0)
      = (Finset.univ.filter (fun i => a i = 0)) ×ˢ
        (Finset.univ.filter (fun j => b j = 0)) := by
    rw [Finset.filter_filter]
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    constructor
    · rintro ⟨hP, hna⟩
      have hai : a i = 0 := by
        by_contra hne
        exact hna hne
      refine ⟨hai, ?_⟩
      have h0 : (p : ℚ) * b j = 0 := by
        have hP' := hP
        rw [hai, mul_zero] at hP'
        exact hP'.symm
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hpQ
      · exact h
    · rintro ⟨hai, hbj⟩
      refine ⟨?_, ?_⟩
      · rw [hai, hbj, mul_zero, mul_zero]
      · intro hne
        exact hne hai
  unfold resCountAll resCount multA
  rw [← hF, ← Finset.card_product, ← hZ]
  exact hsplit.symm

/-- **(b2), the degenerate ratio `p = 0`, at full rank.** With
`p = 0` the unfenced condition on a zero `a`-tone is vacuous in
`b`, so the zero tones contribute `multA a 0 * n`, NOT
`multA a 0 * multA b 0`: the fence identity of `resCountAll_eq_add`
is false at `p = 0`, which is exactly why that lemma carries the
hypothesis `p ≠ 0`. The named ratios `(1,1)`, `(2,1)`, `(3,2)` all
have `p ≠ 0` and are unaffected. -/
theorem resCountAll_zero_left (q : ℕ) (a : Fin m → ℚ) (b : Fin n → ℚ) :
    resCountAll 0 q a b = resCount 0 q a b + multA a 0 * n := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun ij : Fin m × Fin n =>
      (q : ℚ) * a ij.1 = ((0 : ℕ) : ℚ) * b ij.2))
    (p := fun ij : Fin m × Fin n => a ij.1 ≠ 0)
  have hF : (Finset.univ.filter (fun ij : Fin m × Fin n =>
        (q : ℚ) * a ij.1 = ((0 : ℕ) : ℚ) * b ij.2)).filter
        (fun ij => a ij.1 ≠ 0)
      = Finset.univ.filter (fun ij : Fin m × Fin n =>
        (q : ℚ) * a ij.1 = ((0 : ℕ) : ℚ) * b ij.2 ∧ a ij.1 ≠ 0) := by
    rw [Finset.filter_filter]
  have hZ : (Finset.univ.filter (fun ij : Fin m × Fin n =>
        (q : ℚ) * a ij.1 = ((0 : ℕ) : ℚ) * b ij.2)).filter
        (fun ij => ¬ a ij.1 ≠ 0)
      = (Finset.univ.filter (fun i => a i = 0)) ×ˢ Finset.univ := by
    rw [Finset.filter_filter]
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    constructor
    · rintro ⟨-, hna⟩
      have hai : a i = 0 := by
        by_contra hne
        exact hna hne
      exact ⟨hai, trivial⟩
    · rintro ⟨hai, -⟩
      refine ⟨?_, ?_⟩
      · simp [hai]
      · intro hne
        exact hne hai
  have hZcard : ((Finset.univ.filter (fun ij : Fin m × Fin n =>
        (q : ℚ) * a ij.1 = ((0 : ℕ) : ℚ) * b ij.2)).filter
        (fun ij => ¬ a ij.1 ≠ 0)).card
      = (Finset.univ.filter (fun i => a i = 0)).card * n := by
    rw [hZ, Finset.card_product, Finset.card_univ, Fintype.card_fin]
  unfold resCountAll resCount multA
  rw [← hF, ← hZcard]
  exact hsplit.symm

-- ============================================================================
-- (b1) Unison is overlap; all ratios from one theorem
-- ============================================================================

/-- **(b1) Unison is overlap** (memo §2 (b1)): the fenced unison
count is the overlap inner product of the multiplicity functions,
summed over the nonzero tones of the first family — the zero term
of the unfenced inner product `resCountAll_one_one` is exactly the
fence correction `multA a 0 * multA b 0` of (b2). Scaled resonance
at ratio `1` is exactly shared-tone counting. -/
theorem resCount_one_one (a : Fin m → ℚ) (b : Fin n → ℚ) :
    resCount 1 1 a b
      = ∑ x ∈ (Finset.univ.image a).erase 0, multA a x * multA b x := by
  have hfence := resCountAll_eq_add 1 1 (by norm_num) a b
  have hall := resCountAll_one_one a b
  by_cases h0 : (0 : ℚ) ∈ Finset.univ.image a
  · have hsum : multA a 0 * multA b 0
        + ∑ x ∈ (Finset.univ.image a).erase 0, multA a x * multA b x
        = ∑ x ∈ Finset.univ.image a, multA a x * multA b x :=
      Finset.add_sum_erase _ (fun x => multA a x * multA b x) h0
    omega
  · have hma : multA a 0 = 0 := by
      unfold multA
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact h0 (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
    have herase : (Finset.univ.image a).erase 0 = Finset.univ.image a :=
      Finset.erase_eq_of_notMem h0
    rw [hma, Nat.zero_mul, Nat.add_zero] at hfence
    rw [herase, ← hfence]
    exact hall

/-- **(b1), the general ratio form** (memo §2 (b1)): for `q ≠ 0`,
the `(p, q)` resonance count is the unison count against the
second family scaled by the ratio `p / q` (RES-2's `scaleFam`).
Stated once, used everywhere: every ratio count is an overlap
count after scaling. -/
theorem resCount_eq_one_one_scale (p q : ℕ) (hq : q ≠ 0)
    (a : Fin m → ℚ) (b : Fin n → ℚ) :
    resCount p q a b
      = resCount 1 1 a (scaleFam ((p : ℚ) / (q : ℚ)) b) := by
  have hqQ : ((q : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hq
  have key : ∀ ij : Fin m × Fin n,
      (q : ℚ) * a ij.1 = (p : ℚ) * b ij.2
        ↔ a ij.1 = ((p : ℚ) / (q : ℚ)) * b ij.2 := by
    intro ij
    rw [div_mul_eq_mul_div, eq_div_iff hqQ]
    constructor
    · intro h
      linear_combination h
    · intro h
      linear_combination h
  unfold resCount
  congr 1
  apply Finset.filter_congr
  intro ij _
  have h1 : ((1 : ℕ) : ℚ) * a ij.1 = a ij.1 := by simp
  have h2 : ((1 : ℕ) : ℚ) * scaleFam ((p : ℚ) / (q : ℚ)) b ij.2
      = ((p : ℚ) / (q : ℚ)) * b ij.2 := by simp [scaleFam]
  rw [h1, h2]
  exact and_congr (key ij) Iff.rfl

/-- **(b1), all ratios as one inner product:** the `(p, q)` count
is the fenced overlap inner product of `a` against the scaled
family `(p / q) • b` — the composite of `resCount_eq_one_one_scale`
and `resCount_one_one`, so the closed forms of (b3) and any future
seat count cite this one theorem, not a re-derivation. -/
theorem resCount_eq_sum_scaled (p q : ℕ) (hq : q ≠ 0)
    (a : Fin m → ℚ) (b : Fin n → ℚ) :
    resCount p q a b
      = ∑ x ∈ (Finset.univ.image a).erase 0,
        multA a x * multA (scaleFam ((p : ℚ) / (q : ℚ)) b) x := by
  rw [resCount_eq_one_one_scale p q hq a b, resCount_one_one]

-- ============================================================================
-- (c1) The octave-class invariant
-- ============================================================================

/-- Factorization read-back of `octInv`: `x` is its odd part times
the power of two its `padicValRat` records. -/
theorem octInv_mul_zpow_self (x : ℚ) :
    octInv x * (2 : ℚ) ^ (padicValRat 2 x) = x := by
  unfold octInv
  exact div_mul_cancel₀ x (zpow_ne_zero _ (by norm_num))

/-- The 2-adic valuation of a power-of-two multiple: scaling by
`2 ^ k` shifts the valuation by exactly `k`. -/
theorem padicValRat_two_zpow_mul (k : ℤ) {x : ℚ} (hx : x ≠ 0) :
    padicValRat 2 ((2 : ℚ) ^ k * x) = k + padicValRat 2 x := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hself : padicValRat 2 (2 : ℚ) = 1 := by
    have h := padicValRat.self (p := 2) (by norm_num : (1 : ℕ) < 2)
    simpa using h
  rw [padicValRat.mul (zpow_ne_zero k (by norm_num)) hx, padicValRat.zpow,
    hself, mul_one]

/-- **(c1) The class invariant** (memo §2 (c1)): two positive
rational tones are in the same octave class iff their odd parts
agree. This is the working invariant of the whole octave notion. -/
theorem octEq_iff_octInv {x y : ℚ} (hx : 0 < x) (hy : 0 < y) :
    OctEq x y ↔ octInv x = octInv y := by
  constructor
  · rintro ⟨k, rfl⟩
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hval : padicValRat 2 ((2 : ℚ) ^ k * x) = k + padicValRat 2 x :=
      padicValRat_two_zpow_mul k hx0
    have e1 : (2 : ℚ) ^ k ≠ 0 := zpow_ne_zero _ (by norm_num)
    have e2 : (2 : ℚ) ^ padicValRat 2 x ≠ 0 := zpow_ne_zero _ (by norm_num)
    unfold octInv
    rw [hval, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    field_simp
  · intro h
    refine ⟨padicValRat 2 y - padicValRat 2 x, ?_⟩
    symm
    calc (2 : ℚ) ^ (padicValRat 2 y - padicValRat 2 x) * x
        = (2 : ℚ) ^ (padicValRat 2 y - padicValRat 2 x)
            * (octInv x * (2 : ℚ) ^ padicValRat 2 x) := by
          rw [octInv_mul_zpow_self]
      _ = octInv x * ((2 : ℚ) ^ (padicValRat 2 y - padicValRat 2 x)
            * (2 : ℚ) ^ padicValRat 2 x) := by ring
      _ = octInv x * (2 : ℚ) ^ padicValRat 2 y := by
          rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), sub_add_cancel]
      _ = octInv y * (2 : ℚ) ^ padicValRat 2 y := by rw [h]
      _ = y := octInv_mul_zpow_self y

/-- (c1) at `1`: the octave class of `1` is exactly the powers of
two — a positive tone is octave-equivalent to `1` iff its odd part
is `1`. -/
theorem octEq_one_iff {x : ℚ} (hx : 0 < x) :
    OctEq 1 x ↔ octInv x = 1 := by
  have h1 : octInv (1 : ℚ) = 1 := by simp [octInv, padicValRat.one]
  rw [octEq_iff_octInv (by norm_num : (0 : ℚ) < 1) hx, h1]
  exact eq_comm

-- ============================================================================
-- (b3) Geometric-family closed forms
-- ============================================================================

/-- The odd part of a power of two is `1` (the engine of (c3)'s
geometric census and of (b3)'s fifth-deafness). -/
theorem octInv_two_pow (i : ℕ) : octInv ((2 : ℚ) ^ i) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hself : padicValRat 2 (2 : ℚ) = 1 := by
    have h := padicValRat.self (p := 2) (by norm_num : (1 : ℕ) < 2)
    simpa using h
  have hval : padicValRat 2 ((2 : ℚ) ^ i) = (i : ℤ) := by
    rw [padicValRat.pow, hself, mul_one]
  unfold octInv
  rw [hval, zpow_natCast]
  exact div_self (pow_ne_zero i (by norm_num))

/-- The odd part of `3` times a power of two is `3`: a fifth on the
ladder would need exactly this odd part inside a power of two. -/
theorem octInv_three_mul_two_pow (j : ℕ) :
    octInv (3 * (2 : ℚ) ^ j) = 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h3 : padicValRat 2 (3 : ℚ) = 0 := by
    have hpn : padicValNat 2 3 = 0 :=
      padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
    have h := padicValRat_of_nat (p := 2) (n := 3)
    rw [hpn] at h
    simpa using h.symm
  have hself : padicValRat 2 (2 : ℚ) = 1 := by
    have h := padicValRat.self (p := 2) (by norm_num : (1 : ℕ) < 2)
    simpa using h
  have hval : padicValRat 2 (3 * (2 : ℚ) ^ j) = (j : ℤ) := by
    rw [padicValRat.mul (by norm_num) (pow_ne_zero j (by norm_num)), h3,
      padicValRat.pow, hself, mul_one, zero_add]
  unfold octInv
  rw [hval, zpow_natCast, mul_div_assoc,
    div_self (pow_ne_zero j (by norm_num)), mul_one]

/-- **(b3), the octave closed form** (memo §2 (b3)): the ladder
resonates with itself at the octave exactly `k` times — the pairs
`i = j + 1` and no others (exponent comparison is `pow_right_inj₀`,
the counting shadow of (c1)). -/
theorem resCount_two_one_geom (k : ℕ) :
    resCount 2 1 (geomFam k) (geomFam k) = k := by
  have hset : Finset.univ.filter (fun ij : Fin (k + 1) × Fin (k + 1) =>
        ((1 : ℕ) : ℚ) * geomFam k ij.1 = ((2 : ℕ) : ℚ) * geomFam k ij.2
          ∧ geomFam k ij.1 ≠ 0)
      = Finset.univ.image (fun j : Fin k =>
          (⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩,
            ⟨j.val, lt_trans j.isLt (Nat.lt_succ_self k)⟩)) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨heq, -⟩
      simp only [Nat.cast_one, Nat.cast_ofNat, one_mul, geomFam] at heq
      rw [← pow_succ'] at heq
      have hval : i.val = j.val + 1 :=
        (pow_right_inj₀ (by norm_num) (by norm_num)).mp heq
      have hlt : j.val < k := by
        have hi2 := i.isLt
        omega
      exact ⟨⟨j.val, hlt⟩, Prod.ext (Fin.ext hval.symm) (Fin.ext rfl)⟩
    · rintro ⟨j', hjj⟩
      have hi : i = ⟨j'.val + 1, Nat.succ_lt_succ j'.isLt⟩ :=
        (congrArg Prod.fst hjj).symm
      have hj : j = ⟨j'.val, lt_trans j'.isLt (Nat.lt_succ_self k)⟩ :=
        (congrArg Prod.snd hjj).symm
      subst hi
      subst hj
      show ((1 : ℕ) : ℚ) * (2 : ℚ) ^ (j'.val + 1)
          = ((2 : ℕ) : ℚ) * (2 : ℚ) ^ j'.val ∧ (2 : ℚ) ^ (j'.val + 1) ≠ 0
      constructor
      · simp only [Nat.cast_one, Nat.cast_ofNat, one_mul]
        exact pow_succ' (2 : ℚ) j'.val
      · exact pow_ne_zero _ (by norm_num)
  have hinj : Function.Injective (fun j : Fin k =>
      (⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩,
        ⟨j.val, lt_trans j.isLt (Nat.lt_succ_self k)⟩)
      : Fin k → Fin (k + 1) × Fin (k + 1)) := by
    intro a b hab
    simp only [Prod.mk.injEq, Fin.mk.injEq] at hab
    exact Fin.ext hab.2
  unfold resCount
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Fintype.card_fin]

/-- **(b3), the fifth closed form** (memo §2 (b3)): the ladder is
perfectly fifth-deaf. A fifth pair would force
`2 ^ (i + 1) = 3 * 2 ^ j`, whose odd parts are `1` and `3` by
`octInv_two_pow` / `octInv_three_mul_two_pow` — the (c1) invariant
read at the ladder, as the memo registers it. -/
theorem resCount_three_two_geom (k : ℕ) :
    resCount 3 2 (geomFam k) (geomFam k) = 0 := by
  have hempty : Finset.univ.filter (fun ij : Fin (k + 1) × Fin (k + 1) =>
        ((2 : ℕ) : ℚ) * geomFam k ij.1 = ((3 : ℕ) : ℚ) * geomFam k ij.2
          ∧ geomFam k ij.1 ≠ 0) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro ij hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
    obtain ⟨heq, -⟩ := hij
    have heq' : (2 : ℚ) ^ (ij.1.val + 1) = 3 * (2 : ℚ) ^ ij.2.val := by
      have h2 : ((2 : ℕ) : ℚ) * geomFam k ij.1
          = (2 : ℚ) * (2 : ℚ) ^ ij.1.val := by
        simp only [Nat.cast_ofNat, geomFam]
      have h3 : ((3 : ℕ) : ℚ) * geomFam k ij.2
          = 3 * (2 : ℚ) ^ ij.2.val := by
        simp only [Nat.cast_ofNat, geomFam]
      rw [h2, h3] at heq
      rw [← heq]
      exact pow_succ' (2 : ℚ) ij.1.val
    have hcon : octInv ((2 : ℚ) ^ (ij.1.val + 1))
        = octInv (3 * (2 : ℚ) ^ ij.2.val) := by rw [heq']
    rw [octInv_two_pow, octInv_three_mul_two_pow] at hcon
    norm_num at hcon
  unfold resCount
  rw [hempty]
  exact Finset.card_empty

-- ============================================================================
-- (c2) No finite octave closure (kill-grade)
-- ============================================================================

/-- The absolute doubling orbit is strictly monotone: each octave
strictly increases the tone's absolute value. -/
theorem strictMono_two_pow_mul_abs {x : ℚ} (hx : x ≠ 0) :
    StrictMono (fun k : ℕ => (2 : ℚ) ^ k * |x|) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hpos : 0 < (2 : ℚ) ^ k * |x| :=
    mul_pos (pow_pos (by norm_num) _) (abs_pos.mpr hx)
  calc (2 : ℚ) ^ k * |x| < 2 * ((2 : ℚ) ^ k * |x|) := by linarith
    _ = (2 : ℚ) ^ (k + 1) * |x| := by rw [pow_succ']; ring

/-- The doubling orbit of a nonzero tone is injective — its tones
are all distinct, so the orbit is infinite. -/
theorem two_pow_mul_injective {x : ℚ} (hx : x ≠ 0) :
    Function.Injective (fun k : ℕ => (2 : ℚ) ^ k * x) := by
  intro a b hab
  have habs : (2 : ℚ) ^ a * |x| = (2 : ℚ) ^ b * |x| := by
    have h := congrArg (fun y : ℚ => |y|) hab
    simpa [abs_mul, abs_of_pos (pow_pos (show (0 : ℚ) < 2 by norm_num) _)]
      using h
  exact (strictMono_two_pow_mul_abs hx).injective habs

/-- **(c2) No finite octave closure (kill-grade)** (memo §2 (c2)):
if `S : Finset ℚ`, `0 ∉ S`, and `∀ x ∈ S, 2 * x ∈ S`, then
`S = ∅`. A finite nonzero spectrum is NEVER doubling-invariant:
the doubling orbit of any tone is infinite. Any future claim of an
"octave-complete" finite spectrum dies against this theorem on
sight. -/
theorem no_finite_octave_closure {S : Finset ℚ} (h0 : 0 ∉ S)
    (hclose : ∀ x ∈ S, 2 * x ∈ S) : S = ∅ := by
  by_contra hne
  obtain ⟨x, hxS⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hx0 : x ≠ 0 := fun h => h0 (h ▸ hxS)
  have hmem : ∀ k : ℕ, (2 : ℚ) ^ k * x ∈ S := by
    intro k
    induction k with
    | zero => simpa using hxS
    | succ k ih =>
      have e : (2 : ℚ) ^ (k + 1) * x = 2 * ((2 : ℚ) ^ k * x) := by
        rw [pow_succ']; ring
      rw [e]
      exact hclose _ ih
  have hinf : (↑S : Set ℚ).Infinite :=
    Set.infinite_of_injective_forall_mem (two_pow_mul_injective hx0)
      (fun k => Finset.mem_coe.mpr (hmem k))
  exact hinf (Finset.finite_toSet S)

/-- **(c2), the chain-length range bound** (memo §2 (c2)): an
octave chain's top tone lies in `S`, hence at or below the
spectrum's own maximum — so the chain length `k` is bounded by the
spectrum's own range. Finite spectra carry finite chains only. -/
theorem octChain_le_max {S : Finset ℚ} {x : ℚ} {k : ℕ}
    (hchain : OctChain S x k) (hx : x ∈ S) :
    (2 : ℚ) ^ k * x ≤ S.max' ⟨x, hx⟩ :=
  Finset.le_max' _ _ (hchain k le_rfl)

-- ============================================================================
-- (c3) The two extremal class censuses
-- ============================================================================

/-- (c3), geometric pole: every ladder tone has odd part `1`. -/
theorem geomFam_octInv (k : ℕ) (i : Fin (k + 1)) :
    octInv (geomFam k i) = 1 :=
  octInv_two_pow i.val

/-- (c3), geometric pole: the geometric family lies in ONE octave
class — maximal octave concentration. -/
theorem geomFam_octEq (k : ℕ) (i j : Fin (k + 1)) :
    OctEq (geomFam k i) (geomFam k j) := by
  have hi : 0 < geomFam k i := pow_pos (by norm_num) i.val
  have hj : 0 < geomFam k j := pow_pos (by norm_num) j.val
  exact (octEq_iff_octInv hi hj).mpr
    (by rw [geomFam_octInv, geomFam_octInv])

/-- Every positive natural is a power of two times an odd number. -/
theorem exists_two_pow_mul_odd {n : ℕ} (hn : n ≠ 0) :
    ∃ e m : ℕ, Odd m ∧ n = 2 ^ e * m := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd n with hev | hodd
    · obtain ⟨n', hn'⟩ := hev
      have hn'0 : n' ≠ 0 := by
        rintro rfl
        simp at hn'
        exact hn hn'
      have hlt : n' < n := by omega
      obtain ⟨e, m, hm, hdecomp⟩ := ih n' hlt hn'0
      refine ⟨e + 1, m, hm, ?_⟩
      rw [hn', hdecomp, pow_succ']
      ring
    · exact ⟨0, n, hodd, by simp⟩

/-- Odd naturals are their own odd parts: `octInv m = m`. -/
theorem octInv_natCast_of_odd {m : ℕ} (hm : Odd m) :
    octInv ((m : ℚ)) = (m : ℚ) := by
  have hval : padicValRat 2 ((m : ℚ)) = 0 := by
    have h1 : padicValNat 2 m = 0 := by
      rw [padicValNat.eq_zero_iff]
      refine Or.inr (Or.inr ?_)
      intro hdvd
      obtain ⟨t, ht⟩ := hm
      obtain ⟨s, hs⟩ := hdvd
      omega
    have h2 := padicValRat_of_nat (p := 2) (n := m)
    rw [h1] at h2
    simpa using h2.symm
  unfold octInv
  rw [hval]
  simp

/-- (c3), arithmetic pole, representatives: every tone of the
arithmetic family has an odd representative at or below `L` in its
own octave class — its class is met by an odd tone of the family. -/
theorem arith_octInv_rep {L n : ℕ} (hn0 : 1 ≤ n) (hnL : n ≤ L) :
    ∃ m : ℕ, Odd m ∧ 1 ≤ m ∧ m ≤ L ∧ octInv ((n : ℚ)) = (m : ℚ) := by
  obtain ⟨e, m, hm, hdecomp⟩ := exists_two_pow_mul_odd (n := n) (by omega)
  refine ⟨m, hm, ?_, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hm
    omega
  · have hdvd : m ∣ n := ⟨2 ^ e, by rw [hdecomp]; ring⟩
    exact le_trans (Nat.le_of_dvd (by omega) hdvd) hnL
  · have hmpos : (0 : ℚ) < (m : ℚ) := by
      obtain ⟨t, ht⟩ := hm
      exact Nat.cast_pos.mpr (by omega)
    have hnpos : (0 : ℚ) < (n : ℚ) := Nat.cast_pos.mpr (by omega)
    have hOct : OctEq ((m : ℚ)) ((n : ℚ)) := by
      refine ⟨(e : ℤ), ?_⟩
      rw [zpow_natCast, hdecomp]
      norm_cast
    have h := (octEq_iff_octInv hmpos hnpos).mp hOct
    rw [octInv_natCast_of_odd hm] at h
    exact h.symm

/-- (c3), arithmetic pole: the octave classes met by the arithmetic
family `{1, …, L}` are exactly the odd numbers `≤ L`, at their odd
representatives. -/
theorem arith_octInv_image (L : ℕ) :
    (arithSet L).image octInv
      = ((Finset.Icc 1 L).filter Odd).image (fun t : ℕ => (t : ℚ)) := by
  ext z
  simp only [Finset.mem_image, arithSet, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨w, ⟨t, ⟨ht1, ht2⟩, rfl⟩, hz⟩
    obtain ⟨mm, hmmodd, hmm1, hmmL, hrep⟩ := arith_octInv_rep ht1 ht2
    exact ⟨mm, ⟨⟨hmm1, hmmL⟩, hmmodd⟩, by rw [← hrep]; exact hz⟩
  · rintro ⟨t, ⟨⟨ht1, ht2⟩, htodd⟩, rfl⟩
    exact ⟨(t : ℚ), ⟨t, ⟨ht1, ht2⟩, rfl⟩, octInv_natCast_of_odd htodd⟩

/-- The odd numbers in `[1, L]` number exactly `(L + 1) / 2`
(the memo's "(L+1)/2 rounded up", in integer division). -/
theorem odd_Icc_card (L : ℕ) :
    ((Finset.Icc 1 L).filter Odd).card = (L + 1) / 2 := by
  have hset : (Finset.Icc 1 L).filter Odd
      = (Finset.range ((L + 1) / 2)).image (fun t => 2 * t + 1) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image,
      Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨t, ht⟩⟩
      exact ⟨t, by omega, ht.symm⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨t, rfl⟩⟩
  rw [hset, Finset.card_image_of_injective _
    (fun a b h => by
      have h' : 2 * a + 1 = 2 * b + 1 := h
      omega),
    Finset.card_range]

/-- **(c3), arithmetic pole, the census count** (memo §2 (c3)):
the arithmetic family `{1, …, L}` meets exactly `(L + 1) / 2`
octave classes — maximal octave dispersion per tone, against the
geometric family's one class. -/
theorem arith_octInv_image_card (L : ℕ) :
    ((arithSet L).image octInv).card = (L + 1) / 2 := by
  rw [arith_octInv_image,
    Finset.card_image_of_injective _ Nat.cast_injective, odd_Icc_card]

end ThetLogos

#print axioms ThetLogos.resCountAll_one_one
#print axioms ThetLogos.resCountAll_eq_add
#print axioms ThetLogos.resCountAll_zero_left
#print axioms ThetLogos.resCount_one_one
#print axioms ThetLogos.resCount_eq_one_one_scale
#print axioms ThetLogos.resCount_eq_sum_scaled
#print axioms ThetLogos.octEq_iff_octInv
#print axioms ThetLogos.octEq_one_iff
#print axioms ThetLogos.resCount_two_one_geom
#print axioms ThetLogos.resCount_three_two_geom
#print axioms ThetLogos.no_finite_octave_closure
#print axioms ThetLogos.octChain_le_max
#print axioms ThetLogos.geomFam_octEq
#print axioms ThetLogos.arith_octInv_image
#print axioms ThetLogos.arith_octInv_image_card
