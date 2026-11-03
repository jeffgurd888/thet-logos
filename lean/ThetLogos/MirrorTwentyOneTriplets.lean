/-
# TRIPLETS OF CORRELATIONS — the 3-term resonances of `ZMod 21`

Brick: TRIPLETS OF CORRELATIONS (working label; naming is Jeff's hand).
Commission: Jeff, 2026-11-02 21:52 EST — "we need to make the doublets
into triplets of correlations"; build commissioned 2026-11-02 22:03
("build and run"), re-fired 2026-11-03 13:37 ("build and run"). Built
from the frozen scope `mirror21-triplets-scoping-2026-11-02.md`
(pins TR-1..TR-4) on top of `ThetLogos.MirrorTwentyOne`.

**What this module proves — and all it proves.** Mirror-21's doublets are
the 2-term resonances of `ZMod 21`: `k + (-k) = 0`. This module builds the
3-term resonances — triples `(a, b, c)` with `a + b + c = 0` — and proves:
TR-1 the doublet is exactly the zero-slice of the triplet system
(`(a, b, 0)` resonant iff `b = -a`, and the third coordinate is always
forced: `c = -(a + b)`); TR-2 the resonant triples number `441 = 21^2`,
by the parametrization bijection, an argument, not an enumeration; TR-3
the mirror (negation) organizes the 441 as **220 mirror-pairs + the lone
fixed triple `(0, 0, 0)`**; TR-4 (the stretch) the gcd-family strata at
T1: of the 380 all-nonzero resonant triples, **92 stay within one family
and 288 mix families** — triples cross the walls that sealed the pairs.
The strata counts are proved by the Chinese remainder decomposition
`ZMod 21 ≃+* ZMod 3 × ZMod 7` plus the component counting laws
`card = n^2` and `allNonzero = (n-1)(n-2)`.

Finite combinatorics on `ZMod 21` only. No dynamics, no operator,
no spectrum is asserted. The T2 enumeration checker is
`python/mirror21_triplets.py` (a checker, not a proof).

**NO CLAIM** — parts of any official Millennium statement closed by
this module: 0 (this answers nothing about P vs NP or any other
Millennium problem; that suspicion from 2026-11-02 is fenced out here).
Dials: 0/4.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Tauto
import ThetLogos.MirrorTwentyOne

namespace ThetLogos

/-- A triple of residues is *resonant* when its entries cancel jointly:
`a + b + c = 0`. The 3-term generalization of the Mirror-21 doublet. -/
def Resonant {n : ℕ} (t : ZMod n × ZMod n × ZMod n) : Prop :=
  t.1 + t.2.1 + t.2.2 = 0

instance decidableResonant {n : ℕ} (t : ZMod n × ZMod n × ZMod n) :
    Decidable (Resonant t) :=
  inferInstanceAs (Decidable (t.1 + t.2.1 + t.2.2 = 0))

/-- The resonant triples over `ZMod n`, as a type. -/
abbrev ResTriples (n : ℕ) := {t : ZMod n × ZMod n × ZMod n // Resonant t}

/-- The third coordinate of a resonant triple is forced by the first two:
the correlation is a function, not a relation. This one law is the engine
of the whole brick — the count (TR-2) is its corollary. -/
theorem resonant_iff_third {n : ℕ} (a b c : ZMod n) :
    Resonant (a, b, c) ↔ c = -(a + b) := by
  show a + b + c = 0 ↔ c = -(a + b)
  constructor
  · intro h
    apply eq_neg_of_add_eq_zero_left
    rwa [add_comm c (a + b)]
  · intro h
    rw [h, add_neg_cancel]

/-- **TR-1 (the bridge).** A triple with center in the third slot is
resonant iff the other two entries form a Mirror-21 doublet. The old
structure is a slice of the new one, by proof. -/
theorem resonant_center_iff {n : ℕ} (a b : ZMod n) :
    Resonant (a, b, 0) ↔ b = -a := by
  show a + b + 0 = 0 ↔ b = -a
  rw [add_zero, add_comm]
  exact add_eq_zero_iff_eq_neg

/-- **TR-1, extension.** Every doublet extends to a center-triplet. -/
theorem resonant_center_ext {n : ℕ} (a : ZMod n) :
    Resonant (a, -a, 0) :=
  (resonant_center_iff a (-a)).2 rfl

/-- The parametrization: a resonant triple is exactly its first two
coordinates, the third being forced. -/
def resonantEquivPairs (n : ℕ) : ResTriples n ≃ ZMod n × ZMod n where
  toFun t := (t.1.1, t.1.2.1)
  invFun p := ⟨(p.1, p.2, -(p.1 + p.2)), (resonant_iff_third p.1 p.2 _).2 rfl⟩
  left_inv t := by
    obtain ⟨⟨a, b, c⟩, ht⟩ := t
    have hc : c = -(a + b) := (resonant_iff_third a b c).1 ht
    simp only [hc]
  right_inv p := by
    obtain ⟨a, b⟩ := p
    rfl

/-- **TR-2 (the count), general form.** The resonant triples over
`ZMod n` number exactly `n^2` — by the parametrization bijection
(`resonantEquivPairs`), an argument, not an enumeration. -/
theorem card_resonant (n : ℕ) [NeZero n] :
    Fintype.card (ResTriples n) = n ^ 2 := by
  rw [Fintype.card_congr (resonantEquivPairs n), Fintype.card_prod, ZMod.card n,
    pow_two]

/-- **TR-2 at the seat.** The resonant triples of `ZMod 21` number 441. -/
theorem card_resonant_21 :
    Fintype.card (ResTriples 21) = 441 :=
  card_resonant 21

/-! ## TR-3: the mirror closure -/

/-- In `ZMod 21`, self-mirror means zero: `-x = x` forces `x = 0`,
because `2` is invertible mod 21 (`11 * 2 = 22 = 1`). The odd-modulus
fact behind both Mirror-21's unique center and this brick's lone
fixed triple. -/
theorem neg_eq_self_imp_eq_zero (x : ZMod 21) (h : -x = x) : x = 0 := by
  have hx : x + x = 0 := by
    have h0 := neg_add_cancel x
    rwa [h] at h0
  have h2 : (2 : ZMod 21) * x = 0 := by rwa [two_mul]
  have h22 : (11 : ZMod 21) * 2 = 1 := by decide
  calc x = (11 * 2) * x := by rw [h22, one_mul]
    _ = 11 * (2 * x) := by rw [mul_assoc]
    _ = 0 := by rw [h2, mul_zero]

/-- The mirror (negation) on triples, coordinatewise. -/
def negTriple {n : ℕ} (t : ZMod n × ZMod n × ZMod n) :
    ZMod n × ZMod n × ZMod n :=
  (-t.1, -t.2.1, -t.2.2)

/-- Resonance is mirror-closed: the mirror of a resonant triple is
resonant. -/
theorem resonant_neg {n : ℕ} {t : ZMod n × ZMod n × ZMod n}
    (h : Resonant t) : Resonant (negTriple t) := by
  obtain ⟨a, b, c⟩ := t
  show -a + -b + -c = 0
  rw [← neg_add, ← neg_add, show a + b + c = 0 from h, neg_zero]

/-- The mirror as a self-map of the resonant triples of `ZMod 21`. -/
def mirrorTriple : ResTriples 21 → ResTriples 21 :=
  fun t => ⟨negTriple t.1, resonant_neg t.2⟩

/-- The mirror is an involution on resonant triples. -/
theorem mirrorTriple_involutive : Function.Involutive mirrorTriple := by
  intro t
  obtain ⟨⟨a, b, c⟩, ht⟩ := t
  simp [mirrorTriple, negTriple]

/-- The center triple `(0, 0, 0)`: the mirror's candidate fixed point. -/
def centerTriple : ResTriples 21 := ⟨(0, 0, 0), by simp [Resonant]⟩

theorem mirrorTriple_center : mirrorTriple centerTriple = centerTriple := by
  simp [mirrorTriple, negTriple, centerTriple]

/-- **TR-3, fixed point.** The center triple is the mirror's ONLY fixed
triple among the resonant triples — the lone unpaired correlation. -/
theorem mirrorTriple_fixed (t : ResTriples 21) (h : mirrorTriple t = t) :
    t = centerTriple := by
  obtain ⟨⟨a, b, c⟩, ht⟩ := t
  have h1 : (-a, -b, -c) = (a, b, c) := congrArg Subtype.val h
  have ha : a = 0 := neg_eq_self_imp_eq_zero a (congrArg Prod.fst h1)
  have hb : b = 0 := neg_eq_self_imp_eq_zero b (congrArg (fun p => p.2.1) h1)
  have hc : c = 0 := neg_eq_self_imp_eq_zero c (congrArg (fun p => p.2.2) h1)
  apply Subtype.ext
  show (a, b, c) = (0, 0, 0)
  exact Prod.ext ha (Prod.ext hb hc)

/-- Exactly one resonant triple is mirror-fixed. -/
theorem card_mirror_fixed :
    Fintype.card {t : ResTriples 21 // mirrorTriple t = t} = 1 := by
  apply Fintype.card_eq_one_iff.2
  refine ⟨⟨centerTriple, mirrorTriple_center⟩, ?_⟩
  rintro ⟨t, ht⟩
  exact Subtype.ext (mirrorTriple_fixed t ht)

/-- The mirror-pairs: images of the non-fixed resonant triples under
`t ↦ {t, mirror t}`. -/
def mirrorPairs : Finset (Finset (ResTriples 21)) :=
  (Finset.univ.filter fun t => mirrorTriple t ≠ t).image
    (fun t => {t, mirrorTriple t})

/-- Each mirror-pair's fiber in the non-fixed triples is exactly the
pair itself. -/
theorem mirror_pair_fiber (t : ResTriples 21) (ht : mirrorTriple t ≠ t) :
    ((Finset.univ.filter fun s => mirrorTriple s ≠ s).filter
      fun s => ({s, mirrorTriple s} : Finset (ResTriples 21)) = {t, mirrorTriple t})
    = {t, mirrorTriple t} := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hs, hps⟩
    have hmem : s ∈ ({t, mirrorTriple t} : Finset (ResTriples 21)) :=
      hps ▸ Finset.mem_insert_self s _
    simpa using hmem
  · rintro (rfl | rfl)
    · exact ⟨ht, rfl⟩
    · refine ⟨?_, ?_⟩
      · rw [mirrorTriple_involutive t]
        exact Ne.symm ht
      · rw [mirrorTriple_involutive t]
        exact Finset.pair_comm _ _

/-- **TR-3 (mirror closure).** The 441 resonant triples organize as
**220 mirror-pairs + the lone center triple** — tonight's doublet
pattern one level up: pairs and a center, again. -/
theorem card_mirror_pairs : mirrorPairs.card = 220 := by
  show ((Finset.univ.filter fun t : ResTriples 21 => mirrorTriple t ≠ t).image
    (fun t => ({t, mirrorTriple t} : Finset (ResTriples 21)))).card = 220
  have htotal : (Finset.univ : Finset (ResTriples 21)).card = 441 := by
    rw [Finset.card_univ]
    exact card_resonant_21
  have hfixed : (Finset.univ.filter fun t : ResTriples 21 =>
      mirrorTriple t = t).card = 1 := by
    rw [← Fintype.card_subtype]
    exact card_mirror_fixed
  have hnf : (Finset.univ.filter fun t : ResTriples 21 =>
      mirrorTriple t ≠ t).card = 440 := by
    have hadd := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (ResTriples 21)))
      (p := fun t : ResTriples 21 => mirrorTriple t = t)
    rw [hfixed, htotal] at hadd
    -- hadd : 1 + (univ.filter (fun t => ¬ mirrorTriple t = t)).card = 441;
    -- the goal's filter uses `≠`, which is `¬ =` definitionally.
    have hnf' : (Finset.univ.filter fun t : ResTriples 21 =>
        ¬ mirrorTriple t = t).card = 440 := by omega
    exact hnf'
  have key0 := Finset.card_eq_sum_card_image
    (fun t : ResTriples 21 => ({t, mirrorTriple t} : Finset (ResTriples 21)))
    (Finset.univ.filter fun t => mirrorTriple t ≠ t)
  rw [hnf] at key0
  -- key0 : 440 = ∑ b ∈ (nonfixed).image pairFn, (fiber over b).card
  have hfib : ∀ y ∈ (Finset.univ.filter fun t : ResTriples 21 =>
        mirrorTriple t ≠ t).image
        (fun t => ({t, mirrorTriple t} : Finset (ResTriples 21))),
      ((Finset.univ.filter fun s => mirrorTriple s ≠ s).filter
        fun s => ({s, mirrorTriple s} : Finset (ResTriples 21)) = y).card = 2 := by
    intro y hy
    obtain ⟨t, htmem, rfl⟩ := Finset.mem_image.1 hy
    have ht : mirrorTriple t ≠ t := (Finset.mem_filter.1 htmem).2
    rw [mirror_pair_fiber t ht]
    exact Finset.card_pair (Ne.symm ht)
  have hsum := Finset.sum_const_nat hfib
  rw [hsum] at key0
  -- key0 : 440 = ((nonfixed).image pairFn).card * 2, in the goal's own terms.
  apply Nat.eq_of_mul_eq_mul_right (show (0 : ℕ) < 2 by decide)
  exact key0.symm.trans (by decide)

/-- **TR-3, the organization in one line:**
total = 2 · (mirror-pairs) + (fixed triples). -/
theorem mirror_organization_21 :
    Fintype.card (ResTriples 21) = 2 * mirrorPairs.card +
      Fintype.card {t : ResTriples 21 // mirrorTriple t = t} := by
  rw [card_resonant_21, card_mirror_pairs, card_mirror_fixed]

/-! ## TR-4: the family strata (kill-armed stretch)

The gcd families of `ZMod 21` are the vanishing patterns under the two
reductions mod 3 and mod 7: an element is a unit (vanishes at neither),
a multiple of 3 only, a multiple of 7 only, or zero. The doublets were
sealed inside these families; the triples are not. The counting engine
is two component laws, proved for every `n`: the all-zero resonant
triple is unique, and the all-nonzero resonant triples number
`(n-1)(n-2)`. -/

/-- All three entries vanish. -/
def TripleAllZero {n : ℕ} (t : ZMod n × ZMod n × ZMod n) : Prop :=
  t.1 = 0 ∧ t.2.1 = 0 ∧ t.2.2 = 0

/-- No entry vanishes. -/
def TripleAllNonzero {n : ℕ} (t : ZMod n × ZMod n × ZMod n) : Prop :=
  ¬ t.1 = 0 ∧ ¬ t.2.1 = 0 ∧ ¬ t.2.2 = 0

instance decidableTripleAllZero {n : ℕ} (t : ZMod n × ZMod n × ZMod n) :
    Decidable (TripleAllZero t) :=
  inferInstanceAs (Decidable (t.1 = 0 ∧ t.2.1 = 0 ∧ t.2.2 = 0))

instance decidableTripleAllNonzero {n : ℕ} (t : ZMod n × ZMod n × ZMod n) :
    Decidable (TripleAllNonzero t) :=
  inferInstanceAs (Decidable (¬ t.1 = 0 ∧ ¬ t.2.1 = 0 ∧ ¬ t.2.2 = 0))

instance decidableAllZeroRes (n : ℕ) :
    DecidablePred (fun t : ResTriples n => TripleAllZero t.1) :=
  fun _t => inferInstance

instance decidableAllNonzeroRes (n : ℕ) :
    DecidablePred (fun t : ResTriples n => TripleAllNonzero t.1) :=
  fun _t => inferInstance

/-- All-zero and all-nonzero are exclusive. -/
theorem allZero_not_allNonzero {n : ℕ} {t : ZMod n × ZMod n × ZMod n}
    (hz : TripleAllZero t) (hn : TripleAllNonzero t) : False :=
  hn.1 hz.1

/-- **Component law 1.** The all-zero resonant triple is unique. -/
theorem card_allZero (n : ℕ) [NeZero n] :
    Fintype.card {t : ResTriples n // TripleAllZero t.1} = 1 := by
  apply Fintype.card_eq_one_iff.2
  refine ⟨⟨⟨(0, 0, 0), by simp [Resonant]⟩, ⟨rfl, rfl, rfl⟩⟩, ?_⟩
  rintro ⟨⟨⟨a, b, c⟩, ht⟩, hz⟩
  obtain ⟨ha, hb, hc⟩ := hz
  apply Subtype.ext
  apply Subtype.ext
  show (a, b, c) = (0, 0, 0)
  exact Prod.ext ha (Prod.ext hb hc)

/-- The nonzero residues of `ZMod n` number `n - 1`. -/
theorem card_ne_zero (n : ℕ) [NeZero n] :
    Fintype.card {a : ZMod n // a ≠ 0} = n - 1 := by
  rw [Fintype.card_subtype]
  have h0 : (Finset.univ.filter fun a : ZMod n => a = 0) = {0} := by
    ext a
    simp
  have hadd := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (ZMod n))) (p := fun a : ZMod n => a = 0)
  rw [h0, Finset.card_singleton, Finset.card_univ, ZMod.card n] at hadd
  have hcongr : (Finset.univ.filter fun a : ZMod n => a ≠ 0)
      = (Finset.univ.filter fun a : ZMod n => ¬ a = 0) :=
    Finset.filter_congr (fun x _ => Iff.rfl)
  rw [hcongr]
  -- goal : (filter (¬ · = 0)).card = n - 1, with hadd : 1 + that = n
  omega

/-- Pairs with both entries nonzero split as a product of nonzero
residues. -/
def pairsAllNonzeroEquiv (n : ℕ) :
    {p : ZMod n × ZMod n // ¬ p.1 = 0 ∧ ¬ p.2 = 0} ≃
    {a : ZMod n // a ≠ 0} × {b : ZMod n // b ≠ 0} where
  toFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
  invFun q := ⟨(q.1.1, q.2.1), q.1.2, q.2.2⟩
  left_inv p := by
    obtain ⟨⟨a, b⟩, hp⟩ := p
    rfl
  right_inv q := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := q
    rfl

/-- **Component law 2.** The all-nonzero resonant triples over `ZMod n`
number `(n-1)(n-2)`: the first two entries are free nonzero residues
whose sum must not vanish — `(n-1)^2 - (n-1)` pairs — and the third
entry is forced. -/
theorem card_allNonzero (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    Fintype.card {t : ResTriples n // TripleAllNonzero t.1} = (n - 1) * (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  -- Step 1: the all-nonzero resonant triples are the good pairs.
  have step1 : Fintype.card {t : ResTriples (m + 2) // TripleAllNonzero t.1}
      = Fintype.card {p : ZMod (m + 2) × ZMod (m + 2) //
          (¬ p.1 = 0 ∧ ¬ p.2 = 0) ∧ ¬ (p.1 + p.2 = 0)} := by
    apply Fintype.card_congr
    exact {
      toFun := fun t => ⟨(t.1.1.1, t.1.1.2.1),
        ⟨t.2.1, t.2.2.1⟩, fun hsum => t.2.2.2 (by
          have hc : t.1.1.2.2 = -(t.1.1.1 + t.1.1.2.1) :=
            (resonant_iff_third _ _ _).1 t.1.2
          rw [hsum, neg_zero] at hc
          exact hc)⟩
      invFun := fun p => ⟨⟨(p.1.1, p.1.2, -(p.1.1 + p.1.2)),
          (resonant_iff_third _ _ _).2 rfl⟩,
        p.2.1.1, p.2.1.2, fun hc => p.2.2 (by
          have h2 : -(p.1.1 + p.1.2) = 0 := hc
          rwa [neg_eq_zero] at h2)⟩
      left_inv := fun t => by
        obtain ⟨⟨⟨a, b, c⟩, ht⟩, hn1, hn2, hn3⟩ := t
        have hc : c = -(a + b) := (resonant_iff_third a b c).1 ht
        simp only [hc]
      right_inv := fun p => by
        obtain ⟨⟨a, b⟩, hp⟩ := p
        rfl }
  -- Step 2: split good pairs off the all-nonzero pairs.
  have step2 : Fintype.card {p : ZMod (m + 2) × ZMod (m + 2) //
        (¬ p.1 = 0 ∧ ¬ p.2 = 0) ∧ ¬ (p.1 + p.2 = 0)}
      = Fintype.card {p : ZMod (m + 2) × ZMod (m + 2) // ¬ p.1 = 0 ∧ ¬ p.2 = 0}
        - Fintype.card {p : {q : ZMod (m + 2) × ZMod (m + 2) //
            ¬ q.1 = 0 ∧ ¬ q.2 = 0} // p.1.1 + p.1.2 = 0} := by
    have h := (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun p : ZMod (m + 2) × ZMod (m + 2) => ¬ p.1 = 0 ∧ ¬ p.2 = 0)
      (fun p : ZMod (m + 2) × ZMod (m + 2) => ¬ (p.1 + p.2 = 0)))
    rw [← Fintype.card_congr h]
    exact Fintype.card_subtype_compl _
  -- Step 3: the bad pairs (sum zero) are just the nonzero residues.
  have step3 : Fintype.card {p : {q : ZMod (m + 2) × ZMod (m + 2) //
        ¬ q.1 = 0 ∧ ¬ q.2 = 0} // p.1.1 + p.1.2 = 0}
      = Fintype.card {a : ZMod (m + 2) // a ≠ 0} := by
    apply Fintype.card_congr
    exact {
      toFun := fun p => ⟨p.1.1.1, p.1.2.1⟩
      invFun := fun a => ⟨⟨(a.1, -a.1), a.2, fun h => a.2 (by
          have : (-a.1 : ZMod (m + 2)) = 0 := h
          rwa [neg_eq_zero] at this)⟩, by simp⟩
      left_inv := fun p => by
        obtain ⟨⟨⟨a, b⟩, ha, hb⟩, hsum⟩ := p
        have hb' : b = -a := by
          rw [← add_eq_zero_iff_eq_neg, add_comm b a]
          exact hsum
        simp only [hb']
      right_inv := fun a => by
        obtain ⟨a, ha⟩ := a
        rfl }
  -- Step 4: arithmetic.
  rw [step1, step2, step3, Fintype.card_congr (pairsAllNonzeroEquiv (m + 2)),
    Fintype.card_prod, card_ne_zero (m + 2)]
  have key : (m + 2 - 1) * (m + 2 - 1) = (m + 2 - 1) * (m + 2 - 2) + (m + 2 - 1) := by
    show (m + 1) * (m + 1) = (m + 1) * m + (m + 1)
    rw [mul_add, mul_one]
  rw [key, add_tsub_cancel_right]

/-! ### The CRT decomposition: the brick's organizing law

`ZMod 21` is the product of its two reductions: the Chinese remainder
isomorphism `crt21`. Applied coordinatewise it identifies the resonant
triples of `ZMod 21` with pairs of resonant triples over `ZMod 3` and
`ZMod 7` — one law, from which the strata counts below fall out. -/

/-- The Chinese remainder isomorphism `ZMod 21 ≃+* ZMod 3 × ZMod 7`. -/
def crt21 : ZMod 21 ≃+* ZMod 3 × ZMod 7 :=
  ZMod.chineseRemainder (m := 3) (n := 7) (by decide)

/-- Coordinatewise CRT on triples, regrouped by component. -/
def tripleCrtEquiv :
    (ZMod 21 × ZMod 21 × ZMod 21) ≃
    (ZMod 3 × ZMod 3 × ZMod 3) × (ZMod 7 × ZMod 7 × ZMod 7) where
  toFun t := (((crt21 t.1).1, (crt21 t.2.1).1, (crt21 t.2.2).1),
    ((crt21 t.1).2, (crt21 t.2.1).2, (crt21 t.2.2).2))
  invFun u := (crt21.symm (u.1.1, u.2.1), crt21.symm (u.1.2.1, u.2.2.1),
    crt21.symm (u.1.2.2, u.2.2.2))
  left_inv t := by
    obtain ⟨a, b, c⟩ := t
    simp only [Prod.eta, RingEquiv.symm_apply_apply]
  right_inv u := by
    obtain ⟨⟨a3, b3, c3⟩, ⟨a7, b7, c7⟩⟩ := u
    simp only [RingEquiv.apply_symm_apply]

/-- Resonance is a componentwise property under CRT: a triple over
`ZMod 21` is resonant iff both of its shadows are. -/
theorem resonant_tripleCrtEquiv (t : ZMod 21 × ZMod 21 × ZMod 21) :
    Resonant t ↔ Resonant (tripleCrtEquiv t).1 ∧
      Resonant (tripleCrtEquiv t).2 := by
  obtain ⟨a, b, c⟩ := t
  show a + b + c = 0 ↔
    ((crt21 a).1 + (crt21 b).1 + (crt21 c).1 = 0) ∧
      ((crt21 a).2 + (crt21 b).2 + (crt21 c).2 = 0)
  have h : crt21 (a + b + c) = crt21 a + crt21 b + crt21 c := by
    simp [map_add]
  constructor
  · intro hsum
    have h0 : crt21 (a + b + c) = 0 := by rw [hsum, map_zero]
    rw [h] at h0
    exact ⟨congrArg Prod.fst h0, congrArg Prod.snd h0⟩
  · rintro ⟨h1, h2⟩
    have h0 : crt21 (a + b + c) = 0 := by
      rw [h]
      exact Prod.ext h1 h2
    have hinj : crt21 (a + b + c) = crt21 0 := by rw [h0, map_zero]
    exact crt21.injective hinj

/-- **The organizing law.** The resonant triples of `ZMod 21` are
exactly the pairs of resonant triples over `ZMod 3` and `ZMod 7`,
under the Chinese remainder isomorphism. (Built by hand, not via
`Equiv.subtypeEquiv`, so that its components reduce cheaply.) -/
def resTriplesCrtEquiv : ResTriples 21 ≃ ResTriples 3 × ResTriples 7 where
  toFun t := (⟨(tripleCrtEquiv t.1).1, ((resonant_tripleCrtEquiv t.1).1 t.2).1⟩,
    ⟨(tripleCrtEquiv t.1).2, ((resonant_tripleCrtEquiv t.1).1 t.2).2⟩)
  invFun u := ⟨tripleCrtEquiv.symm (u.1.1, u.2.1), by
    have h := resonant_tripleCrtEquiv (tripleCrtEquiv.symm (u.1.1, u.2.1))
    rw [Equiv.apply_symm_apply] at h
    exact h.2 ⟨u.1.2, u.2.2⟩⟩
  left_inv t := by
    apply Subtype.ext
    show tripleCrtEquiv.symm (tripleCrtEquiv t.1) = t.1
    exact Equiv.symm_apply_apply tripleCrtEquiv t.1
  right_inv u := by
    obtain ⟨⟨u1, h1⟩, ⟨u2, h2⟩⟩ := u
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact congrArg Prod.fst (Equiv.apply_symm_apply tripleCrtEquiv (u1, u2))
    · exact congrArg Prod.snd (Equiv.apply_symm_apply tripleCrtEquiv (u1, u2))

/-! ### Vanishing patterns and the strata count -/

/-- Two residues have the same *vanishing pattern* when they vanish at
the same CRT components — the gcd-family relation of the scoping:
unit / multiple of 3 only / multiple of 7 only / zero. -/
def SameVanishing (x y : ZMod 21) : Prop :=
  ((crt21 x).1 = 0 ↔ (crt21 y).1 = 0) ∧
    ((crt21 x).2 = 0 ↔ (crt21 y).2 = 0)

instance decidableSameVanishing (x y : ZMod 21) :
    Decidable (SameVanishing x y) :=
  inferInstanceAs (Decidable (((crt21 x).1 = 0 ↔ (crt21 y).1 = 0) ∧
    ((crt21 x).2 = 0 ↔ (crt21 y).2 = 0)))

/-- A triple has *uniform pattern* when all three entries lie in one
gcd family. -/
def UniformPattern (t : ZMod 21 × ZMod 21 × ZMod 21) : Prop :=
  SameVanishing t.1 t.2.1 ∧ SameVanishing t.1 t.2.2

instance decidableUniformPattern (t : ZMod 21 × ZMod 21 × ZMod 21) :
    Decidable (UniformPattern t) :=
  inferInstanceAs (Decidable (SameVanishing t.1 t.2.1 ∧
    SameVanishing t.1 t.2.2))

instance decidableUniformPatternRes :
    DecidablePred (fun t : ResTriples 21 => UniformPattern t.1) :=
  fun _t => inferInstance

instance decidableWithinRes :
    DecidablePred (fun t : ResTriples 21 =>
      TripleAllNonzero t.1 ∧ UniformPattern t.1) :=
  fun _t => inferInstance

instance decidableMixingRes :
    DecidablePred (fun t : ResTriples 21 =>
      TripleAllNonzero t.1 ∧ ¬ UniformPattern t.1) :=
  fun _t => inferInstance

instance decidableUniformPatternAN :
    DecidablePred (fun s : {t : ResTriples 21 // TripleAllNonzero t.1} =>
      UniformPattern s.1.1) :=
  fun _s => inferInstance

/-- The component values of the organizing equiv, as rewrite rules
(so later proofs never reduce through the equiv itself). -/
theorem resTriplesCrtEquiv_fst_val (t : ResTriples 21) :
    (resTriplesCrtEquiv t).1.1 = (tripleCrtEquiv t.1).1 := rfl

theorem resTriplesCrtEquiv_snd_val (t : ResTriples 21) :
    (resTriplesCrtEquiv t).2.1 = (tripleCrtEquiv t.1).2 := rfl

/-- The family condition on the product side: each component triple is
all-zero or all-nonzero (uniform within its component), and not both
components are all-zero. -/
def ProdFamily (u : ZMod 3 × ZMod 3 × ZMod 3) (v : ZMod 7 × ZMod 7 × ZMod 7) :
    Prop :=
  (TripleAllZero u ∨ TripleAllNonzero u) ∧
    (TripleAllZero v ∨ TripleAllNonzero v) ∧
    ¬ (TripleAllZero u ∧ TripleAllZero v)

instance decidableProdFamily (u : ZMod 3 × ZMod 3 × ZMod 3)
    (v : ZMod 7 × ZMod 7 × ZMod 7) : Decidable (ProdFamily u v) :=
  inferInstanceAs (Decidable
    ((TripleAllZero u ∨ TripleAllNonzero u) ∧
      (TripleAllZero v ∨ TripleAllNonzero v) ∧
      ¬ (TripleAllZero u ∧ TripleAllZero v)))

instance decidableProdFamilyPred :
    DecidablePred (fun w : ResTriples 3 × ResTriples 7 =>
      ProdFamily w.1.1 w.2.1) :=
  fun _w => inferInstance

/-- Three residues share a zero-status iff they are all zero or all
nonzero. -/
theorem zero_status_uniform {k : ℕ} (x y z : ZMod k) :
    ((x = 0 ↔ y = 0) ∧ (x = 0 ↔ z = 0)) ↔
    (x = 0 ∧ y = 0 ∧ z = 0) ∨
      (¬ (x = 0) ∧ ¬ (y = 0) ∧ ¬ (z = 0)) := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> by_cases hz : z = 0 <;>
    simp [hx, hy, hz]

/-- Uniform pattern is a componentwise condition under CRT
(entrywise form). -/
theorem uniformPattern_transport_entries (a b c : ZMod 21) :
    UniformPattern (a, b, c) ↔
    (TripleAllZero (tripleCrtEquiv (a, b, c)).1 ∨
      TripleAllNonzero (tripleCrtEquiv (a, b, c)).1) ∧
    (TripleAllZero (tripleCrtEquiv (a, b, c)).2 ∨
      TripleAllNonzero (tripleCrtEquiv (a, b, c)).2) := by
  show (((crt21 a).1 = 0 ↔ (crt21 b).1 = 0) ∧
        ((crt21 a).2 = 0 ↔ (crt21 b).2 = 0)) ∧
      (((crt21 a).1 = 0 ↔ (crt21 c).1 = 0) ∧
        ((crt21 a).2 = 0 ↔ (crt21 c).2 = 0)) ↔
    (((crt21 a).1 = 0 ∧ (crt21 b).1 = 0 ∧ (crt21 c).1 = 0) ∨
      (¬ (crt21 a).1 = 0 ∧ ¬ (crt21 b).1 = 0 ∧ ¬ (crt21 c).1 = 0)) ∧
    (((crt21 a).2 = 0 ∧ (crt21 b).2 = 0 ∧ (crt21 c).2 = 0) ∨
      (¬ (crt21 a).2 = 0 ∧ ¬ (crt21 b).2 = 0 ∧ ¬ (crt21 c).2 = 0))
  constructor
  · rintro ⟨⟨h3ab, h7ab⟩, ⟨h3ac, h7ac⟩⟩
    exact ⟨(zero_status_uniform _ _ _).1 ⟨h3ab, h3ac⟩,
      (zero_status_uniform _ _ _).1 ⟨h7ab, h7ac⟩⟩
  · rintro ⟨h3, h7⟩
    have h3' := (zero_status_uniform (crt21 a).1 (crt21 b).1 (crt21 c).1).2 h3
    have h7' := (zero_status_uniform (crt21 a).2 (crt21 b).2 (crt21 c).2).2 h7
    exact ⟨⟨h3'.1, h7'.1⟩, ⟨h3'.2, h7'.2⟩⟩

/-- Uniform pattern is a componentwise condition under CRT. -/
theorem uniformPattern_transport (t : ResTriples 21) :
    UniformPattern t.1 ↔
    (TripleAllZero (resTriplesCrtEquiv t).1.1 ∨
      TripleAllNonzero (resTriplesCrtEquiv t).1.1) ∧
    (TripleAllZero (resTriplesCrtEquiv t).2.1 ∨
      TripleAllNonzero (resTriplesCrtEquiv t).2.1) := by
  rw [resTriplesCrtEquiv_fst_val, resTriplesCrtEquiv_snd_val]
  obtain ⟨⟨a, b, c⟩, ht⟩ := t
  exact uniformPattern_transport_entries a b c

/-- A residue vanishes iff both its CRT components vanish. -/
theorem eq_zero_iff_crt (x : ZMod 21) :
    x = 0 ↔ (crt21 x).1 = 0 ∧ (crt21 x).2 = 0 := by
  constructor
  · intro hx
    rw [hx]
    simp [map_zero]
  · rintro ⟨h1, h2⟩
    have hinj : crt21 x = crt21 0 := by
      rw [map_zero]
      exact Prod.ext h1 h2
    exact crt21.injective hinj

theorem ne_zero_of_comp_ne {x : ZMod 21}
    (h : ¬ ((crt21 x).1 = 0 ∧ (crt21 x).2 = 0)) : ¬ x = 0 :=
  fun hx => h ((eq_zero_iff_crt x).1 hx)

/-- **Pattern transport (entrywise form).** A resonant triple over
`ZMod 21` is all-nonzero with uniform pattern iff its CRT shadows
form a `ProdFamily` pair. -/
theorem withinFamily_transport_entries (a b c : ZMod 21) :
    (TripleAllNonzero (a, b, c) ∧ UniformPattern (a, b, c)) ↔
    ProdFamily (tripleCrtEquiv (a, b, c)).1 (tripleCrtEquiv (a, b, c)).2 := by
  rw [uniformPattern_transport_entries a b c]
  show (TripleAllNonzero (a, b, c) ∧
      ((TripleAllZero (tripleCrtEquiv (a, b, c)).1 ∨
          TripleAllNonzero (tripleCrtEquiv (a, b, c)).1) ∧
        (TripleAllZero (tripleCrtEquiv (a, b, c)).2 ∨
          TripleAllNonzero (tripleCrtEquiv (a, b, c)).2))) ↔
    ((TripleAllZero (tripleCrtEquiv (a, b, c)).1 ∨
        TripleAllNonzero (tripleCrtEquiv (a, b, c)).1) ∧
      (TripleAllZero (tripleCrtEquiv (a, b, c)).2 ∨
        TripleAllNonzero (tripleCrtEquiv (a, b, c)).2) ∧
      ¬ (TripleAllZero (tripleCrtEquiv (a, b, c)).1 ∧
        TripleAllZero (tripleCrtEquiv (a, b, c)).2))
  constructor
  · rintro ⟨han, hu3, hu7⟩
    refine ⟨hu3, hu7, ?_⟩
    rintro ⟨hz3, hz7⟩
    exact han.1 ((eq_zero_iff_crt a).2 ⟨hz3.1, hz7.1⟩)
  · rintro ⟨hu3, hu7, hnz⟩
    refine ⟨⟨?_, ?_, ?_⟩, hu3, hu7⟩
    · apply ne_zero_of_comp_ne (x := a)
      rcases hu3 with hz3 | hn3
      · rcases hu7 with hz7 | hn7
        · exact absurd ⟨hz3, hz7⟩ hnz
        · exact fun h => hn7.1 h.2
      · exact fun h => hn3.1 h.1
    · apply ne_zero_of_comp_ne (x := b)
      rcases hu3 with hz3 | hn3
      · rcases hu7 with hz7 | hn7
        · exact absurd ⟨hz3, hz7⟩ hnz
        · exact fun h => hn7.2.1 h.2
      · exact fun h => hn3.2.1 h.1
    · apply ne_zero_of_comp_ne (x := c)
      rcases hu3 with hz3 | hn3
      · rcases hu7 with hz7 | hn7
        · exact absurd ⟨hz3, hz7⟩ hnz
        · exact fun h => hn7.2.2 h.2
      · exact fun h => hn3.2.2 h.1

/-- **Pattern transport.** A resonant triple over `ZMod 21` is
all-nonzero with uniform pattern iff its CRT shadows form a
`ProdFamily` pair. -/
theorem withinFamily_transport (t : ResTriples 21) :
    (TripleAllNonzero t.1 ∧ UniformPattern t.1) ↔
    ProdFamily (resTriplesCrtEquiv t).1.1 (resTriplesCrtEquiv t).2.1 := by
  obtain ⟨⟨a, b, c⟩, _ht⟩ := t
  rw [resTriplesCrtEquiv_fst_val, resTriplesCrtEquiv_snd_val]
  exact withinFamily_transport_entries a b c

/-! ### The strata count: 92 within / 288 mixing -/

/-- The product side has exactly `1*30 + (2*1 + 2*30) = 92`
within-family pairs: split the shadow pairs by which shadow is the
zero triple (not both, by definition of `ProdFamily`), transport
each piece to a product of shadow subtypes, and use the shadow
counts `card_allZero` / `card_allNonzero`. -/
theorem card_withinProd :
    Fintype.card {w : ResTriples 3 × ResTriples 7 //
      ProdFamily w.1.1 w.2.1} = 92 := by
  have split1 : Fintype.card {w : ResTriples 3 × ResTriples 7 //
        ProdFamily w.1.1 w.2.1}
      = Fintype.card {x : {w : ResTriples 3 × ResTriples 7 //
            ProdFamily w.1.1 w.2.1} // TripleAllZero x.1.1.1}
        + Fintype.card {x : {w : ResTriples 3 × ResTriples 7 //
            ProdFamily w.1.1 w.2.1} // ¬ TripleAllZero x.1.1.1} := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl
      (fun x : {w : ResTriples 3 × ResTriples 7 //
        ProdFamily w.1.1 w.2.1} => TripleAllZero x.1.1.1)).symm
  have piece1 : Fintype.card {x : {w : ResTriples 3 × ResTriples 7 //
        ProdFamily w.1.1 w.2.1} // TripleAllZero x.1.1.1} = 30 := by
    calc Fintype.card {x : {w : ResTriples 3 × ResTriples 7 //
            ProdFamily w.1.1 w.2.1} // TripleAllZero x.1.1.1}
        = Fintype.card {w : ResTriples 3 × ResTriples 7 //
            ProdFamily w.1.1 w.2.1 ∧ TripleAllZero w.1.1} :=
          Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
            (fun w : ResTriples 3 × ResTriples 7 => ProdFamily w.1.1 w.2.1)
            (fun w : ResTriples 3 × ResTriples 7 => TripleAllZero w.1.1))
      _ = Fintype.card {w : ResTriples 3 × ResTriples 7 //
            TripleAllZero w.1.1 ∧ TripleAllNonzero w.2.1} :=
          Fintype.card_congr (Equiv.subtypeEquivRight (fun w => by
            constructor
            · rintro ⟨hpf, hz3⟩
              refine ⟨hz3, ?_⟩
              rcases hpf.2.1 with h | h
              · exact absurd ⟨hz3, h⟩ hpf.2.2
              · exact h
            · rintro ⟨hz3, hnz7⟩
              exact ⟨⟨Or.inl hz3, Or.inr hnz7,
                fun h => hnz7.1 h.2.1⟩, hz3⟩))
      _ = Fintype.card ({u : ResTriples 3 // TripleAllZero u.1} ×
            {v : ResTriples 7 // TripleAllNonzero v.1}) :=
          Fintype.card_congr (Equiv.subtypeProdEquivProd
            (p := fun u : ResTriples 3 => TripleAllZero u.1)
            (q := fun v : ResTriples 7 => TripleAllNonzero v.1))
      _ = 1 * 30 := by
          rw [Fintype.card_prod, card_allZero,
            card_allNonzero (n := 7) (by decide)]
      _ = 30 := rfl
  have split2 : Fintype.card {x : {w : ResTriples 3 × ResTriples 7 //
        ProdFamily w.1.1 w.2.1} // ¬ TripleAllZero x.1.1.1}
      = Fintype.card {y : {x : {w : ResTriples 3 × ResTriples 7 //
            ProdFamily w.1.1 w.2.1} // ¬ TripleAllZero x.1.1.1} //
          TripleAllZero y.1.1.2.1}
        + Fintype.card {y : {x : {w : ResTriples 3 × ResTriples 7 //
            ProdFamily w.1.1 w.2.1} // ¬ TripleAllZero x.1.1.1} //
          ¬ TripleAllZero y.1.1.2.1} := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl
      (fun y : {x : {w : ResTriples 3 × ResTriples 7 //
        ProdFamily w.1.1 w.2.1} // ¬ TripleAllZero x.1.1.1} =>
        TripleAllZero y.1.1.2.1)).symm
  have piece2a : Fintype.card {y : {x : {w : ResTriples 3 × ResTriples 7 //
        ProdFamily w.1.1 w.2.1} // ¬ TripleAllZero x.1.1.1} //
        TripleAllZero y.1.1.2.1} = 2 := by
    calc Fintype.card {y : {x : {w : ResTriples 3 × ResTriples 7 //
            ProdFamily w.1.1 w.2.1} // ¬ TripleAllZero x.1.1.1} //
          TripleAllZero y.1.1.2.1}
        = Fintype.card {x : {w : ResTriples 3 × ResTriples 7 //
            ProdFamily w.1.1 w.2.1} //
            ¬ TripleAllZero x.1.1.1 ∧ TripleAllZero x.1.2.1} :=
          Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
            (fun x : {w : ResTriples 3 × ResTriples 7 //
              ProdFamily w.1.1 w.2.1} => ¬ TripleAllZero x.1.1.1)
            (fun x : {w : ResTriples 3 × ResTriples 7 //
              ProdFamily w.1.1 w.2.1} => TripleAllZero x.1.2.1))
      _ = Fintype.card {w : ResTriples 3 × ResTriples 7 //
            ProdFamily w.1.1 w.2.1 ∧
              (¬ TripleAllZero w.1.1 ∧ TripleAllZero w.2.1)} :=
          Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
            (fun w : ResTriples 3 × ResTriples 7 => ProdFamily w.1.1 w.2.1)
            (fun w : ResTriples 3 × ResTriples 7 =>
              ¬ TripleAllZero w.1.1 ∧ TripleAllZero w.2.1))
      _ = Fintype.card {w : ResTriples 3 × ResTriples 7 //
            TripleAllNonzero w.1.1 ∧ TripleAllZero w.2.1} :=
          Fintype.card_congr (Equiv.subtypeEquivRight (fun w => by
            constructor
            · rintro ⟨hpf, hnz3, hz7⟩
              refine ⟨?_, hz7⟩
              rcases hpf.1 with h | h
              · exact absurd h hnz3
              · exact h
            · rintro ⟨hnz3, hz7⟩
              refine ⟨⟨Or.inr hnz3, Or.inl hz7,
                fun h => hnz3.1 h.1.1⟩, ?_, hz7⟩
              exact fun hz => allZero_not_allNonzero hz hnz3))
      _ = Fintype.card ({u : ResTriples 3 // TripleAllNonzero u.1} ×
            {v : ResTriples 7 // TripleAllZero v.1}) :=
          Fintype.card_congr (Equiv.subtypeProdEquivProd
            (p := fun u : ResTriples 3 => TripleAllNonzero u.1)
            (q := fun v : ResTriples 7 => TripleAllZero v.1))
      _ = 2 * 1 := by
          rw [Fintype.card_prod, card_allNonzero (n := 3) (by decide),
            card_allZero]
      _ = 2 := rfl
  have piece2b : Fintype.card {y : {x : {w : ResTriples 3 × ResTriples 7 //
        ProdFamily w.1.1 w.2.1} // ¬ TripleAllZero x.1.1.1} //
        ¬ TripleAllZero y.1.1.2.1} = 60 := by
    calc Fintype.card {y : {x : {w : ResTriples 3 × ResTriples 7 //
            ProdFamily w.1.1 w.2.1} // ¬ TripleAllZero x.1.1.1} //
          ¬ TripleAllZero y.1.1.2.1}
        = Fintype.card {x : {w : ResTriples 3 × ResTriples 7 //
            ProdFamily w.1.1 w.2.1} //
            ¬ TripleAllZero x.1.1.1 ∧ ¬ TripleAllZero x.1.2.1} :=
          Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
            (fun x : {w : ResTriples 3 × ResTriples 7 //
              ProdFamily w.1.1 w.2.1} => ¬ TripleAllZero x.1.1.1)
            (fun x : {w : ResTriples 3 × ResTriples 7 //
              ProdFamily w.1.1 w.2.1} => ¬ TripleAllZero x.1.2.1))
      _ = Fintype.card {w : ResTriples 3 × ResTriples 7 //
            ProdFamily w.1.1 w.2.1 ∧
              (¬ TripleAllZero w.1.1 ∧ ¬ TripleAllZero w.2.1)} :=
          Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
            (fun w : ResTriples 3 × ResTriples 7 => ProdFamily w.1.1 w.2.1)
            (fun w : ResTriples 3 × ResTriples 7 =>
              ¬ TripleAllZero w.1.1 ∧ ¬ TripleAllZero w.2.1))
      _ = Fintype.card {w : ResTriples 3 × ResTriples 7 //
            TripleAllNonzero w.1.1 ∧ TripleAllNonzero w.2.1} :=
          Fintype.card_congr (Equiv.subtypeEquivRight (fun w => by
            constructor
            · rintro ⟨hpf, hnz3, hnz7⟩
              constructor
              · rcases hpf.1 with h | h
                · exact absurd h hnz3
                · exact h
              · rcases hpf.2.1 with h | h
                · exact absurd h hnz7
                · exact h
            · rintro ⟨hnz3, hnz7⟩
              refine ⟨⟨Or.inr hnz3, Or.inr hnz7,
                fun h => hnz3.1 h.1.1⟩, ?_, ?_⟩
              · exact fun hz => allZero_not_allNonzero hz hnz3
              · exact fun hz => allZero_not_allNonzero hz hnz7))
      _ = Fintype.card ({u : ResTriples 3 // TripleAllNonzero u.1} ×
            {v : ResTriples 7 // TripleAllNonzero v.1}) :=
          Fintype.card_congr (Equiv.subtypeProdEquivProd
            (p := fun u : ResTriples 3 => TripleAllNonzero u.1)
            (q := fun v : ResTriples 7 => TripleAllNonzero v.1))
      _ = 2 * 30 := by
          rw [Fintype.card_prod, card_allNonzero (n := 3) (by decide),
            card_allNonzero (n := 7) (by decide)]
      _ = 60 := rfl
  rw [split1, piece1, split2, piece2a, piece2b]

/-- **TR-4 (within).** Exactly 92 of the all-nonzero resonant triples
stay within one gcd family. -/
theorem card_within_family :
    Fintype.card {t : ResTriples 21 //
      TripleAllNonzero t.1 ∧ UniformPattern t.1} = 92 :=
  (Fintype.card_congr (Equiv.subtypeEquiv resTriplesCrtEquiv
    (q := fun w : ResTriples 3 × ResTriples 7 => ProdFamily w.1.1 w.2.1)
    (fun t => withinFamily_transport t))).trans card_withinProd

/-- The all-nonzero resonant triples over `ZMod 21` number 380. -/
theorem card_allNonzero_21 :
    Fintype.card {t : ResTriples 21 // TripleAllNonzero t.1} = 380 :=
  card_allNonzero (n := 21) (by decide)

/-- **TR-4 (mixing).** Exactly 288 of the all-nonzero resonant triples
mix gcd families: `380 − 92`. -/
theorem card_mixing :
    Fintype.card {t : ResTriples 21 //
      TripleAllNonzero t.1 ∧ ¬ UniformPattern t.1} = 288 := by
  calc Fintype.card {t : ResTriples 21 //
        TripleAllNonzero t.1 ∧ ¬ UniformPattern t.1}
      = Fintype.card {s : {t : ResTriples 21 // TripleAllNonzero t.1} //
          ¬ UniformPattern s.1.1} :=
        Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
          (fun t : ResTriples 21 => TripleAllNonzero t.1)
          (fun t : ResTriples 21 => ¬ UniformPattern t.1)).symm
    _ = Fintype.card {t : ResTriples 21 // TripleAllNonzero t.1} -
          Fintype.card {s : {t : ResTriples 21 // TripleAllNonzero t.1} //
            UniformPattern s.1.1} :=
        Fintype.card_subtype_compl _
    _ = 380 - 92 := by
        rw [card_allNonzero_21, Fintype.card_congr
          (Equiv.subtypeSubtypeEquivSubtypeInter
            (fun t : ResTriples 21 => TripleAllNonzero t.1)
            (fun t : ResTriples 21 => UniformPattern t.1)),
          card_within_family]
    _ = 288 := rfl

end ThetLogos
