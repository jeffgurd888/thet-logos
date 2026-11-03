/-
# U-3a ODD RING — the general-n mirror/resonance package

Brick: U-3a of the unification line, per the governing scoping
dossier `whitepaper/unification-scoping-2026-11-03.md` §2 (U-3).
Commissioned by Jeff 2026-11-03 ("can we start to put some of these
together into a unified theory"); fired 2026-11-03 ("All"). Built in
the isolated worktree `~/workspace/thet-logos-u3a`, branch
`u3a-lane`, from main-tree HEAD `4e35329` (the item-5 ceremony
commit); NOT integrated — the parent runs the ceremony.

**What this module proves — and all it proves.** Two promotions of
the Mirror-21 / Triplets packages from the seat `21` to their
general forms, BY ADDITION: no statement in
`ThetLogos.MirrorTwentyOneTriplets` is edited, renamed, or
re-proved; the 21-specific constructions stay exactly where they
were, and the general theorems below make the 21 case a corollary.

1. **Resonance transport along CRT, general coprime.** For
   `m.Coprime n`, the resonant triples of `ZMod (m * n)` are
   exactly the pairs of resonant triples over `ZMod m` and
   `ZMod n`, under Mathlib's own `ZMod.chineseRemainder`
   (`resTriples_crtEquiv`). Triplets' hand-rolled `crt21` /
   `resTriplesCrtEquiv` is the instance `(m, n) = (3, 7)`.

2. **Mirror organization at every odd `n`.** For odd `n`, the
   resonant triples of `ZMod n` organize as `(n^2 - 1) / 2`
   mirror-pairs plus the lone fixed center triple:
   `(mirrorPairsN n).card = (n^2 - 1) / 2` and
   `mirrorFixedN n = {centerTripleN n}` (`mirror_organization_odd`).
   The fixed-point step routes through AxiomTet's general
   `zmod_self_neg_iff`, replacing Triplets' 21-only
   `neg_eq_self_imp_eq_zero`; the count `n^2` is Triplets'
   already-general `card_resonant`. At `n = 21` this returns
   `220` pairs and the singleton fixed set
   (`card_mirror_pairsN_21`).

The general mirror objects carry the `N` suffix (`mirrorTripleN`,
`centerTripleN`, `mirrorPairsN`, `mirrorFixedN`) because the
un-suffixed names are taken by Triplets' frozen 21-specific
definitions; the statements are the scoping's, at general `n`.

**Out of scope, on the face:** TR-4's strata (the gcd-class
combinatorics of `21 = 3 * 7` specifically) are NOT generalized
here; U-3b (the abstract finite-involution fixed-function theorem)
is a separate brick, not in this module. Kernel dimension `1`
(connected webs) and fixed-point counting here are different
theorems and are not conflated.

**NO CLAIM** — parts of any official Millennium statement closed
by this module: 0. Dials: 0/4. Finite combinatorics only.

This module is NOT in the root import list of the library; it is
verified by a targeted build.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import ThetLogos.MirrorTwentyOneTriplets
import ThetLogos.AxiomTet

namespace ThetLogos

/-! ## Part 1 — resonance transport along CRT, general coprime -/

/-- Coordinatewise CRT on triples, regrouped by component, for
general coprime `m n`. At `(m, n) = (3, 7)` this is Triplets'
`tripleCrtEquiv`, with `crt21` replaced by Mathlib's
`ZMod.chineseRemainder`. -/
def tripleCrtEquivGen {m n : ℕ} (h : m.Coprime n) :
    (ZMod (m * n) × ZMod (m * n) × ZMod (m * n)) ≃
    (ZMod m × ZMod m × ZMod m) × (ZMod n × ZMod n × ZMod n) where
  toFun t := (((ZMod.chineseRemainder h t.1).1,
      (ZMod.chineseRemainder h t.2.1).1, (ZMod.chineseRemainder h t.2.2).1),
    ((ZMod.chineseRemainder h t.1).2, (ZMod.chineseRemainder h t.2.1).2,
      (ZMod.chineseRemainder h t.2.2).2))
  invFun u := ((ZMod.chineseRemainder h).symm (u.1.1, u.2.1),
    (ZMod.chineseRemainder h).symm (u.1.2.1, u.2.2.1),
    (ZMod.chineseRemainder h).symm (u.1.2.2, u.2.2.2))
  left_inv t := by
    obtain ⟨a, b, c⟩ := t
    simp only [Prod.eta, RingEquiv.symm_apply_apply]
  right_inv u := by
    obtain ⟨⟨a, b, c⟩, ⟨d, e, f⟩⟩ := u
    simp only [RingEquiv.apply_symm_apply]

/-- Resonance is a componentwise property under CRT, in general:
a triple over `ZMod (m * n)` is resonant iff both of its CRT
shadows are. -/
theorem resonant_tripleCrtEquivGen {m n : ℕ} (h : m.Coprime n)
    (t : ZMod (m * n) × ZMod (m * n) × ZMod (m * n)) :
    Resonant t ↔ Resonant (tripleCrtEquivGen h t).1 ∧
      Resonant (tripleCrtEquivGen h t).2 := by
  obtain ⟨a, b, c⟩ := t
  show a + b + c = 0 ↔
    ((ZMod.chineseRemainder h a).1 + (ZMod.chineseRemainder h b).1 +
        (ZMod.chineseRemainder h c).1 = 0) ∧
      ((ZMod.chineseRemainder h a).2 + (ZMod.chineseRemainder h b).2 +
        (ZMod.chineseRemainder h c).2 = 0)
  have hsum : ZMod.chineseRemainder h (a + b + c)
      = ZMod.chineseRemainder h a + ZMod.chineseRemainder h b
        + ZMod.chineseRemainder h c := by
    simp [map_add]
  constructor
  · intro h0
    have h1 : ZMod.chineseRemainder h (a + b + c) = 0 := by
      rw [h0, map_zero]
    rw [hsum] at h1
    exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩
  · rintro ⟨h1, h2⟩
    have h0 : ZMod.chineseRemainder h (a + b + c) = 0 := by
      rw [hsum]
      exact Prod.ext h1 h2
    have hinj : ZMod.chineseRemainder h (a + b + c)
        = ZMod.chineseRemainder h 0 := by rw [h0, map_zero]
    exact (ZMod.chineseRemainder h).injective hinj

/-- **U-3a headline 1 (CRT transport, general).** The resonant
triples of `ZMod (m * n)` are exactly the pairs of resonant
triples over `ZMod m` and `ZMod n`, under the Chinese remainder
isomorphism — for every coprime pair `(m, n)`. Triplets'
`resTriplesCrtEquiv` at `21 = 3 * 7` is the first instance. -/
def resTriples_crtEquiv {m n : ℕ} (h : m.Coprime n) :
    ResTriples (m * n) ≃ ResTriples m × ResTriples n where
  toFun t := (⟨(tripleCrtEquivGen h t.1).1,
      ((resonant_tripleCrtEquivGen h t.1).1 t.2).1⟩,
    ⟨(tripleCrtEquivGen h t.1).2,
      ((resonant_tripleCrtEquivGen h t.1).1 t.2).2⟩)
  invFun u := ⟨(tripleCrtEquivGen h).symm (u.1.1, u.2.1), by
    have h2 := resonant_tripleCrtEquivGen h
      ((tripleCrtEquivGen h).symm (u.1.1, u.2.1))
    rw [Equiv.apply_symm_apply] at h2
    exact h2.2 ⟨u.1.2, u.2.2⟩⟩
  left_inv t := by
    apply Subtype.ext
    show (tripleCrtEquivGen h).symm (tripleCrtEquivGen h t.1) = t.1
    exact Equiv.symm_apply_apply (tripleCrtEquivGen h) t.1
  right_inv u := by
    obtain ⟨⟨u1, h1⟩, ⟨u2, h2⟩⟩ := u
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact congrArg Prod.fst
        (Equiv.apply_symm_apply (tripleCrtEquivGen h) (u1, u2))
    · exact congrArg Prod.snd
        (Equiv.apply_symm_apply (tripleCrtEquivGen h) (u1, u2))

/-- The first component of the general CRT equiv, as a rewrite
rule (so later proofs never reduce through the equiv itself). -/
theorem resTriples_crtEquiv_fst_val {m n : ℕ} (h : m.Coprime n)
    (t : ResTriples (m * n)) :
    (resTriples_crtEquiv h t).1.1 = (tripleCrtEquivGen h t.1).1 := rfl

/-- The second component of the general CRT equiv. -/
theorem resTriples_crtEquiv_snd_val {m n : ℕ} (h : m.Coprime n)
    (t : ResTriples (m * n)) :
    (resTriples_crtEquiv h t).2.1 = (tripleCrtEquivGen h t.1).2 := rfl

/-- The count splits over a coprime product: the resonant triples
of `ZMod (m * n)` number the product of the two shadow counts
(each side is also `(factor)^2`, by Triplets' `card_resonant`). -/
theorem card_resonant_mul {m n : ℕ} [NeZero m] [NeZero n]
    [NeZero (m * n)] (h : m.Coprime n) :
    Fintype.card (ResTriples (m * n))
      = Fintype.card (ResTriples m) * Fintype.card (ResTriples n) := by
  rw [Fintype.card_congr (resTriples_crtEquiv h), Fintype.card_prod]

/-- **The 21 case as a corollary of the general theorem.** The
equiv Triplets built by hand is the `(3, 7)` instance of
`resTriples_crtEquiv`; `21` here is `3 * 7` on the nose. -/
def resTriplesCrtEquiv_of_general :
    ResTriples 21 ≃ ResTriples 3 × ResTriples 7 :=
  resTriples_crtEquiv (m := 3) (n := 7) (by decide)

/-! ## Part 2 — mirror organization at every odd `n` -/

/-- In `ZMod n` with `n` odd, self-mirror means zero: `-x = x`
forces `x = 0`. This is AxiomTet's `zmod_self_neg_iff` (proved
for `ZMod (2 * k + 1)`) transported along `Odd n` — the general
fact behind both Mirror-21's unique center and Triplets' lone
fixed triple, whose 21-only form was `neg_eq_self_imp_eq_zero`. -/
theorem neg_eq_self_imp_eq_zero_odd {n : ℕ} (hn : Odd n) (x : ZMod n)
    (h : -x = x) : x = 0 := by
  obtain ⟨k, rfl⟩ := hn
  exact (zmod_self_neg_iff k x).1 h.symm

/-- The mirror (negation) as a self-map of the resonant triples
of `ZMod n`, for any `n`. At `21` this is Triplets'
`mirrorTriple`. -/
def mirrorTripleN {n : ℕ} : ResTriples n → ResTriples n :=
  fun t => ⟨negTriple t.1, resonant_neg t.2⟩

/-- The mirror is an involution on resonant triples, at any `n`. -/
theorem mirrorTripleN_involutive {n : ℕ} :
    Function.Involutive (mirrorTripleN (n := n)) := by
  intro t
  obtain ⟨⟨a, b, c⟩, ht⟩ := t
  simp [mirrorTripleN, negTriple]

/-- The center triple `(0, 0, 0)` over `ZMod n`: the mirror's
candidate fixed point. -/
def centerTripleN (n : ℕ) : ResTriples n := ⟨(0, 0, 0), by simp [Resonant]⟩

theorem mirrorTripleN_center {n : ℕ} :
    mirrorTripleN (centerTripleN n) = centerTripleN n := by
  simp [mirrorTripleN, negTriple, centerTripleN]

/-- At odd `n`, the center triple is the mirror's ONLY fixed
triple among the resonant triples — the lone unpaired
correlation, at every odd modulus. -/
theorem mirrorTripleN_fixed {n : ℕ} (hn : Odd n) (t : ResTriples n)
    (h : mirrorTripleN t = t) : t = centerTripleN n := by
  obtain ⟨⟨a, b, c⟩, ht⟩ := t
  have h1 : (-a, -b, -c) = (a, b, c) := congrArg Subtype.val h
  have ha : a = 0 := neg_eq_self_imp_eq_zero_odd hn a
    (congrArg Prod.fst h1)
  have hb : b = 0 := neg_eq_self_imp_eq_zero_odd hn b
    (congrArg (fun p => p.2.1) h1)
  have hc : c = 0 := neg_eq_self_imp_eq_zero_odd hn c
    (congrArg (fun p => p.2.2) h1)
  apply Subtype.ext
  show (a, b, c) = (0, 0, 0)
  exact Prod.ext ha (Prod.ext hb hc)

/-- The mirror-fixed resonant triples of `ZMod n`, as a finset. -/
def mirrorFixedN (n : ℕ) [NeZero n] : Finset (ResTriples n) :=
  Finset.univ.filter fun t => mirrorTripleN t = t

/-- At odd `n`, the fixed set is exactly the singleton center. -/
theorem mirrorFixedN_eq {n : ℕ} [NeZero n] (hn : Odd n) :
    mirrorFixedN n = {centerTripleN n} := by
  ext t
  simp only [mirrorFixedN, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro h
    exact mirrorTripleN_fixed hn t h
  · intro h
    rw [h]
    exact mirrorTripleN_center

/-- At odd `n`, exactly one resonant triple is mirror-fixed. -/
theorem card_mirrorFixedN {n : ℕ} [NeZero n] (hn : Odd n) :
    (mirrorFixedN n).card = 1 := by
  rw [mirrorFixedN_eq hn, Finset.card_singleton]

/-- The mirror-pairs at `n`: images of the non-fixed resonant
triples under `t ↦ {t, mirror t}`. -/
def mirrorPairsN (n : ℕ) [NeZero n] : Finset (Finset (ResTriples n)) :=
  (Finset.univ.filter fun t => mirrorTripleN t ≠ t).image
    (fun t => {t, mirrorTripleN t})

/-- Each mirror-pair's fiber in the non-fixed triples is exactly
the pair itself, at any `n`. -/
theorem mirror_pair_fiberN {n : ℕ} [NeZero n] (t : ResTriples n)
    (ht : mirrorTripleN t ≠ t) :
    ((Finset.univ.filter fun s : ResTriples n => mirrorTripleN s ≠ s).filter
      fun s => ({s, mirrorTripleN s} : Finset (ResTriples n))
        = {t, mirrorTripleN t})
    = {t, mirrorTripleN t} := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hs, hps⟩
    have hmem : s ∈ ({t, mirrorTripleN t} : Finset (ResTriples n)) :=
      hps ▸ Finset.mem_insert_self s _
    simpa using hmem
  · rintro (rfl | rfl)
    · exact ⟨ht, rfl⟩
    · refine ⟨?_, ?_⟩
      · rw [mirrorTripleN_involutive t]
        exact Ne.symm ht
      · rw [mirrorTripleN_involutive t]
        exact Finset.pair_comm _ _

/-- **U-3a headline 2 (the pair count).** At every odd `n`, the
`n^2` resonant triples form exactly `(n^2 - 1) / 2` mirror-pairs
(the remaining triple is the fixed center, counted separately in
`card_mirrorFixedN`). -/
theorem card_mirror_pairs_odd {n : ℕ} [NeZero n] (hn : Odd n) :
    (mirrorPairsN n).card = (n ^ 2 - 1) / 2 := by
  have hn1 : 1 ≤ n := by
    obtain ⟨k, hk⟩ := hn
    omega
  have htotal : (Finset.univ : Finset (ResTriples n)).card = n ^ 2 := by
    rw [Finset.card_univ]
    exact card_resonant n
  have hfixed : (Finset.univ.filter fun t : ResTriples n =>
      mirrorTripleN t = t).card = 1 := by
    have hdef : (Finset.univ.filter fun t : ResTriples n =>
        mirrorTripleN t = t) = mirrorFixedN n := rfl
    rw [hdef, mirrorFixedN_eq hn, Finset.card_singleton]
  have hnf : (Finset.univ.filter fun t : ResTriples n =>
      mirrorTripleN t ≠ t).card = n ^ 2 - 1 := by
    have hadd := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (ResTriples n)))
      (p := fun t : ResTriples n => mirrorTripleN t = t)
    rw [hfixed, htotal] at hadd
    have hnf' : (Finset.univ.filter fun t : ResTriples n =>
        ¬ mirrorTripleN t = t).card = n ^ 2 - 1 := by omega
    exact hnf'
  have key0 := Finset.card_eq_sum_card_image
    (fun t : ResTriples n => ({t, mirrorTripleN t} : Finset (ResTriples n)))
    (Finset.univ.filter fun t => mirrorTripleN t ≠ t)
  rw [hnf] at key0
  have hfib : ∀ y ∈ (Finset.univ.filter fun t : ResTriples n =>
        mirrorTripleN t ≠ t).image
        (fun t => ({t, mirrorTripleN t} : Finset (ResTriples n))),
      ((Finset.univ.filter fun s => mirrorTripleN s ≠ s).filter
        fun s => ({s, mirrorTripleN s} : Finset (ResTriples n)) = y).card
        = 2 := by
    intro y hy
    obtain ⟨t, htmem, rfl⟩ := Finset.mem_image.1 hy
    have ht : mirrorTripleN t ≠ t := (Finset.mem_filter.1 htmem).2
    rw [mirror_pair_fiberN t ht]
    exact Finset.card_pair (Ne.symm ht)
  have hsum := Finset.sum_const_nat hfib
  rw [hsum] at key0
  -- key0 : n^2 - 1 = (image …).card * 2; the image is `mirrorPairsN n`
  -- by definition, so the key restates in the goal's own terms.
  have key : (mirrorPairsN n).card * 2 = n ^ 2 - 1 := key0.symm
  omega

/-- **U-3a headline 2, the organization in one statement.** At
every odd `n`: the mirror-pairs number `(n^2 - 1) / 2`, and the
mirror-fixed set is the singleton center. -/
theorem mirror_organization_odd {n : ℕ} [NeZero n] (hn : Odd n) :
    (mirrorPairsN n).card = (n ^ 2 - 1) / 2 ∧
      mirrorFixedN n = {centerTripleN n} :=
  ⟨card_mirror_pairs_odd hn, mirrorFixedN_eq hn⟩

/-- The organization in additive form: total = 2 · pairs + fixed,
at every odd `n` (the general form of Triplets'
`mirror_organization_21`). -/
theorem mirror_organization_odd_add {n : ℕ} [NeZero n] (hn : Odd n) :
    Fintype.card (ResTriples n)
      = 2 * (mirrorPairsN n).card + (mirrorFixedN n).card := by
  rw [card_resonant n, card_mirror_pairs_odd hn, card_mirrorFixedN hn]
  obtain ⟨k, hk⟩ : Odd (n ^ 2) := hn.pow
  omega

/-- **The 21 count as a corollary.** The general pair count at
`n = 21` returns Triplets' `220` — the hand-proved
`card_mirror_pairs` is now also a one-line instance. -/
theorem card_mirror_pairsN_21 : (mirrorPairsN 21).card = 220 :=
  card_mirror_pairs_odd (n := 21) ⟨10, rfl⟩ |>.trans (by decide)

end ThetLogos
