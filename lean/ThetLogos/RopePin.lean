/-
# RopePin — the massive string: a finite rope's center and tension ladder (finite ℚ seat)

Zero's commission of 2026-11-16 ("scope rope pin and build everything we
need"), in the evening's physical sequence: center bridge pin → centrifugal
gravity → rope. A rope is the string seat grown mass: a finite chain of
links, each link with its own mass and its own length. This pin stands on
`CenterBridgePin`'s weighted center (`wCenter`, imported, not rebuilt):
the rope's center of mass is that weighted center taken with the rope's
own masses at the links' midpoints; its hang is the tension ladder under
a uniform pull; two ropes spliced obey the weighted-average-of-averages
law (`splice`).

THE SEAT. Links `i : Fin n` (`n ≥ 1`), masses `m : Fin n → ℚ` positive,
lengths `ℓ : Fin n → ℚ` positive. Joints are indexed by `ℕ`: joint `k`
(for `0 ≤ k ≤ n`) sits at `jointPos ℓ k`, the sum of the first `k` link
lengths — joint `0` at `0`, joint `n` at `totalLength`. Link `i` spans
`[jointPos ℓ i, jointPos ℓ (i+1)]`; its midpoint is `linkMid ℓ i`.

INDEXING CONVENTION (tension). The rope hangs at rest from a support at
the top. **Link `0` is the TOP link** (at the support), link `n - 1` the
bottom link; `jointPos` measures distance BELOW the support, so joint `0`
is the support itself and joint `n` the free bottom end. `tensionAt g m k`
(for `k : Fin (n + 1)`) is the tension at joint `k`: `g` times the total
mass of the links BELOW joint `k`, which are links `k, k + 1, …, n - 1`
(link `k` hangs from joint `k`). Hence the top joint carries the whole
weight and the bottom joint carries nothing.

What is proved here:
- the **splice law** (`splice`, R-3): the weighted center of two joined
  distributions is the total-mass-weighted average of the two centers,
  the second center shifted by the join offset — the join law for
  weighted centers, stated over two abstract distributions (on `ι ⊕ κ`);
- the **tension ladder** (`tensionAt_top`, `tensionAt_succ_add`,
  `tensionAt_succ_lt`, `tensionAt_bottom`, R-4): the top joint carries
  `g * totalMass`; descending one joint drops the tension by exactly the
  link's weight `g * m k`, so the ladder is strictly decreasing; the
  bottom joint carries `0`;
- the **span bounds** (`ropeCenter_bounds`, R-1): the rope's center lies
  in its span `[0, totalLength]`, via the one general lemma this pin adds
  (`wCenter_bounds`: a positively weighted average lies between any
  uniform lower and upper bounds of the positions);
- the **uniform rope** (`ropeCenter_uniform`, R-2): equal masses and
  equal lengths put the center at `totalLength / 2`, the midpoint.

Fences (read before citing):
- Finite statics only. The **catenary is NOT built**: the continuous
  hanging curve is analysis, not this seat, and no statement here names
  or approximates it. No elasticity, no dynamics, no friction, no pulleys.
- The tension ladder is stated for a rope hanging at rest under a uniform
  pull `g` — `g` is a bare positive parameter, never named a metric, a
  metric component, or a redshift factor (K-TOL-PROXY discipline).
- This pin is NOT a gravity object: the corpus holds zero gravity
  objects, Dial 2 = 0, and only G-READ stands. NO CLAIM.
- The thermal / Gibbs leg is NOT in this pin (the string pins carry it);
  a rotating-rope leg belongs to the queued centrifugal brick's family
  and is named here as a follow-on only.

Charter: T5 for the seeing; the theorems below are T1 lane grade when
proved. Working label only — the public name is Zero's to coin.

Brick 1a lands the seat and the splice law; Brick 1b the tension ladder;
Brick 2 the span bounds and the uniform rope.
-/

import Mathlib
import ThetLogos.CenterBridgePin

namespace ThetLogos.RopePin

open Finset

variable {n : ℕ} [NeZero n]

/-- Joint positions along the rope's own line: joint `k` sits at the sum
of the first `k` link lengths (joint `0` at `0`, joint `n` at the total
length). Lengths past the last link contribute `0`. -/
def jointPos (ℓ : Fin n → ℚ) (k : ℕ) : ℚ :=
  ∑ i ∈ Finset.range k, (if h : i < n then ℓ ⟨i, h⟩ else 0)

/-- The midpoint of link `i`: its starting joint plus half its length. -/
def linkMid (ℓ : Fin n → ℚ) (i : Fin n) : ℚ :=
  jointPos ℓ i.val + ℓ i / 2

/-- The rope's total length: the sum of the link lengths. -/
def totalLength (ℓ : Fin n → ℚ) : ℚ :=
  ∑ i, ℓ i

/-- The rope's total mass: the sum of the link masses. -/
def totalMass (m : Fin n → ℚ) : ℚ :=
  ∑ i, m i

/-- The rope's center of mass: the bridge pin's weighted center of the
link midpoints under the link masses. -/
def ropeCenter (m ℓ : Fin n → ℚ) : ℚ :=
  CenterBridgePin.wCenter m (linkMid ℓ)

/-- The tension at joint `k`: `g` times the total mass of the links below
joint `k` — links `k, k + 1, …, n - 1`, link `0` being the TOP link at the
support (see the indexing convention on the module's face). -/
def tensionAt (g : ℚ) (m : Fin n → ℚ) (k : Fin (n + 1)) : ℚ :=
  g * ∑ i ∈ Finset.univ.filter (fun i : Fin n => k.val ≤ i.val), m i

/-- **R-3, THE SPLICE LAW (the join law for weighted centers).** Two
distributions `A` on `ι` and `B` on `κ`, joined on `ι ⊕ κ` with `B`'s
positions shifted by `s`: the joined weighted center is the
total-weight-weighted average of the two centers, the second center
carrying the shift. For ropes: `A` is the upper rope, `s` its total
length, `B` the spliced-on rope below it. -/
theorem splice {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    {wA : ι → ℚ} {xA : ι → ℚ} {wB : κ → ℚ} {xB : κ → ℚ}
    (hwA : ∀ i, 0 < wA i) (hwB : ∀ j, 0 < wB j) (s : ℚ) :
    CenterBridgePin.wCenter (Sum.elim wA wB) (Sum.elim xA (fun j => s + xB j))
      = ((∑ i, wA i) * CenterBridgePin.wCenter wA xA
          + (∑ j, wB j) * (s + CenterBridgePin.wCenter wB xB))
        / ((∑ i, wA i) + (∑ j, wB j)) := by
  have hSA : (0 : ℚ) < ∑ i, wA i := CenterBridgePin.sum_pos_of_pos hwA
  have hSB : (0 : ℚ) < ∑ j, wB j := CenterBridgePin.sum_pos_of_pos hwB
  have hS : (0 : ℚ) < (∑ i, wA i) + (∑ j, wB j) := add_pos hSA hSB
  have hSA0 : (∑ i, wA i) ≠ 0 := ne_of_gt hSA
  have hSB0 : (∑ j, wB j) ≠ 0 := ne_of_gt hSB
  have hS0 : ((∑ i, wA i) + (∑ j, wB j)) ≠ 0 := ne_of_gt hS
  have hnumB : (∑ j, wB j * (s + xB j)) = s * (∑ j, wB j) + ∑ j, wB j * xB j := by
    calc (∑ j, wB j * (s + xB j)) = ∑ j, (s * wB j + wB j * xB j) :=
          Finset.sum_congr rfl (fun j _ => by ring)
    _ = (∑ j, s * wB j) + ∑ j, wB j * xB j := Finset.sum_add_distrib
    _ = s * (∑ j, wB j) + ∑ j, wB j * xB j := by rw [Finset.mul_sum]
  unfold CenterBridgePin.wCenter
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [hnumB]
  field_simp

/-- **R-4, the ladder's top.** The top joint (the support, joint `0`)
carries the whole weight: `tensionAt g m 0 = g * totalMass m`. -/
theorem tensionAt_top (g : ℚ) (m : Fin n → ℚ) :
    tensionAt g m 0 = g * totalMass m := by
  have hfil : Finset.univ.filter (fun i : Fin n => (0 : Fin (n + 1)).val ≤ i.val)
      = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro i _
    simp
  unfold tensionAt totalMass
  rw [hfil]

/-- **R-4, the ladder's step.** Descending from joint `k` to joint `k + 1`
drops the tension by exactly link `k`'s weight `g * m k`: joint `k` also
carries link `k`, which hangs from it. -/
theorem tensionAt_succ_add (g : ℚ) (m : Fin n → ℚ) (k : Fin n) :
    tensionAt g m k.castSucc = tensionAt g m k.succ + g * m k := by
  have hkB : k ∉ Finset.univ.filter (fun i : Fin n => k.val + 1 ≤ i.val) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hset : Finset.univ.filter (fun i : Fin n => k.val ≤ i.val)
      = insert k (Finset.univ.filter (fun i : Fin n => k.val + 1 ≤ i.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases hik : i = k
      · exact Or.inl hik
      · right
        have hne : i.val ≠ k.val := fun hv => hik (Fin.ext hv)
        omega
    · intro h
      rcases h with rfl | h
      · exact le_refl _
      · omega
  unfold tensionAt
  show g * (∑ i ∈ Finset.univ.filter (fun i : Fin n => k.val ≤ i.val), m i)
      = g * (∑ i ∈ Finset.univ.filter (fun i : Fin n => (k.val + 1) ≤ i.val), m i)
        + g * m k
  rw [hset, Finset.sum_insert hkB]
  ring

/-- **R-4, the ladder descends strictly.** Each joint carries strictly
less than the joint above it (the drop is a link's positive weight). -/
theorem tensionAt_succ_lt {g : ℚ} (hg : 0 < g) {m : Fin n → ℚ}
    (hm : ∀ i, 0 < m i) (k : Fin n) :
    tensionAt g m k.succ < tensionAt g m k.castSucc := by
  rw [tensionAt_succ_add]
  exact lt_add_of_pos_right _ (mul_pos hg (hm k))

/-- **R-4, the ladder's foot.** The bottom joint (joint `n`, the free end)
carries nothing. -/
theorem tensionAt_bottom (g : ℚ) (m : Fin n → ℚ) :
    tensionAt g m (Fin.last n) = 0 := by
  have hfil : Finset.univ.filter (fun i : Fin n => (Fin.last n).val ≤ i.val)
      = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [Fin.val_last] at hi
    exact absurd hi (not_le_of_gt i.isLt)
  unfold tensionAt
  rw [hfil, Finset.sum_empty, mul_zero]

/-- **The one general lemma this pin adds.** A positively weighted
average of positions lies between any uniform lower bound and any uniform
upper bound of the positions. -/
theorem wCenter_bounds {w x : Fin n → ℚ} (hw : ∀ i, 0 < w i) {a b : ℚ}
    (ha : ∀ i, a ≤ x i) (hb : ∀ i, x i ≤ b) :
    a ≤ CenterBridgePin.wCenter w x ∧ CenterBridgePin.wCenter w x ≤ b := by
  haveI : Nonempty (Fin n) := ⟨⟨0, NeZero.pos n⟩⟩
  have hS : (0 : ℚ) < ∑ i, w i := CenterBridgePin.sum_pos_of_pos hw
  have hnum_lo : (∑ i, w i) * a ≤ ∑ i, w i * x i := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (ha i) (le_of_lt (hw i)))
  have hnum_hi : (∑ i, w i * x i) ≤ (∑ i, w i) * b := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hb i) (le_of_lt (hw i)))
  unfold CenterBridgePin.wCenter
  constructor
  · rw [le_div_iff₀ hS]
    calc a * (∑ i, w i) = (∑ i, w i) * a := mul_comm _ _
    _ ≤ ∑ i, w i * x i := hnum_lo
  · rw [div_le_iff₀ hS]
    calc (∑ i, w i * x i) ≤ (∑ i, w i) * b := hnum_hi
    _ = b * (∑ i, w i) := mul_comm _ _

/-- Every link midpoint lies in the rope's span: `0 ≤ linkMid ℓ i` and
`linkMid ℓ i ≤ totalLength ℓ`. -/
theorem linkMid_mem_span {ℓ : Fin n → ℚ} (hℓ : ∀ i, 0 < ℓ i) (i : Fin n) :
    0 ≤ linkMid ℓ i ∧ linkMid ℓ i ≤ totalLength ℓ := by
  have hterm : ∀ j : ℕ, (0 : ℚ) ≤ (if h : j < n then ℓ ⟨j, h⟩ else 0) :=
    fun j => by split_ifs with h; exact le_of_lt (hℓ _); exact le_refl 0
  have hJPnn : ∀ k : ℕ, 0 ≤ jointPos ℓ k :=
    fun k => Finset.sum_nonneg (fun j _ => hterm j)
  have hJPmono : ∀ {k k' : ℕ}, k ≤ k' → jointPos ℓ k ≤ jointPos ℓ k' :=
    fun hkk => Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) hkk))
      (fun j _ _ => hterm j)
  have hJPsucc : jointPos ℓ (i.val + 1) = jointPos ℓ i.val + ℓ i := by
    unfold jointPos
    rw [Finset.sum_range_succ]
    rw [dif_pos i.isLt]
  have hJPn : jointPos ℓ n = totalLength ℓ := by
    unfold jointPos totalLength
    rw [← Fin.sum_univ_eq_sum_range (fun j => if h : j < n then ℓ ⟨j, h⟩ else 0) n]
    apply Finset.sum_congr rfl
    intro j _
    rw [dif_pos j.isLt]
  constructor
  · unfold linkMid
    have h1 : (0 : ℚ) ≤ jointPos ℓ i.val := hJPnn _
    have h2 : (0 : ℚ) ≤ ℓ i / 2 := by linarith [hℓ i]
    linarith
  · unfold linkMid
    have hle : jointPos ℓ i.val + ℓ i ≤ totalLength ℓ := by
      rw [← hJPsucc, ← hJPn]
      exact hJPmono (by omega : i.val + 1 ≤ n)
    have h2 : ℓ i / 2 ≤ ℓ i := by linarith [hℓ i]
    linarith

/-- **R-1, SPAN BOUNDS.** The rope's center of mass lies within its span:
`0 ≤ ropeCenter m ℓ ≤ totalLength ℓ`. -/
theorem ropeCenter_bounds {m ℓ : Fin n → ℚ} (hm : ∀ i, 0 < m i)
    (hℓ : ∀ i, 0 < ℓ i) :
    0 ≤ ropeCenter m ℓ ∧ ropeCenter m ℓ ≤ totalLength ℓ := by
  unfold ropeCenter
  apply wCenter_bounds hm
  · intro i; exact (linkMid_mem_span hℓ i).1
  · intro i; exact (linkMid_mem_span hℓ i).2

/-- **R-2, THE UNIFORM ROPE.** Equal masses and equal lengths put the
center at the midpoint of the span: `ropeCenter = totalLength / 2`. -/
theorem ropeCenter_uniform {m ℓ : Fin n → ℚ} {μ lam : ℚ}
    (hm : ∀ i, m i = μ) (hμ : 0 < μ) (hℓ : ∀ i, ℓ i = lam) (hlam : 0 < lam) :
    ropeCenter m ℓ = totalLength ℓ / 2 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, NeZero.pos n⟩⟩
  have hJP : ∀ k : ℕ, k ≤ n → jointPos ℓ k = (k : ℚ) * lam := by
    intro k
    induction k with
    | zero => intro _; simp [jointPos]
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      unfold jointPos
      rw [Finset.sum_range_succ, dif_pos hkn, hℓ ⟨k, hkn⟩]
      have ih' := ih (by omega)
      unfold jointPos at ih'
      rw [ih']
      push_cast
      ring
  have hmid : ∀ i : Fin n, linkMid ℓ i = lam * (2 * (i.val : ℚ) + 1) / 2 := by
    intro i
    unfold linkMid
    rw [hJP i.val (by omega : i.val ≤ n), hℓ i]
    push_cast
    ring
  have hodd : ∀ k : ℕ, ∑ j ∈ Finset.range k, (2 * (j : ℚ) + 1) = (k : ℚ) ^ 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hsum : (∑ i : Fin n, linkMid ℓ i) = lam * (n : ℚ) ^ 2 / 2 := by
    calc (∑ i : Fin n, linkMid ℓ i) = ∑ i : Fin n, (lam * (2 * (i.val : ℚ) + 1) / 2) :=
          Finset.sum_congr rfl (fun i _ => hmid i)
    _ = (lam / 2) * ∑ i : Fin n, (2 * (i.val : ℚ) + 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = (lam / 2) * ∑ j ∈ Finset.range n, (2 * (j : ℚ) + 1) := by
          congr 1
          exact Fin.sum_univ_eq_sum_range (fun j : ℕ => 2 * (j : ℚ) + 1) n
    _ = (lam / 2) * (n : ℚ) ^ 2 := by rw [hodd n]
    _ = lam * (n : ℚ) ^ 2 / 2 := by ring
  have htot : totalLength ℓ = (n : ℚ) * lam := by
    unfold totalLength
    calc (∑ i : Fin n, ℓ i) = ∑ _i : Fin n, lam :=
          Finset.sum_congr rfl (fun i _ => hℓ i)
    _ = (n : ℚ) * lam := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold ropeCenter
  rw [CenterBridgePin.wCenter_const hm hμ, hsum, htot, Fintype.card_fin]
  have hn : (n : ℚ) ≠ 0 := by
    exact_mod_cast (NeZero.pos n).ne'
  field_simp

end ThetLogos.RopePin
