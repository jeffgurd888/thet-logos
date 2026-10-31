import Mathlib.Tactic
import ThetLogos.Q7C4R4Trifecta
import ThetLogos.FiniteEntropy

namespace ThetLogos

/-!
# ThetLogos.Q7C4R4FirstLeg — T-Q7-1: the First-leg capacity test

**Status: TEST EXECUTED — K-T-Q7-1 FIRES at full rank. NO CLAIM.
Dials 0/4. No measured number.** Governing pack:
`routeb-general-scratch/pack-t-q7-1.md`; registration:
`ThetLogos.Q7C4R4Trifecta` (Q7CR-T0); entropy: T-ENT's
`ThetLogos.FiniteEntropy` (`entropyW` only, log base `e` throughout).

## The registered Prop, quoted verbatim

From `ThetLogos.Q7C4R4Trifecta` (definition and its docstring):

```
def LegFirstCapacity (S : (Fin 7 → ℂ) → ℝ) : Prop :=
  ∀ ρ : Fin 7 → ℂ, S ρ ≤ Real.log 7
```

> Registered form: `log 7`, the complex count. The fork is recorded
> here, on the face: `log 14` is the same bound read under the raw
> real dimension of the DQ1-realified factor; T0 registers the
> `log 7` form, and neither reading may be used silently in place
> of the other.

> What is missing: `S` itself, and the state predicate on
> `Fin 7 → ℂ` that the intended quantification runs over — the
> entropy functional is T-ENT's to supply (T-ENT is the tree's
> missing definition; see the header), and the Q⁷ factor's state
> vocabulary comes with it.

Read exactly, the registered quantification is UNRESTRICTED: it
runs over every `ρ : Fin 7 → ℂ`, with no state predicate and no
restriction to complex-respecting states anywhere in the Prop or
its docstring. This brick therefore does not narrow it. T-ENT now
supplies the entropy functional, in weight form (`entropyW`); the
test instantiates `S` by the entropy of the factor's realified
coordinate weights — the weight form on the factor's real index
set `Fin 7 × Fin 2` (the 7 complex dimensions, each a real pair;
cardinality 14, the fork's raw real dimension).

## The deciding computation

- (a) The maximally mixed weight on the real index set
  `Fin 7 × Fin 2` has `entropyW = Real.log 14` (T-ENT saturation,
  `entropyW_uniform_pair` below), and `Real.log 7 < Real.log 14`.
  Hence the capacity statement in weight form over the real index
  set is FALSE (`capacity_weight_form_false`), with the uniform
  weight as exhibited witness.
- (b) The restriction to complex-respecting states does not rescue
  the bound. A complex-respecting weight is one constant on each
  realification pair; the maximally mixed such weight is the
  doubled uniform complex weight, which IS the uniform real
  weight above (`doubledWeight_uniform`), and its entropy is
  exactly `Real.log 7 + Real.log 2 = Real.log 14`
  (`entropyW_doubled_uniform`) — the pair degeneracy contributes
  `log 2` per complex dimension in T-ENT's real weight form, so
  the registered bound `log 7` is exceeded, not saturated.
- The witness is a state inside the registered quantification:
  the vector `ρ₀ = fun _ => 1 + Complex.I` has equal real and
  imaginary parts, so its realified coordinate weight is the
  pair-constant uniform weight, and the T-ENT functional
  `entropyRealified` built from it attains `Real.log 14` there
  (`entropyRealified_witness`). Hence
  `¬ LegFirstCapacity entropyRealified`
  (`legFirstCapacity_realified_false`).

## Verdict

**K-T-Q7-1 FIRES at full rank: the First-leg capacity
identification, at its registered `log 7` form, is FALSE for the
T-ENT entropy on the factor's realified index set — the witness
state's entropy is `log 14 > log 7`.** The registered Prop is not
narrowed here. A different functional — entropy of the pair-total
(complex-count) weights on `Fin 7`, whose maximum is `log 7` —
would survive, but that is a NEW-ENTRY candidate for the parent
to register or refuse; it is not this brick's verdict and nothing
below asserts it as the leg.

The C⁴ leg's strong form stands REFUTED-AS-STATED (T0) —
untouched here, in either direction. The trifecta assignment
itself is Jeff's registered DATA; this brick tests one leg's
stated consequence only.
-/

/-! ## §1. The real index set and its maximally mixed weight -/

/-- Cardinality of the real index set: the 7 complex dimensions,
    each a real pair, give 14 real indices. Tier T1. -/
theorem card_realIndex : Fintype.card (Fin 7 × Fin 2) = 14 := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- The maximally mixed weight on the factor's real index set:
    `1 / 14` at every real index. Tier T1 (definition). -/
noncomputable def uniformRealWeight : Fin 7 × Fin 2 → ℝ := fun _ => 1 / 14

/-- The maximally mixed real weight is a probability weight.
    Tier T1. -/
theorem isProbWeight_uniformRealWeight :
    IsProbWeight uniformRealWeight := by
  constructor
  · intro _
    unfold uniformRealWeight
    norm_num
  · unfold uniformRealWeight
    rw [Finset.sum_const, Finset.card_univ, card_realIndex]
    norm_num

/-- **Test state (a):** the maximally mixed weight on the real
    index set has entropy exactly `log 14` — T-ENT saturation
    (`entropyW_eq_log_card_iff`) at card 14. Tier T1. -/
theorem entropyW_uniformRealWeight :
    entropyW uniformRealWeight = Real.log 14 := by
  have h := (entropyW_eq_log_card_iff
    isProbWeight_uniformRealWeight).mpr (fun _ => by
      rw [card_realIndex]
      rfl)
  rwa [card_realIndex, Nat.cast_ofNat] at h

/-- The fork's two readings are strictly ordered:
    `log 7 < log 14`. Tier T1. -/
theorem log_seven_lt_log_fourteen :
    Real.log 7 < Real.log 14 :=
  Real.log_lt_log (by norm_num) (by norm_num)

/-- **The capacity statement in weight form over the real index
    set is false:** the uniform real weight is a probability
    weight whose entropy `log 14` exceeds the registered capacity
    `log 7`. The witness is exhibited, not merely asserted.
    Tier T1. -/
theorem capacity_weight_form_false :
    ¬ ∀ w : Fin 7 × Fin 2 → ℝ, IsProbWeight w →
      entropyW w ≤ Real.log 7 := by
  intro h
  have hle := h uniformRealWeight isProbWeight_uniformRealWeight
  rw [entropyW_uniformRealWeight] at hle
  exact not_le_of_gt log_seven_lt_log_fourteen hle

/-! ## §2. Complex-respecting (pair-constant) weights: the exact computation -/

/-- A weight on the real index set is **complex-respecting**
    (pair-constant) when it takes the same value on the two real
    members of each complex dimension's realification pair.
    Tier T1 (definition). -/
def PairConstant (w : Fin 7 × Fin 2 → ℝ) : Prop :=
  ∀ i : Fin 7, w (i, 0) = w (i, 1)

/-- The doubled weight of a complex weight `p` on `Fin 7`: each
    complex weight is split evenly over its realification pair.
    This is the general form of a pair-constant weight induced by
    a complex weight. Tier T1 (definition). -/
noncomputable def doubledWeight (p : Fin 7 → ℝ) : Fin 7 × Fin 2 → ℝ :=
  fun q => p q.1 / 2

/-- Every doubled weight is pair-constant. Tier T1. -/
theorem doubledWeight_pairConstant (p : Fin 7 → ℝ) :
    PairConstant (doubledWeight p) := fun _ => rfl

/-- The maximally mixed complex weight on `Fin 7` is a
    probability weight. Tier T1. -/
theorem isProbWeight_uniform_complex :
    IsProbWeight (fun _ : Fin 7 => (1 : ℝ) / 7) := by
  constructor
  · intro _
    norm_num
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num

/-- The maximally mixed complex weight has entropy `log 7`
    (T-ENT saturation at card 7, the complex count). Tier T1. -/
theorem entropyW_uniform_complex :
    entropyW (fun _ : Fin 7 => (1 : ℝ) / 7) = Real.log 7 := by
  have h := (entropyW_eq_log_card_iff
    isProbWeight_uniform_complex).mpr (fun _ => by
      rw [Fintype.card_fin, Nat.cast_ofNat])
  rwa [Fintype.card_fin, Nat.cast_ofNat] at h

/-- **The maximally mixed pair-constant weight IS the maximally
    mixed real weight:** doubling the uniform complex weight
    `1 / 7` gives `1 / 14` at every real index. Tier T1. -/
theorem doubledWeight_uniform :
    doubledWeight (fun _ : Fin 7 => (1 : ℝ) / 7)
      = uniformRealWeight := by
  funext q
  unfold doubledWeight uniformRealWeight
  norm_num

/-- **Test state (b), exact:** the entropy of the maximally mixed
    complex-respecting weight, in T-ENT's real weight form, is
    `log 7 + log 2 = log 14` — the pair degeneracy contributes
    exactly `log 2`, so the registered bound `log 7` is exceeded
    by the restricted quantification too; it is not saturated at
    `log 7`. Tier T1. -/
theorem entropyW_doubled_uniform :
    entropyW (doubledWeight (fun _ : Fin 7 => (1 : ℝ) / 7))
      = Real.log 7 + Real.log 2 := by
  rw [doubledWeight_uniform, entropyW_uniformRealWeight,
    ← Real.log_mul (by norm_num : (7 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num

/-- Even over pair-constant probability weights alone, the
    entropy attains `log 14`: the restricted quantification's
    maximum (by T-ENT's `entropyW_le_log_card` at card 14) is
    `log 14`, attained at the uniform weight, which is
    pair-constant. Tier T1. -/
theorem pairConstant_max_eq_log_fourteen :
    PairConstant uniformRealWeight ∧
      IsProbWeight uniformRealWeight ∧
      entropyW uniformRealWeight = Real.log 14 ∧
      ∀ w : Fin 7 × Fin 2 → ℝ, IsProbWeight w → PairConstant w →
        entropyW w ≤ Real.log 14 := by
  refine ⟨?_, isProbWeight_uniformRealWeight,
    entropyW_uniformRealWeight, ?_⟩
  · intro i
    rfl
  · intro w hw _
    have h := entropyW_le_log_card hw
    rwa [card_realIndex, Nat.cast_ofNat] at h

/-! ## §3. The T-ENT functional on the factor, and the kill -/

/-- The realified coordinate weight of a vector `ρ` on the Q⁷
    factor: at real index `(i, 0)` the squared real part of
    `ρ i`, at `(i, 1)` the squared imaginary part, normalized by
    the total squared norm. Built only from T-ENT-facing real
    weight data. Tier T1 (definition). -/
noncomputable def realCoordWeight (ρ : Fin 7 → ℂ) :
    Fin 7 × Fin 2 → ℝ :=
  fun q => (if q.2 = 0 then (ρ q.1).re ^ 2 else (ρ q.1).im ^ 2) /
    ∑ i, ((ρ i).re ^ 2 + (ρ i).im ^ 2)

/-- **The T-ENT instantiation of the leg's functional `S`:** the
    entropy (T-ENT's `entropyW`, nothing else) of the realified
    coordinate weight. Tier T1 (definition). -/
noncomputable def entropyRealified (ρ : Fin 7 → ℂ) : ℝ :=
  entropyW (realCoordWeight ρ)

/-- The witness vector: constantly `1 + Complex.I`, of equal real
    and imaginary parts — inside the registered quantification,
    which ranges over every `ρ : Fin 7 → ℂ` without restriction.
    Tier T1 (definition). -/
def witnessVec : Fin 7 → ℂ := fun _ => 1 + Complex.I

/-- The witness's total squared norm is `14`: each of the 7
    components contributes `1 ^ 2 + 1 ^ 2 = 2`. Tier T1. -/
theorem witnessVec_norm_sum :
    (∑ i, ((witnessVec i).re ^ 2 + (witnessVec i).im ^ 2)) = 14 := by
  unfold witnessVec
  simp [Finset.sum_const, Finset.card_univ]
  norm_num

/-- The witness's realified coordinate weight is the maximally
    mixed real weight — in particular it is pair-constant, i.e.
    complex-respecting in the sense of §2. Tier T1. -/
theorem realCoordWeight_witness :
    realCoordWeight witnessVec = uniformRealWeight := by
  funext q
  unfold realCoordWeight uniformRealWeight
  rw [witnessVec_norm_sum]
  by_cases h : q.2 = 0 <;> simp only [h, if_true, if_false]
  · unfold witnessVec
    simp
  · unfold witnessVec
    simp

/-- **The witness attains `log 14`:** the T-ENT functional on the
    Q⁷ factor takes the value `Real.log 14` at `witnessVec`.
    Tier T1. -/
theorem entropyRealified_witness :
    entropyRealified witnessVec = Real.log 14 := by
  unfold entropyRealified
  rw [realCoordWeight_witness, entropyW_uniformRealWeight]

/-- **K-T-Q7-1 FIRES.** The registered First-leg capacity Prop,
    instantiated with the T-ENT functional `entropyRealified`,
    is FALSE as registered: `witnessVec` lies inside the
    registered quantification (which is unrestricted) and its
    entropy is `log 14 > log 7`. The capacity identification at
    the registered `log 7` form dies at full rank; the Prop is
    not narrowed here. Tier T1. -/
theorem legFirstCapacity_realified_false :
    ¬ LegFirstCapacity entropyRealified := by
  intro h
  have hle := h witnessVec
  rw [entropyRealified_witness] at hle
  exact not_le_of_gt log_seven_lt_log_fourteen hle

end ThetLogos
