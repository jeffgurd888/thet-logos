import Mathlib.Tactic
import ThetLogos.ReverseNablaEntropyPin

/-!
# ThetLogos.ComposedBalancePin — the composed balance, in finite form

**Lane-grade pin. NO CLAIM. Pre-registered DIAL-INELIGIBLE; dials
0/4 under every outcome. Dial 2 = 0 under every outcome: the
finite balance characterized here is a fixed-point condition on
quantum counts, not a gravity object, not a force, not a
continuum statement. QTST — Zero's filed candidate name for a
continuum string completion — is NOT worn by this pin.**

Commissioned: Zero, 2026-11-21 ~00:58 EST ("Scope the composed
balance after RNE"); fired 2026-11-21 ~10:29 EST. Scope of
record: `composed-balance-scope-2026-11-21.md` (T5 scope).
Working label only — Zero names.

Zero's seeing, verbatim (filed 2026-11-21 00:57 EST): "I was
just thinking if cold collects at the center and heat radiates
outward and everything with mass is radiating energy our
thermal out out must be offset by our thermal collapse".

**Named resonance, header only:** the physics shape of the
seeing is Kelvin–Helmholtz — a star shines (thermal out) by
slow gravitational collapse (thermal collapse) until fusion
takes over the offset. It is named here as resonance and
nowhere else: it is not imported as physics, no gravity object
exists in this pin, and no theorem cites it. (K-BAL-NAME.)

## The composition point, exactly

HB is two seats, not one. HB-1/HB-2 live on the Gibbs seat —
Gibbs states at (β₁, β₂), the exchange equilibration step, the
rest point at shared β₁ = β₂. HB-3 is a separate, discrete
seat: quantum counts, `splitEntropy`, the greedy one-quantum
step. RNE touches only the discrete seat: quantum counts
`c : Fin n → ℕ`, `seatEntropy s c = ∑ i, s (c i)`, and
`RevStep`, the formal reverse of HB-3's greedy step. The two
flows DO share a common seat object there — counts plus the
seat-entropy potential — and on that seat the greedy step and
`RevStep` are the two directions of the same one-quantum
neighbour move, separated only by the sign of the entropy
change in `seatEntropy_moveMass_sub`. This pin composes them
there.

**The Gibbs seat shares no object with RNE.** No reversed
step exists on the Gibbs seat as built, so no composed
balance can be stated there without building the reverse half
first. **K-BAL-GIBBS FIRED AT SCOPING**: the claim "the
composition lives on HB's Gibbs seat — the shared-β rest is
the composed balance" is false as stated of the built corpus;
HB-2's rest is a forward-only rest. The bridge is a priced
follow-on (~6–9 declarations, separate scope, separate fire
word), fenced OUT of this pin — recorded here so the fence is
a priced door, not a silent drop.

## The balance condition, pinned

**Composition means common rest.** The composed system is the
pair of step relations (forward = entropy-strictly-increasing
neighbour move; reverse = `RevStep`). A distribution is
**balanced** when neither tendency can move it:

    `IsBalance s c := IsFwdRest s c ∧ IsRevRest s c`

This is the offset as a CONDITION: a steady state to be
characterized, not a law of the flow. Three fences ride on
the definition:

- **No convergence is claimed.** The pin characterizes the
  rest points of the composed pair. It does not define an
  alternating iteration and proves nothing about convergence
  to a balance.
- **A body can simply radiate and cool.** Balance is a
  property of special states of a (seat, total) pair, and
  Brick 3 shows existence is a capacity condition — at some
  totals no balance exists at all.
- **Neither half's rest is the balance.** HB-3's rest and
  RNE's rest are different conditions; the balance is their
  intersection, strictly stronger than either. Brick 1 fires
  this as a kill on the nearest exhibit (K-BAL-HB3).

## Fences

- Definitions pinned before any verdict was computed; no
  definition in this module was repaired to force or soften
  an answer (the RTE-2 rule).
- `seatEntropy_moveMass_sub`, `revStep_of_marginal`,
  `exhibit_flat_rest_countermodel`, `exhibit_revStep_to_corner`,
  and HB-3's greedy facts are cited, never re-proved
  (K-BAL-DUP).
- The finite balance is never called gravity (K-BAL-NAME);
  Dial 2 = 0 under every outcome.
-/

namespace ThetLogos

-- ============================================================================
-- BAL-0 (composition card). The forward step, the two rests, the balance
-- ============================================================================

/-- **The forward step** (definition, pinned): `c'` follows
`c` by one forward step when one quantum crosses a neighbour
edge — from a seat holding at least one quantum, to a
neighbouring seat — and the total entropy strictly increases.
HB-3's greedy step as a relation on the `Fin n` seat; the
mirror of RNE's `RevStep`, which takes the same move when the
total entropy strictly decreases. -/
def FwdStep (s : ℕ → ℝ) {n : ℕ} (c c' : Fin n → ℕ) : Prop :=
  ∃ i j, Neighbours i j ∧ 1 ≤ c i ∧ c' = moveMass c i j
    ∧ seatEntropy s c < seatEntropy s c'

/-- **A rest point of the forward flow** (definition): a
distribution no forward step leaves — the mirror of
`IsRevRest`. -/
def IsFwdRest (s : ℕ → ℝ) {n : ℕ} (c : Fin n → ℕ) : Prop :=
  ∀ c', ¬ FwdStep s c c'

/-- **The composed balance** (definition, pinned): a
distribution at rest under BOTH tendencies — no forward step
leaves it (the thermal out cannot run) and no reversed step
leaves it (the thermal collapse cannot run). The offset of
Zero's seeing as a condition on a state, not a law of the
flow: no convergence to a balance is claimed anywhere in
this pin. -/
def IsBalance (s : ℕ → ℝ) {n : ℕ} (c : Fin n → ℕ) : Prop :=
  IsFwdRest s c ∧ IsRevRest s c

/-- **Strictly antitone marginals** (definition): the
nondegeneracy hypothesis of the Brick 3 characterization,
stated on the face in HB's manner — each further quantum
carries strictly less entropy than the one before. A seat
whose marginals do not strictly decrease is not fenced out
of Bricks 0–2; it is fenced out of the characterization, by
hypothesis, never silently. -/
def StrictAntiMarginals (s : ℕ → ℝ) : Prop :=
  StrictAnti (margEntropy s)

-- ============================================================================
-- BAL-1 (forward half). The Fin 2 bridge, the forward marginal test,
-- and K-BAL-HB3
-- ============================================================================

/-- **The Fin 2 bridge** (proved): on two seats, `seatEntropy`
IS HB-3's `splitEntropy` at the split given by the first
seat's count. The prose identification of RNE's header,
proved; HB-3's `Fin 2` facts become citable on the RNE seat
through it. -/
theorem seatEntropy_fin_two (s : ℕ → ℝ) (c : Fin 2 → ℕ) :
    seatEntropy s c = splitEntropy s (c 0 + c 1) (c 0) := by
  unfold seatEntropy splitEntropy
  rw [Fin.sum_univ_two, Nat.add_sub_cancel_left]

/-- **The forward step, by its marginals** (proved): a move
from `i` to a neighbour `j` IS a forward step exactly when it
climbs — when the giving seat's last quantum carries less
entropy than the receiving seat's next quantum gains,
`margEntropy s (c i - 1) < margEntropy s (c j)`. The mirror of
`revStep_of_marginal`: HB-3's greedy condition, stated as a
step relation on the `Fin n` seat. -/
theorem fwdStep_of_marginal (s : ℕ → ℝ) {n : ℕ} (c : Fin n → ℕ)
    (i j : Fin n) (hadj : Neighbours i j) (hi : 1 ≤ c i)
    (hmarg : margEntropy s (c i - 1) < margEntropy s (c j)) :
    FwdStep s c (moveMass c i j) := by
  refine ⟨i, j, hadj, hi, rfl, ?_⟩
  have h := seatEntropy_moveMass_sub s c i j hadj hi
  linarith

/-- **K-BAL-HB3 FIRES** (proved — the pre-registered kill):
HB-3's balanced split `![1, 1]` is NOT the composed balance.
It rests under the forward half — no forward step leaves it —
and collapses under the reverse half: the reversed step
`![1, 1] → ![0, 2]` is legal (the receiving seat's next
quantum gains `log (3/2)`, the giving seat's last quantum
carries `log 2`, and `log (3/2) < log 2`). The forward rest
and the reverse rest are different conditions; any text
calling HB-3's split "the balance" of the composed system is
false by this exhibit. Neither half's rest is the balance. -/
theorem exhibit_balanced_split_not_balance :
    IsFwdRest hbExhibitEntropy ![1, 1]
    ∧ RevStep hbExhibitEntropy ![1, 1] ![0, 2]
    ∧ ¬ IsBalance hbExhibitEntropy ![1, 1] := by
  obtain ⟨hm0, hm1⟩ := exhibit_marginals
  obtain ⟨-, -, -, hlog⟩ := exhibit_entropy_values
  have h10 : (![1, 1] : Fin 2 → ℕ) 0 = 1 := by norm_num
  have h11 : (![1, 1] : Fin 2 → ℕ) 1 = 1 := by norm_num
  have hrev : RevStep hbExhibitEntropy ![1, 1] ![0, 2] := by
    have hmove : moveMass ![1, 1] 0 1 = ![0, 2] := by
      funext k
      fin_cases k <;> simp [moveMass]
    have hmarg : margEntropy hbExhibitEntropy ((![1, 1] : Fin 2 → ℕ) 1)
        < margEntropy hbExhibitEntropy ((![1, 1] : Fin 2 → ℕ) 0 - 1) := by
      rw [h10, h11]
      show margEntropy hbExhibitEntropy 1
        < margEntropy hbExhibitEntropy 0
      rw [hm1, hm0]
      linarith
    have hstep := revStep_of_marginal hbExhibitEntropy ![1, 1] 0 1
      (Or.inl rfl) (by rw [h10]) hmarg
    rwa [hmove] at hstep
  refine ⟨?_, hrev, ?_⟩
  · intro c' hstep
    obtain ⟨i, j, hadj, hi, rfl, hlt⟩ := hstep
    have hdiff := seatEntropy_moveMass_sub hbExhibitEntropy
      ![1, 1] i j hadj hi
    have hgt : margEntropy hbExhibitEntropy ((![1, 1] : Fin 2 → ℕ) i - 1)
        < margEntropy hbExhibitEntropy ((![1, 1] : Fin 2 → ℕ) j) := by
      linarith
    fin_cases i <;> fin_cases j <;>
      norm_num [Neighbours] at hadj <;>
      norm_num at hgt <;>
      rw [hm0, hm1] at hgt <;>
      linarith
  · rintro ⟨-, hrevrest⟩
    exact hrevrest _ hrev

-- ============================================================================
-- BAL-2 (flat-seat exhibits). The balance exists, centre empty;
-- K-BAL-CENTER fires
-- ============================================================================

/-- **The composed balance exists on the flat seat — with the
centre EMPTY** (proved, exhibit): `![1, 0, 1]` on `Fin 3`
under `s₀` is a balance of the composed system. The reverse
half is RNE's countermodel (`exhibit_flat_rest_countermodel`:
it is a rest point of the reversed flow), cited, not
re-proved. The forward half is proved here: every legal
forward move carries a lone corner quantum onto the empty
centre and is entropy-neutral (ΔS = marg s₀ 0 − marg s₀ 0 =
0), so no strictly increasing move exists. The balance claim
does not have to move to a landscaped seat — what the flat
exhibits kill is the CENTRE reading of the balance
(K-BAL-CENTER, next exhibits), not balance itself. -/
theorem exhibit_balance_flat :
    IsBalance hbExhibitEntropy ![1, 0, 1] := by
  refine ⟨?_, exhibit_flat_rest_countermodel.2.2.2⟩
  intro c' hstep
  obtain ⟨i, j, hadj, hi, rfl, hlt⟩ := hstep
  have hdiff := seatEntropy_moveMass_sub hbExhibitEntropy
    ![1, 0, 1] i j hadj hi
  fin_cases i <;> fin_cases j <;>
    norm_num [Neighbours] at hadj <;>
    norm_num at hi <;>
    norm_num at hdiff <;>
    norm_num at hlt <;>
    linarith

/-- **No delta is a balance — K-BAL-CENTER FIRES** (proved,
exhibits): the corner delta `![2, 0, 0]` and the centre delta
`![0, 2, 0]` each admit a forward step (the loaded seat's
second quantum carries `log (3/2)`; the empty neighbour's
first would gain `log 2`), so neither is forward-rest, hence
neither is a balance. Together with `exhibit_balance_flat` —
the total-2 balance has the centre EMPTY — and Brick 3b's
classification (at total 1 the centre singleton balances but
so do both corner singletons), the scoped claim "the composed
balance on the flat seat is a centre configuration" is FALSE:
composing the forward flow with the reversed flow does not
make a centre either. This is K-RNE-FLAT's verdict inherited
by the composition. -/
theorem exhibit_deltas_not_balance :
    ¬ IsBalance hbExhibitEntropy ![2, 0, 0]
    ∧ ¬ IsBalance hbExhibitEntropy ![0, 2, 0] := by
  obtain ⟨hm0, hm1⟩ := exhibit_marginals
  obtain ⟨-, -, -, hlog⟩ := exhibit_entropy_values
  constructor
  · rintro ⟨hfwd, -⟩
    have h20 : (![2, 0, 0] : Fin 3 → ℕ) 0 = 2 := by norm_num
    have h21 : (![2, 0, 0] : Fin 3 → ℕ) 1 = 0 := by norm_num
    have hmarg : margEntropy hbExhibitEntropy ((![2, 0, 0] : Fin 3 → ℕ) 0 - 1)
        < margEntropy hbExhibitEntropy ((![2, 0, 0] : Fin 3 → ℕ) 1) := by
      rw [h20, h21]
      show margEntropy hbExhibitEntropy 1
        < margEntropy hbExhibitEntropy 0
      rw [hm1, hm0]
      linarith
    exact hfwd _ (fwdStep_of_marginal hbExhibitEntropy ![2, 0, 0] 0 1
      (Or.inl rfl) (by norm_num [h20]) hmarg)
  · rintro ⟨hfwd, -⟩
    have h10 : (![0, 2, 0] : Fin 3 → ℕ) 0 = 0 := by norm_num
    have h11 : (![0, 2, 0] : Fin 3 → ℕ) 1 = 2 := by norm_num
    have hmarg : margEntropy hbExhibitEntropy ((![0, 2, 0] : Fin 3 → ℕ) 1 - 1)
        < margEntropy hbExhibitEntropy ((![0, 2, 0] : Fin 3 → ℕ) 0) := by
      rw [h10, h11]
      show margEntropy hbExhibitEntropy 1
        < margEntropy hbExhibitEntropy 0
      rw [hm1, hm0]
      linarith
    exact hfwd _ (fwdStep_of_marginal hbExhibitEntropy ![0, 2, 0] 1 0
      (Or.inr rfl) (by norm_num [h11]) hmarg)

/-- **The pure spread is not a balance** (proved, exhibit):
the uniform distribution `![1, 1, 1]` admits a reversed step
(any seat's quantum descends onto a neighbour: the receiving
seat's next quantum gains `log (3/2)`, the giving seat's last
carries `log 2`), so it is not reverse-rest, hence not a
balance. Radiation alone is not balance, exactly as collapse
alone is not (the deltas, above). The offset is genuinely
two-sided or it is nothing. -/
theorem exhibit_uniform_not_balance :
    ¬ IsBalance hbExhibitEntropy ![1, 1, 1] := by
  obtain ⟨hm0, hm1⟩ := exhibit_marginals
  obtain ⟨-, -, -, hlog⟩ := exhibit_entropy_values
  rintro ⟨-, hrev⟩
  have h10 : (![1, 1, 1] : Fin 3 → ℕ) 0 = 1 := by norm_num
  have h11 : (![1, 1, 1] : Fin 3 → ℕ) 1 = 1 := by norm_num
  have hmarg : margEntropy hbExhibitEntropy ((![1, 1, 1] : Fin 3 → ℕ) 1)
      < margEntropy hbExhibitEntropy ((![1, 1, 1] : Fin 3 → ℕ) 0 - 1) := by
    rw [h10, h11]
    show margEntropy hbExhibitEntropy 1
      < margEntropy hbExhibitEntropy 0
    rw [hm1, hm0]
    linarith
  exact hrev _ (revStep_of_marginal hbExhibitEntropy ![1, 1, 1] 0 1
    (Or.inl rfl) (by rw [h10]) hmarg)

/-- **Adjacent loading is not balance** (proved, exhibit):
`![1, 1, 0]` is not a balance — its reverse half already
fails in-tree: `exhibit_revStep_to_corner` is a legal
reversed step out of it (the centre seat's quantum empties
into the corner delta), cited here, not re-proved
(K-BAL-DUP). The composed statement is new; the step is
RNE's. -/
theorem exhibit_adjacent_not_balance :
    ¬ IsBalance hbExhibitEntropy ![1, 1, 0] := by
  rintro ⟨-, hrev⟩
  exact hrev _ exhibit_revStep_to_corner

-- ============================================================================
-- BAL-3a (the characterization). Balance = isolated single quanta;
-- the capacity bound
-- ============================================================================

/-- **The characterization of the composed balance** (proved,
general seat): under strictly antitone marginals, on a seat
with at least two seats, a distribution is balanced if and
only if every seat holds at most one quantum and no two
neighbouring seats are both occupied — isolated single
quanta. Forward: a seat holding ≥ 2 always admits a move
(forward to a lighter neighbour, or a reversed step across
the edge, by the neighbour's count), and two occupied
neighbours admit a reversed step from the lighter side or a
forward step off the heavier. Backward: from an isolated
single, every legal move is entropy-neutral on the nose
(ΔS = marg s 0 − marg s 0 in the marginal comparison), so
neither step relation can leave it. The `Fin 1` seat is
degenerate (no edges, everything rests) and is excluded by
the `2 ≤ n` hypothesis, stated on the face. -/
theorem isBalance_iff (s : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n)
    (hs : StrictAntiMarginals s) (c : Fin n → ℕ) :
    IsBalance s c ↔ (∀ i, c i ≤ 1) ∧
      (∀ i j, Neighbours i j → c i + c j ≤ 1) := by
  have hs' : StrictAnti (margEntropy s) := hs
  have hmarg_lt : ∀ a b : ℕ,
      margEntropy s a < margEntropy s b ↔ b < a := by
    intro a b
    constructor
    · intro h
      by_contra hb
      push Not at hb
      rcases eq_or_lt_of_le hb with he | hl
      · subst he
        exact lt_irrefl _ h
      · have h2 := hs' hl
        linarith
    · intro h
      exact hs' h
  have hsymm : ∀ i j : Fin n, Neighbours i j → Neighbours j i := by
    intro i j h
    exact h.symm
  have hneigh : ∀ i : Fin n, ∃ j, Neighbours i j := by
    intro i
    by_cases h : i.val + 1 < n
    · exact ⟨⟨i.val + 1, h⟩, Or.inl rfl⟩
    · have hi1 : 1 ≤ i.val := by
        have hlt := i.isLt
        omega
      refine ⟨⟨i.val - 1, by omega⟩, Or.inr ?_⟩
      show (i.val - 1) + 1 = i.val
      omega
  have pair : ∀ i j : Fin n, Neighbours i j → 1 ≤ c i → 1 ≤ c j →
      (∃ c', FwdStep s c c') ∨ (∃ c', RevStep s c c') := by
    intro i j hadj hi hj
    by_cases hle : c i ≤ c j
    · right
      exact ⟨_, revStep_of_marginal s c i j hadj hi
        ((hmarg_lt (c j) (c i - 1)).mpr (by omega))⟩
    · by_cases h2 : c j + 1 = c i
      · right
        exact ⟨_, revStep_of_marginal s c j i (hsymm i j hadj) hj
          ((hmarg_lt (c i) (c j - 1)).mpr (by omega))⟩
      · left
        exact ⟨_, fwdStep_of_marginal s c i j hadj hi
          ((hmarg_lt (c i - 1) (c j)).mpr (by omega))⟩
  constructor
  · intro hbal
    obtain ⟨hfwd, hrev⟩ := hbal
    have hle1 : ∀ i, c i ≤ 1 := by
      intro i
      by_contra hi
      push Not at hi
      obtain ⟨j, hadj⟩ := hneigh i
      by_cases hj : c j = 0
      · exact hfwd _ (fwdStep_of_marginal s c i j hadj (by omega)
          ((hmarg_lt (c i - 1) (c j)).mpr (by omega)))
      · have hj1 : 1 ≤ c j := by omega
        rcases pair i j hadj (by omega) hj1 with ⟨c', hstep⟩ | ⟨c', hstep⟩
        · exact hfwd c' hstep
        · exact hrev c' hstep
    refine ⟨hle1, ?_⟩
    intro i j hadj
    by_contra hsum
    push Not at hsum
    have hi : 1 ≤ c i := by
      have h1 := hle1 i
      have h2 := hle1 j
      omega
    have hj : 1 ≤ c j := by
      have h1 := hle1 i
      have h2 := hle1 j
      omega
    rcases pair i j hadj hi hj with ⟨c', hstep⟩ | ⟨c', hstep⟩
    · exact hfwd c' hstep
    · exact hrev c' hstep
  · rintro ⟨hc1, hc2⟩
    constructor
    · intro c' hstep
      obtain ⟨i, j, hadj, hi, rfl, hlt⟩ := hstep
      have hdiff := seatEntropy_moveMass_sub s c i j hadj hi
      have hgt : margEntropy s (c i - 1) < margEntropy s (c j) := by
        linarith
      have hlt2 : c j < c i - 1 := (hmarg_lt (c i - 1) (c j)).mp hgt
      have hle := hc1 i
      omega
    · intro c' hstep
      obtain ⟨i, j, hadj, hi, rfl, hlt⟩ := hstep
      have hdiff := seatEntropy_moveMass_sub s c i j hadj hi
      have hlt2 : c i - 1 < c j :=
        (hmarg_lt (c j) (c i - 1)).mp (by linarith)
      have h2 := hc2 i j hadj
      omega

/-- **The capacity bound** (proved): a balance has total at
most `⌈n/2⌉` — here `(n + 1) / 2` in natural division. The
pairing bound: seats (0,1), (2,3), … each contribute at most
one quantum between them (neighbours, by the
characterization), and a final unpaired seat contributes at
most one. Existence of a balance is therefore a capacity
condition on (seat, total), not a law — Brick 3b fires
K-BAL-ALWAYS on the first total that exceeds it. -/
theorem balance_sum_le (s : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n)
    (hs : StrictAntiMarginals s) (c : Fin n → ℕ)
    (hbal : IsBalance s c) :
    ∑ i, c i ≤ (n + 1) / 2 := by
  obtain ⟨hc1, hc2⟩ := (isBalance_iff s hn hs c).mp hbal
  have key : ∀ (m : ℕ) (f : ℕ → ℕ), (∀ i, i < m → f i ≤ 1) →
      (∀ i, i + 1 < m → f i + f (i + 1) ≤ 1) →
      ∑ i ∈ Finset.range m, f i ≤ (m + 1) / 2 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro f hf1 hf2
      rcases (by omega : m = 0 ∨ m = 1 ∨ 2 ≤ m) with rfl | rfl | hm
      · simp
      · rw [Finset.sum_range_one]
        have h0 := hf1 0 (by norm_num)
        omega
      · have hpeel : ∑ i ∈ Finset.range m, f i
            = ∑ i ∈ Finset.range (m - 2), f i
              + (f (m - 2) + f (m - 1)) := by
          conv_lhs => rw [show m = (m - 2) + 2 by omega,
            Finset.sum_range_succ, Finset.sum_range_succ,
            show m - 2 + 1 = m - 1 by omega]
          ring
        rw [hpeel]
        have hIH := ih (m - 2) (by omega) f
          (fun i hi => hf1 i (by omega)) (fun i hi => hf2 i (by omega))
        have hpair := hf2 (m - 2) (by omega)
        have e3 : m - 2 + 1 = m - 1 := by omega
        rw [e3] at hpair
        omega
  have hsum : (∑ i, c i)
      = ∑ i ∈ Finset.range n,
        (fun k => if h : k < n then c ⟨k, h⟩ else 0) i := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => if h : k < n then c ⟨k, h⟩ else 0) n]
    apply Finset.sum_congr rfl
    intro i _
    simp only [dif_pos i.isLt, Fin.eta]
  rw [hsum]
  apply key n
  · intro i hi
    show (if h : i < n then c ⟨i, h⟩ else 0) ≤ 1
    rw [dif_pos hi]
    exact hc1 _
  · intro i hi
    have hi' : i < n := by omega
    show (if h : i < n then c ⟨i, h⟩ else 0)
      + (if h : i + 1 < n then c ⟨i + 1, h⟩ else 0) ≤ 1
    rw [dif_pos hi', dif_pos hi]
    exact hc2 ⟨i, hi'⟩ ⟨i + 1, hi⟩ (Or.inl rfl)

-- ============================================================================
-- BAL-3b (existence on the exhibit seat). The Fin 3 classification;
-- K-BAL-ALWAYS fires
-- ============================================================================

/-- **The exhibit's marginals strictly decrease** (proved):
`s₀ = log (· + 1)` has strictly antitone marginals —
`margEntropy s₀ k = log ((k+2)/(k+1)) = log (1 + 1/(k+1))`,
and `(k+2)/(k+1)` strictly decreases in `k`, so `Real.log`'s
strict monotonicity carries the antitonicity. This is the
priced heavy lemma of the brick: it seats the exhibit under
Brick 3a's characterization. (The ill-posed pin's Brick 2
needs the same fact; it will cite this one.) -/
theorem margEntropy_hbExhibit_strictAnti :
    StrictAntiMarginals hbExhibitEntropy := by
  have hval : ∀ k : ℕ, margEntropy hbExhibitEntropy k
      = Real.log ((k + 2 : ℝ) / (k + 1 : ℝ)) := by
    intro k
    have e1 : ((k + 1 + 1 : ℕ) : ℝ) = (k : ℝ) + 2 := by
      push_cast
      ring
    have e2 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by
      push_cast
      ring
    unfold margEntropy hbExhibitEntropy
    rw [e1, e2, ← Real.log_div (by positivity) (by positivity)]
  intro a b hab
  rw [hval b, hval a]
  apply Real.log_lt_log (by positivity)
  have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hpos1 : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hpos2 : (0 : ℝ) < (b : ℝ) + 1 := by positivity
  rw [div_lt_iff₀ hpos2, div_mul_eq_mul_div, lt_div_iff₀ hpos1]
  nlinarith [hab']

/-- **The Fin 3 classification at total 2** (proved,
corollary of Brick 3a): every total-2 balance on `Fin 3`
under `s₀` is `![1, 0, 1]` — the centre-empty configuration
of Brick 2 is the UNIQUE balance at that total. At total 1
the three singletons all balance (the centre singleton among
equals — no centre privilege, K-BAL-CENTER's third leg, by
the same characterization); at total 3 there is none
(next theorem). -/
theorem exhibit_fin3_balance_unique_total_two (c : Fin 3 → ℕ)
    (hbal : IsBalance hbExhibitEntropy c) (htot : ∑ i, c i = 2) :
    c = ![1, 0, 1] := by
  obtain ⟨hc1, hc2⟩ := (isBalance_iff hbExhibitEntropy (by norm_num)
    margEntropy_hbExhibit_strictAnti c).mp hbal
  rw [Fin.sum_univ_three] at htot
  have h01 := hc2 0 1 (Or.inl rfl)
  have h12 := hc2 1 2 (Or.inl rfl)
  have h0 : c 0 = 1 := by
    have a := hc1 0
    have b := hc1 1
    have d := hc1 2
    omega
  have h1 : c 1 = 0 := by
    have a := hc1 0
    have b := hc1 1
    have d := hc1 2
    omega
  have h2 : c 2 = 1 := by
    have a := hc1 0
    have b := hc1 1
    have d := hc1 2
    omega
  have hpt : ∀ i, c i = ![1, 0, 1] i := by
    intro i
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2
  exact funext hpt

/-- **K-BAL-ALWAYS FIRES** (proved — the pre-registered
kill): at total 3 on `Fin 3` under `s₀`, NO distribution is
a balance — the composed system has no rest point at all
there. Corollary of the capacity bound: a balance has total
≤ ⌈3/2⌉ = 2 < 3. The scoped claim "a composed balance always
exists — the thermal out is always offset" is FALSE in
general: existence is the capacity condition K ≤ ⌈n/2⌉ on
(seat, total), never a law. A body can simply radiate and
cool, and the finite seat says exactly when it must. -/
theorem exhibit_fin3_no_balance_total_three (c : Fin 3 → ℕ)
    (htot : ∑ i, c i = 3) : ¬ IsBalance hbExhibitEntropy c := by
  intro hbal
  have hle := balance_sum_le hbExhibitEntropy (by norm_num)
    margEntropy_hbExhibit_strictAnti c hbal
  omega

end ThetLogos
