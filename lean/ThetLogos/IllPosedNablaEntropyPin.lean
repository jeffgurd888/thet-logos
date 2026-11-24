import Mathlib.Tactic
import ThetLogos.ReverseNablaEntropyPin
import ThetLogos.ComposedBalancePin

/-!
# ThetLogos.IllPosedNablaEntropyPin — ill-posed nabla entropy, in finite form

**Lane-grade pin. NO CLAIM. Pre-registered DIAL-INELIGIBLE; dials
0/4 under every outcome. Dial 2 = 0 under every outcome: finite
ill-posedness at a quantum-count seat is a statement about a step
relation's rest sets and its inverse problem — not a PDE theorem,
not a gravity object, not a continuum statement of any kind. QTST
— Zero's filed candidate name for a continuum string completion —
is NOT worn by this pin.**

Commissioned: Zero, 2026-11-21 04:01 EST ("Scope it standalone,
after RNE lands"), from his seeing filed verbatim 2026-11-21
03:59 EST: "if everything is over thermal entropy of time then
our lowest common denominator is heat. what is the shape of
Il-posed nabla entropy? it is without action just static
equilibrium" — "Il-posed" reads as ILL-POSED (speech-to-text).
His verdict-form, carried on this pin's face: the ill-posed
nabla entropy is WITHOUT ACTION, just STATIC EQUILIBRIUM — the
equilibrium as its own reverse, a fixed point. Scope of record:
`ill-posed-nabla-entropy-scope-2026-11-21.md` (T5 scope).
Working label only — Zero names.

## The finite content of "ill-posed" at these seats

Hadamard's three conditions, mapped to finite forms. The map is
a naming of finite analogues, labeled as such (K-IPNE-CONT:
no backward heat equation, no PDE, no continuum ill-posedness
is stated or claimed anywhere in this pin; the theorems are
about `Fin n` quantum counts and nothing else):

- **Existence — the static-equilibrium shape.** A state is a
  static equilibrium in Zero's sense iff NEITHER direction can
  move it: rest for the forward step and rest for the reverse
  step. On the flat seat that is the composed-balance pin's
  `IsBalance` — CITED, never restated (see the ownership line
  below). On a LANDSCAPED seat nobody owned it; Brick 0 defines
  it (`IsLandBalance`) and Brick 1 computes its verdict at the
  exhibits. **K-IPNE-EQUIL is pre-registered** on the claim
  "a landscaped seat has a static equilibrium at the exhibits":
  expected to FIRE — at total 2 on `Fin 3` the landscaped
  balance set is empty on the graded seat and on the bowl.
- **Uniqueness — the reverse problem has no unique answer.**
  Brick 2 counts the reverse-rest set at the flat exhibit
  exactly (fourfold at total 2); Brick 3 exhibits the failure
  in both directions — one state with two reverse futures, one
  rest with two one-step pasts. **K-IPNE-UNIQ is
  pre-registered**: expected to FIRE (Brick 3). The reversed
  step is a relation, not a function, in either direction.
- **Stability — the rest set is discontinuous in the
  landscape. DISCHARGED BY CITATION, not re-proved:**
  `![1, 0, 1]` is a rest on the flat seat
  (`exhibit_flat_rest_countermodel`) and is NOT a rest under
  the bowl landscape (`exhibit_bowl_undeadlocks`) — the
  minimal nonzero landscape destroys it. The rest set does
  not depend continuously on the data. No brick re-proves
  this face.

## "Without action" — the fence, named (K-IPNE-ACTION)

Zero's phrase is a fence, and this pin states what it fences
out. The corpus HAS an action seat — `SpectralAction.lean`
(T5 scaffolding; the expansion carried as a stated axiom) and
`SpectralActionA2.lean` (the a₂ coefficient, registered
imported, not derived). This pin touches NEITHER, imports
NEITHER, and defines NO action functional of any kind: no
trace formula, no Lagrangian, no variational principle. Its
equilibrium is defined purely by the step relations — a state
rests because no step leaves it, never because it stations an
action. Any later text calling this pin's rest sets a
least-action or stationarity result is false by the pin's own
definitions.

## Ownership (K-IPNE-DUP — fence)

- RNE's rests, steps, and bookkeeping (`RevStep`, `IsRevRest`,
  `LandRevStep`, `IsLandRevRest`, `seatEntropy_moveMass_sub`,
  `landEntropy_moveMass_sub`, `revStep_of_marginal`,
  `landRevStep_of_marginal`) are CITED, never re-proved.
- The flat-seat both-directions rest is the composed-balance
  pin's `IsBalance`, and its characterization (isolated single
  quanta; capacity `K ≤ ⌈n/2⌉`) belongs to that pin — cited,
  never restated, never re-proved here.
- The shared s₀ lemma `margEntropy_hbExhibit_strictAnti` was
  priced for whichever of the two pins fired first; the
  composed-balance pin fired first and proved it (its Brick
  3b). This pin CITES it (Brick 2) and does not re-prove it.

## The collapse clause (K-IPNE-RENAME — armed at drafting)

If any brick's content collapses to a restatement of RNE rests
or of the composed-balance pin's `IsBalance`, that brick does
not bank; if the whole pin collapses, it ships as Brick 0's
registration card alone and reports itself a card. Scoping
verdict: the landscaped balance (Bricks 0–1), the reverse-rest
characterization (Brick 2), and the inverse-problem exhibits
(Brick 3) are owned by no existing pin. The fence stays armed
because the margin is honest: this is a small pin standing
between two larger ones.

## Fences

- Definitions pinned before any verdict was computed; no
  definition in this module will be repaired to force or
  soften an answer (the RTE-2 rule).
- The steps are defined finite operations on quantum counts;
  no continuum limit, no physical time, no force law, no
  dynamics beyond the step relations is claimed.
-/

namespace ThetLogos

-- ============================================================================
-- IPNE-0 (the ill-posedness card). The landscaped forward pair and the
-- landscaped static equilibrium
-- ============================================================================

/-- **The landscaped forward step** (definition, pinned): one
quantum crosses a neighbour edge — from a seat holding at least
one quantum, to a neighbouring seat — and the LANDSCAPED
entropy strictly INCREASES. The mirror of RNE's `LandRevStep`,
which takes the same one-quantum neighbour move when the
landscaped entropy strictly decreases: the two directions of
one move on the landscaped seat, separated only by the sign of
the change in `landEntropy_moveMass_sub`. -/
def LandFwdStep (s : ℕ → ℝ) {n : ℕ} (ℓ : Fin n → ℝ) (c c' : Fin n → ℕ) :
    Prop :=
  ∃ i j, Neighbours i j ∧ 1 ≤ c i ∧ c' = moveMass c i j
    ∧ landEntropy s ℓ c < landEntropy s ℓ c'

/-- **A rest point of the landscaped forward flow**
(definition): a distribution no landscaped forward step
leaves. -/
def IsLandFwdRest (s : ℕ → ℝ) {n : ℕ} (ℓ : Fin n → ℝ) (c : Fin n → ℕ) :
    Prop :=
  ∀ c', ¬ LandFwdStep s ℓ c c'

/-- **A landscaped static equilibrium** (definition, pinned):
rest for the landscaped forward step AND rest for the
landscaped reversed step — the state fixed by both directions,
Zero's shape ("without action, just static equilibrium")
seated where a landscape acts. The landscaped mirror of the
composed-balance pin's flat-seat `IsBalance`, which is cited,
never restated: on the flat seat (`ℓ ≡ 0`) the two conditions
are that pin's `IsFwdRest`/`IsRevRest` pair; here the landscape
is part of the seat. -/
def IsLandBalance (s : ℕ → ℝ) {n : ℕ} (ℓ : Fin n → ℝ) (c : Fin n → ℕ) :
    Prop :=
  IsLandFwdRest s ℓ c ∧ IsLandRevRest s ℓ c

-- ============================================================================
-- IPNE-1 (the verdict brick). The landscaped equilibrium is empty at the
-- exhibits — K-IPNE-EQUIL fires, on both landscapes
-- ============================================================================

/-- **A static equilibrium can only be left by neutral moves**
(proved): if `c` is a landscaped balance and `c'` is one
neighbour move from `c`, the move is landscaped-entropy
NEUTRAL — `landEntropy s ℓ c' = landEntropy s ℓ c`. Route:
trichotomy on the sign of the change: strictly negative is a
landscaped reversed step (fenced by the `IsLandRevRest` half),
strictly positive is a landscaped forward step (fenced by the
`IsLandFwdRest` half). The general lemma of the pin: a
both-directions rest admits no strictly-signed move at all.
On the exhibit seats below, every total-2 distribution has a
strictly-signed move, which is what empties the landscaped
balance set there. -/
theorem landBalance_move_neutral (s : ℕ → ℝ) {n : ℕ} (ℓ : Fin n → ℝ)
    (c : Fin n → ℕ) (hbal : IsLandBalance s ℓ c)
    (i j : Fin n) (hadj : Neighbours i j) (hi : 1 ≤ c i) :
    landEntropy s ℓ (moveMass c i j) = landEntropy s ℓ c := by
  rcases lt_trichotomy (landEntropy s ℓ (moveMass c i j))
      (landEntropy s ℓ c) with h | h | h
  · exfalso
    exact hbal.2 _ ⟨i, j, hadj, hi, rfl, h⟩
  · exact h
  · exfalso
    exact hbal.1 _ ⟨i, j, hadj, hi, rfl, h⟩

/-- **K-IPNE-EQUIL FIRES — the graded seat** (proved, exhibit):
at total 2 on `Fin 3`, NO distribution is a landscaped balance
on RTE's graded landscape `exhibitPhi = ![0, 0, 1]`. Checked
distribution by distribution through the neutrality lemma:
each of the six admits a strictly-signed move — the corner
delta `![2, 0, 0]` and the centre delta `![0, 2, 0]` (both
reverse rests on this seat, by RNE) each admit the forward
move toward the other minimum seat, of signed change
`2 log 2 − log 3 > 0`; the far corner delta sheds toward the
centre at `2 log 2 − log 3 − 1 < 0`; the split `![1, 0, 1]`
drops its high corner into the centre at `−1`; the remaining
splits carry the anti-diffusion sign `log 3 − 2 log 2` (with
`−1` more where the high seat is involved). Zero's shape —
the equilibrium as its own reverse — has NO instance where
this landscape acts, at the exhibit total. -/
theorem exhibit_graded_no_land_balance (c : Fin 3 → ℕ)
    (hsum : ∑ i, c i = 2) :
    ¬ IsLandBalance hbExhibitEntropy exhibitPhi c := by
  intro hbal
  obtain ⟨hm0, hm1⟩ := exhibit_marginals
  have h32 : Real.log 3 < 2 * Real.log 2 := exhibit_entropy_values.2.2.2
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt1 : Real.log 2 < 1 :=
    lt_trans Real.log_two_lt_d9 (by norm_num)
  have hlog23 : Real.log 2 < Real.log 3 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hsum3 : c 0 + c 1 + c 2 = 2 := by
    rw [← Fin.sum_univ_three]
    exact hsum
  have h0le : c 0 ≤ 2 := by omega
  have h1le : c 1 ≤ 2 := by omega
  have h2le : c 2 ≤ 2 := by omega
  have hp0 : exhibitPhi 0 = 0 := by norm_num [exhibitPhi]
  have hp1 : exhibitPhi 1 = 0 := by norm_num [exhibitPhi]
  have hp2 : exhibitPhi 2 = 1 := by norm_num [exhibitPhi]
  interval_cases h0 : c 0 <;> interval_cases h1 : c 1 <;>
    interval_cases h2 : c 2 <;> try omega
  · -- (0, 0, 2): the far corner sheds toward the centre, Δ = 2 log 2 − log 3 − 1 < 0
    have hne := landBalance_move_neutral hbExhibitEntropy exhibitPhi c
      hbal 2 1 (Or.inr rfl) (by omega)
    have hdiff := landEntropy_moveMass_sub hbExhibitEntropy exhibitPhi c
      2 1 (Or.inr rfl) (by omega)
    have hΔ : landEntropy hbExhibitEntropy exhibitPhi (moveMass c 2 1)
        - landEntropy hbExhibitEntropy exhibitPhi c
        = 2 * Real.log 2 - Real.log 3 - 1 := by
      rw [hdiff, h1, h2, hp1, hp2]
      show (margEntropy hbExhibitEntropy 0 + 0)
          - (margEntropy hbExhibitEntropy 1 + 1)
          = 2 * Real.log 2 - Real.log 3 - 1
      rw [hm0, hm1]
      ring
    linarith
  · -- (0, 1, 1): the high corner drops into the centre, Δ = log 3 − 2 log 2 − 1 < 0
    have hne := landBalance_move_neutral hbExhibitEntropy exhibitPhi c
      hbal 2 1 (Or.inr rfl) (by omega)
    have hdiff := landEntropy_moveMass_sub hbExhibitEntropy exhibitPhi c
      2 1 (Or.inr rfl) (by omega)
    have hΔ : landEntropy hbExhibitEntropy exhibitPhi (moveMass c 2 1)
        - landEntropy hbExhibitEntropy exhibitPhi c
        = Real.log 3 - 2 * Real.log 2 - 1 := by
      rw [hdiff, h1, h2, hp1, hp2]
      show (margEntropy hbExhibitEntropy 1 + 0)
          - (margEntropy hbExhibitEntropy 0 + 1)
          = Real.log 3 - 2 * Real.log 2 - 1
      rw [hm0, hm1]
      ring
    linarith
  · -- (0, 2, 0): the centre delta steps forward to the corner, Δ = 2 log 2 − log 3 > 0
    have hne := landBalance_move_neutral hbExhibitEntropy exhibitPhi c
      hbal 1 0 (Or.inr rfl) (by omega)
    have hdiff := landEntropy_moveMass_sub hbExhibitEntropy exhibitPhi c
      1 0 (Or.inr rfl) (by omega)
    have hΔ : landEntropy hbExhibitEntropy exhibitPhi (moveMass c 1 0)
        - landEntropy hbExhibitEntropy exhibitPhi c
        = 2 * Real.log 2 - Real.log 3 := by
      rw [hdiff, h0, h1, hp0, hp1]
      show (margEntropy hbExhibitEntropy 0 + 0)
          - (margEntropy hbExhibitEntropy 1 + 0)
          = 2 * Real.log 2 - Real.log 3
      rw [hm0, hm1]
      ring
    linarith
  · -- (1, 0, 1): the high corner drops into the centre, Δ = −1
    have hne := landBalance_move_neutral hbExhibitEntropy exhibitPhi c
      hbal 2 1 (Or.inr rfl) (by omega)
    have hdiff := landEntropy_moveMass_sub hbExhibitEntropy exhibitPhi c
      2 1 (Or.inr rfl) (by omega)
    have hΔ : landEntropy hbExhibitEntropy exhibitPhi (moveMass c 2 1)
        - landEntropy hbExhibitEntropy exhibitPhi c
        = -1 := by
      rw [hdiff, h1, h2, hp1, hp2]
      show (margEntropy hbExhibitEntropy 0 + 0)
          - (margEntropy hbExhibitEntropy 0 + 1)
          = -1
      rw [hm0]
      ring
    linarith
  · -- (1, 1, 0): the centre empties into the corner, Δ = log 3 − 2 log 2 < 0
    have hne := landBalance_move_neutral hbExhibitEntropy exhibitPhi c
      hbal 1 0 (Or.inr rfl) (by omega)
    have hdiff := landEntropy_moveMass_sub hbExhibitEntropy exhibitPhi c
      1 0 (Or.inr rfl) (by omega)
    have hΔ : landEntropy hbExhibitEntropy exhibitPhi (moveMass c 1 0)
        - landEntropy hbExhibitEntropy exhibitPhi c
        = Real.log 3 - 2 * Real.log 2 := by
      rw [hdiff, h0, h1, hp0, hp1]
      show (margEntropy hbExhibitEntropy 1 + 0)
          - (margEntropy hbExhibitEntropy 0 + 0)
          = Real.log 3 - 2 * Real.log 2
      rw [hm0, hm1]
      ring
    linarith
  · -- (2, 0, 0): the corner delta steps forward to the centre, Δ = 2 log 2 − log 3 > 0
    have hne := landBalance_move_neutral hbExhibitEntropy exhibitPhi c
      hbal 0 1 (Or.inl rfl) (by omega)
    have hdiff := landEntropy_moveMass_sub hbExhibitEntropy exhibitPhi c
      0 1 (Or.inl rfl) (by omega)
    have hΔ : landEntropy hbExhibitEntropy exhibitPhi (moveMass c 0 1)
        - landEntropy hbExhibitEntropy exhibitPhi c
        = 2 * Real.log 2 - Real.log 3 := by
      rw [hdiff, h1, h0, hp1, hp0]
      show (margEntropy hbExhibitEntropy 0 + 0)
          - (margEntropy hbExhibitEntropy 1 + 0)
          = 2 * Real.log 2 - Real.log 3
      rw [hm0, hm1]
      ring
    linarith

/-- **K-IPNE-EQUIL FIRES AGAIN — the bowl** (proved, exhibit):
at total 2 on `Fin 3`, NO distribution is a landscaped balance
on the symmetric bowl `bowlLandscape = ![1, 0, 1]` either. The
sharpest case is the centre delta `![0, 2, 0]` — the bowl's
UNIQUE reverse rest (RNE's `exhibit_bowl_unique_rest`) — killed
as a balance by its own forward step to a corner, of signed
change `2 log 2 − log 3 + 1 > 0`: the centre is where the
reversed flow gathers, and the forward flow leaves it. The
flat seat's rest point `![1, 0, 1]` drops a corner into the
centre at `−1` (RNE's un-deadlocking, read in the neutrality
ledger); the corner deltas shed toward the centre at
`2 log 2 − log 3 − 1 < 0`; the splits carry
`log 3 − 2 log 2 − 1 < 0`. On both exhibit landscapes the two
directions never agree to hold still: where a landscape acts,
there is no static equilibrium at this total. The equilibrium
that is its own reverse lives on the flat seat — the
composed-balance pin's isolated singles — and, at these
exhibits, nowhere else. -/
theorem exhibit_bowl_no_land_balance (c : Fin 3 → ℕ)
    (hsum : ∑ i, c i = 2) :
    ¬ IsLandBalance hbExhibitEntropy bowlLandscape c := by
  intro hbal
  obtain ⟨hm0, hm1⟩ := exhibit_marginals
  have h32 : Real.log 3 < 2 * Real.log 2 := exhibit_entropy_values.2.2.2
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt1 : Real.log 2 < 1 :=
    lt_trans Real.log_two_lt_d9 (by norm_num)
  have hlog23 : Real.log 2 < Real.log 3 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hsum3 : c 0 + c 1 + c 2 = 2 := by
    rw [← Fin.sum_univ_three]
    exact hsum
  have h0le : c 0 ≤ 2 := by omega
  have h1le : c 1 ≤ 2 := by omega
  have h2le : c 2 ≤ 2 := by omega
  have hb0 : bowlLandscape 0 = 1 := by norm_num [bowlLandscape]
  have hb1 : bowlLandscape 1 = 0 := by norm_num [bowlLandscape]
  have hb2 : bowlLandscape 2 = 1 := by norm_num [bowlLandscape]
  interval_cases h0 : c 0 <;> interval_cases h1 : c 1 <;>
    interval_cases h2 : c 2 <;> try omega
  · -- (0, 0, 2): the corner sheds toward the centre, Δ = 2 log 2 − log 3 − 1 < 0
    have hne := landBalance_move_neutral hbExhibitEntropy bowlLandscape c
      hbal 2 1 (Or.inr rfl) (by omega)
    have hdiff := landEntropy_moveMass_sub hbExhibitEntropy bowlLandscape c
      2 1 (Or.inr rfl) (by omega)
    have hΔ : landEntropy hbExhibitEntropy bowlLandscape (moveMass c 2 1)
        - landEntropy hbExhibitEntropy bowlLandscape c
        = 2 * Real.log 2 - Real.log 3 - 1 := by
      rw [hdiff, h1, h2, hb1, hb2]
      show (margEntropy hbExhibitEntropy 0 + 0)
          - (margEntropy hbExhibitEntropy 1 + 1)
          = 2 * Real.log 2 - Real.log 3 - 1
      rw [hm0, hm1]
      ring
    linarith
  · -- (0, 1, 1): the high corner drops into the centre, Δ = log 3 − 2 log 2 − 1 < 0
    have hne := landBalance_move_neutral hbExhibitEntropy bowlLandscape c
      hbal 2 1 (Or.inr rfl) (by omega)
    have hdiff := landEntropy_moveMass_sub hbExhibitEntropy bowlLandscape c
      2 1 (Or.inr rfl) (by omega)
    have hΔ : landEntropy hbExhibitEntropy bowlLandscape (moveMass c 2 1)
        - landEntropy hbExhibitEntropy bowlLandscape c
        = Real.log 3 - 2 * Real.log 2 - 1 := by
      rw [hdiff, h1, h2, hb1, hb2]
      show (margEntropy hbExhibitEntropy 1 + 0)
          - (margEntropy hbExhibitEntropy 0 + 1)
          = Real.log 3 - 2 * Real.log 2 - 1
      rw [hm0, hm1]
      ring
    linarith
  · -- (0, 2, 0): the centre delta — the bowl's unique reverse rest — steps
    -- forward to a corner, Δ = 2 log 2 − log 3 + 1 > 0
    have hne := landBalance_move_neutral hbExhibitEntropy bowlLandscape c
      hbal 1 0 (Or.inr rfl) (by omega)
    have hdiff := landEntropy_moveMass_sub hbExhibitEntropy bowlLandscape c
      1 0 (Or.inr rfl) (by omega)
    have hΔ : landEntropy hbExhibitEntropy bowlLandscape (moveMass c 1 0)
        - landEntropy hbExhibitEntropy bowlLandscape c
        = 2 * Real.log 2 - Real.log 3 + 1 := by
      rw [hdiff, h0, h1, hb0, hb1]
      show (margEntropy hbExhibitEntropy 0 + 1)
          - (margEntropy hbExhibitEntropy 1 + 0)
          = 2 * Real.log 2 - Real.log 3 + 1
      rw [hm0, hm1]
      ring
    linarith
  · -- (1, 0, 1): the flat rest point drops a corner into the centre, Δ = −1
    have hne := landBalance_move_neutral hbExhibitEntropy bowlLandscape c
      hbal 0 1 (Or.inl rfl) (by omega)
    have hdiff := landEntropy_moveMass_sub hbExhibitEntropy bowlLandscape c
      0 1 (Or.inl rfl) (by omega)
    have hΔ : landEntropy hbExhibitEntropy bowlLandscape (moveMass c 0 1)
        - landEntropy hbExhibitEntropy bowlLandscape c
        = -1 := by
      rw [hdiff, h1, h0, hb1, hb0]
      show (margEntropy hbExhibitEntropy 0 + 0)
          - (margEntropy hbExhibitEntropy 0 + 1)
          = -1
      rw [hm0]
      ring
    linarith
  · -- (1, 1, 0): the corner drops into the centre, Δ = log 3 − 2 log 2 − 1 < 0
    have hne := landBalance_move_neutral hbExhibitEntropy bowlLandscape c
      hbal 0 1 (Or.inl rfl) (by omega)
    have hdiff := landEntropy_moveMass_sub hbExhibitEntropy bowlLandscape c
      0 1 (Or.inl rfl) (by omega)
    have hΔ : landEntropy hbExhibitEntropy bowlLandscape (moveMass c 0 1)
        - landEntropy hbExhibitEntropy bowlLandscape c
        = Real.log 3 - 2 * Real.log 2 - 1 := by
      rw [hdiff, h1, h0, hb1, hb0]
      show (margEntropy hbExhibitEntropy 1 + 0)
          - (margEntropy hbExhibitEntropy 0 + 1)
          = Real.log 3 - 2 * Real.log 2 - 1
      rw [hm0, hm1]
      ring
    linarith
  · -- (2, 0, 0): the corner sheds toward the centre, Δ = 2 log 2 − log 3 − 1 < 0
    have hne := landBalance_move_neutral hbExhibitEntropy bowlLandscape c
      hbal 0 1 (Or.inl rfl) (by omega)
    have hdiff := landEntropy_moveMass_sub hbExhibitEntropy bowlLandscape c
      0 1 (Or.inl rfl) (by omega)
    have hΔ : landEntropy hbExhibitEntropy bowlLandscape (moveMass c 0 1)
        - landEntropy hbExhibitEntropy bowlLandscape c
        = 2 * Real.log 2 - Real.log 3 - 1 := by
      rw [hdiff, h1, h0, hb1, hb0]
      show (margEntropy hbExhibitEntropy 0 + 0)
          - (margEntropy hbExhibitEntropy 1 + 1)
          = 2 * Real.log 2 - Real.log 3 - 1
      rw [hm0, hm1]
      ring
    linarith

-- ============================================================================
-- IPNE-2 (the heavy brick). The reverse-rest characterization, flat seat
-- ============================================================================

/-- **The reverse rests, characterized** (proved): under
strictly antitone marginals, a distribution is a rest point
of the reversed flow iff every occupied seat STRICTLY EXCEEDS
each of its neighbours — `c j ≤ c i − 1` for every neighbour
`j` of every occupied seat `i`. The strict-peak condition.
Route, both directions pointwise through the exact
bookkeeping: if some occupied seat fails to strictly exceed a
neighbour (`c i ≤ c j`), strict antitonicity turns it into
the marginal descent `margEntropy s (c j) < margEntropy s
(c i − 1)`, and `revStep_of_marginal` exhibits the step the
rest forbids; conversely a reversed step's descent, read
through `seatEntropy_moveMass_sub`, contradicts the peak
condition by the same antitonicity. This is the dual of the
composed-balance pin's isolated-singles characterization of
the both-directions rest: the one-direction rest is a strict
peak, the two-direction rest is an isolated single. -/
theorem isRevRest_iff (s : ℕ → ℝ) {n : ℕ}
    (hs : StrictAnti (margEntropy s)) (c : Fin n → ℕ) :
    IsRevRest s c ↔ ∀ i j, Neighbours i j → 1 ≤ c i → c j ≤ c i - 1 := by
  constructor
  · intro hrest i j hadj hi
    by_contra hcon
    have hlt : c i - 1 < c j := by omega
    have hmarg : margEntropy s (c j) < margEntropy s (c i - 1) := hs hlt
    exact hrest _ (revStep_of_marginal s c i j hadj hi hmarg)
  · intro hpt c' hstep
    obtain ⟨i, j, hadj, hi, rfl, hlt⟩ := hstep
    have hdiff := seatEntropy_moveMass_sub s c i j hadj hi
    have hle : c j ≤ c i - 1 := hpt i j hadj hi
    have hmarg : margEntropy s (c i - 1) ≤ margEntropy s (c j) := by
      rcases lt_or_eq_of_le hle with h | h
      · exact le_of_lt (hs h)
      · exact le_of_eq (congrArg (margEntropy s) h.symm)
    linarith

/-- **The total-2 reverse-rest set on `Fin 3`, counted
exactly** (proved): under `s₀`, the reverse rests of total 2
are exactly the three deltas and the centre-empty split
`![1, 0, 1]` — fourfold. Corollary of the characterization
by finite case check: the splits `![1, 1, 0]` and
`![0, 1, 1]` fail the strict-peak condition at the shared
edge (an occupied seat whose neighbour holds as much), and
every other total-2 distribution is a strict peak at each
occupied seat. The `![1, 0, 1]` membership is CITED from
RNE's `exhibit_flat_rest_countermodel` (the K-RNE-FLAT
countermodel), not re-proved. Read against the
composed-balance pin: at the same seat and total the
both-directions rest is UNIQUE (`![1, 0, 1]`, that pin's
Brick 3b) while the one-direction rest is fourfold — the
reverse problem's non-uniqueness, counted. (K-IPNE-UNIQ,
counted here; exhibited in Brick 3.) The s₀ hypothesis is
CITED from the composed-balance pin's
`margEntropy_hbExhibit_strictAnti` — priced for whichever
pin fired first, proved there, per K-IPNE-DUP. -/
theorem exhibit_flat_rest_set_total_two (c : Fin 3 → ℕ)
    (hsum : ∑ i, c i = 2) :
    IsRevRest hbExhibitEntropy c ↔
      c = ![2, 0, 0] ∨ c = ![0, 2, 0] ∨ c = ![0, 0, 2]
        ∨ c = ![1, 0, 1] := by
  have hs : StrictAnti (margEntropy hbExhibitEntropy) :=
    margEntropy_hbExhibit_strictAnti
  have hsum3 : c 0 + c 1 + c 2 = 2 := by
    rw [← Fin.sum_univ_three]
    exact hsum
  have h0le : c 0 ≤ 2 := by omega
  have h1le : c 1 ≤ 2 := by omega
  have h2le : c 2 ≤ 2 := by omega
  constructor
  · intro hrest
    have hpt := (isRevRest_iff hbExhibitEntropy hs c).mp hrest
    interval_cases h0 : c 0 <;> interval_cases h1 : c 1 <;>
      interval_cases h2 : c 2 <;> try omega
    · -- (0, 0, 2): the far corner delta
      refine Or.inr (Or.inr (Or.inl ?_))
      funext k
      fin_cases k <;> simp [h0, h1, h2]
    · -- (0, 1, 1): fails the peak condition at the 2 → 1 edge
      exfalso
      have hpk := hpt 2 1 (Or.inr rfl) (by omega)
      omega
    · -- (0, 2, 0): the centre delta
      refine Or.inr (Or.inl ?_)
      funext k
      fin_cases k <;> simp [h0, h1, h2]
    · -- (1, 0, 1): the centre-empty split
      refine Or.inr (Or.inr (Or.inr ?_))
      funext k
      fin_cases k <;> simp [h0, h1, h2]
    · -- (1, 1, 0): fails the peak condition at the 0 → 1 edge
      exfalso
      have hpk := hpt 0 1 (Or.inl rfl) (by omega)
      omega
    · -- (2, 0, 0): the corner delta
      refine Or.inl ?_
      funext k
      fin_cases k <;> simp [h0, h1, h2]
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · -- ![2, 0, 0]: strict peak at seat 0, vacuous elsewhere
      refine (isRevRest_iff hbExhibitEntropy hs _).mpr ?_
      intro i j hadj hi
      fin_cases i <;> fin_cases j <;>
        norm_num [Neighbours] at hadj <;> norm_num at hi <;> norm_num
    · -- ![0, 2, 0]: strict peak at seat 1
      refine (isRevRest_iff hbExhibitEntropy hs _).mpr ?_
      intro i j hadj hi
      fin_cases i <;> fin_cases j <;>
        norm_num [Neighbours] at hadj <;> norm_num at hi <;> norm_num
    · -- ![0, 0, 2]: strict peak at seat 2
      refine (isRevRest_iff hbExhibitEntropy hs _).mpr ?_
      intro i j hadj hi
      fin_cases i <;> fin_cases j <;>
        norm_num [Neighbours] at hadj <;> norm_num at hi <;> norm_num
    · -- ![1, 0, 1]: CITED from RNE's flat countermodel
      exact exhibit_flat_rest_countermodel.2.2.2

-- ============================================================================
-- IPNE-3 (the inverse problem). No unique answer, in either direction —
-- K-IPNE-UNIQ fires
-- ============================================================================

/-- **One state, two distinct reverse futures** (proved,
exhibit): from the split `![1, 1, 0]`, the reversed step
reaches TWO distinct distributions, and both are rests (both
are in Brick 2's rest set): the corner delta `![2, 0, 0]` —
CITED from RNE's `exhibit_revStep_to_corner`, the centre
quantum stepping into the corner — and the centre delta
`![0, 2, 0]`, the corner quantum stepping into the centre
(the marginals are the same pair read the other way:
`log (3/2) < log 2`). The reversed dynamics does not
determine its own future: from one present, the film runs to
two different stills. -/
theorem exhibit_revStep_two_futures :
    RevStep hbExhibitEntropy ![1, 1, 0] ![2, 0, 0]
    ∧ RevStep hbExhibitEntropy ![1, 1, 0] ![0, 2, 0] := by
  refine ⟨exhibit_revStep_to_corner, ?_⟩
  obtain ⟨hm0, hm1⟩ := exhibit_marginals
  obtain ⟨-, -, -, hlt⟩ := exhibit_entropy_values
  have hmove : moveMass ![1, 1, 0] 0 1 = ![0, 2, 0] := by
    funext k
    fin_cases k <;> simp [moveMass]
  have h10 : (![1, 1, 0] : Fin 3 → ℕ) 0 = 1 := by norm_num
  have h11 : (![1, 1, 0] : Fin 3 → ℕ) 1 = 1 := by norm_num
  have hmarg : margEntropy hbExhibitEntropy ((![1, 1, 0] : Fin 3 → ℕ) 1)
      < margEntropy hbExhibitEntropy ((![1, 1, 0] : Fin 3 → ℕ) 0 - 1) := by
    rw [h10, h11]
    show margEntropy hbExhibitEntropy 1
      < margEntropy hbExhibitEntropy 0
    rw [hm0, hm1]
    linarith
  have hstep := revStep_of_marginal hbExhibitEntropy ![1, 1, 0] 0 1
    (Or.inl rfl) (by rw [h10]) hmarg
  rwa [hmove] at hstep

/-- **K-IPNE-UNIQ FIRES** (proved — the pre-registered kill,
at full rank): the centre delta `![0, 2, 0]` — itself a
reverse rest, by Brick 2's enumeration — has TWO distinct
one-step pasts among total-2 states: `![1, 1, 0]` (the corner
quantum stepped in) and `![0, 1, 1]` (the far corner's
quantum stepped in). So no inverse of the reversed step
exists even on the exhibit: the present does not determine
the past, and the step cannot be run backwards as a
function. Together with `exhibit_revStep_two_futures` (one
present, two futures) and Brick 2's fourfold rest set, the
claim "the reverse problem is uniquely solvable" is FALSE in
every direction the finite seat can state it. This is the
finite shadow of the backward heat equation's ill-posedness:
the film cannot be run backwards because it was never a
function. (K-IPNE-CONT: a shadow, labeled as such — no PDE
is stated or claimed.) -/
theorem exhibit_revRest_two_pasts :
    RevStep hbExhibitEntropy ![1, 1, 0] ![0, 2, 0]
    ∧ RevStep hbExhibitEntropy ![0, 1, 1] ![0, 2, 0] := by
  refine ⟨exhibit_revStep_two_futures.2, ?_⟩
  obtain ⟨hm0, hm1⟩ := exhibit_marginals
  obtain ⟨-, -, -, hlt⟩ := exhibit_entropy_values
  have hmove : moveMass ![0, 1, 1] 2 1 = ![0, 2, 0] := by
    funext k
    fin_cases k <;> simp [moveMass]
  have h21 : (![0, 1, 1] : Fin 3 → ℕ) 1 = 1 := by norm_num
  have h22 : (![0, 1, 1] : Fin 3 → ℕ) 2 = 1 := by norm_num
  have hmarg : margEntropy hbExhibitEntropy ((![0, 1, 1] : Fin 3 → ℕ) 1)
      < margEntropy hbExhibitEntropy ((![0, 1, 1] : Fin 3 → ℕ) 2 - 1) := by
    rw [h21, h22]
    show margEntropy hbExhibitEntropy 1
      < margEntropy hbExhibitEntropy 0
    rw [hm0, hm1]
    linarith
  have hstep := revStep_of_marginal hbExhibitEntropy ![0, 1, 1] 2 1
    (Or.inr rfl) (by rw [h22]) hmarg
  rwa [hmove] at hstep

end ThetLogos
