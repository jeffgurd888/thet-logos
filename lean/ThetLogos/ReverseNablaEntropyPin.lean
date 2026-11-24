import Mathlib.Tactic
import ThetLogos.HarmonicBalancePin
import ThetLogos.RefractiveThermalEntropyPin
import ThetLogos.CenterCoincidencePin

/-!
# ThetLogos.ReverseNablaEntropyPin — reverse nabla entropy, in finite form

**Lane-grade pin. NO CLAIM. Pre-registered DIAL-INELIGIBLE; dials
0/4 under every outcome. Dial 2 = 0 under every outcome: a finite
seat's center-seeking flow, if one is proved, is a toy dynamics,
not a gravity object. QTST — Zero's filed candidate name for a
continuum string completion — is NOT worn by this pin.**

Commissioned: Zero, 2026-11-20 ("scope it", 20:57 EST; Brick A
fired 23:46 EST — "Fire RNE — Brick A first"), from his seeing of
2026-11-20 20:47 EST: "thermal string theory is working on
finding gravity from the dynamics of reverse nabla entropy", and
his question of 23:46 EST, filed verbatim and not completed:
"the shape of reverse nabla entropy creates Geometrically".
Scope of record: `reverse-nabla-entropy-scope-2026-11-20.md`
(T5 scope). Working label only — Zero names.

## The object and the step (definitions on the face)

The corpus's forward dynamics climb entropy: HB's exchange step
equilibrates toward a spread rest point, HB-3's greedy step moves
one quantum in the direction the marginals dictate — the
entropy-increasing direction — and RTE's kernel flow relaxes to
its rest point. This pin runs the film backwards. The seat is
HB-3's discrete seat generalized from two families to `n`:
quantum counts `c : Fin n → ℕ`, with total entropy the sum of a
per-seat entropy function,

    `seatEntropy s c = ∑ i, s (c i)`

— on `Fin 2` with total `K` this is HB-3's `splitEntropy s K`.
The **reversed step** (anti-exchange) is the formal reverse of
HB-3's greedy step: one quantum crosses a neighbour edge (seats
whose indices are one apart on the path `Fin n`), and the move
is taken exactly when the total entropy strictly DECREASES —
where the greedy step climbs, the reversed step descends. By
the exact bookkeeping of `seatEntropy_moveMass_sub`, a move
`i → j` changes the total entropy by
`margEntropy s (c j) − margEntropy s (c i − 1)`, so the reversed
step is the marginal condition
`margEntropy s (c j) < margEntropy s (c i − 1)` — HB-3's greedy
inequality turned around. On the exhibit entropy function
`s₀ = log (· + 1)` (HB-3's `hbExhibitEntropy`), whose marginals
strictly decrease, that condition reads `c j ≥ c i`: mass moves
to a neighbour seat holding at least as much as the seat it
leaves — from the lighter to the heavier, anti-diffusion.

Zero's question: does the reversed dynamics merely collapse
mass somewhere, or does it SEEK A CENTER — the behaviour
gravity shows? Brick A asks it on the flat seat, where no
landscape and no built-in center can help.

## Brick A — the flat seat (this brick)

Exhibit: `Fin 3`, `s₀`, total mass `2`. Question A1: do
iterates from any non-delta start converge to a delta (total
concentration)? **K-RNE-FLAT armed** on the claim "the flat-seat
reversed flow selects the CENTER seat" — expected to fire: on a
flat seat every delta is an entropy minimum and the center has
no privilege. It fires; both verdicts are proved in this brick
(`exhibit_revStep_to_corner`, `exhibit_flat_rest_countermodel`)
and reported at full rank in the brick's close. If it fires, the
priced obstruction IS the result: reverse nabla entropy ALONE
does not make a center.

## Brick B — the landscaped seat (below, two sub-bricks)

The centre has to be earned by a landscape. The landscaped
reversed step descends `landEntropy` — the flat seat's entropy
plus the landscape potential `∑ k, ℓ k * c k` (coefficient `1`,
β = 1, stated on the definition's face). Sub-brick B1: the
machinery and the SYMMETRIC BOWL `ℓ = ![1, 0, 1]`, whose
minimum is the centre seat alone — there the flow gathers to
the centre delta, uniquely (Brick A's flat countermodel is
un-deadlocked by the landscape and delivered to the centre).
Sub-brick B2: RTE's GRADED seat `exhibitPhi = ![0, 0, 1]` and
the K-RNE-THERMAL verdict. **K-RNE-THERMAL FIRES** on the
graded seat: the centre delta rests, but so does the corner
delta `![2, 0, 0]`, and a legal landscaped step empties the
centre into the corner — the centre is not selected. The
thermal-centre alternative fails with it: the landscape's
thermal centre is `(1 + 2e⁻¹)/(2 + e⁻¹) ≈ 0.733`, strictly
between the two rest seats, and the flow's rest points sit at
mass centres `0` and `1` — the flow rests at the landscape's
minimum set `{0, 1}`, not at any centre. Read with B1: a
centre is earned exactly when the landscape's minimum is the
centre alone. The reversed dynamics seeks the landscape's
minimum — not its geometric centre, and not its thermal
centre.

## Fences

- Definitions pinned before any verdict was computed; no
  definition in this module was repaired to force or soften an
  answer (the RTE-2 rule).
- The step is a defined finite operation on quantum counts; no
  continuum limit, no physical time, no force law is claimed.
-/

namespace ThetLogos

-- ============================================================================
-- RNE-A (machinery). The seat, the move, the reversed step
-- ============================================================================

/-- **Total entropy of a quantum-count distribution**
(definition): the sum of the per-seat entropy function over
all seats. On `Fin 2` with total `K` this is HB-3's
`splitEntropy`. -/
def seatEntropy (s : ℕ → ℝ) {n : ℕ} (c : Fin n → ℕ) : ℝ :=
  ∑ i, s (c i)

/-- **Move one quantum** (definition): the count distribution
obtained from `c` by taking one quantum from seat `i` and
giving it to seat `j`. -/
def moveMass {n : ℕ} (c : Fin n → ℕ) (i j : Fin n) : Fin n → ℕ :=
  fun k => if k = i then c i - 1 else if k = j then c j + 1 else c k

/-- **Neighbouring seats** (definition): indices one apart on
the path `Fin n`. -/
def Neighbours {n : ℕ} (i j : Fin n) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val

/-- **The reversed step** (definition, pinned): `c'` follows
`c` by one reversed step when one quantum crosses a neighbour
edge — from a seat holding at least one quantum, to a
neighbouring seat — and the total entropy strictly decreases.
The formal reverse of HB-3's greedy step, which takes the same
one-quantum neighbour move when the total entropy strictly
increases. -/
def RevStep (s : ℕ → ℝ) {n : ℕ} (c c' : Fin n → ℕ) : Prop :=
  ∃ i j, Neighbours i j ∧ 1 ≤ c i ∧ c' = moveMass c i j
    ∧ seatEntropy s c' < seatEntropy s c

/-- **A delta** (definition): all the mass on a single seat —
total concentration. -/
def IsDelta {n : ℕ} (c : Fin n → ℕ) : Prop :=
  ∃ k, ∀ i, c i = if i = k then ∑ j, c j else 0

/-- **A rest point of the reversed flow** (definition): a
distribution no reversed step leaves. -/
def IsRevRest (s : ℕ → ℝ) {n : ℕ} (c : Fin n → ℕ) : Prop :=
  ∀ c', ¬ RevStep s c c'

/-- **The entropy change of one move, exactly** (proved):
moving one quantum from seat `i` (holding at least one) to a
neighbouring seat `j` changes the total entropy by

    `margEntropy s (c j) - margEntropy s (c i - 1)` —

what the receiving seat's next quantum gains, minus what the
giving seat's last quantum carried. HB-3's bookkeeping
(`greedy_step_entropy_change`) on the `Fin n` seat. -/
theorem seatEntropy_moveMass_sub (s : ℕ → ℝ) {n : ℕ} (c : Fin n → ℕ)
    (i j : Fin n) (hadj : Neighbours i j) (hi : 1 ≤ c i) :
    seatEntropy s (moveMass c i j) - seatEntropy s c
      = margEntropy s (c j) - margEntropy s (c i - 1) := by
  have hij : i ≠ j := by
    intro heq
    subst heq
    rcases hadj with h | h <;> omega
  have hji : j ≠ i := Ne.symm hij
  have hgi : moveMass c i j i = c i - 1 := by simp [moveMass]
  have hgj : moveMass c i j j = c j + 1 := by simp [moveMass, hji]
  have hsum : ∑ k ∈ ({i, j} : Finset (Fin n)),
        (s (moveMass c i j k) - s (c k))
      = ∑ k, (s (moveMass c i j k) - s (c k)) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton,
      not_or] at hk
    have hmk : moveMass c i j k = c k := by
      simp [moveMass, hk.1, hk.2]
    rw [hmk, sub_self]
  unfold seatEntropy
  rw [← Finset.sum_sub_distrib, ← hsum, Finset.sum_pair hij, hgi, hgj]
  have hmarg : margEntropy s (c i - 1) = s (c i) - s (c i - 1) := by
    unfold margEntropy
    rw [Nat.sub_add_cancel hi]
  rw [hmarg]
  unfold margEntropy
  ring

/-- **The reversed step, by its marginals** (proved): a move
from `i` to a neighbour `j` IS a reversed step exactly when it
descends — when the receiving seat's next quantum gains less
entropy than the giving seat's last quantum carries,
`margEntropy s (c j) < margEntropy s (c i - 1)`. This is
HB-3's greedy condition (`greedy_step_increases`) with the
inequality turned around: the formal reverse of the greedy
step. On the exhibit `s₀ = log (· + 1)`, whose marginals
strictly decrease, the condition reads `c j ≥ c i`: mass moves
to a neighbour seat holding at least as much — lighter to
heavier, anti-diffusion. -/
theorem revStep_of_marginal (s : ℕ → ℝ) {n : ℕ} (c : Fin n → ℕ)
    (i j : Fin n) (hadj : Neighbours i j) (hi : 1 ≤ c i)
    (hmarg : margEntropy s (c j) < margEntropy s (c i - 1)) :
    RevStep s c (moveMass c i j) := by
  refine ⟨i, j, hadj, hi, rfl, ?_⟩
  have h := seatEntropy_moveMass_sub s c i j hadj hi
  linarith

-- ============================================================================
-- RNE-A (exhibit). The flat seat — K-RNE-FLAT FIRES
-- ============================================================================

/-- **The reversed step empties the center into the corner**
(proved, exhibit): from the split `![1, 1, 0]` — one quantum
on the center seat `1`, one on the corner seat `0` — a legal
reversed step moves the center seat's quantum into the corner,
landing on the corner delta `![2, 0, 0]`. The marginals:
the corner's next quantum gains `log (3/2)`; the center's last
quantum carries `log 2`; `log (3/2) < log 2`, so the move
descends. The flow does not gather to the center; it leaves. -/
theorem exhibit_revStep_to_corner :
    RevStep hbExhibitEntropy ![1, 1, 0] ![2, 0, 0] := by
  have h10 : (![1, 1, 0] : Fin 3 → ℕ) 0 = 1 := by norm_num
  have h11 : (![1, 1, 0] : Fin 3 → ℕ) 1 = 1 := by norm_num
  have hmove : moveMass ![1, 1, 0] 1 0 = ![2, 0, 0] := by
    funext k
    fin_cases k <;> simp [moveMass]
  obtain ⟨hm0, hm1⟩ := exhibit_marginals
  obtain ⟨-, -, -, hlt⟩ := exhibit_entropy_values
  have hmarg : margEntropy hbExhibitEntropy ((![1, 1, 0] : Fin 3 → ℕ) 0)
      < margEntropy hbExhibitEntropy ((![1, 1, 0] : Fin 3 → ℕ) 1 - 1) := by
    rw [h10, h11]
    show margEntropy hbExhibitEntropy 1
      < margEntropy hbExhibitEntropy 0
    rw [hm1, hm0]
    linarith
  have hstep := revStep_of_marginal hbExhibitEntropy ![1, 1, 0] 1 0
    (Or.inr rfl) (by rw [h11]) hmarg
  rwa [hmove] at hstep

/-- **K-RNE-FLAT FIRES** (proved — the pre-registered kill, at
full rank): the flat-seat reversed flow does NOT select the
center seat. The distribution `![1, 0, 1]` — total mass `2`,
split evenly between the two corner seats, the center seat
`1` EMPTY — is already a rest point of the reversed flow on
the exhibit seat, and it is not a delta: from this start the
flow cannot take even one step, so its iterates never
concentrate at all, let alone at the center. (The only
candidate moves would carry a corner quantum onto the empty
center seat; each is entropy-neutral for `s₀` — a lone quantum
stepping onto an empty seat changes no seat-entropy sum — so
no strictly descending move exists.) Together with
`exhibit_revStep_to_corner` — a legal reversed step that
empties the center into a corner — the scoped claim "the
flat-seat reversed flow selects the CENTER seat" is FALSE for
the pinned reversed step. Question A1 dies with it: iterates
from a non-delta start need not converge to a delta. On a
flat seat every delta is an entropy minimum and the center
has no privilege: reverse nabla entropy ALONE does not make
a center. No definition was adjusted to soften this. -/
theorem exhibit_flat_rest_countermodel :
    (∑ i, (![1, 0, 1] : Fin 3 → ℕ) i) = 2
    ∧ (![1, 0, 1] : Fin 3 → ℕ) 1 = 0
    ∧ ¬ IsDelta (![1, 0, 1] : Fin 3 → ℕ)
    ∧ IsRevRest hbExhibitEntropy (![1, 0, 1] : Fin 3 → ℕ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [Fin.sum_univ_three]
  · norm_num
  · rintro ⟨k, hk⟩
    fin_cases k
    · have h2 := hk 2
      norm_num [Fin.sum_univ_three] at h2
    · have h0 := hk 0
      norm_num [Fin.sum_univ_three] at h0
    · have h0 := hk 0
      norm_num [Fin.sum_univ_three] at h0
  · intro c' hstep
    obtain ⟨i, j, hadj, hi, rfl, hlt⟩ := hstep
    have hdiff := seatEntropy_moveMass_sub hbExhibitEntropy
      ![1, 0, 1] i j hadj hi
    fin_cases i <;> fin_cases j <;>
      norm_num [Neighbours] at hadj <;>
      norm_num at hi <;>
      norm_num at hdiff <;>
      norm_num at hlt <;>
      linarith

-- ============================================================================
-- RNE-B (machinery). The landscaped seat: entropy descent weighted by ℓ
-- ============================================================================

/-- **The landscaped entropy** (definition, pinned): the flat
seat's total entropy plus the landscape potential of the mass
distribution — each quantum at seat `k` pays the landscape
height `ℓ k`. The landscape enters with coefficient `1`
(β = 1, the ICDT exhibit's inverse temperature); the weighting
is part of the pinned definition, stated here on the face. -/
def landEntropy (s : ℕ → ℝ) {n : ℕ} (ℓ : Fin n → ℝ) (c : Fin n → ℕ) :
    ℝ :=
  seatEntropy s c + ∑ k, ℓ k * (c k : ℝ)

/-- **The landscaped reversed step** (definition, pinned):
one quantum crosses a neighbour edge — from a seat holding at
least one quantum, to a neighbouring seat — and the
LANDSCAPED entropy strictly decreases. Brick A's reversed
step is the flat case `ℓ ≡ 0`. -/
def LandRevStep (s : ℕ → ℝ) {n : ℕ} (ℓ : Fin n → ℝ) (c c' : Fin n → ℕ) :
    Prop :=
  ∃ i j, Neighbours i j ∧ 1 ≤ c i ∧ c' = moveMass c i j
    ∧ landEntropy s ℓ c' < landEntropy s ℓ c

/-- **A rest point of the landscaped reversed flow**
(definition): a distribution no landscaped reversed step
leaves. -/
def IsLandRevRest (s : ℕ → ℝ) {n : ℕ} (ℓ : Fin n → ℝ) (c : Fin n → ℕ) :
    Prop :=
  ∀ c', ¬ LandRevStep s ℓ c c'

/-- **The entropy change of one move on the landscaped seat,
exactly** (proved): moving one quantum from seat `i` (holding
at least one) to a neighbouring seat `j` changes the
landscaped entropy by

    `(margEntropy s (c j) + ℓ j) - (margEntropy s (c i - 1) + ℓ i)` —

Brick A's bookkeeping with the landscape height added to each
seat's marginal: the receiving seat's next quantum gains its
marginal plus its height; the giving seat's last quantum
carried its marginal plus its height. -/
theorem landEntropy_moveMass_sub (s : ℕ → ℝ) {n : ℕ} (ℓ : Fin n → ℝ)
    (c : Fin n → ℕ) (i j : Fin n) (hadj : Neighbours i j) (hi : 1 ≤ c i) :
    landEntropy s ℓ (moveMass c i j) - landEntropy s ℓ c
      = (margEntropy s (c j) + ℓ j) - (margEntropy s (c i - 1) + ℓ i) := by
  have hij : i ≠ j := by
    intro heq
    subst heq
    rcases hadj with h | h <;> omega
  have hji : j ≠ i := Ne.symm hij
  have hE := seatEntropy_moveMass_sub s c i j hadj hi
  have hP : (∑ k, ℓ k * ((moveMass c i j k : ℕ) : ℝ))
        - (∑ k, ℓ k * (c k : ℝ))
      = ℓ j - ℓ i := by
    have hsum : ∑ k ∈ ({i, j} : Finset (Fin n)),
          (ℓ k * ((moveMass c i j k : ℕ) : ℝ) - ℓ k * (c k : ℝ))
        = ∑ k, (ℓ k * ((moveMass c i j k : ℕ) : ℝ) - ℓ k * (c k : ℝ)) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      have hmk : moveMass c i j k = c k := by
        simp [moveMass, hk.1, hk.2]
      rw [hmk, sub_self]
    rw [← Finset.sum_sub_distrib, ← hsum, Finset.sum_pair hij]
    have hgi : ((moveMass c i j i : ℕ) : ℝ) = (c i : ℝ) - 1 := by
      have h1 : moveMass c i j i = c i - 1 := by simp [moveMass]
      rw [h1, Nat.cast_sub hi, Nat.cast_one]
    have hgj : ((moveMass c i j j : ℕ) : ℝ) = (c j : ℝ) + 1 := by
      have h2 : moveMass c i j j = c j + 1 := by simp [moveMass, hji]
      rw [h2, Nat.cast_add, Nat.cast_one]
    rw [hgi, hgj]
    ring
  unfold landEntropy
  linarith

/-- **The landscaped reversed step, by its marginals**
(proved): a move from `i` to a neighbour `j` IS a landscaped
reversed step exactly when it descends — when the receiving
seat's marginal-plus-height is less than the giving seat's
last quantum's marginal-plus-height. Brick A's marginal
condition with the landscape height added on both sides. -/
theorem landRevStep_of_marginal (s : ℕ → ℝ) {n : ℕ} (ℓ : Fin n → ℝ)
    (c : Fin n → ℕ) (i j : Fin n) (hadj : Neighbours i j) (hi : 1 ≤ c i)
    (hmarg : margEntropy s (c j) + ℓ j < margEntropy s (c i - 1) + ℓ i) :
    LandRevStep s ℓ c (moveMass c i j) := by
  refine ⟨i, j, hadj, hi, rfl, ?_⟩
  have h := landEntropy_moveMass_sub s ℓ c i j hadj hi
  linarith

-- ============================================================================
-- RNE-B1 (exhibit). The symmetric bowl — the landscape's minimum IS
-- the centre seat, and the flow gathers there
-- ============================================================================

/-- **The symmetric bowl landscape** (definition): on `Fin 3`,
the distance from the centre seat `1` — height `1` at the two
corner seats, `0` at the centre. Its minimum is the centre
seat alone. -/
def bowlLandscape : Fin 3 → ℝ := ![1, 0, 1]

/-- **The centre delta rests on the bowl** (proved, exhibit):
with both quanta on the centre seat, no landscaped reversed
step leaves — a quantum stepping to a corner would gain
`log 2 + 1` of marginal-plus-height against the centre's last
quantum's `log (3/2)`, so no move descends. -/
theorem exhibit_bowl_center_rest :
    IsLandRevRest hbExhibitEntropy bowlLandscape ![0, 2, 0] := by
  intro c' hstep
  obtain ⟨i, j, hadj, hi, rfl, hlt⟩ := hstep
  have hdiff := landEntropy_moveMass_sub hbExhibitEntropy bowlLandscape
    ![0, 2, 0] i j hadj hi
  obtain ⟨hm0, hm1⟩ := exhibit_marginals
  have h32 : Real.log 3 < 2 * Real.log 2 := exhibit_entropy_values.2.2.2
  fin_cases i <;> fin_cases j <;>
    norm_num [Neighbours] at hadj <;>
    norm_num at hi <;>
    norm_num [bowlLandscape] at hdiff <;>
    norm_num [bowlLandscape] at hlt <;>
    (rw [hm0, hm1] at hdiff; linarith)

/-- **The landscape un-deadlocks Brick A's countermodel**
(proved, exhibit): `![1, 0, 1]` — the flat seat's rest point,
corners loaded and centre EMPTY — is not a rest point on the
bowl. A corner quantum drops into the centre
(`![1, 0, 1] → ![0, 1, 1]`: the centre's marginal-plus-height
is `log 2 + 0` against the corner's `log 2 + 1`), and the
second corner follows (`![0, 1, 1] → ![0, 2, 0]`), landing on
the centre delta in two landscaped reversed steps. -/
theorem exhibit_bowl_undeadlocks :
    LandRevStep hbExhibitEntropy bowlLandscape ![1, 0, 1] ![0, 1, 1]
    ∧ LandRevStep hbExhibitEntropy bowlLandscape ![0, 1, 1] ![0, 2, 0] := by
  obtain ⟨hm0, hm1⟩ := exhibit_marginals
  have h32 : Real.log 3 < 2 * Real.log 2 := exhibit_entropy_values.2.2.2
  constructor
  · have hmove : moveMass ![1, 0, 1] 0 1 = ![0, 1, 1] := by
      funext k
      fin_cases k <;> simp [moveMass]
    have h10 : (![1, 0, 1] : Fin 3 → ℕ) 0 = 1 := by norm_num
    have h11 : (![1, 0, 1] : Fin 3 → ℕ) 1 = 0 := by norm_num
    have hb0 : bowlLandscape 0 = 1 := by norm_num [bowlLandscape]
    have hb1 : bowlLandscape 1 = 0 := by norm_num [bowlLandscape]
    have hmarg : margEntropy hbExhibitEntropy ((![1, 0, 1] : Fin 3 → ℕ) 1)
          + bowlLandscape 1
        < margEntropy hbExhibitEntropy ((![1, 0, 1] : Fin 3 → ℕ) 0 - 1)
          + bowlLandscape 0 := by
      rw [h10, h11, hb0, hb1]
      show margEntropy hbExhibitEntropy 0 + 0
        < margEntropy hbExhibitEntropy 0 + 1
      rw [hm0]
      linarith
    have hstep := landRevStep_of_marginal hbExhibitEntropy bowlLandscape
      ![1, 0, 1] 0 1 (Or.inl rfl) (by norm_num) hmarg
    rwa [hmove] at hstep
  · have hmove : moveMass ![0, 1, 1] 2 1 = ![0, 2, 0] := by
      funext k
      fin_cases k <;> simp [moveMass]
    have h21 : (![0, 1, 1] : Fin 3 → ℕ) 1 = 1 := by norm_num
    have h22 : (![0, 1, 1] : Fin 3 → ℕ) 2 = 1 := by norm_num
    have hb1 : bowlLandscape 1 = 0 := by norm_num [bowlLandscape]
    have hb2 : bowlLandscape 2 = 1 := by norm_num [bowlLandscape]
    have hmarg : margEntropy hbExhibitEntropy ((![0, 1, 1] : Fin 3 → ℕ) 1)
          + bowlLandscape 1
        < margEntropy hbExhibitEntropy ((![0, 1, 1] : Fin 3 → ℕ) 2 - 1)
          + bowlLandscape 2 := by
      rw [h21, h22, hb1, hb2]
      show margEntropy hbExhibitEntropy 1 + 0
        < margEntropy hbExhibitEntropy 0 + 1
      rw [hm0, hm1]
      linarith
    have hstep := landRevStep_of_marginal hbExhibitEntropy bowlLandscape
      ![0, 1, 1] 2 1 (Or.inr rfl) (by norm_num) hmarg
    rwa [hmove] at hstep

/-- **On the bowl, the centre delta is the ONLY rest point**
(proved, exhibit): every distribution of total mass `2` on
`Fin 3` other than `![0, 2, 0]` admits a landscaped reversed
step — checked seat by seat: each corner delta sheds a quantum
toward the centre, each split distribution has a descending
move into a fuller, lower seat. Together with
`exhibit_bowl_center_rest`, the bowl's reversed flow rests at
the centre delta and nowhere else. -/
theorem exhibit_bowl_unique_rest (c : Fin 3 → ℕ) (hsum : (∑ i, c i) = 2)
    (hrest : IsLandRevRest hbExhibitEntropy bowlLandscape c) :
    c = ![0, 2, 0] := by
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
  · -- (0, 0, 2): the corner delta sheds a quantum toward the centre
    exfalso
    have hmarg : margEntropy hbExhibitEntropy (c 1) + bowlLandscape 1
        < margEntropy hbExhibitEntropy (c 2 - 1) + bowlLandscape 2 := by
      rw [h1, h2, hb1, hb2]
      show margEntropy hbExhibitEntropy 0 + 0
        < margEntropy hbExhibitEntropy 1 + 1
      rw [hm0, hm1]
      linarith
    exact hrest _ (landRevStep_of_marginal hbExhibitEntropy bowlLandscape
      c 2 1 (Or.inr rfl) (by omega) hmarg)
  · -- (0, 1, 1): the loaded corner drops into the centre
    exfalso
    have hmarg : margEntropy hbExhibitEntropy (c 1) + bowlLandscape 1
        < margEntropy hbExhibitEntropy (c 2 - 1) + bowlLandscape 2 := by
      rw [h1, h2, hb1, hb2]
      show margEntropy hbExhibitEntropy 1 + 0
        < margEntropy hbExhibitEntropy 0 + 1
      rw [hm0, hm1]
      linarith
    exact hrest _ (landRevStep_of_marginal hbExhibitEntropy bowlLandscape
      c 2 1 (Or.inr rfl) (by omega) hmarg)
  · -- (0, 2, 0): the centre delta itself
    funext k
    fin_cases k <;> simp [h0, h1, h2]
  · -- (1, 0, 1): Brick A's countermodel — a corner drops into the centre
    exfalso
    have hmarg : margEntropy hbExhibitEntropy (c 1) + bowlLandscape 1
        < margEntropy hbExhibitEntropy (c 0 - 1) + bowlLandscape 0 := by
      rw [h0, h1, hb0, hb1]
      show margEntropy hbExhibitEntropy 0 + 0
        < margEntropy hbExhibitEntropy 0 + 1
      rw [hm0]
      linarith
    exact hrest _ (landRevStep_of_marginal hbExhibitEntropy bowlLandscape
      c 0 1 (Or.inl rfl) (by omega) hmarg)
  · -- (1, 1, 0): the corner quantum drops into the centre
    exfalso
    have hmarg : margEntropy hbExhibitEntropy (c 1) + bowlLandscape 1
        < margEntropy hbExhibitEntropy (c 0 - 1) + bowlLandscape 0 := by
      rw [h0, h1, hb0, hb1]
      show margEntropy hbExhibitEntropy 1 + 0
        < margEntropy hbExhibitEntropy 0 + 1
      rw [hm0, hm1]
      linarith
    exact hrest _ (landRevStep_of_marginal hbExhibitEntropy bowlLandscape
      c 0 1 (Or.inl rfl) (by omega) hmarg)
  · -- (2, 0, 0): the corner delta sheds a quantum toward the centre
    exfalso
    have hmarg : margEntropy hbExhibitEntropy (c 1) + bowlLandscape 1
        < margEntropy hbExhibitEntropy (c 0 - 1) + bowlLandscape 0 := by
      rw [h0, h1, hb0, hb1]
      show margEntropy hbExhibitEntropy 0 + 0
        < margEntropy hbExhibitEntropy 1 + 1
      rw [hm0, hm1]
      linarith
    exact hrest _ (landRevStep_of_marginal hbExhibitEntropy bowlLandscape
      c 0 1 (Or.inl rfl) (by omega) hmarg)

-- ============================================================================
-- RNE-B2 (exhibit). RTE's graded seat — K-RNE-THERMAL FIRES
-- ============================================================================

/-- **The corner delta rests on the graded seat** (proved,
exhibit): `![2, 0, 0]` — both quanta on seat `0`, a CORNER —
is a rest point of the landscaped reversed flow on RTE's
graded landscape `exhibitPhi = ![0, 0, 1]`. Its only candidate
move, a quantum onto the centre seat, would gain
`log 2` of marginal-plus-height against the corner's last
quantum's `log (3/2)`: concentration at the corner is
landscaped-entropy-cheaper than spreading onto the equally
low centre seat, so no move descends. -/
theorem exhibit_graded_corner_rest :
    IsLandRevRest hbExhibitEntropy exhibitPhi ![2, 0, 0] := by
  intro c' hstep
  obtain ⟨i, j, hadj, hi, rfl, hlt⟩ := hstep
  have hdiff := landEntropy_moveMass_sub hbExhibitEntropy exhibitPhi
    ![2, 0, 0] i j hadj hi
  obtain ⟨hm0, hm1⟩ := exhibit_marginals
  have h32 : Real.log 3 < 2 * Real.log 2 := exhibit_entropy_values.2.2.2
  fin_cases i <;> fin_cases j <;>
    norm_num [Neighbours] at hadj <;>
    norm_num at hi <;>
    norm_num [exhibitPhi] at hdiff <;>
    norm_num [exhibitPhi] at hlt <;>
    (rw [hm0, hm1] at hdiff; linarith)

/-- **The centre delta also rests on the graded seat**
(proved, exhibit): `![0, 2, 0]` is a rest point too — the
graded landscape's bottom is FLAT (seats `0` and `1` both at
height `0`), and the reversed flow rests at either of its
minimum seats. The centre is a rest point, but it is not
selected: it shares the bottom with a corner. -/
theorem exhibit_graded_center_rest :
    IsLandRevRest hbExhibitEntropy exhibitPhi ![0, 2, 0] := by
  intro c' hstep
  obtain ⟨i, j, hadj, hi, rfl, hlt⟩ := hstep
  have hdiff := landEntropy_moveMass_sub hbExhibitEntropy exhibitPhi
    ![0, 2, 0] i j hadj hi
  obtain ⟨hm0, hm1⟩ := exhibit_marginals
  have h32 : Real.log 3 < 2 * Real.log 2 := exhibit_entropy_values.2.2.2
  fin_cases i <;> fin_cases j <;>
    norm_num [Neighbours] at hadj <;>
    norm_num at hi <;>
    norm_num [exhibitPhi] at hdiff <;>
    norm_num [exhibitPhi] at hlt <;>
    (rw [hm0, hm1] at hdiff; linarith)

/-- **A legal landscaped step empties the centre into the
corner** (proved, exhibit): from the split `![1, 1, 0]` a
landscaped reversed step moves the CENTRE seat's quantum into
the corner seat `0`, landing on the corner delta `![2, 0, 0]`.
The marginals: the corner's next quantum gains `log (3/2)`;
the centre's last quantum carries `log 2`; both seats sit at
landscape height `0`, so the plain anti-diffusion inequality
decides — and it points AWAY from the centre. -/
theorem exhibit_graded_step_to_corner :
    LandRevStep hbExhibitEntropy exhibitPhi ![1, 1, 0] ![2, 0, 0] := by
  obtain ⟨hm0, hm1⟩ := exhibit_marginals
  have h32 : Real.log 3 < 2 * Real.log 2 := exhibit_entropy_values.2.2.2
  have hmove : moveMass ![1, 1, 0] 1 0 = ![2, 0, 0] := by
    funext k
    fin_cases k <;> simp [moveMass]
  have h10 : (![1, 1, 0] : Fin 3 → ℕ) 0 = 1 := by norm_num
  have h11 : (![1, 1, 0] : Fin 3 → ℕ) 1 = 1 := by norm_num
  have hp0 : exhibitPhi 0 = 0 := by norm_num [exhibitPhi]
  have hp1 : exhibitPhi 1 = 0 := by norm_num [exhibitPhi]
  have hmarg : margEntropy hbExhibitEntropy ((![1, 1, 0] : Fin 3 → ℕ) 0)
        + exhibitPhi 0
      < margEntropy hbExhibitEntropy ((![1, 1, 0] : Fin 3 → ℕ) 1 - 1)
        + exhibitPhi 1 := by
    rw [h10, h11, hp0, hp1]
    show margEntropy hbExhibitEntropy 1 + 0
      < margEntropy hbExhibitEntropy 0 + 0
    rw [hm0, hm1]
    linarith
  have hstep := landRevStep_of_marginal hbExhibitEntropy exhibitPhi
    ![1, 1, 0] 1 0 (Or.inr rfl) (by norm_num) hmarg
  rwa [hmove] at hstep

/-- **The graded landscape's thermal centre, exactly**
(proved): the corpus's `thermalCenter` (the ICDT seat's
Gibbs-weighted mean position) of RTE's graded landscape at
β = 1, at seat positions `0, 1, 2`, is
`(1 + 2e⁻¹)/(2 + e⁻¹) ≈ 0.733` — strictly between the two
minimum seats `0` and `1`, at NO seat. This is the
0.269-style point of the graded seat. -/
theorem exhibit_graded_thermal_center :
    thermalCenter exhibitPhi 1 ![0, 1, 2]
      = (1 + 2 * Real.exp (-1)) / (2 + Real.exp (-1))
    ∧ 0 < thermalCenter exhibitPhi 1 ![0, 1, 2]
    ∧ thermalCenter exhibitPhi 1 ![0, 1, 2] < 1 := by
  have htc : thermalCenter exhibitPhi 1 ![0, 1, 2]
      = (1 + 2 * Real.exp (-1)) / (2 + Real.exp (-1)) := by
    norm_num [thermalCenter, Fin.sum_univ_three,
      ModularVariance.gibbsProb, ModularVariance.partSum, exhibitPhi]
    have hZ : (2 + Real.exp (-1)) ≠ 0 := by
      have hx := Real.exp_pos (-1)
      linarith
    field_simp
  have hx0 : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
  have hx1 : Real.exp (-1) < 1 := by
    rw [Real.exp_neg]
    apply inv_lt_one_of_one_lt₀
    rw [Real.one_lt_exp_iff]
    norm_num
  refine ⟨htc, ?_, ?_⟩
  · rw [htc]
    exact div_pos (by linarith) (by linarith)
  · rw [htc, div_lt_one (by linarith)]
    linarith

/-- **The mass centres of the graded seat's rest seats,
exactly** (proved): the corner rest delta sits at mass centre
`0`; the centre rest delta at mass centre `1` (the geometric
centre); and the forward bent flow's rest distribution
`(5/16, 5/16, 3/8)` of RTE-2 — the moved rest point of the
FORWARD dynamics on this same landscape — sits at mass centre
`17/16`. The reversed flow's rest points are the first two;
neither is the thermal centre `≈ 0.733`, and the second is
not the forward rest point's centre either. -/
theorem exhibit_graded_rest_centers :
    massCenter ![2, 0, 0] ![0, 1, 2] = 0
    ∧ massCenter ![0, 2, 0] ![0, 1, 2] = 1
    ∧ massCenter ![5 / 16, 5 / 16, 3 / 8] ![0, 1, 2] = 17 / 16 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [massCenter, Fin.sum_univ_three]

/-- **K-RNE-THERMAL FIRES** (proved — the pre-registered kill,
at full rank): on RTE's graded seat, the landscaped reversed
flow does NOT rest at the geometric centre, and it does not
rest at the thermal centre either. The centre delta
`![0, 2, 0]` rests — but so does the CORNER delta
`![2, 0, 0]`, and a legal landscaped step from `![1, 1, 0]`
empties the centre seat into that corner: the centre is not
selected. The thermal centre of the landscape is
`(1 + 2e⁻¹)/(2 + e⁻¹) ≈ 0.733`, strictly between the two rest
seats; the flow's rest points have mass centres exactly `0`
and `1`, so the flow rests at the thermal centre under no
reading — nor at the forward bent flow's rest centre `17/16`.
What the reversed flow rests at is the landscape's MINIMUM
SET: the graded landscape's flat bottom `{0, 1}`, of which
the geometric centre is merely one member. Read together
with the bowl (B1): a centre is earned exactly when the
landscape's minimum is the centre alone. The reversed
dynamics seeks the landscape's minimum — not its geometric
centre, and not its thermal centre. No definition was
adjusted to soften this. -/
theorem exhibit_graded_rest_countermodel :
    IsLandRevRest hbExhibitEntropy exhibitPhi ![2, 0, 0]
    ∧ IsLandRevRest hbExhibitEntropy exhibitPhi ![0, 2, 0]
    ∧ LandRevStep hbExhibitEntropy exhibitPhi ![1, 1, 0] ![2, 0, 0]
    ∧ massCenter ![2, 0, 0] ![0, 1, 2] = 0
    ∧ massCenter ![0, 2, 0] ![0, 1, 2] = 1
    ∧ massCenter ![5 / 16, 5 / 16, 3 / 8] ![0, 1, 2] = 17 / 16
    ∧ 0 < thermalCenter exhibitPhi 1 ![0, 1, 2]
    ∧ thermalCenter exhibitPhi 1 ![0, 1, 2] < 1 :=
  ⟨exhibit_graded_corner_rest, exhibit_graded_center_rest,
    exhibit_graded_step_to_corner,
    exhibit_graded_rest_centers.1, exhibit_graded_rest_centers.2.1,
    exhibit_graded_rest_centers.2.2,
    exhibit_graded_thermal_center.2.1,
    exhibit_graded_thermal_center.2.2⟩

end ThetLogos
