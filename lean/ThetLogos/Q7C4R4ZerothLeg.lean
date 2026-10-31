import Mathlib.Tactic
import ThetLogos.Q7C4R4Trifecta

namespace ThetLogos

/-!
# ThetLogos.Q7C4R4ZerothLeg — T-R4-1: the Zeroth leg, contact form, DECIDED

**Status: TEST EXECUTED — K-T-R4-1 FIRES at the named seat.
NO CLAIM. Dials 0/4. No measured number.** Governing pack:
`routeb-general-scratch/pack-t-r4-1.md`; governing memo:
`routeb-general-scratch/scoping-q7c4r4-trifecta-2026-10-30.md`
§2.3(ii) + §4; registration: `ThetLogos.Q7C4R4Trifecta`
(Q7CR-T0), whose schemas `ContactCompatible` /
`LegZerothContact` are instantiated here, not restated.

## The registered target, verbatim (memo §2.3(ii))

> **(ii) FINITE-TESTABLE — the contact form (brick T-R4-1).**
> Define equilibrium by an operation, not a label: states
> ρ, σ on the composite are *contact-compatible* if a stated
> equilibration step (pair the systems, apply a stated coupling
> step, take marginals) drives the pair to a common Gibbs state
> `gibbsState K β` (KMSBridge's owned family) at a single β.
> The Zeroth content is then a real claim:
> **contact-compatibility is transitive.** Falsifiable — finite
> equilibration relations fail transitivity in general
> (pairwise equilibration at different β's through different
> couplings) — and the brick's statement must fix its coupling
> class broadly enough that transitivity has content; if at
> build time the only statable coupling collapses the relation
> back to "same β of the joint state," the brick reports that
> collapse on its face and the leg's witness is downgraded to
> the weak form, labeled tautological. Kill: a certified
> intransitive triple at the instantiated seat kills the
> contact form; the leg reverts to pure definition.

Memo §4: "**K-T-R4-1** a certified intransitive triple ⇒ the
contact form dead; leg = definition + weak form labeled
tautological."

The weak form ("same temperature" as the kernel of any
β-functional) is REFUSED AS A TEST at registration —
reflexive/symmetric/transitive for free for any function; it
witnesses nothing.

## The stated step, the seat, the coupling class

**Step (`contactStep`, §1, a definition in this module, in
owned vocabulary).** Pair the two states, apply the complete-
mixing coupling, and take marginals: both marginals are
replaced by the pair average `(2⁻¹) • (ρ + σ)`. This is the
finite thermal-contact equilibration that conserves the pair's
total state and equalizes the two marginals in one step. The
step is seat-generic (stated for every `Fin N` seat at once).

**Seat (named, with the downgrade stated on the face).** The
certified test is executed at the FACTOR-sized seat
`Fin 2` with operator `seatK = diagonal ![0, 1]` — NOT at the
composite seat. Downgrade from "the composite", stated plainly:
the composite (`Fin 448`-scale) seat is not the seat of this
certificate; the kill below is seat-scoped to `(Fin 2, seatK)`,
and §3 proves the same triple intransitive for EVERY operator
`K` on `Fin 2` whose Gibbs partition function never vanishes,
so the verdict is a property of the step and the coupling
class, not of one degenerate operator (at `seatK` the Gibbs
family genuinely varies with `β`: `gibbsState seatK β` is
diagonal with entries in ratio `exp (-β)`, §3).

**Coupling class.** All pairs of matrices on the seat under
the one stated step — the broadest class the step defines;
nothing is restricted pair-by-pair.

## The content test, applied on the face

Under `contactStep`, `ρ` and `σ` are contact-compatible iff
their pair average IS a Gibbs state of `K` at some single `β`
(§1, `contactCompatible_contactStep_iff`). This relation is:

- **not total**: at the seat, `0` is not compatible with `0`
  (§4) — the average `0` is no Gibbs state, since a Gibbs
  state at an operator with nonvanishing partition function
  is never `0` (§2);
- **not the refused weak form**: it is NOT the kernel of any
  functional whatsoever (§4, `contact_not_kernel_of_functional`)
  — every kernel relation is reflexive, and this one is not
  (`0` is not compatible with itself, while `0` IS compatible
  with `1`). It is also not "same β of the joint state": the
  average being on the Gibbs curve is a joint condition on the
  pair, not an equality of per-state temperatures.

So transitivity here has content — and it FAILS.

## Verdict

**K-T-R4-1 FIRES (seat-scoped, `(Fin 2, seatK)`, and in fact
at every `Fin 2` operator with everywhere-nonvanishing
partition function).** The certified intransitive triple is
`ρ = 0`, `σ = 1`, `τ = 0`: the pair average of `0` and `1` is
`(2⁻¹) • 1 = gibbsState K 0` at ANY operator `K` (§2), so
`0 ~ 1` and `1 ~ 0`; but `0 ~ 0` would force the average `0`
to be a Gibbs state, which it never is at the seat (§§2–3).
Hence `LegZerothContact contactStep seatK` is FALSE (§4).
The Zeroth leg reverts to pure definition; its only surviving
witness is the weak form, labeled tautological at registration.
The Third leg (K-T-R4-2; degeneracy form) is untouched.
Item-6 fence inherited: nothing here requires the R⁴ factor
to be spacetime rather than the corpus's Minkowski seat.
-/

/-! ## §1. The stated contact step and its compatibility form -/

/-- **The stated contact step (complete mixing).** Pair the two
    states, apply the coupling that replaces each marginal by
    the pair average, and read off the two marginals — both are
    `(2 : ℂ)⁻¹ • (ρ + σ)`. Built only from owned vocabulary
    (matrix addition and scalar multiplication on the seat).
    Tier T2 (definition). -/
noncomputable def contactStep {N : ℕ}
    (p : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ :=
  ((2 : ℂ)⁻¹ • (p.1 + p.2), (2 : ℂ)⁻¹ • (p.1 + p.2))

/-- Contact-compatibility under the stated step, unfolded:
    `ρ` and `σ` are compatible iff their pair average is a
    Gibbs state of `K` at some single `β`. Tier T1. -/
theorem contactCompatible_contactStep_iff {N : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ)
    (ρ σ : Matrix (Fin N) (Fin N) ℂ) :
    ContactCompatible contactStep K ρ σ ↔
      ∃ β : ℝ, (2 : ℂ)⁻¹ • (ρ + σ) = gibbsState K β := by
  constructor
  · rintro ⟨β, h1, -⟩
    exact ⟨β, h1⟩
  · rintro ⟨β, h⟩
    exact ⟨β, h, h⟩

/-! ## §2. Gibbs facts at `β = 0`, and Gibbs states are nonzero -/

/-- At `β = 0` the Gibbs state of ANY operator on `Fin 2` is
    `(2 : ℂ)⁻¹ • 1`: the weight is `exp 0 = 1` and the partition
    function is `trace 1 = 2`. Tier T1. -/
theorem gibbsState_at_zero (K : Matrix (Fin 2) (Fin 2) ℂ) :
    gibbsState K 0 = (2 : ℂ)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold gibbsState gibbsZ gibbsWeight
  simp [Matrix.trace_one]

/-- A Gibbs state on `Fin 2` whose partition function does not
    vanish is never the zero matrix: the weight `exp (-βK)` is
    a unit (the corpus's landed `exp_smul_mul_exp_neg_smul`
    gives its two-sided inverse), so it is nonzero, and the
    normalizing scalar `Z⁻¹` is nonzero. Tier T1. -/
theorem gibbsState_ne_zero_of_gibbsZ_ne
    (K : Matrix (Fin 2) (Fin 2) ℂ) (β : ℝ)
    (hZ : gibbsZ K β ≠ 0) : gibbsState K β ≠ 0 := by
  intro h
  have hW : gibbsWeight K β = 0 := by
    have h' : (gibbsZ K β)⁻¹ • gibbsWeight K β = 0 := h
    rcases smul_eq_zero.mp h' with h1 | h1
    · exact absurd (inv_eq_zero.mp h1) hZ
    · exact h1
  have hinv := exp_smul_mul_exp_neg_smul K (-(β : ℂ))
  rw [gibbsWeight] at hW
  rw [hW, zero_mul] at hinv
  have h10 : (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 0
      = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 :=
    congrFun (congrFun hinv 0) 0
  simp at h10

/-! ## §3. The named seat: `Fin 2`, `K = diagonal ![0, 1]` -/

/-- **The seat operator**: the diagonal operator on `Fin 2` with
    entries `0` and `1` — a factor-sized seat, named on the face
    (see the header for the downgrade from the composite).
    Tier T2 (definition). -/
def seatK : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![0, 1]

/-- The Gibbs weight at the seat is diagonal, with entries
    `1` and `exp (-β)`: the exponential of a diagonal matrix is
    diagonal (`Matrix.exp_diagonal`, landed Mathlib), and the
    scalar exponential at entry `0` is `exp 0 = 1`. So the seat's
    Gibbs family genuinely varies with `β`. Tier T1. -/
theorem seat_gibbsWeight (β : ℝ) :
    gibbsWeight seatK β
      = Matrix.diagonal ![1, NormedSpace.exp (-(β : ℂ))] := by
  unfold gibbsWeight seatK
  rw [← Matrix.diagonal_smul]
  have hsmul : (-(β : ℂ)) • (![0, 1] : Fin 2 → ℂ) = ![0, -(β : ℂ)] := by
    funext i
    fin_cases i <;> simp
  rw [hsmul, Matrix.exp_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

/-- The seat's partition function never vanishes: it is
    `1 + exp (-β)`, a sum of `1` and a positive real, read in
    `ℂ`. Tier T1. -/
theorem seat_gibbsZ_ne_zero (β : ℝ) : gibbsZ seatK β ≠ 0 := by
  have hexp : NormedSpace.exp (-(β : ℂ))
      = ((Real.exp (-β) : ℝ) : ℂ) := by
    have h1 : (-(β : ℂ)) = ((-β : ℝ) : ℂ) := by push_cast; ring
    rw [h1]
    exact (congr_fun Complex.exp_eq_exp_ℂ (((-β : ℝ) : ℂ))).symm.trans
      (Complex.ofReal_exp (-β)).symm
  unfold gibbsZ
  rw [seat_gibbsWeight, Matrix.trace_diagonal, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hexp]
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re,
    Complex.zero_re] at hre
  have hpos := Real.exp_pos (-β)
  linarith

/-- The seat's Gibbs states are never zero. Tier T1. -/
theorem seat_gibbsState_ne_zero (β : ℝ) : gibbsState seatK β ≠ 0 :=
  gibbsState_ne_zero_of_gibbsZ_ne seatK β (seat_gibbsZ_ne_zero β)

/-! ## §4. The certified intransitive triple, and K-T-R4-1 -/

/-- **First leg of the triple, at ANY operator on `Fin 2`**:
    `0` is contact-compatible with `1` — the pair average is
    `(2 : ℂ)⁻¹ • 1 = gibbsState K 0` (§2). Tier T1. -/
theorem contactCompatible_zero_one (K : Matrix (Fin 2) (Fin 2) ℂ) :
    ContactCompatible contactStep K 0 1 := by
  rw [contactCompatible_contactStep_iff]
  refine ⟨0, ?_⟩
  rw [gibbsState_at_zero]
  simp

/-- **Second leg of the triple, at ANY operator on `Fin 2`**:
    `1` is contact-compatible with `0` (the step is symmetric in
    the pair). Tier T1. -/
theorem contactCompatible_one_zero (K : Matrix (Fin 2) (Fin 2) ℂ) :
    ContactCompatible contactStep K 1 0 := by
  rw [contactCompatible_contactStep_iff]
  refine ⟨0, ?_⟩
  rw [gibbsState_at_zero]
  simp

/-- **The broken leg**: at any operator on `Fin 2` whose
    partition function never vanishes, `0` is NOT
    contact-compatible with `0` — its pair average is `0`,
    which is no Gibbs state (§2). This is also the
    content-test witness: the relation is not total, and not
    reflexive. Tier T1. -/
theorem not_contactCompatible_zero_zero
    (K : Matrix (Fin 2) (Fin 2) ℂ)
    (hZ : ∀ β : ℝ, gibbsZ K β ≠ 0) :
    ¬ ContactCompatible contactStep K 0 0 := by
  rw [contactCompatible_contactStep_iff]
  rintro ⟨β, h⟩
  simp at h
  exact gibbsState_ne_zero_of_gibbsZ_ne K β (hZ β) h.symm

/-- **The kill, generic form**: at any operator on `Fin 2`
    whose partition function never vanishes, the registered
    contact-form Zeroth leg `LegZerothContact contactStep K`
    is FALSE — the triple `0, 1, 0` is intransitive there.
    Tier T1. -/
theorem legZerothContact_false_of_gibbsZ_ne
    (K : Matrix (Fin 2) (Fin 2) ℂ)
    (hZ : ∀ β : ℝ, gibbsZ K β ≠ 0) :
    ¬ LegZerothContact contactStep K := by
  intro h
  exact not_contactCompatible_zero_zero K hZ
    (h 0 1 0 (contactCompatible_zero_one K)
      (contactCompatible_one_zero K))

/-- **Content test, formal**: at the seat, contact-compatibility
    under the stated step is not the kernel of ANY functional —
    in particular it is not the refused weak form ("same β" of
    a β-functional), every instance of which is reflexive,
    while this relation has `0 ~ 1` but `0 ≁ 0`. Tier T1. -/
theorem contact_not_kernel_of_functional :
    ¬ ∃ f : Matrix (Fin 2) (Fin 2) ℂ → ℝ,
      ∀ ρ σ : Matrix (Fin 2) (Fin 2) ℂ,
        ContactCompatible contactStep seatK ρ σ ↔ f ρ = f σ := by
  rintro ⟨f, hf⟩
  have h00 : ContactCompatible contactStep seatK 0 0 :=
    (hf 0 0).mpr rfl
  exact not_contactCompatible_zero_zero seatK seat_gibbsZ_ne_zero h00

/-- **K-T-R4-1 FIRES at the named seat `(Fin 2, seatK)`.** The
    certified intransitive triple is `ρ = 0`, `σ = 1`, `τ = 0`:
    `ContactCompatible contactStep seatK 0 1` and
    `ContactCompatible contactStep seatK 1 0` hold (pair average
    `= gibbsState seatK 0`), `ContactCompatible contactStep
    seatK 0 0` fails (pair average `0` is no Gibbs state), and
    consequently the registered leg `LegZerothContact
    contactStep seatK` is false. The contact form is dead at
    this seat; the Zeroth leg reverts to pure definition, its
    only surviving witness the weak form labeled tautological.
    Tier T1. -/
theorem k_t_r4_1_fires :
    ContactCompatible contactStep seatK 0 1 ∧
      ContactCompatible contactStep seatK 1 0 ∧
      ¬ ContactCompatible contactStep seatK 0 0 ∧
      ¬ LegZerothContact contactStep seatK :=
  ⟨contactCompatible_zero_one seatK, contactCompatible_one_zero seatK,
    not_contactCompatible_zero_zero seatK seat_gibbsZ_ne_zero,
    legZerothContact_false_of_gibbsZ_ne seatK seat_gibbsZ_ne_zero⟩

end ThetLogos
