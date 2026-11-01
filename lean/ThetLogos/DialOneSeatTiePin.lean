import Mathlib.Tactic
import ThetLogos.HyperchargeForcing
import ThetLogos.SMFermions
import ThetLogos.ThreeGen

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation

namespace ThetLogos.DialOneSeatTiePin

/-!
# ThetLogos.DialOneSeatTiePin — D1-A′: the seat-tie strengthening, PINNED

Governing text: `whitepaper/dial1-scoping-2026-11-01.md` §3.
Stage 1 of the D1-A′ gauntlet, fired by Jeff's order 2026-11-01
("pin it and run it"): STEP 0 (the common hypercharge matrix)
plus the STATEMENT PIN — definitions and the forcing statement
as a `Prop`, frozen names, read-backs, and the one proved
headline of STEP 0 (commonality). The pre-checks are the next
stage, NOT this brick.

## Relabeling fence

D1-A′ is a NEW ENTRY under the relabeling rule. D1-A's kill
stands untouched beside it at full rank:
`ThetLogos.HyperchargeForcing.dial1_forcing_killed` — at the
landed condition set, `piFlip` (π₁ with the ν_R seat acting by
`star a.u1`) satisfies every clause and its ν_R lift weight is
`4` against the table's `0`. Nothing in this module rescues,
weakens, or re-reads that theorem; `HyperchargeForcing.lean`
is cited, never edited.

## STEP 0 — the COMMON HYPERCHARGE MATRIX (Jeff's coinage)

* `commonHyperchargeMatrix` — **the COMMON HYPERCHARGE
  MATRIX** (Jeff's term, verbatim): the diagonal U(1)-weight
  operator on the per-generation fermion seat space `ℂ³²`,
  whose entry at seat `i` is the seated lifted weight
  `W i + W (partner i)`, built from the landed seat/weight
  vocabulary — `ThetLogos.Track1RouteB.W` (π₁'s integer slot
  weights along its surviving direction) and the landed J
  seat-pairing `partner` (`Scaffold32`). This definition
  names the TARGET object: it is not a hypothesis of the
  condition set, and the K-D1A′-2 fence on the tie clause and
  the hypotheses is unchanged.
* `commonHyperchargeMatrix_diag` (proved): at every fermion
  seat, the entry is exactly the seated weight,
  `commonHyperchargeMatrix (fermionIndex f c) (fermionIndex f c)
  = 3 * (hypercharge f : ℂ)` — the matrix carries the seated
  `3 • Y_f` weights of ONE generation, cited by the landed
  names `fermionIndex` / `hypercharge` (`SMFermions`).
* `commonHyperchargeMatrix3` — the full three-generation
  weight operator on `ℂ⁹⁶`, seated from the same data with
  the generation index inert — the operator form of the
  landed three-generation weight data `hypercharge3`
  (`SMFermions`: generation-blind by imposition, T2;
  `replication_imposed`, T1). Vocabulary note, at full rank:
  the corpus seats NO three-generation weight *matrix* by a
  landed name; `hypercharge3` + `fermionIndex3` are the
  seated data, and this operator is their seat-complete form.
  Its fermion-seat entries are `3 * (hypercharge3 f g : ℂ)`
  (`commonHyperchargeMatrix3_diag`, proved).
* **COMMONALITY, proved as stated**
  (`commonHyperchargeMatrix3_eq_triplication`): the full
  three-generation weight operator IS the one common matrix
  repeated by triplication —
  `commonHyperchargeMatrix3 = smDirac3diag commonHyperchargeMatrix`,
  the corpus's landed triplication `ThreeGen.smDirac3diag`
  (`D₃ = D₁ ⊗ I₃`, block form, the same matrix on each
  generation block). The seated generations DO share one
  matrix. Fence: triplication itself is IMPOSED, not derived
  (`ThreeGen` header) — commonality is a fact about the
  corpus's seated operator, not about nature.

## What is pinned

* `DialOneBase` — the landed D1-A condition set, assembled as
  one predicate. The landed module packages no such predicate:
  the clauses live as the inline hypotheses of
  `dial1_forcing_killed`, and they are conjoined here by their
  landed names and shapes, verbatim in substance —
  representation laws (`afMul` / `afAdd` / `afStar` / `afOne` /
  `afZero`), faithfulness (`Function.Injective`), grading
  (`gammaF`), order-zero against the J-opposite
  `ρπ := piOp ∘ π`, first-order against `DF_oneGen` with the
  Yukawa data universally quantified, and unimodularity of
  the U(1) lift (a primitive direction `(α, β)` with
  `det π (u1ParamGen α β t) = 1` for all `t`). No condition
  added, none dropped; the assembly is bookkeeping, stated
  as such. J-compatibility enters in its landed D1-A form:
  order-zero and first-order are stated against the
  J-opposite `piOp ∘ π` (`piOp M = UJ * M.transpose * UJ`),
  and `DF_oneGen`'s own J-compatibility is the landed theorem
  `DF_oneGen_J_compat`, not a hypothesis on `π`.
* `SeatTie` — the one new clause. For the `π` in question, at
  each particle seat `fermionIndex f c`, the U(1)-lift weight
  equals the lift weight at the seat's J-mirror seat
  `partner (fermionIndex f c)`, where the lift weight at a
  seat `s` is stated in the landed forcing vocabulary of
  `dial1_forcing_killed` / `piFlip_weights_not_proportional`:
  the lifted eigenvalue
  `(π (u1ParamGen α β t) * piOp (π (u1ParamGen α β t))) s s`,
  for every direction `(α, β)` and every `t`. The J
  seat-pairing is the landed `partner` (`Scaffold32`).
  **No weight value is named in the clause. No `hypercharge`,
  no table, no fixed Yukawa value occurs in the clause or
  anywhere upstream of it.**
* `DialOneStrengthened` — base ∧ tie, as one predicate.
* `DialOneForcing` — the forcing statement as a Prop `def`,
  NOT a theorem, RESTATED over the STEP-0 object: every `π`
  satisfying the strengthened set has, along every unimodular
  direction, its lifted sector weights proportional to **the
  COMMON HYPERCHARGE MATRIX** — a single scalar `κ` (the U(1)
  normalization) with lifted eigenvalue
  `exp (κ * t * (common matrix entry at the sector seat) * I)`
  at every sector. By `commonHyperchargeMatrix_diag` this is
  exactly the landed comparison form of
  `dial1_forcing_killed` (`exp (κ * 3 * Y_f * t * I)`), with
  the table packaged into the named matrix.

**The asymmetry, in one sentence (the entire content of the
entry): the hypercharge table occurs nowhere among the
hypotheses — not in the base set, not in the tie — and the
COMMON HYPERCHARGE MATRIX occurs only in the conclusion of
`DialOneForcing`, as the claimed target.**

## The kills, pre-registered on the face

* **K-D1A′-1 (counterexample).** Any `π′` satisfying the
  strengthened set whose weights are not proportional to the
  table kills D1-A′ at that set, permanently.
* **K-D1A′-2 (vacuity / circularity).** If the seat tie, once
  formalized, is shown to fix any seat's weight directly —
  i.e. over the base condition set it is equivalent to a
  weight equation — or if any `Y_f` value, the table, or
  fixed Yukawa values are needed upstream, it is a fit in
  costume: kill on sight.
* **K-D1A′-3 (consistency).** If `π₁` itself fails the tie,
  the strengthened set excludes the corpus's one landed
  model: the entry dies as mis-posed.

The pre-checks named under K-D1A′-2 — the tie must hold for
`π₁` and fail for `piFlip` before any forcing attempt is
priced further — are the NEXT stage. **This pin asserts
neither `SeatTie pi1` nor `¬ SeatTie piFlip`, and asserts
nothing about whether the tie is automatic, restrictive, or
equivalent to a weight equation.**

**NO CLAIM. Dial 1 = 0; all dials 0/4. A pin is not a
derivation: parts of any official statement closed by this
module: 0.**
-/

/-! ## STEP 0 — the COMMON HYPERCHARGE MATRIX -/

/-- **The COMMON HYPERCHARGE MATRIX** (Jeff's coinage): the
diagonal U(1)-weight operator on the per-generation fermion
seat space `ℂ³²`. Its entry at seat `i` is the seated lifted
weight `W i + W (partner i)`, from the landed vocabulary
`ThetLogos.Track1RouteB.W` (π₁'s integer slot weights) and
`partner` (the landed J seat-pairing, `Scaffold32`). This
names the TARGET object of D1-A′; it is not a hypothesis of
the condition set. -/
def commonHyperchargeMatrix : Matrix I32 I32 ℂ :=
  Matrix.diagonal (fun i => ((ThetLogos.Track1RouteB.W i
    + ThetLogos.Track1RouteB.W (partner i) : ℤ) : ℂ))

/-- Read-back: the COMMON HYPERCHARGE MATRIX is visibly the
registered diagonal operator. -/
theorem commonHyperchargeMatrix_unfold :
    commonHyperchargeMatrix
      = Matrix.diagonal (fun i => ((ThetLogos.Track1RouteB.W i
          + ThetLogos.Track1RouteB.W (partner i) : ℤ) : ℂ)) :=
  rfl

/-- **The seated weights, identified** (proved): at every
fermion seat `fermionIndex f c`, the COMMON HYPERCHARGE
MATRIX's entry is exactly `3 * (hypercharge f : ℂ)` — the
seated `3 • Y_f` weight of one generation, by the landed
names `fermionIndex` / `hypercharge` (`SMFermions`). The
integer identities `W (fermionIndex f c) + W (partner
(fermionIndex f c)) = 3 • Y_f` are finite checks (`decide`)
per sector. -/
theorem commonHyperchargeMatrix_diag (f : SMFermion)
    (c : Fin 3) :
    commonHyperchargeMatrix (fermionIndex f c) (fermionIndex f c)
      = 3 * (hypercharge f : ℂ) := by
  rw [commonHyperchargeMatrix, Matrix.diagonal_apply_eq]
  cases f
  · have h : ThetLogos.Track1RouteB.W (fermionIndex SMFermion.nuL c)
        + ThetLogos.Track1RouteB.W
            (partner (fermionIndex SMFermion.nuL c)) = -3 := by
      fin_cases c <;> decide
    rw [h]; norm_num [hypercharge]
  · have h : ThetLogos.Track1RouteB.W (fermionIndex SMFermion.eL c)
        + ThetLogos.Track1RouteB.W
            (partner (fermionIndex SMFermion.eL c)) = -3 := by
      fin_cases c <;> decide
    rw [h]; norm_num [hypercharge]
  · have h : ThetLogos.Track1RouteB.W (fermionIndex SMFermion.uL c)
        + ThetLogos.Track1RouteB.W
            (partner (fermionIndex SMFermion.uL c)) = 1 := by
      fin_cases c <;> decide
    rw [h]; norm_num [hypercharge]
  · have h : ThetLogos.Track1RouteB.W (fermionIndex SMFermion.dL c)
        + ThetLogos.Track1RouteB.W
            (partner (fermionIndex SMFermion.dL c)) = 1 := by
      fin_cases c <;> decide
    rw [h]; norm_num [hypercharge]
  · have h : ThetLogos.Track1RouteB.W (fermionIndex SMFermion.nuR c)
        + ThetLogos.Track1RouteB.W
            (partner (fermionIndex SMFermion.nuR c)) = 0 := by
      fin_cases c <;> decide
    rw [h]; norm_num [hypercharge]
  · have h : ThetLogos.Track1RouteB.W (fermionIndex SMFermion.eR c)
        + ThetLogos.Track1RouteB.W
            (partner (fermionIndex SMFermion.eR c)) = -6 := by
      fin_cases c <;> decide
    rw [h]; norm_num [hypercharge]
  · have h : ThetLogos.Track1RouteB.W (fermionIndex SMFermion.uR c)
        + ThetLogos.Track1RouteB.W
            (partner (fermionIndex SMFermion.uR c)) = 4 := by
      fin_cases c <;> decide
    rw [h]; norm_num [hypercharge]
  · have h : ThetLogos.Track1RouteB.W (fermionIndex SMFermion.dR c)
        + ThetLogos.Track1RouteB.W
            (partner (fermionIndex SMFermion.dR c)) = -2 := by
      fin_cases c <;> decide
    rw [h]; norm_num [hypercharge]

/-- **The full three-generation weight operator** on `ℂ⁹⁶`:
the same seated lifted-weight data with the generation
index inert — the operator form of the landed
three-generation weight data `hypercharge3` (`SMFermions`,
generation-blind by imposition). -/
def commonHyperchargeMatrix3 : Matrix I96 I96 ℂ :=
  Matrix.diagonal (fun i : I96 => ((ThetLogos.Track1RouteB.W i.1
    + ThetLogos.Track1RouteB.W (partner i.1) : ℤ) : ℂ))

/-- Read-back: the full operator is visibly the registered
diagonal operator. -/
theorem commonHyperchargeMatrix3_unfold :
    commonHyperchargeMatrix3
      = Matrix.diagonal (fun i : I96 =>
          ((ThetLogos.Track1RouteB.W i.1
            + ThetLogos.Track1RouteB.W (partner i.1) : ℤ) : ℂ)) :=
  rfl

/-- **The full operator's seated entries** (proved): at every
three-generation fermion seat `fermionIndex3 f c g`, the
entry is `3 * (hypercharge3 f g : ℂ)` — the landed seated
three-generation weight, generation-blind. -/
theorem commonHyperchargeMatrix3_diag (f : SMFermion)
    (c g : Fin 3) :
    commonHyperchargeMatrix3 (fermionIndex3 f c g)
        (fermionIndex3 f c g)
      = 3 * (hypercharge3 f g : ℂ) := by
  have h := commonHyperchargeMatrix_diag f c
  rw [commonHyperchargeMatrix, Matrix.diagonal_apply_eq] at h
  rw [commonHyperchargeMatrix3, Matrix.diagonal_apply_eq]
  dsimp only [fermionIndex3, hypercharge3]
  exact h

/-- **COMMONALITY — proved as stated.** The full
three-generation weight operator IS the COMMON HYPERCHARGE
MATRIX repeated by triplication: the same matrix on each
generation block, in the corpus's landed triplication form
`ThreeGen.smDirac3diag` (`D₃ = D₁ ⊗ I₃`). -/
theorem commonHyperchargeMatrix3_eq_triplication :
    commonHyperchargeMatrix3
      = smDirac3diag commonHyperchargeMatrix := by
  ext ⟨i, g⟩ ⟨j, gp⟩
  by_cases hij : i = j <;> by_cases hgg : g = gp
  · subst hij; subst hgg
    rw [commonHyperchargeMatrix3, Matrix.diagonal_apply_eq,
      smDirac3diag, if_pos rfl, mul_one, commonHyperchargeMatrix,
      Matrix.diagonal_apply_eq]
  · have hne : (i, g) ≠ (j, gp) := fun h => hgg (congrArg Prod.snd h)
    rw [commonHyperchargeMatrix3, Matrix.diagonal_apply_ne _ hne,
      smDirac3diag, if_neg hgg, mul_zero]
  · have hne : (i, g) ≠ (j, gp) := fun h => hij (congrArg Prod.fst h)
    rw [commonHyperchargeMatrix3, Matrix.diagonal_apply_ne _ hne,
      smDirac3diag, commonHyperchargeMatrix,
      Matrix.diagonal_apply_ne _ hij, zero_mul]
  · have hne : (i, g) ≠ (j, gp) := fun h => hij (congrArg Prod.fst h)
    rw [commonHyperchargeMatrix3, Matrix.diagonal_apply_ne _ hne,
      smDirac3diag, if_neg hgg, mul_zero]

/-! ## The statement pin -/

/-- **The landed D1-A condition set, assembled** (bookkeeping
only): the hypotheses of
`ThetLogos.HyperchargeForcing.dial1_forcing_killed`, conjoined
verbatim in substance — representation laws, faithfulness,
grading, order-zero against `piOp ∘ π`, first-order against
`DF_oneGen` with Yukawas universally quantified, and the
existence of a primitive unimodular U(1) direction. -/
def DialOneBase (π : AF → Matrix (Fin 32) (Fin 32) ℂ) : Prop :=
  (∀ a b, π (afMul a b) = π a * π b) ∧
  (∀ a b, π (afAdd a b) = π a + π b) ∧
  (∀ a, π (afStar a) = (π a)ᴴ) ∧
  π afOne = 1 ∧
  π afZero = 0 ∧
  Function.Injective π ∧
  (∀ a, gammaF * π a = π a * gammaF) ∧
  (∀ a b, π a * piOp (π b) = piOp (π b) * π a) ∧
  (∀ (Ynu Ye Yu Yd : ℝ) (a b : AF) (i j : Fin 32),
    ((DF_oneGen Ynu Ye Yu Yd * π a
        - π a * DF_oneGen Ynu Ye Yu Yd) * piOp (π b)
      - piOp (π b) * (DF_oneGen Ynu Ye Yu Yd * π a
        - π a * DF_oneGen Ynu Ye Yu Yd)) i j = 0) ∧
  (∃ (α β : ℤ), Nat.gcd α.natAbs β.natAbs = 1
    ∧ ∀ t, (π (u1ParamGen α β t)).det = 1)

/-- **The seat tie** (the one new clause of D1-A′): at each
particle seat `fermionIndex f c`, the U(1)-lift weight of `π`
— the lifted eigenvalue
`(π (u1ParamGen α β t) * piOp (π (u1ParamGen α β t))) s s`
of the landed forcing vocabulary — equals the lift weight at
the seat's J-mirror seat `partner (fermionIndex f c)`, for
every direction `(α, β)` and every `t`. No weight value, no
`hypercharge`, no table, no Yukawa value occurs in this
clause. -/
def SeatTie (π : AF → Matrix (Fin 32) (Fin 32) ℂ) : Prop :=
  ∀ (α β : ℤ) (t : ℝ) (f : SMFermion) (c : Fin 3),
    (π (u1ParamGen α β t) * piOp (π (u1ParamGen α β t)))
        (fermionIndex f c) (fermionIndex f c)
      = (π (u1ParamGen α β t) * piOp (π (u1ParamGen α β t)))
          (partner (fermionIndex f c)) (partner (fermionIndex f c))

/-- **The strengthened condition set of D1-A′**: the landed
base set ∧ the seat tie, as one predicate. -/
def DialOneStrengthened (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    Prop :=
  DialOneBase π ∧ SeatTie π

/-- **The D1-A′ forcing statement, as a Prop (NOT a theorem)**,
restated over STEP 0's named object: every `π` satisfying
the strengthened set has, along every unimodular direction
`(α, β)`, its lifted sector weights proportional to **the
COMMON HYPERCHARGE MATRIX** — a single scalar `κ` with
lifted eigenvalue
`exp (κ * t * (common matrix entry at the sector seat) * I)`
at every sector `f`. By `commonHyperchargeMatrix_diag` this
is the landed `κ * 3 * Y_f` comparison form of
`dial1_forcing_killed`, with the table packaged into the
named matrix. The matrix occurs ONLY in this conclusion. -/
def DialOneForcing : Prop :=
  ∀ (π : AF → Matrix (Fin 32) (Fin 32) ℂ),
    DialOneStrengthened π →
    ∀ (α β : ℤ), (∀ t, (π (u1ParamGen α β t)).det = 1) →
      ∃ κ : ℝ, ∀ (f : SMFermion) (t : ℝ),
        (π (u1ParamGen α β t) * piOp (π (u1ParamGen α β t)))
            (fermionIndex f 0) (fermionIndex f 0)
          = Complex.exp (↑(κ * t)
              * commonHyperchargeMatrix (fermionIndex f 0)
                  (fermionIndex f 0)
              * Complex.I)

/-- Read-back: `SeatTie` is visibly the registered clause. -/
theorem seatTie_unfold (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    SeatTie π ↔
      ∀ (α β : ℤ) (t : ℝ) (f : SMFermion) (c : Fin 3),
        (π (u1ParamGen α β t) * piOp (π (u1ParamGen α β t)))
            (fermionIndex f c) (fermionIndex f c)
          = (π (u1ParamGen α β t) * piOp (π (u1ParamGen α β t)))
              (partner (fermionIndex f c))
                (partner (fermionIndex f c)) :=
  Iff.rfl

/-- Read-back: the strengthened set is visibly base ∧ tie. -/
theorem dialOneStrengthened_unfold
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    DialOneStrengthened π ↔ DialOneBase π ∧ SeatTie π :=
  Iff.rfl

/-- Read-back: `DialOneForcing` is visibly the registered
forcing statement, the COMMON HYPERCHARGE MATRIX in the
conclusion only. -/
theorem dialOneForcing_unfold :
    DialOneForcing ↔
      ∀ (π : AF → Matrix (Fin 32) (Fin 32) ℂ),
        DialOneStrengthened π →
        ∀ (α β : ℤ), (∀ t, (π (u1ParamGen α β t)).det = 1) →
          ∃ κ : ℝ, ∀ (f : SMFermion) (t : ℝ),
            (π (u1ParamGen α β t) * piOp (π (u1ParamGen α β t)))
                (fermionIndex f 0) (fermionIndex f 0)
              = Complex.exp (↑(κ * t)
                  * commonHyperchargeMatrix (fermionIndex f 0)
                      (fermionIndex f 0)
                  * Complex.I) :=
  Iff.rfl

end ThetLogos.DialOneSeatTiePin
