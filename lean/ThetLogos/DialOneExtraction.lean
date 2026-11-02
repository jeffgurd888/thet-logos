import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import ThetLogos.DialOneClassificationPin

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneDoubleFlipPin
open ThetLogos.DialOneGammaFamilyPin
open ThetLogos.DialOneClassificationPin

namespace ThetLogos.DialOneExtraction

/-!
# ThetLogos.DialOneExtraction — CLS-1: the Grade-W extraction gap, prove-or-kill

Governing text: the next-rotation scoping
(`whitepaper/next-rotation-scoping-2026-11-01.md`, Lane 1,
CLS-1 "Shape A extraction gap"), over the CLS-0 pin
(`DialOneClassificationPin`): `weightAt π v` is a relation
over ALL `π` with NO hypothesis on `π`; the extraction
question — does every `π` with `DialOneBase π` admit a
weight vector at all — was named there as CLS-1, open and
unassumed. **This brick lands the pre-named PARTIAL seam
(§4 of the pack): extraction is proved modulo exactly one
named Prop, `ExtractionLemma π`, and the lemma is named
open. K-CLS-1 does NOT fire in this module: no base `π`
with no weight vector is constructed. NO CLAIM; Dial 1
= 0; all dials 0/4.**

```
Extraction : Prop := ∀ π, DialOneBase π → ∃ v, weightAt π v
```

## §1–§3: the indistinguishability audit (proved, in-tree)

The audit asks, clause by clause, what seat data the
landed `DialOneBase` can see. Its formal content is the
projections of §2 (the base is exactly ten clauses: five
representation laws, injectivity, the grading law, the
order-zero law, the first-order law, and ONE existential
clause about the U(1) family — a primitive direction of
determinant one) and the seat-data lemmas of §3:

* **Grading** sees only the sign of `gammaF` at a seat.
  Seats `8` (ν_R) and `9` (e_R) carry the SAME sign `-1`
  (`gamma_seats_eight_nine`), as do their J-partners `24`,
  `25` (sign `+1`), and the three u_L colour seats
  `2, 4, 6` (sign `+1`). The grading law alone cannot
  distinguish `8` from `9`, nor any colour from another.
* **The Dirac operator** (the only other clause naming
  seats, through the first-order double commutator)
  couples seat `p` only to seat `p + 8` (and the mirror
  pair `p + 16 ↔ p + 24`): `DF_oneGen` at `(0, 8)` is
  `Ynu`, at `(1, 9)` is `Ye`, at `(2, 10)`, `(4, 12)`,
  `(6, 14)` is `Yu`, and the direct entries `(8, 9)` and
  `(0, 1)` are `0` (`df_nu_coupling`, `df_e_coupling`,
  `df_colour_couplings`, `df_no_direct`). So `D` sees the
  pair `{8, 9}` only through the two DIFFERENT Yukawa
  inputs `Ynu`, `Ye` on their respective L-partners — and
  the base's first-order clause sees `D` only through the
  double commutator `[[D, π a], ρ b] = 0`, never through
  `D` itself.
* **The J-partner data** is the fixed involution
  `partner`: `8 ↦ 24`, `9 ↦ 25`, colours `2, 4, 6 ↦
  18, 20, 22` (`partner_eight_nine`, `partner_colour`).
* **The weight side differs where the base is blind, and
  agrees where the base is blind in the harmless way.**
  The common (π₁) lifted weights at seats `8` and `9` are
  `0` and `-6` — DIFFERENT (`weights_eight_nine`,
  `common_matrix_diag_nuR_eR`) — while the three u_L
  colour seats all carry the SAME weight `1`
  (`weights_colour_equal`). This is exactly the pack's
  dichotomy, made concrete: mixing seats of EQUAL lifted
  weight (the colours) leaves any lifted product a scalar
  block and can never obstruct extraction; a
  counterexample must hide where lifted weights DIFFER
  across data the base cannot separate — the `{8, 9}`
  pair is the audit's named candidate locus, separated
  by the base only via the `Ynu`/`Ye` inputs inside a
  double commutator.

**Candidate mechanisms, tested (pack §2).** (i) The
determinant clause: it is a single existential over
directions and constrains, even for a diagonal lift, only
the PRODUCT of the lifted diagonal entries — it names no
per-seat value and forces no per-seat character shape.
(ii) Order-zero: a commutation of `π a` with `ρ b`; it is
invariant under every simultaneous relabelling of the
two factors and sees no diagonal entry of anything.
(iii) The first-order clause: a double commutator; it is
the only clause that can feel the `Ynu`/`Ye` separation
of `{8, 9}`, and it feels it only as a commutant
condition on the image algebras. NONE of the three
forces the lifted diagonal
`(π (u1ParamGen α β t) * piOp (π (u1ParamGen α β t))) s s`
to be a function of `t` of any particular shape at all:
every clause of the base is ALGEBRAIC in the family
parameter — the base quantifies over algebra elements
and real Yukawa scalars, and no clause states or implies
any regularity (continuity, differentiability,
measurability) of `t ↦ π (u1ParamGen α β t)`. A
ℚ-linear twist of the circle parameter would be
invisible to every one of the ten clauses as a clause
shape; excluding it is precisely analytic content the
base does not contain. (That twist is NOT constructed
in this module: K-CLS-1 remains armed, unfired.)

## §4–§7: the PARTIAL seam

`ExtractionLemma π` (one Prop, stated exactly in §6)
supplies the two things the audit shows the base cannot:
**diagonality** of the lifted product in the seat basis
along one primitive determinant-one direction (no seat
mixing — the algebraic half of the gap), and
**differentiability at `0`** of each lifted diagonal
entry in `t` (the analytic half — the regularity that
turns the entry's exponential Cauchy equation, which the
base DOES supply via the representation laws and
order-zero, into a genuine character; integrality of the
exponent is then forced by the family's `2π`-periodicity,
§5). The headline `extraction_of_extractionLemma` proves
`DialOneBase π → ExtractionLemma π → ∃ v, weightAt π v`
for every `π`. The lemma is **named open**: it is not
proved from the base here, and §7 checks it is not
vacuous — π₁ satisfies it (`extractionLemma_pi1`, along
`(3, -1)`), so the seam is a real gap located at one
Prop, not an empty hypothesis.

**Verdict (full rank): PARTIAL.** Extraction is proved
modulo `ExtractionLemma`; unconditional extraction and
K-CLS-1 both remain open, exactly at that Prop.
-/

/-! ## §1. The U(1) family and the J-opposite: algebra -/

/-- The parametrised family at `0` is the algebra unit. -/
theorem gen_zero (α β : ℤ) : u1ParamGen α β 0 = afOne := by
  unfold u1ParamGen afOne
  simp

/-- **The family is a one-parameter group** in `AF`:
`u1ParamGen α β (s + t) = afMul (u1ParamGen α β s)
(u1ParamGen α β t)`, componentwise from
`Complex.exp_add`. This is the group law every later
Cauchy equation comes from. -/
theorem gen_add (α β : ℤ) (s t : ℝ) :
    u1ParamGen α β (s + t)
      = afMul (u1ParamGen α β s) (u1ParamGen α β t) := by
  simp only [u1ParamGen, afMul, SMAlgebra.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  · exact (mul_one 1).symm
  · rw [smul_mul_assoc, mul_smul_comm, mul_one, smul_smul,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf

/-- **The family is `2π`-periodic**: the exponents are
integers (`α, β : ℤ`), so `exp (· * 2π * I) = 1`. This
periodicity is what forces integrality of any continuous
character exponent in §5. -/
theorem gen_periodic (α β : ℤ) (t : ℝ) :
    u1ParamGen α β (t + 2 * Real.pi) = u1ParamGen α β t := by
  simp only [u1ParamGen, SMAlgebra.mk.injEq]
  refine ⟨?_, trivial, ?_⟩
  · have hexp : (α : ℂ) * (((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
        = (α : ℂ) * ((t : ℂ) * Complex.I)
          + (α : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      ring_nf
    rw [hexp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
      mul_one]
  · congr 1
    have hexp : (β : ℂ) * (((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
        = (β : ℂ) * ((t : ℂ) * Complex.I)
          + (β : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      ring_nf
    rw [hexp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
      mul_one]

/-- The J-opposite of the identity is the identity. -/
theorem piOp_one : piOp (1 : Matrix (Fin 32) (Fin 32) ℂ) = 1 := by
  rw [piOp_def_check, Matrix.transpose_one, Matrix.mul_one,
    UJ_mul_self]

/-- The J-opposite reverses products:
`piOp (A * B) = piOp B * piOp A` (entrywise, reindexing
by the partner involution). -/
theorem piOp_mul_rev (A B : Matrix (Fin 32) (Fin 32) ℂ) :
    piOp (A * B) = piOp B * piOp A := by
  ext i j
  rw [piOp_apply, Matrix.mul_apply, Matrix.mul_apply]
  have hsum : (∑ k : Fin 32, A (partner j) k * B k (partner i))
      = ∑ k : Fin 32, piOp B i k * piOp A k j := by
    rw [← Equiv.sum_comp
      (Function.Involutive.toPerm partner partner_involutive)
      (fun k => piOp B i k * piOp A k j)]
    apply Finset.sum_congr rfl
    intro k _
    show A (partner j) k * B k (partner i)
      = piOp B i (partner k) * piOp A (partner k) j
    rw [piOp_apply, piOp_apply, mul_comm, partner_involutive]
  exact hsum

/-! ## §2. The audit, part one: the base is exactly ten clauses

Each projection below is one clause of `DialOneBase` as
landed in `DialOneSeatTiePin`, named for the audit. The
point of the list is its completeness: there is no
eleventh clause, and in particular no clause about the
lifted product's diagonal, no clause about any individual
seat's weight, and no clause with analytic content in
the family parameter `t`. -/

/-- Base clause 1 (multiplicativity) — sees the algebra
product only; no seat data. -/
theorem base_mul (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (h : DialOneBase π) :
    ∀ a b, π (afMul a b) = π a * π b := by
  obtain ⟨hmul, -, -, -, -, -, -, -, -, -⟩ := h
  exact hmul

/-- Base clause 2 (additivity) — no seat data. -/
theorem base_add (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (h : DialOneBase π) :
    ∀ a b, π (afAdd a b) = π a + π b := by
  obtain ⟨-, hadd, -, -, -, -, -, -, -, -⟩ := h
  exact hadd

/-- Base clause 3 (star-compatibility) — no seat data. -/
theorem base_star (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (h : DialOneBase π) :
    ∀ a, π (afStar a) = (π a)ᴴ := by
  obtain ⟨-, -, hstar, -, -, -, -, -, -, -⟩ := h
  exact hstar

/-- Base clause 4 (unit) — no seat data. -/
theorem base_one (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (h : DialOneBase π) : π afOne = 1 := by
  obtain ⟨-, -, -, hone, -, -, -, -, -, -⟩ := h
  exact hone

/-- Base clause 5 (zero) — no seat data. -/
theorem base_zero (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (h : DialOneBase π) : π afZero = 0 := by
  obtain ⟨-, -, -, -, hzero, -, -, -, -, -⟩ := h
  exact hzero

/-- Base clause 6 (faithfulness) — no seat data. -/
theorem base_injective (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (h : DialOneBase π) : Function.Injective π := by
  obtain ⟨-, -, -, -, -, hinj, -, -, -, -⟩ := h
  exact hinj

/-- Base clause 7 (grading) — sees each seat ONLY through
the sign of `gammaF` there (§3: seats `8`, `9` agree). -/
theorem base_gamma (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (h : DialOneBase π) :
    ∀ a, gammaF * π a = π a * gammaF := by
  obtain ⟨-, -, -, -, -, -, hgamma, -, -, -⟩ := h
  exact hgamma

/-- Base clause 8 (order-zero) — a commutation of the two
image algebras; sees no diagonal entry of any product. -/
theorem base_order_zero (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (h : DialOneBase π) :
    ∀ a b, π a * piOp (π b) = piOp (π b) * π a := by
  obtain ⟨-, -, -, -, -, -, -, hord, -, -⟩ := h
  exact hord

/-- Base clause 9 (first-order) — the ONLY clause naming
seat data beyond the grading, and it names it only
through the double commutator with `DF_oneGen`, whose
coupling pattern is §3's `df_*` lemmas. -/
theorem base_first_order (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (h : DialOneBase π) :
    ∀ (Ynu Ye Yu Yd : ℝ) (a b : AF) (i j : Fin 32),
      ((DF_oneGen Ynu Ye Yu Yd * π a
          - π a * DF_oneGen Ynu Ye Yu Yd) * piOp (π b)
        - piOp (π b) * (DF_oneGen Ynu Ye Yu Yd * π a
          - π a * DF_oneGen Ynu Ye Yu Yd)) i j = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, hfirst, -⟩ := h
  exact hfirst

/-- Base clause 10 (unimodularity) — the ONLY clause
about the U(1) family, and it is a single existential:
some primitive direction has determinant `1` for all
`t`. It constrains no seat individually (for a diagonal
lift it constrains only the product of the diagonal
entries) and states no regularity in `t`. -/
theorem base_det_direction (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (h : DialOneBase π) :
    ∃ (α β : ℤ), Nat.gcd α.natAbs β.natAbs = 1
      ∧ ∀ t, (π (u1ParamGen α β t)).det = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hdet⟩ := h
  exact hdet

/-- Audit corollary: `weightAt`'s direction is its OWN
existential. A weight vector needs ONE direction that is
simultaneously determinant-one and character-shaped at
every seat; the base's clause-10 witness is not required
to be that direction, and `weightAt`'s witness is not
required to come from the base. Extraction is exactly
the production of one such joint witness. -/
theorem weightAt_det_direction
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) (v : Fin 32 → ℤ)
    (h : weightAt π v) :
    ∃ (α β : ℤ), Nat.gcd α.natAbs β.natAbs = 1
      ∧ ∀ t, (π (u1ParamGen α β t)).det = 1 := by
  obtain ⟨α, β, hgcd, hdet, -⟩ := h
  exact ⟨α, β, hgcd, hdet⟩

/-! ## §3. The audit, part two: seat data

Concrete seat values, all by finite computation on the
landed definitions. Seats are named by their `Fin 32`
indices (cf. `fermionIndex`: ν_R `= 8`, e_R `= 9`, u_L
colours `= 2, 4, 6`, u_R colours `= 10, 12, 14`). -/

/-- Grading data: the L doublet seats `0`, `1` both carry
sign `+1`. -/
theorem gamma_seats_zero_one :
    gammaF ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = 1
      ∧ gammaF ⟨1, by norm_num⟩ ⟨1, by norm_num⟩ = 1 :=
  ⟨by norm_num [gammaF], by norm_num [gammaF]⟩

/-- **Grading blindness at the candidate locus**: seats
`8` (ν_R) and `9` (e_R) carry the SAME grading sign `-1`.
The grading clause cannot distinguish them. -/
theorem gamma_seats_eight_nine :
    gammaF ⟨8, by norm_num⟩ ⟨8, by norm_num⟩ = -1
      ∧ gammaF ⟨9, by norm_num⟩ ⟨9, by norm_num⟩ = -1 :=
  ⟨by norm_num [gammaF], by norm_num [gammaF]⟩

/-- Grading data: the J-partners of `8`, `9` — seats `24`,
`25` — likewise agree, at sign `+1`. -/
theorem gamma_partner_seats :
    gammaF ⟨24, by norm_num⟩ ⟨24, by norm_num⟩ = 1
      ∧ gammaF ⟨25, by norm_num⟩ ⟨25, by norm_num⟩ = 1 :=
  ⟨by norm_num [gammaF], by norm_num [gammaF]⟩

/-- Grading data: the three u_L colour seats `2, 4, 6`
all carry sign `+1`. -/
theorem gamma_colour_seats :
    gammaF ⟨2, by norm_num⟩ ⟨2, by norm_num⟩ = 1
      ∧ gammaF ⟨4, by norm_num⟩ ⟨4, by norm_num⟩ = 1
      ∧ gammaF ⟨6, by norm_num⟩ ⟨6, by norm_num⟩ = 1 :=
  ⟨by norm_num [gammaF], by norm_num [gammaF],
    by norm_num [gammaF]⟩

/-- J-partner data at the candidate locus:
`partner 8 = 24`, `partner 9 = 25`. -/
theorem partner_eight_nine :
    partner ⟨8, by norm_num⟩ = ⟨24, by norm_num⟩
      ∧ partner ⟨9, by norm_num⟩ = ⟨25, by norm_num⟩ :=
  ⟨rfl, rfl⟩

/-- J-partner data for the u_L colours:
`2 ↦ 18`, `4 ↦ 20`, `6 ↦ 22`. -/
theorem partner_colour :
    partner ⟨2, by norm_num⟩ = ⟨18, by norm_num⟩
      ∧ partner ⟨4, by norm_num⟩ = ⟨20, by norm_num⟩
      ∧ partner ⟨6, by norm_num⟩ = ⟨22, by norm_num⟩ :=
  ⟨rfl, rfl, rfl⟩

/-- Dirac coupling: seat `0` (ν_L) couples only to seat
`8` (ν_R), with input `Ynu`. -/
theorem df_nu_coupling (Ynu Ye Yu Yd : ℝ) :
    DF_oneGen Ynu Ye Yu Yd ⟨0, by norm_num⟩ ⟨8, by norm_num⟩
      = (Ynu : ℂ) := by
  simp [DF_oneGen, buildDirac]

/-- Dirac coupling: seat `1` (e_L) couples only to seat
`9` (e_R), with input `Ye` — a DIFFERENT universally
quantified input from `Ynu`. This (inside the
first-order double commutator, and nowhere else) is the
base's only separation of the pair `{8, 9}`. -/
theorem df_e_coupling (Ynu Ye Yu Yd : ℝ) :
    DF_oneGen Ynu Ye Yu Yd ⟨1, by norm_num⟩ ⟨9, by norm_num⟩
      = (Ye : ℂ) := by
  simp [DF_oneGen, buildDirac]

/-- No direct Dirac coupling inside the pairs: the
entries `(8, 9)` and `(0, 1)` of `DF_oneGen` vanish for
all Yukawa inputs. `D` never mixes the two seats of a
pair directly. -/
theorem df_no_direct (Ynu Ye Yu Yd : ℝ) :
    DF_oneGen Ynu Ye Yu Yd ⟨8, by norm_num⟩ ⟨9, by norm_num⟩ = 0
      ∧ DF_oneGen Ynu Ye Yu Yd ⟨0, by norm_num⟩ ⟨1, by norm_num⟩
        = 0 :=
  ⟨by simp [DF_oneGen, buildDirac],
    by simp [DF_oneGen, buildDirac]⟩

/-- Dirac coupling for the u_L colours: seats `2, 4, 6`
couple to `10, 12, 14` with the SAME input `Yu` — the
Dirac data does not distinguish colours either. -/
theorem df_colour_couplings (Ynu Ye Yu Yd : ℝ) :
    DF_oneGen Ynu Ye Yu Yd ⟨2, by norm_num⟩ ⟨10, by norm_num⟩
        = (Yu : ℂ)
      ∧ DF_oneGen Ynu Ye Yu Yd ⟨4, by norm_num⟩ ⟨12, by norm_num⟩
          = (Yu : ℂ)
      ∧ DF_oneGen Ynu Ye Yu Yd ⟨6, by norm_num⟩ ⟨14, by norm_num⟩
          = (Yu : ℂ) :=
  ⟨by simp [DF_oneGen, buildDirac],
    by simp [DF_oneGen, buildDirac],
    by simp [DF_oneGen, buildDirac]⟩

/-- **The weight side at the candidate locus DIFFERS**:
the common lifted weights (`commonWeightVector`, the
diagonal of the COMMON HYPERCHARGE MATRIX, §STEP 0 of
the seat-tie pin) at seats `8` and `9` are `0` and `-6`.
A seat-mixing counterexample to extraction has somewhere
to live here: base-indistinguishable by grading, by
J-partner grading, and by direct Dirac coupling — with
different lifted weights. -/
theorem weights_eight_nine :
    commonWeightVector ⟨8, by norm_num⟩ = 0
      ∧ commonWeightVector ⟨9, by norm_num⟩ = -6 := by
  decide

/-- The same weights read off the COMMON HYPERCHARGE
MATRIX itself (landed `commonHyperchargeMatrix_diag` at
`ν_R` and `e_R`, whose seats are `8` and `9`): `0` and
`-6` in `ℂ`. -/
theorem common_matrix_diag_nuR_eR :
    commonHyperchargeMatrix ⟨8, by norm_num⟩ ⟨8, by norm_num⟩ = 0
      ∧ commonHyperchargeMatrix ⟨9, by norm_num⟩ ⟨9, by norm_num⟩
        = -6 := by
  constructor
  · have hseat : fermionIndex SMFermion.nuR 0
        = ⟨8, by norm_num⟩ := by
      apply Fin.ext
      rw [fermionIndex_val]
      rfl
    have h := commonHyperchargeMatrix_diag SMFermion.nuR 0
    rw [hseat] at h
    simpa [hypercharge] using h
  · have hseat : fermionIndex SMFermion.eR 0
        = ⟨9, by norm_num⟩ := by
      apply Fin.ext
      rw [fermionIndex_val]
      rfl
    have h := commonHyperchargeMatrix_diag SMFermion.eR 0
    rw [hseat] at h
    norm_num [hypercharge] at h
    exact h

/-- **The harmless side**: the three u_L colour seats
carry EQUAL common lifted weights (all `1`). Mixing
them — the mixing the base's colour-blind data most
obviously permits — leaves any lifted product a scalar
block and cannot obstruct extraction. -/
theorem weights_colour_equal :
    commonWeightVector ⟨2, by norm_num⟩ = 1
      ∧ commonWeightVector ⟨4, by norm_num⟩ = 1
      ∧ commonWeightVector ⟨6, by norm_num⟩ = 1 := by
  decide

/-! ## §4. The lifted product: the group law the base DOES supply

The base's clauses 1 (multiplicativity) and 8
(order-zero), applied to the one-parameter group of §1,
make the lifted product itself a one-parameter group of
matrices. This is the full extent of the base's force on
the lift's `t`-dependence: an exponential Cauchy equation
for its entries, with no regularity and no diagonality. -/

/-- **The lifted product** along `(α, β)`:
`π (u1ParamGen α β t) * piOp (π (u1ParamGen α β t))` —
the matrix whose diagonal entries `weightAt` constrains. -/
noncomputable def liftedProd (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (α β : ℤ) (t : ℝ) : Matrix (Fin 32) (Fin 32) ℂ :=
  π (u1ParamGen α β t) * piOp (π (u1ParamGen α β t))

/-- Read-back: `liftedProd` is visibly the lifted
product of the CLS-0 pin. -/
theorem liftedProd_unfold (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (α β : ℤ) (t : ℝ) :
    liftedProd π α β t
      = π (u1ParamGen α β t) * piOp (π (u1ParamGen α β t)) :=
  rfl

/-- **The lifted product is a one-parameter group**:
`liftedProd π α β (x + y) = liftedProd π α β x *
liftedProd π α β y`, from multiplicativity of `π`
(clause 1), the anti-multiplicativity of `piOp`, the
commutation of the two `piOp` factors (both are
`piOp` of the same group element at `x + y`), and
order-zero (clause 8) for the middle swap. -/
theorem liftedProd_add (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (hmul : ∀ a b, π (afMul a b) = π a * π b)
    (hord : ∀ a b, π a * piOp (π b) = piOp (π b) * π a)
    (α β : ℤ) (x y : ℝ) :
    liftedProd π α β (x + y)
      = liftedProd π α β x * liftedProd π α β y := by
  have hP : π (u1ParamGen α β (x + y))
      = π (u1ParamGen α β x) * π (u1ParamGen α β y) := by
    rw [gen_add]
    exact hmul _ _
  have hPy : π (u1ParamGen α β (y + x))
      = π (u1ParamGen α β y) * π (u1ParamGen α β x) := by
    rw [gen_add]
    exact hmul _ _
  have hQ : piOp (π (u1ParamGen α β (x + y)))
      = piOp (π (u1ParamGen α β y))
        * piOp (π (u1ParamGen α β x)) := by
    rw [hP, piOp_mul_rev]
  have hQcomm : piOp (π (u1ParamGen α β y))
        * piOp (π (u1ParamGen α β x))
      = piOp (π (u1ParamGen α β x))
        * piOp (π (u1ParamGen α β y)) := by
    have e1 : piOp (π (u1ParamGen α β y))
          * piOp (π (u1ParamGen α β x))
        = piOp (π (u1ParamGen α β (x + y))) := hQ.symm
    have e2 : piOp (π (u1ParamGen α β x))
          * piOp (π (u1ParamGen α β y))
        = piOp (π (u1ParamGen α β (x + y))) := by
      have hxy : piOp (π (u1ParamGen α β x))
            * piOp (π (u1ParamGen α β y))
          = piOp (π (u1ParamGen α β (y + x))) := by
        rw [hPy, piOp_mul_rev]
      rwa [add_comm] at hxy
    rw [e1, e2]
  have hswap : π (u1ParamGen α β y)
        * piOp (π (u1ParamGen α β x))
      = piOp (π (u1ParamGen α β x))
        * π (u1ParamGen α β y) := hord _ _
  have hcomm2 : (π (u1ParamGen α β y)
        * piOp (π (u1ParamGen α β y)))
        * piOp (π (u1ParamGen α β x))
      = piOp (π (u1ParamGen α β x))
        * (π (u1ParamGen α β y)
          * piOp (π (u1ParamGen α β y))) := by
    calc (π (u1ParamGen α β y) * piOp (π (u1ParamGen α β y)))
          * piOp (π (u1ParamGen α β x))
        = π (u1ParamGen α β y)
            * (piOp (π (u1ParamGen α β y))
              * piOp (π (u1ParamGen α β x))) :=
          Matrix.mul_assoc _ _ _
      _ = π (u1ParamGen α β y)
            * (piOp (π (u1ParamGen α β x))
              * piOp (π (u1ParamGen α β y))) := by
          rw [hQcomm]
      _ = (π (u1ParamGen α β y)
            * piOp (π (u1ParamGen α β x)))
            * piOp (π (u1ParamGen α β y)) :=
          (Matrix.mul_assoc _ _ _).symm
      _ = (piOp (π (u1ParamGen α β x))
            * π (u1ParamGen α β y))
            * piOp (π (u1ParamGen α β y)) := by
          rw [hswap]
      _ = piOp (π (u1ParamGen α β x))
            * (π (u1ParamGen α β y)
              * piOp (π (u1ParamGen α β y))) :=
          Matrix.mul_assoc _ _ _
  unfold liftedProd
  rw [hQ, hP]
  calc (π (u1ParamGen α β x) * π (u1ParamGen α β y))
        * (piOp (π (u1ParamGen α β y))
          * piOp (π (u1ParamGen α β x)))
      = π (u1ParamGen α β x)
          * ((π (u1ParamGen α β y)
              * piOp (π (u1ParamGen α β y)))
            * piOp (π (u1ParamGen α β x))) := by
        simp only [Matrix.mul_assoc]
    _ = π (u1ParamGen α β x)
          * (piOp (π (u1ParamGen α β x))
            * (π (u1ParamGen α β y)
              * piOp (π (u1ParamGen α β y)))) := by
        rw [hcomm2]
    _ = (π (u1ParamGen α β x)
          * piOp (π (u1ParamGen α β x)))
          * (π (u1ParamGen α β y)
            * piOp (π (u1ParamGen α β y))) := by
        simp only [Matrix.mul_assoc]

/-- The lifted product at `0` is the identity (clause 4
and `piOp_one`). -/
theorem liftedProd_zero (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (hone : π afOne = 1) (α β : ℤ) :
    liftedProd π α β 0 = 1 := by
  unfold liftedProd
  rw [gen_zero, hone, piOp_one, Matrix.mul_one]

/-- **Diagonality turns the group law into a per-seat
Cauchy equation**: if the lifted product is diagonal in
the seat basis along `(α, β)`, each diagonal entry `f`
satisfies `f (x + y) = f x * f y` (the sum over the
middle index collapses to the single seat). -/
theorem liftedProd_diag_add_entry
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (hmul : ∀ a b, π (afMul a b) = π a * π b)
    (hord : ∀ a b, π a * piOp (π b) = piOp (π b) * π a)
    (α β : ℤ)
    (hdiag : ∀ t (s s' : Fin 32), s ≠ s'
      → liftedProd π α β t s s' = 0)
    (x y : ℝ) (s : Fin 32) :
    liftedProd π α β (x + y) s s
      = liftedProd π α β x s s * liftedProd π α β y s s := by
  rw [liftedProd_add π hmul hord, Matrix.mul_apply]
  exact Finset.sum_eq_single s
    (fun k _ hk => by
      rw [hdiag x s k (fun h => hk h.symm), zero_mul])
    (fun h => absurd (Finset.mem_univ s) h)

/-! ## §5. The analytic step: Cauchy + regularity + periodicity = character

Pure analysis, no corpus content: a function
`f : ℝ → ℂ` with `f (x + y) = f x * f y`, `f 0 = 1`, and
a derivative at `0` is `exp (c * t)` with
`c = f'(0)` (the derivative propagates by the group
law, and the integrating factor `exp (-c * t)` kills
it); if moreover `f` is `2π`-periodic, `c` is an integer
multiple of `I` — a pure character with integer weight.
This is exactly the step the base cannot supply: it is
the differentiability hypothesis, not any algebra, that
excludes the pathological (discontinuous) solutions of
the Cauchy equation. -/

/-- The derivative of an exponential-Cauchy function is
everywhere the value times the derivative at `0`
(translation by the group law). -/
theorem hasDerivAt_of_add (f : ℝ → ℂ)
    (hadd : ∀ x y, f (x + y) = f x * f y)
    (hd : DifferentiableAt ℝ f 0) (t : ℝ) :
    HasDerivAt f (f t * deriv f 0) t := by
  have h0 : HasDerivAt f (deriv f 0) 0 := hd.hasDerivAt
  have h1 : HasDerivAt (fun h => f t * f h) (f t * deriv f 0) 0 :=
    h0.const_mul (f t)
  have h2 : HasDerivAt (fun h => f (t + h)) (f t * deriv f 0) 0 := by
    have hfun : (fun h => f (t + h)) = (fun h => f t * f h) := by
      funext h
      exact hadd t h
    rw [hfun]
    exact h1
  have h3 : HasDerivAt (fun y => f (t + (y - t))) (f t * deriv f 0) t := by
    have hf : HasDerivAt (fun h => f (t + h)) (f t * deriv f 0)
        (t - t) := by
      simpa using h2
    exact hf.comp_sub_const t
  have hfun2 : (fun y => f (t + (y - t))) = f := by
    funext y
    congr 1
    ring
  rw [hfun2] at h3
  exact h3

/-- **Exponential form**: a differentiable-at-`0`
solution of the exponential Cauchy equation with
`f 0 = 1` is a genuine exponential `exp (f'(0) * t)`. -/
theorem exp_form_of_add (f : ℝ → ℂ)
    (hadd : ∀ x y, f (x + y) = f x * f y)
    (h0 : f 0 = 1) (hd : DifferentiableAt ℝ f 0) :
    ∀ t, f t = Complex.exp (deriv f 0 * (t : ℂ)) := by
  set c := deriv f 0 with hc
  have hderiv : ∀ t, HasDerivAt f (f t * c) t :=
    fun t => hasDerivAt_of_add f hadd hd t
  have hexp : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => Complex.exp (-(c * (t : ℂ))))
        (Complex.exp (-(c * (t : ℂ))) * (-c)) t := by
    intro t
    have hin : HasDerivAt (fun z : ℂ => -(c * z)) (-c) (t : ℂ) := by
      have h1 : HasDerivAt (fun z : ℂ => c * z) c (t : ℂ) := by
        simpa using (hasDerivAt_id (t : ℂ)).const_mul c
      exact h1.neg
    have hcomp : HasDerivAt (fun y : ℝ => Complex.exp (-(c * (y : ℂ))))
        (Complex.exp (-(c * (t : ℂ))) * (-c)) t := by
      simpa only [Function.comp_apply] using
        ((Complex.hasDerivAt_exp (-(c * (t : ℂ)))).comp (t : ℂ)
          hin).comp_ofReal
    exact hcomp
  set g : ℝ → ℂ := fun t => f t * Complex.exp (-(c * (t : ℂ))) with hg
  have hgderiv : ∀ t, HasDerivAt g 0 t := by
    intro t
    have h := (hderiv t).mul (hexp t)
    have hval : f t * c * Complex.exp (-(c * (t : ℂ)))
        + f t * (Complex.exp (-(c * (t : ℂ))) * -c) = 0 := by ring
    rw [hval] at h
    exact h
  have hgdiff : Differentiable ℝ g :=
    fun t => (hgderiv t).differentiableAt
  have hg0 : ∀ t, deriv g t = 0 := fun t => (hgderiv t).deriv
  have hconst : ∀ t, g t = g 0 :=
    fun t => is_const_of_deriv_eq_zero hgdiff hg0 t 0
  intro t
  have hgt : g t = 1 := by
    rw [hconst t]
    simp [hg, h0]
  have hfin : f t = g t * Complex.exp (c * (t : ℂ)) := by
    show f t = (f t * Complex.exp (-(c * (t : ℂ))))
      * Complex.exp (c * (t : ℂ))
    rw [mul_assoc, ← Complex.exp_add]
    simp
  rw [hgt, one_mul] at hfin
  exact hfin

/-- **Character form**: add `2π`-periodicity, and the
exponential's rate is an integer multiple of `I` —
`f t = exp (n * t * I)` for a single integer `n`
(`Complex.exp_eq_one_iff` at `t = 2π`). This integer is
the seat's weight. -/
theorem char_of_add_periodic (f : ℝ → ℂ)
    (hadd : ∀ x y, f (x + y) = f x * f y)
    (h0 : f 0 = 1) (hper : ∀ t, f (t + 2 * Real.pi) = f t)
    (hd : DifferentiableAt ℝ f 0) :
    ∃ n : ℤ, ∀ t, f t
      = Complex.exp ((n : ℂ) * (t : ℂ) * Complex.I) := by
  have hexp := exp_form_of_add f hadd h0 hd
  have h2pi : f (2 * Real.pi) = 1 := by
    have h := hper 0
    rw [zero_add, h0] at h
    exact h
  have hval : Complex.exp (deriv f 0 * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    rw [← hexp (2 * Real.pi)]
    exact h2pi
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hval
  refine ⟨n, fun t => ?_⟩
  have hc : deriv f 0 = (n : ℂ) * Complex.I := by
    have hne : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast mul_ne_zero (by norm_num) Real.pi_ne_zero
    apply mul_right_cancel₀ hne
    rw [hn]
    push_cast
    ring
  rw [hexp t, hc]
  congr 1
  ring

/-! ## §6. The seam: `ExtractionLemma` and the PARTIAL headline -/

/-- **The extraction question, as a statement** (CLS-1's
target, verbatim from the pack): every base
representation admits a weight vector. This module does
NOT prove it unconditionally and does NOT refute it:
see `extraction_of_extractionLemma` for the proved
modulo form and the header for the verdict. -/
def Extraction : Prop :=
  ∀ π, DialOneBase π → ∃ v, weightAt π v

/-- Read-back: `Extraction` is visibly the registered
question. -/
theorem extraction_unfold :
    Extraction ↔ ∀ π, DialOneBase π → ∃ v, weightAt π v :=
  Iff.rfl

/-- **`ExtractionLemma π` — the named gap, stated
exactly.** Along ONE primitive determinant-one direction
`(α, β)` (the direction is part of the lemma's data, as
it is in `weightAt`):

1. the lifted product `liftedProd π α β t` is DIAGONAL
   in the seat basis for every `t` — no seat mixing
   along the family; and
2. every lifted diagonal entry `t ↦ liftedProd π α β t
   s s` is DIFFERENTIABLE AT `0` as a function
   `ℝ → ℂ`.

No weight value, no character shape, and no value of any
entry is named or assumed: the character conclusion is
derived in §5 from (1) + (2) + the base's group law.
The audit (§§2–3) is the evidence that both clauses are
genuinely outside the base: no base clause states
diagonality of anything in the seat basis along the
family, and no base clause has analytic content in `t`.
**This lemma is named OPEN: it is not proved from
`DialOneBase` in this module, and (K-CLS-1 unfired) it
is not refuted either.** -/
def ExtractionLemma (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    Prop :=
  ∃ α β : ℤ, Nat.gcd α.natAbs β.natAbs = 1
    ∧ (∀ t, (π (u1ParamGen α β t)).det = 1)
    ∧ (∀ t (s s' : Fin 32), s ≠ s'
        → liftedProd π α β t s s' = 0)
    ∧ ∀ s : Fin 32, DifferentiableAt ℝ
        (fun t => liftedProd π α β t s s) 0

/-- Read-back: `ExtractionLemma` is visibly the
registered seam — one primitive det-1 direction,
diagonality of the lifted product, differentiability
at `0` of its diagonal entries. -/
theorem extractionLemma_unfold
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    ExtractionLemma π ↔
      ∃ α β : ℤ, Nat.gcd α.natAbs β.natAbs = 1
        ∧ (∀ t, (π (u1ParamGen α β t)).det = 1)
        ∧ (∀ t (s s' : Fin 32), s ≠ s'
            → liftedProd π α β t s s' = 0)
        ∧ ∀ s : Fin 32, DifferentiableAt ℝ
            (fun t => liftedProd π α β t s s) 0 :=
  Iff.rfl

/-- **THE PARTIAL HEADLINE (CLS-1, modulo form).**
Extraction holds for every base representation
satisfying `ExtractionLemma`: the base supplies the
group law (§4), the lemma supplies diagonality and
regularity, §5 turns them into per-seat characters, and
the periodicity of the family forces the exponents to
be integers — a weight vector. The gap between the
base and Grade W is thereby located at exactly one
Prop: `ExtractionLemma`. -/
theorem extraction_of_extractionLemma
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ)
    (hbase : DialOneBase π) (hlem : ExtractionLemma π) :
    ∃ v, weightAt π v := by
  obtain ⟨hmul, -, -, hone, -, -, -, hord, -, -⟩ := hbase
  obtain ⟨α, β, hgcd, hdet, hdiag, hdiff⟩ := hlem
  have hchar : ∀ s : Fin 32, ∃ n : ℤ, ∀ t,
      liftedProd π α β t s s
        = Complex.exp ((n : ℂ) * (t : ℂ) * Complex.I) := by
    intro s
    apply char_of_add_periodic (fun t => liftedProd π α β t s s)
    · intro x y
      exact liftedProd_diag_add_entry π hmul hord α β hdiag x y s
    · rw [liftedProd_zero π hone α β]
      exact Matrix.one_apply_eq s
    · intro t
      unfold liftedProd
      rw [gen_periodic]
    · exact hdiff s
  choose v hv using hchar
  exact ⟨v, α, β, hgcd, hdet, fun t s => hv s t⟩

/-- The modulo statement as one Prop: extraction with
the seam as a hypothesis. Proved — it is
`extraction_of_extractionLemma` restated. What remains
open is exactly `DialOneBase π → ExtractionLemma π`
(and, independently, K-CLS-1). -/
def ExtractionModulo : Prop :=
  ∀ π, DialOneBase π → ExtractionLemma π → ∃ v, weightAt π v

/-- **Extraction modulo the named lemma: PROVED.** -/
theorem extraction_modulo : ExtractionModulo :=
  fun π hbase hlem => extraction_of_extractionLemma π hbase hlem

/-! ## §7. Consistency: the seam is inhabited (π₁)

`ExtractionLemma` is not vacuous: π₁ satisfies it along
its landed surviving direction `(3, -1)`. Its lifted
product is diagonal (π₁ of a `⟨lam, 1, c • 1⟩` element
is diagonal, and `piOp` preserves diagonality), and its
lifted entries are the landed exponentials
`pi1Diag_exp_gen` at the seat and its partner — smooth
characters, in particular differentiable at `0`. Hence
the modulo headline returns π₁'s weights, as it must:
the seam excludes no landed model. -/

/-- π₁ along the family is diagonal, in the landed
`pi1Diag` form. -/
theorem pi1_family_diagonal (t : ℝ) :
    pi1 (u1ParamGen 3 (-1) t)
      = Matrix.diagonal
          (pi1Diag (Complex.exp (((3 : ℤ) : ℂ) * ((t : ℂ) * Complex.I)))
            (Complex.exp (((-1 : ℤ) : ℂ) * ((t : ℂ) * Complex.I)))) :=
  pi1_eq_diagonal _ _

/-- π₁'s lifted entries along `(3, -1)` are pure
characters: the sum of the seat's and its J-partner's
landed `pi1Diag_exp_gen` exponents. -/
theorem pi1_liftedProd_entry (t : ℝ) (s : Fin 32) :
    liftedProd pi1 3 (-1) t s s
      = Complex.exp
          ((((pi1AVal s.val * 3 + pi1BVal s.val * (-1))
              + (pi1AVal (partner s).val * 3
                + pi1BVal (partner s).val * (-1)) : ℤ) : ℂ)
            * ((t : ℂ) * Complex.I)) := by
  unfold liftedProd
  rw [pi1_family_diagonal, ThetLogos.Track1RouteB.piOp_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
    pi1Diag_exp_gen, pi1Diag_exp_gen, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- π₁'s lifted product along `(3, -1)` is diagonal in
the seat basis. -/
theorem pi1_liftedProd_diag (t : ℝ) (s s' : Fin 32)
    (h : s ≠ s') : liftedProd pi1 3 (-1) t s s' = 0 := by
  unfold liftedProd
  rw [pi1_family_diagonal, ThetLogos.Track1RouteB.piOp_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_ne _ h]

/-- A pure character `t ↦ exp (K * (t * I))` is
differentiable at `0` (in fact everywhere): the analytic
shape §5 produces, seen here on the concrete side. -/
theorem differentiableAt_exp_lin (K : ℂ) :
    DifferentiableAt ℝ
      (fun t : ℝ => Complex.exp (K * ((t : ℂ) * Complex.I))) 0 := by
  have hin : HasDerivAt (fun z : ℂ => K * (z * Complex.I))
      (K * Complex.I) (((0 : ℝ)) : ℂ) := by
    have hform : (fun z : ℂ => K * (z * Complex.I))
        = (fun z : ℂ => (K * Complex.I) * z) := by
      funext z
      ring
    rw [hform]
    simpa using (hasDerivAt_id (((0 : ℝ)) : ℂ)).const_mul (K * Complex.I)
  have hcomp : HasDerivAt
      (fun y : ℝ => Complex.exp (K * ((y : ℂ) * Complex.I)))
      (Complex.exp (K * (((0 : ℝ) : ℂ) * Complex.I)) * (K * Complex.I))
      0 := by
    simpa only [Function.comp_apply] using
      ((Complex.hasDerivAt_exp _).comp (((0 : ℝ)) : ℂ) hin).comp_ofReal
  exact hcomp.differentiableAt

/-- **Consistency of the seam**: `ExtractionLemma pi1`
holds, along the primitive determinant-one direction
`(3, -1)` (determinant by the landed `pi1_det_gen`:
`-4 * 3 + -12 * -1 = 0`). -/
theorem extractionLemma_pi1 : ExtractionLemma pi1 := by
  refine ⟨3, -1, by decide, ?_, ?_, ?_⟩
  · intro t
    have h0 : (-4 * (3 : ℤ) + -12 * (-1) : ℤ) = 0 := rfl
    rw [pi1_det_gen, h0]
    simp
  · intro t s s' h
    exact pi1_liftedProd_diag t s s' h
  · intro s
    have hfun : (fun t => liftedProd pi1 3 (-1) t s s)
        = (fun t : ℝ => Complex.exp
            ((((pi1AVal s.val * 3 + pi1BVal s.val * (-1))
                + (pi1AVal (partner s).val * 3
                  + pi1BVal (partner s).val * (-1)) : ℤ) : ℂ)
              * ((t : ℂ) * Complex.I))) := by
      funext t
      exact pi1_liftedProd_entry t s
    rw [hfun]
    exact differentiableAt_exp_lin _

/-- Corollary: π₁ admits a weight vector — recovered
through the modulo headline from `DialOneBase pi1`
(landed) and `ExtractionLemma pi1` (§7), not assumed. -/
theorem pi1_has_weights : ∃ v, weightAt pi1 v :=
  extraction_of_extractionLemma pi1
    ThetLogos.DialOneGammaTraceChecks.dialOneBase_pi1
    extractionLemma_pi1

end ThetLogos.DialOneExtraction
