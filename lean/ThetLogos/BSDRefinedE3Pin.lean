import ThetLogos.BSDRefinedAssembly
import Mathlib.Tactic

namespace ThetLogos

/-!
# ThetLogos.BSDRefinedE3Pin — the refined BSD formula for `E3`, pinned as a `Prop`

Source: BSD statement-grade line, brick **BSD3-2** (the E3 pin),
scoped 2026-11-02 (`scoping-bsd3-2-2026-11-02.md` §4, shapes frozen
there). This module mirrors the E1 rung-3 pin (`E1`, its seam Props,
and `BSDRefinedE1` in `ThetLogos.BSDRefinedAssembly`) for the second
worked curve, and reuses that rung's `refinedRHS` assembly function
unchanged.

**The curve.** `E3` is LMFDB **11.a1** (Cremona 11a1):
`y² + y = x³ − x² − 10x − 20`, conductor `N = 11`. Model, label, and
rank are **T4 recorded inputs** (LMFDB 11.a1), as on the face below.

**What this file IS.** A machine-checked *statement* of the refined
Birch–Swinnerton-Dyer formula (Wiles's Remark 1 shape) for `E3`, in
the E1/E2 pattern: the curve as an in-tree object, the factors as
named seam Props stated and **not proved**, the (c) interval Props
for the two in-pass-computed values, and the stated-and-unproved pin
`BSDRefinedE3`. This brick proves nothing about the formula; the
torsion sweep (`BSDTorsionE3Sweep`) and the assembly
(`BSDRefinedE3Assembly`) are later bricks, not part of this dispatch.

**What this file is NOT — the board fences, on the face.**
- **NO CLAIM. Parts of Clay BSD closed: 0** — before, during, and
  after this brick. The refined formula is not the official
  statement; this pin is a statement-grade instrument only.
- **Seam B1 stands labeled (FRONTIER).** The pin's `sha` is the
  analytic order (the real quotient); its identification with
  `#Ш(E3)` rides only on the B1 licence, exactly as for E1/E2.
  Any analytic-Sha identification beyond that licence is
  **K-BSD3-2a**, a kill.
- **Seam B4 stands labeled.** Rank `0` is a **T4 recorded input**
  (LMFDB 11.a1), corroborated in-pass only analytically: the study's
  `L(E3, 1)` interval excludes `0`. The algebraic rank-0 statement
  rides as the named seam `E3RankZeroSeam`, proved nowhere here.
- **K-BSD3-2b fence.** `NagellLutzCriterionE3` below is the shared
  E1/E2 seam in its unstrengthened form, verbatim in shape. Any
  other form is a kill, never adopted silently.
- **K-BSD3-2d precision fence.** The study's bars are `L ± 1e-7`,
  `Ω ± 1e-7`, `sha = 1.0000000 ± 5e-7`. Nothing downstream may quote
  `L`, `Ω`, or `sha` past those bars. The pin's own bars are looser
  (per B2-5 discipline): `1e-5` on `L`, the interval
  `[1.2692092, 1.2692094]` on `Ω`.

Honesty tiers in this file:
- **T4 (recorded input):** the LMFDB 11.a1 label/model identity and
  algebraic rank `0`.
- **T5 (statement, unproved by design):** every def below — `E3`'s
  seam Props, the interval Props, and the pin `BSDRefinedE3`.
-/

/-! ## The curve -/

/-- The curve `E3 : y² + y = x³ − x² − 10x − 20` over `ℚ`
(LMFDB 11.a1; Weierstrass coefficients `[0, −1, 1, −10, −20]`),
in the same presentation style as `E1`/`E2` in-tree. Statement
only: no theorem about `E3` appears in this module. Its
discriminant is `Δ = −11⁵ = −161051` (computed in-pass in the
BSD3-2 study; the in-tree proof is the sweep brick's, not this
pin's). -/
def E3 : WeierstrassCurve ℚ := ⟨0, -1, 1, -10, -20⟩

/-! ## The seams -/

/-- **E3's rank-zero seam, distinctly labeled.** `E3(ℚ)` is finite.
Rank `0` is a **T4 recorded input** (LMFDB 11.a1), corroborated
in-pass analytically (the study's `L(E3, 1)` interval excludes `0`,
so the analytic rank is `0`); the algebraic statement itself is
proved nowhere in this tree and rides as this named seam, exactly
as `E1RankZeroSeam` does for E1. -/
def E3RankZeroSeam : Prop :=
  Finite E3.toAffine.Point

/-- **The Nagell–Lutz seam for E3** (`nagellLutz_seam`, E3
instance), in the sanctioned strength only — the *same form* as the
shared `NagellLutzCriterionE2` / `NagellLutzCriterionE1`: every
torsion point of `E3(ℚ)` in affine coordinates has *integer* affine
coordinates whose `y`-coordinate satisfies `y = 0` or
`y² ∣ 161051` (here `161051 = |Δ(E3)| = 11⁵`; the E1 form carries
`64 = Δ(E1)`, the E2 form `1728 = |Δ(E2)|`). A point is torsion if
some nonzero integer multiple of it is `0`. The converse direction
is *not* asserted, and no stronger form is sanctioned
(**K-BSD3-2b**: any other form is a kill). The Nagell–Lutz
criterion itself is not in Mathlib and is not proved here; it is
carried as this one labeled hypothesis, for the sweep brick to
consume. -/
def NagellLutzCriterionE3 : Prop :=
  ∀ (x y : ℚ) (h : E3.toAffine.Nonsingular x y),
    (∃ n : ℤ, n ≠ 0 ∧
      n • (WeierstrassCurve.Affine.Point.some x y h :
        E3.toAffine.Point) = 0) →
    ∃ (xi yi : ℤ), x = (xi : ℚ) ∧ y = (yi : ℚ) ∧
      (yi = 0 ∨ yi ^ 2 ∣ 161051)

/-- **E3's Sha seam (Seam B1, distinctly labeled).** The pin's `sha`
denotes a finite order; its statable residue is positivity, as in
`ShaFiniteE2` / `E1ShaFiniteSeam`. The identification with `#Ш(E3)`
rides on the B1 licence only, cited, never extended
(**K-BSD3-2a**). Stated as a `Prop`, proved nowhere. -/
def E3ShaFiniteSeam (sha : ℕ) : Prop :=
  0 < sha

/-- **E3's Tamagawa seam instance.** `∏c_p = 5` for E3, as a named
hypothesis `Prop` in the same form as `E2TamagawaValue` /
`E1TamagawaValue` (no Tamagawa object exists in Mathlib).
Per-prime record (computed in-pass in the BSD3-2 study, elementary
Tate step at the sole bad prime): at `11`, `ord₁₁(Δ) = 5` and
`11 ∤ c₄`, so the reduction is split multiplicative of type `I₅`
(singular point `(5, 5)` mod `11`, rational tangent slopes;
cross-check `a₁₁ = +1`), hence `c₁₁ = 5`. The general Tamagawa
discharge (B2-7) remains FRONTIER, unpriced, untouched by this
line. Proved nowhere. -/
def E3TamagawaValue (tam : ℝ) : Prop :=
  tam = 5

/-! ## The (c) value Props — provenance on the face; bars per the
K-BSD3-2d fence: nothing downstream quotes `L` or `Ω` past the
study's bars (`L ± 1e-7`, `Ω ± 1e-7`). -/

/-- **The (c) value of `L(E3, 1)`.** `L(E3, 1) = 0.2538418608559107`
at the study's bar `± 1e-7`, **computed in-pass** (BSD3-2 study §2:
AFE/Mellin, newform `q`-series from exact point counts, Fricke
factor measured in-pass; the identical code validated on E1 to
`4.3e-10` against the T4 recorded value). This upgrades E1's
T4-recorded L seam to E2's in-pass grade. The pin's bar `1e-5` is
two orders looser than the study's, per B2-5 discipline. Stated as
a `Prop`, proved nowhere. -/
def E3LValue (Lval : ℝ) : Prop :=
  |Lval - 0.2538418609| ≤ 1e-5

/-- **The (c) value of the real period.** `Ω = 1.2692093042795534`
at the study's bar `± 1e-7`, **computed in-pass** (BSD3-2 study §2:
`Ω = ∫_α^∞ dx/√f(x)` for the shifted model
`Y² = x³ − x² − 10x − 79/4`, real root `α = 4.3463081582053944`;
two independent quadratures agreed to `2.1e-28`). This upgrades
E1's T4 period seam to E2's in-pass grade. Stated as a `Prop`,
proved nowhere. -/
def E3PeriodValue (Ω : ℝ) : Prop :=
  Ω ∈ Set.Icc 1.2692092 1.2692094

/-! ## The pin -/

/-- **The E3 pin (statement only, brick BSD3-2).** The same Prop
shape as `BSDRefinedE1`, for `E3 : y² + y = x³ − x² − 10x − 20`,
with E3's own labeled seams as antecedents: the rank-0 seam
(**T4 recorded input**, Seam B4 labeled), the Sha seam (Seam B1
licence), the in-pass (c) L-value and period Props, and the
Tamagawa seam instance (`∏c_p = 5`). The refined right-hand side is
taken at `(Reg, tam, tors) = (1, 5, 5)`: the regulator is the
literal `1` (rank-0 empty-determinant convention), and the torsion
factor is the literal `5` — `#tors = 5` is not a hypothesis of
this pin; it is the sweep brick's conditional discharge, modulo
`NagellLutzCriterionE3` above (mirroring E2's literal `1` and its
B2-1 discharge). With the seams at their recorded values
`refinedRHS` reduces to `sha · Ω / 5`, and `sha` is **derived by
the later assembly's interval arithmetic, never input** (the
circularity fence). **No assembly theorem is stated or proved in
this brick.** -/
def BSDRefinedE3 : Prop :=
  ∀ (Lval ΩE3 : ℝ) (sha : ℕ) (tam : ℝ),
    E3RankZeroSeam → E3ShaFiniteSeam sha →
    E3LValue Lval → E3PeriodValue ΩE3 → E3TamagawaValue tam →
    |Lval - refinedRHS sha ΩE3 1 tam 5| ≤ 5e-3 ∧ sha = 1

end ThetLogos
