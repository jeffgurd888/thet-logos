import Mathlib.MeasureTheory.Integral.CircleIntegral
import ThetLogos.HolomorphicFunctionalCalculus

/-!
# SHELF-7b statement pin — 7b-disc registered, 7b-in-full gated on its face

Brick 7B-PIN of the SHELF line (refresh scoping
`whitepaper/shelf-7b-refresh-scoping-2026-11-02.md`, section (g)).
This module contains definitions and `Prop`-valued targets only —
it proves and asserts NOTHING. NO CLAIM; dials 0/4.

## Registration

This pin registers **7b-disc** as the buildable content under Jeff's
2026-11-01 build order. 7b-disc is NOT 7b-in-full and may never be
quoted as it. The shelf map's literal 7b row (a stale permanent row)
is superseded; the operative registration is
continuous/holomorphic spectral mapping, of which 7b-disc is the
disc fragment. NO CLAIM; dials 0/4.

The registered content of 7b-disc is the disc spectral mapping
equality `spectrum ℂ (hfcDisc a (discCoeff f R)) = f '' spectrum ℂ a`
for `f` holomorphic on a disc `Metric.ball 0 R` with
`(spectralRadius ℂ a).toReal < R`, frozen below as `Shelf7bDisc`
together with its GATE-B build list.

## The FULL gate (7b-in-full), on the face

- **FULL-1** winding number + rectifiable contour integral for
  `ℂ → A` integrands: L–XL, pin-blocked (absent from the pin).
- **FULL-2** Cauchy theorem / contour independence for a general
  neighbourhood: L–XL, pin-blocked as packaged API.
- **FULL-3** finite contour systems (rectangle/circle-arc
  assemblies) + refinement combinatorics: L, 60–110+, genuine
  blow-up risk, no owned API.
- **FULL-4** germ algebra + `AlgHom` bundle + locality/composition
  on germs: M–L on top of FULL-1–3.

FULL total: XL (150+ strict, tail unpriceable).

7b-in-full is UNSTATABLE in the pin's current vocabulary (no winding
number, no contour-system type) and remains gated at XL; this pin
freezes no target Prop for it, because there is no signature to
freeze it in.

## Kills (one line each; contents in the refresh dossier, section (e))

- K-DISJOINT-COVER: finitely many disjoint discs cannot replace a
  contour system — connected spectra force overlapping discs, hence
  boundary-of-union contours, i.e. FULL-3. KILLED.
- K-GELFAND-SUBALGEBRA: characters of the closed algebra generated
  by `a` see the polynomially convex hull, not `spectrum ℂ a`, so
  they prove mapping only for the filled spectrum. KILLED; binds B3.
- K-CIRCULAR-APPROX: polynomial approximation + passage to the limit
  is circular — the needed resolvent bound presupposes the calculus
  being constructed (Runge is also absent from the pin). KILLED.
- K-CURVE-NAME: the pin's `curveIntegral` integrates real 1-forms
  over real paths (Poincaré on convex sets); it is not contour
  infrastructure for Dunford–Riesz. KILLED (naming trap).
- K-7B-GATE-TRANSFER: GATE-A + SHELF-8b landing does not clear 7b's
  gate — the joint gate sentence was severed into three separate
  gates (GATE-A, FULL, GATE-B) before either chain landed, and the
  landed chains prove no 7b content. KILLED.
- K-DISCCOEFF-PHANTOM: `discCoeff` was a proposed name, not owned
  API (grep: empty over pin + corpus); the `discCoeff` definition
  below CREATES the name and may never be cited as pre-existing API.
  KILLED.
- K-WINDING-NAME: `PhaseWinding`'s `w : ℤ` is lift data on a finite
  ring — no curve, no integral, no complex domain; it supplies no
  part of FULL-1. KILLED (naming trap).

## Frozen build list (GATE-B, refreshed prices, strict counts)

- GATE-B1 (S–M, 18–32): coefficient bridge — `Shelf7bB1CoeffIndep`,
  `Shelf7bB1Summable`, `Shelf7bB1ScalarEval`, `Shelf7bB1Sharp`.
  Pre-registered PARTIAL seam at B1d (`Shelf7bB1Sharp`): if the
  Gelfand-comparison summability blows past M, B1 lands PARTIAL
  there with B1a/B1b/B1c standing and B1d as the named remainder;
  B2/B3 do not fire off a PARTIAL B1d.
- GATE-B2 (S–M, 12–25): forward inclusion at the sharp scale —
  `Shelf7bB2Forward`.
- GATE-B3 (M, 25–45): reverse inclusion, hence the headline
  equality — `Shelf7bDisc`. Pre-registered PARTIAL seam as
  registered: forward inclusion + polynomial case stand (already
  landed in SHELF-8a); if the factorisation glue blows past M, B3
  lands PARTIAL with the reverse inclusion as the named remainder.

GATE-B total: 55–102 strict, M–L chain. The chain consumes nothing
from GATE-A / SHELF-8b.

Context: `A` is a complex Banach algebra (complete, `NormOneClass`),
as in SHELF-8a's module (`ThetLogos.HolomorphicFunctionalCalculus`,
owner of `hfcDisc`, `DiscSummable`, `scalarEval`).
`spectralRadius ℂ a` is `ℝ≥0∞`; the sharp-scale hypothesis is frozen
in the real form `(spectralRadius ℂ a).toReal < R`.
-/

namespace ThetLogos

noncomputable section

variable {A : Type*} [NormedRing A] [NormOneClass A]
  [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A]

/-- Coefficients of `f` at `0`, presented at radius `R`:
Mathlib's `cauchyPowerSeries f 0 R` read as a sequence `ℕ → ℂ`.
This definition CREATES the name `discCoeff` (K-DISCCOEFF-PHANTOM:
it exists nowhere in the pin or the corpus before this pin, and no
text may cite it as pre-existing API). -/
def discCoeff (f : ℂ → ℂ) (R : ℝ) (n : ℕ) : ℂ :=
  cauchyPowerSeries f 0 R n (fun _ => 1)

/-- `f` presented holomorphically on the disc of radius `R`. -/
def DiscHolomorphic (f : ℂ → ℂ) (R : ℝ) : Prop :=
  0 < R ∧ DifferentiableOn ℂ f (Metric.ball 0 R)

/-! ## Frozen target Props (the GATE-B build list; asserted nowhere) -/

/-- B1a: the coefficients do not depend on the presenting radius. -/
def Shelf7bB1CoeffIndep (f : ℂ → ℂ) (R : ℝ) : Prop :=
  DiscHolomorphic f R →
    ∀ R₁ R₂ : ℝ, 0 < R₁ → R₁ < R → 0 < R₂ → R₂ < R →
      discCoeff f R₁ = discCoeff f R₂

/-- B1b: Cauchy-estimate summability at every interior scale. -/
def Shelf7bB1Summable (f : ℂ → ℂ) (R : ℝ) : Prop :=
  DiscHolomorphic f R →
    ∀ s : ℝ, 0 ≤ s → s < R → DiscSummable s (discCoeff f R)

/-- B1c: the scalar series value is `f` on the disc. -/
def Shelf7bB1ScalarEval (f : ℂ → ℂ) (R : ℝ) : Prop :=
  DiscHolomorphic f R →
    ∀ z : ℂ, ‖z‖ < R → scalarEval (discCoeff f R) z = f z

/-- B1d: `hfcDisc` summability at the spectral-radius scale
(the sharp form of 8a's `summable_smul_pow`). -/
def Shelf7bB1Sharp (a : A) (f : ℂ → ℂ) (R : ℝ) : Prop :=
  DiscHolomorphic f R → (spectralRadius ℂ a).toReal < R →
    Summable fun n => ‖discCoeff f R n • a ^ n‖

/-- B2: forward inclusion at the sharp scale. -/
def Shelf7bB2Forward (a : A) (f : ℂ → ℂ) (R : ℝ) : Prop :=
  DiscHolomorphic f R → (spectralRadius ℂ a).toReal < R →
    ∀ lam ∈ spectrum ℂ a, f lam ∈ spectrum ℂ (hfcDisc a (discCoeff f R))

/-- B3 (headline of 7b-disc): the disc spectral mapping equality. -/
def Shelf7bDisc (a : A) (f : ℂ → ℂ) (R : ℝ) : Prop :=
  DiscHolomorphic f R → (spectralRadius ℂ a).toReal < R →
    spectrum ℂ (hfcDisc a (discCoeff f R)) = f '' spectrum ℂ a

end

end ThetLogos
