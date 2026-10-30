import Mathlib.Tactic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import ThetLogos.WightmanAxioms

/-!
# ThetLogos.Q7C4R4Post — registration of Q⁷C⁴R⁴ (Q7CR-0)

**Status: REGISTRATION ONLY — definitions and stated `Prop`s; no proof
attempted. NO CLAIM. No board, no dial.**

This module registers Jeff Gurd's named target **Q⁷C⁴R⁴** as ONE real
space, under the two decisions on the record (scoping
`scoping-q7c4r4-duality-2026-10-30.md`, DQ1 and DQ2 settled by Jeff):

- **DQ1 = ALL-REAL.** The composite is one real space `ℝ⁴⁴⁸`:
  Q⁷ realified (14 ℝ-dimensions) ⊗ C⁴ realified (8 ℝ-dimensions)
  ⊗ R⁴ (4 ℝ-dimensions), tensor product over `ℝ`, associated in the
  order `((Q⁷ ⊗ C⁴) ⊗ R⁴)`. All pairings below are in their exact
  REAL forms.
- **DQ2 = BOTH READINGS TIERED** (see the two paragraphs below; the
  tiers do not blur).

## MECHANICS (the buildable content)

The house WeldDuality reading (`ThetLogos.WeldDuality`, Jeff's
2026-10-16 dial decision "both in duality"): one object carried in
two faces — a space side and a dual side — with a stated pairing as
the linker between them. Here the linker is stated factorwise, by
the three real pairings defined in §2:

- Q⁷: the real part of the standard Hermitian form,
  `(x, y) ↦ (∑ k, x k * conj (y k)).re`;
- C⁴: the same real form on `Fin 4 → ℂ`. This is the REAL pairing.
  The C⁴ factor's complex Pontryagin self-duality (the pin's
  `zmodAddEquiv : ZMod n ≃+ AddChar (ZMod n) ℂ`) does NOT descend
  to this real pairing verbatim, and the complex pairing is not
  borrowed anywhere in this module;
- R⁴: the Minkowski η-pairing `x₀y₀ − x₁y₁ − x₂y₂ − x₃y₃`,
  signature `(+ , − , − , −)`, matching the corpus's owned form
  `minkowskiInner` in `ThetLogos.WightmanAxioms` (which this module
  reuses directly for its R⁴ factor, whose seat is that module's
  `Minkowski := Fin 4 → ℝ`; the factor is referenced, not
  redefined).

The `InDuality` package in §3 names these three pairings against the
composite's factors in the WeldDuality two-faces shape (space side /
dual side / pairing as the stated linker). It proves nothing.

## INTERPRETATION (Jeff's readings, attributed, tier T5)

Jeff's headline reading, carried here ONLY as his stated T5
interpretation, not as content of this registration: the ℝ⁴ frame
and the Q⁷ boundary are dualized via the C⁴ phase clock.

Jeff's purpose sentence (Jeff, 2026-10-30, his words): "it's one
thermal particle causing charge separation and gauge fields." The
composite is, in his stated intent, the state space for ONE thermal
particle (single-particle reading; NOT the vacuum background). This
registration states the SPACE only: no dynamics is stated, and no
causation is stated or implied as content — the "causing" clause is
tiered as his reading wherever it appears.

## Fences

- NO CLAIM; no board, no dial.
- Dimension arithmetic, recorded with nothing claimed from it: the
  finite part is `7 · 4 = 28 ≠ 32`, the corpus's home dimension
  (C³²); the composite dimension stated in §1 is `448 ≠ 32`. This
  object is new, not a rediscovery of C³².
- Q⁷ in this module is NOT identified with Q⁷DFT
  (`ThetLogos.Q7DFTPost`) or with the clock `Fin 7` family (the
  seven measured clock ratios); whether they are related is open
  (DQ5) and is not settled here.
- No continuum / L² content: no such content is part of this brick.
- Pre-registered kills: K-Q7CR-1 (any factor or pairing resisting
  owned vocabulary takes a FRONTIER mark and the brick lands
  PARTIAL at that seam; nothing is invented to fill it — no factor
  resisted at registration, so no such mark appears below) and
  K-Q7CR-2 (a collision with an existing tree object stops the
  brick; scoping's collision check found none, and none was found
  at registration).
-/

namespace ThetLogos

open TensorProduct

/-! ## §1. The factors and the composite (DQ1 = ALL-REAL) -/

/-- The Q⁷ factor, realified: `Fin 7 → ℂ` in its real module
structure (restriction of scalars from `ℂ` to `ℝ`; 14 ℝ-dimensions,
stated as a pin in `q7c4r4_q7_dim` below, not proved here). -/
abbrev q7c4r4Q7 : Type := Fin 7 → ℂ

/-- The C⁴ factor, realified: `Fin 4 → ℂ` in its real module
structure (restriction of scalars from `ℂ` to `ℝ`; 8 ℝ-dimensions,
stated as a pin in `q7c4r4_c4_dim` below, not proved here). -/
abbrev q7c4r4C4 : Type := Fin 4 → ℂ

/-- The R⁴ factor: the corpus's Minkowski seat, `Minkowski` from
`ThetLogos.WightmanAxioms` (`Fin 4 → ℝ`). Referenced, not
redefined. -/
abbrev q7c4r4R4 : Type := Minkowski

/-- **The composite (registration def).** The ℝ-tensor product of
the three factors, associated in the stated order
`((Q⁷ ⊗ C⁴) ⊗ R⁴)`, all over `ℝ` (DQ1 = ALL-REAL): one real
space. An `abbrev`, so the tensor product's module instances are
visible through it to `Module.finrank` in the pins below. -/
abbrev q7c4r4Composite : Type :=
  (q7c4r4Q7 ⊗[ℝ] q7c4r4C4) ⊗[ℝ] q7c4r4R4

/-- The Q⁷ factor's real dimension, STATED as a pin `Prop`
(registration only; not proved): `finrank ℝ (Fin 7 → ℂ) = 14`. -/
def q7c4r4_q7_dim : Prop :=
  Module.finrank ℝ q7c4r4Q7 = 14

/-- The C⁴ factor's real dimension, STATED as a pin `Prop`
(registration only; not proved): `finrank ℝ (Fin 4 → ℂ) = 8`. -/
def q7c4r4_c4_dim : Prop :=
  Module.finrank ℝ q7c4r4C4 = 8

/-- The R⁴ factor's real dimension, STATED as a pin `Prop`
(registration only; not proved): `finrank ℝ Minkowski = 4`. -/
def q7c4r4_r4_dim : Prop :=
  Module.finrank ℝ q7c4r4R4 = 4

/-- **The dimension pin.** The composite's real dimension, STATED
as a pin `Prop` (registration only; not proved):
`finrank ℝ q7c4r4Composite = 448` (`= 14 · 8 · 4`). Recorded with
nothing claimed from it: `448 ≠ 32`, the corpus's home dimension. -/
def q7c4r4_dim : Prop :=
  Module.finrank ℝ q7c4r4Composite = 448

/-! ## §2. The three real pairings (defs — formulas, real-valued) -/

/-- The Q⁷ real pairing: the real part of the standard Hermitian
form, `(x, y) ↦ (∑ k, x k * conj (y k)).re`. Real-valued by
construction (DQ1: exact real form). -/
def q7c4r4PairQ7 (x y : Fin 7 → ℂ) : ℝ :=
  (∑ k, x k * star (y k)).re

/-- The C⁴ real pairing: the same real form on `Fin 4 → ℂ`,
`(x, y) ↦ (∑ k, x k * conj (y k)).re`. This is the real pairing;
the factor's complex Pontryagin self-duality (the pin's
`zmodAddEquiv`) does not descend to it verbatim, and no complex
pairing is borrowed here. -/
def q7c4r4PairC4 (x y : Fin 4 → ℂ) : ℝ :=
  (∑ k, x k * star (y k)).re

/-- The R⁴ η-pairing: the Minkowski form
`x₀y₀ − x₁y₁ − x₂y₂ − x₃y₃`, signature `(+ , − , − , −)`. This is
the corpus's owned form `minkowskiInner` in
`ThetLogos.WightmanAxioms`, reused directly so the signs match the
corpus's Minkowski / weld convention by construction. -/
def q7c4r4PairR4 (x y : Minkowski) : ℝ :=
  minkowskiInner x y

/-! ## §3. The InDuality package (the mechanics, stated)

WeldDuality two-faces shape: the composite is carried together with
its factorwise real pairings as the stated linker — space side
(the composite and its factors as above), dual side (the same
factors read through their pairings), pairing (the three real
pairings of §2). Statement-grade only: the package names the three
pairings against the composite's factors; it proves nothing. -/

/-- **The InDuality package, stated.** A triple of candidate
factor pairings is the composite's stated linker exactly when it
is the three real pairings of §2: the Q⁷ pairing on the Q⁷ factor,
the C⁴ pairing on the C⁴ factor, and the η-pairing on the R⁴
factor. A definition (a posted package), not a theorem. -/
def q7c4r4InDuality
    (pairQ7 : (Fin 7 → ℂ) → (Fin 7 → ℂ) → ℝ)
    (pairC4 : (Fin 4 → ℂ) → (Fin 4 → ℂ) → ℝ)
    (pairR4 : Minkowski → Minkowski → ℝ) : Prop :=
  pairQ7 = q7c4r4PairQ7 ∧ pairC4 = q7c4r4PairC4 ∧
    pairR4 = q7c4r4PairR4

/-- **The canonical stated package.** The composite in duality
with its linker taken to be the three real pairings of §2
themselves. Stated as a `Prop` at registration; no proof is
attempted or asserted in this module. -/
def q7c4r4CanonicalInDuality : Prop :=
  q7c4r4InDuality q7c4r4PairQ7 q7c4r4PairC4 q7c4r4PairR4

end ThetLogos
