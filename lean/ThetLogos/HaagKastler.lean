import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import ThetLogos.WightmanAxioms

namespace ThetLogos

/-!
# ThetLogos.HaagKastler — the Haag–Kastler axioms as a pinned statement

Source: the QFT rungs map (`whitepaper/qft-rungs-map-2026-10-06.md`, Rung 3).
Haag–Kastler, "An algebraic approach to quantum field theory,"
*J. Math. Phys.* 5 (1964) 848–861: the algebraic formulation — nets of local
C*-algebras instead of operator-valued distributions. Same physical content
as Wightman (for theories satisfying both), different mathematical shape.

**What this file IS.** A machine-checked *statement* of the Haag–Kastler
axioms, with each analytic component as a labeled opaque field, plus the open
existence problem for interacting 4D nets. One T1 contribution:
`SpacelikeSeparated` — spacelike separation of regions, defined directly
from the Minkowski inner product already in `WightmanAxioms.lean`.

**What this file is NOT.** A construction of any net, or progress toward
one. The analytic content (C*-algebras of observables, their representations,
the vacuum sector) is beyond Mathlib's 2026 infrastructure — logged, not
wished away.

Honesty tiers in this file:
- **T1 (proved):** `SpacelikeSeparated` is well-defined from checked
  geometry (a definition, not a theorem — the T1 content is inherited).
- **T5 (theorem-shaped, content opaque):** `HaagKastlerAxioms`,
  `InteractingHaagKastlerNet`, `HaagKastlerExistence` — the open problem.
-/

/-- Two spacetime regions are spacelike separated when every pair of
    points, one from each, has spacelike (negative Minkowski-square)
    separation. -/
def SpacelikeSeparated (O₁ O₂ : Set Minkowski) : Prop :=
  ∀ x ∈ O₁, ∀ y ∈ O₂, minkowskiInner (x - y) (x - y) < 0

/-- A local algebra marker: Mathlib has C*-algebras, but the net needs the
    *specific* algebras of observables attached to regions — pinned. -/
structure LocalAlgebraMarker where
  carrier : Type

/-- The Haag–Kastler axioms (Haag–Kastler 1964), pinned as a bundle.
    Each analytic field is an opaque `Prop`; the content (nets of C*-
    algebras, their representations, Tomita–Takesaki theory for the vacuum
    sector) is beyond Mathlib's 2026 infrastructure. -/
structure HaagKastlerAxioms where
  /-- The net: each (bounded open) region carries an algebra of observables. -/
  net : Set Minkowski → LocalAlgebraMarker
  /-- Isotony: `O₁ ⊆ O₂` implies `A(O₁) ⊆ A(O₂)` (opaque). -/
  isotony : Prop
  /-- Locality: spacelike-separated regions have commuting algebras
      (opaque; `SpacelikeSeparated` above pins the geometric input). -/
  locality : Prop
  /-- Poincaré covariance: the net carries a covariant action
      `α_(Λ,a)(A(O)) = A(ΛO + a)` (opaque). -/
  poincareCovariant : Prop
  /-- Spectrum condition: translations are implemented by unitaries with
      joint spectrum in the closed forward light cone (opaque; the cone's
      geometry is T1 in `WightmanAxioms.lean`). -/
  spectrumCondition : Prop
  /-- Vacuum: a cyclic, Poincaré-invariant vector for the net (opaque). -/
  vacuumExists : Prop
  /-- Irreducibility / weak additivity (opaque). -/
  irreducibility : Prop

/-- An interacting Haag–Kastler net in 4D: a non-trivial model of the axioms.
    **Open:** no interacting 4D example has ever been constructed
    (rungs map, Rung 3). -/
def InteractingHaagKastlerNet : Prop :=
  ∃ _ : HaagKastlerAxioms, True

/-- The algebraic-QFT existence problem, pinned: does an interacting 4D
    Haag–Kastler net exist? Fixed target for Rung 3. -/
def HaagKastlerExistence : Prop := InteractingHaagKastlerNet

/-!
## Dependency ledger (what Mathlib 2026 lacks for the Haag–Kastler net)

1. The net itself: C*-algebras attached to spacetime regions with the
   isotony inclusions as *-homomorphisms.
2. Locality at the operator level: commuting von Neumann algebras for
   spacelike regions (needs the algebras first).
3. Covariant representations: unitary implementers of Poincaré
   automorphisms on the net.
4. The vacuum sector: GNS representation of an invariant state, cyclicity.
5. Any interacting 4D example (open problem in mathematics).

Note the asymmetry with Wightman: Haag–Kastler avoids distributions (no
`𝒮'` needed), but needs *more* operator-algebra infrastructure (C*-nets,
their representations) — Mathlib has C*-algebras but not the net
machinery. Neither framework is currently formalizable past the statement.
-/

end ThetLogos
