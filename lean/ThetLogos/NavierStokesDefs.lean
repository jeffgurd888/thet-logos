import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic

namespace ThetLogos

open MeasureTheory
open scoped ContDiff

/-!
# ThetLogos.NavierStokesDefs — Navier–Stokes definitions brick (NS-1a)

Board charter: **NO CLAIM.** Parts of the Clay Navier–Stokes problem
closed by this house: **0** — now, and after this brick lands (a
definitions brick closes no part of the problem). This module is the
definitions half of NS-1 (Lane 3), split per the NS-0 audit
(`routeb-general-scratch/scoping-ns-0-2026-11-02.md`): it DEFINES the
fields, the divergence operator, the Navier–Stokes system as a `Prop`,
and the Fefferman side-condition packages at verbatim grade. It states
NO board alternative (A/B/C/D land in NS-1b against these frozen
names) and proves NO existence content.

Source text: Charles L. Fefferman, "Existence and Smoothness of the
Navier–Stokes Equation," CMI official problem description — equations
(1)–(11), alternatives (A)–(D), and the errata pressure-periodicity
clause, as audited in NS-0 §3.

## Conventions (audit §2.3, pack NS-1a)

- Space is `NSpace := EuclideanSpace ℝ (Fin 3)` — dimension `n = 3`
  is fixed on the face of every definition below (K-NS-1 item 7).
  `‖x‖` is the Euclidean norm; coordinates are `x i`, `i : Fin 3`.
- Fields are plain functions, time-first (pack NS-1a):
  velocity/forcing `ℝ → NSpace → NSpace`, pressure `ℝ → NSpace → ℝ`,
  initial field `NSpace → NSpace`. The PDE and every side condition
  are asserted for `t ≥ 0` only — the Clay half-line `[0, ∞)`.
- The Laplacian is the pin's own: Mathlib's `Laplacian.laplacian`
  (`Mathlib/Analysis/InnerProductSpace/Laplacian.lean`, via the
  `Laplacian` class of `Mathlib/Analysis/Distribution/DerivNotation.lean`),
  applied componentwise to the scalar components `y ↦ u t y i`.
  No house Laplacian is defined.
- Divergence did not exist in-pin as a standalone operator (NS-0
  §2.2); `nsDiv` below owns it, from `fderiv` in the coordinate
  directions `nsBasis i = EuclideanSpace.single i 1`.

## K-NS-1 fence — carried on the face (audit §3)

Any package weaker than the Clay text on any item makes the coming
pin vacuous. What this brick carries, item by item:

1. (4) initial-data decay, all derivative orders and all decay
   powers — `NSInitialDecay`: for every `n K : ℕ` a constant `C`
   bounds `(1 + ‖x‖)^K * ‖∂^w u°(x)‖` for EVERY direction tuple `w`
   of unit vectors. The basis tuples `w = (e_{j₁}, …, e_{jₙ})` are
   exactly Fefferman's multiindices `α` (`∂^w = ∂^α`), so the
   all-`α`, all-`K` quantifier is carried literally, in the pin's
   `iteratedFDeriv` form — the same form Mathlib itself uses to
   define `SchwartzMap`. Smoothness + divergence-free `u°`:
   `NSInitialSmoothDivFree`, a conjunct of both initial packages.
2. (5)/(9) forcing decay, all `α`, all time-orders `m`, all `K` —
   `NSForcingDecayR3` with weight `(1 + ‖x‖ + t)^K` (Clay (5)) and
   `NSForcingDecayTorus` with weight `(1 + t)^K` (Clay (9): on the
   half-line `t ≥ 0`, `(1 + |t|) = (1 + t)`). Forcing smoothness is
   a conjunct of both forcing packages. `f ≡ 0` for A/B is named
   exactly: `NSZeroForcing` (pointwise `f t x = 0`, no "small" or
   "decaying" substitute).
3. (6) genuine `C^∞`: `NSSolutionSmooth` is joint `ContDiffOn ℝ ∞`
   (order `∞`, not finite) of the uncurried `(t, x) ↦ u t x` and
   `(t, x) ↦ p t x` on the FULL half-line set
   `Set.Ici 0 ×ˢ Set.univ` — not local-in-time, not Sobolev, not
   weak. The torus alternatives use the same package (their
   smoothness clause; NS-0 §3 numbers it (11), the NS-1a pack
   numbers the torus smoothness (10) — the content is identical
   under either numbering and is carried once, at full strength).
4. (7) global bounded energy: `NSBoundedEnergy` — one constant `C`
   with `∫ ‖u t x‖² dx < C` for ALL `t ≥ 0` (uniform; `C` does not
   depend on `t`). Torus analogue: `NSBoundedEnergyTorus`, the
   integral over the fundamental cube `ℝ³/ℤ³` (NS-0 §2.3 item 5
   places this analogue under (11)), uniform in `t` the same way.
5. (8) periodicity including the errata clause: `NSInitialPeriodic`
   and `NSForcingPeriodic` (period 1 in each coordinate direction),
   and the solution package `NSSolutionPeriodic` =
   `NSVelocityPeriodic` (Clay (10)) ∧ `NSPressurePeriodic` — the
   pressure periodicity is the Fefferman errata clause ("The
   further condition `p(x + eⱼ, t) = p(x,t)` should be made
   explicit"), carried as its own named conjunct, not folded in
   silently.
6. C/D quantifier shape (`∃` admissible `(u°, f)` with `¬∃` smooth
   finite-energy `(p, u)`): this is the statement layer — it lands
   in NS-1b by design and is NOT stated here. The packages above
   are shaped to be its admissibility and solution predicates
   unchanged.
7. `ν > 0` is the first conjunct of `NavierStokesSystem` itself,
   and `n = 3` is `NSpace` — both on the face, in every use.

## Named resistances (named, never weakened)

- **Torus domain.** The pin has no packaged `ℝ³/ℤ³` PDE setting
  (NS-0 §2.2). Periodicity is therefore encoded on `ℝ³` fields
  directly — which is Fefferman's own formulation: (B)/(D) are
  stated on `ℝ³ × [0, ∞)` with periodicity conditions (8)/(10),
  not on a quotient space. No quotient is constructed and none is
  needed for the statement layer.
- **Boundary smoothness.** Clay's `C^∞(ℝ³ × [0, ∞))` is smoothness
  on a closed half-space; the pin's native form is `ContDiffOn`
  at order `∞` within the half-line set (all iterated derivatives
  within the set, one-sided at `t = 0`). This is the encoding the
  pin's API offers; it is carried at full order `∞`, jointly in
  `(t, x)`, on the whole half-line — the resistance is in the
  boundary formalism only, and it is named here rather than
  smoothed over.

Honesty tiers in this file:
- **T1 (proved):** only the two `Iff.rfl` unfold self-checks at the
  end — about these definitions, not about Navier–Stokes.
- **Definitions (no tier):** everything else. A definition asserts
  nothing; in particular the zero field is NOT exhibited as a
  solution here (that check needs real analysis, not `Iff.rfl`,
  and is omitted per the NS-1a pack's discipline).
- **NO CLAIM:** existence, smoothness, breakdown — A/B/C/D are
  NS-1b's, against these frozen names.
-/

/-- Physical space for the Clay problem: `ℝ³` with the Euclidean
norm, as `EuclideanSpace ℝ (Fin 3)`. Dimension `n = 3` is fixed
here, on the face of every definition in this module (K-NS-1
item 7). -/
abbrev NSpace : Type := EuclideanSpace ℝ (Fin 3)

/-- A velocity field: time-first, `u t x : ℝ³` (pack NS-1a
convention; the PDE constrains `t ≥ 0`). -/
abbrev NSVelocityField : Type := ℝ → NSpace → NSpace

/-- A pressure field: time-first, `p t x : ℝ`. -/
abbrev NSPressureField : Type := ℝ → NSpace → ℝ

/-- An initial velocity field `u° : ℝ³ → ℝ³`. -/
abbrev NSInitialField : Type := NSpace → NSpace

/-- A forcing field `f`: time-first, `f t x : ℝ³`. -/
abbrev NSForcingField : Type := ℝ → NSpace → NSpace

/-- The `j`-th coordinate basis vector `eⱼ ∈ ℝ³`. -/
noncomputable def nsBasis (j : Fin 3) : NSpace := EuclideanSpace.single j 1

/-- The divergence of a vector field `v : ℝ³ → ℝ³` at `x`:
`div v (x) = ∑ i, ∂ᵢ vᵢ (x)`, from `fderiv` in the coordinate
directions. Owned here: the pin has no standalone divergence
operator (NS-0 §2.2). -/
noncomputable def nsDiv (v : NSpace → NSpace) (x : NSpace) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun y => v y i) x (nsBasis i)

/-- Divergence-free predicate: `div v = 0` at every point
(Fefferman (2), for a time-slice field). -/
def nsDivFree (v : NSpace → NSpace) : Prop :=
  ∀ x : NSpace, nsDiv v x = 0

/-- The `i`-th component of the gradient of a scalar field `q`
at `x`: `∂ᵢ q (x)`. -/
noncomputable def nsGradComponent (q : NSpace → ℝ) (x : NSpace) (i : Fin 3) : ℝ :=
  fderiv ℝ q x (nsBasis i)

/-- The `i`-th component of the time derivative `∂ₜ u` at
`(t, x)`: the ordinary derivative in `t` of the `i`-th component. -/
noncomputable def nsTimeDerivComponent (u : NSVelocityField) (t : ℝ) (x : NSpace)
    (i : Fin 3) : ℝ :=
  deriv (fun s => u s x i) t

/-- The `i`-th component of the convective term `(u·∇)u` at
`(t, x)`: `∑ j, uⱼ ∂ⱼ uᵢ`, the Jacobian contraction of `u t`
along the vector `u t x` itself. -/
noncomputable def nsConvectiveComponent (u : NSVelocityField) (t : ℝ) (x : NSpace)
    (i : Fin 3) : ℝ :=
  ∑ j : Fin 3, u t x j * fderiv ℝ (fun y => u t y i) x (nsBasis j)

/-- The `i`-th component of the Laplacian `Δu` at `(t, x)`: the
pin's own `Laplacian.laplacian` (Mathlib) applied to the scalar
component `y ↦ u t y i`. No house Laplacian is defined. -/
noncomputable def nsLaplacianComponent (u : NSVelocityField) (t : ℝ) (x : NSpace)
    (i : Fin 3) : ℝ :=
  Laplacian.laplacian (fun y => u t y i) x

/-- **The Navier–Stokes system as a Prop** (Fefferman (1), (2),
(3)): for named viscosity `ν`, initial field `u°`, forcing `f`,
velocity `u` and pressure `p` —

- `0 < ν` (K-NS-1 item 7, on the face);
- (1) `∂ₜuᵢ + ((u·∇)u)ᵢ = ν Δuᵢ − ∂ᵢp + fᵢ` pointwise, every
  component `i`, every `x`, every `t ≥ 0`, each term the defined
  operator above;
- (2) `div u (t) = 0` for every `t ≥ 0`;
- (3) `u (0) = u°`.

No smoothness, decay, or energy hypothesis is folded in here:
those are the separate side-condition packages below, so NS-1b
assembles Fefferman's alternatives from named parts. -/
def NavierStokesSystem (ν : ℝ) (u0 : NSInitialField) (f : NSForcingField)
    (u : NSVelocityField) (p : NSPressureField) : Prop :=
  0 < ν ∧
  (∀ (t : ℝ), 0 ≤ t → ∀ (x : NSpace) (i : Fin 3),
      nsTimeDerivComponent u t x i + nsConvectiveComponent u t x i
        = ν * nsLaplacianComponent u t x i - nsGradComponent (p t) x i + f t x i) ∧
  (∀ (t : ℝ), 0 ≤ t → ∀ x : NSpace, nsDiv (u t) x = 0) ∧
  (∀ x : NSpace, u 0 x = u0 x)

/-- Initial field smooth and divergence-free: `u° ∈ C^∞(ℝ³)`
(genuine `ContDiff ℝ ∞`, all orders) and `div u° = 0` everywhere.
A conjunct of both initial-data packages — Fefferman requires
smooth, divergence-free `u°` in all four alternatives (K-NS-1
item 1). -/
def NSInitialSmoothDivFree (u0 : NSInitialField) : Prop :=
  ContDiff ℝ ∞ u0 ∧ nsDivFree u0

/-- **Fefferman (4) — initial-data decay, verbatim grade:** for
every derivative order `n` and every decay power `K` there is a
constant `C_{n,K}` with
`(1 + ‖x‖)^K * ‖∂^w u°(x)‖ ≤ C_{n,K}` for every `x` and every
tuple `w` of unit direction vectors. Basis tuples give exactly
Fefferman's `|∂^α u°(x)| ≤ C_{α,K} (1 + |x|)^{-K}` for every
multiindex `α` and every `K` — the all-`α`, all-`K` Schwartz-grade
quantifier (K-NS-1 item 1), in the pin's `iteratedFDeriv` form
(the same form Mathlib uses to define `SchwartzMap`). -/
def NSInitialDecay (u0 : NSInitialField) : Prop :=
  ∀ (n K : ℕ), ∃ C : ℝ, ∀ (x : NSpace) (w : Fin n → NSpace),
    (∀ i, ‖w i‖ ≤ 1) →
    (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ n u0 x w‖ ≤ C

/-- **Fefferman (4) package for (A)/(C):** `u°` smooth,
divergence-free, with the full rapid decay of `NSInitialDecay`. -/
def NSInitialDataR3 (u0 : NSInitialField) : Prop :=
  NSInitialSmoothDivFree u0 ∧ NSInitialDecay u0

/-- **Periodicity of the initial field (part of Fefferman (8)):**
`u°(x + eⱼ) = u°(x)` for each coordinate direction `j`, period 1. -/
def NSInitialPeriodic (u0 : NSInitialField) : Prop :=
  ∀ (j : Fin 3) (x : NSpace), u0 (x + nsBasis j) = u0 x

/-- **Fefferman (8) package for (B)/(D), initial half:** `u°`
smooth, divergence-free, and period-1 in each coordinate. -/
def NSInitialDataTorus (u0 : NSInitialField) : Prop :=
  NSInitialSmoothDivFree u0 ∧ NSInitialPeriodic u0

/-- Forcing smoothness: `f` jointly `C^∞` (order `∞`) on the full
half-line `ℝ³ × [0, ∞)`, as the uncurried map `(t, x) ↦ f t x`
with `ContDiffOn` on `Set.Ici 0 ×ˢ Set.univ`. A conjunct of both
forcing packages — Fefferman's (5)/(9) are conditions on a smooth
`f`. -/
def NSForcingSmooth (f : NSForcingField) : Prop :=
  ContDiffOn ℝ ∞ (fun q : ℝ × NSpace => f q.1 q.2) (Set.Ici 0 ×ˢ Set.univ)

/-- The mixed space-time derivative entering (5)/(9): the order-`n`
spatial `iteratedFDeriv` (along the tuple `w`) of the order-`m`
time derivative `∂ₜ^m f`. For basis tuples `w` this is Fefferman's
`∂^α ∂ₜ^m f (x, t)`. -/
noncomputable def nsMixedDeriv (f : NSForcingField) (n m : ℕ) (t : ℝ) (x : NSpace)
    (w : Fin n → NSpace) : NSpace :=
  iteratedFDeriv ℝ n (fun y => iteratedDeriv m (fun s => f s y) t) x w

/-- **Fefferman (5) — forcing decay on `ℝ³`, verbatim grade:** for
every spatial order `n`, time order `m`, and decay power `K`,
there is `C_{n,m,K}` with
`(1 + ‖x‖ + t)^K * ‖∂^α ∂ₜ^m f (x, t)‖ ≤ C_{n,m,K}` for all
`t ≥ 0`, `x`, and unit direction tuples (basis tuples = the
multiindices `α`). This is `|∂^α ∂ₜ^m f(x,t)| ≤
C_{αmK} (1 + |x| + t)^{-K}` — all `α`, all `m`, all `K`
(K-NS-1 item 2). -/
def NSForcingDecayR3 (f : NSForcingField) : Prop :=
  ∀ (n m K : ℕ), ∃ C : ℝ, ∀ (t : ℝ), 0 ≤ t → ∀ (x : NSpace) (w : Fin n → NSpace),
    (∀ i, ‖w i‖ ≤ 1) →
    (1 + ‖x‖ + t) ^ K * ‖nsMixedDeriv f n m t x w‖ ≤ C

/-- **Fefferman (9) — forcing decay on the torus, verbatim grade:**
the same all-`α`, all-`m`, all-`K` quantifier with the torus
weight `(1 + t)^K` — Clay's `(1 + |t|)^{-K}`, and on the domain
`t ≥ 0` of every package here, `|t| = t`. No spatial decay:
spatial behaviour on the torus is periodicity, carried by
`NSForcingPeriodic` (K-NS-1 item 2). -/
def NSForcingDecayTorus (f : NSForcingField) : Prop :=
  ∀ (n m K : ℕ), ∃ C : ℝ, ∀ (t : ℝ), 0 ≤ t → ∀ (x : NSpace) (w : Fin n → NSpace),
    (∀ i, ‖w i‖ ≤ 1) →
    (1 + t) ^ K * ‖nsMixedDeriv f n m t x w‖ ≤ C

/-- **Fefferman (5) package for (C):** `f` smooth on the
half-line with the full decay of `NSForcingDecayR3`. -/
def NSForcingDataR3 (f : NSForcingField) : Prop :=
  NSForcingSmooth f ∧ NSForcingDecayR3 f

/-- **Periodicity of the forcing (part of Fefferman (8)):**
`f (x + eⱼ, t) = f (x, t)` for each coordinate direction `j`,
period 1, all `t`. -/
def NSForcingPeriodic (f : NSForcingField) : Prop :=
  ∀ (j : Fin 3) (t : ℝ) (x : NSpace), f t (x + nsBasis j) = f t x

/-- **Fefferman (8)+(9) package for (D):** `f` smooth on the
half-line, period-1 in each spatial coordinate (8), with the
full decay of `NSForcingDecayTorus` (9). -/
def NSForcingDataTorus (f : NSForcingField) : Prop :=
  NSForcingSmooth f ∧ NSForcingPeriodic f ∧ NSForcingDecayTorus f

/-- **`f ≡ 0`, named for (A)/(B):** the forcing is exactly zero,
pointwise. No "small", decaying, or compactly-supported substitute
is admitted (K-NS-1 item 2). -/
def NSZeroForcing (f : NSForcingField) : Prop :=
  ∀ (t : ℝ) (x : NSpace), f t x = 0

/-- **Fefferman (6) — solution smoothness, verbatim grade:**
`p, u ∈ C^∞(ℝ³ × [0, ∞))` as genuine joint `ContDiffOn ℝ ∞`
(order `∞`) of the uncurried maps `(t, x) ↦ u t x` and
`(t, x) ↦ p t x` on the full half-line set
`Set.Ici 0 ×ˢ Set.univ`. Not finite-order, not local-in-time,
not a weak/Sobolev substitute (K-NS-1 item 3). The torus
alternatives' smoothness clause is this same package (numbered
(11) in NS-0 §3, (10) in the NS-1a pack — identical content). -/
def NSSolutionSmooth (u : NSVelocityField) (p : NSPressureField) : Prop :=
  ContDiffOn ℝ ∞ (fun q : ℝ × NSpace => u q.1 q.2) (Set.Ici 0 ×ˢ Set.univ) ∧
  ContDiffOn ℝ ∞ (fun q : ℝ × NSpace => p q.1 q.2) (Set.Ici 0 ×ˢ Set.univ)

/-- **Periodicity of the velocity (Fefferman (10)):**
`u (x + eⱼ, t) = u (x, t)` for each coordinate direction `j`,
period 1, all `t`. -/
def NSVelocityPeriodic (u : NSVelocityField) : Prop :=
  ∀ (j : Fin 3) (t : ℝ) (x : NSpace), u t (x + nsBasis j) = u t x

/-- **Periodicity of the pressure — the Fefferman errata clause:**
`p (x + eⱼ, t) = p (x, t)` for each coordinate direction `j`,
period 1, all `t`. Fefferman's text directs that this condition
"should be made explicit in Eqn (8)"; it is carried here as its
own named Prop so it cannot be dropped silently (K-NS-1 item 5). -/
def NSPressurePeriodic (p : NSPressureField) : Prop :=
  ∀ (j : Fin 3) (t : ℝ) (x : NSpace), p t (x + nsBasis j) = p t x

/-- **Solution periodicity package for (B)/(D):** velocity
periodic (10) ∧ pressure periodic (errata clause). Both conjuncts
named separately above; neither is folded into the other. -/
def NSSolutionPeriodic (u : NSVelocityField) (p : NSPressureField) : Prop :=
  NSVelocityPeriodic u ∧ NSPressurePeriodic p

/-- **Fefferman (7) — bounded energy on `ℝ³`, verbatim grade:**
there is ONE constant `C` with `∫_{ℝ³} ‖u (x, t)‖² dx < C` for
all `t ≥ 0`. The bound is uniform in `t` — a `t`-dependent bound
would void the alternatives (K-NS-1 item 4). -/
def NSBoundedEnergy (u : NSVelocityField) : Prop :=
  ∃ C : ℝ, ∀ (t : ℝ), 0 ≤ t → (∫ x : NSpace, ‖u t x‖ ^ 2 ∂volume) < C

/-- The fundamental cube `[0, 1]³ ⊂ ℝ³`, the domain `ℝ³/ℤ³` of
the torus alternatives' energy integral. -/
def NSUnitCube : Set NSpace := {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- **Bounded energy on the torus** (the (7)-analogue for
(B)/(D); NS-0 §2.3 item 5 places it under (11)): one constant
`C` with `∫_{[0,1]³} ‖u (x, t)‖² dx < C` for all `t ≥ 0`,
uniform in `t` exactly as (7). -/
def NSBoundedEnergyTorus (u : NSVelocityField) : Prop :=
  ∃ C : ℝ, ∀ (t : ℝ), 0 ≤ t → (∫ x in NSUnitCube, ‖u t x‖ ^ 2 ∂volume) < C

/-- Pin self-check (T1, statement grade): the NS system `Prop`
unfolds definitionally to its literal text. Proved by `Iff.rfl`.
Asserts nothing about Navier–Stokes. -/
theorem navierStokesSystem_iff (ν : ℝ) (u0 : NSInitialField) (f : NSForcingField)
    (u : NSVelocityField) (p : NSPressureField) :
    NavierStokesSystem ν u0 f u p ↔
      0 < ν ∧
      (∀ (t : ℝ), 0 ≤ t → ∀ (x : NSpace) (i : Fin 3),
          nsTimeDerivComponent u t x i + nsConvectiveComponent u t x i
            = ν * nsLaplacianComponent u t x i - nsGradComponent (p t) x i + f t x i) ∧
      (∀ (t : ℝ), 0 ≤ t → ∀ x : NSpace, nsDiv (u t) x = 0) ∧
      (∀ x : NSpace, u 0 x = u0 x) :=
  Iff.rfl

/-- Pin self-check (T1, statement grade): the (4) package unfolds
definitionally to smooth-divergence-free ∧ full rapid decay.
Proved by `Iff.rfl`. -/
theorem nsInitialDataR3_iff (u0 : NSInitialField) :
    NSInitialDataR3 u0 ↔ NSInitialSmoothDivFree u0 ∧ NSInitialDecay u0 :=
  Iff.rfl

end ThetLogos
