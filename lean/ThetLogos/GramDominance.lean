import ThetLogos.PhiAssembly
import ThetLogos.PlaneCrossingBeta6Assembly

/-
# ThetLogos.GramDominance — GD-0: Gram dominance, registered
in owned vocabulary (orders 5 and 6)

**Registration only (A0 pattern).** This module states Gram
dominance as Lean propositions in the corpus's owned
vocabulary; it proves nothing and asserts dominance
NOWHERE. Gram dominance in all its forms is a **registered
TARGET — a conjecture with evidence** (the B5-PROBE and
B6-PROBE seat multiples), named so the bench can aim at it.
Governing scoping: `scoping-gram-dominance-2026-10-29.md`
§§0, 1.1–1.4, 4.1.

**Face fences (verbatim-tier).** Even proved in full,
dominance retires only the regress's diagonal: 𝒜 ⪰ 0 is
unproved, the off-diagonal forms are untouched, no fixed
β > 0 is reached, clause (a) is unproved, Route B and the
α-wall are unaffected. GD-kernel (the regress form) is NOT
the β⁵ sign; the β⁵ sign is GD-cmp's territory (`GDCmp5`
below), at order 5 only. NO CLAIM; parts of the Clay
Yang–Mills statement closed by this module: **0**. Dials:
**0/4**.

**Scope of the registered forms.** The GD memo's scope is
irreducible `ρ`, even `N`, `3 ≤ N`; the Props below are
stated at general `(G, ρ)` in the β-line's own variable
context (the assemblies themselves are general), and any
future proof attempt inherits the memo's scope from the
objects it consumes. Coefficients in every form are in `ℚ`,
allowed to depend on all seat data `(G, ρ, N)` and, for
`GDGlobal`, on the square's index — no uniformity in the
data is demanded (§1.1 of the memo).

**The squares, and a normalization seam (named, not
smoothed).** The memo §1.1 defines the diagonal square by
`S_{C,t}(u) := Re M_t(u, u) = (d : ℝ)⁻¹⁴ · ‖RN_{C,t}(u)‖²`,
with `RN` the owned `rowNetwork` of `PhiAssembly` and the
pattern moment `M_t = quadCharMoment ρ μG C t u u`. The
owned factorization `quadCharMoment_eq_rowNetwork_mul`
together with `colNetwork_eq_star_rowNetwork` gives
`M_t = ((d : ℂ)⁻¹)⁴ · RN · star RN` on the diagonal, hence
`Re M_t = (d : ℝ)⁻⁴ · ‖RN‖²` at `0 < d` — so the memo's
`⁻¹⁴` display and its display
`κ₄^dep = 2⁻⁴ d⁻⁴ · Σ_{C,t} S_{C,t}` cannot both hold for
this `RN`: they differ by a factor `d⁻¹⁰`. Resolution
recorded here: `gramSquare` below follows the memo's
explicit square formula, `(d : ℝ)⁻¹⁴ · ‖RN‖²` (the pack's
instruction), built from the owned `rowNetwork` itself, so
the owned factorization facts are facts about THIS object
(up to the named `d⁻¹⁰` discrepancy against `Re M_t`,
under the cycle-ordering hypotheses of
`quadCharMoment_eq_rowNetwork_mul`). The cone statements
`GDGlobal5` / `GDGlobal6` are insensitive to a uniform
positive rescaling of all squares at a seat; the
proportionality and comparison forms do not consume the
squares at all. The discrepancy is a seam in the memo,
flagged at full rank; no silent correction is made in
either direction.

**The uniform object — FRONTIER.** Per §4.1 of the memo,
the uniform statement (one Prop over arbitrary order `n`,
with a uniform channel object) was attempted and RESISTS
statement: the corpus owns no definition of "the channel
excesses at order `n`" for arbitrary `n` — channels are
hand-built per order (B5-1, B6-1) and assembled per order
(B5-2, B6-2), and the per-order assemblies carry surprises
that do not uniformize on the record (B6-2's
μ₂-contaminated `A₄` term and its `S4theta` term). Gram
dominance therefore remains a **schema** `GD_n`, one
registered statement per order; this module registers the
order-5 and order-6 instances. The uniform channel object
is FRONTIER: named here as resisting statement, NOT
papered over with a fabricated uniform channel definition.
-/

open MeasureTheory Finset

namespace ThetLogos

section GramDominance

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]
  (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-! ## The squares -/

/-- **The diagonal Gram square of a network presentation**:
`S(u) = (d : ℝ)⁻¹⁴ · ‖RN(u)‖²`, where `RN` is the owned
`rowNetwork` of `PhiAssembly` at the presentation
`(s, P, σ)` — ordered sites, ordered columns, pattern
bits. This is the GD memo §1.1 square in its stated
normalization; see the header for the named `d⁻¹⁰`
normalization seam against `Re (quadCharMoment …)`. A
definition only: no nonnegativity or factorization fact
is asserted here. -/
noncomputable def gramSquare (s : Fin 4 → LayerSite N)
    (P : Fin 4 → LayerColumn N) (σ : Fin 4 → Bool)
    (u : LayerLink N → G) : ℝ :=
  ((d : ℝ)⁻¹) ^ 14 * ‖rowNetwork ρ μG s P σ u‖ ^ 2

/-- **The square of a pattern `t` of a primitive quad
`C`**, in the exact presentation the owned dictionary
consumes: at a cycle ordering `(s, P)` of `C`, the
pattern bits are `fun i => decide (P i ∈ t)`, as in
`quadCharMoment_eq_rowNetwork_mul` and
`colNetwork_eq_star_rowNetwork`. The ambient quad `C`
is carried as a parameter (the pattern's home); the
value depends on the presentation `(s, P)`, not on `C`
beyond it. -/
noncomputable def quadGramSquare (C : Finset (LayerColumn N))
    (t : Finset (LayerColumn N)) (s : Fin 4 → LayerSite N)
    (P : Fin 4 → LayerColumn N) (u : LayerLink N → G) : ℝ :=
  gramSquare ρ μG s P (fun i => decide (P i ∈ t)) u

/-- **A presentation is a genuine `(C, t)` square's
presentation** when it is a cycle ordering of a
primitive quad `C` in the sense of
`quadCharMoment_eq_rowNetwork_mul` (injective sites and
columns, covering `C`, the incidence
`colSites (P i) = {s i, s (i + 1)}`), for some pattern
`t ⊆ C`, with bits `σ = fun i => decide (P i ∈ t)`. Used
to restrict `GDGlobal`'s coefficients to the memo's own
`(C, t)` cone. -/
def gramPresentationValid (s : Fin 4 → LayerSite N)
    (P : Fin 4 → LayerColumn N) (σ : Fin 4 → Bool) : Prop :=
  ∃ (C : Finset (LayerColumn N)) (t : Finset (LayerColumn N)),
    C ∈ primitiveQuads ∧ t ⊆ C ∧ Function.Injective s
      ∧ Function.Injective P ∧ (∀ i, P i ∈ C)
      ∧ (∀ Q ∈ C, ∃ i, P i = Q)
      ∧ (∀ i, colSites (P i) = {s i, s (i + 1)})
      ∧ σ = fun i => decide (P i ∈ t)

/-! ## GD-strong: proportionality (the evidence's shape) -/

/-- **GD-strong at order 5** (registered target; asserted
nowhere). The order's owned channel list is the single
excess `kappa5chanExcess` (the `(2,1,1,1)` channel): it
is an exact positive rational multiple of `kappa4dep` as
diagonal forms. -/
def GDStrong5 : Prop :=
  ∃ lam : ℚ, 0 < lam ∧ ∀ u : LayerLink N → G,
    kappa5chanExcess ρ μG u u = (lam : ℝ) * kappa4dep ρ μG u u

/-- **GD-strong at order 6** (registered target; asserted
nowhere). The order's owned channel list, stated
explicitly: `kappa6chan3111Excess`,
`kappa6chan2211Excess`, `kappa6chanC6Excess`,
`kappa6chanThetaExcess` — each an exact positive
rational multiple of `kappa4dep` as diagonal forms,
with its own coefficient. -/
def GDStrong6 : Prop :=
  (∃ lam : ℚ, 0 < lam ∧ ∀ u : LayerLink N → G,
    kappa6chan3111Excess ρ μG u u = (lam : ℝ) * kappa4dep ρ μG u u)
  ∧ (∃ lam : ℚ, 0 < lam ∧ ∀ u : LayerLink N → G,
    kappa6chan2211Excess ρ μG u u = (lam : ℝ) * kappa4dep ρ μG u u)
  ∧ (∃ lam : ℚ, 0 < lam ∧ ∀ u : LayerLink N → G,
    kappa6chanC6Excess ρ μG u u = (lam : ℝ) * kappa4dep ρ μG u u)
  ∧ (∃ lam : ℚ, 0 < lam ∧ ∀ u : LayerLink N → G,
    kappa6chanThetaExcess ρ μG u u = (lam : ℝ) * kappa4dep ρ μG u u)

/-! ## GD-global: the cone form -/

/-- **Cone membership of one excess's diagonal** in the
cone generated by the Gram squares: a finite
nonnegative rational combination over all network
presentations `(s, P, σ)`, with coefficients forced to
vanish off the genuine `(C, t)` presentations
(`gramPresentationValid`), so the generating squares
are exactly the memo's `S_{C,t}` (a `(C, t)` square with
several cycle-ordering presentations splits its
coefficient among them — the same cone). -/
def ExcessInGramCone
    (E : (LayerLink N → G) → (LayerLink N → G) → ℝ) : Prop :=
  ∃ a : ((Fin 4 → LayerSite N) × (Fin 4 → LayerColumn N)
      × (Fin 4 → Bool)) → ℚ,
    (∀ i, 0 ≤ a i)
    ∧ (∀ i, ¬ gramPresentationValid i.1 i.2.1 i.2.2 → a i = 0)
    ∧ ∀ u : LayerLink N → G, E u u
      = ∑ i, (a i : ℝ) * gramSquare ρ μG i.1 i.2.1 i.2.2 u

/-- **GD-global at order 5** (registered target; asserted
nowhere): the diagonal of `kappa5chanExcess` is a finite
nonnegative rational combination of the squares
`S_{C,t}`. -/
def GDGlobal5 : Prop :=
  ExcessInGramCone ρ μG (kappa5chanExcess (N := N) ρ μG)

/-- **GD-global at order 6** (registered target; asserted
nowhere): the diagonal of each owned order-6 excess —
`kappa6chan3111Excess`, `kappa6chan2211Excess`,
`kappa6chanC6Excess`, `kappa6chanThetaExcess` — is a
finite nonnegative rational combination of the squares
`S_{C,t}`. -/
def GDGlobal6 : Prop :=
  ExcessInGramCone ρ μG (kappa6chan3111Excess (N := N) ρ μG)
  ∧ ExcessInGramCone ρ μG (kappa6chan2211Excess (N := N) ρ μG)
  ∧ ExcessInGramCone ρ μG (kappa6chanC6Excess (N := N) ρ μG)
  ∧ ExcessInGramCone ρ μG (kappa6chanThetaExcess (N := N) ρ μG)

/-! ## GD-kernel: the weakest retiring form -/

/-- **`u` lies in `K₄ = ker κ₄^dep`**, stated in the
form's own terms: `u` annihilates `kappa4dep` as a form
(zero against every second argument), not merely on the
diagonal. -/
def InKerKappa4dep (u : LayerLink N → G) : Prop :=
  ∀ u' : LayerLink N → G, kappa4dep ρ μG u u' = 0

/-- **`u` lies in `K₅ = ker κ₄^dep ∩ ker κ₅^dep`**,
stated in the forms' own terms, as for `InKerKappa4dep`. -/
def InKerKappa5dep (u : LayerLink N → G) : Prop :=
  (∀ u' : LayerLink N → G, kappa4dep ρ μG u u' = 0)
  ∧ ∀ u' : LayerLink N → G, kappa5dep ρ μG u u' = 0

/-- **GD-kernel at order 5** (registered target; asserted
nowhere): the order-5 excess `kappa5chanExcess` vanishes
on `K₄`. This is the memo's cone-phrased GD-kernel read
through §1.1(i): on `K₄` every square `S_{C,t}` vanishes
individually, so the cone form collapses to this
vanishing statement. GD-kernel is the regress form; it
is NOT the β⁵ sign (that is `GDCmp5`). -/
def GDKernel5 : Prop :=
  ∀ u : LayerLink N → G, InKerKappa4dep ρ μG u →
    kappa5chanExcess ρ μG u u = 0

/-- **GD-kernel at order 6** (registered target; asserted
nowhere): every owned order-6 excess —
`kappa6chan3111Excess`, `kappa6chan2211Excess`,
`kappa6chanC6Excess`, `kappa6chanThetaExcess` — vanishes
on `K₅ = ker κ₄^dep ∩ ker κ₅^dep`. -/
def GDKernel6 : Prop :=
  ∀ u : LayerLink N → G, InKerKappa5dep ρ μG u →
    kappa6chan3111Excess ρ μG u u = 0
    ∧ kappa6chan2211Excess ρ μG u u = 0
    ∧ kappa6chanC6Excess ρ μG u u = 0
    ∧ kappa6chanThetaExcess ρ μG u u = 0

/-! ## GD-cmp: the comparison form (β⁵ sign territory) -/

/-- **GD-cmp at order 5** (registered target; asserted
nowhere; memo §1.4, in the landed B5-2 context): some
rational `Λ` with `Λ ≤ 2 * M * d^5` — `M = colCount N`,
the column count of the B5-2 assembly, and `d` the
representation dimension — bounds the order-5 excess
against `kappa4dep` on the whole diagonal. This, not
GD-kernel, is the form the β⁵ sign off `ker κ₄^dep`
needs (via `kappa5dep_diag`:
`κ₅^dep(u, u) = (4 + (M − 4)·B) · κ₄^dep(u, u)
− (d⁻⁵/2) · kappa5chanExcess u u`). -/
def GDCmp5 : Prop :=
  ∃ Λ : ℚ, (Λ : ℝ) ≤ 2 * colCount N * (d : ℝ) ^ 5
    ∧ ∀ u : LayerLink N → G,
      kappa5chanExcess ρ μG u u ≤ (Λ : ℝ) * kappa4dep ρ μG u u

end GramDominance

end ThetLogos
