/-
# ThetLogos.PlaquetteTelescoping — Brick A2-2a: statement
registration of the plaquette telescoping identity (Route B)

**Fences, up front.** NO CLAIM. Parts of the Clay Yang–Mills
statement closed by this module: **0**. Dials **0/4**.

This is a STATEMENT-ONLY registration brick (the A0 pattern of
`LayerKernelPos`): it registers, in owned vocabulary, the
objects and the two propositions (T) and (P) of the A2-2
scoping memo (`scoping-a2-2-telescoping-2026-10-29`, §§1–2).
**No positivity is asserted anywhere in this module, and
neither (T) nor (P) is proved or attempted.** The only proved
content is definitional API: corner/shift facts about the
plaquette datum and the section sanity lemma
`PlaqHol P (plaqSection P x) = x`.

**Naming fence.** The layer's own plaquettes are the columns
of `layerConfig`; the layer contains no spatial–spatial
plaquettes. The "plaquette" of this module is a plaquette of
the **column graph**: the graph on `LayerSite N` whose edges
are the columns `(c, ν)`. The datum below is a plaquette of
that graph, nothing else.

**The block is an auxiliary object. It is NOT a factor of
`layerKernel`** (memo §2, reading R3): each column is an edge
of four column-graph plaquettes and each stratum value is
integrated once in `layerKernel`, whereas the block below
integrates its four corner values afresh. No identity
registered here touches that sharing.

**Status of the statement.** The propositions registered
here are the REVISED entry (memo reading R2: the block
factors through the *pair* of plaquette holonomies, and the
induced two-variable kernel is positive semidefinite and
separately a class function in each argument). This revised
entry supersedes the claim-path memo's literal quotient-form
sentence (memo reading R1: a one-variable function of the
holonomy quotient), whose death is conditional on
A2-2-PROBE's certification — exactly that, no more. (T) is
registered at all real `β` (it is algebraic; the probe
spot-checks `β < 0`); (P) is registered at `0 ≤ β`, and
registers PSD plus separate class invariance only — no
further symmetry is asserted (memo §1.3 (P)(iii) fence).
-/

import ThetLogos.PlaquetteFactorPD

namespace ThetLogos

open Finset MeasureTheory

section PlaqDatumDef

variable {N : ℕ} [NeZero N]

/-- **The column-graph plaquette datum** `P = (c; μ, ν)`: a
base layer site `c` and two distinct nonzero spatial
directions `μ ≠ ν`. (The memo's registration pins one
ordering, e.g. `μ < ν`, so each plaquette is named once; the
block below is defined for any ordered distinct pair, and no
ordering hypothesis is carried here.) -/
structure PlaqDatum (N : ℕ) where
  /-- The base site `c₀₀`. -/
  base : LayerSite N
  /-- The first spatial direction. -/
  mu : Fin 4
  /-- The second spatial direction. -/
  nu : Fin 4
  /-- `μ` is spatial (nonzero). -/
  hmu : mu ≠ 0
  /-- `ν` is spatial (nonzero). -/
  hnu : nu ≠ 0
  /-- The two directions are distinct. -/
  hne : mu ≠ nu

/-- Corner `c₀₀`: the base site. -/
def plaqCorner00 (P : PlaqDatum N) : LayerSite N := P.base

/-- Corner `c₁₀`: the `μ`-shift of the base site. -/
def plaqCorner10 (P : PlaqDatum N) : LayerSite N :=
  layerShift P.mu P.hmu P.base

/-- Corner `c₀₁`: the `ν`-shift of the base site. -/
def plaqCorner01 (P : PlaqDatum N) : LayerSite N :=
  layerShift P.nu P.hnu P.base

/-- Corner `c₁₁`: the `μ`-shift of `c₀₁` (equivalently, by
`layerShift` commutation, the `ν`-shift of `c₁₀`). -/
def plaqCorner11 (P : PlaqDatum N) : LayerSite N :=
  layerShift P.mu P.hmu (plaqCorner01 P)

/-- The bottom edge `ℓ_b`: the column `(c₀₀, μ)`. -/
def plaqEdgeB (P : PlaqDatum N) : LayerLink N :=
  layerLinkOf (plaqCorner00 P) P.mu P.hmu

/-- The right edge `ℓ_r`: the column `(c₁₀, ν)`. -/
def plaqEdgeR (P : PlaqDatum N) : LayerLink N :=
  layerLinkOf (plaqCorner10 P) P.nu P.hnu

/-- The top edge `ℓ_t`: the column `(c₀₁, μ)`. -/
def plaqEdgeT (P : PlaqDatum N) : LayerLink N :=
  layerLinkOf (plaqCorner01 P) P.mu P.hmu

/-- The left edge `ℓ_l`: the column `(c₀₀, ν)`. -/
def plaqEdgeL (P : PlaqDatum N) : LayerLink N :=
  layerLinkOf (plaqCorner00 P) P.nu P.hnu

end PlaqDatumDef

section PlaqHolDef

variable {G : Type*} [Group G] {N : ℕ} [NeZero N]

/-- **The plaquette holonomy**: for a layer configuration
`u`, the loop based at `c₀₀` traversing `+μ, +ν, −μ, −ν`:
`u ℓ_b · u ℓ_r · (u ℓ_t)⁻¹ · (u ℓ_l)⁻¹`. This convention is
pinned by the registration (memo §1.2); changing basepoint
conjugates it and reversing orientation inverts it, both
absorbed by the class properties registered for the kernel
below. -/
def PlaqHol (P : PlaqDatum N) (u : LayerLink N → G) : G :=
  u (plaqEdgeB P) * u (plaqEdgeR P) * (u (plaqEdgeT P))⁻¹
    * (u (plaqEdgeL P))⁻¹

open Classical in
/-- **The section** `s : G → (LayerLink N → G)`: the
configuration equal to `x` on the bottom edge `ℓ_b` and to
`1` on `ℓ_r`, `ℓ_t`, `ℓ_l` and everywhere off the plaquette.
The plaquette kernel below is *defined* through this
section; that the section is irrelevant is the content of
the telescoping proposition (T), not of the definition. -/
noncomputable def plaqSection (P : PlaqDatum N) (x : G) :
    LayerLink N → G :=
  fun ℓ => if ℓ = plaqEdgeB P then x else 1

end PlaqHolDef

section PlaqGeomAPI

variable {N : ℕ} [NeZero N]

/-- **Layer shifts commute** (the datum's two directions):
shifting by `μ` then `ν` is shifting by `ν` then `μ` —
`torusShift_comm` read through `layerShift`. -/
theorem plaqLayerShift_comm (P : PlaqDatum N) (c : LayerSite N) :
    layerShift P.mu P.hmu (layerShift P.nu P.hnu c)
      = layerShift P.nu P.hnu (layerShift P.mu P.hmu c) := by
  apply Subtype.ext
  show torusShift N P.mu (torusShift N P.nu c.1)
    = torusShift N P.nu (torusShift N P.mu c.1)
  exact torusShift_comm N P.mu P.nu c.1

/-- Corner `c₁₁` is also the `ν`-shift of `c₁₀` (by shift
commutation). -/
theorem plaqCorner11_eq_shift10 (P : PlaqDatum N) :
    plaqCorner11 P = layerShift P.nu P.hnu (plaqCorner10 P) :=
  plaqLayerShift_comm P P.base

/-- `1 ≠ 0` in `ZMod N` once `2 ≤ N`. -/
theorem plaq_one_ne_zero (hN : 2 ≤ N) : (1 : ZMod N) ≠ 0 := by
  intro h
  have h5 : N ∣ 1 :=
    (CharP.cast_eq_zero_iff (ZMod N) N 1).mp (by
      rw [Nat.cast_one]; exact h)
  exact absurd (Nat.le_of_dvd (by norm_num) h5) (by omega)

/-- The shifted site's own coordinate moves by `1`. -/
theorem plaqShift_apply_self (ν : Fin 4) (hν : ν ≠ 0)
    (c : LayerSite N) : (layerShift ν hν c).1 ν = 1 + c.1 ν := by
  show torusShift N ν c.1 ν = 1 + c.1 ν
  rw [torusShift_apply_coord, Pi.single_eq_same]

/-- A shift does not move the other coordinates. -/
theorem plaqShift_apply_of_ne {μ ν : Fin 4} (h : ν ≠ μ)
    (hμ : μ ≠ 0) (c : LayerSite N) :
    (layerShift μ hμ c).1 ν = c.1 ν := by
  show torusShift N μ c.1 ν = c.1 ν
  rw [torusShift_apply_coord, Pi.single_eq_of_ne h, zero_add]

/-- A spatial shift has no fixed layer site once `2 ≤ N`:
the shifted coordinate differs by `1 ≠ 0`. -/
theorem plaqShift_ne_self (hN : 2 ≤ N) (ν : Fin 4) (hν : ν ≠ 0)
    (c : LayerSite N) : layerShift ν hν c ≠ c := by
  intro h
  have h2 := congrArg (fun s : LayerSite N => s.1 ν) h
  rw [plaqShift_apply_self] at h2
  have h1 : (1 : ZMod N) = 0 := by
    have h2' : (1 : ZMod N) + c.1 ν = 0 + c.1 ν := by
      rw [zero_add]; exact h2
    exact add_right_cancel_iff.mp h2'
  exact plaq_one_ne_zero hN h1

/-- Two layer sites differing by `1` at one coordinate are
distinct, once `2 ≤ N`. -/
theorem plaqSite_ne_of_coord {a b : LayerSite N} {j : Fin 4}
    (hN : 2 ≤ N) (h : a.1 j = 1 + b.1 j) : a ≠ b := by
  intro hab
  have h2 : a.1 j = b.1 j := by rw [hab]
  rw [h] at h2
  have h1 : (1 : ZMod N) = 0 := by
    have h2' : (1 : ZMod N) + b.1 j = 0 + b.1 j := by
      rw [zero_add]; exact h2
    exact add_right_cancel_iff.mp h2'
  exact plaq_one_ne_zero hN h1

/-- The `μ`-coordinate of `c₁₀`. -/
theorem plaqCorner10_coord_mu (P : PlaqDatum N) :
    (plaqCorner10 P).1 P.mu = 1 + P.base.1 P.mu :=
  plaqShift_apply_self P.mu P.hmu P.base

/-- The `ν`-coordinate of `c₀₁`. -/
theorem plaqCorner01_coord_nu (P : PlaqDatum N) :
    (plaqCorner01 P).1 P.nu = 1 + P.base.1 P.nu :=
  plaqShift_apply_self P.nu P.hnu P.base

/-- The `μ`-coordinate of `c₀₁` is the base's (the `ν`-shift
does not move it). -/
theorem plaqCorner01_coord_mu (P : PlaqDatum N) :
    (plaqCorner01 P).1 P.mu = P.base.1 P.mu :=
  plaqShift_apply_of_ne P.hne P.hnu P.base

/-- The `μ`-coordinate of `c₁₁`. -/
theorem plaqCorner11_coord_mu (P : PlaqDatum N) :
    (plaqCorner11 P).1 P.mu = 1 + P.base.1 P.mu := by
  show (layerShift P.mu P.hmu (plaqCorner01 P)).1 P.mu = _
  rw [plaqShift_apply_self, plaqCorner01_coord_mu]

/-- **Corner distinctness** (`Even N`, `4 ≤ N`): `c₁₀ ≠ c₀₀`. -/
theorem plaqCorner10_ne_00 (hN : Even N) (h4N : 4 ≤ N)
    (P : PlaqDatum N) : plaqCorner10 P ≠ plaqCorner00 P :=
  plaqSite_ne_of_coord (by omega) (plaqCorner10_coord_mu P)

/-- **Corner distinctness** (`Even N`, `4 ≤ N`): `c₀₁ ≠ c₀₀`. -/
theorem plaqCorner01_ne_00 (hN : Even N) (h4N : 4 ≤ N)
    (P : PlaqDatum N) : plaqCorner01 P ≠ plaqCorner00 P :=
  plaqSite_ne_of_coord (by omega) (plaqCorner01_coord_nu P)

/-- **Corner distinctness** (`Even N`, `4 ≤ N`): `c₁₁ ≠ c₀₀`. -/
theorem plaqCorner11_ne_00 (hN : Even N) (h4N : 4 ≤ N)
    (P : PlaqDatum N) : plaqCorner11 P ≠ plaqCorner00 P :=
  plaqSite_ne_of_coord (by omega) (plaqCorner11_coord_mu P)

/-- **Corner distinctness** (`Even N`, `4 ≤ N`): `c₁₁ ≠ c₁₀`
(`c₁₁` is the `ν`-shift of `c₁₀`, and shifts have no fixed
sites). -/
theorem plaqCorner11_ne_10 (hN : Even N) (h4N : 4 ≤ N)
    (P : PlaqDatum N) : plaqCorner11 P ≠ plaqCorner10 P := by
  rw [plaqCorner11_eq_shift10]
  exact plaqShift_ne_self (by omega) P.nu P.hnu (plaqCorner10 P)

/-- **Corner distinctness** (`Even N`, `4 ≤ N`): `c₁₁ ≠ c₀₁`
(`c₁₁` is the `μ`-shift of `c₀₁`). -/
theorem plaqCorner11_ne_01 (hN : Even N) (h4N : 4 ≤ N)
    (P : PlaqDatum N) : plaqCorner11 P ≠ plaqCorner01 P :=
  plaqShift_ne_self (by omega) P.mu P.hmu (plaqCorner01 P)

/-- **Corner distinctness** (`Even N`, `4 ≤ N`): `c₁₀ ≠ c₀₁`
(they differ at the `μ`-coordinate). -/
theorem plaqCorner10_ne_01 (hN : Even N) (h4N : 4 ≤ N)
    (P : PlaqDatum N) : plaqCorner10 P ≠ plaqCorner01 P :=
  plaqSite_ne_of_coord (by omega) (by
    rw [plaqCorner01_coord_mu]; exact plaqCorner10_coord_mu P)

/-- The right edge is not the bottom edge (directions `ν`
and `μ` differ). -/
theorem plaqEdgeR_ne_B (P : PlaqDatum N) :
    plaqEdgeR P ≠ plaqEdgeB P := by
  intro h
  have h2 := congrArg (fun ℓ : LayerLink N => ℓ.1.2) h
  exact P.hne (show P.mu = P.nu from h2.symm)

/-- The left edge is not the bottom edge (directions `ν`
and `μ` differ). -/
theorem plaqEdgeL_ne_B (P : PlaqDatum N) :
    plaqEdgeL P ≠ plaqEdgeB P := by
  intro h
  have h2 := congrArg (fun ℓ : LayerLink N => ℓ.1.2) h
  exact P.hne (show P.mu = P.nu from h2.symm)

/-- The top edge is not the bottom edge (`Even N`, `4 ≤ N`:
same direction `μ`, but bases `c₀₁ ≠ c₀₀`). -/
theorem plaqEdgeT_ne_B (hN : Even N) (h4N : 4 ≤ N)
    (P : PlaqDatum N) : plaqEdgeT P ≠ plaqEdgeB P := by
  intro h
  have h2 := congrArg (fun ℓ : LayerLink N => ℓ.1.1) h
  have h3 : plaqCorner01 P = plaqCorner00 P := Subtype.ext h2
  exact plaqCorner01_ne_00 hN h4N P h3

end PlaqGeomAPI

section PlaqSectionAPI

variable {G : Type*} [Group G] {N : ℕ} [NeZero N]

/-- The section at the bottom edge is the value `x`. -/
theorem plaqSection_at_B (P : PlaqDatum N) (x : G) :
    plaqSection P x (plaqEdgeB P) = x := by
  simp [plaqSection]

/-- The section off the bottom edge is `1`. -/
theorem plaqSection_at_of_ne (P : PlaqDatum N) (x : G)
    {ℓ : LayerLink N} (hℓ : ℓ ≠ plaqEdgeB P) :
    plaqSection P x ℓ = 1 := by
  simp [plaqSection, hℓ]

/-- **Registration sanity lemma**: the holonomy of the
section configuration is the value itself,
`PlaqHol P (s x) = x` — the loop reads `x` on `ℓ_b` and `1`
on the other three edges (edge distinctness at `Even N`,
`4 ≤ N`). -/
theorem PlaqHol_plaqSection (hN : Even N) (h4N : 4 ≤ N)
    (P : PlaqDatum N) (x : G) : PlaqHol P (plaqSection P x) = x := by
  unfold PlaqHol
  rw [plaqSection_at_B, plaqSection_at_of_ne P x (plaqEdgeR_ne_B P),
    plaqSection_at_of_ne P x (plaqEdgeT_ne_B hN h4N P),
    plaqSection_at_of_ne P x (plaqEdgeL_ne_B P)]
  simp

end PlaqSectionAPI

section PosDefKernelDef

variable {G : Type*} [Group G]

/-- **Positive-semidefinite two-variable kernel** on `G`:
the two-variable analogue of A2-1's `PosDefFun` — for every
finite test family `x : Fin n → G` and every coefficient
family `c : Fin n → ℂ`, the quadratic form of `K` has
nonnegative real part. -/
def PosDefKernel (K : G → G → ℂ) : Prop :=
  ∀ n : ℕ, ∀ x : Fin n → G, ∀ c : Fin n → ℂ,
    0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * K (x i) (x j) * c j).re

end PosDefKernelDef

section PlaqKernelSection

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)) {N : ℕ} [NeZero N]

/-- **The plaquette block**: the corner-integral form of
memo §1.2, exactly. The integral is over the four corner
stratum values `(α₀₀, α₁₀, α₀₁, α₁₁) ∈ G⁴`, read off a
function `a : Fin 4 → G` as `a 0 = α₀₀`, `a 1 = α₁₀`,
`a 2 = α₀₁`, `a 3 = α₁₁`, against the product Haar
probability (the pi-measure form owned by the tree), of the
product of the four `columnKernel ρ β` factors with the
corner assignment: bottom `(α₀₀, α₁₀)`, right `(α₁₀, α₁₁)`,
top `(α₀₁, α₁₁)`, left `(α₀₀, α₀₁)`. Real-valued; cast to
`ℂ` where kernel language needs it. **Auxiliary object
only: NOT a factor of `layerKernel`** (see the module
header). -/
noncomputable def PlaqBlock (P : PlaqDatum N) (β : ℝ)
    (u u' : LayerLink N → G) : ℝ :=
  ∫ a : Fin 4 → G,
    columnKernel ρ β (a 0) (a 1) (u (plaqEdgeB P)) (u' (plaqEdgeB P)) *
    columnKernel ρ β (a 1) (a 3) (u (plaqEdgeR P)) (u' (plaqEdgeR P)) *
    columnKernel ρ β (a 2) (a 3) (u (plaqEdgeT P)) (u' (plaqEdgeT P)) *
    columnKernel ρ β (a 0) (a 2) (u (plaqEdgeL P)) (u' (plaqEdgeL P))
    ∂(Measure.pi fun _ : Fin 4 => μG)

/-- **The plaquette kernel** `Ψ`: the block evaluated on the
section configurations, `Ψ x y = PlaqBlock P β (s x) (s y)`.
Ψ is *defined* by the section; its independence of the
section is proposition (T) below. -/
noncomputable def PlaqKernel (P : PlaqDatum N) (β : ℝ) (x y : G) : ℝ :=
  PlaqBlock μG ρ P β (plaqSection P x) (plaqSection P y)

/-- **(T) Telescoping / factorization through holonomies**
(registered proposition; statement only, NOT proved here):
at every plaquette `P`, with `Even N` and `4 ≤ N`, the block
depends on `(u, u')` only through the pair of plaquette
holonomies `(PlaqHol P u, PlaqHol P u')`. Registered at ALL
real `β`: the identity is algebraic in `β`. -/
def PlaqTelescoping (hN : Even N) (h4N : 4 ≤ N) (P : PlaqDatum N)
    (β : ℝ) : Prop :=
  ∀ u u' : LayerLink N → G,
    PlaqBlock μG ρ P β u u'
      = PlaqKernel μG ρ P β (PlaqHol P u) (PlaqHol P u')

/-- **(P) Positivity and class properties of Ψ** (registered
proposition; statement only, NOT proved here): at every
plaquette `P`, with `Even N`, `4 ≤ N` and `0 ≤ β`, the
plaquette kernel `Ψ` is (i) a positive-semidefinite kernel
on `G` (the `PosDefKernel` predicate, in `ℂ` via the real
cast) and (ii) separately a class function in each argument.
No further symmetry is registered (memo §1.3 (P)(iii)
fence). -/
def PlaqKernelPos (hN : Even N) (h4N : 4 ≤ N) (P : PlaqDatum N)
    (β : ℝ) (hβ : 0 ≤ β) : Prop :=
  PosDefKernel (fun x y => (PlaqKernel μG ρ P β x y : ℂ)) ∧
  (∀ g x y : G, PlaqKernel μG ρ P β (g * x * g⁻¹) y
      = PlaqKernel μG ρ P β x y) ∧
  (∀ g x y : G, PlaqKernel μG ρ P β x (g * y * g⁻¹)
      = PlaqKernel μG ρ P β x y)

end PlaqKernelSection

end ThetLogos
