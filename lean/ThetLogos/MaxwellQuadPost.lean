import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank
import ThetLogos.PlaquetteTelescoping

namespace ThetLogos

open Finset

/-!
# ThetLogos.MaxwellQuadPost — MAX-0: registration pin for the finite
Maxwell quadratic operator

**Status: REGISTRATION ONLY — definitions and stated `Prop`s.
NO CLAIM. No Millennium statement, no ladder rung, no dial
(dials stay 0/4). Nothing in this module asserts that any of
the registered Props M1–M5 holds; they are stated verbatim as
targets for MAX-1, MAX-2 and MAX-3.**

Commission: Jeff, 2026-10-31 00:22 EDT; the line SURVIVED
SCOPING with a genuinely missing object. Governing memo:
`routeb-general-scratch/scoping-maxwell-finite-2026-10-31.md`
(the seat §1, the ruling §2, the object §3, the ladder §4, the
rope and kills §5). Working label: MAX. The object registered
is the **finite Maxwell quadratic operator**: the quadratic
(free) part of the U(1) plaquette action as an explicit
operator on the owned layer lattice's real link-angle space,
with its kernel and spectrum registered as targets at named
seats. The corpus owned no operator on link variables anywhere
before this pin (memo §1, grep-verified): `transferOp` acts on
functions on link *configurations*, `PlaqBlock` is a scalar
kernel on the group, `magLin` acts on *vertex* potentials in a
background connection, and OP-1's `higgsMassQuad` is a mass
form on four assembled field directions. None of those is this
object (K-MAX-1 is pre-answered by type, memo §2).

## NO CLAIM face (memo §5, verbatim-grade)

Parts of any official Millennium statement closed by this
line: **0**. Dials: **0/4** — a finite operator's computed
spectrum is **not** a derived measured number (no measured
value is an input or an output of this line), **not** a
gravity object, **not** a continuum-limit theorem, **not** an
externally confirmed prediction. The FINITE dispersion value
registered in M5, `4·sin²(π/N)`, is a property of a chosen
finite operator at spacing 1; it is not evidence about any
continuum theory. Its continuum namesake ω = |k| is a
different sentence and is **never asserted** in this line.

## The word fence (K-MAX-2)

Jeff's phrase "gauge Maxwell lorentzian bridges"
(2026-10-31) is recorded as his **T5 name for a direction**;
it buys nothing and names nothing in this build. FENCE
SENTENCE: the words "Lorentzian" and "bridge" are **not
earned terms in this line** and are refused as names for
anything defined, registered, or proved here; in this module
they appear only inside this fence sentence and in the
quotation of Jeff's phrase in this paragraph. What would earn
them someday — a continuum-limit theorem meeting the S3-2 pin,
a Dial-3 event — is FRONTIER, not priced here and not
promised (memo §5).

## Disjointness from OP-1, and from the STEM family

Two finite senses of the word "photon", **disjoint, neither
implying the other**: OP-1's photon is the unique massless
direction of the Higgs mass form inside the assembled
electroweak sector (algebraic, landed, T2 couplings); this
line's object is the free propagation operator of a lattice
gauge field before any breaking (geometric, this line).
**OP-1 is not re-claimed, re-proved, or extended here.**
Likewise `magLin` is the covariant Laplacian on **vertex
potentials** in a background connection (the matter side),
while `maxwellOp` is the operator on the **connection's own
tangent space** (the gauge-field side): at zero field the
first is d₀ᵀd₀ on vertices, the second is d₁ᵀd₁ on links.
This distinction is stated here so the rename kill below can
never be ambiguous.

## Pre-registered kills, named on the face

- **K-MAX-1 (vacuity / rename).** If `maxwellOp` as built is
  definitionally the transfer operator, the plaquette
  block/factor, `magLin`, or the vertex `lapLin` renamed — or
  its form collapses to `osForm` — the line dies on sight at
  full rank. Pre-answered by type (memo §2), re-checked at
  every landing.
- **K-MAX-2 (fence breach).** Any brick or dossier sentence
  asserting a continuum signature, a continuum dispersion
  (ω = |k| or kin), a signature transition, or the fenced
  words as earned terms is void on sight, whatever it proves.
- **K-MAX-3 (seat-value kill).** The registered seat values
  are M4's spectrum **{4, 0, 0, 0}** and M5's gap
  **4·sin²(π/N)**. A *proved* spectrum or gap differing from
  either kills the seat claim at full rank in the landing
  dossier. (The definitions stand; the claim dies.)
- **K-MAX-S (stall rule).** Fourier-assembly or enumeration
  overrun is a stall and a re-price, never a kill and never a
  silent scope cut.

## What this line does not touch

The 𝒜 ⪰ 0 chain and clause (a) of `TransferFormPos` (standing
exactly as open as before); the S3 pier (statements unchanged,
proof-distance still zero); T-ENT, SE, PUMP, Q7CR-3
(independent lines, separately scoped); the STEM family's own
charter. No continuum object is defined, approximated, or
gestured at beyond the fence sentence above.

## Registration form of the operator (named choice)

`maxwellOp` is registered as a **definition, not a Prop-level
pin**: the explicit linear map on the plain link-angle
function space given by the polarization (component) formula
of `maxwellQuad` — the `lapLinFun` half of the house pattern
used for the vertex Laplacian in the STEM completion module.
Its transport to `EuclideanSpace ℝ (LayerLink N)` (the
`lapLin` step of that pattern) is **not** built in this brick;
M1 is accordingly registered in the coordinate form of the
Euclidean inner product, `∑ ℓ, θ ℓ * (maxwellOp N θ) ℓ`, which
is that inner product read in coordinates.
-/

section MaxwellDefs

/-- **Link-angle space** (memo §3): real link angles on the
owned layer lattice, `linkAngle N := LayerLink N → ℝ` — the
tangent space of the U(1) link configuration space at the
identity. Registered as an `abbrev` so the function-space
instances (addition, scalar action) apply to angles
directly. -/
abbrev linkAngle (N : ℕ) : Type :=
  LayerLink N → ℝ

/-- **Plaquette angle** (memo §3): the additive shadow of the
owned multiplicative `PlaqHol`, for `P : PlaqDatum N` and
`θ : linkAngle N`:
`θ (plaqEdgeB P) + θ (plaqEdgeR P) − θ (plaqEdgeT P)
  − θ (plaqEdgeL P)`, in the corpus's (B, R, T, L) edge
order. -/
def plaqAngle {N : ℕ} [NeZero N] (P : PlaqDatum N)
    (θ : linkAngle N) : ℝ :=
  θ (plaqEdgeB P) + θ (plaqEdgeR P)
    - θ (plaqEdgeT P) - θ (plaqEdgeL P)

open Classical in
/-- **Enumeration of plaquette data** (memo §3).
**Convention, stated on the face:** `allPlaqData N` is the
finset of plaquette data `⟨c, μ, ν⟩` over all base sites
`c : LayerSite N` and all **ordered** direction pairs with
`μ ≠ 0`, `ν ≠ 0` and **`μ < ν`** — the corpus's ordering
convention, so each geometric plaquette of the column graph
is named **exactly once**. (`PlaqDatum` carries no `Fintype`
instance in the corpus, so the enumeration is built by
`biUnion` over the site and direction universes, under the
classical decidability of the datum's equality.) -/
noncomputable def allPlaqData (N : ℕ) [NeZero N] :
    Finset (PlaqDatum N) :=
  Finset.univ.biUnion (fun c : LayerSite N =>
    Finset.univ.biUnion (fun μ : Fin 4 =>
      Finset.univ.biUnion (fun ν : Fin 4 =>
        if h : μ ≠ 0 ∧ ν ≠ 0 ∧ μ < ν then
          {⟨c, μ, ν, h.1, h.2.1, ne_of_lt h.2.2⟩}
        else ∅)))

/-- **The finite Maxwell quadratic form** (memo §3):
`maxwellQuad N θ := Σ P ∈ allPlaqData N, (plaqAngle P θ)²`.
This is, definitionally, the quadratic part of the U(1)
Wilson action summed over plaquettes, with the overall
scalar β/2 stripped — the operator below is β-free, and β
enters only as that stripped scalar on the action. The tie
to the Wilson weight is a statement of two-sided cosine
bounds, never an equality of actions (target of MAX-2). -/
noncomputable def maxwellQuad (N : ℕ) [NeZero N]
    (θ : linkAngle N) : ℝ :=
  ∑ P ∈ allPlaqData N, (plaqAngle P θ) ^ 2

open Classical in
/-- **Plaquette sign pattern**: the coefficient of the link
`ℓ` in `plaqAngle P`, namely `+1` on the (B, R) edges, `−1`
on the (T, L) edges, and `0` on every other link (counted
with multiplicity if edges were to coincide). This is the
polarization data of `maxwellQuad`. -/
noncomputable def plaqSign {N : ℕ} [NeZero N] (P : PlaqDatum N)
    (ℓ : LayerLink N) : ℝ :=
  (if ℓ = plaqEdgeB P then 1 else 0)
    + (if ℓ = plaqEdgeR P then 1 else 0)
    - (if ℓ = plaqEdgeT P then 1 else 0)
    - (if ℓ = plaqEdgeL P then 1 else 0)

/-- **The finite Maxwell quadratic operator** (memo §3),
registered as a **definition** via polarization (see the
registration-form note on the module face):
`maxwellOp N : (LayerLink N → ℝ) →ₗ[ℝ] (LayerLink N → ℝ)`
with component formula
`(maxwellOp N θ) ℓ = Σ P ∈ allPlaqData N,
  plaqSign P ℓ * plaqAngle P θ` —
the self-adjoint operator of `maxwellQuad`, β-free, acting
on the gauge field's own tangent space (link angles), not on
vertex potentials and not on link configurations. -/
noncomputable def maxwellOp (N : ℕ) [NeZero N] :
    (LayerLink N → ℝ) →ₗ[ℝ] (LayerLink N → ℝ) where
  toFun θ ℓ :=
    ∑ P ∈ allPlaqData N, plaqSign P ℓ * plaqAngle P θ
  map_add' θ η := by
    funext ℓ
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro P _
    simp only [plaqAngle, Pi.add_apply]
    ring
  map_smul' c θ := by
    funext ℓ
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro P _
    simp only [plaqAngle, Pi.smul_apply, smul_eq_mul]
    ring

/-- The **tail** of a layer link: its base site, read as a
layer site. -/
def linkTail {N : ℕ} [NeZero N] (ℓ : LayerLink N) :
    LayerSite N :=
  ⟨ℓ.1.1, ℓ.2.1⟩

/-- The **head** of a layer link: the layer site reached from
its tail by the link's own spatial direction. -/
def linkHead {N : ℕ} [NeZero N] (ℓ : LayerLink N) :
    LayerSite N :=
  layerShift ℓ.1.2 ℓ.2.2 (linkTail ℓ)

/-- **Pure-gauge link angle** (memo §3, M3): for a site
potential `φ : LayerSite N → ℝ`, the angle
`gaugeAngle φ ℓ := φ (head ℓ) − φ (tail ℓ)`. -/
def gaugeAngle {N : ℕ} [NeZero N] (φ : LayerSite N → ℝ) :
    linkAngle N :=
  fun ℓ => φ (linkHead ℓ) - φ (linkTail ℓ)

end MaxwellDefs

section MaxwellAtom

/-- The atom's sign vector `v = (1, 1, −1, −1)` in the
(B, R, T, L) edge order (memo §3, M4). -/
def atomVec : Fin 4 → ℝ := ![1, 1, -1, -1]

/-- The single-plaquette angle pattern on four edge values
`x : Fin 4 → ℝ` in (B, R, T, L) order:
`x 0 + x 1 − x 2 − x 3`. -/
def plaqPattern (x : Fin 4 → ℝ) : ℝ :=
  x 0 + x 1 - x 2 - x 3

/-- The **single-plaquette atom operator** (memo §3, M4):
the rank-one local operator on a plaquette's four edge
values, `(maxwellAtomOp x) i = plaqPattern x * atomVec i`. -/
def maxwellAtomOp : Module.End ℝ (Fin 4 → ℝ) where
  toFun x i := plaqPattern x * atomVec i
  map_add' x y := by
    funext i
    simp only [plaqPattern, Pi.add_apply]
    ring
  map_smul' c x := by
    funext i
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul,
      plaqPattern]
    ring

end MaxwellAtom

section MaxwellProps

/-- **(M1) Form identity + positivity** (memo §3, stated
verbatim in substance). The form of `maxwellOp N` is
`maxwellQuad N`, in the coordinate form of the Euclidean
inner product (see the registration-form note on the module
face), and that form is nonnegative:
`(∀ θ, ∑ ℓ, θ ℓ * (maxwellOp N θ) ℓ = maxwellQuad N θ)` and
`(∀ θ, 0 ≤ ∑ ℓ, θ ℓ * (maxwellOp N θ) ℓ)`.
Target of MAX-2. **Not asserted to hold in this brick.** -/
noncomputable def maxwellM1 (N : ℕ) [NeZero N] : Prop :=
  (∀ θ : linkAngle N,
      (∑ ℓ, θ ℓ * (maxwellOp N θ) ℓ) = maxwellQuad N θ) ∧
  (∀ θ : linkAngle N,
      0 ≤ ∑ ℓ, θ ℓ * (maxwellOp N θ) ℓ)

/-- **(M2) Kernel = flat link angles** (memo §3, stated
verbatim): `maxwellOp N θ = 0` iff every registered
plaquette angle vanishes. Failable: the ↔ dies if the
plaquette enumeration misses a class. Target of MAX-2.
**Not asserted to hold in this brick.** -/
noncomputable def maxwellM2 (N : ℕ) [NeZero N] : Prop :=
  ∀ θ : linkAngle N,
    maxwellOp N θ = 0 ↔
      ∀ P ∈ allPlaqData N, plaqAngle P θ = 0

/-- **(M3) Gauge modes are in the kernel** (memo §3, stated
verbatim): for every site potential `φ`, the pure-gauge
angle `gaugeAngle φ` has vanishing plaquette angle at every
plaquette datum — additive telescoping, the additive form
of the corpus's landed `PlaqHol` telescoping. Target of
MAX-2. **Not asserted to hold in this brick.** -/
def maxwellM3 (N : ℕ) [NeZero N] : Prop :=
  ∀ φ : LayerSite N → ℝ, ∀ P : PlaqDatum N,
    plaqAngle P (gaugeAngle φ) = 0

/-- **(M4) The single-plaquette atom** (memo §3, stated
verbatim): the local operator on one plaquette's four edge
values is rank one, `maxwellAtomOp x = plaqPattern x • v`
with `v = (1, 1, −1, −1)` in (B, R, T, L) order; its
spectrum is exactly **{4, 0, 0, 0}** — eigenvalue `4` with
eigenvector `v`, eigenvalue `0`, and no other eigenvalue;
its kernel is `{x | x 0 + x 1 = x 2 + x 3}`, of dimension
`3`; and its Rayleigh form is `∑ i, x i * (maxwellAtomOp x) i
= (plaqPattern x)²`. Seat values {4, 0, 0, 0} are the
K-MAX-3 registered values for this seat. Target of MAX-1.
**Not asserted to hold in this brick.** -/
def maxwellM4 : Prop :=
  (∀ x : Fin 4 → ℝ, maxwellAtomOp x = plaqPattern x • atomVec) ∧
  Module.End.HasEigenvalue maxwellAtomOp 4 ∧
  Module.End.HasEigenvalue maxwellAtomOp 0 ∧
  (∀ μ : ℝ, Module.End.HasEigenvalue maxwellAtomOp μ →
      μ = 4 ∨ μ = 0) ∧
  (∀ x : Fin 4 → ℝ, maxwellAtomOp x = 0 ↔ x 0 + x 1 = x 2 + x 3) ∧
  Module.finrank ℝ (LinearMap.ker maxwellAtomOp) = 3 ∧
  (∀ x : Fin 4 → ℝ,
      (∑ i, x i * (maxwellAtomOp x) i) = (plaqPattern x) ^ 2)

/-- The **FINITE transverse eigenvalue** at spatial momentum
`k = (k₁, k₂, k₃)`, `kᵢ ∈ ZMod N` (memo §3, M5):
`4·(sin²(πk₁/N) + sin²(πk₂/N) + sin²(πk₃/N))`, with each
`kᵢ` read through its representative value in `ℕ`. A
property of the chosen FINITE operator at spacing 1; its
continuum namesake is never asserted (K-MAX-2). -/
noncomputable def maxwellTransverseEig (N : ℕ)
    (k : Fin 3 → ZMod N) : ℝ :=
  4 * ∑ i, Real.sin (Real.pi * ((k i).val : ℝ) / (N : ℝ)) ^ 2

/-- **(M5) Cube spectrum + gap — FINITE** (memo §3, stated
verbatim in substance; the word FINITE is part of the
statement at every occurrence of this line's dispersion).
At general Even `N`: at every spatial momentum
`k = (k₁, k₂, k₃)`, `kᵢ ∈ ZMod N`, the transverse value
`4·Σᵢ sin²(πkᵢ/N)` is an eigenvalue of `maxwellOp N`
(the Fourier link modes diagonalize the operator) and `0`
is an eigenvalue (the longitudinal mode); at `k ≠ 0` the
transverse eigenvalue carries two linearly independent
eigenmodes (multiplicity 2, registered as a pairwise
independence witness). The **gap above the kernel** is
exactly `4·sin²(π/N)`: it is attained — at a momentum with
exactly one component equal to `1`, e.g. `k = (1, 0, 0)`,
whose transverse value is the gap value — and every
eigenvalue is either `0` or at least the gap. The gap value
`4·sin²(π/N)` is the K-MAX-3 registered value for this seat.
Target of MAX-3. **Not asserted to hold in this brick.** -/
noncomputable def maxwellM5 (N : ℕ) [NeZero N] (_hN : Even N) :
    Prop :=
  (∀ k : Fin 3 → ZMod N,
      Module.End.HasEigenvalue (maxwellOp N)
          (maxwellTransverseEig N k) ∧
      Module.End.HasEigenvalue (maxwellOp N) 0) ∧
  (∀ k : Fin 3 → ZMod N, k ≠ 0 →
      ∃ θ₁ θ₂ : linkAngle N,
        (∀ a b : ℝ, a • θ₁ + b • θ₂ = 0 → a = 0 ∧ b = 0) ∧
        maxwellOp N θ₁
            = (maxwellTransverseEig N k) • θ₁ ∧
        maxwellOp N θ₂
            = (maxwellTransverseEig N k) • θ₂) ∧
  Module.End.HasEigenvalue (maxwellOp N)
      (4 * Real.sin (Real.pi / (N : ℝ)) ^ 2) ∧
  (∀ μ : ℝ, Module.End.HasEigenvalue (maxwellOp N) μ →
      μ = 0 ∨ 4 * Real.sin (Real.pi / (N : ℝ)) ^ 2 ≤ μ) ∧
  (∃ k : Fin 3 → ZMod N,
      k 0 = 1 ∧ k 1 = 0 ∧ k 2 = 0 ∧
      maxwellTransverseEig N k
        = 4 * Real.sin (Real.pi / (N : ℝ)) ^ 2)

end MaxwellProps

end ThetLogos
