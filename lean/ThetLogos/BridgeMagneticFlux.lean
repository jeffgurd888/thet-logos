import Mathlib.Tactic
import Mathlib.Analysis.Complex.Circle
import ThetLogos.BridgeMagneticHeat
import ThetLogos.BridgeCompletion

open scoped InnerProductSpace

/-!
# BridgeMagneticFlux — STEM bridge brick B4′: face-restricted flux-dependence

*STEM = Spectral–Thermal ElectroMagnetic (Jeff's name, 2026-10-24).*

**NO CLAIM.** This module is brick **B4′** of the STEM bridge scoped in
`whitepaper/stem-bridge-scoping-2026-10-24.md`: the charter's statement
**S4** (flux-dependence) restricted, exactly as the charter pre-names,
to graphs equipped with the face data of `BridgeCompletion` §9 — faces
are `GraphFace` boundary quadruples `a → b → c → d → a`, and the gauge
class is read from the **face holonomies**, the products of the
connection `θ` around face boundaries. What lands here:

- **Invariance (§2).** The face holonomy `faceHol bd θ f` is a
  gauge-class invariant: it is unchanged by B2's gauge action
  (`faceHol_gauge`), it is `1` for a pure gauge and at zero field, it
  is multiplicative in the connection, and two connections whose face
  holonomies differ at some face are **not** gauge-equivalent — face
  data distinguishes gauge classes.
- **Determination on a face (§3).** On one genuine face (four
  pairwise-distinct boundary vertices), the holonomy is the *complete*
  gauge invariant: there is a gauge transformation making three
  boundary edges of the transformed connection equal to `1` and the
  closing edge equal to exactly the holonomy (`face_trivialize`);
  hence two connections with the same face holonomy are
  gauge-equivalent on that face's boundary.
- **The readings package (§4).** Gauge-equivalent connections share
  their face holonomies, their spectrum (B2), and their heat trace
  (B3) — the three things the bridge reads are all functions of the
  gauge class.

**What this brick does NOT prove — the fence, on the face.** Face
holonomies do not, in general, determine the spectrum or the heat
trace: a general finite graph has cycles that are not faces, and the
gauge class is fixed by holonomies around a full cycle basis, not by
face data alone. That general statement is brick **B4** (spanning-tree
gauge fixing / cycle-space machinery the corpus does not yet hold),
and it remains the named remainder: **landing B4′ leaves the bridge
PARTIAL**, as the charter records. "Flux-dependence" in this module
means exactly the dependence of the finite operator's gauge class —
and, on a face, of its boundary values — on the connection `θ` through
its face holonomies. Nothing more.

**Fences (charter §5, on the face).** This is finite graph
bookkeeping: a U(1) connection on a finite graph, its loop products,
and finite-dimensional operators. It is **not** Maxwell theory
(continuum Maxwell has NO SEAT in this corpus), not a
force-unification claim, not a torsion claim, and not a modular-flux
claim — the killed EM-torsion paste, the killed "strong nuclear =
electromagnetic" identification, and the killed magnetophase flux
(`ModularFlux.magnetophaseFlux_vanishes`) stay killed. Parts of any
official Clay statement closed by this module: **0**.

Conventions follow B1–B3: `θ a b` is the phase of transport from `b`
to `a`, so transport along the boundary step `a → b` carries the phase
`θ b a`; the gauge action is B2's `gaugeConn`. Admission rules: A1 —
the connection and its gauge action are named throughout; A2 — the
zero-field specialization is checked in §2 (`faceHol_one`: at
`θ ≡ 1` every face holonomy is `1`, matching the exhibit's trivial
circulation at zero field); A3 — "spectrum" means eigenvalues of the
named operator `magLin w θ`, "heat trace" is B3's `magHeatTrace`.
Unlike S1's energy identity, the face machinery needs **no** symmetry
hypothesis on `w` and **no** antisymmetry hypothesis on `θ`: the B2/B3
corollaries consumed here are unconditional.

- Status: brick B4′ — built 2026-10-24 under the STEM bridge
  charter; parent-verified 2026-10-24 (targeted build exit 0,
  strict recount, axiom check); verdict STANDS. Dossier:
  `whitepaper/stem-b4prime-flux-2026-10-24.md`.
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V] {F : Type*}

/-! ## §1. The face holonomy

The multiplicative analogue of `BridgeCompletion`'s additive
`edgeCirculation`: where a real edge field is *summed* around a face
boundary, a `Circle`-valued connection is *multiplied* around it. -/

/-- **The face holonomy** of a connection `θ` around the face `f`:
the product of the transport phases around the boundary loop
`a → b → c → d → a` of the `GraphFace` `bd f`. In B1's convention
(`θ x y` = phase of transport from `y` to `x`), the step `a → b`
carries `θ b a`, and so on around the loop. This is the discrete
holonomy of the connection on the face — the flux through the face,
in the only form a `Circle`-valued connection carries it. -/
noncomputable def faceHol (bd : F → GraphFace V)
    (θ : V → V → Circle) (f : F) : Circle :=
  θ (bd f).b (bd f).a * θ (bd f).c (bd f).b
    * θ (bd f).d (bd f).c * θ (bd f).a (bd f).d

theorem faceHol_apply (bd : F → GraphFace V) (θ : V → V → Circle)
    (f : F) :
    faceHol bd θ f
      = θ (bd f).b (bd f).a * θ (bd f).c (bd f).b
        * θ (bd f).d (bd f).c * θ (bd f).a (bd f).d := rfl

/-! ## §2. Invariance: face holonomies are gauge-class data -/

/-- **Zero-field weld check (A2).** At the trivial connection every
face holonomy is `1`: zero field, zero flux through every face —
the multiplicative form of the exhibit's vanishing circulation for
potential fields at the weld. -/
theorem faceHol_one (bd : F → GraphFace V) (f : F) :
    faceHol bd 1 f = 1 := by
  simp [faceHol]

/-- **The face holonomy is multiplicative in the connection**: the
holonomy of a pointwise product of connections is the product of the
holonomies. The face holonomies are characters of the connection
group, one per face. -/
theorem faceHol_mul (bd : F → GraphFace V)
    (θ₁ θ₂ : V → V → Circle) (f : F) :
    faceHol bd (θ₁ * θ₂) f = faceHol bd θ₁ f * faceHol bd θ₂ f := by
  simp only [faceHol, Pi.mul_apply]
  ac_rfl

/-- **The gauge action is multiplication by a pure gauge**: the
conjugated connection factors as the pointwise product of the
pure-gauge connection `gaugeConn g 1` (the coboundary of `g`) with
`θ` itself. -/
theorem gaugeConn_eq_gaugeConn_one_mul (g : V → Circle)
    (θ : V → V → Circle) :
    gaugeConn g θ = gaugeConn g 1 * θ := by
  funext i j
  simp only [Pi.mul_apply, gaugeConn_apply, Pi.one_apply, mul_one]
  ac_rfl

/-- **A pure gauge has no flux**: the holonomy of a connection
gauge-generated from the trivial connection is `1` at every face —
around the closed loop, each vertex phase meets its own inverse. -/
theorem faceHol_gaugeConn_one (bd : F → GraphFace V)
    (g : V → Circle) (f : F) :
    faceHol bd (gaugeConn g 1) f = 1 := by
  simp only [faceHol, gaugeConn_apply, Pi.one_apply, mul_one]
  calc (g (bd f).b * (g (bd f).a)⁻¹) * (g (bd f).c * (g (bd f).b)⁻¹)
        * (g (bd f).d * (g (bd f).c)⁻¹) * (g (bd f).a * (g (bd f).d)⁻¹)
      = (g (bd f).b * (g (bd f).b)⁻¹) * (g (bd f).c * (g (bd f).c)⁻¹)
        * (g (bd f).d * (g (bd f).d)⁻¹)
        * (g (bd f).a * (g (bd f).a)⁻¹) := by ac_rfl
    _ = 1 := by simp

/-- **Gauge invariance of the face holonomy** (the forward half of
face-restricted S4): conjugating the connection by a gauge
transformation `g` multiplies it by a pure gauge
(`gaugeConn_eq_gaugeConn_one_mul`), a pure gauge contributes
holonomy `1` (`faceHol_gaugeConn_one`), and holonomy is
multiplicative in the connection (`faceHol_mul`) — the product is
unchanged. The face holonomy is a function of the gauge class
of `θ`. -/
theorem faceHol_gauge (bd : F → GraphFace V) (g : V → Circle)
    (θ : V → V → Circle) (f : F) :
    faceHol bd (gaugeConn g θ) f = faceHol bd θ f := by
  rw [gaugeConn_eq_gaugeConn_one_mul, faceHol_mul,
    faceHol_gaugeConn_one, one_mul]

/-- Face holonomies of gauge-equivalent connections agree, at every
face. -/
theorem faceHol_congr_gauge (bd : F → GraphFace V)
    (θ₁ θ₂ : V → V → Circle) (g : V → Circle)
    (h : θ₂ = gaugeConn g θ₁) (f : F) :
    faceHol bd θ₂ f = faceHol bd θ₁ f := by
  rw [h]
  exact faceHol_gauge bd g θ₁ f

/-- **Face data distinguishes gauge classes**: if two connections
have different holonomy at some face, no gauge transformation
carries one to the other. The contrapositive of `faceHol_gauge` —
the face reading is a genuine gauge-class observable, not a
gauge artifact. -/
theorem not_gaugeEquiv_of_faceHol_ne (bd : F → GraphFace V)
    (θ₁ θ₂ : V → V → Circle) (f : F)
    (h : faceHol bd θ₂ f ≠ faceHol bd θ₁ f) :
    ¬ ∃ g : V → Circle, θ₂ = gaugeConn g θ₁ := by
  rintro ⟨g, hg⟩
  exact h (faceHol_congr_gauge bd θ₁ θ₂ g hg f)

/-! ## §3. Determination on a face: the holonomy is the whole story

The general S4 would fix a gauge on a spanning tree of the whole
graph — B4's missing machinery. On a *single* face no tree is
needed: the boundary is a 4-cycle, and walking the gauge values
around it trivializes the connection edge by edge. The one point of
honesty: the walk needs the four boundary vertices to be pairwise
distinct. `GraphFace` itself imposes no distinctness (a degenerate
quadruple is a legal face datum), so distinctness is carried as an
explicit hypothesis — B4′'s named side condition, the face-level
shadow of the spanning-tree choice B4 will have to make globally. -/

/-- **Solving a gauge-transformed value back**: the original phase
is the endpoint-corrected value of the transformed phase. -/
theorem gaugeConn_solve (g : V → Circle) (θ : V → V → Circle)
    (i j : V) :
    θ i j = (g i)⁻¹ * gaugeConn g θ i j * g j := by
  simp only [gaugeConn_apply]
  group

/-- **The gauge action is an action**: successive gauge
transformations compose by pointwise multiplication of the gauge
functions. -/
theorem gaugeConn_comp (g₁ g₂ : V → Circle) (θ : V → V → Circle) :
    gaugeConn g₂ (gaugeConn g₁ θ) = gaugeConn (g₂ * g₁) θ := by
  funext i j
  simp only [gaugeConn_apply, Pi.mul_apply, mul_inv_rev]
  ac_rfl

/-- **Face trivialization** (the determination half of
face-restricted S4): on a genuine face — four pairwise-distinct
boundary vertices — every connection is gauge-equivalent, on the
face's boundary, to one whose three walking edges are trivial and
whose closing edge carries exactly the face holonomy. The gauge is
built by walking the loop: at each new vertex, the gauge value is
chosen to cancel the phase just crossed; the closing edge then has
no freedom left, and what remains there is the holonomy. The face
holonomy is the *complete* gauge invariant of a connection on a
face. -/
theorem face_trivialize (bd : F → GraphFace V) (θ : V → V → Circle)
    (f : F)
    (hab : (bd f).a ≠ (bd f).b) (hac : (bd f).a ≠ (bd f).c)
    (had : (bd f).a ≠ (bd f).d) (hbc : (bd f).b ≠ (bd f).c)
    (hbd : (bd f).b ≠ (bd f).d) (hcd : (bd f).c ≠ (bd f).d) :
    ∃ g : V → Circle,
      gaugeConn g θ (bd f).b (bd f).a = 1
        ∧ gaugeConn g θ (bd f).c (bd f).b = 1
        ∧ gaugeConn g θ (bd f).d (bd f).c = 1
        ∧ gaugeConn g θ (bd f).a (bd f).d = faceHol bd θ f := by
  set g : V → Circle := fun x => if x = (bd f).d then
            (θ (bd f).b (bd f).a)⁻¹ * (θ (bd f).c (bd f).b)⁻¹
              * (θ (bd f).d (bd f).c)⁻¹
          else if x = (bd f).c then
            (θ (bd f).b (bd f).a)⁻¹ * (θ (bd f).c (bd f).b)⁻¹
          else if x = (bd f).b then (θ (bd f).b (bd f).a)⁻¹
          else 1 with hg_def
  have hga : g (bd f).a = 1 := by
    rw [hg_def]
    dsimp only
    rw [if_neg had, if_neg hac, if_neg hab]
  have hgb : g (bd f).b = (θ (bd f).b (bd f).a)⁻¹ := by
    rw [hg_def]
    dsimp only
    rw [if_neg hbd, if_neg hbc, if_pos rfl]
  have hgc : g (bd f).c
      = (θ (bd f).b (bd f).a)⁻¹ * (θ (bd f).c (bd f).b)⁻¹ := by
    rw [hg_def]
    dsimp only
    rw [if_neg hcd, if_pos rfl]
  have hgd : g (bd f).d
      = (θ (bd f).b (bd f).a)⁻¹ * (θ (bd f).c (bd f).b)⁻¹
        * (θ (bd f).d (bd f).c)⁻¹ := by
    rw [hg_def]
    dsimp only
    rw [if_pos rfl]
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · -- edge (b, a): the first walking step cancels exactly
    simp only [gaugeConn_apply]
    rw [hgb, hga]
    simp
  · -- edge (c, b): the second walking step
    simp only [gaugeConn_apply]
    rw [hgc, hgb]
    group
  · -- edge (d, c): the third walking step
    simp only [gaugeConn_apply]
    rw [hgd, hgc]
    group
  · -- closing edge (a, d): no freedom left — the holonomy remains
    simp only [gaugeConn_apply, faceHol]
    rw [hga, hgd]
    simp only [one_mul, mul_inv_rev, inv_inv]
    ac_rfl

/-- **A face with unit holonomy is pure gauge on its boundary**: if
`faceHol bd θ f = 1`, some gauge transformation makes all four
boundary values of the transformed connection equal to `1` — on
this face, `θ` is gauge-equivalent to the trivial connection. -/
theorem face_trivialize_of_faceHol_eq_one (bd : F → GraphFace V)
    (θ : V → V → Circle) (f : F)
    (hab : (bd f).a ≠ (bd f).b) (hac : (bd f).a ≠ (bd f).c)
    (had : (bd f).a ≠ (bd f).d) (hbc : (bd f).b ≠ (bd f).c)
    (hbd : (bd f).b ≠ (bd f).d) (hcd : (bd f).c ≠ (bd f).d)
    (hH : faceHol bd θ f = 1) :
    ∃ g : V → Circle,
      gaugeConn g θ (bd f).b (bd f).a = 1
        ∧ gaugeConn g θ (bd f).c (bd f).b = 1
        ∧ gaugeConn g θ (bd f).d (bd f).c = 1
        ∧ gaugeConn g θ (bd f).a (bd f).d = 1 := by
  obtain ⟨g, h₁, h₂, h₃, h₄⟩ :=
    face_trivialize bd θ f hab hac had hbc hbd hcd
  exact ⟨g, h₁, h₂, h₃, h₄.trans hH⟩

/-- **Equal face holonomy ⇒ gauge-equivalent on the face**: two
connections with the same holonomy at a genuine face are carried
to each other, on that face's four boundary values, by a single
gauge transformation (the composite of one trivialization and the
inverse of the other, via `gaugeConn_comp`). Together with
`faceHol_gauge` this is the face-restricted S4 in both directions:
on a face, the gauge class and the holonomy determine each other. -/
theorem face_gaugeEquiv_of_faceHol_eq (bd : F → GraphFace V)
    (θ₁ θ₂ : V → V → Circle) (f : F)
    (hab : (bd f).a ≠ (bd f).b) (hac : (bd f).a ≠ (bd f).c)
    (had : (bd f).a ≠ (bd f).d) (hbc : (bd f).b ≠ (bd f).c)
    (hbd : (bd f).b ≠ (bd f).d) (hcd : (bd f).c ≠ (bd f).d)
    (hH : faceHol bd θ₁ f = faceHol bd θ₂ f) :
    ∃ g : V → Circle,
      gaugeConn g θ₂ (bd f).b (bd f).a = θ₁ (bd f).b (bd f).a
        ∧ gaugeConn g θ₂ (bd f).c (bd f).b = θ₁ (bd f).c (bd f).b
        ∧ gaugeConn g θ₂ (bd f).d (bd f).c = θ₁ (bd f).d (bd f).c
        ∧ gaugeConn g θ₂ (bd f).a (bd f).d = θ₁ (bd f).a (bd f).d := by
  obtain ⟨g₁, h₁₁, h₁₂, h₁₃, h₁₄⟩ :=
    face_trivialize bd θ₁ f hab hac had hbc hbd hcd
  obtain ⟨g₂, h₂₁, h₂₂, h₂₃, h₂₄⟩ :=
    face_trivialize bd θ₂ f hab hac had hbc hbd hcd
  refine ⟨(fun i => (g₁ i)⁻¹) * g₂, ?_, ?_, ?_, ?_⟩ <;>
    rw [← gaugeConn_comp, gaugeConn_apply, inv_inv]
  · rw [h₂₁, gaugeConn_solve g₁ θ₁ (bd f).b (bd f).a, h₁₁]
  · rw [h₂₂, gaugeConn_solve g₁ θ₁ (bd f).c (bd f).b, h₁₂]
  · rw [h₂₃, gaugeConn_solve g₁ θ₁ (bd f).d (bd f).c, h₁₃]
  · rw [h₂₄, gaugeConn_solve g₁ θ₁ (bd f).a (bd f).d, h₁₄, hH]

/-! ## §4. The readings package: what the bridge reads is gauge-class data

B4′'s place in the bridge, stated once: everything the bridge reads
off a connection — its face holonomies (this brick), its spectrum
(B2's `magLin_gauge_hasEigenvalue`), its heat trace (B3's
`magHeatTrace_gauge`) — is constant on gauge classes. Per the fence
in this module's header, the converse at the level of spectrum and
heat trace is **not** asserted: face holonomies alone do not fix
them on a general graph. That is B4's remainder. -/

/-- **The readings package**: if `θ₂` is a gauge transform of `θ₁`,
then at every face the face holonomies agree, the spectra of
`magLin w θ₂` and `magLin w θ₁` agree eigenvalue by eigenvalue, and
the heat traces agree at every time. The bridge's three readings
are functions of the gauge class of the connection — and, by §3,
on any single face the gauge class is in turn read off the face
holonomy. -/
theorem gaugeClass_readings (bd : F → GraphFace V) (w : V → V → ℝ)
    (θ₁ θ₂ : V → V → Circle) (g : V → Circle)
    (h : θ₂ = gaugeConn g θ₁) (f : F) (μ : ℂ) (t : ℝ) :
    faceHol bd θ₂ f = faceHol bd θ₁ f
      ∧ (Module.End.HasEigenvalue (magLin w θ₂) μ
          ↔ Module.End.HasEigenvalue (magLin w θ₁) μ)
      ∧ magHeatTrace w θ₂ t = magHeatTrace w θ₁ t := by
  subst h
  exact ⟨faceHol_gauge bd g θ₁ f, magLin_gauge_hasEigenvalue w g θ₁ μ,
    magHeatTrace_gauge w g θ₁ t⟩

end ThetLogos
