import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Group.Circle
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Circle
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# ThetLogos.LatticeGauge — Pitch 4, Stage 0: finite lattice gauge theory (T1)

HONESTY LEDGER (read before citing):

- Everything in this file is **T1 finite lattice algebra and finite
  integration**: a finite site type `Λ` with four commuting shift
  permutations `σ : Fin 4 → Equiv.Perm Λ`, group-valued link variables
  `U : (Λ × Fin 4) → G` for a compact group `G`, a unitary representation
  `ρ` of `G` on `ℂ^d`, the Wilson action built from plaquette traces,
  the product of normalized Haar measures over the links, and the
  Gibbs expectations defined as ratios of integrals against that finite
  product measure. Zero sorrys, no new axioms (headline theorems are
  checked against the standard three — `propext`, `Classical.choice`,
  `Quot.sound` — and the audit is recorded in the dossier
  `whitepaper/pitch-4-stage-0-2026-10-17.md`).

- *(finite-lattice discipline)* "Results in this module are about a
  finite lattice at fixed spacing and volume. Nothing here is a
  continuum result; the words 'continuum', 'ℝ⁴', and 'Poincaré' do
  not describe anything proved in this module."

- *(gap discipline)* "Any gap statement in this module is a lattice
  statement at the stated $(a, L, \beta)$. No continuum mass gap is
  claimed; a lattice gap transfers to the continuum only with
  uniformity in the spacing along the tuning curve, which is not
  proved here or anywhere in this corpus." (This module in fact proves
  no gap statement of any kind; the clause travels with the pitch.)

- *(gauge discipline)* "Gauge invariance here is exact invariance of
  a finite lattice action and measure under finite gauge
  transformations. It is not a continuum gauge theory, and this module
  contains no quantized continuum gauge field."

- *(RG discipline — included early, since this module's successors
  will carry it)* "A blocking step is a map, not the flow; no
  β-function, fixed-point criticality, or continuum limit is stated or
  implied by anything in this module." (No blocking step is defined
  here either; that is Stage 2.)

- *(standing charter)* "Parts of the official Clay Yang–Mills
  statement closed by this module: 0."

DESIGN CHOICES (the choices §6.1 of the Pitch 4 scoping delegated,
disclosed):

- **Lattice presentation.** Abstract first: sites are a finite type
  `Λ` equipped with four shift bijections `σ μ : Equiv.Perm Λ`;
  pairwise commutation of the shifts is a *hypothesis* on the
  theorems that need it (plaquette conjugation, the plaquette as a
  closed loop), never baked into the definitions. The concrete torus
  `Fin 4 → ZMod N` (cyclic coordinate shifts, by `Equiv.addLeft` of a
  basis vector) is instantiated in §8 and proved to satisfy the
  abstract hypotheses, so the abstract layer is inhabited by the
  intended model.
- **Gauge group and representation.** `G` is an abstract group for the
  algebra (§1–§4) and a compact topological group for the measure
  (§5–§6). The trace layer uses a fixed monoid homomorphism
  `ρ : G →* ↥(unitaryGroup (Fin d) ℂ)`; `repMatrix ρ g` is its matrix.
  Statements are proved for general `(G, ρ)` wherever they run — and
  they do run, including the β = 0 package. Two instance families are
  discharged in §7: the circle `Circle` with its fundamental
  representation (`d = 1`), and the unitary group
  `↥(unitaryGroup (Fin d) ℂ)` itself with the identity representation
  (whose `d = 2` case is the SU(2)-shaped case up to the determinant
  condition, which the expectations proved here do not see). No
  instance is abelian-only: the landing is not PARTIAL-γ.
- **Plaquette convention.** For sites `x` and directions `μ ν`,
  `U_p(x,μ,ν) = U(x,μ) · U(σ μ x, ν) · (U(σ ν x, μ))⁻¹ · (U(x,ν))⁻¹`
  (ordered product counterclockwise from `(x,μ)`). Swapping `μ ν`
  inverts the plaquette (`plaquette_swap`).
- **Action counting.** `S_β(U) = β · Σ_x Σ_{μ} Σ_{ν > μ} (1 − (1/d)
  Re tr ρ(U_p(x,μ,ν)))` — each unordered plaquette counted once.
- **Measure device.** The configuration measure is the finite product
  of a normalized Haar probability measure `haarProb G` over the
  links. `haarProb G` is constructed in-file from Mathlib's `haar`
  (normalized by its total mass), and its right-invariance and
  inversion-invariance are *proved* in-file from uniqueness of
  normalized Haar measure on a compact group. The measure statements
  of §5 are parametrized over any `μG` carrying the four classes
  `[IsProbabilityMeasure μG] [IsMulLeftInvariant μG]
  [IsMulRightInvariant μG] [IsInvInvariant μG]`, so they apply to
  `haarProb G` by instance.
- **Expectation device.** The Gibbs expectation `gibbsExpect β F` is
  *defined* as the ratio `∫ e^{-S_β} F dμ / ∫ e^{-S_β} dμ` (the
  standard normalized-integral device; no separate Gibbs measure
  object is constructed). The denominator is proved positive for
  `β ≥ 0` (`gibbsDenom_pos`), so the ratio is honest wherever
  that hypothesis is in force.

- **Second-countability hypothesis.** The integration sections
  (§6–§7) carry a `[SecondCountableTopology G]` hypothesis (it is
  what makes multiplication of `G`-valued measurable functions
  measurable in this Mathlib). It is disclosed here rather than hidden
  in instance arguments; both instance families of §8 satisfy it
  (for the unitary group the instance is supplied in-module, §8).

WHAT LANDED, per the scoped package of §6.1:

1. Gauge action; plaquettes conjugate under it (needs commuting
   shifts); hence trace and action are exactly invariant for **all**
   `g : Λ → G` (`wilsonAction_gauge_invariant`) — the stage's headline.
2. The product Haar measure on configurations is invariant under the
   gauge action (`configMeasure_map_gaugeAction`), with the integral
   form as corollary.
3. Wilson loops for closed lattice paths (the path formalism of §4):
   gauge invariance by the same conjugation-plus-trace argument
   (`wilsonLoop_gauge_invariant`); the plaquette is exhibited as a
   closed loop (`loopProd_plaquetteSteps`).
4. The β = 0 package: `gibbsExpect` at `β = 0` is the plain Haar
   expectation; the Haar intertwiner `P = ∫ ρ dμ` is a projection onto
   the ρ-fixed vectors (`haarIntertwiner_idempotent`,
   `repMatrix_mulVec_haarIntertwiner`, `haarIntertwiner_mulVec_of_fixed`);
   the intertwiner is defined entrywise, as a matrix of scalar Haar
   integrals (the Bochner integral of a matrix-valued function is its
   entrywise integral);
   the plaquette expectation is `⟨W_p⟩₀ = tr P`
   (`gibbsExpect_zero_plaquette`), which vanishes when ρ has no
   nonzero fixed vectors. Both instance families (circle; unitary
   group, every `d`) have no fixed vectors, so both get `⟨W_p⟩₀ = 0`.
5. Finite identities: trivial-configuration plaquette `= 1`;
   plaquette orientation `U_p(x,ν,μ) = U_p(x,μ,ν)⁻¹`; action
   nonnegativity for `β ≥ 0` from the unitary trace bound
   `Re tr A ≤ d` (`re_trace_le_of_mem_unitaryGroup`,
   `abs_entry_of_mem_unitaryGroup`).

PRE-KILLS HONORED (binding, from §6.1): **no gauge fixing anywhere** —
invariance is proved for all `g`; **group-valued links only** — no
Lie-algebra variable appears; **`β` is a bare parameter** — no
coupling/scale language; the formal `a → 0` expansion
`U_p = exp(i a² F_{μν} + O(a³))` is **not** a theorem here (it is a
statement about continuum fields; context only, T5-context, and it
appears in this header only to be disclaimed); **no continuum word**
is applied to any result; no mass-gap language; no Hilbert space, no
Hamiltonian, no dynamics — this stage's measure is a probability
measure on configurations, not a quantum theory.

PRICED REMAINDERS (named, not hidden): reflection positivity and the
transfer matrix are Stage 1b; the strong-coupling/cluster expansion
is Stage 1c; neither is attempted here. The β = 0 plaquette
computation assumes the plaquette's four links are pairwise distinct,
which on the abstract lattice reduces to the two hypotheses
`σ μ x ≠ x`, `σ ν x ≠ x` (the direction coordinates already separate
the other pairs); on the torus these are discharged for `N ≥ 2`.
Nothing else is priced: the general-`(G, ρ)` β = 0 statement landed,
so no shaped-instance partial was needed.

This module is NOT in the root import list of the library (the corpus
pattern for recent exhibits); it is verified by a targeted build.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal

/-! ## §1. Sites, links, configurations, and the gauge action

Pure group algebra: `G` is an abstract group here. -/

section Algebra

variable {Λ : Type*} [Fintype Λ] {G : Type*} [Group G]
variable (σ : Fin 4 → Equiv.Perm Λ)

/-- A lattice link: a site together with a direction. -/
abbrev Link (Λ : Type*) : Type _ := Λ × Fin 4

/-- A gauge configuration: a group element on every link. -/
abbrev Config (Λ : Type*) (G : Type*) : Type _ := (Λ × Fin 4) → G

/-- The gauge action of `g : Λ → G` on a configuration `U`:
`(U^g)(x, μ) = g x * U(x, μ) * (g (σ μ x))⁻¹`. -/
def gaugeAction (g : Λ → G) (U : Config Λ G) : Config Λ G :=
  fun ℓ => g ℓ.1 * U ℓ * (g (σ ℓ.2 ℓ.1))⁻¹

@[simp]
theorem gaugeAction_apply (g : Λ → G) (U : Config Λ G) (x : Λ) (μ : Fin 4) :
    gaugeAction σ g U (x, μ) = g x * U (x, μ) * (g (σ μ x))⁻¹ := rfl

theorem gaugeAction_one (U : Config Λ G) : gaugeAction σ (fun _ => 1) U = U := by
  funext ℓ
  simp [gaugeAction]

theorem gaugeAction_mul (g h : Λ → G) (U : Config Λ G) :
    gaugeAction σ (fun x => g x * h x) U = gaugeAction σ g (gaugeAction σ h U) := by
  funext ⟨x, μ⟩
  simp only [gaugeAction_apply]
  group

/-! ## §2. Plaquettes and the Wilson action

The representation `ρ` enters here, as data: a monoid homomorphism
into the unitary matrices. No topology yet. -/

/-- The ordered plaquette product at site `x` in directions `μ ν`:
`U(x,μ) * U(σ μ x, ν) * (U(σ ν x, μ))⁻¹ * (U(x,ν))⁻¹`. -/
def plaquette (U : Config Λ G) (x : Λ) (μ ν : Fin 4) : G :=
  U (x, μ) * U (σ μ x, ν) * (U (σ ν x, μ))⁻¹ * (U (x, ν))⁻¹

/-- Plaquettes conjugate under gauge transformations. This is the one
place the commutation of the shifts is spent: the two paths around
the square must end at the same site. -/
theorem plaquette_gauge (hσ : ∀ μ ν x, σ μ (σ ν x) = σ ν (σ μ x)) (g : Λ → G)
    (U : Config Λ G) (x : Λ) (μ ν : Fin 4) :
    plaquette σ (gaugeAction σ g U) x μ ν = g x * plaquette σ U x μ ν * (g x)⁻¹ := by
  have h : σ ν (σ μ x) = σ μ (σ ν x) := hσ ν μ x
  simp only [plaquette, gaugeAction_apply, mul_inv_rev, inv_inv, h]
  group

/-- The plaquette of the trivial configuration is `1`. -/
theorem plaquette_one (x : Λ) (μ ν : Fin 4) :
    plaquette σ (fun _ => (1 : G)) x μ ν = 1 := by
  simp [plaquette]

/-- Orientation: swapping the directions inverts the plaquette. -/
theorem plaquette_swap (U : Config Λ G) (x : Λ) (μ ν : Fin 4) :
    plaquette σ U x ν μ = (plaquette σ U x μ ν)⁻¹ := by
  simp only [plaquette, mul_inv_rev, inv_inv]
  group

section Representation

variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The matrix of the representation `ρ` at `g`. -/
def repMatrix (g : G) : Matrix (Fin d) (Fin d) ℂ := (ρ g).1

@[simp]
theorem repMatrix_one : repMatrix ρ 1 = 1 := by
  simp [repMatrix]

@[simp]
theorem repMatrix_mul (a b : G) : repMatrix ρ (a * b) = repMatrix ρ a * repMatrix ρ b := by
  simp [repMatrix, map_mul]

theorem repMatrix_mem (g : G) : repMatrix ρ g ∈ Matrix.unitaryGroup (Fin d) ℂ := (ρ g).2

/-- The coercion of the inverse in the unitary group is the star. -/
theorem unitary_coe_inv (u : ↥(Matrix.unitaryGroup (Fin d) ℂ)) : (u⁻¹).1 = star u.1 := by
  have hmul : (u⁻¹).1 * u.1 = 1 := by
    have h : (u⁻¹ * u).1 = (1 : ↥(Matrix.unitaryGroup (Fin d) ℂ)).1 := by
      rw [inv_mul_cancel]
    simpa using h
  have hstar : star u.1 * u.1 = 1 := (Matrix.mem_unitaryGroup_iff').1 u.2
  have hstar2 : u.1 * star u.1 = 1 := (Matrix.mem_unitaryGroup_iff).1 u.2
  calc (u⁻¹).1 = (u⁻¹).1 * (u.1 * star u.1) := by rw [hstar2, mul_one]
    _ = ((u⁻¹).1 * u.1) * star u.1 := by rw [mul_assoc]
    _ = star u.1 := by rw [hmul, one_mul]

/-- The matrix of `ρ` at `g⁻¹` is the star of the matrix at `g`. -/
theorem repMatrix_inv (g : G) : repMatrix ρ g⁻¹ = star (repMatrix ρ g) := by
  have h1 : ρ g⁻¹ = (ρ g)⁻¹ := map_inv ρ g
  rw [repMatrix, h1]
  exact unitary_coe_inv (ρ g)

/-- Trace is invariant under conjugation in the representation. -/
theorem trace_repMatrix_conj (a b : G) :
    Matrix.trace (repMatrix ρ (a * b * a⁻¹)) = Matrix.trace (repMatrix ρ b) := by
  have hstar : star (repMatrix ρ a) * repMatrix ρ a = 1 :=
    (Matrix.mem_unitaryGroup_iff').1 (repMatrix_mem ρ a)
  calc Matrix.trace (repMatrix ρ (a * b * a⁻¹))
      = Matrix.trace (repMatrix ρ a * repMatrix ρ b * star (repMatrix ρ a)) := by
        rw [repMatrix_mul, repMatrix_mul, repMatrix_inv]
    _ = Matrix.trace ((star (repMatrix ρ a) * repMatrix ρ a) * repMatrix ρ b) := by
        rw [Matrix.trace_mul_comm, ← mul_assoc]
    _ = Matrix.trace (repMatrix ρ b) := by rw [hstar, one_mul]

/-- The Wilson density of one plaquette: `1 − (1/d) Re tr ρ(U_p)`. -/
noncomputable def plaquetteDensity (U : Config Λ G) (x : Λ) (μ ν : Fin 4) : ℝ :=
  1 - (Matrix.trace (repMatrix ρ (plaquette σ U x μ ν))).re / (d : ℝ)

/-- The Wilson action `S_β(U) = β * Σ_x Σ_{μ<ν} (1 − (1/d) Re tr ρ(U_p))`,
each unordered plaquette counted once. `β` is a bare real parameter. -/
noncomputable def wilsonAction (β : ℝ) (U : Config Λ G) : ℝ :=
  β * ∑ x : Λ, ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ, plaquetteDensity σ ρ U x μ ν

/-- **Exact gauge invariance of the Wilson action**, for every gauge
transformation `g : Λ → G`. The headline theorem of Stage 0. -/
theorem wilsonAction_gauge_invariant (hσ : ∀ μ ν x, σ μ (σ ν x) = σ ν (σ μ x))
    (g : Λ → G) (β : ℝ) (U : Config Λ G) :
    wilsonAction σ ρ β (gaugeAction σ g U) = wilsonAction σ ρ β U := by
  apply congrArg (β * ·)
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro μ _
  apply Finset.sum_congr rfl
  intro ν _
  unfold plaquetteDensity
  rw [plaquette_gauge σ hσ g U x μ ν, trace_repMatrix_conj]

/-- The density of the trivial configuration vanishes (for `0 < d`):
the Wilson action is normalized so that `S_β(1) = 0`. -/
theorem plaquetteDensity_one (hd : 0 < d) (x : Λ) (μ ν : Fin 4) :
    plaquetteDensity σ ρ (fun _ => 1) x μ ν = 0 := by
  have htr : Matrix.trace (repMatrix ρ (plaquette σ (fun _ => 1) x μ ν)) = (d : ℂ) := by
    rw [plaquette_one, repMatrix_one, Matrix.trace_one, Fintype.card_fin]
  simp [plaquetteDensity, htr, hd.ne']

end Representation

/-! ## §3. The unitary trace bound and action estimates

For a unitary matrix, every entry has norm `≤ 1` (a column is a unit
vector), hence `Re tr A ≤ d`. This is what makes the Wilson density,
and therefore the action at `β ≥ 0`, nonnegative. -/

section TraceBounds

variable {d : ℕ}

/-- Real part of a finite sum is the sum of the real parts. -/
theorem Complex.re_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  classical
  refine s.induction_on (fun a => ?_) ?_ f
  · simp
  · intro s a has ih g
    rw [Finset.sum_insert has, Finset.sum_insert has, Complex.add_re, ih]

/-- Entries of a unitary matrix have norm at most `1`. -/
theorem abs_entry_of_mem_unitaryGroup {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin d) ℂ) (i j : Fin d) : ‖A i j‖ ≤ 1 := by
  have hA' : star A * A = 1 := (Matrix.mem_unitaryGroup_iff').1 hA
  have hentry : (star A * A) j j = (1 : Matrix (Fin d) (Fin d) ℂ) j j := by rw [hA']
  rw [Matrix.mul_apply] at hentry
  simp only [Matrix.star_apply, Matrix.one_apply_eq] at hentry
  -- `hentry : ∑ i, (starRingEnd ℂ) (A i j) * A i j = 1`
  have hsum : ∑ i : Fin d, ‖A i j‖ ^ 2 = 1 := by
    have h := congrArg Complex.re hentry
    rw [Complex.re_sum] at h
    have hterm : ∀ i : Fin d, (star (A i j) * A i j).re = ‖A i j‖ ^ 2 := by
      intro i
      have hcc : star (A i j) = (starRingEnd ℂ) (A i j) := congrFun RCLike.star_def (A i j)
      rw [hcc, RCLike.conj_mul]
      simp only [Complex.coe_algebraMap, ← Complex.ofReal_pow, Complex.ofReal_re]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)] at h
    exact h
  have hle : ‖A i j‖ ^ 2 ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun k _ => sq_nonneg (‖A k j‖)) (Finset.mem_univ i)
  have hnn : (0 : ℝ) ≤ ‖A i j‖ := norm_nonneg _
  nlinarith [hle, hnn]

/-- For unitary `A`, `Re tr A ≤ d`. -/
theorem re_trace_le_of_mem_unitaryGroup {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin d) ℂ) : (Matrix.trace A).re ≤ (d : ℝ) := by
  rw [Matrix.trace]
  rw [Complex.re_sum]
  calc ∑ i : Fin d, (Matrix.diag A i).re
      ≤ ∑ _i : Fin d, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        calc (Matrix.diag A i).re = (A i i).re := rfl
          _ ≤ ‖A i i‖ := Complex.re_le_norm (A i i)
          _ ≤ 1 := abs_entry_of_mem_unitaryGroup hA i i
    _ = (d : ℝ) := by simp

/-- For unitary `A`, `−d ≤ Re tr A`. -/
theorem neg_re_trace_le_of_mem_unitaryGroup {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin d) ℂ) : -(d : ℝ) ≤ (Matrix.trace A).re := by
  rw [Matrix.trace, Complex.re_sum]
  calc -(d : ℝ) = ∑ _i : Fin d, (-1 : ℝ) := by simp
    _ ≤ ∑ i : Fin d, (Matrix.diag A i).re := by
        apply Finset.sum_le_sum
        intro i _
        calc (-1 : ℝ) ≤ -‖A i i‖ := by
              rw [neg_le_neg_iff]
              exact abs_entry_of_mem_unitaryGroup hA i i
          _ ≤ (A i i).re := by
              rw [neg_le]
              calc -(A i i).re = (-A i i).re := by rw [Complex.neg_re]
                _ ≤ ‖-A i i‖ := Complex.re_le_norm _
                _ = ‖A i i‖ := norm_neg _

end TraceBounds

section ActionBounds

variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- Each plaquette density lies in `[0, 2]` (for `0 < d`). -/
theorem plaquetteDensity_mem_Icc (hd : 0 < d) (U : Config Λ G) (x : Λ) (μ ν : Fin 4) :
    plaquetteDensity σ ρ U x μ ν ∈ Set.Icc (0 : ℝ) 2 := by
  have hmem : repMatrix ρ (plaquette σ U x μ ν) ∈ Matrix.unitaryGroup (Fin d) ℂ :=
    repMatrix_mem ρ _
  have h1 := re_trace_le_of_mem_unitaryGroup hmem
  have h2 := neg_re_trace_le_of_mem_unitaryGroup hmem
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · unfold plaquetteDensity
    rw [sub_nonneg, div_le_one hdR]
    exact h1
  · unfold plaquetteDensity
    rw [sub_le_iff_le_add]
    have : (Matrix.trace (repMatrix ρ (plaquette σ U x μ ν))).re / (d : ℝ) ≥ -1 := by
      rw [ge_iff_le, le_div_iff₀ hdR]
      calc (-1 : ℝ) * d = -(d : ℝ) := by ring
        _ ≤ (Matrix.trace (repMatrix ρ (plaquette σ U x μ ν))).re := h2
    linarith

/-- The Wilson action is nonnegative for `β ≥ 0`. -/
theorem wilsonAction_nonneg (hd : 0 < d) (hβ : 0 ≤ β) (U : Config Λ G) :
    0 ≤ wilsonAction σ ρ β U := by
  apply mul_nonneg hβ
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro μ _
  apply Finset.sum_nonneg
  intro ν _
  exact (plaquetteDensity_mem_Icc σ ρ hd U x μ ν).1

/-- A crude bound on the Wilson action: `S_β ≤ β * (2 * (16 * card Λ))`
for `β ≥ 0`. Only finiteness matters (it feeds the Gibbs denominator). -/
theorem wilsonAction_le (hd : 0 < d) (hβ : 0 ≤ β) (U : Config Λ G) :
    wilsonAction σ ρ β U ≤ β * (2 * (16 * (Fintype.card Λ : ℝ))) := by
  apply mul_le_mul_of_nonneg_left _ hβ
  calc ∑ x : Λ, ∑ μ : Fin 4, ∑ ν ∈ Finset.Ioi μ, plaquetteDensity σ ρ U x μ ν
      ≤ ∑ _x : Λ, ∑ μ : Fin 4, ∑ _ν ∈ Finset.Ioi μ, (2 : ℝ) := by
        apply Finset.sum_le_sum; intro x _
        apply Finset.sum_le_sum; intro μ _
        apply Finset.sum_le_sum; intro ν _
        exact (plaquetteDensity_mem_Icc σ ρ hd U x μ ν).2
    _ ≤ ∑ _x : Λ, ∑ μ : Fin 4, ∑ _ν : Fin 4, (2 : ℝ) := by
        apply Finset.sum_le_sum; intro x _
        apply Finset.sum_le_sum; intro μ _
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => by norm_num)
    _ = 2 * (16 * (Fintype.card Λ : ℝ)) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring

end ActionBounds

/-! ## §4. Wilson loops: closed lattice paths

A path is a list of directed steps. A forward step in direction `μ`
traverses the link `(s, μ)` from its base site `s`; a backward step
traverses the link `((σ μ)⁻¹ s, μ)` against its orientation and
contributes its inverse. Both orientations transform under a gauge
transformation by the same conjugation pattern, which is what makes
closed-loop traces gauge invariant. -/

/-- One directed step of a lattice path. -/
inductive Step where
  /-- Traverse a link along its orientation. -/
  | fwd (dir : Fin 4)
  /-- Traverse a link against its orientation. -/
  | bwd (dir : Fin 4)
  deriving DecidableEq

/-- The site a step starting at `s` ends at. -/
def stepSite : Λ → Step → Λ
  | s, Step.fwd μ => σ μ s
  | s, Step.bwd μ => (σ μ).symm s

/-- The group element a step contributes, starting at site `s`. -/
def stepFactor (U : Config Λ G) : Λ → Step → G
  | s, Step.fwd μ => U (s, μ)
  | s, Step.bwd μ => (U ((σ μ).symm s, μ))⁻¹

/-- The end site of a path starting at `s`. -/
def loopEnd : Λ → List Step → Λ
  | s, [] => s
  | s, st :: t => loopEnd (stepSite σ s st) t

/-- The ordered product of step factors along a path starting at `s`. -/
def loopProd (U : Config Λ G) : Λ → List Step → G
  | _, [] => 1
  | s, st :: t => stepFactor σ U s st * loopProd U (stepSite σ s st) t

@[simp] theorem loopEnd_nil (s : Λ) : loopEnd σ s [] = s := rfl

@[simp] theorem loopEnd_cons (s : Λ) (st : Step) (t : List Step) :
    loopEnd σ s (st :: t) = loopEnd σ (stepSite σ s st) t := rfl

@[simp] theorem loopProd_nil (U : Config Λ G) (s : Λ) :
    loopProd σ U s [] = 1 := rfl

@[simp] theorem loopProd_cons (U : Config Λ G) (s : Λ) (st : Step)
    (t : List Step) :
    loopProd σ U s (st :: t)
      = stepFactor σ U s st * loopProd σ U (stepSite σ s st) t := rfl

/-- Each step factor conjugates by the gauge elements at its two end
sites — the uniform pattern for both orientations. -/
theorem stepFactor_gauge (g : Λ → G) (U : Config Λ G) (s : Λ) (st : Step) :
    stepFactor σ (gaugeAction σ g U) s st
      = g s * stepFactor σ U s st * (g (stepSite σ s st))⁻¹ := by
  cases st with
  | fwd μ => simp [stepFactor, stepSite, gaugeAction_apply]
  | bwd μ =>
    simp only [stepFactor, stepSite, gaugeAction_apply, mul_inv_rev, inv_inv,
      Equiv.apply_symm_apply]
    group

/-- The ordered product along any path conjugates by the gauge elements
at the path's two ends. -/
theorem loopProd_gauge (g : Λ → G) (U : Config Λ G) :
    ∀ (s : Λ) (steps : List Step),
      loopProd σ (gaugeAction σ g U) s steps
        = g s * loopProd σ U s steps * (g (loopEnd σ s steps))⁻¹ := by
  intro s steps
  induction steps generalizing s with
  | nil => simp
  | cons st t ih =>
    rw [loopProd_cons, loopProd_cons, loopEnd_cons, ih, stepFactor_gauge]
    group

section RepresentationLoops

variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The Wilson loop of a path: the trace of the represented ordered
product along the path. -/
noncomputable def wilsonLoop (U : Config Λ G) (s : Λ) (steps : List Step) : ℂ :=
  Matrix.trace (repMatrix ρ (loopProd σ U s steps))

/-- **Wilson loop gauge invariance**: for a *closed* path (end site =
start site), the Wilson loop is exactly gauge invariant. -/
theorem wilsonLoop_gauge_invariant (g : Λ → G) (U : Config Λ G) (s : Λ)
    (steps : List Step) (hclosed : loopEnd σ s steps = s) :
    wilsonLoop σ ρ (gaugeAction σ g U) s steps = wilsonLoop σ ρ U s steps := by
  unfold wilsonLoop
  rw [loopProd_gauge, hclosed, trace_repMatrix_conj]

/-- The four steps around one plaquette, in the convention of
`plaquette`: forward `μ`, forward `ν`, backward `μ`, backward `ν`. -/
def plaquetteSteps (μ ν : Fin 4) : List Step :=
  [Step.fwd μ, Step.fwd ν, Step.bwd μ, Step.bwd ν]

/-- The plaquette path is closed, using commutativity of the shifts. -/
theorem loopEnd_plaquetteSteps
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (x : Λ) (μ ν : Fin 4) :
    loopEnd σ x (plaquetteSteps μ ν) = x := by
  have h1 : (σ μ).symm (σ ν (σ μ x)) = σ ν x := by
    rw [← hσ μ ν x]
    exact Equiv.symm_apply_apply (σ μ) (σ ν x)
  simp only [plaquetteSteps, loopEnd_cons, loopEnd_nil, stepSite, h1,
    Equiv.symm_apply_apply]

/-- The plaquette *is* the loop product of its four steps. -/
theorem loopProd_plaquetteSteps
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (U : Config Λ G) (x : Λ) (μ ν : Fin 4) :
    loopProd σ U x (plaquetteSteps μ ν) = plaquette σ U x μ ν := by
  have h1 : (σ μ).symm (σ ν (σ μ x)) = σ ν x := by
    rw [← hσ μ ν x]
    exact Equiv.symm_apply_apply (σ μ) (σ ν x)
  simp only [plaquetteSteps, loopProd_cons, loopProd_nil, stepFactor,
    stepSite, h1, Equiv.symm_apply_apply, plaquette, mul_one, ← mul_assoc]

end RepresentationLoops

end Algebra

/-! ## §5. The configuration measure and its exact invariance

`haarProb G` is the normalized Haar probability measure on a compact
group, built from Mathlib's Haar measure by scaling by the inverse of
the total mass. Right- and inversion-invariance are *proved* for it
here: Mathlib's stock instance covers only the abelian case, so the
general compact case goes through uniqueness of normalized Haar
measures (the image of a Haar measure under right translation or
inversion is again a Haar probability measure, hence equal). -/

section HaarProb

open MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [CompactSpace G] [LocallyCompactSpace G]

/-- The total mass of Mathlib's Haar measure on a compact group is
finite (compactness) and positive (Haar measures charge open sets). -/
theorem haar_univ_ne_top : (Measure.haar : Measure G) Set.univ ≠ ∞ :=
  (isCompact_univ.measure_lt_top (μ := (Measure.haar : Measure G))).ne

theorem haar_univ_ne_zero : (Measure.haar : Measure G) Set.univ ≠ 0 :=
  Measure.IsOpenPosMeasure.open_pos Set.univ isOpen_univ Set.univ_nonempty

/-- A normalized Haar probability measure on a compact group:
Mathlib's Haar measure scaled to total mass `1`. -/
noncomputable def haarProb (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [CompactSpace G] [LocallyCompactSpace G] : Measure G :=
  ((Measure.haar : Measure G) Set.univ)⁻¹ • (Measure.haar : Measure G)

instance : IsProbabilityMeasure (haarProb G) := by
  refine ⟨?_⟩
  rw [haarProb, Measure.smul_apply, smul_eq_mul,
    ENNReal.inv_mul_cancel haar_univ_ne_zero haar_univ_ne_top]

instance : Measure.IsHaarMeasure (haarProb G) :=
  Measure.IsHaarMeasure.smul _
    (ENNReal.inv_ne_zero.mpr haar_univ_ne_top)
    (ENNReal.inv_ne_top.mpr haar_univ_ne_zero)

/-- The normalized Haar probability measure on a compact group is
invariant under right translation — proved via uniqueness of
normalized Haar measures, since the stock instance covers only
abelian groups. -/
instance : Measure.IsMulRightInvariant (haarProb G) := by
  refine ⟨fun c => ?_⟩
  haveI : IsProbabilityMeasure ((haarProb G).map (· * c)) := by
    refine ⟨?_⟩
    rw [Measure.map_apply (measurable_mul_const c) MeasurableSet.univ,
      Set.preimage_univ, measure_univ]
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- The normalized Haar probability measure on a compact group is
invariant under inversion — same uniqueness argument. -/
instance : Measure.IsInvInvariant (haarProb G) := by
  refine ⟨?_⟩
  show (haarProb G).map Inv.inv = haarProb G
  haveI : IsProbabilityMeasure ((haarProb G).map Inv.inv) := by
    refine ⟨?_⟩
    rw [Measure.map_apply measurable_inv MeasurableSet.univ,
      Set.preimage_univ, measure_univ]
  -- The inversion pushforward of a Haar probability measure is again a
  -- Haar probability measure: left translations conjugate through
  -- inversion to right translations, where invariance is already known.
  have hfin : IsFiniteMeasureOnCompacts ((haarProb G).map Inv.inv) :=
    ⟨fun K _hK => lt_of_le_of_lt (measure_mono (Set.subset_univ K)) (by
      rw [measure_univ]; exact ENNReal.one_lt_top)⟩
  have hleft : Measure.IsMulLeftInvariant ((haarProb G).map Inv.inv) :=
    ⟨fun a => by
      have e : (a * ·) ∘ Inv.inv = Inv.inv ∘ (· * a⁻¹) := by
        funext x
        simp only [Function.comp_apply, mul_inv_rev, inv_inv]
      rw [Measure.map_map (measurable_const_mul a) measurable_inv, e,
        ← Measure.map_map measurable_inv (measurable_mul_const a⁻¹),
        map_mul_right_eq_self]⟩
  have hopen : Measure.IsOpenPosMeasure ((haarProb G).map Inv.inv) :=
    ⟨fun U hU hne => by
      rw [Measure.map_apply measurable_inv hU.measurableSet]
      obtain ⟨x, hx⟩ := hne
      exact Measure.IsOpenPosMeasure.open_pos _
        (hU.preimage continuous_inv) ⟨x⁻¹, by simpa using hx⟩⟩
  haveI : Measure.IsHaarMeasure ((haarProb G).map Inv.inv) :=
    { toIsFiniteMeasureOnCompacts := hfin, toIsMulLeftInvariant := hleft,
      toIsOpenPosMeasure := hopen }
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

end HaarProb

/-! ### The product measure over links -/

section ConfigMeasure

open MeasureTheory

variable {Λ : Type*} [Fintype Λ] {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]

/-- The configuration measure: the product of `μG` over all links. -/
noncomputable def configMeasure : Measure (Config Λ G) :=
  Measure.pi (fun _ : Link Λ => μG)

instance : IsProbabilityMeasure (configMeasure μG : Measure (Config Λ G)) := by
  unfold configMeasure
  infer_instance

/-- Two-sided translation `a ↦ c * a * d` preserves any measure that
is invariant under left and right translations separately. -/
theorem measurePreserving_mul_mul (c d : G) :
    MeasurePreserving (fun a => c * a * d) μG μG := by
  refine ⟨((measurable_id.const_mul c).mul_const d), ?_⟩
  have e : (fun a => c * a * d) = (c * ·) ∘ (· * d) := by
    funext a
    simp [mul_assoc]
  rw [e, ← Measure.map_map (measurable_const_mul c)
    (measurable_mul_const d), map_mul_left_eq_self, map_mul_right_eq_self]

/-- The gauge action, as a coordinatewise map: at each link it is the
two-sided translation by the gauge elements at the link's ends. -/
theorem gaugeAction_eq (σ : Fin 4 → Equiv.Perm Λ) (g : Λ → G) :
    gaugeAction σ g
      = fun U ℓ => g ℓ.1 * U ℓ * (g (σ ℓ.2 ℓ.1))⁻¹ := by
  funext U ℓ
  obtain ⟨x, μ⟩ := ℓ
  rfl

/-- The gauge action on configurations is measurable: each link
coordinate is a product of an evaluation with constants. -/
theorem measurable_gaugeAction (σ : Fin 4 → Equiv.Perm Λ) (g : Λ → G) :
    Measurable (gaugeAction σ g) := by
  rw [gaugeAction_eq]
  exact measurable_pi_iff.mpr fun ℓ =>
    ((measurable_pi_apply ℓ).const_mul _).mul_const _

/-- **Measure invariance under the gauge action**: the pushforward of
the product Haar measure along any gauge action is itself. The gauge
action is a coordinatewise product of two-sided translations, and the
product measure is preserved factor by factor. -/
theorem configMeasure_map_gaugeAction (σ : Fin 4 → Equiv.Perm Λ) (g : Λ → G) :
    Measure.map (gaugeAction σ g) (configMeasure μG) = configMeasure μG := by
  have hmp := measurePreserving_pi (fun _ : Link Λ => μG)
    (fun _ : Link Λ => μG)
    (fun ℓ => measurePreserving_mul_mul μG (g ℓ.1) (g (σ ℓ.2 ℓ.1))⁻¹)
  rw [gaugeAction_eq]
  exact hmp.map_eq

/-- **Integral invariance under the gauge action** (the form consumed
by the β = 0 analysis): integrating a gauge-transformed observable
against the product Haar measure is the same as integrating the
observable itself. -/
theorem integral_gaugeAction {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (σ : Fin 4 → Equiv.Perm Λ) (g : Λ → G)
    (F : Config Λ G → E) (hF : AEStronglyMeasurable F (configMeasure μG)) :
    ∫ U, F (gaugeAction σ g U) ∂(configMeasure μG)
      = ∫ U, F U ∂(configMeasure μG) := by
  have hF' : AEStronglyMeasurable F
      (Measure.map (gaugeAction σ g) (configMeasure μG)) := by
    rw [configMeasure_map_gaugeAction μG σ g]
    exact hF
  conv_rhs => rw [← configMeasure_map_gaugeAction μG σ g]
  exact (integral_map (measurable_gaugeAction σ g).aemeasurable hF').symm

end ConfigMeasure

/-! ## §6. Gibbs expectations

The Gibbs expectation of an observable `F` at parameter `β` is *defined*
as the ratio of integrals against the product Haar measure,
`⟨F⟩_β = (∫ e^{−S_β} F dU) / (∫ e^{−S_β} dU)`. This is the standard
density formulation; no separate Gibbs measure object is constructed.
The denominator is positive for `β ≥ 0` (proved below), so the ratio
is a genuine normalization in that range. -/

section Gibbs

open MeasureTheory

variable {Λ : Type*} [Fintype Λ] {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ)
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The plaquette map is measurable (product of evaluations and
inverses), for any measurable group structure on `G`. -/
theorem measurable_plaquette (x : Λ) (μ ν : Fin 4) :
    Measurable fun U : Config Λ G => plaquette σ U x μ ν :=
  (((measurable_pi_apply (x, μ)).mul (measurable_pi_apply (σ μ x, ν))).mul
    (measurable_pi_apply (σ ν x, μ)).inv).mul
    (measurable_pi_apply (x, ν)).inv

/-- Entries of represented plaquettes are measurable. -/
theorem measurable_repMatrix_plaquette_entry
    (hρcont : Continuous fun g : G => repMatrix ρ g) (x : Λ) (μ ν : Fin 4)
    (a b : Fin d) :
    Measurable fun U : Config Λ G =>
      repMatrix ρ (plaquette σ U x μ ν) a b :=
  (measurable_pi_apply b).comp ((measurable_pi_apply a).comp
    (hρcont.measurable.comp (measurable_plaquette σ x μ ν)))

/-- The Wilson action is measurable. -/
theorem measurable_wilsonAction
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) :
    Measurable (wilsonAction σ ρ β) := by
  have htr : ∀ x : Λ, ∀ μ ν : Fin 4, Measurable fun U : Config Λ G =>
      (Matrix.trace (repMatrix ρ (plaquette σ U x μ ν))).re := by
    intro x μ ν
    refine Complex.measurable_re.comp ?_
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (measurable_pi_apply i).comp ((measurable_pi_apply i).comp
      (hρcont.measurable.comp (measurable_plaquette σ x μ ν)))
  unfold wilsonAction
  refine Measurable.const_mul ?_ β
  refine Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun μ _ =>
    Finset.measurable_sum _ fun ν _ => ?_
  exact measurable_const.sub ((htr x μ ν).div_const _)

/-- Two-sided bound on the Wilson action, for the Gibbs weight. -/
theorem wilsonAction_abs_le (hd : 0 < d) (β : ℝ) (U : Config Λ G) :
    |wilsonAction σ ρ β U| ≤ |β| * (2 * (16 * (Fintype.card Λ : ℝ))) := by
  by_cases hβ : 0 ≤ β
  · rw [abs_of_nonneg (wilsonAction_nonneg σ ρ hd hβ U), abs_of_nonneg hβ]
    exact wilsonAction_le σ ρ hd hβ U
  · have hβneg : β < 0 := lt_of_not_ge hβ
    have hβ' : 0 ≤ -β := le_of_lt (neg_pos.mpr hβneg)
    have hneg : wilsonAction σ ρ (-β) U = - wilsonAction σ ρ β U := by
      simp [wilsonAction, neg_mul]
    rw [← abs_neg (wilsonAction σ ρ β U), ← hneg,
      abs_of_nonneg (wilsonAction_nonneg σ ρ hd hβ' U), abs_of_neg hβneg]
    exact wilsonAction_le σ ρ hd hβ' U

/-- The Gibbs weight `U ↦ e^{−S_β(U)}` is integrable against the
configuration measure, for every `β`. -/
theorem integrable_exp_neg_wilsonAction
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d) (β : ℝ) :
    Integrable (fun U => Real.exp (- wilsonAction σ ρ β U))
      (configMeasure μG) := by
  have hm : Measurable (fun U => Real.exp (- wilsonAction σ ρ β U)) :=
    Real.measurable_exp.comp (measurable_wilsonAction σ ρ hρcont β).neg
  refine Integrable.of_bound hm.aestronglyMeasurable
    (Real.exp (|β| * (2 * (16 * (Fintype.card Λ : ℝ))))) ?_
  filter_upwards with U
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr
    ((neg_le_abs _).trans (wilsonAction_abs_le σ ρ hd β U))

/-- The Gibbs partition integral is positive for `β ≥ 0`: the weight
is bounded below by a positive constant on the whole configuration
space. -/
theorem gibbsDenom_pos
    (hρcont : Continuous fun g : G => repMatrix ρ g) (hd : 0 < d)
    (hβ : 0 ≤ β) :
    0 < ∫ U, Real.exp (- wilsonAction σ ρ β U) ∂(configMeasure μG) := by
  have hmono : (∫ _U : Config Λ G,
        Real.exp (-(β * (2 * (16 * (Fintype.card Λ : ℝ)))))
        ∂(configMeasure μG))
      ≤ ∫ U, Real.exp (- wilsonAction σ ρ β U) ∂(configMeasure μG) := by
    refine integral_mono_ae (integrable_const _)
      (integrable_exp_neg_wilsonAction σ μG ρ hρcont hd β) ?_
    filter_upwards with U
    exact Real.exp_le_exp.mpr (neg_le_neg (wilsonAction_le σ ρ hd hβ U))
  rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    one_smul] at hmono
  exact (Real.exp_pos _).trans_le hmono

/-- The Gibbs expectation of a complex observable at parameter `β`:
the ratio of the weighted integral to the partition integral. `β` is
a bare parameter. -/
noncomputable def gibbsExpect (β : ℝ) (F : Config Λ G → ℂ) : ℂ :=
  (∫ U, Real.exp (- wilsonAction σ ρ β U) * F U ∂(configMeasure μG)) /
    ((∫ U, Real.exp (- wilsonAction σ ρ β U) ∂(configMeasure μG) : ℝ) : ℂ)

/-- At `β = 0` the Gibbs expectation is the plain product-Haar
expectation: the weight is identically `1` and the partition integral
is `1`. -/
theorem gibbsExpect_zero (F : Config Λ G → ℂ) :
    gibbsExpect σ μG ρ 0 F = ∫ U, F U ∂(configMeasure μG) := by
  have hS : ∀ U : Config Λ G, wilsonAction σ ρ 0 U = 0 := fun U => by
    simp [wilsonAction]
  unfold gibbsExpect
  simp [hS, integral_const]

/-- The Gibbs expectation of a Wilson loop. -/
noncomputable def wilsonLoopExpectation (β : ℝ) (s : Λ) (steps : List Step) :
    ℂ :=
  gibbsExpect σ μG ρ β (fun U => wilsonLoop σ ρ U s steps)

end Gibbs

/-! ## §7. The β = 0 package: Haar orthogonality via the intertwiner

The Haar average `P = ∫ ρ(g) dμ(g)` of a unitary representation is the
projection onto the `ρ`-fixed vectors: it intertwines (`ρ(h) P = P`
and `P ρ(h) = P`), it is idempotent, its range consists of fixed
vectors, and it vanishes when `ρ` has no nonzero fixed vectors. Since
the configuration measure is a product over links, the expectation of
a single link is `P`, and the expectation of a plaquette — a product
over four *distinct* links — factorizes into a product of four copies
of `P`, whose trace collapses by idempotence. This is Haar
orthogonality in projection form, for a general compact group and a
general unitary representation. -/

section BetaZero

open MeasureTheory

variable {Λ : Type*} [Fintype Λ] {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ)
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- Entries of the represented group elements are integrable against
any Haar probability measure (they are continuous and bounded by `1`
in norm, by unitarity). -/
theorem integrable_repMatrix_entry
    (hρcont : Continuous fun g : G => repMatrix ρ g) (i j : Fin d) :
    Integrable (fun g => repMatrix ρ g i j) μG :=
  Integrable.of_bound
    (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      hρcont.measurable)).aestronglyMeasurable) 1
    (Filter.Eventually.of_forall fun g =>
      abs_entry_of_mem_unitaryGroup (repMatrix_mem ρ g) i j)

/-- The Haar intertwiner: the average of the representation over the
group, defined entrywise (the Bochner integral of a matrix-valued
function is its entrywise integral). It is the projection onto the
`ρ`-fixed vectors. -/
noncomputable def haarIntertwiner : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => ∫ g, repMatrix ρ g i j ∂μG

/-- Entries of the intertwiner are single-group-element integrals. -/
theorem haarIntertwiner_apply
    (hρcont : Continuous fun g : G => repMatrix ρ g) (i j : Fin d) :
    haarIntertwiner μG ρ i j = ∫ g, repMatrix ρ g i j ∂μG := rfl

/-- Left intertwining: `ρ(h) P = P`. The average is invariant under
left translation of the integration variable. -/
theorem repMatrix_mul_haarIntertwiner
    (hρcont : Continuous fun g : G => repMatrix ρ g) (h : G) :
    repMatrix ρ h * haarIntertwiner μG ρ = haarIntertwiner μG ρ := by
  ext i j
  rw [Matrix.mul_apply, haarIntertwiner_apply μG ρ hρcont]
  calc ∑ k, repMatrix ρ h i k * (∫ g, repMatrix ρ g k j ∂μG)
      = ∑ k, ∫ g, repMatrix ρ h i k * repMatrix ρ g k j ∂μG :=
        Finset.sum_congr rfl fun k _ => (integral_const_mul _ _).symm
    _ = ∫ g, ∑ k, repMatrix ρ h i k * repMatrix ρ g k j ∂μG :=
        (integral_finsetSum _ fun k _ =>
          (integrable_repMatrix_entry μG ρ hρcont k j).const_mul _).symm
    _ = ∫ g, repMatrix ρ (h * g) i j ∂μG :=
        integral_congr_ae (Filter.Eventually.of_forall fun g => by
          show (∑ k, repMatrix ρ h i k * repMatrix ρ g k j)
            = repMatrix ρ (h * g) i j
          rw [← Matrix.mul_apply, ← repMatrix_mul])
    _ = ∫ g, repMatrix ρ g i j ∂μG :=
        integral_mul_left_eq_self (fun x => repMatrix ρ x i j) h

/-- Right intertwining: `P ρ(h) = P`. -/
theorem haarIntertwiner_mul_repMatrix
    (hρcont : Continuous fun g : G => repMatrix ρ g) (h : G) :
    haarIntertwiner μG ρ * repMatrix ρ h = haarIntertwiner μG ρ := by
  ext i j
  rw [Matrix.mul_apply, haarIntertwiner_apply μG ρ hρcont]
  calc ∑ k, (∫ g, repMatrix ρ g i k ∂μG) * repMatrix ρ h k j
      = ∑ k, ∫ g, repMatrix ρ g i k * repMatrix ρ h k j ∂μG :=
        Finset.sum_congr rfl fun k _ => (integral_mul_const _ _).symm
    _ = ∫ g, ∑ k, repMatrix ρ g i k * repMatrix ρ h k j ∂μG :=
        (integral_finsetSum _ fun k _ =>
          (integrable_repMatrix_entry μG ρ hρcont i k).mul_const _).symm
    _ = ∫ g, repMatrix ρ (g * h) i j ∂μG :=
        integral_congr_ae (Filter.Eventually.of_forall fun g => by
          show (∑ k, repMatrix ρ g i k * repMatrix ρ h k j)
            = repMatrix ρ (g * h) i j
          rw [← Matrix.mul_apply, ← repMatrix_mul])
    _ = ∫ g, repMatrix ρ g i j ∂μG :=
        integral_mul_right_eq_self (fun x => repMatrix ρ x i j) h

/-- Idempotence: `P * P = P`. -/
theorem haarIntertwiner_idempotent
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    haarIntertwiner μG ρ * haarIntertwiner μG ρ = haarIntertwiner μG ρ := by
  ext i j
  rw [Matrix.mul_apply, haarIntertwiner_apply μG ρ hρcont]
  calc ∑ k, haarIntertwiner μG ρ i k * (∫ g, repMatrix ρ g k j ∂μG)
      = ∑ k, ∫ g, haarIntertwiner μG ρ i k * repMatrix ρ g k j ∂μG :=
        Finset.sum_congr rfl fun k _ => (integral_const_mul _ _).symm
    _ = ∫ g, ∑ k, haarIntertwiner μG ρ i k * repMatrix ρ g k j ∂μG :=
        (integral_finsetSum _ fun k _ =>
          (integrable_repMatrix_entry μG ρ hρcont k j).const_mul _).symm
    _ = ∫ g, haarIntertwiner μG ρ i j ∂μG :=
        integral_congr_ae (Filter.Eventually.of_forall fun g => by
          show (∑ k, haarIntertwiner μG ρ i k * repMatrix ρ g k j)
            = haarIntertwiner μG ρ i j
          rw [← Matrix.mul_apply, haarIntertwiner_mul_repMatrix μG ρ hρcont])
    _ = ∫ g, repMatrix ρ g i j ∂μG := by
        rw [← haarIntertwiner_apply μG ρ hρcont]
        simp [integral_const]

/-- Every vector in the range of `P` is `ρ`-fixed. -/
theorem repMatrix_mulVec_haarIntertwiner
    (hρcont : Continuous fun g : G => repMatrix ρ g) (v : Fin d → ℂ)
    (g : G) :
    repMatrix ρ g *ᵥ (haarIntertwiner μG ρ *ᵥ v) = haarIntertwiner μG ρ *ᵥ v := by
  rw [Matrix.mulVec_mulVec, repMatrix_mul_haarIntertwiner μG ρ hρcont]

/-- `P` acts as the identity on `ρ`-fixed vectors. -/
theorem haarIntertwiner_mulVec_of_fixed
    (hρcont : Continuous fun g : G => repMatrix ρ g) (v : Fin d → ℂ)
    (hv : ∀ g : G, repMatrix ρ g *ᵥ v = v) :
    haarIntertwiner μG ρ *ᵥ v = v := by
  funext i
  calc (haarIntertwiner μG ρ *ᵥ v) i
      = ∑ j, ∫ g, repMatrix ρ g i j * v j ∂μG := by
        rw [show (haarIntertwiner μG ρ *ᵥ v) i
            = ∑ j, haarIntertwiner μG ρ i j * v j from rfl]
        exact Finset.sum_congr rfl fun j _ => by
          rw [haarIntertwiner_apply μG ρ hρcont, integral_mul_const]
    _ = ∫ g, ∑ j, repMatrix ρ g i j * v j ∂μG :=
        (integral_finsetSum _ fun j _ =>
          (integrable_repMatrix_entry μG ρ hρcont i j).mul_const _).symm
    _ = ∫ g, v i ∂μG :=
        integral_congr_ae (Filter.Eventually.of_forall fun g =>
          congrFun (hv g) i)
    _ = v i := by simp [integral_const]

/-- If `ρ` has no nonzero fixed vectors, the intertwiner vanishes. -/
theorem haarIntertwiner_eq_zero_of_no_fixed
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (h : ∀ v : Fin d → ℂ, (∀ g : G, repMatrix ρ g *ᵥ v = v) → v = 0) :
    haarIntertwiner μG ρ = 0 := by
  ext i j
  have hz := h (haarIntertwiner μG ρ *ᵥ Pi.single j (1 : ℂ))
    (fun g => repMatrix_mulVec_haarIntertwiner μG ρ hρcont _ g)
  have hi := congrFun hz i
  have hsum : (haarIntertwiner μG ρ *ᵥ Pi.single j (1 : ℂ)) i
      = haarIntertwiner μG ρ i j := by
    have h := congrFun (Matrix.mulVec_single_one (haarIntertwiner μG ρ) j) i
    rwa [Matrix.col_apply] at h
  rw [hsum] at hi
  simpa using hi

/-- Measurability of a single link's represented entries. -/
theorem measurable_repMatrix_link_entry
    (hρcont : Continuous fun g : G => repMatrix ρ g) (ℓ : Link Λ)
    (a b : Fin d) :
    Measurable fun U : Config Λ G => repMatrix ρ (U ℓ) a b :=
  (measurable_pi_apply b).comp ((measurable_pi_apply a).comp
    (hρcont.measurable.comp (measurable_pi_apply ℓ)))

/-- Measurability of a single inverted link's represented entries. -/
theorem measurable_repMatrix_link_entry_inv
    (hρcont : Continuous fun g : G => repMatrix ρ g) (ℓ : Link Λ)
    (a b : Fin d) :
    Measurable fun U : Config Λ G => repMatrix ρ ((U ℓ)⁻¹) a b :=
  (measurable_pi_apply b).comp ((measurable_pi_apply a).comp
    (hρcont.measurable.comp (measurable_pi_apply ℓ).inv))

/-- Integrability of a single link's represented entries over the
configuration space. -/
theorem integrable_repMatrix_link_entry
    (hρcont : Continuous fun g : G => repMatrix ρ g) (ℓ : Link Λ)
    (a b : Fin d) :
    Integrable (fun U : Config Λ G => repMatrix ρ (U ℓ) a b)
      (configMeasure μG) :=
  Integrable.of_bound
    (measurable_repMatrix_link_entry ρ hρcont ℓ a b).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun U =>
      abs_entry_of_mem_unitaryGroup (repMatrix_mem ρ (U ℓ)) a b)

/-- **Single-link expectation at β = 0**: the product-Haar expectation
of one link's represented entry is the intertwiner entry. The other
links integrate to `1` (Fubini over the finite product). -/
theorem integral_repMatrix_link
    (hρcont : Continuous fun g : G => repMatrix ρ g) (ℓ : Link Λ)
    (i j : Fin d) :
    ∫ U, repMatrix ρ (U ℓ) i j ∂(configMeasure μG)
      = haarIntertwiner μG ρ i j := by
  classical
  rw [haarIntertwiner_apply μG ρ hρcont i j]
  have h1 : (∫ U, repMatrix ρ (U ℓ) i j ∂(configMeasure μG))
      = ∫ U, ∏ ℓ' : Link Λ, (if ℓ' = ℓ then repMatrix ρ (U ℓ') i j else 1)
          ∂(configMeasure μG) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    show repMatrix ρ (U ℓ) i j
      = ∏ ℓ' : Link Λ, (if ℓ' = ℓ then repMatrix ρ (U ℓ') i j else 1)
    rw [Finset.prod_eq_single ℓ (fun b _ hb => if_neg hb)
      (fun h => absurd (Finset.mem_univ ℓ) h)]
    exact (if_pos rfl).symm
  rw [h1]
  calc (∫ U, ∏ ℓ' : Link Λ, (if ℓ' = ℓ then repMatrix ρ (U ℓ') i j else 1)
        ∂(configMeasure μG))
      = ∏ ℓ' : Link Λ, ∫ a, (if ℓ' = ℓ then repMatrix ρ a i j else 1) ∂μG := by
        unfold configMeasure
        exact integral_fintype_prod_eq_prod
          (fun ℓ' a => if ℓ' = ℓ then repMatrix ρ a i j else 1)
    _ = ∫ a, repMatrix ρ a i j ∂μG := by
        rw [Finset.prod_eq_single ℓ
          (fun b _ hb => by simp only [if_neg hb]; simp [integral_const])
          (fun h => absurd (Finset.mem_univ ℓ) h)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun _ => if_pos rfl)

/-- The trace version: the β = 0 expectation of a single link's trace
is the trace of the intertwiner. -/
theorem integral_trace_repMatrix_link
    (hρcont : Continuous fun g : G => repMatrix ρ g) (ℓ : Link Λ) :
    ∫ U, Matrix.trace (repMatrix ρ (U ℓ)) ∂(configMeasure μG)
      = Matrix.trace (haarIntertwiner μG ρ) := by
  calc (∫ U, Matrix.trace (repMatrix ρ (U ℓ)) ∂(configMeasure μG))
      = ∑ i, ∫ U, repMatrix ρ (U ℓ) i i ∂(configMeasure μG) :=
        integral_finsetSum _ fun i _ =>
          integrable_repMatrix_link_entry μG ρ hρcont ℓ i i
    _ = ∑ i, haarIntertwiner μG ρ i i :=
        Finset.sum_congr rfl fun i _ =>
          integral_repMatrix_link μG ρ hρcont ℓ i i
    _ = Matrix.trace (haarIntertwiner μG ρ) := rfl

/-- A product over all indices collapses to four distinct factors when
the function is `1` off those four indices. -/
theorem prod_four {ι : Type*} [Fintype ι] {F : ι → ℂ} {a b c d : ι}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d)
    (hF : ∀ ℓ, ℓ ≠ a → ℓ ≠ b → ℓ ≠ c → ℓ ≠ d → F ℓ = 1) :
    ∏ ℓ, F ℓ = F a * (F b * (F c * F d)) := by
  classical
  rw [← Finset.prod_subset (Finset.subset_univ ({a, b, c, d} : Finset ι))
      (fun ℓ' _ hℓ' => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hℓ'
        exact hF ℓ' hℓ'.1 hℓ'.2.1 hℓ'.2.2.1 hℓ'.2.2.2),
    Finset.prod_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, hac, had⟩),
    Finset.prod_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hbc, hbd⟩),
    Finset.prod_insert (by simp only [Finset.mem_singleton]; exact hcd),
    Finset.prod_singleton]

open Classical in
/-- The four-link factor family of a plaquette: at the plaquette's
four links it returns the corresponding represented factor (with
inversion at the third and fourth links); elsewhere it returns `1`,
so that a product over all links is the plaquette's entry product. -/
noncomputable def plaquetteFactor (i0 i1 i2 i3 : Fin d)
    (ℓ1 ℓ2 ℓ3 ℓ4 ℓ' : Link Λ) (a : G) : ℂ :=
  if ℓ' = ℓ1 then repMatrix ρ a i0 i1
  else if ℓ' = ℓ2 then repMatrix ρ a i1 i2
  else if ℓ' = ℓ3 then repMatrix ρ (a⁻¹) i2 i3
  else if ℓ' = ℓ4 then repMatrix ρ (a⁻¹) i3 i0
  else 1

/-- **Plaquette factorization at β = 0**: the product-Haar expectation
of a plaquette entry — a product over four *distinct* links — is the
corresponding entry product of four intertwiners. Only the fixed-point
conditions `σ μ x ≠ x`, `σ ν x ≠ x` and `μ ≠ ν` are needed (they make
the four links pairwise distinct); shift commutation is not. -/
theorem integral_plaquette_entry
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (x : Λ) {μ ν : Fin 4} (hμν : μ ≠ ν)
    (hμx : σ μ x ≠ x) (hνx : σ ν x ≠ x)
    (i0 i1 i2 i3 : Fin d) :
    ∫ U, repMatrix ρ (U (x, μ)) i0 i1 * (repMatrix ρ (U (σ μ x, ν)) i1 i2 *
        (repMatrix ρ ((U (σ ν x, μ))⁻¹) i2 i3 *
          repMatrix ρ ((U (x, ν))⁻¹) i3 i0)) ∂(configMeasure μG)
      = haarIntertwiner μG ρ i0 i1 * (haarIntertwiner μG ρ i1 i2 *
          (haarIntertwiner μG ρ i2 i3 * haarIntertwiner μG ρ i3 i0)) := by
  classical
  set ℓ1 : Link Λ := (x, μ) with hℓ1
  set ℓ2 : Link Λ := (σ μ x, ν) with hℓ2
  set ℓ3 : Link Λ := (σ ν x, μ) with hℓ3
  set ℓ4 : Link Λ := (x, ν) with hℓ4
  have n12 : ℓ1 ≠ ℓ2 := fun h => hμν (Prod.ext_iff.mp h).2
  have n13 : ℓ1 ≠ ℓ3 := fun h => absurd (Prod.ext_iff.mp h).1 (Ne.symm hνx)
  have n14 : ℓ1 ≠ ℓ4 := fun h => hμν (Prod.ext_iff.mp h).2
  have n23 : ℓ2 ≠ ℓ3 := fun h => (Ne.symm hμν) (Prod.ext_iff.mp h).2
  have n24 : ℓ2 ≠ ℓ4 := fun h => absurd (Prod.ext_iff.mp h).1 hμx
  have n34 : ℓ3 ≠ ℓ4 := fun h => hμν (Prod.ext_iff.mp h).2
  have n21 : ℓ2 ≠ ℓ1 := Ne.symm n12
  have n31 : ℓ3 ≠ ℓ1 := Ne.symm n13
  have n41 : ℓ4 ≠ ℓ1 := Ne.symm n14
  have n32 : ℓ3 ≠ ℓ2 := Ne.symm n23
  have n42 : ℓ4 ≠ ℓ2 := Ne.symm n24
  have n43 : ℓ4 ≠ ℓ3 := Ne.symm n34
  have hev1 : ∀ a : G, plaquetteFactor ρ i0 i1 i2 i3 ℓ1 ℓ2 ℓ3 ℓ4 ℓ1 a
      = repMatrix ρ a i0 i1 := fun a => if_pos rfl
  have hev2 : ∀ a : G, plaquetteFactor ρ i0 i1 i2 i3 ℓ1 ℓ2 ℓ3 ℓ4 ℓ2 a
      = repMatrix ρ a i1 i2 := fun a => (if_neg n21).trans (if_pos rfl)
  have hev3 : ∀ a : G, plaquetteFactor ρ i0 i1 i2 i3 ℓ1 ℓ2 ℓ3 ℓ4 ℓ3 a
      = repMatrix ρ (a⁻¹) i2 i3 := fun a =>
    (if_neg n31).trans ((if_neg n32).trans (if_pos rfl))
  have hev4 : ∀ a : G, plaquetteFactor ρ i0 i1 i2 i3 ℓ1 ℓ2 ℓ3 ℓ4 ℓ4 a
      = repMatrix ρ (a⁻¹) i3 i0 := fun a =>
    (if_neg n41).trans ((if_neg n42).trans ((if_neg n43).trans (if_pos rfl)))
  have hev0 : ∀ ℓ' : Link Λ, ∀ a : G, ℓ' ≠ ℓ1 → ℓ' ≠ ℓ2 → ℓ' ≠ ℓ3 →
      ℓ' ≠ ℓ4 → plaquetteFactor ρ i0 i1 i2 i3 ℓ1 ℓ2 ℓ3 ℓ4 ℓ' a = 1 :=
    fun ℓ' a h1 h2 h3 h4 =>
      (if_neg h1).trans ((if_neg h2).trans ((if_neg h3).trans (if_neg h4)))
  have hA : ∀ U : Config Λ G,
      (∏ ℓ' : Link Λ, plaquetteFactor ρ i0 i1 i2 i3 ℓ1 ℓ2 ℓ3 ℓ4 ℓ' (U ℓ'))
        = repMatrix ρ (U ℓ1) i0 i1 * (repMatrix ρ (U ℓ2) i1 i2 *
            (repMatrix ρ ((U ℓ3)⁻¹) i2 i3 *
              repMatrix ρ ((U ℓ4)⁻¹) i3 i0)) := by
    intro U
    rw [prod_four n12 n13 n14 n23 n24 n34
      (fun ℓ' h1 h2 h3 h4 => hev0 ℓ' (U ℓ') h1 h2 h3 h4),
      hev1 (U ℓ1), hev2 (U ℓ2), hev3 (U ℓ3), hev4 (U ℓ4)]
  have hB : (∫ U, ∏ ℓ' : Link Λ,
        plaquetteFactor ρ i0 i1 i2 i3 ℓ1 ℓ2 ℓ3 ℓ4 ℓ' (U ℓ')
        ∂(configMeasure μG))
      = ∏ ℓ' : Link Λ, ∫ a,
          plaquetteFactor ρ i0 i1 i2 i3 ℓ1 ℓ2 ℓ3 ℓ4 ℓ' a ∂μG := by
    unfold configMeasure
    exact integral_fintype_prod_eq_prod
      (fun ℓ' a => plaquetteFactor ρ i0 i1 i2 i3 ℓ1 ℓ2 ℓ3 ℓ4 ℓ' a)
  have hC : ∏ ℓ' : Link Λ, ∫ a,
        plaquetteFactor ρ i0 i1 i2 i3 ℓ1 ℓ2 ℓ3 ℓ4 ℓ' a ∂μG
      = haarIntertwiner μG ρ i0 i1 * (haarIntertwiner μG ρ i1 i2 *
          (haarIntertwiner μG ρ i2 i3 * haarIntertwiner μG ρ i3 i0)) := by
    rw [prod_four n12 n13 n14 n23 n24 n34
      (fun ℓ' h1 h2 h3 h4 => by
        rw [integral_congr_ae (Filter.Eventually.of_forall
          fun a => hev0 ℓ' a h1 h2 h3 h4)]
        simp [integral_const]),
      show (∫ a, plaquetteFactor ρ i0 i1 i2 i3 ℓ1 ℓ2 ℓ3 ℓ4 ℓ1 a ∂μG)
          = haarIntertwiner μG ρ i0 i1 from
        (integral_congr_ae (Filter.Eventually.of_forall fun a => hev1 a)).trans
          (haarIntertwiner_apply μG ρ hρcont i0 i1).symm,
      show (∫ a, plaquetteFactor ρ i0 i1 i2 i3 ℓ1 ℓ2 ℓ3 ℓ4 ℓ2 a ∂μG)
          = haarIntertwiner μG ρ i1 i2 from
        (integral_congr_ae (Filter.Eventually.of_forall fun a => hev2 a)).trans
          (haarIntertwiner_apply μG ρ hρcont i1 i2).symm,
      show (∫ a, plaquetteFactor ρ i0 i1 i2 i3 ℓ1 ℓ2 ℓ3 ℓ4 ℓ3 a ∂μG)
          = haarIntertwiner μG ρ i2 i3 from
        (integral_congr_ae (Filter.Eventually.of_forall fun a => hev3 a)).trans
          ((integral_inv_eq_self (fun a => repMatrix ρ a i2 i3) μG).trans
            (haarIntertwiner_apply μG ρ hρcont i2 i3).symm),
      show (∫ a, plaquetteFactor ρ i0 i1 i2 i3 ℓ1 ℓ2 ℓ3 ℓ4 ℓ4 a ∂μG)
          = haarIntertwiner μG ρ i3 i0 from
        (integral_congr_ae (Filter.Eventually.of_forall fun a => hev4 a)).trans
          ((integral_inv_eq_self (fun a => repMatrix ρ a i3 i0) μG).trans
            (haarIntertwiner_apply μG ρ hρcont i3 i0).symm)]
  calc (∫ U, repMatrix ρ (U ℓ1) i0 i1 * (repMatrix ρ (U ℓ2) i1 i2 *
          (repMatrix ρ ((U ℓ3)⁻¹) i2 i3 * repMatrix ρ ((U ℓ4)⁻¹) i3 i0))
          ∂(configMeasure μG))
      = ∫ U, ∏ ℓ' : Link Λ,
          plaquetteFactor ρ i0 i1 i2 i3 ℓ1 ℓ2 ℓ3 ℓ4 ℓ' (U ℓ')
          ∂(configMeasure μG) :=
        integral_congr_ae (Filter.Eventually.of_forall fun U => (hA U).symm)
    _ = ∏ ℓ' : Link Λ, ∫ a,
          plaquetteFactor ρ i0 i1 i2 i3 ℓ1 ℓ2 ℓ3 ℓ4 ℓ' a ∂μG := hB
    _ = haarIntertwiner μG ρ i0 i1 * (haarIntertwiner μG ρ i1 i2 *
          (haarIntertwiner μG ρ i2 i3 * haarIntertwiner μG ρ i3 i0)) := hC

/-- **β = 0 plaquette trace**: the Haar expectation of the trace of a
plaquette is the trace of the intertwiner — the four factorized
intertwiners collapse by idempotence. -/
theorem integral_trace_plaquette
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (x : Λ) {μ ν : Fin 4} (hμν : μ ≠ ν)
    (hμx : σ μ x ≠ x) (hνx : σ ν x ≠ x) :
    ∫ U, Matrix.trace (repMatrix ρ (plaquette σ U x μ ν)) ∂(configMeasure μG)
      = Matrix.trace (haarIntertwiner μG ρ) := by
  classical
  have entryInt : ∀ a b : Fin d, Integrable
      (fun U : Config Λ G => repMatrix ρ (plaquette σ U x μ ν) a b)
      (configMeasure μG) := by
    intro a b
    refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun U => ?_)
    · have hm : Measurable fun U : Config Λ G => plaquette σ U x μ ν :=
        measurable_plaquette σ x μ ν
      exact ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp
        (hρcont.measurable.comp hm))).aestronglyMeasurable
    · exact abs_entry_of_mem_unitaryGroup (repMatrix_mem ρ _) a b
  have flatInt : ∀ i0 i1 i2 i3 : Fin d, Integrable
      (fun U : Config Λ G => repMatrix ρ (U (x, μ)) i0 i1 *
        (repMatrix ρ (U (σ μ x, ν)) i1 i2 *
          (repMatrix ρ ((U (σ ν x, μ))⁻¹) i2 i3 *
            repMatrix ρ ((U (x, ν))⁻¹) i3 i0))) (configMeasure μG) := by
    intro i0 i1 i2 i3
    have hm : Measurable fun U : Config Λ G => repMatrix ρ (U (x, μ)) i0 i1 *
        (repMatrix ρ (U (σ μ x, ν)) i1 i2 *
          (repMatrix ρ ((U (σ ν x, μ))⁻¹) i2 i3 *
            repMatrix ρ ((U (x, ν))⁻¹) i3 i0)) :=
      (measurable_repMatrix_link_entry ρ hρcont (x, μ) i0 i1).mul
        ((measurable_repMatrix_link_entry ρ hρcont (σ μ x, ν) i1 i2).mul
          ((measurable_repMatrix_link_entry_inv ρ hρcont (σ ν x, μ) i2 i3).mul
            (measurable_repMatrix_link_entry_inv ρ hρcont (x, ν) i3 i0)))
    refine Integrable.of_bound hm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun U => ?_)
    calc ‖repMatrix ρ (U (x, μ)) i0 i1 *
            (repMatrix ρ (U (σ μ x, ν)) i1 i2 *
              (repMatrix ρ ((U (σ ν x, μ))⁻¹) i2 i3 *
                repMatrix ρ ((U (x, ν))⁻¹) i3 i0))‖
        = ‖repMatrix ρ (U (x, μ)) i0 i1‖ *
            (‖repMatrix ρ (U (σ μ x, ν)) i1 i2‖ *
              (‖repMatrix ρ ((U (σ ν x, μ))⁻¹) i2 i3‖ *
                ‖repMatrix ρ ((U (x, ν))⁻¹) i3 i0‖)) := by
          simp only [norm_mul]
      _ ≤ 1 * (1 * (1 * 1)) :=
          mul_le_mul
            (abs_entry_of_mem_unitaryGroup (repMatrix_mem ρ _) _ _)
            (mul_le_mul
              (abs_entry_of_mem_unitaryGroup (repMatrix_mem ρ _) _ _)
              (mul_le_mul
                (abs_entry_of_mem_unitaryGroup (repMatrix_mem ρ _) _ _)
                (abs_entry_of_mem_unitaryGroup (repMatrix_mem ρ _) _ _)
                (norm_nonneg _) (by norm_num))
              (by positivity) (by norm_num))
            (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have hentry : ∀ (U : Config Λ G) (i0 : Fin d),
      repMatrix ρ (plaquette σ U x μ ν) i0 i0
        = ∑ i1, ∑ i2, ∑ i3, repMatrix ρ (U (x, μ)) i0 i1 *
            (repMatrix ρ (U (σ μ x, ν)) i1 i2 *
              (repMatrix ρ ((U (σ ν x, μ))⁻¹) i2 i3 *
                repMatrix ρ ((U (x, ν))⁻¹) i3 i0)) := by
    intro U i0
    have hρ : repMatrix ρ (plaquette σ U x μ ν)
        = repMatrix ρ (U (x, μ)) * (repMatrix ρ (U (σ μ x, ν)) *
            (repMatrix ρ ((U (σ ν x, μ))⁻¹) *
              repMatrix ρ ((U (x, ν))⁻¹))) := by
      simp only [plaquette, repMatrix_mul, mul_assoc]
    rw [hρ]
    simp only [Matrix.mul_apply, Finset.mul_sum]
  have hP4 : ∀ i0 : Fin d, (haarIntertwiner μG ρ * (haarIntertwiner μG ρ *
        (haarIntertwiner μG ρ * haarIntertwiner μG ρ))) i0 i0
      = ∑ i1, ∑ i2, ∑ i3, haarIntertwiner μG ρ i0 i1 *
          (haarIntertwiner μG ρ i1 i2 * (haarIntertwiner μG ρ i2 i3 *
            haarIntertwiner μG ρ i3 i0)) := by
    intro i0
    simp only [Matrix.mul_apply, Finset.mul_sum]
  have per : ∀ i0 : Fin d, (∫ U, repMatrix ρ (plaquette σ U x μ ν) i0 i0
        ∂(configMeasure μG))
      = (haarIntertwiner μG ρ * (haarIntertwiner μG ρ *
          (haarIntertwiner μG ρ * haarIntertwiner μG ρ))) i0 i0 := by
    intro i0
    calc (∫ U, repMatrix ρ (plaquette σ U x μ ν) i0 i0 ∂(configMeasure μG))
        = ∫ U, ∑ i1, ∑ i2, ∑ i3, repMatrix ρ (U (x, μ)) i0 i1 *
            (repMatrix ρ (U (σ μ x, ν)) i1 i2 *
              (repMatrix ρ ((U (σ ν x, μ))⁻¹) i2 i3 *
                repMatrix ρ ((U (x, ν))⁻¹) i3 i0)) ∂(configMeasure μG) :=
          integral_congr_ae (Filter.Eventually.of_forall fun U => hentry U i0)
      _ = ∑ i1, ∫ U, ∑ i2, ∑ i3, repMatrix ρ (U (x, μ)) i0 i1 *
            (repMatrix ρ (U (σ μ x, ν)) i1 i2 *
              (repMatrix ρ ((U (σ ν x, μ))⁻¹) i2 i3 *
                repMatrix ρ ((U (x, ν))⁻¹) i3 i0)) ∂(configMeasure μG) :=
          integral_finsetSum _ fun i1 _ => integrable_finsetSum _ fun i2 _ =>
            integrable_finsetSum _ fun i3 _ => flatInt i0 i1 i2 i3
      _ = ∑ i1, ∑ i2, ∫ U, ∑ i3, repMatrix ρ (U (x, μ)) i0 i1 *
            (repMatrix ρ (U (σ μ x, ν)) i1 i2 *
              (repMatrix ρ ((U (σ ν x, μ))⁻¹) i2 i3 *
                repMatrix ρ ((U (x, ν))⁻¹) i3 i0)) ∂(configMeasure μG) :=
          Finset.sum_congr rfl fun i1 _ => integral_finsetSum _
            fun i2 _ => integrable_finsetSum _ fun i3 _ => flatInt i0 i1 i2 i3
      _ = ∑ i1, ∑ i2, ∑ i3, ∫ U, repMatrix ρ (U (x, μ)) i0 i1 *
            (repMatrix ρ (U (σ μ x, ν)) i1 i2 *
              (repMatrix ρ ((U (σ ν x, μ))⁻¹) i2 i3 *
                repMatrix ρ ((U (x, ν))⁻¹) i3 i0)) ∂(configMeasure μG) :=
          Finset.sum_congr rfl fun i1 _ => Finset.sum_congr rfl fun i2 _ =>
            integral_finsetSum _ fun i3 _ => flatInt i0 i1 i2 i3
      _ = ∑ i1, ∑ i2, ∑ i3, haarIntertwiner μG ρ i0 i1 *
            (haarIntertwiner μG ρ i1 i2 * (haarIntertwiner μG ρ i2 i3 *
              haarIntertwiner μG ρ i3 i0)) :=
          Finset.sum_congr rfl fun i1 _ => Finset.sum_congr rfl fun i2 _ =>
            Finset.sum_congr rfl fun i3 _ =>
              integral_plaquette_entry σ μG ρ hρcont x hμν hμx hνx i0 i1 i2 i3
      _ = (haarIntertwiner μG ρ * (haarIntertwiner μG ρ *
            (haarIntertwiner μG ρ * haarIntertwiner μG ρ))) i0 i0 :=
          (hP4 i0).symm
  have htr : (∫ U, Matrix.trace (repMatrix ρ (plaquette σ U x μ ν))
        ∂(configMeasure μG))
      = ∫ U, ∑ i0, repMatrix ρ (plaquette σ U x μ ν) i0 i0
        ∂(configMeasure μG) := rfl
  rw [htr, integral_finsetSum _ (fun i0 _ => entryInt i0 i0)]
  calc ∑ i0, ∫ U, repMatrix ρ (plaquette σ U x μ ν) i0 i0 ∂(configMeasure μG)
      = ∑ i0, (haarIntertwiner μG ρ * (haarIntertwiner μG ρ *
          (haarIntertwiner μG ρ * haarIntertwiner μG ρ))) i0 i0 :=
        Finset.sum_congr rfl fun i0 _ => per i0
    _ = Matrix.trace (haarIntertwiner μG ρ * (haarIntertwiner μG ρ *
          (haarIntertwiner μG ρ * haarIntertwiner μG ρ))) := rfl
    _ = Matrix.trace (haarIntertwiner μG ρ) := by
        rw [haarIntertwiner_idempotent μG ρ hρcont,
          haarIntertwiner_idempotent μG ρ hρcont,
          haarIntertwiner_idempotent μG ρ hρcont]

/-- **Headline, β = 0**: the Gibbs expectation of a plaquette Wilson
loop at `β = 0` is the trace of the Haar intertwiner of `ρ`. -/
theorem gibbsExpect_zero_plaquette
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (x : Λ) {μ ν : Fin 4} (hμν : μ ≠ ν)
    (hμx : σ μ x ≠ x) (hνx : σ ν x ≠ x) :
    gibbsExpect σ μG ρ 0
        (fun U => Matrix.trace (repMatrix ρ (plaquette σ U x μ ν)))
      = Matrix.trace (haarIntertwiner μG ρ) := by
  rw [gibbsExpect_zero]
  exact integral_trace_plaquette σ μG ρ hρcont x hμν hμx hνx

/-- The same headline in Wilson-loop form: the plaquette loop's
expectation at `β = 0`. -/
theorem gibbsExpect_zero_wilsonLoop_plaquette
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hσ : ∀ μ ν : Fin 4, ∀ x : Λ, σ μ (σ ν x) = σ ν (σ μ x))
    (x : Λ) {μ ν : Fin 4} (hμν : μ ≠ ν)
    (hμx : σ μ x ≠ x) (hνx : σ ν x ≠ x) :
    gibbsExpect σ μG ρ 0
        (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν))
      = Matrix.trace (haarIntertwiner μG ρ) := by
  have hfun : (fun U => wilsonLoop σ ρ U x (plaquetteSteps μ ν))
      = (fun U => Matrix.trace (repMatrix ρ (plaquette σ U x μ ν))) := by
    funext U
    unfold wilsonLoop
    rw [loopProd_plaquetteSteps σ hσ]
  rw [hfun]
  exact gibbsExpect_zero_plaquette σ μG ρ hρcont x hμν hμx hνx

/-- **Vanishing form**: when `ρ` has no nonzero fixed vectors, the
plaquette Wilson loop expectation at `β = 0` is `0`. This is the
Haar-orthogonality vanishing of the brief, in projection form. -/
theorem gibbsExpect_zero_plaquette_eq_zero
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (x : Λ) {μ ν : Fin 4} (hμν : μ ≠ ν)
    (hμx : σ μ x ≠ x) (hνx : σ ν x ≠ x)
    (h : ∀ v : Fin d → ℂ, (∀ g : G, repMatrix ρ g *ᵥ v = v) → v = 0) :
    gibbsExpect σ μG ρ 0
        (fun U => Matrix.trace (repMatrix ρ (plaquette σ U x μ ν))) = 0 := by
  rw [gibbsExpect_zero_plaquette σ μG ρ hρcont x hμν hμx hνx,
    haarIntertwiner_eq_zero_of_no_fixed μG ρ hρcont h, Matrix.trace_zero]

end BetaZero

/-! ## §8. Instances

The abstract hypotheses are inhabited by the intended models:

* the concrete torus lattice `Fin 4 → ZMod N` with cyclic coordinate
  shifts (the abstract `σ` of §1), satisfying commutation and, for
  `2 ≤ N`, the fixed-point-free condition the β = 0 package consumes;
* the circle with its fundamental representation (`d = 1`);
* a unitary group itself with its identity representation (any `d`;
  `d = 2` is the SU(2)-shaped case up to the determinant condition,
  which the expectation values proved here do not see), with the
  topological-group, compactness, second-countability and
  local-compactness instances the Haar/Gibbs/β = 0 sections consume,
  supplied in-module where Mathlib does not register them globally.
-/

section Instances

open MeasureTheory

/-- The torus shifts: cyclic translation of the `μ`-th coordinate of
`Fin 4 → ZMod N`. -/
def torusShift (N : ℕ) : Fin 4 → Equiv.Perm (Fin 4 → ZMod N) :=
  fun μ => Equiv.addLeft (Pi.single μ 1)

theorem torusShift_apply (N : ℕ) (μ : Fin 4) (x : Fin 4 → ZMod N) :
    torusShift N μ x = Pi.single μ 1 + x := rfl

/-- Torus shifts commute (the hypothesis the plaquette-as-loop
identification consumes). -/
theorem torusShift_comm (N : ℕ) (μ ν : Fin 4) (x : Fin 4 → ZMod N) :
    torusShift N μ (torusShift N ν x) = torusShift N ν (torusShift N μ x) := by
  show Pi.single μ (1 : ZMod N) + (Pi.single ν (1 : ZMod N) + x)
    = Pi.single ν (1 : ZMod N) + (Pi.single μ (1 : ZMod N) + x)
  exact add_left_comm _ _ _

/-- For `2 ≤ N`, torus shifts have no fixed points (the hypothesis the
β = 0 plaquette theorem consumes). -/
theorem torusShift_ne_self (N : ℕ) [NeZero N] (hN : 2 ≤ N) (μ : Fin 4)
    (x : Fin 4 → ZMod N) : torusShift N μ x ≠ x := by
  have h10 : (1 : ZMod N) ≠ 0 := by
    intro h
    rw [show (1 : ZMod N) = ((1 : ℕ) : ZMod N) by simp,
      ZMod.natCast_eq_zero_iff] at h
    have hle := Nat.le_of_dvd (by norm_num) h
    omega
  intro h
  have hx := congrFun h μ
  rw [torusShift_apply, Pi.add_apply, Pi.single_eq_same] at hx
  have hx2 : (1 : ZMod N) + x μ = 0 + x μ := by rw [hx, zero_add]
  exact h10 (add_right_cancel hx2)

/-- The fundamental representation of the circle, as a homomorphism
into the `1 × 1` unitary group. -/
def circleRep : Circle →* ↥(Matrix.unitaryGroup (Fin 1) ℂ) where
  toFun z := ⟨Matrix.of fun _ _ => (z : ℂ), by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    obtain rfl : i = j := Subsingleton.elim i j
    obtain rfl : i = 0 := Subsingleton.elim i 0
    simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton,
      Matrix.star_apply, Matrix.of_apply, Matrix.one_apply_eq]
    have hz : ‖(z : ℂ)‖ = 1 := Circle.norm_coe z
    have h2 : (z : ℂ) * star (z : ℂ) = 1 := by
      rw [congrFun RCLike.star_def (z : ℂ)]
      exact (RCLike.mul_conj (z : ℂ)).trans (by rw [hz]; norm_num)
    exact h2⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    obtain rfl : i = j := Subsingleton.elim i j
    obtain rfl : i = 0 := Subsingleton.elim i 0
    simp [Matrix.of_apply, Matrix.one_apply_eq]
  map_mul' := by
    intro z w
    apply Subtype.ext
    ext i j
    obtain rfl : i = j := Subsingleton.elim i j
    obtain rfl : i = 0 := Subsingleton.elim i 0
    simp [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]

theorem circleRep_continuous :
    Continuous fun z : Circle => repMatrix circleRep z := by
  refine continuous_matrix fun i j => ?_
  show Continuous fun z : Circle => (z : ℂ)
  exact continuous_subtype_val

/-- The fundamental representation of the circle has no nonzero fixed
vectors (the witness is `z = -1`). -/
theorem circleRep_no_fixed (v : Fin 1 → ℂ)
    (hv : ∀ z : Circle, repMatrix circleRep z *ᵥ v = v) : v = 0 := by
  have hmem : (-1 : ℂ) ∈ Submonoid.unitSphere ℂ := by
    simp [Submonoid.unitSphere]
  set z₀ : Circle := ⟨-1, hmem⟩ with hz₀
  have h1 := congrFun (hv z₀) 0
  have h2 : (repMatrix circleRep z₀ *ᵥ v) 0 = - v 0 := by
    show (∑ j, (-1 : ℂ) * v j) = - v 0
    rw [Finset.sum_eq_single 0
      (fun b _ hb => absurd (Subsingleton.elim b 0) hb)
      (fun h => absurd (Finset.mem_univ 0) h)]
    ring
  rw [h2] at h1
  have hv0 : v 0 = 0 := by linear_combination -h1 / 2
  funext i
  obtain rfl : i = 0 := Subsingleton.elim i 0
  exact hv0

/-- The Pi-transported locally compact structure on matrices (Mathlib
registers no global norm-based instance; the Pi topology is the one
in use). -/
instance {d : ℕ} : LocallyCompactSpace (Matrix (Fin d) (Fin d) ℂ) :=
  inferInstanceAs (LocallyCompactSpace (Fin d → Fin d → ℂ))

/-- The Pi-transported second-countable structure on matrices. -/
instance {d : ℕ} : SecondCountableTopology (Matrix (Fin d) (Fin d) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℂ))

instance {d : ℕ} : SecondCountableTopology
    ↥(Matrix.unitaryGroup (Fin d) ℂ) :=
  TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val

instance {d : ℕ} : ContinuousMul ↥(Matrix.unitaryGroup (Fin d) ℂ) :=
  ⟨Continuous.subtype_mk
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)) _⟩

instance {d : ℕ} : IsTopologicalGroup ↥(Matrix.unitaryGroup (Fin d) ℂ) where
  continuous_inv := by
    have hstar : ∀ A : ↥(Matrix.unitaryGroup (Fin d) ℂ),
        star (A : Matrix (Fin d) (Fin d) ℂ) ∈ Matrix.unitaryGroup (Fin d) ℂ :=
      fun A => Matrix.mem_unitaryGroup_iff.mpr (by
        rw [star_star]
        exact Matrix.mem_unitaryGroup_iff'.mp A.2)
    have hcont : Continuous fun A : ↥(Matrix.unitaryGroup (Fin d) ℂ) =>
        (⟨star (A : Matrix (Fin d) (Fin d) ℂ), hstar A⟩ :
          ↥(Matrix.unitaryGroup (Fin d) ℂ)) :=
      Continuous.subtype_mk (continuous_star.comp continuous_subtype_val) _
    have hfun : (fun A : ↥(Matrix.unitaryGroup (Fin d) ℂ) => A⁻¹)
        = (fun A : ↥(Matrix.unitaryGroup (Fin d) ℂ) =>
          (⟨star (A : Matrix (Fin d) (Fin d) ℂ), hstar A⟩ :
            ↥(Matrix.unitaryGroup (Fin d) ℂ))) := by
      funext A
      exact Subtype.ext (Matrix.UnitaryGroup.inv_apply A)
    rw [hfun]
    exact hcont

/-- The unitary group is compact: it is a closed subset of the
product of entry disks (entries of a unitary matrix have norm ≤ 1). -/
instance {d : ℕ} : CompactSpace ↥(Matrix.unitaryGroup (Fin d) ℂ) := by
  have hclosed : IsClosed (↑(Matrix.unitaryGroup (Fin d) ℂ) :
      Set (Matrix (Fin d) (Fin d) ℂ)) := by
    have heq : (↑(Matrix.unitaryGroup (Fin d) ℂ) :
        Set (Matrix (Fin d) (Fin d) ℂ))
        = (fun A => star A * A) ⁻¹' {1} := by
      ext A
      simp [Matrix.mem_unitaryGroup_iff']
    rw [heq]
    exact isClosed_singleton.preimage
      ((continuous_star.comp continuous_id).mul continuous_id)
  have hsub : (↑(Matrix.unitaryGroup (Fin d) ℂ) :
      Set (Matrix (Fin d) (Fin d) ℂ))
      ⊆ Set.pi Set.univ (fun _ : Fin d => Set.pi Set.univ
          (fun _ : Fin d => Metric.closedBall 0 1)) := by
    intro A hA
    refine Set.mem_pi.mpr fun i _ => Set.mem_pi.mpr fun j _ => ?_
    rw [Metric.mem_closedBall]
    simpa [dist_zero_right] using abs_entry_of_mem_unitaryGroup hA i j
  have hK : IsCompact (↑(Matrix.unitaryGroup (Fin d) ℂ) :
      Set (Matrix (Fin d) (Fin d) ℂ)) :=
    IsCompact.of_isClosed_subset
      (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
        isCompact_closedBall (0 : ℂ) 1) hclosed hsub
  exact isCompact_iff_compactSpace.mp hK

/-- The identity representation of the unitary group on itself. -/
def unitaryRep (d : ℕ) :
    ↥(Matrix.unitaryGroup (Fin d) ℂ) →* ↥(Matrix.unitaryGroup (Fin d) ℂ) :=
  MonoidHom.id _

theorem unitaryRep_continuous (d : ℕ) :
    Continuous fun A : ↥(Matrix.unitaryGroup (Fin d) ℂ) =>
      repMatrix (unitaryRep d) A :=
  continuous_subtype_val

/-- The identity representation has no nonzero fixed vectors: a vector
fixed by every unitary matrix is killed by the diagonal sign flip at
any coordinate where it does not vanish. -/
theorem unitaryRep_no_fixed (d : ℕ) (v : Fin d → ℂ)
    (hv : ∀ A : ↥(Matrix.unitaryGroup (Fin d) ℂ),
      repMatrix (unitaryRep d) A *ᵥ v = v) : v = 0 := by
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  set w : Fin d → ℂ := Function.update (1 : Fin d → ℂ) i (-1) with hw
  have hwmem : Matrix.diagonal w ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      show (1 : Matrix (Fin d) (Fin d) ℂ) = Matrix.diagonal (1 : Fin d → ℂ) from
        (Matrix.diagonal_one).symm]
    congr 1
    funext k
    by_cases hk : k = i
    · subst hk
      simp [hw, Pi.mul_apply, Pi.star_apply, Function.update_self]
    · simp [hw, Pi.mul_apply, Pi.star_apply, Function.update_of_ne hk]
  have hA := congrFun (hv ⟨Matrix.diagonal w, hwmem⟩) i
  have hentry : (repMatrix (unitaryRep d) ⟨Matrix.diagonal w, hwmem⟩ *ᵥ v) i
      = - v i := by
    show (Matrix.diagonal w *ᵥ v) i = - v i
    rw [Matrix.mulVec_diagonal]
    simp [hw, Function.update_self]
  rw [hentry] at hA
  exact hi (by linear_combination -hA / 2)

/-- **Assembled β = 0 corollary, circle**: on the torus lattice with
`2 ≤ N`, for the circle's fundamental representation, every plaquette
Wilson loop has expectation `0` at `β = 0`. -/
theorem circle_plaquette_expectation_zero (N : ℕ) [NeZero N] (hN : 2 ≤ N)
    (x : Fin 4 → ZMod N) (μ ν : Fin 4) (hμν : μ ≠ ν) :
    gibbsExpect (torusShift N) (haarProb Circle) circleRep 0
        (fun U => Matrix.trace
          (repMatrix circleRep (plaquette (torusShift N) U x μ ν))) = 0 :=
  gibbsExpect_zero_plaquette_eq_zero (torusShift N) (haarProb Circle) circleRep
    circleRep_continuous x hμν (torusShift_ne_self N hN μ x)
    (torusShift_ne_self N hN ν x) circleRep_no_fixed

/-- **Assembled β = 0 corollary, unitary group**: on the torus lattice
with `2 ≤ N`, for the identity representation of a unitary group
(any `d`; `d = 2` is the SU(2)-shaped case up to the determinant
condition), every plaquette Wilson loop has expectation `0` at
`β = 0`. -/
theorem unitary_plaquette_expectation_zero (d N : ℕ) [NeZero N] (hN : 2 ≤ N)
    (x : Fin 4 → ZMod N) (μ ν : Fin 4) (hμν : μ ≠ ν) :
    gibbsExpect (torusShift N)
        (haarProb ↥(Matrix.unitaryGroup (Fin d) ℂ)) (unitaryRep d) 0
        (fun U => Matrix.trace
          (repMatrix (unitaryRep d) (plaquette (torusShift N) U x μ ν)))
      = 0 :=
  gibbsExpect_zero_plaquette_eq_zero (torusShift N)
    (haarProb ↥(Matrix.unitaryGroup (Fin d) ℂ)) (unitaryRep d)
    (unitaryRep_continuous d) x hμν (torusShift_ne_self N hN μ x)
    (torusShift_ne_self N hN ν x) (unitaryRep_no_fixed d)

end Instances
