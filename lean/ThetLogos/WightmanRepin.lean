import Mathlib.Analysis.Distribution.TemperedDistribution
import ThetLogos.OSRepin
import ThetLogos.Rung5W1
import ThetLogos.Rung5W2
import ThetLogos.Rung5W3
import ThetLogos.Rung5W4
import ThetLogos.Rung5W5
import ThetLogos.Rung5W6

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct SchwartzMap

/-!
# ThetLogos.WightmanRepin — the Wightman pin, re-pinned (unlock chain item 3)

Dossier: `whitepaper/wightman-repin-2026-10-18.md`. This module is
the sibling of `ThetLogos.OSRepin`: the OS re-pin convicted the old
OS pin in three places and explicitly flagged the sibling file
`WightmanAxioms.lean` for the same treatment ("correcting that file
is its own future re-pin, flagged here, not done here"). This brick
is that re-pin, at the same priced scope (S–M). Neither
`WightmanAxioms.lean` nor `WightmanTargets.lean` is modified.

What it does, and nothing else:

1. **Corrections (§1).** Two machine-checked findings against the
   old Wightman-side pins:
   (i) `InteractingWightmanQFT` (the 2026 pin's existence
   statement, `∃ _ : WightmanAxioms, True` over an all-`Prop`
   bundle) is **vacuous** — proved in `OSRepin`
   (`oldPin_interactingWightmanQFT_trivial`) and re-cited here in
   `WightmanExistence` form, since this file is the Wightman
   correction sheet of record.
   (ii) **NEW:** the Rung-4 sharpened bundle `SharpWightmanTarget`
   is **also vacuous** (`sharpWightmanTarget_trivial`, T1): the
   bundle existentially quantifies over the very data that carry
   the axioms' content — the field, the joint spectrum `spec`,
   the spacelike-separation relation, the Wightman functions `w`
   — so junk data (one-mode test functions, the scalar-multiple
   "field" `f ↦ f • id`, trivial representations, `spec = {0}`,
   `spacelikeSep = ⊥`, an arbitrary `w` with connected 4-point
   `1`) satisfy all six sharp clauses at once. The six sharp
   definitions are exact *conditions on fixed data*; bundled
   under `∃` over their own semantic parameters, they state
   nothing. This is the OS pin's disease one level up, in the
   file Rung 4 built to sharpen the pin.
   Beside the theorems: the old file's header and dependency
   ledger assert "Mathlib (2026) has no Schwartz distribution
   theory" — **stale**, convicted already by the OS re-pin: the
   pinned Mathlib ships `𝓢'` with Fourier theory, Rung 6 built on
   it, and §2 of this module discharges the old
   `TemperedDistMarker` by using the genuine article.
2. **The re-pinned axioms (§2–§4).** Wightman functions are real
   objects: `W n : 𝓢'(Fin n × Fin 4 → ℝ, ℂ)`, tempered
   distributions on Minkowski point tuples. `WightmanBundle` is a
   structure of *data plus real conditions* — Poincaré covariance
   (Lorentz maps pinned by `minkowskiInner` preservation),
   Hermiticity, the spectrum condition (Fourier-support form, the
   Fourier transform on test functions defined in §3 with its
   integrability proved), locality at spacelike separation,
   Wightman positivity, clustering — every field fully quantified,
   no opaque `Prop`s. Nontriviality is separated, reusing the OS
   re-pin's Wick-defect clause `NonGaussian`; the existence
   statement `InteractingWightmanStatement` is a real, currently
   unproved, failable Prop. **It is not claimed.**
3. **Window citations (§5).** The Rung-5 verdicts against the
   Rung-4 sharp targets, restated as wrapper theorems so the
   window-by-window table in the dossier is machine-cited, not
   prose: W1 **proved** at the one-mode fermionic model; W4
   **proved** at the one-mode model (`s = +1` form); W2 **partial**
   — ℤ₂ fermion parity only, not Poincaré; W3 **partial** — frame
   consistency for the trivial representation only; W5
   **refuted as framed**, corrected span-density **proved**; W6
   as-framed bosonic form proved but a documented **false
   positive**, corrected Koszul–Wick form **proved**.

Honesty tiers: §1 and §5 are T1 (machine-checked). §2–§4 are T1
*statements* (definitions whose content is real) about T5 subject
matter — the bundle `WightmanBundle` is not asserted to be
inhabited by any interacting theory, and no theorem in this file
proves an inhabitant. The bundle pins the **scalar (bosonic)**
form of the axioms; the spinor refinement (fields of nonzero spin,
the `2π`-rotation sign) is beyond this pin, named in the dossier.
**No interacting Wightman QFT is claimed to exist. Clay parts
closed by this module: 0.**
-/

/-! ## §1. Corrections to the old pins (T1, against the old statements) -/

/-- **CORRECTION (T1): the old pin's existence statement is
vacuous.** `WightmanExistence` is defined as
`InteractingWightmanQFT := ∃ _ : WightmanAxioms, True`, over a
bundle whose every content field is an unconstrained `Prop`; the
all-`True` instantiation proves it with no content whatsoever.
The proof itself is `OSRepin.oldPin_interactingWightmanQFT_trivial`
(the OS re-pin recorded the finding because its reconstruction
target lives in the sibling file); this wrapper puts the
correction on the Wightman file's own correction sheet, in the
`WightmanExistence` form the old file states. This theorem proves
the OLD STATEMENT and thereby its emptiness — it constructs no
QFT. Superseded by `InteractingWightmanStatement` (§4). -/
theorem oldPin_wightmanExistence_trivial : WightmanExistence :=
  oldPin_interactingWightmanQFT_trivial

/-- **CORRECTION (T1, NEW): the Rung-4 sharpened bundle
`SharpWightmanTarget` is vacuous.** Rung 4 replaced the old pin's
opaque fields by six sharp definitions with exact formulas — real
progress as *conditions* — but then bundled them as
`∃ (all data), W1 ∧ W2 ∧ W3 ∧ W4 ∧ W5 ∧ W6`, existentially
quantifying over the semantic parameters themselves: the field,
the joint spectrum, the spacelike-separation relation, the
Wightman functions. Junk data satisfy every clause at once:

* `H = ℂ`, `Ω = 1`, one-mode test functions (`T = ⟨ℂ⟩`), `D = ⊤`;
* the "field" `φ(f) = f • id` — scalar multiplication, no operator
  content — is linear, weakly Hermitian for `conjTest = star`,
  and its monomials on `Ω` cover `ℂ` (W5 holds because
  `polyApply [z] = z`);
* trivial representations discharge W2/W3 (with `spec = {0}`);
* `spacelikeSep = ⊥` makes W4 vacuous for `s = 1`;
* an arbitrary `w` with `w 4 _ = 1`, `w 2 _ = 0` gives connected
  4-point `1 ≠ 0` (W6).

So the bundle is a theorem with zero physical content — the same
unfailable shape as the old pin's existence statement, one level
up. The sharp definitions themselves are **not** impugned: as
conditions on *fixed, externally given* data they are exact, and
Rung 5's verdicts against them (§5) stand. What is corrected is
the `∃`-bundling: an existence statement must fix its data as a
structure and separate nontriviality — the method of §4. This
theorem proves the OLD BUNDLE and thereby its emptiness. -/
theorem sharpWightmanTarget_trivial : SharpWightmanTarget := by
  refine ⟨ℂ, inferInstance, inferInstance, inferInstance,
    1, ⟨ℂ⟩, inferInstance, inferInstance,
    ⊤, ?_, Submodule.mem_top,
    star, (fun f => f • LinearMap.id),
    ⟨Multiplicative (ZMod 2)⟩, inferInstance,
    (fun _ => LinearIsometryEquiv.refl ℂ ℂ), (fun _ f => f),
    (fun _ => LinearIsometryEquiv.refl ℂ ℂ), (fun _ => 0), {0},
    (fun _ _ => False), (fun n _ => if n = 4 then 1 else 0),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the domain `⊤` is dense in `ℂ`
    rw [Submodule.top_coe]
    exact dense_univ
  · -- W1 for the scalar-multiple field
    refine ⟨Submodule.mem_top, ?_, ?_, ?_, ?_, one_ne_zero⟩
    · intro f g
      exact add_smul f g _
    · intro c f
      show (c • f) • LinearMap.id = c • (f • LinearMap.id)
      rw [smul_eq_mul, smul_smul]
    · intro f ψ χ
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul,
        smul_eq_mul, RCLike.inner_apply, map_mul, RCLike.star_def]
      ring
    · intro f
      exact star_star f
  · -- W2 for the trivial representation of the marker group
    refine ⟨fun _ _ => Submodule.mem_top, ?_, rfl, ?_, ?_⟩
    · intro g₁ g₂
      simp
    · intro g₁ g₂ f
      rfl
    · intro g f ψ
      apply Subtype.ext
      simp
  · -- W3 for the trivial translation representation, `spec = {0}`
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b
      simp
    · intro _ ψ χ
      simp
    · intro _ _ ψ
      rfl
    · intro p hp
      rw [Set.mem_singleton_iff] at hp
      subst hp
      constructor <;> simp [minkowskiInner]
  · -- W4 vacuous: `spacelikeSep = ⊥`, `s = 1`
    refine ⟨(1 : ℂ), one_pow 2, ?_⟩
    intro f g h
    exact h.elim
  · -- W5: every `z : ℂ` is the monomial `polyApply [z]`
    show Dense (Set.range fun l : List ℂ =>
      (polyApply ℂ 1 ⟨ℂ⟩ ⊤ (fun f => f • LinearMap.id) Submodule.mem_top l : ℂ))
    rw [dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro z
    have hz : z ∈ Set.range (fun l : List ℂ =>
        (polyApply ℂ 1 ⟨ℂ⟩ ⊤ (fun f => f • LinearMap.id)
          Submodule.mem_top l : ℂ)) := by
      refine ⟨[z], ?_⟩
      simp [polyApply, smul_eq_mul]
    exact subset_closure hz
  · -- W6: the arbitrary `w` has connected 4-point `1`
    refine ⟨fun _ => 0, ?_⟩
    simp [connectedFourPoint]

/-! ## §2. The re-pinned Wightman data, and temperedness as the type

Test functions on `n` Minkowski points are Schwartz functions on
`Fin n × Fin 4 → ℝ` (a point is a pair: point index, coordinate) —
the same function space as the OS re-pin's `EucTest`; the
Minkowski content lives in the bundle's conditions (§4), not in
the type. -/

/-- Test functions on `n` Minkowski points: `𝓢(ℝ⁴ⁿ, ℂ)` with
pair-indexed points. -/
abbrev MinkTest (n : ℕ) := 𝓢(Fin n × Fin 4 → ℝ, ℂ)

/-- The `n`-point Wightman function as a genuine object: a tempered
distribution on `ℝ⁴ⁿ`. This discharges the old pin's opaque
`TemperedDistMarker` — the pinned Mathlib ships `𝓢'` with Fourier
theory (`Mathlib/Analysis/Distribution/TemperedDistribution.lean`),
Rung 6 built on it, and the OS re-pin discharged the sibling
marker the same way. The old file's contrary header claim is
Correction 1 of the dossier (a stale premise, not edited in the
old file — flagged for the S-editorial list). -/
abbrev WightmanDist (n : ℕ) := 𝓢'(Fin n × Fin 4 → ℝ, ℂ)

/-- **Temperedness, glue 1 of 3:** a Wightman distribution is
continuous as a function of the test function. In the old pin,
temperedness could not even be stated (the marker had no pairing);
here it is the type: `𝓢'` is by definition the continuous linear
dual of `𝓢`, and this theorem makes the continuity explicit. -/
theorem wightmanDist_continuous (n : ℕ) (W : WightmanDist n) :
    Continuous (fun f : MinkTest n => W f) := W.continuous

/-- **Temperedness, glue 2 of 3:** additivity of the pairing
(linearity of the distribution, made explicit). -/
theorem wightmanDist_add (n : ℕ) (W : WightmanDist n)
    (f g : MinkTest n) : W (f + g) = W f + W g := map_add W f g

/-- **Temperedness, glue 3 of 3:** homogeneity of the pairing.
Together with continuity, these are exactly the statement that
`W n` is a tempered distribution. -/
theorem wightmanDist_smul (n : ℕ) (W : WightmanDist n)
    (c : ℂ) (f : MinkTest n) : W (c • f) = c • W f := map_smul W c f

/-! ## §3. Coordinate operations and the spectrum condition's Fourier form

All transformations are written at the level of coordinate tuples
`Fin n × Fin 4 → ℝ`. The axiom fields in §4 quantify over Schwartz
functions `F'` whose underlying function equals a transformed `F`;
no composition machinery for `𝓢` is needed to *state* the axioms,
and no membership claim is hidden. The block operations
`firstBlock` / `secondBlock` are the OS re-pin's, reused. -/

/-- The point-reversed tuple: point `i` of the result is point
`Fin.rev i` of the input. The coordinate-level shadow of the
Wightman involution (order reversal + conjugation), used by
Hermiticity and positivity in §4. -/
def revPoints {n : ℕ} (x : Fin n × Fin 4 → ℝ) : Fin n × Fin 4 → ℝ :=
  fun p => x (Fin.rev p.1, p.2)

/-- A Lorentz transformation: a linear map on `ℝ⁴` preserving the
Minkowski inner product (signature `+,-,-,-`, pinned T1 in
`WightmanAxioms.lean`) for all pairs. This is the restricted +
reflecting Lorentz group at the linear level — every component
preserving `⟨·,·⟩`, time-orientation being part of the spectrum
condition, not of this predicate. -/
def IsLorentz (Λ : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) : Prop :=
  ∀ x y : Fin 4 → ℝ, minkowskiInner (Λ x) (Λ y) = minkowskiInner x y

/-- A Poincaré motion applied diagonally to every point of a
tuple: Lorentz part `Λ` on each point's coordinates, then
translation by `a`. -/
def minkMotion {n : ℕ} (Λ : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))
    (a : Fin 4 → ℝ) (x : Fin n × Fin 4 → ℝ) : Fin n × Fin 4 → ℝ :=
  fun p => Λ (fun c => x (p.1, c)) p.2 + a p.2

/-- The Fourier transform of a test function's underlying plain
function, at momentum tuple `ξ`, with the `2π` convention and the
Euclidean pairing on tuples:
`F̂(ξ) = ∫ e^{2πi ⟨x, ξ⟩} F(x) dx`. This is a plain Bochner
integral over tuple space (Lebesgue `volume`); the integrand is
integrable because `F` is Schwartz — proved next — so the
integral is the genuine transform, not Lean's junk value. The
spectrum condition (§4) is stated against this fixed convention;
the convention-dependence of the support statement is recorded
in the dossier. -/
noncomputable def fourierTest {n : ℕ} (F : MinkTest n)
    (ξ : Fin n × Fin 4 → ℝ) : ℂ :=
  ∫ x, Complex.exp ((2 * Real.pi * (∑ p, ∑ c, x (p, c) * ξ (p, c)) : ℝ)
    * Complex.I) * F x

/-- **The Fourier integrand is integrable (T1):** the kernel
factor has norm `1` (`Complex.norm_exp_ofReal_mul_I`) and is
continuous, and `F` is Schwartz, hence integrable
(`SchwartzMap.integrable`). This is what makes `fourierTest` an
honest integral. -/
theorem fourierTest_integrable {n : ℕ} (F : MinkTest n)
    (ξ : Fin n × Fin 4 → ℝ) :
    Integrable (fun x => Complex.exp ((2 * Real.pi
      * (∑ p, ∑ c, x (p, c) * ξ (p, c)) : ℝ) * Complex.I) * F x)
      volume := by
  have hexp : ∀ x : Fin n × Fin 4 → ℝ,
      ‖Complex.exp ((2 * Real.pi * (∑ p, ∑ c, x (p, c) * ξ (p, c)) : ℝ)
        * Complex.I)‖ = 1 := fun x => Complex.norm_exp_ofReal_mul_I _
  have hmeas : AEStronglyMeasurable (fun x => Complex.exp ((2 * Real.pi
      * (∑ p, ∑ c, x (p, c) * ξ (p, c)) : ℝ) * Complex.I) * F x) volume :=
    (by continuity : Continuous (fun x : Fin n × Fin 4 → ℝ =>
      Complex.exp ((2 * Real.pi * (∑ p, ∑ c, x (p, c) * ξ (p, c)) : ℝ)
        * Complex.I) * F x)).aestronglyMeasurable
  rw [← integrable_norm_iff hmeas]
  simp only [norm_mul, hexp, one_mul]
  exact F.integrable.norm

/-- The **spectral support set** for an `n`-point momentum tuple,
in the convention of `fourierTest`: every partial sum of the
momenta (in point order) lies in the closed forward light cone
(the cone pinned T1 in `WightmanAxioms.lean`), and the total
momentum vanishes (the translation-invariance constraint). This
is the support the spectrum condition (W3) asserts for the
Wightman functions' Fourier side. -/
def InSpectralSupport {n : ℕ} (ξ : Fin n × Fin 4 → ℝ) : Prop :=
  (∀ k : Fin n, (fun c => ∑ p ∈ Finset.Iic k, ξ (p, c)) ∈ forwardLightCone)
    ∧ (∀ c, ∑ p, ξ (p, c) = 0)

/-- Support in the spacelike-separated region for the pair of
points `i, j`: a test function is supported where the difference
of points `i` and `j` is spacelike (`⟨xᵢ - xⱼ, xᵢ - xⱼ⟩ < 0` in
the Minkowski form). This is the support hypothesis of locality
(W4), stated at the plain-function level like the OS re-pin's
`InPositiveTime`. -/
def SpacelikeSeparatedAt {n : ℕ} (F : MinkTest n) (i j : Fin n) : Prop :=
  ∀ x : Fin n × Fin 4 → ℝ, F x ≠ 0 →
    minkowskiInner (fun c => x (i, c) - x (j, c))
      (fun c => x (i, c) - x (j, c)) < 0

/-! ## §4. The re-pinned bundle (T1 statements, T5 subject matter)

Every field below is a fully quantified statement about the data
`W`. Contrast the old pin (seven unconstrained `Prop`s) and the
Rung-4 bundle (real conditions, but under `∃` over their own
semantic parameters — §1's Correction 2). Here the data are the
structure's field, the conditions are real, and nontriviality is
a separate clause (`NonGaussian`, §4 below), so the existence
statement can actually be false-shaped. The bundle pins the
**scalar** form of the axioms; vacuum cyclicity is not a field —
it is a property of the reconstructed field algebra, whose
distribution-level input is positivity (the GNS content), exactly
as in the OS re-pin, where positivity + the form give the space.
-/

/-- **The Wightman axioms, re-pinned** on genuine tempered
distributions (Streater–Wightman 1964, in the
Wightman-function form): a structure of *data plus real
conditions*, not of opaque `Prop`s, and not existentially bundled
over its own parameters. No inhabitant is asserted or proved in
this file. -/
structure WightmanBundle where
  /-- The Wightman functions: one tempered distribution per point
      count. Temperedness is this field's type (§2). -/
  W : (n : ℕ) → WightmanDist n
  /-- Vacuum normalization: the 0-point function is evaluation at
      the unique point of the empty tuple — `W₀ = 1` as a
      distribution. -/
  vacuumNormalization : ∀ f : MinkTest 0, W 0 f = f 0
  /-- **W2: Poincaré covariance.** For every Lorentz `Λ`
      (Minkowski-form preserving) and translation `a`, the value
      of `W n` is unchanged when the test function is pulled back
      along the diagonal Poincaré motion. -/
  poincareCovariant : ∀ (n : ℕ) (Λ : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)),
    IsLorentz Λ → ∀ (a : Fin 4 → ℝ) (F F' : MinkTest n),
    (∀ x, F' x = F (minkMotion Λ a x)) → W n F' = W n F
  /-- **Hermiticity.** The Wightman functions are real in the
      involutive sense: reversing the point order and conjugating
      the test function conjugates the value. -/
  hermitian : ∀ (n : ℕ) (F F' : MinkTest n),
    (∀ x, F' x = (starRingEnd ℂ) (F (revPoints x))) →
    W n F' = (starRingEnd ℂ) (W n F)
  /-- **W3: spectrum condition.** In the Fourier-support form of
      §3: `W n` annihilates every test function whose Fourier
      transform vanishes on the spectral support set — i.e. the
      Fourier side of `W n` is supported where every partial
      momentum sum lies in the closed forward light cone and the
      total momentum vanishes. (Support of a distribution is an
      annihilator condition; this is that condition, transported
      through the fixed Fourier convention of `fourierTest`.) -/
  spectrumCondition : ∀ (n : ℕ) (F : MinkTest n),
    (∀ ξ : Fin n × Fin 4 → ℝ, InSpectralSupport ξ →
      fourierTest F ξ = 0) → W n F = 0
  /-- **W4: locality.** For a test function supported where points
      `i, j` are spacelike separated, `W n` is unchanged when
      points `i, j` are swapped. (Scalar form; for fermions the
      graded sign is the spin refinement, beyond this pin.) -/
  locality : ∀ (n : ℕ) (i j : Fin n) (F F' : MinkTest n),
    (∀ x, F' x = F (fun p => x (Equiv.swap i j p.1, p.2))) →
    SpacelikeSeparatedAt F i j → W n F' = W n F
  /-- **Wightman positivity** (the Hilbert-space content of the
      axioms, the input to GNS reconstruction): for every finite
      family of test functions `F i`, and every family `G i j`
      factoring — as a plain function — as the
      reversed-conjugate of `F i` on the first block times `F j`
      on the second, the double sum `∑ i j, W (nᵢ + nⱼ) (G i j)`
      is a nonnegative real number. -/
  positive : ∀ (k : ℕ) (ns : Fin k → ℕ)
    (F : (i : Fin k) → MinkTest (ns i)),
    ∀ (G : (i j : Fin k) → MinkTest (ns i + ns j)),
    (∀ i j (z : Fin (ns i + ns j) × Fin 4 → ℝ),
      G i j z = (starRingEnd ℂ) (F i (revPoints (firstBlock z)))
        * F j (secondBlock z)) →
    ∃ r : ℝ, 0 ≤ r ∧ (∑ i, ∑ j, W (ns i + ns j) (G i j)) = r
  /-- **Clustering.** When the second factor of a factorized test
      function is translated away in the time direction
      (separation `T → ∞`), the `(n+m)`-point function converges
      to the product of the factors' functions. -/
  clustering : ∀ (n m : ℕ) (f : MinkTest n) (g : MinkTest m)
    (F : ℝ → MinkTest (n + m)),
    (∀ (T : ℝ) (z : Fin (n + m) × Fin 4 → ℝ),
      F T z = f (firstBlock z)
        * g (fun p => secondBlock z p + (if p.2 = 0 then T else 0))) →
    Filter.Tendsto (fun T : ℝ => W (n + m) (F T)) Filter.atTop
      (nhds (W n f * W m g))

/-- **An interacting Wightman QFT exists** — the re-pinned form of
the old pin's vacuous `InteractingWightmanQFT`: a full Wightman
bundle whose Wightman functions are non-Gaussian in the
Wick-defect sense (the OS re-pin's clause `NonGaussian`, reused —
the same formula, because "not quasi-free" is the same property
on both faces of reconstruction). This is a real Prop, currently
unproved; it is the Minkowski face of the constructive existence
problem. **Not claimed.** (Compare §1: the old form is a theorem,
because it says nothing; this form would be refuted by a proof
that every Wightman bundle is Gaussian.) -/
def InteractingWightmanStatement : Prop :=
  ∃ B : WightmanBundle, NonGaussian B.W

/-- The Wightman-side predicate for the OS reconstruction schema:
`SatisfiesWightmanPin W` holds when `W` is the Wightman-function
family of some bundle. The OS re-pin pinned reconstruction as a
schema (`OSReconstructionStatement`) with two named holes; its
second hole was "the Wightman-side conditions on the reconstructed
distributions (the sibling pin's own re-pin)". This definition is
that re-pin's output: `OSReconstructionStatement
IsBoundaryValueOf SatisfiesWightmanPin` is now a fully concrete
schema — every symbol in it is defined. Instantiating the first
hole (analytic continuation, Bargmann–Hall–Wightman +
edge-of-the-wedge) remains research-scale, per the OS dossier's
audit; **no reconstruction is proved or claimed.** -/
def SatisfiesWightmanPin (W : (n : ℕ) → WightmanDist n) : Prop :=
  ∃ B : WightmanBundle, B.W = W

/-! ## §5. Window citations (T1): the Rung-5 verdicts, restated

The window-by-window table in the dossier is machine-cited here:
each theorem below restates a Rung-5 verdict against the Rung-4
sharp targets and proves it by the standing theorem itself
(module named in each docstring). All verdicts are at the
**one-mode fermionic model** (`Fock1 = ∧(ℂ) ≅ ℂ²`, test functions
`⟨ℂ⟩`) — that is their scope, printed on every line of the table.
Nothing here is a continuum or multi-mode statement. -/

/-- **W1 — PROVED at the one-mode model** (`Rung5W1`): the
Majorana field `ψ(c) = c • (a† + a)` satisfies the sharp W1 target
— complex-linear in the test function, weakly Hermitian for
`conjTest = star`, vacuum in the domain and nonzero. -/
theorem window_w1_majorana :
    W1_fieldsExist_sharp Fock1 vac1 (⟨ℂ⟩ : TestFunctionMarker)
      (⊤ : Submodule ℂ Fock1) star (fun c => liftTop (fieldMajorana c)) :=
  w1_majorana

/-- **W2 — PARTIAL at the one-mode model** (`Rung5W2`): the sharp
covariance target holds for the group `Multiplicative (ZMod 2)`
acting by fermion parity. Honest scope, as in the source: the
marker group is the finite parity group, **not** the Poincaré
group; genuine Poincaré covariance of a field stays priced
(dossier §3), with its price narrowed since Rung 5 by the
standing one-particle representation and its second quantization
with strong continuity (`FockPackaging*`, `LorentzContinuity`,
`TranslationContinuity`, `FockLorentz*`). -/
theorem window_w2_parity :
    W2_poincareCovariant_sharp Fock1 ⟨ℂ⟩ (⊤ : Submodule ℂ Fock1)
      Poin repW2 actW2 (fun c => liftTop (fieldMajorana c))
      (fun _g _ψ => Submodule.mem_top) :=
  w2_parity

/-- **W3 — PARTIAL at the one-mode model** (`Rung5W3`): the sharp
spectrum target holds for the **trivial** translation
representation (energy-momentum zero, `spec = {0}`). A
frame-consistency check, as labeled in the source — not positive
energy for a genuine representation; Stone's theorem and joint
spectral calculus for unbounded operators remain the price. -/
theorem window_w3_trivial :
    W3_spectrumCondition_sharp Fock1 (⊤ : Submodule ℂ Fock1)
      (fun _ => LinearIsometryEquiv.refl ℂ Fock1)
      (fun _ => liftTop 0)
      {0} :=
  w3_trivial

/-- **W4 — PROVED at the one-mode model** (`Rung5W4`): the
Majorana field commutes with itself in the sharp target's
`s = +1` form. Honest scope, as in the source: `spacelikeSep` is
trivially `True` — the one-mode model has no spacetime, so this
discharges the algebraic (anti)commutator content, not the
support condition. -/
theorem window_w4_majorana :
    W4_locality_sharp Fock1 (⟨ℂ⟩ : TestFunctionMarker)
      (⊤ : Submodule ℂ Fock1)
      (fun c => liftTop (fieldMajorana c)) (fun _ _ => True) 1 :=
  w4_majorana

/-- **W5 — REFUTED as framed** (`Rung5W5`): the sharp target's
monomial-*range* density is **false** even for the free one-mode
fermion — every monomial lies on one of two lines, both at
distance `≥ 1` from `vac1 + e1Fock`. The Rung-4 framing was
strictly stronger than the literature's cyclicity; the refutation
is a framing correction, recorded as such in Rung 5's dossier. -/
theorem window_w5_framed_false :
    ¬ W5_vacuumCyclic_sharp Fock1 vac1 ⟨ℂ⟩ (⊤ : Submodule ℂ Fock1)
      (fun c => liftTop (fieldMajorana c)) (Submodule.mem_top) :=
  w5_framed_false

/-- **W5 — the corrected statement PROVED** (`Rung5W5`): the
linear **span** of the field monomials applied to the vacuum is
dense — in fact everything — in `Fock1`. This span form is what
the literature means by vacuum cyclicity, and it is the form the
re-pin's reconstruction-side discussion (positivity ⇒ GNS) uses. -/
theorem window_w5_span_true :
    Dense (↑(Submodule.span ℂ (Set.range fun l : List ℂ =>
      (polyApply Fock1 vac1 ⟨ℂ⟩ ⊤ (fun c => liftTop (fieldMajorana c))
        Submodule.mem_top l : Fock1))) : Set Fock1) :=
  w5_span_true

/-- **W6 — as framed, PROVED but a FALSE POSITIVE** (`Rung5W6`):
the bosonic-form sharp target holds for the free Majorana field
(connected 4-point `= -2 ≠ 0`). As labeled in the source: the
bosonic criterion is fermion-blind, so this "nontriviality" fires
on a free field; it must not be cited as interaction content. The
corrected criterion is the next citation. -/
theorem window_w6_majorana :
    W6_nontrivial_sharp (⟨ℂ⟩ : TestFunctionMarker) wMajorana :=
  w6_majorana

/-- **W6 — the corrected statement PROVED** (`Rung5W6`): with the
Koszul signs, the connected 4-point function of the Majorana
field vanishes identically — fermionic Wick's theorem — correctly
detecting that the field is free. This is the corrected form of
the W6 window. (Consistency note: §4's nontriviality clause is
the Wick-defect form `NonGaussian` — the *scalar* criterion,
matching this pin's scalar bundle. A fermionic Wightman pin would
need its own signed defect clause; unbuilt, and named here so the
reuse is not misread as statistics-aware.) -/
theorem window_w6_fermionic_wick (a b c d : ℂ) :
    wMajorana 4 [a, b, c, d]
      = wMajorana 2 [a, b] * wMajorana 2 [c, d]
        - wMajorana 2 [a, c] * wMajorana 2 [b, d]
        + wMajorana 2 [a, d] * wMajorana 2 [b, c] :=
  w6_fermionic_wick a b c d

end ThetLogos
