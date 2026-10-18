import Mathlib.Analysis.Distribution.TemperedDistribution
import ThetLogos.OsterwalderSchrader
import ThetLogos.LatticeTransfer

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct SchwartzMap

/-!
# ThetLogos.OSRepin — the Osterwalder–Schrader pin, re-pinned (Round 2 intake)

Dossier: `whitepaper/os-repin-2026-10-18.md`. This module is the
re-pin half of the Round 2 OS item, priced **S–M** by the parked-fleet
gauntlet (`whitepaper/gauntlet-parked-fleet-2026-10-17.md` §8; the
fit-audit half was KILLed there as redundant — K3 — absorbed by
Pitch 4). It does three things, and nothing else:

1. **Corrections (§1).** Three machine-checked findings against the
   2026-10-06-era pin in `OsterwalderSchrader.lean` /
   `WightmanAxioms.lean` (both files unmodified):
   (i) the old header's premise "Mathlib (2026) has no tempered
   distributions" is false for the pinned Mathlib v4.35.0-rc3, which
   ships `𝓢'(E, F)` with Fourier theory — so the opaque
   `SchwingerMarker` placeholder is dischargeable, and §2–§3
   discharge it;
   (ii) the old existence/reconstruction statements
   (`OSReconstruction`, `InteractingOSMeasure`, and the sibling
   `InteractingWightmanQFT`) are **vacuous**: they are proved below
   from an all-`True` instantiation of the opaque bundles. The old
   pin's "open problem" statements therefore carried no content.
   These three theorems are audit results *against* the old pin —
   they construct no measure, no reconstruction, and no QFT.
2. **The re-pinned axioms (§2–§3).** Schwinger functions are real
   objects: `S n : 𝓢'(Fin n × Fin 4 → ℝ, ℂ)`, a tempered
   distribution on `ℝ⁴ⁿ` (points pair-indexed; linearly isometric
   to the corpus's flat `Fin (4n) → ℝ` convention). E0 is the type
   itself plus its continuity/linearity made explicit as theorems.
   E1–E4 are fully quantified `Prop`s over this data — no opaque
   fields. The bundle is `OSBundle`; non-Gaussianity is the
   Wick-defect statement `NonGaussian`; the interacting-measure
   existence statement is `∃ B : OSBundle, NonGaussian B.S`
   (a real, currently unproved, Prop). Reconstruction is pinned as
   a *schema* (`OSReconstructionStatement`) with its two analytic
   holes named as parameters — see the dossier's dependency audit.
3. **Lattice citations (§4).** The clause-by-clause discharge
   status at finite lattice level, as wrapper theorems whose proofs
   are the standing theorems themselves: Gibbs probability (1a),
   reflection invariance of the Gibbs measure (1b-A), OS-form
   positivity at `β = 0` and the Gram criterion (1b-B), vacuum
   norm on the OS space (1b-C), transfer contraction / vacuum /
   `β = 0` projection (1b-D), `β = 0` factorization (1a).
   The general-`β` positivity clause is **not** discharged: it is
   1b-B's Gram/character-expansion clause, priced **XL /
   Mathlib-blocked** (Peter–Weyl absent from the pinned Mathlib).
   **PARTIAL-δ is not claimed. No continuum OS reconstruction is
   claimed.** Clay parts closed by this module: **0**.

Honesty tiers: §1 and §4 are T1 (machine-checked). §2–§3 are T1
*statements* (definitions whose content is real) about T5 subject
matter — the bundle `OSBundle` is not asserted to be inhabited by
any interacting theory, and no theorem in this file proves an
inhabitant.
-/

/-! ## §1. Corrections to the old pin (T1, against the old statements) -/

/-- **CORRECTION (T1): the old pin's `OSReconstruction` is vacuous.**
The 2026 pin stated reconstruction as
`∀ _ : OsterwalderSchraderAxioms, ∃ _ : WightmanAxioms, True` over
bundles whose every content field is an unconstrained `Prop`. Both
bundles are inhabited by the all-`True` instantiation, so the
statement is provable with no analytic content whatsoever. This
theorem is the machine-checked form of that finding: it proves the
OLD STATEMENT (which is thereby shown to express nothing), not
reconstruction. Superseded by `OSReconstructionStatement` (§3). -/
theorem oldPin_osReconstruction_trivial : OSReconstruction :=
  fun _ => ⟨⟨⟨PUnit⟩, True, True, True, True, True, True, True⟩, trivial⟩

/-- **CORRECTION (T1): the old pin's `InteractingOSMeasure` is
vacuous.** Stated as `∃ _ : OsterwalderSchraderAxioms, True`, it is
proved by the all-`True` bundle; it never expressed the existence
of a non-Gaussian OS measure. This theorem proves the OLD
STATEMENT and thereby its emptiness — it constructs no measure.
Superseded by `InteractingOSMeasureStatement` (§3). -/
theorem oldPin_interactingOSMeasure_trivial : InteractingOSMeasure :=
  ⟨⟨⟨PUnit⟩, True, True, True, True, True⟩, trivial⟩

/-- **CORRECTION (T1, sibling file): `InteractingWightmanQFT` in
`WightmanAxioms.lean` has the same vacuous shape**
(`∃ _ : WightmanAxioms, True` over an all-`Prop` bundle) and is
likewise provable from the all-`True` instantiation. Recorded here
because the OS reconstruction target lives in that file; that
file's own re-pin is a separate brick, not this one. This theorem
proves the OLD STATEMENT, not any QFT. -/
theorem oldPin_interactingWightmanQFT_trivial : InteractingWightmanQFT :=
  ⟨⟨⟨PUnit⟩, True, True, True, True, True, True, True⟩, trivial⟩

/-! ## §2. The re-pinned Schwinger data, and E0 as the type (T1 statements)

Test functions on `n` Euclidean points are Schwartz functions on
`Fin n × Fin 4 → ℝ` (a point is a pair: point index, coordinate).
The index type is a `4n`-element fintype with the sup norm, linearly
isometric to the corpus's flat `SchwartzTest (4 * n)` convention of
`ThetLogos.SchwartzSpace`; the pair indexing is used here because
E1–E4 act on points and coordinates separately. -/

/-- Test functions on `n` Euclidean points: `𝓢(ℝ⁴ⁿ, ℂ)` with
pair-indexed points. -/
abbrev EucTest (n : ℕ) := 𝓢(Fin n × Fin 4 → ℝ, ℂ)

/-- The `n`-point Schwinger function as a genuine object: a tempered
distribution on `ℝ⁴ⁿ`. This discharges the old pin's opaque
`SchwingerMarker` — the pinned Mathlib ships `𝓢'` with Fourier
theory (`Mathlib/Analysis/Distribution/TemperedDistribution.lean`),
and Rung 6 already built on it. -/
abbrev SchwingerDist (n : ℕ) := 𝓢'(Fin n × Fin 4 → ℝ, ℂ)

/-- **E0 (temperedness), glue 1 of 3:** a Schwinger distribution is
continuous as a function of the test function. In the old pin,
`temperedness` was an unconstrained `Prop` field — it could be
`False`. Here temperedness is the type: `𝓢'` is by definition the
continuous linear dual of `𝓢`, and this theorem makes the
continuity explicit rather than definitional folklore. -/
theorem schwingerDist_continuous (n : ℕ) (S : SchwingerDist n) :
    Continuous (fun f : EucTest n => S f) := S.continuous

/-- **E0, glue 2 of 3:** additivity of the pairing (linearity of
the distribution, made explicit). -/
theorem schwingerDist_add (n : ℕ) (S : SchwingerDist n)
    (f g : EucTest n) : S (f + g) = S f + S g := map_add S f g

/-- **E0, glue 3 of 3:** homogeneity of the pairing. Together with
continuity, these are exactly the statement that `S n` is a
tempered distribution — the growth content of OS73's E0 is the
continuity with respect to the Schwartz seminorm family, which is
the definition of the type `𝓢'`. -/
theorem schwingerDist_smul (n : ℕ) (S : SchwingerDist n)
    (c : ℂ) (f : EucTest n) : S (c • f) = c • S f := map_smul S c f

/-! ### Coordinate operations used by E1–E4 (plain functions)

All transformations are written at the level of coordinate tuples
`Fin n × Fin 4 → ℝ`. The axiom fields in §3 quantify over Schwartz
functions `F'` whose underlying function equals a transformed `F`;
no composition machinery for `𝓢` is needed to *state* the axioms,
and no membership claim is hidden: the quantification itself is
the statement. -/

/-- First block of coordinates: points `0, …, n-1` of an `(n+m)`-tuple. -/
def firstBlock {n m : ℕ} (z : Fin (n + m) × Fin 4 → ℝ) :
    Fin n × Fin 4 → ℝ :=
  fun p => z (Fin.castAdd m p.1, p.2)

/-- Second block of coordinates: points `n, …, n+m-1` of an `(n+m)`-tuple. -/
def secondBlock {n m : ℕ} (z : Fin (n + m) × Fin 4 → ℝ) :
    Fin m × Fin 4 → ℝ :=
  fun p => z (Fin.natAdd n p.1, p.2)

/-- The first block with its time coordinates (coordinate `0` of
each point) reflected — the coordinate-level shadow of the OS
reflection `θ`, used in E2. -/
def reflFirst {n m : ℕ} (z : Fin (n + m) × Fin 4 → ℝ) :
    Fin n × Fin 4 → ℝ :=
  fun p => if p.2 = 0 then - firstBlock z p else firstBlock z p

/-- A Euclidean motion applied diagonally to every point of a
tuple: linear part `R` on each point's coordinates, then
translation by `b`. -/
def euclidMotion {n : ℕ} (R : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))
    (b : Fin 4 → ℝ) (x : Fin n × Fin 4 → ℝ) : Fin n × Fin 4 → ℝ :=
  fun p => R (fun c => x (p.1, c)) p.2 + b p.2

/-- Orthogonality of a linear map on `ℝ⁴`, stated against the
standard dot product: `R` preserves all pairwise inner products.
This is `O(4)`, reflections included. -/
def IsOrthogonal (R : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) : Prop :=
  ∀ x y : Fin 4 → ℝ, (∑ c, R x c * R y c) = ∑ c, x c * y c

/-- Support in the strict positive-time half-space: a test
function is supported where **every** point has positive time
coordinate. This is the support hypothesis of OS reflection
positivity (the algebra of positive-time test functions). -/
def InPositiveTime {n : ℕ} (f : EucTest n) : Prop :=
  ∀ x : Fin n × Fin 4 → ℝ, f x ≠ 0 → ∀ i : Fin n, 0 < x (i, 0)

/-! ## §3. The re-pinned bundle E0–E4 (T1 statements, T5 subject matter)

Every field below is a fully quantified statement about the data
`S`. Contrast the old pin: five unconstrained `Prop`s, any of
which could be `False` (bundle uninhabitable at whim) or `True`
(bundle inhabited with no content) — §1's corrections. Here E0 has
no field at all: it is the type of `S` (§2). -/

/-- **The Osterwalder–Schrader axioms, re-pinned** on genuine
tempered distributions (OS 1973/75, E0–E4). A structure of *data
plus real conditions*, not of opaque `Prop`s. No inhabitant is
asserted or proved in this file. -/
structure OSBundle where
  /-- The Schwinger functions: one tempered distribution per
      point count. E0 (temperedness) is this field's type. -/
  S : (n : ℕ) → SchwingerDist n
  /-- Vacuum normalization: the 0-point function is evaluation at
      the unique point of the empty tuple — `S₀ = 1` as a
      distribution. -/
  vacuumNormalization : ∀ f : EucTest 0, S 0 f = f 0
  /-- **E1: Euclidean covariance.** For every orthogonal `R` and
      translation `b`, the value of `S n` on a test function is
      unchanged when the test function is pulled back along the
      diagonal Euclidean motion. -/
  euclideanCovariant : ∀ (n : ℕ) (R : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)),
    IsOrthogonal R → ∀ (b : Fin 4 → ℝ) (F F' : EucTest n),
    (∀ x, F' x = F (euclidMotion R b x)) → S n F' = S n F
  /-- **E2: reflection (OS) positivity.** For every finite family
      of positive-time test functions `F i`, and every family
      `G i j` factoring — as a plain function — as the
      reflected-conjugate of `F i` on the first block times
      `F j` on the second, the double sum
      `∑ i j, S (nᵢ + nⱼ) (G i j)` is a nonnegative real number. -/
  reflectionPositive : ∀ (k : ℕ) (ns : Fin k → ℕ)
    (F : (i : Fin k) → EucTest (ns i)), (∀ i, InPositiveTime (F i)) →
    ∀ (G : (i j : Fin k) → EucTest (ns i + ns j)),
    (∀ i j (z : Fin (ns i + ns j) × Fin 4 → ℝ),
      G i j z = (starRingEnd ℂ) (F i (reflFirst z)) * F j (secondBlock z)) →
    ∃ r : ℝ, 0 ≤ r ∧ (∑ i, ∑ j, S (ns i + ns j) (G i j)) = r
  /-- **E3: permutation symmetry.** The value of `S n` is
      unchanged when the points of the test function are permuted. -/
  symmetric : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (F F' : EucTest n),
    (∀ x, F' x = F (fun p => x (σ p.1, p.2))) → S n F' = S n F
  /-- **E4: clustering.** When the second factor of a factorized
      test function is translated away in the time direction
      (separation `T → ∞`), the `(n+m)`-point function converges
      to the product of the factors' functions. Factorization and
      translation are at the level of plain functions, as in E2. -/
  clustering : ∀ (n m : ℕ) (f : EucTest n) (g : EucTest m)
    (F : ℝ → EucTest (n + m)),
    (∀ (T : ℝ) (z : Fin (n + m) × Fin 4 → ℝ),
      F T z = f (firstBlock z)
        * g (fun p => secondBlock z p + (if p.2 = 0 then T else 0))) →
    Filter.Tendsto (fun T : ℝ => S (n + m) (F T)) Filter.atTop
      (nhds (S n f * S m g))

/-- **Non-Gaussianity**, in Wick-defect form: for some one-point
test function `f`, the two-point pairing on `f ⊗ f` is nonzero,
and the four-point pairing on `f ⊗ f ⊗ f ⊗ f` differs from the
Gaussian (Wick) value `3 · (S₂ (f⊗f))²`. The tensor factors are
pinned by plain-function factorization identities, as in E2/E4.
This is the "non-trivial" content the old pin's
`InteractingOSMeasure` gestured at with `∃ _, True`. -/
def NonGaussian (S : (n : ℕ) → SchwingerDist n) : Prop :=
  ∃ (f : EucTest 1) (F₂ : EucTest 2) (F₄ : EucTest 4),
    (∀ z, F₂ z = f (fun p => z ((0 : Fin 2), p.2))
        * f (fun p => z ((1 : Fin 2), p.2))) ∧
    (∀ z, F₄ z = f (fun p => z ((0 : Fin 4), p.2))
        * f (fun p => z ((1 : Fin 4), p.2))
        * f (fun p => z ((2 : Fin 4), p.2))
        * f (fun p => z ((3 : Fin 4), p.2))) ∧
    S 2 F₂ ≠ 0 ∧ S 4 F₄ ≠ 3 * (S 2 F₂) ^ 2

/-- **An interacting OS measure exists** — the re-pinned form of
the old pin's vacuous `InteractingOSMeasure`: a full OS bundle
whose Schwinger functions are non-Gaussian. This is a real Prop,
currently unproved; it is the Euclidean face of the constructive
existence problem. **Not claimed.** (Compare §1: the old form is
a theorem, because it says nothing.) -/
def InteractingOSMeasureStatement : Prop :=
  ∃ B : OSBundle, NonGaussian B.S

/-- **The OS reconstruction theorem, re-pinned as a schema.**
The 1973/75 theorem (OS axioms ⇒ Wightman axioms) has exactly two
analytic content-holes, and this statement names both as
parameters instead of hiding them:
`IsBoundaryValueOf S W` — "`W` arises from `S` by analytic
continuation to the extended tube and boundary values in the
Minkowski region" (Bargmann–Hall–Wightman + edge-of-the-wedge;
absent from the pinned Mathlib — see the dossier's dependency
audit), and `SatisfiesWightman W` — the Wightman-side conditions
on the reconstructed distributions (the sibling pin
`WightmanAxioms.lean`'s own re-pin, a separate brick).
Everything around the two holes — the quantifier shape, the
types, the data — is now real. No instantiation of the parameters
is given or claimed here; a fortiori **no reconstruction is
proved, and PARTIAL-δ is not claimed.** -/
def OSReconstructionStatement
    (IsBoundaryValueOf : ((n : ℕ) → SchwingerDist n) →
      ((n : ℕ) → SchwingerDist n) → Prop)
    (SatisfiesWightman : ((n : ℕ) → SchwingerDist n) → Prop) :
    Prop :=
  ∀ B : OSBundle, ∃ W : (n : ℕ) → SchwingerDist n,
    IsBoundaryValueOf B.S W ∧ SatisfiesWightman W

/-! ## §4. Lattice citations (T1): what the standing lattice package
discharges, clause by clause

Each theorem below restates a clause-level fact and proves it by
the standing theorem itself (module named in each docstring). The
full clause table — including the clauses with **no** discharge —
is in the dossier. Nothing in this section is a continuum
statement: every object is a finite lattice at fixed spacing and
volume. -/

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N] (μG : Measure G) [IsProbabilityMeasure μG]
  [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]

/-- **E2 input (Stage 1b-A, `LatticeReflection`):** the Gibbs
measure is invariant under the between-sites configuration
reflection, in strong `Measure.map` form, at **every** real `β`
and every even `N`. This is the measure-level half of lattice
reflection positivity; the form-level half is 1b-B, below. -/
theorem lattice_reflection_gibbs_invariant
    (hρcont : Continuous fun g => repMatrix ρ g) (hN : Even N) (β : ℝ) :
    Measure.map reflConfig (gibbsMeasure (torusShift N) μG ρ β)
      = gibbsMeasure (torusShift N) μG ρ β :=
  gibbsMeasure_map_reflConfig ρ μG hρcont hN β

/-- **E2 at `β = 0` (Stage 1b-B, `LatticePositivity`):** the OS
form's diagonal at `β = 0` is a squared norm — nonnegative real
part, zero imaginary part — for every observable factoring
through the strict positive half. Positivity at `β = 0` STANDS. -/
theorem lattice_osForm_zero_nonneg (hN : Even N)
    (F : Config (Fin 4 → ZMod N) G → ℂ)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (hF : ∀ U, F U = f (fun ℓ : ↥(posLinks (N := N)) => U ℓ.1)) :
    0 ≤ (osForm μG ρ 0 F F).re ∧ (osForm μG ρ 0 F F).im = 0 :=
  osForm_zero_nonneg μG ρ hN F f hF

/-- **E2 at general `β`, conditional (Stage 1b-B,
`LatticePositivity`):** IF the crossing Boltzmann weight is a
finite Gram sum over the strict half (`hgram`), THEN the OS
form's diagonal is nonnegative at that `β`. The criterion STANDS
as a theorem; the hypothesis `hgram` at general `(G, ρ)` is
**1b-B's open clause** — its standard proof needs the
character expansion / Peter–Weyl orthogonality for general
compact groups, absent from the pinned Mathlib, priced
**XL / Mathlib-blocked**. This wrapper cites the criterion; it
does not discharge the hypothesis. -/
theorem lattice_osForm_gram_criterion
    (hρcont : Continuous fun g => repMatrix ρ g) (hN : Even N)
    (hd : 0 < d) (β : ℝ)
    (F : Config (Fin 4 → ZMod N) G → ℂ)
    (f : (↥(posLinks (N := N)) → G) → ℂ)
    (hF : ∀ U, F U = f (fun ℓ : ↥(posLinks (N := N)) => U ℓ.1))
    (hfA : AEStronglyMeasurable f
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (Cf : ℝ) (hfB : ∀ z, ‖f z‖ ≤ Cf)
    {ι : Type*} [Fintype ι]
    (Ξ : ι → (↥(posLinks (N := N)) → G) → ℂ)
    (hΞA : ∀ i, AEStronglyMeasurable (Ξ i)
      (Measure.pi fun _ : ↥(posLinks (N := N)) => μG))
    (CΞ : ℝ) (hΞB : ∀ i z, ‖Ξ i z‖ ≤ CΞ)
    (hgram : ∀ (y : ↥(halfLinks (N := N)) → G)
      (u : ↥(negLinks (N := N)) → G),
      (Real.exp (- wilsonAction (torusShift N) ρ β
        ((splitEquiv (halfLinks (N := N))).symm (y, u))) : ℂ)
      = ∑ i, (starRingEnd ℂ) (Ξ i (mirrorP hN u))
          * Ξ i (restrictPos y)) :
    0 ≤ (osForm μG ρ β F F).re ∧ (osForm μG ρ β F F).im = 0 :=
  osForm_nonneg_of_gram μG ρ hρcont hN hd β F f hF hfA Cf hfB Ξ hΞA
    CΞ hΞB hgram

/-- **Reconstruction output, lattice shadow (Stage 1b-C,
`LatticeOSSpace`):** the OS Hilbert space of the finite theory
exists (`osSpace β = Lp ℂ 2 (sliceMeasure β)`), and its vacuum —
the constant-`1` vector — has norm exactly `1`, at every `β`. -/
theorem lattice_osVacuum_norm_one
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d) (β : ℝ) :
    ‖osVacuum (N := N) μG ρ hρcont hd β‖ = 1 :=
  norm_osVacuum μG ρ hρcont hd β

/-- **Dynamics on the OS space (Stage 1b-D, `LatticeTransfer`):**
the one-step transfer operator is a contraction, `‖T_β‖ ≤ 1`, at
every real `β`. -/
theorem lattice_transfer_contraction (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (β : ℝ) :
    ‖transferOp μG ρ hN2 hρcont β‖ ≤ 1 :=
  transferOp_norm_le μG ρ hN2 hρcont β

/-- **Dynamics (Stage 1b-D):** the transfer operator fixes the
vacuum, `T_β Ω = Ω`, at every real `β` — stationarity of the
Gibbs measure as an operator identity. -/
theorem lattice_transfer_vacuum_fixed (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d) (β : ℝ) :
    transferOp μG ρ hN2 hρcont β (osVacuum (N := N) μG ρ hρcont hd β)
      = osVacuum (N := N) μG ρ hρcont hd β :=
  transferOp_vacuum μG ρ hN2 hρcont hd β

/-- **Dynamics at `β = 0` (Stage 1b-D):** `T₀` is exactly the
vacuum projection, `T₀ f = ⟪Ω, f⟫ • Ω`; hence the lattice gap at
`β = 0` is exactly `1`. (A lattice statement at `β = 0` only;
general-`β` gap and uniformity are Stage 3, not claimed.) -/
theorem lattice_transfer_zero_projection (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g => repMatrix ρ g) (hd : 0 < d)
    (f : ↥(osSpace (N := N) μG ρ 0)) :
    transferOp μG ρ hN2 hρcont 0 f
      = inner ℂ (osVacuum (N := N) μG ρ hρcont hd 0) f
        • osVacuum (N := N) μG ρ hρcont hd 0 :=
  transferOp_zero_apply μG ρ hN2 hρcont hd f

section GeneralLattice

variable {Λ : Type*} [Fintype Λ] {H : Type*} [Group H]
  [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] [SecondCountableTopology H]
  (σ : Fin 4 → Equiv.Perm Λ)
  (μH : Measure H) [IsProbabilityMeasure μH] [μH.IsMulLeftInvariant]
  [μH.IsMulRightInvariant] [μH.IsInvInvariant] {d' : ℕ}
  (ρ' : H →* ↥(Matrix.unitaryGroup (Fin d') ℂ))

/-- **E0 shadow at finite volume (Stage 1a, `LatticeCorrelations`):**
the lattice Schwinger data are expectations against a genuine
probability measure at every real `β` — at finite volume there is
no growth/temperedness question to ask; continuum E0 is a
property of the limit (Stage 3a's target), not of any finite
stage. This wrapper records the finite-level fact the limit
would have to preserve. -/
theorem lattice_gibbsMeasure_probability
    (hρcont : Continuous fun g => repMatrix ρ' g) (hd : 0 < d') (β : ℝ) :
    IsProbabilityMeasure (gibbsMeasure σ μH ρ' β) :=
  isProbabilityMeasure_gibbsMeasure σ μH ρ' hρcont hd β

/-- **E4 shadow at `β = 0` (Stage 1a, `LatticeCorrelations`):**
exact factorization of the two-point expectation over
disjointly-supported observables at `β = 0` — the free point's
clustering, proved hypothesis-free beyond disjointness. General-`β`
clustering/decay is **not** standing: it is Stage 3 content
(uniform estimates), and this citation must not be read as decay
at any `β ≠ 0`. -/
theorem lattice_beta0_factorization [DecidableEq Λ]
    (F H' : Config Λ H → ℂ) (s₁ s₂ : Finset (Link Λ))
    (hdisj : Disjoint s₁ s₂) (hF : DependsOnlyOn F s₁)
    (hH : DependsOnlyOn H' s₂) :
    gibbsExpect σ μH ρ' 0 (fun U => F U * H' U)
      = gibbsExpect σ μH ρ' 0 F * gibbsExpect σ μH ρ' 0 H' :=
  gibbsExpect_zero_mul_of_disjoint σ μH ρ' F H' s₁ s₂ hdisj hF hH

end GeneralLattice

end ThetLogos
