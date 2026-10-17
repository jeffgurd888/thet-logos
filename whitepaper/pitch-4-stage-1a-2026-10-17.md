# Pitch 4, Stage 1a — lattice correlation functions + the Elitzur theorem

**Date:** 2026-10-17. **Module:** `lean/ThetLogos/LatticeCorrelations.lean`
(1,667 lines; imports `ThetLogos.LatticeGauge`).
**Tier:** T1 at the finite-lattice level, throughout.
**Status: STANDS WHOLE** — every scoped item landed, including the
general-(G, ρ) Elitzur headline; the one pre-authorized narrowing
(instance-level Elitzur) was **not** needed.
**Pitch-level shape after this landing: PARTIAL-β** (scoping §8:
Stages 0 + 1a stand; 1b priced, 1c priced).
**Parts of the official Clay Yang–Mills statement closed by this
module: 0.**

Governing spec: §6.2 sub-stage 1a of
`whitepaper/pitch-4-continuum-scoping-DRAFT-2026-10-17.md`, under §8's
five mandatory clauses, all carried verbatim in the module header.

## 1. Scoped vs landed, per item

**Item 1 — the Gibbs probability measure. STANDS.**
`gibbsMeasure σ μG ρ β` is constructed as
`Z⁻¹ • (configMeasure μG).withDensity gibbsDensity`, with
`gibbsDensity U = ⟨exp(−S_β U), _⟩ : ℝ≥0` and
`Z = gibbsPartition σ μG ρ β` (Stage 0's denominator, named).
`isProbabilityMeasure_gibbsMeasure` proves it is a probability
measure for **every real β** (stronger than Stage 0's `0 ≤ β`
denominator positivity: `gibbsPartition_pos` uses Stage 0's
`|S_β| ≤ |β|·C` bound, so `exp(−S_β) ≥ exp(−|β|·C) > 0` pointwise).
The headline connection theorem **`gibbsExpect_eq_integral`** proves
Stage 0's ratio-of-integrals `gibbsExpect` *equal* to the Bochner
integral against this measure — no integrability hypothesis needed,
and no fallback to the ratio device was required: the measure
construction is what landed, ready for Stage 1b to consume.

**Item 2 — expectation algebra. STANDS.**
For Stage 0's ℂ-valued `gibbsExpect`: `⟨1⟩ = 1`
(`gibbsExpect_one`), `⟨c⟩ = c` (`gibbsExpect_const`), additivity
(`gibbsExpect_add`), constant scaling on both sides
(`gibbsExpect_const_mul`, `gibbsExpect_mul_const`), finite sums
(`gibbsExpect_finsetSum`), product observables (the product is an
observable by definition of the integrand), and the bound
`|⟨F⟩| ≤ ⟨|F|⟩` (`norm_gibbsExpect_le`, valued in the real
expectation). The real expectation `gibbsExpectR` is *defined* as the
Gibbs-measure integral and *proved* equal to the real ratio of
integrals (`gibbsExpectR_eq_ratio`); for it: constants, additivity,
subtraction, scaling, monotonicity (`gibbsExpectR_mono`: pointwise
`F ≤ H` ⇒ `⟨F⟩ ≤ ⟨H⟩`), nonnegativity preservation
(`gibbsExpectR_nonneg`), and the compatibility
`⟨(F : ℂ)⟩ = (⟨F⟩_ℝ : ℂ)` for real `F` (`gibbsExpect_ofReal`).
Integrability side conditions are discharged once, centrally:
bounded measurable observables on the Gibbs probability space are
integrable (`integrable_gibbsMeasure_of_bounded`).

**Item 3 — covariance package. STANDS.**
Real observables, `gibbsCov F H = ⟨F·H⟩ − ⟨F⟩⟨H⟩`,
`gibbsVar F = gibbsCov F F` (no conjugate — the real form, disclosed
in the header). Proved: symmetry (`gibbsCov_comm`), the centered
form (`gibbsCov_centered`), `var = ⟨(F − ⟨F⟩)²⟩`
(`gibbsVar_eq_centered_sq`), **`gibbsVar_nonneg`** (variance ≥ 0),
`cov(F, c) = 0` (`gibbsCov_const_right`), the scaling law
`var(F + tH)` expansion (`gibbsVar_add_smul`), and the
**Cauchy–Schwarz bound `gibbsCov_sq_le`**: `cov(F,H)² ≤ var(F)·var(H)`.
Route chosen: the elementary discriminant argument — `var(F + tH) ≥ 0`
for all `t` forces the discriminant inequality, isolated as the
standalone real lemma `sq_le_of_forall_quadratic_nonneg` — over the
Lp/L² inner-product machinery (either was allowed; the discriminant
route is self-contained and its lemma is independently checkable).

**Item 4 — ELIZTUR (the headline). STANDS AT GENERAL (G, ρ), EVERY β.**
The mechanism theorem `expectMatrix_eq_zero_of_left_covariant`: for
any measurable `Φ : Config Λ G → G` with the left-covariance identity
`Φ (U^{update 1 y h}) = h · Φ U` under site-`y`-supported gauge
transformations, the expectation matrix
`expectMatrix σ μG ρ β Φ` (entries `⟨(ρ (Φ U)) i j⟩`) is **zero**,
provided `ρ` has no nonzero fixed vectors
(`∀ v, (∀ g, ρ g *ᵥ v = v) → v = 0` — Stage 0's intertwiner criterion
in hypothesis form). Proof: invariance of the expectation under the
gauge transform (via `gibbsExpect_comp_gaugeAction`, itself from
Stage 0's integral invariance + action invariance) gives
`E = (ρ h) · E` for all `h`; hence every column of `E` is a
`ρ`-fixed vector, hence `0`. Corollaries:
`elitzur_single_link` (the insertion `U ↦ (ρ (U ℓ)) i j` vanishes at
every β, every link ℓ, whenever the shift moves the link's head
site); `elitzur_open_wilson_line` (the trace of the represented
ordered product along any **open** path — `loopEnd ≠ start` —
vanishes at every β); `elitzur_open_plaquette_path` (the open
three-link path of a plaquette is an open line, same vanishing);
and the concrete instances `elitzur_circle_torus`,
`elitzur_unitary_torus` on Stage 0's torus (for `2 ≤ N`).
**The contrast is proved, not gestured:** plaquette expectation
matrices are *intertwiners*, not vanishing subjects —
`expectMatrix_plaquette_intertwines` (`ρ h · E = E · ρ h` at every
β, via constant gauge transformations). The module never claims a
plaquette expectation vanishes at β ≠ 0 (at β = 0 it is Stage 0's
`tr P`, which is `0` exactly when `ρ` is fixed-vector-free).

**Item 5 — β = 0 factorization. STANDS, in a stronger form than
scoped.** The scoped form asked for `⟨F·H⟩₀ = ⟨F⟩₀·⟨H⟩₀` for
integrable `F, H` on disjoint supports. What landed:
`gibbsExpect_zero_mul_of_compl_dependsOnlyOn` (split form: `s`
versus `sᶜ`) and `gibbsExpect_zero_mul_of_disjoint`
(`DependsOnlyOn`-packaged disjoint form), over a general
product-measure core (`splitEquiv` / `measurePreserving_splitEquiv`:
the configuration space splits as `(↥s → G) × (↥sᶜ → G)` via
`MeasurableEquiv.piFinsetUnion` + the index transport
`↥(s ∪ sᶜ) ≃ ι`; `integral_pi_split_mul` is the Fubini step and
`integral_pi_restrict` the marginal). **The identities carry no
integrability hypotheses at all**: `MeasurePreserving.integral_comp`
and `integral_prod_mul` are unconditional, and by the Bochner
junk-value convention both sides agree (both `0`) for non-integrable
factors too. This is recorded in the module header (§0.3) so no
reader mistakes the missing hypotheses for an oversight.
**Nothing is asserted at β ≠ 0** — the section, its theorems, and
the module header all fence factorization to the free point.

**Item 6 — gauge-invariant correlations as objects. STANDS.**
`wilsonTwoPoint β C₁ C₂ := ⟨W_{C₁} · W_{C₂}⟩_β` is defined (§6 of
the module), with: symmetry (`wilsonTwoPoint_symm`); gauge
invariance of the integrand for two closed loops
(`wilsonTwoPoint_integrand_gauge_invariant`, from Stage 0's
`wilsonLoop_gauge_invariant`); the bound `|⟨W_{C₁}W_{C₂}⟩_β| ≤ d²`
at every β (`norm_wilsonTwoPoint_le`); β = 0 factorization for
disjointly supported loops (`wilsonTwoPoint_zero_of_disjoint`);
the connected correlator `wilsonTwoPointConnected` as a defined
object, with its β = 0 vanishing on disjoint supports
(`wilsonTwoPointConnected_zero_of_disjoint`) — the module's only
"clustering-shaped" statement, exact at the free point and fenced
as such. The §3 covariance package is applied to Wilson loops
verbatim via their real parts (`gibbsCov_wilsonLoop_re_sq_le`),
integrability discharged from the proved bound `|W_C| ≤ d`
(`norm_wilsonLoop_le`) and the path measurability proved in-module
(`measurable_loopProd_entry` by induction on the path,
`measurable_wilsonLoop`). Support is the finite link set
`loopLinks`, with `loopProd_eq_of_agree` and
`wilsonLoop_dependsOnlyOn` proving a loop reads only its support.
**No decay, clustering, or correlation-length claim is made at any
β** (Stage 1c, priced XL, untouched).

## 2. Devices and accommodations (plain terms)

1. **The Elitzur section needs a `DecidableEq Λ` instance**
   hypothesis (to form `Function.update` gauge transformations
   supported at one site). The torus sites `Fin 4 → ZMod N` have it
   by the standard Pi/`ZMod` instances; the hypothesis is disclosed
   in the module header (§0.3) and is the only hypothesis this
   campaign adds beyond Stage 0's.
2. **Elitzur is proved through the ratio device, then transported.**
   The invariance step (`gibbsExpect_comp_gaugeAction`) is proved
   directly on Stage 0's ratio-of-integrals `gibbsExpect` (Stage 0's
   `integral_gaugeAction` + `wilsonAction_gauge_invariant`), which
   by Item 1's connection theorem is the same expectation as the
   Gibbs-measure integral. No fork of Stage 0's devices anywhere:
   same `wilsonAction`, same `configMeasure`, same `gibbsExpect`,
   same plaquette/loop formalism, consumed unchanged.
3. **Covariance is real-only**, as scoped ("real-valued statements
   where the observable is real"). The ℂ two-point function and its
   connected form are defined in ℂ; the covariance *package*
   (variance, Cauchy–Schwarz) is applied to Wilson loops through
   their real parts, with a corollary saying exactly that.
4. **β = 0 factorization is unconditional** (see Item 5) — stronger
   than scoped, not narrower. The scope's integrability hypotheses
   turned out to be unnecessary; the dossier and header both say so
   rather than quietly keeping cosmetic hypotheses.
5. **The Gibbs measure uses an ℝ≥0-valued density** (not a bare
   real function), because Mathlib's
   `integral_withDensity_eq_integral_smul` consumes `ℝ≥0`-valued
   densities; `gibbsDensity_coe` records the coercion. A device
   detail, disclosed in the header.
6. **Not in the root import list.** Like every post-Rung-8 module,
   `LatticeCorrelations` is verified by targeted build and is *not*
   added to `ThetLogos.lean`'s imports; the header discloses this.

## 3. Counts (with method)

- `grep -c '^theorem '` on the module: **68 theorems** (0 lemmas —
  the file uses `theorem` throughout).
- `grep -cE '^(noncomputable )?def '`: **13 definitions**
  (`gibbsDensity`, `gibbsPartition`, `gibbsMeasure`, `gibbsExpectR`,
  `gibbsCov`, `gibbsVar`, `expectMatrix`, `finsetUnionComplEquiv`,
  `splitEquiv`, `DependsOnlyOn`, `loopLinks`, `wilsonTwoPoint`,
  `wilsonTwoPointConnected`). Total declarations: **81**.
- `wc -l`: **1,667 lines**.
- `grep -n 'sorry\|admit'`: **0 matches in the entire file,
  comments included** — zero `sorry`/`admit` in code, and the words
  do not occur in prose either.
- Program total: 2,148 + 68 = **2,216 theorems**.

## 4. Axiom checks

`#print axioms` on the five scoped headlines, each **exactly**
`[propext, Classical.choice, Quot.sound]`:

- `ThetLogos.gibbsExpect_eq_integral` ✓
- `ThetLogos.elitzur_single_link` ✓
- `ThetLogos.gibbsExpect_zero_mul_of_disjoint` ✓
- `ThetLogos.gibbsCov_sq_le` ✓
- `ThetLogos.gibbsVar_nonneg` ✓

## 5. Build

Targeted build, `lake build ThetLogos.LatticeCorrelations` in
`~/workspace/thet-logos/lean` (pinned Mathlib v4.35.0-rc3):
**Build completed successfully (3,391 jobs)**, `lake` exit 0, the
module's `.ole
...[truncated 1373 chars]