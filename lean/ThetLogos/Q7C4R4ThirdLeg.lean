import Mathlib.Tactic
import ThetLogos.Q7C4R4Trifecta
import ThetLogos.Q7C4R4Spectrum
import ThetLogos.FiniteEntropy

namespace ThetLogos

/-!
# ThetLogos.Q7C4R4ThirdLeg — T-R4-2: the Third-leg ground-degeneracy test

**Status: TEST EXECUTED — K-T-R4-2 FIRES (seat-scoped, at both
seats named by the registration's memo). NO CLAIM. Dials 0/4.
No measured number.** Governing pack:
`routeb-general-scratch/pack-t-r4-2.md`; registration:
`ThetLogos.Q7C4R4Trifecta` (Q7CR-T0); spectral data: Q7CR-2's
`ThetLogos.Q7C4R4Spectrum`, consumed exactly (no data re-chosen).

## The registered Third statement, quoted verbatim

From `ThetLogos.Q7C4R4Trifecta` (definitions and docstrings):

```
def LegThirdFinite {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ → ℝ)
    (K : Matrix (Fin N) (Fin N) ℂ) (groundDeg : ℕ) : Prop :=
  Filter.Tendsto (fun β : ℝ => S (gibbsState K β)) Filter.atTop
    (nhds (Real.log (groundDeg : ℝ)))
```

> **Leg 4 — Third-Law finite form, as a schema** over a
> functional `S` and the Gibbs family of a stated operator `K`:
> `S (gibbsState K β)` tends, as `β → ∞`, to `Real.log` of `K`'s
> ground degeneracy (`groundDeg`, a variable: the degeneracy
> object and its certification are Q7CR-2's spectrum work).

```
def LegThirdFiniteStrong {N : ℕ}
    (S : Matrix (Fin N) (Fin N) ℂ → ℝ)
    (K : Matrix (Fin N) (Fin N) ℂ) (groundDeg : ℕ) : Prop :=
  (Filter.Tendsto (fun β : ℝ => S (gibbsState K β)) Filter.atTop
    (nhds 0)) ↔ groundDeg = 1
```

> **Leg 4 — the strong form, recorded as a schema beside the
> finite form:** the limit is `0` if and only if the ground space
> is one-dimensional (`groundDeg = 1`). Genuinely falsifiable per
> seat: at an operator with `groundDeg > 1` the strong form fails
> there and the leg survives only in the degeneracy form
> (`LegThirdFinite`), recorded at full rank.

The memo's T-R4-2 design (`scoping-q7c4r4-trifecta-2026-10-30.md`
§2.4 (ii), §4): "if the instantiated operator (the R⁴ factor's
`D_R` package, or the composite `D`) has a degenerate ground
space, the strong form *fails there* — limit `log deg > 0` — and
the leg survives only in the degeneracy form"; **K-T-R4-2:**
ground degeneracy > 1 at the instantiated operator ⇒ the strong
Third form dead *at that operator*; the degeneracy form stands
in its place.

## Which seat — read exactly

The registration's `K` is a VARIABLE; T0 §3 names what supplies
it: "`K` and `groundDeg` await Q7CR-2's certified spectrum."
The memo names the two instantiated operators Q7CR-2 certifies:
the R⁴ factor's `D_R` package (the leg's own factor seat,
primary here) and the composite `D` (corroboration). This brick
executes the degeneracy computation at BOTH, from the same
landed data, so the verdict does not depend on which of the two
the registration is read as naming: the count exceeds `1` at
both. The spectral object Q7CR-2 certifies is the SQUARE: the
factor square's site eigenvalues and the composite `D²`
eigenvalues (`eigComp`). Ground below means ground of the
square; at the factor seat the same two site vectors are also
the `0`-eigenvectors of `D_R` itself (§1).

## The deciding computations

- **Factor seat (§1).** Q7CR-2's chosen `r_R = (0, 2, -2, 0)`
  exactly, so `s_R = r_R² = (0, 4, 4, 0)`: the ground value `0`
  is attained at exactly TWO sites, `0` and `3`
  (`groundFiberR_card : groundDegR = 2`). The site basis vectors
  at `0` and `3` are linearly independent eigenvectors of
  `D_R²` (and of `D_R`) at eigenvalue `0`.
- **Composite seat (§2).** The minimum of `eigComp` is `1/64`
  (landed, `eigComp_ge` / `eigComp_min_attained`). Its fiber:
  `a₇² = 0` at 1 site (site `6`, 2 realified indices),
  `d₄² = 1/64` at 2 sites (rungs `1, 2`, 4 realified indices),
  `r_R² = 0` at 2 sites — 4 site triples, and the ground
  eigenspace of the composite `D²` has dimension exactly `16`
  in the landed realified basis (`groundDegComp = 16`), with
  linearly independent ground basis vectors exhibited.

## Verdict

**K-T-R4-2 FIRES: the ground degeneracy at the R⁴ factor seat
is `2 > 1` (and `16 > 1` at the composite seat), so the strong
Third form — limit `0` — is dead at those operators; the leg
survives only in the degeneracy form (`LegThirdFinite`, limit
`log 2` at the factor seat / `log 16` at the composite seat),
recorded at full rank.** The Zeroth leg (T-R4-1, contact
structure) is a different test — untouched here in either
direction. The assignment itself is Jeff's registered DATA;
this brick tests one leg's stated consequence only, and no
outcome here promotes the assignment to T1.
-/

/-! ## §1. The R⁴ factor seat: ground degeneracy of `D_R²` is 2 -/

/-- The R⁴ square eigenvalues at the two ground sites are `0`,
    and at the other two sites are `4` (from Q7CR-2's chosen
    `r_R = (0, 2, -2, 0)`, consumed exactly). Tier T1. -/
theorem s_R_ground_sites : s_R 0 = 0 ∧ s_R 3 = 0 ∧ s_R 1 = 4 ∧ s_R 2 = 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [s_R, r_R]

/-- The R⁴ diagonal entries at the ground sites are `0`. Tier T1. -/
theorem r_R_ground_sites : r_R 0 = 0 ∧ r_R 3 = 0 := by
  constructor <;> norm_num [r_R]

/-- The R⁴ factor operator's site eigenvectors: `D_R` acts on the
    site basis vector at `m` as the scalar `r_R m`. Tier T1. -/
theorem factorR_D_basis_eigen (m : Fin 4) :
    factorR.D ((Pi.basisFun ℝ (Fin 4)) m)
      = (r_R m) • (Pi.basisFun ℝ (Fin 4)) m := by
  funext j
  rw [factorR_D, diagOpR_apply, Pi.smul_apply, smul_eq_mul,
    Pi.basisFun_apply, Pi.single_apply]
  by_cases hj : j = m <;> simp [hj]

/-- The two ground site vectors are eigenvectors of `D_R` itself
    at eigenvalue `0`. Tier T1. -/
theorem factorR_D_ground_eigen :
    factorR.D ((Pi.basisFun ℝ (Fin 4)) 0) = 0 ∧
      factorR.D ((Pi.basisFun ℝ (Fin 4)) 3) = 0 := by
  obtain ⟨h0, h3⟩ := r_R_ground_sites
  constructor
  · rw [factorR_D_basis_eigen, h0, zero_smul]
  · rw [factorR_D_basis_eigen, h3, zero_smul]

/-- The two ground site vectors are eigenvectors of `D_R²` at
    eigenvalue `0` (the ground value of the factor square).
    Tier T1. -/
theorem factorR_D_sq_ground_eigen :
    (factorR.D ^ 2) ((Pi.basisFun ℝ (Fin 4)) 0) = 0 ∧
      (factorR.D ^ 2) ((Pi.basisFun ℝ (Fin 4)) 3) = 0 := by
  have h0 : (r_R 0) ^ 2 = 0 := s_R_ground_sites.1
  have h3 : (r_R 3) ^ 2 = 0 := s_R_ground_sites.2.1
  constructor
  · rw [factorR_basis_eigen, h0, zero_smul]
  · rw [factorR_basis_eigen, h3, zero_smul]

/-- The ground fiber of the R⁴ factor square: the sites where
    `s_R` attains its ground value `0`. Tier T1 (definition). -/
noncomputable def groundFiberR : Finset (Fin 4) :=
  Finset.univ.filter (fun m => s_R m = 0)

/-- **The factor ground degeneracy**: the cardinality of the
    ground fiber. Tier T1 (definition). -/
noncomputable def groundDegR : ℕ := groundFiberR.card

/-- The ground fiber is exactly `{0, 3}`. Tier T1. -/
theorem groundFiberR_eq : groundFiberR = {0, 3} := by
  ext m
  fin_cases m <;> simp [groundFiberR, s_R, r_R]

/-- **Factor ground count: `groundDegR = 2`.** Tier T1. -/
theorem groundDegR_eq : groundDegR = 2 := by
  rw [groundDegR, groundFiberR_eq]
  decide

/-- The embedding of the two ground sites into `Fin 4`. Tier T1. -/
def groundEmbR : Fin 2 → Fin 4 := ![0, 3]

/-- The ground-site embedding is injective (a `Fin` decidable
    fact). Tier T1. -/
theorem groundEmbR_injective : Function.Injective groundEmbR := by
  decide

/-- The exhibited ground vectors at the factor seat: the site
    basis vectors at sites `0` and `3`, indexed by `Fin 2`.
    Tier T1 (definition). -/
noncomputable def groundVecsR : Fin 2 → Minkowski :=
  fun i => (Pi.basisFun ℝ (Fin 4)) (groundEmbR i)

/-- The exhibited ground vectors are the site vectors at `0`
    and `3`. Tier T1. -/
theorem groundVecsR_values :
    groundVecsR 0 = (Pi.basisFun ℝ (Fin 4)) 0 ∧
      groundVecsR 1 = (Pi.basisFun ℝ (Fin 4)) 3 := by
  constructor <;> rfl

/-- **The exhibited factor ground vectors are linearly
    independent** (distinct vectors of the landed site basis), so
    the ground eigenspace of `D_R²` has dimension at least `2`.
    Tier T1. -/
theorem groundVecsR_linearIndependent :
    LinearIndependent ℝ groundVecsR :=
  (Pi.basisFun ℝ (Fin 4)).linearIndependent.comp groundEmbR
    groundEmbR_injective

/-- The diagonal entry at every embedded ground site is `0`.
    Tier T1. -/
theorem groundEmbR_r_R (i : Fin 2) : r_R (groundEmbR i) = 0 := by
  fin_cases i <;> norm_num [groundEmbR, r_R]

/-- Every exhibited factor ground vector is a `D_R²` eigenvector
    at the ground eigenvalue `0`. Tier T1. -/
theorem groundVecsR_eigen (i : Fin 2) :
    (factorR.D ^ 2) (groundVecsR i) = (0 : ℝ) • groundVecsR i := by
  show (factorR.D ^ 2) ((Pi.basisFun ℝ (Fin 4)) (groundEmbR i))
      = (0 : ℝ) • (Pi.basisFun ℝ (Fin 4)) (groundEmbR i)
  rw [factorR_basis_eigen, groundEmbR_r_R i]
  norm_num

/-! ## §2. The composite seat: ground degeneracy of `D²` is 16 -/

/-- The Q⁷ ground fiber in realified indices: where `s₇c`
    attains `0`. Tier T1 (definition). -/
noncomputable def groundFiberQ7 : Finset (Fin 7 × Fin 2) :=
  Finset.univ.filter (fun a => s₇c a = 0)

/-- The C⁴ ground fiber in realified indices: where `s₄c`
    attains its minimum `1 / 64`. Tier T1 (definition). -/
noncomputable def groundFiberC4 : Finset (Fin 4 × Fin 2) :=
  Finset.univ.filter (fun a => s₄c a = 1 / 64)

/-- The composite ground fiber: the indices where `eigComp`
    attains the composite ground value `1 / 64`. Tier T1
    (definition). -/
noncomputable def groundFiberComp : Finset compIndex :=
  Finset.univ.filter (fun t => eigComp t = 1 / 64)

/-- **The composite ground degeneracy**: the cardinality of the
    composite ground fiber — the dimension of the ground
    eigenspace of the composite `D²` in the landed basis.
    Tier T1 (definition). -/
noncomputable def groundDegComp : ℕ := groundFiberComp.card

/-- The Q⁷ ground fiber is exactly `{(6, 0), (6, 1)}`: site `6`
    (where `a₇ = 0`), both realified parts. Tier T1. -/
theorem groundFiberQ7_eq : groundFiberQ7 = {(6, 0), (6, 1)} := by
  ext ⟨k, b⟩
  fin_cases k <;> fin_cases b <;>
    simp [groundFiberQ7, s₇c_apply, a₇] <;> norm_num

/-- The Q⁷ ground fiber has `2` realified indices. Tier T1. -/
theorem groundFiberQ7_card : groundFiberQ7.card = 2 := by
  rw [groundFiberQ7_eq]
  decide

/-- The C⁴ ground fiber is exactly
    `{(1, 0), (1, 1), (2, 0), (2, 1)}`: rungs `1, 2` (where
    `d₄² = 1 / 64`), both realified parts. Tier T1. -/
theorem groundFiberC4_eq :
    groundFiberC4 = {(1, 0), (1, 1), (2, 0), (2, 1)} := by
  ext ⟨k, b⟩
  fin_cases k <;> fin_cases b <;>
    simp [groundFiberC4, s₄c_apply] <;> norm_num [d₄, z4Energy]

/-- The C⁴ ground fiber has `4` realified indices. Tier T1. -/
theorem groundFiberC4_card : groundFiberC4.card = 4 := by
  rw [groundFiberC4_eq]
  decide

/-- **Ground-fiber characterization at the composite seat**: a
    composite eigenvalue equals the ground value `1 / 64` iff
    every factor sits at its own ground value — since each
    factor value is at least its ground value (`s₇c ≥ 0`,
    `s₄c ≥ 1 / 64`, `s_R ≥ 0`), the sum attains `1 / 64` only
    termwise. Tier T1. -/
theorem eigComp_eq_min_iff (t : compIndex) :
    eigComp t = 1 / 64 ↔
      s₇c t.1.1 = 0 ∧ s₄c t.1.2 = 1 / 64 ∧ s_R t.2 = 0 := by
  have h1 := s₇c_nonneg t.1.1
  have h2 := s₄c_ge t.1.2
  have h3 := s_R_nonneg t.2
  constructor
  · intro h
    have hsum : eigComp t = s₇c t.1.1 + s₄c t.1.2 + s_R t.2 := rfl
    rw [hsum] at h
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h7, h4, hR⟩
    show s₇c t.1.1 + s₄c t.1.2 + s_R t.2 = 1 / 64
    rw [h7, h4, hR]
    norm_num

/-- The composite ground fiber is the product of the three
    factor ground fibers. Tier T1. -/
theorem groundFiberComp_eq :
    groundFiberComp
      = (groundFiberQ7 ×ˢ groundFiberC4) ×ˢ groundFiberR := by
  ext ⟨⟨a, b⟩, m⟩
  simp only [groundFiberComp, groundFiberQ7, groundFiberC4,
    groundFiberR, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_product]
  rw [eigComp_eq_min_iff]
  tauto

/-- **Composite ground count: `groundDegComp = 16`** — `2`
    (Q⁷ realified ground indices) × `4` (C⁴ realified ground
    indices) × `2` (R⁴ ground sites); in site terms, the `4`
    site triples `(6, 1|2, 0|3)`, each contributing `4`
    realified basis vectors. Tier T1. -/
theorem groundDegComp_eq : groundDegComp = 16 := by
  have hR : groundFiberR.card = 2 := groundDegR_eq
  rw [groundDegComp, groundFiberComp_eq, Finset.card_product,
    Finset.card_product, groundFiberQ7_card, groundFiberC4_card, hR]

/-! ## §3. Exhibited composite ground vectors, and the kill -/

/-- The first exhibited composite ground index: Q⁷ site `6`,
    C⁴ rung `1`, R⁴ site `0`. Tier T1 (definition). -/
def groundIdxA : compIndex := (((6, 0), (1, 0)), 0)

/-- The second exhibited composite ground index: Q⁷ site `6`,
    C⁴ rung `1`, R⁴ site `3` — the other R⁴ ground site.
    Tier T1 (definition). -/
def groundIdxB : compIndex := (((6, 0), (1, 0)), 3)

/-- The second exhibited index is also at the ground value
    `1 / 64`. Tier T1. -/
theorem eigComp_groundIdxB : eigComp groundIdxB = 1 / 64 := by
  show s₇c (6, 0) + s₄c (1, 0) + s_R 3 = 1 / 64
  rw [s₇c_apply, s₄c_apply]
  norm_num [a₇, d₄, z4Energy, s_R, r_R]

/-- The first exhibited index is at the ground value `1 / 64`
    (the landed attainment, restated at this brick's name).
    Tier T1. -/
theorem eigComp_groundIdxA : eigComp groundIdxA = 1 / 64 :=
  eigComp_min_attained

/-- The exhibited composite ground vectors: the landed composite
    basis vectors at the two exhibited ground indices.
    Tier T1 (definition). -/
noncomputable def groundVecsComp : Fin 2 → q7c4r4Composite :=
  fun i => basisComp (![groundIdxA, groundIdxB] i)

/-- The exhibited composite ground vectors are the basis vectors
    at `groundIdxA` and `groundIdxB`. Tier T1. -/
theorem groundVecsComp_values :
    groundVecsComp 0 = basisComp groundIdxA ∧
      groundVecsComp 1 = basisComp groundIdxB := by
  constructor <;> rfl

/-- The two exhibited composite ground indices are distinct
    (a `Fin` decidable fact). Tier T1. -/
theorem groundIdxA_ne_groundIdxB : groundIdxA ≠ groundIdxB := by
  decide

/-- **The exhibited composite ground vectors are linearly
    independent** (distinct vectors of the landed composite
    basis), so the ground eigenspace of the composite `D²` has
    dimension at least `2` — its exact dimension is `16`
    (`groundDegComp_eq`). Tier T1. -/
theorem groundVecsComp_linearIndependent :
    LinearIndependent ℝ groundVecsComp := by
  have hinj : Function.Injective
      (![groundIdxA, groundIdxB] : Fin 2 → compIndex) := by
    decide
  exact basisComp.linearIndependent.comp _ hinj

/-- The first exhibited composite ground vector is a composite
    `D²` eigenvector at the ground eigenvalue `1 / 64`. Tier T1. -/
theorem dirac_sq_groundIdxA_eigen :
    ((diracQ7C4R4 factorQ7 factorC4 factorR) ^ 2)
        (basisComp groundIdxA)
      = (1 / 64 : ℝ) • basisComp groundIdxA := by
  rw [dirac_sq_basisComp_eig, eigComp_groundIdxA]

/-- The second exhibited composite ground vector is a composite
    `D²` eigenvector at the ground eigenvalue `1 / 64`. Tier T1. -/
theorem dirac_sq_groundIdxB_eigen :
    ((diracQ7C4R4 factorQ7 factorC4 factorR) ^ 2)
        (basisComp groundIdxB)
      = (1 / 64 : ℝ) • basisComp groundIdxB := by
  rw [dirac_sq_basisComp_eig, eigComp_groundIdxB]

/-! ## §4. The kill, stated at both seats -/

/-- The finite form's limit value at the factor seat,
    `log groundDegR = log 2`, is not `0`. Tier T1. -/
theorem log_groundDegR_ne_zero : Real.log (groundDegR : ℝ) ≠ 0 := by
  rw [groundDegR_eq]
  have h : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  exact ne_of_gt (by push_cast; exact h)

/-- The finite form's limit value at the composite seat,
    `log groundDegComp = log 16`, is not `0`. Tier T1. -/
theorem log_groundDegComp_ne_zero :
    Real.log (groundDegComp : ℝ) ≠ 0 := by
  rw [groundDegComp_eq]
  have h : (0 : ℝ) < Real.log 16 := Real.log_pos (by norm_num)
  exact ne_of_gt (by push_cast; exact h)

/-- **Strong-limit exclusion at the factor degeneracy value**:
    wherever the registered finite form `LegThirdFinite` holds
    with `groundDeg = groundDegR = 2`, the strong form's
    limit-`0` statement is false — the two limits would have to
    agree, and `log 2 ≠ 0`. Tier T1. -/
theorem strong_limit_zero_excluded_of_finite {N : ℕ}
    (S : Matrix (Fin N) (Fin N) ℂ → ℝ)
    (K : Matrix (Fin N) (Fin N) ℂ)
    (hfin : LegThirdFinite S K groundDegR) :
    ¬ Filter.Tendsto (fun β : ℝ => S (gibbsState K β)) Filter.atTop
        (nhds 0) := by
  intro h0
  have huniq := tendsto_nhds_unique hfin h0
  exact log_groundDegR_ne_zero huniq

/-- **K-T-R4-2 FIRES, at both seats named by the registration's
    memo.** The ground degeneracy of the R⁴ factor square is
    `2 ≠ 1`, and of the composite square is `16 ≠ 1`: the
    strong Third form (limit `0`) is dead at those operators,
    and the leg survives there only in the degeneracy form
    (`LegThirdFinite`, with limit `log 2` resp. `log 16`).
    Tier T1. -/
theorem k_t_r4_2_fires :
    groundDegR = 2 ∧ groundDegComp = 16 ∧
      groundDegR ≠ 1 ∧ groundDegComp ≠ 1 ∧
      Real.log (groundDegR : ℝ) ≠ 0 ∧
      Real.log (groundDegComp : ℝ) ≠ 0 :=
  ⟨groundDegR_eq, groundDegComp_eq, by rw [groundDegR_eq]; norm_num,
    by rw [groundDegComp_eq]; norm_num, log_groundDegR_ne_zero,
    log_groundDegComp_ne_zero⟩

end ThetLogos
