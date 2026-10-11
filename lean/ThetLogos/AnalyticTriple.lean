import ThetLogos.ProductTriple

namespace ThetLogos

/-!
# ThetLogos.AnalyticTriple — Rung 4 prep, Track A: the analytic triple (2026-10-10)

Rung 4 prep campaign, Track A (inner product — narrowed scope). Local-only;
nothing here pushes to public.

## What this file IS
- §1: `iprod` — the η-derived inner product `iprod x y = sesq (ηsym x) y`
  (T2 def on `TripleData`).
- §2: `AnalyticTripleData` — `TripleData` plus the analytic debt as T2
  class data: Krein-form symmetry (`hsesq_symm`), positivity
  (`hiprod_pos`), definiteness (`hiprod_def`), and antiunitarity of
  `Janti` (`hJanti_iprod`).
- §§3–7: the T1 consequences — sesquilinearity, `iprod_symm`,
  `iprod_eta`, Cauchy–Schwarz, and the norm `nrm` with `nrm_smul`,
  `nrm_eq_zero`, `nrm_triangle`.

## HONESTY NOTE
Positivity/definiteness of abstract class data cannot be *proved* from
nothing — they are properties, not theorems. "Genuine, not assumed" is met
by constructing the form from existing Krein data (`sesq`, `ηsym`) and
proving everything else; a concrete model (L², finite matrix triple) would
discharge `hiprod_pos`/`hiprod_def` — that is Rung 4 proper. The class is
named `AnalyticTripleData`, never "Hilbert": completeness is pinned, not
claimed (see the PIN below).

## Tier ledger
T2 (definitions/axioms): `iprod`, `AnalyticTripleData` (with
  `hsesq_symm`, `hiprod_pos`, `hiprod_def`, `hJanti_iprod`), `nrm`.
T1 (proved, zero sorrys): `iprod_add_left`, `iprod_add_right`,
  `iprod_smul_left`, `iprod_smul_right`, `iprod_sub_left`,
  `iprod_sub_right`, `iprod_zero_right`, `star_mul_self`, `star_re`,
  `re_le_norm`, `iprod_re_nonneg`, `iprod_symm`, `iprod_eta`,
  `cauchy_schwarz`, `nrm_smul`, `nrm_eq_zero`, `nrm_triangle`.

## Spec adaptations (this Mathlib, v4.35.0-rc3)
- `Complex.abs` no longer exists (removed in favor of `‖·‖`); the
  Cauchy–Schwarz statement uses `‖iprod x y‖ ^ 2`. `Complex.abs_sq` is
  likewise unavailable; the identity `star w * w = ‖w‖²` is proved as
  `star_mul_self` from `Complex.mul_conj` + `Complex.normSq_eq_norm_sq`.
- Cauchy–Schwarz scalar: the sketch's `c := iprod x y / r` does not
  telescope under the antilinear-first convention (the cross terms give
  `-2·Re(w²)/r`, not `-2·‖w‖²/r`); the proof uses
  `c := star (iprod x y) / r` (equivalently `iprod y x / r` by
  `iprod_symm`), which does telescope.
-/

-- ============================================================================
-- §1. The η-derived inner product (T2)
-- ============================================================================

/-- The η-derived inner product (Tier T2 — definition):
    `iprod x y = sesq (ηsym x) y`. Built from the existing Krein data —
    genuine, not assumed. Sesquilinear: antilinear in the first argument
    (from `sesq`'s `starRingEnd ℂ`-semilinearity), linear in the second;
    proved T1 in §3. -/
noncomputable def iprod [τ : TripleData] (x y : τ.S) : ℂ := τ.sesq (τ.ηsym x) y

-- ============================================================================
-- §2. The analytic triple (T2 class)
-- ============================================================================

/-- The analytic triple (Tier T2 class): `TripleData` plus the analytic
    debt, stated honestly as properties (see HONESTY NOTE above).
    - `hsesq_symm`: standard Krein-form symmetry, absent from Rung 3;
    - `hiprod_pos` / `hiprod_def`: positivity / definiteness — explicit
      analytic debt, dischargeable by a concrete model (Rung 4 proper);
    - `hJanti_iprod`: antiunitarity of `Janti` — standard, not derivable
      from the KO data. -/
class AnalyticTripleData extends TripleData where
  hsesq_symm : ∀ x y : S, sesq y x = star (sesq x y)
  hiprod_pos : ∀ x : S, ∃ r : ℝ, 0 ≤ r ∧ iprod x x = (r : ℂ)
  hiprod_def : ∀ x : S, iprod x x = 0 → x = 0
  hJanti_iprod : ∀ x y : S, iprod (Janti x) (Janti y) = star (iprod x y)

-- Projection instances: the class's instance-fields are not found by TC
-- automatically, so they are re-exported here (same pattern as
-- ProductTriple.lean).
instance AnalyticTripleData.instAddS [α : AnalyticTripleData] :
    AddCommGroup α.toTripleData.S := α.toTripleData.addS
instance AnalyticTripleData.instModS [α : AnalyticTripleData] :
    Module ℂ α.toTripleData.S := α.toTripleData.modS

variable [α : AnalyticTripleData]

-- ============================================================================
-- §3. Sesquilinearity of iprod (T1)
-- ============================================================================

/-- Additivity in the first argument (Tier T1 — proved): from `sesq`'s
    semilinearity and `ηsym`'s linearity. -/
theorem iprod_add_left (x₁ x₂ y : α.toTripleData.S) :
    iprod (x₁ + x₂) y = iprod x₁ y + iprod x₂ y := by
  simp only [iprod, map_add, LinearMap.add_apply]

/-- Additivity in the second argument (Tier T1 — proved). -/
theorem iprod_add_right (x y₁ y₂ : α.toTripleData.S) :
    iprod x (y₁ + y₂) = iprod x y₁ + iprod x y₂ := by
  simp only [iprod, map_add]

/-- Antilinearity in the first argument (Tier T1 — proved): from `sesq`'s
    `starRingEnd ℂ`-semilinearity and `ηsym`'s linearity. -/
theorem iprod_smul_left (c : ℂ) (x y : α.toTripleData.S) :
    iprod (c • x) y = star c * iprod x y := by
  simp only [iprod, map_smul, LinearMap.map_smulₛₗ, starRingEnd_apply,
    LinearMap.smul_apply, smul_eq_mul]

/-- Linearity in the second argument (Tier T1 — proved). -/
theorem iprod_smul_right (c : ℂ) (x y : α.toTripleData.S) :
    iprod x (c • y) = c * iprod x y := by
  simp only [iprod, map_smul, smul_eq_mul]

/-- Subtraction in the first argument (Tier T1 — proved). -/
theorem iprod_sub_left (x₁ x₂ y : α.toTripleData.S) :
    iprod (x₁ - x₂) y = iprod x₁ y - iprod x₂ y := by
  simp only [iprod, map_sub, LinearMap.sub_apply]

/-- Subtraction in the second argument (Tier T1 — proved). -/
theorem iprod_sub_right (x y₁ y₂ : α.toTripleData.S) :
    iprod x (y₁ - y₂) = iprod x y₁ - iprod x y₂ := by
  simp only [iprod, map_sub]

/-- `iprod x 0 = 0` (Tier T1 — proved). -/
theorem iprod_zero_right (x : α.toTripleData.S) : iprod x 0 = 0 := by
  have h : (0 : α.toTripleData.S) = (0 : ℂ) • x := (zero_smul _ _).symm
  rw [h, iprod_smul_right, zero_mul]

-- ============================================================================
-- §4. Complex-number helpers (T1)
-- ============================================================================

/-! Complex helpers don't use the `α` section variable. -/
omit α in
/-- `star w * w = ‖w‖²` as a complex number (Tier T1 — proved): from
    `Complex.mul_conj` and `Complex.normSq_eq_norm_sq`. (Stands in for the
    removed `Complex.abs_sq`.) -/
theorem star_mul_self (w : ℂ) : star w * w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : star w = (starRingEnd ℂ) w := congrFun Complex.star_def w
  rw [h1, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

omit α in
/-- `(star w).re = w.re` (Tier T1 — proved). -/
theorem star_re (w : ℂ) : (star w).re = w.re := by
  have h1 : star w = (starRingEnd ℂ) w := congrFun Complex.star_def w
  rw [h1, Complex.conj_re]

omit α in
/-- `w.re ≤ ‖w‖` (Tier T1 — proved). -/
theorem re_le_norm (w : ℂ) : w.re ≤ ‖w‖ :=
  le_trans (le_abs_self _) (RCLike.abs_re_le_norm w)

/-- Nonnegativity of the real part on the diagonal (Tier T1 — proved):
    from `hiprod_pos`. -/
theorem iprod_re_nonneg (x : α.toTripleData.S) : 0 ≤ (iprod x x).re := by
  obtain ⟨r, hr0, hr⟩ := α.hiprod_pos x
  rw [hr, Complex.ofReal_re]
  exact hr0

-- ============================================================================
-- §5. Symmetry and the fundamental symmetry (T1)
-- ============================================================================

/-- Conjugate symmetry of `iprod` (Tier T1 — proved):
    `iprod y x = star (iprod x y)`, via `hsesq_symm` and
    `hηsym_selfadj`. -/
theorem iprod_symm (x y : α.toTripleData.S) :
    iprod y x = star (iprod x y) := by
  simp only [iprod]
  rw [α.hsesq_symm, α.toTripleData.hηsym_selfadj]

/-- `iprod` is invariant under `ηsym` in both arguments (Tier T1 —
    proved): via `hηsym_sq` (`η² = 1`) then `hηsym_selfadj`. -/
theorem iprod_eta (x y : α.toTripleData.S) :
    iprod (α.toTripleData.ηsym x) (α.toTripleData.ηsym y) = iprod x y := by
  have hsq : ∀ z : α.toTripleData.S,
      α.toTripleData.ηsym (α.toTripleData.ηsym z) = z := by
    intro z
    have h := congrFun (congrArg DFunLike.coe α.toTripleData.hηsym_sq) z
    simpa [Module.End.mul_apply] using h
  simp only [iprod]
  rw [hsq, α.toTripleData.hηsym_selfadj]

-- ============================================================================
-- §6. Cauchy–Schwarz (T1)
-- ============================================================================

/-- **Cauchy–Schwarz** (Tier T1 — proved):
    `‖iprod x y‖² ≤ (iprod x x).re * (iprod y y).re`.
    If `iprod y y = 0` then `y = 0` by `hiprod_def` and both sides are `0`.
    Else write `iprod y y = ↑r` with `0 < r` from `hiprod_pos`, set
    `c := star (iprod x y) / ↑r`, and expand
    `0 ≤ (iprod (x - c • y) (x - c • y)).re` by sesquilinearity; the cross
    terms telescope to `‖iprod x y‖² / r`. -/
theorem cauchy_schwarz (x y : α.toTripleData.S) :
    ‖iprod x y‖ ^ 2 ≤ (iprod x x).re * (iprod y y).re := by
  obtain ⟨r, hr0, hry⟩ := α.hiprod_pos y
  by_cases hyy : iprod y y = 0
  · have hy0 : y = 0 := α.hiprod_def y hyy
    subst hy0
    rw [iprod_zero_right, iprod_zero_right]
    simp
  · have hrne : r ≠ 0 := fun h => hyy (by rw [hry, h, Complex.ofReal_zero])
    have hrpos : 0 < r := lt_of_le_of_ne hr0 hrne.symm
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hrne
    set c : ℂ := star (iprod x y) / (r : ℂ) with hc_def
    have hsr : star ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by
      have h1 : star ((r : ℝ) : ℂ) = (starRingEnd ℂ) ((r : ℝ) : ℂ) :=
        congrFun Complex.star_def _
      rw [h1, Complex.conj_ofReal]
    have hsc : star c = iprod x y / (r : ℂ) := by
      rw [hc_def, star_div₀, star_star, hsr]
    have e1 : iprod (x - c • y) (x - c • y)
        = iprod x x - c * iprod x y - star c * star (iprod x y)
          + (star c * c) * (r : ℂ) := by
      rw [iprod_sub_left, iprod_sub_right, iprod_sub_right,
        iprod_smul_right, iprod_smul_left, iprod_smul_left, iprod_smul_right,
        iprod_symm x y, hry]
      ring
    have t1 : c * iprod x y = ((‖iprod x y‖ ^ 2 : ℝ) : ℂ) / (r : ℂ) := by
      rw [hc_def, div_mul_eq_mul_div, star_mul_self]
    have t2 : star c * star (iprod x y)
        = ((‖iprod x y‖ ^ 2 : ℝ) : ℂ) / (r : ℂ) := by
      rw [hsc, div_mul_eq_mul_div, mul_comm (iprod x y) (star (iprod x y)),
        star_mul_self]
    have t3 : (star c * c) * (r : ℂ)
        = ((‖iprod x y‖ ^ 2 : ℝ) : ℂ) / (r : ℂ) := by
      have e : (iprod x y / (r : ℂ)) * (star (iprod x y) / (r : ℂ)) * (r : ℂ)
          = (star (iprod x y) * iprod x y) / (r : ℂ) := by
        field_simp
      rw [hsc, hc_def, e, star_mul_self]
    have hexpand : iprod (x - c • y) (x - c • y)
        = iprod x x - ((‖iprod x y‖ ^ 2 / r : ℝ) : ℂ) := by
      rw [e1, t1, t2, t3, Complex.ofReal_div]
      ring
    have hcs : 0 ≤ (iprod (x - c • y) (x - c • y)).re := iprod_re_nonneg _
    rw [hexpand, Complex.sub_re, Complex.ofReal_re] at hcs
    have hle : ‖iprod x y‖ ^ 2 / r ≤ (iprod x x).re := by linarith
    have hfin := (div_le_iff₀ hrpos).mp hle
    rw [hry, Complex.ofReal_re]
    exact hfin

-- ============================================================================
-- §7. The norm (T2 def, T1 theorems)
-- ============================================================================

/-- The norm from the inner product (Tier T2 — definition):
    `nrm x = √((iprod x x).re)`. -/
noncomputable def nrm (x : α.toTripleData.S) : ℝ :=
  Real.sqrt (iprod x x).re

/-- Homogeneity (Tier T1 — proved): `nrm (c • x) = ‖c‖ * nrm x`. -/
theorem nrm_smul (c : ℂ) (x : α.toTripleData.S) :
    nrm (c • x) = ‖c‖ * nrm x := by
  have e : iprod (c • x) (c • x) = ((‖c‖ ^ 2 : ℝ) : ℂ) * iprod x x := by
    have hcc : star c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := star_mul_self c
    rw [iprod_smul_left, iprod_smul_right, ← hcc]
    ring
  have hre_cast : ((((‖c‖ ^ 2 : ℝ)) : ℂ) * iprod x x).re
      = ‖c‖ ^ 2 * (iprod x x).re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp only [nrm, e, hre_cast, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

/-- Definiteness (Tier T1 — proved): `nrm x = 0 ↔ x = 0`, via
    `hiprod_pos` and `hiprod_def`. -/
theorem nrm_eq_zero (x : α.toTripleData.S) : nrm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hre : (iprod x x).re = 0 :=
      (Real.sqrt_eq_zero (iprod_re_nonneg x)).mp h
    obtain ⟨r, hr0, hr⟩ := α.hiprod_pos x
    have hr0' : r = 0 := by
      have hcongr := congrArg Complex.re hr
      simp only [Complex.ofReal_re] at hcongr
      linarith
    exact α.hiprod_def x (by rw [hr, hr0', Complex.ofReal_zero])
  · intro h
    subst h
    show Real.sqrt (iprod (0 : α.toTripleData.S) 0).re = 0
    rw [iprod_zero_right, Complex.zero_re, Real.sqrt_zero]

/-- Triangle inequality (Tier T1 — proved): from `cauchy_schwarz`. -/
theorem nrm_triangle (x y : α.toTripleData.S) :
    nrm (x + y) ≤ nrm x + nrm y := by
  have hsq2 : ∀ z : α.toTripleData.S, nrm z ^ 2 = (iprod z z).re := by
    intro z
    exact Real.sq_sqrt (iprod_re_nonneg z)
  have e : iprod (x + y) (x + y)
      = iprod x x + iprod y y + (iprod x y + iprod y x) := by
    rw [iprod_add_left, iprod_add_right, iprod_add_right]
    ring
  have e2 : (iprod (x + y) (x + y)).re
      = (iprod x x).re + (iprod y y).re + ((iprod x y).re + (iprod x y).re) := by
    rw [e, iprod_symm y x]
    simp only [Complex.add_re, star_re]
  have hexpand : (iprod (x + y) (x + y)).re
      = (iprod x x).re + (iprod y y).re + 2 * (iprod x y).re := by
    rw [e2]; ring
  have hxy : (iprod x y).re ≤ nrm x * nrm y := by
    have hcs := cauchy_schwarz x y
    have h2 : ‖iprod x y‖ ≤ nrm x * nrm y := by
      calc ‖iprod x y‖ = Real.sqrt (‖iprod x y‖ ^ 2) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt ((iprod x x).re * (iprod y y).re) :=
            Real.sqrt_le_sqrt hcs
        _ = nrm x * nrm y := by
            rw [Real.sqrt_mul (iprod_re_nonneg x)]
            rfl
    exact le_trans (re_le_norm _) h2
  have key : nrm (x + y) ^ 2 ≤ (nrm x + nrm y) ^ 2 := by
    rw [hsq2, add_sq, hsq2, hsq2, hexpand]
    linarith [hxy]
  exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)) (by norm_num)).mp key

-- PIN: CompleteSpace S unprovable for abstract S — needs a concrete model (Rung 4 proper).

#print axioms iprod_symm
#print axioms iprod_eta
#print axioms cauchy_schwarz
#print axioms nrm_smul
#print axioms nrm_eq_zero
#print axioms nrm_triangle

end ThetLogos
