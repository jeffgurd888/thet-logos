import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Topology.Algebra.Module.FiniteDimension
import ThetLogos.FermionicFock
import ThetLogos.BosonicFock
import ThetLogos.FockLimit
import ThetLogos.FermionicInteraction

/-!
# ThetLogos.YukawaInteraction — a finite-mode fermion–boson (Yukawa-type)
interaction, machine-checked (Pitch 3 follow-on; gauntlet parked-fleet §6)

## What this module is

The product-config presentation of a finite-mode matter coupling of
Yukawa SHAPE: a fermionic bilinear (density/current type, built from the
fermionic creation/annihilation operators `adag`/`ann` of
`FermionicFock`) tensored with a bosonic field (creation + annihilation,
`adagBos` + `annBos` of `BosonicFock`), on the product finite-particle
domain. The joint Hilbert space is NOT a completed tensor product: it is
the `lp` space over the product configuration type
`Finset (Fin df) × Config db`, exactly as both parent campaigns build
their spaces, so the two factors share one orthonormal basis and the
cross-factor operators commute ON THE NOSE (proved, §1).

The total Hamiltonian is
`H = H_free + g • H_Y`, where `H_free` is the joint diagonal free
operator (fermionic `freeEig` on the first factor, bosonic number-weighted
energies on the second — the eigenvalues of the parents' free
Hamiltonians `freeHamiltonian` and the bosonic diagonal family), and
`H_Y = Σ_{i,j,k} (Y_{ijk} + conj Y_{jik}) • (a†ᵢ aⱼ) ⊗ (a†ₖ + aₖ)`
is the symmetrized Yukawa interaction for a coupling tensor `Y`.

Ladder (gauntlet §6), as landed:
(a) product space, product finite-particle domain, coupling operator —
§0–§3. (b) Wick-type coefficient calculus for the coupled monomials —
§2. (c) symmetry of `H_Y` and of `H` on the product domain — §4.
(d) relative bounds with explicit constants: the interaction is bounded
relative to the product free/number data with the output-side factor
`sqrt (tot c' + 1)` made explicit per output configuration — §5.
(e) self-adjointness in Pitch 3's scoped senses ONLY: finite-dimensional
band restrictions of the free part carry the full spectral theorem;
the interaction is banded (band `N` maps into band `N+1` — it does NOT
preserve bosonic number sectors, because the field changes the total
boson number by ±1); the total `H` is symmetric on the dense product
domain and is a formal self-adjoint `LinearPMap` with
`H ≤ H†` — §4. (f) gap persistence in WINDOWED form only: an
eigenvector of `H` supported in bosonic band `N` obeys the dichotomy
`μ.re ≤ ‖g‖ • yukBound ∨ Δ/2 ≤ μ.re` at the explicit threshold
`2 • ‖g‖ • yukBound • sqrt (N+1) ≤ Δ/4` — §5.

## Mandatory fences (verbatim substance, gauntlet §6 + Pitch 3)

- FINITE MODES ONLY: `df` fermionic modes, `db` bosonic modes, both
  finite. No infinite-mode limit, no continuum limit is taken or claimed.
- This is a matter coupling of Yukawa SHAPE only (fermion bilinear ×
  boson field). It is NOT the Standard Model Yukawa sector: no Higgs
  mechanism, no flavor or chirality structure is present or claimed.
- No gauge field appears. No continuum. This is NOT a mass gap, and it
  closes no part of any Millennium Problem statement.
- ESSENTIAL SELF-ADJOINTNESS IS NOT PROVED. As in Pitch 3 (Campaign 2),
  it is the priced remainder: pinned Mathlib has no `LinearPMap`
  closure-equality API from sectorwise/domain data and no Kato–Rellich
  theorem; the closure domain of `H` here is an ℓ²-growth condition on
  coefficients, not a band. The scoped senses of (e) are what stands.
- UNIFORM (coupling-independent, band-independent) gap persistence is
  FALSE in general for bosonic factors (Pitch 3 Campaign 2's in-module
  collapse counterexample embeds at the fermion vacuum sector): only
  the windowed statement of (f) is claimed, with the window in the
  hypotheses from line one.
- `BosonicInteraction` does NOT co-import with the fermionic stack
  (the censused `numberOp` collision in `BosonicAssembly`, adag-repair
  dossier 2026-10-17); the bosonic coefficient machinery above
  `BosonicFock`'s parent API (monomial calculus, relative bounds,
  windowed persistence) is therefore rebuilt inside this module on the
  product configurations, in the same style. No statement is routed
  through `BosonicAssembly`.

## Honesty ledger

- Tier: T1 (machine-checked, zero sorries, standard axioms only).
- Cross-factor commutation is a THEOREM here (§1), not a convention:
  in the product-config presentation the two factors act on separate
  coordinates of one basis.
- The interaction is certified NOT diagonal in the joint basis when
  some diagonal coupling has nonzero real part (§6): it is not a `dΓ`,
  not a joint diagonal operator, and not a function of the free
  operator's eigenvalue data.
-/

namespace ThetLogos

open scoped InnerProductSpace

/-! ## §0. The product space, basis, finite-particle domain -/

/-- Product configuration type: a fermionic occupation set and a bosonic
occupation function. -/
abbrev JointConfig (df db : ℕ) : Type := Finset (Fin df) × Config db

/-- The joint Hilbert space: `ℓ²` over product configurations. -/
noncomputable abbrev JointSpace (df db : ℕ) : Type :=
  lp (fun _ : JointConfig df db => ℂ) 2

/-- The joint orthonormal basis vector at a product configuration. -/
noncomputable def jE (df db : ℕ) (q : JointConfig df db) : JointSpace df db :=
  lp.single 2 q 1

theorem jE_inner (df db : ℕ) (q q' : JointConfig df db) :
    ⟪jE df db q, jE df db q'⟫_ℂ = if q = q' then 1 else 0 := by
  unfold jE
  rw [lp.inner_single_left, lp.single_apply]
  by_cases h : q = q' <;> simp [h, RCLike.inner_apply]

theorem jE_orthonormal (df db : ℕ) : Orthonormal ℂ (jE df db) := by
  rw [orthonormal_iff_ite]
  exact jE_inner df db

theorem jLinIndep (df db : ℕ) : LinearIndependent ℂ (jE df db) :=
  (jE_orthonormal df db).linearIndependent

/-- The product finite-particle domain: finite joint combinations. -/
noncomputable def JDom (df db : ℕ) : Submodule ℂ (JointSpace df db) :=
  Submodule.span ℂ (Set.range (jE df db))

noncomputable def jEquiv (df db : ℕ) : (JointConfig df db →₀ ℂ) ≃ₗ[ℂ] JDom df db :=
  (jLinIndep df db).linearCombinationEquiv

/-- Representation: domain vectors ≃ their joint coefficients. -/
noncomputable def jRepr (df db : ℕ) : JDom df db ≃ₗ[ℂ] (JointConfig df db →₀ ℂ) :=
  (jEquiv df db).symm

/-- The basis vector of the domain at `q`. -/
noncomputable def jVec (df db : ℕ) (q : JointConfig df db) : JDom df db :=
  ⟨jE df db q, Submodule.subset_span (Set.mem_range_self q)⟩

theorem jEquiv_basis (df db : ℕ) (q : JointConfig df db) :
    jEquiv df db (Finsupp.single q 1) = jVec df db q := by
  have h : (jLinIndep df db).repr (jVec df db q) = Finsupp.single q 1 :=
    LinearIndependent.repr_eq_single _ _ _ rfl
  have h2 : jEquiv df db ((jLinIndep df db).repr (jVec df db q)) = jVec df db q := by
    show (jLinIndep df db).linearCombinationEquiv
        ((jLinIndep df db).linearCombinationEquiv.symm _) = _
    exact LinearEquiv.apply_symm_apply _ _
  rw [h] at h2
  exact h2

theorem jRepr_jVec (df db : ℕ) (q : JointConfig df db) :
    jRepr df db (jVec df db q) = Finsupp.single q 1 := by
  rw [jRepr, LinearEquiv.symm_apply_eq]
  exact (jEquiv_basis df db q).symm

/-- Double induction on the product domain (port of `Dom_induction₂`). -/
theorem JDom_induction₂ (df db : ℕ) {P : JDom df db → JDom df db → Prop}
    (base : ∀ q q', P (jVec df db q) (jVec df db q'))
    (add₁ : ∀ x x' y, P x y → P x' y → P (x + x') y)
    (zero₁ : ∀ y, P 0 y)
    (smul₁ : ∀ (a : ℂ) x y, P x y → P (a • x) y)
    (add₂ : ∀ x y y', P x y → P x y' → P x (y + y'))
    (zero₂ : ∀ x, P x 0)
    (smul₂ : ∀ (a : ℂ) x y, P x y → P x (a • y))
    (x y : JDom df db) : P x y := by
  obtain ⟨u, hu⟩ := x
  obtain ⟨v, hv⟩ := y
  have key := Submodule.span_induction₂ (s := Set.range (jE df db))
    (t := Set.range (jE df db))
    (p := fun u v hu hv => P ⟨u, hu⟩ ⟨v, hv⟩)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hu hv
  exact key
  · intro x y hx hy
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨c', rfl⟩ := hy
    exact base c c'
  · intro y hy
    exact zero₁ ⟨y, hy⟩
  · intro x hx
    exact zero₂ ⟨x, hx⟩
  · intro x y z hx hy hz ih1 ih2
    have e : (⟨x + y, Submodule.add_mem (JDom df db) hx hy⟩ : JDom df db)
        = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [e]
    exact add₁ _ _ _ ih1 ih2
  · intro x y z hx hy hz ih1 ih2
    have e : (⟨y + z, Submodule.add_mem (JDom df db) hy hz⟩ : JDom df db)
        = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
    rw [e]
    exact add₂ _ _ _ ih1 ih2
  · intro a x y hx hy ih
    have e : (⟨a • x, Submodule.smul_mem (JDom df db) a hx⟩ : JDom df db)
        = a • ⟨x, hx⟩ := rfl
    rw [e]
    exact smul₁ _ _ _ ih
  · intro a x y hx hy ih
    have e : (⟨a • y, Submodule.smul_mem (JDom df db) a hy⟩ : JDom df db)
        = a • ⟨y, hy⟩ := rfl
    rw [e]
    exact smul₂ _ _ _ ih

/-- Coordinate identity: pairing with a basis vector reads off the
representation coefficient. -/
theorem jcoord (df db : ℕ) (x : JDom df db) (q : JointConfig df db) :
    ⟪jE df db q, (x : JointSpace df db)⟫_ℂ = (jRepr df db x) q := by
  obtain ⟨x, hx⟩ := x
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q₀, rfl⟩ := hy
    show ⟪jE df db q, jE df db q₀⟫_ℂ = (jRepr df db (jVec df db q₀)) q
    rw [jE_inner, jRepr_jVec, Finsupp.single_apply]
    rcases eq_or_ne q q₀ with rfl | h
    · simp
    · simp [h, Ne.symm h]
  | zero =>
    show ⟪jE df db q, ((0 : JDom df db) : JointSpace df db)⟫_ℂ
      = (jRepr df db 0) q
    simp
  | add y z hy hz ihy ihz =>
    have e : (⟨y + z, Submodule.add_mem _ hy hz⟩ : JDom df db)
        = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
    show ⟪jE df db q, ((⟨y + z, Submodule.add_mem _ hy hz⟩ : JDom df db)
        : JointSpace df db)⟫_ℂ
      = (jRepr df db ⟨y + z, Submodule.add_mem _ hy hz⟩) q
    rw [e, map_add, Finsupp.add_apply]
    show ⟪jE df db q, ((⟨y, hy⟩ : JDom df db) : JointSpace df db)
      + ((⟨z, hz⟩ : JDom df db) : JointSpace df db)⟫_ℂ = _
    rw [inner_add_right, ihy, ihz]
  | smul a y hy ih =>
    have e : (⟨a • y, Submodule.smul_mem _ a hy⟩ : JDom df db)
        = a • ⟨y, hy⟩ := rfl
    show ⟪jE df db q, ((⟨a • y, Submodule.smul_mem _ a hy⟩ : JDom df db)
        : JointSpace df db)⟫_ℂ
      = (jRepr df db ⟨a • y, Submodule.smul_mem _ a hy⟩) q
    rw [e, map_smul, Finsupp.smul_apply]
    show ⟪jE df db q, a • ((⟨y, hy⟩ : JDom df db) : JointSpace df db)⟫_ℂ = _
    rw [inner_smul_right, ih, smul_eq_mul]

/-! ## §1. Factor operators at the coefficient level

All operators are first built on coefficient finsupp
`JointConfig df db →₀ ℂ`, where the two factors act on separate
coordinates. Cross-factor commutation is proved here, on the nose. -/

/-- Fermionic creation at the coefficient level: inserts mode `i` into
the fermionic factor; the bosonic factor is untouched. This is the
product presentation of `adag i ⊗ 1`. -/
noncomputable def fDagC (df db : ℕ) (i : Fin df) :
    (JointConfig df db →₀ ℂ) →ₗ[ℂ] (JointConfig df db →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun q : JointConfig df db =>
    (if i ∈ q.1 then 0 else sgn df i q.1) • Finsupp.single (insert i q.1, q.2) 1

/-- Fermionic annihilation at the coefficient level: `ann i ⊗ 1`. -/
noncomputable def fAnnC (df db : ℕ) (i : Fin df) :
    (JointConfig df db →₀ ℂ) →ₗ[ℂ] (JointConfig df db →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun q : JointConfig df db =>
    if i ∉ q.1 then 0 else sgn df i q.1 • Finsupp.single (q.1.erase i, q.2) 1

/-- Bosonic creation at the coefficient level: `1 ⊗ adagBos k`. -/
noncomputable def bDagC (df db : ℕ) (k : Fin db) :
    (JointConfig df db →₀ ℂ) →ₗ[ℂ] (JointConfig df db →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun q : JointConfig df db =>
    sqrtNat (q.2 k + 1) • Finsupp.single (q.1, q.2 + Finsupp.single k 1) 1

/-- Bosonic annihilation at the coefficient level: `1 ⊗ annBos k`.
(The vanishing at `q.2 k = 0` is put in the scalar, so downstream
single-formulas carry no finsupp-level `if`.) -/
noncomputable def bAnnC (df db : ℕ) (k : Fin db) :
    (JointConfig df db →₀ ℂ) →ₗ[ℂ] (JointConfig df db →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun q : JointConfig df db =>
    (if q.2 k = 0 then 0 else sqrtNat (q.2 k))
      • Finsupp.single (q.1, q.2 - Finsupp.single k 1) 1

theorem fDagC_single (df db : ℕ) (i : Fin df) (S : Finset (Fin df)) (c : Config db)
    (a : ℂ) :
    fDagC df db i (Finsupp.single (S, c) a)
      = (a * (if i ∈ S then 0 else sgn df i S)) • Finsupp.single (insert i S, c) 1 := by
  simp only [fDagC, Finsupp.linearCombination_single, ← mul_smul]

theorem fAnnC_single (df db : ℕ) (i : Fin df) (S : Finset (Fin df)) (c : Config db)
    (a : ℂ) :
    fAnnC df db i (Finsupp.single (S, c) a)
      = if i ∉ S then 0 else (a * sgn df i S) • Finsupp.single (S.erase i, c) 1 := by
  by_cases h : i ∈ S
  · simp [fAnnC, Finsupp.linearCombination_single, h]
  · simp [fAnnC, Finsupp.linearCombination_single, h]

theorem bDagC_single (df db : ℕ) (k : Fin db) (S : Finset (Fin df)) (c : Config db)
    (a : ℂ) :
    bDagC df db k (Finsupp.single (S, c) a)
      = (a * sqrtNat (c k + 1)) • Finsupp.single (S, c + Finsupp.single k 1) 1 := by
  simp only [bDagC, Finsupp.linearCombination_single, ← mul_smul]

theorem bAnnC_single (df db : ℕ) (k : Fin db) (S : Finset (Fin df)) (c : Config db)
    (a : ℂ) :
    bAnnC df db k (Finsupp.single (S, c) a)
      = (a * (if c k = 0 then 0 else sqrtNat (c k)))
        • Finsupp.single (S, c - Finsupp.single k 1) 1 := by
  simp only [bAnnC, Finsupp.linearCombination_single, ← mul_smul]

/-- Scalar multiples of a basis singleton are singletons. -/
theorem smul_single_one (df db : ℕ) (s : ℂ) (q : JointConfig df db) :
    s • Finsupp.single q (1 : ℂ) = Finsupp.single q s := by
  ext q'
  rw [Finsupp.smul_apply, Finsupp.single_apply, Finsupp.single_apply]
  by_cases h : q = q' <;> simp [h]

/-- Cross-factor commutation, on the nose: fermionic creation commutes
with bosonic creation in the product presentation. -/
theorem fDagC_comp_bDagC (df db : ℕ) (i : Fin df) (k : Fin db) :
    fDagC df db i ∘ₗ bDagC df db k = bDagC df db k ∘ₗ fDagC df db i := by
  apply Finsupp.lhom_ext
  intro q a
  obtain ⟨S, c⟩ := q
  have hL : (fDagC df db i ∘ₗ bDagC df db k) (Finsupp.single (S, c) a)
      = ((a * sqrtNat (c k + 1)) * (if i ∈ S then 0 else sgn df i S))
        • Finsupp.single (insert i S, c + Finsupp.single k 1) 1 := by
    rw [LinearMap.comp_apply, bDagC_single, smul_single_one, fDagC_single]
  have hR : (bDagC df db k ∘ₗ fDagC df db i) (Finsupp.single (S, c) a)
      = ((a * (if i ∈ S then 0 else sgn df i S)) * sqrtNat (c k + 1))
        • Finsupp.single (insert i S, c + Finsupp.single k 1) 1 := by
    rw [LinearMap.comp_apply, fDagC_single, smul_single_one, bDagC_single]
  rw [hL, hR]
  congr 1
  ring

theorem fDagC_comp_bAnnC (df db : ℕ) (i : Fin df) (k : Fin db) :
    fDagC df db i ∘ₗ bAnnC df db k = bAnnC df db k ∘ₗ fDagC df db i := by
  apply Finsupp.lhom_ext
  intro q a
  obtain ⟨S, c⟩ := q
  by_cases hk : c k = 0
  · have hL : (fDagC df db i ∘ₗ bAnnC df db k) (Finsupp.single (S, c) a) = 0 := by
      rw [LinearMap.comp_apply, bAnnC_single, if_pos hk, mul_zero, zero_smul, map_zero]
    have hR : (bAnnC df db k ∘ₗ fDagC df db i) (Finsupp.single (S, c) a) = 0 := by
      rw [LinearMap.comp_apply, fDagC_single, smul_single_one, bAnnC_single, if_pos hk,
        mul_zero, zero_smul]
    rw [hL, hR]
  · have hL : (fDagC df db i ∘ₗ bAnnC df db k) (Finsupp.single (S, c) a)
        = ((a * sqrtNat (c k)) * (if i ∈ S then 0 else sgn df i S))
          • Finsupp.single (insert i S, c - Finsupp.single k 1) 1 := by
      rw [LinearMap.comp_apply, bAnnC_single, if_neg hk, smul_single_one, fDagC_single]
    have hR : (bAnnC df db k ∘ₗ fDagC df db i) (Finsupp.single (S, c) a)
        = ((a * (if i ∈ S then 0 else sgn df i S)) * sqrtNat (c k))
          • Finsupp.single (insert i S, c - Finsupp.single k 1) 1 := by
      rw [LinearMap.comp_apply, fDagC_single, smul_single_one, bAnnC_single, if_neg hk]
    rw [hL, hR]
    congr 1
    ring

theorem fAnnC_comp_bDagC (df db : ℕ) (i : Fin df) (k : Fin db) :
    fAnnC df db i ∘ₗ bDagC df db k = bDagC df db k ∘ₗ fAnnC df db i := by
  apply Finsupp.lhom_ext
  intro q a
  obtain ⟨S, c⟩ := q
  by_cases hi : i ∈ S
  · have hL : (fAnnC df db i ∘ₗ bDagC df db k) (Finsupp.single (S, c) a)
        = ((a * sqrtNat (c k + 1)) * sgn df i S)
          • Finsupp.single (S.erase i, c + Finsupp.single k 1) 1 := by
      rw [LinearMap.comp_apply, bDagC_single, smul_single_one, fAnnC_single,
        if_neg (by simp [hi])]
    have hR : (bDagC df db k ∘ₗ fAnnC df db i) (Finsupp.single (S, c) a)
        = ((a * sgn df i S) * sqrtNat (c k + 1))
          • Finsupp.single (S.erase i, c + Finsupp.single k 1) 1 := by
      rw [LinearMap.comp_apply, fAnnC_single, if_neg (by simp [hi]), smul_single_one,
        bDagC_single]
    rw [hL, hR]
    congr 1
    ring
  · have hL : (fAnnC df db i ∘ₗ bDagC df db k) (Finsupp.single (S, c) a) = 0 := by
      rw [LinearMap.comp_apply, bDagC_single, smul_single_one, fAnnC_single, if_pos hi]
    have hR : (bDagC df db k ∘ₗ fAnnC df db i) (Finsupp.single (S, c) a) = 0 := by
      rw [LinearMap.comp_apply, fAnnC_single, if_pos hi, map_zero]
    rw [hL, hR]

theorem fAnnC_comp_bAnnC (df db : ℕ) (i : Fin df) (k : Fin db) :
    fAnnC df db i ∘ₗ bAnnC df db k = bAnnC df db k ∘ₗ fAnnC df db i := by
  apply Finsupp.lhom_ext
  intro q a
  obtain ⟨S, c⟩ := q
  by_cases hk : c k = 0
  · have hL : (fAnnC df db i ∘ₗ bAnnC df db k) (Finsupp.single (S, c) a) = 0 := by
      rw [LinearMap.comp_apply, bAnnC_single, if_pos hk, mul_zero, zero_smul, map_zero]
    have hR : (bAnnC df db k ∘ₗ fAnnC df db i) (Finsupp.single (S, c) a) = 0 := by
      rw [LinearMap.comp_apply, fAnnC_single]
      by_cases hi : i ∈ S
      · rw [if_neg (by simp [hi]), smul_single_one, bAnnC_single, if_pos hk, mul_zero,
          zero_smul]
      · rw [if_pos hi, map_zero]
    rw [hL, hR]
  · by_cases hi : i ∈ S
    · have hL : (fAnnC df db i ∘ₗ bAnnC df db k) (Finsupp.single (S, c) a)
          = ((a * sqrtNat (c k)) * sgn df i S)
            • Finsupp.single (S.erase i, c - Finsupp.single k 1) 1 := by
        rw [LinearMap.comp_apply, bAnnC_single, if_neg hk, smul_single_one,
          fAnnC_single, if_neg (by simp [hi])]
      have hR : (bAnnC df db k ∘ₗ fAnnC df db i) (Finsupp.single (S, c) a)
          = ((a * sgn df i S) * sqrtNat (c k))
            • Finsupp.single (S.erase i, c - Finsupp.single k 1) 1 := by
        rw [LinearMap.comp_apply, fAnnC_single, if_neg (by simp [hi]), smul_single_one,
          bAnnC_single, if_neg hk]
      rw [hL, hR]
      congr 1
      ring
    · have hL : (fAnnC df db i ∘ₗ bAnnC df db k) (Finsupp.single (S, c) a) = 0 := by
        rw [LinearMap.comp_apply, bAnnC_single, if_neg hk, smul_single_one,
          fAnnC_single, if_pos hi]
      have hR : (bAnnC df db k ∘ₗ fAnnC df db i) (Finsupp.single (S, c) a) = 0 := by
        rw [LinearMap.comp_apply, fAnnC_single, if_pos hi, map_zero]
      rw [hL, hR]

/-! ### The density, the field, and the Yukawa monomial -/

/-- The fermionic configuration map of the density monomial `a†ᵢ aⱼ`. -/
def densPhi (df : ℕ) (i j : Fin df) (S : Finset (Fin df)) : Finset (Fin df) :=
  insert i (S.erase j)

/-- The Wick coefficient of the density monomial `a†ᵢ aⱼ`: a product of
two Koszul signs, or zero when the monomial annihilates the
configuration. -/
noncomputable def densCoef (df : ℕ) (i j : Fin df) (S : Finset (Fin df)) : ℂ :=
  if j ∈ S ∧ i ∉ S.erase j then sgn df j S * sgn df i (S.erase j) else 0

/-- The fermionic density/current factor at the coefficient level:
`densC i j = fDagC i ∘ₗ fAnnC j`, the product presentation of
`(a†ᵢ aⱼ) ⊗ 1`. -/
noncomputable def densC (df db : ℕ) (i j : Fin df) :
    (JointConfig df db →₀ ℂ) →ₗ[ℂ] (JointConfig df db →₀ ℂ) :=
  fDagC df db i ∘ₗ fAnnC df db j

theorem densC_single (df db : ℕ) (i j : Fin df) (S : Finset (Fin df)) (c : Config db)
    (a : ℂ) :
    densC df db i j (Finsupp.single (S, c) a)
      = (a * densCoef df i j S) • Finsupp.single (densPhi df i j S, c) 1 := by
  by_cases hj : j ∈ S
  · by_cases hi : i ∈ S.erase j
    · have hcoef : densCoef df i j S = 0 := by simp [densCoef, hj, hi]
      rw [densC, LinearMap.comp_apply, fAnnC_single, if_neg (by simp [hj]),
        smul_single_one, fDagC_single, if_pos hi, mul_zero, zero_smul, hcoef,
        mul_zero, zero_smul]
    · have hcoef : densCoef df i j S = sgn df j S * sgn df i (S.erase j) := by
        simp [densCoef, hj, hi]
      rw [densC, LinearMap.comp_apply, fAnnC_single, if_neg (by simp [hj]),
        smul_single_one, fDagC_single, if_neg hi, hcoef, densPhi, mul_assoc]
  · have hcoef : densCoef df i j S = 0 := by simp [densCoef, hj]
    rw [densC, LinearMap.comp_apply, fAnnC_single, if_pos hj, map_zero,
      hcoef, mul_zero, zero_smul]

/-- The bosonic field factor at the coefficient level:
`1 ⊗ (adagBos k + annBos k)`. -/
noncomputable def fieldC (df db : ℕ) (k : Fin db) :
    (JointConfig df db →₀ ℂ) →ₗ[ℂ] (JointConfig df db →₀ ℂ) :=
  bDagC df db k + bAnnC df db k

theorem fieldC_single (df db : ℕ) (k : Fin db) (S : Finset (Fin df)) (c : Config db)
    (a : ℂ) :
    fieldC df db k (Finsupp.single (S, c) a)
      = (a * sqrtNat (c k + 1)) • Finsupp.single (S, c + Finsupp.single k 1) 1
        + (a * (if c k = 0 then 0 else sqrtNat (c k)))
            • Finsupp.single (S, c - Finsupp.single k 1) 1 := by
  rw [fieldC, LinearMap.add_apply, bDagC_single, bAnnC_single]

/-- The coupled Yukawa monomial at the coefficient level:
density ⊗ field. -/
noncomputable def yukMonoC (df db : ℕ) (i j : Fin df) (k : Fin db) :
    (JointConfig df db →₀ ℂ) →ₗ[ℂ] (JointConfig df db →₀ ℂ) :=
  densC df db i j ∘ₗ fieldC df db k

theorem yukMonoC_single (df db : ℕ) (i j : Fin df) (k : Fin db)
    (S : Finset (Fin df)) (c : Config db) (a : ℂ) :
    yukMonoC df db i j k (Finsupp.single (S, c) a)
      = (a * densCoef df i j S * sqrtNat (c k + 1))
          • Finsupp.single (densPhi df i j S, c + Finsupp.single k 1) 1
        + (a * densCoef df i j S * (if c k = 0 then 0 else sqrtNat (c k)))
            • Finsupp.single (densPhi df i j S, c - Finsupp.single k 1) 1 := by
  have h1 : densC df db i j ((a * sqrtNat (c k + 1))
        • Finsupp.single (S, c + Finsupp.single k 1) 1)
      = (a * densCoef df i j S * sqrtNat (c k + 1))
          • Finsupp.single (densPhi df i j S, c + Finsupp.single k 1) 1 := by
    rw [smul_single_one, densC_single, mul_right_comm]
  have h2 : densC df db i j ((a * (if c k = 0 then 0 else sqrtNat (c k)))
        • Finsupp.single (S, c - Finsupp.single k 1) 1)
      = (a * densCoef df i j S * (if c k = 0 then 0 else sqrtNat (c k)))
          • Finsupp.single (densPhi df i j S, c - Finsupp.single k 1) 1 := by
    rw [smul_single_one, densC_single, mul_right_comm]
  rw [yukMonoC, LinearMap.comp_apply, fieldC_single, map_add, h1, h2]

/-- The same monomial computed in the other order — the two orders
agree because the factors commute (the four commutation theorems above
are the operator-level input; this is the composite computation). -/
theorem fieldC_densC_single (df db : ℕ) (i j : Fin df) (k : Fin db)
    (S : Finset (Fin df)) (c : Config db) (a : ℂ) :
    fieldC df db k (densC df db i j (Finsupp.single (S, c) a))
      = (a * densCoef df i j S * sqrtNat (c k + 1))
          • Finsupp.single (densPhi df i j S, c + Finsupp.single k 1) 1
        + (a * densCoef df i j S * (if c k = 0 then 0 else sqrtNat (c k)))
            • Finsupp.single (densPhi df i j S, c - Finsupp.single k 1) 1 := by
  rw [densC_single, smul_single_one, fieldC_single]

/-- The density factor commutes with the field factor as operators. -/
theorem densC_comp_fieldC (df db : ℕ) (i j : Fin df) (k : Fin db) :
    densC df db i j ∘ₗ fieldC df db k = fieldC df db k ∘ₗ densC df db i j := by
  apply Finsupp.lhom_ext
  intro q a
  obtain ⟨S, c⟩ := q
  show yukMonoC df db i j k (Finsupp.single (S, c) a)
    = fieldC df db k (densC df db i j (Finsupp.single (S, c) a))
  rw [yukMonoC_single]
  exact (fieldC_densC_single df db i j k S c a).symm


/-! ## §2. Wick-type coefficient calculus for the coupled monomials

Everything is computed in the joint basis. The coupled monomial's
matrix element factors as a fermionic density matrix element times a
bosonic field matrix element; the symmetrized interaction's total
coefficient is hermitian in the joint indices (the adjoint identity
that will give symmetry on the domain in §4). -/

/-- Total boson number of a bosonic configuration. -/
def bTot (db : ℕ) (c : Config db) : ℕ := ∑ k, c k

theorem bTot_add_single (db : ℕ) (c : Config db) (k : Fin db) :
    bTot db (c + Finsupp.single k 1) = bTot db c + 1 := by
  have h : ∀ j : Fin db, (c + Finsupp.single k (1 : ℕ)) j
      = c j + (if j = k then 1 else 0) := by
    intro j
    rw [Finsupp.add_apply, Finsupp.single_apply]
    by_cases hj : j = k
    · rw [if_pos hj, if_pos hj.symm]
    · rw [if_neg hj, if_neg (fun hh => hj hh.symm)]
  rw [bTot, Finset.sum_congr rfl (fun j _ => h j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ k (fun _ => (1 : ℕ)), if_pos (Finset.mem_univ k),
    bTot]

theorem bTot_sub_single_le (db : ℕ) (c : Config db) (k : Fin db) :
    bTot db (c - Finsupp.single k 1) ≤ bTot db c := by
  show (∑ j, (c - Finsupp.single k (1 : ℕ)) j) ≤ ∑ j, c j
  apply Finset.sum_le_sum
  intro j _
  rw [Finsupp.tsub_apply]
  exact Nat.sub_le _ _

theorem config_le_bTot (db : ℕ) (c : Config db) (k : Fin db) : c k ≤ bTot db c :=
  Finset.single_le_sum (fun i _ => Nat.zero_le (c i)) (Finset.mem_univ k)

theorem coord_add_single (db : ℕ) (c : Config db) (k : Fin db) :
    (c + Finsupp.single k (1 : ℕ)) k = c k + 1 := by
  simp [Finsupp.add_apply]

theorem coord_sub_single (db : ℕ) (c : Config db) (k : Fin db) :
    (c - Finsupp.single k (1 : ℕ)) k = c k - 1 := by
  simp [Finsupp.tsub_apply]

theorem config_add_ne_sub (db : ℕ) (c : Config db) (k : Fin db) :
    c + Finsupp.single k 1 ≠ c - Finsupp.single k 1 := by
  intro h
  have h2 := congrArg (fun f : Config db => f k) h
  rw [coord_add_single, coord_sub_single] at h2
  omega

theorem config_add_single_ne_self (db : ℕ) (c : Config db) (k : Fin db) :
    c + Finsupp.single k 1 ≠ c := by
  intro h
  have h2 := congrArg (fun f : Config db => f k) h
  rw [coord_add_single] at h2
  omega

theorem config_sub_single_eq_self (db : ℕ) (c : Config db) (k : Fin db)
    (h : c k = 0) : c - Finsupp.single k 1 = c := by
  ext j
  simp only [Finsupp.tsub_apply, Finsupp.single_apply]
  by_cases hj : j = k
  · subst hj
    rw [if_pos rfl, h]
  · rw [if_neg (fun hh => hj hh.symm), Nat.sub_zero]

theorem norm_sqrtNat (n : ℕ) : ‖sqrtNat n‖ = Real.sqrt (n : ℝ) := by
  rw [sqrtNat, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

/-! ### The density matrix element -/

/-- The unique preimage of the density configuration map on its
support: if `densCoef df i j S ≠ 0` then `densPre df i j (densPhi df i j S) = S`. -/
def densPre (df : ℕ) (i j : Fin df) (S' : Finset (Fin df)) : Finset (Fin df) :=
  insert j (S'.erase i)

theorem densPhi_pre (df : ℕ) {i j : Fin df} {S : Finset (Fin df)}
    (h : densCoef df i j S ≠ 0) : densPre df i j (densPhi df i j S) = S := by
  by_cases hcond : j ∈ S ∧ i ∉ S.erase j
  · obtain ⟨hj, hi⟩ := hcond
    show insert j ((insert i (S.erase j)).erase i) = S
    rw [Finset.erase_insert hi, Finset.insert_erase hj]
  · rw [densCoef, if_neg hcond] at h
    exact absurd rfl h

/-- The density matrix element in the fermionic basis:
`(densC i j)` sends basis `S` to `densMat S' S` at basis `S'`. -/
noncomputable def densMat (df : ℕ) (i j : Fin df) (S' S : Finset (Fin df)) : ℂ :=
  if S' = densPhi df i j S then densCoef df i j S else 0

theorem densMat_pre (df : ℕ) {i j : Fin df} {S' S : Finset (Fin df)}
    (h : densMat df i j S' S ≠ 0) :
    S = densPre df i j S' ∧ densMat df i j S' S = densCoef df i j S := by
  by_cases hphi : S' = densPhi df i j S
  · have hcoef : densCoef df i j S ≠ 0 := by
      rwa [densMat, if_pos hphi] at h
    refine ⟨?_, by rw [densMat, if_pos hphi]⟩
    rw [← densPhi_pre df hcoef, hphi]
  · rw [densMat, if_neg hphi] at h
    exact absurd rfl h

theorem norm_densCoef_le (df : ℕ) (i j : Fin df) (S : Finset (Fin df)) :
    ‖densCoef df i j S‖ ≤ 1 := by
  rw [densCoef]
  split
  · rw [norm_mul, norm_sgn, norm_sgn, mul_one]
  · simp

theorem norm_densMat_le (df : ℕ) (i j : Fin df) (S' S : Finset (Fin df)) :
    ‖densMat df i j S' S‖ ≤ 1 := by
  rw [densMat]
  split
  · exact norm_densCoef_le df i j S
  · simp

/-- The density coefficient identity behind the adjoint relation:
on the support, swapping the density's indices conjugates the
coefficient. -/
theorem densMat_adjoint_aux (df : ℕ) {i j : Fin df} {S' S : Finset (Fin df)}
    (h : densMat df i j S' S ≠ 0) :
    densMat df j i S S' = (starRingEnd ℂ) (densMat df i j S' S) := by
  obtain ⟨hpre, hval⟩ := densMat_pre df h
  have hphi : S' = densPhi df i j S := by
    by_cases hphi : S' = densPhi df i j S
    · exact hphi
    · rw [densMat, if_neg hphi] at h
      exact absurd rfl h
  have hcoef : densCoef df i j S ≠ 0 := by
    rw [← hval]; exact h
  have hcond : j ∈ S ∧ i ∉ S.erase j := by
    by_cases hcond : j ∈ S ∧ i ∉ S.erase j
    · exact hcond
    · rw [densCoef, if_neg hcond] at hcoef
      exact absurd rfl hcoef
  obtain ⟨hj, hi⟩ := hcond
  have hphi2 : densPhi df j i S' = S := hpre.symm
  have hcond2 : i ∈ S' ∧ j ∉ S'.erase i := by
    constructor
    · rw [hphi]; exact Finset.mem_insert_self i (S.erase j)
    · have e : S'.erase i = S.erase j := by
        rw [hphi]
        show (insert i (S.erase j)).erase i = S.erase j
        exact Finset.erase_insert hi
      rw [e]
      simp [Finset.mem_erase]
  have e1 : sgn df i S' = sgn df i (S.erase j) := by
    rw [hphi]
    show sgn df i (insert i (S.erase j)) = sgn df i (S.erase j)
    exact sgn_insert_eq df i (S.erase j)
  have e2 : sgn df j (S'.erase i) = sgn df j (S.erase j) := by
    rw [hphi]
    show sgn df j ((insert i (S.erase j)).erase i) = sgn df j (S.erase j)
    rw [Finset.erase_insert hi]
  have e3 : sgn df j S = sgn df j (S'.erase i) := by
    rw [hpre]
    show sgn df j (insert j (S'.erase i)) = sgn df j (S'.erase i)
    exact sgn_insert_eq df j (S'.erase i)
  rw [densMat, if_pos hphi2.symm, hval, densCoef, if_pos hcond2, densCoef,
    if_pos ⟨hj, hi⟩,
    map_mul, starRingEnd_sgn, starRingEnd_sgn, e1, e3, e2, mul_comm]

/-- The density matrix element is hermitian in its two indices. -/
theorem densMat_adjoint (df : ℕ) (i j : Fin df) (S' S : Finset (Fin df)) :
    (starRingEnd ℂ) (densMat df i j S' S) = densMat df j i S S' := by
  by_cases h : densMat df i j S' S = 0
  · rw [h, map_zero]
    by_contra hne
    have hne' : densMat df j i S S' ≠ 0 := fun hh => hne hh.symm
    have haux := densMat_adjoint_aux df hne'
    have hne2 : (starRingEnd ℂ) (densMat df j i S S') ≠ 0 := by
      intro hh
      rw [starRingEnd_apply, star_eq_zero] at hh
      exact hne' hh
    rw [haux] at h
    exact hne2 h
  · exact (densMat_adjoint_aux df h).symm

/-! ### The field matrix element -/

/-- The field matrix element in the bosonic basis:
`(fieldC k)` sends basis `c` to `fieldMat c' c` at basis `c'`. -/
noncomputable def fieldMat (db : ℕ) (k : Fin db) (c' c : Config db) : ℂ :=
  (if c' = c + Finsupp.single k 1 then sqrtNat (c k + 1) else 0)
    + (if c' = c - Finsupp.single k 1
        then (if c k = 0 then 0 else sqrtNat (c k)) else 0)

theorem fieldMat_eq_zero_of (db : ℕ) (k : Fin db) {c' c : Config db}
    (h1 : c' ≠ c + Finsupp.single k 1)
    (h2 : c' ≠ c - Finsupp.single k 1 ∨ c k = 0) :
    fieldMat db k c' c = 0 := by
  rw [fieldMat, if_neg h1]
  rcases h2 with h2 | h2
  · rw [if_neg h2, add_zero]
  · by_cases h3 : c' = c - Finsupp.single k 1
    · rw [if_pos h3, if_pos h2, add_zero]
    · rw [if_neg h3, add_zero]

/-- The field matrix element is hermitian in its two indices. -/
theorem fieldMat_adjoint (db : ℕ) (k : Fin db) (c' c : Config db) :
    (starRingEnd ℂ) (fieldMat db k c' c) = fieldMat db k c c' := by
  simp only [fieldMat, map_add, apply_ite, map_zero, sqrtNat_starRingEnd]
  by_cases h1 : c' = c + Finsupp.single k 1
  · have h2 : ¬ (c' = c - Finsupp.single k 1) := by
      rw [h1]; exact config_add_ne_sub db c k
    have h3 : c = c' - Finsupp.single k 1 := by
      rw [h1]; exact (config_add_single_sub_single db c k).symm
    have h7 : c' k = c k + 1 := by
      rw [h1]; exact coord_add_single db c k
    have h4 : ¬ (c = c' + Finsupp.single k 1) := by
      intro hh
      have h5 := congrArg (fun f : Config db => f k) hh
      rw [coord_add_single] at h5
      omega
    have h8 : c' k ≠ 0 := by omega
    rw [if_pos h1, if_neg h2, add_zero, if_neg h4, if_pos h3, if_neg h8, zero_add, h7]
  · by_cases h2 : c' = c - Finsupp.single k 1
    · by_cases hk : c k = 0
      · have hc' : c' = c := by
          rw [h2]; exact config_sub_single_eq_self db c k hk
        have h3 : ¬ (c = c' + Finsupp.single k 1) := by
          rw [hc']; exact (config_add_single_ne_self db c k).symm
        have h4 : c = c' - Finsupp.single k 1 := by
          rw [hc']; exact (config_sub_single_eq_self db c k hk).symm
        have h5 : c' k = 0 := by rw [hc']; exact hk
        rw [if_neg h1, if_pos h2, if_pos hk, add_zero, if_neg h3, if_pos h4, if_pos h5,
          add_zero]
      · have h3 : c = c' + Finsupp.single k 1 := by
          rw [h2]; exact (config_sub_single_add_single db c k hk).symm
        have h4 : ¬ (c = c' - Finsupp.single k 1) := by
          intro hh
          have h5 := congrArg (fun f : Config db => f k) hh
          rw [coord_sub_single] at h5
          have h6 : c' k = c k - 1 := by
            rw [h2]; exact coord_sub_single db c k
          omega
        have h7 : c' k + 1 = c k := by
          have h6 : c' k = c k - 1 := by
            rw [h2]; exact coord_sub_single db c k
          omega
        rw [if_neg h1, if_pos h2, if_neg hk, zero_add, if_pos h3, if_neg h4, add_zero,
          h7]
    · have h3 : ¬ (c = c' + Finsupp.single k 1) := by
        intro hh
        have hce : c' = c - Finsupp.single k 1 := by
          rw [hh]; exact (config_add_single_sub_single db c' k).symm
        exact h2 hce
      have h4 : ¬ (c = c' - Finsupp.single k 1) := by
        intro hh
        by_cases hc'0 : c' k = 0
        · have e1 : c' - Finsupp.single k 1 = c' :=
            config_sub_single_eq_self db c' k hc'0
          have hc : c = c' := hh.trans e1
          have hce : c - Finsupp.single k 1 = c' := by rw [hc]; exact e1
          exact h2 hce.symm
        · have hce : c + Finsupp.single k 1 = c' := by
            rw [hh]; exact config_sub_single_add_single db c' k hc'0
          exact h1 hce.symm
      rw [if_neg h1, if_neg h2, add_zero, if_neg h3, if_neg h4, add_zero]

/-- **Field coefficient bound (CF2).** The field matrix element out of
any configuration is at most `sqrt (tot c' + 1)`, measured at the
OUTPUT configuration. -/
theorem norm_fieldMat_le (db : ℕ) (k : Fin db) (c' c : Config db) :
    ‖fieldMat db k c' c‖ ≤ Real.sqrt (bTot db c' + 1) := by
  by_cases hcre : c' = c + Finsupp.single k 1
  · have hsub : ¬ (c' = c - Finsupp.single k 1) := by
      rw [hcre]; exact config_add_ne_sub db c k
    rw [fieldMat, if_pos hcre, if_neg hsub, add_zero, norm_sqrtNat]
    apply Real.sqrt_le_sqrt
    have e : c' k = c k + 1 := by
      rw [hcre]; exact coord_add_single db c k
    have hle : c' k ≤ bTot db c' := config_le_bTot db c' k
    have h1 : ((c k + 1 : ℕ) : ℝ) ≤ (bTot db c' : ℝ) + 1 := by
      have h2 : ((c k + 1 : ℕ) : ℝ) = (c' k : ℝ) := by rw [← e]
      rw [h2]
      have hle' : (c' k : ℝ) ≤ (bTot db c' : ℝ) := by exact_mod_cast hle
      linarith
    exact h1
  · by_cases hsub : c' = c - Finsupp.single k 1
    · by_cases hk : c k = 0
      · rw [fieldMat, if_neg hcre, if_pos hsub, if_pos hk, add_zero, norm_zero]
        exact Real.sqrt_nonneg _
      · rw [fieldMat, if_neg hcre, if_pos hsub, if_neg hk, zero_add, norm_sqrtNat]
        apply Real.sqrt_le_sqrt
        have e : c' k = c k - 1 := by
          rw [hsub]; exact coord_sub_single db c k
        have hle : c' k ≤ bTot db c' := config_le_bTot db c' k
        have hck : c k = c' k + 1 := by omega
        have h1 : (c k : ℝ) ≤ (bTot db c' : ℝ) + 1 := by
          rw [hck]
          exact_mod_cast Nat.add_le_add_right hle 1
        exact h1
    · rw [fieldMat_eq_zero_of db k hcre (Or.inl hsub), norm_zero]
      exact Real.sqrt_nonneg _

/-! ### The coupled monomial's coefficient formula (CF1) -/

/-- **Coefficient formula for the coupled monomial (CF1).** The joint
matrix element of the Yukawa monomial factors:
fermionic density matrix element × bosonic field matrix element. -/
theorem yukMonoC_coeff (df db : ℕ) (i j : Fin df) (k : Fin db)
    (S' : Finset (Fin df)) (c' : Config db) (S : Finset (Fin df)) (c : Config db) :
    (yukMonoC df db i j k (Finsupp.single (S, c) 1)) (S', c')
      = densMat df i j S' S * fieldMat db k c' c := by
  rw [yukMonoC_single, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply]
  by_cases hphi : S' = densPhi df i j S
  · rw [densMat, if_pos hphi]
    by_cases hcre : c' = c + Finsupp.single k 1
    · have hsub : ¬ (c' = c - Finsupp.single k 1) := by
        rw [hcre]; exact config_add_ne_sub db c k
      have e1 : (Finsupp.single (densPhi df i j S, c + Finsupp.single k 1) (1 : ℂ))
          (S', c') = 1 := by
        rw [Finsupp.single_apply]
        exact if_pos (Prod.ext_iff.mpr ⟨hphi.symm, hcre.symm⟩)
      have e2 : (Finsupp.single (densPhi df i j S, c - Finsupp.single k 1) (1 : ℂ))
          (S', c') = 0 := by
        rw [Finsupp.single_apply]
        exact if_neg (fun h => hsub (Prod.ext_iff.mp h).2.symm)
      rw [fieldMat, if_pos hcre, if_neg hsub, add_zero, e1, e2, smul_zero, add_zero,
        smul_eq_mul, mul_one, one_mul]
    · by_cases hsub : c' = c - Finsupp.single k 1
      · by_cases hk : c k = 0
        · have hc' : c' = c := by
            rw [hsub]; exact config_sub_single_eq_self db c k hk
          have e1 : (Finsupp.single (densPhi df i j S, c + Finsupp.single k 1) (1 : ℂ))
              (S', c') = 0 := by
            rw [Finsupp.single_apply]
            exact if_neg (fun h => config_add_single_ne_self db c k
              ((Prod.ext_iff.mp h).2.trans hc'))
          rw [e1, smul_zero, zero_add, fieldMat, if_neg hcre, if_pos hsub, if_pos hk,
            add_zero, mul_zero, mul_zero, zero_smul]
        · have e1 : (Finsupp.single (densPhi df i j S, c + Finsupp.single k 1) (1 : ℂ))
              (S', c') = 0 := by
            rw [Finsupp.single_apply]
            exact if_neg (fun h => hcre (Prod.ext_iff.mp h).2.symm)
          have e2 : (Finsupp.single (densPhi df i j S, c - Finsupp.single k 1) (1 : ℂ))
              (S', c') = 1 := by
            rw [Finsupp.single_apply]
            exact if_pos (Prod.ext_iff.mpr ⟨hphi.symm, hsub.symm⟩)
          rw [fieldMat, if_neg hcre, if_pos hsub, if_neg hk, zero_add, e1, smul_zero,
            zero_add, e2, smul_eq_mul, mul_one, one_mul]
      · rw [fieldMat, if_neg hcre, if_neg hsub, add_zero, mul_zero]
        have e1 : (Finsupp.single (densPhi df i j S, c + Finsupp.single k 1) (1 : ℂ))
            (S', c') = 0 := by
          rw [Finsupp.single_apply]
          exact if_neg (fun h => hcre (Prod.ext_iff.mp h).2.symm)
        have e2 : (Finsupp.single (densPhi df i j S, c - Finsupp.single k 1) (1 : ℂ))
            (S', c') = 0 := by
          rw [Finsupp.single_apply]
          exact if_neg (fun h => hsub (Prod.ext_iff.mp h).2.symm)
        rw [e1, smul_zero, e2, smul_zero, add_zero]
  · rw [densMat, if_neg hphi, zero_mul]
    have e1 : (Finsupp.single (densPhi df i j S, c + Finsupp.single k 1) (1 : ℂ))
        (S', c') = 0 := by
      rw [Finsupp.single_apply]
      exact if_neg (fun h => hphi (Prod.ext_iff.mp h).1.symm)
    have e2 : (Finsupp.single (densPhi df i j S, c - Finsupp.single k 1) (1 : ℂ))
        (S', c') = 0 := by
      rw [Finsupp.single_apply]
      exact if_neg (fun h => hphi (Prod.ext_iff.mp h).1.symm)
    rw [e1, smul_zero, e2, smul_zero, add_zero]

/-! ### The symmetrized interaction and its total coefficient -/

/-- The adjoint coupling tensor: `adjY Y i j k = conj (Y j i k)`
(Pitch 3 symmetrization). -/
noncomputable def adjY (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ) :
    Fin df → Fin df → Fin db → ℂ :=
  fun i j k => (starRingEnd ℂ) (Y j i k)

theorem starRingEnd_adjY (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ)
    (i j : Fin df) (k : Fin db) :
    (starRingEnd ℂ) (adjY df db Y i j k) = Y j i k := by
  show (starRingEnd ℂ) ((starRingEnd ℂ) (Y j i k)) = Y j i k
  rw [starRingEnd_apply, starRingEnd_apply, star_star]

theorem yukFactor_adjoint (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ)
    (i j : Fin df) (k : Fin db) :
    (starRingEnd ℂ) (Y j i k + adjY df db Y j i k) = Y i j k + adjY df db Y i j k := by
  have h1 : (starRingEnd ℂ) (adjY df db Y j i k) = Y i j k :=
    starRingEnd_adjY df db Y j i k
  have h2 : adjY df db Y i j k = (starRingEnd ℂ) (Y j i k) := rfl
  rw [map_add, h1, h2, add_comm]

/-- The unsymmetrized Yukawa sum at the coefficient level. -/
noncomputable def yukawaSumC (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ) :
    (JointConfig df db →₀ ℂ) →ₗ[ℂ] (JointConfig df db →₀ ℂ) :=
  ∑ i, ∑ j, ∑ k, (Y i j k) • yukMonoC df db i j k

/-- The symmetrized Yukawa interaction at the coefficient level. -/
noncomputable def yukawaIntC (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ) :
    (JointConfig df db →₀ ℂ) →ₗ[ℂ] (JointConfig df db →₀ ℂ) :=
  yukawaSumC df db Y + yukawaSumC df db (adjY df db Y)

/-- The total coefficient of the symmetrized interaction. -/
noncomputable def yukCoefTot (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ)
    (S' : Finset (Fin df)) (c' : Config db) (S : Finset (Fin df)) (c : Config db) :
    ℂ :=
  ∑ i, ∑ j, ∑ k, (Y i j k + adjY df db Y i j k)
    * (densMat df i j S' S * fieldMat db k c' c)

/-- **Total coefficient formula.** The symmetrized interaction's joint
matrix element is the total coefficient. -/
theorem yukawaIntC_coeff (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ)
    (S' : Finset (Fin df)) (c' : Config db) (S : Finset (Fin df)) (c : Config db) :
    (yukawaIntC df db Y (Finsupp.single (S, c) 1)) (S', c')
      = yukCoefTot df db Y S' c' S c := by
  have hexpand : ∀ Z : Fin df → Fin df → Fin db → ℂ,
      (yukawaSumC df db Z (Finsupp.single (S, c) 1)) (S', c')
        = ∑ i, ∑ j, ∑ k, Z i j k * (densMat df i j S' S * fieldMat db k c' c) := by
    intro Z
    simp only [yukawaSumC, LinearMap.sum_apply, LinearMap.smul_apply,
      Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    rw [yukMonoC_coeff]
  rw [yukawaIntC, LinearMap.add_apply, Finsupp.add_apply, hexpand, hexpand, yukCoefTot,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  rw [← add_mul]

/-- **Total coefficient adjoint identity (CF3).** The total coefficient
of the symmetrized interaction is hermitian in the joint indices —
the algebraic heart of symmetry on the product domain. -/
theorem yukCoefTot_adjoint (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ)
    (S' : Finset (Fin df)) (c' : Config db) (S : Finset (Fin df)) (c : Config db) :
    (starRingEnd ℂ) (yukCoefTot df db Y S' c' S c)
      = yukCoefTot df db Y S c S' c' := by
  have per : ∀ i j : Fin df, ∀ k : Fin db,
      (starRingEnd ℂ) ((Y j i k + adjY df db Y j i k)
          * (densMat df j i S' S * fieldMat db k c' c))
        = (Y i j k + adjY df db Y i j k)
          * (densMat df i j S S' * fieldMat db k c c') := by
    intro i j k
    rw [map_mul, map_mul, yukFactor_adjoint, densMat_adjoint, fieldMat_adjoint]
  unfold yukCoefTot
  rw [Finset.sum_comm, map_sum]
  apply Finset.sum_congr rfl; intro x _
  rw [map_sum]
  apply Finset.sum_congr rfl; intro y _
  rw [map_sum]
  apply Finset.sum_congr rfl; intro k _
  exact per x y k

/-- Finite expansion of a joint coefficient vector over its support. -/
theorem jfinsupp_eq_sum_single (df db : ℕ) (f : JointConfig df db →₀ ℂ)
    (s : Finset (JointConfig df db)) (hs : ∀ q, f q ≠ 0 → q ∈ s) :
    f = ∑ q ∈ s, (f q) • Finsupp.single q 1 := by
  ext q'
  rw [Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single q']
  · rw [Finsupp.smul_apply, Finsupp.single_apply, if_pos rfl, smul_eq_mul, mul_one]
  · intro q _ hq
    rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg hq, smul_zero]
  · intro hq'
    by_cases hf : f q' = 0
    · rw [Finsupp.smul_apply, Finsupp.single_apply, if_pos rfl, smul_eq_mul, mul_one,
        hf]
    · exact absurd (hs q' hf) hq'

/-- The interaction applied to a general coefficient vector, as a
finite sum of total coefficients over the support. -/
theorem yukawaIntC_apply (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ)
    (f : JointConfig df db →₀ ℂ) (S' : Finset (Fin df)) (c' : Config db) :
    (yukawaIntC df db Y f) (S', c')
      = ∑ q ∈ f.support, f q * yukCoefTot df db Y S' c' q.1 q.2 := by
  conv_lhs => rw [jfinsupp_eq_sum_single df db f f.support
    (fun q hq => Finsupp.mem_support_iff.mpr hq)]
  rw [map_sum, Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  congr 1
  obtain ⟨S, c⟩ := q
  exact yukawaIntC_coeff df db Y S' c' S c


/-! ## §3. Transport to the product domain; free and total Hamiltonians

Coefficient-level operators are transported to `JDom df db` through the
representation equivalence. The free Hamiltonian is the joint diagonal
operator whose eigenvalue on `(S, c)` is the fermionic free eigenvalue
plus the bosonic number-weighted energy — the eigenvalues of the two
parents' free Hamiltonians, added on the product basis. -/

/-- Transport of a coefficient-level operator to the product domain. -/
noncomputable def jTransport (df db : ℕ)
    (F : (JointConfig df db →₀ ℂ) →ₗ[ℂ] (JointConfig df db →₀ ℂ)) :
    JDom df db →ₗ[ℂ] JDom df db :=
  (jEquiv df db).toLinearMap.comp (F.comp (jRepr df db).toLinearMap)

theorem jTransport_apply (df db : ℕ)
    (F : (JointConfig df db →₀ ℂ) →ₗ[ℂ] (JointConfig df db →₀ ℂ))
    (x : JDom df db) :
    jTransport df db F x = jEquiv df db (F (jRepr df db x)) := rfl

theorem jRepr_jEquiv (df db : ℕ) (f : JointConfig df db →₀ ℂ) :
    jRepr df db (jEquiv df db f) = f :=
  LinearEquiv.symm_apply_apply _ _

theorem jTransport_basis (df db : ℕ)
    (F : (JointConfig df db →₀ ℂ) →ₗ[ℂ] (JointConfig df db →₀ ℂ))
    (q : JointConfig df db) :
    jTransport df db F (jVec df db q)
      = jEquiv df db (F (Finsupp.single q 1)) := by
  rw [jTransport_apply, jRepr_jVec]

theorem jTransport_comp (df db : ℕ)
    (F G : (JointConfig df db →₀ ℂ) →ₗ[ℂ] (JointConfig df db →₀ ℂ)) :
    jTransport df db (F ∘ₗ G)
      = (jTransport df db F).comp (jTransport df db G) := by
  ext x
  simp only [jTransport_apply, LinearMap.comp_apply, jRepr_jEquiv]

theorem jTransport_add (df db : ℕ)
    (F G : (JointConfig df db →₀ ℂ) →ₗ[ℂ] (JointConfig df db →₀ ℂ)) :
    jTransport df db (F + G) = jTransport df db F + jTransport df db G := by
  ext x
  rw [LinearMap.add_apply, jTransport_apply, jTransport_apply, jTransport_apply,
    LinearMap.add_apply, map_add]

theorem jTransport_smul (df db : ℕ) (a : ℂ)
    (F : (JointConfig df db →₀ ℂ) →ₗ[ℂ] (JointConfig df db →₀ ℂ)) :
    jTransport df db (a • F) = a • jTransport df db F := by
  ext x
  rw [LinearMap.smul_apply, jTransport_apply, jTransport_apply, LinearMap.smul_apply,
    map_smul]

theorem jTransport_sum (df db : ℕ) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (F : ι → (JointConfig df db →₀ ℂ) →ₗ[ℂ] (JointConfig df db →₀ ℂ)) :
    jTransport df db (∑ i ∈ s, F i) = ∑ i ∈ s, jTransport df db (F i) := by
  induction s using Finset.induction with
  | empty =>
    ext x
    simp [jTransport_apply]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, jTransport_add, ih, Finset.sum_insert ha]

/-! ### The factor operators on the product domain -/

/-- Fermionic creation on the product domain: the transport of `fDagC`,
the product presentation of `adag i ⊗ 1`. -/
noncomputable def fDagJ (df db : ℕ) (i : Fin df) : JDom df db →ₗ[ℂ] JDom df db :=
  jTransport df db (fDagC df db i)

/-- Fermionic annihilation on the product domain: `ann i ⊗ 1`. -/
noncomputable def fAnnJ (df db : ℕ) (i : Fin df) : JDom df db →ₗ[ℂ] JDom df db :=
  jTransport df db (fAnnC df db i)

/-- Bosonic creation on the product domain: `1 ⊗ adagBos k`. -/
noncomputable def bDagJ (df db : ℕ) (k : Fin db) : JDom df db →ₗ[ℂ] JDom df db :=
  jTransport df db (bDagC df db k)

/-- Bosonic annihilation on the product domain: `1 ⊗ annBos k`. -/
noncomputable def bAnnJ (df db : ℕ) (k : Fin db) : JDom df db →ₗ[ℂ] JDom df db :=
  jTransport df db (bAnnC df db k)

/-- The density factor on the product domain: `(a†ᵢ aⱼ) ⊗ 1`. -/
noncomputable def densJ (df db : ℕ) (i j : Fin df) : JDom df db →ₗ[ℂ] JDom df db :=
  jTransport df db (densC df db i j)

/-- The field factor on the product domain: `1 ⊗ (a†ₖ + aₖ)`. -/
noncomputable def fieldJ (df db : ℕ) (k : Fin db) : JDom df db →ₗ[ℂ] JDom df db :=
  jTransport df db (fieldC df db k)

/-- The coupled monomial on the product domain. -/
noncomputable def yukMonoJ (df db : ℕ) (i j : Fin df) (k : Fin db) :
    JDom df db →ₗ[ℂ] JDom df db :=
  jTransport df db (yukMonoC df db i j k)

/-- The unsymmetrized Yukawa sum on the product domain. -/
noncomputable def yukawaSumJ (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ) :
    JDom df db →ₗ[ℂ] JDom df db :=
  jTransport df db (yukawaSumC df db Y)

/-- The symmetrized Yukawa interaction on the product domain. -/
noncomputable def yukawaIntJ (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ) :
    JDom df db →ₗ[ℂ] JDom df db :=
  jTransport df db (yukawaIntC df db Y)

theorem fDagJ_basis (df db : ℕ) (i : Fin df) (S : Finset (Fin df)) (c : Config db) :
    fDagJ df db i (jVec df db (S, c))
      = (if i ∈ S then 0 else sgn df i S) • jVec df db (insert i S, c) := by
  rw [fDagJ, jTransport_basis, fDagC_single, one_mul, map_smul, jEquiv_basis]

theorem fAnnJ_basis (df db : ℕ) (i : Fin df) (S : Finset (Fin df)) (c : Config db) :
    fAnnJ df db i (jVec df db (S, c))
      = if i ∉ S then 0 else sgn df i S • jVec df db (S.erase i, c) := by
  by_cases h : i ∈ S
  · have h2 : ¬ (i ∉ S) := by simp [h]
    rw [fAnnJ, jTransport_basis, fAnnC_single, if_neg h2, if_neg h2, one_mul,
      map_smul, jEquiv_basis]
  · have h2 : i ∉ S := h
    rw [fAnnJ, jTransport_basis, fAnnC_single, if_pos h2, if_pos h2, map_zero]

theorem bDagJ_basis (df db : ℕ) (k : Fin db) (S : Finset (Fin df)) (c : Config db) :
    bDagJ df db k (jVec df db (S, c))
      = sqrtNat (c k + 1) • jVec df db (S, c + Finsupp.single k 1) := by
  rw [bDagJ, jTransport_basis, bDagC_single, one_mul, map_smul, jEquiv_basis]

theorem bAnnJ_basis (df db : ℕ) (k : Fin db) (S : Finset (Fin df)) (c : Config db) :
    bAnnJ df db k (jVec df db (S, c))
      = (if c k = 0 then 0 else sqrtNat (c k))
          • jVec df db (S, c - Finsupp.single k 1) := by
  rw [bAnnJ, jTransport_basis, bAnnC_single, one_mul, map_smul, jEquiv_basis]

theorem densJ_basis (df db : ℕ) (i j : Fin df) (S : Finset (Fin df)) (c : Config db) :
    densJ df db i j (jVec df db (S, c))
      = densCoef df i j S • jVec df db (densPhi df i j S, c) := by
  rw [densJ, jTransport_basis, densC_single, one_mul, map_smul, jEquiv_basis]

theorem fieldJ_basis (df db : ℕ) (k : Fin db) (S : Finset (Fin df)) (c : Config db) :
    fieldJ df db k (jVec df db (S, c))
      = sqrtNat (c k + 1) • jVec df db (S, c + Finsupp.single k 1)
        + (if c k = 0 then 0 else sqrtNat (c k))
            • jVec df db (S, c - Finsupp.single k 1) := by
  simp only [fieldJ, jTransport_basis, fieldC_single, one_mul, map_add, map_smul,
    jEquiv_basis]

/-- The interaction's joint matrix element, read off by pairing with a
basis vector: it is the total coefficient of §2. -/
theorem yukawaIntJ_coord (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ)
    (S : Finset (Fin df)) (c : Config db) (S' : Finset (Fin df)) (c' : Config db) :
    ⟪jE df db (S', c'), ((yukawaIntJ df db Y (jVec df db (S, c)) : JDom df db)
      : JointSpace df db)⟫_ℂ
      = yukCoefTot df db Y S' c' S c := by
  rw [yukawaIntJ, jTransport_apply, jRepr_jVec, jcoord, jRepr_jEquiv,
    yukawaIntC_coeff]

/-! ### The diagonal coefficient operator and the free Hamiltonian -/

/-- The diagonal coefficient operator with eigenvalue function `r`. -/
noncomputable def diagC (df db : ℕ) (r : JointConfig df db → ℂ) :
    (JointConfig df db →₀ ℂ) →ₗ[ℂ] (JointConfig df db →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun q => (r q) • Finsupp.single q 1

theorem diagC_single (df db : ℕ) (r : JointConfig df db → ℂ)
    (q : JointConfig df db) (a : ℂ) :
    diagC df db r (Finsupp.single q a) = (a * r q) • Finsupp.single q 1 := by
  simp only [diagC, Finsupp.linearCombination_single, ← mul_smul]

theorem diagC_apply (df db : ℕ) (r : JointConfig df db → ℂ)
    (f : JointConfig df db →₀ ℂ) (q : JointConfig df db) :
    (diagC df db r f) q = r q * f q := by
  have key : ∀ q₀ : JointConfig df db,
      (diagC df db r (Finsupp.single q₀ 1)) q = if q₀ = q then r q₀ else 0 := by
    intro q₀
    rw [diagC_single, one_mul, smul_single_one, Finsupp.single_apply]
  have hterm : ∀ q₀ ∈ f.support, (diagC df db r (f q₀ • Finsupp.single q₀ 1)) q
      = if q = q₀ then r q * f q else 0 := by
    intro q₀ _
    rw [map_smul, Finsupp.smul_apply, key]
    by_cases h : q₀ = q
    · rw [if_pos h, if_pos h.symm, h, smul_eq_mul, mul_comm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm), smul_zero]
  conv_lhs => rw [jfinsupp_eq_sum_single df db f f.support
    (fun q hq => Finsupp.mem_support_iff.mpr hq)]
  rw [map_sum, Finsupp.finset_sum_apply, Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq]
  by_cases hq : q ∈ f.support
  · rw [if_pos hq]
  · rw [if_neg hq, Finsupp.notMem_support_iff.mp hq, mul_zero]

/-- The bosonic free eigenvalue: number-weighted mode energies. -/
noncomputable def boseEig (db : ℕ) (omB : Fin db → ℝ) (c : Config db) : ℝ :=
  ∑ k, omB k * (c k : ℝ)

/-- The joint free eigenvalue on a product configuration: the fermionic
free eigenvalue plus the bosonic free eigenvalue. -/
noncomputable def jointEigR (df db : ℕ) (lamF : Fin df → ℝ) (omB : Fin db → ℝ)
    (q : JointConfig df db) : ℝ :=
  freeEig df lamF q.1 + boseEig db omB q.2

/-- On the bosonic vacuum the joint eigenvalue is the parents'
fermionic free eigenvalue — the honesty link to `FermionicInteraction`. -/
theorem jointEigR_fst (df db : ℕ) (lamF : Fin df → ℝ) (omB : Fin db → ℝ)
    (S : Finset (Fin df)) :
    jointEigR df db lamF omB (S, 0) = freeEig df lamF S := by
  simp [jointEigR, boseEig]

/-- On the fermionic vacuum the joint eigenvalue is the bosonic free
eigenvalue. -/
theorem jointEigR_snd (df db : ℕ) (lamF : Fin df → ℝ) (omB : Fin db → ℝ)
    (c : Config db) :
    jointEigR df db lamF omB (∅, c) = boseEig db omB c := by
  simp [jointEigR, freeEig]

/-- The joint free Hamiltonian on the product domain: the diagonal
operator with eigenvalues `jointEigR`. -/
noncomputable def hamFreeJ (df db : ℕ) (lamF : Fin df → ℝ) (omB : Fin db → ℝ) :
    JDom df db →ₗ[ℂ] JDom df db :=
  jTransport df db (diagC df db fun q => ((jointEigR df db lamF omB q : ℝ) : ℂ))

theorem hamFreeJ_basis (df db : ℕ) (lamF : Fin df → ℝ) (omB : Fin db → ℝ)
    (q : JointConfig df db) :
    hamFreeJ df db lamF omB (jVec df db q)
      = ((jointEigR df db lamF omB q : ℝ) : ℂ) • jVec df db q := by
  rw [hamFreeJ, jTransport_basis, diagC_single, one_mul, map_smul, jEquiv_basis]

/-- The total Hamiltonian on the product domain:
`H = H_free + g • H_Y`. The coupling `g` is REAL, as in both Pitch 3
campaigns: for complex `g` the operator would not be symmetric (the
two inner-product slots produce `conj g` and `g`). -/
noncomputable def hamYuk (df db : ℕ) (lamF : Fin df → ℝ) (omB : Fin db → ℝ)
    (Y : Fin df → Fin df → Fin db → ℂ) (g : ℝ) :
    JDom df db →ₗ[ℂ] JDom df db :=
  hamFreeJ df db lamF omB + (g : ℂ) • yukawaIntJ df db Y

theorem hamYuk_apply (df db : ℕ) (lamF : Fin df → ℝ) (omB : Fin db → ℝ)
    (Y : Fin df → Fin df → Fin db → ℂ) (g : ℝ) (x : JDom df db) :
    hamYuk df db lamF omB Y g x
      = hamFreeJ df db lamF omB x + (g : ℂ) • yukawaIntJ df db Y x := rfl

theorem hamYuk_zero (df db : ℕ) (lamF : Fin df → ℝ) (omB : Fin db → ℝ)
    (Y : Fin df → Fin df → Fin db → ℂ) :
    hamYuk df db lamF omB Y 0 = hamFreeJ df db lamF omB := by
  simp [hamYuk]

/-- The total Hamiltonian's joint matrix element: the free eigenvalue
on the diagonal plus `g` times the total Yukawa coefficient. -/
theorem hamYuk_coord (df db : ℕ) (lamF : Fin df → ℝ) (omB : Fin db → ℝ)
    (Y : Fin df → Fin df → Fin db → ℂ) (g : ℝ)
    (S : Finset (Fin df)) (c : Config db) (S' : Finset (Fin df)) (c' : Config db) :
    ⟪jE df db (S', c'), ((hamYuk df db lamF omB Y g (jVec df db (S, c)) : JDom df db)
      : JointSpace df db)⟫_ℂ
      = (if (S', c') = (S, c)
          then ((jointEigR df db lamF omB (S, c) : ℝ) : ℂ) else 0)
        + (g : ℂ) * yukCoefTot df db Y S' c' S c := by
  have h1 : ⟪jE df db (S', c'), ((hamFreeJ df db lamF omB (jVec df db (S, c))
        : JDom df db) : JointSpace df db)⟫_ℂ
      = if (S', c') = (S, c)
          then ((jointEigR df db lamF omB (S, c) : ℝ) : ℂ) else 0 := by
    rw [hamFreeJ_basis]
    show ⟪jE df db (S', c'), ((jointEigR df db lamF omB (S, c) : ℝ) : ℂ)
        • jE df db (S, c)⟫_ℂ = _
    rw [inner_smul_right, jE_inner, mul_ite, mul_one, mul_zero]
  have h2 : ⟪jE df db (S', c'), ((yukawaIntJ df db Y (jVec df db (S, c))
        : JDom df db) : JointSpace df db)⟫_ℂ
      = yukCoefTot df db Y S' c' S c := yukawaIntJ_coord df db Y S c S' c'
  rw [hamYuk_apply]
  show ⟪jE df db (S', c'), (((hamFreeJ df db lamF omB (jVec df db (S, c))
        + (g : ℂ) • yukawaIntJ df db Y (jVec df db (S, c)) : JDom df db))
      : JointSpace df db)⟫_ℂ = _
  show ⟪jE df db (S', c'), ((hamFreeJ df db lamF omB (jVec df db (S, c))
        : JDom df db) : JointSpace df db)
      + (g : ℂ) • ((yukawaIntJ df db Y (jVec df db (S, c)) : JDom df db)
        : JointSpace df db)⟫_ℂ = _
  rw [inner_add_right, inner_smul_right, h1, h2]

/-! ## §4. Symmetry on the product domain; scoped self-adjointness

Symmetry is proved once for every transported operator whose
coefficient matrix elements are hermitian, by double induction on the
product domain; the interaction (via CF3) and the free Hamiltonian
(via the real diagonal) are the two instances. The self-adjointness
content is Pitch 3's scoped package: symmetry on the dense product
domain, the formal-adjoint inclusion for the partial map, and the
finite-dimensional spectral theorem on bosonic bands for the free
part — the interaction maps band `N` into band `N + 1` (it does NOT
preserve bosonic number sectors: the field changes the total boson
number by ±1). Essential self-adjointness is NOT claimed; see the
header fence. -/

/-- The domain basis vector coerces to the ambient basis vector. -/
theorem jVec_coe (df db : ℕ) (q : JointConfig df db) :
    ((jVec df db q : JDom df db) : JointSpace df db) = jE df db q := rfl

/-- **Generic symmetry of transported operators.** If a coefficient
operator's basis matrix elements are hermitian, its transport to the
product domain is symmetric. -/
theorem jTransport_isSymmetric (df db : ℕ)
    (F : (JointConfig df db →₀ ℂ) →ₗ[ℂ] (JointConfig df db →₀ ℂ))
    (hF : ∀ q q' : JointConfig df db,
      (starRingEnd ℂ) ((F (Finsupp.single q 1)) q') = (F (Finsupp.single q' 1)) q)
    (x y : JDom df db) :
    ⟪((jTransport df db F x : JDom df db) : JointSpace df db),
      (y : JointSpace df db)⟫_ℂ
      = ⟪(x : JointSpace df db), ((jTransport df db F y : JDom df db)
          : JointSpace df db)⟫_ℂ := by
  induction x, y using JDom_induction₂ with
  | base q q' =>
    have eL : ⟪((jTransport df db F (jVec df db q) : JDom df db) : JointSpace df db),
        ((jVec df db q' : JDom df db) : JointSpace df db)⟫_ℂ
        = (starRingEnd ℂ) ((F (Finsupp.single q 1)) q') := by
      rw [jTransport_basis, jVec_coe, ← inner_conj_symm, jcoord, jRepr_jEquiv]
    have eR : ⟪((jVec df db q : JDom df db) : JointSpace df db),
        ((jTransport df db F (jVec df db q') : JDom df db) : JointSpace df db)⟫_ℂ
        = (F (Finsupp.single q' 1)) q := by
      rw [jTransport_basis, jVec_coe, jcoord, jRepr_jEquiv]
    rw [eL, eR]
    exact hF q q'
  | add₁ x x' y ih1 ih2 =>
    rw [map_add, Submodule.coe_add, Submodule.coe_add, inner_add_left,
      inner_add_left, ih1, ih2]
  | zero₁ y =>
    rw [map_zero, Submodule.coe_zero, inner_zero_left, inner_zero_left]
  | smul₁ a x y ih =>
    rw [map_smul, Submodule.coe_smul, Submodule.coe_smul, inner_smul_left,
      inner_smul_left, ih]
  | add₂ x y y' ih1 ih2 =>
    rw [map_add, Submodule.coe_add, Submodule.coe_add, inner_add_right,
      inner_add_right, ih1, ih2]
  | zero₂ x =>
    rw [map_zero, Submodule.coe_zero, inner_zero_right, inner_zero_right]
  | smul₂ a x y ih =>
    rw [map_smul, Submodule.coe_smul, Submodule.coe_smul, inner_smul_right,
      inner_smul_right, ih]

/-- **Symmetry of the Yukawa interaction (rung (c), interaction part).**
On the product finite-particle domain, via CF3. -/
theorem yukawaIntJ_isSymmetric (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ)
    (x y : JDom df db) :
    ⟪((yukawaIntJ df db Y x : JDom df db) : JointSpace df db),
      (y : JointSpace df db)⟫_ℂ
      = ⟪(x : JointSpace df db), ((yukawaIntJ df db Y y : JDom df db)
          : JointSpace df db)⟫_ℂ :=
  jTransport_isSymmetric df db (yukawaIntC df db Y) (fun q q' => by
    obtain ⟨S, c⟩ := q
    obtain ⟨S', c'⟩ := q'
    rw [yukawaIntC_coeff, yukawaIntC_coeff, yukCoefTot_adjoint]) x y

/-- **Symmetry of the joint free Hamiltonian.** Its eigenvalues are
real, so its coefficient matrix elements are hermitian. -/
theorem hamFreeJ_isSymmetric (df db : ℕ) (lamF : Fin df → ℝ) (omB : Fin db → ℝ)
    (x y : JDom df db) :
    ⟪((hamFreeJ df db lamF omB x : JDom df db) : JointSpace df db),
      (y : JointSpace df db)⟫_ℂ
      = ⟪(x : JointSpace df db), ((hamFreeJ df db lamF omB y : JDom df db)
          : JointSpace df db)⟫_ℂ :=
  jTransport_isSymmetric df db
    (diagC df db fun q => ((jointEigR df db lamF omB q : ℝ) : ℂ)) (fun q q' => by
      rw [diagC_apply, diagC_apply, Finsupp.single_apply, Finsupp.single_apply]
      by_cases h : q = q'
      · rw [if_pos h, if_pos h.symm, h, map_mul, Complex.conj_ofReal, map_one,
          mul_one]
      · rw [if_neg h, if_neg (fun hh => h hh.symm), mul_zero, mul_zero,
          map_zero]) x y

/-- **Symmetry of the total Hamiltonian (rung (c)).** On the product
finite-particle domain, for every real coupling `g`. -/
theorem hamYuk_isSymmetric (df db : ℕ) (lamF : Fin df → ℝ) (omB : Fin db → ℝ)
    (Y : Fin df → Fin df → Fin db → ℂ) (g : ℝ) (x y : JDom df db) :
    ⟪((hamYuk df db lamF omB Y g x : JDom df db) : JointSpace df db),
      (y : JointSpace df db)⟫_ℂ
      = ⟪(x : JointSpace df db), ((hamYuk df db lamF omB Y g y : JDom df db)
          : JointSpace df db)⟫_ℂ := by
  rw [hamYuk_apply, hamYuk_apply]
  show ⟪((hamFreeJ df db lamF omB x : JDom df db) : JointSpace df db)
        + (g : ℂ) • ((yukawaIntJ df db Y x : JDom df db) : JointSpace df db),
      (y : JointSpace df db)⟫_ℂ
    = ⟪(x : JointSpace df db),
        ((hamFreeJ df db lamF omB y : JDom df db) : JointSpace df db)
        + (g : ℂ) • ((yukawaIntJ df db Y y : JDom df db) : JointSpace df db)⟫_ℂ
  rw [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    hamFreeJ_isSymmetric, yukawaIntJ_isSymmetric, Complex.conj_ofReal]

/-- The product finite-particle domain is dense in the joint space. -/
theorem jDom_topologicalClosure (df db : ℕ) :
    (JDom df db).topologicalClosure = ⊤ := by
  have h := lp_single_span_topologicalClosure (JointConfig df db)
  exact h

/-- The product finite-particle domain is dense (set form). -/
theorem jDom_dense (df db : ℕ) :
    Dense ((JDom df db : Set (JointSpace df db))) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr (jDom_topologicalClosure df db)

/-- The total Hamiltonian as a partially defined linear map on the
whole joint space, with domain the product finite-particle domain. -/
noncomputable def hamYukPMap (df db : ℕ) (lamF : Fin df → ℝ) (omB : Fin db → ℝ)
    (Y : Fin df → Fin df → Fin db → ℂ) (g : ℝ) :
    JointSpace df db →ₗ.[ℂ] JointSpace df db where
  domain := JDom df db
  toFun := (JDom df db).subtype ∘ₗ hamYuk df db lamF omB Y g

/-- **The Hamiltonian partial map is a formal adjoint of itself
(rung (e), partial-map sense).** -/
theorem hamYukPMap_isFormalAdjoint (df db : ℕ) (lamF : Fin df → ℝ)
    (omB : Fin db → ℝ) (Y : Fin df → Fin df → Fin db → ℂ) (g : ℝ) :
    (hamYukPMap df db lamF omB Y g).IsFormalAdjoint
      (hamYukPMap df db lamF omB Y g) := by
  intro x y
  exact hamYuk_isSymmetric df db lamF omB Y g x y

/-- Consequently `H ≤ H†` in the partial-map order: the operator is
contained in its adjoint — the maximal self-adjointness statement the
`LinearPMap` API expresses without a closure operation. Essential
self-adjointness is the priced remainder (header fence). -/
theorem hamYukPMap_le_adjoint (df db : ℕ) (lamF : Fin df → ℝ) (omB : Fin db → ℝ)
    (Y : Fin df → Fin df → Fin db → ℂ) (g : ℝ) :
    hamYukPMap df db lamF omB Y g
      ≤ LinearPMap.adjoint (hamYukPMap df db lamF omB Y g) :=
  (hamYukPMap_isFormalAdjoint df db lamF omB Y g).le_adjoint (jDom_dense df db)

/-! ### Bosonic bands: the finite-dimensional sectors of this brick -/

/-- Finite expansion of a domain element over its coefficient support. -/
theorem jEquiv_expand (df db : ℕ) (f : JointConfig df db →₀ ℂ) :
    jEquiv df db f = ∑ q ∈ f.support, (f q) • jVec df db q := by
  apply (jRepr df db).injective
  rw [jRepr_jEquiv, map_sum,
    show (∑ q ∈ f.support, (jRepr df db) ((f q) • jVec df db q))
        = ∑ q ∈ f.support, (f q) • Finsupp.single q 1 from
      Finset.sum_congr rfl (fun q _ => by rw [map_smul, jRepr_jVec])]
  exact jfinsupp_eq_sum_single df db f f.support
    (fun q hq => Finsupp.mem_support_iff.mpr hq)

/-- The bosonic band of order `N`: domain vectors whose coefficients
vanish at every configuration of total boson number `> N`. (The
fermionic factor ranges over a finite type anyway, so bands are
finite-dimensional.) The interaction does NOT preserve bands — the
field shifts the total boson number by ±1 — so bands are the honest
finite-dimensional sectors of this brick: the free Hamiltonian
preserves them, the interaction maps band `N` into band `N + 1`. -/
noncomputable def jBand (df db : ℕ) (N : ℕ) : Submodule ℂ (JDom df db) where
  carrier := {x | ∀ q : JointConfig df db, N < bTot db q.2
    → (jRepr df db x) q = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy q hq
    simp [map_add, Finsupp.add_apply, hx q hq, hy q hq]
  smul_mem' := by
    intro a x hx q hq
    simp [map_smul, Finsupp.smul_apply, hx q hq]

theorem mem_jBand_iff (df db : ℕ) (N : ℕ) (x : JDom df db) :
    x ∈ jBand df db N
      ↔ ∀ q : JointConfig df db, N < bTot db q.2 → (jRepr df db x) q = 0 :=
  Iff.rfl

/-- The band is spanned by the basis vectors inside the band. -/
theorem jBand_eq_span (df db : ℕ) (N : ℕ) :
    jBand df db N = Submodule.span ℂ {x : JDom df db | ∃ q : JointConfig df db,
      bTot db q.2 ≤ N ∧ x = jVec df db q} := by
  apply le_antisymm
  · intro x hx
    rw [mem_jBand_iff] at hx
    have hx2 : x = jEquiv df db (jRepr df db x) :=
      (LinearEquiv.apply_symm_apply _ _).symm
    rw [hx2, jEquiv_expand]
    apply sum_mem
    intro q _
    by_cases hq0 : (jRepr df db x) q = 0
    · rw [hq0, zero_smul]
      exact Submodule.zero_mem _
    · have hTot : bTot db q.2 ≤ N := by
        by_contra hle
        push_neg at hle
        exact hq0 (hx q hle)
      exact Submodule.smul_mem _ ((jRepr df db x) q)
        (Submodule.subset_span ⟨q, hTot, rfl⟩)
  · apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨q, hq, rfl⟩ := hx
    show jVec df db q ∈ jBand df db N
    rw [mem_jBand_iff]
    intro q' hq'
    rw [jRepr_jVec, Finsupp.single_apply]
    by_cases h : q = q'
    · subst h
      exact absurd hq' (not_lt.mpr hq)
    · rw [if_neg h]

/-- Configurations in a band form a finite type. -/
theorem finite_setOf_tot_le (df db : ℕ) (N : ℕ) :
    Finite {q : JointConfig df db // bTot db q.2 ≤ N} := by
  apply Finite.of_injective
    (fun q : {q : JointConfig df db // bTot db q.2 ≤ N} =>
      (q.1.1, fun k => (⟨q.1.2 k, Nat.lt_succ_iff.mpr
        ((config_le_bTot db q.1.2 k).trans q.2)⟩ : Fin (N + 1))))
  intro q₁ q₂ h
  have h' : (q₁.1.1, fun k => (⟨q₁.1.2 k, Nat.lt_succ_iff.mpr
        ((config_le_bTot db q₁.1.2 k).trans q₁.2)⟩ : Fin (N + 1)))
      = (q₂.1.1, fun k => (⟨q₂.1.2 k, Nat.lt_succ_iff.mpr
        ((config_le_bTot db q₂.1.2 k).trans q₂.2)⟩ : Fin (N + 1))) := h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h'
  apply Subtype.ext
  exact Prod.ext h1 (Finsupp.ext fun k => congrArg Fin.val (congrFun h2 k))

/-- Bands are finite-dimensional. -/
theorem jBand_finiteDimensional (df db : ℕ) (N : ℕ) :
    FiniteDimensional ℂ (jBand df db N) := by
  haveI := finite_setOf_tot_le df db N
  have hset : {x : JDom df db | ∃ q : JointConfig df db, bTot db q.2 ≤ N
        ∧ x = jVec df db q}
      = Set.range (fun q : {q : JointConfig df db // bTot db q.2 ≤ N} =>
          jVec df db q.1) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
    · rintro ⟨⟨q, hq⟩, rfl⟩
      exact ⟨q, hq, rfl⟩
  rw [jBand_eq_span, hset]
  exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

/-- The free Hamiltonian preserves every band (it is diagonal). -/
theorem hamFreeJ_mem_jBand (df db : ℕ) (lamF : Fin df → ℝ) (omB : Fin db → ℝ)
    (N : ℕ) (x : JDom df db) (hx : x ∈ jBand df db N) :
    hamFreeJ df db lamF omB x ∈ jBand df db N := by
  rw [mem_jBand_iff] at hx ⊢
  intro q hq
  have e : jRepr df db (hamFreeJ df db lamF omB x)
      = diagC df db (fun q => ((jointEigR df db lamF omB q : ℝ) : ℂ))
        (jRepr df db x) := by
    rw [hamFreeJ, jTransport_apply, jRepr_jEquiv]
  rw [e, diagC_apply, hx q hq, mul_zero]

/-- A nonzero field matrix element raises the total boson number by
at most one. -/
theorem bTot_le_of_fieldMat_ne (db : ℕ) (k : Fin db) {c' c : Config db}
    (h : fieldMat db k c' c ≠ 0) : bTot db c' ≤ bTot db c + 1 := by
  by_contra hcon
  push_neg at hcon
  apply h
  apply fieldMat_eq_zero_of db k
  · intro he
    rw [he, bTot_add_single] at hcon
    omega
  · left
    intro he
    rw [he] at hcon
    have hle := bTot_sub_single_le db c k
    omega

/-- The interaction maps band `N` into band `N + 1` — the banded form
of the statement that the field changes the total boson number by at
most one. It does NOT preserve band `N` (creation raises the number),
so there is no sectorwise spectral theorem for `H` itself in this
brick; see the header. -/
theorem yukawaIntJ_mem_jBand (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ)
    (N : ℕ) (x : JDom df db) (hx : x ∈ jBand df db N) :
    yukawaIntJ df db Y x ∈ jBand df db (N + 1) := by
  rw [mem_jBand_iff] at hx ⊢
  intro q' hq'
  have e : jRepr df db (yukawaIntJ df db Y x)
      = yukawaIntC df db Y (jRepr df db x) := by
    rw [yukawaIntJ, jTransport_apply, jRepr_jEquiv]
  rw [e]
  obtain ⟨S', c'⟩ := q'
  have hq'2 : N + 1 < bTot db c' := hq'
  rw [yukawaIntC_apply]
  apply Finset.sum_eq_zero
  intro q _
  obtain ⟨S, c⟩ := q
  dsimp only
  by_cases hcoef : yukCoefTot df db Y S' c' S c = 0
  · rw [hcoef, mul_zero]
  · have hfm : ∃ k : Fin db, fieldMat db k c' c ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hcoef
      rw [yukCoefTot]
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      apply Finset.sum_eq_zero
      intro k _
      rw [hall k, mul_zero, mul_zero]
    obtain ⟨k, hk⟩ := hfm
    have hle := bTot_le_of_fieldMat_ne db k hk
    have hcN : N < bTot db c := by omega
    rw [hx (S, c) hcN, zero_mul]

/-- The free Hamiltonian restricted to a band: a finite-dimensional
endomorphism of the band. -/
noncomputable def hamFreeJBand (df db : ℕ) (lamF : Fin df → ℝ) (omB : Fin db → ℝ)
    (N : ℕ) : (jBand df db N) →ₗ[ℂ] (jBand df db N) :=
  (hamFreeJ df db lamF omB).restrict
    (fun x hx => hamFreeJ_mem_jBand df db lamF omB N x hx)

/-- The band restriction of the free Hamiltonian is symmetric. -/
theorem hamFreeJBand_isSymmetric (df db : ℕ) (lamF : Fin df → ℝ)
    (omB : Fin db → ℝ) (N : ℕ) :
    @LinearMap.IsSymmetric ℂ (↥(jBand df db N)) _ _ _
      (hamFreeJBand df db lamF omB N) := by
  intro x y
  exact hamFreeJ_isSymmetric df db lamF omB x y

set_option maxHeartbeats 3200000 in
/-- A joint basis vector whose bosonic total lies in the band lies in
the band. -/
theorem jVec_mem_jBand (df db : ℕ) (N : ℕ) (q : JointConfig df db)
    (hq : bTot db q.2 ≤ N) : jVec df db q ∈ jBand df db N := by
  rw [mem_jBand_iff]
  intro q' hq'
  rw [jRepr_jVec, Finsupp.single_apply]
  by_cases h : q = q'
  · subst h
    exact absurd hq' (not_lt.mpr hq)
  · rw [if_neg h]

/-- The band's own basis vector at a band configuration. -/
noncomputable def jBandVec (df db : ℕ) (N : ℕ)
    (q : {q : JointConfig df db // bTot db q.2 ≤ N}) : jBand df db N :=
  ⟨jVec df db q.1, jVec_mem_jBand df db N q.1 q.2⟩

theorem jBandVec_coe (df db : ℕ) (N : ℕ)
    (q : {q : JointConfig df db // bTot db q.2 ≤ N}) :
    ((jBandVec df db N q : jBand df db N) : JDom df db) = jVec df db q.1 :=
  rfl

/-- The band family is orthonormal in the band. -/
theorem jBandVec_orthonormal (df db : ℕ) (N : ℕ) :
    Orthonormal ℂ (jBandVec df db N) := by
  rw [orthonormal_iff_ite]
  intro q q'
  show ⟪jE df db q.1, jE df db q'.1⟫_ℂ = (if q = q' then (1 : ℂ) else 0)
  rw [jE_inner]
  by_cases h : q = q'
  · subst h
    rw [if_pos rfl, if_pos rfl]
  · have h1 : q.1 ≠ q'.1 := fun hh => h (Subtype.ext hh)
    rw [if_neg h, if_neg h1]

/-- The band family is linearly independent. -/
theorem jBandVec_linearIndependent (df db : ℕ) (N : ℕ) :
    LinearIndependent ℂ (jBandVec df db N) := by
  have hcomp : (JDom df db).subtype ∘
      (fun q : {q : JointConfig df db // bTot db q.2 ≤ N} => jVec df db q.1)
      = jE df db ∘ Subtype.val := by
    funext q
    rfl
  have h1 : LinearIndependent ℂ
      (fun q : {q : JointConfig df db // bTot db q.2 ≤ N} =>
        jVec df db q.1) := by
    apply LinearIndependent.of_comp (JDom df db).subtype
    rw [hcomp]
    exact (jLinIndep df db).comp Subtype.val Subtype.val_injective
  exact h1.of_comp (jBand df db N).subtype

/-- The band family spans the band. -/
theorem jBandVec_span (df db : ℕ) (N : ℕ) :
    Submodule.span ℂ (Set.range (jBandVec df db N)) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  obtain ⟨z, hzJ⟩ := x
  rw [jBand_eq_span] at hzJ
  induction hzJ using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨q, hq, rfl⟩ := hz
    exact Submodule.subset_span ⟨⟨q, hq⟩, Subtype.ext rfl⟩
  | zero => exact Submodule.zero_mem _
  | add z₁ z₂ hz₁ hz₂ ih1 ih2 =>
    exact Submodule.add_mem _ (ih1 (jBand_eq_span df db N ▸ hz₁))
      (ih2 (jBand_eq_span df db N ▸ hz₂))
  | smul a z hz ih =>
    exact Submodule.smul_mem _ a (ih (jBand_eq_span df db N ▸ hz))

/-- The band basis: the joint basis restricted to the band. -/
noncomputable def jBandBasis (df db : ℕ) (N : ℕ) :
    Module.Basis {q : JointConfig df db // bTot db q.2 ≤ N} ℂ
      (jBand df db N) :=
  Module.Basis.mk (jBandVec_linearIndependent df db N)
    (le_of_eq (jBandVec_span df db N).symm)

/-- The band basis is orthonormal. -/
theorem jBandBasis_orthonormal (df db : ℕ) (N : ℕ) :
    Orthonormal ℂ (jBandBasis df db N) := by
  rw [jBandBasis, Module.Basis.coe_mk]
  exact jBandVec_orthonormal df db N

/-- The band basis vector at a band configuration is the joint basis
vector. -/
theorem jBandBasis_coe (df db : ℕ) (N : ℕ)
    (q : {q : JointConfig df db // bTot db q.2 ≤ N}) :
    ((jBandBasis df db N q : jBand df db N) : JDom df db)
      = jVec df db q.1 := by
  rw [jBandBasis, Module.Basis.coe_mk]
  exact jBandVec_coe df db N q

theorem hamFreeJBand_coe (df db : ℕ) (lamF : Fin df → ℝ) (omB : Fin db → ℝ)
    (N : ℕ) (x : jBand df db N) :
    ((hamFreeJBand df db lamF omB N x : jBand df db N) : JDom df db)
      = hamFreeJ df db lamF omB (x : JDom df db) :=
  rfl

/-- **Bandwise spectral theorem for the free Hamiltonian (rung (e),
sectorwise sense), with the eigenbasis EXHIBITED**: the band basis
(`jBandBasis`, proved orthonormal in `jBandBasis_orthonormal`)
diagonalizes the band restriction of the free Hamiltonian, with
eigenvalues the joint free eigenvalues. -/
theorem hamFreeJBand_spectral (df db : ℕ) (lamF : Fin df → ℝ)
    (omB : Fin db → ℝ) (N : ℕ)
    (q : {q : JointConfig df db // bTot db q.2 ≤ N}) :
    hamFreeJBand df db lamF omB N (jBandBasis df db N q)
      = ((jointEigR df db lamF omB q.1 : ℝ) : ℂ)
        • (jBandBasis df db N q) := by
  apply Subtype.ext
  rw [hamFreeJBand_coe, Submodule.coe_smul, jBandBasis_coe]
  exact hamFreeJ_basis df db lamF omB q.1


/-! ## §5. Relative bounds and windowed gap persistence

The interaction's coordinate bound is output-side: at output
configuration `(S', c')` every matrix element is at most
`yukBound Y * sqrt (bTot c' + 1)`, and for a fixed output only the
two bosonic preimages `c' ∓ single k 1` (one per sign of the field)
and the single fermionic preimage `densPre` contribute — the
two-point support argument, the product form of Campaign 1's column
sum. The eigenvalue transport at a maximal coefficient then gives
windowed gap persistence in Campaign 2's form: the window (the
bosonic band `N`) is in the hypotheses from line one, because uniform
persistence is false (header fence). -/

/-- The coupling mass of the Yukawa tensor: the sum of the norms of
all its entries. -/
noncomputable def yukMass (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ‖Y i j k‖

/-- The explicit interaction bound constant: `4 * yukMass` — two from
the symmetrization (`Y` and its adjoint), two from the field's two
preimages per output. -/
noncomputable def yukBound (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ) : ℝ :=
  4 * yukMass df db Y

theorem yukMass_nonneg (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ) :
    0 ≤ yukMass df db Y := by
  rw [yukMass]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro k _
  exact norm_nonneg _

theorem yukBound_nonneg (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ) :
    0 ≤ yukBound df db Y := by
  rw [yukBound]
  exact mul_nonneg (by norm_num) (yukMass_nonneg df db Y)

/-- The coupling mass is invariant under the adjoint flip. -/
theorem yukMass_adjY (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ) :
    yukMass df db (adjY df db Y) = yukMass df db Y := by
  have hnorm : ∀ i j k, ‖adjY df db Y i j k‖ = ‖Y j i k‖ := by
    intro i j k
    have e : adjY df db Y i j k = (starRingEnd ℂ) (Y j i k) := rfl
    rw [e]
    exact RCLike.norm_conj _
  rw [yukMass, yukMass]
  simp only [hnorm]
  exact Finset.sum_comm

/-- A nonzero field matrix element has exactly two possible input
configurations for a given output: `c' ∓ single k 1`. -/
theorem fieldMat_ne_cases (db : ℕ) (k : Fin db) {c' c : Config db}
    (h : fieldMat db k c' c ≠ 0) :
    c = c' - Finsupp.single k 1 ∨ c = c' + Finsupp.single k 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  apply h
  apply fieldMat_eq_zero_of db k
  · intro he
    exact h1 (by rw [he]; exact (config_add_single_sub_single db c k).symm)
  · by_cases hk : c k = 0
    · exact Or.inr hk
    · left
      intro he
      apply h2
      rw [he]
      exact (config_sub_single_add_single db c k hk).symm

/-- The coupled monomial applied to a general coefficient vector, as a
finite sum over the support. -/
theorem yukMonoC_apply (df db : ℕ) (i j : Fin df) (k : Fin db)
    (f : JointConfig df db →₀ ℂ) (S' : Finset (Fin df)) (c' : Config db) :
    (yukMonoC df db i j k f) (S', c')
      = ∑ q ∈ f.support, f q * (densMat df i j S' q.1 * fieldMat db k c' q.2) := by
  conv_lhs => rw [jfinsupp_eq_sum_single df db f f.support
    (fun q hq => Finsupp.mem_support_iff.mpr hq)]
  rw [map_sum, Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  congr 1
  obtain ⟨S, c⟩ := q
  exact yukMonoC_coeff df db i j k S' c' S c

/-- **Two-point monomial bound.** At a maximal coefficient `q₀`, one
coupled monomial's output coordinate is at most
`2 * ‖f q₀‖ * sqrt (bTot q₀.2 + 1)`: for the given output, the
density factor has the single preimage `densPre`, and the field
factor has the two preimages `c₀ ∓ single k 1`. -/
theorem yukMonoC_apply_norm_le (df db : ℕ) (i j : Fin df) (k : Fin db)
    (f : JointConfig df db →₀ ℂ) (q₀ : JointConfig df db)
    (hmax : ∀ q ∈ f.support, ‖f q‖ ≤ ‖f q₀‖) :
    ‖(yukMonoC df db i j k f) q₀‖
      ≤ 2 * ‖f q₀‖ * Real.sqrt (bTot db q₀.2 + 1) := by
  obtain ⟨S₀, c₀⟩ := q₀
  have hu : ∀ q : JointConfig df db,
      ‖densMat df i j S₀ q.1 * fieldMat db k c₀ q.2‖
        ≤ Real.sqrt (bTot db c₀ + 1) := by
    intro q
    calc ‖densMat df i j S₀ q.1 * fieldMat db k c₀ q.2‖
        ≤ ‖densMat df i j S₀ q.1‖ * ‖fieldMat db k c₀ q.2‖ :=
          norm_mul_le _ _
      _ ≤ 1 * Real.sqrt (bTot db c₀ + 1) :=
          mul_le_mul (norm_densMat_le df i j S₀ q.1)
            (norm_fieldMat_le db k c₀ q.2) (norm_nonneg _) (by norm_num)
      _ = Real.sqrt (bTot db c₀ + 1) := one_mul _
  set T : Finset (JointConfig df db) :=
    {(densPre df i j S₀, c₀ - Finsupp.single k 1),
     (densPre df i j S₀, c₀ + Finsupp.single k 1)} with hT
  have hvan : ∀ q ∈ f.support, q ∉ f.support ∩ T →
      ‖f q * (densMat df i j S₀ q.1 * fieldMat db k c₀ q.2)‖ = 0 := by
    intro q hqmem hqT
    have hqT' : q ∉ T := fun hmem => hqT (Finset.mem_inter.mpr ⟨hqmem, hmem⟩)
    rw [hT] at hqT'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hqT'
    obtain ⟨hq1, hq2⟩ := hqT'
    by_contra hne
    have hne2 : f q * (densMat df i j S₀ q.1 * fieldMat db k c₀ q.2) ≠ 0 := by
      intro hz
      apply hne
      rw [hz, norm_zero]
    obtain ⟨hd, hf⟩ := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne2).2
    have hS : q.1 = densPre df i j S₀ := (densMat_pre df hd).1
    rcases fieldMat_ne_cases db k hf with hc | hc
    · exact hq1 (Prod.ext hS hc)
    · exact hq2 (Prod.ext hS hc)
  rw [yukMonoC_apply]
  calc ‖∑ q ∈ f.support, f q * (densMat df i j S₀ q.1 * fieldMat db k c₀ q.2)‖
      ≤ ∑ q ∈ f.support, ‖f q * (densMat df i j S₀ q.1 * fieldMat db k c₀ q.2)‖ :=
        norm_sum_le _ _
    _ = ∑ q ∈ f.support ∩ T,
          ‖f q * (densMat df i j S₀ q.1 * fieldMat db k c₀ q.2)‖ :=
        (Finset.sum_subset Finset.inter_subset_left hvan).symm
    _ ≤ ∑ q ∈ f.support ∩ T, ‖f (S₀, c₀)‖ * Real.sqrt (bTot db c₀ + 1) := by
        apply Finset.sum_le_sum
        intro q hq
        have hqsupp : q ∈ f.support := (Finset.mem_inter.mp hq).1
        rw [norm_mul]
        exact mul_le_mul (hmax q hqsupp) (hu q) (norm_nonneg _) (norm_nonneg _)
    _ ≤ ∑ q ∈ T, ‖f (S₀, c₀)‖ * Real.sqrt (bTot db c₀ + 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          (fun q _ _ => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    _ = (T.card : ℝ) * (‖f (S₀, c₀)‖ * Real.sqrt (bTot db c₀ + 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * ‖f (S₀, c₀)‖ * Real.sqrt (bTot db c₀ + 1) := by
        have hcard : T.card ≤ 2 := by
          rw [hT]
          exact (Finset.card_insert_le _ _).trans (by simp)
        have hcard' : (T.card : ℝ) ≤ 2 := by exact_mod_cast hcard
        have hC : (0 : ℝ) ≤ ‖f (S₀, c₀)‖ * Real.sqrt (bTot db c₀ + 1) :=
          mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
        calc (T.card : ℝ) * (‖f (S₀, c₀)‖ * Real.sqrt (bTot db c₀ + 1))
            ≤ 2 * (‖f (S₀, c₀)‖ * Real.sqrt (bTot db c₀ + 1)) :=
              mul_le_mul_of_nonneg_right hcard' hC
          _ = 2 * ‖f (S₀, c₀)‖ * Real.sqrt (bTot db c₀ + 1) := by ring

/-- The unsymmetrized Yukawa sum applied to a general coefficient
vector, expanded over the coupling indices. -/
theorem yukawaSumC_apply (df db : ℕ) (Z : Fin df → Fin df → Fin db → ℂ)
    (f : JointConfig df db →₀ ℂ) (S' : Finset (Fin df)) (c' : Config db) :
    (yukawaSumC df db Z f) (S', c')
      = ∑ i, ∑ j, ∑ k, Z i j k * (yukMonoC df db i j k f) (S', c') := by
  simp only [yukawaSumC, LinearMap.sum_apply, Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul]

/-- **Interaction coordinate bound (rung (d)).** At a maximal
coefficient `q₀`, the symmetrized interaction's output coordinate is
bounded by the explicit constant `yukBound Y` times the output-side
number factor `sqrt (bTot q₀.2 + 1)`. This is the relative bound of
the interaction against the product free/number data, with the
`(tot + 1)^{1/2}` growth made explicit per output configuration. -/
theorem yukawaIntC_apply_norm_le (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ)
    (f : JointConfig df db →₀ ℂ) (q₀ : JointConfig df db)
    (hmax : ∀ q ∈ f.support, ‖f q‖ ≤ ‖f q₀‖) :
    ‖(yukawaIntC df db Y f) q₀‖
      ≤ yukBound df db Y * ‖f q₀‖ * Real.sqrt (bTot db q₀.2 + 1) := by
  have hsum : ∀ Z : Fin df → Fin df → Fin db → ℂ,
      ‖(yukawaSumC df db Z f) q₀‖
        ≤ 2 * yukMass df db Z * ‖f q₀‖ * Real.sqrt (bTot db q₀.2 + 1) := by
    intro Z
    have e : 2 * yukMass df db Z * ‖f q₀‖ * Real.sqrt (bTot db q₀.2 + 1)
        = ∑ i, ∑ j, ∑ k, ‖Z i j k‖
            * (2 * ‖f q₀‖ * Real.sqrt (bTot db q₀.2 + 1)) := by
      calc 2 * yukMass df db Z * ‖f q₀‖ * Real.sqrt (bTot db q₀.2 + 1)
          = yukMass df db Z * (2 * ‖f q₀‖ * Real.sqrt (bTot db q₀.2 + 1)) := by
            ring
        _ = ∑ i, ∑ j, ∑ k, ‖Z i j k‖
              * (2 * ‖f q₀‖ * Real.sqrt (bTot db q₀.2 + 1)) := by
            rw [yukMass]
            simp only [Finset.sum_mul]
    rw [yukawaSumC_apply, e]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (yukMonoC_apply_norm_le df db i j k f q₀ hmax) (norm_nonneg _)
  obtain ⟨S₀, c₀⟩ := q₀
  rw [yukawaIntC, LinearMap.add_apply, Finsupp.add_apply]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (hsum Y) (hsum (adjY df db Y))).trans ?_
  rw [yukMass_adjY, yukBound]
  exact le_of_eq (by ring)

/-- **Eigenvalue transport for the total Hamiltonian.** An eigenvector
in bosonic band `N` has its eigenvalue within
`‖g‖ * yukBound Y * sqrt (N + 1)` of the joint free eigenvalue at a
maximal coefficient configuration of the eigenvector. -/
theorem hamYuk_eigenvalue_transport (df db : ℕ) (lamF : Fin df → ℝ)
    (omB : Fin db → ℝ) (Y : Fin df → Fin df → Fin db → ℂ) (g : ℝ) (N : ℕ)
    {ψ : JDom df db} (hψband : ψ ∈ jBand df db N) (hψ : ψ ≠ 0) {μ : ℂ}
    (hμ : hamYuk df db lamF omB Y g ψ = μ • ψ) :
    ∃ q₀ : JointConfig df db, bTot db q₀.2 ≤ N ∧
      ‖μ - ((jointEigR df db lamF omB q₀ : ℝ) : ℂ)‖
        ≤ ‖(g : ℂ)‖ * yukBound df db Y * Real.sqrt (N + 1) := by
  set f := jRepr df db ψ with hf
  have hf0 : f ≠ 0 := by
    intro h
    apply hψ
    have hψ2 : ψ = jEquiv df db f := (LinearEquiv.apply_symm_apply _ _).symm
    rw [hψ2, h, map_zero]
  obtain ⟨q₀, hq₀mem, hq₀max⟩ := Finset.exists_max_image f.support
    (fun q => ‖f q‖) (Finsupp.support_nonempty_iff.mpr hf0)
  have hfq₀ : f q₀ ≠ 0 := by
    by_contra h
    apply hf0
    ext q
    by_cases hq : q ∈ f.support
    · have hle := hq₀max q hq
      rw [h, norm_zero] at hle
      rw [Finsupp.zero_apply]
      exact norm_le_zero_iff.mp hle
    · exact Finsupp.notMem_support_iff.mp hq
  have hband : bTot db q₀.2 ≤ N := by
    by_contra hcon
    push_neg at hcon
    exact hfq₀ ((mem_jBand_iff df db N ψ).mp hψband q₀ hcon)
  have hcoord : (μ - ((jointEigR df db lamF omB q₀ : ℝ) : ℂ)) * f q₀
      = (g : ℂ) * (yukawaIntC df db Y f) q₀ := by
    have e1 : (jRepr df db (hamYuk df db lamF omB Y g ψ)) q₀
        = ((jointEigR df db lamF omB q₀ : ℝ) : ℂ) * f q₀
          + (g : ℂ) * (yukawaIntC df db Y f) q₀ := by
      rw [hamYuk_apply, map_add, Finsupp.add_apply, map_smul, Finsupp.smul_apply,
        smul_eq_mul]
      congr 1
      · have e : jRepr df db (hamFreeJ df db lamF omB ψ)
            = diagC df db (fun q => ((jointEigR df db lamF omB q : ℝ) : ℂ)) f := by
          rw [hamFreeJ, jTransport_apply, jRepr_jEquiv]
        rw [e, diagC_apply]
      · have e : jRepr df db (yukawaIntJ df db Y ψ) = yukawaIntC df db Y f := by
          rw [yukawaIntJ, jTransport_apply, jRepr_jEquiv]
        rw [e]
    have e2 : (jRepr df db (hamYuk df db lamF omB Y g ψ)) q₀ = μ * f q₀ := by
      rw [hμ, map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [e1] at e2
    rw [sub_mul, ← e2, add_sub_cancel_left]
  refine ⟨q₀, hband, ?_⟩
  have hnorm : ‖μ - ((jointEigR df db lamF omB q₀ : ℝ) : ℂ)‖ * ‖f q₀‖
      ≤ (‖(g : ℂ)‖ * yukBound df db Y * Real.sqrt (N + 1)) * ‖f q₀‖ := by
    calc ‖μ - ((jointEigR df db lamF omB q₀ : ℝ) : ℂ)‖ * ‖f q₀‖
        = ‖(μ - ((jointEigR df db lamF omB q₀ : ℝ) : ℂ)) * f q₀‖ :=
          (norm_mul _ _).symm
      _ = ‖(g : ℂ) * (yukawaIntC df db Y f) q₀‖ := by rw [hcoord]
      _ = ‖(g : ℂ)‖ * ‖(yukawaIntC df db Y f) q₀‖ := norm_mul _ _
      _ ≤ ‖(g : ℂ)‖ * (yukBound df db Y * ‖f q₀‖
            * Real.sqrt (bTot db q₀.2 + 1)) :=
          mul_le_mul_of_nonneg_left
            (yukawaIntC_apply_norm_le df db Y f q₀ hq₀max) (norm_nonneg _)
      _ ≤ (‖(g : ℂ)‖ * yukBound df db Y * Real.sqrt (N + 1)) * ‖f q₀‖ := by
          have hs : Real.sqrt (bTot db q₀.2 + 1) ≤ Real.sqrt (N + 1) := by
            apply Real.sqrt_le_sqrt
            exact_mod_cast Nat.add_le_add_right hband 1
          have hB : (0 : ℝ) ≤ yukBound df db Y := yukBound_nonneg df db Y
          have hf0' : (0 : ℝ) ≤ ‖f q₀‖ := norm_nonneg _
          have hg : (0 : ℝ) ≤ ‖(g : ℂ)‖ := norm_nonneg _
          calc ‖(g : ℂ)‖ * (yukBound df db Y * ‖f q₀‖
                * Real.sqrt (bTot db q₀.2 + 1))
              = (‖(g : ℂ)‖ * yukBound df db Y * ‖f q₀‖)
                  * Real.sqrt (bTot db q₀.2 + 1) := by ring
            _ ≤ (‖(g : ℂ)‖ * yukBound df db Y * ‖f q₀‖)
                  * Real.sqrt (N + 1) :=
                mul_le_mul_of_nonneg_left hs
                  (mul_nonneg (mul_nonneg hg hB) hf0')
            _ = (‖(g : ℂ)‖ * yukBound df db Y * Real.sqrt (N + 1))
                  * ‖f q₀‖ := by ring
  exact le_of_mul_le_mul_right hnorm (norm_pos_iff.mpr hfq₀)

/-- Eigenvalues of the total Hamiltonian are real (from symmetry on
the product domain). -/
theorem hamYuk_eigenvalue_real (df db : ℕ) (lamF : Fin df → ℝ)
    (omB : Fin db → ℝ) (Y : Fin df → Fin df → Fin db → ℂ) (g : ℝ)
    {ψ : JDom df db} (hψ : ψ ≠ 0) {μ : ℂ}
    (hμ : hamYuk df db lamF omB Y g ψ = μ • ψ) : μ.im = 0 := by
  have hψJ : (ψ : JointSpace df db) ≠ 0 := by
    intro h
    apply hψ
    exact Subtype.ext h
  have hR : ⟪(ψ : JointSpace df db), (ψ : JointSpace df db)⟫_ℂ ≠ 0 := by
    rwa [ne_eq, inner_self_eq_zero]
  have h1 : ⟪((hamYuk df db lamF omB Y g ψ : JDom df db) : JointSpace df db),
        (ψ : JointSpace df db)⟫_ℂ
      = (starRingEnd ℂ) μ
        * ⟪(ψ : JointSpace df db), (ψ : JointSpace df db)⟫_ℂ := by
    rw [hμ]
    show ⟪((μ • ψ : JDom df db) : JointSpace df db),
      (ψ : JointSpace df db)⟫_ℂ = _
    show ⟪μ • (ψ : JointSpace df db), (ψ : JointSpace df db)⟫_ℂ = _
    rw [inner_smul_left]
  have h2 : ⟪(ψ : JointSpace df db),
        ((hamYuk df db lamF omB Y g ψ : JDom df db) : JointSpace df db)⟫_ℂ
      = μ * ⟪(ψ : JointSpace df db), (ψ : JointSpace df db)⟫_ℂ := by
    rw [hμ]
    show ⟪(ψ : JointSpace df db),
      ((μ • ψ : JDom df db) : JointSpace df db)⟫_ℂ = _
    show ⟪(ψ : JointSpace df db), μ • (ψ : JointSpace df db)⟫_ℂ = _
    rw [inner_smul_right]
  have hsym := hamYuk_isSymmetric df db lamF omB Y g ψ ψ
  rw [h1, h2] at hsym
  have hμc : (starRingEnd ℂ) μ = μ := mul_right_cancel₀ hR hsym
  exact RCLike.conj_eq_iff_im.mp hμc

/-- The fermionic free dichotomy (the parent campaign's gap
hypothesis, mode by mode). -/
theorem freeEig_dichotomy (df : ℕ) (lamF : Fin df → ℝ) (Δ : ℝ)
    (hlam : ∀ i, 0 ≤ lamF i) (hgap : ∀ i, lamF i = 0 ∨ Δ ≤ lamF i)
    (S : Finset (Fin df)) :
    freeEig df lamF S = 0 ∨ Δ ≤ freeEig df lamF S := by
  by_cases h : ∀ i ∈ S, lamF i = 0
  · left
    rw [freeEig]
    exact Finset.sum_eq_zero (fun i hi => h i hi)
  · right
    push_neg at h
    obtain ⟨i₀, hi₀, hne⟩ := h
    have hΔ : Δ ≤ lamF i₀ := (hgap i₀).resolve_left hne
    refine hΔ.trans ?_
    rw [freeEig]
    exact Finset.single_le_sum (fun i _ => hlam i) hi₀

/-- The bosonic free dichotomy: a bosonic free eigenvalue is `0` or
at least `Δ` (a nonzero occupation of a gapped mode already
contributes `≥ Δ`). -/
theorem boseEig_dichotomy (db : ℕ) (omB : Fin db → ℝ) (Δ : ℝ)
    (hom : ∀ k, 0 ≤ omB k) (hgap : ∀ k, omB k = 0 ∨ Δ ≤ omB k)
    (c : Config db) :
    boseEig db omB c = 0 ∨ Δ ≤ boseEig db omB c := by
  by_cases h : ∀ k, omB k * (c k : ℝ) = 0
  · left
    rw [boseEig]
    exact Finset.sum_eq_zero (fun k _ => h k)
  · right
    push_neg at h
    obtain ⟨k₀, hne⟩ := h
    have hom0 : omB k₀ ≠ 0 := fun hh => hne (by rw [hh, zero_mul])
    have hc0 : (c k₀ : ℝ) ≠ 0 := fun hh => hne (by rw [hh, mul_zero])
    have hΔ : Δ ≤ omB k₀ := (hgap k₀).resolve_left hom0
    have hc1 : (1 : ℝ) ≤ (c k₀ : ℝ) := by
      have hpos : 0 < c k₀ := Nat.pos_of_ne_zero (fun hh => hc0 (by exact_mod_cast hh))
      exact Nat.one_le_cast.mpr hpos
    have hterm : Δ ≤ omB k₀ * (c k₀ : ℝ) := by
      calc Δ = Δ * 1 := (mul_one Δ).symm
        _ ≤ omB k₀ * (c k₀ : ℝ) :=
          mul_le_mul hΔ hc1 (by norm_num) (hom k₀)
    refine hterm.trans ?_
    rw [boseEig]
    exact Finset.single_le_sum
      (fun k _ => mul_nonneg (hom k) (Nat.cast_nonneg _)) (Finset.mem_univ k₀)

/-- **The joint free dichotomy (strong form).** With per-mode gap
hypotheses on both factors, every joint free eigenvalue is `0` or
`≥ Δ`. (The weak form is false in general — a sum of two sub-Δ
contributions — exactly as in Campaign 2; the strong per-mode
hypotheses are what make it true.) -/
theorem jointEig_dichotomy (df db : ℕ) (lamF : Fin df → ℝ) (omB : Fin db → ℝ)
    (Δ : ℝ) (hlamF : ∀ i, 0 ≤ lamF i) (homB : ∀ k, 0 ≤ omB k)
    (hgapF : ∀ i, lamF i = 0 ∨ Δ ≤ lamF i)
    (hgapB : ∀ k, omB k = 0 ∨ Δ ≤ omB k) (q : JointConfig df db) :
    jointEigR df db lamF omB q = 0 ∨ Δ ≤ jointEigR df db lamF omB q := by
  obtain ⟨S, c⟩ := q
  have hF := freeEig_dichotomy df lamF Δ hlamF hgapF S
  have hB := boseEig_dichotomy db omB Δ homB hgapB c
  have hFnn : 0 ≤ freeEig df lamF S := by
    rw [freeEig]
    exact Finset.sum_nonneg (fun i _ => hlamF i)
  have hBnn : 0 ≤ boseEig db omB c := by
    rw [boseEig]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (homB k) (Nat.cast_nonneg _))
  have e : jointEigR df db lamF omB (S, c)
      = freeEig df lamF S + boseEig db omB c := rfl
  rcases hF with hF | hF <;> rcases hB with hB | hB
  · left
    rw [e, hF, hB, add_zero]
  · right
    rw [e]
    linarith
  · right
    rw [e]
    linarith
  · right
    rw [e]
    linarith

/-- **Windowed gap persistence for the coupled Hamiltonian (rung (f),
windowed form).** Let both free factors obey the per-mode gap
hypotheses at `Δ`. An eigenvector of `H` supported in bosonic band
`N`, at the explicit threshold
`2 * (‖g‖ * yukBound Y * sqrt (N + 1)) ≤ Δ / 4`, obeys the dichotomy
`μ.re ≤ ‖g‖ * yukBound Y * sqrt (N + 1)` or `Δ / 2 ≤ μ.re`: the free
gap persists above the ground cluster, inside the window. NO uniform
(band-independent or coupling-independent) persistence is claimed —
it is false in general (header fence; Campaign 2's collapse
counterexample embeds at the fermion vacuum). -/
theorem hamYuk_gap_persistence_windowed (df db : ℕ) (lamF : Fin df → ℝ)
    (omB : Fin db → ℝ) (Y : Fin df → Fin df → Fin db → ℂ) (g : ℝ) (Δ : ℝ)
    (hΔ : 0 < Δ) (hlamF : ∀ i, 0 ≤ lamF i) (homB : ∀ k, 0 ≤ omB k)
    (hgapF : ∀ i, lamF i = 0 ∨ Δ ≤ lamF i)
    (hgapB : ∀ k, omB k = 0 ∨ Δ ≤ omB k)
    {N : ℕ} (hsmall : 2 * (‖(g : ℂ)‖ * yukBound df db Y * Real.sqrt (N + 1))
      ≤ Δ / 4)
    {ψ : JDom df db} (hψband : ψ ∈ jBand df db N) (hψ : ψ ≠ 0) {μ : ℂ}
    (hμ : hamYuk df db lamF omB Y g ψ = μ • ψ) :
    μ.re ≤ ‖(g : ℂ)‖ * yukBound df db Y * Real.sqrt (N + 1)
      ∨ Δ / 2 ≤ μ.re := by
  obtain ⟨q₀, -, htr⟩ := hamYuk_eigenvalue_transport df db lamF omB Y g N
    hψband hψ hμ
  set ρ := ‖(g : ℂ)‖ * yukBound df db Y * Real.sqrt (N + 1) with hρ
  have hμr : μ.im = 0 := hamYuk_eigenvalue_real df db lamF omB Y g hψ hμ
  have hfree : jointEigR df db lamF omB q₀ = 0
      ∨ Δ ≤ jointEigR df db lamF omB q₀ :=
    jointEig_dichotomy df db lamF omB Δ hlamF homB hgapF hgapB q₀
  have hre : |μ.re - jointEigR df db lamF omB q₀| ≤ ρ := by
    have h := Complex.abs_re_le_norm (μ - ((jointEigR df db lamF omB q₀ : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at h
    exact h.trans htr
  have hρle : ρ ≤ Δ / 8 := by linarith [hsmall]
  rcases hfree with he | hΔe
  · left
    rw [he] at hre
    exact le_trans (le_abs_self _) (by simpa using hre)
  · right
    have habs := abs_le.mp hre
    linarith

/-! ## §6. The vacuum exhibit and the not-a-dΓ certificate

The joint vacuum is an exact `0`-eigenvector of `H` for every
coupling (the density annihilates the fermion vacuum before the
field can act). And the interaction is certified NOT diagonal in the
joint basis — hence not a `dΓ`, not a joint diagonal operator, not a
function of the free eigenvalue data — whenever some diagonal
coupling `Y i i k` has nonzero real part: its vacuum-to-one-boson
matrix element at the occupied fermion mode `i` is exactly
`2 * Re (Y i i k) ≠ 0`. -/

/-- The density coefficient vanishes on the fermion vacuum. -/
theorem densCoef_empty (df : ℕ) (i j : Fin df) : densCoef df i j ∅ = 0 := by
  rw [densCoef, if_neg (by simp)]

/-- The interaction annihilates the joint vacuum. -/
theorem yukawaIntJ_vacuum (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ) :
    yukawaIntJ df db Y (jVec df db (∅, 0)) = 0 := by
  apply (jRepr df db).injective
  rw [map_zero, yukawaIntJ, jTransport_apply, jRepr_jVec, jRepr_jEquiv]
  ext ⟨S', c'⟩
  rw [Finsupp.zero_apply, yukawaIntC_coeff, yukCoefTot]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  by_cases h : S' = densPhi df i j ∅
  · rw [densMat, if_pos h, densCoef_empty, zero_mul, mul_zero]
  · rw [densMat, if_neg h, zero_mul, mul_zero]

/-- **The vacuum exhibit.** The joint vacuum `(∅, 0)` is an exact
eigenvector of the total Hamiltonian with eigenvalue `0`, for every
coupling and every free data. This is also the sector at which
Campaign 2's collapse counterexample would embed in a bosonic
self-interaction — the structural reason rung (f) is windowed. -/
theorem hamYuk_vacuum_eigenvalue (df db : ℕ) (lamF : Fin df → ℝ)
    (omB : Fin db → ℝ) (Y : Fin df → Fin df → Fin db → ℂ) (g : ℝ) :
    hamYuk df db lamF omB Y g (jVec df db (∅, 0)) = 0 := by
  have hvac : jointEigR df db lamF omB (∅, 0) = 0 := by
    simp [jointEigR, boseEig, freeEig]
  rw [hamYuk_apply, yukawaIntJ_vacuum, smul_zero, add_zero, hamFreeJ_basis, hvac]
  simp

/-- The diagonal density coefficient at a singleton is `1`: the two
Koszul signs agree (inserting `i` into `{i}` costs the same sign as
into `∅`), and a sign squares to `1`. -/
theorem densCoef_self_singleton (df : ℕ) (i : Fin df) :
    densCoef df i i {i} = 1 := by
  have hcond : i ∈ ({i} : Finset (Fin df))
      ∧ i ∉ ({i} : Finset (Fin df)).erase i := by
    refine ⟨Finset.mem_singleton_self i, ?_⟩
    simp [Finset.erase_singleton]
  have herase : ({i} : Finset (Fin df)).erase i = ∅ := Finset.erase_singleton i
  have e1 : sgn df i ({i} : Finset (Fin df)) = sgn df i (∅ : Finset (Fin df)) := by
    have e : ({i} : Finset (Fin df)) = insert i ∅ := by simp
    rw [e]
    exact sgn_insert_eq df i ∅
  rw [densCoef, if_pos hcond, herase, e1]
  exact sgn_sq df i ∅

/-- The diagonal density matrix element at a singleton is `1`. -/
theorem densMat_self (df : ℕ) (i : Fin df) : densMat df i i {i} {i} = 1 := by
  have e : densPhi df i i {i} = {i} := by simp [densPhi]
  rw [densMat, if_pos e.symm, densCoef_self_singleton]

/-- At a singleton, the density matrix element vanishes off the
diagonal: the coefficient needs `b ∈ {i}`, and then the configuration
map produces `{a}`, not `{i}`. -/
theorem densMat_singleton_ne (df : ℕ) {a b i : Fin df}
    (h : a ≠ i ∨ b ≠ i) : densMat df a b {i} {i} = 0 := by
  rw [densMat]
  by_cases hphi : ({i} : Finset (Fin df)) = densPhi df a b {i}
  · rw [if_pos hphi]
    rcases h with ha | hb
    · by_cases hb2 : b = i
      · have e : densPhi df a b {i} = {a} := by
          rw [densPhi, hb2]; simp
        rw [e] at hphi
        exact absurd (Finset.singleton_inj.mp hphi) (Ne.symm ha)
      · rw [densCoef, if_neg (fun hh => hb2 (Finset.mem_singleton.mp hh.1))]
    · rw [densCoef, if_neg (fun hh => hb (Finset.mem_singleton.mp hh.1))]
  · rw [if_neg hphi]

/-- The field matrix element from the bosonic vacuum to the
one-boson configuration at the same mode is `1`. -/
theorem fieldMat_single_zero (db : ℕ) (k : Fin db) :
    fieldMat db k (Finsupp.single k 1) 0 = 1 := by
  have h1 : (Finsupp.single k (1 : ℕ)) = (0 : Config db) + Finsupp.single k 1 := by
    simp
  have h2 : (Finsupp.single k (1 : ℕ)) ≠ (0 : Config db) - Finsupp.single k 1 := by
    intro h
    have h3 := congrArg (fun f : Config db => f k) (h1.symm.trans h)
    simp [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply] at h3
  rw [fieldMat, if_pos h1, if_neg h2, add_zero]
  simp [sqrtNat]

/-- The field matrix element from the bosonic vacuum to a one-boson
configuration at a DIFFERENT mode vanishes. -/
theorem fieldMat_single_zero_of_ne (db : ℕ) {k κ : Fin db} (h : κ ≠ k) :
    fieldMat db κ (Finsupp.single k 1) 0 = 0 := by
  apply fieldMat_eq_zero_of db κ
  · intro he
    have h3 := congrArg (fun f : Config db => f κ) he
    simp [Finsupp.add_apply, Finsupp.single_apply, h, Ne.symm h] at h3
  · right
    simp

/-- **The vacuum-to-one-boson matrix element.** At the occupied
fermion mode `i`, the total coefficient from the joint vacuum sector
`({i}, 0)` to `({i}, single k 1)` is exactly `2 * Re (Y i i k)`:
only the diagonal monomial `(i, i, k)` contributes. -/
theorem yukCoefTot_diag_vac (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ)
    (i : Fin df) (k : Fin db) :
    yukCoefTot df db Y {i} (Finsupp.single k 1) {i} 0
      = 2 * ((Y i i k).re : ℂ) := by
  have h₀a : ∀ b ∈ (Finset.univ : Finset (Fin df)), b ≠ i →
      (∑ j, ∑ κ, (Y b j κ + adjY df db Y b j κ)
        * (densMat df b j {i} {i} * fieldMat db κ (Finsupp.single k 1) 0))
        = 0 := by
    intro b _ hb
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro κ _
    rw [densMat_singleton_ne df (Or.inl hb), zero_mul, mul_zero]
  have h₀b : ∀ b ∈ (Finset.univ : Finset (Fin df)), b ≠ i →
      (∑ κ, (Y i b κ + adjY df db Y i b κ)
        * (densMat df i b {i} {i} * fieldMat db κ (Finsupp.single k 1) 0))
        = 0 := by
    intro b _ hb
    apply Finset.sum_eq_zero
    intro κ _
    rw [densMat_singleton_ne df (Or.inr hb), zero_mul, mul_zero]
  have h₀c : ∀ κ ∈ (Finset.univ : Finset (Fin db)), κ ≠ k →
      (Y i i κ + adjY df db Y i i κ)
        * (densMat df i i {i} {i} * fieldMat db κ (Finsupp.single k 1) 0)
        = 0 := by
    intro κ _ hκ
    rw [fieldMat_single_zero_of_ne db hκ, mul_zero, mul_zero]
  rw [yukCoefTot,
    Finset.sum_eq_single i h₀a (fun h => absurd (Finset.mem_univ i) h),
    Finset.sum_eq_single i h₀b (fun h => absurd (Finset.mem_univ i) h),
    Finset.sum_eq_single k h₀c (fun h => absurd (Finset.mem_univ k) h)]
  have e : adjY df db Y i i k = (starRingEnd ℂ) (Y i i k) := rfl
  have e2 : Y i i k + (starRingEnd ℂ) (Y i i k) = 2 * ((Y i i k).re : ℂ) :=
    RCLike.add_conj _
  rw [densMat_self, fieldMat_single_zero, e, e2, mul_one, mul_one]

/-- **Not-a-dΓ certificate (rung (b)/(f) fence).** If some diagonal
coupling `Y i i k` has nonzero real part, the Yukawa interaction is
not a diagonal operator in the joint basis for any eigenvalue
function: it is not a `dΓ`, not a function of the joint free
eigenvalue data, and it genuinely mixes the vacuum sector with the
one-boson sector. -/
theorem yukawaIntJ_not_diagonal (df db : ℕ) (Y : Fin df → Fin df → Fin db → ℂ)
    (i : Fin df) (k : Fin db) (hY : (Y i i k).re ≠ 0)
    (r : JointConfig df db → ℂ) :
    yukawaIntJ df db Y ≠ jTransport df db (diagC df db r) := by
  intro hcon
  have hL := yukawaIntJ_coord df db Y {i} 0 {i} (Finsupp.single k 1)
  rw [yukCoefTot_diag_vac] at hL
  have hR : ⟪jE df db ({i}, Finsupp.single k 1),
      ((jTransport df db (diagC df db r) (jVec df db ({i}, 0)) : JDom df db)
        : JointSpace df db)⟫_ℂ = 0 := by
    have hne : (({i}, (0 : Config db)) : JointConfig df db)
        ≠ ({i}, Finsupp.single k 1) := by
      intro hpair
      have h2 : (0 : Config db) = Finsupp.single k 1 := congrArg Prod.snd hpair
      have h3 : ((0 : Config db) k) = (Finsupp.single k (1 : ℕ)) k :=
        congrArg (fun f : Config db => f k) h2
      simp at h3
    rw [jTransport_basis, jcoord, jRepr_jEquiv, diagC_apply, Finsupp.single_apply,
      if_neg hne, mul_zero]
  rw [hcon] at hL
  rw [hR] at hL
  have h2 : ((Y i i k).re : ℂ) = 0 :=
    (mul_eq_zero.mp hL.symm).resolve_left (by norm_num)
  rw [Complex.ofReal_eq_zero] at h2
  exact hY h2

/-! ## §7. Axiom audit

The headlines depend on exactly the standard three axioms
(`propext`, `Classical.choice`, `Quot.sound`) — checked by the build
log for this section. -/

#print axioms hamYuk_isSymmetric
#print axioms hamYukPMap_le_adjoint
#print axioms hamFreeJBand_spectral
#print axioms hamYuk_gap_persistence_windowed
#print axioms yukawaIntJ_not_diagonal
end ThetLogos
