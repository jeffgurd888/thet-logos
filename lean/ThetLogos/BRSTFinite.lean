import Mathlib.Tactic

namespace ThetLogos

open Finset

/-!
# ThetLogos.BRSTFinite — Round 2 intake: BRST, as finite algebra

Dossier: `whitepaper/brst-intake-2026-10-18.md`. Priced **M** by the
parked-fleet gauntlet (`whitepaper/gauntlet-parked-fleet-2026-10-17.md`
§8): "BRST / anomalies — stands as an intake, **M**. … The predictable
honest shape — BRST as pure algebra (a nilpotent differential on a
graded complex built from the finite triple's fluctuation data) FITs
as algebra; BRST as a quantization procedure NO-FITs against the
corpus's stance; the anomaly side tests against the finite triple's
actual cocycle content. The intake's job is to make those verdicts
theorems-and-greps rather than expectations."

## What this file is

The finite, purely algebraic core of BRST: the Chevalley–Eilenberg
differential of a finite-dimensional Lie algebra with trivial
coefficients, in coordinates. A finite Lie algebra is pinned as
*data* — structure constants `c k i j` (the bracket
`[eᵢ, eⱼ] = ∑ k, c k i j • eₖ`) subject to antisymmetry and the Jacobi
identity (§1). On the cochain spaces

- `C⁰ = 𝕜`,
- `C¹ = Fin n → 𝕜` (dual coordinates),
- `C² = Fin n → Fin n → 𝕜` (2-cochains, alternating ones singled out),
- `C³ = Fin n → Fin n → Fin n → 𝕜`,

the differentials `d₀ = 0`, `d₁`, `d₂` are the CE formulas. The
headline theorem is `d₂ ∘ d₁ = 0`, and the proof *is* the Jacobi
identity, contracted (`d2_d1`). The assembled BRST charge
`Q : C⁰ × C¹ × C² → C⁰ × C¹ × C²` (the complex truncated at ghost
number 2 — a named scoping decision, see the dossier) is nilpotent:
`Q_sq`.

The worked example (§3) is `𝔰𝔲(2)` in its standard coordinate
presentation `c k i j = εᵢⱼₖ` — the corpus's smallest nonabelian
gauge factor (the corpus owns the group `SU2 = Matrix.specialUnitaryGroup
(Fin 2) ℂ` in `SMGaugeAlgebra.lean`; it owns no coordinate Lie bracket,
so the ε-presentation is supplied here and named as such — deviation
D1 in the dossier). Its low-degree cohomology is computed exactly:
`H⁰ = ℂ`, `H¹ = 0`, `H² = 0` (Whitehead vanishing, at this finite
level, by explicit computation).

## Fences

- Finite-dimensional algebraic model only. Ghosts are graded
  vector-space generators (the cochain degrees), not fields.
- No continuum gauge theory, no gauge fixing, no physical state
  space, no path integral: BRST *as a quantization procedure* is a
  NO-FIT against this corpus, exactly as the gauntlet predicted.
- The anomaly side is *absent*, named: Lie-algebra cohomology
  vanishing is not anomaly cancellation (which is a statement about
  representation traces the corpus does not compute here).

All theorems are T1 unless a definition is explicitly labelled T2
(data). Zero `sorry`/`admit`.
-/

/-! ## §1. A finite Lie algebra as data (T2), and its CE complex -/

/-- A finite-dimensional Lie algebra over `𝕜`, as data: structure
constants `c k i j` for the bracket `[eᵢ, eⱼ] = ∑ k, c k i j • eₖ` on
the basis indexed by `Fin n`, subject to antisymmetry in the lower
indices and the Jacobi identity in contracted form. This is T2 data:
the standard coordinate presentation of a Lie algebra, pinned, not
derived. -/
structure FiniteLieData (n : ℕ) (𝕜 : Type*) [Field 𝕜] where
  /-- Structure constants: `[eᵢ, eⱼ] = ∑ k, c k i j • eₖ`. -/
  c : Fin n → Fin n → Fin n → 𝕜
  /-- Antisymmetry: `c k j i = - c k i j`. -/
  antisymm : ∀ k i j, c k j i = - c k i j
  /-- Alternation: `c k i i = 0`. (Independent data in
  characteristic 2, where antisymmetry alone does not give it.) -/
  diag : ∀ k i, c k i i = 0
  /-- Jacobi, contracted: for all `m i j k`,
  `∑ l, (c l i j * c m l k + c l j k * c m l i + c l k i * c m l j) = 0`.
  This is `[[eᵢ,eⱼ],eₖ] + [[eⱼ,eₖ],eᵢ] + [[eₖ,eᵢ],eⱼ] = 0` read in the
  `m`-th coordinate. -/
  jacobi : ∀ m i j k, ∑ l, (c l i j * c m l k + c l j k * c m l i
      + c l k i * c m l j) = 0

namespace FiniteLieData

variable {n : ℕ} {𝕜 : Type*} [Field 𝕜] (D : FiniteLieData n 𝕜)

/-- Diagonal structure constants vanish: `c k i i = 0`
(the `diag` field of the data). -/
theorem c_self (k i : Fin n) : D.c k i i = 0 := D.diag k i

/-- The first CE differential `d₁ : C¹ → C²`,
`(d₁ a) i j = - ∑ k, a k * c k i j`. (Trivial coefficients.) -/
def d1 (a : Fin n → 𝕜) : Fin n → Fin n → 𝕜 :=
  fun i j => - ∑ k, a k * D.c k i j

/-- The second CE differential `d₂ : C² → C³`,
`(d₂ A) i j k = - (∑ l, A l k * c l i j) + (∑ l, A l j * c l i k)
- (∑ l, A l i * c l j k)`. For alternating `A` this is the standard
Chevalley–Eilenberg formula. -/
def d2 (A : Fin n → Fin n → 𝕜) : Fin n → Fin n → Fin n → 𝕜 :=
  fun i j k => - (∑ l, A l k * D.c l i j) + (∑ l, A l j * D.c l i k)
    - (∑ l, A l i * D.c l j k)

/-- `d₁` is linear in the cochain. -/
theorem d1_add (a b : Fin n → 𝕜) : D.d1 (a + b) = D.d1 a + D.d1 b := by
  funext i j
  simp only [d1, Pi.add_apply, add_mul, Finset.sum_add_distrib, neg_add]

/-- `d₁` lands in alternating 2-cochains. -/
theorem d1_antisymm (a : Fin n → 𝕜) (i j : Fin n) :
    D.d1 a j i = - D.d1 a i j := by
  simp only [d1]
  rw [Finset.sum_congr rfl (fun k _ => by rw [D.antisymm k i j, mul_neg]),
    Finset.sum_neg_distrib, neg_neg]

/-- `d₁` kills the diagonal. -/
theorem d1_self (a : Fin n → 𝕜) (i : Fin n) : D.d1 a i i = 0 := by
  simp only [d1, D.c_self, mul_zero, Finset.sum_const_zero, neg_zero]

/-- The Jacobi contraction, repackaged in the sign pattern the
`d₂ ∘ d₁` expansion produces: for all `m i j k`,
`∑ l, (c l i j * c m l k - c m l j * c l i k + c m l i * c l j k) = 0`.
The middle term is converted by antisymmetry,
`c l i k = - c l k i`. -/
theorem jacobi' (m i j k : Fin n) :
    ∑ l, (D.c l i j * D.c m l k - D.c m l j * D.c l i k
      + D.c m l i * D.c l j k) = 0 := by
  rw [← D.jacobi m i j k]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h : D.c l i k = - D.c l k i := D.antisymm l k i
  rw [h]; ring

/-- Factorization of one `d₂ ∘ d₁` summand: for all `p q r`,
`∑ l, d₁ a l p * c l q r = - ∑ m, a m * (∑ l, c m l p * c l q r)`. -/
theorem aux (a : Fin n → 𝕜) (p q r : Fin n) :
    (∑ l, D.d1 a l p * D.c l q r)
      = - ∑ m, a m * (∑ l, D.c m l p * D.c l q r) := by
  simp only [d1, neg_mul, Finset.sum_mul, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => mul_assoc _ _ _

/-- **The headline. `d₂ ∘ d₁ = 0`, and the proof is the Jacobi
identity**: expanding both definitions, the `i j k` component of
`d₂ (d₁ a)` factors as `∑ m, a m * (the Jacobi contraction)`. -/
theorem d2_d1 (a : Fin n → 𝕜) : D.d2 (D.d1 a) = 0 := by
  funext i j k
  have hsum : ∀ m : Fin n,
      (∑ l, D.c m l k * D.c l i j) - (∑ l, D.c m l j * D.c l i k)
        + (∑ l, D.c m l i * D.c l j k) = 0 := by
    intro m
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    calc (∑ l, (D.c m l k * D.c l i j - D.c m l j * D.c l i k
          + D.c m l i * D.c l j k))
        = ∑ l, (D.c l i j * D.c m l k - D.c m l j * D.c l i k
          + D.c m l i * D.c l j k) :=
          Finset.sum_congr rfl fun l _ => by ring
      _ = 0 := D.jacobi' m i j k
  have merge : ∀ (U V W : Fin n → 𝕜),
      (∑ m, a m * U m) - (∑ m, a m * V m) + (∑ m, a m * W m)
        = ∑ m, a m * (U m - V m + W m) := by
    intro U V W
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  simp only [d2, Pi.zero_apply]
  rw [D.aux a k i j, D.aux a j i k, D.aux a i j k]
  simp only [neg_neg, sub_neg_eq_add]
  rw [← sub_eq_add_neg, merge]
  exact Finset.sum_eq_zero fun m _ => by rw [hsum m, mul_zero]

end FiniteLieData

/-! ## §2. The BRST charge, assembled; cohomology; the abelian contrast -/

variable {n : ℕ} {𝕜 : Type*} [Field 𝕜]

/-- The truncated BRST complex (ghost numbers `0, 1, 2`) of finite
Lie data `D`: the product of cochain spaces `C⁰ × C¹ × C²`. -/
abbrev BRSTComplex (D : FiniteLieData n 𝕜) :=
  𝕜 × (Fin n → 𝕜) × (Fin n → Fin n → 𝕜)

/-- The **BRST charge** `Q`: raises ghost number by one,
`Q (x, a, A) = (0, 0, d₁ a)` (with `d₀ = 0` at the base). The
`d₂`-component lands outside the truncated complex; `d₂` itself is
kept as the map that defines `H²` below. Truncation at ghost number
2 is a named scoping decision (dossier §3). -/
def brstQ (D : FiniteLieData n 𝕜) :
    BRSTComplex D → BRSTComplex D :=
  fun v => (0, 0, D.d1 v.2.1)

/-- `d₁` annihilates the zero cochain. -/
theorem d1_zero (D : FiniteLieData n 𝕜) : D.d1 0 = 0 := by
  funext i j
  simp [FiniteLieData.d1]

/-- **BRST nilpotency, assembled form: `Q` squared is zero.**
`Q (Q v) = (0, 0, d₁ 0) = 0` because the only nonzero component of
`Q v` in degree 1 is `0`, which `Q`'s `d₁` annihilates. The
content-bearing nilpotency of the complex is `d₂ ∘ d₁ = 0`
(`FiniteLieData.d2_d1`); this theorem is the assembled charge's
bookkeeping form, stated and proved as such — the dossier does not
let the trivial direction impersonate the theorem. -/
theorem brstQ_sq (D : FiniteLieData n 𝕜) (v : BRSTComplex D) :
    brstQ D (brstQ D v) = 0 := by
  simp [brstQ, d1_zero]

/-- Ghost number of a homogeneous cochain — booked as the grading
that `Q` raises by one. -/
def ghostNumber : Fin 3 → ℕ := fun k => k.val

theorem ghostNumber_succ (k : Fin 2) :
    ghostNumber ⟨k.val + 1, by omega⟩ = ghostNumber ⟨k.val, by omega⟩ + 1 := rfl

/-- `H⁰`: the 0-cochains themselves (`d₀ = 0`, nothing is exact in
degree 0). As a statement: every 0-cochain is closed. Booked
elementarily, without quotient machinery. -/
def H0 (D : FiniteLieData n 𝕜) := 𝕜

/-- Closed 1-cochains: the kernel of `d₁` (this is `H¹`, since
`im d₀ = 0`). -/
def Closed1 (D : FiniteLieData n 𝕜) (a : Fin n → 𝕜) : Prop :=
  D.d1 a = 0

/-- Alternating 2-cochains. -/
def Alt2 (A : Fin n → Fin n → 𝕜) : Prop :=
  ∀ i j, A j i = - A i j

/-- Closed alternating 2-cochains: the kernel of `d₂` on `Alt2`. -/
def ClosedAlt2 (D : FiniteLieData n 𝕜) (A : Fin n → Fin n → 𝕜) : Prop :=
  Alt2 A ∧ D.d2 A = 0

/-- Exact alternating 2-cochains: the image of `d₁`. -/
def ExactAlt2 (D : FiniteLieData n 𝕜) (A : Fin n → Fin n → 𝕜) : Prop :=
  ∃ a : Fin n → 𝕜, D.d1 a = A

/-- `d₁` lands in alternating cochains (restating §1). -/
theorem exactAlt2_alt (D : FiniteLieData n 𝕜) {A : Fin n → Fin n → 𝕜}
    (hA : ExactAlt2 D A) : Alt2 A := by
  obtain ⟨a, rfl⟩ := hA
  exact D.d1_antisymm a

/-- **Exact implies closed** — the well-definedness of `H²`:
every `d₁`-exact alternating 2-cochain is `d₂`-closed. This is
`d₂ ∘ d₁ = 0` read as a cohomology statement. -/
theorem exactAlt2_closed (D : FiniteLieData n 𝕜) {A : Fin n → Fin n → 𝕜}
    (hA : ExactAlt2 D A) : ClosedAlt2 D A := by
  obtain ⟨a, rfl⟩ := hA
  exact ⟨D.d1_antisymm a, D.d2_d1 a⟩

/-- The zero Lie data: all structure constants vanish (the abelian
algebra `𝕜ⁿ`). -/
def abelianData (n : ℕ) (𝕜 : Type*) [Field 𝕜] : FiniteLieData n 𝕜 where
  c := 0
  antisymm := by simp
  diag := by simp
  jacobi := by simp

/-- For abelian data the first differential vanishes identically. -/
theorem abelian_d1 (a : Fin n → 𝕜) :
    (abelianData n 𝕜).d1 a = 0 := by
  funext i j
  simp [FiniteLieData.d1, abelianData]

/-- For abelian data the second differential vanishes identically. -/
theorem abelian_d2 (A : Fin n → Fin n → 𝕜) :
    (abelianData n 𝕜).d2 A = 0 := by
  funext i j k
  simp [FiniteLieData.d2, abelianData]

/-- The abelian contrast, cohomological form: for `𝕜ⁿ` abelian,
every 1-cochain is closed and every alternating 2-cochain is
closed — with `d₁ = 0` nothing is exact except `0`, so
`H¹ = C¹` and `H² = Alt C²` in full. -/
theorem abelian_closed1 (a : Fin n → 𝕜) :
    Closed1 (abelianData n 𝕜) a := abelian_d1 a

/-! ## §3. The worked example: `𝔰𝔲(2)` and its exact cohomology -/

/-- The Levi-Civita symbol on `Fin 3`, in closed form:
`ε i j k = ((i - j) * (j - k) * (k - i)) / 2` on the values cast
to `ℂ`. Equals `+1` on cyclic triples, `-1` on anticyclic ones,
`0` on repeated ones. -/
noncomputable def lcEps (i j k : Fin 3) : ℂ :=
  (((i.val : ℂ) - (j.val : ℂ)) * ((j.val : ℂ) - (k.val : ℂ))
    * ((k.val : ℂ) - (i.val : ℂ))) / 2

/-- `𝔰𝔲(2)` as finite Lie data: structure constants
`c k i j = ε i j k` — the standard coordinate presentation of the
Lie algebra of the corpus's smallest nonabelian gauge factor (the
group `SU2` of `SMGaugeAlgebra.lean`). Antisymmetry is a ring
identity; the Jacobi identity is the finite ε-contraction,
discharged by case analysis (`fin_cases` + `norm_num`). -/
noncomputable def su2Data : FiniteLieData 3 ℂ where
  c := fun k i j => lcEps i j k
  antisymm := by
    intro k i j
    simp only [lcEps]
    ring
  diag := by
    intro k i
    simp only [lcEps]
    ring
  jacobi := by
    intro m i j k
    fin_cases m <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [Fin.sum_univ_three, lcEps]

/-- The `𝔰𝔲(2)` differential, evaluated: `(d₁ a) i j = - ∑ k, a k *
ε i j k`. -/
theorem su2_d1_apply (a : Fin 3 → ℂ) (i j : Fin 3) :
    su2Data.d1 a i j = - ∑ k, a k * lcEps i j k := rfl

/-- The `𝔰𝔲(2)` second differential, evaluated. -/
theorem su2_d2_apply (A : Fin 3 → Fin 3 → ℂ) (i j k : Fin 3) :
    su2Data.d2 A i j k = - (∑ l, A l k * lcEps i j l)
      + (∑ l, A l j * lcEps i k l) - (∑ l, A l i * lcEps j k l) := rfl

/-- **`d₁` is injective for `𝔰𝔲(2)`** — read off the three
components `(d₁ a) 0 1 = - a 2`, `(d₁ a) 1 2 = - a 0`,
`(d₁ a) 2 0 = - a 1`. -/
theorem su2_d1_injective {a : Fin 3 → ℂ} (h : su2Data.d1 a = 0) :
    a = 0 := by
  have e : ∀ i j, - ∑ k, a k * lcEps i j k = 0 := by
    intro i j
    have h' := congrFun (congrFun h i) j
    simp only [Pi.zero_apply] at h'
    rwa [su2_d1_apply] at h'
  have a0 : a 0 = 0 := by
    have h12 := e 1 2
    rw [Fin.sum_univ_three] at h12
    norm_num [lcEps] at h12
    exact h12
  have a1 : a 1 = 0 := by
    have h20 := e 2 0
    rw [Fin.sum_univ_three] at h20
    norm_num [lcEps] at h20
    exact h20
  have a2 : a 2 = 0 := by
    have h01 := e 0 1
    rw [Fin.sum_univ_three] at h01
    norm_num [lcEps] at h01
    exact h01
  funext x
  fin_cases x <;> simp [a0, a1, a2]

/-- The complex is not trivial: `d₁` has nonzero values
(`a k = k` gives `(d₁ a) 0 1 = -2`). -/
theorem su2_d1_ne_zero :
    su2Data.d1 (fun k : Fin 3 => (k.val : ℂ)) ≠ 0 := by
  intro h
  have h' := congrFun (congrFun h 0) 1
  simp only [Pi.zero_apply] at h'
  rw [su2_d1_apply, Fin.sum_univ_three] at h'
  norm_num [lcEps] at h'

/-- **`H¹(𝔰𝔲(2)) = 0`**: every closed 1-cochain vanishes
(Whitehead's first lemma, this finite case, by computation). -/
theorem su2_H1_vanishes {a : Fin 3 → ℂ} (h : Closed1 su2Data a) :
    a = 0 := su2_d1_injective h

/-- `H⁰(𝔰𝔲(2)) = ℂ` (by the §2 definition of `H0`). -/
theorem su2_H0 : H0 su2Data = ℂ := rfl

/-- **For `𝔰𝔲(2)`, `d₂` vanishes on every alternating 2-cochain.**
Each component of `d₂ A` collapses, via the ε-support, to diagonal
values `A l l`, which alternation kills. -/
theorem su2_d2_alt_zero {A : Fin 3 → Fin 3 → ℂ} (hA : Alt2 A) :
    su2Data.d2 A = 0 := by
  have hd : ∀ i, A i i = 0 := fun i => by
    have h := hA i i
    linear_combination h / 2
  have r01 : A 1 0 = - A 0 1 := hA 0 1
  have r02 : A 2 0 = - A 0 2 := hA 0 2
  have r12 : A 2 1 = - A 1 2 := hA 1 2
  funext i j k
  rw [su2_d2_apply]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [Fin.sum_univ_three] <;> norm_num [lcEps] <;>
    simp only [r01, r02, r12, hd] <;> ring

/-- **Every alternating 2-cochain of `𝔰𝔲(2)` is exact**: the
Hodge-dual candidate `a k = -½ ∑ p q, ε k p q * A p q` satisfies
`d₁ a = A`, by the εε contraction identity, checked finitely. -/
theorem su2_exact_of_alt {A : Fin 3 → Fin 3 → ℂ} (hA : Alt2 A) :
    ExactAlt2 su2Data A := by
  have hd : ∀ i, A i i = 0 := fun i => by
    have h := hA i i
    linear_combination h / 2
  have r01 : A 1 0 = - A 0 1 := hA 0 1
  have r02 : A 2 0 = - A 0 2 := hA 0 2
  have r12 : A 2 1 = - A 1 2 := hA 1 2
  refine ⟨fun k => - (1 / 2 : ℂ) * ∑ p, ∑ q, lcEps k p q * A p q, ?_⟩
  funext i j
  rw [su2_d1_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.sum_univ_three] <;> norm_num [lcEps] <;>
    simp only [r01, r02, r12, hd] <;> ring

/-- **`H²(𝔰𝔲(2)) = 0`**: every closed alternating 2-cochain is
exact (Whitehead's second lemma, this finite case). In fact every
alternating 2-cochain is exact and every one is closed
(`su2_d2_alt_zero`); booked here in the cohomological form. -/
theorem su2_H2_vanishes {A : Fin 3 → Fin 3 → ℂ}
    (h : ClosedAlt2 su2Data A) : ExactAlt2 su2Data A :=
  su2_exact_of_alt h.1

end ThetLogos
