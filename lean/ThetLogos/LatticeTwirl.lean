import ThetLogos.LatticeAnalyticity
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-
# Haar twirls and pair intertwiners (Pitch 4, Stage 1c-0 — bricks Q13-0 and Q13-1)

HONESTY LEDGER — read this before citing anything from this file.

## 0. What this file is

Tier: **T1 at the finite-representation level** — machine-checked
statements about Haar twirls of finite-dimensional unitary
representations, in the coordinates of `ThetLogos.LatticeGauge` /
`ThetLogos.LatticeAnalyticity`, whose devices are consumed unchanged.

This module builds bricks **Q13-0** (target/interface freeze) and
**Q13-1** (pair representations and Haar twirls) of the re-priced
Stage 1c-0 clause-(ii) remainder
(`whitepaper/stage1c0-q13-reprice-2026-10-24.md`). Bricks Q13-2
(linkwise moment calculus), Q13-3 (two-plaquette tensor-network
contraction) and Q13-4 (assembly and the mandatory checks) are NOT
built here. This module freezes the interfaces they will consume and
proves the twirl theorem they will apply.

## 0.1 The frozen target (charter §1, restated)

For unitary representations `π, τ` of `G` and normalized Haar measure
`μG`, the **J operator** is

  `𝒥(π,τ) = ∫ π(g) ⊗ τ(g) dμG(g)`,

with entry form `𝒥(π,τ) (a,b) (c,e) = ∫ π(g) a c * τ(g) b e dμG(g)`,
and the one-factor boundary case `𝒥(π) = ∫ π(g) dμG(g)`. The canonical
reduction (charter eq. (5)) is

  `𝒥(π,τ) = P`, the orthogonal projector onto the invariant subspace
  of `π ⊗ τ`,

and it is (5) — not the notation — that Q13-1 discharges (§3–§5 below:
invariance, idempotence, self-adjointness, and the invariant-subspace
characterization of the twirl as a linear map).

The remaining frozen targets are the contraction formula (charter
eqs. (6)–(9)): with `κ_p = Cov₀(W_p, A)` the landed covariance of
`LatticeAnalyticity`, each `Cov₀(W_p, D_q)` is to be evaluated as
`-(1/2d) (𝔈⁺_{p,q} + 𝔈⁻_{p,q})`, where the `𝔈` terms are centered
products of expectations, and **each expectation is the explicit
finite tensor contraction `Contr` of the J data** along the two
plaquette words (per link: `𝒥(π)` if only one word uses the link, the
entry tensor of `𝒥(π,τ)` if both do, with `π, τ` drawn from
`ρ, ρ̄, ρ^∨, ρ̄^∨` and the transpose wiring of §6 for literal inverse
factors). `Contr` itself is deliberately **not** defined in this
module: defining it is Q13-3's work, and defining it as an
abbreviation for the original covariance integrals would trigger the
charter's Q13-0 kill (b) — notation mistaken for the closed form.

The mandatory acceptance checks for the full Q13 sequence, frozen
here before any contraction work (charter §4): **C1** — the
circle/fundamental specialization must recover
`Cov₀(W_p, D_q) = -1/2` for `q = p`, `0` otherwise, and `κ_p = -1/2`
in total (in agreement with the landed `covZero_circle_plaquette_density`
and `kappa_circle_plaquette`); **C2** — termwise agreement with the
landed link-sharing sum `covZero_plaquetteLoop_eq_sum` for general
`(G, ρ)`, centering included (for reducible `ρ` the one-factor means
need not vanish); **C3** — orientation/normalization guards: the
contraction must be unchanged by cyclic rotation of either word and
by relabeling of contracted indices, and must give `κ_p = 0` for the
trivial representation (the algebraic content of C3 at the interface
level is §8: covariance against a constant observable vanishes).

## 0.2 Mandatory clauses (binding on this module)

**(i) NO CLAIM; Clay clause.** Parts of the official Clay Yang–Mills
statement closed by this module: **0**. This is Stage 1c-0 territory;
the Stage 1b-B label is untouched.

**(ii) Reducible case included.** No irreducibility, no finiteness of
`G`, no chosen decomposition is assumed anywhere. The twirl theorem
is proved for arbitrary unitary `π, τ` in the corpus's coordinates.

**(iii) Excluded stronger readings stay excluded.** No canonical
Schur-basis / Clebsch–Gordan expansion of the projectors for
reducible `ρ`; no higher Haar moment tensors for pathological words
in which one link occurs more than twice across the two signed
plaquette words. Those are different deliverables (charter §5).

**(iv) Finite seat.** All integrals are over `G` against the
normalized invariant probability measure `μG`; all representation
spaces are `Fin m → ℂ` / `Fin n → ℂ`. No limit is taken or asserted.

This module is NOT in the root import list of the library (the corpus
pattern for recent exhibits); it is verified by a targeted build.

- Status: bricks Q13-0/Q13-1 — built 2026-10-24 under the Q13
  re-price charter; verdict STANDS (both stages, at charter
  generality); parent-verified 2026-10-24 (targeted build
  exit 0, strict recount, axiom check). Dossier:
  `whitepaper/stage1c0-q13-bricks01-2026-10-24.md`.
-/

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix

/-! ## §1. The pair action matrix (Q13-0 interface)

The Kronecker action in the entry form the charter fixes: the index
order is `(row) = (π-index, τ-index)`, `(column) = (π-index, τ-index)`,
and `pairMat A B` is the matrix of `π ⊗ τ` when `A = π g`, `B = τ g`. -/

section PairMat

variable {m n : ℕ}

/-- Product-type sums of separated factors factor:
`∑ (k,l), f k * g l = (∑ k, f k) * (∑ l, g l)`. -/
theorem sum_prod_mul (f : Fin m → ℂ) (g : Fin n → ℂ) :
    ∑ kl : Fin m × Fin n, f kl.1 * g kl.2 = (∑ k, f k) * ∑ l, g l := by
  rw [← Finset.univ_product_univ, Finset.sum_product, ← Finset.sum_mul_sum]

/-- The pair (Kronecker) action matrix, entry form:
`pairMat A B (a, b) (c, e) = A a c * B b e`. -/
def pairMat (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  Matrix.of fun p q => A p.1 q.1 * B p.2 q.2

theorem pairMat_apply (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (p q : Fin m × Fin n) :
    pairMat A B p q = A p.1 q.1 * B p.2 q.2 := rfl

theorem pairMat_one :
    pairMat (1 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext ⟨a, b⟩ ⟨c, e⟩
  by_cases h1 : a = c <;> by_cases h2 : b = e
  · subst h1; subst h2; simp [pairMat_apply]
  · simp [pairMat_apply, h1, h2, Prod.ext_iff]
  · simp [pairMat_apply, h1, h2, Prod.ext_iff]
  · simp [pairMat_apply, h1, h2, Prod.ext_iff]

/-- The pair action is multiplicative: `(π⊗τ)(g) (π⊗τ)(h)` in matrix
form is the pair action of the products. -/
theorem pairMat_mul (A C : Matrix (Fin m) (Fin m) ℂ) (B D : Matrix (Fin n) (Fin n) ℂ) :
    pairMat A B * pairMat C D = pairMat (A * C) (B * D) := by
  ext ⟨a, b⟩ ⟨c, e⟩
  rw [Matrix.mul_apply]
  simp only [pairMat_apply]
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul_sum,
    ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- The summed pair entry collapses to the product entries:
`∑ (k,l), (A a k * C k c) * (B b l * D l e) = (A * C) a c * (B * D) b e`. -/
theorem sum_pair_entries (A C : Matrix (Fin m) (Fin m) ℂ) (B D : Matrix (Fin n) (Fin n) ℂ)
    (a c : Fin m) (b e : Fin n) :
    (∑ kl : Fin m × Fin n, (A a kl.1 * C kl.1 c) * (B b kl.2 * D kl.2 e))
      = (A * C) a c * (B * D) b e := by
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul_sum,
    ← Finset.univ_product_univ, Finset.sum_product]

/-- The pair action on vectors, entry form. -/
theorem pairMat_mulVec_apply (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (w : (Fin m × Fin n) → ℂ) (p : Fin m × Fin n) :
    (pairMat A B *ᵥ w) p = ∑ q, A p.1 q.1 * B p.2 q.2 * w q := by
  show (∑ q, pairMat A B p q * w q) = ∑ q, A p.1 q.1 * B p.2 q.2 * w q
  exact Finset.sum_congr rfl fun q _ => by rw [pairMat_apply]

end PairMat

/-! ## §2. Abstract twirl apparatus (Q13-1, abstract core)

Representations are carried as matrix functions `M : G → Matrix … ℂ`
under an explicit hypothesis bundle (multiplicativity, unit, the
unitary inverse rule, entry continuity), passed as named hypotheses
to every theorem. The projector theorem is proved once at this level;
§7 discharges the corpus's representations into it. -/

section AbstractTwirl

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (μG : Measure G) [IsProbabilityMeasure μG] [Measure.IsMulLeftInvariant μG]
  [Measure.IsMulRightInvariant μG] [Measure.IsInvInvariant μG]
variable {m n : ℕ}

/-- A matrix function satisfying the multiplicative/unit/inverse
clauses of the bundle is unitary-group-valued. -/
theorem matFn_mem_unitaryGroup (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (g : G) :
    M g ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h := hMmul g g⁻¹
  rw [mul_inv_cancel, hMone, hMinv] at h
  exact h.symm

/-- Entries of a bundled matrix function are bounded by `1`. -/
theorem matFn_abs_entry (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (g : G) (a c : Fin m) :
    ‖M g a c‖ ≤ 1 :=
  abs_entry_of_mem_unitaryGroup (matFn_mem_unitaryGroup M hMmul hMone hMinv g) a c

/-- Entry products of two bundled matrix functions are integrable
against the probability measure. -/
theorem matFn_integrable_entry_mul (M : G → Matrix (Fin m) (Fin m) ℂ)
    (N : G → Matrix (Fin n) (Fin n) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c)
    (hNmul : ∀ g h : G, N (g * h) = N g * N h) (hNone : N 1 = 1)
    (hNinv : ∀ g : G, N g⁻¹ = star (N g)) (hNcont : ∀ b e, Continuous fun g => N g b e)
    (a c : Fin m) (b e : Fin n) :
    Integrable (fun g => M g a c * N g b e) μG := by
  refine MeasureTheory.Integrable.of_bound
    (((hMcont a c).mul (hNcont b e)).aestronglyMeasurable) 1 ?_
  refine Filter.Eventually.of_forall fun g => ?_
  calc ‖M g a c * N g b e‖ = ‖M g a c‖ * ‖N g b e‖ := norm_mul _ _
    _ ≤ 1 * 1 := by
        refine mul_le_mul (matFn_abs_entry M hMmul hMone hMinv g a c)
          (matFn_abs_entry N hNmul hNone hNinv g b e) (norm_nonneg _) (by norm_num)
    _ = 1 := mul_one 1

/-- The **Haar twirl** of the pair `(M, N)`, entry form (charter (3)):
`𝒥(M,N) (a,b) (c,e) = ∫ g, M g a c * N g b e ∂μG`. No matrix-valued
integral is used; the operator is its entry matrix. -/
noncomputable def haarTwirl (M : G → Matrix (Fin m) (Fin m) ℂ)
    (N : G → Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  Matrix.of fun p q => ∫ g, M g p.1 q.1 * N g p.2 q.2 ∂μG

theorem haarTwirl_apply (M : G → Matrix (Fin m) (Fin m) ℂ)
    (N : G → Matrix (Fin n) (Fin n) ℂ) (p q : Fin m × Fin n) :
    haarTwirl μG M N p q = ∫ g, M g p.1 q.1 * N g p.2 q.2 ∂μG := rfl

/-- Right invariance, entry form: right-multiplying the twirl by the
pair action at `h` leaves every entry unchanged. -/
theorem haarTwirl_mul_pairMat_apply (M : G → Matrix (Fin m) (Fin m) ℂ)
    (N : G → Matrix (Fin n) (Fin n) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c)
    (hNmul : ∀ g h : G, N (g * h) = N g * N h) (hNone : N 1 = 1)
    (hNinv : ∀ g : G, N g⁻¹ = star (N g)) (hNcont : ∀ b e, Continuous fun g => N g b e)
    (h : G) (a c : Fin m) (b e : Fin n) :
    ∑ kl : Fin m × Fin n, haarTwirl μG M N (a, b) kl * pairMat (M h) (N h) kl (c, e)
      = haarTwirl μG M N (a, b) (c, e) := by
  have hterm : ∀ kl : Fin m × Fin n,
      haarTwirl μG M N (a, b) kl * pairMat (M h) (N h) kl (c, e)
        = ∫ g, (M g a kl.1 * M h kl.1 c) * (N g b kl.2 * N h kl.2 e) ∂μG := by
    intro kl
    rw [haarTwirl_apply, pairMat_apply, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    ring
  calc ∑ kl : Fin m × Fin n, haarTwirl μG M N (a, b) kl * pairMat (M h) (N h) kl (c, e)
      = ∑ kl : Fin m × Fin n,
          ∫ g, (M g a kl.1 * M h kl.1 c) * (N g b kl.2 * N h kl.2 e) ∂μG :=
        Finset.sum_congr rfl fun kl _ => hterm kl
    _ = ∫ g, ∑ kl : Fin m × Fin n,
          (M g a kl.1 * M h kl.1 c) * (N g b kl.2 * N h kl.2 e) ∂μG := by
        rw [integral_finsetSum]
        exact fun kl _ => ((matFn_integrable_entry_mul μG M N hMmul hMone hMinv hMcont
          hNmul hNone hNinv hNcont a kl.1 b kl.2).mul_const (M h kl.1 c * N h kl.2 e)).congr
          (Filter.Eventually.of_forall fun g => (by ring :
            (M g a kl.1 * N g b kl.2) * (M h kl.1 c * N h kl.2 e)
              = (M g a kl.1 * M h kl.1 c) * (N g b kl.2 * N h kl.2 e)))
    _ = ∫ g, M (g * h) a c * N (g * h) b e ∂μG := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show (∑ kl : Fin m × Fin n, (M g a kl.1 * M h kl.1 c) * (N g b kl.2 * N h kl.2 e))
            = M (g * h) a c * N (g * h) b e
        rw [sum_pair_entries, ← hMmul, ← hNmul]
    _ = ∫ g, M g a c * N g b e ∂μG :=
        integral_mul_right_eq_self (fun u => M u a c * N u b e) h
    _ = haarTwirl μG M N (a, b) (c, e) := rfl

/-- Right invariance: `𝒥(M,N) (π⊗τ)(h) = 𝒥(M,N)`. -/
theorem haarTwirl_mul_pairMat (M : G → Matrix (Fin m) (Fin m) ℂ)
    (N : G → Matrix (Fin n) (Fin n) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c)
    (hNmul : ∀ g h : G, N (g * h) = N g * N h) (hNone : N 1 = 1)
    (hNinv : ∀ g : G, N g⁻¹ = star (N g)) (hNcont : ∀ b e, Continuous fun g => N g b e)
    (h : G) :
    haarTwirl μG M N * pairMat (M h) (N h) = haarTwirl μG M N := by
  ext ⟨a, b⟩ ⟨c, e⟩
  rw [Matrix.mul_apply]
  exact haarTwirl_mul_pairMat_apply μG M N hMmul hMone hMinv hMcont
    hNmul hNone hNinv hNcont h a c b e

/-- Left invariance, entry form. -/
theorem pairMat_mul_haarTwirl_apply (M : G → Matrix (Fin m) (Fin m) ℂ)
    (N : G → Matrix (Fin n) (Fin n) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c)
    (hNmul : ∀ g h : G, N (g * h) = N g * N h) (hNone : N 1 = 1)
    (hNinv : ∀ g : G, N g⁻¹ = star (N g)) (hNcont : ∀ b e, Continuous fun g => N g b e)
    (h : G) (a c : Fin m) (b e : Fin n) :
    ∑ kl : Fin m × Fin n, pairMat (M h) (N h) (a, b) kl * haarTwirl μG M N kl (c, e)
      = haarTwirl μG M N (a, b) (c, e) := by
  have hterm : ∀ kl : Fin m × Fin n,
      pairMat (M h) (N h) (a, b) kl * haarTwirl μG M N kl (c, e)
        = ∫ g, (M h a kl.1 * M g kl.1 c) * (N h b kl.2 * N g kl.2 e) ∂μG := by
    intro kl
    rw [haarTwirl_apply, pairMat_apply, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    ring
  calc ∑ kl : Fin m × Fin n, pairMat (M h) (N h) (a, b) kl * haarTwirl μG M N kl (c, e)
      = ∑ kl : Fin m × Fin n,
          ∫ g, (M h a kl.1 * M g kl.1 c) * (N h b kl.2 * N g kl.2 e) ∂μG :=
        Finset.sum_congr rfl fun kl _ => hterm kl
    _ = ∫ g, ∑ kl : Fin m × Fin n,
          (M h a kl.1 * M g kl.1 c) * (N h b kl.2 * N g kl.2 e) ∂μG := by
        rw [integral_finsetSum]
        exact fun kl _ => ((matFn_integrable_entry_mul μG M N hMmul hMone hMinv hMcont
          hNmul hNone hNinv hNcont kl.1 c kl.2 e).const_mul (M h a kl.1 * N h b kl.2)).congr
          (Filter.Eventually.of_forall fun g => (by ring :
            (M h a kl.1 * N h b kl.2) * (M g kl.1 c * N g kl.2 e)
              = (M h a kl.1 * M g kl.1 c) * (N h b kl.2 * N g kl.2 e)))
    _ = ∫ g, M (h * g) a c * N (h * g) b e ∂μG := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show (∑ kl : Fin m × Fin n, (M h a kl.1 * M g kl.1 c) * (N h b kl.2 * N g kl.2 e))
            = M (h * g) a c * N (h * g) b e
        rw [sum_pair_entries, ← hMmul, ← hNmul]
    _ = ∫ g, M g a c * N g b e ∂μG :=
        integral_mul_left_eq_self (fun u => M u a c * N u b e) h
    _ = haarTwirl μG M N (a, b) (c, e) := rfl

/-- Left invariance: `(π⊗τ)(h) 𝒥(M,N) = 𝒥(M,N)`. -/
theorem pairMat_mul_haarTwirl (M : G → Matrix (Fin m) (Fin m) ℂ)
    (N : G → Matrix (Fin n) (Fin n) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c)
    (hNmul : ∀ g h : G, N (g * h) = N g * N h) (hNone : N 1 = 1)
    (hNinv : ∀ g : G, N g⁻¹ = star (N g)) (hNcont : ∀ b e, Continuous fun g => N g b e)
    (h : G) :
    pairMat (M h) (N h) * haarTwirl μG M N = haarTwirl μG M N := by
  ext ⟨a, b⟩ ⟨c, e⟩
  rw [Matrix.mul_apply]
  exact pairMat_mul_haarTwirl_apply μG M N hMmul hMone hMinv hMcont
    hNmul hNone hNinv hNcont h a c b e

end AbstractTwirl

/-! ## §3. The projector package (charter eq. (5))

The canonical reduction `𝒥(π,τ) = P_{(V_π ⊗ V_τ)^G}` is discharged as:
the twirl's range lies in the invariant submodule, it fixes the
invariant submodule pointwise, it is idempotent and self-adjoint, and
packaged as a `LinearMap.IsProj` of its `Matrix.mulVecLin` onto the
invariant submodule, with range exactly that submodule. -/

section AbstractProjector

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (μG : Measure G) [IsProbabilityMeasure μG] [Measure.IsMulLeftInvariant μG]
  [Measure.IsMulRightInvariant μG] [Measure.IsInvInvariant μG]
variable {m n : ℕ}

/-- Matrix action on vectors, entry form (definitional unfolding). -/
theorem mat_mulVec_apply {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (w : ι → ℂ) (p : ι) :
    (A *ᵥ w) p = ∑ q, A p q * w q := rfl

/-- The invariant submodule of the pair action. -/
def pairInvariantSubmodule (M : G → Matrix (Fin m) (Fin m) ℂ)
    (N : G → Matrix (Fin n) (Fin n) ℂ) :
    Submodule ℂ ((Fin m × Fin n) → ℂ) where
  carrier := {w | ∀ h : G, pairMat (M h) (N h) *ᵥ w = w}
  add_mem' := by
    intro x y hx hy h
    rw [Matrix.mulVec_add, hx h, hy h]
  zero_mem' := by
    intro h
    exact Matrix.mulVec_zero _
  smul_mem' := by
    intro c x hx h
    rw [Matrix.mulVec_smul, hx h]

theorem mem_pairInvariantSubmodule (M : G → Matrix (Fin m) (Fin m) ℂ)
    (N : G → Matrix (Fin n) (Fin n) ℂ) (w : (Fin m × Fin n) → ℂ) :
    w ∈ pairInvariantSubmodule M N ↔ ∀ h : G, pairMat (M h) (N h) *ᵥ w = w := Iff.rfl

/-- The twirl's range lies in the invariant submodule. -/
theorem haarTwirl_mulVec_mem (M : G → Matrix (Fin m) (Fin m) ℂ)
    (N : G → Matrix (Fin n) (Fin n) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c)
    (hNmul : ∀ g h : G, N (g * h) = N g * N h) (hNone : N 1 = 1)
    (hNinv : ∀ g : G, N g⁻¹ = star (N g)) (hNcont : ∀ b e, Continuous fun g => N g b e)
    (w : (Fin m × Fin n) → ℂ) :
    haarTwirl μG M N *ᵥ w ∈ pairInvariantSubmodule M N := by
  intro h
  rw [Matrix.mulVec_mulVec, pairMat_mul_haarTwirl μG M N hMmul hMone hMinv hMcont
    hNmul hNone hNinv hNcont h]

/-- The twirl fixes every invariant vector. -/
theorem haarTwirl_mulVec_of_mem (M : G → Matrix (Fin m) (Fin m) ℂ)
    (N : G → Matrix (Fin n) (Fin n) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c)
    (hNmul : ∀ g h : G, N (g * h) = N g * N h) (hNone : N 1 = 1)
    (hNinv : ∀ g : G, N g⁻¹ = star (N g)) (hNcont : ∀ b e, Continuous fun g => N g b e)
    {w : (Fin m × Fin n) → ℂ} (hw : w ∈ pairInvariantSubmodule M N) :
    haarTwirl μG M N *ᵥ w = w := by
  funext p
  obtain ⟨a, b⟩ := p
  rw [mat_mulVec_apply]
  have hterm : ∀ q : Fin m × Fin n,
      haarTwirl μG M N (a, b) q * w q
        = ∫ g, (M g a q.1 * N g b q.2) * w q ∂μG := by
    intro q
    rw [haarTwirl_apply, ← integral_mul_const]
  calc ∑ q : Fin m × Fin n, haarTwirl μG M N (a, b) q * w q
      = ∑ q : Fin m × Fin n, ∫ g, (M g a q.1 * N g b q.2) * w q ∂μG :=
        Finset.sum_congr rfl fun q _ => hterm q
    _ = ∫ g, ∑ q : Fin m × Fin n, (M g a q.1 * N g b q.2) * w q ∂μG := by
        rw [integral_finsetSum]
        exact fun q _ => (matFn_integrable_entry_mul μG M N hMmul hMone hMinv hMcont
          hNmul hNone hNinv hNcont a q.1 b q.2).mul_const _
    _ = ∫ g, (pairMat (M g) (N g) *ᵥ w) (a, b) ∂μG := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show (∑ q : Fin m × Fin n, (M g a q.1 * N g b q.2) * w q)
            = (pairMat (M g) (N g) *ᵥ w) (a, b)
        rw [pairMat_mulVec_apply]
    _ = ∫ g, w (a, b) ∂μG := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show (pairMat (M g) (N g) *ᵥ w) (a, b) = w (a, b)
        rw [hw g]
    _ = w (a, b) := by simp

/-- Idempotence: `𝒥(M,N)² = 𝒥(M,N)`. -/
theorem haarTwirl_mul_self (M : G → Matrix (Fin m) (Fin m) ℂ)
    (N : G → Matrix (Fin n) (Fin n) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c)
    (hNmul : ∀ g h : G, N (g * h) = N g * N h) (hNone : N 1 = 1)
    (hNinv : ∀ g : G, N g⁻¹ = star (N g)) (hNcont : ∀ b e, Continuous fun g => N g b e) :
    haarTwirl μG M N * haarTwirl μG M N = haarTwirl μG M N := by
  ext p q
  have hfix := congrFun (haarTwirl_mulVec_of_mem μG M N hMmul hMone hMinv hMcont
    hNmul hNone hNinv hNcont
    (haarTwirl_mulVec_mem μG M N hMmul hMone hMinv hMcont
      hNmul hNone hNinv hNcont (Pi.single q 1))) p
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hfix

/-- Self-adjointness: `𝒥(M,N)⋆ = 𝒥(M,N)`. -/
theorem haarTwirl_star (M : G → Matrix (Fin m) (Fin m) ℂ)
    (N : G → Matrix (Fin n) (Fin n) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c)
    (hNmul : ∀ g h : G, N (g * h) = N g * N h) (hNone : N 1 = 1)
    (hNinv : ∀ g : G, N g⁻¹ = star (N g)) (hNcont : ∀ b e, Continuous fun g => N g b e) :
    star (haarTwirl μG M N) = haarTwirl μG M N := by
  ext ⟨a, b⟩ ⟨c, e⟩
  have hpt : ∀ g : G, star (M g c a * N g e b) = M g⁻¹ a c * N g⁻¹ b e := by
    intro g
    rw [star_mul, ← Matrix.star_apply, ← Matrix.star_apply, ← hMinv, ← hNinv]
    exact mul_comm _ _
  have hsub : (∫ g, M g a c * N g b e ∂μG) = ∫ g, M g⁻¹ a c * N g⁻¹ b e ∂μG :=
    (integral_inv_eq_self (fun u => M u a c * N u b e) μG).symm
  have hstar : star (∫ g, M g c a * N g e b ∂μG)
      = ∫ g, M g⁻¹ a c * N g⁻¹ b e ∂μG := by
    rw [show star (∫ g, M g c a * N g e b ∂μG)
        = ∫ g, star (M g c a * N g e b) ∂μG from
      (by simpa only [starRingEnd_apply] using
        (integral_conj (μ := μG) (f := fun g => M g c a * N g e b)).symm)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact hpt g
  rw [Matrix.star_apply, haarTwirl_apply, haarTwirl_apply, hsub]
  exact hstar

/-- The projector package: the twirl, as a linear map, is the
projection onto the invariant submodule of the pair action. -/
theorem haarTwirl_isProj (M : G → Matrix (Fin m) (Fin m) ℂ)
    (N : G → Matrix (Fin n) (Fin n) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c)
    (hNmul : ∀ g h : G, N (g * h) = N g * N h) (hNone : N 1 = 1)
    (hNinv : ∀ g : G, N g⁻¹ = star (N g)) (hNcont : ∀ b e, Continuous fun g => N g b e) :
    LinearMap.IsProj (pairInvariantSubmodule M N)
      (Matrix.mulVecLin (haarTwirl μG M N)) where
  map_mem := fun w => by
    rw [Matrix.mulVecLin_apply]
    exact haarTwirl_mulVec_mem μG M N hMmul hMone hMinv hMcont
      hNmul hNone hNinv hNcont w
  map_id := fun w hw => by
    rw [Matrix.mulVecLin_apply]
    exact haarTwirl_mulVec_of_mem μG M N hMmul hMone hMinv hMcont
      hNmul hNone hNinv hNcont hw

/-- The twirl's range is exactly the invariant submodule. -/
theorem haarTwirl_range (M : G → Matrix (Fin m) (Fin m) ℂ)
    (N : G → Matrix (Fin n) (Fin n) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c)
    (hNmul : ∀ g h : G, N (g * h) = N g * N h) (hNone : N 1 = 1)
    (hNinv : ∀ g : G, N g⁻¹ = star (N g)) (hNcont : ∀ b e, Continuous fun g => N g b e) :
    LinearMap.range (Matrix.mulVecLin (haarTwirl μG M N))
      = pairInvariantSubmodule M N := by
  apply le_antisymm
  · rintro w ⟨x, hx⟩
    rw [← hx, Matrix.mulVecLin_apply]
    exact haarTwirl_mulVec_mem μG M N hMmul hMone hMinv hMcont
      hNmul hNone hNinv hNcont x
  · intro w hw
    refine ⟨w, ?_⟩
    rw [Matrix.mulVecLin_apply]
    exact haarTwirl_mulVec_of_mem μG M N hMmul hMone hMinv hMcont
      hNmul hNone hNinv hNcont hw

/-- Trace identity: `tr 𝒥(M,N) = ∫ tr(M g) · tr(N g) dμG` — for an
irreducible pair this is the invariant-subspace dimension formula;
here it is stated and proved without any irreducibility. -/
theorem haarTwirl_trace (M : G → Matrix (Fin m) (Fin m) ℂ)
    (N : G → Matrix (Fin n) (Fin n) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c)
    (hNmul : ∀ g h : G, N (g * h) = N g * N h) (hNone : N 1 = 1)
    (hNinv : ∀ g : G, N g⁻¹ = star (N g)) (hNcont : ∀ b e, Continuous fun g => N g b e) :
    Matrix.trace (haarTwirl μG M N)
      = ∫ g, Matrix.trace (M g) * Matrix.trace (N g) ∂μG := by
  calc Matrix.trace (haarTwirl μG M N)
      = ∑ p : Fin m × Fin n, ∫ g, M g p.1 p.1 * N g p.2 p.2 ∂μG := by
        show (∑ p : Fin m × Fin n, haarTwirl μG M N p p) = _
        exact Finset.sum_congr rfl fun p _ => haarTwirl_apply μG M N p p
    _ = ∫ g, ∑ p : Fin m × Fin n, M g p.1 p.1 * N g p.2 p.2 ∂μG := by
        rw [integral_finsetSum]
        exact fun p _ => matFn_integrable_entry_mul μG M N hMmul hMone hMinv hMcont
          hNmul hNone hNinv hNcont p.1 p.1 p.2 p.2
    _ = ∫ g, Matrix.trace (M g) * Matrix.trace (N g) ∂μG := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show (∑ p : Fin m × Fin n, M g p.1 p.1 * N g p.2 p.2)
            = Matrix.trace (M g) * Matrix.trace (N g)
        have key : (∑ p : Fin m × Fin n, M g p.1 p.1 * N g p.2 p.2)
            = (∑ k, M g k k) * (∑ l, N g l l) := by
          rw [Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
        exact key.trans (by rfl)

end AbstractProjector

/-! ## §4. The one-factor twirl (charter eq. (4))

The boundary case `𝒥(π) = ∫ π(g) dμG`: entered both directly and as
the pair twirl against the trivial representation. Its fixed
submodule package mirrors §3. -/

section OneFactor

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (μG : Measure G) [IsProbabilityMeasure μG] [Measure.IsMulLeftInvariant μG]
  [Measure.IsMulRightInvariant μG] [Measure.IsInvInvariant μG]
variable {m : ℕ}

/-- Single entries of a bundled matrix function are integrable. -/
theorem matFn_integrable_entry (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c)
    (a c : Fin m) :
    Integrable (fun g => M g a c) μG := by
  refine MeasureTheory.Integrable.of_bound ((hMcont a c).aestronglyMeasurable) 1 ?_
  exact Filter.Eventually.of_forall fun g => matFn_abs_entry M hMmul hMone hMinv g a c

/-- The **one-factor Haar twirl** `𝒥(M) = ∫ M(g) dμG`, entry form. -/
noncomputable def haarTwirl1 (M : G → Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun a c => ∫ g, M g a c ∂μG

theorem haarTwirl1_apply (M : G → Matrix (Fin m) (Fin m) ℂ) (a c : Fin m) :
    haarTwirl1 μG M a c = ∫ g, M g a c ∂μG := rfl

/-- Right invariance of the one-factor twirl, entry form. -/
theorem haarTwirl1_mul_apply (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c)
    (h : G) (a c : Fin m) :
    ∑ k, haarTwirl1 μG M a k * M h k c = haarTwirl1 μG M a c := by
  calc ∑ k, haarTwirl1 μG M a k * M h k c
      = ∑ k, ∫ g, M g a k * M h k c ∂μG :=
        Finset.sum_congr rfl fun k _ => by rw [haarTwirl1_apply, ← integral_mul_const]
    _ = ∫ g, ∑ k, M g a k * M h k c ∂μG := by
        rw [integral_finsetSum]
        exact fun k _ => (matFn_integrable_entry μG M hMmul hMone hMinv hMcont a k).mul_const _
    _ = ∫ g, M (g * h) a c ∂μG := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show (∑ k, M g a k * M h k c) = M (g * h) a c
        rw [← Matrix.mul_apply, ← hMmul]
    _ = ∫ g, M g a c ∂μG := integral_mul_right_eq_self (fun u => M u a c) h
    _ = haarTwirl1 μG M a c := rfl

/-- Left invariance of the one-factor twirl, entry form. -/
theorem mul_haarTwirl1_apply (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c)
    (h : G) (a c : Fin m) :
    ∑ k, M h a k * haarTwirl1 μG M k c = haarTwirl1 μG M a c := by
  calc ∑ k, M h a k * haarTwirl1 μG M k c
      = ∑ k, ∫ g, M h a k * M g k c ∂μG :=
        Finset.sum_congr rfl fun k _ => by rw [haarTwirl1_apply, ← integral_const_mul]
    _ = ∫ g, ∑ k, M h a k * M g k c ∂μG := by
        rw [integral_finsetSum]
        exact fun k _ => (matFn_integrable_entry μG M hMmul hMone hMinv hMcont k c).const_mul _
    _ = ∫ g, M (h * g) a c ∂μG := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show (∑ k, M h a k * M g k c) = M (h * g) a c
        rw [← Matrix.mul_apply, ← hMmul]
    _ = ∫ g, M g a c ∂μG := integral_mul_left_eq_self (fun u => M u a c) h
    _ = haarTwirl1 μG M a c := rfl

/-- Right invariance: `𝒥(M) M(h) = 𝒥(M)`. -/
theorem haarTwirl1_mul (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c)
    (h : G) :
    haarTwirl1 μG M * M h = haarTwirl1 μG M := by
  ext a c
  rw [Matrix.mul_apply]
  exact haarTwirl1_mul_apply μG M hMmul hMone hMinv hMcont h a c

/-- Left invariance: `M(h) 𝒥(M) = 𝒥(M)`. -/
theorem mul_haarTwirl1 (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c)
    (h : G) :
    M h * haarTwirl1 μG M = haarTwirl1 μG M := by
  ext a c
  rw [Matrix.mul_apply]
  exact mul_haarTwirl1_apply μG M hMmul hMone hMinv hMcont h a c

/-- The fixed submodule of a single matrix function. -/
def fixedSubmodule (M : G → Matrix (Fin m) (Fin m) ℂ) :
    Submodule ℂ (Fin m → ℂ) where
  carrier := {v | ∀ h : G, M h *ᵥ v = v}
  add_mem' := by
    intro x y hx hy h
    rw [Matrix.mulVec_add, hx h, hy h]
  zero_mem' := by
    intro h
    exact Matrix.mulVec_zero _
  smul_mem' := by
    intro c x hx h
    rw [Matrix.mulVec_smul, hx h]

theorem mem_fixedSubmodule (M : G → Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) :
    v ∈ fixedSubmodule M ↔ ∀ h : G, M h *ᵥ v = v := Iff.rfl

/-- The one-factor twirl's range lies in the fixed submodule. -/
theorem haarTwirl1_mulVec_mem (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c)
    (v : Fin m → ℂ) :
    haarTwirl1 μG M *ᵥ v ∈ fixedSubmodule M := by
  intro h
  rw [Matrix.mulVec_mulVec, mul_haarTwirl1 μG M hMmul hMone hMinv hMcont h]

/-- The one-factor twirl fixes every fixed vector. -/
theorem haarTwirl1_mulVec_of_mem (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c)
    {v : Fin m → ℂ} (hv : v ∈ fixedSubmodule M) :
    haarTwirl1 μG M *ᵥ v = v := by
  funext a
  rw [mat_mulVec_apply]
  have hterm : ∀ k : Fin m, haarTwirl1 μG M a k * v k = ∫ g, M g a k * v k ∂μG := by
    intro k
    rw [haarTwirl1_apply, ← integral_mul_const]
  calc ∑ k : Fin m, haarTwirl1 μG M a k * v k
      = ∑ k : Fin m, ∫ g, M g a k * v k ∂μG :=
        Finset.sum_congr rfl fun k _ => hterm k
    _ = ∫ g, ∑ k : Fin m, M g a k * v k ∂μG := by
        rw [integral_finsetSum]
        exact fun k _ => (matFn_integrable_entry μG M hMmul hMone hMinv hMcont a k).mul_const _
    _ = ∫ g, (M g *ᵥ v) a ∂μG := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show (∑ k : Fin m, M g a k * v k) = (M g *ᵥ v) a
        rw [mat_mulVec_apply]
    _ = ∫ g, v a ∂μG := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show (M g *ᵥ v) a = v a
        rw [hv g]
    _ = v a := by simp

/-- Idempotence: `𝒥(M)² = 𝒥(M)`. -/
theorem haarTwirl1_mul_self (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c) :
    haarTwirl1 μG M * haarTwirl1 μG M = haarTwirl1 μG M := by
  ext a c
  have hfix := congrFun (haarTwirl1_mulVec_of_mem μG M hMmul hMone hMinv hMcont
    (haarTwirl1_mulVec_mem μG M hMmul hMone hMinv hMcont (Pi.single c 1))) a
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hfix

/-- Self-adjointness: `𝒥(M)⋆ = 𝒥(M)`. -/
theorem haarTwirl1_star (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c) :
    star (haarTwirl1 μG M) = haarTwirl1 μG M := by
  ext a c
  have hpt : ∀ g : G, star (M g c a) = M g⁻¹ a c := by
    intro g
    rw [← Matrix.star_apply, ← hMinv]
  have hsub : (∫ g, M g a c ∂μG) = ∫ g, M g⁻¹ a c ∂μG :=
    (integral_inv_eq_self (fun u => M u a c) μG).symm
  have hstar : star (∫ g, M g c a ∂μG) = ∫ g, M g⁻¹ a c ∂μG := by
    rw [show star (∫ g, M g c a ∂μG) = ∫ g, star (M g c a) ∂μG from
      (by simpa only [starRingEnd_apply] using
        (integral_conj (μ := μG) (f := fun g => M g c a)).symm)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact hpt g
  rw [Matrix.star_apply, haarTwirl1_apply, haarTwirl1_apply, hsub]
  exact hstar

/-- The one-factor projector package. -/
theorem haarTwirl1_isProj (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c) :
    LinearMap.IsProj (fixedSubmodule M) (Matrix.mulVecLin (haarTwirl1 μG M)) where
  map_mem := fun v => by
    rw [Matrix.mulVecLin_apply]
    exact haarTwirl1_mulVec_mem μG M hMmul hMone hMinv hMcont v
  map_id := fun v hv => by
    rw [Matrix.mulVecLin_apply]
    exact haarTwirl1_mulVec_of_mem μG M hMmul hMone hMinv hMcont hv

/-- The one-factor twirl's range is exactly the fixed submodule. -/
theorem haarTwirl1_range (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c) :
    LinearMap.range (Matrix.mulVecLin (haarTwirl1 μG M)) = fixedSubmodule M := by
  apply le_antisymm
  · rintro w ⟨x, hx⟩
    rw [← hx, Matrix.mulVecLin_apply]
    exact haarTwirl1_mulVec_mem μG M hMmul hMone hMinv hMcont x
  · intro w hw
    refine ⟨w, ?_⟩
    rw [Matrix.mulVecLin_apply]
    exact haarTwirl1_mulVec_of_mem μG M hMmul hMone hMinv hMcont hw

/-- The trivial one-dimensional matrix function: constantly `1`. -/
def trivMat (G : Type*) : G → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 1

theorem trivMat_apply (g : G) (a c : Fin 1) : trivMat G g a c = 1 := by
  obtain rfl : a = c := Subsingleton.elim a c
  simp [trivMat]

theorem trivMat_mul : ∀ g h : G, trivMat G (g * h) = trivMat G g * trivMat G h := by
  intro g h
  simp [trivMat]

theorem trivMat_one : trivMat G 1 = 1 := rfl

theorem trivMat_inv : ∀ g : G, trivMat G g⁻¹ = star (trivMat G g) := by
  intro g
  simp [trivMat]

theorem trivMat_cont : ∀ a c, Continuous fun g => trivMat G g a c := by
  intro a c
  have hfun : (fun g => trivMat G g a c) = fun _ => (1 : ℂ) :=
    funext fun g => trivMat_apply g a c
  rw [hfun]
  exact continuous_const

/-- The boundary identity of charter eq. (4): the one-factor twirl is
the pair twirl against the trivial representation, read at the
`Fin 1` index. -/
theorem haarTwirl1_apply_eq (M : G → Matrix (Fin m) (Fin m) ℂ) (a c : Fin m) :
    haarTwirl1 μG M a c = haarTwirl μG M (trivMat G) (a, 0) (c, 0) := by
  rw [haarTwirl1_apply, haarTwirl_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show M g a c = M g a c * trivMat G g 0 0
  rw [trivMat_apply]
  exact (mul_one _).symm

end OneFactor

/-! ## §5. Orientations and the dictionary (Q13-1)

The four orientations of a matrix function, the bundle-transfer
lemmas, and the dictionary: the literal matrix inverse is the dual
orientation with its transpose wiring (charter §1.2), and for a
unitary matrix function the dual and conjugate orientations coincide
entrywise, so the conjugate-dual collapses to the identity. -/

section Orientations

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {m : ℕ}

/-- Entrywise conjugate orientation `M̄`. -/
def orientConj (M : G → Matrix (Fin m) (Fin m) ℂ) : G → Matrix (Fin m) (Fin m) ℂ :=
  fun g => (M g).map (starRingEnd ℂ)

/-- Dual orientation `M^∨`, `M^∨(g) = M(g⁻¹)ᵀ`. -/
def orientDual (M : G → Matrix (Fin m) (Fin m) ℂ) : G → Matrix (Fin m) (Fin m) ℂ :=
  fun g => (M g⁻¹)ᵀ

/-- Conjugate-dual orientation `M̄^∨`. -/
def orientConjDual (M : G → Matrix (Fin m) (Fin m) ℂ) : G → Matrix (Fin m) (Fin m) ℂ :=
  orientConj (orientDual M)

theorem orientConj_apply (M : G → Matrix (Fin m) (Fin m) ℂ) (g : G) (a c : Fin m) :
    orientConj M g a c = star (M g a c) := rfl

theorem orientDual_apply (M : G → Matrix (Fin m) (Fin m) ℂ) (g : G) (a c : Fin m) :
    orientDual M g a c = M g⁻¹ c a := rfl

/-- `N` is an **orientation bundle** over `M`: `N` itself satisfies the
multiplicative/unit/inverse/continuity bundle. (The predicate does
not otherwise relate `N` to `M`; it records that `N` is one of the
admissible pair partners for `M`'s twirl package.) -/
def IsOrientationMat (M N : G → Matrix (Fin m) (Fin m) ℂ) : Prop :=
  (∀ g h : G, N (g * h) = N g * N h) ∧ N 1 = 1 ∧ (∀ g : G, N g⁻¹ = star (N g))
    ∧ ∀ a c, Continuous fun g => N g a c

theorem isOrientationMat_self (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hmul : ∀ g h : G, M (g * h) = M g * M h) (hone : M 1 = 1)
    (hinv : ∀ g : G, M g⁻¹ = star (M g)) (hcont : ∀ a c, Continuous fun g => M g a c) :
    IsOrientationMat M M := ⟨hmul, hone, hinv, hcont⟩

theorem orientConj_mul (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hmul : ∀ g h : G, M (g * h) = M g * M h) (g h : G) :
    orientConj M (g * h) = orientConj M g * orientConj M h := by
  ext a c
  rw [orientConj_apply, hmul, Matrix.mul_apply, Matrix.mul_apply, star_sum]
  exact Finset.sum_congr rfl fun k _ => by
    simp only [orientConj_apply, star_mul]
    exact mul_comm _ _

theorem orientConj_one (M : G → Matrix (Fin m) (Fin m) ℂ) (hone : M 1 = 1) :
    orientConj M 1 = 1 := by
  ext a c
  rw [orientConj_apply, hone]
  by_cases h : a = c <;> simp [Matrix.one_apply, h]

theorem orientConj_inv (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hinv : ∀ g : G, M g⁻¹ = star (M g)) (g : G) :
    orientConj M g⁻¹ = star (orientConj M g) := by
  ext a c
  rw [orientConj_apply, Matrix.star_apply, orientConj_apply, hinv, Matrix.star_apply]

theorem orientConj_cont (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hcont : ∀ a c, Continuous fun g => M g a c) (a c : Fin m) :
    Continuous fun g => orientConj M g a c := by
  have hfun : (fun g => orientConj M g a c) = fun g => star (M g a c) :=
    funext fun g => orientConj_apply M g a c
  rw [hfun]
  exact (hcont a c).star

theorem isOrientationMat_conj (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hmul : ∀ g h : G, M (g * h) = M g * M h) (hone : M 1 = 1)
    (hinv : ∀ g : G, M g⁻¹ = star (M g)) (hcont : ∀ a c, Continuous fun g => M g a c) :
    IsOrientationMat M (orientConj M) :=
  ⟨fun g h => orientConj_mul M hmul g h, orientConj_one M hone,
    fun g => orientConj_inv M hinv g, fun a c => orientConj_cont M hcont a c⟩

theorem orientDual_mul (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hmul : ∀ g h : G, M (g * h) = M g * M h) (g h : G) :
    orientDual M (g * h) = orientDual M g * orientDual M h := by
  show (M (g * h)⁻¹)ᵀ = (M g⁻¹)ᵀ * (M h⁻¹)ᵀ
  rw [mul_inv_rev, hmul, Matrix.transpose_mul]

theorem orientDual_one (M : G → Matrix (Fin m) (Fin m) ℂ) (hone : M 1 = 1) :
    orientDual M 1 = 1 := by
  ext a c
  rw [orientDual_apply, inv_one, hone]
  rcases eq_or_ne a c with h | h
  · subst h; simp [Matrix.one_apply]
  · simp [Matrix.one_apply, h, Ne.symm h]

theorem orientDual_inv (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hinv : ∀ g : G, M g⁻¹ = star (M g)) (g : G) :
    orientDual M g⁻¹ = star (orientDual M g) := by
  ext a c
  rw [orientDual_apply, inv_inv, Matrix.star_apply, orientDual_apply, hinv,
    Matrix.star_apply, star_star]

theorem orientDual_cont (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hcont : ∀ a c, Continuous fun g => M g a c) (a c : Fin m) :
    Continuous fun g => orientDual M g a c := by
  have hfun : (fun g => orientDual M g a c) = fun g => M g⁻¹ c a :=
    funext fun g => orientDual_apply M g a c
  rw [hfun]
  exact (hcont c a).comp continuous_inv

theorem isOrientationMat_dual (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hmul : ∀ g h : G, M (g * h) = M g * M h) (hone : M 1 = 1)
    (hinv : ∀ g : G, M g⁻¹ = star (M g)) (hcont : ∀ a c, Continuous fun g => M g a c) :
    IsOrientationMat M (orientDual M) :=
  ⟨fun g h => orientDual_mul M hmul g h, orientDual_one M hone,
    fun g => orientDual_inv M hinv g, fun a c => orientDual_cont M hcont a c⟩

/-- Dictionary, entry form: for a unitary matrix function, the dual
orientation's entries are the conjugate orientation's entries. -/
theorem orientDual_apply_eq (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hinv : ∀ g : G, M g⁻¹ = star (M g)) (g : G) (a c : Fin m) :
    orientDual M g a c = star (M g a c) := by
  rw [orientDual_apply, hinv, Matrix.star_apply]

/-- Dictionary: dual = conjugate for unitary matrix functions. -/
theorem orientDual_eq_orientConj (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hinv : ∀ g : G, M g⁻¹ = star (M g)) (g : G) :
    orientDual M g = orientConj M g := by
  ext a c
  rw [orientDual_apply_eq M hinv, orientConj_apply]

/-- Dictionary: the literal matrix inverse is the dual orientation
with its transpose wiring (charter §1.2). -/
theorem mat_inv_eq_dual_transpose (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hmul : ∀ g h : G, M (g * h) = M g * M h) (hone : M 1 = 1)
    (hinv : ∀ g : G, M g⁻¹ = star (M g)) (g : G) :
    (M g)⁻¹ = (orientDual M g)ᵀ := by
  have hU : star (M g) * M g = 1 := by
    rw [← hinv, ← hmul, inv_mul_cancel, hone]
  have hinv' : (M g)⁻¹ = star (M g) := Matrix.inv_eq_left_inv hU
  rw [hinv']
  show star (M g) = ((M g⁻¹)ᵀ)ᵀ
  rw [Matrix.transpose_transpose, hinv]

/-- Dictionary: the conjugate-dual orientation collapses to the
identity for unitary matrix functions. -/
theorem orientConjDual_eq (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hinv : ∀ g : G, M g⁻¹ = star (M g)) (g : G) :
    orientConjDual M g = M g := by
  ext a c
  show orientConj (orientDual M) g a c = M g a c
  rw [orientConj_apply, orientDual_apply_eq M hinv, star_star]

theorem isOrientationMat_conjDual (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hmul : ∀ g h : G, M (g * h) = M g * M h) (hone : M 1 = 1)
    (hinv : ∀ g : G, M g⁻¹ = star (M g)) (hcont : ∀ a c, Continuous fun g => M g a c) :
    IsOrientationMat M (orientConjDual M) := by
  have hfun : orientConjDual M = M := funext fun g => orientConjDual_eq M hinv g
  rw [hfun]
  exact isOrientationMat_self M hmul hone hinv hcont

end Orientations

/-! ## §6. The conjugation twirl on `End(V)` (the `ρ ⊗ ρ̄` sector)

`twirlEndo M X = ∫ M(g) X M(g)⋆ dμG`, the `End(V)`-valued form of the
twirl at the pair `(M, M̄)`, with its J-contraction form: the entries
of the conjugation twirl are the `𝒥(M, M̄)`-contractions of `X`. -/

section TwirlEndo

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (μG : Measure G) [IsProbabilityMeasure μG] [Measure.IsMulLeftInvariant μG]
  [Measure.IsMulRightInvariant μG] [Measure.IsInvInvariant μG]
variable {m : ℕ}

/-- The conjugation twirl on endomorphisms, entry form. -/
noncomputable def twirlEndo (M : G → Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin m) (Fin m) ℂ → Matrix (Fin m) (Fin m) ℂ :=
  fun X => Matrix.of fun a b => ∫ g, (M g * X * star (M g)) a b ∂μG

theorem twirlEndo_apply (M : G → Matrix (Fin m) (Fin m) ℂ)
    (X : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m) :
    twirlEndo μG M X a b = ∫ g, (M g * X * star (M g)) a b ∂μG := rfl

/-- The J-contraction form of the conjugation twirl:
`twirlEndo M X = ∑_{c,e} 𝒥(M, M̄)_{(a,b),(c,e)} • X c e` entrywise. -/
theorem twirlEndo_eq_sum (M : G → Matrix (Fin m) (Fin m) ℂ)
    (hMmul : ∀ g h : G, M (g * h) = M g * M h) (hMone : M 1 = 1)
    (hMinv : ∀ g : G, M g⁻¹ = star (M g)) (hMcont : ∀ a c, Continuous fun g => M g a c)
    (X : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m) :
    twirlEndo μG M X a b
      = ∑ c, ∑ e, haarTwirl μG M (orientConj M) (a, b) (c, e) * X c e := by
  have hInt : ∀ c e : Fin m, Integrable (fun g => M g a c * orientConj M g b e) μG :=
    fun c e => matFn_integrable_entry_mul μG M (orientConj M) hMmul hMone hMinv hMcont
      (orientConj_mul M hMmul) (orientConj_one M hMone) (orientConj_inv M hMinv)
      (orientConj_cont M hMcont) a c b e
  calc twirlEndo μG M X a b
      = ∫ g, ∑ c, ∑ e, M g a c * X c e * star (M g b e) ∂μG := by
        rw [twirlEndo_apply]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show (M g * X * star (M g)) a b = ∑ c, ∑ e, M g a c * X c e * star (M g b e)
        rw [Matrix.mul_apply, Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Matrix.mul_apply, Matrix.star_apply, Finset.sum_mul]
    _ = ∑ c, ∫ g, ∑ e, M g a c * X c e * star (M g b e) ∂μG :=
        integral_finsetSum Finset.univ (fun c _ =>
          MeasureTheory.integrable_finsetSum Finset.univ (fun e _ =>
            ((hInt c e).mul_const (X c e)).congr
              (Filter.Eventually.of_forall fun g => (by rw [orientConj_apply]; ring :
                (M g a c * orientConj M g b e) * X c e
                  = M g a c * X c e * star (M g b e)))))
    _ = ∑ c, ∑ e, ∫ g, M g a c * X c e * star (M g b e) ∂μG :=
        Finset.sum_congr rfl fun c _ => integral_finsetSum Finset.univ
          (fun e _ => ((hInt c e).mul_const (X c e)).congr
            (Filter.Eventually.of_forall fun g => (by rw [orientConj_apply]; ring :
              (M g a c * orientConj M g b e) * X c e
                = M g a c * X c e * star (M g b e))))
    _ = ∑ c, ∑ e, haarTwirl μG M (orientConj M) (a, b) (c, e) * X c e := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
        rw [haarTwirl_apply, ← integral_mul_const]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show M g a c * X c e * star (M g b e) = (M g a c * orientConj M g b e) * X c e
        rw [orientConj_apply]
        ring

end TwirlEndo

/-! ## §7. Corpus discharge (Q13-1, instantiated)

The corpus's `repMatrix ρ` satisfies the abstract bundle
(`repMatrix_mul`, `repMatrix_one`, `repMatrix_inv` are landed;
entry continuity is `Continuous.matrix_elem` of the standing
hypothesis `hρcont`, the same hypothesis the landed covariance
theorems carry). Hence every orientation pair of `ρ` carries the
full projector package of §3, with no irreducibility and no added
hypothesis on `ρ`. -/

section Corpus

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (μG : Measure G) [IsProbabilityMeasure μG] [Measure.IsMulLeftInvariant μG]
  [Measure.IsMulRightInvariant μG] [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- The conjugate orientation of the corpus representation. -/
def repMatConj : G → Matrix (Fin d) (Fin d) ℂ := orientConj (repMatrix ρ)

/-- The dual orientation of the corpus representation. -/
def repMatDual : G → Matrix (Fin d) (Fin d) ℂ := orientDual (repMatrix ρ)

/-- The conjugate-dual orientation of the corpus representation. -/
def repMatConjDual : G → Matrix (Fin d) (Fin d) ℂ := orientConjDual (repMatrix ρ)

theorem repMatrix_isOrientationMat
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    IsOrientationMat (repMatrix ρ) (repMatrix ρ) :=
  isOrientationMat_self (repMatrix ρ) (fun g h => repMatrix_mul ρ g h)
    (repMatrix_one ρ) (fun g => repMatrix_inv ρ g)
    (fun a c => hρcont.matrix_elem a c)

theorem repMatConj_isOrientationMat
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    IsOrientationMat (repMatrix ρ) (repMatConj ρ) :=
  isOrientationMat_conj (repMatrix ρ) (fun g h => repMatrix_mul ρ g h)
    (repMatrix_one ρ) (fun g => repMatrix_inv ρ g)
    (fun a c => hρcont.matrix_elem a c)

theorem repMatDual_isOrientationMat
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    IsOrientationMat (repMatrix ρ) (repMatDual ρ) :=
  isOrientationMat_dual (repMatrix ρ) (fun g h => repMatrix_mul ρ g h)
    (repMatrix_one ρ) (fun g => repMatrix_inv ρ g)
    (fun a c => hρcont.matrix_elem a c)

theorem repMatConjDual_isOrientationMat
    (hρcont : Continuous fun g : G => repMatrix ρ g) :
    IsOrientationMat (repMatrix ρ) (repMatConjDual ρ) :=
  isOrientationMat_conjDual (repMatrix ρ) (fun g h => repMatrix_mul ρ g h)
    (repMatrix_one ρ) (fun g => repMatrix_inv ρ g)
    (fun a c => hρcont.matrix_elem a c)

/-- **Instantiation headline.** For any two orientations `N₁, N₂` of
the corpus representation `ρ`, the Haar twirl `𝒥(N₁, N₂)` is the
projection onto the pair-invariant submodule: `IsProj`, self-adjoint,
idempotent — at the charter's generality (arbitrary compact `G`,
arbitrary unitary `ρ`, reducible case included). -/
theorem repMatrix_twirl_package
    (N₁ N₂ : G → Matrix (Fin d) (Fin d) ℂ)
    (hN₁ : IsOrientationMat (repMatrix ρ) N₁)
    (hN₂ : IsOrientationMat (repMatrix ρ) N₂) :
    LinearMap.IsProj (pairInvariantSubmodule N₁ N₂)
        (Matrix.mulVecLin (haarTwirl μG N₁ N₂))
      ∧ star (haarTwirl μG N₁ N₂) = haarTwirl μG N₁ N₂
      ∧ haarTwirl μG N₁ N₂ * haarTwirl μG N₁ N₂ = haarTwirl μG N₁ N₂ := by
  obtain ⟨h₁mul, h₁one, h₁inv, h₁cont⟩ := hN₁
  obtain ⟨h₂mul, h₂one, h₂inv, h₂cont⟩ := hN₂
  exact ⟨haarTwirl_isProj μG N₁ N₂ h₁mul h₁one h₁inv h₁cont
      h₂mul h₂one h₂inv h₂cont,
    haarTwirl_star μG N₁ N₂ h₁mul h₁one h₁inv h₁cont h₂mul h₂one h₂inv h₂cont,
    haarTwirl_mul_self μG N₁ N₂ h₁mul h₁one h₁inv h₁cont
      h₂mul h₂one h₂inv h₂cont⟩

/-- The conjugation twirl of the corpus representation, in
J-contraction form against its conjugate orientation. -/
theorem repMatrix_twirlEndo_eq_sum
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (X : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    twirlEndo μG (repMatrix ρ) X a b
      = ∑ c, ∑ e, haarTwirl μG (repMatrix ρ) (repMatConj ρ) (a, b) (c, e) * X c e :=
  twirlEndo_eq_sum μG (repMatrix ρ) (fun g h => repMatrix_mul ρ g h)
    (repMatrix_one ρ) (fun g => repMatrix_inv ρ g)
    (fun a c => hρcont.matrix_elem a c) X a b

/-- The fundamental circle representation has vanishing one-factor
twirl: its fixed submodule is `⊥` (landed as `circleRep_no_fixed`),
and the twirl is the projection onto it. -/
theorem circleRep_haarTwirl1_eq_zero (μC : Measure Circle) [IsProbabilityMeasure μC]
    [Measure.IsMulLeftInvariant μC] [Measure.IsMulRightInvariant μC]
    [Measure.IsInvInvariant μC] :
    haarTwirl1 μC (repMatrix circleRep) = 0 := by
  ext a c
  have hmem : haarTwirl1 μC (repMatrix circleRep) *ᵥ Pi.single c 1
      ∈ fixedSubmodule (repMatrix circleRep) :=
    haarTwirl1_mulVec_mem μC (repMatrix circleRep)
      (fun g h => repMatrix_mul circleRep g h) (repMatrix_one circleRep)
      (fun g => repMatrix_inv circleRep g)
      (fun a c => circleRep_continuous.matrix_elem a c) (Pi.single c 1)
  have h0 : haarTwirl1 μC (repMatrix circleRep) *ᵥ Pi.single c 1 = 0 :=
    circleRep_no_fixed _ ((mem_fixedSubmodule _ _).1 hmem)
  have h1 := congrFun h0 a
  rwa [Matrix.mulVec_single_one] at h1

end Corpus

/-! ## §8. C3 guards at the interface level

Covariance against a constant observable vanishes — the algebraic
content, at the landed `covZero` interface, of the C3 normalization
guard (for the trivial representation the plaquette loop is the
constant `1` and the action density vanishes). The full C3 check
against the contraction formula is Q13-4's acceptance work. -/

section Guards

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (σ : Fin 4 → Equiv.Perm Λ)
variable (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
variable {d : ℕ} (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))

/-- Covariance against a constant observable vanishes (right form). -/
theorem covZero_const_right (F : Config Λ G → ℂ) (c : ℂ) :
    covZero σ μG ρ F (fun _ => c) = 0 := by
  rw [covZero, gibbsExpect_zero, gibbsExpect_zero, gibbsExpect_zero]
  simp [integral_const_mul, integral_mul_const, integral_const]

/-- Covariance against a constant observable vanishes (left form). -/
theorem covZero_const_left (c : ℂ) (H : Config Λ G → ℂ) :
    covZero σ μG ρ (fun _ => c) H = 0 := by
  rw [covZero, gibbsExpect_zero, gibbsExpect_zero, gibbsExpect_zero]
  simp [integral_const_mul, integral_mul_const, integral_const]

end Guards

end ThetLogos
