import Mathlib.Tactic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Matrix.PosDef
import ThetLogos.BridgeMagneticHeat
import ThetLogos.BridgeCompletion

open scoped InnerProductSpace
open scoped ComplexOrder
open Matrix

/-!
# BridgeMagneticWeld — STEM bridge brick B5: the zero-field weld

*STEM = Spectral–Thermal ElectroMagnetic (Jeff's name, 2026-10-24).*

Brick B5 of the STEM bridge charter
(`whitepaper/stem-bridge-scoping-2026-10-24.md`, statement S5): the
magnetic theory of B1–B3 contains the Bridge exhibit's theory as its
zero-field special case, end to end, at the trivial connection
`θ ≡ 1`. The weld is proved at the four levels the objects live at:

- **Operator.** B1's definitional weld `magLap_one`
  (`magLap w 1 = laplacianOpC w`) is cited, not rebuilt; §1 records
  its linear-map and Euclidean-operator forms.
- **Matrix.** `magMat w 1` is identified entrywise (§2): the
  conductance row-sum on the diagonal, the bare cast conductance
  off it — the exhibit's matrix in B3's representation — and, via
  the cast eigenbasis, in spectral form (§3).
- **Heat.** The exhibit's heat operator `BridgeCompletion.heatOp`
  lives on `EuclideanSpace ℝ V` in eigenbasis form; there is no
  ℂ-object to point at. The weld the objects support is proved
  instead (§4): the exhibit's real eigenbasis, read over `ℂ`
  (`castEigVec`), diagonalizes `magHeat w 1 t` with `heatOp`'s own
  factors `exp (-t * lapEig k)` — eigenvector by eigenvector, then
  as a solution formula mirroring `heatOp_solution_formula`, then
  as a matrix identity.
- **Trace.** `magHeatTrace w 1 t` is the cast of the exhibit's heat
  trace datum `∑ k, Real.exp (-t * lapEig k)` (§5), through the
  engine's own trace transport.
- **The gap.** The Fiedler value is the `θ = 1` spectral gap at the
  level the corpus states it (§5): it floors every nonzero welded
  eigenvalue (`fiedler_le_lapEig`, transported), and it is attained
  as an eigenvalue of the welded operator (the exhibit's minimizer,
  transported through the cast).

**NO CLAIM.** Parts of any official (Clay) statement closed: 0.
This is finite graph bookkeeping — the zero-field specialization of
a finite matrix heat semigroup. It is **not** Maxwell theory
(continuum Maxwell has NO SEAT in this corpus), not a
force-unification claim, not a torsion claim, and not a
modular-flux claim (`ModularFlux.magnetophaseFlux_vanishes` stays
a kill at T1). The killed EM-torsion paste and the killed "strong
nuclear = electromagnetic" identification stay killed. Stage 1b-B
is unaffected.

- Status: **VERIFIED — STANDS WHOLE (T1), landed 2026-10-24.**
  The headlines `magMat_one_eq_conj`, `magHeat_one_eq_conj`,
  `magHeatTrace_one` and `magMat_one_fiedler_eigen` are
  machine-checked (parent-verified rebuild, 3,593 jobs; axioms
  standard, no `sorryAx`). NAMED SEAM, kept: the rectangular
  weld matrix `weldMat` carries no `star` (Mathlib has no star
  on rectangular matrices) — its adjoint is `conjTranspose`,
  here and throughout; a representation fact, recorded on the
  face. Dossier:
  `whitepaper/stem-bridge-b5-zero-field-weld-2026-10-24.md`.
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. The cast, and the operator level of the weld

A real potential read over `ℂ`, componentwise. Every eigenvector
transport in this brick goes through this one map: B1's
`laplacianOpC_ofReal` says the complex plain Laplacian of a cast
potential is the cast of the exhibit's `laplacianOp`. -/

/-- A real potential read over `ℂ`. Tier T2 (definition). -/
def castVec (f : V → ℝ) : V → ℂ :=
  fun i => ((f i : ℝ) : ℂ)

theorem castVec_apply (f : V → ℝ) (i : V) :
    castVec f i = ((f i : ℝ) : ℂ) :=
  rfl

/-- The cast of a nonzero potential is nonzero. -/
theorem castVec_ne_zero {f : V → ℝ} (hf : f ≠ 0) :
    castVec f ≠ 0 := by
  intro h
  apply hf
  funext i
  have hi := congrFun h i
  rw [castVec_apply, Pi.zero_apply] at hi
  exact_mod_cast hi

/-- **The eigenvector transport.** If `f` is an eigenvector of the
exhibit's `laplacianOp` with eigenvalue `μ`, its cast is an
eigenvector of the zero-field matrix `magMat w 1` with eigenvalue
`μ` read over `ℂ`. This one lemma carries both the eigenbasis
transport of §3 and the Fiedler attainment of §5. -/
theorem magMat_one_mulVec_castVec (w : V → V → ℝ) (f : V → ℝ)
    (μ : ℝ) (h : ∀ i, laplacianOp w f i = μ * f i) :
    magMat w 1 *ᵥ castVec f = ((μ : ℝ) : ℂ) • castVec f := by
  funext i
  calc (magMat w 1 *ᵥ castVec f) i
      = laplacianOpC w (castVec f) i := by
        rw [magMat_one_mulVec]
    _ = ((laplacianOp w f i : ℝ) : ℂ) :=
        laplacianOpC_ofReal w f i
    _ = ((μ * f i : ℝ) : ℂ) := by rw [h i]
    _ = (((μ : ℝ) : ℂ) • castVec f) i := by
        simp only [Pi.smul_apply, castVec_apply, smul_eq_mul,
          Complex.ofReal_mul]

/-- **Operator weld, linear-map form.** At the trivial connection,
B1's linear map on plain complex potentials is the exhibit's
complex plain Laplacian. (B1's `magLap_one`, restated at the
packaging B1 itself uses.) -/
theorem magLapFun_one_apply (w : V → V → ℝ) (F : V → ℂ) :
    magLapFun w 1 F = laplacianOpC w F :=
  magLap_one w F

/-- **Operator weld, Euclidean form.** At the trivial connection,
B1's operator on `EuclideanSpace ℂ V` transports under
`euclEquivC` to the exhibit's complex plain Laplacian. -/
theorem euclEquivC_magLin_one (w : V → V → ℝ)
    (F : EuclideanSpace ℂ V) :
    euclEquivC (magLin w 1 F) = laplacianOpC w (euclEquivC F) := by
  rw [equiv_magLin, magLap_one]

/-! ## §2. The matrix level of the weld

`magMat w 1` entrywise: at the trivial connection the phase factor
is `1`, so the matrix is the exhibit's Laplacian in B3's
representation — row-sum diagonal, bare conductance off it. -/

/-- **Matrix weld, entrywise.** At `θ ≡ 1`,
`magMat w 1 i j = (row sum of w at i, if j = i) − w i j`, all read
over `ℂ`. -/
theorem magMat_one_apply (w : V → V → ℝ) (i j : V) :
    magMat w 1 i j
      = (if j = i then ∑ k, ((w i k : ℝ) : ℂ) else 0)
        - ((w i j : ℝ) : ℂ) := by
  simp only [magMat_apply, Pi.one_apply, Circle.coe_one, mul_one]

/-- **Matrix weld, closed form.** `magMat w 1` is the exhibit
matrix: diagonal row sums, off-diagonal bare conductances. -/
theorem magMat_one (w : V → V → ℝ) :
    magMat w 1
      = fun i j => (if j = i then ∑ k, ((w i k : ℝ) : ℂ) else 0)
        - ((w i j : ℝ) : ℂ) :=
  Matrix.ext fun i j => magMat_one_apply w i j

/-- **Matrix weld, operator form.** `Matrix.toLin'` of the
zero-field matrix is the exhibit's complex plain Laplacian
(B3's `magMat_one_mulVec`, at the `toLin'` packaging). -/
theorem magMat_one_toLin'_apply (w : V → V → ℝ) (F : V → ℂ) :
    Matrix.toLin' (magMat w 1) F = laplacianOpC w F := by
  rw [Matrix.toLin'_apply]
  exact magMat_one_mulVec w F

/-! ## §3. The cast eigenbasis and the spectral form of the weld

The exhibit's spectral data live at `lapBasis w hsymm` /
`lapEig w hsymm`, indexed by `Fin (finrank ℝ (EuclideanSpace ℝ V))`.
Read over `ℂ`, the eigenbasis vectors stay orthonormal (in the
`dotProduct` pairing B3's contraction uses), stay eigenvectors of
the welded matrix with the same eigenvalues, and assemble into a
rectangular unitary `weldMat` — the change of basis that puts the
zero-field matrix, and then its heat kernel, into `heatOp`'s
diagonal schedule form. -/

/-- Conjugation fixes a real scalar read over `ℂ`. -/
theorem star_ofReal_cast (x : ℝ) : star ((x : ℂ)) = ((x : ℂ)) := by
  rw [RCLike.star_def]
  exact RCLike.conj_ofReal x

/-- **The cast eigenbasis vector**: the exhibit's `k`-th
eigenbasis vector read over `ℂ`. Tier T2 (definition). -/
noncomputable def castEigVec (w : V → V → ℝ)
    (hsymm : (lapLin w).IsSymmetric)
    (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) : V → ℂ :=
  castVec (euclEquiv ((lapBasis w hsymm) k))

theorem castEigVec_apply (w : V → V → ℝ)
    (hsymm : (lapLin w).IsSymmetric)
    (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) (i : V) :
    castEigVec w hsymm k i
      = (((euclEquiv ((lapBasis w hsymm) k)) i : ℝ) : ℂ) :=
  rfl

/-- **Orthonormality over `ℂ`.** The cast eigenbasis is
orthonormal for the sesquilinear `dotProduct` pairing: real
orthonormality, cast. -/
theorem castEigVec_dotProduct (w : V → V → ℝ)
    (hsymm : (lapLin w).IsSymmetric)
    (k l : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) :
    star (castEigVec w hsymm k) ⬝ᵥ castEigVec w hsymm l
      = if k = l then 1 else 0 := by
  have hterm : ∀ i : V, (star (castEigVec w hsymm k)) i
        * castEigVec w hsymm l i
      = (((euclEquiv ((lapBasis w hsymm) k)) i
          * (euclEquiv ((lapBasis w hsymm) l)) i : ℝ) : ℂ) := by
    intro i
    rw [Pi.star_apply, castEigVec_apply, castEigVec_apply,
      star_ofReal_cast, ← Complex.ofReal_mul]
  calc star (castEigVec w hsymm k) ⬝ᵥ castEigVec w hsymm l
      = ∑ i, (((euclEquiv ((lapBasis w hsymm) k)) i
          * (euclEquiv ((lapBasis w hsymm) l)) i : ℝ) : ℂ) := by
        show (∑ i, (star (castEigVec w hsymm k)) i
          * castEigVec w hsymm l i) = _
        exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = ((∑ i, (euclEquiv ((lapBasis w hsymm) k)) i
          * (euclEquiv ((lapBasis w hsymm) l)) i : ℝ) : ℂ) :=
        (RCLike.ofReal_sum Finset.univ _).symm
    _ = ((⟪(lapBasis w hsymm) k, (lapBasis w hsymm) l⟫_ℝ : ℝ)
          : ℂ) := by
        congr 1
        rw [euclid_inner_apply]
        exact Finset.sum_congr rfl (fun i _ => by
          rw [euclEquiv_apply, euclEquiv_apply])
    _ = if k = l then 1 else 0 := by
        rw [orthonormal_iff_ite.mp (lapBasis w hsymm).orthonormal k l]
        split <;> simp

/-- The cast eigenbasis vectors are nonzero. -/
theorem castEigVec_ne_zero (w : V → V → ℝ)
    (hsymm : (lapLin w).IsSymmetric)
    (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) :
    castEigVec w hsymm k ≠ 0 :=
  castVec_ne_zero (by
    intro h
    exact lapBasis_ne_zero w hsymm k
      (euclEquiv.injective (by rw [h, map_zero])))

/-- **The eigen equation of the weld.** Every exhibit eigenvalue
is an eigenvalue of the zero-field matrix, with the cast
eigenbasis vector as eigenvector: the `eigenvalues are lapEig`
clause of S5. -/
theorem magMat_one_mulVec_castEigVec (w : V → V → ℝ)
    (hsymm : (lapLin w).IsSymmetric)
    (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) :
    magMat w 1 *ᵥ castEigVec w hsymm k
      = ((lapEig w hsymm k : ℝ) : ℂ) • castEigVec w hsymm k :=
  magMat_one_mulVec_castVec w _ _ (lapEig_eq_of_basis w hsymm k)

/-- **The weld matrix**: the rectangular unitary whose columns
are the cast eigenbasis vectors. Tier T2 (definition). -/
noncomputable def weldMat (w : V → V → ℝ)
    (hsymm : (lapLin w).IsSymmetric) :
    Matrix V (Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) ℂ :=
  Matrix.of fun i k => castEigVec w hsymm k i

theorem weldMat_apply (w : V → V → ℝ)
    (hsymm : (lapLin w).IsSymmetric) (i : V)
    (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) :
    weldMat w hsymm i k = castEigVec w hsymm k i :=
  rfl

/-- The cast eigenbasis is orthonormal as columns:
`weldMatᴴ * weldMat = 1` over the exhibit's index type. (The
rectangular weld matrix has no `star` — `conjTranspose` is its
adjoint, here and throughout.) -/
theorem weldMat_conjTranspose_mul_self (w : V → V → ℝ)
    (hsymm : (lapLin w).IsSymmetric) :
    (weldMat w hsymm)ᴴ * weldMat w hsymm = 1 := by
  ext k l
  have hsum : ((weldMat w hsymm)ᴴ * weldMat w hsymm) k l
      = star (castEigVec w hsymm k) ⬝ᵥ castEigVec w hsymm l := by
    show (∑ i, ((weldMat w hsymm)ᴴ) k i * weldMat w hsymm i l)
        = (∑ i, (star (castEigVec w hsymm k)) i
            * castEigVec w hsymm l i)
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.conjTranspose_apply, weldMat_apply, weldMat_apply,
      Pi.star_apply]
  rw [hsum, castEigVec_dotProduct, Matrix.one_apply]

/-- The cast eigenbasis is complete: `weldMat * weldMatᴴ = 1`
over `V`. Proved by the real Parseval identity — the exhibit's
eigenbasis reproducing formula, read at one component. -/
theorem weldMat_mul_conjTranspose_self (w : V → V → ℝ)
    (hsymm : (lapLin w).IsSymmetric) :
    weldMat w hsymm * (weldMat w hsymm)ᴴ = 1 := by
  have hpar : ∀ i j : V,
      ∑ k, (euclEquiv ((lapBasis w hsymm) k)) i
          * (euclEquiv ((lapBasis w hsymm) k)) j
        = if i = j then (1 : ℝ) else 0 := by
    intro i j
    set x : EuclideanSpace ℝ V
      := euclEquiv.symm (fun m => if m = j then (1 : ℝ) else 0)
      with hx_def
    have hrepr : ∀ k, (lapBasis w hsymm).repr x k
        = (euclEquiv ((lapBasis w hsymm) k)) j := by
      intro k
      rw [(lapBasis w hsymm).repr_apply_apply, euclid_inner_apply]
      have hcomp : ∀ m : V, x m
          = if m = j then (1 : ℝ) else 0 := by
        intro m
        have h1 : (euclEquiv x) m
            = if m = j then (1 : ℝ) else 0 := by
          rw [hx_def, LinearEquiv.apply_symm_apply]
        rw [← euclEquiv_apply x m]
        exact h1
      calc ∑ m, ((lapBasis w hsymm) k) m * x m
          = ∑ m, ((lapBasis w hsymm) k) m
              * (if m = j then (1 : ℝ) else 0) :=
            Finset.sum_congr rfl (fun m _ => by rw [hcomp m])
        _ = ((lapBasis w hsymm) k) j := by
            rw [Finset.sum_eq_single j]
            · simp
            · intro m _ hm
              rw [if_neg hm, mul_zero]
            · intro h
              exact absurd (Finset.mem_univ j) h
        _ = (euclEquiv ((lapBasis w hsymm) k)) j :=
            (euclEquiv_apply _ _).symm
    have hxcomp : euclEquiv x i
        = if i = j then (1 : ℝ) else 0 := by
      rw [hx_def, LinearEquiv.apply_symm_apply]
    have h2 : euclEquiv x i
        = ∑ k, (lapBasis w hsymm).repr x k
            * (euclEquiv ((lapBasis w hsymm) k)) i := by
      have hsum := (lapBasis w hsymm).sum_repr x
      have hfun : euclEquiv x
          = ∑ k, (lapBasis w hsymm).repr x k
              • euclEquiv ((lapBasis w hsymm) k) := by
        conv_lhs => rw [← hsum]
        rw [map_sum]
        exact Finset.sum_congr rfl (fun k _ => map_smul _ _ _)
      calc euclEquiv x i
          = (∑ k, (lapBasis w hsymm).repr x k
              • euclEquiv ((lapBasis w hsymm) k)) i := by
            rw [hfun]
        _ = ∑ k, (lapBasis w hsymm).repr x k
              * (euclEquiv ((lapBasis w hsymm) k)) i := by
            rw [Finset.sum_apply]
            exact Finset.sum_congr rfl (fun k _ => by
              rw [Pi.smul_apply, smul_eq_mul])
    calc ∑ k, (euclEquiv ((lapBasis w hsymm) k)) i
          * (euclEquiv ((lapBasis w hsymm) k)) j
        = ∑ k, (euclEquiv ((lapBasis w hsymm) k)) j
            * (euclEquiv ((lapBasis w hsymm) k)) i :=
          Finset.sum_congr rfl (fun k _ => mul_comm _ _)
      _ = if i = j then (1 : ℝ) else 0 := by
          rw [← hxcomp, h2]
          exact Finset.sum_congr rfl (fun k _ => by rw [hrepr k])
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ k, weldMat w hsymm i k * (weldMat w hsymm)ᴴ k j
      = (((euclEquiv ((lapBasis w hsymm) k)) i
          * (euclEquiv ((lapBasis w hsymm) k)) j : ℝ) : ℂ) := by
    intro k
    show weldMat w hsymm i k * star (weldMat w hsymm j k) = _
    rw [weldMat_apply, weldMat_apply, castEigVec_apply,
      castEigVec_apply, star_ofReal_cast, ← Complex.ofReal_mul]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  trans ((∑ k, (euclEquiv ((lapBasis w hsymm) k)) i
      * (euclEquiv ((lapBasis w hsymm) k)) j : ℝ) : ℂ)
  · exact (RCLike.ofReal_sum Finset.univ _).symm
  · rw [hpar]
    split <;> simp

/-- The zero-field matrix conjugates by the weld matrix:
`magMat w 1 * weldMat = weldMat * diagonal (lapEig)`. -/
theorem magMat_one_mul_weldMat (w : V → V → ℝ)
    (hsymm : (lapLin w).IsSymmetric) :
    magMat w 1 * weldMat w hsymm
      = weldMat w hsymm
        * Matrix.diagonal (fun k => ((lapEig w hsymm k : ℝ) : ℂ)) := by
  ext i k
  have h1 : (magMat w 1 * weldMat w hsymm) i k
      = (magMat w 1 *ᵥ castEigVec w hsymm k) i := by
    show (∑ j, magMat w 1 i j * weldMat w hsymm j k)
        = (∑ j, magMat w 1 i j * castEigVec w hsymm k j)
    exact Finset.sum_congr rfl (fun j _ => by rw [weldMat_apply])
  have h2 : (weldMat w hsymm
        * Matrix.diagonal (fun k => ((lapEig w hsymm k : ℝ) : ℂ))) i k
      = ((lapEig w hsymm k : ℝ) : ℂ) * castEigVec w hsymm k i := by
    rw [Matrix.mul_apply, Finset.sum_eq_single k]
    · rw [Matrix.diagonal_apply_eq, weldMat_apply]
      exact mul_comm _ _
    · intro j _ hjk
      rw [Matrix.diagonal_apply, if_neg hjk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ k) h
  rw [h1, magMat_one_mulVec_castEigVec, h2, Pi.smul_apply,
    smul_eq_mul]

/-- **Spectral form of the welded matrix.** At `θ ≡ 1`,
`magMat w 1 = weldMat * diagonal (lapEig) * weldMatᴴ` —
the exhibit's spectral decomposition, read over `ℂ`.
Hypothesis-free: pure algebra off the eigen equation and the
two unitary identities. -/
theorem magMat_one_eq_conj (w : V → V → ℝ)
    (hsymm : (lapLin w).IsSymmetric) :
    magMat w 1
      = weldMat w hsymm
        * Matrix.diagonal (fun k => ((lapEig w hsymm k : ℝ) : ℂ))
        * (weldMat w hsymm)ᴴ := by
  calc magMat w 1
      = magMat w 1 * (weldMat w hsymm * (weldMat w hsymm)ᴴ) := by
        rw [weldMat_mul_conjTranspose_self, Matrix.mul_one]
    _ = (magMat w 1 * weldMat w hsymm) * (weldMat w hsymm)ᴴ :=
        (Matrix.mul_assoc _ _ _).symm
    _ = weldMat w hsymm
          * Matrix.diagonal (fun k => ((lapEig w hsymm k : ℝ) : ℂ))
          * (weldMat w hsymm)ᴴ := by
        rw [magMat_one_mul_weldMat]

/-! ## §4. The heat level of the weld

`heatOp` multiplies the `k`-th eigenbasis coefficient by
`Real.exp (-t * lapEig k)`. Read over `ℂ`, the same is true of
`magHeat w 1 t` on the cast eigenbasis — proved, perforce, on
`magMat`'s own (square, `V`-indexed) spectral form: the
rectangular weld matrix cannot feed the engine's conjugation
law, so the eigenvector is pushed through `heatKernelGen_eq_conj`
by the support argument (a vector in the `λ`-eigenspace of a
Hermitian matrix is heated by the scalar `exp (-tλ)`). -/

/-- **The heat action on the cast eigenbasis.** The cast
eigenbasis vector is heated by exactly `heatOp`'s factor:
`magHeat w 1 t *ᵥ castEigVec k = ↑(exp (-t * lapEig k)) •
castEigVec k`. -/
theorem magHeat_one_mulVec_castEigVec (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hsymm : (lapLin w).IsSymmetric)
    (t : ℝ) (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))) :
    magHeat w 1 t *ᵥ castEigVec w hsymm k
      = ((Real.exp (-t * lapEig w hsymm k) : ℝ) : ℂ)
        • castEigVec w hsymm k := by
  have hθ1 : ∀ i j, (1 : V → V → Circle) j i
      = ((1 : V → V → Circle) i j)⁻¹ := by
    intro i j
    simp
  have hA : (magMat w 1).IsHermitian :=
    magMat_isHermitian w hw 1 hθ1
  have heig : magMat w 1 *ᵥ castEigVec w hsymm k
      = ((lapEig w hsymm k : ℝ) : ℂ) • castEigVec w hsymm k :=
    magMat_one_mulVec_castEigVec w hsymm k
  have hspec : magMat w 1
      = (hA.eigenvectorUnitary : Matrix V V ℂ)
        * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℂ)))
        * star (hA.eigenvectorUnitary : Matrix V V ℂ) :=
    hermitian_spectral_form hA
  have hUU : (hA.eigenvectorUnitary : Matrix V V ℂ)
        * star (hA.eigenvectorUnitary : Matrix V V ℂ) = 1 :=
    Unitary.coe_mul_star_self _
  have hUw : (hA.eigenvectorUnitary : Matrix V V ℂ)
        *ᵥ (star (hA.eigenvectorUnitary : Matrix V V ℂ)
          *ᵥ castEigVec w hsymm k)
      = castEigVec w hsymm k := by
    rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
  have hDw : Matrix.diagonal (fun i => ((hA.eigenvalues i : ℂ)))
        *ᵥ (star (hA.eigenvectorUnitary : Matrix V V ℂ)
          *ᵥ castEigVec w hsymm k)
      = ((lapEig w hsymm k : ℝ) : ℂ)
        • (star (hA.eigenvectorUnitary : Matrix V V ℂ)
          *ᵥ castEigVec w hsymm k) := by
    have h2 : star (hA.eigenvectorUnitary : Matrix V V ℂ)
          * (magMat w 1)
        = Matrix.diagonal (fun i => ((hA.eigenvalues i : ℂ)))
          * star (hA.eigenvectorUnitary : Matrix V V ℂ) := by
      calc star (hA.eigenvectorUnitary : Matrix V V ℂ)
            * (magMat w 1)
          = star (hA.eigenvectorUnitary : Matrix V V ℂ)
              * ((hA.eigenvectorUnitary : Matrix V V ℂ)
                * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℂ)))
                * star (hA.eigenvectorUnitary : Matrix V V ℂ)) :=
            congrArg _ hspec
        _ = (star (hA.eigenvectorUnitary : Matrix V V ℂ)
              * (hA.eigenvectorUnitary : Matrix V V ℂ))
              * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℂ)))
              * star (hA.eigenvectorUnitary : Matrix V V ℂ) := by
            simp only [Matrix.mul_assoc]
        _ = Matrix.diagonal (fun i => ((hA.eigenvalues i : ℂ)))
              * star (hA.eigenvectorUnitary : Matrix V V ℂ) := by
            rw [Unitary.coe_star_mul_self, Matrix.one_mul]
    have h1 : star (hA.eigenvectorUnitary : Matrix V V ℂ)
          *ᵥ (magMat w 1 *ᵥ castEigVec w hsymm k)
        = star (hA.eigenvectorUnitary : Matrix V V ℂ)
          *ᵥ (((lapEig w hsymm k : ℝ) : ℂ)
            • castEigVec w hsymm k) := by
      rw [heig]
    rw [Matrix.mulVec_mulVec, h2, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_smul] at h1
    exact h1
  have hsupp : ∀ i, (star (hA.eigenvectorUnitary : Matrix V V ℂ)
        *ᵥ castEigVec w hsymm k) i ≠ 0
      → ((hA.eigenvalues i : ℂ)) = ((lapEig w hsymm k : ℝ) : ℂ) := by
    intro i hi
    have hcomp := congrFun hDw i
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
      at hcomp
    exact (mul_eq_mul_right_iff.mp hcomp).resolve_right hi
  have hHD : hermitianDiagKernel hA.eigenvalues t
        *ᵥ (star (hA.eigenvectorUnitary : Matrix V V ℂ)
          *ᵥ castEigVec w hsymm k)
      = ((Real.exp (-t * lapEig w hsymm k) : ℝ) : ℂ)
        • (star (hA.eigenvectorUnitary : Matrix V V ℂ)
          *ᵥ castEigVec w hsymm k) := by
    funext i
    by_cases hi : (star (hA.eigenvectorUnitary : Matrix V V ℂ)
        *ᵥ castEigVec w hsymm k) i = 0
    · rw [show hermitianDiagKernel hA.eigenvalues t
          = Matrix.diagonal (fun i =>
              ((Real.exp (-t * hA.eigenvalues i) : ℝ) : ℂ)) from rfl,
        Matrix.mulVec_diagonal, hi, mul_zero, Pi.smul_apply,
        smul_eq_mul, hi, mul_zero]
    · have hμ : hA.eigenvalues i = lapEig w hsymm k :=
        Complex.ofReal_inj.mp (hsupp i hi)
      rw [show hermitianDiagKernel hA.eigenvalues t
          = Matrix.diagonal (fun i =>
              ((Real.exp (-t * hA.eigenvalues i) : ℝ) : ℂ)) from rfl,
        Matrix.mulVec_diagonal, hμ, Pi.smul_apply, smul_eq_mul]
  have hheat : magHeat w 1 t *ᵥ castEigVec w hsymm k
      = (hA.eigenvectorUnitary : Matrix V V ℂ)
        *ᵥ (hermitianDiagKernel hA.eigenvalues t
          *ᵥ (star (hA.eigenvectorUnitary : Matrix V V ℂ)
            *ᵥ castEigVec w hsymm k)) := by
    rw [magHeat_one, heatKernelGen_eq_conj hA t,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hheat, hHD, Matrix.mulVec_smul, hUw]

/-- **Completeness of the cast eigenbasis.** Every complex
potential expands in the cast eigenbasis with `dotProduct`
coefficients — the `ℂ` form of `heatOp`'s `repr` expansion. -/
theorem castEigVec_expansion (w : V → V → ℝ)
    (hsymm : (lapLin w).IsSymmetric) (F : V → ℂ) :
    F = ∑ k, (star (castEigVec w hsymm k) ⬝ᵥ F)
      • castEigVec w hsymm k := by
  have h1 : ∀ l, star (castEigVec w hsymm l) ⬝ᵥ
      (F - ∑ k, (star (castEigVec w hsymm k) ⬝ᵥ F)
        • castEigVec w hsymm k) = 0 := by
    intro l
    rw [dotProduct_sub, dotProduct_sum,
      Finset.sum_eq_single l]
    · rw [dotProduct_smul, castEigVec_dotProduct]
      simp
    · intro b _ hbl
      rw [dotProduct_smul, castEigVec_dotProduct,
        if_neg (Ne.symm hbl), smul_zero]
    · intro h
      exact absurd (Finset.mem_univ l) h
  have h2 : ∀ G : V → ℂ,
      (∀ l, star (castEigVec w hsymm l) ⬝ᵥ G = 0) → G = 0 := by
    intro G hG
    have hstar : (weldMat w hsymm)ᴴ *ᵥ G = 0 := by
      funext l
      have hcomp : ((weldMat w hsymm)ᴴ *ᵥ G) l
          = star (castEigVec w hsymm l) ⬝ᵥ G := by
        show (∑ i, ((weldMat w hsymm)ᴴ) l i * G i)
            = (∑ i, (star (castEigVec w hsymm l)) i * G i)
        apply Finset.sum_congr rfl
        intro i _
        show star (weldMat w hsymm i l) * G i = _
        rw [weldMat_apply, Pi.star_apply]
      rw [hcomp, hG l, Pi.zero_apply]
    have hW : weldMat w hsymm *ᵥ ((weldMat w hsymm)ᴴ *ᵥ G) = 0 := by
      rw [hstar, Matrix.mulVec_zero]
    rw [Matrix.mulVec_mulVec, weldMat_mul_conjTranspose_self,
      Matrix.one_mulVec] at hW
    exact hW
  exact sub_eq_zero.mp (h2 _ h1)

/-- **The solution formula of the weld.** `magHeat w 1 t` acts
on a general potential exactly as `heatOp` read over `ℂ`:
expand in the cast eigenbasis, multiply the `k`-th coefficient
by `exp (-t * lapEig k)`, resum. This is
`BridgeCompletion.heatOp_solution_formula` with `ℂ` coefficients
and `dotProduct` repr coefficients. -/
theorem magHeat_one_solution (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hsymm : (lapLin w).IsSymmetric)
    (t : ℝ) (F : V → ℂ) :
    magHeat w 1 t *ᵥ F
      = ∑ k, (((Real.exp (-t * lapEig w hsymm k) : ℝ) : ℂ)
          * (star (castEigVec w hsymm k) ⬝ᵥ F))
        • castEigVec w hsymm k := by
  calc magHeat w 1 t *ᵥ F
      = magHeat w 1 t *ᵥ (∑ k, (star (castEigVec w hsymm k) ⬝ᵥ F)
          • castEigVec w hsymm k) := by
        rw [← castEigVec_expansion w hsymm F]
    _ = ∑ k, (star (castEigVec w hsymm k) ⬝ᵥ F)
          • (magHeat w 1 t *ᵥ castEigVec w hsymm k) := by
        rw [Matrix.mulVec_sum]
        exact Finset.sum_congr rfl (fun k _ => by
          rw [Matrix.mulVec_smul])
    _ = ∑ k, (((Real.exp (-t * lapEig w hsymm k) : ℝ) : ℂ)
          * (star (castEigVec w hsymm k) ⬝ᵥ F))
          • castEigVec w hsymm k :=
        Finset.sum_congr rfl (fun k _ => by
          rw [magHeat_one_mulVec_castEigVec w hw hsymm t k,
            smul_comm, smul_smul])

/-- Two matrices with the same `mulVec` action are equal. -/
theorem matrix_eq_of_mulVec_eq {A B : Matrix V V ℂ}
    (h : ∀ F : V → ℂ, A *ᵥ F = B *ᵥ F) : A = B := by
  ext i j
  have hsingle : ∀ M : Matrix V V ℂ,
      (M *ᵥ (fun l => if l = j then (1 : ℂ) else 0)) i = M i j := by
    intro M
    show (∑ l, M i l * (if l = j then (1 : ℂ) else 0)) = M i j
    rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hlj
      rw [if_neg hlj, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have h2 := congrFun (h (fun l => if l = j then (1 : ℂ) else 0)) i
  rw [hsingle, hsingle] at h2
  exact h2

/-- **The heat weld, matrix form.** `magHeat w 1 t` is the weld
matrix conjugating `heatOp`'s diagonal schedule kernel:
`magHeat w 1 t = weldMat * hermitianDiagKernel (lapEig) t *
weldMatᴴ` — the engine's `heatKernelGen_eq_conj` form, with the
exhibit's own eigenvalues and eigenbasis in place of the
matrix's abstract spectral data. -/
theorem magHeat_one_eq_conj (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hsymm : (lapLin w).IsSymmetric)
    (t : ℝ) :
    magHeat w 1 t
      = weldMat w hsymm * hermitianDiagKernel (lapEig w hsymm) t
        * (weldMat w hsymm)ᴴ := by
  apply matrix_eq_of_mulVec_eq
  intro F
  have hz : ∀ k, ((weldMat w hsymm)ᴴ *ᵥ F) k
      = star (castEigVec w hsymm k) ⬝ᵥ F := by
    intro k
    show (∑ i, ((weldMat w hsymm)ᴴ) k i * F i)
        = (∑ i, (star (castEigVec w hsymm k)) i * F i)
    apply Finset.sum_congr rfl
    intro i _
    show star (weldMat w hsymm i k) * F i = _
    rw [weldMat_apply, Pi.star_apply]
  have hHD : ∀ (y : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))
        → ℂ) (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))),
      (hermitianDiagKernel (lapEig w hsymm) t *ᵥ y) k
        = ((Real.exp (-t * lapEig w hsymm k) : ℝ) : ℂ) * y k := by
    intro y k
    show (Matrix.diagonal (fun k =>
        ((Real.exp (-t * lapEig w hsymm k) : ℝ) : ℂ)) *ᵥ y) k = _
    exact Matrix.mulVec_diagonal _ y k
  have hW : ∀ (y : Fin (Module.finrank ℝ (EuclideanSpace ℝ V))
        → ℂ) (i : V),
      (weldMat w hsymm *ᵥ y) i
        = ∑ k, castEigVec w hsymm k i * y k := by
    intro y i
    show (∑ k, weldMat w hsymm i k * y k) = _
    exact Finset.sum_congr rfl (fun k _ => by rw [weldMat_apply])
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    magHeat_one_solution w hw hsymm t F]
  funext i
  rw [hW, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [hHD, hz, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## §5. The trace level, and the Fiedler gap

The trace weld is the engine's own trace transport with the
rectangular weld matrix cycled through `Matrix.trace_mul_comm`
(the engine's `trace_conj_diagKernel` is stated for square
unitaries; the cycle here is the same computation). The Fiedler
clauses restate the exhibit's gap facts — floor and attainment —
at the welded operator. -/

/-- **The trace weld.** At `θ ≡ 1` the magnetic heat trace is
the cast of the exhibit's heat trace datum at the exhibit's
eigenvalues: `magHeatTrace w 1 t = ↑(∑ k, exp (-t * lapEig k))`. -/
theorem magHeatTrace_one (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hsymm : (lapLin w).IsSymmetric)
    (t : ℝ) :
    magHeatTrace w 1 t
      = ((∑ k, Real.exp (-t * lapEig w hsymm k) : ℝ) : ℂ) := by
  have h1 : magHeatTrace w 1 t
      = Matrix.trace (weldMat w hsymm
          * hermitianDiagKernel (lapEig w hsymm) t
          * (weldMat w hsymm)ᴴ) := by
    show Matrix.trace (magHeat w 1 t) = _
    rw [magHeat_one_eq_conj w hw hsymm t]
  rw [h1, Matrix.mul_assoc,
    Matrix.trace_mul_comm (weldMat w hsymm)
      (hermitianDiagKernel (lapEig w hsymm) t * (weldMat w hsymm)ᴴ),
    Matrix.mul_assoc, weldMat_conjTranspose_mul_self,
    Matrix.mul_one,
    show hermitianDiagKernel (lapEig w hsymm) t
      = Matrix.diagonal (fun k =>
          ((Real.exp (-t * lapEig w hsymm k) : ℝ) : ℂ)) from rfl,
    Matrix.trace_diagonal]
  exact (RCLike.ofReal_sum Finset.univ _).symm

/-- **The Fiedler floor at the weld.** Every nonzero welded
eigenvalue is at least the Fiedler value — the exhibit's
`fiedler_le_lapEig`, with the eigenvalue's welded eigenvector
attached. -/
theorem magMat_one_fiedler_floor (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hsymm : (lapLin w).IsSymmetric)
    (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ V)))
    (hk : lapEig w hsymm k ≠ 0) :
    fiedler w ≤ lapEig w hsymm k
      ∧ magMat w 1 *ᵥ castEigVec w hsymm k
          = ((lapEig w hsymm k : ℝ) : ℂ) • castEigVec w hsymm k
      ∧ castEigVec w hsymm k ≠ 0 :=
  ⟨fiedler_le_lapEig w hw hw0 hsymm k hk,
    magMat_one_mulVec_castEigVec w hsymm k,
    castEigVec_ne_zero w hsymm k⟩

/-- **The Fiedler value is attained at the weld.** For two
distinct vertices, `fiedler w` is an eigenvalue of the zero-field
matrix `magMat w 1`, with a nonzero eigenvector — the exhibit's
attained minimizer (`laplacianOp_fiedler_minimizer`), transported
through the cast. Together with the floor: the Fiedler value is
the `θ = 1` spectral gap. -/
theorem magMat_one_fiedler_eigen (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    {a b : V} (hab : a ≠ b) :
    ∃ F : V → ℂ, F ≠ 0
      ∧ magMat w 1 *ᵥ F = ((fiedler w : ℝ) : ℂ) • F := by
  obtain ⟨F, hFmem, hFeig⟩ :=
    laplacianOp_fiedler_minimizer w hw hw0 hab
  have hF0 : F ≠ 0 := by
    intro hF
    have h2 : ∑ i, F i ^ 2 = 1 := hFmem.2
    rw [hF] at h2
    simp at h2
  exact ⟨castVec F, castVec_ne_zero hF0,
    magMat_one_mulVec_castVec w F (fiedler w) hFeig⟩

end ThetLogos
