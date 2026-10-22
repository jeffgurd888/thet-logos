import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Spectrum
import ThetLogos.ModularTime
import ThetLogos.ModularFlux
import ThetLogos.HermitianReduction

open Matrix

namespace ThetLogos.FluxClassification

/-!
# ThetLogos.FluxClassification — the modular-flux classification

STATUS: STANDS WHOLE (T1) — landed 2026-10-22. Built in scratch under
Jeff's order ("build them both": the circularity ledger and this
brick), roadmap item A / first stress test D of
`your_files/roadmap-answers-2026-10-22.md`; parent-verified
(byte-identical recompile, comment-stripped scan, `#print axioms` on
all headlines) and landed the same day. Dossier:
`whitepaper/flux-classification-2026-10-22.md`.

## What this brick proves

The classification the roadmap asked for, on the corpus's own objects
(`modularFlux K D = Complex.I • (K * D - D * K)`, `ModularTime.lean`):

1. **Diagonal K, entry form** (`classification_diagonal`): for any
   diagonal `K = Matrix.diagonal k` and ANY matrix `D` (no
   Hermiticity, no positivity, nothing),
   `modularFlux (diagonal k) D = 0 ↔ sectorBlockDiagonal k D`,
   where the right side says `D i j = 0` whenever `k i ≠ k j`:
   the flux vanishes iff `D` has no entries between distinct
   K-eigenspaces. The engine is the entry computation
   `modularFlux_diagonal_apply`:
   `(modularFlux (diagonal k) D) i j = I * (k i - k j) * D i j`.

2. **The corpus's built K** (`classification_diagModularK`): at
   `K = diagModularK w` — the corpus's actual `K = -ln ρ` for
   `ρ = diagState w` (`ModularTime.lean`) — the sectors are the
   level sets of `j ↦ Real.log (w j)`, i.e. the eigenspaces of the
   built K itself:
   `modularFlux (diagModularK w) D = 0 ↔
     ∀ i j, Real.log (w i) ≠ Real.log (w j) → D i j = 0`.
   No positivity on `w` is needed: the classification is a statement
   about K's eigenvalues `-log (w j)` as built. For positive weights
   (`classification_diagModularK_of_pos`) log is injective and the
   sectors are exactly the weight level sets `w i = w j`.

3. **Eigenspace preservation** (`classification_diagonal_preserves`):
   the same iff with the right side stated as preservation: `D`
   maps every sector-supported vector to a sector-supported
   vector, sector by sector. And for a general `K`
   (`flux_eq_zero_preserves_eigenspace`), vanishing flux implies
   `D` carries every K-eigenvector to a K-eigenvector of the same
   eigenvalue — the basis-free preservation direction.

4. **General Hermitian K** (`classification_hermitian`): for
   `K` Hermitian and any `D`, with `U = hK.eigenvectorUnitary` and
   `d = hK.eigenvalues` (Mathlib's spectral theorem, in the plain
   product form of `HermitianReduction.hermitian_spectral_form`),
   `modularFlux K D = 0 ↔
     sectorBlockDiagonal (fun i => ((d i : ℂ))) (star U * D * U)`:
   in K's eigenbasis, `D` is block-diagonal with respect to K's
   distinct-eigenvalue sectors. Spelled out entrywise in
   `classification_hermitian_apply`.

## Honest fences

- Finite level only: matrices over `Fin N → ℂ`. No continuum
  statement, no functional calculus beyond the spectral theorem
  already in the corpus.
- `D` needs NO hypothesis anywhere in this brick — not even
  Hermiticity. The commissioned target said "general Hermitian D
  with K diagonal"; the proof needs less, and the statements are
  recorded at the strength actually proved (a strengthening, not a
  narrowing — the Hermitian-D case is the special case where the
  flux is additionally self-adjoint, `modularFlux_selfAdjoint`).
- For non-positive weights the sectors are log-level sets, NOT
  weight level sets: `Real.log` identifies `w` and `-w` (and sends
  `0` to `0`). That is the construction as built (`diagModularK`
  is defined for every real `w`), and the headline states it in
  the log form so the fence is on the theorem's face.
- The general-Hermitian form is an EIGENBASIS statement (entries of
  `star U * D * U`), per HermitianReduction's remainder R1:
  original-basis entry statements do not transport and none is
  claimed.
- Kill-criterion disposition: the iff in the corpus's actual K
  construction required NO hypotheses beyond finite + Hermitian
  (the latter only for the general-K form, where it is the
  construction's own standing hypothesis). The pre-registered
  PARTIAL trigger did not fire.
-/

-- ============================================================================
-- §0. Sector block-diagonality and the entry computation
-- ============================================================================

section Diagonal

variable {N : ℕ}

/-- **Sector block-diagonality** (Tier T2 — definition): `D` is
block-diagonal with respect to the sectors of a diagonal weight
function `k` if it has no entries between distinct sectors:
`D i j = 0` whenever `k i ≠ k j`. For `k` the diagonal of a
diagonal `K`, the sectors are K's eigenspaces. -/
def sectorBlockDiagonal (k : Fin N → ℂ) (D : Matrix (Fin N) (Fin N) ℂ) :
    Prop :=
  ∀ i j, k i ≠ k j → D i j = 0

/-- **The entry computation** (Tier T1 target): the `(i, j)` entry
of the modular flux of a diagonal `K = diagonal k` is
`I * (k i - k j) * D i j`. This one line is the whole
classification: the flux entry at a cross-sector position is the
sector gap times the `D` entry there. -/
theorem modularFlux_diagonal_apply (k : Fin N → ℂ)
    (D : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    (modularFlux (Matrix.diagonal k) D) i j
      = Complex.I * (k i - k j) * D i j := by
  simp only [modularFlux, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

/-- **Flux vanishing is commutation** (Tier T1 target): for any
`K, D` whatsoever, `modularFlux K D = 0 ↔ K * D - D * K = 0`,
since the scalar `Complex.I` is nonzero. The sub form of
`modularFlux_eq_zero_iff_commute` below. -/
theorem modularFlux_eq_zero_iff_sub (K D : Matrix (Fin N) (Fin N) ℂ) :
    modularFlux K D = 0 ↔ K * D - D * K = 0 := by
  unfold modularFlux
  rw [smul_eq_zero, or_iff_right Complex.I_ne_zero]

/-- **Flux vanishing is commutation, equality form** (Tier T1
target): `modularFlux K D = 0 ↔ K * D = D * K`. -/
theorem modularFlux_eq_zero_iff_commute (K D : Matrix (Fin N) (Fin N) ℂ) :
    modularFlux K D = 0 ↔ K * D = D * K := by
  rw [modularFlux_eq_zero_iff_sub, sub_eq_zero]

-- ============================================================================
-- §1. The classification at a diagonal K
-- ============================================================================

/-- **THE CLASSIFICATION, diagonal form** (Tier T1 target): for
`K = Matrix.diagonal k` and ANY `D`,
`modularFlux (diagonal k) D = 0 ↔ sectorBlockDiagonal k D`:
the flux vanishes iff `D` preserves every K-eigenspace, i.e. has
no entries between distinct eigenvalue sectors of `K`. No
hypotheses on `D`, none on `k`. -/
theorem classification_diagonal (k : Fin N → ℂ)
    (D : Matrix (Fin N) (Fin N) ℂ) :
    modularFlux (Matrix.diagonal k) D = 0 ↔ sectorBlockDiagonal k D := by
  constructor
  · intro h i j hij
    have hentry := congrFun (congrFun h i) j
    rw [modularFlux_diagonal_apply] at hentry
    simp only [Matrix.zero_apply] at hentry
    have hsub : k i - k j ≠ 0 := sub_ne_zero.mpr hij
    rcases mul_eq_zero.mp hentry with h1 | h1
    · rcases mul_eq_zero.mp h1 with hI | hsub0
      · exact absurd hI Complex.I_ne_zero
      · exact absurd hsub0 hsub
    · exact h1
  · intro h
    ext i j
    simp only [Matrix.zero_apply, modularFlux_diagonal_apply]
    by_cases hkk : k i = k j
    · rw [hkk, sub_self, mul_zero, zero_mul]
    · rw [h i j hkk, mul_zero]

/-- **The classification as eigenspace preservation** (Tier T1
target): the flux at a diagonal `K` vanishes iff `D` preserves
every sector subspace: any vector supported on the `c`-sector is
mapped to a vector supported on the `c`-sector, for every sector
value `c`. This is `classification_diagonal` with the right side
in its "D preserves every K-eigenspace" wording. -/
theorem classification_diagonal_preserves (k : Fin N → ℂ)
    (D : Matrix (Fin N) (Fin N) ℂ) :
    modularFlux (Matrix.diagonal k) D = 0 ↔
      ∀ (c : ℂ) (x : Fin N → ℂ), (∀ j, k j ≠ c → x j = 0) →
        ∀ i, k i ≠ c → (D *ᵥ x) i = 0 := by
  rw [classification_diagonal]
  constructor
  · intro hblock c x hx i hi
    have hsum : (D *ᵥ x) i = ∑ j, D i j * x j := by
      rw [Matrix.mulVec]
      rfl
    rw [hsum]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hjc : k j = c
    · rw [hblock i j (fun hkj => hi (hkj.trans hjc)), zero_mul]
    · rw [hx j hjc, mul_zero]
  · intro hpres i j hij
    have hx : ∀ l, k l ≠ k j → (Pi.single j (1 : ℂ) : Fin N → ℂ) l = 0 := by
      intro l hl
      by_cases hlj : l = j
      · subst hlj
        exact (hl rfl).elim
      · exact Pi.single_eq_of_ne (M := fun _ : Fin N => ℂ) hlj (1 : ℂ)
    have key := hpres (k j) (Pi.single j (1 : ℂ) : Fin N → ℂ) hx i hij
    have hsum : (D *ᵥ (Pi.single j (1 : ℂ) : Fin N → ℂ)) i = D i j := by
      have e : (D *ᵥ (Pi.single j (1 : ℂ) : Fin N → ℂ)) i
          = ∑ l, D i l * (Pi.single j (1 : ℂ) : Fin N → ℂ) l := by
        rw [Matrix.mulVec]
        rfl
      rw [e, Finset.sum_eq_single j]
      · rw [Pi.single_eq_same, mul_one]
      · intro l _ hlj
        rw [Pi.single_eq_of_ne hlj, mul_zero]
      · simp
    rw [hsum] at key
    exact key

-- ============================================================================
-- §2. The classification at the corpus's built K = diagModularK
-- ============================================================================

/-- **THE CLASSIFICATION at the corpus's modular Hamiltonian**
(Tier T1 target): for `K = diagModularK w` — the corpus's actual
`K = -ln ρ` built from the diagonal state `ρ = diagState w`
(`ModularTime.lean`) — and ANY `D`,
`modularFlux (diagModularK w) D = 0 ↔
  ∀ i j, Real.log (w i) ≠ Real.log (w j) → D i j = 0`.
The sectors are the level sets of `j ↦ Real.log (w j)`, i.e. the
eigenspaces of the built `K` (eigenvalues `-log (w j)`). NO
positivity on `w` is assumed or needed. -/
theorem classification_diagModularK (w : Fin N → ℝ)
    (D : Matrix (Fin N) (Fin N) ℂ) :
    modularFlux (diagModularK w) D = 0 ↔
      ∀ i j, Real.log (w i) ≠ Real.log (w j) → D i j = 0 := by
  have hkk : ∀ i j, ((-Real.log (w i) : ℝ) : ℂ) ≠ ((-Real.log (w j) : ℝ) : ℂ)
      ↔ Real.log (w i) ≠ Real.log (w j) := by
    intro i j
    constructor
    · intro h hlog
      apply h
      rw [hlog]
    · intro h hcast
      apply h
      have hreal : (-Real.log (w i) : ℝ) = (-Real.log (w j) : ℝ) := by
        exact_mod_cast hcast
      exact neg_inj.mp hreal
  show modularFlux (Matrix.diagonal (fun j => ((-Real.log (w j) : ℝ) : ℂ))) D = 0 ↔ _
  rw [classification_diagonal]
  constructor
  · intro h i j hij
    exact h i j ((hkk i j).mpr hij)
  · intro h i j hij
    exact h i j ((hkk i j).mp hij)

/-- **The classification at positive weights** (Tier T1 target):
for strictly positive weights, `Real.log` is injective, so the
sectors of `diagModularK w` are exactly the weight level sets:
`modularFlux (diagModularK w) D = 0 ↔
  ∀ i j, w i ≠ w j → D i j = 0`. -/
theorem classification_diagModularK_of_pos (w : Fin N → ℝ)
    (hw : ∀ j, 0 < w j) (D : Matrix (Fin N) (Fin N) ℂ) :
    modularFlux (diagModularK w) D = 0 ↔
      ∀ i j, w i ≠ w j → D i j = 0 := by
  rw [classification_diagModularK]
  constructor
  · intro h i j hij
    apply h i j
    intro hlog
    apply hij
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr (hw i))
      (Set.mem_Ioi.mpr (hw j)) hlog
  · intro h i j hij
    apply h i j
    intro hw_eq
    apply hij
    rw [hw_eq]

/-- **One-sector collapse** (Tier T1 target): at constant weights
there is a single sector, so the flux at `diagModularK` vanishes
for every `D` — the flux-side companion of
`maximallyMixed_flow_trivial` and `diagFlow_trivial_of_const`:
no gap spread, no flux. -/
theorem flux_diagModularK_eq_zero_of_const (c : ℝ)
    (D : Matrix (Fin N) (Fin N) ℂ) :
    modularFlux (diagModularK (fun _ => c)) D = 0 := by
  rw [classification_diagModularK]
  intro i j hij
  exact (hij rfl).elim

/-- **Cross-sector entry forces flux** (Tier T1 target): the
classification's contrapositive, as a witness criterion — a
single nonzero entry of `D` across distinct log-weight sectors
makes the flux nonzero. This is the structural form of the
corpus's existence results (`exists_activeDriver`,
`interSectoral_flux_nonzero` in `ModularFlux.lean`): those exhibit
witnesses; this says exactly which entries can serve. -/
theorem flux_diagModularK_ne_zero_of_entry (w : Fin N → ℝ)
    (D : Matrix (Fin N) (Fin N) ℂ) {i j : Fin N}
    (hij : Real.log (w i) ≠ Real.log (w j)) (hDij : D i j ≠ 0) :
    modularFlux (diagModularK w) D ≠ 0 := by
  intro h
  exact hDij ((classification_diagModularK w D).mp h i j hij)

/-- **Flux vanishing gives trivial diagonal flow** (Tier T1
target): at positive weights, if the flux at the built `K`
vanishes then `D` is fixed by the corpus's eigenbasis modular
flow `diagFlow w s` at every time `s`. The bridge between this
brick's condition and `diagFlow_trivial_of_commute`
(`ModularTime.lean`): flux vanishing at `K = -ln ρ` yields the
commutation `[ρ, D] = 0` that theorem consumes — at positive
weights, where log is injective. The positivity is load-bearing
and stays on the statement's face: without it, `diagModularK`
sees only log-level sets, which are coarser than ρ's sectors. -/
theorem diagFlow_eq_of_flux_eq_zero (w : Fin N → ℝ)
    (hw : ∀ j, 0 < w j) (D : Matrix (Fin N) (Fin N) ℂ) (s : ℝ)
    (h : modularFlux (diagModularK w) D = 0) :
    diagFlow w s D = D := by
  apply diagFlow_trivial_of_commute
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hwij : w i = w j
  · rw [hwij]
    exact mul_comm _ _
  · have hDij : D i j = 0 :=
      (classification_diagModularK_of_pos w hw D).mp h i j hwij
    rw [hDij, mul_zero, zero_mul]

end Diagonal

-- ============================================================================
-- §3. The general form: arbitrary K, and general Hermitian K
-- ============================================================================

section General

variable {N : ℕ}

/-- **Vanishing flux preserves eigenspaces, any `K`** (Tier T1
target): if `modularFlux K D = 0` then `D` carries every
eigenvector of `K` to an eigenvector of `K` with the same
eigenvalue — `D` preserves every eigenspace of `K`, stated
basis-free. Pure commutation calculus; no Hermiticity needed.
This is the forward (preservation) direction of the
classification for general `K`; the converse needs the spectral
decomposition and is `classification_hermitian`. -/
theorem flux_eq_zero_preserves_eigenspace {K : Matrix (Fin N) (Fin N) ℂ}
    (D : Matrix (Fin N) (Fin N) ℂ) (h : modularFlux K D = 0)
    {c : ℂ} {x : Fin N → ℂ} (hx : K *ᵥ x = c • x) :
    K *ᵥ (D *ᵥ x) = c • (D *ᵥ x) := by
  have hcomm : K * D = D * K := (modularFlux_eq_zero_iff_commute K D).mp h
  calc K *ᵥ (D *ᵥ x) = (K * D) *ᵥ x := Matrix.mulVec_mulVec x K D
    _ = (D * K) *ᵥ x := by rw [hcomm]
    _ = D *ᵥ (K *ᵥ x) := (Matrix.mulVec_mulVec x D K).symm
    _ = D *ᵥ (c • x) := by rw [hx]
    _ = c • (D *ᵥ x) := Matrix.mulVec_smul D c x

/-- **Star-conjugation of a product** (Tier T1 target): for `U`
with `U * star U = 1`, star-conjugation distributes over products
in the mirrored pattern of `HermitianReduction.conj_mul_conj`:
`(star U * X * U) * (star U * Y * U) = star U * (X * Y) * U`.
Pure associativity plus the unitary identity. -/
theorem starConj_mul (U X Y : Matrix (Fin N) (Fin N) ℂ)
    (hU : U * star U = 1) :
    (star U * X * U) * (star U * Y * U) = star U * (X * Y) * U := by
  have h : (star U * X * U) * (star U * Y * U)
      = star U * (X * (U * star U) * Y) * U := by
    simp only [Matrix.mul_assoc]
  rw [h, hU, Matrix.mul_one]

/-- **Conjugating a spectral form back to its diagonal** (Tier
T1 target): if `Km = U * Λ * star U` and `star U * U = 1`, then
`star U * Km * U = Λ`. Stated with plain matrix variables so the
rewrite of `Km` never has to abstract under a term depending on
a Hermitian-ness proof (the motive obstruction that the direct
rewrite inside `classification_hermitian` hits). This is
`HermitianReduction.star_conj_collapse` fed the spectral form. -/
theorem star_mul_spectral_mul (U Km : Matrix (Fin N) (Fin N) ℂ)
    (Λ : Matrix (Fin N) (Fin N) ℂ) (hU : star U * U = 1)
    (hspec : Km = U * Λ * star U) :
    star U * Km * U = Λ := by
  rw [hspec]
  exact star_conj_collapse _ _ hU

/-- **THE CLASSIFICATION, general Hermitian form** (Tier T1
target): for `K` Hermitian and ANY `D`, with
`U = hK.eigenvectorUnitary` (Mathlib's eigenvector unitary) and
`d = hK.eigenvalues`,
`modularFlux K D = 0 ↔
  sectorBlockDiagonal (fun i => ((d i : ℂ))) (star U * D * U)`:
in K's eigenbasis, `D` is block-diagonal with respect to K's
distinct-eigenvalue sectors. The spectral input is the corpus's
own unpacking `HermitianReduction.hermitian_spectral_form`
(`K = U * diagonal d * star U`). Per HermitianReduction's
remainder R1 this is an eigenbasis statement; no original-basis
entry claim is made. Hermiticity of `D` is NOT needed and not
assumed. -/
theorem classification_hermitian {K : Matrix (Fin N) (Fin N) ℂ}
    (hK : K.IsHermitian) (D : Matrix (Fin N) (Fin N) ℂ) :
    modularFlux K D = 0 ↔
      sectorBlockDiagonal (fun i => ((hK.eigenvalues i : ℂ)))
        (star (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) * D
          * (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)) := by
  have hU1 : star (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  have hU2 : (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * star (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_mul_star_self _
  have hKU : star (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) * K
        * (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      = Matrix.diagonal (fun i => ((hK.eigenvalues i : ℂ))) :=
    star_mul_spectral_mul _ _ _ hU1 (hermitian_spectral_form hK)
  have hconj : star (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
        * (K * D - D * K) * (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      = Matrix.diagonal (fun i => ((hK.eigenvalues i : ℂ)))
          * (star (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) * D
            * (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ))
        - (star (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) * D
            * (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ))
          * Matrix.diagonal (fun i => ((hK.eigenvalues i : ℂ))) := by
    rw [Matrix.mul_sub, Matrix.sub_mul,
      ← starConj_mul _ _ _ hU2, ← starConj_mul _ _ _ hU2, hKU]
  have hzero : (K * D - D * K = 0) ↔
      star (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) * (K * D - D * K)
        * (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 0 := by
    constructor
    · intro h
      rw [h, Matrix.mul_zero, Matrix.zero_mul]
    · intro h
      have hback := conj_star_collapse
        (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) (K * D - D * K)
        hU1 hU2
      rw [h, Matrix.mul_zero, Matrix.zero_mul] at hback
      exact hback.symm
  calc modularFlux K D = 0
      ↔ K * D - D * K = 0 := modularFlux_eq_zero_iff_sub K D
    _ ↔ star (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
          * (K * D - D * K)
          * (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 0 := hzero
    _ ↔ Matrix.diagonal (fun i => ((hK.eigenvalues i : ℂ)))
          * (star (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) * D
            * (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ))
        - (star (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) * D
            * (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ))
          * Matrix.diagonal (fun i => ((hK.eigenvalues i : ℂ))) = 0 := by
        rw [hconj]
    _ ↔ modularFlux (Matrix.diagonal (fun i => ((hK.eigenvalues i : ℂ))))
          (star (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) * D
            * (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)) = 0 :=
        (modularFlux_eq_zero_iff_sub _ _).symm
    _ ↔ sectorBlockDiagonal (fun i => ((hK.eigenvalues i : ℂ)))
          (star (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) * D
            * (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)) :=
        classification_diagonal _ _

/-- **The general classification, entrywise** (Tier T1 target):
`classification_hermitian` spelled out — the flux at a Hermitian
`K` vanishes iff every eigenbasis entry of `D` between distinct
eigenvalues of `K` is zero:
`modularFlux K D = 0 ↔ ∀ i j, hK.eigenvalues i ≠ hK.eigenvalues j →
  (star U * D * U) i j = 0`. -/
theorem classification_hermitian_apply {K : Matrix (Fin N) (Fin N) ℂ}
    (hK : K.IsHermitian) (D : Matrix (Fin N) (Fin N) ℂ) :
    modularFlux K D = 0 ↔
      ∀ i j, hK.eigenvalues i ≠ hK.eigenvalues j →
        (star (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) * D
          * (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)) i j = 0 := by
  have hmain := classification_hermitian hK D
  rw [hmain]
  constructor
  · intro h i j hij
    exact h i j (fun hcast => hij (Complex.ofReal_inj.mp
      (show ((hK.eigenvalues i : ℂ)) = ((hK.eigenvalues j : ℂ)) from hcast)))
  · intro h i j hij
    exact h i j (fun heq => hij
      (congrArg (fun r : ℝ => ((r : ℂ))) heq))

end General

end ThetLogos.FluxClassification
