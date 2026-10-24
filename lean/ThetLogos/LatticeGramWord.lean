/-
# Third family, brick F1: the single-plaquette word factorization

Charter: `whitepaper/gram-third-family-scoping-2026-10-24.md`
(§2 the factorization, §5 brick F1). Companion dossiers:
`whitepaper/gram-transfer-r2-obstruction-2026-10-24.md` (§2: the
per-plaquette seam factor), `whitepaper/gram-route-c-2026-10-23.md`
(Route C, the d = 1 discharge this brick must specialize to).

## What this brick is

One crossing plaquette has Boltzmann factor
`e^{-β} · exp ((β/d) · Re ⟨X, Y⟩_HS)` with `X = ρ(y)`,
`Y = ρ(τ⁻¹ u τ')` (R2 §2, via `tr ρ(U_p) = ⟨ρ(y), ρ(τ⁻¹uτ′)⟩_HS`).
This module proves the word factorization of the exponential
factor at general finite `d`, any real `c` (in the application
`c = β/d`), as a `∑'` over word indices in the exact
`conj (B) * A` shape the landed integrated criterion
(`osForm_nonneg_of_gram_integrated`, `LatticeGramSeries.lean`)
consumes:

  `exp (c · Re ⟨X, P₁ * U * P₂⟩_HS)
     = ∑' idx : WordIdx, conj (featB idx U) * featA c idx X P₁ P₂`

The mechanism is the charter's §2.2: `Re z = (z + z̄)/2` splits
the exponential in two; each half expands by the tensor-power
Hilbert–Schmidt identity `⟨A^{⊗n}, B^{⊗n}⟩_HS = ⟨A, B⟩_HS ^ n`
(proved here from `GramWordTensor.tensorMat`) and its entry-path
expansion, in which **the same path appears on both sides** —
an inner product pairs a vector with itself index-by-index, so
no entry-selection step exists at which the (k, a)/(j, i)
mismatch of the dead factored family (T4c′) could enter. The
entries of the product `P₁ * U * P₂` are then split over
internal paths, which are **part of the index** (no sum inside
any feature): the `U`-entries form the B-side feature (a
function of the negative half's variable alone), the `P₁`/`P₂`
entries join the A side with the `X`-words.

Contents: §1 the HS pairing (entry form, trace bridge,
conjugation symmetry); §2 tensor powers and the two identities
(tensor-power HS identity, entry-path expansion); §3 the
internal-path split of a word over a triple product; §4 norm
plumbing for the domination bounds; §5 the feature packaging
(`PlaqIdx`, `WordIdx`, `featA`/`featB`) and the level-bound
summability over `PlaqIdx`; §6 the two factor HasSums; §7 the
combined features and the domination package F2 consumes
(entry bounds, the criterion's `CA`/`CB` shape, summability);
§8 the headline factorization; §9 the d = 1 control at
`circleRep`: the word series resums to Route C's landed
`fourier_exp_circle` (the charter's K-F1(b) guard).

## Fences

Single plaquette only: no assembly over the seam (F2), no
marginals, no Damping Lemma, no discharge (F3). The headline
is stated for abstract matrices — no unitarity, no group, no
Haar measure — because the factorization is finite tensor
algebra plus the exponential series; unitarity enters only
§7's domination bounds, as hypotheses. **NO CLAIM** — parts
of any official Clay statement closed by this module: 0.
Stage 1b-B positivity: T1 for U(1) (Route C); general (G, ρ)
OPEN until F3 lands, and this brick changes no label.

## Status

- Status: **VERIFIED — STANDS WHOLE (T1), landed 2026-10-24.**
  PARENT-VERIFIED: fresh `lake build ThetLogos.LatticeGramWord`
  green (3,445 jobs, exit 0, olean deleted first); 39 strict
  theorems / 16 defs in this file, zero `sorry`/`admit`;
  `#print axioms` on `exp_re_hsInner_word`, `word_tsum_circle`,
  `tensor_hsInner`, `hasSum_factor_one`, `summable_wordCA_mul`
  — standard only (`propext`, `Classical.choice`, `Quot.sound`),
  no `sorryAx`. Neither pre-registered kill fired: K-F1(a)
  (basis choice breaking the word form) — the features are
  entry paths, part of the index, no basis chosen anywhere;
  K-F1(b) (d = 1 control failing to resum) — `word_tsum_circle`
  resums to Route C's `fourier_exp_circle` through the common
  value `exp (β · Re s)`. Dossier:
  `whitepaper/gram-third-family-f1-word-factorization-2026-10-24.md`.
-/

import ThetLogos.LatticeGramSeries
import ThetLogos.GramWordTensor

open Finset
open scoped Matrix

namespace ThetLogos

namespace GramWord

variable {d : ℕ}

/-! ## §1. The Hilbert–Schmidt pairing, entry form -/

/-- The Hilbert–Schmidt pairing of two finite square matrices,
in entry form: `hsInner X Y = ∑ i, ∑ j, star (X i j) * Y i j`
(conjugate-linear in the first argument, linear in the
second). This is the charters' `⟨X, Y⟩_HS`, stated for an
arbitrary finite index type so that it applies both to the
plaquette matrices (index `Fin d`) and to their tensor
powers (index `Fin n → Fin d`). -/
def hsInner {ι : Type*} [Fintype ι] (X Y : Matrix ι ι ℂ) : ℂ :=
  ∑ i, ∑ j, star (X i j) * Y i j

/-- The entry form is the trace form: `⟨X, Y⟩_HS = tr (Xᴴ * Y)`. -/
theorem hsInner_eq_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : Matrix ι ι ℂ) :
    hsInner X Y = (Xᴴ * Y).trace := by
  unfold hsInner
  rw [Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

/-- Conjugation swaps the arguments. -/
theorem star_hsInner {ι : Type*} [Fintype ι] (X Y : Matrix ι ι ℂ) :
    star (hsInner X Y) = hsInner Y X := by
  simp only [hsInner, star_sum, star_mul, star_star]

/-! ## §2. Tensor powers, words, and the two identities -/

/-- The `n`-fold tensor power of a matrix: the slot tensor
matrix of the constant family (`GramWordTensor.tensorMat`). -/
def tensorPow (n : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  GramWordTensor.tensorMat (fun _ : Fin n => M)

theorem tensorPow_apply (n : ℕ) (M : Matrix (Fin d) (Fin d) ℂ)
    (p q : Fin n → Fin d) :
    tensorPow n M p q = ∏ j, M (p j) (q j) :=
  GramWordTensor.tensorMat_apply _ _ _

/-- A **word**: the product of the entries of `M` along an
entry path `α : Fin n → Fin d × Fin d`. -/
def word {n : ℕ} (α : Fin n → Fin d × Fin d)
    (M : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  ∏ j, M (α j).1 (α j).2

/-- The reindexing that turns a pair of row/column paths into
one entry path. -/
def pathEquiv (n : ℕ) :
    ((Fin n → Fin d) × (Fin n → Fin d)) ≃ (Fin n → Fin d × Fin d) where
  toFun pq j := (pq.1 j, pq.2 j)
  invFun α := (fun j => (α j).1, fun j => (α j).2)
  left_inv pq := by cases pq; rfl
  right_inv α := by funext j; rfl

/-- **Entry-path expansion.** The tensor-power HS pairing is
the sum over entry paths of `conj (word α X) * word α Y` —
the **same** path `α` on both sides, by the definition of an
inner product. -/
theorem tensor_hsInner_word (n : ℕ) (X Y : Matrix (Fin d) (Fin d) ℂ) :
    hsInner (tensorPow n X) (tensorPow n Y)
      = ∑ α : Fin n → Fin d × Fin d, star (word α X) * word α Y := by
  have hpair : (∑ p : Fin n → Fin d, ∑ q : Fin n → Fin d,
        star (tensorPow n X p q) * tensorPow n Y p q)
      = ∑ pq : (Fin n → Fin d) × (Fin n → Fin d),
        star (tensorPow n X pq.1 pq.2) * tensorPow n Y pq.1 pq.2 :=
    (Fintype.sum_prod_type' fun p q =>
      star (tensorPow n X p q) * tensorPow n Y p q).symm
  have hstep : hsInner (tensorPow n X) (tensorPow n Y)
      = ∑ pq : (Fin n → Fin d) × (Fin n → Fin d),
        star (tensorPow n X pq.1 pq.2) * tensorPow n Y pq.1 pq.2 := hpair
  rw [hstep]
  refine Fintype.sum_equiv (pathEquiv n) _ _ fun pq => ?_
  rfl

/-- **Tensor-power HS identity.** `⟨X^{⊗n}, Y^{⊗n}⟩_HS =
⟨X, Y⟩_HS ^ n`: the engine of the exponential expansion. -/
theorem tensor_hsInner (n : ℕ) (X Y : Matrix (Fin d) (Fin d) ℂ) :
    hsInner (tensorPow n X) (tensorPow n Y) = hsInner X Y ^ n := by
  classical
  have step : ∀ α : Fin n → Fin d × Fin d,
      star (word α X) * word α Y
        = ∏ j, (star (X (α j).1 (α j).2) * Y (α j).1 (α j).2) := by
    intro α
    rw [word, word, star_prod, ← Finset.prod_mul_distrib]
  have hprod : (∏ _j : Fin n, ∑ k : Fin d × Fin d,
        star (X k.1 k.2) * Y k.1 k.2)
      = ∑ α : Fin n → Fin d × Fin d,
        ∏ j, (star (X (α j).1 (α j).2) * Y (α j).1 (α j).2) := by
    have h := Finset.prod_univ_sum
      (fun _ : Fin n => (Finset.univ : Finset (Fin d × Fin d)))
      (fun (_j : Fin n) (k : Fin d × Fin d) => star (X k.1 k.2) * Y k.1 k.2)
    rwa [Fintype.piFinset_univ] at h
  have hsum : ∀ _j : Fin n,
      (∑ k : Fin d × Fin d, star (X k.1 k.2) * Y k.1 k.2) = hsInner X Y :=
    fun _j => Fintype.sum_prod_type _
  calc hsInner (tensorPow n X) (tensorPow n Y)
      = ∑ α : Fin n → Fin d × Fin d, star (word α X) * word α Y :=
        tensor_hsInner_word n X Y
    _ = ∑ α : Fin n → Fin d × Fin d,
          ∏ j, (star (X (α j).1 (α j).2) * Y (α j).1 (α j).2) :=
        Finset.sum_congr rfl fun α _ => step α
    _ = ∏ _j : Fin n, ∑ k : Fin d × Fin d, star (X k.1 k.2) * Y k.1 k.2 :=
        hprod.symm
    _ = ∏ _j : Fin n, hsInner X Y :=
        Finset.prod_congr rfl fun j _ => hsum j
    _ = hsInner X Y ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## §3. Splitting a word over a triple product -/

/-- An entry of a triple product, expanded over its two
internal indices. -/
theorem mul3_apply (P₁ U P₂ : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (P₁ * U * P₂) i j = ∑ k, ∑ l, P₁ i k * U k l * P₂ l j := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The **plane word**: the `P₁`- and `P₂`-entries along an
entry path `α` with internal path `κ` — the part of a word
over `P₁ * U * P₂` that lives on the plane (positive) side. -/
def planeWord {n : ℕ} (α κ : Fin n → Fin d × Fin d)
    (P₁ P₂ : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  ∏ j, P₁ (α j).1 (κ j).1 * P₂ (κ j).2 (α j).2

/-- A word over a triple product splits over internal paths:
`word α (P₁ * U * P₂) = ∑ κ, planeWord α κ P₁ P₂ * word κ U`.
The internal path `κ` is a summation index here; in the
feature packaging of §5 it becomes part of the word index, so
that no feature contains a sum. -/
theorem word_mul3 {n : ℕ} (α : Fin n → Fin d × Fin d)
    (P₁ U P₂ : Matrix (Fin d) (Fin d) ℂ) :
    word α (P₁ * U * P₂)
      = ∑ κ : Fin n → Fin d × Fin d, planeWord α κ P₁ P₂ * word κ U := by
  classical
  have h1 : ∀ j : Fin n, (P₁ * U * P₂) (α j).1 (α j).2
      = ∑ kl : Fin d × Fin d,
        P₁ (α j).1 kl.1 * U kl.1 kl.2 * P₂ kl.2 (α j).2 := by
    intro j
    rw [mul3_apply]
    exact (Fintype.sum_prod_type' fun k l =>
      P₁ (α j).1 k * U k l * P₂ l (α j).2).symm
  have hprod : (∏ j : Fin n, ∑ kl : Fin d × Fin d,
        P₁ (α j).1 kl.1 * U kl.1 kl.2 * P₂ kl.2 (α j).2)
      = ∑ κ : Fin n → Fin d × Fin d, ∏ j,
        P₁ (α j).1 (κ j).1 * U (κ j).1 (κ j).2 * P₂ (κ j).2 (α j).2 := by
    have h := Finset.prod_univ_sum
      (fun _ : Fin n => (Finset.univ : Finset (Fin d × Fin d)))
      (fun (j : Fin n) (kl : Fin d × Fin d) =>
        P₁ (α j).1 kl.1 * U kl.1 kl.2 * P₂ kl.2 (α j).2)
    rwa [Fintype.piFinset_univ] at h
  calc word α (P₁ * U * P₂)
      = ∏ j, ∑ kl : Fin d × Fin d,
          P₁ (α j).1 kl.1 * U kl.1 kl.2 * P₂ kl.2 (α j).2 :=
        Finset.prod_congr rfl fun j _ => h1 j
    _ = ∑ κ : Fin n → Fin d × Fin d, ∏ j,
          P₁ (α j).1 (κ j).1 * U (κ j).1 (κ j).2 * P₂ (κ j).2 (α j).2 :=
        hprod
    _ = ∑ κ : Fin n → Fin d × Fin d, planeWord α κ P₁ P₂ * word κ U := by
        refine Finset.sum_congr rfl fun κ _ => ?_
        rw [planeWord, word, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j _ => ?_
        ring

/-! ## §4. Norm plumbing for products (domination bounds) -/

/-- A finite product bounded factor-wise by a constant power:
`‖∏ i ∈ s, f i‖ ≤ R ^ s.card` when every factor has norm
`≤ R`. (Proved by finset induction; no norm-of-product API
is assumed.) -/
theorem norm_prod_le_pow {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (R : ℝ) (hR : ∀ i ∈ s, ‖f i‖ ≤ R) (hR0 : 0 ≤ R) :
    ‖∏ i ∈ s, f i‖ ≤ R ^ s.card := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
    refine (norm_mul_le _ _).trans (mul_le_mul (hR a (Finset.mem_insert_self a s))
      (ih fun i hi => hR i (Finset.mem_insert_of_mem hi))
      (norm_nonneg _) hR0)

/-- A word whose matrix entries are all `≤ R` in norm is
`≤ R ^ n`. -/
theorem norm_word_le {n : ℕ} (α : Fin n → Fin d × Fin d)
    (M : Matrix (Fin d) (Fin d) ℂ) (R : ℝ)
    (hR : ∀ i j, ‖M i j‖ ≤ R) (hR0 : 0 ≤ R) : ‖word α M‖ ≤ R ^ n := by
  have h := norm_prod_le_pow Finset.univ (fun j => M (α j).1 (α j).2) R
    (fun j _ => hR _ _) hR0
  rwa [Finset.card_univ, Fintype.card_fin] at h

/-- A plane word whose matrix entries are all `≤ R` in norm
is `≤ (R * R) ^ n`. -/
theorem norm_planeWord_le {n : ℕ} (α κ : Fin n → Fin d × Fin d)
    (P₁ P₂ : Matrix (Fin d) (Fin d) ℂ) (R : ℝ)
    (h₁ : ∀ i j, ‖P₁ i j‖ ≤ R) (h₂ : ∀ i j, ‖P₂ i j‖ ≤ R) (hR0 : 0 ≤ R) :
    ‖planeWord α κ P₁ P₂‖ ≤ (R * R) ^ n := by
  have h := norm_prod_le_pow Finset.univ
    (fun j => P₁ (α j).1 (κ j).1 * P₂ (κ j).2 (α j).2) (R * R)
    (fun j _ => (norm_mul_le _ _).trans
      (mul_le_mul (h₁ (α j).1 (κ j).1) (h₂ (κ j).2 (α j).2)
        (norm_nonneg _) hR0))
    (mul_nonneg hR0 hR0)
  rwa [Finset.card_univ, Fintype.card_fin] at h

/-! ## §5. Feature packaging and `PlaqIdx` summability

The F2-facing packaging.  `PlaqIdx d` is the single-plaquette
word index of the charter criterion §1: a level `n` together
with an `A`-side entry path and a `B`-side entry path.  The two
factors of the charter §2 split are the feature families
`featA1`/`featA2` (A-side) and `featB1`/`featB2` (B-side); F2
assembles products of two plaquette indices into the
criterion's `A` and `B`. -/

/-- The single-plaquette word index: level `n`, an `A`-side
entry path `α`, and a `B`-side entry path `κ`. -/
def PlaqIdx (d : ℕ) : Type :=
  Σ n : ℕ, (Fin n → Fin d × Fin d) × (Fin n → Fin d × Fin d)

instance : Countable (Fin d × Fin d) :=
  Countable.of_equiv (Fin (Fintype.card (Fin d × Fin d)))
    (Fintype.equivFinOfCardEq rfl).symm

instance : Countable (PlaqIdx d) :=
  Countable.of_equiv
    (Σ n : ℕ, (Fin n → Fin d × Fin d) × (Fin n → Fin d × Fin d))
    (Equiv.refl _)

/-- The two-plaquette word index F2 consumes (one `PlaqIdx`
per factor of the charter §2 split). -/
def WordIdx (d : ℕ) : Type := PlaqIdx d × PlaqIdx d

instance : Countable (WordIdx d) :=
  Countable.of_equiv (PlaqIdx d × PlaqIdx d) (Equiv.refl _)

/-- B-side feature, first factor: the `U`-word along `κ`. -/
def featB1 {n : ℕ} (κ : Fin n → Fin d × Fin d)
    (U : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  word κ U

/-- B-side feature, second factor: the conjugate `U`-word
along `κ`. -/
def featB2 {n : ℕ} (κ : Fin n → Fin d × Fin d)
    (U : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  star (word κ U)

/-- A-side feature, first factor: coefficient times the
`X`-word along `α` times the conjugate plane word. -/
noncomputable def featA1 (c : ℝ) {n : ℕ} (α κ : Fin n → Fin d × Fin d)
    (X P₁ P₂ : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  ((c / 2 : ℂ)) ^ n / (Nat.factorial n : ℂ) * word α X * star (planeWord α κ P₁ P₂)

/-- A-side feature, second factor: coefficient times the
conjugate `X`-word along `α` times the plane word. -/
noncomputable def featA2 (c : ℝ) {n : ℕ} (α κ : Fin n → Fin d × Fin d)
    (X P₁ P₂ : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  ((c / 2 : ℂ)) ^ n / (Nat.factorial n : ℂ) * star (word α X) * planeWord α κ P₁ P₂

/-- The exponential series as a `HasSum` (the `NormedSpace.exp`
series, transported to `Complex.exp`). -/
theorem hasSum_exp_div (z : ℂ) :
    HasSum (fun n : ℕ => z ^ n / (Nat.factorial n : ℂ)) (Complex.exp z) := by
  have h := NormedSpace.expSeries_div_hasSum_exp z
  rwa [← Complex.exp_eq_exp_ℂ] at h

/-- The real part as the average of a complex number and its
conjugate — the charter §2 split of the `Re`. -/
theorem ofReal_re (z : ℂ) : ((z.re : ℝ) : ℂ) = (z + star z) / 2 :=
  RCLike.re_eq_add_conj z

/-- Four equal powers collapse: `Kⁿ · (Kⁿ · (Kⁿ · Kⁿ)) = (K⁴)ⁿ`. -/
theorem pow_four (K : ℝ) (n : ℕ) :
    K ^ n * (K ^ n * (K ^ n * K ^ n)) = (K ^ 4) ^ n := by
  rw [← pow_add, ← pow_add, ← pow_add, ← pow_mul]
  congr 1
  ring

/-- The cardinality of a `PlaqIdx` fiber, as a real number:
`d ^ (4n)`. -/
theorem card_plaqIdx_fiber (n : ℕ) :
    (Fintype.card ((Fin n → Fin d × Fin d) × (Fin n → Fin d × Fin d)) : ℝ)
      = (d : ℝ) ^ (4 * n) := by
  rw [Fintype.card_prod, Fintype.card_pi]
  simp only [Fintype.card_prod, Fintype.card_fin, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  push_cast
  rw [pow_mul]
  ring

/-- Summability over `PlaqIdx` from a level bound: if the
family is dominated levelwise by a nonnegative `b` and
`d ^ (4n) · b n` is summable (the fiber has `d ^ (4n)` points),
then the family is summable. -/
theorem summable_plaqIdx_of_level_bound {F : PlaqIdx d → ℂ} {b : ℕ → ℝ}
    (_hb : ∀ n, 0 ≤ b n) (hF : ∀ i₁, ‖F i₁‖ ≤ b i₁.1)
    (hsum : Summable fun n => (d : ℝ) ^ (4 * n) * b n) : Summable F := by
  refine Summable.of_norm ?_
  refine (summable_sigma_of_nonneg (fun i₁ => norm_nonneg _)).mpr
    ⟨fun n => (hasSum_fintype _).summable, ?_⟩
  refine Summable.of_nonneg_of_le
    (fun n => tsum_nonneg fun fib => norm_nonneg _) (fun n => ?_) hsum
  rw [tsum_fintype]
  calc (∑ fib, ‖F ⟨n, fib⟩‖) ≤ ∑ _fib, b n :=
      Finset.sum_le_sum fun fib _ => hF ⟨n, fib⟩
    _ = (d : ℝ) ^ (4 * n) * b n := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          card_plaqIdx_fiber]

/-! ## §6. The two factor HasSums

Each factor of the charter §2 split is built the same way: the
exponential series at the paired matrix, its `n`-th term
rewritten by the tensor identity into a finite fiber sum by
the path expansion and the internal-path split, and the fibers
flattened over `PlaqIdx` by `HasSum.sigma_of_hasSum`, with
summability from the level bound. -/

/-- The norm of the A-side coefficient. -/
theorem norm_coeff (c : ℝ) (n : ℕ) :
    ‖((c / 2 : ℂ)) ^ n / (Nat.factorial n : ℂ)‖
      = (|c| / 2) ^ n / (Nat.factorial n : ℝ) := by
  rw [norm_div, norm_pow]
  simp

/-- The level HasSum: the exponential series at the paired
matrix `X` against `Y`, with its `n`-th term rewritten by the
tensor-power HS identity. -/
theorem hasSum_level (c : ℝ) (X Y : Matrix (Fin d) (Fin d) ℂ) :
    HasSum (fun n : ℕ => ((c / 2 : ℂ)) ^ n / (Nat.factorial n : ℂ)
        * hsInner (tensorPow n X) (tensorPow n Y))
      (Complex.exp ((c / 2 : ℂ) * hsInner X Y)) := by
  have key : (fun n : ℕ => ((c / 2 : ℂ) * hsInner X Y) ^ n
        / (Nat.factorial n : ℂ))
      = (fun n : ℕ => ((c / 2 : ℂ)) ^ n / (Nat.factorial n : ℂ)
        * hsInner (tensorPow n X) (tensorPow n Y)) := by
    funext n
    rw [mul_pow, ← tensor_hsInner]
    ring
  rw [← key]
  exact hasSum_exp_div _

/-- The first factor's fiber sum: at level `n`, the finite sum
of `conj (B-feature) · (A-feature)` over the entry paths is the
paired tensor term, against `P₁ * U * P₂` on the `X`-side. -/
theorem fiber_sum_one (c : ℝ) (n : ℕ)
    (X P₁ P₂ U : Matrix (Fin d) (Fin d) ℂ) :
    (∑ p : (Fin n → Fin d × Fin d) × (Fin n → Fin d × Fin d),
        star (featB1 p.2 U) * featA1 c p.1 p.2 X P₁ P₂)
      = ((c / 2 : ℂ)) ^ n / (Nat.factorial n : ℂ)
        * hsInner (tensorPow n (P₁ * U * P₂)) (tensorPow n X) := by
  rw [Fintype.sum_prod_type, tensor_hsInner_word, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  show (∑ κ : Fin n → Fin d × Fin d,
      star (featB1 κ U) * featA1 c α κ X P₁ P₂)
    = ((c / 2 : ℂ)) ^ n / (Nat.factorial n : ℂ)
      * (star (word α (P₁ * U * P₂)) * word α X)
  simp only [featB1, featA1]
  rw [word_mul3, star_sum]
  simp only [star_mul]
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  ring

/-- The second factor's fiber sum: conjugate features, against
`P₁ * U * P₂` on the `Y`-side. -/
theorem fiber_sum_two (c : ℝ) (n : ℕ)
    (X P₁ P₂ U : Matrix (Fin d) (Fin d) ℂ) :
    (∑ p : (Fin n → Fin d × Fin d) × (Fin n → Fin d × Fin d),
        star (featB2 p.2 U) * featA2 c p.1 p.2 X P₁ P₂)
      = ((c / 2 : ℂ)) ^ n / (Nat.factorial n : ℂ)
        * hsInner (tensorPow n X) (tensorPow n (P₁ * U * P₂)) := by
  rw [Fintype.sum_prod_type, tensor_hsInner_word, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  show (∑ κ : Fin n → Fin d × Fin d,
      star (featB2 κ U) * featA2 c α κ X P₁ P₂)
    = ((c / 2 : ℂ)) ^ n / (Nat.factorial n : ℂ)
      * (star (word α X) * word α (P₁ * U * P₂))
  simp only [featB2, featA2, star_star]
  rw [word_mul3, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  ring

/-- The level bound in single-power form:
`(|c|/2)ⁿ / n! · (K⁴)ⁿ = ((|c|/2) · K⁴)ⁿ / n!`. -/
theorem level_bound_eq (c K : ℝ) (n : ℕ) :
    (|c| / 2) ^ n / (Nat.factorial n : ℝ) * (K ^ 4) ^ n
      = ((|c| / 2) * K ^ 4) ^ n / (Nat.factorial n : ℝ) := by
  rw [mul_pow, div_mul_eq_mul_div]

/-- The level bound for both factor families, discharged by
the exponential series. -/
theorem summable_factor_bound (c : ℝ) (K : ℝ) (_hK : 0 ≤ K) :
    Summable fun n => (d : ℝ) ^ (4 * n)
      * ((|c| / 2) ^ n / (Nat.factorial n : ℝ) * (K ^ 4) ^ n) := by
  refine Summable.congr (Real.summable_pow_div_factorial
    ((d : ℝ) ^ 4 * ((|c| / 2) * K ^ 4))) fun n => ?_
  rw [level_bound_eq, pow_mul, ← mul_div_assoc, ← mul_pow]

/-- Norm bound for the first factor family. -/
theorem norm_factor_one_le (c : ℝ) (K : ℝ) (hK : 0 ≤ K)
    (X P₁ P₂ U : Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ i j, ‖X i j‖ ≤ K) (hP₁ : ∀ i j, ‖P₁ i j‖ ≤ K)
    (hP₂ : ∀ i j, ‖P₂ i j‖ ≤ K) (hU : ∀ i j, ‖U i j‖ ≤ K)
    (i₁ : PlaqIdx d) :
    ‖star (featB1 i₁.2.2 U) * featA1 c i₁.2.1 i₁.2.2 X P₁ P₂‖
      ≤ (|c| / 2) ^ i₁.1 / (Nat.factorial i₁.1 : ℝ) * (K ^ 4) ^ i₁.1 := by
  have h1 : ‖word i₁.2.1 X‖ ≤ K ^ i₁.1 := norm_word_le _ _ _ hX hK
  have h2 : ‖star (planeWord i₁.2.1 i₁.2.2 P₁ P₂)‖ ≤ (K * K) ^ i₁.1 := by
    rw [norm_star]
    exact norm_planeWord_le _ _ _ _ _ hP₁ hP₂ hK
  have hB : ‖star (featB1 i₁.2.2 U)‖ ≤ K ^ i₁.1 := by
    rw [norm_star]
    exact norm_word_le _ _ _ hU hK
  have hA : ‖featA1 c i₁.2.1 i₁.2.2 X P₁ P₂‖
      ≤ (|c| / 2) ^ i₁.1 / (Nat.factorial i₁.1 : ℝ)
        * (K ^ i₁.1 * (K * K) ^ i₁.1) := by
    have hnorm : ‖featA1 c i₁.2.1 i₁.2.2 X P₁ P₂‖
        ≤ ‖((c / 2 : ℂ)) ^ i₁.1 / (Nat.factorial i₁.1 : ℂ)‖
          * (‖word i₁.2.1 X‖ * ‖star (planeWord i₁.2.1 i₁.2.2 P₁ P₂)‖) := by
      show ‖((c / 2 : ℂ)) ^ i₁.1 / (Nat.factorial i₁.1 : ℂ)
          * word i₁.2.1 X * star (planeWord i₁.2.1 i₁.2.2 P₁ P₂)‖ ≤ _
      refine (norm_mul_le _ _).trans ?_
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    refine hnorm.trans ?_
    rw [norm_coeff]
    exact mul_le_mul (le_refl _)
      (mul_le_mul h1 h2 (norm_nonneg _) (pow_nonneg hK _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
  calc ‖star (featB1 i₁.2.2 U) * featA1 c i₁.2.1 i₁.2.2 X P₁ P₂‖
      ≤ ‖star (featB1 i₁.2.2 U)‖ * ‖featA1 c i₁.2.1 i₁.2.2 X P₁ P₂‖ :=
        norm_mul_le _ _
    _ ≤ K ^ i₁.1 * ((|c| / 2) ^ i₁.1 / (Nat.factorial i₁.1 : ℝ)
          * (K ^ i₁.1 * (K * K) ^ i₁.1)) :=
        mul_le_mul hB hA (norm_nonneg _) (pow_nonneg hK _)
    _ = (|c| / 2) ^ i₁.1 / (Nat.factorial i₁.1 : ℝ) * (K ^ 4) ^ i₁.1 := by
        have e : K ^ i₁.1 * ((|c| / 2) ^ i₁.1 / (Nat.factorial i₁.1 : ℝ)
              * (K ^ i₁.1 * (K * K) ^ i₁.1))
            = ((|c| / 2) ^ i₁.1 / (Nat.factorial i₁.1 : ℝ))
              * (K ^ i₁.1 * (K ^ i₁.1 * (K ^ i₁.1 * K ^ i₁.1))) := by
          rw [mul_pow]; ring
        rw [e, pow_four]

/-- Norm bound for the second factor family. -/
theorem norm_factor_two_le (c : ℝ) (K : ℝ) (hK : 0 ≤ K)
    (X P₁ P₂ U : Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ i j, ‖X i j‖ ≤ K) (hP₁ : ∀ i j, ‖P₁ i j‖ ≤ K)
    (hP₂ : ∀ i j, ‖P₂ i j‖ ≤ K) (hU : ∀ i j, ‖U i j‖ ≤ K)
    (i₁ : PlaqIdx d) :
    ‖star (featB2 i₁.2.2 U) * featA2 c i₁.2.1 i₁.2.2 X P₁ P₂‖
      ≤ (|c| / 2) ^ i₁.1 / (Nat.factorial i₁.1 : ℝ) * (K ^ 4) ^ i₁.1 := by
  have h1 : ‖star (word i₁.2.1 X)‖ ≤ K ^ i₁.1 := by
    rw [norm_star]
    exact norm_word_le _ _ _ hX hK
  have h2 : ‖planeWord i₁.2.1 i₁.2.2 P₁ P₂‖ ≤ (K * K) ^ i₁.1 :=
    norm_planeWord_le _ _ _ _ _ hP₁ hP₂ hK
  have hB : ‖star (featB2 i₁.2.2 U)‖ ≤ K ^ i₁.1 := by
    simp only [featB2, star_star]
    exact norm_word_le _ _ _ hU hK
  have hA : ‖featA2 c i₁.2.1 i₁.2.2 X P₁ P₂‖
      ≤ (|c| / 2) ^ i₁.1 / (Nat.factorial i₁.1 : ℝ)
        * (K ^ i₁.1 * (K * K) ^ i₁.1) := by
    have hnorm : ‖featA2 c i₁.2.1 i₁.2.2 X P₁ P₂‖
        ≤ ‖((c / 2 : ℂ)) ^ i₁.1 / (Nat.factorial i₁.1 : ℂ)‖
          * (‖star (word i₁.2.1 X)‖ * ‖planeWord i₁.2.1 i₁.2.2 P₁ P₂‖) := by
      show ‖((c / 2 : ℂ)) ^ i₁.1 / (Nat.factorial i₁.1 : ℂ)
          * star (word i₁.2.1 X) * planeWord i₁.2.1 i₁.2.2 P₁ P₂‖ ≤ _
      refine (norm_mul_le _ _).trans ?_
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    refine hnorm.trans ?_
    rw [norm_coeff]
    exact mul_le_mul (le_refl _)
      (mul_le_mul h1 h2 (norm_nonneg _) (pow_nonneg hK _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
  calc ‖star (featB2 i₁.2.2 U) * featA2 c i₁.2.1 i₁.2.2 X P₁ P₂‖
      ≤ ‖star (featB2 i₁.2.2 U)‖ * ‖featA2 c i₁.2.1 i₁.2.2 X P₁ P₂‖ :=
        norm_mul_le _ _
    _ ≤ K ^ i₁.1 * ((|c| / 2) ^ i₁.1 / (Nat.factorial i₁.1 : ℝ)
          * (K ^ i₁.1 * (K * K) ^ i₁.1)) :=
        mul_le_mul hB hA (norm_nonneg _) (pow_nonneg hK _)
    _ = (|c| / 2) ^ i₁.1 / (Nat.factorial i₁.1 : ℝ) * (K ^ 4) ^ i₁.1 := by
        have e : K ^ i₁.1 * ((|c| / 2) ^ i₁.1 / (Nat.factorial i₁.1 : ℝ)
              * (K ^ i₁.1 * (K * K) ^ i₁.1))
            = ((|c| / 2) ^ i₁.1 / (Nat.factorial i₁.1 : ℝ))
              * (K ^ i₁.1 * (K ^ i₁.1 * (K ^ i₁.1 * K ^ i₁.1))) := by
          rw [mul_pow]; ring
        rw [e, pow_four]

/-- **First factor HasSum.**  The first exponential of the
charter §2 split, as a sum over single-plaquette word indices
of `conj (B-feature) · (A-feature)` with the same `B`-path on
both sides of the pairing.  Entry bounds enter only through
the summability side condition. -/
theorem hasSum_factor_one (c : ℝ) (K : ℝ) (hK : 0 ≤ K)
    (X P₁ P₂ U : Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ i j, ‖X i j‖ ≤ K) (hP₁ : ∀ i j, ‖P₁ i j‖ ≤ K)
    (hP₂ : ∀ i j, ‖P₂ i j‖ ≤ K) (hU : ∀ i j, ‖U i j‖ ≤ K) :
    HasSum (fun i₁ : PlaqIdx d =>
        star (featB1 i₁.2.2 U) * featA1 c i₁.2.1 i₁.2.2 X P₁ P₂)
      (Complex.exp ((c / 2 : ℂ) * hsInner (P₁ * U * P₂) X)) := by
  refine HasSum.sigma_of_hasSum (hasSum_level c (P₁ * U * P₂) X)
    (fun n => ?_) (summable_plaqIdx_of_level_bound
      (b := fun n => (|c| / 2) ^ n / (Nat.factorial n : ℝ) * (K ^ 4) ^ n)
      (fun n => by positivity)
      (fun i₁ => norm_factor_one_le c K hK X P₁ P₂ U hX hP₁ hP₂ hU i₁)
      (summable_factor_bound c K hK))
  show HasSum (fun p : (Fin n → Fin d × Fin d) × (Fin n → Fin d × Fin d) =>
      star (featB1 p.2 U) * featA1 c p.1 p.2 X P₁ P₂) _
  rw [← fiber_sum_one]
  exact hasSum_fintype (fun p : (Fin n → Fin d × Fin d)
    × (Fin n → Fin d × Fin d) =>
    star (featB1 p.2 U) * featA1 c p.1 p.2 X P₁ P₂)

/-- **Second factor HasSum** (the conjugate factor). -/
theorem hasSum_factor_two (c : ℝ) (K : ℝ) (hK : 0 ≤ K)
    (X P₁ P₂ U : Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ i j, ‖X i j‖ ≤ K) (hP₁ : ∀ i j, ‖P₁ i j‖ ≤ K)
    (hP₂ : ∀ i j, ‖P₂ i j‖ ≤ K) (hU : ∀ i j, ‖U i j‖ ≤ K) :
    HasSum (fun i₁ : PlaqIdx d =>
        star (featB2 i₁.2.2 U) * featA2 c i₁.2.1 i₁.2.2 X P₁ P₂)
      (Complex.exp ((c / 2 : ℂ) * hsInner X (P₁ * U * P₂))) := by
  refine HasSum.sigma_of_hasSum (hasSum_level c X (P₁ * U * P₂))
    (fun n => ?_) (summable_plaqIdx_of_level_bound
      (b := fun n => (|c| / 2) ^ n / (Nat.factorial n : ℝ) * (K ^ 4) ^ n)
      (fun n => by positivity)
      (fun i₁ => norm_factor_two_le c K hK X P₁ P₂ U hX hP₁ hP₂ hU i₁)
      (summable_factor_bound c K hK))
  show HasSum (fun p : (Fin n → Fin d × Fin d) × (Fin n → Fin d × Fin d) =>
      star (featB2 p.2 U) * featA2 c p.1 p.2 X P₁ P₂) _
  rw [← fiber_sum_two]
  exact hasSum_fintype (fun p : (Fin n → Fin d × Fin d)
    × (Fin n → Fin d × Fin d) =>
    star (featB2 p.2 U) * featA2 c p.1 p.2 X P₁ P₂)

/-! ## §7. Combined features and the domination package

The criterion (`osForm_nonneg_of_gram_integrated` in
`LatticeGramSeries`) consumes, over a countable index, features
`A i y` and `B i u` with real bounds `CA i`, `CB i`,
`‖A i y‖ ≤ CA i`, `‖B i u‖ ≤ CB i`, and
`Summable fun i => CA i * CB i`.  F2's index is `WordIdx d`;
its A-feature is `featA c · X P₁ P₂`, its B-feature is `featB ·
U` (the criterion applies `star` to the B-feature, matching
the `star (featB idx U)` of §8).  The bounds `wordCA`/`wordCB`
split the work: `wordCA` carries the coefficients, the
`X`-words and the plane words; `wordCB` carries the `U`-words.
Their product regroups to the product of the two factor level
bounds (`wordCA_mul_wordCB`), hence is summable. -/

/-- The combined B-side feature over a two-plaquette word
index: the first factor's `U`-word times the second factor's
conjugate `U`-word. -/
def featB (idx : WordIdx d) (U : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  featB1 idx.1.2.2 U * featB2 idx.2.2.2 U

/-- The combined A-side feature over a two-plaquette word
index: the product of the two factors' A-features. -/
noncomputable def featA (c : ℝ) (idx : WordIdx d)
    (X P₁ P₂ : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  featA1 c idx.1.2.1 idx.1.2.2 X P₁ P₂
    * featA2 c idx.2.2.1 idx.2.2.2 X P₁ P₂

/-- Entry bound for the first A-feature. -/
theorem norm_featA1_le (c : ℝ) (K : ℝ) (hK : 0 ≤ K)
    (X P₁ P₂ : Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ i j, ‖X i j‖ ≤ K) (hP₁ : ∀ i j, ‖P₁ i j‖ ≤ K)
    (hP₂ : ∀ i j, ‖P₂ i j‖ ≤ K) {n : ℕ}
    (α κ : Fin n → Fin d × Fin d) :
    ‖featA1 c α κ X P₁ P₂‖
      ≤ (|c| / 2) ^ n / (Nat.factorial n : ℝ) * (K ^ n * (K * K) ^ n) := by
  have h1 : ‖word α X‖ ≤ K ^ n := norm_word_le _ _ _ hX hK
  have h2 : ‖star (planeWord α κ P₁ P₂)‖ ≤ (K * K) ^ n := by
    rw [norm_star]
    exact norm_planeWord_le _ _ _ _ _ hP₁ hP₂ hK
  have hnorm : ‖featA1 c α κ X P₁ P₂‖
      ≤ ‖((c / 2 : ℂ)) ^ n / (Nat.factorial n : ℂ)‖
        * (‖word α X‖ * ‖star (planeWord α κ P₁ P₂)‖) := by
    show ‖((c / 2 : ℂ)) ^ n / (Nat.factorial n : ℂ)
        * word α X * star (planeWord α κ P₁ P₂)‖ ≤ _
    refine (norm_mul_le _ _).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
  refine hnorm.trans ?_
  rw [norm_coeff]
  exact mul_le_mul (le_refl _)
    (mul_le_mul h1 h2 (norm_nonneg _) (pow_nonneg hK _))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)

/-- Entry bound for the second A-feature. -/
theorem norm_featA2_le (c : ℝ) (K : ℝ) (hK : 0 ≤ K)
    (X P₁ P₂ : Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ i j, ‖X i j‖ ≤ K) (hP₁ : ∀ i j, ‖P₁ i j‖ ≤ K)
    (hP₂ : ∀ i j, ‖P₂ i j‖ ≤ K) {n : ℕ}
    (α κ : Fin n → Fin d × Fin d) :
    ‖featA2 c α κ X P₁ P₂‖
      ≤ (|c| / 2) ^ n / (Nat.factorial n : ℝ) * (K ^ n * (K * K) ^ n) := by
  have h1 : ‖star (word α X)‖ ≤ K ^ n := by
    rw [norm_star]
    exact norm_word_le _ _ _ hX hK
  have h2 : ‖planeWord α κ P₁ P₂‖ ≤ (K * K) ^ n :=
    norm_planeWord_le _ _ _ _ _ hP₁ hP₂ hK
  have hnorm : ‖featA2 c α κ X P₁ P₂‖
      ≤ ‖((c / 2 : ℂ)) ^ n / (Nat.factorial n : ℂ)‖
        * (‖star (word α X)‖ * ‖planeWord α κ P₁ P₂‖) := by
    show ‖((c / 2 : ℂ)) ^ n / (Nat.factorial n : ℂ)
        * star (word α X) * planeWord α κ P₁ P₂‖ ≤ _
    refine (norm_mul_le _ _).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
  refine hnorm.trans ?_
  rw [norm_coeff]
  exact mul_le_mul (le_refl _)
    (mul_le_mul h1 h2 (norm_nonneg _) (pow_nonneg hK _))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)

/-- Entry bound for the first B-feature. -/
theorem norm_featB1_le (K : ℝ) (hK : 0 ≤ K)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : ∀ i j, ‖U i j‖ ≤ K)
    {n : ℕ} (κ : Fin n → Fin d × Fin d) :
    ‖featB1 κ U‖ ≤ K ^ n :=
  norm_word_le κ U K hU hK

/-- Entry bound for the second B-feature. -/
theorem norm_featB2_le (K : ℝ) (hK : 0 ≤ K)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : ∀ i j, ‖U i j‖ ≤ K)
    {n : ℕ} (κ : Fin n → Fin d × Fin d) :
    ‖featB2 κ U‖ ≤ K ^ n := by
  show ‖star (word κ U)‖ ≤ K ^ n
  rw [norm_star]
  exact norm_word_le κ U K hU hK

/-- The per-level domination constant of one factor. -/
noncomputable def wordLevel (c : ℝ) (K : ℝ) (n : ℕ) : ℝ :=
  (|c| / 2) ^ n / (Nat.factorial n : ℝ) * (K ^ 4) ^ n

/-- F2's `CA`: the A-side bound over two-plaquette indices —
coefficients, `X`-words, plane words. -/
noncomputable def wordCA (c : ℝ) (K : ℝ) (idx : WordIdx d) : ℝ :=
  ((|c| / 2) ^ idx.1.1 / (Nat.factorial idx.1.1 : ℝ)
      * (K ^ idx.1.1 * (K * K) ^ idx.1.1))
    * ((|c| / 2) ^ idx.2.1 / (Nat.factorial idx.2.1 : ℝ)
      * (K ^ idx.2.1 * (K * K) ^ idx.2.1))

/-- F2's `CB`: the B-side bound — the `U`-words. -/
def wordCB (K : ℝ) (idx : WordIdx d) : ℝ :=
  K ^ idx.1.1 * K ^ idx.2.1

/-- The A-feature bound, in the criterion's shape. -/
theorem norm_featA_le (c : ℝ) (K : ℝ) (hK : 0 ≤ K)
    (X P₁ P₂ : Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ i j, ‖X i j‖ ≤ K) (hP₁ : ∀ i j, ‖P₁ i j‖ ≤ K)
    (hP₂ : ∀ i j, ‖P₂ i j‖ ≤ K) (idx : WordIdx d) :
    ‖featA c idx X P₁ P₂‖ ≤ wordCA c K idx := by
  show ‖featA1 c idx.1.2.1 idx.1.2.2 X P₁ P₂
        * featA2 c idx.2.2.1 idx.2.2.2 X P₁ P₂‖
      ≤ ((|c| / 2) ^ idx.1.1 / (Nat.factorial idx.1.1 : ℝ)
          * (K ^ idx.1.1 * (K * K) ^ idx.1.1))
        * ((|c| / 2) ^ idx.2.1 / (Nat.factorial idx.2.1 : ℝ)
          * (K ^ idx.2.1 * (K * K) ^ idx.2.1))
  refine (norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _)
    (le_trans (norm_nonneg _)
      (norm_featA1_le c K hK X P₁ P₂ hX hP₁ hP₂ idx.1.2.1 idx.1.2.2)))
  · exact norm_featA1_le c K hK X P₁ P₂ hX hP₁ hP₂ idx.1.2.1 idx.1.2.2
  · exact norm_featA2_le c K hK X P₁ P₂ hX hP₁ hP₂ idx.2.2.1 idx.2.2.2

/-- The B-feature bound, in the criterion's shape (the
criterion applies `star` to its B-feature; `star` preserves
the norm). -/
theorem norm_featB_le (K : ℝ) (hK : 0 ≤ K)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : ∀ i j, ‖U i j‖ ≤ K)
    (idx : WordIdx d) :
    ‖star (featB idx U)‖ ≤ wordCB K idx := by
  show ‖star (featB1 idx.1.2.2 U * featB2 idx.2.2.2 U)‖
      ≤ K ^ idx.1.1 * K ^ idx.2.1
  rw [norm_star]
  refine (norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _)
    (le_trans (norm_nonneg _) (norm_featB1_le K hK U hU idx.1.2.2)))
  · exact norm_featB1_le K hK U hU idx.1.2.2
  · exact norm_featB2_le K hK U hU idx.2.2.2

/-- The level-bound family over `PlaqIdx` is summable. -/
theorem summable_wordLevel (c : ℝ) (K : ℝ) (hK : 0 ≤ K) :
    Summable fun i₁ : PlaqIdx d => wordLevel c K i₁.1 := by
  refine (summable_sigma_of_nonneg (fun i₁ => ?_)).mpr
    ⟨fun n => (hasSum_fintype _).summable, ?_⟩
  · simp only [wordLevel]
    positivity
  · refine Summable.congr (summable_factor_bound (d := d) c K hK) fun n => ?_
    simp only [wordLevel]
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      card_plaqIdx_fiber]

/-- The product of the two factor level bounds is summable
over two-plaquette indices. -/
theorem summable_prod_wordLevel (c : ℝ) (K : ℝ) (hK : 0 ≤ K) :
    Summable fun idx : WordIdx d =>
      wordLevel c K idx.1.1 * wordLevel c K idx.2.1 := by
  refine (summable_prod_of_nonneg (f := fun idx : WordIdx d =>
    wordLevel c K idx.1.1 * wordLevel c K idx.2.1)
    (fun idx => by simp only [wordLevel]; positivity)).mpr
    ⟨fun x => ?_, ?_⟩
  · exact (summable_wordLevel c K hK).mul_left (wordLevel c K x.1)
  · refine Summable.congr ((summable_wordLevel c K hK).mul_left
      (∑' i₁ : PlaqIdx d, wordLevel c K i₁.1)) fun x => ?_
    show (∑' i₁ : PlaqIdx d, wordLevel c K i₁.1) * wordLevel c K x.1
      = ∑' y : PlaqIdx d, wordLevel c K x.1 * wordLevel c K y.1
    rw [tsum_mul_left, mul_comm]

/-- The regrouping identity: `CA · CB` is the product of the
two factor level bounds. -/
theorem wordCA_mul_wordCB (c : ℝ) (K : ℝ) (idx : WordIdx d) :
    wordCA c K idx * wordCB K idx
      = wordLevel c K idx.1.1 * wordLevel c K idx.2.1 := by
  simp only [wordCA, wordCB, wordLevel]
  rw [mul_pow, mul_pow, ← pow_four K idx.1.1, ← pow_four K idx.2.1]
  ring

/-- The criterion's summability hypothesis, discharged:
`Summable fun idx => wordCA c K idx * wordCB K idx`. -/
theorem summable_wordCA_mul (c : ℝ) (K : ℝ) (hK : 0 ≤ K) :
    Summable fun idx : WordIdx d => wordCA c K idx * wordCB K idx :=
  Summable.congr (summable_prod_wordLevel c K hK)
    fun idx => (wordCA_mul_wordCB c K idx).symm

/-- The product of the two ℂ factor families is summable —
the side condition `HasSum.mul` requires for §8. -/
theorem summable_factor_prod (c : ℝ) (K : ℝ) (hK : 0 ≤ K)
    (X P₁ P₂ U : Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ i j, ‖X i j‖ ≤ K) (hP₁ : ∀ i j, ‖P₁ i j‖ ≤ K)
    (hP₂ : ∀ i j, ‖P₂ i j‖ ≤ K) (hU : ∀ i j, ‖U i j‖ ≤ K) :
    Summable fun idx : WordIdx d =>
      (star (featB1 idx.1.2.2 U) * featA1 c idx.1.2.1 idx.1.2.2 X P₁ P₂)
        * (star (featB2 idx.2.2.2 U)
          * featA2 c idx.2.2.1 idx.2.2.2 X P₁ P₂) := by
  refine Summable.of_norm_bounded (summable_prod_wordLevel c K hK)
    (fun idx => ?_)
  rw [norm_mul]
  exact mul_le_mul (norm_factor_one_le c K hK X P₁ P₂ U hX hP₁ hP₂ hU idx.1)
    (norm_factor_two_le c K hK X P₁ P₂ U hX hP₁ hP₂ hU idx.2)
    (norm_nonneg _)
    (le_trans (norm_nonneg _)
      (norm_factor_one_le c K hK X P₁ P₂ U hX hP₁ hP₂ hU idx.1))

/-! ## §8. The headline factorization -/

/-- **The single-plaquette word factorization** (charter §2;
brick F1 headline).  For abstract matrices `X P₁ P₂ U` whose
entries are bounded by `K` (the entry bounds enter only
through the summability side conditions — the identity is
finite tensor algebra plus the exponential series),

`exp (c · Re ⟨X, P₁ * U * P₂⟩_HS)`

is the sum over two-plaquette word indices of
`conj (B-feature) · (A-feature)`, the two factors of the
`Re`-split each carrying the SAME entry path on both sides of
their pairing.  At the application, `X = ρ(y)`,
`P₁ * U * P₂ = ρ(τ⁻¹) * ρ(u) * ρ(τ′) = ρ(τ⁻¹ u τ′)`,
`c = β / d`, and entry bound `K = 1` (unitary entries). -/
theorem exp_re_hsInner_word (c : ℝ) (K : ℝ) (hK : 0 ≤ K)
    (X P₁ P₂ U : Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ i j, ‖X i j‖ ≤ K) (hP₁ : ∀ i j, ‖P₁ i j‖ ≤ K)
    (hP₂ : ∀ i j, ‖P₂ i j‖ ≤ K) (hU : ∀ i j, ‖U i j‖ ≤ K) :
    Complex.exp ((c : ℂ) * ((hsInner X (P₁ * U * P₂)).re : ℂ))
      = ∑' idx : WordIdx d, star (featB idx U) * featA c idx X P₁ P₂ := by
  have h1 := hasSum_factor_one c K hK X P₁ P₂ U hX hP₁ hP₂ hU
  have h2 := hasSum_factor_two c K hK X P₁ P₂ U hX hP₁ hP₂ hU
  have hmul := h1.mul h2 (summable_factor_prod c K hK X P₁ P₂ U hX hP₁ hP₂ hU)
  have htsum : (∑' idx : WordIdx d, star (featB idx U) * featA c idx X P₁ P₂)
      = Complex.exp ((c / 2 : ℂ) * hsInner (P₁ * U * P₂) X)
        * Complex.exp ((c / 2 : ℂ) * hsInner X (P₁ * U * P₂)) := by
    rw [← hmul.tsum_eq]
    refine tsum_congr fun idx => ?_
    simp only [featB, featA, featB1, featB2, star_mul, star_star]
    ring
  rw [htsum, ← Complex.exp_add]
  congr 1
  have hs : hsInner (P₁ * U * P₂) X = star (hsInner X (P₁ * U * P₂)) :=
    (star_hsInner X (P₁ * U * P₂)).symm
  rw [hs, ofReal_re]
  ring

/-! ## §9. The d = 1 control (the charter's K-F1(b) guard) -/

/-- The entries of a circle representation matrix have norm
`1` (the `K = 1` entry bound at `d = 1`). -/
theorem norm_repMatrix_circleRep_entry (z : Circle) (i j : Fin 1) :
    ‖repMatrix circleRep z i j‖ ≤ 1 := by
  have hnorm : ‖repMatrix circleRep z i j‖ = 1 := by
    rw [repMatrix_circleRep]
    simp only [Matrix.of_apply, Circle.norm_coe]
  exact le_of_eq hnorm

/-- **The d = 1 control.**  At `d = 1`, for the corpus's
circle representation, the word series of §8 resums to Route
C's landed `fourier_exp_circle`: both sides are
`exp (β · Re s)` at `s = y⁻¹ * (τ⁻¹ * u * τ')`.  This is the
guard against the pre-registered kill K-F1(b): the word
factorization, specialized to the case Route C discharged by
Fourier analysis, returns the Bessel–Fourier series. -/
theorem word_tsum_circle (β : ℝ) (y u τ τ' : Circle) :
    (∑' idx : WordIdx 1, star (featB idx (repMatrix circleRep u))
        * featA β idx (repMatrix circleRep y)
          (repMatrix circleRep τ⁻¹) (repMatrix circleRep τ'))
      = ∑' k : ℤ, (besselI β k : ℂ)
          * ((y⁻¹ * (τ⁻¹ * u * τ') : Circle) : ℂ) ^ k := by
  have hb : ∀ z : Circle, ∀ i j : Fin 1,
      ‖repMatrix circleRep z i j‖ ≤ 1 :=
    fun z => norm_repMatrix_circleRep_entry z
  have h := exp_re_hsInner_word (d := 1) β 1 zero_le_one
    (repMatrix circleRep y) (repMatrix circleRep τ⁻¹)
    (repMatrix circleRep τ') (repMatrix circleRep u)
    (hb y) (hb τ⁻¹) (hb τ') (hb u)
  rw [← h]
  have hmul : repMatrix circleRep τ⁻¹ * repMatrix circleRep u
        * repMatrix circleRep τ'
      = repMatrix circleRep (τ⁻¹ * u * τ') := by
    rw [← repMatrix_mul, ← repMatrix_mul]
  have hstar : star ((y : ℂ)) = ((y⁻¹ : Circle) : ℂ) := by
    have h1 : star ((y : ℂ)) = (starRingEnd ℂ) ((y : ℂ)) :=
      congrFun Complex.star_def _
    rw [h1, ← Circle.coe_inv_eq_conj]
  have hhs : hsInner (repMatrix circleRep y)
        (repMatrix circleRep (τ⁻¹ * u * τ'))
      = ((y⁻¹ * (τ⁻¹ * u * τ') : Circle) : ℂ) := by
    show (∑ i : Fin 1, ∑ j : Fin 1,
        star (repMatrix circleRep y i j)
          * repMatrix circleRep (τ⁻¹ * u * τ') i j) = _
    simp only [Fin.sum_univ_one, repMatrix_circleRep, Matrix.of_apply,
      hstar]
    exact (Circle.coe_mul _ _).symm
  rw [hmul, hhs, ← fourier_exp_circle, Complex.ofReal_exp,
    Complex.ofReal_mul]
