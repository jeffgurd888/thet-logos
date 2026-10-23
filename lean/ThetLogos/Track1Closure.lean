import Mathlib.Tactic
import ThetLogos.PreOptionARepresentation

open Matrix Complex

namespace ThetLogos.Track1Closure

open ThetLogos.PreOptionARepresentation (pi0 afMul afStar afOne afZero sameBlock
  pi0_afMul pi0_one pi0_zero pi0_afStar pi0_ker_iff pi0_grading_even
  pi0_order_zero_fails pi0_entry_leptonL pi0_entry_leptonLc pi0_entry_eR
  pi0_entry_eRc pi0_entry_eq_zero_of_not_sameBlock pi0_support_sector
  gammaF_diag_eq_of_same_sector sum_eq_of_vanish_outside piOp_apply)

/-!
# ThetLogos.Track1Closure — π₀ against its own opposite

STATUS: LANDED 2026-10-23 by parent review — targeted in-tree build
green on the shipped text, strict recount, placeholder census,
`#print axioms` standard-only on the headline declarations.
VERDICT: T1 STANDS; T2 KILLED; T3 KILLED; Track 1 does NOT close
via Route A, and per K-TC3 the loud statement does not fire.
Commissioned by Jeff, 2026-10-23 00:45 EDT ("let's finish the
Standard model"), as the attack on the loud-statement trigger he
fixed the same night: **Track 1 closes** iff one representation
carries faithfulness + hypercharge ratios + the spectral-triple
compatibilities together at T1. Charter:
`whitepaper/track1-closure-scoping-2026-10-23.md`; dossier:
`whitepaper/track1-closure-2026-10-23.md`.

## NO CLAIM

NO CLAIM beyond the finite statements proved below. In particular
no claim about any continuum Standard Model, any manifold factor,
or any Millennium statement. Fences K-TC1 (finite only) and K-TC2
(inputs stay inputs: the hypercharge table is T2-cited, triplication
/ masses / couplings untouched) are on the face of every section.

## The one identification this brick turns on

The corpus's real structure is the matrix `UJ` of `Scaffold32`
(the partner-involution permutation), and the corpus's opposite
construction is the **matrix-level** combinator of
`FiniteSpectralTriple`,

    `piOp M = UJ * Mᵀ * UJ`,

which applies to *any* represented operator `M` — it is not tied to
Option A's `π`. Since `(Mᴴ).map star = Mᵀ` (proved below as
`conjTranspose_map_star`), the combinator is exactly the charter's
formula `J ρ(a)⋆ J⁻¹` in the corpus's terms: `J` acts on an operator
`X` by `UJ * X.map star * UJ` (the same form as the landed
`buildDirac_J_compat`), and `ρ(a)⋆` is the adjoint `(pi0 a)ᴴ`.
So π₀'s **own** opposite representation, built from the landed `J`,
is `rho0 := piOp ∘ pi0` — defined in §0 and identified with the
charter formula in §1 (`rho0_eq_J_conj`).

Consequence, stated at full rank: the order-zero test for the pair
(π₀, ρ°) is the test the landed module already ran in §7 of
`PreOptionARepresentation` — against `piOp (pi0 b)`, this same
combinator applied to π₀'s own image — and it **failed**, with the
explicit counterexample `(0,1)`-entry `I` vs `-I`
(`pi0_order_zero_fails`). This module does not re-run a different
pairing under a new name. It (i) constructs ρ° and proves its
opposite-representation laws (T1), (ii) restates the order-zero
kill in ρ° notation with the witness entries computed against ρ°
directly (T2), (iii) settles first-order for the pair against the
landed finite Dirac `DF_oneGen` — it also **fails**, with an exact
entry identity (T3), and (iv) assembles the package verdict (T4):
**Track 1 does NOT close via Route A.** Any closure must come
through Route B (a different seat assignment / modified opposite /
enlarged space), which this charter does not commission.

## Verdicts on the pre-registered targets

* **T1 — STANDS.** `rho0` is constructed from the landed `J`
  (`rho0 := piOp ∘ pi0`); the opposite-product law
  `rho0 (afMul a b) = rho0 b * rho0 a` (`rho0_afMul`), the unit and
  zero laws, the J-form identification (`rho0_eq_J_conj`), the
  star-compatiblity (`rho0_afStar`), and grading-evenness
  (`rho0_grading_even`) are all proved. Species: multiplicative,
  opposite-order — the species the construction carries; additivity
  is not claimed (it is proved incompatible with the hypercharge
  seat, landed `additive_rep_u1_eL_trivial`, cited not re-proved).
* **T2 — KILLED.** Order-zero for the pair (π₀, ρ°) fails: the
  witnesses of the landed §7, with the `(0,1)` entries of the two
  products computed against ρ° itself: `I` (`order_zero_entry_left`)
  and `-I` (`order_zero_entry_right`). `order_zero_killed`,
  `order_zero_fails_universal`.
* **T3 — KILLED.** First-order for the pair against the landed
  finite Dirac `DF_oneGen` fails: for the same witnesses, the
  double commutator's `(0,9)` entry is **exactly**
  `-(1 + I) * (ye : ℂ)` for every choice of real Yukawas
  (`DF_first_order_entry_09`) — nonzero the moment `ye ≠ 0`.
  `first_order_killed`, `first_order_fails_universal`.
* **T4 — the package does NOT stand whole.** Everything on the
  representation side stands (T1 here; faithfulness, grading,
  hypercharge ratios landed), `DF_oneGen` is J-compatible
  (`DF_oneGen_J_compat`, from landed `buildDirac_J_compat`), but
  order-zero and first-order are both killed. Assembled in
  `track1_package_routeA`; the closure negation is
  `track1_not_closed_routeA`. Per K-TC3, the loud statement does
  not fire.

Tier map: every theorem below is T1 (proved here, standard axioms
only) over the landed T1 results it cites; the hypercharge table
entering the cited `pi0_hypercharge_pattern` remains T2 (input,
cited — K-TC2). The verdicts "KILLED" are T1 negative results,
reported at the same rank as the positive ones.
-/

/-! ## §0. The opposite representation and the witnesses -/

/-- **π₀'s own opposite representation**: the corpus's J-conjugation
combinator `piOp` applied to π₀'s own image. In the corpus's terms
this is `ρ°(b) = J (pi0 b)⋆ J⁻¹`; the identification is proved as
`rho0_eq_J_conj` in §1. -/
def rho0 (b : AF) : Matrix I32 I32 ℂ := piOp (pi0 b)

/-- The order-zero witnesses of landed §7, named: `a₀` is the pure
quaternion rotation `q = !![0, 1; -1, 0]`. -/
def witA : AF := ⟨0, !![0, 1; -1, 0], 0⟩

/-- The order-zero witnesses of landed §7, named: `b₀` is
`⟨1, !![I, 0; 0, -I], 0⟩`. -/
def witB : AF := ⟨1, !![Complex.I, 0; 0, -Complex.I], 0⟩

/-! ## §1. T1 — ρ° is a representation of the opposite algebra -/

/-- Entry form of ρ°: the partner-transposed entries of π₀. -/
theorem rho0_entry (b : AF) (i j : I32) :
    rho0 b i j = pi0 b (partner j) (partner i) :=
  piOp_apply _ _ _

/-- The corpus combinator `piOp` is anti-multiplicative on matrices:
it reverses products. (Entry proof; the sum reindexes by the partner
involution.) -/
theorem piOp_antimul (M N : Matrix I32 I32 ℂ) :
    piOp (M * N) = piOp N * piOp M := by
  ext i j
  simp only [piOp_apply, Matrix.mul_apply]
  exact Fintype.sum_bijective partner
    (Function.Involutive.bijective (fun i => partner_involutive i))
    (fun k => M (partner j) k * N k (partner i))
    (fun k => N (partner k) (partner i) * M (partner j) (partner k))
    (fun k => by
      show M (partner j) k * N k (partner i)
        = N (partner (partner k)) (partner i) * M (partner j) (partner (partner k))
      rw [partner_involutive]
      exact mul_comm _ _)

/-- **T1, opposite-product law**: ρ° reverses the componentwise
product of `AF` — a representation of the opposite algebra, in the
multiplicative species π₀ itself carries. -/
theorem rho0_afMul (a b : AF) : rho0 (afMul a b) = rho0 b * rho0 a := by
  unfold rho0
  rw [pi0_afMul, piOp_antimul]

/-- **T1, unit law.** -/
theorem rho0_one : rho0 afOne = 1 := by
  unfold rho0
  rw [pi0_one]
  show UJ * (1 : Matrix I32 I32 ℂ).transpose * UJ = 1
  rw [Matrix.transpose_one, Matrix.mul_one, UJ_mul_self]

/-- **T1, zero law.** -/
theorem rho0_zero : rho0 afZero = 0 := by
  unfold rho0
  rw [pi0_zero]
  show UJ * (0 : Matrix I32 I32 ℂ).transpose * UJ = 0
  simp [Matrix.transpose_zero]

/-- Auxiliary identity: entrywise conjugation of the adjoint is the
transpose. This is what identifies the corpus's `piOp` with the
charter's formula `J ρ⋆ J⁻¹`. -/
theorem conjTranspose_map_star (M : Matrix I32 I32 ℂ) :
    (Mᴴ).map (star : ℂ → ℂ) = Mᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply]

/-- **T1, the J-form identification**: ρ° is the J-conjugate of the
adjoint, `rho0 b = UJ * ((pi0 b)ᴴ).map star * UJ` — verbatim the
charter's `ρ°(a) = J ρ(a)⋆ J⁻¹` in the corpus's terms (compare the
J-action form in the landed `buildDirac_J_compat`). -/
theorem rho0_eq_J_conj (b : AF) :
    rho0 b = UJ * ((pi0 b)ᴴ.map (star : ℂ → ℂ)) * UJ := by
  rw [conjTranspose_map_star]
  rfl

/-- Auxiliary identity: the transpose of the adjoint is the
entrywise conjugate. -/
theorem conjTranspose_transpose_eq_map_star (M : Matrix I32 I32 ℂ) :
    (Mᴴ)ᵀ = M.map (star : ℂ → ℂ) := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]

/-- **T1, star-compatibility**: ρ° of the starred element is the
plain J-conjugate of π₀'s image. -/
theorem rho0_afStar (b : AF) :
    rho0 (afStar b) = UJ * (pi0 b).map (star : ℂ → ℂ) * UJ := by
  unfold rho0
  rw [pi0_afStar]
  show UJ * ((pi0 b)ᴴ).transpose * UJ = UJ * (pi0 b).map (star : ℂ → ℂ) * UJ
  rw [conjTranspose_transpose_eq_map_star]

/-- **T1/T4, grading**: ρ° is grading-even, like π₀. Entry proof:
the partner involution flips both grading eigenvalues
(`gammaF_partner_flip`), and π₀'s support lies inside the 8-sectors
(`pi0_support_sector`), so the two flips cancel. -/
theorem rho0_grading_even (b : AF) : gammaF * rho0 b = rho0 b * gammaF := by
  ext i j
  rw [gammaF_mul_apply, mul_gammaF_apply, rho0_entry]
  by_cases h : pi0 b (partner j) (partner i) = 0
  · rw [h, mul_zero, zero_mul]
  · have hsec : (partner j).val / 8 = (partner i).val / 8 :=
      pi0_support_sector h
    have hg : gammaF (partner j) (partner j) = gammaF (partner i) (partner i) :=
      gammaF_diag_eq_of_same_sector hsec
    rw [gammaF_partner_flip i, gammaF_partner_flip j] at hg
    have hgg : gammaF i i = gammaF j j := by simpa using hg.symm
    rw [hgg]
    exact mul_comm _ _

/-! ## §2. T2 — order-zero for the pair: KILLED

The witnesses are §7's. Every ρ° entry used below is computed from
`rho0_entry` and the landed π₀ entry lemmas — the kill is recomputed
against ρ° itself, not merely quoted. -/

theorem partner_mk0 : partner ⟨0, by omega⟩ = ⟨16, by omega⟩ := by
  apply Fin.ext
  simp [partner_val_eq]

theorem partner_mk1 : partner ⟨1, by omega⟩ = ⟨17, by omega⟩ := by
  apply Fin.ext
  simp [partner_val_eq]

theorem partner_mk9 : partner ⟨9, by omega⟩ = ⟨25, by omega⟩ := by
  apply Fin.ext
  simp [partner_val_eq]

/-- Partner value, lower half. -/
theorem partner_val_add (k : I32) (h : k.val < 16) :
    (partner k).val = k.val + 16 := by
  rw [partner_val_eq]
  split_ifs
  · rfl

/-- Partner value, upper half. -/
theorem partner_val_sub (k : I32) (h : ¬ k.val < 16) :
    (partner k).val = k.val - 16 := by
  rw [partner_val_eq]
  split_ifs
  · omega

/-- `star I = -I`, in the form the entry computations need. -/
theorem star_I : star (Complex.I : ℂ) = -Complex.I := by
  rw [← starRingEnd_apply, Complex.ext_iff]
  simp

/-- ρ° of the witness `b₀` at `(0,0)`: the antilepton copy of `q_b`'s
`(0,0)` entry, conjugated: `star 1 * star I = -I`. -/
theorem rho0_wit_00 :
    rho0 witB ⟨0, by omega⟩ ⟨0, by omega⟩ = -Complex.I := by
  show rho0 ⟨1, !![Complex.I, 0; 0, -Complex.I], 0⟩ ⟨0, by omega⟩ ⟨0, by omega⟩
    = -Complex.I
  rw [rho0_entry, partner_mk0]
  have hs16 : (⟨16 + (⟨0, by omega⟩ : Fin 2).val, by omega⟩ : I32)
      = ⟨16, by omega⟩ := Fin.ext rfl
  rw [← hs16, pi0_entry_leptonLc]
  simp [star_I]

/-- ρ° of the witness `b₀` at `(0,1)`: `star 1 * star (q_b 1 0) = 0`. -/
theorem rho0_wit_01 :
    rho0 witB ⟨0, by omega⟩ ⟨1, by omega⟩ = 0 := by
  show rho0 ⟨1, !![Complex.I, 0; 0, -Complex.I], 0⟩ ⟨0, by omega⟩ ⟨1, by omega⟩
    = 0
  rw [rho0_entry, partner_mk0, partner_mk1]
  have hs16 : (⟨16 + (⟨0, by omega⟩ : Fin 2).val, by omega⟩ : I32)
      = ⟨16, by omega⟩ := Fin.ext rfl
  have hs17 : (⟨16 + (⟨1, by omega⟩ : Fin 2).val, by omega⟩ : I32)
      = ⟨17, by omega⟩ := Fin.ext rfl
  rw [← hs17, ← hs16, pi0_entry_leptonLc]
  simp

/-- ρ° of the witness `b₀` at `(1,1)`: `star 1 * star (-I) = I`. -/
theorem rho0_wit_11 :
    rho0 witB ⟨1, by omega⟩ ⟨1, by omega⟩ = Complex.I := by
  show rho0 ⟨1, !![Complex.I, 0; 0, -Complex.I], 0⟩ ⟨1, by omega⟩ ⟨1, by omega⟩
    = Complex.I
  rw [rho0_entry, partner_mk1]
  have hs17 : (⟨16 + (⟨1, by omega⟩ : Fin 2).val, by omega⟩ : I32)
      = ⟨17, by omega⟩ := Fin.ext rfl
  rw [← hs17, pi0_entry_leptonLc]
  simp

/-- ρ° of the witness `b₀` at `(9,9)`: the `e_R^c` singlet entry,
`star 1 = 1`. -/
theorem rho0_wit_99 :
    rho0 witB ⟨9, by omega⟩ ⟨9, by omega⟩ = 1 := by
  show rho0 ⟨1, !![Complex.I, 0; 0, -Complex.I], 0⟩ ⟨9, by omega⟩ ⟨9, by omega⟩
    = 1
  rw [rho0_entry, partner_mk9, pi0_entry_eRc]
  simp

/-- Row-0 vanishing for ρ° of `b₀`: outside the lepton slots `{0, 1}`
the partner slot misses the antilepton block of π₀. -/
theorem rho0_wit_row0_vanish (k : I32)
    (hk : k ∉ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset I32)) :
    rho0 witB ⟨0, by omega⟩ k = 0 := by
  rw [rho0_entry, partner_mk0]
  apply pi0_entry_eq_zero_of_not_sameBlock
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  have hk0 : k.val ≠ 0 := fun h => hk.1 (Fin.ext h)
  have hk1 : k.val ≠ 1 := fun h => hk.2 (Fin.ext h)
  have h16v : (⟨16, by omega⟩ : I32).val = 16 := rfl
  by_cases h16 : k.val < 16
  · have hpk := partner_val_add k h16
    intro hs
    unfold sameBlock at hs
    omega
  · have hpk := partner_val_sub k h16
    intro hs
    unfold sameBlock at hs
    omega

/-- Column-9 vanishing for ρ° of `b₀`: the `e_R^c` row of π₀ is a
singleton block, met only from slot `9` itself. -/
theorem rho0_wit_col9_vanish (k : I32) (hk : k ≠ ⟨9, by omega⟩) :
    rho0 witB k ⟨9, by omega⟩ = 0 := by
  rw [rho0_entry, partner_mk9]
  apply pi0_entry_eq_zero_of_not_sameBlock
  have hk9 : k.val ≠ 9 := fun h => hk (Fin.ext h)
  have h25v : (⟨25, by omega⟩ : I32).val = 25 := rfl
  by_cases h16 : k.val < 16
  · have hpk := partner_val_add k h16
    intro hs
    unfold sameBlock at hs
    omega
  · have hpk := partner_val_sub k h16
    intro hs
    unfold sameBlock at hs
    omega

/-- π₀ of the witness `a₀` at `(0,0)`: `q_a 0 0 = 0`. -/
theorem pi0_witA_00 :
    pi0 witA ⟨0, by omega⟩ ⟨0, by omega⟩ = 0 := by
  show pi0 ⟨0, !![0, 1; -1, 0], 0⟩ ⟨0, by omega⟩ ⟨0, by omega⟩ = 0
  have hs0 : (⟨(⟨0, by omega⟩ : Fin 2).val, by omega⟩ : I32)
      = ⟨0, by omega⟩ := Fin.ext rfl
  rw [← hs0, pi0_entry_leptonL]
  simp

/-- π₀ of the witness `a₀` at `(0,1)`: `q_a 0 1 = 1`. -/
theorem pi0_witA_01 :
    pi0 witA ⟨0, by omega⟩ ⟨1, by omega⟩ = 1 := by
  show pi0 ⟨0, !![0, 1; -1, 0], 0⟩ ⟨0, by omega⟩ ⟨1, by omega⟩ = 1
  have hs0 : (⟨(⟨0, by omega⟩ : Fin 2).val, by omega⟩ : I32)
      = ⟨0, by omega⟩ := Fin.ext rfl
  have hs1 : (⟨(⟨1, by omega⟩ : Fin 2).val, by omega⟩ : I32)
      = ⟨1, by omega⟩ := Fin.ext rfl
  rw [← hs0, ← hs1, pi0_entry_leptonL]
  simp

/-- Row-0 vanishing for π₀ of `a₀` outside the lepton slots. -/
theorem pi0_witA_row0_vanish (k : I32)
    (hk : k ∉ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset I32)) :
    pi0 witA ⟨0, by omega⟩ k = 0 := by
  apply pi0_entry_eq_zero_of_not_sameBlock
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  have hk0 : k.val ≠ 0 := fun h => hk.1 (Fin.ext h)
  have hk1 : k.val ≠ 1 := fun h => hk.2 (Fin.ext h)
  have h0v : (⟨0, by omega⟩ : I32).val = 0 := rfl
  intro hs
  unfold sameBlock at hs
  omega

/-- **T2 kill, left entry**: `(pi0 a₀ * rho0 b₀) (0,1) = I`,
computed against ρ° itself. -/
theorem order_zero_entry_left :
    (pi0 witA * rho0 witB) ⟨0, by omega⟩ ⟨1, by omega⟩ = Complex.I := by
  have hvan : ∀ k : I32, k ∉ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset I32) →
      pi0 witA ⟨0, by omega⟩ k * rho0 witB k ⟨1, by omega⟩ = 0 := by
    intro k hk
    rw [pi0_witA_row0_vanish k hk, zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_pair (show (⟨0, by omega⟩ : I32) ≠ ⟨1, by omega⟩ by decide),
    pi0_witA_00, pi0_witA_01, rho0_wit_01, rho0_wit_11]
  simp

/-- **T2 kill, right entry**: `(rho0 b₀ * pi0 a₀) (0,1) = -I`,
computed against ρ° itself. -/
theorem order_zero_entry_right :
    (rho0 witB * pi0 witA) ⟨0, by omega⟩ ⟨1, by omega⟩ = -Complex.I := by
  have hvan : ∀ k : I32, k ∉ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset I32) →
      rho0 witB ⟨0, by omega⟩ k * pi0 witA k ⟨1, by omega⟩ = 0 := by
    intro k hk
    rw [rho0_wit_row0_vanish k hk, zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_pair (show (⟨0, by omega⟩ : I32) ≠ ⟨1, by omega⟩ by decide),
    rho0_wit_00, rho0_wit_01, pi0_witA_01]
  simp

/-- **T2 — KILLED.** Order-zero fails for the pair (π₀, ρ°): the two
products differ at the `(0,1)` entry, `I ≠ -I`. This is the landed
`pi0_order_zero_fails` restated for π₀'s own opposite — necessarily
the same test, by the §1 identification `rho0 = piOp ∘ pi0`. -/
theorem order_zero_killed :
    ∃ a b : AF, pi0 a * rho0 b ≠ rho0 b * pi0 a := by
  refine ⟨witA, witB, ?_⟩
  intro h
  have e : (pi0 witA * rho0 witB) ⟨0, by omega⟩ ⟨1, by omega⟩
      = (rho0 witB * pi0 witA) ⟨0, by omega⟩ ⟨1, by omega⟩ := by rw [h]
  rw [order_zero_entry_left, order_zero_entry_right] at e
  norm_num [Complex.ext_iff] at e

/-- **T2, universal form**: the order-zero sentence for the pair is
false. -/
theorem order_zero_fails_universal :
    ¬ ∀ a b : AF, pi0 a * rho0 b = rho0 b * pi0 a := by
  intro h
  obtain ⟨a, b, hne⟩ := order_zero_killed
  exact hne (h a b)

/-! ## §3. T3 — first-order against `DF_oneGen`: KILLED

`D_F` is the corpus's landed one-generation finite Dirac of
`FiniteSpectralTriple` (`DF_oneGen`, the companion of `J`/`piOp` in
that module). The double commutator for the §2 witnesses is
supported, at the `(0,9)` entry, on a single Yukawa: `ye`. -/

/-- The one `DF_oneGen` entry the kill turns on: the `(1,9)` entry is
the electron Yukawa. -/
theorem DF_oneGen_19 (ynu ye yu yd : ℝ) :
    DF_oneGen ynu ye yu yd ⟨1, by omega⟩ ⟨9, by omega⟩ = (ye : ℂ) := by
  have hDF : DF_oneGen ynu ye yu yd
      = buildDirac
        (Matrix.diagonal
          (![(ynu : ℂ), (ye : ℂ), (yu : ℂ), (yd : ℂ),
            (yu : ℂ), (yd : ℂ), (yu : ℂ), (yd : ℂ)] : Fin 8 → ℂ))
        ((Matrix.diagonal
          (![(ynu : ℂ), (ye : ℂ), (yu : ℂ), (yd : ℂ),
            (yu : ℂ), (yd : ℂ), (yu : ℂ), (yd : ℂ)] : Fin 8 → ℂ)).map
          (starRingEnd ℂ))
        0 0 := rfl
  rw [hDF]
  unfold buildDirac
  simp [Matrix.diagonal]

/-- The first commutator at `(0,9)`: `[DF, pi0 a₀] (0,9) = -(ye : ℂ)`.
Only the `l = 1` term survives: `pi0 a₀ (0,1) * DF (1,9) = 1 * ye`. -/
theorem DF_pi0_comm_09 (ynu ye yu yd : ℝ) :
    (DF_oneGen ynu ye yu yd * pi0 witA - pi0 witA * DF_oneGen ynu ye yu yd)
        ⟨0, by omega⟩ ⟨9, by omega⟩ = -(ye : ℂ) := by
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  have hsum1 : (∑ k, DF_oneGen ynu ye yu yd ⟨0, by omega⟩ k
      * pi0 witA k ⟨9, by omega⟩) = 0 := by
    have hvan : ∀ k : I32, k ∉ ({⟨9, by omega⟩} : Finset I32) →
        DF_oneGen ynu ye yu yd ⟨0, by omega⟩ k * pi0 witA k ⟨9, by omega⟩
        = 0 := by
      intro k hk
      simp only [Finset.mem_singleton] at hk
      have h0 : pi0 witA k ⟨9, by omega⟩ = 0 := by
        apply pi0_entry_eq_zero_of_not_sameBlock
        have hk9 : k.val ≠ 9 := fun h => hk (Fin.ext h)
        have h9v : (⟨9, by omega⟩ : I32).val = 9 := rfl
        intro hs
        unfold sameBlock at hs
        omega
      rw [h0, mul_zero]
    rw [sum_eq_of_vanish_outside hvan, Finset.sum_singleton]
    have e99 : pi0 witA ⟨9, by omega⟩ ⟨9, by omega⟩ = 0 := by
      show pi0 ⟨0, !![0, 1; -1, 0], 0⟩ ⟨9, by omega⟩ ⟨9, by omega⟩ = 0
      rw [pi0_entry_eR]
      simp
    rw [e99, mul_zero]
  have hsum2 : (∑ k, pi0 witA ⟨0, by omega⟩ k
      * DF_oneGen ynu ye yu yd k ⟨9, by omega⟩) = (ye : ℂ) := by
    have hvan : ∀ k : I32, k ∉ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset I32) →
        pi0 witA ⟨0, by omega⟩ k * DF_oneGen ynu ye yu yd k ⟨9, by omega⟩
        = 0 := by
      intro k hk
      rw [pi0_witA_row0_vanish k hk, zero_mul]
    rw [sum_eq_of_vanish_outside hvan,
      Finset.sum_pair (show (⟨0, by omega⟩ : I32) ≠ ⟨1, by omega⟩ by decide),
      pi0_witA_00, pi0_witA_01, DF_oneGen_19]
    simp
  rw [hsum1, hsum2, zero_sub]

/-- **T3 kill, exact entry identity**: for the §2 witnesses, the
double commutator's `(0,9)` entry against `DF_oneGen` is
`-(1 + I) * (ye : ℂ)` — for **every** choice of real Yukawas. -/
theorem DF_first_order_entry_09 (ynu ye yu yd : ℝ) :
    ((DF_oneGen ynu ye yu yd * pi0 witA - pi0 witA * DF_oneGen ynu ye yu yd)
        * rho0 witB
      - rho0 witB * (DF_oneGen ynu ye yu yd * pi0 witA
        - pi0 witA * DF_oneGen ynu ye yu yd))
        ⟨0, by omega⟩ ⟨9, by omega⟩ = -(1 + Complex.I) * (ye : ℂ) := by
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  have hsum1 : (∑ k, (DF_oneGen ynu ye yu yd * pi0 witA
        - pi0 witA * DF_oneGen ynu ye yu yd) ⟨0, by omega⟩ k
      * rho0 witB k ⟨9, by omega⟩) = -(ye : ℂ) := by
    have hvan : ∀ k : I32, k ∉ ({⟨9, by omega⟩} : Finset I32) →
        (DF_oneGen ynu ye yu yd * pi0 witA - pi0 witA * DF_oneGen ynu ye yu yd)
          ⟨0, by omega⟩ k * rho0 witB k ⟨9, by omega⟩ = 0 := by
      intro k hk
      simp only [Finset.mem_singleton] at hk
      rw [rho0_wit_col9_vanish k hk, mul_zero]
    rw [sum_eq_of_vanish_outside hvan, Finset.sum_singleton,
      DF_pi0_comm_09, rho0_wit_99, mul_one]
  have hsum2 : (∑ k, rho0 witB ⟨0, by omega⟩ k
      * (DF_oneGen ynu ye yu yd * pi0 witA - pi0 witA * DF_oneGen ynu ye yu yd)
          k ⟨9, by omega⟩) = -Complex.I * -(ye : ℂ) := by
    have hvan : ∀ k : I32, k ∉ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset I32) →
        rho0 witB ⟨0, by omega⟩ k
          * (DF_oneGen ynu ye yu yd * pi0 witA
            - pi0 witA * DF_oneGen ynu ye yu yd) k ⟨9, by omega⟩ = 0 := by
      intro k hk
      rw [rho0_wit_row0_vanish k hk, zero_mul]
    rw [sum_eq_of_vanish_outside hvan,
      Finset.sum_pair (show (⟨0, by omega⟩ : I32) ≠ ⟨1, by omega⟩ by decide),
      rho0_wit_00, rho0_wit_01, DF_pi0_comm_09, zero_mul, add_zero]
  rw [hsum1, hsum2]
  ring

/-- **T3 — KILLED.** First-order for the pair (π₀, ρ°) against the
landed `DF_oneGen` fails: at `ye = 1` the double commutator's
`(0,9)` entry is `-(1 + I) ≠ 0`. -/
theorem first_order_killed :
    ∃ (ynu ye yu yd : ℝ) (a b : AF),
      (DF_oneGen ynu ye yu yd * pi0 a - pi0 a * DF_oneGen ynu ye yu yd)
          * rho0 b
        - rho0 b * (DF_oneGen ynu ye yu yd * pi0 a
          - pi0 a * DF_oneGen ynu ye yu yd) ≠ 0 := by
  refine ⟨0, 1, 0, 0, witA, witB, ?_⟩
  intro h
  have e := congrFun (congrFun h ⟨0, by omega⟩) ⟨9, by omega⟩
  rw [DF_first_order_entry_09] at e
  simp only [Matrix.zero_apply] at e
  norm_num [Complex.ext_iff] at e

/-- **T3, universal form**: the first-order sentence for the pair
against `DF_oneGen` is false. -/
theorem first_order_fails_universal :
    ¬ ∀ (ynu ye yu yd : ℝ) (a b : AF),
      (DF_oneGen ynu ye yu yd * pi0 a - pi0 a * DF_oneGen ynu ye yu yd)
          * rho0 b
        - rho0 b * (DF_oneGen ynu ye yu yd * pi0 a
          - pi0 a * DF_oneGen ynu ye yu yd) = 0 := by
  intro h
  obtain ⟨ynu, ye, yu, yd, a, b, hne⟩ := first_order_killed
  exact hne (h ynu ye yu yd a b)

/-! ## §4. T4 — the package verdict

What stands, assembled; what is killed, at the same rank. The landed
π₀ results are cited unmodified (K-TC4): `pi0_afMul`, `pi0_one`,
`pi0_ker_iff`, `pi0_grading_even` from `PreOptionARepresentation`;
`buildDirac_J_compat` from `FiniteSpectralTriple`. -/

/-- J-compatibility of the landed Dirac: `DF_oneGen` satisfies the
hypotheses of the landed `buildDirac_J_compat` (`B = Ā`, `C = E = 0`,
both transpose-symmetric), so `J D_F J⁻¹`-form conjugation fixes it. -/
theorem DF_oneGen_J_compat (ynu ye yu yd : ℝ) :
    UJ * (DF_oneGen ynu ye yu yd).map (star : ℂ → ℂ) * UJ
      = DF_oneGen ynu ye yu yd := by
  have hDF : DF_oneGen ynu ye yu yd
      = buildDirac
        (Matrix.diagonal
          (![(ynu : ℂ), (ye : ℂ), (yu : ℂ), (yd : ℂ),
            (yu : ℂ), (yd : ℂ), (yu : ℂ), (yd : ℂ)] : Fin 8 → ℂ))
        ((Matrix.diagonal
          (![(ynu : ℂ), (ye : ℂ), (yu : ℂ), (yd : ℂ),
            (yu : ℂ), (yd : ℂ), (yu : ℂ), (yd : ℂ)] : Fin 8 → ℂ)).map
          (starRingEnd ℂ))
        0 0 := rfl
  rw [hDF]
  exact buildDirac_J_compat _ _ _ _ rfl (by simp) (by simp)

/-- The landed π₀ package, assembled (citations, unmodified):
multiplicative, unital, faithful, grading-even. Together with the
landed `pi0_det_unimodular` / `pi0_hypercharge_pattern` (hypercharge
ratios, T2 table cited), these are the representation-side contents
of Track 1 that stand. -/
theorem pi0_landed_package :
    (∀ a b : AF, pi0 (afMul a b) = pi0 a * pi0 b) ∧
    pi0 afOne = 1 ∧
    (∀ a : AF, pi0 a = 0 → a = afZero) ∧
    (∀ a : AF, gammaF * pi0 a = pi0 a * gammaF) :=
  ⟨pi0_afMul, pi0_one, fun a h => (pi0_ker_iff a).mp h, pi0_grading_even⟩

/-- **T4 assembly, Route A.** Everything the (π₀, ρ°) pair carries —
opposite-algebra laws, grading on both sides, J-identification,
J-compatibility of `DF_oneGen` — together with both kills. The
package does not stand whole: the last two components are the
obstructions. -/
theorem track1_package_routeA :
    (∀ a b : AF, rho0 (afMul a b) = rho0 b * rho0 a) ∧
    rho0 afOne = 1 ∧
    (∀ b : AF, gammaF * rho0 b = rho0 b * gammaF) ∧
    (∀ b : AF, rho0 b = UJ * ((pi0 b)ᴴ.map (star : ℂ → ℂ)) * UJ) ∧
    (∀ (ynu ye yu yd : ℝ),
      UJ * (DF_oneGen ynu ye yu yd).map (star : ℂ → ℂ) * UJ
        = DF_oneGen ynu ye yu yd) ∧
    (∃ a b : AF, pi0 a * rho0 b ≠ rho0 b * pi0 a) ∧
    (∃ (ynu ye yu yd : ℝ) (a b : AF),
      (DF_oneGen ynu ye yu yd * pi0 a - pi0 a * DF_oneGen ynu ye yu yd)
          * rho0 b
        - rho0 b * (DF_oneGen ynu ye yu yd * pi0 a
          - pi0 a * DF_oneGen ynu ye yu yd) ≠ 0) :=
  ⟨rho0_afMul, rho0_one, rho0_grading_even, rho0_eq_J_conj,
    DF_oneGen_J_compat, order_zero_killed, first_order_killed⟩

/-- **T4 verdict**: Track 1 does **not** close via Route A — the
conjunction "order-zero ∧ first-order for the pair (π₀, ρ°)" is
false. Per K-TC3 the loud statement does not fire; per the charter,
Route B (a different seat assignment, a modified opposite
construction, or an enlarged finite space) requires a new charter,
scoped from these counterexamples. -/
theorem track1_not_closed_routeA :
    ¬ ((∀ a b : AF, pi0 a * rho0 b = rho0 b * pi0 a) ∧
      (∀ (ynu ye yu yd : ℝ) (a b : AF),
        (DF_oneGen ynu ye yu yd * pi0 a - pi0 a * DF_oneGen ynu ye yu yd)
            * rho0 b
          - rho0 b * (DF_oneGen ynu ye yu yd * pi0 a
            - pi0 a * DF_oneGen ynu ye yu yd) = 0)) := by
  rintro ⟨h0, -⟩
  obtain ⟨a, b, hne⟩ := order_zero_killed
  exact hne (h0 a b)

end ThetLogos.Track1Closure
