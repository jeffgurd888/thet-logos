import Mathlib.Tactic
import ThetLogos.Track1Closure

open Matrix Complex

namespace ThetLogos.Track1RouteB

open ThetLogos.PreOptionARepresentation (pi0 afMul afAdd afStar afOne afZero
  afMul_u1 afMul_q afMul_color afAdd_u1 afAdd_q afAdd_color
  afStar_u1 afStar_q afStar_color fin2_mk0 fin2_mk1 fin3_mk0 fin3_mk1 fin3_mk2
  not_sameBlock_of_ne_sector not_sameBlock_of_HL_mixed
  not_sameBlock_of_HR_mixed not_sameBlock_of_Hc_mixed
  sameBlock_symm sameBlock_trans
  sameBlock pi0_entry_leptonL pi0_entry_quarkL pi0_entry_nuR
  pi0_entry_eR pi0_entry_quarkR pi0_entry_leptonLc pi0_entry_quarkLc
  pi0_entry_nuRc pi0_entry_eRc pi0_entry_quarkRc
  pi0_entry_eq_zero_of_not_sameBlock piOp_diagonal eq_diagonal_of_entry
  mul_entry_eq_zero sum_eq_of_vanish_outside
  afZero_u1 afZero_q afZero_color afOne_u1 afOne_q afOne_color
  gammaF_diag_eq_of_same_sector piOp_apply)
open ThetLogos.Track1Closure (rho0 witA witB rho0_wit_00 rho0_entry
  piOp_antimul conjTranspose_map_star DF_oneGen_J_compat star_I
  partner_mk0 partner_mk1 partner_mk9)

/-!
# ThetLogos.Track1RouteB — Track 1, Route B: summand-pure antiparticles

STATUS: LANDED 2026-10-23 by parent review — targeted in-tree build
green on the shipped text, strict recount (273), placeholder census
(zero placeholders), `#print axioms` standard-only on all fourteen headline
declarations. VERDICT: T0–T6 ALL STAND — **TRACK 1 CLOSES via
Route B**: π₁, the summand-pure representation, carries
faithfulness + the hypercharge ratios (surviving unimodular
direction (3, −1), normalization 3) + the full spectral-triple
compatibilities together at T1, as a full unital *-algebra
representation. The loud-statement trigger fixed by Jeff
2026-10-23 00:43 EDT is met; the statement fires with NO CLAIM at
the same volume (K-RB3). Charter:
`whitepaper/track1-routeb-scoping-2026-10-23.md`; dossier:
`whitepaper/track1-routeb-2026-10-23.md`.

## NO CLAIM

NO CLAIM beyond the finite statements proved below. In particular
no claim about any continuum Standard Model, any manifold factor,
or any Millennium statement.

## Why this brick exists

The landed `π₀` (`ThetLogos.PreOptionARepresentation`) is faithful
and carries the exact hypercharge ratios under unimodularity, but
`ThetLogos.Track1Closure` KILLED order-zero and first-order for
`(π₀, ρ°)` — ρ° its own `J`-opposite — with the defect entry
`[[DF_oneGen, π₀ a₀], ρ° b₀](0,9) = −(1+I)·ye`. The defect anatomy
(§2 below) points at π₀'s BOLTED antiparticle blocks: the
antilepton block multiplies two summands' actions on the same
slots (`star λ * star (q s t)`), and the left-antiquark block is
the full tensor product `star (q s t) * m k l`. Route B changes
the CONSTRUCTION so the kills' hypotheses no longer apply, then
re-earns every verdict. Renaming or narrowing is not a fix
(charter K-RB4).

## The π₀ → π₁ change list (complete; §0 is the definition)

Particle sectors are UNCHANGED, entry by entry (proved in §2,
`pi1_eq_pi0_of_lt16`). Exactly three antiparticle branches change:

1. **Antilepton block** (slots 16, 17):
   `star a.u1 * star (a.q s t)` ↦ `if s = t then star a.u1 else 0`
   — the ℂ-summand's pure conjugate action `λ̄ • I₂`; the bolted
   ℍ factor is dropped. Reason: ρ₁° seats this block's transpose
   on the lepton doublet, where π₁(a) = q_a has commutant the
   scalars only; the dressed conjugate `λ̄ • q̄` was the Route A
   order-zero kill's mechanism at entry (0,0)/(0,1).
2. **Left antiquark block** (slots 18–23):
   `star (a.q s t) * a.color k l` ↦
   `if s = t then star (a.color k l) else 0`
   — the M₃-summand's pure conjugate action, flavour-diagonal;
   the bolted q̄ factor is dropped. Reason: ρ₁° seats its
   transpose on the left quark block, where it must lie in the
   commutant of `{q ⊗ I₃}`, namely `I₂ ⊗ M₃(ℂ)` (flavour-scalar
   in the doublet index); `q̄ ⊗ m` transposed mixes flavours.
3. **Right antiquark block** (slots 26–31):
   `if s = t then a.color k l else 0` ↦
   `if s = t then star (a.color k l) else 0`
   — same flavour-diagonal shape, colour conjugated: the
   summand-pure conjugate action, matching blocks 1–2. Reason:
   with one antiquark block conjugated and the other not, the
   determinant weights of colour cancel (+6/−6) and
   unimodularity forces the ℂ weight to 0, killing the lift
   (§9: the colour weight sum is −12, not +12).

## Fences

- K-RB1: finite only. `DF_oneGen` is NOT edited; if its texture
  obstructs a target, that is proved and reported as a finding.
- K-RB2: inputs stay inputs. The hypercharge table is T2-cited
  from `ThetLogos.SMFermions` (as in the landed π₀ module);
  triplication, masses, couplings untouched. Landed files are
  unmodified; π₀ and Route A keep their dossiers exactly.
- K-RB3: the loud statement fires only if the package verdict
  (T6, §10) stands whole.
- K-RB4: no silent narrowing. Any weakening of a target is this
  module's headline, not a footnote.

## Verdicts (charter targets T0–T6)

- T0 (defect anatomy): STANDS, §2 (proved as block-level
  entry identities against the landed Route A defect formulae).
- T1 (π₁ and its species): STANDS, §§3–4 — π₁ is a FULL unital
  `*`-algebra representation of `AF` (multiplicativity,
  ADDITIVITY, star, zero, one) and is grading-even (§6). The
  species is exact: additivity, which π₀ provably could not
  carry with its bolted antiparticle blocks, holds for π₁.
- T2 (faithfulness): STANDS, §5 (`pi1_ker_iff`, `pi1_injective`).
- T3 (hypercharge lift re-derived): STANDS, §9. HEADLINE: the
  surviving unimodular direction is `(α, β) = (3, −1)`, not
  π₀'s `(3, 1)`; the normalisation `3` is unchanged and all
  eight lifted weights are exactly `3 · Y_f`.
- T4 (order-zero for `(π₁, ρ₁°)`): STANDS, §7.
- T5 (first-order against the landed `DF_oneGen`): STANDS, §8.
- T6 (package): STANDS, §10 — Track 1 CLOSES via Route B.
-/

/-! ## §0. The Route B representation π₁ and its own opposite ρ₁°

`pi1` is `pi0`'s definition with exactly the three antiparticle
branch changes listed on the face. `rho1` is π₁'s own
`J`-opposite, by the same landed identification as Route A
(`Track1Closure.rho0_eq_J_conj`: `piOp` is the matrix-level
`J`-conjugate combinator). -/

/-- **The Route B representation** `pi1 : AF → Mat₃₂(ℂ)`.
Identical to `pi0` on the particle half; summand-pure conjugate
actions on the antiparticle half (see the change list). -/
def pi1 (a : AF) : Matrix I32 I32 ℂ := fun i j =>
  let iv := i.val; let jv := j.val
  if hL : iv < 8 ∧ jv < 8 then
    if h_l : iv < 2 ∧ jv < 2 then
      a.q ⟨iv, by omega⟩ ⟨jv, by omega⟩
    else if h_q : 2 ≤ iv ∧ 2 ≤ jv then
      let iso_i : Fin 2 := ⟨(iv - 2) % 2, Nat.mod_lt _ (by norm_num)⟩
      let iso_j : Fin 2 := ⟨(jv - 2) % 2, Nat.mod_lt _ (by norm_num)⟩
      let col_i : Fin 3 := ⟨(iv - 2) / 2, by omega⟩
      let col_j : Fin 3 := ⟨(jv - 2) / 2, by omega⟩
      if col_i = col_j then a.q iso_i iso_j else 0
    else 0
  else if hR : 8 ≤ iv ∧ iv < 16 ∧ 8 ≤ jv ∧ jv < 16 then
    if h1 : iv = 8 ∧ jv = 8 then a.u1
    else if h2 : iv = 9 ∧ jv = 9 then star a.u1
    else if h_q : 10 ≤ iv ∧ 10 ≤ jv then
      let iso_i : Fin 2 := ⟨(iv - 10) % 2, Nat.mod_lt _ (by norm_num)⟩
      let iso_j : Fin 2 := ⟨(jv - 10) % 2, Nat.mod_lt _ (by norm_num)⟩
      let col_i : Fin 3 := ⟨(iv - 10) / 2, by omega⟩
      let col_j : Fin 3 := ⟨(jv - 10) / 2, by omega⟩
      if iso_i = iso_j ∧ col_i = col_j then
        (if iso_i = 0 then a.u1 else star a.u1)
      else 0
    else 0
  else if hLc : 16 ≤ iv ∧ iv < 24 ∧ 16 ≤ jv ∧ jv < 24 then
    if h_l : iv < 18 ∧ jv < 18 then
      if (⟨iv - 16, by omega⟩ : Fin 2) = ⟨jv - 16, by omega⟩
        then star a.u1 else 0
    else if h_q : 18 ≤ iv ∧ 18 ≤ jv then
      let iso_i : Fin 2 := ⟨(iv - 18) % 2, Nat.mod_lt _ (by norm_num)⟩
      let iso_j : Fin 2 := ⟨(jv - 18) % 2, Nat.mod_lt _ (by norm_num)⟩
      let col_i : Fin 3 := ⟨(iv - 18) / 2, by omega⟩
      let col_j : Fin 3 := ⟨(jv - 18) / 2, by omega⟩
      if iso_i = iso_j then star (a.color col_i col_j) else 0
    else 0
  else if hRc : 24 ≤ iv ∧ 24 ≤ jv then
    if h1 : iv = 24 ∧ jv = 24 then star a.u1
    else if h2 : iv = 25 ∧ jv = 25 then star a.u1
    else if h_q : 26 ≤ iv ∧ 26 ≤ jv then
      let iso_i : Fin 2 := ⟨(iv - 26) % 2, Nat.mod_lt _ (by norm_num)⟩
      let iso_j : Fin 2 := ⟨(jv - 26) % 2, Nat.mod_lt _ (by norm_num)⟩
      let col_i : Fin 3 := ⟨(iv - 26) / 2, by omega⟩
      let col_j : Fin 3 := ⟨(jv - 26) / 2, by omega⟩
      if iso_i = iso_j then star (a.color col_i col_j) else 0
    else 0
  else 0

/-- π₁'s own opposite representation: `rho1 := piOp ∘ pi1`,
the corpus's matrix-level `J`-conjugation applied to π₁'s image
(the same construction as Route A's `rho0`). -/
def rho1 (a : AF) : Matrix I32 I32 ℂ := piOp (pi1 a)

/-- Entries of the opposite: `rho1 b i j = pi1 b (partner j)
(partner i)`. -/
theorem rho1_entry (b : AF) (i j : I32) :
    rho1 b i j = pi1 b (partner j) (partner i) := piOp_apply _ _ _

/-! ## §1. Entry lemmas

The seven particle entries and the two antiparticle singlet
entries are π₀'s, verbatim in form (their proofs are the landed
proofs with the definition unfolded being `pi1` — the branches
they read are unchanged). The three changed blocks have their
own entry lemmas, proved the same way. Then the vanishing
lemmas, whose statements and proofs are definition-shape only
(they never inspect the changed leaf values). -/

theorem pi1_entry_leptonL (a : AF) (s t : Fin 2) :
    pi1 a ⟨s.val, by omega⟩ ⟨t.val, by omega⟩ = a.q s t := by
  have hL : s.val < 8 ∧ t.val < 8 := by omega
  have h_l : s.val < 2 ∧ t.val < 2 := by omega
  have hsi : (⟨s.val, by omega⟩ : Fin 2) = s := Fin.eta s _
  have hti : (⟨t.val, by omega⟩ : Fin 2) = t := Fin.eta t _
  unfold pi1
  dsimp only
  simp only [hL, h_l, true_and, and_true, dite_true, hsi, hti]

theorem pi1_entry_quarkL (a : AF) (k l : Fin 3) (s t : Fin 2) :
    pi1 a ⟨2 + 2 * k.val + s.val, by omega⟩ ⟨2 + 2 * l.val + t.val, by omega⟩
      = if k = l then a.q s t else 0 := by
  have hL : (2 + 2 * k.val + s.val) < 8 ∧ (2 + 2 * l.val + t.val) < 8 := by omega
  have hnl : ¬ ((2 + 2 * k.val + s.val) < 2 ∧ (2 + 2 * l.val + t.val) < 2) := by omega
  have hq : (2:ℕ) ≤ 2 + 2 * k.val + s.val ∧ (2:ℕ) ≤ 2 + 2 * l.val + t.val := by omega
  have hmod1 : (2 + 2 * k.val + s.val - 2) % 2 = s.val := by omega
  have hmod2 : (2 + 2 * l.val + t.val - 2) % 2 = t.val := by omega
  have hdiv1 : (2 + 2 * k.val + s.val - 2) / 2 = k.val := by omega
  have hdiv2 : (2 + 2 * l.val + t.val - 2) / 2 = l.val := by omega
  have hsi : (⟨s.val, by omega⟩ : Fin 2) = s := Fin.eta s _
  have hti : (⟨t.val, by omega⟩ : Fin 2) = t := Fin.eta t _
  have hki : (⟨k.val, by omega⟩ : Fin 3) = k := Fin.eta k _
  have hli : (⟨l.val, by omega⟩ : Fin 3) = l := Fin.eta l _
  unfold pi1
  dsimp only
  simp only [hL, hnl, hq, true_and, and_true, dite_true, dite_false, hmod1, hmod2,
    hdiv1, hdiv2, hsi, hti, hki, hli, Fin.mk.injEq]

theorem pi1_entry_nuR (a : AF) : pi1 a ⟨8, by omega⟩ ⟨8, by omega⟩ = a.u1 := by
  have hnL : ¬ ((8:ℕ) < 8 ∧ (8:ℕ) < 8) := by omega
  have hR : 8 ≤ (8:ℕ) ∧ (8:ℕ) < 16 ∧ 8 ≤ (8:ℕ) ∧ (8:ℕ) < 16 := by omega
  have h1 : (8:ℕ) = 8 ∧ (8:ℕ) = 8 := by omega
  unfold pi1
  dsimp only
  simp only [hnL, hR, h1, true_and, and_true, dite_true, dite_false]

theorem pi1_entry_eR (a : AF) : pi1 a ⟨9, by omega⟩ ⟨9, by omega⟩ = star a.u1 := by
  have hnL : ¬ ((9:ℕ) < 8 ∧ (9:ℕ) < 8) := by omega
  have hR : 8 ≤ (9:ℕ) ∧ (9:ℕ) < 16 ∧ 8 ≤ (9:ℕ) ∧ (9:ℕ) < 16 := by omega
  have hn1 : ¬ ((9:ℕ) = 8 ∧ (9:ℕ) = 8) := by omega
  have h2 : (9:ℕ) = 9 ∧ (9:ℕ) = 9 := by omega
  unfold pi1
  dsimp only
  simp only [hnL, hR, hn1, h2, true_and, and_true, dite_true, dite_false]

theorem pi1_entry_quarkR (a : AF) (k l : Fin 3) (s t : Fin 2) :
    pi1 a ⟨10 + 2 * k.val + s.val, by omega⟩ ⟨10 + 2 * l.val + t.val, by omega⟩
      = if s = t ∧ k = l then (if s = 0 then a.u1 else star a.u1)
        else 0 := by
  have hnL : ¬ ((10 + 2 * k.val + s.val) < 8 ∧ (10 + 2 * l.val + t.val) < 8) := by omega
  have hR : 8 ≤ (10 + 2 * k.val + s.val) ∧ (10 + 2 * k.val + s.val) < 16 ∧
      8 ≤ (10 + 2 * l.val + t.val) ∧ (10 + 2 * l.val + t.val) < 16 := by omega
  have hn1 : ¬ ((10 + 2 * k.val + s.val) = 8 ∧ (10 + 2 * l.val + t.val) = 8) := by omega
  have hn2 : ¬ ((10 + 2 * k.val + s.val) = 9 ∧ (10 + 2 * l.val + t.val) = 9) := by omega
  have hq : (10:ℕ) ≤ 10 + 2 * k.val + s.val ∧ (10:ℕ) ≤ 10 + 2 * l.val + t.val := by omega
  have hmod1 : (10 + 2 * k.val + s.val - 10) % 2 = s.val := by omega
  have hmod2 : (10 + 2 * l.val + t.val - 10) % 2 = t.val := by omega
  have hdiv1 : (10 + 2 * k.val + s.val - 10) / 2 = k.val := by omega
  have hdiv2 : (10 + 2 * l.val + t.val - 10) / 2 = l.val := by omega
  have hsi : (⟨s.val, by omega⟩ : Fin 2) = s := Fin.eta s _
  have hti : (⟨t.val, by omega⟩ : Fin 2) = t := Fin.eta t _
  have hki : (⟨k.val, by omega⟩ : Fin 3) = k := Fin.eta k _
  have hli : (⟨l.val, by omega⟩ : Fin 3) = l := Fin.eta l _
  unfold pi1
  dsimp only
  simp only [hnL, hR, hn1, hn2, hq, true_and, and_true, dite_true, dite_false, hmod1,
    hmod2, hdiv1, hdiv2, hsi, hti, hki, hli]

/-- Entry on the H_L antilepton doublet (CHANGED, change 1):
the ℂ-summand's pure conjugate action `λ̄ • I₂`. -/
theorem pi1_entry_leptonLc (a : AF) (s t : Fin 2) :
    pi1 a ⟨16 + s.val, by omega⟩ ⟨16 + t.val, by omega⟩
      = if s = t then star a.u1 else 0 := by
  have hnL : ¬ ((16 + s.val) < 8 ∧ (16 + t.val) < 8) := by omega
  have hnR : ¬ (8 ≤ (16 + s.val) ∧ (16 + s.val) < 16 ∧ 8 ≤ (16 + t.val) ∧ (16 + t.val) < 16) := by omega
  have hLc : 16 ≤ (16 + s.val) ∧ (16 + s.val) < 24 ∧ 16 ≤ (16 + t.val) ∧ (16 + t.val) < 24 := by omega
  have h_l : (16 + s.val) < 18 ∧ (16 + t.val) < 18 := by omega
  unfold pi1
  dsimp only
  simp only [hnL, hnR, hLc, h_l, true_and, and_true, dite_true, dite_false]
  have e1 : (⟨16 + s.val - 16, by omega⟩ : Fin 2) = s := by
    apply Fin.ext
    show 16 + s.val - 16 = s.val
    omega
  have e2 : (⟨16 + t.val - 16, by omega⟩ : Fin 2) = t := by
    apply Fin.ext
    show 16 + t.val - 16 = t.val
    omega
  rw [e1, e2]

/-- Entry on the H_L antiquark block (CHANGED, change 2):
the M₃-summand's pure conjugate action, flavour-diagonal. -/
theorem pi1_entry_quarkLc (a : AF) (k l : Fin 3) (s t : Fin 2) :
    pi1 a ⟨18 + 2 * k.val + s.val, by omega⟩ ⟨18 + 2 * l.val + t.val, by omega⟩
      = if s = t then star (a.color k l) else 0 := by
  have hnL : ¬ ((18 + 2 * k.val + s.val) < 8 ∧ (18 + 2 * l.val + t.val) < 8) := by omega
  have hnR : ¬ (8 ≤ (18 + 2 * k.val + s.val) ∧ (18 + 2 * k.val + s.val) < 16 ∧
    8 ≤ (18 + 2 * l.val + t.val) ∧ (18 + 2 * l.val + t.val) < 16) := by omega
  have hLc : 16 ≤ (18 + 2 * k.val + s.val) ∧ (18 + 2 * k.val + s.val) < 24 ∧
    16 ≤ (18 + 2 * l.val + t.val) ∧ (18 + 2 * l.val + t.val) < 24 := by omega
  have hnl : ¬ ((18 + 2 * k.val + s.val) < 18 ∧ (18 + 2 * l.val + t.val) < 18) := by omega
  have hq : (18:ℕ) ≤ 18 + 2 * k.val + s.val ∧ (18:ℕ) ≤ 18 + 2 * l.val + t.val := by omega
  have hmod1 : (18 + 2 * k.val + s.val - 18) % 2 = s.val := by omega
  have hmod2 : (18 + 2 * l.val + t.val - 18) % 2 = t.val := by omega
  have hdiv1 : (18 + 2 * k.val + s.val - 18) / 2 = k.val := by omega
  have hdiv2 : (18 + 2 * l.val + t.val - 18) / 2 = l.val := by omega
  have hsi : (⟨s.val, by omega⟩ : Fin 2) = s := Fin.eta s _
  have hti : (⟨t.val, by omega⟩ : Fin 2) = t := Fin.eta t _
  have hki : (⟨k.val, by omega⟩ : Fin 3) = k := Fin.eta k _
  have hli : (⟨l.val, by omega⟩ : Fin 3) = l := Fin.eta l _
  unfold pi1
  dsimp only
  simp only [hnL, hnR, hLc, hnl, hq, true_and, and_true, dite_true, dite_false,
    hmod1, hmod2, hdiv1, hdiv2, hsi, hti, hki, hli]

theorem pi1_entry_nuRc (a : AF) : pi1 a ⟨24, by omega⟩ ⟨24, by omega⟩ = star a.u1 := by
  have hnL : ¬ ((24:ℕ) < 8 ∧ (24:ℕ) < 8) := by omega
  have hnR : ¬ (8 ≤ (24:ℕ) ∧ (24:ℕ) < 16 ∧ 8 ≤ (24:ℕ) ∧ (24:ℕ) < 16) := by omega
  have hnLc : ¬ (16 ≤ (24:ℕ) ∧ (24:ℕ) < 24 ∧ 16 ≤ (24:ℕ) ∧ (24:ℕ) < 24) := by omega
  have hRc : 24 ≤ (24:ℕ) ∧ 24 ≤ (24:ℕ) := by omega
  have h1 : (24:ℕ) = 24 ∧ (24:ℕ) = 24 := by omega
  unfold pi1
  dsimp only
  simp only [hnL, hnR, hnLc, hRc, h1, true_and, and_true, dite_true, dite_false]

theorem pi1_entry_eRc (a : AF) : pi1 a ⟨25, by omega⟩ ⟨25, by omega⟩ = star a.u1 := by
  have hnL : ¬ ((25:ℕ) < 8 ∧ (25:ℕ) < 8) := by omega
  have hnR : ¬ (8 ≤ (25:ℕ) ∧ (25:ℕ) < 16 ∧ 8 ≤ (25:ℕ) ∧ (25:ℕ) < 16) := by omega
  have hnLc : ¬ (16 ≤ (25:ℕ) ∧ (25:ℕ) < 24 ∧ 16 ≤ (25:ℕ) ∧ (25:ℕ) < 24) := by omega
  have hRc : 24 ≤ (25:ℕ) ∧ 24 ≤ (25:ℕ) := by omega
  have hn1 : ¬ ((25:ℕ) = 24 ∧ (25:ℕ) = 24) := by omega
  have h2 : (25:ℕ) = 25 ∧ (25:ℕ) = 25 := by omega
  unfold pi1
  dsimp only
  simp only [hnL, hnR, hnLc, hRc, hn1, h2, true_and, and_true, dite_true, dite_false]

/-- Entry on the H_R antiquark block (CHANGED, change 3):
the M₃-summand's pure conjugate action, flavour-diagonal —
π₀'s shape with the colour entry conjugated. -/
theorem pi1_entry_quarkRc (a : AF) (k l : Fin 3) (s t : Fin 2) :
    pi1 a ⟨26 + 2 * k.val + s.val, by omega⟩ ⟨26 + 2 * l.val + t.val, by omega⟩
      = if s = t then star (a.color k l) else 0 := by
  have hnL : ¬ ((26 + 2 * k.val + s.val) < 8 ∧ (26 + 2 * l.val + t.val) < 8) := by omega
  have hnR : ¬ (8 ≤ (26 + 2 * k.val + s.val) ∧ (26 + 2 * k.val + s.val) < 16 ∧
    8 ≤ (26 + 2 * l.val + t.val) ∧ (26 + 2 * l.val + t.val) < 16) := by omega
  have hnLc : ¬ (16 ≤ (26 + 2 * k.val + s.val) ∧ (26 + 2 * k.val + s.val) < 24 ∧
    16 ≤ (26 + 2 * l.val + t.val) ∧ (26 + 2 * l.val + t.val) < 24) := by omega
  have hRc : 24 ≤ (26 + 2 * k.val + s.val) ∧ 24 ≤ (26 + 2 * l.val + t.val) := by omega
  have hn1 : ¬ ((26 + 2 * k.val + s.val) = 24 ∧ (26 + 2 * l.val + t.val) = 24) := by omega
  have hn2 : ¬ ((26 + 2 * k.val + s.val) = 25 ∧ (26 + 2 * l.val + t.val) = 25) := by omega
  have hq : (26:ℕ) ≤ 26 + 2 * k.val + s.val ∧ (26:ℕ) ≤ 26 + 2 * l.val + t.val := by omega
  have hmod1 : (26 + 2 * k.val + s.val - 26) % 2 = s.val := by omega
  have hmod2 : (26 + 2 * l.val + t.val - 26) % 2 = t.val := by omega
  have hdiv1 : (26 + 2 * k.val + s.val - 26) / 2 = k.val := by omega
  have hdiv2 : (26 + 2 * l.val + t.val - 26) / 2 = l.val := by omega
  have hsi : (⟨s.val, by omega⟩ : Fin 2) = s := Fin.eta s _
  have hti : (⟨t.val, by omega⟩ : Fin 2) = t := Fin.eta t _
  have hki : (⟨k.val, by omega⟩ : Fin 3) = k := Fin.eta k _
  have hli : (⟨l.val, by omega⟩ : Fin 3) = l := Fin.eta l _
  unfold pi1
  dsimp only
  simp only [hnL, hnR, hnLc, hRc, hn1, hn2, hq, true_and, and_true, dite_true,
    dite_false, hmod1, hmod2, hdiv1, hdiv2, hsi, hti, hki, hli]

/-! ### Vanishing lemmas -/

theorem pi1_entry_cross_sector (a : AF) {i j : I32}
    (h : i.val / 8 ≠ j.val / 8) : pi1 a i j = 0 := by
  have hi : i.val < 32 := i.isLt
  have hj : j.val < 32 := j.isLt
  have hnL : ¬ (i.val < 8 ∧ j.val < 8) := by omega
  have hnR : ¬ (8 ≤ i.val ∧ i.val < 16 ∧ 8 ≤ j.val ∧ j.val < 16) := by omega
  have hnLc : ¬ (16 ≤ i.val ∧ i.val < 24 ∧ 16 ≤ j.val ∧ j.val < 24) := by omega
  have hnRc : ¬ (24 ≤ i.val ∧ 24 ≤ j.val) := by omega
  unfold pi1
  dsimp only
  simp only [hnL, hnR, hnLc, hnRc, dite_false]

theorem pi1_entry_HL_mixed (a : AF) {i j : I32}
    (h : (i.val < 2 ∧ 2 ≤ j.val ∧ j.val < 8) ∨ (2 ≤ i.val ∧ i.val < 8 ∧ j.val < 2)) :
    pi1 a i j = 0 := by
  have hL : i.val < 8 ∧ j.val < 8 := by omega
  have hnl : ¬ (i.val < 2 ∧ j.val < 2) := by omega
  have hnq : ¬ (2 ≤ i.val ∧ 2 ≤ j.val) := by omega
  unfold pi1
  dsimp only
  simp only [hL, hnl, hnq, true_and, and_true, dite_true, dite_false]

theorem pi1_entry_HR_mixed (a : AF) {i j : I32}
    (h : (i.val = 8 ∧ j.val = 9) ∨ (i.val = 9 ∧ j.val = 8) ∨
         ((i.val = 8 ∨ i.val = 9) ∧ 10 ≤ j.val ∧ j.val < 16) ∨
         (10 ≤ i.val ∧ i.val < 16 ∧ (j.val = 8 ∨ j.val = 9))) :
    pi1 a i j = 0 := by
  have hnL : ¬ (i.val < 8 ∧ j.val < 8) := by omega
  have hR : 8 ≤ i.val ∧ i.val < 16 ∧ 8 ≤ j.val ∧ j.val < 16 := by omega
  have hn1 : ¬ (i.val = 8 ∧ j.val = 8) := by omega
  have hn2 : ¬ (i.val = 9 ∧ j.val = 9) := by omega
  have hnq : ¬ (10 ≤ i.val ∧ 10 ≤ j.val) := by omega
  unfold pi1
  dsimp only
  simp only [hnL, hR, hn1, hn2, hnq, true_and, and_true, dite_true, dite_false]

theorem pi1_entry_Hc_mixed (a : AF) {i j : I32}
    (h : (16 ≤ i.val ∧ i.val < 18 ∧ 18 ≤ j.val ∧ j.val < 24) ∨
         (18 ≤ i.val ∧ i.val < 24 ∧ 16 ≤ j.val ∧ j.val < 18) ∨
         (i.val = 24 ∧ 26 ≤ j.val) ∨ (i.val = 25 ∧ 26 ≤ j.val) ∨
         (26 ≤ i.val ∧ j.val = 24) ∨ (26 ≤ i.val ∧ j.val = 25) ∨
         (i.val = 24 ∧ j.val = 25) ∨ (i.val = 25 ∧ j.val = 24)) :
    pi1 a i j = 0 := by
  have hi : i.val < 32 := i.isLt
  have hj : j.val < 32 := j.isLt
  rcases h with (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
  all_goals
    have hnL : ¬ (i.val < 8 ∧ j.val < 8) := by omega
    have hnR : ¬ (8 ≤ i.val ∧ i.val < 16 ∧ 8 ≤ j.val ∧ j.val < 16) := by omega
  · have hLc : 16 ≤ i.val ∧ i.val < 24 ∧ 16 ≤ j.val ∧ j.val < 24 := by omega
    have hnl : ¬ (i.val < 18 ∧ j.val < 18) := by omega
    have hnq : ¬ (18 ≤ i.val ∧ 18 ≤ j.val) := by omega
    unfold pi1
    simp only [hnL, hnR, hLc, hnl, hnq, true_and, and_true, dite_true, dite_false]
  · have hLc : 16 ≤ i.val ∧ i.val < 24 ∧ 16 ≤ j.val ∧ j.val < 24 := by omega
    have hnl : ¬ (i.val < 18 ∧ j.val < 18) := by omega
    have hnq : ¬ (18 ≤ i.val ∧ 18 ≤ j.val) := by omega
    unfold pi1
    simp only [hnL, hnR, hLc, hnl, hnq, true_and, and_true, dite_true, dite_false]
  all_goals
    have hnLc : ¬ (16 ≤ i.val ∧ i.val < 24 ∧ 16 ≤ j.val ∧ j.val < 24) := by omega
    have hRc : 24 ≤ i.val ∧ 24 ≤ j.val := by omega
    have hn1 : ¬ (i.val = 24 ∧ j.val = 24) := by omega
    have hn2 : ¬ (i.val = 25 ∧ j.val = 25) := by omega
    have hnq : ¬ (26 ≤ i.val ∧ 26 ≤ j.val) := by omega
    unfold pi1
    simp only [hnL, hnR, hnLc, hRc, hn1, hn2, hnq, true_and, and_true, dite_true,
      dite_false]

theorem pi1_entry_eq_zero_of_not_sameBlock (a : AF) {i j : I32}
    (h : ¬ sameBlock i j) : pi1 a i j = 0 := by
  by_cases hsec : i.val / 8 = j.val / 8
  · by_cases hi : i.val < 8
    · have hj : j.val < 8 := by omega
      by_cases hi2 : i.val < 2
      · by_cases hj2 : j.val < 2
        · exact absurd (Or.inl ⟨hi2, hj2⟩) h
        · exact pi1_entry_HL_mixed a (Or.inl ⟨hi2, by omega, hj⟩)
      · by_cases hj2 : j.val < 2
        · exact pi1_entry_HL_mixed a (Or.inr ⟨by omega, hi, hj2⟩)
        · exact absurd (Or.inr (Or.inl ⟨by omega, hi, by omega, hj⟩)) h
    · by_cases hi16 : i.val < 16
      · have hj8 : 8 ≤ j.val := by omega
        have hj16 : j.val < 16 := by omega
        by_cases hi8 : i.val = 8
        · by_cases hj8' : j.val = 8
          · exact absurd (Or.inr (Or.inr (Or.inl ⟨hi8, hj8'⟩))) h
          · by_cases hj9 : j.val = 9
            · exact pi1_entry_HR_mixed a (Or.inl ⟨hi8, hj9⟩)
            · exact pi1_entry_HR_mixed a
                (Or.inr (Or.inr (Or.inl ⟨Or.inl hi8, by omega, hj16⟩)))
        · by_cases hi9 : i.val = 9
          · by_cases hj8' : j.val = 8
            · exact pi1_entry_HR_mixed a (Or.inr (Or.inl ⟨hi9, hj8'⟩))
            · by_cases hj9 : j.val = 9
              · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi9, hj9⟩)))) h
              · exact pi1_entry_HR_mixed a
                  (Or.inr (Or.inr (Or.inl ⟨Or.inr hi9, by omega, hj16⟩)))
          · by_cases hj8' : j.val = 8
            · exact pi1_entry_HR_mixed a
                (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inl hj8'⟩)))
            · by_cases hj9 : j.val = 9
              · exact pi1_entry_HR_mixed a
                  (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inr hj9⟩)))
              · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inl ⟨by omega, hi16, by omega, hj16⟩))))) h
      · by_cases hi24 : i.val < 24
        · have hj16 : 16 ≤ j.val := by omega
          have hj24 : j.val < 24 := by omega
          by_cases hi18 : i.val < 18
          · by_cases hj18 : j.val < 18
            · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨by omega, hi18, hj16, hj18⟩)))))) h
            · exact pi1_entry_Hc_mixed a (Or.inl ⟨by omega, hi18, by omega, hj24⟩)
          · by_cases hj18 : j.val < 18
            · exact pi1_entry_Hc_mixed a (Or.inr (Or.inl ⟨by omega, hi24, hj16, hj18⟩))
            · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨by omega, hi24, by omega, hj24⟩))))))) h
        · have hj24 : 24 ≤ j.val := by omega
          by_cases hi24' : i.val = 24
          · by_cases hj24' : j.val = 24
            · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inl ⟨hi24', hj24'⟩)))))))) h
            · by_cases hj25 : j.val = 25
              · exact pi1_entry_Hc_mixed a (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inl ⟨hi24', hj25⟩)))))))
              · exact pi1_entry_Hc_mixed a (Or.inr (Or.inr (Or.inl ⟨hi24', by omega⟩)))
          · by_cases hi25 : i.val = 25
            · by_cases hj24' : j.val = 24
              · exact pi1_entry_Hc_mixed a (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr ⟨hi25, hj24'⟩)))))))
              · by_cases hj25 : j.val = 25
                · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inr (Or.inl ⟨hi25, hj25⟩))))))))) h
                · exact pi1_entry_Hc_mixed a
                    (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi25, by omega⟩))))
            · by_cases hj24' : j.val = 24
              · exact pi1_entry_Hc_mixed a (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inl ⟨by omega, hj24'⟩)))))
              · by_cases hj25 : j.val = 25
                · exact pi1_entry_Hc_mixed a (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inl ⟨by omega, hj25⟩))))))
                · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega⟩)))))))))) h
  · exact pi1_entry_cross_sector a hsec


/-! ## §2. T0 — the defect anatomy, at block level

What Route A proved, restated as design input. The two BOLTS are
cited from the landed module (they are `pi0`'s own entry lemmas);
the dressed opposite entry is Route A's kill witness; the quark
defect entry is computed here from the landed entry lemmas (it
is the bolt's second site, invisible to the `witB` of Route A
because that witness has `m = 0`). Against these, π₁'s
replacement entries are §1's three changed lemmas, and
`anatomy_rho1_undressed` shows the dress is gone at the very
entry where Route A found `−I`. -/

/-- T0, bolt 1 (cited): π₀'s antilepton block multiplies the ℂ
and ℍ summands' actions on the same slots. -/
theorem anatomy_bolt_leptonLc (a : AF) (s t : Fin 2) :
    pi0 a ⟨16 + s.val, by omega⟩ ⟨16 + t.val, by omega⟩
      = star a.u1 * star (a.q s t) := pi0_entry_leptonLc a s t

/-- T0, bolt 2 (cited): π₀'s left-antiquark block is the full
tensor product `q̄ ⊗ m` of the ℍ and M₃ summands' actions. -/
theorem anatomy_bolt_quarkLc (a : AF) (k l : Fin 3) (s t : Fin 2) :
    pi0 a ⟨18 + 2 * k.val + s.val, by omega⟩ ⟨18 + 2 * l.val + t.val, by omega⟩
      = star (a.q s t) * a.color k l := pi0_entry_quarkLc a k l s t

/-- T0 (cited from Route A): the dressed opposite entry —
ρ° seats `λ̄ • q̄_b` on the lepton doublet, and at `witB` its
`(0,0)` entry is `−I`, not a scalar of the ℂ action. This entry
is the first-order kill's extra term. -/
theorem anatomy_rho0_dressed :
    rho0 witB ⟨0, by omega⟩ ⟨0, by omega⟩ = -Complex.I := rho0_wit_00

/-- T0: at the same witness, π₁'s opposite entry is the plain
scalar `1` — the antilepton block now seats only `λ̄`, whose
value at `witB` (`λ = 1`) is `1`. The dressing is removed by
construction, not by a hypothesis. -/
theorem anatomy_rho1_undressed :
    rho1 witB ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := by
  have h := pi1_entry_leptonLc witB ⟨0, by omega⟩ ⟨0, by omega⟩
  rw [if_pos rfl] at h
  rw [rho1_entry, partner_mk0]
  exact h.trans (by simp [witB])

/-- The second bolt witness: `witB` with the colour component
switched on (`m = 1`). Route A's `witB` has `m = 0`, which hides
the quark-sector bolt. -/
def witBp : AF := ⟨1, !![Complex.I, 0; 0, -Complex.I], 1⟩

/-- T0: π₀'s quark-sector order-zero defect, proved from the
landed entry lemmas. At `(2,3)`: `(π₀ a₀ * ρ° b₁)(2,3) = I`
against `(ρ° b₁ * π₀ a₀)(2,3) = −I`, where `a₀ = witA`. The
defect runs through the bolted antiquark block: `ρ°` seats
`q̄_b ⊗ m_b` transposed on the quark doublet, and `q̄_b`'s
`(1,1)` entry `I` (conjugated) is what fails to commute with
`q_a`. -/
theorem anatomy_pi0_quark_defect :
    (pi0 witA * rho0 witBp) ⟨2, by omega⟩ ⟨3, by omega⟩ = Complex.I ∧
    (rho0 witBp * pi0 witA) ⟨2, by omega⟩ ⟨3, by omega⟩ = -Complex.I := by
  have eA22 : pi0 witA ⟨2, by omega⟩ ⟨2, by omega⟩ = 0 := by
    have h := pi0_entry_quarkL witA ⟨0, by omega⟩ ⟨0, by omega⟩
      ⟨0, by omega⟩ ⟨0, by omega⟩
    rw [if_pos rfl] at h
    simpa [witA] using h
  have eA23 : pi0 witA ⟨2, by omega⟩ ⟨3, by omega⟩ = 1 := by
    have h := pi0_entry_quarkL witA ⟨0, by omega⟩ ⟨0, by omega⟩
      ⟨0, by omega⟩ ⟨1, by omega⟩
    rw [if_pos rfl] at h
    simpa [witA] using h
  have eA33 : pi0 witA ⟨3, by omega⟩ ⟨3, by omega⟩ = 0 := by
    have h := pi0_entry_quarkL witA ⟨0, by omega⟩ ⟨0, by omega⟩
      ⟨1, by omega⟩ ⟨1, by omega⟩
    rw [if_pos rfl] at h
    simpa [witA] using h
  have eB18 : pi0 witBp ⟨18, by omega⟩ ⟨18, by omega⟩ = -Complex.I := by
    have h := pi0_entry_quarkLc witBp ⟨0, by omega⟩ ⟨0, by omega⟩
      ⟨0, by omega⟩ ⟨0, by omega⟩
    simpa [witBp, star_I] using h
  have eB19 : pi0 witBp ⟨19, by omega⟩ ⟨19, by omega⟩ = Complex.I := by
    have h := pi0_entry_quarkLc witBp ⟨0, by omega⟩ ⟨0, by omega⟩
      ⟨1, by omega⟩ ⟨1, by omega⟩
    simpa [witBp, star_I] using h
  have eB1918 : pi0 witBp ⟨19, by omega⟩ ⟨18, by omega⟩ = 0 := by
    have h := pi0_entry_quarkLc witBp ⟨0, by omega⟩ ⟨0, by omega⟩
      ⟨1, by omega⟩ ⟨0, by omega⟩
    simpa [witBp] using h
  have rB22 : rho0 witBp ⟨2, by omega⟩ ⟨2, by omega⟩ = -Complex.I := by
    rw [rho0_entry]
    exact eB18
  have rB23 : rho0 witBp ⟨2, by omega⟩ ⟨3, by omega⟩ = 0 := by
    rw [rho0_entry]
    exact eB1918
  have rB33 : rho0 witBp ⟨3, by omega⟩ ⟨3, by omega⟩ = Complex.I := by
    rw [rho0_entry]
    exact eB19
  have hvan1 : ∀ k : I32, k ∉ ({⟨2, by omega⟩, ⟨3, by omega⟩} : Finset I32) →
      pi0 witA ⟨2, by omega⟩ k * rho0 witBp k ⟨3, by omega⟩ = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    by_cases hsb : sameBlock (⟨2, by omega⟩ : I32) k
    · have hk8 : 2 ≤ k.val ∧ k.val < 8 := by
        unfold sameBlock at hsb
        dsimp only at hsb
        omega
      have hkne : k.val ≠ 2 ∧ k.val ≠ 3 := by
        constructor <;> intro hv
        · exact hk.1 (Fin.ext hv)
        · exact hk.2 (Fin.ext hv)
      have hcol : (⟨(k.val - 2) / 2, by omega⟩ : Fin 3) ≠ ⟨0, by omega⟩ := by
        intro hcon
        have hv : (k.val - 2) / 2 = 0 := by
          have h2 := congrArg Fin.val hcon
          simpa using h2
        omega
      have h0 : pi0 witA ⟨2, by omega⟩ k = 0 := by
        have h := pi0_entry_quarkL witA ⟨0, by omega⟩
          ⟨(k.val - 2) / 2, by omega⟩ ⟨0, by omega⟩
          ⟨(k.val - 2) % 2, by omega⟩
        rw [if_neg (Ne.symm hcol)] at h
        have e1 : (⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val
            + (⟨0, by omega⟩ : Fin 2).val, by omega⟩ : I32)
            = ⟨2, by omega⟩ := rfl
        have e2 : (⟨2 + 2 * (⟨(k.val - 2) / 2, by omega⟩ : Fin 3).val
            + (⟨(k.val - 2) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32)
            = k := by
          apply Fin.ext
          show 2 + 2 * ((k.val - 2) / 2) + (k.val - 2) % 2 = k.val
          have hd := Nat.div_add_mod (k.val - 2) 2
          omega
        rw [e1, e2] at h
        exact h
      rw [h0, zero_mul]
    · have h0 : pi0 witA ⟨2, by omega⟩ k = 0 :=
        pi0_entry_eq_zero_of_not_sameBlock witA hsb
      rw [h0, zero_mul]
  have hvan2 : ∀ k : I32, k ∉ ({⟨2, by omega⟩, ⟨3, by omega⟩} : Finset I32) →
      rho0 witBp ⟨2, by omega⟩ k * pi0 witA k ⟨3, by omega⟩ = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    by_cases hsb : sameBlock k (⟨3, by omega⟩ : I32)
    · have hk8 : 2 ≤ k.val ∧ k.val < 8 := by
        unfold sameBlock at hsb
        dsimp only at hsb
        omega
      have hkne : k.val ≠ 2 ∧ k.val ≠ 3 := by
        constructor <;> intro hv
        · exact hk.1 (Fin.ext hv)
        · exact hk.2 (Fin.ext hv)
      have hcol : (⟨(k.val - 2) / 2, by omega⟩ : Fin 3) ≠ ⟨0, by omega⟩ := by
        intro hcon
        have hv : (k.val - 2) / 2 = 0 := by
          have h2 := congrArg Fin.val hcon
          simpa using h2
        omega
      have h0 : pi0 witA k ⟨3, by omega⟩ = 0 := by
        have h := pi0_entry_quarkL witA ⟨(k.val - 2) / 2, by omega⟩
          ⟨0, by omega⟩ ⟨(k.val - 2) % 2, by omega⟩ ⟨1, by omega⟩
        rw [if_neg hcol] at h
        have e1 : (⟨2 + 2 * (⟨(k.val - 2) / 2, by omega⟩ : Fin 3).val
            + (⟨(k.val - 2) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32)
            = k := by
          apply Fin.ext
          show 2 + 2 * ((k.val - 2) / 2) + (k.val - 2) % 2 = k.val
          have hd := Nat.div_add_mod (k.val - 2) 2
          omega
        have e2 : (⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val
            + (⟨1, by omega⟩ : Fin 2).val, by omega⟩ : I32)
            = ⟨3, by omega⟩ := rfl
        rw [e1, e2] at h
        exact h
      rw [h0, mul_zero]
    · have h0 : pi0 witA k ⟨3, by omega⟩ = 0 :=
        pi0_entry_eq_zero_of_not_sameBlock witA hsb
      rw [h0, mul_zero]
  constructor
  · rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan1,
      Finset.sum_pair (by decide : (⟨2, by omega⟩ : I32) ≠ ⟨3, by omega⟩),
      eA22, rB23, eA23, rB33]
    norm_num
  · rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan2,
      Finset.sum_pair (by decide : (⟨2, by omega⟩ : I32) ≠ ⟨3, by omega⟩),
      rB22, eA23, rB23, eA33]
    norm_num




/-- π₁ agrees with π₀ on the whole particle half. -/
theorem pi1_eq_pi0_of_lt16 (a : AF) {i j : I32} (hi : i.val < 16) (hj : j.val < 16) :
    pi1 a i j = pi0 a i j := by
  unfold pi1 pi0
  dsimp only
  split_ifs <;> first | rfl | omega | simp_all



/-! ## §3. T1 — the representation laws of π₁

The seven unchanged blocks keep π₀'s multiplicativity proofs
verbatim in form. The three changed blocks get new closing
computations: their products now close through `star_mul`,
`star_sum` and commutativity in ℂ — possible exactly because
each block entry mentions ONE summand. Additivity — which π₀
provably failed — is proved block by block the same way: no
block entry of π₁ is a product of two summands' components,
so no cross-terms exist. The species is therefore the full
one: π₁ is a unital `*`-algebra representation (§3 assemblies
plus `pi1_zero`, and `pi1_one` in §5). -/

theorem pi1_mul_leptonL (a b : AF) (s t : Fin 2) :
    (pi1 a * pi1 b) ⟨s.val, by omega⟩ ⟨t.val, by omega⟩
      = pi1 (afMul a b) ⟨s.val, by omega⟩ ⟨t.val, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset I32) →
      pi1 a ⟨s.val, by omega⟩ k * pi1 b k ⟨t.val, by omega⟩ = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    by_cases hk8 : k.val < 8
    · by_cases hk2 : k.val < 2
      · have hkv : k.val = 0 ∨ k.val = 1 := by omega
        rcases hkv with h0 | h1
        · exact absurd (Fin.ext h0) hk.1
        · exact absurd (Fin.ext h1) hk.2
      · rw [pi1_entry_HL_mixed (i := ⟨s.val, by omega⟩) (j := k) a
          (Or.inl ⟨(by show s.val < 2; omega), (by omega), hk8⟩), zero_mul]
    · rw [pi1_entry_cross_sector (i := ⟨s.val, by omega⟩) (j := k) a
        (by show s.val / 8 ≠ k.val / 8; omega), zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_pair (by decide : (⟨0, by omega⟩ : I32) ≠ ⟨1, by omega⟩),
    pi1_entry_leptonL a s ⟨0, by omega⟩, pi1_entry_leptonL b ⟨0, by omega⟩ t,
    pi1_entry_leptonL a s ⟨1, by omega⟩, pi1_entry_leptonL b ⟨1, by omega⟩ t,
    pi1_entry_leptonL (afMul a b) s t, afMul_q, Matrix.mul_apply, Fin.sum_univ_two,
    fin2_mk0, fin2_mk1]

theorem pi1_mul_quarkL (a b : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    (pi1 a * pi1 b) ⟨2 + 2 * ki.val + si.val, by omega⟩
        ⟨2 + 2 * kj.val + sj.val, by omega⟩
      = pi1 (afMul a b) ⟨2 + 2 * ki.val + si.val, by omega⟩
        ⟨2 + 2 * kj.val + sj.val, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) →
      pi1 a ⟨2 + 2 * ki.val + si.val, by omega⟩ k *
        pi1 b k ⟨2 + 2 * kj.val + sj.val, by omega⟩ = 0 := by
    intro k hk
    by_cases hk8 : k.val < 8
    · by_cases hk2 : 2 ≤ k.val
      · have hkv : k.val = 2 ∨ k.val = 3 ∨ k.val = 4 ∨ k.val = 5 ∨ k.val = 6 ∨
            k.val = 7 := by omega
        have hmem : k ∈ ({⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
            ⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
            ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
            ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
            ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
            ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hkv with h | h | h | h | h | h <;>
            first
              | exact Or.inl (Fin.ext (show k.val = 2 by omega))
              | exact Or.inr (Or.inl (Fin.ext (show k.val = 3 by omega)))
              | exact Or.inr (Or.inr (Or.inl (Fin.ext (show k.val = 4 by omega))))
              | exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (show k.val = 5 by omega)))))
              | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (show k.val = 6 by omega))))))
              | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext (show k.val = 7 by omega))))))
        exact absurd hmem hk
      · rw [pi1_entry_HL_mixed (i := ⟨2 + 2 * ki.val + si.val, by omega⟩) (j := k) a
          (Or.inr ⟨(by show 2 ≤ 2 + 2 * ki.val + si.val; omega),
            (by show 2 + 2 * ki.val + si.val < 8; omega), (by omega)⟩), zero_mul]
    · rw [pi1_entry_cross_sector (i := ⟨2 + 2 * ki.val + si.val, by omega⟩) (j := k) a
        (by show (2 + 2 * ki.val + si.val) / 8 ≠ k.val / 8; omega), zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    pi1_entry_quarkL a ki ⟨0, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkL b ⟨0, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkL a ki ⟨0, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkL b ⟨0, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi1_entry_quarkL a ki ⟨1, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkL b ⟨1, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkL a ki ⟨1, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkL b ⟨1, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi1_entry_quarkL a ki ⟨2, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkL b ⟨2, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkL a ki ⟨2, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkL b ⟨2, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi1_entry_quarkL (afMul a b) ki kj si sj, afMul_q, Matrix.mul_apply,
    Fin.sum_univ_two, fin2_mk0, fin2_mk1, fin3_mk0, fin3_mk1, fin3_mk2]
  fin_cases ki <;> fin_cases kj <;> simp <;> ring

theorem pi1_mul_nuR (a b : AF) :
    (pi1 a * pi1 b) ⟨8, by omega⟩ ⟨8, by omega⟩
      = pi1 (afMul a b) ⟨8, by omega⟩ ⟨8, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨8, by omega⟩} : Finset I32) →
      pi1 a ⟨8, by omega⟩ k * pi1 b k ⟨8, by omega⟩ = 0 := by
    intro k hk
    simp only [Finset.mem_singleton] at hk
    have hk8v : k.val ≠ 8 := fun hv => hk (Fin.ext hv)
    by_cases hk8 : k.val < 8
    · rw [pi1_entry_cross_sector (i := ⟨8, by omega⟩) (j := k) a
        (by show (8:ℕ) / 8 ≠ k.val / 8; omega), zero_mul]
    · by_cases hk16 : k.val < 16
      · by_cases hk9 : k.val = 9
        · rw [pi1_entry_HR_mixed (i := ⟨8, by omega⟩) (j := k) a
            (Or.inl ⟨rfl, hk9⟩), zero_mul]
        · rw [pi1_entry_HR_mixed (i := ⟨8, by omega⟩) (j := k) a
            (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, by omega, hk16⟩))), zero_mul]
      · rw [pi1_entry_cross_sector (i := ⟨8, by omega⟩) (j := k) a
          (by show (8:ℕ) / 8 ≠ k.val / 8; omega), zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan, Finset.sum_singleton,
    pi1_entry_nuR, pi1_entry_nuR, pi1_entry_nuR, afMul_u1]

theorem pi1_mul_eR (a b : AF) :
    (pi1 a * pi1 b) ⟨9, by omega⟩ ⟨9, by omega⟩
      = pi1 (afMul a b) ⟨9, by omega⟩ ⟨9, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨9, by omega⟩} : Finset I32) →
      pi1 a ⟨9, by omega⟩ k * pi1 b k ⟨9, by omega⟩ = 0 := by
    intro k hk
    simp only [Finset.mem_singleton] at hk
    have hk9v : k.val ≠ 9 := fun hv => hk (Fin.ext hv)
    by_cases hk8 : k.val < 8
    · rw [pi1_entry_cross_sector (i := ⟨9, by omega⟩) (j := k) a
        (by show (9:ℕ) / 8 ≠ k.val / 8; omega), zero_mul]
    · by_cases hk16 : k.val < 16
      · by_cases hk8' : k.val = 8
        · rw [pi1_entry_HR_mixed (i := ⟨9, by omega⟩) (j := k) a
            (Or.inr (Or.inl ⟨rfl, hk8'⟩)), zero_mul]
        · rw [pi1_entry_HR_mixed (i := ⟨9, by omega⟩) (j := k) a
            (Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, by omega, hk16⟩))), zero_mul]
      · rw [pi1_entry_cross_sector (i := ⟨9, by omega⟩) (j := k) a
          (by show (9:ℕ) / 8 ≠ k.val / 8; omega), zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan, Finset.sum_singleton,
    pi1_entry_eR, pi1_entry_eR, pi1_entry_eR, afMul_u1, star_mul,
    mul_comm (star b.u1) (star a.u1)]

theorem pi1_mul_quarkR (a b : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    (pi1 a * pi1 b) ⟨10 + 2 * ki.val + si.val, by omega⟩
        ⟨10 + 2 * kj.val + sj.val, by omega⟩
      = pi1 (afMul a b) ⟨10 + 2 * ki.val + si.val, by omega⟩
        ⟨10 + 2 * kj.val + sj.val, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) →
      pi1 a ⟨10 + 2 * ki.val + si.val, by omega⟩ k *
        pi1 b k ⟨10 + 2 * kj.val + sj.val, by omega⟩ = 0 := by
    intro k hk
    by_cases hklo : k.val < 8
    · rw [pi1_entry_cross_sector (i := ⟨10 + 2 * ki.val + si.val, by omega⟩) (j := k) a
        (by show (10 + 2 * ki.val + si.val) / 8 ≠ k.val / 8; omega), zero_mul]
    · by_cases hkhi : 16 ≤ k.val
      · rw [pi1_entry_cross_sector (i := ⟨10 + 2 * ki.val + si.val, by omega⟩) (j := k) a
          (by show (10 + 2 * ki.val + si.val) / 8 ≠ k.val / 8; omega), zero_mul]
      · by_cases hk10 : 10 ≤ k.val
        · have hkv : k.val = 10 ∨ k.val = 11 ∨ k.val = 12 ∨ k.val = 13 ∨
              k.val = 14 ∨ k.val = 15 := by omega
          have hmem : k ∈ ({⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
              ⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
              ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
              ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
              ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
              ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) := by
            simp only [Finset.mem_insert, Finset.mem_singleton]
            rcases hkv with h | h | h | h | h | h <;>
              first
                | exact Or.inl (Fin.ext (show k.val = 10 by omega))
                | exact Or.inr (Or.inl (Fin.ext (show k.val = 11 by omega)))
                | exact Or.inr (Or.inr (Or.inl (Fin.ext (show k.val = 12 by omega))))
                | exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (show k.val = 13 by omega)))))
                | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (show k.val = 14 by omega))))))
                | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext (show k.val = 15 by omega))))))
          exact absurd hmem hk
        · by_cases hk8 : k.val = 8
          · rw [pi1_entry_HR_mixed (i := ⟨10 + 2 * ki.val + si.val, by omega⟩) (j := k) a
              (Or.inr (Or.inr (Or.inr ⟨(by show 10 ≤ 10 + 2 * ki.val + si.val; omega),
                (by show 10 + 2 * ki.val + si.val < 16; omega), Or.inl hk8⟩))), zero_mul]
          · rw [pi1_entry_HR_mixed (i := ⟨10 + 2 * ki.val + si.val, by omega⟩) (j := k) a
              (Or.inr (Or.inr (Or.inr ⟨(by show 10 ≤ 10 + 2 * ki.val + si.val; omega),
                (by show 10 + 2 * ki.val + si.val < 16; omega),
                Or.inr (by omega : k.val = 9)⟩))), zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    pi1_entry_quarkR a ki ⟨0, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkR b ⟨0, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkR a ki ⟨0, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkR b ⟨0, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi1_entry_quarkR a ki ⟨1, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkR b ⟨1, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkR a ki ⟨1, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkR b ⟨1, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi1_entry_quarkR a ki ⟨2, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkR b ⟨2, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkR a ki ⟨2, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkR b ⟨2, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi1_entry_quarkR (afMul a b) ki kj si sj, afMul_u1, fin2_mk0, fin2_mk1,
    fin3_mk0, fin3_mk1, fin3_mk2]
  by_cases h : si = sj ∧ ki = kj
  · obtain ⟨h1, h2⟩ := h
    subst h1
    subst h2
    fin_cases si <;> fin_cases ki <;> simp [star_mul, mul_comm]
  · by_cases h1 : si = sj
    · subst h1
      fin_cases si <;> fin_cases ki <;> fin_cases kj <;> simp
    · fin_cases si <;> fin_cases sj <;> fin_cases ki <;> fin_cases kj <;> simp

theorem pi1_mul_leptonLc (a b : AF) (s t : Fin 2) :
    (pi1 a * pi1 b) ⟨16 + s.val, by omega⟩ ⟨16 + t.val, by omega⟩
      = pi1 (afMul a b) ⟨16 + s.val, by omega⟩ ⟨16 + t.val, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨16 + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨16 + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) →
      pi1 a ⟨16 + s.val, by omega⟩ k * pi1 b k ⟨16 + t.val, by omega⟩ = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    by_cases hk24 : k.val < 24
    · by_cases hk16 : 16 ≤ k.val
      · by_cases hk18 : k.val < 18
        · have hkv : k.val = 16 ∨ k.val = 17 := by omega
          rcases hkv with h0 | h1
          · exact absurd (Fin.ext (show k.val = 16 by omega)) hk.1
          · exact absurd (Fin.ext (show k.val = 17 by omega)) hk.2
        · rw [pi1_entry_Hc_mixed (i := ⟨16 + s.val, by omega⟩) (j := k) a
            (Or.inl ⟨(by show 16 ≤ 16 + s.val; omega), (by show 16 + s.val < 18; omega),
              (by omega), hk24⟩), zero_mul]
      · rw [pi1_entry_cross_sector (i := ⟨16 + s.val, by omega⟩) (j := k) a
          (by show (16 + s.val) / 8 ≠ k.val / 8; omega), zero_mul]
    · rw [pi1_entry_cross_sector (i := ⟨16 + s.val, by omega⟩) (j := k) a
        (by show (16 + s.val) / 8 ≠ k.val / 8; omega), zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_pair (by decide : (⟨16 + (⟨0, by omega⟩ : Fin 2).val, by omega⟩ : I32) ≠
      ⟨16 + (⟨1, by omega⟩ : Fin 2).val, by omega⟩),
    pi1_entry_leptonLc a s ⟨0, by omega⟩, pi1_entry_leptonLc b ⟨0, by omega⟩ t,
    pi1_entry_leptonLc a s ⟨1, by omega⟩, pi1_entry_leptonLc b ⟨1, by omega⟩ t,
    pi1_entry_leptonLc (afMul a b) s t, afMul_u1, star_mul]
  fin_cases s <;> fin_cases t <;> simp <;> ring

theorem pi1_mul_quarkLc (a b : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    (pi1 a * pi1 b) ⟨18 + 2 * ki.val + si.val, by omega⟩
        ⟨18 + 2 * kj.val + sj.val, by omega⟩
      = pi1 (afMul a b) ⟨18 + 2 * ki.val + si.val, by omega⟩
        ⟨18 + 2 * kj.val + sj.val, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) →
      pi1 a ⟨18 + 2 * ki.val + si.val, by omega⟩ k *
        pi1 b k ⟨18 + 2 * kj.val + sj.val, by omega⟩ = 0 := by
    intro k hk
    by_cases hk24 : k.val < 24
    · by_cases hk16 : 16 ≤ k.val
      · by_cases hk18 : 18 ≤ k.val
        · have hkv : k.val = 18 ∨ k.val = 19 ∨ k.val = 20 ∨ k.val = 21 ∨
              k.val = 22 ∨ k.val = 23 := by omega
          have hmem : k ∈ ({⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
              ⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
              ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
              ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
              ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
              ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) := by
            simp only [Finset.mem_insert, Finset.mem_singleton]
            rcases hkv with h | h | h | h | h | h <;>
              first
                | exact Or.inl (Fin.ext (show k.val = 18 by omega))
                | exact Or.inr (Or.inl (Fin.ext (show k.val = 19 by omega)))
                | exact Or.inr (Or.inr (Or.inl (Fin.ext (show k.val = 20 by omega))))
                | exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (show k.val = 21 by omega)))))
                | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (show k.val = 22 by omega))))))
                | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext (show k.val = 23 by omega))))))
          exact absurd hmem hk
        · rw [pi1_entry_Hc_mixed (i := ⟨18 + 2 * ki.val + si.val, by omega⟩) (j := k) a
            (Or.inr (Or.inl ⟨(by show 18 ≤ 18 + 2 * ki.val + si.val; omega),
              (by show 18 + 2 * ki.val + si.val < 24; omega), hk16, (by omega)⟩)), zero_mul]
      · rw [pi1_entry_cross_sector (i := ⟨18 + 2 * ki.val + si.val, by omega⟩) (j := k) a
          (by show (18 + 2 * ki.val + si.val) / 8 ≠ k.val / 8; omega), zero_mul]
    · rw [pi1_entry_cross_sector (i := ⟨18 + 2 * ki.val + si.val, by omega⟩) (j := k) a
        (by show (18 + 2 * ki.val + si.val) / 8 ≠ k.val / 8; omega), zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    pi1_entry_quarkLc a ki ⟨0, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkLc b ⟨0, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkLc a ki ⟨0, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkLc b ⟨0, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi1_entry_quarkLc a ki ⟨1, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkLc b ⟨1, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkLc a ki ⟨1, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkLc b ⟨1, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi1_entry_quarkLc a ki ⟨2, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkLc b ⟨2, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkLc a ki ⟨2, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkLc b ⟨2, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi1_entry_quarkLc (afMul a b) ki kj si sj, afMul_color, Matrix.mul_apply]
  by_cases h : si = sj
  · subst h
    fin_cases si <;> fin_cases ki <;> fin_cases kj <;>
      simp [Fin.sum_univ_three, fin3_mk0, fin3_mk1, fin3_mk2, star_sum,
        star_mul] <;> ring
  · fin_cases si <;> fin_cases sj <;> fin_cases ki <;> fin_cases kj <;>
      simp [Fin.sum_univ_three, fin3_mk0, fin3_mk1, fin3_mk2, star_sum,
        star_mul] <;> ring

theorem pi1_mul_nuRc (a b : AF) :
    (pi1 a * pi1 b) ⟨24, by omega⟩ ⟨24, by omega⟩
      = pi1 (afMul a b) ⟨24, by omega⟩ ⟨24, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨24, by omega⟩} : Finset I32) →
      pi1 a ⟨24, by omega⟩ k * pi1 b k ⟨24, by omega⟩ = 0 := by
    intro k hk
    simp only [Finset.mem_singleton] at hk
    have hk24v : k.val ≠ 24 := fun hv => hk (Fin.ext hv)
    by_cases hk24 : k.val < 24
    · rw [pi1_entry_cross_sector (i := ⟨24, by omega⟩) (j := k) a
        (by show (24:ℕ) / 8 ≠ k.val / 8; omega), zero_mul]
    · by_cases hk25 : k.val = 25
      · rw [pi1_entry_Hc_mixed (i := ⟨24, by omega⟩) (j := k) a
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hk25⟩))))))),
          zero_mul]
      · rw [pi1_entry_Hc_mixed (i := ⟨24, by omega⟩) (j := k) a
          (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))), zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan, Finset.sum_singleton,
    pi1_entry_nuRc, pi1_entry_nuRc, pi1_entry_nuRc, afMul_u1, star_mul,
    mul_comm (star b.u1) (star a.u1)]

theorem pi1_mul_eRc (a b : AF) :
    (pi1 a * pi1 b) ⟨25, by omega⟩ ⟨25, by omega⟩
      = pi1 (afMul a b) ⟨25, by omega⟩ ⟨25, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨25, by omega⟩} : Finset I32) →
      pi1 a ⟨25, by omega⟩ k * pi1 b k ⟨25, by omega⟩ = 0 := by
    intro k hk
    simp only [Finset.mem_singleton] at hk
    have hk25v : k.val ≠ 25 := fun hv => hk (Fin.ext hv)
    by_cases hk24 : k.val < 24
    · rw [pi1_entry_cross_sector (i := ⟨25, by omega⟩) (j := k) a
        (by show (25:ℕ) / 8 ≠ k.val / 8; omega), zero_mul]
    · by_cases hk24' : k.val = 24
      · rw [pi1_entry_Hc_mixed (i := ⟨25, by omega⟩) (j := k) a
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hk24'⟩))))))),
          zero_mul]
      · rw [pi1_entry_Hc_mixed (i := ⟨25, by omega⟩) (j := k) a
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩)))), zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan, Finset.sum_singleton,
    pi1_entry_eRc, pi1_entry_eRc, pi1_entry_eRc, afMul_u1, star_mul,
    mul_comm (star b.u1) (star a.u1)]

theorem pi1_mul_quarkRc (a b : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    (pi1 a * pi1 b) ⟨26 + 2 * ki.val + si.val, by omega⟩
        ⟨26 + 2 * kj.val + sj.val, by omega⟩
      = pi1 (afMul a b) ⟨26 + 2 * ki.val + si.val, by omega⟩
        ⟨26 + 2 * kj.val + sj.val, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩,
      ⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩,
      ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩,
      ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩,
      ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩,
      ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩} : Finset I32) →
      pi1 a ⟨26 + 2 * ki.val + si.val, by omega⟩ k *
        pi1 b k ⟨26 + 2 * kj.val + sj.val, by omega⟩ = 0 := by
    intro k hk
    by_cases hk24 : k.val < 24
    · rw [pi1_entry_cross_sector (i := ⟨26 + 2 * ki.val + si.val, by omega⟩) (j := k) a
        (by show (26 + 2 * ki.val + si.val) / 8 ≠ k.val / 8; omega), zero_mul]
    · by_cases hk26 : 26 ≤ k.val
      · have hkv : k.val = 26 ∨ k.val = 27 ∨ k.val = 28 ∨ k.val = 29 ∨
            k.val = 30 ∨ k.val = 31 := by omega
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6⟩ := hk
        rcases hkv with h | h | h | h | h | h
        · exact absurd (Fin.ext (show k.val = 26 by omega)) hk1
        · exact absurd (Fin.ext (show k.val = 27 by omega)) hk2
        · exact absurd (Fin.ext (show k.val = 28 by omega)) hk3
        · exact absurd (Fin.ext (show k.val = 29 by omega)) hk4
        · exact absurd (Fin.ext (show k.val = 30 by omega)) hk5
        · exact absurd (Fin.ext (show k.val = 31 by omega)) hk6
      · by_cases hk24' : k.val = 24
        · rw [pi1_entry_Hc_mixed (i := ⟨26 + 2 * ki.val + si.val, by omega⟩) (j := k) a
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨(by show 26 ≤ 26 + 2 * ki.val + si.val; omega), hk24'⟩))))), zero_mul]
        · rw [pi1_entry_Hc_mixed (i := ⟨26 + 2 * ki.val + si.val, by omega⟩) (j := k) a
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨(by show 26 ≤ 26 + 2 * ki.val + si.val; omega),
                (by omega : k.val = 25)⟩)))))), zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    pi1_entry_quarkRc a ki ⟨0, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkRc b ⟨0, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkRc a ki ⟨0, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkRc b ⟨0, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi1_entry_quarkRc a ki ⟨1, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkRc b ⟨1, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkRc a ki ⟨1, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkRc b ⟨1, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi1_entry_quarkRc a ki ⟨2, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkRc b ⟨2, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkRc a ki ⟨2, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkRc b ⟨2, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi1_entry_quarkRc (afMul a b) ki kj si sj, afMul_color, Matrix.mul_apply]
  by_cases h : si = sj
  · subst h
    fin_cases si <;> fin_cases ki <;> fin_cases kj <;>
      simp [Fin.sum_univ_three, fin3_mk0, fin3_mk1, fin3_mk2, star_sum,
        star_mul] <;> ring
  · fin_cases si <;> fin_cases sj <;> fin_cases ki <;> fin_cases kj <;>
      simp [Fin.sum_univ_three, fin3_mk0, fin3_mk1, fin3_mk2, star_sum,
        star_mul] <;> ring

/-- Product vanishing, entry form (π₁-local copy of the landed
helper, which is stated for `pi0`). -/
theorem pi1_mul_entry_eq_zero (a b : AF) {i j : I32}
    (ha : ∀ k : I32, pi1 a i k = 0 ∨ pi1 b k j = 0) :
    (pi1 a * pi1 b) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rcases ha k with h | h
  · rw [h, zero_mul]
  · rw [h, mul_zero]

theorem pi1_mul_eq_zero_of_not_sameBlock (a b : AF) {i j : I32}
    (h : ¬ sameBlock i j) : (pi1 a * pi1 b) i j = 0 := by
  apply pi1_mul_entry_eq_zero
  intro k
  by_cases hs : sameBlock i k
  · exact Or.inr (pi1_entry_eq_zero_of_not_sameBlock b
      (fun hkj => h (sameBlock_trans hs hkj)))
  · exact Or.inl (pi1_entry_eq_zero_of_not_sameBlock a hs)

/-- T1 (multiplicative part): `pi1` preserves the componentwise
product. Entry case tree as in the landed module: off-block
entries vanish on both sides; on-block entries are the ten block
lemmas above. -/
theorem pi1_afMul (a b : AF) : pi1 (afMul a b) = pi1 a * pi1 b := by
  ext i j
  by_cases hsec : i.val / 8 = j.val / 8
  · by_cases hi : i.val < 8
    · have hj : j.val < 8 := by omega
      by_cases hi2 : i.val < 2
      · by_cases hj2 : j.val < 2
        · have hsi : (⟨(⟨i.val, hi2⟩ : Fin 2).val, by omega⟩ : I32) = i :=
            Fin.ext (show (⟨i.val, hi2⟩ : Fin 2).val = i.val from rfl)
          have hsj : (⟨(⟨j.val, hj2⟩ : Fin 2).val, by omega⟩ : I32) = j :=
            Fin.ext (show (⟨j.val, hj2⟩ : Fin 2).val = j.val from rfl)
          rw [← hsi, ← hsj]
          exact (pi1_mul_leptonL a b ⟨i.val, hi2⟩ ⟨j.val, hj2⟩).symm
        · have hns : ¬ sameBlock i j := not_sameBlock_of_HL_mixed (Or.inl ⟨hi2, by omega, hj⟩)
          rw [pi1_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
            pi1_mul_eq_zero_of_not_sameBlock a b hns]
      · by_cases hj2 : j.val < 2
        · have hns : ¬ sameBlock i j := not_sameBlock_of_HL_mixed (Or.inr ⟨by omega, hi, hj2⟩)
          rw [pi1_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
            pi1_mul_eq_zero_of_not_sameBlock a b hns]
        · have hci : (⟨2 + 2 * (⟨(i.val - 2) / 2, by omega⟩ : Fin 3).val
              + (⟨(i.val - 2) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
            apply Fin.ext
            show 2 + 2 * ((i.val - 2) / 2) + (i.val - 2) % 2 = i.val
            have h := Nat.div_add_mod (i.val - 2) 2
            omega
          have hcj : (⟨2 + 2 * (⟨(j.val - 2) / 2, by omega⟩ : Fin 3).val
              + (⟨(j.val - 2) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
            apply Fin.ext
            show 2 + 2 * ((j.val - 2) / 2) + (j.val - 2) % 2 = j.val
            have h := Nat.div_add_mod (j.val - 2) 2
            omega
          rw [← hci, ← hcj]
          exact (pi1_mul_quarkL a b ⟨(i.val - 2) / 2, by omega⟩
            ⟨(j.val - 2) / 2, by omega⟩ ⟨(i.val - 2) % 2, by omega⟩
            ⟨(j.val - 2) % 2, by omega⟩).symm
    · by_cases hi16 : i.val < 16
      · have hj8 : 8 ≤ j.val := by omega
        have hj16 : j.val < 16 := by omega
        by_cases hi8 : i.val = 8
        · by_cases hj8' : j.val = 8
          · have hsi : (⟨8, by omega⟩ : I32) = i := Fin.ext hi8.symm
            have hsj : (⟨8, by omega⟩ : I32) = j := Fin.ext hj8'.symm
            rw [← hsi, ← hsj]
            exact (pi1_mul_nuR a b).symm
          · by_cases hj9 : j.val = 9
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed (Or.inl ⟨hi8, hj9⟩)
              rw [pi1_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                pi1_mul_eq_zero_of_not_sameBlock a b hns]
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                (Or.inr (Or.inr (Or.inl ⟨Or.inl hi8, by omega, hj16⟩)))
              rw [pi1_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                pi1_mul_eq_zero_of_not_sameBlock a b hns]
        · by_cases hi9 : i.val = 9
          · by_cases hj8' : j.val = 8
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed (Or.inr (Or.inl ⟨hi9, hj8'⟩))
              rw [pi1_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                pi1_mul_eq_zero_of_not_sameBlock a b hns]
            · by_cases hj9 : j.val = 9
              · have hsi : (⟨9, by omega⟩ : I32) = i := Fin.ext hi9.symm
                have hsj : (⟨9, by omega⟩ : I32) = j := Fin.ext hj9.symm
                rw [← hsi, ← hsj]
                exact (pi1_mul_eR a b).symm
              · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                  (Or.inr (Or.inr (Or.inl ⟨Or.inr hi9, by omega, hj16⟩)))
                rw [pi1_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                  pi1_mul_eq_zero_of_not_sameBlock a b hns]
          · by_cases hj8' : j.val = 8
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inl hj8'⟩)))
              rw [pi1_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                pi1_mul_eq_zero_of_not_sameBlock a b hns]
            · by_cases hj9 : j.val = 9
              · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                  (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inr hj9⟩)))
                rw [pi1_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                  pi1_mul_eq_zero_of_not_sameBlock a b hns]
              · have hci : (⟨10 + 2 * (⟨(i.val - 10) / 2, by omega⟩ : Fin 3).val
                    + (⟨(i.val - 10) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
                  apply Fin.ext
                  show 10 + 2 * ((i.val - 10) / 2) + (i.val - 10) % 2 = i.val
                  have h := Nat.div_add_mod (i.val - 10) 2
                  omega
                have hcj : (⟨10 + 2 * (⟨(j.val - 10) / 2, by omega⟩ : Fin 3).val
                    + (⟨(j.val - 10) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
                  apply Fin.ext
                  show 10 + 2 * ((j.val - 10) / 2) + (j.val - 10) % 2 = j.val
                  have h := Nat.div_add_mod (j.val - 10) 2
                  omega
                rw [← hci, ← hcj]
                exact (pi1_mul_quarkR a b ⟨(i.val - 10) / 2, by omega⟩
                  ⟨(j.val - 10) / 2, by omega⟩ ⟨(i.val - 10) % 2, by omega⟩
                  ⟨(j.val - 10) % 2, by omega⟩).symm
      · by_cases hi24 : i.val < 24
        · have hj16 : 16 ≤ j.val := by omega
          have hj24 : j.val < 24 := by omega
          by_cases hi18 : i.val < 18
          · by_cases hj18 : j.val < 18
            · have hsi : (⟨16 + (⟨i.val - 16, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i :=
                Fin.ext (by show 16 + (i.val - 16) = i.val; omega)
              have hsj : (⟨16 + (⟨j.val - 16, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j :=
                Fin.ext (by show 16 + (j.val - 16) = j.val; omega)
              rw [← hsi, ← hsj]
              exact (pi1_mul_leptonLc a b ⟨i.val - 16, by omega⟩
                ⟨j.val - 16, by omega⟩).symm
            · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                (Or.inl ⟨by omega, hi18, by omega, hj24⟩)
              rw [pi1_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                pi1_mul_eq_zero_of_not_sameBlock a b hns]
          · by_cases hj18 : j.val < 18
            · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                (Or.inr (Or.inl ⟨by omega, hi24, hj16, hj18⟩))
              rw [pi1_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                pi1_mul_eq_zero_of_not_sameBlock a b hns]
            · have hci : (⟨18 + 2 * (⟨(i.val - 18) / 2, by omega⟩ : Fin 3).val
                  + (⟨(i.val - 18) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
                apply Fin.ext
                show 18 + 2 * ((i.val - 18) / 2) + (i.val - 18) % 2 = i.val
                have h := Nat.div_add_mod (i.val - 18) 2
                omega
              have hcj : (⟨18 + 2 * (⟨(j.val - 18) / 2, by omega⟩ : Fin 3).val
                  + (⟨(j.val - 18) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
                apply Fin.ext
                show 18 + 2 * ((j.val - 18) / 2) + (j.val - 18) % 2 = j.val
                have h := Nat.div_add_mod (j.val - 18) 2
                omega
              rw [← hci, ← hcj]
              exact (pi1_mul_quarkLc a b ⟨(i.val - 18) / 2, by omega⟩
                ⟨(j.val - 18) / 2, by omega⟩ ⟨(i.val - 18) % 2, by omega⟩
                ⟨(j.val - 18) % 2, by omega⟩).symm
        · have hj24 : 24 ≤ j.val := by omega
          by_cases hi24' : i.val = 24
          · by_cases hj24' : j.val = 24
            · have hsi : (⟨24, by omega⟩ : I32) = i := Fin.ext hi24'.symm
              have hsj : (⟨24, by omega⟩ : I32) = j := Fin.ext hj24'.symm
              rw [← hsi, ← hsj]
              exact (pi1_mul_nuRc a b).symm
            · by_cases hj25 : j.val = 25
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inl ⟨hi24', hj25⟩)))))))
                rw [pi1_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                  pi1_mul_eq_zero_of_not_sameBlock a b hns]
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                  (Or.inr (Or.inr (Or.inl ⟨hi24', by omega⟩)))
                rw [pi1_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                  pi1_mul_eq_zero_of_not_sameBlock a b hns]
          · by_cases hi25 : i.val = 25
            · by_cases hj24' : j.val = 24
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr ⟨hi25, hj24'⟩)))))))
                rw [pi1_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                  pi1_mul_eq_zero_of_not_sameBlock a b hns]
              · by_cases hj25 : j.val = 25
                · have hsi : (⟨25, by omega⟩ : I32) = i := Fin.ext hi25.symm
                  have hsj : (⟨25, by omega⟩ : I32) = j := Fin.ext hj25.symm
                  rw [← hsi, ← hsj]
                  exact (pi1_mul_eRc a b).symm
                · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                    (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi25, by omega⟩))))
                  rw [pi1_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                    pi1_mul_eq_zero_of_not_sameBlock a b hns]
            · by_cases hj24' : j.val = 24
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inl ⟨by omega, hj24'⟩)))))
                rw [pi1_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                  pi1_mul_eq_zero_of_not_sameBlock a b hns]
              · by_cases hj25 : j.val = 25
                · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inl ⟨by omega, hj25⟩))))))
                  rw [pi1_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                    pi1_mul_eq_zero_of_not_sameBlock a b hns]
                · have hci : (⟨26 + 2 * (⟨(i.val - 26) / 2, by omega⟩ : Fin 3).val
                      + (⟨(i.val - 26) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
                    apply Fin.ext
                    show 26 + 2 * ((i.val - 26) / 2) + (i.val - 26) % 2 = i.val
                    have h := Nat.div_add_mod (i.val - 26) 2
                    omega
                  have hcj : (⟨26 + 2 * (⟨(j.val - 26) / 2, by omega⟩ : Fin 3).val
                      + (⟨(j.val - 26) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
                    apply Fin.ext
                    show 26 + 2 * ((j.val - 26) / 2) + (j.val - 26) % 2 = j.val
                    have h := Nat.div_add_mod (j.val - 26) 2
                    omega
                  rw [← hci, ← hcj]
                  exact (pi1_mul_quarkRc a b ⟨(i.val - 26) / 2, by omega⟩
                    ⟨(j.val - 26) / 2, by omega⟩ ⟨(i.val - 26) % 2, by omega⟩
                    ⟨(j.val - 26) % 2, by omega⟩).symm
  · have hns : ¬ sameBlock i j := not_sameBlock_of_ne_sector hsec
    rw [pi1_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
      pi1_mul_eq_zero_of_not_sameBlock a b hns]

/-! ### Additivity (new for Route B)

π₀ failed additivity, and the failure was proved to be the
hypercharge seat's price **at the e_L particle entry**. π₁ pays
no such price anywhere: every block entry depends on exactly
one summand component. The block lemmas are one-liners off the
entry lemmas; the assembly is the same entry tree. -/

/-- Additivity on the H_L lepton doublet. -/
theorem pi1_add_leptonL (a b : AF) (s t : Fin 2) :
    pi1 (afAdd a b) ⟨s.val, by omega⟩ ⟨t.val, by omega⟩
      = pi1 a ⟨s.val, by omega⟩ ⟨t.val, by omega⟩
        + pi1 b ⟨s.val, by omega⟩ ⟨t.val, by omega⟩ := by
  rw [pi1_entry_leptonL (afAdd a b), pi1_entry_leptonL a, pi1_entry_leptonL b,
    afAdd_q, Matrix.add_apply]

/-- Additivity on the H_L quark block. -/
theorem pi1_add_quarkL (a b : AF) (k l : Fin 3) (s t : Fin 2) :
    pi1 (afAdd a b) ⟨2 + 2 * k.val + s.val, by omega⟩
        ⟨2 + 2 * l.val + t.val, by omega⟩
      = pi1 a ⟨2 + 2 * k.val + s.val, by omega⟩ ⟨2 + 2 * l.val + t.val, by omega⟩
        + pi1 b ⟨2 + 2 * k.val + s.val, by omega⟩
          ⟨2 + 2 * l.val + t.val, by omega⟩ := by
  rw [pi1_entry_quarkL (afAdd a b), pi1_entry_quarkL a, pi1_entry_quarkL b]
  by_cases h : k = l
  · subst h
    simp [afAdd_q, Matrix.add_apply]
  · simp [h]

/-- Additivity at ν_R. -/
theorem pi1_add_nuR (a b : AF) :
    pi1 (afAdd a b) ⟨8, by omega⟩ ⟨8, by omega⟩
      = pi1 a ⟨8, by omega⟩ ⟨8, by omega⟩
        + pi1 b ⟨8, by omega⟩ ⟨8, by omega⟩ := by
  rw [pi1_entry_nuR (afAdd a b), pi1_entry_nuR a, pi1_entry_nuR b, afAdd_u1]

/-- Additivity at e_R. -/
theorem pi1_add_eR (a b : AF) :
    pi1 (afAdd a b) ⟨9, by omega⟩ ⟨9, by omega⟩
      = pi1 a ⟨9, by omega⟩ ⟨9, by omega⟩
        + pi1 b ⟨9, by omega⟩ ⟨9, by omega⟩ := by
  rw [pi1_entry_eR (afAdd a b), pi1_entry_eR a, pi1_entry_eR b, afAdd_u1,
    star_add]

/-- Additivity on the H_R quark block. -/
theorem pi1_add_quarkR (a b : AF) (k l : Fin 3) (s t : Fin 2) :
    pi1 (afAdd a b) ⟨10 + 2 * k.val + s.val, by omega⟩
        ⟨10 + 2 * l.val + t.val, by omega⟩
      = pi1 a ⟨10 + 2 * k.val + s.val, by omega⟩ ⟨10 + 2 * l.val + t.val, by omega⟩
        + pi1 b ⟨10 + 2 * k.val + s.val, by omega⟩
          ⟨10 + 2 * l.val + t.val, by omega⟩ := by
  rw [pi1_entry_quarkR (afAdd a b), pi1_entry_quarkR a, pi1_entry_quarkR b]
  by_cases h : s = t ∧ k = l
  · obtain ⟨h1, h2⟩ := h
    subst h1
    subst h2
    by_cases hs : s = 0 <;> simp [hs, afAdd_u1, star_add]
  · simp [h]

/-- Additivity on the H_L antilepton doublet (changed block). -/
theorem pi1_add_leptonLc (a b : AF) (s t : Fin 2) :
    pi1 (afAdd a b) ⟨16 + s.val, by omega⟩ ⟨16 + t.val, by omega⟩
      = pi1 a ⟨16 + s.val, by omega⟩ ⟨16 + t.val, by omega⟩
        + pi1 b ⟨16 + s.val, by omega⟩ ⟨16 + t.val, by omega⟩ := by
  rw [pi1_entry_leptonLc (afAdd a b), pi1_entry_leptonLc a,
    pi1_entry_leptonLc b]
  by_cases h : s = t <;> simp [h, afAdd_u1, star_add]

/-- Additivity on the H_L antiquark block (changed block). -/
theorem pi1_add_quarkLc (a b : AF) (k l : Fin 3) (s t : Fin 2) :
    pi1 (afAdd a b) ⟨18 + 2 * k.val + s.val, by omega⟩
        ⟨18 + 2 * l.val + t.val, by omega⟩
      = pi1 a ⟨18 + 2 * k.val + s.val, by omega⟩ ⟨18 + 2 * l.val + t.val, by omega⟩
        + pi1 b ⟨18 + 2 * k.val + s.val, by omega⟩
          ⟨18 + 2 * l.val + t.val, by omega⟩ := by
  rw [pi1_entry_quarkLc (afAdd a b), pi1_entry_quarkLc a, pi1_entry_quarkLc b]
  by_cases h : s = t <;> simp [h, afAdd_color, Matrix.add_apply, star_add]

/-- Additivity at the ν_R antiparticle singlet. -/
theorem pi1_add_nuRc (a b : AF) :
    pi1 (afAdd a b) ⟨24, by omega⟩ ⟨24, by omega⟩
      = pi1 a ⟨24, by omega⟩ ⟨24, by omega⟩
        + pi1 b ⟨24, by omega⟩ ⟨24, by omega⟩ := by
  rw [pi1_entry_nuRc (afAdd a b), pi1_entry_nuRc a, pi1_entry_nuRc b, afAdd_u1,
    star_add]

/-- Additivity at the e_R antiparticle singlet. -/
theorem pi1_add_eRc (a b : AF) :
    pi1 (afAdd a b) ⟨25, by omega⟩ ⟨25, by omega⟩
      = pi1 a ⟨25, by omega⟩ ⟨25, by omega⟩
        + pi1 b ⟨25, by omega⟩ ⟨25, by omega⟩ := by
  rw [pi1_entry_eRc (afAdd a b), pi1_entry_eRc a, pi1_entry_eRc b, afAdd_u1,
    star_add]

/-- Additivity on the H_R antiquark block (changed block). -/
theorem pi1_add_quarkRc (a b : AF) (k l : Fin 3) (s t : Fin 2) :
    pi1 (afAdd a b) ⟨26 + 2 * k.val + s.val, by omega⟩
        ⟨26 + 2 * l.val + t.val, by omega⟩
      = pi1 a ⟨26 + 2 * k.val + s.val, by omega⟩ ⟨26 + 2 * l.val + t.val, by omega⟩
        + pi1 b ⟨26 + 2 * k.val + s.val, by omega⟩
          ⟨26 + 2 * l.val + t.val, by omega⟩ := by
  rw [pi1_entry_quarkRc (afAdd a b), pi1_entry_quarkRc a, pi1_entry_quarkRc b]
  by_cases h : s = t <;> simp [h, afAdd_color, Matrix.add_apply, star_add]

/-- T1 (additive part): `pi1` preserves the componentwise sum.
Same entry tree as `pi1_afMul`. -/
theorem pi1_afAdd (a b : AF) : pi1 (afAdd a b) = pi1 a + pi1 b := by
  ext i j
  by_cases hsec : i.val / 8 = j.val / 8
  · by_cases hi : i.val < 8
    · have hj : j.val < 8 := by omega
      by_cases hi2 : i.val < 2
      · by_cases hj2 : j.val < 2
        · have hsi : (⟨(⟨i.val, hi2⟩ : Fin 2).val, by omega⟩ : I32) = i :=
            Fin.ext (show (⟨i.val, hi2⟩ : Fin 2).val = i.val from rfl)
          have hsj : (⟨(⟨j.val, hj2⟩ : Fin 2).val, by omega⟩ : I32) = j :=
            Fin.ext (show (⟨j.val, hj2⟩ : Fin 2).val = j.val from rfl)
          rw [← hsi, ← hsj]
          rw [Matrix.add_apply]; exact pi1_add_leptonL a b _ _
        · have hns : ¬ sameBlock i j := not_sameBlock_of_HL_mixed (Or.inl ⟨hi2, by omega, hj⟩)
          rw [pi1_entry_eq_zero_of_not_sameBlock (afAdd a b) hns,
            Matrix.add_apply, pi1_entry_eq_zero_of_not_sameBlock a hns, pi1_entry_eq_zero_of_not_sameBlock b hns, add_zero]
      · by_cases hj2 : j.val < 2
        · have hns : ¬ sameBlock i j := not_sameBlock_of_HL_mixed (Or.inr ⟨by omega, hi, hj2⟩)
          rw [pi1_entry_eq_zero_of_not_sameBlock (afAdd a b) hns,
            Matrix.add_apply, pi1_entry_eq_zero_of_not_sameBlock a hns, pi1_entry_eq_zero_of_not_sameBlock b hns, add_zero]
        · have hci : (⟨2 + 2 * (⟨(i.val - 2) / 2, by omega⟩ : Fin 3).val
              + (⟨(i.val - 2) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
            apply Fin.ext
            show 2 + 2 * ((i.val - 2) / 2) + (i.val - 2) % 2 = i.val
            have h := Nat.div_add_mod (i.val - 2) 2
            omega
          have hcj : (⟨2 + 2 * (⟨(j.val - 2) / 2, by omega⟩ : Fin 3).val
              + (⟨(j.val - 2) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
            apply Fin.ext
            show 2 + 2 * ((j.val - 2) / 2) + (j.val - 2) % 2 = j.val
            have h := Nat.div_add_mod (j.val - 2) 2
            omega
          rw [← hci, ← hcj]
          rw [Matrix.add_apply]; exact pi1_add_quarkL a b _ _ _ _
    · by_cases hi16 : i.val < 16
      · have hj8 : 8 ≤ j.val := by omega
        have hj16 : j.val < 16 := by omega
        by_cases hi8 : i.val = 8
        · by_cases hj8' : j.val = 8
          · have hsi : (⟨8, by omega⟩ : I32) = i := Fin.ext hi8.symm
            have hsj : (⟨8, by omega⟩ : I32) = j := Fin.ext hj8'.symm
            rw [← hsi, ← hsj]
            rw [Matrix.add_apply]; exact pi1_add_nuR a b
          · by_cases hj9 : j.val = 9
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed (Or.inl ⟨hi8, hj9⟩)
              rw [pi1_entry_eq_zero_of_not_sameBlock (afAdd a b) hns,
                Matrix.add_apply, pi1_entry_eq_zero_of_not_sameBlock a hns, pi1_entry_eq_zero_of_not_sameBlock b hns, add_zero]
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                (Or.inr (Or.inr (Or.inl ⟨Or.inl hi8, by omega, hj16⟩)))
              rw [pi1_entry_eq_zero_of_not_sameBlock (afAdd a b) hns,
                Matrix.add_apply, pi1_entry_eq_zero_of_not_sameBlock a hns, pi1_entry_eq_zero_of_not_sameBlock b hns, add_zero]
        · by_cases hi9 : i.val = 9
          · by_cases hj8' : j.val = 8
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed (Or.inr (Or.inl ⟨hi9, hj8'⟩))
              rw [pi1_entry_eq_zero_of_not_sameBlock (afAdd a b) hns,
                Matrix.add_apply, pi1_entry_eq_zero_of_not_sameBlock a hns, pi1_entry_eq_zero_of_not_sameBlock b hns, add_zero]
            · by_cases hj9 : j.val = 9
              · have hsi : (⟨9, by omega⟩ : I32) = i := Fin.ext hi9.symm
                have hsj : (⟨9, by omega⟩ : I32) = j := Fin.ext hj9.symm
                rw [← hsi, ← hsj]
                rw [Matrix.add_apply]; exact pi1_add_eR a b
              · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                  (Or.inr (Or.inr (Or.inl ⟨Or.inr hi9, by omega, hj16⟩)))
                rw [pi1_entry_eq_zero_of_not_sameBlock (afAdd a b) hns,
                  Matrix.add_apply, pi1_entry_eq_zero_of_not_sameBlock a hns, pi1_entry_eq_zero_of_not_sameBlock b hns, add_zero]
          · by_cases hj8' : j.val = 8
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inl hj8'⟩)))
              rw [pi1_entry_eq_zero_of_not_sameBlock (afAdd a b) hns,
                Matrix.add_apply, pi1_entry_eq_zero_of_not_sameBlock a hns, pi1_entry_eq_zero_of_not_sameBlock b hns, add_zero]
            · by_cases hj9 : j.val = 9
              · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                  (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inr hj9⟩)))
                rw [pi1_entry_eq_zero_of_not_sameBlock (afAdd a b) hns,
                  Matrix.add_apply, pi1_entry_eq_zero_of_not_sameBlock a hns, pi1_entry_eq_zero_of_not_sameBlock b hns, add_zero]
              · have hci : (⟨10 + 2 * (⟨(i.val - 10) / 2, by omega⟩ : Fin 3).val
                    + (⟨(i.val - 10) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
                  apply Fin.ext
                  show 10 + 2 * ((i.val - 10) / 2) + (i.val - 10) % 2 = i.val
                  have h := Nat.div_add_mod (i.val - 10) 2
                  omega
                have hcj : (⟨10 + 2 * (⟨(j.val - 10) / 2, by omega⟩ : Fin 3).val
                    + (⟨(j.val - 10) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
                  apply Fin.ext
                  show 10 + 2 * ((j.val - 10) / 2) + (j.val - 10) % 2 = j.val
                  have h := Nat.div_add_mod (j.val - 10) 2
                  omega
                rw [← hci, ← hcj]
                rw [Matrix.add_apply]; exact pi1_add_quarkR a b _ _ _ _
      · by_cases hi24 : i.val < 24
        · have hj16 : 16 ≤ j.val := by omega
          have hj24 : j.val < 24 := by omega
          by_cases hi18 : i.val < 18
          · by_cases hj18 : j.val < 18
            · have hsi : (⟨16 + (⟨i.val - 16, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i :=
                Fin.ext (by show 16 + (i.val - 16) = i.val; omega)
              have hsj : (⟨16 + (⟨j.val - 16, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j :=
                Fin.ext (by show 16 + (j.val - 16) = j.val; omega)
              rw [← hsi, ← hsj]
              rw [Matrix.add_apply]; exact pi1_add_leptonLc a b _ _
            · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                (Or.inl ⟨by omega, hi18, by omega, hj24⟩)
              rw [pi1_entry_eq_zero_of_not_sameBlock (afAdd a b) hns,
                Matrix.add_apply, pi1_entry_eq_zero_of_not_sameBlock a hns, pi1_entry_eq_zero_of_not_sameBlock b hns, add_zero]
          · by_cases hj18 : j.val < 18
            · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                (Or.inr (Or.inl ⟨by omega, hi24, hj16, hj18⟩))
              rw [pi1_entry_eq_zero_of_not_sameBlock (afAdd a b) hns,
                Matrix.add_apply, pi1_entry_eq_zero_of_not_sameBlock a hns, pi1_entry_eq_zero_of_not_sameBlock b hns, add_zero]
            · have hci : (⟨18 + 2 * (⟨(i.val - 18) / 2, by omega⟩ : Fin 3).val
                  + (⟨(i.val - 18) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
                apply Fin.ext
                show 18 + 2 * ((i.val - 18) / 2) + (i.val - 18) % 2 = i.val
                have h := Nat.div_add_mod (i.val - 18) 2
                omega
              have hcj : (⟨18 + 2 * (⟨(j.val - 18) / 2, by omega⟩ : Fin 3).val
                  + (⟨(j.val - 18) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
                apply Fin.ext
                show 18 + 2 * ((j.val - 18) / 2) + (j.val - 18) % 2 = j.val
                have h := Nat.div_add_mod (j.val - 18) 2
                omega
              rw [← hci, ← hcj]
              rw [Matrix.add_apply]; exact pi1_add_quarkLc a b _ _ _ _
        · have hj24 : 24 ≤ j.val := by omega
          by_cases hi24' : i.val = 24
          · by_cases hj24' : j.val = 24
            · have hsi : (⟨24, by omega⟩ : I32) = i := Fin.ext hi24'.symm
              have hsj : (⟨24, by omega⟩ : I32) = j := Fin.ext hj24'.symm
              rw [← hsi, ← hsj]
              rw [Matrix.add_apply]; exact pi1_add_nuRc a b
            · by_cases hj25 : j.val = 25
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inl ⟨hi24', hj25⟩)))))))
                rw [pi1_entry_eq_zero_of_not_sameBlock (afAdd a b) hns,
                  Matrix.add_apply, pi1_entry_eq_zero_of_not_sameBlock a hns, pi1_entry_eq_zero_of_not_sameBlock b hns, add_zero]
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                  (Or.inr (Or.inr (Or.inl ⟨hi24', by omega⟩)))
                rw [pi1_entry_eq_zero_of_not_sameBlock (afAdd a b) hns,
                  Matrix.add_apply, pi1_entry_eq_zero_of_not_sameBlock a hns, pi1_entry_eq_zero_of_not_sameBlock b hns, add_zero]
          · by_cases hi25 : i.val = 25
            · by_cases hj24' : j.val = 24
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr ⟨hi25, hj24'⟩)))))))
                rw [pi1_entry_eq_zero_of_not_sameBlock (afAdd a b) hns,
                  Matrix.add_apply, pi1_entry_eq_zero_of_not_sameBlock a hns, pi1_entry_eq_zero_of_not_sameBlock b hns, add_zero]
              · by_cases hj25 : j.val = 25
                · have hsi : (⟨25, by omega⟩ : I32) = i := Fin.ext hi25.symm
                  have hsj : (⟨25, by omega⟩ : I32) = j := Fin.ext hj25.symm
                  rw [← hsi, ← hsj]
                  rw [Matrix.add_apply]; exact pi1_add_eRc a b
                · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                    (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi25, by omega⟩))))
                  rw [pi1_entry_eq_zero_of_not_sameBlock (afAdd a b) hns,
                    Matrix.add_apply, pi1_entry_eq_zero_of_not_sameBlock a hns, pi1_entry_eq_zero_of_not_sameBlock b hns, add_zero]
            · by_cases hj24' : j.val = 24
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inl ⟨by omega, hj24'⟩)))))
                rw [pi1_entry_eq_zero_of_not_sameBlock (afAdd a b) hns,
                  Matrix.add_apply, pi1_entry_eq_zero_of_not_sameBlock a hns, pi1_entry_eq_zero_of_not_sameBlock b hns, add_zero]
              · by_cases hj25 : j.val = 25
                · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inl ⟨by omega, hj25⟩))))))
                  rw [pi1_entry_eq_zero_of_not_sameBlock (afAdd a b) hns,
                    Matrix.add_apply, pi1_entry_eq_zero_of_not_sameBlock a hns, pi1_entry_eq_zero_of_not_sameBlock b hns, add_zero]
                · have hci : (⟨26 + 2 * (⟨(i.val - 26) / 2, by omega⟩ : Fin 3).val
                      + (⟨(i.val - 26) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
                    apply Fin.ext
                    show 26 + 2 * ((i.val - 26) / 2) + (i.val - 26) % 2 = i.val
                    have h := Nat.div_add_mod (i.val - 26) 2
                    omega
                  have hcj : (⟨26 + 2 * (⟨(j.val - 26) / 2, by omega⟩ : Fin 3).val
                      + (⟨(j.val - 26) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
                    apply Fin.ext
                    show 26 + 2 * ((j.val - 26) / 2) + (j.val - 26) % 2 = j.val
                    have h := Nat.div_add_mod (j.val - 26) 2
                    omega
                  rw [← hci, ← hcj]
                  rw [Matrix.add_apply]; exact pi1_add_quarkRc a b _ _ _ _
  · have hns : ¬ sameBlock i j := not_sameBlock_of_ne_sector hsec
    rw [pi1_entry_eq_zero_of_not_sameBlock (afAdd a b) hns,
      Matrix.add_apply, pi1_entry_eq_zero_of_not_sameBlock a hns, pi1_entry_eq_zero_of_not_sameBlock b hns, add_zero]

/-! ### The star law -/

theorem pi1_star_entry_leptonL (a : AF) (s t : Fin 2) :
    pi1 (afStar a) ⟨s.val, by omega⟩ ⟨t.val, by omega⟩
      = star (pi1 a ⟨t.val, by omega⟩ ⟨s.val, by omega⟩) := by
  rw [pi1_entry_leptonL, pi1_entry_leptonL, afStar_q, Matrix.conjTranspose_apply]

theorem pi1_star_entry_quarkL (a : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    pi1 (afStar a) ⟨2 + 2 * ki.val + si.val, by omega⟩
        ⟨2 + 2 * kj.val + sj.val, by omega⟩
      = star (pi1 a ⟨2 + 2 * kj.val + sj.val, by omega⟩
        ⟨2 + 2 * ki.val + si.val, by omega⟩) := by
  rw [pi1_entry_quarkL, pi1_entry_quarkL]
  by_cases h : ki = kj
  · rw [if_pos h, if_pos h.symm, afStar_q, Matrix.conjTranspose_apply]
  · rw [if_neg h, if_neg (fun hh => h hh.symm), star_zero]

theorem pi1_star_entry_nuR (a : AF) :
    pi1 (afStar a) ⟨8, by omega⟩ ⟨8, by omega⟩
      = star (pi1 a ⟨8, by omega⟩ ⟨8, by omega⟩) := by
  rw [pi1_entry_nuR, pi1_entry_nuR, afStar_u1]

theorem pi1_star_entry_eR (a : AF) :
    pi1 (afStar a) ⟨9, by omega⟩ ⟨9, by omega⟩
      = star (pi1 a ⟨9, by omega⟩ ⟨9, by omega⟩) := by
  rw [pi1_entry_eR, pi1_entry_eR, afStar_u1]

theorem pi1_star_entry_quarkR (a : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    pi1 (afStar a) ⟨10 + 2 * ki.val + si.val, by omega⟩
        ⟨10 + 2 * kj.val + sj.val, by omega⟩
      = star (pi1 a ⟨10 + 2 * kj.val + sj.val, by omega⟩
        ⟨10 + 2 * ki.val + si.val, by omega⟩) := by
  rw [pi1_entry_quarkR, pi1_entry_quarkR]
  by_cases h : si = sj ∧ ki = kj
  · obtain ⟨h1, h2⟩ := h
    have h' : sj = si ∧ kj = ki := ⟨h1.symm, h2.symm⟩
    rw [if_pos ⟨h1, h2⟩, if_pos h']
    subst h1
    split_ifs <;> simp only [afStar_u1, star_star]
  · have h' : ¬ (sj = si ∧ kj = ki) := fun hh => h ⟨hh.1.symm, hh.2.symm⟩
    rw [if_neg h, if_neg h', star_zero]

/-- Star entry on the H_L antilepton doublet (changed block). -/
theorem pi1_star_entry_leptonLc (a : AF) (s t : Fin 2) :
    pi1 (afStar a) ⟨16 + s.val, by omega⟩ ⟨16 + t.val, by omega⟩
      = star (pi1 a ⟨16 + t.val, by omega⟩ ⟨16 + s.val, by omega⟩) := by
  rw [pi1_entry_leptonLc, pi1_entry_leptonLc]
  by_cases h : s = t
  · subst h
    simp [afStar_u1]
  · simp [h, Ne.symm h, afStar_u1]

/-- Star entry on the H_L antiquark block (changed block). -/
theorem pi1_star_entry_quarkLc (a : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    pi1 (afStar a) ⟨18 + 2 * ki.val + si.val, by omega⟩
        ⟨18 + 2 * kj.val + sj.val, by omega⟩
      = star (pi1 a ⟨18 + 2 * kj.val + sj.val, by omega⟩
        ⟨18 + 2 * ki.val + si.val, by omega⟩) := by
  rw [pi1_entry_quarkLc, pi1_entry_quarkLc]
  by_cases h : si = sj
  · subst h
    simp [afStar_color, Matrix.conjTranspose_apply]
  · simp [h, Ne.symm h, afStar_color, Matrix.conjTranspose_apply]

theorem pi1_star_entry_nuRc (a : AF) :
    pi1 (afStar a) ⟨24, by omega⟩ ⟨24, by omega⟩
      = star (pi1 a ⟨24, by omega⟩ ⟨24, by omega⟩) := by
  rw [pi1_entry_nuRc, pi1_entry_nuRc, afStar_u1]

theorem pi1_star_entry_eRc (a : AF) :
    pi1 (afStar a) ⟨25, by omega⟩ ⟨25, by omega⟩
      = star (pi1 a ⟨25, by omega⟩ ⟨25, by omega⟩) := by
  rw [pi1_entry_eRc, pi1_entry_eRc, afStar_u1]

/-- Star entry on the H_R antiquark block (changed block). -/
theorem pi1_star_entry_quarkRc (a : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    pi1 (afStar a) ⟨26 + 2 * ki.val + si.val, by omega⟩
        ⟨26 + 2 * kj.val + sj.val, by omega⟩
      = star (pi1 a ⟨26 + 2 * kj.val + sj.val, by omega⟩
        ⟨26 + 2 * ki.val + si.val, by omega⟩) := by
  rw [pi1_entry_quarkRc, pi1_entry_quarkRc]
  by_cases h : si = sj
  · subst h
    simp [afStar_color, Matrix.conjTranspose_apply]
  · simp [h, Ne.symm h, afStar_color, Matrix.conjTranspose_apply]

/-- T1 (star part): `pi1` preserves the involution. Entry case
tree as for `pi1_afMul`. -/
theorem pi1_afStar (a : AF) : pi1 (afStar a) = (pi1 a)ᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hsec : i.val / 8 = j.val / 8
  · by_cases hi : i.val < 8
    · have hj : j.val < 8 := by omega
      by_cases hi2 : i.val < 2
      · by_cases hj2 : j.val < 2
        · have hsi : (⟨(⟨i.val, hi2⟩ : Fin 2).val, by omega⟩ : I32) = i :=
            Fin.ext (show (⟨i.val, hi2⟩ : Fin 2).val = i.val from rfl)
          have hsj : (⟨(⟨j.val, hj2⟩ : Fin 2).val, by omega⟩ : I32) = j :=
            Fin.ext (show (⟨j.val, hj2⟩ : Fin 2).val = j.val from rfl)
          rw [← hsi, ← hsj]
          exact pi1_star_entry_leptonL a ⟨i.val, hi2⟩ ⟨j.val, hj2⟩
        · have hns : ¬ sameBlock i j := not_sameBlock_of_HL_mixed (Or.inl ⟨hi2, by omega, hj⟩)
          have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
          rw [pi1_entry_eq_zero_of_not_sameBlock (afStar a) hns,
            pi1_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
      · by_cases hj2 : j.val < 2
        · have hns : ¬ sameBlock i j := not_sameBlock_of_HL_mixed (Or.inr ⟨by omega, hi, hj2⟩)
          have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
          rw [pi1_entry_eq_zero_of_not_sameBlock (afStar a) hns,
            pi1_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
        · have hci : (⟨2 + 2 * (⟨(i.val - 2) / 2, by omega⟩ : Fin 3).val
              + (⟨(i.val - 2) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
            apply Fin.ext
            show 2 + 2 * ((i.val - 2) / 2) + (i.val - 2) % 2 = i.val
            have h := Nat.div_add_mod (i.val - 2) 2
            omega
          have hcj : (⟨2 + 2 * (⟨(j.val - 2) / 2, by omega⟩ : Fin 3).val
              + (⟨(j.val - 2) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
            apply Fin.ext
            show 2 + 2 * ((j.val - 2) / 2) + (j.val - 2) % 2 = j.val
            have h := Nat.div_add_mod (j.val - 2) 2
            omega
          rw [← hci, ← hcj]
          exact pi1_star_entry_quarkL a ⟨(i.val - 2) / 2, by omega⟩
            ⟨(j.val - 2) / 2, by omega⟩ ⟨(i.val - 2) % 2, by omega⟩
            ⟨(j.val - 2) % 2, by omega⟩
    · by_cases hi16 : i.val < 16
      · have hj8 : 8 ≤ j.val := by omega
        have hj16 : j.val < 16 := by omega
        by_cases hi8 : i.val = 8
        · by_cases hj8' : j.val = 8
          · have hsi : (⟨8, by omega⟩ : I32) = i := Fin.ext hi8.symm
            have hsj : (⟨8, by omega⟩ : I32) = j := Fin.ext hj8'.symm
            rw [← hsi, ← hsj]
            exact pi1_star_entry_nuR a
          · by_cases hj9 : j.val = 9
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed (Or.inl ⟨hi8, hj9⟩)
              have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
              rw [pi1_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                pi1_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                (Or.inr (Or.inr (Or.inl ⟨Or.inl hi8, by omega, hj16⟩)))
              have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
              rw [pi1_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                pi1_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
        · by_cases hi9 : i.val = 9
          · by_cases hj8' : j.val = 8
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed (Or.inr (Or.inl ⟨hi9, hj8'⟩))
              have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
              rw [pi1_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                pi1_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
            · by_cases hj9 : j.val = 9
              · have hsi : (⟨9, by omega⟩ : I32) = i := Fin.ext hi9.symm
                have hsj : (⟨9, by omega⟩ : I32) = j := Fin.ext hj9.symm
                rw [← hsi, ← hsj]
                exact pi1_star_entry_eR a
              · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                  (Or.inr (Or.inr (Or.inl ⟨Or.inr hi9, by omega, hj16⟩)))
                have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
                rw [pi1_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                  pi1_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
          · by_cases hj8' : j.val = 8
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inl hj8'⟩)))
              have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
              rw [pi1_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                pi1_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
            · by_cases hj9 : j.val = 9
              · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                  (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inr hj9⟩)))
                have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
                rw [pi1_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                  pi1_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
              · have hci : (⟨10 + 2 * (⟨(i.val - 10) / 2, by omega⟩ : Fin 3).val
                    + (⟨(i.val - 10) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
                  apply Fin.ext
                  show 10 + 2 * ((i.val - 10) / 2) + (i.val - 10) % 2 = i.val
                  have h := Nat.div_add_mod (i.val - 10) 2
                  omega
                have hcj : (⟨10 + 2 * (⟨(j.val - 10) / 2, by omega⟩ : Fin 3).val
                    + (⟨(j.val - 10) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
                  apply Fin.ext
                  show 10 + 2 * ((j.val - 10) / 2) + (j.val - 10) % 2 = j.val
                  have h := Nat.div_add_mod (j.val - 10) 2
                  omega
                rw [← hci, ← hcj]
                exact pi1_star_entry_quarkR a ⟨(i.val - 10) / 2, by omega⟩
                  ⟨(j.val - 10) / 2, by omega⟩ ⟨(i.val - 10) % 2, by omega⟩
                  ⟨(j.val - 10) % 2, by omega⟩
      · by_cases hi24 : i.val < 24
        · have hj16 : 16 ≤ j.val := by omega
          have hj24 : j.val < 24 := by omega
          by_cases hi18 : i.val < 18
          · by_cases hj18 : j.val < 18
            · have hsi : (⟨16 + (⟨i.val - 16, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i :=
                Fin.ext (by show 16 + (i.val - 16) = i.val; omega)
              have hsj : (⟨16 + (⟨j.val - 16, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j :=
                Fin.ext (by show 16 + (j.val - 16) = j.val; omega)
              rw [← hsi, ← hsj]
              exact pi1_star_entry_leptonLc a ⟨i.val - 16, by omega⟩
                ⟨j.val - 16, by omega⟩
            · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                (Or.inl ⟨by omega, hi18, by omega, hj24⟩)
              have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
              rw [pi1_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                pi1_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
          · by_cases hj18 : j.val < 18
            · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                (Or.inr (Or.inl ⟨by omega, hi24, hj16, hj18⟩))
              have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
              rw [pi1_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                pi1_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
            · have hci : (⟨18 + 2 * (⟨(i.val - 18) / 2, by omega⟩ : Fin 3).val
                  + (⟨(i.val - 18) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
                apply Fin.ext
                show 18 + 2 * ((i.val - 18) / 2) + (i.val - 18) % 2 = i.val
                have h := Nat.div_add_mod (i.val - 18) 2
                omega
              have hcj : (⟨18 + 2 * (⟨(j.val - 18) / 2, by omega⟩ : Fin 3).val
                  + (⟨(j.val - 18) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
                apply Fin.ext
                show 18 + 2 * ((j.val - 18) / 2) + (j.val - 18) % 2 = j.val
                have h := Nat.div_add_mod (j.val - 18) 2
                omega
              rw [← hci, ← hcj]
              exact pi1_star_entry_quarkLc a ⟨(i.val - 18) / 2, by omega⟩
                ⟨(j.val - 18) / 2, by omega⟩ ⟨(i.val - 18) % 2, by omega⟩
                ⟨(j.val - 18) % 2, by omega⟩
        · have hj24 : 24 ≤ j.val := by omega
          by_cases hi24' : i.val = 24
          · by_cases hj24' : j.val = 24
            · have hsi : (⟨24, by omega⟩ : I32) = i := Fin.ext hi24'.symm
              have hsj : (⟨24, by omega⟩ : I32) = j := Fin.ext hj24'.symm
              rw [← hsi, ← hsj]
              exact pi1_star_entry_nuRc a
            · by_cases hj25 : j.val = 25
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inl ⟨hi24', hj25⟩)))))))
                have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
                rw [pi1_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                  pi1_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                  (Or.inr (Or.inr (Or.inl ⟨hi24', by omega⟩)))
                have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
                rw [pi1_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                  pi1_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
          · by_cases hi25 : i.val = 25
            · by_cases hj24' : j.val = 24
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr ⟨hi25, hj24'⟩)))))))
                have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
                rw [pi1_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                  pi1_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
              · by_cases hj25 : j.val = 25
                · have hsi : (⟨25, by omega⟩ : I32) = i := Fin.ext hi25.symm
                  have hsj : (⟨25, by omega⟩ : I32) = j := Fin.ext hj25.symm
                  rw [← hsi, ← hsj]
                  exact pi1_star_entry_eRc a
                · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                    (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi25, by omega⟩))))
                  have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
                  rw [pi1_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                    pi1_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
            · by_cases hj24' : j.val = 24
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inl ⟨by omega, hj24'⟩)))))
                have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
                rw [pi1_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                  pi1_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
              · by_cases hj25 : j.val = 25
                · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inl ⟨by omega, hj25⟩))))))
                  have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
                  rw [pi1_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                    pi1_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
                · have hci : (⟨26 + 2 * (⟨(i.val - 26) / 2, by omega⟩ : Fin 3).val
                      + (⟨(i.val - 26) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
                    apply Fin.ext
                    show 26 + 2 * ((i.val - 26) / 2) + (i.val - 26) % 2 = i.val
                    have h := Nat.div_add_mod (i.val - 26) 2
                    omega
                  have hcj : (⟨26 + 2 * (⟨(j.val - 26) / 2, by omega⟩ : Fin 3).val
                      + (⟨(j.val - 26) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
                    apply Fin.ext
                    show 26 + 2 * ((j.val - 26) / 2) + (j.val - 26) % 2 = j.val
                    have h := Nat.div_add_mod (j.val - 26) 2
                    omega
                  rw [← hci, ← hcj]
                  exact pi1_star_entry_quarkRc a ⟨(i.val - 26) / 2, by omega⟩
                    ⟨(j.val - 26) / 2, by omega⟩ ⟨(i.val - 26) % 2, by omega⟩
                    ⟨(j.val - 26) % 2, by omega⟩
  · have hns : ¬ sameBlock i j := not_sameBlock_of_ne_sector hsec
    have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
    rw [pi1_entry_eq_zero_of_not_sameBlock (afStar a) hns,
      pi1_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]

/-- T1 (zero): `pi1` sends the zero element to the zero matrix
(entry tree). -/
theorem pi1_zero : pi1 afZero = 0 := by
  ext i j
  by_cases hsec : i.val / 8 = j.val / 8
  · by_cases hi : i.val < 8
    · have hj : j.val < 8 := by omega
      by_cases hi2 : i.val < 2
      · by_cases hj2 : j.val < 2
        · have hsi : (⟨(⟨i.val, hi2⟩ : Fin 2).val, by omega⟩ : I32) = i :=
            Fin.ext (show (⟨i.val, hi2⟩ : Fin 2).val = i.val from rfl)
          have hsj : (⟨(⟨j.val, hj2⟩ : Fin 2).val, by omega⟩ : I32) = j :=
            Fin.ext (show (⟨j.val, hj2⟩ : Fin 2).val = j.val from rfl)
          rw [← hsi, ← hsj, pi1_entry_leptonL]
          simp only [afZero_q, Matrix.zero_apply]
        · have hns : ¬ sameBlock i j := not_sameBlock_of_HL_mixed (Or.inl ⟨hi2, by omega, hj⟩)
          rw [pi1_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
      · by_cases hj2 : j.val < 2
        · have hns : ¬ sameBlock i j := not_sameBlock_of_HL_mixed (Or.inr ⟨by omega, hi, hj2⟩)
          rw [pi1_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
        · have hci : (⟨2 + 2 * (⟨(i.val - 2) / 2, by omega⟩ : Fin 3).val
              + (⟨(i.val - 2) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
            apply Fin.ext
            show 2 + 2 * ((i.val - 2) / 2) + (i.val - 2) % 2 = i.val
            have h := Nat.div_add_mod (i.val - 2) 2
            omega
          have hcj : (⟨2 + 2 * (⟨(j.val - 2) / 2, by omega⟩ : Fin 3).val
              + (⟨(j.val - 2) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
            apply Fin.ext
            show 2 + 2 * ((j.val - 2) / 2) + (j.val - 2) % 2 = j.val
            have h := Nat.div_add_mod (j.val - 2) 2
            omega
          rw [← hci, ← hcj, pi1_entry_quarkL]
          split_ifs <;> simp only [afZero_q, Matrix.zero_apply]
    · by_cases hi16 : i.val < 16
      · have hj8 : 8 ≤ j.val := by omega
        have hj16 : j.val < 16 := by omega
        by_cases hi8 : i.val = 8
        · by_cases hj8' : j.val = 8
          · have hsi : (⟨8, by omega⟩ : I32) = i := Fin.ext hi8.symm
            have hsj : (⟨8, by omega⟩ : I32) = j := Fin.ext hj8'.symm
            rw [← hsi, ← hsj, pi1_entry_nuR]
            simp only [afZero_u1, Matrix.zero_apply]
          · by_cases hj9 : j.val = 9
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed (Or.inl ⟨hi8, hj9⟩)
              rw [pi1_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                (Or.inr (Or.inr (Or.inl ⟨Or.inl hi8, by omega, hj16⟩)))
              rw [pi1_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
        · by_cases hi9 : i.val = 9
          · by_cases hj8' : j.val = 8
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed (Or.inr (Or.inl ⟨hi9, hj8'⟩))
              rw [pi1_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
            · by_cases hj9 : j.val = 9
              · have hsi : (⟨9, by omega⟩ : I32) = i := Fin.ext hi9.symm
                have hsj : (⟨9, by omega⟩ : I32) = j := Fin.ext hj9.symm
                rw [← hsi, ← hsj, pi1_entry_eR]
                simp only [afZero_u1, star_zero, Matrix.zero_apply]
              · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                  (Or.inr (Or.inr (Or.inl ⟨Or.inr hi9, by omega, hj16⟩)))
                rw [pi1_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
          · by_cases hj8' : j.val = 8
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inl hj8'⟩)))
              rw [pi1_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
            · by_cases hj9 : j.val = 9
              · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                  (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inr hj9⟩)))
                rw [pi1_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
              · have hci : (⟨10 + 2 * (⟨(i.val - 10) / 2, by omega⟩ : Fin 3).val
                    + (⟨(i.val - 10) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
                  apply Fin.ext
                  show 10 + 2 * ((i.val - 10) / 2) + (i.val - 10) % 2 = i.val
                  have h := Nat.div_add_mod (i.val - 10) 2
                  omega
                have hcj : (⟨10 + 2 * (⟨(j.val - 10) / 2, by omega⟩ : Fin 3).val
                    + (⟨(j.val - 10) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
                  apply Fin.ext
                  show 10 + 2 * ((j.val - 10) / 2) + (j.val - 10) % 2 = j.val
                  have h := Nat.div_add_mod (j.val - 10) 2
                  omega
                rw [← hci, ← hcj, pi1_entry_quarkR]
                split_ifs <;> simp only [afZero_u1, star_zero, Matrix.zero_apply]
      · by_cases hi24 : i.val < 24
        · have hj16 : 16 ≤ j.val := by omega
          have hj24 : j.val < 24 := by omega
          by_cases hi18 : i.val < 18
          · by_cases hj18 : j.val < 18
            · have hsi : (⟨16 + (⟨i.val - 16, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i :=
                Fin.ext (by show 16 + (i.val - 16) = i.val; omega)
              have hsj : (⟨16 + (⟨j.val - 16, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j :=
                Fin.ext (by show 16 + (j.val - 16) = j.val; omega)
              rw [← hsi, ← hsj, pi1_entry_leptonLc]
              simp only [afZero_u1, star_zero, Matrix.zero_apply]
              split_ifs <;> rfl
            · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                (Or.inl ⟨by omega, hi18, by omega, hj24⟩)
              rw [pi1_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
          · by_cases hj18 : j.val < 18
            · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                (Or.inr (Or.inl ⟨by omega, hi24, hj16, hj18⟩))
              rw [pi1_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
            · have hci : (⟨18 + 2 * (⟨(i.val - 18) / 2, by omega⟩ : Fin 3).val
                  + (⟨(i.val - 18) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
                apply Fin.ext
                show 18 + 2 * ((i.val - 18) / 2) + (i.val - 18) % 2 = i.val
                have h := Nat.div_add_mod (i.val - 18) 2
                omega
              have hcj : (⟨18 + 2 * (⟨(j.val - 18) / 2, by omega⟩ : Fin 3).val
                  + (⟨(j.val - 18) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
                apply Fin.ext
                show 18 + 2 * ((j.val - 18) / 2) + (j.val - 18) % 2 = j.val
                have h := Nat.div_add_mod (j.val - 18) 2
                omega
              rw [← hci, ← hcj, pi1_entry_quarkLc]
              simp only [afZero_color, Matrix.zero_apply, star_zero]
              split_ifs <;> rfl
        · have hj24 : 24 ≤ j.val := by omega
          by_cases hi24' : i.val = 24
          · by_cases hj24' : j.val = 24
            · have hsi : (⟨24, by omega⟩ : I32) = i := Fin.ext hi24'.symm
              have hsj : (⟨24, by omega⟩ : I32) = j := Fin.ext hj24'.symm
              rw [← hsi, ← hsj, pi1_entry_nuRc]
              simp only [afZero_u1, star_zero, Matrix.zero_apply]
            · by_cases hj25 : j.val = 25
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inl ⟨hi24', hj25⟩)))))))
                rw [pi1_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                  (Or.inr (Or.inr (Or.inl ⟨hi24', by omega⟩)))
                rw [pi1_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
          · by_cases hi25 : i.val = 25
            · by_cases hj24' : j.val = 24
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr ⟨hi25, hj24'⟩)))))))
                rw [pi1_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
              · by_cases hj25 : j.val = 25
                · have hsi : (⟨25, by omega⟩ : I32) = i := Fin.ext hi25.symm
                  have hsj : (⟨25, by omega⟩ : I32) = j := Fin.ext hj25.symm
                  rw [← hsi, ← hsj, pi1_entry_eRc]
                  simp only [afZero_u1, star_zero, Matrix.zero_apply]
                · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                    (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi25, by omega⟩))))
                  rw [pi1_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
            · by_cases hj24' : j.val = 24
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inl ⟨by omega, hj24'⟩)))))
                rw [pi1_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
              · by_cases hj25 : j.val = 25
                · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inl ⟨by omega, hj25⟩))))))
                  rw [pi1_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
                · have hci : (⟨26 + 2 * (⟨(i.val - 26) / 2, by omega⟩ : Fin 3).val
                      + (⟨(i.val - 26) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
                    apply Fin.ext
                    show 26 + 2 * ((i.val - 26) / 2) + (i.val - 26) % 2 = i.val
                    have h := Nat.div_add_mod (i.val - 26) 2
                    omega
                  have hcj : (⟨26 + 2 * (⟨(j.val - 26) / 2, by omega⟩ : Fin 3).val
                      + (⟨(j.val - 26) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
                    apply Fin.ext
                    show 26 + 2 * ((j.val - 26) / 2) + (j.val - 26) % 2 = j.val
                    have h := Nat.div_add_mod (j.val - 26) 2
                    omega
                  rw [← hci, ← hcj, pi1_entry_quarkRc]
                  split_ifs <;> simp only [afZero_color, Matrix.zero_apply, star_zero]
  · have hns : ¬ sameBlock i j := not_sameBlock_of_ne_sector hsec
    rw [pi1_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]


/-! ## §4. The diagonal form of `pi1 ⟨lam, 1, c • 1⟩`

Needed for the unit law (here) and for the lift re-derivation
(§9). `pi1DiagVal` is `pi0DiagVal` with the two antiquark
branches valued in `star c` instead of `c` — the diagonal
shadow of changes 2 and 3. -/

/-- The diagonal value of `pi1 ⟨lam, 1, c • 1⟩` at slot
value `v`. -/
def pi1DiagVal (lam c : ℂ) (v : ℕ) : ℂ :=
  if v < 8 then 1
  else if v = 8 then lam
  else if v = 9 then star lam
  else if v < 16 then (if (v - 10) % 2 = 0 then lam else star lam)
  else if v < 18 then star lam
  else if v < 24 then star c
  else if v < 26 then star lam
  else star c

theorem pi1DiagVal_leptonL (lam c : ℂ) (s : Fin 2) :
    pi1DiagVal lam c s.val = 1 := by
  unfold pi1DiagVal
  rw [if_pos (by have hs := s.isLt; omega)]

theorem pi1DiagVal_quarkL (lam c : ℂ) (k : Fin 3) (s : Fin 2) :
    pi1DiagVal lam c (2 + 2 * k.val + s.val) = 1 := by
  unfold pi1DiagVal
  rw [if_pos (by have hk := k.isLt; have hs := s.isLt; omega)]

theorem pi1DiagVal_nuR (lam c : ℂ) :
    pi1DiagVal lam c 8 = lam := by
  unfold pi1DiagVal
  rw [if_neg (by norm_num), if_pos (by norm_num)]

theorem pi1DiagVal_eR (lam c : ℂ) :
    pi1DiagVal lam c 9 = star lam := by
  unfold pi1DiagVal
  rw [if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num)]

theorem pi1DiagVal_quarkR (lam c : ℂ) (k : Fin 3) (s : Fin 2) :
    pi1DiagVal lam c (10 + 2 * k.val + s.val)
      = if s.val % 2 = 0 then lam else star lam := by
  have hk := k.isLt
  have hs := s.isLt
  unfold pi1DiagVal
  by_cases hs2 : s.val % 2 = 0
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (by omega), if_pos (by omega), if_pos hs2]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (by omega), if_neg (by omega), if_neg hs2]

theorem pi1DiagVal_leptonLc (lam c : ℂ) (s : Fin 2) :
    pi1DiagVal lam c (16 + s.val) = star lam := by
  have hs := s.isLt
  unfold pi1DiagVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega)]

theorem pi1DiagVal_quarkLc (lam c : ℂ) (k : Fin 3) (s : Fin 2) :
    pi1DiagVal lam c (18 + 2 * k.val + s.val) = star c := by
  have hk := k.isLt
  have hs := s.isLt
  unfold pi1DiagVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos (by omega)]

theorem pi1DiagVal_nuRc (lam c : ℂ) :
    pi1DiagVal lam c 24 = star lam := by
  unfold pi1DiagVal
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
    if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
    if_pos (by norm_num)]

theorem pi1DiagVal_eRc (lam c : ℂ) :
    pi1DiagVal lam c 25 = star lam := by
  unfold pi1DiagVal
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
    if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
    if_pos (by norm_num)]

theorem pi1DiagVal_quarkRc (lam c : ℂ) (k : Fin 3) (s : Fin 2) :
    pi1DiagVal lam c (26 + 2 * k.val + s.val) = star c := by
  have hk := k.isLt
  have hs := s.isLt
  unfold pi1DiagVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

def pi1Diag (lam c : ℂ) (i : I32) : ℂ := pi1DiagVal lam c i.val

theorem pi1_diag_entry_leptonL (lam c : ℂ) (s : Fin 2) :
    pi1 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
        (⟨s.val, by omega⟩ : I32) ⟨s.val, by omega⟩
      = pi1Diag lam c ⟨s.val, by omega⟩ := by
  rw [pi1_entry_leptonL]
  show (1 : Matrix I2 I2 ℂ) s s = pi1DiagVal lam c s.val
  rw [Matrix.one_apply_eq, pi1DiagVal_leptonL]

theorem pi1_diag_entry_quarkL (lam c : ℂ) (k : Fin 3) (s : Fin 2) :
    pi1 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
        (⟨2 + 2 * k.val + s.val, by omega⟩ : I32)
        ⟨2 + 2 * k.val + s.val, by omega⟩
      = pi1Diag lam c ⟨2 + 2 * k.val + s.val, by omega⟩ := by
  rw [pi1_entry_quarkL, if_pos rfl]
  show (1 : Matrix I2 I2 ℂ) s s = pi1DiagVal lam c (2 + 2 * k.val + s.val)
  rw [Matrix.one_apply_eq, pi1DiagVal_quarkL]

theorem pi1_diag_entry_nuR (lam c : ℂ) :
    pi1 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
        (⟨8, by omega⟩ : I32) ⟨8, by omega⟩
      = pi1Diag lam c ⟨8, by omega⟩ := by
  rw [pi1_entry_nuR]
  show lam = pi1DiagVal lam c 8
  rw [pi1DiagVal_nuR]

theorem pi1_diag_entry_eR (lam c : ℂ) :
    pi1 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
        (⟨9, by omega⟩ : I32) ⟨9, by omega⟩
      = pi1Diag lam c ⟨9, by omega⟩ := by
  rw [pi1_entry_eR]
  show star lam = pi1DiagVal lam c 9
  rw [pi1DiagVal_eR]

theorem pi1_diag_entry_quarkR (lam c : ℂ) (k : Fin 3) (s : Fin 2) :
    pi1 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
        (⟨10 + 2 * k.val + s.val, by omega⟩ : I32)
        ⟨10 + 2 * k.val + s.val, by omega⟩
      = pi1Diag lam c ⟨10 + 2 * k.val + s.val, by omega⟩ := by
  rw [pi1_entry_quarkR, if_pos ⟨rfl, rfl⟩]
  show (if s = 0 then lam else star lam)
    = pi1DiagVal lam c (10 + 2 * k.val + s.val)
  rw [pi1DiagVal_quarkR]
  by_cases hs0 : s = 0
  · rw [if_pos hs0, if_pos (by
      have hv : s.val = 0 := congrArg Fin.val hs0
      omega)]
  · have hv0 : s.val ≠ 0 :=
      fun hv => hs0 (Fin.ext (show s.val = (0 : Fin 2).val from hv))
    have hs1 : s.val = 1 := by have hs := s.isLt; omega
    rw [if_neg hs0, if_neg (by omega)]

/-- Diagonal entry: left antileptons (changed block). -/
theorem pi1_diag_entry_leptonLc (lam c : ℂ) (s : Fin 2) :
    pi1 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
        (⟨16 + s.val, by omega⟩ : I32) ⟨16 + s.val, by omega⟩
      = pi1Diag lam c ⟨16 + s.val, by omega⟩ := by
  rw [pi1_entry_leptonLc, if_pos rfl]
  show star lam = pi1DiagVal lam c (16 + s.val)
  rw [pi1DiagVal_leptonLc]

/-- Diagonal entry: left antiquarks (changed block). -/
theorem pi1_diag_entry_quarkLc (lam c : ℂ) (k : Fin 3) (s : Fin 2) :
    pi1 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
        (⟨18 + 2 * k.val + s.val, by omega⟩ : I32)
        ⟨18 + 2 * k.val + s.val, by omega⟩
      = pi1Diag lam c ⟨18 + 2 * k.val + s.val, by omega⟩ := by
  rw [pi1_entry_quarkLc, if_pos rfl]
  show star ((c • (1 : Matrix I3 I3 ℂ)) k k)
    = pi1DiagVal lam c (18 + 2 * k.val + s.val)
  rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    pi1DiagVal_quarkLc]

theorem pi1_diag_entry_nuRc (lam c : ℂ) :
    pi1 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
        (⟨24, by omega⟩ : I32) ⟨24, by omega⟩
      = pi1Diag lam c ⟨24, by omega⟩ := by
  rw [pi1_entry_nuRc]
  show star lam = pi1DiagVal lam c 24
  rw [pi1DiagVal_nuRc]

theorem pi1_diag_entry_eRc (lam c : ℂ) :
    pi1 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
        (⟨25, by omega⟩ : I32) ⟨25, by omega⟩
      = pi1Diag lam c ⟨25, by omega⟩ := by
  rw [pi1_entry_eRc]
  show star lam = pi1DiagVal lam c 25
  rw [pi1DiagVal_eRc]

/-- Diagonal entry: right antiquarks (changed block). -/
theorem pi1_diag_entry_quarkRc (lam c : ℂ) (k : Fin 3) (s : Fin 2) :
    pi1 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
        (⟨26 + 2 * k.val + s.val, by omega⟩ : I32)
        ⟨26 + 2 * k.val + s.val, by omega⟩
      = pi1Diag lam c ⟨26 + 2 * k.val + s.val, by omega⟩ := by
  rw [pi1_entry_quarkRc, if_pos rfl]
  show star ((c • (1 : Matrix I3 I3 ℂ)) k k)
    = pi1DiagVal lam c (26 + 2 * k.val + s.val)
  rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    pi1DiagVal_quarkRc]

/-- **The diagonal form.** `pi1 ⟨lam, 1, c • 1⟩` is the
diagonal matrix `Matrix.diagonal (pi1Diag lam c)`. Entry tree
as in the landed module. -/
theorem pi1_eq_diagonal (lam c : ℂ) :
    pi1 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
      = Matrix.diagonal (pi1Diag lam c) := by
  apply eq_diagonal_of_entry
  intro i j
  by_cases hsec : i.val / 8 = j.val / 8
  · by_cases hi : i.val < 8
    · have hj : j.val < 8 := by omega
      by_cases hi2 : i.val < 2
      · by_cases hj2 : j.val < 2
        · have hsi : (⟨(⟨i.val, hi2⟩ : Fin 2).val, by omega⟩ : I32) = i :=
            Fin.ext (show (⟨i.val, hi2⟩ : Fin 2).val = i.val from rfl)
          have hsj : (⟨(⟨j.val, hj2⟩ : Fin 2).val, by omega⟩ : I32) = j :=
            Fin.ext (show (⟨j.val, hj2⟩ : Fin 2).val = j.val from rfl)
          rw [← hsi, ← hsj]
          split_ifs with hslot
          · rw [hslot]
            exact pi1_diag_entry_leptonL lam c (⟨j.val, hj2⟩ : Fin 2)
          · have hS : (⟨i.val, hi2⟩ : Fin 2) ≠ (⟨j.val, hj2⟩ : Fin 2) :=
              fun hh => hslot (Fin.ext (show i.val = j.val by
                have hv := congrArg Fin.val hh
                omega))
            rw [pi1_entry_leptonL]
            show (1 : Matrix I2 I2 ℂ) (⟨i.val, hi2⟩ : Fin 2) (⟨j.val, hj2⟩ : Fin 2) = 0
            rw [Matrix.one_apply, if_neg hS]
        · have hns : ¬ sameBlock i j := not_sameBlock_of_HL_mixed (Or.inl ⟨hi2, by omega, hj⟩)
          have hne : i ≠ j := by
            intro hh
            have hv := congrArg Fin.val hh
            omega
          rw [if_neg hne, pi1_entry_eq_zero_of_not_sameBlock _ hns]
      · by_cases hj2 : j.val < 2
        · have hns : ¬ sameBlock i j := not_sameBlock_of_HL_mixed (Or.inr ⟨by omega, hi, hj2⟩)
          have hne : i ≠ j := by
            intro hh
            have hv := congrArg Fin.val hh
            omega
          rw [if_neg hne, pi1_entry_eq_zero_of_not_sameBlock _ hns]
        · have hci : (⟨2 + 2 * (⟨(i.val - 2) / 2, by omega⟩ : Fin 3).val
              + (⟨(i.val - 2) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
            apply Fin.ext
            show 2 + 2 * ((i.val - 2) / 2) + (i.val - 2) % 2 = i.val
            have h := Nat.div_add_mod (i.val - 2) 2
            omega
          have hcj : (⟨2 + 2 * (⟨(j.val - 2) / 2, by omega⟩ : Fin 3).val
              + (⟨(j.val - 2) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
            apply Fin.ext
            show 2 + 2 * ((j.val - 2) / 2) + (j.val - 2) % 2 = j.val
            have h := Nat.div_add_mod (j.val - 2) 2
            omega
          rw [← hci, ← hcj]
          split_ifs with hslot
          · rw [hslot]
            exact pi1_diag_entry_quarkL lam c (⟨(j.val - 2) / 2, by omega⟩ : Fin 3) (⟨(j.val - 2) % 2, by omega⟩ : Fin 2)
          · by_cases hK : (⟨(i.val - 2) / 2, by omega⟩ : Fin 3) = (⟨(j.val - 2) / 2, by omega⟩ : Fin 3)
            · have hS : (⟨(i.val - 2) % 2, by omega⟩ : Fin 2) ≠ (⟨(j.val - 2) % 2, by omega⟩ : Fin 2) :=
                fun hh => hslot (Fin.ext (show
                  2 + 2 * ((⟨(i.val - 2) / 2, by omega⟩ : Fin 3)).val + ((⟨(i.val - 2) % 2, by omega⟩ : Fin 2)).val
                    = 2 + 2 * ((⟨(j.val - 2) / 2, by omega⟩ : Fin 3)).val + ((⟨(j.val - 2) % 2, by omega⟩ : Fin 2)).val by
                  have hv1 := congrArg Fin.val hK
                  have hv2 := congrArg Fin.val hh
                  omega))
              rw [pi1_entry_quarkL, if_pos hK]
              show (1 : Matrix I2 I2 ℂ) (⟨(i.val - 2) % 2, by omega⟩ : Fin 2) (⟨(j.val - 2) % 2, by omega⟩ : Fin 2) = 0
              rw [Matrix.one_apply, if_neg hS]
            · rw [pi1_entry_quarkL, if_neg hK]
    · by_cases hi16 : i.val < 16
      · have hj8 : 8 ≤ j.val := by omega
        have hj16 : j.val < 16 := by omega
        by_cases hi8 : i.val = 8
        · by_cases hj8' : j.val = 8
          · have hsi : (⟨8, by omega⟩ : I32) = i := Fin.ext hi8.symm
            have hsj : (⟨8, by omega⟩ : I32) = j := Fin.ext hj8'.symm
            rw [← hsi, ← hsj]
            split_ifs with hslot
            · exact pi1_diag_entry_nuR lam c
            · exact (hslot rfl).elim
          · by_cases hj9 : j.val = 9
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed (Or.inl ⟨hi8, hj9⟩)
              have hne : i ≠ j := by
                intro hh
                have hv := congrArg Fin.val hh
                omega
              rw [if_neg hne, pi1_entry_eq_zero_of_not_sameBlock _ hns]
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                (Or.inr (Or.inr (Or.inl ⟨Or.inl hi8, by omega, hj16⟩)))
              have hne : i ≠ j := by
                intro hh
                have hv := congrArg Fin.val hh
                omega
              rw [if_neg hne, pi1_entry_eq_zero_of_not_sameBlock _ hns]
        · by_cases hi9 : i.val = 9
          · by_cases hj8' : j.val = 8
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed (Or.inr (Or.inl ⟨hi9, hj8'⟩))
              have hne : i ≠ j := by
                intro hh
                have hv := congrArg Fin.val hh
                omega
              rw [if_neg hne, pi1_entry_eq_zero_of_not_sameBlock _ hns]
            · by_cases hj9 : j.val = 9
              · have hsi : (⟨9, by omega⟩ : I32) = i := Fin.ext hi9.symm
                have hsj : (⟨9, by omega⟩ : I32) = j := Fin.ext hj9.symm
                rw [← hsi, ← hsj]
                split_ifs with hslot
                · exact pi1_diag_entry_eR lam c
                · exact (hslot rfl).elim
              · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                  (Or.inr (Or.inr (Or.inl ⟨Or.inr hi9, by omega, hj16⟩)))
                have hne : i ≠ j := by
                  intro hh
                  have hv := congrArg Fin.val hh
                  omega
                rw [if_neg hne, pi1_entry_eq_zero_of_not_sameBlock _ hns]
          · by_cases hj8' : j.val = 8
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inl hj8'⟩)))
              have hne : i ≠ j := by
                intro hh
                have hv := congrArg Fin.val hh
                omega
              rw [if_neg hne, pi1_entry_eq_zero_of_not_sameBlock _ hns]
            · by_cases hj9 : j.val = 9
              · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                  (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inr hj9⟩)))
                have hne : i ≠ j := by
                  intro hh
                  have hv := congrArg Fin.val hh
                  omega
                rw [if_neg hne, pi1_entry_eq_zero_of_not_sameBlock _ hns]
              · have hci : (⟨10 + 2 * (⟨(i.val - 10) / 2, by omega⟩ : Fin 3).val
                    + (⟨(i.val - 10) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
                  apply Fin.ext
                  show 10 + 2 * ((i.val - 10) / 2) + (i.val - 10) % 2 = i.val
                  have h := Nat.div_add_mod (i.val - 10) 2
                  omega
                have hcj : (⟨10 + 2 * (⟨(j.val - 10) / 2, by omega⟩ : Fin 3).val
                    + (⟨(j.val - 10) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
                  apply Fin.ext
                  show 10 + 2 * ((j.val - 10) / 2) + (j.val - 10) % 2 = j.val
                  have h := Nat.div_add_mod (j.val - 10) 2
                  omega
                rw [← hci, ← hcj]
                split_ifs with hslot
                · rw [hslot]
                  exact pi1_diag_entry_quarkR lam c (⟨(j.val - 10) / 2, by omega⟩ : Fin 3) (⟨(j.val - 10) % 2, by omega⟩ : Fin 2)
                · by_cases hS : (⟨(i.val - 10) % 2, by omega⟩ : Fin 2) = (⟨(j.val - 10) % 2, by omega⟩ : Fin 2)
                  · have hK : (⟨(i.val - 10) / 2, by omega⟩ : Fin 3) ≠ (⟨(j.val - 10) / 2, by omega⟩ : Fin 3) :=
                      fun hh => hslot (Fin.ext (show
                        10 + 2 * ((⟨(i.val - 10) / 2, by omega⟩ : Fin 3)).val + ((⟨(i.val - 10) % 2, by omega⟩ : Fin 2)).val
                          = 10 + 2 * ((⟨(j.val - 10) / 2, by omega⟩ : Fin 3)).val + ((⟨(j.val - 10) % 2, by omega⟩ : Fin 2)).val by
                        have hv1 := congrArg Fin.val hh
                        have hv2 := congrArg Fin.val hS
                        omega))
                    have hne : ¬ ((⟨(i.val - 10) % 2, by omega⟩ : Fin 2) = (⟨(j.val - 10) % 2, by omega⟩ : Fin 2) ∧ (⟨(i.val - 10) / 2, by omega⟩ : Fin 3) = (⟨(j.val - 10) / 2, by omega⟩ : Fin 3)) := fun hh => hK hh.2
                    rw [pi1_entry_quarkR, if_neg hne]
                  · have hne : ¬ ((⟨(i.val - 10) % 2, by omega⟩ : Fin 2) = (⟨(j.val - 10) % 2, by omega⟩ : Fin 2) ∧ (⟨(i.val - 10) / 2, by omega⟩ : Fin 3) = (⟨(j.val - 10) / 2, by omega⟩ : Fin 3)) := fun hh => hS hh.1
                    rw [pi1_entry_quarkR, if_neg hne]
      · by_cases hi24 : i.val < 24
        · have hj16 : 16 ≤ j.val := by omega
          have hj24 : j.val < 24 := by omega
          by_cases hi18 : i.val < 18
          · by_cases hj18 : j.val < 18
            · have hsi : (⟨16 + (⟨i.val - 16, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i :=
                Fin.ext (by show 16 + (i.val - 16) = i.val; omega)
              have hsj : (⟨16 + (⟨j.val - 16, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j :=
                Fin.ext (by show 16 + (j.val - 16) = j.val; omega)
              rw [← hsi, ← hsj]
              split_ifs with hslot
              · rw [hslot]
                exact pi1_diag_entry_leptonLc lam c (⟨j.val - 16, by omega⟩ : Fin 2)
              · have hS : (⟨i.val - 16, by omega⟩ : Fin 2) ≠ (⟨j.val - 16, by omega⟩ : Fin 2) :=
                  fun hh => hslot (Fin.ext (show
                    16 + ((⟨i.val - 16, by omega⟩ : Fin 2)).val = 16 + ((⟨j.val - 16, by omega⟩ : Fin 2)).val by
                    have hv := congrArg Fin.val hh
                    omega))
                rw [pi1_entry_leptonLc, if_neg hS]
            · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                (Or.inl ⟨by omega, hi18, by omega, hj24⟩)
              have hne : i ≠ j := by
                intro hh
                have hv := congrArg Fin.val hh
                omega
              rw [if_neg hne, pi1_entry_eq_zero_of_not_sameBlock _ hns]
          · by_cases hj18 : j.val < 18
            · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                (Or.inr (Or.inl ⟨by omega, hi24, hj16, hj18⟩))
              have hne : i ≠ j := by
                intro hh
                have hv := congrArg Fin.val hh
                omega
              rw [if_neg hne, pi1_entry_eq_zero_of_not_sameBlock _ hns]
            · have hci : (⟨18 + 2 * (⟨(i.val - 18) / 2, by omega⟩ : Fin 3).val
                  + (⟨(i.val - 18) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
                apply Fin.ext
                show 18 + 2 * ((i.val - 18) / 2) + (i.val - 18) % 2 = i.val
                have h := Nat.div_add_mod (i.val - 18) 2
                omega
              have hcj : (⟨18 + 2 * (⟨(j.val - 18) / 2, by omega⟩ : Fin 3).val
                  + (⟨(j.val - 18) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
                apply Fin.ext
                show 18 + 2 * ((j.val - 18) / 2) + (j.val - 18) % 2 = j.val
                have h := Nat.div_add_mod (j.val - 18) 2
                omega
              rw [← hci, ← hcj]
              split_ifs with hslot
              · rw [hslot]
                exact pi1_diag_entry_quarkLc lam c (⟨(j.val - 18) / 2, by omega⟩ : Fin 3) (⟨(j.val - 18) % 2, by omega⟩ : Fin 2)
              · by_cases hS : (⟨(i.val - 18) % 2, by omega⟩ : Fin 2) = (⟨(j.val - 18) % 2, by omega⟩ : Fin 2)
                · have hK : (⟨(i.val - 18) / 2, by omega⟩ : Fin 3) ≠ (⟨(j.val - 18) / 2, by omega⟩ : Fin 3) :=
                    fun hh => hslot (Fin.ext (show
                      18 + 2 * ((⟨(i.val - 18) / 2, by omega⟩ : Fin 3)).val + ((⟨(i.val - 18) % 2, by omega⟩ : Fin 2)).val
                        = 18 + 2 * ((⟨(j.val - 18) / 2, by omega⟩ : Fin 3)).val + ((⟨(j.val - 18) % 2, by omega⟩ : Fin 2)).val by
                      have hv1 := congrArg Fin.val hh
                      have hv2 := congrArg Fin.val hS
                      omega))
                  rw [pi1_entry_quarkLc, if_pos hS]
                  show star ((c • (1 : Matrix I3 I3 ℂ)) (⟨(i.val - 18) / 2, by omega⟩ : Fin 3) (⟨(j.val - 18) / 2, by omega⟩ : Fin 3)) = 0
                  rw [Matrix.smul_apply, Matrix.one_apply, if_neg hK, smul_zero,
                    star_zero]
                · rw [pi1_entry_quarkLc, if_neg hS]
        · have hj24 : 24 ≤ j.val := by omega
          by_cases hi24' : i.val = 24
          · by_cases hj24' : j.val = 24
            · have hsi : (⟨24, by omega⟩ : I32) = i := Fin.ext hi24'.symm
              have hsj : (⟨24, by omega⟩ : I32) = j := Fin.ext hj24'.symm
              rw [← hsi, ← hsj]
              split_ifs with hslot
              · exact pi1_diag_entry_nuRc lam c
              · exact (hslot rfl).elim
            · by_cases hj25 : j.val = 25
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inl ⟨hi24', hj25⟩)))))))
                have hne : i ≠ j := by
                  intro hh
                  have hv := congrArg Fin.val hh
                  omega
                rw [if_neg hne, pi1_entry_eq_zero_of_not_sameBlock _ hns]
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                  (Or.inr (Or.inr (Or.inl ⟨hi24', by omega⟩)))
                have hne : i ≠ j := by
                  intro hh
                  have hv := congrArg Fin.val hh
                  omega
                rw [if_neg hne, pi1_entry_eq_zero_of_not_sameBlock _ hns]
          · by_cases hi25 : i.val = 25
            · by_cases hj24' : j.val = 24
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr ⟨hi25, hj24'⟩)))))))
                have hne : i ≠ j := by
                  intro hh
                  have hv := congrArg Fin.val hh
                  omega
                rw [if_neg hne, pi1_entry_eq_zero_of_not_sameBlock _ hns]
              · by_cases hj25 : j.val = 25
                · have hsi : (⟨25, by omega⟩ : I32) = i := Fin.ext hi25.symm
                  have hsj : (⟨25, by omega⟩ : I32) = j := Fin.ext hj25.symm
                  rw [← hsi, ← hsj]
                  split_ifs with hslot
                  · exact pi1_diag_entry_eRc lam c
                  · exact (hslot rfl).elim
                · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                    (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi25, by omega⟩))))
                  have hne : i ≠ j := by
                    intro hh
                    have hv := congrArg Fin.val hh
                    omega
                  rw [if_neg hne, pi1_entry_eq_zero_of_not_sameBlock _ hns]
            · by_cases hj24' : j.val = 24
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inl ⟨by omega, hj24'⟩)))))
                have hne : i ≠ j := by
                  intro hh
                  have hv := congrArg Fin.val hh
                  omega
                rw [if_neg hne, pi1_entry_eq_zero_of_not_sameBlock _ hns]
              · by_cases hj25 : j.val = 25
                · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inl ⟨by omega, hj25⟩))))))
                  have hne : i ≠ j := by
                    intro hh
                    have hv := congrArg Fin.val hh
                    omega
                  rw [if_neg hne, pi1_entry_eq_zero_of_not_sameBlock _ hns]
                · have hci : (⟨26 + 2 * (⟨(i.val - 26) / 2, by omega⟩ : Fin 3).val
                      + (⟨(i.val - 26) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
                    apply Fin.ext
                    show 26 + 2 * ((i.val - 26) / 2) + (i.val - 26) % 2 = i.val
                    have h := Nat.div_add_mod (i.val - 26) 2
                    omega
                  have hcj : (⟨26 + 2 * (⟨(j.val - 26) / 2, by omega⟩ : Fin 3).val
                      + (⟨(j.val - 26) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
                    apply Fin.ext
                    show 26 + 2 * ((j.val - 26) / 2) + (j.val - 26) % 2 = j.val
                    have h := Nat.div_add_mod (j.val - 26) 2
                    omega
                  rw [← hci, ← hcj]
                  split_ifs with hslot
                  · rw [hslot]
                    exact pi1_diag_entry_quarkRc lam c (⟨(j.val - 26) / 2, by omega⟩ : Fin 3) (⟨(j.val - 26) % 2, by omega⟩ : Fin 2)
                  · by_cases hS : (⟨(i.val - 26) % 2, by omega⟩ : Fin 2) = (⟨(j.val - 26) % 2, by omega⟩ : Fin 2)
                    · have hK : (⟨(i.val - 26) / 2, by omega⟩ : Fin 3) ≠ (⟨(j.val - 26) / 2, by omega⟩ : Fin 3) :=
                        fun hh => hslot (Fin.ext (show
                          26 + 2 * ((⟨(i.val - 26) / 2, by omega⟩ : Fin 3)).val + ((⟨(i.val - 26) % 2, by omega⟩ : Fin 2)).val
                            = 26 + 2 * ((⟨(j.val - 26) / 2, by omega⟩ : Fin 3)).val + ((⟨(j.val - 26) % 2, by omega⟩ : Fin 2)).val by
                          have hv1 := congrArg Fin.val hh
                          have hv2 := congrArg Fin.val hS
                          omega))
                      rw [pi1_entry_quarkRc, if_pos hS]
                      show star ((c • (1 : Matrix I3 I3 ℂ)) (⟨(i.val - 26) / 2, by omega⟩ : Fin 3) (⟨(j.val - 26) / 2, by omega⟩ : Fin 3)) = 0
                      rw [Matrix.smul_apply, Matrix.one_apply, if_neg hK, smul_zero,
                        star_zero]
                    · rw [pi1_entry_quarkRc, if_neg hS]
  · have hns : ¬ sameBlock i j := not_sameBlock_of_ne_sector hsec
    have hne : i ≠ j := by
      intro hh
      have hv := congrArg Fin.val hh
      omega
    rw [if_neg hne, pi1_entry_eq_zero_of_not_sameBlock _ hns]

/-- T1 (unit): `pi1` sends the unit element to the identity
matrix. Via the diagonal form, as in the landed module. -/
theorem pi1_one : pi1 afOne = 1 := by
  have h1 : afOne = ⟨1, 1, (1 : ℂ) • (1 : Matrix I3 I3 ℂ)⟩ := by
    rw [ThetLogos.PreOptionARepresentation.ext_iff]
    refine ⟨afOne_u1, afOne_q, ?_⟩
    rw [afOne_color, one_smul]
  rw [h1, pi1_eq_diagonal]
  have hD : pi1Diag 1 1 = fun _ => 1 := by
    funext i
    show pi1DiagVal 1 1 i.val = 1
    unfold pi1DiagVal
    split_ifs <;> simp [star_one]
  rw [hD]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
  · rw [Matrix.diagonal_apply, if_neg hij, Matrix.one_apply_ne hij]


/-! ## §5. T2 — faithfulness, re-earned

The kernel read-off is π₀'s, with one change of seat: colour is
now read at the right-antiquark block through `star`, which is
injective, so the read-off is exactly as strong. Pure colour
sits **conjugated** on the right antiquarks (π₀: naked) — the
faithfulness content is unchanged, the seat's form is Route B's. -/

/-- T2: `pi1` is faithful — its kernel is zero. -/
theorem pi1_ker_iff (a : AF) : pi1 a = 0 ↔ a = afZero := by
  constructor
  · intro h
    rw [ThetLogos.PreOptionARepresentation.ext_iff]
    refine ⟨?_, ?_, ?_⟩
    · have h8 : pi1 a ⟨8, by omega⟩ ⟨8, by omega⟩ = 0 := by rw [h, Matrix.zero_apply]
      rw [pi1_entry_nuR] at h8
      rw [afZero_u1]
      exact h8
    · ext s t
      have hs : pi1 a ⟨s.val, by omega⟩ ⟨t.val, by omega⟩ = 0 := by
        rw [h, Matrix.zero_apply]
      rw [pi1_entry_leptonL] at hs
      rw [afZero_q, Matrix.zero_apply]
      exact hs
    · ext c c'
      have hc : pi1 a ⟨26 + 2 * c.val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩
          ⟨26 + 2 * c'.val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩ = 0 := by
        rw [h, Matrix.zero_apply]
      rw [pi1_entry_quarkRc, if_pos rfl] at hc
      rw [afZero_color, Matrix.zero_apply]
      exact star_eq_zero.mp hc
  · intro h
    rw [h]
    exact pi1_zero

/-- Equality of elements is equality of their `pi1` images. -/
theorem pi1_eq_iff (a b : AF) : pi1 a = pi1 b ↔ a = b := by
  constructor
  · intro h
    rw [ThetLogos.PreOptionARepresentation.ext_iff]
    refine ⟨?_, ?_, ?_⟩
    · have h8 : pi1 a ⟨8, by omega⟩ ⟨8, by omega⟩
          = pi1 b ⟨8, by omega⟩ ⟨8, by omega⟩ := by rw [h]
      rwa [pi1_entry_nuR, pi1_entry_nuR] at h8
    · ext s t
      have hs : pi1 a ⟨s.val, by omega⟩ ⟨t.val, by omega⟩
          = pi1 b ⟨s.val, by omega⟩ ⟨t.val, by omega⟩ := by rw [h]
      rwa [pi1_entry_leptonL, pi1_entry_leptonL] at hs
    · ext c c'
      have hc : pi1 a ⟨26 + 2 * c.val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩
            ⟨26 + 2 * c'.val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩
          = pi1 b ⟨26 + 2 * c.val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩
            ⟨26 + 2 * c'.val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩ := by rw [h]
      rw [pi1_entry_quarkRc, pi1_entry_quarkRc, if_pos rfl,
        if_pos rfl] at hc
      exact star_injective hc
  · intro h
    rw [h]

theorem pi1_injective : Function.Injective pi1 :=
  fun a b h => (pi1_eq_iff a b).mp h

/-- Pure colour is read off at the right-antiquark block,
through the conjugation. -/
theorem pi1_pure_color_entry (m : Matrix I3 I3 ℂ) (c c' : Fin 3) :
    pi1 ⟨0, 0, m⟩ ⟨26 + 2 * c.val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩
        ⟨26 + 2 * c'.val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩
      = star (m c c') := by
  rw [pi1_entry_quarkRc, if_pos rfl]

/-- T2 in words: a pure-colour element with `m ≠ 0` represents
nontrivially — under Option-A it would be in the kernel. -/
theorem pi1_pure_color_ne_zero (m : Matrix I3 I3 ℂ) (hm : m ≠ 0) :
    pi1 ⟨0, 0, m⟩ ≠ 0 := by
  intro h
  apply hm
  ext c c'
  have e := pi1_pure_color_entry m c c'
  rw [h, Matrix.zero_apply] at e
  exact star_eq_zero.mp e.symm

/-! ## §6. Grading

`gammaF`-evenness: the support of `pi1 a` lies in the block
diagonal of the sector partition, exactly as for `pi0` — the
changed blocks sit inside the same sectors. -/

theorem pi1_support_sector {a : AF} {i j : I32} (h : pi1 a i j ≠ 0) :
    i.val / 8 = j.val / 8 := by
  by_contra hne
  exact h (pi1_entry_cross_sector a hne)

/-- T1 (grading part): `pi1` is even for the corpus's
grading. -/
theorem pi1_grading_even (a : AF) : gammaF * pi1 a = pi1 a * gammaF := by
  ext i j
  rw [gammaF_mul_apply, mul_gammaF_apply]
  by_cases h : pi1 a i j = 0
  · rw [h, mul_zero, zero_mul]
  · have hsec := pi1_support_sector h
    rw [gammaF_diag_eq_of_same_sector hsec]
    exact mul_comm _ _

/-! ## §7. T4 — order-zero for (π₁, ρ₁°)

ρ₁° is π₁'s own J-opposite (`rho1`), identified with the corpus's
`piOp` by construction. The partner involution permutes the ten
blocks (H-blocks ↔ Hᶜ-blocks), and ρ₁'s block entries are the
summand-pure conjugates read off π₁'s antiparticle blocks — no
dressing (compare §2's `anatomy_rho1_undressed`). -/

/-- Partner of a small slot, 16-shifted form. -/
theorem partner_mk_add16 (x : ℕ) (hx : x < 16) :
    partner ⟨x, by omega⟩ = ⟨16 + x, by omega⟩ := by
  apply Fin.ext
  simp [partner_val_eq, hx, Nat.add_comm]

/-- Partner of an antiparticle slot, 16-unshifted form. -/
theorem partner_mk_sub16 (x : ℕ) (hx : x < 16) :
    partner ⟨16 + x, by omega⟩ = ⟨x, by omega⟩ := by
  apply Fin.ext
  simp [partner_val_eq, hx]

/-- Partner of a left-quark slot. -/
theorem partner_mk_quarkL (k : Fin 3) (s : Fin 2) :
    partner ⟨2 + 2 * k.val + s.val, by omega⟩
      = ⟨18 + 2 * k.val + s.val, by omega⟩ := by
  apply Fin.ext
  simp only [partner_val_eq]
  have hk : k.val < 3 := k.isLt
  have hs : s.val < 2 := s.isLt
  split_ifs with h <;> omega

/-- Partner of a right-quark slot. -/
theorem partner_mk_quarkR (k : Fin 3) (s : Fin 2) :
    partner ⟨10 + 2 * k.val + s.val, by omega⟩
      = ⟨26 + 2 * k.val + s.val, by omega⟩ := by
  apply Fin.ext
  simp only [partner_val_eq]
  have hk : k.val < 3 := k.isLt
  have hs : s.val < 2 := s.isLt
  split_ifs with h <;> omega

/-- Partner of a left-antiquark slot. -/
theorem partner_mk_quarkLc (k : Fin 3) (s : Fin 2) :
    partner ⟨18 + 2 * k.val + s.val, by omega⟩
      = ⟨2 + 2 * k.val + s.val, by omega⟩ := by
  apply Fin.ext
  simp only [partner_val_eq]
  have hk : k.val < 3 := k.isLt
  have hs : s.val < 2 := s.isLt
  split_ifs with h <;> omega

/-- Partner of a right-antiquark slot. -/
theorem partner_mk_quarkRc (k : Fin 3) (s : Fin 2) :
    partner ⟨26 + 2 * k.val + s.val, by omega⟩
      = ⟨10 + 2 * k.val + s.val, by omega⟩ := by
  apply Fin.ext
  simp only [partner_val_eq]
  have hk : k.val < 3 := k.isLt
  have hs : s.val < 2 := s.isLt
  split_ifs with h <;> omega

/-- Partner of the ν_R slot. -/
theorem partner_mk8 : partner ⟨8, by omega⟩ = ⟨24, by omega⟩ := by
  apply Fin.ext
  simp [partner_val_eq]

/-- Partner of the ν_Rᶜ slot. -/
theorem partner_mk24 : partner ⟨24, by omega⟩ = ⟨8, by omega⟩ := by
  apply Fin.ext
  simp [partner_val_eq]

/-- Partner of the e_Rᶜ slot. -/
theorem partner_mk25 : partner ⟨25, by omega⟩ = ⟨9, by omega⟩ := by
  apply Fin.ext
  simp [partner_val_eq]

/-- The partner involution permutes the ten blocks: `sameBlock` is
partner-invariant. -/
theorem sameBlock_partner {i j : I32} :
    sameBlock (partner i) (partner j) ↔ sameBlock i j := by
  have hpi : (partner i).val = if i.val < 16 then i.val + 16 else i.val - 16 :=
    partner_val_eq i
  have hpj : (partner j).val = if j.val < 16 then j.val + 16 else j.val - 16 :=
    partner_val_eq j
  unfold sameBlock
  rw [hpi, hpj]
  split_ifs with hi hj <;> constructor <;> intro h <;>
    rcases h with h | h | h | h | h | h | h | h | h | h <;>
    first
      | exact Or.inl ⟨by omega, by omega⟩
      | exact Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega, by omega, by omega⟩))))))))
      | (exfalso; omega)

/-- Membership transport along the partner bijection of finsets. -/
theorem partner_not_mem_of {s t : Finset I32} {k : I32}
    (hbij : ∀ x : I32, x ∈ t → partner x ∈ s) (hk : k ∉ s) :
    partner k ∉ t := by
  intro hmem
  have h2 := hbij (partner k) hmem
  rw [partner_involutive] at h2
  exact hk h2

/-! ### ρ₁'s representation laws -/

/-- **The J-form identification**: ρ₁ is the J-conjugate of the
adjoint, verbatim the charter's `ρ°(a) = J ρ(a)⋆ J⁻¹` in the
corpus's terms (mirror of the landed `rho0_eq_J_conj`). -/
theorem rho1_eq_J_conj (b : AF) :
    rho1 b = UJ * ((pi1 b)ᴴ.map (star : ℂ → ℂ)) * UJ := by
  rw [conjTranspose_map_star]
  rfl

/-- **ρ₁ reverses products.** -/
theorem rho1_afMul (a b : AF) : rho1 (afMul a b) = rho1 b * rho1 a := by
  show piOp (pi1 (afMul a b)) = piOp (pi1 b) * piOp (pi1 a)
  rw [pi1_afMul, piOp_antimul]

/-- **ρ₁ of the adjoint, J-form.** -/
theorem rho1_afStar_J (b : AF) :
    rho1 (afStar b) = UJ * (pi1 b).map (star : ℂ → ℂ) * UJ := by
  show piOp (pi1 (afStar b)) = UJ * (pi1 b).map (star : ℂ → ℂ) * UJ
  rw [pi1_afStar]
  show UJ * ((pi1 b)ᴴ).transpose * UJ = UJ * (pi1 b).map (star : ℂ → ℂ) * UJ
  rw [ThetLogos.Track1Closure.conjTranspose_transpose_eq_map_star]

/-- **ρ₁ is adjoint-compatible**: `rho1 (a*) = (rho1 a)ᴴ`. -/
theorem rho1_afStar (b : AF) : rho1 (afStar b) = (rho1 b)ᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply, rho1_entry, rho1_entry, pi1_afStar,
    Matrix.conjTranspose_apply]

/-- **ρ₁ is unital.** -/
theorem rho1_one : rho1 afOne = 1 := by
  show piOp (pi1 afOne) = 1
  rw [pi1_one]
  show UJ * (1 : Matrix I32 I32 ℂ).transpose * UJ = 1
  rw [Matrix.transpose_one, Matrix.mul_one, UJ_mul_self]

/-- **ρ₁ kills zero.** -/
theorem rho1_zero : rho1 afZero = 0 := by
  show piOp (pi1 afZero) = 0
  rw [pi1_zero]
  show UJ * (0 : Matrix I32 I32 ℂ).transpose * UJ = 0
  simp [Matrix.transpose_zero]

/-- **ρ₁ is grading-even**, like π₁: the partner involution flips
both grading eigenvalues and π₁'s support lies inside the
8-sectors, so the two flips cancel (mirror of `rho0_grading_even`
with π₁'s support lemma). -/
theorem rho1_grading_even (b : AF) : gammaF * rho1 b = rho1 b * gammaF := by
  ext i j
  rw [gammaF_mul_apply, mul_gammaF_apply, rho1_entry]
  by_cases h : pi1 b (partner j) (partner i) = 0
  · rw [h, mul_zero, zero_mul]
  · have hsec : (partner j).val / 8 = (partner i).val / 8 :=
      pi1_support_sector h
    have hg : gammaF (partner j) (partner j) = gammaF (partner i) (partner i) :=
      gammaF_diag_eq_of_same_sector hsec
    rw [gammaF_partner_flip i, gammaF_partner_flip j] at hg
    have hgg : gammaF i i = gammaF j j := by simpa using hg.symm
    rw [hgg]
    exact mul_comm _ _

/-! ### ρ₁'s block entries

Read off `rho1_entry` and π₁'s antiparticle entries: ρ₁'s particle
blocks are the summand-pure conjugates, its antiparticle blocks are
π₁'s particle actions transposed back — no dressing anywhere. -/

/-- ρ₁ entry, left-lepton block: the ℂ-pure conjugate scalar. -/
theorem rho1_entry_leptonL (b : AF) (s t : Fin 2) :
    rho1 b ⟨s.val, by omega⟩ ⟨t.val, by omega⟩
      = if t = s then star b.u1 else 0 := by
  rw [rho1_entry, partner_mk_add16 t.val (by omega),
    partner_mk_add16 s.val (by omega), pi1_entry_leptonLc]

/-- ρ₁ entry, left-quark block: the M₃-pure conjugate, transposed. -/
theorem rho1_entry_quarkL (b : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    rho1 b ⟨2 + 2 * ki.val + si.val, by omega⟩
        ⟨2 + 2 * kj.val + sj.val, by omega⟩
      = if sj = si then star (b.color kj ki) else 0 := by
  rw [rho1_entry, partner_mk_quarkL kj sj, partner_mk_quarkL ki si,
    pi1_entry_quarkLc]

/-- ρ₁ entry, ν_R slot. -/
theorem rho1_entry_nuR (b : AF) :
    rho1 b ⟨8, by omega⟩ ⟨8, by omega⟩ = star b.u1 := by
  rw [rho1_entry, partner_mk8, pi1_entry_nuRc]

/-- ρ₁ entry, e_R slot. -/
theorem rho1_entry_eR (b : AF) :
    rho1 b ⟨9, by omega⟩ ⟨9, by omega⟩ = star b.u1 := by
  rw [rho1_entry, partner_mk9, pi1_entry_eRc]

/-- ρ₁ entry, right-quark block: the M₃-pure conjugate, transposed. -/
theorem rho1_entry_quarkR (b : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    rho1 b ⟨10 + 2 * ki.val + si.val, by omega⟩
        ⟨10 + 2 * kj.val + sj.val, by omega⟩
      = if sj = si then star (b.color kj ki) else 0 := by
  rw [rho1_entry, partner_mk_quarkR kj sj, partner_mk_quarkR ki si,
    pi1_entry_quarkRc]

/-- ρ₁ entry, left-antilepton block: π₁'s doublet action, transposed. -/
theorem rho1_entry_leptonLc (b : AF) (s t : Fin 2) :
    rho1 b ⟨16 + s.val, by omega⟩ ⟨16 + t.val, by omega⟩ = b.q t s := by
  rw [rho1_entry, partner_mk_sub16 t.val (by omega),
    partner_mk_sub16 s.val (by omega), pi1_entry_leptonL]

/-- ρ₁ entry, left-antiquark block: π₁'s doublet action on the
color-diagonal. -/
theorem rho1_entry_quarkLc (b : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    rho1 b ⟨18 + 2 * ki.val + si.val, by omega⟩
        ⟨18 + 2 * kj.val + sj.val, by omega⟩
      = if kj = ki then b.q sj si else 0 := by
  rw [rho1_entry, partner_mk_quarkLc kj sj, partner_mk_quarkLc ki si,
    pi1_entry_quarkL]

/-- ρ₁ entry, ν_Rᶜ slot. -/
theorem rho1_entry_nuRc (b : AF) :
    rho1 b ⟨24, by omega⟩ ⟨24, by omega⟩ = b.u1 := by
  rw [rho1_entry, partner_mk24, pi1_entry_nuR]

/-- ρ₁ entry, e_Rᶜ slot. -/
theorem rho1_entry_eRc (b : AF) :
    rho1 b ⟨25, by omega⟩ ⟨25, by omega⟩ = star b.u1 := by
  rw [rho1_entry, partner_mk25, pi1_entry_eR]

/-- ρ₁ entry, right-antiquark block: π₁'s right action, transposed. -/
theorem rho1_entry_quarkRc (b : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    rho1 b ⟨26 + 2 * ki.val + si.val, by omega⟩
        ⟨26 + 2 * kj.val + sj.val, by omega⟩
      = if sj = si ∧ kj = ki then (if sj = 0 then b.u1 else star b.u1)
        else 0 := by
  rw [rho1_entry, partner_mk_quarkRc kj sj, partner_mk_quarkRc ki si,
    pi1_entry_quarkR]

/-! ### Block support, extracted once

For every block: the `¬sameBlock` fact behind the §3 product
hvans, restated standalone (the hvan branch bodies with the
entry lemmas replaced by their `not_sameBlock_of_*`
companions, whose hypotheses are identical). Row and
column vanishing, partner finset transport, and the
per-block order-zero computation follow. -/

/-- Support of the leptonL block: slots outside the block's
finset are not in the block. -/
theorem not_sameBlock_leptonL (s : Fin 2) :
    ∀ k : I32, k ∉ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset I32) → ¬ sameBlock ⟨s.val, by omega⟩ k := by
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  by_cases hk8 : k.val < 8
  · by_cases hk2 : k.val < 2
    · have hkv : k.val = 0 ∨ k.val = 1 := by omega
      rcases hkv with h0 | h1
      · exact absurd (Fin.ext h0) hk.1
      · exact absurd (Fin.ext h1) hk.2
    · exact not_sameBlock_of_HL_mixed (i := ⟨s.val, by omega⟩) (j := k)
        (Or.inl ⟨(by show s.val < 2; omega), (by omega), hk8⟩)
  · exact not_sameBlock_of_ne_sector (i := ⟨s.val, by omega⟩) (j := k)
      (by show s.val / 8 ≠ k.val / 8; omega)

/-- Row vanishing for the leptonL block. -/
theorem pi1_vanish_leptonL (a : AF) (s : Fin 2) (k : I32)
    (hk : k ∉ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset I32)) : pi1 a ⟨s.val, by omega⟩ k = 0 :=
  pi1_entry_eq_zero_of_not_sameBlock a (not_sameBlock_leptonL s k hk)

/-- Column vanishing for the leptonL block. -/
theorem pi1_vanish_col_leptonL (a : AF) (s : Fin 2) (k : I32)
    (hk : k ∉ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset I32)) : pi1 a k ⟨s.val, by omega⟩ = 0 :=
  pi1_entry_eq_zero_of_not_sameBlock a
    (fun hsb => not_sameBlock_leptonL s k hk (sameBlock_symm hsb))

/-- Support of the quarkL block: slots outside the block's
finset are not in the block. -/
theorem not_sameBlock_quarkL (ki : Fin 3) (si : Fin 2) :
    ∀ k : I32, k ∉ ({⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) → ¬ sameBlock ⟨2 + 2 * ki.val + si.val, by omega⟩ k := by
  intro k hk
  by_cases hk8 : k.val < 8
  · by_cases hk2 : 2 ≤ k.val
    · have hkv : k.val = 2 ∨ k.val = 3 ∨ k.val = 4 ∨ k.val = 5 ∨ k.val = 6 ∨
          k.val = 7 := by omega
      have hmem : k ∈ ({⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
          ⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
          ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
          ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
          ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
          ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hkv with h | h | h | h | h | h <;>
          first
            | exact Or.inl (Fin.ext (show k.val = 2 by omega))
            | exact Or.inr (Or.inl (Fin.ext (show k.val = 3 by omega)))
            | exact Or.inr (Or.inr (Or.inl (Fin.ext (show k.val = 4 by omega))))
            | exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (show k.val = 5 by omega)))))
            | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (show k.val = 6 by omega))))))
            | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext (show k.val = 7 by omega))))))
      exact absurd hmem hk
    · exact not_sameBlock_of_HL_mixed (i := ⟨2 + 2 * ki.val + si.val, by omega⟩) (j := k)
        (Or.inr ⟨(by show 2 ≤ 2 + 2 * ki.val + si.val; omega),
          (by show 2 + 2 * ki.val + si.val < 8; omega), (by omega)⟩)
  · exact not_sameBlock_of_ne_sector (i := ⟨2 + 2 * ki.val + si.val, by omega⟩) (j := k)
      (by show (2 + 2 * ki.val + si.val) / 8 ≠ k.val / 8; omega)

/-- Row vanishing for the quarkL block. -/
theorem pi1_vanish_quarkL (a : AF) (ki : Fin 3) (si : Fin 2) (k : I32)
    (hk : k ∉ ({⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32)) : pi1 a ⟨2 + 2 * ki.val + si.val, by omega⟩ k = 0 :=
  pi1_entry_eq_zero_of_not_sameBlock a (not_sameBlock_quarkL ki si k hk)

/-- Column vanishing for the quarkL block. -/
theorem pi1_vanish_col_quarkL (a : AF) (ki : Fin 3) (si : Fin 2) (k : I32)
    (hk : k ∉ ({⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32)) : pi1 a k ⟨2 + 2 * ki.val + si.val, by omega⟩ = 0 :=
  pi1_entry_eq_zero_of_not_sameBlock a
    (fun hsb => not_sameBlock_quarkL ki si k hk (sameBlock_symm hsb))

/-- Support of the nuR block: slots outside the block's
finset are not in the block. -/
theorem not_sameBlock_nuR  :
    ∀ k : I32, k ∉ ({⟨8, by omega⟩} : Finset I32) → ¬ sameBlock ⟨8, by omega⟩ k := by
  intro k hk
  simp only [Finset.mem_singleton] at hk
  have hk8v : k.val ≠ 8 := fun hv => hk (Fin.ext hv)
  by_cases hk8 : k.val < 8
  · exact not_sameBlock_of_ne_sector (i := ⟨8, by omega⟩) (j := k)
      (by show (8:ℕ) / 8 ≠ k.val / 8; omega)
  · by_cases hk16 : k.val < 16
    · by_cases hk9 : k.val = 9
      · exact not_sameBlock_of_HR_mixed (i := ⟨8, by omega⟩) (j := k)
          (Or.inl ⟨rfl, hk9⟩)
      · exact not_sameBlock_of_HR_mixed (i := ⟨8, by omega⟩) (j := k)
          (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, by omega, hk16⟩)))
    · exact not_sameBlock_of_ne_sector (i := ⟨8, by omega⟩) (j := k)
        (by show (8:ℕ) / 8 ≠ k.val / 8; omega)

/-- Row vanishing for the nuR block. -/
theorem pi1_vanish_nuR (a : AF)  (k : I32)
    (hk : k ∉ ({⟨8, by omega⟩} : Finset I32)) : pi1 a ⟨8, by omega⟩ k = 0 :=
  pi1_entry_eq_zero_of_not_sameBlock a (not_sameBlock_nuR  k hk)

/-- Column vanishing for the nuR block. -/
theorem pi1_vanish_col_nuR (a : AF)  (k : I32)
    (hk : k ∉ ({⟨8, by omega⟩} : Finset I32)) : pi1 a k ⟨8, by omega⟩ = 0 :=
  pi1_entry_eq_zero_of_not_sameBlock a
    (fun hsb => not_sameBlock_nuR  k hk (sameBlock_symm hsb))

/-- Support of the eR block: slots outside the block's
finset are not in the block. -/
theorem not_sameBlock_eR  :
    ∀ k : I32, k ∉ ({⟨9, by omega⟩} : Finset I32) → ¬ sameBlock ⟨9, by omega⟩ k := by
  intro k hk
  simp only [Finset.mem_singleton] at hk
  have hk9v : k.val ≠ 9 := fun hv => hk (Fin.ext hv)
  by_cases hk8 : k.val < 8
  · exact not_sameBlock_of_ne_sector (i := ⟨9, by omega⟩) (j := k)
      (by show (9:ℕ) / 8 ≠ k.val / 8; omega)
  · by_cases hk16 : k.val < 16
    · by_cases hk8' : k.val = 8
      · exact not_sameBlock_of_HR_mixed (i := ⟨9, by omega⟩) (j := k)
          (Or.inr (Or.inl ⟨rfl, hk8'⟩))
      · exact not_sameBlock_of_HR_mixed (i := ⟨9, by omega⟩) (j := k)
          (Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, by omega, hk16⟩)))
    · exact not_sameBlock_of_ne_sector (i := ⟨9, by omega⟩) (j := k)
        (by show (9:ℕ) / 8 ≠ k.val / 8; omega)

/-- Row vanishing for the eR block. -/
theorem pi1_vanish_eR (a : AF)  (k : I32)
    (hk : k ∉ ({⟨9, by omega⟩} : Finset I32)) : pi1 a ⟨9, by omega⟩ k = 0 :=
  pi1_entry_eq_zero_of_not_sameBlock a (not_sameBlock_eR  k hk)

/-- Column vanishing for the eR block. -/
theorem pi1_vanish_col_eR (a : AF)  (k : I32)
    (hk : k ∉ ({⟨9, by omega⟩} : Finset I32)) : pi1 a k ⟨9, by omega⟩ = 0 :=
  pi1_entry_eq_zero_of_not_sameBlock a
    (fun hsb => not_sameBlock_eR  k hk (sameBlock_symm hsb))

/-- Support of the quarkR block: slots outside the block's
finset are not in the block. -/
theorem not_sameBlock_quarkR (ki : Fin 3) (si : Fin 2) :
    ∀ k : I32, k ∉ ({⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) → ¬ sameBlock ⟨10 + 2 * ki.val + si.val, by omega⟩ k := by
  intro k hk
  by_cases hklo : k.val < 8
  · exact not_sameBlock_of_ne_sector (i := ⟨10 + 2 * ki.val + si.val, by omega⟩) (j := k)
      (by show (10 + 2 * ki.val + si.val) / 8 ≠ k.val / 8; omega)
  · by_cases hkhi : 16 ≤ k.val
    · exact not_sameBlock_of_ne_sector (i := ⟨10 + 2 * ki.val + si.val, by omega⟩) (j := k)
        (by show (10 + 2 * ki.val + si.val) / 8 ≠ k.val / 8; omega)
    · by_cases hk10 : 10 ≤ k.val
      · have hkv : k.val = 10 ∨ k.val = 11 ∨ k.val = 12 ∨ k.val = 13 ∨
            k.val = 14 ∨ k.val = 15 := by omega
        have hmem : k ∈ ({⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
            ⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
            ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
            ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
            ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
            ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hkv with h | h | h | h | h | h <;>
            first
              | exact Or.inl (Fin.ext (show k.val = 10 by omega))
              | exact Or.inr (Or.inl (Fin.ext (show k.val = 11 by omega)))
              | exact Or.inr (Or.inr (Or.inl (Fin.ext (show k.val = 12 by omega))))
              | exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (show k.val = 13 by omega)))))
              | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (show k.val = 14 by omega))))))
              | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext (show k.val = 15 by omega))))))
        exact absurd hmem hk
      · by_cases hk8 : k.val = 8
        · exact not_sameBlock_of_HR_mixed (i := ⟨10 + 2 * ki.val + si.val, by omega⟩) (j := k)
            (Or.inr (Or.inr (Or.inr ⟨(by show 10 ≤ 10 + 2 * ki.val + si.val; omega),
              (by show 10 + 2 * ki.val + si.val < 16; omega), Or.inl hk8⟩)))
        · exact not_sameBlock_of_HR_mixed (i := ⟨10 + 2 * ki.val + si.val, by omega⟩) (j := k)
            (Or.inr (Or.inr (Or.inr ⟨(by show 10 ≤ 10 + 2 * ki.val + si.val; omega),
              (by show 10 + 2 * ki.val + si.val < 16; omega),
              Or.inr (by omega : k.val = 9)⟩)))

/-- Row vanishing for the quarkR block. -/
theorem pi1_vanish_quarkR (a : AF) (ki : Fin 3) (si : Fin 2) (k : I32)
    (hk : k ∉ ({⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32)) : pi1 a ⟨10 + 2 * ki.val + si.val, by omega⟩ k = 0 :=
  pi1_entry_eq_zero_of_not_sameBlock a (not_sameBlock_quarkR ki si k hk)

/-- Column vanishing for the quarkR block. -/
theorem pi1_vanish_col_quarkR (a : AF) (ki : Fin 3) (si : Fin 2) (k : I32)
    (hk : k ∉ ({⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32)) : pi1 a k ⟨10 + 2 * ki.val + si.val, by omega⟩ = 0 :=
  pi1_entry_eq_zero_of_not_sameBlock a
    (fun hsb => not_sameBlock_quarkR ki si k hk (sameBlock_symm hsb))

/-- Support of the leptonLc block: slots outside the block's
finset are not in the block. -/
theorem not_sameBlock_leptonLc (s : Fin 2) :
    ∀ k : I32, k ∉ ({⟨16 + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨16 + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) → ¬ sameBlock ⟨16 + s.val, by omega⟩ k := by
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  by_cases hk24 : k.val < 24
  · by_cases hk16 : 16 ≤ k.val
    · by_cases hk18 : k.val < 18
      · have hkv : k.val = 16 ∨ k.val = 17 := by omega
        rcases hkv with h0 | h1
        · exact absurd (Fin.ext (show k.val = 16 by omega)) hk.1
        · exact absurd (Fin.ext (show k.val = 17 by omega)) hk.2
      · exact not_sameBlock_of_Hc_mixed (i := ⟨16 + s.val, by omega⟩) (j := k)
          (Or.inl ⟨(by show 16 ≤ 16 + s.val; omega), (by show 16 + s.val < 18; omega),
            (by omega), hk24⟩)
    · exact not_sameBlock_of_ne_sector (i := ⟨16 + s.val, by omega⟩) (j := k)
        (by show (16 + s.val) / 8 ≠ k.val / 8; omega)
  · exact not_sameBlock_of_ne_sector (i := ⟨16 + s.val, by omega⟩) (j := k)
      (by show (16 + s.val) / 8 ≠ k.val / 8; omega)

/-- Row vanishing for the leptonLc block. -/
theorem pi1_vanish_leptonLc (a : AF) (s : Fin 2) (k : I32)
    (hk : k ∉ ({⟨16 + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨16 + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32)) : pi1 a ⟨16 + s.val, by omega⟩ k = 0 :=
  pi1_entry_eq_zero_of_not_sameBlock a (not_sameBlock_leptonLc s k hk)

/-- Column vanishing for the leptonLc block. -/
theorem pi1_vanish_col_leptonLc (a : AF) (s : Fin 2) (k : I32)
    (hk : k ∉ ({⟨16 + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨16 + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32)) : pi1 a k ⟨16 + s.val, by omega⟩ = 0 :=
  pi1_entry_eq_zero_of_not_sameBlock a
    (fun hsb => not_sameBlock_leptonLc s k hk (sameBlock_symm hsb))

/-- Support of the quarkLc block: slots outside the block's
finset are not in the block. -/
theorem not_sameBlock_quarkLc (ki : Fin 3) (si : Fin 2) :
    ∀ k : I32, k ∉ ({⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) → ¬ sameBlock ⟨18 + 2 * ki.val + si.val, by omega⟩ k := by
  intro k hk
  by_cases hk24 : k.val < 24
  · by_cases hk16 : 16 ≤ k.val
    · by_cases hk18 : 18 ≤ k.val
      · have hkv : k.val = 18 ∨ k.val = 19 ∨ k.val = 20 ∨ k.val = 21 ∨
            k.val = 22 ∨ k.val = 23 := by omega
        have hmem : k ∈ ({⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
            ⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
            ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
            ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
            ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
            ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hkv with h | h | h | h | h | h <;>
            first
              | exact Or.inl (Fin.ext (show k.val = 18 by omega))
              | exact Or.inr (Or.inl (Fin.ext (show k.val = 19 by omega)))
              | exact Or.inr (Or.inr (Or.inl (Fin.ext (show k.val = 20 by omega))))
              | exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (show k.val = 21 by omega)))))
              | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (show k.val = 22 by omega))))))
              | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext (show k.val = 23 by omega))))))
        exact absurd hmem hk
      · exact not_sameBlock_of_Hc_mixed (i := ⟨18 + 2 * ki.val + si.val, by omega⟩) (j := k)
          (Or.inr (Or.inl ⟨(by show 18 ≤ 18 + 2 * ki.val + si.val; omega),
            (by show 18 + 2 * ki.val + si.val < 24; omega), hk16, (by omega)⟩))
    · exact not_sameBlock_of_ne_sector (i := ⟨18 + 2 * ki.val + si.val, by omega⟩) (j := k)
        (by show (18 + 2 * ki.val + si.val) / 8 ≠ k.val / 8; omega)
  · exact not_sameBlock_of_ne_sector (i := ⟨18 + 2 * ki.val + si.val, by omega⟩) (j := k)
      (by show (18 + 2 * ki.val + si.val) / 8 ≠ k.val / 8; omega)

/-- Row vanishing for the quarkLc block. -/
theorem pi1_vanish_quarkLc (a : AF) (ki : Fin 3) (si : Fin 2) (k : I32)
    (hk : k ∉ ({⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32)) : pi1 a ⟨18 + 2 * ki.val + si.val, by omega⟩ k = 0 :=
  pi1_entry_eq_zero_of_not_sameBlock a (not_sameBlock_quarkLc ki si k hk)

/-- Column vanishing for the quarkLc block. -/
theorem pi1_vanish_col_quarkLc (a : AF) (ki : Fin 3) (si : Fin 2) (k : I32)
    (hk : k ∉ ({⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32)) : pi1 a k ⟨18 + 2 * ki.val + si.val, by omega⟩ = 0 :=
  pi1_entry_eq_zero_of_not_sameBlock a
    (fun hsb => not_sameBlock_quarkLc ki si k hk (sameBlock_symm hsb))

/-- Support of the nuRc block: slots outside the block's
finset are not in the block. -/
theorem not_sameBlock_nuRc  :
    ∀ k : I32, k ∉ ({⟨24, by omega⟩} : Finset I32) → ¬ sameBlock ⟨24, by omega⟩ k := by
  intro k hk
  simp only [Finset.mem_singleton] at hk
  have hk24v : k.val ≠ 24 := fun hv => hk (Fin.ext hv)
  by_cases hk24 : k.val < 24
  · exact not_sameBlock_of_ne_sector (i := ⟨24, by omega⟩) (j := k)
      (by show (24:ℕ) / 8 ≠ k.val / 8; omega)
  · by_cases hk25 : k.val = 25
    · exact not_sameBlock_of_Hc_mixed (i := ⟨24, by omega⟩) (j := k)
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hk25⟩)))))))
    · exact not_sameBlock_of_Hc_mixed (i := ⟨24, by omega⟩) (j := k)
        (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩)))

/-- Row vanishing for the nuRc block. -/
theorem pi1_vanish_nuRc (a : AF)  (k : I32)
    (hk : k ∉ ({⟨24, by omega⟩} : Finset I32)) : pi1 a ⟨24, by omega⟩ k = 0 :=
  pi1_entry_eq_zero_of_not_sameBlock a (not_sameBlock_nuRc  k hk)

/-- Column vanishing for the nuRc block. -/
theorem pi1_vanish_col_nuRc (a : AF)  (k : I32)
    (hk : k ∉ ({⟨24, by omega⟩} : Finset I32)) : pi1 a k ⟨24, by omega⟩ = 0 :=
  pi1_entry_eq_zero_of_not_sameBlock a
    (fun hsb => not_sameBlock_nuRc  k hk (sameBlock_symm hsb))

/-- Support of the eRc block: slots outside the block's
finset are not in the block. -/
theorem not_sameBlock_eRc  :
    ∀ k : I32, k ∉ ({⟨25, by omega⟩} : Finset I32) → ¬ sameBlock ⟨25, by omega⟩ k := by
  intro k hk
  simp only [Finset.mem_singleton] at hk
  have hk25v : k.val ≠ 25 := fun hv => hk (Fin.ext hv)
  by_cases hk24 : k.val < 24
  · exact not_sameBlock_of_ne_sector (i := ⟨25, by omega⟩) (j := k)
      (by show (25:ℕ) / 8 ≠ k.val / 8; omega)
  · by_cases hk24' : k.val = 24
    · exact not_sameBlock_of_Hc_mixed (i := ⟨25, by omega⟩) (j := k)
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hk24'⟩)))))))
    · exact not_sameBlock_of_Hc_mixed (i := ⟨25, by omega⟩) (j := k)
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))))

/-- Row vanishing for the eRc block. -/
theorem pi1_vanish_eRc (a : AF)  (k : I32)
    (hk : k ∉ ({⟨25, by omega⟩} : Finset I32)) : pi1 a ⟨25, by omega⟩ k = 0 :=
  pi1_entry_eq_zero_of_not_sameBlock a (not_sameBlock_eRc  k hk)

/-- Column vanishing for the eRc block. -/
theorem pi1_vanish_col_eRc (a : AF)  (k : I32)
    (hk : k ∉ ({⟨25, by omega⟩} : Finset I32)) : pi1 a k ⟨25, by omega⟩ = 0 :=
  pi1_entry_eq_zero_of_not_sameBlock a
    (fun hsb => not_sameBlock_eRc  k hk (sameBlock_symm hsb))

/-- Support of the quarkRc block: slots outside the block's
finset are not in the block. -/
theorem not_sameBlock_quarkRc (ki : Fin 3) (si : Fin 2) :
    ∀ k : I32, k ∉ ({⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩} : Finset I32) → ¬ sameBlock ⟨26 + 2 * ki.val + si.val, by omega⟩ k := by
  intro k hk
  by_cases hk24 : k.val < 24
  · exact not_sameBlock_of_ne_sector (i := ⟨26 + 2 * ki.val + si.val, by omega⟩) (j := k)
      (by show (26 + 2 * ki.val + si.val) / 8 ≠ k.val / 8; omega)
  · by_cases hk26 : 26 ≤ k.val
    · have hkv : k.val = 26 ∨ k.val = 27 ∨ k.val = 28 ∨ k.val = 29 ∨
          k.val = 30 ∨ k.val = 31 := by omega
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6⟩ := hk
      rcases hkv with h | h | h | h | h | h
      · exact absurd (Fin.ext (show k.val = 26 by omega)) hk1
      · exact absurd (Fin.ext (show k.val = 27 by omega)) hk2
      · exact absurd (Fin.ext (show k.val = 28 by omega)) hk3
      · exact absurd (Fin.ext (show k.val = 29 by omega)) hk4
      · exact absurd (Fin.ext (show k.val = 30 by omega)) hk5
      · exact absurd (Fin.ext (show k.val = 31 by omega)) hk6
    · by_cases hk24' : k.val = 24
      · exact not_sameBlock_of_Hc_mixed (i := ⟨26 + 2 * ki.val + si.val, by omega⟩) (j := k)
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨(by show 26 ≤ 26 + 2 * ki.val + si.val; omega), hk24'⟩)))))
      · exact not_sameBlock_of_Hc_mixed (i := ⟨26 + 2 * ki.val + si.val, by omega⟩) (j := k)
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨(by show 26 ≤ 26 + 2 * ki.val + si.val; omega),
              (by omega : k.val = 25)⟩))))))

/-- Row vanishing for the quarkRc block. -/
theorem pi1_vanish_quarkRc (a : AF) (ki : Fin 3) (si : Fin 2) (k : I32)
    (hk : k ∉ ({⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩} : Finset I32)) : pi1 a ⟨26 + 2 * ki.val + si.val, by omega⟩ k = 0 :=
  pi1_entry_eq_zero_of_not_sameBlock a (not_sameBlock_quarkRc ki si k hk)

/-- Column vanishing for the quarkRc block. -/
theorem pi1_vanish_col_quarkRc (a : AF) (ki : Fin 3) (si : Fin 2) (k : I32)
    (hk : k ∉ ({⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩} : Finset I32)) : pi1 a k ⟨26 + 2 * ki.val + si.val, by omega⟩ = 0 :=
  pi1_entry_eq_zero_of_not_sameBlock a
    (fun hsb => not_sameBlock_quarkRc ki si k hk (sameBlock_symm hsb))

/-- The partner map sends the leptonLc finset into the leptonL
finset, elementwise. -/
theorem partner_image_leptonL :
    ∀ x : I32, x ∈ ({⟨16 + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨16 + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) → partner x ∈ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset I32) := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inl (by apply Fin.ext; simp only [partner_val_eq]; split_ifs <;> omega))
  rw [Finset.mem_singleton] at hx
  rcases hx with rfl
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (by apply Fin.ext; simp only [partner_val_eq]; split_ifs <;> omega)))

/-- Partner transport of the leptonL finset complement. -/
theorem partner_not_mem_leptonL {k : I32}
    (hk : k ∉ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset I32)) :
    partner k ∉ ({⟨16 + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨16 + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) :=
  partner_not_mem_of partner_image_leptonL hk

/-- The partner map sends the quarkLc finset into the quarkL
finset, elementwise. -/
theorem partner_image_quarkL :
    ∀ x : I32, x ∈ ({⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) → partner x ∈ ({⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inl (partner_mk_quarkLc ⟨0, by omega⟩ ⟨0, by omega⟩))
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (partner_mk_quarkLc ⟨0, by omega⟩ ⟨1, by omega⟩))))
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (partner_mk_quarkLc ⟨1, by omega⟩ ⟨0, by omega⟩))))))
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (partner_mk_quarkLc ⟨1, by omega⟩ ⟨1, by omega⟩))))))))
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (partner_mk_quarkLc ⟨2, by omega⟩ ⟨0, by omega⟩))))))))))
  rw [Finset.mem_singleton] at hx
  rcases hx with rfl
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (partner_mk_quarkLc ⟨2, by omega⟩ ⟨1, by omega⟩)))))))))))

/-- Partner transport of the quarkL finset complement. -/
theorem partner_not_mem_quarkL {k : I32}
    (hk : k ∉ ({⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32)) :
    partner k ∉ ({⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) :=
  partner_not_mem_of partner_image_quarkL hk

/-- The partner map sends the nuRc finset into the nuR
finset, elementwise. -/
theorem partner_image_nuR :
    ∀ x : I32, x ∈ ({⟨24, by omega⟩} : Finset I32) → partner x ∈ ({⟨8, by omega⟩} : Finset I32) := by
  intro x hx
  rw [Finset.mem_singleton] at hx
  rcases hx with rfl
  exact Finset.mem_singleton.mpr (by apply Fin.ext; simp only [partner_val_eq]; split_ifs <;> omega)

/-- Partner transport of the nuR finset complement. -/
theorem partner_not_mem_nuR {k : I32}
    (hk : k ∉ ({⟨8, by omega⟩} : Finset I32)) :
    partner k ∉ ({⟨24, by omega⟩} : Finset I32) :=
  partner_not_mem_of partner_image_nuR hk

/-- The partner map sends the eRc finset into the eR
finset, elementwise. -/
theorem partner_image_eR :
    ∀ x : I32, x ∈ ({⟨25, by omega⟩} : Finset I32) → partner x ∈ ({⟨9, by omega⟩} : Finset I32) := by
  intro x hx
  rw [Finset.mem_singleton] at hx
  rcases hx with rfl
  exact Finset.mem_singleton.mpr (by apply Fin.ext; simp only [partner_val_eq]; split_ifs <;> omega)

/-- Partner transport of the eR finset complement. -/
theorem partner_not_mem_eR {k : I32}
    (hk : k ∉ ({⟨9, by omega⟩} : Finset I32)) :
    partner k ∉ ({⟨25, by omega⟩} : Finset I32) :=
  partner_not_mem_of partner_image_eR hk

/-- The partner map sends the quarkRc finset into the quarkR
finset, elementwise. -/
theorem partner_image_quarkR :
    ∀ x : I32, x ∈ ({⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩} : Finset I32) → partner x ∈ ({⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inl (partner_mk_quarkRc ⟨0, by omega⟩ ⟨0, by omega⟩))
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (partner_mk_quarkRc ⟨0, by omega⟩ ⟨1, by omega⟩))))
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (partner_mk_quarkRc ⟨1, by omega⟩ ⟨0, by omega⟩))))))
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (partner_mk_quarkRc ⟨1, by omega⟩ ⟨1, by omega⟩))))))))
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (partner_mk_quarkRc ⟨2, by omega⟩ ⟨0, by omega⟩))))))))))
  rw [Finset.mem_singleton] at hx
  rcases hx with rfl
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (partner_mk_quarkRc ⟨2, by omega⟩ ⟨1, by omega⟩)))))))))))

/-- Partner transport of the quarkR finset complement. -/
theorem partner_not_mem_quarkR {k : I32}
    (hk : k ∉ ({⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32)) :
    partner k ∉ ({⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩} : Finset I32) :=
  partner_not_mem_of partner_image_quarkR hk

/-- The partner map sends the leptonL finset into the leptonLc
finset, elementwise. -/
theorem partner_image_leptonLc :
    ∀ x : I32, x ∈ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset I32) → partner x ∈ ({⟨16 + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨16 + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inl (by apply Fin.ext; simp only [partner_val_eq]; split_ifs <;> omega))
  rw [Finset.mem_singleton] at hx
  rcases hx with rfl
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (by apply Fin.ext; simp only [partner_val_eq]; split_ifs <;> omega)))

/-- Partner transport of the leptonLc finset complement. -/
theorem partner_not_mem_leptonLc {k : I32}
    (hk : k ∉ ({⟨16 + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨16 + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32)) :
    partner k ∉ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset I32) :=
  partner_not_mem_of partner_image_leptonLc hk

/-- The partner map sends the quarkL finset into the quarkLc
finset, elementwise. -/
theorem partner_image_quarkLc :
    ∀ x : I32, x ∈ ({⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) → partner x ∈ ({⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inl (partner_mk_quarkL ⟨0, by omega⟩ ⟨0, by omega⟩))
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (partner_mk_quarkL ⟨0, by omega⟩ ⟨1, by omega⟩))))
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (partner_mk_quarkL ⟨1, by omega⟩ ⟨0, by omega⟩))))))
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (partner_mk_quarkL ⟨1, by omega⟩ ⟨1, by omega⟩))))))))
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (partner_mk_quarkL ⟨2, by omega⟩ ⟨0, by omega⟩))))))))))
  rw [Finset.mem_singleton] at hx
  rcases hx with rfl
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (partner_mk_quarkL ⟨2, by omega⟩ ⟨1, by omega⟩)))))))))))

/-- Partner transport of the quarkLc finset complement. -/
theorem partner_not_mem_quarkLc {k : I32}
    (hk : k ∉ ({⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32)) :
    partner k ∉ ({⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) :=
  partner_not_mem_of partner_image_quarkLc hk

/-- The partner map sends the nuR finset into the nuRc
finset, elementwise. -/
theorem partner_image_nuRc :
    ∀ x : I32, x ∈ ({⟨8, by omega⟩} : Finset I32) → partner x ∈ ({⟨24, by omega⟩} : Finset I32) := by
  intro x hx
  rw [Finset.mem_singleton] at hx
  rcases hx with rfl
  exact Finset.mem_singleton.mpr (by apply Fin.ext; simp only [partner_val_eq]; split_ifs <;> omega)

/-- Partner transport of the nuRc finset complement. -/
theorem partner_not_mem_nuRc {k : I32}
    (hk : k ∉ ({⟨24, by omega⟩} : Finset I32)) :
    partner k ∉ ({⟨8, by omega⟩} : Finset I32) :=
  partner_not_mem_of partner_image_nuRc hk

/-- The partner map sends the eR finset into the eRc
finset, elementwise. -/
theorem partner_image_eRc :
    ∀ x : I32, x ∈ ({⟨9, by omega⟩} : Finset I32) → partner x ∈ ({⟨25, by omega⟩} : Finset I32) := by
  intro x hx
  rw [Finset.mem_singleton] at hx
  rcases hx with rfl
  exact Finset.mem_singleton.mpr (by apply Fin.ext; simp only [partner_val_eq]; split_ifs <;> omega)

/-- Partner transport of the eRc finset complement. -/
theorem partner_not_mem_eRc {k : I32}
    (hk : k ∉ ({⟨25, by omega⟩} : Finset I32)) :
    partner k ∉ ({⟨9, by omega⟩} : Finset I32) :=
  partner_not_mem_of partner_image_eRc hk

/-- The partner map sends the quarkR finset into the quarkRc
finset, elementwise. -/
theorem partner_image_quarkRc :
    ∀ x : I32, x ∈ ({⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) → partner x ∈ ({⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩} : Finset I32) := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inl (partner_mk_quarkR ⟨0, by omega⟩ ⟨0, by omega⟩))
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (partner_mk_quarkR ⟨0, by omega⟩ ⟨1, by omega⟩))))
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (partner_mk_quarkR ⟨1, by omega⟩ ⟨0, by omega⟩))))))
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (partner_mk_quarkR ⟨1, by omega⟩ ⟨1, by omega⟩))))))))
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (partner_mk_quarkR ⟨2, by omega⟩ ⟨0, by omega⟩))))))))))
  rw [Finset.mem_singleton] at hx
  rcases hx with rfl
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (partner_mk_quarkR ⟨2, by omega⟩ ⟨1, by omega⟩)))))))))))

/-- Partner transport of the quarkRc finset complement. -/
theorem partner_not_mem_quarkRc {k : I32}
    (hk : k ∉ ({⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩} : Finset I32)) :
    partner k ∉ ({⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) :=
  partner_not_mem_of partner_image_quarkRc hk

/-- **Order-zero, leptonL block**: the two products agree entrywise
on the block (both sums collapse to the block finset; the summands
agree by the summand-pure conjugate entries). -/
theorem pi1_rho1_comm_leptonL (a b : AF) (s t : Fin 2) :
    (pi1 a * rho1 b) ⟨s.val, by omega⟩ ⟨t.val, by omega⟩ = (rho1 b * pi1 a) ⟨s.val, by omega⟩ ⟨t.val, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset I32) →
      pi1 a ⟨s.val, by omega⟩ k * rho1 b k ⟨t.val, by omega⟩ = 0 := by
    intro k hk
    rw [pi1_vanish_leptonL a s k hk, zero_mul]
  have hvanR : ∀ k : I32, k ∉ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset I32) →
      rho1 b ⟨s.val, by omega⟩ k * pi1 a k ⟨t.val, by omega⟩ = 0 := by
    intro k hk
    rw [rho1_entry, partner_mk_add16 s.val (by omega),
      pi1_vanish_col_leptonLc b s (partner k) (partner_not_mem_leptonL hk),
      zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_pair (by decide : (⟨0, by omega⟩ : I32) ≠ ⟨1, by omega⟩),
    pi1_entry_leptonL a s ⟨0, by omega⟩,
    rho1_entry_leptonL b ⟨0, by omega⟩ t,
    pi1_entry_leptonL a s ⟨1, by omega⟩,
    rho1_entry_leptonL b ⟨1, by omega⟩ t]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvanR,
    Finset.sum_pair (by decide : (⟨0, by omega⟩ : I32) ≠ ⟨1, by omega⟩),
    rho1_entry_leptonL b s ⟨0, by omega⟩,
    pi1_entry_leptonL a ⟨0, by omega⟩ t,
    rho1_entry_leptonL b s ⟨1, by omega⟩,
    pi1_entry_leptonL a ⟨1, by omega⟩ t]
  try (fin_cases s <;> fin_cases t <;> simp <;> ring)

/-- **Order-zero, quarkL block**: the two products agree entrywise
on the block (both sums collapse to the block finset; the summands
agree by the summand-pure conjugate entries). -/
theorem pi1_rho1_comm_quarkL (a b : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    (pi1 a * rho1 b) ⟨2 + 2 * ki.val + si.val, by omega⟩ ⟨2 + 2 * kj.val + sj.val, by omega⟩ = (rho1 b * pi1 a) ⟨2 + 2 * ki.val + si.val, by omega⟩ ⟨2 + 2 * kj.val + sj.val, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) →
      pi1 a ⟨2 + 2 * ki.val + si.val, by omega⟩ k * rho1 b k ⟨2 + 2 * kj.val + sj.val, by omega⟩ = 0 := by
    intro k hk
    rw [pi1_vanish_quarkL a ki si k hk, zero_mul]
  have hvanR : ∀ k : I32, k ∉ ({⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) →
      rho1 b ⟨2 + 2 * ki.val + si.val, by omega⟩ k * pi1 a k ⟨2 + 2 * kj.val + sj.val, by omega⟩ = 0 := by
    intro k hk
    rw [rho1_entry, partner_mk_quarkL ki si,
      pi1_vanish_col_quarkLc b ki si (partner k) (partner_not_mem_quarkL hk),
      zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    pi1_entry_quarkL a ki ⟨0, by omega⟩ si ⟨0, by omega⟩,
    rho1_entry_quarkL b ⟨0, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkL a ki ⟨0, by omega⟩ si ⟨1, by omega⟩,
    rho1_entry_quarkL b ⟨0, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi1_entry_quarkL a ki ⟨1, by omega⟩ si ⟨0, by omega⟩,
    rho1_entry_quarkL b ⟨1, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkL a ki ⟨1, by omega⟩ si ⟨1, by omega⟩,
    rho1_entry_quarkL b ⟨1, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi1_entry_quarkL a ki ⟨2, by omega⟩ si ⟨0, by omega⟩,
    rho1_entry_quarkL b ⟨2, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkL a ki ⟨2, by omega⟩ si ⟨1, by omega⟩,
    rho1_entry_quarkL b ⟨2, by omega⟩ kj ⟨1, by omega⟩ sj]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvanR,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    rho1_entry_quarkL b ki ⟨0, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkL a ⟨0, by omega⟩ kj ⟨0, by omega⟩ sj,
    rho1_entry_quarkL b ki ⟨0, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkL a ⟨0, by omega⟩ kj ⟨1, by omega⟩ sj,
    rho1_entry_quarkL b ki ⟨1, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkL a ⟨1, by omega⟩ kj ⟨0, by omega⟩ sj,
    rho1_entry_quarkL b ki ⟨1, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkL a ⟨1, by omega⟩ kj ⟨1, by omega⟩ sj,
    rho1_entry_quarkL b ki ⟨2, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkL a ⟨2, by omega⟩ kj ⟨0, by omega⟩ sj,
    rho1_entry_quarkL b ki ⟨2, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkL a ⟨2, by omega⟩ kj ⟨1, by omega⟩ sj]
  try (fin_cases ki <;> fin_cases kj <;> fin_cases si <;> fin_cases sj <;> simp <;> ring)

/-- **Order-zero, nuR block**: the two products agree entrywise
on the block (both sums collapse to the block finset; the summands
agree by the summand-pure conjugate entries). -/
theorem pi1_rho1_comm_nuR (a b : AF) :
    (pi1 a * rho1 b) ⟨8, by omega⟩ ⟨8, by omega⟩ = (rho1 b * pi1 a) ⟨8, by omega⟩ ⟨8, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨8, by omega⟩} : Finset I32) →
      pi1 a ⟨8, by omega⟩ k * rho1 b k ⟨8, by omega⟩ = 0 := by
    intro k hk
    rw [pi1_vanish_nuR a  k hk, zero_mul]
  have hvanR : ∀ k : I32, k ∉ ({⟨8, by omega⟩} : Finset I32) →
      rho1 b ⟨8, by omega⟩ k * pi1 a k ⟨8, by omega⟩ = 0 := by
    intro k hk
    rw [rho1_entry, partner_mk8,
      pi1_vanish_col_nuRc b  (partner k) (partner_not_mem_nuR hk),
      zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_singleton,
    pi1_entry_nuR,
    rho1_entry_nuR]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvanR,
    Finset.sum_singleton,
    rho1_entry_nuR,
    pi1_entry_nuR]
  try (ring)

/-- **Order-zero, eR block**: the two products agree entrywise
on the block (both sums collapse to the block finset; the summands
agree by the summand-pure conjugate entries). -/
theorem pi1_rho1_comm_eR (a b : AF) :
    (pi1 a * rho1 b) ⟨9, by omega⟩ ⟨9, by omega⟩ = (rho1 b * pi1 a) ⟨9, by omega⟩ ⟨9, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨9, by omega⟩} : Finset I32) →
      pi1 a ⟨9, by omega⟩ k * rho1 b k ⟨9, by omega⟩ = 0 := by
    intro k hk
    rw [pi1_vanish_eR a  k hk, zero_mul]
  have hvanR : ∀ k : I32, k ∉ ({⟨9, by omega⟩} : Finset I32) →
      rho1 b ⟨9, by omega⟩ k * pi1 a k ⟨9, by omega⟩ = 0 := by
    intro k hk
    rw [rho1_entry, partner_mk9,
      pi1_vanish_col_eRc b  (partner k) (partner_not_mem_eR hk),
      zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_singleton,
    pi1_entry_eR,
    rho1_entry_eR]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvanR,
    Finset.sum_singleton,
    rho1_entry_eR,
    pi1_entry_eR]
  try (ring)

/-- **Order-zero, quarkR block**: the two products agree entrywise
on the block (both sums collapse to the block finset; the summands
agree by the summand-pure conjugate entries). -/
theorem pi1_rho1_comm_quarkR (a b : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    (pi1 a * rho1 b) ⟨10 + 2 * ki.val + si.val, by omega⟩ ⟨10 + 2 * kj.val + sj.val, by omega⟩ = (rho1 b * pi1 a) ⟨10 + 2 * ki.val + si.val, by omega⟩ ⟨10 + 2 * kj.val + sj.val, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) →
      pi1 a ⟨10 + 2 * ki.val + si.val, by omega⟩ k * rho1 b k ⟨10 + 2 * kj.val + sj.val, by omega⟩ = 0 := by
    intro k hk
    rw [pi1_vanish_quarkR a ki si k hk, zero_mul]
  have hvanR : ∀ k : I32, k ∉ ({⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) →
      rho1 b ⟨10 + 2 * ki.val + si.val, by omega⟩ k * pi1 a k ⟨10 + 2 * kj.val + sj.val, by omega⟩ = 0 := by
    intro k hk
    rw [rho1_entry, partner_mk_quarkR ki si,
      pi1_vanish_col_quarkRc b ki si (partner k) (partner_not_mem_quarkR hk),
      zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    pi1_entry_quarkR a ki ⟨0, by omega⟩ si ⟨0, by omega⟩,
    rho1_entry_quarkR b ⟨0, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkR a ki ⟨0, by omega⟩ si ⟨1, by omega⟩,
    rho1_entry_quarkR b ⟨0, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi1_entry_quarkR a ki ⟨1, by omega⟩ si ⟨0, by omega⟩,
    rho1_entry_quarkR b ⟨1, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkR a ki ⟨1, by omega⟩ si ⟨1, by omega⟩,
    rho1_entry_quarkR b ⟨1, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi1_entry_quarkR a ki ⟨2, by omega⟩ si ⟨0, by omega⟩,
    rho1_entry_quarkR b ⟨2, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkR a ki ⟨2, by omega⟩ si ⟨1, by omega⟩,
    rho1_entry_quarkR b ⟨2, by omega⟩ kj ⟨1, by omega⟩ sj]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvanR,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    rho1_entry_quarkR b ki ⟨0, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkR a ⟨0, by omega⟩ kj ⟨0, by omega⟩ sj,
    rho1_entry_quarkR b ki ⟨0, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkR a ⟨0, by omega⟩ kj ⟨1, by omega⟩ sj,
    rho1_entry_quarkR b ki ⟨1, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkR a ⟨1, by omega⟩ kj ⟨0, by omega⟩ sj,
    rho1_entry_quarkR b ki ⟨1, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkR a ⟨1, by omega⟩ kj ⟨1, by omega⟩ sj,
    rho1_entry_quarkR b ki ⟨2, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkR a ⟨2, by omega⟩ kj ⟨0, by omega⟩ sj,
    rho1_entry_quarkR b ki ⟨2, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkR a ⟨2, by omega⟩ kj ⟨1, by omega⟩ sj]
  try (fin_cases ki <;> fin_cases kj <;> fin_cases si <;> fin_cases sj <;> simp <;> ring)

/-- **Order-zero, leptonLc block**: the two products agree entrywise
on the block (both sums collapse to the block finset; the summands
agree by the summand-pure conjugate entries). -/
theorem pi1_rho1_comm_leptonLc (a b : AF) (s t : Fin 2) :
    (pi1 a * rho1 b) ⟨16 + s.val, by omega⟩ ⟨16 + t.val, by omega⟩ = (rho1 b * pi1 a) ⟨16 + s.val, by omega⟩ ⟨16 + t.val, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨16 + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨16 + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) →
      pi1 a ⟨16 + s.val, by omega⟩ k * rho1 b k ⟨16 + t.val, by omega⟩ = 0 := by
    intro k hk
    rw [pi1_vanish_leptonLc a s k hk, zero_mul]
  have hvanR : ∀ k : I32, k ∉ ({⟨16 + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨16 + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) →
      rho1 b ⟨16 + s.val, by omega⟩ k * pi1 a k ⟨16 + t.val, by omega⟩ = 0 := by
    intro k hk
    rw [rho1_entry, partner_mk_sub16 s.val (by omega),
      pi1_vanish_col_leptonL b s (partner k) (partner_not_mem_leptonLc hk),
      zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_pair (by decide : (⟨16 + (⟨0, by omega⟩ : Fin 2).val, by omega⟩ : I32) ≠ ⟨16 + (⟨1, by omega⟩ : Fin 2).val, by omega⟩),
    pi1_entry_leptonLc a s ⟨0, by omega⟩,
    rho1_entry_leptonLc b ⟨0, by omega⟩ t,
    pi1_entry_leptonLc a s ⟨1, by omega⟩,
    rho1_entry_leptonLc b ⟨1, by omega⟩ t]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvanR,
    Finset.sum_pair (by decide : (⟨16 + (⟨0, by omega⟩ : Fin 2).val, by omega⟩ : I32) ≠ ⟨16 + (⟨1, by omega⟩ : Fin 2).val, by omega⟩),
    rho1_entry_leptonLc b s ⟨0, by omega⟩,
    pi1_entry_leptonLc a ⟨0, by omega⟩ t,
    rho1_entry_leptonLc b s ⟨1, by omega⟩,
    pi1_entry_leptonLc a ⟨1, by omega⟩ t]
  try (fin_cases s <;> fin_cases t <;> simp <;> ring)

/-- **Order-zero, quarkLc block**: the two products agree entrywise
on the block (both sums collapse to the block finset; the summands
agree by the summand-pure conjugate entries). -/
theorem pi1_rho1_comm_quarkLc (a b : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    (pi1 a * rho1 b) ⟨18 + 2 * ki.val + si.val, by omega⟩ ⟨18 + 2 * kj.val + sj.val, by omega⟩ = (rho1 b * pi1 a) ⟨18 + 2 * ki.val + si.val, by omega⟩ ⟨18 + 2 * kj.val + sj.val, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) →
      pi1 a ⟨18 + 2 * ki.val + si.val, by omega⟩ k * rho1 b k ⟨18 + 2 * kj.val + sj.val, by omega⟩ = 0 := by
    intro k hk
    rw [pi1_vanish_quarkLc a ki si k hk, zero_mul]
  have hvanR : ∀ k : I32, k ∉ ({⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩, ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) →
      rho1 b ⟨18 + 2 * ki.val + si.val, by omega⟩ k * pi1 a k ⟨18 + 2 * kj.val + sj.val, by omega⟩ = 0 := by
    intro k hk
    rw [rho1_entry, partner_mk_quarkLc ki si,
      pi1_vanish_col_quarkL b ki si (partner k) (partner_not_mem_quarkLc hk),
      zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    pi1_entry_quarkLc a ki ⟨0, by omega⟩ si ⟨0, by omega⟩,
    rho1_entry_quarkLc b ⟨0, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkLc a ki ⟨0, by omega⟩ si ⟨1, by omega⟩,
    rho1_entry_quarkLc b ⟨0, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi1_entry_quarkLc a ki ⟨1, by omega⟩ si ⟨0, by omega⟩,
    rho1_entry_quarkLc b ⟨1, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkLc a ki ⟨1, by omega⟩ si ⟨1, by omega⟩,
    rho1_entry_quarkLc b ⟨1, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi1_entry_quarkLc a ki ⟨2, by omega⟩ si ⟨0, by omega⟩,
    rho1_entry_quarkLc b ⟨2, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkLc a ki ⟨2, by omega⟩ si ⟨1, by omega⟩,
    rho1_entry_quarkLc b ⟨2, by omega⟩ kj ⟨1, by omega⟩ sj]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvanR,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    rho1_entry_quarkLc b ki ⟨0, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkLc a ⟨0, by omega⟩ kj ⟨0, by omega⟩ sj,
    rho1_entry_quarkLc b ki ⟨0, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkLc a ⟨0, by omega⟩ kj ⟨1, by omega⟩ sj,
    rho1_entry_quarkLc b ki ⟨1, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkLc a ⟨1, by omega⟩ kj ⟨0, by omega⟩ sj,
    rho1_entry_quarkLc b ki ⟨1, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkLc a ⟨1, by omega⟩ kj ⟨1, by omega⟩ sj,
    rho1_entry_quarkLc b ki ⟨2, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkLc a ⟨2, by omega⟩ kj ⟨0, by omega⟩ sj,
    rho1_entry_quarkLc b ki ⟨2, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkLc a ⟨2, by omega⟩ kj ⟨1, by omega⟩ sj]
  try (fin_cases ki <;> fin_cases kj <;> fin_cases si <;> fin_cases sj <;> simp <;> ring)

/-- **Order-zero, nuRc block**: the two products agree entrywise
on the block (both sums collapse to the block finset; the summands
agree by the summand-pure conjugate entries). -/
theorem pi1_rho1_comm_nuRc (a b : AF) :
    (pi1 a * rho1 b) ⟨24, by omega⟩ ⟨24, by omega⟩ = (rho1 b * pi1 a) ⟨24, by omega⟩ ⟨24, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨24, by omega⟩} : Finset I32) →
      pi1 a ⟨24, by omega⟩ k * rho1 b k ⟨24, by omega⟩ = 0 := by
    intro k hk
    rw [pi1_vanish_nuRc a  k hk, zero_mul]
  have hvanR : ∀ k : I32, k ∉ ({⟨24, by omega⟩} : Finset I32) →
      rho1 b ⟨24, by omega⟩ k * pi1 a k ⟨24, by omega⟩ = 0 := by
    intro k hk
    rw [rho1_entry, partner_mk24,
      pi1_vanish_col_nuR b  (partner k) (partner_not_mem_nuRc hk),
      zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_singleton,
    pi1_entry_nuRc,
    rho1_entry_nuRc]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvanR,
    Finset.sum_singleton,
    rho1_entry_nuRc,
    pi1_entry_nuRc]
  try (ring)

/-- **Order-zero, eRc block**: the two products agree entrywise
on the block (both sums collapse to the block finset; the summands
agree by the summand-pure conjugate entries). -/
theorem pi1_rho1_comm_eRc (a b : AF) :
    (pi1 a * rho1 b) ⟨25, by omega⟩ ⟨25, by omega⟩ = (rho1 b * pi1 a) ⟨25, by omega⟩ ⟨25, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨25, by omega⟩} : Finset I32) →
      pi1 a ⟨25, by omega⟩ k * rho1 b k ⟨25, by omega⟩ = 0 := by
    intro k hk
    rw [pi1_vanish_eRc a  k hk, zero_mul]
  have hvanR : ∀ k : I32, k ∉ ({⟨25, by omega⟩} : Finset I32) →
      rho1 b ⟨25, by omega⟩ k * pi1 a k ⟨25, by omega⟩ = 0 := by
    intro k hk
    rw [rho1_entry, partner_mk25,
      pi1_vanish_col_eR b  (partner k) (partner_not_mem_eRc hk),
      zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_singleton,
    pi1_entry_eRc,
    rho1_entry_eRc]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvanR,
    Finset.sum_singleton,
    rho1_entry_eRc,
    pi1_entry_eRc]
  try (ring)

/-- **Order-zero, quarkRc block**: the two products agree entrywise
on the block (both sums collapse to the block finset; the summands
agree by the summand-pure conjugate entries). -/
theorem pi1_rho1_comm_quarkRc (a b : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    (pi1 a * rho1 b) ⟨26 + 2 * ki.val + si.val, by omega⟩ ⟨26 + 2 * kj.val + sj.val, by omega⟩ = (rho1 b * pi1 a) ⟨26 + 2 * ki.val + si.val, by omega⟩ ⟨26 + 2 * kj.val + sj.val, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩} : Finset I32) →
      pi1 a ⟨26 + 2 * ki.val + si.val, by omega⟩ k * rho1 b k ⟨26 + 2 * kj.val + sj.val, by omega⟩ = 0 := by
    intro k hk
    rw [pi1_vanish_quarkRc a ki si k hk, zero_mul]
  have hvanR : ∀ k : I32, k ∉ ({⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩, ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩} : Finset I32) →
      rho1 b ⟨26 + 2 * ki.val + si.val, by omega⟩ k * pi1 a k ⟨26 + 2 * kj.val + sj.val, by omega⟩ = 0 := by
    intro k hk
    rw [rho1_entry, partner_mk_quarkRc ki si,
      pi1_vanish_col_quarkR b ki si (partner k) (partner_not_mem_quarkRc hk),
      zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    pi1_entry_quarkRc a ki ⟨0, by omega⟩ si ⟨0, by omega⟩,
    rho1_entry_quarkRc b ⟨0, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkRc a ki ⟨0, by omega⟩ si ⟨1, by omega⟩,
    rho1_entry_quarkRc b ⟨0, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi1_entry_quarkRc a ki ⟨1, by omega⟩ si ⟨0, by omega⟩,
    rho1_entry_quarkRc b ⟨1, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkRc a ki ⟨1, by omega⟩ si ⟨1, by omega⟩,
    rho1_entry_quarkRc b ⟨1, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi1_entry_quarkRc a ki ⟨2, by omega⟩ si ⟨0, by omega⟩,
    rho1_entry_quarkRc b ⟨2, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi1_entry_quarkRc a ki ⟨2, by omega⟩ si ⟨1, by omega⟩,
    rho1_entry_quarkRc b ⟨2, by omega⟩ kj ⟨1, by omega⟩ sj]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvanR,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    rho1_entry_quarkRc b ki ⟨0, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkRc a ⟨0, by omega⟩ kj ⟨0, by omega⟩ sj,
    rho1_entry_quarkRc b ki ⟨0, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkRc a ⟨0, by omega⟩ kj ⟨1, by omega⟩ sj,
    rho1_entry_quarkRc b ki ⟨1, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkRc a ⟨1, by omega⟩ kj ⟨0, by omega⟩ sj,
    rho1_entry_quarkRc b ki ⟨1, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkRc a ⟨1, by omega⟩ kj ⟨1, by omega⟩ sj,
    rho1_entry_quarkRc b ki ⟨2, by omega⟩ si ⟨0, by omega⟩,
    pi1_entry_quarkRc a ⟨2, by omega⟩ kj ⟨0, by omega⟩ sj,
    rho1_entry_quarkRc b ki ⟨2, by omega⟩ si ⟨1, by omega⟩,
    pi1_entry_quarkRc a ⟨2, by omega⟩ kj ⟨1, by omega⟩ sj]
  try (fin_cases ki <;> fin_cases kj <;> fin_cases si <;> fin_cases sj <;> simp <;> ring)

/-! ### Cross-block vanishing for the pair -/

/-- Entry form of the vanishing criterion for `pi1 a * rho1 b`. -/
theorem pi1_rho1_mul_entry_eq_zero (a b : AF) {i j : I32}
    (ha : ∀ k : I32, pi1 a i k = 0 ∨ rho1 b k j = 0) :
    (pi1 a * rho1 b) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rcases ha k with h | h
  · rw [h, zero_mul]
  · rw [h, mul_zero]

/-- `(pi1 a * rho1 b) i j = 0` off the block partition. -/
theorem pi1_rho1_mul_eq_zero_of_not_sameBlock (a b : AF) {i j : I32}
    (hij : ¬ sameBlock i j) : (pi1 a * rho1 b) i j = 0 := by
  apply pi1_rho1_mul_entry_eq_zero
  intro k
  by_cases hik : sameBlock i k
  · right
    rw [rho1_entry]
    apply pi1_entry_eq_zero_of_not_sameBlock
    intro hcon
    exact hij (sameBlock_trans hik (sameBlock_symm (sameBlock_partner.mp hcon)))
  · left
    exact pi1_entry_eq_zero_of_not_sameBlock a hik

/-- Entry form of the vanishing criterion for `rho1 b * pi1 a`. -/
theorem rho1_pi1_mul_entry_eq_zero (a b : AF) {i j : I32}
    (ha : ∀ k : I32, rho1 b i k = 0 ∨ pi1 a k j = 0) :
    (rho1 b * pi1 a) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rcases ha k with h | h
  · rw [h, zero_mul]
  · rw [h, mul_zero]

/-- `(rho1 b * pi1 a) i j = 0` off the block partition. -/
theorem rho1_pi1_mul_eq_zero_of_not_sameBlock (a b : AF) {i j : I32}
    (hij : ¬ sameBlock i j) : (rho1 b * pi1 a) i j = 0 := by
  apply rho1_pi1_mul_entry_eq_zero
  intro k
  by_cases hkj : sameBlock k j
  · left
    rw [rho1_entry]
    apply pi1_entry_eq_zero_of_not_sameBlock
    intro hcon
    exact hij (sameBlock_trans (sameBlock_symm (sameBlock_partner.mp hcon)) hkj)
  · right
    exact pi1_entry_eq_zero_of_not_sameBlock a hkj

/-! ### T4 assembly: order-zero for the pair (π₁, ρ₁°)

The §3 case tree with the two products in place of the factored
forms: off the block partition both products vanish; on each block
the §7b computations close. -/

theorem pi1_order_zero (a b : AF) :
    pi1 a * rho1 b = rho1 b * pi1 a := by
  ext i j
  by_cases hsec : i.val / 8 = j.val / 8
  · by_cases hi : i.val < 8
    · have hj : j.val < 8 := by omega
      by_cases hi2 : i.val < 2
      · by_cases hj2 : j.val < 2
        · have hsi : (⟨(⟨i.val, hi2⟩ : Fin 2).val, by omega⟩ : I32) = i :=
            Fin.ext (show (⟨i.val, hi2⟩ : Fin 2).val = i.val from rfl)
          have hsj : (⟨(⟨j.val, hj2⟩ : Fin 2).val, by omega⟩ : I32) = j :=
            Fin.ext (show (⟨j.val, hj2⟩ : Fin 2).val = j.val from rfl)
          rw [← hsi, ← hsj]
          exact pi1_rho1_comm_leptonL a b ⟨i.val, hi2⟩ ⟨j.val, hj2⟩
        · have hns : ¬ sameBlock i j := not_sameBlock_of_HL_mixed (Or.inl ⟨hi2, by omega, hj⟩)
          rw [pi1_rho1_mul_eq_zero_of_not_sameBlock a b hns,
            rho1_pi1_mul_eq_zero_of_not_sameBlock a b hns]
      · by_cases hj2 : j.val < 2
        · have hns : ¬ sameBlock i j := not_sameBlock_of_HL_mixed (Or.inr ⟨by omega, hi, hj2⟩)
          rw [pi1_rho1_mul_eq_zero_of_not_sameBlock a b hns,
            rho1_pi1_mul_eq_zero_of_not_sameBlock a b hns]
        · have hci : (⟨2 + 2 * (⟨(i.val - 2) / 2, by omega⟩ : Fin 3).val
              + (⟨(i.val - 2) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
            apply Fin.ext
            show 2 + 2 * ((i.val - 2) / 2) + (i.val - 2) % 2 = i.val
            have h := Nat.div_add_mod (i.val - 2) 2
            omega
          have hcj : (⟨2 + 2 * (⟨(j.val - 2) / 2, by omega⟩ : Fin 3).val
              + (⟨(j.val - 2) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
            apply Fin.ext
            show 2 + 2 * ((j.val - 2) / 2) + (j.val - 2) % 2 = j.val
            have h := Nat.div_add_mod (j.val - 2) 2
            omega
          rw [← hci, ← hcj]
          exact pi1_rho1_comm_quarkL a b ⟨(i.val - 2) / 2, by omega⟩
            ⟨(j.val - 2) / 2, by omega⟩ ⟨(i.val - 2) % 2, by omega⟩
            ⟨(j.val - 2) % 2, by omega⟩
    · by_cases hi16 : i.val < 16
      · have hj8 : 8 ≤ j.val := by omega
        have hj16 : j.val < 16 := by omega
        by_cases hi8 : i.val = 8
        · by_cases hj8' : j.val = 8
          · have hsi : (⟨8, by omega⟩ : I32) = i := Fin.ext hi8.symm
            have hsj : (⟨8, by omega⟩ : I32) = j := Fin.ext hj8'.symm
            rw [← hsi, ← hsj]
            exact pi1_rho1_comm_nuR a b
          · by_cases hj9 : j.val = 9
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed (Or.inl ⟨hi8, hj9⟩)
              rw [pi1_rho1_mul_eq_zero_of_not_sameBlock a b hns,
                rho1_pi1_mul_eq_zero_of_not_sameBlock a b hns]
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                (Or.inr (Or.inr (Or.inl ⟨Or.inl hi8, by omega, hj16⟩)))
              rw [pi1_rho1_mul_eq_zero_of_not_sameBlock a b hns,
                rho1_pi1_mul_eq_zero_of_not_sameBlock a b hns]
        · by_cases hi9 : i.val = 9
          · by_cases hj8' : j.val = 8
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed (Or.inr (Or.inl ⟨hi9, hj8'⟩))
              rw [pi1_rho1_mul_eq_zero_of_not_sameBlock a b hns,
                rho1_pi1_mul_eq_zero_of_not_sameBlock a b hns]
            · by_cases hj9 : j.val = 9
              · have hsi : (⟨9, by omega⟩ : I32) = i := Fin.ext hi9.symm
                have hsj : (⟨9, by omega⟩ : I32) = j := Fin.ext hj9.symm
                rw [← hsi, ← hsj]
                exact pi1_rho1_comm_eR a b
              · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                  (Or.inr (Or.inr (Or.inl ⟨Or.inr hi9, by omega, hj16⟩)))
                rw [pi1_rho1_mul_eq_zero_of_not_sameBlock a b hns,
                  rho1_pi1_mul_eq_zero_of_not_sameBlock a b hns]
          · by_cases hj8' : j.val = 8
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inl hj8'⟩)))
              rw [pi1_rho1_mul_eq_zero_of_not_sameBlock a b hns,
                rho1_pi1_mul_eq_zero_of_not_sameBlock a b hns]
            · by_cases hj9 : j.val = 9
              · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                  (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inr hj9⟩)))
                rw [pi1_rho1_mul_eq_zero_of_not_sameBlock a b hns,
                  rho1_pi1_mul_eq_zero_of_not_sameBlock a b hns]
              · have hci : (⟨10 + 2 * (⟨(i.val - 10) / 2, by omega⟩ : Fin 3).val
                    + (⟨(i.val - 10) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
                  apply Fin.ext
                  show 10 + 2 * ((i.val - 10) / 2) + (i.val - 10) % 2 = i.val
                  have h := Nat.div_add_mod (i.val - 10) 2
                  omega
                have hcj : (⟨10 + 2 * (⟨(j.val - 10) / 2, by omega⟩ : Fin 3).val
                    + (⟨(j.val - 10) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
                  apply Fin.ext
                  show 10 + 2 * ((j.val - 10) / 2) + (j.val - 10) % 2 = j.val
                  have h := Nat.div_add_mod (j.val - 10) 2
                  omega
                rw [← hci, ← hcj]
                exact pi1_rho1_comm_quarkR a b ⟨(i.val - 10) / 2, by omega⟩
                  ⟨(j.val - 10) / 2, by omega⟩ ⟨(i.val - 10) % 2, by omega⟩
                  ⟨(j.val - 10) % 2, by omega⟩
      · by_cases hi24 : i.val < 24
        · have hj16 : 16 ≤ j.val := by omega
          have hj24 : j.val < 24 := by omega
          by_cases hi18 : i.val < 18
          · by_cases hj18 : j.val < 18
            · have hsi : (⟨16 + (⟨i.val - 16, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i :=
                Fin.ext (by show 16 + (i.val - 16) = i.val; omega)
              have hsj : (⟨16 + (⟨j.val - 16, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j :=
                Fin.ext (by show 16 + (j.val - 16) = j.val; omega)
              rw [← hsi, ← hsj]
              exact pi1_rho1_comm_leptonLc a b ⟨i.val - 16, by omega⟩
                ⟨j.val - 16, by omega⟩
            · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                (Or.inl ⟨by omega, hi18, by omega, hj24⟩)
              rw [pi1_rho1_mul_eq_zero_of_not_sameBlock a b hns,
                rho1_pi1_mul_eq_zero_of_not_sameBlock a b hns]
          · by_cases hj18 : j.val < 18
            · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                (Or.inr (Or.inl ⟨by omega, hi24, hj16, hj18⟩))
              rw [pi1_rho1_mul_eq_zero_of_not_sameBlock a b hns,
                rho1_pi1_mul_eq_zero_of_not_sameBlock a b hns]
            · have hci : (⟨18 + 2 * (⟨(i.val - 18) / 2, by omega⟩ : Fin 3).val
                  + (⟨(i.val - 18) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
                apply Fin.ext
                show 18 + 2 * ((i.val - 18) / 2) + (i.val - 18) % 2 = i.val
                have h := Nat.div_add_mod (i.val - 18) 2
                omega
              have hcj : (⟨18 + 2 * (⟨(j.val - 18) / 2, by omega⟩ : Fin 3).val
                  + (⟨(j.val - 18) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
                apply Fin.ext
                show 18 + 2 * ((j.val - 18) / 2) + (j.val - 18) % 2 = j.val
                have h := Nat.div_add_mod (j.val - 18) 2
                omega
              rw [← hci, ← hcj]
              exact pi1_rho1_comm_quarkLc a b ⟨(i.val - 18) / 2, by omega⟩
                ⟨(j.val - 18) / 2, by omega⟩ ⟨(i.val - 18) % 2, by omega⟩
                ⟨(j.val - 18) % 2, by omega⟩
        · have hj24 : 24 ≤ j.val := by omega
          by_cases hi24' : i.val = 24
          · by_cases hj24' : j.val = 24
            · have hsi : (⟨24, by omega⟩ : I32) = i := Fin.ext hi24'.symm
              have hsj : (⟨24, by omega⟩ : I32) = j := Fin.ext hj24'.symm
              rw [← hsi, ← hsj]
              exact pi1_rho1_comm_nuRc a b
            · by_cases hj25 : j.val = 25
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inl ⟨hi24', hj25⟩)))))))
                rw [pi1_rho1_mul_eq_zero_of_not_sameBlock a b hns,
                  rho1_pi1_mul_eq_zero_of_not_sameBlock a b hns]
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                  (Or.inr (Or.inr (Or.inl ⟨hi24', by omega⟩)))
                rw [pi1_rho1_mul_eq_zero_of_not_sameBlock a b hns,
                  rho1_pi1_mul_eq_zero_of_not_sameBlock a b hns]
          · by_cases hi25 : i.val = 25
            · by_cases hj24' : j.val = 24
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr ⟨hi25, hj24'⟩)))))))
                rw [pi1_rho1_mul_eq_zero_of_not_sameBlock a b hns,
                  rho1_pi1_mul_eq_zero_of_not_sameBlock a b hns]
              · by_cases hj25 : j.val = 25
                · have hsi : (⟨25, by omega⟩ : I32) = i := Fin.ext hi25.symm
                  have hsj : (⟨25, by omega⟩ : I32) = j := Fin.ext hj25.symm
                  rw [← hsi, ← hsj]
                  exact pi1_rho1_comm_eRc a b
                · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                    (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi25, by omega⟩))))
                  rw [pi1_rho1_mul_eq_zero_of_not_sameBlock a b hns,
                    rho1_pi1_mul_eq_zero_of_not_sameBlock a b hns]
            · by_cases hj24' : j.val = 24
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inl ⟨by omega, hj24'⟩)))))
                rw [pi1_rho1_mul_eq_zero_of_not_sameBlock a b hns,
                  rho1_pi1_mul_eq_zero_of_not_sameBlock a b hns]
              · by_cases hj25 : j.val = 25
                · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inl ⟨by omega, hj25⟩))))))
                  rw [pi1_rho1_mul_eq_zero_of_not_sameBlock a b hns,
                    rho1_pi1_mul_eq_zero_of_not_sameBlock a b hns]
                · have hci : (⟨26 + 2 * (⟨(i.val - 26) / 2, by omega⟩ : Fin 3).val
                      + (⟨(i.val - 26) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = i := by
                    apply Fin.ext
                    show 26 + 2 * ((i.val - 26) / 2) + (i.val - 26) % 2 = i.val
                    have h := Nat.div_add_mod (i.val - 26) 2
                    omega
                  have hcj : (⟨26 + 2 * (⟨(j.val - 26) / 2, by omega⟩ : Fin 3).val
                      + (⟨(j.val - 26) % 2, by omega⟩ : Fin 2).val, by omega⟩ : I32) = j := by
                    apply Fin.ext
                    show 26 + 2 * ((j.val - 26) / 2) + (j.val - 26) % 2 = j.val
                    have h := Nat.div_add_mod (j.val - 26) 2
                    omega
                  rw [← hci, ← hcj]
                  exact pi1_rho1_comm_quarkRc a b ⟨(i.val - 26) / 2, by omega⟩
                    ⟨(j.val - 26) / 2, by omega⟩ ⟨(i.val - 26) % 2, by omega⟩
                    ⟨(j.val - 26) % 2, by omega⟩
  · have hns : ¬ sameBlock i j := not_sameBlock_of_ne_sector hsec
    rw [pi1_rho1_mul_eq_zero_of_not_sameBlock a b hns,
      rho1_pi1_mul_eq_zero_of_not_sameBlock a b hns]

/-! ## §8. T5 — first-order for (π₁, ρ₁°) against `DF_oneGen`

The matched-slot map `md` (the Dirac operator's only coupling
pattern), the entry form of the landed `DF_oneGen`, and the closed
form of the first commutator `C a = [DF, π₁ a]`. -/

/-- The matched slot: `DF_oneGen` couples `i` only to `md i`. -/
def md (i : I32) : I32 :=
  if h : i.val < 8 then ⟨i.val + 8, by omega⟩
  else if h2 : 16 ≤ i.val ∧ i.val < 24 then ⟨i.val + 8, by omega⟩
  else ⟨i.val - 8, by omega⟩

/-- Value of the matched slot. -/
theorem md_val (i : I32) : (md i).val
    = if i.val < 8 then i.val + 8
      else if 16 ≤ i.val ∧ i.val < 24 then i.val + 8 else i.val - 8 := by
  unfold md
  split_ifs <;> rfl

/-- Matched slot value, L sector. -/
theorem md_val_L (i : I32) (hi : i.val < 8) : (md i).val = i.val + 8 := by
  rw [md_val, if_pos hi]

/-- Matched slot value, R sector. -/
theorem md_val_R (i : I32) (hi : 8 ≤ i.val ∧ i.val < 16) :
    (md i).val = i.val - 8 := by
  rw [md_val, if_neg (by omega), if_neg (by omega)]

/-- Matched slot value, Lc sector. -/
theorem md_val_Lc (i : I32) (hi : 16 ≤ i.val ∧ i.val < 24) :
    (md i).val = i.val + 8 := by
  rw [md_val, if_neg (by omega), if_pos hi]

/-- Matched slot value, Rc sector. -/
theorem md_val_Rc (i : I32) (hi : 24 ≤ i.val) : (md i).val = i.val - 8 := by
  rw [md_val, if_neg (by omega), if_neg (by omega)]

/-- The matched slot is an involution. -/
theorem md_involutive (i : I32) : md (md i) = i := by
  apply Fin.ext
  rw [md_val, md_val]
  split_ifs <;> omega

/-- The matched slot preserves the particle half. -/
theorem md_particle (i : I32) (hi : i.val < 16) : (md i).val < 16 := by
  rw [md_val]
  split_ifs <;> omega

/-- The matched slot preserves the antiparticle half. -/
theorem md_anti (i : I32) (hi : 16 ≤ i.val) : 16 ≤ (md i).val := by
  rw [md_val]
  split_ifs <;> omega

/-- The Yukawa pattern on `Fin 8` (all entries real). -/
def Y8 (Ynu Ye Yu Yd : ℝ) (s : Fin 8) : ℂ :=
  ![(Ynu : ℂ), (Ye : ℂ), (Yu : ℂ), (Yd : ℂ),
    (Yu : ℂ), (Yd : ℂ), (Yu : ℂ), (Yd : ℂ)] s

/-- The diagonal value of `DF_oneGen` at a slot. -/
def Dval (Ynu Ye Yu Yd : ℝ) (i : I32) : ℂ :=
  Y8 Ynu Ye Yu Yd ⟨i.val % 8, by omega⟩

/-- `Dval` unfolded. -/
theorem Dval_eq (Ynu Ye Yu Yd : ℝ) (i : I32) :
    Dval Ynu Ye Yu Yd i = Y8 Ynu Ye Yu Yd ⟨i.val % 8, by omega⟩ := rfl

/-- The Yukawa weights are real: entrywise conjugation fixes them. -/
theorem Y8_star (Ynu Ye Yu Yd : ℝ) (s : Fin 8) :
    (starRingEnd ℂ) (Y8 Ynu Ye Yu Yd s) = Y8 Ynu Ye Yu Yd s := by
  fin_cases s <;> simp [Y8]

/-- `Dval` at an explicit slot value, via its mod-8 index. -/
theorem Dval_apply (Ynu Ye Yu Yd : ℝ) (v w : ℕ) (hv : v < 32)
    (hw : v % 8 = w) :
    Dval Ynu Ye Yu Yd ⟨v, hv⟩ = Y8 Ynu Ye Yu Yd ⟨w, by omega⟩ := by
  unfold Dval
  congr 1
  exact Fin.ext hw

/-- The quark Yukawa weights are color-independent. -/
theorem Y8_quark (Ynu Ye Yu Yd : ℝ) (k : Fin 3) (s : Fin 2) :
    Y8 Ynu Ye Yu Yd ⟨2 + 2 * k.val + s.val, by omega⟩
      = Y8 Ynu Ye Yu Yd ⟨2 + s.val, by omega⟩ := by
  fin_cases k <;> fin_cases s <;> rfl

/-! ### The entry form of `DF_oneGen` -/

/-- **Entry form of the landed Dirac operator**: `DF_oneGen` couples
slot `i` only to its matched slot `md i`, with the real Yukawa
weight `Dval`. (From the landed `buildDirac` arms: `A` diagonal,
`B = Ā`, `C = E = 0`; the diagonal entries of `A`, `Aᴴ`, `B`, `Bᴴ`
all agree since the weights are real.) -/
theorem DF_oneGen_entry (Ynu Ye Yu Yd : ℝ) (i j : I32) :
    DF_oneGen Ynu Ye Yu Yd i j
      = if j = md i then Dval Ynu Ye Yu Yd i else 0 := by
  by_cases h : j = md i
  · rw [if_pos h]
    subst h
    by_cases h1 : i.val < 8
    · have hmd : (md i).val = i.val + 8 := md_val_L i h1
      have ht1 : ¬ (i.val + 8 < 8) := by omega
      have ht2 : i.val + 8 < 16 := by omega
      unfold DF_oneGen buildDirac
      simp only []
      simp [h1, hmd, ht1, ht2, Matrix.diagonal, Dval, Y8,
        Nat.mod_eq_of_lt h1]
    · by_cases h2 : i.val < 16
      · have hmd : (md i).val = i.val - 8 := md_val_R i ⟨by omega, h2⟩
        have ht1 : i.val - 8 < 8 := by omega
        have hmod : i.val % 8 = i.val - 8 := by omega
        unfold DF_oneGen buildDirac
        simp only []
        simp [h1, h2, hmd, ht1, Matrix.diagonal, Matrix.conjTranspose_apply]
        rw [Dval_eq]
        have hidx : (⟨i.val % 8, by omega⟩ : Fin 8) = ⟨i.val - 8, by omega⟩ :=
          Fin.ext hmod
        rw [hidx]
        exact Y8_star Ynu Ye Yu Yd _
      · by_cases h3 : i.val < 24
        · have hmd : (md i).val = i.val + 8 := md_val_Lc i ⟨by omega, h3⟩
          have ht1 : ¬ (i.val + 8 < 16) := by omega
          have ht2 : ¬ (i.val + 8 < 24) := by omega
          have hmod : i.val % 8 = i.val - 16 := by omega
          unfold DF_oneGen buildDirac
          simp only []
          simp [h1, h2, h3, hmd, ht1, ht2, Matrix.map_apply,
            Matrix.diagonal]
          rw [Dval_eq]
          have hidx : (⟨i.val % 8, by omega⟩ : Fin 8)
              = ⟨i.val - 16, by omega⟩ := Fin.ext hmod
          rw [hidx]
          exact Y8_star Ynu Ye Yu Yd _
        · have hmd : (md i).val = i.val - 8 := md_val_Rc i (by omega)
          have ht0 : ¬ (i.val - 8 < 8) := by omega
          have ht1 : ¬ (i.val - 8 < 16) := by omega
          have ht2 : i.val - 8 < 24 := by omega
          have heq : i.val - 8 - 16 = i.val - 24 := by omega
          have hmod : i.val % 8 = i.val - 24 := by omega
          unfold DF_oneGen buildDirac
          simp only []
          simp [h1, h2, h3, hmd, ht0, ht1, ht2, heq, Matrix.map_apply,
            Matrix.diagonal, Matrix.conjTranspose_apply]
          rw [Dval_eq]
          have hidx : (⟨i.val % 8, by omega⟩ : Fin 8)
              = ⟨i.val - 24, by omega⟩ := Fin.ext hmod
          rw [hidx]
          first | rfl | exact Y8_star Ynu Ye Yu Yd _
  · rw [if_neg h]
    have hjv : j.val ≠ (md i).val := fun hh => h (Fin.ext hh)
    by_cases h1 : i.val < 8
    · have hmd : (md i).val = i.val + 8 := md_val_L i h1
      by_cases g1 : j.val < 8
      · unfold DF_oneGen buildDirac; simp only []
        simp [h1, g1]
      · by_cases g2 : j.val < 16
        · have hne : i.val ≠ j.val - 8 := by omega
          unfold DF_oneGen buildDirac; simp only []
          simp [h1, g1, g2, Matrix.diagonal, Fin.mk.injEq, hne]
        · by_cases g3 : j.val < 24
          · unfold DF_oneGen buildDirac; simp only []
            simp [h1, g1, g2, g3]
          · unfold DF_oneGen buildDirac; simp only []
            simp [h1, g1, g2, g3]
    · by_cases h2 : i.val < 16
      · have hmd : (md i).val = i.val - 8 := md_val_R i ⟨by omega, h2⟩
        by_cases g1 : j.val < 8
        · have hne : j.val ≠ i.val - 8 := by omega
          unfold DF_oneGen buildDirac; simp only []
          simp [h1, h2, g1, Matrix.diagonal, Matrix.conjTranspose_apply,
            Fin.mk.injEq, hne]
        · by_cases g2 : j.val < 16
          · unfold DF_oneGen buildDirac; simp only []
            simp [h1, h2, g1, g2]
          · by_cases g3 : j.val < 24
            · unfold DF_oneGen buildDirac; simp only []
              simp [h1, h2, g1, g2, g3]
            · unfold DF_oneGen buildDirac; simp only []
              simp [h1, h2, g1, g2, g3]
      · by_cases h3 : i.val < 24
        · have hmd : (md i).val = i.val + 8 := md_val_Lc i ⟨by omega, h3⟩
          by_cases g1 : j.val < 8
          · unfold DF_oneGen buildDirac; simp only []
            simp [h1, h2, h3, g1]
          · by_cases g2 : j.val < 16
            · unfold DF_oneGen buildDirac; simp only []
              simp [h1, h2, h3, g1, g2]
            · by_cases g3 : j.val < 24
              · unfold DF_oneGen buildDirac; simp only []
                simp [h1, h2, h3, g1, g2, g3]
              · have hne : i.val - 16 ≠ j.val - 24 := by omega
                unfold DF_oneGen buildDirac; simp only []
                simp [h1, h2, h3, g1, g2, g3, Matrix.map_apply,
                  Matrix.diagonal, Fin.mk.injEq, hne]
        · have hmd : (md i).val = i.val - 8 := md_val_Rc i (by omega)
          by_cases g1 : j.val < 8
          · unfold DF_oneGen buildDirac; simp only []
            simp [h1, h2, h3, g1]
          · by_cases g2 : j.val < 16
            · unfold DF_oneGen buildDirac; simp only []
              simp [h1, h2, h3, g1, g2]
            · by_cases g3 : j.val < 24
              · have hne : j.val - 16 ≠ i.val - 24 := by omega
                unfold DF_oneGen buildDirac; simp only []
                simp [h1, h2, h3, g1, g2, g3, Matrix.map_apply,
                  Matrix.diagonal, Matrix.conjTranspose_apply, Fin.mk.injEq,
                  hne]
              · unfold DF_oneGen buildDirac; simp only []
                simp [h1, h2, h3, g1, g2, g3]

/-! ### The first commutator in closed form -/

/-- **Closed form of the first commutator**
`C a = [DF_oneGen, π₁ a]`: only the two matched terms survive. -/
theorem comm_entry (Ynu Ye Yu Yd : ℝ) (a : AF) (i j : I32) :
    (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) i j
      = Dval Ynu Ye Yu Yd i * pi1 a (md i) j
        - pi1 a i (md j) * Dval Ynu Ye Yu Yd (md j) := by
  have h1 : (DF_oneGen Ynu Ye Yu Yd * pi1 a) i j
      = Dval Ynu Ye Yu Yd i * pi1 a (md i) j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (md i)]
    · rw [DF_oneGen_entry, if_pos rfl]
    · intro k _ hk
      rw [DF_oneGen_entry, if_neg hk, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ (md i)) hcon
  have h2 : (pi1 a * DF_oneGen Ynu Ye Yu Yd) i j
      = pi1 a i (md j) * Dval Ynu Ye Yu Yd (md j) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (md j)]
    · rw [DF_oneGen_entry, md_involutive, if_pos rfl]
    · intro k _ hk
      rw [DF_oneGen_entry, if_neg, mul_zero]
      intro hjk
      apply hk
      have hkj : md j = k := by
        rw [show md j = md (md k) from congrArg md hjk]
        exact md_involutive k
      exact hkj.symm
    · intro hcon
      exact absurd (Finset.mem_univ (md j)) hcon
  rw [Matrix.sub_apply, h1, h2]

/-- ρ₁ entries vanish off the block partition. -/
theorem rho1_entry_eq_zero_of_not_sameBlock (b : AF) {i j : I32}
    (h : ¬ sameBlock i j) : rho1 b i j = 0 := by
  rw [rho1_entry]
  apply pi1_entry_eq_zero_of_not_sameBlock
  intro hcon
  exact h (sameBlock_symm (sameBlock_partner.mp hcon))

/-- ρ₁ support lies in the block partition. -/
theorem rho1_support (b : AF) {i j : I32} (h : rho1 b i j ≠ 0) :
    sameBlock i j := by
  by_contra hcon
  exact h (rho1_entry_eq_zero_of_not_sameBlock b hcon)

/-- **The commutator vanishes on (particle, antiparticle) pairs**:
both matched factors cross the halves. -/
theorem comm_particle_anti (Ynu Ye Yu Yd : ℝ) (a : AF) {i j : I32}
    (hi : i.val < 16) (hj : 16 ≤ j.val) :
    (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) i j
      = 0 := by
  rw [comm_entry,
    pi1_entry_eq_zero_of_not_sameBlock a
      (not_sameBlock_of_ne_sector (i := md i) (j := j) (by
        have h1 : (md i).val < 16 := md_particle i hi
        omega)),
    pi1_entry_eq_zero_of_not_sameBlock a
      (not_sameBlock_of_ne_sector (i := i) (j := md j) (by
        have h2 : 16 ≤ (md j).val := md_anti j hj
        omega)),
    zero_mul, mul_zero, sub_zero]

/-- **The commutator vanishes on (antiparticle, particle) pairs**:
both matched factors cross the halves. -/
theorem comm_anti_particle (Ynu Ye Yu Yd : ℝ) (a : AF) {i j : I32}
    (hi : 16 ≤ i.val) (hj : j.val < 16) :
    (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) i j
      = 0 := by
  rw [comm_entry,
    pi1_entry_eq_zero_of_not_sameBlock a
      (not_sameBlock_of_ne_sector (i := md i) (j := j) (by
        have h1 : 16 ≤ (md i).val := md_anti i hi
        omega)),
    pi1_entry_eq_zero_of_not_sameBlock a
      (not_sameBlock_of_ne_sector (i := i) (j := md j) (by
        have h2 : (md j).val < 16 := md_particle j hj
        omega)),
    zero_mul, mul_zero, sub_zero]

/-- The particle live relation of the commutator: matched pairs
inside the particle half. -/
def mdBlock (i k : I32) : Prop :=
  (i.val < 2 ∧ (k.val = 8 ∨ k.val = 9)) ∨
  (i.val = 8 ∧ k.val < 2) ∨
  (i.val = 9 ∧ k.val < 2) ∨
  (2 ≤ i.val ∧ i.val < 8 ∧ 10 ≤ k.val ∧ k.val < 16) ∨
  (10 ≤ i.val ∧ i.val < 16 ∧ 2 ≤ k.val ∧ k.val < 8)

/-! ### §8b. Matched-slot forms, `Dval` forms, anti-anti rectangles,
the commutator support theorem. -/

/-- Matched slot of a left-lepton slot. -/
theorem md_lepL (s : Fin 2) :
    md ⟨s.val, by omega⟩ = ⟨s.val + 8, by omega⟩ := by
  apply Fin.ext
  show (md ⟨s.val, by omega⟩).val = s.val + 8
  rw [md_val_L _ (by show s.val < 8; omega)]

/-- Matched slot of a left-quark slot. -/
theorem md_quarkL (k : Fin 3) (s : Fin 2) :
    md ⟨2 + 2 * k.val + s.val, by omega⟩
      = ⟨10 + 2 * k.val + s.val, by omega⟩ := by
  apply Fin.ext
  show (md ⟨2 + 2 * k.val + s.val, by omega⟩).val
    = 10 + 2 * k.val + s.val
  rw [md_val_L _ (by show 2 + 2 * k.val + s.val < 8; omega)]
  show 2 + 2 * k.val + s.val + 8 = 10 + 2 * k.val + s.val
  omega

/-- Matched slot of a right-quark slot. -/
theorem md_quarkR (k : Fin 3) (s : Fin 2) :
    md ⟨10 + 2 * k.val + s.val, by omega⟩
      = ⟨2 + 2 * k.val + s.val, by omega⟩ := by
  apply Fin.ext
  show (md ⟨10 + 2 * k.val + s.val, by omega⟩).val
    = 2 + 2 * k.val + s.val
  rw [md_val_R _ (by show 8 ≤ 10 + 2 * k.val + s.val ∧
    10 + 2 * k.val + s.val < 16; omega)]
  show 10 + 2 * k.val + s.val - 8 = 2 + 2 * k.val + s.val
  omega

/-- Matched slot of a left-antilepton slot. -/
theorem md_lepLc (s : Fin 2) :
    md ⟨16 + s.val, by omega⟩ = ⟨24 + s.val, by omega⟩ := by
  apply Fin.ext
  show (md ⟨16 + s.val, by omega⟩).val = 24 + s.val
  rw [md_val_Lc _ (by show 16 ≤ 16 + s.val ∧ 16 + s.val < 24; omega)]
  show 16 + s.val + 8 = 24 + s.val
  omega

/-- Matched slot of a left-antiquark slot. -/
theorem md_quarkLc (k : Fin 3) (s : Fin 2) :
    md ⟨18 + 2 * k.val + s.val, by omega⟩
      = ⟨26 + 2 * k.val + s.val, by omega⟩ := by
  apply Fin.ext
  show (md ⟨18 + 2 * k.val + s.val, by omega⟩).val
    = 26 + 2 * k.val + s.val
  rw [md_val_Lc _ (by show 16 ≤ 18 + 2 * k.val + s.val ∧
    18 + 2 * k.val + s.val < 24; omega)]
  show 18 + 2 * k.val + s.val + 8 = 26 + 2 * k.val + s.val
  omega

/-- Matched slot of a right-antiquark slot. -/
theorem md_quarkRc (k : Fin 3) (s : Fin 2) :
    md ⟨26 + 2 * k.val + s.val, by omega⟩
      = ⟨18 + 2 * k.val + s.val, by omega⟩ := by
  apply Fin.ext
  show (md ⟨26 + 2 * k.val + s.val, by omega⟩).val
    = 18 + 2 * k.val + s.val
  rw [md_val_Rc _ (by show 24 ≤ 26 + 2 * k.val + s.val; omega)]
  show 26 + 2 * k.val + s.val - 8 = 18 + 2 * k.val + s.val
  omega

/-- The `Y8` weight at the quark base index. -/
theorem Y8_two (Ynu Ye Yu Yd : ℝ) (s : Fin 2) :
    Y8 Ynu Ye Yu Yd ⟨2 + s.val, by omega⟩
      = if s = 0 then (Yu : ℂ) else (Yd : ℂ) := by
  fin_cases s <;> simp [Y8]

/-- `Dval` on a left-quark slot: the up/down weight by flavour. -/
theorem Dval_quarkL (Ynu Ye Yu Yd : ℝ) (k : Fin 3) (s : Fin 2) :
    Dval Ynu Ye Yu Yd ⟨2 + 2 * k.val + s.val, by omega⟩
      = if s = 0 then (Yu : ℂ) else (Yd : ℂ) := by
  rw [Dval_eq]
  have hidx : (⟨(2 + 2 * k.val + s.val) % 8, by omega⟩ : Fin 8)
      = ⟨2 + 2 * k.val + s.val, by omega⟩ :=
    Fin.ext (by show (2 + 2 * k.val + s.val) % 8
      = 2 + 2 * k.val + s.val; omega)
  show Y8 Ynu Ye Yu Yd ⟨(2 + 2 * k.val + s.val) % 8, by omega⟩ = _
  rw [hidx, Y8_quark, Y8_two]

/-- `Dval` on a right-quark slot. -/
theorem Dval_quarkR (Ynu Ye Yu Yd : ℝ) (k : Fin 3) (s : Fin 2) :
    Dval Ynu Ye Yu Yd ⟨10 + 2 * k.val + s.val, by omega⟩
      = if s = 0 then (Yu : ℂ) else (Yd : ℂ) := by
  rw [Dval_eq]
  have hidx : (⟨(10 + 2 * k.val + s.val) % 8, by omega⟩ : Fin 8)
      = ⟨2 + 2 * k.val + s.val, by omega⟩ :=
    Fin.ext (by show (10 + 2 * k.val + s.val) % 8
      = 2 + 2 * k.val + s.val; omega)
  show Y8 Ynu Ye Yu Yd ⟨(10 + 2 * k.val + s.val) % 8, by omega⟩ = _
  rw [hidx, Y8_quark, Y8_two]

/-- `Dval` on a left-antiquark slot. -/
theorem Dval_quarkLc (Ynu Ye Yu Yd : ℝ) (k : Fin 3) (s : Fin 2) :
    Dval Ynu Ye Yu Yd ⟨18 + 2 * k.val + s.val, by omega⟩
      = if s = 0 then (Yu : ℂ) else (Yd : ℂ) := by
  rw [Dval_eq]
  have hidx : (⟨(18 + 2 * k.val + s.val) % 8, by omega⟩ : Fin 8)
      = ⟨2 + 2 * k.val + s.val, by omega⟩ :=
    Fin.ext (by show (18 + 2 * k.val + s.val) % 8
      = 2 + 2 * k.val + s.val; omega)
  show Y8 Ynu Ye Yu Yd ⟨(18 + 2 * k.val + s.val) % 8, by omega⟩ = _
  rw [hidx, Y8_quark, Y8_two]

/-- `Dval` on a right-antiquark slot. -/
theorem Dval_quarkRc (Ynu Ye Yu Yd : ℝ) (k : Fin 3) (s : Fin 2) :
    Dval Ynu Ye Yu Yd ⟨26 + 2 * k.val + s.val, by omega⟩
      = if s = 0 then (Yu : ℂ) else (Yd : ℂ) := by
  rw [Dval_eq]
  have hidx : (⟨(26 + 2 * k.val + s.val) % 8, by omega⟩ : Fin 8)
      = ⟨2 + 2 * k.val + s.val, by omega⟩ :=
    Fin.ext (by show (26 + 2 * k.val + s.val) % 8
      = 2 + 2 * k.val + s.val; omega)
  show Y8 Ynu Ye Yu Yd ⟨(26 + 2 * k.val + s.val) % 8, by omega⟩ = _
  rw [hidx, Y8_quark, Y8_two]

/-- Slot decomposition of an `Lc` index. -/
theorem slot_Lc (i : I32) (hi : 16 ≤ i.val ∧ i.val < 24) :
    (∃ s : Fin 2, i = ⟨16 + s.val, by omega⟩) ∨
    (∃ (k : Fin 3) (s : Fin 2),
      i = ⟨18 + 2 * k.val + s.val, by omega⟩) := by
  by_cases h : i.val < 18
  · exact Or.inl ⟨⟨i.val - 16, by omega⟩,
      Fin.ext (by show i.val = 16 + (i.val - 16); omega)⟩
  · exact Or.inr ⟨⟨(i.val - 18) / 2, by omega⟩,
      ⟨(i.val - 18) % 2, by omega⟩,
      Fin.ext (by
        show i.val = 18 + 2 * ((i.val - 18) / 2) + (i.val - 18) % 2
        omega)⟩

/-- Slot decomposition of an `Rc` index. -/
theorem slot_Rc (i : I32) (hi : 24 ≤ i.val) :
    i = ⟨24, by omega⟩ ∨ i = ⟨25, by omega⟩ ∨
    (∃ (k : Fin 3) (s : Fin 2),
      i = ⟨26 + 2 * k.val + s.val, by omega⟩) := by
  by_cases h24 : i.val = 24
  · exact Or.inl (Fin.ext (by show i.val = 24; omega))
  · by_cases h25 : i.val = 25
    · exact Or.inr (Or.inl (Fin.ext (by show i.val = 25; omega)))
    · exact Or.inr (Or.inr ⟨⟨(i.val - 26) / 2, by omega⟩,
        ⟨(i.val - 26) % 2, by omega⟩,
        Fin.ext (by
          show i.val = 26 + 2 * ((i.val - 26) / 2) + (i.val - 26) % 2
          omega)⟩)

/-- **The commutator vanishes on `(Lc, Lc)` pairs.** -/
theorem comm_anti_LcLc (Ynu Ye Yu Yd : ℝ) (a : AF) {i j : I32}
    (hi : 16 ≤ i.val ∧ i.val < 24) (hj : 16 ≤ j.val ∧ j.val < 24) :
    (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) i j
      = 0 := by
  have hmi : (md i).val = i.val + 8 := md_val_Lc i hi
  have hmj : (md j).val = j.val + 8 := md_val_Lc j hj
  rw [comm_entry,
    pi1_entry_eq_zero_of_not_sameBlock a
      (not_sameBlock_of_ne_sector (i := md i) (j := j) (by omega)),
    pi1_entry_eq_zero_of_not_sameBlock a
      (not_sameBlock_of_ne_sector (i := i) (j := md j) (by omega)),
    mul_zero, zero_mul, sub_zero]

/-- **The commutator vanishes on `(Rc, Rc)` pairs.** -/
theorem comm_anti_RcRc (Ynu Ye Yu Yd : ℝ) (a : AF) {i j : I32}
    (hi : 24 ≤ i.val) (hj : 24 ≤ j.val) :
    (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) i j
      = 0 := by
  have hmi : (md i).val = i.val - 8 := md_val_Rc i hi
  have hmj : (md j).val = j.val - 8 := md_val_Rc j hj
  rw [comm_entry,
    pi1_entry_eq_zero_of_not_sameBlock a
      (not_sameBlock_of_ne_sector (i := md i) (j := j) (by omega)),
    pi1_entry_eq_zero_of_not_sameBlock a
      (not_sameBlock_of_ne_sector (i := i) (j := md j) (by omega)),
    mul_zero, zero_mul, sub_zero]

/-- Matched slot of the literal `16`. -/
theorem md16 : md ⟨16, by omega⟩ = ⟨24, by omega⟩ := md_lepLc 0

/-- Matched slot of the literal `24`. -/
theorem md24 : md ⟨24, by omega⟩ = ⟨16, by omega⟩ := by
  apply Fin.ext
  show (md ⟨24, by omega⟩).val = 16
  rw [md_val_Rc _ (by show (24:ℕ) ≤ 24; omega)]
  show 24 - 8 = 16
  rfl

/-- Matched slot of the literal `17`. -/
theorem md17 : md ⟨17, by omega⟩ = ⟨25, by omega⟩ := md_lepLc 1

/-- Matched slot of the literal `25`. -/
theorem md25 : md ⟨25, by omega⟩ = ⟨17, by omega⟩ := by
  apply Fin.ext
  show (md ⟨25, by omega⟩).val = 17
  rw [md_val_Rc _ (by show (24:ℕ) ≤ 25; omega)]
  show 25 - 8 = 17
  rfl

/-- `Dval` at the literal `16`: the neutrino weight. -/
theorem Dval16 (Ynu Ye Yu Yd : ℝ) :
    Dval Ynu Ye Yu Yd ⟨16, by omega⟩ = (Ynu : ℂ) := rfl

/-- `Dval` at the literal `17`: the electron weight. -/
theorem Dval17 (Ynu Ye Yu Yd : ℝ) :
    Dval Ynu Ye Yu Yd ⟨17, by omega⟩ = (Ye : ℂ) := rfl

/-- `Dval` at the literal `24`: the neutrino weight. -/
theorem Dval24 (Ynu Ye Yu Yd : ℝ) :
    Dval Ynu Ye Yu Yd ⟨24, by omega⟩ = (Ynu : ℂ) := rfl

/-- `Dval` at the literal `25`: the electron weight. -/
theorem Dval25 (Ynu Ye Yu Yd : ℝ) :
    Dval Ynu Ye Yu Yd ⟨25, by omega⟩ = (Ye : ℂ) := rfl

/-- **The commutator vanishes on `(Lc, Rc)` pairs**: the matched
rectangles cancel entrywise (the two matched factors carry the same
entry and the same real weight). -/
theorem comm_anti_LcRc (Ynu Ye Yu Yd : ℝ) (a : AF) {i j : I32}
    (hi : 16 ≤ i.val ∧ i.val < 24) (hj : 24 ≤ j.val) :
    (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) i j
      = 0 := by
  have hmi : (md i).val = i.val + 8 := md_val_Lc i hi
  have hmj : (md j).val = j.val - 8 := md_val_Rc j hj
  rcases slot_Lc i hi with ⟨s, his⟩ | ⟨ki, si, his⟩
  · have hiv : i.val = 16 + s.val := congrArg Fin.val his
    rcases slot_Rc j hj with hj24 | hj25 | ⟨kj, sj, hjq⟩
    · have hjv : j.val = 24 := congrArg Fin.val hj24
      by_cases hs : s = 0
      · subst hs
        have hmd : md ⟨16 + (0:Fin 2).val, by omega⟩ = ⟨24, by omega⟩ :=
          md_lepLc 0
        have hmdj : md j = ⟨16, by omega⟩ := by rw [hj24]; exact md24
        have e2 : pi1 a ⟨16 + (0:Fin 2).val, by omega⟩ ⟨16, by omega⟩
            = star a.u1 := by
          have h := pi1_entry_leptonLc a 0 0
          rwa [if_pos rfl] at h
        have d1 : Dval Ynu Ye Yu Yd ⟨16 + (0:Fin 2).val, by omega⟩
            = (Ynu : ℂ) := Dval16 Ynu Ye Yu Yd
        rw [his, hj24, comm_entry, hmd, md24, pi1_entry_nuRc, e2, d1, Dval16,
          mul_comm (Ynu : ℂ) (star a.u1), sub_self]
      · have hs1 : s = 1 := by
          apply Fin.ext
          have h0 : s.val ≠ 0 := fun hh => hs (Fin.ext hh)
          show s.val = 1
          omega
        subst hs1
        have hmdj : md j = ⟨16, by omega⟩ := by rw [hj24]; exact md24
        have e2 : pi1 a ⟨16 + (1:Fin 2).val, by omega⟩ ⟨16, by omega⟩
            = 0 := by
          have h := pi1_entry_leptonLc a 1 0
          rw [if_neg (by decide)] at h
          exact h
        rw [comm_entry,
          pi1_entry_eq_zero_of_not_sameBlock a
            (not_sameBlock_of_Hc_mixed (i := md i) (j := j) (by omega)),
          hmdj, his, e2, mul_zero, zero_mul, sub_self]
    · have hjv : j.val = 25 := congrArg Fin.val hj25
      by_cases hs : s = 1
      · subst hs
        have hmd : md ⟨16 + (1:Fin 2).val, by omega⟩ = ⟨25, by omega⟩ :=
          md_lepLc 1
        have hmdj : md j = ⟨17, by omega⟩ := by rw [hj25]; exact md25
        have e2 : pi1 a ⟨16 + (1:Fin 2).val, by omega⟩ ⟨17, by omega⟩
            = star a.u1 := by
          have h := pi1_entry_leptonLc a 1 1
          rwa [if_pos rfl] at h
        have d1 : Dval Ynu Ye Yu Yd ⟨16 + (1:Fin 2).val, by omega⟩
            = (Ye : ℂ) := Dval17 Ynu Ye Yu Yd
        rw [his, hj25, comm_entry, hmd, md25, pi1_entry_eRc, e2, d1, Dval17,
          mul_comm (Ye : ℂ) (star a.u1), sub_self]
      · have hs0 : s = 0 := by
          apply Fin.ext
          have h1 : s.val ≠ 1 := fun hh => hs (Fin.ext hh)
          show s.val = 0
          omega
        subst hs0
        have hmdj : md j = ⟨17, by omega⟩ := by rw [hj25]; exact md25
        have e2 : pi1 a ⟨16 + (0:Fin 2).val, by omega⟩ ⟨17, by omega⟩
            = 0 := by
          have h := pi1_entry_leptonLc a 0 1
          rw [if_neg (by decide)] at h
          exact h
        rw [comm_entry,
          pi1_entry_eq_zero_of_not_sameBlock a
            (not_sameBlock_of_Hc_mixed (i := md i) (j := j) (by omega)),
          hmdj, his, e2, mul_zero, zero_mul, sub_self]
    · have hjv : j.val = 26 + 2 * kj.val + sj.val := congrArg Fin.val hjq
      rw [comm_entry,
        pi1_entry_eq_zero_of_not_sameBlock a
          (not_sameBlock_of_Hc_mixed (i := md i) (j := j) (by omega)),
        pi1_entry_eq_zero_of_not_sameBlock a
          (not_sameBlock_of_Hc_mixed (i := i) (j := md j) (by omega)),
        mul_zero, zero_mul, sub_self]
  · have hiv : i.val = 18 + 2 * ki.val + si.val := congrArg Fin.val his
    rcases slot_Rc j hj with hj24 | hj25 | ⟨kj, sj, hjq⟩
    · have hjv : j.val = 24 := congrArg Fin.val hj24
      rw [comm_entry,
        pi1_entry_eq_zero_of_not_sameBlock a
          (not_sameBlock_of_Hc_mixed (i := md i) (j := j) (by omega)),
        pi1_entry_eq_zero_of_not_sameBlock a
          (not_sameBlock_of_Hc_mixed (i := i) (j := md j) (by omega)),
        mul_zero, zero_mul, sub_self]
    · have hjv : j.val = 25 := congrArg Fin.val hj25
      rw [comm_entry,
        pi1_entry_eq_zero_of_not_sameBlock a
          (not_sameBlock_of_Hc_mixed (i := md i) (j := j) (by omega)),
        pi1_entry_eq_zero_of_not_sameBlock a
          (not_sameBlock_of_Hc_mixed (i := i) (j := md j) (by omega)),
        mul_zero, zero_mul, sub_self]
    · have hjv : j.val = 26 + 2 * kj.val + sj.val := congrArg Fin.val hjq
      rw [his, hjq, comm_entry, md_quarkLc, md_quarkRc,
        pi1_entry_quarkRc, pi1_entry_quarkLc, Dval_quarkLc, Dval_quarkLc]
      by_cases h : si = sj
      · subst h
        rw [if_pos rfl, mul_comm, sub_self]
      · rw [if_neg h, mul_zero, zero_mul, sub_self]

/-- **The commutator vanishes on `(Rc, Lc)` pairs**: the matched
rectangles cancel entrywise. -/
theorem comm_anti_RcLc (Ynu Ye Yu Yd : ℝ) (a : AF) {i j : I32}
    (hi : 24 ≤ i.val) (hj : 16 ≤ j.val ∧ j.val < 24) :
    (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) i j
      = 0 := by
  have hmi : (md i).val = i.val - 8 := md_val_Rc i hi
  have hmj : (md j).val = j.val + 8 := md_val_Lc j hj
  rcases slot_Rc i hi with hi24 | hi25 | ⟨ki, si, his⟩
  · have hiv : i.val = 24 := congrArg Fin.val hi24
    rcases slot_Lc j hj with ⟨s, hjs⟩ | ⟨kj, sj, hjq⟩
    · have hjv : j.val = 16 + s.val := congrArg Fin.val hjs
      by_cases hs : s = 0
      · subst hs
        have hmd : md ⟨24, by omega⟩ = ⟨16, by omega⟩ := md24
        have hmdj : md j = ⟨24, by omega⟩ := by
          rw [hjs]; exact md_lepLc 0
        have e1 : pi1 a ⟨16, by omega⟩ ⟨16 + (0:Fin 2).val, by omega⟩
            = star a.u1 := by
          have h := pi1_entry_leptonLc a 0 0
          rwa [if_pos rfl] at h
        have e2 : pi1 a ⟨24, by omega⟩ ⟨24 + (0:Fin 2).val, by omega⟩
            = star a.u1 := pi1_entry_nuRc a
        have d1 : Dval Ynu Ye Yu Yd ⟨24, by omega⟩ = (Ynu : ℂ) :=
          Dval24 Ynu Ye Yu Yd
        have d2 : Dval Ynu Ye Yu Yd ⟨24 + (0:Fin 2).val, by omega⟩
            = (Ynu : ℂ) := Dval24 Ynu Ye Yu Yd
        rw [hi24, hjs, comm_entry, hmd, md_lepLc, e1, e2, d1, d2,
          mul_comm (Ynu : ℂ) (star a.u1), sub_self]
      · have hs1 : s = 1 := by
          apply Fin.ext
          have h0 : s.val ≠ 0 := fun hh => hs (Fin.ext hh)
          show s.val = 1
          omega
        subst hs1
        have hmdi : md i = ⟨16, by omega⟩ := by rw [hi24]; exact md24
        have e1 : pi1 a ⟨16, by omega⟩ ⟨16 + (1:Fin 2).val, by omega⟩
            = 0 := by
          have h := pi1_entry_leptonLc a 0 1
          rw [if_neg (by decide)] at h
          exact h
        have hF2 : pi1 a i (md j) = 0 :=
          pi1_entry_eq_zero_of_not_sameBlock a
            (not_sameBlock_of_Hc_mixed (i := i) (j := md j) (by omega))
        rw [comm_entry, hF2, hmdi, hjs, e1, mul_zero, zero_mul, sub_self]
    · have hjv : j.val = 18 + 2 * kj.val + sj.val := congrArg Fin.val hjq
      rw [comm_entry,
        pi1_entry_eq_zero_of_not_sameBlock a
          (not_sameBlock_of_Hc_mixed (i := md i) (j := j) (by omega)),
        pi1_entry_eq_zero_of_not_sameBlock a
          (not_sameBlock_of_Hc_mixed (i := i) (j := md j) (by omega)),
        mul_zero, zero_mul, sub_self]
  · have hiv : i.val = 25 := congrArg Fin.val hi25
    rcases slot_Lc j hj with ⟨s, hjs⟩ | ⟨kj, sj, hjq⟩
    · have hjv : j.val = 16 + s.val := congrArg Fin.val hjs
      by_cases hs : s = 1
      · subst hs
        have hmd : md ⟨25, by omega⟩ = ⟨17, by omega⟩ := md25
        have hmdj : md j = ⟨25, by omega⟩ := by
          rw [hjs]; exact md_lepLc 1
        have e1 : pi1 a ⟨17, by omega⟩ ⟨16 + (1:Fin 2).val, by omega⟩
            = star a.u1 := by
          have h := pi1_entry_leptonLc a 1 1
          rwa [if_pos rfl] at h
        have e2 : pi1 a ⟨25, by omega⟩ ⟨24 + (1:Fin 2).val, by omega⟩
            = star a.u1 := pi1_entry_eRc a
        have d1 : Dval Ynu Ye Yu Yd ⟨25, by omega⟩ = (Ye : ℂ) :=
          Dval25 Ynu Ye Yu Yd
        have d2 : Dval Ynu Ye Yu Yd ⟨24 + (1:Fin 2).val, by omega⟩
            = (Ye : ℂ) := Dval25 Ynu Ye Yu Yd
        rw [hi25, hjs, comm_entry, hmd, md_lepLc, e1, e2, d1, d2,
          mul_comm (Ye : ℂ) (star a.u1), sub_self]
      · have hs0 : s = 0 := by
          apply Fin.ext
          have h1 : s.val ≠ 1 := fun hh => hs (Fin.ext hh)
          show s.val = 0
          omega
        subst hs0
        have hmdi : md i = ⟨17, by omega⟩ := by rw [hi25]; exact md25
        have e1 : pi1 a ⟨17, by omega⟩ ⟨16 + (0:Fin 2).val, by omega⟩
            = 0 := by
          have h := pi1_entry_leptonLc a 1 0
          rw [if_neg (by decide)] at h
          exact h
        have hF2 : pi1 a i (md j) = 0 :=
          pi1_entry_eq_zero_of_not_sameBlock a
            (not_sameBlock_of_Hc_mixed (i := i) (j := md j) (by omega))
        rw [comm_entry, hF2, hmdi, hjs, e1, mul_zero, zero_mul, sub_self]
    · have hjv : j.val = 18 + 2 * kj.val + sj.val := congrArg Fin.val hjq
      rw [comm_entry,
        pi1_entry_eq_zero_of_not_sameBlock a
          (not_sameBlock_of_Hc_mixed (i := md i) (j := j) (by omega)),
        pi1_entry_eq_zero_of_not_sameBlock a
          (not_sameBlock_of_Hc_mixed (i := i) (j := md j) (by omega)),
        mul_zero, zero_mul, sub_self]
  · have hiv : i.val = 26 + 2 * ki.val + si.val := congrArg Fin.val his
    rcases slot_Lc j hj with ⟨s, hjs⟩ | ⟨kj, sj, hjq⟩
    · have hjv : j.val = 16 + s.val := congrArg Fin.val hjs
      rw [comm_entry,
        pi1_entry_eq_zero_of_not_sameBlock a
          (not_sameBlock_of_Hc_mixed (i := md i) (j := j) (by omega)),
        pi1_entry_eq_zero_of_not_sameBlock a
          (not_sameBlock_of_Hc_mixed (i := i) (j := md j) (by omega)),
        mul_zero, zero_mul, sub_self]
    · have hjv : j.val = 18 + 2 * kj.val + sj.val := congrArg Fin.val hjq
      rw [his, hjq, comm_entry, md_quarkRc, md_quarkLc,
        pi1_entry_quarkLc, pi1_entry_quarkRc, Dval_quarkRc, Dval_quarkRc]
      by_cases h : si = sj
      · subst h
        rw [if_pos rfl, mul_comm, sub_self]
      · rw [if_neg h, mul_zero, zero_mul, sub_self]

/-- **The commutator vanishes on all antiparticle pairs.** -/
theorem comm_anti_anti (Ynu Ye Yu Yd : ℝ) (a : AF) {i j : I32}
    (hi : 16 ≤ i.val) (hj : 16 ≤ j.val) :
    (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) i j
      = 0 := by
  by_cases hi24 : 24 ≤ i.val
  · by_cases hj24 : 24 ≤ j.val
    · exact comm_anti_RcRc Ynu Ye Yu Yd a hi24 hj24
    · exact comm_anti_RcLc Ynu Ye Yu Yd a hi24 ⟨hj, by omega⟩
  · by_cases hj24 : 24 ≤ j.val
    · exact comm_anti_LcRc Ynu Ye Yu Yd a ⟨hi, by omega⟩ hj24
    · exact comm_anti_LcLc Ynu Ye Yu Yd a ⟨hi, by omega⟩ ⟨hj, by omega⟩

/-- **The live relation, forward**: a live pair makes one of the
two matched factors block-resident. -/
theorem mdBlock_forward {i k : I32} (hi : i.val < 16) (hk : k.val < 16)
    (h : mdBlock i k) : sameBlock (md i) k ∨ sameBlock i (md k) := by
  by_cases hi8 : i.val < 8
  · by_cases hk8 : k.val < 8
    · exfalso
      unfold mdBlock at h
      rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ |
        ⟨a1, a2, a3, a4⟩ <;> omega
    · have hmi : (md i).val = i.val + 8 := md_val_L i hi8
      have hmk : (md k).val = k.val - 8 := md_val_R k ⟨by omega, hk⟩
      unfold mdBlock at h
      rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ |
        ⟨a1, a2, a3, a4⟩
      · refine Or.inr ?_
        unfold sameBlock
        exact Or.inl ⟨by omega, by omega⟩
      · exfalso; omega
      · exfalso; omega
      · refine Or.inl ?_
        unfold sameBlock
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨by omega, by omega, by omega, by omega⟩))))
      · exfalso; omega
  · by_cases hk8 : k.val < 8
    · have hmi : (md i).val = i.val - 8 := md_val_R i ⟨by omega, hi⟩
      have hmk : (md k).val = k.val + 8 := md_val_L k hk8
      unfold mdBlock at h
      rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ |
        ⟨a1, a2, a3, a4⟩
      · exfalso; omega
      · refine Or.inl ?_
        unfold sameBlock
        exact Or.inl ⟨by omega, by omega⟩
      · refine Or.inl ?_
        unfold sameBlock
        exact Or.inl ⟨by omega, by omega⟩
      · exfalso; omega
      · refine Or.inl ?_
        unfold sameBlock
        exact Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)
    · exfalso
      unfold mdBlock at h
      rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ |
        ⟨a1, a2, a3, a4⟩ <;> omega

/-- **The live relation, backward**: block-residency of a matched
factor forces the live relation. -/
theorem mdBlock_backward {i k : I32} (hi : i.val < 16) (hk : k.val < 16)
    (h : sameBlock (md i) k ∨ sameBlock i (md k)) : mdBlock i k := by
  by_cases hi8 : i.val < 8
  · by_cases hk8 : k.val < 8
    · exfalso
      have hmi : (md i).val = i.val + 8 := md_val_L i hi8
      have hmk : (md k).val = k.val + 8 := md_val_L k hk8
      rcases h with h | h <;>
        (unfold sameBlock at h;
         rcases h with ⟨b1, b2⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2⟩ | ⟨b1, b2⟩ |
           ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2⟩ |
           ⟨b1, b2⟩ | ⟨b1, b2, b3, b4⟩) <;> omega
    · have hmi : (md i).val = i.val + 8 := md_val_L i hi8
      have hmk : (md k).val = k.val - 8 := md_val_R k ⟨by omega, hk⟩
      rcases h with h | h <;>
        (unfold sameBlock at h;
         rcases h with ⟨b1, b2⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2⟩ | ⟨b1, b2⟩ |
           ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2⟩ |
           ⟨b1, b2⟩ | ⟨b1, b2, b3, b4⟩) <;>
        (unfold mdBlock; omega)
  · by_cases hk8 : k.val < 8
    · have hmi : (md i).val = i.val - 8 := md_val_R i ⟨by omega, hi⟩
      have hmk : (md k).val = k.val + 8 := md_val_L k hk8
      rcases h with h | h <;>
        (unfold sameBlock at h;
         rcases h with ⟨b1, b2⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2⟩ | ⟨b1, b2⟩ |
           ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2⟩ |
           ⟨b1, b2⟩ | ⟨b1, b2, b3, b4⟩) <;>
        (unfold mdBlock; omega)
    · exfalso
      have hmi : (md i).val = i.val - 8 := md_val_R i ⟨by omega, hi⟩
      have hmk : (md k).val = k.val - 8 := md_val_R k ⟨by omega, hk⟩
      rcases h with h | h <;>
        (unfold sameBlock at h;
         rcases h with ⟨b1, b2⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2⟩ | ⟨b1, b2⟩ |
           ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2⟩ |
           ⟨b1, b2⟩ | ⟨b1, b2, b3, b4⟩) <;> omega

/-- **The live relation, characterized**: for particle slots,
`mdBlock i k` holds iff one of the two matched factors can be
nonzero. -/
theorem mdBlock_iff (i k : I32) (hi : i.val < 16) (hk : k.val < 16) :
    mdBlock i k ↔ sameBlock (md i) k ∨ sameBlock i (md k) :=
  ⟨mdBlock_forward hi hk, mdBlock_backward hi hk⟩

/-- **Commutator support**: a nonzero commutator entry at particle
slots forces the live relation. -/
theorem comm_support (Ynu Ye Yu Yd : ℝ) (a : AF) {i k : I32}
    (hi : i.val < 16) (hk : k.val < 16)
    (hC : (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
      i k ≠ 0) :
    mdBlock i k := by
  rw [comm_entry] at hC
  have hne : pi1 a (md i) k ≠ 0 ∨ pi1 a i (md k) ≠ 0 := by
    by_contra hc
    push_neg at hc
    rw [hc.1, hc.2, mul_zero, zero_mul, sub_self] at hC
    exact hC rfl
  rw [mdBlock_iff i k hi hk]
  rcases hne with h1 | h2
  · refine Or.inl ?_
    by_contra hns
    exact h1 (pi1_entry_eq_zero_of_not_sameBlock a hns)
  · refine Or.inr ?_
    by_contra hns
    exact h2 (pi1_entry_eq_zero_of_not_sameBlock a hns)

/-! ### §8c. The first-order condition: pair lemmas and assembly. -/

/-- `sameBlock` preserves the two halves. -/
theorem sameBlock_half {i k : I32} (h : sameBlock i k) :
    (i.val < 16 ↔ k.val < 16) := by
  unfold sameBlock at h
  rcases h with ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ |
    ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2⟩ |
    ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ <;> omega

/-- Range of the live partner of a left-lepton slot. -/
theorem mdBlock_range_lepL {i k : I32} (hi : i.val < 2)
    (h : mdBlock i k) : k.val = 8 ∨ k.val = 9 := by
  unfold mdBlock at h
  rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ |
    ⟨a1, a2, a3, a4⟩ <;> omega

/-- Range of the live partner of the `ν_R` slot. -/
theorem mdBlock_range_nuR {i k : I32} (hi : i.val = 8)
    (h : mdBlock i k) : k.val < 2 := by
  unfold mdBlock at h
  rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ |
    ⟨a1, a2, a3, a4⟩ <;> omega

/-- Range of the live partner of the `e_R` slot. -/
theorem mdBlock_range_eR {i k : I32} (hi : i.val = 9)
    (h : mdBlock i k) : k.val < 2 := by
  unfold mdBlock at h
  rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ |
    ⟨a1, a2, a3, a4⟩ <;> omega

/-- Range of the live partner of a left-quark slot. -/
theorem mdBlock_range_quarkL {i k : I32}
    (hi : 2 ≤ i.val ∧ i.val < 8) (h : mdBlock i k) :
    10 ≤ k.val ∧ k.val < 16 := by
  unfold mdBlock at h
  rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ |
    ⟨a1, a2, a3, a4⟩ <;> omega

/-- Range of the live partner of a right-quark slot. -/
theorem mdBlock_range_quarkR {i k : I32}
    (hi : 10 ≤ i.val ∧ i.val < 16) (h : mdBlock i k) :
    2 ≤ k.val ∧ k.val < 8 := by
  unfold mdBlock at h
  rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ |
    ⟨a1, a2, a3, a4⟩ <;> omega

/-- Source range over a left-lepton column. -/
theorem mdBlock_source_lepL {k j : I32} (hj : j.val < 2)
    (h : mdBlock k j) : k.val = 8 ∨ k.val = 9 := by
  unfold mdBlock at h
  rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ |
    ⟨a1, a2, a3, a4⟩ <;> omega

/-- Source range over the `ν_R` column. -/
theorem mdBlock_source_nuR {k j : I32} (hj : j.val = 8)
    (h : mdBlock k j) : k.val < 2 := by
  unfold mdBlock at h
  rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ |
    ⟨a1, a2, a3, a4⟩ <;> omega

/-- Source range over the `e_R` column. -/
theorem mdBlock_source_eR {k j : I32} (hj : j.val = 9)
    (h : mdBlock k j) : k.val < 2 := by
  unfold mdBlock at h
  rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ |
    ⟨a1, a2, a3, a4⟩ <;> omega

/-- Source range over a left-quark column. -/
theorem mdBlock_source_quarkL {k j : I32}
    (hj : 2 ≤ j.val ∧ j.val < 8) (h : mdBlock k j) :
    10 ≤ k.val ∧ k.val < 16 := by
  unfold mdBlock at h
  rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ |
    ⟨a1, a2, a3, a4⟩ <;> omega

/-- Source range over a right-quark column. -/
theorem mdBlock_source_quarkR {k j : I32}
    (hj : 10 ≤ j.val ∧ j.val < 16) (h : mdBlock k j) :
    2 ≤ k.val ∧ k.val < 8 := by
  unfold mdBlock at h
  rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ |
    ⟨a1, a2, a3, a4⟩ <;> omega

/-- Block range of a left-lepton row's block-mate. -/
theorem sameBlock_range_lepL {i k : I32} (hi : i.val < 2)
    (h : sameBlock i k) : k.val < 2 := by
  unfold sameBlock at h
  rcases h with ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ |
    ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2⟩ |
    ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ <;> omega

/-- Block range of the `ν_R` row's block-mate. -/
theorem sameBlock_range_nuR {i k : I32} (hi : i.val = 8)
    (h : sameBlock i k) : k.val = 8 := by
  unfold sameBlock at h
  rcases h with ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ |
    ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2⟩ |
    ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ <;> omega

/-- Block range of the `e_R` row's block-mate. -/
theorem sameBlock_range_eR {i k : I32} (hi : i.val = 9)
    (h : sameBlock i k) : k.val = 9 := by
  unfold sameBlock at h
  rcases h with ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ |
    ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2⟩ |
    ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ <;> omega

/-- Block range of a left-quark row's block-mate. -/
theorem sameBlock_range_quarkL {i k : I32}
    (hi : 2 ≤ i.val ∧ i.val < 8) (h : sameBlock i k) :
    2 ≤ k.val ∧ k.val < 8 := by
  unfold sameBlock at h
  rcases h with ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ |
    ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2⟩ |
    ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ <;> omega

/-- Block range of a right-quark row's block-mate. -/
theorem sameBlock_range_quarkR {i k : I32}
    (hi : 10 ≤ i.val ∧ i.val < 16) (h : sameBlock i k) :
    10 ≤ k.val ∧ k.val < 16 := by
  unfold sameBlock at h
  rcases h with ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ |
    ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2⟩ |
    ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ <;> omega

/-- **Pair (lepL, ν_R)**: the double-commutator entry vanishes —
the two sums collapse to the same matched term. -/
theorem pair_lepL_nuR (Ynu Ye Yu Yd : ℝ) (a b : AF) (s : Fin 2) :
    ((DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) * rho1 b
      - rho1 b * (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a *
        DF_oneGen Ynu Ye Yu Yd))
      ⟨s.val, by omega⟩ ⟨8, by omega⟩ = 0 := by
  have hval : (⟨s.val, by omega⟩ : I32).val = s.val := rfl
  have hsum1 : (∑ k : I32,
      (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
        ⟨s.val, by omega⟩ k * rho1 b k ⟨8, by omega⟩)
      = (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
          ⟨s.val, by omega⟩ ⟨8, by omega⟩ * star b.u1 := by
    rw [Finset.sum_eq_single ⟨8, by omega⟩]
    · rw [rho1_entry_nuR]
    · intro k _ hk
      by_cases hk16 : k.val < 16
      · by_cases hC : (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a *
            DF_oneGen Ynu Ye Yu Yd) ⟨s.val, by omega⟩ k = 0
        · rw [hC, zero_mul]
        · have hmd := comm_support Ynu Ye Yu Yd a (by omega) hk16 hC
          have hkr := mdBlock_range_lepL (by omega) hmd
          rcases hkr with h8 | h9
          · exfalso; exact hk (Fin.ext h8)
          · have hkf : k = ⟨9, by omega⟩ := Fin.ext h9
            rw [hkf, rho1_entry, partner_mk9, partner_mk8,
              pi1_entry_eq_zero_of_not_sameBlock b
                (not_sameBlock_of_Hc_mixed (i := (⟨24, by omega⟩ : I32))
                  (j := (⟨25, by omega⟩ : I32))
                  (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inl ⟨rfl, rfl⟩)))))))), mul_zero]
      · rw [comm_particle_anti (i := (⟨s.val, by omega⟩ : I32)) (j := k)
          Ynu Ye Yu Yd a (by omega) (by omega), zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ (⟨8, by omega⟩ : I32)) hcon
  have hsum2 : (∑ k : I32,
      rho1 b ⟨s.val, by omega⟩ k *
        (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
          k ⟨8, by omega⟩)
      = star b.u1 * (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a *
          DF_oneGen Ynu Ye Yu Yd) ⟨s.val, by omega⟩ ⟨8, by omega⟩ := by
    rw [Finset.sum_eq_single ⟨s.val, by omega⟩]
    · rw [rho1_entry_leptonL, if_pos rfl]
    · intro k _ hk
      by_cases hk2 : k.val < 2
      · have hkf : k = ⟨(⟨k.val, hk2⟩ : Fin 2).val, by omega⟩ := Fin.ext rfl
        have hts : (⟨k.val, hk2⟩ : Fin 2) ≠ s := fun hh =>
          hk (Fin.ext (show k.val = s.val from congrArg Fin.val hh))
        rw [hkf, rho1_entry_leptonL, if_neg hts, zero_mul]
      · by_cases hR : rho1 b ⟨s.val, by omega⟩ k = 0
        · rw [hR, zero_mul]
        · exfalso
          have hsb := rho1_support b hR
          have hkr := sameBlock_range_lepL (by omega) hsb
          omega
    · intro hcon
      exact absurd (Finset.mem_univ (⟨s.val, by omega⟩ : I32)) hcon
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, hsum1, hsum2,
    mul_comm, sub_self]

/-- **Pair (lepL, e_R)**: the double-commutator entry vanishes. -/
theorem pair_lepL_eR (Ynu Ye Yu Yd : ℝ) (a b : AF) (s : Fin 2) :
    ((DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) * rho1 b
      - rho1 b * (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a *
        DF_oneGen Ynu Ye Yu Yd))
      ⟨s.val, by omega⟩ ⟨9, by omega⟩ = 0 := by
  have hval : (⟨s.val, by omega⟩ : I32).val = s.val := rfl
  have hsum1 : (∑ k : I32,
      (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
        ⟨s.val, by omega⟩ k * rho1 b k ⟨9, by omega⟩)
      = (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
          ⟨s.val, by omega⟩ ⟨9, by omega⟩ * star b.u1 := by
    rw [Finset.sum_eq_single ⟨9, by omega⟩]
    · rw [rho1_entry_eR]
    · intro k _ hk
      by_cases hk16 : k.val < 16
      · by_cases hC : (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a *
            DF_oneGen Ynu Ye Yu Yd) ⟨s.val, by omega⟩ k = 0
        · rw [hC, zero_mul]
        · have hmd := comm_support Ynu Ye Yu Yd a (by omega) hk16 hC
          have hkr := mdBlock_range_lepL (by omega) hmd
          rcases hkr with h8 | h9
          · have hkf : k = ⟨8, by omega⟩ := Fin.ext h8
            rw [hkf, rho1_entry, partner_mk8, partner_mk9,
              pi1_entry_eq_zero_of_not_sameBlock b
                (not_sameBlock_of_Hc_mixed (i := (⟨25, by omega⟩ : I32))
                  (j := (⟨24, by omega⟩ : I32))
                  (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr ⟨rfl, rfl⟩)))))))), mul_zero]
          · exfalso; exact hk (Fin.ext h9)
      · rw [comm_particle_anti (i := (⟨s.val, by omega⟩ : I32)) (j := k)
          Ynu Ye Yu Yd a (by omega) (by omega), zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ (⟨9, by omega⟩ : I32)) hcon
  have hsum2 : (∑ k : I32,
      rho1 b ⟨s.val, by omega⟩ k *
        (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
          k ⟨9, by omega⟩)
      = star b.u1 * (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a *
          DF_oneGen Ynu Ye Yu Yd) ⟨s.val, by omega⟩ ⟨9, by omega⟩ := by
    rw [Finset.sum_eq_single ⟨s.val, by omega⟩]
    · rw [rho1_entry_leptonL, if_pos rfl]
    · intro k _ hk
      by_cases hk2 : k.val < 2
      · have hkf : k = ⟨(⟨k.val, hk2⟩ : Fin 2).val, by omega⟩ := Fin.ext rfl
        have hts : (⟨k.val, hk2⟩ : Fin 2) ≠ s := fun hh =>
          hk (Fin.ext (show k.val = s.val from congrArg Fin.val hh))
        rw [hkf, rho1_entry_leptonL, if_neg hts, zero_mul]
      · by_cases hR : rho1 b ⟨s.val, by omega⟩ k = 0
        · rw [hR, zero_mul]
        · exfalso
          have hsb := rho1_support b hR
          have hkr := sameBlock_range_lepL (by omega) hsb
          omega
    · intro hcon
      exact absurd (Finset.mem_univ (⟨s.val, by omega⟩ : I32)) hcon
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, hsum1, hsum2,
    mul_comm, sub_self]

/-- **Pair (ν_R, lepL)**: the double-commutator entry vanishes. -/
theorem pair_nuR_lepL (Ynu Ye Yu Yd : ℝ) (a b : AF) (s : Fin 2) :
    ((DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) * rho1 b
      - rho1 b * (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a *
        DF_oneGen Ynu Ye Yu Yd))
      ⟨8, by omega⟩ ⟨s.val, by omega⟩ = 0 := by
  have hval : (⟨s.val, by omega⟩ : I32).val = s.val := rfl
  have hsum1 : (∑ k : I32,
      (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
        ⟨8, by omega⟩ k * rho1 b k ⟨s.val, by omega⟩)
      = (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
          ⟨8, by omega⟩ ⟨s.val, by omega⟩ * star b.u1 := by
    rw [Finset.sum_eq_single ⟨s.val, by omega⟩]
    · rw [rho1_entry_leptonL, if_pos rfl]
    · intro k _ hk
      by_cases hR : rho1 b k ⟨s.val, by omega⟩ = 0
      · rw [hR, mul_zero]
      · have hsb := rho1_support b hR
        have hk2 : k.val < 2 :=
          sameBlock_range_lepL (by omega) (sameBlock_symm hsb)
        have hkf : k = ⟨(⟨k.val, hk2⟩ : Fin 2).val, by omega⟩ := Fin.ext rfl
        have hst : s ≠ (⟨k.val, hk2⟩ : Fin 2) := fun hh =>
          hk (Fin.ext (show k.val = s.val from
            (congrArg Fin.val hh).symm))
        rw [hkf, rho1_entry_leptonL, if_neg hst, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ (⟨s.val, by omega⟩ : I32)) hcon
  have hsum2 : (∑ k : I32,
      rho1 b ⟨8, by omega⟩ k *
        (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
          k ⟨s.val, by omega⟩)
      = star b.u1 * (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a *
          DF_oneGen Ynu Ye Yu Yd) ⟨8, by omega⟩ ⟨s.val, by omega⟩ := by
    rw [Finset.sum_eq_single ⟨8, by omega⟩]
    · rw [rho1_entry_nuR]
    · intro k _ hk
      by_cases hR : rho1 b ⟨8, by omega⟩ k = 0
      · rw [hR, zero_mul]
      · exfalso
        have hsb := rho1_support b hR
        have hkr := sameBlock_range_nuR rfl hsb
        exact hk (Fin.ext hkr)
    · intro hcon
      exact absurd (Finset.mem_univ (⟨8, by omega⟩ : I32)) hcon
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, hsum1, hsum2,
    mul_comm, sub_self]

/-- **Pair (e_R, lepL)**: the double-commutator entry vanishes. -/
theorem pair_eR_lepL (Ynu Ye Yu Yd : ℝ) (a b : AF) (s : Fin 2) :
    ((DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) * rho1 b
      - rho1 b * (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a *
        DF_oneGen Ynu Ye Yu Yd))
      ⟨9, by omega⟩ ⟨s.val, by omega⟩ = 0 := by
  have hval : (⟨s.val, by omega⟩ : I32).val = s.val := rfl
  have hsum1 : (∑ k : I32,
      (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
        ⟨9, by omega⟩ k * rho1 b k ⟨s.val, by omega⟩)
      = (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
          ⟨9, by omega⟩ ⟨s.val, by omega⟩ * star b.u1 := by
    rw [Finset.sum_eq_single ⟨s.val, by omega⟩]
    · rw [rho1_entry_leptonL, if_pos rfl]
    · intro k _ hk
      by_cases hR : rho1 b k ⟨s.val, by omega⟩ = 0
      · rw [hR, mul_zero]
      · have hsb := rho1_support b hR
        have hk2 : k.val < 2 :=
          sameBlock_range_lepL (by omega) (sameBlock_symm hsb)
        have hkf : k = ⟨(⟨k.val, hk2⟩ : Fin 2).val, by omega⟩ := Fin.ext rfl
        have hst : s ≠ (⟨k.val, hk2⟩ : Fin 2) := fun hh =>
          hk (Fin.ext (show k.val = s.val from
            (congrArg Fin.val hh).symm))
        rw [hkf, rho1_entry_leptonL, if_neg hst, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ (⟨s.val, by omega⟩ : I32)) hcon
  have hsum2 : (∑ k : I32,
      rho1 b ⟨9, by omega⟩ k *
        (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
          k ⟨s.val, by omega⟩)
      = star b.u1 * (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a *
          DF_oneGen Ynu Ye Yu Yd) ⟨9, by omega⟩ ⟨s.val, by omega⟩ := by
    rw [Finset.sum_eq_single ⟨9, by omega⟩]
    · rw [rho1_entry_eR]
    · intro k _ hk
      by_cases hR : rho1 b ⟨9, by omega⟩ k = 0
      · rw [hR, zero_mul]
      · exfalso
        have hsb := rho1_support b hR
        have hkr := sameBlock_range_eR rfl hsb
        exact hk (Fin.ext hkr)
    · intro hcon
      exact absurd (Finset.mem_univ (⟨9, by omega⟩ : I32)) hcon
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, hsum1, hsum2,
    mul_comm, sub_self]

/-- **Closed form of the commutator on (quarkL, quarkR) entries.** -/
theorem comm_quarkLR_entry (Ynu Ye Yu Yd : ℝ) (a : AF)
    (ki kk : Fin 3) (si sk : Fin 2) :
    (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
        ⟨2 + 2 * ki.val + si.val, by omega⟩
        ⟨10 + 2 * kk.val + sk.val, by omega⟩
      = (if si = 0 then (Yu : ℂ) else (Yd : ℂ)) *
          (if si = sk ∧ ki = kk then (if si = 0 then a.u1 else star a.u1)
            else 0)
        - (if ki = kk then a.q si sk else 0) *
          (if sk = 0 then (Yu : ℂ) else (Yd : ℂ)) := by
  rw [comm_entry, md_quarkL, md_quarkR, pi1_entry_quarkR, pi1_entry_quarkL,
    Dval_quarkL, Dval_quarkL]

/-- **Closed form of the commutator on (quarkR, quarkL) entries.** -/
theorem comm_quarkRL_entry (Ynu Ye Yu Yd : ℝ) (a : AF)
    (ki kk : Fin 3) (si sk : Fin 2) :
    (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
        ⟨10 + 2 * ki.val + si.val, by omega⟩
        ⟨2 + 2 * kk.val + sk.val, by omega⟩
      = (if si = 0 then (Yu : ℂ) else (Yd : ℂ)) *
          (if ki = kk then a.q si sk else 0)
        - (if si = sk ∧ ki = kk then (if si = 0 then a.u1 else star a.u1)
            else 0) * (if sk = 0 then (Yu : ℂ) else (Yd : ℂ)) := by
  rw [comm_entry, md_quarkR, md_quarkL, pi1_entry_quarkL, pi1_entry_quarkR,
    Dval_quarkR, Dval_quarkR]

/-- **The quark pair identity (L,R)**: the two matched commutator
entries agree — the colour index rides along symmetrically. -/
theorem comm_quarkLR_id (Ynu Ye Yu Yd : ℝ) (a : AF)
    (ki kj : Fin 3) (si sj : Fin 2) :
    (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
        ⟨2 + 2 * ki.val + si.val, by omega⟩
        ⟨10 + 2 * ki.val + sj.val, by omega⟩
      = (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
          ⟨2 + 2 * kj.val + si.val, by omega⟩
          ⟨10 + 2 * kj.val + sj.val, by omega⟩ := by
  rw [comm_quarkLR_entry, comm_quarkLR_entry]
  simp only [eq_self_iff_true, and_true, if_true]

/-- **The quark pair identity (R,L)**. -/
theorem comm_quarkRL_id (Ynu Ye Yu Yd : ℝ) (a : AF)
    (ki kj : Fin 3) (si sj : Fin 2) :
    (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
        ⟨10 + 2 * ki.val + si.val, by omega⟩
        ⟨2 + 2 * ki.val + sj.val, by omega⟩
      = (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
          ⟨10 + 2 * kj.val + si.val, by omega⟩
          ⟨2 + 2 * kj.val + sj.val, by omega⟩ := by
  rw [comm_quarkRL_entry, comm_quarkRL_entry]
  simp only [eq_self_iff_true, and_true, if_true]

/-- **Pair (quarkL, quarkR)**: the double-commutator entry vanishes —
both sums collapse to the identity-matched term. -/
theorem pair_quarkLR (Ynu Ye Yu Yd : ℝ) (a b : AF)
    (ki kj : Fin 3) (si sj : Fin 2) :
    ((DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) * rho1 b
      - rho1 b * (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a *
        DF_oneGen Ynu Ye Yu Yd))
      ⟨2 + 2 * ki.val + si.val, by omega⟩
      ⟨10 + 2 * kj.val + sj.val, by omega⟩ = 0 := by
  have hval : (⟨2 + 2 * ki.val + si.val, by omega⟩ : I32).val
      = 2 + 2 * ki.val + si.val := rfl
  have hsum1 : (∑ k : I32,
      (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
        ⟨2 + 2 * ki.val + si.val, by omega⟩ k * rho1 b k
        ⟨10 + 2 * kj.val + sj.val, by omega⟩)
      = (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
          ⟨2 + 2 * ki.val + si.val, by omega⟩
          ⟨10 + 2 * ki.val + sj.val, by omega⟩ * star (b.color kj ki) := by
    rw [Finset.sum_eq_single ⟨10 + 2 * ki.val + sj.val, by omega⟩]
    · rw [rho1_entry_quarkR, if_pos rfl]
    · intro k _ hk
      by_cases hk16 : k.val < 16
      · by_cases hC : (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a *
            DF_oneGen Ynu Ye Yu Yd)
            ⟨2 + 2 * ki.val + si.val, by omega⟩ k = 0
        · rw [hC, zero_mul]
        · have hmd := comm_support Ynu Ye Yu Yd a (by omega) hk16 hC
          have hkr := mdBlock_range_quarkL (by omega) hmd
          obtain ⟨kk, sk, hkf⟩ : (∃ (kk : Fin 3) (sk : Fin 2),
              k = ⟨10 + 2 * kk.val + sk.val, by omega⟩) :=
            ⟨⟨(k.val - 10) / 2, by omega⟩, ⟨(k.val - 10) % 2, by omega⟩,
              Fin.ext (by
                show k.val = 10 + 2 * ((k.val - 10) / 2) + (k.val - 10) % 2
                omega)⟩
          by_cases hkk : kk = ki
          · have hsk : sk ≠ sj := by
              intro hh
              apply hk
              rw [hkf, hkk, hh]
            have hRk : rho1 b k ⟨10 + 2 * kj.val + sj.val, by omega⟩
                = 0 := by
              rw [hkf, rho1_entry_quarkR, if_neg (fun hh => hsk hh.symm)]
            rw [hRk, mul_zero]
          · exfalso
            apply hC
            rw [hkf, comm_quarkLR_entry,
              if_neg (show ¬ (si = sk ∧ ki = kk) from fun hh => hkk hh.2.symm),
              if_neg (show ¬ (ki = kk) from fun hh => hkk hh.symm),
              mul_zero, zero_mul, sub_self]
      · rw [comm_particle_anti
          (i := (⟨2 + 2 * ki.val + si.val, by omega⟩ : I32)) (j := k)
          Ynu Ye Yu Yd a (by omega) (by omega), zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ
        (⟨10 + 2 * ki.val + sj.val, by omega⟩ : I32)) hcon
  have hsum2 : (∑ k : I32,
      rho1 b ⟨2 + 2 * ki.val + si.val, by omega⟩ k *
        (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
          k ⟨10 + 2 * kj.val + sj.val, by omega⟩)
      = star (b.color kj ki) *
          (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
            ⟨2 + 2 * kj.val + si.val, by omega⟩
            ⟨10 + 2 * kj.val + sj.val, by omega⟩ := by
    rw [Finset.sum_eq_single ⟨2 + 2 * kj.val + si.val, by omega⟩]
    · rw [rho1_entry_quarkL, if_pos rfl]
    · intro k _ hk
      by_cases hR : rho1 b ⟨2 + 2 * ki.val + si.val, by omega⟩ k = 0
      · rw [hR, zero_mul]
      · have hsb := rho1_support b hR
        have hk16 : k.val < 16 := (sameBlock_half hsb).mp (by omega)
        have hkr := sameBlock_range_quarkL (by omega) hsb
        obtain ⟨kk, sk, hkf⟩ : (∃ (kk : Fin 3) (sk : Fin 2),
            k = ⟨2 + 2 * kk.val + sk.val, by omega⟩) :=
          ⟨⟨(k.val - 2) / 2, by omega⟩, ⟨(k.val - 2) % 2, by omega⟩,
            Fin.ext (by
              show k.val = 2 + 2 * ((k.val - 2) / 2) + (k.val - 2) % 2
              omega)⟩
        by_cases hsk : sk = si
        · have hkk : kk ≠ kj := by
            intro hh
            apply hk
            rw [hkf, hh, hsk]
          have hCk : (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a *
              DF_oneGen Ynu Ye Yu Yd) k
              ⟨10 + 2 * kj.val + sj.val, by omega⟩ = 0 := by
            rw [hkf, comm_quarkLR_entry,
              if_neg (show ¬ (sk = sj ∧ kk = kj) from fun hh => hkk hh.2),
              if_neg (show ¬ (kk = kj) from fun hh => hkk hh),
              mul_zero, zero_mul, sub_self]
          rw [hCk, mul_zero]
        · have hRk : rho1 b ⟨2 + 2 * ki.val + si.val, by omega⟩ k
              = 0 := by
            rw [hkf, rho1_entry_quarkL, if_neg hsk]
          rw [hRk, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ
        (⟨2 + 2 * kj.val + si.val, by omega⟩ : I32)) hcon
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, hsum1, hsum2,
    comm_quarkLR_id, mul_comm, sub_self]

/-- **Pair (quarkR, quarkL)**: the double-commutator entry vanishes. -/
theorem pair_quarkRL (Ynu Ye Yu Yd : ℝ) (a b : AF)
    (ki kj : Fin 3) (si sj : Fin 2) :
    ((DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) * rho1 b
      - rho1 b * (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a *
        DF_oneGen Ynu Ye Yu Yd))
      ⟨10 + 2 * ki.val + si.val, by omega⟩
      ⟨2 + 2 * kj.val + sj.val, by omega⟩ = 0 := by
  have hval : (⟨10 + 2 * ki.val + si.val, by omega⟩ : I32).val
      = 10 + 2 * ki.val + si.val := rfl
  have hsum1 : (∑ k : I32,
      (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
        ⟨10 + 2 * ki.val + si.val, by omega⟩ k * rho1 b k
        ⟨2 + 2 * kj.val + sj.val, by omega⟩)
      = (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
          ⟨10 + 2 * ki.val + si.val, by omega⟩
          ⟨2 + 2 * ki.val + sj.val, by omega⟩ * star (b.color kj ki) := by
    rw [Finset.sum_eq_single ⟨2 + 2 * ki.val + sj.val, by omega⟩]
    · rw [rho1_entry_quarkL, if_pos rfl]
    · intro k _ hk
      by_cases hk16 : k.val < 16
      · by_cases hC : (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a *
            DF_oneGen Ynu Ye Yu Yd)
            ⟨10 + 2 * ki.val + si.val, by omega⟩ k = 0
        · rw [hC, zero_mul]
        · have hmd := comm_support Ynu Ye Yu Yd a (by omega) hk16 hC
          have hkr := mdBlock_range_quarkR (by omega) hmd
          obtain ⟨kk, sk, hkf⟩ : (∃ (kk : Fin 3) (sk : Fin 2),
              k = ⟨2 + 2 * kk.val + sk.val, by omega⟩) :=
            ⟨⟨(k.val - 2) / 2, by omega⟩, ⟨(k.val - 2) % 2, by omega⟩,
              Fin.ext (by
                show k.val = 2 + 2 * ((k.val - 2) / 2) + (k.val - 2) % 2
                omega)⟩
          by_cases hkk : kk = ki
          · have hsk : sk ≠ sj := by
              intro hh
              apply hk
              rw [hkf, hkk, hh]
            have hRk : rho1 b k ⟨2 + 2 * kj.val + sj.val, by omega⟩
                = 0 := by
              rw [hkf, rho1_entry_quarkL, if_neg (fun hh => hsk hh.symm)]
            rw [hRk, mul_zero]
          · exfalso
            apply hC
            rw [hkf, comm_quarkRL_entry,
              if_neg (show ¬ (ki = kk) from fun hh => hkk hh.symm),
              if_neg (show ¬ (si = sk ∧ ki = kk) from fun hh => hkk hh.2.symm),
              mul_zero, zero_mul, sub_self]
      · rw [comm_particle_anti
          (i := (⟨10 + 2 * ki.val + si.val, by omega⟩ : I32)) (j := k)
          Ynu Ye Yu Yd a (by omega) (by omega), zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ
        (⟨2 + 2 * ki.val + sj.val, by omega⟩ : I32)) hcon
  have hsum2 : (∑ k : I32,
      rho1 b ⟨10 + 2 * ki.val + si.val, by omega⟩ k *
        (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
          k ⟨2 + 2 * kj.val + sj.val, by omega⟩)
      = star (b.color kj ki) *
          (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
            ⟨10 + 2 * kj.val + si.val, by omega⟩
            ⟨2 + 2 * kj.val + sj.val, by omega⟩ := by
    rw [Finset.sum_eq_single ⟨10 + 2 * kj.val + si.val, by omega⟩]
    · rw [rho1_entry_quarkR, if_pos rfl]
    · intro k _ hk
      by_cases hR : rho1 b ⟨10 + 2 * ki.val + si.val, by omega⟩ k = 0
      · rw [hR, zero_mul]
      · have hsb := rho1_support b hR
        have hk16 : k.val < 16 := (sameBlock_half hsb).mp (by omega)
        have hkr := sameBlock_range_quarkR (by omega) hsb
        obtain ⟨kk, sk, hkf⟩ : (∃ (kk : Fin 3) (sk : Fin 2),
            k = ⟨10 + 2 * kk.val + sk.val, by omega⟩) :=
          ⟨⟨(k.val - 10) / 2, by omega⟩, ⟨(k.val - 10) % 2, by omega⟩,
            Fin.ext (by
              show k.val = 10 + 2 * ((k.val - 10) / 2) + (k.val - 10) % 2
              omega)⟩
        by_cases hsk : sk = si
        · have hkk : kk ≠ kj := by
            intro hh
            apply hk
            rw [hkf, hh, hsk]
          have hCk : (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a *
              DF_oneGen Ynu Ye Yu Yd) k
              ⟨2 + 2 * kj.val + sj.val, by omega⟩ = 0 := by
            rw [hkf, comm_quarkRL_entry,
              if_neg (show ¬ (kk = kj) from fun hh => hkk hh),
              if_neg (show ¬ (sk = sj ∧ kk = kj) from fun hh => hkk hh.2),
              mul_zero, zero_mul, sub_self]
          rw [hCk, mul_zero]
        · have hRk : rho1 b ⟨10 + 2 * ki.val + si.val, by omega⟩ k
              = 0 := by
            rw [hkf, rho1_entry_quarkR, if_neg hsk]
          rw [hRk, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ
        (⟨10 + 2 * kj.val + si.val, by omega⟩ : I32)) hcon
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, hsum1, hsum2,
    comm_quarkRL_id, mul_comm, sub_self]

/-- **Generic first sum kill**: if the `mdBlock`/`sameBlock` ranges of
`i` and `j` are incompatible, every `C * R` term vanishes. -/
theorem gen_s1 (Ynu Ye Yu Yd : ℝ) (a b : AF) {i j : I32}
    (hi : i.val < 16) (hj : j.val < 16)
    (hcontra : ∀ k : I32, mdBlock i k → sameBlock j k → False) :
    ∀ k : I32, (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) i k * rho1 b k j = 0 := by
  intro k
  by_cases hk16 : k.val < 16
  · by_cases hC : (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) i k = 0
    · rw [hC, zero_mul]
    · by_cases hR : rho1 b k j = 0
      · rw [hR, mul_zero]
      · exfalso
        exact hcontra k (comm_support Ynu Ye Yu Yd a hi hk16 hC)
          (sameBlock_symm (rho1_support b hR))
  · rw [comm_particle_anti (i := i) (j := k) Ynu Ye Yu Yd a hi
      (by omega), zero_mul]

/-- **Generic second sum kill** (mirror). -/
theorem gen_s2 (Ynu Ye Yu Yd : ℝ) (a b : AF) {i j : I32}
    (hi : i.val < 16) (hj : j.val < 16)
    (hcontra : ∀ k : I32, sameBlock i k → mdBlock k j → False) :
    ∀ k : I32, rho1 b i k * (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) k j = 0 := by
  intro k
  by_cases hR : rho1 b i k = 0
  · rw [hR, zero_mul]
  · have hsb := rho1_support b hR
    have hk16 : k.val < 16 := (sameBlock_half hsb).mp hi
    by_cases hC : (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) k j = 0
    · rw [hC, mul_zero]
    · exfalso
      exact hcontra k hsb (comm_support Ynu Ye Yu Yd a hk16 hj hC)

/-- **T5 — FIRST-ORDER CONDITION (entry form)**: for all `a b : AF` and
all slots `i j`, `[[D_F, π₁ a], ρ₁° b] i j = 0`, against the landed
`DF_oneGen` (NOT edited, K-RB1). The double commutator vanishes
identically: antiparticle rows/columns die by the §8a/§8b support
lemmas; particle pairs die by the six matched-pair identities; every
other particle pair dies by the `mdBlock`/`sameBlock` range clash. -/
theorem pi1_first_order (Ynu Ye Yu Yd : ℝ) (a b : AF) (i j : I32) :
    (((DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) * rho1 b - rho1 b * (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd))) i j = 0 := by
  by_cases hiA : 16 ≤ i.val
  · rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
      Finset.sum_eq_zero (f := fun k => (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) i k * rho1 b k j)
        (fun k _ => by
          by_cases hk : 16 ≤ k.val
          · rw [comm_anti_anti Ynu Ye Yu Yd a hiA hk, zero_mul]
          · rw [comm_anti_particle Ynu Ye Yu Yd a hiA (by omega),
              zero_mul]),
      Finset.sum_eq_zero (f := fun k => rho1 b i k * (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) k j)
        (fun k _ => by
          by_cases hk : 16 ≤ k.val
          · by_cases hjA : 16 ≤ j.val
            · rw [comm_anti_anti Ynu Ye Yu Yd a hk hjA, mul_zero]
            · rw [comm_anti_particle Ynu Ye Yu Yd a hk (by omega),
                mul_zero]
          · have hns : ¬ sameBlock i k := fun hs =>
              (by omega : ¬ i.val < 16) ((sameBlock_half hs).mpr
                (by omega))
            rw [rho1_entry_eq_zero_of_not_sameBlock b hns, zero_mul]),
      sub_self]
  · have hi16 : i.val < 16 := by omega
    by_cases hjA : 16 ≤ j.val
    · rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
        Finset.sum_eq_zero (f := fun k => (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) i k * rho1 b k j)
          (fun k _ => by
            by_cases hR : rho1 b k j = 0
            · rw [hR, mul_zero]
            · have hsb := rho1_support b hR
              have hk16 : 16 ≤ k.val := by
                by_contra hlt
                have h2 := (sameBlock_half hsb).mp (by omega : k.val < 16)
                omega
              rw [comm_particle_anti Ynu Ye Yu Yd a hi16 hk16, zero_mul]),
        Finset.sum_eq_zero (f := fun k => rho1 b i k * (DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd) k j)
          (fun k _ => by
            by_cases hk : 16 ≤ k.val
            · rw [comm_anti_anti Ynu Ye Yu Yd a hk hjA, mul_zero]
            · rw [comm_particle_anti Ynu Ye Yu Yd a (by omega) hjA,
                mul_zero]),
        sub_self]
    · have hj16 : j.val < 16 := by omega
      by_cases hi2 : i.val < 2
      ·
        by_cases hj2 : j.val < 2
        ·
          rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
            Finset.sum_eq_zero (fun k _ => gen_s1 Ynu Ye Yu Yd a b hi16 hj16
              (by intro k h1 h2
                  have r1 := mdBlock_range_lepL hi2 h1
                  have r2 := sameBlock_range_lepL hj2 h2
                  omega) k),
            Finset.sum_eq_zero (fun k _ => gen_s2 Ynu Ye Yu Yd a b hi16 hj16
              (by intro k h1 h2
                  have r1 := sameBlock_range_lepL hi2 h1
                  have r2 := mdBlock_source_lepL hj2 h2
                  omega) k), sub_self]
        · by_cases hj8 : j.val = 8
          ·
            have his : i = ⟨(⟨i.val, hi2⟩ : Fin 2).val, by omega⟩ :=
              Fin.ext rfl
            have hjj : j = ⟨8, by omega⟩ := Fin.ext hj8
            rw [his, hjj]
            exact pair_lepL_nuR Ynu Ye Yu Yd a b ⟨i.val, hi2⟩
          · by_cases hj9 : j.val = 9
            ·
              have his : i = ⟨(⟨i.val, hi2⟩ : Fin 2).val, by omega⟩ :=
                Fin.ext rfl
              have hjj : j = ⟨9, by omega⟩ := Fin.ext hj9
              rw [his, hjj]
              exact pair_lepL_eR Ynu Ye Yu Yd a b ⟨i.val, hi2⟩
            · by_cases hj10 : 10 ≤ j.val
              · have hjR : 10 ≤ j.val ∧ j.val < 16 := ⟨hj10, hj16⟩
                rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
                  Finset.sum_eq_zero (fun k _ => gen_s1 Ynu Ye Yu Yd a b hi16 hj16
                    (by intro k h1 h2
                        have r1 := mdBlock_range_lepL hi2 h1
                        have r2 := sameBlock_range_quarkR hjR h2
                        omega) k),
                  Finset.sum_eq_zero (fun k _ => gen_s2 Ynu Ye Yu Yd a b hi16 hj16
                    (by intro k h1 h2
                        have r1 := sameBlock_range_lepL hi2 h1
                        have r2 := mdBlock_source_quarkR hjR h2
                        omega) k), sub_self]
              · have hjQ : 2 ≤ j.val ∧ j.val < 8 := ⟨by omega, by omega⟩
                rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
                  Finset.sum_eq_zero (fun k _ => gen_s1 Ynu Ye Yu Yd a b hi16 hj16
                    (by intro k h1 h2
                        have r1 := mdBlock_range_lepL hi2 h1
                        have r2 := sameBlock_range_quarkL hjQ h2
                        omega) k),
                  Finset.sum_eq_zero (fun k _ => gen_s2 Ynu Ye Yu Yd a b hi16 hj16
                    (by intro k h1 h2
                        have r1 := sameBlock_range_lepL hi2 h1
                        have r2 := mdBlock_source_quarkL hjQ h2
                        omega) k), sub_self]
      · by_cases hi8 : i.val = 8
        ·
          by_cases hj2 : j.val < 2
          ·
            have his : i = ⟨8, by omega⟩ := Fin.ext hi8
            have hjj : j = ⟨(⟨j.val, hj2⟩ : Fin 2).val, by omega⟩ :=
              Fin.ext rfl
            rw [his, hjj]
            exact pair_nuR_lepL Ynu Ye Yu Yd a b ⟨j.val, hj2⟩
          · by_cases hj8 : j.val = 8
            ·
              rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
                Finset.sum_eq_zero (fun k _ => gen_s1 Ynu Ye Yu Yd a b hi16 hj16
                  (by intro k h1 h2
                      have r1 := mdBlock_range_nuR hi8 h1
                      have r2 := sameBlock_range_nuR hj8 h2
                      omega) k),
                Finset.sum_eq_zero (fun k _ => gen_s2 Ynu Ye Yu Yd a b hi16 hj16
                  (by intro k h1 h2
                      have r1 := sameBlock_range_nuR hi8 h1
                      have r2 := mdBlock_source_nuR hj8 h2
                      omega) k), sub_self]
            · by_cases hj9 : j.val = 9
              ·
                rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
                  Finset.sum_eq_zero (fun k _ => gen_s1 Ynu Ye Yu Yd a b hi16 hj16
                    (by intro k h1 h2
                        have r1 := mdBlock_range_nuR hi8 h1
                        have r2 := sameBlock_range_eR hj9 h2
                        omega) k),
                  Finset.sum_eq_zero (fun k _ => gen_s2 Ynu Ye Yu Yd a b hi16 hj16
                    (by intro k h1 h2
                        have r1 := sameBlock_range_nuR hi8 h1
                        have r2 := mdBlock_source_eR hj9 h2
                        omega) k), sub_self]
              · by_cases hj10 : 10 ≤ j.val
                · have hjR : 10 ≤ j.val ∧ j.val < 16 := ⟨hj10, hj16⟩
                  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
                    Finset.sum_eq_zero (fun k _ => gen_s1 Ynu Ye Yu Yd a b hi16 hj16
                      (by intro k h1 h2
                          have r1 := mdBlock_range_nuR hi8 h1
                          have r2 := sameBlock_range_quarkR hjR h2
                          omega) k),
                    Finset.sum_eq_zero (fun k _ => gen_s2 Ynu Ye Yu Yd a b hi16 hj16
                      (by intro k h1 h2
                          have r1 := sameBlock_range_nuR hi8 h1
                          have r2 := mdBlock_source_quarkR hjR h2
                          omega) k), sub_self]
                · have hjQ : 2 ≤ j.val ∧ j.val < 8 := ⟨by omega, by omega⟩
                  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
                    Finset.sum_eq_zero (fun k _ => gen_s1 Ynu Ye Yu Yd a b hi16 hj16
                      (by intro k h1 h2
                          have r1 := mdBlock_range_nuR hi8 h1
                          have r2 := sameBlock_range_quarkL hjQ h2
                          omega) k),
                    Finset.sum_eq_zero (fun k _ => gen_s2 Ynu Ye Yu Yd a b hi16 hj16
                      (by intro k h1 h2
                          have r1 := sameBlock_range_nuR hi8 h1
                          have r2 := mdBlock_source_quarkL hjQ h2
                          omega) k), sub_self]
        · by_cases hi9 : i.val = 9
          ·
            by_cases hj2 : j.val < 2
            ·
              have his : i = ⟨9, by omega⟩ := Fin.ext hi9
              have hjj : j = ⟨(⟨j.val, hj2⟩ : Fin 2).val, by omega⟩ :=
                Fin.ext rfl
              rw [his, hjj]
              exact pair_eR_lepL Ynu Ye Yu Yd a b ⟨j.val, hj2⟩
            · by_cases hj8 : j.val = 8
              ·
                rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
                  Finset.sum_eq_zero (fun k _ => gen_s1 Ynu Ye Yu Yd a b hi16 hj16
                    (by intro k h1 h2
                        have r1 := mdBlock_range_eR hi9 h1
                        have r2 := sameBlock_range_nuR hj8 h2
                        omega) k),
                  Finset.sum_eq_zero (fun k _ => gen_s2 Ynu Ye Yu Yd a b hi16 hj16
                    (by intro k h1 h2
                        have r1 := sameBlock_range_eR hi9 h1
                        have r2 := mdBlock_source_nuR hj8 h2
                        omega) k), sub_self]
              · by_cases hj9 : j.val = 9
                ·
                  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
                    Finset.sum_eq_zero (fun k _ => gen_s1 Ynu Ye Yu Yd a b hi16 hj16
                      (by intro k h1 h2
                          have r1 := mdBlock_range_eR hi9 h1
                          have r2 := sameBlock_range_eR hj9 h2
                          omega) k),
                    Finset.sum_eq_zero (fun k _ => gen_s2 Ynu Ye Yu Yd a b hi16 hj16
                      (by intro k h1 h2
                          have r1 := sameBlock_range_eR hi9 h1
                          have r2 := mdBlock_source_eR hj9 h2
                          omega) k), sub_self]
                · by_cases hj10 : 10 ≤ j.val
                  · have hjR : 10 ≤ j.val ∧ j.val < 16 := ⟨hj10, hj16⟩
                    rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
                      Finset.sum_eq_zero (fun k _ => gen_s1 Ynu Ye Yu Yd a b hi16 hj16
                        (by intro k h1 h2
                            have r1 := mdBlock_range_eR hi9 h1
                            have r2 := sameBlock_range_quarkR hjR h2
                            omega) k),
                      Finset.sum_eq_zero (fun k _ => gen_s2 Ynu Ye Yu Yd a b hi16 hj16
                        (by intro k h1 h2
                            have r1 := sameBlock_range_eR hi9 h1
                            have r2 := mdBlock_source_quarkR hjR h2
                            omega) k), sub_self]
                  · have hjQ : 2 ≤ j.val ∧ j.val < 8 := ⟨by omega, by omega⟩
                    rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
                      Finset.sum_eq_zero (fun k _ => gen_s1 Ynu Ye Yu Yd a b hi16 hj16
                        (by intro k h1 h2
                            have r1 := mdBlock_range_eR hi9 h1
                            have r2 := sameBlock_range_quarkL hjQ h2
                            omega) k),
                      Finset.sum_eq_zero (fun k _ => gen_s2 Ynu Ye Yu Yd a b hi16 hj16
                        (by intro k h1 h2
                            have r1 := sameBlock_range_eR hi9 h1
                            have r2 := mdBlock_source_quarkL hjQ h2
                            omega) k), sub_self]
          · by_cases hi10 : 10 ≤ i.val
            · have hiR : 10 ≤ i.val ∧ i.val < 16 := ⟨hi10, hi16⟩
              by_cases hj2 : j.val < 2
              ·
                rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
                  Finset.sum_eq_zero (fun k _ => gen_s1 Ynu Ye Yu Yd a b hi16 hj16
                    (by intro k h1 h2
                        have r1 := mdBlock_range_quarkR hiR h1
                        have r2 := sameBlock_range_lepL hj2 h2
                        omega) k),
                  Finset.sum_eq_zero (fun k _ => gen_s2 Ynu Ye Yu Yd a b hi16 hj16
                    (by intro k h1 h2
                        have r1 := sameBlock_range_quarkR hiR h1
                        have r2 := mdBlock_source_lepL hj2 h2
                        omega) k), sub_self]
              · by_cases hj8 : j.val = 8
                ·
                  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
                    Finset.sum_eq_zero (fun k _ => gen_s1 Ynu Ye Yu Yd a b hi16 hj16
                      (by intro k h1 h2
                          have r1 := mdBlock_range_quarkR hiR h1
                          have r2 := sameBlock_range_nuR hj8 h2
                          omega) k),
                    Finset.sum_eq_zero (fun k _ => gen_s2 Ynu Ye Yu Yd a b hi16 hj16
                      (by intro k h1 h2
                          have r1 := sameBlock_range_quarkR hiR h1
                          have r2 := mdBlock_source_nuR hj8 h2
                          omega) k), sub_self]
                · by_cases hj9 : j.val = 9
                  ·
                    rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
                      Finset.sum_eq_zero (fun k _ => gen_s1 Ynu Ye Yu Yd a b hi16 hj16
                        (by intro k h1 h2
                            have r1 := mdBlock_range_quarkR hiR h1
                            have r2 := sameBlock_range_eR hj9 h2
                            omega) k),
                      Finset.sum_eq_zero (fun k _ => gen_s2 Ynu Ye Yu Yd a b hi16 hj16
                        (by intro k h1 h2
                            have r1 := sameBlock_range_quarkR hiR h1
                            have r2 := mdBlock_source_eR hj9 h2
                            omega) k), sub_self]
                  · by_cases hj10 : 10 ≤ j.val
                    · have hjR : 10 ≤ j.val ∧ j.val < 16 := ⟨hj10, hj16⟩
                      rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
                        Finset.sum_eq_zero (fun k _ => gen_s1 Ynu Ye Yu Yd a b hi16 hj16
                          (by intro k h1 h2
                              have r1 := mdBlock_range_quarkR hiR h1
                              have r2 := sameBlock_range_quarkR hjR h2
                              omega) k),
                        Finset.sum_eq_zero (fun k _ => gen_s2 Ynu Ye Yu Yd a b hi16 hj16
                          (by intro k h1 h2
                              have r1 := sameBlock_range_quarkR hiR h1
                              have r2 := mdBlock_source_quarkR hjR h2
                              omega) k), sub_self]
                    · have hjQ : 2 ≤ j.val ∧ j.val < 8 := ⟨by omega, by omega⟩
                      obtain ⟨ki, si, his⟩ : (∃ (ki : Fin 3) (si : Fin 2),
                          i = ⟨10 + 2 * ki.val + si.val, by omega⟩) :=
                        ⟨⟨(i.val - 10) / 2, by omega⟩, ⟨(i.val - 10) % 2, by omega⟩,
                          Fin.ext (by
                            show i.val = 10 + 2 * ((i.val - 10) / 2) + (i.val - 10) % 2
                            omega)⟩
                      obtain ⟨kj, sj, hjj⟩ : (∃ (kj : Fin 3) (sj : Fin 2),
                          j = ⟨2 + 2 * kj.val + sj.val, by omega⟩) :=
                        ⟨⟨(j.val - 2) / 2, by omega⟩, ⟨(j.val - 2) % 2, by omega⟩,
                          Fin.ext (by
                            show j.val = 2 + 2 * ((j.val - 2) / 2) + (j.val - 2) % 2
                            omega)⟩
                      rw [his, hjj]
                      exact pair_quarkRL Ynu Ye Yu Yd a b ki kj si sj
            · have hiQ : 2 ≤ i.val ∧ i.val < 8 := ⟨by omega, by omega⟩
              by_cases hj2 : j.val < 2
              ·
                rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
                  Finset.sum_eq_zero (fun k _ => gen_s1 Ynu Ye Yu Yd a b hi16 hj16
                    (by intro k h1 h2
                        have r1 := mdBlock_range_quarkL hiQ h1
                        have r2 := sameBlock_range_lepL hj2 h2
                        omega) k),
                  Finset.sum_eq_zero (fun k _ => gen_s2 Ynu Ye Yu Yd a b hi16 hj16
                    (by intro k h1 h2
                        have r1 := sameBlock_range_quarkL hiQ h1
                        have r2 := mdBlock_source_lepL hj2 h2
                        omega) k), sub_self]
              · by_cases hj8 : j.val = 8
                ·
                  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
                    Finset.sum_eq_zero (fun k _ => gen_s1 Ynu Ye Yu Yd a b hi16 hj16
                      (by intro k h1 h2
                          have r1 := mdBlock_range_quarkL hiQ h1
                          have r2 := sameBlock_range_nuR hj8 h2
                          omega) k),
                    Finset.sum_eq_zero (fun k _ => gen_s2 Ynu Ye Yu Yd a b hi16 hj16
                      (by intro k h1 h2
                          have r1 := sameBlock_range_quarkL hiQ h1
                          have r2 := mdBlock_source_nuR hj8 h2
                          omega) k), sub_self]
                · by_cases hj9 : j.val = 9
                  ·
                    rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
                      Finset.sum_eq_zero (fun k _ => gen_s1 Ynu Ye Yu Yd a b hi16 hj16
                        (by intro k h1 h2
                            have r1 := mdBlock_range_quarkL hiQ h1
                            have r2 := sameBlock_range_eR hj9 h2
                            omega) k),
                      Finset.sum_eq_zero (fun k _ => gen_s2 Ynu Ye Yu Yd a b hi16 hj16
                        (by intro k h1 h2
                            have r1 := sameBlock_range_quarkL hiQ h1
                            have r2 := mdBlock_source_eR hj9 h2
                            omega) k), sub_self]
                  · by_cases hj10 : 10 ≤ j.val
                    · have hjR : 10 ≤ j.val ∧ j.val < 16 := ⟨hj10, hj16⟩
                      obtain ⟨ki, si, his⟩ : (∃ (ki : Fin 3) (si : Fin 2),
                          i = ⟨2 + 2 * ki.val + si.val, by omega⟩) :=
                        ⟨⟨(i.val - 2) / 2, by omega⟩, ⟨(i.val - 2) % 2, by omega⟩,
                          Fin.ext (by
                            show i.val = 2 + 2 * ((i.val - 2) / 2) + (i.val - 2) % 2
                            omega)⟩
                      obtain ⟨kj, sj, hjj⟩ : (∃ (kj : Fin 3) (sj : Fin 2),
                          j = ⟨10 + 2 * kj.val + sj.val, by omega⟩) :=
                        ⟨⟨(j.val - 10) / 2, by omega⟩, ⟨(j.val - 10) % 2, by omega⟩,
                          Fin.ext (by
                            show j.val = 10 + 2 * ((j.val - 10) / 2) + (j.val - 10) % 2
                            omega)⟩
                      rw [his, hjj]
                      exact pair_quarkLR Ynu Ye Yu Yd a b ki kj si sj
                    · have hjQ : 2 ≤ j.val ∧ j.val < 8 := ⟨by omega, by omega⟩
                      rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
                        Finset.sum_eq_zero (fun k _ => gen_s1 Ynu Ye Yu Yd a b hi16 hj16
                          (by intro k h1 h2
                              have r1 := mdBlock_range_quarkL hiQ h1
                              have r2 := sameBlock_range_quarkL hjQ h2
                              omega) k),
                        Finset.sum_eq_zero (fun k _ => gen_s2 Ynu Ye Yu Yd a b hi16 hj16
                          (by intro k h1 h2
                              have r1 := sameBlock_range_quarkL hiQ h1
                              have r2 := mdBlock_source_quarkL hjQ h2
                              omega) k), sub_self]

/-! ## §9. T3 — the hypercharge lift, RE-DERIVED for π₁

The two-parameter diagonal analysis. `pi1AVal` (resp. `pi1BVal) is the
weight of the ℂ seat (resp. the M₃ seat) in π₁'s diagonal at each slot:
the lifted eigenvalue of the generator `(exp (α·t·i), 1, exp (β·t·i)·I)`
at slot `i` is `exp ((A i · α + B i · β) · t · i)`. Summing over the 32
slots: `∑ A = -4` and `∑ B = -12` (π₀'s were `∑ A₀ = -4`, `∑ B₀ = +12`
in the same conventions — the antiquark blocks' conjugation flip is
exactly the sign change in `∑ B`). Unimodularity therefore reads
`-4α - 12β = 0`: the surviving direction is `(α, β) = (3, -1)` —
**the direction's β-sign DIFFERS from π₀'s `(3, 1)`; the normalization
is still 3.** Along `(3, -1)` the weights `3A - B` coincide with π₀'s
`W` at every slot, so the lifted pattern is again `exp (3 · t · i · Y f)`
with the table's exact ratios. -/

/-- The ℂ-seat weight of π₁'s diagonal at slot `v`. -/
def pi1AVal (v : ℕ) : ℤ :=
  if v < 8 then 0
  else if v = 8 then 1
  else if v = 9 then -1
  else if v < 16 then (if (v - 10) % 2 = 0 then 1 else -1)
  else if v < 18 then -1
  else if v < 24 then 0
  else if v < 26 then -1
  else 0

/-- The M₃-seat weight of π₁'s diagonal at slot `v` (nonzero exactly on
the two antiquark blocks, where π₁ is M₃-pure conjugate: weight `-1`). -/
def pi1BVal (v : ℕ) : ℤ :=
  if v < 8 then 0
  else if v = 8 then 0
  else if v = 9 then 0
  else if v < 16 then 0
  else if v < 18 then 0
  else if v < 24 then -1
  else if v < 26 then 0
  else -1

/-- `∑ A = -4` over the 32 slots. -/
theorem sum_A : ∑ i : I32, pi1AVal i.val = -4 := by decide

/-- `∑ B = -12` over the 32 slots — the sign flip against π₀'s `+12`
is the whole headline of this section. -/
theorem sum_B : ∑ i : I32, pi1BVal i.val = -12 := by decide

/- The weight function `W` is carried over verbatim from the π₀
analysis; `pi1WVal_eq` below re-earns it for π₁ as the combination
`3A - B` along π₁'s own surviving direction `(3, -1)` (π₀'s `(3, 1)`
in the carried-over comment refers to the landed π₀ brick). -/
def pi1WVal (v : ℕ) : ℤ :=
  if v < 8 then 0
  else if v = 8 then 3
  else if v = 9 then -3
  else if v < 16 then (if (v - 10) % 2 = 0 then 3 else -3)
  else if v < 18 then -3
  else if v < 24 then 1
  else if v < 26 then -3
  else 1

/-- The integer weight function on slots. -/

def W (i : I32) : ℤ := pi1WVal i.val

/-- The weights sum to zero over the 32 slots — the exact arithmetic
content of unimodularity for the direction `(α, β) = (3, 1)`. -/

theorem sum_W : ∑ i, W i = 0 := by decide

/-- Along the surviving direction `(3, -1)`, π₁'s combined weights
`3A - B` equal π₀'s weights `W` at every slot. -/
theorem pi1WVal_eq (i : I32) :
    pi1WVal i.val = 3 * pi1AVal i.val - pi1BVal i.val := by
  fin_cases i <;> decide

/-- Conjugation of an integer-weighted phase. -/
theorem star_exp_int (n : ℤ) (t : ℝ) :
    star (Complex.exp ((n : ℂ) * ((t : ℂ) * Complex.I)))
      = Complex.exp (-((n : ℂ) * ((t : ℂ) * Complex.I))) := by
  rw [← starRingEnd_apply, ← Complex.exp_conj]
  congr 1
  rw [Complex.ext_iff]
  simp

/-- Conjugation of the inverse phase `exp (-t·i)`. -/
theorem star_exp_neg_one (t : ℝ) :
    star (Complex.exp (-((t : ℂ) * Complex.I)))
      = Complex.exp ((t : ℂ) * Complex.I) := by
  rw [← starRingEnd_apply, ← Complex.exp_conj]
  congr 1
  rw [Complex.ext_iff]
  simp

/-- Conjugation of the ℂ seat's phase `exp (3·t·i)` (the seat value is
unchanged from π₀, so the landed idiom applies verbatim). -/
theorem star_exp_three (t : ℝ) :
    star (Complex.exp (3 * (t : ℂ) * Complex.I))
      = Complex.exp (-(3 * (t : ℂ) * Complex.I)) := by
  rw [← starRingEnd_apply, ← Complex.exp_conj]
  congr 1
  rw [Complex.ext_iff]
  simp

/-- **The two-parameter diagonal of π₁**: at the generator with seat
values `exp (α·t·i)` (ℂ seat) and `exp (β·t·i)` (M₃ seat), the diagonal
entry at slot `i` is `exp ((A i · α + B i · β) · t · i)`. -/

theorem pi1Diag_exp_gen (α β : ℤ) (t : ℝ) (i : I32) :
    pi1Diag (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
        (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i
      = Complex.exp (((pi1AVal i.val * α + pi1BVal i.val * β : ℤ) : ℂ) *
          ((t : ℂ) * Complex.I)) := by
  have hv : i.val < 32 := i.isLt
  by_cases h8 : i.val < 8
  · have hD : pi1DiagVal (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
        (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i.val = 1 := by
      unfold pi1DiagVal
      rw [if_pos h8]
    have hA : pi1AVal i.val = 0 := by
      unfold pi1AVal
      rw [if_pos h8]
    have hB : pi1BVal i.val = 0 := by
      unfold pi1BVal
      rw [if_pos h8]
    show pi1DiagVal (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
        (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i.val
      = Complex.exp (((pi1AVal i.val * α + pi1BVal i.val * β : ℤ) : ℂ) * ((t : ℂ) * Complex.I))
    rw [hD, hA, hB]; simp
  · by_cases h8' : i.val = 8
    · have hD : pi1DiagVal (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
          (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i.val
          = Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)) := by
        unfold pi1DiagVal
        rw [if_neg h8, if_pos h8']
      have hA : pi1AVal i.val = 1 := by
        unfold pi1AVal
        rw [if_neg h8, if_pos h8']
      have hB : pi1BVal i.val = 0 := by
        unfold pi1BVal
        rw [if_neg h8, if_pos h8']
      show pi1DiagVal (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
          (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i.val
        = Complex.exp (((pi1AVal i.val * α + pi1BVal i.val * β : ℤ) : ℂ) * ((t : ℂ) * Complex.I))
      rw [hD, hA, hB]
      congr 1
      push_cast
      ring
    · by_cases h9 : i.val = 9
      · have hD : pi1DiagVal (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
            (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i.val
            = star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))) := by
          unfold pi1DiagVal
          rw [if_neg h8, if_neg h8', if_pos h9]
        have hA : pi1AVal i.val = -1 := by
          unfold pi1AVal
          rw [if_neg h8, if_neg h8', if_pos h9]
        have hB : pi1BVal i.val = 0 := by
          unfold pi1BVal
          rw [if_neg h8, if_neg h8', if_pos h9]
        show pi1DiagVal (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
            (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i.val
          = Complex.exp (((pi1AVal i.val * α + pi1BVal i.val * β : ℤ) : ℂ) * ((t : ℂ) * Complex.I))
        rw [hD, star_exp_int, hA, hB]
        congr 1
        push_cast
        ring
      · by_cases h16 : i.val < 16
        · by_cases hm : (i.val - 10) % 2 = 0
          · have hD : pi1DiagVal (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
                (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i.val
                = Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)) := by
              unfold pi1DiagVal
              rw [if_neg h8, if_neg h8', if_neg h9, if_pos h16, if_pos hm]
            have hA : pi1AVal i.val = 1 := by
              unfold pi1AVal
              rw [if_neg h8, if_neg h8', if_neg h9, if_pos h16, if_pos hm]
            have hB : pi1BVal i.val = 0 := by
              unfold pi1BVal
              rw [if_neg h8, if_neg h8', if_neg h9, if_pos h16]
            show pi1DiagVal (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
                (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i.val
              = Complex.exp (((pi1AVal i.val * α + pi1BVal i.val * β : ℤ) : ℂ) * ((t : ℂ) * Complex.I))
            rw [hD, hA, hB]
            congr 1
            push_cast
            ring
          · have hD : pi1DiagVal (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
                (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i.val
                = star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))) := by
              unfold pi1DiagVal
              rw [if_neg h8, if_neg h8', if_neg h9, if_pos h16, if_neg hm]
            have hA : pi1AVal i.val = -1 := by
              unfold pi1AVal
              rw [if_neg h8, if_neg h8', if_neg h9, if_pos h16, if_neg hm]
            have hB : pi1BVal i.val = 0 := by
              unfold pi1BVal
              rw [if_neg h8, if_neg h8', if_neg h9, if_pos h16]
            show pi1DiagVal (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
                (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i.val
              = Complex.exp (((pi1AVal i.val * α + pi1BVal i.val * β : ℤ) : ℂ) * ((t : ℂ) * Complex.I))
            rw [hD, star_exp_int, hA, hB]
            congr 1
            push_cast
            ring
        · by_cases h18 : i.val < 18
          · have hD : pi1DiagVal (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
                (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i.val
                = star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))) := by
              unfold pi1DiagVal
              rw [if_neg h8, if_neg h8', if_neg h9, if_neg h16, if_pos h18]
            have hA : pi1AVal i.val = -1 := by
              unfold pi1AVal
              rw [if_neg h8, if_neg h8', if_neg h9, if_neg h16, if_pos h18]
            have hB : pi1BVal i.val = 0 := by
              unfold pi1BVal
              rw [if_neg h8, if_neg h8', if_neg h9, if_neg h16, if_pos h18]
            show pi1DiagVal (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
                (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i.val
              = Complex.exp (((pi1AVal i.val * α + pi1BVal i.val * β : ℤ) : ℂ) * ((t : ℂ) * Complex.I))
            rw [hD, star_exp_int, hA, hB]
            congr 1
            push_cast
            ring
          · by_cases h24 : i.val < 24
            · have hD : pi1DiagVal (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
                  (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i.val
                  = star (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) := by
                unfold pi1DiagVal
                rw [if_neg h8, if_neg h8', if_neg h9, if_neg h16,
                  if_neg h18, if_pos h24]
              have hA : pi1AVal i.val = 0 := by
                unfold pi1AVal
                rw [if_neg h8, if_neg h8', if_neg h9, if_neg h16,
                  if_neg h18, if_pos h24]
              have hB : pi1BVal i.val = -1 := by
                unfold pi1BVal
                rw [if_neg h8, if_neg h8', if_neg h9, if_neg h16,
                  if_neg h18, if_pos h24]
              show pi1DiagVal (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
                  (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i.val
                = Complex.exp (((pi1AVal i.val * α + pi1BVal i.val * β : ℤ) : ℂ) * ((t : ℂ) * Complex.I))
              rw [hD, star_exp_int, hA, hB]
              congr 1
              push_cast
              ring
            · by_cases h26 : i.val < 26
              · have hD : pi1DiagVal (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
                    (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i.val
                    = star (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I))) := by
                  unfold pi1DiagVal
                  rw [if_neg h8, if_neg h8', if_neg h9, if_neg h16,
                    if_neg h18, if_neg h24, if_pos h26]
                have hA : pi1AVal i.val = -1 := by
                  unfold pi1AVal
                  rw [if_neg h8, if_neg h8', if_neg h9, if_neg h16,
                    if_neg h18, if_neg h24, if_pos h26]
                have hB : pi1BVal i.val = 0 := by
                  unfold pi1BVal
                  rw [if_neg h8, if_neg h8', if_neg h9, if_neg h16,
                    if_neg h18, if_neg h24, if_pos h26]
                show pi1DiagVal (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
                    (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i.val
                  = Complex.exp (((pi1AVal i.val * α + pi1BVal i.val * β : ℤ) : ℂ) * ((t : ℂ) * Complex.I))
                rw [hD, star_exp_int, hA, hB]
                congr 1
                push_cast
                ring
              · have hD : pi1DiagVal (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
                    (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i.val
                    = star (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) := by
                  unfold pi1DiagVal
                  rw [if_neg h8, if_neg h8', if_neg h9, if_neg h16,
                    if_neg h18, if_neg h24, if_neg h26]
                have hA : pi1AVal i.val = 0 := by
                  unfold pi1AVal
                  rw [if_neg h8, if_neg h8', if_neg h9, if_neg h16,
                    if_neg h18, if_neg h24, if_neg h26]
                have hB : pi1BVal i.val = -1 := by
                  unfold pi1BVal
                  rw [if_neg h8, if_neg h8', if_neg h9, if_neg h16,
                    if_neg h18, if_neg h24, if_neg h26]
                show pi1DiagVal (Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)))
                    (Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I))) i.val
                  = Complex.exp (((pi1AVal i.val * α + pi1BVal i.val * β : ℤ) : ℂ) * ((t : ℂ) * Complex.I))
                rw [hD, star_exp_int, hA, hB]
                congr 1
                push_cast
                ring

/-- The two-parameter circle subgroup of `AF`. -/
noncomputable def u1ParamGen (α β : ℤ) (t : ℝ) : AF :=
  ⟨Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)), 1,
    Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I)) • (1 : Matrix I3 I3 ℂ)⟩

/-- The candidate surviving generator: `(α, β) = (3, -1)` — π₀'s ℂ seat
unchanged, the M₃ seat INVERTED. -/
noncomputable def u1ParamB (t : ℝ) : AF :=
  ⟨Complex.exp (3 * (t : ℂ) * Complex.I), 1,
    Complex.exp (-((t : ℂ) * Complex.I)) • (1 : Matrix I3 I3 ℂ)⟩

/-- `u1ParamB` is the `(3, -1)` point of the two-parameter family. -/
theorem u1ParamB_eq_gen (t : ℝ) : u1ParamB t = u1ParamGen 3 (-1) t := by
  unfold u1ParamB u1ParamGen
  congr 1
  · congr 1
    push_cast
    ring
  · congr 1
    congr 1
    push_cast
    ring

/-- **The determinant along the two-parameter family**:
`det π₁(u1ParamGen α β t) = exp ((-4α - 12β) · t · i)`. -/
theorem pi1_det_gen (α β : ℤ) (t : ℝ) :
    (pi1 (u1ParamGen α β t)).det
      = Complex.exp (((-4 * α + -12 * β : ℤ) : ℂ) *
          ((t : ℂ) * Complex.I)) := by
  have hU : u1ParamGen α β t
      = ⟨Complex.exp ((α : ℂ) * ((t : ℂ) * Complex.I)), 1,
        Complex.exp ((β : ℂ) * ((t : ℂ) * Complex.I)) •
          (1 : Matrix I3 I3 ℂ)⟩ := rfl
  have hsum : ∑ i : I32, (pi1AVal i.val * α + pi1BVal i.val * β)
      = -4 * α + -12 * β := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      sum_A, sum_B]
  rw [hU, pi1_eq_diagonal, Matrix.det_diagonal,
    Finset.prod_congr rfl (fun i _ => pi1Diag_exp_gen α β t i),
    ← Complex.exp_sum, ← Finset.sum_mul, ← Int.cast_sum, hsum]

/-- **T3 (unimodularity)** — `π₁ (u1ParamB t)` is unimodular: the
re-derived lift is determinant-one along `(3, -1)`. -/
theorem pi1_det_unimodular (t : ℝ) : (pi1 (u1ParamB t)).det = 1 := by
  have h0 : (-4 * (3 : ℤ) + -12 * (-1) : ℤ) = 0 := rfl
  rw [u1ParamB_eq_gen, pi1_det_gen, h0, Int.cast_zero, zero_mul,
    Complex.exp_zero]

/-- **The surviving direction is unique up to scale**: unimodularity
for all `t` forces `α = -3β`. Combined with `pi1_det_unimodular`, the
unimodular directions are exactly the multiples of `(3, -1)`. -/
theorem pi1_unimodular_direction (α β : ℤ)
    (h : ∀ t : ℝ, (pi1 (u1ParamGen α β t)).det = 1) : α = -3 * β := by
  by_contra hne
  have hw : (-4 * α + -12 * β : ℤ) ≠ 0 := by
    intro hz
    apply hne
    omega
  have hwR : ((-4 * α + -12 * β : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hw
  have hwC : (((-4 * α + -12 * β : ℤ)) : ℂ) ≠ 0 := by exact_mod_cast hw
  set s : ℝ := Real.pi / (2 * ((-4 * α + -12 * β : ℤ) : ℝ)) with hs
  have h1 := h s
  rw [pi1_det_gen] at h1
  have hE : (((-4 * α + -12 * β : ℤ) : ℂ)) * ((s : ℂ) * Complex.I)
      = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    rw [hs]
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_intCast]
    field_simp
  rw [hE] at h1
  have h2 := congrArg Complex.re h1
  rw [Complex.one_re, Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_two]
    at h2
  exact zero_ne_one h2

/-- `piOp` sends a diagonal matrix to the diagonal of partner-shifted
entries (the corpus's `J`-conjugation on diagonals). -/
theorem piOp_diagonal (w : I32 → ℂ) :
    piOp (Matrix.diagonal w) = Matrix.diagonal (fun i => w (partner i)) := by
  ext i j
  rw [piOp_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, Matrix.diagonal_apply_eq]
  · have hne : partner j ≠ partner i := by
      intro hh
      apply hij
      have h2 := congrArg partner hh
      rw [partner_involutive, partner_involutive] at h2
      exact h2.symm
    rw [if_neg hne, Matrix.diagonal_apply, if_neg hij]

/-- **T3 (the pattern)** — for every fermion sector `f`, the lifted
eigenvalue of the surviving generator `u1ParamB` on `f` is
`exp (3 · t · i · Y f)`: the ratios are EXACTLY the landed hypercharge
table's, with normalization 3 — re-earned for π₁ along its own
surviving direction `(3, -1)`. -/

theorem pi1_hypercharge_pattern (f : SMFermion) (t : ℝ) :
    (pi1 (u1ParamB t) * piOp (pi1 (u1ParamB t)))
        (fermionIndex f 0) (fermionIndex f 0)
      = Complex.exp (3 * (t : ℂ) * Complex.I * (hypercharge f : ℂ)) := by
  have hU : u1ParamB t = ⟨Complex.exp (3 * (t : ℂ) * Complex.I), 1,
      Complex.exp (-((t : ℂ) * Complex.I)) • (1 : Matrix I3 I3 ℂ)⟩ := rfl
  cases f
  · -- ν_L: Y = -1, lifted weight -3
    have hs : fermionIndex SMFermion.nuL (0 : Fin 3) = ⟨0, by omega⟩ := rfl
    have hp : partner (⟨0, by omega⟩ : I32) = ⟨16, by omega⟩ := by
      apply Fin.ext
      simp [partner_val_eq]
    have dA : pi1Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp (-((t : ℂ) * Complex.I))) ⟨0, by omega⟩ = 1 := by
      show pi1DiagVal _ _ 0 = 1
      unfold pi1DiagVal
      rw [if_pos (by norm_num)]
    have dB : pi1Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp (-((t : ℂ) * Complex.I))) ⟨16, by omega⟩
        = star (Complex.exp (3 * (t : ℂ) * Complex.I)) := by
      show pi1DiagVal _ _ 16 = star (Complex.exp (3 * (t : ℂ) * Complex.I))
      unfold pi1DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_pos (by norm_num)]
    have hY : hypercharge SMFermion.nuL = -1 := rfl
    rw [hs, hU, pi1_eq_diagonal, piOp_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq, hp]
    rw [dA, dB, star_exp_three,
      one_mul, hY]
    congr 1
    push_cast
    ring
  · -- e_L: Y = -1, lifted weight -3
    have hs : fermionIndex SMFermion.eL (0 : Fin 3) = ⟨1, by omega⟩ := rfl
    have hp : partner (⟨1, by omega⟩ : I32) = ⟨17, by omega⟩ := by
      apply Fin.ext
      simp [partner_val_eq]
    have dA : pi1Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp (-((t : ℂ) * Complex.I))) ⟨1, by omega⟩ = 1 := by
      show pi1DiagVal _ _ 1 = 1
      unfold pi1DiagVal
      rw [if_pos (by norm_num)]
    have dB : pi1Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp (-((t : ℂ) * Complex.I))) ⟨17, by omega⟩
        = star (Complex.exp (3 * (t : ℂ) * Complex.I)) := by
      show pi1DiagVal _ _ 17 = star (Complex.exp (3 * (t : ℂ) * Complex.I))
      unfold pi1DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_pos (by norm_num)]
    have hY : hypercharge SMFermion.eL = -1 := rfl
    rw [hs, hU, pi1_eq_diagonal, piOp_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq, hp]
    rw [dA, dB, star_exp_three,
      one_mul, hY]
    congr 1
    push_cast
    ring
  · -- u_L: Y = 1/3, lifted weight 1
    have hs : fermionIndex SMFermion.uL (0 : Fin 3) = ⟨2, by omega⟩ := rfl
    have hp : partner (⟨2, by omega⟩ : I32) = ⟨18, by omega⟩ := by
      apply Fin.ext
      simp [partner_val_eq]
    have dA : pi1Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp (-((t : ℂ) * Complex.I))) ⟨2, by omega⟩ = 1 := by
      show pi1DiagVal _ _ 2 = 1
      unfold pi1DiagVal
      rw [if_pos (by norm_num)]
    have dB : pi1Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp (-((t : ℂ) * Complex.I))) ⟨18, by omega⟩
        = star (Complex.exp (-((t : ℂ) * Complex.I))) := by
      show pi1DiagVal _ _ 18 = star (Complex.exp (-((t : ℂ) * Complex.I)))
      unfold pi1DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num)]
    have hY : hypercharge SMFermion.uL = 1 / 3 := rfl
    rw [hs, hU, pi1_eq_diagonal, piOp_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq, hp]
    rw [dA, dB, star_exp_neg_one, one_mul, hY]
    congr 1
    push_cast
    ring
  · -- d_L: Y = 1/3, lifted weight 1
    have hs : fermionIndex SMFermion.dL (0 : Fin 3) = ⟨3, by omega⟩ := rfl
    have hp : partner (⟨3, by omega⟩ : I32) = ⟨19, by omega⟩ := by
      apply Fin.ext
      simp [partner_val_eq]
    have dA : pi1Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp (-((t : ℂ) * Complex.I))) ⟨3, by omega⟩ = 1 := by
      show pi1DiagVal _ _ 3 = 1
      unfold pi1DiagVal
      rw [if_pos (by norm_num)]
    have dB : pi1Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp (-((t : ℂ) * Complex.I))) ⟨19, by omega⟩
        = star (Complex.exp (-((t : ℂ) * Complex.I))) := by
      show pi1DiagVal _ _ 19 = star (Complex.exp (-((t : ℂ) * Complex.I)))
      unfold pi1DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num)]
    have hY : hypercharge SMFermion.dL = 1 / 3 := rfl
    rw [hs, hU, pi1_eq_diagonal, piOp_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq, hp]
    rw [dA, dB, star_exp_neg_one, one_mul, hY]
    congr 1
    push_cast
    ring
  · -- ν_R: Y = 0, lifted weight 0
    have hs : fermionIndex SMFermion.nuR (0 : Fin 3) = ⟨8, by omega⟩ := rfl
    have hp : partner (⟨8, by omega⟩ : I32) = ⟨24, by omega⟩ := by
      apply Fin.ext
      simp [partner_val_eq]
    have dA : pi1Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp (-((t : ℂ) * Complex.I))) ⟨8, by omega⟩
        = Complex.exp (3 * (t : ℂ) * Complex.I) := by
      show pi1DiagVal _ _ 8 = Complex.exp (3 * (t : ℂ) * Complex.I)
      unfold pi1DiagVal
      rw [if_neg (by norm_num), if_pos (by norm_num)]
    have dB : pi1Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp (-((t : ℂ) * Complex.I))) ⟨24, by omega⟩
        = star (Complex.exp (3 * (t : ℂ) * Complex.I)) := by
      show pi1DiagVal _ _ 24 = star (Complex.exp (3 * (t : ℂ) * Complex.I))
      unfold pi1DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_pos (by norm_num)]
    have hY : hypercharge SMFermion.nuR = 0 := rfl
    rw [hs, hU, pi1_eq_diagonal, piOp_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq, hp]
    rw [dA, dB, star_exp_three,       ← Complex.exp_add, hY]
    congr 1
    push_cast
    ring
  · -- e_R: Y = -2, lifted weight -6
    have hs : fermionIndex SMFermion.eR (0 : Fin 3) = ⟨9, by omega⟩ := rfl
    have hp : partner (⟨9, by omega⟩ : I32) = ⟨25, by omega⟩ := by
      apply Fin.ext
      simp [partner_val_eq]
    have dA : pi1Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp (-((t : ℂ) * Complex.I))) ⟨9, by omega⟩
        = star (Complex.exp (3 * (t : ℂ) * Complex.I)) := by
      show pi1DiagVal _ _ 9 = star (Complex.exp (3 * (t : ℂ) * Complex.I))
      unfold pi1DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num)]
    have dB : pi1Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp (-((t : ℂ) * Complex.I))) ⟨25, by omega⟩
        = star (Complex.exp (3 * (t : ℂ) * Complex.I)) := by
      show pi1DiagVal _ _ 25 = star (Complex.exp (3 * (t : ℂ) * Complex.I))
      unfold pi1DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_pos (by norm_num)]
    have hY : hypercharge SMFermion.eR = -2 := rfl
    rw [hs, hU, pi1_eq_diagonal, piOp_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq, hp]
    rw [dA, dB, star_exp_three,       ← Complex.exp_add, hY]
    congr 1
    push_cast
    ring
  · -- u_R: Y = 4/3, lifted weight 4
    have hs : fermionIndex SMFermion.uR (0 : Fin 3) = ⟨10, by omega⟩ := rfl
    have hp : partner (⟨10, by omega⟩ : I32) = ⟨26, by omega⟩ := by
      apply Fin.ext
      simp [partner_val_eq]
    have dA : pi1Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp (-((t : ℂ) * Complex.I))) ⟨10, by omega⟩
        = Complex.exp (3 * (t : ℂ) * Complex.I) := by
      show pi1DiagVal _ _ 10 = Complex.exp (3 * (t : ℂ) * Complex.I)
      unfold pi1DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_pos (by norm_num), if_pos (by norm_num)]
    have dB : pi1Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp (-((t : ℂ) * Complex.I))) ⟨26, by omega⟩
        = star (Complex.exp (-((t : ℂ) * Complex.I))) := by
      show pi1DiagVal _ _ 26 = star (Complex.exp (-((t : ℂ) * Complex.I)))
      unfold pi1DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num)]
    have hY : hypercharge SMFermion.uR = 4 / 3 := rfl
    rw [hs, hU, pi1_eq_diagonal, piOp_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq, hp]
    rw [dA, dB, star_exp_neg_one,
      ← Complex.exp_add, hY]
    congr 1
    push_cast
    ring
  · -- d_R: Y = -2/3, lifted weight -2
    have hs : fermionIndex SMFermion.dR (0 : Fin 3) = ⟨11, by omega⟩ := rfl
    have hp : partner (⟨11, by omega⟩ : I32) = ⟨27, by omega⟩ := by
      apply Fin.ext
      simp [partner_val_eq]
    have dA : pi1Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp (-((t : ℂ) * Complex.I))) ⟨11, by omega⟩
        = star (Complex.exp (3 * (t : ℂ) * Complex.I)) := by
      show pi1DiagVal _ _ 11 = star (Complex.exp (3 * (t : ℂ) * Complex.I))
      unfold pi1DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_pos (by norm_num), if_neg (by norm_num)]
    have dB : pi1Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp (-((t : ℂ) * Complex.I))) ⟨27, by omega⟩
        = star (Complex.exp (-((t : ℂ) * Complex.I))) := by
      show pi1DiagVal _ _ 27 = star (Complex.exp (-((t : ℂ) * Complex.I)))
      unfold pi1DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num)]
    have hY : hypercharge SMFermion.dR = -2 / 3 := rfl
    rw [hs, hU, pi1_eq_diagonal, piOp_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq, hp]
    rw [dA, dB, star_exp_three, star_exp_neg_one,
      ← Complex.exp_add, hY]
    congr 1
    push_cast
    ring

/-! ## §10. T6 — the package verdict

Everything above, assembled into one statement: the single
representation π₁ carries faithfulness, the representation laws,
grading-evenness, unimodularity and the exact hypercharge pattern
along its own surviving direction `(3, -1)`, order-zero against its
own J-opposite ρ₁°, first-order against the landed `DF_oneGen`
(unmodified, K-RB1), and the landed J-compatibility of `DF_oneGen` —
together, at T1. That is the charter's closure condition, and the
loud statement's fixed trigger (K-RB3). -/

/-- The Track 1 closure package for Route B, as a single proposition:
faithfulness + full unital `*`-representation laws + grading +
unimodularity + hypercharge pattern + order-zero + first-order +
`D_F`'s J-compatibility, all for the one representation π₁. -/
def track1_package_statement : Prop :=
  (∀ a : AF, pi1 a = 0 ↔ a = afZero)
  ∧ (∀ a b : AF, pi1 (afMul a b) = pi1 a * pi1 b)
  ∧ (∀ a b : AF, pi1 (afAdd a b) = pi1 a + pi1 b)
  ∧ (∀ a : AF, pi1 (afStar a) = (pi1 a)ᴴ)
  ∧ pi1 afOne = 1
  ∧ (∀ a : AF, gammaF * pi1 a = pi1 a * gammaF)
  ∧ (∀ t : ℝ, (pi1 (u1ParamB t)).det = 1)
  ∧ (∀ (f : SMFermion) (t : ℝ),
      (pi1 (u1ParamB t) * piOp (pi1 (u1ParamB t)))
          (fermionIndex f 0) (fermionIndex f 0)
        = Complex.exp (3 * (t : ℂ) * Complex.I * (hypercharge f : ℂ)))
  ∧ (∀ a b : AF, pi1 a * rho1 b = rho1 b * pi1 a)
  ∧ (∀ (Ynu Ye Yu Yd : ℝ) (a b : AF) (i j : I32),
      ((DF_oneGen Ynu Ye Yu Yd * pi1 a - pi1 a * DF_oneGen Ynu Ye Yu Yd)
          * rho1 b
        - rho1 b * (DF_oneGen Ynu Ye Yu Yd * pi1 a
          - pi1 a * DF_oneGen Ynu Ye Yu Yd)) i j = 0)
  ∧ (∀ (Ynu Ye Yu Yd : ℝ),
      UJ * (DF_oneGen Ynu Ye Yu Yd).map (star : ℂ → ℂ) * UJ
        = DF_oneGen Ynu Ye Yu Yd)

/-- **T6 — THE PACKAGE STANDS (Route B)**: every component is a
headline theorem of this module (§§3–9) or a landed theorem cited
unmodified (`DF_oneGen_J_compat`, Track1Closure). -/
theorem track1_package_routeB : track1_package_statement :=
  ⟨pi1_ker_iff, pi1_afMul, pi1_afAdd, pi1_afStar, pi1_one,
    pi1_grading_even, pi1_det_unimodular, pi1_hypercharge_pattern,
    pi1_order_zero, pi1_first_order, DF_oneGen_J_compat⟩

/-- **TRACK 1 CLOSES via Route B.** In the loud statement's fixed
terms (Jeff, 2026-10-23): one representation — π₁ — carries
faithfulness + hypercharge ratios + spectral-triple compatibilities
together at T1, via the multiplicative species on a changed seat
assignment (the route the landed additivity-incompatibility left
open). The statement is exactly `track1_package_statement`. -/
theorem track1_closes_routeB : track1_package_statement :=
  track1_package_routeB

end ThetLogos.Track1RouteB
