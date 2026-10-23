/-
# ThetLogos.PreOptionARepresentation — the pre-Option-A representation (the hypercharge seat)

STATUS: LANDED 2026-10-23 by parent review — targeted in-tree build
green on the shipped text, strict recount, placeholder census,
`#print axioms` standard-only on the headline declarations.
Per-target verdicts: T1 PARTIAL (obstruction proved), T2 STANDS,
T3 STANDS (sector form, forced exception proved), T4 STANDS
(stated form). Charter:
`whitepaper/pre-option-a-representation-scoping-2026-10-22.md`;
dossier: `whitepaper/pre-option-a-representation-2026-10-23.md`.

**NO CLAIM.** This module is finite representation theory only. It constructs a
candidate "pre-Option-A" representation `pi0` of the finite algebra
`AF = ℂ ⊕ ℍ ⊕ M₃(ℂ)` (`SMAlgebra`, landed in `FiniteSpectralTriple`) on the
corpus's finite Hilbert space `I32 = Fin 32`, and settles the four
pre-registered targets of the scoping charter
(`whitepaper/pre-option-a-representation-scoping-2026-10-22.md`). It does not
derive the Standard Model, and it changes no landed verdict: SM-Match Track 1's
verdicts change only if and when this candidate is landed by review (K-PA3).

## Why this brick exists

Option A (`pi`, landed) has two proved defects as a candidate physical
representation: `pi_ker_iff` (SMGaugeAlgebra) — the kernel of `pi` is exactly
the pure-color part, so `M₃(ℂ)` acts only locked inside the quark blocks; and
`pi_u1_eL_trivial` — the represented U(1) acts trivially on the left-handed
electron while the (T2) hypercharge table says `Y(e_L) = −1`. The represented
U(1) of Option A is therefore *not* hypercharge: the hypercharge seat is
empty. This brick builds the pre-Option-A representation `pi0` — the natural
representation before Option A pinned the color action into the quark blocks —
and tests whether the seat can be occupied.

## The representation (what pi0 is)

For `a = ⟨λ, q, m⟩ : AF`, `pi0 a` is block-diagonal over the four 8-dimensional
sectors of `I32` (H_L = 0–7, H_R = 8–15, H_L^c = 16–23, H_R^c = 24–31):

* H_L particles: `q` on the lepton doublet (0,1); `q ⊗ I₃` on the quark
  doublets (2–7) — the ℍ summand alone.
* H_R particles: `λ` on ν_R (8); `λ̄` on e_R (9); on the right quarks (10–15)
  the diagonal ℂ-action `λ` on the up slots, `λ̄` on the down slots — the
  ℂ summand alone (Option A's formula with the color factor removed).
* H_L antiparticles: `λ̄ • q̄` (entrywise conjugate) on the antilepton doublet
  (16,17); `q̄ ⊗ m` on the antiquark doublets (18–23).
* H_R antiparticles: `λ̄` on both antilepton singlets (24, 25); `m` alone,
  flavour-diagonally, on the right antiquarks (26–31) — pure color, naked:
  the exact contrast with `pi_ker_iff`.

## Verdicts on the pre-registered targets

* **T1 — PARTIAL, with the obstruction proved.** `pi0` is a representation of
  the *multiplicative* structure of `AF`: `pi0_one`, `pi0_afMul`,
  `pi0_afStar` are proved (the same species of representation as the corpus's
  own `pi`, which is likewise multiplicative and unital but not additive).
  `pi0` is grading-even (`pi0_grading_even`, w.r.t. the landed `gammaF`) and
  `pi0` is *not* additive — and this is forced, not a defect of the
  construction: `additive_rep_u1_eL_trivial` proves that **every** additive
  algebra representation of `AF` whose ℍ summand acts as `q` on the H_L
  doublets has `ρ(⟨λ,1,1⟩)` acting as the identity at the e_L particle entry —
  the annihilation argument (summands of a direct-sum algebra annihilate each
  other, so the ℂ summand cannot reach any slot the ℍ summand acts on).
  Additivity and the hypercharge pattern are incompatible; the seat can only
  be occupied by a multiplicative (group) representation. Additionally,
  order-zero w.r.t. the corpus's `piOp` **fails** for `pi0`
  (`pi0_order_zero_fails`, with an explicit counterexample) — the corpus's
  first-order / OrderOneHolds machinery, which is built on `pi` and on the
  Martinetti generators, does **not** port to `pi0`. First-order for `pi0` is
  not attempted.
* **T2 — STANDS.** `pi0_ker_iff`: `pi0 a = 0 ↔ a = 0` componentwise. In
  particular pure color acts nontrivially (`pi0_pure_color_entry`:
  the right-antiquark entries of `pi0 ⟨0,0,m⟩` are exactly `m`'s entries;
  `pi0_pure_color_ne_zero`), against `pi_pure_color_zero` for Option A.
* **T3 — STANDS in the sector form, with the forced exception proved.**
  The e_L *sector* of `I32` is the pair of slots {1, 17} (particle and
  antiparticle). `pi0 ⟨λ,1,1⟩` acts there as `diag(1, λ̄)`
  (`pi0_u1_eL_particle_entry`, `pi0_u1_eL_antiparticle_entry`): nontrivial —
  the Option-A obstruction (which was triviality on the whole of `I32`,
  including vanishing on the antiparticle half) is gone. The particle entry
  itself remains `1`, and `additive_rep_u1_eL_trivial` shows why no additive
  representation can do better there; for `pi0` the charge reaches the sector
  through its antiparticle half.
* **T4 — STANDS, in the stated form.** The hypercharge table is *imported at
  sector level* from `SMFermions.hypercharge` (T2 input, cited — K-PA2): the
  claim proved is (representation + unimodularity) ⇒ ratios. The one-parameter
  family `u1Param t = ⟨e^{3it}, 1, e^{it} • 1⟩` is unimodular as a `pi0`
  operator (`pi0_det_unimodular`: `det (pi0 (u1Param t)) = 1`, by the finite
  weight sum `−4·3 + 12·1 = 0`); the direction (3,1) is the one the
  unimodularity condition `det = 1` selects (the total (ℓ, μ) weight of
  `pi0 (a)` over `I32` is `−4α + 12β` for a direction `(α, β)` — read off the
  diagonal weights in `pi0Diag`). The lifted gauge action
  `pi0 u * piOp (pi0 u)` — the corpus's gauge action form, cf.
  InnerFluctuations — is diagonal, and at every one-generation sector slot its
  entry is exactly `exp (3 · it · Y_f)` (`pi0_hypercharge_pattern`): the
  surviving U(1) generator's sector eigenvalues are `3 · Y_f` — proportional
  to the Standard Model hypercharges with **one** overall normalization (the
  factor 3, fixed by the unimodularity direction, not chosen per sector).
  Ratios equal; no deviation.

## Fences (on the face)

* **K-PA1** Finite representation theory only: no continuum, no dynamics, no
  manifold factor. Nothing here touches Stage 3c / Stage 4.
* **K-PA2** Hypercharge values remain T2-cited inputs (`SMFermions.hypercharge`,
  SMGaugeAlgebra §2b): T4 proves the *ratios* follow from `pi0` +
  unimodularity; it does not derive the table from nothing. Masses, couplings
  and the three-generation triplication are untouched inputs, exactly as
  before. This module does not derive the Standard Model.
* **K-PA3** SM-Match verdicts (and every other landed verdict) change only on
  landing of this candidate by the parent review — not by this file's
  existence.

Tier map: the construction and all theorems are T1 (proved here, standard
axioms only) once built; the hypercharge table they are checked against is T2
(input, cited). The reading "the hypercharge seat is occupied by pi0" is the
charter's T4 statement in its stated form — it is a statement about the finite
representation, not about continuum physics.
-/

import Mathlib.Tactic
import ThetLogos.FiniteSpectralTriple
import ThetLogos.SMGaugeAlgebra
import ThetLogos.SMFermions

open Matrix Complex

namespace ThetLogos.PreOptionARepresentation

/-- Index type of the finite Hilbert space (as in FiniteSpectralTriple). -/
abbrev I32 := Fin 32

/-- Index type for SU(2) doublets. -/
abbrev I2 := Fin 2

/-- Index type for color triplets. -/
abbrev I3 := Fin 3

/-! ## §0. Componentwise operations on AF

`SMAlgebra` carries no `Mul`/`Add`/`Star` instances in the corpus; the
representation statements are made against these componentwise operations,
which are exactly the ones the corpus's landed results use when they speak of
products and adjoints of algebra elements (cf. `SMUnitaryGroup`,
`pi_mul`-style statements for `pi`). -/

/-- Componentwise multiplication on `AF = ℂ ⊕ ℍ ⊕ M₃(ℂ)`. -/
def afMul (a b : AF) : AF := ⟨a.u1 * b.u1, a.q * b.q, a.color * b.color⟩

/-- Componentwise addition on `AF`. -/
def afAdd (a b : AF) : AF := ⟨a.u1 + b.u1, a.q + b.q, a.color + b.color⟩

/-- Componentwise star on `AF`: conjugate on ℂ, conjugate-transpose on the
matrix summands. -/
def afStar (a : AF) : AF := ⟨star a.u1, a.q.conjTranspose, a.color.conjTranspose⟩

/-- The unit element of `AF`. -/
def afOne : AF := ⟨1, 1, 1⟩

/-- The zero element of `AF`. -/
def afZero : AF := ⟨0, 0, 0⟩

@[simp] theorem afMul_u1 (a b : AF) : (afMul a b).u1 = a.u1 * b.u1 := rfl
@[simp] theorem afMul_q (a b : AF) : (afMul a b).q = a.q * b.q := rfl
@[simp] theorem afMul_color (a b : AF) : (afMul a b).color = a.color * b.color := rfl
@[simp] theorem afAdd_u1 (a b : AF) : (afAdd a b).u1 = a.u1 + b.u1 := rfl
@[simp] theorem afAdd_q (a b : AF) : (afAdd a b).q = a.q + b.q := rfl
@[simp] theorem afAdd_color (a b : AF) : (afAdd a b).color = a.color + b.color := rfl
@[simp] theorem afStar_u1 (a : AF) : (afStar a).u1 = star a.u1 := rfl
@[simp] theorem afStar_q (a : AF) : (afStar a).q = a.q.conjTranspose := rfl
@[simp] theorem afStar_color (a : AF) : (afStar a).color = a.color.conjTranspose := rfl

theorem ext_iff {a b : AF} : a = b ↔ a.u1 = b.u1 ∧ a.q = b.q ∧ a.color = b.color := by
  constructor
  · intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨u1, q, color⟩ := a
    obtain ⟨u1', q', color'⟩ := b
    simp only [SMAlgebra.mk.injEq] at *
    exact ⟨h1, h2, h3⟩

/-! ## §1. The pre-Option-A representation

Slot-wise definition, in the style of the landed `embedSM` (named branch
hypotheses, `let`-bound doublet/color indices). On a 6-dimensional quark
block starting at `base`, `iso = (iv - base) % 2` is the doublet (flavour)
index and `col = (iv - base) / 2` is the color index. -/

/-- **The pre-Option-A representation** `pi0 : AF → Mat₃₂(ℂ)`.

Block formulas (see the module header for the sector table): ℍ alone on the
H_L doublets (`q` on leptons, `q ⊗ I₃` on quarks); ℂ alone on the H_R slots
(`λ`, `λ̄`, and the flavour-split diagonal `λ`/`λ̄` on right quarks); on the
antiparticle half the conjugate-flavoured blocks `λ̄ • q̄` (antileptons),
`q̄ ⊗ m` (left antiquarks), `λ̄` (right antileptons), and `m` alone on the
right antiquarks. -/
def pi0 (a : AF) : Matrix I32 I32 ℂ := fun i j =>
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
      star a.u1 * star (a.q ⟨iv - 16, by omega⟩ ⟨jv - 16, by omega⟩)
    else if h_q : 18 ≤ iv ∧ 18 ≤ jv then
      let iso_i : Fin 2 := ⟨(iv - 18) % 2, Nat.mod_lt _ (by norm_num)⟩
      let iso_j : Fin 2 := ⟨(jv - 18) % 2, Nat.mod_lt _ (by norm_num)⟩
      let col_i : Fin 3 := ⟨(iv - 18) / 2, by omega⟩
      let col_j : Fin 3 := ⟨(jv - 18) / 2, by omega⟩
      star (a.q iso_i iso_j) * a.color col_i col_j
    else 0
  else if hRc : 24 ≤ iv ∧ 24 ≤ jv then
    if h1 : iv = 24 ∧ jv = 24 then star a.u1
    else if h2 : iv = 25 ∧ jv = 25 then star a.u1
    else if h_q : 26 ≤ iv ∧ 26 ≤ jv then
      let iso_i : Fin 2 := ⟨(iv - 26) % 2, Nat.mod_lt _ (by norm_num)⟩
      let iso_j : Fin 2 := ⟨(jv - 26) % 2, Nat.mod_lt _ (by norm_num)⟩
      let col_i : Fin 3 := ⟨(iv - 26) / 2, by omega⟩
      let col_j : Fin 3 := ⟨(jv - 26) / 2, by omega⟩
      if iso_i = iso_j then a.color col_i col_j else 0
    else 0
  else 0

/-! ## §2. Entry lemmas

Parameterized entry formulas, in the style of `SMGaugeAlgebra`'s `pi_entry_*`:
one-generation slots are addressed by (color, flavour) index pairs
`base + 2 * color + flavour`. Then the vanishing lemmas: cross-sector,
and mixed inside a sector. -/

/-- Entry on the H_L lepton doublet: the quaternion alone. -/
theorem pi0_entry_leptonL (a : AF) (s t : Fin 2) :
    pi0 a ⟨s.val, by omega⟩ ⟨t.val, by omega⟩ = a.q s t := by
  have hL : s.val < 8 ∧ t.val < 8 := by omega
  have h_l : s.val < 2 ∧ t.val < 2 := by omega
  have hsi : (⟨s.val, by omega⟩ : Fin 2) = s := Fin.eta s _
  have hti : (⟨t.val, by omega⟩ : Fin 2) = t := Fin.eta t _
  unfold pi0
  dsimp only
  simp only [hL, h_l, true_and, and_true, dite_true, hsi, hti]

/-- Entry on the H_L quark block: `q` tensor the color identity. -/
theorem pi0_entry_quarkL (a : AF) (k l : Fin 3) (s t : Fin 2) :
    pi0 a ⟨2 + 2 * k.val + s.val, by omega⟩ ⟨2 + 2 * l.val + t.val, by omega⟩
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
  unfold pi0
  dsimp only
  simp only [hL, hnl, hq, true_and, and_true, dite_true, dite_false, hmod1, hmod2,
    hdiv1, hdiv2, hsi, hti, hki, hli, Fin.mk.injEq]

/-- Entry at ν_R: the λ action. -/
theorem pi0_entry_nuR (a : AF) : pi0 a ⟨8, by omega⟩ ⟨8, by omega⟩ = a.u1 := by
  have hnL : ¬ ((8:ℕ) < 8 ∧ (8:ℕ) < 8) := by omega
  have hR : 8 ≤ (8:ℕ) ∧ (8:ℕ) < 16 ∧ 8 ≤ (8:ℕ) ∧ (8:ℕ) < 16 := by omega
  have h1 : (8:ℕ) = 8 ∧ (8:ℕ) = 8 := by omega
  unfold pi0
  dsimp only
  simp only [hnL, hR, h1, true_and, and_true, dite_true, dite_false]

/-- Entry at e_R: the conjugate λ action. -/
theorem pi0_entry_eR (a : AF) : pi0 a ⟨9, by omega⟩ ⟨9, by omega⟩ = star a.u1 := by
  have hnL : ¬ ((9:ℕ) < 8 ∧ (9:ℕ) < 8) := by omega
  have hR : 8 ≤ (9:ℕ) ∧ (9:ℕ) < 16 ∧ 8 ≤ (9:ℕ) ∧ (9:ℕ) < 16 := by omega
  have hn1 : ¬ ((9:ℕ) = 8 ∧ (9:ℕ) = 8) := by omega
  have h2 : (9:ℕ) = 9 ∧ (9:ℕ) = 9 := by omega
  unfold pi0
  dsimp only
  simp only [hnL, hR, hn1, h2, true_and, and_true, dite_true, dite_false]

/-- Entry on the H_R quark block: the flavour-split diagonal ℂ action. -/
theorem pi0_entry_quarkR (a : AF) (k l : Fin 3) (s t : Fin 2) :
    pi0 a ⟨10 + 2 * k.val + s.val, by omega⟩ ⟨10 + 2 * l.val + t.val, by omega⟩
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
  unfold pi0
  dsimp only
  simp only [hnL, hR, hn1, hn2, hq, true_and, and_true, dite_true, dite_false, hmod1,
    hmod2, hdiv1, hdiv2, hsi, hti, hki, hli]

/-- Entry on the H_L antilepton doublet: `λ̄ • q̄` entrywise. -/
theorem pi0_entry_leptonLc (a : AF) (s t : Fin 2) :
    pi0 a ⟨16 + s.val, by omega⟩ ⟨16 + t.val, by omega⟩
      = star a.u1 * star (a.q s t) := by
  have hnL : ¬ ((16 + s.val) < 8 ∧ (16 + t.val) < 8) := by omega
  have hnR : ¬ (8 ≤ (16 + s.val) ∧ (16 + s.val) < 16 ∧ 8 ≤ (16 + t.val) ∧ (16 + t.val) < 16) := by omega
  have hLc : 16 ≤ (16 + s.val) ∧ (16 + s.val) < 24 ∧ 16 ≤ (16 + t.val) ∧ (16 + t.val) < 24 := by omega
  have h_l : (16 + s.val) < 18 ∧ (16 + t.val) < 18 := by omega
  have hsi : (⟨s.val, by omega⟩ : Fin 2) = s := Fin.eta s _
  have hti : (⟨t.val, by omega⟩ : Fin 2) = t := Fin.eta t _
  unfold pi0
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

/-- Entry on the H_L antiquark block: `q̄ ⊗ m`, no condition — the full tensor
product block. -/
theorem pi0_entry_quarkLc (a : AF) (k l : Fin 3) (s t : Fin 2) :
    pi0 a ⟨18 + 2 * k.val + s.val, by omega⟩ ⟨18 + 2 * l.val + t.val, by omega⟩
      = star (a.q s t) * a.color k l := by
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
  unfold pi0
  dsimp only
  simp only [hnL, hnR, hLc, hnl, hq, true_and, and_true, dite_true, dite_false,
    hmod1, hmod2, hdiv1, hdiv2, hsi, hti, hki, hli]

/-- Entry at the ν_R antiparticle singlet: `λ̄`. -/
theorem pi0_entry_nuRc (a : AF) : pi0 a ⟨24, by omega⟩ ⟨24, by omega⟩ = star a.u1 := by
  have hnL : ¬ ((24:ℕ) < 8 ∧ (24:ℕ) < 8) := by omega
  have hnR : ¬ (8 ≤ (24:ℕ) ∧ (24:ℕ) < 16 ∧ 8 ≤ (24:ℕ) ∧ (24:ℕ) < 16) := by omega
  have hnLc : ¬ (16 ≤ (24:ℕ) ∧ (24:ℕ) < 24 ∧ 16 ≤ (24:ℕ) ∧ (24:ℕ) < 24) := by omega
  have hRc : 24 ≤ (24:ℕ) ∧ 24 ≤ (24:ℕ) := by omega
  have h1 : (24:ℕ) = 24 ∧ (24:ℕ) = 24 := by omega
  unfold pi0
  dsimp only
  simp only [hnL, hnR, hnLc, hRc, h1, true_and, and_true, dite_true, dite_false]

/-- Entry at the e_R antiparticle singlet: `λ̄`. -/
theorem pi0_entry_eRc (a : AF) : pi0 a ⟨25, by omega⟩ ⟨25, by omega⟩ = star a.u1 := by
  have hnL : ¬ ((25:ℕ) < 8 ∧ (25:ℕ) < 8) := by omega
  have hnR : ¬ (8 ≤ (25:ℕ) ∧ (25:ℕ) < 16 ∧ 8 ≤ (25:ℕ) ∧ (25:ℕ) < 16) := by omega
  have hnLc : ¬ (16 ≤ (25:ℕ) ∧ (25:ℕ) < 24 ∧ 16 ≤ (25:ℕ) ∧ (25:ℕ) < 24) := by omega
  have hRc : 24 ≤ (25:ℕ) ∧ 24 ≤ (25:ℕ) := by omega
  have hn1 : ¬ ((25:ℕ) = 24 ∧ (25:ℕ) = 24) := by omega
  have h2 : (25:ℕ) = 25 ∧ (25:ℕ) = 25 := by omega
  unfold pi0
  dsimp only
  simp only [hnL, hnR, hnLc, hRc, hn1, h2, true_and, and_true, dite_true, dite_false]

/-- Entry on the H_R antiquark block: `m` alone, flavour-diagonally. -/
theorem pi0_entry_quarkRc (a : AF) (k l : Fin 3) (s t : Fin 2) :
    pi0 a ⟨26 + 2 * k.val + s.val, by omega⟩ ⟨26 + 2 * l.val + t.val, by omega⟩
      = if s = t then a.color k l else 0 := by
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
  have hki : (⟨k.val, by omega⟩ : Fin 3) = k := Fin.eta k _
  have hli : (⟨l.val, by omega⟩ : Fin 3) = l := Fin.eta l _
  unfold pi0
  dsimp only
  simp only [hnL, hnR, hnLc, hRc, hn1, hn2, hq, true_and, and_true, dite_true,
    dite_false, hmod1, hmod2, hdiv1, hdiv2, hki, hli]

/-! ### Vanishing lemmas

Cross-sector vanishing, and mixed vanishing inside each sector: `pi0` is
block-diagonal for the 10-block partition of `I32` (two sub-blocks per
8-sector, the right-handed singlets split off). -/

/-- Cross-sector vanishing: entries between different 8-dimensional sectors
are zero. -/
theorem pi0_entry_cross_sector (a : AF) {i j : I32}
    (h : i.val / 8 ≠ j.val / 8) : pi0 a i j = 0 := by
  have hi : i.val < 32 := i.isLt
  have hj : j.val < 32 := j.isLt
  have hnL : ¬ (i.val < 8 ∧ j.val < 8) := by omega
  have hnR : ¬ (8 ≤ i.val ∧ i.val < 16 ∧ 8 ≤ j.val ∧ j.val < 16) := by omega
  have hnLc : ¬ (16 ≤ i.val ∧ i.val < 24 ∧ 16 ≤ j.val ∧ j.val < 24) := by omega
  have hnRc : ¬ (24 ≤ i.val ∧ 24 ≤ j.val) := by omega
  unfold pi0
  dsimp only
  simp only [hnL, hnR, hnLc, hnRc, dite_false]

/-- Mixed vanishing in H_L: lepton row against quark column and vice versa. -/
theorem pi0_entry_HL_mixed (a : AF) {i j : I32}
    (h : (i.val < 2 ∧ 2 ≤ j.val ∧ j.val < 8) ∨ (2 ≤ i.val ∧ i.val < 8 ∧ j.val < 2)) :
    pi0 a i j = 0 := by
  have hL : i.val < 8 ∧ j.val < 8 := by omega
  have hnl : ¬ (i.val < 2 ∧ j.val < 2) := by omega
  have hnq : ¬ (2 ≤ i.val ∧ 2 ≤ j.val) := by omega
  unfold pi0
  dsimp only
  simp only [hL, hnl, hnq, true_and, and_true, dite_true, dite_false]

/-- Mixed vanishing in H_R: singlet against quark block, and ν_R against e_R. -/
theorem pi0_entry_HR_mixed (a : AF) {i j : I32}
    (h : (i.val = 8 ∧ j.val = 9) ∨ (i.val = 9 ∧ j.val = 8) ∨
         ((i.val = 8 ∨ i.val = 9) ∧ 10 ≤ j.val ∧ j.val < 16) ∨
         (10 ≤ i.val ∧ i.val < 16 ∧ (j.val = 8 ∨ j.val = 9))) :
    pi0 a i j = 0 := by
  have hnL : ¬ (i.val < 8 ∧ j.val < 8) := by omega
  have hR : 8 ≤ i.val ∧ i.val < 16 ∧ 8 ≤ j.val ∧ j.val < 16 := by omega
  have hn1 : ¬ (i.val = 8 ∧ j.val = 8) := by omega
  have hn2 : ¬ (i.val = 9 ∧ j.val = 9) := by omega
  have hnq : ¬ (10 ≤ i.val ∧ 10 ≤ j.val) := by omega
  unfold pi0
  dsimp only
  simp only [hnL, hR, hn1, hn2, hnq, true_and, and_true, dite_true, dite_false]

/-- Mixed vanishing in the antiparticle half: antilepton against antiquark,
the ν_R^c/e_R^c cross entries, and singlets against the right antiquarks. -/
theorem pi0_entry_Hc_mixed (a : AF) {i j : I32}
    (h : (16 ≤ i.val ∧ i.val < 18 ∧ 18 ≤ j.val ∧ j.val < 24) ∨
         (18 ≤ i.val ∧ i.val < 24 ∧ 16 ≤ j.val ∧ j.val < 18) ∨
         (i.val = 24 ∧ 26 ≤ j.val) ∨ (i.val = 25 ∧ 26 ≤ j.val) ∨
         (26 ≤ i.val ∧ j.val = 24) ∨ (26 ≤ i.val ∧ j.val = 25) ∨
         (i.val = 24 ∧ j.val = 25) ∨ (i.val = 25 ∧ j.val = 24)) :
    pi0 a i j = 0 := by
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
    unfold pi0
    simp only [hnL, hnR, hLc, hnl, hnq, true_and, and_true, dite_true, dite_false]
  · have hLc : 16 ≤ i.val ∧ i.val < 24 ∧ 16 ≤ j.val ∧ j.val < 24 := by omega
    have hnl : ¬ (i.val < 18 ∧ j.val < 18) := by omega
    have hnq : ¬ (18 ≤ i.val ∧ 18 ≤ j.val) := by omega
    unfold pi0
    simp only [hnL, hnR, hLc, hnl, hnq, true_and, and_true, dite_true, dite_false]
  all_goals
    have hnLc : ¬ (16 ≤ i.val ∧ i.val < 24 ∧ 16 ≤ j.val ∧ j.val < 24) := by omega
    have hRc : 24 ≤ i.val ∧ 24 ≤ j.val := by omega
    have hn1 : ¬ (i.val = 24 ∧ j.val = 24) := by omega
    have hn2 : ¬ (i.val = 25 ∧ j.val = 25) := by omega
    have hnq : ¬ (26 ≤ i.val ∧ 26 ≤ j.val) := by omega
    unfold pi0
    simp only [hnL, hnR, hnLc, hRc, hn1, hn2, hnq, true_and, and_true, dite_true,
      dite_false]

/-! ### Sum-reduction helper

A sum over `I32` whose summand vanishes outside an explicit finite set equals
the sum over that set. -/

theorem sum_eq_of_vanish_outside {s : Finset I32} {g : I32 → ℂ}
    (h : ∀ k, k ∉ s → g k = 0) : ∑ k, g k = Finset.sum s g :=
  (Finset.sum_subset (Finset.subset_univ s) (fun k _ hk => h k hk)).symm

/-! ## §3. pi0 is a multiplicative representation (T1, multiplicative part)

`pi0 (afMul a b) = pi0 a * pi0 b` is proved block by block: on each block the
middle-index sum collapses to the block's slot set (all other terms vanish by
§2), and the collapsed sum is the block formula for the product element. -/

theorem fin2_mk0 : (⟨0, by omega⟩ : Fin 2) = 0 := Fin.ext rfl
theorem fin2_mk1 : (⟨1, by omega⟩ : Fin 2) = 1 := Fin.ext rfl
theorem fin3_mk0 : (⟨0, by omega⟩ : Fin 3) = 0 := Fin.ext rfl
theorem fin3_mk1 : (⟨1, by omega⟩ : Fin 3) = 1 := Fin.ext rfl
theorem fin3_mk2 : (⟨2, by omega⟩ : Fin 3) = 2 := Fin.ext rfl

/-- Block multiplicativity on the H_L lepton doublet: plain 2×2 matrix
multiplication of the quaternion block. -/
theorem pi0_mul_leptonL (a b : AF) (s t : Fin 2) :
    (pi0 a * pi0 b) ⟨s.val, by omega⟩ ⟨t.val, by omega⟩
      = pi0 (afMul a b) ⟨s.val, by omega⟩ ⟨t.val, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset I32) →
      pi0 a ⟨s.val, by omega⟩ k * pi0 b k ⟨t.val, by omega⟩ = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    by_cases hk8 : k.val < 8
    · by_cases hk2 : k.val < 2
      · have hkv : k.val = 0 ∨ k.val = 1 := by omega
        rcases hkv with h0 | h1
        · exact absurd (Fin.ext h0) hk.1
        · exact absurd (Fin.ext h1) hk.2
      · rw [pi0_entry_HL_mixed (i := ⟨s.val, by omega⟩) (j := k) a
          (Or.inl ⟨(by show s.val < 2; omega), (by omega), hk8⟩), zero_mul]
    · rw [pi0_entry_cross_sector (i := ⟨s.val, by omega⟩) (j := k) a
        (by show s.val / 8 ≠ k.val / 8; omega), zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_pair (by decide : (⟨0, by omega⟩ : I32) ≠ ⟨1, by omega⟩),
    pi0_entry_leptonL a s ⟨0, by omega⟩, pi0_entry_leptonL b ⟨0, by omega⟩ t,
    pi0_entry_leptonL a s ⟨1, by omega⟩, pi0_entry_leptonL b ⟨1, by omega⟩ t,
    pi0_entry_leptonL (afMul a b) s t, afMul_q, Matrix.mul_apply, Fin.sum_univ_two,
    fin2_mk0, fin2_mk1]

/-- Block multiplicativity on the H_L quark block: the tensor product
`q ⊗ I₃` multiplies factorwise. -/
theorem pi0_mul_quarkL (a b : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    (pi0 a * pi0 b) ⟨2 + 2 * ki.val + si.val, by omega⟩
        ⟨2 + 2 * kj.val + sj.val, by omega⟩
      = pi0 (afMul a b) ⟨2 + 2 * ki.val + si.val, by omega⟩
        ⟨2 + 2 * kj.val + sj.val, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨2 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨2 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨2 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) →
      pi0 a ⟨2 + 2 * ki.val + si.val, by omega⟩ k *
        pi0 b k ⟨2 + 2 * kj.val + sj.val, by omega⟩ = 0 := by
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
      · rw [pi0_entry_HL_mixed (i := ⟨2 + 2 * ki.val + si.val, by omega⟩) (j := k) a
          (Or.inr ⟨(by show 2 ≤ 2 + 2 * ki.val + si.val; omega),
            (by show 2 + 2 * ki.val + si.val < 8; omega), (by omega)⟩), zero_mul]
    · rw [pi0_entry_cross_sector (i := ⟨2 + 2 * ki.val + si.val, by omega⟩) (j := k) a
        (by show (2 + 2 * ki.val + si.val) / 8 ≠ k.val / 8; omega), zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    pi0_entry_quarkL a ki ⟨0, by omega⟩ si ⟨0, by omega⟩,
    pi0_entry_quarkL b ⟨0, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi0_entry_quarkL a ki ⟨0, by omega⟩ si ⟨1, by omega⟩,
    pi0_entry_quarkL b ⟨0, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi0_entry_quarkL a ki ⟨1, by omega⟩ si ⟨0, by omega⟩,
    pi0_entry_quarkL b ⟨1, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi0_entry_quarkL a ki ⟨1, by omega⟩ si ⟨1, by omega⟩,
    pi0_entry_quarkL b ⟨1, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi0_entry_quarkL a ki ⟨2, by omega⟩ si ⟨0, by omega⟩,
    pi0_entry_quarkL b ⟨2, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi0_entry_quarkL a ki ⟨2, by omega⟩ si ⟨1, by omega⟩,
    pi0_entry_quarkL b ⟨2, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi0_entry_quarkL (afMul a b) ki kj si sj, afMul_q, Matrix.mul_apply,
    Fin.sum_univ_two, fin2_mk0, fin2_mk1, fin3_mk0, fin3_mk1, fin3_mk2]
  fin_cases ki <;> fin_cases kj <;> simp <;> ring

/-- Block multiplicativity at ν_R: `λ * λ`. -/
theorem pi0_mul_nuR (a b : AF) :
    (pi0 a * pi0 b) ⟨8, by omega⟩ ⟨8, by omega⟩
      = pi0 (afMul a b) ⟨8, by omega⟩ ⟨8, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨8, by omega⟩} : Finset I32) →
      pi0 a ⟨8, by omega⟩ k * pi0 b k ⟨8, by omega⟩ = 0 := by
    intro k hk
    simp only [Finset.mem_singleton] at hk
    have hk8v : k.val ≠ 8 := fun hv => hk (Fin.ext hv)
    by_cases hk8 : k.val < 8
    · rw [pi0_entry_cross_sector (i := ⟨8, by omega⟩) (j := k) a
        (by show (8:ℕ) / 8 ≠ k.val / 8; omega), zero_mul]
    · by_cases hk16 : k.val < 16
      · by_cases hk9 : k.val = 9
        · rw [pi0_entry_HR_mixed (i := ⟨8, by omega⟩) (j := k) a
            (Or.inl ⟨rfl, hk9⟩), zero_mul]
        · rw [pi0_entry_HR_mixed (i := ⟨8, by omega⟩) (j := k) a
            (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, by omega, hk16⟩))), zero_mul]
      · rw [pi0_entry_cross_sector (i := ⟨8, by omega⟩) (j := k) a
          (by show (8:ℕ) / 8 ≠ k.val / 8; omega), zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan, Finset.sum_singleton,
    pi0_entry_nuR, pi0_entry_nuR, pi0_entry_nuR, afMul_u1]

/-- Block multiplicativity at e_R: `λ̄ * λ̄ = (λλ)̄`. -/
theorem pi0_mul_eR (a b : AF) :
    (pi0 a * pi0 b) ⟨9, by omega⟩ ⟨9, by omega⟩
      = pi0 (afMul a b) ⟨9, by omega⟩ ⟨9, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨9, by omega⟩} : Finset I32) →
      pi0 a ⟨9, by omega⟩ k * pi0 b k ⟨9, by omega⟩ = 0 := by
    intro k hk
    simp only [Finset.mem_singleton] at hk
    have hk9v : k.val ≠ 9 := fun hv => hk (Fin.ext hv)
    by_cases hk8 : k.val < 8
    · rw [pi0_entry_cross_sector (i := ⟨9, by omega⟩) (j := k) a
        (by show (9:ℕ) / 8 ≠ k.val / 8; omega), zero_mul]
    · by_cases hk16 : k.val < 16
      · by_cases hk8' : k.val = 8
        · rw [pi0_entry_HR_mixed (i := ⟨9, by omega⟩) (j := k) a
            (Or.inr (Or.inl ⟨rfl, hk8'⟩)), zero_mul]
        · rw [pi0_entry_HR_mixed (i := ⟨9, by omega⟩) (j := k) a
            (Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, by omega, hk16⟩))), zero_mul]
      · rw [pi0_entry_cross_sector (i := ⟨9, by omega⟩) (j := k) a
          (by show (9:ℕ) / 8 ≠ k.val / 8; omega), zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan, Finset.sum_singleton,
    pi0_entry_eR, pi0_entry_eR, pi0_entry_eR, afMul_u1, star_mul,
    mul_comm (star b.u1) (star a.u1)]

/-- Block multiplicativity on the H_R quark block: the diagonal ℂ action
multiplies entrywise. -/
theorem pi0_mul_quarkR (a b : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    (pi0 a * pi0 b) ⟨10 + 2 * ki.val + si.val, by omega⟩
        ⟨10 + 2 * kj.val + sj.val, by omega⟩
      = pi0 (afMul a b) ⟨10 + 2 * ki.val + si.val, by omega⟩
        ⟨10 + 2 * kj.val + sj.val, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨10 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨10 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨10 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) →
      pi0 a ⟨10 + 2 * ki.val + si.val, by omega⟩ k *
        pi0 b k ⟨10 + 2 * kj.val + sj.val, by omega⟩ = 0 := by
    intro k hk
    by_cases hklo : k.val < 8
    · rw [pi0_entry_cross_sector (i := ⟨10 + 2 * ki.val + si.val, by omega⟩) (j := k) a
        (by show (10 + 2 * ki.val + si.val) / 8 ≠ k.val / 8; omega), zero_mul]
    · by_cases hkhi : 16 ≤ k.val
      · rw [pi0_entry_cross_sector (i := ⟨10 + 2 * ki.val + si.val, by omega⟩) (j := k) a
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
          · rw [pi0_entry_HR_mixed (i := ⟨10 + 2 * ki.val + si.val, by omega⟩) (j := k) a
              (Or.inr (Or.inr (Or.inr ⟨(by show 10 ≤ 10 + 2 * ki.val + si.val; omega),
                (by show 10 + 2 * ki.val + si.val < 16; omega), Or.inl hk8⟩))), zero_mul]
          · rw [pi0_entry_HR_mixed (i := ⟨10 + 2 * ki.val + si.val, by omega⟩) (j := k) a
              (Or.inr (Or.inr (Or.inr ⟨(by show 10 ≤ 10 + 2 * ki.val + si.val; omega),
                (by show 10 + 2 * ki.val + si.val < 16; omega),
                Or.inr (by omega : k.val = 9)⟩))), zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    pi0_entry_quarkR a ki ⟨0, by omega⟩ si ⟨0, by omega⟩,
    pi0_entry_quarkR b ⟨0, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi0_entry_quarkR a ki ⟨0, by omega⟩ si ⟨1, by omega⟩,
    pi0_entry_quarkR b ⟨0, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi0_entry_quarkR a ki ⟨1, by omega⟩ si ⟨0, by omega⟩,
    pi0_entry_quarkR b ⟨1, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi0_entry_quarkR a ki ⟨1, by omega⟩ si ⟨1, by omega⟩,
    pi0_entry_quarkR b ⟨1, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi0_entry_quarkR a ki ⟨2, by omega⟩ si ⟨0, by omega⟩,
    pi0_entry_quarkR b ⟨2, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi0_entry_quarkR a ki ⟨2, by omega⟩ si ⟨1, by omega⟩,
    pi0_entry_quarkR b ⟨2, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi0_entry_quarkR (afMul a b) ki kj si sj, afMul_u1, fin2_mk0, fin2_mk1,
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

/-- Block multiplicativity on the H_L antilepton doublet: `(λ̄ q̄)(λ̄ q̄)`
multiplies factorwise (scalars commute, entrywise conjugation is a ring
homomorphism). -/
theorem pi0_mul_leptonLc (a b : AF) (s t : Fin 2) :
    (pi0 a * pi0 b) ⟨16 + s.val, by omega⟩ ⟨16 + t.val, by omega⟩
      = pi0 (afMul a b) ⟨16 + s.val, by omega⟩ ⟨16 + t.val, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨16 + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨16 + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) →
      pi0 a ⟨16 + s.val, by omega⟩ k * pi0 b k ⟨16 + t.val, by omega⟩ = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    by_cases hk24 : k.val < 24
    · by_cases hk16 : 16 ≤ k.val
      · by_cases hk18 : k.val < 18
        · have hkv : k.val = 16 ∨ k.val = 17 := by omega
          rcases hkv with h0 | h1
          · exact absurd (Fin.ext (show k.val = 16 by omega)) hk.1
          · exact absurd (Fin.ext (show k.val = 17 by omega)) hk.2
        · rw [pi0_entry_Hc_mixed (i := ⟨16 + s.val, by omega⟩) (j := k) a
            (Or.inl ⟨(by show 16 ≤ 16 + s.val; omega), (by show 16 + s.val < 18; omega),
              (by omega), hk24⟩), zero_mul]
      · rw [pi0_entry_cross_sector (i := ⟨16 + s.val, by omega⟩) (j := k) a
          (by show (16 + s.val) / 8 ≠ k.val / 8; omega), zero_mul]
    · rw [pi0_entry_cross_sector (i := ⟨16 + s.val, by omega⟩) (j := k) a
        (by show (16 + s.val) / 8 ≠ k.val / 8; omega), zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_pair (by decide : (⟨16 + (⟨0, by omega⟩ : Fin 2).val, by omega⟩ : I32) ≠
      ⟨16 + (⟨1, by omega⟩ : Fin 2).val, by omega⟩),
    pi0_entry_leptonLc a s ⟨0, by omega⟩, pi0_entry_leptonLc b ⟨0, by omega⟩ t,
    pi0_entry_leptonLc a s ⟨1, by omega⟩, pi0_entry_leptonLc b ⟨1, by omega⟩ t,
    pi0_entry_leptonLc (afMul a b) s t, afMul_u1, afMul_q, star_mul, Matrix.mul_apply,
    star_sum, Fin.sum_univ_two, star_mul, star_mul, fin2_mk0, fin2_mk1]
  ring

/-- Block multiplicativity on the H_L antiquark block: the tensor product
`q̄ ⊗ m` multiplies factorwise. -/
theorem pi0_mul_quarkLc (a b : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    (pi0 a * pi0 b) ⟨18 + 2 * ki.val + si.val, by omega⟩
        ⟨18 + 2 * kj.val + sj.val, by omega⟩
      = pi0 (afMul a b) ⟨18 + 2 * ki.val + si.val, by omega⟩
        ⟨18 + 2 * kj.val + sj.val, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨18 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨18 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩,
      ⟨18 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) →
      pi0 a ⟨18 + 2 * ki.val + si.val, by omega⟩ k *
        pi0 b k ⟨18 + 2 * kj.val + sj.val, by omega⟩ = 0 := by
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
        · rw [pi0_entry_Hc_mixed (i := ⟨18 + 2 * ki.val + si.val, by omega⟩) (j := k) a
            (Or.inr (Or.inl ⟨(by show 18 ≤ 18 + 2 * ki.val + si.val; omega),
              (by show 18 + 2 * ki.val + si.val < 24; omega), hk16, (by omega)⟩)), zero_mul]
      · rw [pi0_entry_cross_sector (i := ⟨18 + 2 * ki.val + si.val, by omega⟩) (j := k) a
          (by show (18 + 2 * ki.val + si.val) / 8 ≠ k.val / 8; omega), zero_mul]
    · rw [pi0_entry_cross_sector (i := ⟨18 + 2 * ki.val + si.val, by omega⟩) (j := k) a
        (by show (18 + 2 * ki.val + si.val) / 8 ≠ k.val / 8; omega), zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    pi0_entry_quarkLc a ki ⟨0, by omega⟩ si ⟨0, by omega⟩,
    pi0_entry_quarkLc b ⟨0, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi0_entry_quarkLc a ki ⟨0, by omega⟩ si ⟨1, by omega⟩,
    pi0_entry_quarkLc b ⟨0, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi0_entry_quarkLc a ki ⟨1, by omega⟩ si ⟨0, by omega⟩,
    pi0_entry_quarkLc b ⟨1, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi0_entry_quarkLc a ki ⟨1, by omega⟩ si ⟨1, by omega⟩,
    pi0_entry_quarkLc b ⟨1, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi0_entry_quarkLc a ki ⟨2, by omega⟩ si ⟨0, by omega⟩,
    pi0_entry_quarkLc b ⟨2, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi0_entry_quarkLc a ki ⟨2, by omega⟩ si ⟨1, by omega⟩,
    pi0_entry_quarkLc b ⟨2, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi0_entry_quarkLc (afMul a b) ki kj si sj, afMul_q, afMul_color, Matrix.mul_apply,
    star_sum, Fin.sum_univ_two, star_mul, star_mul, Matrix.mul_apply,
    Fin.sum_univ_three, fin2_mk0, fin2_mk1, fin3_mk0, fin3_mk1, fin3_mk2]
  ring

/-- Block multiplicativity at the ν_R antiparticle singlet: `λ̄ * λ̄`. -/
theorem pi0_mul_nuRc (a b : AF) :
    (pi0 a * pi0 b) ⟨24, by omega⟩ ⟨24, by omega⟩
      = pi0 (afMul a b) ⟨24, by omega⟩ ⟨24, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨24, by omega⟩} : Finset I32) →
      pi0 a ⟨24, by omega⟩ k * pi0 b k ⟨24, by omega⟩ = 0 := by
    intro k hk
    simp only [Finset.mem_singleton] at hk
    have hk24v : k.val ≠ 24 := fun hv => hk (Fin.ext hv)
    by_cases hk24 : k.val < 24
    · rw [pi0_entry_cross_sector (i := ⟨24, by omega⟩) (j := k) a
        (by show (24:ℕ) / 8 ≠ k.val / 8; omega), zero_mul]
    · by_cases hk25 : k.val = 25
      · rw [pi0_entry_Hc_mixed (i := ⟨24, by omega⟩) (j := k) a
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hk25⟩))))))),
          zero_mul]
      · rw [pi0_entry_Hc_mixed (i := ⟨24, by omega⟩) (j := k) a
          (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))), zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan, Finset.sum_singleton,
    pi0_entry_nuRc, pi0_entry_nuRc, pi0_entry_nuRc, afMul_u1, star_mul,
    mul_comm (star b.u1) (star a.u1)]

/-- Block multiplicativity at the e_R antiparticle singlet: `λ̄ * λ̄`. -/
theorem pi0_mul_eRc (a b : AF) :
    (pi0 a * pi0 b) ⟨25, by omega⟩ ⟨25, by omega⟩
      = pi0 (afMul a b) ⟨25, by omega⟩ ⟨25, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨25, by omega⟩} : Finset I32) →
      pi0 a ⟨25, by omega⟩ k * pi0 b k ⟨25, by omega⟩ = 0 := by
    intro k hk
    simp only [Finset.mem_singleton] at hk
    have hk25v : k.val ≠ 25 := fun hv => hk (Fin.ext hv)
    by_cases hk24 : k.val < 24
    · rw [pi0_entry_cross_sector (i := ⟨25, by omega⟩) (j := k) a
        (by show (25:ℕ) / 8 ≠ k.val / 8; omega), zero_mul]
    · by_cases hk24' : k.val = 24
      · rw [pi0_entry_Hc_mixed (i := ⟨25, by omega⟩) (j := k) a
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hk24'⟩))))))),
          zero_mul]
      · rw [pi0_entry_Hc_mixed (i := ⟨25, by omega⟩) (j := k) a
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩)))), zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan, Finset.sum_singleton,
    pi0_entry_eRc, pi0_entry_eRc, pi0_entry_eRc, afMul_u1, star_mul,
    mul_comm (star b.u1) (star a.u1)]

/-- Block multiplicativity on the H_R antiquark block: `m` alone,
flavour-diagonally — the color factor multiplies as a matrix on triplets. -/
theorem pi0_mul_quarkRc (a b : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    (pi0 a * pi0 b) ⟨26 + 2 * ki.val + si.val, by omega⟩
        ⟨26 + 2 * kj.val + sj.val, by omega⟩
      = pi0 (afMul a b) ⟨26 + 2 * ki.val + si.val, by omega⟩
        ⟨26 + 2 * kj.val + sj.val, by omega⟩ := by
  have hvan : ∀ k : I32, k ∉ ({⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩,
      ⟨26 + 2 * (⟨0, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩,
      ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩,
      ⟨26 + 2 * (⟨1, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩,
      ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨0, by omega⟩ : Fin 2).val, by decide⟩,
      ⟨26 + 2 * (⟨2, by omega⟩ : Fin 3).val + (⟨1, by omega⟩ : Fin 2).val, by decide⟩} : Finset I32) →
      pi0 a ⟨26 + 2 * ki.val + si.val, by omega⟩ k *
        pi0 b k ⟨26 + 2 * kj.val + sj.val, by omega⟩ = 0 := by
    intro k hk
    by_cases hk24 : k.val < 24
    · rw [pi0_entry_cross_sector (i := ⟨26 + 2 * ki.val + si.val, by omega⟩) (j := k) a
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
        · rw [pi0_entry_Hc_mixed (i := ⟨26 + 2 * ki.val + si.val, by omega⟩) (j := k) a
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨(by show 26 ≤ 26 + 2 * ki.val + si.val; omega), hk24'⟩))))), zero_mul]
        · rw [pi0_entry_Hc_mixed (i := ⟨26 + 2 * ki.val + si.val, by omega⟩) (j := k) a
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨(by show 26 ≤ 26 + 2 * ki.val + si.val; omega),
                (by omega : k.val = 25)⟩)))))), zero_mul]
  rw [Matrix.mul_apply, sum_eq_of_vanish_outside hvan,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    pi0_entry_quarkRc a ki ⟨0, by omega⟩ si ⟨0, by omega⟩,
    pi0_entry_quarkRc b ⟨0, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi0_entry_quarkRc a ki ⟨0, by omega⟩ si ⟨1, by omega⟩,
    pi0_entry_quarkRc b ⟨0, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi0_entry_quarkRc a ki ⟨1, by omega⟩ si ⟨0, by omega⟩,
    pi0_entry_quarkRc b ⟨1, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi0_entry_quarkRc a ki ⟨1, by omega⟩ si ⟨1, by omega⟩,
    pi0_entry_quarkRc b ⟨1, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi0_entry_quarkRc a ki ⟨2, by omega⟩ si ⟨0, by omega⟩,
    pi0_entry_quarkRc b ⟨2, by omega⟩ kj ⟨0, by omega⟩ sj,
    pi0_entry_quarkRc a ki ⟨2, by omega⟩ si ⟨1, by omega⟩,
    pi0_entry_quarkRc b ⟨2, by omega⟩ kj ⟨1, by omega⟩ sj,
    pi0_entry_quarkRc (afMul a b) ki kj si sj, afMul_color, Matrix.mul_apply,
    Fin.sum_univ_three, fin3_mk0, fin3_mk1, fin3_mk2]
  by_cases h : si = sj
  · subst h
    fin_cases si <;> simp <;> ring
  · fin_cases si <;> fin_cases sj <;> simp <;> ring

/-- The ten blocks of pi0, as a relation on slots: two slots lie in the same
block when some block contains both. -/
def sameBlock (i j : I32) : Prop :=
  (i.val < 2 ∧ j.val < 2) ∨
  (2 ≤ i.val ∧ i.val < 8 ∧ 2 ≤ j.val ∧ j.val < 8) ∨
  (i.val = 8 ∧ j.val = 8) ∨
  (i.val = 9 ∧ j.val = 9) ∨
  (10 ≤ i.val ∧ i.val < 16 ∧ 10 ≤ j.val ∧ j.val < 16) ∨
  (16 ≤ i.val ∧ i.val < 18 ∧ 16 ≤ j.val ∧ j.val < 18) ∨
  (18 ≤ i.val ∧ i.val < 24 ∧ 18 ≤ j.val ∧ j.val < 24) ∨
  (i.val = 24 ∧ j.val = 24) ∨
  (i.val = 25 ∧ j.val = 25) ∨
  (26 ≤ i.val ∧ i.val < 32 ∧ 26 ≤ j.val ∧ j.val < 32)

theorem sameBlock_symm {i j : I32} (h : sameBlock i j) : sameBlock j i := by
  unfold sameBlock at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨h2, h1⟩
  · exact Or.inr (Or.inl ⟨h3, h4, h1, h2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, h4, h1, h2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, h4, h1, h2⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, h4, h1, h2⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h3, h4, h1, h2⟩))))))))

theorem sameBlock_trans {i k j : I32} (h1 : sameBlock i k) (h2 : sameBlock k j) :
    sameBlock i j := by
  unfold sameBlock at h1 h2
  rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ |
    ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ |
    ⟨a1, a2, a3, a4⟩ <;>
  rcases h2 with ⟨b1, b2⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2⟩ | ⟨b1, b2⟩ |
    ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2⟩ | ⟨b1, b2⟩ |
    ⟨b1, b2, b3, b4⟩ <;>
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

theorem not_sameBlock_of_ne_sector {i j : I32} (h : i.val / 8 ≠ j.val / 8) :
    ¬ sameBlock i j := by
  intro hs
  unfold sameBlock at hs
  omega

theorem not_sameBlock_of_HL_mixed {i j : I32}
    (h : (i.val < 2 ∧ 2 ≤ j.val ∧ j.val < 8) ∨ (2 ≤ i.val ∧ i.val < 8 ∧ j.val < 2)) :
    ¬ sameBlock i j := by
  intro hs
  unfold sameBlock at hs
  omega

theorem not_sameBlock_of_HR_mixed {i j : I32}
    (h : (i.val = 8 ∧ j.val = 9) ∨ (i.val = 9 ∧ j.val = 8) ∨
      ((i.val = 8 ∨ i.val = 9) ∧ 10 ≤ j.val ∧ j.val < 16) ∨
      (10 ≤ i.val ∧ i.val < 16 ∧ (j.val = 8 ∨ j.val = 9))) :
    ¬ sameBlock i j := by
  intro hs
  unfold sameBlock at hs
  omega

theorem not_sameBlock_of_Hc_mixed {i j : I32}
    (h : (16 ≤ i.val ∧ i.val < 18 ∧ 18 ≤ j.val ∧ j.val < 24) ∨
      (18 ≤ i.val ∧ i.val < 24 ∧ 16 ≤ j.val ∧ j.val < 18) ∨
      (i.val = 24 ∧ 26 ≤ j.val) ∨ (i.val = 25 ∧ 26 ≤ j.val) ∨
      (26 ≤ i.val ∧ j.val = 24) ∨ (26 ≤ i.val ∧ j.val = 25) ∨
      (i.val = 24 ∧ j.val = 25) ∨ (i.val = 25 ∧ j.val = 24)) :
    ¬ sameBlock i j := by
  intro hs
  unfold sameBlock at hs
  omega

/-- Unified vanishing: off-block entries of `pi0 a` are zero. Proved by the
sector case tree, using §2's entry/vanishing lemmas — no definition unfolding. -/
theorem pi0_entry_eq_zero_of_not_sameBlock (a : AF) {i j : I32}
    (h : ¬ sameBlock i j) : pi0 a i j = 0 := by
  by_cases hsec : i.val / 8 = j.val / 8
  · by_cases hi : i.val < 8
    · have hj : j.val < 8 := by omega
      by_cases hi2 : i.val < 2
      · by_cases hj2 : j.val < 2
        · exact absurd (Or.inl ⟨hi2, hj2⟩) h
        · exact pi0_entry_HL_mixed a (Or.inl ⟨hi2, by omega, hj⟩)
      · by_cases hj2 : j.val < 2
        · exact pi0_entry_HL_mixed a (Or.inr ⟨by omega, hi, hj2⟩)
        · exact absurd (Or.inr (Or.inl ⟨by omega, hi, by omega, hj⟩)) h
    · by_cases hi16 : i.val < 16
      · have hj8 : 8 ≤ j.val := by omega
        have hj16 : j.val < 16 := by omega
        by_cases hi8 : i.val = 8
        · by_cases hj8' : j.val = 8
          · exact absurd (Or.inr (Or.inr (Or.inl ⟨hi8, hj8'⟩))) h
          · by_cases hj9 : j.val = 9
            · exact pi0_entry_HR_mixed a (Or.inl ⟨hi8, hj9⟩)
            · exact pi0_entry_HR_mixed a
                (Or.inr (Or.inr (Or.inl ⟨Or.inl hi8, by omega, hj16⟩)))
        · by_cases hi9 : i.val = 9
          · by_cases hj8' : j.val = 8
            · exact pi0_entry_HR_mixed a (Or.inr (Or.inl ⟨hi9, hj8'⟩))
            · by_cases hj9 : j.val = 9
              · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi9, hj9⟩)))) h
              · exact pi0_entry_HR_mixed a
                  (Or.inr (Or.inr (Or.inl ⟨Or.inr hi9, by omega, hj16⟩)))
          · by_cases hj8' : j.val = 8
            · exact pi0_entry_HR_mixed a
                (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inl hj8'⟩)))
            · by_cases hj9 : j.val = 9
              · exact pi0_entry_HR_mixed a
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
            · exact pi0_entry_Hc_mixed a (Or.inl ⟨by omega, hi18, by omega, hj24⟩)
          · by_cases hj18 : j.val < 18
            · exact pi0_entry_Hc_mixed a (Or.inr (Or.inl ⟨by omega, hi24, hj16, hj18⟩))
            · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨by omega, hi24, by omega, hj24⟩))))))) h
        · have hj24 : 24 ≤ j.val := by omega
          by_cases hi24' : i.val = 24
          · by_cases hj24' : j.val = 24
            · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inl ⟨hi24', hj24'⟩)))))))) h
            · by_cases hj25 : j.val = 25
              · exact pi0_entry_Hc_mixed a (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inl ⟨hi24', hj25⟩)))))))
              · exact pi0_entry_Hc_mixed a (Or.inr (Or.inr (Or.inl ⟨hi24', by omega⟩)))
          · by_cases hi25 : i.val = 25
            · by_cases hj24' : j.val = 24
              · exact pi0_entry_Hc_mixed a (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr ⟨hi25, hj24'⟩)))))))
              · by_cases hj25 : j.val = 25
                · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inr (Or.inl ⟨hi25, hj25⟩))))))))) h
                · exact pi0_entry_Hc_mixed a
                    (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi25, by omega⟩))))
            · by_cases hj24' : j.val = 24
              · exact pi0_entry_Hc_mixed a (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inl ⟨by omega, hj24'⟩)))))
              · by_cases hj25 : j.val = 25
                · exact pi0_entry_Hc_mixed a (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inl ⟨by omega, hj25⟩))))))
                · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inr (Or.inr (⟨by omega, by omega, by omega, by omega⟩)))))))))) h
  · exact pi0_entry_cross_sector a hsec

theorem mul_entry_eq_zero (a b : AF) {i j : I32}
    (ha : ∀ k : I32, pi0 a i k = 0 ∨ pi0 b k j = 0) : (pi0 a * pi0 b) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rcases ha k with h | h
  · rw [h, zero_mul]
  · rw [h, mul_zero]

/-- Product vanishing off-block: every middle index misses the block of `i`
or the block of `j`. -/
theorem pi0_mul_eq_zero_of_not_sameBlock (a b : AF) {i j : I32}
    (h : ¬ sameBlock i j) : (pi0 a * pi0 b) i j = 0 := by
  apply mul_entry_eq_zero
  intro k
  by_cases hs : sameBlock i k
  · exact Or.inr (pi0_entry_eq_zero_of_not_sameBlock b
      (fun hkj => h (sameBlock_trans hs hkj)))
  · exact Or.inl (pi0_entry_eq_zero_of_not_sameBlock a hs)

/-- T1 (multiplicative part): `pi0` preserves the componentwise product.
The proof is the entry case tree: off-block entries vanish on both sides;
on-block entries are the ten block lemmas of §3. -/
theorem pi0_afMul (a b : AF) : pi0 (afMul a b) = pi0 a * pi0 b := by
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
          exact (pi0_mul_leptonL a b ⟨i.val, hi2⟩ ⟨j.val, hj2⟩).symm
        · have hns : ¬ sameBlock i j := not_sameBlock_of_HL_mixed (Or.inl ⟨hi2, by omega, hj⟩)
          rw [pi0_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
            pi0_mul_eq_zero_of_not_sameBlock a b hns]
      · by_cases hj2 : j.val < 2
        · have hns : ¬ sameBlock i j := not_sameBlock_of_HL_mixed (Or.inr ⟨by omega, hi, hj2⟩)
          rw [pi0_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
            pi0_mul_eq_zero_of_not_sameBlock a b hns]
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
          exact (pi0_mul_quarkL a b ⟨(i.val - 2) / 2, by omega⟩
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
            exact (pi0_mul_nuR a b).symm
          · by_cases hj9 : j.val = 9
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed (Or.inl ⟨hi8, hj9⟩)
              rw [pi0_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                pi0_mul_eq_zero_of_not_sameBlock a b hns]
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                (Or.inr (Or.inr (Or.inl ⟨Or.inl hi8, by omega, hj16⟩)))
              rw [pi0_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                pi0_mul_eq_zero_of_not_sameBlock a b hns]
        · by_cases hi9 : i.val = 9
          · by_cases hj8' : j.val = 8
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed (Or.inr (Or.inl ⟨hi9, hj8'⟩))
              rw [pi0_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                pi0_mul_eq_zero_of_not_sameBlock a b hns]
            · by_cases hj9 : j.val = 9
              · have hsi : (⟨9, by omega⟩ : I32) = i := Fin.ext hi9.symm
                have hsj : (⟨9, by omega⟩ : I32) = j := Fin.ext hj9.symm
                rw [← hsi, ← hsj]
                exact (pi0_mul_eR a b).symm
              · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                  (Or.inr (Or.inr (Or.inl ⟨Or.inr hi9, by omega, hj16⟩)))
                rw [pi0_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                  pi0_mul_eq_zero_of_not_sameBlock a b hns]
          · by_cases hj8' : j.val = 8
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inl hj8'⟩)))
              rw [pi0_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                pi0_mul_eq_zero_of_not_sameBlock a b hns]
            · by_cases hj9 : j.val = 9
              · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                  (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inr hj9⟩)))
                rw [pi0_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                  pi0_mul_eq_zero_of_not_sameBlock a b hns]
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
                exact (pi0_mul_quarkR a b ⟨(i.val - 10) / 2, by omega⟩
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
              exact (pi0_mul_leptonLc a b ⟨i.val - 16, by omega⟩
                ⟨j.val - 16, by omega⟩).symm
            · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                (Or.inl ⟨by omega, hi18, by omega, hj24⟩)
              rw [pi0_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                pi0_mul_eq_zero_of_not_sameBlock a b hns]
          · by_cases hj18 : j.val < 18
            · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                (Or.inr (Or.inl ⟨by omega, hi24, hj16, hj18⟩))
              rw [pi0_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                pi0_mul_eq_zero_of_not_sameBlock a b hns]
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
              exact (pi0_mul_quarkLc a b ⟨(i.val - 18) / 2, by omega⟩
                ⟨(j.val - 18) / 2, by omega⟩ ⟨(i.val - 18) % 2, by omega⟩
                ⟨(j.val - 18) % 2, by omega⟩).symm
        · have hj24 : 24 ≤ j.val := by omega
          by_cases hi24' : i.val = 24
          · by_cases hj24' : j.val = 24
            · have hsi : (⟨24, by omega⟩ : I32) = i := Fin.ext hi24'.symm
              have hsj : (⟨24, by omega⟩ : I32) = j := Fin.ext hj24'.symm
              rw [← hsi, ← hsj]
              exact (pi0_mul_nuRc a b).symm
            · by_cases hj25 : j.val = 25
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inl ⟨hi24', hj25⟩)))))))
                rw [pi0_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                  pi0_mul_eq_zero_of_not_sameBlock a b hns]
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                  (Or.inr (Or.inr (Or.inl ⟨hi24', by omega⟩)))
                rw [pi0_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                  pi0_mul_eq_zero_of_not_sameBlock a b hns]
          · by_cases hi25 : i.val = 25
            · by_cases hj24' : j.val = 24
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr ⟨hi25, hj24'⟩)))))))
                rw [pi0_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                  pi0_mul_eq_zero_of_not_sameBlock a b hns]
              · by_cases hj25 : j.val = 25
                · have hsi : (⟨25, by omega⟩ : I32) = i := Fin.ext hi25.symm
                  have hsj : (⟨25, by omega⟩ : I32) = j := Fin.ext hj25.symm
                  rw [← hsi, ← hsj]
                  exact (pi0_mul_eRc a b).symm
                · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                    (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi25, by omega⟩))))
                  rw [pi0_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                    pi0_mul_eq_zero_of_not_sameBlock a b hns]
            · by_cases hj24' : j.val = 24
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inl ⟨by omega, hj24'⟩)))))
                rw [pi0_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                  pi0_mul_eq_zero_of_not_sameBlock a b hns]
              · by_cases hj25 : j.val = 25
                · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inl ⟨by omega, hj25⟩))))))
                  rw [pi0_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
                    pi0_mul_eq_zero_of_not_sameBlock a b hns]
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
                  exact (pi0_mul_quarkRc a b ⟨(i.val - 26) / 2, by omega⟩
                    ⟨(j.val - 26) / 2, by omega⟩ ⟨(i.val - 26) % 2, by omega⟩
                    ⟨(j.val - 26) % 2, by omega⟩).symm
  · have hns : ¬ sameBlock i j := not_sameBlock_of_ne_sector hsec
    rw [pi0_entry_eq_zero_of_not_sameBlock (afMul a b) hns,
      pi0_mul_eq_zero_of_not_sameBlock a b hns]

theorem afZero_u1 : afZero.u1 = 0 := rfl
theorem afZero_q : afZero.q = 0 := rfl
theorem afZero_color : afZero.color = 0 := rfl
theorem afOne_u1 : afOne.u1 = 1 := rfl
theorem afOne_q : afOne.q = 1 := rfl
theorem afOne_color : afOne.color = 1 := rfl

/-- `pi0` sends the zero element to the zero matrix (entry tree). -/
theorem pi0_zero : pi0 afZero = 0 := by
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
          rw [← hsi, ← hsj, pi0_entry_leptonL]
          simp only [afZero_q, Matrix.zero_apply]
        · have hns : ¬ sameBlock i j := not_sameBlock_of_HL_mixed (Or.inl ⟨hi2, by omega, hj⟩)
          rw [pi0_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
      · by_cases hj2 : j.val < 2
        · have hns : ¬ sameBlock i j := not_sameBlock_of_HL_mixed (Or.inr ⟨by omega, hi, hj2⟩)
          rw [pi0_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
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
          rw [← hci, ← hcj, pi0_entry_quarkL]
          split_ifs <;> simp only [afZero_q, Matrix.zero_apply]
    · by_cases hi16 : i.val < 16
      · have hj8 : 8 ≤ j.val := by omega
        have hj16 : j.val < 16 := by omega
        by_cases hi8 : i.val = 8
        · by_cases hj8' : j.val = 8
          · have hsi : (⟨8, by omega⟩ : I32) = i := Fin.ext hi8.symm
            have hsj : (⟨8, by omega⟩ : I32) = j := Fin.ext hj8'.symm
            rw [← hsi, ← hsj, pi0_entry_nuR]
            simp only [afZero_u1, Matrix.zero_apply]
          · by_cases hj9 : j.val = 9
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed (Or.inl ⟨hi8, hj9⟩)
              rw [pi0_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                (Or.inr (Or.inr (Or.inl ⟨Or.inl hi8, by omega, hj16⟩)))
              rw [pi0_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
        · by_cases hi9 : i.val = 9
          · by_cases hj8' : j.val = 8
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed (Or.inr (Or.inl ⟨hi9, hj8'⟩))
              rw [pi0_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
            · by_cases hj9 : j.val = 9
              · have hsi : (⟨9, by omega⟩ : I32) = i := Fin.ext hi9.symm
                have hsj : (⟨9, by omega⟩ : I32) = j := Fin.ext hj9.symm
                rw [← hsi, ← hsj, pi0_entry_eR]
                simp only [afZero_u1, star_zero, Matrix.zero_apply]
              · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                  (Or.inr (Or.inr (Or.inl ⟨Or.inr hi9, by omega, hj16⟩)))
                rw [pi0_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
          · by_cases hj8' : j.val = 8
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inl hj8'⟩)))
              rw [pi0_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
            · by_cases hj9 : j.val = 9
              · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                  (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inr hj9⟩)))
                rw [pi0_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
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
                rw [← hci, ← hcj, pi0_entry_quarkR]
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
              rw [← hsi, ← hsj, pi0_entry_leptonLc]
              simp only [afZero_u1, afZero_q, star_zero, Matrix.zero_apply, mul_zero]
            · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                (Or.inl ⟨by omega, hi18, by omega, hj24⟩)
              rw [pi0_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
          · by_cases hj18 : j.val < 18
            · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                (Or.inr (Or.inl ⟨by omega, hi24, hj16, hj18⟩))
              rw [pi0_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
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
              rw [← hci, ← hcj, pi0_entry_quarkLc]
              simp only [afZero_q, afZero_color, star_zero, Matrix.zero_apply,
                mul_zero, zero_mul]
        · have hj24 : 24 ≤ j.val := by omega
          by_cases hi24' : i.val = 24
          · by_cases hj24' : j.val = 24
            · have hsi : (⟨24, by omega⟩ : I32) = i := Fin.ext hi24'.symm
              have hsj : (⟨24, by omega⟩ : I32) = j := Fin.ext hj24'.symm
              rw [← hsi, ← hsj, pi0_entry_nuRc]
              simp only [afZero_u1, star_zero, Matrix.zero_apply]
            · by_cases hj25 : j.val = 25
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inl ⟨hi24', hj25⟩)))))))
                rw [pi0_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                  (Or.inr (Or.inr (Or.inl ⟨hi24', by omega⟩)))
                rw [pi0_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
          · by_cases hi25 : i.val = 25
            · by_cases hj24' : j.val = 24
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr ⟨hi25, hj24'⟩)))))))
                rw [pi0_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
              · by_cases hj25 : j.val = 25
                · have hsi : (⟨25, by omega⟩ : I32) = i := Fin.ext hi25.symm
                  have hsj : (⟨25, by omega⟩ : I32) = j := Fin.ext hj25.symm
                  rw [← hsi, ← hsj, pi0_entry_eRc]
                  simp only [afZero_u1, star_zero, Matrix.zero_apply]
                · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                    (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi25, by omega⟩))))
                  rw [pi0_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
            · by_cases hj24' : j.val = 24
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inl ⟨by omega, hj24'⟩)))))
                rw [pi0_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
              · by_cases hj25 : j.val = 25
                · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inl ⟨by omega, hj25⟩))))))
                  rw [pi0_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]
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
                  rw [← hci, ← hcj, pi0_entry_quarkRc]
                  split_ifs <;> simp only [afZero_color, Matrix.zero_apply]
  · have hns : ¬ sameBlock i j := not_sameBlock_of_ne_sector hsec
    rw [pi0_entry_eq_zero_of_not_sameBlock afZero hns, Matrix.zero_apply]

/-! ### Star entries: `pi0 (afStar a)` against the conjugate transpose, block by
block. Stated with variable slot parts so the if-conditions can be split on
genuine variables. -/

theorem pi0_star_entry_leptonL (a : AF) (s t : Fin 2) :
    pi0 (afStar a) ⟨s.val, by omega⟩ ⟨t.val, by omega⟩
      = star (pi0 a ⟨t.val, by omega⟩ ⟨s.val, by omega⟩) := by
  rw [pi0_entry_leptonL, pi0_entry_leptonL, afStar_q, Matrix.conjTranspose_apply]

theorem pi0_star_entry_quarkL (a : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    pi0 (afStar a) ⟨2 + 2 * ki.val + si.val, by omega⟩
        ⟨2 + 2 * kj.val + sj.val, by omega⟩
      = star (pi0 a ⟨2 + 2 * kj.val + sj.val, by omega⟩
        ⟨2 + 2 * ki.val + si.val, by omega⟩) := by
  rw [pi0_entry_quarkL, pi0_entry_quarkL]
  by_cases h : ki = kj
  · rw [if_pos h, if_pos h.symm, afStar_q, Matrix.conjTranspose_apply]
  · rw [if_neg h, if_neg (fun hh => h hh.symm), star_zero]

theorem pi0_star_entry_nuR (a : AF) :
    pi0 (afStar a) ⟨8, by omega⟩ ⟨8, by omega⟩
      = star (pi0 a ⟨8, by omega⟩ ⟨8, by omega⟩) := by
  rw [pi0_entry_nuR, pi0_entry_nuR, afStar_u1]

theorem pi0_star_entry_eR (a : AF) :
    pi0 (afStar a) ⟨9, by omega⟩ ⟨9, by omega⟩
      = star (pi0 a ⟨9, by omega⟩ ⟨9, by omega⟩) := by
  rw [pi0_entry_eR, pi0_entry_eR, afStar_u1]

theorem pi0_star_entry_quarkR (a : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    pi0 (afStar a) ⟨10 + 2 * ki.val + si.val, by omega⟩
        ⟨10 + 2 * kj.val + sj.val, by omega⟩
      = star (pi0 a ⟨10 + 2 * kj.val + sj.val, by omega⟩
        ⟨10 + 2 * ki.val + si.val, by omega⟩) := by
  rw [pi0_entry_quarkR, pi0_entry_quarkR]
  by_cases h : si = sj ∧ ki = kj
  · obtain ⟨h1, h2⟩ := h
    have h' : sj = si ∧ kj = ki := ⟨h1.symm, h2.symm⟩
    rw [if_pos ⟨h1, h2⟩, if_pos h']
    subst h1
    split_ifs <;> simp only [afStar_u1, star_star]
  · have h' : ¬ (sj = si ∧ kj = ki) := fun hh => h ⟨hh.1.symm, hh.2.symm⟩
    rw [if_neg h, if_neg h', star_zero]

theorem pi0_star_entry_leptonLc (a : AF) (s t : Fin 2) :
    pi0 (afStar a) ⟨16 + s.val, by omega⟩ ⟨16 + t.val, by omega⟩
      = star (pi0 a ⟨16 + t.val, by omega⟩ ⟨16 + s.val, by omega⟩) := by
  rw [pi0_entry_leptonLc, pi0_entry_leptonLc, afStar_u1, afStar_q,
    Matrix.conjTranspose_apply, star_mul]
  exact mul_comm _ _

theorem pi0_star_entry_quarkLc (a : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    pi0 (afStar a) ⟨18 + 2 * ki.val + si.val, by omega⟩
        ⟨18 + 2 * kj.val + sj.val, by omega⟩
      = star (pi0 a ⟨18 + 2 * kj.val + sj.val, by omega⟩
        ⟨18 + 2 * ki.val + si.val, by omega⟩) := by
  rw [pi0_entry_quarkLc, pi0_entry_quarkLc, afStar_q, afStar_color,
    Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, star_mul]
  exact mul_comm _ _

theorem pi0_star_entry_nuRc (a : AF) :
    pi0 (afStar a) ⟨24, by omega⟩ ⟨24, by omega⟩
      = star (pi0 a ⟨24, by omega⟩ ⟨24, by omega⟩) := by
  rw [pi0_entry_nuRc, pi0_entry_nuRc, afStar_u1]

theorem pi0_star_entry_eRc (a : AF) :
    pi0 (afStar a) ⟨25, by omega⟩ ⟨25, by omega⟩
      = star (pi0 a ⟨25, by omega⟩ ⟨25, by omega⟩) := by
  rw [pi0_entry_eRc, pi0_entry_eRc, afStar_u1]

theorem pi0_star_entry_quarkRc (a : AF) (ki kj : Fin 3) (si sj : Fin 2) :
    pi0 (afStar a) ⟨26 + 2 * ki.val + si.val, by omega⟩
        ⟨26 + 2 * kj.val + sj.val, by omega⟩
      = star (pi0 a ⟨26 + 2 * kj.val + sj.val, by omega⟩
        ⟨26 + 2 * ki.val + si.val, by omega⟩) := by
  rw [pi0_entry_quarkRc, pi0_entry_quarkRc]
  by_cases h : si = sj
  · rw [if_pos h, if_pos h.symm, afStar_color, Matrix.conjTranspose_apply]
  · rw [if_neg h, if_neg (fun hh => h hh.symm), star_zero]

/-- T1 (star part): `pi0` preserves the involution. Entry case tree as for
`pi0_afMul`: off-block entries vanish on both sides (with blocks swapped);
on-block entries are the ten star-entry lemmas. -/
theorem pi0_afStar (a : AF) : pi0 (afStar a) = (pi0 a)ᴴ := by
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
          exact pi0_star_entry_leptonL a ⟨i.val, hi2⟩ ⟨j.val, hj2⟩
        · have hns : ¬ sameBlock i j := not_sameBlock_of_HL_mixed (Or.inl ⟨hi2, by omega, hj⟩)
          have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
          rw [pi0_entry_eq_zero_of_not_sameBlock (afStar a) hns,
            pi0_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
      · by_cases hj2 : j.val < 2
        · have hns : ¬ sameBlock i j := not_sameBlock_of_HL_mixed (Or.inr ⟨by omega, hi, hj2⟩)
          have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
          rw [pi0_entry_eq_zero_of_not_sameBlock (afStar a) hns,
            pi0_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
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
          exact pi0_star_entry_quarkL a ⟨(i.val - 2) / 2, by omega⟩
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
            exact pi0_star_entry_nuR a
          · by_cases hj9 : j.val = 9
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed (Or.inl ⟨hi8, hj9⟩)
              have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
              rw [pi0_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                pi0_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                (Or.inr (Or.inr (Or.inl ⟨Or.inl hi8, by omega, hj16⟩)))
              have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
              rw [pi0_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                pi0_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
        · by_cases hi9 : i.val = 9
          · by_cases hj8' : j.val = 8
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed (Or.inr (Or.inl ⟨hi9, hj8'⟩))
              have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
              rw [pi0_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                pi0_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
            · by_cases hj9 : j.val = 9
              · have hsi : (⟨9, by omega⟩ : I32) = i := Fin.ext hi9.symm
                have hsj : (⟨9, by omega⟩ : I32) = j := Fin.ext hj9.symm
                rw [← hsi, ← hsj]
                exact pi0_star_entry_eR a
              · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                  (Or.inr (Or.inr (Or.inl ⟨Or.inr hi9, by omega, hj16⟩)))
                have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
                rw [pi0_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                  pi0_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
          · by_cases hj8' : j.val = 8
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inl hj8'⟩)))
              have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
              rw [pi0_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                pi0_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
            · by_cases hj9 : j.val = 9
              · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                  (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inr hj9⟩)))
                have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
                rw [pi0_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                  pi0_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
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
                exact pi0_star_entry_quarkR a ⟨(i.val - 10) / 2, by omega⟩
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
              exact pi0_star_entry_leptonLc a ⟨i.val - 16, by omega⟩
                ⟨j.val - 16, by omega⟩
            · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                (Or.inl ⟨by omega, hi18, by omega, hj24⟩)
              have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
              rw [pi0_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                pi0_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
          · by_cases hj18 : j.val < 18
            · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                (Or.inr (Or.inl ⟨by omega, hi24, hj16, hj18⟩))
              have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
              rw [pi0_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                pi0_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
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
              exact pi0_star_entry_quarkLc a ⟨(i.val - 18) / 2, by omega⟩
                ⟨(j.val - 18) / 2, by omega⟩ ⟨(i.val - 18) % 2, by omega⟩
                ⟨(j.val - 18) % 2, by omega⟩
        · have hj24 : 24 ≤ j.val := by omega
          by_cases hi24' : i.val = 24
          · by_cases hj24' : j.val = 24
            · have hsi : (⟨24, by omega⟩ : I32) = i := Fin.ext hi24'.symm
              have hsj : (⟨24, by omega⟩ : I32) = j := Fin.ext hj24'.symm
              rw [← hsi, ← hsj]
              exact pi0_star_entry_nuRc a
            · by_cases hj25 : j.val = 25
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inl ⟨hi24', hj25⟩)))))))
                have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
                rw [pi0_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                  pi0_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                  (Or.inr (Or.inr (Or.inl ⟨hi24', by omega⟩)))
                have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
                rw [pi0_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                  pi0_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
          · by_cases hi25 : i.val = 25
            · by_cases hj24' : j.val = 24
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr ⟨hi25, hj24'⟩)))))))
                have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
                rw [pi0_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                  pi0_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
              · by_cases hj25 : j.val = 25
                · have hsi : (⟨25, by omega⟩ : I32) = i := Fin.ext hi25.symm
                  have hsj : (⟨25, by omega⟩ : I32) = j := Fin.ext hj25.symm
                  rw [← hsi, ← hsj]
                  exact pi0_star_entry_eRc a
                · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                    (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi25, by omega⟩))))
                  have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
                  rw [pi0_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                    pi0_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
            · by_cases hj24' : j.val = 24
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inl ⟨by omega, hj24'⟩)))))
                have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
                rw [pi0_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                  pi0_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
              · by_cases hj25 : j.val = 25
                · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inl ⟨by omega, hj25⟩))))))
                  have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
                  rw [pi0_entry_eq_zero_of_not_sameBlock (afStar a) hns,
                    pi0_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]
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
                  exact pi0_star_entry_quarkRc a ⟨(i.val - 26) / 2, by omega⟩
                    ⟨(j.val - 26) / 2, by omega⟩ ⟨(i.val - 26) % 2, by omega⟩
                    ⟨(j.val - 26) % 2, by omega⟩
  · have hns : ¬ sameBlock i j := not_sameBlock_of_ne_sector hsec
    have hnsji : ¬ sameBlock j i := fun hjj => hns (sameBlock_symm hjj)
    rw [pi0_entry_eq_zero_of_not_sameBlock (afStar a) hns,
      pi0_entry_eq_zero_of_not_sameBlock a hnsji, star_zero]

/-! ## §4. Faithfulness (T2)

The kernel of `pi0` is trivial: the three components are read off at three
seats — `λ` at the ν_R singlet slot 8, `q` on the lepton doublet, and `m`
naked at the right-antiquark block (slots 26–31), where no other factor
dresses it. The contrast is the point: Option-A's `pi_ker_iff` puts pure
color in the kernel. -/

theorem pi0_ker_iff (a : AF) : pi0 a = 0 ↔ a = afZero := by
  constructor
  · intro h
    rw [ext_iff]
    refine ⟨?_, ?_, ?_⟩
    · have h8 : pi0 a ⟨8, by omega⟩ ⟨8, by omega⟩ = 0 := by rw [h, Matrix.zero_apply]
      rw [pi0_entry_nuR] at h8
      rw [afZero_u1]
      exact h8
    · ext s t
      have hs : pi0 a ⟨s.val, by omega⟩ ⟨t.val, by omega⟩ = 0 := by
        rw [h, Matrix.zero_apply]
      rw [pi0_entry_leptonL] at hs
      rw [afZero_q, Matrix.zero_apply]
      exact hs
    · ext c c'
      have hc : pi0 a ⟨26 + 2 * c.val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩
          ⟨26 + 2 * c'.val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩ = 0 := by
        rw [h, Matrix.zero_apply]
      rw [pi0_entry_quarkRc, if_pos rfl] at hc
      rw [afZero_color, Matrix.zero_apply]
      exact hc
  · intro h
    rw [h]
    exact pi0_zero

theorem pi0_eq_iff (a b : AF) : pi0 a = pi0 b ↔ a = b := by
  constructor
  · intro h
    rw [ext_iff]
    refine ⟨?_, ?_, ?_⟩
    · have h8 : pi0 a ⟨8, by omega⟩ ⟨8, by omega⟩
          = pi0 b ⟨8, by omega⟩ ⟨8, by omega⟩ := by rw [h]
      rwa [pi0_entry_nuR, pi0_entry_nuR] at h8
    · ext s t
      have hs : pi0 a ⟨s.val, by omega⟩ ⟨t.val, by omega⟩
          = pi0 b ⟨s.val, by omega⟩ ⟨t.val, by omega⟩ := by rw [h]
      rwa [pi0_entry_leptonL, pi0_entry_leptonL] at hs
    · ext c c'
      have hc : pi0 a ⟨26 + 2 * c.val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩
            ⟨26 + 2 * c'.val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩
          = pi0 b ⟨26 + 2 * c.val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩
            ⟨26 + 2 * c'.val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩ := by rw [h]
      rwa [pi0_entry_quarkRc, pi0_entry_quarkRc, if_pos rfl, if_pos rfl] at hc
  · intro h
    rw [h]

theorem pi0_injective : Function.Injective pi0 :=
  fun a b h => (pi0_eq_iff a b).mp h

/-- Pure color is read off nakedly at the right-antiquark block. -/
theorem pi0_pure_color_entry (m : Matrix I3 I3 ℂ) (c c' : Fin 3) :
    pi0 ⟨0, 0, m⟩ ⟨26 + 2 * c.val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩
        ⟨26 + 2 * c'.val + (⟨0, by omega⟩ : Fin 2).val, by omega⟩ = m c c' := by
  rw [pi0_entry_quarkRc, if_pos rfl]

/-- T2 in words: a pure-color element with `m ≠ 0` represents nontrivially —
under Option-A it would be in the kernel. -/
theorem pi0_pure_color_ne_zero (m : Matrix I3 I3 ℂ) (hm : m ≠ 0) :
    pi0 ⟨0, 0, m⟩ ≠ 0 := by
  intro h
  apply hm
  ext c c'
  have e := pi0_pure_color_entry m c c'
  rw [h, Matrix.zero_apply] at e
  exact e.symm

/-! ## §5. The e_L sector (T3), the additivity obstruction, and the escape

Under `pi0`, the ℂ-summand's element `⟨lam, 1, 1⟩` acts on the e_L sector
(slots {1, 17} — particle and antiparticle) as diag(1, `star lam`): the
antiparticle entry is `star lam`, NON-trivial (T3 stands in sector form).
The particle entry is `1`, and the obstruction theorem below shows this is
FORCED in any representation that is additive and multiplicative and seats
ℍ on the left doublets as the corpus does: the annihilation
`afMul ⟨lam,0,0⟩ ⟨0,1,0⟩ = afZero` pins it. `pi0` escapes at the
antiparticle slot only by failing additivity (`pi0_not_additive`), and the
failure sits exactly in the antilepton block, whose entry
`star lam * star (q s t)` is bilinear — not additive — in `(lam, q)`. -/

/-- The e_L particle entry of the ℂ-U(1): `1` (forced, see the obstruction). -/
theorem pi0_u1_eL_particle_entry (lam : ℂ) :
    pi0 ⟨lam, 1, 1⟩ ⟨1, by omega⟩ ⟨1, by omega⟩ = 1 := by
  have hs : (⟨(⟨1, by omega⟩ : Fin 2).val, by omega⟩ : I32) = ⟨1, by omega⟩ :=
    Fin.ext (show (⟨1, by omega⟩ : Fin 2).val = 1 from rfl)
  rw [← hs, pi0_entry_leptonL]
  show (1 : Matrix I2 I2 ℂ) (⟨1, by omega⟩ : Fin 2) (⟨1, by omega⟩ : Fin 2) = 1
  rw [Matrix.one_apply, if_pos rfl]

/-- The e_L antiparticle entry of the ℂ-U(1): `star lam` — the Option-A
obstruction is gone on the sector. -/
theorem pi0_u1_eL_antiparticle_entry (lam : ℂ) :
    pi0 ⟨lam, 1, 1⟩ ⟨17, by omega⟩ ⟨17, by omega⟩ = star lam := by
  have hs : (⟨16 + (⟨1, by omega⟩ : Fin 2).val, by omega⟩ : I32) = ⟨17, by omega⟩ :=
    Fin.ext (show 16 + (⟨1, by omega⟩ : Fin 2).val = 17 from rfl)
  rw [← hs, pi0_entry_leptonLc]
  show star lam * star ((1 : Matrix I2 I2 ℂ) (⟨1, by omega⟩ : Fin 2)
    (⟨1, by omega⟩ : Fin 2)) = star lam
  rw [Matrix.one_apply, if_pos rfl, star_one, mul_one]

/-- T3 in one line: at `lam = -1` the represented ℂ-U(1) element is not the
identity — its e_L antiparticle entry is `-1`. -/
theorem pi0_u1_eL_nontrivial : pi0 ⟨(-1 : ℂ), 1, 1⟩ ≠ 1 := by
  intro h
  have e : pi0 ⟨(-1 : ℂ), 1, 1⟩ ⟨17, by omega⟩ ⟨17, by omega⟩
      = (1 : Matrix I32 I32 ℂ) ⟨17, by omega⟩ ⟨17, by omega⟩ := by rw [h]
  rw [pi0_u1_eL_antiparticle_entry, Matrix.one_apply, if_pos rfl] at e
  rw [star_neg, star_one] at e
  exact (by norm_num [Complex.ext_iff] : (-1 : ℂ) ≠ 1) e

/-- The obstruction: in ANY additive, multiplicative representation seating
ℍ on the left doublet (`hSeat` on the doublet, `hSeat0` off it — both hold
for `pi0` itself and for the corpus's seatings), the ℂ-U(1) is trivial at
the e_L particle slot. Hence T3's particle-slot reading is impossible for
an algebra representation in the full (additive) sense; `pi0`'s escape is
exactly its failure of additivity. -/
theorem additive_rep_u1_eL_trivial
    (ρ : AF → Matrix I32 I32 ℂ)
    (hMul : ∀ a b, ρ (afMul a b) = ρ a * ρ b)
    (hAdd : ∀ a b, ρ (afAdd a b) = ρ a + ρ b)
    (hSeat : ∀ (q : Matrix I2 I2 ℂ) (s t : Fin 2),
      ρ ⟨0, q, 0⟩ ⟨s.val, by omega⟩ ⟨t.val, by omega⟩ = q s t)
    (hSeat0 : ∀ (q : Matrix I2 I2 ℂ) (k : I32) (t : Fin 2), 2 ≤ k.val →
      ρ ⟨0, q, 0⟩ k ⟨t.val, by omega⟩ = 0)
    (lam : ℂ) :
    ρ ⟨lam, 1, 1⟩ ⟨1, by omega⟩ ⟨1, by omega⟩ = 1 := by
  have hzz : afAdd afZero afZero = afZero := by
    rw [ext_iff]
    exact ⟨by simp [afAdd_u1, afZero_u1], by simp [afAdd_q, afZero_q],
      by simp [afAdd_color, afZero_color]⟩
  have hρ0 : ρ afZero = 0 := by
    have e := hAdd afZero afZero
    rw [hzz] at e
    exact add_eq_left.mp e.symm
  have hm1 : afMul ⟨lam, 0, 0⟩ ⟨0, 1, 0⟩ = afZero := by
    rw [ext_iff]
    exact ⟨by simp [afMul_u1, afZero_u1], by simp [afMul_q, afZero_q],
      by simp [afMul_color, afZero_color]⟩
  have hm2 : afMul ⟨0, 0, 1⟩ ⟨0, 1, 0⟩ = afZero := by
    rw [ext_iff]
    exact ⟨by simp [afMul_u1, afZero_u1], by simp [afMul_q, afZero_q],
      by simp [afMul_color, afZero_color]⟩
  have hslot : (⟨(⟨1, by omega⟩ : Fin 2).val, by omega⟩ : I32) = ⟨1, by omega⟩ :=
    Fin.ext rfl
  have key : ∀ x : AF, ρ x * ρ ⟨0, 1, 0⟩ = 0 →
      ρ x ⟨1, by omega⟩ ⟨1, by omega⟩ = 0 := by
    intro x hx
    have e : (ρ x * ρ ⟨0, 1, 0⟩) ⟨(⟨1, by omega⟩ : Fin 2).val, by omega⟩
        ⟨(⟨1, by omega⟩ : Fin 2).val, by omega⟩ = 0 := by
      rw [hx, Matrix.zero_apply]
    rw [Matrix.mul_apply] at e
    have hvan : ∀ k : I32, k ∉ ({⟨(⟨0, by omega⟩ : Fin 2).val, by omega⟩,
        ⟨(⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) →
        ρ x ⟨(⟨1, by omega⟩ : Fin 2).val, by omega⟩ k *
          ρ ⟨0, 1, 0⟩ k ⟨(⟨1, by omega⟩ : Fin 2).val, by omega⟩ = 0 := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      have hk2 : 2 ≤ k.val := by
        by_contra hlt
        push_neg at hlt
        have h01 : k.val = 0 ∨ k.val = 1 := by omega
        rcases h01 with h0 | h1
        · exact absurd (Fin.ext (show k.val = (⟨0, by omega⟩ : Fin 2).val from h0)) hk.1
        · exact absurd (Fin.ext (show k.val = (⟨1, by omega⟩ : Fin 2).val from h1)) hk.2
      rw [hSeat0 1 k ⟨1, by omega⟩ hk2, mul_zero]
    rw [sum_eq_of_vanish_outside hvan,
      Finset.sum_pair (show (⟨(⟨0, by omega⟩ : Fin 2).val, by omega⟩ : I32)
        ≠ ⟨(⟨1, by omega⟩ : Fin 2).val, by omega⟩
        from (by decide : (⟨0, by omega⟩ : I32) ≠ ⟨1, by omega⟩))] at e
    rw [hSeat 1 ⟨0, by omega⟩ ⟨1, by omega⟩,
      hSeat 1 ⟨1, by omega⟩ ⟨1, by omega⟩] at e
    rw [Matrix.one_apply, Matrix.one_apply,
      if_neg (by decide : ¬ (⟨0, by omega⟩ : Fin 2) = ⟨1, by omega⟩), if_pos rfl,
      mul_zero, mul_one, zero_add] at e
    rwa [hslot] at e
  have hρe : ρ ⟨lam, 0, 0⟩ ⟨1, by omega⟩ ⟨1, by omega⟩ = 0 :=
    key _ (by rw [← hMul, hm1, hρ0])
  have hρw : ρ ⟨0, 0, 1⟩ ⟨1, by omega⟩ ⟨1, by omega⟩ = 0 :=
    key _ (by rw [← hMul, hm2, hρ0])
  have hρu : ρ ⟨0, 1, 0⟩ ⟨1, by omega⟩ ⟨1, by omega⟩ = 1 := by
    have h := hSeat 1 ⟨1, by omega⟩ ⟨1, by omega⟩
    rw [Matrix.one_apply, if_pos rfl, hslot] at h
    exact h
  have hd1 : afAdd ⟨lam, 0, 0⟩ ⟨0, 1, 1⟩ = ⟨lam, 1, 1⟩ := by
    rw [ext_iff]
    exact ⟨by simp [afAdd_u1], by simp [afAdd_q], by simp [afAdd_color]⟩
  have hd2 : afAdd ⟨0, 1, 0⟩ ⟨0, 0, 1⟩ = ⟨0, 1, 1⟩ := by
    rw [ext_iff]
    exact ⟨by simp [afAdd_u1], by simp [afAdd_q], by simp [afAdd_color]⟩
  have e : ρ ⟨lam, 1, 1⟩ ⟨1, by omega⟩ ⟨1, by omega⟩
      = (ρ ⟨lam, 0, 0⟩ + (ρ ⟨0, 1, 0⟩ + ρ ⟨0, 0, 1⟩)) ⟨1, by omega⟩ ⟨1, by omega⟩ := by
    rw [← hd1, hAdd, ← hd2, hAdd]
  rw [e, Matrix.add_apply, Matrix.add_apply, hρe, hρu, hρw, add_zero, zero_add]

/-- `pi0` is not additive: at the antilepton slot 16 the represented sum
`⟨1,0,0⟩ + ⟨0,1,0⟩` has entry `1`, while the sum of the represented entries
is `0 + 0`. The bilinear antilepton block is the exact obstruction point. -/
theorem pi0_not_additive : ¬ ∀ a b, pi0 (afAdd a b) = pi0 a + pi0 b := by
  intro h
  have e : pi0 (afAdd ⟨1, 0, 0⟩ ⟨0, 1, 0⟩) ⟨16, by omega⟩ ⟨16, by omega⟩
      = (pi0 ⟨1, 0, 0⟩ + pi0 ⟨0, 1, 0⟩) ⟨16, by omega⟩ ⟨16, by omega⟩ := by
    rw [h]
  have hs : (⟨16 + (⟨0, by omega⟩ : Fin 2).val, by omega⟩ : I32) = ⟨16, by omega⟩ :=
    Fin.ext rfl
  rw [← hs, Matrix.add_apply, pi0_entry_leptonLc, pi0_entry_leptonLc,
    pi0_entry_leptonLc] at e
  simp at e

/-! ## §6. Grading compatibility

`pi0` is even for the corpus grading `gammaF`: the support of `pi0 a` lies
inside the four 8-sectors and `gammaF` is constant on each sector, so the
two products agree entrywise. First-order compatibility is NOT attempted
in this module; §7 shows order-zero already fails. -/

theorem gammaF_diag_eq_of_same_sector {i j : I32} (h : i.val / 8 = j.val / 8) :
    gammaF i i = gammaF j j := by
  have gi : gammaF i i = (if i.val < 8 then (1:ℂ) else if i.val < 16 then -1
      else if i.val < 24 then -1 else 1) := by
    unfold gammaF; simp
  have gj : gammaF j j = (if j.val < 8 then (1:ℂ) else if j.val < 16 then -1
      else if j.val < 24 then -1 else 1) := by
    unfold gammaF; simp
  rw [gi, gj]
  by_cases h1 : i.val < 8
  · have hj1 : j.val < 8 := by omega
    simp [h1, hj1]
  · by_cases h2 : i.val < 16
    · have hj1 : ¬ j.val < 8 := by omega
      have hj2 : j.val < 16 := by omega
      simp [h1, h2, hj1, hj2]
    · by_cases h3 : i.val < 24
      · have hj1 : ¬ j.val < 8 := by omega
        have hj2 : ¬ j.val < 16 := by omega
        have hj3 : j.val < 24 := by omega
        simp [h1, h2, h3, hj1, hj2, hj3]
      · have hj1 : ¬ j.val < 8 := by omega
        have hj2 : ¬ j.val < 16 := by omega
        have hj3 : ¬ j.val < 24 := by omega
        simp [h1, h2, h3, hj1, hj2, hj3]

theorem pi0_support_sector {a : AF} {i j : I32} (h : pi0 a i j ≠ 0) :
    i.val / 8 = j.val / 8 := by
  by_contra hne
  exact h (pi0_entry_cross_sector a hne)

/-- T1 (grading part): `pi0 a` commutes with the grading. -/
theorem pi0_grading_even (a : AF) : gammaF * pi0 a = pi0 a * gammaF := by
  ext i j
  rw [gammaF_mul_apply, mul_gammaF_apply]
  by_cases h : pi0 a i j = 0
  · rw [h, mul_zero, zero_mul]
  · have hsec := pi0_support_sector h
    rw [gammaF_diag_eq_of_same_sector hsec]
    exact mul_comm _ _

/-! ## §7. Order-zero fails for `pi0` (proved negative result)

With the corpus's opposite representation `piOp`, order-zero for `pi0`
would require `pi0 a * piOp (pi0 b) = piOp (pi0 b) * pi0 a` for all `a b`.
It fails already on the lepton doublet: for `a = ⟨0, q_a, 0⟩` with
`q_a = !![0, 1; -1, 0]` and `b = ⟨1, q_b, 0⟩` with
`q_b = !![I, 0; 0, -I]`, the `(0, 1)` entries of the two products are
`I` and `-I`. The mechanism is visible in §3's design: `pi0`'s ℍ acts on
the doublet while the ℂ-dressed antiparticle copy of the same doublet sits
in the opposite representation's seat, and the two actions do not commute.
First-order compatibility is therefore moot for `pi0` and is recorded as
NOT ATTEMPTED (it presupposes order-zero in the corpus's usage). -/

theorem piOp_apply (M : Matrix I32 I32 ℂ) (i j : I32) :
    piOp M i j = M (partner j) (partner i) := by
  rw [piOp_def_check, UJ_conj_apply, Matrix.transpose_apply]

theorem partner_slot0 :
    partner ⟨(⟨0, by omega⟩ : Fin 2).val, by omega⟩ = ⟨16, by omega⟩ := by
  apply Fin.ext
  simp [partner_val_eq]

theorem partner_slot1 :
    partner ⟨(⟨1, by omega⟩ : Fin 2).val, by omega⟩ = ⟨17, by omega⟩ := by
  apply Fin.ext
  simp [partner_val_eq]

theorem pi0_order_zero_fails :
    ∃ a b : AF, pi0 a * piOp (pi0 b) ≠ piOp (pi0 b) * pi0 a := by
  refine ⟨⟨0, !![0, 1; -1, 0], 0⟩, ⟨1, !![Complex.I, 0; 0, -Complex.I], 0⟩, ?_⟩
  intro h
  have hstarI : star (-Complex.I : ℂ) = Complex.I := by
    rw [← starRingEnd_apply, map_neg, Complex.ext_iff]
    simp
  have hs0 : (⟨(⟨0, by omega⟩ : Fin 2).val, by omega⟩ : I32) = ⟨0, by omega⟩ :=
    Fin.ext rfl
  have hs1 : (⟨(⟨1, by omega⟩ : Fin 2).val, by omega⟩ : I32) = ⟨1, by omega⟩ :=
    Fin.ext rfl
  have hs16 : (⟨16 + (⟨0, by omega⟩ : Fin 2).val, by decide⟩ : I32)
      = ⟨16, by omega⟩ :=
    Fin.ext (show 16 + (⟨0, by omega⟩ : Fin 2).val = 16 from rfl)
  have hs17 : (⟨16 + (⟨1, by omega⟩ : Fin 2).val, by decide⟩ : I32)
      = ⟨17, by omega⟩ := Fin.ext (show 16 + (⟨1, by omega⟩ : Fin 2).val = 17 from rfl)
  have e : (pi0 ⟨0, !![0, 1; -1, 0], 0⟩
        * piOp (pi0 ⟨1, !![Complex.I, 0; 0, -Complex.I], 0⟩))
        ⟨0, by omega⟩ ⟨1, by omega⟩
      = (piOp (pi0 ⟨1, !![Complex.I, 0; 0, -Complex.I], 0⟩)
        * pi0 ⟨0, !![0, 1; -1, 0], 0⟩) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
    rw [h]
  rw [← hs0, ← hs1] at e
  have hL : (pi0 ⟨0, !![0, 1; -1, 0], 0⟩
        * piOp (pi0 ⟨1, !![Complex.I, 0; 0, -Complex.I], 0⟩))
        ⟨(⟨0, by omega⟩ : Fin 2).val, by omega⟩ ⟨(⟨1, by omega⟩ : Fin 2).val, by omega⟩
      = Complex.I := by
    rw [Matrix.mul_apply]
    have hvan : ∀ k : I32, k ∉ ({⟨(⟨0, by omega⟩ : Fin 2).val, by omega⟩,
        ⟨(⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) →
        pi0 ⟨0, !![0, 1; -1, 0], 0⟩ ⟨(⟨0, by omega⟩ : Fin 2).val, by omega⟩ k *
          piOp (pi0 ⟨1, !![Complex.I, 0; 0, -Complex.I], 0⟩) k
            ⟨(⟨1, by omega⟩ : Fin 2).val, by omega⟩ = 0 := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      by_cases hk8 : k.val < 8
      · by_cases hk2 : 2 ≤ k.val
        · rw [pi0_entry_HL_mixed (i := ⟨(⟨0, by omega⟩ : Fin 2).val, by omega⟩)
            (j := k) ⟨0, !![0, 1; -1, 0], 0⟩
            (Or.inl ⟨(⟨0, by omega⟩ : Fin 2).isLt, hk2, hk8⟩), zero_mul]
        · have hk2' : k.val < 2 := not_le.mp hk2
          have h01 : k.val = 0 ∨ k.val = 1 := by omega
          rcases h01 with h0 | h1
          · exact absurd (Fin.ext (show k.val = (⟨0, by omega⟩ : Fin 2).val from h0)) hk.1
          · exact absurd (Fin.ext (show k.val = (⟨1, by omega⟩ : Fin 2).val from h1)) hk.2
      · rw [pi0_entry_cross_sector (i := ⟨(⟨0, by omega⟩ : Fin 2).val, by omega⟩)
          (j := k) ⟨0, !![0, 1; -1, 0], 0⟩
          (by show (0:ℕ) / 8 ≠ k.val / 8; omega), zero_mul]
    rw [sum_eq_of_vanish_outside hvan,
      Finset.sum_pair (show (⟨(⟨0, by omega⟩ : Fin 2).val, by omega⟩ : I32)
        ≠ ⟨(⟨1, by omega⟩ : Fin 2).val, by omega⟩
        from (by decide : (⟨0, by omega⟩ : I32) ≠ ⟨1, by omega⟩)),
      pi0_entry_leptonL, pi0_entry_leptonL, piOp_apply, piOp_apply,
      partner_slot0, partner_slot1, ← hs16, ← hs17,
      pi0_entry_leptonLc, pi0_entry_leptonLc, fin2_mk0, fin2_mk1]
    simp [hstarI]
  have hR : (piOp (pi0 ⟨1, !![Complex.I, 0; 0, -Complex.I], 0⟩)
        * pi0 ⟨0, !![0, 1; -1, 0], 0⟩)
        ⟨(⟨0, by omega⟩ : Fin 2).val, by omega⟩ ⟨(⟨1, by omega⟩ : Fin 2).val, by omega⟩
      = -Complex.I := by
    rw [Matrix.mul_apply]
    have hvan : ∀ k : I32, k ∉ ({⟨(⟨0, by omega⟩ : Fin 2).val, by omega⟩,
        ⟨(⟨1, by omega⟩ : Fin 2).val, by omega⟩} : Finset I32) →
        piOp (pi0 ⟨1, !![Complex.I, 0; 0, -Complex.I], 0⟩)
            ⟨(⟨0, by omega⟩ : Fin 2).val, by omega⟩ k *
          pi0 ⟨0, !![0, 1; -1, 0], 0⟩ k ⟨(⟨1, by omega⟩ : Fin 2).val, by omega⟩
          = 0 := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      by_cases hk8 : k.val < 8
      · by_cases hk2 : 2 ≤ k.val
        · rw [pi0_entry_HL_mixed (i := k)
            (j := ⟨(⟨1, by omega⟩ : Fin 2).val, by omega⟩) ⟨0, !![0, 1; -1, 0], 0⟩
            (Or.inr ⟨hk2, hk8, (⟨1, by omega⟩ : Fin 2).isLt⟩), mul_zero]
        · have hk2' : k.val < 2 := not_le.mp hk2
          have h01 : k.val = 0 ∨ k.val = 1 := by omega
          rcases h01 with h0 | h1
          · exact absurd (Fin.ext (show k.val = (⟨0, by omega⟩ : Fin 2).val from h0)) hk.1
          · exact absurd (Fin.ext (show k.val = (⟨1, by omega⟩ : Fin 2).val from h1)) hk.2
      · rw [pi0_entry_cross_sector (i := k)
          (j := ⟨(⟨1, by omega⟩ : Fin 2).val, by omega⟩) ⟨0, !![0, 1; -1, 0], 0⟩
          (by show k.val / 8 ≠ (1:ℕ) / 8; omega), mul_zero]
    rw [sum_eq_of_vanish_outside hvan,
      Finset.sum_pair (show (⟨(⟨0, by omega⟩ : Fin 2).val, by omega⟩ : I32)
        ≠ ⟨(⟨1, by omega⟩ : Fin 2).val, by omega⟩
        from (by decide : (⟨0, by omega⟩ : I32) ≠ ⟨1, by omega⟩)),
      piOp_apply, piOp_apply, partner_slot0, partner_slot1, ← hs16, ← hs17,
      pi0_entry_leptonLc, pi0_entry_leptonLc, pi0_entry_leptonL, pi0_entry_leptonL,
      fin2_mk0, fin2_mk1]
    simp
  rw [hL, hR] at e
  norm_num [Complex.ext_iff] at e

/-! ## §8. The diagonal form, unimodularity, and the hypercharge pattern (T4)

For elements of the form `⟨lam, 1, c • 1⟩` — the identity in the quaternion
factor and a scalar in the color factor — `π₀` is DIAGONAL, with the explicit
diagonal `pi0Diag lam c` below (proved as `pi0_eq_diagonal` by the same
38-leaf case tree as multiplicativity). Reading the diagonal:

* left particles: `1` (the quaternion factor contributes `q = 1`);
* `ν_R`: `lam`; `e_R`: `star lam`; right quarks: `lam` at isospin `0`,
  `star lam` at isospin `1`;
* left antileptons: `star lam`; left antiquarks and right antiquarks: `c`.

The one-parameter subgroup `u1Param t = ⟨exp (3 t i), 1, exp (t i) • 1⟩`
is exactly the unimodular direction: the product of its diagonal entries
is `exp ((∑ᵢ W i) · t i)` with integer weights `W` summing to `0`
(`sum_W`, by `decide`), so `det (π₀ (u1Param t)) = 1`
(`pi0_det_unimodular`).

THE T4 STATEMENT AND ITS FACE DISCLOSURE (per the charter): the lifted
eigenvalue of the surviving generator on a fermion sector `f` is
`(π₀ u · piOp (π₀ u)) (slot f) (slot f)`. The theorem
`pi0_hypercharge_pattern` states this equals `exp (3 · t · i · Y f)` for
every sector `f`, where `Y = SMFermions.hypercharge` is the corpus's T2
hypercharge table (SMGaugeAlgebra). The statement therefore IMPORTS the
Y table at sector level — that import is declared here, on the module's
face, as the charter requires. What is PROVED (T1) is that the ratio
pattern is exactly the table's, with the single normalization `3` forced
by unimodularity (the direction `α = 3β`); no sector deviates. -/

/-- The diagonal value of `π₀ ⟨lam, 1, c • 1⟩` at slot value `v`. -/
def pi0DiagVal (lam c : ℂ) (v : ℕ) : ℂ :=
  if v < 8 then 1
  else if v = 8 then lam
  else if v = 9 then star lam
  else if v < 16 then (if (v - 10) % 2 = 0 then lam else star lam)
  else if v < 18 then star lam
  else if v < 24 then c
  else if v < 26 then star lam
  else c

/-- The diagonal of `π₀ ⟨lam, 1, c • 1⟩`, as a function on slots. -/
def pi0Diag (lam c : ℂ) (i : I32) : ℂ := pi0DiagVal lam c i.val

theorem pi0DiagVal_leptonL (lam c : ℂ) (s : Fin 2) :
    pi0DiagVal lam c s.val = 1 := by
  unfold pi0DiagVal
  rw [if_pos (by have hs := s.isLt; omega)]

theorem pi0DiagVal_quarkL (lam c : ℂ) (k : Fin 3) (s : Fin 2) :
    pi0DiagVal lam c (2 + 2 * k.val + s.val) = 1 := by
  unfold pi0DiagVal
  rw [if_pos (by have hk := k.isLt; have hs := s.isLt; omega)]

theorem pi0DiagVal_nuR (lam c : ℂ) :
    pi0DiagVal lam c 8 = lam := by
  unfold pi0DiagVal
  rw [if_neg (by norm_num), if_pos (by norm_num)]

theorem pi0DiagVal_eR (lam c : ℂ) :
    pi0DiagVal lam c 9 = star lam := by
  unfold pi0DiagVal
  rw [if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num)]

theorem pi0DiagVal_quarkR (lam c : ℂ) (k : Fin 3) (s : Fin 2) :
    pi0DiagVal lam c (10 + 2 * k.val + s.val)
      = if s.val % 2 = 0 then lam else star lam := by
  have hk := k.isLt
  have hs := s.isLt
  unfold pi0DiagVal
  by_cases hs2 : s.val % 2 = 0
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (by omega), if_pos (by omega), if_pos hs2]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (by omega), if_neg (by omega), if_neg hs2]

theorem pi0DiagVal_leptonLc (lam c : ℂ) (s : Fin 2) :
    pi0DiagVal lam c (16 + s.val) = star lam := by
  have hs := s.isLt
  unfold pi0DiagVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega)]

theorem pi0DiagVal_quarkLc (lam c : ℂ) (k : Fin 3) (s : Fin 2) :
    pi0DiagVal lam c (18 + 2 * k.val + s.val) = c := by
  have hk := k.isLt
  have hs := s.isLt
  unfold pi0DiagVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos (by omega)]

theorem pi0DiagVal_nuRc (lam c : ℂ) :
    pi0DiagVal lam c 24 = star lam := by
  unfold pi0DiagVal
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
    if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
    if_pos (by norm_num)]

theorem pi0DiagVal_eRc (lam c : ℂ) :
    pi0DiagVal lam c 25 = star lam := by
  unfold pi0DiagVal
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
    if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
    if_pos (by norm_num)]

theorem pi0DiagVal_quarkRc (lam c : ℂ) (k : Fin 3) (s : Fin 2) :
    pi0DiagVal lam c (26 + 2 * k.val + s.val) = c := by
  have hk := k.isLt
  have hs := s.isLt
  unfold pi0DiagVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

/-- The diagonal entries of `π₀ ⟨lam, 1, c • 1⟩`: left leptons. -/
theorem pi0_diag_entry_leptonL (lam c : ℂ) (s : Fin 2) :
    pi0 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
        (⟨s.val, by omega⟩ : I32) ⟨s.val, by omega⟩
      = pi0Diag lam c ⟨s.val, by omega⟩ := by
  rw [pi0_entry_leptonL]
  show (1 : Matrix I2 I2 ℂ) s s = pi0DiagVal lam c s.val
  rw [Matrix.one_apply_eq, pi0DiagVal_leptonL]

/-- The diagonal entries of `π₀ ⟨lam, 1, c • 1⟩`: left quarks. -/
theorem pi0_diag_entry_quarkL (lam c : ℂ) (k : Fin 3) (s : Fin 2) :
    pi0 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
        (⟨2 + 2 * k.val + s.val, by omega⟩ : I32)
        ⟨2 + 2 * k.val + s.val, by omega⟩
      = pi0Diag lam c ⟨2 + 2 * k.val + s.val, by omega⟩ := by
  rw [pi0_entry_quarkL, if_pos rfl]
  show (1 : Matrix I2 I2 ℂ) s s = pi0DiagVal lam c (2 + 2 * k.val + s.val)
  rw [Matrix.one_apply_eq, pi0DiagVal_quarkL]

/-- The diagonal entries of `π₀ ⟨lam, 1, c • 1⟩`: `ν_R`. -/
theorem pi0_diag_entry_nuR (lam c : ℂ) :
    pi0 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
        (⟨8, by omega⟩ : I32) ⟨8, by omega⟩
      = pi0Diag lam c ⟨8, by omega⟩ := by
  rw [pi0_entry_nuR]
  show lam = pi0DiagVal lam c 8
  rw [pi0DiagVal_nuR]

/-- The diagonal entries of `π₀ ⟨lam, 1, c • 1⟩`: `e_R`. -/
theorem pi0_diag_entry_eR (lam c : ℂ) :
    pi0 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
        (⟨9, by omega⟩ : I32) ⟨9, by omega⟩
      = pi0Diag lam c ⟨9, by omega⟩ := by
  rw [pi0_entry_eR]
  show star lam = pi0DiagVal lam c 9
  rw [pi0DiagVal_eR]

/-- The diagonal entries of `π₀ ⟨lam, 1, c • 1⟩`: right quarks. -/
theorem pi0_diag_entry_quarkR (lam c : ℂ) (k : Fin 3) (s : Fin 2) :
    pi0 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
        (⟨10 + 2 * k.val + s.val, by omega⟩ : I32)
        ⟨10 + 2 * k.val + s.val, by omega⟩
      = pi0Diag lam c ⟨10 + 2 * k.val + s.val, by omega⟩ := by
  rw [pi0_entry_quarkR, if_pos ⟨rfl, rfl⟩]
  show (if s = 0 then lam else star lam)
    = pi0DiagVal lam c (10 + 2 * k.val + s.val)
  rw [pi0DiagVal_quarkR]
  by_cases hs0 : s = 0
  · rw [if_pos hs0, if_pos (by
      have hv : s.val = 0 := congrArg Fin.val hs0
      omega)]
  · have hv0 : s.val ≠ 0 :=
      fun hv => hs0 (Fin.ext (show s.val = (0 : Fin 2).val from hv))
    have hs1 : s.val = 1 := by have hs := s.isLt; omega
    rw [if_neg hs0, if_neg (by omega)]

/-- The diagonal entries of `π₀ ⟨lam, 1, c • 1⟩`: left antileptons. -/
theorem pi0_diag_entry_leptonLc (lam c : ℂ) (s : Fin 2) :
    pi0 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
        (⟨16 + s.val, by omega⟩ : I32) ⟨16 + s.val, by omega⟩
      = pi0Diag lam c ⟨16 + s.val, by omega⟩ := by
  rw [pi0_entry_leptonLc]
  show star lam * star ((1 : Matrix I2 I2 ℂ) s s)
    = pi0DiagVal lam c (16 + s.val)
  rw [Matrix.one_apply_eq, star_one, mul_one, pi0DiagVal_leptonLc]

/-- The diagonal entries of `π₀ ⟨lam, 1, c • 1⟩`: left antiquarks. -/
theorem pi0_diag_entry_quarkLc (lam c : ℂ) (k : Fin 3) (s : Fin 2) :
    pi0 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
        (⟨18 + 2 * k.val + s.val, by omega⟩ : I32)
        ⟨18 + 2 * k.val + s.val, by omega⟩
      = pi0Diag lam c ⟨18 + 2 * k.val + s.val, by omega⟩ := by
  rw [pi0_entry_quarkLc]
  show star ((1 : Matrix I2 I2 ℂ) s s) * (c • (1 : Matrix I3 I3 ℂ)) k k
    = pi0DiagVal lam c (18 + 2 * k.val + s.val)
  rw [Matrix.one_apply_eq, star_one, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, one_mul, pi0DiagVal_quarkLc]

/-- The diagonal entries of `π₀ ⟨lam, 1, c • 1⟩`: `ν_R` antiparticle. -/
theorem pi0_diag_entry_nuRc (lam c : ℂ) :
    pi0 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
        (⟨24, by omega⟩ : I32) ⟨24, by omega⟩
      = pi0Diag lam c ⟨24, by omega⟩ := by
  rw [pi0_entry_nuRc]
  show star lam = pi0DiagVal lam c 24
  rw [pi0DiagVal_nuRc]

/-- The diagonal entries of `π₀ ⟨lam, 1, c • 1⟩`: `e_R` antiparticle. -/
theorem pi0_diag_entry_eRc (lam c : ℂ) :
    pi0 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
        (⟨25, by omega⟩ : I32) ⟨25, by omega⟩
      = pi0Diag lam c ⟨25, by omega⟩ := by
  rw [pi0_entry_eRc]
  show star lam = pi0DiagVal lam c 25
  rw [pi0DiagVal_eRc]

/-- The diagonal entries of `π₀ ⟨lam, 1, c • 1⟩`: right antiquarks. -/
theorem pi0_diag_entry_quarkRc (lam c : ℂ) (k : Fin 3) (s : Fin 2) :
    pi0 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
        (⟨26 + 2 * k.val + s.val, by omega⟩ : I32)
        ⟨26 + 2 * k.val + s.val, by omega⟩
      = pi0Diag lam c ⟨26 + 2 * k.val + s.val, by omega⟩ := by
  rw [pi0_entry_quarkRc, if_pos rfl]
  show (c • (1 : Matrix I3 I3 ℂ)) k k
    = pi0DiagVal lam c (26 + 2 * k.val + s.val)
  rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    pi0DiagVal_quarkRc]

/-- A matrix whose entries are `w` on the diagonal and `0` off it is
`Matrix.diagonal w`. -/
theorem eq_diagonal_of_entry {M : Matrix I32 I32 ℂ} {w : I32 → ℂ}
    (h : ∀ i j, M i j = if i = j then w i else 0) :
    M = Matrix.diagonal w := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [h, if_pos rfl, Matrix.diagonal_apply_eq]
  · rw [h, if_neg hij, Matrix.diagonal_apply, if_neg hij]
/-- **The diagonal form.** `π₀ ⟨lam, 1, c • 1⟩` is the diagonal
matrix `Matrix.diagonal (pi0Diag lam c)`. Proved by the entry tree
(the same sector tree as `pi0_afMul`): diagonal leaves close by the
`pi0_diag_entry_*` lemmas, off-diagonal leaves by the block
vanishing lemma. -/
theorem pi0_eq_diagonal (lam c : ℂ) :
    pi0 ⟨lam, 1, c • (1 : Matrix I3 I3 ℂ)⟩
      = Matrix.diagonal (pi0Diag lam c) := by
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
            exact pi0_diag_entry_leptonL lam c (⟨j.val, hj2⟩ : Fin 2)
          · have hS : (⟨i.val, hi2⟩ : Fin 2) ≠ (⟨j.val, hj2⟩ : Fin 2) :=
              fun hh => hslot (Fin.ext (show i.val = j.val by
                have hv := congrArg Fin.val hh
                omega))
            rw [pi0_entry_leptonL]
            show (1 : Matrix I2 I2 ℂ) (⟨i.val, hi2⟩ : Fin 2) (⟨j.val, hj2⟩ : Fin 2) = 0
            rw [Matrix.one_apply, if_neg hS]
        · have hns : ¬ sameBlock i j := not_sameBlock_of_HL_mixed (Or.inl ⟨hi2, by omega, hj⟩)
          have hne : i ≠ j := by
            intro hh
            have hv := congrArg Fin.val hh
            omega
          rw [if_neg hne, pi0_entry_eq_zero_of_not_sameBlock _ hns]
      · by_cases hj2 : j.val < 2
        · have hns : ¬ sameBlock i j := not_sameBlock_of_HL_mixed (Or.inr ⟨by omega, hi, hj2⟩)
          have hne : i ≠ j := by
            intro hh
            have hv := congrArg Fin.val hh
            omega
          rw [if_neg hne, pi0_entry_eq_zero_of_not_sameBlock _ hns]
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
            exact pi0_diag_entry_quarkL lam c (⟨(j.val - 2) / 2, by omega⟩ : Fin 3) (⟨(j.val - 2) % 2, by omega⟩ : Fin 2)
          · by_cases hK : (⟨(i.val - 2) / 2, by omega⟩ : Fin 3) = (⟨(j.val - 2) / 2, by omega⟩ : Fin 3)
            · have hS : (⟨(i.val - 2) % 2, by omega⟩ : Fin 2) ≠ (⟨(j.val - 2) % 2, by omega⟩ : Fin 2) :=
                fun hh => hslot (Fin.ext (show
                  2 + 2 * ((⟨(i.val - 2) / 2, by omega⟩ : Fin 3)).val + ((⟨(i.val - 2) % 2, by omega⟩ : Fin 2)).val
                    = 2 + 2 * ((⟨(j.val - 2) / 2, by omega⟩ : Fin 3)).val + ((⟨(j.val - 2) % 2, by omega⟩ : Fin 2)).val by
                  have hv1 := congrArg Fin.val hK
                  have hv2 := congrArg Fin.val hh
                  omega))
              rw [pi0_entry_quarkL, if_pos hK]
              show (1 : Matrix I2 I2 ℂ) (⟨(i.val - 2) % 2, by omega⟩ : Fin 2) (⟨(j.val - 2) % 2, by omega⟩ : Fin 2) = 0
              rw [Matrix.one_apply, if_neg hS]
            · rw [pi0_entry_quarkL, if_neg hK]
    · by_cases hi16 : i.val < 16
      · have hj8 : 8 ≤ j.val := by omega
        have hj16 : j.val < 16 := by omega
        by_cases hi8 : i.val = 8
        · by_cases hj8' : j.val = 8
          · have hsi : (⟨8, by omega⟩ : I32) = i := Fin.ext hi8.symm
            have hsj : (⟨8, by omega⟩ : I32) = j := Fin.ext hj8'.symm
            rw [← hsi, ← hsj]
            split_ifs with hslot
            · exact pi0_diag_entry_nuR lam c
            · exact (hslot rfl).elim
          · by_cases hj9 : j.val = 9
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed (Or.inl ⟨hi8, hj9⟩)
              have hne : i ≠ j := by
                intro hh
                have hv := congrArg Fin.val hh
                omega
              rw [if_neg hne, pi0_entry_eq_zero_of_not_sameBlock _ hns]
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                (Or.inr (Or.inr (Or.inl ⟨Or.inl hi8, by omega, hj16⟩)))
              have hne : i ≠ j := by
                intro hh
                have hv := congrArg Fin.val hh
                omega
              rw [if_neg hne, pi0_entry_eq_zero_of_not_sameBlock _ hns]
        · by_cases hi9 : i.val = 9
          · by_cases hj8' : j.val = 8
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed (Or.inr (Or.inl ⟨hi9, hj8'⟩))
              have hne : i ≠ j := by
                intro hh
                have hv := congrArg Fin.val hh
                omega
              rw [if_neg hne, pi0_entry_eq_zero_of_not_sameBlock _ hns]
            · by_cases hj9 : j.val = 9
              · have hsi : (⟨9, by omega⟩ : I32) = i := Fin.ext hi9.symm
                have hsj : (⟨9, by omega⟩ : I32) = j := Fin.ext hj9.symm
                rw [← hsi, ← hsj]
                split_ifs with hslot
                · exact pi0_diag_entry_eR lam c
                · exact (hslot rfl).elim
              · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                  (Or.inr (Or.inr (Or.inl ⟨Or.inr hi9, by omega, hj16⟩)))
                have hne : i ≠ j := by
                  intro hh
                  have hv := congrArg Fin.val hh
                  omega
                rw [if_neg hne, pi0_entry_eq_zero_of_not_sameBlock _ hns]
          · by_cases hj8' : j.val = 8
            · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inl hj8'⟩)))
              have hne : i ≠ j := by
                intro hh
                have hv := congrArg Fin.val hh
                omega
              rw [if_neg hne, pi0_entry_eq_zero_of_not_sameBlock _ hns]
            · by_cases hj9 : j.val = 9
              · have hns : ¬ sameBlock i j := not_sameBlock_of_HR_mixed
                  (Or.inr (Or.inr (Or.inr ⟨by omega, hi16, Or.inr hj9⟩)))
                have hne : i ≠ j := by
                  intro hh
                  have hv := congrArg Fin.val hh
                  omega
                rw [if_neg hne, pi0_entry_eq_zero_of_not_sameBlock _ hns]
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
                  exact pi0_diag_entry_quarkR lam c (⟨(j.val - 10) / 2, by omega⟩ : Fin 3) (⟨(j.val - 10) % 2, by omega⟩ : Fin 2)
                · by_cases hS : (⟨(i.val - 10) % 2, by omega⟩ : Fin 2) = (⟨(j.val - 10) % 2, by omega⟩ : Fin 2)
                  · have hK : (⟨(i.val - 10) / 2, by omega⟩ : Fin 3) ≠ (⟨(j.val - 10) / 2, by omega⟩ : Fin 3) :=
                      fun hh => hslot (Fin.ext (show
                        10 + 2 * ((⟨(i.val - 10) / 2, by omega⟩ : Fin 3)).val + ((⟨(i.val - 10) % 2, by omega⟩ : Fin 2)).val
                          = 10 + 2 * ((⟨(j.val - 10) / 2, by omega⟩ : Fin 3)).val + ((⟨(j.val - 10) % 2, by omega⟩ : Fin 2)).val by
                        have hv1 := congrArg Fin.val hh
                        have hv2 := congrArg Fin.val hS
                        omega))
                    have hne : ¬ ((⟨(i.val - 10) % 2, by omega⟩ : Fin 2) = (⟨(j.val - 10) % 2, by omega⟩ : Fin 2) ∧ (⟨(i.val - 10) / 2, by omega⟩ : Fin 3) = (⟨(j.val - 10) / 2, by omega⟩ : Fin 3)) := fun hh => hK hh.2
                    rw [pi0_entry_quarkR, if_neg hne]
                  · have hne : ¬ ((⟨(i.val - 10) % 2, by omega⟩ : Fin 2) = (⟨(j.val - 10) % 2, by omega⟩ : Fin 2) ∧ (⟨(i.val - 10) / 2, by omega⟩ : Fin 3) = (⟨(j.val - 10) / 2, by omega⟩ : Fin 3)) := fun hh => hS hh.1
                    rw [pi0_entry_quarkR, if_neg hne]
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
                exact pi0_diag_entry_leptonLc lam c (⟨j.val - 16, by omega⟩ : Fin 2)
              · have hS : (⟨i.val - 16, by omega⟩ : Fin 2) ≠ (⟨j.val - 16, by omega⟩ : Fin 2) :=
                  fun hh => hslot (Fin.ext (show
                    16 + ((⟨i.val - 16, by omega⟩ : Fin 2)).val = 16 + ((⟨j.val - 16, by omega⟩ : Fin 2)).val by
                    have hv := congrArg Fin.val hh
                    omega))
                rw [pi0_entry_leptonLc]
                show star lam * star ((1 : Matrix I2 I2 ℂ) (⟨i.val - 16, by omega⟩ : Fin 2) (⟨j.val - 16, by omega⟩ : Fin 2)) = 0
                rw [Matrix.one_apply, if_neg hS, star_zero, mul_zero]
            · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                (Or.inl ⟨by omega, hi18, by omega, hj24⟩)
              have hne : i ≠ j := by
                intro hh
                have hv := congrArg Fin.val hh
                omega
              rw [if_neg hne, pi0_entry_eq_zero_of_not_sameBlock _ hns]
          · by_cases hj18 : j.val < 18
            · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                (Or.inr (Or.inl ⟨by omega, hi24, hj16, hj18⟩))
              have hne : i ≠ j := by
                intro hh
                have hv := congrArg Fin.val hh
                omega
              rw [if_neg hne, pi0_entry_eq_zero_of_not_sameBlock _ hns]
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
                exact pi0_diag_entry_quarkLc lam c (⟨(j.val - 18) / 2, by omega⟩ : Fin 3) (⟨(j.val - 18) % 2, by omega⟩ : Fin 2)
              · by_cases hS : (⟨(i.val - 18) % 2, by omega⟩ : Fin 2) = (⟨(j.val - 18) % 2, by omega⟩ : Fin 2)
                · have hK : (⟨(i.val - 18) / 2, by omega⟩ : Fin 3) ≠ (⟨(j.val - 18) / 2, by omega⟩ : Fin 3) :=
                    fun hh => hslot (Fin.ext (show
                      18 + 2 * ((⟨(i.val - 18) / 2, by omega⟩ : Fin 3)).val + ((⟨(i.val - 18) % 2, by omega⟩ : Fin 2)).val
                        = 18 + 2 * ((⟨(j.val - 18) / 2, by omega⟩ : Fin 3)).val + ((⟨(j.val - 18) % 2, by omega⟩ : Fin 2)).val by
                      have hv1 := congrArg Fin.val hh
                      have hv2 := congrArg Fin.val hS
                      omega))
                  rw [pi0_entry_quarkLc]
                  show star ((1 : Matrix I2 I2 ℂ) (⟨(i.val - 18) % 2, by omega⟩ : Fin 2) (⟨(j.val - 18) % 2, by omega⟩ : Fin 2))
                    * (c • (1 : Matrix I3 I3 ℂ)) (⟨(i.val - 18) / 2, by omega⟩ : Fin 3) (⟨(j.val - 18) / 2, by omega⟩ : Fin 3) = 0
                  rw [Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply,
                    if_neg hK, smul_zero, mul_zero]
                · rw [pi0_entry_quarkLc]
                  show star ((1 : Matrix I2 I2 ℂ) (⟨(i.val - 18) % 2, by omega⟩ : Fin 2) (⟨(j.val - 18) % 2, by omega⟩ : Fin 2))
                    * (c • (1 : Matrix I3 I3 ℂ)) (⟨(i.val - 18) / 2, by omega⟩ : Fin 3) (⟨(j.val - 18) / 2, by omega⟩ : Fin 3) = 0
                  rw [Matrix.one_apply, if_neg hS, star_zero, zero_mul]
        · have hj24 : 24 ≤ j.val := by omega
          by_cases hi24' : i.val = 24
          · by_cases hj24' : j.val = 24
            · have hsi : (⟨24, by omega⟩ : I32) = i := Fin.ext hi24'.symm
              have hsj : (⟨24, by omega⟩ : I32) = j := Fin.ext hj24'.symm
              rw [← hsi, ← hsj]
              split_ifs with hslot
              · exact pi0_diag_entry_nuRc lam c
              · exact (hslot rfl).elim
            · by_cases hj25 : j.val = 25
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inl ⟨hi24', hj25⟩)))))))
                have hne : i ≠ j := by
                  intro hh
                  have hv := congrArg Fin.val hh
                  omega
                rw [if_neg hne, pi0_entry_eq_zero_of_not_sameBlock _ hns]
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                  (Or.inr (Or.inr (Or.inl ⟨hi24', by omega⟩)))
                have hne : i ≠ j := by
                  intro hh
                  have hv := congrArg Fin.val hh
                  omega
                rw [if_neg hne, pi0_entry_eq_zero_of_not_sameBlock _ hns]
          · by_cases hi25 : i.val = 25
            · by_cases hj24' : j.val = 24
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr ⟨hi25, hj24'⟩)))))))
                have hne : i ≠ j := by
                  intro hh
                  have hv := congrArg Fin.val hh
                  omega
                rw [if_neg hne, pi0_entry_eq_zero_of_not_sameBlock _ hns]
              · by_cases hj25 : j.val = 25
                · have hsi : (⟨25, by omega⟩ : I32) = i := Fin.ext hi25.symm
                  have hsj : (⟨25, by omega⟩ : I32) = j := Fin.ext hj25.symm
                  rw [← hsi, ← hsj]
                  split_ifs with hslot
                  · exact pi0_diag_entry_eRc lam c
                  · exact (hslot rfl).elim
                · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed
                    (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi25, by omega⟩))))
                  have hne : i ≠ j := by
                    intro hh
                    have hv := congrArg Fin.val hh
                    omega
                  rw [if_neg hne, pi0_entry_eq_zero_of_not_sameBlock _ hns]
            · by_cases hj24' : j.val = 24
              · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inl ⟨by omega, hj24'⟩)))))
                have hne : i ≠ j := by
                  intro hh
                  have hv := congrArg Fin.val hh
                  omega
                rw [if_neg hne, pi0_entry_eq_zero_of_not_sameBlock _ hns]
              · by_cases hj25 : j.val = 25
                · have hns : ¬ sameBlock i j := not_sameBlock_of_Hc_mixed (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inl ⟨by omega, hj25⟩))))))
                  have hne : i ≠ j := by
                    intro hh
                    have hv := congrArg Fin.val hh
                    omega
                  rw [if_neg hne, pi0_entry_eq_zero_of_not_sameBlock _ hns]
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
                    exact pi0_diag_entry_quarkRc lam c (⟨(j.val - 26) / 2, by omega⟩ : Fin 3) (⟨(j.val - 26) % 2, by omega⟩ : Fin 2)
                  · by_cases hS : (⟨(i.val - 26) % 2, by omega⟩ : Fin 2) = (⟨(j.val - 26) % 2, by omega⟩ : Fin 2)
                    · have hK : (⟨(i.val - 26) / 2, by omega⟩ : Fin 3) ≠ (⟨(j.val - 26) / 2, by omega⟩ : Fin 3) :=
                        fun hh => hslot (Fin.ext (show
                          26 + 2 * ((⟨(i.val - 26) / 2, by omega⟩ : Fin 3)).val + ((⟨(i.val - 26) % 2, by omega⟩ : Fin 2)).val
                            = 26 + 2 * ((⟨(j.val - 26) / 2, by omega⟩ : Fin 3)).val + ((⟨(j.val - 26) % 2, by omega⟩ : Fin 2)).val by
                          have hv1 := congrArg Fin.val hh
                          have hv2 := congrArg Fin.val hS
                          omega))
                      rw [pi0_entry_quarkRc, if_pos hS]
                      show (c • (1 : Matrix I3 I3 ℂ)) (⟨(i.val - 26) / 2, by omega⟩ : Fin 3) (⟨(j.val - 26) / 2, by omega⟩ : Fin 3) = 0
                      rw [Matrix.smul_apply, Matrix.one_apply, if_neg hK, smul_zero]
                    · rw [pi0_entry_quarkRc, if_neg hS]
  · have hns : ¬ sameBlock i j := not_sameBlock_of_ne_sector hsec
    have hne : i ≠ j := by
      intro hh
      have hv := congrArg Fin.val hh
      omega
    rw [if_neg hne, pi0_entry_eq_zero_of_not_sameBlock _ hns]

/-- `π₀` sends the algebra unit to the identity matrix. (With
`pi0_afMul`, `pi0_zero`, and `pi0_afStar`, this completes the unital
star-multiplicative package of T1; additivity is the proved exception —
see `pi0_not_additive` and the header.) -/
theorem pi0_one : pi0 afOne = 1 := by
  have h1 : afOne = ⟨1, 1, (1 : ℂ) • (1 : Matrix I3 I3 ℂ)⟩ := by
    rw [ext_iff]
    refine ⟨afOne_u1, afOne_q, ?_⟩
    rw [afOne_color, one_smul]
  rw [h1, pi0_eq_diagonal]
  have hD : pi0Diag 1 1 = fun _ => 1 := by
    funext i
    show pi0DiagVal 1 1 i.val = 1
    unfold pi0DiagVal
    split_ifs <;> simp [star_one]
  rw [hD]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
  · rw [Matrix.diagonal_apply, if_neg hij, Matrix.one_apply_ne hij]

/-- The integer weight of slot value `v` in the determinant computation:
the exponent of the surviving generator before the `piOp` lift. -/
def pi0WVal (v : ℕ) : ℤ :=
  if v < 8 then 0
  else if v = 8 then 3
  else if v = 9 then -3
  else if v < 16 then (if (v - 10) % 2 = 0 then 3 else -3)
  else if v < 18 then -3
  else if v < 24 then 1
  else if v < 26 then -3
  else 1

/-- The integer weight function on slots. -/
def W (i : I32) : ℤ := pi0WVal i.val

/-- The weights sum to zero over the 32 slots — the exact arithmetic
content of unimodularity for the direction `(α, β) = (3, 1)`. -/
theorem sum_W : ∑ i, W i = 0 := by decide

theorem star_exp_three (t : ℝ) :
    star (Complex.exp (3 * (t : ℂ) * Complex.I))
      = Complex.exp (-(3 * (t : ℂ) * Complex.I)) := by
  rw [← starRingEnd_apply, ← Complex.exp_conj]
  congr 1
  rw [Complex.ext_iff]
  simp

theorem star_exp_one (t : ℝ) :
    star (Complex.exp ((t : ℂ) * Complex.I))
      = Complex.exp (-((t : ℂ) * Complex.I)) := by
  rw [← starRingEnd_apply, ← Complex.exp_conj]
  congr 1
  rw [Complex.ext_iff]
  simp

/-- The surviving one-parameter subgroup: the unimodularity condition
`det (π₀ u) = 1` over `ℂ³²` forces the `ℂ`-factor weight to be `3`
times the color weight (the sector weights sum to `-4α + 12β`); with
the color weight normalized to `1`, the `ℂ` weight is `3`. -/
noncomputable def u1Param (t : ℝ) : AF :=
  ⟨Complex.exp (3 * (t : ℂ) * Complex.I), 1,
    Complex.exp ((t : ℂ) * Complex.I) • (1 : Matrix I3 I3 ℂ)⟩

/-- The diagonal of `π₀ (u1Param t)`, entry by entry: each diagonal
entry is `exp (W i · t i)`. -/
theorem pi0Diag_u1Param (t : ℝ) (i : I32) :
    pi0Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I)) i
      = Complex.exp ((W i : ℂ) * ((t : ℂ) * Complex.I)) := by
  have hv : i.val < 32 := i.isLt
  by_cases h8 : i.val < 8
  · have hD : pi0DiagVal (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I)) i.val = 1 := by
      unfold pi0DiagVal
      rw [if_pos h8]
    have hW : pi0WVal i.val = 0 := by
      unfold pi0WVal
      rw [if_pos h8]
    show pi0DiagVal (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I)) i.val
      = Complex.exp ((pi0WVal i.val : ℂ) * ((t : ℂ) * Complex.I))
    rw [hD, hW, Int.cast_zero, zero_mul, Complex.exp_zero]
  · by_cases h8' : i.val = 8
    · have hD : pi0DiagVal (Complex.exp (3 * (t : ℂ) * Complex.I))
          (Complex.exp ((t : ℂ) * Complex.I)) i.val
          = Complex.exp (3 * (t : ℂ) * Complex.I) := by
        unfold pi0DiagVal
        rw [if_neg h8, if_pos h8']
      have hW : pi0WVal i.val = 3 := by
        unfold pi0WVal
        rw [if_neg h8, if_pos h8']
      show pi0DiagVal (Complex.exp (3 * (t : ℂ) * Complex.I))
          (Complex.exp ((t : ℂ) * Complex.I)) i.val
        = Complex.exp ((pi0WVal i.val : ℂ) * ((t : ℂ) * Complex.I))
      rw [hD, hW]
      congr 1
      push_cast
      ring
    · by_cases h9 : i.val = 9
      · have hD : pi0DiagVal (Complex.exp (3 * (t : ℂ) * Complex.I))
            (Complex.exp ((t : ℂ) * Complex.I)) i.val
            = star (Complex.exp (3 * (t : ℂ) * Complex.I)) := by
          unfold pi0DiagVal
          rw [if_neg h8, if_neg h8', if_pos h9]
        have hW : pi0WVal i.val = -3 := by
          unfold pi0WVal
          rw [if_neg h8, if_neg h8', if_pos h9]
        show pi0DiagVal (Complex.exp (3 * (t : ℂ) * Complex.I))
            (Complex.exp ((t : ℂ) * Complex.I)) i.val
          = Complex.exp ((pi0WVal i.val : ℂ) * ((t : ℂ) * Complex.I))
        rw [hD, star_exp_three, hW]
        congr 1
        push_cast
        ring
      · by_cases h16 : i.val < 16
        · by_cases hm : (i.val - 10) % 2 = 0
          · have hD : pi0DiagVal (Complex.exp (3 * (t : ℂ) * Complex.I))
                (Complex.exp ((t : ℂ) * Complex.I)) i.val
                = Complex.exp (3 * (t : ℂ) * Complex.I) := by
              unfold pi0DiagVal
              rw [if_neg h8, if_neg h8', if_neg h9, if_pos h16, if_pos hm]
            have hW : pi0WVal i.val = 3 := by
              unfold pi0WVal
              rw [if_neg h8, if_neg h8', if_neg h9, if_pos h16, if_pos hm]
            show pi0DiagVal (Complex.exp (3 * (t : ℂ) * Complex.I))
                (Complex.exp ((t : ℂ) * Complex.I)) i.val
              = Complex.exp ((pi0WVal i.val : ℂ) * ((t : ℂ) * Complex.I))
            rw [hD, hW]
            congr 1
            push_cast
            ring
          · have hD : pi0DiagVal (Complex.exp (3 * (t : ℂ) * Complex.I))
                (Complex.exp ((t : ℂ) * Complex.I)) i.val
                = star (Complex.exp (3 * (t : ℂ) * Complex.I)) := by
              unfold pi0DiagVal
              rw [if_neg h8, if_neg h8', if_neg h9, if_pos h16, if_neg hm]
            have hW : pi0WVal i.val = -3 := by
              unfold pi0WVal
              rw [if_neg h8, if_neg h8', if_neg h9, if_pos h16, if_neg hm]
            show pi0DiagVal (Complex.exp (3 * (t : ℂ) * Complex.I))
                (Complex.exp ((t : ℂ) * Complex.I)) i.val
              = Complex.exp ((pi0WVal i.val : ℂ) * ((t : ℂ) * Complex.I))
            rw [hD, star_exp_three, hW]
            congr 1
            push_cast
            ring
        · by_cases h18 : i.val < 18
          · have hD : pi0DiagVal (Complex.exp (3 * (t : ℂ) * Complex.I))
                (Complex.exp ((t : ℂ) * Complex.I)) i.val
                = star (Complex.exp (3 * (t : ℂ) * Complex.I)) := by
              unfold pi0DiagVal
              rw [if_neg h8, if_neg h8', if_neg h9, if_neg h16, if_pos h18]
            have hW : pi0WVal i.val = -3 := by
              unfold pi0WVal
              rw [if_neg h8, if_neg h8', if_neg h9, if_neg h16, if_pos h18]
            show pi0DiagVal (Complex.exp (3 * (t : ℂ) * Complex.I))
                (Complex.exp ((t : ℂ) * Complex.I)) i.val
              = Complex.exp ((pi0WVal i.val : ℂ) * ((t : ℂ) * Complex.I))
            rw [hD, star_exp_three, hW]
            congr 1
            push_cast
            ring
          · by_cases h24 : i.val < 24
            · have hD : pi0DiagVal (Complex.exp (3 * (t : ℂ) * Complex.I))
                  (Complex.exp ((t : ℂ) * Complex.I)) i.val
                  = Complex.exp ((t : ℂ) * Complex.I) := by
                unfold pi0DiagVal
                rw [if_neg h8, if_neg h8', if_neg h9, if_neg h16,
                  if_neg h18, if_pos h24]
              have hW : pi0WVal i.val = 1 := by
                unfold pi0WVal
                rw [if_neg h8, if_neg h8', if_neg h9, if_neg h16,
                  if_neg h18, if_pos h24]
              show pi0DiagVal (Complex.exp (3 * (t : ℂ) * Complex.I))
                  (Complex.exp ((t : ℂ) * Complex.I)) i.val
                = Complex.exp ((pi0WVal i.val : ℂ) * ((t : ℂ) * Complex.I))
              rw [hD, hW]
              congr 1
              push_cast
              ring
            · by_cases h26 : i.val < 26
              · have hD : pi0DiagVal (Complex.exp (3 * (t : ℂ) * Complex.I))
                    (Complex.exp ((t : ℂ) * Complex.I)) i.val
                    = star (Complex.exp (3 * (t : ℂ) * Complex.I)) := by
                  unfold pi0DiagVal
                  rw [if_neg h8, if_neg h8', if_neg h9, if_neg h16,
                    if_neg h18, if_neg h24, if_pos h26]
                have hW : pi0WVal i.val = -3 := by
                  unfold pi0WVal
                  rw [if_neg h8, if_neg h8', if_neg h9, if_neg h16,
                    if_neg h18, if_neg h24, if_pos h26]
                show pi0DiagVal (Complex.exp (3 * (t : ℂ) * Complex.I))
                    (Complex.exp ((t : ℂ) * Complex.I)) i.val
                  = Complex.exp ((pi0WVal i.val : ℂ) * ((t : ℂ) * Complex.I))
                rw [hD, star_exp_three, hW]
                congr 1
                push_cast
                ring
              · have hD : pi0DiagVal (Complex.exp (3 * (t : ℂ) * Complex.I))
                    (Complex.exp ((t : ℂ) * Complex.I)) i.val
                    = Complex.exp ((t : ℂ) * Complex.I) := by
                  unfold pi0DiagVal
                  rw [if_neg h8, if_neg h8', if_neg h9, if_neg h16,
                    if_neg h18, if_neg h24, if_neg h26]
                have hW : pi0WVal i.val = 1 := by
                  unfold pi0WVal
                  rw [if_neg h8, if_neg h8', if_neg h9, if_neg h16,
                    if_neg h18, if_neg h24, if_neg h26]
                show pi0DiagVal (Complex.exp (3 * (t : ℂ) * Complex.I))
                    (Complex.exp ((t : ℂ) * Complex.I)) i.val
                  = Complex.exp ((pi0WVal i.val : ℂ) * ((t : ℂ) * Complex.I))
                rw [hD, hW]
                congr 1
                push_cast
                ring

/-- **Unimodularity of the surviving direction (T4, determinant half).**
`det (π₀ (u1Param t)) = 1` for all `t`: the product of the diagonal
entries is `exp ((∑ᵢ W i) · t i) = exp 0`. -/
theorem pi0_det_unimodular (t : ℝ) :
    (pi0 (u1Param t)).det = 1 := by
  have hU : u1Param t = ⟨Complex.exp (3 * (t : ℂ) * Complex.I), 1,
      Complex.exp ((t : ℂ) * Complex.I) • (1 : Matrix I3 I3 ℂ)⟩ := rfl
  rw [hU, pi0_eq_diagonal, Matrix.det_diagonal,
    Finset.prod_congr rfl (fun i _ => pi0Diag_u1Param t i),
    ← Complex.exp_sum, ← Finset.sum_mul, ← Int.cast_sum, sum_W,
    Int.cast_zero, zero_mul, Complex.exp_zero]

/-- `piOp` (the corpus's `J`-conjugation, `FiniteSpectralTriple.piOp`)
sends a diagonal matrix to the diagonal of partner-shifted entries. -/
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

/-- **T4 — the hypercharge pattern.** For every fermion sector `f`, the
lifted eigenvalue of the surviving (unimodular) generator on `f` is
`exp (3 · t · i · Y f)`: the sector eigenvalues are proportional to the
SM hypercharges with ratios EXACTLY the table's, and the single free
normalization is `3`, forced by unimodularity (`pi0_det_unimodular`).
The statement imports the corpus's T2 table `SMFermions.hypercharge`
at sector level — declared on the module's face in the §8 header, as
the charter requires. Case check (with `s = t·i`): `ν_L, e_L`: `exp (-3s)`
(`Y = -1`); `Q_L`: `exp (s)` (`Y = 1/3`); `ν_R`: `1` (`Y = 0`);
`e_R`: `exp (-6s)` (`Y = -2`); `u_R`: `exp (4s)` (`Y = 4/3`);
`d_R`: `exp (-2s)` (`Y = -2/3`). No sector deviates. -/
theorem pi0_hypercharge_pattern (f : SMFermion) (t : ℝ) :
    (pi0 (u1Param t) * piOp (pi0 (u1Param t)))
        (fermionIndex f 0) (fermionIndex f 0)
      = Complex.exp (3 * (t : ℂ) * Complex.I * (hypercharge f : ℂ)) := by
  have hU : u1Param t = ⟨Complex.exp (3 * (t : ℂ) * Complex.I), 1,
      Complex.exp ((t : ℂ) * Complex.I) • (1 : Matrix I3 I3 ℂ)⟩ := rfl
  cases f
  · -- ν_L: Y = -1, lifted weight -3
    have hs : fermionIndex SMFermion.nuL (0 : Fin 3) = ⟨0, by omega⟩ := rfl
    have hp : partner (⟨0, by omega⟩ : I32) = ⟨16, by omega⟩ := by
      apply Fin.ext
      simp [partner_val_eq]
    have dA : pi0Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I)) ⟨0, by omega⟩ = 1 := by
      show pi0DiagVal _ _ 0 = 1
      unfold pi0DiagVal
      rw [if_pos (by norm_num)]
    have dB : pi0Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I)) ⟨16, by omega⟩
        = star (Complex.exp (3 * (t : ℂ) * Complex.I)) := by
      show pi0DiagVal _ _ 16 = star (Complex.exp (3 * (t : ℂ) * Complex.I))
      unfold pi0DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_pos (by norm_num)]
    have hY : hypercharge SMFermion.nuL = -1 := rfl
    rw [hs, hU, pi0_eq_diagonal, piOp_diagonal, Matrix.diagonal_mul_diagonal,
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
    have dA : pi0Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I)) ⟨1, by omega⟩ = 1 := by
      show pi0DiagVal _ _ 1 = 1
      unfold pi0DiagVal
      rw [if_pos (by norm_num)]
    have dB : pi0Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I)) ⟨17, by omega⟩
        = star (Complex.exp (3 * (t : ℂ) * Complex.I)) := by
      show pi0DiagVal _ _ 17 = star (Complex.exp (3 * (t : ℂ) * Complex.I))
      unfold pi0DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_pos (by norm_num)]
    have hY : hypercharge SMFermion.eL = -1 := rfl
    rw [hs, hU, pi0_eq_diagonal, piOp_diagonal, Matrix.diagonal_mul_diagonal,
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
    have dA : pi0Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I)) ⟨2, by omega⟩ = 1 := by
      show pi0DiagVal _ _ 2 = 1
      unfold pi0DiagVal
      rw [if_pos (by norm_num)]
    have dB : pi0Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I)) ⟨18, by omega⟩
        = Complex.exp ((t : ℂ) * Complex.I) := by
      show pi0DiagVal _ _ 18 = Complex.exp ((t : ℂ) * Complex.I)
      unfold pi0DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num)]
    have hY : hypercharge SMFermion.uL = 1 / 3 := rfl
    rw [hs, hU, pi0_eq_diagonal, piOp_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq, hp]
    rw [dA, dB, one_mul, hY]
    congr 1
    push_cast
    ring
  · -- d_L: Y = 1/3, lifted weight 1
    have hs : fermionIndex SMFermion.dL (0 : Fin 3) = ⟨3, by omega⟩ := rfl
    have hp : partner (⟨3, by omega⟩ : I32) = ⟨19, by omega⟩ := by
      apply Fin.ext
      simp [partner_val_eq]
    have dA : pi0Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I)) ⟨3, by omega⟩ = 1 := by
      show pi0DiagVal _ _ 3 = 1
      unfold pi0DiagVal
      rw [if_pos (by norm_num)]
    have dB : pi0Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I)) ⟨19, by omega⟩
        = Complex.exp ((t : ℂ) * Complex.I) := by
      show pi0DiagVal _ _ 19 = Complex.exp ((t : ℂ) * Complex.I)
      unfold pi0DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num)]
    have hY : hypercharge SMFermion.dL = 1 / 3 := rfl
    rw [hs, hU, pi0_eq_diagonal, piOp_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq, hp]
    rw [dA, dB, one_mul, hY]
    congr 1
    push_cast
    ring
  · -- ν_R: Y = 0, lifted weight 0
    have hs : fermionIndex SMFermion.nuR (0 : Fin 3) = ⟨8, by omega⟩ := rfl
    have hp : partner (⟨8, by omega⟩ : I32) = ⟨24, by omega⟩ := by
      apply Fin.ext
      simp [partner_val_eq]
    have dA : pi0Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I)) ⟨8, by omega⟩
        = Complex.exp (3 * (t : ℂ) * Complex.I) := by
      show pi0DiagVal _ _ 8 = Complex.exp (3 * (t : ℂ) * Complex.I)
      unfold pi0DiagVal
      rw [if_neg (by norm_num), if_pos (by norm_num)]
    have dB : pi0Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I)) ⟨24, by omega⟩
        = star (Complex.exp (3 * (t : ℂ) * Complex.I)) := by
      show pi0DiagVal _ _ 24 = star (Complex.exp (3 * (t : ℂ) * Complex.I))
      unfold pi0DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_pos (by norm_num)]
    have hY : hypercharge SMFermion.nuR = 0 := rfl
    rw [hs, hU, pi0_eq_diagonal, piOp_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq, hp]
    rw [dA, dB, star_exp_three,
      ← Complex.exp_add, hY]
    congr 1
    push_cast
    ring
  · -- e_R: Y = -2, lifted weight -6
    have hs : fermionIndex SMFermion.eR (0 : Fin 3) = ⟨9, by omega⟩ := rfl
    have hp : partner (⟨9, by omega⟩ : I32) = ⟨25, by omega⟩ := by
      apply Fin.ext
      simp [partner_val_eq]
    have dA : pi0Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I)) ⟨9, by omega⟩
        = star (Complex.exp (3 * (t : ℂ) * Complex.I)) := by
      show pi0DiagVal _ _ 9 = star (Complex.exp (3 * (t : ℂ) * Complex.I))
      unfold pi0DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num)]
    have dB : pi0Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I)) ⟨25, by omega⟩
        = star (Complex.exp (3 * (t : ℂ) * Complex.I)) := by
      show pi0DiagVal _ _ 25 = star (Complex.exp (3 * (t : ℂ) * Complex.I))
      unfold pi0DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_pos (by norm_num)]
    have hY : hypercharge SMFermion.eR = -2 := rfl
    rw [hs, hU, pi0_eq_diagonal, piOp_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq, hp]
    rw [dA, dB, star_exp_three,
      ← Complex.exp_add, hY]
    congr 1
    push_cast
    ring
  · -- u_R: Y = 4/3, lifted weight 4
    have hs : fermionIndex SMFermion.uR (0 : Fin 3) = ⟨10, by omega⟩ := rfl
    have hp : partner (⟨10, by omega⟩ : I32) = ⟨26, by omega⟩ := by
      apply Fin.ext
      simp [partner_val_eq]
    have dA : pi0Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I)) ⟨10, by omega⟩
        = Complex.exp (3 * (t : ℂ) * Complex.I) := by
      show pi0DiagVal _ _ 10 = Complex.exp (3 * (t : ℂ) * Complex.I)
      unfold pi0DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_pos (by norm_num), if_pos (by norm_num)]
    have dB : pi0Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I)) ⟨26, by omega⟩
        = Complex.exp ((t : ℂ) * Complex.I) := by
      show pi0DiagVal _ _ 26 = Complex.exp ((t : ℂ) * Complex.I)
      unfold pi0DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num)]
    have hY : hypercharge SMFermion.uR = 4 / 3 := rfl
    rw [hs, hU, pi0_eq_diagonal, piOp_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq, hp]
    rw [dA, dB,
      ← Complex.exp_add, hY]
    congr 1
    push_cast
    ring
  · -- d_R: Y = -2/3, lifted weight -2
    have hs : fermionIndex SMFermion.dR (0 : Fin 3) = ⟨11, by omega⟩ := rfl
    have hp : partner (⟨11, by omega⟩ : I32) = ⟨27, by omega⟩ := by
      apply Fin.ext
      simp [partner_val_eq]
    have dA : pi0Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I)) ⟨11, by omega⟩
        = star (Complex.exp (3 * (t : ℂ) * Complex.I)) := by
      show pi0DiagVal _ _ 11 = star (Complex.exp (3 * (t : ℂ) * Complex.I))
      unfold pi0DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_pos (by norm_num), if_neg (by norm_num)]
    have dB : pi0Diag (Complex.exp (3 * (t : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I)) ⟨27, by omega⟩
        = Complex.exp ((t : ℂ) * Complex.I) := by
      show pi0DiagVal _ _ 27 = Complex.exp ((t : ℂ) * Complex.I)
      unfold pi0DiagVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_neg (by norm_num)]
    have hY : hypercharge SMFermion.dR = -2 / 3 := rfl
    rw [hs, hU, pi0_eq_diagonal, piOp_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq, hp]
    rw [dA, dB, star_exp_three,
      ← Complex.exp_add, hY]
    congr 1
    push_cast
    ring

end ThetLogos.PreOptionARepresentation
