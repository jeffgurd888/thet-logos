import Mathlib.Tactic
import ThetLogos.DialOneLeptonChapter
import ThetLogos.DialOneClassificationPin
import ThetLogos.DialOneSwapOrbit
import ThetLogos.Track1Closure

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.HyperchargeForcing
open ThetLogos.DialOneSeatTiePin
open ThetLogos.DialOneGammaTracePin
open ThetLogos.DialOneGammaTraceChecks
open ThetLogos.DialOneGammaFamilyPin
open ThetLogos.DialOneLeptonChapter
open ThetLogos.DialOneClassificationPin
open ThetLogos.DialOneSwapOrbit

/-!
# CLS-3c — the antiparticle chapter of the Dial-1 classification

Governing text: the compensator scoping
(`routeb-general-scratch/scoping-d1-compensator-2026-11-01.md`)
§2.6 — the scope fence on the whole toggle analysis. The
toggle calculus covers particle ℂ-seat conjugation toggles
and (via pair differences) their antiparticle mirrors.
§2.6 names **one** direction outside it:

> the joint antiparticle M₃ un-conjugation (both
> antiparticle blocks, β-side) — the π₀↔π₁ axis.

## The direction, and what is in-tree vs. what is this chapter's

**No in-tree definition of the pure direction exists.**
The axis's landed endpoint is π₀
(`ThetLogos.PreOptionARepresentation.pi0`), but π₀ is NOT
the pure direction: besides the M₃ un-conjugation it
carries the two BOLTED blocks (the antilepton `λ̄ • q̄`
and the left-antiquark `q̄ ⊗ m` tensor products,
`Track1RouteB` §2 anatomy). This chapter therefore
defines the pure direction minimally from §2.6, and says
so on the face: **`piAnti` is this chapter's
definition** — π₁ with exactly the M₃-summand's
conjugation removed in BOTH antiparticle blocks (left
antiquarks, slots 18–23, and right antiquarks, slots
26–31: `star (a.color k l)` ↦ `a.color k l`), and
nothing else changed. Its diagonal β-table `piAntiBVal`
differs from π₁'s `pi1BVal` exactly there (`−1 ↦ +1` on
both antiquark blocks); the α-table is π₁'s unchanged.

## Verdicts

* **C3-invisibility — T1 here** (T2 in the scoping):
  the direction changes only the β-table, and its
  γ-weighted β-difference sum is exactly `0`
  (`gamma_weighted_beta_direction_zero`, ℤ shadow,
  `decide`): the two blocks' contributions `−12` and
  `+12` cancel. Hence the γ-weighted trace of `piAnti`
  at the generator vanishes
  (`trace_gammaF_piAnti_u1Gen`) and **`C3 piAnti`
  holds** (`c3_piAnti`). No γ-trace clause of the
  classification sees this direction.
* **The axis endpoint is BASE-KILLED at the
  first-order clause — T1, landed kill cited exactly**:
  `ThetLogos.Track1Closure.first_order_killed`
  (module `ThetLogos.Track1Closure`, T3 there): for
  π₀'s own opposite `rho0 = piOp ∘ pi0`, there are
  Yukawas and witnesses whose first-order double
  commutator against `DF_oneGen` is nonzero — its
  `(0,9)` entry is exactly `−(1 + I) * ye`
  (`ThetLogos.Track1Closure.DF_first_order_entry_09`).
  That is precisely clause 9 (first-order) of
  `DialOneBase` at `π = pi0`, so the kill transports in
  one step: **`¬ DialOneBase pi0`**
  (`not_dialOneBase_pi0`), and hence
  `¬ DialOneStrengthenedFam pi0`. This is "what Route B
  is": Route B (π₁, summand-pure) exists because the
  un-conjugated side of the axis dies at first-order.
* **THE SEAM, on the face (the chapter's PARTIAL)**:
  the landed kill is at the axis endpoint π₀, whose
  base failure is witnessed through its bolted blocks.
  The PURE direction `piAnti` defined here has **no
  landed base verdict**: transporting π₀'s kill to
  `piAnti` would require a new first-order computation
  (π₀'s witnesses read the bolts, which `piAnti` does
  not have), and identifying the two would silently
  upgrade the scoping's T2 sentence to a T1 kill at a
  different representation. **Not done. `piAnti`'s base
  status is named OPEN.** What is dead at T1 is the
  axis as landed — the only form in which the
  direction has ever been represented in the corpus
  before this chapter.

## The boundary statement

Within the classification's currently named direction
space — the toggle calculus (CLS-0's record form
`IsToggleOfPi1`, CLS-3a's lepton single `piEFlip`, and
the CLS-2 orbit `orbitRep`, CLS-3b's colour swaps
included in both) plus this chapter's antiparticle
axis — the antiparticle direction is the **unique
non-toggle direction currently named**
(`antiparticle_unique_nontoggle`): every named
direction that is not a toggle is `piAnti` or its
landed axis endpoint `pi0`. And it is dead at the base
in its landed form (`not_dialOneBase_pi0`). **New
non-toggle directions are new entries under the
relabeling rule, never extensions of this chapter.**
The classification's boundary is thereby explicit.

**NO CLAIM; Dial 1 = 0; all dials 0/4. Classification
data only: parts of any official statement closed by
this module: 0.**
-/

namespace ThetLogos.DialOneAntiparticleChapter

/-! ## The direction (this chapter's definition, from §2.6) -/

/-- **The joint antiparticle M₃ un-conjugation of π₁**
— THIS CHAPTER'S definition, built minimally from the
compensator scoping §2.6 (no in-tree definition of the
pure direction exists; π₀, the axis's landed endpoint,
additionally carries the bolted blocks and is a
different representation). `piAnti` is π₁'s definition
with exactly two branches changed: in both antiparticle
M₃ blocks — left antiquarks (slots 18–23) and right
antiquarks (slots 26–31) — the colour action is
UN-conjugated, `a.color k l` in place of π₁'s
`star (a.color k l)`. Every other branch is π₁'s
verbatim. -/
def piAnti (a : AF) : Matrix (Fin 32) (Fin 32) ℂ := fun i j =>
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
      if iso_i = iso_j then a.color col_i col_j else 0
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

/-- **The M₃-seat (β) weight of `piAnti`'s diagonal** at
slot `v`: π₁'s `pi1BVal` with the sign flipped on BOTH
antiquark blocks (`+1` at slots 18–23 and 26–31), zero
elsewhere. The direction is β-side only: the α-table is
π₁'s `pi1AVal`, unchanged. -/
def piAntiBVal (v : ℕ) : ℤ :=
  if v < 18 then 0
  else if v < 24 then 1
  else if v < 26 then 0
  else 1

/-! ## C3-invisibility -/

/-- **The diagonal of `piAnti (u1Gen α β)`**, seat by
seat: at seat `i` it is `i · (Aᵢ·α + Bᵢ·β)` for π₁'s
landed α-table `pi1AVal` and this chapter's β-table
`piAntiBVal`. Proved by 32-case exhaustion over the
definition, mirroring the landed `pi1_diag_u1Gen`. -/
theorem piAnti_diag_u1Gen (α β : ℤ) (i : Fin 32) :
    piAnti (u1Gen α β) i i
      = Complex.I * ((pi1AVal i.val * α + piAntiBVal i.val * β : ℤ) : ℂ) := by
  obtain ⟨v, hv⟩ := i
  interval_cases v <;>
    simp [piAnti, u1Gen, pi1AVal, piAntiBVal] <;> ring

/-- **The direction's γ-weighted β-sum is `0`** — the
scoping §2.6 sentence ("its γ-weighted β-sum is 0"),
made T1 as an integer shadow: the un-conjugation
changes the β-table by `+2` on each antiquark block,
and the γ-signs (`−1` on slots 18–23, `+1` on slots
26–31) make the changes cancel, `−12 + 12 = 0`.
Discharged by `decide` over the `Fin 32` tables. -/
theorem gamma_weighted_beta_direction_zero :
    ∑ i : Fin 32, gammaVal i.val * (piAntiBVal i.val - pi1BVal i.val)
      = 0 := by decide

/-- The γ-weighted β-coefficient sum of `piAnti` is `0`
(ℤ shadow, `decide`). -/
theorem gamma_weighted_sum_B_anti :
    ∑ i : Fin 32, gammaVal i.val * piAntiBVal i.val = 0 := by decide

/-- **The γ-weighted trace of `piAnti` at the generator
is `0`**, for every direction `(α, β)`: the α-part is
π₁'s landed vanishing sum, the β-part vanishes by
`gamma_weighted_sum_B_anti`. -/
theorem trace_gammaF_piAnti_u1Gen (α β : ℤ) :
    Matrix.trace (gammaF * piAnti (u1Gen α β)) = 0 := by
  rw [trace_gammaF_mul]
  have hterm : ∀ i : Fin 32, gammaF i i * piAnti (u1Gen α β) i i
      = Complex.I
        * ((gammaVal i.val * (pi1AVal i.val * α + piAntiBVal i.val * β) : ℤ) : ℂ) := by
    intro i
    rw [gammaF_diag_eq, piAnti_diag_u1Gen]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum,
    ← Int.cast_sum]
  have hsum : ∑ i : Fin 32,
        gammaVal i.val * (pi1AVal i.val * α + piAntiBVal i.val * β) = 0 := by
    have h1 : ∀ i : Fin 32, gammaVal i.val * (pi1AVal i.val * α + piAntiBVal i.val * β)
        = (gammaVal i.val * pi1AVal i.val) * α
          + (gammaVal i.val * piAntiBVal i.val) * β := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, gamma_weighted_sum_A,
      gamma_weighted_sum_B_anti]
    simp
  rw [hsum]
  simp

/-- **`C3 piAnti`**: the joint antiparticle M₃
un-conjugation is invisible to the classification's
γ-trace clause. Invisibility only — no base claim is
made for `piAnti` in this chapter (see the seam). -/
theorem c3_piAnti : C3 piAnti :=
  fun α β => trace_gammaF_piAnti_u1Gen α β

/-- Distinctness: `piAnti ≠ pi1`, witnessed at seat 26
at `u1Gen 0 1` (`i` vs π₁'s `−i` — the right-antiquark
block's un-conjugation). -/
theorem piAnti_ne_pi1 : piAnti ≠ pi1 := by
  intro h
  have hentry := congrArg
    (fun M : Matrix (Fin 32) (Fin 32) ℂ => M ⟨26, by omega⟩ ⟨26, by omega⟩)
    (congrFun h (u1Gen 0 1))
  rw [piAnti_diag_u1Gen, pi1_diag_u1Gen] at hentry
  norm_num [pi1AVal, piAntiBVal, pi1BVal, Complex.ext_iff] at hentry

/-! ## The base kill at the axis endpoint (landed, transported one step) -/

/-- **THE BASE KILL — `¬ DialOneBase pi0`**, by the
first-order clause alone. The landed T1 kill is cited
exactly: `ThetLogos.Track1Closure.first_order_killed`
— there exist real Yukawas `ynu ye yu yd` and
`a b : AF` whose first-order double commutator
`[[DF_oneGen, pi0 a], rho0 b]` is nonzero, with
`rho0 = piOp ∘ pi0` by its landed definition. Clause 9
of `DialOneBase` at `π = pi0` is that commutator's
entrywise vanishing against `piOp (pi0 b)` — the same
object — so the clause cannot hold. (π₀ also fails
order-zero, landed; the first-order clause is the one
the scoping names, and the only one used here.) -/
theorem not_dialOneBase_pi0 : ¬ DialOneBase pi0 := by
  intro h
  obtain ⟨ynu, ye, yu, yd, a, b, hne⟩ :=
    ThetLogos.Track1Closure.first_order_killed
  apply hne
  ext i j
  exact h.2.2.2.2.2.2.2.2.1 ynu ye yu yd a b i j

/-- **The axis endpoint is outside the strengthened
family**, by the base kill alone (Base is the first
conjunct of `DialOneStrengthenedFam`). -/
theorem not_strengthenedFam_pi0 :
    ¬ DialOneStrengthenedFam pi0 :=
  fun h => not_dialOneBase_pi0 h.1

/-! ## The boundary statement -/

/-- **Toggle direction, as currently named**: π₁
itself, CLS-0's record form (`IsToggleOfPi1`: piFlip,
piDouble, the per-colour swaps), CLS-3a's lepton single
`piEFlip`, or a point of the CLS-2 toggle orbit
`orbitRep` (which contains the record form and the
lepton singles as its points). Bookkeeping over landed
names only. -/
def IsToggleDirection (π : AF → Matrix (Fin 32) (Fin 32) ℂ) : Prop :=
  π = pi1 ∨ IsToggleOfPi1 π ∨ π = piEFlip
    ∨ ∃ b : Fin 4 → Bool, π = orbitRep b

/-- **Named direction, as currently named**: a toggle
direction, or the antiparticle axis — the pure
direction `piAnti` (this chapter) or its landed
endpoint `pi0`. Nothing else is named in the
classification today. -/
def IsNamedDirection (π : AF → Matrix (Fin 32) (Fin 32) ℂ) : Prop :=
  IsToggleDirection π ∨ π = piAnti ∨ π = pi0

/-- Read-back: `IsNamedDirection` is visibly toggle ∨
the antiparticle axis, nothing else. -/
theorem isNamedDirection_unfold
    (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    IsNamedDirection π ↔
      IsToggleDirection π ∨ π = piAnti ∨ π = pi0 :=
  Iff.rfl

/-- **THE BOUNDARY**: the antiparticle direction is
the unique non-toggle direction currently named —
every named direction that is not a toggle is
`piAnti` or its landed axis endpoint `pi0`. New
non-toggle directions are new entries under the
relabeling rule, never extensions of this chapter. -/
theorem antiparticle_unique_nontoggle {π : AF → Matrix (Fin 32) (Fin 32) ℂ}
    (h : IsNamedDirection π) (ht : ¬ IsToggleDirection π) :
    π = piAnti ∨ π = pi0 := by
  rcases h with h | h | h
  · exact absurd h ht
  · exact Or.inl h
  · exact Or.inr h

/-! ## The chapter headline -/

/-- **CLS-3c, assembled**: the joint antiparticle M₃
un-conjugation is C3-invisible (`C3 piAnti`, and
`piAnti ≠ pi1`); its landed axis endpoint π₀ is
base-killed at the first-order clause, hence outside
the strengthened family; and within the currently
named direction space it is the unique non-toggle
direction. **The seam stands as stated in the header:
`piAnti`'s own base status is OPEN — the T1 kill is
π₀'s, transported to `DialOneBase` at the endpoint,
not to the pure direction.** -/
theorem antiparticle_chapter :
    C3 piAnti ∧ piAnti ≠ pi1
      ∧ ¬ DialOneBase pi0
      ∧ ¬ DialOneStrengthenedFam pi0
      ∧ ∀ π : AF → Matrix (Fin 32) (Fin 32) ℂ,
          IsNamedDirection π → ¬ IsToggleDirection π
            → π = piAnti ∨ π = pi0 :=
  ⟨c3_piAnti, piAnti_ne_pi1, not_dialOneBase_pi0,
    not_strengthenedFam_pi0,
    fun _ h ht => antiparticle_unique_nontoggle h ht⟩

-- Axiom audit for the headline verdicts (expected:
-- [propext, Classical.choice, Quot.sound] throughout).
#print axioms trace_gammaF_piAnti_u1Gen
#print axioms c3_piAnti
#print axioms piAnti_ne_pi1
#print axioms not_dialOneBase_pi0
#print axioms not_strengthenedFam_pi0
#print axioms antiparticle_chapter

end ThetLogos.DialOneAntiparticleChapter
