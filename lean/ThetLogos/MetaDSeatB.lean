import Mathlib.Tactic
import ThetLogos.MetaDPin

namespace ThetLogos

/-!
# ThetLogos.MetaDSeatB — MetaD seat B: the finite
correlation-response seat (Zero's "build it", 2026-11-12)

**Commission:** Zero, 2026-11-12 10:38 EST ("build it"),
immediately on the MetaD pin's landing (10:35 EST, "both and
title it MetaD"; pin: `ThetLogos.MetaDPin`, spec
`~/workspace/your_files/metad-pin-2026-11-12.md`). This module
builds the pin's seat B — and only seat B. Seat A has no
buildable experiment (K-METAD-NULL, fired on the pin's face);
the physical TCR rig is a separate, unfired design and is
NOT this module.

## Face declarations (read before anything below)

- **What this module proves, and all it proves:** the pin's
  definition of correlation response (seat B of
  `ThetLogos.MetaDPin`: a boundary-separated Gibbs pair, the
  response functional `R`, its product-state null `R_null`,
  the claim shape `R ≠ R_null`) has a **non-vacuous finite
  instance** — one concrete finite seat, exhibited below in
  full, where `R` provably differs from `R_null`. That is
  the only thing a pin may ever prove (pin sheet, seat B).
- **It does NOT prove cognition anywhere.** Zero's
  definition ("cognitive = correlation response",
  2026-11-11) is seated, not graded: a finite theorem about
  a definition is evidence about the definition's
  non-vacuity, never about any physical system.
  **Dial-ineligible; NO CLAIM; dials 0/4.**
- **The kills govern, and their status on this seat is
  stated here, not buried:**
  - **K-METAD-DRAIN does NOT fire on the exhibit seat:**
    `R ≠ R_null` is proved of it (headline theorem below),
    so `R = R_null` does not hold identically on the seat
    as defined. The coupled seat in brick B2's companion
    theorem is the exact boundary: on a *separable* seat
    (energy a sum of single-side terms, observables
    side-pure) `R = R_null` DOES hold identically — drain
    is a theorem about uncoupled seats, not a defect of
    this one.
  - **K-METAD-SHADOW does NOT fire on the exhibit:** its
    `R` is carried by the coupling across the boundary
    (the interaction energy at `(true, true)`); with the
    coupling removed the same observables give `R = R_null`
    by the separable-seat theorem, so the response is not a
    single-side functional in disguise.

## The exhibit

States `Bool × Bool` — two two-state sides across the drawn
boundary (`sideA` / `sideB` read the two coordinates).
Inverse temperature `β = 1`. The energy is 0 everywhere
except the joint state `(true, true)`, where it is `−1`: a
pure interaction term — no single-side energies at all. The
observables are the two sides' own state indicators.

The arithmetic (kernel-checked below): weights `e` at
`(true, true)` and `1` elsewhere; `Z = e + 3`;
`R = e / (e + 3)`; `R_null = ((e + 1) / (e + 3))²`; and
`R ≠ R_null` because `e ≠ 1`. Boundary first, coupling
across it, response read off it — the pin's shape, filled.

## Brick B2 — the drain boundary

The companion theorem (`metaDSeparable_response_eq_responseNull`,
below): on any seat over `α × β` whose energy separates
into single-side terms and whose observables are side-pure,
`R = R_null` identically — the Gibbs state factorizes and
there is nothing across the boundary to respond with. This
is the exact boundary of the exhibit's non-vacuity: drain
is a theorem about uncoupled seats. It is also the
K-METAD-SHADOW fence made precise — the exhibit's response
is carried by its coupling term, because the same shape of
seat without one provably has none.
-/

/-- **The exhibit's energy** — a pure interaction term: `−1`
at the joint state `(true, true)`, `0` at the other three.
No single-side part exists to carry anything. -/
noncomputable def metaDExhibitEnergy (p : Bool × Bool) : ℝ :=
  if p = (true, true) then -1 else 0

/-- **The exhibit's side-A observable** — the indicator of
side A's own state (first coordinate). -/
noncomputable def metaDExhibitObsA (p : Bool × Bool) : ℝ :=
  if p.1 then 1 else 0

/-- **The exhibit's side-B observable** — the indicator of
side B's own state (second coordinate). -/
noncomputable def metaDExhibitObsB (p : Bool × Bool) : ℝ :=
  if p.2 then 1 else 0

/-- **The exhibit seat** — the pin's `CorrResponseSeat` at
`Bool × Bool`, boundary drawn as the two coordinates,
`β = 1`, the coupled energy and the two side indicators. -/
noncomputable def metaDExhibit : CorrResponseSeat (Bool × Bool) where
  sideA := Finset.univ.filter (fun p => p.1 = true)
  sideB := Finset.univ.filter (fun p => p.2 = true)
  energy := metaDExhibitEnergy
  beta := 1
  obsA := metaDExhibitObsA
  obsB := metaDExhibitObsB

/-- **The exhibit's partition sum, in closed form:**
`Z = e + 3` — weight `e` at `(true, true)`, weight `1` at
the other three states. -/
theorem metaDExhibit_partitionSum :
    metaDExhibit.partitionSum = Real.exp 1 + 3 := by
  rw [CorrResponseSeat.partitionSum, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, metaDExhibit, metaDExhibitEnergy,
    Prod.mk.injEq, Bool.false_eq_true, true_and, and_true,
    and_false, false_and, ite_true, ite_false, one_mul,
    neg_neg, neg_zero, Real.exp_zero]
  ring

/-- **The exhibit's Gibbs sums, in closed form** — the one
computation every closed form below reads off: for any
weighting `g` of the four states, the Gibbs expectation of
`g` is the weight-`e` value at `(true, true)` plus the
three unit-weight values, over `Z = e + 3`. -/
theorem metaDExhibit_gibbsSum (g : Bool × Bool → ℝ) :
    (∑ p, metaDExhibit.gibbsProb p * g p)
      = (Real.exp 1 * g (true, true) + g (true, false)
        + g (false, true) + g (false, false)) / (Real.exp 1 + 3) := by
  have hZ : metaDExhibit.partitionSum = Real.exp 1 + 3 :=
    metaDExhibit_partitionSum
  have hterm : ∀ p : Bool × Bool,
      metaDExhibit.gibbsProb p * g p
        = (Real.exp (-(1 * metaDExhibitEnergy p)) * g p) / (Real.exp 1 + 3) := by
    intro p
    rw [CorrResponseSeat.gibbsProb, hZ]
    simp only [metaDExhibit]
    ring
  rw [Finset.sum_congr rfl (fun p _ => hterm p), ← Finset.sum_div,
    Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, metaDExhibitEnergy, Prod.mk.injEq,
    Bool.false_eq_true, true_and, and_true, and_false,
    false_and, ite_true, ite_false, one_mul, neg_neg,
    neg_zero, Real.exp_zero]
  ring

/-- **The exhibit's response, in closed form:**
`R = e / (e + 3)` — only the coupled state contributes to
the cross-boundary product. -/
theorem metaDExhibit_response :
    metaDExhibit.response = Real.exp 1 / (Real.exp 1 + 3) := by
  have h := metaDExhibit_gibbsSum
    (fun p => metaDExhibit.obsA p * metaDExhibit.obsB p)
  rw [CorrResponseSeat.response]
  simp only [mul_assoc]
  rw [h]
  simp only [metaDExhibit, metaDExhibitObsA, metaDExhibitObsB,
    Bool.false_eq_true, ite_true, ite_false, mul_one, mul_zero,
    add_zero, zero_add]

/-- **The exhibit's null, in closed form:**
`R_null = ((e + 1) / (e + 3))²`, written as the product of
the two equal side expectations `(e + 1) / (e + 3)`. -/
theorem metaDExhibit_responseNull :
    metaDExhibit.responseNull
      = (Real.exp 1 + 1) / (Real.exp 1 + 3)
        * ((Real.exp 1 + 1) / (Real.exp 1 + 3)) := by
  rw [CorrResponseSeat.responseNull, metaDExhibit_gibbsSum,
    metaDExhibit_gibbsSum]
  simp only [metaDExhibit, metaDExhibitObsA, metaDExhibitObsB,
    Bool.false_eq_true, ite_true, ite_false, mul_one, mul_zero,
    add_zero, zero_add]

/-- **THE HEADLINE — the exhibit exhibits correlation
response.** `R ≠ R_null` at the exhibit seat, in the pin's
own claim shape (`CorrResponseSeat.ExhibitsResponse`).
Equivalently `e ≠ 1`, cross-multiplied through `Z = e + 3`:
`e (e + 3) ≠ (e + 1)²` since `e > 1`. **K-METAD-DRAIN does
not fire on this seat.** What is proved is the definition's
non-vacuity at one finite seat — nothing about cognition in
any system, nothing about any dial. NO CLAIM. -/
theorem metaDExhibit_exhibitsResponse :
    metaDExhibit.ExhibitsResponse := by
  rw [CorrResponseSeat.ExhibitsResponse, metaDExhibit_response,
    metaDExhibit_responseNull]
  have he : (1 : ℝ) < Real.exp 1 := by
    have h := Real.exp_strictMono (show (0 : ℝ) < 1 by norm_num)
    rwa [Real.exp_zero] at h
  have hZ : (0 : ℝ) < Real.exp 1 + 3 := by
    linarith [Real.exp_pos 1]
  have hZne : Real.exp 1 + 3 ≠ 0 := ne_of_gt hZ
  intro h
  field_simp at h
  nlinarith [h, he, hZ, Real.exp_pos 1]

/-- **The separable-seat drain theorem.** On any seat over
`α × β` whose energy separates into single-side terms
(`E p = EA p.1 + EB p.2`) and whose observables are
side-pure (`obsA p = fA p.1`, `obsB p = fB p.2`),
`R = R_null` identically: the Gibbs weights factorize over
the boundary, every cross-boundary expectation splits, and
the response is the null. This is K-METAD-DRAIN's exact
habitat, proved as a theorem about uncoupled seats — and
the fence that keeps K-METAD-SHADOW off the exhibit above:
its nonzero `R` is carried by the coupling, since the
uncoupled shape provably carries none. NO CLAIM;
dial-ineligible. -/
theorem metaDSeparable_response_eq_responseNull
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (S : CorrResponseSeat (α × β))
    (EA : α → ℝ) (EB : β → ℝ) (fA : α → ℝ) (fB : β → ℝ)
    (hE : S.energy = fun p => EA p.1 + EB p.2)
    (hA : S.obsA = fun p => fA p.1)
    (hB : S.obsB = fun p => fB p.2) :
    S.response = S.responseNull := by
  have hexp : ∀ p : α × β,
      -(S.beta * S.energy p)
        = -(S.beta * EA p.1) + -(S.beta * EB p.2) := by
    intro p
    simp only [hE]
    ring
  have hw : ∀ p : α × β,
      Real.exp (-(S.beta * S.energy p))
        = Real.exp (-(S.beta * EA p.1))
          * Real.exp (-(S.beta * EB p.2)) := by
    intro p
    rw [hexp p, Real.exp_add]
  have hZ : S.partitionSum
      = (∑ a, Real.exp (-(S.beta * EA a)))
        * (∑ b, Real.exp (-(S.beta * EB b))) := by
    rw [CorrResponseSeat.partitionSum]
    simp only [hw]
    rw [Fintype.sum_prod_type]
    dsimp only
    have step : ∀ a : α,
        (∑ b, Real.exp (-(S.beta * EA a)) * Real.exp (-(S.beta * EB b)))
          = Real.exp (-(S.beta * EA a))
            * (∑ b, Real.exp (-(S.beta * EB b))) := by
      intro a
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun a _ => step a), Finset.sum_mul]
  have hZA : (0 : ℝ) < ∑ a, Real.exp (-(S.beta * EA a)) :=
    Finset.sum_pos (fun a _ => Real.exp_pos _) Finset.univ_nonempty
  have hZB : (0 : ℝ) < ∑ b, Real.exp (-(S.beta * EB b)) :=
    Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  have hg : ∀ p : α × β, S.gibbsProb p
      = (Real.exp (-(S.beta * EA p.1))
          / (∑ a, Real.exp (-(S.beta * EA a))))
        * (Real.exp (-(S.beta * EB p.2))
          / (∑ b, Real.exp (-(S.beta * EB b)))) := by
    intro p
    rw [CorrResponseSeat.gibbsProb, hZ, hw p, div_mul_div_comm]
  have hresp : S.response
      = (∑ a, Real.exp (-(S.beta * EA a)) * fA a
          / (∑ a', Real.exp (-(S.beta * EA a'))))
        * (∑ b, Real.exp (-(S.beta * EB b)) * fB b
          / (∑ b', Real.exp (-(S.beta * EB b')))) := by
    have hterm : ∀ p : α × β,
        S.gibbsProb p * S.obsA p * S.obsB p
          = (Real.exp (-(S.beta * EA p.1)) * fA p.1
              / (∑ a, Real.exp (-(S.beta * EA a))))
            * (Real.exp (-(S.beta * EB p.2)) * fB p.2
              / (∑ b, Real.exp (-(S.beta * EB b)))) := by
      intro p
      rw [hg p]
      simp only [hA, hB]
      ring
    rw [CorrResponseSeat.response,
      Finset.sum_congr rfl (fun p _ => hterm p),
      Fintype.sum_prod_type]
    dsimp only
    have step : ∀ a : α,
        (∑ b, (Real.exp (-(S.beta * EA a)) * fA a
            / (∑ a', Real.exp (-(S.beta * EA a'))))
          * (Real.exp (-(S.beta * EB b)) * fB b
            / (∑ b', Real.exp (-(S.beta * EB b')))))
          = (Real.exp (-(S.beta * EA a)) * fA a
              / (∑ a', Real.exp (-(S.beta * EA a'))))
            * (∑ b, Real.exp (-(S.beta * EB b)) * fB b
              / (∑ b', Real.exp (-(S.beta * EB b')))) := by
      intro a
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun a _ => step a), Finset.sum_mul]
  have hfac1 : (∑ p : α × β, S.gibbsProb p * S.obsA p)
      = (∑ a, Real.exp (-(S.beta * EA a)) * fA a
          / (∑ a', Real.exp (-(S.beta * EA a')))) := by
    have hterm : ∀ p : α × β, S.gibbsProb p * S.obsA p
        = (Real.exp (-(S.beta * EA p.1)) * fA p.1
            / (∑ a, Real.exp (-(S.beta * EA a))))
          * (Real.exp (-(S.beta * EB p.2))
            / (∑ b, Real.exp (-(S.beta * EB b)))) := by
      intro p
      rw [hg p]
      simp only [hA]
      ring
    have h1 : (∑ b, Real.exp (-(S.beta * EB b))
        / (∑ b', Real.exp (-(S.beta * EB b')))) = 1 := by
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt hZB)
    rw [Finset.sum_congr rfl (fun p _ => hterm p),
      Fintype.sum_prod_type]
    dsimp only
    have step : ∀ a : α,
        (∑ b, (Real.exp (-(S.beta * EA a)) * fA a
            / (∑ a', Real.exp (-(S.beta * EA a'))))
          * (Real.exp (-(S.beta * EB b))
            / (∑ b', Real.exp (-(S.beta * EB b')))))
          = (Real.exp (-(S.beta * EA a)) * fA a
              / (∑ a', Real.exp (-(S.beta * EA a'))))
            * (∑ b, Real.exp (-(S.beta * EB b))
              / (∑ b', Real.exp (-(S.beta * EB b')))) := by
      intro a
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun a _ => step a)]
    simp only [h1, mul_one]
  have hfac2 : (∑ p : α × β, S.gibbsProb p * S.obsB p)
      = (∑ b, Real.exp (-(S.beta * EB b)) * fB b
          / (∑ b', Real.exp (-(S.beta * EB b')))) := by
    have hterm : ∀ p : α × β, S.gibbsProb p * S.obsB p
        = (Real.exp (-(S.beta * EA p.1))
            / (∑ a, Real.exp (-(S.beta * EA a))))
          * (Real.exp (-(S.beta * EB p.2)) * fB p.2
            / (∑ b, Real.exp (-(S.beta * EB b)))) := by
      intro p
      rw [hg p]
      simp only [hB]
      ring
    have h1 : (∑ a, Real.exp (-(S.beta * EA a))
        / (∑ a', Real.exp (-(S.beta * EA a')))) = 1 := by
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt hZA)
    rw [Finset.sum_congr rfl (fun p _ => hterm p),
      Fintype.sum_prod_type]
    dsimp only
    rw [Finset.sum_comm]
    have step : ∀ b : β,
        (∑ a, (Real.exp (-(S.beta * EA a))
            / (∑ a', Real.exp (-(S.beta * EA a'))))
          * (Real.exp (-(S.beta * EB b)) * fB b
            / (∑ b', Real.exp (-(S.beta * EB b')))))
          = (∑ a, Real.exp (-(S.beta * EA a))
              / (∑ a', Real.exp (-(S.beta * EA a'))))
            * (Real.exp (-(S.beta * EB b)) * fB b
              / (∑ b', Real.exp (-(S.beta * EB b')))) := by
      intro b
      rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun b _ => step b)]
    simp only [h1, one_mul]
  rw [CorrResponseSeat.responseNull, hfac1, hfac2]
  exact hresp

end ThetLogos
