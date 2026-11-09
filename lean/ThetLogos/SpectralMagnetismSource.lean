import Mathlib.Tactic
import ThetLogos.SpectralMagnetism
import ThetLogos.BoundarySeat

namespace ThetLogos

/-!
# ThetLogos.SpectralMagnetismSource — SM-2: the sourcing clause at the grounded seat (working label)

Form (4) of the Spectral Magnetism exhibit, from the scoping
`~/workspace/your_files/spectral-magnetism-scope-2026-11-08.md`
(§3.3 form (4); §4, shape (c)): at the grounded Poisson seat
(UA-2, `BoundarySeat` — the corpus's one bulk-sensitive
channel; contrast the closed seat's total-mass blindness,
`PoissonTotalMassBlindness`), a **defined source** is built
from a base source `ρ` plus the spectral functional of the
local occupation, and the grounded potential is proved to
*detect* the state term at fixed total source — a sensitivity
theorem of the UA-2 pattern, about the defined source.
**Price: band S, 4–8 strict, pre-registered DIAL-INELIGIBLE.
NO CLAIM. Dials 0/4. Dial 2 = 0.**

## The fences (verbatim in substance, on the face)

- **A defined source is not a field equation.** This module
  defines a source functional and proves finite theorems
  about the grounded seat's response to it. Nothing here is
  a law of nature, an action, or a varied equation.
- **K-SM-PROXY — ARMED.** Nothing in this module names the
  defined source a gravitational mass, a weight, or a
  coupling; no statement reads it as gravity. Any such
  reading fires the kill.
- **No descent/response rule consumes the defined source.**
  No body falls, descends, or answers to it here.
- **Pre-registered DIAL-INELIGIBLE; Dial 2 = 0 on every
  outcome.** Finite theorems about a defined source at a
  finite seat are Register-A mathematics.

## What stands here

1. **The defined source** — `spectralSource ρ x`, pointwise
   `ρ i + occEnt (x i)`: the base source plus SM-1's
   pointwise spectral functional (the site entropy
   `occEnt`, whose sum is SM-1's `spectralWeight`) of the
   local occupation `x i`.
2. **Its total** — `sum_spectralSource`: the total of the
   defined source is `∑ ρ + spectralWeight x`, so two
   configurations over the same base with equal spectral
   weights have **equal total source**
   (`spectralSource_total_eq_of_spectralWeight_eq`) — the
   exhibit's fixed-total condition.
3. **Sensitivity (headline)** —
   `groundedPotential_spectralSource_ne`: at fixed total
   source, if the two defined sources differ at one
   ungrounded site, their grounded potentials differ. The
   proof is UA-2's own: equal grounded potentials have
   equal Laplacians at every ungrounded site, and there the
   Laplacian *is* the source
   (`interior_eq_of_groundedPotential_eq`).
   `groundedPotential_spectralSource_ne_of_local` is the
   spectral form (same base, equal spectral weights, local
   site entropies different); the field form and an
   existence-of-a-detecting-quantity form follow by UA-2's
   drop-to-the-ground argument.
4. **Non-vacuity witness** —
   `spectralSource_grounded_witness`: on `Fin 2` with the
   constant weight `1`, ground `1`, base `0`, the swapped
   interior states `(1/4, 1/2)` and `(1/2, 1/4)` have equal
   spectral weights (SM-1's swap symmetry, hence equal
   total source) but different local site entropies at
   site `0` (`occEnt (1/4) ≠ log 2 = occEnt (1/2)`, since
   `occEnt (1/4) = log 4 − (3/4) log 3` and `log 16 ≠ log 27`),
   so their grounded potentials provably differ.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The defined source (SM-2, Register A — a declaration,
not a claim):** the base source `ρ` plus the spectral
functional of the local occupation — pointwise, SM-1's site
entropy `occEnt` evaluated at the local occupation `x i`.
Its sum over the seat is `spectralWeight x` (§ total below).
No statement in this module names or treats this source as
a gravitational mass, a weight, or a coupling, and no
descent or response rule consumes it (K-SM-PROXY's fence is
part of this definition's reading). Tier T1 (definition). -/
noncomputable def spectralSource (ρ x : V → ℝ) : V → ℝ :=
  fun i => ρ i + occEnt (x i)

omit [DecidableEq V] in
/-- **The total of the defined source:** `∑ ρ` plus the
spectral weight of the occupation profile — the local
spectral terms assemble into exactly SM-1's functional.
Tier T1. -/
theorem sum_spectralSource (ρ x : V → ℝ) :
    ∑ i, spectralSource ρ x i = (∑ i, ρ i) + spectralWeight x := by
  show (∑ i, (ρ i + occEnt (x i))) = (∑ i, ρ i) + spectralWeight x
  rw [Finset.sum_add_distrib]
  rfl

omit [DecidableEq V] in
/-- **Fixed total from equal spectral weights:** over the
same base source, two occupation profiles with equal
spectral weights give defined sources of equal total — the
exhibit's fixed-total-source condition, in spectral form.
Tier T1. -/
theorem spectralSource_total_eq_of_spectralWeight_eq (ρ : V → ℝ)
    {x x' : V → ℝ} (h : spectralWeight x = spectralWeight x') :
    ∑ i, spectralSource ρ x i = ∑ i, spectralSource ρ x' i := by
  rw [sum_spectralSource, sum_spectralSource, h]

/-- **HEADLINE — sensitivity at fixed total source (UA-2
pattern).** Two defined sources with *equal total source*
whose values differ at one ungrounded site `i` have
*different grounded potentials*: were the potentials equal,
UA-2's inversion would force the sources to agree at `i`
(`interior_eq_of_groundedPotential_eq`), since there the
Laplacian of the grounded potential is the source itself.
A theorem about a DEFINED source (fences in the header):
it names no field equation and no gravitational reading.
Tier T1. -/
theorem groundedPotential_spectralSource_ne (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (ρ ρ' x x' : V → ℝ)
    (_htot : ∑ i, spectralSource ρ x i
      = ∑ i, spectralSource ρ' x' i)
    {i : V} (hi : i ≠ b)
    (hsrc : spectralSource ρ x i ≠ spectralSource ρ' x' i) :
    groundedPotential w hw hw0 hpos b (spectralSource ρ x)
      ≠ groundedPotential w hw hw0 hpos b (spectralSource ρ' x') := by
  intro hEq
  exact hsrc (interior_eq_of_groundedPotential_eq w hw hw0 hpos b
    (spectralSource ρ x) (spectralSource ρ' x') hEq hi)

/-- **Sensitivity, spectral form.** Over the same base
source, two occupation profiles with equal spectral weights
(hence equal total source, by
`spectralSource_total_eq_of_spectralWeight_eq`) whose local
site entropies differ at one ungrounded site have different
grounded potentials: at fixed total source, the grounded
potential detects the spectral-state term. Tier T1. -/
theorem groundedPotential_spectralSource_ne_of_local
    (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (ρ x x' : V → ℝ)
    (hSW : spectralWeight x = spectralWeight x')
    {i : V} (hi : i ≠ b) (hocc : occEnt (x i) ≠ occEnt (x' i)) :
    groundedPotential w hw hw0 hpos b (spectralSource ρ x)
      ≠ groundedPotential w hw hw0 hpos b (spectralSource ρ x') := by
  apply groundedPotential_spectralSource_ne w hw hw0 hpos b ρ ρ x x'
    _ hi
  · show ρ i + occEnt (x i) ≠ ρ i + occEnt (x' i)
    exact fun h => hocc (add_left_cancel h)
  · exact spectralSource_total_eq_of_spectralWeight_eq ρ hSW

/-- **Sensitivity at the field.** The grounded *fields* of
the two defined sources in
`groundedPotential_spectralSource_ne_of_local` also differ:
were the fields equal, the drop to the ground would force
the two grounded potentials — both pinned to `0` at the
ground — to agree, contradicting the potential form
(UA-2's own argument for `groundedField_add_const_ne`).
Tier T1. -/
theorem groundedField_spectralSource_ne_of_local
    (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (ρ x x' : V → ℝ)
    (hSW : spectralWeight x = spectralWeight x')
    {i : V} (hi : i ≠ b) (hocc : occEnt (x i) ≠ occEnt (x' i)) :
    groundedField w hw hw0 hpos b (spectralSource ρ x)
      ≠ groundedField w hw hw0 hpos b (spectralSource ρ x') := by
  intro hEq
  have hpot : groundedPotential w hw hw0 hpos b (spectralSource ρ x)
      = groundedPotential w hw hw0 hpos b (spectralSource ρ x') := by
    funext k
    have hd : dropVec (groundedPotential w hw hw0 hpos b
          (spectralSource ρ x)) k b
        = dropVec (groundedPotential w hw hw0 hpos b
          (spectralSource ρ x')) k b :=
      congrFun (congrFun hEq k) b
    rw [dropVec_apply, dropVec_apply,
      groundedPotential_at_ground, groundedPotential_at_ground] at hd
    linarith
  exact groundedPotential_spectralSource_ne_of_local w hw hw0 hpos b
    ρ x x' hSW hi hocc hpot

/-- **A quantity of the grounded field detects the state
term.** The positive counterpart form, as in UA-2's
`exists_groundedField_detects_totalMass`: under the
hypotheses of the field sensitivity theorem there is a
quantity of the field data at which the two defined
sources' fields provably differ. Detecting a defined
source's state term is all this says. Tier T1. -/
theorem exists_groundedField_quantity_detects_spectral
    (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (ρ x x' : V → ℝ)
    (hSW : spectralWeight x = spectralWeight x')
    {i : V} (hi : i ≠ b) (hocc : occEnt (x i) ≠ occEnt (x' i)) :
    ∃ F : (V → V → ℝ) → ℝ,
      F (groundedField w hw hw0 hpos b (spectralSource ρ x))
        ≠ F (groundedField w hw hw0 hpos b (spectralSource ρ x')) := by
  have hne := groundedField_spectralSource_ne_of_local w hw hw0 hpos b
    ρ x x' hSW hi hocc
  rw [Function.ne_iff] at hne
  obtain ⟨p, hp⟩ := hne
  rw [Function.ne_iff] at hp
  obtain ⟨q, hq⟩ := hp
  exact ⟨fun X => X p q, hq⟩

/-- **The site entropy at `1/4` is not `log 2`.**
`occEnt (1/4) = log 4 − (3/4) · log 3`; equality with
`log 2` would give `4 · log 2 = 3 · log 3`, i.e.
`log 16 = log 27`, i.e. `16 = 27`. Tier T1. -/
theorem occEnt_quarter_ne_log_two :
    occEnt (1 / 4 : ℝ) ≠ Real.log 2 := by
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hval : occEnt (1 / 4 : ℝ)
      = Real.log 4 - (3 / 4) * Real.log 3 := by
    have h14 : Real.log (1 / 4 : ℝ) = - Real.log 4 := by
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv]
    have h34 : Real.log (3 / 4 : ℝ) = Real.log 3 - Real.log 4 :=
      Real.log_div (by norm_num) (by norm_num)
    have hsub : (1 : ℝ) - 1 / 4 = 3 / 4 := by norm_num
    show -(1 / 4 : ℝ) * Real.log (1 / 4)
        - (1 - 1 / 4) * Real.log (1 - 1 / 4)
      = Real.log 4 - (3 / 4) * Real.log 3
    rw [hsub, h14, h34]
    ring
  intro h
  rw [hval, hlog4] at h
  -- `h : 2 log 2 − (3/4) log 3 = log 2`, so `4 log 2 = 3 log 3`.
  have h43 : 4 * Real.log 2 = 3 * Real.log 3 := by linarith
  have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have h27 : Real.log (27 : ℝ) = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hcontra : (16 : ℝ) = 27 := by
    have he : Real.log (16 : ℝ) = Real.log (27 : ℝ) := by
      rw [h16, h27, h43]
    have := congrArg Real.exp he
    rwa [Real.exp_log (by norm_num), Real.exp_log (by norm_num)] at this
  norm_num at hcontra

/-- **Non-vacuity witness (Fin 2).** With the constant
weight `1`, ground `1`, and zero base source, the swapped
interior states `(1/4, 1/2)` and `(1/2, 1/4)` define sources
of equal total (their spectral weights agree by SM-1's swap
symmetry) whose grounded potentials provably differ: the
local spectral term at the ungrounded site `0` is
`occEnt (1/4)` in one and `occEnt (1/2) = log 2` in the
other, and those are different numbers
(`occEnt_quarter_ne_log_two`). The sensitivity theorems
above are not vacuous. Tier T1. -/
theorem spectralSource_grounded_witness :
    groundedPotential (fun _ _ : Fin 2 => (1 : ℝ))
        (fun _ _ => rfl) (fun _ _ => by norm_num)
        (fun _ _ _ => by norm_num) 1
        (spectralSource 0 (![1 / 4, 1 / 2] : Fin 2 → ℝ))
      ≠ groundedPotential (fun _ _ : Fin 2 => (1 : ℝ))
        (fun _ _ => rfl) (fun _ _ => by norm_num)
        (fun _ _ _ => by norm_num) 1
        (spectralSource 0 (![1 / 2, 1 / 4] : Fin 2 → ℝ)) := by
  apply groundedPotential_spectralSource_ne_of_local
    (fun _ _ : Fin 2 => (1 : ℝ)) (fun _ _ => rfl)
    (fun _ _ => by norm_num) (fun _ _ _ => by norm_num) 1 0
    _ _ (spectralWeight_swap (1 / 4) (1 / 2))
    (i := (0 : Fin 2)) (by decide)
  show occEnt ((![1 / 4, 1 / 2] : Fin 2 → ℝ) 0)
    ≠ occEnt ((![1 / 2, 1 / 4] : Fin 2 → ℝ) 0)
  simp only [Matrix.cons_val_zero]
  rw [occEnt_half]
  exact occEnt_quarter_ne_log_two

end ThetLogos
