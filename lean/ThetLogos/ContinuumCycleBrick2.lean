import Mathlib.Tactic
import ThetLogos.ContinuumCyclePin

/-!
# ThetLogos.ContinuumCycleBrick2 — the forcing has teeth, and K-FORCE-GEOM fires (T5 charter; NO CLAIM)

Working label only — naming is Zero's hand. Brick 2 of
the Continuum Cycle line: what `cycleGeometryForced`'s
hypothesis — the thermal-dynamical data — actually
determines, and where it stops.

## The teeth (proved)

`forced_teeth`: if two seats' data agree (the static
charge of every configuration, and of every
configuration carried by the motion), then

1. their charge assignments are EQUAL — the data see
   the charge function pointwise (test with the basis
   configurations), and
2. for every position `j`, the charge-weighted fiber
   sums over the exchange preimages agree:
   `∑ i ∈ exch'⁻¹(j), charge i = ∑ i ∈ exch⁻¹(j),
   charge i` (test with the configuration carried to
   the indicator of `j`).

That is exactly what the data see of the exchange:
the exchange as read through charge-weighted
preimage sums. Nothing more is in the data.

## The kill (proved)

**K-FORCE-GEOM FIRES.** `forced_kill`:
`cycleGeometryForced` is FALSE on `zeroSeatId` — the
Fin 2 seat with identically zero charge and identity
exchange. The seat `zeroSeatSwap` (same zero charge,
exchange swapping the two points) carries IDENTICAL
thermal-dynamical data — every charge in sight is
`0 = 0` — but a different standing locus: under the
identity every configuration stands, while
`![1, 0]` does not stand under the swap. Two distinct
geometries on seats with identical thermal-dynamical
data: the pinned statement GEOMETRY FORCED dies at
the finite level.

The teeth and the kill are the same fact read from
two sides: the data determine the charge-weighted
preimage sums (teeth), and where the charges vanish
those sums are `0` for every exchange — the exchange
becomes invisible to the data, and the locus, which
the exchange alone fixes, is free to differ (kill).
Any revival of the forcing must add data the charge
functionals cannot see — a new registration, a new
scope, Zero's word. This line does not re-aim the
statement silently.

## Walls named on the face

- **K-SHADOW-IDENTITY** (standing tension, unsoftened):
  shadows hold for every weighting and pick out no
  gravity object. This line does not dissolve it and
  claims no gravity object.
- Per Zero's register (2026-11-24): a completed finite
  theorem is not a continuum theorem. T5 charter,
  NO CLAIM; dials 0/4.
-/

namespace ThetLogos

/-- **The forcing's teeth.** The thermal-dynamical
data of `cycleGeometryForced`'s hypothesis determine:
(1) the charge assignment itself, pointwise; (2) for
every position `j`, the charge-weighted sum over the
exchange's preimage of `j` — for both exchanges.
That is all the data see, and the next theorem shows
it is not enough. -/
theorem forced_teeth {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S S' : CycleSeat Ω)
    (hdata : ∀ p : Ω → ℝ,
      nedCharge S'.charge p = nedCharge S.charge p ∧
        nedCharge S'.charge (fun i => p (S'.exch i))
          = nedCharge S.charge (fun i => p (S.exch i))) :
    S'.charge = S.charge ∧
      ∀ j : Ω, ∑ i ∈ Finset.univ.filter (fun i => S'.exch i = j),
            (S.charge i : ℝ)
          = ∑ i ∈ Finset.univ.filter (fun i => S.exch i = j),
            (S.charge i : ℝ) := by
  have hcharge : S'.charge = S.charge := by
    funext i
    have h := (hdata (fun k => if k = i then 1 else 0)).1
    simp only [nedCharge, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    exact_mod_cast h
  refine ⟨hcharge, ?_⟩
  intro j
  have h2 : nedCharge S.charge
        (fun i => (fun k => if k = j then (1 : ℝ) else 0) (S'.exch i))
      = nedCharge S.charge
        (fun i => (fun k => if k = j then (1 : ℝ) else 0) (S.exch i)) := by
    have h := (hdata (fun k => if k = j then (1 : ℝ) else 0)).2
    rwa [hcharge] at h
  have conv : ∀ e : Ω → Ω,
      nedCharge S.charge
          (fun i => (fun k => if k = j then (1 : ℝ) else 0) (e i))
        = ∑ i ∈ Finset.univ.filter (fun i => e i = j),
          (S.charge i : ℝ) := by
    intro e
    rw [nedCharge, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : e i = j <;> simp [hi]
  rwa [conv, conv] at h2

/-- **The zero-charge seat with identity exchange.**
Every thermal-dynamical datum of this seat is `0`;
its standing locus is everything. -/
def zeroSeatId : CycleSeat (Fin 2) :=
  { charge := fun _ => 0, distant := ∅, exch := id }

/-- **The zero-charge seat with swapping exchange.**
The same charge data as `zeroSeatId` — identically
zero — but its standing locus is only the symmetric
configurations. -/
def zeroSeatSwap : CycleSeat (Fin 2) :=
  { charge := fun _ => 0, distant := ∅, exch := ![1, 0] }

/-- **K-FORCE-GEOM FIRES.** `cycleGeometryForced` is
false on `zeroSeatId`: `zeroSeatSwap` agrees with it
on every thermal-dynamical datum (all charges are
zero, on both sides, carried or not) yet their
standing loci differ — `![1, 0]` stands under the
identity and not under the swap. The geometry is NOT
determined by the thermal-dynamical data at the
finite level; GEOMETRY FORCED, as pinned, is dead. -/
theorem forced_kill : ¬ cycleGeometryForced zeroSeatId := by
  intro h
  have hdata : ∀ p : Fin 2 → ℝ,
      nedCharge zeroSeatSwap.charge p
          = nedCharge zeroSeatId.charge p ∧
        nedCharge zeroSeatSwap.charge
            (fun i => p (zeroSeatSwap.exch i))
          = nedCharge zeroSeatId.charge
            (fun i => p (zeroSeatId.exch i)) := by
    intro p
    constructor <;> simp [nedCharge, zeroSeatId, zeroSeatSwap]
  have hiff := h zeroSeatSwap hdata ![1, 0]
  have hstand : (fun i => (![1, 0] : Fin 2 → ℝ) (zeroSeatId.exch i))
      = ![1, 0] := rfl
  have hL := hiff.mpr hstand
  have h0 := congrFun hL 0
  simp [zeroSeatSwap] at h0

end ThetLogos
