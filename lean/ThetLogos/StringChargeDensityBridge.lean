/-
# StringChargeDensityBridge — the weld, seated on the census seat

**Scope: ~/workspace/your_files/charge-density-bridge-scope-2026-11-17.md
(Zero, 2026-11-17 23:51 EST — "we need to weld the charge density
bridge"). Charter: T5 design study. NO CLAIM. Dial-ineligible.
Dials 0/4.**

THE AUDIT VERDICT (the scope's §0, firsthand 2026-11-17): the weld's
in-module seat (`StringChargeDensityPin` §1) is a VERBATIM copy of the
census seat (`StringSeatPin` §1) — same configuration type, same bend
cost and bend energy bodies, same straight configuration, statements
and proof scripts character-identical across all 65 lines modulo one
docstring clause. The two seats are DEFINITIONALLY IDENTICAL. There is
no isomorphism to construct: the correspondence is the identity, and
this module is the short identification-and-transport record that
proves the three definitional equalities and re-seats the weld's
C-1..C-5 over the census seat's `bendEnergy`, so later work over the
census seat composes with the weld without a namespace gap. A weld
seam, not a new span. De-duplication is explicitly out of scope: the
weld module is not refactored by this bridge.

BRICK 1 — seat identification (CD-1..CD-5). BRICK 2 — transport of
the weld (CD-6a..CD-6e), appended below brick 1 when it lands.

KILLS ARMED (the scope's §3): K-CD-SEAT (a CD-1/2/3 identification
not provable by definitional unfolding — a divergence the text audit
missed), K-CD-WEIGHT (CD-4 failing after CD-2 — a module not using
the shared `ModularVariance.gibbsProb` / `partSum` as read),
K-CD-DENSITY (a CD-6 transport failing — the named C-item depends on
more than the energy's identity). Inherited fences stand: V-9 (this
bridge joins the weld to the STRING seat; it couples no charge to
mass and may never be cited as a charge–mass connection),
K-STRING-PHYS, K-STRING-KNOT, K-PLANCK-SEAT. Constructed-target
exposure inherited from both parents: the charge assignment is
chosen, the seat is finite, the density is a classical expectation.

Naming: `StringChargeDensityBridge` is the scope's working label;
final naming is Zero's hand.

STATUS: built in the main tree as INTEG-EVERYTHING T7's closing
brick (2026-11-19); census at the T7 integration.
-/

import Mathlib.Tactic
import ThetLogos.StringSeatPin
import ThetLogos.StringChargeDensityPin

namespace ThetLogos.StringChargeDensityBridge

variable {n k : ℕ}

/-! ## Brick 1 — seat identification (CD-1..CD-5) -/

/-- **CD-1 (bend cost identification)**: the weld's bend cost IS the
census seat's bend cost, pointwise — the two bodies are the same
`if s = 0 then 0 else 1`, so the equality is definitional. -/
theorem bendCost_eq (s : Fin (k + 1)) :
    StringChargeDensityPin.bendCost s = StringSeatPin.bendCost s :=
  rfl

/-- **CD-2 (bend energy identification)**: the weld's bend energy IS
the census seat's bend energy, as functions — both are
`∑ i, bendCost (c i)` over definitionally equal costs. -/
theorem bendEnergy_eq :
    (StringChargeDensityPin.bendEnergy : (Fin n → Fin (k + 1)) → ℝ)
      = StringSeatPin.bendEnergy := by
  funext c
  exact Finset.sum_congr rfl (fun i _ => bendCost_eq (c i))

/-- **CD-3 (ground configuration identification)**: the weld's
straight configuration IS the census seat's — both are `fun _ => 0`. -/
theorem straightConfig_eq :
    (StringChargeDensityPin.straightConfig : Fin n → Fin (k + 1))
      = StringSeatPin.straightConfig :=
  rfl

/-- **CD-4, weight half (Gibbs weights transport)**: at every slope
and configuration, the Gibbs weight computed from the weld's energy
is the weight computed from the census seat's energy — one rewrite
by CD-2, since both modules apply the same shared
`ModularVariance.gibbsProb`. -/
theorem gibbsProb_eq (β : ℝ) (c : Fin n → Fin (k + 1)) :
    ModularVariance.gibbsProb
        (StringChargeDensityPin.bendEnergy : (Fin n → Fin (k + 1)) → ℝ)
        β c
      = ModularVariance.gibbsProb
          (StringSeatPin.bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β c := by
  rw [bendEnergy_eq]

/-- **CD-4, partition half (partition functions transport)**: the
partition sum over the weld's energy is the partition sum over the
census seat's energy, at every slope. -/
theorem partSum_eq (β : ℝ) :
    ModularVariance.partSum
        (StringChargeDensityPin.bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β
      = ModularVariance.partSum
          (StringSeatPin.bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β := by
  rw [bendEnergy_eq]

/-- **CD-5 (density over the census seat)**: the weld's density IS
the Gibbs expectation over the census seat's energy — the density's
own body is the expectation over the weld's energy, and CD-2
re-seats the energy argument. (The charge layer — `chargeAt`,
`totalCharge`, `density` — exists only in the weld; the transport
re-seats its energy argument, it does not move the charge layer.) -/
theorem density_eq (q : Fin n → ℤ) (β : ℝ) (i : Fin n) :
    StringChargeDensityPin.density k q β i
      = ModularVariance.gibbsExpect
          (StringSeatPin.bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β
          (fun c => StringChargeDensityPin.chargeAt q c i) := by
  unfold StringChargeDensityPin.density
  rw [bendEnergy_eq]

/-! ## Brick 2 — transport of the weld (CD-6a..CD-6e)

Each corollary is the corresponding landed C-item with its energy
argument re-seated on the census seat via Brick 1 — no C-item's
argument is re-proved anywhere below. -/

/-- **CD-6a (C-1 over the census seat)**: the density profile sums
to the Gibbs expectation of the total charge, with the expectation
taken at the census seat's `bendEnergy`. -/
theorem density_sum_seat (q : Fin n → ℤ) (β : ℝ) :
    ∑ i, StringChargeDensityPin.density k q β i
      = ModularVariance.gibbsExpect
          (StringSeatPin.bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β
          ((StringChargeDensityPin.totalCharge q) :
            (Fin n → Fin (k + 1)) → ℝ) := by
  have h := StringChargeDensityPin.density_sum (n := n) (k := k) q β
  rwa [bendEnergy_eq] at h

/-- **CD-6b (C-2 over the census seat)**: hot uniformity of the
transported density — at `β = 0` the census-seat expectation of the
charge present at a site is its plain average over all
configurations. -/
theorem density_zero_seat (q : Fin n → ℤ) (i : Fin n) :
    ModularVariance.gibbsExpect
        (StringSeatPin.bendEnergy : (Fin n → Fin (k + 1)) → ℝ) 0
        (fun c => StringChargeDensityPin.chargeAt q c i)
      = (∑ c : Fin n → Fin (k + 1),
          StringChargeDensityPin.chargeAt q c i)
        / (Fintype.card (Fin n → Fin (k + 1)) : ℝ) := by
  rw [← density_eq]
  exact StringChargeDensityPin.density_zero (n := n) (k := k) q i

/-- **CD-6c (C-3 over the census seat)**: charge-flip symmetry of
the transported density — negating the assignment negates the
census-seat expectation, at every `β`. -/
theorem density_neg_seat (q : Fin n → ℤ) (β : ℝ) (i : Fin n) :
    ModularVariance.gibbsExpect
        (StringSeatPin.bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β
        (fun c => StringChargeDensityPin.chargeAt (fun j => -(q j)) c i)
      = - ModularVariance.gibbsExpect
          (StringSeatPin.bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β
          (fun c => StringChargeDensityPin.chargeAt q c i) := by
  calc ModularVariance.gibbsExpect
        (StringSeatPin.bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β
        (fun c => StringChargeDensityPin.chargeAt (fun j => -(q j)) c i)
      = StringChargeDensityPin.density k (fun j => -(q j)) β i :=
        (density_eq (fun j => -(q j)) β i).symm
    _ = - StringChargeDensityPin.density k q β i :=
        StringChargeDensityPin.density_neg (n := n) (k := k) q β i
    _ = - ModularVariance.gibbsExpect
          (StringSeatPin.bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β
          (fun c => StringChargeDensityPin.chargeAt q c i) := by
        rw [density_eq]

/-- **CD-6d, deviation half (C-4's deviation over the census
seat)**: for assignments bounded by `1` and `β ≥ 0`, the
census-seat density at a site deviates from the site's own charge
by at most `(#configurations − 1) · e^{−β}`. -/
theorem density_deviation_seat (q : Fin n → ℤ) (hq : ∀ j, |q j| ≤ 1)
    (β : ℝ) (hβ : 0 ≤ β) (i : Fin n) :
    |ModularVariance.gibbsExpect
        (StringSeatPin.bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β
        (fun c => StringChargeDensityPin.chargeAt q c i) - (q i : ℝ)|
      ≤ ((Fintype.card (Fin n → Fin (k + 1)) : ℝ) - 1)
        * Real.exp (-β) := by
  rw [← density_eq]
  exact StringChargeDensityPin.density_deviation q hq hβ i

/-- **CD-6d, weight half (C-4's weight bound IS the seat's S-4)**:
the weld's `cold_weight`, transported by CD-3 and CD-4, is exactly
the census seat's own `cold_concentration` — the same statement
over the census seat's names, proved here by citing S-4 directly,
as the bridge scope sanctions. -/
theorem cold_weight_seat (β : ℝ) (hβ : 0 ≤ β) :
    ∑ c ∈ Finset.univ
        \ {(StringSeatPin.straightConfig : Fin n → Fin (k + 1))},
        ModularVariance.gibbsProb
          (StringSeatPin.bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β c
      ≤ ((Fintype.card (Fin n → Fin (k + 1)) : ℝ) - 1)
        * Real.exp (-β) :=
  StringSeatPin.cold_concentration hβ

/-- **CD-6e (C-5 over the census seat)**: the spread/concentrate
pair, transported whole — hot uniformity at `β = 0` and the cold
deviation bound at every `β ≥ 0`, both read off the census seat's
energy. -/
theorem hot_cold_profile_seat (q : Fin n → ℤ) (hq : ∀ j, |q j| ≤ 1)
    (i : Fin n) :
    (ModularVariance.gibbsExpect
        (StringSeatPin.bendEnergy : (Fin n → Fin (k + 1)) → ℝ) 0
        (fun c => StringChargeDensityPin.chargeAt q c i)
      = (∑ c : Fin n → Fin (k + 1),
          StringChargeDensityPin.chargeAt q c i)
        / (Fintype.card (Fin n → Fin (k + 1)) : ℝ))
    ∧ (∀ β : ℝ, 0 ≤ β →
        |ModularVariance.gibbsExpect
            (StringSeatPin.bendEnergy : (Fin n → Fin (k + 1)) → ℝ) β
            (fun c => StringChargeDensityPin.chargeAt q c i)
          - (q i : ℝ)|
        ≤ ((Fintype.card (Fin n → Fin (k + 1)) : ℝ) - 1)
          * Real.exp (-β)) :=
  ⟨density_zero_seat q i,
   fun β hβ => density_deviation_seat q hq β hβ i⟩

end ThetLogos.StringChargeDensityBridge
