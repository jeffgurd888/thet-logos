import Mathlib.Tactic
import ThetLogos.ThermoelectricSeat
import ThetLogos.BoundarySeat

/-!
# ThetLogos.ChargeMassSeparationPin — V-9: the charge–mass separation pin (lane grade)

**Commission.** Zero, 2026-11-17 10:52 EST: "Fire the separation
pin (V-9)" — V-9 of the electrogravitic investigation
(`~/workspace/your_files/electrogravitic-investigation-2026-11-17.md`,
verdict table + Source 3 audit, which govern the statement shapes
below).

**What this pin proves — and what it does not.** This pin proves a
fact about **our own vocabulary**, inside our own seats: the charge
vocabulary (`teCharge` and its response form, `ThermoelectricSeat`)
and the mass vocabulary (the grounded Poisson channel,
`BoundarySeat`) never couple. It proves **nothing about nature,
capacitors, or gravity in the world.** NO CLAIM. **Dial 2 = 0**
before, during, and after, under every outcome. Lane grade only —
not integrated, not pushed. Any presentation of this pin as a
gravity result, Dial evidence, or a physical claim about charge
and gravity fires **K-TE-GRAV** / **K-UA2-LAUNDER** (standing) and
**K-OG-RL-SCOPE** (carried).

**The three parts, as scoped (V-9):**
- **(i)** The charge total vanishes identically, for every thermal
  field, in the linear and in every response form. Already landed
  at T1 (TE-T3 / TE-T6); §1 **cites** it, does not re-prove it.
- **(ii)** The grounded potential's source is a mass density: the
  channel detects constant shifts of the source — total-mass
  sensitivity (§3, cited from UA-2). The **teCharge-sourced
  variant fails the strip test at the source joint**: no two
  teCharge sources ever differ by a nonzero constant (§3, general
  countermodel), and at the named two-site seat the uniform unit
  density — total mass 2, the first mass datum of the finite
  Newtonian shadow — is not a teCharge source for any thermal
  field (§3, seat countermodel). Sourcing the potential from
  `teCharge` re-imposes total-mass blindness at the source joint,
  in **K-OG-SHADOW**'s shape — on the grounded channel itself.
  This is the finite form of V-4's grading (the variant was
  refused by Zero's Ruling 2, 2026-11-17: source = ρ).
- **(iii)** The vocabulary separation in stated form (§2): on the
  charge side, the charge sees contrasts only — a constant shift
  of the thermal field changes nothing; on the mass side, the
  grounded potential determines its source at every ungrounded
  site — the mass source is an independent datum, recoverable
  from the field, not a derived contrast of another field.

**Scope of (iii), on the face.** The named modules of the V-9
audit are: charge — `ThermoelectricSeat`, `StringChargeDensityPin`,
`SpinChargeStringPin`; mass — `NewtonSeatPin`, `CenterBridgePin`,
`BoundarySeat`. This pin's base (master `11c8a39`) carries exactly
`ThermoelectricSeat` and `BoundarySeat` — the two modules that
share the border this pin fences (the grounded channel is where a
charge source was proposed). (iii) is therefore stated over those
two. `StringChargeDensityPin`, `SpinChargeStringPin`, and
`CenterBridgePin` are lane-grade only at pin time and
`NewtonSeatPin` is still building in its own lane; their
separation audit stands in the investigation memo (Source 3) and
is **not** restated as Lean forms here.

**Kill armed: K-EG-SEP.** If the §3 countermodel had failed — if
a teCharge-sourced potential at the named seat passed the strip
test — the separation claim would narrow on this face and the
narrowing would be reported at full rank. Disposition recorded
at landing in `STATUS-EGSEP.md`.
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## §1 — Part (i): the charge total vanishes (citations of landed T1) -/

/-- **(i), linear form — citation of TE-T3.** The total separated
charge is identically zero, for every thermal field. This is
`teCharge_sum_eq_zero` (`ThermoelectricSeat`, T1), restated as
this pin's first clause: the charge is a conserved contrast, not
a substance — the fact the §3 countermodel spends. -/
theorem eg_charge_total_vanishes (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (θ : V → ℝ) :
    ∑ i, teCharge w θ i = 0 :=
  teCharge_sum_eq_zero w hw θ

/-- **(i), response form — citation of TE-T6's sum law.** For
every response function `ψ`, the total response charge is also
identically zero: no response form of the charge escapes the
conservation. `teChargeResp_sum_eq_zero` (`ThermoelectricSeat`,
T1). -/
theorem eg_chargeResp_total_vanishes (ψ : ℝ → ℝ) (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (θ : V → ℝ) :
    ∑ i, teChargeResp ψ w θ i = 0 :=
  teChargeResp_sum_eq_zero ψ w hw θ

/-! ## §2 — Part (iii): the vocabulary separation, in stated form -/

/-- **(iii), charge side.** The separated charge sees contrasts
only: shifting the thermal field by a constant — changing its
level, the one datum a mass-like reading would need — changes
the charge **nowhere**. The charge vocabulary contains no level
datum; `teCharge w θ` is a function of the field's differences
alone. -/
theorem eg_teCharge_add_const (w : V → V → ℝ) (θ : V → ℝ)
    (c : ℝ) :
    teCharge w (fun k => θ k + c) = teCharge w θ := by
  funext i
  rw [teCharge_apply, teCharge_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (θ i + c) - (θ j + c) = θ i - θ j by ring]

/-- **(iii), mass side — citation of UA-2's source recovery.**
The grounded potential determines its source at every ungrounded
site: two sources with the same grounded potential agree wherever
the equation is imposed. The mass source is an **independent
datum**, recoverable from the field — the opposite of a derived
contrast. `interior_eq_of_groundedPotential_eq`
(`BoundarySeat`, T1). -/
theorem eg_grounded_source_recovered (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (g g' : V → ℝ)
    (h : groundedPotential w hw hw0 hpos b g
       = groundedPotential w hw hw0 hpos b g')
    {i : V} (hi : i ≠ b) : g i = g' i :=
  interior_eq_of_groundedPotential_eq w hw hw0 hpos b g g' h hi

/-! ## §3 — Part (ii): the source is a mass density; the
teCharge-sourced variant fails the strip test -/

/-- **(ii), the mass side detects its total — citation of
UA-2.** The grounded channel is total-mass sensitive: some
quantity of the grounded field responds to a constant shift
of the source. A source for this channel therefore carries a
level datum — a total — that a charge source, by (i), can
never supply. `exists_groundedField_detects_totalMass`
(`BoundarySeat`, T1). -/
theorem eg_grounded_detects_totalMass (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V)
    (hi : ∃ i, i ≠ b) :
    ∃ (F : (V → V → ℝ) → ℝ) (g : V → ℝ) (c : ℝ), c ≠ 0 ∧
      F (groundedField w hw hw0 hpos b (fun j => g j + c))
        ≠ F (groundedField w hw hw0 hpos b g) :=
  exists_groundedField_detects_totalMass w hw hw0 hpos b hi

/-- **(ii), general countermodel — the strip test fails at
the source joint.** No two teCharge sources ever differ by a
nonzero constant: were `teCharge w θ'` the constant shift of
`teCharge w θ` by `c ≠ 0`, summing over the seat would force
`0 = card V • c ≠ 0`, since both charge totals vanish by (i).
So a teCharge source can never present the grounded channel
with the constant-shifted source the channel provably detects
(§3, citation above): sourcing the potential from `teCharge`
re-imposes total-mass blindness at the source joint —
**K-OG-SHADOW**'s shape, on the grounded channel itself.
This is the finite countermodel behind V-4's grading. -/
theorem eg_teCharge_no_const_shift (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (θ θ' : V → ℝ) (c : ℝ)
    (hc : c ≠ 0) :
    ¬ (∀ i, teCharge w θ' i = teCharge w θ i + c) := by
  intro h
  have hsum : (∑ i, teCharge w θ' i) = ∑ i, (teCharge w θ i + c) :=
    Finset.sum_congr rfl fun i _ => h i
  rw [teCharge_sum_eq_zero w hw θ', Finset.sum_add_distrib,
    teCharge_sum_eq_zero w hw θ] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    zero_add] at hsum
  have hcard : (Fintype.card V : ℝ) ≠ 0 := by
    have hpos : 0 < Fintype.card V :=
      Fintype.card_pos_iff.mpr inferInstance
    exact_mod_cast ne_of_gt hpos
  rcases mul_eq_zero.mp hsum.symm with h0 | h0
  · exact hcard h0
  · exact hc h0

/-- **(ii), seat countermodel at the named seat.** At the
two-site seat, the uniform unit density — total mass 2, the
first mass datum of the finite Newtonian shadow — is not a
teCharge source for **any** thermal field: its total is 2,
and every charge total is 0 by (i). The teCharge-sourced
variant therefore cannot even state the uniform source at
the smallest seat where a mass datum exists. -/
theorem eg_unit_density_not_teCharge (w : Fin 2 → Fin 2 → ℝ)
    (hw : ∀ i j, w i j = w j i) (θ : Fin 2 → ℝ) :
    teCharge w θ ≠ fun _ => (1 : ℝ) := by
  intro h
  have hsum := teCharge_sum_eq_zero w hw θ
  rw [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hsum
  norm_num at hsum

end ThetLogos
