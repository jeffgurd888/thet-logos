import Mathlib.Tactic
import ThetLogos.DialOneSeatTiePin
import ThetLogos.HyperchargeForcing

open Matrix Complex
open ThetLogos.Track1RouteB
open ThetLogos.PreOptionARepresentation
open ThetLogos.DialOneSeatTiePin

namespace ThetLogos.DialOneSeatTieChecks

/-!
# ThetLogos.DialOneSeatTieChecks — D1-A′ stage 2: the PRE-CHECK GATE

Governing: pack `routeb-general-scratch/pack-d1a-checks.md`;
the pin `ThetLogos.DialOneSeatTiePin` (`DialOneBase`, `SeatTie`,
`DialOneStrengthened`, `DialOneForcing`, the COMMON HYPERCHARGE
MATRIX) over `ThetLogos.HyperchargeForcing` (cited by name;
neither edited). `DialOneForcing` itself is NOT attempted here.

## Registered outcome names (both branches, registered up front)

* Pre-check (i), `SeatTie pi1`:
  - holds: `seatTie_pi1_holds`
  - refuted: `seatTie_pi1_refuted` — **K-D1A′-3** (does not fire;
    see the verdict below).
* Pre-check (ii), `SeatTie piFlip`:
  - refuted (both pre-checks pass): `seatTie_piFlip_refuted`
    (does not fire; see the verdict below).
  - holds (gauntlet stops): `seatTie_piFlip_holds`, with
    `dialOneStrengthened_piFlip`,
    `piFlip_forcing_conclusion_fails`,
    `kD1A1_fires_by_piFlip` (**K-D1A′-1 FIRES by piFlip at the
    strengthened set**) and `kD1A2_vacuity_reading`
    (**K-D1A′-2 vacuity reading**: the tie is satisfied by
    EVERY `π`, so it constrains nothing).

## GATE VERDICT (proved below, at full rank)

The pin builder's flag is CONFIRMED, in the strongest form:
for every matrix `M` and every seat `s`, the lifted diagonal
`(M * piOp M) s s` equals its partner reindexing
`(M * piOp M) (partner s) (partner s)` — the two sums are the
same sum under the involution `k ↦ partner k`
(`lifted_diag_partner`). Hence `SeatTie π` holds for EVERY
`π` (`seatTie_universal`), by a **π-independent
partner-reindexing symmetry** — it uses no specifics of `π₁`
and no specifics of `piFlip`.

* (i) `SeatTie pi1` HOLDS (`seatTie_pi1_holds`), by that
  π-independent symmetry. K-D1A′-3 does NOT fire.
* (ii) `SeatTie piFlip` also HOLDS (`seatTie_piFlip_holds`).
  The pre-check gate therefore does NOT pass: the tie excludes
  nothing, in particular not the landed counterexample.
  Since `piFlip` also satisfies the landed base set
  (`dialOneBase_piFlip`, assembled from
  `ThetLogos.HyperchargeForcing`'s landed piFlip theorems),
  `DialOneStrengthened piFlip` holds, while the
  `DialOneForcing` conclusion fails for `piFlip` at its
  unimodular direction `(-2, 1)`, seat `ν_R`: the lifted
  eigenvalue there is `-1` at `t = π / 4`, against
  `exp (κ * t * 0 * I) = 1` forced by the COMMON HYPERCHARGE
  MATRIX entry `0` at `ν_R`. Hence **K-D1A′-1 FIRES by piFlip
  at the strengthened set** (`kD1A1_fires_by_piFlip`:
  `¬ DialOneForcing`), and the **K-D1A′-2 vacuity reading** is
  recorded alongside (`kD1A2_vacuity_reading`): a tie every
  `π` satisfies constrains nothing — it is, over any base set,
  equivalent to no condition at all on `π`, in particular it
  fixes no seat's weight. The tie is NOT re-posed here
  (re-posing is a coordinator/Jeff decision).

**NO CLAIM. Dial 1 = 0; all dials 0/4. Pre-checks are not a
derivation: parts of any official statement closed by this
module: 0.**
-/

/-- **The partner-reindexing symmetry** (the mechanism of the
whole gate): for every matrix `M` and seat `s`, the lifted
diagonal at `s` equals the lifted diagonal at `partner s`.
Proof: both sides are the sum `∑ k, M s k * M (partner s)
(partner k)` up to reindexing the second sum by the involution
`partner` and commuting each product. No hypothesis on `M`. -/
theorem lifted_diag_partner (M : Matrix I32 I32 ℂ) (s : I32) :
    (M * piOp M) s s = (M * piOp M) (partner s) (partner s) := by
  have hinv : Function.Involutive partner :=
    fun i => partner_involutive i
  have hcomp : (∑ k : I32, M (partner s) (partner k)
        * M s (partner (partner k)))
      = ∑ k : I32, M (partner s) k * M s (partner k) := by
    have h := Equiv.sum_comp (hinv.toPerm partner)
      (fun k => M (partner s) k * M s (partner k))
    simpa only [Function.Involutive.coe_toPerm] using h
  simp only [Matrix.mul_apply, piOp_apply, partner_involutive]
  rw [← hcomp]
  apply Finset.sum_congr rfl
  intro k _
  rw [partner_involutive]
  exact mul_comm _ _

/-- **The tie is universal (the K-D1A′-2 vacuity content)**:
`SeatTie π` holds for every representation `π`, every
direction `(α, β)`, every `t`, every seat — by
`lifted_diag_partner` alone. -/
theorem seatTie_universal (π : AF → Matrix (Fin 32) (Fin 32) ℂ) :
    SeatTie π :=
  fun α β t f c => lifted_diag_partner _ _

/-- **Pre-check (i): `SeatTie pi1` HOLDS.** The proof is the
π-independent partner-reindexing symmetry
(`lifted_diag_partner`, via `seatTie_universal`); it uses NO
specifics of `π₁`. K-D1A′-3 does not fire. -/
theorem seatTie_pi1_holds : SeatTie pi1 :=
  seatTie_universal pi1

/-- **Pre-check (ii): `SeatTie piFlip` HOLDS** — by the same
π-independent partner-reindexing symmetry. The refutation
branch (`seatTie_piFlip_refuted`, both pre-checks pass) does
NOT fire; the gauntlet stops here. -/
theorem seatTie_piFlip_holds :
    SeatTie ThetLogos.HyperchargeForcing.piFlip :=
  seatTie_universal _

/-- **`piFlip` satisfies the landed base set** `DialOneBase`,
assembled clause by clause from the landed theorems of
`ThetLogos.HyperchargeForcing` (`piFlip_afMul`, `piFlip_afAdd`,
`piFlip_afStar`, `piFlip_one`, `piFlip_zero`,
`piFlip_injective`, `piFlip_grading_even`, `piFlip_order_zero`,
`piFlip_first_order`), with the primitive unimodular direction
`(-2, 1)` (`piFlip_unimodular_direction`). -/
theorem dialOneBase_piFlip :
    DialOneBase ThetLogos.HyperchargeForcing.piFlip :=
  ⟨ThetLogos.HyperchargeForcing.piFlip_afMul,
   ThetLogos.HyperchargeForcing.piFlip_afAdd,
   ThetLogos.HyperchargeForcing.piFlip_afStar,
   ThetLogos.HyperchargeForcing.piFlip_one,
   ThetLogos.HyperchargeForcing.piFlip_zero,
   ThetLogos.HyperchargeForcing.piFlip_injective,
   ThetLogos.HyperchargeForcing.piFlip_grading_even,
   fun a b => ThetLogos.HyperchargeForcing.piFlip_order_zero a b,
   fun Ynu Ye Yu Yd a b i j =>
     ThetLogos.HyperchargeForcing.piFlip_first_order Ynu Ye Yu Yd a b i j,
   ⟨-2, 1, by norm_num,
     ThetLogos.HyperchargeForcing.piFlip_unimodular_direction⟩⟩

/-- **`piFlip` satisfies the STRENGTHENED set**: base ∧ tie. -/
theorem dialOneStrengthened_piFlip :
    DialOneStrengthened ThetLogos.HyperchargeForcing.piFlip :=
  ⟨dialOneBase_piFlip, seatTie_piFlip_holds⟩

/-- **The flipped ν_R lifted value**: along `piFlip`'s
unimodular direction `(-2, 1)` at `t = π / 4`, the lifted
eigenvalue at the `ν_R` seat (`fermionIndex nuR 0 = s8`) is
exactly `-1` — the value that kills the forcing conclusion,
since the COMMON HYPERCHARGE MATRIX entry at `ν_R` is `0`. -/
theorem piFlip_lifted_nuR_neg_one :
    (ThetLogos.HyperchargeForcing.piFlip (u1ParamGen (-2) 1 (Real.pi / 4))
        * piOp (ThetLogos.HyperchargeForcing.piFlip
            (u1ParamGen (-2) 1 (Real.pi / 4))))
        (fermionIndex SMFermion.nuR 0) (fermionIndex SMFermion.nuR 0)
      = -1 := by
  have hidx : fermionIndex SMFermion.nuR 0
      = ThetLogos.HyperchargeForcing.s8 := rfl
  rw [hidx, ThetLogos.HyperchargeForcing.piFlip_lifted_nuR]
  rw [← star_mul, ← Complex.exp_add]
  have he : (((-2 : ℤ) : ℂ) * (((Real.pi / 4 : ℝ) : ℂ) * Complex.I))
      + (((-2 : ℤ) : ℂ) * (((Real.pi / 4 : ℝ) : ℂ) * Complex.I))
      = -((Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- **The forcing conclusion fails for `piFlip`**: at the
unimodular direction `(-2, 1)` no scalar `κ` makes the lifted
sector weights proportional to the COMMON HYPERCHARGE MATRIX —
at `ν_R` the matrix entry is `0`, forcing the value `1`, while
`piFlip`'s lifted value is `-1`
(`piFlip_lifted_nuR_neg_one`). -/
theorem piFlip_forcing_conclusion_fails :
    ¬ ∀ (α β : ℤ),
      (∀ t, (ThetLogos.HyperchargeForcing.piFlip
          (u1ParamGen α β t)).det = 1) →
        ∃ κ : ℝ, ∀ (f : SMFermion) (t : ℝ),
          (ThetLogos.HyperchargeForcing.piFlip (u1ParamGen α β t)
              * piOp (ThetLogos.HyperchargeForcing.piFlip
                  (u1ParamGen α β t)))
              (fermionIndex f 0) (fermionIndex f 0)
            = Complex.exp (↑(κ * t)
                * commonHyperchargeMatrix (fermionIndex f 0)
                    (fermionIndex f 0)
                * Complex.I) := by
  intro h
  obtain ⟨κ, hκ⟩ := h (-2) 1
    ThetLogos.HyperchargeForcing.piFlip_unimodular_direction
  have h := hκ SMFermion.nuR (Real.pi / 4)
  have hc : commonHyperchargeMatrix (fermionIndex SMFermion.nuR 0)
      (fermionIndex SMFermion.nuR 0) = 0 := by
    rw [commonHyperchargeMatrix_diag]
    norm_num [hypercharge]
  rw [hc] at h
  simp only [mul_zero, zero_mul, Complex.exp_zero] at h
  rw [piFlip_lifted_nuR_neg_one] at h
  exact absurd h (by norm_num)

/-- **K-D1A′-1 FIRES by piFlip at the strengthened set**:
`piFlip` satisfies `DialOneStrengthened` (base ∧ tie) and its
weights are not proportional to the COMMON HYPERCHARGE
MATRIX, so the pinned forcing statement `DialOneForcing` is
FALSE. D1-A′ dies at the strengthened set, permanently, in
exactly the pre-registered K-D1A′-1 form. -/
theorem kD1A1_fires_by_piFlip : ¬ DialOneForcing := by
  intro hF
  exact piFlip_forcing_conclusion_fails
    (hF _ dialOneStrengthened_piFlip)

/-- **K-D1A′-2 vacuity reading, landed**: the seat tie is
satisfied by EVERY `π` whatsoever (`seatTie_universal`) — it
is the partner-reindexing symmetry of the lifted diagonal,
not a condition. A tie every `π` satisfies constrains
nothing: over the base set it excludes no representation and
fixes no seat's weight. This is the framing-kill prong of
K-D1A′-2, recorded at full rank alongside K-D1A′-1; the tie
is not re-posed in this module. -/
theorem kD1A2_vacuity_reading :
    ∀ π : AF → Matrix (Fin 32) (Fin 32) ℂ, SeatTie π :=
  fun π => seatTie_universal π

#print axioms lifted_diag_partner
#print axioms seatTie_pi1_holds
#print axioms seatTie_piFlip_holds
#print axioms dialOneStrengthened_piFlip
#print axioms piFlip_forcing_conclusion_fails
#print axioms kD1A1_fires_by_piFlip
#print axioms kD1A2_vacuity_reading

end ThetLogos.DialOneSeatTieChecks
