import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ThetLogos

/-!
# ThetLogos.ThermalZ4Ladder — the 4-state Gibbs ladder (Tiers T1/T2)

A finite Gibbs weight system on the four states of `Fin 4`, built as raw
material for the Q7CR line's `C⁴` factor. Nothing beyond that raw-material
role is claimed here, in either direction: this module makes no claim
about the `C⁴` leg itself, and no claim about W1/W2 or G1/G2 in either
direction.

## The ladder is a chosen input

The energy ladder `E_k = k / 4` for `k : Fin 4` is a CHOSEN INPUT, declared
as `z4Energy`; it is not derived from any other corpus object. The Gibbs
weights at inverse temperature `β` are the normalized exponentials of
`-β * E_k`, with partition sum `z4Partition β`.

## The staircase does not close as a cycle

The weight function is a staircase that does not close as a cycle. Within
the ladder there are three equal step ratios: moving from one rung to the
next multiplies the weight by `exp (-β / 4)` (steps 0→1, 1→2, 2→3, stated
in `z4Weight_step_ratio` for a general `k : Fin 3`). The wrap step is
different: the weight at rung 0 against the weight at rung 3 carries the
ratio `exp (3 * β / 4)` (stated in `z4Weight_wrap_ratio`). The wrap is NOT
another `exp (-β / 4)` step; the staircase does not close as a cycle.

## Refusals, on the face

The structures named `InternalAlgebra`, `ModularAutomorphismGroup`, and
`KMSState` in the dropped file audited before this build are NOT built
here: as defined there they are content-free / vacuous (the audit found
`KMSState` in that dropped form satisfiable for every automorphism group
and every normalized linear functional at every `β ≠ 0`). Where KMS is
relevant, the corpus's owned finite KMS machinery is `ThetLogos.KMSBridge`,
cited by name; no dropped-file KMS structure is used or reproduced here.

## Fences

NO CLAIM. Dials 0/4. This is a finite definition-and-identity brick: the
partition sum is positive, the weights are positive, the weights sum to
one, and the two ratio identities above hold exactly as stated. Nothing
further is asserted.
-/

/-- The chosen energy ladder on `Fin 4`: `E_k = k / 4`. Tier T2.
    A CHOSEN INPUT, not derived. -/
noncomputable def z4Energy (k : Fin 4) : ℝ := (k : ℝ) / 4

/-- The partition sum of the 4-state ladder at inverse temperature `β`:
    `Z = ∑ k, exp (-β * E_k)`. Tier T2. -/
noncomputable def z4Partition (β : ℝ) : ℝ :=
  ∑ k : Fin 4, Real.exp (-β * z4Energy k)

/-- The normalized Gibbs weight of rung `k` at inverse temperature `β`:
    `exp (-β * E_k) / Z`. Tier T2. -/
noncomputable def z4Weight (β : ℝ) (k : Fin 4) : ℝ :=
  Real.exp (-β * z4Energy k) / z4Partition β

/-- The partition sum is strictly positive: a finite sum of exponentials
    over a nonempty index set. Tier T1. -/
theorem z4Partition_pos (β : ℝ) : 0 < z4Partition β := by
  unfold z4Partition
  apply Finset.sum_pos
  · intro k _
    exact Real.exp_pos _
  · exact ⟨0, Finset.mem_univ 0⟩

/-- Every ladder weight is strictly positive. Tier T1. -/
theorem z4Weight_pos (β : ℝ) (k : Fin 4) : 0 < z4Weight β k :=
  div_pos (Real.exp_pos _) (z4Partition_pos β)

/-- The ladder weights sum to one. Tier T1. -/
theorem z4Weight_sum_eq_one (β : ℝ) : ∑ k : Fin 4, z4Weight β k = 1 := by
  unfold z4Weight
  rw [← Finset.sum_div]
  exact div_self (z4Partition_pos β).ne'

/-- Within-ladder step ratio, stated for a general `k : Fin 3`, covering
    exactly the steps 0→1, 1→2, 2→3: the next rung's weight is the current
    rung's weight times `exp (-β / 4)`. Tier T1. -/
theorem z4Weight_step_ratio (β : ℝ) (k : Fin 3) :
    z4Weight β k.succ
      = z4Weight β (Fin.castSucc k) * Real.exp (-β / 4) := by
  have hE : z4Energy k.succ = z4Energy (Fin.castSucc k) + 1 / 4 := by
    unfold z4Energy
    rw [Fin.val_succ, Fin.val_castSucc]
    push_cast
    ring
  have hexp : Real.exp (-β * z4Energy k.succ)
      = Real.exp (-β * z4Energy (Fin.castSucc k)) * Real.exp (-β / 4) := by
    rw [hE]
    have hsum : -β * (z4Energy (Fin.castSucc k) + 1 / 4)
        = -β * z4Energy (Fin.castSucc k) + -β / 4 := by ring
    rw [hsum, Real.exp_add]
  unfold z4Weight
  rw [hexp]
  ring

/-- Wrap ratio: the weight at rung 0 against the weight at rung 3. The
    factor is `exp (3 * β / 4)`, NOT another `exp (-β / 4)` step; the
    staircase does not close as a cycle. Tier T1. -/
theorem z4Weight_wrap_ratio (β : ℝ) :
    z4Weight β 0 = z4Weight β 3 * Real.exp (3 * β / 4) := by
  have hE0 : z4Energy (0 : Fin 4) = 0 := by
    unfold z4Energy
    simp
  have hE3 : z4Energy (3 : Fin 4) = 3 / 4 := by
    unfold z4Energy
    simp
  have hprod : Real.exp (-β * z4Energy (3 : Fin 4)) * Real.exp (3 * β / 4)
      = Real.exp (-β * z4Energy (0 : Fin 4)) := by
    rw [← Real.exp_add, hE3, hE0]
    congr 1
    ring
  unfold z4Weight
  rw [div_mul_eq_mul_div, hprod]

end ThetLogos
