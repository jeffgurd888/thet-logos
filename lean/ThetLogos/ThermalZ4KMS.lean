import ThetLogos.ThermalZ4Ladder
import ThetLogos.KMSBridge

namespace ThetLogos

/-!
# ThetLogos.ThermalZ4KMS — the ladder seat (Tiers T1/T2)

The 4-state Gibbs ladder of `ThetLogos.ThermalZ4Ladder` seated inside the
corpus's owned finite KMS machinery of `ThetLogos.KMSBridge`.

## The seat is the full algebra

The seat is `M₄(ℂ)`, the FULL 4×4 complex matrix algebra. The state and
the generator are diagonal in the ladder basis, but `KMSCondition`'s
quantifiers range over ALL matrix pairs `A B : Matrix (Fin 4) (Fin 4) ℂ`,
off-diagonals included: the observable algebra is noncommutative (matrix
units `E_{ij}`, `i ≠ j`, exist), so the KMS identity is demanded of pairs
that do not commute. This is the corpus's non-vacuous KMS form. It stands
in exact contrast to the dropped file's `KMSState` structure — refused,
audit-certified as vacuous (satisfiable for every automorphism group and
every normalized linear functional at every `β ≠ 0`) — which is named here
only as the anti-pattern. The dropped structures are not imported, not
reproduced, and not built on. Seating this brick on the diagonal
subalgebra instead (quantifiers restricted to diagonal matrices, where
every factor commutes) would re-enact that anti-pattern in miniature and
is expressly rejected.

## Convention, pinned on the face

`KMSBridge`'s `gibbsWeight` carries `β` as a separate scalar
(`exp (-β • K)`), so the ladder's `/4` lives INSIDE the generator
`z4Generator` below, and the state's `β` is the ladder's own `β`. The
rival pairing (generator `diagonal k`, temperature `β / 4`) is a different
statement about a different (state, generator) pair; it is NOT this one.
The partition identity `z4_gibbsZ_eq` is the checkpoint where the two
modules' normalizations must agree numeral-for-numeral.

## What is content and what is transport

Headline 1, `z4_gibbsState_eq`, is this brick's claim to content: the
ladder's scalar weight function IS the Gibbs state of the named generator
`z4Generator`, proved as a matrix identity over the full algebra.

Headline 2, `z4_ladder_kms`, is a SPECIALIZATION of the owned general
theorem `gibbs_kms` (proved in `KMSBridge` for an arbitrary generator),
transported along Headline 1. It is labeled a specialization on its face;
the KMS identity is not re-proved here.

## Falsifiability

The identification dies under a wrong generator, by computation. With
`diagonal (fun k => ((k.val : ℝ)^2 / 4 : ℂ))` in place of `z4Generator`,
the two agree at sites 0 and 1 but differ at sites 2 and 3 (the Gibbs
weight at site 2 would be `exp (-β)` where the ladder has `exp (-β / 2)`),
so the identification is false for that generator. With
`diagonal (fun k => (k.val : ℂ))` — the `/4` dropped — the weights are
`exp (-β * k)`, wrong at every site for `β ≠ 0`. The statement pins the
generator down to the ladder's exact declared input.

## Fences

No bearing is claimed on W1/W2 or G1/G2 beyond the scoping's §3, which is
KMS-1's territory, not this brick's. NO CLAIM. Dials 0/4. This is a finite
definition-and-identity brick: a generator, a partition identity, a state
identification, and one transported KMS specialization. Nothing further
is asserted.
-/

/-- The ladder generator H₄ on `M₄(ℂ)`: the ladder's declared input
    energies `E_k = k / 4` on the diagonal. Tier T2.

    CONVENTION PINNED: `gibbsWeight` carries `β` as a separate scalar, so
    the `/4` lives INSIDE this generator; the rival pairing
    (`diagonal k`, `β / 4`) is a different statement and is not this one. -/
noncomputable def z4Generator : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal (fun k : Fin 4 => ((k.val : ℝ) / 4 : ℂ))

/-- The ladder's energy at `k`, in the generator's `k.val` form:
    `z4Energy k = k.val / 4`. Tier T1. -/
theorem z4Energy_eq (k : Fin 4) : z4Energy k = (k.val : ℝ) / 4 := by
  unfold z4Energy
  congr 1

/-- The unnormalized Gibbs weight of the ladder generator is the diagonal
    of the ladder's unnormalized real weights. Tier T1. -/
theorem gibbsWeight_z4Generator (β : ℝ) :
    gibbsWeight z4Generator β
      = Matrix.diagonal (fun k : Fin 4 => ((Real.exp (-β * z4Energy k) : ℝ) : ℂ)) := by
  unfold gibbsWeight z4Generator
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext k
  simp only [Pi.smul_apply, Pi.coe_exp, smul_eq_mul]
  rw [z4Energy_eq]
  have hcast : (-(β : ℂ)) * (((k.val : ℝ) / 4 : ℂ))
      = ((-β * ((k.val : ℝ) / 4) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, ← congr_fun Complex.exp_eq_exp_ℂ _, ← Complex.ofReal_exp]

/-- Partition identity (the K-Z4K-1 checkpoint): the Gibbs partition
    function of `z4Generator` is exactly the complex cast of the ladder's
    real partition sum — the two modules' normalizations agree
    numeral-for-numeral. Tier T1. -/
theorem z4_gibbsZ_eq (β : ℝ) :
    gibbsZ z4Generator β = ((z4Partition β : ℝ) : ℂ) := by
  unfold gibbsZ z4Partition
  rw [gibbsWeight_z4Generator, Matrix.trace_diagonal, Complex.ofReal_sum]

/-- Headline 1 — the identification (this brick's content): the Gibbs
    state of `z4Generator` at the ladder's own `β` IS the ladder's scalar
    weight function, as a diagonal matrix over the full algebra `M₄(ℂ)`.
    Tier T1. -/
theorem z4_gibbsState_eq (β : ℝ) :
    gibbsState z4Generator β
      = Matrix.diagonal (fun k : Fin 4 => ((z4Weight β k : ℝ) : ℂ)) := by
  unfold gibbsState
  rw [gibbsWeight_z4Generator, z4_gibbsZ_eq, ← Matrix.diagonal_smul]
  congr 1
  funext k
  simp only [Pi.smul_apply, smul_eq_mul]
  unfold z4Weight
  rw [Complex.ofReal_div, div_eq_mul_inv, mul_comm]

/-- Headline 2 — KMS at the seat, BY TRANSPORT: a SPECIALIZATION of the
    owned general theorem `gibbs_kms`, rewritten along Headline 1. The
    KMS identity is not re-proved here; the quantifiers of `KMSCondition`
    range over all pairs of `M₄(ℂ)` matrices, off-diagonals included.
    Tier T1 (transport). -/
theorem z4_ladder_kms (β : ℝ) :
    KMSCondition (Matrix.diagonal (fun k : Fin 4 => ((z4Weight β k : ℝ) : ℂ)))
      z4Generator β :=
  z4_gibbsState_eq β ▸ gibbs_kms z4Generator β

end ThetLogos
