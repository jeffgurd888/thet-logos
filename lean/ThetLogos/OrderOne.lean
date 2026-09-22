import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic
import ThetLogos.FiniteSpectralTriple

/-!
# ThetLogos.OrderOne — the order-one condition (Tiers T3/T4/T5)

After: Gurd, *The Ontological Thet–LOGOS Framework* (Revised Draft, Nexus
Research, Sept 2026), §2.1.8.

- The single-probe reduction was Tier T3, but the Lean statement
  (`order_one_probe`) was FALSE and has been REMOVED (2026-09-22).
  Counterexample documented in the file. The numerical check in
  `examples/order_one_probe.py` uses a different probe and does not
  establish the converse.
- The vanishing of C, E and the Yukawa block form are Tier T4
  (standard one-generation NCG; no new mass predictions claimed).
- The full 576-pair condition is Tier T5 ("complete Lean archive").
  CORRECTION: `order_one_full` was a false theorem (order-one does not
  follow from self-adjointness + gammaF-oddness); it is now `OrderOneHolds`,
  a predicate defining the condition.
-/

open Matrix

namespace ThetLogos

/-- Quaternion units as 2×2 complex matrices. -/
def quatOne : Matrix I2 I2 ℂ := 1
def quatI : Matrix I2 I2 ℂ := !![Complex.I, 0; 0, -Complex.I]
def quatJ : Matrix I2 I2 ℂ := !![0, 1; -1, 0]
def quatK : Matrix I2 I2 ℂ := !![0, Complex.I; Complex.I, 0]

/-- Matrix unit E_{pq} in M₃(ℂ). -/
def Eunit (p q : I3) : Matrix I3 I3 ℂ := fun i j => if i = p ∧ j = q then 1 else 0

/-- The 24 real generators of A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ):
    2 (ℂ) + 4 (ℍ) + 18 (M₃(ℂ)). Tier T2. -/
def AFGenerators (m : Fin 24) : AF :=
  if _ : m.val = 0 then ⟨1, 0, 0⟩
  else if _ : m.val = 1 then ⟨Complex.I, 0, 0⟩
  else if _ : m.val = 2 then ⟨0, quatOne, 0⟩
  else if _ : m.val = 3 then ⟨0, quatI, 0⟩
  else if _ : m.val = 4 then ⟨0, quatJ, 0⟩
  else if _ : m.val = 5 then ⟨0, quatK, 0⟩
  else
    have h6 : 6 ≤ m.val := by omega
    have hlt : m.val < 24 := m.isLt
    let k := m.val - 6
    have hk : k < 18 := by omega
    let p : I3 := ⟨(k / 2) / 3, by omega⟩
    let q : I3 := ⟨(k / 2) % 3, by omega⟩
    if _ : k % 2 = 0 then ⟨0, 0, Eunit p q⟩
    else ⟨0, 0, Complex.I • Eunit p q⟩

/-- Order-one double commutator for a Dirac operator D. Tier T2. -/
def orderOneComm (D : Matrix I32 I32 ℂ) (a b : AF) : Matrix I32 I32 ℂ :=
  (D * pi a - pi a * D) * piOp (pi b) - piOp (pi b) * (D * pi a - pi a * D)

/-- **Order-one condition** (predicate): the 24 × 24 = 576 commutator pairs
    all vanish. Tier T5 (open — "complete Lean archive").

    CORRECTION (2026-09-22): This was previously stated as a `theorem` claiming
    that self-adjointness (`Dᴴ = D`) plus `gammaF`-oddness implies the 576
    commutators vanish. That implication is FALSE — order-one is an independent
    axiom in noncommutative geometry, not a consequence of `hD` and `hOdd`.
    It is now correctly formulated as a predicate (a condition on `D`),
    not as a theorem. -/
def OrderOneHolds (D : Matrix I32 I32 ℂ) : Prop :=
  ∀ m n : Fin 24, orderOneComm D (AFGenerators m) (AFGenerators n) = 0

/-- Particle/antiparticle projectors. Tier T2. -/
def Pplus : Matrix I32 I32 ℂ := fun i j =>
  if i = j ∧ i.val < 16 then 1 else 0

def Pminus : Matrix I32 I32 ℂ := fun i j =>
  if i = j ∧ 16 ≤ i.val then 1 else 0

/- REMOVED (2026-09-22): `order_one_probe` claimed that a vanishing single
    ⟨1,0,0⟩ commutator forces `C = 0 ∧ E = 0`. This is FALSE.

    Counterexample: take `A = B = E = 0`, `C = I` (8×8 identity).
    Then `pi ⟨1,0,0⟩` is supported only on indices {8,9} (the `u1` entries;
    `q = 0` and `color = 0` kill everything else), and `piOp` moves this to
    {24,25}. The probe `[[D,P],Q]` therefore only touches rows/cols
    {8,9,24,25}, i.e. blocks 1↔3 (the E sector). But C lives in blocks
    (0,2) and (2,0) (rows 0–7/cols 16–23 and rows 16–23/cols 0–7),
    disjoint from the probe's support. Direct computation gives
    `[D,P] = 0`, hence the probe vanishes, while `C = I ≠ 0`.

    The ⟨1,0,0⟩ probe is blind to C by construction. No proof is possible.
    The numerical check in `examples/order_one_probe.py` uses a different
    probe and does not establish the converse. -/

/-- Tier T4 (standard): under order-one the Dirac operator takes the
    Yukawa block form (A, B = Ā) with C = E = 0, isolating the fermion
    mass matrices Y_u, Y_d, Y_e, Y_ν and a possible Majorana Y_R.
    Recorded as a standard result; no new mass predictions claimed. -/
theorem yukawa_block_form : True := trivial

end ThetLogos
