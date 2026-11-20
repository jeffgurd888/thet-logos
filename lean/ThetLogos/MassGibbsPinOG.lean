import Mathlib.Tactic
import ThetLogos.ModularVariance
import ThetLogos.OGResponse
import ThetLogos.MassGibbsPin

namespace ThetLogos

/-!
# ThetLogos.MassGibbsPinOG — Brick 2

**Commission / scope:** as Brick 1 (`MassGibbsPin.lean`); scope
`~/workspace/your_files/mass-gibbs-pin-scope-2026-11-18.md`, §3 MG-4.

## Face declarations

- Same fences as Brick 1: NO CLAIM, T5, dial-ineligible, dials 0/4.
- **Sequencing / dependency disclosure:** this brick imports
  `OGResponse` (OG-RL, landed at lane grade 2026-11-17 in the ogrl
  worktree, tip 3a8dd2e). In this lane the two OG modules
  (`OGResponse`, `OGResponsePin`) are transplanted lane-locally,
  byte-identical to the ogrl blobs; every shared dependency in
  their import closure is byte-identical between ogrl and the main
  tree. MassGibbs therefore integrates only with or after
  OGResponse (the T9 bank). It never ships as an unproved
  statement.
- `og_universality` (OG-RL) is CITED as the variational face of the
  single-scalar fact, not re-proved. The shared engine is
  `ogAction_scaling`; this brick is its Gibbs face.

## Contents (2 declarations)

- `ogAction_mass_smul` — the bridge lemma: the frozen action at
  body `B` is `B.m` times the frozen action at the unit body,
  pointwise in the path.
- `gibbsProb_ogAction_mass` — **MG-4**: the Gibbs state of the OG
  action at body `B` and cold `β` is the Gibbs state of the
  unit-body action at cold `β * B.m`. At the level of states,
  rescaling the body's mass is the same move as rescaling the cold.
-/

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- **Bridge lemma** (Tier T1 — proved at build): the frozen OG
action at body `B` is the scalar multiple by `B.m` of the action
at the unit body `⟨1, one_pos⟩`, at every path. From
`ogAction_scaling` at `t := B.m` over the unit body; the body
`⟨B.m * 1, _⟩` appearing there is `B` itself, since an `OGBody`
is determined by its mass (its only other field is the positivity
proof, and proofs are irrelevant). -/
theorem ogAction_mass_smul (D : OGResponseDatum V) (B : OGBody V)
    (n : ℕ) (x : Fin (n + 1) → V) :
    ogAction D B n x = B.m * ogAction D ⟨1, one_pos⟩ n x := by
  have h := ogAction_scaling D ⟨1, one_pos⟩ B.hm n x
  -- `h : ogAction D ⟨B.m * 1, _⟩ n x = B.m * ogAction D ⟨1, _⟩ n x`
  -- and `⟨B.m * 1, _⟩ = B` by mass-determination of `OGBody`.
  obtain ⟨mB, hmB⟩ := B
  simpa using h

/-- **MG-4 — the Gibbs face of mass-blindness** (Tier T1 — proved
at build): over the finite path type, the Gibbs state whose energy
is the frozen OG action at body `B`, read at cold `β`, equals the
Gibbs state of the unit-body action read at cold `β * B.m`. The
bridge lemma puts the action in `massEnergy` form
(`ogAction D B n = massEnergy (ogAction D ⟨1, one_pos⟩ n) B.m` by
`funext`), and Brick 1's MG-1 closes. Companion to
`og_universality` — the same single scalar, seen by the state
instead of by stationarity. -/
theorem gibbsProb_ogAction_mass (D : OGResponseDatum V)
    (B : OGBody V) (n : ℕ) (β : ℝ) (x : Fin (n + 1) → V) :
    ModularVariance.gibbsProb (ogAction D B n) β x =
      ModularVariance.gibbsProb (ogAction D ⟨1, one_pos⟩ n)
        (β * B.m) x := by
  have hE : ogAction D B n =
      massEnergy (ogAction D ⟨1, one_pos⟩ n) B.m := by
    funext y
    exact ogAction_mass_smul D B n y
  rw [hE]
  exact gibbsProb_massEnergy _ _ _ _

end ThetLogos
