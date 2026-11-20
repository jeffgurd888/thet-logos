import Mathlib.Tactic
import ThetLogos.OGResponsePin
import ThetLogos.BoundarySeat

/-!
# GroundedDirichletPin — ICDT-1, the grounded Dirichlet identity

The one unconditional content brick of the ICDT line (scope:
`inertia-coupled-density-tension-scope-2026-11-19.md` §3, §4).
**Grade: T5. NO CLAIM. Pre-registered DIAL-INELIGIBLE — Dial 2
= 0 under every outcome. Dials 0/4.**

## The join, and why it is not owned

At the grounded (Dirichlet) seat — the seat where falls are
stated — the density↔tension join was verified UNOWNED at
scoping (2026-11-19) and re-verified at this lane's drafting
(2026-11-20, contents-level): `BoundarySeat.lean` carries the
inversion only (existence, uniqueness, the Poisson equation at
ungrounded sites, the ground pin); `OGResponsePin.lean` and
`OGResponse.lean` carry the datum, the action, stationarity,
the EL form, universality — no energy identity anywhere. The
owned `BridgeLaplacian.energy_identity` lives at the CLOSED
seat (the mean-zero inversion), a different seat with a
different potential; the grounded seat's Dirichlet identity is
exactly what it does not cover. FALL-1 owns descent on the
grounded potential and Fall Floor owns arrival; this brick is
an energy identity — disjoint menus, neither absorbed.

## The statement

For the grounded potential `φ` of a source `g` on weights `w`
(symmetric, nonnegative, positive off the diagonal), ground
`b`:

`∑ i, g i * φ i = (1/2) * ∑ i, ∑ j, w i j * (φ i - φ j)^2`

— the density's self-energy IS the field's Dirichlet tension,
at the seat where falls are stated. Proof route (the scope's):
the pairing `∑ i, φ i * laplacianOp w φ i` equals the
self-energy site by site (at ungrounded sites by the landed
Poisson equation `laplacianOp_groundedPotential`; at the
ground both sides vanish because `φ b = 0`), and the pairing
is half the Dirichlet form by the closed seat's owned
`energy_eq_half` — the one closed-seat ingredient, cited, at
the point where the two seats genuinely share mathematics
(the bilinear algebra of `laplacianOp`, not the inversion).

## The corollary's exact form — decided at drafting, disclosed

The scope's draft phrase for the nonnegativity corollary was
"≥ 0, = 0 only at ρ = 0". The seat's own mathematics narrows
the equality clause: a source supported ONLY at the ground
has `φ = 0` (the ground absorbs its total — the landed
inversion solves the equation at ungrounded sites only), so
its self-energy is `0` with `ρ ≠ 0`. The banked exact form is
therefore: **self-energy = 0 ↔ the source vanishes at every
ungrounded site.** The identity itself is exactly as scoped;
only the corollary's equality clause is narrowed, here, on
the record (scope §4 ICDT-1 licensed the decision: "the exact
form decided at drafting, disclosed").

## Fences

This identity is a theorem of the grounded seat. It is not a
"gravitational reading" of anything (G-READ is documentation
only; no reading is added and no wrapper minted), not a
gravity object, not a response law, not Dial evidence.
K-ICDT-DUP / K-ICDT-IMPORT / K-ICDT-COSTUME, K-DENSITY-GRAV,
K-OG-RL-AMEND (the datum and its potentials are cited, never
edited), K-IDENSITY-LAUNDER stand on the face.
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The pairing step.** The density's self-energy pairing
equals the potential's Laplacian pairing, site by site: at
ungrounded sites by the landed Poisson equation, at the
ground because the grounded potential vanishes there. This
is the grounded seat's own step — the closed seat has no
ground and no analogue. -/
theorem sum_source_mul_groundedPotential (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (g : V → ℝ) :
    (∑ i, g i * groundedPotential w hw hw0 hpos b g i)
      = ∑ i, groundedPotential w hw hw0 hpos b g i
          * laplacianOp w (groundedPotential w hw hw0 hpos b g) i := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = b
  · subst hi
    rw [groundedPotential_at_ground]
    ring
  · rw [laplacianOp_groundedPotential w hw hw0 hpos b g hi]
    ring

/-- **THE GROUNDED DIRICHLET IDENTITY.** A density's
self-energy is its field's Dirichlet tension, at the grounded
seat: `∑ i, g i * φ i = (1/2) ∑ i j, w i j (φ i − φ j)²` for
`φ` the grounded potential of `g`. The one unowned join of
the ICDT scope, proved from landed objects alone. -/
theorem groundedDirichlet_identity (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (g : V → ℝ) :
    (∑ i, g i * groundedPotential w hw hw0 hpos b g i)
      = (1 / 2) * ∑ i, ∑ j, w i j
          * (groundedPotential w hw hw0 hpos b g i
            - groundedPotential w hw hw0 hpos b g j) ^ 2 := by
  rw [sum_source_mul_groundedPotential w hw hw0 hpos b g,
    energy_eq_half w hw]

/-- **Nonnegativity.** The grounded Dirichlet self-energy of
any source is nonnegative — the tension of a density's field
is a sum of squares wearing conductances. -/
theorem groundedDirichlet_nonneg (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (g : V → ℝ) :
    0 ≤ ∑ i, g i * groundedPotential w hw hw0 hpos b g i := by
  rw [groundedDirichlet_identity w hw hw0 hpos b g]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (hw0 i j) (sq_nonneg _)

/-- **The exact vanishing form** (drafting decision, disclosed
in the header): the self-energy vanishes iff the source
vanishes at every UNGROUNDED site. A source carried only by
the ground is absorbed by it — `φ = 0`, tension `0`, source
nonzero at `b`. Forward: zero energy makes `φ` constant
(the closed seat's `eq_const_of_energy_eq_zero`), the ground
pin makes the constant `0`, and the Poisson equation then
reads `g i = 0` at every ungrounded site. Backward: such a
source's grounded potential is the zero function, by the
landed uniqueness. -/
theorem groundedDirichlet_eq_zero_iff (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (g : V → ℝ) :
    (∑ i, g i * groundedPotential w hw hw0 hpos b g i) = 0
      ↔ ∀ i ≠ b, g i = 0 := by
  constructor
  · intro h i hi
    have hE : (∑ i, groundedPotential w hw hw0 hpos b g i
        * laplacianOp w (groundedPotential w hw hw0 hpos b g) i)
        = 0 := by
      rw [← sum_source_mul_groundedPotential w hw hw0 hpos b g]
      exact h
    have hconst := eq_const_of_energy_eq_zero w hw hw0 hpos
      (groundedPotential w hw hw0 hpos b g) hE
    have h4 : groundedPotential w hw hw0 hpos b g
        = (fun _ => (0 : ℝ)) := by
      funext k
      have hk := hconst k b
      rw [groundedPotential_at_ground] at hk
      exact hk
    have h2 := laplacianOp_groundedPotential w hw hw0 hpos b g hi
    rw [h4] at h2
    have h5 : laplacianOp w (fun _ => (0 : ℝ)) i = 0 := by
      have hc := congrFun (laplacianOp_const w 0) i
      simpa using hc
    rw [h5] at h2
    exact h2.symm
  · intro h
    have hφ : groundedPotential w hw hw0 hpos b g = (fun _ => (0 : ℝ)) := by
      apply groundedPotential_unique w hw hw0 hpos b g
        (groundedPotential w hw hw0 hpos b g) (fun _ => (0 : ℝ))
      · exact groundedPotential_at_ground w hw hw0 hpos b g
      · rfl
      · intro i hi
        exact laplacianOp_groundedPotential w hw hw0 hpos b g hi
      · intro i hi
        have hc := congrFun (laplacianOp_const w (0 : ℝ)) i
        simp only [Pi.zero_apply] at hc
        rw [hc]
        exact (h i hi).symm
    rw [hφ]
    simp

/-- **Transport to the OG seat — the datum's own density.**
The datum's density self-energy is the Dirichlet tension of
its own potential: `∑ i, D.ρ i * ogPotential D i =
(1/2) ∑ i j, D.w i j (φ i − φ j)²`. `ogPotential` is the
landed grounded inversion of `D.ρ` read through its pinned
definition; nothing is re-proved. -/
theorem ogPotential_dirichlet_identity [Nonempty V] (D : OGResponseDatum V) :
    (∑ i, D.ρ i * ogPotential D i)
      = (1 / 2) * ∑ i, ∑ j, D.w i j
          * (ogPotential D i - ogPotential D j) ^ 2 :=
  groundedDirichlet_identity D.w D.w_symm D.w_nonneg D.w_pos D.b D.ρ

/-- **Transport to the OG seat — the second channel.** The
same identity for an arbitrary second field `σ` through
`ogChargePotential`: the charged apparatus's potential
carries the same tension identity. -/
theorem ogChargePotential_dirichlet_identity [Nonempty V] (D : OGResponseDatum V)
    (σ : V → ℝ) :
    (∑ i, σ i * ogChargePotential D σ i)
      = (1 / 2) * ∑ i, ∑ j, D.w i j
          * (ogChargePotential D σ i - ogChargePotential D σ j) ^ 2 :=
  groundedDirichlet_identity D.w D.w_symm D.w_nonneg D.w_pos D.b σ

/-- **Nonnegativity at the OG seat.** The datum's density
self-energy — its field's grounded tension — is nonnegative. -/
theorem ogPotential_dirichlet_nonneg [Nonempty V] (D : OGResponseDatum V) :
    0 ≤ ∑ i, D.ρ i * ogPotential D i :=
  groundedDirichlet_nonneg D.w D.w_symm D.w_nonneg D.w_pos D.b D.ρ

end ThetLogos
