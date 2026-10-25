/-
# Descent and boundedness for `Π₂` (Stage 2, brick S2-2b)

Built 2026-10-24 under the REVISED S2-2 gate
(`whitepaper/stage2-s22-gate-revision-2026-10-24.md`, §3.5,
§5 brick S2-2b, priced M–L — the ladder's long pole). This
brick discharges the descent claims of the revised gate for
the factored pairings of `LatticeSlicePairing` (S2-2a):

* **(D-desc)ʳ** — `Π₂` vanishes on `Π₁`-null slice
  observables in each slot, under H-pos(1)ʳ; with the
  add-null corollaries, `Π₂` descends to the `Π₁`-quotient.
* **(D-bdd)ʳ** — the diagonal domination
  `Π₂(φ, φ) ≤ Π₁(φ, φ)` (as real parts), and the assembled
  bound `‖Π₂(φ, χ)‖ ≤ ‖[F_φ]‖_OS · ‖[F_χ]‖_OS`, the gate's
  stated form. Route: Cauchy–Schwarz for the one-step form
  plus contraction (`transferOp_norm_le`, the R1/S1 Markov
  package) — a bootstrap at `(v, Tv)`, no operator square
  roots, no spectral theory.
* **(D-symm)ʳ** — the descended pairing's Hermiticity,
  consumed from S2-2a's `slicePairTwo_conj_symm`.
* **(D-vac)ʳ** — `Π₂(χ, 1) = Π₁(χ, 1)`: the constant slice
  state's representative is the vacuum, and `transferOp`
  fixes it (`transferOp_vacuum`, R1's Markov content).

## Fences (on the face)

* **H-pos(1)ʳ remains a hypothesis.** It is named here as
  the predicate `SliceHPosOne`, in the gate's §3.4 form, and
  every headline that uses it carries it. It is NOT
  discharged in this brick (its discharge is S2-3's route
  (R-C2)ʳ, against Route C's class).
* **H-pos(2)ʳ, in the gate's factored form, is a theorem
  here** (`sliceHPosTwo_proved`): by S2-2a's stepped
  identity the two-step diagonal is `‖T (sliceState φ)‖²`,
  a norm square, at every real `β`. This is a statement
  about the factored pairing `Π₂` only; it asserts nothing
  about `osForm` on any other class, and no headline below
  needs H-pos(2)ʳ as a hypothesis.
* **The transport step is labeled.** The one place an
  all-vector statement appears is
  `inner_transferOp_self_re_nonneg_of_sliceHPosOne`: the
  form `⟪f, T f⟫` has nonnegative real part for every
  `f : osSpace`, proved by writing `f` as the slice state
  of its own representative (`sliceState` is `MemLp.toLp`;
  `MemLp.toLp_coeFn`). That is H-pos(1)ʳ transported along
  the corpus's own definition of `sliceState` — the same
  quantifier content, no positivity assumed beyond the
  named hypothesis. Every headline of the package is
  stated over slice observables, in the gate's forms.
* **`twoPointOp 2 = transferOp^2` is not consumed** — it is
  unlanded for `m ≥ 2`; `Π₂` is the iteration itself, as
  S2-2a defined it. No statement quantifies over
  `transferOp` on arbitrary `L²` vectors beyond the
  labeled transport lemma above (TM R2 fence).
* Bricks S2-2c (assembly) and S2-2d (regression suite)
  are out of scope.

NO CLAIM. Parts of any official Clay statement closed: 0.
Stage 1b-B label untouched (OPEN at general `(G, ρ)`;
U(1) T1 at all `β ≥ 0` on its support class).

This module is NOT in the root import list of the library
(the corpus pattern for recent exhibits); it is verified by
a targeted build.

- Status: brick S2-2b — built 2026-10-24 under the
  revised S2-2 gate; verdict STANDS (all four claims);
  parent-verified 2026-10-24 (targeted build exit 0,
  strict recount, axiom check). Dossier:
  `whitepaper/stage2-s22b-descent-2026-10-24.md`.
-/

import ThetLogos.LatticeSlicePairing

namespace ThetLogos

open MeasureTheory Finset
open scoped Matrix ENNReal NNReal InnerProduct

section DescentBoundedness

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
  [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [SecondCountableTopology G] {d : ℕ}
  (μG : Measure G) [IsProbabilityMeasure μG]
  [Measure.IsMulLeftInvariant μG] [Measure.IsMulRightInvariant μG]
  [Measure.IsInvInvariant μG]
  (ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ))
  {N : ℕ} [NeZero N]

/-! ## The hypotheses, in the gate's forms (§3.4) -/

/-- **H-pos(1)ʳ** (gate §3.4, Lean form): for every slice
observable `F_φ ∈ 𝔸_slice`, the one-step diagonal
`Π₁(φ, φ) = ⟪sliceState β φ, transferOp (sliceState β φ)⟫`
is a nonnegative real (stated, as throughout the corpus,
as nonnegativity of the real part — the diagonal is real
by Hermiticity). A named hypothesis of this brick; its
discharge is S2-3's, not this brick's. -/
def SliceHPosOne (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) : Prop :=
  ∀ (φ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β)),
    0 ≤ (slicePairOne μG ρ hN2 hρcont β φ hφ φ hφ).re

/-- **H-pos(2)ʳ** (gate §3.4, Lean form): for every slice
observable `F_φ ∈ 𝔸_slice`, the two-step diagonal
`Π₂(φ, φ)` is a nonnegative real. In this factored form
the statement is a THEOREM of this brick
(`sliceHPosTwo_proved`), because S2-2a's stepped identity
identifies the diagonal with a norm square. The predicate
is recorded so the package's bookkeeping matches the
gate's. -/
def SliceHPosTwo (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ) : Prop :=
  ∀ (φ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β)),
    0 ≤ (slicePairTwo μG ρ hN2 hρcont β φ hφ φ hφ).re

/-! ## §A. The one-step form on `osSpace`: transport,
Hermiticity, reality -/

/-- **The transport step (labeled, see the header).**
H-pos(1)ʳ, transported along `sliceState`'s definition:
every vector of `osSpace` is the slice state of its own
representative, so the one-step form's diagonal has
nonnegative real part at every vector. The hypothesis and
this conclusion have the same quantifier content in the
corpus's own terms; nothing is assumed beyond
H-pos(1)ʳ. -/
theorem inner_transferOp_self_re_nonneg_of_sliceHPosOne (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f : osSpace (N := N) μG ρ β) :
    0 ≤ (inner ℂ f (transferOp μG ρ hN2 hρcont β f)).re := by
  have hf : sliceState μG ρ β (⇑f) (Lp.memLp f) = f :=
    Lp.toLp_coeFn f _
  have h := hpos (⇑f) (Lp.memLp f)
  have h2 : slicePairOne μG ρ hN2 hρcont β (⇑f) (Lp.memLp f)
        (⇑f) (Lp.memLp f)
      = inner ℂ f (transferOp μG ρ hN2 hρcont β f) := by
    show inner ℂ (sliceState μG ρ β (⇑f) (Lp.memLp f))
        (transferOp μG ρ hN2 hρcont β
          (sliceState μG ρ β (⇑f) (Lp.memLp f)))
      = inner ℂ f (transferOp μG ρ hN2 hρcont β f)
    rw [hf]
  rwa [h2] at h

/-- **Hermiticity of the one-step form on `osSpace`:**
`⟪f, T g⟫ = conj ⟪g, T f⟫`, from `transferOp`'s landed
symmetry (`transferOp_inner_symm`). -/
theorem inner_transferOp_conj_symm (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (f g : osSpace (N := N) μG ρ β) :
    inner ℂ f (transferOp μG ρ hN2 hρcont β g)
      = (starRingEnd ℂ)
          (inner ℂ g (transferOp μG ρ hN2 hρcont β f)) := by
  calc inner ℂ f (transferOp μG ρ hN2 hρcont β g)
      = inner ℂ (transferOp μG ρ hN2 hρcont β f) g :=
        (transferOp_inner_symm μG ρ hN2 hρcont hN β f g).symm
    _ = (starRingEnd ℂ)
          (inner ℂ g (transferOp μG ρ hN2 hρcont β f)) :=
        (inner_conj_symm (transferOp μG ρ hN2 hρcont β f) g).symm

/-- **The one-step form's diagonal is real.** -/
theorem inner_transferOp_self_im (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (f : osSpace (N := N) μG ρ β) :
    (inner ℂ f (transferOp μG ρ hN2 hρcont β f)).im = 0 := by
  have h := inner_transferOp_conj_symm μG ρ hN2 hρcont hN β f f
  exact (Complex.conj_eq_iff_im).mp h.symm

/-- **The one-step form's diagonal is its real part, as a
complex number.** -/
theorem inner_transferOp_self_eq_ofReal_re (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (f : osSpace (N := N) μG ρ β) :
    inner ℂ f (transferOp μG ρ hN2 hρcont β f)
      = ((inner ℂ f (transferOp μG ρ hN2 hρcont β f)).re : ℂ) := by
  have him := inner_transferOp_self_im μG ρ hN2 hρcont hN β f
  exact Complex.ext rfl (by simpa using him)

/-! ## §B. Cauchy–Schwarz for the one-step form -/

/-- **Cauchy–Schwarz for the one-step form** (the brick's
core lemma): under H-pos(1)ʳ, for all vectors of
`osSpace`,
`‖⟪f, T g⟫‖² ≤ ⟪f, T f⟫.re · ⟪g, T g⟫.re`.
Proof: the discriminant argument — positivity of the
form's diagonal at `f + c • g` for every `c : ℂ`, with
`c` chosen against the second diagonal (the case split
is on whether that diagonal vanishes). Positivity at the
combined vector is the transported H-pos(1)ʳ of §A. -/
theorem inner_transferOp_cauchy_schwarz (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f g : osSpace (N := N) μG ρ β) :
    ‖inner ℂ f (transferOp μG ρ hN2 hρcont β g)‖ ^ 2
      ≤ (inner ℂ f (transferOp μG ρ hN2 hρcont β f)).re
        * (inner ℂ g (transferOp μG ρ hN2 hρcont β g)).re := by
  set A : ℝ := (inner ℂ f (transferOp μG ρ hN2 hρcont β f)).re
    with hAdef
  set C : ℝ := (inner ℂ g (transferOp μG ρ hN2 hρcont β g)).re
    with hCdef
  set z : ℂ := inner ℂ f (transferOp μG ρ hN2 hρcont β g) with hzdef
  have hA : 0 ≤ A := by
    have h := inner_transferOp_self_re_nonneg_of_sliceHPosOne
      μG ρ hN2 hρcont β hpos f
    rwa [← hAdef] at h
  have hC : 0 ≤ C := by
    have h := inner_transferOp_self_re_nonneg_of_sliceHPosOne
      μG ρ hN2 hρcont β hpos g
    rwa [← hCdef] at h
  have hff : inner ℂ f (transferOp μG ρ hN2 hρcont β f)
      = (A : ℂ) := by
    have h := inner_transferOp_self_eq_ofReal_re
      μG ρ hN2 hρcont hN β f
    rwa [← hAdef] at h
  have hgg : inner ℂ g (transferOp μG ρ hN2 hρcont β g)
      = (C : ℂ) := by
    have h := inner_transferOp_self_eq_ofReal_re
      μG ρ hN2 hρcont hN β g
    rwa [← hCdef] at h
  have hgf : inner ℂ g (transferOp μG ρ hN2 hρcont β f)
      = (starRingEnd ℂ) z := by
    have hsymm := inner_transferOp_conj_symm μG ρ hN2 hρcont hN β f g
    rw [← hzdef] at hsymm
    have h2 := congrArg (starRingEnd ℂ) hsymm
    rw [Complex.conj_conj] at h2
    exact h2.symm
  have hexp : ∀ c : ℂ,
      inner ℂ (f + c • g) (transferOp μG ρ hN2 hρcont β (f + c • g))
        = (A : ℂ) + c * z + (starRingEnd ℂ) c * (starRingEnd ℂ) z
          + ((starRingEnd ℂ) c * c) * (C : ℂ) := by
    intro c
    calc inner ℂ (f + c • g)
          (transferOp μG ρ hN2 hρcont β (f + c • g))
        = inner ℂ f (transferOp μG ρ hN2 hρcont β f)
          + c * inner ℂ f (transferOp μG ρ hN2 hρcont β g)
          + (starRingEnd ℂ) c
            * inner ℂ g (transferOp μG ρ hN2 hρcont β f)
          + ((starRingEnd ℂ) c * c)
            * inner ℂ g (transferOp μG ρ hN2 hρcont β g) := by
          simp only [map_add, map_smul, inner_add_left,
            inner_add_right, inner_smul_left, inner_smul_right]
          ring
      _ = (A : ℂ) + c * z + (starRingEnd ℂ) c * (starRingEnd ℂ) z
          + ((starRingEnd ℂ) c * c) * (C : ℂ) := by
          rw [hff, hgf, hgg, hzdef]
  have hquad : ∀ c : ℂ,
      0 ≤ ((A : ℂ) + c * z + (starRingEnd ℂ) c * (starRingEnd ℂ) z
        + ((starRingEnd ℂ) c * c) * (C : ℂ)).re := by
    intro c
    rw [← hexp c]
    exact inner_transferOp_self_re_nonneg_of_sliceHPosOne
      μG ρ hN2 hρcont β hpos _
  have hzz : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    have h := RCLike.conj_mul z
    rwa [← RCLike.ofReal_pow] at h
  have hzz' : z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    have h := RCLike.mul_conj z
    rwa [← RCLike.ofReal_pow] at h
  by_cases hC0 : C = 0
  · -- Second diagonal zero: the form is linear in `t` along
    -- `c = -t • conj z`, forcing `z = 0`.
    have key : ∀ t : ℝ, 0 ≤ A - 2 * t * ‖z‖ ^ 2 := by
      intro t
      have h := hquad (-(t : ℂ) * (starRingEnd ℂ) z)
      have e1 : (-(t : ℂ) * (starRingEnd ℂ) z) * z
          = -(((t * ‖z‖ ^ 2 : ℝ)) : ℂ) := by
        have hrw : (-(t : ℂ) * (starRingEnd ℂ) z) * z
            = -(t : ℂ) * ((starRingEnd ℂ) z * z) := by ring
        rw [hrw, hzz]; push_cast; ring
      have e2 : (starRingEnd ℂ) (-(t : ℂ) * (starRingEnd ℂ) z)
            * (starRingEnd ℂ) z
          = -(((t * ‖z‖ ^ 2 : ℝ)) : ℂ) := by
        have hc : (starRingEnd ℂ) (-(t : ℂ) * (starRingEnd ℂ) z)
            = -(t : ℂ) * z := by
          simp only [map_mul, map_neg, Complex.conj_conj,
            Complex.conj_ofReal]
        rw [hc]
        have hrw : (-(t : ℂ) * z) * (starRingEnd ℂ) z
            = -(t : ℂ) * (z * (starRingEnd ℂ) z) := by ring
        rw [hrw, hzz']; push_cast; ring
      have e3 : ((starRingEnd ℂ) (-(t : ℂ) * (starRingEnd ℂ) z)
            * (-(t : ℂ) * (starRingEnd ℂ) z)) * (C : ℂ) = 0 := by
        rw [hC0]; simp
      rw [e1, e2, e3] at h
      have hre : ((A : ℂ) + -(((t * ‖z‖ ^ 2 : ℝ)) : ℂ)
          + -(((t * ‖z‖ ^ 2 : ℝ)) : ℂ) + 0).re
          = A - 2 * t * ‖z‖ ^ 2 := by
        simp only [Complex.add_re, Complex.ofReal_re,
          Complex.neg_re, add_zero]
        ring
      rwa [hre] at h
    have hfin : ‖z‖ ^ 2 ≤ A * C := by
      rw [hC0, mul_zero]
      by_contra hcon
      push Not at hcon
      have ht := key ((A + 1) / (2 * ‖z‖ ^ 2))
      have hs0 : (2 * ‖z‖ ^ 2) ≠ 0 :=
        mul_ne_zero (by norm_num) (ne_of_gt hcon)
      have heq : 2 * ((A + 1) / (2 * ‖z‖ ^ 2)) * ‖z‖ ^ 2
          = A + 1 := by
        calc 2 * ((A + 1) / (2 * ‖z‖ ^ 2)) * ‖z‖ ^ 2
            = ((A + 1) / (2 * ‖z‖ ^ 2)) * (2 * ‖z‖ ^ 2) := by
              ring
          _ = A + 1 := div_mul_cancel₀ _ hs0
      rw [heq] at ht
      linarith
    exact hfin
  · -- Second diagonal positive: the discriminant choice
    -- `c = -conj z / C`.
    have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    have h := hquad (-(starRingEnd ℂ) z / (C : ℂ))
    have hcc : (starRingEnd ℂ) (-(starRingEnd ℂ) z / (C : ℂ))
        = -z / (C : ℂ) := by
      simp only [map_div₀, map_neg, Complex.conj_conj,
        Complex.conj_ofReal]
    have e1 : (-(starRingEnd ℂ) z / (C : ℂ)) * z
        = -(((‖z‖ ^ 2 / C : ℝ)) : ℂ) := by
      rw [div_mul_eq_mul_div, neg_mul, hzz, neg_div]
      push_cast
      ring
    have e2 : (starRingEnd ℂ) (-(starRingEnd ℂ) z / (C : ℂ))
          * (starRingEnd ℂ) z
        = -(((‖z‖ ^ 2 / C : ℝ)) : ℂ) := by
      rw [hcc, div_mul_eq_mul_div, neg_mul, hzz', neg_div]
      push_cast
      ring
    have e3 : ((starRingEnd ℂ) (-(starRingEnd ℂ) z / (C : ℂ))
          * (-(starRingEnd ℂ) z / (C : ℂ))) * (C : ℂ)
        = (((‖z‖ ^ 2 / C : ℝ)) : ℂ) := by
      have hcc : (starRingEnd ℂ) (-(starRingEnd ℂ) z / (C : ℂ))
            * (-(starRingEnd ℂ) z / (C : ℂ))
          = (((‖z‖ ^ 2 / C ^ 2 : ℝ)) : ℂ) := by
        rw [hcc, div_mul_div_comm, neg_mul_neg, hzz',
          ← Complex.ofReal_mul, ← Complex.ofReal_div, ← pow_two]
      rw [hcc, ← Complex.ofReal_mul]
      congr 1
      rw [show C ^ 2 = C * C from pow_two C, div_mul_eq_mul_div,
        mul_div_mul_right _ _ (ne_of_gt hCpos)]
    rw [e1, e2, e3] at h
    have hre : ((A : ℂ) + -(((‖z‖ ^ 2 / C : ℝ)) : ℂ)
        + -(((‖z‖ ^ 2 / C : ℝ)) : ℂ)
        + (((‖z‖ ^ 2 / C : ℝ)) : ℂ)).re
        = A - ‖z‖ ^ 2 / C := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.neg_re]
      ring
    rw [hre] at h
    have hle : ‖z‖ ^ 2 / C ≤ A := by linarith
    exact (div_le_iff₀ hCpos).mp hle

/-- **Cauchy–Schwarz for `Π₁`** (pairing form of §B):
under H-pos(1)ʳ,
`‖Π₁(φ, χ)‖² ≤ Π₁(φ, φ).re · Π₁(χ, χ).re`. -/
theorem slicePairOne_cauchy_schwarz (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β)) :
    ‖slicePairOne μG ρ hN2 hρcont β φ hφ χ hχ‖ ^ 2
      ≤ (slicePairOne μG ρ hN2 hρcont β φ hφ φ hφ).re
        * (slicePairOne μG ρ hN2 hρcont β χ hχ χ hχ).re :=
  inner_transferOp_cauchy_schwarz μG ρ hN2 hρcont hN β hpos
    (sliceState μG ρ β φ hφ) (sliceState μG ρ β χ hχ)

/-! ## §C. (D-desc)ʳ — descent of `Π₂` -/

/-- **(D-desc)ʳ, first slot:** under H-pos(1)ʳ, a
`Π₁`-null slice observable pairs to zero under `Π₂`
against every slice observable. Proof: `Π₂(φ, χ)` is the
one-step form at `(sliceState φ, T (sliceState χ))`, and
Cauchy–Schwarz (§B) bounds it by the vanishing first
diagonal. -/
theorem slicePairTwo_eq_zero_of_pairOne_self_eq_zero_left
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β))
    (hnull : slicePairOne μG ρ hN2 hρcont β φ hφ φ hφ = 0) :
    slicePairTwo μG ρ hN2 hρcont β φ hφ χ hχ = 0 := by
  have hCS := inner_transferOp_cauchy_schwarz μG ρ hN2 hρcont hN β
    hpos (sliceState μG ρ β φ hφ)
    (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ))
  have e1 : (inner ℂ (sliceState μG ρ β φ hφ)
      (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β φ hφ))).re
      = 0 := by
    have e : slicePairOne μG ρ hN2 hρcont β φ hφ φ hφ
        = inner ℂ (sliceState μG ρ β φ hφ)
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β φ hφ)) :=
      rfl
    rw [← e, hnull]
    exact Complex.zero_re
  rw [e1, zero_mul] at hCS
  have hnorm : ‖inner ℂ (sliceState μG ρ β φ hφ)
      (transferOp μG ρ hN2 hρcont β
        (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ)))‖
      = 0 := by
    by_contra hc
    have hpos' : 0 < ‖inner ℂ (sliceState μG ρ β φ hφ)
        (transferOp μG ρ hN2 hρcont β
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ)))‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hc)
    have hsq : 0 < ‖inner ℂ (sliceState μG ρ β φ hφ)
        (transferOp μG ρ hN2 hρcont β
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ)))‖
        ^ 2 := pow_pos hpos' 2
    linarith
  have e2 : slicePairTwo μG ρ hN2 hρcont β φ hφ χ hχ
      = inner ℂ (sliceState μG ρ β φ hφ)
        (transferOp μG ρ hN2 hρcont β
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ))) :=
    rfl
  rw [e2]
  exact norm_eq_zero.mp hnorm

/-- **(D-desc)ʳ, second slot:** under H-pos(1)ʳ, `Π₂`
vanishes whenever the second observable is `Π₁`-null —
the first-slot statement conjugated by `Π₂`'s
Hermiticity (S2-2a). -/
theorem slicePairTwo_eq_zero_of_pairOne_self_eq_zero_right
    (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β))
    (hnull : slicePairOne μG ρ hN2 hρcont β χ hχ χ hχ = 0) :
    slicePairTwo μG ρ hN2 hρcont β φ hφ χ hχ = 0 := by
  have h := slicePairTwo_eq_zero_of_pairOne_self_eq_zero_left
    μG ρ hN2 hρcont hN β hpos χ φ hχ hφ hnull
  have hc := slicePairTwo_conj_symm μG ρ hN2 hρcont hN β φ χ hφ hχ
  rw [h] at hc
  simpa using hc

/-- **(D-symm)ʳ for the descended pairing:** `Π₂`'s
Hermiticity, consumed verbatim from S2-2a
(`slicePairTwo_conj_symm`) — with (D-desc)ʳ landed above,
this is the symmetry of the pairing the quotient
inherits. -/
theorem slicePairTwo_conj_symm_descended (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β)) :
    slicePairTwo μG ρ hN2 hρcont β φ hφ χ hχ
      = (starRingEnd ℂ)
          (slicePairTwo μG ρ hN2 hρcont β χ hχ φ hφ) :=
  slicePairTwo_conj_symm μG ρ hN2 hρcont hN β φ χ hφ hχ

/-- **Descent, representative form (first slot):** adding
a `Π₁`-null observable to the first argument does not
change `Π₂` — the well-definedness of the descended
pairing on `Π₁`-classes, for S2-2c's assembly. -/
theorem slicePairTwo_add_left_of_null (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (φ φ₀ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hφ₀ : MemLp φ₀ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β))
    (hnull : slicePairOne μG ρ hN2 hρcont β φ₀ hφ₀ φ₀ hφ₀ = 0) :
    slicePairTwo μG ρ hN2 hρcont β (φ + φ₀) (hφ.add hφ₀) χ hχ
      = slicePairTwo μG ρ hN2 hρcont β φ hφ χ hχ := by
  rw [slicePairTwo_add_left μG ρ hN2 hρcont β φ φ₀ χ hφ hφ₀ hχ,
    slicePairTwo_eq_zero_of_pairOne_self_eq_zero_left
      μG ρ hN2 hρcont hN β hpos φ₀ χ hφ₀ hχ hnull,
    add_zero]

/-- **Descent, representative form (second slot).** -/
theorem slicePairTwo_add_right_of_null (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (φ χ χ₀ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ₀ : MemLp χ₀ 2 (sliceMeasure (N := N) μG ρ β))
    (hnull : slicePairOne μG ρ hN2 hρcont β χ₀ hχ₀ χ₀ hχ₀ = 0) :
    slicePairTwo μG ρ hN2 hρcont β φ hφ (χ + χ₀) (hχ.add hχ₀)
      = slicePairTwo μG ρ hN2 hρcont β φ hφ χ hχ := by
  rw [slicePairTwo_add_right μG ρ hN2 hρcont β φ χ χ₀ hφ hχ hχ₀,
    slicePairTwo_eq_zero_of_pairOne_self_eq_zero_right
      μG ρ hN2 hρcont hN β hpos φ χ₀ hφ hχ₀ hnull,
    add_zero]

/-! ## §D. `Π₂`'s diagonal: a norm square -/

/-- **H-pos(2)ʳ is a theorem in factored form** (see the
header): by S2-2a's stepped identity, `Π₂`'s diagonal is
`‖T (sliceState φ)‖² ≥ 0` at every real `β`. -/
theorem sliceHPosTwo_proved (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ) :
    SliceHPosTwo μG ρ hN2 hρcont β := by
  intro φ hφ
  rw [slicePairTwo_eq_inner_steps μG ρ hN2 hρcont hN β φ φ hφ hφ]
  exact inner_self_nonneg (𝕜 := ℂ)

/-- **Cauchy–Schwarz for `Π₂`** (immediate from the
stepped identity and the ambient Cauchy–Schwarz):
`‖Π₂(φ, χ)‖ ≤ √Π₂(φ, φ).re · √Π₂(χ, χ).re`. -/
theorem slicePairTwo_cauchy_schwarz (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β)) :
    ‖slicePairTwo μG ρ hN2 hρcont β φ hφ χ hχ‖
      ≤ Real.sqrt (slicePairTwo μG ρ hN2 hρcont β φ hφ φ hφ).re
        * Real.sqrt (slicePairTwo μG ρ hN2 hρcont β χ hχ χ hχ).re
    := by
  have hself : ∀ (ψ : (↥(sliceLinks (N := N)) → G) → ℂ)
      (hψ : MemLp ψ 2 (sliceMeasure (N := N) μG ρ β)),
      (slicePairTwo μG ρ hN2 hρcont β ψ hψ ψ hψ).re
        = ‖transferOp μG ρ hN2 hρcont β (sliceState μG ρ β ψ hψ)‖
          ^ 2 := by
    intro ψ hψ
    rw [slicePairTwo_eq_inner_steps μG ρ hN2 hρcont hN β ψ ψ hψ hψ]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [slicePairTwo_eq_inner_steps μG ρ hN2 hρcont hN β φ χ hφ hχ]
  calc ‖inner ℂ
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β φ hφ))
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ))‖
      ≤ ‖transferOp μG ρ hN2 hρcont β (sliceState μG ρ β φ hφ)‖
        * ‖transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ)‖ :=
        norm_inner_le_norm _ _
    _ = Real.sqrt (slicePairTwo μG ρ hN2 hρcont β φ hφ φ hφ).re
        * Real.sqrt (slicePairTwo μG ρ hN2 hρcont β χ hχ χ hχ).re
        := by
        rw [hself φ hφ, hself χ hχ,
          Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-! ## §E. (D-bdd)ʳ — domination and the bound -/

/-- **Contraction, applied form:** `‖T f‖ ≤ ‖f‖` at every
real `β`, from the landed `transferOp_norm_le`. -/
theorem norm_transferOp_apply_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g) (β : ℝ)
    (f : osSpace (N := N) μG ρ β) :
    ‖transferOp μG ρ hN2 hρcont β f‖ ≤ ‖f‖ := by
  calc ‖transferOp μG ρ hN2 hρcont β f‖
      ≤ ‖transferOp μG ρ hN2 hρcont β‖ * ‖f‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact transferOp_norm_le μG ρ hN2 hρcont β
    _ = ‖f‖ := one_mul _

/-- **The iterated form is the norm square of the step:**
`⟪f, T (T f)⟫ = ‖T f‖²` as a complex number (through
`transferOp`'s symmetry and the ambient
`⟪T f, T f⟫ = ‖T f‖²`). -/
theorem inner_transferOp_iter_eq (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (f : osSpace (N := N) μG ρ β) :
    inner ℂ f (transferOp μG ρ hN2 hρcont β
        (transferOp μG ρ hN2 hρcont β f))
      = ((‖transferOp μG ρ hN2 hρcont β f‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : inner ℂ f (transferOp μG ρ hN2 hρcont β
        (transferOp μG ρ hN2 hρcont β f))
      = inner ℂ (transferOp μG ρ hN2 hρcont β f)
          (transferOp μG ρ hN2 hρcont β f) :=
    (transferOp_inner_symm μG ρ hN2 hρcont hN β f
      (transferOp μG ρ hN2 hρcont β f)).symm
  rw [h1]
  apply Complex.ext
  · simp [inner_self_eq_norm_sq_to_K]
  · simp

/-- **The step estimate:** the one-step form's diagonal at
the stepped vector is dominated by the step's norm
square, `⟪T f, T (T f)⟫.re ≤ ‖T f‖²` — ambient
Cauchy–Schwarz against contraction. Positivity at the
stepped vector is the transported H-pos(1)ʳ (its diagonal
is real and nonnegative). -/
theorem inner_transferOp_step_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f : osSpace (N := N) μG ρ β) :
    (inner ℂ (transferOp μG ρ hN2 hρcont β f)
      (transferOp μG ρ hN2 hρcont β
        (transferOp μG ρ hN2 hρcont β f))).re
      ≤ ‖transferOp μG ρ hN2 hρcont β f‖ ^ 2 := by
  have hnn : 0 ≤ (inner ℂ (transferOp μG ρ hN2 hρcont β f)
      (transferOp μG ρ hN2 hρcont β
        (transferOp μG ρ hN2 hρcont β f))).re :=
    inner_transferOp_self_re_nonneg_of_sliceHPosOne
      μG ρ hN2 hρcont β hpos _
  have hre : inner ℂ (transferOp μG ρ hN2 hρcont β f)
        (transferOp μG ρ hN2 hρcont β
          (transferOp μG ρ hN2 hρcont β f))
      = ((inner ℂ (transferOp μG ρ hN2 hρcont β f)
          (transferOp μG ρ hN2 hρcont β
            (transferOp μG ρ hN2 hρcont β f))).re : ℂ) :=
    inner_transferOp_self_eq_ofReal_re μG ρ hN2 hρcont hN β _
  have hnorm_eq : ‖inner ℂ (transferOp μG ρ hN2 hρcont β f)
        (transferOp μG ρ hN2 hρcont β
          (transferOp μG ρ hN2 hρcont β f))‖
      = (inner ℂ (transferOp μG ρ hN2 hρcont β f)
          (transferOp μG ρ hN2 hρcont β
            (transferOp μG ρ hN2 hρcont β f))).re := by
    rw [hre, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs,
      abs_of_nonneg hnn]
  calc (inner ℂ (transferOp μG ρ hN2 hρcont β f)
        (transferOp μG ρ hN2 hρcont β
          (transferOp μG ρ hN2 hρcont β f))).re
      = ‖inner ℂ (transferOp μG ρ hN2 hρcont β f)
          (transferOp μG ρ hN2 hρcont β
            (transferOp μG ρ hN2 hρcont β f))‖ := hnorm_eq.symm
    _ ≤ ‖transferOp μG ρ hN2 hρcont β f‖
          * ‖transferOp μG ρ hN2 hρcont β
              (transferOp μG ρ hN2 hρcont β f)‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖transferOp μG ρ hN2 hρcont β f‖
          * ‖transferOp μG ρ hN2 hρcont β f‖ := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact norm_transferOp_apply_le μG ρ hN2 hρcont β _
    _ = ‖transferOp μG ρ hN2 hρcont β f‖ ^ 2 := (sq _).symm

/-- **(D-bdd)ʳ, diagonal domination, form form:** under
H-pos(1)ʳ, `⟪f, T (T f)⟫.re ≤ ⟪f, T f⟫.re` at every
vector of `osSpace` — in particular at slice states,
which is the pairing statement below. Bootstrap:
Cauchy–Schwarz (§B) at `(f, T f)` gives
`‖T f‖⁴ ≤ ⟪f, T f⟫.re · ⟪T f, T (T f)⟫.re`, and the step
estimate bounds the second factor by `‖T f‖²`. -/
theorem inner_transferOp_iter_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (f : osSpace (N := N) μG ρ β) :
    (inner ℂ f (transferOp μG ρ hN2 hρcont β
        (transferOp μG ρ hN2 hρcont β f))).re
      ≤ (inner ℂ f (transferOp μG ρ hN2 hρcont β f)).re := by
  have hA : 0 ≤ (inner ℂ f (transferOp μG ρ hN2 hρcont β f)).re :=
    inner_transferOp_self_re_nonneg_of_sliceHPosOne
      μG ρ hN2 hρcont β hpos f
  have hre : (inner ℂ f (transferOp μG ρ hN2 hρcont β
        (transferOp μG ρ hN2 hρcont β f))).re
      = ‖transferOp μG ρ hN2 hρcont β f‖ ^ 2 := by
    rw [inner_transferOp_iter_eq μG ρ hN2 hρcont hN β f]
    exact Complex.ofReal_re _
  have hnorm : ‖inner ℂ f (transferOp μG ρ hN2 hρcont β
        (transferOp μG ρ hN2 hρcont β f))‖
      = ‖transferOp μG ρ hN2 hρcont β f‖ ^ 2 := by
    rw [inner_transferOp_iter_eq μG ρ hN2 hρcont hN β f,
      Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  have hCS := inner_transferOp_cauchy_schwarz μG ρ hN2 hρcont hN β
    hpos f (transferOp μG ρ hN2 hρcont β f)
  have hstep := inner_transferOp_step_le μG ρ hN2 hρcont hN β hpos f
  have hcomb : (‖transferOp μG ρ hN2 hρcont β f‖ ^ 2)
        * (‖transferOp μG ρ hN2 hρcont β f‖ ^ 2)
      ≤ (inner ℂ f (transferOp μG ρ hN2 hρcont β f)).re
        * (‖transferOp μG ρ hN2 hρcont β f‖ ^ 2) := by
    calc (‖transferOp μG ρ hN2 hρcont β f‖ ^ 2)
          * (‖transferOp μG ρ hN2 hρcont β f‖ ^ 2)
        = ‖inner ℂ f (transferOp μG ρ hN2 hρcont β
            (transferOp μG ρ hN2 hρcont β f))‖ ^ 2 := by
          rw [hnorm]; ring
      _ ≤ (inner ℂ f (transferOp μG ρ hN2 hρcont β f)).re
            * (inner ℂ (transferOp μG ρ hN2 hρcont β f)
                (transferOp μG ρ hN2 hρcont β
                  (transferOp μG ρ hN2 hρcont β f))).re := hCS
      _ ≤ (inner ℂ f (transferOp μG ρ hN2 hρcont β f)).re
            * (‖transferOp μG ρ hN2 hρcont β f‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hstep hA
  rw [hre]
  by_cases hx : ‖transferOp μG ρ hN2 hρcont β f‖ ^ 2 = 0
  · rw [hx]; exact hA
  · have hxpos : 0 < ‖transferOp μG ρ hN2 hρcont β f‖ ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm hx)
    exact le_of_mul_le_mul_right hcomb hxpos

/-- **(D-bdd)ʳ, diagonal domination** (the gate's §3.5
claim): under H-pos(1)ʳ,
`Π₂(φ, φ).re ≤ Π₁(φ, φ).re` for every slice observable —
the contractivity content from which the descended
operator's bound follows. -/
theorem slicePairTwo_self_re_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (φ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β)) :
    (slicePairTwo μG ρ hN2 hρcont β φ hφ φ hφ).re
      ≤ (slicePairOne μG ρ hN2 hρcont β φ hφ φ hφ).re :=
  inner_transferOp_iter_le μG ρ hN2 hρcont hN β hpos
    (sliceState μG ρ β φ hφ)

/-- **(D-bdd)ʳ, the bound** (the gate's §3.5 form): under
H-pos(1)ʳ,
`‖Π₂(φ, χ)‖ ≤ ‖[F_φ]‖_OS · ‖[F_χ]‖_OS`, where the OS
norm of a class is the square root of `Π₁`'s diagonal.
So the descended two-step form is bounded by `1` in the
OS norm — with (D-desc)ʳ, this is the boundedness input
S2-2c's Riesz assembly consumes. -/
theorem slicePairTwo_norm_le (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hN : Even N) (β : ℝ)
    (hpos : SliceHPosOne μG ρ hN2 hρcont β)
    (φ χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hφ : MemLp φ 2 (sliceMeasure (N := N) μG ρ β))
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β)) :
    ‖slicePairTwo μG ρ hN2 hρcont β φ hφ χ hχ‖
      ≤ Real.sqrt (slicePairOne μG ρ hN2 hρcont β φ hφ φ hφ).re
        * Real.sqrt (slicePairOne μG ρ hN2 hρcont β χ hχ χ hχ).re
    := by
  show ‖inner ℂ (sliceState μG ρ β φ hφ)
      (transferOp μG ρ hN2 hρcont β
        (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ)))‖
    ≤ Real.sqrt (inner ℂ (sliceState μG ρ β φ hφ)
        (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β φ hφ))).re
      * Real.sqrt (inner ℂ (sliceState μG ρ β χ hχ)
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ))).re
  have hAφ : 0 ≤ (inner ℂ (sliceState μG ρ β φ hφ)
      (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β φ hφ))).re :=
    inner_transferOp_self_re_nonneg_of_sliceHPosOne
      μG ρ hN2 hρcont β hpos _
  have hCS := inner_transferOp_cauchy_schwarz μG ρ hN2 hρcont hN β
    hpos (sliceState μG ρ β φ hφ)
    (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ))
  have hstep := inner_transferOp_step_le μG ρ hN2 hρcont hN β hpos
    (sliceState μG ρ β χ hχ)
  have hdom := inner_transferOp_iter_le μG ρ hN2 hρcont hN β hpos
    (sliceState μG ρ β χ hχ)
  have hbχ : (inner ℂ (sliceState μG ρ β χ hχ)
        (transferOp μG ρ hN2 hρcont β
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ)))).re
      = ‖transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ)‖
        ^ 2 := by
    rw [inner_transferOp_iter_eq μG ρ hN2 hρcont hN β _]
    exact Complex.ofReal_re _
  have hchain : (inner ℂ
        (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ))
        (transferOp μG ρ hN2 hρcont β
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ)))).re
      ≤ (inner ℂ (sliceState μG ρ β χ hχ)
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ))).re
      := le_trans hstep (le_trans (le_of_eq hbχ.symm) hdom)
  have hfin : ‖inner ℂ (sliceState μG ρ β φ hφ)
        (transferOp μG ρ hN2 hρcont β
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ)))‖
        ^ 2
      ≤ (inner ℂ (sliceState μG ρ β φ hφ)
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β φ hφ))).re
        * (inner ℂ (sliceState μG ρ β χ hχ)
            (transferOp μG ρ hN2 hρcont β
              (sliceState μG ρ β χ hχ))).re :=
    le_trans hCS (mul_le_mul_of_nonneg_left hchain hAφ)
  have hsqrt : ‖inner ℂ (sliceState μG ρ β φ hφ)
        (transferOp μG ρ hN2 hρcont β
          (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β χ hχ)))‖
      ≤ Real.sqrt ((inner ℂ (sliceState μG ρ β φ hφ)
            (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β φ hφ))).re
          * (inner ℂ (sliceState μG ρ β χ hχ)
              (transferOp μG ρ hN2 hρcont β
                (sliceState μG ρ β χ hχ))).re) := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt hfin
  rwa [Real.sqrt_mul hAφ] at hsqrt

/-! ## §F. (D-vac)ʳ — the vacuum fixed point -/

/-- **The constant slice observable's state is the
vacuum:** `sliceState β 1 = osVacuum`, by `Lp.ext` —
both are almost everywhere the constant `1`. -/
theorem sliceState_one_eq_osVacuum
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hd : 0 < d) (β : ℝ)
    (h1 : MemLp (1 : (↥(sliceLinks (N := N)) → G) → ℂ) 2
      (sliceMeasure (N := N) μG ρ β)) :
    sliceState μG ρ β 1 h1 = osVacuum μG ρ hρcont hd β := by
  haveI := isProbabilityMeasure_sliceMeasure (N := N) μG ρ hρcont
    hd β
  apply MeasureTheory.Lp.ext
  have e1 : ⇑(sliceState μG ρ β 1 h1)
      =ᵐ[sliceMeasure (N := N) μG ρ β]
        (1 : (↥(sliceLinks (N := N)) → G) → ℂ) :=
    MemLp.coeFn_toLp h1
  have e2 : ⇑(osVacuum μG ρ hρcont hd β)
      =ᵐ[sliceMeasure (N := N) μG ρ β]
        (1 : (↥(sliceLinks (N := N)) → G) → ℂ) := by
    show ⇑(MeasureTheory.Lp.const 2 (sliceMeasure (N := N) μG ρ β)
        (1 : ℂ))
      =ᵐ[sliceMeasure (N := N) μG ρ β]
        (1 : (↥(sliceLinks (N := N)) → G) → ℂ)
    exact MeasureTheory.Lp.coeFn_const 2 _ (1 : ℂ)
  exact e1.trans e2.symm

/-- **(D-vac)ʳ:** `Π₂(χ, 1) = Π₁(χ, 1)` for every slice
observable `χ` — the constant observable's slice state is
fixed by `transferOp` (`transferOp_vacuum`, R1's Markov
content), so the second step agrees with the first on
the vacuum. No positivity is used. -/
theorem slicePairTwo_one_right (hN2 : 2 ≤ N)
    (hρcont : Continuous fun g : G => repMatrix ρ g)
    (hd : 0 < d) (β : ℝ)
    (χ : (↥(sliceLinks (N := N)) → G) → ℂ)
    (hχ : MemLp χ 2 (sliceMeasure (N := N) μG ρ β))
    (h1 : MemLp (1 : (↥(sliceLinks (N := N)) → G) → ℂ) 2
      (sliceMeasure (N := N) μG ρ β)) :
    slicePairTwo μG ρ hN2 hρcont β χ hχ 1 h1
      = slicePairOne μG ρ hN2 hρcont β χ hχ 1 h1 := by
  have hfix : transferOp μG ρ hN2 hρcont β (sliceState μG ρ β 1 h1)
      = sliceState μG ρ β 1 h1 := by
    rw [sliceState_one_eq_osVacuum μG ρ hρcont hd β h1]
    exact transferOp_vacuum μG ρ hN2 hρcont hd β
  show inner ℂ (sliceState μG ρ β χ hχ)
      (transferOp μG ρ hN2 hρcont β
        (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β 1 h1)))
    = inner ℂ (sliceState μG ρ β χ hχ)
        (transferOp μG ρ hN2 hρcont β (sliceState μG ρ β 1 h1))
  rw [hfix, hfix]

end DescentBoundedness

end ThetLogos
